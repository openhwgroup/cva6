#include "Variane_core_avalon.h"
#include "verilated.h"
#if VM_TRACE
#include <verilated_vcd_c.h>
#endif
#include <fstream>
#include <iostream>
#include <iomanip>
#include <cstdint>
#include <vector>
#include <unistd.h>
#include "socket_packet_utils.h"
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include <search.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>
#include <execinfo.h>

static std::fstream logfile;
static uint64_t hashcnt = 0;

static struct sort {
        struct sort *nxt;
        uint64_t rnd;
      } *head = NULL;

ENTRY *find(uint64_t oldaddr)
{
  char key[20];
  ENTRY e, *ep;
  uint64_t rnd = oldaddr & -8;
  sprintf(key, "%.14lX", 0xFFFFFFFFFFFFFF & rnd);
  e.key = (char *)strdup(key);
  ep = hsearch(e, FIND);
  if (!ep)
    {
      e.data = calloc(1, sizeof(int64_t));
      ep = hsearch(e, ENTER);
      if (!ep)
        {
          logfile << "hash table full" << std::endl;
          abort();
        }
    }
  return ep;
}

void populate(uint64_t oldaddr, int64_t inst, int shft)
{
  uint64_t rnd = oldaddr & -8;
  ENTRY *ep = find(rnd);
  int64_t *instp = (int64_t *)(ep->data);
  int64_t old = *instp;
  int64_t mask = shft < 0 ? ~(0xFFFFFFFFULL >> -shft) : ~(0xFFFFFFFFULL << shft);
  int64_t shftinst = shft < 0 ? inst >> -shft : inst << shft;
  *instp = (old & mask) | shftinst;
  if (0) printf("Find 0x%lx: shft = %d, old = 0x%.16lx mask = 0x%.16lx new = 0x%.16lx *instp = 0x%.16lx\n",
                oldaddr, shft, old, mask, shftinst, *instp);
}  

struct RVFI_DII_Execution_Packet {
    std::uint64_t rvfi_order : 64;      // [00 - 07] Instruction number:      INSTRET value after completion.
    std::uint64_t rvfi_pc_rdata : 64;   // [08 - 15] PC before instr:         PC for current instruction
    std::uint64_t rvfi_pc_wdata : 64;   // [16 - 23] PC after instr:          Following PC - either PC + 4 or jump/trap target.
    std::uint64_t rvfi_insn : 64;       // [24 - 31] Instruction word:        32-bit command value.
    std::uint64_t rvfi_rs1_data : 64;   // [32 - 39] Read register values:    Values as read from registers named
    std::uint64_t rvfi_rs2_data : 64;   // [40 - 47]                          above. Must be 0 if register ID is 0.
    std::uint64_t rvfi_rd_wdata : 64;   // [48 - 55] Write register value:    MUST be 0 if rd_ is 0.
    std::uint64_t rvfi_mem_addr : 64;   // [56 - 63] Memory access addr:      Points to byte address (aligned if define
                                        //                                      is set). *Should* be straightforward.
                                        //                                      0 if unused.
    std::uint64_t rvfi_mem_rdata : 64;  // [64 - 71] Read data:               Data read from mem_addr (i.e. before write)
    std::uint64_t rvfi_mem_wdata : 64;  // [72 - 79] Write data:              Data written to memory by this command.
    std::uint8_t rvfi_mem_rmask : 8;    // [80]      Read mask:               Indicates valid bytes read. 0 if unused.
    std::uint8_t rvfi_mem_wmask : 8;    // [81]      Write mask:              Indicates valid bytes written. 0 if unused.
    std::uint8_t rvfi_rs1_addr : 8;     // [82]      Read register addresses: Can be arbitrary when not used,
    std::uint8_t rvfi_rs2_addr : 8;     // [83]                          otherwise set as decoded.
    std::uint8_t rvfi_rd_addr : 8;      // [84]      Write register address:  MUST be 0 if not used.
    std::uint8_t rvfi_trap : 8;         // [85] Trap indicator:          Invalid decode, misaligned access or
                                        //                                      jump command to misaligned address.
    std::uint8_t rvfi_halt : 8;         // [86] Halt indicator:          Marks the last instruction retired 
                                        //                                      before halting execution.
    std::uint8_t rvfi_intr : 8;         // [87] Trap handler:            Set for first instruction in trap handler.     
};

struct RVFI_DII_Instruction_Packet {
    std::uint32_t dii_insn : 32;      // [0 - 3] Instruction word: 32-bit instruction or command. The lower 16-bits
                                      // may decode to a 16-bit compressed instruction.
    std::uint16_t dii_time : 16;      // [5 - 4] Time to inject token.  The difference between this and the previous
                                      // instruction time gives a delay before injecting this instruction.
                                      // This can be ignored for models but gives repeatability for implementations
                                      // while shortening counterexamples.
    std::uint8_t dii_cmd : 8;         // [6] This token is a trace command.  For example, reset device under test.
    std::uint8_t padding : 8;         // [7]
};

double main_time = 0;

unsigned int belu[] = {
    0x00000000,
    0x000000ff,
    0x0000ff00,
    0x0000ffff,
    0x00ff0000,
    0x00ff00ff,
    0x00ffff00,
    0x00ffffff,
    0xff000000,
    0xff0000ff,
    0xff00ff00,
    0xff00ffff,
    0xffff0000,
    0xffff00ff,
    0xffffff00,
    0xffffffff
};

double sc_time_stamp() {
    return main_time;
}

static int received = 0;
static int in_count = 0;
static int high_water = 0;
static int abort_putn = 0;
static int out_count = 0;
static int cache_count = 1;
static int ret_cnt = 0;
static int report_cnt = 0;

static unsigned long long socket = 0;
static std::vector<RVFI_DII_Instruction_Packet> instructions;
static std::vector<RVFI_DII_Execution_Packet> returntrace;
static Variane_core_avalon* top;
#if VM_TRACE
static VerilatedVcdC trace_obj;
#endif
// convert verilator data structures on a given commit port to a DII returntrace structure

RVFI_DII_Execution_Packet execpacket(int i)
{
  std::int32_t insn = (top->rvfi_insn >> i*32) & 0xFFFFFFFF;
  RVFI_DII_Execution_Packet execpkt = {
    .rvfi_order = ((std::uint64_t*)(top->rvfi_order))[i],
    .rvfi_pc_rdata = ((std::uint64_t*)(top->rvfi_pc_rdata))[i],
    .rvfi_pc_wdata = ((std::uint64_t*)(top->rvfi_pc_wdata))[i],
    .rvfi_insn = (uint64_t)(int64_t)insn,
    .rvfi_rs1_data = ((std::uint64_t*)(top->rvfi_rs1_rdata))[i],
    .rvfi_rs2_data = ((std::uint64_t*)(top->rvfi_rs2_rdata))[i],
    .rvfi_rd_wdata = ((std::uint64_t*)(top->rvfi_rd_wdata))[i],
    .rvfi_mem_addr = ((std::uint64_t*)(top->rvfi_mem_addr))[i],
    .rvfi_mem_rdata = ((std::uint64_t*)(top->rvfi_mem_rdata))[i],
    .rvfi_mem_wdata = ((std::uint64_t*)(top->rvfi_mem_wdata))[i],
    .rvfi_mem_rmask = (uint8_t)((top->rvfi_mem_rmask >> i*4) & 15),
    .rvfi_mem_wmask = (uint8_t)((top->rvfi_mem_wmask >> i*4) & 15),
    .rvfi_rs1_addr = (uint8_t)((top->rvfi_rs1_addr >> i*5) & 31),
    .rvfi_rs2_addr = (uint8_t)((top->rvfi_rs2_addr >> i*5) & 31),
    .rvfi_rd_addr = (uint8_t)((top->rvfi_rd_addr >> i*5) & 31),
    .rvfi_trap = (uint8_t)((top->rvfi_trap >> i) & 1),
    .rvfi_halt = top->rst_i,
    .rvfi_intr = (uint8_t)((top->rvfi_intr >> i) & 1)
  };
  return execpkt;
}

void receive_packet(void)
{
  int old_rec = 0;
  int prev_rec = received;
  char recbuf[sizeof(RVFI_DII_Instruction_Packet) + 1] = {0};
  // sleep for 1ms before trying to receive another instruction
  usleep(1000);
        
  do {
    old_rec = received;
    //logfile << "receive" << std::endl;
    //logfile << "in_count: " << in_count << " received: " << received << std::endl;
    
    // try to receive a packet
    serv_socket_getN((unsigned int *) recbuf, socket, sizeof(RVFI_DII_Instruction_Packet));
    
    // the last byte received will be 0 if our attempt to receive a packet was successful
    if (recbuf[8] == 0) {
      /*                logfile << "received this" << std::endl;
                        for (int i = 0; i < sizeof(recbuf); i++) {
                        logfile << (int) recbuf[i] << " ";
                        }
                        logfile << std::endl; 
      */
      // set up a packet and try to receive packets if the number of instructions that we've put in is
      // equal to the number of instructions we've received from TestRIG
      RVFI_DII_Instruction_Packet *packet = (RVFI_DII_Instruction_Packet *) recbuf;
      
      //logfile << "time: " << (int) packet->dii_time << std::endl;
      //logfile << "cmd: " << (int) packet->dii_cmd << std::endl;
      //logfile << "insn: 0x" << std::hex <<  (int) packet->dii_insn << std::dec << std::endl;
      
      instructions.push_back(*packet);
      abort_putn = 0;
      received++;
      //                break;
    }    
  }
  while ((in_count >= received) || (received > old_rec));
  if (received > prev_rec)
    {
      logfile << "received: " << received-prev_rec << std::endl;
    }
}

void dump_insn(int count)
{
  int i, cnt = 0;
  char name1[L_tmpnam];
  struct stat buffer;
  if (count > high_water + 10)
    {
      do {
        sprintf(name1, "test%d.rig", ++cnt);
      }
      while (stat (name1, &buffer) == 0); 
      logfile << "temporary file name: " << name1 << '\n';
      std::fstream fs;
      fs.open (name1, std::fstream::binary | std::fstream::out | std::fstream::trunc);
      for (i = high_water; i < out_count; i++)
        {
          if (instructions[i].dii_cmd)
            fs << ".4byte 0x" << std::hex << (int) (instructions[i].dii_insn & 0xFFFFFFFF) << std::dec << std::endl;
        }
      fs.close();
    }
}

void one_clk(int lev)
{
        top->clk_i = lev;
        top->eval();
        
        // tracing
#if VM_TRACE
        trace_obj.dump(main_time);
        trace_obj.flush();
        main_time++;
#endif        
}

void broken_pipe_handler(int signum)
{
  logfile << "broken pipe handler: " << signum << std::endl;
  returntrace.clear();
  logfile << std::flush;
  abort_putn = 1;
  in_count = 0;
  out_count = 0;
  cache_count = 1;
  received = 0;
  high_water = 0;
  ret_cnt = 0;
  report_cnt = 0;
  /*
  for (int i = 0; i < 100; i++)
    {
      one_clk(1);
      one_clk(0);
    }
  */
}

void signal_handler(int signum)
{
  int fd, nptrs;
  char nam[20];
  enum {SIZE=100};
  void *buffer[100];
  char **strings;
  sprintf(nam, "%d.sig", signum);
  fd = open(nam, O_WRONLY|O_CREAT|O_TRUNC, 0600);
  write(fd, nam, strlen(nam)+1);

  nptrs = backtrace(buffer, SIZE);

  /* The call backtrace_symbols_fd(buffer, nptrs, STDOUT_FILENO)
     would produce similar output to the following: */

  strings = backtrace_symbols(buffer, nptrs);
  if (strings == NULL) {
    char *msg = strerror(errno);
    write(fd, msg, strlen(msg)+1);
    close(fd);
    exit(signum);
  }
  
  for (int j = 0; j < nptrs; j++)
    {
    write(fd, strings[j], strlen(strings[j]));
    write(fd, "\n", 1);
    }
  
  close(fd);
  exit(signum);
}

// This will open a socket on the hostname and port provided
// It will then try to receive RVFI-DII packets and put the instructions
// from them into the core and simulate it.
// The RVFI trace is then sent back

int main(int argc, char** argv, char** env) {

    if (argc != 3) {
        std::cerr << "wrong number of args" << std::endl;
        exit(-1);
    }

    for (int i = 0; i < 16; i++)
      signal(i, signal_handler);
    
    Verilated::commandArgs(argc, argv);
    top = new Variane_core_avalon;
    logfile.open ("ariane.log", std::fstream::binary | std::fstream::out | std::fstream::trunc);

    // set up tracing
    #if VM_TRACE
    Verilated::traceEverOn(true);
    top->trace(&trace_obj, 99);
    trace_obj.open("vlt_d.vcd");
    #endif

    uint8_t memory[65536] = {0};

    //logfile << "init socket" << std::endl;
    socket = serv_socket_create(argv[1], std::atoi(argv[2]));
    //logfile << "created" << std::endl;
    serv_socket_init(socket, broken_pipe_handler);
    //logfile << "inited" << std::endl;
    hcreate((1<<19)-1);


    // set up initial core inputs
    top->clk_i = 0;
    top->rst_i = 1;
    top->test_en_i = 0;
    top->boot_addr_i = 0x80000000;
    top->avm_main_waitrequest = 0;
    top->eval();

    top->rst_i = 0;

    uint64_t old_addr = ~0;

    while (1) {
        // logfile << "main loop begin" << std::endl;
           
        // send back execution trace
        // send back execution trace if the number of instructions that have come out is equal to the
        // number that have gone in
        if (returntrace.size() > 0 && out_count == in_count) {
            for (int i = 0; i < returntrace.size(); i++) {
              ++ret_cnt;
              if (!returntrace[i].rvfi_insn)
                logfile << "halt token" << std::endl;
              else
                logfile << std::hex << ".4byte 0x" << (0xFFFFFFFF & returntrace[i].rvfi_insn) << std::dec << std::endl;
              // loop to make sure that the packet has been properly sent
              while (!abort_putn &&
                     !serv_socket_putN(socket, sizeof(RVFI_DII_Execution_Packet), (unsigned int *) &(returntrace[i]))
                     ) {
                // empty
              }
            }
            if (ret_cnt >= report_cnt+100)
              {
                logfile << "sent: " << ret_cnt << std::endl;
                report_cnt = ((ret_cnt+99)/100)*100;
              }
            returntrace.clear();
            logfile << std::flush;
        }

        if ((received < high_water+3) || instructions[received-1].dii_cmd)
                {
                  receive_packet();
                }
        
        // need to clock the core while there are still instructions in the buffer
        //        logfile << "clock" << std::endl;
        if ((in_count <= received) && received > high_water && ((in_count - out_count > 0) || in_count == high_water || (out_count == in_count && received > in_count))) {
          int i;
          // logfile << "in_count: " << in_count << " out_count: " << out_count << " diff: " << in_count - out_count << std::endl;
            /*
            if (in_count - out_count > 0) {
                for (int i = out_count + 1; i <= in_count; i++) {
                    logfile << "next " << i << ": " << std::hex << instructions[i].dii_insn << std::dec << std::endl;
                }
            }
            */

        for (i = 0; i < 2; i++) {
            // read rvfi data and add packet to list of packets to send
            // the condition to read data here is that there is an rvfi valid signal
            // this deals with counting instructions that the core has finished executing
          if (in_count > out_count && (top->rvfi_valid & (1<<i) & ~top->rvfi_trap) && !abort_putn) {
                RVFI_DII_Execution_Packet execpkt = execpacket(i);
                returntrace.push_back(execpkt);
                out_count++;
                logfile << "\t\t\tcommit\t0x" << std::hex << (int) execpkt.rvfi_insn << std::dec << std::endl << std::flush;
                // detect non-exception flush such as fence.i
                if (top->flush_ctrl_if) {
                    logfile << "\t\tnon-exception flush detected" << std::endl << std::flush;
                    in_count = out_count;
                    cache_count = out_count;
                }
            }

          // detect exceptions in order to replay instructions so they don't get lost
          if (in_count > out_count && (top->rvfi_valid & (1<<i) & top->rvfi_trap) && !abort_putn) {
                RVFI_DII_Execution_Packet execpkt = execpacket(i);
                returntrace.push_back(execpkt);
                out_count++;
                logfile << "\t\texception detected" << std::endl << std::flush;
                // this will need to be reworked
                // currently, in order for this to work we need to remove illegal_insn from the assignment
                // to rvfi_trap since when the core is first started the instruction data is garbage so
                // this is high
              if ((top->rvfi_trap >> i) & 1) {
                    // if there has been a trap, then we know that we just tried to do a load/store
                    // we need to go back to out_count
                    in_count = out_count;
                    cache_count = out_count;
                } else {
                    //logfile << "cmd: " << (instructions[out_count].dii_cmd ? "instr" : "rst") << std::endl;
                    if (!instructions[out_count].dii_cmd) {
                        // the last instruction we saw coming out was a reset
                        // this means that we tried to do a jump straight away, and it will only come out of
                        // the rvfi signals later. we need to go forward 2 places from the out_cout
                        // (the jump has already been performed, so we want the instruction after it)
                        in_count = out_count + 2;
                        cache_count = out_count + 2;
                    } else {
                        // the last instruction was an actual instruction. we are doing a jump but it hasn't
                        // come out of the rvfi signals yet so we need to skip it when replaying instructions
                        in_count = out_count + 1;
                        cache_count = out_count + 1;
                    }
                }
            }
        }
          
            // perform instruction read
            // returns instructions from the DII input from TestRIG
            top->rst_i = 0;
            if (in_count < received) {
              if (instructions[in_count].dii_cmd) {
                    if (top->instruction_valid & 1) {
                        // if we have instructions to feed into it, then set readdatavalid and waitrequest accordingly
                        // logfile << "checking instruction in_count: " << in_count << " received: " << received << std::endl;
                        if (received > in_count) {
                          int expected = (int) (instructions[in_count].dii_insn & 0xFFFFFFFF);
                          int insn = (int) (top->instr & 0xFFFFFFFF);
                          int addr = (int) (((std::uint64_t*)(top->addr))[0] & 0xFFFFFFFF);
                          //                        logfile << "inserting instruction @@@@@@@@@@@@@@@@@@@@" << std::endl;
                            top->instr_dii = instructions[in_count++].dii_insn;
                            top->instruction_valid_dii = 1;
                            logfile << "\taddr\t0x" << std::hex << addr << std::dec << std::endl;
                            logfile << "\texpect\t0x" << std::hex << expected << std::dec << std::endl;
                            logfile << "\tinsn\t0x" << std::hex << insn << std::dec << std::endl;
                            if (expected != insn)
                              {
                                logfile << "MISMATCH: " << in_count-high_water << std::endl;
                                dump_insn(in_count+1);
                                abort();
                              }
                        }
                    }        
                } else if (in_count - out_count == 0) {
                    top->rst_i = 1;

                    // clear memory
                    for (int i = 0; i < (sizeof(memory)/sizeof(memory[0])); i++) {
                        memory[i] = 0;
                    }
                    in_count++;
                    ret_cnt = 0;
                    report_cnt = 0;
              }
            }
            // read rvfi data and add packet to list of packets to send
            // the condition to read data here is that the core has just been reset
            // this deals with counting reset instruction packets from TestRIG
            if (in_count - out_count > 0 && top->rst_i && !abort_putn) {
              returntrace.push_back(execpacket(0)); // we only need to consult the first commit port

                out_count++;
                in_count = out_count;
                cache_count = out_count;

                logfile << "resetting, " << "out_count: " << out_count << std::endl;
                dump_insn(received);
                high_water = received;
            }

            // perform main memory read
            if (top->avm_main_read) {
                // get the address so we can manipulate it
                int address = top->avm_main_address;

                // TestRIG specifies that byte addresses must be between 0x80000000 and 0x80008000
                // our avalon wrapper divides the byte address by 4 in order to get a word address
                // so we need to check for addresses between 0x20003fff and 0x20000000
                if (address > 0x20003fff || address < 0x20000000) {
                    // the core tried to read from an address outside the specified range
                    // set the signals appropriately
                    top->avm_main_response = 0b11;
                    top->avm_main_readdata = 0xdeadbeef & belu[top->avm_main_byteenable];
                    top->avm_main_readdatavalid = 1;
                } else {
                    // the core tried to read from an address within the specified range
                    // we need to get the correct data from memory

                    // translate the address so it is between 0x0 and 0x00003fff
                    address = address & 0x00003fff;

                    // convert the address to a byte address
                    address <<= 2;

                    // we want to start with the highest byte address for this word since our
                    // memory is little endian
                    address += 3;

                    // for each bit in the byteenable, check if we should get that byte from memory
                    // if not, set it to 0
                    unsigned int data = 0;
                    data |= ((top->avm_main_byteenable>>3) & 0x1) ? memory[address] : 0;

                    address--;
                    data<<=8;

                    data |= ((top->avm_main_byteenable>>2) & 0x1) ? memory[address] : 0;

                    address--;
                    data<<=8;
                    
                    data |= ((top->avm_main_byteenable>>1) & 0x1) ? memory[address] : 0;

                    address--;
                    data<<=8;

                    data |= ((top->avm_main_byteenable>>0) & 0x1) ? memory[address] : 0;

                    // set the signals appropriately
                    top->avm_main_readdata = data;
                    top->avm_main_readdatavalid = 1;
                    top->avm_main_response = 0b00;
                }
            }

            // perform main memory writes
            if (top->avm_main_write) {
                // get the address so we can manipulate it
                int address = top->avm_main_address;


                // TestRIG specifies that byte addresses must be between 0x80000000 and 0x80008000
                // our avalon wrapper divides the byte address by 4 in order to get a word address
                // so we need to check for addresses between 0x20003fff and 0x20000000
                if (address > 0x20003fff || address < 0x20000000) {
                    // the core tried to write to an address outside the specified range
                    // set the signals appropriately
                    top->avm_main_response = 0b11;
                    top->avm_main_waitrequest = 0;
                } else {
                    // the core tried to read from an address within the specified range

                    // translate the address so it is between 0x0 and 0x00003fff
                    address = address & 0x00003fff;

                    // get the data from the core
                    unsigned int data = top->avm_main_writedata;

                    // convert the address to a byte address
                    address<<=2;

                    // we want to only change the memory values for which byteenable is high
                    // if byteenable is low, preserve that byte in memory
                    memory[address] = (top->avm_main_byteenable & 0x1) ? data : memory[address];
                    address++;
                    data>>=8;

                    memory[address] = ((top->avm_main_byteenable>>1) & 0x1) ? data : memory[address];
                    address++;
                    data>>=8;

                    memory[address] = ((top->avm_main_byteenable>>2) & 0x1) ? data : memory[address];
                    address++;
                    data>>=8;

                    memory[address] = ((top->avm_main_byteenable>>3) & 0x1) ? data : memory[address];


                    // set output signals appropriately
                    top->avm_main_response = 0b00;
                    top->avm_main_waitrequest = 0;
                }
            }

            
            if (!top->avm_main_write && !top->avm_main_read) {
                top->avm_main_readdatavalid = 0;
            }

        if (top->rom_req) {
              uint64_t actual2, actual = 0xDEADBEEF;
              int shft = top->virtual_request_address - top->rom_addr;
              ENTRY *ep = find(top->rom_addr);
              int64_t *entered = (int64_t *)(ep->data);
              while ((received <= cache_count+1) && instructions[received-1].dii_cmd)
                {
                  receive_packet();
                }
              top->rom_rdata = 0;
              if (old_addr != top->virtual_request_address)
                {
                  int shft = top->virtual_request_address & 6;
                  old_addr = top->virtual_request_address;
                  logfile << "newaddr\t0x" << std::hex << top->virtual_request_address << std::dec << std::endl;
                  actual = instructions[cache_count++].dii_insn & 0xFFFFFFFF;
                  logfile << "shift\t" << std::dec << shft << std::endl;
                  actual2 = instructions[cache_count].dii_insn & 0xFFFFFFFF;
                  logfile << "actual2\t0x" << std::hex << actual2 << std::dec << std::endl;
                  switch (shft)
                    {
                    case 0:
                      populate(top->rom_addr, actual, 0);
                      populate(top->rom_addr, actual2, 32);
                      break;
                    case 2:
                      populate(top->rom_addr, actual, 16);
                      populate(top->rom_addr, actual2, 48);
                      break;
                    case 4:
                      populate(top->rom_addr, actual, 32);
                      populate(top->rom_addr+8, actual2, 0);
                      break;
                    case 6:
                      if (top->virtual_request_address < top->rom_addr)
                        {
                          populate(top->rom_addr-8, actual, 48);
                          populate(top->rom_addr, actual, -16);
                          populate(top->rom_addr, actual2, 16);
                        }
                      else
                        {
                          populate(top->rom_addr, actual, 48);
                          populate(top->rom_addr+8, actual, -16);
                          populate(top->rom_addr+8, actual2, 16);
                        }
                      break;                      
                    }
                }
              top->rom_rdata = *entered;
              
              logfile << "romaddr\t0x" << std::hex << top->rom_addr << std::dec << std::endl;
              logfile << "vrqaddr\t0x" << std::hex << top->virtual_request_address << std::dec << std::endl;
              if (actual != 0xDEADBEEF) logfile << "actual\t0x" << std::hex << actual << std::dec << std::endl;
              logfile << "shift1\t0x" << std::hex << *entered << std::dec << std::endl;
        }

        if (top->is_mispredict)
          {
              logfile << "mispred\t" << cache_count << std::endl;
            --cache_count;
          }

        one_clk(1);
        one_clk(0);
        
            // if we have a large difference between the number of instructions that have gone in
            // and the number that have come out, something's gone wrong; exit the program
            if (in_count - out_count > 20) {
              logfile << "inc_count: " << in_count << ", out_count: " << out_count << std::endl;
              break;
            }
        }
    
    }

    logfile << "finished" << std::endl << std::flush;
    delete top;
    exit(0);
}
