
# Block Details

The processor has 5-stages:

## Next PC Generation (PC Gen)

PC gen is responsible for generating the next program counter. All program counters are logical addressed. If the logical to physical mapping changes a fence instruction should flush the pipeline, caches (?) and TLB.
This stage contains speculation on the next branch target as well as the information if the branch target is taken or not. In addition, it provides ports to the branch history table (BHT) and branch target buffer (BTB).

If the branch target buffer decodes a certain PC as a jump the BHT decides if the branch is taken or not.
Because of the various state-full memory structures this stage is split into two pipeline stages. It also provides a handshaking signal to the decode stage to stall the pipeline if this should be necessary (back-pressure).

The next PC can originate from the following sources:

1.  Exception (including interrupts): This also means to figure out to which exception handler the delegate registers are pointing to. If an exception is taken, disable interrupts.
2.  Debug
3.  Request from execute stage (jump, branch) which was not detected as one by the BHT.
4.  Predicted PC (BHT and BTB)
5.  Environment Call (`ecall) instruction. Read the CSRs to figure out where to jump.
6.  Miss-predict: This triggers a pipeline flush and the PC Gen stage starts fetching from there.

### BTB and BHT

Currently all branch prediction data structures reside in a single register like file. It is indexed with the appropriate number of bits from the PC and contains information about the predicted target address as well as the outcome of a two (actually configurable) saturation counter. The prediction result is used in the subsequent stage to jump (or not).

For a future version a more accurate predictor might be necessary (gshare, tournament,...).


## Instruction Fetch (IF)

In the IF stage we already know the physical PC. The request of the instruction is on its way to the instruction memory. We know the result of the BHT and can set the next PC accordingly. At the end of this stage the instruction PC is passed on to the ID stage. Retrieved instructions are stored in an instruction queue.
It is possible that a TLB or cache miss occurred. If this is the case the IF stage signals that it is not ready. The pipeline in the direction of the ID stage will empty itself.

### ITLB


### Instruction Queue

The instruction queue is part of the IF stage. Its purpose is to decouple the instruction fetch unit as much as possible from the rest of the pipeline.

## Instruction Decode (ID)

The ID stage contains the instruction decode logic (including the planned compressed decoder) as well as the register files (CSR, floating point and regular register file). The decoded instruction is committed to the scoreboard. The scoreboard decides which instruction it can issues next to the execute stage.

### Decoder

The decoder's purpose is to expand the 32 bit incoming instruction stream to set the right values in the scoreboard, e.g.: which functional unit to activate, setting wright path and reading the destination, *src1* and *src2* register.

The current privilege level is not checked in the decoder since there could be an operation in progress that sets the privilege level to the appropriate level.
### Scoreboard

The scoreboard's purpose was described in detail in the architecture section.

![Scoreboad](./fig/scoreboard.png)

The field functional unit can be of the following types:

- CSR: Modify the CSR register using OP, OP can be of type:
    + MRET (check the current privilege level against the mret instruction, are we allowed to execute it?)
    + SRET (same as above but with sret)
    + URET (same as above but with uret)
    + ECALL (make an environment call)
    + WRITE (writing a CSR, we need to flush the whole pipeline after a write)
    + READ (we can simply continue with the execution, the worst that could happen is an access fault if we do not have the right privilege level)
    + SET (atomic set, flush the whole pipeline)
    + CLEAR (atomic clear, flush the whole pipeline)
- ALU: Use the ALU to perform OP
    + ADD, SUB, etc. all arithmetic instructions. ALU always writes to the register file
- LSU: Use the LSU to perform OP
    + LD, SD, LBU, etc. Loads are writing to the register file, stores are committed as soon as the store address and store data is known.
- MULT: Use the Multiplier to perform OP
    + MULT, DIV, etc. all multiplier instructions are writing to the register file.

The scoreboard also contains all exception information which occurred during execution. In particular those fields are:
- exception cause
- additional information like illegal instruction and faulting address
- if it is valid or not

If an exception already occurred in IF or ID the corresponding instruction is not executed anymore. Additionally a valid exception is never overwritten. For example an instruction fetch access fault is never overwritten by a load store access fault.

### Issue

The issue stage itself is not a real stage in the sense that it is pipelined, it is still part of the decode stage. The purpose of the issue stage is to find out whether we can issue the current top of the scoreboard to one of the functional units. It therefore takes into account whether the any other FU has or is going to write the destination register of the current instruction and whether or not the necessary functional unit is currently busy. If the FU is not busy and there are no dependencies we can issue the instruction to the execute stage.


### Compressed Decoder
The compressed decoders purpose is to expand a compressed instruction (16 bit) to its 32 bit equivalent.


## Execute Stage (EX)

### Read Operands

The read operands stage is still part of the scoreboard but conceptually lies at the boundary between ID and EX. The operands where read in the previous cycle but we can still use forwarding to get the source operands from either:

1. Register file
2. Scoreboard (Forwarding)
4. Immediate field

The scoreboard and forwarding are mutually exclusive. The selection logic is a classical priority selection giving precedence to results form the scoreboard/FU over the register file.

To obtain the right register value we need to poll the scoreboard for both source operands.

### Write-Back

The write-back stage writes the results from the FU back to the scoreboard. They are committed in-order in the next stage.

## Commit Stage (Commit)

The commit stage is the single commit point in the whole architecture. Everything prior to this stage was just computed in a temporary fashion. This is also the only point where an exception can occur.
The commit stage is entirely decoupled from the rest of the pipeline. It has access to the scoreboard which issues finished instructions in-order to the commit stage.

### CSR Register File

The CSR register file contains all registers which are not directly related to arithmetic instructions. It contains the following registers supervisor registers:

| **Register** | **Address** |                      **Description**                      |
|--------------|-------------|-----------------------------------------------------------|
| sstatus      | 0x100       | Supervisor status register                                |
| sedeleg      | 0x102       | Supervisor exception delegation register (maybe external) |
| sideleg      | 0x103       | Supervisor interrupt delegation register (maybe external) |
| sie          | 0x104       | Supervisor interrupt-enable register (maybe external)     |
| stvec        | 0x105       | Supervisor trap handler base address                      |
| sscratch     | 0x140       | Scratch register for supervisor trap handler              |
| sepc         | 0x141       | Supervisor exception program counter                      |
| scause       | 0x142       | Supervisor trap cause                                     |
| stval        | 0x143       | Supervisor bad address or instruction                     |
| sip          | 0x144       | Supervisor interrupt pending (maybe external)             |
| sptbr        | 0x180       | Page-table base register                                  |
| tlbflush     | ?           | Flush TLB                                                 |
| cflush       | ?           | Flush Cache                                               |

And the following machine mode CSR registers:

|     **Register**    |  **Address**   |                    **Description**                     |
| ------------------- | -------------- | ------------------------------------------------------ |
| mvendorid           | 0xF11          | Vendor ID                                              |
| marchid             | 0xF12          | Architecture ID                                        |
| mimpid              | 0xF13          | Implementation ID                                      |
| mhartid             | 0xF14          | Hardware thread ID                                     |
| mstatus             | 0x300          | Machine status register                                |
| medeleg             | 0x302          | Machine exception delegation register (maybe external) |
| mideleg             | 0x303          | Machine interrupt delegation register (maybe external) |
| mie                 | 0x304          | Machine interrupt-enable register (maybe external)     |
| mtvec               | 0x305          | Machine trap handler base address                      |
| mscratch            | 0x340          | Machine register for machine trap handler              |
| mepc                | 0x341          | Machine exception program counter                      |
| mcause              | 0x342          | Machine trap cause                                     |
| mtval               | 0x343          | Machine bad address or instruction                     |
| mip                 | 0x344          | Machine interrupt pending (maybe external)             |
| mcycle              | 0xB00          | Machine cycle counter                                  |
| minstret            | 0xB02          | Machine instruction-retired counter                    |
| Performance Counter | 0xB03 -- 0xB9F | Machine performance-monitoring counter                 |

We need to be careful when altering some of the register. Some of those registers would potentially lead to different behavior (e.g.: mstatus by enabling address translation).

## MMU


## LSU

### Memory Arbiter

The memory arbiter's purpose is to arbitrate the memory accesses coming/going from/to the PTW, store queue and load requests. On a flush it needs to wait for all previous transactions to return. We currently do not have another way to squash load and stores that already went into the memory hierarchy.

### Store Queue

The store queue keeps track of all stores. It has two entries: One is for already committed instructions and one is for outstanding instructions. On a flush only the instruction which has the already committed instruction saved persists its data. But on a flush it can't request further to the memory since this could potentially stall us indefinitely because of the property of the memory arbiter (see above).

The store queue works with physical addresses only. At the time when they are committed the translation is correct. Furthermore the store queue directly outputs the address and value of the instruction it is going to commit since any subsequent store also needs to check for the address.

# Cache

## Interface

```verilog
    input  logic                                          clk,
    input  logic                                          rst_n,

    // Data Port (TLB or CORE )
    input  logic [DATA_WIDTH-1:0]                         data_wdata_i,
    input  logic                                          data_req_i,
    input  logic [BE_WIDTH-1:0]                           data_be_i,
    input  logic                                          data_we_i,
    input  logic [ADDR_WIDTH-1:0]                         data_add_i,
    input  logic                                          data_abort_i,
    input  logic [ID_WIDTH-1:0]                           data_ID_i,
    output logic                                          data_gnt_o,

    output logic [DATA_WIDTH-1:0]                         data_r_rdata_o,
    output logic                                          data_r_valid_o,
    input  logic [ID_WIDTH-1:0]                           data_r_ID_o,
    input  logic                                          data_r_gnt_i,

    //Service Port (32bit)
    input  logic                                          conf_req_i,
    input  logic [31:0]                                   conf_addr_i,
    input  logic                                          conf_wen_i,
    input  logic [31:0]                                   conf_wdata_i,
    input  logic [3:0]                                    conf_be_i,
    input  logic [PE_ID_WIDTH-1:0]                        conf_id_i,
    output logic                                          conf_gnt_o,

    output logic                                          conf_r_valid_o,
    output logic                                          conf_r_opc_o,
    output logic [PE_ID_WIDTH-1:0]                        conf_r_id_o,
    output logic [31:0]                                   conf_r_rdata_o,
```
