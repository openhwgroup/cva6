// (C) 2001-2024 Intel Corporation. All rights reserved.
// Your use of Intel Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files from any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Intel Program License Subscription 
// Agreement, Intel FPGA IP License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Intel and sold by 
// Intel or its authorized distributors.  Please refer to the applicable 
// agreement for further details.


// (C) 2001-2011 Altera Corporation. All rights reserved.
// Your use of Altera Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Altera Program License Subscription 
// Agreement, Altera MegaCore Function License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Altera and sold by 
// Altera or its authorized distributors.  Please refer to the applicable 
// agreement for further details.

`timescale 1 ns / 1 ns

module cva6_intel_altera_merlin_slave_agent_1921_b6r3djy 
#(
   // Packet parameters
   parameter PKT_BEGIN_BURST           = 81,
   parameter PKT_DATA_H                = 31,
   parameter PKT_DATA_L                = 0,
   parameter PKT_SYMBOL_W              = 8,
   parameter PKT_BYTEEN_H              = 71,
   parameter PKT_BYTEEN_L              = 68,
   parameter PKT_ADDR_H                = 63,
   parameter PKT_ADDR_L                = 32,
   parameter PKT_TRANS_LOCK            = 87,
   parameter PKT_TRANS_COMPRESSED_READ = 67,
   parameter PKT_TRANS_POSTED          = 66, 
   parameter PKT_TRANS_WRITE           = 65,
   parameter PKT_TRANS_READ            = 64,
   parameter PKT_SRC_ID_H              = 74,
   parameter PKT_SRC_ID_L              = 72,
   parameter PKT_DEST_ID_H             = 77,
   parameter PKT_DEST_ID_L             = 75,
   parameter PKT_BURSTWRAP_H           = 85,
   parameter PKT_BURSTWRAP_L           = 82,
   parameter PKT_BYTE_CNT_H            = 81,
   parameter PKT_BYTE_CNT_L            = 78,
   parameter PKT_PROTECTION_H          = 86,
   parameter PKT_PROTECTION_L          = 86,
   parameter PKT_RESPONSE_STATUS_H     = 89,
   parameter PKT_RESPONSE_STATUS_L     = 88,
   parameter PKT_BURST_SIZE_H          = 92,
   parameter PKT_BURST_SIZE_L          = 90,
   parameter PKT_ORI_BURST_SIZE_L      = 93,
   parameter PKT_ORI_BURST_SIZE_H      = 95,
   parameter PKT_POISON_L              = 97,
   parameter PKT_POISON_H              = 97,
   parameter PKT_DATACHK_L             = 98,
   parameter PKT_DATACHK_H             = 98,
   parameter PKT_SAI_L                 = 99,
   parameter PKT_SAI_H                 = 99,
   parameter PKT_ADDRCHK_L             = 100,
   parameter PKT_ADDRCHK_H             = 100,
   parameter PKT_USER_DATA_L           = 101,
   parameter PKT_USER_DATA_H           = 101,
  

   parameter ST_DATA_W                 = 102,
   parameter ST_CHANNEL_W              = 32,
   parameter ROLE_BASED_USER           = 0,
   parameter SYNC_RESET                = 0,

   parameter USE_PKT_DATACHK           = 1,

   // Slave parameters
   parameter ADDR_W           = PKT_ADDR_H - PKT_ADDR_L + 1,
   parameter AVS_DATA_W       = PKT_DATA_H - PKT_DATA_L + 1,
   parameter AVS_BURSTCOUNT_W = 4,
   parameter PKT_SYMBOLS      = AVS_DATA_W / PKT_SYMBOL_W,

   // Slave agent parameters
   parameter USE_MEMORY_BLOCKS     = 1,
   parameter PREVENT_FIFO_OVERFLOW = 0,
   parameter SUPPRESS_0_BYTEEN_CMD = 1,
   parameter USE_READRESPONSE      = 0,
   parameter USE_WRITERESPONSE     = 0,

   // Derived slave parameters
   parameter AVS_BE_W = PKT_BYTEEN_H - PKT_BYTEEN_L + 1,
   parameter BURST_SIZE_W = 3,

   // Derived FIFO width
   parameter FIFO_DATA_W = ST_DATA_W + 1,
   
   // ECC parameter
   parameter ECC_ENABLE = 0
) (
   input                         clk,
   input                         reset,

   // Universal-Avalon anti-slave
   output [ADDR_W-1:0]    m0_address,
   output [AVS_BURSTCOUNT_W-1:0] m0_burstcount,
   output [AVS_BE_W-1:0]         m0_byteenable,
   output                        m0_read,
   input [AVS_DATA_W-1:0]        m0_readdata,
   input                         m0_waitrequest,
   output                        m0_write,
   output [AVS_DATA_W-1:0]       m0_writedata,
   input                         m0_readdatavalid,
   output                        m0_debugaccess,
   output                        m0_lock,
   input [1:0]                   m0_response,
   input                         m0_writeresponsevalid,

   // Avalon-ST FIFO interfaces.
   // Note: there's no need to include the "data" field here, at least for
   // reads, since readdata is filled in from slave info.  To keep life
   // simple, have a data field, but fill it with 0s.
   // Av-st response fifo source interface
   output reg [FIFO_DATA_W-1:0]  rf_source_data,
   output                        rf_source_valid,
   output                        rf_source_startofpacket,
   output                        rf_source_endofpacket,
   input                         rf_source_ready,

   // Av-st response fifo sink interface
   input [FIFO_DATA_W-1:0]       rf_sink_data,
   input                         rf_sink_valid,
   input                         rf_sink_startofpacket,
   input                         rf_sink_endofpacket,
   output     reg                rf_sink_ready,

   // Av-st readdata fifo src interface, data and response
   // extra 2 bits for storing RESPONSE STATUS
   output [AVS_DATA_W+1:0]       rdata_fifo_src_data,
   output                        rdata_fifo_src_valid,
   input                         rdata_fifo_src_ready,

   // Av-st readdata fifo sink interface
   input [AVS_DATA_W+1:0]        rdata_fifo_sink_data,
   input                         rdata_fifo_sink_valid,
   output                        rdata_fifo_sink_ready,
   input                         rdata_fifo_sink_error,

   // Av-st sink command packet interface
   output                        cp_ready,
   input                         cp_valid,
   input [ST_DATA_W-1:0]         cp_data,
   input [ST_CHANNEL_W-1:0]      cp_channel,
   input                         cp_startofpacket,
   input                         cp_endofpacket,

   // Av-st source response packet interface
   input                         rp_ready,
   output reg                    rp_valid,
   output reg [ST_DATA_W-1:0]    rp_data,
   output                        rp_startofpacket,
   output                        rp_endofpacket
);
   // ------------------------------------------------
   // Local Parameters
   // ------------------------------------------------
   localparam DATA_W       = PKT_DATA_H - PKT_DATA_L + 1;
   localparam BE_W         = PKT_BYTEEN_H - PKT_BYTEEN_L + 1;
   localparam MID_W        = PKT_SRC_ID_H - PKT_SRC_ID_L + 1;
   localparam SID_W        = PKT_DEST_ID_H - PKT_DEST_ID_L + 1;
   localparam BYTE_CNT_W   = PKT_BYTE_CNT_H - PKT_BYTE_CNT_L + 1;
   localparam BURSTWRAP_W  = PKT_BURSTWRAP_H - PKT_BURSTWRAP_L + 1;
   localparam BURSTSIZE_W  = PKT_BURST_SIZE_H - PKT_BURST_SIZE_L + 1;
   localparam BITS_TO_MASK = log2ceil(PKT_SYMBOLS);
   localparam MAX_BURST    = 1 << (AVS_BURSTCOUNT_W - 1);
   localparam BURSTING     = (MAX_BURST > PKT_SYMBOLS);
   localparam PKT_DATACHK_W    = (USE_PKT_DATACHK)? PKT_DATACHK_H - PKT_DATACHK_L + 1: 1;

   // --------------------------------------------------
   // Ceil(log2()) function log2ceil of 4 = 2
   // --------------------------------------------------
   function integer log2ceil;
      input reg[63:0] val;
      reg [63:0] i;
   
      begin
         i = 1;
         log2ceil = 0;

         while (i < val) begin
            log2ceil = log2ceil + 1;
            i = i << 1;
         end
      end
   endfunction     

   // --------------------------------------------------
   // calcParity: calculates byte-level parity signal 
   // --------------------------------------------------
   function reg [PKT_DATACHK_W-1:0] calcParity (
       input [DATA_W-1:0] data
    );
       for (int i=0; i<PKT_DATACHK_W; i++)
           calcParity[i] = ~(^ data[i*8 +:8]);
   endfunction


   // ------------------------------------------------
   // Signals
   // ------------------------------------------------
   wire [DATA_W-1:0]      cmd_data;
   wire [BE_W-1:0]        cmd_byteen;
   wire [ADDR_W-1:0]      cmd_addr;
   wire [MID_W-1:0]       cmd_mid;
   wire [SID_W-1:0]       cmd_sid;
   wire                   cmd_read;
   wire                   cmd_write;
   wire                   cmd_compressed;
   wire                   cmd_posted;
   wire [BYTE_CNT_W-1:0]  cmd_byte_cnt;
   wire [BURSTWRAP_W-1:0] cmd_burstwrap;
   wire [BURSTSIZE_W-1:0] cmd_burstsize;
   wire                   cmd_debugaccess;

   wire                   suppress_cmd;
   wire                   byteen_asserted;
   wire                   suppress_read;
   wire                   suppress_write;
   wire                   needs_response_synthesis;
   wire                   generate_response;

  //signals for additional latency due to different memory
   wire [AVS_DATA_W-1:0]  m0_readdata_q;
   wire                   m0_readdatavalid_q;
   wire [1:0]             m0_response_q;
   wire                   m0_writeresponsevalid_q;
   reg [AVS_DATA_W-1:0]   m0_readdata_1;
   reg                    m0_readdatavalid_1;
   reg [1:0]              m0_response_1;
   reg                    m0_writeresponsevalid_1;
   reg [AVS_DATA_W-1:0]   m0_readdata_2;
   reg                    m0_readdatavalid_2;
   reg [1:0]              m0_response_2;
   reg                    m0_writeresponsevalid_2;

   // Assign command fields
   assign cmd_data         = cp_data[PKT_DATA_H  :PKT_DATA_L  ];
   assign cmd_byteen       = cp_data[PKT_BYTEEN_H:PKT_BYTEEN_L];
   assign cmd_addr         = cp_data[PKT_ADDR_H  :PKT_ADDR_L  ];
   assign cmd_compressed   = cp_data[PKT_TRANS_COMPRESSED_READ];
   assign cmd_posted       = cp_data[PKT_TRANS_POSTED];
   assign cmd_write        = cp_data[PKT_TRANS_WRITE];
   assign cmd_read         = cp_data[PKT_TRANS_READ];
   assign cmd_mid          = cp_data[PKT_SRC_ID_H :PKT_SRC_ID_L];
   assign cmd_sid          = cp_data[PKT_DEST_ID_H:PKT_DEST_ID_L];
   assign cmd_byte_cnt     = cp_data[PKT_BYTE_CNT_H:PKT_BYTE_CNT_L];
   assign cmd_burstwrap    = cp_data[PKT_BURSTWRAP_H:PKT_BURSTWRAP_L];
   assign cmd_burstsize    = cp_data[PKT_BURST_SIZE_H:PKT_BURST_SIZE_L];
   assign cmd_debugaccess  = cp_data[PKT_PROTECTION_L];

   // Local "ready_for_command" signal: deasserted when the agent is unable to accept
   // another command, e.g. rdv FIFO is full, (local readdata storage is full &&
   // ~rp_ready), ...
   // Say, this could depend on the type of command, for example, even if the
   // rdv FIFO is full, a write request can be accepted.  For later.
   wire ready_for_command;

   wire local_lock  = cp_valid & cp_data[PKT_TRANS_LOCK];
   wire local_write = cp_valid & cp_data[PKT_TRANS_WRITE];
   wire local_read  = cp_valid & cp_data[PKT_TRANS_READ];
   wire local_compressed_read = cp_valid & cp_data[PKT_TRANS_COMPRESSED_READ];
   wire nonposted_write_endofpacket = ~cp_data[PKT_TRANS_POSTED] & local_write & cp_endofpacket;

   // num_symbols is PKT_SYMBOLS, appropriately sized.
   wire [31:0] int_num_symbols = PKT_SYMBOLS;
   wire [BYTE_CNT_W-1:0] num_symbols = int_num_symbols[BYTE_CNT_W-1:0];

   // Generation of internal reset synchronization
   reg internal_sclr;
   generate if (SYNC_RESET == 1) begin : rst_syncronizer
      always @ (posedge clk) begin
         internal_sclr <= reset;
      end
   end
   endgenerate

  generate
     if (SYNC_RESET ==0 ) begin : async0 
           always_ff @(posedge clk, posedge reset) begin
              if (reset) begin
                  m0_readdata_2 <= '0;
                  m0_readdatavalid_2 <= '0;
                  m0_response_2 <= '0;
                  m0_writeresponsevalid_2 <= '0;
              end 
              else begin
                  m0_readdata_2 <= m0_readdata;
                  m0_readdatavalid_2 <= m0_readdatavalid;
                  m0_response_2 <= m0_response;
                  m0_writeresponsevalid_2 <= m0_writeresponsevalid;
              end
           end //@always_ff
      end // async0

      else begin :sync0
           always_ff @(posedge clk) begin
              if (internal_sclr) begin
                  m0_readdata_2 <= '0;
                  m0_readdatavalid_2 <= '0;
                  m0_response_2 <= '0;
                  m0_writeresponsevalid_2 <= '0;
              end 
              else begin 
                  m0_readdata_2 <= m0_readdata;
                  m0_readdatavalid_2 <= m0_readdatavalid;
                  m0_response_2 <= m0_response;
                  m0_writeresponsevalid_2 <= m0_writeresponsevalid;
              end
           end //@always_ff
      end // sync0
endgenerate

generate
     if (SYNC_RESET ==0 ) begin : async1 
           always_ff @(posedge clk, posedge reset) begin
              if (reset) begin
                  m0_readdata_1 <= '0;
                  m0_readdatavalid_1 <= '0;
                  m0_response_1 <= '0;
                  m0_writeresponsevalid_1 <= '0;
              end 
              else begin
                  m0_readdata_1 <= m0_readdata_2;
                  m0_readdatavalid_1 <= m0_readdatavalid_2;
                  m0_response_1 <= m0_response_2;
                  m0_writeresponsevalid_1 <= m0_writeresponsevalid_2;
              end
           end //@always_ff
      end // async1

      else begin :sync1
           always_ff @(posedge clk) begin
              if (internal_sclr) begin
                  m0_readdata_1 <= '0;
                  m0_readdatavalid_1 <= '0;
                  m0_response_1 <= '0;
                  m0_writeresponsevalid_1 <= '0;
              end 
              else begin 
                  m0_readdata_1 <= m0_readdata_2;
                  m0_readdatavalid_1 <= m0_readdatavalid_2;
                  m0_response_1 <= m0_response_2;
                  m0_writeresponsevalid_1 <= m0_writeresponsevalid_2;
              end
           end //@always_ff
      end // sync1
endgenerate


  generate
      if (USE_MEMORY_BLOCKS) begin : Using_M20k_with_2_clk_latency
          assign m0_readdata_q = m0_readdata_1;
          assign m0_readdatavalid_q = m0_readdatavalid_1;
          assign m0_response_q = m0_response_1;
          assign m0_writeresponsevalid_q = m0_writeresponsevalid_1;
      end else begin : Using_ALM_memory_with_1_clk_latency
          assign m0_readdata_q = m0_readdata;
          assign m0_readdatavalid_q = m0_readdatavalid;
          assign m0_response_q = m0_response;
          assign m0_writeresponsevalid_q = m0_writeresponsevalid;
      end
   endgenerate



   generate
      if (PREVENT_FIFO_OVERFLOW) begin : prevent_fifo_overflow_block
         // ---------------------------------------------------
         // Backpressure if the slave says to, or if FIFO overflow may occur.
         // 
         // All commands are backpressured once the FIFO is full
         // even if they don't need storage. This breaks a long
         // combinatorial path from the master read/write through
         // this logic and back to the master via the backpressure
         // path.
         //
         // To avoid a loss of throughput the FIFO will be parameterized 
         // one slot deeper. The extra slot should never be used in normal
         // operation, but should a slave misbehave and accept one more
         // read than it should then backpressure will kick in.
         //
         // An example: assume a slave with MPRT = 2. It can accept a
         // command sequence RRWW without backpressuring. If the FIFO is
         // only 2 deep, we'd backpressure the writes leading to loss of
         // throughput. If the FIFO is 3 deep, we'll only backpressure when
         // RRR... which is an illegal condition anyway.
         // ---------------------------------------------------

         assign ready_for_command = rf_source_ready;
         assign cp_ready = (~m0_waitrequest | suppress_cmd) && ready_for_command;

      end else begin : no_prevent_fifo_overflow_block

         // Do not suppress the command or the slave will
         // not be able to waitrequest
         assign ready_for_command = 1'b1;
         // Backpressure only if the slave says to.
         assign cp_ready = ~m0_waitrequest | suppress_cmd;

      end
   endgenerate

   generate if (SUPPRESS_0_BYTEEN_CMD && !BURSTING) begin : suppress_0_byteen_cmd_non_bursting
      assign byteen_asserted  = |cmd_byteen;
      assign suppress_read    = ~byteen_asserted;
      assign suppress_write   = ~byteen_asserted;
      assign suppress_cmd     = ~byteen_asserted;
   end else if (SUPPRESS_0_BYTEEN_CMD && BURSTING) begin: suppress_0_byteen_cmd_bursting
      assign byteen_asserted  = |cmd_byteen;
      assign suppress_read    = ~byteen_asserted;
      assign suppress_write   = 1'b0;
      assign suppress_cmd     = ~byteen_asserted && cmd_read;
   end else begin : no_suppress_0_byteen_cmd
      assign suppress_read    = 1'b0;
      assign suppress_write   = 1'b0;
      assign suppress_cmd     = 1'b0;
   end
   endgenerate

   // -------------------------------------------------------------------
   // Extract avalon signals from command packet.
   // -------------------------------------------------------------------
   // Mask off the lower bits of address.
   // The burst adapter before this component will break narrow sized packets
   // into sub-bursts of length 1. However, the packet addresses are preserved,
   // which means this component may see size-aligned addresses.
   //
   // Masking ensures that the addresses seen by an Avalon slave are aligned to 
   // the full data width instead of the size.
   //
   // Example:
   // output from burst adapter (datawidth=4, size=2 bytes):
   // subburst1 addr=0, subburst2 addr=2, subburst3 addr=4, subburst4 addr=6
   // expected output from slave agent:
   // subburst1 addr=0, subburst2 addr=0, subburst3 addr=4, subburst4 addr=4
   generate
      if (BITS_TO_MASK > 0) begin : mask_address
         if(ADDR_W == BITS_TO_MASK)
             assign m0_address = { cmd_addr[ADDR_W-1:BITS_TO_MASK-1], {BITS_TO_MASK-1{1'b0}} };
         else
             assign m0_address = { cmd_addr[ADDR_W-1:BITS_TO_MASK], {BITS_TO_MASK{1'b0}} };

      end else begin : no_mask_address

         assign m0_address = cmd_addr;

      end
   endgenerate

   assign m0_byteenable = cmd_byteen;
   assign m0_writedata  = cmd_data;

   // Note: no Avalon-MM slave in existence accepts uncompressed read bursts -
   // this sort of burst exists only in merlin fabric ST packets. What to do
   // if we see such a burst? All beats in that burst need to be transmitted
   // to the slave so we have enough space-time for byteenable expression.
   //
   // There can be multiple bursts in a packet, but only one beat per burst
   // in <most> cases. The exception is when we've decided not to insert a
   // burst adapter for efficiency reasons, in which case this agent is also
   // responsible for driving burstcount to 1 on each beat of an uncompressed
   // read burst.

   assign m0_read = ready_for_command & !suppress_read & (local_compressed_read | local_read);

   generate 
       // AVS_BURSTCOUNT_W and BYTE_CNT_W may not be equal.  Assign m0_burstcount
       // from a sub-range, or 0-pad, as appropriate.
       if (AVS_BURSTCOUNT_W > BYTE_CNT_W) begin : m0_burstcount_zero_pad
          wire [AVS_BURSTCOUNT_W - BYTE_CNT_W - 1 : 0] zero_pad = {(AVS_BURSTCOUNT_W - BYTE_CNT_W) {1'b0}};
          assign m0_burstcount = (local_read & ~local_compressed_read) ?
             {zero_pad, num_symbols} :
             {zero_pad, cmd_byte_cnt};
       end
       else begin : m0_burstcount_no_pad
          assign m0_burstcount = (local_read & ~local_compressed_read) ? 
          num_symbols[AVS_BURSTCOUNT_W-1:0] : 
          cmd_byte_cnt[AVS_BURSTCOUNT_W-1:0];
       end
   endgenerate

   assign m0_write = ready_for_command & local_write & !suppress_write;
   assign m0_lock  = ready_for_command & local_lock & (m0_read | m0_write);
   assign m0_debugaccess  = cmd_debugaccess;

   // -------------------------------------------------------------------
   // Indirection layer for response packet values.  Some may always wire
   // directly from the slave translator; others will no doubt emerge from
   // various FIFOs.
   // What to put in resp_data when a write occured? Answer: it does not
   // matter, because only response status is needed for non-posted writes,
   // and the packet already has a field for that.
   //
   // We use the rdata_fifo to store write responses as well. This allows us
   // to handle backpressure on the response path, and allows write response
   // merging.
   assign rdata_fifo_src_valid = m0_readdatavalid_q | m0_writeresponsevalid_q;
   assign rdata_fifo_src_data  = {m0_response_q, m0_readdata_q};

   // ------------------------------------------------------------------
   // Generate a token when read commands are suppressed. The token
   // is stored in the response FIFO, and will be used to synthesize 
   // a read response. The same token is used for non-posted write
   // response synthesis.
   //
   // Note: this token is not generated for suppressed uncompressed read cycles;
   // the burst uncompression logic at the read side of the response FIFO
   // generates the correct number of responses.
   //
   // When the slave can return the response, let it do its job. Don't 
   // synthesize a response in that case, unless we've suppressed the
   // the last transfer in a write sub-burst.
   // ------------------------------------------------------------------
   wire write_end_of_subburst;
   assign needs_response_synthesis = ((local_read | local_compressed_read) & suppress_read) || 
                                        (!USE_WRITERESPONSE && nonposted_write_endofpacket) ||
                                        (USE_WRITERESPONSE && write_end_of_subburst && suppress_write);

   // Avalon-ST interfaces to external response FIFO.
   //
   // For efficiency, when synthesizing a write response we only store a non-posted write 
   // transaction at its endofpacket, even if it was split into multiple sub-bursts.
   //
   // When not synthesizing write responses, we store each sub-burst in the FIFO.
   // Each sub-burst to the slave will return a response, which corresponds to one 
   // entry in the FIFO. We merge all the sub-burst responses on the final
   // sub-burst and send it on the response channel.

   wire internal_cp_endofburst;
   wire [31:0] minimum_bytecount_wire = PKT_SYMBOLS; // to solve qis warning
   wire [AVS_BURSTCOUNT_W-1:0] minimum_bytecount;

   assign minimum_bytecount = minimum_bytecount_wire[AVS_BURSTCOUNT_W-1:0];
   assign internal_cp_endofburst = (cmd_byte_cnt == minimum_bytecount);
   assign write_end_of_subburst = local_write & internal_cp_endofburst;

   assign rf_source_valid = (local_read | local_compressed_read | (nonposted_write_endofpacket && !USE_WRITERESPONSE) | (USE_WRITERESPONSE && internal_cp_endofburst && local_write))
                             & ready_for_command & cp_ready;
   assign rf_source_startofpacket = cp_startofpacket;
   assign rf_source_endofpacket   = cp_endofpacket;
   always @* begin
      // default: assign every command packet field to the response FIFO...
      rf_source_data                                  = {1'b0, cp_data};

      // ... and override select fields as needed.
      rf_source_data[FIFO_DATA_W-1]                      = needs_response_synthesis;
      rf_source_data[PKT_DATA_H   :PKT_DATA_L]           = {DATA_W {1'b0}};
      rf_source_data[PKT_BYTEEN_H :PKT_BYTEEN_L]         = cmd_byteen;
      rf_source_data[PKT_ADDR_H   :PKT_ADDR_L]           = cmd_addr;
      rf_source_data[PKT_TRANS_COMPRESSED_READ]          = cmd_compressed;
      rf_source_data[PKT_TRANS_POSTED]                   = cmd_posted;
      rf_source_data[PKT_TRANS_WRITE]                    = cmd_write;
      rf_source_data[PKT_TRANS_READ]                     = cmd_read;
      rf_source_data[PKT_SRC_ID_H :PKT_SRC_ID_L]         = cmd_mid;
      rf_source_data[PKT_DEST_ID_H:PKT_DEST_ID_L]        = cmd_sid;
      rf_source_data[PKT_BYTE_CNT_H:PKT_BYTE_CNT_L]      = cmd_byte_cnt;
      rf_source_data[PKT_BURSTWRAP_H:PKT_BURSTWRAP_L]    = cmd_burstwrap;
      rf_source_data[PKT_BURST_SIZE_H:PKT_BURST_SIZE_L]  = cmd_burstsize;
      rf_source_data[PKT_PROTECTION_H:PKT_PROTECTION_L]  = '0;
      rf_source_data[PKT_PROTECTION_L]                   = cmd_debugaccess;
   end

   wire uncompressor_source_valid;
   wire [BURSTSIZE_W-1:0] uncompressor_burstsize;
   wire last_write_response;

   // last_write_response indicates the last response of the broken-up write burst (sub-bursts).
   // At this time, the final merged response is sent, and rp_valid is only asserted
   // once for the whole burst.
   generate
      if (USE_WRITERESPONSE) begin
         assign last_write_response = rf_sink_data[PKT_TRANS_WRITE] & rf_sink_endofpacket;
         always @* begin
            if (rf_sink_data[PKT_TRANS_WRITE] == 1) 
               rp_valid =   ((rdata_fifo_sink_valid | generate_response) & last_write_response & !rf_sink_data[PKT_TRANS_POSTED]);
            else
               rp_valid = (rdata_fifo_sink_valid | uncompressor_source_valid);
         end
      end else begin
         assign last_write_response = 1'b0;
         always @* begin
            rp_valid =  (rdata_fifo_sink_valid | uncompressor_source_valid);
         end
      end
   endgenerate

   // ------------------------------------------------------------------
   // Response merging
   // ------------------------------------------------------------------
   reg [1:0] current_response;
   reg [1:0] response_merged;
   generate
     if (USE_WRITERESPONSE) begin : response_merging_all
        reg first_write_response;
        reg reset_merged_output;
        reg [1:0] previous_response_in;
        reg [1:0]  previous_response;
   

      if (SYNC_RESET ==0 ) begin : async_reg0 
           always_ff @(posedge clk, posedge reset) begin
              if (reset) begin
                 first_write_response  <= 1'b1;
              end 
              else begin // Merging work for write response, for read: previous_response_in = current_response
                 if (rf_sink_valid & (rdata_fifo_sink_valid | generate_response) & rf_sink_data[PKT_TRANS_WRITE]) begin
                    first_write_response <= 1'b0;
                    if (rf_sink_endofpacket)
                       first_write_response <= 1'b1;
                 end
              end
           end //@always_ff
      end // async_reg0

      else begin :sync_reg0
           always_ff @(posedge clk) begin
              if (internal_sclr) begin
                 first_write_response  <= 1'b1;
              end 
              else begin // Merging work for write response, for read: previous_response_in = current_response
                 if (rf_sink_valid & (rdata_fifo_sink_valid | generate_response) & rf_sink_data[PKT_TRANS_WRITE]) begin
                    first_write_response <= 1'b0;
                    if (rf_sink_endofpacket)
                       first_write_response <= 1'b1;
                 end
              end
           end //@always_ff
      end // sync_reg0

        always_comb begin
           current_response = generate_response ? 2'b00 : rdata_fifo_sink_data[AVS_DATA_W+1:AVS_DATA_W] | {2{rdata_fifo_sink_error}};
           reset_merged_output = first_write_response && (rdata_fifo_sink_valid || generate_response);
           previous_response_in = reset_merged_output ? current_response : previous_response;
           response_merged = current_response >= previous_response ? current_response: previous_response_in;
        end
      
      if (SYNC_RESET == 0) begin : async_reg1
  
           always_ff @(posedge clk or posedge reset) begin
              if (reset) begin 
                 previous_response <= 2'b00;
              end
              else begin
                 if (rf_sink_valid & (rdata_fifo_sink_valid || generate_response)) begin
                    previous_response <= response_merged;
                 end
              end
           end
      end // async_reg1

      else begin : sync_reg1
           always_ff @(posedge clk ) begin
              if (internal_sclr) begin 
                 previous_response <= 2'b00;
              end
              else begin
                 if (rf_sink_valid & (rdata_fifo_sink_valid || generate_response)) begin
                    previous_response <= response_merged;
                 end
              end
           end
      end // sync_reg1


     end else begin : response_merging_read_only
        always @* begin
           current_response = generate_response ? 2'b00: rdata_fifo_sink_data[AVS_DATA_W+1:AVS_DATA_W] | 
                                                         {2{rdata_fifo_sink_error}};
           response_merged = current_response;
        end
     end
   endgenerate

   assign generate_response = rf_sink_data[FIFO_DATA_W-1];

   wire [BYTE_CNT_W-1:0]  rf_sink_byte_cnt   = rf_sink_data[PKT_BYTE_CNT_H:PKT_BYTE_CNT_L];
   wire                   rf_sink_compressed = rf_sink_data[PKT_TRANS_COMPRESSED_READ];
   wire [BURSTWRAP_W-1:0] rf_sink_burstwrap  = rf_sink_data[PKT_BURSTWRAP_H:PKT_BURSTWRAP_L];
   wire [BURSTSIZE_W-1:0] rf_sink_burstsize  = rf_sink_data[PKT_BURST_SIZE_H:PKT_BURST_SIZE_L];
   wire [ADDR_W-1:0]      rf_sink_addr       = rf_sink_data[PKT_ADDR_H:PKT_ADDR_L];
   // a non posted write response is always completed in 1 cycle. Modify the startofpacket signal to 1'b1 instead of taking whatever is in the rf_fifo
   wire rf_sink_startofpacket_wire = rf_sink_data[PKT_TRANS_WRITE] ? 1'b1 : rf_sink_startofpacket;    

   wire [BYTE_CNT_W-1:0]   burst_byte_cnt;
   wire [BURSTWRAP_W-1:0]  rp_burstwrap;
   wire [ADDR_W-1:0]       rp_address;
   wire                    rp_is_compressed;
   wire                    ready_for_response;

   // ------------------------------------------------------------------
   // We're typically ready for a response if the network is ready. There
   // is one exception:
   //
   // If the slave issues write responses, we only issue a merged response on 
   // the final sub-burst. As a result, we only care about response channel 
   // availability on the final burst when we send out the merged response.
   // ------------------------------------------------------------------
   assign ready_for_response = (USE_WRITERESPONSE) ? 
                            rp_ready || (rf_sink_data[PKT_TRANS_WRITE] && !last_write_response) || rf_sink_data[PKT_TRANS_POSTED]: 
                            rp_ready;

   // ------------------------------------------------------------------
   // Backpressure the readdata fifo if we're supposed to synthesize a response.
   // This may be a read response (for suppressed reads) or a write response
   // (for non-posted writes).
   // ------------------------------------------------------------------
   assign rdata_fifo_sink_ready = rdata_fifo_sink_valid & ready_for_response & ~(rf_sink_valid & generate_response);

   always @* begin
      // By default, return all fields...
      rp_data                                               = rf_sink_data[ST_DATA_W - 1 : 0];

      // ... and override specific fields.
      rp_data[PKT_DATA_H   :PKT_DATA_L]                     = rdata_fifo_sink_data[AVS_DATA_W-1:0];
      // Assignments directly from the response fifo.
      rp_data[PKT_TRANS_POSTED]                             = rf_sink_data[PKT_TRANS_POSTED];
      rp_data[PKT_TRANS_WRITE]                              = rf_sink_data[PKT_TRANS_WRITE];
      rp_data[PKT_SRC_ID_H :PKT_SRC_ID_L]                   = rf_sink_data[PKT_DEST_ID_H : PKT_DEST_ID_L];
      rp_data[PKT_DEST_ID_H:PKT_DEST_ID_L]                  = rf_sink_data[PKT_SRC_ID_H : PKT_SRC_ID_L];
      rp_data[PKT_BYTEEN_H :PKT_BYTEEN_L]                   = rf_sink_data[PKT_BYTEEN_H : PKT_BYTEEN_L];
      rp_data[PKT_PROTECTION_H:PKT_PROTECTION_L]            = rf_sink_data[PKT_PROTECTION_H:PKT_PROTECTION_L];

      // Burst uncompressor assignments
      rp_data[PKT_ADDR_H   :PKT_ADDR_L]                     = rp_address;
      rp_data[PKT_BURSTWRAP_H:PKT_BURSTWRAP_L]              = rp_burstwrap;
      rp_data[PKT_BYTE_CNT_H:PKT_BYTE_CNT_L]                = burst_byte_cnt;
      rp_data[PKT_TRANS_READ]                               = rf_sink_data[PKT_TRANS_READ] | rf_sink_data[PKT_TRANS_COMPRESSED_READ];
      rp_data[PKT_TRANS_COMPRESSED_READ]                    = rp_is_compressed;

      rp_data[PKT_RESPONSE_STATUS_H:PKT_RESPONSE_STATUS_L]  = response_merged;
      rp_data[PKT_BURST_SIZE_H:PKT_BURST_SIZE_L]            = uncompressor_burstsize;
      // bounce the original size back to the master untouched
      rp_data[PKT_ORI_BURST_SIZE_H:PKT_ORI_BURST_SIZE_L]    = rf_sink_data[PKT_ORI_BURST_SIZE_H:PKT_ORI_BURST_SIZE_L];

      if (ROLE_BASED_USER) begin
          if(USE_PKT_DATACHK)begin
             rp_data[PKT_DATACHK_H:PKT_DATACHK_L]              = calcParity(rdata_fifo_sink_data[AVS_DATA_W-1:0]);
          end else begin
             rp_data[PKT_DATACHK_H:PKT_DATACHK_L]              = '0;
          end  

      rp_data[PKT_POISON_H:PKT_POISON_L]                    = '0;
      rp_data[PKT_ADDRCHK_H:PKT_ADDRCHK_L]                  = '0;
      rp_data[PKT_SAI_H:PKT_SAI_L]                          = '0;
      rp_data[PKT_USER_DATA_H:PKT_USER_DATA_L]              = '0;
      end
   end

   // ------------------------------------------------------------------
   // Note: the burst uncompressor may be asked to generate responses for
   // write packets; these are treated the same as single-cycle uncompressed 
   // reads.
   // ------------------------------------------------------------------
   altera_merlin_burst_uncompressor #(
      .ADDR_W               (ADDR_W),
      .BURSTWRAP_W          (BURSTWRAP_W),
      .BYTE_CNT_W           (BYTE_CNT_W),
      .PKT_SYMBOLS          (PKT_SYMBOLS),
      .BURST_SIZE_W         (BURSTSIZE_W),
      .SYNC_RESET (SYNC_RESET)
   ) uncompressor (
      .clk                  (clk),
      .reset                (reset),
      .sink_startofpacket   (rf_sink_startofpacket_wire),
      .sink_endofpacket     (rf_sink_endofpacket),
      .sink_valid           ((rf_sink_valid & (rdata_fifo_sink_valid | generate_response))),
      .sink_ready           (rf_sink_ready),
      .sink_addr            (rf_sink_addr),
      .sink_burstwrap       (rf_sink_burstwrap),
      .sink_byte_cnt        (rf_sink_byte_cnt),
      .sink_is_compressed   (rf_sink_compressed),
      .sink_burstsize       (rf_sink_burstsize),

      .source_startofpacket (rp_startofpacket),
      .source_endofpacket   (rp_endofpacket),
      .source_valid         (uncompressor_source_valid),
      .source_ready         (ready_for_response),
      .source_addr          (rp_address),
      .source_burstwrap     (rp_burstwrap),
      .source_byte_cnt      (burst_byte_cnt),
      .source_is_compressed (rp_is_compressed),
      .source_burstsize     (uncompressor_burstsize)
   );

   //--------------------------------------
   // Assertion: In case slave support response. The slave needs return response in order
   // Ex: non-posted write followed by a read: write response must complete before read data 
   //--------------------------------------
   // synthesis translate_off      
   ERROR_write_response_and_read_response_cannot_happen_same_time:
   assert property ( @(posedge clk)
      disable iff (reset) (reset === 0) |-> !(m0_writeresponsevalid_q  && m0_readdatavalid_q)
   );    
   // synthesis translate_on
endmodule


