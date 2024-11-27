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


// -----------------------------------------------------------
// Legal Notice: (C)2007 Altera Corporation. All rights reserved.  Your
// use of Altera Corporation's design tools, logic functions and other
// software and tools, and its AMPP partner logic functions, and any
// output files any of the foregoing (including device programming or
// simulation files), and any associated documentation or information are
// expressly subject to the terms and conditions of the Altera Program
// License Subscription Agreement or other applicable license agreement,
// including, without limitation, that your use is for the sole purpose
// of programming logic devices manufactured by Altera and sold by Altera
// or its authorized distributors.  Please refer to the applicable
// agreement for further details.
//
// Description: Single clock Avalon-ST FIFO.
// -----------------------------------------------------------

`timescale 1 ns / 1 ns


//altera message_off 10036
module cva6_intel_altera_avalon_sc_fifo_1932_w27kryi
#(
    // --------------------------------------------------
    // Parameters
    // --------------------------------------------------
    parameter SYMBOLS_PER_BEAT    = 1,
    parameter BITS_PER_SYMBOL     = 8,
    parameter FIFO_DEPTH          = 16,
    parameter CHANNEL_WIDTH       = 0,
    parameter ERROR_WIDTH         = 0,
    parameter USE_PACKETS         = 0,
    parameter USE_FILL_LEVEL      = 0,
    parameter USE_STORE_FORWARD   = 0,
    parameter USE_ALMOST_FULL_IF  = 0,
    parameter USE_ALMOST_EMPTY_IF = 0,
    parameter SYNC_RESET          = 0,
    parameter MEM_TYPE            = "M20K",
    // --------------------------------------------------
    // Empty latency is defined as the number of cycles
    // required for a write to deassert the empty flag.
    // For example, a latency of 1 means that the empty
    // flag is deasserted on the cycle after a write.
    //
    // Another way to think of it is the latency for a
    // write to propagate to the output. 
    // 
    // An empty latency of 0 implies lookahead, which is
    // only implemented for the register-based FIFO.
    // --------------------------------------------------
    parameter EMPTY_LATENCY     = 3,
    parameter USE_MEMORY_BLOCKS = 1,

    // --------------------------------------------------
    // Internal Parameters
    // --------------------------------------------------
    parameter DATA_WIDTH  = SYMBOLS_PER_BEAT * BITS_PER_SYMBOL,
    parameter EMPTY_WIDTH = 1,

    parameter ALMOST_FULL_THRESHOLD = FIFO_DEPTH - 1
)
(
    // --------------------------------------------------
    // Ports
    // --------------------------------------------------
    input                       clk,
    input                       reset,

    input [DATA_WIDTH-1: 0]     in_data,
    input                       in_valid,
    input                       in_startofpacket,
    input                       in_endofpacket,
    input [((EMPTY_WIDTH>0) ? (EMPTY_WIDTH-1):0) : 0]     in_empty,
    input [((ERROR_WIDTH>0) ? (ERROR_WIDTH-1):0) : 0]     in_error,
    input [((CHANNEL_WIDTH>0) ? (CHANNEL_WIDTH-1):0): 0]  in_channel,
    output                      in_ready,

    output [DATA_WIDTH-1 : 0]   out_data,
    output reg                  out_valid,
    output                      out_startofpacket,
    output                      out_endofpacket,
    output [((EMPTY_WIDTH>0) ? (EMPTY_WIDTH-1):0) : 0]    out_empty,
    output [((ERROR_WIDTH>0) ? (ERROR_WIDTH-1):0) : 0]    out_error,
    output [((CHANNEL_WIDTH>0) ? (CHANNEL_WIDTH-1):0): 0] out_channel,
    input                       out_ready,

    input [(USE_STORE_FORWARD ? 2 : 1) : 0]   csr_address,
    input                       csr_write,
    input                       csr_read,
    input [31 : 0]              csr_writedata,
    output reg [31 : 0]         csr_readdata,

    output  wire                almost_full_data,
    output  wire                almost_empty_data
);

    // --------------------------------------------------
    // Local Parameters
    // --------------------------------------------------
    localparam ADDR_WIDTH   = log2ceil(FIFO_DEPTH);
    localparam DEPTH        = FIFO_DEPTH;
    localparam PKT_SIGNALS_WIDTH = 2 + EMPTY_WIDTH;
    localparam PAYLOAD_WIDTH     = (USE_PACKETS == 1) ? 
                   2 + EMPTY_WIDTH + DATA_WIDTH + ERROR_WIDTH + CHANNEL_WIDTH:
                   DATA_WIDTH + ERROR_WIDTH + CHANNEL_WIDTH;
    localparam NON_POWER2_DEPTH = 2 ** $clog2(FIFO_DEPTH) != FIFO_DEPTH;
    localparam FIFO_DEPTH_PTR = FIFO_DEPTH - 2;

    // --------------------------------------------------
    // Internal Signals
    // --------------------------------------------------
    genvar i;

    reg [PAYLOAD_WIDTH-1 : 0] mem [DEPTH-1 : 0];
    reg [PAYLOAD_WIDTH-1 : 0] infer_mem [DEPTH-1 : 0];
    reg [ADDR_WIDTH-1 : 0]  wr_ptr;
    reg [ADDR_WIDTH-1 : 0]  rd_ptr;
    reg [DEPTH-1      : 0]  mem_used;

    wire [ADDR_WIDTH-1 : 0] next_wr_ptr;
    wire [ADDR_WIDTH-1 : 0] next_rd_ptr;
    wire [ADDR_WIDTH-1 : 0] incremented_wr_ptr;
    wire [ADDR_WIDTH-1 : 0] incremented_rd_ptr;
    reg  [ADDR_WIDTH-1 : 0] next_incremented_wr_ptr;
    reg  [ADDR_WIDTH-1 : 0] next_incremented_rd_ptr;
    reg                     wr_ptr_overflow;
    reg                     rd_ptr_overflow;

    wire [ADDR_WIDTH-1 : 0] mem_rd_ptr;

    wire read;
    wire write;

    reg empty;
    reg next_empty;
    reg full;
    reg next_full;

    wire [PKT_SIGNALS_WIDTH-1 : 0] in_packet_signals;
    wire [PKT_SIGNALS_WIDTH-1 : 0] out_packet_signals;
    wire [PAYLOAD_WIDTH-1 : 0] in_payload;
    reg  [PAYLOAD_WIDTH-1 : 0] internal_out_payload;
    reg  [PAYLOAD_WIDTH-1 : 0] out_payload;

    reg  internal_out_valid;
    wire internal_out_ready;

    reg  [ADDR_WIDTH : 0] fifo_fill_level;
    reg  [ADDR_WIDTH : 0] fill_level;

    reg  [ADDR_WIDTH-1 : 0]   sop_ptr; 
    wire [ADDR_WIDTH-1 : 0]   curr_sop_ptr;
    reg  [23:0]   almost_full_threshold;
    reg  [23:0]   almost_empty_threshold;
    reg  [23:0]   cut_through_threshold;
    reg  [15:0]   pkt_cnt;
    reg           drop_on_error_en;
    reg           error_in_pkt;
    reg           pkt_has_started;
    reg           sop_has_left_fifo;
    reg           fifo_too_small_r;
    reg           pkt_cnt_eq_zero;
    reg           pkt_cnt_eq_one;

    wire          wait_for_threshold;
    reg           pkt_mode;
    wire          wait_for_pkt;
    wire          ok_to_forward;
    wire          in_pkt_eop_arrive;
    wire          out_pkt_leave;
    wire          in_pkt_start;
    wire          in_pkt_error;
    wire          drop_on_error;
    wire          fifo_too_small;
    wire          out_pkt_sop_leave;
    wire [31:0]   max_fifo_size;
    reg           fifo_fill_level_lt_cut_through_threshold;


    reg internal_sclr;

    always @(posedge clk) begin
         internal_sclr <= reset;
    end

    // --------------------------------------------------
    // Define Payload
    //
    // Icky part where we decide which signals form the
    // payload to the FIFO with generate blocks.
    // --------------------------------------------------
    generate
        if (EMPTY_WIDTH > 0) begin : gen_blk1
            assign in_packet_signals = {in_startofpacket, in_endofpacket, in_empty};
            assign {out_startofpacket, out_endofpacket, out_empty} = out_packet_signals;
        end 
        else begin : gen_blk1_else
            assign out_empty = in_error;
            assign in_packet_signals = {in_startofpacket, in_endofpacket};
            assign {out_startofpacket, out_endofpacket} = out_packet_signals;
        end
    endgenerate

    generate
        if (USE_PACKETS) begin : gen_blk2
            if (ERROR_WIDTH > 0) begin : gen_blk3
                if (CHANNEL_WIDTH > 0) begin : gen_blk4
                    assign in_payload = {in_packet_signals, in_data, in_error, in_channel};
                    assign {out_packet_signals, out_data, out_error, out_channel} = out_payload;
                end
                else begin : gen_blk4_else
                    assign out_channel = in_channel;
                    assign in_payload = {in_packet_signals, in_data, in_error};
                    assign {out_packet_signals, out_data, out_error} = out_payload;
                end
            end
            else begin : gen_blk3_else
                assign out_error = in_error;
                if (CHANNEL_WIDTH > 0) begin : gen_blk5
                    assign in_payload = {in_packet_signals, in_data, in_channel};
                    assign {out_packet_signals, out_data, out_channel} = out_payload;
                end
                else begin : gen_blk5_else
                    assign out_channel = in_channel;
                    assign in_payload = {in_packet_signals, in_data};
                    assign {out_packet_signals, out_data} = out_payload;
                end
            end
        end
        else begin : gen_blk2_else
            assign out_packet_signals = 0;
            if (ERROR_WIDTH > 0) begin : gen_blk6
                if (CHANNEL_WIDTH > 0) begin : gen_blk7
                    assign in_payload = {in_data, in_error, in_channel};
                    assign {out_data, out_error, out_channel} = out_payload;
                end
                else begin : gen_blk7_else
                    assign out_channel = in_channel;
                    assign in_payload = {in_data, in_error};
                    assign {out_data, out_error} = out_payload;
                end
            end
            else begin : gen_blk6_else
                assign out_error = in_error;
                if (CHANNEL_WIDTH > 0) begin : gen_blk8
                    assign in_payload = {in_data, in_channel};
                    assign {out_data, out_channel} = out_payload;
                end
                else begin : gen_blk8_else
                    assign out_channel = in_channel;
                    assign in_payload = in_data;
                    assign out_data = out_payload;
                end
            end
        end
    endgenerate

    // --------------------------------------------------
    // Memory-based FIFO storage
    //
    // To allow a ready latency of 0, the read index is 
    // obtained from the next read pointer and memory 
    // outputs are unregistered.
    //
    // If the empty latency is 1, we infer bypass logic
    // around the memory so writes propagate to the
    // outputs on the next cycle.
    //
    // Do not change the way this is coded: Quartus needs
    // a perfect match to the template, and any attempt to 
    // refactor the two always blocks into one will break
    // memory inference.
    // --------------------------------------------------

    generate if (USE_MEMORY_BLOCKS == 1) begin  : gen_blk9

        if (EMPTY_LATENCY == 1) begin : gen_blk10

            always @(posedge clk) begin
                if (in_valid && in_ready)
                    infer_mem[wr_ptr] = in_payload;

                internal_out_payload = infer_mem[mem_rd_ptr];
            end

       end else begin : gen_blk10_else

        wire [PAYLOAD_WIDTH-1:0] fifo_out_payload;

	always @* begin
            internal_out_payload = fifo_out_payload;
        end

        altera_syncram # (
          .address_aclr_b  ("NONE"),
          .address_reg_b   ("CLOCK0"),
          .clock_enable_input_a ("BYPASS"),
          .clock_enable_input_b  ("BYPASS"),
          .clock_enable_output_b  ("BYPASS"),
          .enable_ecc  ("FALSE"),
          .lpm_type   ("altera_syncram"),
          .numwords_a   (FIFO_DEPTH),
          .numwords_b  (FIFO_DEPTH),
          .operation_mode ("DUAL_PORT"),
          .outdata_aclr_b  ("NONE"),
          .outdata_sclr_b  ("NONE"),
          .outdata_reg_b  ("UNREGISTERED"),
          .power_up_uninitialized ("TRUE"),
          .ram_block_type  (MEM_TYPE),
          .read_during_write_mode_mixed_ports  ("DONT_CARE"),
          .widthad_a   (ADDR_WIDTH),
          .widthad_b   (ADDR_WIDTH),
          .width_a   (PAYLOAD_WIDTH),
          .width_b   (PAYLOAD_WIDTH),
          .width_byteena_a  (1)
     ) altera_syncram_component (
                  .address_a (wr_ptr), // write address
                  .address_b (mem_rd_ptr), // read address
                  .clock0 (clk),
                  .data_a (in_payload), // in_data
                  .wren_a (in_valid && in_ready), // wr ptr
                  .q_b (fifo_out_payload),
                  .aclr0 (1'b0),
                  .aclr1 (1'b0),
		  .address2_a (1'b1),
                  .address2_b (1'b1),
                  .addressstall_a (1'b0),
                  .addressstall_b (1'b0),
                  .byteena_a (1'b1),
                  .byteena_b (1'b1),
                  .clock1 (1'b1),
                  .clocken0 (1'b1),
                  .clocken1 (1'b1),
                  .clocken2 (1'b1),
                  .clocken3 (1'b1),
                  .data_b ({PAYLOAD_WIDTH{1'b1}}), // input - connect data width 
                  .q_a (),
		  .eccstatus (),
	          .eccencbypass (1'b0),
		  .eccencparity (8'b0),
      		  .sclr (1'b0),
                  .rden_a (1'b1),
                  .rden_b (1'b1),
                  .wren_b (1'b0));
    end
    assign mem_rd_ptr = next_rd_ptr;
    end else begin : gen_blk9_else

    // --------------------------------------------------
    // Register-based FIFO storage
    //
    // Uses a shift register as the storage element. Each
    // shift register slot has a bit which indicates if
    // the slot is occupied (credit to Sam H for the idea).
    // The occupancy bits are contiguous and start from the
    // lsb, so 0000, 0001, 0011, 0111, 1111 for a 4-deep
    // FIFO.
    // 
    // Each slot is enabled during a read or when it
    // is unoccupied. New data is always written to every
    // going-to-be-empty slot (we keep track of which ones
    // are actually useful with the occupancy bits). On a
    // read we shift occupied slots.
    // 
    // The exception is the last slot, which always gets 
    // new data when it is unoccupied.
    // --------------------------------------------------
        for (i = 0; i < DEPTH-1; i = i + 1) begin : shift_reg
            always @(posedge clk ) begin
                 if (read || !mem_used[i]) begin
                    if (!mem_used[i+1])
                        mem[i] <= in_payload;
                    else
                        mem[i] <= mem[i+1];
                end
            end
        end

        always @(posedge clk) begin
                if (DEPTH == 1) begin
                    if (write)
                        mem[DEPTH-1] <= in_payload;
                end
                else if (!mem_used[DEPTH-1])
                    mem[DEPTH-1] <= in_payload;    
        end

    end
    endgenerate

    assign read  = internal_out_ready && internal_out_valid  && ok_to_forward;
    assign write = in_ready && in_valid;

    // --------------------------------------------------
    // Pointer Management
    // --------------------------------------------------
    generate if (USE_MEMORY_BLOCKS == 1) begin : gen_blk11
        always @ (posedge clk) begin
           next_incremented_wr_ptr <= next_wr_ptr + 1'b1;
           next_incremented_rd_ptr <= next_rd_ptr + 1'b1;
        end

        if (NON_POWER2_DEPTH == 1) begin
            assign incremented_wr_ptr = wr_ptr_overflow ? {ADDR_WIDTH{1'b0}} : next_incremented_wr_ptr;
            assign incremented_rd_ptr = rd_ptr_overflow ? {ADDR_WIDTH{1'b0}} : next_incremented_rd_ptr;
        end
        else begin
            assign incremented_wr_ptr = next_incremented_wr_ptr;
            assign incremented_rd_ptr = next_incremented_rd_ptr;
        end

        assign next_wr_ptr =  drop_on_error ? curr_sop_ptr : write ?  incremented_wr_ptr : wr_ptr;
        assign next_rd_ptr = (read) ? incremented_rd_ptr : rd_ptr;
     
        if (SYNC_RESET == 0) begin: async_rst_ptr
          always @(posedge clk or posedge reset) begin
              if (reset) begin
                  wr_ptr <= 0;
                  rd_ptr <= 0;
              end
              else begin
                  wr_ptr <= next_wr_ptr;
                  rd_ptr <= next_rd_ptr;
              end
          end

          if (NON_POWER2_DEPTH == 1) begin
              always @ (posedge clk, posedge reset) begin
                  if(reset) begin
                     wr_ptr_overflow <= 1'b0;
                     rd_ptr_overflow <= 1'b0;
                  end
                  else begin
                     if(write) begin
                        if(wr_ptr == FIFO_DEPTH_PTR) 
                           wr_ptr_overflow <= 1'b1;
                        else 
                           wr_ptr_overflow <= 1'b0;
                     end

                     if(read) begin
                        if(rd_ptr == FIFO_DEPTH_PTR) 
                           rd_ptr_overflow <= 1'b1;
                        else 
                           rd_ptr_overflow <= 1'b0;
                     end
                  end
              end
          end
        end // async_rst_ptr
        else begin // sync rst ptr
           always @(posedge clk ) begin
               if (internal_sclr) begin
                   wr_ptr <= 0;
                   rd_ptr <= 0;
               end
               else begin
                   wr_ptr <= next_wr_ptr;
                   rd_ptr <= next_rd_ptr;
               end
           end

           if (NON_POWER2_DEPTH == 1) begin
               always @ (posedge clk) begin
                   if(internal_sclr) begin
                      wr_ptr_overflow <= 1'b0;
                      rd_ptr_overflow <= 1'b0;
                   end
                   else begin
                      if(write) begin
                        if(wr_ptr == FIFO_DEPTH_PTR) 
                           wr_ptr_overflow <= 1'b1;
                        else 
                           wr_ptr_overflow <= 1'b0;
                      end

                      if(read) begin
                        if(rd_ptr == FIFO_DEPTH_PTR)
                           rd_ptr_overflow <= 1'b1;
                        else 
                           rd_ptr_overflow <= 1'b0;
                      end
                   end
               end
           end
        end // sync_rst_ptr

    end else begin : gen_blk11_else

    // --------------------------------------------------
    // Shift Register Occupancy Bits
    //
    // Consider a 4-deep FIFO with 2 entries: 0011
    // On a read and write, do not modify the bits.
    // On a write, left-shift the bits to get 0111.
    // On a read, right-shift the bits to get 0001.
    //
    // Also, on a write we set bit0 (the head), while
    // clearing the tail on a read.
    // --------------------------------------------------
   if (SYNC_RESET == 0) begin : async_mem_used 
        always @(posedge clk or posedge reset) begin
            if (reset) begin
                mem_used[0] <= 0;
            end 
            else begin
                if (write ^ read) begin
                    if (write)
                        mem_used[0] <= 1;
                    else if (read) begin
                        if (DEPTH > 1)
                            mem_used[0] <= mem_used[1];
                        else
                            mem_used[0] <= 0;
                    end    
                end
            end
        end
   end // async_mem_used
   else begin // sync_mem_used
       always @(posedge clk ) begin
            if (internal_sclr) begin
                mem_used[0] <= 0;
            end 
            else begin
                if (write ^ read) begin
                    if (write)
                        mem_used[0] <= 1;
                    else if (read) begin
                        if (DEPTH > 1)
                            mem_used[0] <= mem_used[1];
                        else
                            mem_used[0] <= 0;
                    end    
                end
            end
       end
   end // sync_mem_used

       
        if (DEPTH > 1) begin : gen_blk12
           if (SYNC_RESET == 0) begin : async_mem_used_blk2
            always @(posedge clk or posedge reset) begin
                if (reset) begin
                    mem_used[DEPTH-1] <= 0;
                end
                else begin 
                    if (write ^ read) begin            
                        mem_used[DEPTH-1] <= 0;
                        if (write)
                            mem_used[DEPTH-1] <= mem_used[DEPTH-2];
                    end
                end
            end // always
           end // async_mem_used_blk2

          else begin // sync_mem_used_blk2
           always @(posedge clk ) begin
                if (internal_sclr) begin
                    mem_used[DEPTH-1] <= 0;
                end
                else begin 
                    if (write ^ read) begin            
                        mem_used[DEPTH-1] <= 0;
                        if (write)
                            mem_used[DEPTH-1] <= mem_used[DEPTH-2];
                    end
                end
           end // always
          end // sync_mem_used_blk2
        end // depth >1

           
     
        for (i = 1; i < DEPTH-1; i = i + 1) begin : storage_logic
          if (SYNC_RESET == 0) begin : async_storagelogic
            always @(posedge clk, posedge reset) begin
                if (reset) begin
                    mem_used[i] <= 0;
                end 
                else begin
                    if (write ^ read) begin
                        if (write)
                            mem_used[i] <= mem_used[i-1];
                        else if (read)
                            mem_used[i] <= mem_used[i+1];     
                    end
                end
            end
          end // async_storagelogic

          else begin //sync_storagelogic
            always @(posedge clk) begin
                if (internal_sclr) begin
                    mem_used[i] <= 0;
                end 
                else begin
                    if (write ^ read) begin
                        if (write)
                            mem_used[i] <= mem_used[i-1];
                        else if (read)
                            mem_used[i] <= mem_used[i+1];     
                    end
                end
            end
           end //sync_storagelogic
        end // for loop
    end // else
    endgenerate


    // --------------------------------------------------
    // Memory FIFO Status Management
    //
    // Generates the full and empty signals from the
    // pointers. The FIFO is full when the next write 
    // pointer will be equal to the read pointer after
    // a write. Reading from a FIFO clears full.
    //
    // The FIFO is empty when the next read pointer will
    // be equal to the write pointer after a read. Writing
    // to a FIFO clears empty.
    //
    // A simultaneous read and write must not change any of 
    // the empty or full flags unless there is a drop on error event.
    // --------------------------------------------------
    generate if (USE_MEMORY_BLOCKS == 1) begin : gen_blk13

        always @* begin
            next_full = full;
            next_empty = empty;
     
            if (read && !write) begin
                next_full = 1'b0;
     
                if (incremented_rd_ptr == wr_ptr)
                    next_empty = 1'b1;
            end
            
            if (write && !read) begin
                if (!drop_on_error)
                  next_empty = 1'b0;
                else if (curr_sop_ptr == rd_ptr)   // drop on error and only 1 pkt in fifo
                  next_empty = 1'b1;
     
                if (incremented_wr_ptr == rd_ptr && !drop_on_error)
                    next_full = 1'b1;
            end

            if (write && read && drop_on_error) begin
                if (curr_sop_ptr == next_rd_ptr)
                  next_empty = 1'b1;
            end
        end

     if (SYNC_RESET == 0) begin: async_rst_full_empty
        always @(posedge clk or posedge reset) begin
            if (reset) begin
                empty <= 1;
                full  <= 0;
            end
            else begin 
                empty <= next_empty;
                full  <= next_full;
            end
        end
    end // async_rst_full_empty
    else begin // sync_rst_full_empty
        always @(posedge clk ) begin
            if (internal_sclr) begin
                empty <= 1;
                full  <= 0;
            end
            else begin 
                empty <= next_empty;
                full  <= next_full;
            end
        end
    end // sync_rst_full_empty

    end else begin : gen_blk13_else
    // --------------------------------------------------
    // Register FIFO Status Management
    //
    // Full when the tail occupancy bit is 1. Empty when
    // the head occupancy bit is 0.
    // --------------------------------------------------
        always @* begin
            full  = mem_used[DEPTH-1];
            empty = !mem_used[0];

            // ------------------------------------------
            // For a single slot FIFO, reading clears the
            // full status immediately.
            // ------------------------------------------
            if (DEPTH == 1)
                full = mem_used[0] && !read;

            internal_out_payload = mem[0];

            // ------------------------------------------
            // Writes clear empty immediately for lookahead modes.
            // Note that we use in_valid instead of write to avoid
            // combinational loops (in lookahead mode, qualifying
            // with in_ready is meaningless).
            //
            // In a 1-deep FIFO, a possible combinational loop runs
            // from write -> out_valid -> out_ready -> write
            // ------------------------------------------
            if (EMPTY_LATENCY == 0) begin
                empty = !mem_used[0] && !in_valid;

                if (!mem_used[0] && in_valid)
                    internal_out_payload = in_payload;
            end
        end

    end
    endgenerate

    // --------------------------------------------------
    // Avalon-ST Signals
    //
    // The in_ready signal is straightforward. 
    //
    // To match memory latency when empty latency > 1, 
    // out_valid assertions must be delayed by one clock
    // cycle.
    //
    // Note: out_valid deassertions must not be delayed or 
    // the FIFO will underflow.
    // --------------------------------------------------
    assign in_ready = !full;
    assign internal_out_ready = out_ready || !out_valid;

    generate if (EMPTY_LATENCY > 1) begin : gen_blk14
      if (SYNC_RESET == 0) begin : async_rst_internal_out_valid
        always @(posedge clk or posedge reset) begin
            if (reset)
                internal_out_valid <= 0;
            else begin
                internal_out_valid <= !empty & ok_to_forward & ~drop_on_error;

                if (read) begin
                    if (incremented_rd_ptr == wr_ptr)
                        internal_out_valid <= 1'b0;
                end
            end
        end
      end //  async_rst_internal_out_valid
      else begin //  sync_rst_internal_out_valid
         always @(posedge clk ) begin
            if (internal_sclr)
                internal_out_valid <= 0;
            else begin
                internal_out_valid <= !empty & ok_to_forward & ~drop_on_error;

                if (read) begin
                    if (incremented_rd_ptr == wr_ptr)
                        internal_out_valid <= 1'b0;
                end
            end
        end
      end //  sync_rst_internal_out_valid
    end else begin : gen_blk14_else
        always @* begin
            internal_out_valid = !empty & ok_to_forward;
        end
    end
    endgenerate

    // --------------------------------------------------
    // Single Output Pipeline Stage
    //
    // This output pipeline stage is enabled if the FIFO's 
    // empty latency is set to 3 (default). It is disabled
    // for all other allowed latencies.
    //
    // Reason: The memory outputs are unregistered, so we have to
    // register the output or fmax will drop if combinatorial
    // logic is present on the output datapath.
    // 
    // Q: The Avalon-ST spec says that I have to register my outputs
    //    But isn't the memory counted as a register?
    // A: The path from the address lookup to the memory output is
    //    slow. Registering the memory outputs is a good idea. 
    //
    // The registers get packed into the memory by the fitter
    // which means minimal resources are consumed (the result
    // is a altsyncram with registered outputs, available on 
    // all modern Altera devices). 
    //
    // This output stage acts as an extra slot in the FIFO, 
    // and complicates the fill level.
    // --------------------------------------------------
    generate if (EMPTY_LATENCY == 3) begin : gen_blk15
      if (SYNC_RESET == 0) begin : async_rst_out_valid_payload
        always @(posedge clk or posedge reset) begin
            if (reset) begin
                out_valid   <= 0;
                out_payload <= 0;
            end
            else begin
                if (internal_out_ready) begin
                    out_valid   <= internal_out_valid & ok_to_forward;
                    out_payload <= internal_out_payload;
                end
            end
        end
      end // async_rst_out_valid_payload
      else begin // sync_rst_out_valid_payload
        always @(posedge clk ) begin
            if (internal_sclr) begin
                out_valid   <= 0;
                out_payload <= 0;
            end
            else begin
                if (internal_out_ready) begin
                    out_valid   <= internal_out_valid & ok_to_forward;
                    out_payload <= internal_out_payload;
                end
            end
        end 
      end // sync_rst_out_valid_payload
    end
    else begin : gen_blk15_else
        always @* begin
            out_valid   = internal_out_valid;
            out_payload = internal_out_payload;
        end
    end
    endgenerate

    // --------------------------------------------------
    // Fill Level
    //
    // The fill level is calculated from the next write
    // and read pointers to avoid unnecessary latency
    // and logic.
    //
    // However, if the store-and-forward mode of the FIFO
    // is enabled, the fill level is an up-down counter
    // for fmax optimization reasons.
    //
    // If the output pipeline is enabled, the fill level 
    // must account for it, or we'll always be off by one.
    // This may, or may not be important depending on the
    // application.
    //
    // For now, we'll always calculate the exact fill level
    // at the cost of an extra adder when the output stage
    // is enabled.
    // --------------------------------------------------
    generate if (USE_FILL_LEVEL) begin : gen_blk16
        wire [31:0] depth32;
        assign depth32 = DEPTH;

        if (USE_STORE_FORWARD) begin

            reg [ADDR_WIDTH : 0] curr_packet_len_less_one;
            
            // --------------------------------------------------
            // We only drop on endofpacket. As long as we don't add to the fill
            // level on the dropped endofpacket cycle, we can simply subtract
            // (packet length - 1) from the fill level for dropped packets.
            // --------------------------------------------------
         if (SYNC_RESET == 0) begin : async_rst_curr_packet_len_less_one
            always @(posedge clk or posedge reset) begin
                if (reset) begin
                    curr_packet_len_less_one <= 0;
                end else begin
                    if (write) begin
                        curr_packet_len_less_one <= curr_packet_len_less_one + 1'b1;
                        if (in_endofpacket)
                            curr_packet_len_less_one <= 0;
                    end
                end
            end
         end // async_rst_curr_packet_len_less_one

         else begin // sync_rst_curr_packet_len_less_one
            always @(posedge clk ) begin
                if (internal_sclr) begin
                    curr_packet_len_less_one <= 0;
                end else begin
                    if (write) begin
                        curr_packet_len_less_one <= curr_packet_len_less_one + 1'b1;
                        if (in_endofpacket)
                            curr_packet_len_less_one <= 0;
                    end
                end
            end
         end // sync_rst_curr_packet_len_less_one
         
         if (SYNC_RESET == 0) begin : async_rst_fifo_fill_level
            always @(posedge clk or posedge reset) begin
                if (reset) begin
                    fifo_fill_level <= 0;
                end else if (drop_on_error) begin
                    fifo_fill_level <= fifo_fill_level - curr_packet_len_less_one;
                    if (read)
                        fifo_fill_level <= fifo_fill_level - curr_packet_len_less_one - 1'b1;
                end else if (write && !read) begin
                    fifo_fill_level <= fifo_fill_level + 1'b1;
                end else if (read && !write) begin
                    fifo_fill_level <= fifo_fill_level - 1'b1;
                end
            end
         end // async_rst_fifo_fill_level
         else begin // sync_rst_fifo_fill_level
           always @(posedge clk ) begin
                if (internal_sclr) begin
                    fifo_fill_level <= 0;
                end else if (drop_on_error) begin
                    fifo_fill_level <= fifo_fill_level - curr_packet_len_less_one;
                    if (read)
                        fifo_fill_level <= fifo_fill_level - curr_packet_len_less_one - 1'b1;
                end else if (write && !read) begin
                    fifo_fill_level <= fifo_fill_level + 1'b1;
                end else if (read && !write) begin
                    fifo_fill_level <= fifo_fill_level - 1'b1;
                end
            end
         end // sync_rst_fifo_fill_level
 
        end else begin // ~USE_STORE_FORWARD 
         if (SYNC_RESET == 0) begin //async_rst_fifo_fill_level
            always @(posedge clk or posedge reset) begin
                if (reset) 
                    fifo_fill_level <= 0;
                else if (next_full & !drop_on_error)
                    fifo_fill_level <= depth32[ADDR_WIDTH:0];
                else begin
                    fifo_fill_level[ADDR_WIDTH]     <= 1'b0;
                    if(NON_POWER2_DEPTH == 1) begin
                        if(next_wr_ptr < next_rd_ptr) 
                           fifo_fill_level[ADDR_WIDTH-1:0] <= FIFO_DEPTH - next_rd_ptr + next_wr_ptr;
                        else
                           fifo_fill_level[ADDR_WIDTH-1:0] <= next_wr_ptr - next_rd_ptr;
                    end
                    else begin 
                        fifo_fill_level[ADDR_WIDTH-1 : 0] <= next_wr_ptr - next_rd_ptr;
                    end
                end
            end
          end //async_rst_fifo_fill_level
          else begin // sync_rst_fifo_fill_level
            always @(posedge clk ) begin
                if (internal_sclr) 
                    fifo_fill_level <= 0;
                else if (next_full & !drop_on_error)
                    fifo_fill_level <= depth32[ADDR_WIDTH:0];
                else begin
                    fifo_fill_level[ADDR_WIDTH]     <= 1'b0;
                    if(NON_POWER2_DEPTH == 1) begin
                        if(next_wr_ptr < next_rd_ptr) 
                           fifo_fill_level[ADDR_WIDTH-1:0] <= FIFO_DEPTH - next_rd_ptr + next_wr_ptr;
                        else
                           fifo_fill_level[ADDR_WIDTH-1:0] <= next_wr_ptr - next_rd_ptr;
                    end
                    else begin 
                        fifo_fill_level[ADDR_WIDTH-1 : 0] <= next_wr_ptr - next_rd_ptr;
                    end
                end
            end
          end // sync_rst_fifo_fill_level 
        end

        always @* begin
            fill_level = fifo_fill_level;

            if (EMPTY_LATENCY == 3)
                fill_level = fifo_fill_level + {{ADDR_WIDTH{1'b0}}, out_valid};
        end
    end
    else begin : gen_blk16_else
	always @ (posedge clk) begin
		fill_level <= 0;
	end 
    end
    endgenerate

    generate if (USE_ALMOST_FULL_IF) begin : gen_blk17
      if(USE_MEMORY_BLOCKS == 1) begin
         assign almost_full_data = (fill_level >= almost_full_threshold);
      end
      else if(ALMOST_FULL_THRESHOLD > 0) begin
         assign almost_full_data = mem_used[ALMOST_FULL_THRESHOLD - 1];
      end
      else begin
         assign almost_full_data = 0; 
      end
    end
    else begin
         assign almost_full_data = 0; 
    end
    endgenerate

    generate if (USE_ALMOST_EMPTY_IF) begin : gen_blk18
      assign almost_empty_data = (fill_level <= almost_empty_threshold);
    end
    else
      assign almost_empty_data = 0;
    endgenerate

    // --------------------------------------------------
    // Avalon-MM Status & Control Connection Point
    //
    // Register map:
    //
    // | Addr   | RW |     31 - 0      |
    // |  0     | R  |   Fill level    |
    //
    // The registering of this connection point means
    // that there is a cycle of latency between 
    // reads/writes and the updating of the fill level.
    // --------------------------------------------------
    generate if (USE_STORE_FORWARD) begin : gen_blk19
    assign max_fifo_size = ALMOST_FULL_THRESHOLD;
     if (SYNC_RESET == 0) begin // async_rst_full_emp_thrs
      always @(posedge clk or posedge reset) begin
          if (reset) begin
              almost_full_threshold  <= max_fifo_size[23 : 0];
              almost_empty_threshold <= 0;
              cut_through_threshold  <= 0;
              drop_on_error_en       <= 0;
              csr_readdata           <= 0;
              pkt_mode               <= 1'b1;
          end
          else begin
              if (csr_read) begin
                csr_readdata <= 32'b0;
                if (csr_address == 5)
                    csr_readdata <= {31'b0, drop_on_error_en};
                else if (csr_address == 4)
                    csr_readdata <= {8'b0, cut_through_threshold};
                else if (csr_address == 3)
                    csr_readdata <= {8'b0, almost_empty_threshold};
                else if (csr_address == 2)
                    csr_readdata <= {8'b0, almost_full_threshold};
                else if (csr_address == 0)
                    csr_readdata <= {{(31 - ADDR_WIDTH){1'b0}}, fill_level};
             end
             else if (csr_write) begin
               if(csr_address == 3'b101)
                   drop_on_error_en       <= csr_writedata[0];
               else if(csr_address == 3'b100) begin
                   cut_through_threshold  <= csr_writedata[23:0];
                   pkt_mode <= (csr_writedata[23:0] == 0);
               end
               else if(csr_address == 3'b011)
                    almost_empty_threshold <= csr_writedata[23:0];
               else if(csr_address == 3'b010)
                  almost_full_threshold  <= csr_writedata[23:0];
             end     
          end
      end
     end // async_rst_full_emp_thrs 
     else begin //sync_rst_full_emp_thrs
          always @(posedge clk ) begin
          if (internal_sclr) begin
              almost_full_threshold  <= max_fifo_size[23 : 0];
              almost_empty_threshold <= 0;
              cut_through_threshold  <= 0;
              drop_on_error_en       <= 0;
              csr_readdata           <= 0;
              pkt_mode               <= 1'b1;
          end
          else begin
              if (csr_read) begin
                csr_readdata <= 32'b0;
                if (csr_address == 5)
                    csr_readdata <= {31'b0, drop_on_error_en};
                else if (csr_address == 4)
                    csr_readdata <= {8'b0, cut_through_threshold};
                else if (csr_address == 3)
                    csr_readdata <= {8'b0, almost_empty_threshold};
                else if (csr_address == 2)
                    csr_readdata <= {8'b0, almost_full_threshold};
                else if (csr_address == 0)
                    csr_readdata <= {{(31 - ADDR_WIDTH){1'b0}}, fill_level};
             end
             else if (csr_write) begin
               if(csr_address == 3'b101)
                   drop_on_error_en       <= csr_writedata[0];
               else if(csr_address == 3'b100) begin
                   cut_through_threshold  <= csr_writedata[23:0];
                   pkt_mode <= (csr_writedata[23:0] == 0);
               end
               else if(csr_address == 3'b011)
                    almost_empty_threshold <= csr_writedata[23:0];
               else if(csr_address == 3'b010)
                  almost_full_threshold  <= csr_writedata[23:0];
             end     
          end
      end 
     end //sync_rst_full_emp_thrs
    end
    else if (USE_ALMOST_FULL_IF || USE_ALMOST_EMPTY_IF) begin : gen_blk19_else1
         assign max_fifo_size = ALMOST_FULL_THRESHOLD;
         if (SYNC_RESET == 0) begin : async_rst_almost_full_emp_thr_else1
            always @(posedge clk or posedge reset) begin
                if (reset) begin
                    almost_full_threshold  <= max_fifo_size[23 : 0];
                    almost_empty_threshold <= 0;
                    csr_readdata           <= 0;
                end
                else begin
                   if (csr_read) begin
                      csr_readdata <= 32'b0;
                      if (csr_address == 3)
                          csr_readdata <= {8'b0, almost_empty_threshold};
                      else if (csr_address == 2)
                          csr_readdata <= {8'b0, almost_full_threshold};
                      else if (csr_address == 0)
                          csr_readdata <= {{(31 - ADDR_WIDTH){1'b0}}, fill_level};
                   end
                   else if (csr_write) begin
                     if(csr_address == 3'b011)
                         almost_empty_threshold <= csr_writedata[23:0];
                     else if(csr_address == 3'b010)
                        almost_full_threshold  <= csr_writedata[23:0];
                   end       
                end
            end // always 
         end // async_rst_almost_full_emp_thr_else1
         else begin // sync_rst_almost_full_emp_thr_else1
             always @(posedge clk) begin
                 if (internal_sclr) begin
                     almost_full_threshold  <= max_fifo_size[23 : 0];
                     almost_empty_threshold <= 0;
                     csr_readdata           <= 0;
                 end
                 else begin
                    if (csr_read) begin
                       csr_readdata <= 32'b0;
                       if (csr_address == 3)
                           csr_readdata <= {8'b0, almost_empty_threshold};
                       else if (csr_address == 2)
                           csr_readdata <= {8'b0, almost_full_threshold};
                       else if (csr_address == 0)
                           csr_readdata <= {{(31 - ADDR_WIDTH){1'b0}}, fill_level};
                    end
                    else if (csr_write) begin
                      if(csr_address == 3'b011)
                          almost_empty_threshold <= csr_writedata[23:0];
                      else if(csr_address == 3'b010)
                         almost_full_threshold  <= csr_writedata[23:0];
                    end       
                 end
             end // always
         end //sync_rst_almost_full_emp_thr_else1
    end
    else begin : gen_blk19_else2
     if (SYNC_RESET == 0) begin : async_rst_csr_readdata 
      always @(posedge clk or posedge reset) begin
          if (reset) begin
              csr_readdata <= 0;
          end
          else if (csr_read) begin
              csr_readdata <= 0;

              if (csr_address == 0) 
                  csr_readdata <= {{(31 - ADDR_WIDTH){1'b0}}, fill_level};
          end
      end
     end // async_rst_csr_readdata

     else begin //sync_rst_csr_readdata
      always @(posedge clk ) begin
          if (internal_sclr) begin
              csr_readdata <= 0;
          end
          else if (csr_read) begin
              csr_readdata <= 0;

              if (csr_address == 0) 
                  csr_readdata <= {{(31 - ADDR_WIDTH){1'b0}}, fill_level};
          end
      end
     end // sync_rst_csrreaddata
    end
    endgenerate

    // --------------------------------------------------
    // Store and forward logic
    // --------------------------------------------------
    // if the fifo gets full before the entire packet or the
    // cut-threshold condition is met then start sending out
    // data in order to avoid dead-lock situation

    generate if (USE_STORE_FORWARD) begin : gen_blk20
      assign wait_for_threshold   = (fifo_fill_level_lt_cut_through_threshold) & wait_for_pkt ;
      assign wait_for_pkt         = pkt_cnt_eq_zero  | (pkt_cnt_eq_one  & out_pkt_leave);
      assign ok_to_forward        = (pkt_mode ? (~wait_for_pkt | ~pkt_has_started) : 
                                     ~wait_for_threshold) | fifo_too_small_r;
      assign in_pkt_eop_arrive    = in_valid & in_ready & in_endofpacket;
      assign in_pkt_start         = in_valid & in_ready & in_startofpacket;
      assign in_pkt_error         = in_valid & in_ready & |in_error;
      assign out_pkt_sop_leave    = out_valid & out_ready & out_startofpacket;
      assign out_pkt_leave        = out_valid & out_ready & out_endofpacket;
      assign fifo_too_small       = (pkt_mode ? wait_for_pkt : wait_for_threshold) & full & out_ready;

      // count packets coming and going into the fifo
    if (SYNC_RESET == 0) begin : async_rst_count_packets
      always @(posedge clk or posedge reset) begin
        if (reset) begin
          pkt_cnt           <= 0;
          pkt_has_started   <= 0;
          sop_has_left_fifo <= 0;
          fifo_too_small_r  <= 0;
          pkt_cnt_eq_zero   <= 1'b1;
          pkt_cnt_eq_one    <= 1'b0;
          fifo_fill_level_lt_cut_through_threshold <= 1'b1;
        end
        else begin
          fifo_fill_level_lt_cut_through_threshold <= fifo_fill_level < cut_through_threshold;
          fifo_too_small_r <= fifo_too_small;

          if( in_pkt_eop_arrive )
            sop_has_left_fifo <= 1'b0;
          else if (out_pkt_sop_leave & pkt_cnt_eq_zero )
            sop_has_left_fifo <= 1'b1;

          if (in_pkt_eop_arrive & ~out_pkt_leave & ~drop_on_error ) begin
            pkt_cnt <= pkt_cnt + 1'b1;
            pkt_cnt_eq_zero <= 0;
            if (pkt_cnt == 0)
              pkt_cnt_eq_one <= 1'b1;
            else
              pkt_cnt_eq_one <= 1'b0;
          end
          else if((~in_pkt_eop_arrive | drop_on_error) & out_pkt_leave) begin
            pkt_cnt <= pkt_cnt - 1'b1;
            if (pkt_cnt == 1) 
              pkt_cnt_eq_zero <= 1'b1;
            else
              pkt_cnt_eq_zero <= 1'b0;
            if (pkt_cnt == 2) 
              pkt_cnt_eq_one <= 1'b1;
            else
              pkt_cnt_eq_one <= 1'b0;
          end

          if (in_pkt_start)
            pkt_has_started <= 1'b1;
          else if (in_pkt_eop_arrive)
            pkt_has_started <= 1'b0;
        end
      end // always
     end // async_rst_count_packets

     else begin // sync_rst_count_packets
      always @(posedge clk ) begin
        if (internal_sclr) begin
          pkt_cnt           <= 0;
          pkt_has_started   <= 0;
          sop_has_left_fifo <= 0;
          fifo_too_small_r  <= 0;
          pkt_cnt_eq_zero   <= 1'b1;
          pkt_cnt_eq_one    <= 1'b0;
          fifo_fill_level_lt_cut_through_threshold <= 1'b1;
        end
        else begin
          fifo_fill_level_lt_cut_through_threshold <= fifo_fill_level < cut_through_threshold;
          fifo_too_small_r <= fifo_too_small;

          if( in_pkt_eop_arrive )
            sop_has_left_fifo <= 1'b0;
          else if (out_pkt_sop_leave & pkt_cnt_eq_zero )
            sop_has_left_fifo <= 1'b1;

          if (in_pkt_eop_arrive & ~out_pkt_leave & ~drop_on_error ) begin
            pkt_cnt <= pkt_cnt + 1'b1;
            pkt_cnt_eq_zero <= 0;
            if (pkt_cnt == 0)
              pkt_cnt_eq_one <= 1'b1;
            else
              pkt_cnt_eq_one <= 1'b0;
          end
          else if((~in_pkt_eop_arrive | drop_on_error) & out_pkt_leave) begin
            pkt_cnt <= pkt_cnt - 1'b1;
            if (pkt_cnt == 1) 
              pkt_cnt_eq_zero <= 1'b1;
            else
              pkt_cnt_eq_zero <= 1'b0;
            if (pkt_cnt == 2) 
              pkt_cnt_eq_one <= 1'b1;
            else
              pkt_cnt_eq_one <= 1'b0;
          end

          if (in_pkt_start)
            pkt_has_started <= 1'b1;
          else if (in_pkt_eop_arrive)
            pkt_has_started <= 1'b0;
        end
      end // always
    end //sync_rst_count_packets
 
      // drop on error logic
    if (SYNC_RESET == 0) begin: async_rst_err_logic
      always @(posedge clk or posedge reset) begin
        if (reset) begin
          sop_ptr <= 0;
          error_in_pkt <= 0;
        end
        else begin
          // save the location of the SOP
          if ( in_pkt_start ) 
            sop_ptr <= wr_ptr;

          // remember if error in pkt
          // log error only if packet has already started
          if (in_pkt_eop_arrive)
            error_in_pkt <= 1'b0;
          else if ( in_pkt_error & (pkt_has_started | in_pkt_start))
            error_in_pkt <= 1'b1;
        end
      end
    end //async_rst_err_logic
    else begin // sync_rst_err_logic 
      always @(posedge clk ) begin
        if (internal_sclr) begin
          sop_ptr <= 0;
          error_in_pkt <= 0;
        end
        else begin
          // save the location of the SOP
          if ( in_pkt_start ) 
            sop_ptr <= wr_ptr;

          // remember if error in pkt
          // log error only if packet has already started
          if (in_pkt_eop_arrive)
            error_in_pkt <= 1'b0;
          else if ( in_pkt_error & (pkt_has_started | in_pkt_start))
            error_in_pkt <= 1'b1;
        end
      end
    end // sync_rst_error_logic

      assign drop_on_error = drop_on_error_en & (error_in_pkt | in_pkt_error) & in_pkt_eop_arrive & 
                            ~sop_has_left_fifo & ~(out_pkt_sop_leave & pkt_cnt_eq_zero);

      assign curr_sop_ptr = (write && in_startofpacket && in_endofpacket) ? wr_ptr : sop_ptr;

    end
    else begin : gen_blk20_else
      assign ok_to_forward = 1'b1;
      assign drop_on_error = 1'b0;
      if (ADDR_WIDTH <= 1)
        assign curr_sop_ptr = 1'b0;
      else
        assign curr_sop_ptr = {ADDR_WIDTH - 1 { 1'b0 }};
    end
    endgenerate


    // --------------------------------------------------
    // Calculates the log2ceil of the input value
    // --------------------------------------------------
    function integer log2ceil;
        input integer val;
        reg[31:0] i;

        begin
            i = 1;
            log2ceil = 0;

            while (i < val) begin
                log2ceil = log2ceil + 1;
                i = i[30:0] << 1;
            end
        end
    endfunction

endmodule


