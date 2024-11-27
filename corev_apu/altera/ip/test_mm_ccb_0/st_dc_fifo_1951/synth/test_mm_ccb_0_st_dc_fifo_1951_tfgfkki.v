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


//-------------------------------------------------------------------------------
// Description: Dual clocked single channel FIFO with fill levels and status
// information.
// ---------------------------------------------------------------------

`timescale 1 ns / 100 ps

//altera message_off 10036 10858 10230 10030 10034
module test_mm_ccb_0_st_dc_fifo_1951_tfgfkki
(
    
    in_clk,
    in_reset_n,

    out_clk,
    out_reset_n,

    // sink
    in_data,
    in_valid,
    in_ready,
    in_startofpacket,
    in_endofpacket,
    in_empty,
    in_error,
    in_channel,

    // source
    out_data,
    out_valid,
    out_ready,
    out_startofpacket,
    out_endofpacket,
    out_empty,
    out_error,
    out_channel,

    // in csr
    in_csr_address,
    in_csr_write,
    in_csr_read,
    in_csr_readdata,
    in_csr_writedata,

    // out csr
    out_csr_address,
    out_csr_write,
    out_csr_read,
    out_csr_readdata,
    out_csr_writedata,

    // streaming in status
    almost_full_valid,
    almost_full_data,

    // streaming out status
    almost_empty_valid,
    almost_empty_data,

    // (internal, experimental interface) space available st source
    space_avail_data

);

    // ---------------------------------------------------------------------
    // Parameters
    // ---------------------------------------------------------------------
    parameter SYMBOLS_PER_BEAT  = 1;
    parameter BITS_PER_SYMBOL   = 8;
    parameter FIFO_DEPTH        = 16;
    parameter CHANNEL_WIDTH     = 0;
    parameter ERROR_WIDTH       = 0;
    parameter USE_PACKETS       = 0;

    parameter USE_IN_FILL_LEVEL   = 0;
    parameter USE_OUT_FILL_LEVEL  = 0;
    parameter WR_SYNC_DEPTH       = 2;
    parameter RD_SYNC_DEPTH       = 2;
    parameter STREAM_ALMOST_FULL  = 0;
    parameter STREAM_ALMOST_EMPTY = 0;

    parameter BACKPRESSURE_DURING_RESET = 0;

    // optimizations
    parameter LOOKAHEAD_POINTERS  = 0;
    parameter PIPELINE_POINTERS   = 0;

    // experimental, internal parameter
    parameter USE_SPACE_AVAIL_IF  = 0;

    parameter SYNC_RESET = 0;

    parameter retiming_reg_en = 0;

    parameter ADDR_WIDTH   = log2ceil(FIFO_DEPTH);
    localparam DEPTH        = 2 ** ADDR_WIDTH;
    localparam DATA_WIDTH   = SYMBOLS_PER_BEAT * BITS_PER_SYMBOL;
    localparam EMPTY_WIDTH  = log2ceil(SYMBOLS_PER_BEAT);
    localparam PACKET_SIGNALS_WIDTH = 2 + EMPTY_WIDTH;
    localparam PAYLOAD_WIDTH        = (USE_PACKETS == 1) ?
                                          2 + EMPTY_WIDTH + DATA_WIDTH + ERROR_WIDTH + CHANNEL_WIDTH:
                                          DATA_WIDTH + ERROR_WIDTH + CHANNEL_WIDTH;

    // ---------------------------------------------------------------------
    // Input/Output Signals
    // ---------------------------------------------------------------------
    input in_clk;
    input in_reset_n;

    input out_clk;
    input out_reset_n;

    input [DATA_WIDTH - 1 : 0] in_data;
    input in_valid;
    input in_startofpacket;
    input in_endofpacket;
    input [((EMPTY_WIDTH > 0)   ? EMPTY_WIDTH - 1   : 0) : 0] in_empty;
    input [((ERROR_WIDTH > 0)   ? ERROR_WIDTH - 1   : 0) : 0] in_error;
    input [((CHANNEL_WIDTH > 0) ? CHANNEL_WIDTH - 1 : 0) : 0] in_channel;
    output in_ready;

    output [DATA_WIDTH - 1 : 0] out_data;
    output reg out_valid;
    output out_startofpacket;
    output out_endofpacket;
    output [((EMPTY_WIDTH > 0)   ? EMPTY_WIDTH - 1   : 0) : 0] out_empty;
    output [((ERROR_WIDTH > 0)   ? ERROR_WIDTH - 1   : 0) : 0] out_error;
    output [((CHANNEL_WIDTH > 0) ? CHANNEL_WIDTH - 1 : 0) : 0] out_channel;
    input out_ready;

    input in_csr_address;
    input in_csr_read;
    input in_csr_write;
    input [31 : 0] in_csr_writedata;
    output reg [31 : 0] in_csr_readdata;

    input out_csr_address;
    input out_csr_read;
    input out_csr_write;
    input [31 : 0] out_csr_writedata;
    output reg [31 : 0] out_csr_readdata;

    output reg almost_full_valid;
    output reg almost_full_data;
    output reg almost_empty_valid;
    output reg almost_empty_data;

    output [ADDR_WIDTH : 0] space_avail_data;

    // ---------------------------------------------------------------------
    // Memory Pointers
    // ---------------------------------------------------------------------
    (* ramstyle="no_rw_check" *) reg [PAYLOAD_WIDTH - 1 : 0] mem [DEPTH - 1 : 0];
    
    wire [ADDR_WIDTH - 1 : 0] mem_wr_ptr;
    wire [ADDR_WIDTH - 1 : 0] mem_rd_ptr;

    reg [ADDR_WIDTH : 0] in_wr_ptr;
    reg [ADDR_WIDTH : 0] in_wr_ptr_lookahead;
    reg [ADDR_WIDTH : 0] out_rd_ptr;
    reg [ADDR_WIDTH : 0] out_rd_ptr_lookahead;
    
    // ---------------------------------------------------------------------
    // Internal Signals
    // ---------------------------------------------------------------------
    wire [ADDR_WIDTH : 0] next_out_wr_ptr;
    wire [ADDR_WIDTH : 0] next_in_wr_ptr, next_in_wr_ptr_copyB;
    wire [ADDR_WIDTH : 0] next_out_rd_ptr;
    wire [ADDR_WIDTH : 0] next_in_rd_ptr;

    reg  [ADDR_WIDTH : 0] in_wr_ptr_gray     /*synthesis ALTERA_ATTRIBUTE = "SUPPRESS_DA_RULE_INTERNAL=D102" */;
    wire [ADDR_WIDTH : 0] out_wr_ptr_gray;    

    reg  [ADDR_WIDTH : 0] out_rd_ptr_gray    /*synthesis ALTERA_ATTRIBUTE = "SUPPRESS_DA_RULE_INTERNAL=D102" */;
    wire [ADDR_WIDTH : 0] in_rd_ptr_gray;

    reg  [ADDR_WIDTH : 0] out_wr_ptr_gray_reg;
    reg  [ADDR_WIDTH : 0] in_rd_ptr_gray_reg;

    (* preserve_syn_only *)      reg full;
    (* preserve_syn_only *)      reg full_copyA;
    (* preserve_syn_only *)      reg full_copyB;
    (* preserve_syn_only *)      reg full_copyC;

    wire in_ready_copyA;     
    wire in_ready_copyB;
    wire in_ready_copyC;     
    reg empty;

    wire [PAYLOAD_WIDTH - 1 : 0] in_payload;
    reg  [PAYLOAD_WIDTH - 1 : 0] out_payload;
    reg  [PAYLOAD_WIDTH - 1 : 0] internal_out_payload;

    wire [PACKET_SIGNALS_WIDTH - 1 : 0] in_packet_signals;
    wire [PACKET_SIGNALS_WIDTH - 1 : 0] out_packet_signals;

    wire internal_out_ready;
    wire internal_out_valid;

    wire [ADDR_WIDTH : 0] out_fill_level;
    reg  [ADDR_WIDTH : 0] out_fifo_fill_level;
    reg  [ADDR_WIDTH : 0] in_fill_level;
    reg  [ADDR_WIDTH : 0] in_space_avail;

    reg [23 : 0] almost_empty_threshold;
    reg [23 : 0] almost_full_threshold;

    wire internal_in_sclr;
    wire internal_out_sclr;
    
    reg reset_in_reg;
    reg reset_out_reg;

    wire internal_in_sclr_n;
    wire internal_out_sclr_n; 
    
    wire reset_merged;    

    always @ (posedge in_clk) begin
        reset_in_reg <= ~in_reset_n;
    end

    always @ (posedge out_clk) begin
        reset_out_reg <= ~out_reset_n;
    end
    
    
    //logic to reset write & read pointer if write or read reset is asserted
    assign reset_merged = (reset_in_reg | reset_out_reg) ;
     
    altera_reset_synchronizer #(
            .ASYNC_RESET     (1'b1),
            .DEPTH (3)
        ) write_reset_sync (
            .reset_in (reset_merged), /* synthesis ALTERA_ATTRIBUTE = "SUPPRESS_DA_RULE_INTERNAL=R101" */
            .clk(in_clk),
            .reset_out(internal_in_sclr)
        );
    
    assign internal_in_sclr_n = ~(internal_in_sclr);
    
    altera_reset_synchronizer #(
        .ASYNC_RESET     (1'b1),
        .DEPTH (3)
        ) read_reset_sync (
             .reset_in (reset_merged), /* synthesis ALTERA_ATTRIBUTE = "SUPPRESS_DA_RULE_INTERNAL=R101" */
             .clk(out_clk),
             .reset_out(internal_out_sclr)
        );    
    
    assign internal_out_sclr_n = ~(internal_out_sclr);    
    // --------------------------------------------------
    // Define Payload
    //
    // Icky part where we decide which signals form the
    // payload to the FIFO.
    // --------------------------------------------------
    generate
        if (EMPTY_WIDTH > 0) begin
            assign in_packet_signals = {in_startofpacket, in_endofpacket, in_empty};
            assign {out_startofpacket, out_endofpacket, out_empty} = out_packet_signals;
        end 
        else begin
            assign in_packet_signals = {in_startofpacket, in_endofpacket};
            assign {out_startofpacket, out_endofpacket} = out_packet_signals;
            assign out_empty = 0;
        end
    endgenerate

    generate
        if (USE_PACKETS) begin
            if (ERROR_WIDTH > 0) begin
                if (CHANNEL_WIDTH > 0) begin
                    assign in_payload = {in_packet_signals, in_data, in_error, in_channel};
                    assign {out_packet_signals, out_data, out_error, out_channel} = out_payload;
                end
                else begin
                    assign in_payload = {in_packet_signals, in_data, in_error};
                    assign {out_packet_signals, out_data, out_error} = out_payload;
                    assign out_channel = 0;
                end
            end
            else begin
                assign out_error = 0;
                if (CHANNEL_WIDTH > 0) begin
                    assign in_payload = {in_packet_signals, in_data, in_channel};
                    assign {out_packet_signals, out_data, out_channel} = out_payload;
                end
                else begin
                    assign in_payload = {in_packet_signals, in_data};
                    assign {out_packet_signals, out_data} = out_payload;
                    assign out_channel = 0;
                end
            end
        end
        else begin
            assign out_packet_signals = 'b0;
            if (ERROR_WIDTH > 0) begin
                if (CHANNEL_WIDTH > 0) begin
                    assign in_payload = {in_data, in_error, in_channel};
                    assign {out_data, out_error, out_channel} = out_payload;
                end
                else begin
                    assign in_payload = {in_data, in_error};
                    assign {out_data, out_error} = out_payload;
                    assign out_channel = 0;
                end
            end
            else begin
                assign out_error = 0;
                if (CHANNEL_WIDTH > 0) begin
                    assign in_payload = {in_data, in_channel};
                    assign {out_data, out_channel} = out_payload;
                end
                else begin
                    assign in_payload = in_data;
                    assign out_data = out_payload;
                    assign out_channel = 0;
                end
            end
        end
    endgenerate

    // ---------------------------------------------------------------------
    // Memory
    //
    // Infers a simple dual clock memory with unregistered outputs
    // ---------------------------------------------------------------------
    wire [PAYLOAD_WIDTH-1:0] fifo_out_payload;

    always @* begin
            internal_out_payload = fifo_out_payload;
        end


   altera_syncram # (
       // `endif
          .address_aclr_b  ("NONE"),
          .address_reg_b   ("CLOCK1"),
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
          .ram_block_type  ("M20K"),
          .widthad_a   (ADDR_WIDTH),
          .widthad_b   (ADDR_WIDTH),
          .width_a   (PAYLOAD_WIDTH),
          .width_b   (PAYLOAD_WIDTH),
          .width_byteena_a  (1)
     ) altera_syncram_component (
                  .address_a (mem_wr_ptr), // write address
                  .address_b (mem_rd_ptr), // read address
                  .clock0 (in_clk),
          .clock1 (out_clk),
                  .data_a (in_payload), // in_data
                  .wren_a (in_valid && in_ready_copyA), // wr ptr
                  .q_b (fifo_out_payload),
                  .aclr0 (1'b0),
                  .aclr1 (1'b0),
          .address2_a (1'b1),
                  .address2_b (1'b1),
                  .addressstall_a (1'b0),
                  .addressstall_b (1'b0),
                  .byteena_a (1'b1),
                  .byteena_b (1'b1),
                  .clocken0 (1'b1),
                  .clocken1 (1'b1),
                  .clocken2 (1'b1),
                  .clocken3 (1'b1),
                  .data_b ({PAYLOAD_WIDTH{1'b1}}), // input - connect data width 
                  .q_a (),
          .eccstatus (),
              .eccencbypass (1'b0),
          .eccencparity (8'b0), 
                  .rden_a (1'b1),
                  .rden_b (1'b1),
          .sclr (1'b0),
                  .wren_b (1'b0));
   
    assign mem_rd_ptr = next_out_rd_ptr[ADDR_WIDTH-1:0];
    assign mem_wr_ptr = in_wr_ptr[ADDR_WIDTH-1:0];

    // ---------------------------------------------------------------------
    // Pointer Management
    //
    // Increment our good old read and write pointers on their native
    // clock domains.
    // ---------------------------------------------------------------------
   
    generate 
         if (SYNC_RESET == 0) begin
            always @(posedge in_clk or negedge internal_in_sclr_n) begin
                if (!internal_in_sclr_n) begin
                    in_wr_ptr           <= 0;
                    in_wr_ptr_lookahead <= 1;
                end
                else begin
                    in_wr_ptr           <= next_in_wr_ptr_copyB;
                    in_wr_ptr_lookahead <= (in_valid && in_ready_copyC) ? in_wr_ptr_lookahead + 1'b1 : in_wr_ptr_lookahead;
                end
            end
         end
         else begin
            always @(posedge in_clk) begin
                if (~internal_in_sclr_n) begin
                    in_wr_ptr           <= 0;
                    in_wr_ptr_lookahead <= 1;
                end
                else begin
                    in_wr_ptr           <= next_in_wr_ptr_copyB;
                    in_wr_ptr_lookahead <= (in_valid && in_ready_copyC) ? in_wr_ptr_lookahead + 1'b1 : in_wr_ptr_lookahead;
                end
            end
         end
    endgenerate


    generate 
         if(SYNC_RESET == 0) begin
            always @(posedge out_clk or negedge internal_out_sclr_n) begin
                if (!internal_out_sclr_n) begin
                    out_rd_ptr           <= 0;
                    out_rd_ptr_lookahead <= 1;
                end
                else begin
                    out_rd_ptr           <= next_out_rd_ptr;
                    out_rd_ptr_lookahead <= (internal_out_valid && internal_out_ready) ? out_rd_ptr_lookahead + 1'b1 : out_rd_ptr_lookahead;
                end
            end
         end
         else begin
            always @(posedge out_clk) begin
                if (~internal_out_sclr_n) begin
                    out_rd_ptr           <= 0;
                    out_rd_ptr_lookahead <= 1;
                end
                else begin
                    out_rd_ptr           <= next_out_rd_ptr;
                    out_rd_ptr_lookahead <= (internal_out_valid && internal_out_ready) ? out_rd_ptr_lookahead + 1'b1 : out_rd_ptr_lookahead;
                end
            end
         end
    endgenerate

    generate if (LOOKAHEAD_POINTERS) begin : lookahead_pointers

        assign next_in_wr_ptr       = (in_ready_copyC && in_valid) ? in_wr_ptr_lookahead : in_wr_ptr;
        assign next_in_wr_ptr_copyB = (in_ready_copyB && in_valid) ? in_wr_ptr_lookahead : in_wr_ptr;
        assign next_out_rd_ptr      = (internal_out_ready && internal_out_valid) ? out_rd_ptr_lookahead : out_rd_ptr;

    end
    else begin : non_lookahead_pointers

        assign next_in_wr_ptr       = (in_ready_copyC && in_valid) ? in_wr_ptr + 1'b1 : in_wr_ptr;
        assign next_in_wr_ptr_copyB = (in_ready_copyB && in_valid) ? in_wr_ptr + 1'b1 : in_wr_ptr;
        assign next_out_rd_ptr      = (internal_out_ready && internal_out_valid) ? out_rd_ptr + 1'b1 : out_rd_ptr;

    end
    endgenerate

    // ---------------------------------------------------------------------
    // Empty/Full Signal Generation
    //
    // We keep read and write pointers that are one bit wider than
    // required, and use that additional bit to figure out if we're
    // full or empty.
    // ---------------------------------------------------------------------
    generate
         if(SYNC_RESET == 0) begin
            always @(posedge out_clk or negedge internal_out_sclr_n) begin
                if(!internal_out_sclr_n)
                    empty <= 1;
                else
                    empty <= (next_out_rd_ptr == next_out_wr_ptr);
            end
         end
         else begin 
            always @(posedge out_clk) begin
                if(~internal_out_sclr_n)
                    empty <= 1;
                else
                    empty <= (next_out_rd_ptr == next_out_wr_ptr);
            end
         end
    endgenerate

    generate
         if(SYNC_RESET == 0) begin 
            always @(posedge in_clk or negedge internal_in_sclr_n) begin
                if (!internal_in_sclr_n) begin
                    full       <= BACKPRESSURE_DURING_RESET ? 1 : 0;            
                    full_copyA <= BACKPRESSURE_DURING_RESET ? 1 : 0;
                    full_copyB <= BACKPRESSURE_DURING_RESET ? 1 : 0;
                    full_copyC <= BACKPRESSURE_DURING_RESET ? 1 : 0;                
                end
                else begin
                    full       <= (next_in_rd_ptr[ADDR_WIDTH - 1 : 0] == next_in_wr_ptr[ADDR_WIDTH - 1 : 0]) && (next_in_rd_ptr[ADDR_WIDTH] != next_in_wr_ptr[ADDR_WIDTH]);
                    full_copyA <= (next_in_rd_ptr[ADDR_WIDTH - 1 : 0] == next_in_wr_ptr[ADDR_WIDTH - 1 : 0]) && (next_in_rd_ptr[ADDR_WIDTH] != next_in_wr_ptr[ADDR_WIDTH]);
                    full_copyB <= (next_in_rd_ptr[ADDR_WIDTH - 1 : 0] == next_in_wr_ptr[ADDR_WIDTH - 1 : 0]) && (next_in_rd_ptr[ADDR_WIDTH] != next_in_wr_ptr[ADDR_WIDTH]);
                    full_copyC <= (next_in_rd_ptr[ADDR_WIDTH - 1 : 0] == next_in_wr_ptr[ADDR_WIDTH - 1 : 0]) && (next_in_rd_ptr[ADDR_WIDTH] != next_in_wr_ptr[ADDR_WIDTH]);
                end
            end
         end
         else begin
            always @(posedge in_clk) begin
                if (~internal_in_sclr_n) begin
                    full       <= BACKPRESSURE_DURING_RESET ? 1 : 0;            
                    full_copyA <= BACKPRESSURE_DURING_RESET ? 1 : 0;
                    full_copyB <= BACKPRESSURE_DURING_RESET ? 1 : 0;
                    full_copyC <= BACKPRESSURE_DURING_RESET ? 1 : 0;                
                end
                else begin
                    full       <= (next_in_rd_ptr[ADDR_WIDTH - 1 : 0] == next_in_wr_ptr[ADDR_WIDTH - 1 : 0]) && (next_in_rd_ptr[ADDR_WIDTH] != next_in_wr_ptr[ADDR_WIDTH]);
                    full_copyA <= (next_in_rd_ptr[ADDR_WIDTH - 1 : 0] == next_in_wr_ptr[ADDR_WIDTH - 1 : 0]) && (next_in_rd_ptr[ADDR_WIDTH] != next_in_wr_ptr[ADDR_WIDTH]);
                    full_copyB <= (next_in_rd_ptr[ADDR_WIDTH - 1 : 0] == next_in_wr_ptr[ADDR_WIDTH - 1 : 0]) && (next_in_rd_ptr[ADDR_WIDTH] != next_in_wr_ptr[ADDR_WIDTH]);
                    full_copyC <= (next_in_rd_ptr[ADDR_WIDTH - 1 : 0] == next_in_wr_ptr[ADDR_WIDTH - 1 : 0]) && (next_in_rd_ptr[ADDR_WIDTH] != next_in_wr_ptr[ADDR_WIDTH]);
                end
            end
         end
    endgenerate

    // ---------------------------------------------------------------------
    // Write Pointer Clock Crossing
    //
    // Clock crossing is done with gray encoding of the pointers. What? You
    // want to know more? We ensure a one bit change at sampling time,
    // and then metastable harden the sampled gray pointer.
    // ---------------------------------------------------------------------
    
    generate 
         if(SYNC_RESET == 0) begin
            always @(posedge in_clk or negedge internal_in_sclr_n) begin
                if (!internal_in_sclr_n)
                    in_wr_ptr_gray <= 0;
                else
                    in_wr_ptr_gray <= bin2gray(in_wr_ptr);
            end
         end
         else begin
            always @(posedge in_clk) begin
                if (~internal_in_sclr_n)
                    in_wr_ptr_gray <= 0;
                else
                    in_wr_ptr_gray <= bin2gray(in_wr_ptr);
            end
         end
    endgenerate

    generate
         if (SYNC_RESET == 0) begin
            altera_dcfifo_synchronizer_bundle #(.WIDTH(ADDR_WIDTH+1), .retiming_reg_en (retiming_reg_en), .DEPTH(WR_SYNC_DEPTH)) 
              write_crosser (
                .clk(out_clk),
                .reset_n(internal_out_sclr_n),
                .din(in_wr_ptr_gray),
                .dout(out_wr_ptr_gray)
            );
         end
         else begin
            altera_dcfifo_synchronizer_bundle #(.WIDTH(ADDR_WIDTH+1), .retiming_reg_en (retiming_reg_en), .DEPTH(WR_SYNC_DEPTH)) 
              write_crosser (
                .clk(out_clk),
                .reset_n(1'b1),
                .din(in_wr_ptr_gray),
                .dout(out_wr_ptr_gray)
            );
         end
    endgenerate

    // ---------------------------------------------------------------------
    // Optionally pipeline the gray to binary conversion for the write pointer. 
    // Doing this will increase the latency of the FIFO, but increase fmax.
    // ---------------------------------------------------------------------
    generate if (PIPELINE_POINTERS) begin : wr_ptr_pipeline

         if(SYNC_RESET == 0) begin
            always @(posedge out_clk or negedge internal_out_sclr_n) begin
                if (!internal_out_sclr_n)
                    out_wr_ptr_gray_reg <= 0;
                else
                    out_wr_ptr_gray_reg <= gray2bin(out_wr_ptr_gray);
            end
         end
         else begin
            always @(posedge out_clk) begin
                if (~internal_out_sclr_n)
                    out_wr_ptr_gray_reg <= 0;
                else
                    out_wr_ptr_gray_reg <= gray2bin(out_wr_ptr_gray);
            end
         end

        assign next_out_wr_ptr = out_wr_ptr_gray_reg;

    end
    else begin : no_wr_ptr_pipeline

        assign next_out_wr_ptr = gray2bin(out_wr_ptr_gray);

    end
    endgenerate

    // ---------------------------------------------------------------------
    // Read Pointer Clock Crossing
    //
    // Go the other way, go the other way...
    // ---------------------------------------------------------------------

   generate
      if(SYNC_RESET == 0) begin
         always @(posedge out_clk or negedge internal_out_sclr_n) begin
              if (!internal_out_sclr_n)
                  out_rd_ptr_gray <= 0;
              else
                  out_rd_ptr_gray <= bin2gray(out_rd_ptr);
         end
      end
      else begin
         always @(posedge out_clk) begin
              if (~internal_out_sclr_n)
                  out_rd_ptr_gray <= 0;
              else
                  out_rd_ptr_gray <= bin2gray(out_rd_ptr);
         end
      end
   endgenerate

   generate
      if(SYNC_RESET == 0) begin
         altera_dcfifo_synchronizer_bundle #(.WIDTH(ADDR_WIDTH+1), .retiming_reg_en (retiming_reg_en), .DEPTH(RD_SYNC_DEPTH)) 
            read_crosser (
              .clk(in_clk),
              .reset_n(internal_in_sclr_n),
              .din(out_rd_ptr_gray),
              .dout(in_rd_ptr_gray)
         );
      end
      else begin
         altera_dcfifo_synchronizer_bundle #(.WIDTH(ADDR_WIDTH+1), .retiming_reg_en (retiming_reg_en), .DEPTH(RD_SYNC_DEPTH)) 
            read_crosser (
              .clk(in_clk),
              .reset_n(1'b1),
              .din(out_rd_ptr_gray),
              .dout(in_rd_ptr_gray)
         );
      end
    endgenerate

    // ---------------------------------------------------------------------
    // Optionally pipeline the gray to binary conversion of the read pointer. 
    // Doing this will increase the pessimism of the FIFO, but increase fmax.
    // ---------------------------------------------------------------------
    generate if (PIPELINE_POINTERS) begin : rd_ptr_pipeline

        if(SYNC_RESET == 0) begin
            always @(posedge in_clk or negedge internal_in_sclr_n) begin
                if (!internal_in_sclr_n)
                    in_rd_ptr_gray_reg <= 0;
                else
                    in_rd_ptr_gray_reg <= gray2bin(in_rd_ptr_gray);
            end
        end
        else begin
            always @(posedge in_clk) begin
                if (~internal_in_sclr_n)
                    in_rd_ptr_gray_reg <= 0;
                else
                    in_rd_ptr_gray_reg <= gray2bin(in_rd_ptr_gray);
            end
        end
        
        assign next_in_rd_ptr = in_rd_ptr_gray_reg;

    end
    else begin : no_rd_ptr_pipeline

        assign next_in_rd_ptr = gray2bin(in_rd_ptr_gray);

    end
    endgenerate

    // ---------------------------------------------------------------------
    // Avalon ST Signals
    // ---------------------------------------------------------------------
     assign in_ready       = !full; //BACKPRESSURE_DURING_RESET is now supported by resetting full to '1'
     assign in_ready_copyA = !full_copyA; //BACKPRESSURE_DURING_RESET is now supported by resetting full to '1'
     assign in_ready_copyB = !full_copyB; //BACKPRESSURE_DURING_RESET is now supported by resetting full to '1'
     assign in_ready_copyC = !full_copyC; //BACKPRESSURE_DURING_RESET is now supported by resetting full to '1'
     
    assign internal_out_valid = !empty;

    // --------------------------------------------------
    // Output Pipeline Stage
    //
    // We do this on the single clock FIFO to keep fmax
    // up because the memory outputs are kind of slow.
    // Therefore, this stage is even more critical on a dual clock
    // FIFO, wouldn't you say? No one wants a slow dcfifo.
    // --------------------------------------------------
    assign internal_out_ready = out_ready || !out_valid;

    generate 
         if(SYNC_RESET == 0) begin
            always @(posedge out_clk or negedge internal_out_sclr_n) begin
                if (!internal_out_sclr_n) begin
                    out_valid <= 0;
                    out_payload <= 0;
                end
                else begin
                    if (internal_out_ready) begin
                        out_valid <= internal_out_valid;
                        out_payload <= internal_out_payload;
                    end
                end
            end
         end
         else begin
            always @(posedge out_clk) begin
                if (~internal_out_sclr_n) begin
                    out_valid <= 0;
                    out_payload <= 0;
                end
                else begin
                    if (internal_out_ready) begin
                        out_valid <= internal_out_valid;
                        out_payload <= internal_out_payload;
                    end
                end
            end
         end
    endgenerate

    // ---------------------------------------------------------------------
    // Out Fill Level 
    //
    // As in the SCFIFO, we account for the output stage as well in the
    // fill level calculations. This means that the out fill level always
    // gives the most accurate fill level report. 
    //
    // On a full 16-deep FIFO, the out fill level will read 17. Funny, but
    // accurate.
    //
    // That's essential on the output side, because a downstream component 
    // might want to know the exact amount of data in the FIFO at any time.
    // ---------------------------------------------------------------------
    generate 
        if (USE_OUT_FILL_LEVEL || STREAM_ALMOST_EMPTY) begin

            if(SYNC_RESET == 0) begin
               always @(posedge out_clk or negedge internal_out_sclr_n) begin
                   if (!internal_out_sclr_n) begin
                       out_fifo_fill_level <= 0;
                   end
                   else begin
                       out_fifo_fill_level <= next_out_wr_ptr - next_out_rd_ptr;
                   end
               end
            end
            else begin
               always @(posedge out_clk) begin
                   if (~internal_out_sclr_n) begin
                       out_fifo_fill_level <= 0;
                   end
                   else begin
                       out_fifo_fill_level <= next_out_wr_ptr - next_out_rd_ptr;
                   end
               end
            end

            assign out_fill_level = out_fifo_fill_level + {{ADDR_WIDTH{1'b0}}, out_valid};
        end
    endgenerate

    // ---------------------------------------------------------------------
    // Almost Empty Streaming Status & Out CSR
    //
    // This is banal by now, but where's the empty signal? The output side.
    // Where's the almost empty status? The output side.
    //
    // The almost empty signal is asserted when the output fill level
    // in the FIFO falls below the user-specified threshold.
    //
    // Output CSR address map:
    //
    // |  Addr  | RW   |   31 - 24   |          23 - 0          |
    // |    0   |  R   |   Reserved  |      Out fill level      |
    // |    1   |  RW  |   Reserved  |  Almost empty threshold  |
    // ---------------------------------------------------------------------
    generate 
    if (USE_OUT_FILL_LEVEL || STREAM_ALMOST_EMPTY) begin
         if(SYNC_RESET == 0) begin
            always @(posedge out_clk or negedge internal_out_sclr_n) begin
                if (!internal_out_sclr_n) begin
                    out_csr_readdata <= 0;
                    if (STREAM_ALMOST_EMPTY) 
                        almost_empty_threshold <= 0;
                end
                else begin
                    if (out_csr_write) begin
                        if (STREAM_ALMOST_EMPTY && (out_csr_address == 1))
                            almost_empty_threshold <= out_csr_writedata[23 : 0];
                    end
                    else if (out_csr_read) begin
                        out_csr_readdata <= 0;

                        if (out_csr_address == 0)
                            out_csr_readdata[23 : 0] <= out_fill_level;
                        else if (STREAM_ALMOST_EMPTY && (out_csr_address == 1))
                            out_csr_readdata[23 : 0] <= almost_empty_threshold;
                    end
                end
            end
         end
         else begin
            always @(posedge out_clk) begin
                if (~internal_out_sclr_n) begin
                    out_csr_readdata <= 0;
                    if (STREAM_ALMOST_EMPTY) 
                        almost_empty_threshold <= 0;
                end
                else begin
                    if (out_csr_write) begin
                        if (STREAM_ALMOST_EMPTY && (out_csr_address == 1))
                            almost_empty_threshold <= out_csr_writedata[23 : 0];
                    end
                    else if (out_csr_read) begin
                        out_csr_readdata <= 0;

                        if (out_csr_address == 0)
                            out_csr_readdata[23 : 0] <= out_fill_level;
                        else if (STREAM_ALMOST_EMPTY && (out_csr_address == 1))
                            out_csr_readdata[23 : 0] <= almost_empty_threshold;
                    end
                end
            end
         end

    end
    else begin
         always @ (posedge out_clk) begin
            out_csr_readdata <= 0;
         end
    end

    if (STREAM_ALMOST_EMPTY) begin
         if(SYNC_RESET == 0) begin
            always @(posedge out_clk or negedge internal_out_sclr_n) begin
                if (!internal_out_sclr_n) begin
                    almost_empty_valid <= 0;
                    almost_empty_data <= 0;
                end
                else begin
                    almost_empty_valid <= 1'b1;
                    almost_empty_data <= (out_fill_level <= almost_empty_threshold);
                end
            end
         end
         else begin
            always @(posedge out_clk) begin
                if (~internal_out_sclr_n) begin
                    almost_empty_valid <= 0;
                    almost_empty_data <= 0;
                end
                else begin
                    almost_empty_valid <= 1'b1;
                    almost_empty_data <= (out_fill_level <= almost_empty_threshold);
                end
            end
         end

    end
    else begin
         always @ (posedge out_clk) begin
            almost_empty_valid <= 1'b0;
            almost_empty_data <= 0;
         end
    end
    endgenerate
    
    // ---------------------------------------------------------------------
    // In Fill Level & In Status Connection Point
    //
    // Note that the input fill level does not account for the output
    // stage i.e it is only the fifo fill level.
    //
    // Is this a problem? No, because the input fill is usually used to 
    // see how much data can still be pushed into this FIFO. The FIFO
    // fill level gives exactly this information, and there's no need to
    // make our lives more difficult by including the output stage here.
    // 
    // One might ask: why not just report a space available level on the
    // input side? Well, I'd like to make this FIFO be as similar as possible
    // to its single clock cousin, and that uses fill levels and 
    // fill thresholds with nary a mention of space available.
    // ---------------------------------------------------------------------
    generate 
        if (USE_IN_FILL_LEVEL || STREAM_ALMOST_FULL) begin

            if(SYNC_RESET == 0) begin
               always @(posedge in_clk or negedge internal_in_sclr_n) begin
                   if (!internal_in_sclr_n) begin
                       in_fill_level <= 0;
                   end
                   else begin
                       in_fill_level <= next_in_wr_ptr - next_in_rd_ptr;
                   end
               end
            end
            else begin
               always @(posedge in_clk) begin
                   if (~internal_in_sclr_n) begin
                       in_fill_level <= 0;
                   end
                   else begin
                       in_fill_level <= next_in_wr_ptr - next_in_rd_ptr;
                   end
               end
            end

        end
    endgenerate

    generate
        if (USE_SPACE_AVAIL_IF) begin
       
            if(SYNC_RESET == 0) begin 
               always @(posedge in_clk or negedge internal_in_sclr_n) begin
                   if (!internal_in_sclr_n) begin
                       in_space_avail <= FIFO_DEPTH;
                   end
                   else begin
                       // -------------------------------------
                       // space = DEPTH-fill = DEPTH-(wr-rd) = DEPTH+rd-wr
                       // Conveniently, DEPTH requires the same number of bits
                       // as the pointers, e.g. a dcfifo with depth = 8
                       // requires 4-bit pointers.
                       //
                       // Adding 8 to a 4-bit pointer is simply negating the
                       // first bit... as is done below.
                       // -------------------------------------

                       in_space_avail <= {~next_in_rd_ptr[ADDR_WIDTH], 
                                           next_in_rd_ptr[ADDR_WIDTH-1:0]} -
                                         next_in_wr_ptr;
                   end
               end   
            end
            else begin
               always @(posedge in_clk) begin
                   if (~internal_in_sclr_n) begin
                       in_space_avail <= FIFO_DEPTH;
                   end
                   else begin
                       in_space_avail <= {~next_in_rd_ptr[ADDR_WIDTH], 
                                           next_in_rd_ptr[ADDR_WIDTH-1:0]} -
                                         next_in_wr_ptr;
                   end
               end   
            end

            assign space_avail_data = in_space_avail;
        end
        else begin : gen_blk13_else
            assign space_avail_data = 'b0;
        end
    endgenerate

    // ---------------------------------------------------------------------
    // Almost Full Streaming Status & In CSR
    //
    // Where's the full signal? The input side.
    // Where's the almost full status? The input side.
    //
    // The almost full data bit is asserted when the input fill level
    // in the FIFO goes above the user-specified threshold.
    //
    // Input csr port address map:
    //
    // |  Addr  |  RW   |     31 - 24   |       23 - 0           |
    // |    0   |  R    |   Reserved    |     In fill level      |
    // |    1   |  RW   |   Reserved    | Almost full threshold  |
    // ---------------------------------------------------------------------
    generate 
    if (USE_IN_FILL_LEVEL || STREAM_ALMOST_FULL) begin
         if(SYNC_RESET == 0) begin
            always @(posedge in_clk or negedge internal_in_sclr_n) begin
                if (!internal_in_sclr_n) begin
                    in_csr_readdata <= 0;
                    if (STREAM_ALMOST_FULL)
                        almost_full_threshold <= 0;
                end
                else begin
                    if (in_csr_write) begin
                        if (STREAM_ALMOST_FULL && (in_csr_address == 1))
                            almost_full_threshold <= in_csr_writedata[23 : 0];
                    end
                    else if (in_csr_read) begin
                        in_csr_readdata <= 0;

                        if (in_csr_address == 0)
                            in_csr_readdata[23 : 0] <= in_fill_level;
                        else if (STREAM_ALMOST_FULL && (in_csr_address == 1))
                            in_csr_readdata[23 : 0] <= almost_full_threshold;
                    end
                end
            end
         end
         else begin
            always @(posedge in_clk) begin
                if (~internal_in_sclr_n) begin
                    in_csr_readdata <= 0;
                    if (STREAM_ALMOST_FULL)
                        almost_full_threshold <= 0;
                end
                else begin
                    if (in_csr_write) begin
                        if (STREAM_ALMOST_FULL && (in_csr_address == 1))
                            almost_full_threshold <= in_csr_writedata[23 : 0];
                    end
                    else if (in_csr_read) begin
                        in_csr_readdata <= 0;

                        if (in_csr_address == 0)
                            in_csr_readdata[23 : 0] <= in_fill_level;
                        else if (STREAM_ALMOST_FULL && (in_csr_address == 1))
                            in_csr_readdata[23 : 0] <= almost_full_threshold;
                    end
                end
            end
         end

    end
    else begin
       always @ (posedge in_clk) begin
            in_csr_readdata <= 0;
       end
    end

    if (STREAM_ALMOST_FULL) begin
         if(SYNC_RESET == 0) begin
            always @(posedge in_clk or negedge internal_in_sclr_n) begin
                if (!internal_in_sclr_n) begin
                    almost_full_valid <= 0;
                    almost_full_data <= 0;
                end
                else begin
                    almost_full_valid <= 1'b1;
                    almost_full_data <= (in_fill_level >= almost_full_threshold);
                end
            end
         end
         else begin
            always @(posedge in_clk) begin
                if (~internal_in_sclr_n) begin
                    almost_full_valid <= 0;
                    almost_full_data <= 0;
                end
                else begin
                    almost_full_valid <= 1'b1;
                    almost_full_data <= (in_fill_level >= almost_full_threshold);
                end
            end
         end

    end
    else begin
      always @ (posedge in_clk) begin
         almost_full_valid <= 0;
         almost_full_data <= 0;
      end
    end

    endgenerate

    // ---------------------------------------------------------------------
    // Gray Functions
    // 
    // These are real beasts when you look at them. But they'll be
    // tested thoroughly.
    // ---------------------------------------------------------------------
    function [ADDR_WIDTH : 0] bin2gray;
        input [ADDR_WIDTH : 0]  bin_val;
        integer i; 
                
        for (i = 0; i <= ADDR_WIDTH; i = i + 1)
        begin
            if (i == ADDR_WIDTH)
                bin2gray[i] = bin_val[i];
            else
                bin2gray[i] = bin_val[i+1] ^ bin_val[i];
        end
    endfunction

    function [ADDR_WIDTH : 0] gray2bin;
        input [ADDR_WIDTH : 0]  gray_val;
        integer i;
        integer j;
                
        for (i = 0; i <= ADDR_WIDTH; i = i + 1) begin
            
            gray2bin[i] = gray_val[i];

            for (j = ADDR_WIDTH; j > i; j = j - 1) begin
                gray2bin[i] = gray2bin[i] ^ gray_val[j];    
            end

        end
    endfunction

    // --------------------------------------------------
    // Calculates the log2ceil of the input value
    // --------------------------------------------------
    function integer log2ceil;
        input integer val;
        integer i;

        begin
            i = 1;
            log2ceil = 0;

            while (i < val) begin
                log2ceil = log2ceil + 1;
                i = i << 1;
            end
        end
    endfunction

endmodule



