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


// --------------------------------------
// Avalon-MM clock crossing bridge
//
// Clock crosses MM commands and responses with the
// help of asynchronous FIFOs.
//
// This bridge will stop emitting read commands when
// too many read commands are in flight to avoid 
// response FIFO overflow.
// --------------------------------------

`timescale 1 ns / 1 ns
module test_mm_ccb_0_mm_ccb_1921_5zxyagi 
#(
    parameter DATA_WIDTH            = 32,
    parameter SYMBOL_WIDTH          = 8,
    parameter HDL_ADDR_WIDTH        = 10,
    parameter BURSTCOUNT_WIDTH      = 1,

    parameter COMMAND_FIFO_DEPTH    = 4,
    parameter RESPONSE_FIFO_DEPTH   = 4,

    parameter MASTER_SYNC_DEPTH     = 2,
    parameter SLAVE_SYNC_DEPTH      = 2,
    parameter SYNC_RESET            = 0,

    // --------------------------------------
    // Derived parameters
    // --------------------------------------
    parameter BYTEEN_WIDTH = DATA_WIDTH / SYMBOL_WIDTH
)
(
    input                           s0_clk,
    input                           s0_reset,

    input                           m0_clk,
    input                           m0_reset,

    output                          s0_waitrequest,
    output [DATA_WIDTH-1:0]         s0_readdata,
    output                          s0_readdatavalid,
    input  [BURSTCOUNT_WIDTH-1:0]   s0_burstcount,
    input  [DATA_WIDTH-1:0]         s0_writedata,
    input  [HDL_ADDR_WIDTH-1:0]     s0_address, 
    input                           s0_write,  
    input                           s0_read,  
    input  [BYTEEN_WIDTH-1:0]       s0_byteenable,  
    input                           s0_debugaccess,

    input                           m0_waitrequest,
    input  [DATA_WIDTH-1:0]         m0_readdata,
    input                           m0_readdatavalid,
    output [BURSTCOUNT_WIDTH-1:0]   m0_burstcount,
    output [DATA_WIDTH-1:0]         m0_writedata,
    output [HDL_ADDR_WIDTH-1:0]     m0_address, 
    output                          m0_write,  
    output                          m0_read,  
    output [BYTEEN_WIDTH-1:0]       m0_byteenable,
    output                          m0_debugaccess
);

    localparam CMD_WIDTH = BURSTCOUNT_WIDTH + DATA_WIDTH + HDL_ADDR_WIDTH 
                    + BYTEEN_WIDTH 
                    + 3;        // read, write, debugaccess

    localparam NUMSYMBOLS    = DATA_WIDTH / SYMBOL_WIDTH;
    localparam RSP_WIDTH     = DATA_WIDTH;
    localparam MAX_BURST     = (1 << (BURSTCOUNT_WIDTH-1));
    localparam COUNTER_WIDTH = log2ceil(RESPONSE_FIFO_DEPTH) + 1;
    localparam NON_BURSTING  = (MAX_BURST == 1);
    localparam BURST_WORDS_W = BURSTCOUNT_WIDTH;

    // --------------------------------------
    // Signals
    // --------------------------------------
    wire [CMD_WIDTH-1:0]     s0_cmd_payload;
    wire [CMD_WIDTH-1:0]     m0_cmd_payload;
    wire                     s0_cmd_valid;
    wire                     m0_cmd_valid;
    wire                     m0_internal_write;
    wire                     m0_internal_read;
    wire                     s0_cmd_ready;
    wire                     m0_cmd_ready;
    reg  [COUNTER_WIDTH-1:0] pending_read_count;
    wire [COUNTER_WIDTH-1:0] space_avail;
    wire                     stop_cmd;
    reg                      stop_cmd_r;
    wire                     m0_read_accepted;
    wire                     m0_rsp_ready;
    reg                      old_read;
    wire [BURST_WORDS_W-1:0] m0_burstcount_words;

    // --------------------------------------
    // Command FIFO
    // --------------------------------------
    (* altera_attribute = "-name ALLOW_ANY_RAM_SIZE_FOR_RECOGNITION ON" *) 
    test_mm_ccb_0_mm_ccb_st_dc_fifo_1921_pg4qgey #(
        .SYMBOLS_PER_BEAT (1),
        .BITS_PER_SYMBOL  (CMD_WIDTH),
        .FIFO_DEPTH       (COMMAND_FIFO_DEPTH),
        .WR_SYNC_DEPTH    (MASTER_SYNC_DEPTH),
        .RD_SYNC_DEPTH    (SLAVE_SYNC_DEPTH),
        .BACKPRESSURE_DURING_RESET (1),
        .SYNC_RESET         (SYNC_RESET)
    ) 
    cmd_fifo
    (
        .in_clk          (s0_clk),
        .in_reset_n      (~s0_reset),
        .out_clk         (m0_clk),
        .out_reset_n     (~m0_reset),

        .in_data         (s0_cmd_payload),
        .in_valid        (s0_cmd_valid),
        .in_ready        (s0_cmd_ready),

        .out_data        (m0_cmd_payload),
        .out_valid       (m0_cmd_valid),
        .out_ready       (m0_cmd_ready)

        
        
    );


    // Generation of internal reset synchronization
   reg internal_sclr;
   generate if (SYNC_RESET == 1) begin // rst_syncronizer
      always @ (posedge m0_clk) begin
         internal_sclr <= m0_reset;
      end
   end
   endgenerate

    // --------------------------------------
    // Command payload
    // --------------------------------------
    assign s0_waitrequest = ~s0_cmd_ready;
    assign s0_cmd_valid   = s0_write | s0_read;

    assign s0_cmd_payload = {s0_address, 
                             s0_burstcount, 
                             s0_read, 
                             s0_write, 
                             s0_writedata, 
                             s0_byteenable,
                             s0_debugaccess};
    assign {m0_address, 
            m0_burstcount, 
            m0_internal_read, 
            m0_internal_write,
            m0_writedata, 
            m0_byteenable,
            m0_debugaccess} = m0_cmd_payload;

    assign m0_cmd_ready = ~m0_waitrequest & 
                            ~(m0_internal_read & stop_cmd_r & ~old_read);
    assign m0_write =  m0_internal_write & m0_cmd_valid;
    assign m0_read  =  m0_internal_read & m0_cmd_valid & (~stop_cmd_r | old_read);
    assign m0_read_accepted = m0_read & ~m0_waitrequest;


    // ---------------------------------------------
    // the non-bursting case
    // ---------------------------------------------
    generate if (NON_BURSTING)
    begin
      if (SYNC_RESET == 0) begin  
    
           always @(posedge m0_clk, posedge m0_reset) begin
               if (m0_reset) begin
                   pending_read_count <= 0;
               end
               else begin
                   if (m0_read_accepted & m0_readdatavalid)
                       pending_read_count <= pending_read_count;
                   else if (m0_readdatavalid)
                       pending_read_count <= pending_read_count - 1'd1;
                   else if (m0_read_accepted)
                       pending_read_count <= pending_read_count + 1'd1;
               end
           end
      end // async_rst0

      else begin 
           always @(posedge m0_clk) begin
               if (internal_sclr) begin
                   pending_read_count <= 0;
               end
               else begin
                   if (m0_read_accepted & m0_readdatavalid)
                       pending_read_count <= pending_read_count;
                   else if (m0_readdatavalid)
                       pending_read_count <= pending_read_count - 1'd1;
                   else if (m0_read_accepted)
                       pending_read_count <= pending_read_count + 1'd1;
               end
           end
      end // sync_rst0
    end // if non_bursting

    // ---------------------------------------------
    // the bursting case
    // ---------------------------------------------
    else begin
        assign m0_burstcount_words = m0_burstcount;
      if (SYNC_RESET == 0 ) begin 
           always @(posedge m0_clk, posedge m0_reset) begin
               if (m0_reset) begin
                   pending_read_count <= 0;
               end
               else begin
                   if (m0_read_accepted & m0_readdatavalid)
                       pending_read_count <= pending_read_count +
                                               m0_burstcount_words - 1'd1;
                   else if (m0_readdatavalid)
                       pending_read_count <= pending_read_count - 1'd1;
                   else if (m0_read_accepted)
                       pending_read_count <= pending_read_count +
                                               m0_burstcount_words;  
               end
           end
      end // async_rst1
      else begin 
           always @(posedge m0_clk) begin
               if (internal_sclr) begin
                   pending_read_count <= 0;
               end
               else begin
                   if (m0_read_accepted & m0_readdatavalid)
                       pending_read_count <= pending_read_count +
                                               m0_burstcount_words - 1'd1;
                   else if (m0_readdatavalid)
                       pending_read_count <= pending_read_count - 1'd1;
                   else if (m0_read_accepted)
                       pending_read_count <= pending_read_count +
                                               m0_burstcount_words;  
               end
           end // @always
      end // sync_rst1


    end // else bursting
    endgenerate

    assign stop_cmd = (pending_read_count + 2*MAX_BURST) > space_avail;
   
    generate
    if (SYNC_RESET == 0) begin // async_rst2
       always @(posedge m0_clk, posedge m0_reset) begin
           if (m0_reset) begin
               stop_cmd_r <= 1'b0;
               old_read   <= 1'b0;
           end
           else begin
               stop_cmd_r <= stop_cmd;
               old_read   <= m0_read & m0_waitrequest;
           end
       end
     end // async_rst2

     else begin
       always @(posedge m0_clk) begin
           if (internal_sclr) begin
               stop_cmd_r <= 1'b0;
               old_read   <= 1'b0;
           end
           else begin
               stop_cmd_r <= stop_cmd;
               old_read   <= m0_read & m0_waitrequest;
           end
       end
     end // sync_rst2
     endgenerate
    // --------------------------------------
    // Response FIFO
    // --------------------------------------
    (* altera_attribute = "-name ALLOW_ANY_RAM_SIZE_FOR_RECOGNITION ON" *) 
    test_mm_ccb_0_mm_ccb_st_dc_fifo_1921_6qjweta #(
        .SYMBOLS_PER_BEAT   (1),
        .BITS_PER_SYMBOL    (RSP_WIDTH),
        .FIFO_DEPTH         (RESPONSE_FIFO_DEPTH),
        .WR_SYNC_DEPTH      (SLAVE_SYNC_DEPTH),
        .RD_SYNC_DEPTH      (MASTER_SYNC_DEPTH),
        .USE_SPACE_AVAIL_IF (1),
        .SYNC_RESET         (SYNC_RESET)
    ) 
    rsp_fifo
    (
        .in_clk           (m0_clk),
        .in_reset_n       (~m0_reset),
        .out_clk          (s0_clk),
        .out_reset_n      (~s0_reset),

        .in_data          (m0_readdata),
        .in_valid         (m0_readdatavalid),

        // ------------------------------------
        // must never overflow, or we're in trouble
        // (we cannot backpressure the response)
        // ------------------------------------
        .in_ready         (m0_rsp_ready),

        .out_data         (s0_readdata),
        .out_valid        (s0_readdatavalid),
        .out_ready        (1'b1),

        .space_avail_data (space_avail)

    );

// synthesis translate_off
    always @(posedge m0_clk) begin
        if (~m0_rsp_ready & m0_readdatavalid) begin
            $display("%t %m: internal error, response fifo overflow", $time);
        end

        if (pending_read_count > space_avail) begin
            $display("%t %m: internal error, too many pending reads", $time);
        end
    end
// synthesis translate_on

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

