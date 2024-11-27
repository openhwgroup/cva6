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


`timescale 1 ps / 1 ps

module fmiohmc_fifo #
    ( parameter
        CFG_ADDR_WIDTH        = 10,
        CFG_DATA_WIDTH        = 32,
        CFG_REGISTERED_OUTPUT = 0,
        CFG_SHOWAHEAD         = 0,
        CFG_USE_EAB           = "ON",
        CFG_REGISTERED_INPUT  = 0
    )
    (
        ctl_clk,
        ctl_reset_n,
        write_request,
        write_data,
        read_request,
        read_data,
        read_data_valid,
        fifo_empty,
        fifo_full
    );

localparam CFG_REGISTERED_INPUT_STAGES = (CFG_REGISTERED_INPUT == 0) ? 1 : CFG_REGISTERED_INPUT; 
localparam ENTRIES_COUNTER_WIDTH       = CFG_ADDR_WIDTH + 1;
localparam SCFIFO_DEPTH             = 2 ** CFG_ADDR_WIDTH;
localparam SCFIFO_REGISTERED_OUTPUT = CFG_REGISTERED_OUTPUT ? "ON" : "OFF";
localparam SCFIFO_SHOWAHEAD         = CFG_SHOWAHEAD         ? "ON" : "OFF";

input                           ctl_clk;
input                           ctl_reset_n;

input                           write_request;
input  [CFG_DATA_WIDTH - 1 : 0] write_data;

input                           read_request;
output [CFG_DATA_WIDTH - 1 : 0] read_data;
output                          read_data_valid;

output                          fifo_empty;
output                          fifo_full;

    wire [CFG_DATA_WIDTH - 1 : 0] read_data;
    wire                          read_data_valid;
    wire                          direct_fifo_empty;
    wire                          fifo_empty;
    wire                          fifo_full;


wire int_write_request;
wire [CFG_DATA_WIDTH - 1 : 0] int_write_data;

generate
   genvar stage;
   
   if (CFG_REGISTERED_INPUT == 0) begin: input_no_pipe
      assign int_write_request = write_request;
      assign int_write_data = write_data;
   end
   else begin : input_pipe
      reg                          write_request_pipe [CFG_REGISTERED_INPUT_STAGES - 1 : 0];
      reg [CFG_DATA_WIDTH - 1 : 0] write_data_pipe    [CFG_REGISTERED_INPUT_STAGES - 1 : 0];
      
      assign int_write_request = write_request_pipe [CFG_REGISTERED_INPUT_STAGES - 1];
      assign int_write_data    = write_data_pipe    [CFG_REGISTERED_INPUT_STAGES - 1];

      for (stage = 0; stage < CFG_REGISTERED_INPUT_STAGES; stage = stage + 1)
      begin : stage_gen
         always @(posedge ctl_clk) begin
            write_request_pipe[stage] <= (stage == 0) ? write_request : write_request_pipe[stage-1];
            write_data_pipe   [stage] <= (stage == 0) ? write_data    : write_data_pipe   [stage-1];
         end
      end
   end
endgenerate

    scfifo #
    (
        .add_ram_output_register    (SCFIFO_REGISTERED_OUTPUT   ),
        .enable_ecc                 ("FALSE"                    ),
        .intended_device_family     ("Stratix 10"               ),
        .lpm_numwords               (SCFIFO_DEPTH               ),
        .lpm_showahead              (SCFIFO_SHOWAHEAD           ),
        .lpm_type                   ("scfifo"                   ),
        .lpm_width                  (CFG_DATA_WIDTH             ),
        .lpm_widthu                 (CFG_ADDR_WIDTH             ),
        .overflow_checking          ("OFF"                      ),
        .underflow_checking         ("OFF"                      ),
        .use_eab                    (CFG_USE_EAB                )
    )
    scfifo_inst
    (
        .aclr                       ( 1'b0                      ),
        .clock                      ( ctl_clk                   ),
        .data                       ( int_write_data            ),
        .rdreq                      ( read_request              ),
        .wrreq                      ( int_write_request         ),
        .empty                      ( direct_fifo_empty         ),
        .full                       ( fifo_full                 ),
        .q                          ( read_data                 ),
        .almost_empty               (                           ),
        .almost_full                (                           ),
        .sclr                       ( ~ctl_reset_n              ),
        .usedw                      (                           )
    );

generate
   if (CFG_USE_EAB == "ON" && CFG_SHOWAHEAD != 0 && CFG_REGISTERED_OUTPUT != 0) begin : ext_empty_tracker
   
      reg pipe_wrreq_r /* synthesis preserve_syn_only = 1 */;
      reg pipe_wrreq_rr /* synthesis preserve_syn_only = 1 */;
      always @ (posedge ctl_clk)
      begin
         pipe_wrreq_r <= int_write_request;
         pipe_wrreq_rr <= pipe_wrreq_r;
      end

      reg [ENTRIES_COUNTER_WIDTH - 1 : 0] counter;
      reg counter_is_zero;
      reg counter_is_one;

      always @ (posedge ctl_clk)
      begin
         if (~ctl_reset_n) begin
            counter <= {ENTRIES_COUNTER_WIDTH{1'b0}};
            counter_is_zero <= 1'b1;
            counter_is_one <= 1'b0;
         end else begin
            if (pipe_wrreq_rr && ~read_request) begin
               counter <= counter + 1'b1;
               counter_is_zero <= 1'b0;
               counter_is_one <= counter_is_zero;
            end else if (~pipe_wrreq_rr && read_request) begin
               counter <= counter - 1'b1;
               counter_is_zero <= counter_is_one;
               counter_is_one <= (counter == 2);
            end
         end
      end

      assign fifo_empty = counter_is_zero;
      assign read_data_valid = ~counter_is_zero;
   end
   else begin : use_scfifo_empty_tracker
      assign fifo_empty = direct_fifo_empty;
      assign read_data_valid = ~direct_fifo_empty;
   end
endgenerate


endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0EDOk9aHkqOWcF03Flz/QBMSreEuyWo4K6eyOsLyEFYN9On3eZk+elXPo7iY6i+PydkAYxVQfMayJZYIUU2CpWci6DeG5yvciiioyBM9C9TnfFLC35rbm/VIDkBNnR1HQE3A8qOYRXzX7DUX34pdVdNLZf/DYC82NZAuXBEYN0Tn1suTbo7kLNekmusWQQybRj8DarEH32vjE5ieLX7A1ImqW/UNVrjtKEWLBBA+v8CNFOSPeqLJ2J3keLErHE+4i9gAUOotRGIUZSCaHr3hvJowKMQjRFRaVYQBIYFg2QNqMUvB7xXD5D2IBGbggGU52F0AmaOtMX4wJjyZ744NmipE07D7XxvQyrtQ+1kaz0rTl6cDhKf8oFNu23cml5XDbha7Mmd1L2IdARpK5QJbwVDMVLEeb1fAVlPGbovTgwQwPZBeLLoSh32My/TM8GyRgEjWFSH6x4lqqBsG4QyOT3uSZJCy+88a+dbKDm7PMl46Vl7Hx2A5ZImDeYUsM7FmhARCDE76XVnmFD3sFz5wEJxNlix4ubvLd9ske6oYWmAuPnEXPYU9rssBwacS5uQ+4Ke/2e77aLfoNO1Zk9HmuJT/KTswqDbKQZosbw0Vqbo7fTkST2qOrlDM89ZQeA1znKsbV8y+mLy0cDWqj08IfCprwpuD7YTVe1HnIFeEJ4mazaE5bmrraHRmjypEtZXry4jTKEo9mWk/AJ7sFJwCVm//DgvNjNaJCZ0RLcSEjg7b8Ty1PQ1kvSGQ6m7dau//yso84+Q3HU01eiPQdbdPCVJi"
`endif