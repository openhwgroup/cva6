// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`define REGS_MAX_ADR             2'd2

module apb_timer
#(
    parameter APB_ADDR_WIDTH = 12,  //APB slaves are 4KB by default
    parameter TIMER_CNT = 2 // how many timers should be instantiated
)
(
    input  logic                      HCLK,
    input  logic                      HRESETn,
    input  logic [APB_ADDR_WIDTH-1:0] PADDR,
    input  logic               [31:0] PWDATA,
    input  logic                      PWRITE,
    input  logic                      PSEL,
    input  logic                      PENABLE,
    output logic               [31:0] PRDATA,
    output logic                      PREADY,
    output logic                      PSLVERR,

    output logic [(TIMER_CNT * 2) - 1:0] irq_o // overflow and cmp interrupt
);

    logic [TIMER_CNT-1:0] psel_int, pready, pslverr;
    logic [$clog2(TIMER_CNT) - 1:0] slave_address_int;
    logic [TIMER_CNT-1:0] [31:0] prdata;

    assign slave_address_int = PADDR[$clog2(TIMER_CNT)+ `REGS_MAX_ADR + 1:`REGS_MAX_ADR + 2];

    always_comb
    begin
        psel_int = '0;
        psel_int[slave_address_int] = PSEL;
    end

    // output mux
    always_comb
    begin

        if (psel_int != '0)
        begin
            PRDATA = prdata[slave_address_int];
            PREADY = pready[slave_address_int];
            PSLVERR = pslverr[slave_address_int];
        end
        else
        begin
            PRDATA = '0;
            PREADY = 1'b1;
            PSLVERR = 1'b0;
        end
    end


    genvar k;

    generate
    for(k = 0; k < TIMER_CNT; k++)
    begin : TIMER_GEN
      timer #(
          .APB_ADDR_WIDTH ( APB_ADDR_WIDTH )
      ) timer_i (
          .HCLK       ( HCLK          ),
          .HRESETn    ( HRESETn       ),

          .PADDR      ( PADDR        ),
          .PWDATA     ( PWDATA       ),
          .PWRITE     ( PWRITE       ),
          .PSEL       ( psel_int[k]  ),
          .PENABLE    ( PENABLE      ),
          .PRDATA     ( prdata[k]    ),
          .PREADY     ( pready[k]    ),
          .PSLVERR    ( pslverr[k]   ),

          .irq_o      ( irq_o[2*k+1 : 2*k] )
      );
    end
endgenerate
endmodule
