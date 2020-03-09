// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// define three registers per timer - timer, cmp and prescaler registers
`define REGS_MAX_IDX             'd2
`define REG_TIMER                 2'b00
`define REG_TIMER_CTRL            2'b01
`define REG_CMP                   2'b10
`define PRESCALER_STARTBIT        'd3
`define PRESCALER_STOPBIT         'd5
`define ENABLE_BIT                'd0

module timer
#(
    parameter APB_ADDR_WIDTH = 12  //APB slaves are 4KB by default
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

    output logic                [1:0] irq_o // overflow and cmp interrupt
);

    // APB register interface
    logic [`REGS_MAX_IDX-1:0]       register_adr;
    assign register_adr = PADDR[`REGS_MAX_IDX + 2:2];
    // APB logic: we are always ready to capture the data into our regs
    // not supporting transfare failure
    assign PREADY  = 1'b1;
    assign PSLVERR = 1'b0;
    // registers
    logic [0:`REGS_MAX_IDX] [31:0]  regs_q, regs_n;
    logic [31:0] cycle_counter_n, cycle_counter_q;

    logic [2:0] prescaler_int;

    //irq logic
    always_comb
    begin
        irq_o = 2'b0;

        // overlow irq
        if (regs_q[`REG_TIMER] == 32'hffff_ffff)
            irq_o[0] = 1'b1;

        // compare match irq if compare reg ist set
        if (regs_q[`REG_CMP] != 'b0 && regs_q[`REG_TIMER] == regs_q[`REG_CMP])
            irq_o[1] = 1'b1;

    end

    assign prescaler_int = regs_q[`REG_TIMER_CTRL][`PRESCALER_STOPBIT:`PRESCALER_STARTBIT];
    // register write logic
    always_comb
    begin
        regs_n = regs_q;
        cycle_counter_n = cycle_counter_q + 1;

        // reset timer after cmp or overflow
        if (irq_o[0] == 1'b1 || irq_o[1] == 1'b1)
            regs_n[`REG_TIMER] = 1'b0;
        else if(regs_q[`REG_TIMER_CTRL][`ENABLE_BIT] && prescaler_int != 'b0 && prescaler_int == cycle_counter_q) // prescaler
        begin
            regs_n[`REG_TIMER] = regs_q[`REG_TIMER] + 1; //prescaler mode
        end
        else if (regs_q[`REG_TIMER_CTRL][`ENABLE_BIT] && regs_q[`REG_TIMER_CTRL][`PRESCALER_STOPBIT:`PRESCALER_STARTBIT] == 'b0) // normal count mode
            regs_n[`REG_TIMER] = regs_q[`REG_TIMER] + 1;

        // reset prescaler cycle counter
        if (cycle_counter_q >= regs_q[`REG_TIMER_CTRL])
            cycle_counter_n = 32'b0;

        // written from APB bus - gets priority
        if (PSEL && PENABLE && PWRITE)
        begin

            case (register_adr)
                `REG_TIMER:
                    regs_n[`REG_TIMER] = PWDATA;

                `REG_TIMER_CTRL:
                    regs_n[`REG_TIMER_CTRL] = PWDATA;

                `REG_CMP:
                begin
                    regs_n[`REG_CMP] = PWDATA;
                    regs_n[`REG_TIMER] = 32'b0; // reset timer if compare register is written
                end
            endcase
        end
    end

    // APB register read logic
    always_comb
    begin
        PRDATA = 'b0;

        if (PSEL && PENABLE && !PWRITE)
        begin

            case (register_adr)
                `REG_TIMER:
                    PRDATA = regs_q[`REG_TIMER];

                `REG_TIMER_CTRL:
                    PRDATA = regs_q[`REG_TIMER_CTRL];

                `REG_CMP:
                    PRDATA = regs_q[`REG_CMP];
            endcase

        end
    end
    // synchronouse part
    always_ff @(posedge HCLK, negedge HRESETn)
    begin
        if(~HRESETn)
        begin
            regs_q          <= '{default: 32'b0};
            cycle_counter_q <= 32'b0;
        end
        else
        begin
            regs_q          <= regs_n;
            cycle_counter_q <= cycle_counter_n;
        end
    end


endmodule
