/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   dm_sba.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   1.8.2018
 *
 * Description: System Bus Access Module
 *
 */

module dm_sba (
    input  logic          clk_i,       // Clock
    input  logic          dmactive_i,  // synchronous reset active low

    AXI_BUS.Master        axi_master,

    input  logic [63:0]   sbaddress_i,
    input  logic          sbaddress_write_valid_i,
    // control signals in
    input  logic          sbreadonaddr_i,
    output logic [63:0]   sbaddress_o,
    input  logic          sbautoincrement_i,
    input  logic [2:0]    sbaccess_i,
    // data in
    input  logic          sbreadondata_i,
    input  logic [63:0]   sbdata_i,
    input  logic          sbdata_read_valid_i,
    input  logic          sbdata_write_valid_i,
    // read data out
    output logic [63:0]   sbdata_o,
    output logic          sbdata_valid_o,
    // control signals
    output logic          sbbusy_o,
    output logic          sberror_valid_o, // bus error occurred
    output logic [2:0]    sberror_o // bus error occurred
);

    enum logic [2:0] { Idle, Read, Write, WaitRead, WaitWrite } state_d, state_q;

    logic [63:0]      address;
    logic             req;
    logic             gnt;
    logic             we;
    logic [7:0][7:0]  be;

    assign sbbusy_o = (state_q != Idle) ? 1'b1 : 1'b0;

    always_comb begin
        req     = 1'b0;
        address = sbaddress_i;
        we      = 1'b0;
        be      = '0;

        sberror_o       = '0;
        sberror_valid_o = 1'b0;
        sbaddress_o     = sbaddress_i;

        state_d = state_q;

        case (state_q)
            Idle: begin
                // debugger requested a read
                if (sbaddress_write_valid_i && sbreadonaddr_i)  state_d = Read;
                // debugger requested a write
                if (sbdata_write_valid_i) state_d = Write;
                // perform another read
                if (sbdata_read_valid_i && sbreadondata_i) state_d = Read;
            end

            Read: begin
                req = 1'b1;
                if (gnt) state_d = WaitRead;
            end

            Write: begin
                req = 1'b1;
                we  = 1'b1;
                // generate byte enable mask
                case (sbaccess_i)
                    3'b000: be[ sbaddress_i[2:0]] = '1;
                    3'b001: be[{sbaddress_i[2:1], 1'b0} +: 1] = '1;
                    3'b010: be[{sbaddress_i[2:2], 2'b0} +: 3] = '1;
                    3'b011: be = '1;
                    default:;
                endcase
                if (gnt) state_d = WaitWrite;
            end

            WaitRead: begin
                if (sbdata_valid_o) begin
                    state_d = Idle;
                    // auto-increment address
                    if (sbautoincrement_i) sbaddress_o = sbaddress_i + (1 << sbaccess_i);
                end
            end

            WaitWrite: begin
                if (sbdata_valid_o) begin
                    state_d = Idle;
                    // auto-increment address
                    if (sbautoincrement_i) sbaddress_o = sbaddress_i + (1 << sbaccess_i);
                end
            end
        endcase
        // handle error case
        if (sbaccess_i > 3 && state_d != Idle) begin
            req             = 1'b0;
            state_d         = Idle;
            sberror_valid_o = 1'b1;
            sberror_o       = 'd3;
        end
        // further error handling should go here ...
    end

    always_ff @(posedge clk_i) begin
        if (~dmactive_i) begin
            state_q <= Idle;
        end else begin
            state_q <= state_d;
        end
    end

    axi_adapter #(
        .DATA_WIDTH            ( 64                       )
    ) i_axi_master (
        .clk_i,
        .rst_ni                ( dmactive_i               ),
        .req_i                 ( req                      ),
        .type_i                ( std_cache_pkg::SINGLE_REQ),
        .gnt_o                 ( gnt                      ),
        .gnt_id_o              (                          ),
        .addr_i                ( address                  ),
        .we_i                  ( we                       ),
        .wdata_i               ( sbdata_i                 ),
        .be_i                  ( be                       ),
        .size_i                ( sbaccess_i               ),
        .id_i                  ( '0                       ),
        .valid_o               ( sbdata_valid_o           ),
        .rdata_o               ( sbdata_o                 ),
        .id_o                  (                          ),
        .critical_word_o       (                          ), // not needed here
        .critical_word_valid_o (                          ), // not needed here
        .axi                   ( axi_master               )
    );
endmodule
