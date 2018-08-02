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
    input  logic          rst_ni,
    input  logic          ndmreset_i,  // synchronous reset active high

    AXI_BUS.Master        axi_master,

    input  logic [63:0]   sbaddress_i,
    input  logic          sbaddress_write_valid_i,
    // control signals in
    input  logic          sbreadonaddr_i,
    input  logic          sbautoincrement_i,
    input  logic [2:0]    sbaccess_i,
    // data in
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

    // TODO(zarubaf)
    assign sbbusy_o = '0;
    assign sberror_valid_o = '0;
    assign sberror_o = '0;

    logic [63:0] address;
    logic       req;
    logic       gnt;
    logic       we;
    logic [7:0] be;

    always_comb begin
        req = 1'b0;
        address = sbaddress_i;
        we = 1'b0;
        be = 1'b0;
    end

    axi_adapter #(

    ) i_axi_master (
        .clk_i,
        .rst_ni                ( ~ndmreset_i & rst_ni     ),
        .req_i                 ( req                      ),
        .type_i                ( nbdcache_pkg::SINGLE_REQ ),
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
