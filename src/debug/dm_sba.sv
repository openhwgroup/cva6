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
    input  logic [63:0]   sbaddress_i,
    input  logic          sbaddress_write_valid_i,
    // control signals in
    input  logic          sbreadonaddr_i,
    input  logic          sbautoincrement_i,
    input  logic [2:0]    sbaccess_i,
    // data out
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

endmodule
