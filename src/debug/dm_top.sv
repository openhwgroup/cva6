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
 * File:   axi_riscv_debug_module.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   30.6.2018
 *
 * Description: Top-level of debug module (DM). This is an AXI-Slave.
 *              DTM protocol is equal to SiFives debug protocol to leverage
 *              SW infrastructure re-use. As of version 0.13
 */

module dm_top #(
    parameter int NrHarts = -1
)(
    input  logic        clk_i,       // clock
    input  logic        rst_ni,      // asynchronous reset active low, connect PoR here, not the system reset
    output logic        ndmreset_o,  // non-debug module reset
    AXI_BUS.Slave       axi_slave,   // bus slave
    // Connection to DTM - compatible to RocketChip Debug Module
    input  logic        dmi_rst_ni,
    input  logic        dmi_req_valid_i,
    output logic        dmi_req_ready_o,
    input  logic [ 6:0] dmi_req_bits_addr_i,
    input  logic [ 1:0] dmi_req_bits_op_i, // 0 = nop, 1 = read, 2 = write
    input  logic [31:0] dmi_req_bits_data_i,

    output logic        dmi_resp_valid_o,
    input  logic        dmi_resp_ready_i,
    output logic [ 1:0] dmi_resp_bits_resp_o,
    output logic [31:0] dmi_resp_bits_data_o
);

    // Debug CSRs


endmodule
