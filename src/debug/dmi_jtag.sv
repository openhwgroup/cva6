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
 * Date:   19.7.2018
 *
 * Description: JTAG DMI (debug module interface)
 *
 */

module dmi_jtag (
    input  logic        clk_i,      // DMI Clock
    input  logic        rst_ni,     // Asynchronous reset active low

    output logic        dmi_rst_no, // hard reset

    output logic        dmi_req_valid_o,
    input  logic        dmi_req_ready_i,
    output logic [ 6:0] dmi_req_bits_addr_o,
    output logic [ 1:0] dmi_req_bits_op_o, // 0 = nop, 1 = read, 2 = write
    output logic [31:0] dmi_req_bits_data_o,
    input  logic        dmi_resp_valid_i,
    output logic        dmi_resp_ready_o,
    input  logic [ 1:0] dmi_resp_bits_resp_i,
    input  logic [31:0] dmi_resp_bits_data_i,

    input  logic        tck_i,    // JTAG test clock pad
    input  logic        tms_i,    // JTAG test mode select pad
    input  logic        trst_ni,  // JTAG test reset pad
    input  logic        td_i,     // JTAG test data input pad
    output logic        td_o      // JTAG test data output pad
);

    logic        test_logic_reset;
    logic        run_test_idle;
    logic        shift_dr;
    logic        pause_dr;
    logic        update_dr;
    logic        capture_dr;
    logic        dmi_access;
    logic        dmi_tdi;
    logic        dmi_tdo;

    logic        mem_valid;
    logic        mem_gnt;
    logic [6:0]  mem_addr;
    logic        mem_we;
    logic [31:0] mem_wdata;
    logic [31:0] mem_rdata;
    logic        mem_rvalid;
    logic        mem_rerror;

    // ---------
    // TAP
    // ---------
    dmi_jtag_tap #(
        .IrLength (5)
    ) i_dmi_jtag_tap (
        .tck_i,
        .tms_i,
        .trst_ni,
        .td_i,
        .td_o,
        .test_logic_reset_o ( test_logic_reset ),
        .run_test_idle_o    ( run_test_idle    ),
        .shift_dr_o         ( shift_dr         ),
        .pause_dr_o         ( pause_dr         ),
        .update_dr_o        ( update_dr        ),
        .capture_dr_o       ( capture_dr       ),
        .dmi_access_o       ( dmi_access       ),
        .dmi_tdi_o          ( dmi_tdi          ),
        .dmi_tdo_i          ( dmi_tdo          )
    );

    // ---------
    // CDC
    // ---------
    dmi_cdc i_dmi_cdc (
        // JTAG side (master side)
        .tck_i,
        .trst_ni,

        .mem_valid_i       ( mem_valid   ),
        .mem_gnt_o         ( mem_gnt     ),
        .mem_addr_i        ( mem_addr    ),
        .mem_we_i          ( mem_we      ),
        .mem_wdata_i       ( mem_wdata   ),
        .mem_rdata_o       ( mem_rdata   ),
        .mem_rvalid_o      ( mem_rvalid  ),
        .mem_rerror_o      ( mem_rerror  ),

        .clk_i,
        .rst_ni,
        .dmi_req_valid_o,
        .dmi_req_ready_i,
        .dmi_req_bits_addr_o,
        .dmi_req_bits_op_o,
        .dmi_req_bits_data_o,
        .dmi_resp_valid_i,
        .dmi_resp_ready_o,
        .dmi_resp_bits_resp_i,
        .dmi_resp_bits_data_i
    );

endmodule
