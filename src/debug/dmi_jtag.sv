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
    logic        dtmcs_select;
    logic        dmi_reset;
    logic        dmi_tdi;
    logic        dmi_tdo;

    logic        mem_valid;
    logic        mem_gnt;
    logic [6:0]  mem_addr;
    logic        mem_we;
    logic [31:0] mem_wdata;
    logic [31:0] mem_rdata;
    logic        mem_rvalid;

    typedef struct packed {
        logic [7:0]  address;
        logic [31:0] data;
        logic [1:0]  op;
    } dmi_t;

    typedef enum logic [1:0] {
                                DMINoError = 0, DMIReservedError = 1,
                                DMIOPFailed = 2, DMIBusy = 3
                             } dmi_error_t;

    enum logic [1:0] { Idle, Read, WaitReadValid, Write } state_d, state_q;

    logic [$bits(dmi_t)-1:0] dr_d, dr_q;
    logic [7:0] address_d, address_q;
    logic [31:0] data_d, data_q;

    dmi_t  dmi, read_dmi;
    assign dmi       = dmi_t'(dr_q);
    assign mem_addr  = address_q;
    assign mem_wdata = data_q;
    assign mem_we    = (state_q == Write);

    dmi_error_t error_d, error_q;

    // DMI which we return
    assign read_dmi = {7'b0, data_q, error_q};

    always_comb begin
        // default assignments
        state_d   = state_q;
        address_d = address_q;
        data_d    = data_q;
        error_d   = error_q;

        mem_valid = 1'b0;

        case (state_q)
            Idle: begin
                // make sure that no error is sticky
                if (dmi_access && update_dr && (error_q == DMINoError)) begin
                    // save address and value
                    address_d = dmi.address;
                    data_d = dmi.data;
                    if (dm::dtm_op_t'(dmi.op) == dm::DTM_READ) begin
                        state_d = Read;
                    end else if (dm::dtm_op_t'(dmi.op) == dm::DTM_WRITE) begin
                        state_d = Write;
                    end
                    // else this is a nop and we can stay here
                end
            end

            Read: begin
                mem_valid = 1'b1;
                if (mem_gnt) begin
                    state_d = WaitReadValid;
                end
            end

            WaitReadValid: begin
                // load data into register and shift out
                if (mem_rvalid) begin
                    data_d = mem_rdata;
                    state_d = Idle;
                end
            end

            Write: begin
                mem_valid = 1'b1;
                // got a valid answer go back to idle
                if (mem_gnt) begin
                    state_d = Idle;
                end
            end
        endcase

        // update_dr means we got another request but we didn't finish
        // the one in progress, this state is sticky
        if (update_dr && state_q != Idle) begin
            error_d = DMIBusy;
        end

        // clear sticky error flag
        if (dmi_reset && dtmcs_select) begin
            error_d = DMINoError;
        end
    end

    // shift register
    assign dmi_tdo = dr_q[0];

    always_comb begin
        dr_d    = dr_q;

        if (capture_dr) begin
            if (dmi_access) dr_d = data_q;
        end

        if (shift_dr) begin
            if (dmi_access) dr_d = {dmi_tdi, dr_q[$bits(dr_q)-1:1]};
        end

        if (test_logic_reset) begin
            dr_d = '0;
        end
    end

    always_ff @(posedge tck_i or negedge trst_ni) begin
        if (~trst_ni) begin
            dr_q      <= '0;
            state_q   <= Idle;
            address_q <= '0;
            data_q    <= '0;
            error_q   <= DMINoError;
        end else begin
            dr_q      <= dr_d;
            state_q   <= state_d;
            address_q <= address_d;
            data_q    <= data_d;
            error_q   <= error_d;
        end
    end
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
        .dtmcs_select_o     ( dtmcs_select     ),
        .dmi_reset_o        ( dmi_reset        ),
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
