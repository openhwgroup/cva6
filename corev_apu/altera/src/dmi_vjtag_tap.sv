/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright 2024 Thales AVS
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   dmi_jtag_tap.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   19.7.2018
 * Additional contributions by Nicolas Levasseur, Thales AVS
 * Date:   8.11.2024
 * Description: vJTAG TAP for DMI to be able to use vJTAG IP
 *
 */

module dmi_vjtag_tap #(
  parameter int unsigned IrLength = 10,
  // JTAG IDCODE Value
  parameter logic [31:0] IdcodeValue = 32'h00000001
  // xxxx             version
  // xxxxxxxxxxxxxxxx part number
  // xxxxxxxxxxx      manufacturer id
  // 1                required by standard
) (
  input   logic                tck_i,              // JTAG test clock pad
  input   logic                trst_ni,            // JTAG test reset pad
  input   logic                td_i,               // JTAG test data input pad
  output  logic                td_o,               // JTAG test data output pad
  output  logic                tdo_oe_o,           // Data output enable
  input   logic                testmode_i,
  input   logic[IrLength-1:0]  ir_in_i,            // Virtual IR in
  input   logic                jtag_state_tlr_i,     // Test logic reset
  input   logic                virtual_state_cdr_i,  // Virtual Captude DR
  input   logic                virtual_state_sdr_i,  // Virtual Shift DR
  input   logic                virtual_state_udr_i,  // Virutal Update DR

  // we want to access DMI register
  output logic        dmi_access_o,
  // JTAG is interested in writing the DTM CSR register
  output logic        dtmcs_select_o,
  // clear error state
  output logic        dmi_reset_o,
  input  logic [1:0]  dmi_error_i,
  // test data to submodule
  output logic        dmi_tdi_o,
  // test data in from submodule
  input  logic        dmi_tdo_i
);

  // to submodule
  assign dmi_tdi_o = td_i;

  typedef enum logic [IrLength-1:0] {
    BYPASS0   = (IrLength)'('h0),
    IDCODE    = (IrLength)'('h1),
    DTMCSR    = (IrLength)'('h10),
    DMIACCESS = (IrLength)'('h11),
    BYPASS1   = (IrLength)'('h1f)
  } ir_reg_e;

  typedef struct packed {
    logic [31:18] zero1;
    logic         dmihardreset;
    logic         dmireset;
    logic         zero0;
    logic [14:12] idle;
    logic [11:10] dmistat;
    logic [9:4]   abits;
    logic [3:0]   version;
  } dtmcs_t;

  // ----------------
  // TAP DR Regs
  // ----------------
  // - Bypass
  // - IDCODE
  // - DTM CS
  logic [31:0] idcode_d, idcode_q;
  logic        idcode_select;
  logic        bypass_select;
  dtmcs_t      dtmcs_d, dtmcs_q;
  logic        bypass_d, bypass_q;  // this is a 1-bit register

  assign dmi_reset_o = dtmcs_q.dmireset;

  always_comb begin
    idcode_d = idcode_q;
    bypass_d = bypass_q;
    dtmcs_d  = dtmcs_q;

    if (virtual_state_cdr_i) begin
      if (idcode_select) idcode_d = IdcodeValue;
      if (bypass_select) bypass_d = 1'b0;
      if (dtmcs_select_o) begin
        dtmcs_d  = '{
                      zero1        : '0,
                      dmihardreset : 1'b0,
                      dmireset     : 1'b0,
                      zero0        : '0,
                      idle         : 3'd1, // 1: Enter Run-Test/Idle and leave it immediately
                      dmistat      : dmi_error_i, // 0: No error, 2: Op failed, 3: too fast
                      abits        : 6'd7, // The size of address in dmi
                      version      : 4'd1  // Version described in spec version 0.13 (and later?)
                    };
      end
    end

    if (virtual_state_sdr_i) begin
      if (idcode_select)  idcode_d = {td_i, 31'(idcode_q >> 1)};
      if (bypass_select)  bypass_d = td_i;
      if (dtmcs_select_o) dtmcs_d  = {td_i, 31'(dtmcs_q >> 1)};
    end

    if (jtag_state_tlr_i) begin
      idcode_d = IdcodeValue;
      bypass_d = 1'b0;
    end
  end

  // ----------------
  // Data reg select
  // ----------------
  always_comb begin : p_data_reg_sel
    dmi_access_o   = 1'b0;
    dtmcs_select_o = 1'b0;
    idcode_select  = 1'b0;
    bypass_select  = 1'b0;

    unique case (ir_in_i)
      BYPASS0:   bypass_select  = 1'b1;
      IDCODE:    idcode_select  = 1'b1;
      DTMCSR:    dtmcs_select_o = 1'b1;
      DMIACCESS: dmi_access_o   = 1'b1;
      BYPASS1:   bypass_select  = 1'b1;
      default:   bypass_select  = 1'b1;
    endcase
  end

  // ----------------
  // Output select
  // ----------------
  logic tdo_mux;

  always_comb begin : p_out_sel
    // here we are shifting the DR register
    unique case (ir_in_i)
      IDCODE:         tdo_mux = idcode_d[0];     // Reading ID code
      DTMCSR:         tdo_mux = dtmcs_d.version[0];
      DMIACCESS:      tdo_mux = dmi_tdo_i;       // Read from DMI TDO
      default:        tdo_mux = bypass_d;      // BYPASS instruction
    endcase
  end

  // ----------------
  // DFT
  // ----------------
  logic tck_n, tck_ni;

  cluster_clock_inverter i_tck_inv (
    .clk_i ( tck_i  ),
    .clk_o ( tck_ni )
  );

  pulp_clock_mux2 i_dft_tck_mux (
    .clk0_i    ( tck_ni     ),
    .clk1_i    ( tck_i      ), // bypass the inverted clock for testing
    .clk_sel_i ( testmode_i ),
    .clk_o     ( tck_n      )
  );

  // TDO changes state at negative edge of TCK
  always_ff @(posedge tck_n, negedge trst_ni) begin : p_tdo_regs
    if (!trst_ni) begin
      td_o     <= 1'b0;
      tdo_oe_o <= 1'b0;
    end else begin
      td_o     <= tdo_mux;
      tdo_oe_o <= virtual_state_sdr_i;
    end
  end

  always_ff @(posedge tck_i or negedge trst_ni) begin : p_regs
    if (!trst_ni) begin
      idcode_q    <= IdcodeValue;
      bypass_q    <= 1'b0;
      dtmcs_q     <= '0;
    end else begin
      idcode_q    <= idcode_d;
      bypass_q    <= bypass_d;
      dtmcs_q     <= dtmcs_d;
    end
  end

endmodule : dmi_vjtag_tap
