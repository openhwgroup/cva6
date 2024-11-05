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
* Author: Andreas Traber <atraber@iis.ee.ethz.ch>
* Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
*
* Description: Clock domain crossings for JTAG to DMI very heavily based
*              on previous work by Andreas Traber for the PULP project.
*              This is mainly a wrapper around the existing CDCs.
*/
module dmi_cdc (
  // JTAG side (master side)
  input  logic             tck_i,
  input  logic             trst_ni,
  input  dm::dmi_req_t     jtag_dmi_req_i,
  output logic             jtag_dmi_ready_o,
  input  logic             jtag_dmi_valid_i,
  input  logic             jtag_dmi_cdc_clear_i, // Synchronous clear signal.
                                                 // Triggers reset sequencing
                                                 // accross CDC

  output dm::dmi_resp_t    jtag_dmi_resp_o,
  output logic             jtag_dmi_valid_o,
  input  logic             jtag_dmi_ready_i,

  // core side (slave side)
  input  logic             clk_i,
  input  logic             rst_ni,

  output logic             core_dmi_rst_no,
  output dm::dmi_req_t     core_dmi_req_o,
  output logic             core_dmi_valid_o,
  input  logic             core_dmi_ready_i,

  input dm::dmi_resp_t     core_dmi_resp_i,
  output logic             core_dmi_ready_o,
  input  logic             core_dmi_valid_i
);

  logic                    core_clear_pending;

  cdc_2phase_clearable #(.T(dm::dmi_req_t)) i_cdc_req (
    .src_rst_ni  ( trst_ni              ),
    .src_clear_i ( jtag_dmi_cdc_clear_i ),
    .src_clk_i   ( tck_i                ),
    .src_clear_pending_o(), // Not used
    .src_data_i  ( jtag_dmi_req_i       ),
    .src_valid_i ( jtag_dmi_valid_i     ),
    .src_ready_o ( jtag_dmi_ready_o     ),

    .dst_rst_ni  ( rst_ni               ),
    .dst_clear_i ( 1'b0                 ), // No functional reset from core side
                                           // used (only async).
    .dst_clear_pending_o( core_clear_pending ), // use the clear pending signal
                                                // to synchronously clear the
                                                // response FIFO in the dm_top
                                                // csrs
    .dst_clk_i   ( clk_i                ),
    .dst_data_o  ( core_dmi_req_o       ),
    .dst_valid_o ( core_dmi_valid_o     ),
    .dst_ready_i ( core_dmi_ready_i     )
  );

  cdc_2phase_clearable #(.T(dm::dmi_resp_t)) i_cdc_resp (
    .src_rst_ni  ( rst_ni               ),
    .src_clear_i ( 1'b0                 ), // No functional reset from core side
                                           // used (only async ).
    .src_clear_pending_o(), // Not used
    .src_clk_i   ( clk_i                ),
    .src_data_i  ( core_dmi_resp_i      ),
    .src_valid_i ( core_dmi_valid_i     ),
    .src_ready_o ( core_dmi_ready_o     ),

    .dst_rst_ni  ( trst_ni              ),
    .dst_clear_i ( jtag_dmi_cdc_clear_i ),
    .dst_clear_pending_o(), //Not used
    .dst_clk_i   ( tck_i                ),
    .dst_data_o  ( jtag_dmi_resp_o      ),
    .dst_valid_o ( jtag_dmi_valid_o     ),
    .dst_ready_i ( jtag_dmi_ready_i     )
  );

  // We need to flush the DMI response FIFO in DM top using the core clock
  // synchronous clear signal core_dmi_rst_no. We repurpose the clear
  // pending signal in the core clock domain by generating a 1 cycle pulse from
  // it.

  logic                    core_clear_pending_q;
  logic                    core_dmi_rst_nq;
  logic                    clear_pending_rise_edge_detect;

  assign clear_pending_rise_edge_detect = !core_clear_pending_q && core_clear_pending;

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      core_dmi_rst_nq       <= 1'b1;
      core_clear_pending_q <= 1'b0;
    end else begin
      core_dmi_rst_nq       <= ~clear_pending_rise_edge_detect; // active-low!
      core_clear_pending_q <= core_clear_pending;
    end
  end

  assign core_dmi_rst_no = core_dmi_rst_nq;

endmodule : dmi_cdc
