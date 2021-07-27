// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module axi_node_arbiter #(
  parameter int unsigned AUX_WIDTH = 0, // Synopsys DC requires a default value for parameters.
  parameter int unsigned ID_WIDTH = 0,
  parameter int unsigned N_MASTER = 0
) (
  input  logic                                clk_i,
  input  logic                                rst_ni,

  input  logic [N_MASTER-1:0][ID_WIDTH-1:0]   inp_id_i,
  input  logic [N_MASTER-1:0][AUX_WIDTH-1:0]  inp_aux_i,
  input  logic [N_MASTER-1:0]                 inp_valid_i,
  output logic [N_MASTER-1:0]                 inp_ready_o,

  output logic [ID_WIDTH-1:0]                 oup_id_o,
  output logic [AUX_WIDTH-1:0]                oup_aux_o,
  output logic                                oup_valid_o,
  input  logic                                oup_ready_i
);

  typedef struct packed {
    logic [AUX_WIDTH-1:0] aux;
    logic [ID_WIDTH-1:0]  id;
  } axi_meta_t;

  axi_meta_t [N_MASTER-1:0] inp_meta;
  axi_meta_t oup_meta;

  for (genvar i = 0; i < N_MASTER; i++) begin: gen_inp_meta
    assign inp_meta[i].aux = inp_aux_i[i];
    assign inp_meta[i].id = inp_id_i[i];
  end

  stream_arbiter #(
    .DATA_T (axi_meta_t),
    .N_INP  (N_MASTER)
  ) i_arb_inp (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),
    .inp_data_i   (inp_meta),
    .inp_valid_i  (inp_valid_i),
    .inp_ready_o  (inp_ready_o),
    .oup_data_o   (oup_meta),
    .oup_valid_o  (oup_valid_o),
    .oup_ready_i  (oup_ready_i)
  );

  assign oup_id_o = oup_meta.id;
  assign oup_aux_o = oup_meta.aux;

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (AUX_WIDTH >= 1) else $fatal("Minimum width of auxiliary data is 1!");
    assert (ID_WIDTH >= 1) else $fatal("Minimum width of ID is 1!");
    assert (N_MASTER >= 1) else $fatal("Minimum number of masters is 1!");
  end
`endif
// pragma translate_on

endmodule
