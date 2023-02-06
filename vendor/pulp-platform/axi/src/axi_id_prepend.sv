// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

// AXI ID Prepend: This module prepends/strips the MSB from the AXI IDs.
// Constraints enforced through assertions: ID width of slave and master port

module axi_id_prepend #(
  parameter int unsigned NoBus             = 1,     // Can take multiple axi busses
  parameter int unsigned AxiIdWidthSlvPort = 4,     // AXI ID Width of the Slave Ports
  parameter int unsigned AxiIdWidthMstPort = 6,     // AXI ID Width of the Master Ports
  parameter type         slv_aw_chan_t     = logic, // AW Channel Type for slv port
  parameter type         slv_w_chan_t      = logic, //  W Channel Type for slv port
  parameter type         slv_b_chan_t      = logic, //  B Channel Type for slv port
  parameter type         slv_ar_chan_t     = logic, // AR Channel Type for slv port
  parameter type         slv_r_chan_t      = logic, //  R Channel Type for slv port
  parameter type         mst_aw_chan_t     = logic, // AW Channel Type for mst port
  parameter type         mst_w_chan_t      = logic, //  W Channel Type for mst port
  parameter type         mst_b_chan_t      = logic, //  B Channel Type for mst port
  parameter type         mst_ar_chan_t     = logic, // AR Channel Type for mst port
  parameter type         mst_r_chan_t      = logic, //  R Channel Type for mst port
  // DEPENDENT PARAMETER DO NOT OVERWRITE!
  parameter int unsigned PreIdWidth        = AxiIdWidthMstPort - AxiIdWidthSlvPort
) (
  input  logic [PreIdWidth-1:0] pre_id_i, // ID to be prepended
  // slave port (input), connect master modules here
  // AW channel
  input  slv_aw_chan_t [NoBus-1:0] slv_aw_chans_i,
  input  logic         [NoBus-1:0] slv_aw_valids_i,
  output logic         [NoBus-1:0] slv_aw_readies_o,
  //  W channel
  input  slv_w_chan_t  [NoBus-1:0] slv_w_chans_i,
  input  logic         [NoBus-1:0] slv_w_valids_i,
  output logic         [NoBus-1:0] slv_w_readies_o,
  //  B channel
  output slv_b_chan_t  [NoBus-1:0] slv_b_chans_o,
  output logic         [NoBus-1:0] slv_b_valids_o,
  input  logic         [NoBus-1:0] slv_b_readies_i,
  // AR channel
  input  slv_ar_chan_t [NoBus-1:0] slv_ar_chans_i,
  input  logic         [NoBus-1:0] slv_ar_valids_i,
  output logic         [NoBus-1:0] slv_ar_readies_o,
  //  R channel
  output slv_r_chan_t  [NoBus-1:0] slv_r_chans_o,
  output logic         [NoBus-1:0] slv_r_valids_o,
  input  logic         [NoBus-1:0] slv_r_readies_i,
  // master ports (output), connect slave modules here
  // AW channel
  output mst_aw_chan_t [NoBus-1:0] mst_aw_chans_o,
  output logic         [NoBus-1:0] mst_aw_valids_o,
  input  logic         [NoBus-1:0] mst_aw_readies_i,
  //  W channel
  output mst_w_chan_t  [NoBus-1:0] mst_w_chans_o,
  output logic         [NoBus-1:0] mst_w_valids_o,
  input  logic         [NoBus-1:0] mst_w_readies_i,
  //  B channel
  input  mst_b_chan_t  [NoBus-1:0] mst_b_chans_i,
  input  logic         [NoBus-1:0] mst_b_valids_i,
  output logic         [NoBus-1:0] mst_b_readies_o,
  // AR channel
  output mst_ar_chan_t [NoBus-1:0] mst_ar_chans_o,
  output logic         [NoBus-1:0] mst_ar_valids_o,
  input  logic         [NoBus-1:0] mst_ar_readies_i,
  //  R channel
  input  mst_r_chan_t  [NoBus-1:0] mst_r_chans_i,
  input  logic         [NoBus-1:0] mst_r_valids_i,
  output logic         [NoBus-1:0] mst_r_readies_o
);

  // prepend the ID
  for (genvar i = 0; i < NoBus; i++) begin : gen_id_prepend
    if (PreIdWidth == 0) begin : gen_no_prepend
      assign mst_aw_chans_o[i] = slv_aw_chans_i[i];
      assign mst_ar_chans_o[i] = slv_ar_chans_i[i];
    end else begin : gen_prepend
      always_comb begin
        mst_aw_chans_o[i] = slv_aw_chans_i[i];
        mst_ar_chans_o[i] = slv_ar_chans_i[i];
        mst_aw_chans_o[i].id = {pre_id_i, slv_aw_chans_i[i].id[AxiIdWidthSlvPort-1:0]};
        mst_ar_chans_o[i].id = {pre_id_i, slv_ar_chans_i[i].id[AxiIdWidthSlvPort-1:0]};
      end
    end
    // The ID is in the highest bits of the struct, so an assignment from a channel with a wide ID
    // to a channel with a shorter ID correctly cuts the prepended ID.
    assign slv_b_chans_o[i] = mst_b_chans_i[i];
    assign slv_r_chans_o[i] = mst_r_chans_i[i];
  end

  // assign the handshaking's and w channel
  assign mst_w_chans_o    = slv_w_chans_i;
  assign mst_aw_valids_o  = slv_aw_valids_i;
  assign slv_aw_readies_o = mst_aw_readies_i;
  assign mst_w_valids_o   = slv_w_valids_i;
  assign slv_w_readies_o  = mst_w_readies_i;
  assign slv_b_valids_o   = mst_b_valids_i;
  assign mst_b_readies_o  = slv_b_readies_i;
  assign mst_ar_valids_o  = slv_ar_valids_i;
  assign slv_ar_readies_o = mst_ar_readies_i;
  assign slv_r_valids_o   = mst_r_valids_i;
  assign mst_r_readies_o  = slv_r_readies_i;

// pragma translate_off
`ifndef VERILATOR
  initial begin : p_assert
    assert(NoBus > 0)
      else $fatal(1, "Input must be at least one element wide.");
    assert(PreIdWidth == ($bits(mst_aw_chans_o[0].id) - $bits(slv_aw_chans_i[0].id)))
      else $fatal(1, "Prepend ID Width must be: $bits(mst_aw_chans_o.id)-$bits(slv_aw_chans_i.id)");
    assert ($bits(mst_aw_chans_o[0].id) > $bits(slv_aw_chans_i[0].id))
      else $fatal(1, "The master AXI port has to have a wider ID than the slave port.");
  end

  aw_id   : assert final(
      mst_aw_chans_o[0].id[$bits(slv_aw_chans_i[0].id)-1:0] === slv_aw_chans_i[0].id)
        else $fatal (1, "Something with the AW channel ID prepending went wrong.");
  aw_addr : assert final(mst_aw_chans_o[0].addr === slv_aw_chans_i[0].addr)
      else $fatal (1, "Something with the AW channel ID prepending went wrong.");
  aw_len  : assert final(mst_aw_chans_o[0].len === slv_aw_chans_i[0].len)
      else $fatal (1, "Something with the AW channel ID prepending went wrong.");
  aw_size : assert final(mst_aw_chans_o[0].size === slv_aw_chans_i[0].size)
      else $fatal (1, "Something with the AW channel ID prepending went wrong.");
  aw_qos  : assert final(mst_aw_chans_o[0].qos === slv_aw_chans_i[0].qos)
      else $fatal (1, "Something with the AW channel ID prepending went wrong.");

  b_id    : assert final(
      mst_b_chans_i[0].id[$bits(slv_b_chans_o[0].id)-1:0] === slv_b_chans_o[0].id)
        else $fatal (1, "Something with the B channel ID stripping went wrong.");
  b_resp  : assert final(mst_b_chans_i[0].resp === slv_b_chans_o[0].resp)
      else $fatal (1, "Something with the B channel ID stripping went wrong.");

  ar_id   : assert final(
      mst_ar_chans_o[0].id[$bits(slv_ar_chans_i[0].id)-1:0] === slv_ar_chans_i[0].id)
        else $fatal (1, "Something with the AR channel ID prepending went wrong.");
  ar_addr : assert final(mst_ar_chans_o[0].addr === slv_ar_chans_i[0].addr)
      else $fatal (1, "Something with the AR channel ID prepending went wrong.");
  ar_len  : assert final(mst_ar_chans_o[0].len === slv_ar_chans_i[0].len)
      else $fatal (1, "Something with the AR channel ID prepending went wrong.");
  ar_size : assert final(mst_ar_chans_o[0].size === slv_ar_chans_i[0].size)
      else $fatal (1, "Something with the AR channel ID prepending went wrong.");
  ar_qos  : assert final(mst_ar_chans_o[0].qos === slv_ar_chans_i[0].qos)
      else $fatal (1, "Something with the AR channel ID prepending went wrong.");

  r_id    : assert final(mst_r_chans_i[0].id[$bits(slv_r_chans_o[0].id)-1:0] === slv_r_chans_o[0].id)
      else $fatal (1, "Something with the R channel ID stripping went wrong.");
  r_data  : assert final(mst_r_chans_i[0].data === slv_r_chans_o[0].data)
      else $fatal (1, "Something with the R channel ID stripping went wrong.");
  r_resp  : assert final(mst_r_chans_i[0].resp === slv_r_chans_o[0].resp)
      else $fatal (1, "Something with the R channel ID stripping went wrong.");
`endif
// pragma translate_on
endmodule
