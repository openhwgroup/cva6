import ariane_pkg::*;

module lsu (
    input  logic         clk_i,
    input  logic         rst_ni,

    // output to data memory
    output logic         data_req_o,
    input  logic         data_gnt_i,
    input  logic         data_rvalid_i,
    input  logic         data_err_i,

    output logic [63:0]  data_addr_o,
    output logic         data_we_o,
    output logic [7:0]   data_be_o,
    output logic [63:0]  data_wdata_o,
    input  logic [63:0]  data_rdata_i,

    input  fu_op         operator_i,
    input  logic [63:0]  operand_a_i,
    input  logic [63:0]  operand_b_i,
    output logic         lsu_ready_o,      // FU is ready e.g. not busy
    input  logic         lsu_valid_i,      // Input is valid
    input  logic         lsu_trans_id_i,   // transaction id, needed for WB
    output logic [4:0]   lsu_trans_id_o,   // ID of scoreboard entry at which to write back
    output logic         lsu_valid_o,      // transaction id for which the output is the requested one

    output exception     lsu_exception_o   // to writeback, signal exception status ld/st exception

);

endmodule