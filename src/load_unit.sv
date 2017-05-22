// Author: Florian Zaruba, ETH Zurich
// Date: 22.05.2017
// Description: Load Unit, takes care of all load requests
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//
import ariane_pkg::*;

module load_unit (
    input  logic                     clk_i,    // Clock
    input  logic                     rst_ni,  // Asynchronous reset active low
    // load unit input port
    input logic [1:0]                operator_i,
    input logic                      valid_i,
    input logic [63:0]               vaddr_i,
    input logic [7:0]                be_i,
    // load unit output port
    output logic                     valid_o,
    output logic                     ready_o,
    output logic [TRANS_ID_BITS-1:0] trans_id_o,
    output logic [63:0]              result_o,
    // MMU -> Address Translation
    output logic                     translation_req_o, // request address translation
    output logic                     vaddr_o,           // virtual address out
    input  logic [63:0]              paddr_i,           // physical address in
    input  logic                     translation_valid_i,
    // address checker
    output logic [11:0]              page_offset_o,
    input  logic                     page_offset_matches_i,
    // memory interface
    output logic [63:0]              address_o,
    output logic [63:0]              data_wdata_o,
    output logic                     data_req_o,
    output logic                     data_we_o,
    output logic [7:0]               data_be_o,
    output logic [1:0]               data_tag_status_o,
    input  logic                     data_gnt_i,
    input  logic                     data_rvalid_i,
    input  logic [63:0]              data_rdata_i
);

    // ---------------
    // Sign Extend
    // ---------------
    logic [63:0] rdata_d_ext; // sign extension for double words, actually only misaligned assembly
    logic [63:0] rdata_w_ext; // sign extension for words
    logic [63:0] rdata_h_ext; // sign extension for half words
    logic [63:0] rdata_b_ext; // sign extension for bytes

    // double words
    always_comb begin : sign_extend_double_word
        rdata_d_ext = data_rdata_i[63:0];
    end

      // sign extension for words
    always_comb begin : sign_extend_word
        case (vaddr_i[2:0])
            default: rdata_w_ext = (operator_i == LW) ? {{32{data_rdata_i[31]}}, data_rdata_i[31:0]}  : {32'h0, data_rdata_i[31:0]};
            3'b001:  rdata_w_ext = (operator_i == LW) ? {{32{data_rdata_i[39]}}, data_rdata_i[39:8]}  : {32'h0, data_rdata_i[39:8]};
            3'b010:  rdata_w_ext = (operator_i == LW) ? {{32{data_rdata_i[47]}}, data_rdata_i[47:16]} : {32'h0, data_rdata_i[47:16]};
            3'b011:  rdata_w_ext = (operator_i == LW) ? {{32{data_rdata_i[55]}}, data_rdata_i[55:24]} : {32'h0, data_rdata_i[55:24]};
            3'b100:  rdata_w_ext = (operator_i == LW) ? {{32{data_rdata_i[63]}}, data_rdata_i[63:32]} : {32'h0, data_rdata_i[63:32]};
        endcase
    end

    // sign extension for half words
    always_comb begin : sign_extend_half_word
        case (vaddr_i[2:0])
            default: rdata_h_ext = (operator_i == LH) ? {{48{data_rdata_i[15]}}, data_rdata_i[15:0]}  : {48'h0, data_rdata_i[15:0]};
            3'b001:  rdata_h_ext = (operator_i == LH) ? {{48{data_rdata_i[23]}}, data_rdata_i[23:8]}  : {48'h0, data_rdata_i[23:8]};
            3'b010:  rdata_h_ext = (operator_i == LH) ? {{48{data_rdata_i[31]}}, data_rdata_i[31:16]} : {48'h0, data_rdata_i[31:16]};
            3'b011:  rdata_h_ext = (operator_i == LH) ? {{48{data_rdata_i[39]}}, data_rdata_i[39:24]} : {48'h0, data_rdata_i[39:24]};
            3'b100:  rdata_h_ext = (operator_i == LH) ? {{48{data_rdata_i[47]}}, data_rdata_i[47:32]} : {48'h0, data_rdata_i[47:32]};
            3'b101:  rdata_h_ext = (operator_i == LH) ? {{48{data_rdata_i[55]}}, data_rdata_i[55:40]} : {48'h0, data_rdata_i[55:40]};
            3'b110:  rdata_h_ext = (operator_i == LH) ? {{48{data_rdata_i[63]}}, data_rdata_i[63:48]} : {48'h0, data_rdata_i[63:48]};
        endcase
    end

    always_comb begin : sign_extend_byte
        case (vaddr_i[2:0])
            default: rdata_b_ext = (operator_i == LB) ? {{56{data_rdata_i[7]}},  data_rdata_i[7:0]}   : {56'h0, data_rdata_i[7:0]};
            3'b001:  rdata_b_ext = (operator_i == LB) ? {{56{data_rdata_i[15]}}, data_rdata_i[15:8]}  : {56'h0, data_rdata_i[15:8]};
            3'b010:  rdata_b_ext = (operator_i == LB) ? {{56{data_rdata_i[23]}}, data_rdata_i[23:16]} : {56'h0, data_rdata_i[23:16]};
            3'b011:  rdata_b_ext = (operator_i == LB) ? {{56{data_rdata_i[31]}}, data_rdata_i[31:24]} : {56'h0, data_rdata_i[31:24]};
            3'b100:  rdata_b_ext = (operator_i == LB) ? {{56{data_rdata_i[39]}}, data_rdata_i[39:32]} : {56'h0, data_rdata_i[39:32]};
            3'b101:  rdata_b_ext = (operator_i == LB) ? {{56{data_rdata_i[47]}}, data_rdata_i[47:40]} : {56'h0, data_rdata_i[47:40]};
            3'b110:  rdata_b_ext = (operator_i == LB) ? {{56{data_rdata_i[55]}}, data_rdata_i[55:48]} : {56'h0, data_rdata_i[55:48]};
            3'b111:  rdata_b_ext = (operator_i == LB) ? {{56{data_rdata_i[63]}}, data_rdata_i[63:56]} : {56'h0, data_rdata_i[63:56]};
        endcase
    end

    always_comb begin
        case (operator_i)
            LW, LWU:       result_o = rdata_w_ext;
            LH, LHU:       result_o = rdata_h_ext;
            LB, LBU:       result_o = rdata_b_ext;
            default:       result_o = rdata_d_ext;
        endcase
    end

endmodule