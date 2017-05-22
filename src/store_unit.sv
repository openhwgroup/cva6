// Author: Florian Zaruba, ETH Zurich
// Date: 22.05.2017
// Description: Store Unit, takes care of all store requests
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

import ariane_pkg::*;

module store_unit (
    input logic                      clk_i,    // Clock
    input logic                      rst_ni,  // Asynchronous reset active low
    input logic                      flush_i,
    // store unit input port
    input  fu_op                     operator_i,
    input  logic [TRANS_ID_BITS-1:0] trans_id_i,
    input  logic                     valid_i,
    input  logic [63:0]              vaddr_i,
    input  logic [7:0]               be_i,
    input  logic [63:0]              data_i,
    input  logic                     commit_i,
    // store unit output port
    output logic                     valid_o,
    output logic                     ready_o,
    output logic [TRANS_ID_BITS-1:0] trans_id_o,
    output logic [63:0]              result_o,
    // MMU -> Address Translation
    output logic                     translation_req_o, // request address translation
    output logic [63:0]              vaddr_o,           // virtual address out
    input  logic [63:0]              paddr_i,           // physical address in
    input  logic                     translation_valid_i,
    // address checker
    input  logic [11:0]              page_offset_i,
    output logic                     page_offset_matches_o,
    // memory interface
    output logic [63:0]              address_o,
    output logic [63:0]              data_wdata_o,
    output logic                     data_req_o,
    output logic                     data_we_o,
    output logic [7:0]               data_be_o,
    output logic [1:0]               data_tag_status_o,
    input  logic                     data_gnt_i,
    input  logic                     data_rvalid_i
);
    assign result_o = 64'b0;

    logic [63:0]             st_buffer_paddr;   // physical address for store
    logic [63:0]             st_buffer_data;  // store buffer data out
    logic [7:0]              st_buffer_be;
    logic                    st_buffer_valid;
    // store buffer control signals
    logic                    st_ready;
    logic                    st_valid;

    assign vaddr_o = vaddr_i;
    // ---------------
    // Store Control
    // ---------------
    always_comb begin : store_control
        translation_req_o = 1'b0;
        valid_o           = 1'b0;
        ready_o           = 1'b1;
        trans_id_o        = trans_id_i;
        st_valid          = 1'b0;
        // we got a valid store
        if (valid_i) begin
            // first do address translation, we need to do it in the first cycle since we want to share the MMU
            // between the load and the store unit. But we only know that when a new request arrives that we are not using
            // it at the same time.
            translation_req_o = 1'b1;
            // check if translation was valid and we have space in the store buffer
            // otherwise simply stall
            if (translation_valid_i && st_ready) begin
                valid_o  = 1'b0;
                // post this store to the store buffer
                st_valid = 1'b1;
            // translation was not successful - stall here
            end else begin
                ready_o = 1'b0;
            end
        end
    end

    // ---------------
    // Store Queue
    // ---------------
    store_queue store_queue_i (
        // store queue write port
        .valid_i           ( st_valid            ),
        // store buffer in
        .paddr_o           ( st_buffer_paddr     ),
        .data_o            ( st_buffer_data      ),
        .valid_o           ( st_buffer_valid     ),
        .be_o              ( st_buffer_be        ),
        .ready_o           ( st_ready            ),
        .*
    );
    // ------------------
    // Address Checker
    // ------------------
    // The load should return the data stored by the most recent store to the
    // same physical address.  The most direct way to implement this is to
    // maintain physical addresses in the store buffer.

    // Of course, there are other micro-architectural techniques to accomplish
    // the same thing: you can interlock and wait for the store buffer to
    // drain if the load VA matches any store VA modulo the page size (i.e.
    // bits 11:0).  As a special case, it is correct to bypass if the full VA
    // matches, and no younger stores' VAs match in bits 11:0.
    //
    // checks if the requested load is in the store buffer
    // page offsets are virtually and physically the same
    always_comb begin : address_checker
        page_offset_matches_o = 1'b0;
        // check if the LSBs are identical and the entry is valid
        if ((vaddr_i[11:3] == st_buffer_paddr[11:3]) && st_buffer_valid) begin
            page_offset_matches_o = 1'b1;
        end
    end

endmodule