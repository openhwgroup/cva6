// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 22.05.2017
// Description: Load Unit, takes care of all load requests

import ariane_pkg::*;

module load_unit (
    input  logic                     clk_i,    // Clock
    input  logic                     rst_ni,   // Asynchronous reset active low
    input  logic                     flush_i,
    // load unit input port
    input  logic                     valid_i,
    input  lsu_ctrl_t                lsu_ctrl_i,
    output logic                     pop_ld_o,
    // load unit output port
    output logic                     valid_o,
    output logic [TRANS_ID_BITS-1:0] trans_id_o,
    output logic [63:0]              result_o,
    output exception_t               ex_o,
    // MMU -> Address Translation
    output logic                     translation_req_o,   // request address translation
    output logic [63:0]              vaddr_o,             // virtual address out
    input  logic [63:0]              paddr_i,             // physical address in
    input  exception_t               ex_i,                // exception which may has happened earlier. for example: mis-aligned exception
    input  logic                     dtlb_hit_i,          // hit on the dtlb, send in the same cycle as the request
    // address checker
    output logic [11:0]              page_offset_o,
    input  logic                     page_offset_matches_i,
    // D$ interface
    input dcache_req_o_t             req_port_i,
    output dcache_req_i_t            req_port_o  
);
    enum logic [2:0] {IDLE, WAIT_GNT, SEND_TAG, WAIT_PAGE_OFFSET, ABORT_TRANSACTION, WAIT_TRANSLATION, WAIT_FLUSH} NS, CS;
    // in order to decouple the response interface from the request interface we need a
    // a queue which can hold all outstanding memory requests
    struct packed {
        logic [TRANS_ID_BITS-1:0] trans_id;
        logic [2:0]               address_offset;
        fu_op                     operator;
    } load_data_n, load_data_q, in_data;

    // page offset is defined as the lower 12 bits, feed through for address checker
    assign page_offset_o = lsu_ctrl_i.vaddr[11:0];
    // feed-through the virtual address for VA translation
    assign vaddr_o = lsu_ctrl_i.vaddr;
    // this is a read-only interface so set the write enable to 0
    assign req_port_o.data_we = 1'b0;
    // compose the queue data, control is handled in the FSM
    assign in_data = {lsu_ctrl_i.trans_id, lsu_ctrl_i.vaddr[2:0], lsu_ctrl_i.operator};
    // output address
    // we can now output the lower 12 bit as the index to the cache
    assign req_port_o.address_index = lsu_ctrl_i.vaddr[11:0];
    // translation from last cycle, again: control is handled in the FSM
    assign req_port_o.address_tag   = paddr_i[55:12];
    // directly output an exception
    assign ex_o = ex_i;

    // ---------------
    // Load Control
    // ---------------
    always_comb begin : load_control
        // default assignments
        NS                   = CS;
        load_data_n          = load_data_q;
        translation_req_o    = 1'b0;
        req_port_o.data_req  = 1'b0;
        // tag control
        req_port_o.kill_req  = 1'b0;
        req_port_o.tag_valid = 1'b0;
        req_port_o.data_be   = lsu_ctrl_i.be;
        req_port_o.data_size = extract_transfer_size(lsu_ctrl_i.operator);
        pop_ld_o             = 1'b0;

        case (CS)
            IDLE: begin
                // we've got a new load request
                if (valid_i) begin
                    // start the translation process even though we do not know if the addresses match
                    // this should ease timing
                    translation_req_o = 1'b1;
                    // check if the page offset matches with a store, if it does then stall and wait
                    if (!page_offset_matches_i) begin
                        // make a load request to memory
                        req_port_o.data_req = 1'b1;
                        // we got no data grant so wait for the grant before sending the tag
                        if (!req_port_i.data_gnt) begin
                            NS = WAIT_GNT;
                        end else begin
                            if (dtlb_hit_i) begin
                                // we got a grant and a hit on the DTLB so we can send the tag in the next cycle
                                NS = SEND_TAG;
                                pop_ld_o = 1'b1;
                            end else
                                NS = ABORT_TRANSACTION;
                        end
                    end else begin
                        // wait for the store buffer to train and the page offset to not match anymore
                        NS = WAIT_PAGE_OFFSET;
                    end
                end
            end

            // wait here for the page offset to not match anymore
            WAIT_PAGE_OFFSET: begin
                // we make a new request as soon as the page offset does not match anymore
                if (!page_offset_matches_i) begin
                    NS = WAIT_GNT;
                end
            end

            // abort the previous request - free the D$ arbiter
            // we are here because of a TLB miss, we need to abort the current request and give way for the
            // PTW walker to satisfy the TLB miss
            ABORT_TRANSACTION: begin
                req_port_o.kill_req  = 1'b1;
                req_port_o.tag_valid = 1'b1;
                // redo the request by going back to the wait gnt state
                NS          = WAIT_TRANSLATION;
            end

            WAIT_TRANSLATION: begin
                translation_req_o = 1'b1;
                // we've got a hit and we can continue with the request process
                if (dtlb_hit_i)
                    NS = WAIT_GNT;
            end

            WAIT_GNT: begin
                // keep the translation request up
                translation_req_o = 1'b1;
                // keep the request up
                req_port_o.data_req = 1'b1;
                // we finally got a data grant
                if (req_port_i.data_gnt) begin
                    // so we send the tag in the next cycle
                    if (dtlb_hit_i) begin
                        NS = SEND_TAG;
                        pop_ld_o = 1'b1;
                    end else // should we not have hit on the TLB abort this transaction an retry later
                        NS = ABORT_TRANSACTION;
                end
                // otherwise we keep waiting on our grant
            end
            // we know for sure that the tag we want to send is valid
            SEND_TAG: begin
                req_port_o.tag_valid = 1'b1;
                NS = IDLE;
                // we can make a new request here if we got one
                if (valid_i) begin
                    // start the translation process even though we do not know if the addresses match
                    // this should ease timing
                    translation_req_o = 1'b1;
                    // check if the page offset matches with a store, if it does stall and wait
                    if (!page_offset_matches_i) begin
                        // make a load request to memory
                        req_port_o.data_req = 1'b1;
                        // we got no data grant so wait for the grant before sending the tag
                        if (!req_port_i.data_gnt) begin
                            NS = WAIT_GNT;
                        end else begin
                            // we got a grant so we can send the tag in the next cycle
                            if (dtlb_hit_i) begin
                                // we got a grant and a hit on the DTLB so we can send the tag in the next cycle
                                NS = SEND_TAG;
                                pop_ld_o = 1'b1;
                            end else // we missed on the TLB -> wait for the translation
                                NS = ABORT_TRANSACTION;
                        end
                    end else begin
                        // wait for the store buffer to train and the page offset to not match anymore
                        NS = WAIT_PAGE_OFFSET;
                    end
                end
                // ----------
                // Exception
                // ----------
                // if we got an exception we need to kill the request immediately
                if (ex_i.valid) begin
                    req_port_o.kill_req = 1'b1;
                end
            end

            WAIT_FLUSH: begin
                // the D$ arbiter will take care of presenting this to the memory only in case we
                // have an outstanding request
                req_port_o.kill_req  = 1'b1;
                req_port_o.tag_valid = 1'b1;
                // we've killed the current request so we can go back to idle
                NS = IDLE;
            end

        endcase

        // we got an exception
        if (ex_i.valid && valid_i) begin
            // the next state will be the idle state
            NS = IDLE;
            // pop load - but only if we are not getting an rvalid in here - otherwise we will over-wright an incoming transaction
            if (!req_port_i.data_rvalid)
                pop_ld_o = 1'b1;
        end

        // save the load data for later usage -> we should not clutter the load_data register
        if (pop_ld_o && !ex_i.valid) begin
            load_data_n = in_data;
        end

        // if we just flushed and the queue is not empty or we are getting an rvalid this cycle wait in a extra stage
        if (flush_i) begin
            NS = WAIT_FLUSH;
        end
    end

    // ---------------
    // Retire Load
    // ---------------
    // decoupled rvalid process
    always_comb begin : rvalid_output
        valid_o = 1'b0;
        // output the queue data directly, the valid signal is set corresponding to the process above
        trans_id_o = load_data_q.trans_id;
        // we got an rvalid and are currently not flushing and not aborting the request
        if (req_port_i.data_rvalid && CS != WAIT_FLUSH) begin
            // we killed the request
            if(!req_port_o.kill_req)
                valid_o = 1'b1;
            // the output is also valid if we got an exception
            if (ex_i.valid)
                valid_o = 1'b1;
        end
        // an exception occurred during translation (we need to check for the valid flag because we could also get an
        // exception from the store unit)
        // exceptions can retire out-of-order -> but we need to give priority to non-excepting load and stores
        // so we simply check if we got an rvalid if so we prioritize it by not retiring the exception - we simply go for another
        // round in the load FSM
        if (valid_i && ex_i.valid && !req_port_i.data_rvalid) begin
            valid_o    = 1'b1;
            trans_id_o = lsu_ctrl_i.trans_id;
        // if we are waiting for the translation to finish do not give a valid signal yet
        end else if (CS == WAIT_TRANSLATION) begin
            valid_o = 1'b0;
        end

    end


    // latch physical address for the tag cycle (one cycle after applying the index)
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            CS          <= IDLE;
            load_data_q <= '0;
        end else begin
            CS          <= NS;
            load_data_q <= load_data_n;
        end
    end

    // ---------------
    // AMO Operation
    // ---------------
    always_comb begin : amo_op_select
        req_port_o.amo_op = AMO_NONE;

        if (lsu_ctrl_i.valid) begin
            case (lsu_ctrl_i.operator)
                AMO_LRW:    req_port_o.amo_op = AMO_LR;
                AMO_LRD:    req_port_o.amo_op = AMO_LR;
                AMO_SCW:    req_port_o.amo_op = AMO_SC;
                AMO_SCD:    req_port_o.amo_op = AMO_SC;
                AMO_SWAPW:  req_port_o.amo_op = AMO_SWAP;
                AMO_ADDW:   req_port_o.amo_op = AMO_ADD;
                AMO_ANDW:   req_port_o.amo_op = AMO_AND;
                AMO_ORW:    req_port_o.amo_op = AMO_OR;
                AMO_XORW:   req_port_o.amo_op = AMO_XOR;
                AMO_MAXW:   req_port_o.amo_op = AMO_MAX;
                AMO_MAXWU:  req_port_o.amo_op = AMO_MAXU;
                AMO_MINW:   req_port_o.amo_op = AMO_MIN;
                AMO_MINWU:  req_port_o.amo_op = AMO_MINU;
                AMO_SWAPD:  req_port_o.amo_op = AMO_SWAP;
                AMO_ADDD:   req_port_o.amo_op = AMO_ADD;
                AMO_ANDD:   req_port_o.amo_op = AMO_AND;
                AMO_ORD:    req_port_o.amo_op = AMO_OR;
                AMO_XORD:   req_port_o.amo_op = AMO_XOR;
                AMO_MAXD:   req_port_o.amo_op = AMO_MAX;
                AMO_MAXDU:  req_port_o.amo_op = AMO_MAXU;
                AMO_MIND:   req_port_o.amo_op = AMO_MIN;
                AMO_MINDU:  req_port_o.amo_op = AMO_MINU;
                default: req_port_o.amo_op = AMO_NONE;
            endcase
        end
    end

    // ---------------
    // Sign Extend
    // ---------------
    logic [63:0] rdata_d_ext; // sign extension for double words, actually only misaligned assembly
    logic [63:0] rdata_w_ext; // sign extension for words
    logic [63:0] rdata_h_ext; // sign extension for half words
    logic [63:0] rdata_b_ext; // sign extension for bytes

    // double words
    always_comb begin : sign_extend_double_word
        rdata_d_ext = req_port_i.data_rdata[63:0];
    end

    // sign extension for words
    always_comb begin : sign_extend_word
        case (load_data_q.address_offset)
            default: rdata_w_ext = (load_data_q.operator == LW) ? {{32{req_port_i.data_rdata[31]}}, req_port_i.data_rdata[31:0]}  : {32'h0, req_port_i.data_rdata[31:0]};
            3'b001:  rdata_w_ext = (load_data_q.operator == LW) ? {{32{req_port_i.data_rdata[39]}}, req_port_i.data_rdata[39:8]}  : {32'h0, req_port_i.data_rdata[39:8]};
            3'b010:  rdata_w_ext = (load_data_q.operator == LW) ? {{32{req_port_i.data_rdata[47]}}, req_port_i.data_rdata[47:16]} : {32'h0, req_port_i.data_rdata[47:16]};
            3'b011:  rdata_w_ext = (load_data_q.operator == LW) ? {{32{req_port_i.data_rdata[55]}}, req_port_i.data_rdata[55:24]} : {32'h0, req_port_i.data_rdata[55:24]};
            3'b100:  rdata_w_ext = (load_data_q.operator == LW) ? {{32{req_port_i.data_rdata[63]}}, req_port_i.data_rdata[63:32]} : {32'h0, req_port_i.data_rdata[63:32]};
        endcase
    end

    // sign extension for half words
    always_comb begin : sign_extend_half_word
        case (load_data_q.address_offset)
            default: rdata_h_ext = (load_data_q.operator == LH) ? {{48{req_port_i.data_rdata[15]}}, req_port_i.data_rdata[15:0]}  : {48'h0, req_port_i.data_rdata[15:0]};
            3'b001:  rdata_h_ext = (load_data_q.operator == LH) ? {{48{req_port_i.data_rdata[23]}}, req_port_i.data_rdata[23:8]}  : {48'h0, req_port_i.data_rdata[23:8]};
            3'b010:  rdata_h_ext = (load_data_q.operator == LH) ? {{48{req_port_i.data_rdata[31]}}, req_port_i.data_rdata[31:16]} : {48'h0, req_port_i.data_rdata[31:16]};
            3'b011:  rdata_h_ext = (load_data_q.operator == LH) ? {{48{req_port_i.data_rdata[39]}}, req_port_i.data_rdata[39:24]} : {48'h0, req_port_i.data_rdata[39:24]};
            3'b100:  rdata_h_ext = (load_data_q.operator == LH) ? {{48{req_port_i.data_rdata[47]}}, req_port_i.data_rdata[47:32]} : {48'h0, req_port_i.data_rdata[47:32]};
            3'b101:  rdata_h_ext = (load_data_q.operator == LH) ? {{48{req_port_i.data_rdata[55]}}, req_port_i.data_rdata[55:40]} : {48'h0, req_port_i.data_rdata[55:40]};
            3'b110:  rdata_h_ext = (load_data_q.operator == LH) ? {{48{req_port_i.data_rdata[63]}}, req_port_i.data_rdata[63:48]} : {48'h0, req_port_i.data_rdata[63:48]};
        endcase
    end

    // sign extend byte
    always_comb begin : sign_extend_byte
        case (load_data_q.address_offset)
            default: rdata_b_ext = (load_data_q.operator == LB) ? {{56{req_port_i.data_rdata[7]}},  req_port_i.data_rdata[7:0]}   : {56'h0, req_port_i.data_rdata[7:0]};
            3'b001:  rdata_b_ext = (load_data_q.operator == LB) ? {{56{req_port_i.data_rdata[15]}}, req_port_i.data_rdata[15:8]}  : {56'h0, req_port_i.data_rdata[15:8]};
            3'b010:  rdata_b_ext = (load_data_q.operator == LB) ? {{56{req_port_i.data_rdata[23]}}, req_port_i.data_rdata[23:16]} : {56'h0, req_port_i.data_rdata[23:16]};
            3'b011:  rdata_b_ext = (load_data_q.operator == LB) ? {{56{req_port_i.data_rdata[31]}}, req_port_i.data_rdata[31:24]} : {56'h0, req_port_i.data_rdata[31:24]};
            3'b100:  rdata_b_ext = (load_data_q.operator == LB) ? {{56{req_port_i.data_rdata[39]}}, req_port_i.data_rdata[39:32]} : {56'h0, req_port_i.data_rdata[39:32]};
            3'b101:  rdata_b_ext = (load_data_q.operator == LB) ? {{56{req_port_i.data_rdata[47]}}, req_port_i.data_rdata[47:40]} : {56'h0, req_port_i.data_rdata[47:40]};
            3'b110:  rdata_b_ext = (load_data_q.operator == LB) ? {{56{req_port_i.data_rdata[55]}}, req_port_i.data_rdata[55:48]} : {56'h0, req_port_i.data_rdata[55:48]};
            3'b111:  rdata_b_ext = (load_data_q.operator == LB) ? {{56{req_port_i.data_rdata[63]}}, req_port_i.data_rdata[63:56]} : {56'h0, req_port_i.data_rdata[63:56]};
        endcase
    end

    // Result Mux
    always_comb begin
        case (load_data_q.operator)
            LW, LWU:       result_o = rdata_w_ext;
            LH, LHU:       result_o = rdata_h_ext;
            LB, LBU:       result_o = rdata_b_ext;
            default:       result_o = rdata_d_ext;
        endcase
    end

endmodule
