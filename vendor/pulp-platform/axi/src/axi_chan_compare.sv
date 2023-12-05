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
// Authors:
// - Thomas Benz <tbenz@iis.ee.ethz.ch>
//  - Paul Scheffler <paulsc@iis.ee.ethz.ch>
// - Tim Fischer <fischeti@iis.ee.ethz.ch>

/// Non-synthesizable module comparing two AXI channels of the same type
module axi_chan_compare #(
    /// Ignore ID field if it was remapped
    parameter bit  IgnoreId  = 1'b0,
    /// Allow reordered responses of different IDs,
    /// not compatible with `IgnoreId`
    parameter bit  AllowReordering = 1'b0,
    /// AXI ID Width
    parameter int unsigned IdWidth = 1,
    parameter type aw_chan_t = logic,
    parameter type w_chan_t  = logic,
    parameter type b_chan_t  = logic,
    parameter type ar_chan_t = logic,
    parameter type r_chan_t  = logic,
    parameter type req_t     = logic,
    parameter type resp_t    = logic
)(
    input logic  clk_a_i,
    input logic  clk_b_i,
    input req_t  axi_a_req,
    input resp_t axi_a_res,
    input req_t  axi_b_req,
    input resp_t axi_b_res
);

    function automatic void print_aw (
        input aw_chan_t aw_expected,
        input aw_chan_t aw_received
    );
        // verilog_lint: waive-start line-length
        $display("AW      | expected                                                         | received                                                         ");
        $display("--------|------------------------------------------------------------------|-----------------------------------------------------------------");
        $display("id:     | %64d | %64d", aw_expected.id, aw_received.id);
        $display("addr:   | %64x | %64x", aw_expected.addr, aw_received.addr);
        $display("len:    | %64d | %64d", aw_expected.len, aw_received.len);
        $display("size:   | %64d | %64d", aw_expected.size, aw_received.size);
        $display("burst:  | %64d | %64d", aw_expected.burst, aw_received.burst);
        $display("lock:   | %64d | %64d", aw_expected.lock, aw_received.lock);
        $display("cache:  | %64d | %64d", aw_expected.cache, aw_received.cache);
        $display("prot:   | %64d | %64d", aw_expected.prot, aw_received.prot);
        $display("qos:    | %64d | %64d", aw_expected.qos, aw_received.qos);
        $display("region: | %64d | %64d", aw_expected.region, aw_received.region);
        $display("user:   | %64d | %64d", aw_expected.user, aw_received.user);
        $display("atop:   | %64d | %64d", aw_expected.atop, aw_received.atop);
        $display("--------|------------------------------------------------------------------|-----------------------------------------------------------------");
        // verilog_lint: waive-stop line-length
    endfunction

    function automatic void print_ar (
        input ar_chan_t ar_expected,
        input ar_chan_t ar_received
    );
        // verilog_lint: waive-start line-length
        $display("AR      | expected                                                         | received                                                         ");
        $display("--------|------------------------------------------------------------------|-----------------------------------------------------------------");
        $display("id:     | %64d | %64d", ar_expected.id, ar_received.id);
        $display("addr:   | %64x | %64x", ar_expected.addr, ar_received.addr);
        $display("len:    | %64d | %64d", ar_expected.len, ar_received.len);
        $display("size:   | %64d | %64d", ar_expected.size, ar_received.size);
        $display("burst:  | %64d | %64d", ar_expected.burst, ar_received.burst);
        $display("lock:   | %64d | %64d", ar_expected.lock, ar_received.lock);
        $display("cache:  | %64d | %64d", ar_expected.cache, ar_received.cache);
        $display("prot:   | %64d | %64d", ar_expected.prot, ar_received.prot);
        $display("qos:    | %64d | %64d", ar_expected.qos, ar_received.qos);
        $display("region: | %64d | %64d", ar_expected.region, ar_received.region);
        $display("user:   | %64d | %64d", ar_expected.user, ar_received.user);
        $display("--------|------------------------------------------------------------------|-----------------------------------------------------------------");
        // verilog_lint: waive-stop line-length
    endfunction

    function automatic void print_w (
        input w_chan_t w_expected,
        input w_chan_t w_received
    );
        // verilog_lint: waive-start line-length
        $display("W       | expected                                                         | received                                                         ");
        $display("--------|------------------------------------------------------------------|-----------------------------------------------------------------");
        $display("data:   | %64x | %64x", w_expected.data, w_received.data);
        $display("strb:   | %64d | %64d", w_expected.strb, w_received.strb);
        $display("last:   | %64d | %64d", w_expected.last, w_received.last);
        $display("user:   | %64d | %64d", w_expected.user, w_received.user);
        $display("--------|------------------------------------------------------------------|-----------------------------------------------------------------");
        // verilog_lint: waive-stop line-length
    endfunction

    function automatic void print_b (
        input b_chan_t b_expected,
        input b_chan_t b_received
    );
        // verilog_lint: waive-start line-length
        $display("B       | expected                                                         | received                                                         ");
        $display("--------|------------------------------------------------------------------|-----------------------------------------------------------------");
        $display("id:     | %64d | %64d", b_expected.id, b_received.id);
        $display("resp:   | %64d | %64d", b_expected.resp, b_received.resp);
        $display("user:   | %64d | %64d", b_expected.user, b_received.user);
        $display("--------|------------------------------------------------------------------|-----------------------------------------------------------------");
        // verilog_lint: waive-stop line-length
    endfunction

    function automatic void print_r (
        input r_chan_t r_expected,
        input r_chan_t r_received
    );
        // verilog_lint: waive-start line-length
        $display("R       | expected                                                         | received                                                         ");
        $display("--------|------------------------------------------------------------------|-----------------------------------------------------------------");
        $display("id:     | %64d | %64d", r_expected.id, r_received.id);
        $display("data:   | %64x | %64x", r_expected.data, r_received.data);
        $display("resp:   | %64d | %64d", r_expected.resp, r_received.resp);
        $display("last:   | %64d | %64d", r_expected.last, r_received.last);
        $display("user:   | %64d | %64d", r_expected.user, r_received.user);
        $display("--------|------------------------------------------------------------------|-----------------------------------------------------------------");
        // verilog_lint: waive-stop line-length
    endfunction

    localparam NumIds = (AllowReordering)? 2**IdWidth : 1;

    // queues
    aw_chan_t aw_queue [NumIds-1:0][$];
    w_chan_t  w_queue              [$];
    b_chan_t  b_queue  [NumIds-1:0][$];
    ar_chan_t ar_queue [NumIds-1:0][$];
    r_chan_t  r_queue  [NumIds-1:0][$];

    // requests generated at axi A: enqueue elements
    always_ff @(posedge clk_a_i) begin : proc_enqueue_a
        // aw
        if (axi_a_req.aw_valid & axi_a_res.aw_ready)
            if (AllowReordering) aw_queue[axi_a_req.aw.id].push_back(axi_a_req.aw);
            else aw_queue[0].push_back(axi_a_req.aw);
        // w
        if (axi_a_req.w_valid & axi_a_res.w_ready)
            w_queue.push_back(axi_a_req.w);
        // ar
        if (axi_a_req.ar_valid & axi_a_res.ar_ready)
            if (AllowReordering) ar_queue[axi_a_req.ar.id].push_back(axi_a_req.ar);
            else ar_queue[0].push_back(axi_a_req.ar);
    end

    // responses generated at axi B: enqueue elements
    always_ff @(posedge clk_b_i) begin : proc_enqueue_b
        // b
        if (axi_b_res.b_valid & axi_b_req.b_ready)
            if (AllowReordering) b_queue[axi_b_res.b.id].push_back(axi_b_res.b);
            else b_queue[0].push_back(axi_b_res.b);
        // r
        if (axi_b_res.r_valid & axi_b_req.r_ready)
            if (AllowReordering) r_queue[axi_b_res.r.id].push_back(axi_b_res.r);
            else r_queue[0].push_back(axi_b_res.r);
    end

    // requests arriving at axi B from A: dequeue elements and check
    always_ff @(posedge clk_b_i) begin : proc_dequeue_and_check_b
        // aw
        if (axi_b_req.aw_valid & axi_b_res.aw_ready) begin
            automatic aw_chan_t aw_exp, aw_recv;
            if (AllowReordering) begin
                if (aw_queue[axi_b_req.aw.id].size() == 0) $error("AW queue is empty!");
                aw_exp = aw_queue[axi_b_req.aw.id].pop_front(); // verilog_lint: waive always-ff-non-blocking
            end else begin
                if (aw_queue[0].size() == 0) $error("AW queue is empty!");
                aw_exp = aw_queue[0].pop_front(); // verilog_lint: waive always-ff-non-blocking
            end
            aw_recv = axi_b_req.aw;
            if (IgnoreId) begin
                aw_exp.id = 'X;
                aw_recv.id = 'X;
            end
            if (aw_exp !== aw_recv) begin
                $error("AW mismatch!");
                print_aw(aw_exp, aw_recv);
            end
        end
        // w
        if (axi_b_req.w_valid & axi_b_res.w_ready) begin
            automatic w_chan_t w_exp, w_recv;
            if (w_queue.size() == 0) $error("W queue is empty!");
            w_exp = w_queue.pop_front(); // verilog_lint: waive always-ff-non-blocking
            w_recv = axi_b_req.w;
            if (w_exp !== w_recv) begin
                $error("W mismatch!");
                print_w(w_exp, w_recv);
            end
        end
        // ar
        if (axi_b_req.ar_valid & axi_b_res.ar_ready) begin
            automatic ar_chan_t ar_exp, ar_recv;
            if (AllowReordering) begin
                if (ar_queue[axi_b_req.ar.id].size() == 0) $error("AR queue is empty!");
                ar_exp = ar_queue[axi_b_req.ar.id].pop_front(); // verilog_lint: waive always-ff-non-blocking
            end else begin
                if (ar_queue[0].size() == 0) $error("AR queue is empty!");
                ar_exp = ar_queue[0].pop_front(); // verilog_lint: waive always-ff-non-blocking
            end
            ar_recv = axi_b_req.ar;
            if (IgnoreId) begin
                ar_exp.id = 'X;
                ar_recv.id = 'X;
            end
            if (ar_exp !== ar_recv) begin
                $error("AR mismatch!");
                print_ar(ar_exp, ar_recv);
            end
        end
    end

    // responses arriving at axi A from B: dequeue elements and check
    always_ff @(posedge clk_a_i) begin : proc_dequeue_and_check_a
        // b
        if (axi_a_res.b_valid & axi_a_req.b_ready) begin
            automatic b_chan_t b_exp, b_recv;
            if (AllowReordering) begin
                if (b_queue[axi_a_res.b.id].size() == 0) $error("B queue is empty!");
                b_exp = b_queue[axi_a_res.b.id].pop_front(); // verilog_lint: waive always-ff-non-blocking
            end else begin
                if (b_queue[0].size() == 0) $error("B queue is empty!");
                b_exp = b_queue[0].pop_front(); // verilog_lint: waive always-ff-non-blocking
            end
            b_recv = axi_a_res.b;
            if (IgnoreId) begin
                b_exp.id = 'X;
                b_recv.id = 'X;
            end
            if (b_exp !== b_recv) begin
                $error("B mismatch!");
                print_b(b_exp, b_recv);
            end
        end
        // r
        if (axi_a_res.r_valid & axi_a_req.r_ready) begin
            automatic r_chan_t r_exp, r_recv;
            if (AllowReordering) begin
                if (r_queue[axi_a_res.r.id].size() == 0) $error("R queue is empty!");
                r_exp = r_queue[axi_a_res.r.id].pop_front(); // verilog_lint: waive always-ff-non-blocking
            end else begin
                if (r_queue[0].size() == 0) $error("R queue is empty!");
                r_exp = r_queue[0].pop_front(); // verilog_lint: waive always-ff-non-blocking
            end
            r_recv = axi_a_res.r;
            if (IgnoreId) begin
                r_exp.id = 'X;
                r_recv.id = 'X;
            end
            if (r_exp !== r_recv) begin
                $error("R mismatch!");
                print_r(r_exp, r_recv);
            end
        end
    end

endmodule : axi_chan_compare
