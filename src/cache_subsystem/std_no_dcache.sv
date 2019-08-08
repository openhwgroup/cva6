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
// Description: Bypass version of data cache

module std_nbdcache #(
    parameter logic [63:0] CACHE_START_ADDR = 64'h8000_0000
) (
    input  logic                            clk_i,       // Clock
    input  logic                            rst_ni,      // Asynchronous reset active low
    // Cache management
    input  logic                            enable_i,    // from CSR
    input  logic                            flush_i,     // high until acknowledged
    output logic                            flush_ack_o, // send a single cycle acknowledge signal when the cache is flushed
    output logic                            miss_o,      // we missed on a LD/ST
    // AMOs
    input  ariane_pkg::amo_req_t            amo_req_i,
    output ariane_pkg::amo_resp_t           amo_resp_o,
    // Request ports
    input  ariane_pkg::dcache_req_i_t [2:0] req_ports_i,  // request ports
    output ariane_pkg::dcache_req_o_t [2:0] req_ports_o,  // request ports
    // Cache AXI refill port
    output ariane_axi::req_t               axi_data_o,
    input  ariane_axi::resp_t              axi_data_i,
    output ariane_axi::req_t               axi_bypass_o,
    input  ariane_axi::resp_t              axi_bypass_i
);

    localparam PTW = 0;
    localparam LOAD = 1;
    localparam STORE = 2;

    // Registers
    enum logic [3:0] {
        Idle,
        SampleTagPTW,
        SampleTagLoad,
        ReadPTW,
        ReadLoad,
        WaitReadPTW,
        WaitReadLoad,
        Write,
        SendWrite,
        WaitB,
        AMORead,
        WaitAMORead,
        AMOSendAW,
        AMOSendW,
        AMOWaitB
    } state_d, state_q;

    typedef struct packed {
        logic [63:0] addr;
        logic [7:0]  be;
        logic [1:0]  size;
    } cache_req_t;

    struct packed {
        logic [63:3] address;
        logic        valid;
    } reservation_d, reservation_q;

    cache_req_t req_q, req_d;
    logic [63:0] amo_load_d, amo_load_q;
    // tie-off bypass bus
    assign axi_bypass_o.aw_valid = 1'b0;
    assign axi_bypass_o.w_valid = 1'b0;
    assign axi_bypass_o.ar_valid = 1'b0;
    assign axi_bypass_o.b_ready = 1'b1;
    assign axi_bypass_o.r_ready = 1'b1;

    // AMOs
    ariane_pkg::amo_t amo_op;
    logic [63:0] amo_operand_a, amo_operand_b, amo_result_o;

    logic [63:0] load_data;
    // re-align load data
    assign load_data = data_align(amo_req_i.operand_a[2:0], amo_load_q);

    always_comb begin
        req_d = req_q;
        amo_load_d = amo_load_q;

        for (int i = 0; i < 3; i++) begin
            req_ports_o[i].data_gnt = 1'b0;
            req_ports_o[i].data_rvalid = 1'b0;
            req_ports_o[i].data_rdata = '0;
        end

        axi_data_o.aw_valid = 1'b0;
        axi_data_o.aw.id = '0;
        axi_data_o.aw.addr = '0;
        axi_data_o.aw.size = '0;
        axi_data_o.aw.lock = '0;
        axi_data_o.aw.cache = '0;
        axi_data_o.aw.prot = '0;
        axi_data_o.aw.qos = '0;
        axi_data_o.aw.region = '0;

        axi_data_o.w_valid = 1'b0;
        axi_data_o.w.data = '0;
        axi_data_o.w.strb = '0;
        axi_data_o.w.last = 1'b1;

        axi_data_o.ar.id = '0;
        axi_data_o.ar.addr = req_q.addr;
        axi_data_o.ar.size = req_q.size;
        axi_data_o.ar.lock = '0;
        axi_data_o.ar.cache = '0;
        axi_data_o.ar.prot = '0;
        axi_data_o.ar.qos = '0;
        axi_data_o.ar.region = '0;

        // AMOs
        amo_resp_o.ack = 1'b0;
        amo_resp_o.result = '0;
        // silence the unit when not used
        amo_op = amo_req_i.amo_op;
        amo_operand_a = '0;
        amo_operand_b = '0;

        reservation_d = reservation_q;
        case (state_q)

            Idle: begin
                // PTW
                if (req_ports_i[PTW].data_req) begin
                    state_d = SampleTagPTW;
                    req_d.addr[ariane_pkg::DCACHE_INDEX_WIDTH-1:0] = req_ports_i[PTW].address_index;
                    req_d.size = req_ports_i[PTW].data_size;
                    req_ports_o[PTW].data_gnt = 1'b1;
                // Load
                end else if (req_ports_i[LOAD].data_req) begin
                    state_d = SampleTagLoad;
                    req_d.addr[ariane_pkg::DCACHE_INDEX_WIDTH-1:0] = req_ports_i[LOAD].address_index;
                    req_d.size = req_ports_i[LOAD].data_size;
                    req_ports_o[LOAD].data_gnt = 1'b1;
                // Store
                end else if (req_ports_i[STORE].data_req) begin
                    state_d = Write;
                // AMO
                end else if (amo_req_i.req) begin
                    state_d = AMORead;

                end
            end

            SampleTagPTW: begin
                req_d.addr[ariane_pkg::DCACHE_TAG_WIDTH+ariane_pkg::DCACHE_INDEX_WIDTH-1:ariane_pkg::DCACHE_INDEX_WIDTH] = req_ports_i[PTW].address_tag;

                if (req_ports_i[PTW].kill_req) begin
                    state_d = Idle;
                    req_ports_o[PTW].data_rvalid = 1'b1;
                end else begin
                    state_d = ReadPTW;
                end

            end

            SampleTagLoad: begin
                req_d.addr[ariane_pkg::DCACHE_TAG_WIDTH+ariane_pkg::DCACHE_INDEX_WIDTH-1:ariane_pkg::DCACHE_INDEX_WIDTH] = req_ports_i[LOAD].address_tag;

                if (req_ports_i[LOAD].kill_req) begin
                    state_d = Idle;
                    req_ports_o[LOAD].data_rvalid = 1'b1;
                end else begin
                    state_d = ReadLoad;
                end
            end

            ReadPTW: begin
                axi_data_o.aw_valid = 1'b1;

                if (axi_data_i.aw_ready) begin
                    state_d = WaitReadPTW;
                end
            end

            ReadLoad: begin
                axi_data_o.aw_valid = 1'b1;

                if (axi_data_i.aw_ready) begin
                    state_d = WaitReadLoad;
                end
            end

            WaitReadPTW: begin
                axi_data_o.r_ready = 1'b1;
                if (axi_data_i.r_valid) begin
                    req_ports_o[PTW].data_rvalid = 1'b1;
                    req_ports_o[PTW].data_rdata = axi_data_i.r.data;
                    state_d = Idle;
                end
            end

            WaitReadLoad: begin
                axi_data_o.r_ready = 1'b1;
                if (axi_data_i.r_valid) begin
                    req_ports_o[LOAD].data_rvalid = 1'b1;
                    req_ports_o[LOAD].data_rdata = axi_data_i.r.data;
                    state_d = Idle;
                end
            end

            Write: begin
                axi_data_o.aw_valid = 1'b1;
                axi_data_o.aw.addr = {req_ports_i[STORE].address_tag, req_ports_i[STORE].address_index};
                axi_data_o.aw.size = {1'b0, req_ports_i[STORE].data_size};

                if (axi_data_i.w_ready) state_d = SendWrite;
            end

            SendWrite: begin
                axi_data_o.w_valid = 1'b1;
                axi_data_o.w.data = req_ports_i[STORE].data_wdata;
                axi_data_o.w.strb = req_ports_i[STORE].data_be;

                if (axi_data_i.w_ready) begin
                    state_d = WaitB;
                    req_ports_o[STORE].data_gnt = 1'b1;
                end
            end

            WaitB: begin
                axi_data_o.b_ready = 1'b1;
                if (axi_data_i.b_valid) begin
                    state_d = Idle;
                    req_ports_o[STORE].data_rvalid = 1'b1;
                end
            end

            AMORead: begin
                axi_data_o.ar.addr = amo_req_i.operand_a;
                axi_data_o.ar.size = amo_req_i.size;
                axi_data_o.ar_valid = 1'b1;
                if (axi_data_i.ar_ready) state_d = WaitAMORead;
            end

            WaitAMORead: begin

                axi_data_o.r_ready = 1'b1;

                if (axi_data_i.r_valid) begin
                    amo_load_d = axi_data_i.r.data;
                    state_d = AMOSendAW;
                end

                // place a reservation on the memory and bail out
                if (amo_req_i.amo_op == ariane_pkg::AMO_LR) begin
                    state_d = Idle;
                    reservation_d.address = amo_req_i.operand_a[63:3];
                    reservation_d.valid = 1'b1;
                    amo_resp_o.ack = 1'b1;
                    // Sign-extend for word operation
                    if (amo_req_i.size == 2'b10) begin
                        amo_resp_o.result = sext32(load_data[31:0]);
                    end else begin
                        amo_resp_o.result = load_data;
                    end

                end

            end

            AMOSendAW: begin
                axi_data_o.aw_valid = 1'b1;
                axi_data_o.aw.addr = amo_req_i.operand_a;
                axi_data_o.aw.size = {1'b0, amo_req_i.size};

                if (axi_data_i.aw_ready) begin
                    state_d = AMOSendW;
                end
            end

            AMOSendW: begin
                // Sign-extend for word operation
                if (amo_req_i.size == 2'b10) begin
                    amo_operand_a = sext32(load_data[31:0]);
                    amo_operand_b = sext32(amo_req_i.operand_b[31:0]);
                end else begin
                    amo_operand_a = load_data;
                    amo_operand_b = amo_req_i.operand_b;
                end

                axi_data_o.w_valid = 1'b1;
                axi_data_o.w.data = data_align(amo_req_i.operand_a[2:0], amo_result_o);
                axi_data_o.w.strb = be_gen(amo_req_i.operand_a[2:0], amo_req_i.size);

                if (axi_data_i.w_ready) begin
                    state_d = AMOWaitB;
                end

            end

            AMOWaitB: begin
                axi_data_o.b_ready = 1'b1;
                if (axi_data_i.b_valid) begin
                    state_d = Idle;
                end
            end
        endcase
    end

    // -----------------
    // AMO ALU
    // -----------------
    amo_alu i_amo_alu (
        .amo_op_i        ( amo_op        ),
        .amo_operand_a_i ( amo_operand_a ),
        .amo_operand_b_i ( amo_operand_b ),
        .amo_result_o    ( amo_result_o  )
    );

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            state_q <= Idle;
            req_q <= '0;
            amo_load_q <= '0;
            reservation_q <= '0;
         end else begin
            state_q <= state_d;
            req_q <= req_d;
            amo_load_q <= amo_load_d;
            reservation_q <= reservation_d;
        end
    end
endmodule
