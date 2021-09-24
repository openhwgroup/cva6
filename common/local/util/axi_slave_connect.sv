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
// Description: Connects SV AXI interface to structs used by Ariane
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

module axi_slave_connect (
    output ariane_axi::req_t    axi_req_o,
    input  ariane_axi::resp_t   axi_resp_i,
    AXI_BUS.Slave slave
);

    assign  axi_req_o.aw.id      = slave.aw_id;
    assign  axi_req_o.aw.addr    = slave.aw_addr;
    assign  axi_req_o.aw.len     = slave.aw_len;
    assign  axi_req_o.aw.size    = slave.aw_size;
    assign  axi_req_o.aw.burst   = slave.aw_burst;
    assign  axi_req_o.aw.lock    = slave.aw_lock;
    assign  axi_req_o.aw.cache   = slave.aw_cache;
    assign  axi_req_o.aw.prot    = slave.aw_prot;
    assign  axi_req_o.aw.qos     = slave.aw_qos;
    assign  axi_req_o.aw.atop    = slave.aw_atop;
    assign  axi_req_o.aw.region  = slave.aw_region;
    // assign                     = slave.aw_user;
    assign  axi_req_o.aw_valid   = slave.aw_valid;
    assign  slave.aw_ready       = axi_resp_i.aw_ready;

    assign  axi_req_o.w.data     = slave.w_data;
    assign  axi_req_o.w.strb     = slave.w_strb;
    assign  axi_req_o.w.last     = slave.w_last;
    // assign                     = slave.w_user;
    assign  axi_req_o.w_valid    = slave.w_valid;
    assign  slave.w_ready        = axi_resp_i.w_ready;

    assign  slave.b_id           = axi_resp_i.b.id;
    assign  slave.b_resp         = axi_resp_i.b.resp;
    assign  slave.b_valid        = axi_resp_i.b_valid;
    assign  slave.b_user         = 1'b0;
    assign  axi_req_o.b_ready    = slave.b_ready;

    assign  axi_req_o.ar.id      = slave.ar_id;
    assign  axi_req_o.ar.addr    = slave.ar_addr;
    assign  axi_req_o.ar.len     = slave.ar_len;
    assign  axi_req_o.ar.size    = slave.ar_size;
    assign  axi_req_o.ar.burst   = slave.ar_burst;
    assign  axi_req_o.ar.lock    = slave.ar_lock;
    assign  axi_req_o.ar.cache   = slave.ar_cache;
    assign  axi_req_o.ar.prot    = slave.ar_prot;
    assign  axi_req_o.ar.qos     = slave.ar_qos;
    assign  axi_req_o.ar.region  = slave.ar_region;
    // assign                     = slave.ar_user;
    assign  axi_req_o.ar_valid   = slave.ar_valid;
    assign  slave.ar_ready       = axi_resp_i.ar_ready;

    assign  slave.r_id           = axi_resp_i.r.id;
    assign  slave.r_data         = axi_resp_i.r.data;
    assign  slave.r_resp         = axi_resp_i.r.resp;
    assign  slave.r_last         = axi_resp_i.r.last;
    assign  slave.r_valid        = axi_resp_i.r_valid;
    assign  slave.r_user         = 1'b0;
    assign  axi_req_o.r_ready    = slave.r_ready;

endmodule
