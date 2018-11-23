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

module axi_master_connect_rev (
    output ariane_axi::req_t    axi_req_o,
    input  ariane_axi::resp_t   axi_resp_i,
    AXI_BUS.in master
);

    assign  axi_req_o.aw.atop    = '0; // not supported at the moment
    assign  axi_req_o.aw.id      = master.aw_id;
    assign  axi_req_o.aw.addr    = master.aw_addr;
    assign  axi_req_o.aw.len     = master.aw_len;
    assign  axi_req_o.aw.size    = master.aw_size;
    assign  axi_req_o.aw.burst   = master.aw_burst;
    assign  axi_req_o.aw.lock    = master.aw_lock;
    assign  axi_req_o.aw.cache   = master.aw_cache;
    assign  axi_req_o.aw.prot    = master.aw_prot;
    assign  axi_req_o.aw.qos     = master.aw_qos;
    assign  axi_req_o.aw.region  = master.aw_region;
    // assign                     = master.aw_user;
    assign  axi_req_o.aw_valid   = master.aw_valid;
    assign  master.aw_ready       = axi_resp_i.aw_ready;

    assign  axi_req_o.w.data     = master.w_data;
    assign  axi_req_o.w.strb     = master.w_strb;
    assign  axi_req_o.w.last     = master.w_last;
    // assign                     = master.w_user;
    assign  axi_req_o.w_valid    = master.w_valid;
    assign  master.w_ready        = axi_resp_i.w_ready;

    assign  master.b_id           = axi_resp_i.b.id;
    assign  master.b_resp         = axi_resp_i.b.resp;
    assign  master.b_valid        = axi_resp_i.b_valid;
    assign  axi_req_o.b_ready    = master.b_ready;

    assign  axi_req_o.ar.id      = master.ar_id;
    assign  axi_req_o.ar.addr    = master.ar_addr;
    assign  axi_req_o.ar.len     = master.ar_len;
    assign  axi_req_o.ar.size    = master.ar_size;
    assign  axi_req_o.ar.burst   = master.ar_burst;
    assign  axi_req_o.ar.lock    = master.ar_lock;
    assign  axi_req_o.ar.cache   = master.ar_cache;
    assign  axi_req_o.ar.prot    = master.ar_prot;
    assign  axi_req_o.ar.qos     = master.ar_qos;
    assign  axi_req_o.ar.region  = master.ar_region;
    // assign                     = master.ar_user;
    assign  axi_req_o.ar_valid   = master.ar_valid;
    assign  master.ar_ready       = axi_resp_i.ar_ready;

    assign  master.r_id           = axi_resp_i.r.id;
    assign  master.r_data         = axi_resp_i.r.data;
    assign  master.r_resp         = axi_resp_i.r.resp;
    assign  master.r_last         = axi_resp_i.r.last;
    assign  master.r_valid        = axi_resp_i.r_valid;
    assign  axi_req_o.r_ready    = master.r_ready;

endmodule
