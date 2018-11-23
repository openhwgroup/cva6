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

module axi_master_connect (
    input  ariane_axi::req_t    axi_req_i,
    output ariane_axi::resp_t   axi_resp_o,
    AXI_BUS.out master
);

    assign master.aw_id         = axi_req_i.aw.id;
    assign master.aw_addr       = axi_req_i.aw.addr;
    assign master.aw_len        = axi_req_i.aw.len;
    assign master.aw_size       = axi_req_i.aw.size;
    assign master.aw_burst      = axi_req_i.aw.burst;
    assign master.aw_lock       = axi_req_i.aw.lock;
    assign master.aw_cache      = axi_req_i.aw.cache;
    assign master.aw_prot       = axi_req_i.aw.prot;
    assign master.aw_qos        = axi_req_i.aw.qos;
    assign master.aw_region     = axi_req_i.aw.region;
    assign master.aw_user       = '0;
    assign master.aw_valid      = axi_req_i.aw_valid;
    assign axi_resp_o.aw_ready  = master.aw_ready;

    assign master.w_data        = axi_req_i.w.data;
    assign master.w_strb        = axi_req_i.w.strb;
    assign master.w_last        = axi_req_i.w.last;
    assign master.w_user        = '0;
    assign master.w_valid       = axi_req_i.w_valid;
    assign axi_resp_o.w_ready   = master.w_ready;

    assign axi_resp_o.b.id      = master.b_id;
    assign axi_resp_o.b.resp    = master.b_resp;
    assign axi_resp_o.b_valid   = master.b_valid;
    assign master.b_ready       = axi_req_i.b_ready;

    assign master.ar_id         = axi_req_i.ar.id;
    assign master.ar_addr       = axi_req_i.ar.addr;
    assign master.ar_len        = axi_req_i.ar.len;
    assign master.ar_size       = axi_req_i.ar.size;
    assign master.ar_burst      = axi_req_i.ar.burst;
    assign master.ar_lock       = axi_req_i.ar.lock;
    assign master.ar_cache      = axi_req_i.ar.cache;
    assign master.ar_prot       = axi_req_i.ar.prot;
    assign master.ar_qos        = axi_req_i.ar.qos;
    assign master.ar_region     = axi_req_i.ar.region;
    assign master.ar_user       = '0;
    assign master.ar_valid      = axi_req_i.ar_valid;
    assign axi_resp_o.ar_ready  = master.ar_ready;

    assign axi_resp_o.r.id      = master.r_id;
    assign axi_resp_o.r.data    = master.r_data;
    assign axi_resp_o.r.resp    = master.r_resp;
    assign axi_resp_o.r.last    = master.r_last;
    assign axi_resp_o.r_valid   = master.r_valid;
    assign master.r_ready       = axi_req_i.r_ready;

endmodule
