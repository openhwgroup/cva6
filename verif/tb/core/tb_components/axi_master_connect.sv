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
    input  bit                  dis_mem,
    AXI_BUS.Master master
);

    assign master.aw_id         = dis_mem? '0 : axi_req_i.aw.id;
    assign master.aw_addr       = dis_mem? '0 : axi_req_i.aw.addr;
    assign master.aw_len        = dis_mem? '0 : axi_req_i.aw.len;
    assign master.aw_size       = dis_mem? '0 : axi_req_i.aw.size;
    assign master.aw_burst      = dis_mem? '0 : axi_req_i.aw.burst;
    assign master.aw_lock       = dis_mem? '0 : axi_req_i.aw.lock;
    assign master.aw_cache      = dis_mem? '0 : axi_req_i.aw.cache;
    assign master.aw_prot       = dis_mem? '0 : axi_req_i.aw.prot;
    assign master.aw_qos        = dis_mem? '0 : axi_req_i.aw.qos;
    assign master.aw_atop       = dis_mem? '0 : axi_req_i.aw.atop;
    assign master.aw_region     = dis_mem? '0 : axi_req_i.aw.region;
    assign master.aw_user       = dis_mem? '0 : '0;
    assign master.aw_valid      = dis_mem? '0 : axi_req_i.aw_valid;

    assign master.w_data        = dis_mem? '0 : axi_req_i.w.data;
    assign master.w_strb        = dis_mem? '0 : axi_req_i.w.strb;
    assign master.w_last        = dis_mem? '0 : axi_req_i.w.last;
    assign master.w_user        = dis_mem? '0 : axi_req_i.w.user;
    assign master.w_valid       = dis_mem? '0 : axi_req_i.w_valid;

    assign master.b_ready       = dis_mem? '0 : axi_req_i.b_ready;

    assign master.ar_id         = dis_mem? '0 : axi_req_i.ar.id;
    assign master.ar_addr       = dis_mem? '0 : axi_req_i.ar.addr;
    assign master.ar_len        = dis_mem? '0 : axi_req_i.ar.len;
    assign master.ar_size       = dis_mem? '0 : axi_req_i.ar.size;
    assign master.ar_burst      = dis_mem? '0 : axi_req_i.ar.burst;
    assign master.ar_lock       = dis_mem? '0 : axi_req_i.ar.lock;
    assign master.ar_cache      = dis_mem? '0 : axi_req_i.ar.cache;
    assign master.ar_prot       = dis_mem? '0 : axi_req_i.ar.prot;
    assign master.ar_qos        = dis_mem? '0 : axi_req_i.ar.qos;
    assign master.ar_region     = dis_mem? '0 : axi_req_i.ar.region;
    assign master.ar_user       = dis_mem? '0 : '0;
    assign master.ar_valid      = dis_mem? '0 : axi_req_i.ar_valid;

    assign master.r_ready       = dis_mem? '0 : axi_req_i.r_ready;

endmodule
