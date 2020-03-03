/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   ariane_axi_pkg.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   17.8.2018
 *
 * Description: Contains Ariane's AXI ports, does not contain user ports
 */

`include "axi/typedef.svh"

package ariane_axi;

    // used in axi_adapter.sv
    typedef enum logic { SINGLE_REQ, CACHE_LINE_REQ } ad_req_t;

    localparam UserWidth   = 1;
    localparam AddrWidth   = 64;
    localparam DataWidth   = 64;
    localparam DataWidth32 = 32;
    localparam StrbWidth   = DataWidth / 8;
    localparam StrbWidth32 = DataWidth32 / 8;

    typedef logic [ariane_soc::IdWidth-1:0]      id_t;
    typedef logic [ariane_soc::IdWidthSlave-1:0] id_slv_t;
    typedef logic [AddrWidth-1:0]   addr_t;
    typedef logic [DataWidth-1:0]   data_t;
    typedef logic [DataWidth32-1:0] data_32_t;
    typedef logic [StrbWidth-1:0]   strb_t;
    typedef logic [StrbWidth32-1:0] strb_32_t;
    typedef logic [UserWidth-1:0]   user_t;

    // Typedefs for data 64 bit AXI4-ATOP
    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_slv_t, addr_t, id_slv_t, user_t)
    `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
    `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
    `AXI_TYPEDEF_B_CHAN_T(b_chan_slv_t, id_slv_t, user_t)
    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_slv_t, addr_t, id_slv_t, user_t)
    `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
    `AXI_TYPEDEF_R_CHAN_T(r_chan_slv_t, data_t, id_slv_t, user_t)

    `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
    `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

    `AXI_TYPEDEF_REQ_T(req_slv_t, aw_chan_slv_t, w_chan_t, ar_chan_slv_t)
    `AXI_TYPEDEF_RESP_T(resp_slv_t, b_chan_slv_t, r_chan_slv_t)

    // Typedef for data 32 bit AXI4-ATOP
    `AXI_TYPEDEF_W_CHAN_T(w_chan_32_t, data_32_t, strb_32_t, user_t )
    `AXI_TYPEDEF_R_CHAN_T(r_chan_32_t, data_32_t, id_slv_t, user_t )

    `AXI_TYPEDEF_REQ_T(req_32_t, aw_chan_slv_t, w_chan_32_t, ar_chan_slv_t)
    `AXI_TYPEDEF_RESP_T(resp_32_t, b_chan_slv_t, r_chan_32_t)

    // Typedef for AXI4-Lite 32 bit data
    `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_lite_t, addr_t)
    `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_lite_t, data_32_t, strb_32_t)
    `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_lite_t)
    `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_lite_t, addr_t)
    `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_lite_t, data_32_t)

    `AXI_LITE_TYPEDEF_REQ_T(req_lite_t, aw_chan_lite_t, w_chan_lite_t, ar_chan_lite_t)
    `AXI_LITE_TYPEDEF_RESP_T(resp_lite_t, b_chan_lite_t, r_chan_lite_t)
endpackage
