// Copyright (c) 2020 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Florian Zaruba <zarubaf@iis.ee.ethz.ch>
/// Macros to define register bus request/response structs.

`ifndef REGISTER_INTERFACE_TYPEDEF_SVH_
`define REGISTER_INTERFACE_TYPEDEF_SVH_

`define REG_BUS_TYPEDEF_REQ(req_t, addr_t, data_t, strb_t) \
    typedef struct packed { \
        addr_t addr; \
        logic  write; \
        data_t wdata; \
        strb_t wstrb; \
        logic  valid; \
    } req_t;

`define REG_BUS_TYPEDEF_RSP(rsp_t, data_t) \
    typedef struct packed { \
        data_t rdata; \
        logic  error; \
        logic  ready; \
    } rsp_t;

`define REG_BUS_TYPEDEF_ALL(name, addr_t, data_t, strb_t) \
    `REG_BUS_TYPEDEF_REQ(name``_req_t, addr_t, data_t, strb_t) \
    `REG_BUS_TYPEDEF_RSP(name``_rsp_t, data_t)

`endif
