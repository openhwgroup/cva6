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

`ifndef REGISTER_INTERFACE_ASSIGN_SVH_
`define REGISTER_INTERFACE_ASSIGN_SVH_

`define REG_BUS_ASSIGN_TO_REQ(lhs, rhs) \
  assign lhs = '{                       \
    addr: rhs.addr,                     \
    write: rhs.write,                   \
    wdata: rhs.wdata,                   \
    wstrb: rhs.wstrb,                   \
    valid: rhs.valid                    \
  };

`define REG_BUS_ASSIGN_FROM_REQ(lhs, rhs) \
  assign lhs.addr = rhs.addr;             \
  assign lhs.write = rhs.write;           \
  assign lhs.wdata = rhs.wdata;           \
  assign lhs.wstrb = rhs.wstrb;           \
  assign lhs.valid = rhs.valid;           \

`define REG_BUS_ASSIGN_TO_RSP(lhs, rhs) \
  assign lhs = '{                       \
    rdata: rhs.rdata,                   \
    error: rhs.error,                   \
    ready: rhs.ready                    \
  };

`define REG_BUS_ASSIGN_FROM_RSP(lhs, rhs) \
  assign lhs.rdata = rhs.rdata;           \
  assign lhs.error = rhs.error;           \
  assign lhs.ready = rhs.ready;

`endif