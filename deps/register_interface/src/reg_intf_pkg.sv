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
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// A simple register interface.
///
/// This is pretty much as simple as it gets. Transactions consist of only one
/// phase. The master sets the address, write, write data, and write strobe
/// signals and pulls valid high. Once pulled high, valid must remain high and
/// none of the signals may change. The transaction completes when both valid
/// and ready are high. Valid must not depend on ready. The slave presents the
/// read data and error signals. These signals must be constant while valid and
/// ready are both high.
package reg_intf;

    /// 32 bit address, 32 bit data request package
    typedef struct packed {
        logic [31:0] addr;
        logic        write;
        logic [31:0] wdata;
        logic [3:0]  wstrb;
        logic        valid;
    } reg_intf_req_a32_d32;

    /// 32 bit address, 64 bit data request package
    typedef struct packed {
        logic [31:0] addr;
        logic        write;
        logic [63:0] wdata;
        logic [7:0]  wstrb;
        logic        valid;
    } reg_intf_req_a32_d64;

    /// 32 bit Response packages
    typedef struct packed {
        logic [31:0] rdata;
        logic        error;
        logic        ready;
    } reg_intf_resp_d32;

    /// 32 bit Response packages
    typedef struct packed {
        logic [63:0] rdata;
        logic        error;
        logic        ready;
    } reg_intf_resp_d64;

endpackage
