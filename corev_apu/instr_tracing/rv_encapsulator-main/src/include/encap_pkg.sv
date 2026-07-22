// Copyright 2025 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// SPDX-License-Identifier: SHL-0.51

// Author:  Umberto Laghi
// Contact: umberto.laghi2@unibo.it
// Github:  @ubolakes

/*
all the type associated params are commented because the type is not required for trace encoders 
supporting only instruction tracing
*/

package encap_pkg;

    localparam H_LEN = 8; // header length
    //localparam SRCID_LEN = 7; // not used because only one source in system
    //localparam TYPE_LEN = 8;
    localparam PAYLOAD_LEN = 248 /*- TYPE_LEN - (SRCID_LEN % 8)*/; // trace_payload_len
    localparam T_LEN = 64; // timestamp length: mcycle length is always 64
    localparam FLOW_LEN = 2;
    localparam P_LEN = 5;
    localparam MAX_LEN = 264; // max length for payload to slice

    typedef struct packed {
        logic                   extend;
        logic [FLOW_LEN-1:0]    flow;
        logic [P_LEN-1:0]       length;
    } header_s;

    typedef struct packed {
        //logic [TYPE_LEN-1:0]    type; // omitted because only instruction trace available
        logic [PAYLOAD_LEN-1:0] trace_payload;
    } payload_s;

    typedef struct packed {
        header_s            header;
        //logic [SRCID_LEN-1:0] srcid;
        logic [T_LEN-1:0]   timestamp;
        payload_s           payload;
    } encap_fifo_entry_s;

endpackage