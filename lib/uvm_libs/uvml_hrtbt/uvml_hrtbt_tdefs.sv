// Copyright 2020 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// 
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.


`ifndef __UVML_HRTBT_TDEFS_SV__
`define __UVML_HRTBT_TDEFS_SV__


/**
 * Describes a component issuing a heartbeat to an instance of the heartbeat monitor (uvml_hrtbt_mon_c).
 */
typedef struct {
   uvm_component  owner;
   int            id;
   realtime       timestamp;
} uvml_hrtbt_entry_struct;


`endif // __UVML_HRTBT_TDEFS_SV__
