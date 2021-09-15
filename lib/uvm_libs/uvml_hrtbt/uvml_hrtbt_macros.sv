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


`ifndef __UVML_HRTBT_MACROS_SV__
`define __UVML_HRTBT_MACROS_SV__


`define uvml_hrtbt_stringify(x) `"x`"
`define uvml_hrtbt(ID) \
   uvml_default_hrtbt.heartbeat(this, ID); \

`define uvml_hrtbt_nowner(ID) \
   uvml_default_hrtbt.heartbeat(null, ID); \

`define uvml_hrtbt_set_cfg(PARAM, VALUE) \
   uvml_default_hrtbt.PARAM = VALUE; \
   `uvm_info("HRTBT", {"Default heartbeat field '", `uvml_hrtbt_stringify(PARAM), "' set to '", $sformatf("%0d", VALUE), "'"}, UVM_NONE) \

`define uvml_hrtbt_reset \
   uvml_default_hrtbt.reset(); \


`endif // __UVML_HRTBT_MACROS_SV__
