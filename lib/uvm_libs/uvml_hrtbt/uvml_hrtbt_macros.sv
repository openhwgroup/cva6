// 
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// 
// Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// 


`ifndef __UVML_HRTBT_MACROS_SV__
`define __UVML_HRTBT_MACROS_SV__


`define uvml_hrtbt(ID) \
   uvml_default_hrtbt.heartbeat(this, ID); \

`define uvml_hrtbt_nowner(ID) \
   uvml_default_hrtbt.heartbeat(null, ID); \

`define uvml_hrtbt_set_cfg(PARAM, VALUE) \
   uvml_default_hrtbt.PARAM = VALUE; \
   `uvm_info("HRTBT", {"Default heartbeat field '", PARAM, "' set to '", VALUE, "'"}, UVM_NONE) \

`define uvml_hrtbt_reset \
   uvml_default_hrtbt.reset(); \


`endif // __UVML_HRTBT_MACROS_SV__
