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


`ifndef __UVML_LOGS_CONSTANTS_SV__
`define __UVML_LOGS_CONSTANTS_SV__


`ifdef _VCP
parameter uvml_logs_default_sim_dir_cli_arg  = "SIM_DIR_RESULTS";
parameter uvml_logs_default_trn_log_dir_name =         "trn_log";
parameter uvml_logs_default_trn_fextension   =             "log";
`else
const string  uvml_logs_default_sim_dir_cli_arg  = "SIM_DIR_RESULTS";
const string  uvml_logs_default_trn_log_dir_name =         "trn_log";
const string  uvml_logs_default_trn_fextension   =             "log";
`endif //end VCP


`endif // __UVML_LOGS_CONSTANTS_SV__
