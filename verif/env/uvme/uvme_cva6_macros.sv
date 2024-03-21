// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2021 Thales DIS Design Services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


`ifndef __UVME_CVA6_MACROS_SV__
`define __UVME_CVA6_MACROS_SV__


`define per_instance_fcov `ifndef DSIM option.per_instance = 1; `endif

`ifdef UNSUPPORTED_WITH //TODO - Remove ifdef when the issue in VCS simulator is fixed
  `define WITH iff
`else
   `define WITH with
`endif

`endif // __UVME_CVA6_MACROS_SV__
