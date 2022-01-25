// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technologies
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


`ifndef __UVMT_CVA6_TDEFS_SV__
`define __UVMT_CVA6_TDEFS_SV__


/**
 * Test Program Type.  See the Verification Strategy for a discussion of this.
 */
typedef enum {
              PREEXISTING_SELFCHECKING,
              PREEXISTING_NOTSELFCHECKING,
              GENERATED_SELFCHECKING,
              GENERATED_NOTSELFCHECKING,
              NO_TEST_PROGRAM
             } test_program_type;


`endif // __UVMT_CVA6_TDEFS_SV__
