/*
 * Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com
 * Copyright (C) EM Microelectronic US Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
 * either express or implied.
 *
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */


package params_pkg;
   parameter int INSTR_RDATA_WIDTH=32;
   parameter int APU_NARGS_CPU=3;
   parameter int APU_WOP_CPU=6;
   parameter int APU_NDSFLAGS_CPU=15;
   parameter int APU_NUSFLAGS_CPU=5;
   parameter int WAPUTYPE=0;
   parameter int N_EXT_PERF_COUNTERS=0;

   // IRQ
   parameter int NUM_IRQ    = 64;
   parameter int NUM_LEVELS = 3;
   parameter int IRQ_ID_W   = 5;
   parameter int IRQ_LEV_W  = 2;

   typedef enum {WFI} opcode_e;
endpackage // params_pkg
   
