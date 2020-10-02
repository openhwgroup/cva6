
/*
**
** Copyright 2020 OpenHW Group
** 
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
** 
**     https://solderpad.org/licenses/
** 
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
** 
*******************************************************************************
** Debugger code
*******************************************************************************
*/

.section .debugger, "ax"
.global _debugger_start
.set test_ret_val, 0x20000000
.set test_fail, 0x1
        
_debugger_start:        
    // No code should have been run before this
    // check dpc == boot_addr == 0x80
    csrr t1, dpc
    li t2, 0x84 # Boot addr 
    bne t1, t2, _debugger_error

    dret

_debugger_error:
    li a0, test_ret_val
    li t0, test_fail
    sw t0, 0(a0)
    dret
