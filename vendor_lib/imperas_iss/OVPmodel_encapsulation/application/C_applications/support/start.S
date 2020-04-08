/*
 * Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com
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


#ifndef TOP_OF_STACK
#   define TOP_OF_STACK 0x10000000
#endif

.global _setup_stack
.global _trap_vector
.global _exit
.global _traphandlerC
.global _boot_value
.global _test_stdout

# boot code
.section .reset_vector,"ax"
 _reset_vector:
    # Point to trap handler code
    la a0, _trap_vector
    csrw mtvec, a0
    # Setup stack pointer
    li sp, TOP_OF_STACK
    # jump to staert
    j _start
    #j _setup_stack

.section .trap_vector,"ax"
_trap_vector:
    call _traphandlerC
    j _exit

.text
_test_exit:
    j _test_exit

# Redefine _exit
_exit:
    j _test_exit

.align 4
.data
_boot_value:
.word 0x0

.section .tty,"aw"
_test_stdout:
.word 0x0

