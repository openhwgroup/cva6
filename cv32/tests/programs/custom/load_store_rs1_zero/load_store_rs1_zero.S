################################################################################
#
# Copyright (C) EM Microelectronic US Inc.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
# either express or implied.
#
# See the License for the specific language governing permissions and
# limitations under the License.
#
# SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0
# 
################################################################################
# - Addresses coverage hole in which load and store instructions are not
#   generated for which operand rs1=ZERO.
# - THIS TEST IS SELF CHECKING but should be run against a
#   reference model to check results.
# - This test can be abandoned and corev_rand_instr_test should produce
#   this combination when https://github.com/google/riscv-dv/issues/752
#   is addressed.
################################################################################
.include "user_define.h"
.section .text.start
.globl _start
.section .text
.type _start, @function

_start:
    j _start_main

.globl _start_main
.section .text
_start_main:

# Verify uncompressed load and store
    # Write/read mem[2044]=12, mem[2045]=34, mem[2046]=56, mem[2047]=78
    li a1, 0x12345678
    sw a1, 2044(zero)
    lw a2, 2044(zero)
    bne a2, a1, csr_fail

    # write/read mem[2047]=9A with sb and lb (lbu does sign extend)
    li a3, 0x9A
    sb a3, 2047(zero)
    li a3, 0xFFFFFF9A # Expected value
    lb a4, 2047(zero)
    bne a4, a3, csr_fail
        
    # write/read mem[2047]=BC with sb and lbu (lbu does not sign extend)
    li a5, 0xBC
    sb a5, 2047(zero)
    lbu a6, 2047(zero)
    bne a5, a6, csr_fail
        
test_done:
    lui a0,print_port>>12
    addi a1,zero,'\n'
    sw a1,0(a0)
    addi a1,zero,'C'
    sw a1,0(a0)
    addi a1,zero,'V'
    sw a1,0(a0)
    addi a1,zero,'3'
    sw a1,0(a0)
    addi a1,zero,'2'
    sw a1,0(a0)
    addi a1,zero,' '
    sw a1,0(a0)
    addi a1,zero,'D'
    sw a1,0(a0)
    addi a1,zero,'O'
    sw a1,0(a0)
    addi a1,zero,'N'
    sw a1,0(a0)
    addi a1,zero,'E'
    sw a1,0(a0)
    addi a1,zero,'\n'
    sw a1,0(a0)
    sw a1,0(a0)

csr_pass:
    li x18, 123456789
    li x17, 0x20000000
    sw x18,0(x17)
    wfi

csr_fail:
    lui a0,print_port>>12
    addi a1,zero,'\n'
    sw a1,0(a0)
    addi a1,zero,'C'
    sw a1,0(a0)
    addi a1,zero,'V'
    sw a1,0(a0)
    addi a1,zero,'3'
    sw a1,0(a0)
    addi a1,zero,'2'
    sw a1,0(a0)
    addi a1,zero,' '
    sw a1,0(a0)
    addi a1,zero,'F'
    sw a1,0(a0)
    addi a1,zero,'A'
    sw a1,0(a0)
    addi a1,zero,'I'
    sw a1,0(a0)
    addi a1,zero,'L'
    sw a1,0(a0)
    addi a1,zero,'\n'
    sw a1,0(a0)
    sw a1,0(a0)

    li x18, 1
    li x17, 0x20000000
    sw x18,0(x17)
    wfi
#
# end
#
