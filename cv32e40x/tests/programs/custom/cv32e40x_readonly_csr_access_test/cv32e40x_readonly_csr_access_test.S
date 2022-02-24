#
# Copyright (C) EM Microelectronic US Inc.
# Copyright (C) 2020 OpenHW Group
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
# SPDX-License-Identifier: Apache-2.0
#
###############################################################################
# READ ONLY CSRs: access read-only CSRs and check for side-effects.
###############################################################################

.globl _start
.globl main
.globl exit
.global debug
.section .text
.global u_sw_irq_handler

#include "corev_uvmt.h"

#define TEST_PASS                      123456789
#define TEST_FAIL                              1
#define VIRT_PERIPH_STATUS_FLAG_ADDR  CV_VP_STATUS_FLAGS_BASE
#define EXPECTED_ILLEGAL_INSTRUCTIONS         86

main:
    li        t0, (0x1 << 3)
    csrs      mstatus, t0
    li x5, 0x0
    li x6, 0x6
    li x7, 0x7
    li x8, 0x8
    li x9, 0x9
    li x10, 0xa
    li x11, 0xb
    li x12, 0xc
    li x13, 0xd
    li x14, 0xe
    li x15, 0xf
    li x16, 0x10
    li x17, 0x11
    li x18, 0x12
    li x19, 0x13
    li x20, 0x14
    li x21, 0x15
    li x22, 0x16
    li x23, 0x17
    li x24, 0x18
    li x25, 0x19
    li x28, 0x1c
    li x29, 0x1d
    li x30, 0x1e
    li x31, 0x0
    addi    sp,sp,-84
    sw      x6,80(sp)
    sw      x7,76(sp)
    sw      x8,72(sp)
    sw      x9,68(sp)
    sw      x10,64(sp)
    sw      x11,60(sp)
    sw      x12,56(sp)
    sw      x13,52(sp)
    sw      x14,48(sp)
    sw      x15,44(sp)
    sw      x16,40(sp)
    sw      x17,36(sp)
    sw      x18,32(sp)
    sw      x19,28(sp)
    sw      x20,24(sp)
    sw      x21,20(sp)
    sw      x22,16(sp)
    sw      x23,12(sp)
    sw      x24,8(sp)
    sw      x25,4(sp)
###############################################################################

	csrrci x5,  0x340, 0x0a   # not illegal instruction: attempt to write RW CSR

	# mhpmevent3
	csrrci x5,  0x323, 0x0a   # not illegal instruction: attempt to write RW CSR
	csrrc  x5,  0x323, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  0x323, x5     # not illegal instruction: attempt to write RW CSR
	csrrci x5,  0x323, 0x0a   # not illegal instruction: attempt to write RW CSR
	csrrs  x0,  0x323, x5     # not illegal instruction: attempt to write RW CSR
 	csrrsi x0,  0x323, 0x0a   # not illegal instruction: attempt to write RW CSR
 	csrrw  x0,  0x323, x0     # not illegal instruction: attempt to write RW CSR
	csrrwi x0,  0x323, 0x0a   # not illegal instruction: attempt to write RW CSR

	# mvendorid
	csrrc  x5,  0xF11, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  0xF11, x5     # illegal instruction: attempt to write RO CSR
	csrrci x5,  0xF11, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  0xF11, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xF11, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xF11, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  0xF11, 0x0a   # illegal instruction: attempt to write RO CSR

	csrrc  x5,  0xF11, x0     # not illegal
	li     x30, 0x00000602
	bne    x5,  x30, fail

	# marchid
	csrrc  x5,  0xF12, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  0xF12, x5     # illegal instruction: attempt to write RO CSR
	csrrci x0,  0xF12, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  0xF12, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xF12, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xF12, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  0xF12, 0x0a   # illegal instruction: attempt to write RO CSR

	csrrc  x5,  0xF12, x0     # not illegal
	li     x30, 0x00000014
	bne    x5,  x30, fail

	# mipmid
	csrrc  x5,  0xF13, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  0xF13, x5     # illegal instruction: attempt to write RO CSR
	csrrci x0,  0xF13, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  0xF13, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xF13, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xF13, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  0xF13, 0x0a   # illegal instruction: attempt to write RO CSR

	csrrc  x5,  0xF13, x0     # not illegal
	li     x30, 0x00000000
	bne    x5,  x30, fail

  # mhartid
  csrrc  x5,  0xF14, x0     # not illegal instruction: no attempt to write RO CSR
  csrrc  x0,  0xF14, x5     # illegal instruction: attempt to write RO CSR
  csrrci x0,  0xF14, 0x0a   # illegal instruction: attempt to write RO CSR
  csrrs  x0,  0xF14, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xF14, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xF14, x0     # illegal instruction: attempt to write RO CSR
  csrrwi x0,  0xF14, 0x0a   # illegal instruction: attempt to write RO CSR

	csrrc  x5,  0xF14, x0     # not illegal
	li     x30, 0x00000000
	bne    x5,  x30, fail

  # mconfigptr 3861
  csrrc  x5,  0xF15, x0     # not illegal instruction: no attempt to write RO CSR
  csrrc  x0,  0xF15, x5     # illegal instruction: attempt to write RO CSR
  csrrci x0,  0xF15, 0x0a   # illegal instruction: attempt to write RO CSR
  csrrs  x0,  0xF15, x5     # illegal instruction: attempt to write RO CSR
  csrrsi x0,  0xF15, 0x0a   # illegal instruction: attempt to write RO CSR
  csrrw  x0,  0xF15, x0     # illegal instruction: attempt to write RO CSR
  csrrwi x0,  0xF15, 0x0a   # illegal instruction: attempt to write RO CSR

  csrrc  x5,  0xF15, x0     # not illegal
  li     x30, 0x00000000
  bne    x5,  x30, fail

  ##
  ## Access the User Custom CSRs.   These are all illegal instructions when
  ## PULP_XPULP = 0 (which is the default for CV32E40X).
  ##

  # lpstart0
  csrrc  x5,  0x800, x0     # illegal instructions: attempt access "non-existant" CSR
  csrrc  x0,  0x800, x5
  csrrci x0,  0x800, 0x0a
  csrrs  x0,  0x800, x5
 	csrrsi x0,  0x800, 0x0a
 	csrrw  x0,  0x800, x0
  csrrwi x0,  0x800, 0x0a

  # lpend0
  csrrc  x5,  0x801, x0     # illegal instructions: attempt access "non-existant" CSR
  csrrc  x0,  0x801, x5
  csrrci x0,  0x801, 0x0a
  csrrs  x0,  0x801, x5
 	csrrsi x0,  0x801, 0x0a
 	csrrw  x0,  0x801, x0
  csrrwi x0,  0x801, 0x0a

  # lpcount0
  csrrc  x5,  0x802, x0     # illegal instructions: attempt access "non-existant" CSR
  csrrc  x0,  0x802, x5
  csrrci x0,  0x802, 0x0a
  csrrs  x0,  0x802, x5
 	csrrsi x0,  0x802, 0x0a
 	csrrw  x0,  0x802, x0
  csrrwi x0,  0x802, 0x0a

  # lpstart1
  csrrc  x5,  0x804, x0     # illegal instructions: attempt access "non-existant" CSR
  csrrc  x0,  0x804, x5
  csrrci x0,  0x804, 0x0a
  csrrs  x0,  0x804, x5
 	csrrsi x0,  0x804, 0x0a
 	csrrw  x0,  0x804, x0
  csrrwi x0,  0x804, 0x0a

  # lpend1
  csrrc  x5,  0x805, x0     # illegal instructions: attempt access "non-existant" CSR
  csrrc  x0,  0x805, x5
  csrrci x0,  0x805, 0x0a
  csrrs  x0,  0x805, x5
 	csrrsi x0,  0x805, 0x0a
 	csrrw  x0,  0x805, x0
  csrrwi x0,  0x805, 0x0a

  # lpcount1
  csrrc  x5,  0x806, x0     # illegal instructions: attempt access "non-existant" CSR
  csrrc  x0,  0x806, x5
  csrrci x0,  0x806, 0x0a
  csrrs  x0,  0x806, x5
 	csrrsi x0,  0x806, 0x0a
 	csrrw  x0,  0x806, x0
  csrrwi x0,  0x806, 0x0a

  # uhartid
  csrrc  x5,  0xCC0, x0     # illegal instructions: attempt access "non-existant" CSR
  csrrc  x0,  0xCC0, x5
  csrrci x0,  0xCC0, 0x0a
  csrrs  x0,  0xCC0, x5
 	csrrsi x0,  0xCC0, 0x0a
 	csrrw  x0,  0xCC0, x0
  csrrwi x0,  0xCC0, 0x0a

  # privlv
  csrrc  x5,  0xCC1, x0     # illegal instructions: attempt access "non-existant" CSR
  csrrc  x0,  0xCC1, x5
  csrrci x0,  0xCC1, 0x0a
  csrrs  x0,  0xCC1, x5
 	csrrsi x0,  0xCC1, 0x0a
 	csrrw  x0,  0xCC1, x0
  csrrwi x0,  0xCC1, 0x0a

###############################################################################
    lw      x5,80(sp)
    bne     x5, x6, fail
    lw      x5,76(sp)
    bne     x5, x7, fail
    lw      x5,72(sp)
    bne     x5, x8, fail
    lw      x5,68(sp)
    bne     x5, x9, fail
    lw      x5,64(sp)
    bne     x5, x10, fail
    lw      x5,60(sp)
    bne     x5, x11, fail
    lw      x5,56(sp)
    bne     x5, x12, fail
    lw      x5,52(sp)
    bne     x5, x13, fail
    lw      x5,48(sp)
    bne     x5, x14, fail
    lw      x5,44(sp)
    bne     x5, x15, fail
    lw      x5,40(sp)
    bne     x5, x16, fail
    lw      x5,36(sp)
    bne     x5, x17, fail
    lw      x5,32(sp)
    bne     x5, x18, fail
    lw      x5,28(sp)
    bne     x5, x19, fail
    lw      x5,24(sp)
    bne     x5, x20, fail
    lw      x5,20(sp)
    bne     x5, x21, fail
    lw      x5,16(sp)
    bne     x5, x22, fail
    lw      x5,12(sp)
    bne     x5, x23, fail
    lw      x5,8(sp)
    bne     x5, x24, fail
    lw      x5,4(sp)
    bne     x5, x25, fail
    addi    sp,sp,84
    li x18, TEST_PASS
    li x16, EXPECTED_ILLEGAL_INSTRUCTIONS
    beq x31, x16, test_end
fail:
    li x18, TEST_FAIL
test_end:
    li x17, VIRT_PERIPH_STATUS_FLAG_ADDR
    sw x18,0(x17)
    j _exit

# The "sw_irq_handler" is entered on each illegal instruction.  Clears
# mepc and increments the illegal instruction count in x31.
u_sw_irq_handler:
    li x30, 0xf
    csrrc x29, mcause, x0
    and x30, x29, x30
    li x28, 2
    bne x30, x28, _exit
    csrrc x27, mepc, x0
    c.addi x27, 4
    csrrw x0, mepc, x27
    c.addi x31, 1
    mret

_exit:
    j _exit

debug:
    j _exit
