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
# MHPMCOUNTERS29: access testcase for mhpmcounter3..31 CSRs in cv32e40s.
#     Notes:
#       1. This test requires NUM_MHPMCOUNTERS set to 29.
#       2. Does not test function - just access.
#       3. FIXME: ISS currently does not set mcountinhibit correctly on reset
#          for non-default number of registers, RVVI and RVFI will mismatch if
#          sb checking is enabled.
###############################################################################
#include "corev_uvmt.h"

.globl _start
.globl main
.globl exit
.global debug
.section .text
.global u_sw_irq_handler


#define TEST_PASS                      123456789
#define TEST_FAIL                              1
#define VIRT_PERIPH_STATUS_FLAG_ADDR  CV_VP_STATUS_FLAGS_BASE
#define EXPECTED_ILLEGAL_INSTRUCTIONS         24

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
# Do-nothing reads/writes to mhpmevent3..31, mhpmcounter3..31, mhpmcounterh3..31,
# to ensure that all CSR instructions ping each of these CSRs at least once.

	# mhpmevent3
	csrrci x5,  0x323, 0x0a   # not illegal instruction: attempt to write RW CSR
	csrrc  x5,  0x323, x0     # not illegal instruction: no attempt to write CSR
	csrrc  x0,  0x323, x5     # not illegal instruction: attempt to write RW CSR
	csrrci x5,  0x323, 0x0a   # not illegal instruction: attempt to write RW CSR
	csrrs  x0,  0x323, x5     # not illegal instruction: attempt to write RW CSR
 	csrrsi x0,  0x323, 0x0a   # not illegal instruction: attempt to write RW CSR
 	csrrw  x0,  0x323, x0     # not illegal instruction: attempt to write RW CSR
	csrrwi x0,  0x323, 0x0a   # not illegal instruction: attempt to write RW CSR

	# mhpmevent4
	csrrci x5,  0x324, 0x0a
	csrrc  x5,  0x324, x0
	csrrc  x0,  0x324, x5
	csrrci x5,  0x324, 0x0a
	csrrs  x0,  0x324, x5
 	csrrsi x0,  0x324, 0x0a
 	csrrw  x0,  0x324, x0
	csrrwi x0,  0x324, 0x0a

	# mhpmevent5
	csrrci x5,  0x325, 0x0a
	csrrc  x5,  0x325, x0
	csrrc  x0,  0x325, x5
	csrrci x5,  0x325, 0x0a
	csrrs  x0,  0x325, x5
 	csrrsi x0,  0x325, 0x0a
 	csrrw  x0,  0x325, x0
	csrrwi x0,  0x325, 0x0a

	# mhpmevent6
	csrrci x5,  0x326, 0x0a
	csrrc  x5,  0x326, x0
	csrrc  x0,  0x326, x5
	csrrci x5,  0x326, 0x0a
	csrrs  x0,  0x326, x5
 	csrrsi x0,  0x326, 0x0a
 	csrrw  x0,  0x326, x0
	csrrwi x0,  0x326, 0x0a

	# mhpmevent7
	csrrci x5,  0x327, 0x0a
	csrrc  x5,  0x327, x0
	csrrc  x0,  0x327, x5
	csrrci x5,  0x327, 0x0a
	csrrs  x0,  0x327, x5
 	csrrsi x0,  0x327, 0x0a
 	csrrw  x0,  0x327, x0
	csrrwi x0,  0x327, 0x0a

	# mhpmevent8
	csrrci x5,  0x328, 0x0a
	csrrc  x5,  0x328, x0
	csrrc  x0,  0x328, x5
	csrrci x5,  0x328, 0x0a
	csrrs  x0,  0x328, x5
 	csrrsi x0,  0x328, 0x0a
 	csrrw  x0,  0x328, x0
	csrrwi x0,  0x328, 0x0a

	# mhpmevent9
	csrrci x5,  0x329, 0x0a
	csrrc  x5,  0x329, x0
	csrrc  x0,  0x329, x5
	csrrci x5,  0x329, 0x0a
	csrrs  x0,  0x329, x5
 	csrrsi x0,  0x329, 0x0a
 	csrrw  x0,  0x329, x0
	csrrwi x0,  0x329, 0x0a

	# mhpmevent10
	csrrci x5,  0x32a, 0x0a
	csrrc  x5,  0x32a, x0
	csrrc  x0,  0x32a, x5
	csrrci x5,  0x32a, 0x0a
	csrrs  x0,  0x32a, x5
 	csrrsi x0,  0x32a, 0x0a
 	csrrw  x0,  0x32a, x0
	csrrwi x0,  0x32a, 0x0a

	# mhpmevent11
	csrrci x5,  0x32b, 0x0a
	csrrc  x5,  0x32b, x0
	csrrc  x0,  0x32b, x5
	csrrci x5,  0x32b, 0x0a
	csrrs  x0,  0x32b, x5
 	csrrsi x0,  0x32b, 0x0a
 	csrrw  x0,  0x32b, x0
	csrrwi x0,  0x32b, 0x0a

	# mhpmevent12
	csrrci x5,  0x32c, 0x0a
	csrrc  x5,  0x32c, x0
	csrrc  x0,  0x32c, x5
	csrrci x5,  0x32c, 0x0a
	csrrs  x0,  0x32c, x5
 	csrrsi x0,  0x32c, 0x0a
 	csrrw  x0,  0x32c, x0
	csrrwi x0,  0x32c, 0x0a

	# mhpmevent13
	csrrci x5,  0x32d, 0x0a
	csrrc  x5,  0x32d, x0
	csrrc  x0,  0x32d, x5
	csrrci x5,  0x32d, 0x0a
	csrrs  x0,  0x32d, x5
 	csrrsi x0,  0x32d, 0x0a
 	csrrw  x0,  0x32d, x0
	csrrwi x0,  0x32d, 0x0a

	# mhpmevent14
	csrrci x5,  0x32e, 0x0a
	csrrc  x5,  0x32e, x0
	csrrc  x0,  0x32e, x5
	csrrci x5,  0x32e, 0x0a
	csrrs  x0,  0x32e, x5
 	csrrsi x0,  0x32e, 0x0a
 	csrrw  x0,  0x32e, x0
	csrrwi x0,  0x32e, 0x0a

	# mhpmevent15
	csrrci x5,  0x32f, 0x0a
	csrrc  x5,  0x32f, x0
	csrrc  x0,  0x32f, x5
	csrrci x5,  0x32f, 0x0a
	csrrs  x0,  0x32f, x5
 	csrrsi x0,  0x32f, 0x0a
 	csrrw  x0,  0x32f, x0
	csrrwi x0,  0x32f, 0x0a

	# mhpmevent16
	csrrci x5,  0x330, 0x0a
	csrrc  x5,  0x330, x0
	csrrc  x0,  0x330, x5
	csrrci x5,  0x330, 0x0a
	csrrs  x0,  0x330, x5
 	csrrsi x0,  0x330, 0x0a
 	csrrw  x0,  0x330, x0
	csrrwi x0,  0x330, 0x0a

	# mhpmevent17
	csrrci x5,  0x331, 0x0a
	csrrc  x5,  0x331, x0
	csrrc  x0,  0x331, x5
	csrrci x5,  0x331, 0x0a
	csrrs  x0,  0x331, x5
 	csrrsi x0,  0x331, 0x0a
 	csrrw  x0,  0x331, x0
	csrrwi x0,  0x331, 0x0a

	# mhpmevent18
	csrrci x5,  0x332, 0x0a
	csrrc  x5,  0x332, x0
	csrrc  x0,  0x332, x5
	csrrci x5,  0x332, 0x0a
	csrrs  x0,  0x332, x5
 	csrrsi x0,  0x332, 0x0a
 	csrrw  x0,  0x332, x0
	csrrwi x0,  0x332, 0x0a

	# mhpmevent19
	csrrci x5,  0x333, 0x0a
	csrrc  x5,  0x333, x0
	csrrc  x0,  0x333, x5
	csrrci x5,  0x333, 0x0a
	csrrs  x0,  0x333, x5
 	csrrsi x0,  0x333, 0x0a
 	csrrw  x0,  0x333, x0
	csrrwi x0,  0x333, 0x0a

	# mhpmevent20
	csrrci x5,  0x334, 0x0a
	csrrc  x5,  0x334, x0
	csrrc  x0,  0x334, x5
	csrrci x5,  0x334, 0x0a
	csrrs  x0,  0x334, x5
 	csrrsi x0,  0x334, 0x0a
 	csrrw  x0,  0x334, x0
	csrrwi x0,  0x334, 0x0a

	# mhpmevent21
	csrrci x5,  0x335, 0x0a
	csrrc  x5,  0x335, x0
	csrrc  x0,  0x335, x5
	csrrci x5,  0x335, 0x0a
	csrrs  x0,  0x335, x5
 	csrrsi x0,  0x335, 0x0a
 	csrrw  x0,  0x335, x0
	csrrwi x0,  0x335, 0x0a

	# mhpmevent22
	csrrci x5,  0x336, 0x0a
	csrrc  x5,  0x336, x0
	csrrc  x0,  0x336, x5
	csrrci x5,  0x336, 0x0a
	csrrs  x0,  0x336, x5
 	csrrsi x0,  0x336, 0x0a
 	csrrw  x0,  0x336, x0
	csrrwi x0,  0x336, 0x0a

	# mhpmevent23
	csrrci x5,  0x337, 0x0a
	csrrc  x5,  0x337, x0
	csrrc  x0,  0x337, x5
	csrrci x5,  0x337, 0x0a
	csrrs  x0,  0x337, x5
 	csrrsi x0,  0x337, 0x0a
 	csrrw  x0,  0x337, x0
	csrrwi x0,  0x337, 0x0a

	# mhpmevent24
	csrrci x5,  0x338, 0x0a
	csrrc  x5,  0x338, x0
	csrrc  x0,  0x338, x5
	csrrci x5,  0x338, 0x0a
	csrrs  x0,  0x338, x5
 	csrrsi x0,  0x338, 0x0a
 	csrrw  x0,  0x338, x0
	csrrwi x0,  0x338, 0x0a

	# mhpmevent25
	csrrci x5,  0x339, 0x0a
	csrrc  x5,  0x339, x0
	csrrc  x0,  0x339, x5
	csrrci x5,  0x339, 0x0a
	csrrs  x0,  0x339, x5
 	csrrsi x0,  0x339, 0x0a
 	csrrw  x0,  0x339, x0
	csrrwi x0,  0x339, 0x0a

	# mhpmevent26
	csrrci x5,  0x33a, 0x0a
	csrrc  x5,  0x33a, x0
	csrrc  x0,  0x33a, x5
	csrrci x5,  0x33a, 0x0a
	csrrs  x0,  0x33a, x5
 	csrrsi x0,  0x33a, 0x0a
 	csrrw  x0,  0x33a, x0
	csrrwi x0,  0x33a, 0x0a

	# mhpmevent27
	csrrci x5,  0x33b, 0x0a
	csrrc  x5,  0x33b, x0
	csrrc  x0,  0x33b, x5
	csrrci x5,  0x33b, 0x0a
	csrrs  x0,  0x33b, x5
 	csrrsi x0,  0x33b, 0x0a
 	csrrw  x0,  0x33b, x0
	csrrwi x0,  0x33b, 0x0a

	# mhpmevent28
	csrrci x5,  0x33c, 0x0a
	csrrc  x5,  0x33c, x0
	csrrc  x0,  0x33c, x5
	csrrci x5,  0x33c, 0x0a
	csrrs  x0,  0x33c, x5
 	csrrsi x0,  0x33c, 0x0a
 	csrrw  x0,  0x33c, x0
	csrrwi x0,  0x33c, 0x0a

	# mhpmevent29
	csrrci x5,  0x33d, 0x0a
	csrrc  x5,  0x33d, x0
	csrrc  x0,  0x33d, x5
	csrrci x5,  0x33d, 0x0a
	csrrs  x0,  0x33d, x5
 	csrrsi x0,  0x33d, 0x0a
 	csrrw  x0,  0x33d, x0
	csrrwi x0,  0x33d, 0x0a

	# mhpmevent30
	csrrci x5,  0x33e, 0x0a
	csrrc  x5,  0x33e, x0
	csrrc  x0,  0x33e, x5
	csrrci x5,  0x33e, 0x0a
	csrrs  x0,  0x33e, x5
 	csrrsi x0,  0x33e, 0x0a
 	csrrw  x0,  0x33e, x0
	csrrwi x0,  0x33e, 0x0a

	# mhpmevent31
	csrrci x5,  0x33f, 0x0a
	csrrc  x5,  0x33f, x0
	csrrc  x0,  0x33f, x5
	csrrci x5,  0x33f, 0x0a
	csrrs  x0,  0x33f, x5
 	csrrsi x0,  0x33f, 0x0a
 	csrrw  x0,  0x33f, x0
	csrrwi x0,  0x33f, 0x0a

    ################

	# mhpmcounter3
	csrrci x5,  0xB03, 0x0a   # not illegal instruction: attempt to write RW CSR
	csrrc  x5,  0xB03, x0     # not illegal instruction: no attempt to write CSR
	csrrc  x0,  0xB03, x5     # not illegal instruction: attempt to write RW CSR
	csrrci x5,  0xB03, 0x0a   # not illegal instruction: attempt to write RW CSR
	csrrs  x0,  0xB03, x5     # not illegal instruction: attempt to write RW CSR
 	csrrsi x0,  0xB03, 0x0a   # not illegal instruction: attempt to write RW CSR
 	csrrw  x0,  0xB03, x0     # not illegal instruction: attempt to write RW CSR
	csrrwi x0,  0xB03, 0x0a   # not illegal instruction: attempt to write RW CSR

	# mhpmcounter4
	csrrci x5,  0xB04, 0x0a
	csrrc  x5,  0xB04, x0
	csrrc  x0,  0xB04, x5
	csrrci x5,  0xB04, 0x0a
	csrrs  x0,  0xB04, x5
 	csrrsi x0,  0xB04, 0x0a
 	csrrw  x0,  0xB04, x0
	csrrwi x0,  0xB04, 0x0a

	# mhpmcounter5
	csrrci x5,  0xB05, 0x0a
	csrrc  x5,  0xB05, x0
	csrrc  x0,  0xB05, x5
	csrrci x5,  0xB05, 0x0a
	csrrs  x0,  0xB05, x5
 	csrrsi x0,  0xB05, 0x0a
 	csrrw  x0,  0xB05, x0
	csrrwi x0,  0xB05, 0x0a

	# mhpmcounter6
	csrrci x5,  0xB06, 0x0a
	csrrc  x5,  0xB06, x0
	csrrc  x0,  0xB06, x5
	csrrci x5,  0xB06, 0x0a
	csrrs  x0,  0xB06, x5
 	csrrsi x0,  0xB06, 0x0a
 	csrrw  x0,  0xB06, x0
	csrrwi x0,  0xB06, 0x0a

	# mhpmcounter7
	csrrci x5,  0xB07, 0x0a
	csrrc  x5,  0xB07, x0
	csrrc  x0,  0xB07, x5
	csrrci x5,  0xB07, 0x0a
	csrrs  x0,  0xB07, x5
 	csrrsi x0,  0xB07, 0x0a
 	csrrw  x0,  0xB07, x0
	csrrwi x0,  0xB07, 0x0a

	# mhpmcounter8
	csrrci x5,  0xB08, 0x0a
	csrrc  x5,  0xB08, x0
	csrrc  x0,  0xB08, x5
	csrrci x5,  0xB08, 0x0a
	csrrs  x0,  0xB08, x5
 	csrrsi x0,  0xB08, 0x0a
 	csrrw  x0,  0xB08, x0
	csrrwi x0,  0xB08, 0x0a

	# mhpmcounter9
	csrrci x5,  0xB09, 0x0a
	csrrc  x5,  0xB09, x0
	csrrc  x0,  0xB09, x5
	csrrci x5,  0xB09, 0x0a
	csrrs  x0,  0xB09, x5
 	csrrsi x0,  0xB09, 0x0a
 	csrrw  x0,  0xB09, x0
	csrrwi x0,  0xB09, 0x0a

	# mhpmcounter10
	csrrci x5,  0xB0A, 0x0a
	csrrc  x5,  0xB0A, x0
	csrrc  x0,  0xB0A, x5
	csrrci x5,  0xB0A, 0x0a
	csrrs  x0,  0xB0A, x5
 	csrrsi x0,  0xB0A, 0x0a
 	csrrw  x0,  0xB0A, x0
	csrrwi x0,  0xB0A, 0x0a

	# mhpmcounter11
	csrrci x5,  0xB0B, 0x0a
	csrrc  x5,  0xB0B, x0
	csrrc  x0,  0xB0B, x5
	csrrci x5,  0xB0B, 0x0a
	csrrs  x0,  0xB0B, x5
 	csrrsi x0,  0xB0B, 0x0a
 	csrrw  x0,  0xB0B, x0
	csrrwi x0,  0xB0B, 0x0a

	# mhpmcounter12
	csrrci x5,  0xB0C, 0x0a
	csrrc  x5,  0xB0C, x0
	csrrc  x0,  0xB0C, x5
	csrrci x5,  0xB0C, 0x0a
	csrrs  x0,  0xB0C, x5
 	csrrsi x0,  0xB0C, 0x0a
 	csrrw  x0,  0xB0C, x0
	csrrwi x0,  0xB0C, 0x0a

	# mhpmcounter13
	csrrci x5,  0xB0D, 0x0a
	csrrc  x5,  0xB0D, x0
	csrrc  x0,  0xB0D, x5
	csrrci x5,  0xB0D, 0x0a
	csrrs  x0,  0xB0D, x5
 	csrrsi x0,  0xB0D, 0x0a
 	csrrw  x0,  0xB0D, x0
	csrrwi x0,  0xB0D, 0x0a

	# mhpmcounter14
	csrrci x5,  0xB0E, 0x0a
	csrrc  x5,  0xB0E, x0
	csrrc  x0,  0xB0E, x5
	csrrci x5,  0xB0E, 0x0a
	csrrs  x0,  0xB0E, x5
 	csrrsi x0,  0xB0E, 0x0a
 	csrrw  x0,  0xB0E, x0
	csrrwi x0,  0xB0E, 0x0a

	# mhpmcounter15
	csrrci x5,  0xB0F, 0x0a
	csrrc  x5,  0xB0F, x0
	csrrc  x0,  0xB0F, x5
	csrrci x5,  0xB0F, 0x0a
	csrrs  x0,  0xB0F, x5
 	csrrsi x0,  0xB0F, 0x0a
 	csrrw  x0,  0xB0F, x0
	csrrwi x0,  0xB0F, 0x0a

	# mhpmcounter16
	csrrci x5,  0xB10, 0x0a
	csrrc  x5,  0xB10, x0
	csrrc  x0,  0xB10, x5
	csrrci x5,  0xB10, 0x0a
	csrrs  x0,  0xB10, x5
 	csrrsi x0,  0xB10, 0x0a
 	csrrw  x0,  0xB10, x0
	csrrwi x0,  0xB10, 0x0a

	# mhpmcounter17
	csrrci x5,  0xB11, 0x0a
	csrrc  x5,  0xB11, x0
	csrrc  x0,  0xB11, x5
	csrrci x5,  0xB11, 0x0a
	csrrs  x0,  0xB11, x5
 	csrrsi x0,  0xB11, 0x0a
 	csrrw  x0,  0xB11, x0
	csrrwi x0,  0xB11, 0x0a

	# mhpmcounter18
	csrrci x5,  0xB12, 0x0a
	csrrc  x5,  0xB12, x0
	csrrc  x0,  0xB12, x5
	csrrci x5,  0xB12, 0x0a
	csrrs  x0,  0xB12, x5
 	csrrsi x0,  0xB12, 0x0a
 	csrrw  x0,  0xB12, x0
	csrrwi x0,  0xB12, 0x0a

	# mhpmcounter19
	csrrci x5,  0xB13, 0x0a
	csrrc  x5,  0xB13, x0
	csrrc  x0,  0xB13, x5
	csrrci x5,  0xB13, 0x0a
	csrrs  x0,  0xB13, x5
 	csrrsi x0,  0xB13, 0x0a
 	csrrw  x0,  0xB13, x0
	csrrwi x0,  0xB13, 0x0a

	# mhpmcounter20
	csrrci x5,  0xB14, 0x0a
	csrrc  x5,  0xB14, x0
	csrrc  x0,  0xB14, x5
	csrrci x5,  0xB14, 0x0a
	csrrs  x0,  0xB14, x5
 	csrrsi x0,  0xB14, 0x0a
 	csrrw  x0,  0xB14, x0
	csrrwi x0,  0xB14, 0x0a

	# mhpmcounter21
	csrrci x5,  0xB15, 0x0a
	csrrc  x5,  0xB15, x0
	csrrc  x0,  0xB15, x5
	csrrci x5,  0xB15, 0x0a
	csrrs  x0,  0xB15, x5
 	csrrsi x0,  0xB15, 0x0a
 	csrrw  x0,  0xB15, x0
	csrrwi x0,  0xB15, 0x0a

	# mhpmcounter22
	csrrci x5,  0xB16, 0x0a
	csrrc  x5,  0xB16, x0
	csrrc  x0,  0xB16, x5
	csrrci x5,  0xB16, 0x0a
	csrrs  x0,  0xB16, x5
 	csrrsi x0,  0xB16, 0x0a
 	csrrw  x0,  0xB16, x0
	csrrwi x0,  0xB16, 0x0a

	# mhpmcounter23
	csrrci x5,  0xB17, 0x0a
	csrrc  x5,  0xB17, x0
	csrrc  x0,  0xB17, x5
	csrrci x5,  0xB17, 0x0a
	csrrs  x0,  0xB17, x5
 	csrrsi x0,  0xB17, 0x0a
 	csrrw  x0,  0xB17, x0
	csrrwi x0,  0xB17, 0x0a

	# mhpmcounter24
	csrrci x5,  0xB18, 0x0a
	csrrc  x5,  0xB18, x0
	csrrc  x0,  0xB18, x5
	csrrci x5,  0xB18, 0x0a
	csrrs  x0,  0xB18, x5
 	csrrsi x0,  0xB18, 0x0a
 	csrrw  x0,  0xB18, x0
	csrrwi x0,  0xB18, 0x0a

	# mhpmcounter25
	csrrci x5,  0xB19, 0x0a
	csrrc  x5,  0xB19, x0
	csrrc  x0,  0xB19, x5
	csrrci x5,  0xB19, 0x0a
	csrrs  x0,  0xB19, x5
 	csrrsi x0,  0xB19, 0x0a
 	csrrw  x0,  0xB19, x0
	csrrwi x0,  0xB19, 0x0a

	# mhpmcounter26
	csrrci x5,  0xB1A, 0x0a
	csrrc  x5,  0xB1A, x0
	csrrc  x0,  0xB1A, x5
	csrrci x5,  0xB1A, 0x0a
	csrrs  x0,  0xB1A, x5
 	csrrsi x0,  0xB1A, 0x0a
 	csrrw  x0,  0xB1A, x0
	csrrwi x0,  0xB1A, 0x0a

	# mhpmcounter27
	csrrci x5,  0xB1B, 0x0a
	csrrc  x5,  0xB1B, x0
	csrrc  x0,  0xB1B, x5
	csrrci x5,  0xB1B, 0x0a
	csrrs  x0,  0xB1B, x5
 	csrrsi x0,  0xB1B, 0x0a
 	csrrw  x0,  0xB1B, x0
	csrrwi x0,  0xB1B, 0x0a

	# mhpmcounter28
	csrrci x5,  0xB1C, 0x0a
	csrrc  x5,  0xB1C, x0
	csrrc  x0,  0xB1C, x5
	csrrci x5,  0xB1C, 0x0a
	csrrs  x0,  0xB1C, x5
 	csrrsi x0,  0xB1C, 0x0a
 	csrrw  x0,  0xB1C, x0
	csrrwi x0,  0xB1C, 0x0a

	# mhpmcounter29
	csrrci x5,  0xB1D, 0x0a
	csrrc  x5,  0xB1D, x0
	csrrc  x0,  0xB1D, x5
	csrrci x5,  0xB1D, 0x0a
	csrrs  x0,  0xB1D, x5
 	csrrsi x0,  0xB1D, 0x0a
 	csrrw  x0,  0xB1D, x0
	csrrwi x0,  0xB1D, 0x0a

	# mhpmcounter30
	csrrci x5,  0xB1E, 0x0a
	csrrc  x5,  0xB1E, x0
	csrrc  x0,  0xB1E, x5
	csrrci x5,  0xB1E, 0x0a
	csrrs  x0,  0xB1E, x5
 	csrrsi x0,  0xB1E, 0x0a
 	csrrw  x0,  0xB1E, x0
	csrrwi x0,  0xB1E, 0x0a

	# mhpmcounter31
	csrrci x5,  0xB1F, 0x0a
	csrrc  x5,  0xB1F, x0
	csrrc  x0,  0xB1F, x5
	csrrci x5,  0xB1F, 0x0a
	csrrs  x0,  0xB1F, x5
 	csrrsi x0,  0xB1F, 0x0a
 	csrrw  x0,  0xB1F, x0
	csrrwi x0,  0xB1F, 0x0a

    ################

	# mhpmcounter3h
	csrrci x5,  0xB83, 0x0a   # not illegal instruction: attempt to write RW CSR
	csrrc  x5,  0xB83, x0     # not illegal instruction: no attempt to write CSR
	csrrc  x0,  0xB83, x5     # not illegal instruction: attempt to write RW CSR
	csrrci x5,  0xB83, 0x0a   # not illegal instruction: attempt to write RW CSR
	csrrs  x0,  0xB83, x5     # not illegal instruction: attempt to write RW CSR
 	csrrsi x0,  0xB83, 0x0a   # not illegal instruction: attempt to write RW CSR
 	csrrw  x0,  0xB83, x0     # not illegal instruction: attempt to write RW CSR
	csrrwi x0,  0xB83, 0x0a   # not illegal instruction: attempt to write RW CSR

	# mhpmcounter4h
	csrrci x5,  0xB84, 0x0a   # not illegal instruction: attempt to write RW CSR
	csrrc  x5,  0xB84, x0     # not illegal instruction: no attempt to write CSR
	csrrc  x0,  0xB84, x5     # not illegal instruction: attempt to write RW CSR
	csrrci x5,  0xB84, 0x0a   # not illegal instruction: attempt to write RW CSR
	csrrs  x0,  0xB84, x5     # not illegal instruction: attempt to write RW CSR
 	csrrsi x0,  0xB84, 0x0a   # not illegal instruction: attempt to write RW CSR
 	csrrw  x0,  0xB84, x0     # not illegal instruction: attempt to write RW CSR
	csrrwi x0,  0xB84, 0x0a   # not illegal instruction: attempt to write RW CSR

	# mhpmcounterh5
	csrrci x5,  0xB85, 0x0a
	csrrc  x5,  0xB85, x0
	csrrc  x0,  0xB85, x5
	csrrci x5,  0xB85, 0x0a
	csrrs  x0,  0xB85, x5
 	csrrsi x0,  0xB85, 0x0a
 	csrrw  x0,  0xB85, x0
	csrrwi x0,  0xB85, 0x0a

	# mhpmcounterh6
	csrrci x5,  0xB86, 0x0a
	csrrc  x5,  0xB86, x0
	csrrc  x0,  0xB86, x5
	csrrci x5,  0xB86, 0x0a
	csrrs  x0,  0xB86, x5
 	csrrsi x0,  0xB86, 0x0a
 	csrrw  x0,  0xB86, x0
	csrrwi x0,  0xB86, 0x0a

	# mhpmcounterh7
	csrrci x5,  0xB87, 0x0a
	csrrc  x5,  0xB87, x0
	csrrc  x0,  0xB87, x5
	csrrci x5,  0xB87, 0x0a
	csrrs  x0,  0xB87, x5
 	csrrsi x0,  0xB87, 0x0a
 	csrrw  x0,  0xB87, x0
	csrrwi x0,  0xB87, 0x0a

	# mhpmcounterh8
	csrrci x5,  0xB88, 0x0a
	csrrc  x5,  0xB88, x0
	csrrc  x0,  0xB88, x5
	csrrci x5,  0xB88, 0x0a
	csrrs  x0,  0xB88, x5
 	csrrsi x0,  0xB88, 0x0a
 	csrrw  x0,  0xB88, x0
	csrrwi x0,  0xB88, 0x0a

	# mhpmcounterh9
	csrrci x5,  0xB89, 0x0a
	csrrc  x5,  0xB89, x0
	csrrc  x0,  0xB89, x5
	csrrci x5,  0xB89, 0x0a
	csrrs  x0,  0xB89, x5
 	csrrsi x0,  0xB89, 0x0a
 	csrrw  x0,  0xB89, x0
	csrrwi x0,  0xB89, 0x0a

	# mhpmcounterh10
	csrrci x5,  0xB8A, 0x0a
	csrrc  x5,  0xB8A, x0
	csrrc  x0,  0xB8A, x5
	csrrci x5,  0xB8A, 0x0a
	csrrs  x0,  0xB8A, x5
 	csrrsi x0,  0xB8A, 0x0a
 	csrrw  x0,  0xB8A, x0
	csrrwi x0,  0xB8A, 0x0a

	# mhpmcounterh11
	csrrci x5,  0xB8B, 0x0a
	csrrc  x5,  0xB8B, x0
	csrrc  x0,  0xB8B, x5
	csrrci x5,  0xB8B, 0x0a
	csrrs  x0,  0xB8B, x5
 	csrrsi x0,  0xB8B, 0x0a
 	csrrw  x0,  0xB8B, x0
	csrrwi x0,  0xB8B, 0x0a

	# mhpmcounterh12
	csrrci x5,  0xB8C, 0x0a
	csrrc  x5,  0xB8C, x0
	csrrc  x0,  0xB8C, x5
	csrrci x5,  0xB8C, 0x0a
	csrrs  x0,  0xB8C, x5
 	csrrsi x0,  0xB8C, 0x0a
 	csrrw  x0,  0xB8C, x0
	csrrwi x0,  0xB8C, 0x0a

	# mhpmcounterh13
	csrrci x5,  0xB8D, 0x0a
	csrrc  x5,  0xB8D, x0
	csrrc  x0,  0xB8D, x5
	csrrci x5,  0xB8D, 0x0a
	csrrs  x0,  0xB8D, x5
 	csrrsi x0,  0xB8D, 0x0a
 	csrrw  x0,  0xB8D, x0
	csrrwi x0,  0xB8D, 0x0a

	# mhpmcounterh14
	csrrci x5,  0xB8E, 0x0a
	csrrc  x5,  0xB8E, x0
	csrrc  x0,  0xB8E, x5
	csrrci x5,  0xB8E, 0x0a
	csrrs  x0,  0xB8E, x5
 	csrrsi x0,  0xB8E, 0x0a
 	csrrw  x0,  0xB8E, x0
	csrrwi x0,  0xB8E, 0x0a

	# mhpmcounterh15
	csrrci x5,  0xB8F, 0x0a
	csrrc  x5,  0xB8F, x0
	csrrc  x0,  0xB8F, x5
	csrrci x5,  0xB8F, 0x0a
	csrrs  x0,  0xB8F, x5
 	csrrsi x0,  0xB8F, 0x0a
 	csrrw  x0,  0xB8F, x0
	csrrwi x0,  0xB8F, 0x0a

	# mhpmcounterh16
	csrrci x5,  0xB90, 0x0a
	csrrc  x5,  0xB90, x0
	csrrc  x0,  0xB90, x5
	csrrci x5,  0xB90, 0x0a
	csrrs  x0,  0xB90, x5
 	csrrsi x0,  0xB90, 0x0a
 	csrrw  x0,  0xB90, x0
	csrrwi x0,  0xB90, 0x0a

	# mhpmcounterh17
	csrrci x5,  0xB91, 0x0a
	csrrc  x5,  0xB91, x0
	csrrc  x0,  0xB91, x5
	csrrci x5,  0xB91, 0x0a
	csrrs  x0,  0xB91, x5
 	csrrsi x0,  0xB91, 0x0a
 	csrrw  x0,  0xB91, x0
	csrrwi x0,  0xB91, 0x0a

	# mhpmcounterh18
	csrrci x5,  0xB92, 0x0a
	csrrc  x5,  0xB92, x0
	csrrc  x0,  0xB92, x5
	csrrci x5,  0xB92, 0x0a
	csrrs  x0,  0xB92, x5
 	csrrsi x0,  0xB92, 0x0a
 	csrrw  x0,  0xB92, x0
	csrrwi x0,  0xB92, 0x0a

	# mhpmcounterh19
	csrrci x5,  0xB93, 0x0a
	csrrc  x5,  0xB93, x0
	csrrc  x0,  0xB93, x5
	csrrci x5,  0xB93, 0x0a
	csrrs  x0,  0xB93, x5
 	csrrsi x0,  0xB93, 0x0a
 	csrrw  x0,  0xB93, x0
	csrrwi x0,  0xB93, 0x0a

	# mhpmcounterh20
	csrrci x5,  0xB94, 0x0a
	csrrc  x5,  0xB94, x0
	csrrc  x0,  0xB94, x5
	csrrci x5,  0xB94, 0x0a
	csrrs  x0,  0xB94, x5
 	csrrsi x0,  0xB94, 0x0a
 	csrrw  x0,  0xB94, x0
	csrrwi x0,  0xB94, 0x0a

	# mhpmcounterh21
	csrrci x5,  0xB95, 0x0a
	csrrc  x5,  0xB95, x0
	csrrc  x0,  0xB95, x5
	csrrci x5,  0xB95, 0x0a
	csrrs  x0,  0xB95, x5
 	csrrsi x0,  0xB95, 0x0a
 	csrrw  x0,  0xB95, x0
	csrrwi x0,  0xB95, 0x0a

	# mhpmcounterh22
	csrrci x5,  0xB96, 0x0a
	csrrc  x5,  0xB96, x0
	csrrc  x0,  0xB96, x5
	csrrci x5,  0xB96, 0x0a
	csrrs  x0,  0xB96, x5
 	csrrsi x0,  0xB96, 0x0a
 	csrrw  x0,  0xB96, x0
	csrrwi x0,  0xB96, 0x0a

	# mhpmcounterh23
	csrrci x5,  0xB97, 0x0a
	csrrc  x5,  0xB97, x0
	csrrc  x0,  0xB97, x5
	csrrci x5,  0xB97, 0x0a
	csrrs  x0,  0xB97, x5
 	csrrsi x0,  0xB97, 0x0a
 	csrrw  x0,  0xB97, x0
	csrrwi x0,  0xB97, 0x0a

	# mhpmcounterh24
	csrrci x5,  0xB98, 0x0a
	csrrc  x5,  0xB98, x0
	csrrc  x0,  0xB98, x5
	csrrci x5,  0xB98, 0x0a
	csrrs  x0,  0xB98, x5
 	csrrsi x0,  0xB98, 0x0a
 	csrrw  x0,  0xB98, x0
	csrrwi x0,  0xB98, 0x0a

	# mhpmcounterh25
	csrrci x5,  0xB99, 0x0a
	csrrc  x5,  0xB99, x0
	csrrc  x0,  0xB99, x5
	csrrci x5,  0xB99, 0x0a
	csrrs  x0,  0xB99, x5
 	csrrsi x0,  0xB99, 0x0a
 	csrrw  x0,  0xB99, x0
	csrrwi x0,  0xB99, 0x0a

	# mhpmcounterh26
	csrrci x5,  0xB9A, 0x0a
	csrrc  x5,  0xB9A, x0
	csrrc  x0,  0xB9A, x5
	csrrci x5,  0xB9A, 0x0a
	csrrs  x0,  0xB9A, x5
 	csrrsi x0,  0xB9A, 0x0a
 	csrrw  x0,  0xB9A, x0
	csrrwi x0,  0xB9A, 0x0a

	# mhpmcounterh27
	csrrci x5,  0xB9B, 0x0a
	csrrc  x5,  0xB9B, x0
	csrrc  x0,  0xB9B, x5
	csrrci x5,  0xB9B, 0x0a
	csrrs  x0,  0xB9B, x5
 	csrrsi x0,  0xB9B, 0x0a
 	csrrw  x0,  0xB9B, x0
	csrrwi x0,  0xB9B, 0x0a

	# mhpmcounterh28
	csrrci x5,  0xB9C, 0x0a
	csrrc  x5,  0xB9C, x0
	csrrc  x0,  0xB9C, x5
	csrrci x5,  0xB9C, 0x0a
	csrrs  x0,  0xB9C, x5
 	csrrsi x0,  0xB9C, 0x0a
 	csrrw  x0,  0xB9C, x0
	csrrwi x0,  0xB9C, 0x0a

	# mhpmcounterh29
	csrrci x5,  0xB9D, 0x0a
	csrrc  x5,  0xB9D, x0
	csrrc  x0,  0xB9D, x5
	csrrci x5,  0xB9D, 0x0a
	csrrs  x0,  0xB9D, x5
 	csrrsi x0,  0xB9D, 0x0a
 	csrrw  x0,  0xB9D, x0
	csrrwi x0,  0xB9D, 0x0a

	# mhpmcounterh30
	csrrci x5,  0xB9E, 0x0a
	csrrc  x5,  0xB9E, x0
	csrrc  x0,  0xB9E, x5
	csrrci x5,  0xB9E, 0x0a
	csrrs  x0,  0xB9E, x5
 	csrrsi x0,  0xB9E, 0x0a
 	csrrw  x0,  0xB9E, x0
	csrrwi x0,  0xB9E, 0x0a

	# mhpmcounterh31
	csrrci x5,  0xB9F, 0x0a
	csrrc  x5,  0xB9F, x0
	csrrc  x0,  0xB9F, x5
	csrrci x5,  0xB9F, 0x0a
	csrrs  x0,  0xB9F, x5
 	csrrsi x0,  0xB9F, 0x0a
 	csrrw  x0,  0xB9F, x0
	csrrwi x0,  0xB9F, 0x0a

###############################################################################
# Access a few other CSRs, including accesses that throw illegal instruction
# exceptions.

	# mvendorid
	csrrc  x5,  3857, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  3857, x5     # illegal instruction: attempt to write RO CSR
	csrrci x5,  3857, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  3857, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  3857, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  3857, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  3857, 0x0a   # illegal instruction: attempt to write RO CSR

	csrrc  x5,  3857, x0     # not illegal
	li     x30, 0x00000602
	bne    x5,  x30, fail

	# marchid
	csrrc  x5,  3858, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  3858, x5     # illegal instruction: attempt to write RO CSR
	csrrci x0,  3858, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  3858, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  3858, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  3858, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  3858, 0x0a   # illegal instruction: attempt to write RO CSR

	csrrc  x5,  3858, x0     # not illegal
	li     x30, 0x00000014
	bne    x5,  x30, fail

	# mipmid
	csrrc  x5,  3859, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  3859, x5     # illegal instruction: attempt to write RO CSR
	csrrci x0,  3859, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  3859, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  3859, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  3859, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  3859, 0x0a   # illegal instruction: attempt to write RO CSR

	csrrc  x5,  3859, x0     # not illegal
	li     x30, 0x00000000
	bne    x5,  x30, fail

	# mhartid
	csrrc  x5,  3860, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  3860, x5     # illegal instruction: attempt to write RO CSR
	csrrci x0,  3860, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  3860, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  3860, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  3860, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  3860, 0x0a   # illegal instruction: attempt to write RO CSR

	csrrc  x5,  3860, x0     # not illegal
	li     x30, 0x00000000
	bne    x5,  x30, fail

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
csr_fail:
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
