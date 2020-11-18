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
# MHPMCOUNTERS29: access testcase for mhpmcounter3..31 CSRs in cv32e40p.
#     Notes:
#       1. This test requires NUM_MHPMCOUNTERS set to 29.
#       2. Does not test function - just access.
#       3. Cannot run with the ISS.
###############################################################################
.include "user_define.h"
.section .text.start
.globl _start
.section .text
#.include "user_init.s"
.type _start, @function

_start:
    j _start_main

.globl _start_main
.section .text
_start_main:

	#ifdef NO_PULP
	#define EXP_MISA 0x40001104
	#else
	#define EXP_MISA 0x40801104
	#endif


###############################################################################
# Script generated code to verify write/read access of these CSRs.
#start
	# mhpmevent3
	li x12, 0xa5a5a5a5
	csrrw x14, 803, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 803, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0x5599ca67
	csrrw x14, 803, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 803, x12
	li x12, 0x0000ca67
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 803, x12
	li x12, 0x0000efe7
	bne x12, x14, csr_fail
	li x12, 0x943b6954
	csrrs x14, 803, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 803, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 803, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0x7c4c5d22
	csrrc x14, 803, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 803, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 803, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 803, 0b01010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 803, 0b00101
	li x12, 0x0000000a
	bne x12, x14, csr_fail
	csrrsi x14, 803, 0b11010
	li x12, 0x0000000f
	bne x12, x14, csr_fail
	csrrsi x14, 803, 0b11100
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 803, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 803, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 803, 0b10110
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent4
	li x12, 0xa5a5a5a5
	csrrw x14, 804, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 804, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0x192b5afa
	csrrw x14, 804, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 804, x12
	li x12, 0x00005afa
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 804, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x86015c6d
	csrrs x14, 804, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 804, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 804, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0x029db46e
	csrrc x14, 804, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 804, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 804, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 804, 0b10111
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 804, 0b00101
	li x12, 0x00000017
	bne x12, x14, csr_fail
	csrrsi x14, 804, 0b11010
	li x12, 0x00000017
	bne x12, x14, csr_fail
	csrrsi x14, 804, 0b11000
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 804, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 804, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 804, 0b10111
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent5
	li x12, 0xa5a5a5a5
	csrrw x14, 805, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 805, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0xe3ab797d
	csrrw x14, 805, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 805, x12
	li x12, 0x0000797d
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 805, x12
	li x12, 0x0000fdfd
	bne x12, x14, csr_fail
	li x12, 0x3d002294
	csrrs x14, 805, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 805, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 805, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0x1e882616
	csrrc x14, 805, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 805, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 805, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 805, 0b00001
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 805, 0b00101
	li x12, 0x00000001
	bne x12, x14, csr_fail
	csrrsi x14, 805, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrsi x14, 805, 0b10111
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 805, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 805, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 805, 0b01001
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent6
	li x12, 0xa5a5a5a5
	csrrw x14, 806, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 806, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0xbbaff885
	csrrw x14, 806, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 806, x12
	li x12, 0x0000f885
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 806, x12
	li x12, 0x0000fda5
	bne x12, x14, csr_fail
	li x12, 0x3c6f2d52
	csrrs x14, 806, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 806, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 806, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0x809d900c
	csrrc x14, 806, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 806, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 806, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 806, 0b11001
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 806, 0b00101
	li x12, 0x00000019
	bne x12, x14, csr_fail
	csrrsi x14, 806, 0b11010
	li x12, 0x0000001d
	bne x12, x14, csr_fail
	csrrsi x14, 806, 0b11001
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 806, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 806, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 806, 0b11101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent7
	li x12, 0xa5a5a5a5
	csrrw x14, 807, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 807, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0xf550d5ab
	csrrw x14, 807, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 807, x12
	li x12, 0x0000d5ab
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 807, x12
	li x12, 0x0000f5af
	bne x12, x14, csr_fail
	li x12, 0xe62f0e49
	csrrs x14, 807, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 807, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 807, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0x5f55ce76
	csrrc x14, 807, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 807, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 807, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 807, 0b00100
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 807, 0b00101
	li x12, 0x00000004
	bne x12, x14, csr_fail
	csrrsi x14, 807, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrsi x14, 807, 0b11001
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 807, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 807, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 807, 0b11100
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent8
	li x12, 0xa5a5a5a5
	csrrw x14, 808, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 808, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0x36cd731a
	csrrw x14, 808, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 808, x12
	li x12, 0x0000731a
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 808, x12
	li x12, 0x0000f7bf
	bne x12, x14, csr_fail
	li x12, 0x578155b4
	csrrs x14, 808, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 808, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 808, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0x21794a9c
	csrrc x14, 808, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 808, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 808, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 808, 0b11011
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 808, 0b00101
	li x12, 0x0000001b
	bne x12, x14, csr_fail
	csrrsi x14, 808, 0b11010
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrsi x14, 808, 0b10000
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 808, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 808, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 808, 0b11011
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent9
	li x12, 0xa5a5a5a5
	csrrw x14, 809, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 809, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0x4df46846
	csrrw x14, 809, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 809, x12
	li x12, 0x00006846
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 809, x12
	li x12, 0x0000ede7
	bne x12, x14, csr_fail
	li x12, 0x46e6d02b
	csrrs x14, 809, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 809, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 809, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xb07c4e41
	csrrc x14, 809, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 809, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 809, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 809, 0b00100
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 809, 0b00101
	li x12, 0x00000004
	bne x12, x14, csr_fail
	csrrsi x14, 809, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrsi x14, 809, 0b00011
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 809, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 809, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 809, 0b00100
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent10
	li x12, 0xa5a5a5a5
	csrrw x14, 810, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 810, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0x249666b3
	csrrw x14, 810, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 810, x12
	li x12, 0x000066b3
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 810, x12
	li x12, 0x0000e7b7
	bne x12, x14, csr_fail
	li x12, 0x5a36a091
	csrrs x14, 810, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 810, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 810, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xf26df110
	csrrc x14, 810, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 810, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 810, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 810, 0b11001
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 810, 0b00101
	li x12, 0x00000019
	bne x12, x14, csr_fail
	csrrsi x14, 810, 0b11010
	li x12, 0x0000001d
	bne x12, x14, csr_fail
	csrrsi x14, 810, 0b01100
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 810, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 810, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 810, 0b10011
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent11
	li x12, 0xa5a5a5a5
	csrrw x14, 811, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 811, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0xaf9407ee
	csrrw x14, 811, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 811, x12
	li x12, 0x000007ee
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 811, x12
	li x12, 0x0000a7ef
	bne x12, x14, csr_fail
	li x12, 0x9c1024e8
	csrrs x14, 811, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 811, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 811, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0x823a6c57
	csrrc x14, 811, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 811, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 811, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 811, 0b01000
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 811, 0b00101
	li x12, 0x00000008
	bne x12, x14, csr_fail
	csrrsi x14, 811, 0b11010
	li x12, 0x0000000d
	bne x12, x14, csr_fail
	csrrsi x14, 811, 0b10100
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 811, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 811, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 811, 0b11010
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent12
	li x12, 0xa5a5a5a5
	csrrw x14, 812, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 812, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0xb3cd262d
	csrrw x14, 812, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 812, x12
	li x12, 0x0000262d
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 812, x12
	li x12, 0x0000a7ad
	bne x12, x14, csr_fail
	li x12, 0xd44e7e03
	csrrs x14, 812, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 812, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 812, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xfe9717de
	csrrc x14, 812, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 812, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 812, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 812, 0b10111
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 812, 0b00101
	li x12, 0x00000017
	bne x12, x14, csr_fail
	csrrsi x14, 812, 0b11010
	li x12, 0x00000017
	bne x12, x14, csr_fail
	csrrsi x14, 812, 0b01101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 812, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 812, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 812, 0b11011
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent13
	li x12, 0xa5a5a5a5
	csrrw x14, 813, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 813, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0xeb86004c
	csrrw x14, 813, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 813, x12
	li x12, 0x0000004c
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 813, x12
	li x12, 0x0000a5ed
	bne x12, x14, csr_fail
	li x12, 0x8f03af04
	csrrs x14, 813, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 813, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 813, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xd665472c
	csrrc x14, 813, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 813, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 813, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 813, 0b01000
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 813, 0b00101
	li x12, 0x00000008
	bne x12, x14, csr_fail
	csrrsi x14, 813, 0b11010
	li x12, 0x0000000d
	bne x12, x14, csr_fail
	csrrsi x14, 813, 0b00000
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 813, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 813, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 813, 0b00000
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent14
	li x12, 0xa5a5a5a5
	csrrw x14, 814, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 814, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0xc25aaf9d
	csrrw x14, 814, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 814, x12
	li x12, 0x0000af9d
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 814, x12
	li x12, 0x0000afbd
	bne x12, x14, csr_fail
	li x12, 0x6232f2cf
	csrrs x14, 814, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 814, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 814, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xab4c8b27
	csrrc x14, 814, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 814, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 814, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 814, 0b00111
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 814, 0b00101
	li x12, 0x00000007
	bne x12, x14, csr_fail
	csrrsi x14, 814, 0b11010
	li x12, 0x00000007
	bne x12, x14, csr_fail
	csrrsi x14, 814, 0b10001
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 814, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 814, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 814, 0b00100
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent15
	li x12, 0xa5a5a5a5
	csrrw x14, 815, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 815, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0xfc450eb6
	csrrw x14, 815, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 815, x12
	li x12, 0x00000eb6
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 815, x12
	li x12, 0x0000afb7
	bne x12, x14, csr_fail
	li x12, 0xdf21d66b
	csrrs x14, 815, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 815, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 815, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0x5d877b70
	csrrc x14, 815, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 815, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 815, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 815, 0b01111
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 815, 0b00101
	li x12, 0x0000000f
	bne x12, x14, csr_fail
	csrrsi x14, 815, 0b11010
	li x12, 0x0000000f
	bne x12, x14, csr_fail
	csrrsi x14, 815, 0b11010
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 815, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 815, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 815, 0b01001
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent16
	li x12, 0xa5a5a5a5
	csrrw x14, 816, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 816, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0x60c43ac1
	csrrw x14, 816, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 816, x12
	li x12, 0x00003ac1
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 816, x12
	li x12, 0x0000bfe5
	bne x12, x14, csr_fail
	li x12, 0xa353dd27
	csrrs x14, 816, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 816, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 816, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0x25d46c45
	csrrc x14, 816, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 816, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 816, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 816, 0b01010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 816, 0b00101
	li x12, 0x0000000a
	bne x12, x14, csr_fail
	csrrsi x14, 816, 0b11010
	li x12, 0x0000000f
	bne x12, x14, csr_fail
	csrrsi x14, 816, 0b00010
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 816, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 816, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 816, 0b00010
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent17
	li x12, 0xa5a5a5a5
	csrrw x14, 817, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 817, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0x6d77c506
	csrrw x14, 817, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 817, x12
	li x12, 0x0000c506
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 817, x12
	li x12, 0x0000e5a7
	bne x12, x14, csr_fail
	li x12, 0x615f4a97
	csrrs x14, 817, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 817, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 817, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xaba4a7c0
	csrrc x14, 817, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 817, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 817, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 817, 0b11101
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 817, 0b00101
	li x12, 0x0000001d
	bne x12, x14, csr_fail
	csrrsi x14, 817, 0b11010
	li x12, 0x0000001d
	bne x12, x14, csr_fail
	csrrsi x14, 817, 0b10110
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 817, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 817, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 817, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent18
	li x12, 0xa5a5a5a5
	csrrw x14, 818, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 818, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0xa006a626
	csrrw x14, 818, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 818, x12
	li x12, 0x0000a626
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 818, x12
	li x12, 0x0000a7a7
	bne x12, x14, csr_fail
	li x12, 0x4a2ebbef
	csrrs x14, 818, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 818, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 818, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa4d3b6b3
	csrrc x14, 818, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 818, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 818, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 818, 0b00100
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 818, 0b00101
	li x12, 0x00000004
	bne x12, x14, csr_fail
	csrrsi x14, 818, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrsi x14, 818, 0b01011
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 818, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 818, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 818, 0b00010
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent19
	li x12, 0xa5a5a5a5
	csrrw x14, 819, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 819, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0x2db1490a
	csrrw x14, 819, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 819, x12
	li x12, 0x0000490a
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 819, x12
	li x12, 0x0000edaf
	bne x12, x14, csr_fail
	li x12, 0x48747d08
	csrrs x14, 819, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 819, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 819, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa0f18bd1
	csrrc x14, 819, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 819, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 819, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 819, 0b11111
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 819, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrsi x14, 819, 0b11010
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrsi x14, 819, 0b11110
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 819, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 819, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 819, 0b00011
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent20
	li x12, 0xa5a5a5a5
	csrrw x14, 820, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 820, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0xd9df844d
	csrrw x14, 820, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 820, x12
	li x12, 0x0000844d
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 820, x12
	li x12, 0x0000a5ed
	bne x12, x14, csr_fail
	li x12, 0xde339ea9
	csrrs x14, 820, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 820, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 820, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa6382e89
	csrrc x14, 820, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 820, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 820, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 820, 0b01101
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 820, 0b00101
	li x12, 0x0000000d
	bne x12, x14, csr_fail
	csrrsi x14, 820, 0b11010
	li x12, 0x0000000d
	bne x12, x14, csr_fail
	csrrsi x14, 820, 0b10111
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 820, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 820, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 820, 0b01001
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent21
	li x12, 0xa5a5a5a5
	csrrw x14, 821, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 821, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0x8a23cad8
	csrrw x14, 821, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 821, x12
	li x12, 0x0000cad8
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 821, x12
	li x12, 0x0000effd
	bne x12, x14, csr_fail
	li x12, 0xe23ee27b
	csrrs x14, 821, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 821, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 821, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xce9f2bb9
	csrrc x14, 821, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 821, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 821, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 821, 0b11101
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 821, 0b00101
	li x12, 0x0000001d
	bne x12, x14, csr_fail
	csrrsi x14, 821, 0b11010
	li x12, 0x0000001d
	bne x12, x14, csr_fail
	csrrsi x14, 821, 0b01000
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 821, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 821, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 821, 0b11000
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent22
	li x12, 0xa5a5a5a5
	csrrw x14, 822, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 822, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0x7942fd02
	csrrw x14, 822, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 822, x12
	li x12, 0x0000fd02
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 822, x12
	li x12, 0x0000fda7
	bne x12, x14, csr_fail
	li x12, 0x67a9e836
	csrrs x14, 822, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 822, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 822, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xbd53627f
	csrrc x14, 822, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 822, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 822, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 822, 0b00101
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 822, 0b00101
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrsi x14, 822, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrsi x14, 822, 0b01010
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 822, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 822, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 822, 0b10011
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent23
	li x12, 0xa5a5a5a5
	csrrw x14, 823, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 823, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0x297f98b8
	csrrw x14, 823, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 823, x12
	li x12, 0x000098b8
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 823, x12
	li x12, 0x0000bdbd
	bne x12, x14, csr_fail
	li x12, 0x122088b3
	csrrs x14, 823, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 823, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 823, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0x848ec6e4
	csrrc x14, 823, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 823, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 823, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 823, 0b00110
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 823, 0b00101
	li x12, 0x00000006
	bne x12, x14, csr_fail
	csrrsi x14, 823, 0b11010
	li x12, 0x00000007
	bne x12, x14, csr_fail
	csrrsi x14, 823, 0b01111
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 823, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 823, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 823, 0b10011
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent24
	li x12, 0xa5a5a5a5
	csrrw x14, 824, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 824, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0xf48c6acd
	csrrw x14, 824, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 824, x12
	li x12, 0x00006acd
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 824, x12
	li x12, 0x0000efed
	bne x12, x14, csr_fail
	li x12, 0x32d05494
	csrrs x14, 824, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 824, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 824, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xbc98c71d
	csrrc x14, 824, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 824, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 824, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 824, 0b10111
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 824, 0b00101
	li x12, 0x00000017
	bne x12, x14, csr_fail
	csrrsi x14, 824, 0b11010
	li x12, 0x00000017
	bne x12, x14, csr_fail
	csrrsi x14, 824, 0b00110
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 824, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 824, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 824, 0b00100
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent25
	li x12, 0xa5a5a5a5
	csrrw x14, 825, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 825, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0x5f668177
	csrrw x14, 825, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 825, x12
	li x12, 0x00008177
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 825, x12
	li x12, 0x0000a5f7
	bne x12, x14, csr_fail
	li x12, 0x73970670
	csrrs x14, 825, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 825, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 825, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa1adae60
	csrrc x14, 825, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 825, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 825, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 825, 0b01001
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 825, 0b00101
	li x12, 0x00000009
	bne x12, x14, csr_fail
	csrrsi x14, 825, 0b11010
	li x12, 0x0000000d
	bne x12, x14, csr_fail
	csrrsi x14, 825, 0b01001
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 825, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 825, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 825, 0b10101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent26
	li x12, 0xa5a5a5a5
	csrrw x14, 826, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 826, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0xd6668cc8
	csrrw x14, 826, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 826, x12
	li x12, 0x00008cc8
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 826, x12
	li x12, 0x0000aded
	bne x12, x14, csr_fail
	li x12, 0xbd9ed990
	csrrs x14, 826, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 826, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 826, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xcedecfcd
	csrrc x14, 826, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 826, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 826, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 826, 0b11100
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 826, 0b00101
	li x12, 0x0000001c
	bne x12, x14, csr_fail
	csrrsi x14, 826, 0b11010
	li x12, 0x0000001d
	bne x12, x14, csr_fail
	csrrsi x14, 826, 0b11100
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 826, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 826, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 826, 0b10001
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent27
	li x12, 0xa5a5a5a5
	csrrw x14, 827, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 827, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0xa425e498
	csrrw x14, 827, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 827, x12
	li x12, 0x0000e498
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 827, x12
	li x12, 0x0000e5bd
	bne x12, x14, csr_fail
	li x12, 0x3556abe1
	csrrs x14, 827, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 827, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 827, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xbf4d3dd4
	csrrc x14, 827, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 827, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 827, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 827, 0b01000
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 827, 0b00101
	li x12, 0x00000008
	bne x12, x14, csr_fail
	csrrsi x14, 827, 0b11010
	li x12, 0x0000000d
	bne x12, x14, csr_fail
	csrrsi x14, 827, 0b10111
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 827, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 827, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 827, 0b10111
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent28
	li x12, 0xa5a5a5a5
	csrrw x14, 828, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 828, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0x356e8358
	csrrw x14, 828, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 828, x12
	li x12, 0x00008358
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 828, x12
	li x12, 0x0000a7fd
	bne x12, x14, csr_fail
	li x12, 0x60d5d1c4
	csrrs x14, 828, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 828, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 828, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0x3f6d5395
	csrrc x14, 828, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 828, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 828, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 828, 0b00101
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 828, 0b00101
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrsi x14, 828, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrsi x14, 828, 0b01110
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 828, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 828, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 828, 0b11101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent29
	li x12, 0xa5a5a5a5
	csrrw x14, 829, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 829, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0x5f596028
	csrrw x14, 829, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 829, x12
	li x12, 0x00006028
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 829, x12
	li x12, 0x0000e5ad
	bne x12, x14, csr_fail
	li x12, 0x61430933
	csrrs x14, 829, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 829, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 829, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0x6717a138
	csrrc x14, 829, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 829, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 829, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 829, 0b01100
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 829, 0b00101
	li x12, 0x0000000c
	bne x12, x14, csr_fail
	csrrsi x14, 829, 0b11010
	li x12, 0x0000000d
	bne x12, x14, csr_fail
	csrrsi x14, 829, 0b11100
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 829, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 829, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 829, 0b11110
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent30
	li x12, 0xa5a5a5a5
	csrrw x14, 830, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 830, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0x28c0c58e
	csrrw x14, 830, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 830, x12
	li x12, 0x0000c58e
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 830, x12
	li x12, 0x0000e5af
	bne x12, x14, csr_fail
	li x12, 0x32370e52
	csrrs x14, 830, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 830, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 830, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0x8d540cb7
	csrrc x14, 830, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 830, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 830, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 830, 0b11111
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 830, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrsi x14, 830, 0b11010
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrsi x14, 830, 0b10111
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 830, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 830, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 830, 0b00010
	li x12, 0x00000000
	bne x12, x14, csr_fail
	# mhpmevent31
	li x12, 0xa5a5a5a5
	csrrw x14, 831, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x14, 831, x12
	li x12, 0x0000a5a5
	bne x12, x14, csr_fail
	li x12, 0xfb37c936
	csrrw x14, 831, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x14, 831, x12
	li x12, 0x0000c936
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x14, 831, x12
	li x12, 0x0000edb7
	bne x12, x14, csr_fail
	li x12, 0x8e300970
	csrrs x14, 831, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x14, 831, x12
	li x12, 0x0000ffff
	bne x12, x14, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x14, 831, x12
	li x12, 0x00005a5a
	bne x12, x14, csr_fail
	li x12, 0x6056a394
	csrrc x14, 831, x12
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 831, 0b00101
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrrwi x14, 831, 0b11010
	li x12, 0x00000005
	bne x12, x14, csr_fail
	csrrwi x14, 831, 0b01000
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrsi x14, 831, 0b00101
	li x12, 0x00000008
	bne x12, x14, csr_fail
	csrrsi x14, 831, 0b11010
	li x12, 0x0000000d
	bne x12, x14, csr_fail
	csrrsi x14, 831, 0b11111
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 831, 0b00101
	li x12, 0x0000001f
	bne x12, x14, csr_fail
	csrrci x14, 831, 0b11010
	li x12, 0x0000001a
	bne x12, x14, csr_fail
	csrrci x14, 831, 0b00000
	li x12, 0x00000000
	bne x12, x14, csr_fail
	csrr x14, 831
	li x12, 0x00000000
	bne x12, x14, csr_fail
#end

################################################################################
#
# Generated code ends...
#
################################################################################
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
