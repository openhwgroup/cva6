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
###############################################################################
	# mhpmcounter3
	li x13, 0xa5a5a5a5
	csrrw x11, 2819, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2819, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x58d817e6
	csrrw x11, 2819, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2819, x13
	li x13, 0x58d817e6
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2819, x13
	li x13, 0xfdfdb7e7
	bne x13, x11, csr_fail
	li x13, 0x11b4174c
	csrrs x11, 2819, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2819, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2819, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x60f899eb
	csrrc x11, 2819, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2819, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2819, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2819, 0b01110
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2819, 0b00101
	li x13, 0x0000000e
	bne x13, x11, csr_fail
	csrrsi x11, 2819, 0b11010
	li x13, 0x0000000f
	bne x13, x11, csr_fail
	csrrsi x11, 2819, 0b10011
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2819, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2819, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2819, 0b10101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter4
	li x13, 0xa5a5a5a5
	csrrw x11, 2820, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2820, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0xd62407a2
	csrrw x11, 2820, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2820, x13
	li x13, 0xd62407a2
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2820, x13
	li x13, 0xf7a5a7a7
	bne x13, x11, csr_fail
	li x13, 0xaf7d9050
	csrrs x11, 2820, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2820, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2820, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xab8b9bbc
	csrrc x11, 2820, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2820, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2820, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2820, 0b11111
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2820, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrsi x11, 2820, 0b11010
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrsi x11, 2820, 0b01101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2820, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2820, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2820, 0b01111
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter5
	li x13, 0xa5a5a5a5
	csrrw x11, 2821, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2821, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x233a825d
	csrrw x11, 2821, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2821, x13
	li x13, 0x233a825d
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2821, x13
	li x13, 0xa7bfa7fd
	bne x13, x11, csr_fail
	li x13, 0x7e568133
	csrrs x11, 2821, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2821, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2821, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x6edf1ab9
	csrrc x11, 2821, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2821, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2821, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2821, 0b11000
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2821, 0b00101
	li x13, 0x00000018
	bne x13, x11, csr_fail
	csrrsi x11, 2821, 0b11010
	li x13, 0x0000001d
	bne x13, x11, csr_fail
	csrrsi x11, 2821, 0b01001
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2821, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2821, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2821, 0b10110
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter6
	li x13, 0xa5a5a5a5
	csrrw x11, 2822, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2822, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0xc7a32aad
	csrrw x11, 2822, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2822, x13
	li x13, 0xc7a32aad
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2822, x13
	li x13, 0xe7a7afad
	bne x13, x11, csr_fail
	li x13, 0x9ace7026
	csrrs x11, 2822, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2822, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2822, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xc92bf27a
	csrrc x11, 2822, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2822, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2822, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2822, 0b01010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2822, 0b00101
	li x13, 0x0000000a
	bne x13, x11, csr_fail
	csrrsi x11, 2822, 0b11010
	li x13, 0x0000000f
	bne x13, x11, csr_fail
	csrrsi x11, 2822, 0b11011
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2822, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2822, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2822, 0b11011
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter7
	li x13, 0xa5a5a5a5
	csrrw x11, 2823, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2823, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x184a572d
	csrrw x11, 2823, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2823, x13
	li x13, 0x184a572d
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2823, x13
	li x13, 0xbdeff7ad
	bne x13, x11, csr_fail
	li x13, 0x85cfd036
	csrrs x11, 2823, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2823, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2823, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x86ac69a6
	csrrc x11, 2823, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2823, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2823, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2823, 0b10011
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2823, 0b00101
	li x13, 0x00000013
	bne x13, x11, csr_fail
	csrrsi x11, 2823, 0b11010
	li x13, 0x00000017
	bne x13, x11, csr_fail
	csrrsi x11, 2823, 0b10010
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2823, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2823, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2823, 0b01111
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter8
	li x13, 0xa5a5a5a5
	csrrw x11, 2824, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2824, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x9355a775
	csrrw x11, 2824, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2824, x13
	li x13, 0x9355a775
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2824, x13
	li x13, 0xb7f5a7f5
	bne x13, x11, csr_fail
	li x13, 0x9f6de57c
	csrrs x11, 2824, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2824, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2824, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x85ec8fd2
	csrrc x11, 2824, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2824, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2824, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2824, 0b01010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2824, 0b00101
	li x13, 0x0000000a
	bne x13, x11, csr_fail
	csrrsi x11, 2824, 0b11010
	li x13, 0x0000000f
	bne x13, x11, csr_fail
	csrrsi x11, 2824, 0b11000
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2824, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2824, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2824, 0b01000
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter9
	li x13, 0xa5a5a5a5
	csrrw x11, 2825, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2825, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0xb4a0230e
	csrrw x11, 2825, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2825, x13
	li x13, 0xb4a0230e
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2825, x13
	li x13, 0xb5a5a7af
	bne x13, x11, csr_fail
	li x13, 0x882e6ec1
	csrrs x11, 2825, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2825, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2825, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xb5886b83
	csrrc x11, 2825, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2825, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2825, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2825, 0b11101
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2825, 0b00101
	li x13, 0x0000001d
	bne x13, x11, csr_fail
	csrrsi x11, 2825, 0b11010
	li x13, 0x0000001d
	bne x13, x11, csr_fail
	csrrsi x11, 2825, 0b11110
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2825, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2825, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2825, 0b11000
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter10
	li x13, 0xa5a5a5a5
	csrrw x11, 2826, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2826, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0xeb5456ff
	csrrw x11, 2826, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2826, x13
	li x13, 0xeb5456ff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2826, x13
	li x13, 0xeff5f7ff
	bne x13, x11, csr_fail
	li x13, 0xbd1f6642
	csrrs x11, 2826, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2826, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2826, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xfa6e3d89
	csrrc x11, 2826, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2826, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2826, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2826, 0b01110
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2826, 0b00101
	li x13, 0x0000000e
	bne x13, x11, csr_fail
	csrrsi x11, 2826, 0b11010
	li x13, 0x0000000f
	bne x13, x11, csr_fail
	csrrsi x11, 2826, 0b00110
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2826, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2826, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2826, 0b11010
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter11
	li x13, 0xa5a5a5a5
	csrrw x11, 2827, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2827, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0xf07058c6
	csrrw x11, 2827, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2827, x13
	li x13, 0xf07058c6
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2827, x13
	li x13, 0xf5f5fde7
	bne x13, x11, csr_fail
	li x13, 0x35e3d846
	csrrs x11, 2827, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2827, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2827, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x8a77a20e
	csrrc x11, 2827, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2827, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2827, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2827, 0b00001
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2827, 0b00101
	li x13, 0x00000001
	bne x13, x11, csr_fail
	csrrsi x11, 2827, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrsi x11, 2827, 0b10110
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2827, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2827, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2827, 0b11101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter12
	li x13, 0xa5a5a5a5
	csrrw x11, 2828, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2828, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0xdbbe17ed
	csrrw x11, 2828, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2828, x13
	li x13, 0xdbbe17ed
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2828, x13
	li x13, 0xffbfb7ed
	bne x13, x11, csr_fail
	li x13, 0x6c87baac
	csrrs x11, 2828, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2828, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2828, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x8b90c327
	csrrc x11, 2828, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2828, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2828, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2828, 0b01111
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2828, 0b00101
	li x13, 0x0000000f
	bne x13, x11, csr_fail
	csrrsi x11, 2828, 0b11010
	li x13, 0x0000000f
	bne x13, x11, csr_fail
	csrrsi x11, 2828, 0b10100
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2828, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2828, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2828, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter13
	li x13, 0xa5a5a5a5
	csrrw x11, 2829, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2829, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x6e69c984
	csrrw x11, 2829, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2829, x13
	li x13, 0x6e69c984
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2829, x13
	li x13, 0xefededa5
	bne x13, x11, csr_fail
	li x13, 0x9285cadb
	csrrs x11, 2829, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2829, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2829, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x51afbfef
	csrrc x11, 2829, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2829, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2829, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2829, 0b00101
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2829, 0b00101
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrsi x11, 2829, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrsi x11, 2829, 0b01010
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2829, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2829, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2829, 0b11111
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter14
	li x13, 0xa5a5a5a5
	csrrw x11, 2830, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2830, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0xe045db3e
	csrrw x11, 2830, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2830, x13
	li x13, 0xe045db3e
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2830, x13
	li x13, 0xe5e5ffbf
	bne x13, x11, csr_fail
	li x13, 0xf14d1b59
	csrrs x11, 2830, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2830, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2830, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x44a8f6a6
	csrrc x11, 2830, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2830, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2830, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2830, 0b10010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2830, 0b00101
	li x13, 0x00000012
	bne x13, x11, csr_fail
	csrrsi x11, 2830, 0b11010
	li x13, 0x00000017
	bne x13, x11, csr_fail
	csrrsi x11, 2830, 0b01001
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2830, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2830, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2830, 0b01001
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter15
	li x13, 0xa5a5a5a5
	csrrw x11, 2831, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2831, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0xb6a578fb
	csrrw x11, 2831, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2831, x13
	li x13, 0xb6a578fb
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2831, x13
	li x13, 0xb7a5fdff
	bne x13, x11, csr_fail
	li x13, 0xc8c54afb
	csrrs x11, 2831, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2831, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2831, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x7198a93f
	csrrc x11, 2831, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2831, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2831, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2831, 0b11100
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2831, 0b00101
	li x13, 0x0000001c
	bne x13, x11, csr_fail
	csrrsi x11, 2831, 0b11010
	li x13, 0x0000001d
	bne x13, x11, csr_fail
	csrrsi x11, 2831, 0b00011
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2831, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2831, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2831, 0b01101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter16
	li x13, 0xa5a5a5a5
	csrrw x11, 2832, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2832, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0xf55fd3fa
	csrrw x11, 2832, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2832, x13
	li x13, 0xf55fd3fa
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2832, x13
	li x13, 0xf5fff7ff
	bne x13, x11, csr_fail
	li x13, 0xe2b12d78
	csrrs x11, 2832, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2832, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2832, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x7cb08e77
	csrrc x11, 2832, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2832, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2832, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2832, 0b01111
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2832, 0b00101
	li x13, 0x0000000f
	bne x13, x11, csr_fail
	csrrsi x11, 2832, 0b11010
	li x13, 0x0000000f
	bne x13, x11, csr_fail
	csrrsi x11, 2832, 0b11111
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2832, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2832, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2832, 0b01000
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter17
	li x13, 0xa5a5a5a5
	csrrw x11, 2833, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2833, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x0c51d700
	csrrw x11, 2833, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2833, x13
	li x13, 0x0c51d700
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2833, x13
	li x13, 0xadf5f7a5
	bne x13, x11, csr_fail
	li x13, 0x812bd85e
	csrrs x11, 2833, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2833, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2833, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xbc1cacdf
	csrrc x11, 2833, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2833, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2833, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2833, 0b11110
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2833, 0b00101
	li x13, 0x0000001e
	bne x13, x11, csr_fail
	csrrsi x11, 2833, 0b11010
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrsi x11, 2833, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2833, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2833, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2833, 0b10010
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter18
	li x13, 0xa5a5a5a5
	csrrw x11, 2834, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2834, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x27f2b3f5
	csrrw x11, 2834, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2834, x13
	li x13, 0x27f2b3f5
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2834, x13
	li x13, 0xa7f7b7f5
	bne x13, x11, csr_fail
	li x13, 0x50daa8a6
	csrrs x11, 2834, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2834, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2834, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xaed090af
	csrrc x11, 2834, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2834, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2834, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2834, 0b10101
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2834, 0b00101
	li x13, 0x00000015
	bne x13, x11, csr_fail
	csrrsi x11, 2834, 0b11010
	li x13, 0x00000015
	bne x13, x11, csr_fail
	csrrsi x11, 2834, 0b00001
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2834, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2834, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2834, 0b11010
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter19
	li x13, 0xa5a5a5a5
	csrrw x11, 2835, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2835, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0xbb9f11de
	csrrw x11, 2835, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2835, x13
	li x13, 0xbb9f11de
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2835, x13
	li x13, 0xbfbfb5ff
	bne x13, x11, csr_fail
	li x13, 0xb8b44a62
	csrrs x11, 2835, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2835, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2835, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x8cfc8f2d
	csrrc x11, 2835, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2835, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2835, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2835, 0b11111
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2835, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrsi x11, 2835, 0b11010
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrsi x11, 2835, 0b01001
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2835, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2835, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2835, 0b00000
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter20
	li x13, 0xa5a5a5a5
	csrrw x11, 2836, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2836, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x481e52b3
	csrrw x11, 2836, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2836, x13
	li x13, 0x481e52b3
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2836, x13
	li x13, 0xedbff7b7
	bne x13, x11, csr_fail
	li x13, 0x6a7ac135
	csrrs x11, 2836, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2836, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2836, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x27c10d05
	csrrc x11, 2836, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2836, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2836, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2836, 0b00110
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2836, 0b00101
	li x13, 0x00000006
	bne x13, x11, csr_fail
	csrrsi x11, 2836, 0b11010
	li x13, 0x00000007
	bne x13, x11, csr_fail
	csrrsi x11, 2836, 0b00110
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2836, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2836, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2836, 0b10111
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter21
	li x13, 0xa5a5a5a5
	csrrw x11, 2837, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2837, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x7429cf49
	csrrw x11, 2837, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2837, x13
	li x13, 0x7429cf49
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2837, x13
	li x13, 0xf5adefed
	bne x13, x11, csr_fail
	li x13, 0x9d4886ce
	csrrs x11, 2837, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2837, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2837, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x05ddcfef
	csrrc x11, 2837, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2837, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2837, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2837, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2837, 0b00101
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2837, 0b11010
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrsi x11, 2837, 0b00000
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2837, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2837, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2837, 0b00010
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter22
	li x13, 0xa5a5a5a5
	csrrw x11, 2838, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2838, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x9d16666a
	csrrw x11, 2838, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2838, x13
	li x13, 0x9d16666a
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2838, x13
	li x13, 0xbdb7e7ef
	bne x13, x11, csr_fail
	li x13, 0x142246a0
	csrrs x11, 2838, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2838, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2838, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x61cde58d
	csrrc x11, 2838, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2838, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2838, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2838, 0b00101
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2838, 0b00101
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrsi x11, 2838, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrsi x11, 2838, 0b11100
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2838, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2838, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2838, 0b11110
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter23
	li x13, 0xa5a5a5a5
	csrrw x11, 2839, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2839, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0xc7a95284
	csrrw x11, 2839, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2839, x13
	li x13, 0xc7a95284
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2839, x13
	li x13, 0xe7adf7a5
	bne x13, x11, csr_fail
	li x13, 0xa7e4b1fe
	csrrs x11, 2839, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2839, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2839, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xca65a5e3
	csrrc x11, 2839, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2839, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2839, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2839, 0b11000
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2839, 0b00101
	li x13, 0x00000018
	bne x13, x11, csr_fail
	csrrsi x11, 2839, 0b11010
	li x13, 0x0000001d
	bne x13, x11, csr_fail
	csrrsi x11, 2839, 0b10111
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2839, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2839, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2839, 0b01011
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter24
	li x13, 0xa5a5a5a5
	csrrw x11, 2840, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2840, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x448a9e22
	csrrw x11, 2840, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2840, x13
	li x13, 0x448a9e22
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2840, x13
	li x13, 0xe5afbfa7
	bne x13, x11, csr_fail
	li x13, 0xf4d3cb7f
	csrrs x11, 2840, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2840, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2840, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x24425424
	csrrc x11, 2840, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2840, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2840, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2840, 0b00010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2840, 0b00101
	li x13, 0x00000002
	bne x13, x11, csr_fail
	csrrsi x11, 2840, 0b11010
	li x13, 0x00000007
	bne x13, x11, csr_fail
	csrrsi x11, 2840, 0b11110
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2840, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2840, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2840, 0b00001
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter25
	li x13, 0xa5a5a5a5
	csrrw x11, 2841, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2841, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x9c79f6e9
	csrrw x11, 2841, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2841, x13
	li x13, 0x9c79f6e9
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2841, x13
	li x13, 0xbdfdf7ed
	bne x13, x11, csr_fail
	li x13, 0xd9dd54c2
	csrrs x11, 2841, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2841, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2841, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x2711d141
	csrrc x11, 2841, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2841, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2841, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2841, 0b00011
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2841, 0b00101
	li x13, 0x00000003
	bne x13, x11, csr_fail
	csrrsi x11, 2841, 0b11010
	li x13, 0x00000007
	bne x13, x11, csr_fail
	csrrsi x11, 2841, 0b01100
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2841, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2841, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2841, 0b11101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter26
	li x13, 0xa5a5a5a5
	csrrw x11, 2842, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2842, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x5443f6a3
	csrrw x11, 2842, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2842, x13
	li x13, 0x5443f6a3
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2842, x13
	li x13, 0xf5e7f7a7
	bne x13, x11, csr_fail
	li x13, 0x4a3510d1
	csrrs x11, 2842, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2842, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2842, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0x5a4d1518
	csrrc x11, 2842, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2842, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2842, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2842, 0b11111
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2842, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrsi x11, 2842, 0b11010
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrsi x11, 2842, 0b11110
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2842, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2842, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2842, 0b11011
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter27
	li x13, 0xa5a5a5a5
	csrrw x11, 2843, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2843, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x64d8b2de
	csrrw x11, 2843, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2843, x13
	li x13, 0x64d8b2de
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2843, x13
	li x13, 0xe5fdb7ff
	bne x13, x11, csr_fail
	li x13, 0x9ca8e026
	csrrs x11, 2843, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2843, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2843, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xeee2ae60
	csrrc x11, 2843, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2843, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2843, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2843, 0b10000
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2843, 0b00101
	li x13, 0x00000010
	bne x13, x11, csr_fail
	csrrsi x11, 2843, 0b11010
	li x13, 0x00000015
	bne x13, x11, csr_fail
	csrrsi x11, 2843, 0b01101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2843, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2843, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2843, 0b11111
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter28
	li x13, 0xa5a5a5a5
	csrrw x11, 2844, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2844, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x2e03ed20
	csrrw x11, 2844, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2844, x13
	li x13, 0x2e03ed20
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2844, x13
	li x13, 0xafa7eda5
	bne x13, x11, csr_fail
	li x13, 0x5fe9e959
	csrrs x11, 2844, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2844, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2844, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xf91e6877
	csrrc x11, 2844, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2844, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2844, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2844, 0b01000
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2844, 0b00101
	li x13, 0x00000008
	bne x13, x11, csr_fail
	csrrsi x11, 2844, 0b11010
	li x13, 0x0000000d
	bne x13, x11, csr_fail
	csrrsi x11, 2844, 0b10000
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2844, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2844, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2844, 0b01001
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter29
	li x13, 0xa5a5a5a5
	csrrw x11, 2845, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2845, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x499c9ef2
	csrrw x11, 2845, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2845, x13
	li x13, 0x499c9ef2
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2845, x13
	li x13, 0xedbdbff7
	bne x13, x11, csr_fail
	li x13, 0xb43b0f6f
	csrrs x11, 2845, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2845, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2845, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xe1c1be2d
	csrrc x11, 2845, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2845, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2845, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2845, 0b11110
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2845, 0b00101
	li x13, 0x0000001e
	bne x13, x11, csr_fail
	csrrsi x11, 2845, 0b11010
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrsi x11, 2845, 0b01110
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2845, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2845, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2845, 0b11010
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter30
	li x13, 0xa5a5a5a5
	csrrw x11, 2846, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2846, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x7427b2d4
	csrrw x11, 2846, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2846, x13
	li x13, 0x7427b2d4
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2846, x13
	li x13, 0xf5a7b7f5
	bne x13, x11, csr_fail
	li x13, 0xf6a36392
	csrrs x11, 2846, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2846, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2846, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xe0384721
	csrrc x11, 2846, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2846, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2846, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2846, 0b10101
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2846, 0b00101
	li x13, 0x00000015
	bne x13, x11, csr_fail
	csrrsi x11, 2846, 0b11010
	li x13, 0x00000015
	bne x13, x11, csr_fail
	csrrsi x11, 2846, 0b10010
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2846, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2846, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2846, 0b10001
	li x13, 0x00000000
	bne x13, x11, csr_fail
	# mhpmcounter31
	li x13, 0xa5a5a5a5
	csrrw x11, 2847, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x11, 2847, x13
	li x13, 0xa5a5a5a5
	bne x13, x11, csr_fail
	li x13, 0x99220c48
	csrrw x11, 2847, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x11, 2847, x13
	li x13, 0x99220c48
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x11, 2847, x13
	li x13, 0xbda7aded
	bne x13, x11, csr_fail
	li x13, 0x8ae5417c
	csrrs x11, 2847, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x11, 2847, x13
	li x13, 0xffffffff
	bne x13, x11, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x11, 2847, x13
	li x13, 0x5a5a5a5a
	bne x13, x11, csr_fail
	li x13, 0xfd516423
	csrrc x11, 2847, x13
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2847, 0b00101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrrwi x11, 2847, 0b11010
	li x13, 0x00000005
	bne x13, x11, csr_fail
	csrrwi x11, 2847, 0b11111
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrsi x11, 2847, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrsi x11, 2847, 0b11010
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrsi x11, 2847, 0b01011
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2847, 0b00101
	li x13, 0x0000001f
	bne x13, x11, csr_fail
	csrrci x11, 2847, 0b11010
	li x13, 0x0000001a
	bne x13, x11, csr_fail
	csrrci x11, 2847, 0b10101
	li x13, 0x00000000
	bne x13, x11, csr_fail
	csrr x11, 2847
	li x13, 0x00000000
	bne x13, x11, csr_fail
###############################################################################
	# mhpmcounterh3
	li x5, 0xa5a5a5a5
	csrrw x15, 2947, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2947, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x3eb0a869
	csrrw x15, 2947, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2947, x5
	li x5, 0x3eb0a869
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2947, x5
	li x5, 0xbfb5aded
	bne x5, x15, csr_fail
	li x5, 0x080bee67
	csrrs x15, 2947, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2947, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2947, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x31462855
	csrrc x15, 2947, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2947, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2947, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2947, 0b00001
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2947, 0b00101
	li x5, 0x00000001
	bne x5, x15, csr_fail
	csrrsi x15, 2947, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrsi x15, 2947, 0b11110
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2947, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2947, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2947, 0b00100
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh4
	li x5, 0xa5a5a5a5
	csrrw x15, 2948, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2948, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x4c90ee23
	csrrw x15, 2948, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2948, x5
	li x5, 0x4c90ee23
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2948, x5
	li x5, 0xedb5efa7
	bne x5, x15, csr_fail
	li x5, 0x502190eb
	csrrs x15, 2948, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2948, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2948, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x5b6fc098
	csrrc x15, 2948, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2948, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2948, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2948, 0b00011
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2948, 0b00101
	li x5, 0x00000003
	bne x5, x15, csr_fail
	csrrsi x15, 2948, 0b11010
	li x5, 0x00000007
	bne x5, x15, csr_fail
	csrrsi x15, 2948, 0b01011
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2948, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2948, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2948, 0b01111
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh5
	li x5, 0xa5a5a5a5
	csrrw x15, 2949, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2949, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x359322b3
	csrrw x15, 2949, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2949, x5
	li x5, 0x359322b3
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2949, x5
	li x5, 0xb5b7a7b7
	bne x5, x15, csr_fail
	li x5, 0x7f1393f5
	csrrs x15, 2949, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2949, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2949, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x6b55cf35
	csrrc x15, 2949, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2949, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2949, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2949, 0b01001
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2949, 0b00101
	li x5, 0x00000009
	bne x5, x15, csr_fail
	csrrsi x15, 2949, 0b11010
	li x5, 0x0000000d
	bne x5, x15, csr_fail
	csrrsi x15, 2949, 0b01010
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2949, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2949, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2949, 0b11010
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh6
	li x5, 0xa5a5a5a5
	csrrw x15, 2950, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2950, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x677f9bec
	csrrw x15, 2950, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2950, x5
	li x5, 0x677f9bec
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2950, x5
	li x5, 0xe7ffbfed
	bne x5, x15, csr_fail
	li x5, 0x85c1ef2f
	csrrs x15, 2950, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2950, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2950, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x37e60d36
	csrrc x15, 2950, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2950, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2950, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2950, 0b11011
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2950, 0b00101
	li x5, 0x0000001b
	bne x5, x15, csr_fail
	csrrsi x15, 2950, 0b11010
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrsi x15, 2950, 0b11111
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2950, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2950, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2950, 0b10110
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh7
	li x5, 0xa5a5a5a5
	csrrw x15, 2951, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2951, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0xf42a7164
	csrrw x15, 2951, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2951, x5
	li x5, 0xf42a7164
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2951, x5
	li x5, 0xf5aff5e5
	bne x5, x15, csr_fail
	li x5, 0xd0928679
	csrrs x15, 2951, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2951, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2951, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xad3fa01c
	csrrc x15, 2951, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2951, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2951, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2951, 0b01011
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2951, 0b00101
	li x5, 0x0000000b
	bne x5, x15, csr_fail
	csrrsi x15, 2951, 0b11010
	li x5, 0x0000000f
	bne x5, x15, csr_fail
	csrrsi x15, 2951, 0b11100
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2951, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2951, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2951, 0b11100
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh8
	li x5, 0xa5a5a5a5
	csrrw x15, 2952, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2952, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0xe64a378d
	csrrw x15, 2952, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2952, x5
	li x5, 0xe64a378d
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2952, x5
	li x5, 0xe7efb7ad
	bne x5, x15, csr_fail
	li x5, 0xd6ebbc1c
	csrrs x15, 2952, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2952, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2952, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x663587a9
	csrrc x15, 2952, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2952, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2952, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2952, 0b11100
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2952, 0b00101
	li x5, 0x0000001c
	bne x5, x15, csr_fail
	csrrsi x15, 2952, 0b11010
	li x5, 0x0000001d
	bne x5, x15, csr_fail
	csrrsi x15, 2952, 0b00111
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2952, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2952, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2952, 0b01011
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh9
	li x5, 0xa5a5a5a5
	csrrw x15, 2953, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2953, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x1bf9e6dd
	csrrw x15, 2953, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2953, x5
	li x5, 0x1bf9e6dd
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2953, x5
	li x5, 0xbffde7fd
	bne x5, x15, csr_fail
	li x5, 0x67d15643
	csrrs x15, 2953, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2953, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2953, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xbc1e804b
	csrrc x15, 2953, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2953, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2953, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2953, 0b00110
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2953, 0b00101
	li x5, 0x00000006
	bne x5, x15, csr_fail
	csrrsi x15, 2953, 0b11010
	li x5, 0x00000007
	bne x5, x15, csr_fail
	csrrsi x15, 2953, 0b10000
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2953, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2953, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2953, 0b01011
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh10
	li x5, 0xa5a5a5a5
	csrrw x15, 2954, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2954, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x19bfdb8a
	csrrw x15, 2954, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2954, x5
	li x5, 0x19bfdb8a
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2954, x5
	li x5, 0xbdbfffaf
	bne x5, x15, csr_fail
	li x5, 0x1dc114af
	csrrs x15, 2954, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2954, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2954, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x0948d631
	csrrc x15, 2954, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2954, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2954, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2954, 0b01101
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2954, 0b00101
	li x5, 0x0000000d
	bne x5, x15, csr_fail
	csrrsi x15, 2954, 0b11010
	li x5, 0x0000000d
	bne x5, x15, csr_fail
	csrrsi x15, 2954, 0b00111
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2954, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2954, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2954, 0b10100
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh11
	li x5, 0xa5a5a5a5
	csrrw x15, 2955, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2955, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x0bea34fa
	csrrw x15, 2955, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2955, x5
	li x5, 0x0bea34fa
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2955, x5
	li x5, 0xafefb5ff
	bne x5, x15, csr_fail
	li x5, 0xa32b5c5b
	csrrs x15, 2955, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2955, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2955, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x77b267a0
	csrrc x15, 2955, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2955, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2955, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2955, 0b00110
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2955, 0b00101
	li x5, 0x00000006
	bne x5, x15, csr_fail
	csrrsi x15, 2955, 0b11010
	li x5, 0x00000007
	bne x5, x15, csr_fail
	csrrsi x15, 2955, 0b01111
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2955, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2955, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2955, 0b10001
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh12
	li x5, 0xa5a5a5a5
	csrrw x15, 2956, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2956, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x51b87738
	csrrw x15, 2956, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2956, x5
	li x5, 0x51b87738
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2956, x5
	li x5, 0xf5bdf7bd
	bne x5, x15, csr_fail
	li x5, 0xef71fa43
	csrrs x15, 2956, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2956, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2956, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x6e04d174
	csrrc x15, 2956, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2956, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2956, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2956, 0b10010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2956, 0b00101
	li x5, 0x00000012
	bne x5, x15, csr_fail
	csrrsi x15, 2956, 0b11010
	li x5, 0x00000017
	bne x5, x15, csr_fail
	csrrsi x15, 2956, 0b10111
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2956, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2956, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2956, 0b10011
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh13
	li x5, 0xa5a5a5a5
	csrrw x15, 2957, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2957, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x4906d0a6
	csrrw x15, 2957, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2957, x5
	li x5, 0x4906d0a6
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2957, x5
	li x5, 0xeda7f5a7
	bne x5, x15, csr_fail
	li x5, 0xf643ef2d
	csrrs x15, 2957, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2957, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2957, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa6be64e9
	csrrc x15, 2957, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2957, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2957, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2957, 0b10101
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2957, 0b00101
	li x5, 0x00000015
	bne x5, x15, csr_fail
	csrrsi x15, 2957, 0b11010
	li x5, 0x00000015
	bne x5, x15, csr_fail
	csrrsi x15, 2957, 0b11010
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2957, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2957, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2957, 0b10011
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh14
	li x5, 0xa5a5a5a5
	csrrw x15, 2958, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2958, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x7772d54a
	csrrw x15, 2958, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2958, x5
	li x5, 0x7772d54a
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2958, x5
	li x5, 0xf7f7f5ef
	bne x5, x15, csr_fail
	li x5, 0x5e2d84b5
	csrrs x15, 2958, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2958, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2958, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xfd804e78
	csrrc x15, 2958, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2958, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2958, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2958, 0b01000
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2958, 0b00101
	li x5, 0x00000008
	bne x5, x15, csr_fail
	csrrsi x15, 2958, 0b11010
	li x5, 0x0000000d
	bne x5, x15, csr_fail
	csrrsi x15, 2958, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2958, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2958, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2958, 0b01100
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh15
	li x5, 0xa5a5a5a5
	csrrw x15, 2959, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2959, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x2d2f3ca0
	csrrw x15, 2959, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2959, x5
	li x5, 0x2d2f3ca0
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2959, x5
	li x5, 0xadafbda5
	bne x5, x15, csr_fail
	li x5, 0xed51c6ed
	csrrs x15, 2959, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2959, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2959, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x2b93882f
	csrrc x15, 2959, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2959, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2959, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2959, 0b11110
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2959, 0b00101
	li x5, 0x0000001e
	bne x5, x15, csr_fail
	csrrsi x15, 2959, 0b11010
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrsi x15, 2959, 0b00111
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2959, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2959, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2959, 0b10101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh16
	li x5, 0xa5a5a5a5
	csrrw x15, 2960, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2960, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x0b99311d
	csrrw x15, 2960, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2960, x5
	li x5, 0x0b99311d
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2960, x5
	li x5, 0xafbdb5bd
	bne x5, x15, csr_fail
	li x5, 0xa20d6c13
	csrrs x15, 2960, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2960, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2960, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x0e4813b8
	csrrc x15, 2960, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2960, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2960, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2960, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2960, 0b00101
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2960, 0b11010
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrsi x15, 2960, 0b10100
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2960, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2960, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2960, 0b10100
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh17
	li x5, 0xa5a5a5a5
	csrrw x15, 2961, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2961, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x8c7062a5
	csrrw x15, 2961, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2961, x5
	li x5, 0x8c7062a5
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2961, x5
	li x5, 0xadf5e7a5
	bne x5, x15, csr_fail
	li x5, 0x168b744f
	csrrs x15, 2961, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2961, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2961, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x679bf535
	csrrc x15, 2961, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2961, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2961, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2961, 0b01010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2961, 0b00101
	li x5, 0x0000000a
	bne x5, x15, csr_fail
	csrrsi x15, 2961, 0b11010
	li x5, 0x0000000f
	bne x5, x15, csr_fail
	csrrsi x15, 2961, 0b11100
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2961, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2961, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2961, 0b11100
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh18
	li x5, 0xa5a5a5a5
	csrrw x15, 2962, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2962, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x19175bd2
	csrrw x15, 2962, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2962, x5
	li x5, 0x19175bd2
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2962, x5
	li x5, 0xbdb7fff7
	bne x5, x15, csr_fail
	li x5, 0x78e5331f
	csrrs x15, 2962, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2962, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2962, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x030c0f19
	csrrc x15, 2962, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2962, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2962, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2962, 0b00001
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2962, 0b00101
	li x5, 0x00000001
	bne x5, x15, csr_fail
	csrrsi x15, 2962, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrsi x15, 2962, 0b10001
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2962, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2962, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2962, 0b10000
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh19
	li x5, 0xa5a5a5a5
	csrrw x15, 2963, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2963, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x1d5d199e
	csrrw x15, 2963, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2963, x5
	li x5, 0x1d5d199e
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2963, x5
	li x5, 0xbdfdbdbf
	bne x5, x15, csr_fail
	li x5, 0xebff1c39
	csrrs x15, 2963, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2963, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2963, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x927e647f
	csrrc x15, 2963, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2963, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2963, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2963, 0b10011
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2963, 0b00101
	li x5, 0x00000013
	bne x5, x15, csr_fail
	csrrsi x15, 2963, 0b11010
	li x5, 0x00000017
	bne x5, x15, csr_fail
	csrrsi x15, 2963, 0b00011
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2963, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2963, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2963, 0b10000
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh20
	li x5, 0xa5a5a5a5
	csrrw x15, 2964, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2964, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x7c713b24
	csrrw x15, 2964, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2964, x5
	li x5, 0x7c713b24
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2964, x5
	li x5, 0xfdf5bfa5
	bne x5, x15, csr_fail
	li x5, 0x1d6635ee
	csrrs x15, 2964, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2964, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2964, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x0968a804
	csrrc x15, 2964, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2964, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2964, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2964, 0b00110
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2964, 0b00101
	li x5, 0x00000006
	bne x5, x15, csr_fail
	csrrsi x15, 2964, 0b11010
	li x5, 0x00000007
	bne x5, x15, csr_fail
	csrrsi x15, 2964, 0b00010
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2964, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2964, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2964, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh21
	li x5, 0xa5a5a5a5
	csrrw x15, 2965, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2965, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x612df4ba
	csrrw x15, 2965, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2965, x5
	li x5, 0x612df4ba
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2965, x5
	li x5, 0xe5adf5bf
	bne x5, x15, csr_fail
	li x5, 0x4c97cb48
	csrrs x15, 2965, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2965, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2965, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x7fe2f772
	csrrc x15, 2965, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2965, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2965, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2965, 0b10000
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2965, 0b00101
	li x5, 0x00000010
	bne x5, x15, csr_fail
	csrrsi x15, 2965, 0b11010
	li x5, 0x00000015
	bne x5, x15, csr_fail
	csrrsi x15, 2965, 0b00010
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2965, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2965, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2965, 0b11110
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh22
	li x5, 0xa5a5a5a5
	csrrw x15, 2966, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2966, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0xce837a0f
	csrrw x15, 2966, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2966, x5
	li x5, 0xce837a0f
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2966, x5
	li x5, 0xefa7ffaf
	bne x5, x15, csr_fail
	li x5, 0x923e9fde
	csrrs x15, 2966, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2966, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2966, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xad473df8
	csrrc x15, 2966, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2966, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2966, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2966, 0b10111
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2966, 0b00101
	li x5, 0x00000017
	bne x5, x15, csr_fail
	csrrsi x15, 2966, 0b11010
	li x5, 0x00000017
	bne x5, x15, csr_fail
	csrrsi x15, 2966, 0b01000
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2966, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2966, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2966, 0b01011
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh23
	li x5, 0xa5a5a5a5
	csrrw x15, 2967, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2967, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0xe6276ce9
	csrrw x15, 2967, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2967, x5
	li x5, 0xe6276ce9
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2967, x5
	li x5, 0xe7a7eded
	bne x5, x15, csr_fail
	li x5, 0x30a2bc64
	csrrs x15, 2967, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2967, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2967, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x1993db40
	csrrc x15, 2967, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2967, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2967, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2967, 0b11000
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2967, 0b00101
	li x5, 0x00000018
	bne x5, x15, csr_fail
	csrrsi x15, 2967, 0b11010
	li x5, 0x0000001d
	bne x5, x15, csr_fail
	csrrsi x15, 2967, 0b11011
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2967, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2967, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2967, 0b11001
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh24
	li x5, 0xa5a5a5a5
	csrrw x15, 2968, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2968, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x33aec0ed
	csrrw x15, 2968, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2968, x5
	li x5, 0x33aec0ed
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2968, x5
	li x5, 0xb7afe5ed
	bne x5, x15, csr_fail
	li x5, 0xfa5a4dd9
	csrrs x15, 2968, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2968, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2968, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x16b2cdd0
	csrrc x15, 2968, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2968, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2968, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2968, 0b10000
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2968, 0b00101
	li x5, 0x00000010
	bne x5, x15, csr_fail
	csrrsi x15, 2968, 0b11010
	li x5, 0x00000015
	bne x5, x15, csr_fail
	csrrsi x15, 2968, 0b11010
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2968, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2968, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2968, 0b01001
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh25
	li x5, 0xa5a5a5a5
	csrrw x15, 2969, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2969, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x7981abbb
	csrrw x15, 2969, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2969, x5
	li x5, 0x7981abbb
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2969, x5
	li x5, 0xfda5afbf
	bne x5, x15, csr_fail
	li x5, 0x2a637600
	csrrs x15, 2969, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2969, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2969, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x8e5de396
	csrrc x15, 2969, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2969, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2969, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2969, 0b01111
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2969, 0b00101
	li x5, 0x0000000f
	bne x5, x15, csr_fail
	csrrsi x15, 2969, 0b11010
	li x5, 0x0000000f
	bne x5, x15, csr_fail
	csrrsi x15, 2969, 0b10111
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2969, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2969, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2969, 0b11010
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh26
	li x5, 0xa5a5a5a5
	csrrw x15, 2970, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2970, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x453b4cc5
	csrrw x15, 2970, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2970, x5
	li x5, 0x453b4cc5
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2970, x5
	li x5, 0xe5bfede5
	bne x5, x15, csr_fail
	li x5, 0x9af3ee1b
	csrrs x15, 2970, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2970, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2970, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x9b5af5a0
	csrrc x15, 2970, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2970, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2970, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2970, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2970, 0b00101
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2970, 0b11010
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrsi x15, 2970, 0b11111
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2970, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2970, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2970, 0b11011
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh27
	li x5, 0xa5a5a5a5
	csrrw x15, 2971, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2971, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x2ea119f8
	csrrw x15, 2971, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2971, x5
	li x5, 0x2ea119f8
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2971, x5
	li x5, 0xafa5bdfd
	bne x5, x15, csr_fail
	li x5, 0x263ed361
	csrrs x15, 2971, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2971, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2971, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x3559f480
	csrrc x15, 2971, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2971, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2971, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2971, 0b10010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2971, 0b00101
	li x5, 0x00000012
	bne x5, x15, csr_fail
	csrrsi x15, 2971, 0b11010
	li x5, 0x00000017
	bne x5, x15, csr_fail
	csrrsi x15, 2971, 0b01100
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2971, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2971, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2971, 0b00001
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh28
	li x5, 0xa5a5a5a5
	csrrw x15, 2972, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2972, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x8e030ab4
	csrrw x15, 2972, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2972, x5
	li x5, 0x8e030ab4
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2972, x5
	li x5, 0xafa7afb5
	bne x5, x15, csr_fail
	li x5, 0x1c55a07b
	csrrs x15, 2972, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2972, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2972, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x69b45543
	csrrc x15, 2972, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2972, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2972, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2972, 0b01000
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2972, 0b00101
	li x5, 0x00000008
	bne x5, x15, csr_fail
	csrrsi x15, 2972, 0b11010
	li x5, 0x0000000d
	bne x5, x15, csr_fail
	csrrsi x15, 2972, 0b11100
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2972, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2972, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2972, 0b10100
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh29
	li x5, 0xa5a5a5a5
	csrrw x15, 2973, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2973, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0xeeaee738
	csrrw x15, 2973, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2973, x5
	li x5, 0xeeaee738
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2973, x5
	li x5, 0xefafe7bd
	bne x5, x15, csr_fail
	li x5, 0x184d62ef
	csrrs x15, 2973, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2973, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2973, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xd1aee09c
	csrrc x15, 2973, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2973, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2973, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2973, 0b10000
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2973, 0b00101
	li x5, 0x00000010
	bne x5, x15, csr_fail
	csrrsi x15, 2973, 0b11010
	li x5, 0x00000015
	bne x5, x15, csr_fail
	csrrsi x15, 2973, 0b00111
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2973, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2973, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2973, 0b11101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh30
	li x5, 0xa5a5a5a5
	csrrw x15, 2974, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2974, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x11c41528
	csrrw x15, 2974, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2974, x5
	li x5, 0x11c41528
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2974, x5
	li x5, 0xb5e5b5ad
	bne x5, x15, csr_fail
	li x5, 0xce03cd76
	csrrs x15, 2974, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2974, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2974, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x8d82832d
	csrrc x15, 2974, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2974, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2974, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2974, 0b10010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2974, 0b00101
	li x5, 0x00000012
	bne x5, x15, csr_fail
	csrrsi x15, 2974, 0b11010
	li x5, 0x00000017
	bne x5, x15, csr_fail
	csrrsi x15, 2974, 0b00011
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2974, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2974, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2974, 0b00000
	li x5, 0x00000000
	bne x5, x15, csr_fail
	# mhpmcounterh31
	li x5, 0xa5a5a5a5
	csrrw x15, 2975, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 2975, x5
	li x5, 0xa5a5a5a5
	bne x5, x15, csr_fail
	li x5, 0x8fbb05fb
	csrrw x15, 2975, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 2975, x5
	li x5, 0x8fbb05fb
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 2975, x5
	li x5, 0xafbfa5ff
	bne x5, x15, csr_fail
	li x5, 0x4b6a3f57
	csrrs x15, 2975, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 2975, x5
	li x5, 0xffffffff
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 2975, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xcf06f89a
	csrrc x15, 2975, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2975, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 2975, 0b11010
	li x5, 0x00000005
	bne x5, x15, csr_fail
	csrrwi x15, 2975, 0b10110
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 2975, 0b00101
	li x5, 0x00000016
	bne x5, x15, csr_fail
	csrrsi x15, 2975, 0b11010
	li x5, 0x00000017
	bne x5, x15, csr_fail
	csrrsi x15, 2975, 0b00011
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2975, 0b00101
	li x5, 0x0000001f
	bne x5, x15, csr_fail
	csrrci x15, 2975, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 2975, 0b00011
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrr x15, 2975
	li x5, 0x00000000
	bne x5, x15, csr_fail

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
