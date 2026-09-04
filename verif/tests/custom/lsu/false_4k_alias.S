# Copyright 2026 Srinidhi-Magesh
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

# Check that a conservative 4 KiB alias never forwards data from another page.

  .globl main
main:
  la t0, page_a
  la t1, page_b

  # page_a + 0x18 and page_b + 0x18 intentionally have identical [11:3]
  # address bits, but page_a and page_b are distinct 4 KiB-aligned pages.
  li t2, 0x13579bdf
  sw t2, 0x18(t1)
  fence rw, rw

  # Keep the store and load adjacent so the older store can still be pending.
  li a2, 0x55667788
  sw a2, 0x18(t0)
  lw a3, 0x18(t1)
  bne a3, t2, fail

pass:
  li a0, 0
  jal exit

fail:
  li a0, 1
  jal exit

  .section .data,"aw",@progbits
  .balign 4096
page_a:
  .space 4096
page_b:
  .space 4096
