# ------------------------------------------------------------------------------
#   Copyright 2026 Thales France
#
#   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#   You may obtain a copy of the License at https://solderpad.org/licenses/
# ------------------------------------------------------------------------------
#   cm_popret_all.S
#
#   cm.popret and cm.popretz for every register list (rlist 4 to 15), as the
#   epilogue of a called function:
#     - the caller calls fn_N, which runs cm.push, overwrites the saved
#       registers, sets a0 to a marker, then returns with cm.popret or
#       cm.popretz;
#     - back in the caller, the test checks that it came back to the right
#       place, that every saved register holds its value from before the
#       call, that sp is unchanged, and that a0 is zero after cm.popretz and
#       still the marker after cm.popret.
#
#   Failure writes the case number to tohost as (2*n+1).
# ------------------------------------------------------------------------------

#include "riscv_test.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN
    li    gp, 0

    # case 1: cm.popret {ra}, 16
    li    gp, 1
    la    sp, stack_top
    li    a0, 0
    mv    a2, sp
    jal   fn_1
ret_1:
    bne   sp, a2, fail
    li    t1, 0x1077
    bne   a0, t1, fail
    la    t1, ret_1
    bne   ra, t1, fail
    # case 2: cm.popretz {ra}, 16
    li    gp, 2
    la    sp, stack_top
    li    a0, 0
    mv    a2, sp
    jal   fn_2
ret_2:
    bne   sp, a2, fail
    bnez  a0, fail
    la    t1, ret_2
    bne   ra, t1, fail
    # case 3: cm.popret {ra, s0}, 16
    li    gp, 3
    la    sp, stack_top
    li    s0, 0x3002
    li    a0, 0
    mv    a2, sp
    jal   fn_3
ret_3:
    bne   sp, a2, fail
    li    t1, 0x3002
    bne   s0, t1, fail
    li    t1, 0x3077
    bne   a0, t1, fail
    la    t1, ret_3
    bne   ra, t1, fail
    # case 4: cm.popretz {ra, s0}, 16
    li    gp, 4
    la    sp, stack_top
    li    s0, 0x4002
    li    a0, 0
    mv    a2, sp
    jal   fn_4
ret_4:
    bne   sp, a2, fail
    li    t1, 0x4002
    bne   s0, t1, fail
    bnez  a0, fail
    la    t1, ret_4
    bne   ra, t1, fail
    # case 5: cm.popret {ra, s0-s1}, 16
    li    gp, 5
    la    sp, stack_top
    li    s0, 0x5002
    li    s1, 0x5003
    li    a0, 0
    mv    a2, sp
    jal   fn_5
ret_5:
    bne   sp, a2, fail
    li    t1, 0x5002
    bne   s0, t1, fail
    li    t1, 0x5003
    bne   s1, t1, fail
    li    t1, 0x5077
    bne   a0, t1, fail
    la    t1, ret_5
    bne   ra, t1, fail
    # case 6: cm.popretz {ra, s0-s1}, 16
    li    gp, 6
    la    sp, stack_top
    li    s0, 0x6002
    li    s1, 0x6003
    li    a0, 0
    mv    a2, sp
    jal   fn_6
ret_6:
    bne   sp, a2, fail
    li    t1, 0x6002
    bne   s0, t1, fail
    li    t1, 0x6003
    bne   s1, t1, fail
    bnez  a0, fail
    la    t1, ret_6
    bne   ra, t1, fail
    # case 7: cm.popret {ra, s0-s2}, 16
    li    gp, 7
    la    sp, stack_top
    li    s0, 0x7002
    li    s1, 0x7003
    li    s2, 0x7004
    li    a0, 0
    mv    a2, sp
    jal   fn_7
ret_7:
    bne   sp, a2, fail
    li    t1, 0x7002
    bne   s0, t1, fail
    li    t1, 0x7003
    bne   s1, t1, fail
    li    t1, 0x7004
    bne   s2, t1, fail
    li    t1, 0x7077
    bne   a0, t1, fail
    la    t1, ret_7
    bne   ra, t1, fail
    # case 8: cm.popretz {ra, s0-s2}, 16
    li    gp, 8
    la    sp, stack_top
    li    s0, 0x8002
    li    s1, 0x8003
    li    s2, 0x8004
    li    a0, 0
    mv    a2, sp
    jal   fn_8
ret_8:
    bne   sp, a2, fail
    li    t1, 0x8002
    bne   s0, t1, fail
    li    t1, 0x8003
    bne   s1, t1, fail
    li    t1, 0x8004
    bne   s2, t1, fail
    bnez  a0, fail
    la    t1, ret_8
    bne   ra, t1, fail
    # case 9: cm.popret {ra, s0-s3}, 32
    li    gp, 9
    la    sp, stack_top
    li    s0, 0x9002
    li    s1, 0x9003
    li    s2, 0x9004
    li    s3, 0x9005
    li    a0, 0
    mv    a2, sp
    jal   fn_9
ret_9:
    bne   sp, a2, fail
    li    t1, 0x9002
    bne   s0, t1, fail
    li    t1, 0x9003
    bne   s1, t1, fail
    li    t1, 0x9004
    bne   s2, t1, fail
    li    t1, 0x9005
    bne   s3, t1, fail
    li    t1, 0x9077
    bne   a0, t1, fail
    la    t1, ret_9
    bne   ra, t1, fail
    # case 10: cm.popretz {ra, s0-s3}, 32
    li    gp, 10
    la    sp, stack_top
    li    s0, 0xa002
    li    s1, 0xa003
    li    s2, 0xa004
    li    s3, 0xa005
    li    a0, 0
    mv    a2, sp
    jal   fn_10
ret_10:
    bne   sp, a2, fail
    li    t1, 0xa002
    bne   s0, t1, fail
    li    t1, 0xa003
    bne   s1, t1, fail
    li    t1, 0xa004
    bne   s2, t1, fail
    li    t1, 0xa005
    bne   s3, t1, fail
    bnez  a0, fail
    la    t1, ret_10
    bne   ra, t1, fail
    # case 11: cm.popret {ra, s0-s4}, 32
    li    gp, 11
    la    sp, stack_top
    li    s0, 0xb002
    li    s1, 0xb003
    li    s2, 0xb004
    li    s3, 0xb005
    li    s4, 0xb006
    li    a0, 0
    mv    a2, sp
    jal   fn_11
ret_11:
    bne   sp, a2, fail
    li    t1, 0xb002
    bne   s0, t1, fail
    li    t1, 0xb003
    bne   s1, t1, fail
    li    t1, 0xb004
    bne   s2, t1, fail
    li    t1, 0xb005
    bne   s3, t1, fail
    li    t1, 0xb006
    bne   s4, t1, fail
    li    t1, 0xb077
    bne   a0, t1, fail
    la    t1, ret_11
    bne   ra, t1, fail
    # case 12: cm.popretz {ra, s0-s4}, 32
    li    gp, 12
    la    sp, stack_top
    li    s0, 0xc002
    li    s1, 0xc003
    li    s2, 0xc004
    li    s3, 0xc005
    li    s4, 0xc006
    li    a0, 0
    mv    a2, sp
    jal   fn_12
ret_12:
    bne   sp, a2, fail
    li    t1, 0xc002
    bne   s0, t1, fail
    li    t1, 0xc003
    bne   s1, t1, fail
    li    t1, 0xc004
    bne   s2, t1, fail
    li    t1, 0xc005
    bne   s3, t1, fail
    li    t1, 0xc006
    bne   s4, t1, fail
    bnez  a0, fail
    la    t1, ret_12
    bne   ra, t1, fail
    # case 13: cm.popret {ra, s0-s5}, 32
    li    gp, 13
    la    sp, stack_top
    li    s0, 0xd002
    li    s1, 0xd003
    li    s2, 0xd004
    li    s3, 0xd005
    li    s4, 0xd006
    li    s5, 0xd007
    li    a0, 0
    mv    a2, sp
    jal   fn_13
ret_13:
    bne   sp, a2, fail
    li    t1, 0xd002
    bne   s0, t1, fail
    li    t1, 0xd003
    bne   s1, t1, fail
    li    t1, 0xd004
    bne   s2, t1, fail
    li    t1, 0xd005
    bne   s3, t1, fail
    li    t1, 0xd006
    bne   s4, t1, fail
    li    t1, 0xd007
    bne   s5, t1, fail
    li    t1, 0xd077
    bne   a0, t1, fail
    la    t1, ret_13
    bne   ra, t1, fail
    # case 14: cm.popretz {ra, s0-s5}, 32
    li    gp, 14
    la    sp, stack_top
    li    s0, 0xe002
    li    s1, 0xe003
    li    s2, 0xe004
    li    s3, 0xe005
    li    s4, 0xe006
    li    s5, 0xe007
    li    a0, 0
    mv    a2, sp
    jal   fn_14
ret_14:
    bne   sp, a2, fail
    li    t1, 0xe002
    bne   s0, t1, fail
    li    t1, 0xe003
    bne   s1, t1, fail
    li    t1, 0xe004
    bne   s2, t1, fail
    li    t1, 0xe005
    bne   s3, t1, fail
    li    t1, 0xe006
    bne   s4, t1, fail
    li    t1, 0xe007
    bne   s5, t1, fail
    bnez  a0, fail
    la    t1, ret_14
    bne   ra, t1, fail
    # case 15: cm.popret {ra, s0-s6}, 32
    li    gp, 15
    la    sp, stack_top
    li    s0, 0xf002
    li    s1, 0xf003
    li    s2, 0xf004
    li    s3, 0xf005
    li    s4, 0xf006
    li    s5, 0xf007
    li    s6, 0xf008
    li    a0, 0
    mv    a2, sp
    jal   fn_15
ret_15:
    bne   sp, a2, fail
    li    t1, 0xf002
    bne   s0, t1, fail
    li    t1, 0xf003
    bne   s1, t1, fail
    li    t1, 0xf004
    bne   s2, t1, fail
    li    t1, 0xf005
    bne   s3, t1, fail
    li    t1, 0xf006
    bne   s4, t1, fail
    li    t1, 0xf007
    bne   s5, t1, fail
    li    t1, 0xf008
    bne   s6, t1, fail
    li    t1, 0xf077
    bne   a0, t1, fail
    la    t1, ret_15
    bne   ra, t1, fail
    # case 16: cm.popretz {ra, s0-s6}, 32
    li    gp, 16
    la    sp, stack_top
    li    s0, 0x10002
    li    s1, 0x10003
    li    s2, 0x10004
    li    s3, 0x10005
    li    s4, 0x10006
    li    s5, 0x10007
    li    s6, 0x10008
    li    a0, 0
    mv    a2, sp
    jal   fn_16
ret_16:
    bne   sp, a2, fail
    li    t1, 0x10002
    bne   s0, t1, fail
    li    t1, 0x10003
    bne   s1, t1, fail
    li    t1, 0x10004
    bne   s2, t1, fail
    li    t1, 0x10005
    bne   s3, t1, fail
    li    t1, 0x10006
    bne   s4, t1, fail
    li    t1, 0x10007
    bne   s5, t1, fail
    li    t1, 0x10008
    bne   s6, t1, fail
    bnez  a0, fail
    la    t1, ret_16
    bne   ra, t1, fail
    # case 17: cm.popret {ra, s0-s7}, 48
    li    gp, 17
    la    sp, stack_top
    li    s0, 0x11002
    li    s1, 0x11003
    li    s2, 0x11004
    li    s3, 0x11005
    li    s4, 0x11006
    li    s5, 0x11007
    li    s6, 0x11008
    li    s7, 0x11009
    li    a0, 0
    mv    a2, sp
    jal   fn_17
ret_17:
    bne   sp, a2, fail
    li    t1, 0x11002
    bne   s0, t1, fail
    li    t1, 0x11003
    bne   s1, t1, fail
    li    t1, 0x11004
    bne   s2, t1, fail
    li    t1, 0x11005
    bne   s3, t1, fail
    li    t1, 0x11006
    bne   s4, t1, fail
    li    t1, 0x11007
    bne   s5, t1, fail
    li    t1, 0x11008
    bne   s6, t1, fail
    li    t1, 0x11009
    bne   s7, t1, fail
    li    t1, 0x11077
    bne   a0, t1, fail
    la    t1, ret_17
    bne   ra, t1, fail
    # case 18: cm.popretz {ra, s0-s7}, 48
    li    gp, 18
    la    sp, stack_top
    li    s0, 0x12002
    li    s1, 0x12003
    li    s2, 0x12004
    li    s3, 0x12005
    li    s4, 0x12006
    li    s5, 0x12007
    li    s6, 0x12008
    li    s7, 0x12009
    li    a0, 0
    mv    a2, sp
    jal   fn_18
ret_18:
    bne   sp, a2, fail
    li    t1, 0x12002
    bne   s0, t1, fail
    li    t1, 0x12003
    bne   s1, t1, fail
    li    t1, 0x12004
    bne   s2, t1, fail
    li    t1, 0x12005
    bne   s3, t1, fail
    li    t1, 0x12006
    bne   s4, t1, fail
    li    t1, 0x12007
    bne   s5, t1, fail
    li    t1, 0x12008
    bne   s6, t1, fail
    li    t1, 0x12009
    bne   s7, t1, fail
    bnez  a0, fail
    la    t1, ret_18
    bne   ra, t1, fail
    # case 19: cm.popret {ra, s0-s8}, 48
    li    gp, 19
    la    sp, stack_top
    li    s0, 0x13002
    li    s1, 0x13003
    li    s2, 0x13004
    li    s3, 0x13005
    li    s4, 0x13006
    li    s5, 0x13007
    li    s6, 0x13008
    li    s7, 0x13009
    li    s8, 0x1300a
    li    a0, 0
    mv    a2, sp
    jal   fn_19
ret_19:
    bne   sp, a2, fail
    li    t1, 0x13002
    bne   s0, t1, fail
    li    t1, 0x13003
    bne   s1, t1, fail
    li    t1, 0x13004
    bne   s2, t1, fail
    li    t1, 0x13005
    bne   s3, t1, fail
    li    t1, 0x13006
    bne   s4, t1, fail
    li    t1, 0x13007
    bne   s5, t1, fail
    li    t1, 0x13008
    bne   s6, t1, fail
    li    t1, 0x13009
    bne   s7, t1, fail
    li    t1, 0x1300a
    bne   s8, t1, fail
    li    t1, 0x13077
    bne   a0, t1, fail
    la    t1, ret_19
    bne   ra, t1, fail
    # case 20: cm.popretz {ra, s0-s8}, 48
    li    gp, 20
    la    sp, stack_top
    li    s0, 0x14002
    li    s1, 0x14003
    li    s2, 0x14004
    li    s3, 0x14005
    li    s4, 0x14006
    li    s5, 0x14007
    li    s6, 0x14008
    li    s7, 0x14009
    li    s8, 0x1400a
    li    a0, 0
    mv    a2, sp
    jal   fn_20
ret_20:
    bne   sp, a2, fail
    li    t1, 0x14002
    bne   s0, t1, fail
    li    t1, 0x14003
    bne   s1, t1, fail
    li    t1, 0x14004
    bne   s2, t1, fail
    li    t1, 0x14005
    bne   s3, t1, fail
    li    t1, 0x14006
    bne   s4, t1, fail
    li    t1, 0x14007
    bne   s5, t1, fail
    li    t1, 0x14008
    bne   s6, t1, fail
    li    t1, 0x14009
    bne   s7, t1, fail
    li    t1, 0x1400a
    bne   s8, t1, fail
    bnez  a0, fail
    la    t1, ret_20
    bne   ra, t1, fail
    # case 21: cm.popret {ra, s0-s9}, 48
    li    gp, 21
    la    sp, stack_top
    li    s0, 0x15002
    li    s1, 0x15003
    li    s2, 0x15004
    li    s3, 0x15005
    li    s4, 0x15006
    li    s5, 0x15007
    li    s6, 0x15008
    li    s7, 0x15009
    li    s8, 0x1500a
    li    s9, 0x1500b
    li    a0, 0
    mv    a2, sp
    jal   fn_21
ret_21:
    bne   sp, a2, fail
    li    t1, 0x15002
    bne   s0, t1, fail
    li    t1, 0x15003
    bne   s1, t1, fail
    li    t1, 0x15004
    bne   s2, t1, fail
    li    t1, 0x15005
    bne   s3, t1, fail
    li    t1, 0x15006
    bne   s4, t1, fail
    li    t1, 0x15007
    bne   s5, t1, fail
    li    t1, 0x15008
    bne   s6, t1, fail
    li    t1, 0x15009
    bne   s7, t1, fail
    li    t1, 0x1500a
    bne   s8, t1, fail
    li    t1, 0x1500b
    bne   s9, t1, fail
    li    t1, 0x15077
    bne   a0, t1, fail
    la    t1, ret_21
    bne   ra, t1, fail
    # case 22: cm.popretz {ra, s0-s9}, 48
    li    gp, 22
    la    sp, stack_top
    li    s0, 0x16002
    li    s1, 0x16003
    li    s2, 0x16004
    li    s3, 0x16005
    li    s4, 0x16006
    li    s5, 0x16007
    li    s6, 0x16008
    li    s7, 0x16009
    li    s8, 0x1600a
    li    s9, 0x1600b
    li    a0, 0
    mv    a2, sp
    jal   fn_22
ret_22:
    bne   sp, a2, fail
    li    t1, 0x16002
    bne   s0, t1, fail
    li    t1, 0x16003
    bne   s1, t1, fail
    li    t1, 0x16004
    bne   s2, t1, fail
    li    t1, 0x16005
    bne   s3, t1, fail
    li    t1, 0x16006
    bne   s4, t1, fail
    li    t1, 0x16007
    bne   s5, t1, fail
    li    t1, 0x16008
    bne   s6, t1, fail
    li    t1, 0x16009
    bne   s7, t1, fail
    li    t1, 0x1600a
    bne   s8, t1, fail
    li    t1, 0x1600b
    bne   s9, t1, fail
    bnez  a0, fail
    la    t1, ret_22
    bne   ra, t1, fail
    # case 23: cm.popret {ra, s0-s11}, 64
    li    gp, 23
    la    sp, stack_top
    li    s0, 0x17002
    li    s1, 0x17003
    li    s2, 0x17004
    li    s3, 0x17005
    li    s4, 0x17006
    li    s5, 0x17007
    li    s6, 0x17008
    li    s7, 0x17009
    li    s8, 0x1700a
    li    s9, 0x1700b
    li    s10, 0x1700c
    li    s11, 0x1700d
    li    a0, 0
    mv    a2, sp
    jal   fn_23
ret_23:
    bne   sp, a2, fail
    li    t1, 0x17002
    bne   s0, t1, fail
    li    t1, 0x17003
    bne   s1, t1, fail
    li    t1, 0x17004
    bne   s2, t1, fail
    li    t1, 0x17005
    bne   s3, t1, fail
    li    t1, 0x17006
    bne   s4, t1, fail
    li    t1, 0x17007
    bne   s5, t1, fail
    li    t1, 0x17008
    bne   s6, t1, fail
    li    t1, 0x17009
    bne   s7, t1, fail
    li    t1, 0x1700a
    bne   s8, t1, fail
    li    t1, 0x1700b
    bne   s9, t1, fail
    li    t1, 0x1700c
    bne   s10, t1, fail
    li    t1, 0x1700d
    bne   s11, t1, fail
    li    t1, 0x17077
    bne   a0, t1, fail
    la    t1, ret_23
    bne   ra, t1, fail
    # case 24: cm.popretz {ra, s0-s11}, 64
    li    gp, 24
    la    sp, stack_top
    li    s0, 0x18002
    li    s1, 0x18003
    li    s2, 0x18004
    li    s3, 0x18005
    li    s4, 0x18006
    li    s5, 0x18007
    li    s6, 0x18008
    li    s7, 0x18009
    li    s8, 0x1800a
    li    s9, 0x1800b
    li    s10, 0x1800c
    li    s11, 0x1800d
    li    a0, 0
    mv    a2, sp
    jal   fn_24
ret_24:
    bne   sp, a2, fail
    li    t1, 0x18002
    bne   s0, t1, fail
    li    t1, 0x18003
    bne   s1, t1, fail
    li    t1, 0x18004
    bne   s2, t1, fail
    li    t1, 0x18005
    bne   s3, t1, fail
    li    t1, 0x18006
    bne   s4, t1, fail
    li    t1, 0x18007
    bne   s5, t1, fail
    li    t1, 0x18008
    bne   s6, t1, fail
    li    t1, 0x18009
    bne   s7, t1, fail
    li    t1, 0x1800a
    bne   s8, t1, fail
    li    t1, 0x1800b
    bne   s9, t1, fail
    li    t1, 0x1800c
    bne   s10, t1, fail
    li    t1, 0x1800d
    bne   s11, t1, fail
    bnez  a0, fail
    la    t1, ret_24
    bne   ra, t1, fail

pass:
    RVTEST_PASS

fail:
    RVTEST_FAIL

fn_1:
    cm.push {ra}, -16
    li    a0, 0x1077
    cm.popret {ra}, 16
    j     fail                  # cm.popret must not fall through

fn_2:
    cm.push {ra}, -16
    li    a0, 0x2077
    cm.popretz {ra}, 16
    j     fail                  # cm.popret must not fall through

fn_3:
    cm.push {ra, s0}, -16
    li    s0, -1
    li    a0, 0x3077
    cm.popret {ra, s0}, 16
    j     fail                  # cm.popret must not fall through

fn_4:
    cm.push {ra, s0}, -16
    li    s0, -1
    li    a0, 0x4077
    cm.popretz {ra, s0}, 16
    j     fail                  # cm.popret must not fall through

fn_5:
    cm.push {ra, s0-s1}, -16
    li    s0, -1
    li    s1, -1
    li    a0, 0x5077
    cm.popret {ra, s0-s1}, 16
    j     fail                  # cm.popret must not fall through

fn_6:
    cm.push {ra, s0-s1}, -16
    li    s0, -1
    li    s1, -1
    li    a0, 0x6077
    cm.popretz {ra, s0-s1}, 16
    j     fail                  # cm.popret must not fall through

fn_7:
    cm.push {ra, s0-s2}, -16
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    a0, 0x7077
    cm.popret {ra, s0-s2}, 16
    j     fail                  # cm.popret must not fall through

fn_8:
    cm.push {ra, s0-s2}, -16
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    a0, 0x8077
    cm.popretz {ra, s0-s2}, 16
    j     fail                  # cm.popret must not fall through

fn_9:
    cm.push {ra, s0-s3}, -32
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    a0, 0x9077
    cm.popret {ra, s0-s3}, 32
    j     fail                  # cm.popret must not fall through

fn_10:
    cm.push {ra, s0-s3}, -32
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    a0, 0xa077
    cm.popretz {ra, s0-s3}, 32
    j     fail                  # cm.popret must not fall through

fn_11:
    cm.push {ra, s0-s4}, -32
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    s4, -1
    li    a0, 0xb077
    cm.popret {ra, s0-s4}, 32
    j     fail                  # cm.popret must not fall through

fn_12:
    cm.push {ra, s0-s4}, -32
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    s4, -1
    li    a0, 0xc077
    cm.popretz {ra, s0-s4}, 32
    j     fail                  # cm.popret must not fall through

fn_13:
    cm.push {ra, s0-s5}, -32
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    s4, -1
    li    s5, -1
    li    a0, 0xd077
    cm.popret {ra, s0-s5}, 32
    j     fail                  # cm.popret must not fall through

fn_14:
    cm.push {ra, s0-s5}, -32
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    s4, -1
    li    s5, -1
    li    a0, 0xe077
    cm.popretz {ra, s0-s5}, 32
    j     fail                  # cm.popret must not fall through

fn_15:
    cm.push {ra, s0-s6}, -32
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    s4, -1
    li    s5, -1
    li    s6, -1
    li    a0, 0xf077
    cm.popret {ra, s0-s6}, 32
    j     fail                  # cm.popret must not fall through

fn_16:
    cm.push {ra, s0-s6}, -32
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    s4, -1
    li    s5, -1
    li    s6, -1
    li    a0, 0x10077
    cm.popretz {ra, s0-s6}, 32
    j     fail                  # cm.popret must not fall through

fn_17:
    cm.push {ra, s0-s7}, -48
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    s4, -1
    li    s5, -1
    li    s6, -1
    li    s7, -1
    li    a0, 0x11077
    cm.popret {ra, s0-s7}, 48
    j     fail                  # cm.popret must not fall through

fn_18:
    cm.push {ra, s0-s7}, -48
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    s4, -1
    li    s5, -1
    li    s6, -1
    li    s7, -1
    li    a0, 0x12077
    cm.popretz {ra, s0-s7}, 48
    j     fail                  # cm.popret must not fall through

fn_19:
    cm.push {ra, s0-s8}, -48
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    s4, -1
    li    s5, -1
    li    s6, -1
    li    s7, -1
    li    s8, -1
    li    a0, 0x13077
    cm.popret {ra, s0-s8}, 48
    j     fail                  # cm.popret must not fall through

fn_20:
    cm.push {ra, s0-s8}, -48
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    s4, -1
    li    s5, -1
    li    s6, -1
    li    s7, -1
    li    s8, -1
    li    a0, 0x14077
    cm.popretz {ra, s0-s8}, 48
    j     fail                  # cm.popret must not fall through

fn_21:
    cm.push {ra, s0-s9}, -48
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    s4, -1
    li    s5, -1
    li    s6, -1
    li    s7, -1
    li    s8, -1
    li    s9, -1
    li    a0, 0x15077
    cm.popret {ra, s0-s9}, 48
    j     fail                  # cm.popret must not fall through

fn_22:
    cm.push {ra, s0-s9}, -48
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    s4, -1
    li    s5, -1
    li    s6, -1
    li    s7, -1
    li    s8, -1
    li    s9, -1
    li    a0, 0x16077
    cm.popretz {ra, s0-s9}, 48
    j     fail                  # cm.popret must not fall through

fn_23:
    cm.push {ra, s0-s11}, -64
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    s4, -1
    li    s5, -1
    li    s6, -1
    li    s7, -1
    li    s8, -1
    li    s9, -1
    li    s10, -1
    li    s11, -1
    li    a0, 0x17077
    cm.popret {ra, s0-s11}, 64
    j     fail                  # cm.popret must not fall through

fn_24:
    cm.push {ra, s0-s11}, -64
    li    s0, -1
    li    s1, -1
    li    s2, -1
    li    s3, -1
    li    s4, -1
    li    s5, -1
    li    s6, -1
    li    s7, -1
    li    s8, -1
    li    s9, -1
    li    s10, -1
    li    s11, -1
    li    a0, 0x18077
    cm.popretz {ra, s0-s11}, 64
    j     fail                  # cm.popret must not fall through

RVTEST_CODE_END

    .data
RVTEST_DATA_BEGIN
    .align 4
stack_bot:
    .space 256
stack_top:
    .space 16
RVTEST_DATA_END
