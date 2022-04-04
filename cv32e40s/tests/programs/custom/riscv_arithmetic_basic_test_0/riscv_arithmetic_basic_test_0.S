# BEGIN: riscv-dv
#.include "user_define.h"
#.globl _start
#.section .text
#_start:
# END: riscv-dv
# BEGIN: gtumbush
#include "corev_uvmt.h"
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
# END: gtumbush
# BEGIN: riscv-dv
                  csrr x5, mhartid
                  li x6, 0
                  beq x5, x6, 0f

0: j h0_start
h0_start:
                  li x30, 0x40001104
                  csrw misa, x30
kernel_sp:
                  la x13, kernel_stack_end

trap_vec_init:
                  la x30, mtvec_handler
                  ori x30, x30, 1
                  csrw 0x305, x30 # MTVEC

mepc_setup:
                  la x30, init
                  csrw mepc, x30
                  j init_machine_mode

init:
                  li x0, 0xffae545d
                  li x1, 0xf
                  li x2, 0xfaea503e
                  li x3, 0x0
                  li x4, 0x997a59f3
                  li x5, 0x0
                  li x6, 0xf4dc53a8
                  li x7, 0x35df9683
                  li x8, 0xf1921e04
                  li x9, 0xa551247f
                  li x10, 0xe2a90995
                  li x11, 0x80000000
                  li x14, 0x80000000
                  li x15, 0xc
                  li x16, 0x0
                  li x17, 0x8
                  li x18, 0xa083f312
                  li x19, 0x80000000
                  li x20, 0x5
                  li x21, 0x0
                  li x22, 0x60e0dbfd
                  li x23, 0x0
                  li x24, 0x9
                  li x25, 0x7e6a229e
                  li x26, 0xfe02b342
                  li x27, 0x4a45113b
                  li x28, 0xf8d2ebf6
                  li x29, 0x5
                  li x30, 0x80000000
                  li x31, 0xf4b85b42
                  la x12, user_stack_end
main:             li         s0, 0x0 #start riscv_int_numeric_corner_stream_39
                  li         s9, 0x55c5ec2
                  li         a0, 0x80000000
                  li         ra, 0xffffffff
                  li         s11, 0xffffffff
                  li         t3, 0x509311f5
                  li         t6, 0x0
                  li         a6, 0xffffffff
                  li         s1, 0x80000000
                  li         a1, 0xffffffff
                  nop
                  sub        t3, s0, t3
                  add        ra, a6, s9
                  add        ra, a6, s9
                  nop
                  addi       ra, ra, 999
                  remu       t6, s1, s0
                  sub        t3, s0, t3
                  auipc      t6, 688967
                  add        ra, a6, s9
                  remu       t6, s1, s0
                  sub        t3, s0, t3
                  nop
                  nop
                  addi       ra, ra, 999
                  mul        t3, t3, t3
                  addi       ra, ra, 999
                  mul        t3, t3, t3
                  auipc      t6, 688967
                  lui        s0, 195546
                  mulhsu     a1, s9, a6
                  rem        ra, t6, ra
                  nop
                  nop
                  mul        t3, t3, t3
                  auipc      t6, 688967
                  nop
                  lui        s0, 195546
                  lui        s0, 195546 #end riscv_int_numeric_corner_stream_39
                  li         s10, 0x3b187182 #start riscv_int_numeric_corner_stream_17
                  li         a0, 0xffffffff
                  li         a4, 0x80000000
                  li         s11, 0x0
                  li         t3, 0xffffffff
                  li         gp, 0x6bf008b9
                  li         s5, 0x82079a19
                  li         s6, 0x4cc65169
                  li         t5, 0x80000000
                  li         s2, 0xa39db5a2
                  addi       s5, s5, 999
                  nop
                  nop
                  mulhu      t3, gp, s5
                  mulh       s11, a4, t3
                  auipc      t5, 688967
                  mulh       s11, a4, t3
                  add        t3, t3, t3
                  nop
                  lui        a0, 195546
                  mulhu      t3, gp, s5
                  lui        a0, 195546
                  mulhsu     a4, s6, a0
                  nop
                  rem        s5, a0, gp #end riscv_int_numeric_corner_stream_17
                  li         s11, 0xfa5b47ab #start riscv_int_numeric_corner_stream_11
                  li         s6, 0x80000000
                  li         gp, 0x2c06b99d
                  li         t6, 0x80000000
                  li         a6, 0x0
                  li         a7, 0x0
                  li         sp, 0x80000000
                  li         t1, 0x0
                  li         ra, 0x235c6d08
                  li         s1, 0x757584ff
                  addi       ra, s6, 999
                  sub        a7, a6, t1
                  divu       a7, s11, a7
                  mulhu      s1, t1, a6
                  nop
                  mul        t1, s11, s6
                  auipc      t6, 688967
                  nop
                  mulhsu     s1, t1, a6
                  mulhsu     s1, t1, a6
                  nop
                  nop
                  rem        s6, a6, s1
                  sub        a7, a6, t1
                  nop
                  mulhu      s1, t1, a6
                  addi       ra, s6, 999
                  nop
                  sub        a7, a6, t1
                  mulhu      s1, t1, a6
                  mulhsu     s1, t1, a6
                  nop #end riscv_int_numeric_corner_stream_11
                  li         a1, 0x15dda8f2 #start riscv_int_numeric_corner_stream_27
                  li         ra, 0x89e65545
                  li         s6, 0x80000000
                  li         t4, 0x80000000
                  li         s9, 0xc70d87b5
                  li         t6, 0xaa63dcb9
                  li         t1, 0xb3603135
                  li         a7, 0x80000000
                  li         s3, 0xf0bfbdcf
                  li         t5, 0x1ca1a70e
                  rem        t5, t1, a1
                  sub        t1, s9, s6
                  mulhu      a7, s3, a7
                  divu       a7, a1, t4
                  auipc      t6, 688967
                  mulh       s6, s3, t4
                  mulhu      a7, s3, a7
                  div        ra, s3, t1
                  lui        ra, 195546
                  sub        t1, s9, s6
                  nop
                  remu       s6, a1, t1
                  mul        t1, t4, t5
                  add        t5, s6, t4
                  mul        t1, t4, t5
                  mul        t1, t4, t5
                  mul        t1, t4, t5
                  sub        t1, s9, s6
                  addi       ra, s6, 999
                  nop
                  mulhu      a7, s3, a7
                  sub        t1, s9, s6 #end riscv_int_numeric_corner_stream_27
                  li         s11, 0xffffffff #start riscv_int_numeric_corner_stream_25
                  li         s1, 0xffffffff
                  li         sp, 0xffffffff
                  li         a5, 0x0
                  li         t0, 0x5238ad9d
                  li         t6, 0x0
                  li         s8, 0xffffffff
                  li         a7, 0x0
                  li         t3, 0x80000000
                  li         a4, 0xf87a1de6
                  addi       a7, t0, 999
                  mulh       a7, a7, a7
                  nop
                  mulhu      sp, s11, s1
                  addi       a7, t0, 999
                  mulhsu     a5, s8, a7
                  remu       t6, a4, s8
                  mulhsu     a5, s8, a7
                  remu       t6, a4, s8
                  add        a7, sp, a7
                  auipc      t6, 688967
                  nop
                  nop
                  mul        a4, t3, t3
                  nop #end riscv_int_numeric_corner_stream_25
                  li         a1, 0x0 #start riscv_int_numeric_corner_stream_30
                  li         t0, 0x80000000
                  li         s3, 0x7309f479
                  li         ra, 0x80000000
                  li         a5, 0xffffffff
                  li         a6, 0x80000000
                  li         s8, 0x9f9ee8d2
                  li         a0, 0xbdf31cb0
                  li         s0, 0xe7fb0dd4
                  li         sp, 0x80000000
                  mulhsu     s0, t0, a6
                  mulh       s3, s8, s8
                  nop
                  nop
                  mulhsu     s0, t0, a6
                  sub        a6, s0, t0
                  nop
                  mul        t0, a5, a0
                  mulh       s3, s8, s8
                  nop
                  add        s3, a1, a6
                  mul        t0, a5, a0
                  addi       a6, t0, 999
                  add        s3, a1, a6
                  divu       a6, a1, t0 #end riscv_int_numeric_corner_stream_30
                  li         t5, 0x8abcfca2 #start riscv_int_numeric_corner_stream_12
                  li         s6, 0x80000000
                  li         t3, 0x4427d9eb
                  li         t2, 0x80000000
                  li         t6, 0xffffffff
                  li         s2, 0x0
                  li         s7, 0x0
                  li         a5, 0x0
                  li         ra, 0xbd2bbe3c
                  li         s3, 0x0
                  nop
                  sub        ra, t3, s6
                  rem        t5, t3, a5
                  lui        ra, 195546
                  lui        ra, 195546
                  add        t3, t3, t3
                  rem        t5, t3, a5
                  mulhu      t3, a5, ra
                  div        s2, s2, s2
                  nop
                  remu       t2, s2, s2
                  sub        ra, t3, s6
                  mulhsu     t3, ra, s2
                  sub        ra, t3, s6
                  add        t3, t3, t3
                  lui        ra, 195546
                  nop
                  divu       s7, s2, ra
                  remu       t2, s2, s2
                  remu       t2, s2, s2
                  nop
                  divu       s7, s2, ra
                  add        t3, t3, t3
                  auipc      t6, 688967
                  mulhsu     t3, ra, s2
                  add        t3, t3, t3
                  auipc      t6, 688967
                  mulh       a5, t3, t3
                  addi       t2, s6, 999 #end riscv_int_numeric_corner_stream_12
                  li         a0, 0xef977b58 #start riscv_int_numeric_corner_stream_34
                  li         a7, 0x0
                  li         t5, 0xffffffff
                  li         a4, 0xffffffff
                  li         a6, 0xdb294899
                  li         t0, 0xffffffff
                  li         t3, 0x80000000
                  li         t4, 0xbc8a01e6
                  li         t6, 0x80000000
                  li         s9, 0x80000000
                  addi       a6, t0, 999
                  divu       a0, a0, t4
                  auipc      t6, 688967
                  mulhu      a6, t0, t0
                  mulhsu     a0, s9, a7
                  divu       a0, a0, t4
                  addi       a6, t0, 999
                  addi       a6, t0, 999
                  divu       a0, a0, t4
                  remu       t0, a0, a0
                  mulhsu     a0, s9, a7
                  add        t5, a0, a7
                  divu       a0, a0, t4
                  mulhu      a6, t0, t0
                  mul        s9, t0, t3
                  sub        a0, t3, a4
                  mulh       t0, t6, a7
                  sub        a0, t3, a4
                  sub        a0, t3, a4
                  nop
                  nop
                  auipc      t6, 688967
                  sub        a0, t3, a4
                  sub        a0, t3, a4
                  addi       a6, t0, 999
                  sub        a0, t3, a4 #end riscv_int_numeric_corner_stream_34
                  li         s9, 0x80000000 #start riscv_int_numeric_corner_stream_2
                  li         a6, 0xdb0dc444
                  li         s6, 0xc82e2f21
                  li         t4, 0x80000000
                  li         a7, 0x3f56d519
                  li         t2, 0xffffffff
                  li         s3, 0x7d0bc5b6
                  li         a0, 0xffffffff
                  li         a5, 0x0
                  li         t0, 0xffffffff
                  nop
                  add        s3, a0, a7
                  auipc      t4, 688967
                  sub        t4, a6, s6
                  div        t0, a6, a0
                  mulh       s9, t2, a7
                  lui        t0, 195546
                  add        s3, a0, a7
                  mulhsu     a0, s9, s3
                  mul        t0, t4, s6
                  mul        t0, t4, s6
                  remu       a6, s3, a0
                  nop
                  mulhsu     a0, s9, s3
                  add        s3, a0, a7
                  mul        t0, t4, s6
                  auipc      t4, 688967
                  nop
                  addi       a6, s6, 999
                  nop
                  auipc      t4, 688967
                  nop
                  sub        t4, a6, s6
                  lui        t0, 195546
                  sub        t4, a6, s6
                  div        t0, a6, a0
                  addi       a6, s6, 999
                  add        s3, a0, a7 #end riscv_int_numeric_corner_stream_2
                  li         s8, 0x0 #start riscv_int_numeric_corner_stream_35
                  li         s0, 0x0
                  li         a5, 0x80000000
                  li         s2, 0x0
                  li         s1, 0x80000000
                  li         a4, 0x80000000
                  li         t6, 0x0
                  li         s11, 0x4c56e1cf
                  li         a6, 0x0
                  li         t5, 0x0
                  mulhsu     a5, s8, s2
                  addi       a6, s2, 999
                  mulhu      s0, a4, s8
                  nop
                  nop
                  mulhsu     a5, s8, s2
                  nop
                  addi       a6, s2, 999
                  nop
                  mulh       t6, a4, s1
                  mulhu      s0, a4, s8
                  lui        s0, 195546
                  remu       a5, a5, s0
                  nop
                  mulh       t6, a4, s1
                  add        s2, a6, s8
                  mulhsu     a5, s8, s2
                  nop
                  nop
                  mulhsu     a5, s8, s2
                  auipc      t6, 688967
                  div        s2, s2, a4
                  mul        a4, s1, s8
                  auipc      t6, 688967 #end riscv_int_numeric_corner_stream_35
                  li         t3, 0xffffffff #start riscv_int_numeric_corner_stream_5
                  li         ra, 0x80000000
                  li         s6, 0x80000000
                  li         t5, 0xffffffff
                  li         a5, 0x0
                  li         gp, 0xffffffff
                  li         a7, 0x0
                  li         s0, 0xffffffff
                  li         t2, 0x7246594c
                  li         s7, 0x0
                  auipc      t5, 688967
                  mulhsu     t5, a7, a7
                  mulhsu     t5, a7, a7
                  div        ra, s0, t5
                  addi       s0, t2, 999
                  addi       s0, t2, 999
                  mul        s7, t2, s6
                  sub        t3, t3, s6
                  sub        t3, t3, s6
                  divu       a7, gp, a7
                  addi       s0, t2, 999
                  add        ra, a5, a7
                  auipc      t5, 688967
                  nop
                  remu       a5, gp, s0
                  lui        ra, 195546
                  div        ra, s0, t5
                  remu       a5, gp, s0
                  mulhsu     t5, a7, a7
                  mulh       a7, a7, a7
                  add        ra, a5, a7
                  sub        t3, t3, s6
                  add        ra, a5, a7
                  divu       a7, gp, a7
                  add        ra, a5, a7
                  mulhsu     t5, a7, a7
                  sub        t3, t3, s6
                  div        ra, s0, t5
                  mulhu      s6, gp, s0 #end riscv_int_numeric_corner_stream_5
                  li         tp, 0x80000000 #start riscv_int_numeric_corner_stream_8
                  li         sp, 0x57428f37
                  li         t3, 0x80000000
                  li         s11, 0x0
                  li         t0, 0xffffffff
                  li         s5, 0x0
                  li         a4, 0x0
                  li         s0, 0xcc190b07
                  li         t4, 0xffffffff
                  li         s10, 0xffffffff
                  mul        s11, t4, s10
                  lui        tp, 195546
                  sub        sp, s0, a4
                  mulhu      tp, s11, t0
                  remu       t4, a4, s0
                  nop
                  add        s5, a4, t3
                  nop
                  div        sp, s11, a4
                  rem        s0, t4, s0
                  nop
                  auipc      t4, 688967
                  lui        tp, 195546
                  nop
                  nop
                  auipc      t4, 688967
                  sub        sp, s0, a4
                  auipc      t4, 688967
                  rem        s0, t4, s0
                  nop #end riscv_int_numeric_corner_stream_8
                  li         a7, 0xffffffff #start riscv_int_numeric_corner_stream_26
                  li         a4, 0xc4356872
                  li         a5, 0x0
                  li         t4, 0x80000000
                  li         s6, 0x49020efb
                  li         s0, 0x6825c196
                  li         tp, 0xd8b9438b
                  li         t2, 0x80000000
                  li         s9, 0xffffffff
                  li         t1, 0xffffffff
                  rem        a7, tp, s0
                  remu       t2, s0, s0
                  add        s9, s0, s9
                  nop
                  add        s9, s0, s9
                  nop
                  nop
                  remu       t2, s0, s0
                  nop
                  mulhsu     a5, s0, s0
                  nop
                  mul        t4, s6, s6
                  divu       a7, a4, t4
                  mul        t4, s6, s6
                  nop
                  mulhu      tp, a5, s0
                  nop
                  addi       tp, s6, 999
                  mulh       s6, s9, t4 #end riscv_int_numeric_corner_stream_26
                  li         s6, 0x1b5f179d #start riscv_int_numeric_corner_stream_7
                  li         s3, 0x80000000
                  li         s1, 0x0
                  li         s2, 0x80000000
                  li         a6, 0x0
                  li         s11, 0x80000000
                  li         t3, 0x80000000
                  li         s0, 0x98e2d452
                  li         s7, 0x0
                  li         s10, 0x80000000
                  add        s1, s10, a6
                  lui        s0, 195546
                  mulhsu     s1, s6, s2
                  nop
                  nop
                  divu       a6, s0, s1
                  addi       a6, s7, 999
                  add        s1, s10, a6
                  mulh       t3, s11, t3
                  mulh       t3, s11, t3
                  nop
                  addi       a6, s7, 999
                  sub        t3, a6, s6
                  remu       a6, s1, s0
                  lui        s0, 195546
                  lui        s0, 195546
                  nop
                  nop
                  lui        s0, 195546
                  mulhu      s0, s7, s1
                  add        s1, s10, a6
                  mulhu      s0, s7, s1
                  sub        t3, a6, s6
                  addi       a6, s7, 999
                  add        s1, s10, a6
                  remu       a6, s1, s0 #end riscv_int_numeric_corner_stream_7
                  li         t1, 0xffffffff #start riscv_int_numeric_corner_stream_19
                  li         a7, 0xffffffff
                  li         a4, 0x0
                  li         t0, 0x80000000
                  li         t5, 0x75f28eac
                  li         s10, 0x76ad73b
                  li         a5, 0xdbbd3320
                  li         tp, 0x0
                  li         ra, 0xffffffff
                  li         t3, 0x80000000
                  mulhsu     s10, s10, a7
                  mulhsu     s10, s10, a7
                  rem        s10, a5, a4
                  nop
                  nop
                  lui        ra, 195546
                  div        ra, a5, a4
                  nop
                  auipc      t5, 688967
                  add        s10, a4, a7
                  mulhsu     s10, s10, a7
                  nop
                  divu       t0, s10, a7
                  nop
                  divu       t0, s10, a7
                  mul        ra, t0, s10 #end riscv_int_numeric_corner_stream_19
                  li         s2, 0x0 #start riscv_int_numeric_corner_stream_33
                  li         tp, 0x80000000
                  li         s5, 0x80000000
                  li         s0, 0x0
                  li         t3, 0xffffffff
                  li         sp, 0x0
                  li         s6, 0x80000000
                  li         t4, 0x0
                  li         s7, 0x46a46daf
                  li         t5, 0x80000000
                  add        t3, t5, t3
                  addi       sp, s5, 999
                  div        s5, s2, sp
                  mulhu      sp, s2, s0
                  addi       sp, s5, 999
                  add        t3, t5, t3
                  sub        s5, s5, tp
                  nop
                  auipc      t4, 688967
                  nop
                  nop
                  auipc      t4, 688967
                  lui        tp, 195546
                  nop
                  rem        sp, tp, s0 #end riscv_int_numeric_corner_stream_33
                  li         t4, 0xffffffff #start riscv_int_numeric_corner_stream_1
                  li         s2, 0x80000000
                  li         a5, 0x80000000
                  li         sp, 0x80000000
                  li         a6, 0x80000000
                  li         gp, 0x0
                  li         s11, 0x0
                  li         s0, 0x80000000
                  li         s3, 0x0
                  li         s8, 0x80000000
                  mulhu      s0, a5, s0
                  lui        s0, 195546
                  lui        s0, 195546
                  nop
                  mulh       gp, s3, t4
                  div        s3, s2, sp
                  nop
                  nop
                  mul        a5, t4, s8
                  mul        a5, t4, s8
                  divu       s2, s0, t4
                  sub        sp, s0, a5
                  mulhu      s0, a5, s0
                  div        s3, s2, sp
                  add        sp, a6, s8
                  add        sp, a6, s8
                  nop
                  mulhu      s0, a5, s0
                  div        s3, s2, sp
                  lui        s0, 195546
                  nop
                  nop
                  nop
                  sub        sp, s0, a5
                  mul        a5, t4, s8
                  add        sp, a6, s8
                  nop
                  sub        sp, s0, a5 #end riscv_int_numeric_corner_stream_1
                  li         a4, 0xffffffff #start riscv_int_numeric_corner_stream_9
                  li         gp, 0x7dbecfed
                  li         s6, 0x80000000
                  li         s9, 0xffffffff
                  li         t5, 0xffffffff
                  li         sp, 0x0
                  li         s1, 0x0
                  li         a5, 0x0
                  li         t0, 0xffffffff
                  li         t1, 0x1d9b4eae
                  mulhu      sp, t0, t0
                  mulh       t5, s9, s9
                  addi       t0, s6, 999
                  mul        s1, gp, a4
                  lui        t0, 195546
                  auipc      t5, 688967
                  lui        t0, 195546
                  add        t5, s6, t0
                  auipc      t5, 688967
                  div        s9, t0, a4
                  lui        t0, 195546
                  add        t5, s6, t0
                  divu       t0, sp, s9
                  lui        t0, 195546
                  divu       t0, sp, s9
                  nop
                  nop
                  remu       t0, sp, sp
                  addi       t0, s6, 999
                  lui        t0, 195546
                  nop
                  lui        t0, 195546
                  div        s9, t0, a4
                  mulhu      sp, t0, t0
                  addi       t0, s6, 999
                  auipc      t5, 688967
                  mulh       t5, s9, s9
                  divu       t0, sp, s9 #end riscv_int_numeric_corner_stream_9
                  li         a1, 0x69328841 #start riscv_int_numeric_corner_stream_32
                  li         tp, 0xa511979b
                  li         s8, 0x52bbaa18
                  li         a5, 0x96eb2b95
                  li         t0, 0x0
                  li         s0, 0x80000000
                  li         s5, 0x90ae797a
                  li         t5, 0x0
                  li         t1, 0xffffffff
                  li         a0, 0x80000000
                  add        t0, t5, s8
                  add        t0, t5, s8
                  div        a0, a5, t1
                  divu       s5, a1, s5
                  remu       tp, a1, a0
                  rem        s5, tp, s0
                  sub        t1, s0, t1
                  sub        t1, s0, t1
                  sub        t1, s0, t1
                  lui        tp, 195546
                  mulh       t5, s5, s5
                  mulh       t5, s5, s5
                  lui        tp, 195546
                  lui        tp, 195546
                  nop #end riscv_int_numeric_corner_stream_32
                  remu       s5, s11, t1
                  mul        sp, s9, s11
                  remu       s5, s11, t1
                  xori       a4, t0, 974
                  andi       s8, t1, -26
                  slli       s11, gp, 14
                  add        s7, s5, a6
                  c.xor      a1, a2
                  c.add      t1, a1
                  auipc      t6, 688967
                  c.slli     t4, 28
                  div        t3, t1, t5
                  sub        s9, s6, s5
                  mulhu      tp, s3, a4
                  c.nop
                  c.srli     a0, 25
                  srl        a0, s2, a0
                  slli       s11, gp, 14
                  mulh       s11, s1, s9
                  sra        s1, t3, s1
                  c.mv       a1, s5
                  sll        t3, s7, a3
                  sra        s1, t3, s1
                  slt        t1, a1, a4
                  slli       s11, gp, 14
                  add        s7, s5, a6
                  c.addi16sp sp, 16
                  srai       s10, s1, 24
                  mulhu      tp, s3, a4
                  sra        s1, t3, s1
                  andi       s8, t1, -26
                  remu       s5, s11, t1
                  c.and      a0, s0
                  c.addi     s1, 6
                  mul        sp, s9, s11
                  sltu       t2, s1, t1
                  c.lui      a0, 24
                  mulhsu     gp, a1, s1
                  srli       s8, t6, 19
                  andi       s8, t1, -26
                  nop
                  li         s8, 0x70979df7 #start riscv_int_numeric_corner_stream_38
                  li         t6, 0x80000000
                  li         t4, 0xab935de3
                  li         s2, 0xffffffff
                  li         s11, 0xffffffff
                  li         tp, 0x0
                  li         s1, 0x80000000
                  li         s10, 0xffffffff
                  li         t2, 0x0
                  li         a1, 0x0
                  addi       tp, t2, 999
                  add        s1, s10, s8
                  lui        tp, 195546
                  add        s1, s10, s8
                  auipc      t6, 688967
                  mulh       t2, t4, t4
                  mulhu      a1, s10, s1
                  mul        tp, t2, s2
                  remu       t4, t2, s8
                  lui        tp, 195546
                  nop
                  sub        t4, s8, tp
                  remu       t4, t2, s8
                  addi       tp, t2, 999
                  mulh       t2, t4, t4 #end riscv_int_numeric_corner_stream_38
                  div        t3, t1, t5
                  rem        s0, a3, a2
                  or         s0, a2, a0
                  xor        t4, s3, t3
                  sltu       t2, s1, t1
                  srl        a0, s2, a0
                  sltu       t2, s1, t1
                  c.srli     a0, 25
                  sll        t3, s7, a3
                  and        a1, t3, a6
                  andi       s8, t1, -26
                  c.lui      a0, 24
                  div        t3, t1, t5
                  c.addi     s1, 6
                  c.add      t1, a1
                  c.addi     s1, 6
                  c.li       a7, 27
                  sub        s9, s6, s5
                  add        s7, s5, a6
                  c.mv       a1, s5
                  sll        t3, s7, a3
                  remu       s5, s11, t1
                  c.addi16sp sp, 16
                  c.addi16sp sp, 16
                  slt        t1, a1, a4
                  mul        sp, s9, s11
                  c.addi4spn a4, sp, 288
                  ori        t5, t2, 999
                  c.add      t1, a1
                  c.lui      a0, 24
                  divu       sp, ra, t0
                  slt        t1, a1, a4
                  c.lui      a0, 24
                  or         s0, a2, a0
                  sra        s1, t3, s1
                  add        s7, s5, a6
                  sll        t3, s7, a3
                  sltu       t2, s1, t1
                  andi       s8, t1, -26
                  sll        t3, s7, a3
                  slt        t1, a1, a4
                  c.xor      a1, a2
                  andi       s8, t1, -26
                  srl        a0, s2, a0
                  and        a1, t3, a6
                  andi       s8, t1, -26
                  c.lui      a0, 24
                  srli       s8, t6, 19
                  c.lui      a0, 24
                  lui        zero, 195546
                  c.lui      a0, 24
                  lui        zero, 195546
                  srli       s8, t6, 19
                  mulhu      tp, s3, a4
                  c.xor      a1, a2
                  mulhu      tp, s3, a4
                  c.srli     a0, 25
                  c.slli     t4, 28
                  mulhsu     gp, a1, s1
                  c.andi     a5, -1
                  c.or       a5, a1
                  c.srai     s0, 31
                  or         s0, a2, a0
                  sll        t3, s7, a3
                  div        t3, t1, t5
                  and        a1, t3, a6
                  c.add      t1, a1
                  sll        t3, s7, a3
                  sra        s1, t3, s1
                  mulh       s11, s1, s9
                  nop
                  rem        s0, a3, a2
                  c.lui      a0, 24
                  srai       s10, s1, 24
                  sll        t3, s7, a3
                  xor        t4, s3, t3
                  c.mv       a1, s5
                  c.mv       a1, s5
                  c.andi     a5, -1
                  c.and      a0, s0
                  c.nop
                  c.sub      s1, a4
                  add        s7, s5, a6
                  sub        s9, s6, s5
                  c.xor      a1, a2
                  auipc      t6, 688967
                  sra        s1, t3, s1
                  div        t3, t1, t5
                  rem        s0, a3, a2
                  ori        t5, t2, 999
                  c.add      t1, a1
                  divu       sp, ra, t0
                  c.mv       a1, s5
                  c.li       a7, 27
                  c.slli     t4, 28
                  xori       a4, t0, 974
                  xori       a4, t0, 974
                  c.addi     s1, 6
                  add        s7, s5, a6
                  and        a1, t3, a6
                  mulhsu     gp, a1, s1
                  remu       s5, s11, t1
                  c.addi4spn a4, sp, 288
                  sltu       t2, s1, t1
                  c.addi16sp sp, 16
                  div        t3, t1, t5
                  slti       tp, t6, 301
                  sll        t3, s7, a3
                  sra        s1, t3, s1
                  nop
                  slti       tp, t6, 301
                  sll        t3, s7, a3
                  div        t3, t1, t5
                  addi       a7, t2, -784
                  c.mv       a1, s5
                  c.and      a0, s0
                  sltu       t2, s1, t1
                  sra        s1, t3, s1
                  c.addi4spn a4, sp, 288
                  c.li       a7, 27
                  sub        s9, s6, s5
                  c.li       a7, 27
                  c.addi4spn a4, sp, 288
                  c.srai     s0, 31
                  c.addi     s1, 6
                  add        s7, s5, a6
                  c.li       a7, 27
                  sltiu      s6, ra, 913
                  slli       s11, gp, 14
                  srl        a0, s2, a0
                  or         s0, a2, a0
                  srai       s10, s1, 24
                  c.and      a0, s0
                  ori        t5, t2, 999
                  mulh       s11, s1, s9
                  rem        s0, a3, a2
                  andi       s8, t1, -26
                  andi       s8, t1, -26
                  c.nop
                  c.li       a7, 27
                  sra        s1, t3, s1
                  c.or       a5, a1
                  srli       s8, t6, 19
                  c.add      t1, a1
                  sltu       t2, s1, t1
                  slt        t1, a1, a4
                  mulh       s11, s1, s9
                  nop
                  mulhsu     gp, a1, s1
                  nop
                  c.li       a7, 27
                  c.slli     t4, 28
                  c.srli     a0, 25
                  mul        sp, s9, s11
                  c.srli     a0, 25
                  mulhu      tp, s3, a4
                  mulhsu     gp, a1, s1
                  slli       s11, gp, 14
                  mulh       s11, s1, s9
                  xori       a4, t0, 974
                  c.li       a7, 27
                  divu       sp, ra, t0
                  c.srli     a0, 25
                  auipc      t6, 688967
                  sub        s9, s6, s5
                  slt        t1, a1, a4
                  andi       s8, t1, -26
                  xor        t4, s3, t3
                  c.srai     s0, 31
                  c.slli     t4, 28
                  ori        t5, t2, 999
                  ori        t5, t2, 999
                  div        t3, t1, t5
                  c.addi16sp sp, 16
                  sub        s9, s6, s5
                  divu       sp, ra, t0
                  c.add      t1, a1
                  and        a1, t3, a6
                  nop
                  c.slli     t4, 28
                  lui        zero, 195546
                  c.nop
                  c.or       a5, a1
                  c.nop
                  c.add      t1, a1
                  c.slli     t4, 28
                  slt        t1, a1, a4
                  sll        t3, s7, a3
                  sra        s1, t3, s1
                  sll        t3, s7, a3
                  srai       s10, s1, 24
                  c.lui      a0, 24
                  sltiu      s6, ra, 913
                  nop
                  c.addi     s1, 6
                  c.addi4spn a4, sp, 288
                  ori        t5, t2, 999
                  add        s7, s5, a6
                  srli       s8, t6, 19
                  srli       s8, t6, 19
                  mulh       s11, s1, s9
                  c.andi     a5, -1
                  c.or       a5, a1
                  addi       a7, t2, -784
                  addi       a7, t2, -784
                  sltiu      s6, ra, 913
                  andi       s8, t1, -26
                  mulhsu     gp, a1, s1
                  remu       s5, s11, t1
                  xor        t4, s3, t3
                  c.addi4spn a4, sp, 288
                  slli       s11, gp, 14
                  andi       s8, t1, -26
                  slt        t1, a1, a4
                  c.nop
                  sra        s1, t3, s1
                  c.li       a7, 27
                  add        s7, s5, a6
                  c.sub      s1, a4
                  sll        t3, s7, a3
                  sll        t3, s7, a3
                  mulhu      tp, s3, a4
                  divu       sp, ra, t0
                  slti       tp, t6, 301
                  c.srai     s0, 31
                  c.add      t1, a1
                  c.srai     s0, 31
                  c.sub      s1, a4
                  slt        t1, a1, a4
                  c.sub      s1, a4
                  addi       a7, t2, -784
                  c.slli     t4, 28
                  sra        s1, t3, s1
                  c.mv       a1, s5
                  c.li       a7, 27
                  or         s0, a2, a0
                  sltiu      s6, ra, 913
                  slt        t1, a1, a4
                  c.addi16sp sp, 16
                  sll        t3, s7, a3
                  c.xor      a1, a2
                  nop
                  slt        t1, a1, a4
                  srai       s10, s1, 24
                  sra        s1, t3, s1
                  add        s7, s5, a6
                  c.add      t1, a1
                  mulhu      tp, s3, a4
                  c.addi     s1, 6
                  sltu       t2, s1, t1
                  addi       a7, t2, -784
                  c.mv       a1, s5
                  c.li       a7, 27
                  div        t3, t1, t5
                  c.srli     a0, 25
                  rem        s0, a3, a2
                  rem        s0, a3, a2
                  nop
                  c.li       a7, 27
                  divu       sp, ra, t0
                  c.and      a0, s0
                  auipc      t6, 688967
                  c.and      a0, s0
                  c.srai     s0, 31
                  srl        a0, s2, a0
                  c.xor      a1, a2
                  rem        s0, a3, a2
                  sll        t3, s7, a3
                  add        s7, s5, a6
                  sltu       t2, s1, t1
                  sltu       t2, s1, t1
                  mulh       s11, s1, s9
                  c.and      a0, s0
                  remu       s5, s11, t1
                  ori        t5, t2, 999
                  c.mv       a1, s5
                  sll        t3, s7, a3
                  mulh       s11, s1, s9
                  div        t3, t1, t5
                  mul        sp, s9, s11
                  c.srai     s0, 31
                  c.xor      a1, a2
                  slli       s11, gp, 14
                  and        a1, t3, a6
                  c.nop
                  nop
                  srli       s8, t6, 19
                  xori       a4, t0, 974
                  add        s7, s5, a6
                  c.slli     t4, 28
                  sra        s1, t3, s1
                  c.srli     a0, 25
                  slti       tp, t6, 301
                  mulhsu     gp, a1, s1
                  remu       s5, s11, t1
                  c.sub      s1, a4
                  or         s0, a2, a0
                  xori       a4, t0, 974
                  divu       sp, ra, t0
                  c.li       a7, 27
                  slli       s11, gp, 14
                  sltu       t2, s1, t1
                  sltiu      s6, ra, 913
                  c.lui      a0, 24
                  remu       s5, s11, t1
                  mulh       s11, s1, s9
                  c.sub      s1, a4
                  srl        a0, s2, a0
                  slli       s11, gp, 14
                  ori        t5, t2, 999
                  c.mv       a1, s5
                  c.or       a5, a1
                  slti       tp, t6, 301
                  c.sub      s1, a4
                  c.and      a0, s0
                  c.andi     a5, -1
                  c.andi     a5, -1
                  c.li       a7, 27
                  mulhu      tp, s3, a4
                  mulhu      tp, s3, a4
                  c.addi4spn a4, sp, 288
                  slli       s11, gp, 14
                  c.add      t1, a1
                  sll        t3, s7, a3
                  slli       s11, gp, 14
                  mulhsu     gp, a1, s1
                  srai       s10, s1, 24
                  mulhu      tp, s3, a4
                  xori       a4, t0, 974
                  slti       tp, t6, 301
                  c.and      a0, s0
                  c.addi     s1, 6
                  divu       sp, ra, t0
                  c.add      t1, a1
                  c.add      t1, a1
                  nop
                  c.and      a0, s0
                  srli       s8, t6, 19
                  andi       s8, t1, -26
                  or         s0, a2, a0
                  mulhu      tp, s3, a4
                  sll        t3, s7, a3
                  c.mv       a1, s5
                  srl        a0, s2, a0
                  div        t3, t1, t5
                  lui        zero, 195546
                  c.li       a7, 27
                  c.addi16sp sp, 16
                  c.addi     s1, 6
                  auipc      t6, 688967
                  mulhsu     gp, a1, s1
                  nop
                  slt        t1, a1, a4
                  ori        t5, t2, 999
                  c.or       a5, a1
                  rem        s0, a3, a2
                  c.sub      s1, a4
                  andi       s8, t1, -26
                  c.mv       a1, s5
                  srli       s8, t6, 19
                  c.add      t1, a1
                  sltu       t2, s1, t1
                  xor        t4, s3, t3
                  sltiu      s6, ra, 913
                  srli       s8, t6, 19
                  c.slli     t4, 28
                  sub        s9, s6, s5
                  c.xor      a1, a2
                  c.xor      a1, a2
                  slti       tp, t6, 301
                  nop
                  mulhu      tp, s3, a4
                  auipc      t6, 688967
                  xori       a4, t0, 974
                  c.addi4spn a4, sp, 288
                  c.sub      s1, a4
                  slt        t1, a1, a4
                  addi       a7, t2, -784
                  c.nop
                  slti       tp, t6, 301
                  srl        a0, s2, a0
                  c.xor      a1, a2
                  divu       sp, ra, t0
                  srai       s10, s1, 24
                  div        t3, t1, t5
                  div        t3, t1, t5
                  divu       sp, ra, t0
                  c.nop
                  lui        zero, 195546
                  xor        t4, s3, t3
                  andi       s8, t1, -26
                  c.or       a5, a1
                  auipc      t6, 688967
                  lui        zero, 195546
                  rem        s0, a3, a2
                  addi       a7, t2, -784
                  c.lui      a0, 24
                  c.andi     a5, -1
                  slli       s11, gp, 14
                  and        a1, t3, a6
                  remu       s5, s11, t1
                  c.addi4spn a4, sp, 288
                  mulhsu     gp, a1, s1
                  ori        t5, t2, 999
                  mulh       s11, s1, s9
                  c.addi     s1, 6
                  and        a1, t3, a6
                  add        s7, s5, a6
                  c.slli     t4, 28
                  mulhsu     gp, a1, s1
                  xor        t4, s3, t3
                  slt        t1, a1, a4
                  sra        s1, t3, s1
                  addi       a7, t2, -784
                  c.andi     a5, -1
                  c.xor      a1, a2
                  lui        zero, 195546
                  c.srai     s0, 31
                  c.nop
                  or         s0, a2, a0
                  c.nop
                  or         s0, a2, a0
                  auipc      t6, 688967
                  add        s7, s5, a6
                  c.add      t1, a1
                  c.addi4spn a4, sp, 288
                  slti       tp, t6, 301
                  c.xor      a1, a2
                  auipc      t6, 688967
                  mulhsu     gp, a1, s1
                  xori       a4, t0, 974
                  sra        s1, t3, s1
                  andi       s8, t1, -26
                  c.sub      s1, a4
                  nop
                  lui        zero, 195546
                  c.and      a0, s0
                  c.lui      a0, 24
                  mulh       s11, s1, s9
                  c.slli     t4, 28
                  c.srli     a0, 25
                  slli       s11, gp, 14
                  divu       sp, ra, t0
                  c.slli     t4, 28
                  xori       a4, t0, 974
                  c.addi4spn a4, sp, 288
                  sll        t3, s7, a3
                  c.addi4spn a4, sp, 288
                  sltiu      s6, ra, 913
                  addi       a7, t2, -784
                  nop
                  divu       sp, ra, t0
                  add        s7, s5, a6
                  sltiu      s6, ra, 913
                  c.addi16sp sp, 16
                  c.li       a7, 27
                  c.xor      a1, a2
                  c.addi16sp sp, 16
                  and        a1, t3, a6
                  c.srai     s0, 31
                  c.addi16sp sp, 16
                  addi       a7, t2, -784
                  c.srli     a0, 25
                  c.addi     s1, 6
                  c.addi16sp sp, 16
                  c.or       a5, a1
                  slli       s11, gp, 14
                  c.nop
                  slt        t1, a1, a4
                  c.addi16sp sp, 16
                  xor        t4, s3, t3
                  sub        s9, s6, s5
                  slt        t1, a1, a4
                  div        t3, t1, t5
                  divu       sp, ra, t0
                  remu       s5, s11, t1
                  rem        s0, a3, a2
                  slt        t1, a1, a4
                  addi       a7, t2, -784
                  and        a1, t3, a6
                  srl        a0, s2, a0
                  divu       sp, ra, t0
                  rem        s0, a3, a2
                  div        t3, t1, t5
                  xor        t4, s3, t3
                  srai       s10, s1, 24
                  andi       s8, t1, -26
                  slt        t1, a1, a4
                  sub        s9, s6, s5
                  c.li       a7, 27
                  div        t3, t1, t5
                  lui        zero, 195546
                  and        a1, t3, a6
                  c.nop
                  sub        s9, s6, s5
                  xor        t4, s3, t3
                  add        s7, s5, a6
                  c.andi     a5, -1
                  c.mv       a1, s5
                  c.add      t1, a1
                  rem        s0, a3, a2
                  xori       a4, t0, 974
                  c.and      a0, s0
                  xor        t4, s3, t3
                  c.srai     s0, 31
                  c.sub      s1, a4
                  rem        s0, a3, a2
                  nop
                  c.addi     s1, 6
                  c.sub      s1, a4
                  c.slli     t4, 28
                  sub        s9, s6, s5
                  c.mv       a1, s5
                  mulh       s11, s1, s9
                  mul        sp, s9, s11
                  xor        t4, s3, t3
                  sll        t3, s7, a3
                  mul        sp, s9, s11
                  div        t3, t1, t5
                  c.andi     a5, -1
                  mulhsu     gp, a1, s1
                  c.li       a7, 27
                  c.slli     t4, 28
                  divu       sp, ra, t0
                  auipc      t6, 688967
                  c.srai     s0, 31
                  c.addi16sp sp, 16
                  c.and      a0, s0
                  c.sub      s1, a4
                  sra        s1, t3, s1
                  xor        t4, s3, t3
                  c.and      a0, s0
                  slli       s11, gp, 14
                  c.slli     t4, 28
                  srl        a0, s2, a0
                  c.slli     t4, 28
                  slli       s11, gp, 14
                  xor        t4, s3, t3
                  lui        zero, 195546
                  addi       a7, t2, -784
                  c.srai     s0, 31
                  xor        t4, s3, t3
                  mulhsu     gp, a1, s1
                  c.mv       a1, s5
                  c.lui      a0, 24
                  c.lui      a0, 24
                  div        t3, t1, t5
                  c.li       a7, 27
                  sltiu      s6, ra, 913
                  mulhu      tp, s3, a4
                  slt        t1, a1, a4
                  lui        zero, 195546
                  sra        s1, t3, s1
                  srl        a0, s2, a0
                  auipc      t6, 688967
                  ori        t5, t2, 999
                  c.li       a7, 27
                  andi       s8, t1, -26
                  and        a1, t3, a6
                  rem        s0, a3, a2
                  c.srli     a0, 25
                  add        s7, s5, a6
                  sra        s1, t3, s1
                  or         s0, a2, a0
                  c.slli     t4, 28
                  xori       a4, t0, 974
                  c.srli     a0, 25
                  c.addi     s1, 6
                  c.xor      a1, a2
                  xori       a4, t0, 974
                  divu       sp, ra, t0
                  mulh       s11, s1, s9
                  c.addi     s1, 6
                  sll        t3, s7, a3
                  addi       a7, t2, -784
                  andi       s8, t1, -26
                  c.nop
                  srli       s8, t6, 19
                  mulh       s11, s1, s9
                  slt        t1, a1, a4
                  lui        zero, 195546
                  c.srai     s0, 31
                  c.li       a7, 27
                  sltiu      s6, ra, 913
                  sltu       t2, s1, t1
                  divu       sp, ra, t0
                  mulhu      tp, s3, a4
                  c.sub      s1, a4
                  c.srai     s0, 31
                  c.li       a7, 27
                  c.slli     t4, 28
                  c.srli     a0, 25
                  nop
                  and        a1, t3, a6
                  c.xor      a1, a2
                  xori       a4, t0, 974
                  c.xor      a1, a2
                  xori       a4, t0, 974
                  c.lui      a0, 24
                  remu       s5, s11, t1
                  or         s0, a2, a0
                  mulh       s11, s1, s9
                  c.add      t1, a1
                  sltiu      s6, ra, 913
                  slt        t1, a1, a4
                  sra        s1, t3, s1
                  mulhu      tp, s3, a4
                  c.srai     s0, 31
                  c.addi16sp sp, 16
                  remu       s5, s11, t1
                  c.addi4spn a4, sp, 288
                  rem        s0, a3, a2
                  and        a1, t3, a6
                  sub        s9, s6, s5
                  c.andi     a5, -1
                  divu       sp, ra, t0
                  c.addi4spn a4, sp, 288
                  mulh       s11, s1, s9
                  c.xor      a1, a2
                  sltu       t2, s1, t1
                  div        t3, t1, t5
                  srai       s10, s1, 24
                  lui        zero, 195546
                  c.srli     a0, 25
                  srli       s8, t6, 19
                  slli       s11, gp, 14
                  c.xor      a1, a2
                  mul        sp, s9, s11
                  div        t3, t1, t5
                  c.mv       a1, s5
                  c.addi16sp sp, 16
                  c.lui      a0, 24
                  c.or       a5, a1
                  c.lui      a0, 24
                  c.add      t1, a1
                  c.andi     a5, -1
                  li         s9, 0x3fdba535 #start riscv_int_numeric_corner_stream_22
                  li         s3, 0x4c21c560
                  li         a5, 0x80000000
                  li         a1, 0xa53a8937
                  li         s10, 0xd1b05e67
                  li         t0, 0xa5ee5d42
                  li         s1, 0x80000000
                  li         s11, 0xffffffff
                  li         s0, 0x0
                  li         s5, 0xf87dbd06
                  sub        s5, s5, t0
                  sub        s5, s5, t0
                  remu       s5, s3, s0
                  rem        s5, a5, s0
                  add        s1, s10, s9
                  lui        t0, 195546
                  addi       t0, s5, 999
                  addi       t0, s5, 999
                  nop
                  divu       s9, s10, s5
                  lui        t0, 195546
                  lui        t0, 195546
                  lui        t0, 195546
                  add        s1, s10, s9
                  nop
                  sub        s5, s5, t0
                  nop
                  nop
                  sub        s5, s5, t0
                  sub        s5, s5, t0
                  mulhsu     s0, s0, s3
                  auipc      s11, 688967
                  remu       s5, s3, s0
                  auipc      s11, 688967
                  addi       t0, s5, 999 #end riscv_int_numeric_corner_stream_22
                  addi       a7, t2, -784
                  c.srai     s0, 31
                  c.and      a0, s0
                  c.sub      s1, a4
                  ori        t5, t2, 999
                  c.and      a0, s0
                  mulhu      tp, s3, a4
                  c.srli     a0, 25
                  c.andi     a5, -1
                  mulh       s11, s1, s9
                  sub        s9, s6, s5
                  c.nop
                  slli       s11, gp, 14
                  sra        s1, t3, s1
                  lui        zero, 195546
                  c.or       a5, a1
                  mulhsu     gp, a1, s1
                  sll        t3, s7, a3
                  c.addi4spn a4, sp, 288
                  c.addi16sp sp, 16
                  lui        zero, 195546
                  c.xor      a1, a2
                  mulhsu     gp, a1, s1
                  auipc      t6, 688967
                  sltu       t2, s1, t1
                  sltu       t2, s1, t1
                  c.nop
                  andi       s8, t1, -26
                  sll        t3, s7, a3
                  add        s7, s5, a6
                  c.sub      s1, a4
                  c.nop
                  andi       s8, t1, -26
                  srl        a0, s2, a0
                  c.or       a5, a1
                  divu       sp, ra, t0
                  remu       s5, s11, t1
                  c.li       a7, 27
                  c.srai     s0, 31
                  c.lui      a0, 24
                  and        a1, t3, a6
                  auipc      t6, 688967
                  or         s0, a2, a0
                  sltu       t2, s1, t1
                  c.or       a5, a1
                  ori        t5, t2, 999
                  slli       s11, gp, 14
                  c.srli     a0, 25
                  auipc      t6, 688967
                  c.xor      a1, a2
                  c.and      a0, s0
                  c.srai     s0, 31
                  c.and      a0, s0
                  c.nop
                  slt        t1, a1, a4
                  sub        s9, s6, s5
                  sll        t3, s7, a3
                  c.li       a7, 27
                  slt        t1, a1, a4
                  c.addi     s1, 6
                  remu       s5, s11, t1
                  c.addi     s1, 6
                  mul        sp, s9, s11
                  addi       a7, t2, -784
                  c.srli     a0, 25
                  divu       sp, ra, t0
                  c.addi16sp sp, 16
                  xori       a4, t0, 974
                  srai       s10, s1, 24
                  c.li       a7, 27
                  ori        t5, t2, 999
                  sll        t3, s7, a3
                  xor        t4, s3, t3
                  c.add      t1, a1
                  sub        s9, s6, s5
                  div        t3, t1, t5
                  divu       sp, ra, t0
                  sra        s1, t3, s1
                  addi       a7, t2, -784
                  and        a1, t3, a6
                  rem        s0, a3, a2
                  c.add      t1, a1
                  c.slli     t4, 28
                  div        t3, t1, t5
                  remu       s5, s11, t1
                  rem        s0, a3, a2
                  or         s0, a2, a0
                  c.xor      a1, a2
                  addi       a7, t2, -784
                  and        a1, t3, a6
                  c.sub      s1, a4
                  c.or       a5, a1
                  c.srli     a0, 25
                  srli       s8, t6, 19
                  mulh       s11, s1, s9
                  slti       tp, t6, 301
                  addi       a7, t2, -784
                  srl        a0, s2, a0
                  add        s7, s5, a6
                  sub        s9, s6, s5
                  nop
                  sltiu      s6, ra, 913
                  c.xor      a1, a2
                  srli       s8, t6, 19
                  slli       s11, gp, 14
                  srai       s10, s1, 24
                  mulh       s11, s1, s9
                  c.slli     t4, 28
                  c.sub      s1, a4
                  sltu       t2, s1, t1
                  srl        a0, s2, a0
                  sltu       t2, s1, t1
                  xori       a4, t0, 974
                  mulh       s11, s1, s9
                  mulhu      tp, s3, a4
                  c.addi     s1, 6
                  c.addi16sp sp, 16
                  remu       s5, s11, t1
                  c.sub      s1, a4
                  srai       s10, s1, 24
                  or         s0, a2, a0
                  lui        zero, 195546
                  nop
                  c.xor      a1, a2
                  add        s7, s5, a6
                  ori        t5, t2, 999
                  slti       tp, t6, 301
                  sltu       t2, s1, t1
                  auipc      t6, 688967
                  rem        s0, a3, a2
                  mul        sp, s9, s11
                  xor        t4, s3, t3
                  c.add      t1, a1
                  c.sub      s1, a4
                  slli       s11, gp, 14
                  c.lui      a0, 24
                  xor        t4, s3, t3
                  c.srai     s0, 31
                  divu       sp, ra, t0
                  sltu       t2, s1, t1
                  c.srli     a0, 25
                  mulhsu     gp, a1, s1
                  c.sub      s1, a4
                  srai       s10, s1, 24
                  slt        t1, a1, a4
                  srai       s10, s1, 24
                  divu       sp, ra, t0
                  c.addi     s1, 6
                  sub        s9, s6, s5
                  c.slli     t4, 28
                  slti       tp, t6, 301
                  xor        t4, s3, t3
                  c.srli     a0, 25
                  divu       sp, ra, t0
                  sra        s1, t3, s1
                  c.add      t1, a1
                  slti       tp, t6, 301
                  c.addi4spn a4, sp, 288
                  c.addi16sp sp, 16
                  auipc      t6, 688967
                  c.sub      s1, a4
                  li         s6, 0x346d4183 #start riscv_int_numeric_corner_stream_28
                  li         a6, 0x3f6be97e
                  li         s8, 0x80000000
                  li         sp, 0x0
                  li         s10, 0x0
                  li         s7, 0xf9e194fe
                  li         s11, 0x0
                  li         s9, 0x2fd4852a
                  li         s0, 0xe7dc72c8
                  li         a1, 0xffffffff
                  nop
                  add        s7, sp, s8
                  sub        sp, s8, s6
                  addi       s0, s7, 999
                  sub        sp, s8, s6
                  nop
                  sub        sp, s8, s6
                  sub        sp, s8, s6
                  divu       s0, s0, s9
                  auipc      s11, 688967
                  lui        s0, 195546
                  mulhu      sp, sp, s8
                  nop
                  nop
                  mulh       s11, s0, s9
                  mulh       s11, s0, s9
                  auipc      s11, 688967
                  div        sp, s10, sp
                  lui        s0, 195546
                  add        s7, sp, s8
                  mul        s6, s7, s8
                  mulhu      sp, sp, s8
                  add        s7, sp, s8
                  nop
                  sub        sp, s8, s6
                  auipc      s11, 688967
                  lui        s0, 195546
                  rem        s7, s0, a1 #end riscv_int_numeric_corner_stream_28
                  c.or       a5, a1
                  xori       a4, t0, 974
                  sub        s9, s6, s5
                  sltiu      s6, ra, 913
                  and        a1, t3, a6
                  nop
                  xor        t4, s3, t3
                  auipc      t6, 688967
                  c.srai     s0, 31
                  c.nop
                  c.srai     s0, 31
                  c.nop
                  sra        s1, t3, s1
                  sltu       t2, s1, t1
                  c.mv       a1, s5
                  c.xor      a1, a2
                  nop
                  nop
                  c.add      t1, a1
                  c.srli     a0, 25
                  c.xor      a1, a2
                  add        s7, s5, a6
                  divu       sp, ra, t0
                  c.addi16sp sp, 16
                  ori        t5, t2, 999
                  remu       s5, s11, t1
                  c.mv       a1, s5
                  c.lui      a0, 24
                  c.and      a0, s0
                  mulhsu     gp, a1, s1
                  c.or       a5, a1
                  c.addi4spn a4, sp, 288
                  sra        s1, t3, s1
                  nop
                  c.li       a7, 27
                  c.li       a7, 27
                  sra        s1, t3, s1
                  c.xor      a1, a2
                  c.nop
                  mul        sp, s9, s11
                  and        a1, t3, a6
                  div        t3, t1, t5
                  mulh       s11, s1, s9
                  slt        t1, a1, a4
                  c.li       a7, 27
                  slti       tp, t6, 301
                  c.sub      s1, a4
                  sltu       t2, s1, t1
                  c.addi     s1, 6
                  mulhsu     gp, a1, s1
                  c.sub      s1, a4
                  nop
                  mulhu      tp, s3, a4
                  lui        zero, 195546
                  div        t3, t1, t5
                  c.add      t1, a1
                  slt        t1, a1, a4
                  sltiu      s6, ra, 913
                  sub        s9, s6, s5
                  c.srai     s0, 31
                  srli       s8, t6, 19
                  and        a1, t3, a6
                  c.slli     t4, 28
                  sra        s1, t3, s1
                  andi       s8, t1, -26
                  srai       s10, s1, 24
                  sub        s9, s6, s5
                  srl        a0, s2, a0
                  or         s0, a2, a0
                  c.slli     t4, 28
                  xor        t4, s3, t3
                  c.srai     s0, 31
                  mulh       s11, s1, s9
                  c.li       a7, 27
                  sltiu      s6, ra, 913
                  slt        t1, a1, a4
                  slli       s11, gp, 14
                  divu       sp, ra, t0
                  c.addi     s1, 6
                  c.addi16sp sp, 16
                  c.srai     s0, 31
                  xori       a4, t0, 974
                  add        s7, s5, a6
                  c.add      t1, a1
                  and        a1, t3, a6
                  mulh       s11, s1, s9
                  sltu       t2, s1, t1
                  c.srli     a0, 25
                  c.andi     a5, -1
                  slti       tp, t6, 301
                  div        t3, t1, t5
                  slt        t1, a1, a4
                  c.sub      s1, a4
                  or         s0, a2, a0
                  remu       s5, s11, t1
                  slt        t1, a1, a4
                  c.addi4spn a4, sp, 288
                  c.nop
                  c.sub      s1, a4
                  mulh       s11, s1, s9
                  c.nop
                  andi       s8, t1, -26
                  slt        t1, a1, a4
                  ori        t5, t2, 999
                  c.xor      a1, a2
                  c.add      t1, a1
                  sll        t3, s7, a3
                  c.li       a7, 27
                  auipc      t6, 688967
                  remu       s5, s11, t1
                  c.mv       a1, s5
                  c.srai     s0, 31
                  div        t3, t1, t5
                  srli       s8, t6, 19
                  c.srai     s0, 31
                  c.add      t1, a1
                  c.addi     s1, 6
                  c.srli     a0, 25
                  c.xor      a1, a2
                  remu       s5, s11, t1
                  sub        s9, s6, s5
                  mulhu      tp, s3, a4
                  divu       sp, ra, t0
                  xor        t4, s3, t3
                  c.slli     t4, 28
                  c.or       a5, a1
                  sll        t3, s7, a3
                  slli       s11, gp, 14
                  c.andi     a5, -1
                  srl        a0, s2, a0
                  sltiu      s6, ra, 913
                  add        s7, s5, a6
                  c.li       a7, 27
                  remu       s5, s11, t1
                  mulhsu     gp, a1, s1
                  mulh       s11, s1, s9
                  remu       s5, s11, t1
                  c.srli     a0, 25
                  c.xor      a1, a2
                  mulh       s11, s1, s9
                  c.nop
                  and        a1, t3, a6
                  sll        t3, s7, a3
                  divu       sp, ra, t0
                  slti       tp, t6, 301
                  slli       s11, gp, 14
                  div        t3, t1, t5
                  c.and      a0, s0
                  c.addi16sp sp, 16
                  c.lui      a0, 24
                  mulhsu     gp, a1, s1
                  div        t3, t1, t5
                  auipc      t6, 688967
                  slli       s11, gp, 14
                  remu       s5, s11, t1
                  and        a1, t3, a6
                  nop
                  mulh       s11, s1, s9
                  div        t3, t1, t5
                  c.or       a5, a1
                  srai       s10, s1, 24
                  remu       s5, s11, t1
                  mulh       s11, s1, s9
                  c.xor      a1, a2
                  slli       s11, gp, 14
                  c.srai     s0, 31
                  c.lui      a0, 24
                  auipc      t6, 688967
                  mulh       s11, s1, s9
                  c.slli     t4, 28
                  lui        zero, 195546
                  c.sub      s1, a4
                  or         s0, a2, a0
                  mulhu      tp, s3, a4
                  c.addi16sp sp, 16
                  c.addi4spn a4, sp, 288
                  sub        s9, s6, s5
                  xor        t4, s3, t3
                  sltu       t2, s1, t1
                  addi       a7, t2, -784
                  slli       s11, gp, 14
                  srl        a0, s2, a0
                  srai       s10, s1, 24
                  andi       s8, t1, -26
                  remu       s5, s11, t1
                  sra        s1, t3, s1
                  srli       s8, t6, 19
                  div        t3, t1, t5
                  ori        t5, t2, 999
                  c.srli     a0, 25
                  lui        zero, 195546
                  mulhu      tp, s3, a4
                  c.or       a5, a1
                  sltu       t2, s1, t1
                  c.mv       a1, s5
                  c.add      t1, a1
                  remu       s5, s11, t1
                  xor        t4, s3, t3
                  remu       s5, s11, t1
                  sll        t3, s7, a3
                  remu       s5, s11, t1
                  slti       tp, t6, 301
                  divu       sp, ra, t0
                  or         s0, a2, a0
                  c.xor      a1, a2
                  addi       a7, t2, -784
                  sltu       t2, s1, t1
                  mulhu      tp, s3, a4
                  c.and      a0, s0
                  c.slli     t4, 28
                  slli       s11, gp, 14
                  sltiu      s6, ra, 913
                  andi       s8, t1, -26
                  ori        t5, t2, 999
                  srli       s8, t6, 19
                  slti       tp, t6, 301
                  mulhsu     gp, a1, s1
                  ori        t5, t2, 999
                  c.addi16sp sp, 16
                  sub        s9, s6, s5
                  mulhsu     gp, a1, s1
                  c.li       a7, 27
                  sltiu      s6, ra, 913
                  xor        t4, s3, t3
                  slt        t1, a1, a4
                  c.addi     s1, 6
                  c.or       a5, a1
                  c.add      t1, a1
                  c.andi     a5, -1
                  c.xor      a1, a2
                  mulhu      tp, s3, a4
                  c.nop
                  div        t3, t1, t5
                  mulhsu     gp, a1, s1
                  c.xor      a1, a2
                  rem        s0, a3, a2
                  rem        s0, a3, a2
                  sltiu      s6, ra, 913
                  sltu       t2, s1, t1
                  c.and      a0, s0
                  mulhu      tp, s3, a4
                  c.lui      a0, 24
                  c.sub      s1, a4
                  c.nop
                  xor        t4, s3, t3
                  rem        s0, a3, a2
                  mulh       s11, s1, s9
                  c.add      t1, a1
                  c.addi     s1, 6
                  c.xor      a1, a2
                  sub        s9, s6, s5
                  xor        t4, s3, t3
                  lui        zero, 195546
                  addi       a7, t2, -784
                  or         s0, a2, a0
                  srai       s10, s1, 24
                  c.lui      a0, 24
                  auipc      t6, 688967
                  c.slli     t4, 28
                  mulh       s11, s1, s9
                  slli       s11, gp, 14
                  slli       s11, gp, 14
                  andi       s8, t1, -26
                  c.and      a0, s0
                  or         s0, a2, a0
                  c.sub      s1, a4
                  c.slli     t4, 28
                  nop
                  c.or       a5, a1
                  c.and      a0, s0
                  c.srai     s0, 31
                  c.slli     t4, 28
                  c.addi     s1, 6
                  slli       s11, gp, 14
                  mul        sp, s9, s11
                  c.or       a5, a1
                  sra        s1, t3, s1
                  sra        s1, t3, s1
                  rem        s0, a3, a2
                  lui        zero, 195546
                  c.srli     a0, 25
                  c.nop
                  sltu       t2, s1, t1
                  c.li       a7, 27
                  c.nop
                  c.srli     a0, 25
                  srl        a0, s2, a0
                  c.xor      a1, a2
                  slti       tp, t6, 301
                  nop
                  c.nop
                  mulhu      tp, s3, a4
                  sra        s1, t3, s1
                  mulhu      tp, s3, a4
                  c.add      t1, a1
                  c.mv       a1, s5
                  sltu       t2, s1, t1
                  sra        s1, t3, s1
                  sra        s1, t3, s1
                  c.xor      a1, a2
                  c.lui      a0, 24
                  c.add      t1, a1
                  srl        a0, s2, a0
                  addi       a7, t2, -784
                  mulhsu     gp, a1, s1
                  slt        t1, a1, a4
                  c.addi16sp sp, 16
                  mulhu      tp, s3, a4
                  sra        s1, t3, s1
                  c.slli     t4, 28
                  c.or       a5, a1
                  slti       tp, t6, 301
                  c.nop
                  sra        s1, t3, s1
                  c.addi16sp sp, 16
                  mulh       s11, s1, s9
                  c.andi     a5, -1
                  li         t2, 0xc4932c7f #start riscv_int_numeric_corner_stream_13
                  li         t4, 0x2a86312c
                  li         ra, 0x80000000
                  li         s0, 0x0
                  li         s2, 0x0
                  li         t6, 0xc7e65d08
                  li         a7, 0x836d4acb
                  li         s11, 0xf7833188
                  li         s8, 0x9b44a905
                  li         a1, 0x80000000
                  auipc      t6, 688967
                  nop
                  nop
                  rem        s8, t6, s0
                  add        ra, s2, a7
                  addi       ra, t2, 999
                  nop
                  rem        s8, t6, s0
                  nop
                  mulhsu     s0, t2, a7
                  mulhsu     s0, t2, a7
                  auipc      t6, 688967
                  mulh       t4, t2, a7
                  lui        ra, 195546
                  auipc      t6, 688967
                  nop
                  mulhsu     s0, t2, a7
                  mulhu      ra, s11, s0 #end riscv_int_numeric_corner_stream_13
                  c.srli     a0, 25
                  xor        t4, s3, t3
                  mulhsu     gp, a1, s1
                  xor        t4, s3, t3
                  andi       s8, t1, -26
                  lui        zero, 195546
                  c.lui      a0, 24
                  c.srli     a0, 25
                  sltu       t2, s1, t1
                  sltiu      s6, ra, 913
                  srli       s8, t6, 19
                  sltiu      s6, ra, 913
                  sra        s1, t3, s1
                  c.or       a5, a1
                  srai       s10, s1, 24
                  srl        a0, s2, a0
                  xor        t4, s3, t3
                  c.mv       a1, s5
                  sltiu      s6, ra, 913
                  sltiu      s6, ra, 913
                  c.and      a0, s0
                  sra        s1, t3, s1
                  c.and      a0, s0
                  c.srli     a0, 25
                  srli       s8, t6, 19
                  c.addi     s1, 6
                  andi       s8, t1, -26
                  or         s0, a2, a0
                  c.srli     a0, 25
                  c.xor      a1, a2
                  slti       tp, t6, 301
                  auipc      t6, 688967
                  mulhu      tp, s3, a4
                  ori        t5, t2, 999
                  sub        s9, s6, s5
                  slt        t1, a1, a4
                  nop
                  xor        t4, s3, t3
                  srli       s8, t6, 19
                  srli       s8, t6, 19
                  sltiu      s6, ra, 913
                  sll        t3, s7, a3
                  auipc      t6, 688967
                  mulhu      tp, s3, a4
                  c.add      t1, a1
                  and        a1, t3, a6
                  c.xor      a1, a2
                  sra        s1, t3, s1
                  srli       s8, t6, 19
                  mulhu      tp, s3, a4
                  or         s0, a2, a0
                  div        t3, t1, t5
                  c.li       a7, 27
                  nop
                  sltiu      s6, ra, 913
                  andi       s8, t1, -26
                  c.slli     t4, 28
                  rem        s0, a3, a2
                  c.srai     s0, 31
                  mulhu      tp, s3, a4
                  xori       a4, t0, 974
                  slli       s11, gp, 14
                  lui        zero, 195546
                  rem        s0, a3, a2
                  c.nop
                  or         s0, a2, a0
                  sra        s1, t3, s1
                  c.slli     t4, 28
                  divu       sp, ra, t0
                  c.mv       a1, s5
                  srl        a0, s2, a0
                  c.addi     s1, 6
                  c.addi4spn a4, sp, 288
                  lui        zero, 195546
                  c.or       a5, a1
                  remu       s5, s11, t1
                  c.addi     s1, 6
                  sltu       t2, s1, t1
                  sll        t3, s7, a3
                  mul        sp, s9, s11
                  mul        sp, s9, s11
                  c.slli     t4, 28
                  c.slli     t4, 28
                  mul        sp, s9, s11
                  srl        a0, s2, a0
                  srli       s8, t6, 19
                  slt        t1, a1, a4
                  srai       s10, s1, 24
                  c.addi4spn a4, sp, 288
                  c.addi     s1, 6
                  c.srli     a0, 25
                  slt        t1, a1, a4
                  xor        t4, s3, t3
                  add        s7, s5, a6
                  div        t3, t1, t5
                  srli       s8, t6, 19
                  remu       s5, s11, t1
                  sra        s1, t3, s1
                  andi       s8, t1, -26
                  xori       a4, t0, 974
                  auipc      t6, 688967
                  sll        t3, s7, a3
                  sltu       t2, s1, t1
                  rem        s0, a3, a2
                  auipc      t6, 688967
                  lui        zero, 195546
                  slli       s11, gp, 14
                  c.sub      s1, a4
                  srli       s8, t6, 19
                  and        a1, t3, a6
                  srl        a0, s2, a0
                  c.or       a5, a1
                  add        s7, s5, a6
                  mul        sp, s9, s11
                  c.srai     s0, 31
                  sltiu      s6, ra, 913
                  andi       s8, t1, -26
                  c.addi4spn a4, sp, 288
                  c.srli     a0, 25
                  sltiu      s6, ra, 913
                  and        a1, t3, a6
                  srli       s8, t6, 19
                  xori       a4, t0, 974
                  auipc      t6, 688967
                  mulh       s11, s1, s9
                  c.and      a0, s0
                  c.andi     a5, -1
                  sltiu      s6, ra, 913
                  nop
                  sll        t3, s7, a3
                  or         s0, a2, a0
                  c.xor      a1, a2
                  rem        s0, a3, a2
                  sltu       t2, s1, t1
                  slti       tp, t6, 301
                  c.xor      a1, a2
                  sra        s1, t3, s1
                  mulhsu     gp, a1, s1
                  c.srai     s0, 31
                  c.li       a7, 27
                  c.or       a5, a1
                  c.srli     a0, 25
                  or         s0, a2, a0
                  c.addi16sp sp, 16
                  srai       s10, s1, 24
                  slt        t1, a1, a4
                  slli       s11, gp, 14
                  sub        s9, s6, s5
                  nop
                  rem        s0, a3, a2
                  and        a1, t3, a6
                  c.xor      a1, a2
                  mulhsu     gp, a1, s1
                  sltiu      s6, ra, 913
                  div        t3, t1, t5
                  c.lui      a0, 24
                  c.and      a0, s0
                  c.mv       a1, s5
                  sra        s1, t3, s1
                  c.sub      s1, a4
                  mulh       s11, s1, s9
                  auipc      t6, 688967
                  c.addi4spn a4, sp, 288
                  add        s7, s5, a6
                  c.addi4spn a4, sp, 288
                  or         s0, a2, a0
                  c.and      a0, s0
                  c.li       a7, 27
                  c.and      a0, s0
                  slli       s11, gp, 14
                  sra        s1, t3, s1
                  auipc      t6, 688967
                  srli       s8, t6, 19
                  xor        t4, s3, t3
                  sub        s9, s6, s5
                  and        a1, t3, a6
                  c.srai     s0, 31
                  c.mv       a1, s5
                  c.nop
                  c.xor      a1, a2
                  sltiu      s6, ra, 913
                  mul        sp, s9, s11
                  mul        sp, s9, s11
                  c.or       a5, a1
                  c.andi     a5, -1
                  c.addi16sp sp, 16
                  c.li       a7, 27
                  c.add      t1, a1
                  sll        t3, s7, a3
                  sll        t3, s7, a3
                  c.addi16sp sp, 16
                  slti       tp, t6, 301
                  c.lui      a0, 24
                  lui        zero, 195546
                  addi       a7, t2, -784
                  and        a1, t3, a6
                  auipc      t6, 688967
                  srli       s8, t6, 19
                  c.slli     t4, 28
                  div        t3, t1, t5
                  mulh       s11, s1, s9
                  or         s0, a2, a0
                  c.nop
                  mul        sp, s9, s11
                  c.li       a7, 27
                  c.nop
                  rem        s0, a3, a2
                  mul        sp, s9, s11
                  auipc      t6, 688967
                  slli       s11, gp, 14
                  c.mv       a1, s5
                  mulh       s11, s1, s9
                  c.lui      a0, 24
                  add        s7, s5, a6
                  mul        sp, s9, s11
                  srli       s8, t6, 19
                  xor        t4, s3, t3
                  sra        s1, t3, s1
                  c.nop
                  c.addi16sp sp, 16
                  c.srli     a0, 25
                  xor        t4, s3, t3
                  mulhu      tp, s3, a4
                  andi       s8, t1, -26
                  mulh       s11, s1, s9
                  rem        s0, a3, a2
                  srai       s10, s1, 24
                  srl        a0, s2, a0
                  sll        t3, s7, a3
                  xori       a4, t0, 974
                  c.lui      a0, 24
                  ori        t5, t2, 999
                  c.srai     s0, 31
                  sra        s1, t3, s1
                  c.srli     a0, 25
                  xor        t4, s3, t3
                  c.lui      a0, 24
                  nop
                  nop
                  sub        s9, s6, s5
                  li         tp, 0xc58a97b6 #start riscv_int_numeric_corner_stream_37
                  li         a7, 0x80000000
                  li         s5, 0x0
                  li         gp, 0x80000000
                  li         a4, 0xf03a9a1f
                  li         ra, 0x0
                  li         s1, 0x0
                  li         a0, 0x9166eac1
                  li         t0, 0xffffffff
                  li         sp, 0x0
                  divu       tp, s1, s5
                  lui        tp, 195546
                  addi       tp, t0, 999
                  nop
                  sub        tp, a7, tp
                  remu       sp, gp, a0
                  divu       tp, s1, s5
                  sub        tp, a7, tp
                  rem        sp, tp, a0
                  sub        tp, a7, tp
                  nop
                  mulh       gp, s5, s5
                  nop
                  div        ra, a0, sp
                  nop #end riscv_int_numeric_corner_stream_37
                  c.xor      a1, a2
                  c.li       a7, 27
                  c.or       a5, a1
                  sll        t3, s7, a3
                  slt        t1, a1, a4
                  c.nop
                  div        t3, t1, t5
                  slti       tp, t6, 301
                  auipc      t6, 688967
                  mulhsu     gp, a1, s1
                  slti       tp, t6, 301
                  divu       sp, ra, t0
                  sltiu      s6, ra, 913
                  c.and      a0, s0
                  c.xor      a1, a2
                  auipc      t6, 688967
                  andi       s8, t1, -26
                  sra        s1, t3, s1
                  divu       sp, ra, t0
                  mulh       s11, s1, s9
                  c.addi     s1, 6
                  c.or       a5, a1
                  c.mv       a1, s5
                  mulhsu     gp, a1, s1
                  c.add      t1, a1
                  c.lui      a0, 24
                  auipc      t6, 688967
                  srl        a0, s2, a0
                  xor        t4, s3, t3
                  remu       s5, s11, t1
                  c.nop
                  srli       s8, t6, 19
                  add        s7, s5, a6
                  mulhsu     gp, a1, s1
                  c.nop
                  mulh       s11, s1, s9
                  auipc      t6, 688967
                  slli       s11, gp, 14
                  remu       s5, s11, t1
                  divu       sp, ra, t0
                  c.add      t1, a1
                  sub        s9, s6, s5
                  div        t3, t1, t5
                  add        s7, s5, a6
                  addi       a7, t2, -784
                  sll        t3, s7, a3
                  c.addi     s1, 6
                  mulhsu     gp, a1, s1
                  c.and      a0, s0
                  lui        zero, 195546
                  srli       s8, t6, 19
                  rem        s0, a3, a2
                  rem        s0, a3, a2
                  mulh       s11, s1, s9
                  mulh       s11, s1, s9
                  c.slli     t4, 28
                  add        s7, s5, a6
                  c.or       a5, a1
                  xor        t4, s3, t3
                  c.sub      s1, a4
                  divu       sp, ra, t0
                  sll        t3, s7, a3
                  srli       s8, t6, 19
                  mulhu      tp, s3, a4
                  c.addi16sp sp, 16
                  sub        s9, s6, s5
                  mulh       s11, s1, s9
                  c.andi     a5, -1
                  add        s7, s5, a6
                  ori        t5, t2, 999
                  sltiu      s6, ra, 913
                  c.and      a0, s0
                  andi       s8, t1, -26
                  rem        s0, a3, a2
                  or         s0, a2, a0
                  c.srai     s0, 31
                  sub        s9, s6, s5
                  slti       tp, t6, 301
                  sltiu      s6, ra, 913
                  mulh       s11, s1, s9
                  c.mv       a1, s5
                  mulhu      tp, s3, a4
                  mulhsu     gp, a1, s1
                  slti       tp, t6, 301
                  c.lui      a0, 24
                  auipc      t6, 688967
                  ori        t5, t2, 999
                  divu       sp, ra, t0
                  srli       s8, t6, 19
                  mul        sp, s9, s11
                  remu       s5, s11, t1
                  c.add      t1, a1
                  c.addi4spn a4, sp, 288
                  c.addi     s1, 6
                  xori       a4, t0, 974
                  c.sub      s1, a4
                  or         s0, a2, a0
                  andi       s8, t1, -26
                  c.addi4spn a4, sp, 288
                  mulhu      tp, s3, a4
                  c.xor      a1, a2
                  xor        t4, s3, t3
                  c.lui      a0, 24
                  srli       s8, t6, 19
                  mulhu      tp, s3, a4
                  divu       sp, ra, t0
                  add        s7, s5, a6
                  ori        t5, t2, 999
                  mulh       s11, s1, s9
                  lui        zero, 195546
                  sltiu      s6, ra, 913
                  c.addi16sp sp, 16
                  xori       a4, t0, 974
                  xor        t4, s3, t3
                  c.addi16sp sp, 16
                  sra        s1, t3, s1
                  divu       sp, ra, t0
                  addi       a7, t2, -784
                  c.add      t1, a1
                  divu       sp, ra, t0
                  nop
                  xori       a4, t0, 974
                  ori        t5, t2, 999
                  addi       a7, t2, -784
                  c.slli     t4, 28
                  c.srli     a0, 25
                  sltiu      s6, ra, 913
                  sltu       t2, s1, t1
                  c.li       a7, 27
                  xori       a4, t0, 974
                  slt        t1, a1, a4
                  c.srli     a0, 25
                  c.srai     s0, 31
                  c.and      a0, s0
                  nop
                  and        a1, t3, a6
                  sltiu      s6, ra, 913
                  slt        t1, a1, a4
                  addi       a7, t2, -784
                  c.or       a5, a1
                  xor        t4, s3, t3
                  c.add      t1, a1
                  rem        s0, a3, a2
                  c.andi     a5, -1
                  slt        t1, a1, a4
                  nop
                  xori       a4, t0, 974
                  sra        s1, t3, s1
                  slli       s11, gp, 14
                  andi       s8, t1, -26
                  xori       a4, t0, 974
                  c.addi16sp sp, 16
                  and        a1, t3, a6
                  c.slli     t4, 28
                  srli       s8, t6, 19
                  slti       tp, t6, 301
                  srli       s8, t6, 19
                  or         s0, a2, a0
                  c.andi     a5, -1
                  sub        s9, s6, s5
                  c.addi     s1, 6
                  c.lui      a0, 24
                  c.addi16sp sp, 16
                  c.nop
                  divu       sp, ra, t0
                  or         s0, a2, a0
                  rem        s0, a3, a2
                  slli       s11, gp, 14
                  sltu       t2, s1, t1
                  c.li       a7, 27
                  addi       a7, t2, -784
                  sub        s9, s6, s5
                  sll        t3, s7, a3
                  slli       s11, gp, 14
                  c.addi4spn a4, sp, 288
                  c.nop
                  auipc      t6, 688967
                  c.srai     s0, 31
                  srai       s10, s1, 24
                  sub        s9, s6, s5
                  c.xor      a1, a2
                  nop
                  c.li       a7, 27
                  sra        s1, t3, s1
                  c.slli     t4, 28
                  andi       s8, t1, -26
                  xor        t4, s3, t3
                  c.addi     s1, 6
                  c.or       a5, a1
                  c.srli     a0, 25
                  sra        s1, t3, s1
                  c.slli     t4, 28
                  sub        s9, s6, s5
                  c.sub      s1, a4
                  c.li       a7, 27
                  xori       a4, t0, 974
                  nop
                  rem        s0, a3, a2
                  slt        t1, a1, a4
                  or         s0, a2, a0
                  c.xor      a1, a2
                  c.mv       a1, s5
                  c.andi     a5, -1
                  c.addi16sp sp, 16
                  andi       s8, t1, -26
                  c.andi     a5, -1
                  andi       s8, t1, -26
                  auipc      t6, 688967
                  c.slli     t4, 28
                  c.srli     a0, 25
                  sll        t3, s7, a3
                  auipc      t6, 688967
                  andi       s8, t1, -26
                  c.addi4spn a4, sp, 288
                  c.addi4spn a4, sp, 288
                  c.srai     s0, 31
                  c.addi4spn a4, sp, 288
                  srli       s8, t6, 19
                  c.addi16sp sp, 16
                  xor        t4, s3, t3
                  slli       s11, gp, 14
                  sltiu      s6, ra, 913
                  c.lui      a0, 24
                  divu       sp, ra, t0
                  xori       a4, t0, 974
                  xori       a4, t0, 974
                  sra        s1, t3, s1
                  div        t3, t1, t5
                  c.addi     s1, 6
                  div        t3, t1, t5
                  sll        t3, s7, a3
                  sub        s9, s6, s5
                  nop
                  add        s7, s5, a6
                  srli       s8, t6, 19
                  slli       s11, gp, 14
                  c.add      t1, a1
                  sltiu      s6, ra, 913
                  and        a1, t3, a6
                  slli       s11, gp, 14
                  mulh       s11, s1, s9
                  c.addi4spn a4, sp, 288
                  c.addi     s1, 6
                  c.or       a5, a1
                  c.or       a5, a1
                  mul        sp, s9, s11
                  ori        t5, t2, 999
                  div        t3, t1, t5
                  c.addi4spn a4, sp, 288
                  c.or       a5, a1
                  lui        zero, 195546
                  ori        t5, t2, 999
                  c.and      a0, s0
                  c.or       a5, a1
                  xori       a4, t0, 974
                  c.add      t1, a1
                  addi       a7, t2, -784
                  mulhsu     gp, a1, s1
                  c.or       a5, a1
                  slti       tp, t6, 301
                  mul        sp, s9, s11
                  andi       s8, t1, -26
                  c.sub      s1, a4
                  c.or       a5, a1
                  c.slli     t4, 28
                  slt        t1, a1, a4
                  sltu       t2, s1, t1
                  sltu       t2, s1, t1
                  mul        sp, s9, s11
                  nop
                  slt        t1, a1, a4
                  slt        t1, a1, a4
                  mul        sp, s9, s11
                  sltu       t2, s1, t1
                  c.sub      s1, a4
                  mul        sp, s9, s11
                  sra        s1, t3, s1
                  srl        a0, s2, a0
                  c.addi16sp sp, 16
                  div        t3, t1, t5
                  srai       s10, s1, 24
                  ori        t5, t2, 999
                  mulhsu     gp, a1, s1
                  ori        t5, t2, 999
                  srai       s10, s1, 24
                  or         s0, a2, a0
                  add        s7, s5, a6
                  mulhu      tp, s3, a4
                  xor        t4, s3, t3
                  and        a1, t3, a6
                  c.sub      s1, a4
                  c.sub      s1, a4
                  slli       s11, gp, 14
                  sra        s1, t3, s1
                  c.add      t1, a1
                  srl        a0, s2, a0
                  c.mv       a1, s5
                  sub        s9, s6, s5
                  auipc      t6, 688967
                  c.add      t1, a1
                  lui        zero, 195546
                  c.sub      s1, a4
                  div        t3, t1, t5
                  c.slli     t4, 28
                  c.or       a5, a1
                  c.addi4spn a4, sp, 288
                  c.srai     s0, 31
                  srl        a0, s2, a0
                  c.addi16sp sp, 16
                  c.xor      a1, a2
                  c.slli     t4, 28
                  srai       s10, s1, 24
                  sll        t3, s7, a3
                  divu       sp, ra, t0
                  c.li       a7, 27
                  sra        s1, t3, s1
                  mulh       s11, s1, s9
                  sll        t3, s7, a3
                  or         s0, a2, a0
                  c.slli     t4, 28
                  slt        t1, a1, a4
                  c.addi     s1, 6
                  or         s0, a2, a0
                  c.srai     s0, 31
                  and        a1, t3, a6
                  auipc      t6, 688967
                  lui        zero, 195546
                  c.xor      a1, a2
                  sub        s9, s6, s5
                  or         s0, a2, a0
                  slti       tp, t6, 301
                  mulh       s11, s1, s9
                  xor        t4, s3, t3
                  remu       s5, s11, t1
                  srai       s10, s1, 24
                  slli       s11, gp, 14
                  sltu       t2, s1, t1
                  srl        a0, s2, a0
                  srai       s10, s1, 24
                  sltu       t2, s1, t1
                  xori       a4, t0, 974
                  srl        a0, s2, a0
                  remu       s5, s11, t1
                  c.srai     s0, 31
                  c.xor      a1, a2
                  c.addi16sp sp, 16
                  xor        t4, s3, t3
                  sltiu      s6, ra, 913
                  mul        sp, s9, s11
                  mulh       s11, s1, s9
                  mulhsu     gp, a1, s1
                  srli       s8, t6, 19
                  c.addi4spn a4, sp, 288
                  slli       s11, gp, 14
                  mulhsu     gp, a1, s1
                  c.nop
                  c.slli     t4, 28
                  sub        s9, s6, s5
                  slt        t1, a1, a4
                  slli       s11, gp, 14
                  div        t3, t1, t5
                  mul        sp, s9, s11
                  c.srli     a0, 25
                  c.srai     s0, 31
                  or         s0, a2, a0
                  slti       tp, t6, 301
                  c.addi     s1, 6
                  srli       s8, t6, 19
                  and        a1, t3, a6
                  mul        sp, s9, s11
                  mulhu      tp, s3, a4
                  and        a1, t3, a6
                  c.srli     a0, 25
                  c.mv       a1, s5
                  c.and      a0, s0
                  div        t3, t1, t5
                  c.nop
                  sll        t3, s7, a3
                  add        s7, s5, a6
                  slti       tp, t6, 301
                  addi       a7, t2, -784
                  slt        t1, a1, a4
                  mulhsu     gp, a1, s1
                  div        t3, t1, t5
                  slt        t1, a1, a4
                  add        s7, s5, a6
                  c.mv       a1, s5
                  c.mv       a1, s5
                  c.addi4spn a4, sp, 288
                  add        s7, s5, a6
                  c.addi     s1, 6
                  c.srai     s0, 31
                  c.and      a0, s0
                  slli       s11, gp, 14
                  lui        zero, 195546
                  c.addi4spn a4, sp, 288
                  div        t3, t1, t5
                  mul        sp, s9, s11
                  c.and      a0, s0
                  slti       tp, t6, 301
                  ori        t5, t2, 999
                  remu       s5, s11, t1
                  sltu       t2, s1, t1
                  nop
                  c.andi     a5, -1
                  c.add      t1, a1
                  slt        t1, a1, a4
                  c.addi     s1, 6
                  c.addi     s1, 6
                  sra        s1, t3, s1
                  c.srai     s0, 31
                  c.and      a0, s0
                  slli       s11, gp, 14
                  add        s7, s5, a6
                  c.slli     t4, 28
                  auipc      t6, 688967
                  c.or       a5, a1
                  slti       tp, t6, 301
                  remu       s5, s11, t1
                  c.addi4spn a4, sp, 288
                  sra        s1, t3, s1
                  srai       s10, s1, 24
                  slli       s11, gp, 14
                  c.andi     a5, -1
                  divu       sp, ra, t0
                  ori        t5, t2, 999
                  c.mv       a1, s5
                  add        s7, s5, a6
                  sll        t3, s7, a3
                  ori        t5, t2, 999
                  c.addi16sp sp, 16
                  c.slli     t4, 28
                  c.nop
                  c.srai     s0, 31
                  c.li       a7, 27
                  sub        s9, s6, s5
                  rem        s0, a3, a2
                  add        s7, s5, a6
                  addi       a7, t2, -784
                  c.mv       a1, s5
                  c.slli     t4, 28
                  or         s0, a2, a0
                  mulh       s11, s1, s9
                  addi       a7, t2, -784
                  nop
                  c.add      t1, a1
                  c.mv       a1, s5
                  c.xor      a1, a2
                  xor        t4, s3, t3
                  add        s7, s5, a6
                  ori        t5, t2, 999
                  sub        s9, s6, s5
                  remu       s5, s11, t1
                  divu       sp, ra, t0
                  auipc      t6, 688967
                  ori        t5, t2, 999
                  srai       s10, s1, 24
                  and        a1, t3, a6
                  auipc      t6, 688967
                  sra        s1, t3, s1
                  div        t3, t1, t5
                  mulhsu     gp, a1, s1
                  sltu       t2, s1, t1
                  c.or       a5, a1
                  andi       s8, t1, -26
                  c.nop
                  c.mv       a1, s5
                  c.lui      a0, 24
                  sub        s9, s6, s5
                  mul        sp, s9, s11
                  addi       a7, t2, -784
                  nop
                  c.xor      a1, a2
                  srai       s10, s1, 24
                  c.lui      a0, 24
                  mulhsu     gp, a1, s1
                  or         s0, a2, a0
                  c.addi16sp sp, 16
                  sub        s9, s6, s5
                  c.or       a5, a1
                  c.slli     t4, 28
                  ori        t5, t2, 999
                  srl        a0, s2, a0
                  divu       sp, ra, t0
                  c.andi     a5, -1
                  slti       tp, t6, 301
                  c.addi     s1, 6
                  c.add      t1, a1
                  and        a1, t3, a6
                  xori       a4, t0, 974
                  sltu       t2, s1, t1
                  srl        a0, s2, a0
                  srli       s8, t6, 19
                  c.andi     a5, -1
                  sra        s1, t3, s1
                  c.li       a7, 27
                  sltu       t2, s1, t1
                  c.addi     s1, 6
                  div        t3, t1, t5
                  slli       s11, gp, 14
                  remu       s5, s11, t1
                  slt        t1, a1, a4
                  c.andi     a5, -1
                  ori        t5, t2, 999
                  sltu       t2, s1, t1
                  c.nop
                  auipc      t6, 688967
                  andi       s8, t1, -26
                  div        t3, t1, t5
                  mulhu      tp, s3, a4
                  xori       a4, t0, 974
                  addi       a7, t2, -784
                  sll        t3, s7, a3
                  c.addi16sp sp, 16
                  div        t3, t1, t5
                  c.xor      a1, a2
                  andi       s8, t1, -26
                  c.addi     s1, 6
                  c.addi     s1, 6
                  c.nop
                  xori       a4, t0, 974
                  remu       s5, s11, t1
                  c.and      a0, s0
                  c.slli     t4, 28
                  c.srli     a0, 25
                  srai       s10, s1, 24
                  c.mv       a1, s5
                  andi       s8, t1, -26
                  slti       tp, t6, 301
                  sltu       t2, s1, t1
                  mul        sp, s9, s11
                  c.li       a7, 27
                  srl        a0, s2, a0
                  c.or       a5, a1
                  slti       tp, t6, 301
                  mulhu      tp, s3, a4
                  mulhu      tp, s3, a4
                  c.li       a7, 27
                  sra        s1, t3, s1
                  c.srli     a0, 25
                  sll        t3, s7, a3
                  c.lui      a0, 24
                  slti       tp, t6, 301
                  or         s0, a2, a0
                  slli       s11, gp, 14
                  addi       a7, t2, -784
                  auipc      t6, 688967
                  add        s7, s5, a6
                  c.addi16sp sp, 16
                  c.lui      a0, 24
                  c.andi     a5, -1
                  rem        s0, a3, a2
                  div        t3, t1, t5
                  and        a1, t3, a6
                  rem        s0, a3, a2
                  c.li       a7, 27
                  srl        a0, s2, a0
                  mul        sp, s9, s11
                  c.add      t1, a1
                  sra        s1, t3, s1
                  c.mv       a1, s5
                  rem        s0, a3, a2
                  srli       s8, t6, 19
                  c.addi4spn a4, sp, 288
                  c.li       a7, 27
                  slti       tp, t6, 301
                  sub        s9, s6, s5
                  c.lui      a0, 24
                  c.addi4spn a4, sp, 288
                  div        t3, t1, t5
                  slt        t1, a1, a4
                  rem        s0, a3, a2
                  c.xor      a1, a2
                  srli       s8, t6, 19
                  xori       a4, t0, 974
                  mulhsu     gp, a1, s1
                  mulhsu     gp, a1, s1
                  c.add      t1, a1
                  div        t3, t1, t5
                  lui        zero, 195546
                  c.sub      s1, a4
                  sub        s9, s6, s5
                  mulh       s11, s1, s9
                  slt        t1, a1, a4
                  remu       s5, s11, t1
                  slli       s11, gp, 14
                  rem        s0, a3, a2
                  divu       sp, ra, t0
                  xor        t4, s3, t3
                  sltiu      s6, ra, 913
                  add        s7, s5, a6
                  mulhsu     gp, a1, s1
                  rem        s0, a3, a2
                  rem        s0, a3, a2
                  add        s7, s5, a6
                  or         s0, a2, a0
                  c.andi     a5, -1
                  sltiu      s6, ra, 913
                  c.sub      s1, a4
                  c.and      a0, s0
                  c.or       a5, a1
                  c.add      t1, a1
                  c.addi4spn a4, sp, 288
                  c.add      t1, a1
                  sub        s9, s6, s5
                  c.slli     t4, 28
                  c.srli     a0, 25
                  addi       a7, t2, -784
                  lui        zero, 195546
                  c.or       a5, a1
                  mulh       s11, s1, s9
                  c.srli     a0, 25
                  srli       s8, t6, 19
                  c.xor      a1, a2
                  xor        t4, s3, t3
                  c.mv       a1, s5
                  sltiu      s6, ra, 913
                  sll        t3, s7, a3
                  srli       s8, t6, 19
                  c.srai     s0, 31
                  c.or       a5, a1
                  c.xor      a1, a2
                  mulhu      tp, s3, a4
                  c.xor      a1, a2
                  mulhu      tp, s3, a4
                  nop
                  sll        t3, s7, a3
                  c.addi4spn a4, sp, 288
                  c.and      a0, s0
                  addi       a7, t2, -784
                  nop
                  nop
                  remu       s5, s11, t1
                  sra        s1, t3, s1
                  mulhu      tp, s3, a4
                  c.addi     s1, 6
                  srl        a0, s2, a0
                  xor        t4, s3, t3
                  xor        t4, s3, t3
                  c.addi4spn a4, sp, 288
                  or         s0, a2, a0
                  xori       a4, t0, 974
                  mulhsu     gp, a1, s1
                  c.andi     a5, -1
                  remu       s5, s11, t1
                  slli       s11, gp, 14
                  sub        s9, s6, s5
                  sub        s9, s6, s5
                  mulhsu     gp, a1, s1
                  divu       sp, ra, t0
                  c.andi     a5, -1
                  slt        t1, a1, a4
                  c.andi     a5, -1
                  srai       s10, s1, 24
                  ori        t5, t2, 999
                  c.li       a7, 27
                  c.lui      a0, 24
                  c.srai     s0, 31
                  xor        t4, s3, t3
                  c.srai     s0, 31
                  nop
                  c.addi16sp sp, 16
                  or         s0, a2, a0
                  c.srai     s0, 31
                  add        s7, s5, a6
                  sll        t3, s7, a3
                  srl        a0, s2, a0
                  slli       s11, gp, 14
                  c.and      a0, s0
                  sub        s9, s6, s5
                  c.slli     t4, 28
                  slli       s11, gp, 14
                  add        s7, s5, a6
                  slli       s11, gp, 14
                  srli       s8, t6, 19
                  c.li       a7, 27
                  c.or       a5, a1
                  divu       sp, ra, t0
                  c.srli     a0, 25
                  slt        t1, a1, a4
                  mulh       s11, s1, s9
                  sub        s9, s6, s5
                  c.add      t1, a1
                  mulhu      tp, s3, a4
                  and        a1, t3, a6
                  c.xor      a1, a2
                  andi       s8, t1, -26
                  lui        zero, 195546
                  c.add      t1, a1
                  xor        t4, s3, t3
                  divu       sp, ra, t0
                  nop
                  c.or       a5, a1
                  and        a1, t3, a6
                  slti       tp, t6, 301
                  sll        t3, s7, a3
                  sltu       t2, s1, t1
                  c.andi     a5, -1
                  srl        a0, s2, a0
                  c.mv       a1, s5
                  slli       s11, gp, 14
                  c.addi16sp sp, 16
                  c.mv       a1, s5
                  rem        s0, a3, a2
                  c.addi4spn a4, sp, 288
                  remu       s5, s11, t1
                  c.addi4spn a4, sp, 288
                  nop
                  mulh       s11, s1, s9
                  c.mv       a1, s5
                  c.or       a5, a1
                  c.or       a5, a1
                  xori       a4, t0, 974
                  c.add      t1, a1
                  c.addi     s1, 6
                  c.slli     t4, 28
                  srli       s8, t6, 19
                  c.xor      a1, a2
                  xori       a4, t0, 974
                  c.slli     t4, 28
                  c.addi     s1, 6
                  mulh       s11, s1, s9
                  srli       s8, t6, 19
                  slli       s11, gp, 14
                  c.andi     a5, -1
                  divu       sp, ra, t0
                  sltiu      s6, ra, 913
                  c.li       a7, 27
                  c.addi     s1, 6
                  c.nop
                  c.nop
                  c.srai     s0, 31
                  auipc      t6, 688967
                  xor        t4, s3, t3
                  c.xor      a1, a2
                  xor        t4, s3, t3
                  srli       s8, t6, 19
                  or         s0, a2, a0
                  sltiu      s6, ra, 913
                  c.addi4spn a4, sp, 288
                  xor        t4, s3, t3
                  c.xor      a1, a2
                  c.add      t1, a1
                  xor        t4, s3, t3
                  remu       s5, s11, t1
                  c.andi     a5, -1
                  lui        zero, 195546
                  rem        s0, a3, a2
                  c.xor      a1, a2
                  c.or       a5, a1
                  sll        t3, s7, a3
                  sll        t3, s7, a3
                  lui        zero, 195546
                  sub        s9, s6, s5
                  slti       tp, t6, 301
                  and        a1, t3, a6
                  c.srai     s0, 31
                  c.mv       a1, s5
                  add        s7, s5, a6
                  addi       a7, t2, -784
                  nop
                  add        s7, s5, a6
                  lui        zero, 195546
                  sub        s9, s6, s5
                  c.addi4spn a4, sp, 288
                  addi       a7, t2, -784
                  c.srli     a0, 25
                  xor        t4, s3, t3
                  slt        t1, a1, a4
                  c.addi4spn a4, sp, 288
                  c.lui      a0, 24
                  sub        s9, s6, s5
                  rem        s0, a3, a2
                  mul        sp, s9, s11
                  sltiu      s6, ra, 913
                  slt        t1, a1, a4
                  auipc      t6, 688967
                  c.andi     a5, -1
                  c.andi     a5, -1
                  c.addi     s1, 6
                  div        t3, t1, t5
                  mulh       s11, s1, s9
                  mulhsu     gp, a1, s1
                  lui        zero, 195546
                  c.srai     s0, 31
                  auipc      t6, 688967
                  c.li       a7, 27
                  c.sub      s1, a4
                  add        s7, s5, a6
                  c.slli     t4, 28
                  nop
                  xori       a4, t0, 974
                  andi       s8, t1, -26
                  addi       a7, t2, -784
                  c.sub      s1, a4
                  c.addi4spn a4, sp, 288
                  rem        s0, a3, a2
                  addi       a7, t2, -784
                  sltiu      s6, ra, 913
                  sra        s1, t3, s1
                  c.srai     s0, 31
                  c.mv       a1, s5
                  slti       tp, t6, 301
                  c.or       a5, a1
                  rem        s0, a3, a2
                  c.srli     a0, 25
                  c.slli     t4, 28
                  srli       s8, t6, 19
                  xori       a4, t0, 974
                  addi       a7, t2, -784
                  sra        s1, t3, s1
                  c.and      a0, s0
                  c.addi4spn a4, sp, 288
                  add        s7, s5, a6
                  mulh       s11, s1, s9
                  xor        t4, s3, t3
                  c.and      a0, s0
                  srli       s8, t6, 19
                  mulhu      tp, s3, a4
                  lui        zero, 195546
                  ori        t5, t2, 999
                  auipc      t6, 688967
                  rem        s0, a3, a2
                  xori       a4, t0, 974
                  srli       s8, t6, 19
                  c.addi16sp sp, 16
                  addi       a7, t2, -784
                  sltu       t2, s1, t1
                  c.nop
                  mulhu      tp, s3, a4
                  sub        s9, s6, s5
                  c.mv       a1, s5
                  c.addi     s1, 6
                  andi       s8, t1, -26
                  mul        sp, s9, s11
                  c.addi16sp sp, 16
                  sltu       t2, s1, t1
                  mulhsu     gp, a1, s1
                  slti       tp, t6, 301
                  nop
                  c.or       a5, a1
                  sub        s9, s6, s5
                  c.li       a7, 27
                  lui        zero, 195546
                  c.srai     s0, 31
                  xori       a4, t0, 974
                  srl        a0, s2, a0
                  c.andi     a5, -1
                  nop
                  lui        zero, 195546
                  sll        t3, s7, a3
                  rem        s0, a3, a2
                  c.sub      s1, a4
                  c.srli     a0, 25
                  srai       s10, s1, 24
                  slti       tp, t6, 301
                  srai       s10, s1, 24
                  add        s7, s5, a6
                  c.slli     t4, 28
                  c.li       a7, 27
                  addi       a7, t2, -784
                  mulhsu     gp, a1, s1
                  andi       s8, t1, -26
                  sltu       t2, s1, t1
                  auipc      t6, 688967
                  sltiu      s6, ra, 913
                  c.and      a0, s0
                  c.and      a0, s0
                  slti       tp, t6, 301
                  c.andi     a5, -1
                  srli       s8, t6, 19
                  slti       tp, t6, 301
                  mulhsu     gp, a1, s1
                  slti       tp, t6, 301
                  add        s7, s5, a6
                  sll        t3, s7, a3
                  c.li       a7, 27
                  xor        t4, s3, t3
                  xor        t4, s3, t3
                  c.nop
                  srl        a0, s2, a0
                  slli       s11, gp, 14
                  div        t3, t1, t5
                  srli       s8, t6, 19
                  and        a1, t3, a6
                  lui        zero, 195546
                  andi       s8, t1, -26
                  mulhu      tp, s3, a4
                  slt        t1, a1, a4
                  c.addi4spn a4, sp, 288
                  sll        t3, s7, a3
                  lui        zero, 195546
                  mulhu      tp, s3, a4
                  andi       s8, t1, -26
                  divu       sp, ra, t0
                  c.xor      a1, a2
                  c.sub      s1, a4
                  mulhsu     gp, a1, s1
                  addi       a7, t2, -784
                  remu       s5, s11, t1
                  mulh       s11, s1, s9
                  divu       sp, ra, t0
                  divu       sp, ra, t0
                  remu       s5, s11, t1
                  c.srli     a0, 25
                  nop
                  c.srai     s0, 31
                  xori       a4, t0, 974
                  srai       s10, s1, 24
                  nop
                  sltu       t2, s1, t1
                  xori       a4, t0, 974
                  mulhu      tp, s3, a4
                  c.srai     s0, 31
                  srai       s10, s1, 24
                  c.srli     a0, 25
                  andi       s8, t1, -26
                  slti       tp, t6, 301
                  c.srai     s0, 31
                  c.add      t1, a1
                  c.addi4spn a4, sp, 288
                  c.xor      a1, a2
                  c.li       a7, 27
                  sub        s9, s6, s5
                  sra        s1, t3, s1
                  c.xor      a1, a2
                  mul        sp, s9, s11
                  sltu       t2, s1, t1
                  c.andi     a5, -1
                  c.addi4spn a4, sp, 288
                  add        s7, s5, a6
                  lui        zero, 195546
                  c.add      t1, a1
                  sub        s9, s6, s5
                  slt        t1, a1, a4
                  c.addi16sp sp, 16
                  slli       s11, gp, 14
                  and        a1, t3, a6
                  sll        t3, s7, a3
                  or         s0, a2, a0
                  c.lui      a0, 24
                  c.addi     s1, 6
                  mulh       s11, s1, s9
                  auipc      t6, 688967
                  andi       s8, t1, -26
                  nop
                  rem        s0, a3, a2
                  srai       s10, s1, 24
                  c.srli     a0, 25
                  slt        t1, a1, a4
                  c.and      a0, s0
                  srl        a0, s2, a0
                  c.or       a5, a1
                  srl        a0, s2, a0
                  mulhu      tp, s3, a4
                  sub        s9, s6, s5
                  sra        s1, t3, s1
                  rem        s0, a3, a2
                  c.or       a5, a1
                  and        a1, t3, a6
                  mulhsu     gp, a1, s1
                  div        t3, t1, t5
                  auipc      t6, 688967
                  c.and      a0, s0
                  c.sub      s1, a4
                  nop
                  c.slli     t4, 28
                  add        s7, s5, a6
                  c.srli     a0, 25
                  c.lui      a0, 24
                  c.andi     a5, -1
                  srai       s10, s1, 24
                  srli       s8, t6, 19
                  ori        t5, t2, 999
                  auipc      t6, 688967
                  c.addi16sp sp, 16
                  addi       a7, t2, -784
                  srl        a0, s2, a0
                  c.li       a7, 27
                  divu       sp, ra, t0
                  or         s0, a2, a0
                  and        a1, t3, a6
                  c.sub      s1, a4
                  lui        zero, 195546
                  srai       s10, s1, 24
                  auipc      t6, 688967
                  mulhu      tp, s3, a4
                  or         s0, a2, a0
                  slli       s11, gp, 14
                  add        s7, s5, a6
                  xor        t4, s3, t3
                  divu       sp, ra, t0
                  srli       s8, t6, 19
                  sub        s9, s6, s5
                  mulhsu     gp, a1, s1
                  c.sub      s1, a4
                  slt        t1, a1, a4
                  c.nop
                  xori       a4, t0, 974
                  remu       s5, s11, t1
                  c.addi4spn a4, sp, 288
                  xor        t4, s3, t3
                  slli       s11, gp, 14
                  srai       s10, s1, 24
                  sll        t3, s7, a3
                  or         s0, a2, a0
                  mul        sp, s9, s11
                  c.addi     s1, 6
                  div        t3, t1, t5
                  c.li       a7, 27
                  c.srai     s0, 31
                  addi       a7, t2, -784
                  andi       s8, t1, -26
                  c.slli     t4, 28
                  mulh       s11, s1, s9
                  mulh       s11, s1, s9
                  and        a1, t3, a6
                  srli       s8, t6, 19
                  c.addi4spn a4, sp, 288
                  nop
                  and        a1, t3, a6
                  c.slli     t4, 28
                  divu       sp, ra, t0
                  c.mv       a1, s5
                  slt        t1, a1, a4
                  c.and      a0, s0
                  c.slli     t4, 28
                  srai       s10, s1, 24
                  c.srli     a0, 25
                  c.addi4spn a4, sp, 288
                  xor        t4, s3, t3
                  xor        t4, s3, t3
                  c.mv       a1, s5
                  sltu       t2, s1, t1
                  c.slli     t4, 28
                  remu       s5, s11, t1
                  rem        s0, a3, a2
                  xori       a4, t0, 974
                  ori        t5, t2, 999
                  xor        t4, s3, t3
                  auipc      t6, 688967
                  c.addi4spn a4, sp, 288
                  or         s0, a2, a0
                  lui        zero, 195546
                  mulh       s11, s1, s9
                  xori       a4, t0, 974
                  c.srai     s0, 31
                  c.mv       a1, s5
                  mulhu      tp, s3, a4
                  ori        t5, t2, 999
                  ori        t5, t2, 999
                  c.addi4spn a4, sp, 288
                  and        a1, t3, a6
                  divu       sp, ra, t0
                  c.andi     a5, -1
                  c.addi4spn a4, sp, 288
                  auipc      t6, 688967
                  c.addi4spn a4, sp, 288
                  c.sub      s1, a4
                  c.li       a7, 27
                  c.srli     a0, 25
                  divu       sp, ra, t0
                  c.addi4spn a4, sp, 288
                  divu       sp, ra, t0
                  auipc      t6, 688967
                  slli       s11, gp, 14
                  and        a1, t3, a6
                  add        s7, s5, a6
                  c.add      t1, a1
                  srli       s8, t6, 19
                  mulhu      tp, s3, a4
                  c.sub      s1, a4
                  xori       a4, t0, 974
                  c.mv       a1, s5
                  c.addi     s1, 6
                  c.srai     s0, 31
                  srli       s8, t6, 19
                  remu       s5, s11, t1
                  c.andi     a5, -1
                  sltiu      s6, ra, 913
                  sll        t3, s7, a3
                  srai       s10, s1, 24
                  c.andi     a5, -1
                  srli       s8, t6, 19
                  divu       sp, ra, t0
                  addi       a7, t2, -784
                  srli       s8, t6, 19
                  srl        a0, s2, a0
                  remu       s5, s11, t1
                  sltu       t2, s1, t1
                  or         s0, a2, a0
                  andi       s8, t1, -26
                  and        a1, t3, a6
                  sltiu      s6, ra, 913
                  c.mv       a1, s5
                  auipc      t6, 688967
                  mulh       s11, s1, s9
                  c.nop
                  c.srai     s0, 31
                  c.addi4spn a4, sp, 288
                  c.slli     t4, 28
                  lui        zero, 195546
                  c.addi4spn a4, sp, 288
                  divu       sp, ra, t0
                  c.nop
                  c.andi     a5, -1
                  c.and      a0, s0
                  sltiu      s6, ra, 913
                  srli       s8, t6, 19
                  slti       tp, t6, 301
                  c.addi4spn a4, sp, 288
                  srai       s10, s1, 24
                  sll        t3, s7, a3
                  add        s7, s5, a6
                  srl        a0, s2, a0
                  c.xor      a1, a2
                  addi       a7, t2, -784
                  rem        s0, a3, a2
                  mulhu      tp, s3, a4
                  slt        t1, a1, a4
                  c.srai     s0, 31
                  c.and      a0, s0
                  mulhu      tp, s3, a4
                  xor        t4, s3, t3
                  c.andi     a5, -1
                  lui        zero, 195546
                  andi       s8, t1, -26
                  slti       tp, t6, 301
                  sra        s1, t3, s1
                  slli       s11, gp, 14
                  divu       sp, ra, t0
                  c.mv       a1, s5
                  mulhu      tp, s3, a4
                  c.addi16sp sp, 16
                  c.addi     s1, 6
                  c.sub      s1, a4
                  c.srli     a0, 25
                  add        s7, s5, a6
                  remu       s5, s11, t1
                  srl        a0, s2, a0
                  c.srli     a0, 25
                  sub        s9, s6, s5
                  c.xor      a1, a2
                  lui        zero, 195546
                  mulhu      tp, s3, a4
                  sltu       t2, s1, t1
                  auipc      t6, 688967
                  c.or       a5, a1
                  c.add      t1, a1
                  or         s0, a2, a0
                  mulhsu     gp, a1, s1
                  sltiu      s6, ra, 913
                  lui        zero, 195546
                  c.nop
                  c.xor      a1, a2
                  slt        t1, a1, a4
                  c.add      t1, a1
                  auipc      t6, 688967
                  c.srli     a0, 25
                  c.xor      a1, a2
                  xor        t4, s3, t3
                  div        t3, t1, t5
                  auipc      t6, 688967
                  c.srli     a0, 25
                  div        t3, t1, t5
                  srai       s10, s1, 24
                  srl        a0, s2, a0
                  c.srai     s0, 31
                  srli       s8, t6, 19
                  rem        s0, a3, a2
                  sra        s1, t3, s1
                  and        a1, t3, a6
                  mulhu      tp, s3, a4
                  c.srli     a0, 25
                  mul        sp, s9, s11
                  xori       a4, t0, 974
                  sra        s1, t3, s1
                  c.addi     s1, 6
                  sll        t3, s7, a3
                  auipc      t6, 688967
                  div        t3, t1, t5
                  add        s7, s5, a6
                  sll        t3, s7, a3
                  c.xor      a1, a2
                  xori       a4, t0, 974
                  srli       s8, t6, 19
                  c.li       a7, 27
                  nop
                  mulhsu     gp, a1, s1
                  c.addi4spn a4, sp, 288
                  c.xor      a1, a2
                  slti       tp, t6, 301
                  rem        s0, a3, a2
                  c.andi     a5, -1
                  mulhsu     gp, a1, s1
                  div        t3, t1, t5
                  c.addi     s1, 6
                  remu       s5, s11, t1
                  c.srai     s0, 31
                  c.andi     a5, -1
                  li         s3, 0xea294de #start riscv_int_numeric_corner_stream_14
                  li         s7, 0x80000000
                  li         s1, 0xffffffff
                  li         tp, 0x80000000
                  li         s8, 0x80000000
                  li         s11, 0xef2ff383
                  li         a6, 0xffffffff
                  li         a5, 0x80000000
                  li         gp, 0x80000000
                  li         a1, 0x0
                  lui        tp, 195546
                  addi       a6, s7, 999
                  addi       a6, s7, 999
                  addi       a6, s7, 999
                  nop
                  nop
                  nop
                  mul        tp, a6, tp
                  div        gp, s8, gp
                  div        gp, s8, gp
                  nop
                  nop
                  add        s3, s11, a6
                  lui        tp, 195546
                  auipc      s11, 688967 #end riscv_int_numeric_corner_stream_14
                  srai       s10, s1, 24
                  srai       s10, s1, 24
                  addi       a7, t2, -784
                  c.lui      a0, 24
                  mulhsu     gp, a1, s1
                  srai       s10, s1, 24
                  srli       s8, t6, 19
                  c.li       a7, 27
                  c.srai     s0, 31
                  srl        a0, s2, a0
                  rem        s0, a3, a2
                  remu       s5, s11, t1
                  addi       a7, t2, -784
                  srai       s10, s1, 24
                  slti       tp, t6, 301
                  add        s7, s5, a6
                  c.and      a0, s0
                  mul        sp, s9, s11
                  slli       s11, gp, 14
                  and        a1, t3, a6
                  slti       tp, t6, 301
                  c.and      a0, s0
                  c.mv       a1, s5
                  add        s7, s5, a6
                  slt        t1, a1, a4
                  remu       s5, s11, t1
                  divu       sp, ra, t0
                  slli       s11, gp, 14
                  c.lui      a0, 24
                  andi       s8, t1, -26
                  c.addi     s1, 6
                  srli       s8, t6, 19
                  and        a1, t3, a6
                  lui        zero, 195546
                  c.add      t1, a1
                  sll        t3, s7, a3
                  c.slli     t4, 28
                  xori       a4, t0, 974
                  c.mv       a1, s5
                  c.andi     a5, -1
                  or         s0, a2, a0
                  slt        t1, a1, a4
                  slt        t1, a1, a4
                  sra        s1, t3, s1
                  srl        a0, s2, a0
                  add        s7, s5, a6
                  c.nop
                  c.addi16sp sp, 16
                  sltiu      s6, ra, 913
                  ori        t5, t2, 999
                  c.sub      s1, a4
                  mul        sp, s9, s11
                  mulhsu     gp, a1, s1
                  srli       s8, t6, 19
                  c.srai     s0, 31
                  or         s0, a2, a0
                  c.mv       a1, s5
                  xor        t4, s3, t3
                  c.nop
                  srl        a0, s2, a0
                  addi       a7, t2, -784
                  auipc      t6, 688967
                  sltiu      s6, ra, 913
                  c.or       a5, a1
                  addi       a7, t2, -784
                  nop
                  c.lui      a0, 24
                  c.lui      a0, 24
                  c.add      t1, a1
                  divu       sp, ra, t0
                  ori        t5, t2, 999
                  c.nop
                  c.slli     t4, 28
                  remu       s5, s11, t1
                  sltu       t2, s1, t1
                  rem        s0, a3, a2
                  c.add      t1, a1
                  mulhu      tp, s3, a4
                  sub        s9, s6, s5
                  srai       s10, s1, 24
                  srl        a0, s2, a0
                  sub        s9, s6, s5
                  c.slli     t4, 28
                  c.srai     s0, 31
                  srl        a0, s2, a0
                  c.or       a5, a1
                  c.sub      s1, a4
                  c.li       a7, 27
                  div        t3, t1, t5
                  srli       s8, t6, 19
                  c.addi16sp sp, 16
                  lui        zero, 195546
                  div        t3, t1, t5
                  c.xor      a1, a2
                  c.addi16sp sp, 16
                  mulhsu     gp, a1, s1
                  c.or       a5, a1
                  slti       tp, t6, 301
                  andi       s8, t1, -26
                  sra        s1, t3, s1
                  mul        sp, s9, s11
                  sra        s1, t3, s1
                  andi       s8, t1, -26
                  slti       tp, t6, 301
                  c.xor      a1, a2
                  or         s0, a2, a0
                  c.lui      a0, 24
                  mulh       s11, s1, s9
                  nop
                  c.mv       a1, s5
                  or         s0, a2, a0
                  add        s7, s5, a6
                  nop
                  srai       s10, s1, 24
                  mulhu      tp, s3, a4
                  sra        s1, t3, s1
                  c.slli     t4, 28
                  andi       s8, t1, -26
                  li         sp, 0x65e8c87c #start riscv_int_numeric_corner_stream_24
                  li         s8, 0x0
                  li         s7, 0x0
                  li         s11, 0xffffffff
                  li         s0, 0x80000000
                  li         t1, 0xf2fed3a2
                  li         gp, 0x933359ef
                  li         t3, 0x80000000
                  li         s6, 0x80000000
                  li         a4, 0x31bba2df
                  sub        sp, s8, a4
                  remu       s7, a4, s0
                  rem        s8, a4, s0
                  lui        s0, 195546
                  addi       s0, s7, 999
                  lui        s0, 195546
                  nop
                  div        gp, s0, a4
                  mul        gp, s7, s8
                  add        gp, a4, s8
                  sub        sp, s8, a4
                  rem        s8, a4, s0
                  remu       s7, a4, s0
                  add        gp, a4, s8
                  rem        s8, a4, s0
                  addi       s0, s7, 999
                  nop #end riscv_int_numeric_corner_stream_24
                  mul        sp, s9, s11
                  c.mv       a1, s5
                  c.addi     s1, 6
                  and        a1, t3, a6
                  addi       a7, t2, -784
                  c.li       a7, 27
                  srai       s10, s1, 24
                  and        a1, t3, a6
                  c.add      t1, a1
                  c.srai     s0, 31
                  srli       s8, t6, 19
                  c.andi     a5, -1
                  c.addi     s1, 6
                  c.andi     a5, -1
                  c.addi16sp sp, 16
                  mulhu      tp, s3, a4
                  lui        zero, 195546
                  sltiu      s6, ra, 913
                  c.li       a7, 27
                  sltiu      s6, ra, 913
                  divu       sp, ra, t0
                  c.addi     s1, 6
                  sll        t3, s7, a3
                  c.addi     s1, 6
                  c.addi     s1, 6
                  c.xor      a1, a2
                  c.srai     s0, 31
                  xor        t4, s3, t3
                  addi       a7, t2, -784
                  xor        t4, s3, t3
                  sra        s1, t3, s1
                  nop
                  mulhsu     gp, a1, s1
                  c.sub      s1, a4
                  c.addi     s1, 6
                  mulhsu     gp, a1, s1
                  srai       s10, s1, 24
                  srli       s8, t6, 19
                  c.xor      a1, a2
                  c.li       a7, 27
                  addi       a7, t2, -784
                  xor        t4, s3, t3
                  slli       s11, gp, 14
                  mulhsu     gp, a1, s1
                  srli       s8, t6, 19
                  auipc      t6, 688967
                  add        s7, s5, a6
                  sra        s1, t3, s1
                  mulh       s11, s1, s9
                  add        s7, s5, a6
                  c.nop
                  srl        a0, s2, a0
                  divu       sp, ra, t0
                  c.slli     t4, 28
                  c.or       a5, a1
                  andi       s8, t1, -26
                  sll        t3, s7, a3
                  xor        t4, s3, t3
                  remu       s5, s11, t1
                  srli       s8, t6, 19
                  mulhu      tp, s3, a4
                  c.andi     a5, -1
                  c.xor      a1, a2
                  remu       s5, s11, t1
                  mulhu      tp, s3, a4
                  add        s7, s5, a6
                  sll        t3, s7, a3
                  div        t3, t1, t5
                  slti       tp, t6, 301
                  ori        t5, t2, 999
                  sra        s1, t3, s1
                  c.andi     a5, -1
                  c.sub      s1, a4
                  nop
                  ori        t5, t2, 999
                  c.and      a0, s0
                  sll        t3, s7, a3
                  c.li       a7, 27
                  andi       s8, t1, -26
                  c.and      a0, s0
                  c.lui      a0, 24
                  slt        t1, a1, a4
                  sub        s9, s6, s5
                  mulhu      tp, s3, a4
                  srl        a0, s2, a0
                  srl        a0, s2, a0
                  slti       tp, t6, 301
                  rem        s0, a3, a2
                  divu       sp, ra, t0
                  c.srai     s0, 31
                  addi       a7, t2, -784
                  lui        zero, 195546
                  c.andi     a5, -1
                  c.sub      s1, a4
                  c.nop
                  lui        zero, 195546
                  andi       s8, t1, -26
                  add        s7, s5, a6
                  or         s0, a2, a0
                  xori       a4, t0, 974
                  c.addi16sp sp, 16
                  mulhsu     gp, a1, s1
                  c.andi     a5, -1
                  or         s0, a2, a0
                  srai       s10, s1, 24
                  or         s0, a2, a0
                  c.addi4spn a4, sp, 288
                  srli       s8, t6, 19
                  mulhsu     gp, a1, s1
                  div        t3, t1, t5
                  sub        s9, s6, s5
                  c.slli     t4, 28
                  add        s7, s5, a6
                  srli       s8, t6, 19
                  nop
                  andi       s8, t1, -26
                  c.srli     a0, 25
                  div        t3, t1, t5
                  mulh       s11, s1, s9
                  c.and      a0, s0
                  slt        t1, a1, a4
                  slt        t1, a1, a4
                  add        s7, s5, a6
                  andi       s8, t1, -26
                  slti       tp, t6, 301
                  srl        a0, s2, a0
                  mul        sp, s9, s11
                  ori        t5, t2, 999
                  divu       sp, ra, t0
                  rem        s0, a3, a2
                  slti       tp, t6, 301
                  c.and      a0, s0
                  c.lui      a0, 24
                  slli       s11, gp, 14
                  ori        t5, t2, 999
                  slt        t1, a1, a4
                  ori        t5, t2, 999
                  mulhu      tp, s3, a4
                  srl        a0, s2, a0
                  c.andi     a5, -1
                  c.or       a5, a1
                  and        a1, t3, a6
                  add        s7, s5, a6
                  c.add      t1, a1
                  sll        t3, s7, a3
                  c.and      a0, s0
                  c.slli     t4, 28
                  c.sub      s1, a4
                  c.add      t1, a1
                  c.addi16sp sp, 16
                  div        t3, t1, t5
                  mulh       s11, s1, s9
                  srli       s8, t6, 19
                  add        s7, s5, a6
                  andi       s8, t1, -26
                  lui        zero, 195546
                  ori        t5, t2, 999
                  srli       s8, t6, 19
                  c.add      t1, a1
                  xori       a4, t0, 974
                  remu       s5, s11, t1
                  c.and      a0, s0
                  xori       a4, t0, 974
                  srli       s8, t6, 19
                  add        s7, s5, a6
                  divu       sp, ra, t0
                  and        a1, t3, a6
                  srai       s10, s1, 24
                  xori       a4, t0, 974
                  mul        sp, s9, s11
                  lui        zero, 195546
                  slli       s11, gp, 14
                  srli       s8, t6, 19
                  andi       s8, t1, -26
                  mulhsu     gp, a1, s1
                  divu       sp, ra, t0
                  slli       s11, gp, 14
                  c.slli     t4, 28
                  mulh       s11, s1, s9
                  andi       s8, t1, -26
                  srai       s10, s1, 24
                  addi       a7, t2, -784
                  add        s7, s5, a6
                  c.addi16sp sp, 16
                  srli       s8, t6, 19
                  xor        t4, s3, t3
                  c.srai     s0, 31
                  sra        s1, t3, s1
                  slli       s11, gp, 14
                  ori        t5, t2, 999
                  c.sub      s1, a4
                  remu       s5, s11, t1
                  c.lui      a0, 24
                  nop
                  slli       s11, gp, 14
                  sltu       t2, s1, t1
                  c.slli     t4, 28
                  srl        a0, s2, a0
                  c.srli     a0, 25
                  mulh       s11, s1, s9
                  sll        t3, s7, a3
                  sltu       t2, s1, t1
                  sll        t3, s7, a3
                  c.and      a0, s0
                  c.addi     s1, 6
                  c.lui      a0, 24
                  mulh       s11, s1, s9
                  c.srli     a0, 25
                  mulhsu     gp, a1, s1
                  sll        t3, s7, a3
                  c.srli     a0, 25
                  srl        a0, s2, a0
                  slti       tp, t6, 301
                  add        s7, s5, a6
                  mulhu      tp, s3, a4
                  c.nop
                  xori       a4, t0, 974
                  c.srai     s0, 31
                  mul        sp, s9, s11
                  nop
                  c.nop
                  c.li       a7, 27
                  nop
                  c.mv       a1, s5
                  c.xor      a1, a2
                  mulhsu     gp, a1, s1
                  mulhu      tp, s3, a4
                  c.addi     s1, 6
                  srli       s8, t6, 19
                  c.addi16sp sp, 16
                  nop
                  div        t3, t1, t5
                  c.or       a5, a1
                  srai       s10, s1, 24
                  mul        sp, s9, s11
                  nop
                  div        t3, t1, t5
                  c.xor      a1, a2
                  srli       s8, t6, 19
                  remu       s5, s11, t1
                  sub        s9, s6, s5
                  c.slli     t4, 28
                  c.li       a7, 27
                  srli       s8, t6, 19
                  c.or       a5, a1
                  lui        zero, 195546
                  c.nop
                  or         s0, a2, a0
                  c.nop
                  c.li       a7, 27
                  c.mv       a1, s5
                  mulhsu     gp, a1, s1
                  and        a1, t3, a6
                  c.addi16sp sp, 16
                  slt        t1, a1, a4
                  div        t3, t1, t5
                  sra        s1, t3, s1
                  c.lui      a0, 24
                  c.li       a7, 27
                  mul        sp, s9, s11
                  add        s7, s5, a6
                  c.nop
                  add        s7, s5, a6
                  auipc      t6, 688967
                  sll        t3, s7, a3
                  c.addi4spn a4, sp, 288
                  rem        s0, a3, a2
                  c.and      a0, s0
                  sltiu      s6, ra, 913
                  c.add      t1, a1
                  mul        sp, s9, s11
                  xori       a4, t0, 974
                  c.lui      a0, 24
                  sll        t3, s7, a3
                  divu       sp, ra, t0
                  add        s7, s5, a6
                  c.lui      a0, 24
                  slti       tp, t6, 301
                  mulhsu     gp, a1, s1
                  rem        s0, a3, a2
                  c.li       a7, 27
                  addi       a7, t2, -784
                  xori       a4, t0, 974
                  c.andi     a5, -1
                  srli       s8, t6, 19
                  srli       s8, t6, 19
                  c.li       a7, 27
                  c.addi     s1, 6
                  divu       sp, ra, t0
                  c.addi     s1, 6
                  srl        a0, s2, a0
                  nop
                  sll        t3, s7, a3
                  c.mv       a1, s5
                  c.addi16sp sp, 16
                  mulhu      tp, s3, a4
                  c.xor      a1, a2
                  c.addi16sp sp, 16
                  add        s7, s5, a6
                  xor        t4, s3, t3
                  c.xor      a1, a2
                  c.add      t1, a1
                  mulh       s11, s1, s9
                  sltiu      s6, ra, 913
                  c.lui      a0, 24
                  c.xor      a1, a2
                  div        t3, t1, t5
                  auipc      t6, 688967
                  sltiu      s6, ra, 913
                  lui        zero, 195546
                  c.lui      a0, 24
                  c.nop
                  sub        s9, s6, s5
                  sltiu      s6, ra, 913
                  remu       s5, s11, t1
                  nop
                  sub        s9, s6, s5
                  mul        sp, s9, s11
                  c.slli     t4, 28
                  slti       tp, t6, 301
                  slti       tp, t6, 301
                  xori       a4, t0, 974
                  sub        s9, s6, s5
                  sll        t3, s7, a3
                  c.sub      s1, a4
                  divu       sp, ra, t0
                  c.add      t1, a1
                  mul        sp, s9, s11
                  div        t3, t1, t5
                  remu       s5, s11, t1
                  sltu       t2, s1, t1
                  ori        t5, t2, 999
                  srai       s10, s1, 24
                  ori        t5, t2, 999
                  c.addi4spn a4, sp, 288
                  c.sub      s1, a4
                  slti       tp, t6, 301
                  divu       sp, ra, t0
                  c.andi     a5, -1
                  c.lui      a0, 24
                  srli       s8, t6, 19
                  c.addi     s1, 6
                  c.xor      a1, a2
                  sra        s1, t3, s1
                  c.lui      a0, 24
                  andi       s8, t1, -26
                  slli       s11, gp, 14
                  srli       s8, t6, 19
                  srli       s8, t6, 19
                  and        a1, t3, a6
                  c.xor      a1, a2
                  slli       s11, gp, 14
                  and        a1, t3, a6
                  sltu       t2, s1, t1
                  srl        a0, s2, a0
                  slt        t1, a1, a4
                  c.xor      a1, a2
                  ori        t5, t2, 999
                  slti       tp, t6, 301
                  xori       a4, t0, 974
                  addi       a7, t2, -784
                  c.or       a5, a1
                  mul        sp, s9, s11
                  slt        t1, a1, a4
                  srl        a0, s2, a0
                  mul        sp, s9, s11
                  c.addi     s1, 6
                  srai       s10, s1, 24
                  c.addi4spn a4, sp, 288
                  c.and      a0, s0
                  li         s1, 0xffffffff #start riscv_int_numeric_corner_stream_3
                  li         s0, 0xffffffff
                  li         a1, 0x5e48d745
                  li         a6, 0xffffffff
                  li         t3, 0xffffffff
                  li         tp, 0x80000000
                  li         t5, 0xffffffff
                  li         t4, 0x0
                  li         s6, 0x0
                  li         s7, 0xffffffff
                  lui        tp, 195546
                  add        s1, t5, a6
                  sub        a1, t3, tp
                  nop
                  nop
                  auipc      t4, 688967
                  remu       s7, a1, s0
                  remu       s7, a1, s0
                  auipc      t4, 688967
                  nop
                  div        s7, a6, s6
                  auipc      t4, 688967
                  auipc      t4, 688967
                  sub        a1, t3, tp
                  nop
                  div        s7, a6, s6
                  add        s1, t5, a6
                  mulh       s7, t4, t4
                  auipc      t4, 688967
                  nop
                  auipc      t4, 688967
                  nop
                  addi       tp, s6, 999
                  sub        a1, t3, tp
                  remu       s7, a1, s0
                  nop
                  mulhu      tp, a1, s1 #end riscv_int_numeric_corner_stream_3
                  c.mv       a1, s5
                  add        s7, s5, a6
                  sltiu      s6, ra, 913
                  c.add      t1, a1
                  mulh       s11, s1, s9
                  add        s7, s5, a6
                  c.andi     a5, -1
                  xor        t4, s3, t3
                  div        t3, t1, t5
                  srli       s8, t6, 19
                  or         s0, a2, a0
                  c.xor      a1, a2
                  c.addi4spn a4, sp, 288
                  c.mv       a1, s5
                  c.addi     s1, 6
                  c.addi     s1, 6
                  srai       s10, s1, 24
                  c.sub      s1, a4
                  c.nop
                  sltiu      s6, ra, 913
                  srai       s10, s1, 24
                  c.lui      a0, 24
                  c.addi16sp sp, 16
                  sll        t3, s7, a3
                  c.addi4spn a4, sp, 288
                  c.andi     a5, -1
                  c.xor      a1, a2
                  c.and      a0, s0
                  li         a6, 0x0 #start riscv_int_numeric_corner_stream_10
                  li         ra, 0x8ff08a33
                  li         s2, 0x0
                  li         s5, 0xffffffff
                  li         a0, 0x44530758
                  li         s9, 0xffffffff
                  li         t2, 0x0
                  li         s3, 0x0
                  li         a7, 0x4391f359
                  li         sp, 0x0
                  rem        a0, a6, a0
                  nop
                  nop
                  sub        a6, sp, t2
                  lui        ra, 195546
                  nop
                  nop
                  nop
                  nop
                  mul        t2, s2, a0
                  mulhsu     a0, a6, a7
                  add        s9, sp, a7
                  mulh       s9, t2, s5
                  mulhu      s9, t2, ra
                  nop #end riscv_int_numeric_corner_stream_10
                  c.srai     s0, 31
                  or         s0, a2, a0
                  srl        a0, s2, a0
                  c.mv       a1, s5
                  c.and      a0, s0
                  andi       s8, t1, -26
                  c.nop
                  c.sub      s1, a4
                  srai       s10, s1, 24
                  c.andi     a5, -1
                  add        s7, s5, a6
                  c.li       a7, 27
                  andi       s8, t1, -26
                  mulhu      tp, s3, a4
                  div        t3, t1, t5
                  c.addi4spn a4, sp, 288
                  li         t6, 0x0 #start riscv_int_numeric_corner_stream_4
                  li         tp, 0x5e6c1d6f
                  li         s0, 0xdde826d1
                  li         a6, 0x80000000
                  li         ra, 0xadbbc3fe
                  li         s7, 0xffffffff
                  li         s11, 0xffffffff
                  li         a4, 0x24719b7e
                  li         s9, 0x4cd82e1b
                  li         t4, 0x0
                  rem        s7, t4, s0
                  lui        tp, 195546
                  add        ra, a6, s9
                  mulhsu     a4, s9, a6
                  nop
                  auipc      t6, 688967
                  mulhu      tp, s11, ra
                  sub        t4, a6, tp
                  add        ra, a6, s9
                  rem        s7, t4, s0
                  mulhsu     a4, s9, a6
                  mulh       s7, s7, t4
                  mul        t4, a6, a6
                  nop
                  addi       a6, s7, 999
                  divu       s0, s0, t4
                  divu       s0, s0, t4
                  lui        tp, 195546 #end riscv_int_numeric_corner_stream_4
                  remu       s5, s11, t1
                  slli       s11, gp, 14
                  c.srai     s0, 31
                  c.add      t1, a1
                  addi       a7, t2, -784
                  remu       s5, s11, t1
                  sub        s9, s6, s5
                  slt        t1, a1, a4
                  c.or       a5, a1
                  mul        sp, s9, s11
                  c.srai     s0, 31
                  sltu       t2, s1, t1
                  slt        t1, a1, a4
                  or         s0, a2, a0
                  sll        t3, s7, a3
                  rem        s0, a3, a2
                  c.lui      a0, 24
                  div        t3, t1, t5
                  c.lui      a0, 24
                  slti       tp, t6, 301
                  c.xor      a1, a2
                  srli       s8, t6, 19
                  sltiu      s6, ra, 913
                  mulhsu     gp, a1, s1
                  srai       s10, s1, 24
                  rem        s0, a3, a2
                  mulhsu     gp, a1, s1
                  add        s7, s5, a6
                  mulhsu     gp, a1, s1
                  sltiu      s6, ra, 913
                  addi       a7, t2, -784
                  sll        t3, s7, a3
                  slt        t1, a1, a4
                  divu       sp, ra, t0
                  mulh       s11, s1, s9
                  sltiu      s6, ra, 913
                  sltu       t2, s1, t1
                  xor        t4, s3, t3
                  xor        t4, s3, t3
                  rem        s0, a3, a2
                  slli       s11, gp, 14
                  c.or       a5, a1
                  rem        s0, a3, a2
                  div        t3, t1, t5
                  remu       s5, s11, t1
                  c.srli     a0, 25
                  mulh       s11, s1, s9
                  add        s7, s5, a6
                  div        t3, t1, t5
                  slli       s11, gp, 14
                  mulhsu     gp, a1, s1
                  c.srli     a0, 25
                  slti       tp, t6, 301
                  xor        t4, s3, t3
                  xori       a4, t0, 974
                  slli       s11, gp, 14
                  c.li       a7, 27
                  c.nop
                  srl        a0, s2, a0
                  c.xor      a1, a2
                  c.andi     a5, -1
                  c.li       a7, 27
                  or         s0, a2, a0
                  c.nop
                  srl        a0, s2, a0
                  srai       s10, s1, 24
                  c.mv       a1, s5
                  xori       a4, t0, 974
                  xori       a4, t0, 974
                  srl        a0, s2, a0
                  c.mv       a1, s5
                  c.or       a5, a1
                  c.srli     a0, 25
                  slti       tp, t6, 301
                  c.srli     a0, 25
                  srli       s8, t6, 19
                  c.mv       a1, s5
                  c.srai     s0, 31
                  c.nop
                  nop
                  slli       s11, gp, 14
                  srli       s8, t6, 19
                  srai       s10, s1, 24
                  c.and      a0, s0
                  add        s7, s5, a6
                  c.slli     t4, 28
                  srli       s8, t6, 19
                  srl        a0, s2, a0
                  add        s7, s5, a6
                  or         s0, a2, a0
                  mulhsu     gp, a1, s1
                  c.slli     t4, 28
                  c.slli     t4, 28
                  srli       s8, t6, 19
                  slti       tp, t6, 301
                  sltiu      s6, ra, 913
                  remu       s5, s11, t1
                  srai       s10, s1, 24
                  c.li       a7, 27
                  remu       s5, s11, t1
                  slti       tp, t6, 301
                  c.nop
                  sra        s1, t3, s1
                  c.add      t1, a1
                  sub        s9, s6, s5
                  mul        sp, s9, s11
                  sltiu      s6, ra, 913
                  slli       s11, gp, 14
                  srai       s10, s1, 24
                  lui        zero, 195546
                  nop
                  mulh       s11, s1, s9
                  srl        a0, s2, a0
                  c.xor      a1, a2
                  c.lui      a0, 24
                  srl        a0, s2, a0
                  c.xor      a1, a2
                  rem        s0, a3, a2
                  add        s7, s5, a6
                  rem        s0, a3, a2
                  or         s0, a2, a0
                  c.li       a7, 27
                  c.li       a7, 27
                  nop
                  rem        s0, a3, a2
                  rem        s0, a3, a2
                  sltiu      s6, ra, 913
                  rem        s0, a3, a2
                  nop
                  c.or       a5, a1
                  slt        t1, a1, a4
                  c.addi     s1, 6
                  and        a1, t3, a6
                  or         s0, a2, a0
                  mul        sp, s9, s11
                  c.addi4spn a4, sp, 288
                  mulhsu     gp, a1, s1
                  c.srai     s0, 31
                  addi       a7, t2, -784
                  mulh       s11, s1, s9
                  or         s0, a2, a0
                  srl        a0, s2, a0
                  c.srli     a0, 25
                  sltiu      s6, ra, 913
                  c.addi     s1, 6
                  addi       a7, t2, -784
                  srl        a0, s2, a0
                  c.sub      s1, a4
                  lui        zero, 195546
                  xor        t4, s3, t3
                  c.mv       a1, s5
                  c.mv       a1, s5
                  c.mv       a1, s5
                  c.nop
                  mulhu      tp, s3, a4
                  remu       s5, s11, t1
                  c.sub      s1, a4
                  c.xor      a1, a2
                  c.addi16sp sp, 16
                  div        t3, t1, t5
                  and        a1, t3, a6
                  sll        t3, s7, a3
                  c.and      a0, s0
                  sub        s9, s6, s5
                  remu       s5, s11, t1
                  c.lui      a0, 24
                  c.add      t1, a1
                  c.xor      a1, a2
                  c.and      a0, s0
                  sll        t3, s7, a3
                  sub        s9, s6, s5
                  slt        t1, a1, a4
                  c.slli     t4, 28
                  c.srai     s0, 31
                  srai       s10, s1, 24
                  slt        t1, a1, a4
                  sll        t3, s7, a3
                  c.andi     a5, -1
                  c.and      a0, s0
                  lui        zero, 195546
                  rem        s0, a3, a2
                  c.li       a7, 27
                  sll        t3, s7, a3
                  ori        t5, t2, 999
                  mulhsu     gp, a1, s1
                  c.sub      s1, a4
                  c.srli     a0, 25
                  or         s0, a2, a0
                  add        s7, s5, a6
                  srli       s8, t6, 19
                  c.and      a0, s0
                  c.addi     s1, 6
                  c.addi     s1, 6
                  c.lui      a0, 24
                  c.lui      a0, 24
                  c.add      t1, a1
                  c.or       a5, a1
                  slt        t1, a1, a4
                  c.srli     a0, 25
                  auipc      t6, 688967
                  addi       a7, t2, -784
                  divu       sp, ra, t0
                  nop
                  sra        s1, t3, s1
                  c.addi4spn a4, sp, 288
                  c.slli     t4, 28
                  and        a1, t3, a6
                  c.sub      s1, a4
                  c.srli     a0, 25
                  lui        zero, 195546
                  c.mv       a1, s5
                  srli       s8, t6, 19
                  c.xor      a1, a2
                  c.srli     a0, 25
                  div        t3, t1, t5
                  slti       tp, t6, 301
                  c.and      a0, s0
                  or         s0, a2, a0
                  c.add      t1, a1
                  c.addi4spn a4, sp, 288
                  lui        zero, 195546
                  slt        t1, a1, a4
                  c.sub      s1, a4
                  sll        t3, s7, a3
                  slt        t1, a1, a4
                  xori       a4, t0, 974
                  mulhsu     gp, a1, s1
                  c.mv       a1, s5
                  c.lui      a0, 24
                  c.nop
                  sltiu      s6, ra, 913
                  slt        t1, a1, a4
                  rem        s0, a3, a2
                  c.andi     a5, -1
                  sra        s1, t3, s1
                  li         s1, 0xffffffff #start riscv_int_numeric_corner_stream_20
                  li         s2, 0x80000000
                  li         t5, 0x76bbf178
                  li         s6, 0x80000000
                  li         s5, 0x80000000
                  li         ra, 0x0
                  li         s0, 0x0
                  li         a5, 0xffffffff
                  li         gp, 0x1b14077b
                  li         a6, 0x0
                  lui        ra, 195546
                  mulh       t5, s5, s5
                  auipc      t5, 688967
                  lui        ra, 195546
                  lui        ra, 195546
                  mulhu      ra, a5, s1
                  add        s1, a5, a6
                  addi       a6, s5, 999
                  addi       a6, s5, 999
                  mulh       t5, s5, s5
                  nop
                  add        s1, a5, a6
                  mulhsu     a5, s6, a6
                  nop
                  sub        s5, a6, s6
                  auipc      t5, 688967
                  add        s1, a5, a6
                  nop
                  mul        ra, t5, t5
                  nop
                  add        s1, a5, a6
                  nop
                  auipc      t5, 688967
                  rem        s0, a5, s0 #end riscv_int_numeric_corner_stream_20
                  sltiu      s6, ra, 913
                  addi       a7, t2, -784
                  c.srai     s0, 31
                  divu       sp, ra, t0
                  auipc      t6, 688967
                  c.xor      a1, a2
                  nop
                  c.srai     s0, 31
                  sub        s9, s6, s5
                  c.srai     s0, 31
                  c.andi     a5, -1
                  div        t3, t1, t5
                  c.li       a7, 27
                  or         s0, a2, a0
                  mulh       s11, s1, s9
                  sltiu      s6, ra, 913
                  mulhsu     gp, a1, s1
                  c.mv       a1, s5
                  c.slli     t4, 28
                  srl        a0, s2, a0
                  c.mv       a1, s5
                  mulh       s11, s1, s9
                  c.or       a5, a1
                  xor        t4, s3, t3
                  c.srli     a0, 25
                  srl        a0, s2, a0
                  c.sub      s1, a4
                  sltiu      s6, ra, 913
                  c.mv       a1, s5
                  mulhsu     gp, a1, s1
                  sltiu      s6, ra, 913
                  lui        zero, 195546
                  c.andi     a5, -1
                  sltiu      s6, ra, 913
                  mulh       s11, s1, s9
                  xori       a4, t0, 974
                  c.srai     s0, 31
                  slt        t1, a1, a4
                  c.srai     s0, 31
                  rem        s0, a3, a2
                  sll        t3, s7, a3
                  xor        t4, s3, t3
                  xor        t4, s3, t3
                  c.addi4spn a4, sp, 288
                  c.mv       a1, s5
                  and        a1, t3, a6
                  sra        s1, t3, s1
                  div        t3, t1, t5
                  c.slli     t4, 28
                  mulh       s11, s1, s9
                  c.mv       a1, s5
                  nop
                  div        t3, t1, t5
                  sra        s1, t3, s1
                  c.addi     s1, 6
                  c.lui      a0, 24
                  andi       s8, t1, -26
                  sltiu      s6, ra, 913
                  c.slli     t4, 28
                  sltu       t2, s1, t1
                  sltiu      s6, ra, 913
                  c.andi     a5, -1
                  c.nop
                  sll        t3, s7, a3
                  mulh       s11, s1, s9
                  c.lui      a0, 24
                  c.lui      a0, 24
                  mulh       s11, s1, s9
                  xor        t4, s3, t3
                  mulhu      tp, s3, a4
                  or         s0, a2, a0
                  c.slli     t4, 28
                  xori       a4, t0, 974
                  c.addi4spn a4, sp, 288
                  mul        sp, s9, s11
                  c.andi     a5, -1
                  c.and      a0, s0
                  c.srai     s0, 31
                  rem        s0, a3, a2
                  add        s7, s5, a6
                  andi       s8, t1, -26
                  addi       a7, t2, -784
                  xori       a4, t0, 974
                  srli       s8, t6, 19
                  nop
                  divu       sp, ra, t0
                  c.and      a0, s0
                  srai       s10, s1, 24
                  c.srai     s0, 31
                  srl        a0, s2, a0
                  sra        s1, t3, s1
                  nop
                  sll        t3, s7, a3
                  mul        sp, s9, s11
                  sll        t3, s7, a3
                  auipc      t6, 688967
                  c.addi     s1, 6
                  c.and      a0, s0
                  mul        sp, s9, s11
                  rem        s0, a3, a2
                  srl        a0, s2, a0
                  c.add      t1, a1
                  mulhu      tp, s3, a4
                  and        a1, t3, a6
                  mulhu      tp, s3, a4
                  xor        t4, s3, t3
                  addi       a7, t2, -784
                  andi       s8, t1, -26
                  c.addi16sp sp, 16
                  srai       s10, s1, 24
                  sub        s9, s6, s5
                  andi       s8, t1, -26
                  or         s0, a2, a0
                  slt        t1, a1, a4
                  sltu       t2, s1, t1
                  c.xor      a1, a2
                  div        t3, t1, t5
                  c.or       a5, a1
                  srli       s8, t6, 19
                  mulh       s11, s1, s9
                  div        t3, t1, t5
                  or         s0, a2, a0
                  mulhsu     gp, a1, s1
                  mulhu      tp, s3, a4
                  sra        s1, t3, s1
                  c.lui      a0, 24
                  slti       tp, t6, 301
                  c.xor      a1, a2
                  xori       a4, t0, 974
                  ori        t5, t2, 999
                  c.addi     s1, 6
                  c.mv       a1, s5
                  add        s7, s5, a6
                  srli       s8, t6, 19
                  c.add      t1, a1
                  c.srli     a0, 25
                  divu       sp, ra, t0
                  c.addi     s1, 6
                  c.add      t1, a1
                  c.sub      s1, a4
                  sra        s1, t3, s1
                  sltu       t2, s1, t1
                  xori       a4, t0, 974
                  slti       tp, t6, 301
                  c.andi     a5, -1
                  and        a1, t3, a6
                  c.srai     s0, 31
                  divu       sp, ra, t0
                  c.andi     a5, -1
                  c.or       a5, a1
                  slt        t1, a1, a4
                  c.andi     a5, -1
                  sltiu      s6, ra, 913
                  sub        s9, s6, s5
                  c.li       a7, 27
                  c.srai     s0, 31
                  srli       s8, t6, 19
                  remu       s5, s11, t1
                  mul        sp, s9, s11
                  c.or       a5, a1
                  lui        zero, 195546
                  c.sub      s1, a4
                  c.slli     t4, 28
                  divu       sp, ra, t0
                  div        t3, t1, t5
                  andi       s8, t1, -26
                  sra        s1, t3, s1
                  c.or       a5, a1
                  sltiu      s6, ra, 913
                  c.addi4spn a4, sp, 288
                  divu       sp, ra, t0
                  slli       s11, gp, 14
                  slli       s11, gp, 14
                  c.xor      a1, a2
                  addi       a7, t2, -784
                  and        a1, t3, a6
                  xori       a4, t0, 974
                  c.or       a5, a1
                  slti       tp, t6, 301
                  divu       sp, ra, t0
                  div        t3, t1, t5
                  mul        sp, s9, s11
                  sltu       t2, s1, t1
                  sltiu      s6, ra, 913
                  sub        s9, s6, s5
                  c.lui      a0, 24
                  c.sub      s1, a4
                  auipc      t6, 688967
                  c.srai     s0, 31
                  remu       s5, s11, t1
                  auipc      t6, 688967
                  remu       s5, s11, t1
                  c.addi4spn a4, sp, 288
                  c.andi     a5, -1
                  sra        s1, t3, s1
                  div        t3, t1, t5
                  c.andi     a5, -1
                  mulhu      tp, s3, a4
                  mulh       s11, s1, s9
                  c.add      t1, a1
                  mulhu      tp, s3, a4
                  c.addi4spn a4, sp, 288
                  slti       tp, t6, 301
                  sltiu      s6, ra, 913
                  c.slli     t4, 28
                  c.srai     s0, 31
                  c.andi     a5, -1
                  mulhu      tp, s3, a4
                  slti       tp, t6, 301
                  divu       sp, ra, t0
                  slti       tp, t6, 301
                  slli       s11, gp, 14
                  remu       s5, s11, t1
                  slti       tp, t6, 301
                  c.and      a0, s0
                  c.slli     t4, 28
                  and        a1, t3, a6
                  c.andi     a5, -1
                  sltiu      s6, ra, 913
                  slli       s11, gp, 14
                  xor        t4, s3, t3
                  srli       s8, t6, 19
                  andi       s8, t1, -26
                  c.addi16sp sp, 16
                  sll        t3, s7, a3
                  c.addi16sp sp, 16
                  remu       s5, s11, t1
                  srli       s8, t6, 19
                  slli       s11, gp, 14
                  c.lui      a0, 24
                  c.addi     s1, 6
                  or         s0, a2, a0
                  slli       s11, gp, 14
                  c.mv       a1, s5
                  c.add      t1, a1
                  remu       s5, s11, t1
                  mul        sp, s9, s11
                  srl        a0, s2, a0
                  c.add      t1, a1
                  sltiu      s6, ra, 913
                  c.andi     a5, -1
                  mulhu      tp, s3, a4
                  lui        zero, 195546
                  c.srai     s0, 31
                  slt        t1, a1, a4
                  c.mv       a1, s5
                  rem        s0, a3, a2
                  rem        s0, a3, a2
                  srai       s10, s1, 24
                  auipc      t6, 688967
                  c.nop
                  and        a1, t3, a6
                  c.addi16sp sp, 16
                  auipc      t6, 688967
                  div        t3, t1, t5
                  srai       s10, s1, 24
                  xor        t4, s3, t3
                  sra        s1, t3, s1
                  c.slli     t4, 28
                  ori        t5, t2, 999
                  auipc      t6, 688967
                  addi       a7, t2, -784
                  slli       s11, gp, 14
                  mulhsu     gp, a1, s1
                  and        a1, t3, a6
                  add        s7, s5, a6
                  c.xor      a1, a2
                  xori       a4, t0, 974
                  c.addi     s1, 6
                  c.srli     a0, 25
                  sll        t3, s7, a3
                  sll        t3, s7, a3
                  c.add      t1, a1
                  divu       sp, ra, t0
                  c.li       a7, 27
                  srl        a0, s2, a0
                  mul        sp, s9, s11
                  c.and      a0, s0
                  c.or       a5, a1
                  div        t3, t1, t5
                  ori        t5, t2, 999
                  mul        sp, s9, s11
                  add        s7, s5, a6
                  c.mv       a1, s5
                  mulhsu     gp, a1, s1
                  srli       s8, t6, 19
                  c.andi     a5, -1
                  c.add      t1, a1
                  slli       s11, gp, 14
                  andi       s8, t1, -26
                  mulh       s11, s1, s9
                  or         s0, a2, a0
                  mul        sp, s9, s11
                  c.srai     s0, 31
                  sltu       t2, s1, t1
                  c.srai     s0, 31
                  sltu       t2, s1, t1
                  sub        s9, s6, s5
                  andi       s8, t1, -26
                  sll        t3, s7, a3
                  sub        s9, s6, s5
                  c.andi     a5, -1
                  add        s7, s5, a6
                  slli       s11, gp, 14
                  div        t3, t1, t5
                  andi       s8, t1, -26
                  c.lui      a0, 24
                  c.slli     t4, 28
                  c.addi4spn a4, sp, 288
                  add        s7, s5, a6
                  remu       s5, s11, t1
                  c.nop
                  xori       a4, t0, 974
                  add        s7, s5, a6
                  sltu       t2, s1, t1
                  c.and      a0, s0
                  sll        t3, s7, a3
                  srli       s8, t6, 19
                  sltiu      s6, ra, 913
                  mulh       s11, s1, s9
                  addi       a7, t2, -784
                  mulh       s11, s1, s9
                  lui        zero, 195546
                  c.or       a5, a1
                  c.xor      a1, a2
                  mulhsu     gp, a1, s1
                  srl        a0, s2, a0
                  auipc      t6, 688967
                  c.addi     s1, 6
                  and        a1, t3, a6
                  or         s0, a2, a0
                  sltiu      s6, ra, 913
                  c.addi16sp sp, 16
                  lui        zero, 195546
                  c.lui      a0, 24
                  c.or       a5, a1
                  c.mv       a1, s5
                  c.andi     a5, -1
                  c.nop
                  lui        zero, 195546
                  xori       a4, t0, 974
                  li         s5, 0x80000000 #start riscv_int_numeric_corner_stream_36
                  li         a5, 0xe22a63ce
                  li         a7, 0x80000000
                  li         a1, 0xffffffff
                  li         t3, 0x1cea3d51
                  li         a6, 0x4b0eafba
                  li         a0, 0x36dd1f9f
                  li         t4, 0xffffffff
                  li         a4, 0x80000000
                  li         ra, 0xffffffff
                  remu       a6, a1, a0
                  div        ra, a6, a0
                  div        ra, a6, a0
                  mul        ra, t4, t3
                  lui        ra, 195546
                  addi       ra, s5, 999
                  nop
                  addi       ra, s5, 999
                  addi       ra, s5, 999
                  nop
                  addi       ra, s5, 999
                  mulhu      a6, a4, ra
                  div        ra, a6, a0
                  add        ra, a6, a7
                  nop #end riscv_int_numeric_corner_stream_36
                  c.srai     s0, 31
                  slt        t1, a1, a4
                  mulh       s11, s1, s9
                  c.andi     a5, -1
                  c.and      a0, s0
                  c.addi16sp sp, 16
                  xor        t4, s3, t3
                  c.srli     a0, 25
                  sub        s9, s6, s5
                  c.srli     a0, 25
                  c.addi     s1, 6
                  auipc      t6, 688967
                  mulhsu     gp, a1, s1
                  ori        t5, t2, 999
                  srai       s10, s1, 24
                  c.sub      s1, a4
                  slti       tp, t6, 301
                  remu       s5, s11, t1
                  c.sub      s1, a4
                  mul        sp, s9, s11
                  c.or       a5, a1
                  c.add      t1, a1
                  or         s0, a2, a0
                  slli       s11, gp, 14
                  xor        t4, s3, t3
                  sra        s1, t3, s1
                  lui        zero, 195546
                  ori        t5, t2, 999
                  c.xor      a1, a2
                  c.srai     s0, 31
                  c.mv       a1, s5
                  slti       tp, t6, 301
                  sub        s9, s6, s5
                  mul        sp, s9, s11
                  mulhsu     gp, a1, s1
                  srai       s10, s1, 24
                  rem        s0, a3, a2
                  slti       tp, t6, 301
                  xor        t4, s3, t3
                  sltiu      s6, ra, 913
                  mulhu      tp, s3, a4
                  xori       a4, t0, 974
                  c.li       a7, 27
                  c.srli     a0, 25
                  c.nop
                  sra        s1, t3, s1
                  sll        t3, s7, a3
                  c.add      t1, a1
                  c.nop
                  slt        t1, a1, a4
                  mulh       s11, s1, s9
                  c.and      a0, s0
                  ori        t5, t2, 999
                  sll        t3, s7, a3
                  c.addi16sp sp, 16
                  li         s8, 0xffffffff #start riscv_int_numeric_corner_stream_29
                  li         s11, 0x80000000
                  li         t1, 0xab55c50e
                  li         a0, 0x80000000
                  li         s10, 0x0
                  li         s7, 0x1018821
                  li         s1, 0x9ce6fbd3
                  li         ra, 0x80000000
                  li         s3, 0xffffffff
                  li         s9, 0x80000000
                  sub        ra, s8, t1
                  nop
                  lui        ra, 195546
                  nop
                  remu       t1, t1, a0
                  add        s1, a0, s8
                  remu       t1, t1, a0
                  nop
                  nop
                  mulhsu     s8, s8, s3
                  addi       ra, s7, 999
                  nop
                  lui        ra, 195546
                  sub        ra, s8, t1
                  nop #end riscv_int_numeric_corner_stream_29
                  c.li       a7, 27
                  mulhu      tp, s3, a4
                  add        s7, s5, a6
                  add        s7, s5, a6
                  and        a1, t3, a6
                  srl        a0, s2, a0
                  c.srai     s0, 31
                  c.li       a7, 27
                  remu       s5, s11, t1
                  and        a1, t3, a6
                  mulhu      tp, s3, a4
                  srli       s8, t6, 19
                  srai       s10, s1, 24
                  sltiu      s6, ra, 913
                  c.addi     s1, 6
                  xor        t4, s3, t3
                  c.slli     t4, 28
                  andi       s8, t1, -26
                  or         s0, a2, a0
                  c.sub      s1, a4
                  c.mv       a1, s5
                  nop
                  c.addi4spn a4, sp, 288
                  c.xor      a1, a2
                  divu       sp, ra, t0
                  c.and      a0, s0
                  sll        t3, s7, a3
                  mulhsu     gp, a1, s1
                  mulhu      tp, s3, a4
                  or         s0, a2, a0
                  c.andi     a5, -1
                  remu       s5, s11, t1
                  rem        s0, a3, a2
                  lui        zero, 195546
                  divu       sp, ra, t0
                  c.xor      a1, a2
                  nop
                  srl        a0, s2, a0
                  mul        sp, s9, s11
                  sltu       t2, s1, t1
                  c.sub      s1, a4
                  or         s0, a2, a0
                  lui        zero, 195546
                  c.addi     s1, 6
                  or         s0, a2, a0
                  c.addi16sp sp, 16
                  nop
                  auipc      t6, 688967
                  c.add      t1, a1
                  mulhu      tp, s3, a4
                  srai       s10, s1, 24
                  sltiu      s6, ra, 913
                  c.or       a5, a1
                  ori        t5, t2, 999
                  mulh       s11, s1, s9
                  c.lui      a0, 24
                  lui        zero, 195546
                  slt        t1, a1, a4
                  sll        t3, s7, a3
                  c.add      t1, a1
                  xor        t4, s3, t3
                  xori       a4, t0, 974
                  mulhsu     gp, a1, s1
                  ori        t5, t2, 999
                  c.mv       a1, s5
                  lui        zero, 195546
                  or         s0, a2, a0
                  c.srai     s0, 31
                  c.xor      a1, a2
                  c.sub      s1, a4
                  xor        t4, s3, t3
                  srl        a0, s2, a0
                  c.addi4spn a4, sp, 288
                  sltiu      s6, ra, 913
                  c.nop
                  slti       tp, t6, 301
                  sltu       t2, s1, t1
                  c.xor      a1, a2
                  rem        s0, a3, a2
                  divu       sp, ra, t0
                  slti       tp, t6, 301
                  c.addi4spn a4, sp, 288
                  andi       s8, t1, -26
                  srl        a0, s2, a0
                  sltu       t2, s1, t1
                  srai       s10, s1, 24
                  lui        zero, 195546
                  c.nop
                  c.addi     s1, 6
                  and        a1, t3, a6
                  lui        zero, 195546
                  mul        sp, s9, s11
                  and        a1, t3, a6
                  c.li       a7, 27
                  xor        t4, s3, t3
                  c.and      a0, s0
                  c.srai     s0, 31
                  c.lui      a0, 24
                  c.li       a7, 27
                  c.and      a0, s0
                  slti       tp, t6, 301
                  srli       s8, t6, 19
                  add        s7, s5, a6
                  c.nop
                  andi       s8, t1, -26
                  div        t3, t1, t5
                  mulhu      tp, s3, a4
                  c.srai     s0, 31
                  and        a1, t3, a6
                  c.xor      a1, a2
                  add        s7, s5, a6
                  remu       s5, s11, t1
                  slti       tp, t6, 301
                  slli       s11, gp, 14
                  nop
                  sltu       t2, s1, t1
                  c.addi4spn a4, sp, 288
                  c.addi16sp sp, 16
                  sll        t3, s7, a3
                  addi       a7, t2, -784
                  slt        t1, a1, a4
                  auipc      t6, 688967
                  srl        a0, s2, a0
                  c.slli     t4, 28
                  c.addi4spn a4, sp, 288
                  mulhsu     gp, a1, s1
                  slti       tp, t6, 301
                  auipc      t6, 688967
                  c.slli     t4, 28
                  mul        sp, s9, s11
                  sltu       t2, s1, t1
                  mulhu      tp, s3, a4
                  lui        zero, 195546
                  c.srli     a0, 25
                  c.srai     s0, 31
                  div        t3, t1, t5
                  sll        t3, s7, a3
                  c.and      a0, s0
                  rem        s0, a3, a2
                  c.srai     s0, 31
                  c.add      t1, a1
                  sltu       t2, s1, t1
                  c.lui      a0, 24
                  rem        s0, a3, a2
                  auipc      t6, 688967
                  c.srli     a0, 25
                  c.mv       a1, s5
                  sltu       t2, s1, t1
                  srai       s10, s1, 24
                  c.addi16sp sp, 16
                  remu       s5, s11, t1
                  slli       s11, gp, 14
                  nop
                  c.addi     s1, 6
                  mulh       s11, s1, s9
                  sra        s1, t3, s1
                  divu       sp, ra, t0
                  slli       s11, gp, 14
                  andi       s8, t1, -26
                  slt        t1, a1, a4
                  addi       a7, t2, -784
                  srli       s8, t6, 19
                  xori       a4, t0, 974
                  c.addi     s1, 6
                  xor        t4, s3, t3
                  srai       s10, s1, 24
                  slti       tp, t6, 301
                  mul        sp, s9, s11
                  mul        sp, s9, s11
                  sltu       t2, s1, t1
                  c.addi     s1, 6
                  sll        t3, s7, a3
                  add        s7, s5, a6
                  c.sub      s1, a4
                  c.nop
                  sltiu      s6, ra, 913
                  c.srai     s0, 31
                  div        t3, t1, t5
                  c.nop
                  div        t3, t1, t5
                  c.xor      a1, a2
                  slt        t1, a1, a4
                  c.srai     s0, 31
                  sll        t3, s7, a3
                  c.addi4spn a4, sp, 288
                  sltu       t2, s1, t1
                  sltiu      s6, ra, 913
                  remu       s5, s11, t1
                  c.addi16sp sp, 16
                  mulh       s11, s1, s9
                  slt        t1, a1, a4
                  rem        s0, a3, a2
                  slti       tp, t6, 301
                  c.mv       a1, s5
                  ori        t5, t2, 999
                  c.and      a0, s0
                  c.xor      a1, a2
                  sra        s1, t3, s1
                  c.mv       a1, s5
                  xor        t4, s3, t3
                  auipc      t6, 688967
                  remu       s5, s11, t1
                  mulhu      tp, s3, a4
                  sltiu      s6, ra, 913
                  ori        t5, t2, 999
                  c.xor      a1, a2
                  c.addi4spn a4, sp, 288
                  ori        t5, t2, 999
                  slti       tp, t6, 301
                  c.and      a0, s0
                  slt        t1, a1, a4
                  slti       tp, t6, 301
                  remu       s5, s11, t1
                  nop
                  sra        s1, t3, s1
                  c.mv       a1, s5
                  mulh       s11, s1, s9
                  c.nop
                  c.mv       a1, s5
                  c.mv       a1, s5
                  divu       sp, ra, t0
                  addi       a7, t2, -784
                  c.nop
                  and        a1, t3, a6
                  sra        s1, t3, s1
                  srl        a0, s2, a0
                  addi       a7, t2, -784
                  slli       s11, gp, 14
                  mul        sp, s9, s11
                  or         s0, a2, a0
                  xori       a4, t0, 974
                  c.li       a7, 27
                  c.andi     a5, -1
                  c.addi     s1, 6
                  rem        s0, a3, a2
                  c.addi4spn a4, sp, 288
                  lui        zero, 195546
                  c.srli     a0, 25
                  divu       sp, ra, t0
                  sltu       t2, s1, t1
                  and        a1, t3, a6
                  add        s7, s5, a6
                  c.nop
                  div        t3, t1, t5
                  xor        t4, s3, t3
                  mulhsu     gp, a1, s1
                  c.mv       a1, s5
                  add        s7, s5, a6
                  c.nop
                  div        t3, t1, t5
                  div        t3, t1, t5
                  c.srai     s0, 31
                  c.addi     s1, 6
                  xor        t4, s3, t3
                  mulh       s11, s1, s9
                  slti       tp, t6, 301
                  and        a1, t3, a6
                  andi       s8, t1, -26
                  addi       a7, t2, -784
                  nop
                  ori        t5, t2, 999
                  srai       s10, s1, 24
                  addi       a7, t2, -784
                  remu       s5, s11, t1
                  nop
                  ori        t5, t2, 999
                  xor        t4, s3, t3
                  div        t3, t1, t5
                  auipc      t6, 688967
                  c.srai     s0, 31
                  slli       s11, gp, 14
                  div        t3, t1, t5
                  c.and      a0, s0
                  c.addi16sp sp, 16
                  c.mv       a1, s5
                  c.add      t1, a1
                  c.srai     s0, 31
                  add        s7, s5, a6
                  srai       s10, s1, 24
                  c.mv       a1, s5
                  srai       s10, s1, 24
                  mulh       s11, s1, s9
                  c.andi     a5, -1
                  or         s0, a2, a0
                  sltiu      s6, ra, 913
                  nop
                  sub        s9, s6, s5
                  rem        s0, a3, a2
                  c.mv       a1, s5
                  srl        a0, s2, a0
                  slt        t1, a1, a4
                  mul        sp, s9, s11
                  c.srli     a0, 25
                  c.srli     a0, 25
                  c.andi     a5, -1
                  c.mv       a1, s5
                  nop
                  sll        t3, s7, a3
                  srai       s10, s1, 24
                  addi       a7, t2, -784
                  c.addi     s1, 6
                  c.slli     t4, 28
                  c.lui      a0, 24
                  slli       s11, gp, 14
                  c.or       a5, a1
                  mul        sp, s9, s11
                  mulhsu     gp, a1, s1
                  div        t3, t1, t5
                  c.addi16sp sp, 16
                  mulh       s11, s1, s9
                  add        s7, s5, a6
                  c.addi4spn a4, sp, 288
                  sltu       t2, s1, t1
                  srl        a0, s2, a0
                  sub        s9, s6, s5
                  c.addi     s1, 6
                  slli       s11, gp, 14
                  c.addi     s1, 6
                  sltiu      s6, ra, 913
                  slti       tp, t6, 301
                  c.xor      a1, a2
                  and        a1, t3, a6
                  slt        t1, a1, a4
                  mulhu      tp, s3, a4
                  c.and      a0, s0
                  mulhu      tp, s3, a4
                  slli       s11, gp, 14
                  xori       a4, t0, 974
                  c.sub      s1, a4
                  remu       s5, s11, t1
                  c.xor      a1, a2
                  mulhu      tp, s3, a4
                  slti       tp, t6, 301
                  lui        zero, 195546
                  c.nop
                  c.nop
                  c.addi16sp sp, 16
                  xor        t4, s3, t3
                  mulh       s11, s1, s9
                  srai       s10, s1, 24
                  c.nop
                  add        s7, s5, a6
                  c.nop
                  xor        t4, s3, t3
                  c.andi     a5, -1
                  slt        t1, a1, a4
                  c.srai     s0, 31
                  sra        s1, t3, s1
                  slli       s11, gp, 14
                  srl        a0, s2, a0
                  srli       s8, t6, 19
                  c.li       a7, 27
                  slti       tp, t6, 301
                  nop
                  rem        s0, a3, a2
                  mulhu      tp, s3, a4
                  xor        t4, s3, t3
                  c.sub      s1, a4
                  sll        t3, s7, a3
                  c.addi4spn a4, sp, 288
                  c.or       a5, a1
                  ori        t5, t2, 999
                  srl        a0, s2, a0
                  c.or       a5, a1
                  c.srai     s0, 31
                  sra        s1, t3, s1
                  c.addi     s1, 6
                  sltiu      s6, ra, 913
                  addi       a7, t2, -784
                  sub        s9, s6, s5
                  sltu       t2, s1, t1
                  sltu       t2, s1, t1
                  c.addi     s1, 6
                  mul        sp, s9, s11
                  c.nop
                  auipc      t6, 688967
                  c.lui      a0, 24
                  xor        t4, s3, t3
                  c.slli     t4, 28
                  c.and      a0, s0
                  c.srai     s0, 31
                  c.addi     s1, 6
                  c.or       a5, a1
                  slli       s11, gp, 14
                  mulh       s11, s1, s9
                  c.sub      s1, a4
                  srai       s10, s1, 24
                  sltu       t2, s1, t1
                  c.addi16sp sp, 16
                  srai       s10, s1, 24
                  sub        s9, s6, s5
                  and        a1, t3, a6
                  c.xor      a1, a2
                  c.add      t1, a1
                  mulhsu     gp, a1, s1
                  c.srai     s0, 31
                  mul        sp, s9, s11
                  or         s0, a2, a0
                  divu       sp, ra, t0
                  c.or       a5, a1
                  c.addi4spn a4, sp, 288
                  c.srli     a0, 25
                  c.addi16sp sp, 16
                  div        t3, t1, t5
                  add        s7, s5, a6
                  lui        zero, 195546
                  c.nop
                  c.addi     s1, 6
                  c.sub      s1, a4
                  c.srli     a0, 25
                  sra        s1, t3, s1
                  mul        sp, s9, s11
                  sltu       t2, s1, t1
                  sltu       t2, s1, t1
                  mulh       s11, s1, s9
                  c.and      a0, s0
                  c.or       a5, a1
                  mulh       s11, s1, s9
                  mul        sp, s9, s11
                  sra        s1, t3, s1
                  sub        s9, s6, s5
                  srl        a0, s2, a0
                  c.sub      s1, a4
                  lui        zero, 195546
                  add        s7, s5, a6
                  srli       s8, t6, 19
                  c.srli     a0, 25
                  c.nop
                  ori        t5, t2, 999
                  c.and      a0, s0
                  c.andi     a5, -1
                  c.and      a0, s0
                  c.andi     a5, -1
                  auipc      t6, 688967
                  c.add      t1, a1
                  c.mv       a1, s5
                  c.or       a5, a1
                  lui        zero, 195546
                  c.addi4spn a4, sp, 288
                  andi       s8, t1, -26
                  c.sub      s1, a4
                  c.lui      a0, 24
                  c.and      a0, s0
                  srl        a0, s2, a0
                  c.srai     s0, 31
                  xori       a4, t0, 974
                  addi       a7, t2, -784
                  addi       a7, t2, -784
                  c.andi     a5, -1
                  c.srai     s0, 31
                  c.slli     t4, 28
                  c.and      a0, s0
                  slt        t1, a1, a4
                  c.addi4spn a4, sp, 288
                  c.sub      s1, a4
                  add        s7, s5, a6
                  divu       sp, ra, t0
                  mulhsu     gp, a1, s1
                  xori       a4, t0, 974
                  c.xor      a1, a2
                  addi       a7, t2, -784
                  rem        s0, a3, a2
                  slt        t1, a1, a4
                  c.li       a7, 27
                  c.and      a0, s0
                  mulhsu     gp, a1, s1
                  ori        t5, t2, 999
                  xor        t4, s3, t3
                  div        t3, t1, t5
                  c.and      a0, s0
                  andi       s8, t1, -26
                  mul        sp, s9, s11
                  add        s7, s5, a6
                  or         s0, a2, a0
                  c.addi     s1, 6
                  mulh       s11, s1, s9
                  srai       s10, s1, 24
                  xori       a4, t0, 974
                  mulh       s11, s1, s9
                  c.andi     a5, -1
                  or         s0, a2, a0
                  or         s0, a2, a0
                  slli       s11, gp, 14
                  c.andi     a5, -1
                  mul        sp, s9, s11
                  xori       a4, t0, 974
                  div        t3, t1, t5
                  srli       s8, t6, 19
                  andi       s8, t1, -26
                  mulh       s11, s1, s9
                  sub        s9, s6, s5
                  divu       sp, ra, t0
                  sub        s9, s6, s5
                  remu       s5, s11, t1
                  c.lui      a0, 24
                  rem        s0, a3, a2
                  rem        s0, a3, a2
                  xor        t4, s3, t3
                  divu       sp, ra, t0
                  c.mv       a1, s5
                  lui        zero, 195546
                  srai       s10, s1, 24
                  and        a1, t3, a6
                  addi       a7, t2, -784
                  c.nop
                  mulhu      tp, s3, a4
                  sra        s1, t3, s1
                  c.xor      a1, a2
                  c.nop
                  c.xor      a1, a2
                  nop
                  mulhsu     gp, a1, s1
                  xori       a4, t0, 974
                  xori       a4, t0, 974
                  c.andi     a5, -1
                  nop
                  xor        t4, s3, t3
                  xor        t4, s3, t3
                  lui        zero, 195546
                  sll        t3, s7, a3
                  srai       s10, s1, 24
                  slli       s11, gp, 14
                  div        t3, t1, t5
                  and        a1, t3, a6
                  sub        s9, s6, s5
                  add        s7, s5, a6
                  slli       s11, gp, 14
                  c.li       a7, 27
                  lui        zero, 195546
                  c.slli     t4, 28
                  add        s7, s5, a6
                  c.slli     t4, 28
                  srl        a0, s2, a0
                  c.li       a7, 27
                  c.mv       a1, s5
                  c.nop
                  slt        t1, a1, a4
                  ori        t5, t2, 999
                  sltiu      s6, ra, 913
                  mulh       s11, s1, s9
                  addi       a7, t2, -784
                  srli       s8, t6, 19
                  c.li       a7, 27
                  mulhsu     gp, a1, s1
                  c.li       a7, 27
                  c.srli     a0, 25
                  srli       s8, t6, 19
                  sub        s9, s6, s5
                  c.addi16sp sp, 16
                  andi       s8, t1, -26
                  c.addi4spn a4, sp, 288
                  c.xor      a1, a2
                  c.srai     s0, 31
                  c.add      t1, a1
                  c.addi16sp sp, 16
                  c.sub      s1, a4
                  lui        zero, 195546
                  slt        t1, a1, a4
                  c.sub      s1, a4
                  c.andi     a5, -1
                  srl        a0, s2, a0
                  add        s7, s5, a6
                  xori       a4, t0, 974
                  sub        s9, s6, s5
                  slti       tp, t6, 301
                  andi       s8, t1, -26
                  addi       a7, t2, -784
                  srai       s10, s1, 24
                  sltiu      s6, ra, 913
                  c.sub      s1, a4
                  mulhsu     gp, a1, s1
                  mulhu      tp, s3, a4
                  c.nop
                  and        a1, t3, a6
                  slti       tp, t6, 301
                  nop
                  c.srai     s0, 31
                  c.andi     a5, -1
                  sltiu      s6, ra, 913
                  sltiu      s6, ra, 913
                  rem        s0, a3, a2
                  or         s0, a2, a0
                  addi       a7, t2, -784
                  xor        t4, s3, t3
                  and        a1, t3, a6
                  add        s7, s5, a6
                  slli       s11, gp, 14
                  auipc      t6, 688967
                  srai       s10, s1, 24
                  xor        t4, s3, t3
                  sra        s1, t3, s1
                  sltu       t2, s1, t1
                  sra        s1, t3, s1
                  c.xor      a1, a2
                  c.or       a5, a1
                  remu       s5, s11, t1
                  sub        s9, s6, s5
                  c.srai     s0, 31
                  c.andi     a5, -1
                  c.addi4spn a4, sp, 288
                  sub        s9, s6, s5
                  and        a1, t3, a6
                  slt        t1, a1, a4
                  sra        s1, t3, s1
                  xor        t4, s3, t3
                  c.lui      a0, 24
                  nop
                  div        t3, t1, t5
                  andi       s8, t1, -26
                  c.mv       a1, s5
                  c.srli     a0, 25
                  c.li       a7, 27
                  sll        t3, s7, a3
                  ori        t5, t2, 999
                  srai       s10, s1, 24
                  srai       s10, s1, 24
                  c.nop
                  mulh       s11, s1, s9
                  c.srli     a0, 25
                  c.andi     a5, -1
                  srli       s8, t6, 19
                  auipc      t6, 688967
                  rem        s0, a3, a2
                  c.addi16sp sp, 16
                  srai       s10, s1, 24
                  mul        sp, s9, s11
                  c.and      a0, s0
                  c.lui      a0, 24
                  c.or       a5, a1
                  remu       s5, s11, t1
                  div        t3, t1, t5
                  c.add      t1, a1
                  slt        t1, a1, a4
                  c.add      t1, a1
                  c.and      a0, s0
                  or         s0, a2, a0
                  srli       s8, t6, 19
                  lui        zero, 195546
                  sll        t3, s7, a3
                  remu       s5, s11, t1
                  c.lui      a0, 24
                  mul        sp, s9, s11
                  slli       s11, gp, 14
                  ori        t5, t2, 999
                  mul        sp, s9, s11
                  slti       tp, t6, 301
                  mulhsu     gp, a1, s1
                  remu       s5, s11, t1
                  c.srai     s0, 31
                  ori        t5, t2, 999
                  sltiu      s6, ra, 913
                  sltu       t2, s1, t1
                  sltiu      s6, ra, 913
                  slli       s11, gp, 14
                  c.and      a0, s0
                  c.srli     a0, 25
                  slti       tp, t6, 301
                  sra        s1, t3, s1
                  mulh       s11, s1, s9
                  c.or       a5, a1
                  nop
                  mulhu      tp, s3, a4
                  c.lui      a0, 24
                  addi       a7, t2, -784
                  c.li       a7, 27
                  srai       s10, s1, 24
                  mulhu      tp, s3, a4
                  rem        s0, a3, a2
                  c.li       a7, 27
                  c.add      t1, a1
                  c.or       a5, a1
                  div        t3, t1, t5
                  sltiu      s6, ra, 913
                  lui        zero, 195546
                  c.srai     s0, 31
                  add        s7, s5, a6
                  andi       s8, t1, -26
                  xori       a4, t0, 974
                  c.add      t1, a1
                  c.sub      s1, a4
                  c.sub      s1, a4
                  sltu       t2, s1, t1
                  c.and      a0, s0
                  c.addi     s1, 6
                  div        t3, t1, t5
                  xor        t4, s3, t3
                  nop
                  andi       s8, t1, -26
                  and        a1, t3, a6
                  c.slli     t4, 28
                  mulhsu     gp, a1, s1
                  remu       s5, s11, t1
                  mulhsu     gp, a1, s1
                  slli       s11, gp, 14
                  xor        t4, s3, t3
                  srai       s10, s1, 24
                  c.xor      a1, a2
                  ori        t5, t2, 999
                  c.addi     s1, 6
                  c.nop
                  c.slli     t4, 28
                  mulhsu     gp, a1, s1
                  c.nop
                  c.mv       a1, s5
                  sll        t3, s7, a3
                  xor        t4, s3, t3
                  nop
                  c.mv       a1, s5
                  slli       s11, gp, 14
                  xori       a4, t0, 974
                  andi       s8, t1, -26
                  xor        t4, s3, t3
                  c.slli     t4, 28
                  slt        t1, a1, a4
                  slt        t1, a1, a4
                  mulh       s11, s1, s9
                  c.add      t1, a1
                  c.lui      a0, 24
                  mulh       s11, s1, s9
                  c.addi     s1, 6
                  c.nop
                  srli       s8, t6, 19
                  add        s7, s5, a6
                  div        t3, t1, t5
                  sub        s9, s6, s5
                  nop
                  slti       tp, t6, 301
                  c.add      t1, a1
                  c.mv       a1, s5
                  c.andi     a5, -1
                  remu       s5, s11, t1
                  c.addi16sp sp, 16
                  sltiu      s6, ra, 913
                  auipc      t6, 688967
                  c.addi     s1, 6
                  c.mv       a1, s5
                  sltiu      s6, ra, 913
                  c.add      t1, a1
                  c.add      t1, a1
                  divu       sp, ra, t0
                  sra        s1, t3, s1
                  addi       a7, t2, -784
                  c.sub      s1, a4
                  c.nop
                  c.mv       a1, s5
                  c.srli     a0, 25
                  sra        s1, t3, s1
                  c.add      t1, a1
                  srli       s8, t6, 19
                  lui        zero, 195546
                  c.srli     a0, 25
                  mulh       s11, s1, s9
                  rem        s0, a3, a2
                  andi       s8, t1, -26
                  c.li       a7, 27
                  auipc      t6, 688967
                  xori       a4, t0, 974
                  slti       tp, t6, 301
                  c.li       a7, 27
                  srl        a0, s2, a0
                  c.mv       a1, s5
                  andi       s8, t1, -26
                  auipc      t6, 688967
                  auipc      t6, 688967
                  slti       tp, t6, 301
                  sltu       t2, s1, t1
                  srli       s8, t6, 19
                  sltiu      s6, ra, 913
                  srli       s8, t6, 19
                  c.xor      a1, a2
                  remu       s5, s11, t1
                  sltiu      s6, ra, 913
                  c.or       a5, a1
                  c.addi4spn a4, sp, 288
                  sub        s9, s6, s5
                  xor        t4, s3, t3
                  c.mv       a1, s5
                  and        a1, t3, a6
                  sltu       t2, s1, t1
                  c.slli     t4, 28
                  c.or       a5, a1
                  c.add      t1, a1
                  mul        sp, s9, s11
                  c.li       a7, 27
                  addi       a7, t2, -784
                  c.and      a0, s0
                  add        s7, s5, a6
                  add        s7, s5, a6
                  add        s7, s5, a6
                  srl        a0, s2, a0
                  sltu       t2, s1, t1
                  sltiu      s6, ra, 913
                  sltiu      s6, ra, 913
                  mulhu      tp, s3, a4
                  c.slli     t4, 28
                  c.sub      s1, a4
                  sra        s1, t3, s1
                  ori        t5, t2, 999
                  or         s0, a2, a0
                  auipc      t6, 688967
                  add        s7, s5, a6
                  c.nop
                  mulhu      tp, s3, a4
                  add        s7, s5, a6
                  c.add      t1, a1
                  sub        s9, s6, s5
                  c.li       a7, 27
                  slli       s11, gp, 14
                  srai       s10, s1, 24
                  c.addi     s1, 6
                  xori       a4, t0, 974
                  add        s7, s5, a6
                  c.nop
                  xor        t4, s3, t3
                  c.addi16sp sp, 16
                  xor        t4, s3, t3
                  srl        a0, s2, a0
                  mul        sp, s9, s11
                  sltiu      s6, ra, 913
                  srai       s10, s1, 24
                  c.and      a0, s0
                  andi       s8, t1, -26
                  c.mv       a1, s5
                  c.addi16sp sp, 16
                  mulhsu     gp, a1, s1
                  c.sub      s1, a4
                  auipc      t6, 688967
                  c.srai     s0, 31
                  c.or       a5, a1
                  srai       s10, s1, 24
                  xori       a4, t0, 974
                  c.li       a7, 27
                  divu       sp, ra, t0
                  srl        a0, s2, a0
                  srli       s8, t6, 19
                  c.srai     s0, 31
                  nop
                  auipc      t6, 688967
                  slt        t1, a1, a4
                  c.and      a0, s0
                  c.add      t1, a1
                  mulhu      tp, s3, a4
                  nop
                  c.srli     a0, 25
                  c.srli     a0, 25
                  c.addi16sp sp, 16
                  sltu       t2, s1, t1
                  c.addi16sp sp, 16
                  slti       tp, t6, 301
                  auipc      t6, 688967
                  sll        t3, s7, a3
                  srl        a0, s2, a0
                  c.li       a7, 27
                  c.sub      s1, a4
                  c.srli     a0, 25
                  c.xor      a1, a2
                  c.srli     a0, 25
                  c.li       a7, 27
                  c.andi     a5, -1
                  or         s0, a2, a0
                  mulhu      tp, s3, a4
                  divu       sp, ra, t0
                  srai       s10, s1, 24
                  c.slli     t4, 28
                  auipc      t6, 688967
                  rem        s0, a3, a2
                  sll        t3, s7, a3
                  slti       tp, t6, 301
                  remu       s5, s11, t1
                  c.addi     s1, 6
                  add        s7, s5, a6
                  slti       tp, t6, 301
                  slt        t1, a1, a4
                  mulhu      tp, s3, a4
                  mulh       s11, s1, s9
                  sra        s1, t3, s1
                  c.addi16sp sp, 16
                  xori       a4, t0, 974
                  mulh       s11, s1, s9
                  c.and      a0, s0
                  andi       s8, t1, -26
                  c.lui      a0, 24
                  c.or       a5, a1
                  slt        t1, a1, a4
                  c.andi     a5, -1
                  and        a1, t3, a6
                  c.lui      a0, 24
                  slli       s11, gp, 14
                  and        a1, t3, a6
                  c.addi     s1, 6
                  slti       tp, t6, 301
                  auipc      t6, 688967
                  nop
                  xori       a4, t0, 974
                  c.li       a7, 27
                  c.addi16sp sp, 16
                  c.slli     t4, 28
                  slli       s11, gp, 14
                  or         s0, a2, a0
                  c.srai     s0, 31
                  sub        s9, s6, s5
                  mulhu      tp, s3, a4
                  xori       a4, t0, 974
                  slti       tp, t6, 301
                  xori       a4, t0, 974
                  addi       a7, t2, -784
                  c.and      a0, s0
                  c.xor      a1, a2
                  c.sub      s1, a4
                  slt        t1, a1, a4
                  mulh       s11, s1, s9
                  slti       tp, t6, 301
                  slli       s11, gp, 14
                  c.sub      s1, a4
                  xori       a4, t0, 974
                  rem        s0, a3, a2
                  sub        s9, s6, s5
                  c.nop
                  srl        a0, s2, a0
                  c.xor      a1, a2
                  c.and      a0, s0
                  c.mv       a1, s5
                  andi       s8, t1, -26
                  c.srli     a0, 25
                  c.addi     s1, 6
                  div        t3, t1, t5
                  lui        zero, 195546
                  sub        s9, s6, s5
                  remu       s5, s11, t1
                  divu       sp, ra, t0
                  c.sub      s1, a4
                  mulhsu     gp, a1, s1
                  sub        s9, s6, s5
                  ori        t5, t2, 999
                  auipc      t6, 688967
                  andi       s8, t1, -26
                  auipc      t6, 688967
                  sra        s1, t3, s1
                  c.addi4spn a4, sp, 288
                  remu       s5, s11, t1
                  c.addi16sp sp, 16
                  srai       s10, s1, 24
                  sll        t3, s7, a3
                  andi       s8, t1, -26
                  c.slli     t4, 28
                  c.addi     s1, 6
                  and        a1, t3, a6
                  rem        s0, a3, a2
                  and        a1, t3, a6
                  slt        t1, a1, a4
                  mul        sp, s9, s11
                  ori        t5, t2, 999
                  sll        t3, s7, a3
                  andi       s8, t1, -26
                  sub        s9, s6, s5
                  xori       a4, t0, 974
                  andi       s8, t1, -26
                  slti       tp, t6, 301
                  c.li       a7, 27
                  c.nop
                  sll        t3, s7, a3
                  slti       tp, t6, 301
                  srai       s10, s1, 24
                  sltu       t2, s1, t1
                  sub        s9, s6, s5
                  divu       sp, ra, t0
                  c.addi16sp sp, 16
                  srai       s10, s1, 24
                  xor        t4, s3, t3
                  c.lui      a0, 24
                  sll        t3, s7, a3
                  div        t3, t1, t5
                  c.li       a7, 27
                  c.or       a5, a1
                  rem        s0, a3, a2
                  c.add      t1, a1
                  lui        zero, 195546
                  srl        a0, s2, a0
                  sltiu      s6, ra, 913
                  srl        a0, s2, a0
                  xori       a4, t0, 974
                  slli       s11, gp, 14
                  slli       s11, gp, 14
                  ori        t5, t2, 999
                  sltu       t2, s1, t1
                  c.slli     t4, 28
                  or         s0, a2, a0
                  c.slli     t4, 28
                  c.lui      a0, 24
                  srai       s10, s1, 24
                  xori       a4, t0, 974
                  remu       s5, s11, t1
                  mulhsu     gp, a1, s1
                  mulhu      tp, s3, a4
                  and        a1, t3, a6
                  srli       s8, t6, 19
                  srl        a0, s2, a0
                  c.slli     t4, 28
                  srli       s8, t6, 19
                  xori       a4, t0, 974
                  mulh       s11, s1, s9
                  c.srai     s0, 31
                  srli       s8, t6, 19
                  mul        sp, s9, s11
                  c.lui      a0, 24
                  andi       s8, t1, -26
                  xori       a4, t0, 974
                  sltu       t2, s1, t1
                  rem        s0, a3, a2
                  divu       sp, ra, t0
                  c.sub      s1, a4
                  mulh       s11, s1, s9
                  c.and      a0, s0
                  mul        sp, s9, s11
                  c.lui      a0, 24
                  addi       a7, t2, -784
                  or         s0, a2, a0
                  mulh       s11, s1, s9
                  sltu       t2, s1, t1
                  slt        t1, a1, a4
                  auipc      t6, 688967
                  c.and      a0, s0
                  mulh       s11, s1, s9
                  c.li       a7, 27
                  auipc      t6, 688967
                  srai       s10, s1, 24
                  sra        s1, t3, s1
                  c.slli     t4, 28
                  addi       a7, t2, -784
                  c.xor      a1, a2
                  and        a1, t3, a6
                  and        a1, t3, a6
                  c.andi     a5, -1
                  c.addi     s1, 6
                  c.add      t1, a1
                  c.addi16sp sp, 16
                  sll        t3, s7, a3
                  srl        a0, s2, a0
                  srl        a0, s2, a0
                  xor        t4, s3, t3
                  c.and      a0, s0
                  sub        s9, s6, s5
                  c.mv       a1, s5
                  c.li       a7, 27
                  xor        t4, s3, t3
                  c.slli     t4, 28
                  c.srli     a0, 25
                  xor        t4, s3, t3
                  add        s7, s5, a6
                  c.srli     a0, 25
                  mulhu      tp, s3, a4
                  c.sub      s1, a4
                  addi       a7, t2, -784
                  slti       tp, t6, 301
                  mulh       s11, s1, s9
                  c.xor      a1, a2
                  slt        t1, a1, a4
                  c.addi4spn a4, sp, 288
                  sltu       t2, s1, t1
                  andi       s8, t1, -26
                  and        a1, t3, a6
                  c.or       a5, a1
                  c.srai     s0, 31
                  sub        s9, s6, s5
                  c.srai     s0, 31
                  c.li       a7, 27
                  c.addi4spn a4, sp, 288
                  c.sub      s1, a4
                  c.srli     a0, 25
                  remu       s5, s11, t1
                  srli       s8, t6, 19
                  c.nop
                  srl        a0, s2, a0
                  divu       sp, ra, t0
                  sra        s1, t3, s1
                  c.addi     s1, 6
                  add        s7, s5, a6
                  remu       s5, s11, t1
                  or         s0, a2, a0
                  sub        s9, s6, s5
                  c.andi     a5, -1
                  c.lui      a0, 24
                  c.sub      s1, a4
                  c.addi4spn a4, sp, 288
                  c.andi     a5, -1
                  div        t3, t1, t5
                  c.add      t1, a1
                  slli       s11, gp, 14
                  c.xor      a1, a2
                  slli       s11, gp, 14
                  divu       sp, ra, t0
                  add        s7, s5, a6
                  c.xor      a1, a2
                  c.andi     a5, -1
                  c.xor      a1, a2
                  rem        s0, a3, a2
                  srli       s8, t6, 19
                  sltiu      s6, ra, 913
                  xor        t4, s3, t3
                  divu       sp, ra, t0
                  auipc      t6, 688967
                  or         s0, a2, a0
                  auipc      t6, 688967
                  slti       tp, t6, 301
                  slti       tp, t6, 301
                  or         s0, a2, a0
                  slti       tp, t6, 301
                  c.mv       a1, s5
                  c.slli     t4, 28
                  slti       tp, t6, 301
                  c.add      t1, a1
                  div        t3, t1, t5
                  c.addi4spn a4, sp, 288
                  c.srli     a0, 25
                  c.li       a7, 27
                  c.add      t1, a1
                  srl        a0, s2, a0
                  c.sub      s1, a4
                  c.lui      a0, 24
                  nop
                  addi       a7, t2, -784
                  ori        t5, t2, 999
                  c.li       a7, 27
                  slli       s11, gp, 14
                  c.addi4spn a4, sp, 288
                  add        s7, s5, a6
                  c.addi16sp sp, 16
                  ori        t5, t2, 999
                  srai       s10, s1, 24
                  c.add      t1, a1
                  addi       a7, t2, -784
                  addi       a7, t2, -784
                  c.nop
                  c.add      t1, a1
                  c.addi16sp sp, 16
                  mul        sp, s9, s11
                  slti       tp, t6, 301
                  srl        a0, s2, a0
                  xor        t4, s3, t3
                  rem        s0, a3, a2
                  mulhu      tp, s3, a4
                  rem        s0, a3, a2
                  addi       a7, t2, -784
                  xori       a4, t0, 974
                  div        t3, t1, t5
                  xor        t4, s3, t3
                  srai       s10, s1, 24
                  sltu       t2, s1, t1
                  c.andi     a5, -1
                  c.andi     a5, -1
                  srl        a0, s2, a0
                  li         t0, 0xffffffff #start riscv_int_numeric_corner_stream_16
                  li         s0, 0x0
                  li         tp, 0xffffffff
                  li         s6, 0x80000000
                  li         s3, 0x80000000
                  li         t4, 0xffffffff
                  li         a6, 0x80000000
                  li         sp, 0xa273e7c6
                  li         a0, 0x35e4306a
                  li         t6, 0xffffffff
                  mulh       s3, s3, t4
                  remu       t4, t0, s0
                  nop
                  remu       t4, t0, s0
                  auipc      t6, 688967
                  div        s3, t6, a0
                  mulh       s3, s3, t4
                  remu       t4, t0, s0
                  mulh       s3, s3, t4
                  div        s3, t6, a0
                  sub        t0, a6, tp
                  mul        tp, t4, s6
                  sub        t0, a6, tp
                  mulhu      sp, s3, t0
                  add        t0, a0, a6
                  remu       t4, t0, s0
                  auipc      t6, 688967
                  divu       a6, a0, t4
                  auipc      t6, 688967
                  lui        tp, 195546
                  add        t0, a0, a6
                  div        s3, t6, a0
                  sub        t0, a6, tp
                  remu       t4, t0, s0
                  mul        tp, t4, s6
                  rem        s0, t6, s0
                  add        t0, a0, a6 #end riscv_int_numeric_corner_stream_16
                  srai       s10, s1, 24
                  xori       a4, t0, 974
                  c.andi     a5, -1
                  c.mv       a1, s5
                  sltiu      s6, ra, 913
                  c.srli     a0, 25
                  auipc      t6, 688967
                  slti       tp, t6, 301
                  srli       s8, t6, 19
                  srl        a0, s2, a0
                  c.or       a5, a1
                  c.add      t1, a1
                  c.xor      a1, a2
                  mulhu      tp, s3, a4
                  remu       s5, s11, t1
                  div        t3, t1, t5
                  sltu       t2, s1, t1
                  slti       tp, t6, 301
                  c.addi16sp sp, 16
                  c.addi     s1, 6
                  xor        t4, s3, t3
                  mulh       s11, s1, s9
                  slt        t1, a1, a4
                  sltiu      s6, ra, 913
                  addi       a7, t2, -784
                  c.mv       a1, s5
                  and        a1, t3, a6
                  sltiu      s6, ra, 913
                  c.nop
                  and        a1, t3, a6
                  c.addi     s1, 6
                  sra        s1, t3, s1
                  c.addi4spn a4, sp, 288
                  slli       s11, gp, 14
                  nop
                  mulhu      tp, s3, a4
                  c.srli     a0, 25
                  c.addi16sp sp, 16
                  c.srai     s0, 31
                  sltiu      s6, ra, 913
                  xori       a4, t0, 974
                  c.add      t1, a1
                  sll        t3, s7, a3
                  and        a1, t3, a6
                  c.andi     a5, -1
                  c.li       a7, 27
                  remu       s5, s11, t1
                  or         s0, a2, a0
                  or         s0, a2, a0
                  sltu       t2, s1, t1
                  c.sub      s1, a4
                  c.nop
                  auipc      t6, 688967
                  add        s7, s5, a6
                  lui        zero, 195546
                  c.andi     a5, -1
                  srli       s8, t6, 19
                  mulhsu     gp, a1, s1
                  mul        sp, s9, s11
                  divu       sp, ra, t0
                  slli       s11, gp, 14
                  mulhsu     gp, a1, s1
                  mulhu      tp, s3, a4
                  c.sub      s1, a4
                  sltiu      s6, ra, 913
                  sll        t3, s7, a3
                  sub        s9, s6, s5
                  c.slli     t4, 28
                  sub        s9, s6, s5
                  c.slli     t4, 28
                  c.sub      s1, a4
                  rem        s0, a3, a2
                  slli       s11, gp, 14
                  c.lui      a0, 24
                  mul        sp, s9, s11
                  c.and      a0, s0
                  and        a1, t3, a6
                  rem        s0, a3, a2
                  and        a1, t3, a6
                  sltiu      s6, ra, 913
                  c.srli     a0, 25
                  sub        s9, s6, s5
                  sltiu      s6, ra, 913
                  mulh       s11, s1, s9
                  c.addi4spn a4, sp, 288
                  xor        t4, s3, t3
                  srli       s8, t6, 19
                  div        t3, t1, t5
                  sra        s1, t3, s1
                  mulh       s11, s1, s9
                  c.addi     s1, 6
                  srli       s8, t6, 19
                  xor        t4, s3, t3
                  auipc      t6, 688967
                  srl        a0, s2, a0
                  slti       tp, t6, 301
                  c.andi     a5, -1
                  sltiu      s6, ra, 913
                  slli       s11, gp, 14
                  divu       sp, ra, t0
                  c.addi4spn a4, sp, 288
                  c.srli     a0, 25
                  xor        t4, s3, t3
                  srai       s10, s1, 24
                  c.addi4spn a4, sp, 288
                  rem        s0, a3, a2
                  add        s7, s5, a6
                  c.li       a7, 27
                  c.xor      a1, a2
                  nop
                  mulh       s11, s1, s9
                  c.add      t1, a1
                  c.addi     s1, 6
                  add        s7, s5, a6
                  srl        a0, s2, a0
                  sltiu      s6, ra, 913
                  slli       s11, gp, 14
                  c.andi     a5, -1
                  auipc      t6, 688967
                  c.slli     t4, 28
                  lui        zero, 195546
                  c.andi     a5, -1
                  sltu       t2, s1, t1
                  c.mv       a1, s5
                  c.add      t1, a1
                  divu       sp, ra, t0
                  c.nop
                  c.add      t1, a1
                  andi       s8, t1, -26
                  c.srli     a0, 25
                  slt        t1, a1, a4
                  slli       s11, gp, 14
                  divu       sp, ra, t0
                  mul        sp, s9, s11
                  or         s0, a2, a0
                  c.nop
                  mulh       s11, s1, s9
                  sll        t3, s7, a3
                  sltiu      s6, ra, 913
                  c.slli     t4, 28
                  c.srli     a0, 25
                  sltiu      s6, ra, 913
                  slt        t1, a1, a4
                  c.add      t1, a1
                  c.add      t1, a1
                  srl        a0, s2, a0
                  remu       s5, s11, t1
                  slti       tp, t6, 301
                  mulhsu     gp, a1, s1
                  c.li       a7, 27
                  c.mv       a1, s5
                  c.addi4spn a4, sp, 288
                  sra        s1, t3, s1
                  c.lui      a0, 24
                  sub        s9, s6, s5
                  sll        t3, s7, a3
                  c.addi4spn a4, sp, 288
                  srli       s8, t6, 19
                  ori        t5, t2, 999
                  slli       s11, gp, 14
                  c.andi     a5, -1
                  c.addi16sp sp, 16
                  xori       a4, t0, 974
                  mulhu      tp, s3, a4
                  c.addi     s1, 6
                  ori        t5, t2, 999
                  rem        s0, a3, a2
                  xor        t4, s3, t3
                  addi       a7, t2, -784
                  sll        t3, s7, a3
                  div        t3, t1, t5
                  addi       a7, t2, -784
                  c.srli     a0, 25
                  c.nop
                  add        s7, s5, a6
                  sra        s1, t3, s1
                  c.add      t1, a1
                  c.nop
                  c.addi16sp sp, 16
                  xor        t4, s3, t3
                  slti       tp, t6, 301
                  c.or       a5, a1
                  c.lui      a0, 24
                  ori        t5, t2, 999
                  srli       s8, t6, 19
                  remu       s5, s11, t1
                  c.addi4spn a4, sp, 288
                  srl        a0, s2, a0
                  c.mv       a1, s5
                  c.or       a5, a1
                  c.slli     t4, 28
                  c.add      t1, a1
                  srl        a0, s2, a0
                  andi       s8, t1, -26
                  remu       s5, s11, t1
                  mulh       s11, s1, s9
                  sltu       t2, s1, t1
                  nop
                  div        t3, t1, t5
                  mul        sp, s9, s11
                  c.lui      a0, 24
                  xor        t4, s3, t3
                  c.li       a7, 27
                  srai       s10, s1, 24
                  srl        a0, s2, a0
                  c.srai     s0, 31
                  nop
                  or         s0, a2, a0
                  mulhu      tp, s3, a4
                  sra        s1, t3, s1
                  andi       s8, t1, -26
                  mulh       s11, s1, s9
                  c.nop
                  div        t3, t1, t5
                  c.lui      a0, 24
                  c.addi     s1, 6
                  c.slli     t4, 28
                  c.addi16sp sp, 16
                  sra        s1, t3, s1
                  c.slli     t4, 28
                  xori       a4, t0, 974
                  c.addi     s1, 6
                  c.or       a5, a1
                  mulhu      tp, s3, a4
                  divu       sp, ra, t0
                  c.andi     a5, -1
                  c.sub      s1, a4
                  mul        sp, s9, s11
                  slli       s11, gp, 14
                  xor        t4, s3, t3
                  srl        a0, s2, a0
                  c.slli     t4, 28
                  mulh       s11, s1, s9
                  div        t3, t1, t5
                  auipc      t6, 688967
                  slt        t1, a1, a4
                  rem        s0, a3, a2
                  c.sub      s1, a4
                  rem        s0, a3, a2
                  sltu       t2, s1, t1
                  c.nop
                  sltu       t2, s1, t1
                  c.xor      a1, a2
                  andi       s8, t1, -26
                  c.xor      a1, a2
                  c.addi16sp sp, 16
                  c.mv       a1, s5
                  sltu       t2, s1, t1
                  c.or       a5, a1
                  c.addi16sp sp, 16
                  sll        t3, s7, a3
                  addi       a7, t2, -784
                  sltiu      s6, ra, 913
                  xori       a4, t0, 974
                  c.andi     a5, -1
                  c.addi16sp sp, 16
                  auipc      t6, 688967
                  c.addi16sp sp, 16
                  c.srli     a0, 25
                  mulhsu     gp, a1, s1
                  slt        t1, a1, a4
                  sra        s1, t3, s1
                  li         a5, 0x8e524495 #start riscv_int_numeric_corner_stream_31
                  li         t1, 0x5dd7b636
                  li         s5, 0x0
                  li         t0, 0xa0f522bd
                  li         a4, 0xd3dab263
                  li         t5, 0x80000000
                  li         a6, 0x0
                  li         tp, 0xffffffff
                  li         s8, 0xad0127b4
                  li         a0, 0x80000000
                  add        t0, a6, s8
                  mulh       t5, s5, s5
                  rem        a5, t0, a0
                  divu       t0, a0, s5
                  mulhsu     a5, tp, a6
                  nop
                  nop
                  mulhsu     a5, tp, a6
                  lui        tp, 195546
                  addi       a6, s5, 999
                  lui        tp, 195546
                  sub        a0, a6, t1
                  add        t0, a6, s8
                  sub        a0, a6, t1
                  add        t0, a6, s8 #end riscv_int_numeric_corner_stream_31
                  and        a1, t3, a6
                  srl        a0, s2, a0
                  addi       a7, t2, -784
                  c.lui      a0, 24
                  c.li       a7, 27
                  c.addi     s1, 6
                  slli       s11, gp, 14
                  andi       s8, t1, -26
                  c.addi16sp sp, 16
                  nop
                  mulh       s11, s1, s9
                  andi       s8, t1, -26
                  sub        s9, s6, s5
                  srai       s10, s1, 24
                  auipc      t6, 688967
                  c.addi4spn a4, sp, 288
                  sll        t3, s7, a3
                  sltu       t2, s1, t1
                  c.srai     s0, 31
                  auipc      t6, 688967
                  c.nop
                  auipc      t6, 688967
                  sll        t3, s7, a3
                  slli       s11, gp, 14
                  andi       s8, t1, -26
                  c.addi4spn a4, sp, 288
                  sra        s1, t3, s1
                  mulh       s11, s1, s9
                  c.addi16sp sp, 16
                  addi       a7, t2, -784
                  slli       s11, gp, 14
                  c.mv       a1, s5
                  c.lui      a0, 24
                  mul        sp, s9, s11
                  lui        zero, 195546
                  add        s7, s5, a6
                  c.or       a5, a1
                  c.lui      a0, 24
                  c.li       a7, 27
                  li         t4, 0xffffffff #start riscv_int_numeric_corner_stream_0
                  li         s3, 0x0
                  li         tp, 0x0
                  li         a1, 0x0
                  li         t1, 0x0
                  li         s10, 0x56c23892
                  li         s8, 0xffffffff
                  li         a5, 0x0
                  li         s7, 0x0
                  li         s6, 0xffffffff
                  mulh       s7, s7, t4
                  addi       t1, s6, 999
                  sub        t1, s8, t1
                  lui        tp, 195546
                  rem        s8, a5, a1
                  nop
                  add        t4, s10, s8
                  nop
                  add        t4, s10, s8
                  div        s3, s10, t1
                  mul        s3, s7, s8
                  auipc      t4, 688967
                  lui        tp, 195546
                  nop
                  nop #end riscv_int_numeric_corner_stream_0
                  slli       s11, gp, 14
                  c.or       a5, a1
                  remu       s5, s11, t1
                  and        a1, t3, a6
                  div        t3, t1, t5
                  mulh       s11, s1, s9
                  c.lui      a0, 24
                  and        a1, t3, a6
                  srli       s8, t6, 19
                  c.srli     a0, 25
                  nop
                  sub        s9, s6, s5
                  c.andi     a5, -1
                  xori       a4, t0, 974
                  lui        zero, 195546
                  c.andi     a5, -1
                  c.andi     a5, -1
                  c.addi     s1, 6
                  xori       a4, t0, 974
                  c.addi16sp sp, 16
                  c.srai     s0, 31
                  c.andi     a5, -1
                  c.li       a7, 27
                  auipc      t6, 688967
                  mul        sp, s9, s11
                  c.and      a0, s0
                  srai       s10, s1, 24
                  or         s0, a2, a0
                  c.addi16sp sp, 16
                  c.li       a7, 27
                  c.addi16sp sp, 16
                  slt        t1, a1, a4
                  c.srai     s0, 31
                  c.lui      a0, 24
                  rem        s0, a3, a2
                  c.srli     a0, 25
                  c.addi4spn a4, sp, 288
                  rem        s0, a3, a2
                  c.slli     t4, 28
                  xor        t4, s3, t3
                  mulhsu     gp, a1, s1
                  slli       s11, gp, 14
                  c.xor      a1, a2
                  div        t3, t1, t5
                  andi       s8, t1, -26
                  rem        s0, a3, a2
                  nop
                  div        t3, t1, t5
                  c.nop
                  mulhu      tp, s3, a4
                  c.slli     t4, 28
                  c.srai     s0, 31
                  c.and      a0, s0
                  srai       s10, s1, 24
                  xori       a4, t0, 974
                  c.andi     a5, -1
                  and        a1, t3, a6
                  c.slli     t4, 28
                  lui        zero, 195546
                  auipc      t6, 688967
                  c.srai     s0, 31
                  srai       s10, s1, 24
                  xori       a4, t0, 974
                  slli       s11, gp, 14
                  auipc      t6, 688967
                  mulh       s11, s1, s9
                  mul        sp, s9, s11
                  c.or       a5, a1
                  slt        t1, a1, a4
                  slli       s11, gp, 14
                  c.add      t1, a1
                  srl        a0, s2, a0
                  slti       tp, t6, 301
                  ori        t5, t2, 999
                  rem        s0, a3, a2
                  mulhsu     gp, a1, s1
                  c.srli     a0, 25
                  mul        sp, s9, s11
                  c.srli     a0, 25
                  c.slli     t4, 28
                  c.srai     s0, 31
                  c.srli     a0, 25
                  c.srai     s0, 31
                  slt        t1, a1, a4
                  c.srai     s0, 31
                  ori        t5, t2, 999
                  c.xor      a1, a2
                  c.xor      a1, a2
                  c.xor      a1, a2
                  auipc      t6, 688967
                  c.add      t1, a1
                  c.or       a5, a1
                  slti       tp, t6, 301
                  mul        sp, s9, s11
                  c.addi     s1, 6
                  nop
                  mulhu      tp, s3, a4
                  xor        t4, s3, t3
                  srl        a0, s2, a0
                  c.srai     s0, 31
                  c.mv       a1, s5
                  addi       a7, t2, -784
                  c.sub      s1, a4
                  slti       tp, t6, 301
                  sra        s1, t3, s1
                  c.sub      s1, a4
                  sltu       t2, s1, t1
                  div        t3, t1, t5
                  mulh       s11, s1, s9
                  add        s7, s5, a6
                  slti       tp, t6, 301
                  c.addi4spn a4, sp, 288
                  srl        a0, s2, a0
                  mul        sp, s9, s11
                  c.xor      a1, a2
                  c.li       a7, 27
                  c.mv       a1, s5
                  sltiu      s6, ra, 913
                  sll        t3, s7, a3
                  xori       a4, t0, 974
                  sra        s1, t3, s1
                  xori       a4, t0, 974
                  mulhu      tp, s3, a4
                  nop
                  c.add      t1, a1
                  c.sub      s1, a4
                  div        t3, t1, t5
                  ori        t5, t2, 999
                  andi       s8, t1, -26
                  c.and      a0, s0
                  c.addi     s1, 6
                  sll        t3, s7, a3
                  div        t3, t1, t5
                  c.xor      a1, a2
                  srli       s8, t6, 19
                  xor        t4, s3, t3
                  sltiu      s6, ra, 913
                  addi       a7, t2, -784
                  lui        zero, 195546
                  c.add      t1, a1
                  slli       s11, gp, 14
                  mulhu      tp, s3, a4
                  c.and      a0, s0
                  sra        s1, t3, s1
                  lui        zero, 195546
                  c.and      a0, s0
                  mulh       s11, s1, s9
                  div        t3, t1, t5
                  mulh       s11, s1, s9
                  c.lui      a0, 24
                  c.xor      a1, a2
                  mulh       s11, s1, s9
                  auipc      t6, 688967
                  srai       s10, s1, 24
                  c.mv       a1, s5
                  c.nop
                  c.mv       a1, s5
                  div        t3, t1, t5
                  or         s0, a2, a0
                  c.add      t1, a1
                  addi       a7, t2, -784
                  div        t3, t1, t5
                  ori        t5, t2, 999
                  sra        s1, t3, s1
                  mul        sp, s9, s11
                  slli       s11, gp, 14
                  lui        zero, 195546
                  srli       s8, t6, 19
                  c.slli     t4, 28
                  c.srai     s0, 31
                  c.addi     s1, 6
                  c.addi4spn a4, sp, 288
                  c.addi4spn a4, sp, 288
                  srai       s10, s1, 24
                  or         s0, a2, a0
                  remu       s5, s11, t1
                  xor        t4, s3, t3
                  mulhsu     gp, a1, s1
                  c.add      t1, a1
                  xori       a4, t0, 974
                  sltu       t2, s1, t1
                  c.addi4spn a4, sp, 288
                  slti       tp, t6, 301
                  div        t3, t1, t5
                  mulhu      tp, s3, a4
                  srai       s10, s1, 24
                  nop
                  c.slli     t4, 28
                  ori        t5, t2, 999
                  sub        s9, s6, s5
                  add        s7, s5, a6
                  c.xor      a1, a2
                  mul        sp, s9, s11
                  sltu       t2, s1, t1
                  slti       tp, t6, 301
                  xor        t4, s3, t3
                  c.slli     t4, 28
                  c.lui      a0, 24
                  auipc      t6, 688967
                  srl        a0, s2, a0
                  srli       s8, t6, 19
                  c.add      t1, a1
                  c.addi4spn a4, sp, 288
                  divu       sp, ra, t0
                  div        t3, t1, t5
                  ori        t5, t2, 999
                  mulhu      tp, s3, a4
                  or         s0, a2, a0
                  div        t3, t1, t5
                  divu       sp, ra, t0
                  c.sub      s1, a4
                  c.or       a5, a1
                  c.addi4spn a4, sp, 288
                  srl        a0, s2, a0
                  mulhu      tp, s3, a4
                  mulhsu     gp, a1, s1
                  mulhsu     gp, a1, s1
                  c.add      t1, a1
                  c.nop
                  rem        s0, a3, a2
                  lui        zero, 195546
                  slti       tp, t6, 301
                  lui        zero, 195546
                  c.lui      a0, 24
                  ori        t5, t2, 999
                  sub        s9, s6, s5
                  divu       sp, ra, t0
                  srl        a0, s2, a0
                  or         s0, a2, a0
                  c.xor      a1, a2
                  c.sub      s1, a4
                  sll        t3, s7, a3
                  c.addi     s1, 6
                  sub        s9, s6, s5
                  sltu       t2, s1, t1
                  c.xor      a1, a2
                  remu       s5, s11, t1
                  sra        s1, t3, s1
                  add        s7, s5, a6
                  c.and      a0, s0
                  c.sub      s1, a4
                  srli       s8, t6, 19
                  slt        t1, a1, a4
                  c.li       a7, 27
                  slti       tp, t6, 301
                  c.nop
                  sub        s9, s6, s5
                  ori        t5, t2, 999
                  c.addi16sp sp, 16
                  xor        t4, s3, t3
                  srai       s10, s1, 24
                  c.sub      s1, a4
                  c.andi     a5, -1
                  c.lui      a0, 24
                  c.sub      s1, a4
                  c.addi     s1, 6
                  c.addi16sp sp, 16
                  c.mv       a1, s5
                  lui        zero, 195546
                  ori        t5, t2, 999
                  mulhu      tp, s3, a4
                  c.mv       a1, s5
                  mulhsu     gp, a1, s1
                  slli       s11, gp, 14
                  or         s0, a2, a0
                  c.xor      a1, a2
                  slli       s11, gp, 14
                  c.slli     t4, 28
                  or         s0, a2, a0
                  srli       s8, t6, 19
                  rem        s0, a3, a2
                  sll        t3, s7, a3
                  ori        t5, t2, 999
                  c.or       a5, a1
                  srli       s8, t6, 19
                  add        s7, s5, a6
                  slt        t1, a1, a4
                  mul        sp, s9, s11
                  sltu       t2, s1, t1
                  andi       s8, t1, -26
                  srai       s10, s1, 24
                  lui        zero, 195546
                  or         s0, a2, a0
                  mulh       s11, s1, s9
                  andi       s8, t1, -26
                  c.slli     t4, 28
                  sub        s9, s6, s5
                  addi       a7, t2, -784
                  c.and      a0, s0
                  auipc      t6, 688967
                  c.addi     s1, 6
                  c.or       a5, a1
                  c.sub      s1, a4
                  mulhu      tp, s3, a4
                  mulhu      tp, s3, a4
                  lui        zero, 195546
                  c.lui      a0, 24
                  and        a1, t3, a6
                  mulhsu     gp, a1, s1
                  add        s7, s5, a6
                  c.li       a7, 27
                  mulhu      tp, s3, a4
                  c.mv       a1, s5
                  xor        t4, s3, t3
                  c.slli     t4, 28
                  slli       s11, gp, 14
                  c.addi     s1, 6
                  or         s0, a2, a0
                  c.srai     s0, 31
                  xor        t4, s3, t3
                  c.xor      a1, a2
                  lui        zero, 195546
                  xori       a4, t0, 974
                  c.srai     s0, 31
                  andi       s8, t1, -26
                  mul        sp, s9, s11
                  ori        t5, t2, 999
                  c.srli     a0, 25
                  div        t3, t1, t5
                  mul        sp, s9, s11
                  andi       s8, t1, -26
                  c.addi16sp sp, 16
                  slt        t1, a1, a4
                  xori       a4, t0, 974
                  c.srli     a0, 25
                  mulh       s11, s1, s9
                  sll        t3, s7, a3
                  mulh       s11, s1, s9
                  add        s7, s5, a6
                  sra        s1, t3, s1
                  srl        a0, s2, a0
                  xori       a4, t0, 974
                  mulhu      tp, s3, a4
                  c.or       a5, a1
                  divu       sp, ra, t0
                  c.lui      a0, 24
                  slli       s11, gp, 14
                  c.li       a7, 27
                  sltu       t2, s1, t1
                  mulhu      tp, s3, a4
                  mulhsu     gp, a1, s1
                  div        t3, t1, t5
                  mul        sp, s9, s11
                  c.mv       a1, s5
                  c.addi16sp sp, 16
                  div        t3, t1, t5
                  and        a1, t3, a6
                  lui        zero, 195546
                  xor        t4, s3, t3
                  sltiu      s6, ra, 913
                  c.mv       a1, s5
                  ori        t5, t2, 999
                  and        a1, t3, a6
                  sub        s9, s6, s5
                  srli       s8, t6, 19
                  c.li       a7, 27
                  c.slli     t4, 28
                  remu       s5, s11, t1
                  c.srai     s0, 31
                  divu       sp, ra, t0
                  c.lui      a0, 24
                  xor        t4, s3, t3
                  c.slli     t4, 28
                  mulhsu     gp, a1, s1
                  slli       s11, gp, 14
                  c.or       a5, a1
                  sltiu      s6, ra, 913
                  c.lui      a0, 24
                  nop
                  c.or       a5, a1
                  xor        t4, s3, t3
                  and        a1, t3, a6
                  srli       s8, t6, 19
                  c.add      t1, a1
                  srai       s10, s1, 24
                  sltu       t2, s1, t1
                  slli       s11, gp, 14
                  mulhu      tp, s3, a4
                  slt        t1, a1, a4
                  xori       a4, t0, 974
                  nop
                  sll        t3, s7, a3
                  lui        zero, 195546
                  c.sub      s1, a4
                  nop
                  sra        s1, t3, s1
                  c.srli     a0, 25
                  nop
                  lui        zero, 195546
                  c.nop
                  mulhsu     gp, a1, s1
                  c.mv       a1, s5
                  c.sub      s1, a4
                  sra        s1, t3, s1
                  slli       s11, gp, 14
                  c.nop
                  c.sub      s1, a4
                  mulhsu     gp, a1, s1
                  div        t3, t1, t5
                  c.andi     a5, -1
                  addi       a7, t2, -784
                  c.mv       a1, s5
                  lui        zero, 195546
                  div        t3, t1, t5
                  c.srli     a0, 25
                  c.or       a5, a1
                  mulh       s11, s1, s9
                  srli       s8, t6, 19
                  c.srai     s0, 31
                  lui        zero, 195546
                  addi       a7, t2, -784
                  c.sub      s1, a4
                  andi       s8, t1, -26
                  c.slli     t4, 28
                  sltu       t2, s1, t1
                  mul        sp, s9, s11
                  sub        s9, s6, s5
                  srl        a0, s2, a0
                  auipc      t6, 688967
                  c.or       a5, a1
                  mulh       s11, s1, s9
                  c.li       a7, 27
                  mulhu      tp, s3, a4
                  sltu       t2, s1, t1
                  c.andi     a5, -1
                  srai       s10, s1, 24
                  rem        s0, a3, a2
                  srli       s8, t6, 19
                  c.srli     a0, 25
                  sra        s1, t3, s1
                  xori       a4, t0, 974
                  ori        t5, t2, 999
                  c.li       a7, 27
                  auipc      t6, 688967
                  sltiu      s6, ra, 913
                  addi       a7, t2, -784
                  c.addi     s1, 6
                  sub        s9, s6, s5
                  slli       s11, gp, 14
                  c.nop
                  srl        a0, s2, a0
                  slli       s11, gp, 14
                  xori       a4, t0, 974
                  c.or       a5, a1
                  c.mv       a1, s5
                  xori       a4, t0, 974
                  sltu       t2, s1, t1
                  mulhu      tp, s3, a4
                  lui        zero, 195546
                  mulhu      tp, s3, a4
                  sltiu      s6, ra, 913
                  sub        s9, s6, s5
                  sll        t3, s7, a3
                  c.sub      s1, a4
                  sltiu      s6, ra, 913
                  mulhsu     gp, a1, s1
                  mul        sp, s9, s11
                  or         s0, a2, a0
                  c.xor      a1, a2
                  lui        zero, 195546
                  c.and      a0, s0
                  c.slli     t4, 28
                  sltiu      s6, ra, 913
                  c.addi4spn a4, sp, 288
                  c.lui      a0, 24
                  slt        t1, a1, a4
                  sltu       t2, s1, t1
                  c.lui      a0, 24
                  sra        s1, t3, s1
                  andi       s8, t1, -26
                  sub        s9, s6, s5
                  c.mv       a1, s5
                  auipc      t6, 688967
                  sub        s9, s6, s5
                  c.sub      s1, a4
                  c.add      t1, a1
                  c.sub      s1, a4
                  rem        s0, a3, a2
                  slt        t1, a1, a4
                  mulhsu     gp, a1, s1
                  c.addi16sp sp, 16
                  nop
                  slli       s11, gp, 14
                  c.srli     a0, 25
                  addi       a7, t2, -784
                  c.slli     t4, 28
                  srai       s10, s1, 24
                  c.lui      a0, 24
                  c.xor      a1, a2
                  mulhsu     gp, a1, s1
                  srli       s8, t6, 19
                  c.slli     t4, 28
                  c.addi     s1, 6
                  c.srai     s0, 31
                  slt        t1, a1, a4
                  c.lui      a0, 24
                  and        a1, t3, a6
                  rem        s0, a3, a2
                  nop
                  c.mv       a1, s5
                  nop
                  c.andi     a5, -1
                  rem        s0, a3, a2
                  c.andi     a5, -1
                  c.nop
                  xor        t4, s3, t3
                  c.addi4spn a4, sp, 288
                  mulh       s11, s1, s9
                  divu       sp, ra, t0
                  c.and      a0, s0
                  c.srai     s0, 31
                  c.li       a7, 27
                  sra        s1, t3, s1
                  c.lui      a0, 24
                  mul        sp, s9, s11
                  addi       a7, t2, -784
                  c.mv       a1, s5
                  c.sub      s1, a4
                  lui        zero, 195546
                  c.or       a5, a1
                  c.lui      a0, 24
                  srl        a0, s2, a0
                  c.srli     a0, 25
                  c.mv       a1, s5
                  c.slli     t4, 28
                  c.lui      a0, 24
                  c.add      t1, a1
                  c.sub      s1, a4
                  srl        a0, s2, a0
                  or         s0, a2, a0
                  c.xor      a1, a2
                  nop
                  c.nop
                  andi       s8, t1, -26
                  add        s7, s5, a6
                  mulh       s11, s1, s9
                  ori        t5, t2, 999
                  or         s0, a2, a0
                  sub        s9, s6, s5
                  c.add      t1, a1
                  srli       s8, t6, 19
                  c.mv       a1, s5
                  add        s7, s5, a6
                  c.or       a5, a1
                  c.and      a0, s0
                  c.addi16sp sp, 16
                  sub        s9, s6, s5
                  rem        s0, a3, a2
                  c.mv       a1, s5
                  c.sub      s1, a4
                  rem        s0, a3, a2
                  and        a1, t3, a6
                  c.sub      s1, a4
                  mulhu      tp, s3, a4
                  srai       s10, s1, 24
                  sltiu      s6, ra, 913
                  and        a1, t3, a6
                  and        a1, t3, a6
                  c.mv       a1, s5
                  srl        a0, s2, a0
                  srai       s10, s1, 24
                  mulhsu     gp, a1, s1
                  sub        s9, s6, s5
                  sra        s1, t3, s1
                  c.andi     a5, -1
                  addi       a7, t2, -784
                  xori       a4, t0, 974
                  c.li       a7, 27
                  c.and      a0, s0
                  sll        t3, s7, a3
                  nop
                  srai       s10, s1, 24
                  slli       s11, gp, 14
                  c.nop
                  srli       s8, t6, 19
                  c.addi16sp sp, 16
                  addi       a7, t2, -784
                  mulhsu     gp, a1, s1
                  c.mv       a1, s5
                  and        a1, t3, a6
                  sub        s9, s6, s5
                  div        t3, t1, t5
                  c.addi4spn a4, sp, 288
                  andi       s8, t1, -26
                  c.slli     t4, 28
                  c.and      a0, s0
                  and        a1, t3, a6
                  c.and      a0, s0
                  c.addi4spn a4, sp, 288
                  divu       sp, ra, t0
                  and        a1, t3, a6
                  auipc      t6, 688967
                  addi       a7, t2, -784
                  c.mv       a1, s5
                  c.srai     s0, 31
                  mul        sp, s9, s11
                  ori        t5, t2, 999
                  sub        s9, s6, s5
                  and        a1, t3, a6
                  mulh       s11, s1, s9
                  c.and      a0, s0
                  c.addi     s1, 6
                  c.srli     a0, 25
                  c.addi4spn a4, sp, 288
                  c.li       a7, 27
                  sltiu      s6, ra, 913
                  auipc      t6, 688967
                  mulhu      tp, s3, a4
                  c.add      t1, a1
                  and        a1, t3, a6
                  c.mv       a1, s5
                  div        t3, t1, t5
                  mulh       s11, s1, s9
                  c.xor      a1, a2
                  slti       tp, t6, 301
                  c.xor      a1, a2
                  c.mv       a1, s5
                  c.srli     a0, 25
                  mulh       s11, s1, s9
                  or         s0, a2, a0
                  add        s7, s5, a6
                  srli       s8, t6, 19
                  auipc      t6, 688967
                  c.xor      a1, a2
                  sltu       t2, s1, t1
                  srai       s10, s1, 24
                  c.slli     t4, 28
                  xor        t4, s3, t3
                  slti       tp, t6, 301
                  mulh       s11, s1, s9
                  c.li       a7, 27
                  slt        t1, a1, a4
                  auipc      t6, 688967
                  c.srai     s0, 31
                  c.srai     s0, 31
                  xor        t4, s3, t3
                  mul        sp, s9, s11
                  slt        t1, a1, a4
                  slt        t1, a1, a4
                  c.srli     a0, 25
                  rem        s0, a3, a2
                  mulh       s11, s1, s9
                  c.and      a0, s0
                  slt        t1, a1, a4
                  c.lui      a0, 24
                  c.xor      a1, a2
                  rem        s0, a3, a2
                  xor        t4, s3, t3
                  mul        sp, s9, s11
                  xori       a4, t0, 974
                  ori        t5, t2, 999
                  div        t3, t1, t5
                  sll        t3, s7, a3
                  sll        t3, s7, a3
                  c.addi16sp sp, 16
                  sll        t3, s7, a3
                  slti       tp, t6, 301
                  div        t3, t1, t5
                  c.nop
                  xori       a4, t0, 974
                  c.andi     a5, -1
                  slti       tp, t6, 301
                  c.add      t1, a1
                  c.li       a7, 27
                  mulh       s11, s1, s9
                  c.xor      a1, a2
                  c.add      t1, a1
                  sub        s9, s6, s5
                  c.srli     a0, 25
                  rem        s0, a3, a2
                  xor        t4, s3, t3
                  slli       s11, gp, 14
                  c.addi16sp sp, 16
                  or         s0, a2, a0
                  mulh       s11, s1, s9
                  remu       s5, s11, t1
                  c.add      t1, a1
                  slti       tp, t6, 301
                  c.addi16sp sp, 16
                  c.srai     s0, 31
                  c.addi4spn a4, sp, 288
                  nop
                  and        a1, t3, a6
                  or         s0, a2, a0
                  xor        t4, s3, t3
                  c.and      a0, s0
                  slt        t1, a1, a4
                  c.addi     s1, 6
                  c.add      t1, a1
                  c.addi     s1, 6
                  srai       s10, s1, 24
                  sub        s9, s6, s5
                  c.addi16sp sp, 16
                  c.and      a0, s0
                  c.srli     a0, 25
                  addi       a7, t2, -784
                  srli       s8, t6, 19
                  rem        s0, a3, a2
                  c.addi     s1, 6
                  c.nop
                  c.xor      a1, a2
                  c.add      t1, a1
                  c.lui      a0, 24
                  slli       s11, gp, 14
                  mul        sp, s9, s11
                  mulh       s11, s1, s9
                  sll        t3, s7, a3
                  c.andi     a5, -1
                  c.mv       a1, s5
                  remu       s5, s11, t1
                  c.addi     s1, 6
                  rem        s0, a3, a2
                  addi       a7, t2, -784
                  sltu       t2, s1, t1
                  slli       s11, gp, 14
                  sll        t3, s7, a3
                  c.srli     a0, 25
                  c.addi     s1, 6
                  rem        s0, a3, a2
                  div        t3, t1, t5
                  mulhu      tp, s3, a4
                  c.xor      a1, a2
                  c.mv       a1, s5
                  c.lui      a0, 24
                  c.and      a0, s0
                  srli       s8, t6, 19
                  c.nop
                  mulhu      tp, s3, a4
                  c.srai     s0, 31
                  c.addi4spn a4, sp, 288
                  nop
                  and        a1, t3, a6
                  and        a1, t3, a6
                  add        s7, s5, a6
                  sll        t3, s7, a3
                  xori       a4, t0, 974
                  andi       s8, t1, -26
                  lui        zero, 195546
                  c.mv       a1, s5
                  and        a1, t3, a6
                  div        t3, t1, t5
                  xori       a4, t0, 974
                  c.mv       a1, s5
                  sll        t3, s7, a3
                  and        a1, t3, a6
                  c.li       a7, 27
                  c.xor      a1, a2
                  slt        t1, a1, a4
                  c.nop
                  c.slli     t4, 28
                  lui        zero, 195546
                  remu       s5, s11, t1
                  c.andi     a5, -1
                  remu       s5, s11, t1
                  srli       s8, t6, 19
                  c.addi4spn a4, sp, 288
                  xori       a4, t0, 974
                  slli       s11, gp, 14
                  mulh       s11, s1, s9
                  c.add      t1, a1
                  c.addi16sp sp, 16
                  c.addi4spn a4, sp, 288
                  c.lui      a0, 24
                  c.srli     a0, 25
                  add        s7, s5, a6
                  and        a1, t3, a6
                  c.addi     s1, 6
                  c.srai     s0, 31
                  mulhsu     gp, a1, s1
                  lui        zero, 195546
                  add        s7, s5, a6
                  mul        sp, s9, s11
                  addi       a7, t2, -784
                  mulhsu     gp, a1, s1
                  divu       sp, ra, t0
                  c.srli     a0, 25
                  c.slli     t4, 28
                  andi       s8, t1, -26
                  div        t3, t1, t5
                  xor        t4, s3, t3
                  c.li       a7, 27
                  auipc      t6, 688967
                  mulhsu     gp, a1, s1
                  slt        t1, a1, a4
                  slti       tp, t6, 301
                  c.li       a7, 27
                  andi       s8, t1, -26
                  ori        t5, t2, 999
                  mulh       s11, s1, s9
                  remu       s5, s11, t1
                  slt        t1, a1, a4
                  ori        t5, t2, 999
                  ori        t5, t2, 999
                  c.sub      s1, a4
                  sra        s1, t3, s1
                  srai       s10, s1, 24
                  add        s7, s5, a6
                  mul        sp, s9, s11
                  srl        a0, s2, a0
                  andi       s8, t1, -26
                  c.mv       a1, s5
                  c.nop
                  c.srai     s0, 31
                  sltu       t2, s1, t1
                  c.add      t1, a1
                  srl        a0, s2, a0
                  slti       tp, t6, 301
                  slti       tp, t6, 301
                  nop
                  and        a1, t3, a6
                  mulh       s11, s1, s9
                  lui        zero, 195546
                  rem        s0, a3, a2
                  addi       a7, t2, -784
                  c.addi     s1, 6
                  slt        t1, a1, a4
                  mulh       s11, s1, s9
                  c.addi     s1, 6
                  divu       sp, ra, t0
                  sll        t3, s7, a3
                  c.lui      a0, 24
                  slli       s11, gp, 14
                  c.and      a0, s0
                  li         s7, 0x5c21e8c4 #start riscv_int_numeric_corner_stream_21
                  li         s11, 0x0
                  li         a1, 0x0
                  li         t6, 0x69666040
                  li         a0, 0x0
                  li         s3, 0x991745b6
                  li         tp, 0xce51867e
                  li         a4, 0xffffffff
                  li         sp, 0x5a409975
                  li         t4, 0xbacb45ac
                  rem        a0, tp, a0
                  auipc      t6, 688967
                  sub        tp, t4, tp
                  nop
                  div        a0, a1, a0
                  lui        tp, 195546
                  mulhsu     a0, s11, a0
                  nop
                  addi       tp, s7, 999
                  mulhsu     a0, s11, a0
                  mulhu      tp, tp, tp
                  mulhsu     a0, s11, a0
                  lui        tp, 195546
                  divu       tp, sp, t4
                  nop #end riscv_int_numeric_corner_stream_21
                  slti       tp, t6, 301
                  rem        s0, a3, a2
                  andi       s8, t1, -26
                  slli       s11, gp, 14
                  c.mv       a1, s5
                  andi       s8, t1, -26
                  mulhsu     gp, a1, s1
                  ori        t5, t2, 999
                  nop
                  c.addi4spn a4, sp, 288
                  sub        s9, s6, s5
                  c.xor      a1, a2
                  auipc      t6, 688967
                  slti       tp, t6, 301
                  c.andi     a5, -1
                  sra        s1, t3, s1
                  mul        sp, s9, s11
                  c.and      a0, s0
                  c.and      a0, s0
                  c.li       a7, 27
                  sub        s9, s6, s5
                  c.or       a5, a1
                  auipc      t6, 688967
                  c.xor      a1, a2
                  or         s0, a2, a0
                  li         t5, 0xe86da700 #start riscv_int_numeric_corner_stream_15
                  li         s9, 0x80000000
                  li         a4, 0xffffffff
                  li         s5, 0xffffffff
                  li         s1, 0x80000000
                  li         s11, 0xf4dea5f0
                  li         t4, 0x0
                  li         s6, 0x4819fc5a
                  li         t2, 0xffffffff
                  li         s0, 0x0
                  nop
                  auipc      t5, 688967
                  nop
                  add        s11, a4, s9
                  add        s11, a4, s9
                  nop
                  div        s0, s0, a4
                  auipc      t5, 688967
                  addi       s5, s5, 999
                  div        s0, s0, a4
                  nop
                  addi       s5, s5, 999
                  addi       s5, s5, 999
                  auipc      t5, 688967
                  mulhsu     t5, s0, s0
                  mul        a4, t4, t5
                  mul        a4, t4, t5
                  addi       s5, s5, 999
                  lui        s0, 195546 #end riscv_int_numeric_corner_stream_15
                  mulhsu     gp, a1, s1
                  remu       s5, s11, t1
                  sltiu      s6, ra, 913
                  nop
                  sltu       t2, s1, t1
                  c.nop
                  sll        t3, s7, a3
                  c.mv       a1, s5
                  add        s7, s5, a6
                  and        a1, t3, a6
                  mulh       s11, s1, s9
                  sltiu      s6, ra, 913
                  div        t3, t1, t5
                  lui        zero, 195546
                  nop
                  c.and      a0, s0
                  c.srli     a0, 25
                  srl        a0, s2, a0
                  remu       s5, s11, t1
                  sra        s1, t3, s1
                  c.sub      s1, a4
                  c.nop
                  slli       s11, gp, 14
                  mulhu      tp, s3, a4
                  c.addi     s1, 6
                  mulhu      tp, s3, a4
                  c.addi4spn a4, sp, 288
                  xori       a4, t0, 974
                  c.lui      a0, 24
                  srai       s10, s1, 24
                  xori       a4, t0, 974
                  mul        sp, s9, s11
                  sltiu      s6, ra, 913
                  mulhsu     gp, a1, s1
                  c.nop
                  rem        s0, a3, a2
                  sltiu      s6, ra, 913
                  mulhsu     gp, a1, s1
                  c.li       a7, 27
                  addi       a7, t2, -784
                  c.mv       a1, s5
                  c.addi4spn a4, sp, 288
                  c.or       a5, a1
                  slt        t1, a1, a4
                  addi       a7, t2, -784
                  lui        zero, 195546
                  c.slli     t4, 28
                  div        t3, t1, t5
                  or         s0, a2, a0
                  and        a1, t3, a6
                  c.mv       a1, s5
                  andi       s8, t1, -26
                  mulhu      tp, s3, a4
                  c.addi     s1, 6
                  sll        t3, s7, a3
                  c.slli     t4, 28
                  add        s7, s5, a6
                  nop
                  or         s0, a2, a0
                  rem        s0, a3, a2
                  sltiu      s6, ra, 913
                  c.add      t1, a1
                  div        t3, t1, t5
                  and        a1, t3, a6
                  sll        t3, s7, a3
                  c.xor      a1, a2
                  c.nop
                  c.nop
                  c.nop
                  c.slli     t4, 28
                  slti       tp, t6, 301
                  mulhsu     gp, a1, s1
                  sltu       t2, s1, t1
                  sltu       t2, s1, t1
                  c.andi     a5, -1
                  c.srli     a0, 25
                  srl        a0, s2, a0
                  nop
                  c.srai     s0, 31
                  sll        t3, s7, a3
                  and        a1, t3, a6
                  remu       s5, s11, t1
                  sra        s1, t3, s1
                  slli       s11, gp, 14
                  or         s0, a2, a0
                  sltiu      s6, ra, 913
                  c.add      t1, a1
                  rem        s0, a3, a2
                  slti       tp, t6, 301
                  add        s7, s5, a6
                  srli       s8, t6, 19
                  c.srli     a0, 25
                  sll        t3, s7, a3
                  divu       sp, ra, t0
                  rem        s0, a3, a2
                  srl        a0, s2, a0
                  slt        t1, a1, a4
                  divu       sp, ra, t0
                  srli       s8, t6, 19
                  c.li       a7, 27
                  ori        t5, t2, 999
                  c.addi     s1, 6
                  c.and      a0, s0
                  remu       s5, s11, t1
                  c.addi     s1, 6
                  xori       a4, t0, 974
                  ori        t5, t2, 999
                  srl        a0, s2, a0
                  lui        zero, 195546
                  srai       s10, s1, 24
                  ori        t5, t2, 999
                  rem        s0, a3, a2
                  c.nop
                  c.and      a0, s0
                  c.addi4spn a4, sp, 288
                  auipc      t6, 688967
                  c.xor      a1, a2
                  ori        t5, t2, 999
                  slli       s11, gp, 14
                  c.srli     a0, 25
                  xor        t4, s3, t3
                  sltiu      s6, ra, 913
                  xori       a4, t0, 974
                  c.xor      a1, a2
                  and        a1, t3, a6
                  nop
                  c.or       a5, a1
                  c.and      a0, s0
                  mulhsu     gp, a1, s1
                  addi       a7, t2, -784
                  sra        s1, t3, s1
                  c.add      t1, a1
                  c.mv       a1, s5
                  mulhsu     gp, a1, s1
                  sll        t3, s7, a3
                  srai       s10, s1, 24
                  remu       s5, s11, t1
                  rem        s0, a3, a2
                  divu       sp, ra, t0
                  c.li       a7, 27
                  slt        t1, a1, a4
                  c.lui      a0, 24
                  srli       s8, t6, 19
                  sll        t3, s7, a3
                  srai       s10, s1, 24
                  slti       tp, t6, 301
                  c.sub      s1, a4
                  c.srli     a0, 25
                  c.srai     s0, 31
                  mulhsu     gp, a1, s1
                  sltu       t2, s1, t1
                  c.addi4spn a4, sp, 288
                  c.or       a5, a1
                  c.lui      a0, 24
                  srli       s8, t6, 19
                  c.addi4spn a4, sp, 288
                  srai       s10, s1, 24
                  c.addi16sp sp, 16
                  c.mv       a1, s5
                  or         s0, a2, a0
                  add        s7, s5, a6
                  remu       s5, s11, t1
                  sll        t3, s7, a3
                  c.lui      a0, 24
                  c.andi     a5, -1
                  mul        sp, s9, s11
                  sub        s9, s6, s5
                  add        s7, s5, a6
                  c.addi16sp sp, 16
                  xor        t4, s3, t3
                  sltu       t2, s1, t1
                  divu       sp, ra, t0
                  nop
                  c.addi     s1, 6
                  c.mv       a1, s5
                  lui        zero, 195546
                  mulh       s11, s1, s9
                  remu       s5, s11, t1
                  c.xor      a1, a2
                  sra        s1, t3, s1
                  xor        t4, s3, t3
                  c.lui      a0, 24
                  sll        t3, s7, a3
                  c.addi16sp sp, 16
                  sra        s1, t3, s1
                  c.andi     a5, -1
                  slti       tp, t6, 301
                  and        a1, t3, a6
                  sub        s9, s6, s5
                  c.addi4spn a4, sp, 288
                  c.and      a0, s0
                  c.addi     s1, 6
                  c.addi4spn a4, sp, 288
                  c.srli     a0, 25
                  c.nop
                  c.andi     a5, -1
                  addi       a7, t2, -784
                  sltu       t2, s1, t1
                  c.srai     s0, 31
                  remu       s5, s11, t1
                  sltiu      s6, ra, 913
                  c.add      t1, a1
                  ori        t5, t2, 999
                  xor        t4, s3, t3
                  xori       a4, t0, 974
                  sra        s1, t3, s1
                  c.srli     a0, 25
                  mulhsu     gp, a1, s1
                  c.slli     t4, 28
                  c.addi4spn a4, sp, 288
                  srl        a0, s2, a0
                  div        t3, t1, t5
                  mulhsu     gp, a1, s1
                  mulhu      tp, s3, a4
                  sltu       t2, s1, t1
                  mulhsu     gp, a1, s1
                  slti       tp, t6, 301
                  c.lui      a0, 24
                  xor        t4, s3, t3
                  c.xor      a1, a2
                  c.li       a7, 27
                  div        t3, t1, t5
                  c.slli     t4, 28
                  c.li       a7, 27
                  c.add      t1, a1
                  c.xor      a1, a2
                  rem        s0, a3, a2
                  rem        s0, a3, a2
                  c.and      a0, s0
                  mulhu      tp, s3, a4
                  c.addi16sp sp, 16
                  nop
                  or         s0, a2, a0
                  mulh       s11, s1, s9
                  c.srli     a0, 25
                  srai       s10, s1, 24
                  ori        t5, t2, 999
                  sub        s9, s6, s5
                  c.nop
                  mul        sp, s9, s11
                  andi       s8, t1, -26
                  c.add      t1, a1
                  sll        t3, s7, a3
                  c.sub      s1, a4
                  ori        t5, t2, 999
                  c.sub      s1, a4
                  add        s7, s5, a6
                  c.addi     s1, 6
                  and        a1, t3, a6
                  mulh       s11, s1, s9
                  srli       s8, t6, 19
                  c.or       a5, a1
                  srai       s10, s1, 24
                  remu       s5, s11, t1
                  c.andi     a5, -1
                  srli       s8, t6, 19
                  add        s7, s5, a6
                  sll        t3, s7, a3
                  sltu       t2, s1, t1
                  c.andi     a5, -1
                  c.or       a5, a1
                  c.and      a0, s0
                  xor        t4, s3, t3
                  c.addi16sp sp, 16
                  add        s7, s5, a6
                  remu       s5, s11, t1
                  c.sub      s1, a4
                  c.sub      s1, a4
                  sltiu      s6, ra, 913
                  remu       s5, s11, t1
                  c.andi     a5, -1
                  c.and      a0, s0
                  slli       s11, gp, 14
                  c.addi16sp sp, 16
                  c.mv       a1, s5
                  ori        t5, t2, 999
                  c.addi4spn a4, sp, 288
                  auipc      t6, 688967
                  c.xor      a1, a2
                  srai       s10, s1, 24
                  and        a1, t3, a6
                  sltiu      s6, ra, 913
                  c.li       a7, 27
                  rem        s0, a3, a2
                  c.srli     a0, 25
                  divu       sp, ra, t0
                  slli       s11, gp, 14
                  or         s0, a2, a0
                  lui        zero, 195546
                  c.sub      s1, a4
                  xor        t4, s3, t3
                  slti       tp, t6, 301
                  c.addi16sp sp, 16
                  c.add      t1, a1
                  mulh       s11, s1, s9
                  srai       s10, s1, 24
                  slti       tp, t6, 301
                  remu       s5, s11, t1
                  nop
                  sll        t3, s7, a3
                  nop
                  ori        t5, t2, 999
                  c.add      t1, a1
                  mul        sp, s9, s11
                  c.sub      s1, a4
                  c.srai     s0, 31
                  auipc      t6, 688967
                  mulhsu     gp, a1, s1
                  div        t3, t1, t5
                  add        s7, s5, a6
                  srl        a0, s2, a0
                  c.mv       a1, s5
                  addi       a7, t2, -784
                  mulhsu     gp, a1, s1
                  c.mv       a1, s5
                  mulhsu     gp, a1, s1
                  c.or       a5, a1
                  mulhu      tp, s3, a4
                  slt        t1, a1, a4
                  slti       tp, t6, 301
                  slli       s11, gp, 14
                  or         s0, a2, a0
                  slt        t1, a1, a4
                  sltiu      s6, ra, 913
                  c.li       a7, 27
                  add        s7, s5, a6
                  srli       s8, t6, 19
                  xori       a4, t0, 974
                  c.addi4spn a4, sp, 288
                  auipc      t6, 688967
                  slt        t1, a1, a4
                  c.addi     s1, 6
                  auipc      t6, 688967
                  sltu       t2, s1, t1
                  mulhu      tp, s3, a4
                  sltiu      s6, ra, 913
                  sub        s9, s6, s5
                  sll        t3, s7, a3
                  c.xor      a1, a2
                  slli       s11, gp, 14
                  c.srli     a0, 25
                  slti       tp, t6, 301
                  rem        s0, a3, a2
                  andi       s8, t1, -26
                  c.addi4spn a4, sp, 288
                  nop
                  add        s7, s5, a6
                  rem        s0, a3, a2
                  c.addi4spn a4, sp, 288
                  auipc      t6, 688967
                  andi       s8, t1, -26
                  mulhsu     gp, a1, s1
                  c.or       a5, a1
                  add        s7, s5, a6
                  div        t3, t1, t5
                  c.nop
                  mulhsu     gp, a1, s1
                  remu       s5, s11, t1
                  c.addi4spn a4, sp, 288
                  mulhu      tp, s3, a4
                  c.nop
                  addi       a7, t2, -784
                  c.sub      s1, a4
                  rem        s0, a3, a2
                  c.slli     t4, 28
                  c.sub      s1, a4
                  slti       tp, t6, 301
                  sltiu      s6, ra, 913
                  c.or       a5, a1
                  mul        sp, s9, s11
                  c.andi     a5, -1
                  slt        t1, a1, a4
                  c.addi4spn a4, sp, 288
                  c.andi     a5, -1
                  or         s0, a2, a0
                  c.add      t1, a1
                  mulh       s11, s1, s9
                  andi       s8, t1, -26
                  c.andi     a5, -1
                  c.mv       a1, s5
                  addi       a7, t2, -784
                  slli       s11, gp, 14
                  c.xor      a1, a2
                  sltiu      s6, ra, 913
                  c.slli     t4, 28
                  or         s0, a2, a0
                  auipc      t6, 688967
                  srl        a0, s2, a0
                  c.add      t1, a1
                  c.addi     s1, 6
                  remu       s5, s11, t1
                  c.addi     s1, 6
                  c.mv       a1, s5
                  ori        t5, t2, 999
                  c.andi     a5, -1
                  srl        a0, s2, a0
                  srl        a0, s2, a0
                  div        t3, t1, t5
                  srai       s10, s1, 24
                  c.xor      a1, a2
                  divu       sp, ra, t0
                  div        t3, t1, t5
                  lui        zero, 195546
                  c.xor      a1, a2
                  c.addi     s1, 6
                  ori        t5, t2, 999
                  c.lui      a0, 24
                  srai       s10, s1, 24
                  lui        zero, 195546
                  xori       a4, t0, 974
                  sltu       t2, s1, t1
                  c.li       a7, 27
                  c.sub      s1, a4
                  c.and      a0, s0
                  c.addi     s1, 6
                  xori       a4, t0, 974
                  c.srli     a0, 25
                  c.lui      a0, 24
                  c.addi     s1, 6
                  c.andi     a5, -1
                  c.mv       a1, s5
                  c.addi     s1, 6
                  srai       s10, s1, 24
                  srai       s10, s1, 24
                  andi       s8, t1, -26
                  c.addi4spn a4, sp, 288
                  c.and      a0, s0
                  mulh       s11, s1, s9
                  andi       s8, t1, -26
                  lui        zero, 195546
                  remu       s5, s11, t1
                  lui        zero, 195546
                  xori       a4, t0, 974
                  c.slli     t4, 28
                  add        s7, s5, a6
                  andi       s8, t1, -26
                  c.xor      a1, a2
                  slli       s11, gp, 14
                  xori       a4, t0, 974
                  sra        s1, t3, s1
                  mulh       s11, s1, s9
                  c.mv       a1, s5
                  mulhsu     gp, a1, s1
                  mulhu      tp, s3, a4
                  srl        a0, s2, a0
                  mulhsu     gp, a1, s1
                  divu       sp, ra, t0
                  xor        t4, s3, t3
                  sltiu      s6, ra, 913
                  c.sub      s1, a4
                  rem        s0, a3, a2
                  sra        s1, t3, s1
                  c.xor      a1, a2
                  or         s0, a2, a0
                  sltiu      s6, ra, 913
                  addi       a7, t2, -784
                  c.srli     a0, 25
                  c.nop
                  sll        t3, s7, a3
                  c.li       a7, 27
                  or         s0, a2, a0
                  srli       s8, t6, 19
                  sltiu      s6, ra, 913
                  sltu       t2, s1, t1
                  sll        t3, s7, a3
                  auipc      t6, 688967
                  mul        sp, s9, s11
                  sltu       t2, s1, t1
                  c.andi     a5, -1
                  srli       s8, t6, 19
                  nop
                  srai       s10, s1, 24
                  xor        t4, s3, t3
                  c.or       a5, a1
                  sra        s1, t3, s1
                  slti       tp, t6, 301
                  c.srli     a0, 25
                  remu       s5, s11, t1
                  add        s7, s5, a6
                  or         s0, a2, a0
                  auipc      t6, 688967
                  xori       a4, t0, 974
                  divu       sp, ra, t0
                  mulhu      tp, s3, a4
                  slli       s11, gp, 14
                  c.srli     a0, 25
                  srl        a0, s2, a0
                  c.xor      a1, a2
                  mul        sp, s9, s11
                  srai       s10, s1, 24
                  srli       s8, t6, 19
                  mulhu      tp, s3, a4
                  c.slli     t4, 28
                  nop
                  c.or       a5, a1
                  c.li       a7, 27
                  c.addi     s1, 6
                  c.nop
                  sltiu      s6, ra, 913
                  mulhu      tp, s3, a4
                  c.sub      s1, a4
                  c.lui      a0, 24
                  c.addi16sp sp, 16
                  sll        t3, s7, a3
                  c.addi4spn a4, sp, 288
                  xor        t4, s3, t3
                  slti       tp, t6, 301
                  and        a1, t3, a6
                  auipc      t6, 688967
                  c.addi4spn a4, sp, 288
                  c.srli     a0, 25
                  slt        t1, a1, a4
                  c.addi     s1, 6
                  mul        sp, s9, s11
                  sub        s9, s6, s5
                  c.srai     s0, 31
                  mul        sp, s9, s11
                  sltiu      s6, ra, 913
                  remu       s5, s11, t1
                  mulh       s11, s1, s9
                  c.srai     s0, 31
                  c.addi     s1, 6
                  mulhsu     gp, a1, s1
                  srai       s10, s1, 24
                  remu       s5, s11, t1
                  sra        s1, t3, s1
                  c.xor      a1, a2
                  c.xor      a1, a2
                  sltu       t2, s1, t1
                  sltiu      s6, ra, 913
                  sra        s1, t3, s1
                  c.li       a7, 27
                  sub        s9, s6, s5
                  xor        t4, s3, t3
                  c.lui      a0, 24
                  c.and      a0, s0
                  c.addi16sp sp, 16
                  xori       a4, t0, 974
                  c.addi16sp sp, 16
                  slli       s11, gp, 14
                  slti       tp, t6, 301
                  c.addi16sp sp, 16
                  c.lui      a0, 24
                  and        a1, t3, a6
                  lui        zero, 195546
                  lui        zero, 195546
                  remu       s5, s11, t1
                  mul        sp, s9, s11
                  c.addi     s1, 6
                  c.addi4spn a4, sp, 288
                  c.nop
                  c.xor      a1, a2
                  c.li       a7, 27
                  sltu       t2, s1, t1
                  xor        t4, s3, t3
                  c.sub      s1, a4
                  c.nop
                  auipc      t6, 688967
                  remu       s5, s11, t1
                  srl        a0, s2, a0
                  c.srai     s0, 31
                  c.nop
                  lui        zero, 195546
                  xor        t4, s3, t3
                  sub        s9, s6, s5
                  c.li       a7, 27
                  sltiu      s6, ra, 913
                  sub        s9, s6, s5
                  mulhu      tp, s3, a4
                  sll        t3, s7, a3
                  sra        s1, t3, s1
                  and        a1, t3, a6
                  sra        s1, t3, s1
                  add        s7, s5, a6
                  c.andi     a5, -1
                  or         s0, a2, a0
                  c.slli     t4, 28
                  c.and      a0, s0
                  mulh       s11, s1, s9
                  c.sub      s1, a4
                  c.andi     a5, -1
                  xor        t4, s3, t3
                  remu       s5, s11, t1
                  c.or       a5, a1
                  andi       s8, t1, -26
                  slt        t1, a1, a4
                  srai       s10, s1, 24
                  auipc      t6, 688967
                  div        t3, t1, t5
                  mulhsu     gp, a1, s1
                  and        a1, t3, a6
                  c.and      a0, s0
                  rem        s0, a3, a2
                  remu       s5, s11, t1
                  mulh       s11, s1, s9
                  auipc      t6, 688967
                  mulh       s11, s1, s9
                  divu       sp, ra, t0
                  mulhsu     gp, a1, s1
                  slt        t1, a1, a4
                  sltiu      s6, ra, 913
                  ori        t5, t2, 999
                  c.nop
                  mulh       s11, s1, s9
                  or         s0, a2, a0
                  xori       a4, t0, 974
                  slli       s11, gp, 14
                  mulhsu     gp, a1, s1
                  c.lui      a0, 24
                  c.nop
                  xor        t4, s3, t3
                  mulhsu     gp, a1, s1
                  c.addi4spn a4, sp, 288
                  c.srli     a0, 25
                  c.and      a0, s0
                  andi       s8, t1, -26
                  add        s7, s5, a6
                  auipc      t6, 688967
                  sltiu      s6, ra, 913
                  andi       s8, t1, -26
                  divu       sp, ra, t0
                  c.nop
                  c.nop
                  div        t3, t1, t5
                  c.sub      s1, a4
                  andi       s8, t1, -26
                  ori        t5, t2, 999
                  xor        t4, s3, t3
                  c.lui      a0, 24
                  sltu       t2, s1, t1
                  c.srai     s0, 31
                  c.lui      a0, 24
                  c.addi     s1, 6
                  rem        s0, a3, a2
                  srli       s8, t6, 19
                  slt        t1, a1, a4
                  and        a1, t3, a6
                  auipc      t6, 688967
                  c.and      a0, s0
                  srli       s8, t6, 19
                  add        s7, s5, a6
                  c.andi     a5, -1
                  c.srli     a0, 25
                  sll        t3, s7, a3
                  c.li       a7, 27
                  c.andi     a5, -1
                  lui        zero, 195546
                  c.lui      a0, 24
                  sub        s9, s6, s5
                  srl        a0, s2, a0
                  mul        sp, s9, s11
                  and        a1, t3, a6
                  c.srai     s0, 31
                  c.addi16sp sp, 16
                  c.andi     a5, -1
                  andi       s8, t1, -26
                  slti       tp, t6, 301
                  c.addi4spn a4, sp, 288
                  c.or       a5, a1
                  nop
                  c.sub      s1, a4
                  sll        t3, s7, a3
                  c.lui      a0, 24
                  sll        t3, s7, a3
                  c.andi     a5, -1
                  sll        t3, s7, a3
                  c.add      t1, a1
                  add        s7, s5, a6
                  srai       s10, s1, 24
                  xor        t4, s3, t3
                  c.nop
                  auipc      t6, 688967
                  c.andi     a5, -1
                  c.srli     a0, 25
                  c.srli     a0, 25
                  xori       a4, t0, 974
                  c.li       a7, 27
                  xor        t4, s3, t3
                  sra        s1, t3, s1
                  nop
                  c.addi     s1, 6
                  srai       s10, s1, 24
                  xor        t4, s3, t3
                  c.xor      a1, a2
                  c.and      a0, s0
                  lui        zero, 195546
                  c.li       a7, 27
                  mulhu      tp, s3, a4
                  c.srai     s0, 31
                  c.lui      a0, 24
                  sub        s9, s6, s5
                  xor        t4, s3, t3
                  addi       a7, t2, -784
                  c.lui      a0, 24
                  c.srli     a0, 25
                  c.and      a0, s0
                  c.addi     s1, 6
                  xor        t4, s3, t3
                  c.xor      a1, a2
                  auipc      t6, 688967
                  c.addi     s1, 6
                  mul        sp, s9, s11
                  ori        t5, t2, 999
                  c.addi     s1, 6
                  or         s0, a2, a0
                  c.addi16sp sp, 16
                  c.srli     a0, 25
                  c.lui      a0, 24
                  mul        sp, s9, s11
                  ori        t5, t2, 999
                  c.or       a5, a1
                  c.mv       a1, s5
                  div        t3, t1, t5
                  c.srai     s0, 31
                  mulhsu     gp, a1, s1
                  c.andi     a5, -1
                  c.li       a7, 27
                  div        t3, t1, t5
                  xor        t4, s3, t3
                  sltiu      s6, ra, 913
                  c.sub      s1, a4
                  sll        t3, s7, a3
                  mulhsu     gp, a1, s1
                  ori        t5, t2, 999
                  srli       s8, t6, 19
                  remu       s5, s11, t1
                  sltu       t2, s1, t1
                  c.srai     s0, 31
                  c.nop
                  c.li       a7, 27
                  mul        sp, s9, s11
                  sltu       t2, s1, t1
                  slt        t1, a1, a4
                  c.li       a7, 27
                  rem        s0, a3, a2
                  c.or       a5, a1
                  c.slli     t4, 28
                  srl        a0, s2, a0
                  remu       s5, s11, t1
                  lui        zero, 195546
                  auipc      t6, 688967
                  c.mv       a1, s5
                  ori        t5, t2, 999
                  rem        s0, a3, a2
                  sub        s9, s6, s5
                  divu       sp, ra, t0
                  andi       s8, t1, -26
                  and        a1, t3, a6
                  srl        a0, s2, a0
                  div        t3, t1, t5
                  li         s8, 0xffffffff #start riscv_int_numeric_corner_stream_18
                  li         a1, 0xffffffff
                  li         t2, 0xc2599e47
                  li         s7, 0xf8b0bfea
                  li         a6, 0x0
                  li         t5, 0xffffffff
                  li         t6, 0x71c3cd1f
                  li         s6, 0x80000000
                  li         t3, 0x80000000
                  li         s0, 0x0
                  auipc      t6, 688967
                  remu       s7, t2, s0
                  add        a1, t3, t3
                  add        a1, t3, t3
                  mul        s7, s0, s8
                  div        a6, s8, s6
                  auipc      t6, 688967
                  remu       s7, t2, s0
                  sub        t2, s0, t3
                  lui        s0, 195546
                  mulh       s7, s7, t3
                  auipc      t6, 688967
                  addi       s0, t2, 999
                  remu       s7, t2, s0
                  mul        s7, s0, s8 #end riscv_int_numeric_corner_stream_18
                  auipc      t6, 688967
                  slt        t1, a1, a4
                  slti       tp, t6, 301
                  c.addi4spn a4, sp, 288
                  slti       tp, t6, 301
                  slli       s11, gp, 14
                  mulhu      tp, s3, a4
                  xori       a4, t0, 974
                  c.addi4spn a4, sp, 288
                  remu       s5, s11, t1
                  c.xor      a1, a2
                  div        t3, t1, t5
                  c.mv       a1, s5
                  auipc      t6, 688967
                  c.or       a5, a1
                  srl        a0, s2, a0
                  c.lui      a0, 24
                  slti       tp, t6, 301
                  divu       sp, ra, t0
                  div        t3, t1, t5
                  c.andi     a5, -1
                  c.xor      a1, a2
                  c.sub      s1, a4
                  mulhsu     gp, a1, s1
                  xor        t4, s3, t3
                  and        a1, t3, a6
                  c.addi16sp sp, 16
                  sra        s1, t3, s1
                  slt        t1, a1, a4
                  mulhsu     gp, a1, s1
                  srai       s10, s1, 24
                  mulhsu     gp, a1, s1
                  nop
                  mulhsu     gp, a1, s1
                  add        s7, s5, a6
                  c.addi16sp sp, 16
                  ori        t5, t2, 999
                  auipc      t6, 688967
                  addi       a7, t2, -784
                  lui        zero, 195546
                  and        a1, t3, a6
                  c.add      t1, a1
                  ori        t5, t2, 999
                  c.mv       a1, s5
                  c.srai     s0, 31
                  sll        t3, s7, a3
                  c.addi16sp sp, 16
                  mul        sp, s9, s11
                  rem        s0, a3, a2
                  c.or       a5, a1
                  xori       a4, t0, 974
                  div        t3, t1, t5
                  mulhu      tp, s3, a4
                  div        t3, t1, t5
                  mulh       s11, s1, s9
                  c.mv       a1, s5
                  mulhsu     gp, a1, s1
                  c.and      a0, s0
                  add        s7, s5, a6
                  c.addi     s1, 6
                  c.mv       a1, s5
                  c.slli     t4, 28
                  sltiu      s6, ra, 913
                  add        s7, s5, a6
                  c.nop
                  auipc      t6, 688967
                  c.srai     s0, 31
                  srli       s8, t6, 19
                  c.srli     a0, 25
                  c.addi16sp sp, 16
                  c.slli     t4, 28
                  nop
                  nop
                  c.add      t1, a1
                  srli       s8, t6, 19
                  c.slli     t4, 28
                  c.srai     s0, 31
                  xor        t4, s3, t3
                  c.addi     s1, 6
                  lui        zero, 195546
                  andi       s8, t1, -26
                  mul        sp, s9, s11
                  c.and      a0, s0
                  c.srli     a0, 25
                  mulhu      tp, s3, a4
                  c.addi16sp sp, 16
                  lui        zero, 195546
                  c.xor      a1, a2
                  c.addi     s1, 6
                  c.addi     s1, 6
                  divu       sp, ra, t0
                  divu       sp, ra, t0
                  c.srai     s0, 31
                  slli       s11, gp, 14
                  c.xor      a1, a2
                  c.and      a0, s0
                  slt        t1, a1, a4
                  c.mv       a1, s5
                  c.and      a0, s0
                  c.nop
                  c.li       a7, 27
                  mulhu      tp, s3, a4
                  c.and      a0, s0
                  c.srli     a0, 25
                  sra        s1, t3, s1
                  xor        t4, s3, t3
                  c.add      t1, a1
                  srli       s8, t6, 19
                  slli       s11, gp, 14
                  c.and      a0, s0
                  c.addi4spn a4, sp, 288
                  srai       s10, s1, 24
                  and        a1, t3, a6
                  c.andi     a5, -1
                  srli       s8, t6, 19
                  div        t3, t1, t5
                  ori        t5, t2, 999
                  andi       s8, t1, -26
                  c.and      a0, s0
                  add        s7, s5, a6
                  div        t3, t1, t5
                  srai       s10, s1, 24
                  mulh       s11, s1, s9
                  mulh       s11, s1, s9
                  c.xor      a1, a2
                  c.addi16sp sp, 16
                  c.slli     t4, 28
                  srai       s10, s1, 24
                  mulh       s11, s1, s9
                  sll        t3, s7, a3
                  c.xor      a1, a2
                  rem        s0, a3, a2
                  auipc      t6, 688967
                  srai       s10, s1, 24
                  c.add      t1, a1
                  remu       s5, s11, t1
                  c.slli     t4, 28
                  c.sub      s1, a4
                  c.lui      a0, 24
                  and        a1, t3, a6
                  c.addi4spn a4, sp, 288
                  c.srli     a0, 25
                  ori        t5, t2, 999
                  slli       s11, gp, 14
                  sra        s1, t3, s1
                  c.lui      a0, 24
                  auipc      t6, 688967
                  c.or       a5, a1
                  slli       s11, gp, 14
                  c.addi16sp sp, 16
                  sub        s9, s6, s5
                  mulhsu     gp, a1, s1
                  ori        t5, t2, 999
                  c.add      t1, a1
                  remu       s5, s11, t1
                  srai       s10, s1, 24
                  c.mv       a1, s5
                  sub        s9, s6, s5
                  mulhu      tp, s3, a4
                  auipc      t6, 688967
                  nop
                  srai       s10, s1, 24
                  c.andi     a5, -1
                  ori        t5, t2, 999
                  slli       s11, gp, 14
                  c.li       a7, 27
                  c.li       a7, 27
                  xor        t4, s3, t3
                  srli       s8, t6, 19
                  lui        zero, 195546
                  c.and      a0, s0
                  srai       s10, s1, 24
                  add        s7, s5, a6
                  mulh       s11, s1, s9
                  c.mv       a1, s5
                  divu       sp, ra, t0
                  c.sub      s1, a4
                  c.slli     t4, 28
                  sra        s1, t3, s1
                  sll        t3, s7, a3
                  c.addi4spn a4, sp, 288
                  and        a1, t3, a6
                  srai       s10, s1, 24
                  lui        zero, 195546
                  c.srai     s0, 31
                  nop
                  sll        t3, s7, a3
                  c.addi4spn a4, sp, 288
                  mulhu      tp, s3, a4
                  srli       s8, t6, 19
                  sltiu      s6, ra, 913
                  c.nop
                  ori        t5, t2, 999
                  div        t3, t1, t5
                  srl        a0, s2, a0
                  c.and      a0, s0
                  sra        s1, t3, s1
                  c.add      t1, a1
                  sltu       t2, s1, t1
                  remu       s5, s11, t1
                  c.slli     t4, 28
                  sra        s1, t3, s1
                  mulhsu     gp, a1, s1
                  sra        s1, t3, s1
                  c.addi16sp sp, 16
                  c.mv       a1, s5
                  c.addi     s1, 6
                  xor        t4, s3, t3
                  mulhu      tp, s3, a4
                  rem        s0, a3, a2
                  c.addi16sp sp, 16
                  lui        zero, 195546
                  c.addi16sp sp, 16
                  lui        zero, 195546
                  rem        s0, a3, a2
                  mulh       s11, s1, s9
                  xor        t4, s3, t3
                  c.or       a5, a1
                  c.lui      a0, 24
                  sub        s9, s6, s5
                  rem        s0, a3, a2
                  mulh       s11, s1, s9
                  srli       s8, t6, 19
                  c.addi16sp sp, 16
                  mulh       s11, s1, s9
                  c.nop
                  c.srli     a0, 25
                  remu       s5, s11, t1
                  c.addi     s1, 6
                  andi       s8, t1, -26
                  slt        t1, a1, a4
                  remu       s5, s11, t1
                  or         s0, a2, a0
                  srai       s10, s1, 24
                  ori        t5, t2, 999
                  slti       tp, t6, 301
                  slti       tp, t6, 301
                  c.srli     a0, 25
                  sltiu      s6, ra, 913
                  c.nop
                  c.addi16sp sp, 16
                  lui        zero, 195546
                  andi       s8, t1, -26
                  remu       s5, s11, t1
                  c.andi     a5, -1
                  c.slli     t4, 28
                  srai       s10, s1, 24
                  add        s7, s5, a6
                  or         s0, a2, a0
                  srl        a0, s2, a0
                  c.srli     a0, 25
                  nop
                  c.lui      a0, 24
                  c.slli     t4, 28
                  c.srai     s0, 31
                  div        t3, t1, t5
                  c.and      a0, s0
                  auipc      t6, 688967
                  sll        t3, s7, a3
                  c.slli     t4, 28
                  c.or       a5, a1
                  rem        s0, a3, a2
                  srai       s10, s1, 24
                  add        s7, s5, a6
                  c.andi     a5, -1
                  c.add      t1, a1
                  rem        s0, a3, a2
                  auipc      t6, 688967
                  c.srli     a0, 25
                  c.sub      s1, a4
                  ori        t5, t2, 999
                  addi       a7, t2, -784
                  sltiu      s6, ra, 913
                  sltu       t2, s1, t1
                  srai       s10, s1, 24
                  lui        zero, 195546
                  sra        s1, t3, s1
                  c.slli     t4, 28
                  and        a1, t3, a6
                  c.nop
                  divu       sp, ra, t0
                  c.addi16sp sp, 16
                  sra        s1, t3, s1
                  divu       sp, ra, t0
                  div        t3, t1, t5
                  c.andi     a5, -1
                  c.srai     s0, 31
                  c.li       a7, 27
                  c.lui      a0, 24
                  mulhsu     gp, a1, s1
                  sltiu      s6, ra, 913
                  div        t3, t1, t5
                  andi       s8, t1, -26
                  mulhu      tp, s3, a4
                  srai       s10, s1, 24
                  or         s0, a2, a0
                  c.slli     t4, 28
                  slti       tp, t6, 301
                  srl        a0, s2, a0
                  slti       tp, t6, 301
                  srai       s10, s1, 24
                  c.srli     a0, 25
                  sub        s9, s6, s5
                  srl        a0, s2, a0
                  xori       a4, t0, 974
                  c.srai     s0, 31
                  div        t3, t1, t5
                  divu       sp, ra, t0
                  slt        t1, a1, a4
                  addi       a7, t2, -784
                  mulhu      tp, s3, a4
                  or         s0, a2, a0
                  mulh       s11, s1, s9
                  c.xor      a1, a2
                  rem        s0, a3, a2
                  sll        t3, s7, a3
                  sltiu      s6, ra, 913
                  remu       s5, s11, t1
                  mulhsu     gp, a1, s1
                  rem        s0, a3, a2
                  c.srai     s0, 31
                  c.or       a5, a1
                  mulhsu     gp, a1, s1
                  and        a1, t3, a6
                  mulhu      tp, s3, a4
                  c.and      a0, s0
                  c.srai     s0, 31
                  mulh       s11, s1, s9
                  srli       s8, t6, 19
                  div        t3, t1, t5
                  srli       s8, t6, 19
                  srl        a0, s2, a0
                  sltiu      s6, ra, 913
                  add        s7, s5, a6
                  and        a1, t3, a6
                  c.srai     s0, 31
                  and        a1, t3, a6
                  c.addi     s1, 6
                  srl        a0, s2, a0
                  c.srli     a0, 25
                  sra        s1, t3, s1
                  sra        s1, t3, s1
                  and        a1, t3, a6
                  c.srai     s0, 31
                  mulh       s11, s1, s9
                  div        t3, t1, t5
                  c.srli     a0, 25
                  or         s0, a2, a0
                  slli       s11, gp, 14
                  and        a1, t3, a6
                  sltiu      s6, ra, 913
                  div        t3, t1, t5
                  add        s7, s5, a6
                  c.addi     s1, 6
                  srl        a0, s2, a0
                  srl        a0, s2, a0
                  slti       tp, t6, 301
                  c.addi16sp sp, 16
                  mulhu      tp, s3, a4
                  rem        s0, a3, a2
                  c.mv       a1, s5
                  lui        zero, 195546
                  slt        t1, a1, a4
                  c.slli     t4, 28
                  slti       tp, t6, 301
                  auipc      t6, 688967
                  c.li       a7, 27
                  c.or       a5, a1
                  sub        s9, s6, s5
                  ori        t5, t2, 999
                  slli       s11, gp, 14
                  nop
                  c.nop
                  mul        sp, s9, s11
                  c.or       a5, a1
                  c.mv       a1, s5
                  sub        s9, s6, s5
                  xor        t4, s3, t3
                  andi       s8, t1, -26
                  auipc      t6, 688967
                  xori       a4, t0, 974
                  srai       s10, s1, 24
                  c.mv       a1, s5
                  and        a1, t3, a6
                  c.li       a7, 27
                  sra        s1, t3, s1
                  remu       s5, s11, t1
                  c.lui      a0, 24
                  addi       a7, t2, -784
                  c.andi     a5, -1
                  c.addi16sp sp, 16
                  c.andi     a5, -1
                  sll        t3, s7, a3
                  c.sub      s1, a4
                  c.addi16sp sp, 16
                  div        t3, t1, t5
                  nop
                  remu       s5, s11, t1
                  lui        zero, 195546
                  rem        s0, a3, a2
                  sltiu      s6, ra, 913
                  div        t3, t1, t5
                  c.addi     s1, 6
                  auipc      t6, 688967
                  sltu       t2, s1, t1
                  c.slli     t4, 28
                  srai       s10, s1, 24
                  sll        t3, s7, a3
                  div        t3, t1, t5
                  nop
                  ori        t5, t2, 999
                  c.srli     a0, 25
                  slt        t1, a1, a4
                  nop
                  c.nop
                  c.add      t1, a1
                  slti       tp, t6, 301
                  c.add      t1, a1
                  sltu       t2, s1, t1
                  div        t3, t1, t5
                  slli       s11, gp, 14
                  c.srai     s0, 31
                  sltu       t2, s1, t1
                  mulhu      tp, s3, a4
                  c.slli     t4, 28
                  slt        t1, a1, a4
                  c.mv       a1, s5
                  slli       s11, gp, 14
                  xori       a4, t0, 974
                  c.addi16sp sp, 16
                  mulhu      tp, s3, a4
                  srli       s8, t6, 19
                  slti       tp, t6, 301
                  mulhsu     gp, a1, s1
                  c.srai     s0, 31
                  auipc      t6, 688967
                  srai       s10, s1, 24
                  mulhu      tp, s3, a4
                  c.andi     a5, -1
                  srl        a0, s2, a0
                  and        a1, t3, a6
                  srl        a0, s2, a0
                  slt        t1, a1, a4
                  sltu       t2, s1, t1
                  c.slli     t4, 28
                  c.or       a5, a1
                  rem        s0, a3, a2
                  addi       a7, t2, -784
                  c.and      a0, s0
                  andi       s8, t1, -26
                  c.lui      a0, 24
                  ori        t5, t2, 999
                  c.lui      a0, 24
                  c.lui      a0, 24
                  auipc      t6, 688967
                  auipc      t6, 688967
                  c.and      a0, s0
                  and        a1, t3, a6
                  slt        t1, a1, a4
                  rem        s0, a3, a2
                  addi       a7, t2, -784
                  and        a1, t3, a6
                  c.or       a5, a1
                  c.addi     s1, 6
                  rem        s0, a3, a2
                  c.addi16sp sp, 16
                  sll        t3, s7, a3
                  xori       a4, t0, 974
                  add        s7, s5, a6
                  c.slli     t4, 28
                  c.nop
                  c.or       a5, a1
                  srli       s8, t6, 19
                  sra        s1, t3, s1
                  ori        t5, t2, 999
                  xor        t4, s3, t3
                  c.andi     a5, -1
                  sll        t3, s7, a3
                  c.lui      a0, 24
                  c.or       a5, a1
                  mulhu      tp, s3, a4
                  c.addi4spn a4, sp, 288
                  sub        s9, s6, s5
                  andi       s8, t1, -26
                  c.lui      a0, 24
                  c.add      t1, a1
                  and        a1, t3, a6
                  sll        t3, s7, a3
                  c.li       a7, 27
                  mulhsu     gp, a1, s1
                  mulhu      tp, s3, a4
                  ori        t5, t2, 999
                  srli       s8, t6, 19
                  srai       s10, s1, 24
                  srai       s10, s1, 24
                  or         s0, a2, a0
                  div        t3, t1, t5
                  mulh       s11, s1, s9
                  c.nop
                  ori        t5, t2, 999
                  c.andi     a5, -1
                  c.srli     a0, 25
                  nop
                  sub        s9, s6, s5
                  c.addi4spn a4, sp, 288
                  mulhsu     gp, a1, s1
                  andi       s8, t1, -26
                  sltiu      s6, ra, 913
                  divu       sp, ra, t0
                  c.addi4spn a4, sp, 288
                  c.srai     s0, 31
                  lui        zero, 195546
                  slt        t1, a1, a4
                  auipc      t6, 688967
                  c.slli     t4, 28
                  addi       a7, t2, -784
                  slt        t1, a1, a4
                  srl        a0, s2, a0
                  div        t3, t1, t5
                  c.li       a7, 27
                  c.andi     a5, -1
                  c.addi     s1, 6
                  lui        zero, 195546
                  slli       s11, gp, 14
                  andi       s8, t1, -26
                  auipc      t6, 688967
                  sltu       t2, s1, t1
                  srai       s10, s1, 24
                  c.nop
                  c.mv       a1, s5
                  xori       a4, t0, 974
                  c.or       a5, a1
                  ori        t5, t2, 999
                  sltu       t2, s1, t1
                  c.nop
                  c.slli     t4, 28
                  lui        zero, 195546
                  c.addi16sp sp, 16
                  c.add      t1, a1
                  slt        t1, a1, a4
                  div        t3, t1, t5
                  c.slli     t4, 28
                  addi       a7, t2, -784
                  sltu       t2, s1, t1
                  mulhu      tp, s3, a4
                  c.addi16sp sp, 16
                  c.xor      a1, a2
                  remu       s5, s11, t1
                  rem        s0, a3, a2
                  remu       s5, s11, t1
                  c.addi     s1, 6
                  auipc      t6, 688967
                  c.mv       a1, s5
                  sub        s9, s6, s5
                  add        s7, s5, a6
                  sltiu      s6, ra, 913
                  nop
                  srai       s10, s1, 24
                  sub        s9, s6, s5
                  srai       s10, s1, 24
                  addi       a7, t2, -784
                  srli       s8, t6, 19
                  mulh       s11, s1, s9
                  srai       s10, s1, 24
                  c.andi     a5, -1
                  c.li       a7, 27
                  c.nop
                  andi       s8, t1, -26
                  c.addi4spn a4, sp, 288
                  lui        zero, 195546
                  c.xor      a1, a2
                  sll        t3, s7, a3
                  addi       a7, t2, -784
                  slti       tp, t6, 301
                  addi       a7, t2, -784
                  c.addi4spn a4, sp, 288
                  c.xor      a1, a2
                  c.and      a0, s0
                  mulhu      tp, s3, a4
                  c.and      a0, s0
                  sll        t3, s7, a3
                  xor        t4, s3, t3
                  c.addi     s1, 6
                  sltiu      s6, ra, 913
                  lui        zero, 195546
                  or         s0, a2, a0
                  divu       sp, ra, t0
                  add        s7, s5, a6
                  c.xor      a1, a2
                  c.add      t1, a1
                  c.srai     s0, 31
                  c.xor      a1, a2
                  srl        a0, s2, a0
                  xor        t4, s3, t3
                  slti       tp, t6, 301
                  sub        s9, s6, s5
                  slli       s11, gp, 14
                  sltiu      s6, ra, 913
                  slti       tp, t6, 301
                  sltiu      s6, ra, 913
                  remu       s5, s11, t1
                  sub        s9, s6, s5
                  div        t3, t1, t5
                  c.srli     a0, 25
                  c.nop
                  c.srli     a0, 25
                  nop
                  xori       a4, t0, 974
                  xor        t4, s3, t3
                  c.addi     s1, 6
                  sltiu      s6, ra, 913
                  sltiu      s6, ra, 913
                  slti       tp, t6, 301
                  c.nop
                  c.or       a5, a1
                  nop
                  auipc      t6, 688967
                  sltiu      s6, ra, 913
                  auipc      t6, 688967
                  add        s7, s5, a6
                  nop
                  c.andi     a5, -1
                  c.add      t1, a1
                  xor        t4, s3, t3
                  slt        t1, a1, a4
                  slli       s11, gp, 14
                  c.srai     s0, 31
                  slt        t1, a1, a4
                  c.addi     s1, 6
                  addi       a7, t2, -784
                  rem        s0, a3, a2
                  c.sub      s1, a4
                  srli       s8, t6, 19
                  c.add      t1, a1
                  addi       a7, t2, -784
                  c.slli     t4, 28
                  c.addi16sp sp, 16
                  c.or       a5, a1
                  c.nop
                  andi       s8, t1, -26
                  xori       a4, t0, 974
                  c.lui      a0, 24
                  andi       s8, t1, -26
                  c.addi16sp sp, 16
                  c.add      t1, a1
                  c.slli     t4, 28
                  addi       a7, t2, -784
                  sltiu      s6, ra, 913
                  slti       tp, t6, 301
                  xori       a4, t0, 974
                  addi       a7, t2, -784
                  srl        a0, s2, a0
                  auipc      t6, 688967
                  lui        zero, 195546
                  c.srli     a0, 25
                  sll        t3, s7, a3
                  sltu       t2, s1, t1
                  c.sub      s1, a4
                  addi       a7, t2, -784
                  c.andi     a5, -1
                  slt        t1, a1, a4
                  c.andi     a5, -1
                  c.or       a5, a1
                  addi       a7, t2, -784
                  c.sub      s1, a4
                  slt        t1, a1, a4
                  andi       s8, t1, -26
                  c.slli     t4, 28
                  c.li       a7, 27
                  c.sub      s1, a4
                  or         s0, a2, a0
                  auipc      t6, 688967
                  c.srai     s0, 31
                  c.srai     s0, 31
                  c.add      t1, a1
                  divu       sp, ra, t0
                  c.slli     t4, 28
                  c.slli     t4, 28
                  c.or       a5, a1
                  lui        zero, 195546
                  lui        zero, 195546
                  auipc      t6, 688967
                  auipc      t6, 688967
                  sra        s1, t3, s1
                  c.lui      a0, 24
                  rem        s0, a3, a2
                  c.slli     t4, 28
                  c.nop
                  sub        s9, s6, s5
                  addi       a7, t2, -784
                  slti       tp, t6, 301
                  mulh       s11, s1, s9
                  c.mv       a1, s5
                  c.slli     t4, 28
                  xori       a4, t0, 974
                  sra        s1, t3, s1
                  sll        t3, s7, a3
                  c.andi     a5, -1
                  mulhu      tp, s3, a4
                  and        a1, t3, a6
                  c.li       a7, 27
                  c.li       a7, 27
                  andi       s8, t1, -26
                  slli       s11, gp, 14
                  ori        t5, t2, 999
                  mul        sp, s9, s11
                  c.xor      a1, a2
                  sltiu      s6, ra, 913
                  addi       a7, t2, -784
                  c.or       a5, a1
                  c.or       a5, a1
                  nop
                  c.addi16sp sp, 16
                  srli       s8, t6, 19
                  or         s0, a2, a0
                  div        t3, t1, t5
                  addi       a7, t2, -784
                  srli       s8, t6, 19
                  c.srli     a0, 25
                  andi       s8, t1, -26
                  rem        s0, a3, a2
                  c.and      a0, s0
                  c.li       a7, 27
                  mulhu      tp, s3, a4
                  slti       tp, t6, 301
                  div        t3, t1, t5
                  div        t3, t1, t5
                  sub        s9, s6, s5
                  c.add      t1, a1
                  c.mv       a1, s5
                  rem        s0, a3, a2
                  c.lui      a0, 24
                  xori       a4, t0, 974
                  slli       s11, gp, 14
                  c.addi16sp sp, 16
                  c.xor      a1, a2
                  or         s0, a2, a0
                  sll        t3, s7, a3
                  ori        t5, t2, 999
                  sra        s1, t3, s1
                  c.addi16sp sp, 16
                  slti       tp, t6, 301
                  xori       a4, t0, 974
                  divu       sp, ra, t0
                  c.lui      a0, 24
                  sltiu      s6, ra, 913
                  mulhsu     gp, a1, s1
                  add        s7, s5, a6
                  c.nop
                  c.srli     a0, 25
                  mulh       s11, s1, s9
                  and        a1, t3, a6
                  add        s7, s5, a6
                  c.srai     s0, 31
                  remu       s5, s11, t1
                  sll        t3, s7, a3
                  c.mv       a1, s5
                  c.and      a0, s0
                  c.andi     a5, -1
                  c.addi     s1, 6
                  c.addi     s1, 6
                  c.add      t1, a1
                  ori        t5, t2, 999
                  srl        a0, s2, a0
                  srl        a0, s2, a0
                  srli       s8, t6, 19
                  ori        t5, t2, 999
                  c.or       a5, a1
                  or         s0, a2, a0
                  c.xor      a1, a2
                  and        a1, t3, a6
                  remu       s5, s11, t1
                  ori        t5, t2, 999
                  srai       s10, s1, 24
                  mulhsu     gp, a1, s1
                  auipc      t6, 688967
                  c.mv       a1, s5
                  srai       s10, s1, 24
                  mulhsu     gp, a1, s1
                  addi       a7, t2, -784
                  or         s0, a2, a0
                  sltu       t2, s1, t1
                  c.or       a5, a1
                  c.srli     a0, 25
                  sltu       t2, s1, t1
                  c.srli     a0, 25
                  sltiu      s6, ra, 913
                  c.or       a5, a1
                  c.li       a7, 27
                  srl        a0, s2, a0
                  ori        t5, t2, 999
                  mulhu      tp, s3, a4
                  c.addi16sp sp, 16
                  c.srli     a0, 25
                  or         s0, a2, a0
                  or         s0, a2, a0
                  slt        t1, a1, a4
                  c.mv       a1, s5
                  c.nop
                  and        a1, t3, a6
                  slli       s11, gp, 14
                  andi       s8, t1, -26
                  div        t3, t1, t5
                  nop
                  c.andi     a5, -1
                  addi       a7, t2, -784
                  c.or       a5, a1
                  andi       s8, t1, -26
                  c.lui      a0, 24
                  slli       s11, gp, 14
                  lui        zero, 195546
                  or         s0, a2, a0
                  divu       sp, ra, t0
                  c.or       a5, a1
                  slli       s11, gp, 14
                  c.addi4spn a4, sp, 288
                  divu       sp, ra, t0
                  slti       tp, t6, 301
                  mulhu      tp, s3, a4
                  c.srli     a0, 25
                  slt        t1, a1, a4
                  remu       s5, s11, t1
                  c.addi     s1, 6
                  mul        sp, s9, s11
                  divu       sp, ra, t0
                  and        a1, t3, a6
                  c.addi16sp sp, 16
                  c.addi16sp sp, 16
                  lui        zero, 195546
                  sra        s1, t3, s1
                  c.lui      a0, 24
                  c.and      a0, s0
                  c.andi     a5, -1
                  c.addi4spn a4, sp, 288
                  sltu       t2, s1, t1
                  or         s0, a2, a0
                  srli       s8, t6, 19
                  c.mv       a1, s5
                  srai       s10, s1, 24
                  c.nop
                  slti       tp, t6, 301
                  slt        t1, a1, a4
                  sll        t3, s7, a3
                  c.lui      a0, 24
                  or         s0, a2, a0
                  c.li       a7, 27
                  c.nop
                  c.add      t1, a1
                  c.and      a0, s0
                  sub        s9, s6, s5
                  xori       a4, t0, 974
                  c.li       a7, 27
                  mulh       s11, s1, s9
                  div        t3, t1, t5
                  sra        s1, t3, s1
                  andi       s8, t1, -26
                  mul        sp, s9, s11
                  c.and      a0, s0
                  lui        zero, 195546
                  c.andi     a5, -1
                  c.addi4spn a4, sp, 288
                  auipc      t6, 688967
                  c.and      a0, s0
                  c.addi4spn a4, sp, 288
                  sub        s9, s6, s5
                  c.slli     t4, 28
                  mulhu      tp, s3, a4
                  auipc      t6, 688967
                  mulh       s11, s1, s9
                  or         s0, a2, a0
                  c.addi4spn a4, sp, 288
                  c.lui      a0, 24
                  divu       sp, ra, t0
                  and        a1, t3, a6
                  andi       s8, t1, -26
                  xor        t4, s3, t3
                  c.addi4spn a4, sp, 288
                  add        s7, s5, a6
                  c.addi16sp sp, 16
                  srai       s10, s1, 24
                  c.sub      s1, a4
                  slti       tp, t6, 301
                  xor        t4, s3, t3
                  c.addi     s1, 6
                  remu       s5, s11, t1
                  slt        t1, a1, a4
                  divu       sp, ra, t0
                  div        t3, t1, t5
                  lui        zero, 195546
                  c.lui      a0, 24
                  nop
                  c.xor      a1, a2
                  c.addi4spn a4, sp, 288
                  c.add      t1, a1
                  addi       a7, t2, -784
                  or         s0, a2, a0
                  c.xor      a1, a2
                  c.xor      a1, a2
                  mul        sp, s9, s11
                  c.add      t1, a1
                  c.nop
                  c.xor      a1, a2
                  div        t3, t1, t5
                  c.or       a5, a1
                  divu       sp, ra, t0
                  ori        t5, t2, 999
                  c.srai     s0, 31
                  c.addi     s1, 6
                  mul        sp, s9, s11
                  divu       sp, ra, t0
                  c.addi     s1, 6
                  mul        sp, s9, s11
                  sll        t3, s7, a3
                  andi       s8, t1, -26
                  ori        t5, t2, 999
                  slti       tp, t6, 301
                  mul        sp, s9, s11
                  slti       tp, t6, 301
                  slti       tp, t6, 301
                  addi       a7, t2, -784
                  xor        t4, s3, t3
                  divu       sp, ra, t0
                  or         s0, a2, a0
                  rem        s0, a3, a2
                  c.andi     a5, -1
                  andi       s8, t1, -26
                  c.srai     s0, 31
                  nop
                  sll        t3, s7, a3
                  sltiu      s6, ra, 913
                  srli       s8, t6, 19
                  sll        t3, s7, a3
                  c.srli     a0, 25
                  c.and      a0, s0
                  lui        zero, 195546
                  c.slli     t4, 28
                  c.addi16sp sp, 16
                  c.addi4spn a4, sp, 288
                  and        a1, t3, a6
                  c.srai     s0, 31
                  ori        t5, t2, 999
                  srai       s10, s1, 24
                  srli       s8, t6, 19
                  addi       a7, t2, -784
                  or         s0, a2, a0
                  nop
                  mul        sp, s9, s11
                  c.and      a0, s0
                  c.or       a5, a1
                  c.slli     t4, 28
                  mul        sp, s9, s11
                  xor        t4, s3, t3
                  or         s0, a2, a0
                  sltiu      s6, ra, 913
                  c.add      t1, a1
                  c.addi     s1, 6
                  srai       s10, s1, 24
                  c.li       a7, 27
                  c.srai     s0, 31
                  sltu       t2, s1, t1
                  srl        a0, s2, a0
                  andi       s8, t1, -26
                  c.slli     t4, 28
                  c.nop
                  srai       s10, s1, 24
                  c.mv       a1, s5
                  divu       sp, ra, t0
                  srai       s10, s1, 24
                  c.srli     a0, 25
                  c.srai     s0, 31
                  mulhsu     gp, a1, s1
                  sra        s1, t3, s1
                  c.nop
                  slt        t1, a1, a4
                  c.sub      s1, a4
                  c.or       a5, a1
                  or         s0, a2, a0
                  ori        t5, t2, 999
                  slli       s11, gp, 14
                  add        s7, s5, a6
                  div        t3, t1, t5
                  slt        t1, a1, a4
                  xor        t4, s3, t3
                  slt        t1, a1, a4
                  ori        t5, t2, 999
                  slt        t1, a1, a4
                  c.sub      s1, a4
                  c.slli     t4, 28
                  addi       a7, t2, -784
                  mulhu      tp, s3, a4
                  sub        s9, s6, s5
                  mulhsu     gp, a1, s1
                  sll        t3, s7, a3
                  c.li       a7, 27
                  slt        t1, a1, a4
                  c.srli     a0, 25
                  c.xor      a1, a2
                  xori       a4, t0, 974
                  add        s7, s5, a6
                  remu       s5, s11, t1
                  c.slli     t4, 28
                  c.and      a0, s0
                  c.sub      s1, a4
                  nop
                  add        s7, s5, a6
                  slt        t1, a1, a4
                  mulh       s11, s1, s9
                  andi       s8, t1, -26
                  mulhu      tp, s3, a4
                  c.add      t1, a1
                  mulhu      tp, s3, a4
                  slt        t1, a1, a4
                  mulh       s11, s1, s9
                  addi       a7, t2, -784
                  sra        s1, t3, s1
                  sub        s9, s6, s5
                  sll        t3, s7, a3
                  mulhsu     gp, a1, s1
                  mul        sp, s9, s11
                  xori       a4, t0, 974
                  remu       s5, s11, t1
                  lui        zero, 195546
                  srli       s8, t6, 19
                  c.or       a5, a1
                  c.andi     a5, -1
                  c.addi4spn a4, sp, 288
                  c.slli     t4, 28
                  slt        t1, a1, a4
                  sltu       t2, s1, t1
                  c.nop
                  xori       a4, t0, 974
                  c.sub      s1, a4
                  c.addi     s1, 6
                  mulhsu     gp, a1, s1
                  c.nop
                  lui        zero, 195546
                  c.lui      a0, 24
                  xori       a4, t0, 974
                  or         s0, a2, a0
                  div        t3, t1, t5
                  c.addi     s1, 6
                  c.add      t1, a1
                  c.slli     t4, 28
                  mulhu      tp, s3, a4
                  remu       s5, s11, t1
                  andi       s8, t1, -26
                  div        t3, t1, t5
                  andi       s8, t1, -26
                  sltu       t2, s1, t1
                  sub        s9, s6, s5
                  c.sub      s1, a4
                  or         s0, a2, a0
                  c.nop
                  andi       s8, t1, -26
                  slti       tp, t6, 301
                  lui        zero, 195546
                  sltiu      s6, ra, 913
                  mulhu      tp, s3, a4
                  c.addi4spn a4, sp, 288
                  div        t3, t1, t5
                  sltu       t2, s1, t1
                  xor        t4, s3, t3
                  or         s0, a2, a0
                  andi       s8, t1, -26
                  mulh       s11, s1, s9
                  c.or       a5, a1
                  xori       a4, t0, 974
                  slli       s11, gp, 14
                  slt        t1, a1, a4
                  c.andi     a5, -1
                  c.addi4spn a4, sp, 288
                  srl        a0, s2, a0
                  c.slli     t4, 28
                  rem        s0, a3, a2
                  mul        sp, s9, s11
                  mulhsu     gp, a1, s1
                  nop
                  c.and      a0, s0
                  addi       a7, t2, -784
                  c.mv       a1, s5
                  c.srai     s0, 31
                  div        t3, t1, t5
                  srli       s8, t6, 19
                  sra        s1, t3, s1
                  c.srli     a0, 25
                  mulhsu     gp, a1, s1
                  c.mv       a1, s5
                  c.xor      a1, a2
                  xori       a4, t0, 974
                  remu       s5, s11, t1
                  c.add      t1, a1
                  li         ra, 0xffffffff #start riscv_int_numeric_corner_stream_23
                  li         a5, 0x80000000
                  li         s6, 0xffffffff
                  li         a6, 0x80000000
                  li         a7, 0xffffffff
                  li         t3, 0x0
                  li         a4, 0xaa2a5c0
                  li         t4, 0x80000000
                  li         s5, 0x0
                  li         t0, 0x0
                  sub        a4, t3, a4
                  lui        ra, 195546
                  nop
                  nop
                  add        t0, ra, a7
                  auipc      t4, 688967
                  add        t0, ra, a7
                  nop
                  auipc      t4, 688967
                  mulh       ra, a5, s5
                  nop
                  mulhsu     a5, ra, ra
                  sub        a4, t3, a4
                  nop
                  div        a6, a6, a4
                  mul        a4, t4, t3
                  rem        a7, a5, a4
                  div        a6, a6, a4
                  div        a6, a6, a4
                  sub        a4, t3, a4
                  mulhsu     a5, ra, ra
                  nop
                  mulhu      ra, a5, t0 #end riscv_int_numeric_corner_stream_23
                  c.nop
                  mulhu      tp, s3, a4
                  sll        t3, s7, a3
                  sltu       t2, s1, t1
                  c.mv       a1, s5
                  c.srai     s0, 31
                  c.sub      s1, a4
                  c.add      t1, a1
                  xori       a4, t0, 974
                  xor        t4, s3, t3
                  sltiu      s6, ra, 913
                  sub        s9, s6, s5
                  div        t3, t1, t5
                  sll        t3, s7, a3
                  c.lui      a0, 24
                  c.li       a7, 27
                  c.andi     a5, -1
                  srl        a0, s2, a0
                  auipc      t6, 688967
                  divu       sp, ra, t0
                  addi       a7, t2, -784
                  mulhu      tp, s3, a4
                  c.nop
                  addi       a7, t2, -784
                  slti       tp, t6, 301
                  remu       s5, s11, t1
                  c.or       a5, a1
                  c.add      t1, a1
                  c.add      t1, a1
                  c.xor      a1, a2
                  mulh       s11, s1, s9
                  auipc      t6, 688967
                  div        t3, t1, t5
                  and        a1, t3, a6
                  addi       a7, t2, -784
                  slti       tp, t6, 301
                  rem        s0, a3, a2
                  ori        t5, t2, 999
                  c.li       a7, 27
                  sll        t3, s7, a3
                  slt        t1, a1, a4
                  c.lui      a0, 24
                  mulhu      tp, s3, a4
                  sra        s1, t3, s1
                  srai       s10, s1, 24
                  c.add      t1, a1
                  lui        zero, 195546
                  sll        t3, s7, a3
                  slti       tp, t6, 301
                  c.or       a5, a1
                  divu       sp, ra, t0
                  add        s7, s5, a6
                  sll        t3, s7, a3
                  c.addi     s1, 6
                  lui        zero, 195546
                  slli       s11, gp, 14
                  mulh       s11, s1, s9
                  lui        zero, 195546
                  or         s0, a2, a0
                  div        t3, t1, t5
                  mulhu      tp, s3, a4
                  c.and      a0, s0
                  slli       s11, gp, 14
                  c.srai     s0, 31
                  c.addi4spn a4, sp, 288
                  andi       s8, t1, -26
                  divu       sp, ra, t0
                  xori       a4, t0, 974
                  divu       sp, ra, t0
                  sub        s9, s6, s5
                  c.srli     a0, 25
                  c.srli     a0, 25
                  mulhsu     gp, a1, s1
                  auipc      t6, 688967
                  c.li       a7, 27
                  sltu       t2, s1, t1
                  c.mv       a1, s5
                  mulhsu     gp, a1, s1
                  srl        a0, s2, a0
                  rem        s0, a3, a2
                  andi       s8, t1, -26
                  c.addi16sp sp, 16
                  slti       tp, t6, 301
                  auipc      t6, 688967
                  sra        s1, t3, s1
                  c.srai     s0, 31
                  mulhsu     gp, a1, s1
                  div        t3, t1, t5
                  andi       s8, t1, -26
                  sra        s1, t3, s1
                  div        t3, t1, t5
                  sra        s1, t3, s1
                  c.addi4spn a4, sp, 288
                  sltiu      s6, ra, 913
                  div        t3, t1, t5
                  div        t3, t1, t5
                  srai       s10, s1, 24
                  c.addi     s1, 6
                  c.add      t1, a1
                  sltu       t2, s1, t1
                  nop
                  mul        sp, s9, s11
                  or         s0, a2, a0
                  andi       s8, t1, -26
                  remu       s5, s11, t1
                  mulh       s11, s1, s9
                  c.lui      a0, 24
                  c.srli     a0, 25
                  addi       a7, t2, -784
                  add        s7, s5, a6
                  c.or       a5, a1
                  div        t3, t1, t5
                  srai       s10, s1, 24
                  srai       s10, s1, 24
                  and        a1, t3, a6
                  c.addi     s1, 6
                  and        a1, t3, a6
                  rem        s0, a3, a2
                  andi       s8, t1, -26
                  c.addi16sp sp, 16
                  c.xor      a1, a2
                  c.li       a7, 27
                  sub        s9, s6, s5
                  c.slli     t4, 28
                  ori        t5, t2, 999
                  lui        zero, 195546
                  mulhu      tp, s3, a4
                  slti       tp, t6, 301
                  c.li       a7, 27
                  c.srai     s0, 31
                  c.mv       a1, s5
                  sll        t3, s7, a3
                  sltiu      s6, ra, 913
                  slti       tp, t6, 301
                  lui        zero, 195546
                  c.srai     s0, 31
                  div        t3, t1, t5
                  rem        s0, a3, a2
                  mulhsu     gp, a1, s1
                  c.andi     a5, -1
                  c.addi4spn a4, sp, 288
                  divu       sp, ra, t0
                  c.nop
                  c.mv       a1, s5
                  c.lui      a0, 24
                  c.and      a0, s0
                  sll        t3, s7, a3
                  c.add      t1, a1
                  srai       s10, s1, 24
                  c.xor      a1, a2
                  mulhsu     gp, a1, s1
                  srl        a0, s2, a0
                  srli       s8, t6, 19
                  sll        t3, s7, a3
                  slli       s11, gp, 14
                  c.srai     s0, 31
                  c.slli     t4, 28
                  add        s7, s5, a6
                  mulhsu     gp, a1, s1
                  c.or       a5, a1
                  add        s7, s5, a6
                  c.and      a0, s0
                  c.lui      a0, 24
                  sltiu      s6, ra, 913
                  div        t3, t1, t5
                  nop
                  c.nop
                  lui        zero, 195546
                  slt        t1, a1, a4
                  and        a1, t3, a6
                  slti       tp, t6, 301
                  or         s0, a2, a0
                  c.add      t1, a1
                  rem        s0, a3, a2
                  andi       s8, t1, -26
                  andi       s8, t1, -26
                  c.addi     s1, 6
                  mulhsu     gp, a1, s1
                  divu       sp, ra, t0
                  add        s7, s5, a6
                  srai       s10, s1, 24
                  divu       sp, ra, t0
                  sll        t3, s7, a3
                  and        a1, t3, a6
                  c.andi     a5, -1
                  divu       sp, ra, t0
                  remu       s5, s11, t1
                  c.lui      a0, 24
                  srli       s8, t6, 19
                  div        t3, t1, t5
                  c.add      t1, a1
                  c.li       a7, 27
                  div        t3, t1, t5
                  divu       sp, ra, t0
                  slt        t1, a1, a4
                  c.lui      a0, 24
                  c.srli     a0, 25
                  sub        s9, s6, s5
                  c.mv       a1, s5
                  mul        sp, s9, s11
                  c.srai     s0, 31
                  andi       s8, t1, -26
                  div        t3, t1, t5
                  sltu       t2, s1, t1
                  c.srli     a0, 25
                  auipc      t6, 688967
                  sub        s9, s6, s5
                  sub        s9, s6, s5
                  sll        t3, s7, a3
                  and        a1, t3, a6
                  c.and      a0, s0
                  sltiu      s6, ra, 913
                  ori        t5, t2, 999
                  c.addi4spn a4, sp, 288
                  c.mv       a1, s5
                  srl        a0, s2, a0
                  c.and      a0, s0
                  mul        sp, s9, s11
                  mulh       s11, s1, s9
                  c.and      a0, s0
                  srli       s8, t6, 19
                  c.nop
                  srl        a0, s2, a0
                  and        a1, t3, a6
                  srli       s8, t6, 19
                  c.li       a7, 27
                  remu       s5, s11, t1
                  xori       a4, t0, 974
                  ori        t5, t2, 999
                  c.li       a7, 27
                  c.nop
                  remu       s5, s11, t1
                  c.mv       a1, s5
                  mul        sp, s9, s11
                  c.nop
                  srl        a0, s2, a0
                  xor        t4, s3, t3
                  c.andi     a5, -1
                  c.srli     a0, 25
                  div        t3, t1, t5
                  slti       tp, t6, 301
                  rem        s0, a3, a2
                  c.mv       a1, s5
                  c.li       a7, 27
                  or         s0, a2, a0
                  c.li       a7, 27
                  c.xor      a1, a2
                  mulhu      tp, s3, a4
                  sub        s9, s6, s5
                  sltiu      s6, ra, 913
                  add        s7, s5, a6
                  andi       s8, t1, -26
                  ori        t5, t2, 999
                  c.xor      a1, a2
                  slli       s11, gp, 14
                  c.addi4spn a4, sp, 288
                  rem        s0, a3, a2
                  and        a1, t3, a6
                  add        s7, s5, a6
                  andi       s8, t1, -26
                  sub        s9, s6, s5
                  and        a1, t3, a6
                  mulh       s11, s1, s9
                  xor        t4, s3, t3
                  c.add      t1, a1
                  c.addi16sp sp, 16
                  mul        sp, s9, s11
                  c.addi16sp sp, 16
                  add        s7, s5, a6
                  sltiu      s6, ra, 913
                  sltu       t2, s1, t1
                  remu       s5, s11, t1
                  sll        t3, s7, a3
                  remu       s5, s11, t1
                  c.andi     a5, -1
                  slt        t1, a1, a4
                  lui        zero, 195546
                  rem        s0, a3, a2
                  c.mv       a1, s5
                  mulh       s11, s1, s9
                  c.or       a5, a1
                  c.li       a7, 27
                  nop
                  c.srli     a0, 25
                  or         s0, a2, a0
                  remu       s5, s11, t1
                  lui        zero, 195546
                  sltiu      s6, ra, 913
                  c.srai     s0, 31
                  c.srai     s0, 31
                  c.srai     s0, 31
                  c.slli     t4, 28
                  c.li       a7, 27
                  xor        t4, s3, t3
                  mul        sp, s9, s11
                  c.add      t1, a1
                  mul        sp, s9, s11
                  c.addi4spn a4, sp, 288
                  srli       s8, t6, 19
                  sltiu      s6, ra, 913
                  and        a1, t3, a6
                  div        t3, t1, t5
                  addi       a7, t2, -784
                  xori       a4, t0, 974
                  c.addi     s1, 6
                  divu       sp, ra, t0
                  c.lui      a0, 24
                  c.mv       a1, s5
                  c.lui      a0, 24
                  sra        s1, t3, s1
                  sub        s9, s6, s5
                  c.srli     a0, 25
                  c.li       a7, 27
                  c.add      t1, a1
                  c.addi     s1, 6
                  mulhu      tp, s3, a4
                  srl        a0, s2, a0
                  nop
                  c.add      t1, a1
                  c.srai     s0, 31
                  lui        zero, 195546
                  sra        s1, t3, s1
                  c.xor      a1, a2
                  divu       sp, ra, t0
                  ori        t5, t2, 999
                  nop
                  slli       s11, gp, 14
                  divu       sp, ra, t0
                  c.and      a0, s0
                  ori        t5, t2, 999
                  c.nop
                  c.xor      a1, a2
                  c.mv       a1, s5
                  c.addi16sp sp, 16
                  c.mv       a1, s5
                  xori       a4, t0, 974
                  sub        s9, s6, s5
                  c.add      t1, a1
                  mulhu      tp, s3, a4
                  xori       a4, t0, 974
                  or         s0, a2, a0
                  remu       s5, s11, t1
                  srai       s10, s1, 24
                  slt        t1, a1, a4
                  c.and      a0, s0
                  c.mv       a1, s5
                  sll        t3, s7, a3
                  xori       a4, t0, 974
                  c.srli     a0, 25
                  slti       tp, t6, 301
                  or         s0, a2, a0
                  c.srli     a0, 25
                  c.mv       a1, s5
                  mulh       s11, s1, s9
                  c.addi16sp sp, 16
                  xori       a4, t0, 974
                  sra        s1, t3, s1
                  sub        s9, s6, s5
                  mulh       s11, s1, s9
                  mul        sp, s9, s11
                  c.slli     t4, 28
                  addi       a7, t2, -784
                  c.slli     t4, 28
                  addi       a7, t2, -784
                  c.li       a7, 27
                  c.mv       a1, s5
                  slti       tp, t6, 301
                  slti       tp, t6, 301
                  c.or       a5, a1
                  div        t3, t1, t5
                  add        s7, s5, a6
                  c.sub      s1, a4
                  lui        zero, 195546
                  mul        sp, s9, s11
                  ori        t5, t2, 999
                  c.addi     s1, 6
                  c.nop
                  sll        t3, s7, a3
                  c.sub      s1, a4
                  auipc      t6, 688967
                  c.add      t1, a1
                  c.srai     s0, 31
                  c.add      t1, a1
                  srl        a0, s2, a0
                  slti       tp, t6, 301
                  sltu       t2, s1, t1
                  and        a1, t3, a6
                  srai       s10, s1, 24
                  lui        zero, 195546
                  sra        s1, t3, s1
                  c.addi4spn a4, sp, 288
                  sll        t3, s7, a3
                  srl        a0, s2, a0
                  sra        s1, t3, s1
                  mulhsu     gp, a1, s1
                  mulh       s11, s1, s9
                  c.addi16sp sp, 16
                  mul        sp, s9, s11
                  xor        t4, s3, t3
                  c.and      a0, s0
                  c.mv       a1, s5
                  c.srai     s0, 31
                  c.addi16sp sp, 16
                  c.srli     a0, 25
                  div        t3, t1, t5
                  srai       s10, s1, 24
                  sub        s9, s6, s5
                  srai       s10, s1, 24
                  rem        s0, a3, a2
                  xor        t4, s3, t3
                  mul        sp, s9, s11
                  c.lui      a0, 24
                  and        a1, t3, a6
                  sltiu      s6, ra, 913
                  xori       a4, t0, 974
                  xor        t4, s3, t3
                  sra        s1, t3, s1
                  c.xor      a1, a2
                  c.addi     s1, 6
                  xori       a4, t0, 974
                  c.mv       a1, s5
                  xori       a4, t0, 974
                  sub        s9, s6, s5
                  c.and      a0, s0
                  sra        s1, t3, s1
                  mulh       s11, s1, s9
                  addi       a7, t2, -784
                  slli       s11, gp, 14
                  nop
                  auipc      t6, 688967
                  c.addi4spn a4, sp, 288
                  c.lui      a0, 24
                  c.addi     s1, 6
                  addi       a7, t2, -784
                  lui        zero, 195546
                  addi       a7, t2, -784
                  and        a1, t3, a6
                  or         s0, a2, a0
                  sra        s1, t3, s1
                  slti       tp, t6, 301
                  srl        a0, s2, a0
                  c.sub      s1, a4
                  c.add      t1, a1
                  ori        t5, t2, 999
                  c.addi4spn a4, sp, 288
                  remu       s5, s11, t1
                  slli       s11, gp, 14
                  or         s0, a2, a0
                  andi       s8, t1, -26
                  andi       s8, t1, -26
                  sltiu      s6, ra, 913
                  auipc      t6, 688967
                  rem        s0, a3, a2
                  c.li       a7, 27
                  mulh       s11, s1, s9
                  sra        s1, t3, s1
                  c.xor      a1, a2
                  srl        a0, s2, a0
                  remu       s5, s11, t1
                  add        s7, s5, a6
                  auipc      t6, 688967
                  c.lui      a0, 24
                  c.and      a0, s0
                  slli       s11, gp, 14
                  add        s7, s5, a6
                  c.andi     a5, -1
                  rem        s0, a3, a2
                  srai       s10, s1, 24
                  c.addi4spn a4, sp, 288
                  sll        t3, s7, a3
                  c.addi16sp sp, 16
                  sltu       t2, s1, t1
                  andi       s8, t1, -26
                  c.mv       a1, s5
                  c.lui      a0, 24
                  c.nop
                  c.nop
                  remu       s5, s11, t1
                  addi       a7, t2, -784
                  slt        t1, a1, a4
                  or         s0, a2, a0
                  c.sub      s1, a4
                  mulhsu     gp, a1, s1
                  c.andi     a5, -1
                  c.addi     s1, 6
                  slt        t1, a1, a4
                  mulh       s11, s1, s9
                  ori        t5, t2, 999
                  mulhu      tp, s3, a4
                  c.sub      s1, a4
                  c.srai     s0, 31
                  sub        s9, s6, s5
                  lui        zero, 195546
                  c.addi16sp sp, 16
                  xori       a4, t0, 974
                  c.lui      a0, 24
                  lui        zero, 195546
                  lui        zero, 195546
                  addi       a7, t2, -784
                  srli       s8, t6, 19
                  nop
                  andi       s8, t1, -26
                  c.andi     a5, -1
                  c.lui      a0, 24
                  mulhsu     gp, a1, s1
                  srai       s10, s1, 24
                  sll        t3, s7, a3
                  remu       s5, s11, t1
                  divu       sp, ra, t0
                  c.add      t1, a1
                  remu       s5, s11, t1
                  c.add      t1, a1
                  sub        s9, s6, s5
                  c.sub      s1, a4
                  c.li       a7, 27
                  divu       sp, ra, t0
                  lui        zero, 195546
                  c.mv       a1, s5
                  slli       s11, gp, 14
                  c.addi4spn a4, sp, 288
                  divu       sp, ra, t0
                  sll        t3, s7, a3
                  xori       a4, t0, 974
                  remu       s5, s11, t1
                  c.add      t1, a1
                  lui        zero, 195546
                  mulhu      tp, s3, a4
                  c.addi     s1, 6
                  add        s7, s5, a6
                  ori        t5, t2, 999
                  c.or       a5, a1
                  mulhsu     gp, a1, s1
                  xor        t4, s3, t3
                  slt        t1, a1, a4
                  c.xor      a1, a2
                  c.or       a5, a1
                  sra        s1, t3, s1
                  auipc      t6, 688967
                  c.lui      a0, 24
                  c.add      t1, a1
                  c.and      a0, s0
                  sub        s9, s6, s5
                  c.mv       a1, s5
                  div        t3, t1, t5
                  or         s0, a2, a0
                  divu       sp, ra, t0
                  c.andi     a5, -1
                  slt        t1, a1, a4
                  xor        t4, s3, t3
                  xori       a4, t0, 974
                  srli       s8, t6, 19
                  c.slli     t4, 28
                  mulhu      tp, s3, a4
                  ori        t5, t2, 999
                  srli       s8, t6, 19
                  slli       s11, gp, 14
                  c.xor      a1, a2
                  c.and      a0, s0
                  add        s7, s5, a6
                  and        a1, t3, a6
                  mulhu      tp, s3, a4
                  srai       s10, s1, 24
                  slti       tp, t6, 301
                  c.andi     a5, -1
                  mulh       s11, s1, s9
                  c.srai     s0, 31
                  slti       tp, t6, 301
                  srl        a0, s2, a0
                  slli       s11, gp, 14
                  c.lui      a0, 24
                  srai       s10, s1, 24
                  c.srai     s0, 31
                  xor        t4, s3, t3
                  div        t3, t1, t5
                  rem        s0, a3, a2
                  mulhsu     gp, a1, s1
                  div        t3, t1, t5
                  c.and      a0, s0
                  rem        s0, a3, a2
                  andi       s8, t1, -26
                  c.and      a0, s0
                  c.nop
                  div        t3, t1, t5
                  div        t3, t1, t5
                  div        t3, t1, t5
                  c.andi     a5, -1
                  c.addi     s1, 6
                  slti       tp, t6, 301
                  mulhu      tp, s3, a4
                  xori       a4, t0, 974
                  add        s7, s5, a6
                  slti       tp, t6, 301
                  sltu       t2, s1, t1
                  c.li       a7, 27
                  sra        s1, t3, s1
                  c.add      t1, a1
                  c.addi4spn a4, sp, 288
                  div        t3, t1, t5
                  c.xor      a1, a2
                  c.lui      a0, 24
                  c.slli     t4, 28
                  and        a1, t3, a6
                  slt        t1, a1, a4
                  sll        t3, s7, a3
                  auipc      t6, 688967
                  sll        t3, s7, a3
                  c.sub      s1, a4
                  ori        t5, t2, 999
                  nop
                  mulh       s11, s1, s9
                  c.addi     s1, 6
                  nop
                  c.nop
                  sltiu      s6, ra, 913
                  addi       a7, t2, -784
                  or         s0, a2, a0
                  or         s0, a2, a0
                  c.li       a7, 27
                  srl        a0, s2, a0
                  mulhsu     gp, a1, s1
                  mulhsu     gp, a1, s1
                  xor        t4, s3, t3
                  c.li       a7, 27
                  c.addi     s1, 6
                  nop
                  slti       tp, t6, 301
                  c.addi16sp sp, 16
                  nop
                  srli       s8, t6, 19
                  nop
                  lui        zero, 195546
                  divu       sp, ra, t0
                  addi       a7, t2, -784
                  slti       tp, t6, 301
                  c.slli     t4, 28
                  c.addi16sp sp, 16
                  c.slli     t4, 28
                  sltiu      s6, ra, 913
                  or         s0, a2, a0
                  c.mv       a1, s5
                  ori        t5, t2, 999
                  addi       a7, t2, -784
                  remu       s5, s11, t1
                  c.addi     s1, 6
                  c.add      t1, a1
                  c.or       a5, a1
                  c.addi4spn a4, sp, 288
                  c.addi     s1, 6
                  c.addi16sp sp, 16
                  c.addi16sp sp, 16
                  mul        sp, s9, s11
                  sltiu      s6, ra, 913
                  ori        t5, t2, 999
                  sra        s1, t3, s1
                  c.lui      a0, 24
                  slt        t1, a1, a4
                  mulh       s11, s1, s9
                  andi       s8, t1, -26
                  slt        t1, a1, a4
                  xori       a4, t0, 974
                  mulhu      tp, s3, a4
                  add        s7, s5, a6
                  c.li       a7, 27
                  srl        a0, s2, a0
                  c.and      a0, s0
                  c.slli     t4, 28
                  add        s7, s5, a6
                  c.or       a5, a1
                  c.andi     a5, -1
                  remu       s5, s11, t1
                  srl        a0, s2, a0
                  c.addi4spn a4, sp, 288
                  c.li       a7, 27
                  srli       s8, t6, 19
                  c.xor      a1, a2
                  addi       a7, t2, -784
                  c.lui      a0, 24
                  div        t3, t1, t5
                  lui        zero, 195546
                  c.lui      a0, 24
                  c.xor      a1, a2
                  xor        t4, s3, t3
                  c.lui      a0, 24
                  c.lui      a0, 24
                  sra        s1, t3, s1
                  c.sub      s1, a4
                  sltiu      s6, ra, 913
                  slli       s11, gp, 14
                  c.nop
                  div        t3, t1, t5
                  andi       s8, t1, -26
                  remu       s5, s11, t1
                  c.srai     s0, 31
                  sltiu      s6, ra, 913
                  slti       tp, t6, 301
                  sltiu      s6, ra, 913
                  sub        s9, s6, s5
                  sub        s9, s6, s5
                  c.nop
                  c.mv       a1, s5
                  c.addi     s1, 6
                  srl        a0, s2, a0
                  sltu       t2, s1, t1
                  xori       a4, t0, 974
                  auipc      t6, 688967
                  slti       tp, t6, 301
                  or         s0, a2, a0
                  sra        s1, t3, s1
                  srli       s8, t6, 19
                  div        t3, t1, t5
                  slt        t1, a1, a4
                  c.addi4spn a4, sp, 288
                  auipc      t6, 688967
                  andi       s8, t1, -26
                  srli       s8, t6, 19
                  sll        t3, s7, a3
                  remu       s5, s11, t1
                  nop
                  nop
                  c.or       a5, a1
                  and        a1, t3, a6
                  or         s0, a2, a0
                  c.addi     s1, 6
                  addi       a7, t2, -784
                  c.lui      a0, 24
                  c.srli     a0, 25
                  sltu       t2, s1, t1
                  srl        a0, s2, a0
                  sltiu      s6, ra, 913
                  sra        s1, t3, s1
                  c.sub      s1, a4
                  mulhsu     gp, a1, s1
                  xori       a4, t0, 974
                  c.nop
                  xor        t4, s3, t3
                  andi       s8, t1, -26
                  c.and      a0, s0
                  c.add      t1, a1
                  sll        t3, s7, a3
                  slti       tp, t6, 301
                  rem        s0, a3, a2
                  mulhsu     gp, a1, s1
                  slt        t1, a1, a4
                  c.srai     s0, 31
                  sll        t3, s7, a3
                  auipc      t6, 688967
                  c.add      t1, a1
                  lui        zero, 195546
                  addi       a7, t2, -784
                  slli       s11, gp, 14
                  xor        t4, s3, t3
                  c.lui      a0, 24
                  sra        s1, t3, s1
                  c.add      t1, a1
                  mulhsu     gp, a1, s1
                  c.nop
                  xor        t4, s3, t3
                  xori       a4, t0, 974
                  srl        a0, s2, a0
                  c.li       a7, 27
                  sltiu      s6, ra, 913
                  or         s0, a2, a0
                  c.or       a5, a1
                  mulh       s11, s1, s9
                  andi       s8, t1, -26
                  rem        s0, a3, a2
                  lui        zero, 195546
                  c.slli     t4, 28
                  sll        t3, s7, a3
                  c.srai     s0, 31
                  srli       s8, t6, 19
                  c.slli     t4, 28
                  c.addi16sp sp, 16
                  slti       tp, t6, 301
                  c.addi     s1, 6
                  c.srli     a0, 25
                  mulhsu     gp, a1, s1
                  sra        s1, t3, s1
                  c.lui      a0, 24
                  lui        zero, 195546
                  c.srai     s0, 31
                  auipc      t6, 688967
                  xori       a4, t0, 974
                  auipc      t6, 688967
                  c.add      t1, a1
                  auipc      t6, 688967
                  srli       s8, t6, 19
                  addi       a7, t2, -784
                  mulh       s11, s1, s9
                  auipc      t6, 688967
                  slt        t1, a1, a4
                  slt        t1, a1, a4
                  mulhsu     gp, a1, s1
                  c.andi     a5, -1
                  c.lui      a0, 24
                  c.andi     a5, -1
                  c.sub      s1, a4
                  addi       a7, t2, -784
                  nop
                  sll        t3, s7, a3
                  add        s7, s5, a6
                  sltiu      s6, ra, 913
                  c.addi4spn a4, sp, 288
                  c.or       a5, a1
                  addi       a7, t2, -784
                  andi       s8, t1, -26
                  c.li       a7, 27
                  andi       s8, t1, -26
                  c.mv       a1, s5
                  srl        a0, s2, a0
                  c.slli     t4, 28
                  srli       s8, t6, 19
                  sra        s1, t3, s1
                  c.and      a0, s0
                  sltu       t2, s1, t1
                  c.xor      a1, a2
                  sra        s1, t3, s1
                  div        t3, t1, t5
                  c.addi     s1, 6
                  c.andi     a5, -1
                  auipc      t6, 688967
                  divu       sp, ra, t0
                  and        a1, t3, a6
                  srli       s8, t6, 19
                  mulhu      tp, s3, a4
                  c.addi4spn a4, sp, 288
                  mulhsu     gp, a1, s1
                  xor        t4, s3, t3
                  c.add      t1, a1
                  add        s7, s5, a6
                  srli       s8, t6, 19
                  auipc      t6, 688967
                  auipc      t6, 688967
                  srl        a0, s2, a0
                  c.add      t1, a1
                  slti       tp, t6, 301
                  sltu       t2, s1, t1
                  andi       s8, t1, -26
                  c.li       a7, 27
                  or         s0, a2, a0
                  srli       s8, t6, 19
                  xori       a4, t0, 974
                  rem        s0, a3, a2
                  c.or       a5, a1
                  srai       s10, s1, 24
                  c.srli     a0, 25
                  srai       s10, s1, 24
                  sra        s1, t3, s1
                  andi       s8, t1, -26
                  srai       s10, s1, 24
                  mulhsu     gp, a1, s1
                  sltiu      s6, ra, 913
                  c.srli     a0, 25
                  c.andi     a5, -1
                  c.or       a5, a1
                  slt        t1, a1, a4
                  xori       a4, t0, 974
                  slti       tp, t6, 301
                  sltu       t2, s1, t1
                  c.addi16sp sp, 16
                  nop
                  xor        t4, s3, t3
                  c.addi16sp sp, 16
                  rem        s0, a3, a2
                  sltu       t2, s1, t1
                  c.nop
                  xor        t4, s3, t3
                  mulhu      tp, s3, a4
                  ori        t5, t2, 999
                  c.or       a5, a1
                  c.addi     s1, 6
                  c.addi4spn a4, sp, 288
                  c.addi     s1, 6
                  c.srli     a0, 25
                  sll        t3, s7, a3
                  addi       a7, t2, -784
                  c.or       a5, a1
                  sll        t3, s7, a3
                  mulhu      tp, s3, a4
                  auipc      t6, 688967
                  mulhsu     gp, a1, s1
                  rem        s0, a3, a2
                  nop
                  mulh       s11, s1, s9
                  srl        a0, s2, a0
                  mulhu      tp, s3, a4
                  mulh       s11, s1, s9
                  mul        sp, s9, s11
                  div        t3, t1, t5
                  srl        a0, s2, a0
                  srli       s8, t6, 19
                  andi       s8, t1, -26
                  c.addi16sp sp, 16
                  sub        s9, s6, s5
                  c.mv       a1, s5
                  c.addi4spn a4, sp, 288
                  c.sub      s1, a4
                  ori        t5, t2, 999
                  divu       sp, ra, t0
                  c.addi4spn a4, sp, 288
                  lui        zero, 195546
                  divu       sp, ra, t0
                  slli       s11, gp, 14
                  andi       s8, t1, -26
                  mul        sp, s9, s11
                  c.addi4spn a4, sp, 288
                  mul        sp, s9, s11
                  c.li       a7, 27
                  c.addi16sp sp, 16
                  srli       s8, t6, 19
                  auipc      t6, 688967
                  srai       s10, s1, 24
                  srl        a0, s2, a0
                  slli       s11, gp, 14
                  mulh       s11, s1, s9
                  lui        zero, 195546
                  srl        a0, s2, a0
                  sltu       t2, s1, t1
                  div        t3, t1, t5
                  srli       s8, t6, 19
                  sltiu      s6, ra, 913
                  sltu       t2, s1, t1
                  mulhsu     gp, a1, s1
                  c.li       a7, 27
                  sltiu      s6, ra, 913
                  c.or       a5, a1
                  c.or       a5, a1
                  andi       s8, t1, -26
                  c.addi     s1, 6
                  c.srai     s0, 31
                  divu       sp, ra, t0
                  add        s7, s5, a6
                  slti       tp, t6, 301
                  or         s0, a2, a0
                  divu       sp, ra, t0
                  remu       s5, s11, t1
                  c.and      a0, s0
                  c.or       a5, a1
                  c.srli     a0, 25
                  ori        t5, t2, 999
                  slli       s11, gp, 14
                  c.srli     a0, 25
                  c.lui      a0, 24
                  xori       a4, t0, 974
                  slt        t1, a1, a4
                  mulhsu     gp, a1, s1
                  and        a1, t3, a6
                  srl        a0, s2, a0
                  c.sub      s1, a4
                  andi       s8, t1, -26
                  c.addi16sp sp, 16
                  c.nop
                  c.lui      a0, 24
                  ori        t5, t2, 999
                  mulhu      tp, s3, a4
                  mul        sp, s9, s11
                  ori        t5, t2, 999
                  c.add      t1, a1
                  srli       s8, t6, 19
                  remu       s5, s11, t1
                  c.sub      s1, a4
                  slt        t1, a1, a4
                  or         s0, a2, a0
                  c.srai     s0, 31
                  lui        zero, 195546
                  slt        t1, a1, a4
                  srli       s8, t6, 19
                  sll        t3, s7, a3
                  nop
                  add        s7, s5, a6
                  c.sub      s1, a4
                  slt        t1, a1, a4
                  sub        s9, s6, s5
                  slli       s11, gp, 14
                  add        s7, s5, a6
                  c.sub      s1, a4
                  mulhu      tp, s3, a4
                  div        t3, t1, t5
                  remu       s5, s11, t1
                  c.mv       a1, s5
                  c.addi4spn a4, sp, 288
                  div        t3, t1, t5
                  c.addi4spn a4, sp, 288
                  mulhu      tp, s3, a4
                  c.mv       a1, s5
                  mulhsu     gp, a1, s1
                  addi       a7, t2, -784
                  slli       s11, gp, 14
                  rem        s0, a3, a2
                  xor        t4, s3, t3
                  ori        t5, t2, 999
                  mulhsu     gp, a1, s1
                  c.srai     s0, 31
                  c.and      a0, s0
                  sra        s1, t3, s1
                  xori       a4, t0, 974
                  add        s7, s5, a6
                  c.and      a0, s0
                  ori        t5, t2, 999
                  sra        s1, t3, s1
                  srai       s10, s1, 24
                  mul        sp, s9, s11
                  mulhsu     gp, a1, s1
                  mulhsu     gp, a1, s1
                  slti       tp, t6, 301
                  c.addi4spn a4, sp, 288
                  remu       s5, s11, t1
                  or         s0, a2, a0
                  srai       s10, s1, 24
                  slti       tp, t6, 301
                  sltu       t2, s1, t1
                  remu       s5, s11, t1
                  sub        s9, s6, s5
                  c.or       a5, a1
                  mulhsu     gp, a1, s1
                  sub        s9, s6, s5
                  sltiu      s6, ra, 913
                  slt        t1, a1, a4
                  mul        sp, s9, s11
                  addi       a7, t2, -784
                  c.srli     a0, 25
                  srai       s10, s1, 24
                  c.addi     s1, 6
                  mulhu      tp, s3, a4
                  div        t3, t1, t5
                  srl        a0, s2, a0
                  sltiu      s6, ra, 913
                  sub        s9, s6, s5
                  c.addi16sp sp, 16
                  add        s7, s5, a6
                  add        s7, s5, a6
                  sll        t3, s7, a3
                  xor        t4, s3, t3
                  add        s7, s5, a6
                  and        a1, t3, a6
                  c.lui      a0, 24
                  c.li       a7, 27
                  div        t3, t1, t5
                  divu       sp, ra, t0
                  c.addi4spn a4, sp, 288
                  slt        t1, a1, a4
                  auipc      t6, 688967
                  slti       tp, t6, 301
                  srli       s8, t6, 19
                  nop
                  ori        t5, t2, 999
                  c.nop
                  sub        s9, s6, s5
                  slt        t1, a1, a4
                  c.or       a5, a1
                  xori       a4, t0, 974
                  mulhu      tp, s3, a4
                  sltiu      s6, ra, 913
                  c.mv       a1, s5
                  auipc      t6, 688967
                  sltu       t2, s1, t1
                  slli       s11, gp, 14
                  c.slli     t4, 28
                  c.and      a0, s0
                  c.sub      s1, a4
                  sltu       t2, s1, t1
                  c.nop
                  mul        sp, s9, s11
                  c.slli     t4, 28
                  divu       sp, ra, t0
                  slli       s11, gp, 14
                  sub        s9, s6, s5
                  xor        t4, s3, t3
                  c.sub      s1, a4
                  slti       tp, t6, 301
                  sub        s9, s6, s5
                  sltiu      s6, ra, 913
                  srl        a0, s2, a0
                  srli       s8, t6, 19
                  remu       s5, s11, t1
                  c.srai     s0, 31
                  srli       s8, t6, 19
                  addi       a7, t2, -784
                  c.and      a0, s0
                  slt        t1, a1, a4
                  srl        a0, s2, a0
                  mulhsu     gp, a1, s1
                  c.addi16sp sp, 16
                  xor        t4, s3, t3
                  sltiu      s6, ra, 913
                  sub        s9, s6, s5
                  c.add      t1, a1
                  c.srli     a0, 25
                  ori        t5, t2, 999
                  mul        sp, s9, s11
                  sll        t3, s7, a3
                  or         s0, a2, a0
                  lui        zero, 195546
                  srl        a0, s2, a0
                  or         s0, a2, a0
                  c.mv       a1, s5
                  add        s7, s5, a6
                  xori       a4, t0, 974
                  c.and      a0, s0
                  lui        zero, 195546
                  add        s7, s5, a6
                  add        s7, s5, a6
                  srli       s8, t6, 19
                  srai       s10, s1, 24
                  rem        s0, a3, a2
                  mulh       s11, s1, s9
                  c.andi     a5, -1
                  slti       tp, t6, 301
                  or         s0, a2, a0
                  c.slli     t4, 28
                  srl        a0, s2, a0
                  srli       s8, t6, 19
                  c.sub      s1, a4
                  sltiu      s6, ra, 913
                  xori       a4, t0, 974
                  slti       tp, t6, 301
                  slli       s11, gp, 14
                  remu       s5, s11, t1
                  sra        s1, t3, s1
                  sub        s9, s6, s5
                  slli       s11, gp, 14
                  lui        zero, 195546
                  lui        zero, 195546
                  rem        s0, a3, a2
                  rem        s0, a3, a2
                  divu       sp, ra, t0
                  rem        s0, a3, a2
                  sltu       t2, s1, t1
                  c.addi4spn a4, sp, 288
                  c.sub      s1, a4
                  c.srli     a0, 25
                  xori       a4, t0, 974
                  addi       a7, t2, -784
                  c.or       a5, a1
                  rem        s0, a3, a2
                  add        s7, s5, a6
                  srai       s10, s1, 24
                  srli       s8, t6, 19
                  sltu       t2, s1, t1
                  c.nop
                  add        s7, s5, a6
                  c.lui      a0, 24
                  andi       s8, t1, -26
                  c.addi4spn a4, sp, 288
                  auipc      t6, 688967
                  mulhu      tp, s3, a4
                  c.li       a7, 27
                  andi       s8, t1, -26
                  c.addi4spn a4, sp, 288
                  sub        s9, s6, s5
                  sltu       t2, s1, t1
                  c.or       a5, a1
                  c.li       a7, 27
                  sltiu      s6, ra, 913
                  ori        t5, t2, 999
                  c.xor      a1, a2
                  c.andi     a5, -1
                  c.mv       a1, s5
                  ori        t5, t2, 999
                  auipc      t6, 688967
                  c.nop
                  c.add      t1, a1
                  mulhsu     gp, a1, s1
                  c.andi     a5, -1
                  mulhsu     gp, a1, s1
                  remu       s5, s11, t1
                  divu       sp, ra, t0
                  c.li       a7, 27
                  c.slli     t4, 28
                  c.li       a7, 27
                  slt        t1, a1, a4
                  sltu       t2, s1, t1
                  xor        t4, s3, t3
                  c.li       a7, 27
                  c.li       a7, 27
                  xor        t4, s3, t3
                  c.andi     a5, -1
                  remu       s5, s11, t1
                  add        s7, s5, a6
                  slt        t1, a1, a4
                  and        a1, t3, a6
                  c.slli     t4, 28
                  mulhu      tp, s3, a4
                  c.add      t1, a1
                  mulhsu     gp, a1, s1
                  mulhsu     gp, a1, s1
                  c.mv       a1, s5
                  mulh       s11, s1, s9
                  sub        s9, s6, s5
                  mul        sp, s9, s11
                  lui        zero, 195546
                  srl        a0, s2, a0
                  and        a1, t3, a6
                  c.addi16sp sp, 16
                  mul        sp, s9, s11
                  remu       s5, s11, t1
                  c.xor      a1, a2
                  c.addi16sp sp, 16
                  c.addi16sp sp, 16
                  or         s0, a2, a0
                  or         s0, a2, a0
                  lui        zero, 195546
                  slt        t1, a1, a4
                  c.lui      a0, 24
                  c.andi     a5, -1
                  rem        s0, a3, a2
                  c.addi     s1, 6
                  c.add      t1, a1
                  sltu       t2, s1, t1
                  c.lui      a0, 24
                  c.srai     s0, 31
                  mulh       s11, s1, s9
                  srai       s10, s1, 24
                  xori       a4, t0, 974
                  andi       s8, t1, -26
                  andi       s8, t1, -26
                  c.li       a7, 27
                  srai       s10, s1, 24
                  mul        sp, s9, s11
                  c.mv       a1, s5
                  lui        zero, 195546
                  mulhu      tp, s3, a4
                  nop
                  auipc      t6, 688967
                  nop
                  c.srli     a0, 25
                  c.li       a7, 27
                  nop
                  mul        sp, s9, s11
                  c.nop
                  mulh       s11, s1, s9
                  lui        zero, 195546
                  c.srai     s0, 31
                  c.lui      a0, 24
                  c.slli     t4, 28
                  slt        t1, a1, a4
                  add        s7, s5, a6
                  and        a1, t3, a6
                  c.addi4spn a4, sp, 288
                  c.addi4spn a4, sp, 288
                  div        t3, t1, t5
                  c.lui      a0, 24
                  add        s7, s5, a6
                  lui        zero, 195546
                  div        t3, t1, t5
                  slti       tp, t6, 301
                  c.addi4spn a4, sp, 288
                  srai       s10, s1, 24
                  rem        s0, a3, a2
                  c.lui      a0, 24
                  slli       s11, gp, 14
                  c.xor      a1, a2
                  andi       s8, t1, -26
                  sltiu      s6, ra, 913
                  lui        zero, 195546
                  sltiu      s6, ra, 913
                  xori       a4, t0, 974
                  and        a1, t3, a6
                  and        a1, t3, a6
                  sub        s9, s6, s5
                  rem        s0, a3, a2
                  c.slli     t4, 28
                  c.li       a7, 27
                  c.xor      a1, a2
                  nop
                  divu       sp, ra, t0
                  c.addi16sp sp, 16
                  c.nop
                  auipc      t6, 688967
                  c.mv       a1, s5
                  xor        t4, s3, t3
                  and        a1, t3, a6
                  srl        a0, s2, a0
                  slli       s11, gp, 14
                  addi       a7, t2, -784
                  andi       s8, t1, -26
                  c.xor      a1, a2
                  mulhu      tp, s3, a4
                  c.addi4spn a4, sp, 288
                  srai       s10, s1, 24
                  c.add      t1, a1
                  srli       s8, t6, 19
                  c.slli     t4, 28
                  c.srai     s0, 31
                  c.slli     t4, 28
                  addi       a7, t2, -784
                  srl        a0, s2, a0
                  c.srli     a0, 25
                  sltiu      s6, ra, 913
                  c.xor      a1, a2
                  sll        t3, s7, a3
                  auipc      t6, 688967
                  c.andi     a5, -1
                  slti       tp, t6, 301
                  xori       a4, t0, 974
                  c.mv       a1, s5
                  remu       s5, s11, t1
                  c.srli     a0, 25
                  c.add      t1, a1
                  xori       a4, t0, 974
                  sltu       t2, s1, t1
                  remu       s5, s11, t1
                  auipc      t6, 688967
                  addi       a7, t2, -784
                  c.and      a0, s0
                  c.add      t1, a1
                  mulhsu     gp, a1, s1
                  srl        a0, s2, a0
                  addi       a7, t2, -784
                  andi       s8, t1, -26
                  mul        sp, s9, s11
                  sub        s9, s6, s5
                  c.andi     a5, -1
                  c.andi     a5, -1
                  slti       tp, t6, 301
                  ori        t5, t2, 999
                  c.lui      a0, 24
                  c.slli     t4, 28
                  srli       s8, t6, 19
                  c.add      t1, a1
                  and        a1, t3, a6
                  xor        t4, s3, t3
                  c.addi4spn a4, sp, 288
                  c.mv       a1, s5
                  sra        s1, t3, s1
                  lui        zero, 195546
                  andi       s8, t1, -26
                  sll        t3, s7, a3
                  c.xor      a1, a2
                  xori       a4, t0, 974
                  srli       s8, t6, 19
                  c.and      a0, s0
                  c.li       a7, 27
                  slt        t1, a1, a4
                  c.addi4spn a4, sp, 288
                  c.addi4spn a4, sp, 288
                  sltiu      s6, ra, 913
                  c.addi4spn a4, sp, 288
                  mul        sp, s9, s11
                  c.mv       a1, s5
                  nop
                  add        s7, s5, a6
                  remu       s5, s11, t1
                  c.xor      a1, a2
                  c.andi     a5, -1
                  lui        zero, 195546
                  or         s0, a2, a0
                  remu       s5, s11, t1
                  slti       tp, t6, 301
                  sub        s9, s6, s5
                  c.nop
                  andi       s8, t1, -26
                  auipc      t6, 688967
                  c.slli     t4, 28
                  mulh       s11, s1, s9
                  sltiu      s6, ra, 913
                  and        a1, t3, a6
                  lui        zero, 195546
                  slti       tp, t6, 301
                  c.mv       a1, s5
                  sll        t3, s7, a3
                  xori       a4, t0, 974
                  nop
                  c.li       a7, 27
                  c.addi4spn a4, sp, 288
                  andi       s8, t1, -26
                  c.mv       a1, s5
                  div        t3, t1, t5
                  c.and      a0, s0
                  sub        s9, s6, s5
                  mulhu      tp, s3, a4
                  or         s0, a2, a0
                  div        t3, t1, t5
                  srli       s8, t6, 19
                  c.xor      a1, a2
                  srai       s10, s1, 24
                  slt        t1, a1, a4
                  c.slli     t4, 28
                  c.addi16sp sp, 16
                  c.or       a5, a1
                  c.sub      s1, a4
                  mulh       s11, s1, s9
                  sub        s9, s6, s5
                  sub        s9, s6, s5
                  lui        zero, 195546
                  mulhsu     gp, a1, s1
                  addi       a7, t2, -784
                  slti       tp, t6, 301
                  c.add      t1, a1
                  srli       s8, t6, 19
                  slli       s11, gp, 14
                  mulhsu     gp, a1, s1
                  c.and      a0, s0
                  srli       s8, t6, 19
                  c.addi     s1, 6
                  or         s0, a2, a0
                  sll        t3, s7, a3
                  remu       s5, s11, t1
                  ori        t5, t2, 999
                  c.addi4spn a4, sp, 288
                  c.and      a0, s0
                  sltiu      s6, ra, 913
                  ori        t5, t2, 999
                  sub        s9, s6, s5
                  sra        s1, t3, s1
                  c.add      t1, a1
                  add        s7, s5, a6
                  srl        a0, s2, a0
                  sub        s9, s6, s5
                  sra        s1, t3, s1
                  xor        t4, s3, t3
                  c.slli     t4, 28
                  slti       tp, t6, 301
                  ori        t5, t2, 999
                  mul        sp, s9, s11
                  and        a1, t3, a6
                  mulhu      tp, s3, a4
                  auipc      t6, 688967
                  addi       a7, t2, -784
                  c.li       a7, 27
                  mulhu      tp, s3, a4
                  slt        t1, a1, a4
                  c.andi     a5, -1
                  c.lui      a0, 24
                  srai       s10, s1, 24
                  remu       s5, s11, t1
                  c.lui      a0, 24
                  c.andi     a5, -1
                  sll        t3, s7, a3
                  mulhsu     gp, a1, s1
                  c.addi     s1, 6
                  c.mv       a1, s5
                  c.slli     t4, 28
                  c.slli     t4, 28
                  srl        a0, s2, a0
                  c.or       a5, a1
                  div        t3, t1, t5
                  sltiu      s6, ra, 913
                  srli       s8, t6, 19
                  c.lui      a0, 24
                  c.sub      s1, a4
                  c.lui      a0, 24
                  c.addi4spn a4, sp, 288
                  mulh       s11, s1, s9
                  or         s0, a2, a0
                  sltu       t2, s1, t1
                  c.xor      a1, a2
                  remu       s5, s11, t1
                  c.and      a0, s0
                  add        s7, s5, a6
                  divu       sp, ra, t0
                  remu       s5, s11, t1
                  c.add      t1, a1
                  c.and      a0, s0
                  mulhu      tp, s3, a4
                  c.or       a5, a1
                  and        a1, t3, a6
                  sra        s1, t3, s1
                  c.andi     a5, -1
                  sltu       t2, s1, t1
                  c.xor      a1, a2
                  srl        a0, s2, a0
                  sub        s9, s6, s5
                  c.lui      a0, 24
                  sub        s9, s6, s5
                  ori        t5, t2, 999
                  sltu       t2, s1, t1
                  or         s0, a2, a0
                  sub        s9, s6, s5
                  sll        t3, s7, a3
                  slti       tp, t6, 301
                  andi       s8, t1, -26
                  mul        sp, s9, s11
                  ori        t5, t2, 999
                  ori        t5, t2, 999
                  addi       a7, t2, -784
                  c.srli     a0, 25
                  srli       s8, t6, 19
                  nop
                  c.xor      a1, a2
                  c.sub      s1, a4
                  c.xor      a1, a2
                  mulhu      tp, s3, a4
                  mulh       s11, s1, s9
                  c.srai     s0, 31
                  divu       sp, ra, t0
                  c.andi     a5, -1
                  sra        s1, t3, s1
                  c.lui      a0, 24
                  c.srai     s0, 31
                  c.or       a5, a1
                  remu       s5, s11, t1
                  auipc      t6, 688967
                  mulhu      tp, s3, a4
                  mul        sp, s9, s11
                  slt        t1, a1, a4
                  c.srli     a0, 25
                  c.and      a0, s0
                  mulhu      tp, s3, a4
                  xor        t4, s3, t3
                  lui        zero, 195546
                  sltu       t2, s1, t1
                  c.mv       a1, s5
                  c.nop
                  xori       a4, t0, 974
                  c.add      t1, a1
                  slt        t1, a1, a4
                  c.nop
                  sltu       t2, s1, t1
                  c.srai     s0, 31
                  rem        s0, a3, a2
                  mulh       s11, s1, s9
                  mulhsu     gp, a1, s1
                  slli       s11, gp, 14
                  c.slli     t4, 28
                  mulhsu     gp, a1, s1
                  sub        s9, s6, s5
                  c.and      a0, s0
                  c.or       a5, a1
                  slli       s11, gp, 14
                  c.andi     a5, -1
                  c.srli     a0, 25
                  rem        s0, a3, a2
                  and        a1, t3, a6
                  c.and      a0, s0
                  sltiu      s6, ra, 913
                  slt        t1, a1, a4
                  srl        a0, s2, a0
                  nop
                  mul        sp, s9, s11
                  c.nop
                  sltiu      s6, ra, 913
                  sll        t3, s7, a3
                  c.nop
                  c.sub      s1, a4
                  c.nop
                  srl        a0, s2, a0
                  c.mv       a1, s5
                  slt        t1, a1, a4
                  sltu       t2, s1, t1
                  c.nop
                  divu       sp, ra, t0
                  c.addi16sp sp, 16
                  c.lui      a0, 24
                  c.nop
                  c.addi16sp sp, 16
                  slt        t1, a1, a4
                  c.srai     s0, 31
                  remu       s5, s11, t1
                  mulhsu     gp, a1, s1
                  slt        t1, a1, a4
                  sub        s9, s6, s5
                  slt        t1, a1, a4
                  c.li       a7, 27
                  addi       a7, t2, -784
                  xor        t4, s3, t3
                  add        s7, s5, a6
                  c.slli     t4, 28
                  ori        t5, t2, 999
                  srli       s8, t6, 19
                  slt        t1, a1, a4
                  sub        s9, s6, s5
                  rem        s0, a3, a2
                  ori        t5, t2, 999
                  c.addi4spn a4, sp, 288
                  andi       s8, t1, -26
                  add        s7, s5, a6
                  c.sub      s1, a4
                  c.addi     s1, 6
                  mulh       s11, s1, s9
                  lui        zero, 195546
                  c.addi16sp sp, 16
                  div        t3, t1, t5
                  c.addi4spn a4, sp, 288
                  c.addi16sp sp, 16
                  sltu       t2, s1, t1
                  ori        t5, t2, 999
                  c.nop
                  c.addi16sp sp, 16
                  c.or       a5, a1
                  auipc      t6, 688967
                  lui        zero, 195546
                  c.add      t1, a1
                  c.srli     a0, 25
                  c.srli     a0, 25
                  divu       sp, ra, t0
                  c.addi4spn a4, sp, 288
                  c.nop
                  c.addi16sp sp, 16
                  rem        s0, a3, a2
                  c.nop
                  remu       s5, s11, t1
                  c.mv       a1, s5
                  mulhsu     gp, a1, s1
                  add        s7, s5, a6
                  mulhu      tp, s3, a4
                  sll        t3, s7, a3
                  sltiu      s6, ra, 913
                  c.lui      a0, 24
                  xor        t4, s3, t3
                  c.srai     s0, 31
                  c.and      a0, s0
                  auipc      t6, 688967
                  xori       a4, t0, 974
                  c.mv       a1, s5
                  add        s7, s5, a6
                  xori       a4, t0, 974
                  sll        t3, s7, a3
                  xor        t4, s3, t3
                  xor        t4, s3, t3
                  slli       s11, gp, 14
                  c.lui      a0, 24
                  c.addi16sp sp, 16
                  srai       s10, s1, 24
                  mulhsu     gp, a1, s1
                  addi       a7, t2, -784
                  or         s0, a2, a0
                  c.addi     s1, 6
                  c.addi4spn a4, sp, 288
                  sub        s9, s6, s5
                  slli       s11, gp, 14
                  sra        s1, t3, s1
                  sltu       t2, s1, t1
                  add        s7, s5, a6
                  srli       s8, t6, 19
                  c.or       a5, a1
                  remu       s5, s11, t1
                  c.srai     s0, 31
                  divu       sp, ra, t0
                  c.xor      a1, a2
                  ori        t5, t2, 999
                  c.add      t1, a1
                  mulh       s11, s1, s9
                  or         s0, a2, a0
                  addi       a7, t2, -784
                  c.addi16sp sp, 16
                  srl        a0, s2, a0
                  divu       sp, ra, t0
                  sra        s1, t3, s1
                  c.sub      s1, a4
                  addi       a7, t2, -784
                  c.addi16sp sp, 16
                  mul        sp, s9, s11
                  sll        t3, s7, a3
                  c.addi     s1, 6
                  mulh       s11, s1, s9
                  mul        sp, s9, s11
                  sltiu      s6, ra, 913
                  srai       s10, s1, 24
                  srli       s8, t6, 19
                  c.sub      s1, a4
                  andi       s8, t1, -26
                  c.srli     a0, 25
                  c.xor      a1, a2
                  sub        s9, s6, s5
                  c.nop
                  c.addi4spn a4, sp, 288
                  c.andi     a5, -1
                  srl        a0, s2, a0
                  c.or       a5, a1
                  andi       s8, t1, -26
                  c.slli     t4, 28
                  xori       a4, t0, 974
                  c.andi     a5, -1
                  xori       a4, t0, 974
                  xor        t4, s3, t3
                  c.slli     t4, 28
                  c.li       a7, 27
                  c.lui      a0, 24
                  add        s7, s5, a6
                  mulhsu     gp, a1, s1
                  srl        a0, s2, a0
                  andi       s8, t1, -26
                  srl        a0, s2, a0
                  c.addi4spn a4, sp, 288
                  andi       s8, t1, -26
                  lui        zero, 195546
                  c.andi     a5, -1
                  lui        zero, 195546
                  nop
                  remu       s5, s11, t1
                  divu       sp, ra, t0
                  c.or       a5, a1
                  andi       s8, t1, -26
                  c.mv       a1, s5
                  addi       a7, t2, -784
                  slli       s11, gp, 14
                  addi       a7, t2, -784
                  ori        t5, t2, 999
                  slti       tp, t6, 301
                  mulhsu     gp, a1, s1
                  c.srai     s0, 31
                  mulhsu     gp, a1, s1
                  c.sub      s1, a4
                  sub        s9, s6, s5
                  srli       s8, t6, 19
                  add        s7, s5, a6
                  add        s7, s5, a6
                  srai       s10, s1, 24
                  mulh       s11, s1, s9
                  and        a1, t3, a6
                  c.or       a5, a1
                  c.mv       a1, s5
                  sub        s9, s6, s5
                  mulhu      tp, s3, a4
                  c.sub      s1, a4
                  c.li       a7, 27
                  c.or       a5, a1
                  c.addi     s1, 6
                  sll        t3, s7, a3
                  mulhsu     gp, a1, s1
                  xori       a4, t0, 974
                  andi       s8, t1, -26
                  c.and      a0, s0
                  slli       s11, gp, 14
                  addi       a7, t2, -784
                  c.srai     s0, 31
                  c.addi4spn a4, sp, 288
                  c.xor      a1, a2
                  xor        t4, s3, t3
                  divu       sp, ra, t0
                  auipc      t6, 688967
                  c.add      t1, a1
                  add        s7, s5, a6
                  c.andi     a5, -1
                  sra        s1, t3, s1
                  addi       a7, t2, -784
                  and        a1, t3, a6
                  c.mv       a1, s5
                  c.and      a0, s0
                  remu       s5, s11, t1
                  sltu       t2, s1, t1
                  c.add      t1, a1
                  add        s7, s5, a6
                  xor        t4, s3, t3
                  rem        s0, a3, a2
                  c.and      a0, s0
                  ori        t5, t2, 999
                  c.addi     s1, 6
                  c.srli     a0, 25
                  div        t3, t1, t5
                  c.xor      a1, a2
                  c.sub      s1, a4
                  div        t3, t1, t5
                  srl        a0, s2, a0
                  slti       tp, t6, 301
                  c.or       a5, a1
                  c.sub      s1, a4
                  mulhu      tp, s3, a4
                  mulhsu     gp, a1, s1
                  c.li       a7, 27
                  c.nop
                  lui        zero, 195546
                  addi       a7, t2, -784
                  andi       s8, t1, -26
                  addi       a7, t2, -784
                  c.add      t1, a1
                  slti       tp, t6, 301
                  sub        s9, s6, s5
                  sll        t3, s7, a3
                  xori       a4, t0, 974
                  rem        s0, a3, a2
                  sltiu      s6, ra, 913
                  c.mv       a1, s5
                  andi       s8, t1, -26
                  andi       s8, t1, -26
                  nop
                  srai       s10, s1, 24
                  xori       a4, t0, 974
                  nop
                  c.slli     t4, 28
                  auipc      t6, 688967
                  c.srai     s0, 31
                  sub        s9, s6, s5
                  mulhsu     gp, a1, s1
                  divu       sp, ra, t0
                  sra        s1, t3, s1
                  srai       s10, s1, 24
                  sll        t3, s7, a3
                  div        t3, t1, t5
                  addi       a7, t2, -784
                  or         s0, a2, a0
                  sra        s1, t3, s1
                  divu       sp, ra, t0
                  mulhu      tp, s3, a4
                  c.slli     t4, 28
                  c.slli     t4, 28
                  slt        t1, a1, a4
                  c.mv       a1, s5
                  srli       s8, t6, 19
                  li         s5, 0x0 #start riscv_int_numeric_corner_stream_6
                  li         s11, 0x80000000
                  li         s3, 0xd6366199
                  li         s7, 0x80000000
                  li         t6, 0xffffffff
                  li         tp, 0xffffffff
                  li         a1, 0x80000000
                  li         t5, 0x0
                  li         s9, 0x0
                  li         s6, 0x80000000
                  addi       tp, s5, 999
                  nop
                  nop
                  mulh       a1, s7, s5
                  mulhu      s9, tp, tp
                  addi       tp, s5, 999
                  remu       s5, s11, s6
                  addi       tp, s5, 999
                  lui        tp, 195546
                  rem        t5, tp, a1
                  div        s3, s3, t5
                  mul        s5, s6, t5
                  sub        s5, s5, tp
                  div        s3, s3, t5
                  mul        s5, s6, t5 #end riscv_int_numeric_corner_stream_6
                  c.xor      a1, a2
                  sra        s1, t3, s1
                  slti       tp, t6, 301
                  xori       a4, t0, 974
                  c.sub      s1, a4
                  xor        t4, s3, t3
                  c.andi     a5, -1
                  c.addi4spn a4, sp, 288
                  mulh       s11, s1, s9
                  srai       s10, s1, 24
                  c.lui      a0, 24
                  mulh       s11, s1, s9
                  auipc      t6, 688967
                  div        t3, t1, t5
                  srai       s10, s1, 24
                  c.or       a5, a1
                  mulhsu     gp, a1, s1
                  ori        t5, t2, 999
                  c.xor      a1, a2
                  mulhsu     gp, a1, s1
                  c.mv       a1, s5
                  mulhu      tp, s3, a4
                  nop
                  c.xor      a1, a2
                  nop
                  c.addi16sp sp, 16
                  c.or       a5, a1
                  c.addi     s1, 6
                  add        s7, s5, a6
                  c.li       a7, 27
                  xor        t4, s3, t3
                  remu       s5, s11, t1
                  mulhsu     gp, a1, s1
                  srai       s10, s1, 24
                  c.li       a7, 27
                  c.nop
                  addi       a7, t2, -784
                  sll        t3, s7, a3
                  slt        t1, a1, a4
                  addi       a7, t2, -784
                  c.srai     s0, 31
                  c.lui      a0, 24
                  c.or       a5, a1
                  mulhu      tp, s3, a4
                  slti       tp, t6, 301
                  mul        sp, s9, s11
                  c.mv       a1, s5
                  mulhsu     gp, a1, s1
                  ori        t5, t2, 999
                  slti       tp, t6, 301
                  auipc      t6, 688967
                  xor        t4, s3, t3
                  c.srai     s0, 31
                  auipc      t6, 688967
                  mulhsu     gp, a1, s1
                  c.andi     a5, -1
                  xor        t4, s3, t3
                  auipc      t6, 688967
                  c.srai     s0, 31
                  c.or       a5, a1
                  divu       sp, ra, t0
                  c.nop
                  div        t3, t1, t5
                  mulhu      tp, s3, a4
                  c.srli     a0, 25
                  rem        s0, a3, a2
                  mulh       s11, s1, s9
                  ori        t5, t2, 999
                  srl        a0, s2, a0
                  c.or       a5, a1
                  sltu       t2, s1, t1
                  c.mv       a1, s5
                  c.add      t1, a1
                  sra        s1, t3, s1
                  sltiu      s6, ra, 913
                  sra        s1, t3, s1
                  slli       s11, gp, 14
                  c.srai     s0, 31
                  c.and      a0, s0
                  c.andi     a5, -1
                  slt        t1, a1, a4
                  sub        s9, s6, s5
                  srli       s8, t6, 19
                  sltu       t2, s1, t1
                  slti       tp, t6, 301
                  c.li       a7, 27
                  mulhu      tp, s3, a4
                  c.andi     a5, -1
                  sll        t3, s7, a3
                  mulhu      tp, s3, a4
                  divu       sp, ra, t0
                  andi       s8, t1, -26
                  add        s7, s5, a6
                  c.srli     a0, 25
                  xori       a4, t0, 974
                  c.lui      a0, 24
                  c.and      a0, s0
                  auipc      t6, 688967
                  divu       sp, ra, t0
                  divu       sp, ra, t0
                  sra        s1, t3, s1
                  slti       tp, t6, 301
                  ori        t5, t2, 999
                  mulhu      tp, s3, a4
                  or         s0, a2, a0
                  srl        a0, s2, a0
                  slti       tp, t6, 301
                  xori       a4, t0, 974
                  srai       s10, s1, 24
                  xori       a4, t0, 974
                  sub        s9, s6, s5
                  c.slli     t4, 28
                  add        s7, s5, a6
                  c.slli     t4, 28
                  c.add      t1, a1
                  srai       s10, s1, 24
                  c.srai     s0, 31
                  mulh       s11, s1, s9
                  lui        zero, 195546
                  c.xor      a1, a2
                  mulhsu     gp, a1, s1
                  add        s7, s5, a6
                  lui        zero, 195546
                  c.nop
                  c.xor      a1, a2
                  mul        sp, s9, s11
                  lui        zero, 195546
                  sltiu      s6, ra, 913
                  sub        s9, s6, s5
                  slt        t1, a1, a4
                  c.addi16sp sp, 16
                  slli       s11, gp, 14
                  c.li       a7, 27
                  c.mv       a1, s5
                  slli       s11, gp, 14
                  c.slli     t4, 28
                  c.slli     t4, 28
                  addi       a7, t2, -784
                  c.srli     a0, 25
                  srli       s8, t6, 19
                  srl        a0, s2, a0
                  sub        s9, s6, s5
                  c.andi     a5, -1
                  sub        s9, s6, s5
                  c.xor      a1, a2
                  c.slli     t4, 28
                  c.srai     s0, 31
                  div        t3, t1, t5
                  slli       s11, gp, 14
                  c.addi     s1, 6
                  sll        t3, s7, a3
                  c.lui      a0, 24
                  c.addi4spn a4, sp, 288
                  andi       s8, t1, -26
                  c.li       a7, 27
                  and        a1, t3, a6
                  c.nop
                  c.addi4spn a4, sp, 288
                  c.addi4spn a4, sp, 288
                  c.sub      s1, a4
                  srai       s10, s1, 24
                  c.lui      a0, 24
                  srli       s8, t6, 19
                  c.lui      a0, 24
                  c.addi4spn a4, sp, 288
                  c.and      a0, s0
                  c.andi     a5, -1
                  srai       s10, s1, 24
                  auipc      t6, 688967
                  c.nop
                  sll        t3, s7, a3
                  nop
                  remu       s5, s11, t1
                  c.add      t1, a1
                  divu       sp, ra, t0
                  divu       sp, ra, t0
                  c.and      a0, s0
                  srai       s10, s1, 24
                  c.andi     a5, -1
                  divu       sp, ra, t0
                  slti       tp, t6, 301
                  c.or       a5, a1
                  mul        sp, s9, s11
                  or         s0, a2, a0
                  mul        sp, s9, s11
                  slt        t1, a1, a4
                  c.sub      s1, a4
                  sub        s9, s6, s5
                  mulhu      tp, s3, a4
                  sub        s9, s6, s5
                  srli       s8, t6, 19
                  andi       s8, t1, -26
                  add        s7, s5, a6
                  c.addi     s1, 6
                  div        t3, t1, t5
                  and        a1, t3, a6
                  divu       sp, ra, t0
                  slt        t1, a1, a4
                  srli       s8, t6, 19
                  sltiu      s6, ra, 913
                  sub        s9, s6, s5
                  nop
                  c.srli     a0, 25
                  c.slli     t4, 28
                  mulh       s11, s1, s9
                  c.addi16sp sp, 16
                  c.or       a5, a1
                  lui        zero, 195546
                  c.slli     t4, 28
                  ori        t5, t2, 999
                  mulhu      tp, s3, a4
                  c.li       a7, 27
                  c.add      t1, a1
                  c.and      a0, s0
                  c.lui      a0, 24
                  c.addi16sp sp, 16
                  srai       s10, s1, 24
                  xori       a4, t0, 974
                  ori        t5, t2, 999
                  and        a1, t3, a6
                  andi       s8, t1, -26
                  c.and      a0, s0
                  rem        s0, a3, a2
                  c.slli     t4, 28
                  c.srli     a0, 25
                  sub        s9, s6, s5
                  mul        sp, s9, s11
                  c.li       a7, 27
                  sll        t3, s7, a3
                  srl        a0, s2, a0
                  c.lui      a0, 24
                  sra        s1, t3, s1
                  c.srli     a0, 25
                  or         s0, a2, a0
                  c.srai     s0, 31
                  mul        sp, s9, s11
                  c.lui      a0, 24
                  mulh       s11, s1, s9
                  sltu       t2, s1, t1
                  xor        t4, s3, t3
                  c.andi     a5, -1
                  c.and      a0, s0
                  c.addi     s1, 6
                  sll        t3, s7, a3
                  c.xor      a1, a2
                  c.li       a7, 27
                  c.mv       a1, s5
                  c.srai     s0, 31
                  rem        s0, a3, a2
                  c.srli     a0, 25
                  c.nop
                  mulhu      tp, s3, a4
                  lui        zero, 195546
                  c.sub      s1, a4
                  ori        t5, t2, 999
                  srli       s8, t6, 19
                  c.nop
                  slti       tp, t6, 301
                  div        t3, t1, t5
                  c.srai     s0, 31
                  sra        s1, t3, s1
                  c.srai     s0, 31
                  c.addi16sp sp, 16
                  c.addi     s1, 6
                  mulhu      tp, s3, a4
                  c.nop
                  slt        t1, a1, a4
                  addi       a7, t2, -784
                  rem        s0, a3, a2
                  c.addi4spn a4, sp, 288
                  xor        t4, s3, t3
                  srli       s8, t6, 19
                  mulh       s11, s1, s9
                  slli       s11, gp, 14
                  sll        t3, s7, a3
                  c.lui      a0, 24
                  and        a1, t3, a6
                  remu       s5, s11, t1
                  or         s0, a2, a0
                  sra        s1, t3, s1
                  srl        a0, s2, a0
                  slli       s11, gp, 14
                  and        a1, t3, a6
                  srai       s10, s1, 24
                  mulhsu     gp, a1, s1
                  c.nop
                  mulh       s11, s1, s9
                  c.slli     t4, 28
                  div        t3, t1, t5
                  andi       s8, t1, -26
                  xori       a4, t0, 974
                  or         s0, a2, a0
                  c.xor      a1, a2
                  xor        t4, s3, t3
                  c.sub      s1, a4
                  c.srai     s0, 31
                  c.sub      s1, a4
                  mulhu      tp, s3, a4
                  slt        t1, a1, a4
                  c.li       a7, 27
                  and        a1, t3, a6
                  sltiu      s6, ra, 913
                  mulh       s11, s1, s9
                  mulh       s11, s1, s9
                  c.srai     s0, 31
                  c.lui      a0, 24
                  sll        t3, s7, a3
                  c.add      t1, a1
                  srai       s10, s1, 24
                  remu       s5, s11, t1
                  addi       a7, t2, -784
                  j fast_exit

#Start: Extracted from riscv_compliance_tests/riscv_test.h
fast_exit:
                  /* print "\nDONE\n\n" */
                  lui a0,print_port>>12
                  addi a1,zero,'D'
                  addi a2,zero,'O'
                  addi a3,zero,'N'
                  addi a4,zero,'E'
                  addi a5,zero,'\n'
                  sw a5,0(a0)
                  sw a1,0(a0)
                  sw a2,0(a0)
                  sw a3,0(a0)
                  sw a4,0(a0)
                  sw a5,0(a0)
                  sw a5,0(a0)

                  li a0, CV_VP_STATUS_FLAGS_BASE
                  lw a1, test_results /* report result */
                  sw a1,0(a0)

                  wfi  /* we are done */
##End: Extracted from riscv_compliance_tests/riscv_test.h

                  j test_done
test_done:
                  li gp, 1
                  ecall
write_tohost:
                  sw gp, tohost, t5

_exit:
                  j write_tohost

init_machine_mode:
                  li x30, 0x1800
                  csrw 0x300, x30 # MSTATUS
                  li x30, 0x0
                  csrw 0x304, x30 # MIE
                  mret
instr_end:
                  nop

.section .data
.align 6; .global tohost; tohost: .dword 0;
.align 6; .global fromhost; fromhost: .dword 0;
.section .user_stack,"aw",@progbits;
.align 2
user_stack_start:
.rept 4999
.4byte 0x0
.endr
user_stack_end:
.4byte 0x0
.align 2
kernel_instr_start:
.text
mmode_intr_vector_1:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x342 # MCAUSE
                  srli x30, x30, 0x1f
                  beqz x30, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_2:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x342 # MCAUSE
                  srli x30, x30, 0x1f
                  beqz x30, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_3:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x342 # MCAUSE
                  srli x30, x30, 0x1f
                  beqz x30, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_4:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x342 # MCAUSE
                  srli x30, x30, 0x1f
                  beqz x30, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_5:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x342 # MCAUSE
                  srli x30, x30, 0x1f
                  beqz x30, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_6:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x342 # MCAUSE
                  srli x30, x30, 0x1f
                  beqz x30, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_7:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x342 # MCAUSE
                  srli x30, x30, 0x1f
                  beqz x30, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_8:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x342 # MCAUSE
                  srli x30, x30, 0x1f
                  beqz x30, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_9:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x342 # MCAUSE
                  srli x30, x30, 0x1f
                  beqz x30, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_10:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x342 # MCAUSE
                  srli x30, x30, 0x1f
                  beqz x30, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_11:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x342 # MCAUSE
                  srli x30, x30, 0x1f
                  beqz x30, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_12:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x342 # MCAUSE
                  srli x30, x30, 0x1f
                  beqz x30, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_13:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x342 # MCAUSE
                  srli x30, x30, 0x1f
                  beqz x30, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_14:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x342 # MCAUSE
                  srli x30, x30, 0x1f
                  beqz x30, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_15:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x342 # MCAUSE
                  srli x30, x30, 0x1f
                  beqz x30, 1f
                  j mmode_intr_handler
                  1: j test_done

.align 2
mtvec_handler:
                  .option norvc;
                  j mmode_exception_handler
                  j mmode_intr_vector_1
                  j mmode_intr_vector_2
                  j mmode_intr_vector_3
                  j mmode_intr_vector_4
                  j mmode_intr_vector_5
                  j mmode_intr_vector_6
                  j mmode_intr_vector_7
                  j mmode_intr_vector_8
                  j mmode_intr_vector_9
                  j mmode_intr_vector_10
                  j mmode_intr_vector_11
                  j mmode_intr_vector_12
                  j mmode_intr_vector_13
                  j mmode_intr_vector_14
                  j mmode_intr_vector_15
                  .option rvc;

mmode_exception_handler:
                  csrrw x12, 0x340, x12
                  add x12, x13, zero
                  1: addi x12, x12, -124
                  sw  x1, 4(x12)
                  sw  x2, 8(x12)
                  sw  x3, 12(x12)
                  sw  x4, 16(x12)
                  sw  x5, 20(x12)
                  sw  x6, 24(x12)
                  sw  x7, 28(x12)
                  sw  x8, 32(x12)
                  sw  x9, 36(x12)
                  sw  x10, 40(x12)
                  sw  x11, 44(x12)
                  sw  x12, 48(x12)
                  sw  x13, 52(x12)
                  sw  x14, 56(x12)
                  sw  x15, 60(x12)
                  sw  x16, 64(x12)
                  sw  x17, 68(x12)
                  sw  x18, 72(x12)
                  sw  x19, 76(x12)
                  sw  x20, 80(x12)
                  sw  x21, 84(x12)
                  sw  x22, 88(x12)
                  sw  x23, 92(x12)
                  sw  x24, 96(x12)
                  sw  x25, 100(x12)
                  sw  x26, 104(x12)
                  sw  x27, 108(x12)
                  sw  x28, 112(x12)
                  sw  x29, 116(x12)
                  sw  x30, 120(x12)
                  sw  x31, 124(x12)
                  csrr x30, 0x341 # MEPC
                  csrr x30, 0x342 # MCAUSE
                  li x22, 0x3 # BREAKPOINT
                  beq x30, x22, ebreak_handler
                  li x22, 0x8 # ECALL_UMODE
                  beq x30, x22, ecall_handler
                  li x22, 0x9 # ECALL_SMODE
                  beq x30, x22, ecall_handler
                  li x22, 0xb # ECALL_MMODE
                  beq x30, x22, ecall_handler
                  li x22, 0x1
                  beq x30, x22, instr_fault_handler
                  li x22, 0x5
                  beq x30, x22, load_fault_handler
                  li x22, 0x7
                  beq x30, x22, store_fault_handler
                  li x22, 0xc
                  beq x30, x22, pt_fault_handler
                  li x22, 0xd
                  beq x30, x22, pt_fault_handler
                  li x22, 0xf
                  beq x30, x22, pt_fault_handler
                  li x22, 0x2 # ILLEGAL_INSTRUCTION
                  beq x30, x22, illegal_instr_handler
                  csrr x22, 0x343 # MTVAL
                  1: jal x1, test_done

ecall_handler:
                  la x30, _start
                  sw x0, 0(x30)
                  sw x1, 4(x30)
                  sw x2, 8(x30)
                  sw x3, 12(x30)
                  sw x4, 16(x30)
                  sw x5, 20(x30)
                  sw x6, 24(x30)
                  sw x7, 28(x30)
                  sw x8, 32(x30)
                  sw x9, 36(x30)
                  sw x10, 40(x30)
                  sw x11, 44(x30)
                  sw x12, 48(x30)
                  sw x13, 52(x30)
                  sw x14, 56(x30)
                  sw x15, 60(x30)
                  sw x16, 64(x30)
                  sw x17, 68(x30)
                  sw x18, 72(x30)
                  sw x19, 76(x30)
                  sw x20, 80(x30)
                  sw x21, 84(x30)
                  sw x22, 88(x30)
                  sw x23, 92(x30)
                  sw x24, 96(x30)
                  sw x25, 100(x30)
                  sw x26, 104(x30)
                  sw x27, 108(x30)
                  sw x28, 112(x30)
                  sw x29, 116(x30)
                  sw x30, 120(x30)
                  sw x31, 124(x30)
                  j write_tohost
instr_fault_handler:
                  lw  x1, 4(x12)
                  lw  x2, 8(x12)
                  lw  x3, 12(x12)
                  lw  x4, 16(x12)
                  lw  x5, 20(x12)
                  lw  x6, 24(x12)
                  lw  x7, 28(x12)
                  lw  x8, 32(x12)
                  lw  x9, 36(x12)
                  lw  x10, 40(x12)
                  lw  x11, 44(x12)
                  lw  x12, 48(x12)
                  lw  x13, 52(x12)
                  lw  x14, 56(x12)
                  lw  x15, 60(x12)
                  lw  x16, 64(x12)
                  lw  x17, 68(x12)
                  lw  x18, 72(x12)
                  lw  x19, 76(x12)
                  lw  x20, 80(x12)
                  lw  x21, 84(x12)
                  lw  x22, 88(x12)
                  lw  x23, 92(x12)
                  lw  x24, 96(x12)
                  lw  x25, 100(x12)
                  lw  x26, 104(x12)
                  lw  x27, 108(x12)
                  lw  x28, 112(x12)
                  lw  x29, 116(x12)
                  lw  x30, 120(x12)
                  lw  x31, 124(x12)
                  addi x12, x12, 124
                  add x13, x12, zero
                  csrrw x12, 0x340, x12
                  mret

load_fault_handler:
                  lw  x1, 4(x12)
                  lw  x2, 8(x12)
                  lw  x3, 12(x12)
                  lw  x4, 16(x12)
                  lw  x5, 20(x12)
                  lw  x6, 24(x12)
                  lw  x7, 28(x12)
                  lw  x8, 32(x12)
                  lw  x9, 36(x12)
                  lw  x10, 40(x12)
                  lw  x11, 44(x12)
                  lw  x12, 48(x12)
                  lw  x13, 52(x12)
                  lw  x14, 56(x12)
                  lw  x15, 60(x12)
                  lw  x16, 64(x12)
                  lw  x17, 68(x12)
                  lw  x18, 72(x12)
                  lw  x19, 76(x12)
                  lw  x20, 80(x12)
                  lw  x21, 84(x12)
                  lw  x22, 88(x12)
                  lw  x23, 92(x12)
                  lw  x24, 96(x12)
                  lw  x25, 100(x12)
                  lw  x26, 104(x12)
                  lw  x27, 108(x12)
                  lw  x28, 112(x12)
                  lw  x29, 116(x12)
                  lw  x30, 120(x12)
                  lw  x31, 124(x12)
                  addi x12, x12, 124
                  add x13, x12, zero
                  csrrw x12, 0x340, x12
                  mret

store_fault_handler:
                  lw  x1, 4(x12)
                  lw  x2, 8(x12)
                  lw  x3, 12(x12)
                  lw  x4, 16(x12)
                  lw  x5, 20(x12)
                  lw  x6, 24(x12)
                  lw  x7, 28(x12)
                  lw  x8, 32(x12)
                  lw  x9, 36(x12)
                  lw  x10, 40(x12)
                  lw  x11, 44(x12)
                  lw  x12, 48(x12)
                  lw  x13, 52(x12)
                  lw  x14, 56(x12)
                  lw  x15, 60(x12)
                  lw  x16, 64(x12)
                  lw  x17, 68(x12)
                  lw  x18, 72(x12)
                  lw  x19, 76(x12)
                  lw  x20, 80(x12)
                  lw  x21, 84(x12)
                  lw  x22, 88(x12)
                  lw  x23, 92(x12)
                  lw  x24, 96(x12)
                  lw  x25, 100(x12)
                  lw  x26, 104(x12)
                  lw  x27, 108(x12)
                  lw  x28, 112(x12)
                  lw  x29, 116(x12)
                  lw  x30, 120(x12)
                  lw  x31, 124(x12)
                  addi x12, x12, 124
                  add x13, x12, zero
                  csrrw x12, 0x340, x12
                  mret

ebreak_handler:
                  csrr  x30, mepc
                  addi  x30, x30, 4
                  csrw  mepc, x30
                  lw  x1, 4(x12)
                  lw  x2, 8(x12)
                  lw  x3, 12(x12)
                  lw  x4, 16(x12)
                  lw  x5, 20(x12)
                  lw  x6, 24(x12)
                  lw  x7, 28(x12)
                  lw  x8, 32(x12)
                  lw  x9, 36(x12)
                  lw  x10, 40(x12)
                  lw  x11, 44(x12)
                  lw  x12, 48(x12)
                  lw  x13, 52(x12)
                  lw  x14, 56(x12)
                  lw  x15, 60(x12)
                  lw  x16, 64(x12)
                  lw  x17, 68(x12)
                  lw  x18, 72(x12)
                  lw  x19, 76(x12)
                  lw  x20, 80(x12)
                  lw  x21, 84(x12)
                  lw  x22, 88(x12)
                  lw  x23, 92(x12)
                  lw  x24, 96(x12)
                  lw  x25, 100(x12)
                  lw  x26, 104(x12)
                  lw  x27, 108(x12)
                  lw  x28, 112(x12)
                  lw  x29, 116(x12)
                  lw  x30, 120(x12)
                  lw  x31, 124(x12)
                  addi x12, x12, 124
                  add x13, x12, zero
                  csrrw x12, 0x340, x12
                  mret

illegal_instr_handler:
                  csrr  x30, mepc
                  addi  x30, x30, 4
                  csrw  mepc, x30
                  lw  x1, 4(x12)
                  lw  x2, 8(x12)
                  lw  x3, 12(x12)
                  lw  x4, 16(x12)
                  lw  x5, 20(x12)
                  lw  x6, 24(x12)
                  lw  x7, 28(x12)
                  lw  x8, 32(x12)
                  lw  x9, 36(x12)
                  lw  x10, 40(x12)
                  lw  x11, 44(x12)
                  lw  x12, 48(x12)
                  lw  x13, 52(x12)
                  lw  x14, 56(x12)
                  lw  x15, 60(x12)
                  lw  x16, 64(x12)
                  lw  x17, 68(x12)
                  lw  x18, 72(x12)
                  lw  x19, 76(x12)
                  lw  x20, 80(x12)
                  lw  x21, 84(x12)
                  lw  x22, 88(x12)
                  lw  x23, 92(x12)
                  lw  x24, 96(x12)
                  lw  x25, 100(x12)
                  lw  x26, 104(x12)
                  lw  x27, 108(x12)
                  lw  x28, 112(x12)
                  lw  x29, 116(x12)
                  lw  x30, 120(x12)
                  lw  x31, 124(x12)
                  addi x12, x12, 124
                  add x13, x12, zero
                  csrrw x12, 0x340, x12
                  mret

pt_fault_handler:
                  nop

.align 2
mmode_intr_handler:
                  csrr  x30, 0x300 # MSTATUS;
                  csrr  x30, 0x304 # MIE;
                  csrr  x30, 0x344 # MIP;
                  csrrc x30, 0x344, x30 # MIP;
                  lw  x1, 4(x12)
                  lw  x2, 8(x12)
                  lw  x3, 12(x12)
                  lw  x4, 16(x12)
                  lw  x5, 20(x12)
                  lw  x6, 24(x12)
                  lw  x7, 28(x12)
                  lw  x8, 32(x12)
                  lw  x9, 36(x12)
                  lw  x10, 40(x12)
                  lw  x11, 44(x12)
                  lw  x12, 48(x12)
                  lw  x13, 52(x12)
                  lw  x14, 56(x12)
                  lw  x15, 60(x12)
                  lw  x16, 64(x12)
                  lw  x17, 68(x12)
                  lw  x18, 72(x12)
                  lw  x19, 76(x12)
                  lw  x20, 80(x12)
                  lw  x21, 84(x12)
                  lw  x22, 88(x12)
                  lw  x23, 92(x12)
                  lw  x24, 96(x12)
                  lw  x25, 100(x12)
                  lw  x26, 104(x12)
                  lw  x27, 108(x12)
                  lw  x28, 112(x12)
                  lw  x29, 116(x12)
                  lw  x30, 120(x12)
                  lw  x31, 124(x12)
                  addi x12, x12, 124
                  add x13, x12, zero
                  csrrw x12, 0x340, x12
                  mret;

kernel_instr_end: nop
.section .kernel_stack,"aw",@progbits;
.align 2
kernel_stack_start:
.rept 3999
.4byte 0x0
.endr
kernel_stack_end:
.4byte 0x0
