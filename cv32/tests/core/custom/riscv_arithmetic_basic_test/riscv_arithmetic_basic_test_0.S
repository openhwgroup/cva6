.include "user_define.h"
.section .text.start
.globl _start
.section .init
#.include "user_init.s"
.type _start, @function

_start:
    j _start_main

.globl _start_main
.section .text
_start_main:
h0_start:
                  li x13, 0x40001104
                  csrw misa, x13
kernel_sp:        
                  la x17, kernel_stack_end

trap_vec_init:    
                  la x13, mtvec_handler
                  ori x13, x13, 1
                  csrw 0x305, x13 # MTVEC

mepc_setup:       
                  la x13, init
                  csrw mepc, x13
                  j init_machine_mode

init:             
                  li x0, 0x9
                  li x1, 0xf
                  li x2, 0x0
                  li x3, 0x80000000
                  li x4, 0xb
                  li x5, 0x2
                  li x6, 0x3
                  li x7, 0x0
                  li x8, 0xd
                  li x9, 0x1
                  li x10, 0xf44c3f5c
                  li x11, 0x675963c3
                  li x12, 0x5
                  li x13, 0x9
                  li x14, 0xa538e974
                  li x15, 0x0
                  li x16, 0x5ff795f5
                  li x18, 0xf3544e92
                  li x19, 0x25acaf40
                  li x20, 0x80000000
                  li x21, 0x23e17cbd
                  li x22, 0xa
                  li x23, 0x17bf7c33
                  li x24, 0xfdcbdf3
                  li x25, 0x91fa5a2c
                  li x26, 0x1
                  li x27, 0xf4c75d49
                  li x28, 0x80000000
                  li x30, 0xf3ac0b83
                  li x31, 0xca817b99
                  la x29, user_stack_end
main:             li         t0, 0x74ca5029 #start riscv_int_numeric_corner_stream_8
                  li         s9, 0x17b62ec4
                  li         sp, 0x0
                  li         s3, 0xffffffff
                  li         s8, 0x80000000
                  li         a4, 0x80000000
                  li         s4, 0x9e0a8583
                  li         t3, 0xffffffff
                  li         a1, 0x9f14e510
                  li         s0, 0xffffffff
                  divu       s3, a1, a4
                  lui        a4, 944293
                  rem        s0, s0, s3
                  mulh       s9, a1, t0
                  nop
                  addi       s8, sp, -245
                  lui        s3, 956922
                  rem        t0, t0, s0
                  lui        s8, 872052
                  mulhsu     s0, s4, sp
                  nop
                  sub        s4, s0, a4
                  remu       s9, s3, a4
                  sub        a1, a1, sp
                  lui        a4, 569
                  mulhsu     a1, t3, t3
                  auipc      s4, 186335
                  mulhu      a4, s0, s3
                  addi       a4, t3, -1011
                  mul        s0, s4, a1 #end riscv_int_numeric_corner_stream_8
                  li         ra, 0x0 #start riscv_int_numeric_corner_stream_24
                  li         s7, 0x0
                  li         a0, 0x0
                  li         t3, 0x0
                  li         a5, 0xe382873f
                  li         t2, 0x0
                  li         a1, 0xa2871079
                  li         sp, 0x0
                  li         s1, 0x0
                  li         s8, 0x3a5ab929
                  add        t3, t2, a1
                  nop
                  mulh       s1, t3, s7
                  mulhu      a0, a5, t3
                  remu       s7, ra, t2
                  lui        s7, 371537
                  div        s1, ra, t2
                  add        t2, a5, a0
                  div        a1, a1, sp
                  mul        s8, t2, sp
                  div        s1, s7, ra
                  div        ra, ra, s7
                  mulhsu     t3, s1, a1
                  div        a5, a1, s8
                  div        t3, ra, t3
                  div        ra, s7, s8
                  divu       sp, ra, s7 #end riscv_int_numeric_corner_stream_24
                  li         t2, 0x80000000 #start riscv_int_numeric_corner_stream_10
                  li         s6, 0xfa97e3d8
                  li         t5, 0xffffffff
                  li         t6, 0x0
                  li         s8, 0xffffffff
                  li         s10, 0x5915c2ec
                  li         ra, 0xffffffff
                  li         a3, 0xd09a6665
                  li         s4, 0x80000000
                  li         gp, 0x25a7d23d
                  sub        gp, t2, gp
                  rem        s10, gp, t5
                  mulh       t5, t6, t2
                  auipc      s4, 850237
                  mulhu      a3, gp, a3
                  auipc      t2, 531819
                  mul        gp, s10, t2
                  addi       gp, a3, -973
                  mulh       t5, ra, ra
                  div        a3, ra, t2
                  lui        s4, 8729
                  divu       s4, t2, s10
                  auipc      s4, 452461
                  mulhu      t6, ra, t5
                  mulh       t2, s8, s4
                  mul        s10, s8, s4
                  mulhu      t5, s10, t6
                  addi       s4, t6, -223
                  addi       s10, gp, 461
                  nop #end riscv_int_numeric_corner_stream_10
                  li         a4, 0x2381f747 #start riscv_int_numeric_corner_stream_21
                  li         t1, 0x0
                  li         ra, 0x80000000
                  li         a6, 0xffffffff
                  li         s11, 0xffffffff
                  li         a0, 0xffffffff
                  li         s1, 0xb5a4de8b
                  li         a3, 0x5890a63e
                  li         t0, 0xed8f2dc6
                  li         t6, 0xffffffff
                  add        t6, a0, s1
                  mulhu      t6, a3, a3
                  div        t0, ra, t6
                  remu       t1, a0, a3
                  mulhu      a4, ra, t0
                  mulhsu     t1, a4, t1
                  mul        t1, a6, s1
                  mulhsu     ra, s1, a0
                  auipc      ra, 512853
                  addi       t0, a0, -495
                  mulhu      ra, t6, a3
                  mulhsu     a3, t1, t0
                  mul        a6, s1, t6
                  lui        s1, 482122
                  mulhsu     t0, t6, a4
                  add        ra, a4, a3
                  add        a0, ra, a0
                  addi       t0, t0, 517
                  auipc      s11, 585106
                  mulhu      t0, ra, a6
                  addi       t6, a3, 321
                  sub        t1, ra, t6
                  rem        ra, t0, t6
                  remu       a6, a0, a3
                  lui        s11, 177123
                  auipc      ra, 413101
                  divu       a6, s1, s1
                  add        a0, a3, a4 #end riscv_int_numeric_corner_stream_21
                  li         sp, 0xffffffff #start riscv_int_numeric_corner_stream_2
                  li         t3, 0x2b73f9f8
                  li         s1, 0x0
                  li         s7, 0x80000000
                  li         t6, 0x1e734f65
                  li         t1, 0xd7e24b9f
                  li         t2, 0xe46fb7cc
                  li         a4, 0xffffffff
                  li         a1, 0xffffffff
                  li         s3, 0xffffffff
                  nop
                  lui        t3, 230246
                  divu       a1, a1, a4
                  divu       s7, s7, a4
                  add        a4, t2, t1
                  nop
                  mulhsu     a1, t3, s7
                  rem        t2, a4, a4
                  lui        t3, 868536
                  lui        t3, 667372
                  remu       s3, t2, t3
                  sub        t3, t1, s3
                  rem        s7, t6, a4
                  auipc      a1, 556887
                  remu       s3, s3, s7
                  mul        s7, a1, a1
                  auipc      t6, 296009
                  auipc      t1, 302991
                  divu       a1, t3, a1
                  nop
                  divu       t3, t1, t3
                  divu       t2, t2, t1
                  div        a1, t3, t3
                  add        sp, s1, s7
                  lui        t1, 429817
                  mulhu      s3, t1, t3
                  nop
                  sub        s7, s7, sp #end riscv_int_numeric_corner_stream_2
                  li         a1, 0xffffffff #start riscv_int_numeric_corner_stream_6
                  li         a2, 0xffffffff
                  li         s10, 0xa3b524b0
                  li         t3, 0xffffffff
                  li         s9, 0x0
                  li         s0, 0xffffffff
                  li         t0, 0x80000000
                  li         s4, 0x80000000
                  li         s11, 0x0
                  li         tp, 0xa69a9753
                  mulhu      t3, t0, t3
                  lui        s9, 2327
                  mul        s11, s11, t3
                  mulh       tp, a2, s11
                  mul        t3, s9, tp
                  mul        s4, t0, s10
                  mul        s0, a1, a2
                  nop
                  auipc      a1, 297846
                  addi       s9, s9, -986
                  add        s4, t0, s0
                  mulh       s0, t0, a2
                  nop
                  nop
                  addi       s9, s11, 262
                  lui        s11, 484970
                  divu       s11, tp, tp
                  nop
                  remu       t3, s0, s11
                  mulhsu     tp, t0, a1
                  mul        t0, s11, s4
                  add        s0, s11, s10 #end riscv_int_numeric_corner_stream_6
                  li         s9, 0x0 #start riscv_int_numeric_corner_stream_20
                  li         t2, 0x336b6d78
                  li         t3, 0x0
                  li         s10, 0x0
                  li         ra, 0x1c30fb91
                  li         s4, 0x94ddf920
                  li         a2, 0x80000000
                  li         s11, 0x0
                  li         t6, 0x0
                  li         a1, 0xffffffff
                  auipc      s4, 760114
                  mul        s9, a2, s4
                  nop
                  div        ra, s4, ra
                  sub        ra, s4, s9
                  rem        a1, s4, t3
                  mulh       s10, ra, t6
                  add        t3, t3, t6
                  mul        a1, a2, t6
                  mulhsu     t2, s11, s9
                  add        t3, s11, s11
                  remu       s11, ra, s11
                  lui        a1, 623078
                  nop
                  divu       s9, s11, t3
                  divu       s4, s10, s9
                  mulh       s4, ra, t6
                  mulh       t2, s10, a1
                  add        s9, t3, t6
                  mulhu      ra, t2, s10
                  mulhsu     s9, a1, s11
                  auipc      t6, 115126
                  remu       a2, t2, a2
                  rem        t2, s11, t6
                  nop
                  mul        s10, s9, s9
                  remu       s9, t3, t6 #end riscv_int_numeric_corner_stream_20
                  li         t2, 0x0 #start riscv_int_numeric_corner_stream_4
                  li         a4, 0x7225dd5d
                  li         s0, 0x5ab987bc
                  li         gp, 0x824631b2
                  li         a2, 0xee2f578f
                  li         a6, 0x1becda41
                  li         a0, 0xd2786bb2
                  li         sp, 0x6a89e7aa
                  li         s9, 0xb2a81291
                  li         s1, 0x0
                  sub        a4, a0, a6
                  div        s1, a4, sp
                  mulhsu     a6, s1, gp
                  divu       a4, a2, a4
                  mulh       a6, a6, s1
                  mulhu      s0, s1, sp
                  lui        s0, 637918
                  remu       a4, s0, s0
                  mul        a2, a6, s1
                  divu       t2, s1, s9
                  nop
                  add        gp, a0, gp
                  sub        s0, t2, t2
                  addi       a6, s9, 749
                  add        a2, s1, s9
                  lui        a2, 125758
                  addi       a6, s0, 51 #end riscv_int_numeric_corner_stream_4
                  li         s4, 0x0 #start riscv_int_numeric_corner_stream_31
                  li         gp, 0x0
                  li         s1, 0x80000000
                  li         t6, 0x0
                  li         sp, 0x0
                  li         a0, 0x0
                  li         a6, 0x0
                  li         s7, 0xf767bb2e
                  li         s10, 0x80000000
                  li         a5, 0x80000000
                  mulh       gp, a5, a0
                  add        s7, a0, sp
                  nop
                  div        s7, a0, s10
                  divu       s4, a0, s4
                  mulhsu     a5, a6, s10
                  add        s10, s10, s10
                  divu       a5, sp, sp
                  rem        a5, t6, a5
                  remu       s4, sp, t6
                  rem        s1, s1, s4
                  auipc      s10, 963800
                  div        s1, t6, gp
                  divu       s1, s7, s7
                  remu       s7, t6, a0
                  mulh       s1, s7, gp
                  div        s1, a6, a0
                  nop
                  addi       a5, s1, 484
                  mul        t6, s4, a6
                  mulhu      s10, s7, s10
                  auipc      s4, 872518 #end riscv_int_numeric_corner_stream_31
                  li         a3, 0xfc3a27bf #start riscv_int_numeric_corner_stream_38
                  li         tp, 0x80000000
                  li         s7, 0x0
                  li         a5, 0x1136f16c
                  li         t5, 0x0
                  li         t2, 0x1cfc0352
                  li         gp, 0x80000000
                  li         t6, 0x22f9d31d
                  li         a6, 0x80000000
                  li         a0, 0x0
                  addi       a0, a3, 451
                  nop
                  divu       s7, a6, a5
                  divu       s7, t5, s7
                  addi       tp, a0, 703
                  rem        s7, a6, a3
                  mulhu      t5, t5, s7
                  mulhu      a5, t6, t2
                  divu       s7, t5, gp
                  sub        tp, a6, a6
                  lui        a0, 780187
                  divu       t5, t6, a3
                  remu       gp, a6, a5
                  mulhsu     t6, a0, t6
                  add        a3, s7, a5
                  add        s7, t5, a5
                  remu       a0, a5, a3
                  remu       t2, s7, tp
                  sub        t5, a0, t6
                  nop
                  remu       t6, tp, a5
                  nop
                  mulhsu     t6, tp, t6
                  add        a5, a3, gp
                  lui        t5, 220690
                  addi       a5, tp, 132
                  lui        gp, 137987
                  auipc      t2, 741535 #end riscv_int_numeric_corner_stream_38
                  li         sp, 0xffffffff #start riscv_int_numeric_corner_stream_15
                  li         t1, 0x0
                  li         s1, 0x277ec460
                  li         a4, 0x80000000
                  li         s5, 0xffffffff
                  li         s3, 0x0
                  li         tp, 0x80000000
                  li         s8, 0xffffffff
                  li         s0, 0x0
                  li         a6, 0x80000000
                  nop
                  mulh       s8, tp, s3
                  divu       a4, tp, t1
                  divu       s3, s1, t1
                  div        t1, s1, sp
                  mul        s8, t1, a4
                  mulhu      s1, s3, t1
                  rem        s1, sp, s8
                  mulhu      a6, s0, a4
                  divu       s3, tp, a6
                  mulhsu     s5, a6, s8
                  lui        a4, 618050
                  remu       s8, s5, s0
                  div        t1, s8, sp
                  lui        s5, 200101
                  sub        s0, a4, s0
                  auipc      s1, 40220
                  mul        s1, s3, a6 #end riscv_int_numeric_corner_stream_15
                  li         s9, 0xffffffff #start riscv_int_numeric_corner_stream_28
                  li         a3, 0x0
                  li         t0, 0x0
                  li         t2, 0xc72e7f1a
                  li         sp, 0x0
                  li         a0, 0x80000000
                  li         gp, 0xc6569c02
                  li         t1, 0x0
                  li         s5, 0x0
                  li         a5, 0xd2b4e84f
                  mul        t1, a0, a0
                  mul        t0, a3, t1
                  lui        gp, 124302
                  remu       sp, gp, sp
                  divu       gp, t1, a0
                  divu       t0, s9, a3
                  mul        gp, t2, t1
                  addi       t0, sp, 1022
                  mulhsu     a3, a0, a3
                  auipc      s9, 175972
                  nop
                  addi       t2, gp, 963
                  mulhsu     s5, a0, a0
                  rem        t1, t0, gp
                  addi       t1, sp, 294
                  auipc      a0, 783086
                  lui        t2, 1041065
                  add        sp, s9, t0
                  mulh       t2, gp, s9
                  lui        t2, 776872 #end riscv_int_numeric_corner_stream_28
                  li         s3, 0x80000000 #start riscv_int_numeric_corner_stream_1
                  li         s8, 0x0
                  li         tp, 0xffffffff
                  li         s10, 0xe7fbc04e
                  li         sp, 0xffffffff
                  li         s1, 0xffffffff
                  li         gp, 0xffffffff
                  li         a2, 0x0
                  li         a3, 0x80000000
                  li         s7, 0x0
                  mul        s8, s3, gp
                  mul        s1, s1, a2
                  addi       sp, gp, 1020
                  remu       s10, a3, s8
                  mulh       s1, s8, s8
                  remu       s3, s3, sp
                  mulh       s3, gp, s7
                  add        tp, tp, s10
                  mulh       s10, sp, s10
                  remu       a3, a2, a2
                  nop
                  lui        s1, 72439
                  add        s3, s8, a3
                  auipc      a2, 787280
                  auipc      s7, 708628
                  remu       a3, s8, s8
                  add        a2, s10, tp
                  sub        gp, sp, s10
                  rem        tp, s1, s8
                  mulhu      s7, s8, s7
                  mulhu      s8, s7, s7
                  auipc      s10, 893484
                  addi       sp, tp, -364
                  rem        s8, a3, s3
                  remu       a3, s7, sp
                  sub        sp, s7, a2 #end riscv_int_numeric_corner_stream_1
                  li         a4, 0x8c85bcc0 #start riscv_int_numeric_corner_stream_35
                  li         s0, 0xffffffff
                  li         a5, 0x0
                  li         s4, 0x0
                  li         s5, 0xffffffff
                  li         s7, 0x0
                  li         a1, 0x80000000
                  li         t6, 0x80000000
                  li         tp, 0x0
                  li         a3, 0x80000000
                  lui        s7, 231264
                  add        s5, a5, s7
                  nop
                  div        s0, a5, tp
                  sub        a3, s0, s0
                  divu       t6, s7, s4
                  mulh       a5, t6, a3
                  addi       s0, a1, -596
                  mulhsu     s4, a5, tp
                  mulhu      tp, a3, a3
                  remu       s4, a1, a3
                  mul        s5, a3, s0
                  divu       s0, a5, s0
                  mulhu      a3, a3, a3
                  auipc      s0, 487820
                  auipc      t6, 512324
                  add        a1, a4, s5
                  mulh       a5, tp, s0 #end riscv_int_numeric_corner_stream_35
                  li         s3, 0x27fe3f5b #start riscv_int_numeric_corner_stream_29
                  li         s0, 0x80000000
                  li         t3, 0x0
                  li         tp, 0x6da86f48
                  li         a4, 0xffffffff
                  li         a2, 0x80000000
                  li         a5, 0x874f2132
                  li         s11, 0x80000000
                  li         t6, 0xffffffff
                  li         a1, 0x80000000
                  addi       s3, a2, -715
                  mulhsu     a1, tp, s0
                  div        a5, tp, a4
                  mul        a5, s11, a5
                  divu       a1, s11, a1
                  addi       a1, s11, 638
                  mulhsu     s0, a5, a1
                  addi       t6, a5, 781
                  remu       t6, t6, a4
                  div        s0, s11, a5
                  mul        s3, t3, a2
                  mulhu      s11, a4, tp
                  nop
                  divu       t3, t6, s11
                  auipc      s11, 123759
                  mul        s11, s0, a5
                  rem        s0, s3, tp
                  lui        s0, 776255
                  div        a5, t6, t3
                  mul        tp, a4, s11
                  remu       tp, t3, s3
                  sub        t3, a1, s0
                  mul        s3, a4, a4
                  addi       tp, a4, -326
                  add        a5, s11, s3
                  add        a2, s0, s11
                  rem        a4, tp, t3 #end riscv_int_numeric_corner_stream_29
                  li         tp, 0x0 #start riscv_int_numeric_corner_stream_13
                  li         a6, 0x80000000
                  li         s1, 0xffffffff
                  li         t1, 0x2cb6ae5b
                  li         t3, 0xffffffff
                  li         s4, 0x80000000
                  li         s0, 0x80000000
                  li         s10, 0x0
                  li         a3, 0x0
                  li         gp, 0x80000000
                  auipc      t3, 618995
                  lui        tp, 529808
                  lui        tp, 128553
                  mulhu      s10, t1, a3
                  auipc      a3, 173485
                  div        s0, s4, t3
                  remu       s1, s1, s10
                  nop
                  divu       s0, a6, t1
                  add        t3, t3, s4
                  div        t3, s1, s0
                  div        s10, s10, s0
                  div        s1, t3, s10
                  mulh       a6, a3, s0
                  addi       t1, s10, -325
                  nop
                  mulhu      s10, t1, s4
                  auipc      s10, 188404 #end riscv_int_numeric_corner_stream_13
                  li         a0, 0x80000000 #start riscv_int_numeric_corner_stream_0
                  li         s4, 0x80000000
                  li         tp, 0x0
                  li         s10, 0xffffffff
                  li         sp, 0x80000000
                  li         s9, 0xffffffff
                  li         t6, 0x0
                  li         s5, 0x10636b86
                  li         gp, 0x80000000
                  li         s3, 0xffffffff
                  mulh       s9, tp, s3
                  addi       gp, gp, -560
                  mulhu      s10, s4, s10
                  mulhsu     t6, sp, t6
                  add        t6, tp, gp
                  nop
                  mul        a0, gp, s9
                  remu       tp, sp, s4
                  divu       sp, s10, t6
                  addi       gp, s3, -246
                  mulhsu     s4, s9, t6
                  nop
                  lui        tp, 761768
                  rem        s5, tp, a0
                  auipc      s5, 554526
                  divu       s9, s3, sp
                  mul        gp, a0, t6
                  nop
                  nop
                  auipc      t6, 669743
                  auipc      s9, 800513 #end riscv_int_numeric_corner_stream_0
                  sll        sp, s0, s7
                  c.srai     s1, 21
                  c.slli     a0, 7
                  mulhsu     t2, zero, s7
                  c.or       a5, a4
                  mulhsu     s7, zero, s0
                  xori       s4, s8, -584
                  srl        s0, s5, s0
                  sltu       a4, a6, a5
                  remu       ra, s1, a2
                  c.and      a0, a1
                  xori       a4, s1, -663
                  addi       s1, t5, -290
                  c.sub      a2, a2
                  add        a2, s4, a1
                  c.xor      a3, a2
                  c.slli     a2, 5
                  nop
                  auipc      s9, 496362
                  slt        ra, s6, ra
                  divu       tp, s6, tp
                  mul        gp, s2, a1
                  sltiu      s11, t3, -164
                  c.add      a6, ra
                  rem        s3, t5, s0
                  c.srli     s1, 9
                  srl        zero, t2, a6
                  divu       s5, ra, s2
                  c.and      a5, a1
                  rem        s5, a1, s3
                  c.addi     a5, -1
                  slli       t1, zero, 0
                  sll        t0, t1, s8
                  ori        s10, a3, 813
                  slti       s5, a3, 749
                  sltiu      s9, a3, 884
                  addi       s1, s4, 854
                  c.addi16sp sp, -16
                  mulh       a2, s7, sp
                  or         s5, gp, s10
                  srai       a4, zero, 0
                  sltiu      t2, s2, -1003
                  and        s10, a3, s3
                  c.nop
                  c.li       a2, -1
                  c.nop
                  c.nop
                  auipc      a6, 904110
                  c.li       s4, -1
                  divu       t0, s2, a5
                  srli       s5, s7, 23
                  sll        s10, s5, gp
                  c.mv       ra, a1
                  sra        zero, t3, s2
                  srli       gp, t3, 28
                  c.add      a3, a4
                  lui        a3, 657184
                  c.add      s4, a7
                  c.srli     a3, 27
                  c.lui      tp, 29
                  rem        s6, t1, s8
                  nop
                  mulhu      s7, s6, s8
                  mul        t2, s9, a4
                  mulh       a0, a0, s1
                  divu       s0, a3, s10
                  rem        tp, a6, a6
                  rem        sp, s2, t2
                  mulh       t1, a1, t5
                  c.li       a2, -1
                  xori       s5, s5, 949
                  auipc      a0, 501539
                  mulh       t1, t1, t0
                  slli       a1, s9, 25
                  add        t5, s9, tp
                  c.sub      a2, a5
                  nop
                  c.and      a0, s1
                  sltiu      s0, s1, 773
                  c.xor      a0, a4
                  sltu       t2, a6, t0
                  c.add      s8, t1
                  c.srai     a1, 14
                  mulhsu     a3, t0, sp
                  divu       s6, t6, t1
                  c.and      s1, a3
                  c.nop
                  c.srli     a0, 14
                  c.nop
                  c.nop
                  divu       zero, a6, s1
                  mulhu      sp, gp, t5
                  srl        s4, a6, s3
                  divu       a5, zero, sp
                  lui        t0, 312897
                  srl        a4, a3, ra
                  c.or       s0, a5
                  sll        s1, a6, t1
                  add        a2, a7, gp
                  mulhsu     sp, gp, t1
                  mulh       t2, zero, tp
                  c.mv       a1, a3
                  slti       s5, s5, -683
                  or         s9, a5, a3
                  nop
                  div        t6, ra, t5
                  srl        s10, t1, a7
                  c.xor      a3, a4
                  c.slli     ra, 12
                  rem        t5, a1, a7
                  c.add      s10, s5
                  srai       t1, a7, 17
                  nop
                  c.sub      a2, s1
                  sltiu      gp, t1, 552
                  c.slli     s9, 4
                  c.or       s0, s0
                  or         s1, s3, zero
                  slt        a2, t0, a6
                  mul        zero, s11, a2
                  c.srai     a1, 23
                  c.xor      a5, a0
                  ori        a2, s1, 617
                  sra        s3, s7, t6
                  nop
                  slt        t6, t4, s2
                  div        s0, t5, a7
                  remu       s6, s9, s2
                  mulhsu     s0, s10, s9
                  lui        s6, 39458
                  c.addi     t2, 14
                  and        a2, t0, s7
                  lui        s3, 223541
                  and        s3, s8, t6
                  slt        s4, s9, s3
                  c.sub      a1, a4
                  srai       s5, s10, 26
                  c.add      s7, s6
                  slt        s0, t1, a3
                  c.addi     t5, -1
                  c.addi     s9, 14
                  mulhsu     s4, a4, a6
                  c.slli     s6, 4
                  c.xor      s1, s0
                  sra        ra, t3, s2
                  andi       s10, gp, 291
                  divu       t2, s9, t3
                  c.addi4spn a1, sp, 368
                  or         s1, s0, s2
                  c.nop
                  c.add      s0, sp
                  addi       t3, t5, 757
                  c.add      s5, t3
                  remu       sp, s8, a7
                  c.addi     s8, 2
                  xori       s4, a1, 427
                  nop
                  c.add      t6, s11
                  add        s9, t0, a7
                  divu       gp, s4, s5
                  nop
                  c.srli     a4, 8
                  auipc      t1, 942413
                  xori       s6, s11, -325
                  c.li       s8, 27
                  c.xor      a4, a5
                  rem        a5, a1, a6
                  c.addi16sp sp, 416
                  c.addi4spn a4, sp, 864
                  sltu       a2, s5, t4
                  add        ra, t0, s4
                  rem        t2, s7, a5
                  rem        s6, s7, s1
                  sub        a5, t4, a1
                  c.sub      a3, a3
                  c.srli     a1, 17
                  ori        s6, s0, -376
                  auipc      a4, 940337
                  remu       s10, ra, s8
                  c.srli     a4, 9
                  ori        s5, gp, 355
                  add        a1, a4, tp
                  nop
                  c.add      a6, t0
                  slt        a2, tp, t0
                  andi       t0, a2, 44
                  sra        a2, a1, t6
                  c.or       a0, a2
                  c.srli     a5, 6
                  c.srai     a3, 5
                  ori        s5, t5, -130
                  c.mv       gp, a0
                  slti       a6, a4, 270
                  c.and      a0, a3
                  srli       ra, zero, 5
                  xori       t6, a3, -608
                  c.or       a4, s1
                  nop
                  c.andi     s0, 6
                  nop
                  nop
                  mulhsu     gp, t4, s8
                  c.srli     a4, 10
                  addi       s4, a7, -113
                  c.xor      a2, a2
                  xori       t3, t6, 108
                  or         t1, tp, a6
                  mulhu      t5, t2, t5
                  sub        s1, a3, a7
                  sltu       ra, t5, a1
                  c.add      a4, s2
                  c.sub      a2, a2
                  sltu       t3, s1, s9
                  c.and      a5, s1
                  auipc      a4, 310601
                  srai       t2, t2, 30
                  c.sub      a0, a2
                  rem        gp, a3, a7
                  remu       t2, t2, t6
                  sra        s3, s9, a7
                  c.addi4spn a2, sp, 560
                  or         t5, zero, t4
                  c.li       t3, -1
                  c.addi16sp sp, 112
                  sra        s10, s5, t0
                  nop
                  mulhsu     s8, s7, a3
                  auipc      a0, 521277
                  mulh       s5, s8, s2
                  div        a1, gp, s3
                  sub        s8, a4, s1
                  c.slli     t1, 23
                  c.or       a5, a5
                  c.addi16sp sp, -16
                  divu       tp, a3, gp
                  addi       t3, s8, -155
                  mulh       tp, t6, t1
                  or         a3, s11, sp
                  mulh       a2, s6, a6
                  slli       a4, gp, 3
                  c.addi16sp sp, -16
                  c.nop
                  add        a0, a7, tp
                  auipc      zero, 556478
                  c.mv       s4, ra
                  ori        t6, t1, -660
                  divu       t2, t3, s10
                  xori       a1, t1, -107
                  c.or       a4, a4
                  addi       s5, s5, 509
                  mulhu      s11, s9, t6
                  c.add      t5, s5
                  slt        t1, t4, gp
                  c.lui      t3, 21
                  lui        s8, 1044541
                  mulhsu     s1, s2, s1
                  c.add      s11, t3
                  c.and      a3, a2
                  c.addi4spn a2, sp, 816
                  divu       t1, gp, t5
                  c.and      a3, a1
                  lui        a2, 93566
                  xori       a3, a3, 227
                  mulh       a2, s0, s2
                  mulh       s7, a6, s3
                  srai       a1, zero, 23
                  c.andi     s0, -1
                  c.addi16sp sp, -16
                  sub        s5, sp, a7
                  c.li       s7, 22
                  c.add      t3, s5
                  slli       zero, s2, 18
                  auipc      ra, 72815
                  xor        s6, s9, sp
                  mulhu      a4, s8, ra
                  slli       s10, s1, 9
                  c.addi4spn a5, sp, 416
                  c.nop
                  ori        t5, s6, 656
                  c.lui      t1, 13
                  or         s11, s9, tp
                  c.addi4spn a4, sp, 800
                  mulhsu     gp, s6, t6
                  rem        t0, t2, s2
                  c.nop
                  rem        a5, a0, a0
                  slti       s10, a0, 938
                  srli       t2, ra, 6
                  slli       s0, s8, 24
                  slli       zero, ra, 1
                  mulh       ra, s8, t3
                  addi       a2, t0, -397
                  lui        ra, 134130
                  rem        t1, t4, s5
                  xor        s11, t0, s11
                  c.nop
                  c.mv       tp, s1
                  sll        a6, s4, t6
                  ori        s9, a4, 592
                  srli       s9, sp, 12
                  and        s5, s1, t2
                  c.add      a3, a6
                  xor        a4, a4, a2
                  auipc      s11, 791466
                  c.addi16sp sp, 144
                  mulhu      t2, s5, t2
                  c.or       a2, a5
                  andi       s10, a2, 972
                  sra        a1, s4, zero
                  mulh       t0, tp, sp
                  c.add      s0, s9
                  c.addi4spn a5, sp, 144
                  c.srli     a1, 26
                  nop
                  c.nop
                  addi       t3, a4, -833
                  ori        s5, ra, -330
                  sltiu      tp, t0, -678
                  c.add      gp, t6
                  lui        a6, 814419
                  mulhsu     t5, a5, sp
                  c.add      a6, s11
                  c.sub      a0, a2
                  sub        a2, s8, s8
                  xori       s4, gp, 247
                  c.nop
                  c.and      s1, a3
                  or         ra, gp, s7
                  mulhu      t3, s6, a6
                  c.mv       s11, a4
                  lui        ra, 721346
                  add        gp, a7, t2
                  and        a0, tp, s6
                  c.lui      t0, 26
                  c.lui      ra, 1
                  auipc      a3, 223153
                  c.nop
                  c.addi4spn a0, sp, 480
                  sub        s8, gp, a7
                  slt        a2, s0, t4
                  and        a2, a6, s10
                  c.slli     s9, 11
                  c.addi     a4, -1
                  slti       a0, s9, -999
                  div        a3, t1, gp
                  li         s6, 0xffffffff #start riscv_int_numeric_corner_stream_3
                  li         t1, 0xffffffff
                  li         s0, 0x80000000
                  li         t2, 0x80000000
                  li         a5, 0x7d1885cd
                  li         tp, 0xbcff6786
                  li         t5, 0x80000000
                  li         s9, 0x80000000
                  li         s5, 0xffffffff
                  li         a1, 0x0
                  mul        t5, a1, s9
                  addi       tp, a5, 23
                  remu       s9, a5, s0
                  nop
                  auipc      s9, 275118
                  nop
                  mulh       a1, t1, tp
                  div        tp, a5, a5
                  rem        a1, s6, t1
                  add        a5, t1, t2
                  mul        a5, s5, t1
                  mulhsu     s9, t2, s6
                  divu       t5, t5, s6
                  nop
                  mulhsu     a1, s9, a5
                  remu       s6, s6, a5
                  mulhu      s9, tp, t5
                  mulh       s5, tp, t1
                  nop
                  auipc      tp, 35344
                  auipc      a5, 338398 #end riscv_int_numeric_corner_stream_3
                  c.addi     s10, 22
                  mul        s11, s0, t6
                  c.addi4spn a1, sp, 960
                  and        a2, t6, s9
                  mulh       s7, t3, s5
                  lui        s10, 646723
                  mulh       ra, sp, s10
                  xori       s7, a5, 868
                  c.add      s6, t3
                  andi       t2, s5, 408
                  srli       t5, s2, 23
                  c.lui      tp, 24
                  c.srai     a5, 22
                  addi       a1, a6, -288
                  srai       t5, s1, 24
                  srli       a1, t5, 5
                  divu       t1, s5, s9
                  lui        a5, 986812
                  c.lui      a4, 16
                  c.xor      a3, s1
                  c.addi     a5, -1
                  xori       t1, a3, -541
                  mul        a5, s4, tp
                  div        s3, gp, t1
                  or         t5, zero, a2
                  sltiu      s0, t2, 563
                  sltu       s1, a0, t6
                  c.sub      s1, s0
                  nop
                  mulh       a6, zero, s5
                  srl        a3, a1, s8
                  slti       s5, ra, 481
                  or         sp, a3, t5
                  sll        t2, t0, s5
                  divu       a0, s6, s0
                  divu       t3, s7, t1
                  c.andi     s0, 26
                  sltu       s1, s5, s6
                  c.nop
                  andi       t5, a7, 566
                  c.addi16sp sp, -16
                  sltiu      a5, t1, 14
                  c.addi16sp sp, -16
                  or         s10, t2, s5
                  c.or       a5, a5
                  andi       ra, a0, -671
                  c.mv       t6, a5
                  c.nop
                  slli       t5, t4, 29
                  mul        a0, s10, t4
                  c.srli     s0, 5
                  mulhsu     s8, s7, a4
                  rem        sp, s6, a7
                  remu       s11, a0, s8
                  c.lui      s4, 30
                  mulhsu     a2, t3, gp
                  c.mv       a3, t3
                  c.and      a2, a5
                  or         s7, a5, s4
                  mulhsu     s1, a5, s7
                  c.lui      s8, 6
                  slt        t6, s3, a5
                  srai       a0, a2, 0
                  xori       s5, ra, -949
                  rem        s7, s6, a6
                  divu       sp, t3, a0
                  srli       ra, t3, 14
                  c.xor      a5, a4
                  c.srai     a0, 28
                  add        t3, s7, a4
                  srl        s9, s10, a4
                  sltiu      s7, a7, 993
                  c.nop
                  c.srli     a5, 11
                  c.xor      a5, a2
                  sltu       s10, zero, a3
                  c.add      s5, t4
                  srl        t5, s11, s11
                  mulhu      a3, t2, t1
                  addi       a1, t3, -69
                  c.li       s11, -1
                  sltu       s9, s9, s1
                  ori        t3, tp, 789
                  divu       s5, a1, t1
                  srl        s11, a3, s1
                  slli       a4, s3, 19
                  c.xor      a4, s0
                  c.or       a0, a5
                  add        s6, a0, a0
                  srli       t2, s4, 8
                  auipc      a2, 1036680
                  c.mv       s11, sp
                  ori        a6, s9, -1001
                  c.or       a4, a0
                  c.addi4spn a3, sp, 976
                  c.addi4spn a1, sp, 880
                  c.mv       t1, s2
                  c.nop
                  slli       ra, ra, 1
                  srai       sp, t3, 20
                  sltiu      t5, a2, -361
                  slli       s8, t1, 6
                  nop
                  c.addi     s5, -1
                  srli       s0, s5, 15
                  srai       gp, s11, 4
                  c.li       s5, -1
                  c.sub      a4, a2
                  sltu       s9, s11, a4
                  c.add      s9, s1
                  slt        t5, s9, s8
                  div        zero, t5, t3
                  srl        a1, t5, t4
                  nop
                  slt        s4, s6, gp
                  slt        t1, a6, t3
                  c.or       a2, a2
                  c.srai     a3, 21
                  c.add      t5, a7
                  srli       t1, s4, 14
                  c.addi16sp sp, -16
                  c.xor      a2, a5
                  or         t2, t6, zero
                  c.nop
                  srl        zero, a3, s0
                  mulhsu     s5, t0, a6
                  slli       ra, t4, 31
                  c.xor      a3, s1
                  auipc      t0, 619527
                  or         zero, t4, s9
                  c.xor      s0, s0
                  or         a6, s11, t5
                  c.addi4spn a3, sp, 752
                  slt        t1, a6, s11
                  or         s5, s7, s5
                  divu       t6, a0, t5
                  rem        s5, t6, t1
                  c.srli     a2, 26
                  srai       a3, t1, 9
                  c.or       a0, s1
                  c.srai     a1, 22
                  c.sub      s0, a5
                  xori       a4, a7, -551
                  c.li       s8, -1
                  mul        gp, s6, s4
                  c.slli     s5, 15
                  lui        s5, 567662
                  c.li       s5, 18
                  slli       s4, a6, 8
                  c.addi     t1, -1
                  mul        t2, ra, s1
                  c.add      s1, a3
                  addi       a2, a1, -31
                  andi       a2, s9, -2
                  xor        zero, gp, a4
                  c.sub      a4, s1
                  and        t6, s2, s6
                  c.li       t1, -1
                  and        s7, s8, a5
                  sll        a2, a0, t3
                  xor        a0, t3, t3
                  c.addi16sp sp, 304
                  xor        a2, a7, t0
                  c.li       tp, 10
                  sltiu      s0, t1, -75
                  c.lui      t6, 11
                  c.nop
                  div        a2, a0, s0
                  remu       s9, t3, s5
                  c.lui      gp, 26
                  c.addi     s10, 31
                  c.nop
                  c.srai     a4, 4
                  slti       t1, t6, -161
                  or         zero, s7, t1
                  c.xor      a5, a3
                  and        t0, t2, t5
                  addi       s7, t3, -697
                  c.addi     a6, 8
                  c.li       s10, -1
                  divu       gp, a1, t3
                  remu       a4, t4, s4
                  sltiu      s10, a4, 859
                  mulh       s6, s11, s0
                  ori        a3, t0, 130
                  andi       s1, a4, -586
                  lui        s1, 714562
                  auipc      a0, 896688
                  or         a5, a0, ra
                  c.srai     a5, 27
                  li         a6, 0x0 #start riscv_int_numeric_corner_stream_36
                  li         s8, 0x0
                  li         a2, 0xffffffff
                  li         s9, 0x0
                  li         s5, 0xffffffff
                  li         t2, 0x0
                  li         s1, 0x0
                  li         s11, 0xffffffff
                  li         t3, 0x0
                  li         a5, 0x0
                  add        t2, s5, s1
                  lui        s5, 800941
                  auipc      a6, 346199
                  mulh       a6, t3, t2
                  add        t3, t2, s11
                  mulhsu     a2, s11, s1
                  sub        s9, t2, t3
                  rem        s11, s5, a5
                  mulh       s8, s9, a6
                  add        s8, t2, s1
                  mul        s11, s5, a6
                  mulhu      s9, a2, s8
                  add        a6, s1, t2
                  auipc      a6, 490408
                  lui        s11, 340341
                  div        s5, s1, a5
                  mulhu      a6, s8, s11
                  remu       s11, a6, t2
                  sub        s11, t3, s5
                  auipc      s8, 334473
                  rem        s1, s11, t2
                  mulhu      a2, s8, s11
                  divu       t3, s1, s5
                  addi       t3, s9, -705
                  sub        a2, a6, a5
                  mulhsu     a5, t3, t2
                  mulhu      a5, s5, t3
                  lui        s5, 978323
                  mul        s1, a6, s9
                  remu       s1, t2, s5 #end riscv_int_numeric_corner_stream_36
                  c.or       s0, a2
                  c.srai     s0, 28
                  xori       s7, s6, 448
                  c.addi     a3, -1
                  ori        t0, ra, 671
                  c.sub      a4, a4
                  sll        s11, s9, t4
                  c.srli     a5, 5
                  slt        a5, a1, s7
                  sltiu      a0, a4, 225
                  divu       zero, s2, zero
                  mulhsu     t2, t3, a3
                  c.or       s1, s0
                  andi       s8, t6, -129
                  or         zero, t4, t2
                  auipc      s8, 93161
                  srai       zero, s8, 8
                  c.srai     a5, 17
                  xori       t5, t3, 396
                  c.or       a5, a1
                  and        s4, t4, zero
                  c.srli     s1, 28
                  slti       a5, ra, 481
                  sra        s8, t1, a2
                  nop
                  remu       s4, tp, t3
                  c.srai     a2, 16
                  xori       tp, a2, 629
                  c.and      a4, a5
                  sll        s6, a0, sp
                  xori       t0, s2, 806
                  andi       a1, s3, 707
                  slli       t6, ra, 8
                  c.and      a3, a4
                  srl        a3, a6, s7
                  c.and      s0, a3
                  remu       zero, s11, a3
                  slti       a5, t3, 1020
                  remu       s9, s4, s4
                  c.addi16sp sp, -16
                  nop
                  c.slli     a5, 23
                  mulh       s7, s1, a6
                  c.srai     a0, 18
                  or         ra, t0, t3
                  rem        s6, a2, s10
                  c.li       s7, 0
                  sltiu      a3, a1, -709
                  c.srai     a3, 19
                  c.slli     sp, 17
                  srai       a1, s9, 24
                  addi       s1, s11, 660
                  c.mv       a3, a1
                  c.srli     s1, 11
                  c.xor      a0, a4
                  sub        t3, a6, a7
                  slli       a6, s11, 29
                  srl        t6, s6, ra
                  remu       a2, a1, s2
                  c.slli     a1, 19
                  mulh       t1, s11, sp
                  rem        s11, t0, s11
                  c.and      a2, a5
                  c.sub      a1, a1
                  c.nop
                  or         s1, t4, tp
                  c.andi     a0, 31
                  xori       a6, gp, -479
                  remu       s5, s2, a2
                  add        a2, t2, s8
                  c.addi     sp, 20
                  c.add      a0, s4
                  c.srai     a5, 9
                  c.srli     s1, 28
                  srli       s1, t5, 15
                  div        s8, s10, t1
                  c.mv       s1, a3
                  srli       s9, s4, 22
                  andi       s6, t1, 347
                  auipc      s11, 459446
                  rem        s7, tp, t3
                  nop
                  c.addi16sp sp, -16
                  lui        s9, 910443
                  mulhsu     s11, s2, t4
                  lui        s6, 998916
                  c.addi4spn a4, sp, 976
                  c.mv       t1, s3
                  mul        a1, s1, tp
                  sll        zero, a0, t0
                  mulhu      a0, t4, t1
                  c.addi     t3, -1
                  c.and      a0, s0
                  rem        gp, a0, s0
                  c.li       a4, 9
                  and        s7, t2, ra
                  c.srli     a3, 30
                  c.srai     s0, 5
                  c.addi4spn a0, sp, 224
                  ori        sp, s2, -473
                  sltiu      sp, s11, -106
                  c.srli     s1, 21
                  add        s5, s3, a1
                  c.andi     a2, 4
                  ori        a2, s11, -962
                  c.addi     s9, 16
                  slli       ra, a0, 15
                  mul        tp, a4, s2
                  c.sub      a0, a1
                  mulhu      t2, t0, t6
                  mulh       a0, t4, s3
                  srli       s8, s10, 27
                  srl        s8, s7, s10
                  c.nop
                  xor        t2, sp, s9
                  mulhu      tp, a7, tp
                  srl        s0, gp, ra
                  c.nop
                  or         a0, s4, a3
                  rem        a5, t6, a3
                  mulh       gp, s9, s10
                  sltu       s4, s11, ra
                  sub        s6, zero, a1
                  xor        a4, s7, a0
                  c.addi     t0, -1
                  c.or       a0, a0
                  c.addi16sp sp, -16
                  c.srli     a1, 22
                  div        a5, t5, gp
                  slli       a4, a0, 15
                  c.addi4spn s0, sp, 160
                  divu       a5, t0, t5
                  c.or       a0, s1
                  xor        a5, a7, a6
                  c.addi     gp, -1
                  mulh       s8, t6, a3
                  sltiu      s3, s2, 477
                  or         a4, a1, ra
                  c.sub      a4, s1
                  c.or       a0, a3
                  c.sub      a5, a5
                  add        zero, s11, zero
                  c.srai     a4, 15
                  slli       a5, a4, 13
                  slt        a1, s8, ra
                  lui        a0, 528963
                  c.or       a2, a0
                  auipc      t5, 517030
                  c.mv       t1, sp
                  xori       a1, sp, -104
                  div        s5, s3, gp
                  slti       t0, t3, 732
                  slti       a6, sp, -630
                  c.srai     s0, 18
                  mulhsu     t3, a1, a3
                  xor        s4, t6, tp
                  srai       a3, s10, 10
                  add        s3, s0, tp
                  c.li       t6, -1
                  sra        a5, s4, a1
                  add        s1, gp, tp
                  sra        s11, s11, t3
                  sltiu      s3, s0, 771
                  c.srai     a3, 13
                  slt        s10, t1, a3
                  c.srai     a3, 26
                  c.and      a3, a4
                  c.slli     s0, 11
                  remu       tp, s5, s7
                  c.slli     t3, 22
                  c.and      a5, a0
                  ori        a2, zero, 865
                  sub        a1, a7, a0
                  slli       s4, t2, 26
                  c.nop
                  c.addi16sp sp, 160
                  c.nop
                  c.addi     t6, 18
                  c.xor      a3, s0
                  and        gp, s9, s0
                  c.mv       s6, t2
                  c.srai     a3, 21
                  c.or       a0, s1
                  c.andi     s0, 10
                  c.li       s10, -1
                  ori        t6, sp, 741
                  c.li       tp, 31
                  srl        t0, t4, t6
                  slli       a1, s5, 31
                  sltiu      s3, a7, 347
                  sltiu      a5, a2, -652
                  srai       s7, s9, 10
                  c.slli     a4, 2
                  slli       s10, a4, 25
                  c.nop
                  c.xor      s1, s0
                  xori       t0, s4, -848
                  sll        t2, a3, a7
                  ori        s9, t2, -460
                  srl        a6, s11, t4
                  and        a6, a7, t2
                  c.sub      a5, a5
                  c.add      t3, t3
                  mulh       s10, s0, s9
                  srl        a0, s2, s4
                  c.or       a0, a3
                  lui        sp, 215998
                  c.or       s0, a3
                  c.sub      a5, a4
                  sll        s0, ra, s4
                  remu       s6, a2, tp
                  srai       a6, s5, 24
                  div        s9, a4, t6
                  c.mv       s4, a0
                  mulh       zero, s5, sp
                  and        s7, s10, s8
                  c.sub      a1, a2
                  remu       s6, a4, a1
                  c.addi4spn a0, sp, 128
                  sll        s10, s11, zero
                  c.nop
                  slt        s9, zero, a1
                  c.xor      s0, a4
                  sltu       zero, t2, ra
                  div        t5, a0, s7
                  sltu       a4, t4, s2
                  nop
                  nop
                  nop
                  sltu       a2, sp, t5
                  srl        s1, s4, sp
                  c.addi4spn s0, sp, 160
                  srl        s11, s2, a5
                  c.xor      a0, a1
                  div        s6, s10, gp
                  sltiu      a2, a2, 734
                  c.srli     a2, 12
                  xor        ra, a4, s4
                  andi       s0, a1, 189
                  c.or       s1, a2
                  c.and      s0, a0
                  slt        s10, s3, s11
                  auipc      t2, 443634
                  c.lui      gp, 2
                  srl        s10, gp, a4
                  c.li       a4, -1
                  or         t2, gp, s8
                  addi       s9, a2, 953
                  c.srli     a4, 13
                  srai       gp, a2, 24
                  c.nop
                  xor        a3, a0, t2
                  srl        t6, s11, s8
                  c.srli     a4, 17
                  lui        t6, 435931
                  ori        a1, s8, 935
                  slli       s8, zero, 25
                  srai       t2, s10, 28
                  auipc      t6, 303576
                  srli       zero, t2, 2
                  xor        s10, a2, s4
                  c.srai     s0, 19
                  and        a3, s10, sp
                  xori       s8, a7, -839
                  nop
                  mul        zero, t0, ra
                  c.addi     s7, -1
                  divu       s7, s8, t3
                  mulh       s7, a4, a3
                  mulh       s0, a4, a1
                  sll        a4, t4, s4
                  auipc      t1, 856625
                  divu       t6, a7, a5
                  c.srli     s1, 25
                  mul        t0, s2, t0
                  and        s1, gp, s7
                  c.addi4spn a3, sp, 32
                  sltu       s3, a3, sp
                  li         sp, 0x80000000 #start riscv_int_numeric_corner_stream_17
                  li         s6, 0x80000000
                  li         s11, 0x80000000
                  li         t5, 0x0
                  li         a2, 0x80000000
                  li         t2, 0xb3a8bf0f
                  li         s5, 0x0
                  li         tp, 0x0
                  li         a3, 0x80000000
                  li         a4, 0x8f612b54
                  mul        t2, s11, t5
                  mulh       t2, a3, tp
                  auipc      s5, 328452
                  lui        s11, 817027
                  add        a2, a4, s5
                  mulh       s11, a4, sp
                  nop
                  remu       s11, s11, s5
                  lui        s5, 267023
                  lui        t5, 82157
                  mulh       t5, s11, a2
                  mulhu      s11, a2, s11
                  div        a4, a4, tp
                  remu       t5, s6, s6
                  add        t2, a2, t5
                  div        t5, s11, a3 #end riscv_int_numeric_corner_stream_17
                  sltiu      a1, s5, 147
                  lui        s10, 829640
                  slt        a3, t2, a4
                  xor        s11, s11, t0
                  auipc      zero, 327077
                  slli       t6, tp, 12
                  srli       zero, t5, 2
                  srli       zero, tp, 22
                  c.mv       s5, a2
                  or         s1, a7, a5
                  c.add      t1, t1
                  sltu       a1, a1, a1
                  c.addi     t6, -1
                  add        t3, s7, s1
                  xor        a5, s10, a7
                  c.addi16sp sp, 352
                  remu       s1, a2, s1
                  c.mv       t0, a0
                  c.srli     a0, 21
                  sub        t5, s7, a3
                  slli       sp, s6, 16
                  c.addi16sp sp, -16
                  div        a6, t1, t5
                  sra        ra, t3, s5
                  xori       s1, a3, 443
                  mul        a4, s6, t3
                  c.andi     a4, 29
                  auipc      a0, 732371
                  or         s1, s1, t2
                  c.xor      s0, s1
                  addi       a4, s11, 653
                  c.andi     a3, 7
                  auipc      ra, 471444
                  c.li       s0, 20
                  c.add      a1, gp
                  xori       sp, s9, 305
                  srl        ra, s9, s7
                  mulhsu     a5, s0, t1
                  srai       gp, a0, 24
                  sltiu      s5, s5, 726
                  c.addi     t6, 4
                  remu       gp, t3, s5
                  c.and      a3, s1
                  mul        s0, a6, s6
                  sll        s1, a7, sp
                  sll        gp, a6, s0
                  c.andi     a0, -1
                  slli       s1, s9, 4
                  div        t6, s11, gp
                  sll        tp, a6, t4
                  slli       ra, gp, 15
                  c.nop
                  c.add      a0, t0
                  xor        gp, gp, a2
                  ori        t6, s11, -122
                  lui        t3, 191291
                  c.and      s0, a4
                  mulhu      s8, t2, s1
                  remu       t5, gp, s3
                  c.mv       s4, s1
                  mul        ra, s11, s1
                  c.lui      s7, 18
                  c.nop
                  xori       gp, s7, 347
                  c.xor      a4, a5
                  slti       t2, t6, -210
                  c.addi4spn s1, sp, 304
                  ori        s9, a2, -461
                  sltiu      s5, a3, -370
                  lui        a4, 182623
                  div        s3, s7, s7
                  sltiu      s8, s6, -316
                  srli       t1, s9, 6
                  c.xor      a3, s0
                  slt        t2, s1, tp
                  mulh       s9, t2, gp
                  remu       s5, a2, s11
                  c.srai     a0, 13
                  c.srai     a4, 12
                  slti       t0, a4, -190
                  andi       s6, a5, 191
                  divu       s8, s7, gp
                  c.srli     a1, 24
                  auipc      tp, 268327
                  srai       s6, a5, 5
                  auipc      s7, 447796
                  div        gp, a6, a6
                  c.li       a1, -1
                  c.nop
                  sub        sp, s11, sp
                  c.addi4spn a0, sp, 192
                  c.li       s5, 30
                  rem        t0, s0, a4
                  c.add      t0, a1
                  c.or       a4, s0
                  slt        sp, a0, s10
                  and        a4, a7, t3
                  c.mv       t0, s6
                  c.sub      a4, a2
                  div        sp, s10, sp
                  lui        t3, 1018579
                  c.li       a3, -1
                  c.slli     a4, 28
                  and        a1, gp, sp
                  srai       a5, t4, 6
                  xori       a0, tp, 438
                  c.and      a4, a1
                  srl        gp, s0, t5
                  c.srli     a1, 30
                  sll        tp, a5, s11
                  ori        a3, zero, -150
                  c.addi16sp sp, -16
                  addi       t2, sp, -424
                  srli       s6, a7, 9
                  divu       s8, gp, s6
                  mulhsu     s5, a6, s1
                  remu       a5, s4, t5
                  slti       zero, t0, -1016
                  divu       ra, s9, s7
                  c.xor      a2, a1
                  c.xor      a3, s0
                  ori        t2, gp, -39
                  xor        s5, a6, ra
                  and        ra, s10, a6
                  div        a1, a1, s4
                  remu       gp, a2, tp
                  ori        t2, s0, -284
                  xor        t3, t4, s4
                  xor        sp, t1, s11
                  and        s5, t2, s2
                  or         s4, a3, s1
                  srl        t1, s7, a0
                  srai       a1, t3, 17
                  addi       tp, t2, 726
                  c.srli     a4, 31
                  c.srai     s0, 20
                  addi       s1, a5, 707
                  c.li       ra, 22
                  divu       s1, s4, a6
                  mul        tp, a5, t4
                  c.srli     a2, 17
                  sll        tp, ra, ra
                  auipc      a1, 493141
                  slt        s11, a3, t1
                  c.li       s7, -1
                  xor        zero, s7, a2
                  c.sub      a4, a5
                  mulhsu     s1, t5, s2
                  sltu       zero, sp, gp
                  c.addi     s0, 27
                  divu       a6, gp, t2
                  c.li       t1, -1
                  c.and      a0, a5
                  sll        s8, s0, s7
                  sltiu      a6, a4, 713
                  c.srli     a2, 21
                  c.srai     s1, 12
                  c.srai     a1, 27
                  or         tp, t2, t0
                  slt        s11, s3, gp
                  auipc      a1, 219484
                  nop
                  c.lui      a5, 7
                  li         s8, 0x1e6646db #start riscv_int_numeric_corner_stream_16
                  li         t0, 0x80000000
                  li         a0, 0x80000000
                  li         a5, 0x0
                  li         s11, 0x80000000
                  li         tp, 0x0
                  li         t5, 0x0
                  li         s6, 0x0
                  li         t6, 0xae71ec16
                  li         s7, 0xffffffff
                  add        s8, s6, a0
                  mulhu      s6, s7, s8
                  div        tp, t0, t6
                  divu       s8, a5, t5
                  remu       t5, tp, t6
                  addi       tp, t6, -878
                  mul        t5, a0, a5
                  mulhsu     s8, t6, t0
                  div        t0, s11, t0
                  rem        s6, t5, a0
                  mulhsu     t5, a0, t5
                  div        a0, t6, tp
                  divu       s11, a0, s6
                  mulhu      t5, s8, a5
                  mulhu      s11, a0, a5
                  mul        a0, t5, s7
                  nop
                  mulhsu     s8, t6, s11
                  rem        t6, t0, t5
                  nop
                  mulhu      s6, s7, tp
                  rem        a0, s11, t5
                  add        t5, a0, s11
                  remu       a0, s11, s7
                  rem        a5, t0, t6
                  mulh       s11, s8, t5
                  addi       s7, t0, 858
                  mulhsu     s8, a5, tp #end riscv_int_numeric_corner_stream_16
                  c.or       s0, a1
                  mulhu      ra, a2, a7
                  c.xor      a5, a4
                  or         s1, t2, s11
                  add        a3, s10, ra
                  slt        t2, s3, t3
                  ori        s8, s3, 845
                  sll        a1, ra, s4
                  c.addi16sp sp, 32
                  mul        t1, a3, s5
                  c.srai     s1, 29
                  c.slli     t1, 5
                  c.xor      s1, a5
                  sltiu      s8, s7, -231
                  div        s7, a5, s0
                  sra        tp, s0, t5
                  c.srai     a4, 22
                  mulhsu     gp, a5, t3
                  remu       a6, s0, t3
                  c.andi     a4, -1
                  c.andi     s1, 0
                  srl        a4, sp, tp
                  c.li       sp, -1
                  mulhsu     a1, s9, s5
                  c.or       s1, s1
                  rem        s9, a1, zero
                  c.lui      a5, 15
                  divu       a5, a6, a1
                  c.srai     s1, 2
                  mulh       t1, s4, s4
                  ori        s8, s8, -622
                  mul        tp, s8, t0
                  c.lui      a0, 17
                  slt        a3, s6, a5
                  ori        t5, a2, 86
                  divu       s1, a4, t6
                  c.slli     ra, 23
                  mulhu      sp, a1, a2
                  addi       zero, a4, 974
                  srl        s1, t1, s11
                  sra        t0, a6, a2
                  mulhsu     s6, a2, a2
                  srl        sp, s2, sp
                  and        zero, s1, s8
                  ori        s9, a6, -111
                  c.addi     a0, -1
                  rem        t1, s8, s7
                  c.srli     a5, 8
                  rem        a1, a5, s4
                  lui        s5, 412628
                  srli       s5, s10, 29
                  xor        s7, a4, s4
                  c.lui      s6, 3
                  rem        t5, a5, sp
                  sll        s4, s9, s1
                  lui        t3, 326735
                  lui        ra, 955184
                  and        s8, t3, tp
                  div        t2, t3, s7
                  xor        t3, t2, s6
                  xor        sp, s5, t5
                  sra        t3, t6, a4
                  divu       s11, t4, s5
                  srl        a0, t4, a0
                  c.andi     a2, -1
                  c.srli     a0, 12
                  slti       s6, a3, -815
                  c.srli     a1, 13
                  ori        gp, t0, 364
                  div        a5, s0, s8
                  slti       s1, t1, -679
                  rem        t2, zero, tp
                  slt        s9, sp, s9
                  c.addi16sp sp, 144
                  mulhu      a3, a6, gp
                  srai       ra, t1, 27
                  c.andi     a3, -1
                  c.srai     a5, 21
                  sra        s10, t6, t1
                  c.lui      ra, 18
                  ori        s0, a4, 325
                  xor        t1, a6, s1
                  srl        gp, t1, s6
                  c.srai     s0, 18
                  c.addi16sp sp, -16
                  or         s5, s3, s1
                  add        gp, t6, s3
                  nop
                  srai       ra, s10, 23
                  divu       a3, t5, s4
                  srli       s3, s2, 27
                  c.sub      a4, s1
                  c.or       a3, a4
                  addi       s8, s6, 143
                  c.addi     s7, 24
                  xori       t3, a4, 123
                  slt        a3, tp, zero
                  sra        s4, s10, s10
                  add        a1, t4, t6
                  c.add      a2, s0
                  rem        s3, s7, s5
                  c.nop
                  add        a1, s9, zero
                  slt        a0, t5, sp
                  sltiu      s3, a7, -894
                  srl        a4, tp, t4
                  mul        s3, a3, s11
                  c.mv       tp, s1
                  c.srai     s1, 25
                  mulhu      s10, gp, gp
                  mulhsu     t0, a1, t3
                  lui        s0, 133849
                  lui        a2, 729969
                  c.srli     a5, 10
                  mulhsu     s8, gp, a5
                  xori       t2, t4, -901
                  c.srai     s0, 29
                  c.lui      s6, 19
                  c.lui      s4, 25
                  nop
                  srli       t3, t2, 29
                  nop
                  c.li       s9, -1
                  c.addi16sp sp, -16
                  mulhsu     a0, t0, s2
                  c.slli     a6, 30
                  c.or       a3, a0
                  c.nop
                  srli       t5, t4, 20
                  and        s4, a5, s0
                  mulh       a3, t5, s7
                  c.li       a6, -1
                  ori        a1, a4, -162
                  c.addi16sp sp, -16
                  c.lui      t2, 6
                  sll        t3, gp, a0
                  c.addi     a0, -1
                  or         a5, a3, a3
                  slti       a5, t3, -855
                  sll        a5, t3, s6
                  remu       a2, tp, ra
                  c.addi16sp sp, 240
                  sltiu      zero, t6, -164
                  div        s10, s9, t4
                  c.andi     a3, -1
                  srl        gp, t6, s5
                  nop
                  andi       s8, t5, -144
                  c.addi16sp sp, 464
                  sra        zero, s0, a5
                  lui        t1, 211689
                  c.sub      s1, a5
                  c.li       s5, 21
                  lui        sp, 652944
                  c.or       a1, s1
                  srli       a6, tp, 30
                  c.xor      a0, a0
                  sra        t2, tp, gp
                  sll        gp, a2, s11
                  mulhu      s1, a2, ra
                  c.and      s1, a2
                  slti       s7, gp, 642
                  remu       a2, a5, t0
                  sll        t0, s10, a5
                  c.addi4spn s0, sp, 416
                  addi       t2, sp, -727
                  slt        gp, s4, a3
                  sll        t6, tp, a1
                  srli       t3, s6, 5
                  addi       a1, a5, -53
                  c.and      s0, a2
                  c.li       s1, 30
                  addi       s11, t1, 425
                  or         t3, gp, s10
                  mulh       a4, s3, t6
                  mulhu      a5, gp, sp
                  mulh       a5, t0, s5
                  lui        s3, 304391
                  c.srli     a1, 22
                  c.addi4spn a0, sp, 96
                  ori        s4, a3, 522
                  div        s6, s4, s11
                  srli       t1, s4, 28
                  mul        a4, s6, s7
                  or         a5, tp, s11
                  c.addi16sp sp, 16
                  c.mv       gp, s2
                  srli       zero, zero, 29
                  andi       s8, zero, -822
                  srai       s9, t6, 21
                  remu       a5, s6, t2
                  c.and      a3, a5
                  c.srai     a3, 4
                  c.andi     a3, 25
                  ori        s6, s6, -21
                  add        a2, a0, s7
                  c.nop
                  c.lui      t1, 31
                  c.srai     a5, 29
                  slt        tp, t3, t2
                  remu       s0, t2, s5
                  c.xor      a0, a1
                  and        s5, s10, s1
                  sll        s9, a3, s4
                  xor        a5, t4, tp
                  c.xor      a2, s0
                  or         a3, t3, gp
                  sra        s0, a1, s7
                  lui        t3, 231998
                  andi       t6, s11, 1005
                  or         a5, s2, s1
                  c.xor      a1, a4
                  sub        s8, t6, t1
                  addi       s3, s7, 880
                  ori        s6, s2, -714
                  mul        a6, a4, s0
                  c.mv       s3, s6
                  xori       a0, s4, -137
                  addi       s1, s0, 876
                  rem        a5, zero, a5
                  sra        s6, s1, ra
                  c.add      a6, s7
                  lui        s5, 152337
                  sltu       sp, t5, t4
                  c.srai     s0, 9
                  xor        s6, s1, a0
                  sltiu      s10, a5, 380
                  sltiu      s1, t5, -238
                  or         ra, s8, s6
                  add        t5, s6, t5
                  xori       s10, s4, 416
                  c.addi4spn s1, sp, 864
                  c.mv       t5, a3
                  ori        a3, t6, 161
                  c.and      s0, s0
                  mul        a4, zero, a4
                  sltu       s4, a1, sp
                  mulh       s11, s2, s1
                  addi       s10, s9, 105
                  addi       a4, s2, -322
                  c.sub      s1, a0
                  or         t2, a0, s0
                  sltiu      s4, s2, -736
                  remu       a4, t6, s3
                  andi       s0, t3, -930
                  sra        a3, t6, tp
                  li         s3, 0x0 #start riscv_int_numeric_corner_stream_33
                  li         t3, 0x6d46b82a
                  li         s0, 0x80000000
                  li         t6, 0x80000000
                  li         s5, 0x0
                  li         s9, 0xffffffff
                  li         a6, 0xfcd2345f
                  li         t5, 0x5a5dd540
                  li         a3, 0x37d0847d
                  li         sp, 0x22b93311
                  auipc      t3, 754052
                  sub        s5, sp, sp
                  sub        t3, s0, s0
                  rem        s0, s0, s9
                  div        a6, sp, sp
                  sub        s0, sp, a6
                  lui        s0, 596697
                  addi       s9, t6, -737
                  lui        s0, 592569
                  sub        sp, sp, sp
                  nop
                  mul        a3, s3, sp
                  lui        s5, 558996
                  mul        t3, a6, sp
                  add        sp, a6, s3
                  addi       t6, s5, -549
                  mulhsu     s5, s0, s0 #end riscv_int_numeric_corner_stream_33
                  xori       ra, a1, 660
                  add        t5, ra, t6
                  ori        s4, a7, -452
                  c.addi     s11, -1
                  c.andi     s1, -1
                  slti       t2, t3, 908
                  c.xor      a0, s1
                  mulhu      a3, a6, s8
                  srl        sp, sp, t4
                  add        a4, s0, gp
                  sltu       t3, a7, t3
                  c.mv       s9, s6
                  c.add      a5, gp
                  c.sub      a4, a4
                  sra        t0, t1, a3
                  c.add      s11, a3
                  slti       s5, a5, 823
                  c.slli     sp, 6
                  srli       s11, a5, 6
                  xori       a5, a2, -101
                  c.slli     s5, 25
                  and        zero, zero, a4
                  c.add      a6, s1
                  c.add      s6, t1
                  rem        s0, gp, s6
                  auipc      sp, 484247
                  c.li       t5, 2
                  c.srli     a5, 22
                  sll        s11, ra, s11
                  or         t3, a4, ra
                  addi       t2, ra, 277
                  sub        t3, t4, t3
                  c.srai     a3, 23
                  c.addi4spn s0, sp, 832
                  c.addi4spn s0, sp, 144
                  c.andi     a4, -1
                  add        zero, s3, t3
                  andi       a1, s1, 832
                  c.lui      s10, 18
                  remu       s7, tp, tp
                  xor        a1, t6, a6
                  slli       a6, s8, 21
                  rem        a2, t2, tp
                  srl        s5, a5, t3
                  addi       a5, t0, -964
                  c.lui      s4, 9
                  xor        s3, t4, a3
                  c.and      a4, a5
                  c.andi     s1, -1
                  add        a3, s8, s0
                  slt        s10, a0, zero
                  divu       a6, s10, s0
                  div        tp, s4, a6
                  andi       s8, t0, -794
                  sub        s11, t5, s2
                  or         a1, s10, a2
                  sltiu      s6, s2, 198
                  add        s10, s6, a5
                  ori        s10, t2, 439
                  mul        s7, t2, s7
                  mulhsu     ra, s0, sp
                  slti       t2, a1, -889
                  ori        zero, sp, 313
                  c.andi     a0, -1
                  sltu       t1, sp, s10
                  lui        a2, 985397
                  sll        s5, a7, s11
                  sll        t5, t2, s2
                  c.slli     s6, 5
                  srli       a6, s5, 12
                  xori       s11, gp, 677
                  c.and      a2, a2
                  c.addi16sp sp, -16
                  mul        gp, sp, sp
                  lui        s11, 890199
                  c.sub      s0, s1
                  xor        tp, sp, a3
                  c.or       a2, a1
                  c.addi4spn a5, sp, 64
                  slti       a0, s4, 651
                  addi       a1, gp, -616
                  xor        s6, t4, s0
                  div        s11, a3, s9
                  add        s3, ra, a7
                  c.srli     a3, 5
                  srl        t2, s8, t3
                  c.srai     a1, 28
                  c.mv       a5, a3
                  c.xor      s1, a3
                  sub        s7, sp, s1
                  c.sub      a4, a2
                  c.nop
                  or         gp, t3, t1
                  and        s9, t6, s8
                  c.xor      a1, s1
                  remu       a0, s0, a2
                  c.xor      a1, a2
                  c.slli     t5, 4
                  mulhu      t3, s3, t4
                  c.addi     a0, -1
                  sltu       t5, a2, a0
                  c.sub      a3, a5
                  nop
                  nop
                  c.sub      a5, a3
                  slli       gp, tp, 19
                  c.addi     s9, -1
                  nop
                  srli       s7, a0, 17
                  sub        s9, s6, s1
                  c.and      s0, s0
                  mul        s8, a3, a5
                  xori       s1, a2, 770
                  div        a1, tp, s9
                  auipc      t6, 961025
                  nop
                  c.addi16sp sp, -16
                  c.addi16sp sp, 32
                  lui        t6, 798135
                  andi       s3, t6, 917
                  addi       a3, a7, 619
                  slli       t0, a7, 5
                  div        tp, t6, t6
                  addi       t1, t3, -228
                  srai       s6, a6, 15
                  sra        a6, ra, s4
                  sra        t1, s10, s8
                  andi       a0, s8, 766
                  lui        a2, 852780
                  sra        s6, s4, a1
                  sll        tp, s5, s10
                  c.srli     a5, 8
                  and        s3, s4, s5
                  c.srli     a1, 23
                  addi       s1, a6, 438
                  lui        tp, 39261
                  andi       t1, s9, -697
                  c.sub      a0, a4
                  c.li       t0, -1
                  c.slli     a3, 24
                  c.sub      a4, a5
                  mul        s5, t0, a4
                  sub        s1, t5, t6
                  c.addi     s8, 2
                  remu       s8, zero, ra
                  ori        t6, s0, 379
                  c.or       a4, a5
                  divu       s9, a2, s0
                  xor        s5, a7, zero
                  xori       t5, t6, -788
                  lui        t6, 412117
                  rem        a1, t1, t0
                  or         t0, a3, tp
                  c.xor      s1, a3
                  srl        s9, t0, s10
                  and        gp, zero, t0
                  c.addi16sp sp, 464
                  addi       a2, s9, 29
                  c.mv       s11, ra
                  slti       s7, t5, -970
                  lui        s8, 246160
                  mulhsu     s8, s2, t0
                  c.addi     tp, -1
                  c.nop
                  c.li       a4, -1
                  c.and      a2, a1
                  lui        a5, 52983
                  or         a5, s6, t4
                  c.lui      ra, 29
                  remu       s4, t4, s7
                  srl        s1, a6, a6
                  c.andi     a0, 26
                  c.xor      a3, s1
                  mul        zero, sp, t4
                  ori        s11, s6, 420
                  c.nop
                  c.add      s6, s2
                  slt        zero, a0, s0
                  c.nop
                  add        a0, s3, tp
                  rem        s5, a0, tp
                  c.add      t1, a6
                  c.nop
                  c.or       a2, s1
                  srli       ra, t1, 9
                  srli       s8, t3, 7
                  mulhu      a0, s5, s2
                  sltiu      gp, a6, 204
                  c.li       s4, 19
                  mulh       s8, t6, gp
                  mulhu      s0, sp, s0
                  srli       t2, s0, 17
                  andi       tp, a5, -243
                  srl        s4, gp, s7
                  c.and      s1, a0
                  c.sub      s0, s0
                  c.andi     s1, -1
                  srli       t6, a6, 9
                  remu       t5, t5, t3
                  sltu       s3, a0, s4
                  c.addi4spn a1, sp, 320
                  c.nop
                  andi       t1, a3, 136
                  andi       a0, t3, 663
                  c.andi     s0, 5
                  sub        a1, t3, s0
                  sltu       a5, gp, t0
                  c.nop
                  sltu       t5, a2, s3
                  c.srli     s1, 22
                  c.mv       a1, t3
                  c.srli     a5, 5
                  c.srai     a1, 18
                  div        a1, gp, t4
                  c.andi     a2, 20
                  and        a2, zero, t4
                  c.srli     a1, 16
                  rem        s1, t3, t0
                  xor        s6, ra, a6
                  slti       a4, s6, -432
                  slt        a4, a3, s2
                  mulh       t1, s10, s5
                  sll        s3, t3, t6
                  c.andi     a1, 1
                  c.addi4spn a4, sp, 352
                  c.srai     a4, 29
                  c.srli     a2, 13
                  auipc      a4, 841470
                  srai       a2, t5, 18
                  mulhsu     s10, gp, sp
                  addi       a2, t3, 228
                  c.li       t5, 2
                  c.lui      s1, 25
                  srli       a6, ra, 2
                  c.or       a1, a5
                  sll        a3, s0, a1
                  mulh       t1, s9, s1
                  slli       s10, t6, 21
                  c.add      s7, t0
                  c.srai     a0, 24
                  srai       s7, t6, 16
                  sltu       t6, t5, s7
                  c.addi     a3, 6
                  lui        t5, 234489
                  c.srai     a5, 28
                  ori        t5, s5, 809
                  c.nop
                  c.or       a3, s1
                  c.srli     a1, 10
                  c.andi     s0, 6
                  mulhu      t3, t4, s8
                  and        t5, s2, s0
                  remu       sp, t0, a4
                  slti       t1, a0, -882
                  sll        s9, t5, s2
                  c.andi     a0, 6
                  sltiu      t1, sp, 554
                  c.slli     s1, 25
                  c.andi     a1, 19
                  divu       sp, a7, t0
                  mul        s0, a7, t3
                  c.addi     gp, -1
                  mulh       zero, a5, a5
                  slti       s10, s11, 373
                  c.nop
                  sll        a1, ra, s7
                  c.addi     sp, -1
                  andi       sp, a1, 1005
                  slli       gp, s9, 23
                  slli       s3, t0, 14
                  srai       t1, s9, 11
                  c.addi4spn a3, sp, 224
                  sra        s8, a7, a4
                  slli       t2, s10, 19
                  c.and      a2, s1
                  sub        t2, tp, t5
                  rem        a2, a6, t1
                  srai       s10, s1, 18
                  slt        a0, s5, s11
                  mulh       t1, ra, a3
                  andi       t0, t2, 670
                  c.sub      s1, a4
                  nop
                  div        s8, gp, s0
                  c.lui      a6, 30
                  divu       s1, s10, sp
                  c.sub      a4, a2
                  mul        s5, t1, ra
                  c.srai     a2, 27
                  c.addi     t0, 29
                  divu       s7, zero, s5
                  srai       s9, s1, 29
                  c.addi16sp sp, 96
                  c.andi     a5, -1
                  divu       tp, t6, ra
                  sub        s0, s0, t4
                  div        t0, a6, ra
                  c.srli     a1, 14
                  c.lui      t2, 25
                  divu       s8, ra, s1
                  sra        sp, s3, t5
                  c.lui      s5, 6
                  lui        s4, 889912
                  c.and      a4, a3
                  addi       gp, t1, 689
                  li         a2, 0x80000000 #start riscv_int_numeric_corner_stream_22
                  li         s7, 0x0
                  li         a3, 0xffffffff
                  li         s5, 0x0
                  li         sp, 0xffffffff
                  li         gp, 0xffffffff
                  li         t2, 0x80000000
                  li         s0, 0x80000000
                  li         s8, 0x6c62020e
                  li         a6, 0x80000000
                  auipc      t2, 466628
                  div        s0, a6, a3
                  mul        gp, s5, a6
                  remu       s0, a3, s5
                  sub        s7, gp, s7
                  auipc      s8, 3215
                  mulhsu     t2, t2, a3
                  remu       s8, a2, t2
                  auipc      s7, 592826
                  mulh       s8, a3, t2
                  mulhsu     s0, a3, a6
                  mulhu      s0, t2, s7
                  div        a6, a6, sp
                  addi       s5, sp, 810
                  mulhu      s7, gp, a6
                  mul        sp, s7, s7
                  add        s8, s7, s8
                  addi       s8, s8, -984
                  addi       s0, a3, -58
                  nop
                  add        t2, a6, s0
                  rem        s7, a2, sp
                  mulhsu     s5, s7, s0
                  remu       gp, t2, s5 #end riscv_int_numeric_corner_stream_22
                  remu       s1, t5, a5
                  slli       s4, s0, 10
                  srli       a0, s3, 17
                  and        s3, s7, t4
                  c.sub      a2, s1
                  c.slli     s1, 27
                  mulh       s8, s3, a2
                  divu       s9, s0, s2
                  slli       s11, a2, 9
                  c.srai     s1, 5
                  nop
                  remu       s9, a6, s5
                  srl        a3, sp, s4
                  c.lui      a2, 19
                  mul        s0, a2, s0
                  c.srli     a2, 30
                  mulhsu     t5, t1, s1
                  sll        ra, a2, t3
                  c.addi     s9, -1
                  div        t1, t2, s3
                  mulhu      gp, a4, s1
                  c.or       a1, a1
                  c.mv       t2, s5
                  c.srli     s1, 19
                  nop
                  c.mv       gp, t5
                  c.addi16sp sp, 368
                  andi       t1, zero, 915
                  or         a6, a2, t6
                  sltiu      a3, t2, 987
                  lui        zero, 299515
                  lui        t1, 800974
                  mulhu      a6, ra, a1
                  slti       s7, s6, 363
                  or         s3, sp, s0
                  ori        a3, a1, 812
                  mulhsu     s0, t5, ra
                  c.lui      s9, 30
                  ori        s3, s5, -438
                  divu       tp, a1, ra
                  slti       t1, a1, 880
                  rem        tp, a3, a3
                  andi       a1, tp, -123
                  sll        t2, s10, t5
                  or         t6, s5, a6
                  andi       s4, s1, 567
                  c.lui      s11, 6
                  remu       a6, s3, s6
                  c.li       s8, -1
                  c.add      a6, s3
                  srl        t0, s9, a5
                  auipc      zero, 1028547
                  srai       zero, s8, 18
                  xor        s1, a7, t2
                  c.nop
                  sltiu      zero, a5, 291
                  mulhsu     s11, sp, s10
                  slli       s5, s10, 16
                  mul        a4, a3, zero
                  ori        tp, s3, 902
                  mulhu      t5, s6, s9
                  c.andi     a3, -1
                  sll        gp, t5, a6
                  c.addi16sp sp, 112
                  c.addi     t3, -1
                  mulh       s3, zero, s4
                  c.nop
                  remu       a3, t5, s0
                  srl        s9, a3, s9
                  c.slli     s0, 2
                  srli       t3, t5, 21
                  xor        t5, t3, a4
                  srai       s9, s9, 10
                  div        s0, s11, s5
                  and        s8, s5, t3
                  srl        s11, tp, s10
                  c.slli     s9, 18
                  rem        t2, t5, a3
                  c.add      s3, s1
                  c.nop
                  ori        s3, t0, 372
                  c.xor      s0, a5
                  xor        s6, s6, a4
                  c.slli     sp, 3
                  div        gp, s0, t4
                  slli       a6, t3, 6
                  c.andi     a4, 21
                  xori       a6, s0, 165
                  sltiu      t3, s7, 51
                  xor        t2, s5, t5
                  c.add      a4, t0
                  c.add      a0, tp
                  sltiu      s6, t0, -541
                  c.slli     s7, 5
                  c.and      s0, a3
                  c.mv       sp, s10
                  mulh       s11, s0, t3
                  c.and      a2, a4
                  c.li       t0, 9
                  srl        s6, t0, s5
                  lui        s8, 1048125
                  xori       s4, t3, 703
                  c.sub      a0, a4
                  sra        s5, t6, t1
                  c.xor      a1, s1
                  slt        t5, a2, a7
                  nop
                  sltu       s10, a5, gp
                  c.nop
                  sltiu      s11, s1, 659
                  and        gp, s9, gp
                  c.xor      s1, a5
                  add        s3, a5, zero
                  srai       s10, s9, 4
                  add        s8, s6, s9
                  c.srli     a3, 28
                  c.andi     a0, 15
                  c.slli     sp, 23
                  mulh       s10, sp, s11
                  slli       a4, s6, 12
                  sub        a0, zero, a4
                  or         zero, a3, t2
                  lui        t2, 334518
                  c.andi     s1, 29
                  xori       s1, a5, 542
                  srli       a2, s5, 26
                  c.xor      s1, a0
                  div        a0, a3, t5
                  c.srli     a3, 6
                  or         sp, s4, a0
                  srai       s6, t0, 7
                  nop
                  sltiu      a5, s5, 603
                  c.add      sp, a3
                  c.addi     a1, -1
                  slt        s0, s6, s7
                  c.addi4spn a4, sp, 608
                  c.xor      s0, s0
                  xor        t1, a7, s9
                  slt        t6, a5, a7
                  rem        t1, tp, s7
                  sra        gp, t1, s6
                  srli       s3, s2, 26
                  sltiu      t3, s6, -510
                  nop
                  mulhu      s8, s10, t6
                  srl        a0, t2, gp
                  ori        t0, s7, 911
                  mulhu      sp, s5, a4
                  xori       t3, s1, -901
                  c.srai     a0, 24
                  auipc      s10, 97607
                  remu       a5, s3, t1
                  c.add      s5, s10
                  mulhu      s9, s6, t0
                  mul        t5, s2, a4
                  ori        s6, a1, 484
                  lui        t3, 179933
                  or         a5, s6, a5
                  ori        s5, a6, 399
                  c.or       s1, a0
                  sll        t6, a3, t4
                  c.addi4spn a4, sp, 112
                  c.mv       a0, s10
                  sub        s4, t3, a2
                  add        a1, ra, t6
                  c.add      s6, s4
                  c.lui      s5, 31
                  slt        s11, s7, t6
                  c.li       t0, 16
                  c.addi4spn a1, sp, 976
                  slt        s4, a4, s6
                  divu       s3, s7, a0
                  c.nop
                  sra        gp, s8, s3
                  c.sub      s0, a4
                  xori       s8, s3, 316
                  and        s8, t6, s6
                  rem        s3, s9, zero
                  mulh       s0, s2, s11
                  sltiu      s11, s0, 792
                  c.nop
                  sltu       t2, a1, s7
                  rem        a4, s0, s3
                  mulhsu     a5, s2, s4
                  ori        t2, s1, -9
                  divu       t5, s5, s4
                  sltu       a3, t6, s9
                  or         s5, t0, s9
                  add        s11, gp, s2
                  mulhu      a0, zero, s0
                  srl        s8, a4, a0
                  mulh       t0, s1, s4
                  c.addi     a3, 13
                  sll        s1, s0, a5
                  mulh       s1, s2, t6
                  slt        a5, s3, s4
                  c.addi16sp sp, -16
                  c.li       s4, 28
                  slti       a5, s3, -487
                  slti       a6, a6, 47
                  addi       t0, t1, 259
                  c.li       a5, 19
                  c.nop
                  addi       s9, a4, 781
                  sll        s4, sp, s3
                  c.addi16sp sp, -16
                  add        t6, a3, s2
                  sra        s1, s1, t4
                  sltiu      a0, s2, -172
                  mulhu      gp, s6, a3
                  c.srai     a2, 26
                  sra        t1, t3, t1
                  slt        t2, s7, s3
                  add        t0, t0, s2
                  c.lui      t5, 3
                  c.addi     t5, -1
                  srai       t2, s11, 26
                  auipc      a2, 995090
                  mulhsu     a4, t6, tp
                  divu       s7, s11, s6
                  c.addi4spn s1, sp, 960
                  srli       s6, a4, 29
                  c.andi     a2, 5
                  srai       ra, s7, 19
                  c.nop
                  c.addi16sp sp, -16
                  rem        s6, zero, t5
                  divu       a6, gp, t6
                  add        s10, a1, a5
                  c.li       t6, -1
                  ori        tp, t5, -736
                  c.andi     a5, -1
                  slti       s5, t1, 663
                  andi       ra, s11, -443
                  c.addi16sp sp, 480
                  nop
                  divu       t6, gp, t0
                  c.nop
                  srl        a2, t3, t4
                  slti       t6, t1, -930
                  c.slli     t5, 2
                  c.mv       s1, a0
                  srli       s10, a0, 24
                  lui        t2, 469008
                  lui        gp, 397755
                  addi       a6, t6, -182
                  c.slli     a5, 21
                  auipc      tp, 726675
                  remu       t2, s2, a2
                  divu       t2, a7, s8
                  and        t6, ra, s8
                  slt        t0, a2, t0
                  slli       t6, s9, 13
                  c.xor      a3, a1
                  slt        s9, sp, a4
                  auipc      s10, 336465
                  or         a5, s9, s4
                  c.mv       a5, a3
                  andi       a0, a4, 734
                  sltiu      a2, s7, -257
                  c.and      a0, a0
                  ori        a5, a0, -792
                  rem        s10, s11, a7
                  c.xor      a5, a2
                  sub        t3, s4, sp
                  c.sub      a5, a5
                  c.andi     a5, -1
                  or         a6, a5, a2
                  xor        a3, s9, s1
                  divu       a2, t6, t1
                  slli       t6, t4, 2
                  auipc      t5, 192078
                  xori       sp, a4, 169
                  c.mv       s8, a0
                  c.lui      s1, 7
                  mulh       s7, tp, s2
                  xor        a5, s6, a3
                  c.xor      s0, a0
                  c.sub      s0, a5
                  c.li       a5, -1
                  c.add      a6, s2
                  c.addi     s10, 18
                  mulhu      s6, t6, s8
                  mulhu      a0, t0, a1
                  c.addi16sp sp, 304
                  or         s5, a0, s11
                  nop
                  c.and      a4, s0
                  slti       a0, s1, -269
                  c.mv       a2, a4
                  xori       tp, s0, 32
                  divu       s4, t1, tp
                  c.nop
                  sltiu      s6, a5, 955
                  mulhsu     s0, a2, a4
                  sltiu      s7, a4, -24
                  and        a3, s1, s6
                  rem        gp, a7, t1
                  div        zero, t5, s6
                  c.lui      t1, 14
                  xori       a1, ra, -126
                  c.add      t1, s9
                  c.add      s1, a6
                  slti       s11, t5, -252
                  mulhsu     s6, t3, t5
                  c.add      a1, s1
                  addi       zero, t0, 206
                  mulhu      s8, s5, s4
                  xor        s8, a4, s3
                  or         sp, a7, a7
                  slli       a3, s8, 12
                  mul        t1, s7, s3
                  c.xor      s0, a0
                  c.add      a5, a6
                  slti       a6, s7, 594
                  c.addi4spn a0, sp, 896
                  xor        tp, s8, s9
                  div        tp, a3, a6
                  mulhu      s5, a0, a4
                  or         t2, s0, t5
                  c.andi     s0, 7
                  c.nop
                  c.addi16sp sp, -16
                  c.add      t0, a6
                  c.sub      a2, s1
                  andi       ra, s3, 54
                  divu       s3, t3, zero
                  and        a1, s6, tp
                  xori       t6, a4, -79
                  mulh       t2, a6, t2
                  srli       t5, s8, 13
                  mulhu      s11, tp, a4
                  xori       sp, a1, 662
                  c.xor      a3, s0
                  c.addi4spn a1, sp, 528
                  c.add      t0, s9
                  c.and      s0, a3
                  c.nop
                  sra        gp, t5, gp
                  slti       s8, a1, -746
                  srl        t0, t1, a2
                  c.li       s3, -1
                  c.slli     t3, 3
                  c.srli     s1, 21
                  lui        s10, 780030
                  xor        a5, ra, t0
                  sltu       s9, t3, s11
                  c.andi     a3, -1
                  c.or       a2, a3
                  lui        gp, 397354
                  c.addi     t3, -1
                  divu       a4, t1, sp
                  srai       s5, s9, 24
                  c.mv       a5, a6
                  mulhu      tp, s3, s1
                  sll        s1, t3, a6
                  rem        t6, a5, s5
                  remu       s4, a2, zero
                  mulhsu     s0, zero, s2
                  c.or       s1, a2
                  slt        s9, t1, s9
                  sll        s8, t3, a5
                  sra        s5, ra, a4
                  c.lui      s8, 7
                  sltiu      t0, sp, 312
                  addi       t0, a5, -154
                  c.nop
                  or         a3, gp, s5
                  c.mv       a0, s4
                  rem        t1, s9, sp
                  srl        a5, gp, a1
                  sub        s5, a5, t2
                  mul        a3, s9, a1
                  nop
                  xor        zero, a6, a6
                  add        a1, ra, s5
                  c.addi4spn a0, sp, 432
                  c.addi4spn a2, sp, 368
                  c.and      a5, a1
                  xori       s10, zero, -96
                  slt        zero, tp, s5
                  addi       t0, t2, 427
                  andi       s7, a7, 110
                  sll        t5, a3, gp
                  c.or       a1, s1
                  srl        s6, s7, a5
                  sltiu      a3, s1, 789
                  slti       gp, s0, -699
                  xori       a1, a4, 233
                  addi       s6, ra, -486
                  xori       a4, a5, 667
                  mul        s7, s7, s5
                  addi       a4, s5, -957
                  c.slli     gp, 12
                  c.or       s1, a2
                  mulh       a2, t2, a5
                  mulh       t1, s8, gp
                  slti       gp, s3, 50
                  sra        s11, a7, t6
                  divu       a6, s8, s9
                  xor        s7, s9, s0
                  rem        a0, a2, a4
                  c.andi     a0, 12
                  c.lui      s8, 30
                  c.and      a5, a5
                  srli       s6, a6, 18
                  c.srli     s1, 23
                  and        s6, a2, s10
                  mulhu      s8, a2, s0
                  nop
                  andi       t5, a2, 41
                  srl        s9, ra, tp
                  c.xor      a1, a3
                  rem        s11, tp, t1
                  c.andi     a2, -1
                  ori        t2, a6, -886
                  sub        a6, s1, s7
                  rem        s3, zero, s4
                  ori        ra, a5, 752
                  c.srai     s1, 16
                  c.sub      a1, a0
                  c.xor      a5, a3
                  c.sub      a0, a5
                  c.srai     s1, 17
                  sll        s9, s0, ra
                  sltu       a3, t4, t5
                  add        a0, s10, t1
                  c.lui      s8, 21
                  c.mv       s1, s5
                  c.lui      s5, 27
                  remu       t0, a4, s3
                  c.addi     t6, -1
                  c.slli     s5, 27
                  slt        t5, s1, a0
                  xori       gp, s0, 509
                  c.nop
                  c.or       a5, a4
                  divu       t2, ra, t6
                  mulh       tp, t0, s6
                  c.addi16sp sp, 416
                  lui        a0, 304600
                  mulh       s11, s9, s2
                  mulh       s4, a3, t4
                  c.andi     s1, -1
                  sra        s8, a4, a7
                  remu       t2, t1, a6
                  mul        sp, s9, t4
                  c.srli     a4, 4
                  sra        ra, t5, s10
                  c.andi     s1, -1
                  slt        t6, s4, t6
                  c.addi4spn a0, sp, 928
                  c.srai     a1, 23
                  slti       s0, t2, -231
                  sra        tp, a7, zero
                  sltu       tp, a0, s5
                  c.mv       t0, s11
                  c.addi     s5, 30
                  sltu       a0, t2, a2
                  li         t3, 0x80d6ae35 #start riscv_int_numeric_corner_stream_34
                  li         s9, 0x0
                  li         s1, 0x69823fc1
                  li         a1, 0x0
                  li         s8, 0x80000000
                  li         a3, 0x0
                  li         t1, 0xffffffff
                  li         a5, 0x2e1b5463
                  li         t6, 0x80000000
                  li         a6, 0x80000000
                  lui        s9, 572265
                  remu       s1, s1, t6
                  nop
                  rem        t3, a6, t6
                  mulh       t6, s1, t3
                  auipc      a3, 520571
                  remu       s9, s9, a1
                  rem        a1, t6, s8
                  remu       a5, a1, t1
                  mulh       s1, t3, a5
                  mulh       s1, a1, s8
                  mulhu      a3, a1, a3
                  mulh       t6, s1, a3
                  sub        a6, a1, a5
                  mul        s8, t6, s9
                  nop
                  mulh       a1, t6, a1
                  mulhu      a5, s9, a3
                  rem        a5, s1, a3 #end riscv_int_numeric_corner_stream_34
                  slt        t2, s4, t3
                  lui        sp, 229439
                  and        tp, s6, s9
                  lui        a2, 387788
                  c.mv       a1, s7
                  c.li       ra, 21
                  slti       t1, s7, -425
                  c.andi     a0, 11
                  c.srai     a3, 15
                  c.slli     t0, 13
                  slt        t3, ra, a2
                  sub        s8, s7, s11
                  sra        t1, s1, a6
                  slli       sp, s6, 19
                  c.addi16sp sp, 144
                  sub        tp, s7, t2
                  divu       sp, s1, a3
                  srai       s4, s11, 28
                  ori        a4, a5, 895
                  c.li       a0, 18
                  and        s9, s3, s3
                  c.xor      a1, a0
                  srai       s8, zero, 28
                  ori        s0, s0, -989
                  divu       sp, t3, t0
                  srl        a5, t0, s1
                  andi       a6, t3, 320
                  slti       s11, zero, -934
                  nop
                  c.and      a5, a1
                  c.sub      a4, a2
                  rem        s8, t2, s6
                  c.or       a5, a1
                  addi       sp, t1, 648
                  c.xor      a1, a5
                  divu       s5, s11, tp
                  c.slli     s1, 23
                  addi       a5, ra, -130
                  sll        s10, a6, s0
                  c.srli     a2, 2
                  mulhsu     a4, sp, t4
                  mulhsu     t5, a7, s9
                  c.xor      a3, s1
                  c.addi16sp sp, 384
                  andi       s9, t6, 235
                  c.add      t1, t2
                  c.add      sp, s6
                  c.or       s0, a1
                  lui        s11, 1011236
                  xori       s9, t2, 674
                  nop
                  c.addi     t5, 13
                  slli       a0, t4, 13
                  or         t3, t6, t1
                  xor        s6, s8, a6
                  ori        t1, a1, 853
                  lui        s7, 975517
                  slti       s6, s7, 33
                  mulhu      sp, s5, s7
                  c.addi4spn s0, sp, 640
                  nop
                  c.addi16sp sp, 160
                  or         t6, tp, ra
                  sltiu      gp, t4, -123
                  c.addi4spn a1, sp, 368
                  xori       a3, t1, -716
                  ori        a4, t0, 451
                  sra        s7, a6, zero
                  add        s9, s9, s11
                  divu       t3, ra, a7
                  slti       t3, gp, -42
                  addi       gp, t1, -982
                  div        s10, a0, s6
                  c.and      a3, s0
                  srli       t2, s7, 22
                  c.li       t2, -1
                  c.addi16sp sp, -16
                  andi       zero, s9, -617
                  slli       t2, t5, 5
                  lui        gp, 712036
                  c.srai     a2, 27
                  c.or       a4, a2
                  c.srli     a0, 27
                  srai       s5, zero, 5
                  ori        s5, t2, -153
                  sltu       a2, s5, tp
                  nop
                  c.addi4spn s0, sp, 832
                  andi       s5, sp, -87
                  c.or       a4, a5
                  xor        s4, s7, t1
                  c.srli     s0, 15
                  c.and      a3, a1
                  c.srli     s0, 21
                  mulh       zero, t5, t0
                  mul        s1, a5, s2
                  andi       ra, s7, 560
                  addi       a6, s1, 283
                  c.slli     s10, 31
                  c.or       s1, a4
                  or         t2, t6, s6
                  srai       s11, t2, 29
                  xori       s3, t5, -692
                  c.addi     s5, 25
                  c.srli     s0, 17
                  and        a6, tp, s6
                  lui        s5, 74532
                  nop
                  mulhsu     a4, s6, t5
                  c.lui      a4, 17
                  and        tp, s11, a1
                  sll        zero, t0, a2
                  srl        a5, s8, s8
                  c.slli     s6, 22
                  c.or       a2, a4
                  c.nop
                  xori       ra, t2, 15
                  c.srai     a2, 23
                  c.andi     a5, -1
                  mul        t0, s3, s8
                  or         t1, s1, s6
                  sltu       tp, s9, t6
                  mulhsu     a2, s3, a0
                  xor        t0, s9, ra
                  and        gp, s6, s1
                  and        a3, a1, ra
                  mulhsu     a3, a4, t3
                  mul        zero, t4, a4
                  add        s7, s10, t0
                  mulh       t0, s6, a1
                  or         s11, s1, a5
                  c.slli     a2, 25
                  mulhsu     s5, s7, s8
                  xori       a2, gp, -843
                  mulhu      s4, s0, s7
                  c.srli     a5, 16
                  c.srli     a5, 24
                  srli       t0, s10, 10
                  c.xor      s1, a3
                  andi       a6, a4, -563
                  andi       a4, zero, -476
                  nop
                  slli       s5, s6, 20
                  srl        a5, s11, s0
                  c.li       t3, -1
                  c.xor      s1, a4
                  c.and      a4, s0
                  xori       tp, a2, 979
                  remu       t1, tp, s9
                  c.or       a4, a2
                  c.srai     a4, 27
                  lui        s10, 889765
                  c.andi     s0, -1
                  slt        t5, a3, s2
                  c.sub      a2, s1
                  c.srli     a0, 3
                  divu       s8, ra, s8
                  c.li       t1, -1
                  c.mv       ra, s4
                  divu       a1, zero, a5
                  rem        t3, s3, a5
                  c.srai     a0, 11
                  xor        t2, t1, s3
                  c.slli     s7, 22
                  div        s6, s7, s6
                  and        a4, a3, t1
                  xor        a2, t5, t1
                  slt        s7, a7, s8
                  xor        s9, s4, s8
                  c.srai     a5, 19
                  c.slli     a3, 8
                  div        sp, a5, s0
                  slt        t2, s2, s8
                  andi       a4, s4, 708
                  addi       a3, a5, -599
                  c.addi16sp sp, 288
                  or         a5, s10, s3
                  srli       s10, t5, 5
                  mulhsu     a0, s2, sp
                  c.srai     a5, 28
                  nop
                  div        t0, t4, t5
                  slti       sp, a2, 124
                  c.and      a3, a2
                  srl        tp, s11, a4
                  mul        s3, zero, s4
                  c.addi4spn a3, sp, 80
                  xori       a6, tp, 235
                  srli       s4, a3, 6
                  sll        s1, s3, a3
                  xori       s5, a1, 336
                  and        s5, gp, t2
                  c.addi     a1, -1
                  c.sub      a1, a0
                  c.slli     t1, 26
                  or         tp, t5, s3
                  srli       s9, t5, 14
                  c.addi     ra, 22
                  sub        tp, ra, a0
                  c.mv       t2, s0
                  c.srli     a4, 12
                  c.addi16sp sp, -16
                  sra        a6, a4, s1
                  xori       t5, t6, 204
                  c.srli     a2, 13
                  rem        sp, a4, s2
                  slt        t3, t6, s7
                  c.addi16sp sp, 336
                  c.and      a5, a3
                  divu       ra, s8, t5
                  c.srai     a0, 6
                  c.andi     a5, 23
                  c.srai     a4, 15
                  or         a3, s3, s1
                  remu       s11, a5, gp
                  c.and      a3, a1
                  c.addi     t1, 25
                  mul        gp, s9, t2
                  sltiu      s10, a6, 83
                  andi       s9, s6, 231
                  c.addi4spn a0, sp, 784
                  c.andi     a1, 15
                  c.or       a1, a5
                  mulhu      sp, s10, t6
                  mulh       s0, a7, t3
                  mulhu      sp, s0, s11
                  xor        s4, s3, ra
                  c.add      s6, a0
                  sll        s9, t1, gp
                  andi       t1, s7, 855
                  c.slli     a2, 15
                  c.li       s4, -1
                  sll        gp, a3, ra
                  mulhu      s4, a1, t5
                  div        s6, zero, a2
                  ori        s1, t2, 153
                  sll        s4, s6, t5
                  c.andi     a2, -1
                  mulh       a2, zero, a3
                  sltiu      zero, a3, 379
                  c.lui      s4, 5
                  ori        a3, ra, 323
                  slti       t2, s4, -799
                  add        a3, a1, t5
                  c.andi     s1, -1
                  or         s1, tp, s11
                  sltu       a3, gp, s3
                  c.addi4spn s1, sp, 976
                  c.xor      s0, a0
                  sltiu      a6, tp, -1024
                  rem        a0, s2, s0
                  lui        s9, 142809
                  c.li       s3, -1
                  sll        a4, a6, a3
                  lui        ra, 512694
                  slti       s0, t0, 808
                  c.lui      s5, 12
                  slt        ra, t4, s11
                  sll        s4, zero, s10
                  addi       s9, s7, -999
                  lui        t5, 909809
                  c.srai     a3, 28
                  rem        s1, a1, sp
                  c.andi     a3, 25
                  c.slli     a6, 19
                  remu       s11, a4, s8
                  c.addi4spn a1, sp, 656
                  nop
                  mul        a5, sp, s9
                  slti       a5, s11, -945
                  nop
                  auipc      t0, 50268
                  remu       t1, a6, t3
                  c.srli     a2, 26
                  sll        a0, s2, t6
                  or         s6, t1, t4
                  or         zero, tp, a0
                  sltiu      s4, a6, -831
                  addi       a0, a5, 186
                  xori       tp, s6, -129
                  c.addi16sp sp, 288
                  slti       s9, a1, 11
                  div        s10, tp, s7
                  c.andi     a3, -1
                  c.lui      t5, 4
                  ori        a4, gp, 758
                  remu       s4, s9, t1
                  and        t0, tp, s2
                  c.add      a6, s7
                  remu       a0, a7, gp
                  mul        a1, s11, t3
                  xori       t1, a7, -905
                  and        s1, s1, tp
                  sra        s3, s10, t1
                  c.or       s0, s1
                  mulhsu     s11, s11, a7
                  and        a2, t1, gp
                  remu       a0, s1, s7
                  c.lui      s6, 15
                  srl        t2, t1, t4
                  addi       t1, a1, 484
                  c.lui      s9, 29
                  c.li       t5, 0
                  or         ra, a5, t1
                  or         ra, t6, t1
                  andi       s9, zero, 562
                  ori        t2, t6, -863
                  div        t3, s11, a2
                  nop
                  c.addi     t3, 7
                  c.and      a2, a0
                  add        gp, s0, zero
                  c.and      s1, s0
                  xor        s4, t0, gp
                  c.and      s0, a2
                  srl        zero, a4, a3
                  c.xor      s0, s1
                  c.addi     t6, 31
                  sub        s4, a4, s6
                  sub        s8, s5, s3
                  andi       t3, a2, 836
                  c.and      s1, s0
                  c.sub      s1, s0
                  sltiu      a0, s3, -360
                  slli       s3, s3, 14
                  and        zero, a0, s6
                  c.or       a3, a2
                  c.andi     s0, -1
                  sll        s3, t5, sp
                  andi       a6, t0, 922
                  c.add      a3, t5
                  div        s7, a3, t0
                  c.xor      a2, a4
                  div        s5, a7, s3
                  remu       t2, s2, s10
                  c.add      a2, s10
                  c.lui      s7, 5
                  mulhsu     a0, a4, zero
                  and        a2, a7, a6
                  sltiu      s10, gp, 145
                  mulhsu     s1, a4, s11
                  c.li       s3, 26
                  nop
                  xori       s0, tp, 372
                  and        a4, s6, s9
                  ori        s6, t3, -1022
                  xori       a5, t2, 482
                  addi       t5, s6, -267
                  add        a2, t1, a7
                  slt        s5, t6, sp
                  c.and      a3, a2
                  sub        t6, t3, s11
                  ori        tp, s3, -599
                  c.and      a2, a1
                  c.add      s5, s0
                  c.mv       ra, t1
                  c.add      tp, t3
                  c.srli     a1, 23
                  ori        t6, s8, 564
                  c.addi16sp sp, 80
                  or         t1, a7, gp
                  mulhu      s0, s2, s9
                  mulhsu     ra, a7, ra
                  mulhsu     s8, s11, s8
                  sltu       a1, t4, t0
                  andi       s9, t3, 628
                  add        sp, t5, a6
                  xori       gp, s7, 793
                  c.nop
                  c.addi16sp sp, 16
                  sltiu      s8, s7, 15
                  slti       s4, a0, 777
                  or         a1, zero, s0
                  and        s3, t4, s5
                  c.sub      s1, a3
                  add        a0, a2, a0
                  slli       a2, a5, 15
                  and        t0, a2, s1
                  rem        s4, t5, a0
                  addi       t2, s6, 734
                  c.addi     t0, -1
                  lui        sp, 975649
                  mulh       s3, t3, t6
                  c.addi     t0, -1
                  add        t6, t5, s8
                  c.and      s1, a5
                  sltu       s0, t5, a1
                  auipc      s3, 559425
                  div        s10, t4, t0
                  ori        t1, a5, 944
                  div        s0, ra, t0
                  andi       a2, tp, -543
                  c.lui      t3, 19
                  mul        s11, s5, a3
                  addi       ra, s5, 674
                  c.xor      a5, a4
                  auipc      a0, 221869
                  c.add      a4, a7
                  c.xor      s0, a1
                  remu       gp, a3, sp
                  c.li       s1, 10
                  c.add      s11, t0
                  c.addi     a4, -1
                  c.mv       a4, s7
                  slli       t1, t1, 6
                  c.xor      s0, a0
                  c.mv       t1, t0
                  slli       s11, s10, 6
                  sltu       s11, s1, s2
                  andi       ra, a0, -993
                  remu       s11, a7, t5
                  c.andi     a0, -1
                  sll        zero, s4, s0
                  addi       s10, s1, 240
                  remu       s4, s7, a5
                  divu       zero, s8, zero
                  or         t1, s11, a7
                  sll        s1, s7, s9
                  c.xor      s0, a1
                  c.andi     a2, -1
                  c.nop
                  srli       a0, a3, 17
                  c.nop
                  auipc      t1, 183044
                  and        a2, t5, a3
                  c.srli     a0, 4
                  divu       a4, s3, sp
                  div        s7, a1, t0
                  c.xor      a4, a2
                  slli       t6, s2, 14
                  slti       a4, s9, -641
                  mul        sp, a2, s9
                  c.addi     s7, 27
                  c.nop
                  ori        s5, s10, -523
                  c.srli     s0, 23
                  nop
                  slti       t2, a4, 764
                  slli       s3, a1, 27
                  c.mv       a1, s10
                  slt        s10, s7, a7
                  srli       s5, a4, 10
                  c.andi     a3, -1
                  remu       t3, t1, s11
                  srl        s3, s7, s1
                  or         gp, s7, a3
                  c.andi     s0, 27
                  auipc      s8, 655981
                  rem        ra, tp, tp
                  mulhu      s11, sp, a0
                  mul        s0, a1, s1
                  div        s8, s2, s5
                  c.addi     t3, -1
                  c.srli     s0, 3
                  srli       zero, gp, 9
                  c.add      t3, t4
                  c.addi     tp, -1
                  auipc      zero, 270236
                  slti       s11, s9, -192
                  remu       t6, ra, a4
                  sltu       a5, t2, a7
                  mulhsu     a6, t4, s8
                  c.or       a5, a2
                  nop
                  c.sub      a2, s0
                  rem        s0, s3, a3
                  mulhu      a4, s11, zero
                  lui        s10, 734063
                  c.nop
                  sll        s0, t2, zero
                  srl        s9, a4, s6
                  xori       s3, s5, 31
                  c.and      s1, a5
                  slti       zero, a1, -582
                  mulhsu     t0, t2, a6
                  divu       a1, s4, a7
                  c.addi     s7, -1
                  nop
                  c.nop
                  c.andi     s0, -1
                  c.slli     a5, 23
                  c.addi     s7, 6
                  c.srli     a5, 11
                  c.mv       t3, t0
                  c.or       s1, a4
                  slli       s0, s9, 31
                  c.add      a4, s6
                  div        s10, s1, s7
                  c.mv       a0, s2
                  c.nop
                  div        t1, a5, t4
                  srl        t5, sp, a2
                  div        t1, s4, zero
                  sra        s11, s2, s11
                  c.and      a1, a0
                  addi       a3, s8, 668
                  c.sub      a4, a1
                  c.li       s1, 1
                  auipc      a4, 849488
                  div        s8, gp, s0
                  slti       s11, t6, -131
                  sll        ra, a3, a4
                  srli       s8, s3, 15
                  rem        a6, a5, s8
                  c.li       s3, 25
                  div        s5, a5, s3
                  xori       s7, t2, 455
                  xori       t5, t2, 521
                  sll        s9, a7, gp
                  srai       a1, t6, 29
                  sra        gp, s8, s11
                  sltu       t6, a5, sp
                  c.sub      s1, a4
                  c.and      s1, a4
                  c.andi     s1, -1
                  c.and      a3, a0
                  mulh       s10, s2, s8
                  addi       t2, a3, 528
                  c.addi16sp sp, -16
                  c.add      s7, t2
                  c.nop
                  mulhu      a5, s2, t2
                  mulhsu     s5, tp, s7
                  c.srli     a0, 15
                  xori       a1, s5, 256
                  sub        a0, t2, s0
                  slti       sp, a4, -84
                  xori       t1, a0, -922
                  sll        s7, ra, tp
                  add        t2, tp, t3
                  c.lui      s4, 10
                  srli       a2, t4, 21
                  rem        a6, s5, t3
                  divu       s3, a2, t3
                  c.mv       t0, a0
                  slti       t1, a5, -1024
                  mulh       t6, s6, ra
                  addi       s0, s11, 193
                  srl        t1, ra, s1
                  slt        gp, s1, s10
                  c.slli     s9, 16
                  slti       t0, s10, -338
                  slti       s11, a0, -494
                  sra        t2, s5, t4
                  c.srai     a3, 2
                  xori       sp, sp, -828
                  c.add      a6, s3
                  mulhsu     s1, a7, s3
                  nop
                  nop
                  c.addi     ra, -1
                  add        t1, s9, a0
                  srai       s1, s5, 14
                  sltu       a3, s8, s9
                  sltu       t0, s8, a7
                  auipc      a4, 572923
                  c.srai     a2, 4
                  or         t5, sp, gp
                  c.mv       a1, a5
                  srli       gp, t0, 1
                  add        t5, s9, s5
                  c.add      a4, a5
                  c.mv       t1, s2
                  sra        gp, s4, t5
                  c.mv       s0, s5
                  rem        ra, s2, s7
                  c.addi16sp sp, 416
                  c.xor      a1, a1
                  c.li       s0, -1
                  sltiu      t3, a1, 768
                  c.nop
                  xori       tp, s5, 984
                  srli       s10, tp, 3
                  c.add      s4, a2
                  c.mv       s4, s6
                  div        a6, s2, ra
                  slli       sp, s10, 5
                  c.and      s1, a5
                  c.mv       s1, s11
                  slli       t3, a7, 30
                  slti       a5, tp, -677
                  nop
                  slli       s1, t2, 3
                  c.and      a1, a2
                  c.andi     a5, 24
                  and        a2, ra, tp
                  addi       a5, s5, 495
                  xori       s8, sp, 71
                  c.or       a2, a1
                  c.srai     s0, 25
                  divu       t1, a1, t4
                  sub        a0, zero, t1
                  auipc      s9, 592339
                  c.li       s9, -1
                  add        a3, t2, a4
                  rem        s3, tp, t0
                  mulhu      t3, zero, s4
                  c.srai     a5, 5
                  c.srai     a4, 25
                  andi       a2, t6, -801
                  sra        s11, t0, t4
                  xori       a3, a3, -12
                  add        s3, a1, s2
                  c.slli     t6, 8
                  c.addi16sp sp, -16
                  andi       s0, tp, -557
                  c.lui      t3, 29
                  c.andi     s1, -1
                  srli       a4, a2, 9
                  sra        s10, s2, s11
                  c.li       s6, 12
                  divu       t3, s2, t6
                  srli       s7, a4, 30
                  c.srai     a3, 31
                  addi       s7, a3, -480
                  c.and      a3, a0
                  c.or       s1, a1
                  srli       s0, ra, 9
                  c.andi     a4, -1
                  c.nop
                  c.nop
                  xor        t0, a4, s5
                  c.li       s11, 9
                  nop
                  andi       a0, s2, 943
                  rem        s0, s9, s1
                  srl        a5, t0, t3
                  c.lui      t0, 20
                  c.addi4spn a3, sp, 752
                  mul        a2, t0, t1
                  c.addi     t5, -1
                  c.and      a5, a4
                  or         gp, a1, sp
                  c.addi16sp sp, 272
                  rem        s6, t2, a4
                  mulhsu     a4, a6, tp
                  remu       ra, a3, a4
                  mulhu      a6, s4, t0
                  and        s3, t1, t0
                  srl        s8, a6, zero
                  slti       t3, zero, 327
                  c.andi     a1, -1
                  sltiu      s10, t1, -292
                  sra        zero, a5, s10
                  sub        s7, s5, t3
                  c.addi     s6, 30
                  addi       a2, t2, -513
                  div        t0, tp, s9
                  xor        a3, sp, a3
                  remu       s8, ra, s11
                  auipc      ra, 515152
                  srli       t2, s2, 2
                  srl        gp, sp, t6
                  c.nop
                  c.xor      a2, a2
                  c.nop
                  mulh       t3, ra, a7
                  xor        a2, ra, sp
                  c.addi16sp sp, 432
                  and        s5, tp, t4
                  remu       s7, s0, a6
                  remu       a1, t1, t4
                  c.addi16sp sp, -16
                  sub        t0, s3, t6
                  slli       tp, a1, 21
                  add        sp, gp, t6
                  c.lui      s3, 15
                  slli       t6, tp, 22
                  addi       s4, s5, 622
                  c.li       a5, -1
                  sra        s6, s11, s11
                  c.mv       a5, a7
                  sll        s8, s10, a0
                  lui        a1, 914591
                  srli       s0, a6, 4
                  c.srai     a2, 10
                  srai       s8, s4, 25
                  or         t5, zero, s5
                  ori        t5, sp, -769
                  mulhsu     s7, t0, s5
                  c.or       s0, a2
                  or         a1, a6, t3
                  c.lui      s4, 19
                  nop
                  rem        t6, a4, a7
                  xor        s0, a1, s2
                  srli       s3, s7, 10
                  xori       tp, t2, -752
                  mulh       a0, s6, a0
                  rem        a2, a4, s5
                  or         a4, s7, s6
                  c.slli     s5, 4
                  c.lui      a5, 4
                  slti       t3, s5, -489
                  c.or       a1, a2
                  xori       a5, t0, -868
                  slli       s5, t3, 19
                  sub        zero, s0, tp
                  ori        s6, s6, 267
                  c.li       t3, -1
                  slli       s10, a1, 25
                  sltiu      t6, s10, -484
                  srli       s3, t6, 20
                  c.add      s0, s6
                  c.add      t3, t1
                  lui        a3, 941915
                  c.xor      a0, a2
                  c.addi     t0, -1
                  remu       t6, t0, s7
                  c.srli     a1, 6
                  c.slli     ra, 10
                  mulhsu     zero, s9, s9
                  sub        t3, s10, s9
                  mulh       t2, gp, a5
                  sltiu      s3, t0, -940
                  slti       a5, s6, 790
                  c.xor      a1, a2
                  c.lui      t1, 15
                  c.addi     tp, 26
                  divu       gp, s4, a5
                  xor        a1, tp, s6
                  div        s0, sp, t0
                  c.nop
                  remu       t1, a4, sp
                  and        s9, s2, t6
                  c.mv       tp, s2
                  or         tp, a0, t4
                  c.mv       s3, s4
                  or         a3, a6, s5
                  c.and      a2, a5
                  xori       a6, a7, -822
                  addi       t0, s3, -852
                  ori        gp, a5, -952
                  srai       s7, a1, 18
                  c.and      a1, s1
                  srl        t1, s7, s1
                  c.lui      a4, 21
                  remu       a4, t4, a1
                  auipc      t5, 470664
                  c.and      s0, s1
                  div        sp, a1, s6
                  divu       a1, a5, s5
                  c.xor      a4, a0
                  and        s5, s8, a4
                  c.xor      a3, a3
                  add        tp, s11, t1
                  sltiu      a5, s7, 131
                  slt        t5, a3, s6
                  sll        t1, t3, s2
                  c.addi4spn a4, sp, 816
                  c.addi     s6, -1
                  xor        s5, s3, t4
                  mulhsu     s7, s7, s11
                  c.srli     a4, 18
                  c.or       s1, s0
                  addi       a0, t3, -879
                  c.and      a3, s1
                  div        s9, t6, s7
                  rem        a4, s11, zero
                  mulh       s8, sp, a1
                  srli       a1, a1, 7
                  srl        a1, s3, s6
                  srl        s7, a2, t4
                  srl        t6, t5, s9
                  srl        s8, s0, s8
                  sll        a2, a4, s0
                  andi       s5, a1, -972
                  c.nop
                  c.addi     s3, -1
                  remu       gp, zero, tp
                  c.lui      t3, 31
                  c.add      a1, t6
                  c.li       a0, -1
                  mulh       s3, gp, t5
                  ori        a1, t0, 795
                  c.andi     a4, -1
                  c.srai     a3, 2
                  mulhu      tp, t6, s9
                  sll        a2, a7, tp
                  sub        a2, a6, s8
                  xori       t2, s10, -394
                  c.sub      a5, s0
                  slti       s0, s6, 677
                  auipc      a3, 421427
                  ori        a5, zero, -870
                  slt        s10, t3, t4
                  xor        s11, t1, tp
                  or         t1, gp, ra
                  mulhsu     t0, zero, t0
                  c.andi     s0, 29
                  andi       a4, s6, -362
                  c.and      s0, a3
                  addi       s8, t2, -171
                  c.lui      s10, 12
                  add        t6, s7, ra
                  or         s5, s6, gp
                  c.li       t3, 18
                  slt        s9, a4, t0
                  mulhsu     s11, t1, s9
                  c.andi     s0, -1
                  c.or       a0, a0
                  mulhu      a0, zero, s1
                  sub        a2, s9, t0
                  sltu       s9, t3, s6
                  lui        a3, 952119
                  nop
                  c.li       t3, 23
                  nop
                  c.addi16sp sp, 144
                  mulhu      a4, s7, s10
                  c.li       s7, -1
                  remu       t3, a6, s3
                  srai       a4, t2, 3
                  andi       s3, ra, 166
                  div        a1, sp, a2
                  c.srli     s0, 9
                  srl        t1, t1, s9
                  sltiu      ra, t0, 404
                  c.addi4spn a4, sp, 688
                  c.srli     s0, 15
                  remu       s11, ra, s4
                  sra        gp, s10, a4
                  addi       s5, s2, 917
                  sltu       t6, s5, s2
                  c.mv       s11, a2
                  slti       a3, t3, 193
                  add        s0, t3, t5
                  c.andi     s1, -1
                  nop
                  rem        s3, a1, s3
                  mul        a3, s4, s1
                  xor        a1, t4, s2
                  or         s1, s7, t3
                  c.srli     a0, 15
                  nop
                  and        s1, s7, s3
                  c.addi     s3, 23
                  div        a1, s4, zero
                  and        t5, s4, a7
                  c.and      s0, a2
                  lui        t6, 508827
                  c.sub      a0, a5
                  nop
                  sltiu      a3, a3, 77
                  c.slli     a0, 4
                  remu       s4, a1, s11
                  div        a2, s10, t3
                  c.addi16sp sp, -16
                  c.addi     t2, -1
                  c.or       a2, s0
                  slli       a4, gp, 24
                  sra        sp, t0, t5
                  addi       t5, a1, -351
                  nop
                  mul        sp, t1, a7
                  c.srai     a0, 5
                  lui        s3, 644025
                  nop
                  slt        t3, tp, s1
                  rem        a3, s4, s8
                  sub        s1, a3, s4
                  srli       s1, sp, 26
                  sltiu      a1, s10, -26
                  divu       gp, s8, a7
                  c.slli     s6, 4
                  div        a1, t2, t4
                  div        a2, t3, a5
                  or         t1, a1, sp
                  mulhu      zero, s3, a7
                  c.mv       a1, s0
                  xor        s0, a3, s7
                  sltu       s9, a7, a3
                  c.xor      a5, a0
                  c.slli     a5, 31
                  sll        a0, t6, s2
                  andi       t3, a0, 975
                  sltiu      s3, s10, 45
                  c.slli     s0, 29
                  c.srli     a0, 26
                  mulhu      s10, s8, t4
                  and        s10, a1, s9
                  mulh       a2, s9, s0
                  c.or       s0, s0
                  auipc      s9, 511899
                  mulhu      a4, s9, s6
                  c.slli     a2, 7
                  sra        a2, s2, ra
                  c.nop
                  c.sub      a0, a4
                  xor        s4, s1, t5
                  c.and      a4, s0
                  c.add      a1, t3
                  c.slli     a3, 22
                  c.or       s0, a4
                  auipc      t2, 543924
                  c.li       t6, 25
                  ori        s11, gp, -854
                  c.add      s9, t2
                  c.srli     a2, 11
                  mulh       s9, a6, s11
                  divu       zero, t4, s10
                  c.addi16sp sp, 288
                  mulh       a5, s0, sp
                  c.nop
                  c.srai     a0, 29
                  sltu       t6, s4, a5
                  add        a0, s10, a3
                  andi       a6, s0, 698
                  c.xor      s1, s1
                  slti       s7, s9, -464
                  rem        s1, a1, s9
                  c.srli     a2, 11
                  rem        s5, a0, s5
                  c.add      s4, t4
                  c.addi     s8, 4
                  xor        s5, a0, s0
                  divu       a4, tp, s8
                  add        a5, t6, s7
                  rem        s5, t2, t3
                  c.li       t2, -1
                  mulhu      s8, a7, s6
                  srai       s9, zero, 27
                  divu       a1, gp, s6
                  c.srli     a3, 2
                  divu       a5, t5, s8
                  slt        s6, sp, a3
                  srli       s3, s2, 11
                  c.addi     ra, -1
                  c.andi     a2, -1
                  srai       t5, zero, 6
                  xor        a0, s5, s0
                  c.add      s0, s11
                  srai       t1, a3, 26
                  c.mv       s11, sp
                  mulh       gp, t1, a5
                  slti       s7, gp, 205
                  remu       t0, s11, s11
                  c.sub      s1, s1
                  c.srai     a5, 28
                  c.addi16sp sp, 352
                  addi       zero, s5, 1019
                  c.li       sp, 11
                  srl        t2, a3, s0
                  c.srai     a4, 13
                  and        zero, s2, a5
                  c.or       a0, a5
                  srl        a0, t5, s1
                  and        s1, s3, ra
                  c.add      t1, t5
                  c.xor      a4, a5
                  sltu       s6, s5, sp
                  c.li       s0, -1
                  xor        t0, s0, t5
                  c.mv       s10, a1
                  c.add      t6, gp
                  mulhu      gp, tp, s2
                  add        a6, s4, t2
                  srli       zero, a6, 20
                  c.xor      a3, a3
                  c.lui      t5, 13
                  c.mv       t0, s9
                  c.addi     s0, -1
                  sub        t3, tp, s2
                  c.mv       a5, t0
                  mulh       s0, gp, t4
                  slli       a1, zero, 6
                  add        a2, t4, s2
                  sub        s8, zero, t1
                  c.or       a5, s0
                  divu       a2, s5, sp
                  c.add      ra, s0
                  c.li       s10, -1
                  auipc      t6, 546256
                  c.mv       t1, sp
                  divu       s11, s1, a3
                  c.addi4spn a1, sp, 688
                  c.andi     a0, -1
                  or         a3, s6, a2
                  c.addi4spn a0, sp, 672
                  c.srli     a2, 11
                  srli       s6, a3, 11
                  sltu       s1, gp, s5
                  sll        t2, zero, ra
                  c.srai     a5, 17
                  c.nop
                  xor        s0, a0, t4
                  mulhsu     a4, ra, zero
                  c.mv       s6, a5
                  c.lui      s7, 31
                  c.addi4spn a1, sp, 720
                  srli       s8, t5, 6
                  c.nop
                  srl        a4, a3, a6
                  xor        s0, a1, t5
                  remu       t5, a6, t2
                  sltiu      s5, zero, -173
                  auipc      a2, 440978
                  c.li       t0, 27
                  sub        s7, a0, gp
                  auipc      s9, 962827
                  auipc      s6, 627073
                  c.sub      a4, a3
                  c.addi4spn a2, sp, 192
                  c.andi     s0, 11
                  c.li       s7, -1
                  c.addi16sp sp, -16
                  xori       t2, t0, 473
                  slli       s7, t1, 31
                  mulhsu     s1, s6, s6
                  slt        t5, s8, s10
                  mulhsu     s4, t1, t1
                  sub        t0, s5, s4
                  nop
                  mulhu      s8, t1, tp
                  or         t1, s11, ra
                  c.nop
                  c.xor      s1, a5
                  divu       t5, zero, t6
                  lui        gp, 218192
                  c.and      a2, a0
                  srl        a2, t3, a2
                  c.mv       s8, a0
                  c.lui      a0, 25
                  c.addi4spn s0, sp, 272
                  c.andi     a0, -1
                  lui        s10, 680319
                  c.or       a4, s0
                  slli       t3, s4, 10
                  sub        s7, t5, s9
                  slt        a6, ra, s2
                  divu       gp, s0, t6
                  c.andi     s0, -1
                  sra        s5, s2, s8
                  slli       gp, s8, 1
                  sra        a0, t3, t3
                  auipc      s4, 702402
                  c.andi     s0, -1
                  mulhu      ra, a6, a4
                  or         gp, t5, gp
                  add        s11, ra, a0
                  slti       ra, a2, 503
                  xori       s4, t5, -841
                  sra        s10, s9, ra
                  c.addi16sp sp, 80
                  slli       s6, s4, 3
                  c.mv       s10, t5
                  srai       a0, a6, 25
                  srl        s11, s6, s10
                  or         t5, s11, t1
                  divu       s11, s4, gp
                  divu       s7, a2, t2
                  c.xor      a2, a3
                  li         t3, 0xffffffff #start riscv_int_numeric_corner_stream_26
                  li         tp, 0x8a5da050
                  li         a1, 0x252cf912
                  li         s6, 0x80000000
                  li         a6, 0x75484c7f
                  li         s10, 0x0
                  li         s8, 0xffffffff
                  li         gp, 0xffffffff
                  li         t5, 0x0
                  li         t2, 0x80000000
                  add        t3, gp, a1
                  auipc      s6, 1047713
                  mul        gp, t3, t3
                  mulhsu     a6, a1, t2
                  auipc      s6, 437087
                  remu       t5, t2, a6
                  add        s10, tp, a6
                  addi       s6, a6, -6
                  addi       a1, t3, -83
                  mulh       t3, t2, a1
                  sub        s6, tp, a1
                  sub        t2, a1, tp
                  mulhsu     s8, a6, s8
                  auipc      gp, 377209
                  rem        s10, t3, s6
                  lui        s6, 402028
                  mulhsu     s10, s10, t5
                  rem        t3, a1, tp
                  add        t2, s10, s6
                  mulhu      s8, s10, t2
                  add        s10, gp, t5
                  add        a1, gp, tp #end riscv_int_numeric_corner_stream_26
                  auipc      s5, 180593
                  mulhsu     zero, s10, a7
                  mulh       t1, s9, s8
                  c.addi4spn a2, sp, 192
                  add        zero, s6, t3
                  srli       s9, s7, 18
                  andi       a5, s3, 464
                  slli       s3, s4, 15
                  sltiu      a3, s5, 600
                  c.sub      a4, a2
                  divu       s9, t6, gp
                  sltu       ra, s0, gp
                  c.or       s0, a0
                  auipc      s6, 265568
                  andi       t1, a7, 693
                  mulh       s6, s2, t2
                  mulhsu     t0, t6, s1
                  slt        a1, t3, s3
                  mulhsu     s7, s6, a2
                  c.addi16sp sp, -16
                  or         a4, a2, s1
                  srl        s1, s1, t2
                  c.or       a2, a2
                  slli       a5, t5, 23
                  mulhsu     s7, s9, ra
                  sltu       s6, a3, t3
                  divu       a6, s2, sp
                  c.slli     t2, 9
                  c.nop
                  auipc      a1, 770953
                  c.slli     t3, 20
                  slli       zero, t5, 16
                  c.slli     sp, 6
                  divu       a1, s3, a6
                  c.or       s0, s0
                  c.and      s0, s0
                  c.addi16sp sp, -16
                  c.srai     s0, 13
                  sra        s6, s6, s9
                  c.andi     s1, 4
                  nop
                  c.nop
                  and        s10, s1, a7
                  mulhsu     zero, s9, a1
                  c.add      s11, sp
                  c.mv       t0, a1
                  mul        gp, ra, t3
                  c.lui      s9, 27
                  addi       a3, t3, -918
                  c.and      a2, a4
                  c.and      s0, a2
                  srli       s11, a4, 9
                  slli       s1, s8, 9
                  slti       s4, s9, 987
                  c.addi     s9, -1
                  mulhu      s8, s3, t1
                  divu       a3, s4, t2
                  rem        s4, s3, a0
                  nop
                  divu       t3, s8, t1
                  c.addi     t6, -1
                  srai       t0, s1, 23
                  add        s5, s4, a2
                  c.lui      a6, 1
                  slti       a5, s7, -545
                  sub        t5, a7, s2
                  rem        t1, s8, a2
                  c.sub      a5, a0
                  c.add      a4, t6
                  nop
                  ori        t5, t3, -135
                  c.slli     t2, 12
                  addi       a3, ra, -415
                  srli       s5, s6, 12
                  andi       ra, t6, 579
                  mul        a4, a7, s2
                  addi       s5, s9, -37
                  mulhu      s1, t0, t1
                  c.addi16sp sp, 336
                  srli       s8, sp, 27
                  add        a5, t1, s1
                  remu       gp, s7, ra
                  c.addi     t0, -1
                  divu       s11, s8, a0
                  mulh       t2, a3, t5
                  andi       t2, t6, 285
                  andi       t2, a4, 718
                  sub        s5, s6, zero
                  sltiu      s7, t4, -80
                  c.or       a1, a4
                  c.andi     a0, -1
                  c.srli     a1, 24
                  srli       t2, t2, 29
                  slti       s11, a6, 202
                  add        s11, a5, a7
                  c.lui      gp, 3
                  sra        a1, a6, sp
                  c.srai     a3, 2
                  c.srli     a3, 25
                  mulhsu     t5, a7, s7
                  c.slli     s11, 10
                  c.and      s1, a2
                  sra        t2, s3, a7
                  divu       s11, a1, t5
                  div        t1, s0, t5
                  mulh       s10, s6, a3
                  add        sp, a3, a3
                  srai       t6, a1, 9
                  sub        a3, t0, a7
                  mul        t5, s11, a3
                  slti       t1, a4, 749
                  c.addi     s9, -1
                  slli       s7, s11, 18
                  c.xor      a3, s0
                  lui        tp, 1041186
                  mulhu      a2, s1, t6
                  mulhsu     s10, s3, a5
                  c.or       a3, s0
                  c.and      s1, s1
                  sltu       ra, t5, s10
                  mulh       s6, a1, s8
                  ori        a0, s3, -969
                  and        s11, a0, sp
                  nop
                  c.nop
                  c.lui      s9, 1
                  c.li       a6, 15
                  andi       t1, t5, 343
                  lui        a6, 63893
                  sltu       t5, s6, s3
                  xori       a6, s9, 810
                  c.sub      s1, s1
                  c.addi     t6, 30
                  sra        a0, s1, a0
                  c.addi16sp sp, 320
                  c.andi     a0, 8
                  c.slli     a5, 21
                  srai       zero, s11, 9
                  sra        s3, a2, s4
                  mulh       t1, t5, a4
                  sra        a6, s11, s4
                  sll        a1, s3, t2
                  c.sub      a1, a0
                  xori       a3, s2, -449
                  andi       gp, t0, -634
                  c.andi     s1, -1
                  c.lui      a5, 17
                  lui        t3, 308505
                  mulhsu     a1, a6, a5
                  mulhu      t3, t2, s5
                  c.srli     s0, 23
                  c.addi4spn a3, sp, 960
                  sltu       a5, s4, s3
                  sub        t6, s10, a2
                  c.or       a0, a1
                  xori       tp, zero, 505
                  xori       s0, t5, -598
                  c.addi     s0, -1
                  c.srai     a3, 13
                  c.addi4spn s0, sp, 400
                  mulhu      a4, s11, t2
                  c.addi     s11, -1
                  andi       ra, zero, -770
                  c.addi     a3, -1
                  c.and      a2, a0
                  c.or       a2, a5
                  srl        a2, s2, s7
                  auipc      a0, 899667
                  c.nop
                  addi       t0, a6, 75
                  xor        ra, s10, ra
                  sltiu      s0, t3, 528
                  c.andi     s1, -1
                  srli       s11, zero, 8
                  c.lui      s4, 31
                  c.or       s0, a1
                  c.sub      s0, a1
                  srli       a1, s10, 30
                  sra        t0, t3, s8
                  slt        t2, s2, t5
                  mulh       t6, a2, s10
                  srl        s3, s0, a0
                  mulhsu     a2, a1, s1
                  c.nop
                  and        s7, s11, a7
                  c.lui      s9, 9
                  div        s0, a6, s9
                  and        s4, s8, s4
                  sll        s9, gp, s1
                  slli       t3, t4, 14
                  slti       s8, s9, -583
                  c.srli     a4, 25
                  c.sub      a3, a2
                  lui        ra, 221711
                  c.li       s0, -1
                  sll        sp, sp, t0
                  c.slli     ra, 11
                  c.and      a4, a5
                  divu       t3, t3, t4
                  sub        t6, s1, s2
                  xor        t5, s0, a0
                  c.or       a1, a5
                  rem        a2, gp, a0
                  c.srai     a2, 7
                  add        zero, t2, s8
                  sub        a2, s11, ra
                  c.addi16sp sp, 240
                  c.slli     t1, 20
                  mulhsu     a6, s1, s0
                  xor        t2, t3, s4
                  sltiu      s11, s10, -175
                  remu       t5, s7, s8
                  srl        s7, a1, sp
                  c.addi     s7, 18
                  addi       t1, sp, -122
                  srli       t6, t6, 31
                  c.lui      ra, 3
                  divu       s3, t5, a5
                  c.addi4spn s1, sp, 464
                  slti       s5, s1, 647
                  remu       s3, s9, s2
                  slli       s1, s0, 22
                  rem        s0, t6, s0
                  c.lui      s8, 7
                  c.addi16sp sp, -16
                  addi       s6, s2, 482
                  c.srai     s0, 6
                  slt        zero, s2, s10
                  srai       t2, a0, 24
                  c.addi16sp sp, 320
                  c.slli     t5, 20
                  remu       s1, s2, t3
                  sra        sp, s2, s11
                  c.addi16sp sp, 224
                  c.slli     s3, 21
                  c.srai     a4, 13
                  srli       gp, a4, 24
                  ori        t5, s4, 561
                  slli       s4, zero, 10
                  remu       s4, t3, zero
                  c.sub      a5, a3
                  sra        s4, a6, s3
                  srli       a3, s3, 20
                  mulh       s10, sp, sp
                  c.slli     s1, 31
                  slli       gp, s0, 28
                  c.srli     a3, 19
                  c.xor      a0, s0
                  c.andi     a4, -1
                  mul        t3, s0, tp
                  srai       s11, a3, 8
                  srli       a1, a3, 2
                  divu       a1, a7, s8
                  sub        t2, zero, a6
                  srl        a3, t3, s2
                  c.sub      s0, s1
                  xori       a2, t1, 341
                  li         a4, 0x0 #start riscv_int_numeric_corner_stream_7
                  li         tp, 0x80000000
                  li         s0, 0xffffffff
                  li         t1, 0x0
                  li         gp, 0x80000000
                  li         s1, 0xffffffff
                  li         a2, 0xffffffff
                  li         s10, 0xb00693cb
                  li         ra, 0x566bf44c
                  li         t6, 0xffffffff
                  nop
                  lui        s1, 1027902
                  remu       t6, s1, s1
                  div        a2, tp, gp
                  div        a2, t6, t1
                  addi       ra, s10, 591
                  mulhsu     t1, a2, a4
                  divu       a4, t1, ra
                  auipc      s0, 92064
                  add        a2, a4, t6
                  div        ra, s10, a2
                  mulhsu     s0, s1, gp
                  mul        a2, s10, gp
                  lui        a4, 118066
                  auipc      s0, 80281
                  mulh       s1, a2, ra
                  sub        t6, t6, s10 #end riscv_int_numeric_corner_stream_7
                  c.mv       s3, s7
                  mulhsu     zero, a7, s10
                  c.sub      a2, a2
                  c.and      a4, s1
                  sra        t1, t0, t1
                  c.addi     s4, -1
                  sltiu      s11, sp, -204
                  sll        ra, a0, s2
                  andi       t5, t6, -749
                  c.nop
                  and        t1, t1, sp
                  remu       ra, t1, s2
                  slt        s10, zero, s0
                  srl        t5, s5, a5
                  mulh       s6, s7, s9
                  c.nop
                  slt        ra, a3, s6
                  srli       s3, s1, 24
                  c.or       a3, a3
                  c.xor      a1, a1
                  c.lui      ra, 16
                  lui        s0, 326626
                  c.slli     a4, 4
                  or         gp, a6, s6
                  c.addi16sp sp, 16
                  c.mv       a5, a5
                  slti       s8, s10, 334
                  c.srai     a4, 5
                  mulh       s4, t6, t4
                  c.or       s0, a1
                  xori       t0, s0, 551
                  c.slli     t1, 24
                  srl        t1, s10, a6
                  xor        s1, sp, a7
                  add        gp, t6, s5
                  c.and      a1, a5
                  rem        s4, s1, s8
                  c.li       s4, -1
                  c.lui      a3, 3
                  xor        s4, sp, t3
                  c.li       t1, -1
                  rem        a0, ra, s5
                  or         a6, a2, s0
                  xori       s11, ra, -573
                  mulhu      a1, t2, s6
                  and        a2, s4, a6
                  lui        s6, 83290
                  c.lui      s7, 16
                  c.or       a0, a4
                  mulhsu     a5, s10, t1
                  c.srli     a3, 28
                  c.srai     a4, 17
                  sra        s6, t4, s6
                  mulh       sp, s4, a3
                  and        a1, zero, s5
                  rem        s10, a5, a5
                  c.slli     s1, 21
                  c.mv       a3, gp
                  sll        a5, gp, t1
                  c.sub      a1, a2
                  div        zero, gp, t0
                  c.nop
                  srai       s0, a5, 0
                  sltu       a3, a7, zero
                  srai       s5, t0, 1
                  c.sub      a0, a2
                  c.xor      a4, a5
                  slt        t1, a4, s5
                  sub        gp, gp, a6
                  sltu       gp, s8, a3
                  sra        t6, s4, t3
                  sra        t5, s2, a6
                  c.or       a4, a5
                  ori        s6, s6, -992
                  rem        s5, a3, t6
                  c.addi16sp sp, -16
                  sra        s0, a7, a0
                  c.xor      a2, s0
                  sll        s10, a7, a2
                  c.slli     sp, 3
                  c.slli     t1, 2
                  addi       s8, tp, -672
                  slt        sp, zero, gp
                  c.and      a2, a0
                  sra        zero, a5, a4
                  lui        t5, 257506
                  nop
                  c.sub      a4, a5
                  slti       s3, s10, 47
                  c.slli     t2, 30
                  or         t2, s6, zero
                  c.addi4spn a3, sp, 32
                  c.addi     t3, 18
                  sll        t0, tp, t4
                  c.nop
                  xor        s5, gp, t4
                  andi       s8, s3, 166
                  sltu       a0, a3, s4
                  sll        s11, s6, s0
                  xor        s9, s11, t5
                  srli       s10, t5, 4
                  mulh       s7, s1, a1
                  c.and      a1, a1
                  xori       s9, s3, 892
                  mulhu      tp, t5, a3
                  remu       a3, s8, s9
                  slt        s11, s6, s9
                  c.mv       ra, gp
                  srli       s0, s0, 28
                  c.add      s10, t0
                  c.or       a5, a1
                  srli       a0, t4, 2
                  slli       t0, s8, 23
                  c.addi16sp sp, -16
                  sltiu      s11, a7, 487
                  c.lui      a6, 8
                  c.and      a3, a3
                  c.slli     s7, 27
                  slt        a5, s5, s1
                  andi       s7, a5, 605
                  nop
                  sra        t0, s7, s0
                  srai       s1, s1, 11
                  mulh       gp, s11, s4
                  mulhsu     s7, ra, s8
                  mulhsu     tp, a0, s8
                  sub        s9, t1, t6
                  slli       s0, gp, 26
                  c.srli     a1, 23
                  c.nop
                  mulhsu     tp, s10, s6
                  xori       t2, t2, 414
                  c.or       s0, a4
                  sltiu      s4, t0, 627
                  c.srai     a2, 9
                  slti       zero, t0, -920
                  c.addi4spn s0, sp, 384
                  remu       a5, a0, a6
                  lui        s0, 230647
                  sub        s3, s6, s0
                  ori        sp, t0, 112
                  remu       ra, s2, t2
                  c.slli     s11, 3
                  divu       s8, t2, s3
                  c.srai     s1, 2
                  srli       s7, a2, 10
                  mulhsu     a3, a6, zero
                  c.li       tp, 16
                  c.addi     s10, -1
                  mulhu      t2, t0, zero
                  or         t6, a7, s6
                  sra        a2, a7, t2
                  c.nop
                  srli       s7, s9, 10
                  c.mv       gp, sp
                  mulh       s9, t4, tp
                  c.addi4spn s1, sp, 368
                  xori       s3, s5, -595
                  mulhu      a0, s6, a1
                  c.or       a2, a5
                  sltiu      zero, s5, 758
                  addi       s1, s7, 22
                  slt        tp, s8, s11
                  slti       s4, a4, 838
                  andi       s1, s11, 218
                  xor        s5, tp, t1
                  xor        s6, s4, a7
                  slti       a0, a2, 179
                  mulhsu     s3, s3, s8
                  lui        a2, 313915
                  xor        s5, s11, t1
                  c.sub      a0, s0
                  c.addi16sp sp, -16
                  addi       t0, a7, 158
                  mulhsu     s4, t1, ra
                  c.addi4spn s0, sp, 576
                  auipc      s10, 365616
                  srli       sp, t2, 17
                  mul        s0, s4, s11
                  xor        s8, s1, a1
                  and        t0, a2, s1
                  or         a5, s4, s4
                  c.sub      a5, a0
                  xori       a0, t0, 406
                  slli       gp, s5, 3
                  mul        ra, t1, s5
                  sll        s4, s0, s3
                  rem        ra, sp, s8
                  c.srli     a4, 6
                  c.xor      s0, a4
                  lui        s4, 146536
                  nop
                  c.mv       a0, s8
                  sltu       s3, s5, t1
                  or         s4, t6, gp
                  mulh       s7, s10, t5
                  mulh       gp, s8, s2
                  c.sub      s0, a2
                  divu       t3, s6, t2
                  c.addi16sp sp, -16
                  c.or       a5, a5
                  c.xor      s0, a2
                  srl        a3, s1, a5
                  rem        a4, s5, t2
                  ori        a3, s5, 493
                  c.nop
                  c.addi     s3, -1
                  slli       t0, t1, 11
                  c.lui      gp, 30
                  xor        s4, t5, t1
                  c.nop
                  sll        s5, t6, s0
                  mul        t3, s3, t5
                  slt        s0, t2, s8
                  slt        s9, s6, a2
                  nop
                  srl        s10, s5, s4
                  c.srli     s1, 10
                  c.addi16sp sp, 400
                  divu       sp, zero, t6
                  add        ra, t5, t0
                  div        s9, s5, t0
                  c.nop
                  srli       s5, ra, 0
                  div        s7, s6, s9
                  sltiu      s4, s1, 358
                  c.addi     a5, -1
                  c.mv       s10, t1
                  srl        s10, a6, s7
                  slt        s1, a6, t2
                  c.li       s5, 20
                  remu       t5, s6, s2
                  c.add      a4, tp
                  remu       a0, t2, a6
                  nop
                  divu       a1, a0, s1
                  srli       s7, t6, 9
                  auipc      s4, 71880
                  c.li       a4, -1
                  c.li       sp, -1
                  nop
                  c.srai     a4, 5
                  slt        t6, t6, s7
                  sltu       s9, tp, a4
                  mulh       a6, sp, tp
                  nop
                  c.srli     a2, 1
                  mulhu      s3, s9, a3
                  rem        s9, t0, a6
                  add        s5, t2, a6
                  lui        s11, 198026
                  andi       a2, s9, 294
                  c.add      gp, a6
                  andi       s7, s0, 921
                  c.lui      s7, 29
                  divu       a0, t3, a3
                  add        t6, s2, s8
                  sltiu      t5, a0, 243
                  c.nop
                  auipc      s9, 187200
                  c.slli     a5, 26
                  c.srli     a1, 25
                  sub        a6, s6, ra
                  sll        s10, a3, sp
                  c.slli     ra, 15
                  or         tp, a4, ra
                  sub        t5, s3, s7
                  c.or       s0, a5
                  c.srli     a1, 4
                  srl        t2, a3, s11
                  sltu       tp, t1, t6
                  mulhu      s5, gp, s6
                  auipc      t2, 765560
                  c.or       a4, s0
                  c.addi4spn s1, sp, 240
                  xor        s4, s0, s7
                  sltu       t3, s8, gp
                  srli       a0, a3, 10
                  c.slli     a1, 28
                  addi       s11, tp, -426
                  mulhu      a5, t6, t6
                  mulhsu     t0, tp, t0
                  xori       s11, sp, -31
                  c.addi16sp sp, -16
                  and        t3, a1, s7
                  c.and      a3, a2
                  div        s1, a0, a3
                  xor        t1, t1, s4
                  c.and      a3, a2
                  c.addi4spn a0, sp, 176
                  mulhu      zero, s8, t5
                  addi       s5, a3, -633
                  c.li       t2, -1
                  sra        t0, t0, s0
                  c.addi16sp sp, 352
                  divu       a4, a7, a7
                  c.addi     sp, 30
                  sub        s3, t6, s0
                  c.nop
                  c.or       a1, a5
                  mulhsu     s10, tp, s0
                  addi       a0, s6, 495
                  auipc      a5, 617436
                  c.nop
                  slti       s0, t0, -411
                  mulh       t1, t4, a7
                  mulhu      s9, s8, s11
                  c.addi4spn a0, sp, 656
                  slli       t6, a1, 25
                  slt        s8, t2, s10
                  c.or       a4, s1
                  c.xor      s1, s1
                  c.and      a4, a3
                  and        a5, t4, t6
                  c.addi16sp sp, 448
                  sltiu      t2, tp, 793
                  sltiu      a4, s9, 494
                  ori        s4, a0, 550
                  li         t1, 0xffffffff #start riscv_int_numeric_corner_stream_23
                  li         s8, 0x0
                  li         a5, 0xffffffff
                  li         t5, 0x0
                  li         s7, 0x0
                  li         s10, 0x80000000
                  li         t0, 0x80000000
                  li         tp, 0x0
                  li         gp, 0x0
                  li         t6, 0x80000000
                  addi       s8, s8, 193
                  mulhu      t0, a5, tp
                  lui        t1, 621509
                  divu       s7, s8, gp
                  mulh       a5, a5, t1
                  mul        t0, tp, t6
                  mulhsu     t1, gp, s8
                  mulhsu     s8, s10, tp
                  remu       gp, gp, t0
                  nop
                  mulhsu     t1, t6, t1
                  div        tp, t6, a5
                  mul        gp, t0, tp
                  lui        t6, 812378
                  mul        t6, s8, gp
                  nop
                  mulhu      t6, t6, gp
                  sub        s10, s10, t1
                  sub        t6, s8, t1
                  lui        s7, 753983
                  sub        gp, tp, tp #end riscv_int_numeric_corner_stream_23
                  mulh       gp, a6, s8
                  sltiu      s0, s8, -471
                  xor        t5, a5, s9
                  sltiu      tp, t0, -401
                  c.add      s9, s2
                  c.sub      a0, a0
                  c.xor      s1, a3
                  c.nop
                  sll        a3, s9, t2
                  rem        s5, s7, s1
                  c.add      t5, sp
                  c.slli     t1, 17
                  c.xor      s1, a5
                  sub        a3, zero, a6
                  c.and      a1, s0
                  mulhu      s6, a5, a3
                  mulhsu     a6, tp, a5
                  c.slli     s1, 31
                  xor        a3, tp, sp
                  or         zero, s0, t3
                  rem        s11, a7, s9
                  sltiu      s11, zero, -686
                  sltu       a0, zero, a2
                  or         t6, a1, sp
                  or         t2, a2, a1
                  slt        a1, t0, t4
                  or         a5, sp, t6
                  c.nop
                  srl        s1, s11, t2
                  c.addi16sp sp, -16
                  sll        s11, s6, s4
                  and        s6, t3, t1
                  div        s5, a5, t2
                  c.add      a5, s9
                  sra        ra, t2, s2
                  mul        sp, s9, s8
                  c.srai     a0, 2
                  slli       zero, a0, 16
                  c.addi16sp sp, 16
                  mulh       a4, t3, t2
                  auipc      a2, 7822
                  or         sp, gp, t2
                  c.slli     ra, 18
                  c.addi4spn a4, sp, 800
                  sltu       s8, s4, s11
                  ori        s10, s11, -69
                  c.addi16sp sp, -16
                  sltu       a4, s0, a3
                  sub        t0, s10, s4
                  rem        s3, a4, s7
                  c.xor      a3, s0
                  sll        sp, a5, t3
                  addi       s4, t4, 691
                  c.sub      a5, a0
                  auipc      t3, 1001693
                  c.or       s0, s1
                  lui        a6, 884890
                  srl        t2, t6, t0
                  c.addi16sp sp, -16
                  c.xor      a3, a4
                  sub        s8, s0, t4
                  c.and      a1, a3
                  sltiu      a3, a6, -577
                  rem        s5, s11, s8
                  mul        s0, tp, a4
                  mulh       sp, s8, s0
                  c.or       a5, a5
                  divu       t0, s8, a4
                  mul        s11, t2, zero
                  and        t0, a0, t0
                  c.xor      s1, a3
                  mulhu      s7, tp, t2
                  c.srai     a5, 18
                  or         s5, t2, ra
                  c.li       a1, -1
                  slt        gp, t4, s2
                  slti       t2, t3, 874
                  c.addi4spn a4, sp, 112
                  srli       t2, t0, 18
                  addi       tp, s5, -898
                  c.li       t3, 12
                  c.xor      a1, s0
                  sltu       t3, a1, t1
                  c.and      a4, s1
                  sra        s11, s2, ra
                  c.andi     a4, -1
                  or         t0, s4, a6
                  mulhu      s8, s9, s1
                  c.srli     a2, 5
                  c.addi4spn a3, sp, 384
                  c.addi     s0, -1
                  slt        zero, a2, s8
                  c.and      a5, s1
                  c.slli     s3, 2
                  srai       s7, a7, 23
                  and        s0, t3, a4
                  c.addi16sp sp, 352
                  lui        s4, 109214
                  or         a3, a4, a5
                  c.xor      a5, a0
                  mulhu      zero, s6, tp
                  lui        zero, 478181
                  c.add      s0, t4
                  c.xor      s1, a4
                  and        a3, s5, t4
                  c.sub      a4, a1
                  c.xor      a4, a0
                  srai       s10, a2, 0
                  nop
                  xor        a5, t2, a2
                  c.sub      s1, a2
                  sra        s1, a0, t4
                  c.li       a5, 3
                  div        s1, s9, a0
                  xor        a5, a1, s10
                  xori       a5, tp, -57
                  sra        t2, s2, zero
                  c.mv       a4, t6
                  remu       s5, s6, a7
                  auipc      t0, 996990
                  div        s11, t5, t3
                  lui        s7, 810391
                  c.nop
                  mulh       a4, a2, t5
                  divu       a1, t1, gp
                  mulhsu     s7, t5, s3
                  c.mv       t6, a3
                  c.mv       s4, s10
                  mulh       s0, gp, ra
                  c.slli     s0, 15
                  sub        s0, t4, a6
                  c.andi     a1, -1
                  nop
                  srl        a0, sp, t3
                  c.mv       a3, s10
                  rem        tp, tp, s1
                  c.xor      a3, s0
                  sra        s4, s7, t1
                  srai       s1, t5, 16
                  slli       t5, t1, 9
                  c.addi16sp sp, 32
                  mul        s4, a1, s0
                  rem        t1, a6, a1
                  nop
                  mulhu      t5, a4, sp
                  sltu       s4, t1, zero
                  c.li       a0, -1
                  c.mv       a4, t0
                  srl        s5, zero, s6
                  or         t6, s6, t5
                  c.or       a1, a4
                  srli       s3, tp, 26
                  c.lui      t3, 10
                  slti       s1, s1, 796
                  c.andi     a4, 23
                  c.srli     a3, 8
                  c.slli     s0, 18
                  lui        zero, 766106
                  ori        zero, a2, -579
                  c.li       tp, -1
                  xori       a6, s8, -513
                  slt        a0, s3, t0
                  c.mv       s10, s3
                  rem        t3, ra, t4
                  andi       a6, a3, -241
                  c.srli     a5, 8
                  add        s6, gp, s4
                  or         tp, s0, zero
                  ori        t3, s11, -657
                  slti       ra, gp, 629
                  xor        a5, zero, t5
                  c.andi     a5, 13
                  or         s0, t2, s1
                  and        s5, t4, s10
                  rem        a2, a0, t6
                  sub        sp, zero, t2
                  slti       s10, s10, -520
                  srl        t2, t6, s9
                  divu       sp, a6, a5
                  c.mv       s9, a1
                  c.sub      a3, a1
                  c.andi     a4, -1
                  add        s4, a1, sp
                  c.srai     a0, 8
                  sltiu      t3, s7, -253
                  c.slli     t0, 23
                  remu       tp, s0, a4
                  c.slli     s10, 19
                  sra        t6, a1, a0
                  c.srai     s0, 27
                  srli       t3, s6, 19
                  c.and      a0, s1
                  sub        t6, t4, a7
                  slli       gp, s7, 29
                  xor        t3, t1, a7
                  c.addi     t1, 6
                  c.slli     t3, 22
                  xor        zero, t3, s2
                  xori       t2, a0, -736
                  srai       s11, s11, 8
                  c.li       t1, 30
                  divu       s10, t4, t2
                  div        zero, t2, zero
                  add        a2, t4, s7
                  c.and      a5, a2
                  c.addi     t3, -1
                  lui        s1, 587300
                  addi       ra, t2, 1013
                  ori        t6, a1, -448
                  srl        s9, a5, s6
                  addi       tp, s8, 816
                  mulhu      a6, s11, t6
                  slli       ra, gp, 9
                  sll        s8, t2, s4
                  ori        s1, zero, -895
                  and        s8, a2, t4
                  c.addi4spn a5, sp, 336
                  auipc      a4, 685259
                  slti       s4, s3, 261
                  sra        a5, s5, t5
                  srli       t5, s3, 31
                  divu       s10, s8, s8
                  sll        s7, tp, s9
                  ori        a3, s6, 935
                  c.add      s3, t4
                  remu       s1, s4, sp
                  mulhu      a0, zero, a7
                  c.lui      t1, 25
                  or         s5, zero, s7
                  sra        s9, sp, a5
                  c.and      a3, a4
                  nop
                  sub        sp, t5, a7
                  xor        a0, a1, a0
                  c.srai     a3, 31
                  or         s10, s0, s0
                  c.addi4spn a4, sp, 464
                  c.sub      a0, s0
                  srl        a5, gp, s0
                  c.srai     a2, 3
                  c.slli     tp, 11
                  srli       t1, a1, 16
                  c.addi16sp sp, 128
                  mul        s11, s6, a6
                  mul        t0, a5, s11
                  c.addi4spn s0, sp, 720
                  sll        s6, a0, t5
                  c.or       a2, a4
                  sll        ra, a5, a0
                  sll        t2, a7, t1
                  c.slli     t3, 28
                  sub        s6, s10, a3
                  divu       s7, ra, s4
                  srai       a4, t1, 30
                  sll        s7, s8, a1
                  c.and      a4, a2
                  slli       a3, s8, 4
                  mul        a2, t1, t0
                  sltu       a3, gp, s5
                  sltiu      s8, s5, -237
                  c.addi     s8, 18
                  srl        t0, a7, gp
                  c.addi4spn a5, sp, 944
                  nop
                  c.lui      s10, 28
                  and        a5, s0, ra
                  c.or       a4, a2
                  c.mv       ra, s4
                  srli       tp, s10, 30
                  slti       s3, t3, -924
                  auipc      s4, 431081
                  ori        a4, s9, 659
                  mulhu      a1, a1, a6
                  andi       zero, s1, -172
                  andi       t2, s6, 370
                  c.sub      a5, a1
                  div        t6, s0, a6
                  slt        s5, s6, s8
                  c.andi     a0, -1
                  slt        t0, a7, t4
                  lui        a4, 698397
                  rem        s11, s5, t1
                  srli       s7, s8, 1
                  and        s5, a0, t3
                  c.lui      t2, 16
                  c.nop
                  srai       a0, s5, 9
                  slt        s4, t1, s1
                  nop
                  sub        a5, s2, s4
                  or         t5, s3, a2
                  c.mv       s7, s5
                  sra        a3, s1, a3
                  mulhu      a3, sp, a2
                  slli       zero, t4, 2
                  c.lui      t1, 22
                  c.or       a2, a0
                  lui        s6, 530538
                  auipc      a1, 843715
                  and        t3, a7, s3
                  c.addi16sp sp, -16
                  slli       s0, a6, 11
                  remu       s8, ra, t0
                  div        a3, ra, s1
                  addi       t3, tp, 372
                  xor        s4, s2, t1
                  c.and      a1, a4
                  c.slli     a4, 17
                  c.xor      a4, a3
                  sltiu      a1, a0, -575
                  mul        s3, t3, a6
                  c.addi4spn a0, sp, 896
                  c.slli     t0, 11
                  slti       s10, s4, -467
                  sltu       s4, tp, zero
                  c.addi16sp sp, 224
                  c.addi4spn s1, sp, 144
                  c.andi     a1, 0
                  andi       t0, s4, -246
                  nop
                  nop
                  andi       gp, s10, -465
                  ori        a1, t2, 244
                  remu       t5, a4, zero
                  sltu       t0, sp, a4
                  mulhu      ra, t6, sp
                  c.li       a0, 17
                  div        t3, t4, s7
                  nop
                  sub        s10, a7, s8
                  c.mv       a6, t5
                  srai       s9, gp, 19
                  srai       gp, s8, 16
                  add        a5, a5, a5
                  remu       a0, s9, t3
                  div        s0, s1, t4
                  sub        s4, s10, a5
                  divu       s1, a7, s5
                  and        s10, s8, a5
                  xori       t6, s8, 982
                  slt        t6, s9, s7
                  andi       s7, t3, 27
                  c.add      t5, s10
                  c.sub      a0, a1
                  sll        s5, s3, a4
                  c.nop
                  mulh       ra, s4, a6
                  c.srai     s1, 15
                  sltiu      s5, a3, 569
                  xori       a3, t3, -165
                  c.add      s0, t5
                  slt        s3, s11, a4
                  c.addi4spn a0, sp, 352
                  c.and      a5, a4
                  c.li       s11, -1
                  srli       a5, a1, 30
                  mulh       s0, a7, s10
                  add        s1, s11, s5
                  sll        a0, t1, s6
                  and        s1, s3, ra
                  c.andi     a5, 2
                  auipc      s3, 769190
                  auipc      zero, 63592
                  and        s11, a2, t5
                  sll        a3, zero, zero
                  xor        s9, t1, a3
                  c.sub      a4, a4
                  xori       s5, s11, 141
                  slti       t0, a0, 420
                  c.andi     a3, 23
                  c.srli     a3, 21
                  c.sub      a0, s0
                  and        s1, t1, t6
                  div        sp, t3, a5
                  c.addi16sp sp, -16
                  auipc      a4, 557125
                  c.mv       a2, s2
                  xor        zero, s7, gp
                  c.srai     s1, 23
                  sltiu      a6, ra, 667
                  div        s6, s9, a0
                  sub        t2, a6, s0
                  srai       a3, s10, 30
                  or         s3, a7, zero
                  sra        a3, ra, s5
                  ori        s7, t2, 370
                  c.nop
                  c.lui      t1, 22
                  c.srai     a0, 19
                  sltiu      s7, s6, 632
                  add        tp, a7, a4
                  c.addi     s0, 27
                  srl        s3, s8, s2
                  c.and      a4, a4
                  slti       t6, s1, -785
                  mulhu      a3, s7, a5
                  srai       a1, s2, 31
                  mulh       t6, s6, t4
                  sltu       ra, t1, s0
                  slt        s9, a1, s2
                  addi       a3, a7, -537
                  xor        s8, ra, zero
                  c.slli     s9, 10
                  sll        s7, t5, s10
                  addi       a3, s11, -908
                  andi       gp, gp, -584
                  c.add      s5, t5
                  sltiu      a4, a7, 849
                  divu       a1, t0, t6
                  slti       a5, t1, -841
                  c.srai     a0, 4
                  srli       s11, s6, 22
                  c.slli     t2, 7
                  sub        gp, t6, a7
                  c.or       s0, a4
                  mulhsu     s1, a3, t0
                  srl        a2, t3, a5
                  c.and      a3, a4
                  mulhu      s4, sp, ra
                  c.slli     a1, 4
                  srl        zero, s2, a3
                  srai       s9, a0, 23
                  c.lui      a5, 17
                  srl        s4, s4, t0
                  c.addi4spn s1, sp, 480
                  slti       ra, a6, -655
                  mulhsu     t3, a4, a4
                  ori        s1, a0, -748
                  sra        t2, a0, ra
                  c.add      s11, t2
                  rem        a0, sp, s6
                  c.nop
                  srl        a3, s11, s4
                  or         t0, gp, a2
                  srli       tp, s4, 16
                  srli       t1, s8, 17
                  and        t6, a4, a2
                  addi       s5, tp, -91
                  addi       s4, s11, 276
                  c.slli     t3, 3
                  andi       s5, t2, -478
                  c.add      t5, t2
                  slti       s7, s1, -910
                  nop
                  add        s1, ra, sp
                  lui        s6, 333329
                  slti       a0, sp, 520
                  srli       a3, s3, 10
                  lui        s8, 436387
                  c.xor      a2, a2
                  c.lui      s9, 19
                  c.mv       s9, a1
                  c.sub      a2, a5
                  slli       t1, gp, 21
                  c.slli     t3, 11
                  and        s0, a6, a3
                  addi       a5, sp, -276
                  c.nop
                  sltu       s5, a5, a7
                  c.lui      s10, 6
                  c.srai     s0, 13
                  sltu       t2, a6, zero
                  c.nop
                  srai       s6, a3, 3
                  srl        a4, t3, zero
                  auipc      s6, 561645
                  c.addi     s0, -1
                  sra        a4, zero, s8
                  c.andi     a5, -1
                  auipc      a2, 849453
                  mulh       s8, gp, t3
                  srl        a0, s11, s2
                  c.add      a4, s5
                  auipc      s1, 556956
                  c.add      gp, a2
                  mulhsu     t0, t2, zero
                  div        a2, gp, s9
                  addi       s3, s7, -809
                  c.add      t5, a6
                  c.xor      a1, s1
                  slti       t5, s4, -79
                  or         s3, t5, s5
                  srai       a3, s6, 23
                  c.addi4spn s1, sp, 400
                  slti       t2, sp, 774
                  slli       t0, a5, 21
                  slli       a3, s6, 18
                  c.add      s4, a0
                  addi       s3, s6, -555
                  sub        a5, t1, t4
                  c.and      a5, a1
                  rem        s3, t2, t5
                  and        a5, s2, s2
                  remu       s1, gp, s4
                  srli       s11, s2, 1
                  srli       s4, a5, 28
                  c.addi16sp sp, -16
                  c.srai     s0, 11
                  sub        gp, t6, s1
                  c.andi     a5, 8
                  div        a4, a0, tp
                  xori       s10, gp, 810
                  and        a1, s4, a6
                  c.addi16sp sp, 16
                  slti       a6, a3, -281
                  c.mv       a5, s1
                  rem        t0, s9, a5
                  c.sub      a5, a3
                  c.slli     s5, 23
                  mulhu      t1, t3, s5
                  mulh       a0, s3, s10
                  c.nop
                  remu       a5, sp, s10
                  c.add      t6, s8
                  lui        t6, 11821
                  sll        s1, t0, s0
                  slt        s6, a3, t0
                  slti       s11, s0, -10
                  andi       s4, t5, -760
                  div        a6, t6, s0
                  c.srai     s0, 16
                  c.add      ra, t4
                  srli       t2, a3, 4
                  c.addi16sp sp, -16
                  rem        t1, s4, tp
                  slt        t6, s5, a0
                  c.addi16sp sp, 352
                  mul        gp, s11, t6
                  c.nop
                  mulhsu     s11, s6, t0
                  c.sub      a3, s1
                  sub        a0, a3, t1
                  mulh       s8, s6, a1
                  rem        s9, a7, s9
                  c.slli     a0, 23
                  addi       t6, t2, -119
                  sll        t1, t1, a0
                  c.sub      a0, s1
                  srl        a5, a7, a3
                  srl        t0, sp, s9
                  xor        t6, s1, t5
                  mulhsu     a1, s1, s0
                  sltu       s1, a4, s3
                  sll        t6, s3, s10
                  c.xor      a0, a1
                  c.srli     s1, 6
                  addi       t5, s8, 655
                  div        gp, t4, tp
                  rem        a1, a6, s10
                  div        s7, s8, s6
                  c.andi     a5, 2
                  c.sub      a0, a1
                  mulhu      t0, s4, t3
                  div        s8, s7, t6
                  srli       t6, t0, 26
                  slti       s10, t3, 654
                  addi       t5, s2, -160
                  srli       s7, t0, 25
                  addi       t2, t2, -423
                  div        s3, a4, sp
                  add        gp, s10, a6
                  rem        a2, zero, a7
                  c.mv       s5, s10
                  divu       s1, a4, s3
                  addi       t3, t1, 803
                  sll        a4, a1, a4
                  xor        t1, a3, s2
                  c.addi     s4, 5
                  divu       s3, s7, t1
                  xori       zero, a7, 365
                  srai       a6, s9, 16
                  ori        t5, s11, 762
                  auipc      s0, 490988
                  c.mv       a1, s2
                  mul        s3, a5, a3
                  mulhsu     s10, a6, a5
                  or         tp, a4, t5
                  c.nop
                  lui        tp, 830482
                  nop
                  c.andi     s1, -1
                  sltiu      s5, s4, -21
                  divu       a3, a4, tp
                  c.addi     s11, 21
                  c.srai     a4, 1
                  c.and      a4, a2
                  sub        t6, t3, a5
                  addi       a3, a0, -608
                  sll        ra, s3, t6
                  srai       s4, a2, 31
                  c.sub      a3, a0
                  remu       t5, t6, a0
                  c.and      a5, a2
                  andi       a1, ra, 148
                  c.slli     s6, 28
                  slt        t2, t0, s2
                  div        s6, t4, t4
                  xor        gp, a6, a4
                  c.mv       a5, a3
                  c.addi16sp sp, 80
                  sll        sp, t2, s8
                  c.srli     a5, 18
                  c.add      t5, s10
                  sra        a4, s3, t6
                  sub        s6, s11, s2
                  div        s9, zero, s5
                  c.xor      s1, a0
                  c.nop
                  ori        a3, t6, 417
                  rem        gp, a2, s10
                  ori        s5, gp, -534
                  nop
                  nop
                  c.lui      s7, 26
                  c.addi4spn a5, sp, 608
                  c.srai     a1, 27
                  mul        s0, t2, a4
                  sub        t2, a2, gp
                  slt        t1, s7, s4
                  srli       s1, s1, 20
                  c.addi     tp, -1
                  srl        a6, s3, zero
                  srl        s5, t5, t6
                  remu       a3, t0, a6
                  slt        s3, t2, zero
                  sub        gp, t1, s6
                  c.andi     a0, -1
                  sub        ra, t4, s10
                  slti       s5, s4, -798
                  c.mv       s7, ra
                  c.lui      s0, 24
                  addi       s0, s9, 93
                  ori        a3, gp, -695
                  sltiu      s1, s2, 330
                  c.and      a1, a1
                  c.sub      a3, a0
                  c.addi4spn a5, sp, 336
                  xori       a3, a5, -234
                  and        a2, s7, s3
                  c.andi     a2, -1
                  sltiu      t6, t3, -390
                  divu       s5, s8, a6
                  mul        s0, tp, s2
                  andi       a1, ra, -565
                  and        sp, zero, a5
                  mulh       sp, a5, t6
                  andi       a3, a6, -140
                  sub        s7, sp, t0
                  c.sub      a2, a4
                  divu       gp, a7, t3
                  sltu       s7, t0, t6
                  c.addi4spn a4, sp, 16
                  sll        gp, a0, s11
                  srai       s1, a0, 13
                  or         s7, gp, s0
                  c.srli     s1, 5
                  c.addi16sp sp, 64
                  c.or       s1, a2
                  slti       t2, a3, 550
                  c.addi16sp sp, 384
                  c.lui      a3, 1
                  divu       s7, s10, s9
                  lui        t3, 989300
                  lui        a2, 20713
                  slt        t3, s9, t1
                  c.xor      s0, a5
                  c.lui      s3, 13
                  mul        gp, a2, s1
                  c.srli     a1, 9
                  lui        a6, 169151
                  auipc      t3, 738268
                  mulhsu     sp, s8, a6
                  mulhu      s9, a5, sp
                  nop
                  lui        s7, 574113
                  c.mv       s11, s8
                  srai       a2, s5, 3
                  c.andi     s0, 0
                  c.li       t0, -1
                  divu       a3, t0, a6
                  mulhu      s8, tp, t1
                  sltu       ra, s4, s10
                  sltu       s0, s10, s4
                  c.nop
                  xor        t5, s1, a0
                  remu       s0, a5, t0
                  c.lui      t6, 21
                  slti       t0, t1, -681
                  c.addi16sp sp, -16
                  sra        t0, s7, a5
                  c.addi16sp sp, -16
                  xor        s4, s0, a5
                  srli       zero, s6, 5
                  xori       t6, s0, -334
                  andi       gp, s3, -864
                  c.xor      a0, a1
                  srl        t5, a1, a7
                  mulhsu     s11, a6, a5
                  addi       s3, a4, 895
                  c.srli     a2, 15
                  c.srai     s0, 27
                  mulhu      a2, a3, zero
                  or         a2, s5, s5
                  c.add      s10, a6
                  c.andi     s1, -1
                  c.addi4spn s0, sp, 320
                  nop
                  or         t2, s7, s10
                  remu       s0, a4, t2
                  rem        s7, sp, ra
                  sra        s6, s6, zero
                  c.or       a4, s1
                  c.xor      a1, a4
                  sub        s10, s2, s10
                  mulh       zero, a2, t4
                  sub        a6, s2, t2
                  c.addi16sp sp, 352
                  andi       a2, ra, -529
                  srl        s4, a3, t4
                  slli       a2, t6, 23
                  c.addi16sp sp, 32
                  nop
                  c.addi16sp sp, 384
                  c.addi     sp, -1
                  c.addi     a5, -1
                  andi       tp, s7, 467
                  mul        ra, t4, gp
                  mul        a1, s9, s3
                  sra        a3, s2, s8
                  xor        t2, s0, a7
                  c.srli     s0, 8
                  c.add      a0, a3
                  mulhsu     t2, t5, a7
                  c.addi4spn a1, sp, 720
                  sll        gp, a1, zero
                  or         a6, s7, s5
                  ori        s1, s7, -670
                  lui        tp, 449825
                  mulhsu     s8, s6, tp
                  or         ra, a7, s9
                  nop
                  mulhu      s0, a4, s6
                  mulhu      t0, a7, t2
                  c.sub      s1, a3
                  slti       a6, s0, 612
                  c.addi4spn a1, sp, 192
                  add        t6, s4, sp
                  and        s9, t6, s8
                  sll        t6, s2, s1
                  sltiu      a3, t3, -597
                  c.nop
                  mulh       t1, tp, a4
                  slti       sp, s4, 689
                  c.addi     a4, 29
                  c.addi16sp sp, 480
                  nop
                  c.srai     s1, 17
                  c.addi16sp sp, 192
                  ori        gp, a4, 19
                  c.li       s4, 16
                  c.or       a3, s1
                  srli       t6, gp, 5
                  sub        s9, zero, s9
                  addi       a0, s2, 365
                  add        a1, s3, s5
                  c.addi4spn s0, sp, 496
                  addi       a0, t5, -721
                  c.addi16sp sp, -16
                  nop
                  mulhu      t1, gp, t6
                  c.or       a1, a0
                  c.or       a3, a2
                  remu       t3, s1, a7
                  c.addi16sp sp, -16
                  sll        a6, a6, t0
                  rem        a5, a0, a7
                  addi       s7, s6, -97
                  c.addi4spn a4, sp, 528
                  c.sub      s1, a1
                  remu       s0, gp, a1
                  c.add      t6, s1
                  slti       s6, s6, -864
                  rem        a4, a3, s9
                  xori       tp, t0, -409
                  ori        ra, s7, -1003
                  c.lui      a2, 29
                  c.or       s1, a4
                  add        s4, t3, t6
                  xor        a6, t5, s8
                  slt        s1, s9, t1
                  c.addi     a3, -1
                  c.srli     a3, 13
                  c.and      s1, a5
                  slti       a0, tp, -674
                  c.addi4spn a5, sp, 1008
                  srli       t0, a6, 23
                  sra        a3, s8, s5
                  sra        s9, a0, a1
                  mulhsu     t3, a1, s5
                  c.lui      s8, 1
                  c.li       a3, -1
                  ori        s11, ra, -863
                  srli       s6, a0, 26
                  c.srai     s0, 27
                  c.nop
                  c.lui      t2, 22
                  c.li       t2, 2
                  c.or       s1, a2
                  add        gp, t2, sp
                  sltiu      s6, s3, -632
                  srai       s9, s6, 21
                  mul        a6, s1, a5
                  c.addi4spn a4, sp, 784
                  sub        a3, s0, t1
                  mul        s9, a1, sp
                  c.addi4spn a4, sp, 304
                  c.andi     s1, -1
                  sll        a1, t3, a0
                  c.lui      t0, 31
                  nop
                  sltiu      t2, s7, -106
                  remu       s9, s6, a4
                  slli       s7, s10, 0
                  remu       a0, s11, a1
                  rem        a0, a3, ra
                  slt        s4, tp, sp
                  sub        s10, s3, s8
                  c.xor      s0, a3
                  slti       sp, s11, 222
                  and        zero, s9, sp
                  c.srai     s1, 30
                  lui        gp, 187417
                  lui        s8, 470994
                  c.add      s3, a3
                  xor        t0, a5, t6
                  div        s0, zero, a2
                  mulhsu     tp, s6, t6
                  slti       t2, ra, 188
                  srai       a3, s3, 12
                  c.slli     a3, 28
                  c.srai     s0, 25
                  c.srli     a3, 5
                  slli       s9, s0, 28
                  srai       t0, s0, 27
                  remu       t2, a1, s1
                  mulhsu     t5, t2, s0
                  slti       t6, s0, 565
                  sltiu      t5, s0, -673
                  c.or       a2, a2
                  addi       tp, sp, 654
                  c.li       s8, 16
                  c.srai     s1, 3
                  slt        s5, ra, s8
                  div        s9, t2, s10
                  addi       s7, ra, 358
                  andi       a2, t4, -579
                  c.mv       s11, s7
                  mulhsu     t5, s4, sp
                  slti       sp, s7, 598
                  mul        s5, zero, s8
                  divu       a6, s1, s2
                  c.andi     a5, 27
                  sra        gp, a2, s7
                  rem        zero, s2, a4
                  ori        a0, s4, 925
                  mulhsu     a4, t2, s6
                  c.andi     a3, -1
                  lui        a3, 217894
                  xor        s11, s8, a6
                  xori       tp, s9, -151
                  remu       t2, t4, s3
                  mulhsu     s6, a5, ra
                  and        t6, t6, t2
                  sub        a5, gp, a4
                  c.lui      s9, 23
                  c.srli     a1, 2
                  lui        ra, 283775
                  sub        a4, sp, a5
                  c.li       gp, -1
                  sltu       t5, s8, t2
                  lui        s10, 745206
                  auipc      s7, 18608
                  mulh       s11, s6, t0
                  lui        s1, 211418
                  sltiu      t6, a2, 121
                  or         ra, a5, s8
                  srai       s7, s9, 2
                  and        a0, s10, zero
                  lui        tp, 30237
                  lui        s5, 573656
                  divu       s10, ra, sp
                  c.xor      a5, a3
                  auipc      s3, 862922
                  sra        s11, a0, a7
                  rem        a6, s10, s5
                  auipc      a1, 689833
                  mulhsu     s5, t4, s7
                  and        s4, s1, s7
                  c.nop
                  and        t0, s7, t0
                  or         a3, sp, a5
                  c.xor      a3, s1
                  c.li       a0, 20
                  auipc      a4, 430259
                  slti       s0, a0, 670
                  auipc      s4, 526750
                  ori        a5, t5, -798
                  c.xor      s1, s0
                  srl        t1, sp, t3
                  c.and      a1, s0
                  mulhu      a3, t2, s10
                  mulh       s10, t4, gp
                  slti       t1, a6, -976
                  c.andi     a5, -1
                  nop
                  c.mv       ra, a1
                  c.nop
                  mulhsu     s10, s10, t3
                  slt        zero, ra, s8
                  mul        s6, s2, a2
                  xori       t6, t5, 149
                  c.srai     s1, 20
                  c.sub      a2, a5
                  c.addi4spn a4, sp, 208
                  c.addi4spn a3, sp, 576
                  div        a5, zero, s2
                  addi       ra, t1, -717
                  srai       t5, s7, 31
                  sra        s11, s1, s8
                  xori       s7, a7, -265
                  c.li       s4, 2
                  nop
                  c.srai     a3, 3
                  srli       s4, t5, 8
                  c.add      s4, s3
                  add        a6, s3, s0
                  c.or       s1, a4
                  c.lui      ra, 2
                  sll        a3, a1, a1
                  c.slli     s4, 23
                  add        a1, t6, t3
                  xor        a0, a2, s10
                  nop
                  remu       s4, a6, a0
                  c.or       a5, a5
                  c.lui      s7, 29
                  li         t1, 0xffffffff #start riscv_int_numeric_corner_stream_18
                  li         a2, 0x80000000
                  li         s1, 0xa78a7801
                  li         t2, 0x80000000
                  li         tp, 0xf7289b6c
                  li         s3, 0x4b55113f
                  li         s7, 0x80000000
                  li         s6, 0xf78abd28
                  li         t5, 0x80000000
                  li         ra, 0x0
                  lui        t2, 743247
                  addi       a2, s3, -295
                  sub        s3, a2, s1
                  divu       s1, t1, s3
                  mulh       s1, t2, s3
                  div        t1, s3, s1
                  mulhu      t1, a2, s7
                  mulhu      t1, tp, s3
                  mulh       s3, s3, t5
                  rem        ra, ra, a2
                  mulhu      ra, a2, s6
                  mulhsu     t1, s3, t5
                  sub        s3, s3, a2
                  auipc      t2, 162479
                  mulh       ra, s1, a2
                  lui        t5, 170192
                  lui        tp, 946470
                  mul        s1, ra, s6
                  mul        a2, s3, a2
                  add        s3, t2, t5 #end riscv_int_numeric_corner_stream_18
                  c.li       tp, -1
                  mulhu      tp, s3, t1
                  or         a2, s7, a3
                  ori        s1, sp, -198
                  mul        sp, t3, s6
                  xori       s0, s1, 848
                  div        s3, t3, s9
                  or         s4, s3, s6
                  sltu       t3, a4, s2
                  c.slli     a4, 14
                  sub        ra, a1, s9
                  lui        a3, 355928
                  lui        zero, 635449
                  sub        s0, t0, s5
                  c.nop
                  divu       a6, s7, a3
                  mulhsu     s1, s4, tp
                  remu       ra, s4, zero
                  nop
                  c.mv       t6, t5
                  srli       s5, s5, 31
                  xor        a0, t3, a5
                  c.or       s0, a4
                  or         t6, t0, ra
                  srli       a6, t3, 10
                  c.andi     a3, -1
                  c.sub      a3, s1
                  add        s1, a3, s6
                  c.and      s0, a3
                  c.lui      s9, 28
                  c.add      s6, s6
                  c.xor      a5, s0
                  c.and      a0, a0
                  c.srli     s1, 23
                  c.li       a4, 18
                  sra        a4, zero, s8
                  c.slli     s10, 10
                  sll        s1, a5, zero
                  div        s7, a5, s10
                  mul        s6, s2, a7
                  and        t2, s1, s7
                  rem        sp, t3, s9
                  mulh       a2, a7, a6
                  xori       s7, t3, -42
                  or         a5, sp, gp
                  srli       a0, t0, 19
                  c.li       s8, -1
                  addi       t1, a0, 586
                  c.or       s1, a4
                  c.and      s0, s1
                  rem        s11, s1, s7
                  c.andi     a5, -1
                  c.addi16sp sp, 80
                  ori        s0, s4, 659
                  c.andi     a2, -1
                  slti       s3, a5, -447
                  xor        s9, s6, a3
                  mul        s11, a3, s3
                  xor        sp, t5, a0
                  remu       s9, a3, s5
                  c.addi16sp sp, -16
                  c.add      a4, s5
                  c.nop
                  c.nop
                  sltiu      s5, t0, -988
                  sub        t6, ra, a1
                  sll        a4, t4, a6
                  c.sub      a0, a0
                  mul        s1, t1, a4
                  mul        s11, t1, a7
                  remu       ra, a6, s11
                  xor        a3, sp, t6
                  c.srai     a2, 13
                  ori        s11, t3, 353
                  auipc      sp, 320585
                  c.or       s0, a2
                  sub        ra, s1, s0
                  srl        zero, a7, s3
                  slt        t3, t1, t4
                  srai       sp, zero, 2
                  c.li       a5, -1
                  c.andi     a4, -1
                  c.li       s3, 25
                  c.li       t3, -1
                  sltu       tp, s6, t3
                  sltiu      s11, t4, 64
                  mulhu      ra, t6, a0
                  c.xor      a3, a2
                  c.srli     a2, 27
                  c.and      a3, a3
                  c.srli     a1, 15
                  sub        a4, s11, t3
                  mulhu      a4, ra, s6
                  mulhsu     s6, zero, s2
                  sltu       t6, s0, t6
                  c.and      a2, a4
                  srli       s7, t4, 21
                  srai       sp, s10, 19
                  c.srai     s1, 13
                  slt        t1, t5, s0
                  mulh       s8, a3, tp
                  sra        t0, t0, sp
                  c.srai     a3, 19
                  c.or       s0, a2
                  andi       tp, a3, -923
                  srl        s6, a7, t1
                  sra        s9, t2, s7
                  divu       a1, a5, s7
                  c.nop
                  srai       t5, t0, 4
                  c.and      a4, a3
                  c.li       s10, 30
                  c.lui      a5, 26
                  mulhsu     a3, s1, a7
                  add        s4, t5, a0
                  div        t2, s5, t0
                  c.nop
                  slti       s10, a6, -228
                  slli       t0, t3, 20
                  add        t2, s1, a5
                  c.xor      a1, a3
                  c.addi     a0, 28
                  c.xor      a0, s0
                  addi       zero, a5, 468
                  sub        ra, gp, s6
                  c.slli     s9, 3
                  rem        t2, gp, tp
                  srai       s8, s7, 0
                  addi       s10, a2, -51
                  nop
                  mulhu      a0, t0, s4
                  ori        s4, s2, -348
                  c.li       s5, -1
                  c.xor      a4, a3
                  andi       tp, s2, 826
                  c.slli     ra, 5
                  c.srai     a4, 8
                  div        sp, t0, t2
                  srl        s0, a0, t5
                  c.or       a2, a3
                  andi       s11, t3, 58
                  add        a5, t4, s7
                  srl        sp, a2, s7
                  c.slli     a6, 14
                  sltiu      t0, zero, 889
                  nop
                  srl        sp, s2, s0
                  c.or       a2, a4
                  c.or       a0, a3
                  slti       s9, s6, 780
                  c.andi     a1, -1
                  c.addi4spn a1, sp, 800
                  add        s5, s10, a5
                  slt        tp, a4, sp
                  or         t1, s2, zero
                  andi       a4, a5, 94
                  c.or       a3, s1
                  nop
                  ori        s3, a5, -678
                  rem        s5, t1, s7
                  divu       t5, s5, a0
                  or         a5, s3, s10
                  srl        tp, zero, s8
                  c.slli     s9, 19
                  slt        s3, sp, t5
                  c.mv       s10, a0
                  sub        s9, a6, s11
                  c.and      a1, a3
                  c.add      t2, s10
                  mul        s5, s8, s3
                  c.and      s0, a2
                  divu       a6, s4, a0
                  slti       s8, s1, -103
                  or         s7, zero, s10
                  slli       a3, a6, 9
                  c.srli     a2, 17
                  mulh       gp, s2, t5
                  c.slli     t1, 19
                  auipc      a3, 186368
                  srl        s1, s5, s9
                  rem        gp, t1, a2
                  sltu       a4, a6, t3
                  xor        a2, s6, s2
                  xori       s7, s0, 483
                  c.addi16sp sp, -16
                  c.nop
                  c.addi16sp sp, -16
                  c.andi     a0, -1
                  remu       s4, s2, s4
                  xori       a6, s9, 628
                  sra        sp, t2, a7
                  lui        s10, 78512
                  lui        a1, 766682
                  c.or       s1, a3
                  mulh       t2, t4, s4
                  mulh       s8, a3, ra
                  div        a3, tp, s10
                  div        t6, s3, t0
                  c.addi16sp sp, 368
                  srai       s8, s10, 31
                  addi       a5, s9, 759
                  c.slli     s8, 20
                  srai       t2, a0, 22
                  srai       tp, s3, 0
                  c.addi4spn a0, sp, 464
                  remu       a4, a1, zero
                  c.and      a1, a5
                  mulhsu     a1, t3, s7
                  sub        t1, s0, s4
                  sub        s1, tp, a1
                  c.addi16sp sp, -16
                  sltiu      s6, a6, 945
                  c.slli     ra, 20
                  c.or       a0, a2
                  c.addi     t3, -1
                  andi       s5, a7, 850
                  c.add      tp, a0
                  sltiu      a0, a2, -296
                  c.mv       s0, s9
                  mulhu      s6, ra, s10
                  sub        t3, t2, s5
                  sll        s9, a5, s1
                  andi       t2, t0, -84
                  srl        a6, s1, s1
                  c.xor      s1, a4
                  xor        a6, s2, s1
                  sltu       t6, t4, t6
                  srai       a1, s0, 9
                  remu       a5, a2, s10
                  and        a2, zero, t1
                  c.srli     s1, 22
                  mulhu      t5, s3, t2
                  ori        zero, a2, -487
                  srl        s6, a7, sp
                  or         a1, t1, t2
                  rem        sp, t3, s4
                  remu       s9, sp, gp
                  slti       t3, s2, 431
                  ori        ra, s11, -985
                  c.addi16sp sp, 224
                  sltiu      t6, s0, -298
                  xori       t6, a3, 514
                  c.or       s0, a1
                  sra        s10, s7, s9
                  div        ra, a2, t3
                  sra        s0, sp, s7
                  remu       ra, a3, a4
                  add        s8, s6, s0
                  c.slli     s6, 7
                  ori        t2, t4, -771
                  sll        t0, a1, s7
                  srai       s6, s10, 7
                  c.srli     a4, 20
                  c.and      a5, a3
                  rem        s4, t0, t2
                  xori       s8, ra, -956
                  c.addi4spn s1, sp, 544
                  mulhu      sp, gp, a6
                  c.addi16sp sp, -16
                  or         t5, t0, t6
                  rem        s4, a1, s2
                  auipc      a6, 800379
                  add        t1, s11, ra
                  div        a0, t2, gp
                  c.mv       a1, sp
                  slti       sp, s10, -987
                  c.srai     a3, 31
                  c.srai     a3, 6
                  c.lui      a3, 13
                  div        s10, t4, a6
                  addi       s5, a7, 422
                  c.slli     s5, 7
                  sub        t3, t1, sp
                  lui        tp, 618494
                  c.addi16sp sp, 224
                  slli       s7, a4, 10
                  mulhu      s7, s11, t5
                  sltu       a4, s11, s0
                  and        s4, s3, a2
                  c.mv       a0, s8
                  c.addi     ra, -1
                  andi       s1, s7, -561
                  and        s1, a0, t4
                  srl        sp, a0, a5
                  c.mv       t2, t1
                  mulh       a6, a6, a5
                  c.and      a3, a3
                  mulh       s0, zero, a2
                  sltu       a1, a0, zero
                  div        s1, s10, s3
                  div        s1, ra, s6
                  c.or       a0, s1
                  mulhu      t3, ra, t2
                  or         a3, a1, a0
                  srai       a3, a6, 0
                  div        t1, s9, s2
                  auipc      s11, 664443
                  add        s3, s1, s1
                  c.and      a2, a3
                  mul        s0, s5, a6
                  mul        s10, t0, t4
                  sll        a4, tp, s9
                  c.and      s0, a5
                  mulhsu     sp, s7, t2
                  sll        a5, s6, s2
                  mulh       s4, t1, t0
                  c.xor      a1, a0
                  or         a6, a0, s1
                  slli       gp, a3, 8
                  rem        a6, sp, t3
                  rem        s4, s0, t1
                  sltu       t3, tp, t2
                  c.or       a3, s0
                  c.addi     ra, 15
                  divu       s5, s3, s4
                  c.mv       a2, a1
                  c.slli     t6, 5
                  div        a1, s4, a7
                  mulhsu     s6, a5, a2
                  srl        t2, a2, a6
                  c.and      a1, s1
                  sub        a3, s5, s2
                  c.mv       t3, t5
                  mul        a2, s11, a7
                  sra        t0, a5, a7
                  mulhu      t6, t5, t0
                  auipc      t3, 430878
                  mulh       s8, t6, t1
                  c.addi     s6, 16
                  c.addi     s11, 2
                  c.addi     s1, 1
                  sltu       ra, a1, ra
                  slt        sp, s11, s8
                  ori        s0, a2, -185
                  slt        s8, a1, s10
                  sra        s4, t5, a0
                  xori       a0, t4, -169
                  rem        s3, s2, a5
                  c.nop
                  mulh       a4, s8, s10
                  slt        t3, t6, a3
                  mulhsu     s8, a5, zero
                  srl        ra, a7, t1
                  lui        s6, 514905
                  sra        s4, s6, s5
                  sub        tp, a2, s0
                  mulhsu     s9, a6, a1
                  c.addi16sp sp, -16
                  c.or       a5, s0
                  or         s8, s5, s2
                  slli       a2, a3, 15
                  xor        s5, t0, s3
                  c.addi16sp sp, 448
                  c.srli     s1, 20
                  slli       a2, a6, 22
                  sltiu      t5, a3, 113
                  c.slli     a1, 19
                  ori        s5, t3, 956
                  mulhsu     s8, t5, s4
                  slli       a6, t3, 6
                  mulh       s8, t0, t1
                  and        t3, s1, s7
                  nop
                  c.andi     a0, -1
                  rem        sp, s7, a2
                  sltiu      zero, s7, 88
                  mulhu      a2, s10, zero
                  srl        s9, a4, t5
                  divu       s9, t0, tp
                  c.addi16sp sp, 288
                  andi       t2, zero, -703
                  mulhu      t1, a4, s1
                  xori       tp, s2, -377
                  lui        sp, 630328
                  srl        s8, s0, a3
                  slti       ra, s8, 693
                  c.and      a0, a4
                  srli       ra, s3, 25
                  xor        a5, t4, t5
                  divu       s5, a6, a6
                  c.sub      a4, a5
                  sltiu      s3, s5, 122
                  c.add      s8, t1
                  c.and      a1, a2
                  sra        tp, t2, a6
                  sltiu      s5, a3, -410
                  c.srli     s0, 13
                  addi       a0, a3, -903
                  c.or       s1, a4
                  c.srli     a4, 15
                  or         tp, s6, a4
                  c.xor      s1, s0
                  lui        gp, 171451
                  slt        zero, s5, tp
                  add        s3, s2, s8
                  mul        a1, s6, a0
                  c.addi16sp sp, 464
                  sll        t6, a6, tp
                  sltiu      t6, s1, -232
                  andi       t5, a1, 579
                  addi       t1, s5, 647
                  remu       t2, t1, t1
                  c.addi     s4, 8
                  sub        s8, a6, s4
                  li         s8, 0x0 #start riscv_int_numeric_corner_stream_9
                  li         s5, 0x0
                  li         a6, 0xffffffff
                  li         t0, 0xffffffff
                  li         sp, 0xffffffff
                  li         a2, 0x80000000
                  li         s0, 0x80000000
                  li         t1, 0x0
                  li         s1, 0x9df76eb5
                  li         gp, 0x80000000
                  remu       s1, s8, s8
                  nop
                  mulhu      t1, gp, s8
                  mulhsu     a2, a6, s0
                  div        s8, s1, gp
                  mulhu      a6, t1, sp
                  div        s5, a2, s5
                  rem        sp, s8, a6
                  mul        s8, sp, s8
                  auipc      a6, 790860
                  lui        s8, 381176
                  addi       sp, s8, -28
                  sub        t1, t0, s1
                  mulh       sp, sp, sp
                  mulhu      s1, a6, gp
                  sub        t1, t1, t0
                  mulhsu     s8, a6, a6
                  mulh       gp, a6, s1
                  nop
                  remu       gp, t1, s1
                  add        s1, a6, t0
                  rem        t0, s8, a2
                  auipc      s8, 405025 #end riscv_int_numeric_corner_stream_9
                  mulhu      gp, s6, a1
                  addi       a2, t0, -902
                  c.add      a0, s0
                  remu       t6, s8, t6
                  c.sub      a4, s0
                  c.addi4spn a4, sp, 640
                  remu       a1, zero, s4
                  c.mv       t0, t1
                  sltu       a2, s9, s9
                  sll        a1, s8, t6
                  slt        s4, a5, a7
                  c.xor      a0, a2
                  mulh       t6, a6, s4
                  mulh       a1, s0, tp
                  mul        gp, a5, t5
                  c.li       s8, -1
                  sub        t5, t1, a7
                  or         s10, t3, a0
                  c.addi4spn a0, sp, 400
                  c.slli     a6, 21
                  mulh       a1, a7, t1
                  c.lui      s10, 9
                  c.srai     a3, 5
                  ori        s7, t1, -998
                  c.andi     a1, -1
                  c.slli     tp, 17
                  sll        t0, s11, t4
                  add        s7, s9, a1
                  and        s8, s11, a5
                  andi       s4, a0, 544
                  c.slli     t6, 24
                  auipc      s3, 668039
                  sltu       ra, a6, s2
                  remu       s3, zero, ra
                  ori        s5, zero, 585
                  sll        s3, t4, s1
                  divu       a4, s3, a6
                  c.srai     s0, 8
                  c.srai     s1, 28
                  auipc      a6, 588551
                  mulhu      a5, a0, s6
                  c.srli     a1, 30
                  auipc      t3, 1014014
                  c.nop
                  c.or       a2, a1
                  and        gp, a2, t2
                  xori       a4, s10, -447
                  c.xor      a5, a1
                  auipc      ra, 257227
                  c.addi16sp sp, -16
                  nop
                  sltu       tp, s6, s6
                  c.andi     s1, 29
                  srl        a2, t1, gp
                  remu       s11, t1, zero
                  sltu       a4, s0, a0
                  divu       t5, tp, t1
                  sra        a2, s11, s0
                  slli       t0, t0, 11
                  c.lui      s11, 23
                  c.sub      a1, a5
                  c.nop
                  c.nop
                  sra        a6, ra, a2
                  c.srai     a1, 1
                  ori        s7, gp, -873
                  slti       t0, t3, 941
                  c.addi     s5, -1
                  sub        a4, s11, a5
                  add        tp, s5, s5
                  lui        s3, 223262
                  sll        gp, s10, s3
                  slt        s11, s6, gp
                  c.andi     a2, 29
                  c.addi16sp sp, 240
                  c.slli     a2, 23
                  srli       s8, sp, 19
                  rem        a4, s3, zero
                  srli       s0, tp, 8
                  slt        zero, a0, s1
                  addi       s6, a1, -980
                  c.srli     s1, 19
                  andi       a5, s1, -677
                  srli       s5, t3, 23
                  divu       s8, t3, s4
                  c.li       s3, 19
                  c.addi4spn s0, sp, 32
                  c.andi     s1, 29
                  div        a2, ra, t0
                  rem        a6, a3, s2
                  andi       gp, a2, -10
                  div        t3, t2, s10
                  c.and      s0, s0
                  nop
                  ori        ra, tp, -269
                  c.lui      gp, 13
                  mul        a1, s2, t2
                  remu       s3, t0, a6
                  c.nop
                  c.addi4spn s0, sp, 912
                  or         s5, a7, a2
                  and        s1, a2, s1
                  ori        a0, s9, 202
                  or         a2, s4, sp
                  c.li       s0, 1
                  c.mv       t1, t5
                  c.or       a4, a4
                  slt        t6, s10, s9
                  c.and      a5, a3
                  add        s9, tp, a4
                  c.and      a4, a3
                  div        s7, t3, gp
                  c.mv       t6, ra
                  c.and      s1, a2
                  c.srli     a2, 20
                  or         t1, a3, s2
                  c.nop
                  c.xor      a0, a2
                  add        a3, a5, a6
                  ori        s10, a6, 551
                  c.addi4spn a4, sp, 800
                  c.addi     s4, -1
                  slli       s7, s1, 27
                  lui        t6, 89483
                  c.addi16sp sp, 496
                  rem        s9, s11, t2
                  xor        s3, t6, a5
                  srl        tp, s10, tp
                  xori       a4, t2, -82
                  slli       s5, a2, 14
                  c.slli     t0, 20
                  mulhsu     a4, s2, s3
                  mul        sp, t3, a0
                  c.addi     s6, -1
                  c.mv       a6, a2
                  xori       ra, a7, 774
                  xor        zero, s5, s11
                  andi       s4, s10, 4
                  andi       ra, a0, 153
                  sub        t6, a3, ra
                  mul        s4, s6, t2
                  c.and      a3, s0
                  c.add      a3, s2
                  remu       gp, ra, t4
                  remu       zero, t4, s5
                  slt        s1, gp, s5
                  remu       t1, s8, a5
                  c.addi     ra, -1
                  c.xor      s0, a2
                  c.sub      a3, s1
                  remu       s3, s6, a0
                  slti       s7, a4, -706
                  lui        t1, 981851
                  div        t6, s2, a6
                  sub        s8, t3, s11
                  sra        t5, sp, tp
                  div        s0, ra, a4
                  c.add      a3, s5
                  slli       t5, t1, 16
                  andi       s11, s0, -938
                  auipc      a3, 669530
                  mulh       t5, gp, t4
                  mul        t0, s6, s3
                  add        s4, s0, t3
                  sra        s1, tp, zero
                  c.and      a0, s1
                  c.addi16sp sp, 464
                  c.and      s0, a2
                  slli       t6, t0, 20
                  c.srli     a4, 1
                  c.addi4spn s1, sp, 944
                  add        s6, a1, s10
                  slti       gp, a3, -1002
                  xor        s9, a1, s9
                  mulh       s5, sp, s6
                  auipc      s1, 597111
                  c.addi16sp sp, 256
                  addi       s4, s0, -839
                  c.sub      s0, a3
                  sub        a1, s11, a0
                  slt        ra, t6, sp
                  c.srai     a2, 11
                  xori       t3, t4, -230
                  mulh       sp, s1, s6
                  xor        t6, s6, t5
                  sltu       s1, s2, a3
                  and        t3, s7, s2
                  sra        sp, s4, t1
                  c.andi     s1, 10
                  addi       a4, s0, -219
                  mulhsu     s3, t1, a2
                  c.addi4spn a3, sp, 656
                  c.li       s7, -1
                  addi       zero, a2, -460
                  and        t3, s9, t2
                  srai       t5, ra, 10
                  slli       t1, s4, 21
                  c.slli     s0, 31
                  c.and      a2, s1
                  add        a4, a7, s1
                  mulhsu     s0, s9, t5
                  c.addi4spn a5, sp, 656
                  add        sp, s2, gp
                  xori       a1, t3, -143
                  slli       t6, gp, 19
                  sll        t0, t1, a7
                  c.andi     s1, 0
                  div        s10, ra, s9
                  remu       s3, t2, t0
                  mulhu      a1, s3, s2
                  srai       a5, s1, 21
                  xor        s9, s6, a2
                  or         s8, t3, t2
                  c.add      a0, s2
                  c.slli     a4, 1
                  or         a1, s3, s2
                  c.slli     s7, 27
                  xor        ra, s11, ra
                  c.li       s5, 1
                  c.or       s0, a2
                  srl        gp, sp, a1
                  auipc      a3, 307031
                  c.sub      a5, s0
                  slli       t5, t2, 21
                  c.srli     a4, 24
                  addi       s3, t5, 880
                  srli       a2, s6, 12
                  mulhsu     a4, tp, t5
                  c.nop
                  mul        s10, s10, s6
                  xor        s5, a5, sp
                  mulhsu     a4, s9, a4
                  xor        a5, s1, t4
                  sub        a6, s7, a7
                  slti       s6, tp, 299
                  c.srai     a2, 6
                  c.nop
                  xori       t0, ra, 944
                  c.nop
                  c.lui      t1, 2
                  c.addi     t5, -1
                  c.andi     s0, 17
                  srl        a1, t0, s1
                  c.addi4spn s0, sp, 464
                  c.and      a2, s0
                  sltiu      ra, sp, 652
                  sltiu      a5, ra, -156
                  c.add      a1, s10
                  c.slli     a0, 22
                  sra        t5, a0, zero
                  addi       s4, s3, 579
                  c.xor      a2, a4
                  c.srli     a4, 20
                  divu       t3, ra, t3
                  c.srli     a5, 6
                  c.nop
                  c.srli     s1, 30
                  c.sub      s0, s0
                  c.slli     t1, 6
                  c.lui      t5, 5
                  c.addi     s1, 13
                  c.srli     s0, 16
                  sll        a4, t2, t0
                  c.addi16sp sp, 96
                  or         s8, tp, a4
                  ori        s0, s2, -262
                  srai       t1, s2, 17
                  slt        t5, s7, a2
                  xor        a3, t4, a5
                  mulhsu     a6, t3, a2
                  c.slli     t3, 20
                  srli       a1, a1, 18
                  andi       t1, a0, -421
                  c.mv       a1, s3
                  or         t2, t3, s8
                  xor        s1, a0, s7
                  c.addi     tp, 17
                  c.sub      s1, a4
                  xori       s4, ra, -587
                  auipc      s6, 857233
                  sub        a5, s4, s11
                  sra        t3, s3, s4
                  mulhu      s8, s9, gp
                  addi       ra, a0, 729
                  c.nop
                  div        t0, t2, s2
                  c.srli     s0, 22
                  c.add      t2, sp
                  c.addi     s0, -1
                  mulhsu     t6, a0, sp
                  c.srli     a0, 31
                  c.or       a0, a2
                  xori       s8, t5, -293
                  srai       zero, ra, 10
                  rem        s0, a0, s4
                  slt        s3, a7, ra
                  or         s4, a1, zero
                  xor        zero, a1, t3
                  slli       a5, t2, 11
                  c.slli     tp, 13
                  c.or       a3, a3
                  remu       t6, zero, gp
                  divu       s4, s5, tp
                  xor        s8, s7, s0
                  slt        s8, a6, s10
                  xor        ra, s11, t6
                  sltiu      a3, s3, 174
                  c.addi     a1, 29
                  xori       a0, a6, 475
                  sll        s0, a5, a6
                  srli       a4, a2, 31
                  div        s6, s6, a0
                  andi       s9, s2, 362
                  c.sub      a4, a4
                  lui        a0, 144844
                  sltu       a4, tp, t3
                  c.slli     t6, 4
                  rem        s6, t6, s8
                  c.lui      tp, 1
                  c.xor      a1, a4
                  slt        t2, s1, s7
                  add        s5, s7, s6
                  c.lui      s8, 24
                  sll        t1, gp, t1
                  srl        s4, a2, a7
                  mul        gp, s5, s11
                  sub        t0, ra, a3
                  div        s3, s8, a3
                  sltiu      s4, s5, 987
                  sra        a6, gp, t4
                  c.and      a2, s0
                  c.sub      s1, a3
                  mul        ra, a5, a4
                  auipc      s11, 68481
                  add        a4, s1, a1
                  c.sub      a0, s0
                  andi       t3, t4, 318
                  c.andi     a4, -1
                  srl        a5, a6, gp
                  c.li       a4, -1
                  addi       sp, a7, -797
                  div        a5, t3, s4
                  c.srai     s0, 29
                  slli       tp, s10, 13
                  c.addi     t5, -1
                  c.slli     t1, 8
                  c.add      s3, t0
                  xor        t5, s4, a5
                  c.or       a1, s1
                  c.mv       t3, sp
                  lui        tp, 850199
                  slt        t0, s0, tp
                  c.and      a5, a0
                  c.xor      s0, a3
                  sltu       t0, s8, t4
                  and        a5, a0, s6
                  mulhsu     s6, s9, t6
                  sltiu      s4, s5, 193
                  xori       a0, t5, 157
                  c.addi4spn s0, sp, 416
                  sll        s4, zero, s10
                  auipc      a2, 924677
                  c.lui      s8, 28
                  c.andi     s0, -1
                  addi       t2, a1, 14
                  c.addi     t0, -1
                  add        s11, s5, s6
                  srl        tp, s8, s7
                  mulhsu     t1, s1, s0
                  auipc      a6, 707321
                  c.addi4spn s1, sp, 80
                  mulh       a1, zero, zero
                  c.mv       s5, s11
                  c.addi4spn a0, sp, 528
                  srl        a6, gp, t0
                  divu       s11, sp, sp
                  div        a2, ra, t0
                  c.srli     a2, 9
                  remu       t3, a3, a6
                  srli       a5, s6, 15
                  ori        a5, a5, 421
                  andi       a6, ra, -346
                  div        s7, a6, s3
                  mulhsu     s9, tp, a6
                  c.addi4spn a1, sp, 192
                  mulhsu     sp, t1, gp
                  rem        a1, s0, t5
                  remu       t0, s5, a5
                  slt        a5, ra, s8
                  c.add      t0, a2
                  c.sub      a2, s0
                  c.lui      ra, 19
                  c.andi     a0, -1
                  nop
                  xori       t0, a7, -222
                  c.slli     tp, 6
                  divu       s3, a1, s1
                  sll        a5, a0, t4
                  ori        t2, s10, -473
                  rem        sp, s5, gp
                  slti       t3, s9, 327
                  c.srli     a5, 20
                  addi       s8, a3, -385
                  c.slli     t5, 11
                  c.slli     s7, 18
                  slt        t3, s8, a6
                  c.mv       s10, s8
                  sltiu      s1, a3, -38
                  c.and      a0, a0
                  c.lui      s11, 23
                  lui        s5, 1043402
                  slt        a1, t5, a4
                  div        a3, s1, s4
                  nop
                  mulhu      a6, t3, a5
                  addi       t1, ra, -772
                  xori       t6, s8, -793
                  c.xor      a4, a4
                  sltiu      t6, s3, 162
                  auipc      gp, 10822
                  sltu       a3, a7, t1
                  sltiu      s1, s4, -687
                  c.mv       a3, s6
                  andi       a2, s11, 581
                  c.addi16sp sp, 320
                  mul        t6, t1, t6
                  c.li       a6, -1
                  xori       s10, t1, -425
                  c.addi     t2, -1
                  add        a0, s7, s4
                  andi       t2, t1, 233
                  and        s6, ra, a6
                  auipc      s7, 551827
                  mulhu      s6, a3, a3
                  c.srli     a4, 3
                  srai       tp, t5, 28
                  c.and      a4, a5
                  c.srli     a5, 13
                  addi       t0, t1, -721
                  remu       a4, sp, zero
                  lui        a5, 891653
                  mulh       gp, t3, a2
                  sltu       t0, a4, zero
                  c.addi     s0, -1
                  rem        t5, a2, a7
                  c.nop
                  c.srai     s0, 18
                  remu       t6, s9, zero
                  lui        tp, 551692
                  srl        s6, s1, a2
                  srl        t2, s1, s1
                  c.and      a2, a4
                  mulh       a0, a4, a2
                  srai       s11, sp, 30
                  c.slli     s7, 8
                  c.xor      a1, a2
                  divu       t5, tp, a2
                  sltu       t2, a5, sp
                  sub        t0, s0, a7
                  auipc      tp, 315114
                  c.andi     a0, 15
                  sub        s3, t2, a5
                  c.srli     a0, 22
                  c.or       a5, a3
                  or         s9, s5, ra
                  xori       t3, t3, -841
                  c.add      s1, a3
                  xori       t3, tp, -770
                  c.addi16sp sp, -16
                  c.srai     s1, 21
                  auipc      s10, 138559
                  and        a4, s5, ra
                  mul        t6, s5, s10
                  slli       t5, a0, 3
                  c.xor      a3, a3
                  mulhu      s1, t4, t6
                  srai       a4, s0, 13
                  c.xor      a2, a0
                  mul        a2, t1, t1
                  xor        s8, ra, s1
                  divu       t2, a1, s3
                  c.addi16sp sp, -16
                  mul        s11, s8, t2
                  c.srli     a5, 16
                  ori        a2, a2, -939
                  sltiu      s8, tp, 274
                  mulh       s7, s11, a4
                  c.addi4spn a1, sp, 624
                  sub        ra, s7, t4
                  andi       gp, s11, 395
                  ori        a6, s7, -771
                  nop
                  divu       t0, s3, s7
                  srl        s5, t1, a3
                  remu       a6, s3, t2
                  auipc      a1, 100891
                  li         sp, 0xffffffff #start riscv_int_numeric_corner_stream_39
                  li         s8, 0xffffffff
                  li         s5, 0x0
                  li         s10, 0x500d7c06
                  li         a1, 0xffffffff
                  li         t6, 0xffffffff
                  li         a4, 0x80000000
                  li         s9, 0x80000000
                  li         t5, 0x0
                  li         a0, 0x80000000
                  sub        s8, sp, a0
                  div        t5, t6, t6
                  divu       a0, a0, t5
                  mul        s8, s10, t5
                  remu       a4, s8, s8
                  mulhu      s9, s10, s10
                  mulh       s8, s8, s5
                  lui        a0, 202172
                  addi       a0, a4, 521
                  auipc      s10, 877511
                  sub        s10, s10, a4
                  lui        a0, 40805
                  addi       a4, a0, -734
                  rem        a0, s10, a1
                  mul        s5, a0, a1
                  auipc      s9, 771077
                  rem        a1, s10, a0
                  mul        a4, a4, t6
                  div        s9, s5, a1
                  mulh       s5, s9, a4
                  mulh       t5, a1, a0
                  div        s10, s10, t6 #end riscv_int_numeric_corner_stream_39
                  sltu       t5, s5, s11
                  divu       t1, s4, sp
                  c.srai     a3, 24
                  c.mv       s5, ra
                  andi       s4, ra, -347
                  c.or       a3, s0
                  c.lui      a0, 29
                  mulhsu     a1, s4, t4
                  srai       a6, s9, 23
                  slti       a6, a6, -138
                  c.addi     t1, -1
                  slli       s3, s2, 16
                  c.srli     a1, 21
                  c.nop
                  div        tp, s4, a5
                  c.addi4spn a3, sp, 784
                  c.lui      a0, 10
                  c.addi16sp sp, -16
                  c.xor      s0, s1
                  mul        gp, tp, a0
                  remu       ra, tp, zero
                  mulhu      t2, s1, s8
                  sll        s8, a4, a7
                  srai       s10, s8, 24
                  ori        a3, s10, -446
                  or         sp, s0, t6
                  c.addi4spn a2, sp, 592
                  add        a1, s9, ra
                  lui        s11, 78823
                  nop
                  sra        t6, s3, t2
                  c.srli     s1, 22
                  c.andi     a1, -1
                  ori        s5, s4, 671
                  c.add      s5, s6
                  sra        s4, s7, tp
                  c.add      t6, a4
                  slti       s0, a5, -1021
                  sll        s10, tp, s8
                  mulhu      a2, a6, a0
                  c.andi     a0, 25
                  sra        a6, zero, s2
                  c.addi4spn a0, sp, 704
                  c.addi16sp sp, 64
                  rem        s3, tp, s0
                  c.nop
                  c.sub      a5, a1
                  c.andi     a0, 22
                  c.lui      s0, 30
                  c.srli     a0, 2
                  c.addi     s1, -1
                  c.sub      a5, a3
                  and        t5, a2, zero
                  c.or       a3, s0
                  sltiu      ra, s9, -54
                  c.addi16sp sp, -16
                  c.srai     s1, 4
                  sra        s10, a6, t5
                  slt        a2, a3, t2
                  c.slli     a2, 5
                  xori       t5, s2, -367
                  div        s0, s4, s8
                  srl        t3, ra, s0
                  c.mv       s3, t0
                  c.srli     a5, 15
                  remu       t3, a4, sp
                  slt        s0, s0, a2
                  c.srai     a2, 8
                  mulh       s1, t0, a2
                  c.mv       t1, a0
                  lui        t3, 255897
                  c.or       a4, s0
                  sltiu      s0, gp, 663
                  remu       s1, t3, a6
                  sltu       s6, t1, a5
                  srli       sp, t5, 15
                  remu       s3, s5, zero
                  c.srai     s0, 17
                  c.andi     a0, -1
                  xori       s5, s2, 426
                  sra        t5, s4, a6
                  slli       t5, t0, 24
                  srl        a3, t0, a5
                  c.andi     a3, 1
                  c.lui      a1, 22
                  c.sub      s1, s1
                  mulhu      s6, t6, s11
                  slti       a3, a1, 919
                  xori       a1, s3, 752
                  div        s5, t5, s10
                  auipc      s6, 308117
                  c.xor      a2, s1
                  sub        ra, zero, s5
                  c.li       t6, -1
                  addi       ra, sp, 207
                  c.addi4spn a1, sp, 352
                  remu       a4, t3, t3
                  mulh       s5, sp, a4
                  c.sub      a1, a1
                  remu       gp, a6, s2
                  c.mv       ra, s11
                  c.slli     s9, 28
                  auipc      s5, 995535
                  c.addi4spn s0, sp, 464
                  li         t1, 0xffffffff #start riscv_int_numeric_corner_stream_27
                  li         t0, 0x13e01cb
                  li         s5, 0x0
                  li         s10, 0xffffffff
                  li         s8, 0xffffffff
                  li         s1, 0x587f526a
                  li         sp, 0xffffffff
                  li         a0, 0x0
                  li         t3, 0xffffffff
                  li         t2, 0x0
                  addi       t2, t3, 1011
                  mulhsu     a0, a0, s5
                  divu       t2, s5, t1
                  divu       t1, s5, t3
                  mulh       t3, a0, t0
                  addi       s1, t2, -21
                  mulh       sp, t2, sp
                  lui        sp, 516180
                  mulhsu     t0, s1, s5
                  add        s8, t0, s5
                  lui        t3, 478891
                  mulhsu     t0, s8, t1
                  auipc      t0, 950844
                  mul        s10, s10, t2
                  add        sp, s1, s10 #end riscv_int_numeric_corner_stream_27
                  mulh       a2, zero, a4
                  c.lui      s3, 2
                  sltu       a6, s4, s4
                  sll        a1, t2, a6
                  div        a6, a1, t0
                  lui        ra, 751647
                  and        t3, t1, s3
                  andi       t3, t1, 116
                  c.lui      t3, 30
                  ori        t0, sp, -336
                  c.and      a3, a4
                  c.add      a1, s11
                  remu       a2, t1, gp
                  c.mv       a2, t4
                  c.addi     s10, -1
                  xori       a2, t0, 337
                  lui        s7, 916204
                  c.srli     a0, 17
                  c.srli     a0, 2
                  c.or       s1, s1
                  srai       gp, zero, 25
                  c.add      s10, a3
                  c.srai     a2, 27
                  nop
                  c.srai     s0, 27
                  andi       t6, t0, -256
                  c.and      a0, a2
                  c.mv       a2, s8
                  slli       sp, s4, 12
                  mulh       s10, t1, zero
                  c.slli     ra, 12
                  xor        s4, s9, t6
                  c.xor      s0, a3
                  andi       a1, t0, -442
                  lui        a4, 446776
                  c.srli     a5, 28
                  auipc      a1, 808156
                  c.li       s6, 18
                  sltu       sp, sp, s7
                  mulhsu     s10, t3, ra
                  addi       a2, a5, 696
                  c.li       a0, -1
                  c.srai     a4, 26
                  rem        a4, t6, sp
                  c.and      s0, s1
                  c.add      s4, s9
                  addi       a1, s1, 989
                  add        ra, s0, a7
                  sub        a1, t1, s3
                  c.addi4spn a0, sp, 384
                  sub        a3, tp, s7
                  c.addi     t0, -1
                  c.andi     a1, 18
                  div        t0, gp, s9
                  c.srai     a5, 27
                  nop
                  addi       s8, t2, 854
                  xor        a6, a0, s9
                  c.xor      a5, a4
                  c.xor      s1, s0
                  andi       s0, a5, 922
                  c.andi     a2, 10
                  c.andi     a0, 19
                  slti       s0, s0, -42
                  c.and      a4, s0
                  srai       s8, t5, 18
                  c.srli     a3, 13
                  div        t0, t3, s9
                  c.sub      a1, a0
                  and        s10, zero, t0
                  c.addi16sp sp, 240
                  xor        s0, t0, t3
                  slt        t2, s3, s1
                  c.addi4spn a3, sp, 784
                  xor        s11, s0, s10
                  mulh       s5, t5, a1
                  sltu       t6, t0, ra
                  c.srai     a0, 19
                  c.slli     t0, 20
                  xori       a0, s5, -776
                  mulhsu     sp, t2, s1
                  rem        t6, s5, s7
                  srai       ra, t4, 17
                  c.and      a3, a5
                  lui        t3, 727181
                  addi       s3, a6, -563
                  sub        s5, s0, sp
                  c.li       s1, 16
                  c.addi     sp, -1
                  mul        t1, ra, a1
                  sub        s7, s7, a4
                  c.srai     a2, 12
                  c.and      a5, a5
                  slti       t5, s7, 827
                  c.add      s4, a5
                  c.or       a4, a3
                  xor        s9, s5, s8
                  mulh       a6, a4, t6
                  slli       t5, s11, 6
                  c.xor      a4, s1
                  sll        a2, t4, s7
                  add        s1, s1, t4
                  remu       a5, a1, ra
                  and        s9, a7, s10
                  rem        s10, a5, a2
                  mulh       a6, s3, t5
                  mulhu      s0, a2, a2
                  auipc      t6, 194546
                  c.mv       sp, t2
                  mulhu      zero, a0, s5
                  ori        s8, t0, 598
                  c.or       a5, a4
                  c.addi     s3, 23
                  andi       gp, s6, 264
                  c.li       s1, -1
                  and        t5, a0, s5
                  c.addi     t6, 18
                  mul        s7, s1, s7
                  div        a1, t4, t4
                  c.andi     a4, 28
                  c.lui      s3, 13
                  sra        s5, a5, s4
                  ori        t1, s7, -197
                  add        t0, s1, a7
                  lui        t3, 789241
                  or         s1, s8, a4
                  slt        a2, a2, t0
                  mulhu      a6, a4, s2
                  divu       s1, a3, a2
                  lui        t6, 45005
                  and        s4, ra, gp
                  c.srli     a4, 1
                  or         t0, a5, s9
                  slt        a3, s5, t1
                  rem        t5, a5, s6
                  c.slli     s9, 26
                  c.srai     a4, 12
                  c.mv       t2, a5
                  remu       a2, s2, a4
                  xori       a4, a6, -319
                  c.addi4spn s1, sp, 224
                  mulh       s10, s0, zero
                  srli       gp, s5, 26
                  mulhsu     s0, t6, s10
                  c.mv       s5, sp
                  xor        s11, a1, s4
                  c.lui      t6, 2
                  c.andi     s1, 31
                  c.and      s0, a4
                  c.lui      t2, 17
                  srl        a5, t2, a1
                  c.add      s10, s7
                  andi       a1, s6, -1013
                  rem        t2, t1, a6
                  remu       s11, s11, a2
                  ori        tp, a0, 308
                  addi       zero, tp, 183
                  add        sp, t4, a2
                  ori        t0, t5, 341
                  slt        a2, a2, ra
                  c.add      a4, s7
                  sltiu      t6, t4, -685
                  sub        a3, a5, ra
                  xori       a0, t0, 73
                  xor        a4, s10, s4
                  xori       ra, t4, -777
                  slti       sp, s4, -117
                  sub        t6, t2, a7
                  addi       t0, t6, -391
                  c.lui      s1, 28
                  c.slli     s3, 19
                  c.slli     t6, 24
                  slli       a5, ra, 16
                  andi       a1, t2, 125
                  sltiu      zero, t0, -644
                  c.li       s0, -1
                  mulh       t3, a7, s11
                  xor        a3, t1, s2
                  c.andi     a3, -1
                  add        tp, s3, gp
                  c.srli     s0, 24
                  xori       a6, s6, -838
                  c.mv       s5, s6
                  mul        a0, s3, a3
                  slli       s3, t0, 10
                  c.li       s6, -1
                  c.sub      s0, a2
                  andi       zero, t4, 959
                  add        zero, gp, s8
                  sltu       a3, a0, gp
                  ori        a5, gp, -536
                  xor        t2, t5, s3
                  sltiu      s10, tp, -809
                  c.nop
                  c.or       s1, a3
                  xor        a6, t1, s7
                  c.nop
                  srli       ra, s4, 11
                  srl        gp, sp, t0
                  nop
                  c.add      s11, sp
                  sub        s10, s0, zero
                  div        s10, s11, sp
                  xor        s5, zero, t5
                  nop
                  sra        t5, a5, t1
                  c.srai     a2, 12
                  c.addi4spn s0, sp, 448
                  slli       s6, s4, 8
                  c.nop
                  c.sub      s1, a3
                  lui        s9, 78602
                  c.xor      s0, s1
                  srl        a6, s1, tp
                  c.srai     a1, 1
                  c.and      a2, s1
                  addi       s10, sp, 830
                  add        a5, s4, s4
                  c.or       a2, a1
                  mulhsu     a0, s3, ra
                  sub        a6, t1, a5
                  sub        a5, a4, gp
                  rem        s11, t2, s5
                  c.andi     a0, 31
                  c.addi4spn a0, sp, 48
                  auipc      s8, 697214
                  c.xor      a0, a2
                  add        a4, gp, zero
                  srli       t3, t3, 17
                  add        t3, s2, s1
                  c.and      a1, a3
                  sra        s4, tp, a2
                  srl        a0, a5, s6
                  divu       s10, ra, s2
                  c.xor      a3, s0
                  mulh       s7, a1, t6
                  add        t3, a6, s4
                  c.add      s4, ra
                  slli       s3, s0, 14
                  sll        zero, s1, tp
                  andi       s7, s7, -90
                  addi       t3, s3, -379
                  srai       t1, gp, 20
                  div        s1, s4, t2
                  mulhsu     a2, t0, a4
                  sltiu      a0, a7, -812
                  divu       a3, tp, a1
                  c.srli     a1, 1
                  slt        s11, zero, t1
                  addi       t3, t0, 524
                  c.andi     a3, 25
                  mul        gp, s6, t2
                  sra        s1, s6, zero
                  nop
                  auipc      s6, 841745
                  and        a4, t3, t2
                  mulhsu     s9, s0, s4
                  c.slli     s4, 15
                  lui        a4, 382701
                  c.or       a1, s1
                  slli       t1, a1, 21
                  rem        s8, t5, s0
                  srai       tp, s7, 18
                  div        t0, t1, t1
                  slt        a0, s7, s11
                  c.sub      a1, a0
                  slti       s9, gp, -437
                  c.lui      s4, 17
                  c.lui      s8, 21
                  mulhsu     a4, a2, gp
                  c.add      a1, gp
                  c.or       a0, a3
                  div        t1, zero, zero
                  c.and      s0, a3
                  slt        t2, a0, s9
                  c.addi     a6, -1
                  and        s5, s8, s7
                  c.slli     s10, 17
                  srl        s1, s11, s2
                  c.lui      ra, 7
                  c.addi4spn a3, sp, 576
                  slti       s1, s6, 148
                  or         a2, t0, t4
                  c.srai     a2, 28
                  add        s11, a3, a6
                  slti       zero, s9, 745
                  slli       a4, a3, 22
                  addi       t6, s0, 602
                  sub        t3, a5, t5
                  c.andi     s0, -1
                  c.sub      a5, s0
                  srai       s11, gp, 20
                  c.addi16sp sp, 352
                  mulhu      s7, a5, gp
                  srli       t3, gp, 28
                  c.addi16sp sp, -16
                  divu       s8, t4, t2
                  srai       s5, s11, 21
                  xor        t5, s0, s2
                  and        s0, t1, ra
                  c.mv       t0, s7
                  slli       tp, t6, 4
                  slli       s8, a0, 21
                  auipc      s6, 375043
                  c.nop
                  c.xor      a1, s0
                  sltu       zero, s1, t1
                  c.andi     a4, 28
                  slt        s0, a2, sp
                  rem        s5, s1, s8
                  div        t5, s7, a2
                  c.addi     s7, -1
                  sltiu      s0, a7, -384
                  mulhu      a6, a4, t1
                  xor        gp, s9, sp
                  sll        t3, t3, zero
                  srli       s9, s1, 7
                  xori       a5, a0, -452
                  c.addi16sp sp, -16
                  nop
                  ori        s3, a6, -70
                  mul        gp, t4, s11
                  c.lui      s8, 13
                  sltu       t6, s10, t1
                  remu       tp, a1, s0
                  c.add      sp, t6
                  sltu       a2, s5, sp
                  or         t2, gp, t0
                  c.addi4spn a5, sp, 112
                  or         a5, s1, s7
                  mul        zero, s7, a2
                  c.slli     t1, 15
                  c.lui      a4, 17
                  srai       a0, t0, 19
                  c.nop
                  add        zero, t6, s4
                  c.or       s0, a5
                  sll        a3, s9, s11
                  remu       s11, tp, a7
                  mulhsu     a6, t5, t6
                  rem        s6, a7, zero
                  addi       s0, a7, -233
                  c.addi4spn a0, sp, 544
                  sltu       s0, ra, s3
                  srli       ra, a6, 1
                  c.addi16sp sp, -16
                  c.addi16sp sp, 192
                  srl        t5, gp, t1
                  mulhu      a4, s7, a6
                  srai       s8, t0, 10
                  div        a1, t3, t1
                  srli       s4, s7, 24
                  slt        a1, s3, t4
                  rem        s3, s2, a7
                  mulhsu     a4, s6, t4
                  c.lui      s7, 19
                  c.srai     a2, 16
                  c.addi4spn a2, sp, 416
                  c.or       a0, s1
                  slt        a3, a5, s8
                  or         t1, a0, s8
                  c.addi16sp sp, -16
                  add        t3, t2, s10
                  c.addi16sp sp, 128
                  mul        gp, s3, s9
                  ori        a4, t1, 657
                  srai       a5, s10, 4
                  and        zero, s9, s7
                  c.srai     a2, 14
                  add        a5, t5, t1
                  c.li       s7, 0
                  sltu       s6, t5, sp
                  c.mv       t0, a3
                  xori       a5, s1, -860
                  c.srai     s0, 29
                  xor        tp, s0, s8
                  mulhu      a3, s6, a1
                  sra        zero, a1, s8
                  andi       gp, a3, -438
                  slli       s0, a2, 20
                  c.slli     ra, 18
                  sll        t2, tp, t2
                  c.xor      s1, a5
                  sll        s8, ra, s8
                  sltu       s6, t3, s9
                  and        a5, s2, t0
                  slti       s8, s1, -616
                  c.sub      a3, s1
                  c.xor      a4, a4
                  srli       t1, s6, 29
                  divu       a1, s0, sp
                  andi       tp, t0, 705
                  or         s10, a7, t0
                  slt        s0, s7, t5
                  sltu       t2, s5, s9
                  c.lui      s7, 6
                  c.li       s0, -1
                  srai       s5, t6, 6
                  add        gp, s6, s3
                  rem        s7, t1, s8
                  mulh       s11, a7, s10
                  c.or       s1, s0
                  srli       s6, s5, 19
                  add        s5, a5, s9
                  c.addi16sp sp, 32
                  ori        s11, t4, 684
                  sltu       t0, a1, t2
                  mulhu      a1, tp, s5
                  sub        s3, s4, a3
                  mulhu      t5, s6, t0
                  c.addi16sp sp, 480
                  add        tp, a4, t4
                  c.and      a4, s1
                  c.sub      s1, s0
                  c.xor      a5, s0
                  sltiu      a0, t3, 742
                  c.addi     tp, -1
                  ori        a6, a0, -749
                  sltu       s3, gp, t6
                  rem        s5, a1, a7
                  remu       t5, s5, a3
                  slli       s1, t1, 24
                  srl        s5, s2, t0
                  c.li       s3, -1
                  c.mv       a1, a0
                  lui        s0, 697505
                  xori       sp, t0, 882
                  c.add      a6, ra
                  c.lui      s11, 11
                  ori        s7, a7, -566
                  auipc      s1, 475396
                  c.lui      s7, 4
                  sra        ra, s0, a2
                  c.srli     a0, 15
                  c.li       a5, -1
                  remu       a3, a4, tp
                  sra        s0, s8, t6
                  srli       sp, a2, 30
                  add        s6, s1, s10
                  c.slli     gp, 27
                  and        a6, t4, t0
                  c.lui      t0, 9
                  c.srli     a3, 30
                  c.srai     a0, 1
                  c.andi     a2, 24
                  nop
                  c.slli     a4, 7
                  c.xor      a5, a0
                  sra        s7, s3, t0
                  sub        s9, s0, t2
                  srai       s0, s6, 11
                  mul        s0, zero, a0
                  and        sp, s5, s5
                  sltu       gp, s0, s3
                  srai       s4, t4, 2
                  c.addi     s7, -1
                  add        sp, s8, a4
                  nop
                  sub        s6, s3, s1
                  c.or       s0, a1
                  c.add      s6, sp
                  add        s9, s8, s11
                  c.li       t5, 14
                  sub        s9, a7, s9
                  and        s6, a0, s1
                  slt        s10, t4, s9
                  rem        t0, a2, s9
                  ori        t0, s5, 335
                  c.xor      s1, a2
                  srli       a1, ra, 24
                  c.srli     a4, 19
                  sra        t0, a4, s5
                  xor        t2, tp, t5
                  c.addi16sp sp, -16
                  c.slli     gp, 18
                  c.nop
                  slli       a4, s2, 15
                  c.addi     s9, 13
                  mulh       s6, t4, s4
                  or         zero, t5, s6
                  slt        s8, s8, s1
                  mul        gp, t3, s9
                  mul        s10, sp, a1
                  c.srai     a2, 27
                  sub        zero, a2, a6
                  sub        s1, s2, zero
                  add        a3, s7, s9
                  c.mv       a2, tp
                  mulhu      t2, s0, a3
                  sll        s3, t0, s9
                  div        a4, s4, gp
                  c.srli     s0, 19
                  c.mv       t0, t2
                  slti       t5, tp, 681
                  c.add      a0, s3
                  mulhu      sp, zero, zero
                  c.addi16sp sp, 176
                  srl        t1, t5, t2
                  c.xor      s1, a0
                  c.andi     s0, -1
                  sra        a2, t6, s1
                  c.and      a2, a0
                  mulhsu     s11, zero, t3
                  srli       a3, s9, 30
                  c.nop
                  slli       a1, a4, 26
                  add        a1, s9, t1
                  c.addi16sp sp, 464
                  lui        s3, 564636
                  mulh       t0, zero, t2
                  c.mv       s0, s2
                  rem        a3, s2, s8
                  sll        tp, t5, s1
                  divu       ra, s0, a7
                  and        a6, s4, s1
                  c.add      s9, s10
                  c.srli     a4, 19
                  slt        s7, a4, zero
                  div        s0, a5, t0
                  remu       t0, s8, s10
                  rem        s9, s3, zero
                  slli       t6, a6, 1
                  c.addi     a5, 30
                  sll        s10, s2, s1
                  c.slli     s3, 25
                  c.add      gp, a4
                  c.mv       tp, a3
                  c.addi4spn a3, sp, 544
                  addi       a4, s6, 130
                  slli       s6, gp, 11
                  c.sub      a2, s0
                  mul        a5, a3, gp
                  slli       t0, a7, 18
                  c.addi16sp sp, 80
                  c.li       s6, -1
                  div        a3, a3, tp
                  slti       a4, a5, -454
                  addi       s1, t6, -164
                  xori       s0, t4, 64
                  mulhsu     t2, gp, sp
                  sltiu      a1, s6, -717
                  c.nop
                  srai       t2, a5, 0
                  mul        s1, s4, tp
                  auipc      sp, 900148
                  sltiu      tp, a4, 166
                  addi       s9, s5, 987
                  addi       s8, s9, 227
                  nop
                  or         sp, a2, s5
                  sltu       tp, s2, a7
                  c.addi4spn a4, sp, 784
                  c.sub      s0, a0
                  mulhsu     a2, tp, t3
                  or         a4, a0, s3
                  srli       a4, s0, 29
                  xori       t1, s9, 627
                  auipc      a4, 228296
                  div        a5, s9, s11
                  sltu       s11, t0, a0
                  remu       t5, s8, s5
                  c.xor      a4, a1
                  nop
                  c.addi16sp sp, -16
                  mulhsu     zero, gp, s1
                  xori       a5, t4, 723
                  srli       a2, a0, 5
                  c.lui      s10, 17
                  remu       s6, tp, ra
                  remu       s10, s11, s11
                  c.addi4spn a1, sp, 272
                  nop
                  c.addi     a5, 13
                  sra        t3, ra, s10
                  mulh       t1, t5, t4
                  c.nop
                  c.or       a1, s0
                  c.and      a3, a2
                  sll        s8, s6, t1
                  c.srli     a0, 24
                  c.addi4spn a5, sp, 240
                  mulh       a5, s9, zero
                  c.srli     a4, 13
                  c.xor      a0, a4
                  and        s3, a6, t6
                  lui        sp, 1034508
                  sra        gp, a7, s5
                  c.slli     s1, 18
                  mul        s10, a5, s3
                  sra        a4, s3, zero
                  c.sub      s0, a0
                  slti       t5, zero, 805
                  c.sub      a2, s0
                  c.add      a4, a6
                  mulh       ra, a7, s3
                  c.lui      s4, 30
                  and        s11, a2, s1
                  andi       t1, a0, 53
                  c.xor      a3, a2
                  c.lui      a3, 26
                  auipc      a0, 394121
                  c.lui      t5, 13
                  c.addi4spn s0, sp, 992
                  mulhu      a3, s10, a5
                  sltiu      a4, s11, 200
                  slli       a2, s4, 26
                  srai       s1, s1, 22
                  div        gp, a2, s5
                  sub        s6, t2, s2
                  c.slli     s7, 2
                  c.addi16sp sp, 64
                  add        a5, s10, s2
                  addi       t1, a4, -455
                  slti       t5, t3, 702
                  c.xor      a2, s0
                  divu       t6, a2, s9
                  ori        t0, s3, -120
                  addi       a3, t3, -702
                  c.srai     a3, 27
                  mulhu      s8, tp, ra
                  sltu       t3, a0, tp
                  c.li       t3, -1
                  c.mv       gp, sp
                  c.srli     s0, 19
                  and        t0, a4, a4
                  sll        a0, s2, s10
                  or         a2, s11, t6
                  addi       a3, s2, -766
                  c.mv       s1, s10
                  c.or       a5, a1
                  c.or       a5, a3
                  lui        t0, 248644
                  c.nop
                  auipc      ra, 746804
                  lui        a2, 7384
                  mulhsu     t6, s9, s2
                  slli       a2, t0, 1
                  remu       s1, gp, s2
                  div        s0, t5, t3
                  sub        s4, a3, s8
                  remu       a5, s2, s4
                  mulh       s3, s6, t3
                  c.nop
                  mul        a0, t2, s0
                  c.nop
                  c.addi16sp sp, -16
                  and        t6, t5, a3
                  sltiu      tp, a5, 772
                  or         s9, t0, s7
                  srai       t1, t0, 5
                  mulh       s1, zero, gp
                  sub        t6, s6, s10
                  mul        s7, s4, s1
                  c.li       tp, -1
                  c.lui      t0, 10
                  sub        ra, t1, t4
                  slti       s10, a4, 754
                  c.lui      t1, 23
                  c.addi4spn a2, sp, 208
                  sll        s10, a6, a3
                  sltiu      t3, sp, 34
                  sltu       tp, a1, a5
                  c.add      s0, a1
                  sltiu      s4, gp, 74
                  c.srai     a1, 12
                  xor        s6, a7, tp
                  sltiu      a4, s9, 556
                  or         a3, a5, tp
                  auipc      t3, 878277
                  div        s4, s8, t6
                  rem        s4, zero, a7
                  or         s1, tp, t5
                  c.srai     a3, 17
                  xor        a6, t0, s3
                  c.srai     s0, 5
                  andi       s5, t5, -755
                  c.andi     s1, -1
                  srl        s0, ra, t2
                  remu       a4, s4, a1
                  andi       t1, s8, 764
                  lui        a5, 569180
                  c.or       a3, s0
                  c.or       s0, a1
                  add        s11, a2, s9
                  andi       t1, s3, -665
                  and        ra, s5, a1
                  mulhu      a1, t0, a2
                  c.nop
                  c.addi16sp sp, -16
                  mulhu      gp, a3, a5
                  sra        a4, s11, a5
                  mulhu      s5, sp, gp
                  c.lui      t6, 2
                  or         sp, s7, t0
                  c.addi4spn a3, sp, 704
                  sra        t3, s5, t0
                  andi       s7, a1, 111
                  mulhsu     s9, s10, s4
                  ori        t3, t6, 370
                  c.xor      a3, a5
                  c.or       a2, s0
                  div        a2, a5, s9
                  sltiu      s0, a3, -431
                  sra        s1, s4, s3
                  c.xor      a0, a2
                  rem        a6, t4, ra
                  remu       s4, s1, t4
                  andi       gp, a3, 975
                  mulhsu     t0, a2, t1
                  srli       s3, s9, 13
                  srai       a5, t1, 17
                  srai       a5, t4, 20
                  c.and      s0, s0
                  andi       t1, s5, -574
                  c.sub      a4, a1
                  div        a5, a7, a7
                  mulhu      s11, s4, t2
                  c.or       a3, a5
                  c.nop
                  div        zero, s2, gp
                  sra        s3, s4, t4
                  rem        t5, s5, a2
                  slt        a3, a7, a2
                  sub        s11, gp, s1
                  c.srai     a0, 24
                  ori        t6, a5, 516
                  c.addi4spn s0, sp, 944
                  andi       a4, s9, -576
                  auipc      s4, 406306
                  sltiu      tp, s6, -181
                  mulh       s5, a2, s1
                  c.addi16sp sp, 208
                  slli       s0, s11, 20
                  c.andi     s1, 0
                  mulh       s9, gp, s8
                  addi       a2, t6, -760
                  or         s5, s9, a2
                  nop
                  c.or       a2, a2
                  auipc      t6, 376658
                  or         s4, s2, a6
                  ori        a3, tp, 874
                  rem        a6, s10, a6
                  ori        a2, s1, 83
                  c.li       a5, 8
                  mulhu      s10, a0, t6
                  sub        tp, s9, s3
                  c.add      a1, s7
                  lui        s9, 151209
                  slti       s4, a0, 699
                  and        zero, gp, ra
                  mulhsu     a6, a4, a4
                  xori       a2, t1, 334
                  remu       a0, tp, zero
                  c.srai     a5, 8
                  c.li       s8, -1
                  sltu       zero, a2, s11
                  slti       s11, s9, -604
                  c.addi4spn a4, sp, 160
                  c.mv       ra, s11
                  c.srai     a1, 1
                  srl        s5, t4, sp
                  mulhu      sp, a7, s10
                  ori        s0, s2, -512
                  mulhsu     s8, s7, a5
                  or         s6, s6, s6
                  sltu       sp, a1, t3
                  c.and      s1, a4
                  sltu       a2, zero, s11
                  c.and      a3, a2
                  mul        s5, a7, t1
                  slti       t5, sp, -85
                  nop
                  c.slli     t2, 28
                  div        t2, sp, s8
                  divu       s1, t0, s0
                  c.sub      a4, s0
                  div        s8, t2, a1
                  add        s0, t3, a6
                  c.lui      s1, 12
                  or         s6, s0, t0
                  slli       s11, s11, 2
                  sltiu      t5, t1, -487
                  sra        a5, a6, t6
                  c.slli     a2, 8
                  sltiu      s3, t6, -697
                  c.addi16sp sp, 144
                  xor        s5, zero, t5
                  c.slli     a0, 5
                  li         s6, 0xebee576a #start riscv_int_numeric_corner_stream_19
                  li         s8, 0x80000000
                  li         s11, 0xab23dc9f
                  li         s3, 0xffffffff
                  li         t2, 0x676971b0
                  li         s9, 0xe7df8368
                  li         a1, 0x0
                  li         t5, 0x48fd7707
                  li         a5, 0xffffffff
                  li         ra, 0x0
                  div        a1, s3, s8
                  auipc      ra, 208375
                  sub        t5, s9, s8
                  rem        s8, t2, s9
                  mulhsu     t2, s3, ra
                  rem        t5, a1, s8
                  divu       a5, a1, s9
                  lui        a1, 284097
                  auipc      s9, 365216
                  rem        s6, t2, t2
                  div        t2, a5, s6
                  mul        t2, t5, t5
                  mulh       s8, s6, s3
                  divu       s8, a5, s8
                  divu       s11, a1, s3
                  mulhu      t5, s8, s9
                  addi       t2, ra, -629
                  nop #end riscv_int_numeric_corner_stream_19
                  mul        a1, s7, s2
                  srai       a6, a3, 27
                  nop
                  c.xor      a2, a0
                  add        t5, gp, s7
                  sra        s10, a2, s1
                  and        s3, t2, sp
                  c.addi     t2, -1
                  c.srai     a3, 17
                  c.xor      s1, a3
                  c.addi16sp sp, 96
                  c.srai     a4, 22
                  c.addi     t0, -1
                  c.lui      t0, 8
                  addi       a1, a7, -511
                  c.or       a5, a3
                  lui        tp, 531655
                  mulhu      s0, s8, s10
                  c.sub      a1, s0
                  addi       a1, sp, 154
                  srli       zero, a4, 21
                  andi       zero, s8, -635
                  c.mv       t1, s9
                  c.addi16sp sp, 16
                  and        s0, t1, t5
                  sltu       s3, s6, gp
                  srli       a0, gp, 25
                  c.slli     t5, 28
                  slli       ra, a6, 13
                  xor        a4, t0, t1
                  add        s0, s0, s3
                  c.li       s8, 11
                  c.mv       t6, a5
                  remu       a1, sp, a4
                  srai       ra, t2, 23
                  mulhu      t1, t2, s6
                  c.addi16sp sp, 96
                  c.addi16sp sp, -16
                  sll        a0, t0, s2
                  ori        a1, a0, 235
                  c.addi     s3, -1
                  xori       a0, tp, 136
                  rem        s7, s0, tp
                  c.xor      s0, a2
                  sub        a4, a0, a7
                  srl        zero, t4, a6
                  div        t5, t6, t4
                  auipc      s5, 633160
                  mulhsu     s4, s8, ra
                  c.addi16sp sp, -16
                  div        s7, t3, t6
                  mulhsu     t1, s5, a5
                  addi       s5, t6, -63
                  c.mv       t3, s10
                  c.or       a1, a5
                  xori       s1, a4, -757
                  c.xor      a5, s0
                  c.addi     s11, 8
                  c.srai     s0, 23
                  srl        t1, sp, ra
                  c.nop
                  c.srli     a1, 4
                  srl        a6, a2, a3
                  ori        s0, s10, -192
                  addi       s0, sp, -1020
                  c.and      a1, a1
                  c.or       a1, a1
                  c.addi16sp sp, -16
                  c.and      a1, a0
                  c.li       a4, -1
                  c.addi     s6, 10
                  slli       s1, a5, 4
                  sub        s10, s11, a2
                  srai       t2, t5, 31
                  c.addi16sp sp, -16
                  add        a6, s2, s8
                  srli       s3, a6, 6
                  sra        s11, s5, s1
                  mulh       a2, tp, s6
                  or         t3, t1, gp
                  sltu       a2, s6, t1
                  c.or       a3, s1
                  xor        t5, t0, ra
                  ori        s5, s11, 689
                  c.or       a4, s1
                  c.lui      s0, 5
                  auipc      t6, 734339
                  sll        a0, s11, s4
                  mulh       sp, s2, s1
                  sltu       s8, s8, s5
                  mulhu      t3, t1, s4
                  srli       t6, s4, 27
                  c.add      tp, t2
                  or         t6, s6, s3
                  sll        s7, a1, a1
                  slli       a1, s0, 9
                  mulh       zero, t1, a6
                  sll        s3, t3, a5
                  c.sub      a1, a2
                  sltiu      s9, s5, -987
                  sltiu      s9, s5, -827
                  c.sub      a1, a2
                  slti       s3, s1, -739
                  c.srai     s1, 14
                  c.li       s1, -1
                  c.srai     a2, 20
                  c.lui      s8, 6
                  div        s6, t0, t2
                  mul        t2, a6, t4
                  c.lui      s9, 4
                  xor        t2, t4, gp
                  c.andi     a5, -1
                  sll        t5, t2, s5
                  sll        a3, s7, tp
                  sub        ra, s9, a2
                  xori       s0, t5, -1014
                  mulhu      t5, a7, sp
                  sll        zero, s1, a4
                  sub        ra, a7, gp
                  mulhsu     s1, a4, a5
                  mul        a1, t3, t1
                  c.addi4spn a2, sp, 848
                  mul        s0, s3, sp
                  c.andi     s0, 23
                  mulhsu     t2, s4, s0
                  c.li       t1, -1
                  xor        t0, a4, t0
                  c.addi     a2, 23
                  c.or       a2, a3
                  c.sub      a5, a4
                  or         a2, s10, s9
                  c.andi     s1, 1
                  srai       s6, ra, 14
                  srai       t2, a0, 22
                  xor        t1, a6, s8
                  xori       zero, s11, -633
                  c.slli     gp, 26
                  srai       ra, a2, 4
                  srli       s1, t2, 15
                  srai       s7, s2, 18
                  c.addi     s3, 30
                  nop
                  srl        a5, s0, gp
                  add        s8, s10, sp
                  rem        a5, s11, s2
                  c.li       s8, -1
                  div        sp, t0, t4
                  c.addi4spn a5, sp, 336
                  sra        s10, t2, t2
                  auipc      s3, 200560
                  remu       t3, s7, zero
                  slt        s10, s8, s0
                  c.addi4spn s0, sp, 528
                  slt        t6, ra, tp
                  nop
                  c.srai     a3, 18
                  srai       t5, a4, 0
                  sll        a3, a5, a2
                  c.addi4spn a0, sp, 48
                  srl        s4, t3, ra
                  c.addi4spn a5, sp, 464
                  c.andi     a0, 23
                  c.nop
                  sub        s4, s7, s2
                  mulhsu     sp, s4, zero
                  c.or       a0, a0
                  nop
                  c.and      a2, a1
                  xor        tp, s8, s6
                  remu       t0, a4, a4
                  sll        a6, s8, t1
                  c.add      s6, s4
                  xori       t3, s4, 871
                  xori       s9, t1, 464
                  c.addi4spn s1, sp, 336
                  c.xor      a3, a1
                  c.nop
                  c.addi     gp, 21
                  nop
                  srai       s6, s1, 27
                  srai       t3, gp, 1
                  sltiu      s5, s1, -334
                  c.and      a5, a3
                  srli       s7, s9, 19
                  mulhsu     a5, s0, t0
                  slli       s5, a0, 10
                  div        s11, s1, s10
                  mulhsu     t2, t0, a1
                  c.add      a3, a2
                  c.nop
                  mul        a6, t2, a4
                  nop
                  c.add      t3, s0
                  and        a1, s8, s8
                  nop
                  srl        a2, a2, s9
                  c.andi     a3, 3
                  slti       t1, sp, -218
                  c.addi16sp sp, -16
                  or         s1, a7, a3
                  ori        a4, s2, 234
                  slt        t5, s10, sp
                  xori       s3, s2, -541
                  c.addi4spn s0, sp, 208
                  c.add      sp, s9
                  srli       a2, s7, 30
                  slt        ra, a2, s11
                  srli       t3, s2, 6
                  srai       a3, t3, 26
                  slt        tp, a0, sp
                  c.and      s1, a5
                  srai       t2, a0, 7
                  sltiu      a1, tp, -711
                  sltiu      t2, a1, -376
                  div        a5, tp, s3
                  divu       a0, s3, s1
                  c.slli     t5, 11
                  sltu       t0, a5, t6
                  c.addi     s9, 19
                  c.sub      s1, a1
                  c.and      s1, s1
                  rem        sp, sp, s9
                  srl        s8, ra, s9
                  c.addi4spn s0, sp, 224
                  remu       s4, a0, s9
                  mulhsu     s10, t4, a7
                  remu       a0, a6, s1
                  c.or       a5, a0
                  srai       zero, s7, 29
                  xori       t3, tp, 840
                  sub        a2, a1, a7
                  c.srai     a1, 24
                  sra        s8, s0, s11
                  xor        t6, tp, ra
                  c.nop
                  c.addi16sp sp, -16
                  srli       s7, s11, 29
                  add        s9, sp, t4
                  c.slli     t6, 25
                  srli       s11, s5, 5
                  c.lui      a5, 8
                  c.li       s6, 8
                  or         a1, s7, a7
                  c.and      a5, s1
                  mul        a3, s3, s0
                  c.lui      a0, 18
                  xori       a5, s11, 682
                  c.and      a0, a0
                  c.or       s0, s0
                  srl        s0, a0, a6
                  auipc      ra, 1030422
                  xori       gp, a6, -996
                  lui        a5, 874358
                  mul        a2, a0, gp
                  mulh       a0, a5, s8
                  or         a2, t6, zero
                  slt        sp, s0, s10
                  srl        s1, t6, sp
                  andi       a4, s11, 963
                  c.or       a5, a4
                  div        t5, t2, s3
                  c.li       s4, -1
                  slt        tp, s0, t0
                  c.addi     s9, -1
                  and        t1, s10, a7
                  c.and      a0, a1
                  divu       s1, a6, s6
                  c.sub      s1, a1
                  srl        t1, s2, s6
                  c.srli     a3, 24
                  c.li       s6, 24
                  and        s3, s4, ra
                  c.srai     a3, 3
                  andi       s6, t4, -399
                  rem        s8, a3, t3
                  c.andi     a2, -1
                  remu       sp, s8, s5
                  sra        sp, a5, a0
                  srl        s3, t4, s10
                  andi       t0, a3, 101
                  addi       t0, s6, 777
                  c.slli     t2, 19
                  c.xor      s0, a5
                  nop
                  and        t5, tp, sp
                  li         s7, 0x8a0affdd #start riscv_int_numeric_corner_stream_25
                  li         s3, 0x80000000
                  li         sp, 0xa0824e44
                  li         s8, 0xffffffff
                  li         a6, 0xffffffff
                  li         s6, 0xffffffff
                  li         t0, 0x80000000
                  li         s11, 0x0
                  li         s4, 0x80000000
                  li         a2, 0x0
                  nop
                  rem        a2, t0, s4
                  mulh       s3, t0, s4
                  mulhsu     s3, t0, a6
                  remu       t0, s8, t0
                  rem        s3, a2, s3
                  lui        s7, 617867
                  mul        s6, s8, s4
                  mul        s11, s4, s6
                  remu       a6, s4, s6
                  nop
                  sub        a2, sp, s11
                  auipc      s4, 363828
                  divu       t0, s7, s7
                  lui        a6, 259944
                  lui        s3, 125355
                  divu       t0, t0, t0
                  add        s3, s7, s4
                  remu       s7, s7, s3
                  remu       a6, t0, s3
                  mulh       s11, s8, sp
                  auipc      s3, 732484
                  mul        a6, t0, a6
                  mul        s4, s7, s8
                  sub        s8, s8, s6
                  mulh       s8, t0, sp
                  mul        s3, a2, sp #end riscv_int_numeric_corner_stream_25
                  c.andi     a5, -1
                  div        a1, s5, a1
                  slli       a3, gp, 19
                  andi       sp, a3, 305
                  nop
                  mulh       sp, tp, a1
                  c.slli     s9, 19
                  sra        t6, t3, tp
                  rem        s11, t3, a6
                  c.or       a4, a2
                  c.srai     a4, 11
                  rem        a5, s6, a0
                  srl        s1, a6, s3
                  lui        t0, 137521
                  c.srli     a4, 30
                  sltu       sp, zero, s8
                  c.srli     a2, 27
                  nop
                  srl        a0, s5, tp
                  add        s11, s10, a7
                  ori        tp, s5, 870
                  srli       t1, sp, 26
                  andi       s11, s10, 1005
                  div        a0, t5, a0
                  mulhsu     a5, s0, zero
                  xor        t5, s11, s6
                  c.slli     t6, 5
                  xor        s8, t2, tp
                  c.and      a2, a5
                  c.addi4spn a2, sp, 912
                  or         a4, s6, s6
                  c.nop
                  mulhsu     a4, a2, s1
                  mul        s9, ra, s11
                  ori        a3, a6, 691
                  addi       t2, a3, -919
                  sll        gp, a7, a2
                  mulh       ra, t2, sp
                  c.sub      a2, a1
                  slli       zero, s1, 5
                  add        s0, ra, a1
                  slli       s11, s10, 4
                  sra        a3, t2, s0
                  mulhu      gp, s1, s11
                  slti       gp, a7, -351
                  sltu       s1, t5, a2
                  mulh       s10, t2, a6
                  c.addi4spn s1, sp, 816
                  remu       t5, t5, t4
                  mulhsu     t0, s9, a6
                  mul        a3, ra, s7
                  lui        gp, 81271
                  remu       ra, sp, s7
                  div        s9, a1, s9
                  nop
                  slti       zero, t5, -920
                  srl        s0, ra, s8
                  c.li       t5, 8
                  sra        s9, s10, t6
                  c.add      t5, s5
                  c.sub      a4, a0
                  sll        s9, a0, a2
                  add        a6, s11, s6
                  c.addi4spn a5, sp, 592
                  srli       a3, t1, 13
                  slt        a3, a4, t4
                  sub        s1, s0, ra
                  c.add      gp, s2
                  auipc      t6, 132265
                  c.addi     s0, 16
                  ori        s10, t6, -213
                  andi       s7, tp, -894
                  remu       s1, zero, a5
                  sra        ra, a0, a5
                  c.srai     a5, 31
                  xor        sp, t0, a3
                  c.lui      a2, 26
                  rem        s10, s0, s9
                  sub        a3, a0, a3
                  addi       t1, t1, -382
                  c.srai     s0, 15
                  divu       s10, s3, a2
                  xor        t6, sp, a0
                  srai       s0, s9, 4
                  c.nop
                  sub        t3, t3, t6
                  srli       s7, t1, 27
                  c.addi4spn a1, sp, 992
                  c.mv       s1, a3
                  sra        a1, s10, t1
                  c.srai     a3, 31
                  sltiu      t2, a3, 375
                  c.addi4spn a3, sp, 496
                  srl        a3, a7, a5
                  c.sub      a0, s1
                  andi       s10, s0, -223
                  c.add      a2, s11
                  c.xor      a2, a4
                  and        a6, s11, t5
                  c.and      a5, a5
                  mulh       s3, t2, s7
                  divu       a3, s3, a2
                  and        sp, s11, s7
                  ori        t2, a6, -120
                  div        t3, zero, t5
                  ori        a3, s6, -834
                  and        s4, s0, s10
                  mulhu      gp, a7, t6
                  c.srai     a1, 6
                  c.srli     a3, 23
                  xori       s6, t4, 565
                  c.li       s10, -1
                  c.and      s0, s0
                  slt        zero, t1, sp
                  mul        a4, t4, t0
                  c.sub      a2, a3
                  or         ra, t4, zero
                  srai       a4, s6, 3
                  slli       a1, a2, 16
                  divu       t1, s5, zero
                  auipc      a4, 172564
                  c.andi     a2, 7
                  andi       s3, a3, 196
                  mul        gp, a4, s5
                  div        s5, s6, ra
                  slt        s4, a5, gp
                  divu       s11, s6, t4
                  c.sub      a4, a2
                  c.or       s1, a5
                  nop
                  srl        tp, a5, a7
                  li         s10, 0x4443648 #start riscv_int_numeric_corner_stream_30
                  li         a0, 0x0
                  li         s5, 0x80000000
                  li         t3, 0x80000000
                  li         s7, 0x0
                  li         t2, 0xffffffff
                  li         s4, 0xffffffff
                  li         ra, 0x80000000
                  li         s3, 0x80000000
                  li         a3, 0x80000000
                  auipc      a0, 130061
                  mulh       ra, t3, s5
                  mul        s3, s7, s7
                  mul        s10, s10, s3
                  rem        s3, ra, s5
                  mulhsu     s7, a0, s10
                  rem        s5, s4, s7
                  remu       s5, s7, ra
                  div        s3, a0, s7
                  div        s10, t3, s3
                  mul        t3, s10, s7
                  addi       ra, t3, 228
                  remu       s3, s5, s7
                  rem        s5, a0, s10
                  mulh       a0, s5, ra
                  mulhu      ra, s7, s3
                  mulhu      s10, s7, s5
                  nop
                  addi       a0, t3, -726
                  nop
                  mul        a3, a0, t2
                  rem        ra, a0, t3
                  div        s10, ra, a3
                  mulhsu     s3, ra, ra
                  nop
                  sub        t3, t2, a0
                  auipc      a3, 373530 #end riscv_int_numeric_corner_stream_30
                  c.add      t0, s11
                  andi       t3, t4, -736
                  mulh       s5, s4, t1
                  sltiu      t0, t4, 928
                  sra        a5, t5, s8
                  sra        a4, t2, t2
                  sll        s3, t6, t5
                  mulhsu     a0, a0, a2
                  slti       s7, a0, 409
                  mulh       a1, t0, s0
                  auipc      a0, 360944
                  srai       t3, s7, 20
                  remu       a2, zero, s4
                  lui        gp, 678610
                  c.srli     a2, 6
                  andi       t5, tp, 909
                  div        s4, t0, a2
                  slli       a6, t3, 29
                  c.xor      a2, s1
                  auipc      ra, 464366
                  ori        t6, t2, -670
                  andi       a6, s11, 708
                  and        a3, a6, s8
                  slli       a3, tp, 21
                  nop
                  srli       t0, s5, 30
                  andi       sp, a2, 985
                  c.srli     s1, 21
                  sll        gp, s2, zero
                  srai       t2, s7, 0
                  div        a1, t4, gp
                  xor        gp, s3, zero
                  mul        t3, a7, t4
                  c.addi4spn a1, sp, 880
                  nop
                  slti       tp, t6, -16
                  xor        s6, sp, t5
                  mulhsu     t2, t1, s11
                  c.srai     a0, 26
                  c.andi     s0, 27
                  c.nop
                  xori       s4, t1, -832
                  c.nop
                  c.sub      s1, s0
                  c.or       a0, a0
                  add        s6, s4, s8
                  c.or       a4, a4
                  c.addi4spn a5, sp, 656
                  or         t5, t2, a1
                  add        t6, s10, s5
                  c.mv       a1, s5
                  mulhsu     t5, ra, a5
                  c.srai     a0, 11
                  c.or       a0, a5
                  sltiu      s1, sp, 650
                  c.or       a2, a0
                  c.srli     s1, 13
                  xori       t3, a5, 880
                  mul        s7, s1, t5
                  and        s9, t4, t4
                  and        ra, t4, t6
                  add        t3, t5, s1
                  sltu       a6, gp, t1
                  c.srai     a5, 31
                  c.srli     a0, 16
                  rem        a2, a5, t2
                  sll        a6, a0, s0
                  nop
                  mulh       tp, sp, t1
                  ori        s11, s2, 441
                  andi       t5, s0, 601
                  slli       a1, a0, 31
                  c.andi     s1, -1
                  rem        tp, s11, s3
                  add        s9, s1, t1
                  mulhsu     s6, a0, t4
                  mul        s1, t4, gp
                  srl        s10, s5, ra
                  c.and      a5, a5
                  and        a0, s8, s10
                  xor        t0, s10, sp
                  nop
                  srai       t1, s11, 16
                  c.xor      s1, a4
                  addi       t5, s5, -380
                  srli       s3, t6, 29
                  c.xor      a0, a2
                  sltu       s8, t1, a0
                  and        a3, ra, s3
                  c.addi16sp sp, 256
                  sub        a5, s10, s3
                  mul        a2, a4, s5
                  nop
                  mulhu      a1, s9, ra
                  c.addi16sp sp, -16
                  mulh       ra, ra, zero
                  sltu       a3, t1, a7
                  c.srai     a4, 30
                  auipc      t5, 839177
                  divu       t0, s2, a2
                  add        ra, s0, s8
                  remu       sp, a0, s6
                  mul        gp, s7, s6
                  div        a0, s2, zero
                  lui        t6, 280925
                  c.add      t6, t2
                  div        gp, a1, t6
                  srl        s5, a1, s10
                  c.slli     a5, 11
                  div        a4, t5, s5
                  c.mv       gp, a7
                  c.sub      a5, a4
                  c.srli     a2, 30
                  c.addi     s6, -1
                  c.addi4spn a5, sp, 528
                  c.or       s1, a5
                  add        a6, s6, a3
                  mulhu      s1, gp, t1
                  sltiu      s10, s2, 164
                  andi       a3, a5, -945
                  srai       t2, s11, 17
                  c.addi     a3, 3
                  slt        tp, s4, t3
                  mulh       s7, sp, t1
                  xor        a6, s6, s3
                  srli       s7, zero, 17
                  c.addi4spn a4, sp, 304
                  lui        t3, 729150
                  c.li       a4, 22
                  slt        a6, s1, a6
                  slli       t1, s8, 21
                  mul        gp, a3, a3
                  c.add      tp, sp
                  c.nop
                  lui        a2, 62005
                  nop
                  div        s10, t5, t2
                  srai       s3, s11, 11
                  mulhu      t3, t4, a1
                  addi       a5, t6, -45
                  remu       t0, a5, zero
                  xori       s5, t3, -620
                  sub        s10, s1, zero
                  c.mv       t1, s5
                  remu       t5, s11, t3
                  c.srai     a0, 11
                  c.srli     a2, 6
                  mulh       s7, a1, s10
                  addi       a1, a3, 40
                  c.xor      s1, a0
                  mul        a5, s0, zero
                  nop
                  mulh       a6, a2, ra
                  auipc      tp, 1037367
                  rem        ra, ra, t4
                  lui        s1, 343485
                  c.srli     a0, 14
                  c.addi     s0, -1
                  c.xor      a5, s1
                  sub        s9, t4, gp
                  addi       t6, zero, 202
                  slti       t2, a1, 336
                  remu       sp, s9, a1
                  c.andi     a0, -1
                  mulhu      a1, a5, s11
                  srl        s5, a2, s9
                  nop
                  xor        a6, a1, s5
                  c.xor      s1, a1
                  c.srli     a1, 2
                  c.srli     a5, 8
                  srl        a0, s3, s5
                  srl        s6, t3, t1
                  lui        t2, 751442
                  and        t5, a5, a5
                  mulh       s11, a1, ra
                  srl        a5, t5, t4
                  c.srai     a2, 27
                  c.and      a4, a4
                  slli       s10, a0, 27
                  sltiu      a0, a3, -955
                  sra        s3, t3, s7
                  c.or       a0, a2
                  c.addi16sp sp, 224
                  sltiu      sp, t2, -717
                  srli       t5, ra, 21
                  c.mv       a1, a4
                  srai       a2, s6, 25
                  c.srli     a4, 4
                  slli       t6, gp, 14
                  divu       a6, a5, s5
                  sltiu      s0, a2, 923
                  add        s4, t2, ra
                  c.or       a4, s0
                  divu       s3, s2, a0
                  remu       a0, s7, a5
                  c.srai     a4, 12
                  sub        zero, t6, gp
                  rem        s7, t4, t3
                  c.addi4spn a0, sp, 368
                  c.sub      a2, s0
                  c.slli     s4, 14
                  mulhu      tp, t4, a2
                  c.sub      a5, s0
                  c.lui      tp, 5
                  c.or       a4, a2
                  c.xor      s1, s0
                  sltu       s9, a1, s9
                  slli       sp, a2, 12
                  lui        a6, 713196
                  div        t3, a3, zero
                  auipc      a2, 387159
                  c.or       a3, a4
                  c.addi16sp sp, 128
                  addi       zero, a6, 446
                  lui        t2, 117768
                  c.andi     s0, -1
                  sll        s1, s1, s6
                  srl        s3, a4, s5
                  ori        s7, tp, 838
                  auipc      s8, 268190
                  mul        s10, zero, ra
                  c.andi     s0, 1
                  sub        tp, t3, t2
                  c.addi     a4, -1
                  mulhsu     s1, a3, s4
                  mulhu      a2, t1, t1
                  c.addi16sp sp, 448
                  mul        a6, a0, s7
                  c.li       a5, -1
                  c.srli     a1, 7
                  sra        s10, ra, a0
                  c.li       s4, -1
                  auipc      s11, 702746
                  c.sub      s1, a0
                  c.lui      t2, 22
                  nop
                  remu       sp, a2, t0
                  c.and      a2, a3
                  remu       a0, s3, tp
                  srai       t3, s9, 2
                  andi       s0, t6, -618
                  c.srli     a4, 15
                  auipc      s5, 736768
                  nop
                  mulhu      sp, s9, a6
                  or         t2, a2, t4
                  c.addi16sp sp, -16
                  andi       s5, t5, 505
                  sub        t0, s1, gp
                  c.srai     a4, 22
                  c.or       a0, a2
                  c.lui      s8, 19
                  sll        a1, ra, a6
                  nop
                  c.srli     a2, 31
                  ori        s8, s2, 805
                  xor        zero, a2, s5
                  c.mv       s3, s1
                  lui        s6, 749987
                  sll        t6, a1, a3
                  sltiu      tp, tp, 823
                  c.lui      s10, 2
                  and        t1, sp, a3
                  nop
                  slli       s9, s9, 4
                  srai       s6, a5, 31
                  c.addi4spn a1, sp, 752
                  nop
                  rem        a2, s6, a1
                  sra        s7, a5, t2
                  c.addi16sp sp, 496
                  xor        s8, ra, a6
                  slli       s7, s5, 26
                  c.slli     s3, 16
                  sltiu      s8, a0, 982
                  sub        s1, s7, tp
                  c.addi     t0, 24
                  c.add      a3, s3
                  c.or       a0, a1
                  c.slli     a4, 13
                  add        s4, s7, s10
                  sltiu      a0, s10, 413
                  c.xor      s1, a5
                  lui        a4, 507701
                  c.sub      a1, a4
                  slli       zero, a2, 13
                  sll        sp, a7, a0
                  add        sp, t5, t3
                  sra        tp, s9, s2
                  auipc      a0, 37586
                  c.srai     s0, 18
                  addi       t0, s11, -708
                  auipc      a1, 670529
                  c.andi     s0, 3
                  c.nop
                  auipc      s8, 997640
                  srli       s7, s6, 3
                  c.add      gp, gp
                  c.lui      s5, 4
                  rem        t6, sp, a7
                  srl        s8, t1, a1
                  rem        s5, a1, s6
                  ori        a6, t3, -903
                  divu       s10, t1, t3
                  slti       tp, a6, -917
                  remu       s5, a6, sp
                  srli       t2, gp, 0
                  c.addi16sp sp, 432
                  c.sub      a3, s1
                  xori       sp, sp, -383
                  slli       s8, a5, 26
                  mulh       s8, a1, a2
                  div        tp, a3, ra
                  sub        tp, a5, a1
                  or         t0, s5, s11
                  xor        tp, s7, a3
                  sll        s10, t1, a0
                  c.nop
                  rem        sp, gp, sp
                  mulh       s4, gp, s11
                  add        a0, s2, t3
                  slti       a4, t6, -126
                  slli       t0, t5, 27
                  c.addi4spn a3, sp, 192
                  slt        s4, sp, a4
                  c.lui      s0, 10
                  rem        t6, t4, t3
                  divu       a0, sp, a4
                  c.lui      t5, 7
                  c.srai     a5, 3
                  c.xor      a2, a5
                  mul        a4, s9, a5
                  mul        t0, zero, zero
                  c.sub      a3, a1
                  sra        s5, sp, t2
                  c.srli     a4, 25
                  c.slli     a5, 26
                  xori       a5, s0, 927
                  sltiu      t5, t6, -452
                  c.nop
                  sll        a2, t3, s6
                  c.addi16sp sp, 160
                  c.lui      a6, 7
                  sub        ra, s5, a0
                  c.or       a2, a3
                  and        s8, s8, s10
                  c.addi16sp sp, -16
                  xor        s7, ra, t5
                  add        a0, a7, gp
                  slti       s3, s4, 190
                  mulhsu     t1, a7, t6
                  c.or       a1, s0
                  xor        s7, s1, a7
                  add        s1, s11, s1
                  srai       t0, t2, 13
                  add        t5, s0, s2
                  divu       s5, s9, s7
                  div        s6, sp, s1
                  xori       ra, a7, -252
                  or         t2, a5, t2
                  c.add      a0, s6
                  srai       t2, ra, 5
                  srai       sp, a4, 17
                  addi       s5, ra, -822
                  c.and      a5, a5
                  srli       a6, a3, 24
                  xor        s0, t2, a1
                  c.add      t6, t0
                  add        s5, s4, s3
                  addi       t3, s11, -645
                  c.or       a3, s1
                  c.or       a5, a2
                  srl        zero, s10, a2
                  c.add      s4, t1
                  srai       s11, s6, 6
                  xori       s5, s6, 509
                  c.addi4spn a3, sp, 880
                  c.xor      a0, a4
                  and        t0, tp, t0
                  mulhsu     a4, t5, t2
                  c.andi     a5, -1
                  srai       s5, a2, 1
                  c.nop
                  c.addi     s10, -1
                  slt        s11, a3, t4
                  c.li       sp, 7
                  mulh       a1, sp, s8
                  c.add      s4, gp
                  xori       s1, t4, -466
                  c.li       t6, -1
                  c.nop
                  c.and      a2, a0
                  srai       gp, s4, 22
                  c.addi4spn a4, sp, 1008
                  c.add      a3, s5
                  sub        tp, tp, a5
                  nop
                  c.and      s1, s0
                  mulh       tp, t3, s5
                  c.li       a1, 10
                  mul        sp, ra, tp
                  sub        s8, a6, s0
                  xor        s4, ra, s7
                  lui        a4, 1023398
                  c.addi16sp sp, -16
                  sll        t1, t0, s4
                  c.li       t0, -1
                  sra        a3, t2, s3
                  sltu       t2, zero, t2
                  c.addi4spn a2, sp, 912
                  c.xor      s0, a3
                  c.addi16sp sp, 480
                  c.srli     a3, 12
                  c.srli     s1, 27
                  sltiu      a1, zero, -479
                  andi       t0, s3, -228
                  slti       a4, sp, -335
                  and        a6, a0, s1
                  ori        t3, t3, -328
                  c.lui      a5, 22
                  c.addi16sp sp, 160
                  sltu       t6, ra, s9
                  div        a3, zero, s2
                  c.srli     a0, 6
                  auipc      s0, 85593
                  c.li       t1, 22
                  sltiu      s3, s9, -214
                  sub        a0, t0, s2
                  xor        s5, t0, t4
                  c.srai     s1, 15
                  mulhsu     ra, s8, a4
                  c.srli     s1, 14
                  mulhsu     s4, a0, s2
                  ori        s1, s11, 741
                  add        t0, t1, a0
                  mulhu      s11, a4, a5
                  c.slli     a4, 23
                  xori       a4, a5, -585
                  slt        s1, t0, s9
                  xori       s4, s0, -363
                  c.nop
                  c.sub      a1, a4
                  c.or       a0, a3
                  srai       s10, gp, 17
                  addi       a6, t5, 478
                  slli       s8, s2, 2
                  c.addi4spn a4, sp, 352
                  xori       a1, tp, 988
                  rem        s9, s7, a7
                  c.andi     s0, 0
                  ori        s4, a4, 174
                  c.nop
                  c.li       s3, -1
                  rem        sp, gp, a5
                  xori       s1, a4, -871
                  c.lui      s4, 28
                  rem        a1, a4, t2
                  c.and      a0, a4
                  c.and      a5, s1
                  c.xor      a0, a5
                  addi       s8, tp, -214
                  remu       s0, t5, a2
                  srli       s5, t5, 18
                  divu       s0, a3, a7
                  sll        a5, a5, t1
                  lui        s6, 258581
                  c.andi     s1, -1
                  slli       s0, s10, 31
                  mulh       a4, s11, t5
                  c.slli     t5, 18
                  sltu       a3, s10, s4
                  c.addi     t5, -1
                  andi       a1, ra, -116
                  or         a3, t6, s10
                  xori       sp, s11, 639
                  add        a5, a4, ra
                  srai       s7, zero, 26
                  c.slli     t0, 9
                  rem        s3, s9, t4
                  nop
                  c.slli     s1, 24
                  c.srli     a4, 5
                  c.add      sp, s0
                  mulh       gp, gp, t2
                  sltiu      s6, a5, 877
                  c.addi     s8, -1
                  srai       s9, t6, 21
                  c.slli     s9, 16
                  or         a5, s0, s1
                  slli       t5, t5, 1
                  add        a1, sp, t0
                  nop
                  c.addi4spn a2, sp, 224
                  mulh       t3, t1, s8
                  add        s6, s10, a3
                  add        s0, s5, t0
                  c.or       a2, a3
                  c.slli     s0, 22
                  c.add      t2, s8
                  sub        a1, s4, t5
                  addi       sp, a5, 114
                  c.or       a1, a5
                  sltu       sp, a3, s0
                  add        s3, s11, s1
                  srli       a2, a2, 6
                  mulhsu     t1, s10, a1
                  slt        t0, s9, a1
                  rem        s3, s3, s10
                  c.srli     s0, 17
                  srli       a2, a3, 25
                  c.nop
                  addi       s10, s4, -563
                  mulhsu     t5, s8, a2
                  srai       a4, t4, 15
                  c.lui      t5, 28
                  andi       s5, a1, 76
                  and        t5, s9, a5
                  mulhu      a0, s6, s11
                  andi       t0, s0, -549
                  remu       sp, s3, s7
                  slt        t2, t1, a5
                  srl        a3, s1, s2
                  c.addi     ra, -1
                  xori       s1, a1, -865
                  srli       t5, a1, 22
                  sltiu      t5, t6, 308
                  and        a6, t3, a1
                  c.slli     s9, 27
                  sltu       s0, a0, s9
                  xor        t6, t4, sp
                  c.add      s1, s9
                  add        t2, s1, t5
                  or         a1, a5, s10
                  slti       a0, a7, 290
                  sra        t3, a1, sp
                  rem        a2, t3, s2
                  lui        a6, 801164
                  remu       a2, s4, a3
                  srai       tp, s11, 10
                  c.li       t0, 2
                  c.or       a2, a1
                  c.lui      t2, 22
                  xori       s3, zero, 1003
                  slt        s7, t0, s6
                  c.srli     a1, 17
                  c.addi16sp sp, -16
                  mul        a2, a4, s8
                  andi       s1, t0, 536
                  sltiu      s1, s6, -632
                  srl        s4, gp, t2
                  and        s9, a2, gp
                  c.xor      a2, s1
                  remu       s0, s1, zero
                  c.srli     a0, 19
                  slt        zero, s11, s6
                  slti       t2, zero, -349
                  slli       t6, sp, 17
                  lui        s5, 451386
                  c.srai     a3, 5
                  remu       s9, a1, s5
                  mulhsu     a2, t5, a3
                  c.and      a5, a1
                  c.addi     a3, 6
                  xori       t0, s6, 814
                  c.mv       s6, gp
                  auipc      tp, 922959
                  nop
                  nop
                  c.add      s0, s8
                  slti       t0, t2, 323
                  sll        s10, t1, a6
                  add        t3, s11, t5
                  mulh       s5, sp, t4
                  xori       s1, a7, -223
                  c.and      a0, a4
                  c.sub      a3, a0
                  sub        sp, a5, t0
                  remu       s11, s4, s0
                  divu       a4, ra, gp
                  srli       t1, a0, 5
                  c.or       a0, a5
                  mulhsu     t3, t0, s6
                  srli       t5, s6, 22
                  divu       s9, a3, t1
                  c.mv       t3, a1
                  c.and      a0, a3
                  c.li       s4, -1
                  c.addi4spn s1, sp, 576
                  rem        t1, s3, s7
                  and        t0, s5, s1
                  remu       zero, t2, t3
                  auipc      t2, 622321
                  xori       sp, zero, 946
                  addi       s6, s6, 950
                  xori       tp, ra, -988
                  c.srli     a3, 31
                  auipc      s9, 138368
                  mulh       s0, s6, tp
                  c.slli     s1, 16
                  c.andi     a1, -1
                  c.addi4spn a2, sp, 224
                  mul        ra, a6, t1
                  c.and      a1, a3
                  srai       gp, a3, 22
                  rem        a1, s11, a4
                  slti       s7, sp, 386
                  mulh       t3, a4, gp
                  c.srli     a4, 12
                  div        a6, gp, s11
                  mulh       s3, t5, s5
                  auipc      s11, 277562
                  sltiu      a2, a5, 900
                  c.and      a2, a0
                  ori        s6, a2, -379
                  slti       s6, a6, 612
                  sll        ra, t6, a7
                  div        s8, a7, s8
                  or         a0, a6, s8
                  srli       a4, s8, 11
                  and        a3, s11, s10
                  sra        t6, s7, a6
                  lui        a2, 313817
                  or         s4, a6, t1
                  lui        zero, 67187
                  div        s8, ra, a0
                  lui        a5, 859448
                  mulh       t5, a2, t4
                  and        t6, s11, a0
                  xori       a2, s6, 66
                  andi       s11, a6, 699
                  c.slli     a2, 6
                  andi       gp, t3, 129
                  c.mv       sp, s0
                  srai       s10, s5, 28
                  c.srai     a4, 8
                  c.srli     a3, 9
                  xor        t1, s5, t2
                  c.li       sp, -1
                  slti       s9, s4, 597
                  auipc      t5, 953608
                  and        s6, s7, sp
                  divu       s0, zero, s11
                  andi       a1, t2, -268
                  c.add      t2, t3
                  sll        t3, s9, s4
                  divu       a3, a6, s6
                  xor        t5, t4, s2
                  mulhsu     s4, s6, gp
                  c.lui      a6, 29
                  srl        t5, t3, s3
                  slti       s1, s2, -285
                  c.and      s1, a0
                  div        s1, t6, sp
                  c.lui      t0, 10
                  andi       tp, tp, 115
                  slt        s8, s2, t3
                  xor        zero, a7, a5
                  sltiu      t3, ra, -989
                  divu       zero, t5, a3
                  or         a1, a7, gp
                  slli       s7, a2, 29
                  c.addi4spn a5, sp, 576
                  div        s8, a5, zero
                  c.addi     t3, 29
                  ori        ra, s9, -148
                  c.srai     a0, 5
                  addi       s6, a1, -366
                  divu       t6, s3, s4
                  c.add      s11, t4
                  c.nop
                  c.srai     a5, 16
                  addi       s6, t4, 884
                  c.lui      s7, 30
                  and        t5, s2, t1
                  and        t6, s11, a3
                  sll        t5, s5, t5
                  c.slli     t3, 6
                  remu       s4, a4, s11
                  c.sub      a2, s0
                  ori        s0, sp, 665
                  c.add      gp, a6
                  ori        a3, t4, 596
                  divu       s1, a7, s4
                  c.sub      a1, s0
                  c.add      t5, sp
                  slti       zero, s3, -867
                  c.or       a3, s0
                  c.andi     a2, -1
                  c.nop
                  mulhsu     s10, sp, a0
                  c.sub      s1, a1
                  and        s6, t0, t1
                  and        t0, a4, zero
                  c.addi     a6, 11
                  and        s10, t6, a7
                  rem        s0, ra, s11
                  sra        s10, a4, s8
                  c.addi     s8, -1
                  auipc      gp, 943366
                  ori        s3, t5, -836
                  auipc      s8, 587192
                  sra        s6, t6, a0
                  divu       a4, a2, a4
                  divu       s3, sp, a6
                  c.li       a4, -1
                  lui        s0, 794982
                  slt        ra, t6, s5
                  and        a6, sp, s2
                  andi       s10, gp, -960
                  c.sub      a5, s0
                  addi       a1, gp, -394
                  addi       a6, t0, -300
                  slti       a4, s0, -328
                  rem        gp, s1, sp
                  c.sub      a4, s1
                  c.addi16sp sp, 416
                  xor        t1, s5, s8
                  c.xor      a3, s1
                  mulh       gp, s7, s8
                  c.andi     s0, 29
                  c.andi     a4, 29
                  c.srli     a5, 31
                  mul        a1, t5, t5
                  mulhu      s8, t1, s7
                  c.addi4spn a2, sp, 464
                  div        s1, t0, ra
                  srli       a1, s4, 12
                  c.addi4spn a5, sp, 16
                  sltu       tp, s8, zero
                  andi       t5, a7, -878
                  slli       t3, zero, 10
                  div        t1, t5, a6
                  mul        a2, t0, s10
                  divu       s3, a5, a4
                  c.xor      a0, s1
                  xori       s4, a3, 343
                  sub        t2, zero, a7
                  lui        t1, 669332
                  c.li       a4, -1
                  nop
                  sra        s4, a1, tp
                  mulhsu     s0, s0, s6
                  c.srli     a2, 25
                  xor        a5, s6, zero
                  mulh       a0, t2, a4
                  andi       zero, s5, 916
                  c.slli     a3, 16
                  srai       t2, gp, 5
                  c.addi4spn a4, sp, 272
                  c.or       a4, a2
                  c.srli     a1, 3
                  xor        sp, a2, s0
                  xori       a0, s10, -764
                  c.nop
                  or         a3, a6, t1
                  and        s4, t4, t6
                  add        t6, s11, s0
                  c.lui      s0, 19
                  divu       s7, sp, a1
                  div        a5, a1, s8
                  c.slli     a3, 8
                  c.srai     a2, 31
                  auipc      tp, 308960
                  ori        t6, s11, -824
                  c.addi16sp sp, 80
                  sltiu      gp, s2, 121
                  auipc      t5, 833041
                  ori        s4, a3, -74
                  srl        t0, s10, t6
                  sll        s7, gp, sp
                  c.sub      a5, a5
                  c.add      s5, t3
                  add        a5, sp, s5
                  sltu       t2, s9, s11
                  c.sub      a4, a3
                  slti       s3, s0, -437
                  ori        sp, t0, 906
                  and        t3, s1, s8
                  c.mv       s0, s1
                  c.srai     a2, 9
                  mul        s0, a0, s2
                  c.srli     a3, 7
                  sltu       a0, a5, t4
                  auipc      zero, 890600
                  remu       a5, s4, t4
                  c.srli     a0, 28
                  c.and      a1, a4
                  srl        s7, tp, s4
                  srli       s1, t5, 3
                  c.srli     a0, 29
                  addi       sp, t3, -702
                  c.add      t0, s11
                  mulh       s0, s1, s0
                  c.xor      a5, s1
                  auipc      s4, 378181
                  c.lui      s10, 14
                  nop
                  ori        s5, t0, 811
                  c.srai     a4, 3
                  slti       s0, zero, 50
                  sll        s10, tp, s4
                  c.andi     s0, 29
                  sltiu      s11, s8, 927
                  and        t0, t5, a5
                  srai       tp, s10, 20
                  divu       t6, a6, a4
                  xori       a2, s1, -587
                  sll        s0, t4, s0
                  c.li       t3, 29
                  c.mv       t6, s3
                  lui        gp, 219074
                  andi       a1, s1, -694
                  c.addi4spn a2, sp, 1008
                  c.sub      a5, a3
                  mul        gp, s5, a0
                  rem        s1, t0, a6
                  c.srli     a4, 8
                  div        a2, gp, a2
                  mulh       a2, s4, t3
                  slli       a4, tp, 23
                  rem        s8, zero, s3
                  slt        s6, a1, a3
                  sub        s3, a3, t1
                  remu       tp, s10, zero
                  slti       s5, s8, -881
                  ori        t2, ra, 417
                  c.srli     s0, 16
                  xor        t6, a2, a5
                  c.mv       s6, tp
                  c.addi16sp sp, -16
                  sltu       t5, s4, ra
                  rem        s8, a6, s11
                  srai       t1, t0, 29
                  nop
                  sra        gp, s11, zero
                  mulhsu     a3, gp, t2
                  sltu       zero, t2, s0
                  c.addi     s1, -1
                  c.srai     a0, 9
                  mul        s10, s9, a7
                  sra        s5, tp, a5
                  sltiu      s10, s1, 891
                  slti       a1, ra, 393
                  mulh       s7, s8, t4
                  sltu       s0, s1, t5
                  sltu       s0, a4, s8
                  mulhu      sp, s8, s1
                  c.li       a0, 18
                  mul        s10, t6, s4
                  lui        sp, 1001463
                  c.lui      a0, 11
                  srl        s11, s0, a2
                  sltu       a1, a0, s2
                  xori       zero, t6, 543
                  sub        a0, s10, ra
                  c.and      a4, s1
                  slt        t3, s6, a0
                  mul        s6, a0, a0
                  c.andi     a1, -1
                  c.nop
                  divu       a1, s5, a4
                  srai       s5, t5, 13
                  or         a5, a0, t6
                  sub        t2, t5, s9
                  c.lui      s5, 23
                  slli       s5, s0, 2
                  rem        t3, a5, t1
                  xor        s9, s1, s0
                  mulhsu     a1, a2, a4
                  andi       s11, gp, -731
                  c.addi     t6, -1
                  c.li       s0, -1
                  mulhu      a1, s8, a5
                  c.slli     s8, 30
                  c.addi     t3, -1
                  mulh       t1, t1, t2
                  c.addi     a0, -1
                  c.nop
                  c.srai     a2, 27
                  sub        a3, a0, s4
                  c.li       s7, -1
                  c.or       a1, a5
                  or         zero, s3, s6
                  c.addi16sp sp, 128
                  andi       t3, t0, -439
                  xori       t6, s1, -650
                  c.lui      s1, 22
                  c.sub      s1, a5
                  div        a6, zero, s3
                  srli       a2, a6, 18
                  sltiu      t5, s0, 461
                  c.addi     a3, -1
                  mul        t2, s3, gp
                  c.addi4spn a5, sp, 464
                  div        a0, gp, tp
                  srl        t2, t3, t2
                  srli       t3, tp, 13
                  auipc      s9, 837343
                  slli       s8, tp, 21
                  sra        a3, s0, s2
                  addi       s7, a3, -691
                  mul        s9, s8, s0
                  srl        s5, a7, t3
                  mulhsu     gp, a2, s11
                  c.slli     a2, 19
                  c.lui      s1, 20
                  remu       s11, s4, a5
                  and        s10, s4, t0
                  c.addi16sp sp, -16
                  slti       gp, s9, 231
                  nop
                  auipc      gp, 823204
                  slt        sp, a6, s8
                  c.mv       t6, t4
                  c.or       a2, a4
                  c.addi4spn s0, sp, 992
                  c.nop
                  c.srli     a2, 2
                  mulhu      a2, s9, t3
                  c.srli     a5, 24
                  slti       s10, gp, -754
                  c.and      a3, s1
                  c.andi     a2, -1
                  sub        a2, t5, s8
                  c.sub      s0, a4
                  sltu       t3, zero, a0
                  rem        a2, s5, a1
                  add        sp, a7, a6
                  div        zero, s7, t1
                  sltu       t2, t2, t3
                  c.li       a0, 8
                  mul        t1, a4, s5
                  div        t3, a5, zero
                  nop
                  c.xor      s1, a5
                  c.srai     a0, 13
                  sltu       s4, t3, s1
                  c.srai     a5, 31
                  sll        t2, t2, s11
                  c.addi16sp sp, 352
                  mulhu      s5, a1, t2
                  c.sub      a4, a5
                  mulh       s1, s11, t4
                  c.nop
                  c.li       s4, -1
                  mulh       gp, ra, a0
                  c.li       sp, 24
                  c.add      s4, a6
                  rem        tp, s6, s4
                  c.xor      a5, a5
                  c.lui      s5, 4
                  xori       t0, sp, 729
                  c.andi     a1, -1
                  c.andi     a1, -1
                  c.mv       a4, t1
                  c.nop
                  divu       zero, a4, a0
                  mul        s0, a7, a3
                  sub        tp, s9, s0
                  slli       t3, a3, 7
                  c.sub      a1, a4
                  srl        t6, a0, ra
                  xori       s6, s7, 532
                  srai       a5, tp, 24
                  div        sp, a3, t4
                  divu       s5, t3, t4
                  c.sub      a0, s1
                  slli       s1, a0, 18
                  srai       t5, t6, 25
                  c.lui      s9, 1
                  sub        s5, s6, a6
                  lui        s11, 914436
                  sltiu      s8, s8, -71
                  rem        a4, s8, gp
                  rem        sp, t5, a6
                  c.nop
                  sltu       s5, t0, a1
                  ori        t5, t5, 752
                  addi       a1, zero, -632
                  c.addi     s0, 21
                  remu       s8, s2, a6
                  remu       s9, s5, s3
                  and        s4, s4, s0
                  nop
                  sub        zero, a0, s6
                  mulhu      s8, a2, s11
                  c.slli     a1, 7
                  c.srli     a1, 23
                  c.add      ra, a3
                  sll        a5, s3, s11
                  sltiu      a0, a0, -1015
                  auipc      s7, 560071
                  c.srai     a1, 27
                  sll        gp, t1, zero
                  andi       t2, a2, 133
                  c.add      t2, s1
                  c.addi     s10, -1
                  c.slli     t5, 7
                  c.and      a4, a0
                  or         t1, ra, t5
                  mulhu      s10, t1, a3
                  mulhsu     t6, s11, gp
                  c.xor      s1, a2
                  srli       t5, t6, 29
                  slt        a5, t0, a5
                  sltiu      gp, s10, 758
                  c.mv       ra, t4
                  srai       t2, s3, 14
                  ori        sp, a4, -1
                  c.srli     a4, 4
                  c.srli     s0, 16
                  div        s0, a6, a3
                  slt        s6, s8, s2
                  div        a4, t3, t5
                  rem        s1, a4, a6
                  c.add      sp, s10
                  lui        s3, 1043068
                  slt        gp, t3, t2
                  c.srai     a0, 3
                  c.or       a0, s0
                  c.xor      a2, a2
                  c.li       s6, -1
                  nop
                  c.sub      a1, a3
                  mulhu      t5, zero, s11
                  lui        sp, 76939
                  ori        a0, sp, -487
                  nop
                  and        a2, a3, a4
                  c.andi     a4, 7
                  sltu       a3, sp, a6
                  sra        s4, a5, t4
                  or         s3, a5, s9
                  andi       s10, s1, 42
                  sub        s1, a7, a6
                  c.slli     s5, 4
                  sltiu      ra, s7, -621
                  lui        a1, 143208
                  c.addi16sp sp, -16
                  mul        gp, tp, s6
                  sltu       s3, s8, a3
                  xor        a0, s7, s1
                  c.srai     a0, 9
                  mul        sp, s1, t0
                  xor        t5, sp, a1
                  or         t2, ra, t6
                  ori        s7, s9, 236
                  sub        a3, ra, t1
                  auipc      zero, 727186
                  c.lui      s8, 18
                  c.or       s0, a1
                  c.or       s0, a1
                  div        t3, t5, a2
                  c.andi     a2, -1
                  sltiu      s10, t1, -583
                  c.sub      a5, a5
                  div        a0, s3, a0
                  c.addi     s0, 30
                  remu       s10, tp, t1
                  slti       t6, s5, 507
                  srai       a2, s0, 1
                  mulhu      s6, gp, a7
                  c.or       a1, a0
                  mulh       a3, t6, zero
                  andi       s7, a1, -203
                  c.mv       s0, s1
                  c.xor      a0, s1
                  div        gp, s8, gp
                  sra        s10, sp, t6
                  lui        s11, 323454
                  andi       s8, a6, 1014
                  c.andi     a0, 5
                  ori        ra, s0, -406
                  c.addi4spn s1, sp, 912
                  srli       a6, a2, 24
                  srli       s11, sp, 19
                  c.lui      a3, 27
                  remu       s9, s2, t2
                  remu       t3, s8, s0
                  div        s3, a6, t3
                  c.nop
                  c.slli     a6, 24
                  c.addi4spn s0, sp, 384
                  or         a0, t5, ra
                  divu       zero, s1, a6
                  andi       a5, a2, -673
                  lui        a2, 914858
                  mulh       a1, t1, s8
                  srli       s8, a2, 19
                  c.xor      a0, s1
                  c.li       s1, -1
                  srl        s3, sp, a4
                  and        s8, s2, t5
                  c.sub      a0, a0
                  mulhu      s1, sp, a0
                  c.sub      a2, s1
                  c.addi4spn a1, sp, 528
                  or         a6, a7, s1
                  c.addi4spn a0, sp, 48
                  mulhu      zero, a6, a4
                  divu       s8, s3, a4
                  c.mv       s9, s8
                  mulh       a4, t2, a3
                  c.addi16sp sp, -16
                  c.lui      a3, 25
                  srli       s8, a4, 17
                  c.srli     a4, 6
                  srai       a1, s9, 15
                  c.andi     a2, 31
                  srl        a5, s4, s5
                  mulhsu     s1, s3, a1
                  srli       t2, tp, 9
                  xor        zero, a0, t6
                  sub        tp, ra, gp
                  c.or       a0, s1
                  c.srli     a3, 1
                  andi       s0, t4, 27
                  c.andi     a3, 16
                  c.srai     a2, 21
                  and        t0, t2, t6
                  and        t0, s6, s8
                  xori       s3, tp, 343
                  auipc      s10, 929271
                  add        t2, s3, s8
                  mulhsu     t0, s2, s3
                  sltu       s7, t2, s10
                  srai       s4, s0, 23
                  xor        t5, s4, sp
                  sra        a1, a7, t6
                  c.nop
                  slli       t3, a1, 31
                  mulhu      a2, t1, s0
                  c.add      ra, s2
                  sltiu      s3, a1, -911
                  mulhu      s8, tp, t2
                  mulhu      s6, a0, s1
                  srl        s3, a0, s10
                  andi       zero, t6, -462
                  c.nop
                  c.add      t6, t5
                  xori       t5, s11, -156
                  srai       s1, sp, 5
                  c.xor      a1, a1
                  c.or       a4, a3
                  mulh       t1, t4, gp
                  sub        t6, tp, t5
                  c.mv       t3, s5
                  srl        a4, a7, a3
                  slli       t1, s6, 5
                  div        s9, s11, tp
                  c.nop
                  c.mv       s4, s2
                  sll        gp, t1, s2
                  mulh       s10, zero, t4
                  c.sub      s0, a1
                  c.addi16sp sp, -16
                  xor        s8, a6, s9
                  or         a0, t3, ra
                  sra        zero, s7, a7
                  mulhu      t5, t0, s3
                  mul        s5, s11, t1
                  c.li       t5, -1
                  c.or       a0, a4
                  c.addi     s10, -1
                  addi       ra, t2, -540
                  mul        ra, t6, s0
                  c.li       a5, 20
                  c.andi     a0, 31
                  mulhu      sp, a0, a7
                  c.andi     a2, -1
                  c.lui      s8, 15
                  c.xor      a4, a3
                  srl        gp, s0, s11
                  divu       t3, tp, s3
                  slli       t0, a7, 10
                  div        sp, t0, s0
                  sll        a1, t6, a6
                  addi       s9, gp, 202
                  c.srai     a1, 14
                  c.sub      s0, a2
                  c.addi4spn a0, sp, 912
                  c.addi16sp sp, -16
                  mulh       a1, a5, t1
                  add        s8, s4, a5
                  c.and      s1, a4
                  c.andi     a1, 24
                  c.addi4spn s0, sp, 560
                  c.or       a5, a4
                  or         t1, s11, s1
                  slli       a6, t1, 12
                  c.sub      a4, s1
                  slti       s5, t0, -897
                  c.add      s4, sp
                  mulh       s4, sp, s7
                  mul        s11, s0, tp
                  c.mv       a1, tp
                  rem        t2, s0, a5
                  ori        s5, s4, 808
                  nop
                  lui        a4, 664664
                  rem        s10, sp, t0
                  c.slli     a0, 1
                  c.addi16sp sp, -16
                  divu       t3, s1, s11
                  c.add      t2, s8
                  c.srai     a5, 5
                  or         sp, a1, s8
                  sltiu      zero, s0, -465
                  nop
                  srai       t3, a7, 31
                  c.addi16sp sp, -16
                  div        a5, a7, s8
                  div        s6, s8, gp
                  sra        gp, t3, zero
                  c.addi4spn a2, sp, 880
                  c.or       s1, s1
                  c.srli     a4, 2
                  sltiu      s11, tp, 723
                  divu       s6, a4, s7
                  c.or       a0, s0
                  slli       a3, s2, 17
                  mulhu      t6, s0, a4
                  mul        t0, t1, s4
                  div        a0, t3, s10
                  mul        tp, s1, a7
                  and        s6, s11, s11
                  mulhu      s0, a1, a4
                  add        gp, t0, s11
                  add        a4, t4, s6
                  and        gp, gp, t3
                  c.or       a2, s1
                  c.addi     ra, -1
                  slli       s8, s2, 10
                  divu       t2, a0, s9
                  srai       gp, s4, 5
                  sltiu      sp, a7, -191
                  c.andi     s0, 31
                  c.xor      s0, s0
                  c.andi     a0, 13
                  mulhu      s0, s2, t2
                  lui        s7, 398932
                  sub        a0, ra, sp
                  ori        s9, t0, 727
                  slt        a1, s3, s0
                  c.li       s8, 30
                  c.sub      a3, s1
                  addi       t3, t4, -50
                  mulhsu     tp, s4, a1
                  mul        s4, gp, s11
                  auipc      a6, 215521
                  andi       a5, s7, 934
                  slti       a5, a7, 264
                  xori       gp, a7, 991
                  rem        t3, a4, s8
                  and        sp, s8, s5
                  xor        a3, t3, s5
                  div        t1, zero, t4
                  mulhu      s11, a7, gp
                  or         s9, a5, s2
                  xor        a1, s0, sp
                  mulhu      s8, a3, s3
                  srai       s1, a0, 9
                  addi       a5, s10, -995
                  c.mv       a1, a5
                  divu       a5, a0, s4
                  srai       t5, s1, 25
                  lui        a5, 642612
                  c.lui      t6, 19
                  and        t5, s3, tp
                  c.or       a4, a3
                  c.li       tp, -1
                  c.addi     sp, 20
                  c.mv       t6, t3
                  sub        sp, t0, t5
                  addi       a5, a6, -964
                  divu       a0, s5, s10
                  c.addi     sp, -1
                  mulhsu     t0, zero, s0
                  mulhu      sp, t2, t2
                  rem        s11, zero, s4
                  and        a6, s11, s3
                  sltiu      a0, s4, 578
                  rem        t1, s9, s8
                  c.slli     a2, 1
                  slti       sp, zero, 979
                  remu       a0, zero, s0
                  sub        sp, a5, a3
                  c.lui      a3, 20
                  c.mv       s0, t0
                  mulh       zero, gp, s5
                  srli       ra, a2, 2
                  auipc      s8, 593248
                  mul        s4, a4, t5
                  c.sub      a2, a0
                  sll        s1, t6, a3
                  srai       t0, a2, 10
                  slli       t6, a0, 18
                  c.srai     s0, 2
                  slt        s8, t6, sp
                  divu       tp, gp, t5
                  rem        s4, s2, a3
                  mulhsu     a6, s3, a1
                  srl        t5, a1, sp
                  c.xor      a3, a2
                  add        a4, s8, s9
                  c.slli     s10, 16
                  c.addi4spn a1, sp, 976
                  c.xor      a2, a3
                  ori        a2, tp, 909
                  remu       zero, zero, t6
                  c.li       gp, 15
                  c.li       s9, -1
                  c.nop
                  c.srai     a3, 15
                  divu       sp, gp, ra
                  c.li       sp, 14
                  divu       a4, s3, t3
                  divu       a1, t1, s11
                  c.xor      a2, a1
                  auipc      a2, 220839
                  c.addi     t3, 4
                  c.mv       s4, t6
                  mulh       s0, s5, s3
                  remu       s7, s2, t0
                  sub        s0, s3, t3
                  rem        s9, tp, t3
                  c.or       s1, s0
                  sra        s9, s1, s5
                  c.sub      a3, a1
                  c.nop
                  srli       t2, tp, 6
                  addi       a0, gp, 396
                  remu       ra, t3, t2
                  auipc      t6, 373333
                  mulh       a6, s10, s7
                  li         s11, 0x80000000 #start riscv_int_numeric_corner_stream_12
                  li         s4, 0xffffffff
                  li         t0, 0x388d8d71
                  li         s3, 0x0
                  li         t5, 0x80000000
                  li         a4, 0x80000000
                  li         s10, 0xffffffff
                  li         t6, 0xffffffff
                  li         gp, 0xffffffff
                  li         sp, 0x0
                  div        a4, t5, s10
                  remu       gp, a4, t5
                  div        a4, gp, t5
                  auipc      t0, 263438
                  auipc      s11, 788233
                  div        s10, sp, s4
                  mulhu      t6, gp, s11
                  add        t6, s10, s3
                  addi       a4, t5, -153
                  addi       t5, s3, -177
                  mulhu      a4, s4, sp
                  mulhu      a4, t0, gp
                  mul        t0, s3, a4
                  mulh       s4, s3, gp
                  mulhu      sp, t0, s3
                  mul        s11, s3, s11
                  lui        t6, 60975
                  remu       sp, s4, s11
                  div        s3, s3, sp
                  rem        t0, s10, sp #end riscv_int_numeric_corner_stream_12
                  c.addi16sp sp, 304
                  remu       s10, s8, t4
                  or         s7, a0, a5
                  c.mv       a5, t5
                  c.xor      a1, a4
                  lui        s11, 173768
                  andi       a2, s2, -330
                  srai       sp, ra, 30
                  c.andi     a1, -1
                  ori        s7, a2, 522
                  c.add      t0, t4
                  lui        s6, 877264
                  c.nop
                  c.andi     a2, -1
                  srl        s6, s11, a3
                  auipc      tp, 919228
                  or         a3, ra, s5
                  mul        s3, s4, t1
                  slt        tp, s5, tp
                  xor        s6, gp, s8
                  sra        t2, s11, a6
                  add        t2, ra, t5
                  sub        sp, gp, s1
                  c.xor      s0, a3
                  c.andi     a2, -1
                  slli       s9, t6, 0
                  add        s11, a1, t4
                  and        s0, t3, t2
                  c.addi     t2, 16
                  nop
                  sll        a1, a6, s1
                  sltu       s1, t6, a3
                  xori       t2, t0, 641
                  mulhu      t3, s0, s0
                  ori        s8, t3, 553
                  c.addi4spn a5, sp, 928
                  sltiu      t5, t6, 522
                  c.or       s0, s0
                  ori        s1, tp, 263
                  sltu       a4, s11, s1
                  auipc      s11, 3706
                  c.li       s7, 9
                  sltiu      gp, s8, 164
                  sll        a6, a1, s11
                  sltiu      t0, zero, -49
                  mulh       t2, s9, t1
                  sltiu      s9, s5, 873
                  slt        tp, tp, s9
                  c.srai     a5, 6
                  srl        s5, s4, t6
                  c.andi     a2, -1
                  slli       t3, tp, 2
                  divu       a3, t6, a1
                  slli       a0, a2, 21
                  c.addi4spn a4, sp, 992
                  sltu       t5, t3, t0
                  srai       s6, t2, 7
                  c.lui      t5, 11
                  mul        ra, t6, sp
                  c.addi     s5, 26
                  c.li       s8, -1
                  sll        a2, s9, s8
                  addi       t2, t4, 303
                  mulhu      a3, s2, s8
                  slt        t6, t0, gp
                  slti       a6, a1, -321
                  mul        a6, a5, s10
                  andi       s5, s8, 82
                  sub        sp, t5, s4
                  sub        s1, a1, a0
                  xor        t1, s1, t0
                  auipc      a1, 752176
                  mulhu      a5, zero, gp
                  rem        t5, t1, a6
                  mul        t5, tp, s5
                  srl        a5, a4, gp
                  remu       s1, s5, s1
                  srl        a2, a5, a1
                  addi       t1, s6, 998
                  mulh       t2, zero, a0
                  sltiu      zero, a5, 349
                  c.addi     s1, 22
                  divu       a6, t5, a0
                  c.addi16sp sp, -16
                  c.addi16sp sp, 240
                  slt        ra, tp, s3
                  li         s5, 0x80000000 #start riscv_int_numeric_corner_stream_5
                  li         s3, 0x0
                  li         a6, 0x926d6020
                  li         t5, 0xffffffff
                  li         s1, 0x0
                  li         ra, 0xffffffff
                  li         a0, 0x80000000
                  li         s11, 0x80000000
                  li         s8, 0x0
                  li         tp, 0x80000000
                  remu       s5, s3, s5
                  sub        a0, a0, ra
                  remu       ra, s1, s5
                  mulhu      t5, tp, tp
                  remu       ra, ra, s1
                  add        t5, t5, s3
                  auipc      t5, 637556
                  rem        s8, s3, s1
                  rem        s1, s1, t5
                  rem        s8, s8, s3
                  mulhu      tp, tp, tp
                  mulh       a0, t5, s5
                  add        a6, ra, tp
                  divu       a0, a6, a6
                  divu       s3, s11, s11
                  nop
                  auipc      a6, 43244
                  divu       s5, a0, s5
                  div        s11, s11, a0
                  auipc      s11, 946557
                  mulhsu     a6, s1, a6
                  mulh       s8, s5, t5
                  addi       tp, s3, -278
                  mulh       ra, s1, a0
                  rem        s3, ra, a0
                  mulhu      tp, a0, s5
                  nop #end riscv_int_numeric_corner_stream_5
                  mulh       a5, a4, a0
                  slt        t1, s5, s6
                  sub        a3, sp, s9
                  c.lui      ra, 25
                  srai       t0, s4, 26
                  srl        ra, a3, t6
                  mulh       s4, s8, a5
                  ori        a3, sp, 415
                  sltiu      s8, tp, 315
                  andi       zero, gp, -181
                  c.or       a3, a5
                  c.add      s11, t0
                  xori       a1, s9, -826
                  ori        s0, s8, 667
                  c.or       s1, a3
                  c.xor      s1, s0
                  c.and      s0, a5
                  nop
                  or         s6, t1, t1
                  c.li       a2, 14
                  c.xor      a0, a3
                  sra        t0, a2, a0
                  auipc      a1, 1001819
                  and        t6, s4, s6
                  srli       s5, t5, 17
                  mulhu      s4, s9, s1
                  c.addi     a2, 12
                  c.slli     a4, 7
                  or         s8, s6, a6
                  ori        gp, t5, 568
                  nop
                  mulhsu     s7, a4, a5
                  andi       a2, s6, -419
                  add        gp, ra, t4
                  c.or       a4, s0
                  slt        t1, s4, s0
                  mul        t6, s0, t4
                  c.slli     s3, 20
                  xori       s9, zero, 683
                  c.and      a1, a1
                  sltu       s11, a3, s10
                  sltiu      tp, zero, 621
                  c.mv       sp, s6
                  srai       s0, a0, 26
                  c.nop
                  c.li       t0, 29
                  div        s0, t3, s11
                  c.mv       s6, t6
                  slt        a3, sp, a3
                  c.sub      a4, a0
                  c.li       s0, -1
                  c.mv       ra, a6
                  sub        s10, s9, t5
                  c.add      s11, t0
                  and        s11, s5, t5
                  sll        s8, s0, a4
                  slli       a2, s9, 29
                  c.and      s0, a3
                  sltu       s6, t4, t0
                  nop
                  c.lui      s4, 7
                  divu       zero, ra, s10
                  add        s11, s2, t0
                  addi       sp, ra, 299
                  mulhsu     a0, t0, t6
                  srl        t0, s2, s2
                  c.andi     a4, -1
                  mulhu      t0, s11, t2
                  and        a2, a4, s11
                  addi       tp, a7, 382
                  srl        s7, zero, s4
                  srai       t5, t2, 4
                  srli       s11, a0, 4
                  c.mv       ra, a6
                  add        s10, sp, t6
                  c.slli     sp, 4
                  c.and      s1, s0
                  srl        a4, zero, t2
                  mulh       s9, s6, s6
                  c.addi4spn a2, sp, 32
                  c.addi     a6, -1
                  addi       t5, t2, 321
                  c.add      s1, a3
                  add        zero, s5, s5
                  c.slli     s3, 7
                  srli       s10, gp, 31
                  c.sub      a4, s1
                  c.srai     s0, 26
                  ori        s11, gp, -234
                  mulhsu     a1, t4, a0
                  auipc      s5, 234315
                  sltiu      a5, s7, 223
                  sub        s1, a0, s5
                  remu       s7, a3, t3
                  andi       a6, t4, -739
                  sub        s9, t2, a5
                  c.nop
                  divu       t5, s2, t3
                  sltu       t5, a1, t5
                  mulh       s3, s7, s5
                  sltiu      t5, tp, -755
                  rem        s11, s10, t1
                  c.andi     a0, -1
                  nop
                  rem        s8, s10, sp
                  lui        tp, 28562
                  c.addi4spn a4, sp, 832
                  slt        t3, s7, s8
                  c.nop
                  sltu       a4, a5, s5
                  slti       ra, a3, 112
                  sll        sp, a1, t6
                  c.and      a2, a3
                  sltu       t0, a3, tp
                  andi       a6, t4, 711
                  and        s6, a0, a1
                  and        ra, s1, t3
                  mul        t5, sp, a0
                  or         gp, s8, t0
                  srl        ra, ra, t0
                  mulhu      gp, t1, ra
                  srl        t5, s11, t1
                  and        a1, s9, ra
                  and        zero, s3, s4
                  c.srai     a3, 7
                  mul        zero, t1, t0
                  c.xor      a0, s1
                  sltu       a6, a4, gp
                  c.or       a4, a3
                  slli       s6, a6, 18
                  c.or       s1, a5
                  slli       a2, t0, 12
                  c.andi     a0, 28
                  xor        t1, a4, a5
                  slti       t1, a4, -358
                  c.mv       s7, a6
                  mulhu      s6, a4, t5
                  c.andi     s1, -1
                  c.andi     a3, -1
                  srai       s3, a4, 19
                  sra        s10, t6, a3
                  c.sub      a5, s0
                  srli       s11, t4, 12
                  xori       a5, s9, -202
                  c.srli     a4, 21
                  remu       t0, s2, a1
                  addi       a2, t3, 394
                  mul        t3, a1, a4
                  auipc      s8, 769486
                  mul        t1, gp, gp
                  auipc      ra, 43242
                  ori        t1, t4, 207
                  sll        a5, s7, sp
                  srl        s3, a7, a1
                  c.srai     a1, 29
                  divu       gp, s6, a7
                  c.srli     a5, 26
                  addi       s6, t0, 420
                  div        t2, ra, s9
                  c.addi16sp sp, -16
                  c.or       a1, a1
                  add        a3, s11, zero
                  or         a3, t3, a6
                  mul        t2, s0, a4
                  divu       sp, a2, s10
                  c.xor      a5, a0
                  c.srli     s1, 16
                  xori       t2, t0, 730
                  andi       t5, s1, 754
                  mulhu      s9, s6, tp
                  rem        t0, a7, s6
                  or         a4, sp, a6
                  sll        s7, s3, s8
                  sll        a2, a6, a3
                  divu       s11, t0, t3
                  remu       zero, a2, zero
                  sll        s10, s1, a4
                  srai       s10, t3, 8
                  mulh       s9, t3, s0
                  c.mv       s6, s3
                  c.slli     t6, 26
                  c.lui      s11, 1
                  c.lui      a5, 11
                  c.li       s1, 12
                  rem        s6, t0, a7
                  c.srai     a4, 7
                  mulh       a0, sp, t0
                  srl        a5, t3, t6
                  slt        s1, a0, a3
                  auipc      a5, 209415
                  slli       t2, s5, 19
                  slli       a5, s4, 9
                  mulhu      s3, ra, s6
                  div        s7, t3, s6
                  and        a3, s11, s3
                  srli       s4, a1, 17
                  mulhu      s5, s10, s7
                  c.srai     a0, 1
                  slli       s1, sp, 26
                  c.or       a5, s1
                  srl        s0, s2, t5
                  c.lui      s11, 1
                  div        ra, t2, t2
                  mulh       t3, gp, t5
                  c.srli     a5, 8
                  addi       s8, sp, -84
                  c.addi16sp sp, 80
                  sub        s11, t0, t4
                  sub        gp, s8, s9
                  or         s8, s1, sp
                  sltu       t0, s3, gp
                  mul        s6, a1, s6
                  addi       a1, s6, 859
                  rem        zero, s9, ra
                  add        t2, a1, s4
                  c.or       a2, a3
                  sra        s10, t1, s5
                  and        a0, s7, s2
                  add        ra, gp, s1
                  or         t0, a5, t3
                  sra        t6, gp, t5
                  srli       s11, gp, 31
                  sltu       zero, s2, s10
                  sll        a4, s4, t5
                  c.or       a3, a1
                  divu       s0, t6, t4
                  ori        t6, s6, 376
                  c.addi     t6, -1
                  c.srli     a2, 23
                  c.andi     a5, 10
                  xor        a6, s1, s10
                  mulh       t1, s2, s5
                  c.andi     s0, 9
                  xor        gp, a7, s6
                  divu       s5, t3, t4
                  c.sub      a0, s0
                  c.add      ra, ra
                  xor        s4, s6, ra
                  c.mv       s11, t6
                  xori       t5, t0, -811
                  sll        a3, a1, t5
                  c.addi     s0, -1
                  c.andi     a0, 23
                  xori       a4, s2, -587
                  xori       s5, s5, 848
                  slt        a4, a6, a4
                  mulhu      a5, t0, gp
                  andi       gp, a7, 436
                  addi       t5, s5, -597
                  nop
                  c.addi4spn a1, sp, 816
                  add        s7, ra, a4
                  or         a2, a6, tp
                  sra        t1, a7, a1
                  mulhu      a2, t3, s3
                  lui        s0, 344320
                  remu       t2, s1, t2
                  srai       s4, a3, 8
                  srl        t0, sp, tp
                  srai       t6, a2, 31
                  and        t3, s0, t0
                  c.xor      s1, a4
                  remu       s3, s11, s0
                  sll        t0, ra, t5
                  sra        s6, t2, s5
                  sra        zero, ra, s1
                  slli       zero, a5, 16
                  auipc      t3, 441021
                  andi       s6, zero, -791
                  slli       t5, ra, 6
                  c.sub      a0, s1
                  sra        a0, t5, s5
                  c.addi4spn a0, sp, 288
                  c.xor      a4, a5
                  sub        s11, a4, a7
                  c.xor      a4, s0
                  c.addi16sp sp, 384
                  c.and      s0, a2
                  c.or       a2, a0
                  slt        t6, ra, t2
                  c.and      a5, a5
                  ori        sp, t6, -754
                  divu       t5, s2, t1
                  srl        s3, tp, s7
                  sltu       s9, a4, t2
                  andi       s4, a0, -61
                  sra        s10, s4, s0
                  c.mv       t3, t0
                  lui        a3, 221954
                  xori       s8, s0, -934
                  lui        t5, 986283
                  c.addi     a4, -1
                  nop
                  c.or       a4, a0
                  c.and      a5, s1
                  c.nop
                  or         ra, tp, s6
                  c.addi     s10, 13
                  mulh       s4, t6, zero
                  c.li       s4, 12
                  addi       t3, a2, -142
                  srai       s1, a3, 12
                  lui        t6, 184025
                  c.lui      s3, 8
                  mulhu      a6, s11, sp
                  c.srli     a4, 28
                  c.li       s10, -1
                  c.lui      a4, 16
                  c.mv       a0, t1
                  c.xor      a4, a3
                  mulh       t1, a2, a2
                  sll        s1, s8, a6
                  or         a4, s9, a2
                  and        a5, sp, t3
                  lui        s7, 491243
                  rem        t5, a6, s1
                  div        t0, s4, a1
                  sltiu      s7, a0, 624
                  c.nop
                  mulhsu     t1, a6, a4
                  c.nop
                  c.sub      a2, s1
                  srl        a3, zero, s0
                  c.nop
                  mul        s11, s8, zero
                  mulh       a4, a4, s10
                  c.addi     s4, -1
                  c.lui      s0, 24
                  c.addi     a1, 9
                  c.add      a6, s1
                  rem        s1, a4, a5
                  andi       t5, a0, -64
                  andi       s11, a6, -78
                  and        a5, t2, s10
                  c.xor      a2, s0
                  slli       a2, s2, 13
                  mul        a6, s11, tp
                  divu       s9, a2, s10
                  c.li       s8, -1
                  c.addi4spn s1, sp, 448
                  rem        a1, s2, a0
                  c.srli     s0, 1
                  lui        ra, 819191
                  mulh       zero, s10, t4
                  divu       a0, t3, sp
                  srl        gp, ra, s1
                  c.sub      a0, a4
                  divu       s1, a2, a4
                  c.addi16sp sp, 304
                  divu       s5, a1, a3
                  rem        s9, s11, a0
                  c.srli     s0, 6
                  mulhsu     gp, sp, a7
                  xor        s6, a2, a4
                  c.sub      a4, a5
                  sltiu      t3, t6, 367
                  add        s4, ra, sp
                  divu       s10, ra, t3
                  c.add      a1, s1
                  slli       gp, s4, 9
                  c.nop
                  slti       s1, s6, -507
                  srl        t5, t2, s6
                  xori       t2, s1, -813
                  c.lui      t1, 4
                  c.and      a3, a5
                  or         sp, s3, t1
                  sltu       s11, s2, s0
                  c.sub      a1, s1
                  c.sub      a0, a3
                  slt        s4, a4, t3
                  slti       gp, t5, -101
                  sub        s8, a1, t1
                  and        ra, zero, s1
                  c.sub      s0, s1
                  c.xor      a4, a2
                  sra        t3, tp, s6
                  c.xor      a0, s1
                  mul        gp, s4, a5
                  xor        a2, a1, s7
                  c.add      ra, s11
                  ori        t5, s6, -457
                  c.addi     s4, 2
                  div        s5, a5, s7
                  c.addi4spn s0, sp, 160
                  c.xor      a3, a4
                  add        gp, a7, a7
                  c.addi     t2, -1
                  sub        a5, s0, gp
                  sra        a2, t4, s7
                  nop
                  and        tp, s0, a6
                  mulh       t6, s0, s5
                  divu       gp, t0, t4
                  ori        s5, s4, -479
                  srli       a5, s10, 6
                  c.and      a2, a1
                  c.nop
                  sltiu      zero, s5, -824
                  c.or       a5, a5
                  nop
                  li         s11, 0x0 #start riscv_int_numeric_corner_stream_32
                  li         t1, 0x4556d0b8
                  li         s1, 0x0
                  li         a4, 0xffffffff
                  li         a5, 0x959b0289
                  li         s3, 0xffffffff
                  li         sp, 0x80000000
                  li         s8, 0x8e0ff458
                  li         t6, 0xffffffff
                  li         s5, 0x695766c9
                  nop
                  divu       s8, a4, s3
                  mulhu      t1, t1, t1
                  divu       s1, s5, t6
                  addi       s11, s5, 927
                  add        s8, s1, a4
                  add        s3, s3, a5
                  mulhsu     t1, s1, a5
                  mul        s11, s3, sp
                  rem        s3, t1, a5
                  remu       s1, sp, s3
                  mul        t6, sp, t1
                  auipc      sp, 153844
                  divu       a5, t1, s3
                  remu       s3, s5, a5
                  mul        s3, s11, s8 #end riscv_int_numeric_corner_stream_32
                  addi       zero, s2, 779
                  lui        s4, 502544
                  slti       s8, t1, 1007
                  lui        t0, 765861
                  c.add      t3, s9
                  rem        s3, s0, s10
                  mulhsu     a5, t1, s10
                  or         a6, s3, a5
                  sra        s6, zero, zero
                  c.nop
                  sltiu      s11, ra, -443
                  c.add      s7, gp
                  srli       zero, s1, 28
                  ori        t6, a2, -148
                  div        ra, a5, t0
                  sltu       a6, zero, s7
                  mulhsu     s3, s1, t4
                  mulhu      s0, s2, t1
                  mulhsu     s3, t4, tp
                  sub        t2, a4, s0
                  srli       t6, a4, 7
                  addi       s9, a0, -854
                  c.nop
                  remu       t1, a3, a2
                  c.srli     s1, 22
                  c.lui      t3, 18
                  c.srli     a2, 7
                  c.addi4spn a5, sp, 48
                  sub        a4, t6, s11
                  srai       s0, s7, 7
                  xor        a2, a7, zero
                  addi       a4, s8, -313
                  c.nop
                  rem        s1, t0, s11
                  sub        t0, t4, t6
                  slt        a3, s0, s5
                  addi       sp, a0, -855
                  mulhsu     a0, s3, zero
                  rem        a6, a3, s5
                  add        a3, tp, t5
                  c.nop
                  and        a5, s5, s7
                  add        ra, t2, t1
                  sub        s4, s6, a2
                  mulhu      a5, s9, s11
                  c.lui      t1, 20
                  c.srai     a2, 5
                  c.addi4spn a2, sp, 976
                  c.addi4spn a1, sp, 992
                  slli       t6, s0, 2
                  c.slli     a4, 27
                  sltiu      s7, t6, -654
                  c.mv       a5, s8
                  sltu       tp, gp, s10
                  srai       s5, tp, 21
                  c.add      t2, s8
                  c.nop
                  xori       t6, s4, 471
                  c.srai     a0, 1
                  srli       s3, s6, 23
                  c.lui      t2, 15
                  c.li       t5, 30
                  c.addi4spn s1, sp, 832
                  slt        sp, s5, sp
                  srli       t5, a3, 31
                  c.add      s11, s11
                  c.mv       t3, t4
                  sra        zero, a6, a1
                  c.and      a0, s1
                  xor        tp, sp, sp
                  mulhu      a1, t3, t6
                  slli       s8, s1, 16
                  srli       s8, sp, 25
                  c.addi16sp sp, -16
                  ori        t5, ra, -63
                  slli       s1, sp, 15
                  c.addi     s1, 1
                  c.addi4spn a2, sp, 16
                  mul        a5, t0, s2
                  c.addi     s4, 30
                  addi       zero, a6, 454
                  sltiu      t6, s1, 737
                  mulhu      tp, gp, a7
                  c.mv       s5, a2
                  sra        s7, a0, t1
                  and        t2, t4, zero
                  sll        ra, a6, t1
                  sub        s3, s2, s6
                  divu       s7, a5, gp
                  xor        t5, t5, t5
                  sltu       a4, tp, s9
                  or         t3, t3, t4
                  lui        zero, 685119
                  c.mv       t5, a5
                  andi       s8, a7, 653
                  and        s4, s11, s4
                  srl        ra, t1, s6
                  rem        t6, s11, t2
                  sub        t3, s9, t3
                  slti       a2, a4, -73
                  c.nop
                  xor        tp, a4, tp
                  auipc      s5, 638675
                  sub        s6, s11, a3
                  c.addi4spn a5, sp, 672
                  c.addi16sp sp, -16
                  sll        s11, s11, t5
                  sll        t6, s11, a3
                  slt        a4, s3, s8
                  c.li       s8, -1
                  rem        s8, s3, a3
                  auipc      a5, 299066
                  sub        t0, a3, zero
                  ori        gp, s10, -482
                  addi       s11, s2, 239
                  c.addi16sp sp, 112
                  mulhsu     a2, t1, s3
                  andi       tp, zero, -599
                  c.add      sp, a6
                  remu       a5, a6, a7
                  c.sub      a2, a0
                  nop
                  addi       t2, a2, -684
                  c.and      a3, a3
                  c.addi4spn a5, sp, 16
                  nop
                  and        t2, s10, sp
                  c.xor      a1, a2
                  rem        s0, s1, s8
                  nop
                  nop
                  divu       ra, t0, zero
                  mulhsu     t5, s1, a5
                  sub        a5, a6, s9
                  xor        t3, s1, t6
                  srl        s1, s8, t0
                  sll        s1, a2, t4
                  lui        t2, 286439
                  c.xor      a2, s0
                  divu       s0, a6, s5
                  slti       s6, sp, 490
                  c.addi     s8, -1
                  ori        t6, t3, -79
                  c.li       s9, 7
                  sra        a2, t5, t2
                  c.nop
                  c.add      sp, a5
                  c.mv       t1, s3
                  c.srai     s0, 7
                  c.addi     t3, -1
                  c.addi4spn a2, sp, 288
                  sra        s7, t2, t2
                  srai       t5, sp, 29
                  c.addi     a1, -1
                  mul        s0, ra, s11
                  lui        gp, 335479
                  c.sub      a0, a3
                  add        t2, s5, t5
                  or         s10, a5, s5
                  c.and      a3, a1
                  c.addi     a2, -1
                  mulhsu     a3, a0, ra
                  c.addi     s8, -1
                  rem        t0, a6, zero
                  c.addi16sp sp, 144
                  sltu       s11, s8, s3
                  c.addi     s10, -1
                  lui        a6, 907810
                  c.li       s5, 7
                  c.addi     s6, 7
                  sub        a2, a5, s9
                  c.andi     a0, -1
                  mulhu      t1, a1, t0
                  srai       zero, sp, 27
                  c.srai     a4, 2
                  lui        a1, 425875
                  slti       gp, s0, -625
                  c.xor      a5, a2
                  mul        zero, tp, s11
                  c.addi4spn s0, sp, 608
                  c.andi     a1, 4
                  xori       a0, t5, -84
                  srli       ra, s1, 31
                  c.andi     a4, 7
                  divu       sp, s3, t1
                  divu       t1, t0, s8
                  mulhu      a0, a7, ra
                  sub        s9, tp, a0
                  mulhu      s3, s11, gp
                  sltiu      s0, t3, 68
                  c.lui      t3, 5
                  c.addi     a4, -1
                  mul        t3, s6, s10
                  c.lui      a0, 17
                  c.addi     t2, -1
                  c.addi     t0, -1
                  c.li       a4, 4
                  auipc      s7, 74286
                  and        a3, a1, zero
                  sra        s11, a5, a1
                  rem        s10, t0, s7
                  rem        a1, s2, s4
                  divu       s0, s7, sp
                  ori        s9, ra, -148
                  c.srli     s0, 25
                  divu       a4, t6, a4
                  rem        s6, s9, s11
                  c.sub      a0, s1
                  c.nop
                  srli       a2, a2, 8
                  ori        s5, sp, 592
                  c.addi16sp sp, -16
                  c.mv       s8, s6
                  c.li       t2, -1
                  mulh       t1, s3, s3
                  slli       t0, a6, 7
                  c.slli     s3, 1
                  or         a6, ra, s3
                  nop
                  c.li       s10, -1
                  remu       s8, t0, a7
                  c.li       t2, -1
                  xor        s6, s2, t2
                  srli       tp, s6, 3
                  andi       t6, zero, 928
                  c.sub      a5, s0
                  c.sub      a1, a2
                  c.and      a0, a1
                  mulhu      t6, s3, s9
                  c.slli     s10, 13
                  c.nop
                  srl        tp, s3, t4
                  sll        ra, s9, ra
                  c.lui      a6, 1
                  srli       t5, s6, 0
                  mulh       a0, s4, zero
                  c.add      s9, a2
                  xor        s4, t2, s9
                  sra        s9, s11, a5
                  sltu       s3, s6, a5
                  c.srli     s1, 23
                  xor        s10, t4, t2
                  srli       s3, s2, 9
                  slli       s1, a1, 4
                  remu       t6, s1, t2
                  sll        s6, s1, t4
                  rem        zero, tp, a1
                  andi       a0, t0, -225
                  divu       t6, s0, s4
                  srai       t5, a6, 10
                  xori       t3, t5, 6
                  srli       s11, a7, 24
                  addi       tp, t0, -561
                  srai       s7, s6, 22
                  ori        a3, a0, -495
                  remu       s6, ra, s11
                  mul        a0, tp, s4
                  c.and      a5, a3
                  c.and      a1, a2
                  c.sub      a3, a5
                  c.and      a3, a2
                  ori        zero, t0, -907
                  slti       a2, s5, -609
                  sra        a2, sp, s7
                  div        s8, a2, t4
                  sub        a0, a4, t2
                  c.addi16sp sp, -16
                  c.nop
                  lui        s11, 260117
                  c.or       s1, a4
                  mulhsu     t1, a3, s11
                  addi       tp, s6, -798
                  ori        zero, tp, -302
                  mulhu      s9, s7, s11
                  auipc      a3, 295
                  xori       s6, t3, 827
                  srai       a1, a1, 4
                  srai       a1, gp, 3
                  slt        s5, a5, s5
                  sltu       sp, a5, ra
                  sll        t1, a0, t1
                  rem        a1, sp, s3
                  sltu       s9, t5, s3
                  c.sub      a0, a2
                  and        s3, s5, a4
                  c.slli     ra, 19
                  c.addi     s7, -1
                  ori        t2, a5, 420
                  rem        s8, s2, s1
                  c.sub      s0, s1
                  c.srai     s1, 31
                  remu       gp, s4, s9
                  c.mv       s10, s11
                  c.addi4spn s1, sp, 496
                  sll        s3, sp, t6
                  sltiu      s11, a4, -875
                  sub        t6, s0, zero
                  c.add      tp, gp
                  mulhsu     t6, t1, t4
                  div        t5, s6, s0
                  andi       tp, zero, -314
                  mulh       t2, a7, gp
                  lui        t2, 609431
                  srl        s5, tp, s9
                  c.add      s11, s10
                  slti       s11, t2, -636
                  slt        t2, s3, t4
                  mulh       t5, gp, a6
                  xor        a1, s8, s11
                  sltu       s4, a7, zero
                  mul        t6, s8, s0
                  nop
                  or         a4, s2, a4
                  srli       a5, tp, 27
                  sub        sp, a0, gp
                  c.or       s1, a4
                  srli       ra, t5, 11
                  mulh       t1, a2, t6
                  srai       t6, a3, 29
                  sub        s9, tp, s5
                  lui        s4, 996234
                  c.nop
                  sltu       t1, s6, s1
                  slli       s3, s6, 22
                  c.and      s1, a2
                  slti       t3, s11, 511
                  divu       t6, tp, a4
                  sra        t3, tp, s0
                  c.slli     a1, 5
                  c.lui      t2, 30
                  mulhu      s0, s4, s2
                  srai       s0, s9, 7
                  srai       zero, ra, 25
                  c.addi     sp, 27
                  mul        a4, s9, gp
                  sltu       t3, sp, s8
                  slti       s5, a4, 377
                  c.slli     t3, 31
                  ori        s10, t0, 872
                  mulh       a4, a3, s2
                  c.andi     s1, 26
                  c.slli     s7, 3
                  xori       sp, zero, 318
                  sra        gp, a2, t0
                  sltiu      s4, a4, -817
                  rem        t0, tp, a6
                  remu       t3, a4, t1
                  c.slli     t5, 27
                  c.li       s11, 31
                  and        a5, a1, t3
                  c.and      s1, a5
                  c.addi     s9, 15
                  div        a1, t5, s11
                  xor        s0, s4, t3
                  ori        a5, a4, -802
                  c.addi4spn a0, sp, 192
                  xor        s1, t0, ra
                  c.srli     a0, 27
                  srli       tp, a7, 2
                  c.andi     a0, -1
                  mulhu      s4, s1, t2
                  c.nop
                  div        t1, gp, s8
                  and        zero, s3, a5
                  c.mv       s1, t3
                  c.addi4spn a4, sp, 336
                  addi       s1, a5, -90
                  sll        s9, s9, ra
                  lui        t2, 40422
                  ori        t2, s6, -278
                  xori       s9, a4, -909
                  c.xor      a5, a1
                  lui        t5, 518707
                  c.mv       s11, a2
                  sltu       zero, s1, s5
                  c.addi     s3, -1
                  ori        a3, s11, -500
                  add        s8, s6, a6
                  auipc      t1, 823075
                  c.mv       t0, a0
                  andi       a2, t2, 416
                  remu       t2, zero, gp
                  divu       s3, a0, t0
                  remu       a5, gp, t0
                  c.add      s8, a3
                  nop
                  divu       s3, t4, a1
                  slli       t6, a0, 23
                  srli       s11, s1, 11
                  srli       t6, s11, 16
                  c.nop
                  c.srli     s1, 9
                  slt        sp, gp, t6
                  sub        s9, a0, tp
                  slt        a0, t4, s4
                  c.add      a0, t3
                  xori       t1, a5, -478
                  sll        s0, a1, gp
                  c.srai     a0, 30
                  mulh       t0, s4, s1
                  slli       a4, zero, 25
                  c.andi     a0, 8
                  c.xor      a2, a3
                  or         gp, s10, t5
                  c.addi4spn a2, sp, 608
                  sra        sp, s0, s11
                  c.or       a5, a5
                  div        a1, s4, s11
                  srli       s3, ra, 2
                  xori       s4, s9, -745
                  c.and      a3, a2
                  sll        s4, a2, s5
                  xori       t6, t4, 236
                  srl        s3, a1, s3
                  andi       zero, s10, 738
                  sltu       s8, a5, a6
                  nop
                  c.addi4spn a1, sp, 640
                  slt        gp, t6, t2
                  sub        gp, t5, s11
                  add        a6, a1, gp
                  auipc      s5, 953365
                  slti       s8, a7, -724
                  or         s8, t3, a1
                  c.add      t2, s3
                  c.addi     s1, -1
                  sub        s10, s1, s8
                  nop
                  add        s4, t4, s7
                  c.andi     a5, -1
                  srl        s11, a3, ra
                  remu       tp, s5, t1
                  c.addi     s5, 3
                  c.addi16sp sp, -16
                  c.or       a5, a0
                  and        s1, s2, s3
                  addi       a0, gp, -828
                  c.srai     a4, 14
                  or         sp, zero, a1
                  divu       s0, s10, a0
                  remu       t3, s1, s0
                  ori        s1, ra, -236
                  c.sub      a2, a1
                  sll        a6, zero, ra
                  mul        sp, t1, t3
                  srl        a3, gp, t3
                  ori        a3, a3, -560
                  c.lui      t5, 16
                  divu       a2, s9, s7
                  addi       sp, s2, -129
                  c.andi     a0, -1
                  c.and      s0, a3
                  xor        zero, s11, s11
                  c.srai     s1, 11
                  srai       a2, a1, 25
                  add        s10, s7, s0
                  slli       t6, t5, 1
                  add        a5, s10, sp
                  div        a4, t0, s3
                  add        a0, s11, a3
                  srl        s7, ra, zero
                  c.srli     a1, 21
                  andi       s1, t2, -790
                  c.and      a5, a0
                  ori        a1, s5, 608
                  ori        t0, s11, -260
                  lui        s8, 1005824
                  nop
                  c.addi     a5, 12
                  slli       s8, t6, 15
                  c.or       a3, a1
                  sltiu      a2, a2, 487
                  c.addi     t6, 5
                  srl        a3, s2, s6
                  nop
                  srli       a1, s5, 7
                  auipc      a2, 345802
                  ori        a5, t0, 915
                  slti       a0, a2, 225
                  c.mv       s8, a3
                  c.and      a0, a1
                  auipc      s3, 202767
                  div        s0, zero, sp
                  srl        t1, a2, t3
                  c.lui      t1, 10
                  slt        a3, gp, t0
                  srl        a3, t0, a6
                  c.xor      a0, a1
                  add        t2, s2, s4
                  c.srli     a5, 27
                  srl        a2, a1, a2
                  andi       t5, a1, -394
                  c.nop
                  srai       t3, s6, 24
                  c.sub      a4, a1
                  c.andi     s1, -1
                  mul        s11, ra, a6
                  c.or       s0, s1
                  srai       gp, s1, 2
                  remu       s1, gp, s8
                  mulh       s11, a5, s4
                  ori        s9, tp, -113
                  sll        s10, s1, s10
                  srl        s3, ra, a2
                  sub        a5, a6, s2
                  sub        a6, a6, s9
                  c.lui      t2, 23
                  slli       zero, t4, 23
                  or         s6, s9, t6
                  c.and      a5, s1
                  andi       t3, s6, 802
                  c.slli     t3, 31
                  add        s10, a0, s2
                  c.xor      a3, s1
                  or         s0, t6, gp
                  sltiu      t5, s0, 701
                  c.addi16sp sp, 208
                  c.addi     ra, -1
                  c.xor      a3, a1
                  c.addi4spn a1, sp, 480
                  c.addi4spn a1, sp, 528
                  remu       t0, t3, s10
                  c.andi     a2, -1
                  xori       s1, s2, -145
                  addi       a1, t3, 513
                  div        a4, s5, s9
                  slti       zero, t2, -36
                  c.slli     t1, 25
                  or         s5, s11, tp
                  nop
                  mulhsu     a0, s6, t3
                  auipc      a6, 578749
                  mulhsu     a3, a3, s6
                  srai       s0, tp, 19
                  srai       a6, s2, 8
                  ori        a0, s9, -745
                  xori       s1, gp, 362
                  c.addi16sp sp, -16
                  c.xor      a3, s0
                  c.or       a4, a2
                  sra        t6, t4, s8
                  mul        t3, tp, a0
                  sub        t3, t2, s8
                  srli       t6, s0, 21
                  c.or       s0, s1
                  mul        gp, a3, a2
                  andi       a5, s10, 36
                  auipc      s3, 92752
                  add        t5, s11, s4
                  remu       s1, t3, s10
                  c.and      s0, a5
                  srai       s8, s6, 4
                  remu       zero, t3, a4
                  div        t1, s10, a0
                  c.and      a2, a5
                  c.xor      s1, a5
                  or         s7, gp, a6
                  and        a1, a4, t2
                  c.add      t0, s6
                  c.add      sp, s0
                  mulh       a1, a3, zero
                  sll        s8, t6, s3
                  c.or       a3, a4
                  c.slli     s7, 17
                  srai       t0, s2, 12
                  c.addi4spn a4, sp, 528
                  auipc      tp, 465092
                  c.addi4spn a0, sp, 816
                  mulhsu     a1, t6, t4
                  c.and      a0, a2
                  addi       tp, a0, 193
                  auipc      a2, 112744
                  sll        a0, t1, s2
                  c.addi4spn a4, sp, 272
                  mulhu      t6, s4, a5
                  xor        s5, t6, t3
                  c.xor      a5, a1
                  c.lui      a5, 12
                  c.or       a5, s0
                  rem        a5, s4, s2
                  slt        s9, a5, t4
                  addi       t2, a5, 31
                  remu       t6, a1, s8
                  slti       a5, s10, 452
                  ori        zero, a3, -310
                  and        t5, s11, a7
                  nop
                  ori        s6, t5, -475
                  srl        zero, gp, a0
                  c.li       t2, -1
                  c.addi     t3, 27
                  ori        s3, a1, -965
                  sltiu      s4, s7, -656
                  slt        s3, s0, a7
                  sltu       a0, t6, t5
                  xor        s11, s0, a7
                  c.addi     t6, -1
                  mulhsu     s6, tp, t3
                  andi       a1, ra, -710
                  and        a6, zero, s2
                  andi       s9, s9, -790
                  slli       s8, t6, 15
                  c.sub      s0, s1
                  mulhsu     t5, t0, ra
                  nop
                  c.sub      s1, a3
                  c.nop
                  c.nop
                  slli       ra, s1, 21
                  add        s8, a4, s8
                  c.addi4spn s1, sp, 576
                  slt        t0, t2, s10
                  ori        s7, s5, 656
                  slt        a5, a6, t2
                  c.add      a1, s11
                  div        s7, sp, s6
                  c.addi4spn a1, sp, 336
                  sub        s7, s10, s9
                  c.andi     a0, 21
                  remu       a2, t3, a6
                  c.sub      a0, a5
                  andi       s7, a4, -383
                  srai       s1, s2, 29
                  c.addi     t5, -1
                  nop
                  c.li       gp, 2
                  slti       a2, s10, -13
                  c.slli     s11, 1
                  or         t2, tp, t0
                  c.add      s8, t4
                  c.li       s8, 12
                  andi       s8, s4, -484
                  slt        s7, s2, gp
                  div        sp, ra, s0
                  c.add      s11, a5
                  remu       s7, sp, t6
                  lui        a1, 800504
                  c.lui      a5, 14
                  remu       t0, s8, t1
                  c.or       s0, a3
                  sltiu      s6, zero, -981
                  c.andi     s1, 21
                  ori        t0, sp, -293
                  andi       t0, ra, -783
                  mulh       t2, s5, sp
                  c.addi     s9, -1
                  addi       s8, s2, 348
                  c.addi     s10, 31
                  c.or       a2, a1
                  lui        zero, 919234
                  slt        zero, sp, s10
                  sra        a0, s8, a7
                  c.sub      a0, a0
                  auipc      t5, 334806
                  divu       gp, t4, a1
                  srai       gp, t1, 1
                  c.and      a3, a3
                  c.srli     a4, 8
                  c.sub      s0, s0
                  sub        sp, a0, a6
                  rem        s11, s0, s11
                  c.srai     a1, 16
                  sub        zero, zero, a6
                  auipc      s8, 401617
                  slti       a4, s11, -650
                  mulh       s8, a7, a6
                  xori       t5, s9, 154
                  mulh       s3, a7, s5
                  c.andi     a1, -1
                  lui        a5, 137436
                  sltiu      a2, a6, 534
                  c.srai     a1, 17
                  sltu       s4, t3, gp
                  divu       s3, s10, ra
                  mul        s9, t0, ra
                  c.lui      a2, 8
                  divu       gp, s11, ra
                  c.addi16sp sp, 480
                  xor        a1, sp, s10
                  srli       ra, t1, 19
                  c.lui      a2, 13
                  c.add      s7, a0
                  sltu       s3, ra, s11
                  mulh       s7, t2, s3
                  sra        s7, s6, t2
                  c.addi16sp sp, 432
                  c.nop
                  slt        zero, tp, s2
                  slti       t3, s3, 960
                  andi       s4, s7, 682
                  or         s0, ra, tp
                  xor        a1, a3, s6
                  srli       gp, s4, 14
                  mulh       s10, s3, zero
                  div        a6, a1, a1
                  c.xor      s1, s0
                  add        zero, t2, s1
                  and        t3, t2, tp
                  sltiu      s9, a4, 909
                  c.lui      a0, 18
                  sra        s1, a1, s6
                  c.xor      s0, a3
                  c.and      a3, a4
                  sll        a3, s8, a5
                  addi       a6, t0, -656
                  srli       a6, sp, 4
                  slti       s6, t2, 806
                  sll        s8, a7, t1
                  sub        s6, tp, tp
                  c.addi4spn a5, sp, 416
                  c.addi     s5, 26
                  mulhsu     a6, s6, t1
                  c.slli     s7, 26
                  c.addi     s1, 16
                  c.or       a2, s1
                  c.nop
                  c.andi     a4, -1
                  srl        t0, a7, t3
                  c.addi4spn s0, sp, 656
                  ori        s8, t1, -263
                  mulhsu     ra, s0, s8
                  auipc      t5, 292446
                  c.or       a0, s1
                  srli       zero, a0, 7
                  c.add      ra, t1
                  c.li       t1, 26
                  sll        a1, t5, a0
                  srli       s6, s8, 11
                  div        a6, sp, s0
                  c.addi4spn s1, sp, 32
                  auipc      gp, 437486
                  c.li       s1, -1
                  c.mv       a6, a6
                  or         t3, t3, a6
                  slt        s3, a1, a4
                  slt        s3, a2, a1
                  c.addi16sp sp, -16
                  addi       ra, t2, -50
                  and        t2, a3, s10
                  div        zero, ra, s0
                  slti       tp, t1, -453
                  rem        s1, s7, s6
                  c.addi16sp sp, 336
                  c.or       a0, a2
                  sltiu      t3, s8, 545
                  divu       s0, a5, s11
                  divu       t5, zero, t3
                  nop
                  add        s10, zero, s9
                  c.and      s0, a1
                  mulhsu     s1, s9, a3
                  c.addi     t3, -1
                  sltiu      ra, a6, -649
                  sll        s7, ra, gp
                  sll        t6, a7, a0
                  addi       t0, t2, 135
                  add        ra, t0, s7
                  andi       s3, a6, -305
                  c.slli     a5, 2
                  c.xor      a5, a2
                  c.addi     t5, 3
                  slt        t5, s2, zero
                  lui        s1, 418844
                  mul        t5, ra, a3
                  or         a6, a0, t0
                  sltiu      zero, zero, 613
                  rem        a4, a1, ra
                  c.or       a0, a2
                  c.addi4spn a3, sp, 672
                  c.addi16sp sp, -16
                  srl        s4, gp, s7
                  ori        a2, a7, 641
                  c.slli     gp, 15
                  mulh       gp, s4, t6
                  c.nop
                  c.addi4spn a5, sp, 128
                  c.or       s1, a2
                  andi       s10, sp, 300
                  c.slli     sp, 10
                  auipc      zero, 241314
                  c.add      t5, a4
                  and        t0, a5, gp
                  c.li       t0, 12
                  sub        a3, s9, a7
                  sra        t0, a2, a5
                  c.sub      s1, a5
                  mulh       a3, s7, t6
                  nop
                  c.addi16sp sp, -16
                  andi       s3, zero, -730
                  div        gp, s6, t0
                  auipc      s10, 495654
                  c.addi4spn a4, sp, 240
                  mulhu      s4, s7, t6
                  addi       s6, t0, 951
                  or         a2, a5, t1
                  xori       s11, s3, 462
                  slli       tp, t0, 0
                  c.li       tp, -1
                  c.add      s0, s6
                  divu       s7, s9, a4
                  c.srli     a0, 6
                  c.li       s7, -1
                  ori        a6, a7, -838
                  c.mv       t2, s4
                  and        s3, t0, a3
                  mulhu      gp, s4, s7
                  srai       s4, t0, 22
                  or         t1, ra, s2
                  c.li       s9, -1
                  mulh       a5, a1, t4
                  c.srli     a5, 4
                  srai       s8, sp, 13
                  divu       s9, t1, s9
                  slli       s4, s7, 1
                  ori        a3, s1, -383
                  srl        t1, s4, t3
                  slti       s5, a6, 400
                  div        a4, s11, ra
                  c.and      a3, a0
                  sltu       a0, s9, s3
                  srli       a3, tp, 14
                  lui        s5, 1029450
                  xor        s0, a4, a4
                  sltu       t1, tp, ra
                  and        t5, s4, t6
                  c.addi     a6, 25
                  c.addi     s4, -1
                  auipc      s3, 464803
                  remu       s4, s11, a4
                  srai       s5, t6, 17
                  c.xor      a2, a4
                  divu       a2, sp, t6
                  c.or       a4, a4
                  or         a6, a4, s6
                  sltu       s0, tp, a2
                  c.addi16sp sp, -16
                  addi       a4, a4, 713
                  srli       s10, t4, 5
                  slt        t2, a0, s8
                  c.slli     s4, 25
                  andi       t6, a5, -337
                  slt        s6, a1, s1
                  c.addi4spn a4, sp, 896
                  c.srli     s1, 4
                  sll        a5, t3, gp
                  divu       ra, gp, s9
                  addi       t1, gp, 508
                  c.andi     s1, -1
                  or         s6, a1, a2
                  c.nop
                  mulhu      s0, zero, a5
                  xori       s3, t2, 202
                  c.or       a5, a2
                  xori       a4, ra, 479
                  c.or       s0, a2
                  mulhsu     tp, a7, s3
                  slti       gp, s4, 77
                  slti       s8, s11, -102
                  c.xor      s0, a4
                  sltu       t3, a5, ra
                  c.li       t3, -1
                  c.addi16sp sp, 144
                  or         gp, gp, s9
                  mulhsu     s8, ra, t4
                  rem        s7, s9, s5
                  c.srli     a4, 5
                  or         tp, s4, t6
                  srai       tp, sp, 27
                  or         s10, s4, a7
                  c.sub      a4, a4
                  c.addi     t1, -1
                  mulh       t5, t6, a4
                  slti       zero, s6, -754
                  xor        s6, s7, t5
                  c.lui      a5, 28
                  div        a3, a6, s4
                  and        gp, a5, ra
                  mulhu      t6, t6, s5
                  srl        s7, t4, t3
                  sll        s0, s4, a4
                  andi       t2, s7, -944
                  mulhsu     s9, a0, s8
                  slli       t0, s2, 29
                  c.mv       s1, gp
                  mul        sp, a0, tp
                  c.andi     a2, 2
                  c.nop
                  c.andi     a0, -1
                  addi       s7, t2, -125
                  srai       t6, s5, 21
                  slti       a1, s8, 795
                  mulhsu     gp, t2, t5
                  c.slli     t2, 26
                  remu       s8, a7, a1
                  c.addi     ra, -1
                  or         s10, t1, a6
                  mulh       zero, sp, a1
                  c.nop
                  c.srai     a4, 14
                  c.or       a0, a0
                  mul        s10, s9, t5
                  sltiu      t6, s1, 702
                  xor        s0, gp, t5
                  mul        s4, t1, ra
                  divu       s1, t0, a1
                  nop
                  mul        a5, t4, t4
                  c.slli     a3, 19
                  c.addi4spn a4, sp, 816
                  srai       zero, tp, 10
                  c.slli     s8, 18
                  add        s3, t5, s5
                  srl        a0, t4, s2
                  divu       tp, s0, a0
                  c.sub      a5, a3
                  c.addi4spn a4, sp, 304
                  c.srli     a5, 6
                  addi       s6, gp, -10
                  srli       sp, s4, 2
                  addi       t0, s7, -782
                  slli       t6, a4, 0
                  nop
                  c.li       s9, 27
                  c.addi4spn s0, sp, 624
                  srl        tp, s8, s6
                  c.and      a3, s1
                  c.or       a2, s0
                  srai       gp, a5, 5
                  xori       t0, a4, -137
                  li         s8, 0xffffffff #start riscv_int_numeric_corner_stream_37
                  li         t1, 0x69449c44
                  li         s6, 0x0
                  li         t6, 0x0
                  li         a3, 0xdd34a4a0
                  li         a5, 0xffffffff
                  li         sp, 0xffffffff
                  li         a6, 0x0
                  li         a1, 0xffffffff
                  li         tp, 0xad3b6681
                  add        a6, t1, s6
                  mulhu      s8, s8, a1
                  mulhsu     t1, s6, a3
                  nop
                  addi       sp, a3, 743
                  remu       a6, a1, s8
                  div        a5, t1, s8
                  auipc      t1, 705461
                  mulh       tp, s6, a3
                  rem        t1, a5, t1
                  mulhsu     a3, s6, t1
                  mul        t6, t6, t6
                  remu       s6, s8, a1
                  auipc      a3, 798819
                  add        a6, a1, a6
                  div        s8, t1, s8
                  lui        a6, 173741
                  mulhsu     sp, s6, tp
                  nop
                  mul        t1, t1, a5
                  div        s6, sp, tp
                  divu       a1, a5, sp
                  mulhu      t1, tp, tp
                  mulh       s6, a1, a6
                  mulh       s8, a6, s8
                  nop
                  nop #end riscv_int_numeric_corner_stream_37
                  lui        a6, 22867
                  c.and      s1, a3
                  c.mv       t3, a7
                  c.addi     t1, 30
                  c.addi16sp sp, 464
                  div        s7, s7, t6
                  c.or       a5, a4
                  div        a0, s7, t1
                  c.andi     s0, 10
                  remu       t3, s0, t2
                  mulhu      tp, a3, t6
                  ori        t3, t4, 674
                  div        s11, s1, s9
                  lui        t5, 346957
                  c.mv       a6, a5
                  c.and      a4, a2
                  c.addi16sp sp, -16
                  c.or       a4, s0
                  ori        a0, s11, 375
                  and        a2, s2, a4
                  mulhu      s3, s7, s1
                  c.lui      s3, 21
                  nop
                  c.slli     s11, 9
                  c.andi     a4, 18
                  mul        s1, a4, s10
                  addi       ra, s7, 576
                  xori       a0, s1, 479
                  c.mv       s8, s11
                  divu       s10, tp, s3
                  add        a4, a4, a3
                  divu       a3, t6, s2
                  nop
                  c.li       a6, -1
                  c.sub      a2, s1
                  xor        s6, s10, t0
                  or         a4, s0, s5
                  slt        a6, sp, s7
                  c.addi     t6, 23
                  andi       t2, a7, 667
                  mul        a6, s3, s3
                  remu       s9, s1, t1
                  and        zero, s11, t6
                  or         gp, s7, s3
                  lui        a2, 532349
                  c.lui      s7, 11
                  c.srli     s1, 11
                  sltu       sp, a7, t1
                  auipc      s5, 769613
                  lui        s4, 407670
                  rem        a5, s0, a6
                  c.add      a6, a1
                  div        s3, s6, s6
                  xori       s11, a5, -965
                  mulhsu     s7, s8, t6
                  c.li       a0, 12
                  c.addi4spn s0, sp, 32
                  c.sub      a0, a4
                  lui        s1, 440523
                  addi       s3, s2, -447
                  mulh       t6, s0, s7
                  remu       s0, t3, s11
                  addi       s9, a1, 759
                  auipc      s1, 850951
                  nop
                  mulhsu     s4, s9, sp
                  c.or       a5, a0
                  auipc      s4, 802057
                  c.sub      a4, s1
                  xori       sp, s0, 270
                  c.addi16sp sp, -16
                  slli       a4, t2, 5
                  c.sub      s0, a3
                  c.lui      s6, 2
                  slti       a2, t3, -977
                  and        a6, tp, tp
                  slti       a2, s0, 750
                  c.addi16sp sp, 128
                  remu       s9, s9, sp
                  c.xor      a0, a5
                  c.sub      a1, a1
                  xor        t5, s6, t6
                  xori       s11, s9, -159
                  c.nop
                  add        a1, s7, t1
                  c.li       s11, 13
                  c.mv       sp, gp
                  c.li       t5, 4
                  slli       zero, a5, 16
                  c.addi     s3, 28
                  xor        a5, t4, s6
                  c.nop
                  mulhsu     a1, s11, t0
                  sra        t0, a6, a5
                  c.lui      a4, 14
                  c.addi     s8, 10
                  sub        a5, gp, t4
                  mulhu      t3, s7, a4
                  auipc      sp, 219960
                  andi       s7, a6, -731
                  c.or       a1, a3
                  c.sub      a3, s1
                  srli       a6, s3, 2
                  c.lui      s5, 4
                  c.srai     a2, 28
                  xor        a5, s7, sp
                  sltu       sp, s0, s9
                  c.lui      t6, 10
                  xor        s5, a4, zero
                  srai       a0, a6, 14
                  c.srai     a5, 22
                  c.xor      a5, s1
                  c.add      s11, a2
                  remu       s7, s8, s7
                  srl        s5, t0, t0
                  c.mv       s3, a0
                  c.lui      t5, 28
                  slt        zero, a6, t6
                  sltu       t0, a6, a5
                  rem        t6, s2, t4
                  c.add      s0, s5
                  c.or       a3, s0
                  sll        a2, s11, t2
                  ori        ra, s4, -70
                  li         s1, 0x0 #start riscv_int_numeric_corner_stream_11
                  li         t1, 0xffffffff
                  li         s3, 0x80000000
                  li         t2, 0x0
                  li         s0, 0x80000000
                  li         a1, 0x28a67546
                  li         a3, 0x0
                  li         ra, 0x0
                  li         s7, 0x80000000
                  li         sp, 0x0
                  addi       a3, s3, 131
                  mulh       a3, ra, t1
                  auipc      s3, 732290
                  addi       s0, ra, -634
                  addi       s0, s1, 1018
                  nop
                  mulhsu     s1, t1, sp
                  lui        ra, 78158
                  mul        s0, ra, s3
                  add        a1, a3, a3
                  lui        t1, 392334
                  mulh       t2, s7, s3
                  auipc      ra, 508571
                  rem        a1, s1, s7
                  sub        ra, t2, s7
                  sub        sp, t2, a1
                  nop
                  divu       sp, ra, s3
                  divu       s1, sp, s7
                  mulhsu     s1, ra, sp
                  mul        sp, sp, a1 #end riscv_int_numeric_corner_stream_11
                  and        t5, s4, a5
                  sra        t1, t6, t4
                  c.mv       s7, t2
                  remu       sp, a0, t3
                  srl        a4, t3, a5
                  rem        s7, s1, s11
                  addi       s6, s5, -1011
                  slli       a6, s9, 24
                  sra        ra, s4, s6
                  divu       ra, s8, t4
                  c.nop
                  c.lui      t1, 18
                  auipc      sp, 1020287
                  ori        tp, a1, -844
                  sltu       t1, s5, s4
                  andi       zero, t5, 60
                  andi       s7, s7, 244
                  andi       a2, s4, -1019
                  mulhsu     a0, a1, a4
                  slli       t0, tp, 26
                  sll        s5, s9, s5
                  slli       s8, a1, 9
                  srai       s4, ra, 21
                  srai       s8, s1, 15
                  or         zero, t3, a3
                  c.lui      a2, 5
                  sll        s1, ra, s7
                  add        t2, t6, s9
                  c.add      s9, a6
                  nop
                  slt        s3, s3, s5
                  and        t3, s3, a4
                  c.addi4spn a3, sp, 560
                  srl        a1, s2, a3
                  c.addi4spn a2, sp, 912
                  srli       s1, s2, 17
                  addi       sp, a4, -272
                  srai       t2, s9, 14
                  auipc      gp, 416134
                  mulhu      a4, t0, s6
                  c.lui      tp, 24
                  ori        a5, sp, 727
                  srai       a1, s2, 15
                  li         sp, 0x0 #start riscv_int_numeric_corner_stream_14
                  li         s9, 0xffffffff
                  li         gp, 0xeff23cd7
                  li         t0, 0x0
                  li         t6, 0x80000000
                  li         a2, 0xffffffff
                  li         s5, 0x0
                  li         t1, 0x80000000
                  li         a5, 0x0
                  li         t3, 0xffffffff
                  mulhsu     a5, sp, t3
                  mulhsu     sp, s9, s5
                  mulhu      s5, t0, a2
                  nop
                  mulhu      sp, s9, s5
                  remu       t3, s9, s9
                  addi       t6, gp, 102
                  mulh       sp, a2, t1
                  div        a2, t6, sp
                  mulh       t3, t0, t3
                  add        t0, t1, s9
                  mul        sp, t6, t3
                  divu       s9, s9, s5
                  mulhu      gp, a2, gp
                  lui        gp, 674980
                  lui        s9, 387521
                  addi       a2, a5, -260
                  mulh       t1, t1, t0
                  mulhsu     s5, a2, a2
                  mul        t6, t6, s5
                  lui        a5, 509309
                  addi       a2, a2, 315
                  add        gp, t6, a2
                  rem        gp, t6, a5
                  mulhsu     s5, t1, sp
                  lui        a2, 243214
                  addi       t0, a2, 120
                  nop
                  remu       s9, t1, a5 #end riscv_int_numeric_corner_stream_14
                  c.or       a0, a3
                  c.xor      a2, a3
                  sltiu      t1, sp, -245
                  c.nop
                  c.addi16sp sp, -16
                  c.lui      s6, 7
                  srl        s10, t1, s5
                  sll        s10, s4, t2
                  sra        s7, s8, a4
                  mul        tp, a4, s10
                  andi       s11, s6, 484
                  and        t3, tp, s4
                  lui        s5, 761289
                  sll        s10, a0, a7
                  c.andi     a4, 19
                  sub        sp, tp, sp
                  xori       ra, s6, -493
                  c.xor      a1, a1
                  c.srli     a0, 25
                  srl        a5, s1, t2
                  c.srai     a1, 15
                  srl        a6, a1, s10
                  mulh       zero, a3, s0
                  sltu       a3, s5, s9
                  c.xor      a0, a3
                  c.srli     a0, 24
                  rem        a2, zero, ra
                  auipc      gp, 154741
                  sll        s4, t1, a0
                  mulhu      t3, t6, t0
                  c.nop
                  mulhu      a3, zero, tp
                  srai       s6, sp, 6
                  xor        s8, s2, a0
                  c.mv       s10, s4
                  c.li       s8, 16
                  c.slli     t5, 4
                  xor        s1, ra, ra
                  add        a2, a7, t5
                  slli       s8, t2, 27
                  xor        a0, s0, gp
                  c.lui      t6, 8
                  c.xor      s1, a3
                  add        ra, a6, a4
                  sra        s7, zero, s11
                  mul        s6, s2, t0
                  xor        a4, a1, s3
                  and        t1, t4, a6
                  addi       t6, a4, 475
                  c.or       a4, a3
                  rem        s8, t2, a4
                  or         a2, s6, s3
                  andi       s10, t1, -455
                  slti       a1, a4, -577
                  sltiu      s10, s11, 101
                  ori        s11, a4, -921
                  mulhsu     t3, tp, t2
                  xor        s11, s0, s10
                  xor        s9, s4, a0
                  sll        ra, a0, s0
                  slti       a4, sp, 506
                  sub        a2, ra, s6
                  mul        s10, a3, a7
                  and        t0, tp, s0
                  c.addi4spn a5, sp, 192
                  c.addi     t0, -1
                  and        a4, s11, s10
                  c.or       a3, a3
                  mulhu      s5, s2, s7
                  c.addi4spn s1, sp, 384
                  auipc      zero, 483978
                  c.sub      a0, a1
                  lui        a0, 984284
                  c.andi     a2, -1
                  add        ra, a0, tp
                  sra        a2, a0, s8
                  c.li       s10, -1
                  addi       t1, t3, -132
                  mul        a3, s6, s7
                  c.addi     s1, -1
                  c.srli     a4, 3
                  c.srai     s0, 17
                  c.srli     s1, 14
                  auipc      t1, 594048
                  addi       s5, a7, -713
                  srl        s4, t4, s1
                  xori       a6, t6, -34
                  slli       s0, t1, 11
                  xor        s4, s3, t2
                  srli       s5, s2, 0
                  xori       s8, zero, -147
                  sub        a4, t5, ra
                  c.addi16sp sp, -16
                  c.andi     s1, -1
                  rem        t1, s6, a2
                  slli       s4, s5, 19
                  mul        s4, t5, s8
                  mulh       a4, t2, a4
                  c.srai     a3, 22
                  c.sub      s0, a1
                  and        sp, t6, gp
                  and        a4, s6, s4
                  c.add      ra, s7
                  sra        zero, s8, ra
                  c.addi     t1, -1
                  andi       t5, tp, -961
                  c.sub      a4, a1
                  and        a5, t5, s0
                  srai       a1, a0, 9
                  auipc      s1, 300753
                  sra        s5, t6, a4
                  srl        s1, s0, a6
                  mulhsu     sp, s9, s2
                  and        zero, t5, s1
                  or         a1, s11, t1
                  auipc      s5, 333118
                  c.srli     a4, 19
                  divu       s7, t1, t4
                  c.slli     a6, 13
                  sltu       s4, t3, s0
                  slt        s4, a7, t4
                  rem        t5, a1, ra
                  c.andi     a4, -1
                  auipc      gp, 450952
                  rem        t2, s4, a6
                  sub        t2, s4, a5
                  c.addi     t1, 31
                  c.addi     a4, -1
                  div        s7, zero, sp
                  sub        s3, t4, s10
                  c.srai     a3, 28
                  c.li       a4, 21
                  ori        gp, a0, 353
                  mulhu      a2, s10, a6
                  srli       a1, s2, 26
                  remu       s9, a1, s1
                  c.addi     s4, -1
                  or         t5, s5, a2
                  mul        a1, t6, a0
                  c.addi4spn a5, sp, 944
                  c.andi     a0, 25
                  rem        s5, s7, s0
                  c.addi     tp, -1
                  c.and      a2, a3
                  c.nop
                  xori       s10, a4, -224
                  ori        gp, tp, 985
                  divu       s5, t1, gp
                  c.sub      s0, a3
                  c.sub      s0, a5
                  xori       sp, ra, -92
                  divu       a6, s3, s7
                  c.mv       s1, s2
                  mulhu      s8, s9, s11
                  div        s10, s3, t5
                  slti       t3, t5, 987
                  c.nop
                  andi       s6, s5, -496
                  or         a4, t5, a7
                  c.nop
                  mulh       t2, a7, s9
                  sll        s7, a1, s0
                  srai       a3, a4, 7
                  c.srli     a3, 24
                  add        t5, ra, ra
                  andi       s6, t4, -131
                  remu       sp, t2, a6
                  divu       s4, s1, s6
                  andi       a2, t2, 1023
                  c.srli     s1, 5
                  c.addi16sp sp, 480
                  c.srai     a0, 15
                  sltu       s0, s6, t0
                  c.andi     a5, -1
                  c.nop
                  c.srli     a5, 22
                  c.addi16sp sp, -16
                  c.addi4spn a2, sp, 448
                  srai       a3, t6, 4
                  addi       sp, t0, -466
                  c.add      t3, t4
                  sltiu      sp, a0, -1018
                  mul        gp, a1, sp
                  sltu       t0, t2, s5
                  auipc      a3, 973052
                  slti       zero, a2, -441
                  c.addi     a1, 30
                  lui        s1, 332325
                  c.slli     s10, 10
                  sltu       s7, t1, t2
                  sub        sp, s1, tp
                  rem        t0, s3, t4
                  c.addi4spn a3, sp, 384
                  addi       sp, a5, -773
                  and        s10, a1, s8
                  c.add      a6, s7
                  addi       s6, s1, -289
                  sll        a4, a2, s6
                  slli       s10, s11, 14
                  divu       a1, s6, s4
                  remu       ra, s6, t2
                  xor        s5, sp, s6
                  addi       t5, t4, 455
                  divu       s1, s10, sp
                  auipc      a3, 425008
                  srai       s8, s9, 29
                  rem        t0, s1, tp
                  c.nop
                  sub        sp, a6, t6
                  c.lui      s3, 27
                  c.mv       s8, a0
                  andi       zero, a6, -933
                  slt        t0, a6, tp
                  c.li       s5, 9
                  slti       s0, s2, -355
                  sltu       s11, a4, s7
                  c.and      s0, a0
                  c.andi     a1, -1
                  sltiu      s0, s3, 208
                  c.lui      s7, 28
                  c.li       s8, -1
                  c.addi     s9, -1
                  andi       a2, a1, -215
                  c.add      s7, s3
                  slli       a5, t5, 15
                  srli       a3, s8, 31
                  sra        t5, zero, sp
                  sra        s0, s2, s3
                  auipc      t0, 815093
                  mulhu      a6, zero, t3
                  add        s1, t6, s6
                  xori       t5, a4, -367
                  and        a3, s1, tp
                  mulhsu     a0, a0, t2
                  slli       t0, s3, 15
                  or         s5, a3, t1
                  srl        s0, s9, s11
                  c.addi4spn a1, sp, 800
                  remu       s8, a1, s11
                  c.slli     t5, 25
                  or         s3, a7, s11
                  srl        s11, t4, t3
                  sll        s6, a2, t1
                  and        t1, a6, a7
                  slt        s10, s5, sp
                  sub        gp, sp, tp
                  sltu       t6, a7, a4
                  c.addi4spn a4, sp, 304
                  c.addi16sp sp, -16
                  andi       s8, tp, 900
                  c.srai     a3, 3
                  divu       s8, a2, s10
                  auipc      s0, 181518
                  c.nop
                  c.nop
                  and        s6, t6, a7
                  xori       s5, ra, 243
                  remu       s0, s10, zero
                  c.addi4spn a1, sp, 480
                  auipc      a5, 882537
                  c.addi16sp sp, -16
                  divu       a0, s8, s11
                  xori       s9, s4, -424
                  c.slli     t0, 14
                  c.addi4spn a5, sp, 448
                  div        a6, t6, s6
                  sub        t0, s4, a3
                  mulhsu     s6, s5, s5
                  c.xor      a2, a4
                  mulhsu     s11, a1, s11
                  c.srli     a4, 25
                  srli       s10, tp, 24
                  c.andi     a4, -1
                  slti       s11, s1, 337
                  c.nop
                  srl        s7, t2, a3
                  slti       zero, t5, 615
                  andi       a3, t6, -852
                  c.xor      a1, a5
                  mulhsu     t6, t6, t6
                  slti       tp, t1, 884
                  slt        s3, s2, s8
                  c.addi     t3, 25
                  or         t2, s10, s0
                  mulh       tp, s5, a7
                  remu       tp, a5, ra
                  mulh       s7, a7, t1
                  c.slli     s0, 13
                  auipc      a1, 711609
                  mul        a4, ra, s3
                  c.srli     a3, 25
                  c.addi4spn a4, sp, 16
                  mulh       a0, a6, s0
                  c.add      a0, a1
                  c.li       a3, 10
                  c.sub      a2, a1
                  c.srli     s1, 11
                  sll        a5, gp, t6
                  auipc      sp, 519324
                  c.slli     s4, 15
                  c.li       s10, 12
                  c.addi16sp sp, 464
                  c.addi16sp sp, -16
                  div        t3, gp, t1
                  c.and      s1, a1
                  c.nop
                  c.sub      a3, s1
                  slti       t5, a4, -679
                  andi       zero, s7, -331
                  sub        s8, a3, s5
                  c.sub      a0, s1
                  j test_done

#Start: Extracted from riscv_compliance_tests/riscv_test.h
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

                  li a0, test_ret_val
                  lw a1, test_results /* report result */
                  sw a1,0(a0)

                  wfi  /* we are done */
#End: Extracted from riscv_compliance_tests/riscv_test.h

write_tohost:     
                  sw gp, tohost, t5

_exit:            
                  j write_tohost

init_machine_mode:
                  li x13, 0x1800
                  csrw 0x300, x13 # MSTATUS
                  li x13, 0x0
                  csrw 0x304, x13 # MIE
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
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_2:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_3:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_4:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_5:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_6:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_7:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_8:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_9:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_10:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_11:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_12:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_13:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_14:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_15:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_16:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_17:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_18:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_19:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_20:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_21:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_22:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_23:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_24:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_25:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_26:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_27:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_28:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_29:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_30:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_31:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x342 # MCAUSE
                  srli x13, x13, 0x1f
                  beqz x13, 1f
                  j mmode_intr_handler
                  1: j test_done

.align           8
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
                  j mmode_intr_vector_16
                  j mmode_intr_vector_17
                  j mmode_intr_vector_18
                  j mmode_intr_vector_19
                  j mmode_intr_vector_20
                  j mmode_intr_vector_21
                  j mmode_intr_vector_22
                  j mmode_intr_vector_23
                  j mmode_intr_vector_24
                  j mmode_intr_vector_25
                  j mmode_intr_vector_26
                  j mmode_intr_vector_27
                  j mmode_intr_vector_28
                  j mmode_intr_vector_29
                  j mmode_intr_vector_30
                  j mmode_intr_vector_31
                  .option rvc;

mmode_exception_handler:
                  csrrw x29, 0x340, x29
                  add x29, x17, zero
                  1: addi x29, x29, -124
                  sw  x1, 4(x29)
                  sw  x2, 8(x29)
                  sw  x3, 12(x29)
                  sw  x4, 16(x29)
                  sw  x5, 20(x29)
                  sw  x6, 24(x29)
                  sw  x7, 28(x29)
                  sw  x8, 32(x29)
                  sw  x9, 36(x29)
                  sw  x10, 40(x29)
                  sw  x11, 44(x29)
                  sw  x12, 48(x29)
                  sw  x13, 52(x29)
                  sw  x14, 56(x29)
                  sw  x15, 60(x29)
                  sw  x16, 64(x29)
                  sw  x17, 68(x29)
                  sw  x18, 72(x29)
                  sw  x19, 76(x29)
                  sw  x20, 80(x29)
                  sw  x21, 84(x29)
                  sw  x22, 88(x29)
                  sw  x23, 92(x29)
                  sw  x24, 96(x29)
                  sw  x25, 100(x29)
                  sw  x26, 104(x29)
                  sw  x27, 108(x29)
                  sw  x28, 112(x29)
                  sw  x29, 116(x29)
                  sw  x30, 120(x29)
                  sw  x31, 124(x29)
                  csrr x13, 0x341 # MEPC
                  csrr x13, 0x342 # MCAUSE
                  li x6, 0x3 # BREAKPOINT
                  beq x13, x6, ebreak_handler
                  li x6, 0x8 # ECALL_UMODE
                  beq x13, x6, ecall_handler
                  li x6, 0x9 # ECALL_SMODE
                  beq x13, x6, ecall_handler
                  li x6, 0xb # ECALL_MMODE
                  beq x13, x6, ecall_handler
                  li x6, 0x1
                  beq x13, x6, instr_fault_handler
                  li x6, 0x5
                  beq x13, x6, load_fault_handler
                  li x6, 0x7
                  beq x13, x6, store_fault_handler
                  li x6, 0xc
                  beq x13, x6, pt_fault_handler
                  li x6, 0xd
                  beq x13, x6, pt_fault_handler
                  li x6, 0xf
                  beq x13, x6, pt_fault_handler
                  li x6, 0x2 # ILLEGAL_INSTRUCTION
                  beq x13, x6, illegal_instr_handler
                  csrr x6, 0x343 # MTVAL
                  1: jal x1, test_done 

ecall_handler:    
                  la x13, _start
                  sw x0, 0(x13)
                  sw x1, 4(x13)
                  sw x2, 8(x13)
                  sw x3, 12(x13)
                  sw x4, 16(x13)
                  sw x5, 20(x13)
                  sw x6, 24(x13)
                  sw x7, 28(x13)
                  sw x8, 32(x13)
                  sw x9, 36(x13)
                  sw x10, 40(x13)
                  sw x11, 44(x13)
                  sw x12, 48(x13)
                  sw x13, 52(x13)
                  sw x14, 56(x13)
                  sw x15, 60(x13)
                  sw x16, 64(x13)
                  sw x17, 68(x13)
                  sw x18, 72(x13)
                  sw x19, 76(x13)
                  sw x20, 80(x13)
                  sw x21, 84(x13)
                  sw x22, 88(x13)
                  sw x23, 92(x13)
                  sw x24, 96(x13)
                  sw x25, 100(x13)
                  sw x26, 104(x13)
                  sw x27, 108(x13)
                  sw x28, 112(x13)
                  sw x29, 116(x13)
                  sw x30, 120(x13)
                  sw x31, 124(x13)
                  j write_tohost
instr_fault_handler:
                  li x13, 0
                  csrw 0x340, x13
                  li x28, 0
                  0: csrr x13, 0x340
                  mv x18, x13
                  li x18, 0
                  beq x13, x18, 1f
                  1: csrr x6, 0x3b0
                  csrr x5, 0x3a0
                  j 17f
                  17: li x4, 4
                  csrr x13, 0x340
                  slli x13, x13, 30
                  srli x13, x13, 30
                  sub x18, x4, x13
                  addi x18, x18, -1
                  slli x18, x18, 3
                  sll x4, x5, x18
                  slli x13, x13, 3
                  add x18, x18, x13
                  srl x4, x4, x18
                  slli x18, x4, 27
                  srli x18, x18, 30
                  beqz x18, 20f
                  li x13, 1
                  beq x18, x13, 21f
                  li x13, 2
                  beq x18, x13, 25f
                  li x13, 3
                  beq x18, x13, 27f
                  j test_done
                  18: csrr x13, 0x340
                  mv x28, x6
                  addi x13, x13, 1
                  csrw 0x340, x13
                  li x6, 1
                  ble x6, x13, 19f
                  j 0b
                  19: j test_done
                  20: j 18b
                  21: csrr x13, 0x340
                  csrr x18, 0x343
                  srli x18, x18, 2
                  bnez x13, 22f
                  bltz x18, 18b
                  j 23f
                  22: bgtu x28, x18, 18b
                  23: bleu x6, x18, 18b
                  andi x18, x4, 128
                  beqz x18, 24f
                  j test_done
                  24: j 29f
                  25: csrr x13, 0x343
                  srli x13, x13, 2
                  slli x18, x6, 2
                  srli x18, x18, 2
                  bne x13, x18, 18b
                  andi x18, x4, 128
                  beqz x18, 26f
                  j test_done
                  26: j 29f
                  27: csrr x13, 0x343
                  srli x13, x13, 2
                  srli x13, x13, 0
                  slli x13, x13, 0
                  slli x18, x6, 2
                  srli x18, x18, 2
                  srli x18, x18, 0
                  slli x18, x18, 0
                  bne x13, x18, 18b
                  andi x18, x4, 128
                  beqz x18, 29f
                  j test_done
                  28: j 29f
                  29: ori x4, x4, 4
                  csrr x13, 0x340
                  li x18, 30
                  sll x13, x13, x18
                  srl x13, x13, x18
                  slli x18, x13, 3
                  sll x4, x4, x18
                  or x5, x5, x4
                  csrr x13, 0x340
                  srli x13, x13, 2
                  beqz x13, 30f
                  li x18, 1
                  beq x13, x18, 31f
                  li x18, 2
                  beq x13, x18, 32f
                  li x18, 3
                  beq x13, x18, 33f
                  30: csrw 0x3a0, x5
                  j 34f
                  31: csrw 0x3a1, x5
                  j 34f
                  32: csrw 0x3a2, x5
                  j 34f
                  33: csrw 0x3a3, x5
                  34: nop
                  lw  x1, 4(x29)
                  lw  x2, 8(x29)
                  lw  x3, 12(x29)
                  lw  x4, 16(x29)
                  lw  x5, 20(x29)
                  lw  x6, 24(x29)
                  lw  x7, 28(x29)
                  lw  x8, 32(x29)
                  lw  x9, 36(x29)
                  lw  x10, 40(x29)
                  lw  x11, 44(x29)
                  lw  x12, 48(x29)
                  lw  x13, 52(x29)
                  lw  x14, 56(x29)
                  lw  x15, 60(x29)
                  lw  x16, 64(x29)
                  lw  x17, 68(x29)
                  lw  x18, 72(x29)
                  lw  x19, 76(x29)
                  lw  x20, 80(x29)
                  lw  x21, 84(x29)
                  lw  x22, 88(x29)
                  lw  x23, 92(x29)
                  lw  x24, 96(x29)
                  lw  x25, 100(x29)
                  lw  x26, 104(x29)
                  lw  x27, 108(x29)
                  lw  x28, 112(x29)
                  lw  x29, 116(x29)
                  lw  x30, 120(x29)
                  lw  x31, 124(x29)
                  addi x29, x29, 124
                  add x17, x29, zero
                  csrrw x29, 0x340, x29
                  mret

load_fault_handler:
                  li x13, 0
                  csrw 0x340, x13
                  li x28, 0
                  0: csrr x13, 0x340
                  mv x18, x13
                  li x18, 0
                  beq x13, x18, 1f
                  1: csrr x6, 0x3b0
                  csrr x5, 0x3a0
                  j 17f
                  17: li x4, 4
                  csrr x13, 0x340
                  slli x13, x13, 30
                  srli x13, x13, 30
                  sub x18, x4, x13
                  addi x18, x18, -1
                  slli x18, x18, 3
                  sll x4, x5, x18
                  slli x13, x13, 3
                  add x18, x18, x13
                  srl x4, x4, x18
                  slli x18, x4, 27
                  srli x18, x18, 30
                  beqz x18, 20f
                  li x13, 1
                  beq x18, x13, 21f
                  li x13, 2
                  beq x18, x13, 25f
                  li x13, 3
                  beq x18, x13, 27f
                  j test_done
                  18: csrr x13, 0x340
                  mv x28, x6
                  addi x13, x13, 1
                  csrw 0x340, x13
                  li x6, 1
                  ble x6, x13, 19f
                  j 0b
                  19: j test_done
                  20: j 18b
                  21: csrr x13, 0x340
                  csrr x18, 0x343
                  srli x18, x18, 2
                  bnez x13, 22f
                  bltz x18, 18b
                  j 23f
                  22: bgtu x28, x18, 18b
                  23: bleu x6, x18, 18b
                  andi x18, x4, 128
                  beqz x18, 24f
                  j test_done
                  24: j 29f
                  25: csrr x13, 0x343
                  srli x13, x13, 2
                  slli x18, x6, 2
                  srli x18, x18, 2
                  bne x13, x18, 18b
                  andi x18, x4, 128
                  beqz x18, 26f
                  j test_done
                  26: j 29f
                  27: csrr x13, 0x343
                  srli x13, x13, 2
                  srli x13, x13, 0
                  slli x13, x13, 0
                  slli x18, x6, 2
                  srli x18, x18, 2
                  srli x18, x18, 0
                  slli x18, x18, 0
                  bne x13, x18, 18b
                  andi x18, x4, 128
                  beqz x18, 29f
                  j test_done
                  28: j 29f
                  29: ori x4, x4, 1
                  csrr x13, 0x340
                  li x18, 30
                  sll x13, x13, x18
                  srl x13, x13, x18
                  slli x18, x13, 3
                  sll x4, x4, x18
                  or x5, x5, x4
                  csrr x13, 0x340
                  srli x13, x13, 2
                  beqz x13, 30f
                  li x18, 1
                  beq x13, x18, 31f
                  li x18, 2
                  beq x13, x18, 32f
                  li x18, 3
                  beq x13, x18, 33f
                  30: csrw 0x3a0, x5
                  j 34f
                  31: csrw 0x3a1, x5
                  j 34f
                  32: csrw 0x3a2, x5
                  j 34f
                  33: csrw 0x3a3, x5
                  34: nop
                  lw  x1, 4(x29)
                  lw  x2, 8(x29)
                  lw  x3, 12(x29)
                  lw  x4, 16(x29)
                  lw  x5, 20(x29)
                  lw  x6, 24(x29)
                  lw  x7, 28(x29)
                  lw  x8, 32(x29)
                  lw  x9, 36(x29)
                  lw  x10, 40(x29)
                  lw  x11, 44(x29)
                  lw  x12, 48(x29)
                  lw  x13, 52(x29)
                  lw  x14, 56(x29)
                  lw  x15, 60(x29)
                  lw  x16, 64(x29)
                  lw  x17, 68(x29)
                  lw  x18, 72(x29)
                  lw  x19, 76(x29)
                  lw  x20, 80(x29)
                  lw  x21, 84(x29)
                  lw  x22, 88(x29)
                  lw  x23, 92(x29)
                  lw  x24, 96(x29)
                  lw  x25, 100(x29)
                  lw  x26, 104(x29)
                  lw  x27, 108(x29)
                  lw  x28, 112(x29)
                  lw  x29, 116(x29)
                  lw  x30, 120(x29)
                  lw  x31, 124(x29)
                  addi x29, x29, 124
                  add x17, x29, zero
                  csrrw x29, 0x340, x29
                  mret

store_fault_handler:
                  li x13, 0
                  csrw 0x340, x13
                  li x28, 0
                  0: csrr x13, 0x340
                  mv x18, x13
                  li x18, 0
                  beq x13, x18, 1f
                  1: csrr x6, 0x3b0
                  csrr x5, 0x3a0
                  j 17f
                  17: li x4, 4
                  csrr x13, 0x340
                  slli x13, x13, 30
                  srli x13, x13, 30
                  sub x18, x4, x13
                  addi x18, x18, -1
                  slli x18, x18, 3
                  sll x4, x5, x18
                  slli x13, x13, 3
                  add x18, x18, x13
                  srl x4, x4, x18
                  slli x18, x4, 27
                  srli x18, x18, 30
                  beqz x18, 20f
                  li x13, 1
                  beq x18, x13, 21f
                  li x13, 2
                  beq x18, x13, 25f
                  li x13, 3
                  beq x18, x13, 27f
                  j test_done
                  18: csrr x13, 0x340
                  mv x28, x6
                  addi x13, x13, 1
                  csrw 0x340, x13
                  li x6, 1
                  ble x6, x13, 19f
                  j 0b
                  19: j test_done
                  20: j 18b
                  21: csrr x13, 0x340
                  csrr x18, 0x343
                  srli x18, x18, 2
                  bnez x13, 22f
                  bltz x18, 18b
                  j 23f
                  22: bgtu x28, x18, 18b
                  23: bleu x6, x18, 18b
                  andi x18, x4, 128
                  beqz x18, 24f
                  j test_done
                  24: j 29f
                  25: csrr x13, 0x343
                  srli x13, x13, 2
                  slli x18, x6, 2
                  srli x18, x18, 2
                  bne x13, x18, 18b
                  andi x18, x4, 128
                  beqz x18, 26f
                  j test_done
                  26: j 29f
                  27: csrr x13, 0x343
                  srli x13, x13, 2
                  srli x13, x13, 0
                  slli x13, x13, 0
                  slli x18, x6, 2
                  srli x18, x18, 2
                  srli x18, x18, 0
                  slli x18, x18, 0
                  bne x13, x18, 18b
                  andi x18, x4, 128
                  beqz x18, 29f
                  j test_done
                  28: j 29f
                  29: ori x4, x4, 3
                  csrr x13, 0x340
                  li x18, 30
                  sll x13, x13, x18
                  srl x13, x13, x18
                  slli x18, x13, 3
                  sll x4, x4, x18
                  or x5, x5, x4
                  csrr x13, 0x340
                  srli x13, x13, 2
                  beqz x13, 30f
                  li x18, 1
                  beq x13, x18, 31f
                  li x18, 2
                  beq x13, x18, 32f
                  li x18, 3
                  beq x13, x18, 33f
                  30: csrw 0x3a0, x5
                  j 34f
                  31: csrw 0x3a1, x5
                  j 34f
                  32: csrw 0x3a2, x5
                  j 34f
                  33: csrw 0x3a3, x5
                  34: nop
                  lw  x1, 4(x29)
                  lw  x2, 8(x29)
                  lw  x3, 12(x29)
                  lw  x4, 16(x29)
                  lw  x5, 20(x29)
                  lw  x6, 24(x29)
                  lw  x7, 28(x29)
                  lw  x8, 32(x29)
                  lw  x9, 36(x29)
                  lw  x10, 40(x29)
                  lw  x11, 44(x29)
                  lw  x12, 48(x29)
                  lw  x13, 52(x29)
                  lw  x14, 56(x29)
                  lw  x15, 60(x29)
                  lw  x16, 64(x29)
                  lw  x17, 68(x29)
                  lw  x18, 72(x29)
                  lw  x19, 76(x29)
                  lw  x20, 80(x29)
                  lw  x21, 84(x29)
                  lw  x22, 88(x29)
                  lw  x23, 92(x29)
                  lw  x24, 96(x29)
                  lw  x25, 100(x29)
                  lw  x26, 104(x29)
                  lw  x27, 108(x29)
                  lw  x28, 112(x29)
                  lw  x29, 116(x29)
                  lw  x30, 120(x29)
                  lw  x31, 124(x29)
                  addi x29, x29, 124
                  add x17, x29, zero
                  csrrw x29, 0x340, x29
                  mret

ebreak_handler:   
                  csrr  x13, mepc
                  addi  x13, x13, 4
                  csrw  mepc, x13
                  lw  x1, 4(x29)
                  lw  x2, 8(x29)
                  lw  x3, 12(x29)
                  lw  x4, 16(x29)
                  lw  x5, 20(x29)
                  lw  x6, 24(x29)
                  lw  x7, 28(x29)
                  lw  x8, 32(x29)
                  lw  x9, 36(x29)
                  lw  x10, 40(x29)
                  lw  x11, 44(x29)
                  lw  x12, 48(x29)
                  lw  x13, 52(x29)
                  lw  x14, 56(x29)
                  lw  x15, 60(x29)
                  lw  x16, 64(x29)
                  lw  x17, 68(x29)
                  lw  x18, 72(x29)
                  lw  x19, 76(x29)
                  lw  x20, 80(x29)
                  lw  x21, 84(x29)
                  lw  x22, 88(x29)
                  lw  x23, 92(x29)
                  lw  x24, 96(x29)
                  lw  x25, 100(x29)
                  lw  x26, 104(x29)
                  lw  x27, 108(x29)
                  lw  x28, 112(x29)
                  lw  x29, 116(x29)
                  lw  x30, 120(x29)
                  lw  x31, 124(x29)
                  addi x29, x29, 124
                  add x17, x29, zero
                  csrrw x29, 0x340, x29
                  mret

illegal_instr_handler:
                  csrr  x13, mepc
                  addi  x13, x13, 4
                  csrw  mepc, x13
                  lw  x1, 4(x29)
                  lw  x2, 8(x29)
                  lw  x3, 12(x29)
                  lw  x4, 16(x29)
                  lw  x5, 20(x29)
                  lw  x6, 24(x29)
                  lw  x7, 28(x29)
                  lw  x8, 32(x29)
                  lw  x9, 36(x29)
                  lw  x10, 40(x29)
                  lw  x11, 44(x29)
                  lw  x12, 48(x29)
                  lw  x13, 52(x29)
                  lw  x14, 56(x29)
                  lw  x15, 60(x29)
                  lw  x16, 64(x29)
                  lw  x17, 68(x29)
                  lw  x18, 72(x29)
                  lw  x19, 76(x29)
                  lw  x20, 80(x29)
                  lw  x21, 84(x29)
                  lw  x22, 88(x29)
                  lw  x23, 92(x29)
                  lw  x24, 96(x29)
                  lw  x25, 100(x29)
                  lw  x26, 104(x29)
                  lw  x27, 108(x29)
                  lw  x28, 112(x29)
                  lw  x29, 116(x29)
                  lw  x30, 120(x29)
                  lw  x31, 124(x29)
                  addi x29, x29, 124
                  add x17, x29, zero
                  csrrw x29, 0x340, x29
                  mret

pt_fault_handler: 
                  nop

.align 2
mmode_intr_handler:
                  csrr  x13, 0x300 # MSTATUS;
                  csrr  x13, 0x304 # MIE;
                  csrr  x13, 0x344 # MIP;
                  csrrc x13, 0x344, x13 # MIP;
                  lw  x1, 4(x29)
                  lw  x2, 8(x29)
                  lw  x3, 12(x29)
                  lw  x4, 16(x29)
                  lw  x5, 20(x29)
                  lw  x6, 24(x29)
                  lw  x7, 28(x29)
                  lw  x8, 32(x29)
                  lw  x9, 36(x29)
                  lw  x10, 40(x29)
                  lw  x11, 44(x29)
                  lw  x12, 48(x29)
                  lw  x13, 52(x29)
                  lw  x14, 56(x29)
                  lw  x15, 60(x29)
                  lw  x16, 64(x29)
                  lw  x17, 68(x29)
                  lw  x18, 72(x29)
                  lw  x19, 76(x29)
                  lw  x20, 80(x29)
                  lw  x21, 84(x29)
                  lw  x22, 88(x29)
                  lw  x23, 92(x29)
                  lw  x24, 96(x29)
                  lw  x25, 100(x29)
                  lw  x26, 104(x29)
                  lw  x27, 108(x29)
                  lw  x28, 112(x29)
                  lw  x29, 116(x29)
                  lw  x30, 120(x29)
                  lw  x31, 124(x29)
                  addi x29, x29, 124
                  add x17, x29, zero
                  csrrw x29, 0x340, x29
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
