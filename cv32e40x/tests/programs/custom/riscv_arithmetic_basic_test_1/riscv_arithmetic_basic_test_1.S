# BEGIN: riscv-dv
#.include "user_define.h"
#.globl _start
#.section .text
#_start:           
# END: riscv-dv
# BEGIN: gtumbush
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
                  li x10, 0x40001104
                  csrw misa, x10
kernel_sp:        
                  la x31, kernel_stack_end

trap_vec_init:    
                  la x10, mtvec_handler
                  ori x10, x10, 1
                  csrw 0x305, x10 # MTVEC

mepc_setup:       
                  la x10, init
                  csrw mepc, x10
                  j init_machine_mode

init:             
                  li x0, 0xfd790eda
                  li x1, 0x80000000
                  li x2, 0x6
                  li x3, 0x0
                  li x4, 0x80000000
                  li x5, 0xe
                  li x6, 0x87c36d9
                  li x7, 0xb
                  li x8, 0x80000000
                  li x9, 0x9
                  li x10, 0xf510029d
                  li x11, 0x47cc0565
                  li x12, 0x80000000
                  li x13, 0x80000000
                  li x14, 0x0
                  li x16, 0xf03e6cd8
                  li x17, 0x9
                  li x18, 0x0
                  li x19, 0x0
                  li x20, 0xfb21c919
                  li x21, 0x8b56ef7a
                  li x22, 0xd10cbf06
                  li x23, 0xfdbec9f2
                  li x24, 0xf34f30bf
                  li x25, 0x7
                  li x26, 0x0
                  li x27, 0xf61c9318
                  li x28, 0x5
                  li x29, 0xf7e30b15
                  li x30, 0x15a65931
                  la x15, user_stack_end
main:             li         s7, 0xffffffff #start riscv_int_numeric_corner_stream_10
                  li         t2, 0x80000000
                  li         tp, 0x80000000
                  li         a6, 0x3ac3aef8
                  li         s11, 0xffffffff
                  li         s6, 0x4ad1c1ff
                  li         s8, 0x80000000
                  li         a2, 0x80000000
                  li         a0, 0xffffffff
                  li         s10, 0x80000000
                  auipc      a0, 11691
                  nop
                  nop
                  add        s6, tp, s6
                  divu       a0, s6, s8
                  div        a6, a2, t2
                  divu       a0, s6, s8
                  nop
                  nop
                  divu       a0, s6, s8
                  mul        a2, tp, a0
                  divu       a0, s6, s8
                  sub        a0, a0, s8
                  div        a6, a2, t2
                  lui        s6, 985951
                  nop
                  nop
                  nop
                  add        s6, tp, s6
                  remu       s8, s6, a2
                  mul        a2, tp, a0
                  mulh       s8, s7, tp
                  mulhsu     tp, a2, s11
                  div        a6, a2, t2
                  mul        a2, tp, a0 #end riscv_int_numeric_corner_stream_10
                  li         t5, 0x0 #start riscv_int_numeric_corner_stream_19
                  li         s3, 0x80000000
                  li         t4, 0xed3ad258
                  li         a7, 0xffffffff
                  li         s6, 0x0
                  li         s2, 0xffffffff
                  li         s7, 0x80000000
                  li         t0, 0xd203cab0
                  li         a4, 0x9c87e90b
                  li         s5, 0x80000000
                  divu       a7, a4, a7
                  nop
                  auipc      t4, 11691
                  mulhsu     t4, t0, t0
                  auipc      t4, 11691
                  lui        s6, 985951
                  rem        a7, t0, a4
                  lui        s6, 985951
                  nop
                  add        s3, s7, t5
                  add        s3, s7, t5
                  addi       a4, s3, -40
                  add        s3, s7, t5
                  auipc      t4, 11691
                  nop #end riscv_int_numeric_corner_stream_19
                  li         s4, 0x0 #start riscv_int_numeric_corner_stream_31
                  li         a6, 0x4efe2548
                  li         sp, 0x0
                  li         s11, 0x80000000
                  li         s9, 0x80000000
                  li         s3, 0xcacc4459
                  li         a4, 0xffffffff
                  li         a0, 0xffffffff
                  li         gp, 0x80000000
                  li         t1, 0x3b7b50de
                  mulh       s11, gp, gp
                  add        s3, s11, a4
                  rem        s4, a6, a4
                  lui        gp, 985951
                  lui        gp, 985951
                  mulhsu     s4, a0, gp
                  add        s3, s11, a4
                  nop
                  mulhu      s9, a4, a4
                  lui        gp, 985951
                  lui        gp, 985951
                  addi       s9, s3, -40
                  sub        a0, s9, s9
                  nop
                  remu       s9, s4, a4
                  mulhsu     s4, a0, gp
                  addi       s9, s3, -40
                  div        a0, s9, gp
                  mul        t1, s4, a4
                  divu       s4, a0, s9
                  nop
                  mul        t1, s4, a4
                  nop
                  addi       s9, s3, -40 #end riscv_int_numeric_corner_stream_31
                  li         tp, 0x80000000 #start riscv_int_numeric_corner_stream_39
                  li         t1, 0xffffffff
                  li         s7, 0x80000000
                  li         a3, 0x80000000
                  li         s2, 0x0
                  li         s6, 0x80000000
                  li         sp, 0x80000000
                  li         gp, 0xdce02feb
                  li         s11, 0x0
                  li         s1, 0x80000000
                  remu       a3, s11, s2
                  rem        a3, s2, t1
                  sub        s6, a3, s11
                  auipc      s1, 11691
                  rem        a3, s2, t1
                  sub        s6, a3, s11
                  addi       s11, s11, -40
                  auipc      s1, 11691
                  nop
                  lui        gp, 985951
                  rem        a3, s2, t1
                  div        tp, s11, gp
                  sub        s6, a3, s11
                  nop
                  add        t1, sp, s6
                  nop
                  mulhsu     s7, sp, gp
                  sub        s6, a3, s11
                  nop
                  nop
                  addi       s11, s11, -40
                  nop
                  div        tp, s11, gp
                  add        t1, sp, s6
                  mulhsu     s7, sp, gp
                  mulhu      s1, a3, s7
                  mul        tp, tp, a3
                  add        t1, sp, s6
                  div        tp, s11, gp
                  addi       s11, s11, -40 #end riscv_int_numeric_corner_stream_39
                  li         s8, 0xffffffff #start riscv_int_numeric_corner_stream_36
                  li         t3, 0xc9ee93a5
                  li         a2, 0x80000000
                  li         t1, 0x98dfc66b
                  li         t0, 0x1878354d
                  li         s11, 0x80000000
                  li         t4, 0xffffffff
                  li         gp, 0x80000000
                  li         tp, 0x80000000
                  li         s9, 0xfc3b413b
                  sub        gp, gp, s9
                  addi       a2, s11, -40
                  auipc      a2, 11691
                  lui        t1, 985951
                  mulhsu     t1, t1, t0
                  addi       a2, s11, -40
                  divu       a2, t1, s9
                  add        t4, t0, t1
                  mulhu      tp, a2, t4
                  mul        gp, t1, a2
                  add        t4, t0, t1
                  nop
                  lui        t1, 985951
                  nop
                  div        a2, t4, gp #end riscv_int_numeric_corner_stream_36
                  li         s1, 0xffffffff #start riscv_int_numeric_corner_stream_3
                  li         a6, 0x79e3b252
                  li         s11, 0x0
                  li         s6, 0x80000000
                  li         a3, 0x80000000
                  li         gp, 0xffffffff
                  li         t2, 0x2004d0a7
                  li         s3, 0x5a561351
                  li         s2, 0xffffffff
                  li         t1, 0x80000000
                  mulhsu     s6, a3, gp
                  mulhu      s11, a6, s6
                  auipc      s1, 11691
                  mulh       t2, t2, a3
                  add        s6, t1, s6
                  divu       s2, t2, a6
                  mulhsu     s6, a3, gp
                  nop
                  div        a6, s6, t2
                  mulhu      s11, a6, s6
                  divu       s2, t2, a6
                  nop
                  mulhsu     s6, a3, gp
                  rem        a6, a6, t2
                  add        s6, t1, s6
                  auipc      s1, 11691
                  lui        s3, 985951
                  addi       s11, s11, -40
                  add        s6, t1, s6
                  nop
                  mulh       t2, t2, a3
                  div        a6, s6, t2
                  add        s6, t1, s6
                  mulhu      s11, a6, s6
                  nop #end riscv_int_numeric_corner_stream_3
                  li         tp, 0x80000000 #start riscv_int_numeric_corner_stream_34
                  li         t1, 0xffffffff
                  li         s6, 0xbb2d7d7d
                  li         t5, 0x80000000
                  li         a7, 0xbd53de38
                  li         s4, 0x80000000
                  li         gp, 0x80000000
                  li         a2, 0x80000000
                  li         t2, 0x80000000
                  li         t0, 0x80000000
                  nop
                  add        t2, t1, t5
                  nop
                  rem        a7, s4, t2
                  add        t2, t1, t5
                  divu       tp, gp, a7
                  nop
                  div        s4, a7, t2
                  addi       t0, s6, -40
                  addi       t0, s6, -40
                  add        t2, t1, t5
                  mulhu      t0, s6, t5
                  auipc      a2, 11691
                  sub        t5, a7, t5
                  addi       t0, s6, -40
                  addi       t0, s6, -40 #end riscv_int_numeric_corner_stream_34
                  li         s4, 0x80000000 #start riscv_int_numeric_corner_stream_28
                  li         s10, 0x636d4c95
                  li         a4, 0x0
                  li         t0, 0x8a8a1c6c
                  li         t3, 0x281c157a
                  li         t5, 0x0
                  li         a0, 0x9aabfa88
                  li         s6, 0x0
                  li         s3, 0x3fbbf7da
                  li         t2, 0x534dc5c2
                  nop
                  mulhsu     t2, t5, s3
                  mulhu      s3, s6, t5
                  addi       a0, s10, -40
                  add        s3, t2, a4
                  divu       a0, a4, s3
                  sub        s10, a4, s10
                  mul        t3, s6, t3
                  addi       a0, s10, -40
                  addi       a0, s10, -40
                  div        s4, s10, t2
                  addi       a0, s10, -40
                  auipc      t3, 11691
                  addi       a0, s10, -40
                  sub        s10, a4, s10
                  nop #end riscv_int_numeric_corner_stream_28
                  li         s2, 0x80000000 #start riscv_int_numeric_corner_stream_7
                  li         s7, 0x80000000
                  li         s1, 0xffffffff
                  li         a0, 0x80000000
                  li         a7, 0x0
                  li         s0, 0x80000000
                  li         a2, 0x689cd09d
                  li         s6, 0x3e6ea5e0
                  li         ra, 0x0
                  li         a6, 0xffffffff
                  lui        s6, 985951
                  div        a2, s7, ra
                  mulhu      a7, s1, s7
                  nop
                  divu       a0, s6, a7
                  auipc      s0, 11691
                  add        s7, a0, s6
                  nop
                  auipc      s0, 11691
                  auipc      s0, 11691
                  auipc      s0, 11691
                  auipc      s0, 11691
                  nop
                  sub        s6, a0, a7
                  nop #end riscv_int_numeric_corner_stream_7
                  li         a3, 0xffffffff #start riscv_int_numeric_corner_stream_29
                  li         t5, 0xde4c99ec
                  li         t4, 0x0
                  li         s5, 0xffffffff
                  li         s7, 0x80000000
                  li         s11, 0x0
                  li         a7, 0x0
                  li         s3, 0xce081e9d
                  li         ra, 0x3fa8bcfc
                  li         t3, 0xffffffff
                  mulhu      a7, ra, t5
                  nop
                  mulhu      a7, ra, t5
                  lui        s11, 985951
                  mul        s3, s7, a3
                  remu       s11, s7, t3
                  nop
                  lui        s11, 985951
                  auipc      a3, 11691
                  nop
                  mul        s3, s7, a3
                  lui        s11, 985951
                  nop
                  nop
                  div        t3, s5, s3
                  nop
                  nop
                  add        t5, s7, t5
                  remu       s11, s7, t3
                  remu       s11, s7, t3
                  addi       t5, s7, -40
                  remu       s11, s7, t3
                  remu       s11, s7, t3
                  sub        s11, t5, t3
                  nop #end riscv_int_numeric_corner_stream_29
                  li         t2, 0xae086eb9 #start riscv_int_numeric_corner_stream_22
                  li         s0, 0x0
                  li         tp, 0x80000000
                  li         t4, 0x80000000
                  li         ra, 0x0
                  li         a0, 0x80000000
                  li         s4, 0x80000000
                  li         s7, 0x0
                  li         a2, 0x0
                  li         s11, 0x0
                  mulhu      ra, a2, t4
                  addi       ra, s7, -40
                  addi       ra, s7, -40
                  div        s4, tp, t2
                  mul        a2, s4, a0
                  add        s7, s7, a0
                  add        s7, s7, a0
                  nop
                  nop
                  add        s7, s7, a0
                  lui        s7, 985951
                  nop
                  nop
                  mulhsu     s7, s7, ra
                  divu       s0, a0, s11
                  addi       ra, s7, -40
                  divu       s0, a0, s11
                  lui        s7, 985951
                  nop
                  mulhu      ra, a2, t4
                  lui        s7, 985951
                  add        s7, s7, a0
                  mulh       s4, t4, tp
                  add        s7, s7, a0 #end riscv_int_numeric_corner_stream_22
                  li         s5, 0xffffffff #start riscv_int_numeric_corner_stream_4
                  li         t5, 0x0
                  li         s7, 0x80000000
                  li         sp, 0xffffffff
                  li         s2, 0x80000000
                  li         a0, 0x0
                  li         s1, 0x80000000
                  li         s9, 0x0
                  li         s11, 0xffffffff
                  li         gp, 0xeaed74f6
                  divu       s9, a0, s9
                  nop
                  mul        gp, s5, a0
                  lui        gp, 985951
                  rem        s9, s2, a0
                  mulhsu     s7, sp, gp
                  div        s5, s9, gp
                  addi       a0, s11, -40
                  div        s5, s9, gp
                  mulhu      s1, gp, t5
                  lui        gp, 985951
                  lui        gp, 985951
                  divu       s9, a0, s9
                  nop
                  add        t5, s2, t5
                  div        s5, s9, gp #end riscv_int_numeric_corner_stream_4
                  li         t3, 0x407c80ae #start riscv_int_numeric_corner_stream_8
                  li         a4, 0x0
                  li         s11, 0x0
                  li         s8, 0x9c296067
                  li         t5, 0x80000000
                  li         gp, 0x80000000
                  li         s9, 0x0
                  li         a0, 0x80000000
                  li         s3, 0x0
                  li         s10, 0x80000000
                  divu       s9, a4, s9
                  nop
                  mulhu      s9, a4, t5
                  mulhu      s9, a4, t5
                  lui        s3, 985951
                  mulhu      s9, a4, t5
                  lui        s3, 985951
                  sub        s8, t5, s8
                  add        gp, s11, t5
                  mul        gp, t3, a4
                  sub        s8, t5, s8
                  sub        s8, t5, s8
                  divu       s9, a4, s9
                  mul        gp, t3, a4
                  mul        gp, t3, a4
                  div        a0, t5, gp
                  auipc      a0, 11691
                  remu       gp, t5, s10
                  divu       s9, a4, s9
                  nop
                  add        gp, s11, t5
                  nop
                  mulhu      s9, a4, t5
                  sub        s8, t5, s8
                  mulh       s11, gp, gp
                  mulhu      s9, a4, t5
                  mulhsu     s3, a0, gp #end riscv_int_numeric_corner_stream_8
                  li         ra, 0x80000000 #start riscv_int_numeric_corner_stream_12
                  li         t2, 0x80000000
                  li         t4, 0x0
                  li         s5, 0xc8b5b745
                  li         t0, 0x0
                  li         s0, 0xaf19864a
                  li         s9, 0x0
                  li         s3, 0xffffffff
                  li         s7, 0x80000000
                  li         s1, 0xdb76c9dc
                  sub        s0, s0, s9
                  lui        t2, 985951
                  addi       s9, s3, -40
                  addi       s9, s3, -40
                  mulh       t0, s7, t0
                  mulhu      ra, s1, s7
                  nop
                  nop
                  nop
                  nop
                  remu       s7, s3, s0
                  add        t4, s5, s0
                  remu       s7, s3, s0
                  divu       s0, t2, s9
                  auipc      s0, 11691
                  mulhsu     s7, s7, ra
                  addi       s9, s3, -40
                  auipc      s0, 11691
                  addi       s9, s3, -40
                  add        t4, s5, s0
                  nop
                  mulh       t0, s7, t0
                  mulh       t0, s7, t0
                  nop
                  nop
                  div        s9, s1, s3 #end riscv_int_numeric_corner_stream_12
                  li         t4, 0x80000000 #start riscv_int_numeric_corner_stream_26
                  li         a3, 0x0
                  li         s2, 0xa091fb6
                  li         t5, 0xffffffff
                  li         a4, 0x0
                  li         s0, 0x80000000
                  li         s3, 0x0
                  li         t2, 0xffffffff
                  li         s1, 0x80000000
                  li         s9, 0x80000000
                  mulhsu     t2, s0, s3
                  nop
                  remu       a3, s3, a4
                  nop
                  div        t4, a3, s3
                  add        s2, t2, a4
                  lui        s3, 985951
                  mul        s0, a3, a4
                  add        s2, t2, a4
                  mulh       a3, s3, a3
                  div        t4, a3, s3
                  mul        s0, a3, a4
                  add        s2, t2, a4
                  divu       a3, a4, s9
                  add        s2, t2, a4
                  sub        s9, s9, t5
                  nop #end riscv_int_numeric_corner_stream_26
                  li         t0, 0x0 #start riscv_int_numeric_corner_stream_30
                  li         t4, 0x0
                  li         s0, 0x0
                  li         gp, 0x80000000
                  li         t5, 0x0
                  li         t2, 0x0
                  li         s2, 0x34fc9f73
                  li         t3, 0x80000000
                  li         a3, 0x12997968
                  li         a4, 0x80000000
                  mul        t3, t3, a4
                  mulhsu     t2, s0, t0
                  sub        gp, gp, t3
                  sub        gp, gp, t3
                  nop
                  divu       s0, gp, s2
                  mulh       t3, t4, t0
                  nop
                  lui        gp, 985951
                  remu       t3, gp, a4
                  mulhu      t0, a3, t5
                  nop
                  lui        gp, 985951
                  auipc      s0, 11691
                  nop
                  mulh       t3, t4, t0
                  remu       t3, gp, a4
                  mulhu      t0, a3, t5
                  mulhsu     t2, s0, t0
                  addi       t4, s2, -40 #end riscv_int_numeric_corner_stream_30
                  li         a2, 0xffffffff #start riscv_int_numeric_corner_stream_32
                  li         t3, 0xffffffff
                  li         t4, 0x80000000
                  li         t1, 0xffffffff
                  li         a0, 0x96d8c8c7
                  li         sp, 0x80000000
                  li         s11, 0x75e0c140
                  li         a4, 0xa697830b
                  li         s0, 0x80000000
                  li         s9, 0xffffffff
                  divu       sp, a4, s9
                  mulhu      t4, a0, t4
                  rem        t4, sp, a4
                  addi       sp, s11, -40
                  mul        a4, a2, a4
                  mul        a4, a2, a4
                  div        a2, t4, sp
                  add        t3, t4, a4
                  addi       sp, s11, -40
                  rem        t4, sp, a4
                  nop
                  add        t3, t4, a4
                  add        t3, t4, a4
                  remu       s0, t4, a2
                  divu       sp, a4, s9
                  auipc      s0, 11691
                  auipc      s0, 11691
                  divu       sp, a4, s9
                  divu       sp, a4, s9
                  addi       sp, s11, -40
                  nop
                  sub        t1, sp, s9
                  mulh       t4, s11, s0
                  auipc      s0, 11691
                  nop #end riscv_int_numeric_corner_stream_32
                  remu       s6, s3, t1
                  div        s7, gp, a4
                  c.xor      a4, a5
                  and        s6, t2, a4
                  sra        s9, s4, t5
                  c.slli     t5, 22
                  c.or       a0, a2
                  srl        t1, tp, zero
                  addi       gp, s8, -298
                  or         a4, a4, zero
                  addi       gp, s8, -298
                  mulh       s1, t4, s11
                  or         a4, a4, zero
                  or         a4, a4, zero
                  c.li       s11, -1
                  sltu       s3, a6, a4
                  div        s7, gp, a4
                  mulhu      s4, a6, t3
                  srl        t1, tp, zero
                  c.nop
                  c.add      t3, t1
                  slt        a0, s5, s11
                  addi       gp, s8, -298
                  div        s7, gp, a4
                  srai       a4, a3, 0
                  c.addi     s9, -1
                  and        s6, t2, a4
                  c.addi16sp sp, -16
                  slt        a0, s5, s11
                  srl        t1, tp, zero
                  c.sub      s0, s1
                  or         a4, a4, zero
                  srli       zero, a0, 13
                  sub        s0, t3, gp
                  c.andi     s1, 31
                  c.or       a0, a2
                  c.srai     s1, 28
                  c.addi4spn a2, sp, 528
                  c.addi     s9, -1
                  nop
                  sub        s0, t3, gp
                  c.sub      s0, s1
                  slti       tp, a1, -167
                  c.mv       a2, a0
                  c.slli     t5, 22
                  sltiu      s3, tp, 300
                  sltu       s3, a6, a4
                  sll        s8, s0, s6
                  auipc      s1, 11691
                  sra        s9, s4, t5
                  c.mv       a2, a0
                  addi       gp, s8, -298
                  mulhsu     tp, t5, a6
                  mulhsu     tp, t5, a6
                  mulhu      s4, a6, t3
                  mulhu      s4, a6, t3
                  sll        s8, s0, s6
                  c.srai     s1, 28
                  slt        a0, s5, s11
                  xori       t3, t1, -721
                  c.xor      a4, a5
                  auipc      s1, 11691
                  slti       tp, a1, -167
                  ori        tp, a0, -848
                  c.nop
                  c.lui      a6, 24
                  c.andi     s1, 31
                  sub        s0, t3, gp
                  and        s6, t2, a4
                  mulh       s1, t4, s11
                  c.add      t3, t1
                  c.andi     s1, 31
                  sltiu      s3, tp, 300
                  c.mv       a2, a0
                  c.mv       a2, a0
                  sltu       s3, a6, a4
                  c.addi16sp sp, -16
                  sra        s9, s4, t5
                  mulhu      s4, a6, t3
                  c.or       a0, a2
                  andi       t0, a3, 147
                  ori        tp, a0, -848
                  slli       a2, a4, 25
                  c.addi4spn a2, sp, 528
                  remu       s6, s3, t1
                  c.xor      a4, a5
                  c.sub      s0, s1
                  mul        tp, s2, t5
                  srl        t1, tp, zero
                  div        s7, gp, a4
                  mulhu      s4, a6, t3
                  andi       t0, a3, 147
                  mulhsu     tp, t5, a6
                  c.andi     s1, 31
                  srai       a4, a3, 0
                  rem        a2, s2, s9
                  c.slli     t5, 22
                  rem        a2, s2, s9
                  c.and      a4, s1
                  c.addi     s9, -1
                  c.andi     s1, 31
                  mul        tp, s2, t5
                  c.li       s11, -1
                  sub        s0, t3, gp
                  c.srli     a4, 9
                  and        s6, t2, a4
                  andi       t0, a3, 147
                  sll        s8, s0, s6
                  c.srli     a4, 9
                  c.xor      a4, a5
                  sltiu      s3, tp, 300
                  srl        t1, tp, zero
                  mul        tp, s2, t5
                  c.and      a4, s1
                  nop
                  slti       tp, a1, -167
                  slti       tp, a1, -167
                  add        s4, a7, s6
                  c.mv       a2, a0
                  mulh       s1, t4, s11
                  c.srai     s1, 28
                  srai       a4, a3, 0
                  srli       zero, a0, 13
                  srl        t1, tp, zero
                  c.or       a0, a2
                  andi       t0, a3, 147
                  c.nop
                  divu       tp, s5, t4
                  c.sub      s0, s1
                  c.srli     a4, 9
                  mulh       s1, t4, s11
                  c.mv       a2, a0
                  nop
                  addi       gp, s8, -298
                  c.sub      s0, s1
                  c.lui      a6, 24
                  sltu       s3, a6, a4
                  sltiu      s3, tp, 300
                  slti       tp, a1, -167
                  c.andi     s1, 31
                  c.mv       a2, a0
                  c.nop
                  slt        a0, s5, s11
                  xor        s11, zero, s7
                  addi       gp, s8, -298
                  divu       tp, s5, t4
                  c.xor      a4, a5
                  c.li       s11, -1
                  add        s4, a7, s6
                  sra        s9, s4, t5
                  addi       gp, s8, -298
                  c.andi     s1, 31
                  c.mv       a2, a0
                  addi       gp, s8, -298
                  c.srli     a4, 9
                  c.or       a0, a2
                  srli       zero, a0, 13
                  mulh       s1, t4, s11
                  remu       s6, s3, t1
                  mulh       s1, t4, s11
                  ori        tp, a0, -848
                  c.slli     t5, 22
                  nop
                  divu       tp, s5, t4
                  sltiu      s3, tp, 300
                  mul        tp, s2, t5
                  sltiu      s3, tp, 300
                  c.addi16sp sp, -16
                  rem        a2, s2, s9
                  srai       a4, a3, 0
                  c.nop
                  ori        tp, a0, -848
                  mul        tp, s2, t5
                  srl        t1, tp, zero
                  lui        s3, 985951
                  mulhu      s4, a6, t3
                  andi       t0, a3, 147
                  add        s4, a7, s6
                  xori       t3, t1, -721
                  c.add      t3, t1
                  div        s7, gp, a4
                  c.slli     t5, 22
                  srai       a4, a3, 0
                  c.addi16sp sp, -16
                  c.sub      s0, s1
                  slli       a2, a4, 25
                  lui        s3, 985951
                  sra        s9, s4, t5
                  mul        tp, s2, t5
                  slt        a0, s5, s11
                  c.srli     a4, 9
                  c.srai     s1, 28
                  srli       zero, a0, 13
                  remu       s6, s3, t1
                  div        s7, gp, a4
                  xor        s11, zero, s7
                  div        s7, gp, a4
                  slt        a0, s5, s11
                  sub        s0, t3, gp
                  c.li       s11, -1
                  lui        s3, 985951
                  srai       a4, a3, 0
                  c.li       s11, -1
                  c.xor      a4, a5
                  c.srli     a4, 9
                  c.xor      a4, a5
                  c.mv       a2, a0
                  c.nop
                  and        s6, t2, a4
                  c.nop
                  c.addi4spn a2, sp, 528
                  c.andi     s1, 31
                  c.lui      a6, 24
                  c.add      t3, t1
                  add        s4, a7, s6
                  c.addi16sp sp, -16
                  c.srli     a4, 9
                  c.sub      s0, s1
                  c.or       a0, a2
                  rem        a2, s2, s9
                  c.and      a4, s1
                  slt        a0, s5, s11
                  divu       tp, s5, t4
                  c.mv       a2, a0
                  sll        s8, s0, s6
                  div        s7, gp, a4
                  add        s4, a7, s6
                  c.nop
                  c.add      t3, t1
                  c.lui      a6, 24
                  c.li       s11, -1
                  addi       gp, s8, -298
                  div        s7, gp, a4
                  c.nop
                  c.sub      s0, s1
                  divu       tp, s5, t4
                  or         a4, a4, zero
                  addi       gp, s8, -298
                  c.nop
                  c.addi     s9, -1
                  c.slli     t5, 22
                  andi       t0, a3, 147
                  c.srai     s1, 28
                  c.add      t3, t1
                  c.nop
                  ori        tp, a0, -848
                  xor        s11, zero, s7
                  c.slli     t5, 22
                  mulh       s1, t4, s11
                  c.addi4spn a2, sp, 528
                  c.andi     s1, 31
                  srl        t1, tp, zero
                  auipc      s1, 11691
                  c.li       s11, -1
                  c.addi16sp sp, -16
                  slt        a0, s5, s11
                  add        s4, a7, s6
                  ori        tp, a0, -848
                  sub        s0, t3, gp
                  srai       a4, a3, 0
                  nop
                  remu       s6, s3, t1
                  sll        s8, s0, s6
                  c.addi4spn a2, sp, 528
                  srai       a4, a3, 0
                  slt        a0, s5, s11
                  add        s4, a7, s6
                  add        s4, a7, s6
                  c.xor      a4, a5
                  lui        s3, 985951
                  c.srli     a4, 9
                  mulhu      s4, a6, t3
                  c.srai     s1, 28
                  lui        s3, 985951
                  srl        t1, tp, zero
                  mul        tp, s2, t5
                  slt        a0, s5, s11
                  sra        s9, s4, t5
                  sll        s8, s0, s6
                  slt        a0, s5, s11
                  ori        tp, a0, -848
                  addi       gp, s8, -298
                  remu       s6, s3, t1
                  mulhu      s4, a6, t3
                  and        s6, t2, a4
                  c.srai     s1, 28
                  c.xor      a4, a5
                  srl        t1, tp, zero
                  c.addi16sp sp, -16
                  addi       gp, s8, -298
                  nop
                  remu       s6, s3, t1
                  lui        s3, 985951
                  c.li       s11, -1
                  c.mv       a2, a0
                  add        s4, a7, s6
                  lui        s3, 985951
                  remu       s6, s3, t1
                  c.srai     s1, 28
                  sub        s0, t3, gp
                  slti       tp, a1, -167
                  slti       tp, a1, -167
                  srl        t1, tp, zero
                  lui        s3, 985951
                  c.sub      s0, s1
                  sltu       s3, a6, a4
                  srai       a4, a3, 0
                  mulhu      s4, a6, t3
                  andi       t0, a3, 147
                  c.addi4spn a2, sp, 528
                  mulhsu     tp, t5, a6
                  c.slli     t5, 22
                  c.lui      a6, 24
                  sltiu      s3, tp, 300
                  ori        tp, a0, -848
                  li         s6, 0x7616aea9 #start riscv_int_numeric_corner_stream_0
                  li         t5, 0xffffffff
                  li         s5, 0x0
                  li         s4, 0xffffffff
                  li         t2, 0x80000000
                  li         a4, 0x15ad0402
                  li         s7, 0x80000000
                  li         t0, 0x53566214
                  li         t3, 0xa62661f
                  li         gp, 0xffffffff
                  rem        a4, s4, a4
                  mulhu      s7, s6, t5
                  nop
                  mulhsu     s7, t5, gp
                  mulh       gp, s7, t0
                  auipc      t3, 11691
                  add        s5, s7, t5
                  nop
                  rem        a4, s4, a4
                  nop
                  nop
                  nop
                  sub        gp, a4, s5
                  addi       a4, s7, -40
                  remu       a4, gp, s6
                  remu       a4, gp, s6
                  nop #end riscv_int_numeric_corner_stream_0
                  div        s7, gp, a4
                  sltiu      s3, tp, 300
                  c.srai     s1, 28
                  c.srli     a4, 9
                  sll        s8, s0, s6
                  and        s6, t2, a4
                  c.addi     s9, -1
                  sltu       s3, a6, a4
                  c.add      t3, t1
                  c.slli     t5, 22
                  srai       a4, a3, 0
                  c.nop
                  c.sub      s0, s1
                  slli       a2, a4, 25
                  c.andi     s1, 31
                  auipc      s1, 11691
                  c.andi     s1, 31
                  or         a4, a4, zero
                  andi       t0, a3, 147
                  xori       t3, t1, -721
                  c.sub      s0, s1
                  srai       a4, a3, 0
                  sltiu      s3, tp, 300
                  srli       zero, a0, 13
                  div        s7, gp, a4
                  slt        a0, s5, s11
                  c.andi     s1, 31
                  sub        s0, t3, gp
                  lui        s3, 985951
                  sltu       s3, a6, a4
                  mulhu      s4, a6, t3
                  sltiu      s3, tp, 300
                  slti       tp, a1, -167
                  sltiu      s3, tp, 300
                  c.addi     s9, -1
                  li         a6, 0x80000000 #start riscv_int_numeric_corner_stream_35
                  li         s6, 0x80000000
                  li         a2, 0x0
                  li         gp, 0xffffffff
                  li         t5, 0x80000000
                  li         a0, 0x33b488ff
                  li         s2, 0x80000000
                  li         s3, 0x0
                  li         t1, 0xa27585b5
                  li         sp, 0xffffffff
                  rem        gp, s2, t1
                  add        s6, s3, t5
                  nop
                  nop
                  sub        t5, a6, t5
                  remu       t1, t5, a2
                  sub        t5, a6, t5
                  sub        t5, a6, t5
                  auipc      a2, 11691
                  div        a2, a0, gp
                  mul        a2, t1, a2
                  add        s6, s3, t5
                  mulhsu     t5, t5, gp
                  nop
                  nop
                  mulhsu     t5, t5, gp
                  mulhu      t5, s6, t5
                  add        s6, s3, t5
                  add        s6, s3, t5
                  nop #end riscv_int_numeric_corner_stream_35
                  slti       tp, a1, -167
                  auipc      s1, 11691
                  srli       zero, a0, 13
                  c.sub      s0, s1
                  auipc      s1, 11691
                  slt        a0, s5, s11
                  rem        a2, s2, s9
                  c.lui      a6, 24
                  c.srai     s1, 28
                  andi       t0, a3, 147
                  add        s4, a7, s6
                  nop
                  xori       t3, t1, -721
                  c.lui      a6, 24
                  andi       t0, a3, 147
                  c.srai     s1, 28
                  c.add      t3, t1
                  c.lui      a6, 24
                  c.srai     s1, 28
                  ori        tp, a0, -848
                  c.andi     s1, 31
                  c.li       s11, -1
                  c.addi     s9, -1
                  srli       zero, a0, 13
                  sll        s8, s0, s6
                  c.lui      a6, 24
                  slt        a0, s5, s11
                  sll        s8, s0, s6
                  c.addi     s9, -1
                  mulhu      s4, a6, t3
                  slti       tp, a1, -167
                  div        s7, gp, a4
                  c.xor      a4, a5
                  sll        s8, s0, s6
                  remu       s6, s3, t1
                  xor        s11, zero, s7
                  nop
                  lui        s3, 985951
                  mul        tp, s2, t5
                  c.add      t3, t1
                  add        s4, a7, s6
                  sub        s0, t3, gp
                  andi       t0, a3, 147
                  srai       a4, a3, 0
                  remu       s6, s3, t1
                  c.add      t3, t1
                  ori        tp, a0, -848
                  c.sub      s0, s1
                  c.nop
                  add        s4, a7, s6
                  c.addi     s9, -1
                  slti       tp, a1, -167
                  mul        tp, s2, t5
                  mulhu      s4, a6, t3
                  sltiu      s3, tp, 300
                  divu       tp, s5, t4
                  mulhu      s4, a6, t3
                  srli       zero, a0, 13
                  sra        s9, s4, t5
                  c.li       s11, -1
                  add        s4, a7, s6
                  rem        a2, s2, s9
                  c.addi     s9, -1
                  xor        s11, zero, s7
                  c.nop
                  addi       gp, s8, -298
                  c.and      a4, s1
                  mulhsu     tp, t5, a6
                  mulhsu     tp, t5, a6
                  c.and      a4, s1
                  xori       t3, t1, -721
                  div        s7, gp, a4
                  sltiu      s3, tp, 300
                  c.mv       a2, a0
                  slti       tp, a1, -167
                  sub        s0, t3, gp
                  sub        s0, t3, gp
                  c.mv       a2, a0
                  c.addi4spn a2, sp, 528
                  c.and      a4, s1
                  c.srli     a4, 9
                  remu       s6, s3, t1
                  c.li       s11, -1
                  srl        t1, tp, zero
                  remu       s6, s3, t1
                  mulh       s1, t4, s11
                  mulhu      s4, a6, t3
                  remu       s6, s3, t1
                  c.slli     t5, 22
                  c.sub      s0, s1
                  slli       a2, a4, 25
                  sll        s8, s0, s6
                  slti       tp, a1, -167
                  c.andi     s1, 31
                  srai       a4, a3, 0
                  c.addi16sp sp, -16
                  c.nop
                  c.addi     s9, -1
                  sll        s8, s0, s6
                  c.addi16sp sp, -16
                  c.mv       a2, a0
                  c.lui      a6, 24
                  mulh       s1, t4, s11
                  mulhsu     tp, t5, a6
                  auipc      s1, 11691
                  c.sub      s0, s1
                  c.add      t3, t1
                  slt        a0, s5, s11
                  slt        a0, s5, s11
                  auipc      s1, 11691
                  mulhsu     tp, t5, a6
                  srai       a4, a3, 0
                  slli       a2, a4, 25
                  c.addi16sp sp, -16
                  mul        tp, s2, t5
                  srl        t1, tp, zero
                  auipc      s1, 11691
                  slli       a2, a4, 25
                  slti       tp, a1, -167
                  sra        s9, s4, t5
                  div        s7, gp, a4
                  sll        s8, s0, s6
                  c.addi     s9, -1
                  slti       tp, a1, -167
                  c.sub      s0, s1
                  c.srai     s1, 28
                  mulhu      s4, a6, t3
                  c.and      a4, s1
                  xor        s11, zero, s7
                  slli       a2, a4, 25
                  divu       tp, s5, t4
                  c.srli     a4, 9
                  c.addi4spn a2, sp, 528
                  rem        a2, s2, s9
                  mulhsu     tp, t5, a6
                  c.andi     s1, 31
                  srai       a4, a3, 0
                  ori        tp, a0, -848
                  mul        tp, s2, t5
                  sub        s0, t3, gp
                  remu       s6, s3, t1
                  andi       t0, a3, 147
                  sltiu      s3, tp, 300
                  and        s6, t2, a4
                  c.and      a4, s1
                  sltu       s3, a6, a4
                  sltiu      s3, tp, 300
                  slt        a0, s5, s11
                  c.add      t3, t1
                  nop
                  or         a4, a4, zero
                  xori       t3, t1, -721
                  xor        s11, zero, s7
                  c.lui      a6, 24
                  c.slli     t5, 22
                  xor        s11, zero, s7
                  sra        s9, s4, t5
                  slli       a2, a4, 25
                  divu       tp, s5, t4
                  srl        t1, tp, zero
                  c.srli     a4, 9
                  srl        t1, tp, zero
                  sltiu      s3, tp, 300
                  mul        tp, s2, t5
                  c.and      a4, s1
                  c.li       s11, -1
                  c.li       s11, -1
                  c.or       a0, a2
                  c.srai     s1, 28
                  or         a4, a4, zero
                  c.xor      a4, a5
                  mulh       s1, t4, s11
                  c.li       s11, -1
                  lui        s3, 985951
                  c.addi4spn a2, sp, 528
                  c.srli     a4, 9
                  andi       t0, a3, 147
                  c.mv       a2, a0
                  and        s6, t2, a4
                  slt        a0, s5, s11
                  nop
                  slli       a2, a4, 25
                  slti       tp, a1, -167
                  add        s4, a7, s6
                  divu       tp, s5, t4
                  slti       tp, a1, -167
                  mul        tp, s2, t5
                  ori        tp, a0, -848
                  c.addi     s9, -1
                  sltu       s3, a6, a4
                  c.addi4spn a2, sp, 528
                  slli       a2, a4, 25
                  c.li       s11, -1
                  mulhsu     tp, t5, a6
                  andi       t0, a3, 147
                  c.mv       a2, a0
                  c.srli     a4, 9
                  slti       tp, a1, -167
                  xori       t3, t1, -721
                  c.addi     s9, -1
                  divu       tp, s5, t4
                  sub        s0, t3, gp
                  srai       a4, a3, 0
                  c.addi4spn a2, sp, 528
                  andi       t0, a3, 147
                  sltu       s3, a6, a4
                  c.srli     a4, 9
                  and        s6, t2, a4
                  c.nop
                  mulhu      s4, a6, t3
                  c.sub      s0, s1
                  sltu       s3, a6, a4
                  and        s6, t2, a4
                  slti       tp, a1, -167
                  c.and      a4, s1
                  c.lui      a6, 24
                  c.srli     a4, 9
                  div        s7, gp, a4
                  addi       gp, s8, -298
                  xori       t3, t1, -721
                  sll        s8, s0, s6
                  c.or       a0, a2
                  c.srai     s1, 28
                  c.add      t3, t1
                  mulhsu     tp, t5, a6
                  add        s4, a7, s6
                  mulhsu     tp, t5, a6
                  c.srai     s1, 28
                  sra        s9, s4, t5
                  sll        s8, s0, s6
                  xor        s11, zero, s7
                  nop
                  mulhsu     tp, t5, a6
                  lui        s3, 985951
                  xor        s11, zero, s7
                  mulh       s1, t4, s11
                  srai       a4, a3, 0
                  c.lui      a6, 24
                  sra        s9, s4, t5
                  and        s6, t2, a4
                  c.li       s11, -1
                  li         s7, 0x0 #start riscv_int_numeric_corner_stream_38
                  li         s0, 0xedd3f26b
                  li         tp, 0x0
                  li         gp, 0x0
                  li         t0, 0x0
                  li         s8, 0xffffffff
                  li         s6, 0xffffffff
                  li         s11, 0x6e0f303b
                  li         t4, 0xffffffff
                  li         t5, 0xce724ebd
                  remu       s8, s11, tp
                  sub        s11, gp, s8
                  mulhu      s7, s6, t5
                  nop
                  div        s8, tp, t0
                  nop
                  add        s6, tp, t5
                  nop
                  sub        s11, gp, s8
                  nop
                  nop
                  addi       t0, s11, -40
                  nop
                  add        s6, tp, t5
                  divu       s0, gp, s8
                  lui        gp, 985951
                  sub        s11, gp, s8
                  nop
                  nop
                  mulhu      s7, s6, t5
                  mul        s8, s6, s0
                  sub        s11, gp, s8
                  mulh       t0, s7, tp
                  rem        t4, s8, gp
                  mulhsu     t5, s7, gp
                  nop
                  mulhu      s7, s6, t5
                  addi       t0, s11, -40 #end riscv_int_numeric_corner_stream_38
                  or         a4, a4, zero
                  c.sub      s0, s1
                  c.sub      s0, s1
                  c.or       a0, a2
                  c.li       s11, -1
                  c.srai     s1, 28
                  rem        a2, s2, s9
                  c.slli     t5, 22
                  c.andi     s1, 31
                  mulhsu     tp, t5, a6
                  div        s7, gp, a4
                  srli       zero, a0, 13
                  srli       zero, a0, 13
                  c.addi16sp sp, -16
                  c.or       a0, a2
                  rem        a2, s2, s9
                  xor        s11, zero, s7
                  lui        s3, 985951
                  xori       t3, t1, -721
                  c.xor      a4, a5
                  c.slli     t5, 22
                  sra        s9, s4, t5
                  sltiu      s3, tp, 300
                  li         s2, 0x0 #start riscv_int_numeric_corner_stream_2
                  li         sp, 0x80000000
                  li         s10, 0x80000000
                  li         t4, 0x5378c6be
                  li         a4, 0x80000000
                  li         s0, 0x80000000
                  li         s8, 0x63562bed
                  li         s3, 0x80000000
                  li         t1, 0xffffffff
                  li         s11, 0xffffffff
                  remu       s2, s10, a4
                  lui        s3, 985951
                  auipc      s0, 11691
                  nop
                  nop
                  nop
                  nop
                  lui        s3, 985951
                  sub        t1, sp, s8
                  auipc      s0, 11691
                  mul        t1, t4, a4
                  nop
                  sub        t1, sp, s8
                  add        t1, t4, a4
                  rem        t1, s2, a4
                  nop
                  nop
                  mulhu      t4, t4, t4
                  add        t1, t4, a4
                  nop
                  remu       s2, s10, a4
                  nop
                  divu       t4, a4, s8
                  lui        s3, 985951 #end riscv_int_numeric_corner_stream_2
                  c.addi     s9, -1
                  div        s7, gp, a4
                  andi       t0, a3, 147
                  sltiu      s3, tp, 300
                  or         a4, a4, zero
                  c.addi16sp sp, -16
                  andi       t0, a3, 147
                  c.srai     s1, 28
                  c.add      t3, t1
                  auipc      s1, 11691
                  andi       t0, a3, 147
                  remu       s6, s3, t1
                  c.and      a4, s1
                  c.addi4spn a2, sp, 528
                  c.mv       a2, a0
                  c.srli     a4, 9
                  c.slli     t5, 22
                  mulhu      s4, a6, t3
                  mulh       s1, t4, s11
                  or         a4, a4, zero
                  c.li       s11, -1
                  mulhu      s4, a6, t3
                  sll        s8, s0, s6
                  div        s7, gp, a4
                  slti       tp, a1, -167
                  srli       zero, a0, 13
                  add        s4, a7, s6
                  divu       tp, s5, t4
                  remu       s6, s3, t1
                  c.and      a4, s1
                  div        s7, gp, a4
                  c.lui      a6, 24
                  sltu       s3, a6, a4
                  c.sub      s0, s1
                  c.add      t3, t1
                  c.and      a4, s1
                  sltu       s3, a6, a4
                  c.lui      a6, 24
                  or         a4, a4, zero
                  mulh       s1, t4, s11
                  rem        a2, s2, s9
                  c.andi     s1, 31
                  c.slli     t5, 22
                  divu       tp, s5, t4
                  xor        s11, zero, s7
                  and        s6, t2, a4
                  sltiu      s3, tp, 300
                  mulh       s1, t4, s11
                  xori       t3, t1, -721
                  xor        s11, zero, s7
                  mulhu      s4, a6, t3
                  c.srai     s1, 28
                  divu       tp, s5, t4
                  c.and      a4, s1
                  xori       t3, t1, -721
                  c.or       a0, a2
                  remu       s6, s3, t1
                  c.srli     a4, 9
                  c.slli     t5, 22
                  c.sub      s0, s1
                  c.andi     s1, 31
                  c.li       s11, -1
                  xori       t3, t1, -721
                  divu       tp, s5, t4
                  mulhsu     tp, t5, a6
                  xor        s11, zero, s7
                  c.addi16sp sp, -16
                  c.add      t3, t1
                  rem        a2, s2, s9
                  sra        s9, s4, t5
                  c.srai     s1, 28
                  slti       tp, a1, -167
                  sra        s9, s4, t5
                  sll        s8, s0, s6
                  sltiu      s3, tp, 300
                  andi       t0, a3, 147
                  nop
                  c.addi     s9, -1
                  c.or       a0, a2
                  c.srai     s1, 28
                  ori        tp, a0, -848
                  c.srai     s1, 28
                  or         a4, a4, zero
                  c.li       s11, -1
                  mulh       s1, t4, s11
                  c.addi4spn a2, sp, 528
                  c.li       s11, -1
                  ori        tp, a0, -848
                  c.or       a0, a2
                  c.addi     s9, -1
                  xor        s11, zero, s7
                  add        s4, a7, s6
                  c.andi     s1, 31
                  remu       s6, s3, t1
                  mulh       s1, t4, s11
                  xor        s11, zero, s7
                  c.mv       a2, a0
                  c.add      t3, t1
                  c.andi     s1, 31
                  nop
                  c.srli     a4, 9
                  addi       gp, s8, -298
                  remu       s6, s3, t1
                  c.sub      s0, s1
                  c.or       a0, a2
                  xor        s11, zero, s7
                  ori        tp, a0, -848
                  c.slli     t5, 22
                  nop
                  c.add      t3, t1
                  c.srai     s1, 28
                  c.srai     s1, 28
                  slt        a0, s5, s11
                  xor        s11, zero, s7
                  c.addi16sp sp, -16
                  or         a4, a4, zero
                  c.lui      a6, 24
                  mulhu      s4, a6, t3
                  slti       tp, a1, -167
                  c.addi4spn a2, sp, 528
                  sub        s0, t3, gp
                  c.mv       a2, a0
                  slti       tp, a1, -167
                  and        s6, t2, a4
                  c.or       a0, a2
                  divu       tp, s5, t4
                  c.nop
                  mul        tp, s2, t5
                  c.sub      s0, s1
                  srai       a4, a3, 0
                  c.li       s11, -1
                  c.lui      a6, 24
                  c.xor      a4, a5
                  rem        a2, s2, s9
                  or         a4, a4, zero
                  c.slli     t5, 22
                  sltu       s3, a6, a4
                  sltu       s3, a6, a4
                  div        s7, gp, a4
                  mulhsu     tp, t5, a6
                  rem        a2, s2, s9
                  c.addi16sp sp, -16
                  c.xor      a4, a5
                  c.or       a0, a2
                  c.or       a0, a2
                  addi       gp, s8, -298
                  auipc      s1, 11691
                  srai       a4, a3, 0
                  c.addi16sp sp, -16
                  srl        t1, tp, zero
                  c.addi     s9, -1
                  or         a4, a4, zero
                  lui        s3, 985951
                  srli       zero, a0, 13
                  addi       gp, s8, -298
                  c.andi     s1, 31
                  c.mv       a2, a0
                  addi       gp, s8, -298
                  c.or       a0, a2
                  andi       t0, a3, 147
                  sltu       s3, a6, a4
                  sra        s9, s4, t5
                  srl        t1, tp, zero
                  sltu       s3, a6, a4
                  srai       a4, a3, 0
                  xori       t3, t1, -721
                  mulhu      s4, a6, t3
                  sll        s8, s0, s6
                  c.xor      a4, a5
                  div        s7, gp, a4
                  c.addi4spn a2, sp, 528
                  div        s7, gp, a4
                  c.li       s11, -1
                  ori        tp, a0, -848
                  c.addi16sp sp, -16
                  c.slli     t5, 22
                  sltiu      s3, tp, 300
                  c.slli     t5, 22
                  c.addi16sp sp, -16
                  slt        a0, s5, s11
                  lui        s3, 985951
                  remu       s6, s3, t1
                  c.addi     s9, -1
                  c.li       s11, -1
                  mulh       s1, t4, s11
                  c.srai     s1, 28
                  c.addi4spn a2, sp, 528
                  and        s6, t2, a4
                  slti       tp, a1, -167
                  div        s7, gp, a4
                  c.andi     s1, 31
                  c.mv       a2, a0
                  div        s7, gp, a4
                  ori        tp, a0, -848
                  mulhsu     tp, t5, a6
                  sltiu      s3, tp, 300
                  add        s4, a7, s6
                  lui        s3, 985951
                  ori        tp, a0, -848
                  sra        s9, s4, t5
                  srai       a4, a3, 0
                  div        s7, gp, a4
                  c.lui      a6, 24
                  c.addi4spn a2, sp, 528
                  c.add      t3, t1
                  c.li       s11, -1
                  ori        tp, a0, -848
                  rem        a2, s2, s9
                  srai       a4, a3, 0
                  c.addi16sp sp, -16
                  remu       s6, s3, t1
                  mulhu      s4, a6, t3
                  slt        a0, s5, s11
                  mulhsu     tp, t5, a6
                  divu       tp, s5, t4
                  mulh       s1, t4, s11
                  div        s7, gp, a4
                  c.and      a4, s1
                  c.srli     a4, 9
                  xor        s11, zero, s7
                  ori        tp, a0, -848
                  c.addi4spn a2, sp, 528
                  c.li       s11, -1
                  divu       tp, s5, t4
                  c.srli     a4, 9
                  auipc      s1, 11691
                  or         a4, a4, zero
                  sltu       s3, a6, a4
                  c.mv       a2, a0
                  auipc      s1, 11691
                  and        s6, t2, a4
                  c.srai     s1, 28
                  c.srli     a4, 9
                  c.li       s11, -1
                  srl        t1, tp, zero
                  mulh       s1, t4, s11
                  c.andi     s1, 31
                  andi       t0, a3, 147
                  slt        a0, s5, s11
                  auipc      s1, 11691
                  c.nop
                  c.slli     t5, 22
                  c.lui      a6, 24
                  mul        tp, s2, t5
                  slt        a0, s5, s11
                  nop
                  auipc      s1, 11691
                  xori       t3, t1, -721
                  mulhu      s4, a6, t3
                  c.addi16sp sp, -16
                  mulh       s1, t4, s11
                  or         a4, a4, zero
                  add        s4, a7, s6
                  c.srli     a4, 9
                  mulhsu     tp, t5, a6
                  sltu       s3, a6, a4
                  ori        tp, a0, -848
                  c.andi     s1, 31
                  sra        s9, s4, t5
                  srli       zero, a0, 13
                  sltiu      s3, tp, 300
                  or         a4, a4, zero
                  srl        t1, tp, zero
                  sub        s0, t3, gp
                  c.lui      a6, 24
                  remu       s6, s3, t1
                  srli       zero, a0, 13
                  slt        a0, s5, s11
                  c.srli     a4, 9
                  c.addi4spn a2, sp, 528
                  mulh       s1, t4, s11
                  add        s4, a7, s6
                  sll        s8, s0, s6
                  c.addi4spn a2, sp, 528
                  srai       a4, a3, 0
                  c.addi16sp sp, -16
                  sra        s9, s4, t5
                  c.and      a4, s1
                  c.add      t3, t1
                  mulh       s1, t4, s11
                  c.xor      a4, a5
                  sra        s9, s4, t5
                  srl        t1, tp, zero
                  rem        a2, s2, s9
                  andi       t0, a3, 147
                  c.add      t3, t1
                  mul        tp, s2, t5
                  c.addi4spn a2, sp, 528
                  c.xor      a4, a5
                  ori        tp, a0, -848
                  sub        s0, t3, gp
                  nop
                  c.srli     a4, 9
                  addi       gp, s8, -298
                  rem        a2, s2, s9
                  remu       s6, s3, t1
                  c.slli     t5, 22
                  c.addi     s9, -1
                  auipc      s1, 11691
                  c.srai     s1, 28
                  slt        a0, s5, s11
                  andi       t0, a3, 147
                  c.srli     a4, 9
                  sll        s8, s0, s6
                  slt        a0, s5, s11
                  slt        a0, s5, s11
                  c.mv       a2, a0
                  add        s4, a7, s6
                  c.slli     t5, 22
                  sltiu      s3, tp, 300
                  andi       t0, a3, 147
                  srli       zero, a0, 13
                  srai       a4, a3, 0
                  c.li       s11, -1
                  div        s7, gp, a4
                  sub        s0, t3, gp
                  mulhu      s4, a6, t3
                  srai       a4, a3, 0
                  add        s4, a7, s6
                  sltu       s3, a6, a4
                  andi       t0, a3, 147
                  addi       gp, s8, -298
                  mul        tp, s2, t5
                  c.mv       a2, a0
                  c.addi     s9, -1
                  nop
                  mulh       s1, t4, s11
                  c.sub      s0, s1
                  xor        s11, zero, s7
                  mulhsu     tp, t5, a6
                  slli       a2, a4, 25
                  srli       zero, a0, 13
                  srl        t1, tp, zero
                  slt        a0, s5, s11
                  c.sub      s0, s1
                  c.addi4spn a2, sp, 528
                  sltiu      s3, tp, 300
                  c.mv       a2, a0
                  c.or       a0, a2
                  sll        s8, s0, s6
                  c.srai     s1, 28
                  div        s7, gp, a4
                  xor        s11, zero, s7
                  xor        s11, zero, s7
                  srli       zero, a0, 13
                  c.addi16sp sp, -16
                  sub        s0, t3, gp
                  mulh       s1, t4, s11
                  slli       a2, a4, 25
                  mulhsu     tp, t5, a6
                  remu       s6, s3, t1
                  c.li       s11, -1
                  sltu       s3, a6, a4
                  c.addi16sp sp, -16
                  c.lui      a6, 24
                  sll        s8, s0, s6
                  c.nop
                  c.xor      a4, a5
                  addi       gp, s8, -298
                  slti       tp, a1, -167
                  xor        s11, zero, s7
                  xori       t3, t1, -721
                  c.slli     t5, 22
                  sltiu      s3, tp, 300
                  c.lui      a6, 24
                  and        s6, t2, a4
                  andi       t0, a3, 147
                  c.sub      s0, s1
                  div        s7, gp, a4
                  c.srai     s1, 28
                  mulhsu     tp, t5, a6
                  c.and      a4, s1
                  c.add      t3, t1
                  c.or       a0, a2
                  c.addi     s9, -1
                  sra        s9, s4, t5
                  xori       t3, t1, -721
                  sll        s8, s0, s6
                  sll        s8, s0, s6
                  sub        s0, t3, gp
                  c.or       a0, a2
                  sltu       s3, a6, a4
                  xor        s11, zero, s7
                  xor        s11, zero, s7
                  c.srli     a4, 9
                  xor        s11, zero, s7
                  c.slli     t5, 22
                  xor        s11, zero, s7
                  c.or       a0, a2
                  c.or       a0, a2
                  sltu       s3, a6, a4
                  remu       s6, s3, t1
                  c.andi     s1, 31
                  slti       tp, a1, -167
                  srl        t1, tp, zero
                  c.andi     s1, 31
                  addi       gp, s8, -298
                  c.nop
                  mulh       s1, t4, s11
                  add        s4, a7, s6
                  c.addi     s9, -1
                  srl        t1, tp, zero
                  c.li       s11, -1
                  mulh       s1, t4, s11
                  c.mv       a2, a0
                  sltu       s3, a6, a4
                  mulh       s1, t4, s11
                  xori       t3, t1, -721
                  srai       a4, a3, 0
                  remu       s6, s3, t1
                  slli       a2, a4, 25
                  c.addi16sp sp, -16
                  lui        s3, 985951
                  c.sub      s0, s1
                  addi       gp, s8, -298
                  add        s4, a7, s6
                  addi       gp, s8, -298
                  add        s4, a7, s6
                  div        s7, gp, a4
                  sub        s0, t3, gp
                  sub        s0, t3, gp
                  c.andi     s1, 31
                  c.or       a0, a2
                  c.lui      a6, 24
                  slli       a2, a4, 25
                  ori        tp, a0, -848
                  ori        tp, a0, -848
                  or         a4, a4, zero
                  addi       gp, s8, -298
                  sra        s9, s4, t5
                  or         a4, a4, zero
                  srl        t1, tp, zero
                  xor        s11, zero, s7
                  c.sub      s0, s1
                  c.mv       a2, a0
                  sub        s0, t3, gp
                  add        s4, a7, s6
                  ori        tp, a0, -848
                  rem        a2, s2, s9
                  sll        s8, s0, s6
                  sub        s0, t3, gp
                  remu       s6, s3, t1
                  sub        s0, t3, gp
                  srai       a4, a3, 0
                  xori       t3, t1, -721
                  srl        t1, tp, zero
                  c.add      t3, t1
                  c.or       a0, a2
                  ori        tp, a0, -848
                  and        s6, t2, a4
                  sra        s9, s4, t5
                  srai       a4, a3, 0
                  xor        s11, zero, s7
                  c.mv       a2, a0
                  srl        t1, tp, zero
                  andi       t0, a3, 147
                  remu       s6, s3, t1
                  c.lui      a6, 24
                  c.and      a4, s1
                  xor        s11, zero, s7
                  c.slli     t5, 22
                  rem        a2, s2, s9
                  mul        tp, s2, t5
                  c.sub      s0, s1
                  auipc      s1, 11691
                  add        s4, a7, s6
                  div        s7, gp, a4
                  xori       t3, t1, -721
                  mulhu      s4, a6, t3
                  c.addi     s9, -1
                  c.and      a4, s1
                  c.andi     s1, 31
                  c.mv       a2, a0
                  xori       t3, t1, -721
                  mulhsu     tp, t5, a6
                  c.mv       a2, a0
                  andi       t0, a3, 147
                  slli       a2, a4, 25
                  rem        a2, s2, s9
                  sub        s0, t3, gp
                  c.andi     s1, 31
                  c.nop
                  slli       a2, a4, 25
                  ori        tp, a0, -848
                  add        s4, a7, s6
                  srli       zero, a0, 13
                  c.srli     a4, 9
                  ori        tp, a0, -848
                  mulhu      s4, a6, t3
                  c.sub      s0, s1
                  remu       s6, s3, t1
                  xor        s11, zero, s7
                  or         a4, a4, zero
                  lui        s3, 985951
                  c.addi16sp sp, -16
                  c.srai     s1, 28
                  c.mv       a2, a0
                  rem        a2, s2, s9
                  slti       tp, a1, -167
                  remu       s6, s3, t1
                  slti       tp, a1, -167
                  divu       tp, s5, t4
                  srai       a4, a3, 0
                  remu       s6, s3, t1
                  c.mv       a2, a0
                  c.andi     s1, 31
                  sll        s8, s0, s6
                  c.or       a0, a2
                  c.addi16sp sp, -16
                  c.xor      a4, a5
                  sltiu      s3, tp, 300
                  mul        tp, s2, t5
                  auipc      s1, 11691
                  c.mv       a2, a0
                  c.xor      a4, a5
                  mul        tp, s2, t5
                  c.srli     a4, 9
                  sll        s8, s0, s6
                  c.addi16sp sp, -16
                  or         a4, a4, zero
                  c.sub      s0, s1
                  sll        s8, s0, s6
                  divu       tp, s5, t4
                  rem        a2, s2, s9
                  c.addi4spn a2, sp, 528
                  c.and      a4, s1
                  c.andi     s1, 31
                  sub        s0, t3, gp
                  c.slli     t5, 22
                  sub        s0, t3, gp
                  c.addi4spn a2, sp, 528
                  sltiu      s3, tp, 300
                  c.xor      a4, a5
                  c.lui      a6, 24
                  c.nop
                  c.mv       a2, a0
                  addi       gp, s8, -298
                  slli       a2, a4, 25
                  c.mv       a2, a0
                  addi       gp, s8, -298
                  ori        tp, a0, -848
                  mulhu      s4, a6, t3
                  add        s4, a7, s6
                  divu       tp, s5, t4
                  nop
                  lui        s3, 985951
                  c.srli     a4, 9
                  sub        s0, t3, gp
                  c.addi4spn a2, sp, 528
                  slli       a2, a4, 25
                  c.nop
                  srl        t1, tp, zero
                  c.add      t3, t1
                  c.addi16sp sp, -16
                  c.addi16sp sp, -16
                  sltiu      s3, tp, 300
                  slti       tp, a1, -167
                  c.addi4spn a2, sp, 528
                  rem        a2, s2, s9
                  or         a4, a4, zero
                  mulhu      s4, a6, t3
                  c.slli     t5, 22
                  c.and      a4, s1
                  c.mv       a2, a0
                  mulhu      s4, a6, t3
                  mulhu      s4, a6, t3
                  sra        s9, s4, t5
                  slti       tp, a1, -167
                  srl        t1, tp, zero
                  auipc      s1, 11691
                  c.lui      a6, 24
                  addi       gp, s8, -298
                  sltiu      s3, tp, 300
                  c.or       a0, a2
                  remu       s6, s3, t1
                  mulh       s1, t4, s11
                  divu       tp, s5, t4
                  div        s7, gp, a4
                  srai       a4, a3, 0
                  sltiu      s3, tp, 300
                  c.addi4spn a2, sp, 528
                  lui        s3, 985951
                  c.srli     a4, 9
                  divu       tp, s5, t4
                  nop
                  ori        tp, a0, -848
                  c.or       a0, a2
                  c.srli     a4, 9
                  lui        s3, 985951
                  c.mv       a2, a0
                  c.add      t3, t1
                  auipc      s1, 11691
                  c.srli     a4, 9
                  c.li       s11, -1
                  sra        s9, s4, t5
                  c.xor      a4, a5
                  c.and      a4, s1
                  srl        t1, tp, zero
                  mulhu      s4, a6, t3
                  c.andi     s1, 31
                  mul        tp, s2, t5
                  c.slli     t5, 22
                  srai       a4, a3, 0
                  rem        a2, s2, s9
                  sra        s9, s4, t5
                  auipc      s1, 11691
                  c.addi16sp sp, -16
                  xor        s11, zero, s7
                  c.srli     a4, 9
                  xor        s11, zero, s7
                  xor        s11, zero, s7
                  divu       tp, s5, t4
                  slli       a2, a4, 25
                  c.nop
                  lui        s3, 985951
                  mulh       s1, t4, s11
                  addi       gp, s8, -298
                  remu       s6, s3, t1
                  c.srai     s1, 28
                  c.addi16sp sp, -16
                  c.add      t3, t1
                  c.li       s11, -1
                  mulh       s1, t4, s11
                  rem        a2, s2, s9
                  sltu       s3, a6, a4
                  mulhsu     tp, t5, a6
                  srl        t1, tp, zero
                  nop
                  c.or       a0, a2
                  c.xor      a4, a5
                  and        s6, t2, a4
                  srli       zero, a0, 13
                  remu       s6, s3, t1
                  rem        a2, s2, s9
                  or         a4, a4, zero
                  xori       t3, t1, -721
                  and        s6, t2, a4
                  srl        t1, tp, zero
                  c.slli     t5, 22
                  c.add      t3, t1
                  slti       tp, a1, -167
                  nop
                  mulhu      s4, a6, t3
                  c.or       a0, a2
                  sub        s0, t3, gp
                  c.srai     s1, 28
                  mul        tp, s2, t5
                  c.srai     s1, 28
                  c.srai     s1, 28
                  c.slli     t5, 22
                  c.andi     s1, 31
                  c.and      a4, s1
                  and        s6, t2, a4
                  c.or       a0, a2
                  sltiu      s3, tp, 300
                  auipc      s1, 11691
                  divu       tp, s5, t4
                  c.and      a4, s1
                  srli       zero, a0, 13
                  c.addi4spn a2, sp, 528
                  slli       a2, a4, 25
                  and        s6, t2, a4
                  srl        t1, tp, zero
                  ori        tp, a0, -848
                  slli       a2, a4, 25
                  and        s6, t2, a4
                  c.mv       a2, a0
                  srli       zero, a0, 13
                  c.and      a4, s1
                  nop
                  auipc      s1, 11691
                  addi       gp, s8, -298
                  remu       s6, s3, t1
                  slli       a2, a4, 25
                  mulh       s1, t4, s11
                  c.addi4spn a2, sp, 528
                  add        s4, a7, s6
                  slt        a0, s5, s11
                  remu       s6, s3, t1
                  srli       zero, a0, 13
                  sltiu      s3, tp, 300
                  auipc      s1, 11691
                  srli       zero, a0, 13
                  srli       zero, a0, 13
                  mul        tp, s2, t5
                  ori        tp, a0, -848
                  c.or       a0, a2
                  srai       a4, a3, 0
                  sltiu      s3, tp, 300
                  slti       tp, a1, -167
                  sub        s0, t3, gp
                  mul        tp, s2, t5
                  c.addi4spn a2, sp, 528
                  auipc      s1, 11691
                  mul        tp, s2, t5
                  c.xor      a4, a5
                  andi       t0, a3, 147
                  xori       t3, t1, -721
                  c.add      t3, t1
                  div        s7, gp, a4
                  c.srli     a4, 9
                  or         a4, a4, zero
                  c.srli     a4, 9
                  div        s7, gp, a4
                  c.andi     s1, 31
                  slti       tp, a1, -167
                  sra        s9, s4, t5
                  andi       t0, a3, 147
                  divu       tp, s5, t4
                  srli       zero, a0, 13
                  slt        a0, s5, s11
                  c.add      t3, t1
                  mulh       s1, t4, s11
                  slti       tp, a1, -167
                  srli       zero, a0, 13
                  addi       gp, s8, -298
                  srl        t1, tp, zero
                  slti       tp, a1, -167
                  nop
                  c.sub      s0, s1
                  c.xor      a4, a5
                  c.addi16sp sp, -16
                  mulh       s1, t4, s11
                  andi       t0, a3, 147
                  auipc      s1, 11691
                  c.sub      s0, s1
                  mulhsu     tp, t5, a6
                  or         a4, a4, zero
                  c.xor      a4, a5
                  c.slli     t5, 22
                  and        s6, t2, a4
                  mulhu      s4, a6, t3
                  srai       a4, a3, 0
                  sub        s0, t3, gp
                  c.nop
                  srl        t1, tp, zero
                  xori       t3, t1, -721
                  mulhu      s4, a6, t3
                  lui        s3, 985951
                  c.nop
                  c.li       s11, -1
                  mulh       s1, t4, s11
                  lui        s3, 985951
                  mul        tp, s2, t5
                  c.lui      a6, 24
                  c.sub      s0, s1
                  rem        a2, s2, s9
                  c.and      a4, s1
                  slt        a0, s5, s11
                  slli       a2, a4, 25
                  sltiu      s3, tp, 300
                  slli       a2, a4, 25
                  andi       t0, a3, 147
                  lui        s3, 985951
                  addi       gp, s8, -298
                  remu       s6, s3, t1
                  c.or       a0, a2
                  auipc      s1, 11691
                  c.andi     s1, 31
                  c.addi     s9, -1
                  c.add      t3, t1
                  c.addi     s9, -1
                  c.or       a0, a2
                  c.sub      s0, s1
                  c.addi     s9, -1
                  c.nop
                  lui        s3, 985951
                  sra        s9, s4, t5
                  andi       t0, a3, 147
                  sltiu      s3, tp, 300
                  c.add      t3, t1
                  xor        s11, zero, s7
                  div        s7, gp, a4
                  c.li       s11, -1
                  sll        s8, s0, s6
                  addi       gp, s8, -298
                  c.srai     s1, 28
                  c.nop
                  c.srli     a4, 9
                  andi       t0, a3, 147
                  c.li       s11, -1
                  addi       gp, s8, -298
                  c.add      t3, t1
                  andi       t0, a3, 147
                  sltu       s3, a6, a4
                  c.addi16sp sp, -16
                  sltiu      s3, tp, 300
                  sub        s0, t3, gp
                  slt        a0, s5, s11
                  c.and      a4, s1
                  or         a4, a4, zero
                  c.add      t3, t1
                  sub        s0, t3, gp
                  sll        s8, s0, s6
                  xori       t3, t1, -721
                  c.addi     s9, -1
                  slli       a2, a4, 25
                  add        s4, a7, s6
                  sltiu      s3, tp, 300
                  slt        a0, s5, s11
                  or         a4, a4, zero
                  c.addi16sp sp, -16
                  mulhsu     tp, t5, a6
                  nop
                  srl        t1, tp, zero
                  sll        s8, s0, s6
                  c.slli     t5, 22
                  srli       zero, a0, 13
                  addi       gp, s8, -298
                  c.andi     s1, 31
                  xor        s11, zero, s7
                  c.srli     a4, 9
                  c.andi     s1, 31
                  sub        s0, t3, gp
                  c.andi     s1, 31
                  add        s4, a7, s6
                  xor        s11, zero, s7
                  c.add      t3, t1
                  remu       s6, s3, t1
                  c.sub      s0, s1
                  add        s4, a7, s6
                  auipc      s1, 11691
                  xor        s11, zero, s7
                  c.sub      s0, s1
                  slti       tp, a1, -167
                  c.addi4spn a2, sp, 528
                  auipc      s1, 11691
                  c.or       a0, a2
                  srli       zero, a0, 13
                  remu       s6, s3, t1
                  c.addi4spn a2, sp, 528
                  slt        a0, s5, s11
                  mul        tp, s2, t5
                  sub        s0, t3, gp
                  c.and      a4, s1
                  and        s6, t2, a4
                  srl        t1, tp, zero
                  c.li       s11, -1
                  slti       tp, a1, -167
                  c.addi4spn a2, sp, 528
                  c.addi4spn a2, sp, 528
                  nop
                  sltiu      s3, tp, 300
                  sub        s0, t3, gp
                  mulhu      s4, a6, t3
                  slli       a2, a4, 25
                  sra        s9, s4, t5
                  c.srai     s1, 28
                  c.addi4spn a2, sp, 528
                  c.lui      a6, 24
                  sra        s9, s4, t5
                  divu       tp, s5, t4
                  slli       a2, a4, 25
                  remu       s6, s3, t1
                  c.add      t3, t1
                  c.srli     a4, 9
                  or         a4, a4, zero
                  c.add      t3, t1
                  auipc      s1, 11691
                  lui        s3, 985951
                  srli       zero, a0, 13
                  c.slli     t5, 22
                  auipc      s1, 11691
                  add        s4, a7, s6
                  andi       t0, a3, 147
                  c.slli     t5, 22
                  sll        s8, s0, s6
                  slli       a2, a4, 25
                  c.nop
                  c.srai     s1, 28
                  xori       t3, t1, -721
                  or         a4, a4, zero
                  c.lui      a6, 24
                  slti       tp, a1, -167
                  c.lui      a6, 24
                  mulhsu     tp, t5, a6
                  c.add      t3, t1
                  srli       zero, a0, 13
                  c.sub      s0, s1
                  c.sub      s0, s1
                  divu       tp, s5, t4
                  mulh       s1, t4, s11
                  srl        t1, tp, zero
                  mulh       s1, t4, s11
                  mulhsu     tp, t5, a6
                  addi       gp, s8, -298
                  c.or       a0, a2
                  sll        s8, s0, s6
                  c.slli     t5, 22
                  mulh       s1, t4, s11
                  or         a4, a4, zero
                  slli       a2, a4, 25
                  slti       tp, a1, -167
                  mulhu      s4, a6, t3
                  remu       s6, s3, t1
                  xor        s11, zero, s7
                  lui        s3, 985951
                  c.andi     s1, 31
                  c.and      a4, s1
                  sll        s8, s0, s6
                  remu       s6, s3, t1
                  c.li       s11, -1
                  auipc      s1, 11691
                  c.add      t3, t1
                  sub        s0, t3, gp
                  slt        a0, s5, s11
                  c.sub      s0, s1
                  c.srai     s1, 28
                  addi       gp, s8, -298
                  andi       t0, a3, 147
                  addi       gp, s8, -298
                  xori       t3, t1, -721
                  rem        a2, s2, s9
                  c.nop
                  nop
                  mulhsu     tp, t5, a6
                  sub        s0, t3, gp
                  c.addi     s9, -1
                  srli       zero, a0, 13
                  c.nop
                  andi       t0, a3, 147
                  c.li       s11, -1
                  c.nop
                  c.lui      a6, 24
                  mul        tp, s2, t5
                  and        s6, t2, a4
                  slti       tp, a1, -167
                  nop
                  slti       tp, a1, -167
                  sltiu      s3, tp, 300
                  c.addi4spn a2, sp, 528
                  slli       a2, a4, 25
                  andi       t0, a3, 147
                  lui        s3, 985951
                  c.addi     s9, -1
                  xor        s11, zero, s7
                  slti       tp, a1, -167
                  c.xor      a4, a5
                  div        s7, gp, a4
                  ori        tp, a0, -848
                  div        s7, gp, a4
                  sub        s0, t3, gp
                  sltiu      s3, tp, 300
                  xor        s11, zero, s7
                  mulh       s1, t4, s11
                  c.add      t3, t1
                  c.sub      s0, s1
                  slti       tp, a1, -167
                  c.andi     s1, 31
                  sll        s8, s0, s6
                  c.andi     s1, 31
                  sra        s9, s4, t5
                  rem        a2, s2, s9
                  sub        s0, t3, gp
                  mulhsu     tp, t5, a6
                  add        s4, a7, s6
                  xor        s11, zero, s7
                  sub        s0, t3, gp
                  rem        a2, s2, s9
                  auipc      s1, 11691
                  divu       tp, s5, t4
                  c.xor      a4, a5
                  c.srli     a4, 9
                  c.or       a0, a2
                  c.add      t3, t1
                  c.mv       a2, a0
                  ori        tp, a0, -848
                  slt        a0, s5, s11
                  mulh       s1, t4, s11
                  addi       gp, s8, -298
                  lui        s3, 985951
                  div        s7, gp, a4
                  rem        a2, s2, s9
                  c.addi     s9, -1
                  c.xor      a4, a5
                  mul        tp, s2, t5
                  add        s4, a7, s6
                  mul        tp, s2, t5
                  mulh       s1, t4, s11
                  c.sub      s0, s1
                  sub        s0, t3, gp
                  sra        s9, s4, t5
                  sll        s8, s0, s6
                  nop
                  xori       t3, t1, -721
                  mul        tp, s2, t5
                  divu       tp, s5, t4
                  c.or       a0, a2
                  srl        t1, tp, zero
                  c.addi     s9, -1
                  mulh       s1, t4, s11
                  c.or       a0, a2
                  srai       a4, a3, 0
                  mul        tp, s2, t5
                  sll        s8, s0, s6
                  sltiu      s3, tp, 300
                  c.slli     t5, 22
                  c.andi     s1, 31
                  c.and      a4, s1
                  c.xor      a4, a5
                  c.xor      a4, a5
                  sltu       s3, a6, a4
                  slt        a0, s5, s11
                  ori        tp, a0, -848
                  c.add      t3, t1
                  c.lui      a6, 24
                  auipc      s1, 11691
                  and        s6, t2, a4
                  c.li       s11, -1
                  mulh       s1, t4, s11
                  mul        tp, s2, t5
                  mulhsu     tp, t5, a6
                  divu       tp, s5, t4
                  add        s4, a7, s6
                  c.srai     s1, 28
                  rem        a2, s2, s9
                  mulhsu     tp, t5, a6
                  remu       s6, s3, t1
                  lui        s3, 985951
                  remu       s6, s3, t1
                  sra        s9, s4, t5
                  sltiu      s3, tp, 300
                  c.addi     s9, -1
                  lui        s3, 985951
                  lui        s3, 985951
                  andi       t0, a3, 147
                  slt        a0, s5, s11
                  c.add      t3, t1
                  andi       t0, a3, 147
                  add        s4, a7, s6
                  andi       t0, a3, 147
                  sltu       s3, a6, a4
                  c.sub      s0, s1
                  andi       t0, a3, 147
                  c.add      t3, t1
                  c.sub      s0, s1
                  c.slli     t5, 22
                  srl        t1, tp, zero
                  lui        s3, 985951
                  slli       a2, a4, 25
                  sltu       s3, a6, a4
                  c.mv       a2, a0
                  mulh       s1, t4, s11
                  c.sub      s0, s1
                  addi       gp, s8, -298
                  c.li       s11, -1
                  slli       a2, a4, 25
                  nop
                  add        s4, a7, s6
                  nop
                  sra        s9, s4, t5
                  c.li       s11, -1
                  c.srli     a4, 9
                  sub        s0, t3, gp
                  nop
                  c.slli     t5, 22
                  mulhsu     tp, t5, a6
                  c.addi16sp sp, -16
                  c.or       a0, a2
                  lui        s3, 985951
                  c.srli     a4, 9
                  slti       tp, a1, -167
                  c.nop
                  c.addi4spn a2, sp, 528
                  c.srai     s1, 28
                  c.xor      a4, a5
                  c.xor      a4, a5
                  slti       tp, a1, -167
                  or         a4, a4, zero
                  sll        s8, s0, s6
                  xor        s11, zero, s7
                  c.mv       a2, a0
                  c.addi16sp sp, -16
                  sra        s9, s4, t5
                  mul        tp, s2, t5
                  c.xor      a4, a5
                  auipc      s1, 11691
                  xori       t3, t1, -721
                  slli       a2, a4, 25
                  srli       zero, a0, 13
                  slli       a2, a4, 25
                  sltiu      s3, tp, 300
                  c.xor      a4, a5
                  c.or       a0, a2
                  addi       gp, s8, -298
                  c.addi16sp sp, -16
                  c.srai     s1, 28
                  or         a4, a4, zero
                  and        s6, t2, a4
                  c.sub      s0, s1
                  c.xor      a4, a5
                  c.add      t3, t1
                  mulh       s1, t4, s11
                  mulhsu     tp, t5, a6
                  slti       tp, a1, -167
                  c.srai     s1, 28
                  c.li       s11, -1
                  slti       tp, a1, -167
                  sub        s0, t3, gp
                  lui        s3, 985951
                  c.sub      s0, s1
                  rem        a2, s2, s9
                  auipc      s1, 11691
                  c.addi4spn a2, sp, 528
                  c.nop
                  mulh       s1, t4, s11
                  c.addi     s9, -1
                  c.sub      s0, s1
                  auipc      s1, 11691
                  xor        s11, zero, s7
                  mulh       s1, t4, s11
                  c.lui      a6, 24
                  mulh       s1, t4, s11
                  c.andi     s1, 31
                  c.addi4spn a2, sp, 528
                  mulh       s1, t4, s11
                  c.addi     s9, -1
                  c.addi     s9, -1
                  and        s6, t2, a4
                  c.li       s11, -1
                  addi       gp, s8, -298
                  srai       a4, a3, 0
                  c.mv       a2, a0
                  mulhsu     tp, t5, a6
                  xor        s11, zero, s7
                  xori       t3, t1, -721
                  c.xor      a4, a5
                  or         a4, a4, zero
                  auipc      s1, 11691
                  c.srli     a4, 9
                  slli       a2, a4, 25
                  rem        a2, s2, s9
                  c.addi4spn a2, sp, 528
                  rem        a2, s2, s9
                  c.xor      a4, a5
                  c.srai     s1, 28
                  divu       tp, s5, t4
                  sll        s8, s0, s6
                  c.xor      a4, a5
                  andi       t0, a3, 147
                  slli       a2, a4, 25
                  c.slli     t5, 22
                  slti       tp, a1, -167
                  c.slli     t5, 22
                  divu       tp, s5, t4
                  srl        t1, tp, zero
                  div        s7, gp, a4
                  xor        s11, zero, s7
                  c.slli     t5, 22
                  remu       s6, s3, t1
                  c.mv       a2, a0
                  lui        s3, 985951
                  c.srli     a4, 9
                  c.slli     t5, 22
                  c.or       a0, a2
                  c.addi16sp sp, -16
                  mulh       s1, t4, s11
                  c.or       a0, a2
                  c.lui      a6, 24
                  c.addi4spn a2, sp, 528
                  c.add      t3, t1
                  nop
                  divu       tp, s5, t4
                  c.li       s11, -1
                  add        s4, a7, s6
                  c.slli     t5, 22
                  lui        s3, 985951
                  c.addi4spn a2, sp, 528
                  sltu       s3, a6, a4
                  mulhsu     tp, t5, a6
                  auipc      s1, 11691
                  sll        s8, s0, s6
                  c.mv       a2, a0
                  xor        s11, zero, s7
                  srai       a4, a3, 0
                  c.mv       a2, a0
                  mulhsu     tp, t5, a6
                  xor        s11, zero, s7
                  auipc      s1, 11691
                  nop
                  remu       s6, s3, t1
                  divu       tp, s5, t4
                  slli       a2, a4, 25
                  xori       t3, t1, -721
                  c.srli     a4, 9
                  auipc      s1, 11691
                  rem        a2, s2, s9
                  c.xor      a4, a5
                  sltiu      s3, tp, 300
                  addi       gp, s8, -298
                  slti       tp, a1, -167
                  srai       a4, a3, 0
                  xori       t3, t1, -721
                  xor        s11, zero, s7
                  c.and      a4, s1
                  sra        s9, s4, t5
                  c.li       s11, -1
                  sltiu      s3, tp, 300
                  slt        a0, s5, s11
                  sltiu      s3, tp, 300
                  addi       gp, s8, -298
                  sltiu      s3, tp, 300
                  lui        s3, 985951
                  divu       tp, s5, t4
                  divu       tp, s5, t4
                  mul        tp, s2, t5
                  and        s6, t2, a4
                  ori        tp, a0, -848
                  c.lui      a6, 24
                  srli       zero, a0, 13
                  mul        tp, s2, t5
                  sll        s8, s0, s6
                  sub        s0, t3, gp
                  srli       zero, a0, 13
                  c.andi     s1, 31
                  andi       t0, a3, 147
                  slt        a0, s5, s11
                  lui        s3, 985951
                  srai       a4, a3, 0
                  auipc      s1, 11691
                  slt        a0, s5, s11
                  ori        tp, a0, -848
                  sltu       s3, a6, a4
                  divu       tp, s5, t4
                  ori        tp, a0, -848
                  c.nop
                  div        s7, gp, a4
                  c.addi     s9, -1
                  c.slli     t5, 22
                  mul        tp, s2, t5
                  c.addi16sp sp, -16
                  addi       gp, s8, -298
                  rem        a2, s2, s9
                  c.addi     s9, -1
                  sub        s0, t3, gp
                  c.lui      a6, 24
                  or         a4, a4, zero
                  rem        a2, s2, s9
                  srl        t1, tp, zero
                  slli       a2, a4, 25
                  sll        s8, s0, s6
                  c.xor      a4, a5
                  divu       tp, s5, t4
                  slli       a2, a4, 25
                  or         a4, a4, zero
                  mulh       s1, t4, s11
                  c.xor      a4, a5
                  c.addi16sp sp, -16
                  c.mv       a2, a0
                  c.andi     s1, 31
                  slli       a2, a4, 25
                  and        s6, t2, a4
                  c.and      a4, s1
                  c.or       a0, a2
                  divu       tp, s5, t4
                  andi       t0, a3, 147
                  c.srai     s1, 28
                  mulh       s1, t4, s11
                  c.xor      a4, a5
                  remu       s6, s3, t1
                  mulhsu     tp, t5, a6
                  c.srai     s1, 28
                  c.addi4spn a2, sp, 528
                  ori        tp, a0, -848
                  rem        a2, s2, s9
                  sltiu      s3, tp, 300
                  c.and      a4, s1
                  c.addi4spn a2, sp, 528
                  rem        a2, s2, s9
                  mulh       s1, t4, s11
                  or         a4, a4, zero
                  c.li       s11, -1
                  c.mv       a2, a0
                  sll        s8, s0, s6
                  c.or       a0, a2
                  slli       a2, a4, 25
                  srli       zero, a0, 13
                  lui        s3, 985951
                  slti       tp, a1, -167
                  c.srai     s1, 28
                  c.srli     a4, 9
                  c.slli     t5, 22
                  c.sub      s0, s1
                  c.lui      a6, 24
                  c.addi16sp sp, -16
                  and        s6, t2, a4
                  c.and      a4, s1
                  c.sub      s0, s1
                  srli       zero, a0, 13
                  c.srai     s1, 28
                  c.lui      a6, 24
                  mulhu      s4, a6, t3
                  c.sub      s0, s1
                  remu       s6, s3, t1
                  div        s7, gp, a4
                  sltu       s3, a6, a4
                  sll        s8, s0, s6
                  c.andi     s1, 31
                  sltiu      s3, tp, 300
                  mulh       s1, t4, s11
                  c.srli     a4, 9
                  sltiu      s3, tp, 300
                  c.srli     a4, 9
                  xori       t3, t1, -721
                  c.slli     t5, 22
                  mul        tp, s2, t5
                  c.srli     a4, 9
                  rem        a2, s2, s9
                  ori        tp, a0, -848
                  remu       s6, s3, t1
                  mulhu      s4, a6, t3
                  ori        tp, a0, -848
                  or         a4, a4, zero
                  c.addi16sp sp, -16
                  c.andi     s1, 31
                  c.lui      a6, 24
                  div        s7, gp, a4
                  c.slli     t5, 22
                  srai       a4, a3, 0
                  c.addi4spn a2, sp, 528
                  slli       a2, a4, 25
                  c.nop
                  c.sub      s0, s1
                  sub        s0, t3, gp
                  c.srai     s1, 28
                  sltu       s3, a6, a4
                  c.li       s11, -1
                  slt        a0, s5, s11
                  sll        s8, s0, s6
                  sll        s8, s0, s6
                  xori       t3, t1, -721
                  remu       s6, s3, t1
                  or         a4, a4, zero
                  c.srli     a4, 9
                  xor        s11, zero, s7
                  div        s7, gp, a4
                  c.xor      a4, a5
                  c.slli     t5, 22
                  auipc      s1, 11691
                  remu       s6, s3, t1
                  c.addi     s9, -1
                  sltu       s3, a6, a4
                  c.add      t3, t1
                  remu       s6, s3, t1
                  c.sub      s0, s1
                  divu       tp, s5, t4
                  c.xor      a4, a5
                  sra        s9, s4, t5
                  c.xor      a4, a5
                  mulhu      s4, a6, t3
                  auipc      s1, 11691
                  sll        s8, s0, s6
                  andi       t0, a3, 147
                  sltiu      s3, tp, 300
                  c.srli     a4, 9
                  lui        s3, 985951
                  c.or       a0, a2
                  srli       zero, a0, 13
                  c.lui      a6, 24
                  rem        a2, s2, s9
                  nop
                  mulhsu     tp, t5, a6
                  lui        s3, 985951
                  lui        s3, 985951
                  add        s4, a7, s6
                  c.or       a0, a2
                  c.add      t3, t1
                  c.addi16sp sp, -16
                  c.slli     t5, 22
                  slti       tp, a1, -167
                  c.sub      s0, s1
                  srli       zero, a0, 13
                  slli       a2, a4, 25
                  c.lui      a6, 24
                  xor        s11, zero, s7
                  c.srai     s1, 28
                  c.add      t3, t1
                  slti       tp, a1, -167
                  sll        s8, s0, s6
                  sltiu      s3, tp, 300
                  c.andi     s1, 31
                  mulh       s1, t4, s11
                  sltiu      s3, tp, 300
                  srai       a4, a3, 0
                  mul        tp, s2, t5
                  sra        s9, s4, t5
                  slti       tp, a1, -167
                  c.xor      a4, a5
                  auipc      s1, 11691
                  sltiu      s3, tp, 300
                  c.and      a4, s1
                  c.addi16sp sp, -16
                  sltu       s3, a6, a4
                  c.addi16sp sp, -16
                  c.nop
                  sub        s0, t3, gp
                  sltiu      s3, tp, 300
                  c.addi4spn a2, sp, 528
                  sltiu      s3, tp, 300
                  slt        a0, s5, s11
                  c.xor      a4, a5
                  slli       a2, a4, 25
                  c.srli     a4, 9
                  auipc      s1, 11691
                  c.andi     s1, 31
                  c.andi     s1, 31
                  sub        s0, t3, gp
                  c.srli     a4, 9
                  xori       t3, t1, -721
                  c.add      t3, t1
                  xor        s11, zero, s7
                  c.or       a0, a2
                  c.sub      s0, s1
                  slti       tp, a1, -167
                  srli       zero, a0, 13
                  c.sub      s0, s1
                  slli       a2, a4, 25
                  c.andi     s1, 31
                  c.nop
                  srli       zero, a0, 13
                  mulhu      s4, a6, t3
                  mulhsu     tp, t5, a6
                  sltiu      s3, tp, 300
                  slli       a2, a4, 25
                  c.add      t3, t1
                  c.addi     s9, -1
                  mul        tp, s2, t5
                  c.addi4spn a2, sp, 528
                  c.slli     t5, 22
                  sra        s9, s4, t5
                  c.mv       a2, a0
                  or         a4, a4, zero
                  auipc      s1, 11691
                  c.andi     s1, 31
                  c.srai     s1, 28
                  divu       tp, s5, t4
                  sltiu      s3, tp, 300
                  srai       a4, a3, 0
                  mulh       s1, t4, s11
                  xori       t3, t1, -721
                  ori        tp, a0, -848
                  c.or       a0, a2
                  auipc      s1, 11691
                  srai       a4, a3, 0
                  srai       a4, a3, 0
                  c.xor      a4, a5
                  sra        s9, s4, t5
                  auipc      s1, 11691
                  lui        s3, 985951
                  c.srli     a4, 9
                  slti       tp, a1, -167
                  sltu       s3, a6, a4
                  c.addi4spn a2, sp, 528
                  sltiu      s3, tp, 300
                  divu       tp, s5, t4
                  sub        s0, t3, gp
                  c.mv       a2, a0
                  addi       gp, s8, -298
                  c.addi4spn a2, sp, 528
                  ori        tp, a0, -848
                  mulhsu     tp, t5, a6
                  remu       s6, s3, t1
                  sltu       s3, a6, a4
                  xor        s11, zero, s7
                  c.add      t3, t1
                  c.addi     s9, -1
                  c.addi4spn a2, sp, 528
                  c.li       s11, -1
                  lui        s3, 985951
                  sll        s8, s0, s6
                  c.li       s11, -1
                  nop
                  c.li       s11, -1
                  slt        a0, s5, s11
                  addi       gp, s8, -298
                  slli       a2, a4, 25
                  xori       t3, t1, -721
                  remu       s6, s3, t1
                  divu       tp, s5, t4
                  c.srli     a4, 9
                  c.mv       a2, a0
                  div        s7, gp, a4
                  srl        t1, tp, zero
                  srli       zero, a0, 13
                  c.xor      a4, a5
                  c.mv       a2, a0
                  ori        tp, a0, -848
                  c.xor      a4, a5
                  c.xor      a4, a5
                  c.xor      a4, a5
                  c.li       s11, -1
                  mul        tp, s2, t5
                  sll        s8, s0, s6
                  c.srai     s1, 28
                  c.and      a4, s1
                  and        s6, t2, a4
                  slli       a2, a4, 25
                  c.lui      a6, 24
                  mulhsu     tp, t5, a6
                  ori        tp, a0, -848
                  xor        s11, zero, s7
                  c.nop
                  srli       zero, a0, 13
                  sltiu      s3, tp, 300
                  divu       tp, s5, t4
                  mulh       s1, t4, s11
                  c.and      a4, s1
                  srli       zero, a0, 13
                  c.xor      a4, a5
                  c.slli     t5, 22
                  c.mv       a2, a0
                  c.or       a0, a2
                  c.srai     s1, 28
                  c.or       a0, a2
                  nop
                  or         a4, a4, zero
                  ori        tp, a0, -848
                  xor        s11, zero, s7
                  slti       tp, a1, -167
                  sltiu      s3, tp, 300
                  or         a4, a4, zero
                  slt        a0, s5, s11
                  c.add      t3, t1
                  srai       a4, a3, 0
                  add        s4, a7, s6
                  divu       tp, s5, t4
                  ori        tp, a0, -848
                  mul        tp, s2, t5
                  sub        s0, t3, gp
                  c.addi4spn a2, sp, 528
                  ori        tp, a0, -848
                  addi       gp, s8, -298
                  mulhsu     tp, t5, a6
                  c.slli     t5, 22
                  c.mv       a2, a0
                  sltu       s3, a6, a4
                  sltiu      s3, tp, 300
                  and        s6, t2, a4
                  and        s6, t2, a4
                  c.slli     t5, 22
                  ori        tp, a0, -848
                  srli       zero, a0, 13
                  sltiu      s3, tp, 300
                  rem        a2, s2, s9
                  srai       a4, a3, 0
                  or         a4, a4, zero
                  c.srai     s1, 28
                  andi       t0, a3, 147
                  srl        t1, tp, zero
                  c.srai     s1, 28
                  slli       a2, a4, 25
                  c.mv       a2, a0
                  add        s4, a7, s6
                  c.mv       a2, a0
                  c.li       s11, -1
                  srli       zero, a0, 13
                  ori        tp, a0, -848
                  sub        s0, t3, gp
                  and        s6, t2, a4
                  divu       tp, s5, t4
                  slt        a0, s5, s11
                  c.addi     s9, -1
                  c.addi     s9, -1
                  andi       t0, a3, 147
                  slti       tp, a1, -167
                  slt        a0, s5, s11
                  xor        s11, zero, s7
                  sll        s8, s0, s6
                  c.nop
                  mul        tp, s2, t5
                  mulhu      s4, a6, t3
                  c.li       s11, -1
                  c.addi4spn a2, sp, 528
                  c.mv       a2, a0
                  c.andi     s1, 31
                  divu       tp, s5, t4
                  srli       zero, a0, 13
                  ori        tp, a0, -848
                  xori       t3, t1, -721
                  add        s4, a7, s6
                  c.andi     s1, 31
                  div        s7, gp, a4
                  xor        s11, zero, s7
                  sub        s0, t3, gp
                  c.lui      a6, 24
                  addi       gp, s8, -298
                  add        s4, a7, s6
                  ori        tp, a0, -848
                  c.slli     t5, 22
                  c.addi16sp sp, -16
                  mulhu      s4, a6, t3
                  mulhu      s4, a6, t3
                  ori        tp, a0, -848
                  c.andi     s1, 31
                  mulh       s1, t4, s11
                  c.lui      a6, 24
                  srli       zero, a0, 13
                  c.lui      a6, 24
                  sltu       s3, a6, a4
                  slti       tp, a1, -167
                  c.srli     a4, 9
                  c.addi     s9, -1
                  c.mv       a2, a0
                  c.nop
                  slt        a0, s5, s11
                  add        s4, a7, s6
                  andi       t0, a3, 147
                  slt        a0, s5, s11
                  mulhsu     tp, t5, a6
                  sltu       s3, a6, a4
                  add        s4, a7, s6
                  divu       tp, s5, t4
                  c.nop
                  slli       a2, a4, 25
                  ori        tp, a0, -848
                  sll        s8, s0, s6
                  xor        s11, zero, s7
                  mul        tp, s2, t5
                  add        s4, a7, s6
                  addi       gp, s8, -298
                  c.and      a4, s1
                  c.sub      s0, s1
                  c.slli     t5, 22
                  remu       s6, s3, t1
                  c.srai     s1, 28
                  xor        s11, zero, s7
                  div        s7, gp, a4
                  c.mv       a2, a0
                  slti       tp, a1, -167
                  c.nop
                  and        s6, t2, a4
                  c.nop
                  rem        a2, s2, s9
                  c.srai     s1, 28
                  xori       t3, t1, -721
                  and        s6, t2, a4
                  slli       a2, a4, 25
                  c.xor      a4, a5
                  c.addi4spn a2, sp, 528
                  srai       a4, a3, 0
                  slli       a2, a4, 25
                  srli       zero, a0, 13
                  div        s7, gp, a4
                  add        s4, a7, s6
                  add        s4, a7, s6
                  nop
                  slt        a0, s5, s11
                  mul        tp, s2, t5
                  c.srli     a4, 9
                  lui        s3, 985951
                  xor        s11, zero, s7
                  c.addi4spn a2, sp, 528
                  addi       gp, s8, -298
                  sll        s8, s0, s6
                  slli       a2, a4, 25
                  sll        s8, s0, s6
                  mulhsu     tp, t5, a6
                  srl        t1, tp, zero
                  sltu       s3, a6, a4
                  add        s4, a7, s6
                  c.addi     s9, -1
                  c.addi16sp sp, -16
                  mulh       s1, t4, s11
                  mulhsu     tp, t5, a6
                  slli       a2, a4, 25
                  c.lui      a6, 24
                  srli       zero, a0, 13
                  c.li       s11, -1
                  add        s4, a7, s6
                  slt        a0, s5, s11
                  c.srai     s1, 28
                  c.nop
                  c.mv       a2, a0
                  ori        tp, a0, -848
                  c.xor      a4, a5
                  c.mv       a2, a0
                  div        s7, gp, a4
                  mulhu      s4, a6, t3
                  nop
                  mulhu      s4, a6, t3
                  c.andi     s1, 31
                  c.sub      s0, s1
                  c.addi     s9, -1
                  c.nop
                  or         a4, a4, zero
                  xori       t3, t1, -721
                  ori        tp, a0, -848
                  srli       zero, a0, 13
                  slt        a0, s5, s11
                  or         a4, a4, zero
                  ori        tp, a0, -848
                  auipc      s1, 11691
                  remu       s6, s3, t1
                  sll        s8, s0, s6
                  and        s6, t2, a4
                  c.addi     s9, -1
                  mul        tp, s2, t5
                  c.nop
                  xor        s11, zero, s7
                  and        s6, t2, a4
                  srl        t1, tp, zero
                  c.slli     t5, 22
                  mul        tp, s2, t5
                  c.add      t3, t1
                  and        s6, t2, a4
                  slli       a2, a4, 25
                  or         a4, a4, zero
                  mulhu      s4, a6, t3
                  slt        a0, s5, s11
                  mulhu      s4, a6, t3
                  c.and      a4, s1
                  c.nop
                  srai       a4, a3, 0
                  c.nop
                  slti       tp, a1, -167
                  c.addi16sp sp, -16
                  c.xor      a4, a5
                  c.addi4spn a2, sp, 528
                  slli       a2, a4, 25
                  lui        s3, 985951
                  c.nop
                  addi       gp, s8, -298
                  mulh       s1, t4, s11
                  remu       s6, s3, t1
                  sltiu      s3, tp, 300
                  c.mv       a2, a0
                  c.li       s11, -1
                  c.addi4spn a2, sp, 528
                  div        s7, gp, a4
                  rem        a2, s2, s9
                  xor        s11, zero, s7
                  c.addi16sp sp, -16
                  c.and      a4, s1
                  c.srli     a4, 9
                  mulhu      s4, a6, t3
                  mulhu      s4, a6, t3
                  c.xor      a4, a5
                  mulh       s1, t4, s11
                  andi       t0, a3, 147
                  mul        tp, s2, t5
                  or         a4, a4, zero
                  slli       a2, a4, 25
                  xor        s11, zero, s7
                  c.li       s11, -1
                  c.and      a4, s1
                  sra        s9, s4, t5
                  sra        s9, s4, t5
                  divu       tp, s5, t4
                  srli       zero, a0, 13
                  xor        s11, zero, s7
                  divu       tp, s5, t4
                  sra        s9, s4, t5
                  andi       t0, a3, 147
                  add        s4, a7, s6
                  mulhu      s4, a6, t3
                  c.addi16sp sp, -16
                  sra        s9, s4, t5
                  remu       s6, s3, t1
                  c.add      t3, t1
                  sub        s0, t3, gp
                  andi       t0, a3, 147
                  addi       gp, s8, -298
                  c.andi     s1, 31
                  mulhu      s4, a6, t3
                  mulhu      s4, a6, t3
                  add        s4, a7, s6
                  c.xor      a4, a5
                  mulhsu     tp, t5, a6
                  srl        t1, tp, zero
                  mulh       s1, t4, s11
                  div        s7, gp, a4
                  c.lui      a6, 24
                  sub        s0, t3, gp
                  divu       tp, s5, t4
                  add        s4, a7, s6
                  rem        a2, s2, s9
                  sll        s8, s0, s6
                  auipc      s1, 11691
                  c.or       a0, a2
                  andi       t0, a3, 147
                  xori       t3, t1, -721
                  c.addi     s9, -1
                  c.addi16sp sp, -16
                  c.andi     s1, 31
                  c.sub      s0, s1
                  sll        s8, s0, s6
                  c.lui      a6, 24
                  li         t5, 0xffffffff #start riscv_int_numeric_corner_stream_21
                  li         a7, 0x0
                  li         s10, 0xffffffff
                  li         s4, 0xca55fb0b
                  li         s0, 0x39cd0672
                  li         t1, 0x16661571
                  li         sp, 0x3c77746c
                  li         a0, 0xa8989e13
                  li         t2, 0xffffffff
                  li         gp, 0x0
                  nop
                  remu       a7, gp, t1
                  sub        s10, a0, s10
                  mulh       gp, t2, t1
                  mulh       gp, t2, t1
                  remu       a7, gp, t1
                  mul        s0, t1, s0
                  nop
                  mulhsu     t2, s0, a7
                  lui        t1, 985951
                  auipc      s0, 11691
                  sub        s10, a0, s10
                  lui        t1, 985951
                  remu       a7, gp, t1
                  divu       sp, t2, a7 #end riscv_int_numeric_corner_stream_21
                  remu       s6, s3, t1
                  and        s6, t2, a4
                  mulhsu     tp, t5, a6
                  mulh       s1, t4, s11
                  sra        s9, s4, t5
                  c.sub      s0, s1
                  divu       tp, s5, t4
                  c.li       s11, -1
                  c.xor      a4, a5
                  lui        s3, 985951
                  auipc      s1, 11691
                  slt        a0, s5, s11
                  c.addi4spn a2, sp, 528
                  c.addi     s9, -1
                  srai       a4, a3, 0
                  sltiu      s3, tp, 300
                  c.sub      s0, s1
                  c.or       a0, a2
                  remu       s6, s3, t1
                  xor        s11, zero, s7
                  c.slli     t5, 22
                  ori        tp, a0, -848
                  div        s7, gp, a4
                  sub        s0, t3, gp
                  c.li       s11, -1
                  c.addi16sp sp, -16
                  sltu       s3, a6, a4
                  c.or       a0, a2
                  c.srli     a4, 9
                  c.addi     s9, -1
                  c.and      a4, s1
                  c.addi16sp sp, -16
                  divu       tp, s5, t4
                  div        s7, gp, a4
                  c.mv       a2, a0
                  divu       tp, s5, t4
                  c.or       a0, a2
                  sltu       s3, a6, a4
                  slt        a0, s5, s11
                  c.lui      a6, 24
                  slti       tp, a1, -167
                  c.slli     t5, 22
                  sub        s0, t3, gp
                  ori        tp, a0, -848
                  or         a4, a4, zero
                  auipc      s1, 11691
                  divu       tp, s5, t4
                  srl        t1, tp, zero
                  slli       a2, a4, 25
                  mul        tp, s2, t5
                  andi       t0, a3, 147
                  remu       s6, s3, t1
                  or         a4, a4, zero
                  c.addi4spn a2, sp, 528
                  c.slli     t5, 22
                  srai       a4, a3, 0
                  srli       zero, a0, 13
                  c.slli     t5, 22
                  srai       a4, a3, 0
                  addi       gp, s8, -298
                  xor        s11, zero, s7
                  c.nop
                  div        s7, gp, a4
                  addi       gp, s8, -298
                  srai       a4, a3, 0
                  srl        t1, tp, zero
                  slt        a0, s5, s11
                  remu       s6, s3, t1
                  nop
                  addi       gp, s8, -298
                  addi       gp, s8, -298
                  c.srai     s1, 28
                  remu       s6, s3, t1
                  sll        s8, s0, s6
                  c.li       s11, -1
                  nop
                  slt        a0, s5, s11
                  c.lui      a6, 24
                  nop
                  c.xor      a4, a5
                  slti       tp, a1, -167
                  addi       gp, s8, -298
                  c.mv       a2, a0
                  slli       a2, a4, 25
                  add        s4, a7, s6
                  c.xor      a4, a5
                  add        s4, a7, s6
                  mulhu      s4, a6, t3
                  remu       s6, s3, t1
                  srai       a4, a3, 0
                  addi       gp, s8, -298
                  divu       tp, s5, t4
                  c.addi16sp sp, -16
                  mulhu      s4, a6, t3
                  c.andi     s1, 31
                  c.andi     s1, 31
                  slli       a2, a4, 25
                  sll        s8, s0, s6
                  c.addi16sp sp, -16
                  mul        tp, s2, t5
                  remu       s6, s3, t1
                  ori        tp, a0, -848
                  srli       zero, a0, 13
                  c.addi16sp sp, -16
                  c.nop
                  rem        a2, s2, s9
                  srl        t1, tp, zero
                  c.li       s11, -1
                  c.srai     s1, 28
                  c.or       a0, a2
                  add        s4, a7, s6
                  sll        s8, s0, s6
                  c.slli     t5, 22
                  div        s7, gp, a4
                  srli       zero, a0, 13
                  slti       tp, a1, -167
                  add        s4, a7, s6
                  slli       a2, a4, 25
                  mulhsu     tp, t5, a6
                  c.li       s11, -1
                  mulhu      s4, a6, t3
                  c.sub      s0, s1
                  c.addi16sp sp, -16
                  c.srli     a4, 9
                  and        s6, t2, a4
                  rem        a2, s2, s9
                  srl        t1, tp, zero
                  xor        s11, zero, s7
                  xor        s11, zero, s7
                  c.xor      a4, a5
                  or         a4, a4, zero
                  ori        tp, a0, -848
                  remu       s6, s3, t1
                  c.li       s11, -1
                  sub        s0, t3, gp
                  c.addi4spn a2, sp, 528
                  andi       t0, a3, 147
                  sltu       s3, a6, a4
                  c.li       s11, -1
                  sll        s8, s0, s6
                  c.srai     s1, 28
                  rem        a2, s2, s9
                  mulh       s1, t4, s11
                  slti       tp, a1, -167
                  srli       zero, a0, 13
                  c.sub      s0, s1
                  c.add      t3, t1
                  srl        t1, tp, zero
                  addi       gp, s8, -298
                  c.mv       a2, a0
                  mulhsu     tp, t5, a6
                  ori        tp, a0, -848
                  xori       t3, t1, -721
                  xor        s11, zero, s7
                  sll        s8, s0, s6
                  mulh       s1, t4, s11
                  andi       t0, a3, 147
                  andi       t0, a3, 147
                  divu       tp, s5, t4
                  rem        a2, s2, s9
                  mul        tp, s2, t5
                  divu       tp, s5, t4
                  sltiu      s3, tp, 300
                  c.add      t3, t1
                  divu       tp, s5, t4
                  c.or       a0, a2
                  c.nop
                  auipc      s1, 11691
                  c.slli     t5, 22
                  div        s7, gp, a4
                  mulhsu     tp, t5, a6
                  addi       gp, s8, -298
                  c.srli     a4, 9
                  ori        tp, a0, -848
                  srai       a4, a3, 0
                  srai       a4, a3, 0
                  lui        s3, 985951
                  xor        s11, zero, s7
                  slli       a2, a4, 25
                  andi       t0, a3, 147
                  andi       t0, a3, 147
                  mulhu      s4, a6, t3
                  c.xor      a4, a5
                  lui        s3, 985951
                  c.srai     s1, 28
                  slli       a2, a4, 25
                  srl        t1, tp, zero
                  andi       t0, a3, 147
                  div        s7, gp, a4
                  lui        s3, 985951
                  c.andi     s1, 31
                  srli       zero, a0, 13
                  sub        s0, t3, gp
                  c.addi     s9, -1
                  ori        tp, a0, -848
                  c.xor      a4, a5
                  srli       zero, a0, 13
                  mulhsu     tp, t5, a6
                  slli       a2, a4, 25
                  nop
                  c.or       a0, a2
                  mul        tp, s2, t5
                  srl        t1, tp, zero
                  auipc      s1, 11691
                  c.mv       a2, a0
                  sll        s8, s0, s6
                  addi       gp, s8, -298
                  remu       s6, s3, t1
                  mulhsu     tp, t5, a6
                  div        s7, gp, a4
                  sltiu      s3, tp, 300
                  add        s4, a7, s6
                  rem        a2, s2, s9
                  c.xor      a4, a5
                  c.add      t3, t1
                  addi       gp, s8, -298
                  add        s4, a7, s6
                  xori       t3, t1, -721
                  c.li       s11, -1
                  xori       t3, t1, -721
                  mulhu      s4, a6, t3
                  mul        tp, s2, t5
                  sll        s8, s0, s6
                  c.andi     s1, 31
                  xor        s11, zero, s7
                  mulh       s1, t4, s11
                  sra        s9, s4, t5
                  sltiu      s3, tp, 300
                  c.or       a0, a2
                  xor        s11, zero, s7
                  div        s7, gp, a4
                  rem        a2, s2, s9
                  add        s4, a7, s6
                  sltu       s3, a6, a4
                  rem        a2, s2, s9
                  c.addi16sp sp, -16
                  c.srli     a4, 9
                  c.add      t3, t1
                  c.nop
                  c.mv       a2, a0
                  c.add      t3, t1
                  divu       tp, s5, t4
                  remu       s6, s3, t1
                  slt        a0, s5, s11
                  slli       a2, a4, 25
                  div        s7, gp, a4
                  c.sub      s0, s1
                  slti       tp, a1, -167
                  mul        tp, s2, t5
                  sll        s8, s0, s6
                  srai       a4, a3, 0
                  slti       tp, a1, -167
                  c.srai     s1, 28
                  srai       a4, a3, 0
                  sll        s8, s0, s6
                  nop
                  c.li       s11, -1
                  srli       zero, a0, 13
                  slli       a2, a4, 25
                  sltu       s3, a6, a4
                  c.xor      a4, a5
                  slli       a2, a4, 25
                  c.and      a4, s1
                  c.and      a4, s1
                  nop
                  lui        s3, 985951
                  c.addi16sp sp, -16
                  srl        t1, tp, zero
                  or         a4, a4, zero
                  c.srli     a4, 9
                  mulhsu     tp, t5, a6
                  or         a4, a4, zero
                  sltu       s3, a6, a4
                  c.addi16sp sp, -16
                  divu       tp, s5, t4
                  c.sub      s0, s1
                  or         a4, a4, zero
                  and        s6, t2, a4
                  div        s7, gp, a4
                  slt        a0, s5, s11
                  sltiu      s3, tp, 300
                  c.mv       a2, a0
                  c.addi16sp sp, -16
                  mulhu      s4, a6, t3
                  c.xor      a4, a5
                  and        s6, t2, a4
                  c.or       a0, a2
                  c.lui      a6, 24
                  c.andi     s1, 31
                  sra        s9, s4, t5
                  nop
                  remu       s6, s3, t1
                  c.addi16sp sp, -16
                  c.addi     s9, -1
                  c.li       s11, -1
                  divu       tp, s5, t4
                  c.addi     s9, -1
                  divu       tp, s5, t4
                  ori        tp, a0, -848
                  srl        t1, tp, zero
                  sra        s9, s4, t5
                  c.addi4spn a2, sp, 528
                  xori       t3, t1, -721
                  andi       t0, a3, 147
                  addi       gp, s8, -298
                  xori       t3, t1, -721
                  mulhsu     tp, t5, a6
                  c.or       a0, a2
                  divu       tp, s5, t4
                  li         ra, 0xffffffff #start riscv_int_numeric_corner_stream_20
                  li         t1, 0xcb010afa
                  li         s1, 0xffffffff
                  li         s7, 0x0
                  li         s5, 0x80000000
                  li         sp, 0x0
                  li         gp, 0x80000000
                  li         a6, 0x0
                  li         a2, 0x80000000
                  li         s6, 0x0
                  divu       a2, gp, a6
                  addi       s1, gp, -40
                  nop
                  auipc      s1, 11691
                  divu       a2, gp, a6
                  add        s7, t1, s6
                  sub        sp, a2, s5
                  nop
                  div        a6, s6, gp
                  lui        gp, 985951
                  add        s7, t1, s6
                  remu       a2, s6, a2
                  lui        gp, 985951
                  rem        a2, sp, t1
                  mul        t1, s6, s1 #end riscv_int_numeric_corner_stream_20
                  lui        s3, 985951
                  xor        s11, zero, s7
                  srai       a4, a3, 0
                  c.andi     s1, 31
                  srl        t1, tp, zero
                  addi       gp, s8, -298
                  mulhsu     tp, t5, a6
                  rem        a2, s2, s9
                  and        s6, t2, a4
                  mul        tp, s2, t5
                  mulhsu     tp, t5, a6
                  srai       a4, a3, 0
                  mul        tp, s2, t5
                  mulhsu     tp, t5, a6
                  lui        s3, 985951
                  andi       t0, a3, 147
                  c.srai     s1, 28
                  c.slli     t5, 22
                  mulhu      s4, a6, t3
                  srli       zero, a0, 13
                  mulh       s1, t4, s11
                  xor        s11, zero, s7
                  auipc      s1, 11691
                  c.sub      s0, s1
                  divu       tp, s5, t4
                  mul        tp, s2, t5
                  c.slli     t5, 22
                  mul        tp, s2, t5
                  add        s4, a7, s6
                  xor        s11, zero, s7
                  c.li       s11, -1
                  srl        t1, tp, zero
                  addi       gp, s8, -298
                  remu       s6, s3, t1
                  xori       t3, t1, -721
                  lui        s3, 985951
                  sltiu      s3, tp, 300
                  c.or       a0, a2
                  c.nop
                  c.slli     t5, 22
                  andi       t0, a3, 147
                  slli       a2, a4, 25
                  c.addi16sp sp, -16
                  sra        s9, s4, t5
                  srl        t1, tp, zero
                  divu       tp, s5, t4
                  c.add      t3, t1
                  mulhsu     tp, t5, a6
                  xor        s11, zero, s7
                  rem        a2, s2, s9
                  c.addi     s9, -1
                  srli       zero, a0, 13
                  xori       t3, t1, -721
                  sll        s8, s0, s6
                  remu       s6, s3, t1
                  c.add      t3, t1
                  c.slli     t5, 22
                  mulh       s1, t4, s11
                  sra        s9, s4, t5
                  srli       zero, a0, 13
                  div        s7, gp, a4
                  c.andi     s1, 31
                  slli       a2, a4, 25
                  add        s4, a7, s6
                  c.lui      a6, 24
                  c.srli     a4, 9
                  c.srli     a4, 9
                  sll        s8, s0, s6
                  or         a4, a4, zero
                  c.addi16sp sp, -16
                  srai       a4, a3, 0
                  auipc      s1, 11691
                  slti       tp, a1, -167
                  and        s6, t2, a4
                  mulhsu     tp, t5, a6
                  remu       s6, s3, t1
                  mulhsu     tp, t5, a6
                  sltiu      s3, tp, 300
                  sub        s0, t3, gp
                  srli       zero, a0, 13
                  c.and      a4, s1
                  andi       t0, a3, 147
                  srl        t1, tp, zero
                  c.and      a4, s1
                  mulhsu     tp, t5, a6
                  c.xor      a4, a5
                  c.xor      a4, a5
                  slt        a0, s5, s11
                  add        s4, a7, s6
                  addi       gp, s8, -298
                  c.add      t3, t1
                  sltiu      s3, tp, 300
                  c.srli     a4, 9
                  or         a4, a4, zero
                  srl        t1, tp, zero
                  addi       gp, s8, -298
                  divu       tp, s5, t4
                  and        s6, t2, a4
                  c.and      a4, s1
                  nop
                  c.li       s11, -1
                  srl        t1, tp, zero
                  auipc      s1, 11691
                  slli       a2, a4, 25
                  rem        a2, s2, s9
                  slt        a0, s5, s11
                  sll        s8, s0, s6
                  divu       tp, s5, t4
                  srli       zero, a0, 13
                  c.or       a0, a2
                  auipc      s1, 11691
                  c.addi4spn a2, sp, 528
                  c.or       a0, a2
                  mulhu      s4, a6, t3
                  c.srai     s1, 28
                  c.sub      s0, s1
                  remu       s6, s3, t1
                  c.slli     t5, 22
                  nop
                  andi       t0, a3, 147
                  and        s6, t2, a4
                  sub        s0, t3, gp
                  c.slli     t5, 22
                  mul        tp, s2, t5
                  c.nop
                  lui        s3, 985951
                  c.srli     a4, 9
                  sltu       s3, a6, a4
                  mulhsu     tp, t5, a6
                  slli       a2, a4, 25
                  div        s7, gp, a4
                  slli       a2, a4, 25
                  c.add      t3, t1
                  li         a3, 0x510d6db9 #start riscv_int_numeric_corner_stream_1
                  li         a0, 0xfea2006a
                  li         tp, 0xbb5a5c20
                  li         t4, 0x0
                  li         t2, 0x80000000
                  li         s0, 0x0
                  li         ra, 0xffffffff
                  li         s8, 0x0
                  li         gp, 0x1880902
                  li         a4, 0xffffffff
                  nop
                  addi       ra, gp, -40
                  sub        a0, ra, t4
                  auipc      s0, 11691
                  rem        t4, gp, t2
                  auipc      s0, 11691
                  nop
                  auipc      s0, 11691
                  nop
                  mulhsu     a4, s0, ra
                  nop
                  nop
                  auipc      s0, 11691
                  nop
                  mulh       s8, t4, tp #end riscv_int_numeric_corner_stream_1
                  c.addi16sp sp, -16
                  c.mv       a2, a0
                  nop
                  mul        tp, s2, t5
                  c.addi16sp sp, -16
                  li         s10, 0x0 #start riscv_int_numeric_corner_stream_9
                  li         s5, 0x80000000
                  li         a7, 0xe1480c42
                  li         s3, 0x80000000
                  li         tp, 0xa7f765d2
                  li         gp, 0x51c5e20f
                  li         t0, 0x6b1abb01
                  li         t5, 0x0
                  li         ra, 0xf5603a3b
                  li         s0, 0xa5cf641c
                  divu       s0, gp, a7
                  mul        gp, s3, s0
                  addi       s10, s10, -40
                  mulhu      s0, s0, t5
                  nop
                  lui        s3, 985951
                  add        t5, tp, t5
                  mulhsu     t5, s3, ra
                  add        t5, tp, t5
                  nop
                  nop
                  nop
                  nop
                  nop
                  addi       s10, s10, -40 #end riscv_int_numeric_corner_stream_9
                  c.sub      s0, s1
                  c.srli     a4, 9
                  c.srli     a4, 9
                  c.slli     t5, 22
                  c.addi4spn a2, sp, 528
                  mul        tp, s2, t5
                  slli       a2, a4, 25
                  c.srai     s1, 28
                  c.srai     s1, 28
                  c.and      a4, s1
                  c.mv       a2, a0
                  sltiu      s3, tp, 300
                  c.andi     s1, 31
                  c.xor      a4, a5
                  c.and      a4, s1
                  and        s6, t2, a4
                  sltiu      s3, tp, 300
                  srl        t1, tp, zero
                  c.addi16sp sp, -16
                  c.addi4spn a2, sp, 528
                  slt        a0, s5, s11
                  srli       zero, a0, 13
                  c.li       s11, -1
                  c.addi     s9, -1
                  and        s6, t2, a4
                  mulh       s1, t4, s11
                  c.srli     a4, 9
                  c.srli     a4, 9
                  or         a4, a4, zero
                  sll        s8, s0, s6
                  c.nop
                  c.li       s11, -1
                  sra        s9, s4, t5
                  and        s6, t2, a4
                  srl        t1, tp, zero
                  c.lui      a6, 24
                  mul        tp, s2, t5
                  mulh       s1, t4, s11
                  add        s4, a7, s6
                  c.srli     a4, 9
                  c.and      a4, s1
                  c.add      t3, t1
                  c.and      a4, s1
                  xori       t3, t1, -721
                  c.srli     a4, 9
                  mulhu      s4, a6, t3
                  srai       a4, a3, 0
                  c.srai     s1, 28
                  sltu       s3, a6, a4
                  slti       tp, a1, -167
                  srai       a4, a3, 0
                  addi       gp, s8, -298
                  c.srai     s1, 28
                  remu       s6, s3, t1
                  lui        s3, 985951
                  remu       s6, s3, t1
                  sub        s0, t3, gp
                  add        s4, a7, s6
                  xori       t3, t1, -721
                  mul        tp, s2, t5
                  mulhsu     tp, t5, a6
                  c.andi     s1, 31
                  ori        tp, a0, -848
                  c.or       a0, a2
                  c.nop
                  slli       a2, a4, 25
                  c.srli     a4, 9
                  sll        s8, s0, s6
                  srli       zero, a0, 13
                  c.addi4spn a2, sp, 528
                  srai       a4, a3, 0
                  lui        s3, 985951
                  rem        a2, s2, s9
                  mulhu      s4, a6, t3
                  c.or       a0, a2
                  rem        a2, s2, s9
                  c.li       s11, -1
                  rem        a2, s2, s9
                  srli       zero, a0, 13
                  c.li       s11, -1
                  andi       t0, a3, 147
                  xor        s11, zero, s7
                  c.lui      a6, 24
                  c.andi     s1, 31
                  c.add      t3, t1
                  or         a4, a4, zero
                  divu       tp, s5, t4
                  c.addi     s9, -1
                  c.sub      s0, s1
                  c.li       s11, -1
                  sub        s0, t3, gp
                  slt        a0, s5, s11
                  c.srai     s1, 28
                  c.srli     a4, 9
                  c.li       s11, -1
                  c.addi     s9, -1
                  slli       a2, a4, 25
                  sll        s8, s0, s6
                  divu       tp, s5, t4
                  andi       t0, a3, 147
                  divu       tp, s5, t4
                  auipc      s1, 11691
                  c.or       a0, a2
                  c.addi4spn a2, sp, 528
                  mulh       s1, t4, s11
                  xor        s11, zero, s7
                  xori       t3, t1, -721
                  or         a4, a4, zero
                  c.sub      s0, s1
                  slti       tp, a1, -167
                  divu       tp, s5, t4
                  mulh       s1, t4, s11
                  sll        s8, s0, s6
                  c.nop
                  c.mv       a2, a0
                  srl        t1, tp, zero
                  sll        s8, s0, s6
                  sub        s0, t3, gp
                  c.sub      s0, s1
                  c.lui      a6, 24
                  c.mv       a2, a0
                  xori       t3, t1, -721
                  mulhsu     tp, t5, a6
                  sltiu      s3, tp, 300
                  c.mv       a2, a0
                  c.sub      s0, s1
                  c.or       a0, a2
                  c.andi     s1, 31
                  ori        tp, a0, -848
                  sub        s0, t3, gp
                  c.nop
                  srl        t1, tp, zero
                  or         a4, a4, zero
                  add        s4, a7, s6
                  sltu       s3, a6, a4
                  addi       gp, s8, -298
                  andi       t0, a3, 147
                  c.li       s11, -1
                  c.slli     t5, 22
                  c.lui      a6, 24
                  c.slli     t5, 22
                  c.and      a4, s1
                  srli       zero, a0, 13
                  srl        t1, tp, zero
                  c.slli     t5, 22
                  xori       t3, t1, -721
                  andi       t0, a3, 147
                  sltu       s3, a6, a4
                  c.andi     s1, 31
                  sll        s8, s0, s6
                  or         a4, a4, zero
                  or         a4, a4, zero
                  c.andi     s1, 31
                  rem        a2, s2, s9
                  add        s4, a7, s6
                  mul        tp, s2, t5
                  c.and      a4, s1
                  sra        s9, s4, t5
                  c.addi     s9, -1
                  c.sub      s0, s1
                  c.slli     t5, 22
                  slti       tp, a1, -167
                  sra        s9, s4, t5
                  andi       t0, a3, 147
                  or         a4, a4, zero
                  c.xor      a4, a5
                  ori        tp, a0, -848
                  srl        t1, tp, zero
                  c.sub      s0, s1
                  c.slli     t5, 22
                  lui        s3, 985951
                  addi       gp, s8, -298
                  xor        s11, zero, s7
                  lui        s3, 985951
                  ori        tp, a0, -848
                  sll        s8, s0, s6
                  c.or       a0, a2
                  or         a4, a4, zero
                  remu       s6, s3, t1
                  c.slli     t5, 22
                  c.mv       a2, a0
                  c.addi     s9, -1
                  div        s7, gp, a4
                  srl        t1, tp, zero
                  andi       t0, a3, 147
                  c.addi     s9, -1
                  mul        tp, s2, t5
                  c.sub      s0, s1
                  div        s7, gp, a4
                  c.srli     a4, 9
                  sll        s8, s0, s6
                  nop
                  sub        s0, t3, gp
                  c.xor      a4, a5
                  c.li       s11, -1
                  divu       tp, s5, t4
                  c.slli     t5, 22
                  sltiu      s3, tp, 300
                  mulhsu     tp, t5, a6
                  nop
                  mulhu      s4, a6, t3
                  andi       t0, a3, 147
                  xor        s11, zero, s7
                  c.slli     t5, 22
                  c.mv       a2, a0
                  c.or       a0, a2
                  auipc      s1, 11691
                  or         a4, a4, zero
                  c.srai     s1, 28
                  c.and      a4, s1
                  c.sub      s0, s1
                  and        s6, t2, a4
                  and        s6, t2, a4
                  mulh       s1, t4, s11
                  div        s7, gp, a4
                  divu       tp, s5, t4
                  add        s4, a7, s6
                  srai       a4, a3, 0
                  xor        s11, zero, s7
                  slli       a2, a4, 25
                  srli       zero, a0, 13
                  c.srai     s1, 28
                  andi       t0, a3, 147
                  c.addi16sp sp, -16
                  srai       a4, a3, 0
                  c.addi     s9, -1
                  add        s4, a7, s6
                  mul        tp, s2, t5
                  c.slli     t5, 22
                  c.li       s11, -1
                  mulhsu     tp, t5, a6
                  slti       tp, a1, -167
                  divu       tp, s5, t4
                  c.and      a4, s1
                  c.li       s11, -1
                  c.srai     s1, 28
                  c.nop
                  xori       t3, t1, -721
                  xori       t3, t1, -721
                  ori        tp, a0, -848
                  srli       zero, a0, 13
                  c.li       s11, -1
                  c.xor      a4, a5
                  lui        s3, 985951
                  c.mv       a2, a0
                  c.andi     s1, 31
                  c.slli     t5, 22
                  c.li       s11, -1
                  c.srai     s1, 28
                  slt        a0, s5, s11
                  slti       tp, a1, -167
                  xori       t3, t1, -721
                  divu       tp, s5, t4
                  c.and      a4, s1
                  lui        s3, 985951
                  rem        a2, s2, s9
                  sll        s8, s0, s6
                  sll        s8, s0, s6
                  c.add      t3, t1
                  mul        tp, s2, t5
                  slt        a0, s5, s11
                  c.addi4spn a2, sp, 528
                  slli       a2, a4, 25
                  sltu       s3, a6, a4
                  srai       a4, a3, 0
                  c.andi     s1, 31
                  xori       t3, t1, -721
                  mulh       s1, t4, s11
                  nop
                  sra        s9, s4, t5
                  slt        a0, s5, s11
                  c.srai     s1, 28
                  sub        s0, t3, gp
                  c.srli     a4, 9
                  remu       s6, s3, t1
                  nop
                  slti       tp, a1, -167
                  sra        s9, s4, t5
                  slli       a2, a4, 25
                  srl        t1, tp, zero
                  sltiu      s3, tp, 300
                  c.add      t3, t1
                  sltu       s3, a6, a4
                  slt        a0, s5, s11
                  addi       gp, s8, -298
                  srli       zero, a0, 13
                  divu       tp, s5, t4
                  sltu       s3, a6, a4
                  c.srli     a4, 9
                  divu       tp, s5, t4
                  sltu       s3, a6, a4
                  c.sub      s0, s1
                  slli       a2, a4, 25
                  c.mv       a2, a0
                  andi       t0, a3, 147
                  c.nop
                  c.li       s11, -1
                  mul        tp, s2, t5
                  c.addi4spn a2, sp, 528
                  mulhu      s4, a6, t3
                  lui        s3, 985951
                  xori       t3, t1, -721
                  and        s6, t2, a4
                  lui        s3, 985951
                  c.srli     a4, 9
                  divu       tp, s5, t4
                  c.or       a0, a2
                  c.addi16sp sp, -16
                  c.add      t3, t1
                  c.add      t3, t1
                  divu       tp, s5, t4
                  mulhu      s4, a6, t3
                  remu       s6, s3, t1
                  sra        s9, s4, t5
                  c.li       s11, -1
                  c.slli     t5, 22
                  lui        s3, 985951
                  mul        tp, s2, t5
                  c.lui      a6, 24
                  slli       a2, a4, 25
                  c.mv       a2, a0
                  c.nop
                  slti       tp, a1, -167
                  c.lui      a6, 24
                  c.addi16sp sp, -16
                  mulhsu     tp, t5, a6
                  c.li       s11, -1
                  and        s6, t2, a4
                  rem        a2, s2, s9
                  sltiu      s3, tp, 300
                  c.addi16sp sp, -16
                  rem        a2, s2, s9
                  c.li       s11, -1
                  or         a4, a4, zero
                  c.or       a0, a2
                  and        s6, t2, a4
                  c.addi16sp sp, -16
                  c.xor      a4, a5
                  or         a4, a4, zero
                  sra        s9, s4, t5
                  rem        a2, s2, s9
                  mulh       s1, t4, s11
                  lui        s3, 985951
                  c.addi4spn a2, sp, 528
                  srl        t1, tp, zero
                  srl        t1, tp, zero
                  sub        s0, t3, gp
                  srli       zero, a0, 13
                  srl        t1, tp, zero
                  xor        s11, zero, s7
                  c.xor      a4, a5
                  srl        t1, tp, zero
                  c.slli     t5, 22
                  rem        a2, s2, s9
                  andi       t0, a3, 147
                  auipc      s1, 11691
                  mulh       s1, t4, s11
                  and        s6, t2, a4
                  c.srai     s1, 28
                  sltiu      s3, tp, 300
                  sltu       s3, a6, a4
                  sltiu      s3, tp, 300
                  mulhu      s4, a6, t3
                  c.addi16sp sp, -16
                  ori        tp, a0, -848
                  or         a4, a4, zero
                  c.addi     s9, -1
                  add        s4, a7, s6
                  div        s7, gp, a4
                  mul        tp, s2, t5
                  andi       t0, a3, 147
                  auipc      s1, 11691
                  c.lui      a6, 24
                  mul        tp, s2, t5
                  slt        a0, s5, s11
                  rem        a2, s2, s9
                  add        s4, a7, s6
                  c.and      a4, s1
                  srai       a4, a3, 0
                  sltiu      s3, tp, 300
                  addi       gp, s8, -298
                  and        s6, t2, a4
                  c.slli     t5, 22
                  c.sub      s0, s1
                  sll        s8, s0, s6
                  srli       zero, a0, 13
                  slt        a0, s5, s11
                  slti       tp, a1, -167
                  xor        s11, zero, s7
                  nop
                  divu       tp, s5, t4
                  c.or       a0, a2
                  mul        tp, s2, t5
                  srai       a4, a3, 0
                  mul        tp, s2, t5
                  sub        s0, t3, gp
                  ori        tp, a0, -848
                  srai       a4, a3, 0
                  nop
                  srai       a4, a3, 0
                  or         a4, a4, zero
                  srl        t1, tp, zero
                  xor        s11, zero, s7
                  slt        a0, s5, s11
                  c.li       s11, -1
                  c.li       s11, -1
                  c.addi16sp sp, -16
                  xori       t3, t1, -721
                  c.addi     s9, -1
                  c.add      t3, t1
                  c.andi     s1, 31
                  remu       s6, s3, t1
                  and        s6, t2, a4
                  sltiu      s3, tp, 300
                  c.li       s11, -1
                  ori        tp, a0, -848
                  mul        tp, s2, t5
                  rem        a2, s2, s9
                  c.addi     s9, -1
                  mulhu      s4, a6, t3
                  or         a4, a4, zero
                  sltiu      s3, tp, 300
                  mulh       s1, t4, s11
                  c.srai     s1, 28
                  mul        tp, s2, t5
                  andi       t0, a3, 147
                  c.xor      a4, a5
                  c.xor      a4, a5
                  sll        s8, s0, s6
                  auipc      s1, 11691
                  sra        s9, s4, t5
                  rem        a2, s2, s9
                  c.addi4spn a2, sp, 528
                  c.add      t3, t1
                  mulhu      s4, a6, t3
                  c.sub      s0, s1
                  lui        s3, 985951
                  addi       gp, s8, -298
                  div        s7, gp, a4
                  mul        tp, s2, t5
                  slli       a2, a4, 25
                  slli       a2, a4, 25
                  c.srai     s1, 28
                  c.srai     s1, 28
                  slt        a0, s5, s11
                  slli       a2, a4, 25
                  slt        a0, s5, s11
                  c.and      a4, s1
                  c.srai     s1, 28
                  andi       t0, a3, 147
                  sra        s9, s4, t5
                  remu       s6, s3, t1
                  c.mv       a2, a0
                  sll        s8, s0, s6
                  c.sub      s0, s1
                  mulhu      s4, a6, t3
                  c.srai     s1, 28
                  c.lui      a6, 24
                  lui        s3, 985951
                  lui        s3, 985951
                  xori       t3, t1, -721
                  slli       a2, a4, 25
                  c.sub      s0, s1
                  c.addi16sp sp, -16
                  sltiu      s3, tp, 300
                  slti       tp, a1, -167
                  c.xor      a4, a5
                  lui        s3, 985951
                  c.or       a0, a2
                  ori        tp, a0, -848
                  c.and      a4, s1
                  c.xor      a4, a5
                  xori       t3, t1, -721
                  c.mv       a2, a0
                  sltu       s3, a6, a4
                  c.xor      a4, a5
                  sub        s0, t3, gp
                  mul        tp, s2, t5
                  sra        s9, s4, t5
                  xor        s11, zero, s7
                  ori        tp, a0, -848
                  xor        s11, zero, s7
                  c.andi     s1, 31
                  divu       tp, s5, t4
                  mulh       s1, t4, s11
                  div        s7, gp, a4
                  c.add      t3, t1
                  lui        s3, 985951
                  add        s4, a7, s6
                  mulhu      s4, a6, t3
                  mulhu      s4, a6, t3
                  andi       t0, a3, 147
                  srl        t1, tp, zero
                  c.sub      s0, s1
                  andi       t0, a3, 147
                  slt        a0, s5, s11
                  c.and      a4, s1
                  sub        s0, t3, gp
                  c.addi16sp sp, -16
                  mulhsu     tp, t5, a6
                  sltu       s3, a6, a4
                  nop
                  mulhu      s4, a6, t3
                  slt        a0, s5, s11
                  sub        s0, t3, gp
                  c.andi     s1, 31
                  mul        tp, s2, t5
                  slti       tp, a1, -167
                  mulhu      s4, a6, t3
                  c.addi16sp sp, -16
                  or         a4, a4, zero
                  c.mv       a2, a0
                  c.xor      a4, a5
                  div        s7, gp, a4
                  sra        s9, s4, t5
                  c.andi     s1, 31
                  divu       tp, s5, t4
                  nop
                  c.mv       a2, a0
                  c.xor      a4, a5
                  and        s6, t2, a4
                  add        s4, a7, s6
                  remu       s6, s3, t1
                  slti       tp, a1, -167
                  c.nop
                  mulhu      s4, a6, t3
                  div        s7, gp, a4
                  c.addi     s9, -1
                  c.li       s11, -1
                  srl        t1, tp, zero
                  slti       tp, a1, -167
                  c.addi4spn a2, sp, 528
                  c.addi16sp sp, -16
                  rem        a2, s2, s9
                  sltu       s3, a6, a4
                  divu       tp, s5, t4
                  rem        a2, s2, s9
                  c.slli     t5, 22
                  srl        t1, tp, zero
                  c.sub      s0, s1
                  c.and      a4, s1
                  mul        tp, s2, t5
                  sltiu      s3, tp, 300
                  c.andi     s1, 31
                  srai       a4, a3, 0
                  sll        s8, s0, s6
                  rem        a2, s2, s9
                  ori        tp, a0, -848
                  remu       s6, s3, t1
                  srl        t1, tp, zero
                  lui        s3, 985951
                  slti       tp, a1, -167
                  auipc      s1, 11691
                  c.li       s11, -1
                  ori        tp, a0, -848
                  mulhu      s4, a6, t3
                  slt        a0, s5, s11
                  xori       t3, t1, -721
                  srai       a4, a3, 0
                  slti       tp, a1, -167
                  c.add      t3, t1
                  sll        s8, s0, s6
                  add        s4, a7, s6
                  mulhu      s4, a6, t3
                  mulhsu     tp, t5, a6
                  c.addi4spn a2, sp, 528
                  c.nop
                  c.or       a0, a2
                  add        s4, a7, s6
                  auipc      s1, 11691
                  srli       zero, a0, 13
                  sll        s8, s0, s6
                  sub        s0, t3, gp
                  c.lui      a6, 24
                  c.slli     t5, 22
                  slti       tp, a1, -167
                  c.sub      s0, s1
                  c.srai     s1, 28
                  divu       tp, s5, t4
                  c.addi16sp sp, -16
                  sra        s9, s4, t5
                  c.xor      a4, a5
                  sltiu      s3, tp, 300
                  remu       s6, s3, t1
                  sll        s8, s0, s6
                  c.srai     s1, 28
                  srl        t1, tp, zero
                  ori        tp, a0, -848
                  c.addi4spn a2, sp, 528
                  sltiu      s3, tp, 300
                  mulh       s1, t4, s11
                  sltu       s3, a6, a4
                  c.addi16sp sp, -16
                  c.sub      s0, s1
                  c.slli     t5, 22
                  c.sub      s0, s1
                  xor        s11, zero, s7
                  or         a4, a4, zero
                  c.li       s11, -1
                  add        s4, a7, s6
                  slli       a2, a4, 25
                  and        s6, t2, a4
                  ori        tp, a0, -848
                  c.add      t3, t1
                  c.mv       a2, a0
                  c.sub      s0, s1
                  c.lui      a6, 24
                  c.sub      s0, s1
                  c.and      a4, s1
                  c.addi4spn a2, sp, 528
                  xor        s11, zero, s7
                  slti       tp, a1, -167
                  auipc      s1, 11691
                  c.addi4spn a2, sp, 528
                  c.srli     a4, 9
                  mulhsu     tp, t5, a6
                  slt        a0, s5, s11
                  slti       tp, a1, -167
                  nop
                  ori        tp, a0, -848
                  add        s4, a7, s6
                  xor        s11, zero, s7
                  mul        tp, s2, t5
                  remu       s6, s3, t1
                  nop
                  sra        s9, s4, t5
                  srl        t1, tp, zero
                  c.andi     s1, 31
                  addi       gp, s8, -298
                  rem        a2, s2, s9
                  c.slli     t5, 22
                  c.or       a0, a2
                  mulhu      s4, a6, t3
                  xor        s11, zero, s7
                  c.sub      s0, s1
                  or         a4, a4, zero
                  mul        tp, s2, t5
                  or         a4, a4, zero
                  c.addi     s9, -1
                  mulhsu     tp, t5, a6
                  sltu       s3, a6, a4
                  c.addi     s9, -1
                  sltiu      s3, tp, 300
                  remu       s6, s3, t1
                  sub        s0, t3, gp
                  c.addi     s9, -1
                  c.and      a4, s1
                  div        s7, gp, a4
                  c.andi     s1, 31
                  lui        s3, 985951
                  nop
                  srai       a4, a3, 0
                  sltiu      s3, tp, 300
                  sub        s0, t3, gp
                  srai       a4, a3, 0
                  c.addi4spn a2, sp, 528
                  c.nop
                  addi       gp, s8, -298
                  c.srai     s1, 28
                  and        s6, t2, a4
                  sltu       s3, a6, a4
                  c.slli     t5, 22
                  mulhsu     tp, t5, a6
                  srl        t1, tp, zero
                  slt        a0, s5, s11
                  auipc      s1, 11691
                  c.addi4spn a2, sp, 528
                  c.and      a4, s1
                  sub        s0, t3, gp
                  c.add      t3, t1
                  and        s6, t2, a4
                  andi       t0, a3, 147
                  remu       s6, s3, t1
                  remu       s6, s3, t1
                  srli       zero, a0, 13
                  srli       zero, a0, 13
                  c.li       s11, -1
                  c.and      a4, s1
                  c.addi     s9, -1
                  c.sub      s0, s1
                  and        s6, t2, a4
                  addi       gp, s8, -298
                  c.lui      a6, 24
                  c.xor      a4, a5
                  c.addi16sp sp, -16
                  sltu       s3, a6, a4
                  mul        tp, s2, t5
                  srai       a4, a3, 0
                  c.and      a4, s1
                  srli       zero, a0, 13
                  sll        s8, s0, s6
                  auipc      s1, 11691
                  sub        s0, t3, gp
                  c.addi16sp sp, -16
                  auipc      s1, 11691
                  c.addi     s9, -1
                  nop
                  mulhsu     tp, t5, a6
                  c.addi     s9, -1
                  c.slli     t5, 22
                  addi       gp, s8, -298
                  c.srli     a4, 9
                  slti       tp, a1, -167
                  addi       gp, s8, -298
                  divu       tp, s5, t4
                  sltiu      s3, tp, 300
                  mul        tp, s2, t5
                  and        s6, t2, a4
                  c.srai     s1, 28
                  c.addi4spn a2, sp, 528
                  c.lui      a6, 24
                  ori        tp, a0, -848
                  c.addi     s9, -1
                  mulh       s1, t4, s11
                  srl        t1, tp, zero
                  auipc      s1, 11691
                  slt        a0, s5, s11
                  c.nop
                  c.srli     a4, 9
                  andi       t0, a3, 147
                  add        s4, a7, s6
                  nop
                  c.sub      s0, s1
                  mul        tp, s2, t5
                  sltu       s3, a6, a4
                  lui        s3, 985951
                  div        s7, gp, a4
                  xor        s11, zero, s7
                  sra        s9, s4, t5
                  sltu       s3, a6, a4
                  c.nop
                  sltiu      s3, tp, 300
                  auipc      s1, 11691
                  c.addi16sp sp, -16
                  ori        tp, a0, -848
                  sra        s9, s4, t5
                  xor        s11, zero, s7
                  mulh       s1, t4, s11
                  c.addi16sp sp, -16
                  slt        a0, s5, s11
                  lui        s3, 985951
                  c.srai     s1, 28
                  c.li       s11, -1
                  c.addi4spn a2, sp, 528
                  mulhsu     tp, t5, a6
                  sltiu      s3, tp, 300
                  mul        tp, s2, t5
                  sltiu      s3, tp, 300
                  c.li       s11, -1
                  xori       t3, t1, -721
                  rem        a2, s2, s9
                  add        s4, a7, s6
                  c.li       s11, -1
                  andi       t0, a3, 147
                  slt        a0, s5, s11
                  xori       t3, t1, -721
                  mulh       s1, t4, s11
                  slli       a2, a4, 25
                  c.nop
                  sltu       s3, a6, a4
                  c.or       a0, a2
                  mulhsu     tp, t5, a6
                  srl        t1, tp, zero
                  mulhu      s4, a6, t3
                  slli       a2, a4, 25
                  srai       a4, a3, 0
                  srli       zero, a0, 13
                  add        s4, a7, s6
                  slti       tp, a1, -167
                  mulhsu     tp, t5, a6
                  div        s7, gp, a4
                  xor        s11, zero, s7
                  c.nop
                  c.mv       a2, a0
                  c.addi16sp sp, -16
                  xor        s11, zero, s7
                  or         a4, a4, zero
                  xor        s11, zero, s7
                  sltiu      s3, tp, 300
                  sll        s8, s0, s6
                  remu       s6, s3, t1
                  remu       s6, s3, t1
                  c.nop
                  addi       gp, s8, -298
                  c.slli     t5, 22
                  c.and      a4, s1
                  sltiu      s3, tp, 300
                  sltu       s3, a6, a4
                  c.mv       a2, a0
                  mulhu      s4, a6, t3
                  c.mv       a2, a0
                  c.xor      a4, a5
                  c.xor      a4, a5
                  sltiu      s3, tp, 300
                  slli       a2, a4, 25
                  c.li       s11, -1
                  andi       t0, a3, 147
                  c.add      t3, t1
                  remu       s6, s3, t1
                  c.addi     s9, -1
                  c.xor      a4, a5
                  c.or       a0, a2
                  sll        s8, s0, s6
                  c.srli     a4, 9
                  remu       s6, s3, t1
                  srli       zero, a0, 13
                  nop
                  c.xor      a4, a5
                  auipc      s1, 11691
                  c.and      a4, s1
                  sltiu      s3, tp, 300
                  c.lui      a6, 24
                  xori       t3, t1, -721
                  mulh       s1, t4, s11
                  c.srli     a4, 9
                  c.addi     s9, -1
                  auipc      s1, 11691
                  and        s6, t2, a4
                  c.or       a0, a2
                  mulhsu     tp, t5, a6
                  mulh       s1, t4, s11
                  sltu       s3, a6, a4
                  slt        a0, s5, s11
                  xor        s11, zero, s7
                  c.addi4spn a2, sp, 528
                  c.srai     s1, 28
                  add        s4, a7, s6
                  addi       gp, s8, -298
                  sub        s0, t3, gp
                  divu       tp, s5, t4
                  mulh       s1, t4, s11
                  mulhsu     tp, t5, a6
                  c.srli     a4, 9
                  andi       t0, a3, 147
                  auipc      s1, 11691
                  lui        s3, 985951
                  sltiu      s3, tp, 300
                  c.and      a4, s1
                  c.andi     s1, 31
                  rem        a2, s2, s9
                  sltu       s3, a6, a4
                  div        s7, gp, a4
                  c.xor      a4, a5
                  divu       tp, s5, t4
                  slti       tp, a1, -167
                  c.addi16sp sp, -16
                  c.addi16sp sp, -16
                  and        s6, t2, a4
                  or         a4, a4, zero
                  slti       tp, a1, -167
                  slt        a0, s5, s11
                  c.addi4spn a2, sp, 528
                  c.srli     a4, 9
                  xor        s11, zero, s7
                  sra        s9, s4, t5
                  c.slli     t5, 22
                  c.or       a0, a2
                  nop
                  rem        a2, s2, s9
                  remu       s6, s3, t1
                  c.li       s11, -1
                  c.addi16sp sp, -16
                  c.lui      a6, 24
                  li         sp, 0x80000000 #start riscv_int_numeric_corner_stream_25
                  li         s3, 0x80000000
                  li         s1, 0x0
                  li         t2, 0x80000000
                  li         t5, 0x80000000
                  li         a2, 0x80000000
                  li         gp, 0x80000000
                  li         t3, 0x80000000
                  li         a3, 0x80000000
                  li         s5, 0xffffffff
                  rem        a2, sp, t2
                  addi       s1, s3, -40
                  mulhu      s5, sp, t5
                  mulhsu     t5, t2, gp
                  remu       s1, s3, a2
                  rem        a2, sp, t2
                  lui        s3, 985951
                  mul        t2, a2, a3
                  remu       s1, s3, a2
                  add        t5, sp, t5
                  nop
                  mulhu      s5, sp, t5
                  lui        s3, 985951
                  lui        s3, 985951
                  sub        sp, s1, t3
                  sub        sp, s1, t3
                  sub        sp, s1, t3
                  remu       s1, s3, a2
                  mulhu      s5, sp, t5 #end riscv_int_numeric_corner_stream_25
                  c.li       s11, -1
                  xori       t3, t1, -721
                  c.andi     s1, 31
                  sra        s9, s4, t5
                  slt        a0, s5, s11
                  ori        tp, a0, -848
                  c.and      a4, s1
                  c.addi16sp sp, -16
                  remu       s6, s3, t1
                  mulhsu     tp, t5, a6
                  mulhsu     tp, t5, a6
                  c.slli     t5, 22
                  c.lui      a6, 24
                  sll        s8, s0, s6
                  mulhsu     tp, t5, a6
                  mulhsu     tp, t5, a6
                  c.li       s11, -1
                  mulhsu     tp, t5, a6
                  div        s7, gp, a4
                  nop
                  c.addi4spn a2, sp, 528
                  slt        a0, s5, s11
                  xor        s11, zero, s7
                  c.addi     s9, -1
                  nop
                  sub        s0, t3, gp
                  nop
                  add        s4, a7, s6
                  ori        tp, a0, -848
                  c.slli     t5, 22
                  srai       a4, a3, 0
                  mulh       s1, t4, s11
                  srl        t1, tp, zero
                  ori        tp, a0, -848
                  c.slli     t5, 22
                  c.li       s11, -1
                  c.srli     a4, 9
                  c.lui      a6, 24
                  c.mv       a2, a0
                  remu       s6, s3, t1
                  c.addi     s9, -1
                  or         a4, a4, zero
                  divu       tp, s5, t4
                  sub        s0, t3, gp
                  xori       t3, t1, -721
                  c.andi     s1, 31
                  srli       zero, a0, 13
                  sltiu      s3, tp, 300
                  srai       a4, a3, 0
                  slt        a0, s5, s11
                  c.lui      a6, 24
                  c.or       a0, a2
                  c.addi16sp sp, -16
                  c.or       a0, a2
                  andi       t0, a3, 147
                  c.or       a0, a2
                  c.nop
                  xori       t3, t1, -721
                  xori       t3, t1, -721
                  remu       s6, s3, t1
                  slt        a0, s5, s11
                  c.li       s11, -1
                  c.addi     s9, -1
                  c.sub      s0, s1
                  srl        t1, tp, zero
                  mulhsu     tp, t5, a6
                  xori       t3, t1, -721
                  add        s4, a7, s6
                  sll        s8, s0, s6
                  slli       a2, a4, 25
                  mulhu      s4, a6, t3
                  ori        tp, a0, -848
                  c.lui      a6, 24
                  c.srai     s1, 28
                  slt        a0, s5, s11
                  nop
                  sltu       s3, a6, a4
                  add        s4, a7, s6
                  auipc      s1, 11691
                  c.li       s11, -1
                  rem        a2, s2, s9
                  xori       t3, t1, -721
                  c.li       s11, -1
                  sll        s8, s0, s6
                  c.andi     s1, 31
                  rem        a2, s2, s9
                  c.xor      a4, a5
                  c.add      t3, t1
                  sltiu      s3, tp, 300
                  c.lui      a6, 24
                  c.li       s11, -1
                  and        s6, t2, a4
                  mulhsu     tp, t5, a6
                  c.addi     s9, -1
                  slti       tp, a1, -167
                  mulhsu     tp, t5, a6
                  add        s4, a7, s6
                  c.or       a0, a2
                  c.lui      a6, 24
                  mul        tp, s2, t5
                  c.li       s11, -1
                  c.srli     a4, 9
                  mulhsu     tp, t5, a6
                  ori        tp, a0, -848
                  remu       s6, s3, t1
                  c.nop
                  sra        s9, s4, t5
                  nop
                  c.slli     t5, 22
                  auipc      s1, 11691
                  and        s6, t2, a4
                  remu       s6, s3, t1
                  mulhu      s4, a6, t3
                  mulhsu     tp, t5, a6
                  c.srai     s1, 28
                  c.sub      s0, s1
                  c.srli     a4, 9
                  ori        tp, a0, -848
                  slti       tp, a1, -167
                  c.slli     t5, 22
                  srai       a4, a3, 0
                  rem        a2, s2, s9
                  c.and      a4, s1
                  addi       gp, s8, -298
                  c.and      a4, s1
                  slli       a2, a4, 25
                  lui        s3, 985951
                  andi       t0, a3, 147
                  c.sub      s0, s1
                  div        s7, gp, a4
                  srl        t1, tp, zero
                  remu       s6, s3, t1
                  sltu       s3, a6, a4
                  addi       gp, s8, -298
                  remu       s6, s3, t1
                  c.addi4spn a2, sp, 528
                  slt        a0, s5, s11
                  add        s4, a7, s6
                  divu       tp, s5, t4
                  mul        tp, s2, t5
                  andi       t0, a3, 147
                  c.addi     s9, -1
                  ori        tp, a0, -848
                  addi       gp, s8, -298
                  c.sub      s0, s1
                  add        s4, a7, s6
                  ori        tp, a0, -848
                  divu       tp, s5, t4
                  slli       a2, a4, 25
                  xor        s11, zero, s7
                  xori       t3, t1, -721
                  c.sub      s0, s1
                  srai       a4, a3, 0
                  srai       a4, a3, 0
                  andi       t0, a3, 147
                  c.addi     s9, -1
                  c.addi4spn a2, sp, 528
                  srai       a4, a3, 0
                  div        s7, gp, a4
                  c.slli     t5, 22
                  div        s7, gp, a4
                  c.sub      s0, s1
                  c.xor      a4, a5
                  c.srai     s1, 28
                  c.and      a4, s1
                  c.mv       a2, a0
                  ori        tp, a0, -848
                  c.mv       a2, a0
                  srl        t1, tp, zero
                  nop
                  c.xor      a4, a5
                  c.addi     s9, -1
                  or         a4, a4, zero
                  c.srai     s1, 28
                  sra        s9, s4, t5
                  rem        a2, s2, s9
                  and        s6, t2, a4
                  c.or       a0, a2
                  nop
                  c.addi4spn a2, sp, 528
                  xori       t3, t1, -721
                  remu       s6, s3, t1
                  sub        s0, t3, gp
                  c.lui      a6, 24
                  addi       gp, s8, -298
                  addi       gp, s8, -298
                  add        s4, a7, s6
                  xori       t3, t1, -721
                  and        s6, t2, a4
                  xor        s11, zero, s7
                  xori       t3, t1, -721
                  c.srli     a4, 9
                  li         s10, 0x0 #start riscv_int_numeric_corner_stream_13
                  li         s7, 0x0
                  li         a4, 0xffffffff
                  li         s8, 0xffffffff
                  li         t4, 0x1fef3313
                  li         a6, 0x0
                  li         s5, 0x80000000
                  li         a2, 0x0
                  li         s4, 0x5e753a47
                  li         s1, 0x80000000
                  mulhu      a2, a4, t4
                  mul        a4, s4, a4
                  nop
                  nop
                  nop
                  nop
                  lui        s7, 985951
                  lui        s7, 985951
                  lui        s7, 985951
                  nop
                  lui        s7, 985951
                  divu       s10, a4, s8
                  sub        s10, a4, s8
                  lui        s7, 985951
                  div        s1, t4, a6
                  sub        s10, a4, s8
                  addi       s1, s10, -40
                  mulhsu     a4, s1, s5
                  add        s4, a2, s10
                  mul        a4, s4, a4
                  divu       s10, a4, s8
                  lui        s7, 985951
                  mulh       a4, s1, s1
                  lui        s7, 985951
                  nop
                  remu       a4, s10, a4
                  add        s4, a2, s10
                  addi       s1, s10, -40
                  nop #end riscv_int_numeric_corner_stream_13
                  mulhsu     tp, t5, a6
                  ori        tp, a0, -848
                  or         a4, a4, zero
                  mul        tp, s2, t5
                  or         a4, a4, zero
                  auipc      s1, 11691
                  add        s4, a7, s6
                  lui        s3, 985951
                  c.srli     a4, 9
                  c.li       s11, -1
                  and        s6, t2, a4
                  sltiu      s3, tp, 300
                  c.addi     s9, -1
                  c.lui      a6, 24
                  sub        s0, t3, gp
                  slli       a2, a4, 25
                  add        s4, a7, s6
                  lui        s3, 985951
                  mulhsu     tp, t5, a6
                  sll        s8, s0, s6
                  auipc      s1, 11691
                  c.slli     t5, 22
                  c.and      a4, s1
                  c.addi4spn a2, sp, 528
                  c.nop
                  slti       tp, a1, -167
                  srl        t1, tp, zero
                  sub        s0, t3, gp
                  c.addi     s9, -1
                  c.lui      a6, 24
                  c.or       a0, a2
                  c.sub      s0, s1
                  c.or       a0, a2
                  ori        tp, a0, -848
                  mul        tp, s2, t5
                  sltu       s3, a6, a4
                  or         a4, a4, zero
                  c.nop
                  auipc      s1, 11691
                  sltu       s3, a6, a4
                  c.add      t3, t1
                  c.srai     s1, 28
                  c.li       s11, -1
                  c.xor      a4, a5
                  mul        tp, s2, t5
                  auipc      s1, 11691
                  c.lui      a6, 24
                  c.andi     s1, 31
                  xor        s11, zero, s7
                  mulh       s1, t4, s11
                  addi       gp, s8, -298
                  c.and      a4, s1
                  c.and      a4, s1
                  mulhu      s4, a6, t3
                  slti       tp, a1, -167
                  mulhsu     tp, t5, a6
                  andi       t0, a3, 147
                  or         a4, a4, zero
                  addi       gp, s8, -298
                  c.li       s11, -1
                  c.li       s11, -1
                  mulh       s1, t4, s11
                  nop
                  divu       tp, s5, t4
                  or         a4, a4, zero
                  slti       tp, a1, -167
                  add        s4, a7, s6
                  addi       gp, s8, -298
                  xor        s11, zero, s7
                  c.addi     s9, -1
                  c.add      t3, t1
                  sltu       s3, a6, a4
                  mul        tp, s2, t5
                  mul        tp, s2, t5
                  divu       tp, s5, t4
                  andi       t0, a3, 147
                  nop
                  c.andi     s1, 31
                  add        s4, a7, s6
                  and        s6, t2, a4
                  slt        a0, s5, s11
                  divu       tp, s5, t4
                  xori       t3, t1, -721
                  xori       t3, t1, -721
                  xor        s11, zero, s7
                  sltu       s3, a6, a4
                  remu       s6, s3, t1
                  xori       t3, t1, -721
                  c.andi     s1, 31
                  c.slli     t5, 22
                  mulhsu     tp, t5, a6
                  div        s7, gp, a4
                  auipc      s1, 11691
                  xori       t3, t1, -721
                  add        s4, a7, s6
                  slli       a2, a4, 25
                  c.nop
                  auipc      s1, 11691
                  c.xor      a4, a5
                  sra        s9, s4, t5
                  addi       gp, s8, -298
                  and        s6, t2, a4
                  c.addi     s9, -1
                  c.and      a4, s1
                  sll        s8, s0, s6
                  add        s4, a7, s6
                  sll        s8, s0, s6
                  c.srai     s1, 28
                  c.or       a0, a2
                  mul        tp, s2, t5
                  sub        s0, t3, gp
                  c.add      t3, t1
                  xor        s11, zero, s7
                  remu       s6, s3, t1
                  nop
                  c.srli     a4, 9
                  sll        s8, s0, s6
                  slt        a0, s5, s11
                  c.addi16sp sp, -16
                  auipc      s1, 11691
                  c.andi     s1, 31
                  c.sub      s0, s1
                  c.srai     s1, 28
                  srl        t1, tp, zero
                  nop
                  lui        s3, 985951
                  sub        s0, t3, gp
                  c.andi     s1, 31
                  ori        tp, a0, -848
                  mulhu      s4, a6, t3
                  c.or       a0, a2
                  mulhu      s4, a6, t3
                  auipc      s1, 11691
                  srli       zero, a0, 13
                  sra        s9, s4, t5
                  slti       tp, a1, -167
                  c.addi     s9, -1
                  c.mv       a2, a0
                  c.li       s11, -1
                  c.addi4spn a2, sp, 528
                  c.nop
                  divu       tp, s5, t4
                  sll        s8, s0, s6
                  srl        t1, tp, zero
                  mulhsu     tp, t5, a6
                  rem        a2, s2, s9
                  slli       a2, a4, 25
                  c.addi16sp sp, -16
                  sub        s0, t3, gp
                  sltiu      s3, tp, 300
                  c.nop
                  srl        t1, tp, zero
                  c.andi     s1, 31
                  c.add      t3, t1
                  sltu       s3, a6, a4
                  remu       s6, s3, t1
                  slt        a0, s5, s11
                  and        s6, t2, a4
                  c.srli     a4, 9
                  sltu       s3, a6, a4
                  auipc      s1, 11691
                  and        s6, t2, a4
                  rem        a2, s2, s9
                  slt        a0, s5, s11
                  rem        a2, s2, s9
                  srli       zero, a0, 13
                  mul        tp, s2, t5
                  or         a4, a4, zero
                  c.xor      a4, a5
                  div        s7, gp, a4
                  c.sub      s0, s1
                  c.slli     t5, 22
                  slli       a2, a4, 25
                  srl        t1, tp, zero
                  mulhu      s4, a6, t3
                  c.srli     a4, 9
                  divu       tp, s5, t4
                  c.xor      a4, a5
                  srai       a4, a3, 0
                  slt        a0, s5, s11
                  c.addi16sp sp, -16
                  c.li       s11, -1
                  xori       t3, t1, -721
                  c.addi4spn a2, sp, 528
                  c.lui      a6, 24
                  c.srli     a4, 9
                  sltiu      s3, tp, 300
                  c.addi     s9, -1
                  xor        s11, zero, s7
                  c.and      a4, s1
                  slt        a0, s5, s11
                  xori       t3, t1, -721
                  c.xor      a4, a5
                  slti       tp, a1, -167
                  remu       s6, s3, t1
                  c.and      a4, s1
                  remu       s6, s3, t1
                  add        s4, a7, s6
                  c.lui      a6, 24
                  c.or       a0, a2
                  xor        s11, zero, s7
                  slti       tp, a1, -167
                  sub        s0, t3, gp
                  c.addi4spn a2, sp, 528
                  c.addi     s9, -1
                  c.mv       a2, a0
                  xor        s11, zero, s7
                  remu       s6, s3, t1
                  srli       zero, a0, 13
                  remu       s6, s3, t1
                  div        s7, gp, a4
                  c.add      t3, t1
                  c.mv       a2, a0
                  c.addi16sp sp, -16
                  c.srli     a4, 9
                  lui        s3, 985951
                  mulhu      s4, a6, t3
                  c.srli     a4, 9
                  c.slli     t5, 22
                  sltu       s3, a6, a4
                  sub        s0, t3, gp
                  sub        s0, t3, gp
                  slti       tp, a1, -167
                  c.li       s11, -1
                  sltiu      s3, tp, 300
                  and        s6, t2, a4
                  slli       a2, a4, 25
                  slt        a0, s5, s11
                  slti       tp, a1, -167
                  sra        s9, s4, t5
                  c.add      t3, t1
                  c.slli     t5, 22
                  srai       a4, a3, 0
                  add        s4, a7, s6
                  ori        tp, a0, -848
                  c.sub      s0, s1
                  sltu       s3, a6, a4
                  addi       gp, s8, -298
                  remu       s6, s3, t1
                  add        s4, a7, s6
                  c.mv       a2, a0
                  srl        t1, tp, zero
                  c.or       a0, a2
                  c.slli     t5, 22
                  sll        s8, s0, s6
                  c.or       a0, a2
                  and        s6, t2, a4
                  slti       tp, a1, -167
                  c.add      t3, t1
                  nop
                  c.mv       a2, a0
                  sll        s8, s0, s6
                  rem        a2, s2, s9
                  c.or       a0, a2
                  lui        s3, 985951
                  sll        s8, s0, s6
                  sltu       s3, a6, a4
                  xori       t3, t1, -721
                  c.or       a0, a2
                  andi       t0, a3, 147
                  addi       gp, s8, -298
                  sltu       s3, a6, a4
                  c.addi16sp sp, -16
                  c.andi     s1, 31
                  or         a4, a4, zero
                  c.srai     s1, 28
                  c.mv       a2, a0
                  sltu       s3, a6, a4
                  sltu       s3, a6, a4
                  divu       tp, s5, t4
                  divu       tp, s5, t4
                  c.or       a0, a2
                  c.andi     s1, 31
                  mulh       s1, t4, s11
                  c.nop
                  slti       tp, a1, -167
                  slt        a0, s5, s11
                  c.or       a0, a2
                  div        s7, gp, a4
                  c.addi16sp sp, -16
                  c.srli     a4, 9
                  c.xor      a4, a5
                  c.lui      a6, 24
                  nop
                  xori       t3, t1, -721
                  sub        s0, t3, gp
                  c.li       s11, -1
                  slli       a2, a4, 25
                  c.or       a0, a2
                  mul        tp, s2, t5
                  nop
                  auipc      s1, 11691
                  xori       t3, t1, -721
                  srli       zero, a0, 13
                  c.srai     s1, 28
                  srl        t1, tp, zero
                  auipc      s1, 11691
                  lui        s3, 985951
                  slt        a0, s5, s11
                  c.add      t3, t1
                  and        s6, t2, a4
                  auipc      s1, 11691
                  add        s4, a7, s6
                  c.andi     s1, 31
                  remu       s6, s3, t1
                  slli       a2, a4, 25
                  c.slli     t5, 22
                  c.li       s11, -1
                  slli       a2, a4, 25
                  mulh       s1, t4, s11
                  srli       zero, a0, 13
                  srl        t1, tp, zero
                  mul        tp, s2, t5
                  slt        a0, s5, s11
                  sltiu      s3, tp, 300
                  xori       t3, t1, -721
                  and        s6, t2, a4
                  c.lui      a6, 24
                  add        s4, a7, s6
                  c.addi4spn a2, sp, 528
                  slt        a0, s5, s11
                  c.xor      a4, a5
                  mul        tp, s2, t5
                  c.addi16sp sp, -16
                  nop
                  andi       t0, a3, 147
                  xor        s11, zero, s7
                  lui        s3, 985951
                  lui        s3, 985951
                  andi       t0, a3, 147
                  mulhu      s4, a6, t3
                  c.srli     a4, 9
                  c.srai     s1, 28
                  sltu       s3, a6, a4
                  or         a4, a4, zero
                  mulh       s1, t4, s11
                  c.mv       a2, a0
                  c.andi     s1, 31
                  mulh       s1, t4, s11
                  remu       s6, s3, t1
                  rem        a2, s2, s9
                  c.add      t3, t1
                  sltu       s3, a6, a4
                  c.srai     s1, 28
                  c.andi     s1, 31
                  c.and      a4, s1
                  and        s6, t2, a4
                  xor        s11, zero, s7
                  c.addi4spn a2, sp, 528
                  addi       gp, s8, -298
                  c.srli     a4, 9
                  c.nop
                  lui        s3, 985951
                  andi       t0, a3, 147
                  c.slli     t5, 22
                  addi       gp, s8, -298
                  auipc      s1, 11691
                  c.li       s11, -1
                  slli       a2, a4, 25
                  andi       t0, a3, 147
                  auipc      s1, 11691
                  mulhsu     tp, t5, a6
                  srli       zero, a0, 13
                  c.li       s11, -1
                  sra        s9, s4, t5
                  c.lui      a6, 24
                  c.addi16sp sp, -16
                  c.mv       a2, a0
                  div        s7, gp, a4
                  srli       zero, a0, 13
                  rem        a2, s2, s9
                  c.mv       a2, a0
                  and        s6, t2, a4
                  c.li       s11, -1
                  divu       tp, s5, t4
                  c.slli     t5, 22
                  c.addi4spn a2, sp, 528
                  slti       tp, a1, -167
                  c.xor      a4, a5
                  sltu       s3, a6, a4
                  c.lui      a6, 24
                  c.lui      a6, 24
                  sll        s8, s0, s6
                  addi       gp, s8, -298
                  sltiu      s3, tp, 300
                  add        s4, a7, s6
                  slli       a2, a4, 25
                  lui        s3, 985951
                  ori        tp, a0, -848
                  remu       s6, s3, t1
                  and        s6, t2, a4
                  c.add      t3, t1
                  and        s6, t2, a4
                  c.andi     s1, 31
                  div        s7, gp, a4
                  c.addi16sp sp, -16
                  auipc      s1, 11691
                  slli       a2, a4, 25
                  srai       a4, a3, 0
                  c.srai     s1, 28
                  xori       t3, t1, -721
                  mulhsu     tp, t5, a6
                  auipc      s1, 11691
                  c.and      a4, s1
                  c.li       s11, -1
                  div        s7, gp, a4
                  sra        s9, s4, t5
                  c.nop
                  c.or       a0, a2
                  c.xor      a4, a5
                  xor        s11, zero, s7
                  slt        a0, s5, s11
                  addi       gp, s8, -298
                  mulhu      s4, a6, t3
                  sub        s0, t3, gp
                  mulhu      s4, a6, t3
                  ori        tp, a0, -848
                  mulhu      s4, a6, t3
                  c.slli     t5, 22
                  srai       a4, a3, 0
                  sltu       s3, a6, a4
                  c.addi16sp sp, -16
                  xor        s11, zero, s7
                  sll        s8, s0, s6
                  divu       tp, s5, t4
                  c.xor      a4, a5
                  slti       tp, a1, -167
                  sltiu      s3, tp, 300
                  c.sub      s0, s1
                  addi       gp, s8, -298
                  c.add      t3, t1
                  slli       a2, a4, 25
                  srai       a4, a3, 0
                  c.lui      a6, 24
                  nop
                  c.addi16sp sp, -16
                  sra        s9, s4, t5
                  c.andi     s1, 31
                  or         a4, a4, zero
                  xori       t3, t1, -721
                  lui        s3, 985951
                  c.addi4spn a2, sp, 528
                  sra        s9, s4, t5
                  divu       tp, s5, t4
                  sra        s9, s4, t5
                  sra        s9, s4, t5
                  sub        s0, t3, gp
                  ori        tp, a0, -848
                  mulhsu     tp, t5, a6
                  c.li       s11, -1
                  c.xor      a4, a5
                  srli       zero, a0, 13
                  sltu       s3, a6, a4
                  c.sub      s0, s1
                  li         s1, 0xfb847450 #start riscv_int_numeric_corner_stream_27
                  li         tp, 0x80000000
                  li         t0, 0xffffffff
                  li         a2, 0x0
                  li         ra, 0xa187a44a
                  li         t1, 0x80000000
                  li         gp, 0xffffffff
                  li         a0, 0xffffffff
                  li         sp, 0x0
                  li         s11, 0xffffffff
                  nop
                  divu       t0, a0, s11
                  nop
                  lui        t1, 985951
                  add        t1, tp, a2
                  rem        tp, sp, t1
                  divu       t0, a0, s11
                  mulh       a2, tp, tp
                  mulh       a2, tp, tp
                  mulhu      ra, ra, t1
                  nop
                  rem        tp, sp, t1
                  lui        t1, 985951
                  addi       tp, s11, -40
                  remu       a2, s11, a0
                  mulhu      ra, ra, t1
                  nop
                  mulhsu     t0, t0, ra
                  nop
                  lui        t1, 985951
                  auipc      s1, 11691
                  rem        tp, sp, t1
                  add        t1, tp, a2
                  nop
                  mulhsu     t0, t0, ra
                  divu       t0, a0, s11
                  nop #end riscv_int_numeric_corner_stream_27
                  c.or       a0, a2
                  or         a4, a4, zero
                  slli       a2, a4, 25
                  c.sub      s0, s1
                  c.andi     s1, 31
                  c.li       s11, -1
                  remu       s6, s3, t1
                  div        s7, gp, a4
                  c.add      t3, t1
                  srli       zero, a0, 13
                  xor        s11, zero, s7
                  divu       tp, s5, t4
                  or         a4, a4, zero
                  add        s4, a7, s6
                  c.nop
                  auipc      s1, 11691
                  c.andi     s1, 31
                  addi       gp, s8, -298
                  c.addi     s9, -1
                  c.xor      a4, a5
                  sub        s0, t3, gp
                  or         a4, a4, zero
                  c.add      t3, t1
                  slt        a0, s5, s11
                  c.addi16sp sp, -16
                  remu       s6, s3, t1
                  add        s4, a7, s6
                  addi       gp, s8, -298
                  mulhu      s4, a6, t3
                  c.add      t3, t1
                  c.addi     s9, -1
                  c.lui      a6, 24
                  slt        a0, s5, s11
                  c.srai     s1, 28
                  c.xor      a4, a5
                  c.xor      a4, a5
                  srl        t1, tp, zero
                  addi       gp, s8, -298
                  sltu       s3, a6, a4
                  ori        tp, a0, -848
                  ori        tp, a0, -848
                  c.xor      a4, a5
                  c.li       s11, -1
                  andi       t0, a3, 147
                  xori       t3, t1, -721
                  slt        a0, s5, s11
                  sub        s0, t3, gp
                  auipc      s1, 11691
                  c.sub      s0, s1
                  sra        s9, s4, t5
                  sltiu      s3, tp, 300
                  mul        tp, s2, t5
                  xori       t3, t1, -721
                  or         a4, a4, zero
                  c.srai     s1, 28
                  mul        tp, s2, t5
                  or         a4, a4, zero
                  c.srli     a4, 9
                  srl        t1, tp, zero
                  div        s7, gp, a4
                  andi       t0, a3, 147
                  c.mv       a2, a0
                  addi       gp, s8, -298
                  divu       tp, s5, t4
                  nop
                  c.li       s11, -1
                  ori        tp, a0, -848
                  div        s7, gp, a4
                  c.andi     s1, 31
                  c.mv       a2, a0
                  andi       t0, a3, 147
                  sll        s8, s0, s6
                  c.xor      a4, a5
                  mulhsu     tp, t5, a6
                  mul        tp, s2, t5
                  sra        s9, s4, t5
                  srli       zero, a0, 13
                  rem        a2, s2, s9
                  c.mv       a2, a0
                  and        s6, t2, a4
                  mulhsu     tp, t5, a6
                  c.addi4spn a2, sp, 528
                  srai       a4, a3, 0
                  mulh       s1, t4, s11
                  c.nop
                  c.mv       a2, a0
                  div        s7, gp, a4
                  xori       t3, t1, -721
                  or         a4, a4, zero
                  sll        s8, s0, s6
                  addi       gp, s8, -298
                  sltiu      s3, tp, 300
                  sra        s9, s4, t5
                  slli       a2, a4, 25
                  slti       tp, a1, -167
                  div        s7, gp, a4
                  xori       t3, t1, -721
                  c.addi     s9, -1
                  slti       tp, a1, -167
                  mulhsu     tp, t5, a6
                  sra        s9, s4, t5
                  nop
                  ori        tp, a0, -848
                  slt        a0, s5, s11
                  c.nop
                  xor        s11, zero, s7
                  c.nop
                  c.andi     s1, 31
                  srl        t1, tp, zero
                  mulh       s1, t4, s11
                  slti       tp, a1, -167
                  sra        s9, s4, t5
                  slti       tp, a1, -167
                  div        s7, gp, a4
                  c.lui      a6, 24
                  nop
                  c.nop
                  mul        tp, s2, t5
                  c.and      a4, s1
                  c.li       s11, -1
                  slli       a2, a4, 25
                  c.li       s11, -1
                  mul        tp, s2, t5
                  c.sub      s0, s1
                  c.srli     a4, 9
                  srai       a4, a3, 0
                  div        s7, gp, a4
                  slti       tp, a1, -167
                  c.and      a4, s1
                  c.nop
                  c.or       a0, a2
                  c.lui      a6, 24
                  slt        a0, s5, s11
                  c.addi     s9, -1
                  c.and      a4, s1
                  slti       tp, a1, -167
                  sll        s8, s0, s6
                  ori        tp, a0, -848
                  add        s4, a7, s6
                  c.andi     s1, 31
                  srli       zero, a0, 13
                  divu       tp, s5, t4
                  c.andi     s1, 31
                  mul        tp, s2, t5
                  c.srai     s1, 28
                  srl        t1, tp, zero
                  c.sub      s0, s1
                  slti       tp, a1, -167
                  c.slli     t5, 22
                  srai       a4, a3, 0
                  c.slli     t5, 22
                  nop
                  slt        a0, s5, s11
                  lui        s3, 985951
                  mul        tp, s2, t5
                  mulhsu     tp, t5, a6
                  mulh       s1, t4, s11
                  sltu       s3, a6, a4
                  sub        s0, t3, gp
                  sra        s9, s4, t5
                  c.or       a0, a2
                  add        s4, a7, s6
                  sra        s9, s4, t5
                  auipc      s1, 11691
                  c.add      t3, t1
                  c.srli     a4, 9
                  mulhu      s4, a6, t3
                  xori       t3, t1, -721
                  c.and      a4, s1
                  c.srai     s1, 28
                  xori       t3, t1, -721
                  addi       gp, s8, -298
                  c.mv       a2, a0
                  ori        tp, a0, -848
                  c.addi16sp sp, -16
                  c.andi     s1, 31
                  mulhsu     tp, t5, a6
                  c.nop
                  sltiu      s3, tp, 300
                  auipc      s1, 11691
                  c.add      t3, t1
                  srl        t1, tp, zero
                  remu       s6, s3, t1
                  c.srli     a4, 9
                  c.nop
                  rem        a2, s2, s9
                  c.slli     t5, 22
                  add        s4, a7, s6
                  sll        s8, s0, s6
                  c.andi     s1, 31
                  srai       a4, a3, 0
                  ori        tp, a0, -848
                  srli       zero, a0, 13
                  lui        s3, 985951
                  mulhu      s4, a6, t3
                  mulh       s1, t4, s11
                  li         a4, 0xffffffff #start riscv_int_numeric_corner_stream_24
                  li         t3, 0x8f5c3da4
                  li         a6, 0xffffffff
                  li         a3, 0x71372280
                  li         s8, 0xbcdedf11
                  li         t5, 0xffffffff
                  li         a2, 0xffffffff
                  li         t0, 0xffffffff
                  li         s11, 0x80000000
                  li         ra, 0xffffffff
                  mulhu      ra, a3, t5
                  lui        s11, 985951
                  addi       t0, s11, -40
                  divu       s11, t5, s8
                  mulhu      ra, a3, t5
                  nop
                  remu       t5, a4, a4
                  add        t3, a2, t5
                  addi       t0, s11, -40
                  nop
                  divu       s11, t5, s8
                  div        s8, a2, ra
                  nop
                  mulhsu     t0, a2, ra
                  sub        a6, t5, s8
                  mulh       s8, s11, a2
                  mulhu      ra, a3, t5
                  lui        s11, 985951
                  addi       t0, s11, -40
                  nop
                  lui        s11, 985951
                  div        s8, a2, ra
                  addi       t0, s11, -40
                  sub        a6, t5, s8
                  addi       t0, s11, -40
                  div        s8, a2, ra
                  mulhsu     t0, a2, ra #end riscv_int_numeric_corner_stream_24
                  slti       tp, a1, -167
                  slti       tp, a1, -167
                  add        s4, a7, s6
                  xor        s11, zero, s7
                  c.lui      a6, 24
                  div        s7, gp, a4
                  c.and      a4, s1
                  mulhu      s4, a6, t3
                  xori       t3, t1, -721
                  c.slli     t5, 22
                  c.add      t3, t1
                  c.mv       a2, a0
                  ori        tp, a0, -848
                  slt        a0, s5, s11
                  c.or       a0, a2
                  c.and      a4, s1
                  srai       a4, a3, 0
                  auipc      s1, 11691
                  rem        a2, s2, s9
                  or         a4, a4, zero
                  c.slli     t5, 22
                  c.add      t3, t1
                  div        s7, gp, a4
                  c.or       a0, a2
                  mulhu      s4, a6, t3
                  divu       tp, s5, t4
                  slli       a2, a4, 25
                  c.xor      a4, a5
                  div        s7, gp, a4
                  andi       t0, a3, 147
                  div        s7, gp, a4
                  xor        s11, zero, s7
                  slli       a2, a4, 25
                  sltu       s3, a6, a4
                  c.andi     s1, 31
                  ori        tp, a0, -848
                  xori       t3, t1, -721
                  add        s4, a7, s6
                  c.or       a0, a2
                  c.li       s11, -1
                  or         a4, a4, zero
                  c.andi     s1, 31
                  mul        tp, s2, t5
                  mulh       s1, t4, s11
                  sub        s0, t3, gp
                  xori       t3, t1, -721
                  andi       t0, a3, 147
                  c.addi     s9, -1
                  nop
                  c.srli     a4, 9
                  c.or       a0, a2
                  lui        s3, 985951
                  xori       t3, t1, -721
                  divu       tp, s5, t4
                  c.or       a0, a2
                  mulhu      s4, a6, t3
                  xor        s11, zero, s7
                  c.srli     a4, 9
                  c.or       a0, a2
                  mulh       s1, t4, s11
                  ori        tp, a0, -848
                  srl        t1, tp, zero
                  nop
                  c.slli     t5, 22
                  add        s4, a7, s6
                  c.srai     s1, 28
                  add        s4, a7, s6
                  c.srli     a4, 9
                  nop
                  srl        t1, tp, zero
                  sra        s9, s4, t5
                  c.srai     s1, 28
                  c.xor      a4, a5
                  c.add      t3, t1
                  c.add      t3, t1
                  srai       a4, a3, 0
                  ori        tp, a0, -848
                  nop
                  mulh       s1, t4, s11
                  c.li       s11, -1
                  remu       s6, s3, t1
                  addi       gp, s8, -298
                  sltiu      s3, tp, 300
                  andi       t0, a3, 147
                  sub        s0, t3, gp
                  mul        tp, s2, t5
                  mulhsu     tp, t5, a6
                  c.addi4spn a2, sp, 528
                  slli       a2, a4, 25
                  sra        s9, s4, t5
                  mul        tp, s2, t5
                  c.addi16sp sp, -16
                  sub        s0, t3, gp
                  divu       tp, s5, t4
                  slt        a0, s5, s11
                  c.or       a0, a2
                  and        s6, t2, a4
                  c.or       a0, a2
                  mulh       s1, t4, s11
                  or         a4, a4, zero
                  ori        tp, a0, -848
                  c.nop
                  sll        s8, s0, s6
                  rem        a2, s2, s9
                  nop
                  sltiu      s3, tp, 300
                  c.andi     s1, 31
                  nop
                  slt        a0, s5, s11
                  slt        a0, s5, s11
                  c.mv       a2, a0
                  c.and      a4, s1
                  srai       a4, a3, 0
                  sltu       s3, a6, a4
                  c.andi     s1, 31
                  xor        s11, zero, s7
                  divu       tp, s5, t4
                  c.sub      s0, s1
                  or         a4, a4, zero
                  nop
                  c.addi16sp sp, -16
                  c.add      t3, t1
                  srai       a4, a3, 0
                  c.lui      a6, 24
                  or         a4, a4, zero
                  c.slli     t5, 22
                  c.slli     t5, 22
                  div        s7, gp, a4
                  mulh       s1, t4, s11
                  srl        t1, tp, zero
                  or         a4, a4, zero
                  c.or       a0, a2
                  and        s6, t2, a4
                  c.li       s11, -1
                  sltiu      s3, tp, 300
                  mulhu      s4, a6, t3
                  c.lui      a6, 24
                  srl        t1, tp, zero
                  lui        s3, 985951
                  c.mv       a2, a0
                  ori        tp, a0, -848
                  sltiu      s3, tp, 300
                  remu       s6, s3, t1
                  addi       gp, s8, -298
                  c.lui      a6, 24
                  c.and      a4, s1
                  and        s6, t2, a4
                  mulh       s1, t4, s11
                  sub        s0, t3, gp
                  c.or       a0, a2
                  addi       gp, s8, -298
                  c.li       s11, -1
                  or         a4, a4, zero
                  mul        tp, s2, t5
                  sltiu      s3, tp, 300
                  srai       a4, a3, 0
                  c.addi4spn a2, sp, 528
                  auipc      s1, 11691
                  add        s4, a7, s6
                  remu       s6, s3, t1
                  sll        s8, s0, s6
                  slt        a0, s5, s11
                  rem        a2, s2, s9
                  addi       gp, s8, -298
                  sll        s8, s0, s6
                  xori       t3, t1, -721
                  xor        s11, zero, s7
                  srli       zero, a0, 13
                  div        s7, gp, a4
                  slli       a2, a4, 25
                  c.add      t3, t1
                  c.addi16sp sp, -16
                  c.slli     t5, 22
                  nop
                  c.addi4spn a2, sp, 528
                  sll        s8, s0, s6
                  c.srai     s1, 28
                  c.addi4spn a2, sp, 528
                  addi       gp, s8, -298
                  auipc      s1, 11691
                  lui        s3, 985951
                  sra        s9, s4, t5
                  c.addi4spn a2, sp, 528
                  c.mv       a2, a0
                  remu       s6, s3, t1
                  and        s6, t2, a4
                  sltu       s3, a6, a4
                  slti       tp, a1, -167
                  mul        tp, s2, t5
                  sltiu      s3, tp, 300
                  xor        s11, zero, s7
                  srl        t1, tp, zero
                  mulh       s1, t4, s11
                  or         a4, a4, zero
                  rem        a2, s2, s9
                  c.nop
                  slli       a2, a4, 25
                  xori       t3, t1, -721
                  add        s4, a7, s6
                  srl        t1, tp, zero
                  addi       gp, s8, -298
                  slt        a0, s5, s11
                  c.lui      a6, 24
                  and        s6, t2, a4
                  andi       t0, a3, 147
                  slti       tp, a1, -167
                  c.addi16sp sp, -16
                  c.srli     a4, 9
                  add        s4, a7, s6
                  c.addi4spn a2, sp, 528
                  c.or       a0, a2
                  sra        s9, s4, t5
                  c.li       s11, -1
                  div        s7, gp, a4
                  c.li       s11, -1
                  and        s6, t2, a4
                  srli       zero, a0, 13
                  or         a4, a4, zero
                  srl        t1, tp, zero
                  c.mv       a2, a0
                  c.mv       a2, a0
                  lui        s3, 985951
                  c.andi     s1, 31
                  and        s6, t2, a4
                  andi       t0, a3, 147
                  mulhu      s4, a6, t3
                  mulh       s1, t4, s11
                  mulhu      s4, a6, t3
                  or         a4, a4, zero
                  addi       gp, s8, -298
                  or         a4, a4, zero
                  divu       tp, s5, t4
                  andi       t0, a3, 147
                  sll        s8, s0, s6
                  c.and      a4, s1
                  sltu       s3, a6, a4
                  c.addi     s9, -1
                  divu       tp, s5, t4
                  xori       t3, t1, -721
                  auipc      s1, 11691
                  sub        s0, t3, gp
                  slti       tp, a1, -167
                  c.andi     s1, 31
                  ori        tp, a0, -848
                  and        s6, t2, a4
                  xori       t3, t1, -721
                  slli       a2, a4, 25
                  addi       gp, s8, -298
                  mulh       s1, t4, s11
                  andi       t0, a3, 147
                  add        s4, a7, s6
                  c.or       a0, a2
                  rem        a2, s2, s9
                  slti       tp, a1, -167
                  auipc      s1, 11691
                  andi       t0, a3, 147
                  srli       zero, a0, 13
                  mulhu      s4, a6, t3
                  sra        s9, s4, t5
                  c.addi16sp sp, -16
                  sub        s0, t3, gp
                  c.or       a0, a2
                  c.mv       a2, a0
                  c.srai     s1, 28
                  sub        s0, t3, gp
                  xor        s11, zero, s7
                  nop
                  c.srli     a4, 9
                  or         a4, a4, zero
                  andi       t0, a3, 147
                  or         a4, a4, zero
                  c.or       a0, a2
                  slli       a2, a4, 25
                  slti       tp, a1, -167
                  c.xor      a4, a5
                  c.srli     a4, 9
                  xor        s11, zero, s7
                  sll        s8, s0, s6
                  c.lui      a6, 24
                  slt        a0, s5, s11
                  mulhu      s4, a6, t3
                  sra        s9, s4, t5
                  mulhu      s4, a6, t3
                  c.add      t3, t1
                  li         s6, 0x80000000 #start riscv_int_numeric_corner_stream_33
                  li         a3, 0x3f59d3a4
                  li         tp, 0x92610f89
                  li         a2, 0x0
                  li         gp, 0xffffffff
                  li         s4, 0xffffffff
                  li         t0, 0xffffffff
                  li         t2, 0xaade8403
                  li         a6, 0xbb5b45cc
                  li         s5, 0xffffffff
                  sub        a2, a6, s5
                  nop
                  nop
                  mulhsu     s6, t2, gp
                  add        s5, s6, s6
                  add        s5, s6, s6
                  rem        a6, a6, t2
                  nop
                  sub        a2, a6, s5
                  mulh       s5, a2, tp
                  add        s5, s6, s6
                  lui        gp, 985951
                  divu       tp, gp, a6
                  add        s5, s6, s6
                  nop
                  remu       a6, t2, a2 #end riscv_int_numeric_corner_stream_33
                  slli       a2, a4, 25
                  sll        s8, s0, s6
                  slt        a0, s5, s11
                  slli       a2, a4, 25
                  or         a4, a4, zero
                  c.srai     s1, 28
                  c.mv       a2, a0
                  sltu       s3, a6, a4
                  slli       a2, a4, 25
                  div        s7, gp, a4
                  addi       gp, s8, -298
                  mul        tp, s2, t5
                  slt        a0, s5, s11
                  rem        a2, s2, s9
                  c.li       s11, -1
                  c.addi16sp sp, -16
                  divu       tp, s5, t4
                  c.addi4spn a2, sp, 528
                  c.addi16sp sp, -16
                  c.addi16sp sp, -16
                  c.slli     t5, 22
                  srai       a4, a3, 0
                  c.mv       a2, a0
                  mulhu      s4, a6, t3
                  c.nop
                  slti       tp, a1, -167
                  mul        tp, s2, t5
                  xor        s11, zero, s7
                  slt        a0, s5, s11
                  xor        s11, zero, s7
                  ori        tp, a0, -848
                  c.addi     s9, -1
                  divu       tp, s5, t4
                  mulhu      s4, a6, t3
                  addi       gp, s8, -298
                  sll        s8, s0, s6
                  divu       tp, s5, t4
                  divu       tp, s5, t4
                  c.add      t3, t1
                  andi       t0, a3, 147
                  mul        tp, s2, t5
                  addi       gp, s8, -298
                  c.nop
                  c.sub      s0, s1
                  mulhsu     tp, t5, a6
                  mulh       s1, t4, s11
                  mulhu      s4, a6, t3
                  nop
                  mulhsu     tp, t5, a6
                  ori        tp, a0, -848
                  and        s6, t2, a4
                  mul        tp, s2, t5
                  c.sub      s0, s1
                  slt        a0, s5, s11
                  xor        s11, zero, s7
                  lui        s3, 985951
                  slli       a2, a4, 25
                  mulhu      s4, a6, t3
                  sltiu      s3, tp, 300
                  c.addi16sp sp, -16
                  xor        s11, zero, s7
                  mulhu      s4, a6, t3
                  c.add      t3, t1
                  c.slli     t5, 22
                  remu       s6, s3, t1
                  mulhu      s4, a6, t3
                  xori       t3, t1, -721
                  c.addi     s9, -1
                  srai       a4, a3, 0
                  div        s7, gp, a4
                  c.nop
                  sub        s0, t3, gp
                  add        s4, a7, s6
                  rem        a2, s2, s9
                  slti       tp, a1, -167
                  lui        s3, 985951
                  c.srli     a4, 9
                  c.li       s11, -1
                  sll        s8, s0, s6
                  slt        a0, s5, s11
                  xor        s11, zero, s7
                  nop
                  srli       zero, a0, 13
                  c.srli     a4, 9
                  div        s7, gp, a4
                  sltu       s3, a6, a4
                  mul        tp, s2, t5
                  srli       zero, a0, 13
                  add        s4, a7, s6
                  div        s7, gp, a4
                  c.or       a0, a2
                  mulh       s1, t4, s11
                  c.xor      a4, a5
                  c.addi     s9, -1
                  slti       tp, a1, -167
                  srl        t1, tp, zero
                  slt        a0, s5, s11
                  c.srai     s1, 28
                  c.addi4spn a2, sp, 528
                  mul        tp, s2, t5
                  c.addi     s9, -1
                  srli       zero, a0, 13
                  srl        t1, tp, zero
                  sll        s8, s0, s6
                  sltiu      s3, tp, 300
                  c.sub      s0, s1
                  c.addi4spn a2, sp, 528
                  or         a4, a4, zero
                  c.nop
                  mulhu      s4, a6, t3
                  c.andi     s1, 31
                  nop
                  div        s7, gp, a4
                  c.sub      s0, s1
                  auipc      s1, 11691
                  slli       a2, a4, 25
                  mulh       s1, t4, s11
                  divu       tp, s5, t4
                  c.li       s11, -1
                  srl        t1, tp, zero
                  c.li       s11, -1
                  c.lui      a6, 24
                  sltiu      s3, tp, 300
                  c.srai     s1, 28
                  slti       tp, a1, -167
                  ori        tp, a0, -848
                  c.nop
                  srl        t1, tp, zero
                  c.srai     s1, 28
                  div        s7, gp, a4
                  mulh       s1, t4, s11
                  mulh       s1, t4, s11
                  div        s7, gp, a4
                  sll        s8, s0, s6
                  c.nop
                  c.srai     s1, 28
                  mulhsu     tp, t5, a6
                  c.add      t3, t1
                  mulh       s1, t4, s11
                  remu       s6, s3, t1
                  xor        s11, zero, s7
                  add        s4, a7, s6
                  c.mv       a2, a0
                  sra        s9, s4, t5
                  c.addi     s9, -1
                  divu       tp, s5, t4
                  and        s6, t2, a4
                  add        s4, a7, s6
                  sub        s0, t3, gp
                  sltu       s3, a6, a4
                  nop
                  mulh       s1, t4, s11
                  xor        s11, zero, s7
                  c.addi16sp sp, -16
                  lui        s3, 985951
                  c.slli     t5, 22
                  c.li       s11, -1
                  sra        s9, s4, t5
                  c.addi16sp sp, -16
                  c.lui      a6, 24
                  divu       tp, s5, t4
                  xor        s11, zero, s7
                  div        s7, gp, a4
                  lui        s3, 985951
                  sra        s9, s4, t5
                  slli       a2, a4, 25
                  sra        s9, s4, t5
                  add        s4, a7, s6
                  sltu       s3, a6, a4
                  remu       s6, s3, t1
                  c.lui      a6, 24
                  sll        s8, s0, s6
                  srl        t1, tp, zero
                  addi       gp, s8, -298
                  addi       gp, s8, -298
                  c.sub      s0, s1
                  nop
                  mulhsu     tp, t5, a6
                  c.xor      a4, a5
                  c.li       s11, -1
                  rem        a2, s2, s9
                  c.li       s11, -1
                  xor        s11, zero, s7
                  c.addi4spn a2, sp, 528
                  add        s4, a7, s6
                  c.add      t3, t1
                  slti       tp, a1, -167
                  andi       t0, a3, 147
                  remu       s6, s3, t1
                  c.srai     s1, 28
                  sll        s8, s0, s6
                  c.srli     a4, 9
                  c.srai     s1, 28
                  c.lui      a6, 24
                  srl        t1, tp, zero
                  sll        s8, s0, s6
                  c.and      a4, s1
                  sll        s8, s0, s6
                  c.andi     s1, 31
                  rem        a2, s2, s9
                  slli       a2, a4, 25
                  c.or       a0, a2
                  c.add      t3, t1
                  rem        a2, s2, s9
                  slli       a2, a4, 25
                  c.srai     s1, 28
                  or         a4, a4, zero
                  and        s6, t2, a4
                  c.lui      a6, 24
                  sltu       s3, a6, a4
                  c.nop
                  srl        t1, tp, zero
                  c.or       a0, a2
                  addi       gp, s8, -298
                  add        s4, a7, s6
                  div        s7, gp, a4
                  c.li       s11, -1
                  andi       t0, a3, 147
                  sra        s9, s4, t5
                  slt        a0, s5, s11
                  sub        s0, t3, gp
                  c.srli     a4, 9
                  mulhu      s4, a6, t3
                  c.li       s11, -1
                  mul        tp, s2, t5
                  sra        s9, s4, t5
                  sub        s0, t3, gp
                  mul        tp, s2, t5
                  c.addi     s9, -1
                  remu       s6, s3, t1
                  c.addi16sp sp, -16
                  lui        s3, 985951
                  div        s7, gp, a4
                  c.andi     s1, 31
                  c.lui      a6, 24
                  lui        s3, 985951
                  slt        a0, s5, s11
                  rem        a2, s2, s9
                  mulh       s1, t4, s11
                  sra        s9, s4, t5
                  mulh       s1, t4, s11
                  xor        s11, zero, s7
                  mulh       s1, t4, s11
                  add        s4, a7, s6
                  slli       a2, a4, 25
                  c.addi     s9, -1
                  c.srli     a4, 9
                  c.srai     s1, 28
                  mul        tp, s2, t5
                  c.xor      a4, a5
                  or         a4, a4, zero
                  rem        a2, s2, s9
                  slti       tp, a1, -167
                  ori        tp, a0, -848
                  sltu       s3, a6, a4
                  c.addi     s9, -1
                  div        s7, gp, a4
                  srl        t1, tp, zero
                  c.nop
                  and        s6, t2, a4
                  c.addi4spn a2, sp, 528
                  sub        s0, t3, gp
                  slt        a0, s5, s11
                  srai       a4, a3, 0
                  sra        s9, s4, t5
                  c.lui      a6, 24
                  c.add      t3, t1
                  sub        s0, t3, gp
                  c.srli     a4, 9
                  mul        tp, s2, t5
                  slt        a0, s5, s11
                  mul        tp, s2, t5
                  div        s7, gp, a4
                  c.sub      s0, s1
                  c.add      t3, t1
                  remu       s6, s3, t1
                  nop
                  srai       a4, a3, 0
                  c.add      t3, t1
                  c.addi16sp sp, -16
                  c.sub      s0, s1
                  srl        t1, tp, zero
                  mulhsu     tp, t5, a6
                  lui        s3, 985951
                  add        s4, a7, s6
                  c.addi4spn a2, sp, 528
                  add        s4, a7, s6
                  sltiu      s3, tp, 300
                  xori       t3, t1, -721
                  sltiu      s3, tp, 300
                  divu       tp, s5, t4
                  and        s6, t2, a4
                  c.li       s11, -1
                  mul        tp, s2, t5
                  c.xor      a4, a5
                  sltu       s3, a6, a4
                  addi       gp, s8, -298
                  c.or       a0, a2
                  c.addi     s9, -1
                  mul        tp, s2, t5
                  slti       tp, a1, -167
                  xori       t3, t1, -721
                  ori        tp, a0, -848
                  c.sub      s0, s1
                  srai       a4, a3, 0
                  ori        tp, a0, -848
                  ori        tp, a0, -848
                  c.sub      s0, s1
                  lui        s3, 985951
                  c.li       s11, -1
                  c.mv       a2, a0
                  c.addi4spn a2, sp, 528
                  or         a4, a4, zero
                  nop
                  div        s7, gp, a4
                  mulhsu     tp, t5, a6
                  xor        s11, zero, s7
                  rem        a2, s2, s9
                  c.and      a4, s1
                  c.andi     s1, 31
                  c.addi     s9, -1
                  sra        s9, s4, t5
                  c.mv       a2, a0
                  xor        s11, zero, s7
                  c.slli     t5, 22
                  srai       a4, a3, 0
                  c.srai     s1, 28
                  div        s7, gp, a4
                  c.srli     a4, 9
                  rem        a2, s2, s9
                  c.mv       a2, a0
                  c.srli     a4, 9
                  c.nop
                  c.lui      a6, 24
                  mulhsu     tp, t5, a6
                  lui        s3, 985951
                  c.nop
                  mulhu      s4, a6, t3
                  ori        tp, a0, -848
                  auipc      s1, 11691
                  mulhu      s4, a6, t3
                  add        s4, a7, s6
                  c.andi     s1, 31
                  c.addi4spn a2, sp, 528
                  c.addi4spn a2, sp, 528
                  c.andi     s1, 31
                  srli       zero, a0, 13
                  sll        s8, s0, s6
                  slti       tp, a1, -167
                  sltu       s3, a6, a4
                  c.add      t3, t1
                  xori       t3, t1, -721
                  add        s4, a7, s6
                  c.addi16sp sp, -16
                  xori       t3, t1, -721
                  c.lui      a6, 24
                  nop
                  rem        a2, s2, s9
                  sltu       s3, a6, a4
                  rem        a2, s2, s9
                  rem        a2, s2, s9
                  c.slli     t5, 22
                  c.mv       a2, a0
                  c.mv       a2, a0
                  slt        a0, s5, s11
                  slti       tp, a1, -167
                  srli       zero, a0, 13
                  lui        s3, 985951
                  auipc      s1, 11691
                  divu       tp, s5, t4
                  srli       zero, a0, 13
                  mul        tp, s2, t5
                  c.srli     a4, 9
                  andi       t0, a3, 147
                  c.slli     t5, 22
                  srl        t1, tp, zero
                  mulhu      s4, a6, t3
                  slt        a0, s5, s11
                  andi       t0, a3, 147
                  c.or       a0, a2
                  c.addi16sp sp, -16
                  add        s4, a7, s6
                  nop
                  divu       tp, s5, t4
                  addi       gp, s8, -298
                  nop
                  srli       zero, a0, 13
                  srai       a4, a3, 0
                  nop
                  c.nop
                  c.srli     a4, 9
                  mulh       s1, t4, s11
                  xori       t3, t1, -721
                  sll        s8, s0, s6
                  c.and      a4, s1
                  nop
                  c.xor      a4, a5
                  c.xor      a4, a5
                  lui        s3, 985951
                  sltu       s3, a6, a4
                  and        s6, t2, a4
                  add        s4, a7, s6
                  and        s6, t2, a4
                  c.sub      s0, s1
                  mul        tp, s2, t5
                  srai       a4, a3, 0
                  slt        a0, s5, s11
                  c.andi     s1, 31
                  c.add      t3, t1
                  slt        a0, s5, s11
                  divu       tp, s5, t4
                  c.xor      a4, a5
                  c.mv       a2, a0
                  div        s7, gp, a4
                  c.xor      a4, a5
                  c.add      t3, t1
                  slt        a0, s5, s11
                  c.andi     s1, 31
                  div        s7, gp, a4
                  div        s7, gp, a4
                  xor        s11, zero, s7
                  c.srai     s1, 28
                  nop
                  addi       gp, s8, -298
                  sra        s9, s4, t5
                  c.addi     s9, -1
                  addi       gp, s8, -298
                  c.xor      a4, a5
                  c.add      t3, t1
                  sltiu      s3, tp, 300
                  srl        t1, tp, zero
                  ori        tp, a0, -848
                  c.srli     a4, 9
                  slli       a2, a4, 25
                  sll        s8, s0, s6
                  add        s4, a7, s6
                  c.addi16sp sp, -16
                  srli       zero, a0, 13
                  srai       a4, a3, 0
                  add        s4, a7, s6
                  srl        t1, tp, zero
                  andi       t0, a3, 147
                  c.srli     a4, 9
                  c.nop
                  sltiu      s3, tp, 300
                  c.srli     a4, 9
                  slli       a2, a4, 25
                  lui        s3, 985951
                  xor        s11, zero, s7
                  mulh       s1, t4, s11
                  divu       tp, s5, t4
                  mul        tp, s2, t5
                  c.andi     s1, 31
                  srli       zero, a0, 13
                  c.nop
                  xor        s11, zero, s7
                  rem        a2, s2, s9
                  c.addi     s9, -1
                  c.add      t3, t1
                  srli       zero, a0, 13
                  nop
                  xori       t3, t1, -721
                  c.xor      a4, a5
                  c.slli     t5, 22
                  c.andi     s1, 31
                  slli       a2, a4, 25
                  srl        t1, tp, zero
                  sltiu      s3, tp, 300
                  slti       tp, a1, -167
                  mulhsu     tp, t5, a6
                  c.slli     t5, 22
                  or         a4, a4, zero
                  slti       tp, a1, -167
                  srai       a4, a3, 0
                  add        s4, a7, s6
                  c.addi16sp sp, -16
                  slti       tp, a1, -167
                  c.lui      a6, 24
                  mulhsu     tp, t5, a6
                  c.xor      a4, a5
                  slt        a0, s5, s11
                  auipc      s1, 11691
                  nop
                  ori        tp, a0, -848
                  sub        s0, t3, gp
                  and        s6, t2, a4
                  xori       t3, t1, -721
                  slli       a2, a4, 25
                  c.lui      a6, 24
                  srli       zero, a0, 13
                  srl        t1, tp, zero
                  c.addi     s9, -1
                  sltu       s3, a6, a4
                  div        s7, gp, a4
                  c.sub      s0, s1
                  slli       a2, a4, 25
                  srai       a4, a3, 0
                  or         a4, a4, zero
                  c.li       s11, -1
                  mulhu      s4, a6, t3
                  srl        t1, tp, zero
                  lui        s3, 985951
                  divu       tp, s5, t4
                  auipc      s1, 11691
                  c.nop
                  add        s4, a7, s6
                  srli       zero, a0, 13
                  div        s7, gp, a4
                  c.slli     t5, 22
                  srli       zero, a0, 13
                  mulhu      s4, a6, t3
                  c.srli     a4, 9
                  c.sub      s0, s1
                  andi       t0, a3, 147
                  divu       tp, s5, t4
                  mul        tp, s2, t5
                  mul        tp, s2, t5
                  slti       tp, a1, -167
                  srli       zero, a0, 13
                  sra        s9, s4, t5
                  c.mv       a2, a0
                  c.sub      s0, s1
                  sub        s0, t3, gp
                  xor        s11, zero, s7
                  or         a4, a4, zero
                  auipc      s1, 11691
                  c.srli     a4, 9
                  divu       tp, s5, t4
                  c.sub      s0, s1
                  rem        a2, s2, s9
                  slli       a2, a4, 25
                  c.sub      s0, s1
                  c.addi     s9, -1
                  nop
                  sltiu      s3, tp, 300
                  c.xor      a4, a5
                  c.andi     s1, 31
                  rem        a2, s2, s9
                  c.lui      a6, 24
                  and        s6, t2, a4
                  slli       a2, a4, 25
                  c.lui      a6, 24
                  add        s4, a7, s6
                  c.slli     t5, 22
                  mulhu      s4, a6, t3
                  mulhu      s4, a6, t3
                  sll        s8, s0, s6
                  srai       a4, a3, 0
                  srl        t1, tp, zero
                  c.mv       a2, a0
                  srai       a4, a3, 0
                  c.add      t3, t1
                  c.mv       a2, a0
                  srai       a4, a3, 0
                  c.mv       a2, a0
                  ori        tp, a0, -848
                  sll        s8, s0, s6
                  sltiu      s3, tp, 300
                  addi       gp, s8, -298
                  rem        a2, s2, s9
                  addi       gp, s8, -298
                  nop
                  add        s4, a7, s6
                  c.srli     a4, 9
                  c.andi     s1, 31
                  c.slli     t5, 22
                  c.srli     a4, 9
                  ori        tp, a0, -848
                  andi       t0, a3, 147
                  divu       tp, s5, t4
                  addi       gp, s8, -298
                  c.addi4spn a2, sp, 528
                  c.mv       a2, a0
                  xor        s11, zero, s7
                  nop
                  xori       t3, t1, -721
                  or         a4, a4, zero
                  c.xor      a4, a5
                  ori        tp, a0, -848
                  srl        t1, tp, zero
                  mulhsu     tp, t5, a6
                  xori       t3, t1, -721
                  c.mv       a2, a0
                  addi       gp, s8, -298
                  sll        s8, s0, s6
                  and        s6, t2, a4
                  slti       tp, a1, -167
                  c.add      t3, t1
                  c.addi4spn a2, sp, 528
                  slli       a2, a4, 25
                  c.sub      s0, s1
                  and        s6, t2, a4
                  c.andi     s1, 31
                  slti       tp, a1, -167
                  c.lui      a6, 24
                  c.srli     a4, 9
                  sltu       s3, a6, a4
                  c.xor      a4, a5
                  xor        s11, zero, s7
                  sltiu      s3, tp, 300
                  add        s4, a7, s6
                  c.xor      a4, a5
                  slti       tp, a1, -167
                  mulhsu     tp, t5, a6
                  c.slli     t5, 22
                  c.sub      s0, s1
                  c.srai     s1, 28
                  c.xor      a4, a5
                  c.lui      a6, 24
                  c.and      a4, s1
                  srl        t1, tp, zero
                  c.add      t3, t1
                  c.and      a4, s1
                  c.sub      s0, s1
                  div        s7, gp, a4
                  c.nop
                  ori        tp, a0, -848
                  xori       t3, t1, -721
                  c.addi4spn a2, sp, 528
                  ori        tp, a0, -848
                  add        s4, a7, s6
                  c.addi     s9, -1
                  c.srli     a4, 9
                  mul        tp, s2, t5
                  and        s6, t2, a4
                  sll        s8, s0, s6
                  andi       t0, a3, 147
                  divu       tp, s5, t4
                  c.and      a4, s1
                  auipc      s1, 11691
                  c.srli     a4, 9
                  mulhsu     tp, t5, a6
                  rem        a2, s2, s9
                  c.addi     s9, -1
                  mul        tp, s2, t5
                  and        s6, t2, a4
                  lui        s3, 985951
                  addi       gp, s8, -298
                  nop
                  xori       t3, t1, -721
                  slli       a2, a4, 25
                  c.addi16sp sp, -16
                  sltu       s3, a6, a4
                  xori       t3, t1, -721
                  andi       t0, a3, 147
                  c.add      t3, t1
                  mulhu      s4, a6, t3
                  c.addi16sp sp, -16
                  remu       s6, s3, t1
                  or         a4, a4, zero
                  mulhsu     tp, t5, a6
                  addi       gp, s8, -298
                  c.mv       a2, a0
                  slt        a0, s5, s11
                  c.li       s11, -1
                  c.srai     s1, 28
                  srli       zero, a0, 13
                  c.andi     s1, 31
                  ori        tp, a0, -848
                  c.srli     a4, 9
                  and        s6, t2, a4
                  mulh       s1, t4, s11
                  mulhu      s4, a6, t3
                  nop
                  c.add      t3, t1
                  rem        a2, s2, s9
                  srli       zero, a0, 13
                  srli       zero, a0, 13
                  auipc      s1, 11691
                  mulhsu     tp, t5, a6
                  srl        t1, tp, zero
                  auipc      s1, 11691
                  mul        tp, s2, t5
                  c.sub      s0, s1
                  c.xor      a4, a5
                  c.andi     s1, 31
                  c.xor      a4, a5
                  ori        tp, a0, -848
                  c.sub      s0, s1
                  div        s7, gp, a4
                  c.addi16sp sp, -16
                  srl        t1, tp, zero
                  c.lui      a6, 24
                  remu       s6, s3, t1
                  c.slli     t5, 22
                  c.add      t3, t1
                  li         s10, 0x80000000 #start riscv_int_numeric_corner_stream_16
                  li         s7, 0x0
                  li         t3, 0x0
                  li         s4, 0x80000000
                  li         a0, 0x0
                  li         a6, 0xffffffff
                  li         s8, 0x80000000
                  li         a2, 0x24121a76
                  li         ra, 0xffffffff
                  li         tp, 0xffffffff
                  divu       a0, s10, s8
                  div        s8, s8, ra
                  mulhsu     t3, t3, ra
                  addi       ra, s10, -40
                  rem        a6, a2, a0
                  nop
                  add        s4, tp, s10
                  rem        a6, a2, a0
                  nop
                  addi       ra, s10, -40
                  sub        s10, a0, s8
                  add        s4, tp, s10
                  sub        s10, a0, s8
                  mul        tp, s4, t3
                  nop
                  remu       tp, s4, a2
                  mul        tp, s4, t3
                  mul        tp, s4, t3
                  divu       a0, s10, s8
                  remu       tp, s4, a2
                  auipc      a2, 11691
                  sub        s10, a0, s8
                  mulhu      ra, a2, t3
                  addi       ra, s10, -40
                  lui        s7, 985951
                  mulhu      ra, a2, t3
                  rem        a6, a2, a0
                  mulh       t3, s7, tp
                  mulhu      ra, a2, t3 #end riscv_int_numeric_corner_stream_16
                  nop
                  c.mv       a2, a0
                  remu       s6, s3, t1
                  slti       tp, a1, -167
                  addi       gp, s8, -298
                  sltiu      s3, tp, 300
                  sub        s0, t3, gp
                  slti       tp, a1, -167
                  addi       gp, s8, -298
                  sltiu      s3, tp, 300
                  c.xor      a4, a5
                  c.lui      a6, 24
                  mulhsu     tp, t5, a6
                  auipc      s1, 11691
                  remu       s6, s3, t1
                  c.mv       a2, a0
                  auipc      s1, 11691
                  mulhsu     tp, t5, a6
                  c.mv       a2, a0
                  srl        t1, tp, zero
                  and        s6, t2, a4
                  lui        s3, 985951
                  srli       zero, a0, 13
                  remu       s6, s3, t1
                  c.addi16sp sp, -16
                  remu       s6, s3, t1
                  nop
                  mul        tp, s2, t5
                  mulh       s1, t4, s11
                  sub        s0, t3, gp
                  slt        a0, s5, s11
                  addi       gp, s8, -298
                  and        s6, t2, a4
                  addi       gp, s8, -298
                  xori       t3, t1, -721
                  slti       tp, a1, -167
                  mulhu      s4, a6, t3
                  sub        s0, t3, gp
                  div        s7, gp, a4
                  c.lui      a6, 24
                  add        s4, a7, s6
                  slli       a2, a4, 25
                  sltu       s3, a6, a4
                  c.srai     s1, 28
                  c.addi4spn a2, sp, 528
                  mul        tp, s2, t5
                  srl        t1, tp, zero
                  sltiu      s3, tp, 300
                  srli       zero, a0, 13
                  addi       gp, s8, -298
                  mulh       s1, t4, s11
                  and        s6, t2, a4
                  ori        tp, a0, -848
                  div        s7, gp, a4
                  and        s6, t2, a4
                  srl        t1, tp, zero
                  xori       t3, t1, -721
                  c.slli     t5, 22
                  slti       tp, a1, -167
                  c.srli     a4, 9
                  c.nop
                  c.or       a0, a2
                  sra        s9, s4, t5
                  addi       gp, s8, -298
                  div        s7, gp, a4
                  slti       tp, a1, -167
                  sra        s9, s4, t5
                  c.xor      a4, a5
                  mul        tp, s2, t5
                  c.srai     s1, 28
                  c.andi     s1, 31
                  andi       t0, a3, 147
                  xor        s11, zero, s7
                  c.srai     s1, 28
                  nop
                  or         a4, a4, zero
                  sll        s8, s0, s6
                  mulh       s1, t4, s11
                  sub        s0, t3, gp
                  mul        tp, s2, t5
                  c.nop
                  remu       s6, s3, t1
                  sub        s0, t3, gp
                  or         a4, a4, zero
                  c.li       s11, -1
                  c.lui      a6, 24
                  c.and      a4, s1
                  sll        s8, s0, s6
                  sll        s8, s0, s6
                  or         a4, a4, zero
                  lui        s3, 985951
                  auipc      s1, 11691
                  slli       a2, a4, 25
                  andi       t0, a3, 147
                  c.addi16sp sp, -16
                  div        s7, gp, a4
                  div        s7, gp, a4
                  srl        t1, tp, zero
                  sra        s9, s4, t5
                  srl        t1, tp, zero
                  c.andi     s1, 31
                  sltu       s3, a6, a4
                  xor        s11, zero, s7
                  c.addi     s9, -1
                  nop
                  div        s7, gp, a4
                  sltu       s3, a6, a4
                  add        s4, a7, s6
                  srai       a4, a3, 0
                  addi       gp, s8, -298
                  c.xor      a4, a5
                  c.add      t3, t1
                  c.lui      a6, 24
                  andi       t0, a3, 147
                  andi       t0, a3, 147
                  xor        s11, zero, s7
                  c.sub      s0, s1
                  remu       s6, s3, t1
                  divu       tp, s5, t4
                  andi       t0, a3, 147
                  srai       a4, a3, 0
                  mulhsu     tp, t5, a6
                  c.xor      a4, a5
                  c.mv       a2, a0
                  auipc      s1, 11691
                  slli       a2, a4, 25
                  c.add      t3, t1
                  srl        t1, tp, zero
                  xori       t3, t1, -721
                  c.li       s11, -1
                  slti       tp, a1, -167
                  c.lui      a6, 24
                  c.srai     s1, 28
                  c.li       s11, -1
                  c.mv       a2, a0
                  remu       s6, s3, t1
                  srl        t1, tp, zero
                  c.li       s11, -1
                  c.addi4spn a2, sp, 528
                  xori       t3, t1, -721
                  c.addi4spn a2, sp, 528
                  slli       a2, a4, 25
                  c.lui      a6, 24
                  c.andi     s1, 31
                  sltiu      s3, tp, 300
                  c.and      a4, s1
                  c.xor      a4, a5
                  sra        s9, s4, t5
                  srli       zero, a0, 13
                  ori        tp, a0, -848
                  sub        s0, t3, gp
                  divu       tp, s5, t4
                  c.xor      a4, a5
                  auipc      s1, 11691
                  or         a4, a4, zero
                  srli       zero, a0, 13
                  c.addi4spn a2, sp, 528
                  c.srai     s1, 28
                  c.or       a0, a2
                  c.andi     s1, 31
                  sra        s9, s4, t5
                  sll        s8, s0, s6
                  c.mv       a2, a0
                  slti       tp, a1, -167
                  srli       zero, a0, 13
                  c.or       a0, a2
                  sltiu      s3, tp, 300
                  slt        a0, s5, s11
                  rem        a2, s2, s9
                  c.and      a4, s1
                  slt        a0, s5, s11
                  sltu       s3, a6, a4
                  c.li       s11, -1
                  sra        s9, s4, t5
                  c.nop
                  andi       t0, a3, 147
                  c.slli     t5, 22
                  sltu       s3, a6, a4
                  mulhu      s4, a6, t3
                  and        s6, t2, a4
                  sltu       s3, a6, a4
                  mulhu      s4, a6, t3
                  nop
                  mul        tp, s2, t5
                  c.andi     s1, 31
                  c.addi4spn a2, sp, 528
                  c.srai     s1, 28
                  divu       tp, s5, t4
                  c.addi4spn a2, sp, 528
                  srai       a4, a3, 0
                  c.slli     t5, 22
                  c.lui      a6, 24
                  c.addi16sp sp, -16
                  c.srli     a4, 9
                  sra        s9, s4, t5
                  slli       a2, a4, 25
                  sll        s8, s0, s6
                  c.slli     t5, 22
                  c.lui      a6, 24
                  auipc      s1, 11691
                  ori        tp, a0, -848
                  srl        t1, tp, zero
                  rem        a2, s2, s9
                  c.li       s11, -1
                  c.sub      s0, s1
                  mulh       s1, t4, s11
                  slti       tp, a1, -167
                  nop
                  c.andi     s1, 31
                  c.sub      s0, s1
                  xor        s11, zero, s7
                  c.srai     s1, 28
                  c.srai     s1, 28
                  srai       a4, a3, 0
                  sll        s8, s0, s6
                  c.addi4spn a2, sp, 528
                  srl        t1, tp, zero
                  c.addi4spn a2, sp, 528
                  slti       tp, a1, -167
                  c.addi16sp sp, -16
                  slti       tp, a1, -167
                  sll        s8, s0, s6
                  c.andi     s1, 31
                  sra        s9, s4, t5
                  nop
                  add        s4, a7, s6
                  c.lui      a6, 24
                  remu       s6, s3, t1
                  c.lui      a6, 24
                  c.and      a4, s1
                  rem        a2, s2, s9
                  c.srai     s1, 28
                  div        s7, gp, a4
                  sll        s8, s0, s6
                  div        s7, gp, a4
                  nop
                  xori       t3, t1, -721
                  sltiu      s3, tp, 300
                  c.lui      a6, 24
                  slli       a2, a4, 25
                  xori       t3, t1, -721
                  addi       gp, s8, -298
                  div        s7, gp, a4
                  andi       t0, a3, 147
                  mul        tp, s2, t5
                  xori       t3, t1, -721
                  c.addi     s9, -1
                  srai       a4, a3, 0
                  c.addi     s9, -1
                  auipc      s1, 11691
                  mul        tp, s2, t5
                  and        s6, t2, a4
                  c.xor      a4, a5
                  srli       zero, a0, 13
                  slti       tp, a1, -167
                  addi       gp, s8, -298
                  srl        t1, tp, zero
                  div        s7, gp, a4
                  ori        tp, a0, -848
                  xor        s11, zero, s7
                  c.and      a4, s1
                  rem        a2, s2, s9
                  c.li       s11, -1
                  sub        s0, t3, gp
                  c.mv       a2, a0
                  srl        t1, tp, zero
                  c.addi     s9, -1
                  c.sub      s0, s1
                  and        s6, t2, a4
                  slt        a0, s5, s11
                  c.srli     a4, 9
                  sub        s0, t3, gp
                  c.andi     s1, 31
                  sll        s8, s0, s6
                  sltiu      s3, tp, 300
                  add        s4, a7, s6
                  sltu       s3, a6, a4
                  nop
                  srli       zero, a0, 13
                  c.lui      a6, 24
                  rem        a2, s2, s9
                  c.andi     s1, 31
                  srl        t1, tp, zero
                  c.or       a0, a2
                  xori       t3, t1, -721
                  c.lui      a6, 24
                  xor        s11, zero, s7
                  divu       tp, s5, t4
                  c.addi4spn a2, sp, 528
                  sra        s9, s4, t5
                  mulh       s1, t4, s11
                  c.andi     s1, 31
                  mulh       s1, t4, s11
                  sltu       s3, a6, a4
                  c.addi4spn a2, sp, 528
                  and        s6, t2, a4
                  c.addi16sp sp, -16
                  slli       a2, a4, 25
                  mul        tp, s2, t5
                  addi       gp, s8, -298
                  c.srai     s1, 28
                  ori        tp, a0, -848
                  nop
                  c.and      a4, s1
                  c.nop
                  c.srli     a4, 9
                  divu       tp, s5, t4
                  c.nop
                  slt        a0, s5, s11
                  slli       a2, a4, 25
                  nop
                  ori        tp, a0, -848
                  sra        s9, s4, t5
                  remu       s6, s3, t1
                  addi       gp, s8, -298
                  sll        s8, s0, s6
                  sll        s8, s0, s6
                  slli       a2, a4, 25
                  nop
                  c.sub      s0, s1
                  c.slli     t5, 22
                  xor        s11, zero, s7
                  c.srai     s1, 28
                  or         a4, a4, zero
                  c.li       s11, -1
                  c.lui      a6, 24
                  c.or       a0, a2
                  sltiu      s3, tp, 300
                  or         a4, a4, zero
                  srli       zero, a0, 13
                  sll        s8, s0, s6
                  mulh       s1, t4, s11
                  sub        s0, t3, gp
                  slt        a0, s5, s11
                  c.addi16sp sp, -16
                  c.addi16sp sp, -16
                  c.addi     s9, -1
                  nop
                  c.sub      s0, s1
                  c.addi16sp sp, -16
                  slli       a2, a4, 25
                  mulhu      s4, a6, t3
                  ori        tp, a0, -848
                  auipc      s1, 11691
                  c.addi4spn a2, sp, 528
                  c.srai     s1, 28
                  c.nop
                  div        s7, gp, a4
                  sra        s9, s4, t5
                  xor        s11, zero, s7
                  sub        s0, t3, gp
                  add        s4, a7, s6
                  c.li       s11, -1
                  add        s4, a7, s6
                  sra        s9, s4, t5
                  c.andi     s1, 31
                  sub        s0, t3, gp
                  c.add      t3, t1
                  c.lui      a6, 24
                  xor        s11, zero, s7
                  ori        tp, a0, -848
                  mulhu      s4, a6, t3
                  c.mv       a2, a0
                  c.lui      a6, 24
                  c.add      t3, t1
                  sltiu      s3, tp, 300
                  c.srli     a4, 9
                  div        s7, gp, a4
                  c.mv       a2, a0
                  c.srli     a4, 9
                  nop
                  c.add      t3, t1
                  sltu       s3, a6, a4
                  c.sub      s0, s1
                  c.slli     t5, 22
                  c.and      a4, s1
                  rem        a2, s2, s9
                  slli       a2, a4, 25
                  divu       tp, s5, t4
                  c.nop
                  lui        s3, 985951
                  andi       t0, a3, 147
                  div        s7, gp, a4
                  lui        s3, 985951
                  c.addi4spn a2, sp, 528
                  addi       gp, s8, -298
                  sltu       s3, a6, a4
                  srli       zero, a0, 13
                  xor        s11, zero, s7
                  mulhsu     tp, t5, a6
                  c.srli     a4, 9
                  c.slli     t5, 22
                  sltu       s3, a6, a4
                  add        s4, a7, s6
                  c.mv       a2, a0
                  c.addi     s9, -1
                  mul        tp, s2, t5
                  c.addi4spn a2, sp, 528
                  ori        tp, a0, -848
                  lui        s3, 985951
                  c.srai     s1, 28
                  auipc      s1, 11691
                  c.addi     s9, -1
                  slli       a2, a4, 25
                  nop
                  div        s7, gp, a4
                  auipc      s1, 11691
                  c.sub      s0, s1
                  c.sub      s0, s1
                  srli       zero, a0, 13
                  c.li       s11, -1
                  c.li       s11, -1
                  add        s4, a7, s6
                  nop
                  addi       gp, s8, -298
                  lui        s3, 985951
                  c.mv       a2, a0
                  c.mv       a2, a0
                  ori        tp, a0, -848
                  sll        s8, s0, s6
                  c.slli     t5, 22
                  c.srai     s1, 28
                  c.addi16sp sp, -16
                  and        s6, t2, a4
                  c.slli     t5, 22
                  c.slli     t5, 22
                  mulh       s1, t4, s11
                  xor        s11, zero, s7
                  c.lui      a6, 24
                  c.slli     t5, 22
                  remu       s6, s3, t1
                  add        s4, a7, s6
                  div        s7, gp, a4
                  sltiu      s3, tp, 300
                  c.lui      a6, 24
                  c.or       a0, a2
                  c.nop
                  rem        a2, s2, s9
                  c.srli     a4, 9
                  sltiu      s3, tp, 300
                  slli       a2, a4, 25
                  auipc      s1, 11691
                  c.sub      s0, s1
                  c.addi16sp sp, -16
                  or         a4, a4, zero
                  xor        s11, zero, s7
                  c.li       s11, -1
                  c.li       s11, -1
                  and        s6, t2, a4
                  c.li       s11, -1
                  mulhu      s4, a6, t3
                  c.addi16sp sp, -16
                  c.srli     a4, 9
                  mulhsu     tp, t5, a6
                  srai       a4, a3, 0
                  xor        s11, zero, s7
                  auipc      s1, 11691
                  sltiu      s3, tp, 300
                  add        s4, a7, s6
                  add        s4, a7, s6
                  c.srai     s1, 28
                  c.srai     s1, 28
                  nop
                  c.addi     s9, -1
                  mulhsu     tp, t5, a6
                  slli       a2, a4, 25
                  c.add      t3, t1
                  rem        a2, s2, s9
                  srai       a4, a3, 0
                  c.addi4spn a2, sp, 528
                  c.slli     t5, 22
                  rem        a2, s2, s9
                  c.xor      a4, a5
                  c.addi4spn a2, sp, 528
                  or         a4, a4, zero
                  slti       tp, a1, -167
                  addi       gp, s8, -298
                  rem        a2, s2, s9
                  c.srli     a4, 9
                  c.or       a0, a2
                  c.addi16sp sp, -16
                  srai       a4, a3, 0
                  c.addi16sp sp, -16
                  mul        tp, s2, t5
                  srai       a4, a3, 0
                  divu       tp, s5, t4
                  lui        s3, 985951
                  c.srli     a4, 9
                  remu       s6, s3, t1
                  xor        s11, zero, s7
                  sll        s8, s0, s6
                  c.slli     t5, 22
                  sll        s8, s0, s6
                  c.li       s11, -1
                  c.addi     s9, -1
                  srl        t1, tp, zero
                  lui        s3, 985951
                  c.mv       a2, a0
                  srl        t1, tp, zero
                  mulh       s1, t4, s11
                  srli       zero, a0, 13
                  c.lui      a6, 24
                  mulh       s1, t4, s11
                  c.srli     a4, 9
                  sltiu      s3, tp, 300
                  xori       t3, t1, -721
                  slti       tp, a1, -167
                  c.srai     s1, 28
                  sltu       s3, a6, a4
                  remu       s6, s3, t1
                  c.andi     s1, 31
                  c.addi     s9, -1
                  mulhsu     tp, t5, a6
                  c.mv       a2, a0
                  addi       gp, s8, -298
                  c.srai     s1, 28
                  andi       t0, a3, 147
                  srli       zero, a0, 13
                  srl        t1, tp, zero
                  mulhsu     tp, t5, a6
                  mulh       s1, t4, s11
                  c.xor      a4, a5
                  c.slli     t5, 22
                  addi       gp, s8, -298
                  div        s7, gp, a4
                  c.srli     a4, 9
                  c.slli     t5, 22
                  c.li       s11, -1
                  c.and      a4, s1
                  mul        tp, s2, t5
                  c.addi16sp sp, -16
                  c.and      a4, s1
                  c.lui      a6, 24
                  c.addi16sp sp, -16
                  srl        t1, tp, zero
                  slti       tp, a1, -167
                  ori        tp, a0, -848
                  sltu       s3, a6, a4
                  c.srai     s1, 28
                  sltiu      s3, tp, 300
                  c.slli     t5, 22
                  slti       tp, a1, -167
                  and        s6, t2, a4
                  auipc      s1, 11691
                  div        s7, gp, a4
                  c.sub      s0, s1
                  c.li       s11, -1
                  divu       tp, s5, t4
                  c.addi4spn a2, sp, 528
                  or         a4, a4, zero
                  mulhsu     tp, t5, a6
                  sltiu      s3, tp, 300
                  c.lui      a6, 24
                  auipc      s1, 11691
                  div        s7, gp, a4
                  c.lui      a6, 24
                  sll        s8, s0, s6
                  div        s7, gp, a4
                  c.nop
                  add        s4, a7, s6
                  mulhu      s4, a6, t3
                  mul        tp, s2, t5
                  div        s7, gp, a4
                  c.slli     t5, 22
                  nop
                  addi       gp, s8, -298
                  andi       t0, a3, 147
                  slli       a2, a4, 25
                  slli       a2, a4, 25
                  c.xor      a4, a5
                  c.and      a4, s1
                  div        s7, gp, a4
                  srli       zero, a0, 13
                  c.or       a0, a2
                  add        s4, a7, s6
                  c.srai     s1, 28
                  c.and      a4, s1
                  slt        a0, s5, s11
                  nop
                  srli       zero, a0, 13
                  addi       gp, s8, -298
                  sra        s9, s4, t5
                  c.sub      s0, s1
                  slti       tp, a1, -167
                  sltiu      s3, tp, 300
                  c.addi     s9, -1
                  auipc      s1, 11691
                  sltu       s3, a6, a4
                  slti       tp, a1, -167
                  c.slli     t5, 22
                  c.and      a4, s1
                  c.addi     s9, -1
                  c.addi     s9, -1
                  sltu       s3, a6, a4
                  sub        s0, t3, gp
                  slti       tp, a1, -167
                  remu       s6, s3, t1
                  slti       tp, a1, -167
                  c.addi16sp sp, -16
                  srli       zero, a0, 13
                  andi       t0, a3, 147
                  remu       s6, s3, t1
                  mulh       s1, t4, s11
                  xori       t3, t1, -721
                  srli       zero, a0, 13
                  c.addi     s9, -1
                  add        s4, a7, s6
                  srai       a4, a3, 0
                  auipc      s1, 11691
                  srl        t1, tp, zero
                  c.nop
                  c.and      a4, s1
                  c.and      a4, s1
                  c.slli     t5, 22
                  c.add      t3, t1
                  sra        s9, s4, t5
                  or         a4, a4, zero
                  mulhsu     tp, t5, a6
                  c.addi16sp sp, -16
                  remu       s6, s3, t1
                  c.addi4spn a2, sp, 528
                  mul        tp, s2, t5
                  srli       zero, a0, 13
                  andi       t0, a3, 147
                  mul        tp, s2, t5
                  c.add      t3, t1
                  xor        s11, zero, s7
                  add        s4, a7, s6
                  divu       tp, s5, t4
                  slti       tp, a1, -167
                  and        s6, t2, a4
                  sltiu      s3, tp, 300
                  sra        s9, s4, t5
                  div        s7, gp, a4
                  c.or       a0, a2
                  sltu       s3, a6, a4
                  nop
                  mulhu      s4, a6, t3
                  sll        s8, s0, s6
                  sll        s8, s0, s6
                  c.li       s11, -1
                  lui        s3, 985951
                  xor        s11, zero, s7
                  c.addi     s9, -1
                  c.li       s11, -1
                  sll        s8, s0, s6
                  mulh       s1, t4, s11
                  xor        s11, zero, s7
                  srai       a4, a3, 0
                  rem        a2, s2, s9
                  slt        a0, s5, s11
                  srl        t1, tp, zero
                  lui        s3, 985951
                  lui        s3, 985951
                  srai       a4, a3, 0
                  div        s7, gp, a4
                  slt        a0, s5, s11
                  c.nop
                  auipc      s1, 11691
                  c.slli     t5, 22
                  srli       zero, a0, 13
                  c.nop
                  sltu       s3, a6, a4
                  xori       t3, t1, -721
                  sll        s8, s0, s6
                  c.srai     s1, 28
                  c.addi4spn a2, sp, 528
                  sub        s0, t3, gp
                  or         a4, a4, zero
                  c.addi4spn a2, sp, 528
                  mulhu      s4, a6, t3
                  mul        tp, s2, t5
                  lui        s3, 985951
                  mulhu      s4, a6, t3
                  nop
                  add        s4, a7, s6
                  div        s7, gp, a4
                  sub        s0, t3, gp
                  srl        t1, tp, zero
                  andi       t0, a3, 147
                  c.sub      s0, s1
                  lui        s3, 985951
                  xori       t3, t1, -721
                  auipc      s1, 11691
                  srai       a4, a3, 0
                  li         a0, 0x0 #start riscv_int_numeric_corner_stream_23
                  li         tp, 0x2182c967
                  li         t1, 0x0
                  li         s7, 0xffffffff
                  li         sp, 0x78213fcb
                  li         a7, 0x80000000
                  li         s4, 0x90f3ffac
                  li         a2, 0xffffffff
                  li         s1, 0x80000000
                  li         s9, 0x9d674d41
                  addi       tp, s7, -40
                  lui        s7, 985951
                  mulh       s4, s9, tp
                  divu       a2, a0, a7
                  mulhsu     t1, a2, a7
                  divu       a2, a0, a7
                  nop
                  mulhu      a7, s1, s7
                  add        sp, tp, t1
                  sub        s9, s1, s9
                  auipc      s1, 11691
                  nop
                  lui        s7, 985951
                  mulhu      a7, s1, s7
                  lui        s7, 985951
                  auipc      s1, 11691
                  add        sp, tp, t1
                  lui        s7, 985951
                  nop
                  sub        s9, s1, s9
                  lui        s7, 985951
                  divu       a2, a0, a7
                  mulh       s4, s9, tp
                  mul        a2, s4, a0
                  add        sp, tp, t1
                  mulhu      a7, s1, s7
                  mulh       s4, s9, tp
                  mulhu      a7, s1, s7 #end riscv_int_numeric_corner_stream_23
                  xor        s11, zero, s7
                  c.lui      a6, 24
                  srl        t1, tp, zero
                  c.sub      s0, s1
                  c.li       s11, -1
                  remu       s6, s3, t1
                  slt        a0, s5, s11
                  mul        tp, s2, t5
                  divu       tp, s5, t4
                  sll        s8, s0, s6
                  xor        s11, zero, s7
                  slli       a2, a4, 25
                  c.srai     s1, 28
                  c.xor      a4, a5
                  auipc      s1, 11691
                  c.nop
                  sltiu      s3, tp, 300
                  c.lui      a6, 24
                  divu       tp, s5, t4
                  nop
                  ori        tp, a0, -848
                  c.add      t3, t1
                  slt        a0, s5, s11
                  c.add      t3, t1
                  sltiu      s3, tp, 300
                  remu       s6, s3, t1
                  c.nop
                  mulh       s1, t4, s11
                  sltu       s3, a6, a4
                  ori        tp, a0, -848
                  mul        tp, s2, t5
                  mulhu      s4, a6, t3
                  srli       zero, a0, 13
                  c.sub      s0, s1
                  mulhu      s4, a6, t3
                  sltu       s3, a6, a4
                  or         a4, a4, zero
                  c.nop
                  c.srli     a4, 9
                  nop
                  c.or       a0, a2
                  c.addi     s9, -1
                  c.slli     t5, 22
                  c.srli     a4, 9
                  xor        s11, zero, s7
                  slti       tp, a1, -167
                  lui        s3, 985951
                  mulh       s1, t4, s11
                  div        s7, gp, a4
                  c.slli     t5, 22
                  divu       tp, s5, t4
                  and        s6, t2, a4
                  c.srai     s1, 28
                  c.sub      s0, s1
                  and        s6, t2, a4
                  sltu       s3, a6, a4
                  c.or       a0, a2
                  add        s4, a7, s6
                  div        s7, gp, a4
                  mul        tp, s2, t5
                  srl        t1, tp, zero
                  mul        tp, s2, t5
                  c.srli     a4, 9
                  c.slli     t5, 22
                  c.and      a4, s1
                  divu       tp, s5, t4
                  c.andi     s1, 31
                  sltu       s3, a6, a4
                  and        s6, t2, a4
                  sll        s8, s0, s6
                  sra        s9, s4, t5
                  c.srai     s1, 28
                  c.addi16sp sp, -16
                  srli       zero, a0, 13
                  c.nop
                  sltiu      s3, tp, 300
                  c.addi4spn a2, sp, 528
                  c.addi4spn a2, sp, 528
                  mulhsu     tp, t5, a6
                  c.xor      a4, a5
                  sltiu      s3, tp, 300
                  addi       gp, s8, -298
                  div        s7, gp, a4
                  slti       tp, a1, -167
                  or         a4, a4, zero
                  c.sub      s0, s1
                  c.li       s11, -1
                  srl        t1, tp, zero
                  div        s7, gp, a4
                  sll        s8, s0, s6
                  srai       a4, a3, 0
                  mulhu      s4, a6, t3
                  sra        s9, s4, t5
                  c.slli     t5, 22
                  srai       a4, a3, 0
                  c.addi4spn a2, sp, 528
                  auipc      s1, 11691
                  lui        s3, 985951
                  div        s7, gp, a4
                  c.addi4spn a2, sp, 528
                  divu       tp, s5, t4
                  ori        tp, a0, -848
                  slti       tp, a1, -167
                  auipc      s1, 11691
                  srli       zero, a0, 13
                  c.add      t3, t1
                  auipc      s1, 11691
                  c.lui      a6, 24
                  remu       s6, s3, t1
                  nop
                  c.srai     s1, 28
                  xor        s11, zero, s7
                  c.sub      s0, s1
                  sltu       s3, a6, a4
                  slt        a0, s5, s11
                  and        s6, t2, a4
                  c.andi     s1, 31
                  mulh       s1, t4, s11
                  c.or       a0, a2
                  sra        s9, s4, t5
                  xori       t3, t1, -721
                  c.li       s11, -1
                  xor        s11, zero, s7
                  auipc      s1, 11691
                  or         a4, a4, zero
                  addi       gp, s8, -298
                  c.nop
                  slli       a2, a4, 25
                  c.or       a0, a2
                  c.sub      s0, s1
                  ori        tp, a0, -848
                  c.nop
                  div        s7, gp, a4
                  c.lui      a6, 24
                  c.mv       a2, a0
                  c.mv       a2, a0
                  c.addi     s9, -1
                  slli       a2, a4, 25
                  slli       a2, a4, 25
                  c.and      a4, s1
                  addi       gp, s8, -298
                  slt        a0, s5, s11
                  c.andi     s1, 31
                  mul        tp, s2, t5
                  c.addi16sp sp, -16
                  srli       zero, a0, 13
                  divu       tp, s5, t4
                  c.mv       a2, a0
                  c.addi     s9, -1
                  c.mv       a2, a0
                  sub        s0, t3, gp
                  srai       a4, a3, 0
                  c.or       a0, a2
                  sub        s0, t3, gp
                  sub        s0, t3, gp
                  srai       a4, a3, 0
                  c.slli     t5, 22
                  slli       a2, a4, 25
                  srli       zero, a0, 13
                  c.srai     s1, 28
                  remu       s6, s3, t1
                  c.or       a0, a2
                  c.lui      a6, 24
                  sltu       s3, a6, a4
                  c.addi16sp sp, -16
                  c.mv       a2, a0
                  c.and      a4, s1
                  sra        s9, s4, t5
                  c.addi4spn a2, sp, 528
                  sub        s0, t3, gp
                  srl        t1, tp, zero
                  c.srai     s1, 28
                  andi       t0, a3, 147
                  srl        t1, tp, zero
                  c.lui      a6, 24
                  c.andi     s1, 31
                  slli       a2, a4, 25
                  srli       zero, a0, 13
                  remu       s6, s3, t1
                  mulhu      s4, a6, t3
                  remu       s6, s3, t1
                  c.lui      a6, 24
                  slli       a2, a4, 25
                  nop
                  c.mv       a2, a0
                  lui        s3, 985951
                  c.addi4spn a2, sp, 528
                  rem        a2, s2, s9
                  slli       a2, a4, 25
                  auipc      s1, 11691
                  mul        tp, s2, t5
                  c.add      t3, t1
                  remu       s6, s3, t1
                  c.addi16sp sp, -16
                  add        s4, a7, s6
                  slti       tp, a1, -167
                  mulhsu     tp, t5, a6
                  srli       zero, a0, 13
                  slli       a2, a4, 25
                  c.srli     a4, 9
                  sra        s9, s4, t5
                  c.add      t3, t1
                  c.add      t3, t1
                  mulhu      s4, a6, t3
                  mulhsu     tp, t5, a6
                  slli       a2, a4, 25
                  rem        a2, s2, s9
                  c.or       a0, a2
                  c.and      a4, s1
                  c.andi     s1, 31
                  auipc      s1, 11691
                  sub        s0, t3, gp
                  c.srli     a4, 9
                  rem        a2, s2, s9
                  remu       s6, s3, t1
                  sll        s8, s0, s6
                  c.and      a4, s1
                  sll        s8, s0, s6
                  sltiu      s3, tp, 300
                  div        s7, gp, a4
                  xori       t3, t1, -721
                  srai       a4, a3, 0
                  sltu       s3, a6, a4
                  c.mv       a2, a0
                  sub        s0, t3, gp
                  rem        a2, s2, s9
                  c.li       s11, -1
                  c.xor      a4, a5
                  mulhu      s4, a6, t3
                  srai       a4, a3, 0
                  slt        a0, s5, s11
                  slli       a2, a4, 25
                  mulhsu     tp, t5, a6
                  mul        tp, s2, t5
                  slt        a0, s5, s11
                  c.andi     s1, 31
                  c.xor      a4, a5
                  c.and      a4, s1
                  srai       a4, a3, 0
                  sll        s8, s0, s6
                  c.srai     s1, 28
                  c.addi4spn a2, sp, 528
                  and        s6, t2, a4
                  c.li       s11, -1
                  add        s4, a7, s6
                  c.or       a0, a2
                  c.nop
                  c.and      a4, s1
                  sll        s8, s0, s6
                  c.lui      a6, 24
                  slli       a2, a4, 25
                  addi       gp, s8, -298
                  c.addi4spn a2, sp, 528
                  xor        s11, zero, s7
                  c.xor      a4, a5
                  remu       s6, s3, t1
                  c.andi     s1, 31
                  remu       s6, s3, t1
                  lui        s3, 985951
                  c.lui      a6, 24
                  remu       s6, s3, t1
                  c.and      a4, s1
                  c.srai     s1, 28
                  mul        tp, s2, t5
                  sltiu      s3, tp, 300
                  sll        s8, s0, s6
                  addi       gp, s8, -298
                  or         a4, a4, zero
                  sub        s0, t3, gp
                  slti       tp, a1, -167
                  sltu       s3, a6, a4
                  c.andi     s1, 31
                  add        s4, a7, s6
                  c.addi     s9, -1
                  mulhu      s4, a6, t3
                  div        s7, gp, a4
                  sub        s0, t3, gp
                  xori       t3, t1, -721
                  sra        s9, s4, t5
                  rem        a2, s2, s9
                  c.or       a0, a2
                  c.slli     t5, 22
                  auipc      s1, 11691
                  slt        a0, s5, s11
                  xor        s11, zero, s7
                  c.andi     s1, 31
                  divu       tp, s5, t4
                  auipc      s1, 11691
                  mul        tp, s2, t5
                  xori       t3, t1, -721
                  slli       a2, a4, 25
                  c.nop
                  xor        s11, zero, s7
                  remu       s6, s3, t1
                  rem        a2, s2, s9
                  slli       a2, a4, 25
                  addi       gp, s8, -298
                  sub        s0, t3, gp
                  sub        s0, t3, gp
                  sll        s8, s0, s6
                  or         a4, a4, zero
                  c.xor      a4, a5
                  c.or       a0, a2
                  c.li       s11, -1
                  c.add      t3, t1
                  c.or       a0, a2
                  sub        s0, t3, gp
                  xori       t3, t1, -721
                  div        s7, gp, a4
                  sltiu      s3, tp, 300
                  add        s4, a7, s6
                  sltu       s3, a6, a4
                  srli       zero, a0, 13
                  srli       zero, a0, 13
                  c.xor      a4, a5
                  sltu       s3, a6, a4
                  c.addi16sp sp, -16
                  c.addi16sp sp, -16
                  mulhu      s4, a6, t3
                  slli       a2, a4, 25
                  c.srai     s1, 28
                  mulh       s1, t4, s11
                  c.nop
                  slt        a0, s5, s11
                  c.xor      a4, a5
                  mulhsu     tp, t5, a6
                  c.srli     a4, 9
                  divu       tp, s5, t4
                  mul        tp, s2, t5
                  c.lui      a6, 24
                  mul        tp, s2, t5
                  c.lui      a6, 24
                  c.slli     t5, 22
                  c.mv       a2, a0
                  mul        tp, s2, t5
                  lui        s3, 985951
                  c.sub      s0, s1
                  div        s7, gp, a4
                  c.slli     t5, 22
                  sra        s9, s4, t5
                  c.mv       a2, a0
                  c.addi4spn a2, sp, 528
                  add        s4, a7, s6
                  c.and      a4, s1
                  c.srai     s1, 28
                  c.sub      s0, s1
                  remu       s6, s3, t1
                  addi       gp, s8, -298
                  sra        s9, s4, t5
                  srl        t1, tp, zero
                  c.xor      a4, a5
                  lui        s3, 985951
                  srl        t1, tp, zero
                  c.slli     t5, 22
                  c.or       a0, a2
                  remu       s6, s3, t1
                  c.add      t3, t1
                  andi       t0, a3, 147
                  c.or       a0, a2
                  andi       t0, a3, 147
                  slti       tp, a1, -167
                  mulhu      s4, a6, t3
                  mul        tp, s2, t5
                  c.slli     t5, 22
                  xor        s11, zero, s7
                  c.srai     s1, 28
                  sltu       s3, a6, a4
                  rem        a2, s2, s9
                  and        s6, t2, a4
                  srl        t1, tp, zero
                  addi       gp, s8, -298
                  c.lui      a6, 24
                  or         a4, a4, zero
                  li         ra, 0x0 #start riscv_int_numeric_corner_stream_11
                  li         t2, 0xffffffff
                  li         t5, 0xad6c0f11
                  li         tp, 0xa4f40228
                  li         a6, 0x0
                  li         s0, 0xffffffff
                  li         a0, 0xffffffff
                  li         s3, 0x80000000
                  li         t0, 0x0
                  li         a4, 0x8965d238
                  mulhu      t5, a6, t5
                  sub        a6, ra, t5
                  divu       a0, a4, a6
                  lui        s3, 985951
                  nop
                  lui        s3, 985951
                  remu       s0, t5, a4
                  lui        s3, 985951
                  lui        s3, 985951
                  div        a6, s3, t2
                  nop
                  mulhsu     t5, s0, ra
                  mul        t2, s3, s0
                  nop
                  addi       ra, s3, -40 #end riscv_int_numeric_corner_stream_11
                  sub        s0, t3, gp
                  xori       t3, t1, -721
                  c.addi     s9, -1
                  c.slli     t5, 22
                  and        s6, t2, a4
                  mul        tp, s2, t5
                  srai       a4, a3, 0
                  mulhu      s4, a6, t3
                  c.and      a4, s1
                  srli       zero, a0, 13
                  add        s4, a7, s6
                  sll        s8, s0, s6
                  srli       zero, a0, 13
                  c.nop
                  c.addi16sp sp, -16
                  divu       tp, s5, t4
                  c.lui      a6, 24
                  c.lui      a6, 24
                  srli       zero, a0, 13
                  add        s4, a7, s6
                  rem        a2, s2, s9
                  srli       zero, a0, 13
                  and        s6, t2, a4
                  and        s6, t2, a4
                  sltiu      s3, tp, 300
                  auipc      s1, 11691
                  mulh       s1, t4, s11
                  remu       s6, s3, t1
                  c.mv       a2, a0
                  c.lui      a6, 24
                  add        s4, a7, s6
                  c.addi     s9, -1
                  c.add      t3, t1
                  auipc      s1, 11691
                  c.mv       a2, a0
                  or         a4, a4, zero
                  c.and      a4, s1
                  sll        s8, s0, s6
                  and        s6, t2, a4
                  c.or       a0, a2
                  auipc      s1, 11691
                  xor        s11, zero, s7
                  nop
                  mulhu      s4, a6, t3
                  mulhsu     tp, t5, a6
                  rem        a2, s2, s9
                  mul        tp, s2, t5
                  c.and      a4, s1
                  c.srli     a4, 9
                  c.srli     a4, 9
                  add        s4, a7, s6
                  slt        a0, s5, s11
                  rem        a2, s2, s9
                  sltu       s3, a6, a4
                  or         a4, a4, zero
                  mulhsu     tp, t5, a6
                  mulhu      s4, a6, t3
                  c.mv       a2, a0
                  mul        tp, s2, t5
                  add        s4, a7, s6
                  c.andi     s1, 31
                  div        s7, gp, a4
                  sub        s0, t3, gp
                  add        s4, a7, s6
                  c.nop
                  lui        s3, 985951
                  srli       zero, a0, 13
                  c.srli     a4, 9
                  c.addi     s9, -1
                  lui        s3, 985951
                  xori       t3, t1, -721
                  rem        a2, s2, s9
                  divu       tp, s5, t4
                  c.addi16sp sp, -16
                  srl        t1, tp, zero
                  slt        a0, s5, s11
                  nop
                  sll        s8, s0, s6
                  c.xor      a4, a5
                  mulh       s1, t4, s11
                  srai       a4, a3, 0
                  or         a4, a4, zero
                  c.srli     a4, 9
                  addi       gp, s8, -298
                  rem        a2, s2, s9
                  mul        tp, s2, t5
                  divu       tp, s5, t4
                  srai       a4, a3, 0
                  sltiu      s3, tp, 300
                  ori        tp, a0, -848
                  div        s7, gp, a4
                  xor        s11, zero, s7
                  add        s4, a7, s6
                  mulh       s1, t4, s11
                  div        s7, gp, a4
                  c.mv       a2, a0
                  sltiu      s3, tp, 300
                  mulhu      s4, a6, t3
                  c.lui      a6, 24
                  c.addi16sp sp, -16
                  c.and      a4, s1
                  xori       t3, t1, -721
                  andi       t0, a3, 147
                  addi       gp, s8, -298
                  rem        a2, s2, s9
                  c.addi4spn a2, sp, 528
                  andi       t0, a3, 147
                  addi       gp, s8, -298
                  slli       a2, a4, 25
                  mulhsu     tp, t5, a6
                  c.srai     s1, 28
                  mulhsu     tp, t5, a6
                  sll        s8, s0, s6
                  c.add      t3, t1
                  slti       tp, a1, -167
                  slli       a2, a4, 25
                  mul        tp, s2, t5
                  c.li       s11, -1
                  sltu       s3, a6, a4
                  c.or       a0, a2
                  auipc      s1, 11691
                  sub        s0, t3, gp
                  c.addi     s9, -1
                  mulhsu     tp, t5, a6
                  c.add      t3, t1
                  ori        tp, a0, -848
                  mulh       s1, t4, s11
                  rem        a2, s2, s9
                  sltiu      s3, tp, 300
                  srl        t1, tp, zero
                  c.and      a4, s1
                  div        s7, gp, a4
                  nop
                  c.slli     t5, 22
                  c.addi     s9, -1
                  xor        s11, zero, s7
                  div        s7, gp, a4
                  c.or       a0, a2
                  slli       a2, a4, 25
                  c.xor      a4, a5
                  sltu       s3, a6, a4
                  mulh       s1, t4, s11
                  c.addi4spn a2, sp, 528
                  sub        s0, t3, gp
                  ori        tp, a0, -848
                  nop
                  sltiu      s3, tp, 300
                  lui        s3, 985951
                  sltiu      s3, tp, 300
                  c.lui      a6, 24
                  sltu       s3, a6, a4
                  sltiu      s3, tp, 300
                  add        s4, a7, s6
                  c.addi4spn a2, sp, 528
                  remu       s6, s3, t1
                  c.andi     s1, 31
                  xor        s11, zero, s7
                  rem        a2, s2, s9
                  sra        s9, s4, t5
                  c.sub      s0, s1
                  c.addi16sp sp, -16
                  sll        s8, s0, s6
                  slti       tp, a1, -167
                  srli       zero, a0, 13
                  div        s7, gp, a4
                  c.addi16sp sp, -16
                  c.andi     s1, 31
                  xor        s11, zero, s7
                  auipc      s1, 11691
                  c.andi     s1, 31
                  ori        tp, a0, -848
                  rem        a2, s2, s9
                  srli       zero, a0, 13
                  c.nop
                  mulh       s1, t4, s11
                  rem        a2, s2, s9
                  add        s4, a7, s6
                  sltu       s3, a6, a4
                  c.or       a0, a2
                  c.addi16sp sp, -16
                  slt        a0, s5, s11
                  divu       tp, s5, t4
                  sra        s9, s4, t5
                  divu       tp, s5, t4
                  c.addi16sp sp, -16
                  c.andi     s1, 31
                  c.addi4spn a2, sp, 528
                  mulh       s1, t4, s11
                  sll        s8, s0, s6
                  c.sub      s0, s1
                  c.srli     a4, 9
                  mulh       s1, t4, s11
                  c.and      a4, s1
                  mulhsu     tp, t5, a6
                  srli       zero, a0, 13
                  sra        s9, s4, t5
                  div        s7, gp, a4
                  c.or       a0, a2
                  mulh       s1, t4, s11
                  rem        a2, s2, s9
                  add        s4, a7, s6
                  mulh       s1, t4, s11
                  mulh       s1, t4, s11
                  c.or       a0, a2
                  srli       zero, a0, 13
                  c.addi16sp sp, -16
                  xori       t3, t1, -721
                  c.or       a0, a2
                  mulhsu     tp, t5, a6
                  xori       t3, t1, -721
                  slli       a2, a4, 25
                  auipc      s1, 11691
                  divu       tp, s5, t4
                  c.srli     a4, 9
                  c.and      a4, s1
                  lui        s3, 985951
                  or         a4, a4, zero
                  or         a4, a4, zero
                  nop
                  li         s8, 0x80000000 #start riscv_int_numeric_corner_stream_14
                  li         a0, 0x0
                  li         a3, 0x0
                  li         s2, 0x80000000
                  li         sp, 0xffffffff
                  li         s10, 0xffffffff
                  li         s4, 0x80000000
                  li         s1, 0xc60aaa38
                  li         s6, 0xffffffff
                  li         t2, 0x0
                  mulh       a3, t2, t2
                  lui        t2, 985951
                  remu       s4, s10, a0
                  addi       a0, s6, -40
                  div        s4, a3, t2
                  mulhu      s10, s1, s6
                  addi       a0, s6, -40
                  sub        s4, s1, s8
                  sub        s4, s1, s8
                  auipc      s1, 11691
                  div        s4, a3, t2
                  sub        s4, s1, s8
                  remu       s4, s10, a0
                  nop
                  nop
                  remu       s4, s10, a0
                  addi       a0, s6, -40
                  mulhsu     s4, a3, s1
                  add        s6, sp, s6
                  nop
                  mulh       a3, t2, t2
                  rem        s4, s2, t2
                  nop
                  add        s6, sp, s6
                  sub        s4, s1, s8
                  mulhsu     s4, a3, s1
                  mulh       a3, t2, t2
                  sub        s4, s1, s8
                  div        s4, a3, t2 #end riscv_int_numeric_corner_stream_14
                  c.srai     s1, 28
                  mulh       s1, t4, s11
                  sra        s9, s4, t5
                  c.sub      s0, s1
                  c.and      a4, s1
                  c.li       s11, -1
                  c.li       s11, -1
                  mul        tp, s2, t5
                  mulhsu     tp, t5, a6
                  sltiu      s3, tp, 300
                  ori        tp, a0, -848
                  mulhu      s4, a6, t3
                  c.addi4spn a2, sp, 528
                  c.addi4spn a2, sp, 528
                  divu       tp, s5, t4
                  lui        s3, 985951
                  srl        t1, tp, zero
                  sltu       s3, a6, a4
                  c.or       a0, a2
                  srai       a4, a3, 0
                  sll        s8, s0, s6
                  slti       tp, a1, -167
                  c.srli     a4, 9
                  mulhsu     tp, t5, a6
                  mulhu      s4, a6, t3
                  mul        tp, s2, t5
                  remu       s6, s3, t1
                  sub        s0, t3, gp
                  sub        s0, t3, gp
                  c.add      t3, t1
                  c.xor      a4, a5
                  c.mv       a2, a0
                  nop
                  sra        s9, s4, t5
                  mulh       s1, t4, s11
                  mulhu      s4, a6, t3
                  rem        a2, s2, s9
                  xori       t3, t1, -721
                  auipc      s1, 11691
                  mulhsu     tp, t5, a6
                  slt        a0, s5, s11
                  mulhsu     tp, t5, a6
                  sra        s9, s4, t5
                  and        s6, t2, a4
                  div        s7, gp, a4
                  div        s7, gp, a4
                  slli       a2, a4, 25
                  div        s7, gp, a4
                  xori       t3, t1, -721
                  andi       t0, a3, 147
                  srl        t1, tp, zero
                  c.li       s11, -1
                  sltiu      s3, tp, 300
                  andi       t0, a3, 147
                  xori       t3, t1, -721
                  sltiu      s3, tp, 300
                  slti       tp, a1, -167
                  rem        a2, s2, s9
                  xori       t3, t1, -721
                  mulhu      s4, a6, t3
                  c.addi16sp sp, -16
                  sll        s8, s0, s6
                  c.nop
                  ori        tp, a0, -848
                  mulhsu     tp, t5, a6
                  c.srai     s1, 28
                  slti       tp, a1, -167
                  mulh       s1, t4, s11
                  divu       tp, s5, t4
                  auipc      s1, 11691
                  srai       a4, a3, 0
                  c.lui      a6, 24
                  slli       a2, a4, 25
                  rem        a2, s2, s9
                  c.xor      a4, a5
                  or         a4, a4, zero
                  c.and      a4, s1
                  c.mv       a2, a0
                  addi       gp, s8, -298
                  andi       t0, a3, 147
                  slti       tp, a1, -167
                  c.xor      a4, a5
                  c.li       s11, -1
                  add        s4, a7, s6
                  c.addi16sp sp, -16
                  add        s4, a7, s6
                  c.or       a0, a2
                  c.and      a4, s1
                  div        s7, gp, a4
                  c.mv       a2, a0
                  sltiu      s3, tp, 300
                  nop
                  srl        t1, tp, zero
                  slli       a2, a4, 25
                  remu       s6, s3, t1
                  andi       t0, a3, 147
                  slli       a2, a4, 25
                  c.slli     t5, 22
                  c.nop
                  srl        t1, tp, zero
                  c.addi16sp sp, -16
                  slli       a2, a4, 25
                  c.addi16sp sp, -16
                  add        s4, a7, s6
                  sub        s0, t3, gp
                  c.sub      s0, s1
                  srli       zero, a0, 13
                  mulh       s1, t4, s11
                  slt        a0, s5, s11
                  srl        t1, tp, zero
                  xor        s11, zero, s7
                  mulh       s1, t4, s11
                  rem        a2, s2, s9
                  sub        s0, t3, gp
                  div        s7, gp, a4
                  sll        s8, s0, s6
                  c.xor      a4, a5
                  c.mv       a2, a0
                  c.add      t3, t1
                  slt        a0, s5, s11
                  srl        t1, tp, zero
                  srli       zero, a0, 13
                  sltiu      s3, tp, 300
                  andi       t0, a3, 147
                  mulhu      s4, a6, t3
                  c.li       s11, -1
                  lui        s3, 985951
                  rem        a2, s2, s9
                  c.addi     s9, -1
                  c.lui      a6, 24
                  remu       s6, s3, t1
                  srai       a4, a3, 0
                  c.and      a4, s1
                  andi       t0, a3, 147
                  add        s4, a7, s6
                  c.nop
                  c.sub      s0, s1
                  or         a4, a4, zero
                  remu       s6, s3, t1
                  xori       t3, t1, -721
                  addi       gp, s8, -298
                  c.nop
                  divu       tp, s5, t4
                  div        s7, gp, a4
                  or         a4, a4, zero
                  c.addi4spn a2, sp, 528
                  c.xor      a4, a5
                  c.add      t3, t1
                  c.or       a0, a2
                  add        s4, a7, s6
                  c.and      a4, s1
                  or         a4, a4, zero
                  srl        t1, tp, zero
                  sltu       s3, a6, a4
                  slt        a0, s5, s11
                  nop
                  srli       zero, a0, 13
                  nop
                  c.andi     s1, 31
                  c.xor      a4, a5
                  c.xor      a4, a5
                  mulhu      s4, a6, t3
                  mulhsu     tp, t5, a6
                  andi       t0, a3, 147
                  srli       zero, a0, 13
                  mulhu      s4, a6, t3
                  sll        s8, s0, s6
                  c.or       a0, a2
                  sltu       s3, a6, a4
                  divu       tp, s5, t4
                  mulh       s1, t4, s11
                  sltiu      s3, tp, 300
                  c.or       a0, a2
                  auipc      s1, 11691
                  mulhu      s4, a6, t3
                  srai       a4, a3, 0
                  c.srai     s1, 28
                  c.slli     t5, 22
                  add        s4, a7, s6
                  div        s7, gp, a4
                  c.sub      s0, s1
                  or         a4, a4, zero
                  mulh       s1, t4, s11
                  sra        s9, s4, t5
                  c.mv       a2, a0
                  srl        t1, tp, zero
                  c.srli     a4, 9
                  sub        s0, t3, gp
                  or         a4, a4, zero
                  sra        s9, s4, t5
                  xor        s11, zero, s7
                  andi       t0, a3, 147
                  c.slli     t5, 22
                  mul        tp, s2, t5
                  lui        s3, 985951
                  c.addi     s9, -1
                  c.mv       a2, a0
                  slli       a2, a4, 25
                  c.xor      a4, a5
                  c.srai     s1, 28
                  addi       gp, s8, -298
                  sub        s0, t3, gp
                  sltiu      s3, tp, 300
                  slt        a0, s5, s11
                  c.slli     t5, 22
                  xor        s11, zero, s7
                  sub        s0, t3, gp
                  and        s6, t2, a4
                  xor        s11, zero, s7
                  lui        s3, 985951
                  mulhu      s4, a6, t3
                  mulhu      s4, a6, t3
                  or         a4, a4, zero
                  c.addi16sp sp, -16
                  c.slli     t5, 22
                  slti       tp, a1, -167
                  lui        s3, 985951
                  mulh       s1, t4, s11
                  slti       tp, a1, -167
                  sub        s0, t3, gp
                  c.srli     a4, 9
                  c.srai     s1, 28
                  and        s6, t2, a4
                  divu       tp, s5, t4
                  slli       a2, a4, 25
                  auipc      s1, 11691
                  remu       s6, s3, t1
                  sub        s0, t3, gp
                  srli       zero, a0, 13
                  c.addi16sp sp, -16
                  c.mv       a2, a0
                  c.addi4spn a2, sp, 528
                  or         a4, a4, zero
                  xori       t3, t1, -721
                  addi       gp, s8, -298
                  divu       tp, s5, t4
                  add        s4, a7, s6
                  mulh       s1, t4, s11
                  nop
                  andi       t0, a3, 147
                  auipc      s1, 11691
                  sll        s8, s0, s6
                  c.add      t3, t1
                  c.srai     s1, 28
                  nop
                  c.sub      s0, s1
                  li         ra, 0xe770c156 #start riscv_int_numeric_corner_stream_18
                  li         s2, 0xd7ebdf2c
                  li         t0, 0xffffffff
                  li         a0, 0x0
                  li         s11, 0x0
                  li         a6, 0xffffffff
                  li         s10, 0xffffffff
                  li         s5, 0xffffffff
                  li         s3, 0xffffffff
                  li         s1, 0x461213ee
                  nop
                  mulhu      ra, a6, s5
                  divu       ra, a0, a6
                  nop
                  rem        s5, s1, a0
                  mulhsu     t0, s5, ra
                  add        s11, a0, s10
                  add        s11, a0, s10
                  mulh       t0, t0, t0
                  divu       ra, a0, a6
                  sub        ra, a0, s10
                  nop
                  addi       s1, s3, -40
                  lui        s3, 985951
                  divu       ra, a0, a6
                  sub        ra, a0, s10
                  nop
                  add        s11, a0, s10
                  auipc      s1, 11691
                  div        t0, s1, t0
                  sub        ra, a0, s10
                  remu       s10, a0, s2
                  mul        s2, s3, s1
                  sub        ra, a0, s10
                  auipc      s1, 11691
                  sub        ra, a0, s10 #end riscv_int_numeric_corner_stream_18
                  c.sub      s0, s1
                  srl        t1, tp, zero
                  andi       t0, a3, 147
                  c.addi16sp sp, -16
                  div        s7, gp, a4
                  div        s7, gp, a4
                  rem        a2, s2, s9
                  c.addi     s9, -1
                  c.srli     a4, 9
                  c.srli     a4, 9
                  or         a4, a4, zero
                  c.mv       a2, a0
                  c.addi     s9, -1
                  c.slli     t5, 22
                  slli       a2, a4, 25
                  c.and      a4, s1
                  c.andi     s1, 31
                  c.nop
                  c.or       a0, a2
                  slli       a2, a4, 25
                  c.andi     s1, 31
                  sltu       s3, a6, a4
                  sltu       s3, a6, a4
                  c.addi4spn a2, sp, 528
                  nop
                  slti       tp, a1, -167
                  c.xor      a4, a5
                  remu       s6, s3, t1
                  remu       s6, s3, t1
                  slt        a0, s5, s11
                  lui        s3, 985951
                  andi       t0, a3, 147
                  lui        s3, 985951
                  mulhu      s4, a6, t3
                  c.srli     a4, 9
                  c.addi     s9, -1
                  auipc      s1, 11691
                  c.addi4spn a2, sp, 528
                  c.xor      a4, a5
                  remu       s6, s3, t1
                  remu       s6, s3, t1
                  add        s4, a7, s6
                  sra        s9, s4, t5
                  c.srai     s1, 28
                  c.nop
                  remu       s6, s3, t1
                  srl        t1, tp, zero
                  ori        tp, a0, -848
                  c.nop
                  c.addi     s9, -1
                  c.sub      s0, s1
                  c.srai     s1, 28
                  or         a4, a4, zero
                  rem        a2, s2, s9
                  c.and      a4, s1
                  srli       zero, a0, 13
                  c.and      a4, s1
                  auipc      s1, 11691
                  srai       a4, a3, 0
                  c.nop
                  xor        s11, zero, s7
                  mulhu      s4, a6, t3
                  c.slli     t5, 22
                  c.srli     a4, 9
                  slti       tp, a1, -167
                  c.lui      a6, 24
                  sub        s0, t3, gp
                  addi       gp, s8, -298
                  srli       zero, a0, 13
                  srl        t1, tp, zero
                  xor        s11, zero, s7
                  c.mv       a2, a0
                  ori        tp, a0, -848
                  c.srli     a4, 9
                  or         a4, a4, zero
                  xori       t3, t1, -721
                  rem        a2, s2, s9
                  c.add      t3, t1
                  mulh       s1, t4, s11
                  c.addi     s9, -1
                  rem        a2, s2, s9
                  and        s6, t2, a4
                  srl        t1, tp, zero
                  c.add      t3, t1
                  c.srli     a4, 9
                  srli       zero, a0, 13
                  slti       tp, a1, -167
                  mulhsu     tp, t5, a6
                  auipc      s1, 11691
                  and        s6, t2, a4
                  c.sub      s0, s1
                  srl        t1, tp, zero
                  ori        tp, a0, -848
                  mulh       s1, t4, s11
                  c.li       s11, -1
                  c.li       s11, -1
                  slti       tp, a1, -167
                  div        s7, gp, a4
                  sll        s8, s0, s6
                  lui        s3, 985951
                  mulhu      s4, a6, t3
                  sll        s8, s0, s6
                  andi       t0, a3, 147
                  mulhsu     tp, t5, a6
                  sltu       s3, a6, a4
                  and        s6, t2, a4
                  auipc      s1, 11691
                  srai       a4, a3, 0
                  rem        a2, s2, s9
                  nop
                  c.sub      s0, s1
                  srl        t1, tp, zero
                  add        s4, a7, s6
                  c.lui      a6, 24
                  mul        tp, s2, t5
                  mulhu      s4, a6, t3
                  c.addi4spn a2, sp, 528
                  c.sub      s0, s1
                  or         a4, a4, zero
                  c.sub      s0, s1
                  xori       t3, t1, -721
                  add        s4, a7, s6
                  c.slli     t5, 22
                  ori        tp, a0, -848
                  c.addi     s9, -1
                  auipc      s1, 11691
                  slli       a2, a4, 25
                  c.lui      a6, 24
                  slli       a2, a4, 25
                  srl        t1, tp, zero
                  sub        s0, t3, gp
                  ori        tp, a0, -848
                  slt        a0, s5, s11
                  nop
                  sltu       s3, a6, a4
                  mulhu      s4, a6, t3
                  c.srai     s1, 28
                  mul        tp, s2, t5
                  nop
                  c.addi16sp sp, -16
                  c.and      a4, s1
                  ori        tp, a0, -848
                  slli       a2, a4, 25
                  c.srai     s1, 28
                  xor        s11, zero, s7
                  c.srli     a4, 9
                  srai       a4, a3, 0
                  mulhsu     tp, t5, a6
                  addi       gp, s8, -298
                  srli       zero, a0, 13
                  c.addi4spn a2, sp, 528
                  c.sub      s0, s1
                  sltu       s3, a6, a4
                  xori       t3, t1, -721
                  sltu       s3, a6, a4
                  c.li       s11, -1
                  c.nop
                  c.srai     s1, 28
                  div        s7, gp, a4
                  c.addi16sp sp, -16
                  c.mv       a2, a0
                  c.and      a4, s1
                  sltu       s3, a6, a4
                  c.srai     s1, 28
                  xori       t3, t1, -721
                  sra        s9, s4, t5
                  c.addi     s9, -1
                  addi       gp, s8, -298
                  c.nop
                  div        s7, gp, a4
                  nop
                  srli       zero, a0, 13
                  ori        tp, a0, -848
                  add        s4, a7, s6
                  c.slli     t5, 22
                  auipc      s1, 11691
                  mul        tp, s2, t5
                  c.slli     t5, 22
                  slt        a0, s5, s11
                  sll        s8, s0, s6
                  and        s6, t2, a4
                  add        s4, a7, s6
                  mul        tp, s2, t5
                  mulhu      s4, a6, t3
                  slli       a2, a4, 25
                  c.mv       a2, a0
                  sra        s9, s4, t5
                  c.addi4spn a2, sp, 528
                  srl        t1, tp, zero
                  c.addi16sp sp, -16
                  c.addi16sp sp, -16
                  andi       t0, a3, 147
                  remu       s6, s3, t1
                  mul        tp, s2, t5
                  c.slli     t5, 22
                  c.addi16sp sp, -16
                  sll        s8, s0, s6
                  slti       tp, a1, -167
                  auipc      s1, 11691
                  mul        tp, s2, t5
                  nop
                  c.add      t3, t1
                  or         a4, a4, zero
                  sltu       s3, a6, a4
                  remu       s6, s3, t1
                  remu       s6, s3, t1
                  auipc      s1, 11691
                  remu       s6, s3, t1
                  andi       t0, a3, 147
                  or         a4, a4, zero
                  srl        t1, tp, zero
                  c.slli     t5, 22
                  remu       s6, s3, t1
                  c.and      a4, s1
                  sltu       s3, a6, a4
                  sub        s0, t3, gp
                  c.addi     s9, -1
                  ori        tp, a0, -848
                  addi       gp, s8, -298
                  mulh       s1, t4, s11
                  c.mv       a2, a0
                  auipc      s1, 11691
                  c.and      a4, s1
                  c.slli     t5, 22
                  c.xor      a4, a5
                  sra        s9, s4, t5
                  c.srai     s1, 28
                  add        s4, a7, s6
                  auipc      s1, 11691
                  mul        tp, s2, t5
                  srai       a4, a3, 0
                  srai       a4, a3, 0
                  c.add      t3, t1
                  c.andi     s1, 31
                  sltu       s3, a6, a4
                  c.xor      a4, a5
                  c.lui      a6, 24
                  srl        t1, tp, zero
                  xori       t3, t1, -721
                  lui        s3, 985951
                  div        s7, gp, a4
                  srli       zero, a0, 13
                  divu       tp, s5, t4
                  add        s4, a7, s6
                  srli       zero, a0, 13
                  c.srai     s1, 28
                  xori       t3, t1, -721
                  sltu       s3, a6, a4
                  c.lui      a6, 24
                  sub        s0, t3, gp
                  c.or       a0, a2
                  mulhsu     tp, t5, a6
                  c.li       s11, -1
                  add        s4, a7, s6
                  slt        a0, s5, s11
                  andi       t0, a3, 147
                  mulhsu     tp, t5, a6
                  and        s6, t2, a4
                  c.lui      a6, 24
                  c.addi16sp sp, -16
                  remu       s6, s3, t1
                  sll        s8, s0, s6
                  c.addi16sp sp, -16
                  c.lui      a6, 24
                  c.li       s11, -1
                  c.sub      s0, s1
                  sra        s9, s4, t5
                  srli       zero, a0, 13
                  slli       a2, a4, 25
                  divu       tp, s5, t4
                  mulh       s1, t4, s11
                  c.addi16sp sp, -16
                  auipc      s1, 11691
                  c.nop
                  slti       tp, a1, -167
                  add        s4, a7, s6
                  xori       t3, t1, -721
                  c.addi4spn a2, sp, 528
                  mulh       s1, t4, s11
                  xor        s11, zero, s7
                  slti       tp, a1, -167
                  c.srai     s1, 28
                  c.srli     a4, 9
                  and        s6, t2, a4
                  auipc      s1, 11691
                  or         a4, a4, zero
                  remu       s6, s3, t1
                  div        s7, gp, a4
                  c.xor      a4, a5
                  div        s7, gp, a4
                  c.and      a4, s1
                  slli       a2, a4, 25
                  c.addi     s9, -1
                  c.xor      a4, a5
                  c.slli     t5, 22
                  addi       gp, s8, -298
                  c.xor      a4, a5
                  and        s6, t2, a4
                  c.srli     a4, 9
                  srl        t1, tp, zero
                  mulhu      s4, a6, t3
                  addi       gp, s8, -298
                  c.li       s11, -1
                  sub        s0, t3, gp
                  c.addi4spn a2, sp, 528
                  and        s6, t2, a4
                  xori       t3, t1, -721
                  c.srli     a4, 9
                  slt        a0, s5, s11
                  addi       gp, s8, -298
                  slt        a0, s5, s11
                  c.slli     t5, 22
                  xori       t3, t1, -721
                  srli       zero, a0, 13
                  c.andi     s1, 31
                  mulhu      s4, a6, t3
                  sltiu      s3, tp, 300
                  slli       a2, a4, 25
                  mulhsu     tp, t5, a6
                  c.addi4spn a2, sp, 528
                  divu       tp, s5, t4
                  xor        s11, zero, s7
                  c.addi16sp sp, -16
                  c.andi     s1, 31
                  divu       tp, s5, t4
                  c.nop
                  slli       a2, a4, 25
                  srl        t1, tp, zero
                  div        s7, gp, a4
                  slli       a2, a4, 25
                  add        s4, a7, s6
                  c.or       a0, a2
                  lui        s3, 985951
                  nop
                  c.slli     t5, 22
                  c.or       a0, a2
                  or         a4, a4, zero
                  c.addi4spn a2, sp, 528
                  slli       a2, a4, 25
                  c.srai     s1, 28
                  div        s7, gp, a4
                  divu       tp, s5, t4
                  c.addi4spn a2, sp, 528
                  and        s6, t2, a4
                  mulhsu     tp, t5, a6
                  or         a4, a4, zero
                  mulh       s1, t4, s11
                  rem        a2, s2, s9
                  c.addi4spn a2, sp, 528
                  c.srai     s1, 28
                  remu       s6, s3, t1
                  rem        a2, s2, s9
                  addi       gp, s8, -298
                  c.sub      s0, s1
                  andi       t0, a3, 147
                  mulhu      s4, a6, t3
                  c.slli     t5, 22
                  c.li       s11, -1
                  divu       tp, s5, t4
                  add        s4, a7, s6
                  c.addi4spn a2, sp, 528
                  auipc      s1, 11691
                  and        s6, t2, a4
                  c.addi     s9, -1
                  mulh       s1, t4, s11
                  and        s6, t2, a4
                  xor        s11, zero, s7
                  sltu       s3, a6, a4
                  rem        a2, s2, s9
                  c.slli     t5, 22
                  c.sub      s0, s1
                  c.addi4spn a2, sp, 528
                  c.mv       a2, a0
                  mulhsu     tp, t5, a6
                  c.add      t3, t1
                  sltiu      s3, tp, 300
                  c.add      t3, t1
                  c.andi     s1, 31
                  srli       zero, a0, 13
                  c.li       s11, -1
                  div        s7, gp, a4
                  sra        s9, s4, t5
                  remu       s6, s3, t1
                  sub        s0, t3, gp
                  c.srai     s1, 28
                  c.and      a4, s1
                  c.mv       a2, a0
                  c.srli     a4, 9
                  c.srli     a4, 9
                  c.sub      s0, s1
                  add        s4, a7, s6
                  c.nop
                  c.mv       a2, a0
                  or         a4, a4, zero
                  c.and      a4, s1
                  c.lui      a6, 24
                  c.addi     s9, -1
                  sltu       s3, a6, a4
                  c.or       a0, a2
                  divu       tp, s5, t4
                  sltiu      s3, tp, 300
                  slli       a2, a4, 25
                  rem        a2, s2, s9
                  addi       gp, s8, -298
                  and        s6, t2, a4
                  xori       t3, t1, -721
                  sll        s8, s0, s6
                  and        s6, t2, a4
                  slli       a2, a4, 25
                  c.srli     a4, 9
                  c.xor      a4, a5
                  and        s6, t2, a4
                  ori        tp, a0, -848
                  ori        tp, a0, -848
                  c.sub      s0, s1
                  andi       t0, a3, 147
                  c.or       a0, a2
                  srli       zero, a0, 13
                  c.and      a4, s1
                  c.srli     a4, 9
                  c.addi4spn a2, sp, 528
                  c.andi     s1, 31
                  c.li       s11, -1
                  c.mv       a2, a0
                  xor        s11, zero, s7
                  and        s6, t2, a4
                  c.addi     s9, -1
                  c.srli     a4, 9
                  c.addi4spn a2, sp, 528
                  mulhu      s4, a6, t3
                  c.or       a0, a2
                  c.srai     s1, 28
                  c.srli     a4, 9
                  c.xor      a4, a5
                  c.li       s11, -1
                  auipc      s1, 11691
                  and        s6, t2, a4
                  lui        s3, 985951
                  c.slli     t5, 22
                  xori       t3, t1, -721
                  ori        tp, a0, -848
                  remu       s6, s3, t1
                  sra        s9, s4, t5
                  c.addi     s9, -1
                  c.or       a0, a2
                  sub        s0, t3, gp
                  rem        a2, s2, s9
                  c.srli     a4, 9
                  c.nop
                  c.sub      s0, s1
                  rem        a2, s2, s9
                  c.lui      a6, 24
                  lui        s3, 985951
                  mulhsu     tp, t5, a6
                  mul        tp, s2, t5
                  c.addi4spn a2, sp, 528
                  srai       a4, a3, 0
                  sltu       s3, a6, a4
                  divu       tp, s5, t4
                  mulhsu     tp, t5, a6
                  c.xor      a4, a5
                  remu       s6, s3, t1
                  sra        s9, s4, t5
                  c.srli     a4, 9
                  slli       a2, a4, 25
                  c.or       a0, a2
                  xori       t3, t1, -721
                  c.or       a0, a2
                  divu       tp, s5, t4
                  or         a4, a4, zero
                  c.lui      a6, 24
                  mul        tp, s2, t5
                  rem        a2, s2, s9
                  c.addi16sp sp, -16
                  slt        a0, s5, s11
                  c.srli     a4, 9
                  c.addi16sp sp, -16
                  and        s6, t2, a4
                  sub        s0, t3, gp
                  c.srai     s1, 28
                  c.addi     s9, -1
                  sltu       s3, a6, a4
                  c.add      t3, t1
                  c.slli     t5, 22
                  mulhu      s4, a6, t3
                  srai       a4, a3, 0
                  srl        t1, tp, zero
                  ori        tp, a0, -848
                  ori        tp, a0, -848
                  srai       a4, a3, 0
                  mulhsu     tp, t5, a6
                  sltiu      s3, tp, 300
                  c.sub      s0, s1
                  c.li       s11, -1
                  slt        a0, s5, s11
                  c.addi4spn a2, sp, 528
                  c.and      a4, s1
                  c.addi16sp sp, -16
                  sll        s8, s0, s6
                  sltiu      s3, tp, 300
                  mulhsu     tp, t5, a6
                  mul        tp, s2, t5
                  c.sub      s0, s1
                  c.mv       a2, a0
                  c.srli     a4, 9
                  andi       t0, a3, 147
                  c.andi     s1, 31
                  xor        s11, zero, s7
                  slli       a2, a4, 25
                  c.mv       a2, a0
                  nop
                  mulh       s1, t4, s11
                  c.and      a4, s1
                  auipc      s1, 11691
                  sltu       s3, a6, a4
                  or         a4, a4, zero
                  andi       t0, a3, 147
                  sub        s0, t3, gp
                  c.addi4spn a2, sp, 528
                  add        s4, a7, s6
                  xori       t3, t1, -721
                  c.srli     a4, 9
                  mulhsu     tp, t5, a6
                  addi       gp, s8, -298
                  c.srli     a4, 9
                  divu       tp, s5, t4
                  rem        a2, s2, s9
                  div        s7, gp, a4
                  mul        tp, s2, t5
                  ori        tp, a0, -848
                  c.addi16sp sp, -16
                  c.nop
                  div        s7, gp, a4
                  c.srli     a4, 9
                  c.andi     s1, 31
                  divu       tp, s5, t4
                  slli       a2, a4, 25
                  li         s10, 0x3b7c3fe7 #start riscv_int_numeric_corner_stream_37
                  li         ra, 0x7aa9128f
                  li         t1, 0xffffffff
                  li         t0, 0x0
                  li         s4, 0x0
                  li         s0, 0x0
                  li         s7, 0x0
                  li         a2, 0xd2381f93
                  li         s6, 0x4a083316
                  li         a4, 0xffffffff
                  auipc      s0, 11691
                  nop
                  add        s4, s7, a4
                  div        s4, s4, t0
                  mulhu      t0, s6, s7
                  add        s4, s7, a4
                  rem        s4, ra, a4
                  nop
                  addi       ra, s10, -40
                  nop
                  rem        s4, ra, a4
                  mulh       s10, s7, a2
                  sub        s10, ra, s10
                  lui        s7, 985951
                  mulhsu     a4, a4, ra
                  divu       s0, t1, s10
                  nop
                  nop
                  nop
                  nop
                  nop
                  mulhu      t0, s6, s7
                  rem        s4, ra, a4
                  rem        s4, ra, a4
                  nop
                  mul        t1, s4, a2
                  lui        s7, 985951
                  rem        s4, ra, a4
                  remu       t0, a2, a2 #end riscv_int_numeric_corner_stream_37
                  c.srli     a4, 9
                  c.addi16sp sp, -16
                  or         a4, a4, zero
                  lui        s3, 985951
                  sra        s9, s4, t5
                  mulhu      s4, a6, t3
                  srai       a4, a3, 0
                  c.andi     s1, 31
                  c.add      t3, t1
                  c.nop
                  srai       a4, a3, 0
                  divu       tp, s5, t4
                  mulhsu     tp, t5, a6
                  slti       tp, a1, -167
                  add        s4, a7, s6
                  c.nop
                  ori        tp, a0, -848
                  sra        s9, s4, t5
                  slt        a0, s5, s11
                  srli       zero, a0, 13
                  c.sub      s0, s1
                  rem        a2, s2, s9
                  c.li       s11, -1
                  sltiu      s3, tp, 300
                  and        s6, t2, a4
                  xori       t3, t1, -721
                  mulhu      s4, a6, t3
                  c.addi16sp sp, -16
                  ori        tp, a0, -848
                  c.lui      a6, 24
                  xori       t3, t1, -721
                  auipc      s1, 11691
                  c.lui      a6, 24
                  sub        s0, t3, gp
                  mulhsu     tp, t5, a6
                  c.and      a4, s1
                  c.nop
                  auipc      s1, 11691
                  mulhsu     tp, t5, a6
                  c.slli     t5, 22
                  c.add      t3, t1
                  sub        s0, t3, gp
                  mulhsu     tp, t5, a6
                  add        s4, a7, s6
                  and        s6, t2, a4
                  div        s7, gp, a4
                  ori        tp, a0, -848
                  c.srli     a4, 9
                  add        s4, a7, s6
                  lui        s3, 985951
                  andi       t0, a3, 147
                  ori        tp, a0, -848
                  srai       a4, a3, 0
                  c.xor      a4, a5
                  or         a4, a4, zero
                  srli       zero, a0, 13
                  c.li       s11, -1
                  div        s7, gp, a4
                  c.li       s11, -1
                  sub        s0, t3, gp
                  nop
                  c.sub      s0, s1
                  c.xor      a4, a5
                  divu       tp, s5, t4
                  div        s7, gp, a4
                  mulhu      s4, a6, t3
                  add        s4, a7, s6
                  c.srli     a4, 9
                  andi       t0, a3, 147
                  c.lui      a6, 24
                  slti       tp, a1, -167
                  xori       t3, t1, -721
                  sll        s8, s0, s6
                  sll        s8, s0, s6
                  c.srli     a4, 9
                  c.xor      a4, a5
                  c.srai     s1, 28
                  c.srli     a4, 9
                  c.sub      s0, s1
                  addi       gp, s8, -298
                  srli       zero, a0, 13
                  mul        tp, s2, t5
                  sll        s8, s0, s6
                  c.and      a4, s1
                  addi       gp, s8, -298
                  c.xor      a4, a5
                  slt        a0, s5, s11
                  c.and      a4, s1
                  c.li       s11, -1
                  remu       s6, s3, t1
                  c.xor      a4, a5
                  c.or       a0, a2
                  rem        a2, s2, s9
                  c.addi16sp sp, -16
                  c.addi16sp sp, -16
                  c.lui      a6, 24
                  c.and      a4, s1
                  c.srai     s1, 28
                  lui        s3, 985951
                  mulhsu     tp, t5, a6
                  xor        s11, zero, s7
                  sub        s0, t3, gp
                  ori        tp, a0, -848
                  lui        s3, 985951
                  lui        s3, 985951
                  sub        s0, t3, gp
                  c.or       a0, a2
                  sltiu      s3, tp, 300
                  c.and      a4, s1
                  mulhsu     tp, t5, a6
                  srai       a4, a3, 0
                  c.nop
                  rem        a2, s2, s9
                  mulhsu     tp, t5, a6
                  and        s6, t2, a4
                  and        s6, t2, a4
                  slt        a0, s5, s11
                  c.addi16sp sp, -16
                  lui        s3, 985951
                  c.srai     s1, 28
                  ori        tp, a0, -848
                  rem        a2, s2, s9
                  c.slli     t5, 22
                  sltiu      s3, tp, 300
                  c.srai     s1, 28
                  c.addi16sp sp, -16
                  c.srai     s1, 28
                  slti       tp, a1, -167
                  add        s4, a7, s6
                  mulhu      s4, a6, t3
                  add        s4, a7, s6
                  c.nop
                  srl        t1, tp, zero
                  rem        a2, s2, s9
                  c.addi     s9, -1
                  c.mv       a2, a0
                  c.add      t3, t1
                  mulhu      s4, a6, t3
                  andi       t0, a3, 147
                  srli       zero, a0, 13
                  mulhsu     tp, t5, a6
                  addi       gp, s8, -298
                  c.add      t3, t1
                  c.add      t3, t1
                  divu       tp, s5, t4
                  lui        s3, 985951
                  remu       s6, s3, t1
                  rem        a2, s2, s9
                  mulhu      s4, a6, t3
                  c.srli     a4, 9
                  srai       a4, a3, 0
                  c.srai     s1, 28
                  div        s7, gp, a4
                  c.mv       a2, a0
                  xor        s11, zero, s7
                  c.sub      s0, s1
                  c.xor      a4, a5
                  c.xor      a4, a5
                  slli       a2, a4, 25
                  srai       a4, a3, 0
                  slti       tp, a1, -167
                  c.sub      s0, s1
                  and        s6, t2, a4
                  nop
                  slti       tp, a1, -167
                  sra        s9, s4, t5
                  mulh       s1, t4, s11
                  c.addi16sp sp, -16
                  srl        t1, tp, zero
                  c.slli     t5, 22
                  sll        s8, s0, s6
                  sub        s0, t3, gp
                  sll        s8, s0, s6
                  sra        s9, s4, t5
                  c.lui      a6, 24
                  mulhu      s4, a6, t3
                  c.addi4spn a2, sp, 528
                  slli       a2, a4, 25
                  and        s6, t2, a4
                  nop
                  slt        a0, s5, s11
                  c.srai     s1, 28
                  mul        tp, s2, t5
                  c.srli     a4, 9
                  c.lui      a6, 24
                  c.slli     t5, 22
                  c.add      t3, t1
                  sltu       s3, a6, a4
                  c.srli     a4, 9
                  c.srli     a4, 9
                  divu       tp, s5, t4
                  c.slli     t5, 22
                  c.xor      a4, a5
                  c.sub      s0, s1
                  and        s6, t2, a4
                  sra        s9, s4, t5
                  c.addi     s9, -1
                  c.srli     a4, 9
                  rem        a2, s2, s9
                  andi       t0, a3, 147
                  srai       a4, a3, 0
                  rem        a2, s2, s9
                  sltu       s3, a6, a4
                  c.srai     s1, 28
                  addi       gp, s8, -298
                  or         a4, a4, zero
                  srai       a4, a3, 0
                  c.nop
                  rem        a2, s2, s9
                  remu       s6, s3, t1
                  slt        a0, s5, s11
                  c.andi     s1, 31
                  ori        tp, a0, -848
                  add        s4, a7, s6
                  xor        s11, zero, s7
                  c.srli     a4, 9
                  sltu       s3, a6, a4
                  mulhu      s4, a6, t3
                  nop
                  c.srai     s1, 28
                  sltu       s3, a6, a4
                  divu       tp, s5, t4
                  slti       tp, a1, -167
                  slti       tp, a1, -167
                  rem        a2, s2, s9
                  c.srli     a4, 9
                  divu       tp, s5, t4
                  c.mv       a2, a0
                  nop
                  slt        a0, s5, s11
                  c.nop
                  mulhsu     tp, t5, a6
                  c.addi     s9, -1
                  sra        s9, s4, t5
                  sltiu      s3, tp, 300
                  c.srai     s1, 28
                  auipc      s1, 11691
                  sltiu      s3, tp, 300
                  c.lui      a6, 24
                  addi       gp, s8, -298
                  c.addi16sp sp, -16
                  sra        s9, s4, t5
                  srai       a4, a3, 0
                  ori        tp, a0, -848
                  c.xor      a4, a5
                  sltu       s3, a6, a4
                  c.or       a0, a2
                  and        s6, t2, a4
                  mulhsu     tp, t5, a6
                  c.nop
                  slt        a0, s5, s11
                  mul        tp, s2, t5
                  c.nop
                  c.and      a4, s1
                  sltiu      s3, tp, 300
                  divu       tp, s5, t4
                  c.andi     s1, 31
                  c.andi     s1, 31
                  c.slli     t5, 22
                  slt        a0, s5, s11
                  mulhsu     tp, t5, a6
                  and        s6, t2, a4
                  rem        a2, s2, s9
                  sub        s0, t3, gp
                  c.li       s11, -1
                  nop
                  c.srli     a4, 9
                  xor        s11, zero, s7
                  sltiu      s3, tp, 300
                  sll        s8, s0, s6
                  c.addi16sp sp, -16
                  sub        s0, t3, gp
                  c.li       s11, -1
                  and        s6, t2, a4
                  c.and      a4, s1
                  remu       s6, s3, t1
                  c.xor      a4, a5
                  mulh       s1, t4, s11
                  c.lui      a6, 24
                  srl        t1, tp, zero
                  rem        a2, s2, s9
                  c.addi4spn a2, sp, 528
                  c.lui      a6, 24
                  slt        a0, s5, s11
                  slti       tp, a1, -167
                  and        s6, t2, a4
                  c.sub      s0, s1
                  sltiu      s3, tp, 300
                  srl        t1, tp, zero
                  andi       t0, a3, 147
                  andi       t0, a3, 147
                  c.and      a4, s1
                  auipc      s1, 11691
                  divu       tp, s5, t4
                  auipc      s1, 11691
                  addi       gp, s8, -298
                  c.addi4spn a2, sp, 528
                  slli       a2, a4, 25
                  c.addi4spn a2, sp, 528
                  c.or       a0, a2
                  c.andi     s1, 31
                  lui        s3, 985951
                  srl        t1, tp, zero
                  sll        s8, s0, s6
                  sltiu      s3, tp, 300
                  c.li       s11, -1
                  c.or       a0, a2
                  c.srai     s1, 28
                  auipc      s1, 11691
                  mulhsu     tp, t5, a6
                  and        s6, t2, a4
                  mulh       s1, t4, s11
                  sub        s0, t3, gp
                  mulhu      s4, a6, t3
                  xor        s11, zero, s7
                  c.addi     s9, -1
                  add        s4, a7, s6
                  c.li       s11, -1
                  remu       s6, s3, t1
                  addi       gp, s8, -298
                  sub        s0, t3, gp
                  srl        t1, tp, zero
                  c.sub      s0, s1
                  c.mv       a2, a0
                  c.addi4spn a2, sp, 528
                  add        s4, a7, s6
                  srai       a4, a3, 0
                  srl        t1, tp, zero
                  c.mv       a2, a0
                  xori       t3, t1, -721
                  nop
                  lui        s3, 985951
                  andi       t0, a3, 147
                  xor        s11, zero, s7
                  srai       a4, a3, 0
                  c.srli     a4, 9
                  c.addi     s9, -1
                  and        s6, t2, a4
                  c.addi     s9, -1
                  c.add      t3, t1
                  sra        s9, s4, t5
                  c.nop
                  sltiu      s3, tp, 300
                  xori       t3, t1, -721
                  slli       a2, a4, 25
                  divu       tp, s5, t4
                  srli       zero, a0, 13
                  c.add      t3, t1
                  rem        a2, s2, s9
                  divu       tp, s5, t4
                  c.lui      a6, 24
                  sll        s8, s0, s6
                  nop
                  slli       a2, a4, 25
                  divu       tp, s5, t4
                  remu       s6, s3, t1
                  c.addi4spn a2, sp, 528
                  ori        tp, a0, -848
                  or         a4, a4, zero
                  c.xor      a4, a5
                  c.addi4spn a2, sp, 528
                  sltiu      s3, tp, 300
                  addi       gp, s8, -298
                  nop
                  srai       a4, a3, 0
                  addi       gp, s8, -298
                  sltiu      s3, tp, 300
                  lui        s3, 985951
                  slti       tp, a1, -167
                  c.li       s11, -1
                  sltu       s3, a6, a4
                  remu       s6, s3, t1
                  or         a4, a4, zero
                  rem        a2, s2, s9
                  slli       a2, a4, 25
                  c.addi16sp sp, -16
                  c.xor      a4, a5
                  slti       tp, a1, -167
                  c.addi4spn a2, sp, 528
                  or         a4, a4, zero
                  div        s7, gp, a4
                  sltu       s3, a6, a4
                  lui        s3, 985951
                  slli       a2, a4, 25
                  c.slli     t5, 22
                  c.addi4spn a2, sp, 528
                  nop
                  sub        s0, t3, gp
                  ori        tp, a0, -848
                  c.li       s11, -1
                  srli       zero, a0, 13
                  slti       tp, a1, -167
                  srai       a4, a3, 0
                  c.lui      a6, 24
                  slti       tp, a1, -167
                  c.mv       a2, a0
                  c.sub      s0, s1
                  mulh       s1, t4, s11
                  c.addi4spn a2, sp, 528
                  mulhsu     tp, t5, a6
                  lui        s3, 985951
                  mul        tp, s2, t5
                  c.lui      a6, 24
                  nop
                  c.sub      s0, s1
                  div        s7, gp, a4
                  c.addi     s9, -1
                  remu       s6, s3, t1
                  c.andi     s1, 31
                  c.and      a4, s1
                  c.or       a0, a2
                  lui        s3, 985951
                  mulhsu     tp, t5, a6
                  div        s7, gp, a4
                  c.slli     t5, 22
                  sltu       s3, a6, a4
                  c.and      a4, s1
                  c.or       a0, a2
                  mulh       s1, t4, s11
                  c.addi     s9, -1
                  ori        tp, a0, -848
                  divu       tp, s5, t4
                  or         a4, a4, zero
                  mulh       s1, t4, s11
                  lui        s3, 985951
                  c.or       a0, a2
                  sll        s8, s0, s6
                  c.add      t3, t1
                  ori        tp, a0, -848
                  ori        tp, a0, -848
                  sltu       s3, a6, a4
                  nop
                  mul        tp, s2, t5
                  c.xor      a4, a5
                  sub        s0, t3, gp
                  mulhu      s4, a6, t3
                  c.andi     s1, 31
                  lui        s3, 985951
                  c.slli     t5, 22
                  c.addi4spn a2, sp, 528
                  c.sub      s0, s1
                  div        s7, gp, a4
                  slli       a2, a4, 25
                  c.nop
                  add        s4, a7, s6
                  c.slli     t5, 22
                  c.addi4spn a2, sp, 528
                  c.or       a0, a2
                  div        s7, gp, a4
                  andi       t0, a3, 147
                  c.lui      a6, 24
                  andi       t0, a3, 147
                  c.lui      a6, 24
                  or         a4, a4, zero
                  auipc      s1, 11691
                  sll        s8, s0, s6
                  nop
                  c.addi     s9, -1
                  xori       t3, t1, -721
                  slt        a0, s5, s11
                  remu       s6, s3, t1
                  sub        s0, t3, gp
                  srl        t1, tp, zero
                  sltu       s3, a6, a4
                  c.slli     t5, 22
                  c.mv       a2, a0
                  sra        s9, s4, t5
                  sra        s9, s4, t5
                  sub        s0, t3, gp
                  slli       a2, a4, 25
                  c.srai     s1, 28
                  addi       gp, s8, -298
                  mul        tp, s2, t5
                  c.addi4spn a2, sp, 528
                  mul        tp, s2, t5
                  sub        s0, t3, gp
                  sltiu      s3, tp, 300
                  c.nop
                  c.srai     s1, 28
                  c.addi16sp sp, -16
                  and        s6, t2, a4
                  c.nop
                  c.addi     s9, -1
                  auipc      s1, 11691
                  srli       zero, a0, 13
                  srl        t1, tp, zero
                  srai       a4, a3, 0
                  sra        s9, s4, t5
                  slt        a0, s5, s11
                  mulhu      s4, a6, t3
                  rem        a2, s2, s9
                  nop
                  ori        tp, a0, -848
                  xor        s11, zero, s7
                  c.mv       a2, a0
                  slti       tp, a1, -167
                  addi       gp, s8, -298
                  c.srli     a4, 9
                  lui        s3, 985951
                  c.nop
                  sub        s0, t3, gp
                  srl        t1, tp, zero
                  c.or       a0, a2
                  div        s7, gp, a4
                  sll        s8, s0, s6
                  srai       a4, a3, 0
                  slt        a0, s5, s11
                  sra        s9, s4, t5
                  rem        a2, s2, s9
                  c.sub      s0, s1
                  rem        a2, s2, s9
                  sra        s9, s4, t5
                  c.srai     s1, 28
                  sub        s0, t3, gp
                  c.or       a0, a2
                  mulh       s1, t4, s11
                  c.addi     s9, -1
                  addi       gp, s8, -298
                  c.slli     t5, 22
                  c.xor      a4, a5
                  c.sub      s0, s1
                  sltiu      s3, tp, 300
                  c.addi16sp sp, -16
                  mulh       s1, t4, s11
                  mulhu      s4, a6, t3
                  c.add      t3, t1
                  c.or       a0, a2
                  addi       gp, s8, -298
                  sra        s9, s4, t5
                  sltiu      s3, tp, 300
                  c.add      t3, t1
                  c.lui      a6, 24
                  slti       tp, a1, -167
                  add        s4, a7, s6
                  mulhsu     tp, t5, a6
                  c.sub      s0, s1
                  c.and      a4, s1
                  ori        tp, a0, -848
                  or         a4, a4, zero
                  srai       a4, a3, 0
                  c.xor      a4, a5
                  c.li       s11, -1
                  mulh       s1, t4, s11
                  andi       t0, a3, 147
                  div        s7, gp, a4
                  c.addi     s9, -1
                  sltu       s3, a6, a4
                  ori        tp, a0, -848
                  andi       t0, a3, 147
                  srli       zero, a0, 13
                  c.lui      a6, 24
                  rem        a2, s2, s9
                  c.or       a0, a2
                  divu       tp, s5, t4
                  xor        s11, zero, s7
                  c.srli     a4, 9
                  auipc      s1, 11691
                  c.nop
                  mul        tp, s2, t5
                  div        s7, gp, a4
                  lui        s3, 985951
                  andi       t0, a3, 147
                  c.or       a0, a2
                  slt        a0, s5, s11
                  slt        a0, s5, s11
                  c.addi4spn a2, sp, 528
                  mulhu      s4, a6, t3
                  c.addi16sp sp, -16
                  sltiu      s3, tp, 300
                  andi       t0, a3, 147
                  xor        s11, zero, s7
                  lui        s3, 985951
                  c.lui      a6, 24
                  slt        a0, s5, s11
                  c.and      a4, s1
                  c.add      t3, t1
                  sltiu      s3, tp, 300
                  sltu       s3, a6, a4
                  divu       tp, s5, t4
                  div        s7, gp, a4
                  slli       a2, a4, 25
                  c.addi16sp sp, -16
                  c.srai     s1, 28
                  mulhu      s4, a6, t3
                  srl        t1, tp, zero
                  addi       gp, s8, -298
                  sub        s0, t3, gp
                  c.addi     s9, -1
                  auipc      s1, 11691
                  c.lui      a6, 24
                  sra        s9, s4, t5
                  c.slli     t5, 22
                  srli       zero, a0, 13
                  sll        s8, s0, s6
                  remu       s6, s3, t1
                  addi       gp, s8, -298
                  nop
                  mulh       s1, t4, s11
                  slti       tp, a1, -167
                  srl        t1, tp, zero
                  c.srai     s1, 28
                  or         a4, a4, zero
                  c.add      t3, t1
                  nop
                  mulh       s1, t4, s11
                  mulh       s1, t4, s11
                  srl        t1, tp, zero
                  mulh       s1, t4, s11
                  xori       t3, t1, -721
                  mulhu      s4, a6, t3
                  c.nop
                  c.andi     s1, 31
                  mul        tp, s2, t5
                  addi       gp, s8, -298
                  add        s4, a7, s6
                  slt        a0, s5, s11
                  xor        s11, zero, s7
                  div        s7, gp, a4
                  slli       a2, a4, 25
                  c.andi     s1, 31
                  or         a4, a4, zero
                  c.and      a4, s1
                  c.srai     s1, 28
                  andi       t0, a3, 147
                  add        s4, a7, s6
                  sub        s0, t3, gp
                  div        s7, gp, a4
                  mulhu      s4, a6, t3
                  c.srli     a4, 9
                  c.and      a4, s1
                  c.or       a0, a2
                  mulhsu     tp, t5, a6
                  c.andi     s1, 31
                  c.addi16sp sp, -16
                  c.and      a4, s1
                  rem        a2, s2, s9
                  lui        s3, 985951
                  ori        tp, a0, -848
                  c.srli     a4, 9
                  c.srai     s1, 28
                  c.addi     s9, -1
                  c.add      t3, t1
                  auipc      s1, 11691
                  xori       t3, t1, -721
                  divu       tp, s5, t4
                  lui        s3, 985951
                  c.nop
                  c.srai     s1, 28
                  auipc      s1, 11691
                  srl        t1, tp, zero
                  c.addi16sp sp, -16
                  mul        tp, s2, t5
                  srl        t1, tp, zero
                  c.nop
                  sltu       s3, a6, a4
                  div        s7, gp, a4
                  andi       t0, a3, 147
                  sra        s9, s4, t5
                  lui        s3, 985951
                  c.slli     t5, 22
                  sra        s9, s4, t5
                  srli       zero, a0, 13
                  auipc      s1, 11691
                  mul        tp, s2, t5
                  mul        tp, s2, t5
                  sltu       s3, a6, a4
                  c.mv       a2, a0
                  mulhsu     tp, t5, a6
                  divu       tp, s5, t4
                  c.addi     s9, -1
                  xori       t3, t1, -721
                  rem        a2, s2, s9
                  c.xor      a4, a5
                  mulh       s1, t4, s11
                  srai       a4, a3, 0
                  sra        s9, s4, t5
                  c.addi     s9, -1
                  c.mv       a2, a0
                  slti       tp, a1, -167
                  c.nop
                  mulh       s1, t4, s11
                  slli       a2, a4, 25
                  ori        tp, a0, -848
                  or         a4, a4, zero
                  addi       gp, s8, -298
                  slt        a0, s5, s11
                  sll        s8, s0, s6
                  srli       zero, a0, 13
                  c.lui      a6, 24
                  srl        t1, tp, zero
                  mulh       s1, t4, s11
                  c.srli     a4, 9
                  ori        tp, a0, -848
                  mul        tp, s2, t5
                  sra        s9, s4, t5
                  c.or       a0, a2
                  slti       tp, a1, -167
                  ori        tp, a0, -848
                  c.and      a4, s1
                  c.srli     a4, 9
                  c.srli     a4, 9
                  mulhu      s4, a6, t3
                  c.sub      s0, s1
                  lui        s3, 985951
                  slli       a2, a4, 25
                  sub        s0, t3, gp
                  sll        s8, s0, s6
                  c.and      a4, s1
                  sltu       s3, a6, a4
                  rem        a2, s2, s9
                  srl        t1, tp, zero
                  remu       s6, s3, t1
                  or         a4, a4, zero
                  c.srai     s1, 28
                  slt        a0, s5, s11
                  sll        s8, s0, s6
                  xor        s11, zero, s7
                  rem        a2, s2, s9
                  auipc      s1, 11691
                  sub        s0, t3, gp
                  mulhsu     tp, t5, a6
                  lui        s3, 985951
                  andi       t0, a3, 147
                  remu       s6, s3, t1
                  or         a4, a4, zero
                  lui        s3, 985951
                  sra        s9, s4, t5
                  sltu       s3, a6, a4
                  srai       a4, a3, 0
                  c.srai     s1, 28
                  c.srai     s1, 28
                  lui        s3, 985951
                  c.li       s11, -1
                  rem        a2, s2, s9
                  c.sub      s0, s1
                  mul        tp, s2, t5
                  c.addi4spn a2, sp, 528
                  divu       tp, s5, t4
                  sltu       s3, a6, a4
                  ori        tp, a0, -848
                  sltu       s3, a6, a4
                  c.or       a0, a2
                  c.lui      a6, 24
                  slt        a0, s5, s11
                  lui        s3, 985951
                  mul        tp, s2, t5
                  mulhsu     tp, t5, a6
                  c.srli     a4, 9
                  c.xor      a4, a5
                  add        s4, a7, s6
                  rem        a2, s2, s9
                  sltiu      s3, tp, 300
                  sra        s9, s4, t5
                  c.srai     s1, 28
                  c.andi     s1, 31
                  c.sub      s0, s1
                  and        s6, t2, a4
                  and        s6, t2, a4
                  c.lui      a6, 24
                  mulhsu     tp, t5, a6
                  and        s6, t2, a4
                  c.addi     s9, -1
                  remu       s6, s3, t1
                  c.li       s11, -1
                  xor        s11, zero, s7
                  c.and      a4, s1
                  sltu       s3, a6, a4
                  xor        s11, zero, s7
                  sltiu      s3, tp, 300
                  c.addi4spn a2, sp, 528
                  div        s7, gp, a4
                  c.lui      a6, 24
                  andi       t0, a3, 147
                  c.slli     t5, 22
                  c.srli     a4, 9
                  divu       tp, s5, t4
                  slt        a0, s5, s11
                  auipc      s1, 11691
                  slti       tp, a1, -167
                  c.sub      s0, s1
                  c.xor      a4, a5
                  ori        tp, a0, -848
                  auipc      s1, 11691
                  xor        s11, zero, s7
                  rem        a2, s2, s9
                  c.srai     s1, 28
                  slti       tp, a1, -167
                  mulhu      s4, a6, t3
                  mulhsu     tp, t5, a6
                  c.mv       a2, a0
                  c.addi     s9, -1
                  c.addi16sp sp, -16
                  c.slli     t5, 22
                  sltu       s3, a6, a4
                  sltiu      s3, tp, 300
                  add        s4, a7, s6
                  auipc      s1, 11691
                  add        s4, a7, s6
                  c.or       a0, a2
                  auipc      s1, 11691
                  srli       zero, a0, 13
                  sra        s9, s4, t5
                  srl        t1, tp, zero
                  c.andi     s1, 31
                  and        s6, t2, a4
                  c.or       a0, a2
                  c.li       s11, -1
                  xor        s11, zero, s7
                  mul        tp, s2, t5
                  c.and      a4, s1
                  div        s7, gp, a4
                  div        s7, gp, a4
                  lui        s3, 985951
                  or         a4, a4, zero
                  add        s4, a7, s6
                  auipc      s1, 11691
                  c.andi     s1, 31
                  c.mv       a2, a0
                  sll        s8, s0, s6
                  div        s7, gp, a4
                  sltu       s3, a6, a4
                  lui        s3, 985951
                  slti       tp, a1, -167
                  or         a4, a4, zero
                  slti       tp, a1, -167
                  slt        a0, s5, s11
                  c.andi     s1, 31
                  xor        s11, zero, s7
                  divu       tp, s5, t4
                  div        s7, gp, a4
                  lui        s3, 985951
                  c.add      t3, t1
                  c.srli     a4, 9
                  mulhsu     tp, t5, a6
                  remu       s6, s3, t1
                  sll        s8, s0, s6
                  srl        t1, tp, zero
                  mulh       s1, t4, s11
                  slti       tp, a1, -167
                  c.srai     s1, 28
                  c.add      t3, t1
                  addi       gp, s8, -298
                  xori       t3, t1, -721
                  c.srli     a4, 9
                  sltu       s3, a6, a4
                  c.slli     t5, 22
                  c.sub      s0, s1
                  remu       s6, s3, t1
                  c.and      a4, s1
                  srai       a4, a3, 0
                  srai       a4, a3, 0
                  mulhu      s4, a6, t3
                  c.srai     s1, 28
                  add        s4, a7, s6
                  and        s6, t2, a4
                  srli       zero, a0, 13
                  xor        s11, zero, s7
                  sltu       s3, a6, a4
                  xor        s11, zero, s7
                  remu       s6, s3, t1
                  srli       zero, a0, 13
                  sub        s0, t3, gp
                  c.or       a0, a2
                  sltu       s3, a6, a4
                  slli       a2, a4, 25
                  c.and      a4, s1
                  c.mv       a2, a0
                  sll        s8, s0, s6
                  xor        s11, zero, s7
                  mul        tp, s2, t5
                  sra        s9, s4, t5
                  sub        s0, t3, gp
                  sll        s8, s0, s6
                  divu       tp, s5, t4
                  srli       zero, a0, 13
                  rem        a2, s2, s9
                  c.lui      a6, 24
                  mulhsu     tp, t5, a6
                  c.srai     s1, 28
                  and        s6, t2, a4
                  mulhu      s4, a6, t3
                  srli       zero, a0, 13
                  c.srli     a4, 9
                  c.addi4spn a2, sp, 528
                  c.slli     t5, 22
                  c.mv       a2, a0
                  c.sub      s0, s1
                  sub        s0, t3, gp
                  c.add      t3, t1
                  srli       zero, a0, 13
                  c.mv       a2, a0
                  c.li       s11, -1
                  div        s7, gp, a4
                  divu       tp, s5, t4
                  c.or       a0, a2
                  mul        tp, s2, t5
                  remu       s6, s3, t1
                  c.sub      s0, s1
                  slli       a2, a4, 25
                  c.srai     s1, 28
                  c.xor      a4, a5
                  nop
                  xor        s11, zero, s7
                  or         a4, a4, zero
                  srl        t1, tp, zero
                  mul        tp, s2, t5
                  nop
                  add        s4, a7, s6
                  srli       zero, a0, 13
                  srl        t1, tp, zero
                  sub        s0, t3, gp
                  and        s6, t2, a4
                  c.andi     s1, 31
                  xori       t3, t1, -721
                  mulhsu     tp, t5, a6
                  xori       t3, t1, -721
                  c.add      t3, t1
                  sra        s9, s4, t5
                  c.xor      a4, a5
                  auipc      s1, 11691
                  mulh       s1, t4, s11
                  c.andi     s1, 31
                  c.addi16sp sp, -16
                  mulhu      s4, a6, t3
                  c.srli     a4, 9
                  add        s4, a7, s6
                  mulh       s1, t4, s11
                  c.nop
                  c.srai     s1, 28
                  rem        a2, s2, s9
                  srai       a4, a3, 0
                  c.lui      a6, 24
                  or         a4, a4, zero
                  sub        s0, t3, gp
                  add        s4, a7, s6
                  sll        s8, s0, s6
                  xor        s11, zero, s7
                  c.add      t3, t1
                  c.xor      a4, a5
                  c.slli     t5, 22
                  slti       tp, a1, -167
                  c.addi     s9, -1
                  mulh       s1, t4, s11
                  srli       zero, a0, 13
                  addi       gp, s8, -298
                  sub        s0, t3, gp
                  and        s6, t2, a4
                  div        s7, gp, a4
                  c.addi16sp sp, -16
                  sltiu      s3, tp, 300
                  xor        s11, zero, s7
                  xor        s11, zero, s7
                  andi       t0, a3, 147
                  sltiu      s3, tp, 300
                  sltiu      s3, tp, 300
                  c.slli     t5, 22
                  srl        t1, tp, zero
                  divu       tp, s5, t4
                  c.srai     s1, 28
                  sltu       s3, a6, a4
                  nop
                  div        s7, gp, a4
                  c.addi4spn a2, sp, 528
                  c.addi16sp sp, -16
                  c.addi     s9, -1
                  c.addi     s9, -1
                  c.srai     s1, 28
                  addi       gp, s8, -298
                  c.sub      s0, s1
                  slt        a0, s5, s11
                  ori        tp, a0, -848
                  remu       s6, s3, t1
                  c.sub      s0, s1
                  divu       tp, s5, t4
                  add        s4, a7, s6
                  and        s6, t2, a4
                  slli       a2, a4, 25
                  c.mv       a2, a0
                  lui        s3, 985951
                  c.lui      a6, 24
                  lui        s3, 985951
                  c.xor      a4, a5
                  xori       t3, t1, -721
                  c.andi     s1, 31
                  or         a4, a4, zero
                  sra        s9, s4, t5
                  c.nop
                  andi       t0, a3, 147
                  ori        tp, a0, -848
                  remu       s6, s3, t1
                  c.addi     s9, -1
                  mul        tp, s2, t5
                  divu       tp, s5, t4
                  sltu       s3, a6, a4
                  c.nop
                  ori        tp, a0, -848
                  addi       gp, s8, -298
                  xori       t3, t1, -721
                  and        s6, t2, a4
                  sltiu      s3, tp, 300
                  sll        s8, s0, s6
                  c.addi16sp sp, -16
                  sra        s9, s4, t5
                  srai       a4, a3, 0
                  c.or       a0, a2
                  srli       zero, a0, 13
                  c.srli     a4, 9
                  remu       s6, s3, t1
                  sltiu      s3, tp, 300
                  slt        a0, s5, s11
                  c.srli     a4, 9
                  c.slli     t5, 22
                  c.sub      s0, s1
                  slli       a2, a4, 25
                  sltu       s3, a6, a4
                  divu       tp, s5, t4
                  slli       a2, a4, 25
                  srai       a4, a3, 0
                  or         a4, a4, zero
                  and        s6, t2, a4
                  slli       a2, a4, 25
                  slti       tp, a1, -167
                  c.slli     t5, 22
                  mulh       s1, t4, s11
                  andi       t0, a3, 147
                  or         a4, a4, zero
                  andi       t0, a3, 147
                  sltu       s3, a6, a4
                  and        s6, t2, a4
                  or         a4, a4, zero
                  xori       t3, t1, -721
                  c.srai     s1, 28
                  c.lui      a6, 24
                  mul        tp, s2, t5
                  sub        s0, t3, gp
                  mul        tp, s2, t5
                  mulh       s1, t4, s11
                  lui        s3, 985951
                  lui        s3, 985951
                  andi       t0, a3, 147
                  c.xor      a4, a5
                  slti       tp, a1, -167
                  add        s4, a7, s6
                  andi       t0, a3, 147
                  lui        s3, 985951
                  sltiu      s3, tp, 300
                  srai       a4, a3, 0
                  slti       tp, a1, -167
                  mulhsu     tp, t5, a6
                  c.sub      s0, s1
                  c.sub      s0, s1
                  div        s7, gp, a4
                  c.srai     s1, 28
                  c.li       s11, -1
                  c.addi4spn a2, sp, 528
                  c.addi4spn a2, sp, 528
                  c.andi     s1, 31
                  mulh       s1, t4, s11
                  c.sub      s0, s1
                  c.srli     a4, 9
                  mulhsu     tp, t5, a6
                  addi       gp, s8, -298
                  slti       tp, a1, -167
                  srl        t1, tp, zero
                  addi       gp, s8, -298
                  c.li       s11, -1
                  c.srli     a4, 9
                  c.addi16sp sp, -16
                  c.addi16sp sp, -16
                  ori        tp, a0, -848
                  nop
                  and        s6, t2, a4
                  mulhsu     tp, t5, a6
                  c.srli     a4, 9
                  rem        a2, s2, s9
                  mulhsu     tp, t5, a6
                  c.addi4spn a2, sp, 528
                  mul        tp, s2, t5
                  sltu       s3, a6, a4
                  sra        s9, s4, t5
                  c.addi16sp sp, -16
                  c.srai     s1, 28
                  sra        s9, s4, t5
                  c.lui      a6, 24
                  rem        a2, s2, s9
                  sltu       s3, a6, a4
                  divu       tp, s5, t4
                  rem        a2, s2, s9
                  sll        s8, s0, s6
                  srl        t1, tp, zero
                  c.mv       a2, a0
                  and        s6, t2, a4
                  c.nop
                  remu       s6, s3, t1
                  srli       zero, a0, 13
                  mulhsu     tp, t5, a6
                  c.or       a0, a2
                  c.addi4spn a2, sp, 528
                  c.slli     t5, 22
                  mulh       s1, t4, s11
                  divu       tp, s5, t4
                  slt        a0, s5, s11
                  srl        t1, tp, zero
                  c.andi     s1, 31
                  and        s6, t2, a4
                  sltiu      s3, tp, 300
                  mulh       s1, t4, s11
                  c.li       s11, -1
                  rem        a2, s2, s9
                  mulhu      s4, a6, t3
                  c.li       s11, -1
                  mul        tp, s2, t5
                  srl        t1, tp, zero
                  and        s6, t2, a4
                  rem        a2, s2, s9
                  sra        s9, s4, t5
                  c.andi     s1, 31
                  auipc      s1, 11691
                  c.sub      s0, s1
                  c.addi     s9, -1
                  mul        tp, s2, t5
                  addi       gp, s8, -298
                  sll        s8, s0, s6
                  or         a4, a4, zero
                  c.and      a4, s1
                  c.srli     a4, 9
                  c.addi     s9, -1
                  c.and      a4, s1
                  slti       tp, a1, -167
                  c.andi     s1, 31
                  and        s6, t2, a4
                  c.addi4spn a2, sp, 528
                  c.xor      a4, a5
                  nop
                  c.li       s11, -1
                  xor        s11, zero, s7
                  c.sub      s0, s1
                  add        s4, a7, s6
                  c.sub      s0, s1
                  c.sub      s0, s1
                  and        s6, t2, a4
                  sra        s9, s4, t5
                  c.or       a0, a2
                  c.addi4spn a2, sp, 528
                  mulh       s1, t4, s11
                  mulhu      s4, a6, t3
                  nop
                  srai       a4, a3, 0
                  c.srli     a4, 9
                  c.xor      a4, a5
                  and        s6, t2, a4
                  c.mv       a2, a0
                  c.addi     s9, -1
                  or         a4, a4, zero
                  srai       a4, a3, 0
                  ori        tp, a0, -848
                  xor        s11, zero, s7
                  c.or       a0, a2
                  mul        tp, s2, t5
                  c.and      a4, s1
                  sll        s8, s0, s6
                  slli       a2, a4, 25
                  srl        t1, tp, zero
                  add        s4, a7, s6
                  slti       tp, a1, -167
                  c.and      a4, s1
                  add        s4, a7, s6
                  c.mv       a2, a0
                  nop
                  sltu       s3, a6, a4
                  c.or       a0, a2
                  c.sub      s0, s1
                  c.srai     s1, 28
                  ori        tp, a0, -848
                  sub        s0, t3, gp
                  c.addi16sp sp, -16
                  c.mv       a2, a0
                  slti       tp, a1, -167
                  sra        s9, s4, t5
                  and        s6, t2, a4
                  c.addi16sp sp, -16
                  sltu       s3, a6, a4
                  addi       gp, s8, -298
                  div        s7, gp, a4
                  mulh       s1, t4, s11
                  c.addi4spn a2, sp, 528
                  rem        a2, s2, s9
                  sra        s9, s4, t5
                  c.li       s11, -1
                  c.srai     s1, 28
                  remu       s6, s3, t1
                  andi       t0, a3, 147
                  sltu       s3, a6, a4
                  divu       tp, s5, t4
                  remu       s6, s3, t1
                  ori        tp, a0, -848
                  xori       t3, t1, -721
                  c.and      a4, s1
                  srl        t1, tp, zero
                  slt        a0, s5, s11
                  nop
                  mulhsu     tp, t5, a6
                  c.nop
                  div        s7, gp, a4
                  mul        tp, s2, t5
                  srli       zero, a0, 13
                  nop
                  ori        tp, a0, -848
                  rem        a2, s2, s9
                  slt        a0, s5, s11
                  srl        t1, tp, zero
                  c.srai     s1, 28
                  c.addi4spn a2, sp, 528
                  c.srli     a4, 9
                  rem        a2, s2, s9
                  sltu       s3, a6, a4
                  andi       t0, a3, 147
                  srli       zero, a0, 13
                  remu       s6, s3, t1
                  div        s7, gp, a4
                  addi       gp, s8, -298
                  addi       gp, s8, -298
                  sra        s9, s4, t5
                  c.addi16sp sp, -16
                  add        s4, a7, s6
                  sltu       s3, a6, a4
                  srai       a4, a3, 0
                  c.add      t3, t1
                  c.xor      a4, a5
                  li         s7, 0xffffffff #start riscv_int_numeric_corner_stream_6
                  li         a3, 0xffffffff
                  li         s5, 0x80000000
                  li         s4, 0xbb59ec9c
                  li         s6, 0xffffffff
                  li         t5, 0x0
                  li         s10, 0xffffffff
                  li         s9, 0x80000000
                  li         gp, 0xffffffff
                  li         s0, 0x80000000
                  sub        s10, gp, s10
                  nop
                  auipc      s0, 11691
                  mul        s0, s4, a3
                  add        gp, s7, t5
                  remu       s10, s7, s0
                  sub        s10, gp, s10
                  mulhsu     t5, s0, gp
                  nop
                  mulhu      s5, a3, t5
                  div        s0, t5, gp
                  auipc      s0, 11691
                  rem        s4, s0, gp
                  remu       s10, s7, s0
                  mulhu      s5, a3, t5
                  nop
                  nop
                  add        gp, s7, t5
                  nop
                  sub        s10, gp, s10
                  divu       s0, gp, s9
                  addi       s9, s10, -40
                  nop
                  divu       s0, gp, s9
                  lui        gp, 985951
                  mulhsu     t5, s0, gp #end riscv_int_numeric_corner_stream_6
                  sll        s8, s0, s6
                  c.addi4spn a2, sp, 528
                  xor        s11, zero, s7
                  srai       a4, a3, 0
                  c.nop
                  mul        tp, s2, t5
                  slli       a2, a4, 25
                  mulhu      s4, a6, t3
                  srai       a4, a3, 0
                  sra        s9, s4, t5
                  c.li       s11, -1
                  c.slli     t5, 22
                  or         a4, a4, zero
                  xori       t3, t1, -721
                  slli       a2, a4, 25
                  c.lui      a6, 24
                  sra        s9, s4, t5
                  sub        s0, t3, gp
                  slli       a2, a4, 25
                  lui        s3, 985951
                  c.lui      a6, 24
                  slti       tp, a1, -167
                  slti       tp, a1, -167
                  mulhu      s4, a6, t3
                  c.and      a4, s1
                  lui        s3, 985951
                  lui        s3, 985951
                  mul        tp, s2, t5
                  divu       tp, s5, t4
                  add        s4, a7, s6
                  auipc      s1, 11691
                  mulhu      s4, a6, t3
                  sll        s8, s0, s6
                  mulh       s1, t4, s11
                  li         t3, 0x0 #start riscv_int_numeric_corner_stream_5
                  li         s1, 0xffffffff
                  li         a2, 0x80000000
                  li         s2, 0xeedf868b
                  li         s6, 0x0
                  li         s0, 0xc9175766
                  li         a4, 0xffffffff
                  li         a7, 0xd8542073
                  li         sp, 0x80000000
                  li         a0, 0xffffffff
                  auipc      s1, 11691
                  mulh       a7, a4, a2
                  mulhu      a7, s1, s6
                  remu       sp, s6, a4
                  remu       sp, s6, a4
                  mulhsu     a4, t3, a7
                  divu       sp, a4, a7
                  rem        a2, sp, a4
                  mulhu      a7, s1, s6
                  nop
                  nop
                  auipc      s1, 11691
                  nop
                  mulhu      a7, s1, s6
                  auipc      s1, 11691
                  divu       sp, a4, a7
                  nop #end riscv_int_numeric_corner_stream_5
                  sltiu      s3, tp, 300
                  c.srli     a4, 9
                  sra        s9, s4, t5
                  lui        s3, 985951
                  and        s6, t2, a4
                  c.add      t3, t1
                  c.addi16sp sp, -16
                  divu       tp, s5, t4
                  andi       t0, a3, 147
                  addi       gp, s8, -298
                  c.xor      a4, a5
                  andi       t0, a3, 147
                  sub        s0, t3, gp
                  slti       tp, a1, -167
                  sra        s9, s4, t5
                  rem        a2, s2, s9
                  c.li       s11, -1
                  rem        a2, s2, s9
                  remu       s6, s3, t1
                  c.and      a4, s1
                  nop
                  mul        tp, s2, t5
                  add        s4, a7, s6
                  srai       a4, a3, 0
                  c.addi16sp sp, -16
                  mulh       s1, t4, s11
                  andi       t0, a3, 147
                  auipc      s1, 11691
                  mulhu      s4, a6, t3
                  sub        s0, t3, gp
                  lui        s3, 985951
                  c.lui      a6, 24
                  slti       tp, a1, -167
                  andi       t0, a3, 147
                  addi       gp, s8, -298
                  c.nop
                  sll        s8, s0, s6
                  c.or       a0, a2
                  ori        tp, a0, -848
                  remu       s6, s3, t1
                  rem        a2, s2, s9
                  c.or       a0, a2
                  slt        a0, s5, s11
                  c.and      a4, s1
                  auipc      s1, 11691
                  c.sub      s0, s1
                  addi       gp, s8, -298
                  sub        s0, t3, gp
                  c.srai     s1, 28
                  c.and      a4, s1
                  srl        t1, tp, zero
                  nop
                  lui        s3, 985951
                  c.or       a0, a2
                  ori        tp, a0, -848
                  c.slli     t5, 22
                  addi       gp, s8, -298
                  c.xor      a4, a5
                  xori       t3, t1, -721
                  c.slli     t5, 22
                  srl        t1, tp, zero
                  sub        s0, t3, gp
                  remu       s6, s3, t1
                  c.or       a0, a2
                  sll        s8, s0, s6
                  slti       tp, a1, -167
                  c.mv       a2, a0
                  c.mv       a2, a0
                  mulh       s1, t4, s11
                  srai       a4, a3, 0
                  remu       s6, s3, t1
                  add        s4, a7, s6
                  srai       a4, a3, 0
                  c.srli     a4, 9
                  li         t5, 0x0 #start riscv_int_numeric_corner_stream_15
                  li         s1, 0x0
                  li         s5, 0x351e7347
                  li         s8, 0x80000000
                  li         a4, 0x0
                  li         a0, 0x9f5dafc5
                  li         s0, 0xffffffff
                  li         s3, 0x80000000
                  li         a6, 0xffffffff
                  li         t3, 0xae935f1a
                  sub        s8, s1, s8
                  mulhsu     t5, a0, s5
                  addi       s1, s3, -40
                  mul        a4, a4, a4
                  nop
                  nop
                  sub        s8, s1, s8
                  sub        s8, s1, s8
                  addi       s1, s3, -40
                  nop
                  div        s3, t3, s3
                  mulh       a4, s1, s1
                  auipc      s0, 11691
                  lui        s3, 985951
                  nop
                  rem        s5, s3, a4 #end riscv_int_numeric_corner_stream_15
                  c.addi16sp sp, -16
                  remu       s6, s3, t1
                  divu       tp, s5, t4
                  c.slli     t5, 22
                  lui        s3, 985951
                  c.addi     s9, -1
                  c.andi     s1, 31
                  c.addi16sp sp, -16
                  srai       a4, a3, 0
                  sub        s0, t3, gp
                  slt        a0, s5, s11
                  srl        t1, tp, zero
                  c.and      a4, s1
                  c.slli     t5, 22
                  slli       a2, a4, 25
                  nop
                  c.lui      a6, 24
                  sra        s9, s4, t5
                  c.srai     s1, 28
                  c.li       s11, -1
                  c.and      a4, s1
                  and        s6, t2, a4
                  mulhu      s4, a6, t3
                  divu       tp, s5, t4
                  c.li       s11, -1
                  c.addi4spn a2, sp, 528
                  c.addi16sp sp, -16
                  and        s6, t2, a4
                  div        s7, gp, a4
                  slli       a2, a4, 25
                  rem        a2, s2, s9
                  rem        a2, s2, s9
                  sltiu      s3, tp, 300
                  c.sub      s0, s1
                  c.sub      s0, s1
                  lui        s3, 985951
                  sub        s0, t3, gp
                  add        s4, a7, s6
                  c.and      a4, s1
                  c.li       s11, -1
                  rem        a2, s2, s9
                  c.xor      a4, a5
                  c.srai     s1, 28
                  mulh       s1, t4, s11
                  div        s7, gp, a4
                  slti       tp, a1, -167
                  xor        s11, zero, s7
                  mulh       s1, t4, s11
                  c.or       a0, a2
                  add        s4, a7, s6
                  div        s7, gp, a4
                  c.srli     a4, 9
                  remu       s6, s3, t1
                  nop
                  c.li       s11, -1
                  c.or       a0, a2
                  c.addi16sp sp, -16
                  sub        s0, t3, gp
                  c.li       s11, -1
                  c.srli     a4, 9
                  or         a4, a4, zero
                  srai       a4, a3, 0
                  srai       a4, a3, 0
                  and        s6, t2, a4
                  srli       zero, a0, 13
                  srl        t1, tp, zero
                  xori       t3, t1, -721
                  ori        tp, a0, -848
                  c.or       a0, a2
                  c.mv       a2, a0
                  div        s7, gp, a4
                  ori        tp, a0, -848
                  sltiu      s3, tp, 300
                  c.lui      a6, 24
                  c.add      t3, t1
                  nop
                  sub        s0, t3, gp
                  sltiu      s3, tp, 300
                  slli       a2, a4, 25
                  c.li       s11, -1
                  sll        s8, s0, s6
                  add        s4, a7, s6
                  andi       t0, a3, 147
                  lui        s3, 985951
                  or         a4, a4, zero
                  c.and      a4, s1
                  c.lui      a6, 24
                  slt        a0, s5, s11
                  c.add      t3, t1
                  sltu       s3, a6, a4
                  or         a4, a4, zero
                  c.addi4spn a2, sp, 528
                  add        s4, a7, s6
                  add        s4, a7, s6
                  addi       gp, s8, -298
                  c.addi     s9, -1
                  auipc      s1, 11691
                  rem        a2, s2, s9
                  and        s6, t2, a4
                  c.or       a0, a2
                  mulh       s1, t4, s11
                  divu       tp, s5, t4
                  c.li       s11, -1
                  c.addi     s9, -1
                  c.addi16sp sp, -16
                  srli       zero, a0, 13
                  or         a4, a4, zero
                  c.and      a4, s1
                  c.addi16sp sp, -16
                  sra        s9, s4, t5
                  sltu       s3, a6, a4
                  c.li       s11, -1
                  sltiu      s3, tp, 300
                  addi       gp, s8, -298
                  auipc      s1, 11691
                  c.addi4spn a2, sp, 528
                  c.srai     s1, 28
                  sll        s8, s0, s6
                  c.addi4spn a2, sp, 528
                  c.andi     s1, 31
                  xori       t3, t1, -721
                  add        s4, a7, s6
                  srai       a4, a3, 0
                  srli       zero, a0, 13
                  andi       t0, a3, 147
                  rem        a2, s2, s9
                  srl        t1, tp, zero
                  sub        s0, t3, gp
                  c.slli     t5, 22
                  mul        tp, s2, t5
                  slti       tp, a1, -167
                  xori       t3, t1, -721
                  c.addi16sp sp, -16
                  auipc      s1, 11691
                  c.xor      a4, a5
                  and        s6, t2, a4
                  andi       t0, a3, 147
                  c.li       s11, -1
                  andi       t0, a3, 147
                  andi       t0, a3, 147
                  c.lui      a6, 24
                  xor        s11, zero, s7
                  slti       tp, a1, -167
                  c.srai     s1, 28
                  sltiu      s3, tp, 300
                  c.addi4spn a2, sp, 528
                  add        s4, a7, s6
                  div        s7, gp, a4
                  c.addi4spn a2, sp, 528
                  c.andi     s1, 31
                  c.slli     t5, 22
                  ori        tp, a0, -848
                  rem        a2, s2, s9
                  c.mv       a2, a0
                  mulhu      s4, a6, t3
                  ori        tp, a0, -848
                  ori        tp, a0, -848
                  nop
                  c.add      t3, t1
                  xori       t3, t1, -721
                  c.mv       a2, a0
                  c.nop
                  remu       s6, s3, t1
                  nop
                  mulh       s1, t4, s11
                  c.add      t3, t1
                  c.slli     t5, 22
                  c.srli     a4, 9
                  c.xor      a4, a5
                  xori       t3, t1, -721
                  mulhsu     tp, t5, a6
                  c.addi16sp sp, -16
                  add        s4, a7, s6
                  mulhsu     tp, t5, a6
                  c.sub      s0, s1
                  c.srli     a4, 9
                  srl        t1, tp, zero
                  auipc      s1, 11691
                  sub        s0, t3, gp
                  mulh       s1, t4, s11
                  mulhsu     tp, t5, a6
                  slt        a0, s5, s11
                  c.nop
                  c.slli     t5, 22
                  c.addi16sp sp, -16
                  mul        tp, s2, t5
                  c.lui      a6, 24
                  c.addi4spn a2, sp, 528
                  or         a4, a4, zero
                  divu       tp, s5, t4
                  c.lui      a6, 24
                  mulhsu     tp, t5, a6
                  c.addi     s9, -1
                  slt        a0, s5, s11
                  ori        tp, a0, -848
                  ori        tp, a0, -848
                  sll        s8, s0, s6
                  slti       tp, a1, -167
                  nop
                  auipc      s1, 11691
                  srai       a4, a3, 0
                  sra        s9, s4, t5
                  sltu       s3, a6, a4
                  sub        s0, t3, gp
                  c.srai     s1, 28
                  c.mv       a2, a0
                  c.addi     s9, -1
                  add        s4, a7, s6
                  c.xor      a4, a5
                  c.slli     t5, 22
                  ori        tp, a0, -848
                  ori        tp, a0, -848
                  c.mv       a2, a0
                  c.and      a4, s1
                  add        s4, a7, s6
                  remu       s6, s3, t1
                  xor        s11, zero, s7
                  c.xor      a4, a5
                  srli       zero, a0, 13
                  sub        s0, t3, gp
                  c.sub      s0, s1
                  c.mv       a2, a0
                  or         a4, a4, zero
                  auipc      s1, 11691
                  c.slli     t5, 22
                  ori        tp, a0, -848
                  mulhsu     tp, t5, a6
                  sra        s9, s4, t5
                  slti       tp, a1, -167
                  add        s4, a7, s6
                  slt        a0, s5, s11
                  auipc      s1, 11691
                  addi       gp, s8, -298
                  lui        s3, 985951
                  c.addi16sp sp, -16
                  mulhsu     tp, t5, a6
                  c.slli     t5, 22
                  c.add      t3, t1
                  sltu       s3, a6, a4
                  rem        a2, s2, s9
                  c.li       s11, -1
                  c.srli     a4, 9
                  xor        s11, zero, s7
                  slt        a0, s5, s11
                  remu       s6, s3, t1
                  c.nop
                  or         a4, a4, zero
                  auipc      s1, 11691
                  c.slli     t5, 22
                  slt        a0, s5, s11
                  c.andi     s1, 31
                  or         a4, a4, zero
                  sub        s0, t3, gp
                  lui        s3, 985951
                  c.addi16sp sp, -16
                  add        s4, a7, s6
                  nop
                  div        s7, gp, a4
                  auipc      s1, 11691
                  c.li       s11, -1
                  mulh       s1, t4, s11
                  and        s6, t2, a4
                  sub        s0, t3, gp
                  srai       a4, a3, 0
                  and        s6, t2, a4
                  slli       a2, a4, 25
                  add        s4, a7, s6
                  c.mv       a2, a0
                  sltu       s3, a6, a4
                  c.addi     s9, -1
                  rem        a2, s2, s9
                  c.mv       a2, a0
                  add        s4, a7, s6
                  sra        s9, s4, t5
                  xori       t3, t1, -721
                  srai       a4, a3, 0
                  c.slli     t5, 22
                  c.andi     s1, 31
                  c.lui      a6, 24
                  xori       t3, t1, -721
                  or         a4, a4, zero
                  mulhsu     tp, t5, a6
                  auipc      s1, 11691
                  srli       zero, a0, 13
                  mulh       s1, t4, s11
                  srai       a4, a3, 0
                  c.nop
                  xori       t3, t1, -721
                  sltu       s3, a6, a4
                  c.addi     s9, -1
                  c.nop
                  c.addi16sp sp, -16
                  add        s4, a7, s6
                  sltiu      s3, tp, 300
                  sra        s9, s4, t5
                  c.addi     s9, -1
                  or         a4, a4, zero
                  c.andi     s1, 31
                  c.andi     s1, 31
                  or         a4, a4, zero
                  c.addi16sp sp, -16
                  or         a4, a4, zero
                  sra        s9, s4, t5
                  rem        a2, s2, s9
                  slt        a0, s5, s11
                  c.addi     s9, -1
                  c.andi     s1, 31
                  sll        s8, s0, s6
                  c.addi4spn a2, sp, 528
                  c.addi     s9, -1
                  c.srli     a4, 9
                  mulhu      s4, a6, t3
                  and        s6, t2, a4
                  div        s7, gp, a4
                  c.and      a4, s1
                  addi       gp, s8, -298
                  c.andi     s1, 31
                  nop
                  c.xor      a4, a5
                  c.and      a4, s1
                  c.sub      s0, s1
                  div        s7, gp, a4
                  and        s6, t2, a4
                  sub        s0, t3, gp
                  c.and      a4, s1
                  c.srli     a4, 9
                  mulhsu     tp, t5, a6
                  remu       s6, s3, t1
                  c.srai     s1, 28
                  addi       gp, s8, -298
                  and        s6, t2, a4
                  c.add      t3, t1
                  lui        s3, 985951
                  add        s4, a7, s6
                  ori        tp, a0, -848
                  c.addi4spn a2, sp, 528
                  mulhsu     tp, t5, a6
                  sub        s0, t3, gp
                  c.and      a4, s1
                  remu       s6, s3, t1
                  mul        tp, s2, t5
                  mulhu      s4, a6, t3
                  c.addi     s9, -1
                  mulh       s1, t4, s11
                  remu       s6, s3, t1
                  addi       gp, s8, -298
                  c.and      a4, s1
                  lui        s3, 985951
                  c.xor      a4, a5
                  div        s7, gp, a4
                  c.andi     s1, 31
                  c.mv       a2, a0
                  add        s4, a7, s6
                  slti       tp, a1, -167
                  sll        s8, s0, s6
                  c.li       s11, -1
                  auipc      s1, 11691
                  divu       tp, s5, t4
                  c.andi     s1, 31
                  sub        s0, t3, gp
                  c.addi16sp sp, -16
                  remu       s6, s3, t1
                  xor        s11, zero, s7
                  srli       zero, a0, 13
                  and        s6, t2, a4
                  c.addi     s9, -1
                  mulhu      s4, a6, t3
                  xor        s11, zero, s7
                  or         a4, a4, zero
                  c.srli     a4, 9
                  xori       t3, t1, -721
                  ori        tp, a0, -848
                  mulh       s1, t4, s11
                  xori       t3, t1, -721
                  sltiu      s3, tp, 300
                  or         a4, a4, zero
                  addi       gp, s8, -298
                  rem        a2, s2, s9
                  mulhsu     tp, t5, a6
                  div        s7, gp, a4
                  c.or       a0, a2
                  c.srai     s1, 28
                  mul        tp, s2, t5
                  c.sub      s0, s1
                  c.add      t3, t1
                  divu       tp, s5, t4
                  c.addi     s9, -1
                  mulh       s1, t4, s11
                  auipc      s1, 11691
                  nop
                  c.nop
                  c.nop
                  div        s7, gp, a4
                  or         a4, a4, zero
                  srli       zero, a0, 13
                  nop
                  remu       s6, s3, t1
                  addi       gp, s8, -298
                  auipc      s1, 11691
                  c.srli     a4, 9
                  andi       t0, a3, 147
                  sltiu      s3, tp, 300
                  or         a4, a4, zero
                  c.and      a4, s1
                  auipc      s1, 11691
                  c.mv       a2, a0
                  sub        s0, t3, gp
                  xori       t3, t1, -721
                  c.li       s11, -1
                  c.nop
                  srl        t1, tp, zero
                  auipc      s1, 11691
                  andi       t0, a3, 147
                  c.sub      s0, s1
                  nop
                  c.add      t3, t1
                  div        s7, gp, a4
                  slti       tp, a1, -167
                  c.nop
                  mulhu      s4, a6, t3
                  slli       a2, a4, 25
                  sltiu      s3, tp, 300
                  nop
                  auipc      s1, 11691
                  c.andi     s1, 31
                  xor        s11, zero, s7
                  xori       t3, t1, -721
                  remu       s6, s3, t1
                  mulhsu     tp, t5, a6
                  srli       zero, a0, 13
                  mulh       s1, t4, s11
                  c.and      a4, s1
                  mulh       s1, t4, s11
                  sltiu      s3, tp, 300
                  ori        tp, a0, -848
                  c.li       s11, -1
                  c.andi     s1, 31
                  c.addi4spn a2, sp, 528
                  c.add      t3, t1
                  c.and      a4, s1
                  sltu       s3, a6, a4
                  c.srai     s1, 28
                  xori       t3, t1, -721
                  srai       a4, a3, 0
                  nop
                  mulhu      s4, a6, t3
                  add        s4, a7, s6
                  c.srai     s1, 28
                  c.or       a0, a2
                  xor        s11, zero, s7
                  auipc      s1, 11691
                  sra        s9, s4, t5
                  andi       t0, a3, 147
                  sltiu      s3, tp, 300
                  srl        t1, tp, zero
                  slt        a0, s5, s11
                  c.li       s11, -1
                  sra        s9, s4, t5
                  xor        s11, zero, s7
                  mulhsu     tp, t5, a6
                  c.addi16sp sp, -16
                  c.xor      a4, a5
                  c.li       s11, -1
                  c.lui      a6, 24
                  c.mv       a2, a0
                  lui        s3, 985951
                  div        s7, gp, a4
                  xor        s11, zero, s7
                  and        s6, t2, a4
                  sra        s9, s4, t5
                  ori        tp, a0, -848
                  or         a4, a4, zero
                  c.lui      a6, 24
                  c.addi4spn a2, sp, 528
                  sra        s9, s4, t5
                  slt        a0, s5, s11
                  c.slli     t5, 22
                  c.or       a0, a2
                  mulhsu     tp, t5, a6
                  mulhsu     tp, t5, a6
                  srli       zero, a0, 13
                  slt        a0, s5, s11
                  c.slli     t5, 22
                  remu       s6, s3, t1
                  c.nop
                  c.nop
                  srl        t1, tp, zero
                  srai       a4, a3, 0
                  c.mv       a2, a0
                  xor        s11, zero, s7
                  and        s6, t2, a4
                  srai       a4, a3, 0
                  c.lui      a6, 24
                  nop
                  sub        s0, t3, gp
                  c.nop
                  mulh       s1, t4, s11
                  slti       tp, a1, -167
                  sltiu      s3, tp, 300
                  sub        s0, t3, gp
                  xori       t3, t1, -721
                  c.andi     s1, 31
                  remu       s6, s3, t1
                  c.sub      s0, s1
                  sltu       s3, a6, a4
                  addi       gp, s8, -298
                  slli       a2, a4, 25
                  div        s7, gp, a4
                  c.or       a0, a2
                  mul        tp, s2, t5
                  c.or       a0, a2
                  divu       tp, s5, t4
                  rem        a2, s2, s9
                  slt        a0, s5, s11
                  c.srai     s1, 28
                  sll        s8, s0, s6
                  c.add      t3, t1
                  c.add      t3, t1
                  srai       a4, a3, 0
                  sltu       s3, a6, a4
                  mul        tp, s2, t5
                  sltiu      s3, tp, 300
                  c.and      a4, s1
                  srai       a4, a3, 0
                  sltu       s3, a6, a4
                  c.srli     a4, 9
                  slti       tp, a1, -167
                  srai       a4, a3, 0
                  sltiu      s3, tp, 300
                  c.slli     t5, 22
                  sll        s8, s0, s6
                  andi       t0, a3, 147
                  ori        tp, a0, -848
                  srli       zero, a0, 13
                  mul        tp, s2, t5
                  c.li       s11, -1
                  ori        tp, a0, -848
                  nop
                  c.xor      a4, a5
                  add        s4, a7, s6
                  sltu       s3, a6, a4
                  slli       a2, a4, 25
                  xor        s11, zero, s7
                  nop
                  c.li       s11, -1
                  nop
                  c.andi     s1, 31
                  slti       tp, a1, -167
                  rem        a2, s2, s9
                  c.srai     s1, 28
                  c.mv       a2, a0
                  mulhsu     tp, t5, a6
                  c.sub      s0, s1
                  c.xor      a4, a5
                  slti       tp, a1, -167
                  xori       t3, t1, -721
                  slli       a2, a4, 25
                  mulhsu     tp, t5, a6
                  c.lui      a6, 24
                  auipc      s1, 11691
                  div        s7, gp, a4
                  div        s7, gp, a4
                  xor        s11, zero, s7
                  c.slli     t5, 22
                  c.addi16sp sp, -16
                  c.sub      s0, s1
                  sll        s8, s0, s6
                  add        s4, a7, s6
                  sltiu      s3, tp, 300
                  slt        a0, s5, s11
                  xori       t3, t1, -721
                  xor        s11, zero, s7
                  sltiu      s3, tp, 300
                  divu       tp, s5, t4
                  sra        s9, s4, t5
                  xori       t3, t1, -721
                  c.and      a4, s1
                  c.addi4spn a2, sp, 528
                  c.and      a4, s1
                  andi       t0, a3, 147
                  c.add      t3, t1
                  ori        tp, a0, -848
                  lui        s3, 985951
                  nop
                  mulh       s1, t4, s11
                  remu       s6, s3, t1
                  sub        s0, t3, gp
                  sub        s0, t3, gp
                  c.srai     s1, 28
                  c.addi4spn a2, sp, 528
                  c.addi     s9, -1
                  xori       t3, t1, -721
                  and        s6, t2, a4
                  divu       tp, s5, t4
                  c.xor      a4, a5
                  divu       tp, s5, t4
                  lui        s3, 985951
                  lui        s3, 985951
                  ori        tp, a0, -848
                  remu       s6, s3, t1
                  c.srai     s1, 28
                  c.srli     a4, 9
                  nop
                  c.and      a4, s1
                  c.andi     s1, 31
                  andi       t0, a3, 147
                  lui        s3, 985951
                  or         a4, a4, zero
                  add        s4, a7, s6
                  auipc      s1, 11691
                  slt        a0, s5, s11
                  remu       s6, s3, t1
                  slli       a2, a4, 25
                  sll        s8, s0, s6
                  remu       s6, s3, t1
                  c.or       a0, a2
                  remu       s6, s3, t1
                  slti       tp, a1, -167
                  slt        a0, s5, s11
                  c.slli     t5, 22
                  srai       a4, a3, 0
                  mulh       s1, t4, s11
                  c.add      t3, t1
                  c.addi4spn a2, sp, 528
                  rem        a2, s2, s9
                  sltiu      s3, tp, 300
                  c.xor      a4, a5
                  auipc      s1, 11691
                  srai       a4, a3, 0
                  srl        t1, tp, zero
                  addi       gp, s8, -298
                  rem        a2, s2, s9
                  slti       tp, a1, -167
                  slti       tp, a1, -167
                  ori        tp, a0, -848
                  sra        s9, s4, t5
                  slli       a2, a4, 25
                  or         a4, a4, zero
                  ori        tp, a0, -848
                  addi       gp, s8, -298
                  nop
                  c.addi4spn a2, sp, 528
                  xor        s11, zero, s7
                  mulhu      s4, a6, t3
                  c.srai     s1, 28
                  ori        tp, a0, -848
                  add        s4, a7, s6
                  c.add      t3, t1
                  or         a4, a4, zero
                  c.xor      a4, a5
                  c.xor      a4, a5
                  c.addi4spn a2, sp, 528
                  c.xor      a4, a5
                  xor        s11, zero, s7
                  c.addi4spn a2, sp, 528
                  add        s4, a7, s6
                  sltiu      s3, tp, 300
                  srai       a4, a3, 0
                  sra        s9, s4, t5
                  auipc      s1, 11691
                  mul        tp, s2, t5
                  auipc      s1, 11691
                  remu       s6, s3, t1
                  mulh       s1, t4, s11
                  and        s6, t2, a4
                  sltiu      s3, tp, 300
                  sltiu      s3, tp, 300
                  andi       t0, a3, 147
                  slti       tp, a1, -167
                  slti       tp, a1, -167
                  srl        t1, tp, zero
                  c.nop
                  addi       gp, s8, -298
                  mulhsu     tp, t5, a6
                  xor        s11, zero, s7
                  mulhu      s4, a6, t3
                  ori        tp, a0, -848
                  sll        s8, s0, s6
                  c.andi     s1, 31
                  or         a4, a4, zero
                  mulhsu     tp, t5, a6
                  div        s7, gp, a4
                  sll        s8, s0, s6
                  slti       tp, a1, -167
                  divu       tp, s5, t4
                  and        s6, t2, a4
                  sll        s8, s0, s6
                  remu       s6, s3, t1
                  rem        a2, s2, s9
                  auipc      s1, 11691
                  c.xor      a4, a5
                  c.srai     s1, 28
                  sltu       s3, a6, a4
                  c.sub      s0, s1
                  nop
                  c.srli     a4, 9
                  srl        t1, tp, zero
                  mulhsu     tp, t5, a6
                  c.srli     a4, 9
                  ori        tp, a0, -848
                  c.or       a0, a2
                  and        s6, t2, a4
                  xori       t3, t1, -721
                  c.srli     a4, 9
                  xor        s11, zero, s7
                  mul        tp, s2, t5
                  c.lui      a6, 24
                  c.mv       a2, a0
                  c.slli     t5, 22
                  c.sub      s0, s1
                  mul        tp, s2, t5
                  mulhu      s4, a6, t3
                  c.or       a0, a2
                  nop
                  ori        tp, a0, -848
                  slli       a2, a4, 25
                  xor        s11, zero, s7
                  mul        tp, s2, t5
                  rem        a2, s2, s9
                  auipc      s1, 11691
                  mulh       s1, t4, s11
                  sra        s9, s4, t5
                  c.srai     s1, 28
                  c.addi4spn a2, sp, 528
                  rem        a2, s2, s9
                  div        s7, gp, a4
                  slli       a2, a4, 25
                  andi       t0, a3, 147
                  c.or       a0, a2
                  c.srli     a4, 9
                  c.add      t3, t1
                  sltu       s3, a6, a4
                  remu       s6, s3, t1
                  nop
                  c.add      t3, t1
                  slli       a2, a4, 25
                  c.andi     s1, 31
                  sra        s9, s4, t5
                  divu       tp, s5, t4
                  srl        t1, tp, zero
                  and        s6, t2, a4
                  mulhsu     tp, t5, a6
                  c.and      a4, s1
                  divu       tp, s5, t4
                  c.sub      s0, s1
                  c.or       a0, a2
                  div        s7, gp, a4
                  auipc      s1, 11691
                  sltiu      s3, tp, 300
                  sltiu      s3, tp, 300
                  divu       tp, s5, t4
                  srli       zero, a0, 13
                  and        s6, t2, a4
                  c.addi     s9, -1
                  mulhu      s4, a6, t3
                  andi       t0, a3, 147
                  c.slli     t5, 22
                  srli       zero, a0, 13
                  c.addi     s9, -1
                  divu       tp, s5, t4
                  c.sub      s0, s1
                  sltu       s3, a6, a4
                  c.srli     a4, 9
                  srli       zero, a0, 13
                  ori        tp, a0, -848
                  auipc      s1, 11691
                  mulhu      s4, a6, t3
                  sltiu      s3, tp, 300
                  mulh       s1, t4, s11
                  c.srai     s1, 28
                  nop
                  c.andi     s1, 31
                  c.mv       a2, a0
                  c.addi16sp sp, -16
                  mulhsu     tp, t5, a6
                  c.mv       a2, a0
                  c.lui      a6, 24
                  c.sub      s0, s1
                  sub        s0, t3, gp
                  c.slli     t5, 22
                  mulhu      s4, a6, t3
                  c.srai     s1, 28
                  c.li       s11, -1
                  divu       tp, s5, t4
                  srli       zero, a0, 13
                  c.lui      a6, 24
                  srl        t1, tp, zero
                  or         a4, a4, zero
                  c.srli     a4, 9
                  c.slli     t5, 22
                  lui        s3, 985951
                  div        s7, gp, a4
                  c.or       a0, a2
                  sra        s9, s4, t5
                  lui        s3, 985951
                  srai       a4, a3, 0
                  divu       tp, s5, t4
                  c.mv       a2, a0
                  c.mv       a2, a0
                  auipc      s1, 11691
                  c.xor      a4, a5
                  c.li       s11, -1
                  xor        s11, zero, s7
                  c.mv       a2, a0
                  andi       t0, a3, 147
                  c.and      a4, s1
                  c.srai     s1, 28
                  ori        tp, a0, -848
                  c.nop
                  c.and      a4, s1
                  c.addi16sp sp, -16
                  ori        tp, a0, -848
                  srli       zero, a0, 13
                  and        s6, t2, a4
                  sltiu      s3, tp, 300
                  sll        s8, s0, s6
                  c.and      a4, s1
                  sra        s9, s4, t5
                  li         s3, 0x9fc4ed12 #start riscv_int_numeric_corner_stream_17
                  li         a4, 0xffffffff
                  li         s8, 0x0
                  li         sp, 0x29cafa7d
                  li         t4, 0x7b501a29
                  li         s6, 0xda2565da
                  li         s0, 0xffffffff
                  li         t2, 0x80000000
                  li         a6, 0xffffffff
                  li         a3, 0x2fd7c225
                  sub        s8, s8, s8
                  nop
                  rem        t4, a6, a4
                  mulhsu     t2, s0, s3
                  nop
                  divu       s8, s6, a6
                  sub        s8, s8, s8
                  nop
                  lui        s3, 985951
                  div        t4, a3, t2
                  sub        s8, s8, s8
                  mul        t2, s8, a4
                  nop
                  div        t4, a3, t2
                  rem        t4, a6, a4
                  add        t2, t4, a4 #end riscv_int_numeric_corner_stream_17
                  sltu       s3, a6, a4
                  auipc      s1, 11691
                  sltu       s3, a6, a4
                  remu       s6, s3, t1
                  div        s7, gp, a4
                  mul        tp, s2, t5
                  andi       t0, a3, 147
                  c.add      t3, t1
                  andi       t0, a3, 147
                  mulhsu     tp, t5, a6
                  c.mv       a2, a0
                  ori        tp, a0, -848
                  nop
                  mulh       s1, t4, s11
                  sltu       s3, a6, a4
                  xor        s11, zero, s7
                  slli       a2, a4, 25
                  c.addi4spn a2, sp, 528
                  c.nop
                  nop
                  c.addi16sp sp, -16
                  and        s6, t2, a4
                  c.addi     s9, -1
                  slti       tp, a1, -167
                  xori       t3, t1, -721
                  mulh       s1, t4, s11
                  c.srai     s1, 28
                  and        s6, t2, a4
                  srai       a4, a3, 0
                  c.addi16sp sp, -16
                  sltiu      s3, tp, 300
                  c.addi16sp sp, -16
                  div        s7, gp, a4
                  c.li       s11, -1
                  divu       tp, s5, t4
                  c.srai     s1, 28
                  or         a4, a4, zero
                  mul        tp, s2, t5
                  c.nop
                  c.and      a4, s1
                  srai       a4, a3, 0
                  c.li       s11, -1
                  nop
                  c.srai     s1, 28
                  c.lui      a6, 24
                  sra        s9, s4, t5
                  c.or       a0, a2
                  c.addi     s9, -1
                  c.addi4spn a2, sp, 528
                  c.srai     s1, 28
                  c.addi16sp sp, -16
                  c.lui      a6, 24
                  srl        t1, tp, zero
                  c.addi     s9, -1
                  nop
                  c.lui      a6, 24
                  sltiu      s3, tp, 300
                  xor        s11, zero, s7
                  sltu       s3, a6, a4
                  and        s6, t2, a4
                  c.andi     s1, 31
                  andi       t0, a3, 147
                  sll        s8, s0, s6
                  mulhsu     tp, t5, a6
                  srli       zero, a0, 13
                  srai       a4, a3, 0
                  sll        s8, s0, s6
                  and        s6, t2, a4
                  sltiu      s3, tp, 300
                  slt        a0, s5, s11
                  add        s4, a7, s6
                  slli       a2, a4, 25
                  xori       t3, t1, -721
                  c.or       a0, a2
                  slli       a2, a4, 25
                  xori       t3, t1, -721
                  mulhsu     tp, t5, a6
                  and        s6, t2, a4
                  div        s7, gp, a4
                  mul        tp, s2, t5
                  or         a4, a4, zero
                  sltu       s3, a6, a4
                  c.srai     s1, 28
                  srli       zero, a0, 13
                  andi       t0, a3, 147
                  sra        s9, s4, t5
                  xori       t3, t1, -721
                  srli       zero, a0, 13
                  slti       tp, a1, -167
                  and        s6, t2, a4
                  slt        a0, s5, s11
                  sltiu      s3, tp, 300
                  c.or       a0, a2
                  slti       tp, a1, -167
                  ori        tp, a0, -848
                  c.addi     s9, -1
                  srai       a4, a3, 0
                  slti       tp, a1, -167
                  and        s6, t2, a4
                  srl        t1, tp, zero
                  divu       tp, s5, t4
                  remu       s6, s3, t1
                  c.sub      s0, s1
                  c.xor      a4, a5
                  c.and      a4, s1
                  mul        tp, s2, t5
                  or         a4, a4, zero
                  lui        s3, 985951
                  c.addi16sp sp, -16
                  andi       t0, a3, 147
                  sub        s0, t3, gp
                  srli       zero, a0, 13
                  mulh       s1, t4, s11
                  xori       t3, t1, -721
                  ori        tp, a0, -848
                  c.srli     a4, 9
                  c.addi16sp sp, -16
                  divu       tp, s5, t4
                  ori        tp, a0, -848
                  c.xor      a4, a5
                  mulhu      s4, a6, t3
                  c.or       a0, a2
                  xor        s11, zero, s7
                  mulh       s1, t4, s11
                  srai       a4, a3, 0
                  c.srai     s1, 28
                  mulhu      s4, a6, t3
                  div        s7, gp, a4
                  sub        s0, t3, gp
                  c.lui      a6, 24
                  auipc      s1, 11691
                  c.addi4spn a2, sp, 528
                  div        s7, gp, a4
                  c.mv       a2, a0
                  mulhsu     tp, t5, a6
                  c.srli     a4, 9
                  srli       zero, a0, 13
                  c.xor      a4, a5
                  add        s4, a7, s6
                  mul        tp, s2, t5
                  slt        a0, s5, s11
                  mulhu      s4, a6, t3
                  mulhu      s4, a6, t3
                  srli       zero, a0, 13
                  or         a4, a4, zero
                  mulh       s1, t4, s11
                  nop
                  ori        tp, a0, -848
                  srli       zero, a0, 13
                  rem        a2, s2, s9
                  srli       zero, a0, 13
                  c.li       s11, -1
                  slti       tp, a1, -167
                  c.andi     s1, 31
                  sltu       s3, a6, a4
                  srai       a4, a3, 0
                  c.srai     s1, 28
                  c.srai     s1, 28
                  remu       s6, s3, t1
                  slti       tp, a1, -167
                  c.xor      a4, a5
                  c.addi16sp sp, -16
                  srl        t1, tp, zero
                  addi       gp, s8, -298
                  slti       tp, a1, -167
                  remu       s6, s3, t1
                  mulhu      s4, a6, t3
                  addi       gp, s8, -298
                  remu       s6, s3, t1
                  c.nop
                  c.srai     s1, 28
                  slt        a0, s5, s11
                  c.srai     s1, 28
                  andi       t0, a3, 147
                  mulhsu     tp, t5, a6
                  xori       t3, t1, -721
                  c.and      a4, s1
                  srai       a4, a3, 0
                  nop
                  c.srai     s1, 28
                  auipc      s1, 11691
                  rem        a2, s2, s9
                  or         a4, a4, zero
                  sltu       s3, a6, a4
                  and        s6, t2, a4
                  addi       gp, s8, -298
                  divu       tp, s5, t4
                  mulhsu     tp, t5, a6
                  c.srai     s1, 28
                  sltu       s3, a6, a4
                  c.or       a0, a2
                  rem        a2, s2, s9
                  c.xor      a4, a5
                  sra        s9, s4, t5
                  auipc      s1, 11691
                  slli       a2, a4, 25
                  c.and      a4, s1
                  mulhsu     tp, t5, a6
                  srl        t1, tp, zero
                  slti       tp, a1, -167
                  c.xor      a4, a5
                  c.sub      s0, s1
                  and        s6, t2, a4
                  xori       t3, t1, -721
                  mulhu      s4, a6, t3
                  divu       tp, s5, t4
                  srli       zero, a0, 13
                  andi       t0, a3, 147
                  auipc      s1, 11691
                  auipc      s1, 11691
                  andi       t0, a3, 147
                  sub        s0, t3, gp
                  srai       a4, a3, 0
                  or         a4, a4, zero
                  srai       a4, a3, 0
                  c.nop
                  c.and      a4, s1
                  c.and      a4, s1
                  ori        tp, a0, -848
                  mulhu      s4, a6, t3
                  divu       tp, s5, t4
                  ori        tp, a0, -848
                  sll        s8, s0, s6
                  slti       tp, a1, -167
                  nop
                  and        s6, t2, a4
                  lui        s3, 985951
                  c.or       a0, a2
                  slt        a0, s5, s11
                  srai       a4, a3, 0
                  c.srai     s1, 28
                  div        s7, gp, a4
                  c.srli     a4, 9
                  c.li       s11, -1
                  srl        t1, tp, zero
                  c.li       s11, -1
                  divu       tp, s5, t4
                  lui        s3, 985951
                  c.addi     s9, -1
                  c.nop
                  xori       t3, t1, -721
                  srai       a4, a3, 0
                  c.and      a4, s1
                  andi       t0, a3, 147
                  sra        s9, s4, t5
                  c.srai     s1, 28
                  c.add      t3, t1
                  nop
                  lui        s3, 985951
                  c.and      a4, s1
                  c.add      t3, t1
                  c.nop
                  c.andi     s1, 31
                  c.nop
                  slli       a2, a4, 25
                  c.slli     t5, 22
                  srli       zero, a0, 13
                  lui        s3, 985951
                  slti       tp, a1, -167
                  c.addi16sp sp, -16
                  c.slli     t5, 22
                  srl        t1, tp, zero
                  #j test_done
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

                  li a0, test_ret_val
                  lw a1, test_results /* report result */
                  sw a1,0(a0)

                  wfi  /* we are done */
##End: Extracted from riscv_compliance_tests/riscv_test.h

test_done:        
                  li gp, 1
                  ecall
write_tohost:     
                  sw gp, tohost, t5

_exit:            
                  j write_tohost

init_machine_mode:
                  li x10, 0x1800
                  csrw 0x300, x10 # MSTATUS
                  li x10, 0x0
                  csrw 0x304, x10 # MIE
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
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x342 # MCAUSE
                  srli x10, x10, 0x1f
                  beqz x10, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_2:
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x342 # MCAUSE
                  srli x10, x10, 0x1f
                  beqz x10, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_3:
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x342 # MCAUSE
                  srli x10, x10, 0x1f
                  beqz x10, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_4:
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x342 # MCAUSE
                  srli x10, x10, 0x1f
                  beqz x10, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_5:
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x342 # MCAUSE
                  srli x10, x10, 0x1f
                  beqz x10, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_6:
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x342 # MCAUSE
                  srli x10, x10, 0x1f
                  beqz x10, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_7:
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x342 # MCAUSE
                  srli x10, x10, 0x1f
                  beqz x10, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_8:
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x342 # MCAUSE
                  srli x10, x10, 0x1f
                  beqz x10, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_9:
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x342 # MCAUSE
                  srli x10, x10, 0x1f
                  beqz x10, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_10:
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x342 # MCAUSE
                  srli x10, x10, 0x1f
                  beqz x10, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_11:
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x342 # MCAUSE
                  srli x10, x10, 0x1f
                  beqz x10, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_12:
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x342 # MCAUSE
                  srli x10, x10, 0x1f
                  beqz x10, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_13:
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x342 # MCAUSE
                  srli x10, x10, 0x1f
                  beqz x10, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_14:
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x342 # MCAUSE
                  srli x10, x10, 0x1f
                  beqz x10, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_15:
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x342 # MCAUSE
                  srli x10, x10, 0x1f
                  beqz x10, 1f
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
                  csrrw x15, 0x340, x15
                  add x15, x31, zero
                  1: addi x15, x15, -124
                  sw  x1, 4(x15)
                  sw  x2, 8(x15)
                  sw  x3, 12(x15)
                  sw  x4, 16(x15)
                  sw  x5, 20(x15)
                  sw  x6, 24(x15)
                  sw  x7, 28(x15)
                  sw  x8, 32(x15)
                  sw  x9, 36(x15)
                  sw  x10, 40(x15)
                  sw  x11, 44(x15)
                  sw  x12, 48(x15)
                  sw  x13, 52(x15)
                  sw  x14, 56(x15)
                  sw  x15, 60(x15)
                  sw  x16, 64(x15)
                  sw  x17, 68(x15)
                  sw  x18, 72(x15)
                  sw  x19, 76(x15)
                  sw  x20, 80(x15)
                  sw  x21, 84(x15)
                  sw  x22, 88(x15)
                  sw  x23, 92(x15)
                  sw  x24, 96(x15)
                  sw  x25, 100(x15)
                  sw  x26, 104(x15)
                  sw  x27, 108(x15)
                  sw  x28, 112(x15)
                  sw  x29, 116(x15)
                  sw  x30, 120(x15)
                  sw  x31, 124(x15)
                  csrr x10, 0x341 # MEPC
                  csrr x10, 0x342 # MCAUSE
                  li x2, 0x3 # BREAKPOINT
                  beq x10, x2, ebreak_handler
                  li x2, 0x8 # ECALL_UMODE
                  beq x10, x2, ecall_handler
                  li x2, 0x9 # ECALL_SMODE
                  beq x10, x2, ecall_handler
                  li x2, 0xb # ECALL_MMODE
                  beq x10, x2, ecall_handler
                  li x2, 0x1
                  beq x10, x2, instr_fault_handler
                  li x2, 0x5
                  beq x10, x2, load_fault_handler
                  li x2, 0x7
                  beq x10, x2, store_fault_handler
                  li x2, 0xc
                  beq x10, x2, pt_fault_handler
                  li x2, 0xd
                  beq x10, x2, pt_fault_handler
                  li x2, 0xf
                  beq x10, x2, pt_fault_handler
                  li x2, 0x2 # ILLEGAL_INSTRUCTION
                  beq x10, x2, illegal_instr_handler
                  csrr x2, 0x343 # MTVAL
                  1: jal x1, test_done 

ecall_handler:    
                  la x10, _start
                  sw x0, 0(x10)
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  j write_tohost
instr_fault_handler:
                  lw  x1, 4(x15)
                  lw  x2, 8(x15)
                  lw  x3, 12(x15)
                  lw  x4, 16(x15)
                  lw  x5, 20(x15)
                  lw  x6, 24(x15)
                  lw  x7, 28(x15)
                  lw  x8, 32(x15)
                  lw  x9, 36(x15)
                  lw  x10, 40(x15)
                  lw  x11, 44(x15)
                  lw  x12, 48(x15)
                  lw  x13, 52(x15)
                  lw  x14, 56(x15)
                  lw  x15, 60(x15)
                  lw  x16, 64(x15)
                  lw  x17, 68(x15)
                  lw  x18, 72(x15)
                  lw  x19, 76(x15)
                  lw  x20, 80(x15)
                  lw  x21, 84(x15)
                  lw  x22, 88(x15)
                  lw  x23, 92(x15)
                  lw  x24, 96(x15)
                  lw  x25, 100(x15)
                  lw  x26, 104(x15)
                  lw  x27, 108(x15)
                  lw  x28, 112(x15)
                  lw  x29, 116(x15)
                  lw  x30, 120(x15)
                  lw  x31, 124(x15)
                  addi x15, x15, 124
                  add x31, x15, zero
                  csrrw x15, 0x340, x15
                  mret

load_fault_handler:
                  lw  x1, 4(x15)
                  lw  x2, 8(x15)
                  lw  x3, 12(x15)
                  lw  x4, 16(x15)
                  lw  x5, 20(x15)
                  lw  x6, 24(x15)
                  lw  x7, 28(x15)
                  lw  x8, 32(x15)
                  lw  x9, 36(x15)
                  lw  x10, 40(x15)
                  lw  x11, 44(x15)
                  lw  x12, 48(x15)
                  lw  x13, 52(x15)
                  lw  x14, 56(x15)
                  lw  x15, 60(x15)
                  lw  x16, 64(x15)
                  lw  x17, 68(x15)
                  lw  x18, 72(x15)
                  lw  x19, 76(x15)
                  lw  x20, 80(x15)
                  lw  x21, 84(x15)
                  lw  x22, 88(x15)
                  lw  x23, 92(x15)
                  lw  x24, 96(x15)
                  lw  x25, 100(x15)
                  lw  x26, 104(x15)
                  lw  x27, 108(x15)
                  lw  x28, 112(x15)
                  lw  x29, 116(x15)
                  lw  x30, 120(x15)
                  lw  x31, 124(x15)
                  addi x15, x15, 124
                  add x31, x15, zero
                  csrrw x15, 0x340, x15
                  mret

store_fault_handler:
                  lw  x1, 4(x15)
                  lw  x2, 8(x15)
                  lw  x3, 12(x15)
                  lw  x4, 16(x15)
                  lw  x5, 20(x15)
                  lw  x6, 24(x15)
                  lw  x7, 28(x15)
                  lw  x8, 32(x15)
                  lw  x9, 36(x15)
                  lw  x10, 40(x15)
                  lw  x11, 44(x15)
                  lw  x12, 48(x15)
                  lw  x13, 52(x15)
                  lw  x14, 56(x15)
                  lw  x15, 60(x15)
                  lw  x16, 64(x15)
                  lw  x17, 68(x15)
                  lw  x18, 72(x15)
                  lw  x19, 76(x15)
                  lw  x20, 80(x15)
                  lw  x21, 84(x15)
                  lw  x22, 88(x15)
                  lw  x23, 92(x15)
                  lw  x24, 96(x15)
                  lw  x25, 100(x15)
                  lw  x26, 104(x15)
                  lw  x27, 108(x15)
                  lw  x28, 112(x15)
                  lw  x29, 116(x15)
                  lw  x30, 120(x15)
                  lw  x31, 124(x15)
                  addi x15, x15, 124
                  add x31, x15, zero
                  csrrw x15, 0x340, x15
                  mret

ebreak_handler:   
                  csrr  x10, mepc
                  addi  x10, x10, 4
                  csrw  mepc, x10
                  lw  x1, 4(x15)
                  lw  x2, 8(x15)
                  lw  x3, 12(x15)
                  lw  x4, 16(x15)
                  lw  x5, 20(x15)
                  lw  x6, 24(x15)
                  lw  x7, 28(x15)
                  lw  x8, 32(x15)
                  lw  x9, 36(x15)
                  lw  x10, 40(x15)
                  lw  x11, 44(x15)
                  lw  x12, 48(x15)
                  lw  x13, 52(x15)
                  lw  x14, 56(x15)
                  lw  x15, 60(x15)
                  lw  x16, 64(x15)
                  lw  x17, 68(x15)
                  lw  x18, 72(x15)
                  lw  x19, 76(x15)
                  lw  x20, 80(x15)
                  lw  x21, 84(x15)
                  lw  x22, 88(x15)
                  lw  x23, 92(x15)
                  lw  x24, 96(x15)
                  lw  x25, 100(x15)
                  lw  x26, 104(x15)
                  lw  x27, 108(x15)
                  lw  x28, 112(x15)
                  lw  x29, 116(x15)
                  lw  x30, 120(x15)
                  lw  x31, 124(x15)
                  addi x15, x15, 124
                  add x31, x15, zero
                  csrrw x15, 0x340, x15
                  mret

illegal_instr_handler:
                  csrr  x10, mepc
                  addi  x10, x10, 4
                  csrw  mepc, x10
                  lw  x1, 4(x15)
                  lw  x2, 8(x15)
                  lw  x3, 12(x15)
                  lw  x4, 16(x15)
                  lw  x5, 20(x15)
                  lw  x6, 24(x15)
                  lw  x7, 28(x15)
                  lw  x8, 32(x15)
                  lw  x9, 36(x15)
                  lw  x10, 40(x15)
                  lw  x11, 44(x15)
                  lw  x12, 48(x15)
                  lw  x13, 52(x15)
                  lw  x14, 56(x15)
                  lw  x15, 60(x15)
                  lw  x16, 64(x15)
                  lw  x17, 68(x15)
                  lw  x18, 72(x15)
                  lw  x19, 76(x15)
                  lw  x20, 80(x15)
                  lw  x21, 84(x15)
                  lw  x22, 88(x15)
                  lw  x23, 92(x15)
                  lw  x24, 96(x15)
                  lw  x25, 100(x15)
                  lw  x26, 104(x15)
                  lw  x27, 108(x15)
                  lw  x28, 112(x15)
                  lw  x29, 116(x15)
                  lw  x30, 120(x15)
                  lw  x31, 124(x15)
                  addi x15, x15, 124
                  add x31, x15, zero
                  csrrw x15, 0x340, x15
                  mret

pt_fault_handler: 
                  nop

.align 2
mmode_intr_handler:
                  csrr  x10, 0x300 # MSTATUS;
                  csrr  x10, 0x304 # MIE;
                  csrr  x10, 0x344 # MIP;
                  csrrc x10, 0x344, x10 # MIP;
                  lw  x1, 4(x15)
                  lw  x2, 8(x15)
                  lw  x3, 12(x15)
                  lw  x4, 16(x15)
                  lw  x5, 20(x15)
                  lw  x6, 24(x15)
                  lw  x7, 28(x15)
                  lw  x8, 32(x15)
                  lw  x9, 36(x15)
                  lw  x10, 40(x15)
                  lw  x11, 44(x15)
                  lw  x12, 48(x15)
                  lw  x13, 52(x15)
                  lw  x14, 56(x15)
                  lw  x15, 60(x15)
                  lw  x16, 64(x15)
                  lw  x17, 68(x15)
                  lw  x18, 72(x15)
                  lw  x19, 76(x15)
                  lw  x20, 80(x15)
                  lw  x21, 84(x15)
                  lw  x22, 88(x15)
                  lw  x23, 92(x15)
                  lw  x24, 96(x15)
                  lw  x25, 100(x15)
                  lw  x26, 104(x15)
                  lw  x27, 108(x15)
                  lw  x28, 112(x15)
                  lw  x29, 116(x15)
                  lw  x30, 120(x15)
                  lw  x31, 124(x15)
                  addi x15, x15, 124
                  add x31, x15, zero
                  csrrw x15, 0x340, x15
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
