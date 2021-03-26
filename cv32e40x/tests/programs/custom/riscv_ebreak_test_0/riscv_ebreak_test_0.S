.include "user_define.h"

.section .text.start
.global _start
.type _start, @function

_start:
    j _start_main


.globl _start_main
.section .text
_start_main:
                  li x0, 0xf21ee7dc
                  li x1, 0x80000000
                  li x2, 0xfd183497
                  li x3, 0xccda4374
                  li x4, 0x0
                  li x5, 0xf4cb539d
                  li x6, 0x80000000
                  li x7, 0x3
                  li x8, 0xfdef1f09
                  li x9, 0x80000000
                  li x10, 0x4
                  li x11, 0xf58fad61
                  li x12, 0xfb6606db
                  li x13, 0x0
                  li x14, 0xf0cee247
                  li x15, 0x0
                  li x16, 0xff7811b4
                  li x17, 0xf61163af
                  li x18, 0x0
                  li x19, 0x0
                  li x20, 0x0
                  li x21, 0xc552e854
                  li x22, 0xf3ae47cd
                  li x23, 0xc356d985
                  li x24, 0x0
                  li x25, 0x80000000
                  li x26, 0xaad8efdc
                  li x27, 0xffa38c28
                  li x28, 0xf915a8c7
                  li x29, 0x9
                  li x30, 0x5
                  li x31, 0x5912efde
                  li x4, 0x40001104
                  csrw misa, x4
kernel_sp:        
                  la x24, _kernel_stack_end

trap_vec_init:    
                  la x4, mtvec_handler
                  ori x4, x4, 0
                  csrw 0x305, x4 # MTVEC

mepc_setup:       
                  la x4, _init
                  csrw mepc, x4
                  j init_machine_mode

_init:            
                  la x2, _user_stack_end
_main:            la         s1, region_2+5617 #start riscv_load_store_rand_instr_stream_9
                  sb         s5, 64(s1)
                  div        s2, a2, t4
                  andi       a2, t6, -398
                  or         a3, a0, ra
                  lb         t0, 174(s1)
                  sltiu      s6, a3, -222
                  c.add      t5, t3
                  csrrs      t3, 0x340, s2
                  csrrc      a4, 0x340, s9
                  addi       t4, a3, 802
                  c.srli     a5, 5
                  divu       s0, s0, t6
                  lb         a7, -148(s1)
                  slli       zero, zero, 23
                  mul        s6, t6, t2
                  mulh       a2, s10, s7
                  lb         t5, 88(s1)
                  andi       s2, a5, 363
                  csrrs      s10, 0x340, s11
                  addi       a5, t3, -80
                  mulh       t6, t3, s0
                  divu       s7, s3, a5
                  lb         tp, -56(s1)
                  lbu        s6, -121(s1)
                  sb         s10, 152(s1)
                  lb         a6, 96(s1)
                  csrrc      t3, 0x340, zero
                  c.lui      a0, 20
                  c.andi     a3, -13
                  c.and      s0, a2
                  csrrci     t3, 0x340, 29
                  and        t3, s6, t5
                  sb         s4, -178(s1)
                  c.slli     s5, 27
                  xori       t3, t5, -788
                  c.mv       a2, t1
                  sb         s4, 164(s1) #end riscv_load_store_rand_instr_stream_9
                  la         t3, region_3+468 #start riscv_hazard_instr_stream_7
                  sb         zero, -29(t3)
                  lbu        s11, -7(t3)
                  c.lui      s7, 31
                  lb         zero, 16(t3)
                  sh         s0, -34(t3)
                  lbu        a1, 25(t3)
                  srai       s11, s0, 24
                  lw         a1, -20(t3)
                  csrrw      a1, 0x340, s7
                  sb         s11, -53(t3)
                  csrrsi     s11, 0x340, 8
                  lb         s0, -63(t3)
                  srl        s7, s0, a4
                  c.srai     s0, 13
                  c.sub      s0, a4
                  lbu        zero, 21(t3)
                  sw         s0, 40(t3)
                  xor        s11, s11, s7
                  lhu        s11, -12(t3)
                  lbu        a1, 25(t3)
                  lh         a4, -64(t3)
                  or         a4, a1, zero
                  lbu        s11, 25(t3)
                  lb         a1, -16(t3)
                  lbu        a4, 42(t3)
                  lbu        s7, -60(t3)
                  lb         zero, -63(t3)
                  lb         a4, -47(t3)
                  sb         s7, -54(t3)
                  lhu        s7, -60(t3)
                  sb         a4, 7(t3)
                  lbu        s11, -35(t3)
                  xori       s7, s11, 785
                  sb         s0, -49(t3)
                  lb         zero, 17(t3)
                  lbu        s11, 17(t3)
                  lb         zero, -25(t3)
                  lb         zero, 3(t3)
                  lbu        s7, 9(t3)
                  lb         s7, 30(t3) #end riscv_hazard_instr_stream_7
                  la         a1, region_2+6211 #start load_store_instr_stream_0
                  la         t1, region_0+2527 #start load_store_instr_stream_2
                  la         s10, region_1+10809 #start load_store_instr_stream_1
                  sh         a0, -3(s10)
                  lb         zero, -2(s10)
                  lbu        s4, -39(a1)
                  sw         s3, -163(t1)
                  lw         s3, -193(s10)
                  lh         a0, -189(t1)
                  lh         t0, 173(s10)
                  lbu        s1, 1(t1)
                  lb         a0, 46(s10)
                  sb         s11, 16(t1)
                  lhu        a5, -37(a1)
                  lb         s0, 59(a1)
                  sb         a3, -137(t1)
                  sb         s9, 83(t1) #end load_store_instr_stream_2
                  lhu        t0, -135(s10)
                  lb         s3, 31(a1)
                  lh         s4, 41(a1)
                  lhu        s1, -9(s10)
                  lbu        t0, -111(s10)
                  sb         s4, 24(s10) #end load_store_instr_stream_1
                  lb         s4, 55(a1) #end load_store_instr_stream_0
                  la         a5, region_4+3214 #start load_store_instr_stream_0
                  lhu        s0, 162(a5)
                  la         t5, region_1+10813 #start load_store_instr_stream_1
                  lbu        tp, 193(a5)
                  sh         s7, -917(t5)
                  lb         t4, 86(t5)
                  lbu        t1, -20(a5)
                  lh         s1, -184(a5)
                  sb         t2, -753(t5)
                  sb         t1, 234(a5)
                  sb         t1, 17(a5)
                  lb         s6, -296(t5)
                  lbu        a2, -159(a5)
                  sb         t4, -906(t5)
                  lhu        gp, 265(t5) #end load_store_instr_stream_1
                  lbu        t0, 63(a5)
                  lb         zero, 115(a5) #end load_store_instr_stream_0
                  la         a5, region_3+329 #start riscv_hazard_instr_stream_11
                  xor        s7, tp, s3
                  mul        t2, s7, s3
                  sb         t2, -255(a5)
                  lbu        s7, -157(a5)
                  lb         t2, -285(a5)
                  ori        s7, s3, -404
                  lbu        gp, -228(a5)
                  slti       t2, s7, 372
                  sw         t2, 95(a5)
                  lb         s7, 52(a5)
                  c.andi     a4, 0
                  xor        tp, gp, s3
                  sb         tp, 34(a5)
                  sh         gp, -5(a5)
                  lh         tp, 49(a5)
                  lb         s3, -242(a5)
                  lui        s3, 893729
                  mul        s7, tp, tp
                  slti       tp, t2, 743
                  lw         s3, -85(a5)
                  lbu        tp, -208(a5)
                  lb         s7, -36(a5)
                  sub        s7, a4, gp
                  lb         s7, -146(a5)
                  auipc      s7, 957020
                  c.li       s7, 12
                  mul        s7, t2, s3
                  sub        s3, a4, a4
                  lbu        t2, -125(a5)
                  sb         s7, 116(a5)
                  sh         tp, -135(a5)
                  c.li       a4, 21
                  slt        s7, gp, t2
                  sb         t2, -24(a5)
                  c.xor      a4, a4
                  lh         gp, -135(a5)
                  lb         tp, -173(a5)
                  .4byte 0x00100073 # ebreak
                  lhu        tp, 181(a5)
                  slti       tp, gp, -96
                  lhu        s3, -217(a5)
                  mulhsu     tp, gp, a4
                  lb         t2, -96(a5) #end riscv_hazard_instr_stream_11
                  la         s10, region_3+266 #start riscv_hazard_instr_stream_5
                  lui        s1, 886275
                  sll        t2, a5, a7
                  c.xor      s1, s1
                  c.xor      a5, s1
                  srl        a7, s6, s1
                  c.add      s2, s1
                  lb         t2, -234(s10)
                  csrrci     a5, 0x340, 14
                  lw         t2, 14(s10)
                  sb         s1, -249(s10)
                  lb         a7, 73(s10)
                  slti       a5, s2, -62
                  c.mv       s6, a7
                  lw         a5, -162(s10)
                  lb         a5, -48(s10)
                  lbu        a7, 201(s10)
                  lui        s1, 444853
                  lbu        s6, -210(s10)
                  sltu       s2, t2, s6
                  c.mv       a5, s2
                  slti       a5, s1, -643
                  or         s1, s2, s6
                  lbu        s6, -135(s10)
                  rem        s1, s1, a5
                  csrrsi     s2, 0x340, 8
                  auipc      s1, 518882
                  lbu        s1, -246(s10)
                  c.sub      a5, a5
                  c.slli     t2, 6
                  sw         s6, -226(s10)
                  c.srai     a5, 2
                  csrrw      t2, 0x340, s2
                  lui        s1, 170373
                  xori       a7, s1, -806
                  lbu        a7, 239(s10) #end riscv_hazard_instr_stream_5
                  la         a5, region_1+2555 #start riscv_hazard_instr_stream_2
                  .4byte 0x00100073 # ebreak
                  lb         t1, 932(a5)
                  srli       t1, t0, 27
                  lhu        a1, -481(a5)
                  lbu        t1, 391(a5)
                  c.slli     t0, 31
                  sh         a3, -639(a5)
                  slli       t3, s4, 24
                  c.sub      a1, a3
                  sb         t3, -542(a5)
                  csrrci     a3, 0x340, 5
                  csrrwi     s4, 0x340, 14
                  add        t1, a3, t0
                  lb         a1, 86(a5)
                  mulhu      t3, t1, s4
                  xori       a1, a3, 416
                  c.srai     a3, 22
                  mulhsu     t3, a1, a3
                  c.add      t3, t1
                  sb         s4, -975(a5)
                  sltu       s4, a1, t0
                  div        t1, s4, t0
                  c.slli     t0, 1
                  sb         t1, -174(a5)
                  add        t0, t1, a1
                  lb         s4, 302(a5)
                  lh         s4, -997(a5)
                  divu       t0, a3, t0
                  ori        a1, t3, 689
                  lb         t1, 782(a5)
                  lh         t3, 29(a5)
                  xori       s4, s4, 662
                  srli       t0, t3, 17
                  lh         a3, 637(a5)
                  mulh       t0, s4, s4
                  lb         a3, -355(a5) #end riscv_hazard_instr_stream_2
                  la         t3, region_0+1354 #start riscv_hazard_instr_stream_10
                  c.sub      a1, a0
                  rem        t5, a1, t5
                  sh         s10, 72(t3)
                  lb         a7, 83(t3)
                  c.slli     a0, 11
                  lui        t5, 903409
                  sb         s7, -213(t3)
                  c.or       a0, a1
                  lbu        a7, 79(t3)
                  sh         a7, 74(t3)
                  sub        s7, a0, a7
                  lb         a7, 81(t3)
                  sb         t5, -5(t3)
                  addi       a0, s7, 226
                  lw         a0, -130(t3)
                  csrrci     s7, 0x340, 13
                  sb         s10, 37(t3)
                  sb         s10, -57(t3)
                  csrrw      a1, 0x340, s7
                  csrrw      s7, 0x340, s10
                  slli       a0, a7, 9
                  sb         s10, -143(t3)
                  csrrs      t5, 0x340, t5
                  lhu        a0, -218(t3)
                  c.or       a0, a1
                  lw         a0, -2(t3)
                  div        t5, s7, a7
                  lw         a7, 206(t3)
                  lbu        a0, 148(t3)
                  lb         a1, 161(t3)
                  addi       t5, a7, -704
                  lw         t5, 42(t3)
                  sh         s7, 76(t3)
                  lb         t5, 3(t3)
                  lbu        t5, -231(t3)
                  lb         s10, 59(t3)
                  sb         s7, -186(t3)
                  sll        s7, s10, s10
                  sb         s7, -44(t3)
                  srl        a0, a1, s10
                  sb         s7, -13(t3)
                  sh         a7, 88(t3)
                  c.addi     a0, -25
                  xor        s10, a1, t5
                  lbu        a1, -23(t3)
                  c.slli     s7, 30
                  sub        s7, s7, a7
                  c.nop
                  sh         s7, 16(t3)
                  c.andi     a1, -19
                  sb         t5, 1(t3)
                  c.srli     a1, 9
                  or         t5, a1, a0
                  lb         a1, 226(t3) #end riscv_hazard_instr_stream_10
                  la         s4, region_2+4179 #start load_store_instr_stream_0
                  la         t3, region_2+4157 #start load_store_instr_stream_2
                  la         t5, region_2+1993 #start load_store_instr_stream_3
                  la         s0, region_2+3803 #start load_store_instr_stream_4
                  la         a0, region_2+5855 #start load_store_instr_stream_1
                  lh         s3, 57(s4)
                  sh         s6, -29(t5)
                  sb         s1, -246(t3)
                  sb         t0, 75(a0)
                  lb         s2, 600(s0)
                  lh         gp, -55(s4)
                  lb         s3, 494(s0)
                  sb         s9, -116(a0)
                  sb         t3, 309(t3)
                  lh         a2, 39(s0)
                  lb         a4, -57(s4)
                  sh         s0, -37(s4)
                  sw         s10, -137(t5)
                  lbu        s10, 28(s4)
                  sb         a2, 210(t5)
                  lb         a6, 302(s0)
                  lbu        s1, -696(t3)
                  sb         s2, -182(t5)
                  lw         t4, 125(a0)
                  lbu        a5, 141(t5)
                  lh         s1, 199(a0)
                  lh         t6, 63(s4)
                  lb         s7, -141(t5)
                  lb         gp, -236(t5)
                  sb         t1, -824(t3)
                  sb         s7, -79(a0)
                  sb         s4, 71(t5)
                  lhu        s3, 767(t3)
                  lbu        a6, -49(a0)
                  lhu        ra, 43(s4)
                  lbu        t6, -94(a0)
                  sb         ra, -3(t5)
                  sb         a7, -30(s4)
                  sw         t4, 57(a0)
                  lbu        s11, 167(t3)
                  sh         s2, 321(t3) #end load_store_instr_stream_2
                  lbu        gp, -140(a0) #end load_store_instr_stream_1
                  sh         s10, -63(s4)
                  lb         s3, -278(s0)
                  lhu        s6, -1(t5) #end load_store_instr_stream_3
                  lh         a3, 435(s0)
                  lb         a3, -944(s0)
                  lbu        s2, 560(s0) #end load_store_instr_stream_4
                  lbu        t0, -56(s4) #end load_store_instr_stream_0
                  la         a0, region_1+2305 #start riscv_load_store_rand_instr_stream_10
                  lui        s6, 564656
                  lb         zero, 53(a0)
                  ori        a3, t3, -858
                  lb         a7, -35(a0)
                  lbu        a6, 10(a0)
                  sb         s10, -46(a0)
                  addi       gp, gp, -721
                  slli       s11, ra, 3
                  add        a3, s10, t0
                  lui        s3, 716353
                  csrrc      s1, 0x340, s5
                  lb         a3, -22(a0)
                  sb         sp, -12(a0)
                  srl        a1, t0, s0
                  lb         a7, 38(a0)
                  nop
                  slti       s5, s2, 623
                  sltu       s5, s10, t6
                  csrrwi     tp, 0x340, 20
                  auipc      zero, 769520
                  csrrw      s1, 0x340, s2
                  slti       s0, s3, 550
                  sb         t0, 62(a0)
                  lbu        ra, -49(a0)
                  nop
                  csrrci     zero, 0x340, 17
                  lb         s2, 63(a0)
                  mulh       t4, s0, a2
                  lb         a3, 36(a0)
                  or         t6, a4, s0
                  or         a3, tp, s11
                  lh         gp, -23(a0)
                  sltiu      s1, s9, 414
                  c.nop
                  lb         s3, -38(a0)
                  sb         zero, -34(a0)
                  slt        s7, sp, ra
                  sltiu      s1, a4, 737
                  lbu        a6, -10(a0)
                  mulhu      s1, t1, s1
                  csrrw      s5, 0x340, t3
                  mulh       a7, tp, s4
                  srai       tp, s3, 17
                  sb         s5, 44(a0)
                  sltu       t6, a7, a7
                  lb         s7, -41(a0) #end riscv_load_store_rand_instr_stream_10
                  addi       t3, zero, 10 #init loop 0 counter
                  remu       s1, s7, t6
                  addi       a3, zero, 10 #init loop 0 limit
main_50_0_t:      xor        s7, zero, t3
                  slt        tp, s10, t1
                  addi       t3, t3, -2 #update loop 0 counter
                  mulh       t6, t4, s2
                  bge        t3, a3, main_50_0_t #branch for loop 0
                  c.xor      a2, a5
                  la         a2, region_4+2940 #start riscv_hazard_instr_stream_3
                  sb         a1, -10(a2)
                  c.ebreak;c.nop;
                  lhu        s2, 2(a2)
                  mulhu      a1, s2, t5
                  lui        s2, 901457
                  and        t6, t5, a5
                  sb         a1, 1(a2)
                  lb         zero, 15(a2)
                  c.andi     a5, -31
                  sb         a1, 11(a2)
                  sltu       a5, t5, a5
                  sw         zero, 8(a2)
                  sb         t5, 11(a2)
                  lbu        a5, -9(a2)
                  sb         t6, 9(a2)
                  slti       t5, s2, 331
                  .4byte 0x00100073 # ebreak
                  csrrsi     a5, 0x340, 20
                  c.lw       a5, 4(a2)
                  sb         a1, -13(a2)
                  mul        s2, s2, t5
                  c.and      a5, a1
                  lbu        s2, 9(a2)
                  lbu        zero, 14(a2)
                  lhu        a1, -2(a2)
                  sb         s2, -5(a2)
                  sb         s2, 16(a2)
                  lh         a5, -14(a2)
                  sw         t5, 8(a2) #end riscv_hazard_instr_stream_3
main_17:          jal        gp, 8f
0:                c.j        18f
1:                jal        gp, 14f
2:                c.jal      17f
3:                c.jal      19f
4:                c.j        12f
5:                c.jal      4b
6:                jal        ra, 10f
7:                c.jal      15f
8:                c.j        1b
9:                c.jal      3b
10:               jal        gp, 2b
11:               jal        ra, 7b
12:               jal        ra, 0b
13:               c.j        20f
14:               c.j        13b
15:               jal        t1, 9b
16:               c.jal      5b
17:               c.jal      11b
18:               jal        ra, 6b
19:               c.j        21f
20:               c.jal      16b
21:               div        a7, a3, s3
                  la         t2, region_4+1075 #start load_store_instr_stream_2
                  la         gp, region_1+6840 #start load_store_instr_stream_0
                  lbu        s2, 34(gp)
                  la         s0, region_2+5224 #start load_store_instr_stream_1
                  sh         s5, 26(s0)
                  lhu        s1, -46(gp)
                  lbu        a0, -51(gp)
                  lbu        s2, -12(t2)
                  lw         t0, -3(t2)
                  sb         s5, -27(s0)
                  sb         s0, 0(t2)
                  lb         s7, -11(t2)
                  lh         t0, 12(s0)
                  lhu        s4, -5(t2)
                  sb         gp, -8(gp)
                  sb         ra, 9(t2)
                  sb         s3, -21(s0)
                  lbu        t6, -7(s0) #end load_store_instr_stream_1
                  sb         a7, -12(t2)
                  sh         s7, 5(t2)
                  sb         a6, -59(gp)
                  lb         zero, 0(t2)
                  lhu        a6, -60(gp)
                  lb         a7, 41(gp)
                  sb         t2, -7(t2) #end load_store_instr_stream_2
                  lbu        s5, 33(gp)
                  lb         t3, 29(gp) #end load_store_instr_stream_0
                  la         s0, region_3+27 #start riscv_hazard_instr_stream_6
                  lbu        a0, 2(s0)
                  lhu        a4, 5(s0)
                  sll        s6, t1, t1
                  lh         a3, 9(s0)
                  sb         s6, 10(s0)
                  sb         a3, -8(s0)
                  sw         a4, -15(s0)
                  lhu        a4, -7(s0)
                  sw         a0, 5(s0)
                  slt        a0, a3, a0
                  lb         t1, 10(s0)
                  lbu        s7, 0(s0)
                  lhu        a0, -1(s0)
                  lbu        a0, 12(s0)
                  lbu        s7, 4(s0)
                  mulhu      a0, s7, a4
                  lhu        a0, 9(s0)
                  lbu        t1, 4(s0)
                  and        s6, a0, t1
                  sb         a0, 0(s0)
                  sltiu      s6, s6, 1002
                  lbu        s7, -11(s0)
                  sw         a4, 9(s0)
                  c.slli     a0, 3
                  lbu        a3, 2(s0)
                  c.lui      t1, 18
                  mulhsu     a3, s7, a3
                  lhu        a4, -7(s0)
                  lhu        a0, -7(s0)
                  lh         s6, -3(s0)
                  lb         a4, -2(s0)
                  lb         a4, -12(s0)
                  div        a0, s6, s7
                  sb         a0, -8(s0)
                  sh         s6, -13(s0)
                  lb         s6, 10(s0)
                  sb         t1, 6(s0)
                  div        s7, a0, a3
                  sb         s7, 14(s0) #end riscv_hazard_instr_stream_6
                  la         s6, region_0+3981 #start load_store_instr_stream_2
                  la         t3, region_0+805 #start load_store_instr_stream_1
                  lh         a1, 3(t3)
                  lbu        a5, -84(s6)
                  la         s11, region_0+2587 #start load_store_instr_stream_3
                  lbu        t1, 2(s11)
                  lbu        a0, 14(t3)
                  lbu        t1, -13(s11)
                  sb         s3, -6(s11)
                  lh         a7, 77(s6)
                  lbu        a5, 46(s6)
                  la         s5, region_0+589 #start load_store_instr_stream_0
                  sb         s11, 148(t3)
                  lbu        a1, -110(s6)
                  lh         a1, 1(s5)
                  lbu        gp, -127(s6)
                  lh         t0, -137(t3)
                  lbu        s3, -194(t3)
                  lb         a3, 13(s5)
                  lb         a6, 6(s6)
                  lb         s3, 23(t3)
                  lbu        t0, -114(s6)
                  lw         s4, -253(t3)
                  lb         ra, 14(s6)
                  lbu        t4, 8(s5)
                  lw         a7, -9(s6) #end load_store_instr_stream_2
                  lbu        s0, 202(t3)
                  lbu        tp, -2(s11)
                  lbu        t0, -9(s5)
                  lb         a7, 193(t3)
                  lbu        s1, -164(t3) #end load_store_instr_stream_1
                  lbu        s0, -15(s5)
                  lb         t1, 8(s11) #end load_store_instr_stream_3
                  lbu        a0, 4(s5) #end load_store_instr_stream_0
                  la         a2, region_0+2360 #start load_store_instr_stream_1
                  la         a5, region_0+1901 #start load_store_instr_stream_2
                  lh         s1, 6(a2)
                  lbu        gp, -5(a5)
                  la         s2, region_0+3225 #start load_store_instr_stream_3
                  la         s6, region_0+55 #start load_store_instr_stream_4
                  lb         t3, -46(s2)
                  la         s11, region_0+121 #start load_store_instr_stream_0
                  lbu        s0, -13(a5)
                  lbu        a0, -54(s6)
                  lhu        s5, 9(s11)
                  lbu        t6, 6(a2)
                  lbu        gp, -2(a5)
                  sh         a1, -29(s6)
                  lb         s10, -11(s11)
                  lb         t2, -8(s6)
                  lhu        t2, 12(a2)
                  sh         a5, -37(s6)
                  lh         t1, -3(s2)
                  sw         t3, 11(a5)
                  lw         t0, 21(s6)
                  lb         s3, 30(s2)
                  lb         a0, 12(s11)
                  lb         a3, 14(s2)
                  lbu        t5, -16(a5)
                  lhu        gp, -33(s6)
                  lbu        tp, 50(s2)
                  sb         s7, -10(s6)
                  lbu        t5, -11(a5)
                  lbu        s4, -4(a5)
                  sb         zero, -54(s2)
                  lb         t4, 0(a2)
                  lb         s5, -6(s2)
                  lb         a6, 14(s11)
                  lh         s5, 10(a2) #end load_store_instr_stream_1
                  sb         gp, -3(a5)
                  lbu        s1, 0(s6)
                  sb         t3, -7(s2) #end load_store_instr_stream_3
                  sh         tp, -3(a5)
                  sb         t6, 1(s11)
                  sb         s2, 50(s6)
                  sw         s8, -1(a5) #end load_store_instr_stream_2
                  lh         ra, -43(s6) #end load_store_instr_stream_4
                  lbu        t2, 8(s11) #end load_store_instr_stream_0
main_21:          jal        gp, 19f
0:                jal        ra, 3f
1:                c.j        7f
2:                jal        t1, 1b
3:                jal        ra, 11f
4:                jal        t1, 9f
5:                c.jal      21f
6:                jal        s11, 10f
7:                c.j        14f
8:                jal        ra, 4b
9:                c.j        23f
10:               jal        t2, 15f
11:               c.jal      2b
12:               c.jal      6b
13:               jal        gp, 18f
14:               c.jal      16f
15:               c.j        0b
16:               c.jal      22f
17:               c.j        20f
18:               jal        s3, 8b
19:               c.j        5b
20:               jal        ra, 12b
21:               jal        t1, 17b
22:               c.jal      13b
23:               mulh       t5, a6, sp
                  la         s3, region_1+4597 #start load_store_instr_stream_0
                  sb         s5, -48(s3)
                  la         t4, region_0+816 #start load_store_instr_stream_1
                  lb         s4, 54(s3)
                  sb         ra, -237(t4)
                  lhu        t3, -31(s3)
                  sw         a2, 56(t4)
                  lbu        a5, -20(s3)
                  lb         s6, 8(s3)
                  sb         tp, 119(t4)
                  lbu        s7, -24(s3)
                  sh         a4, 27(s3)
                  lhu        a5, -174(t4)
                  lbu        t2, -61(s3)
                  lhu        t0, -256(t4) #end load_store_instr_stream_1
                  lbu        t6, -3(s3) #end load_store_instr_stream_0
                  la         t6, region_4+3054 #start load_store_instr_stream_0
                  la         s7, region_1+16141 #start load_store_instr_stream_1
                  la         tp, region_3+374 #start load_store_instr_stream_2
                  lb         a0, 62(t6)
                  lh         s5, 614(t6)
                  lbu        a6, -973(t6)
                  sb         s6, 16(tp)
                  lb         s6, -3(s7)
                  lh         ra, 44(tp)
                  lb         s3, 99(t6)
                  lbu        zero, 16(s7)
                  lhu        a5, 20(tp)
                  sb         s7, 4(s7)
                  sh         t5, -32(tp)
                  lb         ra, -153(t6)
                  lhu        a6, 7(s7)
                  sb         t4, -4(s7)
                  lhu        s1, 1(s7)
                  sb         zero, -61(tp)
                  sb         a5, 941(t6)
                  lbu        s6, -24(tp)
                  lw         s11, -1(s7)
                  lbu        s4, 13(tp)
                  lbu        a0, 381(t6)
                  lb         a3, 2(s7)
                  lb         s10, -14(s7)
                  lbu        s5, 34(tp)
                  lbu        t2, 25(tp) #end load_store_instr_stream_2
                  lb         s5, 10(s7) #end load_store_instr_stream_1
                  lb         a6, 897(t6) #end load_store_instr_stream_0
main_23:          jal        gp, 7f
0:                jal        ra, 2f
1:                jal        ra, 28f
2:                c.j        23f
3:                c.jal      16f
4:                c.jal      6f
5:                jal        t1, 14f
6:                jal        ra, 22f
7:                c.j        27f
8:                c.jal      13f
9:                c.j        0b
10:               c.j        25f
11:               jal        t1, 8b
12:               c.jal      21f
13:               c.j        10b
14:               jal        s11, 1b
15:               c.jal      26f
16:               jal        t1, 9b
17:               c.jal      24f
18:               jal        ra, 11b
19:               jal        ra, 3b
20:               jal        t1, 5b
21:               jal        a0, 20b
22:               jal        t1, 12b
23:               jal        ra, 18b
24:               jal        tp, 4b
25:               jal        ra, 17b
26:               c.jal      19b
27:               c.j        15b
28:               divu       s7, t5, s11
main_12:          jal        gp, 9f
0:                jal        s5, 12f
1:                c.j        3f
2:                jal        ra, 6f
3:                c.jal      15f
4:                jal        s4, 17f
5:                jal        t1, 21f
6:                c.j        4b
7:                c.jal      1b
8:                jal        ra, 11f
9:                c.jal      8b
10:               jal        ra, 2b
11:               jal        t1, 0b
12:               c.jal      16f
13:               jal        ra, 14f
14:               c.j        22f
15:               jal        tp, 19f
16:               c.jal      5b
17:               jal        ra, 18f
18:               jal        t1, 20f
19:               jal        t1, 10b
20:               c.jal      13b
21:               c.j        7b
22:               csrrwi     s1, 0x340, 2
                  la         a7, region_1+6463 #start load_store_instr_stream_1
                  la         t5, region_2+5260 #start load_store_instr_stream_2
                  lbu        s3, -3(t5)
                  sb         t6, -49(a7)
                  sb         s3, -44(a7)
                  sb         gp, -28(a7)
                  la         s0, region_4+3392 #start load_store_instr_stream_0
                  lbu        t6, -7(t5)
                  lb         a5, -15(t5)
                  lbu        a4, 2(a7)
                  lbu        s7, -175(s0)
                  sw         t1, -12(t5)
                  lb         s5, 45(a7)
                  lbu        s4, -11(t5)
                  lh         tp, 15(a7)
                  sw         a7, -35(a7)
                  lb         t0, -245(s0)
                  lb         s3, 11(t5) #end load_store_instr_stream_2
                  lbu        s1, 168(s0)
                  lbu        a1, 137(s0)
                  lbu        a5, -61(a7)
                  sh         s8, 13(a7)
                  lb         s4, 33(a7) #end load_store_instr_stream_1
                  lhu        s11, 202(s0) #end load_store_instr_stream_0
                  la         a0, region_4+469 #start load_store_instr_stream_2
                  la         t1, region_4+959 #start load_store_instr_stream_1
                  la         s5, region_4+3010 #start load_store_instr_stream_0
                  lb         gp, -91(a0)
                  lb         t2, 31(t1)
                  sb         t2, -3(s5)
                  lb         s11, -5(s5)
                  lbu        a5, 56(t1)
                  sb         a5, 5(s5)
                  sb         a1, -9(s5)
                  sb         s0, -134(a0)
                  lbu        s7, 42(t1)
                  sb         tp, -106(a0)
                  lhu        t2, 16(s5)
                  sw         zero, -43(t1)
                  lb         t2, 28(t1)
                  sb         t4, 120(a0)
                  sh         s6, -175(a0)
                  sw         zero, 75(a0) #end load_store_instr_stream_2
                  sh         a7, -17(t1)
                  lbu        a2, -15(s5)
                  lw         zero, -63(t1) #end load_store_instr_stream_1
                  lbu        ra, -16(s5) #end load_store_instr_stream_0
                  la         ra, region_0+1926 #start load_store_instr_stream_3
                  la         s6, region_0+3511 #start load_store_instr_stream_1
                  la         a1, region_0+3106 #start load_store_instr_stream_2
                  lb         a5, 40(s6)
                  la         s11, region_0+153 #start load_store_instr_stream_0
                  lbu        a3, -21(s6)
                  sb         t2, -18(s6)
                  sw         s5, -27(s6)
                  sb         t5, -49(ra)
                  sb         tp, -50(s11)
                  lh         gp, 5(s11)
                  lbu        t0, -135(ra)
                  sb         a3, -9(a1)
                  lb         t4, -42(s11)
                  lbu        a4, -48(s6)
                  lbu        a0, -9(a1)
                  lb         s0, -88(ra)
                  lw         t5, 138(ra)
                  lbu        t1, -43(s11)
                  lb         tp, 11(a1)
                  lb         a5, -60(s6)
                  sb         a6, 13(a1)
                  lhu        a6, -14(a1)
                  sb         ra, 20(s6)
                  lbu        a3, -31(ra) #end load_store_instr_stream_3
                  sb         t6, 10(a1)
                  lb         s4, 8(s6) #end load_store_instr_stream_1
                  lbu        s10, -3(a1)
                  lh         tp, -25(s11)
                  sb         s6, -45(s11)
                  sb         a1, -16(a1) #end load_store_instr_stream_2
                  lb         t1, 9(s11) #end load_store_instr_stream_0
main_14:          jal        gp, 5f
0:                c.j        4f
1:                c.j        7f
2:                jal        ra, 16f
3:                jal        ra, 17f
4:                c.j        9f
5:                c.jal      6f
6:                jal        ra, 11f
7:                jal        ra, 14f
8:                c.jal      18f
9:                jal        ra, 8b
10:               jal        a0, 2b
11:               c.jal      13f
12:               jal        ra, 15f
13:               jal        ra, 1b
14:               c.j        3b
15:               c.jal      0b
16:               c.jal      12b
17:               c.j        10b
18:               sltu       s10, s11, a2
                  la         s10, region_3+12 #start riscv_load_store_rand_instr_stream_1
                  ori        t2, s7, 971
                  c.ebreak;c.nop;
                  c.andi     a3, 9
                  sh         s4, -8(s10)
                  .4byte 0x00100073 # ebreak
                  mul        s5, s3, tp
                  or         s4, s8, s4
                  csrrw      gp, 0x340, s11
                  lb         a1, 15(s10)
                  lb         t2, 4(s10)
                  andi       s3, tp, -498
                  addi       t2, t3, -384
                  c.add      s3, s9
                  xor        s6, a6, zero
                  sll        s4, s8, a3
                  c.nop
                  slti       t3, t4, 476
                  sb         s8, -4(s10)
                  sb         tp, -6(s10)
                  rem        gp, s9, zero
                  c.nop
                  lh         s2, 8(s10)
                  srai       a5, zero, 21
                  lbu        a5, -6(s10)
                  lui        a4, 109413
                  lui        t5, 40312
                  lh         s2, -8(s10)
                  addi       a2, s9, -184
                  lui        zero, 921504
                  lh         a7, -2(s10)
                  lbu        a5, -6(s10)
                  lbu        t2, 14(s10)
                  lh         a0, -10(s10)
                  slti       s11, s8, 890
                  csrrs      s4, 0x340, a2
                  sw         t0, -8(s10)
                  rem        a3, s6, s10
                  mulhsu     a3, gp, s0
                  c.slli     s2, 20
                  sh         a6, -2(s10)
                  c.li       s2, 24
                  lb         a0, 3(s10)
                  lb         tp, -9(s10)
                  divu       a3, a4, s7
                  sb         s9, -5(s10) #end riscv_load_store_rand_instr_stream_1
                  la         s4, region_2+4149 #start riscv_hazard_instr_stream_1
                  sb         a4, 4(s4)
                  lbu        s2, -8(s4)
                  c.andi     a4, -7
                  lb         s2, -12(s4)
                  lb         a4, 7(s4)
                  c.li       s2, -27
                  sll        t6, s2, t5
                  lui        s2, 391195
                  c.addi     a4, 15
                  sb         s2, 5(s4)
                  lb         t5, 2(s4)
                  srl        s2, s2, a5
                  c.slli     t6, 5
                  lbu        s2, -7(s4)
                  csrrsi     t5, 0x340, 7
                  sh         a7, 3(s4)
                  lb         t5, -12(s4)
                  sltiu      a5, s2, -313
                  or         a7, s2, t6
                  lbu        a4, -6(s4)
                  sb         s2, -10(s4)
                  sw         a4, 3(s4)
                  lbu        a5, 6(s4)
                  c.srai     a5, 27
                  csrrci     a4, 0x340, 23
                  sb         s2, 2(s4)
                  lbu        a5, -3(s4)
                  sb         t5, -16(s4)
                  mul        a4, a7, a5
                  lbu        s2, -8(s4)
                  lh         a7, -15(s4)
                  slt        s2, s2, t5
                  sb         a4, -14(s4)
                  lb         t6, 12(s4)
                  rem        s2, a5, s2
                  mulhsu     a4, a7, t6
                  lbu        a4, -1(s4)
                  ori        s2, t5, -910
                  lb         t6, 16(s4)
                  lbu        t5, 16(s4)
                  sw         s2, -9(s4)
                  c.addi     s2, 11
                  sw         a4, 3(s4)
                  lbu        t5, 0(s4)
                  c.ebreak;c.nop;
                  slli       a4, a7, 4
                  lhu        t5, 7(s4)
                  div        t6, s2, s2
                  slli       a4, t6, 25
                  auipc      a5, 27481
                  srai       a7, t5, 16
                  nop
                  mulh       a5, a5, t6
                  sb         a5, 9(s4)
                  lbu        a5, 2(s4) #end riscv_hazard_instr_stream_1
                  la         ra, region_0+1961 #start riscv_load_store_rand_instr_stream_7
                  and        t2, a0, s3
                  c.slli     s11, 27
                  sb         tp, -52(ra)
                  sb         s1, 39(ra)
                  c.nop
                  srli       s7, tp, 7
                  lh         a2, -63(ra)
                  lb         t1, -64(ra)
                  lb         a2, -45(ra)
                  sb         s10, -53(ra)
                  lh         s7, -27(ra)
                  sb         zero, -5(ra)
                  lb         s7, -56(ra)
                  lbu        s6, -38(ra)
                  or         a1, t6, a0
                  sra        s7, s5, a0
                  csrrsi     s4, 0x340, 20
                  csrrs      s5, 0x340, s10
                  sub        a2, sp, a1
                  addi       t0, a2, 515
                  lbu        s2, -7(ra) #end riscv_load_store_rand_instr_stream_7
main_19:          jal        gp, 6f
0:                c.j        5f
1:                jal        t0, 10f
2:                c.jal      1b
3:                c.j        0b
4:                jal        ra, 8f
5:                c.j        11f
6:                c.jal      2b
7:                jal        ra, 9f
8:                c.j        12f
9:                jal        ra, 3b
10:               jal        s6, 7b
11:               c.jal      4b
12:               sltiu      t3, s1, 580
main_22:          jal        gp, 2f
0:                jal        t1, 3f
1:                jal        ra, 18f
2:                c.jal      17f
3:                c.jal      19f
4:                c.j        7f
5:                c.j        20f
6:                jal        t2, 15f
7:                c.jal      14f
8:                jal        ra, 12f
9:                jal        ra, 6b
10:               jal        ra, 16f
11:               jal        s3, 5b
12:               c.jal      1b
13:               c.j        21f
14:               jal        ra, 0b
15:               c.jal      4b
16:               jal        ra, 9b
17:               jal        t2, 11b
18:               c.jal      13b
19:               c.j        8b
20:               jal        t0, 10b
21:               mulhu      s11, a7, t4
                  la         t3, region_2+1119 #start riscv_hazard_instr_stream_4
                  mulh       a7, t1, t1
                  lbu        t1, -135(t3)
                  lbu        t1, -24(t3)
                  sw         t1, -23(t3)
                  lb         t1, 181(t3)
                  lhu        a0, 69(t3)
                  c.li       s6, 2
                  lbu        a2, 2(t3)
                  lb         t1, 247(t3)
                  or         a7, a7, a0
                  sb         s6, 190(t3)
                  c.srai     a0, 31
                  c.xor      a2, a2
                  auipc      a0, 723358
                  remu       a2, s0, a0
                  sh         s6, -91(t3)
                  xor        a7, a7, s0
                  lbu        a2, -92(t3)
                  c.srai     s0, 31
                  c.mv       s6, t1
                  lbu        s0, 140(t3)
                  c.xor      a2, s0
                  sb         s0, -160(t3)
                  srl        a7, t1, a7
                  sltu       a2, t1, a2
                  sh         s0, -181(t3) #end riscv_hazard_instr_stream_4
                  addi       t4, zero, 8 #init loop 0 counter
                  addi       a4, zero, 8 #init loop 0 limit
                  csrrs      a3, 0x340, a2
                  c.add      s7, t4
main_54_0_t:      slti       a2, s9, -609
                  addi       t4, t4, -5 #update loop 0 counter
                  sll        s2, t1, s7
                  bgeu       t4, a4, main_54_0_t #branch for loop 0
                  srli       a3, s0, 0
                  la         a0, region_2+6978 #start load_store_instr_stream_1
                  sb         s4, -889(a0)
                  la         s7, region_2+636 #start load_store_instr_stream_2
                  la         s0, region_2+6608 #start load_store_instr_stream_0
                  lh         t5, 232(s7)
                  sb         s8, 56(s7)
                  lbu        s4, -21(s0)
                  lbu        t0, -33(s0)
                  lb         t4, -31(s0)
                  lb         s11, -431(a0)
                  sh         t5, -64(s7)
                  lw         a2, -208(s7)
                  lhu        a7, 98(s7)
                  lbu        s1, -15(s0)
                  lh         s6, 206(s7)
                  lbu        ra, 289(a0)
                  lb         gp, -859(a0)
                  sb         t3, 109(s7)
                  sb         t1, 51(s0)
                  sb         s2, 95(a0)
                  lbu        a5, 595(a0)
                  lbu        t1, 39(s0)
                  sb         t5, 178(s7)
                  sb         a4, -984(a0) #end load_store_instr_stream_1
                  sb         sp, -65(s7)
                  lh         a5, 118(s7) #end load_store_instr_stream_2
                  lw         s2, -8(s0) #end load_store_instr_stream_0
                  la         t4, region_3+406 #start load_store_instr_stream_1
                  la         s3, region_0+2690 #start load_store_instr_stream_0
                  lh         zero, -32(t4)
                  la         s11, region_2+7566 #start load_store_instr_stream_2
                  lb         a4, 229(s11)
                  lbu        zero, 25(t4)
                  lbu        gp, -19(t4)
                  sh         a3, 36(s3)
                  sb         s8, 15(t4)
                  lbu        gp, 220(s11)
                  lb         zero, -44(t4)
                  lhu        t2, 186(s11)
                  lb         s0, -616(s3)
                  lbu        a0, -696(s3)
                  sb         a4, 61(t4)
                  sh         t0, 20(s11)
                  lbu        t1, 479(s3)
                  lbu        s7, -35(t4)
                  lw         t5, 62(s3)
                  sh         a4, -58(t4)
                  sb         a7, -681(s3)
                  lb         t2, 13(s11)
                  lbu        t5, 41(s11) #end load_store_instr_stream_2
                  lb         s4, -149(s3)
                  sb         s0, 39(t4)
                  sw         s1, 482(s3)
                  sb         a1, -698(s3)
                  lbu        t3, -18(t4) #end load_store_instr_stream_1
                  sb         s6, 192(s3) #end load_store_instr_stream_0
                  la         a5, region_4+3106 #start riscv_hazard_instr_stream_8
                  srai       t6, s2, 21
                  c.and      a4, a4
                  nop
                  sb         t4, 3(a5)
                  lb         a4, -8(a5)
                  remu       s2, s2, s3
                  sb         a7, -5(a5)
                  csrrw      a7, 0x340, a7
                  slli       s2, t4, 5
                  srli       a4, s3, 27
                  c.add      t6, t6
                  sh         a7, 8(a5)
                  csrrs      a4, 0x340, a7
                  remu       s2, a7, a4
                  sll        t4, t6, t4
                  lb         a4, -3(a5)
                  srli       t4, a4, 16
                  andi       s2, s3, 464
                  sw         t4, 2(a5)
                  slt        a7, t4, a7
                  sb         a7, 15(a5)
                  lb         a4, 13(a5)
                  lhu        a4, 4(a5)
                  sb         a7, -4(a5)
                  sh         a4, 0(a5)
                  lbu        s2, -11(a5)
                  c.or       a4, a4
                  lbu        t4, -9(a5)
                  sb         s3, -9(a5)
                  sb         t4, 10(a5)
                  c.li       a7, -4
                  c.add      s3, a4
                  xor        a7, s2, s2
                  lbu        a7, -4(a5)
                  sub        s3, a4, t6
                  srai       s3, a7, 29
                  .4byte 0x00100073 # ebreak
                  csrrsi     t4, 0x340, 6
                  c.and      a4, a4
                  sb         t4, 9(a5)
                  srli       t6, t6, 13
                  mulhu      s2, a7, s3
                  lb         s2, -3(a5)
                  csrrs      a7, 0x340, t4
                  c.nop
                  sb         t4, -12(a5)
                  mulhsu     s3, t4, s2
                  nop
                  c.ebreak;c.nop;
                  lb         t6, 1(a5) #end riscv_hazard_instr_stream_8
                  la         a7, region_1+13938 #start riscv_load_store_rand_instr_stream_4
                  divu       zero, t6, t1
                  lb         s11, -7(a7)
                  auipc      t3, 936229
                  lb         a4, 9(a7)
                  sb         s0, -15(a7)
                  sll        s7, s8, s0
                  lbu        gp, 7(a7)
                  .4byte 0x00100073 # ebreak
                  c.add      s4, sp
                  lbu        s10, -3(a7)
                  add        ra, a2, a0
                  lb         a4, 12(a7)
                  mulh       s10, s11, t4
                  c.addi     t5, -17
                  lb         t6, 12(a7)
                  lhu        a2, -12(a7)
                  lb         s10, -3(a7)
                  lhu        a2, 4(a7)
                  c.srli     a1, 22
                  xor        ra, zero, s6
                  lui        t6, 753310
                  csrrci     a1, 0x340, 27
                  c.srli     a0, 31
                  sb         s4, -12(a7)
                  xor        s10, s4, t4
                  lb         a4, 7(a7) #end riscv_load_store_rand_instr_stream_4
                  addi       t5, zero, -8 #init loop 0 counter
                  c.or       a1, a3
                  c.and      a0, a3
                  nop
                  addi       s6, zero, -7 #init loop 0 limit
                  xori       t0, ra, 468
                  remu       a3, a5, t3
                  remu       a6, sp, sp
                  c.nop
                  c.ebreak;c.nop;
                  csrrsi     s1, 0x340, 27
main_53_0_t:      c.slli     a0, 29
                  nop
                  c.sub      a0, a0
                  slti       s0, s9, -42
                  c.and      a4, a4
                  c.srli     a2, 15
                  nop
                  sll        s5, a6, s3
                  csrrc      t2, 0x340, s1
                  addi       t5, t5, 2 #update loop 0 counter
                  c.sub      a3, a5
                  slt        a2, t1, s6
                  blt        t5, s6, main_53_0_t #branch for loop 0
                  c.addi     a4, -21
                  addi       t4, zero, 9 #init loop 0 counter
                  lui        s3, 241177
                  mulhsu     a3, s9, a2
                  addi       s2, zero, -8 #init loop 0 limit
                  slti       a2, a4, -639
                  xori       s10, s8, 983
                  csrrc      t2, 0x340, t1
                  c.srli     s0, 6
                  c.andi     s0, -18
main_55_0_t:      c.andi     s0, 23
                  c.srai     a5, 2
                  c.lui      a2, 25
                  or         s6, ra, s2
                  c.and      a5, a4
                  auipc      s1, 612956
                  c.slli     gp, 9
                  addi       t4, t4, -5 #update loop 0 counter
                  mulhsu     zero, s4, s9
                  c.and      a5, a3
                  lui        s4, 1036049
                  sra        zero, s8, a5
                  bge        t4, s2, main_55_0_t #branch for loop 0
                  auipc      t0, 812467
                  la         t4, region_3+501 #start riscv_load_store_rand_instr_stream_11
                  c.andi     s1, 15
                  rem        tp, a3, a1
                  divu       s0, s4, a1
                  lbu        s11, -178(t4)
                  c.srai     a2, 2
                  c.add      s4, s8
                  addi       tp, ra, -153
                  sh         s5, -219(t4)
                  lh         a3, -61(t4)
                  csrrw      t3, 0x340, s4
                  and        a6, t6, t4
                  csrrc      gp, 0x340, s9
                  lh         a7, -67(t4)
                  csrrs      s11, 0x340, s8
                  lhu        t3, -477(t4)
                  lbu        a0, -334(t4)
                  sb         s9, -177(t4)
                  lhu        s11, -407(t4)
                  lhu        zero, -181(t4)
                  sb         zero, -346(t4)
                  lh         s1, -103(t4)
                  sh         t6, -161(t4)
                  c.srai     a2, 21
                  c.li       s7, -14
                  sh         a4, -59(t4)
                  sb         t2, -297(t4)
                  lb         s1, 10(t4)
                  lhu        a4, -35(t4)
                  lbu        s1, -292(t4)
                  sh         a0, -103(t4)
                  lb         s7, -90(t4)
                  mulhu      tp, sp, s3
                  sb         s11, -36(t4)
                  sb         s11, -500(t4)
                  csrrc      ra, 0x340, t1
                  sb         a2, -304(t4)
                  lb         s7, -402(t4)
                  csrrsi     s0, 0x340, 2
                  rem        s3, s11, s8
                  sh         a0, -269(t4)
                  lh         t1, -303(t4)
                  csrrci     t1, 0x340, 28
                  mul        s5, t1, s10
                  .4byte 0x00100073 # ebreak
                  lh         t2, -221(t4)
                  lbu        t2, -264(t4) #end riscv_load_store_rand_instr_stream_11
                  la         a2, region_1+16367 #start load_store_instr_stream_1
                  la         t5, region_0+206 #start load_store_instr_stream_0
                  lbu        s11, -224(a2)
                  sb         t0, 6(a2)
                  lbu        s10, -130(a2)
                  la         a3, region_4+58 #start load_store_instr_stream_2
                  lb         a6, -632(t5)
                  sb         a7, -26(a2)
                  lw         tp, -51(a2)
                  lhu        t1, -16(a3)
                  sb         a2, 206(t5)
                  lb         tp, 21(a3)
                  sb         s2, -81(t5)
                  sb         s0, -118(a2)
                  la         s4, region_2+51 #start load_store_instr_stream_3
                  sw         tp, 181(s4)
                  lb         s1, -886(t5)
                  lbu        a6, -102(a2)
                  lb         zero, 244(s4)
                  sb         a4, -16(s4)
                  lb         t6, 63(a3)
                  sb         s7, -40(a3)
                  sh         a1, -189(a2)
                  lb         gp, 206(s4)
                  lbu        s1, 27(s4)
                  sb         s10, -248(a2) #end load_store_instr_stream_1
                  lhu        t4, 123(s4)
                  sh         t3, -40(a3)
                  lbu        a6, 236(s4) #end load_store_instr_stream_3
                  sb         s1, 515(t5)
                  sh         t3, -2(a3)
                  sb         t1, 60(a3)
                  lb         s10, 15(a3) #end load_store_instr_stream_2
                  lbu        s6, 687(t5) #end load_store_instr_stream_0
                  la         a3, region_0+2070 #start riscv_hazard_instr_stream_9
                  lbu        t6, 1(a3)
                  srli       a7, gp, 20
                  lb         gp, -7(a3)
                  lb         a5, -1(a3)
                  lbu        a1, -13(a3)
                  ori        a1, gp, 242
                  csrrwi     a7, 0x340, 24
                  mulh       a7, a1, gp
                  csrrw      a7, 0x340, s1
                  lh         a5, 4(a3)
                  lbu        s1, -13(a3)
                  csrrci     s1, 0x340, 15
                  lbu        a7, -5(a3)
                  c.mv       a7, a5
                  lb         a7, -4(a3)
                  lbu        a7, -2(a3)
                  lbu        a7, -3(a3)
                  lbu        s1, -10(a3)
                  lb         gp, 12(a3)
                  lbu        a1, 4(a3)
                  nop
                  nop
                  lb         s1, 9(a3)
                  xor        s1, a5, gp
                  mulh       a5, a7, a5
                  lbu        s1, 3(a3)
                  auipc      gp, 211427
                  lbu        gp, -6(a3) #end riscv_hazard_instr_stream_9
                  addi       tp, zero, -8 #init loop 1 counter
                  csrrs      ra, 0x340, t2
                  csrrsi     a2, 0x340, 30
                  slli       zero, a3, 16
                  .4byte 0x00100073 # ebreak
                  add        s6, a2, t2
                  c.ebreak;c.nop;
                  addi       t1, zero, 8 #init loop 1 limit
                  sll        s11, a3, a5
main_49_1_t:      csrrsi     a1, 0x340, 14
                  csrrwi     t0, 0x340, 28
                  andi       s11, tp, 775
                  srai       s11, a4, 22
                  addi       tp, tp, 9 #update loop 1 counter
                  addi       s2, zero, -8 #init loop 0 counter
                  addi       a7, zero, -15 #init loop 0 limit
                  c.mv       s3, sp
                  c.li       s5, 5
                  csrrw      t4, 0x340, t5
                  srai       a6, a4, 21
                  remu       zero, s9, a1
main_49_0_t:      csrrci     s3, 0x340, 1
                  addi       s2, s2, -6 #update loop 0 counter
                  c.mv       a2, t0
                  sltiu      s0, a2, 481
                  bge        s2, a7, main_49_0_t #branch for loop 0
                  rem        a2, s11, a5
                  bltu       tp, t1, main_49_1_t #branch for loop 1
                  srai       s10, t6, 20
                  la         s1, region_1+2219 #start load_store_instr_stream_1
                  la         t2, region_1+10841 #start load_store_instr_stream_2
                  lbu        a1, 32(t2)
                  la         gp, region_1+15168 #start load_store_instr_stream_0
                  lbu        ra, 527(gp)
                  lbu        a6, -157(s1)
                  lbu        s2, -937(gp)
                  lb         a3, -54(t2)
                  lbu        a0, -12(s1)
                  lb         s5, -82(s1)
                  lhu        a3, 41(t2)
                  lb         s4, 150(s1)
                  lb         zero, -33(t2)
                  lh         t6, 386(gp)
                  lbu        a3, -342(gp)
                  lb         s2, -41(t2) #end load_store_instr_stream_2
                  lb         tp, -26(s1)
                  lb         s4, 923(gp)
                  lbu        t4, -120(s1)
                  lb         s2, -70(s1) #end load_store_instr_stream_1
                  lb         s7, 816(gp)
                  lbu        tp, 15(gp) #end load_store_instr_stream_0
                  addi       s5, zero, 10 #init loop 1 counter
                  c.lui      s11, 19
                  addi       a6, zero, 6 #init loop 1 limit
                  sltu       a7, a6, ra
                  c.srli     a1, 30
main_56_1_t:      auipc      zero, 30332
                  addi       s5, s5, -8 #update loop 1 counter
                  c.nop
                  addi       t2, zero, 4 #init loop 0 counter
                  or         a1, t3, sp
                  c.li       t5, -18
                  c.or       a4, s0
                  addi       t6, zero, -16 #init loop 0 limit
main_56_0_t:      .4byte 0x00100073 # ebreak
                  c.ebreak;c.nop;
                  addi       t2, t2, -10 #update loop 0 counter
                  c.ebreak;c.nop;
                  c.addi     s0, -20
                  bge        t2, t6, main_56_0_t #branch for loop 0
                  lui        a4, 321774
                  bge        s5, a6, main_56_1_t #branch for loop 1
                  sltu       ra, t4, a6
main_15:          jal        gp, 16f
0:                jal        ra, 20f
1:                jal        ra, 5f
2:                c.j        10f
3:                jal        ra, 7f
4:                c.j        0b
5:                jal        t4, 2b
6:                jal        a4, 19f
7:                jal        t1, 27f
8:                jal        s1, 12f
9:                c.jal      24f
10:               c.j        22f
11:               c.j        28f
12:               jal        ra, 25f
13:               jal        t1, 21f
14:               c.j        23f
15:               jal        s1, 8b
16:               c.j        4b
17:               jal        a0, 26f
18:               c.jal      14b
19:               c.jal      18b
20:               jal        t1, 13b
21:               jal        ra, 9b
22:               c.jal      11b
23:               c.j        17b
24:               jal        a2, 6b
25:               c.j        3b
26:               c.jal      15b
27:               c.j        1b
28:               srli       s10, t5, 3
                  la         a6, region_1+8955 #start riscv_load_store_rand_instr_stream_5
                  lbu        s11, -921(a6)
                  sw         a4, -411(a6)
                  lbu        t4, 338(a6)
                  sb         s0, -120(a6)
                  mulh       a2, tp, a4
                  lh         t0, 75(a6)
                  sb         t6, -16(a6)
                  lbu        zero, 418(a6)
                  remu       t6, s7, t4
                  sh         t6, 13(a6)
                  csrrci     s11, 0x340, 21
                  sb         a4, -540(a6)
                  lh         s10, -755(a6)
                  lbu        a0, -260(a6)
                  sb         a4, 278(a6)
                  sw         s8, -619(a6)
                  slt        a2, t0, a6
                  csrrsi     a2, 0x340, 2
                  lbu        t0, -468(a6)
                  sb         t2, -351(a6)
                  sltiu      s10, t2, -652
                  xor        s3, a5, s2
                  sb         t3, 907(a6)
                  div        a0, s11, a4
                  sub        a5, a5, s11
                  lbu        zero, 714(a6)
                  lbu        s7, 186(a6)
                  or         t6, s0, t0
                  sb         a0, 676(a6)
                  sb         sp, -578(a6)
                  lbu        ra, 39(a6)
                  lb         t3, 578(a6)
                  lhu        tp, 831(a6)
                  sb         a3, -828(a6)
                  and        s0, t0, sp
                  c.mv       s3, t1
                  lbu        s1, 189(a6)
                  xori       s10, s1, 252
                  lbu        t2, 522(a6)
                  sb         s10, 1003(a6) #end riscv_load_store_rand_instr_stream_5
                  addi       a2, zero, -2 #init loop 0 counter
                  mulhu      tp, a4, gp
                  addi       zero, zero, 0 #init loop 0 limit
main_48_0_t:      divu       a1, s6, t3
                  csrrc      s2, 0x340, s8
                  addi       a2, a2, 2 #update loop 0 counter
                  slti       gp, s1, 766
                  c.bnez     a2, main_48_0_t #branch for loop 0
                  sltiu      t5, s11, -99
                  addi       s1, zero, 4 #init loop 0 counter
                  c.add      t5, s4
                  or         a6, a4, zero
                  sltiu      t5, t6, -837
                  or         s11, tp, s4
                  sll        a2, a4, gp
                  csrrw      t6, 0x340, s10
                  div        a1, s10, a2
                  csrrc      a3, 0x340, a6
                  c.srli     a1, 27
                  addi       s6, zero, 19 #init loop 0 limit
                  lui        s4, 47346
main_52_0_t:      addi       t6, s3, -912
                  csrrc      t3, 0x340, t4
                  divu       a0, s6, t2
                  csrrwi     t4, 0x340, 17
                  addi       s1, s1, 2 #update loop 0 counter
                  srai       s10, s9, 2
                  srai       s10, ra, 26
                  andi       zero, ra, 580
                  csrrw      gp, 0x340, s3
                  blt        s1, s6, main_52_0_t #branch for loop 0
                  c.add      a3, a3
                  la         gp, region_3+189 #start load_store_instr_stream_1
                  la         s7, region_3+59 #start load_store_instr_stream_3
                  la         tp, region_3+224 #start load_store_instr_stream_2
                  sh         t3, -33(s7)
                  lbu        s11, -51(gp)
                  lb         s0, 86(gp)
                  lb         t1, 43(s7)
                  lbu        a7, -118(gp)
                  la         s1, region_3+262 #start load_store_instr_stream_0
                  lbu        a0, 224(gp)
                  sb         s1, -129(s1)
                  sb         t3, -228(s1)
                  sh         tp, -40(tp)
                  sb         s6, -132(gp)
                  sb         zero, 46(s7)
                  lb         t2, 170(s1)
                  lb         t5, 62(s7)
                  sb         a3, -10(s7)
                  lh         a2, -3(gp)
                  sh         t6, -26(tp)
                  lbu        t3, 200(gp)
                  lb         s0, 25(tp)
                  sb         s4, -225(s1)
                  lb         a5, 59(tp)
                  sh         a3, -45(s7)
                  sb         gp, 58(s7)
                  sh         s8, 54(tp)
                  sb         t4, 48(s7)
                  sb         s8, -36(s7)
                  lb         a2, 320(gp) #end load_store_instr_stream_1
                  sw         a4, -3(s7) #end load_store_instr_stream_3
                  lbu        a5, -60(tp) #end load_store_instr_stream_2
                  sb         tp, -74(s1) #end load_store_instr_stream_0
main_16:          jal        gp, 19f
0:                jal        tp, 1f
1:                jal        ra, 3f
2:                c.jal      11f
3:                jal        a3, 14f
4:                jal        t1, 16f
5:                c.jal      13f
6:                jal        a3, 4b
7:                c.j        15f
8:                c.j        21f
9:                c.jal      10f
10:               jal        t2, 24f
11:               c.jal      17f
12:               c.j        7b
13:               jal        ra, 12b
14:               jal        ra, 2b
15:               c.jal      8b
16:               c.jal      0b
17:               jal        t1, 5b
18:               jal        ra, 23f
19:               c.jal      20f
20:               jal        t1, 22f
21:               jal        t1, 18b
22:               jal        t1, 6b
23:               c.j        9b
24:               ori        s4, s8, -101
                  la         t5, region_0+1619 #start riscv_load_store_rand_instr_stream_3
                  slti       s3, s1, 66
                  ori        t4, a0, 898
                  lhu        a5, 53(t5)
                  addi       s10, a4, -775
                  sb         a5, -24(t5)
                  lbu        a6, -60(t5)
                  lbu        t3, 19(t5)
                  sb         t3, 51(t5)
                  csrrsi     s0, 0x340, 8
                  sll        a0, a6, zero
                  sb         s6, 61(t5)
                  c.li       s5, 18
                  sb         sp, -49(t5)
                  lbu        s10, -14(t5)
                  lbu        s11, -46(t5)
                  remu       t4, sp, gp
                  sh         sp, 31(t5)
                  lbu        a6, -22(t5)
                  c.sub      a2, a4
                  sb         ra, 8(t5)
                  lh         s11, -43(t5)
                  lbu        s6, -34(t5)
                  lui        gp, 607932
                  lbu        s2, 45(t5)
                  mul        t6, a3, a6
                  rem        t4, a4, s10
                  lbu        a0, 60(t5)
                  sb         t1, 16(t5)
                  csrrsi     t0, 0x340, 20
                  rem        s2, a6, t1
                  lb         a4, -52(t5)
                  csrrc      s2, 0x340, a1
                  lbu        s7, 40(t5)
                  sh         t0, -35(t5)
                  sh         s11, -5(t5)
                  lbu        gp, 32(t5)
                  csrrwi     a3, 0x340, 9
                  c.lui      ra, 4
                  sb         s11, -34(t5)
                  mulh       gp, t5, s3
                  sra        s1, t5, a3
                  c.srai     a3, 10
                  csrrs      s2, 0x340, s4
                  sw         s5, 49(t5)
                  andi       t0, gp, 494
                  lb         s4, 4(t5)
                  lbu        t0, 54(t5)
                  c.srai     s1, 3
                  lbu        a7, 38(t5)
                  sra        a1, sp, s8
                  lbu        s3, -11(t5)
                  lb         a6, -35(t5) #end riscv_load_store_rand_instr_stream_3
                  la         s11, region_3+190 #start load_store_instr_stream_2
                  la         s2, region_4+1571 #start load_store_instr_stream_1
                  la         gp, region_0+3657 #start load_store_instr_stream_4
                  sh         a4, 62(s11)
                  lb         ra, 6(s2)
                  la         a4, region_1+8267 #start load_store_instr_stream_3
                  la         tp, region_2+2719 #start load_store_instr_stream_0
                  sb         s2, 245(gp)
                  lbu        a0, 56(s11)
                  lb         ra, 3(s2)
                  sb         t5, 47(s11)
                  lw         t0, 9(tp)
                  lb         t3, -45(a4)
                  lhu        a3, 7(s2)
                  lb         ra, -63(s11)
                  lbu        a3, -30(a4)
                  lbu        s6, 238(gp)
                  lb         s10, 6(s2)
                  lhu        s0, 215(gp)
                  sb         s2, 8(s2)
                  lbu        s7, -51(gp)
                  sb         t3, 6(tp)
                  lb         s4, 4(s2)
                  lbu        s10, -79(gp)
                  lb         t6, -1(tp)
                  lb         a0, -50(a4)
                  lbu        a1, -3(s11)
                  lw         a3, 6(s11) #end load_store_instr_stream_2
                  sb         gp, -38(a4)
                  lb         s7, 5(tp)
                  lbu        a3, -8(s2)
                  lh         s5, 215(gp) #end load_store_instr_stream_4
                  lbu        s5, 26(a4)
                  lh         s3, -1(s2)
                  lbu        s5, 7(tp)
                  lbu        a7, 16(s2)
                  lb         a5, -22(a4) #end load_store_instr_stream_3
                  lhu        a6, -9(s2) #end load_store_instr_stream_1
                  lbu        a7, -16(tp) #end load_store_instr_stream_0
main_20:          jal        gp, 9f
0:                jal        ra, 5f
1:                jal        tp, 0b
2:                c.j        8f
3:                c.jal      10f
4:                c.jal      13f
5:                c.j        4b
6:                c.j        3b
7:                c.j        12f
8:                jal        t1, 1b
9:                c.jal      11f
10:               c.j        7b
11:               c.jal      6b
12:               c.jal      2b
13:               c.nop
                  la         t1, region_3+392 #start load_store_instr_stream_4
                  la         a5, region_3+297 #start load_store_instr_stream_2
                  sb         s11, -2(a5)
                  lbu        a0, 35(t1)
                  la         s3, region_3+323 #start load_store_instr_stream_3
                  la         a2, region_3+311 #start load_store_instr_stream_0
                  lbu        a3, -64(t1)
                  lb         t6, -160(s3)
                  lbu        t4, 12(a5)
                  lb         t4, -8(a5)
                  lb         t2, -17(s3)
                  lbu        t0, -59(t1)
                  la         s4, region_3+164 #start load_store_instr_stream_1
                  sh         t3, -119(s3)
                  lbu        a0, -14(a5)
                  lbu        t6, -30(a2)
                  lb         s11, -7(s4)
                  sb         s10, 186(s3)
                  lbu        s11, 43(t1)
                  lbu        s11, 0(s4)
                  lb         s11, -3(s4)
                  lb         s6, 12(a5)
                  lb         s11, -202(s3)
                  sh         a2, -61(a2)
                  lb         s2, 30(s3)
                  sb         s1, 13(a5)
                  lb         a0, 21(a2)
                  lh         t2, 43(a2)
                  lh         t3, 3(a5)
                  lbu        a7, -64(s3)
                  sb         t1, -1(s4)
                  lh         zero, -8(s4)
                  lb         s11, -225(s3)
                  lb         t3, 0(a5) #end load_store_instr_stream_2
                  lb         a7, 126(s3)
                  lh         a1, 22(t1)
                  lbu        tp, -1(s4) #end load_store_instr_stream_1
                  sb         a6, -13(t1)
                  sb         a2, -32(a2)
                  lbu        s7, 30(t1)
                  lb         t4, -90(s3) #end load_store_instr_stream_3
                  lbu        a3, 37(a2)
                  lb         a1, 11(t1) #end load_store_instr_stream_4
                  lbu        s6, 26(a2) #end load_store_instr_stream_0
                  la         t0, region_3+81 #start riscv_load_store_rand_instr_stream_0
                  div        t2, s11, t0
                  lhu        s7, -27(t0)
                  c.nop
                  lh         s11, -43(t0)
                  csrrwi     s10, 0x340, 10
                  csrrwi     a7, 0x340, 24
                  add        a1, t0, a1
                  csrrci     t4, 0x340, 3
                  slli       s1, a0, 11
                  addi       s4, a3, -1
                  sb         sp, -29(t0)
                  xor        s7, a5, a3
                  sb         sp, 78(t0)
                  lbu        a1, 222(t0)
                  slt        t1, s5, sp
                  csrrsi     t4, 0x340, 8
                  lb         tp, 110(t0)
                  c.xor      s0, a5
                  c.andi     a4, 26
                  c.mv       t2, a0
                  c.srli     s1, 24
                  c.li       s11, 20
                  c.or       s1, s0
                  lbu        a5, -46(t0)
                  nop
                  and        t3, a3, s0
                  lbu        s1, 128(t0)
                  rem        a6, t0, a5
                  and        s5, t2, t5
                  c.ebreak;c.nop;
                  sb         s5, 148(t0)
                  csrrwi     s10, 0x340, 19
                  c.slli     s1, 2
                  sb         gp, 106(t0) #end riscv_load_store_rand_instr_stream_0
                  la         t5, region_0+2728 #start load_store_instr_stream_3
                  la         t2, region_2+4997 #start load_store_instr_stream_4
                  la         s10, region_4+1476 #start load_store_instr_stream_0
                  sh         a1, -6(t5)
                  lw         s4, 844(s10)
                  la         gp, region_3+192 #start load_store_instr_stream_1
                  lb         s7, 248(t2)
                  lb         s11, 48(gp)
                  lb         a2, 15(t5)
                  lbu        a7, 23(gp)
                  lb         s7, -2(t2)
                  la         t6, region_1+7463 #start load_store_instr_stream_2
                  lh         s6, -14(t5)
                  lbu        s6, 7(t5)
                  sb         s10, 5(t5)
                  sh         a3, -160(s10)
                  lbu        s7, 4(t5)
                  lhu        s0, 241(t2)
                  lh         a1, 8(gp)
                  lhu        s2, 16(t5)
                  sb         t2, -49(s10)
                  lb         s7, -18(t6)
                  lbu        a2, -13(t5)
                  sw         s8, 48(gp)
                  sb         s11, 188(t2)
                  lbu        t4, 3(t5)
                  lb         a0, 87(t2)
                  lbu        a3, 907(s10)
                  lbu        a7, 216(t6)
                  sb         t2, -17(gp)
                  sw         s3, -47(t6)
                  sb         a1, -1(t5) #end load_store_instr_stream_3
                  lbu        a0, -110(t2)
                  sh         a1, 766(s10)
                  lbu        tp, 232(t6)
                  lh         a6, -54(gp)
                  lbu        s11, 42(t2)
                  lbu        a3, -172(t6) #end load_store_instr_stream_2
                  sb         s1, 59(gp) #end load_store_instr_stream_1
                  lh         t1, -27(t2)
                  lh         s1, -107(t2) #end load_store_instr_stream_4
                  sb         a3, -845(s10) #end load_store_instr_stream_0
                  add        zero, s0, a4
                  c.sub      s1, s0
                  csrrwi     s6, 0x340, 25
                  lui        t1, 843362
                  c.nop
                  csrrw      a0, 0x340, s7
                  c.slli     a5, 10
main_18:          jal        gp, 5f
0:                c.jal      9f
1:                jal        ra, 10f
2:                jal        t0, 11f
3:                c.jal      7f
4:                jal        t5, 0b
5:                c.j        8f
6:                c.j        4b
7:                jal        ra, 1b
8:                jal        s4, 3b
9:                jal        ra, 2b
10:               c.j        6b
11:               jal        a4, 12f
12:               c.ebreak;c.nop;
                  divu       s6, a5, a7
                  or         a4, sp, sp
                  csrrci     a3, 0x340, 31
                  c.addi     s3, -9
                  and        a5, s8, a4
                  c.addi     s6, 3
                  xor        s5, s11, a7
                  c.ebreak;c.nop;
                  c.lui      t2, 4
                  bltu       s3, t6, 35f
                  slt        t4, a1, s6
                  c.add      a7, a0
                  c.and      a3, a0
                  mulhu      a3, a0, a4
                  auipc      s5, 332405
                  csrrci     s3, 0x340, 7
                  c.bnez     a2, 38f
                  .4byte 0x00100073 # ebreak
                  c.beqz     a3, 37f
                  sra        s2, gp, a4
                  remu       s6, s3, a7
                  srl        a5, s0, a0
                  rem        s1, a3, a4
                  csrrc      a1, 0x340, s6
                  mulhu      s6, tp, a6
                  mulhu      t6, s8, a1
                  slt        s3, t0, s4
                  nop
35:               csrrc      t3, 0x340, s1
                  srl        a1, a4, sp
37:               c.sub      a3, s0
38:               add        gp, ra, s9
                  xor        gp, sp, gp
                  auipc      s4, 46061
                  c.beqz     s1, 56f
                  andi       s5, t2, 738
                  c.srai     a3, 30
                  beq        s6, s5, 56f
                  xori       s6, s4, -951
                  blt        a2, a1, 62f
                  c.andi     a3, 5
                  mul        t6, s2, t2
                  div        s7, t2, ra
                  nop
                  c.slli     s10, 30
                  c.add      ra, s3
                  c.and      a2, s0
                  c.bnez     a0, 73f
                  csrrw      s3, 0x340, s11
56:               .4byte 0x00100073 # ebreak
                  c.add      s4, s11
                  csrrwi     gp, 0x340, 19
                  csrrw      s3, 0x340, a0
                  csrrw      s10, 0x340, s2
                  xori       t2, s10, 1014
62:               bltu       s2, t0, 63f
63:               addi       s2, sp, 845
                  srai       a3, a2, 17
                  csrrsi     s0, 0x340, 1
                  c.slli     a1, 7
                  blt        s1, gp, 82f
                  sltiu      t3, sp, -273
                  c.srai     a5, 25
                  sltu       a0, a6, t0
                  andi       gp, t4, -277
                  csrrwi     t3, 0x340, 21
73:               auipc      s7, 143689
                  mul        a7, a3, t1
                  addi       s6, t6, -397
                  mulhsu     a4, a6, a2
                  auipc      a0, 262041
                  rem        a0, s0, a4
                  c.andi     a1, -16
                  csrrwi     a4, 0x340, 12
                  ori        s7, t1, -805
82:               or         a7, a6, s8
                  c.nop
                  ori        a5, t6, -841
                  c.and      s1, a5
                  mul        t4, a4, a3
                  c.mv       ra, a6
                  c.and      s1, a1
                  c.bnez     a3, 99f
                  xor        s11, s1, s1
                  c.slli     ra, 15
                  c.or       a2, s0
                  bge        a6, s5, 112f
                  c.lui      s10, 1
                  csrrw      t6, 0x340, t3
                  blt        zero, t2, 100f
                  c.and      a1, s0
                  div        a7, s0, t2
99:               c.slli     tp, 19
100:              sub        s4, t0, a1
                  bltu       s8, t5, 114f
                  c.or       a0, a2
                  srai       s10, zero, 23
                  lui        zero, 353254
                  c.slli     a6, 8
                  c.and      a0, a4
                  c.mv       ra, a5
                  mulhu      a0, s9, gp
                  remu       s11, s0, s4
                  c.add      s6, s9
                  nop
112:              c.andi     a2, -19
                  divu       s5, a1, t2
114:              c.sub      a4, a1
                  c.bnez     a5, 120f
                  lui        s0, 993948
                  bgeu       t3, a0, 127f
                  srli       s10, t2, 21
                  bge        t4, a4, 139f
120:              srl        a0, t0, tp
                  blt        t1, s5, 137f
                  slt        t3, t6, t1
                  c.bnez     a4, 133f
                  sll        s4, a2, a6
                  csrrw      t6, 0x340, a4
                  csrrs      a4, 0x340, t2
127:              csrrs      s3, 0x340, t0
                  div        a5, a7, t0
                  csrrwi     s3, 0x340, 10
                  slt        a1, s1, a6
                  bne        t3, zero, 139f
                  sra        t4, s8, s3
133:              srli       a2, t0, 22
                  c.srli     s0, 28
                  .4byte 0x00100073 # ebreak
                  andi       s3, s1, -38
137:              c.xor      a3, s0
                  blt        t6, t5, 156f
139:              srli       tp, s10, 7
                  andi       a5, s4, 517
                  c.andi     a5, -29
                  mul        tp, a0, tp
                  lui        s2, 260708
                  c.addi     s10, 30
                  sra        a0, s2, t4
                  srli       gp, s7, 13
                  c.bnez     a5, 165f
                  mulh       s5, s10, t6
                  sltiu      a0, s11, 887
                  .4byte 0x00100073 # ebreak
                  c.bnez     a2, 160f
                  c.srai     a4, 31
                  remu       t1, a4, sp
                  rem        t2, s4, a2
                  xor        t3, s3, tp
156:              beq        ra, s2, 168f
                  rem        t3, ra, a6
                  csrrci     s6, 0x340, 18
                  c.andi     a3, 3
160:              .4byte 0x00100073 # ebreak
                  nop
                  csrrwi     a4, 0x340, 15
                  csrrc      a7, 0x340, s9
                  addi       s2, sp, -594
165:              srai       a3, gp, 29
                  c.addi     t4, 15
                  bne        ra, ra, 178f
168:              c.or       s1, a5
                  csrrs      t5, 0x340, t0
                  c.or       s1, a5
                  and        a7, s7, a4
                  sltu       t2, a5, a0
                  csrrsi     s7, 0x340, 17
                  c.li       t0, 23
                  c.bnez     a5, 183f
                  bge        t3, t6, 189f
                  c.nop
178:              xor        a4, a0, t4
                  c.xor      a4, a2
                  bne        s10, s5, 189f
                  add        a6, s11, t2
                  sub        ra, zero, a2
183:              sltu       a1, sp, t3
                  auipc      s4, 852190
                  auipc      t4, 906415
                  sub        t3, a3, t5
                  mulh       a3, t1, s8
                  lui        a7, 91376
189:              addi       zero, a0, 98
                  c.beqz     a0, 205f
                  slli       a3, zero, 20
                  xori       s10, sp, 637
                  add        a0, tp, a5
                  sll        gp, a1, s11
                  add        s2, zero, a0
                  bltu       a7, s1, 199f
                  c.srai     s0, 20
                  bne        t0, s3, 199f
199:              csrrwi     a1, 0x340, 29
                  c.srai     a3, 20
                  c.add      tp, s11
                  add        t2, t6, s10
                  csrrwi     s1, 0x340, 18
                  srai       t0, t2, 19
205:              csrrs      a5, 0x340, s11
                  rem        a5, zero, s1
                  bltu       t2, s10, 215f
                  slt        s3, a5, t4
                  srli       gp, s5, 7
                  add        gp, sp, tp
                  csrrsi     s2, 0x340, 11
                  bltu       sp, a1, 228f
                  sub        a1, s11, a5
                  and        a7, s3, a0
215:              c.srai     a1, 27
                  c.srli     a2, 5
                  srli       a3, s5, 8
                  div        t1, t5, a0
                  lui        s6, 142569
                  csrrsi     s10, 0x340, 1
                  srli       t5, t2, 0
                  csrrc      s11, 0x340, s6
                  la         t2, region_2+4999 #start load_store_instr_stream_1
                  la         t5, region_2+3602 #start load_store_instr_stream_4
                  la         s0, region_2+5185 #start load_store_instr_stream_3
                  sb         s3, 46(t2)
                  la         ra, region_2+2269 #start load_store_instr_stream_2
                  lhu        a6, 11(s0)
                  sb         tp, 8(s0)
                  la         a2, region_2+3772 #start load_store_instr_stream_0
                  lbu        s4, -58(ra)
                  sw         a5, -203(t2)
                  lhu        s10, 25(ra)
                  sb         s9, -184(t2)
                  lbu        a3, -60(ra)
                  sb         a7, 252(t2)
                  sh         s9, -15(s0)
                  sh         s1, 36(t5)
                  lb         s5, 80(t2)
                  lb         t1, -12(s0)
                  lb         s6, -7(ra)
                  sb         a1, -14(ra)
                  lhu        a7, 1(s0)
                  sb         sp, -25(t5)
                  sh         s1, -50(t5)
                  sb         zero, -14(a2)
                  lb         s5, 5(a2)
                  sb         a4, 7(t5)
                  lbu        t6, -6(ra)
                  lbu        a5, -51(ra)
                  lbu        s6, -15(a2)
                  lbu        t4, -7(s0)
                  lh         s1, -1(s0)
                  lb         s6, 17(t5)
                  sb         s4, 15(t5)
                  lb         a0, 46(ra)
                  sb         t5, 2(a2)
                  sh         ra, -63(ra)
                  lb         s4, 115(t2)
                  lbu        t6, -10(s0) #end load_store_instr_stream_3
                  lbu        gp, 220(t2)
                  sb         sp, 139(t2)
                  sb         s8, -13(t5) #end load_store_instr_stream_4
                  lb         t3, -7(a2)
                  sb         s3, -49(ra) #end load_store_instr_stream_2
                  sw         a7, 233(t2) #end load_store_instr_stream_1
                  lb         a7, 8(a2) #end load_store_instr_stream_0
                  c.or       a2, s0
                  and        t4, s5, a4
                  c.or       a2, s1
                  nop
                  srai       tp, a3, 14
228:              sltiu      t0, a5, 131
                  sra        t5, a1, t6
                  remu       a7, s11, a3
                  beq        s2, a6, 243f
                  rem        a6, a2, tp
                  xori       t6, t6, -1014
                  c.nop
                  sub        t4, s1, a3
                  c.bnez     a4, 256f
                  beq        t0, s5, 255f
                  c.nop
                  c.beqz     s0, 254f
                  slti       s11, a3, -493
                  blt        s0, t1, 250f
                  .4byte 0x00100073 # ebreak
243:              csrrs      s5, 0x340, t3
                  mul        s3, t3, t2
                  sltiu      s5, s1, -387
                  nop
                  xor        a2, s9, a6
                  auipc      t2, 262443
                  remu       s2, sp, s4
250:              csrrci     t1, 0x340, 18
                  bltu       s6, t0, 252f
252:              div        a2, a5, s9
                  blt        a2, t1, 261f
254:              c.lui      t3, 11
255:              c.xor      a1, s1
256:              mul        a1, a5, s8
                  csrrs      s7, 0x340, a1
                  nop
                  xori       tp, s8, -377
                  csrrsi     t6, 0x340, 19
261:              auipc      t1, 883809
                  addi       t4, t4, 10
                  bge        t6, s2, 276f
                  c.or       a1, a1
                  srai       a2, a0, 25
                  c.addi     s4, 29
                  mul        t2, s8, s2
                  c.mv       gp, a2
                  srli       t4, s6, 18
                  csrrci     t1, 0x340, 1
                  mulhu      t5, ra, zero
                  xor        t0, s9, s11
                  c.nop
                  bge        s1, a1, 293f
                  sll        ra, tp, ra
276:              bne        s2, s0, 286f
                  c.add      t0, s11
                  nop
                  mulhsu     s3, a5, t6
                  csrrs      a7, 0x340, t0
                  c.andi     s1, -15
                  csrrsi     a2, 0x340, 0
                  csrrs      t5, 0x340, t6
                  csrrci     t5, 0x340, 18
                  c.xor      s1, s0
286:              blt        a4, s3, 295f
                  c.addi     a5, -21
                  ori        tp, ra, -342
                  or         t4, a2, t0
                  csrrwi     s7, 0x340, 3
                  xori       a4, a5, 747
                  .4byte 0x00100073 # ebreak
293:              csrrsi     t6, 0x340, 3
                  srai       gp, t1, 17
295:              sltu       s11, tp, a7
                  slt        t1, s7, s8
                  bgeu       gp, a0, 307f
                  c.add      a1, t4
                  andi       t5, t6, -32
                  c.add      a5, a0
                  c.slli     t4, 19
                  divu       t6, tp, t2
                  mulhsu     gp, a6, a4
                  add        s1, s0, a4
                  add        gp, s8, t2
                  remu       a7, a6, s5
307:              nop
                  mul        t3, s8, a4
                  c.lui      s10, 15
                  .4byte 0x00100073 # ebreak
                  rem        s11, a4, a1
                  c.andi     a3, -29
                  srli       s1, s10, 8
                  c.li       a1, 7
                  mulh       t4, a5, s2
                  beq        a2, a7, 332f
                  and        a3, a2, a3
                  c.srai     s1, 14
                  c.mv       a4, s7
                  srl        a2, t3, sp
                  xor        tp, s3, t0
                  csrrwi     a4, 0x340, 3
                  sll        a2, s4, zero
                  c.ebreak;c.nop;
                  mulh       t6, s1, zero
                  c.and      a5, a2
                  c.addi     s4, 22
                  andi       a3, a3, -181
                  andi       t3, sp, 172
                  mul        s0, t5, t3
                  c.sub      a0, s0
332:              .4byte 0x00100073 # ebreak
                  sltu       s4, s10, s10
                  div        s11, t1, a3
                  csrrwi     zero, 0x340, 23
                  beq        s10, t5, 347f
                  csrrci     s1, 0x340, 10
                  csrrs      zero, 0x340, t5
                  c.beqz     a1, 349f
                  c.srli     a2, 7
                  c.li       ra, -20
                  csrrc      t5, 0x340, t6
                  sra        a1, gp, t6
                  c.bnez     a4, 356f
                  sra        s10, a0, s1
                  sltu       s2, a6, a1
347:              sltiu      s4, sp, 51
                  rem        s3, s8, s7
349:              c.li       s7, 4
                  c.lui      s7, 31
                  bltu       s5, t3, 366f
                  c.add      a7, t3
                  c.nop
                  csrrw      s10, 0x340, s2
                  c.li       a6, 12
356:              beq        t5, s4, 371f
                  slli       s11, sp, 1
                  c.slli     ra, 16
                  csrrwi     a1, 0x340, 22
                  srai       a6, s2, 19
                  slli       zero, s0, 20
                  lui        a4, 138441
                  blt        a2, a6, 368f
                  c.addi     a1, 21
                  or         t2, a1, s3
366:              c.bnez     a4, 367f
367:              c.beqz     a4, 371f
368:              mulhsu     a7, sp, t4
                  bge        a3, t0, 372f
                  mulh       a2, s2, s5
371:              sll        t1, a3, s3
372:              xor        zero, a0, s1
                  remu       a6, s7, t2
                  csrrci     s10, 0x340, 15
                  bge        a0, s3, 388f
                  c.addi     s3, 31
                  .4byte 0x00100073 # ebreak
                  c.add      t5, a2
                  .4byte 0x00100073 # ebreak
                  c.bnez     s1, 395f
                  c.srli     s0, 30
                  mulhu      a4, s2, s2
                  rem        s4, t3, t0
                  c.srai     a1, 22
                  c.or       a1, a4
                  c.and      s1, s0
                  slt        t6, s5, s1
388:              bgeu       a4, a6, 407f
                  ori        zero, t5, 203
                  sltiu      t0, a5, -891
                  csrrc      s7, 0x340, t3
                  c.nop
                  rem        t4, s5, s6
                  addi       a2, t1, 28
395:              slt        a4, s7, s1
                  bltu       s11, s6, 414f
                  nop
                  addi       t3, a0, 993
                  sub        a6, s3, a2
                  c.srli     a4, 24
                  csrrs      s11, 0x340, s11
                  nop
                  sltiu      t0, a2, -506
                  xor        t6, a1, s0
                  ori        s11, a5, -995
                  mulhsu     a6, a2, t5
407:              mulh       t6, a5, a3
                  sra        gp, s3, tp
                  c.srli     s1, 30
                  csrrw      s7, 0x340, s5
                  remu       ra, s6, s7
                  srl        a1, t4, a0
                  xor        t3, a7, a5
414:              auipc      a1, 385598
                  c.srai     a5, 5
                  or         s11, a6, s8
                  divu       ra, s6, a4
                  c.nop
                  mulhsu     a7, s7, s9
                  c.lui      t6, 30
                  .4byte 0x00100073 # ebreak
                  c.add      a1, s6
                  xori       ra, s5, 331
                  bge        zero, sp, 436f
                  andi       t5, ra, 593
                  c.lui      s7, 7
                  csrrc      s3, 0x340, s0
                  c.mv       a2, gp
                  or         a2, ra, a1
                  csrrwi     t1, 0x340, 19
                  bge        s11, gp, 450f
                  slt        a5, ra, s11
                  div        s4, a2, a4
                  bge        s9, a4, 449f
                  c.beqz     s1, 444f
436:              c.or       s1, a1
                  c.xor      a0, a5
                  sltu       s3, t2, s0
                  divu       a4, t5, a0
                  xor        a1, tp, a4
                  addi       ra, t4, -152
                  c.add      s7, a6
                  xori       t5, gp, -239
444:              c.mv       s4, sp
                  bgeu       s7, a1, 450f
                  mulhsu     t6, gp, ra
                  andi       a4, a2, -995
                  c.nop
449:              add        s2, s3, t0
450:              c.bnez     a3, 454f
                  mulhu      a0, s9, s1
                  addi       zero, t6, -880
                  mulhsu     t6, s11, s11
454:              nop
                  divu       t0, sp, ra
                  c.lui      t4, 16
                  slli       a6, a6, 0
                  divu       a0, s11, s1
                  c.lui      s3, 16
                  csrrsi     t5, 0x340, 13
                  csrrc      t2, 0x340, t0
                  csrrs      a6, 0x340, s6
                  csrrci     a2, 0x340, 25
                  c.srli     s1, 19
                  ori        a2, s1, 76
                  xori       s11, gp, 717
                  srli       a7, t2, 2
                  slt        s5, t3, t3
                  xori       s6, s4, -648
                  c.and      a1, a2
                  or         t3, s7, t5
                  mulhsu     s3, t3, zero
                  divu       a6, a6, a2
                  csrrc      a0, 0x340, s7
                  srli       a0, a4, 2
                  csrrwi     zero, 0x340, 28
                  csrrw      ra, 0x340, a1
                  sra        a2, t4, a1
                  mulh       t5, s11, t6
                  srai       ra, t4, 30
                  csrrc      t2, 0x340, sp
                  sra        a1, tp, zero
                  blt        a0, t0, 496f
                  beq        gp, s7, 494f
                  lui        a5, 532072
                  c.nop
                  bltu       s3, t2, 496f
                  c.mv       s10, t0
                  srli       t6, ra, 25
                  blt        t0, a3, 498f
                  c.xor      a3, a3
                  mulh       t5, t0, s0
                  c.sub      s1, s0
494:              divu       ra, s4, s9
                  csrrwi     t2, 0x340, 31
496:              div        a2, ra, zero
                  slli       a6, t3, 20
498:              beq        tp, s1, 517f
                  rem        a0, t2, t2
                  srli       s4, ra, 22
                  c.bnez     a1, 520f
                  c.li       s6, -17
                  ori        s3, s11, 881
                  mul        s6, s5, ra
                  c.or       a5, a0
                  xor        a5, t5, a2
                  bltu       a6, t6, 519f
                  mulh       a3, tp, t1
                  c.lui      a3, 26
                  srl        t1, t3, a5
                  slli       s4, s5, 13
                  slti       t5, t0, 176
                  csrrwi     ra, 0x340, 5
                  auipc      t5, 678866
                  bge        t5, t1, 535f
                  c.lui      s0, 25
517:              addi       a0, sp, 774
                  c.andi     a0, -6
519:              c.addi     t6, -5
520:              blt        t0, a2, 521f
521:              and        ra, s8, t1
                  mulh       a5, a1, a4
                  mul        t6, a0, gp
                  c.beqz     a3, 527f
                  sltiu      a3, t5, 604
                  c.lui      tp, 14
527:              sra        t0, gp, s10
                  c.sub      a0, a2
                  c.beqz     a5, 537f
                  c.add      t6, t1
                  c.beqz     a5, 543f
                  c.or       a3, s0
                  bne        gp, a0, 548f
                  slti       s11, s1, -113
535:              bgeu       s0, s8, 547f
                  blt        s7, t6, 549f
537:              csrrwi     a5, 0x340, 26
                  c.andi     a0, -11
                  sltiu      a0, sp, -649
                  sltu       a4, sp, a1
                  mul        t0, s6, s1
                  sll        t0, sp, t4
543:              andi       s2, a3, -561
                  c.srli     a0, 23
                  csrrsi     s4, 0x340, 19
                  c.add      a2, s8
547:              slt        s2, a6, s8
548:              c.li       s3, 21
549:              slli       s10, a1, 6
                  c.srli     a2, 16
                  or         a3, a7, s11
                  srli       s6, a0, 20
                  .4byte 0x00100073 # ebreak
                  mulh       a6, t4, t1
                  sub        a1, s4, a2
                  .4byte 0x00100073 # ebreak
                  slti       s5, a7, -112
                  mulhsu     s3, t4, t2
                  c.and      s1, a2
                  and        a1, a5, zero
                  add        gp, s7, s5
                  remu       s3, a3, a6
                  c.lui      s5, 28
                  srli       a2, a4, 15
                  c.and      s1, a2
                  csrrs      a3, 0x340, s0
                  addi       t1, a7, 708
                  sub        ra, sp, s9
                  divu       ra, a7, s9
                  rem        a2, a2, s7
                  mulhu      s0, ra, t4
                  bgeu       a7, tp, 590f
                  srli       a2, s8, 21
                  blt        s8, s8, 585f
                  sra        s6, t5, s9
                  divu       a6, s10, a6
                  csrrci     t6, 0x340, 18
                  c.ebreak;c.nop;
                  addi       s5, s0, 449
                  c.xor      a2, a3
                  bgeu       gp, gp, 591f
                  c.nop
                  c.srai     a3, 7
                  csrrci     s11, 0x340, 9
585:              rem        t2, t5, s10
                  slt        s4, s1, s9
                  c.addi     a7, -9
                  add        t4, a1, t1
                  slt        t2, t4, t4
590:              blt        t4, s10, 609f
591:              divu       s6, a7, s2
                  rem        s2, s10, s2
                  bge        s7, a4, 608f
                  sll        a3, sp, tp
                  c.srai     a3, 19
                  c.lui      a3, 24
                  sltiu      t1, ra, -395
                  c.li       a1, 13
                  c.lui      s6, 10
                  mulhu      gp, s0, a1
                  srai       s10, t2, 22
                  c.lui      s2, 24
                  csrrwi     s10, 0x340, 5
                  srai       s6, a2, 17
                  .4byte 0x00100073 # ebreak
                  srli       zero, gp, 20
                  sltiu      t6, sp, 90
608:              slt        s5, s7, gp
609:              and        t4, a1, a1
                  csrrw      a1, 0x340, t5
                  c.slli     a4, 25
                  c.lui      a3, 16
                  mulhu      ra, t5, a1
                  slli       a2, a3, 14
                  csrrsi     ra, 0x340, 5
                  c.ebreak;c.nop;
                  or         t5, s4, a0
                  remu       a5, ra, s0
                  srli       s7, a4, 29
                  blt        zero, s11, 635f
                  andi       a1, s7, -290
                  c.bnez     a3, 640f
                  bgeu       t2, zero, 633f
                  xori       a3, sp, 224
                  c.addi     a0, -8
                  bne        s11, s5, 642f
                  bgeu       s8, s2, 643f
                  srai       s7, s3, 11
                  mulhu      t4, a6, s4
                  rem        gp, s8, s4
                  mul        gp, s6, s6
                  beq        ra, t5, 633f
633:              bge        s7, ra, 651f
                  c.or       a1, s0
635:              c.srai     a2, 17
                  csrrw      a0, 0x340, s10
                  srl        s10, t0, a0
                  divu       s1, t4, gp
                  srli       a6, a5, 14
640:              srai       s7, s7, 20
                  c.addi     t5, 11
642:              addi       a4, a0, -172
643:              srli       s7, s8, 31
                  c.slli     ra, 7
                  bge        s2, tp, 663f
                  c.srli     a1, 12
                  c.slli     t6, 21
                  or         gp, s1, t1
                  and        gp, s6, t4
                  mul        s4, s5, s2
651:              xor        t6, s11, a2
                  srai       t4, s11, 1
                  mulhsu     t1, a0, s4
                  srl        zero, ra, t6
                  lui        t0, 123367
                  bne        s2, s1, 666f
                  sub        tp, t1, tp
                  and        t4, t2, t5
                  c.xor      s0, s1
                  c.srai     a3, 26
                  mul        t2, a4, a4
                  remu       t2, zero, t1
663:              c.andi     s1, -13
                  csrrw      t0, 0x340, s0
                  divu       a7, a3, a7
666:              sltu       a1, s6, s2
                  csrrs      t2, 0x340, gp
                  xori       a1, tp, -993
                  xori       t2, t6, 259
                  c.and      a3, a3
                  csrrc      zero, 0x340, sp
                  sub        t6, s3, s6
                  slli       s5, s8, 25
                  remu       tp, a7, t4
                  c.slli     s0, 11
                  slt        gp, s0, tp
                  slt        zero, t3, s8
                  slti       s11, gp, 292
                  c.srai     a2, 11
                  c.and      s1, s0
                  csrrwi     s5, 0x340, 26
                  mulhsu     a6, s3, a2
                  ori        ra, tp, -598
                  srli       a4, s3, 11
                  c.nop
                  and        s6, t6, s8
                  sltiu      s11, a0, 118
                  addi       s6, t5, 34
                  c.add      a6, t5
                  c.lui      a3, 1
                  bne        s10, s0, 706f
                  c.mv       gp, s0
                  auipc      t4, 641196
                  xori       s3, t0, -1008
                  srli       s4, s7, 21
                  blt        s9, a4, 716f
                  bgeu       a4, gp, 713f
                  mul        tp, s4, s7
                  sll        ra, s3, s10
                  blt        s0, ra, 715f
                  blt        a1, s5, 702f
702:              mulhsu     a4, ra, t6
                  sra        a2, s1, s9
                  div        a4, sp, s7
                  srli       t1, s0, 28
706:              c.and      a5, a5
                  slt        s3, t5, t1
                  mulhu      gp, a1, t4
                  andi       a3, a5, -206
                  c.beqz     a3, 719f
                  sra        a5, s11, s7
                  or         t6, s8, t0
713:              slt        gp, s8, a7
                  c.bnez     a4, 719f
715:              c.sub      a0, s1
716:              srl        a5, a3, a5
                  c.beqz     s1, 726f
                  c.bnez     s0, 726f
719:              xori       s10, s8, 1018
                  and        t0, t5, t5
                  sra        t4, a5, t1
                  addi       a4, s5, 317
                  c.beqz     s1, 724f
724:              c.or       a3, a3
                  c.li       s2, -19
726:              beq        ra, s7, 736f
                  csrrs      s2, 0x340, s11
                  slt        s11, t6, a1
                  sub        tp, a5, t3
                  csrrci     s7, 0x340, 27
                  mulhu      tp, a0, t4
                  blt        s1, sp, 735f
                  sra        s11, a4, s8
                  or         t0, t4, s7
735:              nop
736:              c.and      a3, s1
                  auipc      s11, 745905
                  lui        a6, 298635
                  mulh       s11, s10, t1
                  remu       t3, t2, sp
                  or         gp, gp, s0
                  beq        a2, a3, 755f
                  rem        s7, a5, s8
                  sll        t6, s2, gp
                  slli       tp, a3, 28
                  c.li       t3, -29
                  andi       t3, s4, 645
                  add        t2, tp, a0
                  bltu       sp, s3, 757f
                  srai       s1, t4, 9
                  csrrsi     t6, 0x340, 17
                  csrrs      s0, 0x340, sp
                  c.and      s1, s1
                  bne        s7, gp, 766f
755:              mulhsu     t5, s2, t2
                  remu       t2, a5, t1
757:              c.ebreak;c.nop;
                  beq        t1, t4, 777f
                  srl        s5, s0, s0
                  remu       ra, ra, s11
                  c.ebreak;c.nop;
                  bne        a5, a7, 774f
                  mulh       t4, a7, a5
                  c.li       t6, 29
                  sll        a5, a1, s11
766:              csrrw      a4, 0x340, ra
                  rem        a6, s10, a2
                  slti       t5, a6, 399
                  c.ebreak;c.nop;
                  c.and      a5, a0
                  c.srli     a5, 15
                  slt        a1, t6, zero
                  c.xor      a3, a5
774:              c.li       s3, -13
                  xor        s0, a1, s6
                  mul        a4, s5, t6
777:              auipc      s4, 204943
                  add        ra, t0, a4
                  beq        tp, a7, 789f
                  srai       s4, a1, 3
                  srai       t4, a4, 30
                  .4byte 0x00100073 # ebreak
                  c.beqz     a4, 799f
                  c.lui      a1, 23
                  slt        s10, zero, a4
                  csrrc      t2, 0x340, a3
                  or         tp, ra, s5
                  csrrwi     zero, 0x340, 17
789:              c.mv       s4, s10
                  c.and      a4, a1
                  xor        s1, tp, t6
                  .4byte 0x00100073 # ebreak
                  slti       a4, s4, 155
                  c.xor      a1, s1
                  csrrc      tp, 0x340, s2
                  csrrci     t2, 0x340, 7
                  xori       ra, zero, 552
                  c.and      s1, a3
799:              ori        a6, s4, -735
                  csrrw      s10, 0x340, t5
                  xori       t5, zero, 769
                  or         a6, t2, a6
                  c.andi     s0, 14
                  lui        a7, 755028
                  c.sub      a2, s0
                  c.mv       s7, s10
                  c.sub      a5, a2
                  rem        s1, s3, s2
                  auipc      s5, 621671
                  bne        a4, t1, 829f
                  srai       a5, t4, 26
                  slt        a3, t1, s11
                  mul        tp, sp, a3
                  c.ebreak;c.nop;
                  sltiu      t3, t5, 489
                  bgeu       s9, s2, 829f
                  xori       t6, ra, 417
                  sra        t4, a3, a0
                  c.or       s0, a5
                  c.mv       s11, a2
                  remu       s5, a0, t2
                  auipc      t4, 761075
                  remu       t1, s4, t3
                  sra        t2, s9, s7
                  csrrs      s10, 0x340, s1
                  c.srli     a2, 14
                  beq        s5, t0, 838f
                  bltu       s2, sp, 843f
829:              c.li       s1, 20
                  c.nop
                  c.lui      a6, 11
                  c.srli     a0, 21
                  mulh       s3, s5, zero
                  c.addi     a0, 21
                  c.nop
                  addi       a4, t0, 126
                  mulh       a6, t0, s6
838:              nop
                  srli       a4, s9, 1
                  c.mv       s5, t6
                  and        t2, gp, s11
                  or         s1, s11, a5
843:              c.li       ra, 28
                  c.ebreak;c.nop;
                  csrrci     s3, 0x340, 13
                  csrrsi     a2, 0x340, 9
                  csrrc      s1, 0x340, s11
                  beq        s4, s1, 863f
                  c.lui      s11, 30
                  csrrw      s11, 0x340, t0
                  .4byte 0x00100073 # ebreak
                  nop
                  divu       gp, s1, t0
                  add        a0, a0, t5
                  slli       t5, gp, 24
                  lui        t6, 591528
                  and        a1, s6, a5
                  c.and      a4, a4
                  or         s6, a7, s1
                  or         t5, t6, a4
                  or         t3, s11, t0
                  c.andi     s0, -14
863:              mulhu      a5, t4, gp
                  c.sub      a2, a5
                  sub        t3, a6, a4
                  srl        t3, s4, zero
                  sra        s11, ra, s9
                  beq        s4, s11, 887f
                  srai       s2, gp, 13
                  c.and      s1, s0
                  div        a7, t5, a6
                  c.addi     s1, -21
                  beq        a5, s7, 877f
                  slt        s10, s9, s8
                  sub        s10, s7, a2
                  xori       a5, s3, 322
877:              csrrw      s11, 0x340, t6
                  c.srai     s0, 13
                  div        a6, a1, gp
                  c.xor      a1, a2
                  c.nop
                  c.nop
                  csrrs      t5, 0x340, s3
                  and        t4, s8, gp
                  c.lui      s0, 10
                  c.xor      a2, a1
main_13:          jal        gp, 8f
0:                c.j        13f
1:                c.jal      6f
2:                c.j        17f
3:                jal        ra, 4f
4:                jal        t1, 15f
5:                jal        t1, 19f
6:                c.jal      16f
7:                c.j        14f
8:                c.jal      2b
9:                jal        ra, 18f
10:               jal        gp, 1b
11:               c.jal      0b
12:               c.j        7b
13:               jal        ra, 3b
14:               jal        ra, 5b
15:               c.j        12b
16:               c.j        11b
17:               c.jal      9b
18:               jal        ra, 10b
19:               c.and      a1, a3
887:              slt        ra, s4, s5
                  nop
                  c.andi     a3, -24
                  .4byte 0x00100073 # ebreak
                  ori        a3, gp, 485
                  lui        a0, 214630
                  xor        a7, a2, s3
                  mulhsu     a1, s9, t0
                  sltiu      a4, t1, -653
                  .4byte 0x00100073 # ebreak
                  c.lui      a4, 24
                  c.nop
                  ori        ra, a4, -703
                  slli       a4, s3, 1
                  beq        s10, t3, 913f
                  sll        a7, a0, s5
                  xor        a3, s8, s6
                  c.bnez     a0, 919f
                  bge        ra, sp, 918f
                  div        s1, a1, s5
                  csrrs      a6, 0x340, t5
                  csrrs      a6, 0x340, t0
                  mulhsu     a6, a5, t4
                  rem        a3, t4, a4
                  c.lui      tp, 28
                  srl        t2, t2, s4
913:              beq        ra, s0, 918f
                  csrrs      s11, 0x340, a0
                  srli       a3, s2, 24
                  rem        s1, s9, gp
                  c.add      a5, s5
918:              slli       zero, gp, 10
919:              beq        sp, s1, 929f
                  bne        s1, a0, 932f
                  auipc      a5, 209844
                  slli       s2, s7, 24
                  slli       s5, s1, 8
                  c.mv       s10, s8
                  or         s7, s6, t5
                  ori        s11, s3, 970
                  add        s2, t3, a2
                  csrrw      t0, 0x340, sp
929:              mulhu      t0, s2, a1
                  mul        t0, t3, s10
                  c.lui      a1, 15
932:              or         s0, a6, ra
                  mul        a3, a0, s1
                  div        t0, s9, t4
                  xori       a6, s3, -341
                  sra        a6, s8, t0
                  mulhsu     s6, t5, t1
                  slt        s11, s10, ra
                  mul        a2, a6, ra
                  csrrsi     s5, 0x340, 13
                  c.beqz     a2, 954f
                  srai       s11, s8, 4
                  csrrw      tp, 0x340, s4
                  mulhu      s3, s11, a3
                  sll        t3, s4, s2
                  nop
                  bgeu       s2, zero, 957f
                  csrrc      ra, 0x340, ra
                  mulhsu     a4, gp, t3
                  csrrc      a7, 0x340, a4
                  remu       t4, s11, t6
                  xori       tp, a3, -582
                  auipc      a2, 486275
954:              auipc      a0, 568176
                  sltiu      s2, s9, 557
                  sra        t5, s2, t3
957:              slt        s3, s5, zero
                  mulhu      s10, t6, tp
                  slti       s5, a3, 644
                  srli       t5, ra, 16
                  sll        s0, s6, t6
                  c.or       s1, a5
                  mulhsu     a3, s5, s2
                  c.nop
                  c.add      a5, tp
                  blt        t5, s0, 984f
                  c.srai     a4, 1
                  c.or       s1, a0
                  lui        s5, 731125
                  csrrwi     a7, 0x340, 2
                  csrrc      a3, 0x340, a5
                  sub        s10, a0, t0
                  sub        t2, s2, s1
                  or         ra, s0, s0
                  divu       s1, t3, zero
                  sltiu      gp, s10, 335
                  srli       a4, t6, 31
                  andi       s0, a1, -87
                  csrrs      t2, 0x340, t0
                  mulh       a0, t2, a7
                  ori        s3, gp, -987
                  divu       t5, s6, a1
                  sub        t4, s2, t4
984:              csrrw      s2, 0x340, zero
                  csrrw      s1, 0x340, t6
                  sltu       a6, s9, s2
                  nop
                  sub        t0, s0, t1
                  c.li       a5, 30
                  csrrc      a3, 0x340, s5
                  c.li       s5, -4
                  bne        t2, t2, 1002f
                  c.and      s0, a3
                  auipc      s0, 887655
                  csrrs      s4, 0x340, s1
                  sltiu      a0, t6, 780
                  mulhsu     t4, a2, t4
                  c.mv       s1, t0
                  csrrs      a2, 0x340, s7
                  and        a5, t3, tp
                  sra        s10, zero, s4
1002:             c.sub      a2, a3
                  divu       a0, t6, sp
                  c.mv       a1, s0
                  c.li       a4, -3
                  csrrsi     t1, 0x340, 0
                  remu       t3, tp, a5
                  ori        a0, gp, 15
                  divu       t1, a4, s7
                  slli       a3, t0, 17
                  csrrwi     t6, 0x340, 4
                  c.li       a7, -5
                  c.li       a3, -9
                  xor        t0, s9, t3
                  addi       s3, s4, -734
                  sub        t3, t0, gp
                  ori        s10, s3, -46
                  or         s5, t6, s4
                  csrrci     t0, 0x340, 1
                  csrrwi     tp, 0x340, 13
                  bgeu       t1, a4, 1029f
                  bne        a0, s8, 1034f
                  sltiu      a7, a7, 206
                  bne        t6, t0, 1028f
                  sll        t2, s9, s7
                  c.mv       ra, a0
                  c.xor      a5, s0
1028:             c.add      a3, s11
1029:             c.lui      t4, 10
                  c.andi     a5, 3
                  and        ra, sp, t0
                  andi       t0, a5, 909
                  csrrs      t1, 0x340, a0
1034:             c.beqz     a5, 1042f
                  csrrwi     s2, 0x340, 20
                  c.and      s0, s0
                  sltiu      t4, s2, 446
                  div        s4, t4, t2
                  rem        t6, s1, gp
                  slti       s0, sp, -652
                  .4byte 0x00100073 # ebreak
1042:             sub        a7, a0, a5
                  slt        t1, tp, s9
                  div        a0, t0, t3
                  csrrw      a5, 0x340, a4
                  xor        tp, a2, gp
                  sub        s3, a0, a1
                  lui        t3, 587122
                  srai       t5, s10, 23
                  c.andi     a5, -3
                  beq        t2, s1, 1067f
                  c.sub      a3, a3
                  c.xor      s0, a1
                  nop
                  c.addi     s3, 23
                  sll        ra, a6, s2
                  add        t5, a7, sp
                  c.sub      a4, a3
                  bge        s11, s1, 1070f
                  c.li       t4, -4
                  mul        s7, a3, s1
                  divu       t5, sp, s0
                  div        s7, zero, t0
                  c.mv       s4, a0
                  mulhu      gp, a5, t0
                  addi       a5, s4, -976
1067:             mulh       s11, gp, t3
                  c.lui      s5, 19
                  sltiu      gp, a3, 310
1070:             bne        t0, a1, 1082f
                  sltiu      s4, t0, 787
                  c.addi     t5, -14
                  bltu       tp, t6, 1092f
                  sll        s4, s2, ra
                  c.li       s10, 2
                  rem        tp, s6, a6
                  srli       s6, a6, 4
                  lui        s3, 68082
                  blt        sp, s7, 1080f
1080:             csrrw      s2, 0x340, s7
                  c.andi     a1, -28
1082:             srli       s5, sp, 14
                  .4byte 0x00100073 # ebreak
                  .4byte 0x00100073 # ebreak
                  andi       tp, t1, -1001
                  c.and      s0, a5
                  bne        a7, sp, 1106f
                  c.or       s1, s0
                  slli       t0, tp, 8
                  auipc      s4, 145290
                  bge        s6, a4, 1110f
1092:             div        s1, s2, s9
                  srl        s6, t2, s10
                  ori        tp, ra, -50
                  remu       t1, ra, s3
                  slli       a3, a3, 8
                  mulh       s11, t0, t6
                  c.beqz     a1, 1116f
                  addi       ra, ra, 692
                  ori        tp, tp, -448
                  mulhu      s4, t4, t5
                  csrrwi     t6, 0x340, 27
                  srli       a2, s5, 22
                  mulhsu     a0, gp, s9
                  auipc      a7, 97985
1106:             c.lui      a0, 2
                  nop
                  andi       s3, s3, 811
                  mulhsu     t3, s6, s1
1110:             blt        s7, t1, 1130f
                  nop
                  c.xor      a2, a0
                  xori       a3, tp, -149
                  c.and      s1, a0
                  c.andi     s1, 31
1116:             sra        gp, s7, s1
                  c.slli     t4, 10
                  and        gp, s2, ra
                  divu       s4, gp, a0
                  c.and      s0, a1
                  c.ebreak;c.nop;
                  srli       s4, s0, 27
                  mulh       zero, zero, s1
                  divu       a0, a3, gp
                  beq        t3, a5, 1140f
                  rem        a5, s5, t0
                  mul        s11, s2, a4
                  c.srli     a5, 28
                  .4byte 0x00100073 # ebreak
1130:             lui        zero, 536705
                  addi       t4, tp, 77
                  mulhsu     a2, s11, s10
                  la         s3, sub_1
                  csrrsi     s10, 0x340, 18
                  rem        a3, s8, t4
                  srl        gp, a7, s6
                  addi       s3, s3, -897
                  blt        s9, a3, j__main_sub_1_1 #branch to jump instr
                  srl        s10, s11, s7
j__main_sub_1_1:  jalr       gp, s3, 897
                  nop
                  c.bnez     a0, 1147f
                  remu       a6, a4, s7
                  rem        s4, s2, a6
                  mulh       a6, t5, t2
                  mul        zero, s1, t5
                  srai       t4, a6, 10
                  sll        t0, a2, a5
                  divu       s2, t3, a3
1140:             c.slli     s7, 11
                  auipc      a2, 647299
                  bgeu       s0, a0, 1151f
                  divu       s0, a0, a5
                  c.srli     s1, 3
                  c.beqz     a3, 1148f
                  csrrw      tp, 0x340, t5
1147:             auipc      s2, 1001058
1148:             nop
                  lui        zero, 478904
                  bge        gp, s3, 1151f
1151:             c.li       t3, 14
                  c.xor      a3, a2
                  sltiu      s1, s0, 469
                  c.srai     a5, 27
                  addi       s5, s4, -611
                  bltu       t3, s6, 1165f
                  c.and      s0, a1
                  auipc      a5, 379980
                  sll        a6, a1, t4
                  c.sub      s0, a0
                  andi       a5, t3, 355
                  lui        s4, 371847
                  mulhsu     ra, t6, a6
                  bgeu       tp, a1, 1180f
1165:             csrrci     a1, 0x340, 28
                  lui        gp, 974152
                  srai       a4, t3, 26
                  c.li       s10, -24
                  c.mv       t3, t5
                  blt        a2, gp, 1185f
                  csrrwi     s10, 0x340, 9
                  bge        a5, t3, 1184f
                  c.nop
                  and        s10, tp, t5
                  sll        s0, a1, s5
                  c.or       s1, a1
                  c.ebreak;c.nop;
                  srli       t0, a6, 25
                  divu       a1, s0, tp
1180:             divu       a0, a5, s4
                  auipc      t6, 204000
                  c.lui      a4, 2
                  .4byte 0x00100073 # ebreak
1184:             c.ebreak;c.nop;
1185:             div        tp, s6, a4
                  blt        zero, s1, 1195f
                  add        ra, s6, s0
                  srli       a3, tp, 0
                  auipc      s11, 594068
                  sll        s0, t3, t4
                  c.bnez     a2, 1210f
                  and        t4, t5, t0
                  c.addi     s7, 25
                  ori        t5, s2, 876
1195:             xori       t0, s3, -918
                  c.nop
                  sll        t1, s8, s7
                  add        t6, t2, s1
                  c.sub      a0, a4
                  slti       ra, sp, 354
                  srl        t4, s0, zero
                  sra        s2, s8, s11
                  slt        a7, a6, sp
                  bge        t1, a3, 1213f
                  csrrs      s6, 0x340, a7
                  sub        s6, s2, a7
                  csrrw      t5, 0x340, a5
                  bgeu       t0, s6, 1227f
                  srl        ra, t2, zero
1210:             csrrw      t6, 0x340, s2
                  beq        t4, s7, 1227f
                  mulhu      a4, t2, sp
1213:             c.srai     a4, 27
                  xori       t2, s11, -703
                  srl        s7, s6, s7
                  or         t6, tp, s6
                  c.beqz     s1, 1220f
                  c.add      s2, ra
                  xori       s10, t4, 145
1220:             slti       a3, a2, -65
                  or         t6, a4, t4
                  slt        zero, a5, s11
                  c.lui      a6, 29
                  c.sub      s0, s1
                  ori        t6, s5, -454
                  csrrwi     t5, 0x340, 4
1227:             sll        a4, t1, s3
                  c.beqz     a3, 1243f
                  csrrwi     t2, 0x340, 0
                  mul        s4, t4, t0
                  srai       a5, t0, 12
                  srli       s10, zero, 9
                  c.andi     s1, 12
                  csrrc      a5, 0x340, s7
                  addi       s5, s11, -852
                  add        s7, a6, s10
                  c.and      a5, a5
                  mulh       s6, a3, t4
                  nop
                  c.or       s0, a1
                  slli       s7, s8, 12
                  beq        s11, zero, 1257f
1243:             bltu       a1, s11, 1253f
                  c.and      a0, s0
                  beq        t5, t3, 1253f
                  and        a7, s0, s7
                  rem        s1, s4, s3
                  srai       gp, a0, 14
                  slt        gp, gp, a6
                  c.sub      a1, a5
                  add        s3, s4, t5
                  blt        gp, a5, 1256f
1253:             c.li       a0, -4
                  sub        t0, s1, t1
                  c.slli     s6, 22
1256:             csrrc      a3, 0x340, s11
1257:             slt        s1, a1, s8
                  slt        s4, a1, ra
                  c.bnez     a5, 1274f
                  mulhsu     a6, s8, a6
                  slli       t2, t3, 1
                  c.bnez     a4, 1272f
                  andi       s7, s4, -901
                  c.xor      a5, a4
                  csrrsi     t2, 0x340, 1
                  mulh       s10, t6, s1
                  remu       a3, t5, s4
                  la         t6, region_3+101 #start load_store_instr_stream_1
                  la         a1, region_1+11010 #start load_store_instr_stream_0
                  sb         a1, 235(t6)
                  sh         s5, 143(t6)
                  sb         t6, 261(t6)
                  sb         s9, 3(a1)
                  lbu        s0, 252(t6)
                  sb         a7, 259(t6)
                  sb         s8, -4(a1)
                  lb         ra, 16(a1)
                  lh         a7, 125(t6)
                  lb         gp, 9(a1)
                  lb         s5, 224(t6)
                  sb         t6, 1(a1)
                  sb         s9, 370(t6) #end load_store_instr_stream_1
                  lbu        t5, -5(a1) #end load_store_instr_stream_0
                  csrrc      a6, 0x340, a4
                  bne        s1, t6, 1270f
1270:             c.li       s1, -30
                  c.beqz     a4, 1279f
1272:             c.beqz     s0, 1283f
                  slli       s10, a2, 2
1274:             bne        s5, s9, 1292f
                  c.or       s1, a1
                  divu       gp, a7, s2
                  or         t6, a6, s3
                  csrrci     s10, 0x340, 24
1279:             add        s5, t0, a2
                  .4byte 0x00100073 # ebreak
                  csrrc      a0, 0x340, gp
                  divu       t3, s11, a0
1283:             c.ebreak;c.nop;
                  nop
                  mulhu      s4, s10, s8
                  xor        t6, ra, t4
                  c.mv       s10, a4
                  rem        t0, s7, s10
                  c.li       a0, -13
                  srl        s11, s1, t6
                  bne        s10, s2, 1292f
1292:             c.ebreak;c.nop;
                  mulhu      ra, s5, s11
                  csrrc      a3, 0x340, t6
                  la         t0, region_2+3045 #start riscv_load_store_rand_instr_stream_8
                  csrrw      t1, 0x340, a0
                  sb         s3, -48(t0)
                  sb         s7, -11(t0)
                  c.and      a1, a3
                  c.sub      a5, a3
                  sb         sp, -36(t0)
                  lb         t4, 60(t0)
                  slti       a0, t3, -511
                  xori       a6, s4, -22
                  sltu       zero, s0, s4
                  sh         a3, -57(t0)
                  c.slli     tp, 25
                  sh         t4, -59(t0)
                  sb         s8, -26(t0)
                  lbu        t4, 19(t0)
                  sb         s1, 4(t0)
                  lbu        ra, -6(t0)
                  csrrci     tp, 0x340, 1
                  lbu        a7, 32(t0)
                  lw         a5, 47(t0)
                  sb         a0, -40(t0)
                  csrrwi     zero, 0x340, 25
                  sub        a3, t1, a1
                  slti       s10, s10, 301
                  sb         t3, 36(t0)
                  lbu        a4, 12(t0)
                  lb         s1, -17(t0)
                  ori        s1, a2, -628
                  divu       zero, t5, s2
                  mulh       zero, t0, a7
                  c.nop
                  lh         a6, 25(t0)
                  lbu        s6, -8(t0)
                  lb         s7, 5(t0)
                  c.lui      a0, 2
                  c.li       t1, 14
                  lb         t6, 46(t0)
                  lbu        zero, 46(t0)
                  lbu        t4, 42(t0)
                  lb         a7, 32(t0) #end riscv_load_store_rand_instr_stream_8
                  srli       a6, s10, 4
                  slti       t2, s3, -74
                  andi       zero, t3, -830
                  rem        t2, t0, a3
                  c.mv       a0, s10
                  c.beqz     a3, 1313f
                  divu       t0, a5, t5
                  beq        t1, s8, 1312f
                  slli       s3, a0, 28
                  c.xor      a4, a4
                  csrrs      a1, 0x340, t5
                  csrrsi     s2, 0x340, 21
                  c.slli     s5, 25
                  c.li       tp, -3
                  ori        s2, s9, -497
                  c.nop
                  mulh       s5, a2, s7
1312:             c.srai     a4, 30
1313:             c.slli     tp, 18
                  .4byte 0x00100073 # ebreak
                  srli       t1, s1, 2
                  c.or       a4, a0
                  csrrw      a7, 0x340, t1
                  beq        a5, s6, 1330f
                  andi       s7, s0, -982
                  csrrc      s11, 0x340, gp
                  mulhsu     s10, a2, t6
                  and        s7, s4, gp
                  andi       a7, zero, -418
                  c.sub      a1, a5
                  c.slli     t3, 9
                  mul        s0, a5, gp
                  c.lui      tp, 9
                  or         a7, a2, ra
                  mulhsu     a3, sp, a4
1330:             c.lui      s6, 20
                  remu       a4, gp, t0
                  c.addi     a4, 21
                  c.li       s3, -6
                  c.beqz     a0, 1339f
                  bge        s7, t5, 1347f
                  xori       s7, t1, 475
                  slli       s1, a2, 18
                  c.mv       a1, t2
1339:             divu       t6, s3, a0
                  rem        a1, t5, ra
                  addi       t3, a2, -580
                  slli       s11, t2, 12
                  c.srai     a5, 31
                  xori       a0, tp, -633
                  remu       ra, zero, a3
                  mulhsu     s6, a7, t4
1347:             c.beqz     a5, 1366f
                  auipc      t1, 358321
                  beq        s4, t1, 1365f
                  csrrsi     s7, 0x340, 14
                  csrrc      s10, 0x340, s8
                  csrrs      s11, 0x340, a5
                  divu       a0, a7, a6
                  slti       a0, s10, -817
                  div        t2, gp, s6
                  c.addi     a2, 9
                  c.li       tp, -6
                  csrrs      a1, 0x340, s9
                  sub        t3, s6, s10
                  srli       ra, s3, 1
                  csrrci     t6, 0x340, 24
                  divu       a3, s3, gp
                  c.slli     s1, 20
                  .4byte 0x00100073 # ebreak
1365:             xor        zero, s0, s0
1366:             slt        t6, s7, a4
                  c.li       t4, 0
                  csrrsi     s10, 0x340, 22
                  .4byte 0x00100073 # ebreak
                  mulhsu     s6, s6, ra
                  bge        a5, a2, 1389f
                  c.xor      s1, s1
                  sltiu      t0, sp, 991
                  bne        s7, a6, 1394f
                  .4byte 0x00100073 # ebreak
                  c.xor      a1, a3
                  ori        tp, a6, -957
                  remu       a5, a1, t0
                  addi       t0, a2, -529
                  la         t3, region_1+12649 #start riscv_hazard_instr_stream_0
                  csrrs      ra, 0x340, s3
                  lh         a2, -15(t3)
                  lb         a2, 18(t3)
                  sh         a0, -11(t3)
                  c.add      ra, a0
                  lb         a1, 28(t3)
                  lb         a2, -40(t3)
                  lw         a2, -33(t3)
                  lh         s3, 51(t3)
                  lb         a0, -50(t3)
                  c.andi     a1, -8
                  lbu        a1, -32(t3)
                  lh         a1, 3(t3)
                  sb         a2, 22(t3)
                  lb         t6, -29(t3)
                  mulh       t6, ra, s3
                  lb         a1, 36(t3)
                  csrrs      a2, 0x340, t6
                  sb         s3, 46(t3)
                  sb         a1, -2(t3)
                  c.and      a1, a0
                  sll        a0, ra, a2
                  mulh       a2, s3, a0
                  mul        ra, a0, a0
                  mulh       t6, s3, s3
                  lb         a2, 44(t3)
                  sb         ra, -16(t3)
                  sb         a2, -26(t3)
                  lb         s3, 43(t3)
                  mulh       a2, ra, a2
                  lbu        a2, -53(t3)
                  sb         a0, -14(t3)
                  lb         a2, 50(t3)
                  lb         a0, 38(t3)
                  lb         t6, 59(t3)
                  sb         t6, -46(t3)
                  lw         s3, -5(t3)
                  lh         s3, 31(t3)
                  sh         a0, 27(t3)
                  sh         ra, 19(t3) #end riscv_hazard_instr_stream_0
                  c.mv       ra, s7
                  mulhsu     s3, t1, gp
                  slti       t3, s10, 883
                  and        a3, s6, s8
                  bltu       s2, s11, 1399f
                  xori       gp, s11, 856
                  c.srai     a3, 25
                  .4byte 0x00100073 # ebreak
                  blt        a1, a3, 1401f
1389:             rem        a4, s2, s1
                  addi       s10, s0, -955
                  auipc      s5, 586661
                  xori       s3, s11, -634
                  add        a0, t2, gp
1394:             bne        s6, s5, 1410f
                  slli       s10, s5, 12
                  sra        s7, t2, s10
                  remu       s6, t0, t4
                  sltu       a7, tp, t1
1399:             c.mv       s5, a0
                  c.sub      a2, a1
1401:             csrrsi     s7, 0x340, 16
                  c.beqz     s1, 1410f
                  c.addi     a1, 30
                  c.nop
                  csrrwi     s10, 0x340, 0
                  c.and      a4, a3
                  mul        t0, a1, t6
                  and        zero, t3, s5
                  rem        tp, a0, a0
1410:             c.addi     s0, 1
                  sltiu      s11, a5, 147
                  c.srai     s0, 31
                  csrrwi     t3, 0x340, 15
                  .4byte 0x00100073 # ebreak
                  sltu       zero, s10, s6
                  c.bnez     a1, 1426f
                  c.srli     a0, 3
                  remu       s11, t4, ra
                  divu       t3, s4, s0
                  sub        a6, t5, tp
                  slt        s2, t2, s1
                  sltu       s0, t2, a1
                  c.slli     t1, 2
                  auipc      t0, 184604
                  sltiu      s5, s2, 271
1426:             andi       t1, t5, -260
                  c.bnez     a0, 1447f
                  bgeu       a5, a1, 1440f
                  sll        a3, t4, a0
                  remu       t4, t0, a3
                  csrrwi     t3, 0x340, 27
                  mul        t0, t4, tp
                  c.and      a1, s1
                  sltiu      t4, t3, -941
                  c.slli     t3, 9
                  c.srli     s0, 15
                  csrrs      a0, 0x340, t3
                  mul        s2, ra, s9
                  c.beqz     a2, 1449f
1440:             c.lui      t4, 27
                  srai       t1, s6, 9
                  c.xor      s0, a5
                  sltu       s7, t3, s7
                  c.mv       t2, s6
                  andi       s10, t4, 171
                  c.beqz     a0, 1458f
1447:             div        t0, t3, t6
                  srai       a4, s11, 26
1449:             c.mv       a5, a1
                  bge        s3, s1, 1465f
                  beq        t2, s10, 1463f
                  c.li       tp, 17
                  mul        t3, gp, t0
                  sltu       t5, a2, a4
                  c.bnez     a2, 1470f
                  csrrci     t0, 0x340, 2
                  rem        a4, a0, tp
1458:             mulhsu     gp, t0, t5
                  lui        s4, 547352
                  slt        s1, s9, t3
                  slti       s7, a5, -630
                  xor        a1, t5, a3
1463:             divu       ra, a6, s4
                  nop
1465:             bge        s7, tp, 1480f
                  lui        s6, 704647
                  slli       s11, t2, 14
                  .4byte 0x00100073 # ebreak
                  add        a0, s0, s1
1470:             csrrwi     t1, 0x340, 0
                  .4byte 0x00100073 # ebreak
                  xor        t4, s4, t1
                  srl        tp, s9, tp
                  divu       s7, s10, a4
                  nop
                  c.sub      a5, a0
                  rem        s6, tp, a6
                  nop
                  c.beqz     a1, 1497f
1480:             slti       gp, s7, -717
                  div        t5, t1, a5
                  csrrc      t3, 0x340, t3
                  sltiu      a6, s10, -15
                  and        gp, t3, s5
                  remu       s4, t0, a1
                  c.add      s10, s5
                  xori       s7, t3, 73
                  nop
                  c.xor      a3, a2
                  c.andi     a5, -22
                  and        s4, s5, t2
                  xor        a5, t3, a3
                  c.slli     s0, 11
                  or         gp, s1, t5
                  mulhu      s10, a4, sp
                  remu       a5, tp, tp
1497:             and        ra, t3, sp
                  bge        s3, zero, 1514f
                  bne        a0, a6, 1510f
                  mulhu      a7, a1, gp
                  mul        a1, ra, a2
                  or         t1, s9, zero
                  c.srli     a4, 31
                  srli       s2, a5, 21
                  addi       t6, a1, 115
                  xor        s4, s0, zero
                  c.andi     a0, 13
                  csrrwi     s6, 0x340, 5
                  andi       t2, t6, -674
1510:             c.beqz     a5, 1519f
                  csrrw      tp, 0x340, a6
                  and        a5, a5, s10
                  c.beqz     a4, 1526f
1514:             mulhsu     s5, t4, s0
                  c.srli     a4, 12
                  c.xor      a4, s1
                  bge        a4, a0, 1532f
                  slti       s1, s2, -933
1519:             .4byte 0x00100073 # ebreak
                  sra        t2, t4, a6
                  srai       t6, t4, 1
                  c.add      a5, s11
                  c.nop
                  mulhsu     s11, a4, a2
                  c.sub      a3, a5
1526:             csrrsi     a4, 0x340, 10
                  add        gp, s7, t2
                  c.slli     s4, 7
                  c.and      a0, s0
                  csrrsi     s1, 0x340, 17
                  csrrs      tp, 0x340, s11
1532:             slli       zero, a2, 22
                  slli       s1, t2, 18
                  slli       s1, a0, 3
                  sltiu      s4, s1, -673
                  mulhsu     a4, gp, t2
                  bne        s4, s10, 1538f
1538:             c.and      s0, a3
                  csrrw      a1, 0x340, t6
                  remu       s4, s11, a4
                  div        t6, t4, s6
                  c.srai     s0, 30
                  xori       s11, s0, -1003
                  remu       zero, s5, zero
                  slt        t6, a3, t2
                  c.andi     a0, -18
                  csrrs      s2, 0x340, s5
                  c.andi     a5, -18
                  sll        t5, t2, a5
                  xori       s0, s9, 215
                  csrrwi     tp, 0x340, 17
                  csrrc      s5, 0x340, t5
                  or         zero, t3, s2
                  csrrc      tp, 0x340, t4
                  csrrc      s11, 0x340, s6
                  blt        ra, a4, 1566f
                  sra        s1, t0, sp
                  divu       t6, t5, s9
                  c.bnez     a5, 1578f
                  xori       a5, s7, 253
                  and        s7, a2, s5
                  mulh       s0, s4, t5
                  divu       s7, s2, sp
                  sltu       a1, s3, s11
                  andi       a6, a4, 612
1566:             xor        a5, gp, a3
                  remu       t3, zero, s11
                  srli       t4, a3, 18
                  slli       a7, t0, 3
                  remu       s11, a1, a1
                  csrrwi     a7, 0x340, 25
                  csrrc      s2, 0x340, t4
                  blt        s4, s8, 1581f
                  c.nop
                  srli       s5, s5, 9
                  sltu       t0, s8, zero
                  .4byte 0x00100073 # ebreak
1578:             .4byte 0x00100073 # ebreak
                  sltu       s3, t5, ra
                  csrrsi     s11, 0x340, 12
1581:             csrrc      a2, 0x340, s5
                  divu       s2, t5, s6
                  c.bnez     a3, 1602f
                  mulhu      a5, sp, t3
                  csrrsi     s2, 0x340, 8
                  mulhsu     s1, s5, s2
                  slli       s7, s7, 15
                  bltu       a4, a3, 1592f
                  blt        t0, t2, 1590f
1590:             c.or       a3, a3
                  sra        s3, a4, gp
1592:             blt        zero, t1, 1610f
                  csrrs      a6, 0x340, a2
                  sltiu      t6, a1, -851
                  bgeu       t0, a7, 1600f
                  srl        a0, sp, s3
                  bge        a4, sp, 1616f
                  div        a6, zero, s0
                  mulh       a2, s6, s1
1600:             csrrc      a5, 0x340, a4
                  ori        a2, a1, 408
1602:             xori       s4, a0, 77
                  srl        t5, s2, t4
                  slt        t0, s4, gp
                  c.andi     a4, 0
                  c.slli     gp, 31
                  c.srli     a3, 22
                  srai       t3, t3, 0
                  sra        t3, s0, t6
1610:             mulhsu     s1, gp, t2
                  csrrci     zero, 0x340, 21
                  csrrwi     s3, 0x340, 0
                  sltu       s11, s0, a1
                  andi       tp, t1, 32
                  sltu       tp, s3, s5
1616:             csrrci     ra, 0x340, 26
                  divu       s1, a0, a1
                  sll        s6, s10, sp
                  c.srai     s0, 28
                  c.ebreak;c.nop;
                  add        s3, gp, a0
                  addi       a4, t0, -963
                  rem        s2, t2, t6
                  mulh       a6, a1, a3
                  xor        a4, sp, gp
                  nop
                  c.xor      a1, a2
                  ori        s6, a3, 275
                  divu       s4, s2, t3
                  srli       a4, a1, 12
                  auipc      a5, 234635
                  nop
                  c.mv       s3, s9
                  mulhu      s4, t2, t6
                  c.ebreak;c.nop;
                  c.add      ra, ra
                  c.srli     a5, 14
                  sll        s2, t0, t4
                  slti       a0, s0, -573
                  sub        t0, a5, s1
                  c.andi     s1, -12
                  add        tp, s10, s2
                  srl        t5, t2, s7
                  c.nop
                  la         a1, region_0+775 #start load_store_instr_stream_1
                  la         t3, region_0+943 #start load_store_instr_stream_2
                  la         a3, region_0+3180 #start load_store_instr_stream_0
                  sb         s0, -4(t3)
                  sb         t3, 16(a1)
                  lb         tp, 16(t3)
                  lh         zero, -15(a1)
                  sh         s4, 16(a3)
                  sh         t1, -11(t3)
                  lh         s3, 1(a1)
                  lh         s4, -146(a3)
                  lb         a2, -11(a1)
                  lbu        s10, 11(t3)
                  sw         zero, -200(a3)
                  sb         a3, 15(a1)
                  lb         s5, -22(a3)
                  lb         t5, 79(a3)
                  lb         s0, 13(t3)
                  sb         sp, 103(a3)
                  lbu        s4, 0(a1) #end load_store_instr_stream_1
                  sb         s7, -9(t3) #end load_store_instr_stream_2
                  lbu        tp, -163(a3) #end load_store_instr_stream_0
                  c.lui      s4, 22
                  c.bnez     a2, 1655f
                  c.and      a2, a4
                  ori        s4, a5, -651
                  c.ebreak;c.nop;
                  add        t2, s3, a3
                  divu       gp, a7, gp
                  csrrw      a2, 0x340, a5
                  c.andi     a5, -17
                  c.srli     a5, 31
1655:             or         s4, s4, ra
                  c.lui      a3, 18
                  c.addi     s4, -16
                  bne        a6, a2, 1661f
                  addi       s11, s0, 274
                  srli       a0, t4, 16
1661:             xor        s4, t0, tp
                  mul        a3, a4, t1
                  nop
                  or         t2, s7, s4
                  c.mv       t6, t4
                  addi       a5, s1, 753
                  c.slli     a4, 6
                  nop
                  csrrsi     a0, 0x340, 11
                  c.ebreak;c.nop;
                  c.xor      a4, a5
                  remu       t1, t1, a4
                  c.bnez     a2, 1686f
                  csrrc      s6, 0x340, t0
                  mulh       a2, t4, s1
                  rem        t1, t2, a3
                  c.bnez     s0, 1692f
                  c.or       a1, s1
                  c.beqz     a0, 1689f
                  c.li       a6, -11
                  csrrsi     t6, 0x340, 1
                  xori       t3, a4, -437
                  c.srli     a2, 4
                  sltu       t4, s3, t3
                  ori        t1, zero, -862
1686:             sll        a5, a7, s0
                  c.andi     a4, 13
                  remu       t0, a3, s0
1689:             add        a7, s1, s6
                  bgeu       s6, t4, 1699f
                  add        ra, t6, s5
1692:             c.srai     a0, 24
                  blt        t3, ra, 1712f
                  bne        sp, s11, 1703f
                  mulh       s10, a0, a7
                  c.bnez     a3, 1704f
                  ori        t1, a6, -335
                  bne        ra, t0, 1710f
1699:             c.srli     a3, 29
                  add        a3, s4, a0
                  and        zero, s3, s2
                  c.nop
1703:             c.beqz     s1, 1704f
1704:             c.ebreak;c.nop;
                  bge        s9, s5, 1708f
                  c.lui      a2, 4
                  c.xor      a3, s1
1708:             beq        s1, s5, 1724f
                  srai       s10, s2, 24
1710:             slli       s6, s6, 28
                  c.or       a5, a2
1712:             c.srai     a3, 15
                  remu       a0, t0, t5
                  div        a7, s5, a6
                  c.mv       a7, sp
                  slli       s0, a6, 20
                  csrrs      s1, 0x340, tp
                  c.ebreak;c.nop;
                  bne        s11, tp, 1735f
                  slti       tp, s11, 151
                  csrrci     t6, 0x340, 27
                  or         a6, s0, s9
                  sll        s4, a4, t0
1724:             c.srai     a2, 17
                  xori       zero, t1, -26
                  blt        s9, s11, 1739f
                  srl        t5, t3, a7
                  c.and      a3, a1
                  bne        a4, a1, 1740f
                  csrrs      a6, 0x340, s4
                  .4byte 0x00100073 # ebreak
                  c.ebreak;c.nop;
                  csrrwi     s4, 0x340, 9
                  andi       s10, s2, -602
1735:             c.li       t5, 20
                  c.and      a1, a3
                  and        s11, s5, t0
                  c.andi     a4, 2
1739:             sltiu      a1, s5, -949
1740:             c.xor      s0, a3
                  srli       a1, t6, 1
                  beq        a7, a0, 1755f
                  slt        zero, s0, s6
                  sltu       ra, s4, t5
                  divu       t3, ra, s5
                  c.add      s3, t5
                  bne        t5, t0, 1759f
                  rem        zero, a2, gp
                  c.addi     s3, 17
                  c.nop
                  sll        s11, zero, t3
                  c.li       a1, -20
                  c.li       s1, -15
                  c.mv       t2, a6
1755:             ori        s10, sp, 122
                  xor        a0, t6, a2
                  mulhu      s4, a0, t1
                  csrrc      s5, 0x340, a2
1759:             bltu       zero, s2, 1774f
                  slli       s0, t4, 23
                  c.bnez     a1, 1779f
                  c.srai     a1, 7
                  srai       s4, a3, 26
                  c.nop
                  xori       t2, a3, -785
                  c.beqz     s1, 1778f
                  slt        s7, s0, t5
                  div        t0, s4, t2
                  rem        a2, ra, a1
                  c.xor      s1, a4
                  sra        s11, t1, s1
                  slli       tp, s3, 13
                  mulhu      s4, t0, a0
1774:             beq        s8, s6, 1775f
1775:             sll        s1, t1, t1
                  slli       s7, gp, 16
                  c.li       a1, -28
1778:             c.add      s10, tp
1779:             c.srai     a0, 15
                  c.mv       s7, t0
                  andi       a5, a4, 261
                  div        s6, ra, ra
                  c.addi     t4, -1
                  mulhu      gp, a0, s2
                  add        a7, a0, s6
                  c.ebreak;c.nop;
                  bltu       a0, a7, 1806f
                  csrrwi     a2, 0x340, 2
                  xori       a1, s0, 41
                  c.xor      s0, a4
                  c.srli     a0, 29
                  sltu       t3, t1, t3
                  c.xor      a2, a1
                  xori       zero, s0, -604
                  c.lui      s11, 16
                  beq        s4, a7, 1811f
                  c.slli     s10, 21
                  xor        s0, s5, s9
                  bge        a1, a1, 1818f
                  bge        s10, s10, 1820f
                  csrrs      tp, 0x340, t4
                  xori       t4, t5, 282
                  c.ebreak;c.nop;
                  nop
                  c.sub      a2, s1
1806:             csrrsi     ra, 0x340, 16
                  csrrwi     s5, 0x340, 23
                  andi       s4, t4, 513
                  mul        tp, s11, s6
                  srai       s4, t2, 5
1811:             srl        t5, s5, sp
                  c.or       a4, a2
                  c.addi     gp, 24
                  divu       t3, zero, a0
                  auipc      a3, 311590
                  c.li       a4, 20
                  c.mv       a4, t2
1818:             bltu       t5, zero, 1833f
                  c.sub      a3, s1
1820:             sub        s4, a0, zero
                  xor        s10, tp, s0
                  bgeu       t5, s3, 1826f
                  srl        s4, a4, t1
                  mulhsu     a0, a6, t3
                  csrrci     a0, 0x340, 11
1826:             remu       tp, a4, s2
                  sub        a7, s7, s2
                  add        t5, a4, s5
                  xori       gp, s10, 944
                  sll        zero, s0, a3
                  c.sub      s0, s0
                  addi       gp, tp, 60
1833:             xori       a3, t3, -774
                  c.add      s10, s0
                  xor        s6, s6, t6
                  bgeu       s11, a1, 1846f
                  sltiu      a7, t4, 761
                  beq        s11, s5, 1856f
                  csrrc      s2, 0x340, s1
                  c.li       a6, -13
                  c.sub      a4, s0
                  addi       a6, s6, -548
                  bltu       tp, s2, 1853f
                  ori        s3, s9, 54
                  c.and      s0, a2
1846:             ori        t4, zero, -337
                  andi       s10, a6, 287
                  add        a1, s2, s2
                  c.and      s0, a2
                  c.sub      a2, s0
                  csrrc      s3, 0x340, t2
                  c.and      s1, a1
1853:             sltu       t5, t5, s7
                  srli       a7, s0, 26
                  sltu       zero, s3, s11
1856:             bgeu       t1, s5, 1864f
                  c.xor      a5, s0
                  bne        t3, s8, 1863f
                  c.beqz     s1, 1871f
                  c.mv       a2, a0
                  auipc      s4, 344639
                  srai       s2, a6, 8
                  and        s4, t3, tp
                  sub        t3, t0, tp
                  srli       a0, tp, 19
                  la         s2, sub_2
                  c.andi     s0, -6
                  addi       s2, s2, -983
                  sltu       t1, t1, a5
                  add        a0, a6, s3
j__main_sub_2_2:  jalr       gp, s2, 983
                  addi       a0, zero, 5 #init loop 0 counter
                  slli       s11, a3, 25
                  srl        a6, a5, s4
                  rem        s3, a5, s2
                  addi       tp, zero, -9 #init loop 0 limit
                  rem        a1, a0, sp
main_51_0_t:      srl        gp, s5, t4
                  csrrsi     a7, 0x340, 6
                  xor        s0, t5, a4
                  srl        a7, t6, t3
                  mulhsu     a7, gp, s0
                  andi       t3, a2, -487
                  srli       a6, t3, 26
                  srai       a5, s11, 9
                  srai       s7, tp, 27
                  add        a4, s10, s1
                  addi       a0, a0, -10 #update loop 0 counter
                  c.slli     a5, 8
                  add        a1, s4, a1
                  srl        a4, t6, zero
                  addi       s2, s0, -984
                  bge        a0, tp, main_51_0_t #branch for loop 0
                  mulh       s0, t2, gp
1863:             c.srai     a1, 24
1864:             c.andi     a5, -11
                  nop
                  and        gp, a5, s11
                  csrrs      a4, 0x340, s2
                  add        s1, s4, s1
                  sltu       t2, t6, s11
                  c.add      a4, s2
1871:             slti       ra, s6, 893
                  xor        s10, s10, t1
                  csrrci     t0, 0x340, 29
                  div        t2, a0, s11
                  rem        s11, a6, s3
                  mulhsu     ra, t5, a6
                  rem        t5, t5, a2
                  srai       t1, t4, 23
                  div        t1, t5, a6
                  sll        tp, tp, t0
                  sltiu      a4, a3, -930
                  lui        t5, 696739
                  .4byte 0x00100073 # ebreak
                  c.andi     a4, 18
                  remu       s4, s5, s0
                  rem        gp, t4, s1
                  mulh       s0, t3, s1
                  csrrc      s2, 0x340, t1
                  mulhsu     a2, tp, s7
                  .4byte 0x00100073 # ebreak
                  sra        s5, t2, s5
                  csrrsi     a3, 0x340, 6
                  rem        a3, a7, s6
                  nop
                  divu       s7, t0, s5
                  xor        t5, s6, t1
                  remu       t3, t4, a2
                  xor        s1, a2, a7
                  blt        s4, s1, 1912f
                  c.lui      s5, 14
                  sub        a4, s0, s7
                  c.add      s4, gp
                  auipc      s6, 370524
                  addi       t3, a5, -544
                  xor        a6, s11, t6
                  csrrwi     s4, 0x340, 6
                  add        a0, gp, a2
                  c.srai     a0, 28
                  slti       s7, s4, 285
                  c.srli     a4, 21
                  c.or       a2, a4
1912:             c.andi     a2, 2
                  c.beqz     s0, 1925f
                  add        tp, a6, a6
                  c.add      a1, t6
                  c.lui      s1, 17
                  xor        t0, s8, t2
                  sll        a0, t1, s7
                  mulh       a0, sp, zero
                  lui        s5, 139954
                  ori        zero, s8, -325
                  srl        s3, s5, t0
                  csrrwi     t1, 0x340, 23
                  nop
1925:             blt        s5, s11, 1935f
                  bge        a3, t3, 1935f
                  c.srli     s1, 19
                  auipc      s3, 553367
                  slli       a1, a3, 5
                  csrrc      a3, 0x340, s9
                  c.srai     a2, 10
                  c.srai     a5, 26
                  c.sub      a4, s0
                  andi       a6, t4, -101
1935:             xor        s7, s11, a1
                  beq        t4, a2, 1945f
                  add        s4, t5, a2
                  sltu       t3, s10, s7
                  divu       t6, sp, a7
                  mulhu      s0, a7, a4
                  srl        s4, s0, s11
                  remu       s11, a6, s8
                  bltu       s11, a1, 1962f
                  sltu       s1, s11, a1
1945:             c.bnez     a1, 1957f
                  sltiu      t3, t1, -341
                  srai       a7, a3, 2
                  mulhu      s4, s0, ra
                  slti       t3, a0, 824
                  remu       a3, zero, s4
                  bltu       t1, s8, 1954f
                  csrrw      a4, 0x340, tp
                  rem        gp, s1, t5
1954:             c.srli     a3, 13
                  sub        t4, a6, a7
                  sub        gp, s7, s9
1957:             andi       a7, s9, -720
                  c.lui      s11, 19
                  c.nop
                  c.srli     a1, 6
                  lui        s7, 292213
1962:             csrrwi     s4, 0x340, 3
                  mulhsu     t3, s6, s3
                  nop
                  slt        gp, a1, a1
                  or         s10, s2, a4
                  divu       a7, s11, a6
                  addi       a2, t6, -605
                  slli       gp, t6, 4
                  c.lui      t4, 3
                  xor        a6, gp, s0
                  or         tp, s11, s5
                  ori        a2, t2, -418
                  or         s1, a1, a0
                  c.nop
                  add        t4, s3, sp
                  mulh       a6, t1, s6
                  c.and      a0, a4
                  bge        a0, a5, 1997f
                  csrrw      s0, 0x340, zero
                  c.srai     s1, 13
                  mul        s0, a2, a0
                  c.and      s1, a2
                  c.li       t4, 24
                  blt        s8, t1, 1998f
                  beq        s3, a1, 1996f
                  csrrwi     t1, 0x340, 22
                  c.slli     s3, 19
                  mulhsu     a2, a3, t6
                  sra        tp, ra, s4
                  csrrci     zero, 0x340, 13
                  andi       s7, t2, 910
                  bge        s9, s11, 2008f
                  c.beqz     a3, 2013f
                  c.sub      a4, a1
1996:             remu       s2, s7, s10
1997:             add        t4, a3, t5
1998:             sra        s7, s6, sp
                  sll        s11, s1, s10
                  c.beqz     s1, 2001f
2001:             sltu       a1, s0, tp
                  sltu       a4, s1, s2
                  c.beqz     a2, 2007f
                  srli       t3, t2, 14
                  c.beqz     a1, 2016f
                  csrrsi     t0, 0x340, 12
2007:             divu       s11, s6, t6
2008:             c.xor      a0, a1
                  mulh       a2, s10, a0
                  bltu       a4, a3, 2025f
                  xor        s10, s3, s6
                  mulhsu     t1, s5, s1
2013:             csrrw      gp, 0x340, a4
                  bgeu       ra, t0, 2033f
                  blt        s6, sp, 2023f
2016:             c.ebreak;c.nop;
                  csrrwi     a0, 0x340, 0
                  csrrsi     a3, 0x340, 2
                  mul        a6, t1, a2
                  c.mv       tp, t5
                  bgeu       a6, zero, 2031f
                  mulhsu     t2, zero, a1
2023:             csrrs      a1, 0x340, sp
                  csrrc      zero, 0x340, ra
2025:             auipc      s0, 914806
                  blt        a2, a0, 2031f
                  c.add      s5, s5
                  mulhsu     s4, a6, s7
                  c.and      s0, a1
                  c.nop
2031:             div        s11, a3, sp
                  sltiu      a6, s9, -804
2033:             c.add      a2, sp
                  remu       s0, a3, a5
                  xor        t6, sp, t3
                  slti       gp, s9, -65
                  mulh       a0, s0, s8
                  bne        s1, s7, 2054f
                  addi       gp, s5, -428
                  c.mv       s5, sp
                  c.lui      a5, 31
                  nop
                  c.sub      a1, a0
                  c.and      a2, a1
                  mulhu      s5, a3, gp
                  c.bnez     a1, 2066f
                  c.srai     a4, 25
                  c.beqz     a5, 2056f
                  nop
                  c.bnez     s1, 2066f
                  c.or       a5, a4
                  rem        s11, t0, t6
                  blt        s9, t6, 2054f
2054:             xor        s2, t6, sp
                  divu       t6, s4, a2
2056:             c.addi     s0, 4
                  and        a7, s10, t4
                  srl        t0, t3, t4
                  srli       a5, s8, 7
                  slti       a4, s1, -645
                  mulhsu     s3, a1, t4
                  andi       a5, t4, 58
                  rem        s5, a6, tp
                  mulh       gp, a1, t0
                  csrrs      s7, 0x340, t2
2066:             c.srli     a3, 8
                  ori        a5, s5, -611
                  .4byte 0x00100073 # ebreak
                  sll        s6, a0, s4
                  c.slli     s6, 4
                  csrrwi     t1, 0x340, 14
                  slli       a5, gp, 0
                  c.srai     a5, 11
                  sltu       t0, t6, a2
                  csrrwi     gp, 0x340, 20
                  srli       a4, s6, 11
                  nop
                  bgeu       a1, s2, 2093f
                  bge        s11, a7, 2094f
                  srli       ra, zero, 29
                  ori        gp, a1, 361
                  sll        s7, t1, a7
                  bge        tp, zero, 2101f
                  bltu       a4, s9, 2103f
                  csrrw      s7, 0x340, s6
                  bge        s7, a4, 2096f
                  mulhu      s3, t4, s11
                  bne        t3, t4, 2096f
                  sltiu      a2, t5, -623
                  c.and      a5, a5
                  c.li       s5, -9
                  c.mv       a1, a3
2093:             c.mv       t4, t4
2094:             slt        s4, s8, s8
                  csrrwi     t3, 0x340, 21
2096:             xor        t4, s9, a0
                  csrrci     t3, 0x340, 26
                  mulh       s2, t6, s6
                  c.slli     a2, 23
                  remu       s1, t3, s1
2101:             lui        t2, 247790
                  c.nop
2103:             mulhu      s2, a4, s9
                  csrrci     s5, 0x340, 13
                  xor        a1, t3, s8
                  mulh       s0, s9, s0
                  c.add      a0, t0
                  and        s2, t5, s8
                  addi       tp, a1, 959
                  c.addi     t3, -30
                  srli       s7, a2, 15
                  xor        gp, s2, a0
                  beq        t4, zero, 2132f
                  c.li       t0, 15
                  c.mv       a7, s7
                  bne        s5, s7, 2120f
                  divu       s11, sp, t5
                  remu       s10, a6, a4
                  c.mv       ra, a4
2120:             rem        s7, t6, s3
                  csrrsi     s3, 0x340, 28
                  c.add      t3, t1
                  c.sub      s1, a5
                  rem        t0, s10, s6
                  xori       t0, s5, 40
                  bgeu       s11, a6, 2138f
                  c.and      a3, a0
                  rem        zero, ra, a1
                  csrrci     s7, 0x340, 15
                  add        t0, t6, sp
                  c.or       s0, a2
2132:             c.and      a1, s1
                  c.addi     a7, -16
                  blt        s4, s5, 2150f
                  c.sub      s1, a2
                  c.add      s5, s10
                  beq        t6, t3, 2140f
2138:             rem        ra, t2, a6
                  c.addi     a7, -1
2140:             xori       t2, t6, 487
                  srli       s10, a7, 17
                  c.ebreak;c.nop;
                  xori       s0, a6, 601
                  c.srai     a3, 14
                  bge        s9, tp, 2158f
                  c.li       t5, -24
                  bgeu       s1, s5, 2148f
2148:             ori        zero, a5, 427
                  sltiu      a6, t4, -476
2150:             c.slli     a4, 14
                  rem        t5, gp, a6
                  csrrsi     s7, 0x340, 16
                  rem        s11, sp, s2
                  c.bnez     a1, 2159f
                  c.srai     a4, 9
                  c.add      s10, a2
                  mulhu      s11, a2, s11
2158:             xori       a0, a3, -1003
2159:             c.li       s7, -31
                  add        s1, a6, s8
                  csrrw      s4, 0x340, a4
                  csrrw      s7, 0x340, ra
                  auipc      s0, 953710
                  mulhu      s3, t1, a4
                  bge        s2, a7, 2174f
                  c.li       s3, -3
                  c.andi     a4, 13
                  bge        t6, s9, 2177f
                  c.andi     a2, 6
                  bltu       t6, s3, 2189f
                  bne        s3, tp, 2186f
                  c.add      t1, a3
                  c.srli     a0, 28
2174:             bne        s0, a5, 2192f
                  ori        tp, s10, -537
                  addi       s11, ra, -801
2177:             or         tp, s4, t6
                  slli       a0, tp, 31
                  slti       zero, a5, -128
                  c.nop
                  add        s10, a0, t3
                  mulhsu     gp, s1, zero
                  div        t1, s1, tp
                  addi       t1, a5, 980
                  sltu       t0, a2, s6
2186:             c.beqz     a2, 2199f
                  bne        s5, a6, 2205f
                  nop
2189:             sltu       a1, t6, ra
                  c.mv       s3, a3
                  bgeu       s8, s10, 2206f
2192:             c.mv       t6, tp
                  mulhsu     t0, a1, zero
                  csrrw      a2, 0x340, s7
                  andi       zero, a5, 330
                  csrrw      a0, 0x340, t5
                  bne        s5, sp, 2217f
                  mul        s4, a4, t2
2199:             csrrci     t4, 0x340, 6
                  c.sub      s0, s1
                  c.andi     a3, -12
                  blt        ra, s5, 2213f
                  sub        zero, a3, s2
                  sltu       a2, t5, a3
2205:             blt        s3, s11, 2220f
2206:             add        s0, t4, a1
                  srl        t6, s2, s8
                  and        a5, s0, s3
                  bgeu       a2, s6, 2217f
                  slti       t6, s11, 247
                  c.ebreak;c.nop;
                  mulh       t2, t2, s8
2213:             c.beqz     a4, 2223f
                  beq        t1, ra, 2226f
                  c.and      a2, a1
                  c.li       s7, 26
2217:             srl        s11, sp, gp
                  div        t5, t1, a0
                  mulhsu     s0, t3, s4
2220:             c.or       a3, a5
                  mul        s11, s4, a6
                  addi       a5, t0, 511
2223:             csrrsi     s2, 0x340, 25
                  csrrwi     a2, 0x340, 2
                  mulhu      t6, s1, s4
2226:             add        t2, s5, sp
                  c.sub      a0, a3
                  lui        a0, 774936
                  bgeu       s3, a7, 2241f
                  beq        t6, s8, 2246f
                  c.xor      a1, s0
                  bgeu       tp, s11, 2247f
                  rem        t4, t3, s2
                  blt        s0, a1, 2244f
                  csrrc      s2, 0x340, s0
                  slli       t6, s0, 17
                  c.bnez     a0, 2238f
2238:             ori        a0, a4, 135
                  slt        t5, s4, t6
                  c.bnez     a0, 2244f
2241:             xor        t2, t6, zero
                  c.slli     s5, 24
                  c.srai     a4, 3
2244:             add        s7, s10, s8
                  slt        s3, a7, a1
2246:             andi       a4, a0, 44
2247:             c.srai     a1, 7
                  sltu       t3, s10, gp
                  c.lui      a4, 11
                  la         s7, region_1+10627 #start riscv_load_store_rand_instr_stream_2
                  srli       t6, a3, 3
                  lui        t0, 703817
                  lw         s0, -59(s7)
                  slli       t5, a2, 16
                  lbu        s6, 12(s7)
                  lb         s11, 26(s7)
                  div        a4, a5, zero
                  lbu        gp, -22(s7)
                  addi       t4, t1, 732
                  lb         tp, 36(s7)
                  srai       a1, a6, 19
                  c.ebreak;c.nop;
                  lb         t3, 64(s7)
                  lb         ra, 14(s7)
                  sltiu      s2, s5, -828
                  slt        gp, t5, a0
                  srl        t2, s1, s10
                  lhu        t0, 21(s7)
                  c.lui      t0, 30
                  addi       a2, a4, 1019
                  sb         s6, -56(s7)
                  lh         s5, -55(s7)
                  lbu        t5, 11(s7)
                  sub        a7, s0, t3
                  sb         t5, 4(s7) #end riscv_load_store_rand_instr_stream_2
                  sltiu      t2, a4, -460
                  csrrsi     s0, 0x340, 19
                  sltiu      t0, a7, 734
                  c.or       a5, a0
                  c.and      a2, a0
                  div        ra, s11, s2
                  slli       s4, t4, 15
                  mulhsu     t2, s8, t3
                  c.lui      s2, 9
                  c.and      a0, a5
                  auipc      s3, 126626
                  c.add      a1, s11
                  or         t1, sp, s0
                  xori       gp, s7, 806
                  remu       s7, a1, t1
                  nop
                  bne        s7, s6, 2281f
                  csrrs      t1, 0x340, s11
                  bge        a6, s7, 2280f
                  auipc      a3, 182823
                  xor        s1, ra, s1
                  csrrsi     a5, 0x340, 4
                  c.slli     ra, 4
                  c.bnez     s0, 2278f
                  csrrwi     s5, 0x340, 12
                  beq        s3, a1, 2276f
2276:             divu       s6, s9, a7
                  blt        s4, a4, 2286f
2278:             divu       s11, sp, s4
                  srl        a5, s8, gp
2280:             sltu       a0, a6, s4
2281:             slli       gp, t3, 4
                  slti       a0, zero, 974
                  c.addi     gp, -20
                  c.add      gp, s5
                  srl        a5, t3, s5
2286:             bgeu       zero, a3, 2296f
                  c.srli     a3, 20
                  srl        a5, a4, s3
                  sra        t1, t5, a0
                  csrrw      ra, 0x340, a7
                  mulhsu     a1, s3, t1
                  c.ebreak;c.nop;
                  mul        a2, a0, tp
                  c.beqz     a4, 2302f
                  c.add      s5, t4
2296:             slt        s2, s11, a3
                  c.srai     a1, 2
                  c.add      s3, a6
                  srai       s7, a1, 13
                  sra        t1, s6, sp
                  bgeu       t0, a2, 2317f
2302:             sra        t4, s8, a3
                  auipc      s10, 329382
                  beq        s2, sp, 2312f
                  srli       s10, tp, 20
                  srai       t5, a0, 7
                  c.beqz     a1, 2317f
                  add        a3, t0, s3
                  and        t5, a1, s3
                  sltu       s0, s10, t4
                  c.andi     a3, 5
2312:             or         a6, a3, t3
                  c.beqz     a4, 2314f
2314:             divu       s2, t4, a0
                  c.nop
                  bgeu       t5, a4, 2327f
2317:             c.ebreak;c.nop;
                  mul        gp, a1, t4
                  c.srai     a5, 12
                  srai       t2, s11, 11
                  sra        t0, a3, s4
                  addi       s7, a0, 544
                  srli       s7, a1, 15
                  andi       t5, s7, 554
                  sll        a2, s1, t3
                  bltu       a0, t3, 2345f
2327:             auipc      t2, 119739
                  remu       s11, s10, a1
                  mulhu      t4, tp, a7
                  csrrsi     a6, 0x340, 30
                  c.beqz     a0, 2350f
                  csrrs      s7, 0x340, s4
                  div        t3, a7, s10
                  c.mv       s6, a6
                  beq        t3, t3, 2350f
                  andi       gp, a5, 7
                  divu       a6, s4, ra
                  xori       s7, a3, -924
                  remu       s5, t3, a7
                  csrrwi     s1, 0x340, 23
                  div        s1, tp, a0
                  c.xor      a4, a3
                  xori       s11, a3, 492
                  mul        s5, s6, t1
2345:             srai       t2, s5, 23
                  csrrci     a6, 0x340, 30
                  c.sub      a5, a5
                  mul        t1, s4, s11
                  bgeu       s2, s2, 2369f
2350:             bgeu       s6, a5, 2365f
                  or         gp, s5, a0
                  lui        a4, 964947
                  slli       a7, t0, 15
                  c.add      ra, s9
                  sub        t6, t6, s2
                  c.srli     s1, 18
                  c.bnez     s1, 2370f
                  c.lui      s11, 4
                  mulhsu     s4, a1, a1
                  c.slli     s4, 6
                  c.bnez     a5, 2373f
                  c.beqz     a4, 2380f
                  sltiu      a3, s7, 277
                  mulhu      s4, t0, a1
2365:             csrrw      s10, 0x340, t3
                  beq        s0, s3, 2381f
                  c.srli     a2, 28
                  c.slli     s6, 13
2369:             beq        a2, tp, 2378f
2370:             andi       tp, s3, 601
                  c.nop
                  ori        a0, t1, 669
2373:             divu       t1, zero, s6
                  lui        s11, 321541
                  c.sub      s0, a3
                  slti       a4, a5, -384
                  rem        s3, a4, gp
2378:             c.nop
                  beq        s8, s11, 2395f
2380:             csrrsi     s5, 0x340, 30
2381:             c.slli     t5, 19
                  c.beqz     a2, 2395f
                  slt        a4, a1, t6
                  c.li       t6, 24
                  csrrc      s1, 0x340, sp
                  srli       a2, s7, 20
                  xori       a1, s10, 221
                  srli       tp, a0, 21
                  nop
                  rem        a5, a6, t4
                  csrrs      a0, 0x340, t3
                  slt        gp, a2, t0
                  rem        s6, s0, a3
                  c.nop
2395:             sltu       s1, t2, a0
                  sltu       s10, t2, gp
                  xori       a6, s6, -397
                  sra        a4, s1, t6
                  c.srai     s1, 21
                  auipc      s7, 738538
                  sub        s0, a3, s4
                  mulhsu     t5, a0, a3
                  slt        s10, a7, s3
                  mulhsu     tp, a5, s9
                  and        a7, s2, a3
                  sltiu      s5, tp, -702
                  sltu       t5, tp, s8
                  xor        t0, a5, a0
                  beq        a5, tp, 2419f
                  sra        s1, t1, sp
                  sra        s2, s8, t0
                  beq        t6, a1, 2424f
                  csrrw      s1, 0x340, a0
                  or         t4, ra, t6
                  blt        a6, sp, 2418f
                  slli       a6, s7, 11
                  srl        t4, a6, gp
2418:             rem        a5, a1, s8
2419:             c.li       s5, 14
                  mul        s3, s0, t2
                  csrrw      a7, 0x340, s1
                  csrrc      s0, 0x340, s8
                  div        a5, a1, tp
2424:             add        s5, a3, a6
                  xor        t0, tp, s4
                  c.srli     a0, 31
                  csrrc      a2, 0x340, s6
                  ori        s1, a5, -823
                  blt        a5, a7, 2447f
                  sll        s7, s3, s3
                  sltiu      t3, s0, -336
                  beq        a7, t5, 2451f
                  c.andi     a3, -29
                  c.ebreak;c.nop;
                  ori        t5, t6, -348
                  mulh       s2, s8, a4
                  c.andi     a3, -13
                  remu       t4, sp, s10
                  c.srli     a4, 29
                  c.or       a2, a3
                  divu       s0, s3, a5
                  rem        t1, a2, sp
                  auipc      ra, 246854
                  add        ra, t6, t5
                  or         gp, a5, s11
                  sltiu      a5, a1, -768
2447:             srli       t4, t0, 6
                  xor        s0, s7, s2
                  sltu       s4, t2, s4
                  bne        gp, a0, 2461f
2451:             sll        gp, a7, sp
                  xor        ra, a6, t1
                  mulh       s7, a1, s4
                  c.andi     s1, 3
                  c.srli     a3, 3
                  c.lui      a7, 6
                  addi       s7, sp, 688
                  c.beqz     a0, 2470f
                  c.bnez     a5, 2475f
                  nop
2461:             csrrc      a3, 0x340, t1
                  mulh       s4, s0, s0
                  c.sub      a1, a0
                  c.and      a4, a0
                  bne        a3, ra, 2484f
                  xor        t3, t4, sp
                  c.and      a5, a1
                  lui        t0, 480417
                  c.addi     a4, 28
2470:             div        a5, s3, a0
                  add        s4, t6, a1
                  c.nop
                  ori        a2, gp, 268
                  mulh       t5, t2, t6
2475:             csrrc      a7, 0x340, s0
                  rem        a6, sp, a1
                  c.and      a0, a3
                  or         t0, a1, tp
                  csrrc      t2, 0x340, s1
                  srai       s0, s5, 22
                  sra        a7, t3, a7
                  .4byte 0x00100073 # ebreak
                  slli       a3, ra, 13
2484:             rem        a0, s1, t2
                  slli       s2, tp, 22
                  c.mv       s7, tp
                  csrrs      t2, 0x340, t4
                  mulhsu     s2, a1, s11
                  lui        a2, 828503
                  c.bnez     a1, 2491f
2491:             csrrci     a7, 0x340, 15
                  sltiu      s10, sp, 297
                  and        s4, a6, a1
                  csrrci     s2, 0x340, 1
                  mulhu      a3, s11, s5
                  and        tp, t2, s7
                  mulh       a4, a6, a3
                  sll        s3, ra, t1
                  csrrw      a5, 0x340, t1
                  c.addi     s6, 29
                  c.srai     s1, 5
                  sltiu      gp, s9, 935
                  sra        a7, s11, a1
                  div        s1, s2, t0
                  div        t3, t4, t6
                  bltu       zero, gp, 2516f
                  c.add      ra, a3
                  bltu       tp, a1, 2520f
                  remu       t2, s9, a0
                  xori       tp, s7, 776
                  slli       a5, s1, 21
                  csrrci     a7, 0x340, 11
                  andi       a3, s2, 370
                  c.ebreak;c.nop;
                  auipc      s0, 83481
2516:             c.lui      s1, 16
                  c.li       t0, -32
                  xori       a4, s2, -706
                  sll        t4, s7, t6
2520:             bgeu       s10, tp, 2538f
                  slt        a4, t3, s4
                  and        t0, gp, s0
                  csrrc      t0, 0x340, tp
                  c.beqz     s0, 2536f
                  sltiu      a1, t2, -103
                  lui        t1, 628051
                  xor        s10, s9, a3
                  bne        a4, s1, 2543f
                  xor        t0, s2, ra
                  c.srai     a4, 10
                  c.bnez     a5, 2539f
                  c.mv       s5, a3
                  sub        s10, t0, a2
                  c.beqz     a0, 2553f
                  bne        s10, a2, 2548f
2536:             c.xor      a1, s1
                  bltu       a7, t5, 2546f
2538:             div        s3, a0, s6
2539:             remu       a3, t2, s11
                  c.ebreak;c.nop;
                  nop
                  sub        t4, a3, t5
2543:             divu       s3, a1, s2
                  remu       ra, a7, t2
                  c.ebreak;c.nop;
2546:             srl        t3, s11, s1
                  auipc      s4, 81914
2548:             bne        a2, a1, 2563f
                  srai       a2, ra, 2
                  c.ebreak;c.nop;
                  la         ra, region_2+6957 #start load_store_instr_stream_2
                  la         s2, region_2+4943 #start load_store_instr_stream_1
                  sw         t1, 9(s2)
                  la         t0, region_2+384 #start load_store_instr_stream_0
                  lb         t5, -33(t0)
                  la         gp, region_2+1135 #start load_store_instr_stream_3
                  lhu        s7, 117(ra)
                  lb         s5, -11(s2)
                  sh         s0, 183(gp)
                  sb         s4, -14(s2)
                  lbu        s7, 10(t0)
                  sw         t5, 85(gp)
                  sb         a3, -202(ra)
                  sw         s8, -81(ra)
                  sh         a3, -30(t0)
                  lbu        a4, -5(s2)
                  sh         t4, -9(s2)
                  sb         a0, -26(t0)
                  lh         a6, -11(s2)
                  lh         a5, 44(t0)
                  lh         s5, -35(ra)
                  sb         t1, 12(s2)
                  lbu        a3, -35(t0)
                  lw         a4, 175(ra)
                  sb         s1, 80(gp)
                  lbu        s7, 23(t0)
                  lbu        a3, -132(ra)
                  lbu        s11, 5(s2) #end load_store_instr_stream_1
                  sb         s5, -178(ra)
                  lbu        t4, 7(gp)
                  sb         s3, -62(ra) #end load_store_instr_stream_2
                  sh         s4, -35(gp) #end load_store_instr_stream_3
                  sb         s5, -24(t0) #end load_store_instr_stream_0
                  auipc      t6, 24453
                  c.add      s7, t6
2553:             csrrwi     t6, 0x340, 28
                  and        s6, t4, s2
                  lui        a3, 632370
                  c.xor      s1, s0
                  c.bnez     a1, 2572f
                  divu       s1, s4, t4
                  c.and      s0, a1
                  srai       s1, s3, 1
                  auipc      ra, 60263
                  sub        t5, s8, s9
2563:             mulhsu     a1, s5, zero
                  slli       t5, t3, 30
                  csrrwi     t4, 0x340, 2
                  .4byte 0x00100073 # ebreak
                  c.xor      a4, a2
                  div        s5, t6, t1
                  sll        t1, t5, a7
                  sub        s7, a4, s2
                  and        t5, s3, s11
2572:             slt        t2, s3, t3
                  lui        s1, 648230
                  lui        a4, 193664
                  c.sub      a1, a2
                  c.xor      a1, s0
                  addi       tp, s7, 437
                  srai       t5, sp, 7
                  mulh       gp, s8, s3
                  and        ra, a4, a6
                  slli       t2, zero, 21
                  c.andi     a2, 24
                  bge        a4, sp, 2588f
                  andi       a5, a3, 364
                  c.mv       s5, tp
                  div        s3, s2, a2
                  sub        zero, a7, s5
2588:             mul        s1, t2, gp
                  c.addi     s5, 30
                  ori        s7, a6, -517
                  mul        a6, s9, s11
                  c.li       s6, 7
                  div        a3, t5, s6
                  bne        a7, t1, 2604f
                  sra        s10, s8, s0
                  slti       a7, sp, 617
                  csrrwi     t2, 0x340, 6
                  srai       a6, t0, 16
                  bgeu       t4, gp, 2600f
2600:             sltiu      a5, s2, -752
                  sltiu      t3, s7, -227
                  csrrsi     a5, 0x340, 21
                  .4byte 0x00100073 # ebreak
2604:             ori        s5, t6, 113
                  sub        s4, a4, a4
                  c.andi     a3, 5
                  c.mv       t5, sp
                  c.lui      t5, 3
                  slli       t4, s2, 21
                  c.srai     a1, 30
                  mul        a3, s10, s1
                  c.add      gp, t3
                  lui        s3, 641496
                  .4byte 0x00100073 # ebreak
                  bltu       s1, t0, 2618f
                  c.lui      s0, 17
                  c.lui      s4, 30
2618:             xor        a0, t5, a2
                  divu       t0, s8, a2
                  sub        a5, a5, sp
                  sub        s7, a5, s0
                  divu       t2, a5, t3
                  andi       s1, t6, 779
                  nop
                  remu       a0, t0, sp
                  bgeu       t6, a5, 2644f
                  c.and      a3, a2
                  c.slli     a1, 17
                  blt        a4, a0, 2648f
                  c.andi     a2, -14
                  csrrc      a4, 0x340, a2
                  c.srli     a4, 21
                  csrrw      a0, 0x340, s7
                  mul        s10, t6, t5
                  c.mv       s4, s8
                  c.xor      a1, a5
                  addi       t2, t4, -285
                  and        a0, a3, a4
                  csrrw      s1, 0x340, t4
                  sra        t5, t3, s2
                  xori       s5, s11, 883
                  la         s3, region_2+3509 #start load_store_instr_stream_3
                  la         a2, region_1+284 #start load_store_instr_stream_2
                  la         ra, region_4+1462 #start load_store_instr_stream_1
                  sb         a3, -630(s3)
                  la         a3, region_0+603 #start load_store_instr_stream_0
                  sb         a4, 132(a3)
                  sb         t6, -6(ra)
                  lh         gp, -253(a3)
                  lbu        s10, 13(ra)
                  sb         a1, 359(s3)
                  lb         t5, 1(a2)
                  lb         t0, -195(a3)
                  sh         sp, 75(s3)
                  lw         s1, -12(a2)
                  sb         s4, 159(a3)
                  sh         ra, -61(a3)
                  lb         s1, -38(s3)
                  sw         t4, 10(ra)
                  lb         t6, -204(a3)
                  lb         s5, 14(ra)
                  lhu        a0, 221(s3)
                  sb         ra, 140(a3)
                  sb         s9, 12(a2)
                  lbu        gp, 3(a2)
                  lbu        a1, -718(s3)
                  lb         a1, -15(ra)
                  lbu        t0, -3(a2)
                  sb         s1, -5(a3)
                  lb         a5, -2(ra) #end load_store_instr_stream_1
                  sb         s7, -158(s3)
                  lb         s4, -14(a2)
                  sh         s1, -93(a3)
                  lhu        s5, 137(s3)
                  sh         t6, -2(a2)
                  sb         s7, 1015(s3) #end load_store_instr_stream_3
                  lh         t1, -4(a2) #end load_store_instr_stream_2
                  lbu        tp, 81(a3) #end load_store_instr_stream_0
                  bltu       a3, s3, 2652f
                  c.srai     a4, 13
2644:             csrrwi     s7, 0x340, 2
                  addi       s1, a2, 601
                  srai       s6, a4, 1
                  slt        t4, s10, s8
2648:             mulhu      t6, gp, a1
                  mulhsu     s0, a0, s7
                  c.and      s0, s1
                  mulhsu     s0, a5, ra
2652:             c.xor      a1, a2
                  c.ebreak;c.nop;
                  c.ebreak;c.nop;
                  c.lui      s0, 2
                  remu       s11, t2, a5
                  c.srli     a2, 17
                  csrrsi     tp, 0x340, 29
                  csrrs      ra, 0x340, a6
                  bgeu       a5, t4, 2664f
                  c.nop
                  srl        zero, a6, s1
                  c.bnez     a3, 2676f
2664:             c.bnez     s1, 2672f
                  c.xor      a5, a3
                  nop
                  sub        a5, s2, ra
                  or         a2, s6, t2
                  remu       s10, sp, t2
                  c.xor      a1, a4
                  srl        s10, a1, s8
2672:             srai       s5, s11, 8
                  bgeu       s11, t6, 2688f
                  c.srli     s1, 27
                  bltu       zero, s2, 2691f
2676:             c.srli     a2, 24
                  c.xor      a1, a2
                  csrrci     t4, 0x340, 28
                  mul        t0, gp, s4
                  bgeu       gp, s0, 2689f
                  sub        t4, tp, t0
                  c.lui      s11, 25
                  c.slli     t2, 1
                  c.srli     a4, 8
                  c.srai     a1, 3
                  c.addi     s2, -22
                  srai       s6, sp, 20
2688:             c.or       a0, a4
2689:             bltu       a1, s1, 2709f
                  c.mv       s1, s6
2691:             nop
                  andi       s6, a2, -906
                  sltiu      s10, a5, 743
                  csrrci     a5, 0x340, 29
                  csrrci     s5, 0x340, 1
                  and        a7, t6, s8
                  .4byte 0x00100073 # ebreak
                  c.beqz     s0, 2714f
                  sra        t5, s1, gp
                  c.andi     a5, -24
                  c.andi     s0, -12
                  c.sub      a2, a5
                  c.and      a1, a0
                  beq        t0, tp, 2712f
                  c.and      a0, a0
                  csrrw      s6, 0x340, t1
                  mulh       t0, s4, s0
                  bge        tp, t2, 2727f
2709:             c.ebreak;c.nop;
                  mulhsu     a1, t6, s10
                  mulhu      a0, s6, s5
2712:             csrrwi     s1, 0x340, 19
                  c.lui      a4, 28
2714:             c.or       a5, a3
                  srai       tp, s11, 3
                  c.slli     s11, 5
                  c.addi     a2, 5
                  xor        a0, s9, a3
                  c.srli     s0, 20
                  csrrs      a5, 0x340, s5
                  c.mv       s11, t3
                  csrrsi     s4, 0x340, 21
                  c.sub      s0, a5
                  mulh       t0, a4, t0
                  andi       t3, s7, -476
                  bgeu       tp, zero, 2746f
2727:             andi       a1, t5, 217
                  srl        s6, a5, s1
                  xori       s3, zero, 702
                  mulhsu     s2, s3, s11
                  bgeu       a5, s7, 2742f
                  addi       t3, s10, -468
                  c.slli     a7, 2
                  bgeu       a2, s6, 2746f
                  c.sub      a1, a4
                  bgeu       s5, zero, 2744f
                  and        t3, zero, a6
                  slti       s3, s1, 676
                  srl        t5, a3, gp
                  c.bnez     a0, 2759f
                  sub        s6, ra, t1
2742:             c.srai     a2, 31
                  srli       t1, sp, 25
2744:             c.add      a6, a2
                  bgeu       a4, s4, 2746f
2746:             add        s2, s11, s2
                  sltu       a3, t5, s4
                  srl        zero, t3, s5
                  srai       a4, s7, 23
                  andi       s10, s4, -909
                  beq        a0, s0, 2756f
                  slt        t5, zero, gp
                  xori       s11, t2, -644
                  sltu       t4, t6, s0
                  andi       t3, s4, -70
2756:             lui        a2, 742720
                  c.addi     s0, -26
                  c.ebreak;c.nop;
2759:             c.addi     t5, 3
                  bltu       s8, a3, 2772f
                  srai       s4, s2, 10
                  sltu       s1, a5, gp
                  c.or       a3, s1
                  beq        a1, t2, 2768f
                  div        t3, a0, t0
                  sltiu      ra, s10, -648
                  and        a7, t1, tp
2768:             mulhu      t3, s9, s1
                  srli       s2, a4, 29
                  xor        t5, s0, a5
                  or         s11, s4, t6
2772:             sll        a4, a7, a4
                  remu       s5, gp, a6
                  bne        s0, s1, 2787f
                  and        t2, a1, t6
                  csrrc      tp, 0x340, gp
                  lui        t4, 848977
                  c.lui      s7, 11
                  bge        s6, s6, 2780f
2780:             add        a7, s10, a0
                  csrrsi     t0, 0x340, 21
                  c.beqz     a4, 2792f
                  bne        s4, a7, 2792f
                  c.bnez     a2, 2797f
                  bltu       gp, t0, 2794f
                  sltiu      s7, t2, 554
2787:             c.addi     s0, 5
                  xor        t2, t5, s11
                  slli       a2, a2, 2
                  sub        a4, s7, t1
                  mulhu      a0, s10, s9
2792:             mul        s10, s2, a7
                  slli       t0, a6, 4
2794:             nop
                  c.andi     a4, -25
                  c.and      a5, s1
2797:             c.srai     a5, 12
                  sub        s3, s3, s10
                  sra        t2, s0, t1
                  c.addi     gp, 2
                  mulh       a3, s10, t1
                  csrrs      a2, 0x340, s11
                  andi       ra, a5, 259
                  ori        a5, a7, 442
                  add        t5, gp, t2
                  c.srai     a3, 26
                  blt        sp, t2, 2822f
                  or         a2, s11, t4
                  addi       a5, t0, 710
                  mulh       t4, a7, s11
                  csrrci     s4, 0x340, 24
                  csrrwi     a0, 0x340, 27
                  c.slli     a3, 21
                  andi       a5, sp, 906
                  srl        s7, s10, s10
                  c.srai     s1, 15
                  mulhu      a5, a0, s9
                  add        t2, tp, sp
                  ori        t1, t5, -178
                  c.and      a2, a1
                  c.bnez     a2, 2831f
2822:             mulhsu     s6, a2, s7
                  div        s11, s11, s10
                  csrrci     zero, 0x340, 2
                  sltu       t4, sp, a0
                  auipc      a5, 636559
                  sltiu      s10, s5, -258
                  sll        a0, s1, tp
                  c.andi     a1, 3
                  nop
2831:             srli       t4, s11, 1
                  lui        a6, 687826
                  ori        gp, s2, -918
                  c.beqz     s1, 2850f
                  csrrs      t2, 0x340, a7
                  csrrsi     s6, 0x340, 1
                  slt        zero, t3, a1
                  add        a7, s10, s5
                  c.sub      a3, s1
                  c.srli     s1, 5
                  srl        s2, s5, s3
                  beq        s11, s3, 2857f
                  c.or       a0, s1
                  c.or       a3, s0
                  c.bnez     a2, 2855f
                  bge        a3, a4, 2864f
                  c.sub      a3, a3
                  csrrsi     a4, 0x340, 12
                  c.slli     s1, 31
2850:             c.srai     a5, 17
                  xori       s7, ra, -146
                  add        s10, a2, gp
                  div        s0, zero, t2
                  sll        s0, zero, s8
2855:             c.ebreak;c.nop;
                  andi       s10, a6, -919
2857:             sltu       tp, a7, tp
                  bgeu       a7, tp, 2870f
                  lui        t3, 438906
                  srl        a0, gp, s3
                  srli       tp, t2, 28
                  c.and      a1, a5
                  sltiu      a6, zero, 982
2864:             andi       t2, a1, -635
                  csrrc      t3, 0x340, sp
                  xori       a2, t3, 388
                  csrrci     s3, 0x340, 1
                  mulh       t5, sp, a2
                  c.sub      s0, a5
2870:             slli       t1, t4, 19
                  remu       t3, sp, a5
                  mulh       t6, s3, t4
                  c.and      a5, a3
                  ori        s2, s5, -622
                  slt        t0, ra, t1
                  la         t4, region_3+141 #start riscv_load_store_rand_instr_stream_6
                  sb         a6, -28(t4)
                  lbu        s6, 212(t4)
                  or         zero, a4, s6
                  sb         a6, -38(t4)
                  c.lui      s10, 27
                  lhu        s6, 135(t4)
                  slt        s6, s5, t5
                  lbu        tp, 6(t4)
                  csrrc      zero, 0x340, a3
                  ori        a7, s3, 479
                  sb         a2, 101(t4)
                  divu       s11, sp, s5
                  sb         t3, -10(t4)
                  srl        t0, gp, s1
                  lb         s6, -36(t4)
                  lbu        t2, -6(t4)
                  lb         s10, 133(t4)
                  lbu        s1, -115(t4)
                  c.srli     a2, 29
                  lbu        a6, 22(t4)
                  csrrwi     s11, 0x340, 24
                  nop
                  andi       a7, t1, 288
                  lbu        s7, 19(t4)
                  c.mv       tp, s2
                  c.srai     s0, 1
                  csrrc      s3, 0x340, s10
                  lhu        a1, 91(t4)
                  mulhsu     s0, t5, t6
                  sb         a7, 252(t4)
                  lb         s1, 26(t4)
                  andi       ra, a0, -605
                  c.ebreak;c.nop;
                  lbu        s6, -77(t4)
                  c.nop
                  lbu        a6, -38(t4)
                  lw         s4, 183(t4)
                  lbu        a0, 180(t4)
                  c.li       s10, 21
                  lh         s11, -119(t4)
                  div        s3, a6, a6
                  c.nop
                  xori       a0, s0, -158
                  sh         s0, 31(t4)
                  c.xor      a2, a4
                  lbu        s6, -98(t4)
                  csrrci     s5, 0x340, 18
                  ori        s3, tp, 882
                  lb         s6, 174(t4)
                  ori        s0, s3, 1006
                  sb         s8, 235(t4)
                  sh         a2, -55(t4)
                  sub        s4, t2, t0
                  lbu        a7, 160(t4)
                  lui        t0, 200020
                  lbu        a5, 185(t4)
                  slli       gp, s2, 6
                  sb         t1, 101(t4) #end riscv_load_store_rand_instr_stream_6
                  andi       t2, s10, 63
                  sll        a0, a3, s1
                  c.and      a0, a3
                  sltiu      s6, a3, 752
                  xor        t1, a7, s11
                  csrrw      t0, 0x340, s11
                  bltu       t6, a4, 2885f
                  csrrsi     a7, 0x340, 3
                  c.beqz     a4, 2899f
2885:             ori        tp, a3, -435
                  c.xor      a5, a1
                  c.add      a6, s3
                  divu       s2, s10, s7
                  remu       t5, ra, sp
                  csrrsi     ra, 0x340, 25
                  c.andi     a5, 13
                  c.nop
                  slli       a2, s8, 29
                  c.add      a1, s3
                  csrrsi     ra, 0x340, 22
                  c.li       a2, 23
                  xori       t6, t2, -733
                  mulhsu     a6, gp, s9
2899:             .4byte 0x00100073 # ebreak
                  c.li       s5, -21
                  srai       a0, s8, 30
                  sra        a3, s2, t5
                  csrrsi     gp, 0x340, 7
                  sub        t1, t1, sp
                  c.andi     a5, -32
                  csrrci     t0, 0x340, 18
                  srli       s3, ra, 4
                  csrrw      t5, 0x340, a3
                  sub        a1, a5, a3
                  beq        t4, zero, 2925f
                  slt        t6, s7, t5
                  auipc      t4, 116265
                  mulhu      ra, s4, tp
                  slli       t6, s0, 3
                  beq        a3, s0, 2934f
                  csrrc      a2, 0x340, t2
                  beq        a4, a0, 2935f
                  xor        t6, a6, a5
                  ori        s2, t6, 276
                  andi       a3, a3, 23
                  remu       t6, s6, s3
                  blt        a7, a1, 2940f
                  c.srli     s0, 17
                  or         a0, a4, a5
2925:             mulhsu     a3, s3, t0
                  srli       a4, s5, 12
                  slti       s7, ra, -534
                  c.lui      gp, 29
                  c.ebreak;c.nop;
                  auipc      s7, 403676
                  c.or       a1, s0
                  beq        ra, s5, 2940f
                  slti       s4, a7, 759
2934:             srl        t6, a2, zero
2935:             sltu       t5, s11, t2
                  slt        gp, s4, s8
                  xori       s3, gp, -554
                  c.beqz     a0, 2951f
                  csrrci     zero, 0x340, 6
2940:             csrrwi     s5, 0x340, 7
                  c.srai     a5, 13
                  csrrwi     t6, 0x340, 13
                  c.add      t0, s5
                  sltu       a0, a5, t6
                  srl        s5, t4, s10
                  srli       t5, ra, 3
                  slti       s7, s4, 668
                  c.srai     s0, 30
                  c.andi     a5, -23
                  bgeu       zero, s9, 2954f
2951:             c.mv       s1, s11
                  auipc      t4, 653251
                  c.xor      s1, s0
2954:             and        tp, s0, s1
                  div        t4, s3, s3
                  div        ra, a1, zero
                  srl        tp, t1, s10
                  mulhu      t3, s10, a1
                  c.add      a0, s5
                  c.nop
                  srl        a7, a0, a7
                  rem        s10, a3, s1
                  xor        zero, s11, a2
                  c.addi     s1, 27
                  slli       a7, tp, 8
                  c.beqz     a1, 2981f
                  bge        a1, a1, 2977f
                  srai       s11, s1, 9
                  c.srai     s0, 31
                  c.bnez     s1, 2980f
                  mulhsu     a3, s10, s4
                  rem        a1, a2, t6
                  andi       gp, s10, -20
                  slt        zero, a4, s7
                  c.andi     a3, -13
                  srl        a3, gp, t2
2977:             c.beqz     a0, 2986f
                  csrrw      s0, 0x340, a2
                  lui        s7, 632924
2980:             mulhu      s6, t1, a6
2981:             nop
                  or         s1, s4, s9
                  c.srli     a0, 3
                  csrrwi     t5, 0x340, 31
                  remu       a4, t0, s9
2986:             c.sub      a0, a4
                  srai       zero, t0, 24
                  mulhsu     a4, a6, s5
                  andi       s5, ra, -322
                  .4byte 0x00100073 # ebreak
                  blt        s8, s8, 3003f
                  beq        s3, t4, 3011f
                  csrrwi     a6, 0x340, 31
                  nop
                  and        s0, sp, t0
                  c.mv       s5, s10
                  mulhu      a5, s2, t1
                  lui        tp, 291569
                  c.add      s5, s11
                  rem        tp, a4, a4
                  beq        s6, s3, 3021f
                  mulh       s10, s0, s7
3003:             auipc      a7, 379441
                  beq        ra, gp, 3016f
                  bge        t3, s0, 3023f
                  srli       a7, tp, 3
                  c.beqz     s0, 3020f
                  csrrw      s10, 0x340, s7
                  nop
                  sltu       t6, t6, tp
3011:             slli       tp, s5, 9
                  csrrw      a4, 0x340, a5
                  mulhsu     s5, t1, s11
                  c.ebreak;c.nop;
                  c.addi     s1, -4
3016:             c.andi     a5, -2
                  auipc      gp, 318731
                  slt        s5, gp, s0
                  c.or       s0, s0
3020:             c.andi     s0, 15
3021:             srli       gp, a5, 31
                  c.sub      a1, a3
3023:             csrrc      a2, 0x340, a0
                  or         s10, s2, s3
                  srl        s1, ra, a4
                  c.andi     s0, 26
                  c.andi     s1, -10
                  slti       s10, s2, 732
                  c.andi     a4, 17
                  or         t3, sp, s9
                  bge        gp, s0, 3032f
3032:             c.slli     s6, 10
                  sub        a0, s10, t4
                  rem        a1, tp, s4
                  slli       s7, s4, 9
                  addi       a1, t1, -43
                  c.bnez     s0, 3041f
                  c.xor      a1, s0
                  sub        ra, s5, t0
                  csrrc      ra, 0x340, t1
3041:             remu       t3, t1, t4
test_done:        
                  li gp, 1
                  ecall
sub_2:            c.nop
                  addi       sp, sp, -64
                  sw         gp, 4(sp)
                  sra        s7, a3, t4
                  sltu       s3, a3, a5
                  addi       ra, s9, 546
                  srli       s4, a5, 20
                  xor        s11, a0, t6
                  mulhsu     t5, s2, a0
                  c.mv       t0, s5
                  andi       tp, t2, 383
                  remu       t3, sp, s3
                  la         a2, region_1+14192 #start riscv_load_store_rand_instr_stream_1
                  slli       a1, t1, 28
                  lb         zero, 287(a2)
                  lbu        t3, 538(a2)
                  csrrsi     a3, 0x340, 26
                  c.srai     a0, 13
                  c.ebreak;c.nop;
                  lb         s3, -637(a2)
                  lh         a6, -276(a2)
                  lb         zero, -282(a2)
                  andi       s6, a3, 597
                  srl        ra, a4, ra
                  sb         a6, 49(a2)
                  srai       s2, s6, 3
                  c.srai     a0, 28
                  lbu        a4, 135(a2)
                  sb         tp, 678(a2)
                  srli       s3, t4, 6
                  sh         s3, 300(a2)
                  c.andi     a0, 1
                  .4byte 0x00100073 # ebreak
                  sltu       a3, t4, ra
                  andi       t3, gp, 932
                  srl        s0, tp, t0
                  mulh       s5, s2, s8
                  c.lui      s6, 20
                  rem        s3, a0, s5
                  csrrc      a0, 0x340, s2
                  auipc      a6, 947258
                  lb         t2, -95(a2)
                  .4byte 0x00100073 # ebreak
                  srli       s4, a6, 22
                  slli       a7, s11, 30
                  slli       gp, t6, 0
                  lh         tp, -852(a2)
                  c.srli     s0, 8
                  sw         t3, 496(a2)
                  srai       a7, s9, 25
                  sb         s4, 237(a2)
                  add        a4, s8, s9
                  lb         s6, -101(a2) #end riscv_load_store_rand_instr_stream_1
                  la         tp, region_4+259 #start riscv_load_store_rand_instr_stream_0
                  csrrs      s10, 0x340, s5
                  slt        a6, gp, a5
                  andi       zero, ra, -487
                  mulhu      zero, a5, tp
                  lw         a3, -3(tp)
                  lhu        s10, 11(tp)
                  c.sub      s1, s0
                  rem        s5, tp, t3
                  srli       s10, t0, 31
                  srl        s3, a1, tp
                  lh         a1, -9(tp)
                  c.lui      t5, 17
                  c.or       a3, s0
                  or         t1, s11, a0
                  sltu       s10, tp, s2
                  csrrw      s7, 0x340, t2
                  lb         t1, 16(tp)
                  .4byte 0x00100073 # ebreak
                  lb         s10, -16(tp)
                  xor        s6, s11, t2
                  lb         a6, -14(tp)
                  csrrci     a3, 0x340, 12
                  sub        a2, a2, s5
                  c.addi     a2, -6
                  lb         a2, 15(tp)
                  lbu        s7, 16(tp)
                  c.srli     a5, 22
                  c.addi     s1, 12
                  lhu        s0, -15(tp)
                  csrrc      a6, 0x340, t0
                  sra        s10, gp, s8
                  xori       s5, t3, 276
                  nop
                  mulhu      t6, s5, a5
                  mulh       t2, tp, t5
                  mulhu      s0, a5, s7
                  lhu        t2, -1(tp) #end riscv_load_store_rand_instr_stream_0
                  la         t6, region_1+6299 #start riscv_load_store_rand_instr_stream_2
                  lw         a6, 237(t6)
                  lb         t3, 142(t6)
                  sll        s2, a6, a7
                  c.ebreak;c.nop;
                  sb         s10, -202(t6)
                  sb         a0, -222(t6)
                  lbu        tp, 14(t6)
                  slli       a0, t5, 4
                  sb         gp, 158(t6)
                  csrrs      t2, 0x340, s0
                  lbu        t4, 41(t6)
                  lb         s4, 8(t6)
                  sb         s8, -184(t6)
                  c.addi     a2, -19
                  lbu        a7, -212(t6)
                  sb         a1, 89(t6)
                  sb         ra, 156(t6)
                  lb         gp, 133(t6)
                  lh         s3, 111(t6)
                  lb         zero, 37(t6)
                  lbu        s7, 82(t6)
                  srli       s1, a3, 24
                  slti       zero, ra, 158
                  csrrci     a0, 0x340, 21
                  rem        a1, a3, zero
                  lbu        t2, -62(t6)
                  sb         ra, -56(t6)
                  csrrc      zero, 0x340, s10
                  lbu        gp, 245(t6)
                  lb         a1, 223(t6)
                  csrrsi     t0, 0x340, 19
                  sb         ra, -148(t6) #end riscv_load_store_rand_instr_stream_2
                  la         t3, region_0+1963 #start riscv_load_store_rand_instr_stream_3
                  lbu        a7, 479(t3)
                  sh         a4, -143(t3)
                  c.add      s10, tp
                  lhu        a6, -23(t3)
                  lbu        t5, -860(t3)
                  lhu        s10, -113(t3)
                  sll        a1, s11, a2
                  lh         s1, -929(t3)
                  lb         a1, 677(t3)
                  sub        a7, t3, t0
                  or         s7, tp, sp
                  lb         a0, 395(t3)
                  add        t2, s7, sp
                  sb         s11, 679(t3)
                  srli       a3, a1, 2
                  sb         a2, -220(t3)
                  c.add      a2, a0
                  c.or       s1, a5
                  sub        a3, s9, a1
                  c.srai     a2, 18
                  sh         t2, -513(t3)
                  lbu        s2, 166(t3)
                  lbu        t4, -16(t3)
                  lbu        t4, -5(t3)
                  lb         a7, -1004(t3)
                  mulhsu     a0, t2, sp
                  sh         s0, 629(t3)
                  c.sub      a0, a3
                  c.li       s2, 0
                  sh         s7, -797(t3)
                  lbu        s7, 921(t3)
                  or         t5, t2, a0
                  or         ra, a0, a6
                  lhu        a4, 623(t3)
                  ori        a5, a0, -103
                  lhu        s11, -965(t3)
                  lbu        ra, -484(t3)
                  rem        t2, t5, s11
                  lhu        s10, -259(t3)
                  lb         s10, -168(t3)
                  lbu        s3, -113(t3)
                  andi       t4, a7, 24
                  csrrc      a7, 0x340, a7
                  sh         s2, 923(t3) #end riscv_load_store_rand_instr_stream_3
                  la         s1, region_3+389 #start load_store_instr_stream_1
                  la         t3, region_3+436 #start load_store_instr_stream_3
                  la         t6, region_3+489 #start load_store_instr_stream_0
                  sb         a3, -194(s1)
                  lb         a0, -10(t3)
                  lw         ra, -53(t6)
                  la         s6, region_3+81 #start load_store_instr_stream_2
                  lb         s0, -1(t3)
                  sh         a3, -159(s1)
                  sh         a3, 4(t3)
                  lb         a6, 2(s6)
                  sb         a1, -5(t3)
                  lbu        s0, -7(t6)
                  lhu        a3, 7(s6)
                  sb         ra, -2(t3)
                  lw         t4, -37(t6)
                  lh         a2, -59(t6)
                  lb         gp, -3(t3)
                  sb         t0, -61(t6)
                  lbu        s3, 8(s1)
                  lh         a7, 1(t6)
                  lh         a4, 10(t3)
                  lhu        s2, 16(t3)
                  lb         a7, 2(t6)
                  lb         a2, 14(t3) #end load_store_instr_stream_3
                  sh         a2, -13(s6)
                  lbu        t4, 45(s1)
                  lbu        zero, 5(s6)
                  lbu        s11, -202(s1)
                  sb         t3, -10(s6)
                  lb         s7, -50(t6)
                  sb         s3, -50(s1) #end load_store_instr_stream_1
                  lbu        t5, -12(s6) #end load_store_instr_stream_2
                  lb         t5, -28(t6) #end load_store_instr_stream_0
                  addi       s0, zero, -7 #init loop 1 counter
                  div        t6, s0, s8
                  addi       s10, zero, 6 #init loop 1 limit
                  sltiu      a4, s6, -802
sub_2_18_1_t:     csrrsi     t2, 0x340, 27
                  csrrw      a2, 0x340, t0
                  xor        s11, s9, s1
                  addi       s0, s0, 3 #update loop 1 counter
                  addi       a3, zero, 1 #init loop 0 counter
                  slti       t6, sp, 43
                  addi       zero, zero, 0 #init loop 0 limit
sub_2_18_0_t:     c.or       a1, a0
                  addi       a3, a3, -1 #update loop 0 counter
                  c.slli     s11, 10
                  c.bnez     a3, sub_2_18_0_t #branch for loop 0
                  srl        a2, t2, s10
                  bltu       s0, s10, sub_2_18_1_t #branch for loop 1
                  c.andi     a2, 31
                  la         t0, region_0+3987 #start load_store_instr_stream_1
                  sb         s9, 49(t0)
                  la         gp, region_4+191 #start load_store_instr_stream_2
                  sh         zero, -93(t0)
                  lbu        a7, 164(gp)
                  lbu        a5, 67(t0)
                  la         t4, region_2+4717 #start load_store_instr_stream_0
                  lw         s11, -169(t4)
                  sb         a3, 188(gp)
                  sb         s2, -201(t0)
                  sb         t6, 224(t4)
                  lh         s0, 61(t0)
                  lb         a2, -7(t0)
                  sb         s8, 247(t4)
                  sw         a1, 161(gp)
                  lh         s3, -41(t0)
                  sb         a7, -53(gp)
                  lw         zero, -21(t4)
                  lbu        ra, -188(t4)
                  lbu        s4, -111(t0)
                  lb         a7, 231(gp)
                  lbu        a7, -102(t4)
                  sb         a0, -142(gp)
                  lb         s11, 75(t0) #end load_store_instr_stream_1
                  lbu        s6, -146(t4)
                  sb         a6, 54(gp) #end load_store_instr_stream_2
                  lbu        a6, -254(t4)
                  sh         s0, 237(t4)
                  lbu        zero, 24(t4) #end load_store_instr_stream_0
sub_2_5:          jal        gp, 1f
0:                jal        t1, 4f
1:                c.jal      16f
2:                jal        t0, 25f
3:                c.j        13f
4:                c.j        9f
5:                jal        ra, 8f
6:                jal        ra, 17f
7:                c.j        24f
8:                c.jal      2b
9:                c.jal      7b
10:               jal        t1, 11f
11:               c.j        23f
12:               jal        t0, 19f
13:               c.j        22f
14:               c.jal      15f
15:               c.j        21f
16:               c.jal      20f
17:               jal        ra, 5b
18:               c.j        14b
19:               c.jal      0b
20:               jal        ra, 12b
21:               c.j        3b
22:               jal        tp, 10b
23:               c.j        6b
24:               c.j        18b
25:               rem        s3, gp, s11
sub_2_7:          jal        gp, 10f
0:                jal        a4, 20f
1:                jal        t1, 18f
2:                c.jal      0b
3:                c.j        24f
4:                c.jal      13f
5:                c.j        2b
6:                c.j        27f
7:                jal        s11, 9f
8:                jal        a1, 25f
9:                c.j        29f
10:               jal        ra, 26f
11:               c.jal      8b
12:               c.jal      19f
13:               jal        ra, 17f
14:               jal        t1, 16f
15:               c.j        1b
16:               c.j        23f
17:               jal        ra, 14b
18:               c.jal      11b
19:               c.jal      5b
20:               c.j        15b
21:               c.j        28f
22:               c.jal      6b
23:               c.jal      22b
24:               jal        t1, 7b
25:               jal        a4, 3b
26:               jal        s2, 4b
27:               c.j        21b
28:               c.jal      12b
29:               sub        s10, s2, gp
                  la         s3, region_4+53 #start load_store_instr_stream_1
                  la         s7, region_0+1799 #start load_store_instr_stream_0
                  lb         s4, 8(s3)
                  sb         a4, -242(s7)
                  lb         ra, -9(s3)
                  sw         a1, -207(s7)
                  lhu        tp, -15(s3)
                  sb         a6, -9(s3)
                  lbu        ra, -16(s3)
                  sb         s9, -9(s3)
                  lb         gp, -75(s7)
                  lbu        s5, 68(s7)
                  lb         tp, 229(s7)
                  lbu        t1, -12(s3) #end load_store_instr_stream_1
                  lbu        gp, 139(s7) #end load_store_instr_stream_0
                  la         a5, region_1+13109 #start riscv_hazard_instr_stream_0
                  sb         ra, 424(a5)
                  lbu        t6, 534(a5)
                  lw         a2, 619(a5)
                  sh         ra, -351(a5)
                  sb         t5, 400(a5)
                  sb         t5, 344(a5)
                  lbu        t5, 697(a5)
                  sh         gp, -705(a5)
                  lhu        ra, 141(a5)
                  lw         ra, 659(a5)
                  sb         t6, 882(a5)
                  sb         gp, -48(a5)
                  c.lui      t5, 18
                  lhu        t5, -729(a5)
                  slti       ra, ra, 969
                  sb         t6, 358(a5)
                  add        t5, t2, gp
                  sb         a2, 268(a5)
                  sra        ra, ra, t5
                  lbu        ra, 118(a5)
                  sb         gp, 586(a5)
                  lb         a2, 753(a5)
                  mul        t5, t5, ra
                  mulhsu     gp, ra, gp
                  lb         ra, 642(a5)
                  sh         t6, 753(a5)
                  sb         t2, 181(a5)
                  sh         t6, 985(a5)
                  sb         t5, 418(a5)
                  add        t2, t2, t5
                  sb         gp, 839(a5)
                  nop
                  lb         ra, -148(a5)
                  sll        ra, t5, t6
                  lb         t6, 800(a5)
                  mulh       t6, ra, ra
                  lh         a2, -171(a5)
                  auipc      t5, 886068
                  c.xor      a2, a2
                  sb         t5, -34(a5) #end riscv_hazard_instr_stream_0
                  la         t3, region_3+496 #start load_store_instr_stream_2
                  la         a4, region_4+209 #start load_store_instr_stream_4
                  la         gp, region_0+2167 #start load_store_instr_stream_3
                  la         s2, region_1+12425 #start load_store_instr_stream_1
                  lb         s6, -8(a4)
                  la         s1, region_2+5828 #start load_store_instr_stream_0
                  lbu        a6, -28(s2)
                  lbu        a5, 537(s1)
                  sw         t5, 31(a4)
                  sb         ra, -52(s2)
                  lbu        a0, -357(t3)
                  sb         s6, -370(gp)
                  lbu        s10, 667(s1)
                  sh         s1, -29(a4)
                  lbu        t6, -928(gp)
                  sb         tp, -300(t3)
                  sh         s10, 942(s1)
                  lbu        s10, -19(s2)
                  lb         s5, -887(s1)
                  lhu        s5, -7(s2)
                  sb         zero, -20(s2)
                  sw         zero, -17(a4)
                  lb         s4, 415(gp)
                  lb         t5, -51(s2)
                  lb         t4, -733(gp)
                  lw         a7, 116(s1)
                  sb         s1, -93(t3)
                  lb         s11, -24(a4) #end load_store_instr_stream_4
                  sh         ra, -225(gp)
                  lw         zero, -33(s2)
                  sh         t2, -18(t3)
                  lb         s11, 964(s1)
                  lbu        a6, -589(s1)
                  sb         s10, 438(gp)
                  lbu        a3, 39(s2)
                  lbu        t1, -247(t3)
                  lb         a3, 250(gp) #end load_store_instr_stream_3
                  lbu        t6, -46(s2) #end load_store_instr_stream_1
                  sb         t6, -183(t3) #end load_store_instr_stream_2
                  sb         s10, 92(s1) #end load_store_instr_stream_0
                  addi       a6, zero, 6 #init loop 1 counter
                  addi       t2, zero, 5 #init loop 1 limit
sub_2_17_1_t:     sll        t0, s6, t4
                  addi       a6, a6, -6 #update loop 1 counter
                  addi       s0, zero, -5 #init loop 0 counter
                  addi       zero, zero, 0 #init loop 0 limit
sub_2_17_0_t:     sltiu      a2, s5, 859
                  addi       s0, s0, 5 #update loop 0 counter
                  c.beqz     s0, sub_2_17_0_t #branch for loop 0
                  bge        a6, t2, sub_2_17_1_t #branch for loop 1
                  c.ebreak;c.nop;
                  la         a2, region_3+323 #start load_store_instr_stream_2
                  la         a5, region_3+368 #start load_store_instr_stream_0
                  la         a1, region_3+119 #start load_store_instr_stream_1
                  lbu        s6, -76(a2)
                  lh         t1, 117(a1)
                  lb         a7, -58(a5)
                  sb         s1, 376(a1)
                  lw         s5, 61(a2)
                  lb         t3, -166(a2)
                  sb         tp, 256(a1)
                  lbu        t2, 166(a1)
                  sb         sp, -34(a5)
                  lbu        s4, -140(a2)
                  lhu        t1, 52(a5)
                  lbu        s2, -76(a2)
                  sh         a7, 249(a1)
                  sb         a0, -33(a2)
                  lb         t3, 1(a5)
                  sb         s6, 18(a2)
                  lb         a3, -124(a2)
                  sb         s0, -49(a5)
                  lhu        a6, 60(a5)
                  lbu        t4, 268(a1)
                  lhu        s6, 11(a1)
                  lbu        s11, 50(a1)
                  lbu        tp, -11(a2) #end load_store_instr_stream_2
                  lhu        t6, -10(a5)
                  sb         s11, -27(a5)
                  lb         t0, 277(a1)
                  lh         s4, -48(a5)
                  lbu        t4, -59(a1) #end load_store_instr_stream_1
                  lb         t4, -9(a5) #end load_store_instr_stream_0
                  la         t6, region_3+240 #start riscv_hazard_instr_stream_2
                  sll        s10, s4, s10
                  slli       t5, s10, 25
                  lbu        s1, -12(t6)
                  csrrci     s10, 0x340, 28
                  c.sub      s1, a5
                  lbu        s1, 11(t6)
                  mulhsu     s1, t5, a5
                  srli       a5, s10, 12
                  lui        a5, 940248
                  csrrw      a5, 0x340, a7
                  c.mv       s1, s4
                  lbu        s10, 11(t6)
                  ori        s4, a7, 21
                  c.nop
                  sh         s4, 2(t6)
                  lbu        s10, -7(t6)
                  lbu        t5, 7(t6)
                  c.addi     s4, -20
                  lb         a7, 12(t6)
                  lw         s1, -16(t6)
                  slt        s1, a7, t5
                  lb         a7, -7(t6)
                  lbu        s10, -11(t6)
                  nop
                  c.srai     a5, 10
                  xor        t5, t5, s1
                  lbu        s4, 5(t6)
                  lh         s4, -12(t6)
                  lbu        t5, -13(t6)
                  ori        a7, a5, 258
                  lb         s4, 13(t6)
                  c.nop
                  c.lui      s4, 27
                  sh         s10, -10(t6)
                  lh         a5, 2(t6)
                  sb         a5, 0(t6)
                  lhu        s10, -16(t6)
                  auipc      s10, 274007
                  lh         a7, -6(t6)
                  lb         s10, 11(t6) #end riscv_hazard_instr_stream_2
                  addi       t4, zero, -4 #init loop 0 counter
                  c.nop
                  c.andi     a1, -6
                  addi       ra, zero, 10 #init loop 0 limit
                  and        t5, zero, s5
sub_2_16_0_t:     c.or       a0, a0
                  andi       s7, tp, -754
                  addi       t4, t4, 9 #update loop 0 counter
                  nop
                  c.ebreak;c.nop;
                  or         s3, a7, a1
                  c.xor      a5, a2
                  c.andi     a2, -21
                  sra        s4, s10, a6
                  bltu       t4, ra, sub_2_16_0_t #branch for loop 0
                  c.andi     a0, 21
                  la         t2, region_4+3323 #start load_store_instr_stream_2
                  la         s2, region_4+1207 #start load_store_instr_stream_0
                  la         s5, region_4+3448 #start load_store_instr_stream_3
                  lbu        s7, -28(t2)
                  lb         t4, 398(s5)
                  lb         t6, 457(s5)
                  sb         t4, -1016(s2)
                  sh         gp, 13(t2)
                  lb         s3, 36(t2)
                  lb         s0, -48(t2)
                  lbu        t3, -994(s2)
                  sh         s11, -501(s2)
                  lb         s7, 8(t2)
                  lh         ra, 612(s5)
                  la         s6, region_4+2431 #start load_store_instr_stream_1
                  sh         t3, -440(s5)
                  lb         a6, 222(s6)
                  sb         t4, -339(s5)
                  lb         zero, -40(t2)
                  lbu        a1, -901(s5)
                  sb         a7, -96(s6)
                  lbu        s10, -12(s5)
                  lbu        a2, 530(s2)
                  lb         a1, -36(s6)
                  lb         t6, -97(s6)
                  lbu        s1, -14(t2)
                  sb         a1, -42(s6)
                  lbu        t6, -78(s6)
                  sb         ra, -1019(s5) #end load_store_instr_stream_3
                  lbu        a7, -195(s6)
                  lbu        t1, 10(t2) #end load_store_instr_stream_2
                  lbu        a6, -69(s6) #end load_store_instr_stream_1
                  sb         s11, 176(s2) #end load_store_instr_stream_0
                  la         s10, region_1+1100 #start riscv_hazard_instr_stream_1
                  c.andi     s1, -2
                  c.slli     s2, 13
                  mulh       s11, s1, s11
                  lb         a5, -227(s10)
                  lhu        s1, -92(s10)
                  sb         s2, -141(s10)
                  sb         s11, -114(s10)
                  sltiu      a5, s1, -261
                  sh         s4, -108(s10)
                  auipc      s0, 691150
                  lbu        s11, 120(s10)
                  lbu        s2, -169(s10)
                  nop
                  remu       s1, s2, a5
                  c.mv       s11, s1
                  or         s4, s0, s2
                  srai       s2, s0, 7
                  sh         s0, 34(s10)
                  lb         s1, -105(s10)
                  c.or       s0, s1
                  sb         a5, 195(s10)
                  mulhsu     s1, s1, a5
                  lh         s0, -190(s10)
                  srli       s0, s1, 30
                  nop
                  lbu        s4, 11(s10)
                  sb         s4, -19(s10)
                  sw         s0, 124(s10)
                  mulh       s2, s0, a5
                  sh         s11, -4(s10)
                  sll        s1, a5, s2
                  lb         s2, -78(s10)
                  c.li       s11, -1
                  ori        s11, s1, 313
                  c.li       a5, 24
                  lbu        s4, 71(s10)
                  csrrw      s11, 0x340, s11
                  sw         s4, -116(s10)
                  lbu        s1, 185(s10)
                  sw         s11, -72(s10)
                  lbu        s0, 163(s10)
                  srai       s4, s0, 9
                  slt        s4, a5, s11
                  lbu        s1, -101(s10)
                  csrrci     s2, 0x340, 2
                  lb         s1, 7(s10) #end riscv_hazard_instr_stream_1
                  bne        sp, sp, 12f
                  xor        s0, a1, a1
                  mul        ra, a6, s11
                  and        a2, t0, s6
                  xor        s5, t4, zero
                  and        a5, t0, a2
                  addi       a5, s7, 552
                  c.srai     a2, 16
                  c.srli     s0, 13
                  or         t0, s5, a7
                  c.bnez     a0, 23f
                  sltu       s7, t3, s10
12:               csrrs      t6, 0x340, gp
                  or         gp, s0, s4
                  sltiu      s1, t6, 127
                  divu       a4, t0, t3
                  csrrw      s3, 0x340, s7
                  nop
                  c.add      t2, s11
                  bltu       s3, ra, 30f
                  c.srli     s1, 20
                  andi       a2, gp, 188
                  c.lui      s7, 26
23:               sra        gp, s4, s9
                  c.and      a3, a2
                  bltu       s10, ra, 32f
                  c.beqz     a3, 31f
                  srl        a7, a1, a7
                  nop
                  mulh       s3, a2, a0
30:               ori        ra, s5, 261
31:               csrrs      s11, 0x340, a5
32:               csrrc      s11, 0x340, a7
                  bne        t1, s4, 36f
                  mulhu      a7, s2, t3
                  blt        a0, t6, 43f
36:               lui        gp, 440233
                  divu       ra, t0, s0
                  csrrw      a1, 0x340, zero
                  c.srli     s0, 28
                  c.lui      a1, 1
                  csrrc      t5, 0x340, s8
                  lui        a7, 1026660
43:               csrrsi     s2, 0x340, 28
                  addi       s1, s11, -483
                  c.and      a3, a1
                  .4byte 0x00100073 # ebreak
                  ori        zero, a7, 387
                  bne        s6, t0, 66f
                  srl        a6, s5, gp
                  csrrs      t1, 0x340, s11
                  add        a6, zero, s3
                  ori        a3, s1, 77
                  and        a2, zero, a1
                  mulhu      a3, a0, t0
sub_2_6:          jal        gp, 5f
0:                c.j        3f
1:                jal        t0, 16f
2:                jal        s4, 15f
3:                c.jal      12f
4:                c.j        6f
5:                jal        s4, 8f
6:                c.jal      14f
7:                jal        t1, 0b
8:                c.j        4b
9:                c.j        10f
10:               c.j        11f
11:               jal        gp, 17f
12:               jal        s6, 1b
13:               c.j        7b
14:               c.jal      13b
15:               c.j        9b
16:               c.jal      2b
17:               c.xor      s0, a3
                  c.or       a2, a2
                  mulhsu     s2, ra, t3
                  sltiu      s5, a1, 240
                  c.bnez     s1, 66f
                  srli       s3, s10, 26
                  c.slli     tp, 15
                  nop
                  srli       s5, gp, 30
                  auipc      t1, 441617
                  c.add      t4, s9
                  csrrci     s3, 0x340, 25
66:               srl        s3, a4, a4
                  c.bnez     a2, 75f
                  c.srai     s1, 17
                  c.slli     s3, 2
                  or         t2, ra, a5
                  slti       s4, a1, -826
                  la         t1, region_4+1973 #start load_store_instr_stream_2
                  la         s4, region_1+12100 #start load_store_instr_stream_1
                  lbu        a7, 903(t1)
                  sb         t4, -380(t1)
                  la         t2, region_3+143 #start load_store_instr_stream_0
                  lbu        a4, -82(s4)
                  sb         s6, -79(s4)
                  lb         t4, 226(t2)
                  lhu        gp, -166(s4)
                  lb         t0, 90(s4)
                  lbu        a5, 17(s4)
                  sh         a6, 263(t2)
                  lbu        s2, 220(t1)
                  lb         a2, 35(t2)
                  lb         s1, -114(s4) #end load_store_instr_stream_1
                  lb         a1, 31(t1)
                  lhu        t5, 293(t1)
                  sb         t1, 90(t2)
                  lbu        gp, 360(t1) #end load_store_instr_stream_2
                  sb         s3, 298(t2) #end load_store_instr_stream_0
                  csrrs      s7, 0x340, t1
                  beq        a2, s0, 88f
                  c.beqz     a1, 84f
75:               c.bnez     a4, 76f
76:               c.andi     a0, -18
                  sub        a6, a7, a2
                  c.or       a1, s1
                  sltiu      s11, a4, -551
                  c.li       s5, -12
                  srli       a7, a0, 27
                  c.and      s1, s1
                  sltiu      a0, s7, -553
84:               rem        a6, ra, a7
                  c.mv       s10, s0
                  mulhsu     s7, s8, s9
                  csrrw      a5, 0x340, sp
88:               lui        s7, 413888
                  c.ebreak;c.nop;
                  c.bnez     s1, 95f
                  mul        s1, t3, s1
                  c.srli     a2, 28
                  c.beqz     a1, 111f
                  beq        s11, s1, 107f
95:               beq        sp, tp, 99f
                  sltu       s1, s1, s2
                  .4byte 0x00100073 # ebreak
                  srli       a3, t6, 5
99:               c.slli     s11, 15
                  addi       t3, a7, 235
                  bne        s5, a0, 116f
                  bgeu       s0, t0, 110f
                  mul        s7, tp, sp
                  beq        s4, s6, 105f
105:              c.srli     a3, 17
                  bge        a1, a5, 107f
107:              mul        gp, t2, t6
                  c.beqz     s1, 114f
                  c.addi     a6, 21
110:              bne        gp, a5, 113f
111:              xori       gp, s0, 339
                  xori       s0, s9, -600
113:              csrrwi     gp, 0x340, 9
114:              srai       t1, s5, 11
                  bne        a4, a4, 118f
116:              c.add      s5, tp
                  sub        ra, t5, s7
118:              sub        s4, s0, ra
                  srai       s0, s4, 31
                  mul        gp, zero, s9
                  c.bnez     s1, 130f
                  csrrwi     a1, 0x340, 22
                  mulhsu     gp, ra, s10
                  remu       a2, t0, a1
                  or         s5, a1, s6
                  andi       s0, s1, 354
                  sltu       a1, a5, t0
                  c.ebreak;c.nop;
                  sltiu      t2, s4, -209
130:              slti       t6, a5, 968
                  .4byte 0x00100073 # ebreak
                  c.mv       t2, a2
                  or         s10, t0, a4
                  sra        s11, t6, t6
                  slli       s4, s6, 1
                  csrrwi     a6, 0x340, 2
                  sll        t2, t2, sp
                  sra        s2, s6, t4
                  rem        s10, t5, a4
                  bgeu       t0, t3, 146f
                  slli       t3, t2, 3
                  lui        t4, 1014003
                  c.slli     s2, 5
                  c.bnez     a2, 156f
                  csrrci     a4, 0x340, 16
146:              bltu       ra, tp, 148f
                  csrrsi     s2, 0x340, 25
148:              auipc      s3, 934217
                  slti       t2, s1, 681
                  blt        a2, gp, 160f
                  beq        a3, s6, 164f
                  csrrci     gp, 0x340, 14
                  srli       s6, a5, 4
                  srai       a4, t6, 13
                  sltiu      s5, a0, 441
156:              xori       zero, a4, 47
                  sub        a7, t1, a5
                  sra        tp, s3, tp
                  c.mv       a4, a1
160:              c.bnez     a0, 175f
                  div        t3, s6, t5
                  c.slli     t0, 29
                  sltu       ra, s8, s9
164:              mulh       s3, s2, s0
                  addi       s11, zero, -459
                  sltu       a2, tp, t5
                  add        s5, a0, s4
                  mul        t3, s11, t3
                  nop
                  c.ebreak;c.nop;
                  c.bnez     a2, 177f
                  c.mv       s10, a1
                  xori       s5, a0, 239
                  div        s1, s2, s2
175:              ori        s5, t3, -977
                  mul        s3, s9, s7
177:              csrrc      s1, 0x340, ra
                  c.nop
                  or         s2, t5, s10
                  c.xor      a2, s0
                  or         zero, a3, s2
                  bne        t5, s10, 192f
                  mulh       tp, s5, a1
                  c.slli     a3, 21
                  slli       t5, t5, 3
                  rem        t1, a4, a6
                  srl        a2, a4, sp
                  and        a3, s4, t2
                  bne        s8, t1, 197f
                  blt        a0, a0, 196f
                  c.sub      a3, a3
192:              slti       s5, s1, 959
                  c.or       a0, a3
                  mul        s3, a1, s9
                  lui        s4, 573303
196:              auipc      gp, 12781
197:              div        t5, tp, a3
                  auipc      s10, 892344
                  c.xor      a4, a3
                  c.srai     a5, 5
                  sll        t2, t0, a7
                  slli       t0, t2, 16
                  c.xor      a3, a0
                  sltiu      zero, s2, 59
                  c.sub      s0, a4
                  csrrsi     gp, 0x340, 0
                  srl        t6, a2, a3
                  beq        s9, gp, 217f
                  c.and      a4, s0
                  csrrw      s6, 0x340, s6
                  sltu       s6, s1, a4
                  xori       t3, s0, 309
                  andi       s1, t5, -708
                  c.add      gp, t5
                  c.srli     a1, 22
                  mul        tp, s4, a4
217:              csrrw      a6, 0x340, s7
                  c.andi     s1, -7
                  divu       t4, t4, s0
                  xor        a0, a3, t6
                  slti       a6, s10, 367
                  divu       s1, zero, a4
                  c.mv       t0, t5
                  remu       zero, s11, zero
                  c.sub      a5, a5
                  csrrc      s0, 0x340, s0
                  c.sub      s1, s0
                  c.sub      s0, a0
                  c.sub      a3, s0
                  c.slli     t3, 26
                  c.andi     a0, 12
                  slli       t6, s3, 12
                  add        t2, a1, t0
                  srl        t3, a0, s4
                  c.and      a4, a0
                  c.or       a2, a2
                  .4byte 0x00100073 # ebreak
                  csrrsi     t6, 0x340, 28
                  rem        gp, s10, gp
                  csrrs      s3, 0x340, t5
                  c.lui      a7, 14
                  c.addi     a0, -30
                  c.xor      a4, a5
                  csrrci     t6, 0x340, 31
                  c.mv       a5, s10
                  ori        a0, s5, -945
                  c.lui      tp, 6
                  c.beqz     s0, 256f
                  bgeu       s3, s3, 259f
                  c.or       a4, a0
                  addi       s7, t1, 328
                  csrrc      t3, 0x340, s7
                  add        s11, tp, a0
                  slli       a0, a2, 24
                  c.bnez     a1, 267f
256:              c.lui      s11, 31
                  c.lui      s6, 20
                  c.slli     t2, 22
259:              addi       t4, t0, -18
                  csrrci     t4, 0x340, 4
                  srai       t1, t3, 7
                  mulhsu     s10, s2, s0
                  c.bnez     a1, 264f
264:              c.mv       s10, ra
                  c.xor      s0, a2
                  c.mv       t0, a3
267:              c.li       s4, -26
                  .4byte 0x00100073 # ebreak
                  mulhsu     a5, s8, t1
                  or         zero, s5, s5
                  mulhu      a0, t6, s11
                  srai       s2, s11, 3
                  ori        s5, s11, -156
                  or         a4, s5, t2
                  sltiu      a1, tp, 631
                  c.and      s0, s0
                  c.beqz     a4, 278f
278:              remu       t6, gp, s7
                  sltu       s7, a1, t2
                  c.bnez     a4, 283f
                  remu       s2, a2, s2
                  sra        a4, s5, a2
283:              mul        s10, a2, a6
                  c.or       s1, a4
                  la         t1, region_2+1093 #start load_store_instr_stream_1
                  la         s6, region_2+2134 #start load_store_instr_stream_2
                  la         s3, region_2+1247 #start load_store_instr_stream_3
                  la         s7, region_2+7123 #start load_store_instr_stream_4
                  lw         s5, -39(s7)
                  lb         t2, 31(s7)
                  la         tp, region_2+2241 #start load_store_instr_stream_0
                  lb         s1, 15(s7)
                  lb         a5, 22(t1)
                  lb         t3, 17(s6)
                  lb         t3, -45(s6)
                  lb         a7, -23(s7)
                  lb         s10, 32(t1)
                  lbu        t5, 63(t1)
                  lbu        a0, -759(tp)
                  lhu        s2, -13(s3)
                  lw         a1, 23(t1)
                  sb         a5, 41(s6)
                  lb         t5, -24(tp)
                  lbu        t0, -32(s6)
                  lb         t0, -45(s7)
                  lbu        s0, -26(t1)
                  lbu        ra, 983(tp)
                  sb         t3, -52(s6)
                  lb         t2, -62(t1)
                  lb         a3, -816(tp)
                  lb         s2, 522(tp)
                  lbu        a7, 10(s7)
                  lb         a1, 8(s3)
                  lbu        t5, 671(tp)
                  sb         a6, 4(s3)
                  sb         tp, -10(s3)
                  lbu        s1, 7(s7)
                  lb         t4, -29(t1)
                  lbu        t0, 14(s3)
                  lb         t3, 44(tp)
                  sh         a4, -11(s7)
                  lb         ra, 6(s3)
                  sb         s9, 10(t1)
                  sb         s9, 9(s3) #end load_store_instr_stream_3
                  sb         a0, -62(s6)
                  lhu        a3, -51(t1)
                  lbu        t0, 54(s7)
                  lw         t4, -3(s7) #end load_store_instr_stream_4
                  lb         a2, -667(tp)
                  lb         s0, 10(t1) #end load_store_instr_stream_1
                  lb         a0, -39(s6) #end load_store_instr_stream_2
                  lbu        s5, -659(tp) #end load_store_instr_stream_0
                  c.srli     s1, 24
                  csrrs      tp, 0x340, a2
                  slt        a3, ra, t1
                  bne        a4, s5, 299f
                  slli       ra, t0, 21
                  srai       t4, s9, 7
                  c.nop
                  c.lui      t0, 11
                  csrrc      ra, 0x340, s9
                  csrrs      t1, 0x340, t6
                  sub        s7, s6, a7
                  xor        t2, t6, zero
                  c.slli     t3, 13
                  c.or       s0, a1
299:              mulhsu     s10, a7, s2
                  bne        a5, t5, 305f
                  c.mv       a7, t5
                  sltu       zero, zero, t2
                  xor        s11, t3, s0
                  c.slli     s11, 7
305:              c.beqz     a5, 323f
                  c.srai     s0, 5
                  csrrsi     a1, 0x340, 27
                  csrrci     a1, 0x340, 15
                  slli       s0, a5, 26
                  c.ebreak;c.nop;
                  bne        t1, s4, 314f
                  nop
                  c.slli     t2, 24
314:              c.ebreak;c.nop;
                  bltu       s6, t2, 319f
                  c.slli     a3, 23
                  mulh       s1, s5, a1
                  or         s4, t4, s3
319:              sltiu      a1, s10, -317
                  srli       s6, t4, 17
                  sub        t0, a1, zero
                  sll        a7, t1, t1
323:              srl        s2, t6, s9
                  mulhsu     s2, s10, t2
                  csrrci     t0, 0x340, 5
                  .4byte 0x00100073 # ebreak
                  slt        s0, s10, a4
                  rem        s3, ra, t5
                  xori       s3, tp, -315
                  mulhsu     t4, zero, s3
                  divu       a1, gp, t3
                  csrrs      a4, 0x340, s2
                  divu       a7, s5, a7
                  c.nop
                  or         s6, t2, s8
                  c.or       a5, a4
                  c.mv       a0, t3
                  c.slli     t3, 22
                  and        a1, t3, s9
                  c.slli     s4, 31
                  add        s11, s10, a0
                  xori       a2, a2, 21
                  nop
                  csrrci     s1, 0x340, 18
                  csrrc      tp, 0x340, t5
                  c.beqz     a1, 359f
                  sll        a3, s7, a1
                  c.andi     a4, 16
                  xori       zero, a2, 403
                  c.sub      a2, a1
                  c.nop
                  csrrc      s4, 0x340, s7
                  xor        a0, a4, t0
                  or         ra, a3, t2
                  beq        t0, s1, 363f
                  auipc      s2, 1006943
                  srai       a0, s7, 20
                  c.beqz     a0, 363f
359:              lui        a7, 428888
                  bltu       t4, t2, 361f
361:              csrrci     a4, 0x340, 5
                  srai       t2, sp, 4
363:              c.sub      a5, s1
                  beq        s3, a6, 377f
                  sltiu      a7, a2, 196
                  addi       s10, t4, -309
                  c.andi     a1, -12
                  c.mv       s4, t1
                  csrrw      s6, 0x340, s10
                  divu       s7, t5, t4
                  xor        s7, a6, s5
                  slt        t5, t6, t3
                  c.lui      a2, 31
                  srl        a3, a5, tp
                  mulh       a1, a2, t3
                  add        a7, t1, s0
377:              c.and      a4, a4
                  c.ebreak;c.nop;
                  sll        t6, s7, a2
                  sll        a0, t0, a0
                  andi       s4, a5, -69
                  and        s4, s7, s7
                  auipc      t0, 667201
                  c.srai     a0, 9
                  bge        s7, s11, 398f
                  or         s1, t3, t3
                  c.andi     a2, 25
                  csrrsi     s1, 0x340, 7
                  sub        s1, s1, t3
                  c.beqz     s0, 405f
                  blt        t0, s3, 409f
                  beq        s3, a5, 395f
                  beq        ra, t0, 395f
                  or         a7, s2, a2
395:              mulhu      t4, s3, sp
                  or         a3, a7, tp
                  slt        s1, tp, sp
398:              mul        s0, t4, s1
                  sra        a3, s3, s11
                  c.sub      a0, a5
                  bne        a6, s5, 413f
                  sltiu      a0, a1, -160
                  csrrw      s0, 0x340, a1
                  beq        a3, a0, 412f
405:              csrrci     s6, 0x340, 28
                  bltu       zero, s0, 413f
                  c.beqz     a3, 410f
                  sub        a5, s10, t0
409:              c.ebreak;c.nop;
410:              c.add      a7, s0
                  blt        s11, s10, 423f
412:              ori        a1, s3, -483
413:              beq        a4, t6, 426f
                  auipc      t2, 644136
                  mulh       s0, s4, s9
                  slt        ra, s1, s5
                  div        s0, a0, s7
                  bgeu       a3, s10, 436f
                  c.li       s6, -29
                  .4byte 0x00100073 # ebreak
                  c.and      s0, s1
                  c.sub      s1, a4
423:              srl        t0, s11, sp
                  xori       a4, ra, 599
                  .4byte 0x00100073 # ebreak
426:              mulhu      s1, s4, t0
                  csrrc      a7, 0x340, t4
                  mulhu      tp, s11, s3
                  sll        s4, s7, t0
                  bgeu       t0, a3, 435f
                  mulhsu     s2, t4, ra
                  lui        zero, 567133
                  bgeu       a5, tp, 436f
                  srli       a6, a2, 7
435:              add        s10, s10, ra
436:              csrrwi     s1, 0x340, 9
                  sra        gp, t4, s1
                  c.sub      a3, a1
                  c.sub      a2, a5
                  c.add      s6, a2
                  c.add      s0, s5
                  csrrwi     s4, 0x340, 0
                  csrrs      s7, 0x340, s4
                  csrrw      t3, 0x340, zero
                  c.and      a5, s0
                  blt        s1, a6, 461f
                  xor        t6, a2, a0
                  and        a1, sp, t2
                  srai       gp, a7, 6
                  sra        ra, t2, s11
                  andi       gp, s3, 883
                  ori        t2, a7, -74
                  sltu       s2, s6, s4
                  slli       t2, s7, 0
                  beq        s8, t5, 461f
                  bgeu       zero, a6, 461f
                  mul        s10, zero, s6
                  c.li       a3, -27
                  c.srai     a0, 14
                  bge        t6, a1, 464f
461:              c.andi     s1, 0
                  c.ebreak;c.nop;
                  c.srai     a2, 14
464:              srli       t4, s9, 16
                  csrrsi     t2, 0x340, 8
                  rem        a6, t2, sp
                  slli       s3, gp, 18
                  blt        t1, a0, 480f
                  sra        t5, tp, t3
                  slt        s0, zero, a0
                  bne        a6, s0, 479f
                  c.beqz     a1, 473f
473:              c.bnez     s1, 483f
                  add        gp, s0, s6
                  csrrwi     ra, 0x340, 1
                  csrrw      s0, 0x340, s8
                  sltu       a4, ra, s9
                  sra        a1, ra, s1
479:              and        s10, a7, s6
480:              mulhu      t0, a5, s2
                  c.mv       t3, a5
                  remu       ra, gp, s2
483:              c.beqz     a5, 489f
                  xor        ra, s6, ra
                  slli       a7, t2, 28
                  bge        s1, gp, 496f
                  or         a5, zero, s7
                  sltu       s0, s4, gp
489:              auipc      t3, 19451
                  divu       a6, a3, a3
                  c.bnez     s1, 499f
                  slt        t4, a3, a1
                  csrrw      t0, 0x340, a7
                  auipc      s7, 122954
                  bne        a1, s1, 502f
496:              c.add      t5, s8
                  bltu       s1, s10, 498f
498:              mulhu      a1, a6, t6
499:              srli       a0, t1, 17
                  c.addi     t2, 20
                  mul        s7, t0, s5
502:              c.ebreak;c.nop;
                  srai       t1, t4, 24
                  csrrw      a3, 0x340, s3
                  bne        ra, s0, 508f
                  c.sub      s0, a0
                  c.li       t3, 27
508:              slt        tp, a6, t0
                  c.li       t1, 17
                  srl        s2, t4, s7
                  c.mv       a3, a3
                  xori       tp, s11, 585
                  c.nop
                  srl        t4, s6, a2
                  c.beqz     a2, 517f
                  bgeu       s4, a0, 534f
517:              add        t2, t0, s3
                  c.slli     t3, 6
                  slli       s0, s11, 17
                  bge        a2, s9, 521f
521:              sltiu      s4, a1, -756
                  lui        s3, 616822
                  addi       a5, tp, -479
                  divu       zero, t0, a3
                  mulh       t3, t5, s2
                  xori       a3, t5, -721
                  add        t3, t6, s9
                  mulhsu     s10, a5, a6
                  csrrsi     t1, 0x340, 16
                  mulh       s4, s9, s10
                  slli       a5, a0, 27
                  c.srai     a4, 1
                  csrrwi     s6, 0x340, 13
534:              c.or       a5, a5
                  andi       t2, tp, 337
                  c.and      a3, a5
                  sra        a1, s8, s7
                  xori       tp, tp, 371
                  andi       s4, s8, 843
                  c.andi     a3, 11
                  auipc      s2, 586091
                  sltiu      s1, s5, 411
                  beq        tp, gp, 558f
                  mul        s5, t0, s0
                  remu       s10, s10, s10
                  remu       s4, s9, ra
                  blt        s1, s5, 560f
                  mul        ra, t5, gp
                  bne        a5, s4, 560f
                  divu       a5, a0, s11
                  csrrw      a0, 0x340, s9
                  sltu       t4, s4, ra
                  sll        a0, a7, sp
                  bge        s11, zero, 567f
                  srl        tp, zero, t3
                  mulhsu     gp, t6, a0
                  c.srai     a0, 21
558:              slt        t5, s1, a5
                  xor        s6, t0, s1
560:              remu       t2, a1, a3
                  ori        t2, zero, 154
                  xor        s6, zero, zero
                  mul        s4, s11, s2
                  c.li       a3, 12
                  rem        gp, a4, s10
                  c.add      a5, t1
567:              sra        t6, s9, t1
                  srl        a7, s3, s4
                  c.mv       s4, s11
                  or         t0, s11, ra
                  c.li       t2, -21
                  mul        zero, a7, s0
                  bge        a2, s9, 581f
                  c.sub      a0, s0
                  mulhsu     s6, ra, s11
                  bgeu       tp, zero, 585f
                  slli       tp, a4, 18
                  mulhu      t2, a2, s6
                  xori       t4, s11, -398
                  mulhu      t6, a2, tp
581:              c.bnez     a0, 589f
                  mulh       s3, a4, s3
                  add        t2, s1, s1
                  sub        s4, zero, a7
585:              sll        a2, a5, a0
                  c.ebreak;c.nop;
                  mul        s4, gp, a6
                  bne        t0, t6, 603f
589:              xori       s6, s1, -447
                  sra        s7, s9, s8
                  csrrs      a1, 0x340, a6
                  and        s7, s2, s0
                  c.srai     a5, 19
                  c.addi     tp, -8
                  csrrwi     t1, 0x340, 16
                  csrrwi     zero, 0x340, 2
                  c.addi     s3, -2
                  lui        t4, 827079
                  add        ra, s10, a7
                  and        t1, sp, s5
                  add        a5, t1, s5
                  auipc      t3, 694951
603:              sub        a6, s8, t2
                  add        s0, s5, sp
                  c.and      a2, a5
                  slt        a0, t1, sp
                  sltiu      s3, s0, -96
                  c.nop
                  csrrci     t1, 0x340, 8
                  c.slli     s2, 11
                  .4byte 0x00100073 # ebreak
                  c.xor      a3, a4
                  blt        a3, s4, 614f
614:              c.addi     tp, 1
                  xori       a3, a6, 187
                  ori        t2, s4, 787
                  ori        t0, s9, -648
                  sltiu      a4, tp, 944
                  sltiu      s3, s5, 855
                  csrrs      t5, 0x340, t4
                  c.andi     s1, -27
                  csrrwi     a0, 0x340, 25
                  c.or       s1, a5
                  mul        a4, s2, s4
                  beq        t0, t5, 635f
                  c.addi     a1, -32
                  c.and      a0, a1
                  c.li       a5, -4
                  slt        s3, a1, s10
                  srl        tp, s4, s9
                  c.xor      s1, a2
                  c.beqz     a2, 645f
                  bge        s2, s1, 643f
                  sra        a2, s4, s2
635:              and        a7, tp, a7
                  blt        s7, t3, 648f
                  and        s10, t4, s6
                  bgeu       s11, s0, 646f
                  c.ebreak;c.nop;
                  c.slli     t0, 1
                  bge        t1, t5, 643f
                  addi       s5, t5, -240
643:              c.nop
                  mulhu      t4, s4, t1
645:              c.ebreak;c.nop;
646:              add        a0, s2, t1
                  slti       s6, t4, 594
648:              mulh       a3, s0, s9
                  c.and      a1, a3
                  csrrc      t0, 0x340, tp
                  c.mv       t6, t1
                  bltu       s4, t3, 655f
                  or         s7, ra, a3
                  slt        a6, t5, s4
655:              xori       s5, s6, 803
                  c.mv       a5, gp
                  mulh       gp, sp, t2
                  div        s3, s4, s10
                  and        t1, s6, a2
                  c.srli     a3, 29
                  rem        s1, gp, t0
                  c.srai     a0, 6
                  beq        t2, tp, 666f
                  c.lui      s3, 2
                  sra        s11, a2, t3
666:              c.andi     a1, -11
                  c.sub      a3, a2
                  slli       a5, s8, 11
                  remu       zero, a4, t2
                  blt        a1, s6, 681f
                  c.li       a3, 19
                  c.srli     a5, 13
                  mulhu      a0, s11, a2
                  slt        s2, s5, s6
                  auipc      a2, 275418
                  c.lui      t4, 29
                  andi       t0, s2, 492
                  rem        s3, a6, a7
                  c.srli     a2, 25
                  divu       t1, t4, t0
681:              bge        zero, t2, 689f
                  bne        t1, s11, 687f
                  srl        a5, t2, s5
                  beq        s6, t3, 699f
                  mulhu      s4, s6, a5
                  c.srai     a4, 9
687:              c.slli     s3, 14
                  c.srai     a4, 2
689:              c.beqz     s0, 694f
                  c.mv       t4, s3
                  rem        a3, s8, tp
                  sltiu      a7, s3, -412
                  mulhsu     s1, a7, t1
694:              bge        t0, a4, 701f
                  c.nop
                  c.srli     a0, 1
                  c.andi     a4, 18
                  divu       t3, sp, s2
699:              c.beqz     a0, 708f
                  c.bnez     a3, 718f
701:              divu       a0, s2, t2
                  addi       t5, ra, 683
                  c.srli     s1, 23
                  c.slli     s6, 22
                  sub        a1, sp, s9
                  bgeu       a6, a6, 719f
                  beq        s7, t1, 708f
708:              csrrci     s5, 0x340, 13
                  addi       a4, zero, 924
                  nop
                  csrrw      s5, 0x340, t2
                  slti       zero, t0, 296
                  csrrsi     t4, 0x340, 24
                  srl        s2, s2, sp
                  mulhsu     s0, zero, t2
                  csrrci     s3, 0x340, 23
                  addi       gp, ra, -581
718:              sll        a7, s8, s8
719:              nop
                  csrrwi     t5, 0x340, 9
                  sra        gp, a3, a2
                  c.andi     a1, 9
                  srl        s3, t0, s1
                  csrrs      tp, 0x340, a0
                  blt        tp, sp, 743f
                  c.beqz     a2, 734f
                  bgeu       tp, t0, 739f
                  c.srai     a4, 15
                  slli       t0, a2, 8
                  c.mv       s3, s2
                  ori        zero, a2, 54
                  csrrs      zero, 0x340, s0
                  or         t5, a3, s7
734:              mulh       s3, s3, a0
                  andi       s5, t5, -428
                  sub        a1, t3, s5
                  c.srai     a4, 30
                  mulhu      s0, s2, ra
739:              c.add      a2, s3
                  add        t1, t2, s3
                  srl        s2, t6, a3
                  or         s5, s10, tp
743:              mulh       s4, a4, a3
                  c.ebreak;c.nop;
                  bge        s2, a5, 746f
746:              lui        s2, 181520
                  addi       gp, zero, 508
                  c.add      s3, t1
                  csrrsi     gp, 0x340, 11
                  csrrc      tp, 0x340, s9
                  csrrci     a2, 0x340, 19
                  addi       a7, ra, -783
                  bge        s9, a5, 756f
                  csrrwi     a4, 0x340, 11
                  .4byte 0x00100073 # ebreak
756:              csrrci     tp, 0x340, 11
                  c.mv       gp, ra
                  sltiu      s1, s8, 333
                  csrrsi     s3, 0x340, 23
                  c.and      s0, s1
                  csrrwi     s1, 0x340, 19
                  c.sub      a4, a2
                  rem        zero, t1, s1
                  .4byte 0x00100073 # ebreak
                  srl        s7, s3, s9
                  csrrc      s2, 0x340, s7
                  lui        s5, 827953
                  bne        a3, t0, 772f
                  blt        gp, s7, 775f
                  sra        a2, a6, tp
                  srli       s2, t5, 14
772:              auipc      a7, 720648
sub_2_4:          jal        gp, 6f
0:                jal        ra, 4f
1:                jal        ra, 13f
2:                jal        a1, 15f
3:                jal        t1, 11f
4:                jal        t1, 12f
5:                jal        ra, 17f
6:                c.jal      2b
7:                c.j        0b
8:                c.j        3b
9:                jal        t1, 16f
10:               c.jal      9b
11:               c.j        7b
12:               c.jal      5b
13:               jal        ra, 14f
14:               c.jal      10b
15:               jal        t1, 8b
16:               jal        ra, 18f
17:               c.jal      1b
18:               slt        s6, s7, zero
                  csrrci     t4, 0x340, 3
                  csrrwi     s3, 0x340, 5
775:              csrrwi     tp, 0x340, 18
                  nop
                  csrrw      a2, 0x340, s11
                  c.add      tp, sp
                  ori        tp, s9, -935
                  srl        s0, sp, ra
                  nop
                  bne        ra, s4, 788f
                  mul        t1, zero, a1
                  csrrc      a2, 0x340, s3
                  c.li       s11, 28
                  c.nop
                  lui        s0, 483671
788:              lui        t0, 610414
                  c.lui      s7, 24
                  bgeu       s3, a1, 798f
                  andi       s11, t5, -507
                  srli       s6, gp, 13
                  add        s2, t4, s8
                  ori        a6, s8, 459
                  xori       s3, t5, 113
                  auipc      s3, 70999
                  bge        s11, t2, 810f
798:              csrrsi     tp, 0x340, 19
                  mulhsu     a5, sp, s11
                  c.sub      s0, a5
                  c.mv       gp, a4
                  sltu       s10, s3, t5
                  srli       t1, a3, 1
                  csrrsi     t5, 0x340, 29
                  c.beqz     s0, 807f
                  addi       a2, t4, -636
807:              bgeu       a6, zero, 808f
808:              sltu       t3, s3, s1
                  c.srli     a4, 27
810:              c.mv       t5, a5
                  c.lui      a0, 18
                  c.addi     ra, 17
                  c.slli     tp, 18
                  c.sub      s0, a1
                  auipc      gp, 431627
                  c.sub      a5, s1
                  c.bnez     a1, 830f
                  slt        s3, s5, t4
                  sltu       a4, s0, sp
                  csrrw      t5, 0x340, s9
                  blt        a6, a2, 833f
                  c.xor      a0, a0
                  srl        a0, s3, t2
                  sll        a1, t4, s11
                  nop
                  mulhsu     s3, s3, s9
                  and        s4, a5, tp
                  .4byte 0x00100073 # ebreak
                  andi       t6, t3, 475
830:              mulhu      s1, a1, t2
                  xori       a5, sp, 121
                  srai       zero, t3, 27
833:              c.srai     a3, 11
                  c.nop
                  c.beqz     a4, 841f
                  sll        s2, s9, a7
                  csrrs      t0, 0x340, a6
                  slt        t6, a5, s9
                  andi       s1, t1, 897
                  c.srai     a3, 24
841:              csrrci     s7, 0x340, 15
                  c.ebreak;c.nop;
                  blt        a6, s11, 848f
                  csrrci     t4, 0x340, 2
                  c.mv       s0, s2
                  csrrc      ra, 0x340, t6
                  rem        a2, a7, s3
848:              add        t0, sp, ra
                  blt        zero, s1, 850f
850:              blt        t6, t1, 858f
                  slt        s1, a6, t0
                  c.xor      a3, a4
                  mul        tp, t5, t5
                  slti       a2, t0, 300
                  .4byte 0x00100073 # ebreak
                  c.or       a4, s1
                  slli       t3, sp, 1
858:              beq        t0, s0, 873f
                  csrrsi     a2, 0x340, 24
                  mulh       zero, s8, sp
                  mulhsu     a2, s10, a7
                  andi       a2, s8, -120
                  csrrsi     s6, 0x340, 19
                  csrrci     gp, 0x340, 30
                  sltiu      s4, s9, 649
                  csrrsi     t2, 0x340, 2
                  mulhsu     a0, a4, t0
                  csrrwi     s10, 0x340, 23
                  blt        s4, s9, 887f
                  c.lui      a6, 23
                  csrrci     a3, 0x340, 5
                  la         s6, region_4+410 #start riscv_hazard_instr_stream_3
                  sltiu      t4, ra, 814
                  lb         t1, 2(s6)
                  lh         a3, -6(s6)
                  and        a0, t1, t4
                  sb         a0, -9(s6)
                  auipc      t4, 150124
                  lbu        t1, 1(s6)
                  mul        a3, tp, ra
                  sb         a0, -11(s6)
                  mulh       tp, t1, a0
                  c.mv       a3, tp
                  sb         tp, 6(s6)
                  .4byte 0x00100073 # ebreak
                  lb         t1, 9(s6)
                  lw         t1, -14(s6)
                  lb         t4, -8(s6)
                  mulhsu     t4, t1, tp
                  slti       ra, a3, -254
                  c.srai     a3, 8
                  lbu        a3, -10(s6)
                  lbu        t1, 13(s6)
                  slli       tp, t1, 18
                  mulh       a0, tp, tp
                  lbu        tp, -11(s6) #end riscv_hazard_instr_stream_3
                  c.nop
873:              slti       s5, t5, -673
                  mulhsu     s5, t1, t2
                  rem        s11, gp, zero
                  c.srai     a2, 10
                  c.addi     s2, 8
                  sltu       a3, a7, s1
                  divu       a6, a1, a6
                  srai       s4, tp, 19
                  c.srai     a4, 18
                  auipc      t1, 10958
                  c.slli     s0, 25
                  ori        a1, s8, 253
                  c.andi     a1, 13
                  c.srli     a3, 1
887:              mulhu      a1, s6, a1
                  beq        t6, a3, 901f
                  add        s0, s4, s11
                  slti       zero, t2, -554
                  csrrs      s10, 0x340, a4
                  c.bnez     a2, 900f
                  beq        t6, a1, 903f
                  csrrsi     s11, 0x340, 29
                  bltu       sp, s3, 908f
                  auipc      s0, 491417
                  c.addi     s4, -21
                  c.srli     a3, 31
                  sra        zero, t3, t3
900:              bne        s11, zero, 911f
901:              mul        s2, s4, a6
                  nop
903:              add        t1, s11, a1
                  bgeu       t1, t5, j_sub_2_sub_3_3 #branch to jump instr
                  slt        t2, t3, s3
                  c.srai     a4, 27
                  lui        t5, 437879
                  sll        s0, t5, s11
                  mulh       s10, a5, a0
                  mulhu      s7, t6, zero
                  or         a2, t0, s11
                  lui        a7, 125317
                  c.mv       s1, s2
                  csrrwi     t2, 0x340, 18
j_sub_2_sub_3_3:  jal        gp, sub_3
                  lui        a2, 15334
                  c.andi     s1, -27
                  sltu       a6, s5, s0
                  c.and      a5, a3
908:              csrrsi     a6, 0x340, 0
                  csrrci     ra, 0x340, 10
                  c.xor      s1, a4
911:              c.mv       t6, t1
                  c.slli     t5, 7
                  divu       s1, t3, a0
                  andi       a2, s8, 93
                  slti       a3, t3, -579
                  c.xor      a0, s1
                  mulhu      t3, s7, t2
                  nop
                  andi       t3, t6, -50
                  mulhsu     s1, s2, s11
                  or         t3, s4, a7
                  csrrw      t1, 0x340, s0
                  csrrs      s3, 0x340, a0
                  auipc      s6, 243556
                  csrrc      zero, 0x340, a1
                  auipc      t6, 1034381
                  andi       t4, zero, 542
                  nop
                  nop
                  mulhu      a4, sp, t5
                  c.srai     a5, 15
                  c.li       a2, -23
                  ori        a0, a7, -972
                  c.sub      a3, a2
                  c.ebreak;c.nop;
                  sll        gp, a1, t5
                  slt        a5, s5, s5
                  c.lui      a5, 5
                  bge        t5, ra, 954f
                  c.nop
                  csrrw      t4, 0x340, s2
                  slti       t1, gp, 253
                  c.add      t4, s9
                  c.andi     a3, -13
                  and        a3, t4, s7
                  nop
                  remu       t6, a6, tp
                  c.and      s1, a4
                  or         s3, a2, a6
                  sltiu      s6, s4, 678
                  srl        a3, gp, s3
                  beq        s5, ra, 955f
                  xori       s0, s6, 1010
954:              csrrci     s6, 0x340, 29
955:              blt        s11, t3, 960f
                  auipc      zero, 31326
                  .4byte 0x00100073 # ebreak
                  c.lui      s2, 21
                  and        s6, s0, sp
960:              mulhu      s4, s7, a0
                  sll        t3, s7, s2
                  c.lui      s2, 29
                  c.bnez     a3, 971f
                  lui        s2, 455953
                  mulhsu     a2, s10, t1
                  slti       t2, t2, -413
                  slti       t0, t5, -698
                  csrrw      s10, 0x340, s10
                  csrrsi     s0, 0x340, 3
                  csrrsi     s11, 0x340, 24
971:              div        t4, s4, s11
                  c.beqz     a3, 975f
                  xor        t6, t4, s10
                  srl        a7, t2, tp
975:              c.mv       t2, tp
                  c.addi     t0, 1
                  blt        t6, s1, 981f
                  remu       t4, s0, t4
                  c.beqz     s1, 988f
                  remu       a4, s3, t4
981:              bge        s9, a0, 993f
                  csrrci     a3, 0x340, 1
                  c.nop
                  xor        s6, s3, s3
                  c.beqz     a5, 988f
                  mul        a4, s11, a7
                  remu       s4, t5, s0
988:              sltu       s7, t1, t1
                  div        tp, a7, tp
                  mul        zero, a0, a5
                  sltu       t0, s0, s10
                  xori       t4, s4, 494
993:              csrrc      tp, 0x340, sp
                  rem        s1, gp, gp
                  c.slli     t5, 27
                  csrrsi     t3, 0x340, 21
                  or         a7, zero, a0
                  add        s7, s10, a5
                  mulhsu     zero, a0, a2
                  lui        s6, 442848
                  c.srai     a2, 1
                  mulhu      s2, s8, s7
                  xor        s4, a2, t3
                  sll        a3, ra, s11
                  blt        s6, t5, 1023f
                  c.mv       s2, a4
                  nop
                  srl        t5, s4, a6
                  auipc      s6, 658570
                  c.mv       a5, s1
                  c.li       a1, 12
                  c.sub      a4, a2
                  csrrci     tp, 0x340, 30
                  div        t3, a4, s0
                  blt        s6, t5, 1021f
                  csrrw      t1, 0x340, s10
                  xor        tp, s8, s11
                  ori        gp, tp, 162
                  c.addi     s0, 11
                  c.addi     s10, -30
1021:             csrrw      a6, 0x340, t0
                  nop
1023:             slt        a3, a3, s7
                  csrrc      a6, 0x340, a0
                  c.and      a4, a4
                  csrrw      a1, 0x340, tp
                  csrrw      s3, 0x340, t0
                  sltiu      a1, s9, -194
                  bltu       a7, a5, 1039f
                  or         a6, t3, a6
                  csrrsi     t2, 0x340, 19
                  sltu       a4, s7, s5
                  div        t1, tp, a4
                  mulhu      a1, s4, t0
                  c.addi     gp, 16
                  c.sub      s0, a0
                  c.slli     ra, 5
                  mul        s3, a5, tp
1039:             srli       a1, tp, 9
                  srai       s10, t3, 5
                  lui        a6, 498037
                  slli       s2, s2, 7
                  lui        tp, 44685
                  lui        a4, 526875
                  c.bnez     a5, 1052f
                  nop
                  c.bnez     a5, 1048f
1048:             srai       t6, t2, 20
                  c.or       a5, a4
                  srl        a7, a3, s8
                  bgeu       sp, s10, 1059f
1052:             sra        t4, s1, s8
                  lui        a2, 862581
                  and        t3, s6, s6
                  c.sub      a3, a1
                  bge        a0, a6, 1061f
                  slt        ra, s8, s4
                  xori       zero, ra, -396
1059:             bgeu       s4, gp, 1074f
                  c.lui      a1, 16
1061:             c.xor      a2, s1
                  c.mv       s10, s2
                  csrrsi     t0, 0x340, 4
                  add        s10, a7, s2
                  bne        s9, t3, 1075f
                  c.ebreak;c.nop;
                  sra        a3, s8, a6
                  sll        t4, s3, s9
                  sltu       t1, a4, zero
                  sub        s4, t6, tp
                  slli       gp, sp, 17
                  .4byte 0x00100073 # ebreak
                  c.and      s1, a3
1074:             c.xor      a3, s1
1075:             c.andi     a4, -11
                  sub        t3, a3, s6
                  c.slli     s7, 8
                  c.li       gp, -3
                  bgeu       t4, s5, 1089f
                  c.srli     a0, 21
                  csrrci     t6, 0x340, 14
                  xor        a6, sp, s8
                  c.nop
                  c.ebreak;c.nop;
                  c.srli     a1, 13
                  srl        t0, a5, s7
                  srai       a0, s4, 2
                  c.addi     tp, -15
1089:             sltiu      a7, s5, 576
                  c.li       s7, 23
                  bge        t6, s4, 1103f
                  slli       ra, a5, 25
                  c.nop
                  c.sub      a2, s0
                  mul        a3, s5, s4
                  c.nop
                  auipc      a0, 548174
                  c.bnez     a1, 1116f
                  nop
                  srai       t6, zero, 20
                  c.li       ra, 20
                  add        s4, gp, sp
1103:             divu       s0, s11, s7
                  csrrs      s0, 0x340, s5
                  sltu       s4, gp, a2
                  c.slli     s2, 8
                  slti       s7, s6, -821
                  slt        a1, t6, s5
                  c.srai     a2, 21
                  c.sub      s0, s0
                  sltu       ra, a6, t4
                  bltu       tp, s6, 1113f
1113:             sra        a5, a3, s7
                  sra        s2, t6, zero
                  mulhsu     a1, a3, sp
1116:             mul        s5, a2, t2
                  slt        a2, t5, s7
                  c.lui      t0, 22
                  srli       a7, t3, 15
                  c.beqz     a1, 1127f
                  xori       a0, t3, 700
                  csrrwi     ra, 0x340, 16
                  div        t4, s5, ra
                  csrrc      a0, 0x340, ra
                  srl        ra, a3, t1
                  blt        s0, zero, 1128f
1127:             divu       s11, sp, s5
1128:             c.ebreak;c.nop;
                  srai       a2, a0, 23
                  c.andi     s0, 6
                  c.nop
                  csrrsi     s7, 0x340, 30
                  add        t3, s0, s5
                  lui        s2, 288309
                  and        s5, s11, t6
                  c.sub      a5, s0
                  c.li       s5, 30
                  addi       a4, s7, -667
                  csrrs      s1, 0x340, zero
                  lui        s0, 807741
                  c.sub      a0, s0
                  sub        zero, tp, s9
                  bgeu       s3, a4, 1151f
                  slt        s3, t5, t6
                  csrrs      s5, 0x340, s4
                  csrrwi     zero, 0x340, 30
                  csrrw      a5, 0x340, a4
                  csrrs      t4, 0x340, s8
                  xori       s11, tp, -204
                  c.bnez     a4, 1168f
1151:             slt        t2, a6, a5
                  bgeu       a5, t6, 1165f
                  bne        a0, gp, 1158f
                  sra        s5, a7, tp
                  c.srai     s1, 13
                  csrrw      t4, 0x340, s5
                  lui        s0, 869827
1158:             c.srai     s0, 1
                  nop
                  auipc      a6, 59221
                  csrrwi     s5, 0x340, 29
                  rem        ra, gp, s3
                  divu       ra, a6, s6
                  srl        t3, a4, a6
1165:             xori       s6, s0, 207
                  csrrc      s1, 0x340, t5
                  lui        s3, 637642
1168:             or         t6, s6, a3
                  divu       s1, s4, s10
                  c.ebreak;c.nop;
                  c.srai     a1, 28
                  csrrs      s4, 0x340, gp
                  c.or       a0, s1
                  csrrw      s4, 0x340, zero
                  bgeu       ra, t4, 1179f
                  xor        gp, s11, t4
                  slti       s7, t0, 919
                  div        t6, sp, s3
1179:             add        s11, t3, s11
                  div        s5, s2, t5
                  and        t5, zero, s7
                  c.lui      a4, 23
                  srai       s11, s1, 1
                  beq        t5, s3, 1199f
                  ori        s1, s9, 84
                  slt        s5, a3, s0
                  .4byte 0x00100073 # ebreak
                  xori       s3, a2, -549
                  c.li       t4, -12
                  c.slli     s7, 23
                  c.li       tp, -11
                  c.srli     a0, 13
                  add        gp, a3, s2
                  c.bnez     a4, 1205f
                  csrrs      ra, 0x340, t3
                  .4byte 0x00100073 # ebreak
                  ori        a6, gp, -433
                  srli       a2, t6, 0
1199:             c.sub      a3, a4
                  srai       s5, t3, 29
                  bgeu       t4, a4, 1207f
                  sltu       s11, t6, s7
                  c.add      t4, t6
                  c.mv       a1, t1
1205:             c.srli     a0, 18
                  rem        ra, s9, s6
1207:             srai       a3, a0, 4
                  c.xor      a3, a3
                  bge        ra, zero, 1212f
                  xor        s3, s10, ra
                  beq        s9, ra, 1222f
1212:             c.mv       t3, t6
                  csrrwi     s1, 0x340, 24
                  sra        s5, s8, s11
                  bgeu       a3, a2, 1222f
                  c.or       a1, s1
                  c.mv       s0, t1
                  lui        a0, 417957
                  remu       s5, zero, zero
                  mulh       t3, a4, tp
                  sll        a4, ra, t4
1222:             add        a6, s10, t2
                  lw         gp, 4(sp)
                  addi       sp, sp, 64
                  c.srai     a0, 24
                  .4byte 0x00100073 # ebreak
                  .4byte 0x00100073 # ebreak
                  c.li       a0, 20
                  mulhsu     a0, s2, s6
                  rem        s7, s3, a7
                  c.sub      s1, a4
1960:             c.jr x3
sub_4:            blt        a5, ra, sub_4_stack_p
                  sra        s4, a1, s9
                  c.mv       t2, gp
                  c.slli     t4, 2
                  c.addi     t6, 27
sub_4_stack_p:    addi       sp, sp, -36
                  slli       t6, t0, 8
                  c.srai     a4, 8
                  sw         gp, 4(sp)
                  c.addi     s2, 16
                  slli       s2, s8, 23
                  .4byte 0x00100073 # ebreak
                  la         t1, region_1+11208 #start load_store_instr_stream_2
                  sb         tp, -3(t1)
                  la         a2, region_4+2726 #start load_store_instr_stream_1
                  la         ra, region_0+880 #start load_store_instr_stream_3
                  lh         a7, -14(t1)
                  lbu        gp, -1(t1)
                  lh         t2, 6(ra)
                  lh         gp, -12(ra)
                  sb         s7, 3(ra)
                  la         tp, region_2+2416 #start load_store_instr_stream_0
                  lbu        s10, -167(a2)
                  lh         t0, 10(ra)
                  lhu        a5, -2(ra)
                  sb         s9, -50(tp)
                  sb         gp, 90(a2)
                  lb         a6, 10(t1)
                  lhu        a0, 8(t1)
                  lb         s10, -53(tp)
                  lb         t4, -16(ra)
                  lb         s5, -48(a2)
                  lb         a0, -153(a2)
                  sb         a1, 9(ra)
                  lbu        zero, -15(tp)
                  lhu        s0, -52(tp)
                  sw         a7, 8(ra)
                  lhu        s10, 178(a2)
                  lb         s3, -7(t1)
                  sb         a6, -8(a2)
                  sb         a5, 33(tp)
                  lhu        t4, 8(a2)
                  lbu        t4, 172(a2)
                  lb         a4, -9(t1)
                  sb         t1, 17(a2) #end load_store_instr_stream_1
                  sh         s8, -12(t1) #end load_store_instr_stream_2
                  lbu        s2, 9(ra) #end load_store_instr_stream_3
                  lbu        t3, 59(tp) #end load_store_instr_stream_0
                  la         a0, region_3+196 #start load_store_instr_stream_1
                  lbu        t4, -61(a0)
                  la         s6, region_3+220 #start load_store_instr_stream_0
                  lb         t5, -41(a0)
                  lbu        s3, 11(s6)
                  lbu        s5, -31(a0)
                  lhu        a5, -22(a0)
                  lbu        a6, -46(a0)
                  sb         s10, 37(s6)
                  lh         t2, -6(s6)
                  lh         a6, -34(a0)
                  sb         a0, -62(s6)
                  lbu        t3, -3(s6)
                  lbu        gp, 14(a0)
                  lb         t2, 14(s6)
                  lbu        s7, 39(a0)
                  sh         a4, 54(s6)
                  lbu        s3, 31(a0)
                  sb         a3, -5(a0) #end load_store_instr_stream_1
                  lb         a4, 13(s6) #end load_store_instr_stream_0
                  la         s2, region_3+201 #start riscv_hazard_instr_stream_1
                  lbu        a6, 34(s2)
                  xor        t6, s1, t6
                  lb         s0, -28(s2)
                  csrrwi     t6, 0x340, 18
                  divu       t6, s7, s1
                  lhu        s1, -89(s2)
                  andi       s0, s7, 949
                  lb         t3, 202(s2)
                  c.add      t3, t3
                  xori       s0, t6, 409
                  lb         s7, -154(s2)
                  sh         t6, 25(s2)
                  sb         a6, -50(s2)
                  ori        t3, s1, -580
                  mul        s7, a6, s1
                  div        t3, s0, s1
                  sb         s0, -135(s2)
                  mulh       a6, s0, a6
                  srl        s1, s1, s1
                  lh         a6, 3(s2)
                  lb         s1, 60(s2)
                  lbu        s0, 254(s2)
                  addi       s1, s0, 376
                  slti       a6, t3, -527
                  lb         t6, 23(s2)
                  sb         s7, -37(s2)
                  lb         t3, 58(s2)
                  sw         s0, -73(s2)
                  slt        s1, s7, t3
                  lb         t3, 87(s2)
                  lhu        s0, -65(s2)
                  xori       s1, s7, -666
                  sb         t6, -96(s2)
                  lhu        t6, 43(s2)
                  lhu        a6, -139(s2) #end riscv_hazard_instr_stream_1
sub_4_4:          jal        gp, 15f
0:                c.j        11f
1:                c.j        8f
2:                c.jal      17f
3:                jal        t1, 1b
4:                jal        ra, 6f
5:                c.jal      13f
6:                c.jal      0b
7:                c.j        10f
8:                c.jal      4b
9:                c.j        12f
10:               c.j        5b
11:               jal        a7, 2b
12:               jal        ra, 7b
13:               c.jal      14f
14:               c.j        16f
15:               jal        ra, 9b
16:               jal        t1, 3b
17:               sra        t3, s3, t5
                  la         t1, region_0+1185 #start riscv_load_store_rand_instr_stream_0
                  sw         t1, 47(t1)
                  srl        s1, t1, s1
                  sh         t2, 11(t1)
                  sb         s4, -6(t1)
                  srli       s0, s9, 12
                  rem        t2, s9, a4
                  sb         s6, -3(t1)
                  lbu        t4, -24(t1)
                  c.ebreak;c.nop;
                  remu       a7, t0, a1
                  andi       s4, t5, 980
                  sb         a3, 60(t1)
                  c.andi     a1, 11
                  c.add      tp, a4
                  xori       s5, s9, -183
                  c.sub      s1, a3
                  c.xor      s0, a4
                  lb         s4, 30(t1)
                  mul        s3, t6, t4
                  lb         s3, 12(t1)
                  c.srai     a3, 19
                  csrrsi     s4, 0x340, 3
                  sb         t4, 47(t1)
                  lhu        t6, -41(t1)
                  mulhsu     s1, a2, t1
                  rem        t4, t6, s11
                  c.mv       s6, s6
                  lbu        s5, 44(t1)
                  c.srli     a5, 2
                  c.slli     s10, 17
                  c.or       a0, a1
                  mulhsu     s6, t4, s7
                  lbu        s10, 24(t1)
                  divu       s3, s9, s2
                  mulhsu     s4, a3, s2
                  lb         tp, -42(t1)
                  csrrw      a2, 0x340, t6
                  lb         t2, 33(t1)
                  c.srai     s0, 11
                  and        t0, sp, s7
                  xori       s5, t0, -674
                  ori        a7, s4, 927
                  lbu        s3, 24(t1) #end riscv_load_store_rand_instr_stream_0
                  la         t1, region_2+5172 #start load_store_instr_stream_2
                  la         a5, region_2+4643 #start load_store_instr_stream_0
                  sb         a7, 897(t1)
                  la         a4, region_2+3101 #start load_store_instr_stream_1
                  lb         t6, 34(t1)
                  sh         a0, -53(a5)
                  lw         a2, -844(t1)
                  sh         s11, 1(a4)
                  lbu        ra, -2(a4)
                  sh         a6, -7(a4)
                  lbu        gp, -682(t1)
                  sb         s11, 1022(a5)
                  sh         a4, -224(t1)
                  sw         gp, 11(a4)
                  lw         s2, -684(t1)
                  lb         s2, -534(a5)
                  lbu        zero, 6(a4)
                  lbu        s4, 530(a5)
                  lbu        s1, -14(a4)
                  sb         s8, -737(a5)
                  lb         ra, -2(a4)
                  lb         a7, -873(t1) #end load_store_instr_stream_2
                  sb         a4, 9(a4) #end load_store_instr_stream_1
                  lbu        zero, 662(a5) #end load_store_instr_stream_0
sub_4_3:          jal        gp, 21f
0:                c.jal      18f
1:                jal        ra, 24f
2:                c.jal      17f
3:                jal        t1, 5f
4:                c.j        22f
5:                c.jal      13f
6:                jal        t1, 1b
7:                c.jal      15f
8:                jal        ra, 9f
9:                c.jal      20f
10:               c.jal      14f
11:               c.j        6b
12:               jal        ra, 7b
13:               jal        ra, 12b
14:               jal        ra, 8b
15:               jal        t5, 25f
16:               c.j        23f
17:               c.j        26f
18:               c.jal      4b
19:               c.jal      10b
20:               c.j        27f
21:               jal        gp, 2b
22:               c.jal      16b
23:               c.j        3b
24:               c.j        19b
25:               jal        ra, 11b
26:               jal        ra, 0b
27:               div        s6, s11, t3
                  la         t3, region_2+2652 #start riscv_hazard_instr_stream_2
                  or         a6, a1, s0
                  add        a4, a4, a1
                  lb         a4, -33(t3)
                  c.mv       s0, s0
                  c.and      a0, s0
                  lb         t4, -39(t3)
                  sltu       t4, a1, t4
                  lui        a1, 804247
                  srli       a6, a4, 5
                  xor        a4, a4, a4
                  rem        t4, a1, t4
                  lh         s0, 48(t3)
                  sltiu      s0, a1, 482
                  div        a1, a6, a1
                  ori        a4, s0, 504
                  lb         s0, -21(t3)
                  sra        a4, a0, t4
                  lbu        s0, -8(t3)
                  lhu        a0, -52(t3)
                  lbu        a1, 54(t3)
                  sb         a1, 22(t3)
                  sb         a6, -37(t3)
                  div        s0, a4, t4
                  sb         a1, -47(t3)
                  lhu        t4, 42(t3)
                  sw         a6, 20(t3)
                  lh         a1, 18(t3)
                  sb         s0, -51(t3)
                  sw         a1, 60(t3)
                  c.xor      a1, a4
                  lb         t4, 43(t3)
                  lhu        s0, -18(t3)
                  c.nop
                  or         a4, a1, a0
                  addi       a0, t4, 932
                  add        a0, a0, a6
                  lui        a4, 1034402
                  lbu        t4, 32(t3)
                  sb         t4, -21(t3)
                  sb         a0, -60(t3)
                  sw         a6, 48(t3)
                  lb         s0, 43(t3)
                  andi       s0, t4, -1006
                  c.srai     a0, 16
                  csrrc      s0, 0x340, a0
                  sltu       s0, s0, a4
                  csrrwi     a1, 0x340, 8
                  sb         t4, 45(t3)
                  sb         a1, 47(t3) #end riscv_hazard_instr_stream_2
sub_4_5:          jal        gp, 21f
0:                jal        ra, 12f
1:                c.jal      18f
2:                c.j        9f
3:                jal        ra, 15f
4:                c.jal      7f
5:                jal        gp, 4b
6:                c.j        2b
7:                c.j        0b
8:                jal        ra, 20f
9:                c.jal      1b
10:               c.jal      14f
11:               jal        ra, 5b
12:               jal        ra, 22f
13:               c.j        8b
14:               c.j        6b
15:               c.j        10b
16:               jal        ra, 3b
17:               jal        ra, 19f
18:               c.j        11b
19:               c.jal      16b
20:               jal        t1, 17b
21:               jal        ra, 13b
22:               srli       t4, zero, 19
                  la         a0, region_4+1705 #start load_store_instr_stream_1
                  la         s11, region_0+2345 #start load_store_instr_stream_2
                  la         s10, region_1+6317 #start load_store_instr_stream_0
                  sb         s2, -6(a0)
                  sb         a6, 137(s10)
                  lhu        tp, -7(a0)
                  lb         t0, -14(a0)
                  lbu        tp, 127(s11)
                  lb         t4, 12(a0)
                  sb         a2, 16(s10)
                  lbu        s7, -9(a0)
                  lb         s6, -191(s10)
                  lw         s0, -733(s11)
                  lb         a1, 548(s11)
                  sb         s10, 10(a0)
                  sh         s4, -365(s11)
                  sb         a1, -298(s11)
                  lb         a5, 10(a0)
                  lhu        s2, 239(s10)
                  lbu        a5, -4(a0) #end load_store_instr_stream_1
                  lh         a5, 507(s11) #end load_store_instr_stream_2
                  lb         s3, 58(s10) #end load_store_instr_stream_0
                  la         a1, region_2+58 #start riscv_hazard_instr_stream_0
                  .4byte 0x00100073 # ebreak
                  sh         t3, 158(a1)
                  c.sub      s0, s0
                  lbu        s0, -25(a1)
                  c.andi     s0, -8
                  lh         ra, 176(a1)
                  c.nop
                  lbu        a2, 58(a1)
                  lh         a2, 234(a1)
                  mulh       s0, zero, ra
                  c.or       s0, s0
                  c.mv       ra, a2
                  sb         a6, 127(a1)
                  sh         a6, 236(a1)
                  xor        a6, zero, ra
                  sb         s0, 248(a1)
                  mulhsu     a2, a6, s0
                  lbu        ra, -41(a1)
                  div        a2, s0, t3
                  and        t3, a2, zero
                  lw         a2, 34(a1)
                  rem        s0, zero, s0
                  lbu        t3, 223(a1)
                  sb         s0, 83(a1)
                  lbu        a2, 15(a1)
                  lh         ra, 140(a1)
                  lbu        t3, 206(a1)
                  sb         t3, 135(a1)
                  csrrc      zero, 0x340, t3
                  sub        s0, a2, t3
                  srli       t3, a2, 18
                  mulh       t3, a2, a6
                  div        a6, a6, s0
                  c.mv       s0, t3
                  lb         s0, 65(a1)
                  csrrwi     t3, 0x340, 4
                  srli       a2, ra, 26
                  lb         a6, -39(a1) #end riscv_hazard_instr_stream_0
                  la         s3, region_4+2995 #start load_store_instr_stream_4
                  la         a5, region_4+1263 #start load_store_instr_stream_0
                  la         s10, region_4+2405 #start load_store_instr_stream_1
                  lh         a7, 803(s3)
                  lh         s2, -747(s3)
                  la         s6, region_4+1141 #start load_store_instr_stream_2
                  la         t0, region_4+304 #start load_store_instr_stream_3
                  sb         s4, -121(t0)
                  lb         s5, -1(a5)
                  lh         ra, -31(s10)
                  lb         s11, 8(s6)
                  lw         a3, -49(s10)
                  sb         a1, -8(a5)
                  sb         s11, 37(t0)
                  lb         s4, 6(s6)
                  lbu        gp, 10(s6)
                  lb         a7, -24(s10)
                  lbu        a7, 2(a5)
                  sb         s4, -848(s3)
                  lb         tp, -96(t0)
                  lhu        a1, 3(a5)
                  lbu        gp, 7(a5)
                  sb         tp, -24(s10)
                  sb         a6, 580(s3)
                  lbu        s2, 255(t0)
                  sh         s6, -5(a5)
                  sb         s0, -51(s10)
                  lb         ra, -15(s6)
                  lbu        s4, 205(t0) #end load_store_instr_stream_3
                  sb         tp, 9(s6)
                  lb         s5, -41(s10)
                  lbu        ra, 6(s6)
                  sb         t2, 37(s10)
                  lb         t2, -36(s10)
                  sb         a3, 0(s6)
                  lb         a0, 4(a5)
                  sh         zero, 9(s6)
                  sb         s0, -21(s10)
                  lhu        a0, 971(s3) #end load_store_instr_stream_4
                  lbu        a0, 5(s6)
                  lhu        s4, 3(a5)
                  lhu        ra, 1(s6) #end load_store_instr_stream_2
                  lhu        s2, 35(s10) #end load_store_instr_stream_1
                  lhu        a3, 5(a5) #end load_store_instr_stream_0
                  la         s5, region_4+1660 #start riscv_load_store_rand_instr_stream_2
                  mulhsu     t6, zero, s4
                  divu       zero, s10, ra
                  c.srai     a2, 22
                  sra        s0, s2, t1
                  mulhsu     s2, s7, s10
                  lb         a2, -138(s5)
                  .4byte 0x00100073 # ebreak
                  mulhu      t6, s0, s4
                  sw         s4, -72(s5)
                  c.ebreak;c.nop;
                  mulhsu     t0, a7, s0
                  c.addi     s10, -7
                  c.nop
                  sub        t2, a4, a6
                  add        t2, t5, tp
                  sb         s5, 89(s5)
                  lbu        t6, -3(s5)
                  sll        t6, s4, s10
                  c.xor      a5, s1
                  mulhsu     s1, s5, s5
                  c.xor      a1, a2
                  lb         t0, -240(s5)
                  c.or       a4, a0
                  lb         s0, -150(s5)
                  c.or       s0, a4
                  c.mv       t4, s6
                  sb         s0, -225(s5)
                  sb         t4, 202(s5)
                  lui        t3, 861101
                  auipc      ra, 547871
                  remu       t1, s2, s11
                  srl        a1, s10, s6
                  mulhu      t4, s9, t0
                  c.and      a2, a3
                  c.add      a2, a3
                  sra        t2, s10, s10
                  sb         s11, 131(s5)
                  srl        t5, a1, a0
                  lhu        t1, 214(s5) #end riscv_load_store_rand_instr_stream_2
                  bge        t4, t3, 15f
                  lui        s10, 404034
                  sra        t0, s7, t5
                  c.sub      a1, a2
                  xori       s5, t2, -801
                  c.andi     s0, -25
                  sltu       s5, t3, a5
                  sra        s11, s6, s2
                  or         s7, s6, t2
                  c.srli     a4, 12
                  rem        gp, a6, s10
                  remu       a4, a2, tp
                  bne        s0, s0, 32f
                  bgeu       sp, a5, 31f
                  c.li       a4, 7
15:               c.or       a0, a2
                  mulhsu     a4, zero, tp
                  mul        a6, a6, s8
                  slt        t2, a7, a0
                  c.srli     a2, 27
                  csrrsi     a4, 0x340, 10
                  csrrwi     t1, 0x340, 26
                  csrrwi     t3, 0x340, 13
                  c.addi     s5, -20
                  slti       s6, a0, 847
                  addi       a1, t2, 347
                  sltu       t3, s10, t4
                  add        s3, t2, t5
                  c.addi     tp, 26
                  mulhu      a6, s10, t2
                  c.slli     a5, 13
31:               bltu       t1, s10, 51f
32:               csrrc      gp, 0x340, s2
                  .4byte 0x00100073 # ebreak
                  mul        t0, a2, t4
                  csrrs      t6, 0x340, t2
                  sltiu      tp, s10, -456
                  or         s11, a4, zero
                  srl        s1, a2, tp
                  andi       s4, t2, 812
                  bge        s6, zero, 60f
                  bne        t3, t2, 57f
                  csrrw      a7, 0x340, a4
                  c.addi     gp, -16
                  mul        s1, s5, tp
                  slli       t6, sp, 23
                  bltu       t3, t2, 61f
                  c.or       a0, a1
                  xori       t3, s7, -636
                  c.nop
                  or         s7, a2, s5
51:               slt        t1, s2, s5
                  c.srai     a0, 14
                  csrrw      t3, 0x340, tp
                  add        s7, t4, sp
                  xori       s5, a2, -440
                  mulhsu     t4, a1, s1
57:               c.addi     s2, -28
                  lui        s1, 11189
                  c.nop
60:               addi       t5, a2, 559
61:               srl        a5, s9, a7
                  add        t6, s6, s8
                  c.add      t1, s5
                  c.xor      a4, a4
                  xor        s0, s10, s1
                  xori       a1, a2, -28
                  slt        s3, t6, a1
                  ori        t2, a7, 602
                  c.mv       t4, s9
                  sltu       a6, s7, a0
                  divu       a4, s10, s2
                  csrrci     s0, 0x340, 7
                  remu       t4, s1, a7
                  ori        t3, t3, -878
                  ori        s5, s5, 883
                  remu       a6, a4, a0
                  slli       a7, a6, 21
                  xor        s7, sp, a7
                  add        s3, tp, s5
                  c.nop
                  bge        a6, gp, 100f
                  andi       t0, a5, -376
                  and        a4, gp, ra
                  bgeu       s9, a1, 95f
                  c.li       s3, -32
                  c.lui      s5, 10
                  c.srli     s0, 2
                  bne        zero, t1, 105f
                  divu       a2, a2, s0
                  bgeu       s8, t4, 103f
                  srli       t6, t0, 30
                  c.slli     tp, 25
                  slt        a1, a2, t0
                  rem        s2, a5, t4
95:               bge        s11, s6, 113f
                  csrrsi     a3, 0x340, 21
                  c.bnez     a5, 117f
                  c.beqz     s1, 112f
                  lui        zero, 24942
100:              ori        t2, ra, 367
                  addi       s7, a6, 76
                  blt        s2, s9, 110f
103:              c.add      s11, t1
                  csrrsi     t4, 0x340, 12
105:              beq        s9, a4, 117f
                  csrrc      t2, 0x340, a0
                  nop
                  c.srli     a3, 7
                  srl        t4, s6, t1
110:              csrrw      s1, 0x340, s1
                  csrrwi     s0, 0x340, 30
112:              srl        a4, t2, t0
113:              c.lui      s1, 17
                  xori       t1, t4, -42
                  c.andi     a1, 13
                  c.andi     a1, -11
117:              bltu       s0, t1, 135f
                  sll        s5, a1, t6
                  nop
                  csrrw      zero, 0x340, t3
                  mulhu      s2, t0, s6
                  addi       a3, s3, 92
                  bgeu       s11, s5, 128f
                  addi       s2, a3, -484
                  c.xor      a3, s1
                  sra        a3, a0, a1
                  c.andi     s0, -10
128:              c.bnez     a2, 132f
                  c.or       a5, a0
                  xori       a2, a2, -34
                  csrrs      s3, 0x340, t0
132:              c.andi     a0, -30
                  c.nop
                  sll        s10, t2, s0
135:              mulhu      s0, t1, s2
                  blt        sp, t4, 155f
                  beq        a1, a6, 150f
                  sra        s5, t3, s6
                  .4byte 0x00100073 # ebreak
                  mulhu      a6, a6, t0
                  slti       zero, s4, 402
                  or         a0, s8, s5
                  csrrci     t4, 0x340, 10
                  divu       a5, s9, a3
                  c.beqz     a2, 161f
                  csrrc      s11, 0x340, s1
                  csrrsi     a2, 0x340, 27
                  blt        s4, s10, 161f
                  c.slli     a6, 8
150:              csrrwi     s2, 0x340, 5
                  nop
                  remu       a6, s4, s3
                  add        t1, s0, s4
                  c.li       a1, -12
155:              bne        s10, t5, 166f
                  andi       s5, a1, -852
                  c.sub      a3, a5
                  c.li       s6, -5
                  mulhsu     s3, t6, gp
                  c.srai     a1, 10
161:              c.mv       a0, gp
                  csrrwi     t4, 0x340, 7
                  .4byte 0x00100073 # ebreak
                  c.ebreak;c.nop;
                  c.srai     a3, 28
166:              divu       ra, t2, s2
                  mulh       s1, s8, a4
                  csrrwi     a3, 0x340, 3
                  c.srli     s1, 18
                  srl        s2, a5, a0
                  mulhu      s11, t5, s7
                  c.li       t2, 5
                  slti       a5, a5, 625
                  srai       s11, sp, 1
                  or         s0, sp, s10
                  c.beqz     a5, 193f
                  sub        zero, a7, s10
                  div        s5, s8, a4
                  c.sub      s1, a5
                  sltiu      t3, ra, -912
                  c.srli     s1, 31
                  div        zero, t2, t4
                  csrrci     s11, 0x340, 25
                  or         s11, t0, gp
                  mul        s6, a4, s11
                  srl        a0, zero, a4
                  mul        s2, a5, a5
                  c.and      a3, a2
                  .4byte 0x00100073 # ebreak
                  divu       a3, s11, s7
                  sub        a3, a1, t0
                  mulhsu     gp, t3, s11
193:              c.slli     a1, 16
                  sltu       t5, s5, t5
                  mulhsu     s10, t0, a7
                  c.add      ra, a6
                  xori       s1, gp, 334
                  csrrci     s2, 0x340, 28
                  c.bnez     s1, 218f
                  c.li       s5, -27
                  mulh       a1, ra, s10
                  andi       gp, a0, -282
                  c.xor      a5, a0
                  srl        t5, s10, zero
                  c.andi     a0, 7
                  srli       t6, t4, 13
                  slti       s2, sp, -549
                  blt        s4, s5, 224f
                  ori        s1, s10, 615
                  csrrs      a7, 0x340, t6
                  rem        t5, sp, t3
                  bne        a3, s11, 214f
                  andi       tp, s10, -410
214:              divu       a6, s1, a5
                  nop
                  c.or       a3, a3
                  rem        a0, s8, a7
218:              c.add      s2, t6
                  mulhu      s4, s5, t2
                  sltu       s1, s5, s2
                  ori        tp, gp, 0
                  andi       s5, a7, 315
                  addi       ra, t6, 61
224:              and        t1, a4, t6
                  csrrc      s2, 0x340, t3
                  or         tp, s2, ra
                  c.add      s10, a7
                  mulhsu     a1, s9, t4
                  sra        t5, s4, a7
                  c.slli     a0, 24
                  xor        s3, a5, s0
                  ori        a4, a1, 235
                  mulh       t0, s1, a1
                  c.li       a7, 8
                  mulhu      s5, t0, a1
                  xori       a0, sp, -950
                  csrrw      a4, 0x340, a6
                  auipc      a3, 825923
                  slti       t0, sp, -855
                  c.li       s2, 22
                  andi       s0, a3, -756
                  or         s3, a7, a4
                  addi       t4, a5, -738
                  bltu       s11, a6, 259f
                  sll        s0, a3, s3
                  sltu       s0, a6, a7
                  srl        t0, s7, t0
                  mulhu      a0, t4, s9
                  c.add      tp, s9
                  c.mv       t5, t0
                  csrrwi     s3, 0x340, 9
                  xor        t4, a6, s3
                  or         a5, s0, tp
                  bgeu       t2, a6, 260f
                  andi       a0, s6, 503
                  add        s7, tp, a3
                  c.srli     a0, 25
                  csrrw      s7, 0x340, a1
259:              nop
260:              nop
                  c.or       a2, a5
                  nop
                  add        a1, ra, a6
                  c.and      a3, a4
                  sra        ra, t5, s10
                  c.beqz     s0, 286f
                  mulhsu     t1, t4, ra
                  c.bnez     s0, 282f
                  c.ebreak;c.nop;
                  sra        s0, a2, ra
                  c.add      a7, a0
                  blt        s7, zero, 287f
                  or         a4, zero, s3
                  add        s7, a3, a7
                  c.beqz     a1, 280f
                  ori        a2, a5, 241
                  c.srai     s1, 15
                  mulhsu     t2, a1, s5
                  or         t5, s11, s7
280:              .4byte 0x00100073 # ebreak
                  remu       t1, zero, a7
282:              divu       t4, a6, a6
                  c.slli     a7, 30
                  srl        s1, s1, s7
                  c.sub      s1, a1
286:              nop
287:              c.slli     s4, 8
                  andi       a5, a4, -662
                  lui        s1, 343712
                  c.and      a0, a0
                  c.or       s1, a0
                  rem        s5, t1, t4
                  c.srli     a3, 18
                  c.slli     tp, 29
                  c.srai     a3, 14
                  csrrci     s5, 0x340, 27
                  sub        t0, s4, a2
                  mul        a1, t5, t3
                  c.srai     a2, 6
                  csrrwi     gp, 0x340, 20
                  div        a0, a6, t2
                  c.li       ra, 25
                  c.srli     s0, 27
                  srl        a3, sp, a1
                  c.xor      s0, a3
                  bne        a7, tp, 319f
                  c.bnez     a1, 323f
                  rem        s0, s2, s10
                  nop
                  csrrci     s4, 0x340, 19
                  blt        a1, t2, 331f
                  sub        s11, t6, t3
                  or         s2, s0, s7
                  csrrw      a4, 0x340, t4
                  add        a3, a4, sp
                  c.ebreak;c.nop;
                  mulhu      t2, t1, s11
                  and        a4, a2, gp
319:              slti       t6, s3, 796
                  div        a3, s11, s4
                  bgeu       gp, s10, 339f
                  addi       t5, a4, 765
323:              div        s0, s7, a0
                  c.or       a4, a2
                  c.slli     s5, 20
                  .4byte 0x00100073 # ebreak
                  c.ebreak;c.nop;
                  c.li       a1, -7
                  csrrci     a2, 0x340, 14
                  auipc      gp, 444824
331:              bgeu       sp, a4, 339f
                  c.xor      a5, a2
                  c.bnez     a0, 344f
                  c.nop
                  div        gp, s6, t5
                  slt        a0, s5, tp
                  mulhu      a6, a3, zero
                  mulhsu     a1, s0, s1
339:              c.xor      a3, a1
                  rem        t1, t6, s6
                  mulhu      t5, t4, sp
                  csrrci     t6, 0x340, 2
                  bge        a2, s1, 360f
344:              sub        a1, s1, s5
                  auipc      a3, 623228
                  c.mv       t4, s6
                  div        t4, a7, s8
                  c.add      a0, s1
                  c.srli     s1, 22
                  beq        tp, s9, 366f
                  csrrci     ra, 0x340, 4
                  srli       s3, t2, 30
                  c.srli     s0, 23
                  c.sub      s0, a0
                  csrrs      a0, 0x340, t1
                  csrrc      ra, 0x340, t2
                  mulhu      a0, s11, sp
                  div        a4, s10, tp
                  lui        a0, 208933
360:              mulhu      a3, t4, a1
                  srl        s11, s7, sp
                  sltiu      s0, s0, 866
                  c.ebreak;c.nop;
                  csrrc      s10, 0x340, a4
                  add        t1, s4, a4
366:              auipc      tp, 940702
                  sltu       a6, s4, s9
                  divu       t4, gp, s4
                  sra        a2, t4, a6
                  srl        a2, s11, a1
                  auipc      s3, 873548
                  mul        a1, a0, sp
                  c.mv       a5, s5
                  srli       a7, s3, 10
                  csrrw      s2, 0x340, t0
                  mulh       t6, a5, tp
                  mul        t3, s2, tp
                  nop
                  c.bnez     a0, 399f
                  c.li       s11, 25
                  c.nop
                  mul        a0, s3, a7
                  csrrw      t0, 0x340, a4
                  bne        t0, a5, 399f
                  .4byte 0x00100073 # ebreak
                  csrrwi     zero, 0x340, 23
                  srai       s10, s8, 10
                  mulh       zero, s6, s3
                  csrrs      a3, 0x340, s4
                  sltiu      t6, a6, -263
                  slli       t6, s0, 12
                  srli       s10, a3, 19
                  slti       a0, s11, -223
                  slt        s7, a2, a3
                  c.addi     t3, -4
                  c.add      a0, t4
                  rem        s2, s11, s9
                  remu       a6, tp, s3
399:              c.srli     s0, 1
                  c.and      a4, s1
                  remu       t6, a2, s1
                  addi       a5, zero, 10 #init loop 0 counter
                  c.srai     a2, 28
                  .4byte 0x00100073 # ebreak
                  auipc      a6, 733674
                  srai       t6, zero, 15
                  c.andi     a2, 30
                  ori        a0, t5, -861
                  or         s10, s8, a4
                  sltiu      a2, t1, 298
                  c.add      t2, s2
                  sra        t6, a5, a7
                  addi       zero, zero, 0 #init loop 0 limit
                  c.andi     s1, -22
                  mul        a7, s1, gp
sub_4_12_0_t:     xori       t5, t2, -987
                  addi       a5, a5, -1 #update loop 0 counter
                  csrrc      s10, 0x340, t0
                  c.or       s0, s1
                  rem        s5, a6, t0
                  c.andi     s1, 2
                  c.mv       s0, s5
                  c.beqz     a5, sub_4_12_0_t #branch for loop 0
                  c.xor      s0, a4
                  or         t0, s10, tp
                  bne        s4, s8, 416f
                  c.ebreak;c.nop;
                  xori       a1, a0, 756
                  beq        s0, s3, 424f
                  csrrsi     s4, 0x340, 10
                  c.xor      a2, a5
                  rem        s7, t5, s1
                  rem        s5, s8, s6
                  and        a3, a0, s1
                  srli       s4, s3, 20
                  rem        s2, a6, a4
                  add        a1, s7, t4
                  bltu       s3, s1, 417f
416:              divu       t6, s6, t1
417:              .4byte 0x00100073 # ebreak
                  srli       t1, s6, 20
                  lui        t0, 907459
                  c.or       a4, a4
                  div        a5, t5, a5
                  addi       t5, t1, 903
                  c.li       a0, 7
424:              csrrc      a1, 0x340, s1
                  beq        zero, s6, 431f
                  divu       gp, s6, s11
                  bgeu       s11, a1, 446f
                  rem        tp, t4, s11
                  ori        t4, a0, -87
                  bne        t0, a6, 445f
431:              c.lui      t5, 8
                  mul        s10, a6, tp
                  slli       s5, s3, 5
                  blt        zero, s6, 446f
                  srli       a3, s0, 18
                  srli       ra, s5, 27
                  sra        s2, t5, s6
                  sra        t3, s11, gp
                  srli       zero, s11, 2
                  csrrsi     s11, 0x340, 15
                  c.bnez     a2, 461f
                  blt        a5, s11, 460f
                  add        s6, s7, s4
                  xori       gp, s6, 59
445:              addi       t1, ra, 12
446:              auipc      s6, 739814
                  .4byte 0x00100073 # ebreak
                  div        a7, a2, t5
                  beq        s9, s9, 453f
                  div        t0, s0, s6
                  xori       a6, s2, -424
                  xor        a0, zero, t4
453:              mulhsu     t1, s2, a1
                  or         t2, zero, ra
                  mulh       s3, t2, s6
                  xori       t1, s10, -364
                  sra        zero, s6, s5
                  c.nop
                  sltiu      s6, s4, 199
460:              c.sub      a4, a5
461:              c.sub      a3, a2
                  divu       t5, s8, a2
                  c.or       a3, a1
                  rem        t6, t0, zero
                  mulh       s11, s6, a6
                  c.or       a3, s1
                  xori       a5, ra, 521
                  csrrci     tp, 0x340, 23
                  c.andi     s1, -8
                  csrrs      a2, 0x340, t2
                  .4byte 0x00100073 # ebreak
                  or         s5, a0, a6
                  sltu       a1, t1, s9
                  sra        t1, s5, s7
                  lui        a3, 390550
                  bge        t5, s6, 492f
                  c.slli     t6, 10
                  csrrwi     zero, 0x340, 19
                  slli       s3, t3, 0
                  c.slli     a0, 6
                  srli       s0, t6, 8
                  c.slli     t0, 18
                  mulhu      s7, s11, s3
                  and        a3, t5, s5
                  mulhu      t2, a3, t5
                  beq        s2, gp, 499f
                  slti       a7, s8, 862
                  c.bnez     a0, 507f
                  mulhu      a0, t6, a4
                  c.andi     s0, 29
                  c.xor      a2, s1
492:              xor        a4, s0, s1
                  sltu       a5, sp, sp
                  ori        s6, s4, -49
                  csrrci     a2, 0x340, 4
                  rem        s10, s10, a2
                  mul        s1, a3, t0
                  c.andi     a3, -17
499:              .4byte 0x00100073 # ebreak
                  remu       s7, s10, s6
                  auipc      zero, 722577
                  rem        ra, s1, t3
                  c.beqz     s1, 522f
                  add        t3, s4, a1
                  .4byte 0x00100073 # ebreak
                  c.srli     a0, 24
507:              nop
                  c.bnez     s1, 519f
                  bge        t2, s2, 526f
                  c.ebreak;c.nop;
                  c.lui      t5, 20
                  c.addi     s2, -2
                  remu       a3, tp, s10
                  divu       s7, tp, t1
                  mulh       gp, t0, a0
                  andi       s0, s9, 232
                  nop
                  div        a0, s7, s8
519:              slli       zero, a6, 15
                  sra        zero, s8, s0
                  nop
522:              csrrc      a6, 0x340, s1
                  srai       s3, s6, 10
                  c.sub      a2, s0
                  xori       s7, s11, -440
526:              c.beqz     a1, 541f
                  sra        a6, a5, a1
                  remu       s4, zero, t0
                  c.add      a7, t2
                  c.or       a2, a5
                  xor        s7, s6, t3
                  c.ebreak;c.nop;
                  bne        tp, a6, 547f
                  beq        s6, s0, 552f
                  srl        t5, a0, a0
                  rem        a6, a7, a4
                  remu       s0, s4, s1
                  mul        s2, t1, t4
                  c.add      ra, tp
                  c.sub      a5, a1
541:              xori       s0, s4, -88
                  rem        s11, a4, t1
                  c.and      s0, a3
                  c.xor      s0, s0
                  c.sub      a2, a1
                  bgeu       s4, s9, 559f
547:              nop
                  add        a0, s5, a5
                  srli       s3, ra, 17
                  csrrsi     a0, 0x340, 11
                  c.ebreak;c.nop;
552:              c.or       a4, a1
                  csrrc      s2, 0x340, ra
                  c.and      a0, s1
                  bge        a2, a1, 561f
                  bne        t2, t4, 574f
                  csrrc      t5, 0x340, a2
                  xori       ra, a5, -203
559:              c.ebreak;c.nop;
                  csrrs      s3, 0x340, s1
561:              c.or       a0, a0
                  c.beqz     a1, 578f
                  blt        a7, zero, 565f
                  lui        t6, 298128
565:              c.sub      a2, a5
                  csrrsi     t6, 0x340, 2
                  csrrw      s2, 0x340, ra
                  and        s2, s11, sp
                  csrrwi     a6, 0x340, 22
                  addi       s2, t3, -752
                  bge        a1, s11, 575f
                  sltu       s4, s9, a4
                  addi       ra, tp, -771
574:              csrrci     a4, 0x340, 30
575:              sub        t0, t5, a4
                  sll        s0, a5, s8
                  divu       s3, s8, s8
578:              mulhu      s11, a6, s9
                  and        tp, a6, t2
                  c.bnez     a3, 599f
                  slti       s1, a3, 568
                  c.and      a0, a3
                  srl        zero, a1, s11
                  slti       s3, t4, -462
                  slti       t4, s7, -453
                  c.lui      s4, 3
                  c.srli     a0, 30
                  csrrc      t4, 0x340, t1
                  c.nop
                  xor        t6, sp, s11
                  .4byte 0x00100073 # ebreak
                  bgeu       sp, s2, 607f
                  c.bnez     a3, 604f
                  ori        s10, t3, -201
                  sltiu      a0, a3, -764
                  c.sub      a2, a0
                  c.bnez     s0, 615f
                  csrrs      t1, 0x340, s4
                  la         a4, region_3+451 #start load_store_instr_stream_2
                  la         t6, region_4+1416 #start load_store_instr_stream_1
                  lb         t1, -1007(t6)
                  la         s1, region_0+609 #start load_store_instr_stream_0
                  la         a5, region_1+5369 #start load_store_instr_stream_3
                  la         a7, region_2+2614 #start load_store_instr_stream_4
                  sb         a2, 10(a4)
                  sh         s4, -539(s1)
                  sb         a6, -66(s1)
                  lbu        t0, 897(t6)
                  sh         s8, 3(a4)
                  lbu        s7, 266(s1)
                  lbu        s10, -1(a4)
                  lhu        a1, 829(s1)
                  lb         t0, -8(a7)
                  lbu        t3, 19(a4)
                  lbu        zero, 130(a5)
                  sb         a1, 291(t6)
                  sh         ra, 557(a5)
                  lbu        a3, 529(s1)
                  sb         t0, 638(t6)
                  sb         s3, 210(s1)
                  sw         a6, -416(t6)
                  lb         a6, 669(t6)
                  lbu        t5, -55(s1)
                  sw         sp, 25(a4)
                  sb         t1, 0(a7)
                  sb         a7, -758(a5)
                  lb         ra, 999(t6)
                  sh         s10, 649(a5)
                  lh         a0, 23(a4)
                  lb         s5, -15(a7)
                  sb         a2, -520(a5)
                  lb         t0, 60(a4)
                  lb         a3, 5(a7)
                  lb         s10, 832(a5) #end load_store_instr_stream_3
                  lb         ra, 12(a4)
                  lb         s3, -7(a7) #end load_store_instr_stream_4
                  lb         s7, -44(a4) #end load_store_instr_stream_2
                  lb         s5, 647(t6)
                  lh         t3, -990(t6) #end load_store_instr_stream_1
                  lhu        s11, -121(s1) #end load_store_instr_stream_0
599:              mulhu      s4, s2, t2
                  c.and      a2, s0
                  xor        a5, zero, tp
                  xori       s1, s3, 350
                  add        t0, s8, a3
604:              add        s1, t6, sp
                  divu       a6, s7, s8
                  srai       a3, a5, 24
607:              xor        s4, sp, a5
                  .4byte 0x00100073 # ebreak
                  srai       t0, t6, 3
                  c.srli     a0, 30
                  auipc      a3, 472884
                  mulh       t0, t5, s6
                  divu       t2, a1, sp
                  c.nop
615:              sltiu      a3, s4, -795
                  xori       a6, ra, 786
                  nop
                  bgeu       a6, t6, 631f
                  blt        zero, s1, 636f
                  c.nop
                  c.beqz     s0, 633f
                  slt        t3, a3, s11
                  c.xor      a1, a3
                  divu       a4, s11, a3
                  lui        s3, 532002
                  beq        zero, tp, 634f
                  div        a5, t4, t3
                  ori        s6, t2, 860
                  srai       a2, s6, 27
                  csrrci     a0, 0x340, 28
631:              remu       s5, gp, t0
                  nop
633:              c.srai     a0, 7
634:              sltiu      a3, s4, -777
                  xori       s7, t4, -181
636:              srl        tp, a7, s4
                  add        a1, t3, s10
                  c.andi     a4, -15
                  xor        s5, a4, s10
                  csrrsi     s10, 0x340, 8
                  slli       t5, s7, 24
                  auipc      s7, 203673
                  divu       s4, t4, t0
                  andi       s2, a3, -628
                  bge        s6, s4, 662f
                  c.li       s11, -4
                  sub        ra, zero, s11
                  c.beqz     a4, 668f
                  div        t1, s1, a3
                  c.sub      a5, a1
                  bge        a3, t2, 670f
                  bge        a3, s6, 672f
                  beq        s4, t0, 658f
                  beq        s0, s8, 674f
                  lui        a3, 402310
                  div        t1, s0, a5
                  slti       s4, s1, 931
658:              .4byte 0x00100073 # ebreak
                  csrrsi     ra, 0x340, 19
                  srli       tp, a7, 20
                  sll        a3, s8, a1
662:              srli       s0, s1, 18
                  c.bnez     s0, 678f
                  c.add      a3, s7
                  sra        s10, t4, gp
                  c.srai     a4, 30
                  c.slli     s4, 26
668:              c.and      a5, a0
                  srli       t2, a6, 30
670:              csrrsi     s10, 0x340, 0
                  c.xor      a4, a2
672:              sltiu      a3, s6, -802
                  xor        a5, t5, ra
674:              c.srai     a2, 22
                  csrrci     t3, 0x340, 11
                  rem        zero, t0, t3
                  add        a2, s8, t5
678:              c.xor      s0, s0
                  sltiu      s6, s3, -674
                  andi       s4, a6, -591
                  addi       a6, t6, -254
                  c.bnez     a3, 693f
                  add        a6, a6, t5
                  csrrci     a0, 0x340, 29
                  c.ebreak;c.nop;
                  .4byte 0x00100073 # ebreak
                  c.srli     s1, 17
                  sra        t3, t1, s4
                  xor        s0, s4, t3
                  c.xor      a3, a3
                  c.beqz     a0, 707f
                  c.mv       t0, a1
693:              div        s3, s2, a6
                  ori        a6, s10, -862
                  slt        t4, t0, s9
                  nop
                  c.mv       gp, s1
                  sltu       s1, t1, a0
                  bltu       t2, s8, 715f
                  bltu       s5, t2, 720f
                  csrrsi     t4, 0x340, 15
                  mulhu      t2, a3, t5
                  slli       a2, sp, 31
                  xor        s3, t1, t1
                  bgeu       t1, s10, 724f
                  csrrsi     s6, 0x340, 20
707:              andi       t6, a4, 807
                  xor        a1, ra, t3
                  addi       a6, zero, 2 #init loop 0 counter
                  c.nop
                  c.addi     s10, -8
                  c.sub      a3, a2
                  addi       t0, zero, -9 #init loop 0 limit
                  c.mv       s6, t0
                  mulhu      s4, sp, s5
                  csrrs      t2, 0x340, s6
                  c.add      a2, s2
                  csrrsi     zero, 0x340, 3
                  sltu       s3, a4, s8
                  c.addi     a3, -14
                  csrrw      ra, 0x340, a2
                  remu       a0, t5, t6
                  and        t2, t0, s10
                  sub        s6, t5, s8
                  csrrc      a4, 0x340, t2
                  c.li       s0, 20
                  c.li       s6, -20
                  csrrc      a7, 0x340, t3
sub_4_13_0_t:     c.lui      ra, 28
                  addi       a6, a6, -1 #update loop 0 counter
                  divu       a3, s7, a0
                  and        a4, t4, s5
                  sub        s11, s10, s1
                  rem        zero, s1, a1
                  srai       gp, gp, 14
                  beq        a6, t0, sub_4_13_0_t #branch for loop 0
                  and        s3, t0, s3
                  sll        a1, t2, a5
                  csrrs      a0, 0x340, sp
                  slli       s3, a7, 21
                  srai       a7, t3, 31
                  c.nop
                  sub        s6, a4, s7
715:              c.add      a5, a6
                  c.xor      a1, a4
                  remu       t6, s9, s6
                  lui        tp, 221489
                  lui        s0, 464350
720:              xori       a5, s8, -879
                  sll        s3, a1, zero
                  c.and      a2, a0
                  slt        a4, a5, t4
724:              csrrci     t0, 0x340, 25
                  srl        a0, t0, s2
                  bne        s5, s2, 739f
                  slti       tp, a5, -643
                  c.and      a4, a5
                  c.and      a1, a0
                  ori        a0, ra, -609
                  blt        t0, s5, 742f
                  bne        s4, s1, 751f
                  div        s3, zero, a3
                  nop
                  xori       a5, t6, 12
                  andi       zero, zero, 578
                  c.bnez     a4, 755f
                  c.add      s2, t5
739:              .4byte 0x00100073 # ebreak
                  xori       zero, s6, 829
                  beq        t6, s3, 758f
742:              or         t1, a3, a3
                  bge        s5, s1, 758f
                  lui        t3, 694317
                  c.andi     a0, -7
                  lui        s1, 712598
                  or         s2, s3, t3
                  csrrwi     a4, 0x340, 4
                  srli       s2, a7, 11
                  srl        s5, t0, t4
751:              c.lui      t1, 29
                  c.ebreak;c.nop;
                  div        a7, t2, a3
                  ori        t5, s2, -231
755:              rem        t2, a5, t6
                  c.mv       s5, s6
                  c.beqz     s0, 768f
758:              rem        s0, a2, t5
                  divu       s7, ra, t6
                  nop
                  c.nop
                  c.addi     s6, 10
                  auipc      s2, 878289
                  c.andi     a3, -8
                  csrrw      gp, 0x340, t5
                  andi       tp, t6, 588
                  c.add      a2, sp
768:              csrrc      s11, 0x340, s2
                  slt        t2, a4, a7
                  c.mv       t5, s0
                  c.sub      a3, a1
                  bge        t2, t1, 787f
                  addi       t3, t1, -51
                  slti       a0, s0, 905
                  mulhsu     a7, t1, t0
                  c.li       a3, -22
                  csrrsi     a6, 0x340, 30
                  c.slli     s11, 31
                  csrrwi     s6, 0x340, 9
                  .4byte 0x00100073 # ebreak
                  c.nop
                  div        tp, s5, s9
                  csrrsi     a2, 0x340, 1
                  slli       a4, sp, 14
                  sltu       a5, a3, ra
                  or         s2, t3, s11
787:              bge        t1, s0, 792f
                  slt        s7, t4, a7
                  csrrci     tp, 0x340, 0
                  mul        t4, a7, s11
                  c.srli     a4, 18
792:              csrrw      s1, 0x340, a6
                  xor        s6, a6, t0
                  c.or       a5, a5
                  sll        t6, a7, a7
                  c.andi     a5, -11
                  c.srai     a3, 20
                  csrrwi     a6, 0x340, 1
                  c.li       a4, -20
                  csrrw      s1, 0x340, a2
                  ori        s10, s6, 870
                  divu       s6, s0, t5
                  c.addi     a5, -15
                  beq        s5, s2, 820f
                  mulhu      t2, a0, tp
                  sub        s6, t5, s3
                  mul        t2, a6, t5
                  remu       s4, a6, s5
                  beq        a6, a3, 828f
                  mulhu      gp, t6, s0
                  div        s5, t2, t3
                  bne        s6, t5, 814f
                  and        a4, a3, t2
814:              slli       s1, s7, 5
                  mul        a7, s3, s11
                  add        a2, s0, ra
                  c.nop
                  sll        tp, a0, s10
                  c.beqz     s0, 839f
820:              mulhsu     a1, s4, sp
                  sra        t2, s8, a5
                  addi       s5, t5, -435
                  c.or       a4, a2
                  remu       a6, a0, s11
                  add        t2, s5, t1
                  bgeu       a2, s9, 832f
                  c.and      a1, s1
828:              sra        a5, a0, a2
                  sltiu      t4, s2, 94
                  csrrci     s6, 0x340, 23
                  lui        s4, 300824
832:              bltu       a0, ra, 840f
                  sltiu      a2, s1, -268
                  sub        a3, s5, a1
                  csrrwi     s6, 0x340, 6
                  and        a7, a7, s9
                  bltu       a3, t4, 850f
                  c.nop
839:              bgeu       a5, s4, 859f
840:              c.andi     a4, -24
                  c.beqz     s1, 856f
                  mulh       t5, tp, s8
                  c.xor      a3, a5
                  srai       a0, s7, 14
                  bne        t1, a0, 849f
                  nop
                  xor        t3, s3, a0
                  .4byte 0x00100073 # ebreak
849:              divu       t1, s5, zero
850:              c.li       s10, 22
                  srli       s3, t1, 28
                  ori        s1, a2, 549
                  .4byte 0x00100073 # ebreak
                  or         t1, s10, a0
                  mul        s1, s5, s4
856:              bge        gp, s7, 874f
                  c.add      t2, t2
                  csrrsi     s4, 0x340, 3
859:              sltiu      a3, sp, 382
                  .4byte 0x00100073 # ebreak
                  c.srai     s1, 2
                  c.li       s4, 16
                  auipc      t5, 199554
                  c.addi     t2, 17
                  addi       s6, t6, -11
                  rem        a4, s1, s7
                  lui        a0, 621383
                  andi       a7, s2, 215
                  c.li       s1, 21
                  xor        s2, s10, t5
                  c.andi     s1, -13
                  csrrs      a0, 0x340, s10
                  slti       a6, t2, 33
874:              andi       a2, s2, 185
                  xori       s11, t4, 334
                  c.add      s0, a6
                  csrrwi     t1, 0x340, 16
                  remu       tp, s4, t4
                  slli       s7, t5, 22
                  c.andi     s0, -21
                  .4byte 0x00100073 # ebreak
                  slli       t0, s0, 12
                  and        s7, a0, sp
                  nop
                  srli       a2, t3, 12
                  csrrc      s3, 0x340, a2
                  c.or       a0, s0
                  srl        s3, s6, a7
                  bne        s1, zero, 909f
                  sltiu      s0, a3, 139
                  c.slli     t3, 8
                  mulhsu     s3, s1, s9
                  la         a0, region_4+1257 #start riscv_load_store_rand_instr_stream_1
                  sh         s0, -1(a0)
                  c.srai     a1, 13
                  sw         a6, 11(a0)
                  mulhsu     s4, a2, s8
                  sb         a6, -7(a0)
                  lb         s5, -8(a0)
                  sh         tp, 1(a0)
                  mulh       s3, s7, t1
                  sub        s4, sp, a0
                  lb         s5, 16(a0)
                  lb         s1, 8(a0)
                  c.srai     a3, 14
                  remu       t2, tp, s10
                  sltu       ra, s3, a4
                  lbu        a2, -6(a0)
                  and        t2, t0, gp
                  c.nop
                  sw         ra, 15(a0)
                  mulhsu     s2, sp, s1
                  sw         a5, 11(a0)
                  lbu        zero, 14(a0)
                  slli       a5, t1, 24
                  csrrwi     t2, 0x340, 4
                  sh         a0, 7(a0)
                  slti       t0, a4, 922
                  lb         t2, 4(a0)
                  sh         ra, 9(a0)
                  lhu        s5, 5(a0)
                  rem        ra, sp, a2
                  lbu        s6, -15(a0)
                  lbu        s2, -10(a0)
                  sll        s4, a0, s11
                  lhu        t6, -13(a0)
                  lui        s1, 453200
                  lb         s1, -11(a0)
                  c.srai     a5, 26
                  c.and      a1, a4
                  c.lui      s5, 2
                  sb         s9, -12(a0)
                  c.srli     a2, 7
                  srl        zero, s3, s5
                  lb         t1, -6(a0)
                  c.mv       s10, s10
                  lb         t0, 12(a0)
                  divu       a6, a7, zero
                  csrrwi     s5, 0x340, 18
                  lh         t3, -13(a0) #end riscv_load_store_rand_instr_stream_1
                  csrrw      t3, 0x340, ra
                  xori       t0, a7, -264
                  sll        s3, s8, a7
                  mulhsu     a3, a6, a6
                  srli       t1, t3, 15
                  csrrc      s6, 0x340, a0
                  sltu       a4, t4, s10
                  srai       s7, s11, 19
                  csrrwi     gp, 0x340, 24
                  rem        t4, a6, zero
                  c.and      a4, a3
                  c.ebreak;c.nop;
                  sub        a5, a4, s9
                  csrrw      a6, 0x340, s1
                  add        a6, s11, t4
                  add        gp, s3, s7
909:              c.srli     a1, 10
                  bgeu       a1, s4, 926f
                  bge        t6, s11, 928f
                  rem        s11, a2, a2
                  xor        t5, a0, s2
                  c.beqz     s1, 926f
                  c.srli     a1, 2
                  mulh       a4, ra, s9
                  mulh       a3, a5, t5
                  c.ebreak;c.nop;
                  csrrw      s3, 0x340, s3
                  divu       s3, t6, ra
                  c.or       a0, a0
                  mul        tp, tp, s6
                  c.andi     s1, 17
                  c.xor      a1, a0
                  csrrwi     s11, 0x340, 25
926:              divu       s3, t3, a3
                  beq        t5, t4, 938f
928:              xor        s11, s5, t4
                  c.lui      s0, 8
                  sll        t2, s10, t3
                  csrrs      a0, 0x340, t6
                  slt        t3, a3, s11
                  csrrwi     t1, 0x340, 20
                  lui        ra, 505293
                  csrrwi     zero, 0x340, 29
                  sltu       t6, t4, gp
                  div        s5, zero, tp
938:              slti       s5, s8, 621
                  lw         gp, 4(sp)
                  and        a4, s8, a2
                  addi       sp, sp, 36
                  ori        s2, t4, 171
                  srl        s7, s7, a4
                  c.or       a2, a2
                  nop
                  c.mv       s4, a1
                  c.or       a4, a5
                  c.ebreak;c.nop;
1530:             c.jr x3
sub_5:            srai       t5, a2, 8
                  c.sub      a5, a2
                  c.and      a0, s0
                  nop
                  addi       sp, sp, -16
                  c.mv       a3, s9
                  sll        t6, s7, a2
                  mul        a6, t1, a7
                  sw         gp, 4(sp)
                  c.slli     s2, 4
                  la         s11, region_0+3728 #start riscv_hazard_instr_stream_1
                  sb         t1, -5(s11)
                  lbu        t1, -8(s11)
                  sb         t1, 9(s11)
                  lb         a5, 15(s11)
                  sb         t1, -13(s11)
                  lbu        t1, 9(s11)
                  lbu        t3, -5(s11)
                  csrrwi     s5, 0x340, 30
                  sb         s5, -15(s11)
                  lb         t1, -15(s11)
                  lh         t1, -14(s11)
                  xori       t3, t1, 259
                  lb         t3, -13(s11)
                  sh         t3, 6(s11)
                  lbu        a2, -1(s11)
                  sh         a1, -8(s11)
                  csrrw      a1, 0x340, a2
                  lb         a2, -1(s11)
                  lbu        a2, -15(s11)
                  sh         t1, -16(s11)
                  lbu        a5, -6(s11)
                  c.srai     a2, 10
                  sb         t1, 11(s11)
                  sra        a5, s5, t3
                  sra        s5, t1, s5
                  lb         a1, -15(s11)
                  or         a2, t3, a1
                  lhu        t3, 6(s11)
                  lhu        t1, -6(s11)
                  c.slli     a5, 18
                  lh         s5, 8(s11)
                  c.lui      s5, 20
                  lh         a5, 0(s11)
                  c.mv       s5, t3
                  lbu        a2, -1(s11)
                  lb         t1, 11(s11) #end riscv_hazard_instr_stream_1
                  la         t2, region_4+4005 #start load_store_instr_stream_3
                  la         s10, region_2+5 #start load_store_instr_stream_0
                  lh         a6, -1(s10)
                  sb         gp, 1(s10)
                  la         s6, region_3+50 #start load_store_instr_stream_1
                  sb         a4, 5(s6)
                  lbu        a6, -7(t2)
                  lbu        s2, 37(t2)
                  la         t5, region_1+9371 #start load_store_instr_stream_2
                  lh         t6, 25(t2)
                  sh         s2, -87(t5)
                  sw         gp, 13(t5)
                  lhu        a4, 13(s10)
                  lb         t0, 13(s6)
                  sb         a4, -16(s6)
                  sb         a5, 16(s10)
                  sh         s10, 23(t2)
                  lw         s2, -159(t5)
                  lb         gp, -16(s6)
                  sb         s2, 11(s10)
                  lb         t3, 51(t5)
                  sb         s11, 2(s10)
                  lh         gp, -1(s10)
                  lbu        a3, 10(t2)
                  lbu        s5, 4(s10)
                  sh         s2, -67(t5)
                  sh         sp, 0(s6)
                  lhu        zero, 5(s10)
                  lbu        zero, 25(t2)
                  lhu        t1, -15(t2)
                  lb         a0, -35(t2)
                  sh         t2, 31(t5)
                  lb         s1, 14(t2)
                  lbu        t3, 85(t5)
                  sw         tp, -6(s6) #end load_store_instr_stream_1
                  lbu        s7, 103(t5) #end load_store_instr_stream_2
                  lh         a6, 17(t2) #end load_store_instr_stream_3
                  lbu        zero, -2(s10) #end load_store_instr_stream_0
                  la         tp, region_4+254 #start riscv_load_store_rand_instr_stream_1
                  lb         ra, 481(tp)
                  lbu        a4, -711(tp)
                  sb         s10, -157(tp)
                  sb         a6, 183(tp)
                  lui        a0, 328074
                  sh         t1, 552(tp)
                  lbu        s10, -69(tp)
                  remu       a3, t2, t6
                  csrrwi     t1, 0x340, 25
                  and        t5, s6, a0
                  sll        gp, ra, a5
                  csrrs      s4, 0x340, s11
                  lb         t3, 349(tp)
                  lh         a1, 628(tp)
                  c.slli     s11, 4
                  c.ebreak;c.nop;
                  sh         tp, -462(tp)
                  rem        s2, t6, t4
                  srai       a1, a2, 0
                  lbu        a2, -741(tp)
                  lb         a6, 809(tp)
                  sra        t4, a0, tp
                  sh         s4, -206(tp)
                  sh         a3, -288(tp)
                  lhu        s2, -74(tp)
                  lbu        s3, 187(tp)
                  sh         ra, 242(tp)
                  lbu        a4, 894(tp)
                  csrrs      s7, 0x340, t3
                  c.nop
                  sb         s2, 176(tp)
                  rem        t5, zero, a6
                  c.ebreak;c.nop;
                  addi       a3, a0, 1005
                  sh         s0, 476(tp)
                  sub        a5, zero, a5
                  lbu        a1, -17(tp)
                  sb         t1, -135(tp) #end riscv_load_store_rand_instr_stream_1
sub_5_2:          jal        gp, 8f
0:                c.jal      15f
1:                c.j        3f
2:                jal        t0, 14f
3:                jal        ra, 4f
4:                jal        ra, 0b
5:                jal        s2, 11f
6:                c.j        5b
7:                c.j        9f
8:                c.j        18f
9:                jal        t1, 16f
10:               jal        t1, 19f
11:               c.jal      1b
12:               c.j        13f
13:               c.j        7b
14:               c.jal      6b
15:               jal        t1, 12b
16:               jal        ra, 17f
17:               c.jal      21f
18:               c.j        20f
19:               c.j        2b
20:               c.jal      10b
21:               mul        a0, s8, tp
                  la         ra, region_3+293 #start load_store_instr_stream_0
                  la         a5, region_3+501 #start load_store_instr_stream_3
                  la         t6, region_3+368 #start load_store_instr_stream_2
                  la         t0, region_3+130 #start load_store_instr_stream_1
                  sb         t5, 40(ra)
                  lbu        s1, -55(a5)
                  lb         zero, -59(ra)
                  sh         t3, 21(ra)
                  lh         a6, 54(t6)
                  lbu        a4, 16(ra)
                  sb         a0, 7(t6)
                  sb         s6, -60(ra)
                  lbu        t5, -3(t0)
                  sb         a3, -35(t6)
                  sh         a1, -28(t6)
                  sw         s5, -10(t0)
                  sb         a4, -184(a5)
                  sb         s9, 49(t6)
                  lbu        zero, 56(ra)
                  lb         gp, -137(a5)
                  sb         s10, -42(ra)
                  sb         zero, -5(t0)
                  sb         gp, -112(a5)
                  sb         tp, -248(a5)
                  lbu        s11, -13(t0)
                  lb         t3, -48(ra)
                  lhu        s4, -12(t6)
                  lbu        tp, -16(t0)
                  sh         a7, 12(t6)
                  lhu        a4, -215(a5) #end load_store_instr_stream_3
                  lbu        s3, 5(t0)
                  lhu        gp, 2(t0) #end load_store_instr_stream_1
                  sb         s3, 59(t6) #end load_store_instr_stream_2
                  lbu        a0, -14(ra) #end load_store_instr_stream_0
                  la         t6, region_3+228 #start riscv_load_store_rand_instr_stream_0
                  lhu        a5, 146(t6)
                  lh         tp, 22(t6)
                  c.ebreak;c.nop;
                  c.li       a0, -13
                  lbu        a1, 245(t6)
                  lhu        s6, -108(t6)
                  sb         s9, -184(t6)
                  rem        a2, s6, s9
                  lb         s0, 75(t6)
                  csrrw      t4, 0x340, ra
                  ori        s10, a6, -267
                  c.add      a3, s2
                  mulhu      a5, gp, s6
                  srai       zero, a4, 14
                  lb         a1, -79(t6)
                  srli       zero, s2, 22
                  lb         s11, 114(t6)
                  sltu       a1, s3, t1
                  sra        gp, s0, t5
                  .4byte 0x00100073 # ebreak
                  xori       t4, s9, 34
                  nop
                  lb         s0, -67(t6)
                  lhu        s11, -92(t6)
                  sb         t2, -39(t6)
                  sub        ra, a3, a2
                  xor        zero, t5, s0
                  mul        gp, t0, s6
                  lb         t4, -77(t6)
                  srli       a1, a3, 20
                  lbu        a4, 237(t6)
                  c.nop
                  lbu        s7, 69(t6)
                  c.srai     a5, 14
                  sw         a3, -216(t6)
                  divu       a2, s1, ra
                  rem        tp, t1, a7
                  lbu        a3, 143(t6)
                  lbu        s11, 173(t6)
                  mulh       a7, t5, s5
                  lh         s0, 8(t6)
                  sh         sp, 230(t6)
                  c.lui      s1, 28
                  sb         s4, 248(t6)
                  and        zero, t5, zero
                  ori        t5, t2, 227
                  lbu        a1, -132(t6)
                  lbu        a1, 42(t6)
                  sb         a5, -88(t6)
                  sw         t5, -108(t6)
                  lb         a1, -39(t6) #end riscv_load_store_rand_instr_stream_0
                  la         t4, region_2+6486 #start load_store_instr_stream_1
                  la         s1, region_0+3012 #start load_store_instr_stream_0
                  lb         a5, 15(t4)
                  la         s6, region_4+1799 #start load_store_instr_stream_3
                  la         ra, region_3+336 #start load_store_instr_stream_2
                  lb         s2, 207(s1)
                  sb         a7, -7(s6)
                  lhu        a7, 0(t4)
                  sb         a1, 8(t4)
                  lbu        a1, -77(ra)
                  lbu        zero, 645(s1)
                  lw         t6, -228(ra)
                  sb         a3, 455(s1)
                  lb         a6, -10(s6)
                  lb         a2, -95(ra)
                  lbu        s4, -969(s1)
                  sb         t4, 139(ra)
                  sb         s6, -63(ra)
                  lh         a1, -57(s6)
                  lhu        s5, 2(t4)
                  sb         s1, 4(t4)
                  sb         a5, -36(s6)
                  sb         s11, 29(s6)
                  lbu        a6, -43(ra)
                  lb         gp, -10(s6)
                  lh         a7, -890(s1)
                  lbu        s4, -125(s1)
                  sw         t6, -23(s6)
                  lhu        a0, 4(t4)
                  sb         a0, 91(ra)
                  lhu        s10, -68(ra)
                  sb         s0, 801(s1)
                  lb         a1, -46(s6) #end load_store_instr_stream_3
                  sw         a6, 14(t4) #end load_store_instr_stream_1
                  sb         t0, -197(ra)
                  sb         a2, 875(s1)
                  lb         a4, -141(ra) #end load_store_instr_stream_2
                  lb         s0, 319(s1)
                  sb         s7, 43(s1) #end load_store_instr_stream_0
sub_5_3:          jal        gp, 12f
0:                jal        tp, 5f
1:                jal        ra, 3f
2:                c.jal      9f
3:                c.j        13f
4:                jal        ra, 6f
5:                jal        tp, 1b
6:                jal        t1, 0b
7:                c.jal      2b
8:                jal        ra, 10f
9:                jal        t1, 11f
10:               c.j        7b
11:               c.j        4b
12:               jal        ra, 8b
13:               divu       s3, t0, s3
                  la         t1, region_0+2530 #start riscv_hazard_instr_stream_0
                  sb         a6, -1(t1)
                  c.srli     a2, 11
                  lw         t6, 38(t1)
                  and        a4, t6, a1
                  lb         s11, 63(t1)
                  lbu        a4, 64(t1)
                  csrrw      a2, 0x340, s11
                  sw         a1, -18(t1)
                  sb         t6, -19(t1)
                  sub        a1, a2, t6
                  sb         s11, 39(t1)
                  lui        a4, 799675
                  csrrc      a6, 0x340, s11
                  lb         t6, -1(t1)
                  sw         a2, 42(t1)
                  lh         a2, 32(t1)
                  nop
                  srli       t6, s11, 24
                  c.andi     a1, 13
                  c.sub      a2, a4
                  lh         s11, -10(t1)
                  lb         a1, 61(t1)
                  c.addi     a6, -9
                  ori        s11, a6, -573
                  sltiu      a1, a4, -146
                  sw         a1, -18(t1)
                  lbu        a6, -33(t1)
                  sh         a1, 4(t1)
                  csrrw      a6, 0x340, a1
                  sb         a2, 5(t1)
                  c.nop
                  sb         a1, -31(t1)
                  lhu        a1, 2(t1) #end riscv_hazard_instr_stream_0
                  ori        tp, a7, -906
                  mulh       a1, a5, a3
                  c.li       t0, 6
                  sub        a2, t0, s0
                  divu       a0, gp, ra
                  c.xor      a4, s1
                  bge        gp, s8, 8f
                  auipc      t4, 402073
8:                c.sub      s1, s1
                  csrrsi     s11, 0x340, 8
                  sltiu      s10, ra, 811
                  div        tp, s7, s10
                  bne        s9, a1, 29f
                  bne        s9, a3, 33f
                  mulhsu     a3, s3, s11
                  c.and      a3, a0
                  c.and      s1, a0
                  csrrci     s0, 0x340, 6
                  bgeu       zero, t3, 37f
                  bgeu       gp, s1, 27f
                  nop
                  xor        a3, a1, t1
                  sra        a3, a1, a5
                  c.addi     a0, -32
                  sll        a4, a6, t2
                  csrrwi     a3, 0x340, 1
                  rem        s3, t0, t2
27:               beq        a3, gp, 41f
                  bne        a7, zero, 35f
29:               bne        s10, a1, 48f
                  lui        t0, 209065
                  slt        t1, t3, s2
                  mul        s0, t5, s5
33:               bge        s4, s11, 46f
                  andi       s4, a1, -855
35:               srli       t0, s11, 2
                  beq        s9, a6, 56f
37:               bgeu       a1, s7, 47f
                  c.lui      t2, 30
                  slli       a6, s6, 28
                  c.and      a0, a2
41:               slti       s1, t5, 145
                  or         s5, sp, t5
                  add        s11, a4, t4
                  c.sub      a4, s1
                  addi       t1, t3, 180
46:               andi       a3, t6, -597
47:               c.srli     s1, 22
48:               .4byte 0x00100073 # ebreak
                  beq        a2, a0, 69f
                  c.nop
                  c.nop
                  c.add      s2, t1
                  beq        s0, s5, 72f
                  c.mv       a3, s1
                  c.bnez     a2, 58f
56:               .4byte 0x00100073 # ebreak
                  csrrw      t2, 0x340, s10
58:               blt        s1, ra, 73f
                  srl        t6, t2, zero
                  srli       a7, a3, 31
                  .4byte 0x00100073 # ebreak
                  c.mv       s2, s8
                  rem        t2, s1, s5
                  srl        tp, sp, a4
                  andi       s2, s10, 267
                  c.andi     a4, -30
                  andi       s1, a4, 272
                  add        tp, a4, t1
69:               auipc      t1, 537810
                  c.add      a3, a6
                  addi       a0, ra, -794
72:               mulhsu     t6, a6, s7
73:               c.andi     s0, 24
                  c.and      s1, a1
                  mulhu      t2, s10, s2
                  c.srai     a0, 17
                  c.xor      s0, s1
                  c.add      s11, a7
                  c.bnez     s1, 85f
                  or         a3, a1, a4
                  xori       a3, a4, -907
                  c.add      t6, t5
                  remu       s6, s3, a7
                  c.slli     s10, 16
85:               ori        s10, s11, 796
                  c.or       a4, a2
                  csrrci     t3, 0x340, 7
                  andi       s2, ra, -907
                  c.or       a2, s0
                  c.li       a0, -32
                  c.nop
                  c.slli     ra, 29
                  slt        s5, t5, gp
                  c.srai     s0, 12
                  xori       t5, t0, -1012
                  slli       s6, a1, 28
                  ori        t5, s3, 977
                  mulhu      t5, s7, s3
                  csrrs      ra, 0x340, sp
                  nop
                  c.andi     s0, 31
                  bge        s3, s8, 112f
                  c.nop
                  slli       t0, a0, 26
                  sltu       s11, s0, a4
                  c.mv       s1, ra
                  remu       a5, s3, s11
                  sltu       a3, s2, ra
                  mulh       a3, s7, s7
                  sub        s5, s4, t2
                  c.nop
112:              c.bnez     a3, 124f
                  c.srai     a5, 13
                  sll        zero, s8, t6
                  xor        s6, t1, a0
                  .4byte 0x00100073 # ebreak
                  nop
                  bne        t3, tp, 131f
                  c.bnez     s1, 137f
                  divu       zero, t0, s0
                  srli       a3, t5, 5
                  csrrwi     s5, 0x340, 15
                  csrrw      s11, 0x340, s2
124:              c.xor      s1, s0
                  csrrs      s6, 0x340, a6
                  nop
                  c.bnez     s1, 141f
                  mul        s5, s1, t5
                  or         s5, t5, s9
                  srl        zero, a2, tp
131:              srli       gp, s3, 16
                  lui        s0, 272294
                  mulhsu     a0, a3, t0
                  bltu       s2, s8, 144f
                  csrrci     s5, 0x340, 23
                  srli       s0, s2, 22
137:              sltu       t2, a0, a5
                  mulhsu     a3, t0, sp
                  c.srai     a3, 16
                  c.and      s1, s0
141:              auipc      s2, 616637
                  add        ra, s6, t0
                  csrrs      t3, 0x340, s10
144:              slt        s2, ra, a0
                  c.lui      s1, 24
                  andi       s1, a4, 769
                  c.addi     a5, 29
                  srli       s5, a7, 11
                  srl        t3, ra, t2
                  c.xor      a3, s0
                  mulh       t4, a0, s1
                  mulh       t5, s2, a0
                  c.addi     s11, -29
                  nop
                  csrrsi     s7, 0x340, 25
                  csrrsi     s0, 0x340, 12
                  c.addi     s4, 2
                  c.slli     s6, 27
                  c.andi     a0, 25
                  sltiu      ra, t5, -1
                  addi       t2, a0, -371
                  c.mv       s3, a0
                  mulhsu     a6, s7, s10
                  andi       s1, a6, -23
                  addi       t4, s8, 496
                  mulhu      ra, a4, s3
                  sltiu      t1, gp, 498
                  nop
                  csrrwi     zero, 0x340, 1
                  xori       t3, s10, -160
                  c.or       s0, a0
                  div        t0, a2, sp
                  andi       s5, s10, 1018
                  rem        t5, t0, tp
                  sra        a1, t0, t1
                  divu       s10, s1, t5
                  sltiu      s4, a2, 173
                  c.nop
                  c.and      a4, a4
                  c.li       t6, -21
                  lui        s4, 819528
                  nop
                  nop
                  and        s7, s11, a5
                  and        t5, a5, s5
                  c.beqz     a2, 197f
                  sll        s0, ra, a3
                  andi       t2, sp, 656
                  csrrs      s6, 0x340, gp
                  c.bnez     a0, 208f
                  csrrw      tp, 0x340, s0
                  c.lui      t3, 13
                  lui        a6, 873107
                  c.ebreak;c.nop;
                  c.bnez     a1, 203f
                  xor        a1, gp, a2
197:              c.li       s3, -1
                  remu       s10, t2, zero
                  srli       t1, a3, 11
                  lui        t4, 656843
                  bge        sp, s9, 218f
                  andi       t0, a5, 212
203:              c.addi     t1, 12
                  c.and      a4, a0
                  beq        t6, s7, 209f
                  c.addi     t3, -29
                  xor        gp, sp, a1
208:              c.sub      a2, a4
209:              slt        t4, a1, s2
                  ori        a7, s5, 974
                  addi       a2, s1, 178
                  c.nop
                  beq        s6, a1, 224f
                  .4byte 0x00100073 # ebreak
                  csrrw      a6, 0x340, s2
                  slli       s6, s8, 3
                  sra        s2, s10, s10
218:              nop
                  c.andi     s0, 13
                  addi       a3, zero, -7 #init loop 0 counter
                  sub        t3, zero, a3
                  sra        t1, a3, s10
                  sub        zero, a1, zero
                  sll        a0, a5, t0
                  andi       s6, t5, 590
                  csrrs      s5, 0x340, s0
                  csrrw      a2, 0x340, sp
                  srl        s11, s10, t6
                  rem        zero, s4, zero
                  addi       t0, s7, -461
                  c.slli     a6, 31
                  rem        s6, tp, t5
                  sltiu      a4, s4, 332
                  addi       tp, zero, -10 #init loop 0 limit
                  remu       a4, a6, a0
                  sra        s6, a2, s10
sub_5_8_0_t:      divu       zero, tp, s4
                  .4byte 0x00100073 # ebreak
                  c.sub      a1, a1
                  csrrsi     zero, 0x340, 18
                  addi       a3, a3, -6 #update loop 0 counter
                  srli       s2, t4, 21
                  ori        t5, s2, -720
                  c.xor      a2, a3
                  bge        a3, tp, sub_5_8_0_t #branch for loop 0
                  c.mv       s5, t4
                  csrrwi     tp, 0x340, 25
                  mulhsu     a4, s0, a4
                  c.li       s5, 0
                  addi       t0, a0, -641
224:              remu       tp, a4, s1
                  mul        zero, s5, s4
                  bltu       t2, s8, 242f
                  c.addi     t0, -32
                  c.lui      s6, 29
                  sltu       s10, s3, t0
                  or         s0, a4, t0
                  .4byte 0x00100073 # ebreak
                  sra        s3, a4, tp
                  csrrc      t6, 0x340, tp
                  csrrsi     t3, 0x340, 25
                  slt        ra, a7, t0
                  slli       ra, sp, 12
                  csrrs      s6, 0x340, a7
                  andi       t0, t6, 448
                  xor        s0, t4, s6
                  blt        t1, zero, 256f
                  c.or       a0, a3
242:              c.nop
                  auipc      t2, 1045254
                  c.lui      a0, 6
                  div        s2, a5, s10
                  xor        a2, s5, zero
                  xor        s7, s1, zero
                  slti       a1, t2, -942
                  slt        t5, t0, t1
                  bne        s2, t5, 270f
                  xor        tp, a2, t1
                  sra        gp, t3, s9
                  srli       zero, s7, 20
                  auipc      s10, 801478
                  c.andi     a2, 5
256:              xori       s4, a1, 979
                  andi       s5, a0, -713
                  csrrci     gp, 0x340, 12
                  sltiu      t5, sp, 41
                  csrrsi     ra, 0x340, 2
                  c.andi     a4, 27
                  c.bnez     a4, 281f
                  sra        a4, gp, t5
                  c.srai     a4, 10
                  xori       t4, t5, -491
                  c.srai     a5, 1
                  c.and      a2, s0
                  c.xor      a4, a4
                  mulhu      ra, t5, s6
270:              lui        s2, 588349
                  c.beqz     s0, 282f
                  beq        a1, a7, 285f
                  bge        a6, a6, 292f
                  bltu       tp, a7, 282f
                  c.and      s0, s0
                  bne        a7, s8, 289f
                  ori        t0, t5, 230
                  and        t3, t6, a7
                  divu       a0, s6, s3
                  mul        a6, t4, s4
281:              c.bnez     a4, 284f
282:              bltu       s2, t4, 301f
                  srli       tp, a1, 17
284:              divu       ra, sp, t2
285:              mulhu      s1, s3, a4
                  csrrw      s2, 0x340, a3
                  sll        s7, ra, s4
                  c.srai     a5, 14
289:              .4byte 0x00100073 # ebreak
                  sltiu      a4, tp, 67
                  c.li       s0, -18
292:              c.lui      s4, 2
                  c.xor      a0, a4
                  andi       t6, ra, -114
                  csrrci     a7, 0x340, 4
                  c.addi     t4, 27
                  bne        s0, s5, 315f
                  srai       t3, s9, 7
                  sra        s0, s6, zero
                  c.xor      a3, a3
301:              bge        s7, a1, 318f
                  bgeu       t2, s8, 308f
                  c.or       a3, a3
                  c.add      s6, s9
                  c.addi     s11, -4
                  slli       s11, tp, 29
                  lui        a6, 433343
308:              sll        s1, s5, t2
                  bgeu       s4, s7, 319f
                  bge        s11, a6, 322f
                  c.or       s0, a2
                  mulhsu     t6, a6, a2
                  xor        s10, s4, t6
                  c.addi     t3, 15
315:              lui        a3, 598733
                  add        s6, a7, a5
                  c.srai     a5, 9
318:              or         gp, ra, t3
319:              c.beqz     a2, 330f
                  addi       s1, a6, 821
                  div        s10, a1, tp
322:              c.or       a2, a2
                  or         a7, a6, t6
                  c.nop
                  c.slli     t3, 6
                  bgeu       s8, a2, 342f
                  sra        tp, a6, s5
                  addi       ra, t0, 636
                  bge        t6, t1, 337f
330:              c.xor      a4, a5
                  c.add      s1, t4
                  srl        s4, a2, a7
                  csrrc      a2, 0x340, s9
                  c.or       a2, a3
                  c.srli     a3, 31
                  csrrc      a5, 0x340, s6
337:              sra        s5, t3, s11
                  sltiu      a2, t0, -920
                  sub        s5, ra, s1
                  add        t0, a7, t0
                  mulhu      gp, a5, s7
342:              remu       gp, tp, t3
                  nop
                  c.ebreak;c.nop;
                  bltu       gp, a4, 361f
                  slti       a3, t4, 956
                  c.ebreak;c.nop;
                  remu       s4, s1, s7
                  c.sub      a3, a3
                  c.or       a5, s1
                  srli       s10, zero, 10
                  mul        s0, a1, s4
                  srl        a2, s6, s4
                  xori       s6, s3, -970
                  andi       s11, a6, -1023
                  bgeu       s4, t6, 370f
                  sll        a3, t2, ra
                  c.add      gp, s0
                  c.beqz     s0, 374f
                  la         s2, region_2+171 #start load_store_instr_stream_3
                  la         a7, region_2+7396 #start load_store_instr_stream_2
                  sb         ra, -256(s2)
                  la         t5, region_2+4838 #start load_store_instr_stream_1
                  la         s4, region_2+7226 #start load_store_instr_stream_0
                  sb         gp, -168(s2)
                  lh         a5, 16(s4)
                  sb         t2, 362(a7)
                  sh         gp, -2(t5)
                  lhu        a6, 662(a7)
                  lb         ra, 416(s2)
                  sb         t4, -9(s4)
                  sb         s9, 434(a7)
                  lw         tp, 480(a7)
                  lbu        a5, -3(t5)
                  sb         a5, -193(s2)
                  lb         s3, -9(s4)
                  lhu        tp, 0(t5)
                  lb         s10, 279(s2)
                  sw         t2, -6(s4)
                  lb         s10, -114(a7)
                  sw         t0, 693(s2)
                  lb         t4, 983(a7)
                  lbu        t3, 11(t5)
                  lb         t2, 656(s2)
                  lb         a2, 5(s4)
                  lb         s10, 11(s4)
                  lbu        a5, 58(a7)
                  sh         s2, -57(s2)
                  lw         s6, 560(a7) #end load_store_instr_stream_2
                  sh         a3, 781(s2) #end load_store_instr_stream_3
                  lbu        a5, -9(t5) #end load_store_instr_stream_1
                  lbu        t2, 5(s4) #end load_store_instr_stream_0
                  sra        s1, sp, a5
361:              csrrc      s10, 0x340, sp
                  c.bnez     a1, 376f
                  srli       s10, zero, 24
                  c.srli     a3, 28
                  c.nop
                  divu       s10, s1, s8
                  auipc      s5, 810864
                  c.nop
                  c.srli     a5, 9
370:              sub        s10, s1, a0
                  c.beqz     a1, 391f
                  bge        s8, gp, 374f
                  blt        t2, t3, 383f
374:              slt        a6, s5, t4
                  c.nop
376:              addi       a0, zero, -541
                  xor        a1, a0, s4
                  rem        s11, a4, zero
                  c.slli     s6, 29
                  bne        s8, sp, 384f
                  srai       tp, s7, 8
                  remu       tp, a6, a5
383:              or         s7, t2, t6
384:              .4byte 0x00100073 # ebreak
                  srli       s4, a5, 13
                  c.or       s0, a5
                  ori        t2, s11, 116
                  mulhu      a5, t3, t2
                  sra        gp, a6, tp
                  bne        sp, s4, 407f
391:              mul        s6, t1, tp
                  sltiu      s1, gp, -910
                  c.lui      a3, 8
                  mulh       a2, s5, zero
                  mulh       t0, a0, zero
                  c.or       a1, a2
                  sub        s6, t2, a6
                  c.ebreak;c.nop;
                  c.nop
                  c.srli     a0, 28
                  bge        zero, ra, 421f
                  lui        a1, 125172
                  csrrs      ra, 0x340, a5
                  c.sub      a2, a2
                  xor        t2, s8, sp
                  c.xor      a3, a3
407:              auipc      tp, 103940
                  sltu       s3, a6, a7
                  mul        a2, a3, t4
                  auipc      a2, 948988
                  c.srli     a3, 21
                  c.srai     a3, 30
                  c.nop
                  srli       gp, a1, 14
                  bne        ra, a4, 433f
                  c.and      a3, a3
                  c.or       a3, a5
                  c.slli     s7, 30
                  slli       t6, a2, 19
                  srai       s3, t0, 21
421:              c.and      a0, a2
                  csrrs      t1, 0x340, a7
                  bgeu       s0, a2, 430f
                  nop
                  blt        t6, t1, 435f
                  andi       t3, a1, -429
                  c.beqz     a3, 443f
                  csrrc      t1, 0x340, gp
                  c.or       a3, a2
430:              c.or       a4, s0
                  c.srai     a5, 29
                  c.slli     s6, 10
433:              slt        t5, t4, s4
                  rem        t0, s3, sp
435:              bne        s2, a7, 454f
                  csrrs      zero, 0x340, a3
                  mulhsu     s7, s3, sp
                  add        t4, t3, s6
                  sll        s11, tp, s8
                  div        s1, s0, s3
                  csrrc      t5, 0x340, tp
                  c.sub      a2, a5
443:              csrrc      s3, 0x340, s0
                  c.and      a1, a4
                  div        t6, a1, a4
                  c.sub      a4, s0
                  csrrs      s7, 0x340, t2
                  slt        s2, s4, sp
                  sltiu      a5, s9, 622
                  beq        a6, t5, 470f
                  c.addi     s3, 28
                  mulhsu     a7, s0, t5
                  c.srai     a3, 8
454:              add        t1, t0, s7
                  c.beqz     a5, 468f
                  bge        t0, a0, 473f
                  c.andi     a1, 6
                  and        a3, s7, t6
                  add        t3, tp, s8
                  slli       s2, s6, 21
                  nop
                  ori        s3, a5, 839
                  or         a6, a6, gp
                  lui        s5, 922184
                  srl        t6, s1, s5
                  sll        gp, a1, t5
                  mulhu      s3, t3, t4
468:              andi       t3, s11, 726
                  and        zero, t1, a0
470:              csrrc      a0, 0x340, gp
                  c.andi     a1, 4
                  rem        s11, zero, sp
473:              csrrw      zero, 0x340, a6
                  c.srli     s0, 11
                  csrrci     s0, 0x340, 15
                  c.addi     t3, 12
                  csrrc      a2, 0x340, a2
                  mulhsu     ra, a2, a5
                  c.bnez     a0, 496f
                  or         a3, a1, gp
                  ori        t6, s5, -1020
                  c.srai     s1, 31
                  sll        t0, t2, t0
                  c.add      s2, s7
                  sll        t1, s3, s11
                  slli       t3, s8, 26
                  sll        a1, s1, a0
                  c.addi     a1, -13
                  add        a5, s8, t1
                  mulhu      a7, s9, s4
                  addi       s10, s8, -377
                  sra        a6, s2, a4
                  addi       t2, s4, -69
                  addi       s1, s4, -161
                  slt        a3, s11, a4
496:              .4byte 0x00100073 # ebreak
                  slti       tp, a5, 254
                  and        t4, s2, a6
                  c.nop
                  beq        sp, a7, 508f
                  mulh       zero, gp, sp
                  sub        a1, t1, s1
                  c.add      gp, t1
                  sll        s3, t2, t5
                  mulhu      zero, s6, zero
                  add        s6, a3, s11
                  c.srai     a3, 6
508:              ori        zero, t1, -402
                  csrrs      s6, 0x340, a3
                  mulhu      t2, s9, s8
                  lui        a1, 877662
                  ori        t6, a0, 903
                  c.sub      s1, a1
                  csrrwi     s3, 0x340, 27
                  c.beqz     s1, 521f
                  ori        a4, s2, 457
                  c.srai     s1, 20
                  add        s1, s8, s11
                  c.beqz     a5, 532f
                  c.ebreak;c.nop;
521:              xori       s10, a1, -711
                  c.beqz     s1, 530f
                  and        t3, a6, t0
                  lui        zero, 578180
                  c.beqz     a0, 536f
                  c.sub      s0, a5
                  slli       t1, s11, 10
                  or         s0, t6, s9
                  c.beqz     s0, 539f
530:              and        a6, a7, a0
                  slt        s1, ra, a2
532:              sltiu      t0, s1, 819
                  c.li       t2, 17
                  c.ebreak;c.nop;
                  c.xor      a5, a5
536:              srli       zero, gp, 20
                  srai       a2, a1, 15
                  xor        s0, zero, s9
539:              sltiu      s7, s5, -857
                  csrrc      t2, 0x340, sp
                  csrrs      t1, 0x340, t4
                  c.mv       s6, t3
                  c.li       t6, 29
                  slli       s0, s0, 4
                  slt        s5, a5, a6
                  or         a7, s0, a0
                  mulhu      ra, t2, s11
                  mulhu      s4, s2, t3
                  c.mv       tp, a1
                  div        a6, a1, s8
                  beq        s7, sp, 561f
                  lui        a4, 978872
                  sra        a0, a4, tp
                  c.beqz     a3, 573f
                  c.or       a1, s1
                  c.lui      s0, 2
                  c.and      a3, a2
                  srl        s1, gp, gp
                  c.beqz     a3, 566f
                  sltu       t1, s7, s2
561:              c.bnez     a4, 581f
                  c.sub      a5, a1
                  mulhu      t2, ra, s0
                  or         t4, a7, s10
                  c.nop
566:              div        t3, s7, t6
                  mulhu      a7, s4, a3
                  or         a7, a5, s7
                  c.slli     t0, 25
                  c.sub      a4, a4
                  c.bnez     a0, 589f
                  bne        s4, t4, 574f
573:              bge        ra, a0, 576f
574:              c.beqz     a5, 592f
                  mulhsu     zero, s3, t4
576:              bltu       a3, a1, 592f
                  div        t6, s0, s8
                  mulhsu     a2, t3, s11
                  c.andi     a4, -17
                  mulhu      a2, tp, s7
581:              slti       t2, s0, -975
                  blt        s5, s8, 586f
                  div        a1, a3, a4
                  add        a6, a3, zero
                  nop
586:              c.sub      a4, s0
                  or         a5, s0, a4
                  lui        gp, 600974
589:              slti       s5, a2, -441
                  bgeu       gp, gp, 592f
                  c.or       a1, a4
592:              mulhu      s4, a6, a2
                  sltiu      s1, s11, -210
                  lw         gp, 4(sp)
                  .4byte 0x00100073 # ebreak
                  add        t2, t0, a7
                  add        t0, s4, a4
                  remu       t3, sp, a0
                  slli       a5, s8, 3
                  addi       sp, sp, 16
                  c.mv       s10, s2
                  mulhsu     a3, a1, a4
                  divu       ra, a3, s3
985:              c.jr x3
sub_1:            lui        s2, 809301
                  sub        ra, t3, t6
                  divu       tp, s3, s10
                  addi       sp, sp, -36
                  sw         gp, 4(sp)
                  c.ebreak;c.nop;
                  c.srli     s0, 5
                  slti       t1, s3, -611
                  mul        a5, a7, t5
                  la         s11, region_3+142 #start riscv_hazard_instr_stream_5
                  lbu        t3, -15(s11)
                  lb         a7, 13(s11)
                  sltiu      s4, a4, 385
                  c.slli     tp, 18
                  sb         s4, 13(s11)
                  csrrci     a7, 0x340, 14
                  lbu        tp, 3(s11)
                  sb         tp, -7(s11)
                  sb         t3, 13(s11)
                  sb         t3, 5(s11)
                  lbu        a7, 1(s11)
                  sb         s4, 15(s11)
                  c.sub      a4, a4
                  lb         t3, 13(s11)
                  sb         a4, 5(s11)
                  lhu        tp, -10(s11)
                  sb         t3, -15(s11)
                  lbu        tp, 3(s11)
                  sb         a4, 4(s11)
                  sb         t3, 2(s11)
                  lbu        t6, 12(s11)
                  lh         a4, -2(s11)
                  csrrsi     t3, 0x340, 2
                  c.ebreak;c.nop;
                  sb         a4, -2(s11)
                  sb         t6, 0(s11)
                  lbu        tp, 15(s11)
                  lb         t3, -4(s11)
                  c.and      a4, a4
                  lui        t6, 630497
                  lhu        t3, 16(s11)
                  lhu        a4, -4(s11)
                  c.srai     a4, 15
                  lb         tp, -9(s11)
                  lw         a7, -14(s11)
                  sb         s4, -8(s11)
                  lbu        a7, 16(s11)
                  sltiu      t3, t3, 169
                  lhu        t6, 0(s11) #end riscv_hazard_instr_stream_5
                  la         a1, region_4+3339 #start riscv_hazard_instr_stream_11
                  sb         t2, -12(a1)
                  lbu        a2, -1(a1)
                  lh         a4, -1(a1)
                  c.srli     a4, 14
                  sh         s1, 11(a1)
                  add        a4, s1, a4
                  srl        t2, a2, s1
                  sb         t2, 9(a1)
                  c.xor      a2, a2
                  lb         t2, 15(a1)
                  lbu        t2, 16(a1)
                  slt        t2, s11, a2
                  lh         t2, -15(a1)
                  mulhu      a4, a6, s1
                  lbu        a6, 14(a1)
                  sb         a2, -14(a1)
                  lbu        t2, -8(a1)
                  srli       t2, a4, 25
                  lhu        s1, -5(a1)
                  sb         a2, 2(a1)
                  sh         s11, -13(a1)
                  sra        a6, t2, a2
                  lb         s11, -2(a1)
                  srli       a6, a4, 24
                  sb         s1, -16(a1)
                  c.ebreak;c.nop;
                  c.slli     t2, 29
                  sb         s1, 12(a1)
                  sb         a2, -12(a1)
                  lbu        a6, -16(a1)
                  lb         s1, -5(a1)
                  c.nop
                  remu       a6, a4, s1
                  lb         t2, -13(a1)
                  lbu        s11, 16(a1)
                  lbu        a4, -11(a1)
                  lbu        s1, 11(a1)
                  sh         t2, 3(a1)
                  lb         s1, -4(a1)
                  lb         a6, 16(a1)
                  sb         s11, 10(a1)
                  lui        a6, 699600
                  xori       t2, t2, 261
                  lbu        s11, 0(a1) #end riscv_hazard_instr_stream_11
                  la         a5, region_4+3428 #start load_store_instr_stream_2
                  la         s0, region_1+3960 #start load_store_instr_stream_1
                  lhu        a6, 10(a5)
                  lb         s7, 15(a5)
                  lbu        tp, 5(s0)
                  sw         s11, -16(a5)
                  lbu        s2, -7(s0)
                  la         s10, region_0+1867 #start load_store_instr_stream_0
                  sb         s6, 8(s0)
                  lb         a3, 38(s10)
                  sb         t0, 2(a5)
                  sb         s2, -13(a5)
                  lb         s1, -5(s0)
                  lb         s1, -7(s0)
                  lbu        t5, 30(s10)
                  sb         t4, 9(a5)
                  sh         a4, 14(s0)
                  lb         t0, -12(s0)
                  sb         a2, -11(a5)
                  lhu        zero, 8(s0) #end load_store_instr_stream_1
                  lb         a0, 16(a5)
                  sb         a5, 64(s10)
                  lw         t5, 45(s10)
                  sb         s8, 1(a5) #end load_store_instr_stream_2
                  sb         s9, -14(s10) #end load_store_instr_stream_0
                  la         a0, region_3+85 #start load_store_instr_stream_0
                  la         t2, region_4+2037 #start load_store_instr_stream_2
                  lhu        s5, 11(a0)
                  la         t4, region_2+4117 #start load_store_instr_stream_3
                  la         a3, region_1+2137 #start load_store_instr_stream_4
                  la         s0, region_0+2644 #start load_store_instr_stream_1
                  lbu        t6, 6(a3)
                  lbu        s6, -2(t2)
                  lhu        s3, 1(t4)
                  lb         s10, 93(s0)
                  lb         s5, -2(t2)
                  sb         gp, -6(a3)
                  sh         t1, 13(t4)
                  sb         a5, -14(a0)
                  sh         a5, 814(s0)
                  lbu        zero, 13(t4)
                  sh         t4, -35(a0)
                  lh         a1, 272(s0)
                  sw         a3, -840(s0)
                  lw         t3, -53(a3)
                  sb         t2, 28(a0)
                  lb         s4, -28(a3)
                  lb         s4, -12(t4)
                  lb         t6, 8(t2)
                  sb         a6, -55(t2)
                  lbu        gp, 957(s0)
                  sh         s5, -49(a3)
                  sh         a5, -51(t2)
                  lbu        a5, 13(a3)
                  sb         ra, 56(a0)
                  sb         a6, -50(t2)
                  lbu        a2, 0(t4) #end load_store_instr_stream_3
                  lbu        t6, -34(t2)
                  lbu        a5, 845(s0)
                  sb         s7, -8(a3)
                  sb         a1, 27(a3)
                  lbu        t0, -8(t2)
                  lbu        s6, 8(a0)
                  sh         a4, 194(s0) #end load_store_instr_stream_1
                  sb         gp, -8(a0)
                  lb         t1, 19(a0)
                  lb         t1, -29(t2) #end load_store_instr_stream_2
                  lhu        a5, -3(a3) #end load_store_instr_stream_4
                  lw         t6, -1(a0) #end load_store_instr_stream_0
                  la         s11, region_1+1943 #start riscv_hazard_instr_stream_9
                  c.nop
                  .4byte 0x00100073 # ebreak
                  lbu        s7, 16(s11)
                  lh         t1, 3(s11)
                  sw         t1, -3(s11)
                  lh         t4, 11(s11)
                  sra        t1, t1, t1
                  mul        t4, s0, s1
                  sltu       s0, s7, s0
                  divu       tp, t4, s7
                  c.or       s1, s1
                  lh         s7, 15(s11)
                  divu       s1, s7, tp
                  lb         t4, -4(s11)
                  lbu        t4, -6(s11)
                  sb         t4, 4(s11)
                  mul        t4, t4, tp
                  lb         tp, -5(s11)
                  mulhu      t4, s1, s1
                  lb         s7, 0(s11)
                  mulhsu     s7, s7, s7
                  mulhsu     t4, t4, t1
                  mulh       tp, t1, s0
                  sh         tp, -13(s11)
                  div        s0, t4, t4
                  sb         s7, 16(s11)
                  sh         s7, 5(s11)
                  lh         t1, -13(s11)
                  lhu        s1, 11(s11)
                  lbu        t1, -10(s11)
                  lbu        s1, -4(s11)
                  lb         tp, 9(s11)
                  c.lui      s1, 10
                  add        t1, s0, s7
                  sub        s7, s1, t4
                  lb         t1, -2(s11)
                  sb         t4, 10(s11)
                  lb         s7, 8(s11)
                  c.sub      s0, s1
                  mulhu      s1, s7, s7
                  sb         tp, -2(s11)
                  lb         t1, -3(s11)
                  lbu        s7, 12(s11)
                  sb         t4, 5(s11)
                  sb         tp, 15(s11)
                  mulhsu     s1, s0, tp
                  csrrc      s1, 0x340, s7
                  lbu        tp, -10(s11) #end riscv_hazard_instr_stream_9
sub_1_17:         jal        gp, 6f
0:                c.j        13f
1:                jal        ra, 8f
2:                jal        ra, 11f
3:                c.j        15f
4:                jal        t1, 2b
5:                c.jal      10f
6:                jal        s4, 22f
7:                c.j        5b
8:                jal        ra, 12f
9:                c.j        18f
10:               c.jal      14f
11:               c.jal      7b
12:               jal        tp, 17f
13:               c.jal      1b
14:               jal        s4, 28f
15:               jal        s11, 25f
16:               c.jal      30f
17:               jal        ra, 29f
18:               c.j        26f
19:               jal        a0, 0b
20:               c.j        3b
21:               jal        ra, 19b
22:               c.j        27f
23:               jal        a5, 20b
24:               jal        ra, 9b
25:               c.j        24b
26:               jal        ra, 21b
27:               jal        ra, 4b
28:               jal        a2, 23b
29:               c.j        16b
30:               remu       t6, a3, t0
                  la         t5, region_0+1764 #start load_store_instr_stream_1
                  la         s4, region_4+2629 #start load_store_instr_stream_2
                  la         s2, region_2+5644 #start load_store_instr_stream_0
                  lhu        a5, -696(t5)
                  lb         zero, -557(s2)
                  la         a2, region_1+16332 #start load_store_instr_stream_3
                  lb         s7, -9(a2)
                  sh         a0, -168(s2)
                  lbu        s10, -195(t5)
                  lh         t6, 12(a2)
                  lb         a3, 22(s4)
                  lbu        ra, 271(t5)
                  lbu        zero, -5(s4)
                  lhu        ra, -10(a2)
                  lhu        s1, -320(s2)
                  lh         s5, 14(a2)
                  lbu        ra, 53(s4)
                  sw         a1, 19(s4)
                  lhu        a6, -626(t5)
                  lbu        s5, 60(s4) #end load_store_instr_stream_2
                  lb         a6, 190(s2)
                  lb         a6, -475(t5)
                  lbu        s0, 255(s2)
                  lb         t2, -12(a2)
                  lbu        t1, -13(a2)
                  lbu        a5, -869(t5) #end load_store_instr_stream_1
                  lb         a6, -6(a2) #end load_store_instr_stream_3
                  sh         a3, -428(s2) #end load_store_instr_stream_0
                  la         t0, region_1+1233 #start riscv_load_store_rand_instr_stream_8
                  .4byte 0x00100073 # ebreak
                  lb         s11, 174(t0)
                  lbu        s0, 85(t0)
                  sub        t6, a4, s11
                  lb         gp, 41(t0)
                  lb         a0, -43(t0)
                  lbu        zero, 82(t0)
                  lb         s5, 135(t0)
                  or         t1, t3, s0
                  lb         t4, 241(t0)
                  sb         s9, 132(t0)
                  lbu        gp, 16(t0)
                  c.nop
                  lbu        t2, 34(t0)
                  mulhsu     t2, s8, t2
                  lb         a1, -224(t0)
                  lhu        a0, 81(t0)
                  sb         a0, -219(t0)
                  lbu        a2, 20(t0)
                  csrrsi     ra, 0x340, 28
                  lw         t3, 215(t0)
                  c.addi     a6, -8
                  c.srai     a3, 29
                  divu       t5, s5, a1
                  lb         a2, -200(t0)
                  lb         s2, 156(t0)
                  lb         s5, 74(t0)
                  csrrsi     s3, 0x340, 12
                  lb         a2, 140(t0)
                  add        a2, t0, ra
                  lb         a5, 32(t0)
                  xor        a1, s6, t3
                  csrrci     s3, 0x340, 8
                  lb         a4, -114(t0)
                  c.nop
                  lh         s10, -39(t0)
                  csrrs      s3, 0x340, s9
                  csrrw      tp, 0x340, a1
                  slti       s7, s2, -284
                  lbu        a1, -192(t0)
                  lb         s10, -252(t0)
                  sb         ra, 168(t0)
                  .4byte 0x00100073 # ebreak
                  srl        s1, tp, s7
                  lbu        s0, -228(t0)
                  c.li       a7, -21
                  lbu        s0, 120(t0)
                  sb         ra, -92(t0) #end riscv_load_store_rand_instr_stream_8
                  addi       s0, zero, -3 #init loop 1 counter
                  addi       s11, zero, 14 #init loop 1 limit
sub_1_65_1_t:     sltiu      t4, t6, -852
                  addi       s0, s0, 6 #update loop 1 counter
                  c.lui      s3, 21
                  addi       a3, zero, 9 #init loop 0 counter
                  addi       s2, zero, 4 #init loop 0 limit
                  mulh       t3, a7, s7
sub_1_65_0_t:     csrrsi     s6, 0x340, 18
                  addi       a3, a3, -1 #update loop 0 counter
                  nop
                  bgeu       a3, s2, sub_1_65_0_t #branch for loop 0
                  bltu       s0, s11, sub_1_65_1_t #branch for loop 1
                  mulh       t0, gp, a1
                  la         t3, region_1+3038 #start load_store_instr_stream_1
                  sb         s6, -29(t3)
                  la         a2, region_2+6888 #start load_store_instr_stream_2
                  lbu        s1, -13(a2)
                  la         a1, region_0+3420 #start load_store_instr_stream_0
                  lbu        s5, -15(a2)
                  lhu        ra, -28(t3)
                  lb         t2, 3(a2)
                  sh         ra, 14(a2)
                  sb         a5, -133(a1)
                  sh         a5, -100(a1)
                  lbu        tp, -8(a2)
                  lhu        s4, -8(t3)
                  lb         s11, 235(a1)
                  sb         a2, -65(t3)
                  sh         a6, -16(a2)
                  lh         a5, -4(a1)
                  lb         s4, -10(a2) #end load_store_instr_stream_2
                  sb         a6, -6(t3)
                  sb         a1, 139(a1)
                  lh         a3, -60(t3)
                  lhu        s11, -182(t3)
                  lbu        a3, 145(a1)
                  sh         s10, 202(a1)
                  sh         s10, 242(a1)
                  lbu        a6, -167(a1)
                  sb         s3, 57(t3) #end load_store_instr_stream_1
                  sb         t5, 180(a1) #end load_store_instr_stream_0
                  la         a6, region_2+6753 #start load_store_instr_stream_1
                  la         s0, region_2+5757 #start load_store_instr_stream_2
                  lbu        t0, 10(a6)
                  la         s1, region_2+5604 #start load_store_instr_stream_0
                  lh         t4, -15(a6)
                  lh         a2, -251(s0)
                  sb         ra, -4(a6)
                  lb         s5, 133(s1)
                  lbu        ra, -381(s1)
                  lhu        s7, 1(a6)
                  sb         s1, 126(s0)
                  lbu        t1, -686(s0)
                  lb         s10, -74(s0)
                  lbu        s3, -779(s1)
                  lb         t5, -9(a6)
                  sw         a1, 416(s1)
                  lh         t5, -5(a6) #end load_store_instr_stream_1
                  sb         t0, 920(s1)
                  lbu        t4, -858(s0)
                  sb         a3, 199(s1)
                  lw         t5, -44(s1)
                  sw         t3, 540(s1)
                  lbu        ra, -938(s0) #end load_store_instr_stream_2
                  lbu        a5, -258(s1) #end load_store_instr_stream_0
                  la         a1, region_4+845 #start riscv_load_store_rand_instr_stream_0
                  c.add      a4, t3
                  c.li       s4, 24
                  lhu        a3, 43(a1)
                  csrrw      zero, 0x340, a6
                  csrrs      s2, 0x340, a4
                  c.srli     a0, 3
                  csrrsi     s11, 0x340, 17
                  c.addi     s6, -20
                  lh         t6, -45(a1)
                  xori       t5, a1, 318
                  slli       s0, t0, 22
                  mulhu      tp, s10, t3
                  lui        tp, 922128
                  lbu        s1, 45(a1)
                  sh         t1, -35(a1)
                  csrrs      a0, 0x340, a3
                  c.addi     s5, -30
                  sb         s10, 43(a1)
                  c.andi     a4, -21
                  lh         a0, -43(a1)
                  xori       tp, a7, 9
                  slti       t3, t2, 760
                  addi       s1, tp, -462
                  mulhu      zero, s3, s9
                  remu       s11, s9, t5
                  csrrwi     tp, 0x340, 16
                  c.or       a5, a1
                  csrrc      s4, 0x340, t6
                  auipc      t5, 862105
                  and        a0, ra, zero
                  .4byte 0x00100073 # ebreak
                  lh         s1, -15(a1)
                  sb         a1, 20(a1)
                  lb         a7, -20(a1)
                  mulhsu     a7, zero, s7
                  divu       s5, s2, s9
                  or         s10, t4, a6
                  c.addi     a7, -1
                  srli       s3, t5, 25
                  lb         t2, 61(a1) #end riscv_load_store_rand_instr_stream_0
sub_1_22:         jal        gp, 1f
0:                c.j        26f
1:                c.jal      21f
2:                c.jal      27f
3:                c.j        23f
4:                jal        ra, 12f
5:                c.j        29f
6:                jal        ra, 7f
7:                jal        t1, 19f
8:                c.j        24f
9:                c.jal      15f
10:               jal        a4, 17f
11:               jal        ra, 8b
12:               jal        ra, 25f
13:               c.j        2b
14:               jal        t3, 13b
15:               c.j        4b
16:               c.j        22f
17:               jal        tp, 9b
18:               c.jal      0b
19:               c.j        18b
20:               jal        t6, 5b
21:               jal        t1, 10b
22:               jal        t0, 11b
23:               jal        ra, 16b
24:               jal        ra, 28f
25:               c.j        14b
26:               c.jal      20b
27:               jal        s2, 3b
28:               c.jal      6b
29:               c.srai     a4, 29
                  la         s5, region_2+1454 #start load_store_instr_stream_3
                  la         t0, region_2+860 #start load_store_instr_stream_0
                  sb         t1, 15(s5)
                  la         a0, region_2+7805 #start load_store_instr_stream_1
                  sb         ra, -13(s5)
                  la         s0, region_2+4887 #start load_store_instr_stream_2
                  lbu        s7, 5(s5)
                  lb         t6, 481(s0)
                  lbu        a3, 3(t0)
                  sb         s7, -16(a0)
                  lb         s10, 6(a0)
                  sb         s1, -9(s5)
                  sh         a7, -6(s5)
                  lbu        t3, 584(s0)
                  lbu        a6, -13(a0)
                  lhu        t4, 12(s5)
                  lhu        t1, 63(a0)
                  lhu        t2, -14(s5)
                  lb         gp, -808(s0)
                  lhu        gp, 419(s0)
                  sh         a1, -6(t0)
                  lh         a1, 29(a0)
                  lhu        t5, 319(s0)
                  sb         s5, -1012(s0)
                  sb         s0, 6(t0)
                  lh         tp, -10(s5)
                  sb         a0, -494(s0)
                  lb         s11, 442(s0)
                  lbu        t6, -10(t0)
                  lbu        a3, -10(s5)
                  lbu        ra, -3(t0)
                  lbu        t4, 48(a0) #end load_store_instr_stream_1
                  lb         gp, 852(s0)
                  lbu        a1, 819(s0) #end load_store_instr_stream_2
                  sb         t1, 11(s5) #end load_store_instr_stream_3
                  sb         ra, 3(t0) #end load_store_instr_stream_0
                  la         gp, region_1+11720 #start load_store_instr_stream_1
                  sb         s10, 759(gp)
                  la         s4, region_1+7872 #start load_store_instr_stream_4
                  la         s11, region_1+2767 #start load_store_instr_stream_0
                  sb         t4, 295(s4)
                  sb         t1, 640(s4)
                  lhu        s10, -776(gp)
                  lb         zero, -411(gp)
                  la         s1, region_1+6895 #start load_store_instr_stream_2
                  la         a4, region_1+10970 #start load_store_instr_stream_3
                  lbu        a6, 338(s4)
                  lhu        ra, 13(s1)
                  lbu        s0, -787(gp)
                  sb         gp, 3(s1)
                  lb         s7, -2(s1)
                  lb         t3, 378(s4)
                  lh         s3, 1(s1)
                  lb         s5, 41(s4)
                  sb         tp, 231(s11)
                  lb         s7, -66(s11)
                  lbu        t5, 763(s4)
                  lbu        ra, -15(s1)
                  lbu        t0, 219(a4)
                  lhu        a3, -40(a4)
                  lbu        s10, -127(gp)
                  lb         a6, 806(gp)
                  lb         zero, 0(s11)
                  sh         s2, 336(gp) #end load_store_instr_stream_1
                  lhu        a3, -26(a4)
                  sb         t6, -689(s4)
                  lb         ra, -12(s1)
                  sb         gp, 72(s11)
                  lhu        t3, 44(a4)
                  lh         s10, 15(s1)
                  lh         t6, -60(a4) #end load_store_instr_stream_3
                  lbu        a6, -2(s1) #end load_store_instr_stream_2
                  lb         s5, 809(s4) #end load_store_instr_stream_4
                  sb         s2, -126(s11) #end load_store_instr_stream_0
                  la         tp, region_1+9603 #start riscv_hazard_instr_stream_10
                  sh         ra, 13(tp)
                  c.mv       a6, t6
                  auipc      t5, 770602
                  sb         a1, 8(tp)
                  xor        a6, a6, a1
                  addi       ra, a6, -881
                  lbu        ra, 13(tp)
                  lb         t5, -5(tp)
                  or         a1, a6, a1
                  c.nop
                  sb         ra, -8(tp)
                  ori        a6, a2, 259
                  lbu        a1, 7(tp)
                  csrrwi     a2, 0x340, 5
                  slt        a1, ra, ra
                  lbu        a6, 14(tp)
                  srl        t5, a6, a6
                  lui        t5, 526491
                  sw         t5, 5(tp)
                  mul        a6, a1, a6
                  sb         a1, 7(tp)
                  sb         a2, -8(tp)
                  srl        a1, ra, t6
                  divu       a1, a1, a6
                  lw         a6, -11(tp)
                  slti       t5, ra, 737
                  c.slli     ra, 10
                  lb         t5, -15(tp)
                  sb         a1, -16(tp)
                  lb         t5, -6(tp)
                  c.mv       t6, a1
                  lb         a2, 2(tp)
                  lb         ra, -1(tp)
                  xori       t6, t6, -346
                  csrrc      t6, 0x340, a1
                  srl        ra, a2, ra
                  c.xor      a1, a1
                  lbu        t6, 0(tp)
                  lbu        a6, -13(tp)
                  xori       a2, a1, 635
                  sb         a6, -14(tp)
                  lhu        t6, -1(tp)
                  lh         a1, -9(tp)
                  lb         ra, -4(tp)
                  sb         t5, -4(tp)
                  lbu        a2, 8(tp)
                  mulhsu     a2, a6, ra
                  and        a1, a6, ra
                  lbu        a6, -8(tp)
                  mulhsu     t5, a1, a1
                  csrrsi     ra, 0x340, 29
                  lhu        a6, 3(tp)
                  sb         ra, -12(tp)
                  sh         ra, 15(tp)
                  mulhu      t5, t5, a2
                  lb         a1, 10(tp)
                  nop
                  lb         t5, -12(tp) #end riscv_hazard_instr_stream_10
                  la         gp, region_1+7888 #start load_store_instr_stream_0
                  la         a7, region_3+217 #start load_store_instr_stream_1
                  lbu        a0, 15(gp)
                  sb         a5, -19(gp)
                  lb         s11, 17(a7)
                  lbu        zero, 201(gp)
                  lb         s1, 26(a7)
                  sb         s1, -91(gp)
                  sb         t2, -5(gp)
                  lbu        t3, -36(a7)
                  lbu        s2, -11(a7)
                  lb         t0, 49(a7)
                  lhu        t2, 230(gp)
                  lbu        a3, 121(gp)
                  lbu        a6, 48(a7)
                  lh         a6, 21(a7)
                  lbu        tp, 181(gp)
                  lb         ra, -30(a7)
                  lbu        a3, -50(a7) #end load_store_instr_stream_1
                  lbu        t2, 197(gp) #end load_store_instr_stream_0
                  la         t3, region_2+1770 #start riscv_hazard_instr_stream_6
                  c.add      s0, s2
                  mul        zero, zero, s0
                  lbu        s10, -44(t3)
                  div        a5, a5, a5
                  lbu        s10, 49(t3)
                  c.andi     s0, -25
                  nop
                  add        s2, s10, s10
                  lb         s2, 33(t3)
                  sb         a5, -2(t3)
                  sb         a0, 9(t3)
                  lb         a5, 12(t3)
                  sb         s10, -9(t3)
                  lbu        a0, -33(t3)
                  lui        s2, 562367
                  c.add      s2, s0
                  sb         a5, -44(t3)
                  sb         zero, -45(t3)
                  c.ebreak;c.nop;
                  lb         s0, -14(t3)
                  lb         a5, -43(t3)
                  c.and      a0, a0
                  c.srai     a0, 7
                  or         s10, zero, a5
                  c.andi     a5, 16
                  lb         a0, -45(t3)
                  c.srai     a0, 1
                  andi       a5, a5, 635
                  lb         a5, -13(t3)
                  c.sub      s0, s0
                  or         a0, s0, zero
                  sb         s10, 62(t3)
                  srl        s10, s0, a5
                  csrrwi     s10, 0x340, 24
                  and        s10, s2, s0
                  sh         a5, -48(t3)
                  csrrs      s0, 0x340, a5
                  sb         s10, 39(t3)
                  lbu        s10, -61(t3)
                  c.nop
                  c.xor      a5, a0
                  lhu        zero, -14(t3)
                  lbu        a0, -15(t3)
                  lb         s0, 41(t3)
                  lbu        s10, -57(t3) #end riscv_hazard_instr_stream_6
                  la         t5, region_0+3923 #start load_store_instr_stream_3
                  la         tp, region_1+849 #start load_store_instr_stream_2
                  la         s11, region_2+2032 #start load_store_instr_stream_1
                  sb         a0, 799(s11)
                  la         s2, region_4+2381 #start load_store_instr_stream_0
                  lh         gp, -552(s11)
                  lbu        a6, 8(tp)
                  sb         s8, -859(s11)
                  lh         s6, -3(s2)
                  lh         t3, -13(tp)
                  sb         a4, 0(tp)
                  lb         a7, -218(t5)
                  lbu        s6, 6(tp)
                  lbu        t1, -62(t5)
                  lbu        t0, 52(t5)
                  sb         s7, 676(s11)
                  lh         a4, 5(tp)
                  lbu        s0, -15(s2)
                  lh         a7, -1(s2)
                  lbu        s1, -125(t5)
                  lb         t4, -14(tp) #end load_store_instr_stream_2
                  lh         a5, 286(s11)
                  sw         s4, -9(s2)
                  lbu        zero, -239(s11)
                  sw         t4, -99(t5)
                  lhu        s6, 204(s11)
                  lw         zero, -75(t5) #end load_store_instr_stream_3
                  lbu        t0, 260(s11) #end load_store_instr_stream_1
                  sb         a3, -16(s2) #end load_store_instr_stream_0
                  addi       a2, zero, -3 #init loop 1 counter
                  csrrc      t3, 0x340, s4
                  addi       zero, zero, 0 #init loop 1 limit
                  nop
sub_1_63_1_t:     sltu       a5, s0, a5
                  csrrwi     ra, 0x340, 24
                  add        a5, s3, s10
                  c.srai     a3, 11
                  slli       s3, tp, 8
                  .4byte 0x00100073 # ebreak
                  sll        a5, s9, t2
                  addi       a2, a2, 3 #update loop 1 counter
                  rem        s7, ra, s6
                  sub        t5, a3, s9
                  addi       a4, zero, -7 #init loop 0 counter
                  addi       t0, zero, -15 #init loop 0 limit
sub_1_63_0_t:     add        a7, s3, s9
                  andi       a3, s0, 248
                  c.addi     s10, -17
                  ori        s1, t4, 997
                  addi       a4, a4, -4 #update loop 0 counter
                  sra        s2, t3, a0
                  divu       tp, a7, s3
                  addi       s10, s5, -343
                  beq        a4, t0, sub_1_63_0_t #branch for loop 0
                  c.beqz     a2, sub_1_63_1_t #branch for loop 1
                  xor        t4, tp, a4
sub_1_19:         jal        gp, 9f
0:                c.jal      1f
1:                c.j        3f
2:                jal        tp, 4f
3:                jal        ra, 12f
4:                jal        ra, 10f
5:                c.jal      13f
6:                jal        ra, 8f
7:                jal        s10, 14f
8:                jal        t1, 16f
9:                jal        s6, 0b
10:               c.jal      7b
11:               c.j        5b
12:               c.j        2b
13:               jal        t3, 6b
14:               jal        gp, 15f
15:               c.jal      11b
16:               csrrsi     t0, 0x340, 26
                  la         t6, region_1+15071 #start riscv_load_store_rand_instr_stream_6
                  srl        zero, sp, s3
                  c.mv       s4, s8
                  lb         s1, -14(t6)
                  lb         a6, -12(t6)
                  c.or       a0, a5
                  lbu        t2, -8(t6)
                  csrrci     t3, 0x340, 17
                  sb         a2, 6(t6)
                  rem        zero, s3, tp
                  remu       zero, a3, s8
                  lui        s7, 491023
                  sw         t0, -15(t6)
                  csrrc      s4, 0x340, s11
                  csrrs      s3, 0x340, a2
                  c.nop
                  lb         s10, -10(t6)
                  lb         t5, 14(t6)
                  c.andi     s0, -30
                  lb         s7, 6(t6)
                  c.addi     a4, -31
                  lbu        a3, -10(t6)
                  sb         a3, -2(t6)
                  lb         s5, 5(t6)
                  lb         t5, -10(t6)
                  nop
                  c.nop
                  csrrwi     s5, 0x340, 4
                  and        t5, t4, a4
                  add        s10, t0, t2
                  lb         a1, 16(t6)
                  sltiu      s0, t6, 900
                  slti       a3, t2, -450
                  c.xor      a0, a5
                  slli       tp, t5, 21
                  mulh       s10, s11, t4
                  div        a4, a3, a2
                  c.mv       ra, t2
                  sh         ra, 3(t6)
                  sb         gp, -10(t6) #end riscv_load_store_rand_instr_stream_6
                  la         s5, region_2+6577 #start riscv_hazard_instr_stream_3
                  mulhsu     a7, gp, s4
                  sll        a3, a5, s2
                  lh         s4, -223(s5)
                  c.mv       a7, a7
                  lw         s4, 187(s5)
                  c.srli     a3, 31
                  sb         s2, -71(s5)
                  sh         a3, -49(s5)
                  addi       s2, s2, 1002
                  c.add      a3, a3
                  lbu        gp, 176(s5)
                  ori        a5, a7, 795
                  lw         a5, -125(s5)
                  ori        a7, a5, 361
                  or         gp, a5, s2
                  slti       a7, s2, -250
                  lbu        gp, 154(s5)
                  lbu        s4, 72(s5)
                  addi       s4, gp, -228
                  lbu        a7, 167(s5)
                  sub        gp, s2, gp
                  csrrw      gp, 0x340, s2
                  c.add      a3, a3
                  add        s2, a7, s2
                  csrrwi     a5, 0x340, 14
                  .4byte 0x00100073 # ebreak
                  lbu        s2, -26(s5)
                  sb         a5, -24(s5)
                  sh         a7, -79(s5)
                  c.li       a3, -11
                  lbu        a5, 192(s5)
                  sh         a7, 107(s5)
                  nop
                  mulhu      gp, s4, a7
                  sh         gp, 29(s5)
                  csrrc      s2, 0x340, s4
                  sw         s2, 227(s5)
                  c.addi     a5, 20
                  csrrc      a5, 0x340, gp
                  lbu        s2, -20(s5) #end riscv_hazard_instr_stream_3
                  la         s5, region_3+397 #start riscv_load_store_rand_instr_stream_7
                  sltiu      s0, s4, 422
                  c.add      s10, s6
                  lbu        s11, 57(s5)
                  srli       s2, s4, 18
                  nop
                  lbu        a5, -101(s5)
                  lh         s7, -43(s5)
                  lh         t3, -5(s5)
                  sb         t2, -318(s5)
                  lw         s0, -137(s5)
                  sra        s7, t0, s10
                  csrrs      s10, 0x340, a7
                  nop
                  sb         tp, -356(s5)
                  lhu        s4, 3(s5)
                  sb         s3, -163(s5)
                  sw         a1, -97(s5)
                  sw         ra, 59(s5)
                  lbu        t6, -290(s5)
                  sltiu      t4, t3, 212
                  lui        t3, 532802
                  and        t0, sp, s10
                  lhu        zero, -187(s5)
                  sh         tp, -207(s5)
                  sltiu      ra, gp, 181
                  lb         gp, -52(s5)
                  lbu        t0, -355(s5)
                  lh         s2, -381(s5)
                  sb         a2, -342(s5)
                  lb         gp, -6(s5)
                  div        a0, t2, s4
                  add        s4, a3, t2
                  lh         t3, -291(s5)
                  sb         s1, -372(s5)
                  lhu        s3, -283(s5)
                  sh         t2, 81(s5)
                  lbu        t6, -12(s5)
                  sh         s6, -331(s5)
                  lb         t3, -219(s5)
                  lb         a4, -240(s5) #end riscv_load_store_rand_instr_stream_7
                  addi       ra, zero, 7 #init loop 0 counter
                  c.ebreak;c.nop;
                  c.slli     a1, 25
                  addi       a7, zero, 2 #init loop 0 limit
sub_1_56_0_t:     mulhu      a2, a6, a3
                  sub        t6, a6, a7
                  c.srai     s0, 18
                  addi       ra, ra, -1 #update loop 0 counter
                  c.li       t2, 11
                  c.srli     s1, 6
                  bgeu       ra, a7, sub_1_56_0_t #branch for loop 0
                  ori        a0, t1, 325
                  la         s5, region_2+2314 #start riscv_load_store_rand_instr_stream_11
                  remu       t2, a6, s7
                  sb         a4, -59(s5)
                  lbu        a7, -16(s5)
                  lh         t0, -52(s5)
                  lui        a0, 1017564
                  srli       s4, s9, 21
                  sh         t6, -36(s5)
                  andi       gp, t6, 152
                  c.nop
                  slti       a6, a0, 384
                  mul        a6, t1, t1
                  csrrc      gp, 0x340, gp
                  srl        a5, s4, ra
                  xor        t1, t3, s4
                  auipc      s2, 1014333
                  sb         t3, 16(s5)
                  sb         a1, -39(s5)
                  lbu        s11, 12(s5)
                  or         a4, a7, sp
                  srl        a7, t2, s3
                  sb         t3, 49(s5)
                  lb         a7, 58(s5)
                  lb         a3, 15(s5)
                  lui        t4, 144595
                  srai       tp, s5, 25
                  lhu        s1, 38(s5)
                  lhu        s4, -34(s5)
                  lb         t1, 34(s5)
                  lhu        s11, 46(s5)
                  c.srai     s1, 1
                  lb         a0, -40(s5)
                  sh         t0, -32(s5)
                  sb         s0, 50(s5)
                  c.xor      a3, s0
                  c.nop
                  sb         sp, 52(s5)
                  c.slli     tp, 14
                  lhu        t5, 22(s5)
                  sb         s8, 5(s5) #end riscv_load_store_rand_instr_stream_11
                  la         t1, region_2+7749 #start load_store_instr_stream_1
                  la         a4, region_2+641 #start load_store_instr_stream_0
                  lb         s7, 6(a4)
                  lbu        a0, 13(a4)
                  lhu        t6, -15(a4)
                  lh         s11, -11(t1)
                  lb         s11, -56(t1)
                  lb         tp, 16(a4)
                  lh         s0, -13(a4)
                  sh         ra, -13(t1)
                  lbu        t5, 3(a4)
                  sh         tp, 55(t1)
                  lb         a0, 1(a4)
                  lhu        t0, 3(t1) #end load_store_instr_stream_1
                  lbu        a2, -12(a4)
                  sb         ra, 8(a4) #end load_store_instr_stream_0
                  la         s11, region_3+495 #start load_store_instr_stream_3
                  la         s3, region_3+395 #start load_store_instr_stream_1
                  la         a1, region_3+162 #start load_store_instr_stream_4
                  lbu        a0, -62(s11)
                  sb         t6, -11(a1)
                  sb         s10, -36(s11)
                  lb         s7, -54(s11)
                  la         t1, region_3+16 #start load_store_instr_stream_0
                  sb         s10, -52(s11)
                  la         t2, region_3+96 #start load_store_instr_stream_2
                  sb         t3, -7(a1)
                  lb         gp, -24(t2)
                  sh         a2, 113(s3)
                  lb         gp, 71(t1)
                  lw         a3, -63(s11)
                  lb         a7, -255(s3)
                  lb         a6, -316(s3)
                  lbu        a5, 12(t2)
                  lhu        tp, 148(t1)
                  sb         s4, -18(s11)
                  sh         a7, 6(a1)
                  sb         s0, -105(s3)
                  sb         s3, -11(a1)
                  lb         t3, 13(a1)
                  lh         s10, -15(s3)
                  sh         s8, -46(t2)
                  lb         a6, 127(t1)
                  lbu        s6, 31(t2)
                  sb         ra, 102(s3)
                  lbu        a6, -19(t2) #end load_store_instr_stream_2
                  sh         t0, -53(s3) #end load_store_instr_stream_1
                  lbu        a2, 13(a1)
                  lw         zero, 2(a1)
                  lb         a3, -58(s11) #end load_store_instr_stream_3
                  sw         s6, 14(a1) #end load_store_instr_stream_4
                  sb         a4, -13(t1)
                  lhu        t4, 128(t1) #end load_store_instr_stream_0
sub_1_21:         jal        gp, 13f
0:                c.jal      5f
1:                jal        ra, 24f
2:                jal        ra, 12f
3:                c.j        17f
4:                jal        ra, 1b
5:                jal        t1, 3b
6:                jal        t1, 19f
7:                c.j        4b
8:                c.jal      15f
9:                c.j        10f
10:               c.jal      0b
11:               jal        ra, 16f
12:               c.jal      26f
13:               jal        t1, 21f
14:               jal        ra, 2b
15:               c.j        9b
16:               c.jal      14b
17:               jal        t6, 18f
18:               jal        ra, 6b
19:               c.j        25f
20:               c.j        22f
21:               jal        ra, 20b
22:               c.jal      23f
23:               jal        a2, 7b
24:               c.jal      8b
25:               c.jal      11b
26:               mulhu      a6, ra, sp
sub_1_20:         jal        gp, 16f
0:                jal        ra, 6f
1:                jal        ra, 17f
2:                c.j        14f
3:                c.jal      11f
4:                c.jal      21f
5:                jal        t3, 8f
6:                c.j        1b
7:                jal        ra, 10f
8:                jal        a1, 3b
9:                c.j        23f
10:               c.jal      9b
11:               c.j        22f
12:               c.j        13f
13:               c.j        18f
14:               c.jal      4b
15:               c.jal      5b
16:               jal        t6, 19f
17:               c.jal      28f
18:               jal        ra, 24f
19:               c.jal      26f
20:               jal        ra, 7b
21:               c.j        12b
22:               c.j        25f
23:               jal        t1, 0b
24:               jal        a2, 27f
25:               c.j        2b
26:               jal        t1, 15b
27:               c.j        20b
28:               andi       t0, s3, 825
                  addi       a2, zero, 6 #init loop 1 counter
                  addi       zero, zero, 0 #init loop 1 limit
                  sltiu      s4, s2, -272
                  andi       s2, t3, -781
sub_1_58_1_t:     c.slli     t6, 9
                  ori        t5, t1, 994
                  addi       a2, a2, -3 #update loop 1 counter
                  c.slli     s3, 7
                  add        a1, t3, t5
                  addi       a0, zero, 5 #init loop 0 counter
                  srli       s11, t4, 26
                  addi       t0, zero, 15 #init loop 0 limit
sub_1_58_0_t:     divu       s11, s6, s4
                  c.or       s1, a1
                  addi       a0, a0, 1 #update loop 0 counter
                  bltu       a0, t0, sub_1_58_0_t #branch for loop 0
                  remu       s2, s11, s5
                  sltiu      s5, s1, 368
                  c.bnez     a2, sub_1_58_1_t #branch for loop 1
                  mulhsu     t5, a4, zero
sub_1_18:         jal        gp, 13f
0:                c.j        2f
1:                c.j        14f
2:                jal        t1, 5f
3:                c.j        17f
4:                c.j        11f
5:                jal        ra, 10f
6:                jal        t1, 9f
7:                c.jal      15f
8:                jal        t1, 12f
9:                jal        ra, 16f
10:               jal        t0, 7b
11:               c.j        1b
12:               c.j        3b
13:               c.jal      0b
14:               c.jal      6b
15:               c.jal      4b
16:               jal        s6, 8b
17:               srai       s3, s2, 11
                  la         s6, region_4+390 #start load_store_instr_stream_1
                  sb         t1, 821(s6)
                  la         a6, region_1+11209 #start load_store_instr_stream_2
                  la         s5, region_0+1111 #start load_store_instr_stream_3
                  lb         t1, -24(a6)
                  lh         s7, 972(s6)
                  sb         t0, -22(s5)
                  sb         tp, 242(s5)
                  lbu        t4, -178(s5)
                  la         a1, region_2+5854 #start load_store_instr_stream_0
                  sh         s11, 141(s5)
                  lbu        t3, -24(a6)
                  lb         t0, 303(s6)
                  lbu        s1, 847(a1)
                  sh         s4, -538(s6)
                  lb         ra, 89(s5)
                  sb         ra, 56(a6)
                  lb         t0, -241(s5)
                  lhu        a3, -926(a1)
                  sb         s9, -118(a1)
                  lh         a7, 930(s6)
                  sb         s6, 63(s5)
                  sh         t2, -58(a1)
                  sb         a4, -224(s6) #end load_store_instr_stream_1
                  sb         zero, -211(a1)
                  lh         s10, -1(a6)
                  lb         s0, -203(s5)
                  sb         ra, 343(a1)
                  lbu        s0, 18(s5)
                  sh         sp, -21(a6) #end load_store_instr_stream_2
                  sw         s7, 69(s5) #end load_store_instr_stream_3
                  lh         s3, -10(a1) #end load_store_instr_stream_0
                  la         t4, region_2+1405 #start riscv_hazard_instr_stream_2
                  sb         a2, 2(t4)
                  srli       s6, ra, 13
                  sb         t2, -15(t4)
                  addi       t2, a2, 664
                  csrrs      a3, 0x340, a2
                  mul        gp, gp, gp
                  sb         ra, 13(t4)
                  sb         t2, 10(t4)
                  mulhsu     s6, t2, ra
                  sb         gp, -4(t4)
                  ori        a3, ra, -289
                  srli       s6, gp, 31
                  c.or       a3, a2
                  c.sub      a3, a3
                  mulh       ra, ra, gp
                  lbu        s6, 16(t4)
                  sh         a3, -7(t4)
                  lbu        ra, 0(t4)
                  lbu        t2, 5(t4)
                  lh         ra, -3(t4)
                  lb         t2, 0(t4)
                  sh         a3, -11(t4)
                  addi       a3, t2, -728
                  sb         s6, 6(t4)
                  mulh       t2, ra, a2
                  c.srli     a2, 16
                  sltiu      t2, a3, 725
                  c.srli     a2, 12
                  lbu        gp, -14(t4)
                  c.nop
                  xori       gp, gp, -539
                  lbu        ra, 15(t4)
                  slti       t2, a3, -210
                  sb         a2, -12(t4)
                  lui        t2, 1010440
                  c.lui      s6, 8
                  sb         t2, 14(t4) #end riscv_hazard_instr_stream_2
sub_1_27:         jal        gp, 9f
0:                jal        t1, 6f
1:                jal        t1, 7f
2:                c.j        4f
3:                c.jal      2b
4:                jal        ra, 13f
5:                c.j        12f
6:                c.jal      10f
7:                c.jal      3b
8:                jal        t1, 1b
9:                c.jal      8b
10:               jal        t5, 5b
11:               jal        s3, 0b
12:               c.jal      14f
13:               c.j        11b
14:               mulh       s11, a0, s10
                  la         s7, region_2+4022 #start riscv_hazard_instr_stream_0
                  c.srli     a0, 22
                  rem        a4, tp, a4
                  mulh       a4, s10, t5
                  lui        a0, 403989
                  mulh       a0, t5, a6
                  mulhsu     s10, a4, t5
                  sh         tp, 12(s7)
                  auipc      tp, 6010
                  c.or       a4, a0
                  c.li       s10, -31
                  srai       t5, a0, 29
                  divu       a0, tp, s10
                  sb         t5, -4(s7)
                  csrrs      a4, 0x340, tp
                  rem        a6, tp, a0
                  sb         s10, -3(s7)
                  lbu        t5, -11(s7)
                  lui        a0, 550487
                  slli       s10, a6, 14
                  lbu        a0, -3(s7)
                  sltiu      tp, a0, -900
                  lbu        a6, 14(s7)
                  c.ebreak;c.nop;
                  slt        t5, a6, t5
                  srl        a4, a4, tp
                  csrrsi     t5, 0x340, 28
                  divu       a6, a0, s10
                  mulhu      a0, a4, t5
                  add        a4, t5, a0
                  lbu        a0, 11(s7)
                  sb         a6, 3(s7)
                  c.slli     tp, 10
                  sltu       a0, a6, t5
                  sb         s10, 4(s7)
                  sb         t5, 13(s7)
                  c.nop
                  mul        a4, t5, s10
                  slti       a4, a0, 836
                  sltu       tp, s10, tp
                  .4byte 0x00100073 # ebreak
                  sh         s10, 6(s7) #end riscv_hazard_instr_stream_0
                  la         a3, region_2+5062 #start load_store_instr_stream_1
                  la         a0, region_4+2126 #start load_store_instr_stream_0
                  lhu        s6, -100(a3)
                  la         s10, region_0+3396 #start load_store_instr_stream_2
                  sh         s10, 488(a0)
                  lb         gp, 11(s10)
                  lh         a5, -180(a3)
                  lh         a1, -288(a0)
                  lb         s2, -6(s10)
                  sb         s1, -690(a0)
                  lb         a4, 15(s10)
                  lbu        zero, 155(a3)
                  sb         a0, -203(a0)
                  lbu        a7, -5(s10)
                  lw         a7, 8(s10)
                  lhu        s11, 380(a0)
                  lbu        s1, -4(a3)
                  lbu        s5, 190(a3)
                  lbu        t1, -577(a0)
                  sb         t2, -13(s10) #end load_store_instr_stream_2
                  lh         s1, 104(a3)
                  lbu        tp, -231(a3)
                  lbu        a7, 699(a0)
                  sh         s8, 60(a3)
                  lbu        zero, 296(a0)
                  lb         s0, 92(a3) #end load_store_instr_stream_1
                  lbu        s1, -775(a0) #end load_store_instr_stream_0
                  addi       a6, zero, 8 #init loop 0 counter
                  div        s7, s0, t2
                  c.lui      gp, 26
                  addi       t0, zero, -12 #init loop 0 limit
                  c.ebreak;c.nop;
                  csrrc      s11, 0x340, s10
sub_1_57_0_t:     auipc      tp, 914809
                  addi       a6, a6, -10 #update loop 0 counter
                  c.addi     a0, -24
                  beq        a6, t0, sub_1_57_0_t #branch for loop 0
                  sll        s0, s0, a2
                  la         s0, region_3+266 #start riscv_load_store_rand_instr_stream_4
                  sb         s6, 125(s0)
                  sb         t1, -171(s0)
                  lui        s3, 83688
                  c.mv       t5, a6
                  lh         s11, -16(s0)
                  sra        ra, t6, s10
                  sh         ra, -136(s0)
                  lbu        a0, 29(s0)
                  lb         t0, -132(s0)
                  rem        ra, a1, t1
                  c.or       a1, a2
                  sh         t4, -100(s0)
                  lh         a6, -80(s0)
                  sub        gp, tp, a1
                  c.and      a0, a4
                  lb         a2, -246(s0)
                  c.mv       ra, t4
                  sltu       t0, a7, s3
                  lbu        t0, -212(s0)
                  lb         ra, -205(s0)
                  lbu        ra, 127(s0)
                  lb         zero, 222(s0)
                  sb         t3, -213(s0)
                  sra        a5, t3, t3
                  sb         a6, -169(s0)
                  c.ebreak;c.nop;
                  lbu        t1, 62(s0)
                  sh         sp, 126(s0)
                  sra        t2, zero, ra
                  sb         s11, -154(s0)
                  c.and      a0, a2
                  sb         t5, 34(s0)
                  lbu        s7, -96(s0)
                  sltiu      a2, t4, -159
                  .4byte 0x00100073 # ebreak
                  csrrw      a0, 0x340, t3
                  c.srli     a2, 18
                  sltiu      t6, a2, -478
                  auipc      s4, 941036
                  sb         t0, 229(s0)
                  c.sub      a1, s0
                  sh         s7, 60(s0)
                  or         s10, sp, sp
                  c.and      a3, a0
                  lui        s4, 880231
                  lbu        ra, 91(s0) #end riscv_load_store_rand_instr_stream_4
                  la         s5, region_3+499 #start load_store_instr_stream_0
                  sb         gp, -43(s5)
                  la         a5, region_3+373 #start load_store_instr_stream_1
                  sb         s0, 10(s5)
                  lb         s7, -16(a5)
                  lbu        ra, -14(a5)
                  lh         s0, -51(s5)
                  lbu        t1, -40(a5)
                  sb         t1, 8(s5)
                  lbu        gp, 0(s5)
                  sw         zero, 3(a5)
                  sb         s6, -32(s5)
                  lbu        s2, 16(a5)
                  lbu        t6, -30(s5)
                  lb         s10, -54(s5)
                  sb         sp, 32(a5)
                  sh         a2, -29(s5)
                  sb         a3, -45(a5)
                  lbu        a2, -41(a5) #end load_store_instr_stream_1
                  lbu        s4, -33(s5) #end load_store_instr_stream_0
                  la         t6, region_4+3031 #start riscv_load_store_rand_instr_stream_1
                  c.ebreak;c.nop;
                  srai       s5, s8, 18
                  c.add      t0, t4
                  remu       s1, t5, s4
                  lbu        a1, 14(t6)
                  sltu       gp, a4, a2
                  csrrsi     t0, 0x340, 20
                  c.srai     a0, 1
                  csrrw      s6, 0x340, t1
                  sltiu      s11, s2, 207
                  sltu       s4, s9, s3
                  sb         t6, 4(t6)
                  remu       s2, s10, s0
                  lb         a1, 0(t6)
                  lbu        s0, 3(t6)
                  c.li       a7, 18
                  c.add      t5, t6
                  lbu        s0, 9(t6)
                  xori       s0, zero, -496
                  c.and      a2, a2
                  sltu       s10, t1, gp
                  csrrci     s4, 0x340, 15
                  lbu        a6, -10(t6)
                  lhu        a5, -5(t6)
                  c.or       s1, a5
                  srli       t4, t1, 13
                  sb         s2, -15(t6)
                  sh         t6, 5(t6)
                  divu       a0, t2, s5
                  sb         a4, 6(t6)
                  ori        a0, t4, 539
                  sb         gp, -10(t6)
                  c.mv       a1, t1
                  lb         s2, 0(t6)
                  sb         s6, -10(t6) #end riscv_load_store_rand_instr_stream_1
                  addi       s5, zero, 3 #init loop 0 counter
                  addi       tp, zero, -14 #init loop 0 limit
                  xor        a2, t3, s0
                  c.andi     a0, -17
                  and        t0, t5, a7
                  mulhu      a5, t0, s7
sub_1_60_0_t:     divu       s1, a4, a6
                  csrrsi     s1, 0x340, 7
                  csrrc      a1, 0x340, a1
                  ori        s11, ra, -91
                  lui        t4, 929648
                  addi       s5, s5, -1 #update loop 0 counter
                  c.srai     a0, 21
                  c.addi     a4, -20
                  c.srai     a1, 4
                  bne        s5, tp, sub_1_60_0_t #branch for loop 0
                  mulhsu     t0, zero, a1
                  la         s11, region_4+1594 #start riscv_hazard_instr_stream_13
                  lb         t4, -11(s11)
                  sb         t4, 8(s11)
                  sll        a4, t4, a2
                  lbu        a4, 4(s11)
                  lb         a4, 8(s11)
                  lb         s4, 11(s11)
                  csrrci     a2, 0x340, 28
                  c.slli     a6, 20
                  lb         a4, -8(s11)
                  lbu        a4, -7(s11)
                  andi       a6, a4, -633
                  lbu        t4, 10(s11)
                  lbu        s4, 15(s11)
                  c.srli     s1, 14
                  c.sub      a4, a2
                  c.slli     s1, 4
                  slt        t4, a4, t4
                  srai       a2, a4, 9
                  lbu        a4, 16(s11)
                  lbu        a4, 4(s11)
                  csrrc      a4, 0x340, s4
                  lbu        s1, 12(s11)
                  sb         a2, -9(s11)
                  lb         t4, 3(s11)
                  c.xor      a2, a2
                  add        t4, s4, a4
                  lbu        s1, 4(s11)
                  xor        t4, t4, t4
                  sb         a4, -15(s11)
                  xori       a6, s4, 192
                  lb         a4, 7(s11)
                  csrrci     a2, 0x340, 29
                  sb         s1, -11(s11)
                  c.sub      a2, a2
                  srl        t4, s1, s1
                  sb         a2, 16(s11)
                  sh         a6, -4(s11)
                  sub        s1, a4, s4
                  mulhsu     a6, a2, s4
                  lbu        a2, 2(s11)
                  lbu        a6, -4(s11)
                  mul        t4, a6, s4
                  sra        a4, s1, a6
                  lb         a4, 1(s11)
                  lbu        a6, 5(s11)
                  c.srai     a4, 3
                  csrrci     a4, 0x340, 24
                  div        t4, a6, a4
                  lbu        a2, -9(s11)
                  lb         a6, -15(s11)
                  lb         t4, -1(s11)
                  lbu        a6, -9(s11) #end riscv_hazard_instr_stream_13
                  la         t4, region_2+2029 #start riscv_load_store_rand_instr_stream_5
                  c.and      s0, s1
                  c.or       a1, a4
                  c.li       t0, 9
                  .4byte 0x00100073 # ebreak
                  lbu        s5, 14(t4)
                  sb         s11, -8(t4)
                  sll        tp, a5, s3
                  lb         t5, -6(t4)
                  sh         t2, -15(t4)
                  csrrci     s0, 0x340, 13
                  c.mv       a1, s10
                  mulh       zero, gp, t2
                  sltu       a1, ra, a6
                  lbu        t2, -14(t4)
                  lb         s2, 15(t4)
                  c.and      s0, a1
                  addi       t0, a6, -704
                  sb         a2, -12(t4)
                  lbu        t3, -15(t4)
                  lb         a0, -7(t4)
                  sb         a0, 10(t4)
                  c.srai     a4, 8
                  xor        tp, s5, t1
                  div        zero, a5, s2
                  sra        t5, a1, s8
                  .4byte 0x00100073 # ebreak
                  lb         tp, 6(t4)
                  nop
                  lw         t1, 11(t4) #end riscv_load_store_rand_instr_stream_5
                  la         s2, region_4+1009 #start riscv_load_store_rand_instr_stream_13
                  lh         a6, -35(s2)
                  sh         a3, -169(s2)
                  slt        tp, a4, a1
                  lbu        t5, -114(s2)
                  c.ebreak;c.nop;
                  c.and      a4, a4
                  c.andi     s1, -23
                  sb         s3, -79(s2)
                  lbu        a4, 67(s2)
                  csrrci     tp, 0x340, 30
                  c.srai     s1, 18
                  nop
                  div        a5, s10, t1
                  lb         a6, 68(s2)
                  sb         sp, -236(s2)
                  andi       a1, t1, -14
                  c.and      s0, a2
                  c.and      s0, a1
                  c.mv       s11, a2
                  slt        ra, s8, s7
                  lui        t5, 204334
                  auipc      a6, 679306
                  sw         tp, 83(s2)
                  lhu        a3, 225(s2)
                  slt        t2, t5, t1
                  lbu        s6, 64(s2)
                  lb         a7, -156(s2)
                  sh         s3, -23(s2) #end riscv_load_store_rand_instr_stream_13
                  la         gp, region_3+229 #start riscv_hazard_instr_stream_12
                  sltiu      a1, zero, -52
                  mulhu      zero, zero, a1
                  lbu        a4, 9(gp)
                  sb         a1, -10(gp)
                  sltiu      a1, a4, -193
                  sb         s6, 2(gp)
                  mulhu      a4, zero, zero
                  lhu        t3, 13(gp)
                  mulh       a1, t0, s6
                  lbu        zero, 16(gp)
                  c.srai     a4, 30
                  slti       zero, s6, -646
                  lb         s6, 16(gp)
                  lb         a1, -6(gp)
                  lb         a1, 7(gp)
                  mulhsu     t3, zero, t3
                  rem        zero, t0, t0
                  sh         a1, 1(gp)
                  slti       a4, a4, -977
                  sh         t0, -1(gp)
                  lh         zero, 13(gp)
                  lbu        t3, -2(gp)
                  csrrs      zero, 0x340, zero
                  .4byte 0x00100073 # ebreak
                  sll        a4, zero, t3
                  sb         t0, -14(gp)
                  csrrs      a4, 0x340, s6
                  lh         a4, 9(gp)
                  csrrci     t3, 0x340, 11
                  sb         t3, 16(gp)
                  c.or       a4, a1
                  sll        t0, t0, t3
                  lbu        t0, -10(gp) #end riscv_hazard_instr_stream_12
                  la         s0, region_2+4373 #start load_store_instr_stream_1
                  la         a7, region_1+8046 #start load_store_instr_stream_0
                  lbu        s3, 4(s0)
                  sb         s7, -14(s0)
                  lb         a2, -14(s0)
                  sb         s3, 807(a7)
                  sb         t0, -14(s0)
                  lbu        t0, -491(a7)
                  sh         t1, -11(s0)
                  sb         s9, 1003(a7)
                  lb         s7, 14(s0)
                  lb         t3, 169(a7)
                  lb         t4, -13(s0) #end load_store_instr_stream_1
                  lhu        t6, 748(a7)
                  sb         t1, -759(a7)
                  sw         s10, -362(a7) #end load_store_instr_stream_0
sub_1_25:         jal        gp, 3f
0:                jal        t1, 7f
1:                c.jal      4f
2:                jal        ra, 9f
3:                jal        t1, 12f
4:                jal        a7, 11f
5:                jal        ra, 0b
6:                jal        t1, 1b
7:                jal        tp, 13f
8:                jal        ra, 10f
9:                jal        ra, 5b
10:               c.jal      2b
11:               c.jal      14f
12:               jal        a2, 8b
13:               c.jal      6b
14:               sll        a3, s8, s7
sub_1_26:         jal        gp, 13f
0:                c.jal      25f
1:                c.j        0b
2:                jal        t3, 12f
3:                c.j        7f
4:                jal        tp, 16f
5:                c.j        26f
6:                jal        ra, 2b
7:                c.j        28f
8:                jal        ra, 18f
9:                c.j        24f
10:               jal        t0, 23f
11:               jal        a0, 5b
12:               c.j        20f
13:               jal        ra, 15f
14:               c.jal      1b
15:               c.jal      10b
16:               c.jal      11b
17:               c.jal      29f
18:               c.j        6b
19:               c.jal      4b
20:               jal        tp, 22f
21:               c.jal      14b
22:               jal        ra, 3b
23:               jal        ra, 17b
24:               c.j        19b
25:               jal        gp, 9b
26:               jal        t1, 8b
27:               c.jal      30f
28:               jal        ra, 27b
29:               jal        t1, 21b
30:               c.li       tp, 19
                  la         s1, region_0+1432 #start load_store_instr_stream_3
                  la         a2, region_0+75 #start load_store_instr_stream_1
                  sb         s4, -18(a2)
                  la         t3, region_0+4064 #start load_store_instr_stream_4
                  sb         zero, 32(a2)
                  la         s2, region_0+2944 #start load_store_instr_stream_0
                  la         t0, region_0+3745 #start load_store_instr_stream_2
                  lbu        a3, -43(t3)
                  lb         ra, 13(t0)
                  lhu        s4, -29(a2)
                  lbu        t2, -25(a2)
                  lb         s7, -981(s1)
                  lh         s6, 19(a2)
                  sh         tp, -58(t3)
                  lbu        t1, -44(a2)
                  sb         sp, -27(t3)
                  lh         s5, -50(t3)
                  lb         zero, 13(t0)
                  sw         s1, -5(t0)
                  lw         s7, 372(s1)
                  lbu        a3, 769(s2)
                  lbu        ra, -31(t3)
                  lb         t6, -37(a2)
                  lb         s6, -49(t3)
                  lb         s3, -12(t0)
                  sw         t4, -35(a2) #end load_store_instr_stream_1
                  sh         s1, -826(s1)
                  lh         s3, -1(t0)
                  lb         a3, -53(t3) #end load_store_instr_stream_4
                  lb         s5, -815(s2)
                  lbu        s6, -12(t0)
                  sw         t2, -604(s2)
                  sb         t2, -227(s1)
                  lb         s0, -848(s2)
                  lhu        zero, 9(t0) #end load_store_instr_stream_2
                  lbu        s6, 71(s1) #end load_store_instr_stream_3
                  sb         gp, 115(s2)
                  lb         ra, 25(s2) #end load_store_instr_stream_0
sub_1_15:         jal        gp, 1f
0:                jal        ra, 3f
1:                c.jal      7f
2:                c.j        12f
3:                c.j        5f
4:                jal        ra, 2b
5:                c.j        8f
6:                jal        ra, 9f
7:                jal        t1, 0b
8:                c.j        11f
9:                jal        t0, 4b
10:               c.jal      6b
11:               jal        ra, 10b
12:               rem        gp, tp, s11
                  la         s0, region_2+7136 #start load_store_instr_stream_1
                  la         t2, region_2+820 #start load_store_instr_stream_2
                  la         t3, region_2+2452 #start load_store_instr_stream_3
                  la         s10, region_2+4840 #start load_store_instr_stream_0
                  lbu        t1, 13(s10)
                  sb         t1, 229(t2)
                  lbu        s1, -6(t3)
                  sb         a2, -7(s0)
                  sb         a2, 3(s0)
                  lbu        s6, 59(t2)
                  sb         s2, -13(s10)
                  sb         s0, 219(t2)
                  lb         s3, 10(t3)
                  lb         s1, 19(s0)
                  sb         s3, 45(t2)
                  sb         ra, -9(t3)
                  lb         s2, -63(s0)
                  lb         t4, 2(s10)
                  sb         t5, 7(s10)
                  sb         a4, 196(t2)
                  sw         s6, 120(t2)
                  lbu        t4, 7(s10)
                  sb         t4, -13(t3)
                  lb         a4, -3(t3)
                  lbu        t6, 7(s10)
                  lbu        gp, -30(s0) #end load_store_instr_stream_1
                  lbu        s11, 13(t3)
                  lbu        tp, 7(t3) #end load_store_instr_stream_3
                  lb         gp, -15(t2) #end load_store_instr_stream_2
                  sb         a1, -16(s10) #end load_store_instr_stream_0
                  la         a2, region_3+385 #start riscv_load_store_rand_instr_stream_9
                  lhu        s2, -235(a2)
                  sb         s2, 97(a2)
                  lb         tp, 12(a2)
                  lbu        s0, -178(a2)
                  add        a4, s10, a0
                  c.li       s7, -17
                  sw         s10, -17(a2)
                  lh         t0, -1(a2)
                  lb         a0, -128(a2)
                  lbu        s10, -238(a2)
                  csrrsi     t6, 0x340, 3
                  srai       t6, t6, 14
                  auipc      a4, 319034
                  sb         a1, -37(a2)
                  and        t3, t4, a7
                  lh         t3, -55(a2)
                  csrrsi     a3, 0x340, 17
                  lb         t6, -104(a2)
                  mulhu      s3, ra, a5
                  c.add      s2, s11
                  lb         tp, 57(a2)
                  c.nop
                  andi       t3, s4, -962
                  rem        a7, a2, a2
                  or         s6, a1, ra
                  lb         a6, 30(a2)
                  sb         s10, -107(a2)
                  add        s0, t4, s5
                  mulhu      s4, s3, s6
                  lb         zero, -164(a2)
                  sb         zero, -105(a2)
                  sh         s2, -39(a2)
                  lb         tp, 58(a2)
                  sll        s7, a0, t0
                  sb         t4, -213(a2)
                  lh         t4, -63(a2)
                  c.sub      a4, a1
                  lh         t1, -125(a2)
                  c.lui      a6, 17
                  lb         a0, -116(a2)
                  lw         s7, -97(a2) #end riscv_load_store_rand_instr_stream_9
                  la         a4, region_0+1688 #start riscv_hazard_instr_stream_8
                  lhu        t5, 10(a4)
                  c.and      a3, a3
                  lbu        t1, 1(a4)
                  mulhsu     t1, a5, t1
                  mul        a3, t5, a5
                  lw         s1, 16(a4)
                  lw         a5, 12(a4)
                  auipc      a1, 159560
                  csrrs      a1, 0x340, a1
                  c.add      t5, a1
                  lbu        t1, 16(a4)
                  c.andi     a3, -32
                  sw         t5, 16(a4)
                  .4byte 0x00100073 # ebreak
                  c.xor      s1, a5
                  ori        a3, t5, 431
                  sh         a5, 16(a4)
                  sw         a3, 8(a4)
                  lhu        a5, -4(a4)
                  lbu        s1, 14(a4) #end riscv_hazard_instr_stream_8
                  la         a4, region_0+1030 #start riscv_load_store_rand_instr_stream_12
                  sb         s10, 183(a4)
                  csrrci     tp, 0x340, 23
                  c.nop
                  sb         a5, -56(a4)
                  c.or       a2, a5
                  lbu        a2, 919(a4)
                  lhu        s0, 140(a4)
                  sb         t2, 727(a4)
                  sb         s2, -147(a4)
                  c.sub      s0, s1
                  or         a2, s10, s2
                  lbu        s10, -565(a4)
                  sb         s3, -485(a4)
                  xori       t4, a6, -72
                  csrrwi     gp, 0x340, 27
                  lh         s7, 608(a4)
                  lh         t4, -284(a4)
                  add        a7, gp, s11
                  srli       s7, s2, 16
                  c.mv       t5, a0
                  c.srai     a5, 10
                  nop
                  lh         zero, -990(a4)
                  sb         t2, 945(a4)
                  sh         a0, -214(a4)
                  sb         s11, 596(a4)
                  csrrsi     zero, 0x340, 7
                  c.slli     t1, 29
                  srai       s11, s3, 21
                  sh         zero, 526(a4)
                  sltu       zero, tp, a6
                  lb         s7, -466(a4)
                  sb         s8, -663(a4)
                  lb         s3, -337(a4)
                  mulh       t6, a2, a1
                  sll        s6, tp, t2
                  sll        s4, s8, s11
                  c.and      a0, s0
                  mulh       ra, gp, sp
                  csrrc      t6, 0x340, s0
                  c.xor      a0, a5
                  lb         gp, -40(a4)
                  lb         a6, -973(a4)
                  lw         s11, -138(a4)
                  lb         ra, -494(a4)
                  csrrwi     a2, 0x340, 22
                  lw         t0, 562(a4)
                  srli       s6, a6, 9
                  lw         t2, -570(a4) #end riscv_load_store_rand_instr_stream_12
                  addi       a5, zero, 9 #init loop 0 counter
                  c.and      a3, a0
                  slli       t1, a2, 0
                  srai       t3, s8, 12
                  csrrci     s4, 0x340, 24
                  mulhu      t5, s5, s6
                  addi       zero, zero, 0 #init loop 0 limit
                  mulh       t0, s8, s1
                  add        t6, t2, a3
                  c.srai     s1, 30
sub_1_59_0_t:     divu       a3, gp, s11
                  mul        s5, s8, t4
                  c.nop
                  sltu       a3, s10, t5
                  c.srai     a2, 19
                  c.xor      s0, a3
                  mulhsu     t1, gp, a1
                  mulhu      t0, a5, zero
                  andi       t4, s11, -446
                  remu       s4, a6, a2
                  addi       a5, a5, -3 #update loop 0 counter
                  c.beqz     a5, sub_1_59_0_t #branch for loop 0
                  csrrw      s7, 0x340, a3
                  la         s3, region_2+3133 #start riscv_hazard_instr_stream_7
                  mulh       t2, s6, a7
                  lb         a7, 684(s3)
                  csrrsi     s6, 0x340, 19
                  sb         s6, -327(s3)
                  lbu        s1, 562(s3)
                  andi       s1, a7, 871
                  c.srli     s1, 15
                  lh         s1, -523(s3)
                  sub        s6, t2, s1
                  lb         s6, -411(s3)
                  lui        t2, 197641
                  srl        a0, s6, a0
                  xor        a0, s1, t6
                  slli       a0, s1, 23
                  csrrw      t6, 0x340, t2
                  lbu        a0, -481(s3)
                  csrrsi     t2, 0x340, 31
                  sb         s6, 763(s3)
                  sb         t2, 948(s3)
                  sltu       s1, s6, t2
                  slti       a7, a7, -269
                  sh         a0, 213(s3)
                  sh         s1, 369(s3)
                  lui        a7, 536346
                  lbu        a0, 392(s3)
                  lh         t6, -887(s3) #end riscv_hazard_instr_stream_7
sub_1_24:         jal        gp, 9f
0:                c.j        12f
1:                jal        gp, 5f
2:                jal        ra, 19f
3:                jal        ra, 17f
4:                jal        s10, 2b
5:                c.j        16f
6:                c.j        11f
7:                c.j        21f
8:                jal        ra, 14f
9:                jal        a0, 1b
10:               jal        ra, 3b
11:               c.jal      10b
12:               jal        ra, 7b
13:               jal        t3, 20f
14:               jal        ra, 4b
15:               jal        s2, 6b
16:               c.j        15b
17:               c.j        0b
18:               jal        ra, 22f
19:               c.jal      18b
20:               jal        ra, 8b
21:               jal        t1, 13b
22:               sub        a2, a2, a0
                  la         a6, region_2+6974 #start riscv_load_store_rand_instr_stream_3
                  sb         t1, 435(a6)
                  and        t2, t3, s8
                  nop
                  mulh       a0, t0, s0
                  lb         s5, 755(a6)
                  c.and      a2, a3
                  c.and      a3, a0
                  sb         gp, -658(a6)
                  .4byte 0x00100073 # ebreak
                  lh         t5, 886(a6)
                  divu       s4, s7, t2
                  nop
                  lbu        tp, 505(a6)
                  sb         s3, 274(a6)
                  mul        s10, s5, s10
                  sw         s6, 154(a6)
                  c.andi     a1, 19
                  csrrsi     t6, 0x340, 6
                  csrrsi     t2, 0x340, 6
                  add        t6, sp, a3
                  slt        s1, s1, a1
                  andi       gp, a1, -222
                  csrrc      a4, 0x340, s9
                  sb         a0, 779(a6)
                  lh         zero, 844(a6)
                  lb         s10, 475(a6)
                  csrrw      s4, 0x340, t3
                  csrrc      a5, 0x340, zero
                  sb         a1, -933(a6)
                  lb         ra, -851(a6) #end riscv_load_store_rand_instr_stream_3
                  la         s10, region_1+9455 #start load_store_instr_stream_2
                  la         t1, region_1+13526 #start load_store_instr_stream_3
                  la         a1, region_1+15929 #start load_store_instr_stream_0
                  sb         s9, 171(t1)
                  la         s4, region_1+997 #start load_store_instr_stream_1
                  lbu        t6, -214(s4)
                  lb         t4, -10(a1)
                  lb         a5, -114(s4)
                  lw         t3, -101(s4)
                  lbu        t4, 6(a1)
                  sb         a2, 234(s4)
                  lb         s7, -169(s10)
                  lh         t2, 185(s10)
                  lh         t4, -3(a1)
                  sh         s9, -175(s4)
                  sb         gp, 35(t1)
                  lbu        s7, 158(s4)
                  lbu        s0, -14(a1)
                  lbu        s11, -221(t1)
                  sb         a6, -175(s4)
                  lbu        s5, 122(s10)
                  sb         a3, -242(t1)
                  lbu        s11, -246(s10)
                  lbu        s3, -138(s4) #end load_store_instr_stream_1
                  lb         t4, 55(t1) #end load_store_instr_stream_3
                  lb         s7, 82(s10) #end load_store_instr_stream_2
                  lb         a2, 13(a1) #end load_store_instr_stream_0
                  la         a3, region_4+391 #start riscv_hazard_instr_stream_1
                  remu       s7, s1, s0
                  lb         a1, 12(a3)
                  csrrw      tp, 0x340, s0
                  c.xor      s1, a1
                  c.lui      tp, 24
                  lb         tp, -6(a3)
                  lb         s7, 14(a3)
                  c.add      s0, s7
                  sh         s7, -13(a3)
                  lb         a1, 2(a3)
                  div        tp, s7, s0
                  addi       tp, s1, 425
                  lb         a1, 11(a3)
                  lbu        s7, -14(a3)
                  mul        s1, s1, s1
                  lb         s7, -2(a3)
                  lb         s0, -8(a3)
                  c.addi     s0, -32
                  sb         a1, -6(a3)
                  lb         s1, 15(a3)
                  lb         s0, 2(a3)
                  c.srli     s0, 16
                  csrrwi     tp, 0x340, 4
                  lh         s7, 3(a3)
                  sub        s1, gp, gp
                  slli       tp, s1, 31
                  mul        s0, a1, s0
                  lb         s7, -6(a3)
                  csrrc      tp, 0x340, a1
                  lh         a1, 9(a3)
                  lb         s0, 4(a3) #end riscv_hazard_instr_stream_1
                  addi       a5, zero, 6 #init loop 1 counter
                  addi       zero, zero, 0 #init loop 1 limit
sub_1_61_1_t:     c.addi     a3, -21
                  c.sub      s1, a5
                  addi       a5, a5, -1 #update loop 1 counter
                  c.sub      s0, a1
                  addi       s3, zero, 10 #init loop 0 counter
                  c.slli     t1, 12
                  addi       s7, zero, 6 #init loop 0 limit
sub_1_61_0_t:     c.addi     s10, -14
                  addi       s3, s3, -1 #update loop 0 counter
                  srai       ra, t4, 31
                  bgeu       s3, s7, sub_1_61_0_t #branch for loop 0
                  c.beqz     a5, sub_1_61_1_t #branch for loop 1
                  mulhu      s10, t0, a0
                  la         s1, region_4+506 #start load_store_instr_stream_0
                  lhu        t1, -104(s1)
                  lb         a6, 216(s1)
                  lbu        a1, 100(s1)
                  sb         sp, 141(s1)
                  la         t4, region_4+1971 #start load_store_instr_stream_1
                  lbu        a2, 38(s1)
                  sb         t0, -599(t4)
                  lhu        ra, -459(t4)
                  sh         a4, -222(s1)
                  lb         t0, 118(t4)
                  lbu        s5, 167(s1)
                  lbu        a0, -62(t4)
                  sb         a6, -121(s1)
                  sb         s0, 13(s1)
                  sb         a7, 396(t4) #end load_store_instr_stream_1
                  lbu        tp, -214(s1) #end load_store_instr_stream_0
                  addi       ra, zero, 3 #init loop 0 counter
                  addi       s5, zero, -16 #init loop 0 limit
                  .4byte 0x00100073 # ebreak
sub_1_62_0_t:     csrrwi     zero, 0x340, 13
                  addi       ra, ra, -1 #update loop 0 counter
                  bne        ra, s5, sub_1_62_0_t #branch for loop 0
                  remu       t2, t4, t3
                  la         gp, region_2+3557 #start load_store_instr_stream_2
                  la         s11, region_0+1323 #start load_store_instr_stream_1
                  lb         s7, -486(s11)
                  la         s3, region_1+1164 #start load_store_instr_stream_3
                  la         tp, region_4+925 #start load_store_instr_stream_0
                  lh         s1, 13(gp)
                  lbu        s10, 714(s11)
                  lhu        s7, 995(s11)
                  lbu        s6, 2(gp)
                  lbu        s7, 1013(s11)
                  lb         a5, 0(gp)
                  sb         t5, 10(tp)
                  lhu        s2, -15(gp)
                  lb         zero, -141(s11)
                  lhu        a0, 25(tp)
                  sb         s5, 4(gp)
                  lb         a6, 39(s3)
                  sb         ra, -39(tp)
                  lh         s0, -1015(s11)
                  lw         s1, 3(gp) #end load_store_instr_stream_2
                  sb         s9, 49(s3)
                  lb         t3, 833(s11)
                  sb         a5, 22(s3)
                  sb         a7, 823(s11)
                  lb         s10, -6(tp)
                  sw         s3, 793(s11) #end load_store_instr_stream_1
                  lbu        a6, -12(tp)
                  sh         s8, -40(s3)
                  lb         s2, 55(s3) #end load_store_instr_stream_3
                  lb         a3, 46(tp) #end load_store_instr_stream_0
                  la         tp, region_0+330 #start riscv_load_store_rand_instr_stream_2
                  addi       s1, a7, -57
                  lb         t5, 201(tp)
                  sll        s7, a5, a6
                  mulhsu     s0, zero, s11
                  remu       s11, sp, zero
                  lb         t0, 113(tp)
                  lb         s3, 67(tp)
                  c.ebreak;c.nop;
                  lb         a4, -17(tp)
                  sub        a4, a2, s1
                  lhu        s2, -4(tp)
                  lhu        t3, 164(tp)
                  ori        a0, a5, -632
                  slli       a4, s2, 19
                  c.andi     a3, -26
                  mulhsu     t5, tp, s5
                  lui        a3, 306607
                  lhu        a1, -130(tp)
                  c.add      s6, s10
                  lbu        a4, -82(tp)
                  lb         gp, -34(tp)
                  mulhsu     t6, a5, s9
                  lbu        t4, 226(tp)
                  and        zero, s7, t4
                  lb         s4, -88(tp)
                  lb         t0, -245(tp)
                  add        a0, t1, t1
                  sb         s4, 176(tp)
                  c.andi     a3, 26
                  lb         s2, 143(tp)
                  addi       s2, t6, -385
                  lbu        s11, 61(tp)
                  sltu       a1, s8, s11
                  nop
                  sb         s6, -76(tp)
                  lhu        t2, 200(tp)
                  lbu        gp, -208(tp)
                  c.or       s1, a1
                  sb         ra, -55(tp)
                  sb         t0, -168(tp)
                  addi       t2, a3, 436
                  sltiu      s2, s10, -680
                  lb         a7, -162(tp)
                  c.srli     a1, 23
                  sb         s6, -140(tp)
                  lhu        t4, -226(tp) #end riscv_load_store_rand_instr_stream_2
sub_1_23:         jal        gp, 1f
0:                c.jal      25f
1:                c.j        12f
2:                jal        t1, 22f
3:                jal        t1, 20f
4:                c.j        13f
5:                jal        s11, 26f
6:                c.jal      4b
7:                c.j        11f
8:                c.j        2b
9:                jal        a0, 10f
10:               jal        t1, 28f
11:               jal        ra, 3b
12:               c.j        27f
13:               c.j        16f
14:               jal        t1, 5b
15:               c.j        17f
16:               jal        t1, 23f
17:               c.jal      0b
18:               c.j        15b
19:               jal        a3, 8b
20:               c.jal      21f
21:               c.jal      24f
22:               c.jal      14b
23:               c.j        18b
24:               c.jal      6b
25:               c.jal      19b
26:               jal        gp, 9b
27:               c.j        7b
28:               c.lui      t3, 4
                  la         s11, region_1+9223 #start load_store_instr_stream_4
                  la         t5, region_3+63 #start load_store_instr_stream_3
                  la         t6, region_0+2721 #start load_store_instr_stream_1
                  la         a5, region_4+1049 #start load_store_instr_stream_0
                  lh         zero, 495(t6)
                  la         gp, region_2+685 #start load_store_instr_stream_2
                  sb         a3, -196(a5)
                  lb         a3, 210(gp)
                  sb         tp, -838(t6)
                  sb         s6, 48(s11)
                  sh         t3, -15(s11)
                  sb         a5, 20(gp)
                  lb         s1, -164(gp)
                  lhu        a7, 7(t5)
                  lb         a2, 95(a5)
                  lh         a7, 51(s11)
                  lhu        s5, -179(a5)
                  lb         ra, 28(s11)
                  lh         t2, 397(t6)
                  lh         s10, 11(a5)
                  lhu        ra, -3(s11)
                  sw         s11, -31(s11)
                  lbu        s10, -56(t5)
                  sb         a0, 141(gp)
                  lbu        t4, -32(t5)
                  lhu        s6, 17(a5)
                  sb         sp, -62(t5)
                  sb         s4, 570(t6)
                  sh         t5, 49(s11)
                  sb         t1, -126(a5)
                  lw         s4, 227(a5)
                  lbu        s10, -42(t5)
                  lb         t1, 30(s11) #end load_store_instr_stream_4
                  lhu        zero, -29(t5)
                  lbu        s2, 232(gp)
                  lh         zero, 975(t6)
                  sb         t4, -226(t6) #end load_store_instr_stream_1
                  lbu        t3, 16(gp) #end load_store_instr_stream_2
                  lbu        s1, 60(a5)
                  lb         s10, -30(t5)
                  lb         s7, -16(t5) #end load_store_instr_stream_3
                  lbu        a1, 161(a5) #end load_store_instr_stream_0
                  addi       a2, zero, -6 #init loop 1 counter
                  addi       s5, t1, -209
                  addi       zero, zero, 0 #init loop 1 limit
                  div        a3, t4, a0
                  xori       s5, t3, -925
                  sra        t3, s3, t6
                  c.or       s0, a5
                  auipc      s0, 549420
                  rem        a5, s4, a4
sub_1_66_1_t:     slt        a7, s11, a4
                  lui        a0, 791510
                  auipc      t0, 438576
                  addi       a2, a2, 3 #update loop 1 counter
                  csrrw      s10, 0x340, t3
                  addi       a6, zero, -4 #init loop 0 counter
                  add        a7, s4, t5
                  c.andi     a4, -28
                  c.lui      a3, 15
                  rem        t3, s2, t2
                  csrrsi     s1, 0x340, 0
                  addi       t4, zero, -1 #init loop 0 limit
                  c.xor      a1, a0
sub_1_66_0_t:     c.mv       s5, s5
                  mul        s10, s3, s8
                  xor        tp, t4, s1
                  csrrci     gp, 0x340, 4
                  addi       a6, a6, 2 #update loop 0 counter
                  srl        t0, zero, s8
                  blt        a6, t4, sub_1_66_0_t #branch for loop 0
                  csrrs      s3, 0x340, s4
                  sra        a0, s9, a1
                  c.bnez     a2, sub_1_66_1_t #branch for loop 1
                  auipc      s3, 927834
                  la         a0, region_3+112 #start riscv_hazard_instr_stream_4
                  xori       a2, t0, -355
                  ori        a3, t4, -159
                  lb         a2, 5(a0)
                  lbu        a5, 130(a0)
                  div        a5, a2, t0
                  c.nop
                  sh         a2, 360(a0)
                  ori        a2, t4, -337
                  and        t0, a3, t4
                  lbu        t2, 171(a0)
                  lbu        t4, 293(a0)
                  c.srai     a3, 10
                  xor        t2, a5, t4
                  sb         t4, 64(a0)
                  nop
                  lw         a5, 280(a0)
                  .4byte 0x00100073 # ebreak
                  or         t2, t0, a2
                  mul        t0, t2, t4
                  sltu       a2, a5, a5
                  srli       t2, t4, 14
                  sh         t0, 150(a0)
                  c.lw       a2, 8(a0)
                  xor        a2, a3, t2
                  sb         t4, 217(a0)
                  lb         t2, -9(a0)
                  div        t0, t0, t4
                  sra        a5, a2, t0
                  lh         a2, -24(a0)
                  lbu        t4, 201(a0)
                  lbu        t4, 109(a0)
                  lbu        a5, 360(a0)
                  lb         t4, 166(a0)
                  add        t0, t4, t4
                  lb         t0, 234(a0)
                  lb         a3, -85(a0)
                  sub        a5, a5, t2
                  lb         a3, 77(a0)
                  csrrwi     t2, 0x340, 9
                  c.ebreak;c.nop;
                  add        a3, a3, a2
                  c.sw       a3, 8(a0)
                  c.srli     a3, 16
                  sll        a5, a3, t2
                  c.sub      a3, a3
                  lb         a3, 240(a0)
                  sll        t2, t0, t0
                  divu       a2, t2, t4
                  sb         a3, -30(a0)
                  c.sub      a2, a3
                  csrrci     t0, 0x340, 16
                  auipc      a5, 382164
                  lb         a5, 150(a0) #end riscv_hazard_instr_stream_4
                  la         t0, region_2+5991 #start load_store_instr_stream_1
                  lb         ra, -366(t0)
                  lb         s5, -957(t0)
                  la         t6, region_2+2050 #start load_store_instr_stream_2
                  la         s11, region_2+6387 #start load_store_instr_stream_0
                  la         gp, region_2+1942 #start load_store_instr_stream_4
                  la         s2, region_2+2099 #start load_store_instr_stream_3
                  sh         ra, -2(gp)
                  sh         t6, -484(t6)
                  lhu        a0, 47(s11)
                  sb         a3, 285(t0)
                  lbu        a6, -413(s2)
                  lbu        s7, 1(gp)
                  lbu        s3, 25(s11)
                  lbu        a6, -32(s11)
                  lb         s4, -933(t0)
                  lb         s7, 124(s2)
                  sh         s10, -245(s2)
                  lbu        t2, 987(t6)
                  lhu        s4, -913(s2)
                  lbu        a6, -9(gp)
                  sb         a4, -336(s2)
                  lb         a3, -20(s11)
                  lhu        s10, -8(gp)
                  lb         s5, 3(gp)
                  sb         s1, -50(s11)
                  lbu        s6, 176(t6)
                  lh         a5, -6(gp)
                  lhu        a1, 39(s11)
                  lb         a5, -16(gp)
                  lbu        t4, 497(s2)
                  lb         s1, -918(t6)
                  lb         ra, 851(t6)
                  lb         a3, 396(s2)
                  lw         a4, 857(s2) #end load_store_instr_stream_3
                  lbu        a1, 3(gp) #end load_store_instr_stream_4
                  sb         a1, -464(t0) #end load_store_instr_stream_1
                  lbu        t5, -203(t6) #end load_store_instr_stream_2
                  lhu        t5, -19(s11) #end load_store_instr_stream_0
                  la         t6, region_2+4459 #start load_store_instr_stream_2
                  la         a2, region_2+2203 #start load_store_instr_stream_1
                  la         a4, region_2+4803 #start load_store_instr_stream_0
                  lh         s1, -811(a2)
                  lb         t4, -42(t6)
                  sb         a1, -15(t6)
                  lbu        t1, 6(t6)
                  lhu        s10, 135(a2)
                  sw         ra, 777(a4)
                  lb         tp, 10(t6)
                  sw         a6, 445(a2)
                  lbu        a3, 32(t6)
                  lb         t2, 186(a4)
                  lb         t5, -28(t6) #end load_store_instr_stream_2
                  sb         t4, 400(a4)
                  sb         s0, -281(a4)
                  lhu        t5, -887(a2)
                  sh         s6, -585(a2) #end load_store_instr_stream_1
                  lbu        s4, 983(a4)
                  lw         a0, 557(a4) #end load_store_instr_stream_0
                  la         a0, region_2+3710 #start load_store_instr_stream_0
                  la         ra, region_1+5059 #start load_store_instr_stream_2
                  sh         t1, -8(a0)
                  la         t3, region_4+3445 #start load_store_instr_stream_3
                  lhu        tp, -11(ra)
                  lhu        t6, 5(ra)
                  lb         s5, 649(t3)
                  sb         s7, 15(a0)
                  sb         s4, 6(ra)
                  lhu        t1, 429(t3)
                  lh         s2, 265(t3)
                  lh         zero, 5(ra)
                  la         a5, region_0+3177 #start load_store_instr_stream_1
                  sh         s9, -599(t3)
                  lbu        s1, -7(ra)
                  lbu        s10, 593(t3)
                  lh         t4, 5(a5)
                  lbu        a6, 8(a5)
                  lbu        a1, 23(a0)
                  lbu        s1, -8(a5)
                  sb         sp, 60(a0)
                  lbu        t1, -12(a5)
                  sb         s1, 245(t3)
                  lb         a2, 8(a5)
                  sh         t6, -5(ra)
                  sb         s10, 10(a5)
                  lb         a6, 923(t3)
                  sb         tp, -16(a5) #end load_store_instr_stream_1
                  lh         s2, 393(t3)
                  lb         s2, 1(a0)
                  lb         s6, -6(ra)
                  lhu        s2, -18(a0)
                  sh         sp, -845(t3)
                  lhu        s0, -12(a0)
                  sb         a6, -14(ra) #end load_store_instr_stream_2
                  sb         a6, 648(t3) #end load_store_instr_stream_3
                  lbu        s3, -35(a0) #end load_store_instr_stream_0
                  addi       t6, zero, 9 #init loop 1 counter
                  addi       s3, zero, -1 #init loop 1 limit
sub_1_64_1_t:     mulh       t0, t5, a6
                  addi       t6, t6, -2 #update loop 1 counter
                  addi       ra, zero, -10 #init loop 0 counter
                  sub        t3, s8, t3
                  addi       s6, zero, -9 #init loop 0 limit
sub_1_64_0_t:     sltu       t4, tp, s8
                  addi       ra, ra, 3 #update loop 0 counter
                  blt        ra, s6, sub_1_64_0_t #branch for loop 0
                  bne        t6, s3, sub_1_64_1_t #branch for loop 1
                  csrrw      t1, 0x340, gp
sub_1_16:         jal        gp, 3f
0:                c.jal      6f
1:                c.jal      5f
2:                c.jal      4f
3:                c.jal      12f
4:                c.jal      8f
5:                jal        ra, 0b
6:                jal        ra, 7f
7:                jal        ra, 11f
8:                jal        tp, 1b
9:                c.jal      10f
10:               c.j        13f
11:               jal        ra, 9b
12:               c.j        2b
13:               slti       t0, s1, 1013
                  blt        s7, t2, 8f
                  sltu       a3, ra, t5
                  c.slli     t3, 13
                  sll        s1, tp, t1
                  bltu       t3, a3, 16f
                  srli       t4, t3, 11
                  sub        s1, s2, t4
                  andi       gp, s8, 638
8:                c.ebreak;c.nop;
                  bge        s4, s4, 17f
                  ori        a2, s2, 922
                  csrrsi     s11, 0x340, 31
                  and        a5, s9, s11
                  sll        t5, s0, sp
                  sub        t1, t3, s1
                  beq        a7, a5, 29f
16:               c.andi     a4, -30
17:               rem        a7, zero, ra
                  sltu       s4, s3, s3
                  slli       zero, t0, 31
                  mulh       a6, a1, s4
                  blt        a5, t0, 40f
                  div        a6, a3, s5
                  bne        s5, t6, 39f
                  and        t4, s8, ra
                  and        s3, s0, t0
                  c.xor      a0, a1
                  mulhu      a6, a4, t0
                  csrrsi     s2, 0x340, 9
29:               c.lui      tp, 19
                  nop
                  c.bnez     s1, 43f
                  csrrsi     t0, 0x340, 21
                  remu       s1, a2, s5
                  c.nop
                  csrrci     s7, 0x340, 5
                  c.lui      gp, 4
                  c.li       gp, -16
                  nop
39:               mul        t4, s11, t4
40:               rem        s3, ra, a4
                  slli       s2, a0, 10
                  srl        s0, t5, s5
43:               blt        s4, t0, 45f
                  c.xor      a4, a2
45:               c.xor      s1, s0
                  srli       a1, s9, 22
                  c.nop
                  sltu       t4, ra, t5
                  bltu       t2, s11, 57f
                  slti       t0, s9, -708
                  bltu       zero, gp, 69f
                  sll        a7, s8, gp
                  blt        a5, tp, 57f
                  or         s10, a5, t1
                  srai       a7, s3, 10
                  c.mv       a3, a3
57:               c.li       t3, 19
                  bge        t2, ra, 74f
                  addi       t3, ra, 27
                  nop
                  slti       t1, s8, 976
                  rem        a7, a3, t2
                  csrrc      t0, 0x340, ra
                  lui        t2, 456716
                  mul        t5, a5, a7
                  auipc      s3, 611063
                  .4byte 0x00100073 # ebreak
                  csrrci     a4, 0x340, 24
69:               rem        ra, s8, s8
                  c.beqz     a4, 76f
                  c.ebreak;c.nop;
                  slt        a3, s9, s3
                  csrrci     a5, 0x340, 20
74:               nop
                  xor        t5, gp, a5
76:               mul        t1, a2, s6
                  csrrci     s11, 0x340, 13
                  bne        s5, s8, 97f
                  add        t1, s10, zero
                  c.xor      a1, a5
                  c.li       s6, 21
                  bltu       s4, t6, 88f
                  mulh       a7, s2, zero
                  xor        zero, t4, a5
                  bgeu       t4, t4, 87f
                  csrrc      a7, 0x340, t1
87:               add        t5, t0, s8
88:               c.srli     s0, 8
                  c.xor      s1, a1
                  csrrwi     t0, 0x340, 26
                  xor        tp, a7, t6
                  xori       t0, t1, -859
                  c.ebreak;c.nop;
                  mulhu      t6, a5, s7
                  addi       t3, t0, -307
                  c.mv       a3, s0
97:               c.sub      a5, a1
                  c.bnez     a5, 103f
                  and        a4, t6, ra
                  bne        s6, s8, 102f
                  csrrwi     s6, 0x340, 20
102:              c.srai     a4, 5
103:              csrrci     t4, 0x340, 7
                  bltu       tp, s8, 108f
                  or         t6, a5, t1
                  or         t6, ra, t1
                  bge        tp, a0, 120f
108:              mulhsu     s4, a6, s4
                  csrrci     t0, 0x340, 18
                  bgeu       sp, a6, 124f
                  auipc      s6, 515478
                  sra        a6, a2, s10
                  addi       a0, a4, -181
                  srai       t0, a0, 9
                  bge        a4, s2, 125f
                  bge        sp, a0, 136f
                  c.ebreak;c.nop;
                  xori       gp, a1, 612
                  bge        t0, s4, 138f
120:              ori        a7, t0, 930
                  mulhu      t6, t0, t6
                  and        ra, t3, a6
                  csrrsi     zero, 0x340, 18
124:              rem        gp, s11, s1
125:              remu       s1, a2, a2
                  mulhu      a7, a0, s9
                  c.xor      a3, s0
                  c.andi     s1, 19
                  csrrsi     a6, 0x340, 11
                  or         gp, s0, a2
                  c.ebreak;c.nop;
                  mul        t0, a3, a3
                  lui        s6, 43309
                  c.nop
                  csrrw      s7, 0x340, s6
136:              csrrc      s11, 0x340, s4
                  auipc      t5, 562037
138:              div        s4, s7, a0
                  mulhsu     a5, s6, s0
                  remu       s2, a2, t5
                  c.and      a3, a3
                  c.lui      t4, 28
                  c.xor      s1, a0
                  and        s4, a0, zero
                  c.andi     a4, -13
                  blt        s3, s2, 151f
                  rem        zero, a0, t3
                  slli       a4, t1, 24
                  c.xor      a2, s1
                  xor        s2, zero, a0
151:              sll        a2, t5, t2
                  srli       s11, t1, 26
                  csrrw      gp, 0x340, s4
                  c.addi     s11, -7
                  csrrci     tp, 0x340, 1
                  c.andi     a5, -8
                  c.lui      a6, 5
                  csrrci     s5, 0x340, 23
                  .4byte 0x00100073 # ebreak
                  div        s10, a6, s11
                  csrrci     t5, 0x340, 28
                  mul        t4, s0, a2
                  or         a6, a3, s11
                  csrrc      s0, 0x340, s0
                  c.li       t4, 24
                  c.srli     a2, 30
                  divu       t6, t5, s1
                  bltu       zero, a7, 180f
                  ori        s10, s1, -603
                  c.and      a3, a4
                  csrrs      s1, 0x340, s3
                  sub        a1, a6, s11
                  c.add      s5, t6
                  lui        a1, 576890
                  xor        a0, a5, s8
                  c.beqz     a4, 196f
                  c.nop
                  rem        s4, a7, s11
                  c.li       t3, -12
180:              div        s11, a5, t0
                  c.srli     a5, 28
                  c.addi     gp, 24
                  csrrci     s5, 0x340, 6
                  c.andi     a1, 7
                  c.ebreak;c.nop;
                  sltu       a6, a7, s11
                  srl        t2, t6, t2
                  csrrwi     s6, 0x340, 8
                  csrrsi     a1, 0x340, 17
                  slti       a2, s4, -730
                  bge        a7, a0, 199f
                  c.ebreak;c.nop;
                  csrrw      a1, 0x340, a4
                  and        s3, a4, t1
                  andi       a2, t3, 465
196:              c.beqz     a0, 204f
                  sltiu      s7, a7, -710
                  remu       s11, a3, s9
199:              c.bnez     a1, 207f
                  mul        a5, s8, s8
                  slti       a2, a0, 585
                  nop
                  c.xor      s0, a2
204:              addi       t4, s1, -260
                  c.sub      s0, a4
                  xori       a1, a0, 956
207:              csrrwi     a0, 0x340, 18
                  srli       a2, a3, 29
                  ori        s5, s11, -305
                  slti       a4, s0, -311
                  csrrci     a0, 0x340, 28
                  sltiu      s7, a3, -437
                  mulhu      a7, s3, zero
                  c.bnez     a4, 226f
                  addi       t6, a0, 550
                  add        s10, s4, a3
                  sll        s0, a5, a2
                  slli       s10, s1, 21
                  andi       t0, t0, -315
                  c.sub      a0, s0
                  mul        gp, s1, t6
                  rem        a3, sp, s2
                  beq        s7, s7, 242f
                  c.li       s10, 28
                  c.addi     a2, 18
226:              beq        s2, a0, 228f
                  c.and      a5, a0
228:              and        t1, a2, sp
                  slti       tp, t3, -411
                  slli       t1, t3, 21
                  c.bnez     s0, 233f
                  c.srli     a0, 10
233:              c.ebreak;c.nop;
                  bge        s2, sp, 239f
                  c.add      a4, t6
                  bne        t1, s8, 241f
                  csrrw      t4, 0x340, ra
                  c.lui      a3, 8
239:              c.addi     t2, -27
                  c.addi     t4, 12
241:              bgeu       s2, s4, 259f
242:              slti       s5, s8, 939
                  c.lui      t0, 31
                  c.slli     s6, 2
                  div        tp, s4, s1
                  sltu       t6, s0, s8
                  lui        s6, 454137
                  bltu       s3, t5, 262f
                  andi       zero, ra, -682
                  auipc      a4, 267417
                  c.and      s1, a3
                  bgeu       t6, t2, 254f
                  c.addi     s11, 6
254:              c.add      gp, t1
                  c.and      a4, s1
                  c.addi     ra, -28
                  c.nop
                  divu       t0, s3, zero
259:              mulhsu     a0, t2, t5
                  c.lui      t3, 17
                  blt        t6, tp, 281f
262:              remu       a5, s1, sp
                  .4byte 0x00100073 # ebreak
                  c.bnez     s1, 284f
                  sll        s6, a3, a5
                  csrrc      t2, 0x340, a6
                  c.li       a7, -3
                  xori       ra, t5, 94
                  srl        s4, s0, a4
                  slti       a0, s9, 86
                  blt        a4, ra, 285f
                  srl        a0, a6, s4
                  sltu       s2, s9, s5
                  bge        s0, s4, 293f
                  slti       a0, s10, -727
                  beq        a0, tp, 284f
                  csrrwi     ra, 0x340, 8
                  c.xor      a5, a2
                  csrrci     a6, 0x340, 29
                  mulhu      s10, a1, s5
281:              c.beqz     s1, 285f
                  c.and      a0, s0
                  mul        s0, s1, s10
284:              srli       a7, s7, 8
285:              c.li       a4, -16
                  csrrci     s0, 0x340, 11
                  slt        gp, a0, a4
                  sltu       t1, a0, tp
                  c.and      s1, a1
                  div        a0, a6, t6
                  and        t1, t1, a1
                  c.srli     a5, 6
293:              lui        a4, 839995
                  and        s2, a3, s11
                  sra        s1, t5, ra
                  csrrwi     t2, 0x340, 28
                  sll        a1, s4, s6
                  and        a7, a7, s5
                  mul        a4, s9, s1
                  mulhu      s0, s3, a6
                  csrrs      s4, 0x340, s10
                  nop
                  bltu       a6, ra, 322f
                  .4byte 0x00100073 # ebreak
                  c.andi     a3, -11
                  slt        t2, a0, zero
                  c.xor      a2, a2
                  and        a1, s10, sp
                  c.ebreak;c.nop;
                  addi       t5, t5, -663
                  srli       s1, s4, 4
                  slti       s4, s10, 225
                  csrrs      a3, 0x340, t5
                  xori       a7, t3, 901
                  c.add      t3, a2
                  srl        zero, s8, a6
                  rem        s5, a0, s5
                  lui        zero, 649289
                  c.andi     a4, 13
                  c.mv       t6, s0
                  c.srli     a0, 29
322:              csrrwi     t1, 0x340, 4
                  c.or       a5, a0
                  c.slli     tp, 5
                  nop
                  sltu       ra, s11, s5
                  bgeu       a7, a5, 343f
                  c.li       s6, -15
                  mulh       s7, ra, a1
                  mulhu      s0, ra, t1
                  xor        t3, a4, a6
                  srli       s11, t4, 26
                  mul        s0, t3, tp
                  sll        tp, t2, t3
                  rem        s10, a6, a6
                  c.and      a5, s1
                  csrrc      zero, 0x340, gp
                  bltu       a7, a4, 350f
                  sltiu      a5, gp, -248
                  csrrs      s0, 0x340, s5
                  or         t0, a1, t1
                  lui        a2, 1031426
343:              addi       a7, s11, 535
                  c.bnez     s1, 352f
                  c.ebreak;c.nop;
                  c.add      tp, s9
                  c.xor      a5, a0
                  c.addi     s0, 23
                  mul        t0, t3, zero
350:              add        s7, ra, s6
                  c.andi     a3, 16
352:              c.or       a4, a2
                  c.sub      a2, a5
                  sub        a0, s6, a1
                  c.lui      t1, 13
                  csrrs      a2, 0x340, s3
                  csrrc      a0, 0x340, gp
                  addi       s1, s5, 341
                  slti       s7, a7, -172
                  xori       s0, t0, -572
                  c.bnez     a4, 374f
                  bgeu       s5, sp, 366f
                  mulhsu     s7, s1, a5
                  c.nop
                  nop
366:              csrrw      zero, 0x340, zero
                  c.sub      a3, a4
                  c.andi     a1, 9
                  c.srai     a4, 29
                  csrrw      ra, 0x340, a0
                  addi       t0, t0, -382
                  bgeu       t4, tp, 378f
                  divu       s7, s3, s0
374:              c.slli     s11, 19
                  srli       s1, t2, 15
                  nop
                  mul        s7, t2, t0
378:              bne        sp, sp, 386f
                  slt        tp, t2, tp
                  xori       zero, a0, -649
                  divu       a2, s9, s11
                  c.add      t2, t3
                  beq        gp, s11, 391f
                  mul        t5, sp, s6
                  sub        a5, s1, a0
386:              addi       s6, t1, -920
                  csrrsi     a3, 0x340, 7
                  csrrwi     a3, 0x340, 12
                  nop
                  c.nop
391:              c.or       a3, a4
                  xor        t2, a2, t3
                  and        a7, a4, a5
                  blt        a3, a3, 406f
                  srl        a3, s6, s1
                  divu       a7, t3, t0
                  blt        t0, zero, 407f
                  xori       gp, zero, 135
                  slti       t0, s4, -440
                  sltu       s7, sp, s3
                  c.srli     s0, 19
                  xori       s2, a1, 156
                  ori        s3, a3, -269
                  c.beqz     a4, 410f
                  nop
406:              c.slli     a2, 5
407:              c.srai     a5, 14
                  csrrsi     t0, 0x340, 16
                  c.nop
410:              srl        ra, s8, t1
                  c.andi     a0, -31
                  sll        t5, s8, zero
                  c.and      a5, a4
                  slti       t4, t6, -78
                  c.and      a4, a4
                  c.add      t2, t4
                  sll        s2, a6, t3
                  and        a1, a6, t5
                  lui        a4, 475989
                  addi       s2, sp, -583
                  bge        s1, s1, 429f
                  addi       s2, a6, 104
                  sra        s4, s10, s2
                  mul        t5, s2, s1
                  xor        ra, s4, a1
                  sltiu      t4, zero, 297
                  csrrci     zero, 0x340, 22
                  c.srai     a4, 12
429:              bgeu       a7, a5, 437f
                  c.xor      a2, s0
                  xori       t1, s5, -529
                  rem        a2, a0, s3
                  c.ebreak;c.nop;
                  sra        a0, a4, gp
                  and        a3, ra, a4
                  csrrwi     s10, 0x340, 12
437:              sltu       a5, sp, a0
                  srl        a3, s6, a1
                  bgeu       tp, t5, 455f
                  c.addi     t0, -19
                  sltiu      t3, a7, -333
                  nop
                  mulhsu     t1, s5, a5
                  sltiu      a5, s2, -431
                  or         s11, a4, s3
                  sltu       s1, s4, s2
                  mulhsu     a6, s3, t2
                  and        t4, s5, a5
                  div        s2, a2, a4
                  c.andi     a1, -26
                  divu       t4, a5, s1
                  nop
                  bge        s2, a2, 472f
                  csrrs      t0, 0x340, s8
455:              c.andi     s1, 23
                  c.srli     a4, 29
                  andi       t1, a2, -269
                  blt        a3, s4, 466f
                  sltu       a5, s11, s6
                  c.mv       s3, sp
                  c.addi     gp, -14
                  divu       a6, t3, s3
                  remu       gp, gp, sp
                  divu       ra, t3, ra
                  c.or       a3, a3
466:              srai       s3, a7, 5
                  bne        t2, zero, 477f
                  c.bnez     a0, 474f
                  xor        t5, sp, t0
                  sra        a6, s8, gp
                  csrrc      s2, 0x340, s7
472:              mulh       s3, t4, a6
                  xor        t5, a1, s6
474:              divu       s1, a0, s8
                  c.nop
                  add        a3, gp, a6
477:              sub        s1, s5, zero
                  slli       ra, s8, 21
                  lui        s11, 274496
                  srl        s10, t1, s6
                  addi       s5, s7, -431
                  blt        a5, tp, 488f
                  c.andi     a4, 24
                  srli       a0, tp, 20
                  slli       a0, s0, 19
                  csrrs      a7, 0x340, s3
                  csrrwi     t4, 0x340, 17
488:              blt        ra, tp, 500f
                  or         s1, zero, s0
                  c.add      t3, a3
                  beq        a0, t1, 509f
                  mulh       gp, a1, tp
                  sltu       t6, t4, t6
                  div        a3, s10, s2
                  csrrc      s7, 0x340, a2
                  sub        s11, a5, gp
                  mul        a5, s7, s1
                  divu       gp, t6, s1
                  mulhu      s7, t4, a7
500:              sra        a1, s8, t3
                  add        t2, s4, s9
                  srli       a0, s6, 14
                  xor        t3, s9, gp
                  .4byte 0x00100073 # ebreak
                  mulhsu     s3, s3, a5
                  divu       t4, t2, a7
                  srl        t6, a0, t5
                  csrrs      t0, 0x340, t3
509:              srli       a3, s11, 19
                  rem        a1, s3, a0
                  rem        s10, sp, s5
                  and        s1, s0, a3
                  beq        s11, s3, 521f
                  c.or       a1, a3
                  bge        a7, s0, 535f
                  slli       s3, s11, 31
                  c.add      s5, a6
                  addi       t0, s10, 919
                  sltu       a0, s10, a6
                  c.mv       t3, tp
521:              c.srli     a5, 12
                  mulh       t3, s9, ra
                  sra        t3, s10, tp
                  mulhu      t4, t1, t6
                  csrrsi     s10, 0x340, 31
                  bge        s8, a1, 542f
                  c.and      a1, a5
                  remu       t5, a7, s2
                  mul        t5, s10, t5
                  .4byte 0x00100073 # ebreak
                  blt        s1, t4, 536f
                  or         s7, s0, ra
                  mulh       ra, a1, ra
                  bgeu       t1, a4, 542f
535:              rem        a4, s10, sp
536:              addi       a0, a1, -768
                  andi       a7, s10, -1004
                  c.andi     a4, -32
                  srli       s2, tp, 10
                  csrrc      a5, 0x340, s11
                  div        t2, t0, s0
542:              xori       a3, s2, 166
                  mulhu      a7, t2, s0
                  remu       a4, gp, a0
                  c.sub      a2, s0
                  c.bnez     s1, 560f
                  c.srai     a5, 25
                  rem        gp, s9, t0
                  andi       t6, t2, -852
                  mulhu      a7, t6, a5
                  c.slli     a3, 15
                  sra        s7, sp, s8
                  c.beqz     s0, 555f
                  csrrci     s0, 0x340, 19
555:              add        a2, a5, t4
                  c.add      a4, a3
                  sub        ra, s5, s1
                  sub        s10, s6, t1
                  slt        s11, sp, t3
560:              slli       t0, s0, 26
                  mulhu      a6, zero, a6
                  sra        s3, s3, a6
                  sltiu      s3, s5, -284
                  blt        a4, s5, 584f
                  slli       t1, s9, 12
                  c.nop
                  blt        a7, tp, 575f
                  c.lui      t0, 31
                  csrrci     a2, 0x340, 2
                  bltu       t2, t1, 574f
                  c.li       ra, -31
                  c.add      t4, t0
                  c.nop
574:              slti       t0, a1, 319
575:              bge        gp, a1, 577f
                  srli       s0, s7, 31
577:              c.and      a4, a4
                  c.nop
                  sll        gp, t1, a5
                  csrrsi     s7, 0x340, 7
                  rem        a0, a2, gp
                  c.xor      s0, s1
                  csrrwi     s4, 0x340, 10
584:              mul        ra, s7, a3
                  c.lui      s5, 29
                  bgeu       t1, s2, 605f
                  and        a3, s6, s4
                  remu       a3, t5, s2
                  csrrw      a2, 0x340, s4
                  csrrs      s5, 0x340, gp
                  slti       a2, a3, 418
                  lui        a5, 894303
                  mul        a4, s9, s10
                  nop
                  c.bnez     s0, 603f
                  c.addi     a0, 7
                  csrrci     a7, 0x340, 18
                  xor        s6, s0, s7
                  c.lui      s3, 8
                  mulh       s4, s4, t1
                  c.or       a4, a0
                  c.addi     a5, -31
603:              csrrwi     s2, 0x340, 11
                  addi       a5, t4, 866
605:              c.bnez     a1, 613f
                  c.beqz     a4, 622f
                  c.and      s1, a3
                  c.slli     s4, 13
                  c.bnez     a2, 623f
                  c.srai     s0, 28
                  c.mv       a3, s10
                  sltiu      a5, ra, 503
613:              c.addi     s4, -5
                  c.xor      a1, a5
                  c.addi     t0, 26
                  mulhu      zero, s6, t2
                  c.bnez     a3, 636f
                  c.srai     a5, 27
                  c.add      a2, s7
                  andi       s2, a0, -279
                  or         a2, t3, s2
622:              c.addi     a7, -24
623:              add        a4, a5, a6
                  c.nop
                  and        tp, t3, s8
                  csrrsi     s6, 0x340, 23
                  c.slli     a0, 3
                  sub        s7, a5, a3
                  sltu       s4, s2, s3
                  c.lui      a0, 19
                  remu       s3, a5, a4
                  mulh       s11, s9, s10
                  c.sub      a0, s1
                  c.beqz     s0, 638f
                  sra        t1, t6, a0
636:              c.nop
                  sltiu      ra, s3, -325
638:              bne        s8, t4, 651f
                  remu       ra, t1, sp
                  bgeu       ra, t0, 652f
                  c.srai     s1, 3
                  sub        a0, a6, s10
                  slti       a1, s4, -518
                  lui        t6, 28343
                  csrrw      s1, 0x340, s4
                  slt        tp, a6, ra
                  lui        a1, 636970
                  csrrci     a6, 0x340, 30
                  or         s4, s8, zero
                  c.srli     a2, 15
651:              srli       a0, a7, 23
652:              mulh       a4, ra, s10
                  srli       s5, a1, 25
                  nop
                  sltiu      t3, t0, 316
                  c.add      t1, s11
                  andi       a0, s3, -470
                  c.addi     gp, -19
                  div        a1, s8, t5
                  slti       a7, t1, -751
                  remu       a3, s9, a7
                  csrrw      gp, 0x340, s10
                  .4byte 0x00100073 # ebreak
                  c.srli     a0, 3
                  bge        s11, ra, 677f
                  .4byte 0x00100073 # ebreak
                  slti       s7, s10, -900
                  lui        s7, 226741
                  srli       a2, a1, 9
                  slli       a4, t4, 30
                  c.add      s0, s8
                  csrrsi     t1, 0x340, 2
                  csrrc      tp, 0x340, a0
                  srl        a2, sp, tp
                  bgeu       a0, a0, 680f
                  csrrw      a0, 0x340, sp
677:              srli       s11, a7, 24
                  csrrc      a6, 0x340, s10
                  and        s1, s2, s8
680:              mulh       t0, s8, zero
                  bne        t3, t5, 683f
                  mulh       a5, a1, t1
683:              c.mv       gp, s8
                  c.addi     t2, -7
                  csrrs      zero, 0x340, a3
                  c.or       s1, a0
                  xori       a6, s7, 829
                  c.addi     ra, -30
                  sub        a7, ra, ra
                  c.or       a3, a2
                  xor        s1, s0, s3
                  sra        s5, a3, t5
                  csrrw      t4, 0x340, t1
                  c.srli     a0, 18
                  csrrwi     s2, 0x340, 6
                  c.mv       s5, t1
                  div        zero, s0, a4
                  xor        gp, a2, s7
                  div        s1, tp, a0
                  c.addi     s0, -11
                  c.srli     a1, 28
                  lui        t1, 840602
                  c.nop
                  and        t1, zero, a5
                  bltu       s6, t1, 718f
                  c.nop
                  sltu       s11, sp, s8
                  mulh       s5, s10, s3
                  lui        s1, 966335
                  or         a6, t4, ra
                  lui        s5, 344608
                  srl        a1, ra, s11
                  add        s11, tp, s2
                  c.nop
                  c.add      t1, sp
                  sra        a2, s1, ra
                  c.add      s10, s7
718:              mulhu      s0, gp, s8
                  sub        s5, s11, s9
                  add        s11, a2, s10
                  sltu       a4, s11, a3
                  c.add      s6, s6
                  slt        s2, a2, a5
                  slli       t3, s4, 28
                  bltu       a2, zero, 731f
                  mulhsu     s1, s11, s8
                  csrrwi     ra, 0x340, 29
                  div        a6, s0, s0
                  add        t2, s9, s6
                  srli       gp, s2, 14
731:              c.addi     t1, -32
                  csrrci     s4, 0x340, 3
                  c.addi     a1, -16
                  div        s11, s11, s7
                  divu       s6, s4, a7
                  bne        t4, zero, 744f
                  or         a0, s1, t2
                  beq        zero, a3, 742f
                  xori       s4, a0, -455
                  bge        a6, s10, 742f
                  mulh       s3, s10, a5
742:              bne        a7, s0, 754f
                  div        gp, sp, t5
744:              lui        t4, 345562
                  sub        t6, s4, s4
                  .4byte 0x00100073 # ebreak
                  andi       a2, ra, 761
                  ori        s1, s4, -111
                  addi       a1, s11, -285
                  srl        s4, s2, a4
                  .4byte 0x00100073 # ebreak
                  sltiu      a6, t0, -35
                  bltu       t6, a0, 767f
754:              sra        t0, s1, t4
                  c.ebreak;c.nop;
                  lui        s6, 137751
                  c.li       s2, 14
                  c.bnez     a3, 778f
                  remu       a7, s11, s10
                  divu       s5, a2, s11
                  and        a0, tp, tp
                  srai       zero, s10, 21
                  remu       a6, a3, s3
                  divu       s2, t0, s10
                  remu       s11, t4, s10
                  c.mv       t0, tp
767:              or         a4, s4, s7
                  sra        s2, a3, a2
                  mul        s5, s3, a0
                  addi       t5, s1, 895
                  lui        t0, 506598
                  c.and      a5, a2
                  c.nop
                  csrrw      s7, 0x340, t6
                  c.xor      a0, s1
                  srl        a4, t3, t6
                  bgeu       s5, a7, 791f
778:              c.xor      a4, a0
                  bltu       t5, ra, 784f
                  slt        s7, s4, s8
                  sltu       t2, s0, t5
                  c.xor      a0, a2
                  .4byte 0x00100073 # ebreak
784:              xor        t4, a1, sp
                  c.mv       a2, a6
                  srli       s10, a2, 26
                  blt        t4, tp, 795f
                  csrrsi     tp, 0x340, 27
                  beq        s10, s6, 808f
                  ori        s4, s1, 970
791:              nop
                  c.addi     ra, 15
                  csrrc      s5, 0x340, gp
                  remu       s2, t3, gp
795:              srl        tp, s1, a7
                  c.srli     a5, 5
                  c.lui      a3, 19
                  srai       s10, s8, 24
                  slti       s11, a3, 774
                  csrrwi     s2, 0x340, 29
                  srai       tp, a3, 0
                  c.andi     a1, 10
                  c.li       a2, -14
                  slli       s1, s4, 30
                  csrrw      s4, 0x340, s6
                  sra        s6, t3, a4
                  c.slli     t5, 3
808:              sra        a6, s9, s0
                  mulhsu     a6, a6, s11
                  c.srli     a1, 29
                  srl        s0, s1, a6
                  c.srli     a3, 15
                  srai       ra, t3, 10
                  xori       s10, a1, -829
                  csrrc      a7, 0x340, a7
                  remu       s3, s6, ra
                  csrrs      t4, 0x340, s1
                  srl        gp, s3, s0
                  div        zero, s5, a3
                  auipc      s11, 425057
                  bltu       s10, s4, 839f
                  addi       s11, a3, -843
                  sltu       zero, s7, t1
                  csrrsi     a4, 0x340, 0
                  c.srai     a3, 9
                  mulhsu     s1, a5, t6
                  nop
                  c.add      s10, s4
                  c.nop
                  c.andi     a1, 18
                  bne        s3, zero, 851f
                  divu       s6, s6, t2
                  csrrci     s11, 0x340, 20
                  srli       s10, a1, 25
                  slti       t6, t1, 76
                  c.add      a5, a7
                  mulhu      s5, a7, s5
                  csrrw      t3, 0x340, s11
839:              auipc      tp, 241521
                  srli       t0, ra, 31
                  xor        ra, a1, a0
                  srai       s6, s4, 6
                  lui        s2, 714116
                  c.sub      s0, a4
                  slli       t0, s3, 14
                  slt        a2, t6, t2
                  or         a5, s7, t6
                  mulh       a3, t4, s9
                  c.or       s1, s0
                  c.srli     a2, 2
851:              c.nop
                  csrrci     s6, 0x340, 2
                  c.add      s2, s1
                  c.slli     ra, 17
                  bge        a7, t5, 860f
                  c.bnez     a3, 860f
                  c.sub      a4, a5
                  sll        t6, t3, t1
                  csrrc      s0, 0x340, zero
860:              div        t3, tp, s10
                  sltu       a6, sp, a7
                  andi       a4, a4, -360
                  c.slli     s10, 18
                  lui        s11, 780535
                  nop
                  srli       t6, gp, 9
                  slt        t6, t2, a6
                  c.or       a1, a0
                  nop
                  c.xor      s0, a2
                  c.ebreak;c.nop;
                  c.and      a5, a3
                  and        t0, s7, s11
                  sltu       s5, a2, s6
                  c.beqz     a3, 881f
                  srl        a2, s5, t5
                  mulhu      tp, a5, a1
                  c.nop
                  mulhu      t5, s2, sp
                  c.or       a1, s0
881:              add        s5, sp, s2
                  srl        s6, a2, s11
                  c.and      a4, a5
                  c.nop
                  add        zero, t6, a0
                  srl        a5, t3, a5
                  sltu       ra, sp, s11
                  csrrw      s7, 0x340, a3
                  .4byte 0x00100073 # ebreak
                  mulhu      s1, s1, t0
                  and        t3, s8, t3
                  sltu       t0, t6, ra
                  auipc      a1, 938603
                  add        s4, s2, s0
                  c.mv       s2, a2
                  blt        a5, a2, 904f
                  csrrs      a0, 0x340, gp
                  ori        s2, t3, -620
                  andi       t6, s3, -571
                  div        a1, ra, a5
                  c.and      a2, a4
                  c.beqz     s0, 912f
                  sltiu      t3, a7, -243
904:              ori        ra, a4, 147
                  slti       a1, s6, 1008
                  c.srai     s1, 13
                  mul        a5, s2, zero
                  auipc      s1, 42370
                  slti       a4, s2, -825
                  mulhu      a7, t0, s5
                  c.lui      tp, 5
912:              csrrc      s3, 0x340, t4
                  xor        a0, t6, a7
                  c.slli     s10, 2
                  xor        zero, s1, a2
                  srli       zero, s7, 8
                  slti       t6, tp, 1021
                  remu       t4, a3, zero
                  mulhu      a3, s5, s3
                  xori       s7, t4, 680
                  slli       s5, s1, 1
                  csrrc      a1, 0x340, s9
                  csrrc      t5, 0x340, a0
                  csrrw      a1, 0x340, a6
                  mulhsu     gp, s7, t6
                  c.lui      t4, 29
                  slli       ra, s3, 6
                  c.addi     a2, -3
                  csrrwi     a2, 0x340, 3
                  c.and      a4, a5
                  csrrc      a6, 0x340, s10
                  csrrci     a2, 0x340, 26
                  srai       ra, t2, 23
                  nop
                  .4byte 0x00100073 # ebreak
                  blt        a5, a0, 938f
                  div        t6, s4, s3
938:              slt        s3, s10, t5
                  csrrci     t0, 0x340, 28
                  sltiu      s4, s7, 274
                  c.bnez     a1, 943f
                  c.mv       a5, t1
943:              slti       s11, zero, 911
                  mulh       t5, s3, a4
                  c.or       a5, a4
                  sltiu      a1, a4, -684
                  div        s7, t0, s2
                  divu       a6, t5, t2
                  beq        s9, s9, 968f
                  sltu       a1, t4, a4
                  csrrci     s10, 0x340, 20
                  c.bnez     a1, 964f
                  div        t6, s8, a5
                  srli       a1, a1, 15
                  mulhu      s1, s11, a6
                  c.srli     a4, 17
                  c.srli     a0, 13
                  andi       a7, s10, 715
                  sltu       a2, a0, sp
                  csrrw      a0, 0x340, t2
                  sltiu      a7, t0, -609
                  c.beqz     s0, 978f
                  c.lui      s6, 3
964:              c.ebreak;c.nop;
                  c.srai     a0, 18
                  csrrc      s7, 0x340, t3
                  csrrc      tp, 0x340, t4
968:              bne        t0, a6, 984f
                  mulhu      a1, t1, a2
                  c.li       s4, -26
                  ori        s1, t1, 444
                  srl        gp, t1, a0
                  srl        ra, s6, sp
                  auipc      t2, 414418
                  c.li       a4, 29
                  c.nop
                  div        a1, t3, s0
978:              sltu       t1, t4, ra
                  or         gp, t3, t2
                  c.nop
                  addi       t3, tp, 881
                  xori       s7, a3, -199
                  c.li       a5, 23
984:              c.bnez     a1, 1003f
                  sll        s7, s2, a0
                  c.sub      a3, a4
                  div        a0, a6, zero
                  add        s10, a4, t4
                  csrrc      a3, 0x340, s10
                  add        gp, s5, sp
                  or         gp, s5, a7
                  c.or       a3, a4
                  c.or       s1, a2
                  beq        t2, s3, 1002f
                  slli       t2, s0, 23
                  srli       s0, gp, 9
                  mul        a6, sp, a4
                  mul        s7, sp, s5
                  ori        a6, a3, -975
                  c.add      s1, a4
                  srl        s0, t3, t4
1002:             bge        zero, t3, 1014f
1003:             sll        t5, zero, ra
                  div        s6, a5, s0
                  c.sub      a4, a5
                  c.addi     t2, -15
                  andi       s6, a3, 418
                  csrrci     t5, 0x340, 18
                  bgeu       s9, t3, 1017f
                  rem        a5, tp, s11
                  mulhsu     t6, s0, a5
                  .4byte 0x00100073 # ebreak
                  andi       t5, t6, 694
1014:             csrrci     s7, 0x340, 0
                  c.andi     a1, -2
                  c.lui      s4, 21
1017:             c.sub      a4, s0
                  auipc      tp, 807402
                  csrrwi     s0, 0x340, 0
                  sra        s6, a4, t2
                  beq        t0, t4, 1029f
                  c.bnez     a2, 1042f
                  xori       s11, s7, 542
                  c.nop
                  divu       a0, sp, s2
                  c.srai     a0, 18
                  divu       a7, s0, s7
                  c.beqz     a3, 1044f
1029:             c.ebreak;c.nop;
                  and        tp, t5, s6
                  c.slli     a5, 9
                  sub        s5, t0, a7
                  blt        a2, a1, 1037f
                  c.mv       s5, s3
                  auipc      a0, 161399
                  slt        t6, s4, s8
1037:             mulhsu     tp, s7, a4
                  mulhu      a1, s1, a6
                  csrrc      ra, 0x340, t0
                  srli       t1, tp, 18
                  csrrci     a3, 0x340, 16
1042:             sra        a4, a1, s4
                  c.srai     a4, 11
1044:             slti       s3, gp, -185
                  slti       s6, t5, 980
                  c.srai     a5, 13
                  csrrsi     s0, 0x340, 13
                  mulhu      a2, tp, a0
                  srli       t2, a5, 28
                  sub        ra, a5, a0
                  or         s3, tp, a7
                  slli       t0, a0, 30
                  csrrci     a6, 0x340, 11
                  csrrci     s6, 0x340, 2
                  sltu       t2, s1, t1
                  rem        s3, t6, a2
                  mulh       gp, s6, a2
                  c.addi     t5, -25
                  rem        t1, t5, s7
                  beq        gp, t1, 1062f
                  mulh       a3, t6, s1
1062:             ori        t1, t6, 717
                  c.or       s0, a0
                  mulhsu     a1, s6, t5
                  csrrs      t1, 0x340, a1
                  mulhu      t4, s6, s3
                  div        t3, a2, t4
                  csrrwi     t0, 0x340, 28
                  mulhu      a6, t3, t5
                  mul        t6, s3, sp
                  rem        a1, gp, a4
                  c.slli     s11, 1
                  andi       s4, tp, -801
                  c.nop
                  csrrs      a4, 0x340, s4
                  divu       s5, a2, s9
                  blt        s2, t0, 1085f
                  c.mv       gp, a6
                  .4byte 0x00100073 # ebreak
                  c.and      a3, a3
                  remu       s4, s10, a7
                  xori       ra, s10, -967
                  bge        a7, t4, 1091f
                  bne        s11, a5, 1103f
1085:             lui        a5, 886186
                  xori       a6, s4, 988
                  mulh       s3, t4, s1
                  c.mv       tp, a2
                  c.srli     a0, 23
                  slti       a6, s3, -1008
1091:             c.addi     ra, -3
                  slti       t1, zero, 928
                  mulhu      zero, a5, s0
                  bne        t0, s10, 1113f
                  rem        s1, a7, sp
                  csrrs      a6, 0x340, t4
                  srai       s11, t2, 1
                  csrrw      t2, 0x340, s1
                  and        t6, a4, a0
                  c.srli     a3, 21
                  sra        gp, s6, sp
                  csrrwi     a1, 0x340, 9
1103:             csrrsi     t6, 0x340, 23
                  rem        s6, s4, t3
                  remu       s10, t5, s9
                  auipc      t1, 775217
                  remu       s6, s6, a7
                  lui        t3, 727793
                  c.andi     a2, -21
                  srai       s1, t4, 10
                  rem        a5, a7, s11
                  xor        t2, a4, a0
1113:             lui        a4, 606219
                  c.srai     a3, 14
                  sltu       s6, s7, s9
                  c.add      s3, s10
                  c.srai     a1, 24
                  bne        s4, zero, 1137f
                  sra        s0, s11, a1
                  csrrci     s5, 0x340, 26
                  csrrsi     a2, 0x340, 26
                  add        a6, s10, a7
                  c.andi     a1, -23
                  srl        s11, s8, a1
                  bge        s0, a0, 1133f
                  c.lui      s3, 3
                  slti       gp, zero, 49
                  mulh       t0, s11, a6
                  csrrci     gp, 0x340, 21
                  c.addi     t4, -6
                  c.addi     a0, 31
                  add        a7, s9, s4
1133:             c.xor      a5, a4
                  c.andi     a5, -12
                  csrrwi     s7, 0x340, 19
                  mulhsu     s4, t5, a7
1137:             xori       ra, t1, -222
                  sub        s11, s3, s2
                  bge        a6, a4, 1149f
                  bgeu       a2, s4, 1145f
                  c.addi     t4, 28
                  andi       zero, s3, -111
                  .4byte 0x00100073 # ebreak
                  c.sub      a0, s1
1145:             c.srli     a4, 24
                  csrrs      s10, 0x340, t2
                  c.slli     t1, 16
                  csrrc      a4, 0x340, t2
1149:             xor        t0, gp, a6
                  beq        s1, t4, 1152f
                  srai       s2, a7, 25
1152:             bge        s6, s0, 1160f
                  slli       s7, zero, 10
                  slti       t6, a5, -372
                  bltu       t5, a7, 1157f
                  addi       s6, t2, 990
1157:             or         s5, a1, t2
                  sll        s11, a1, a4
                  blt        sp, t5, 1173f
1160:             sll        t1, tp, s8
                  sra        s5, a5, s7
                  c.ebreak;c.nop;
                  sub        zero, a5, gp
                  c.nop
                  c.beqz     a3, 1178f
                  bgeu       a3, zero, 1180f
                  csrrwi     t5, 0x340, 0
                  c.addi     a2, -18
                  csrrs      a3, 0x340, s11
                  slti       s6, s10, 815
                  ori        gp, t1, -901
                  sll        a6, s11, a3
1173:             mulhu      s10, s6, a7
                  nop
                  csrrwi     a2, 0x340, 18
                  c.or       a5, a3
                  c.slli     a2, 7
1178:             c.mv       a2, t6
                  lui        t4, 530983
1180:             bne        s11, s9, 1188f
                  blt        a7, a5, 1193f
                  c.li       a0, -12
                  c.mv       s6, t3
                  sra        a5, t3, s1
                  csrrci     s10, 0x340, 4
                  mulh       t6, t3, s2
                  srl        t2, s8, s10
1188:             mulhu      ra, s10, s1
                  csrrci     a2, 0x340, 31
                  sub        s6, s2, a5
                  c.srli     a5, 26
                  ori        a5, s3, 422
1193:             c.bnez     a5, 1201f
                  slti       tp, a0, -207
                  blt        s6, ra, 1213f
                  sra        s0, gp, s4
                  lui        s11, 750459
                  csrrsi     t0, 0x340, 11
                  mulhu      a6, s4, t5
                  addi       t5, s11, 987
1201:             nop
                  or         s10, t2, s4
                  sra        t6, a7, t5
                  csrrc      s6, 0x340, a6
                  c.srai     a5, 27
                  auipc      s11, 995329
                  bgeu       t1, tp, 1219f
                  lui        a3, 823780
                  c.add      a5, s4
                  or         a5, a7, s7
                  mulh       s3, s0, a1
                  xori       s11, t1, -864
1213:             bge        t4, t6, 1219f
                  divu       a3, a0, a5
                  sltiu      a0, t6, 822
                  addi       a4, a2, 947
                  c.lui      s10, 27
                  c.srai     a2, 11
1219:             csrrc      a5, 0x340, s8
                  auipc      s3, 447586
                  csrrw      s4, 0x340, s11
                  ori        a5, s3, 892
                  sll        s3, s1, s1
                  srli       t1, sp, 29
                  srli       t1, t4, 5
                  lui        t3, 1009668
                  lui        a6, 756267
                  csrrc      t1, 0x340, s1
                  remu       s2, zero, ra
                  bne        s9, s6, 1250f
                  csrrsi     zero, 0x340, 25
                  bgeu       a6, a4, 1248f
                  auipc      t0, 721912
                  srl        s10, s11, gp
                  c.srai     a0, 17
                  c.bnez     a0, 1241f
                  xori       ra, a7, 331
                  csrrci     gp, 0x340, 5
                  xor        zero, t6, zero
                  srli       a0, s0, 18
1241:             mul        s2, t2, s4
                  c.addi     s0, -26
                  rem        ra, s10, a0
                  xor        zero, zero, a6
                  mulhu      ra, tp, tp
                  slli       s7, a0, 0
                  slli       s5, t2, 9
1248:             blt        a0, t5, 1260f
                  c.li       a1, 13
1250:             csrrw      t2, 0x340, a6
                  addi       a1, t0, 457
                  csrrwi     t4, 0x340, 18
                  rem        a3, s7, t3
                  remu       s2, s5, s1
                  auipc      a7, 118419
                  beq        sp, t3, 1260f
                  mulh       a3, s1, s0
                  c.andi     s1, 4
                  c.srai     a0, 22
1260:             c.ebreak;c.nop;
                  c.li       gp, 22
                  slt        s11, t0, t1
                  c.beqz     s0, 1269f
                  srli       tp, a3, 28
                  slli       ra, a0, 27
                  c.lui      t1, 16
                  or         s2, t2, s3
                  slt        a6, s5, a2
1269:             c.xor      a2, a4
                  c.mv       s5, t1
                  bne        s7, ra, 1276f
                  c.li       a5, 1
                  nop
                  and        s2, t2, a4
                  sll        tp, tp, tp
1276:             blt        sp, t4, 1288f
                  .4byte 0x00100073 # ebreak
                  andi       a2, s0, -702
                  remu       a1, s4, t0
                  slt        s6, a2, a4
                  csrrs      a7, 0x340, t6
                  nop
                  lui        s10, 528456
                  andi       t4, a6, -671
                  bne        s11, s3, 1305f
                  rem        a2, s4, a0
                  sltiu      s2, s10, 924
1288:             c.bnez     a1, 1294f
                  c.lui      s4, 24
                  c.ebreak;c.nop;
                  c.or       s0, a0
                  csrrci     gp, 0x340, 2
                  c.mv       s5, t3
                  la         a0, region_3+42 #start load_store_instr_stream_3
                  la         t3, region_0+852 #start load_store_instr_stream_4
                  la         s3, region_1+15818 #start load_store_instr_stream_1
                  la         s11, region_2+2019 #start load_store_instr_stream_2
                  sb         t0, -95(t3)
                  lb         a2, -60(s11)
                  la         a1, region_4+3209 #start load_store_instr_stream_0
                  lhu        a5, 180(t3)
                  sb         t4, 69(s3)
                  lb         a5, 105(s3)
                  sb         t3, -250(t3)
                  sb         tp, 28(s11)
                  lbu        s0, 49(a0)
                  lb         s1, -374(a1)
                  lw         t1, -244(t3)
                  sb         t2, -20(s11)
                  sb         a6, -186(t3)
                  lb         s0, -3(a0)
                  lbu        s2, -19(a0)
                  lb         s5, -241(s3)
                  lw         a2, -52(t3)
                  lhu        s4, 13(s11)
                  lb         t6, -220(t3)
                  sb         a1, 12(a0)
                  lb         a3, -63(t3) #end load_store_instr_stream_4
                  lbu        a6, 216(a1)
                  lb         a3, 44(s11)
                  lbu        a7, -466(a1)
                  lb         s2, -116(s3)
                  lbu        s1, 99(s3) #end load_store_instr_stream_1
                  lbu        t5, 566(a1)
                  sb         s0, -64(s11) #end load_store_instr_stream_2
                  lbu        a2, -27(a0) #end load_store_instr_stream_3
                  lb         a5, 484(a1) #end load_store_instr_stream_0
1294:             c.lui      s2, 4
                  c.or       a3, a5
                  c.li       t3, -25
                  sub        s5, s6, a1
                  slti       s0, s9, 368
                  and        s2, a1, s8
                  csrrwi     a2, 0x340, 10
                  slli       s3, s7, 2
                  sll        a6, a1, a4
                  c.and      s1, a2
                  c.add      a0, a2
1305:             sll        s7, gp, s3
                  c.sub      s0, a4
                  rem        a0, s10, s8
                  c.addi     a5, -26
                  bne        s1, a6, 1317f
                  srai       a0, t3, 4
                  csrrw      s3, 0x340, tp
                  lui        t0, 980678
                  c.mv       t3, a6
                  sll        s7, s2, gp
                  xor        s11, s5, s7
                  c.mv       s3, s1
1317:             slli       s7, s8, 2
                  sll        t5, s10, sp
                  mulh       t5, a5, t0
                  sltu       s5, s7, tp
                  or         t5, sp, ra
                  div        s7, t2, a2
                  slti       a3, a2, -5
                  sltu       gp, t4, s7
                  c.nop
                  and        tp, s3, s2
                  c.or       a3, a5
                  xori       s3, t3, -706
                  c.lui      t4, 14
                  c.andi     a0, 31
                  srai       s7, s9, 23
                  sltu       gp, s8, s1
                  c.slli     a4, 29
                  srli       s0, s10, 20
                  sub        t1, a6, s5
                  c.xor      s1, s0
                  add        s10, sp, s8
                  bne        a3, t5, 1351f
                  .4byte 0x00100073 # ebreak
                  andi       t0, zero, 311
                  andi       s3, t5, -178
                  nop
                  c.add      a4, sp
                  c.srai     a4, 28
                  nop
                  csrrwi     a6, 0x340, 25
                  mulhu      t2, a7, a1
                  addi       t0, s9, -858
                  sltu       t5, zero, t6
                  .4byte 0x00100073 # ebreak
1351:             lui        zero, 974384
                  c.srai     s1, 7
                  c.srli     a0, 4
                  srai       s10, s7, 17
                  slti       s2, s6, 215
                  slli       a4, s2, 17
                  c.slli     s5, 27
                  bne        s1, s8, 1362f
                  andi       tp, sp, 903
                  csrrwi     gp, 0x340, 6
                  csrrs      t6, 0x340, t6
1362:             csrrc      s1, 0x340, s9
                  divu       t6, gp, gp
                  div        gp, gp, a6
                  csrrw      s2, 0x340, a3
                  slti       t4, s8, -234
                  xori       t4, t1, -13
                  blt        t3, a5, 1374f
                  slli       a6, a3, 18
                  nop
                  auipc      s7, 731053
                  csrrsi     tp, 0x340, 31
                  csrrw      t4, 0x340, a2
1374:             xori       zero, s6, -323
                  slli       a1, s11, 23
                  beq        a5, t5, 1392f
                  beq        s8, t4, 1385f
                  lui        t2, 1028653
                  srli       t1, a0, 23
                  srli       a2, s10, 0
                  addi       t1, a3, -844
                  c.addi     tp, -30
                  bgeu       s11, gp, 1393f
                  and        t6, t3, s0
1385:             mulh       t0, s9, s0
                  csrrci     t4, 0x340, 23
                  mulh       s3, a1, t5
                  c.add      s10, s5
                  csrrc      ra, 0x340, s11
                  srai       zero, t6, 20
                  auipc      a7, 972982
1392:             ori        a6, s0, 478
1393:             auipc      a0, 1018773
                  remu       zero, s4, s10
                  rem        a2, s11, a5
                  srai       a3, s6, 7
                  c.addi     t6, -19
                  mul        t2, a0, t4
                  srli       t3, a4, 15
                  bltu       s7, s1, 1408f
                  beq        s2, zero, 1406f
                  c.mv       s6, a7
                  c.nop
                  blt        gp, a1, 1412f
                  .4byte 0x00100073 # ebreak
1406:             c.li       a5, 4
                  c.slli     s6, 14
1408:             blt        sp, t1, 1422f
                  bltu       a7, a5, 1421f
                  c.ebreak;c.nop;
                  sll        t0, s6, s6
1412:             c.sub      a1, s0
                  mulhu      s5, gp, a6
                  c.nop
                  bltu       s10, s3, 1417f
                  beq        gp, zero, 1436f
1417:             c.mv       s7, a1
                  csrrwi     s6, 0x340, 20
                  c.nop
                  xor        a1, a3, gp
1421:             c.and      a2, a0
1422:             c.xor      a5, s1
                  srli       a4, s7, 11
                  add        s4, a3, a4
                  srl        a6, s9, s10
                  and        tp, s4, t6
                  blt        s7, tp, 1446f
                  sll        a1, t5, a2
                  .4byte 0x00100073 # ebreak
                  and        a2, s9, s9
                  xori       s10, ra, 666
                  c.xor      s1, a4
                  c.addi     s5, 1
                  slt        s0, t6, tp
                  addi       gp, zero, -508
1436:             divu       a0, a0, a3
                  srai       a6, a7, 5
                  csrrs      a2, 0x340, a2
                  slti       a4, a1, -739
                  c.beqz     a0, 1444f
                  div        a1, a3, t6
                  mulhu      ra, tp, s6
                  addi       s2, t0, -849
1444:             remu       s7, a3, a0
                  .4byte 0x00100073 # ebreak
1446:             slt        t3, t3, s8
                  slti       a4, a5, -577
                  csrrci     gp, 0x340, 23
                  remu       t3, a1, a6
                  c.or       a1, a1
                  c.beqz     a3, 1453f
                  addi       t1, gp, -554
1453:             c.and      a2, a0
                  sltu       t6, gp, sp
                  c.sub      a2, a0
                  csrrw      a3, 0x340, s4
                  c.addi     s7, 13
                  slli       s1, a1, 21
                  mulhsu     zero, t5, t0
                  ori        a5, s10, -463
                  bltu       a7, a5, 1479f
                  c.li       t5, 3
                  sll        s10, a5, s1
                  c.and      a2, a5
                  c.xor      a2, s1
                  bne        s3, a0, 1468f
                  and        a7, t4, zero
1468:             c.add      s11, a4
                  sll        gp, s5, t1
                  csrrci     a0, 0x340, 16
                  c.li       s4, 25
                  sltiu      a3, s6, 417
                  c.mv       s11, s8
                  c.bnez     a2, 1486f
                  sub        t2, ra, a3
                  csrrci     zero, 0x340, 25
                  srai       a5, s6, 7
                  sll        s3, s6, s8
1479:             beq        t0, s8, 1495f
                  nop
                  sub        s10, a7, s1
                  bgeu       tp, s1, 1490f
                  addi       a7, t0, -771
                  beq        tp, t1, 1498f
                  sll        s5, s3, t0
1486:             xori       s0, a6, -354
                  c.nop
                  csrrwi     gp, 0x340, 8
                  slli       s2, a4, 9
1490:             c.xor      s1, s0
                  bge        s6, s6, 1499f
                  c.bnez     a5, 1511f
                  c.addi     ra, -9
                  bne        a0, sp, 1513f
1495:             or         s3, s4, a2
                  c.sub      a3, a3
                  slt        a6, s4, a0
1498:             sll        a7, a0, a1
1499:             bge        s2, t2, 1507f
                  csrrw      s6, 0x340, s10
                  lui        t6, 306045
                  c.beqz     a4, 1510f
                  rem        a5, a5, s9
                  and        a5, s4, s0
                  c.srai     a1, 2
                  mulhu      a6, a0, gp
1507:             srl        t0, s4, s3
                  andi       t2, a0, -416
                  sltiu      gp, gp, -670
1510:             c.li       s2, -8
1511:             .4byte 0x00100073 # ebreak
                  bltu       t4, a2, 1518f
1513:             c.addi     s5, -31
                  blt        a3, t1, 1518f
                  c.li       ra, -23
                  bne        t2, t0, 1528f
                  csrrw      zero, 0x340, a1
1518:             c.ebreak;c.nop;
                  slti       a7, zero, 317
                  c.lui      s3, 31
                  c.li       s4, -27
                  slt        s5, t6, s4
                  csrrsi     t1, 0x340, 5
                  and        t2, a2, tp
                  addi       tp, a5, 836
                  beq        t0, s7, 1538f
                  andi       gp, ra, -398
1528:             c.slli     t4, 2
                  slt        t2, t0, s3
                  c.beqz     a3, 1548f
                  bge        t6, s9, 1539f
                  slli       t6, t2, 7
                  c.and      a3, a5
                  csrrwi     t3, 0x340, 10
                  csrrc      t2, 0x340, s10
                  srl        s7, s2, s7
                  c.li       a2, -30
1538:             csrrs      ra, 0x340, gp
1539:             mul        s6, gp, t3
                  c.bnez     a4, 1559f
                  c.ebreak;c.nop;
                  div        s6, s11, s5
                  c.or       a3, a4
                  c.lui      t0, 7
                  c.beqz     s1, 1549f
                  c.mv       a2, s2
                  sll        t0, ra, a5
1548:             auipc      t0, 477002
1549:             c.add      t1, s2
                  c.li       a5, 21
                  srai       s6, a1, 25
                  beq        t0, s2, 1554f
                  sll        s2, t3, a0
1554:             csrrsi     t5, 0x340, 11
                  csrrwi     t6, 0x340, 9
                  slti       t4, t3, -881
                  div        tp, s7, s6
                  c.srai     a4, 18
1559:             mulhu      s5, a1, a0
                  sltu       a6, s3, a2
                  lui        ra, 139249
                  csrrsi     s5, 0x340, 10
                  .4byte 0x00100073 # ebreak
                  c.and      a5, a2
                  .4byte 0x00100073 # ebreak
                  srli       a5, ra, 2
                  sub        t3, s10, t4
                  c.slli     a7, 23
                  c.li       a0, 5
                  rem        s7, s8, t1
                  csrrwi     s1, 0x340, 0
                  slli       s0, s4, 18
                  blt        t6, t0, 1583f
                  la         s4, region_1+15360 #start load_store_instr_stream_2
                  la         t6, region_1+2522 #start load_store_instr_stream_1
                  la         a1, region_1+10669 #start load_store_instr_stream_0
                  lh         s10, -62(s4)
                  lw         s3, -56(s4)
                  lb         s1, -13(a1)
                  lb         s6, 18(s4)
                  lw         a0, -938(t6)
                  lbu        a5, -165(t6)
                  sb         t3, 23(s4)
                  lbu        a7, -57(a1)
                  lw         t5, -862(t6)
                  lb         a5, -577(t6)
                  lhu        tp, -49(a1)
                  sb         a0, -877(t6)
                  sh         zero, 14(s4) #end load_store_instr_stream_2
                  sb         a2, 639(t6)
                  lbu        t2, 41(t6)
                  lhu        a5, 27(a1)
                  sb         a5, -158(t6)
                  lbu        ra, 836(t6)
                  sb         a6, -25(t6) #end load_store_instr_stream_1
                  lbu        s1, 22(a1) #end load_store_instr_stream_0
                  csrrci     s7, 0x340, 10
                  addi       t0, t2, 539
                  mul        s5, s3, t3
                  c.andi     a1, 19
                  c.xor      s1, s0
                  srli       a2, s0, 1
                  csrrc      t5, 0x340, t5
                  csrrc      a5, 0x340, a4
                  .4byte 0x00100073 # ebreak
1583:             addi       s7, s3, 29
                  csrrw      s0, 0x340, t3
                  nop
                  auipc      a0, 935182
                  csrrc      a7, 0x340, s2
                  bne        t0, s6, 1596f
                  divu       gp, s11, zero
                  c.addi     a3, -30
                  srl        t5, s0, s5
                  mulhsu     s11, t4, ra
                  nop
                  sll        a5, s9, s9
                  c.lui      s5, 16
1596:             c.li       s10, 10
                  c.mv       tp, s3
                  sll        s11, s9, s0
                  mulhu      t0, sp, t6
                  addi       t0, t5, 481
                  sltiu      s6, a5, 639
                  or         s10, s8, t2
                  c.bnez     a1, 1617f
                  csrrsi     a6, 0x340, 29
                  c.bnez     s1, 1613f
                  srai       a0, tp, 21
                  mulhu      s7, s6, s0
                  srl        t2, t1, s2
                  remu       ra, s1, s11
                  csrrci     t0, 0x340, 20
                  srl        s10, t4, s8
                  c.sub      a3, a5
1613:             c.mv       t5, t0
                  c.andi     s1, 21
                  slt        s1, t5, a2
                  c.li       s6, 28
1617:             xori       t2, a4, -699
                  srl        a7, a3, tp
                  csrrwi     t1, 0x340, 20
                  sll        a3, s8, zero
                  mulh       s11, zero, t2
                  mulhu      t3, s7, s1
                  bge        s4, a6, 1625f
                  slt        s4, a2, t2
1625:             or         a5, t0, s6
                  c.bnez     a0, 1632f
                  c.nop
                  c.mv       a4, s9
                  slli       s4, s9, 3
                  sub        a7, s6, ra
                  bgeu       s8, a7, 1647f
1632:             c.slli     a2, 27
                  andi       s0, s10, 24
                  csrrc      a3, 0x340, s6
                  div        a7, t0, t4
                  rem        zero, s8, s2
                  mulhu      ra, gp, a6
                  bne        a2, a4, 1652f
                  xor        t6, t5, s11
                  csrrwi     s1, 0x340, 28
                  c.li       a2, -6
                  csrrw      s5, 0x340, s7
                  c.beqz     a0, 1648f
                  andi       s1, s6, 471
                  srli       t5, t3, 0
                  xor        a1, s5, tp
1647:             sltu       s7, s3, s1
1648:             c.lui      a3, 10
                  c.ebreak;c.nop;
                  addi       a2, gp, -368
                  divu       gp, s7, s8
1652:             slti       t4, s2, 950
                  auipc      s7, 809965
                  div        a0, a5, t1
                  c.xor      s1, s1
                  bne        t5, s11, 1669f
                  blt        gp, s0, 1677f
                  c.andi     s1, 19
                  c.xor      a3, a0
                  c.xor      a3, a2
                  blt        t3, a6, 1680f
                  remu       a2, s1, s3
                  c.li       t4, 1
                  mulh       a5, t4, t4
                  remu       s5, s0, zero
                  csrrwi     s1, 0x340, 12
                  slti       gp, a5, 972
                  csrrsi     t5, 0x340, 2
1669:             slti       a0, a4, 704
                  bgeu       tp, tp, 1682f
                  divu       s7, s10, s10
                  sra        t5, t5, t1
                  csrrs      s4, 0x340, a6
                  slti       a2, a6, -219
                  nop
                  c.bnez     a4, 1695f
1677:             c.lui      s11, 4
                  sltu       s6, s8, s11
                  rem        s6, t5, zero
1680:             c.bnez     s0, 1688f
                  csrrsi     s10, 0x340, 30
1682:             c.slli     ra, 30
                  c.or       s0, a4
                  mulhu      s0, a2, s6
                  srl        t4, gp, s0
                  csrrs      s10, 0x340, s11
                  csrrs      tp, 0x340, s7
1688:             slti       t4, t4, 643
                  divu       a2, s2, a7
                  c.lui      gp, 27
                  andi       s5, a7, -464
                  sltu       t4, a0, zero
                  mul        t4, t2, s2
                  div        s7, a4, a1
1695:             xor        t6, s2, a2
                  c.and      a5, a1
                  and        t5, a2, t1
                  csrrwi     s3, 0x340, 27
                  c.andi     a1, -24
                  mulhu      a2, t0, t3
                  mulhsu     t4, a6, tp
                  xori       s7, a5, -30
                  bltu       s9, s5, 1705f
                  rem        s1, s2, gp
1705:             bltu       sp, gp, 1721f
                  addi       t1, s9, -14
                  mulh       s11, a3, a1
                  mul        s11, s4, ra
                  csrrci     s11, 0x340, 2
                  divu       zero, s11, t1
                  c.nop
                  .4byte 0x00100073 # ebreak
                  addi       a7, t1, 857
                  c.bnez     a1, 1719f
                  c.lui      a5, 12
                  c.add      a2, t6
                  mulh       a3, a6, t1
                  ori        a6, a0, 655
1719:             c.bnez     a5, 1739f
                  c.bnez     a3, 1734f
1721:             c.lui      a6, 27
                  slti       a6, t0, -580
                  sra        t2, s3, s2
                  rem        a2, zero, tp
                  mulhu      t5, a0, t5
                  slli       s0, gp, 13
                  c.nop
                  mulhsu     gp, sp, a0
                  sll        s0, s10, t3
                  nop
                  ori        a3, s9, -748
                  csrrsi     s11, 0x340, 24
                  mulh       t6, s4, s9
1734:             nop
                  and        gp, a1, s1
                  slti       s2, s10, -351
                  c.nop
                  c.addi     t3, -9
1739:             c.bnez     a1, 1743f
                  csrrw      t5, 0x340, s0
                  bne        zero, sp, 1745f
                  csrrsi     t0, 0x340, 3
1743:             c.addi     t3, 26
                  sub        s1, s2, t2
1745:             c.nop
                  csrrwi     t6, 0x340, 19
                  csrrsi     a0, 0x340, 21
                  sra        a3, s2, s7
                  mul        a1, t1, s3
                  c.ebreak;c.nop;
                  sub        s0, a7, a3
                  div        a3, s10, s0
                  beq        s11, s2, 1772f
                  blt        s1, s3, 1760f
                  nop
                  mul        a7, s9, s0
                  and        s2, s0, a7
                  srl        s3, sp, t3
                  c.sub      a3, a5
1760:             andi       gp, gp, -557
                  .4byte 0x00100073 # ebreak
                  c.or       s1, a0
                  slli       t4, t3, 27
                  sltiu      s4, s4, -147
                  srl        a3, t4, s10
                  c.slli     s5, 19
                  slti       s3, s0, -546
                  c.lui      s2, 17
                  nop
                  csrrsi     a7, 0x340, 16
                  c.andi     a2, 15
1772:             slti       s5, s7, 713
                  xori       s11, s7, -31
                  blt        t4, s4, 1782f
                  lui        gp, 721957
                  bltu       a6, a2, 1784f
                  c.xor      a0, a0
                  c.nop
                  andi       s6, s0, 319
                  csrrci     s11, 0x340, 20
                  c.andi     a0, 12
1782:             c.and      s0, a2
                  c.andi     s1, -3
1784:             nop
                  beq        t3, s10, 1798f
                  mulhu      s10, t4, t5
                  beq        s11, a1, 1789f
                  bltu       ra, gp, 1804f
1789:             bgeu       a3, a3, 1801f
                  srai       t1, t1, 31
                  auipc      a7, 639153
                  mulhsu     t5, s0, a4
                  remu       s5, t2, t1
                  c.beqz     a0, 1813f
                  srai       ra, a0, 10
                  csrrc      tp, 0x340, tp
                  xor        s7, t4, s9
1798:             srli       t5, t4, 6
                  csrrc      zero, 0x340, a2
                  csrrw      a6, 0x340, a6
1801:             csrrci     a0, 0x340, 17
                  sra        a6, a7, s3
                  auipc      s7, 847017
1804:             rem        a6, s4, t3
                  srli       s2, a2, 5
                  nop
                  remu       a2, s4, s11
                  addi       s1, s7, 899
                  slt        t2, s2, a2
                  remu       t6, s2, a2
                  mul        a0, s9, t1
                  mul        zero, t6, s6
1813:             sub        t4, s4, t4
                  div        a3, s4, gp
                  sll        s1, t0, zero
                  c.addi     s11, 2
                  slt        a6, s11, t0
                  c.add      a0, t1
                  csrrsi     t3, 0x340, 31
                  c.add      s3, s11
                  c.bnez     a1, 1837f
                  csrrci     t2, 0x340, 9
                  c.xor      a0, s1
                  blt        a0, a4, 1838f
                  c.xor      a2, a0
                  c.bnez     s0, 1846f
                  rem        s2, s9, t3
                  slli       s11, t2, 29
                  c.lui      s6, 7
                  sub        t1, a2, gp
                  andi       t0, a1, 860
                  bge        s11, s6, 1850f
                  xor        s11, a1, a5
                  or         s5, t4, t4
                  mulh       a5, a0, t4
                  c.beqz     a5, 1844f
1837:             c.or       a4, a1
1838:             c.addi     tp, 12
                  c.sub      a4, s0
                  bne        t6, a4, 1860f
                  .4byte 0x00100073 # ebreak
                  c.beqz     a1, 1850f
                  csrrsi     s0, 0x340, 28
1844:             csrrs      s2, 0x340, s3
                  c.mv       a2, a1
1846:             sltu       t3, s2, s0
                  xor        s1, s7, t6
                  srli       gp, t5, 16
                  slti       t5, a5, 553
1850:             mulh       a3, t5, t5
                  csrrwi     gp, 0x340, 30
                  csrrc      s1, 0x340, t4
                  srli       a6, s4, 10
                  blt        s7, t2, 1859f
                  csrrsi     s11, 0x340, 29
                  mulh       s10, s11, s7
                  c.mv       s11, s0
                  c.addi     a4, -26
1859:             c.srai     s0, 12
1860:             c.mv       s4, s11
                  lui        a0, 955192
                  bge        s2, s0, 1868f
                  csrrsi     a0, 0x340, 28
                  csrrwi     s11, 0x340, 11
                  sll        a1, t4, s7
                  csrrc      t3, 0x340, a5
                  c.srli     a2, 8
1868:             c.xor      a3, a4
                  add        s7, a6, a7
                  add        a5, a3, a1
                  srai       ra, s5, 13
                  beq        a3, ra, 1884f
                  csrrsi     a5, 0x340, 6
                  c.or       a3, a4
                  sra        a1, s10, s9
                  xori       zero, s1, 792
                  sub        zero, a5, s11
                  bgeu       s7, a2, 1886f
                  remu       s1, ra, a5
                  bge        gp, t5, 1890f
                  bgeu       t2, s4, 1893f
                  c.addi     t3, -26
                  and        t2, s10, a6
1884:             sub        t3, t5, gp
                  andi       a3, s9, -726
1886:             .4byte 0x00100073 # ebreak
                  c.sub      a1, a2
                  slt        a4, a6, a3
                  c.andi     s0, -1
1890:             nop
                  sra        a1, s1, t2
                  c.andi     a3, -4
1893:             srli       s4, t2, 17
                  srli       t5, a6, 4
                  div        a2, a2, ra
                  sltu       s1, s10, s8
                  divu       a7, t6, s11
                  slli       t0, a5, 24
                  csrrci     t4, 0x340, 10
                  div        s2, s6, gp
                  xori       a7, a2, 96
                  csrrci     tp, 0x340, 16
                  nop
                  c.and      a4, a4
                  and        s3, s4, gp
                  sub        tp, s2, a0
                  sltu       s0, s4, s11
                  csrrs      s10, 0x340, a1
                  sll        t6, a1, s11
                  c.li       a5, -14
                  nop
                  rem        s2, a2, zero
                  c.bnez     a1, 1918f
                  csrrc      zero, 0x340, a2
                  csrrc      t0, 0x340, s11
                  slli       gp, s9, 29
                  csrrs      t6, 0x340, s5
1918:             mul        s1, sp, t5
                  andi       s5, s10, -959
                  addi       a7, s9, -658
                  csrrs      t5, 0x340, a4
                  c.xor      a2, a2
                  xori       t1, s11, 153
                  sra        t1, s2, ra
                  csrrsi     s7, 0x340, 7
                  csrrs      a1, 0x340, s11
                  c.ebreak;c.nop;
                  csrrw      t5, 0x340, a2
                  csrrwi     s5, 0x340, 13
                  nop
                  mulh       t3, t0, s8
                  sra        ra, s9, t6
                  c.bnez     a4, 1935f
                  blt        tp, a3, 1936f
1935:             c.ebreak;c.nop;
1936:             c.or       a2, a5
                  mulhu      t0, s5, zero
                  mulh       s4, a6, s4
                  auipc      a6, 35214
                  c.or       a3, s0
                  nop
                  and        a5, t0, a7
                  slli       a5, t2, 7
                  sra        a1, a0, tp
                  srl        a6, t0, a4
                  bgeu       a4, t1, 1954f
                  c.addi     s3, -19
                  c.nop
                  c.srai     a2, 2
                  mul        s4, t2, t3
                  sltu       t4, t3, tp
                  c.and      a1, a2
                  c.srli     a1, 1
1954:             c.slli     s4, 17
                  csrrci     s3, 0x340, 1
                  slti       s7, t6, 462
                  csrrci     s11, 0x340, 2
                  csrrsi     t6, 0x340, 16
                  csrrsi     s3, 0x340, 29
                  divu       s11, a6, a6
                  csrrw      s7, 0x340, s10
                  rem        a2, s10, t6
                  sltiu      tp, t1, 561
                  c.addi     tp, 16
                  sra        a5, t5, s1
                  xor        a3, s0, s4
                  .4byte 0x00100073 # ebreak
                  mul        s6, a7, a0
                  c.lui      t6, 3
                  c.srli     a4, 17
                  and        tp, a3, t3
                  c.addi     s1, 30
                  csrrc      a2, 0x340, a5
                  srl        a3, s4, a5
                  sltu       s2, s1, t0
                  c.srai     a2, 13
                  mul        s6, s2, t0
                  c.andi     s0, -19
                  sltiu      a7, s9, -884
                  sll        t5, a3, s7
                  c.srai     a3, 26
                  andi       a6, tp, 798
                  c.addi     s1, -16
                  csrrs      a7, 0x340, t6
                  c.bnez     s1, 2004f
                  c.andi     s1, 6
                  sltiu      t5, a2, 786
                  auipc      s1, 869020
                  rem        s11, t6, a7
                  bne        s5, t5, 2010f
                  c.add      s6, a4
                  c.mv       s7, s11
                  mulh       a3, tp, a7
                  c.or       a1, s0
                  mulhu      t4, s3, zero
                  mul        s11, s6, s0
                  csrrwi     a1, 0x340, 8
                  c.srai     s1, 28
                  andi       t0, t4, -893
                  c.ebreak;c.nop;
                  ori        gp, s4, -570
                  bge        a3, a5, 2008f
                  mulhsu     s3, a7, t1
2004:             c.srai     a5, 3
                  c.add      s6, a1
                  bne        t6, s11, 2008f
                  xor        a3, t1, sp
2008:             rem        s6, sp, a3
                  div        s1, s6, a0
2010:             c.andi     s1, -16
                  c.and      a1, a3
                  c.andi     a1, -31
                  c.andi     a4, 0
                  c.add      s4, t5
                  ori        a3, s1, 96
                  beq        a2, t4, 2021f
                  slti       a4, t1, 528
                  and        t0, a2, t5
                  c.srli     s1, 26
                  c.srli     a2, 27
2021:             srli       t1, s6, 20
                  c.srli     a5, 23
                  mulhsu     a7, sp, t5
                  mulhu      t3, a6, t0
                  xor        a6, t6, ra
                  bgeu       s5, t4, 2046f
                  c.bnez     a3, 2039f
                  c.nop
                  bne        s1, ra, 2043f
                  and        s2, tp, s1
                  csrrs      s1, 0x340, gp
                  sltiu      a4, a5, -365
                  c.beqz     a1, 2052f
                  c.sub      a3, a1
                  csrrw      t5, 0x340, t5
                  c.lui      s11, 5
                  remu       s2, s3, t5
                  bltu       a0, a2, 2054f
2039:             slli       a4, ra, 30
                  .4byte 0x00100073 # ebreak
                  c.mv       s1, s10
                  mul        t1, a7, s1
2043:             bne        s5, s10, 2045f
                  c.beqz     a0, 2048f
2045:             bltu       zero, s2, 2053f
2046:             c.srli     s1, 7
                  c.slli     a1, 6
2048:             nop
                  andi       t0, s3, -421
                  c.srai     a0, 6
                  addi       a0, s8, 471
2052:             xor        s4, sp, ra
2053:             ori        s3, s4, -11
2054:             csrrwi     s11, 0x340, 5
                  c.sub      s0, s0
                  c.mv       t6, s4
                  sll        t1, a1, ra
                  csrrc      s10, 0x340, zero
                  srai       ra, t5, 7
                  sltiu      s4, t6, 430
                  bge        t6, s8, 2063f
                  csrrwi     a0, 0x340, 1
2063:             csrrs      t0, 0x340, t3
                  csrrw      s6, 0x340, s3
                  lui        s0, 31833
                  nop
                  c.andi     a3, 10
                  srl        t2, s10, s4
                  div        a7, tp, s8
                  c.nop
                  c.nop
                  csrrsi     ra, 0x340, 23
                  mulh       a6, s10, t4
                  sll        t1, gp, a1
                  addi       t3, t1, -725
                  xori       s5, s1, -324
                  and        t5, a5, s3
                  sra        t6, s7, s10
                  xori       a2, a7, 511
                  bge        zero, s9, 2085f
                  c.beqz     a2, 2099f
                  mulhu      a4, a2, s0
                  bgeu       s8, s1, 2102f
                  divu       a4, s3, t6
2085:             sltu       s1, t3, a7
                  addi       s0, a4, 451
                  beq        tp, gp, 2101f
                  mulh       zero, t6, s5
                  c.andi     a1, -4
                  slt        s7, a1, a2
                  nop
                  c.xor      a3, a2
                  sltu       s4, a1, s10
                  divu       a2, tp, t3
                  c.srli     a1, 27
                  c.beqz     a4, 2102f
                  sltiu      a5, s8, -170
                  remu       a6, gp, t3
2099:             or         ra, sp, tp
                  slti       a4, s7, 752
2101:             rem        s2, t5, s4
2102:             blt        sp, t6, 2110f
                  slti       s10, gp, 336
                  and        ra, t5, s9
                  c.slli     a1, 10
                  srai       t3, t4, 13
                  bltu       t1, s9, 2126f
                  c.nop
                  srl        s6, s6, t3
2110:             mulhsu     s4, a0, t4
                  bge        a5, a4, 2115f
                  c.andi     s0, 15
                  blt        s8, t4, 2121f
                  srai       s11, sp, 25
2115:             and        s7, s5, a0
                  beq        s4, t2, 2124f
                  csrrsi     s10, 0x340, 18
                  csrrc      s7, 0x340, t2
                  c.srli     a2, 4
                  c.sub      a3, s1
2121:             rem        s11, t3, s1
                  c.ebreak;c.nop;
                  bltu       t4, t5, 2135f
2124:             lui        s2, 462320
                  c.beqz     a3, 2138f
2126:             c.mv       a6, t3
                  csrrw      t5, 0x340, t3
                  remu       s10, s8, t1
                  lui        t0, 558719
                  slli       t0, ra, 2
                  csrrci     a1, 0x340, 24
                  c.nop
                  c.nop
                  xori       t2, t6, 908
2135:             ori        a0, s8, 141
                  c.or       a3, a1
                  mulhsu     t5, a1, a0
2138:             slli       s3, gp, 26
                  lui        s6, 467426
                  sltu       a3, a3, t0
                  or         a3, a1, a7
                  c.ebreak;c.nop;
                  beq        t0, sp, 2155f
                  c.srli     a2, 17
                  sll        a5, s4, a3
                  c.addi     t4, -10
                  slt        zero, t0, s1
                  c.sub      a2, a4
                  c.addi     s5, -9
                  .4byte 0x00100073 # ebreak
                  c.mv       t6, t2
                  slt        t5, a6, a1
                  lui        t4, 468730
                  .4byte 0x00100073 # ebreak
2155:             addi       t2, s6, -904
                  xori       a5, ra, 993
                  bge        s7, ra, 2165f
                  c.and      s1, s0
                  c.and      a5, s0
                  sra        a4, a7, zero
                  c.ebreak;c.nop;
                  nop
                  csrrwi     s10, 0x340, 20
                  sltu       s6, a0, a4
2165:             sltu       t4, a7, s7
                  bne        a6, a5, 2182f
                  c.srli     a4, 9
                  addi       s1, t3, 914
                  c.lui      s1, 10
                  rem        t3, t1, s7
                  slti       s1, s6, 897
                  c.sub      a1, a5
                  blt        s9, s4, 2183f
                  srl        t1, t0, s1
                  c.andi     s1, -29
                  .4byte 0x00100073 # ebreak
                  c.and      a4, a4
                  sra        s0, a7, t3
                  blt        gp, s4, 2187f
                  sltu       s4, s5, s10
                  slt        s1, s11, gp
2182:             mulhsu     t0, t0, a7
2183:             andi       t0, s3, 780
                  mulhu      s0, a2, a4
                  divu       a0, s3, s10
                  c.addi     a4, 4
2187:             beq        a5, s11, 2195f
                  c.slli     a3, 3
                  c.slli     s0, 15
                  mulhu      tp, s1, gp
                  c.ebreak;c.nop;
                  bge        s10, a1, 2212f
                  c.slli     s0, 11
                  c.addi     s4, 19
2195:             c.xor      a1, a4
                  div        s11, zero, t5
                  bge        zero, t5, 2205f
                  c.and      a2, a3
                  c.lui      a5, 4
                  c.srli     a1, 14
                  remu       a0, gp, ra
                  c.lui      a1, 11
                  divu       a1, a5, zero
                  xor        s1, a6, s0
2205:             div        ra, s11, a0
                  c.xor      a0, a5
                  lui        a0, 935979
                  sll        zero, a5, s4
                  blt        s3, a5, 2222f
                  csrrs      zero, 0x340, t1
                  bne        a6, a7, 2219f
2212:             mulhu      s4, gp, s0
                  or         a4, sp, t1
                  lui        a0, 76271
                  slt        s5, s0, s4
                  srli       t6, a3, 5
                  slt        s10, a7, t0
                  c.nop
2219:             bne        a3, ra, 2231f
                  c.or       a1, a5
                  c.beqz     a4, 2233f
2222:             mul        s3, s0, s5
                  c.add      s1, a6
                  csrrc      a4, 0x340, tp
                  c.and      a4, a4
                  c.lui      gp, 30
                  c.li       t0, -5
                  mulhu      t4, s2, sp
                  auipc      s2, 202567
                  blt        s1, t0, 2246f
2231:             c.add      t3, a7
                  csrrci     a3, 0x340, 10
2233:             csrrw      a7, 0x340, s10
                  bge        s0, t1, 2236f
                  c.lui      t5, 21
2236:             xori       a3, a4, -698
                  bltu       t4, s9, 2249f
                  sltu       s7, a1, zero
                  xor        gp, zero, t6
                  c.lui      a1, 21
                  slti       a1, s5, -914
                  divu       s11, a4, s0
                  c.slli     a5, 21
                  c.mv       s4, a1
                  c.xor      a1, s0
2246:             and        gp, s5, s0
                  mul        s6, s0, s7
                  c.ebreak;c.nop;
2249:             srli       s3, s3, 16
                  slti       a5, t1, 661
                  remu       s6, s9, zero
                  bgeu       s7, s9, 2254f
                  c.nop
2254:             add        a0, s4, s7
                  sltiu      t6, sp, 678
                  mulhu      a4, ra, a7
                  c.mv       s7, t3
                  auipc      ra, 363600
                  xori       s6, t1, 927
                  csrrwi     s10, 0x340, 28
                  c.ebreak;c.nop;
                  sra        a3, t0, a7
                  slti       ra, a3, -665
                  andi       t4, ra, 206
                  csrrw      t1, 0x340, s7
                  bgeu       s7, a2, 2282f
                  bge        s4, a3, 2286f
                  mulhu      t3, s8, a7
                  csrrs      t5, 0x340, s7
                  auipc      s1, 106261
                  csrrc      s0, 0x340, t3
                  slli       a7, s10, 28
                  beq        a0, t4, 2279f
                  c.addi     a6, -24
                  slli       t3, s1, 20
                  addi       s2, zero, 520
                  c.xor      s0, a3
                  c.beqz     a5, 2298f
2279:             auipc      s1, 334252
                  c.lui      a0, 15
                  c.sub      a0, s1
2282:             c.nop
                  c.srai     a0, 5
                  bne        t2, t6, 2294f
                  csrrw      a6, 0x340, a6
2286:             c.sub      a5, a3
                  c.bnez     s1, 2306f
                  and        a7, t5, t3
                  c.addi     s11, -12
                  remu       ra, s4, a3
                  sra        t2, t3, t6
                  sll        gp, gp, s11
                  add        a0, t5, tp
2294:             c.lui      a0, 12
                  mul        t0, s8, s0
                  divu       s3, ra, a4
                  nop
2298:             beq        a2, ra, 2300f
                  add        t6, t2, a3
2300:             addi       s0, s4, 827
                  c.mv       t3, sp
                  c.ebreak;c.nop;
                  c.li       s4, -12
                  rem        tp, t3, a7
                  nop
2306:             sra        s0, s9, s7
                  c.ebreak;c.nop;
                  .4byte 0x00100073 # ebreak
                  c.bnez     a3, 2323f
                  andi       a4, s5, -367
                  c.lui      s6, 1
                  remu       s11, s2, s9
                  c.xor      a5, s1
                  mulhu      t6, s1, s11
                  and        a5, a1, a1
                  remu       s2, sp, s1
                  ori        t6, t5, -581
                  divu       s11, s4, s3
                  c.lui      gp, 22
                  xor        a7, s2, s8
                  c.lui      a0, 22
                  xori       t3, s6, -764
2323:             c.or       a3, s0
                  c.li       a7, -2
                  addi       a1, t3, 560
                  andi       t6, zero, -145
                  slt        t0, ra, tp
                  csrrci     t1, 0x340, 0
                  divu       s4, t4, t6
                  .4byte 0x00100073 # ebreak
                  ori        t6, zero, -248
                  andi       t1, t5, -661
                  div        t3, a2, t0
                  xor        a1, a5, a7
                  c.beqz     s1, 2349f
                  addi       s4, ra, -369
                  div        ra, s2, s10
                  c.srli     a2, 10
                  slti       s1, s2, 1009
                  sltiu      ra, s1, 414
                  or         t0, a1, a0
                  c.xor      a2, a0
                  bne        a1, a2, 2361f
                  srai       s6, tp, 28
                  sll        s7, s7, t5
                  div        a0, ra, a2
                  csrrsi     t6, 0x340, 18
                  c.srli     a1, 31
2349:             c.mv       t1, gp
                  bltu       zero, zero, 2369f
                  div        tp, s4, t1
                  srli       s7, sp, 22
                  c.ebreak;c.nop;
                  c.nop
                  divu       zero, t6, t2
                  sltu       a3, a5, a6
                  c.srai     a5, 24
                  .4byte 0x00100073 # ebreak
                  nop
                  c.sub      a3, a1
2361:             mul        t3, a3, sp
                  mulhu      t0, ra, s7
                  c.lui      a2, 20
                  c.lui      gp, 28
                  c.slli     s1, 9
                  c.xor      a1, a5
                  c.srli     a3, 22
                  c.add      a6, s2
2369:             nop
                  csrrci     t1, 0x340, 29
                  csrrci     s1, 0x340, 20
                  c.slli     t0, 3
                  sra        tp, s8, a3
                  c.srai     s0, 2
                  andi       s11, s0, 680
                  nop
                  .4byte 0x00100073 # ebreak
                  c.srai     a0, 2
                  sll        a4, s6, zero
                  and        t6, a1, s1
                  mul        a5, a0, s4
                  auipc      t0, 986667
                  c.add      s5, t1
                  csrrsi     ra, 0x340, 23
                  addi       ra, s3, 421
                  c.srli     a0, 14
                  add        a0, s5, ra
                  and        a0, tp, s10
                  blt        s6, t2, 2395f
                  c.li       a3, 18
                  c.srli     a4, 9
                  slli       s2, s3, 1
                  rem        s10, s7, sp
                  srl        s0, a3, s0
2395:             srl        s11, a5, s11
                  remu       s10, t5, t3
                  divu       a6, s11, t1
                  remu       a0, s7, s0
                  bge        t0, s7, 2403f
                  andi       a6, zero, 24
                  ori        s0, a7, -648
                  mul        s5, a2, s3
2403:             add        s0, s4, t5
                  c.lui      t5, 24
                  sll        s11, t1, a0
                  xor        a6, t4, ra
                  mul        t6, t2, s7
                  ori        s11, t3, 481
                  srli       a0, t2, 3
                  c.lui      s3, 23
                  ori        t6, a5, -830
                  c.addi     s11, 14
                  mulhu      s3, a7, gp
                  c.xor      a4, a2
                  c.beqz     a4, 2420f
                  csrrw      t0, 0x340, tp
                  bge        s3, s9, 2425f
                  c.srai     a3, 10
                  c.bnez     s0, 2424f
2420:             c.sub      a5, a0
                  slti       t4, s6, 125
                  mul        ra, s10, t3
                  remu       s4, s9, a7
2424:             auipc      s11, 661482
2425:             add        s6, s5, s0
                  divu       s11, s7, t0
                  sll        a0, a7, tp
                  sll        s4, a4, s10
                  c.srli     a0, 1
                  rem        a3, s6, s1
                  sub        a6, t0, s6
                  csrrci     s7, 0x340, 3
                  and        a6, a5, a2
                  addi       t6, a0, -463
                  bge        t0, a3, 2439f
                  slli       s11, s9, 13
                  srai       s3, a7, 26
                  c.addi     a1, 18
2439:             nop
                  xor        a2, zero, a0
                  csrrw      a0, 0x340, a1
                  c.xor      a1, s0
                  slt        s11, s1, s1
                  c.addi     a2, -24
                  c.srli     a4, 17
                  rem        s1, s6, t6
                  and        a6, s3, tp
                  slt        t2, a5, s8
                  sub        s11, s10, zero
                  srl        s10, t1, t0
                  auipc      a3, 772615
                  c.addi     t4, -7
                  sltu       s1, s1, s4
                  bne        zero, a0, 2462f
                  lui        a2, 99638
                  xor        a3, ra, s10
                  bgeu       s9, a0, 2465f
                  rem        t5, t5, ra
                  xori       zero, s8, 61
                  andi       gp, t4, -488
                  addi       s5, a0, 71
2462:             slt        s0, s10, t4
                  csrrsi     s11, 0x340, 5
                  c.nop
2465:             csrrs      s1, 0x340, a3
                  divu       t1, a5, t5
                  c.andi     a0, -3
                  and        a5, s2, a7
                  c.addi     s0, -30
                  bgeu       a1, a4, 2472f
                  beq        a2, s1, 2487f
2472:             srli       a2, s0, 26
                  sltu       s0, t4, a5
                  c.nop
                  c.sub      s1, a4
                  mulhsu     a6, t1, s2
                  div        a3, a0, tp
                  c.beqz     a2, 2483f
                  c.nop
                  sub        a3, t5, s1
                  c.bnez     a2, 2500f
                  auipc      a2, 480393
2483:             c.ebreak;c.nop;
                  xori       t5, s8, -83
                  c.srli     a3, 3
                  beq        sp, s5, 2506f
2487:             slli       s2, t2, 12
                  add        t1, a1, a7
                  slt        t0, s5, a5
                  blt        s9, a1, 2510f
                  rem        s10, s2, s0
                  slli       a1, t4, 26
                  c.srli     a4, 12
                  sra        a6, t2, s0
                  c.bnez     a3, 2499f
                  bne        ra, ra, 2508f
                  ori        s4, s4, -309
                  divu       t0, a7, s1
2499:             or         s1, a1, gp
2500:             c.srai     a2, 3
                  and        s2, tp, t4
                  beq        s10, t6, 2504f
                  csrrsi     a2, 0x340, 21
2504:             rem        t2, t6, t5
                  c.and      a4, a5
2506:             sltu       a0, s10, s5
                  ori        s0, a7, -222
2508:             addi       a3, a5, -822
                  bge        s2, a3, 2521f
2510:             c.andi     a1, 12
                  srai       gp, a7, 26
                  c.ebreak;c.nop;
                  ori        s3, zero, -527
                  c.bnez     a2, 2522f
                  or         zero, a2, gp
                  c.xor      a1, a2
                  xor        s4, s7, tp
                  csrrw      s4, 0x340, s1
                  ori        s11, a3, 34
                  bltu       s3, t2, 2528f
2521:             and        a2, gp, tp
2522:             srl        zero, a0, s8
                  or         t2, s1, s10
                  csrrc      tp, 0x340, a1
                  c.ebreak;c.nop;
                  sll        s4, s7, t3
                  bgeu       s9, s1, 2545f
2528:             c.add      a2, s10
                  add        t6, a1, ra
                  c.nop
                  csrrs      zero, 0x340, s3
                  csrrw      t3, 0x340, ra
                  csrrc      s5, 0x340, t6
                  slti       zero, sp, -563
                  csrrci     s5, 0x340, 19
                  mulhu      a4, gp, t1
                  c.lui      t5, 7
                  c.andi     s1, 30
                  sltu       t1, ra, sp
                  c.bnez     s0, 2559f
                  c.beqz     a0, 2555f
                  slti       s6, a0, 632
                  rem        s10, s7, a3
                  or         s5, s4, t0
2545:             sltiu      a0, s1, -407
                  csrrs      t0, 0x340, s2
                  bgeu       zero, s11, 2555f
                  c.ebreak;c.nop;
                  addi       s11, s4, 139
                  c.lui      a4, 31
                  c.sub      s1, a3
                  and        t1, tp, a5
                  csrrci     t6, 0x340, 6
                  c.or       a0, a4
2555:             c.xor      a0, a3
                  add        a7, s2, a4
                  divu       a3, s7, t0
                  auipc      a6, 399601
2559:             mulhsu     s0, tp, a0
                  csrrc      t2, 0x340, s10
                  srli       t3, t2, 9
                  nop
                  csrrsi     a2, 0x340, 0
                  slti       s11, sp, 280
                  csrrwi     t6, 0x340, 31
                  c.add      t1, s10
                  ori        s1, t0, -576
                  mulh       a6, a2, a5
                  c.lui      a5, 23
                  c.bnez     a0, 2572f
                  c.beqz     a1, 2587f
2572:             srai       s6, a0, 24
                  bltu       ra, s1, 2585f
                  sll        s5, ra, s10
                  mul        t4, t2, ra
                  beq        t0, s9, 2582f
                  c.slli     tp, 2
                  beq        s11, s8, 2592f
                  srl        s2, s1, a1
                  blt        s2, t0, 2590f
                  c.nop
2582:             sub        t3, a4, t3
                  ori        gp, s4, 445
                  slti       t2, s2, -748
2585:             srl        a4, a7, gp
                  c.srli     a0, 29
2587:             lui        zero, 835328
                  sltu       a4, s5, a0
                  csrrc      a1, 0x340, s8
2590:             addi       s10, a2, 682
                  c.bnez     a1, 2610f
2592:             sra        s0, s4, t5
                  sll        a5, zero, s2
                  c.xor      a5, a4
                  c.sub      a3, a4
                  and        gp, s2, s11
                  c.andi     a1, 6
                  srl        a1, a3, a3
                  divu       a3, a4, s4
                  xor        a5, s0, s8
                  c.and      s0, a1
                  c.srli     a1, 24
                  c.srli     a2, 29
                  remu       s11, s10, t1
                  add        s10, t1, s4
                  c.bnez     a3, 2619f
                  mul        a6, s2, t6
                  c.andi     a4, 6
                  add        t3, t0, a1
2610:             blt        a1, a0, 2618f
                  c.mv       a2, t3
                  csrrwi     a0, 0x340, 23
                  c.add      s5, t6
                  csrrc      t4, 0x340, a5
                  sltiu      a7, a2, 711
                  xor        t1, t6, t1
                  auipc      t4, 1038754
2618:             rem        s0, tp, a1
2619:             csrrsi     t2, 0x340, 31
                  auipc      t0, 184266
                  sll        a7, t6, s7
                  srli       a1, a4, 27
                  csrrci     t0, 0x340, 31
                  bltu       t3, t2, 2630f
                  c.sub      s1, a5
                  csrrsi     t0, 0x340, 8
                  mulhsu     a3, ra, s11
                  srli       a3, t0, 5
                  auipc      s6, 157168
2630:             mulhsu     t4, s8, t1
                  c.addi     a2, -13
                  bgeu       t3, gp, 2637f
                  slt        ra, t4, s10
                  srli       t5, t4, 16
                  mulhu      a6, a0, a2
                  div        s3, a1, a1
2637:             mulhu      a6, s2, sp
                  srli       s3, s7, 15
                  ori        t1, a2, -579
                  sll        s10, a5, t1
                  c.srli     a4, 22
                  c.mv       t1, t0
                  ori        s10, a2, -390
                  sub        s6, s10, t3
                  c.nop
                  blt        t2, s3, 2654f
                  c.srai     a4, 13
                  c.sub      s1, s0
                  sltu       s1, ra, t0
                  addi       t2, a6, 40
                  xori       s10, sp, -888
                  csrrsi     t0, 0x340, 8
                  div        s1, t5, s0
2654:             add        s11, t2, zero
                  c.bnez     a2, 2663f
                  c.or       a4, s1
                  lui        t0, 234487
                  rem        t3, a2, s9
                  or         tp, a1, tp
                  bltu       a4, ra, 2664f
                  c.ebreak;c.nop;
                  csrrs      s1, 0x340, s0
2663:             c.sub      a5, a4
2664:             sra        a1, s5, a6
                  c.or       s1, s0
                  slti       t2, t1, -76
                  c.sub      s1, a1
                  csrrsi     t1, 0x340, 25
                  bge        ra, zero, 2675f
                  xor        s4, a7, s10
                  sltu       zero, a2, t0
                  slli       a5, s10, 26
                  xor        tp, a1, t3
                  and        s10, s1, t6
2675:             csrrwi     a2, 0x340, 7
                  csrrc      s6, 0x340, s0
                  c.nop
                  blt        t1, s4, 2696f
                  sltiu      s10, s11, -744
                  c.bnez     a5, 2694f
                  andi       t6, s9, -844
                  lui        ra, 952731
                  ori        t3, a4, -74
                  c.or       s0, a0
                  mul        tp, s1, s7
                  csrrw      s5, 0x340, t2
                  csrrwi     a6, 0x340, 17
                  c.add      t5, s6
                  and        a7, s10, s9
                  csrrw      a1, 0x340, t4
                  c.and      s0, a1
                  mulh       a0, t5, s10
                  bge        a3, a0, 2705f
2694:             c.srai     s1, 4
                  c.li       s11, -26
2696:             c.slli     t4, 2
                  csrrs      a1, 0x340, s8
                  csrrc      tp, 0x340, zero
                  c.beqz     a3, 2718f
                  bltu       a7, a0, 2708f
                  addi       a3, sp, -443
                  sll        t1, t1, a7
                  beq        t5, t3, 2705f
                  mulhsu     s2, a0, a7
2705:             c.bnez     a4, 2725f
                  auipc      s2, 443629
                  remu       s0, tp, t4
2708:             csrrci     s4, 0x340, 17
                  bne        s1, s1, 2717f
                  xori       a3, a6, 765
                  c.sub      s0, a1
                  c.mv       t4, s0
                  c.slli     t4, 5
                  c.li       s4, -15
                  c.bnez     a3, 2731f
                  add        a5, s8, s2
2717:             c.lui      a5, 1
2718:             csrrci     s7, 0x340, 17
                  slt        t0, a1, gp
                  nop
                  mulhsu     t2, s4, a0
                  c.beqz     a5, 2741f
                  c.beqz     s0, 2736f
                  div        s3, tp, t3
2725:             c.slli     t5, 16
                  mulhu      s0, t5, s5
                  csrrs      zero, 0x340, zero
                  slt        t6, zero, s11
                  c.addi     a7, -22
                  lui        s7, 830727
2731:             xor        a4, s8, a0
                  csrrwi     zero, 0x340, 24
                  c.beqz     a2, 2735f
                  andi       a6, ra, -527
2735:             c.andi     a4, -27
2736:             sltiu      a6, t2, 247
                  srai       s4, a6, 24
                  sub        a6, a4, a2
                  auipc      a6, 896866
                  nop
2741:             bgeu       a2, t0, 2747f
                  srli       s2, zero, 28
                  c.addi     s11, 14
                  csrrw      a6, 0x340, t1
                  sltiu      t2, t3, 3
                  mulh       s6, sp, t0
2747:             blt        s7, t2, 2751f
                  c.and      a5, a4
                  c.addi     ra, -25
                  bge        s5, t0, 2758f
2751:             or         s10, sp, zero
                  mulh       tp, sp, a4
                  remu       zero, a7, t0
                  csrrs      s2, 0x340, s7
                  blt        tp, tp, 2763f
                  c.srai     a4, 28
                  c.mv       gp, gp
2758:             and        a1, zero, a3
                  csrrsi     a7, 0x340, 17
                  slli       a6, a3, 12
                  c.xor      s0, s1
                  slli       s3, a7, 21
2763:             and        s0, s2, t0
                  mulh       s0, t1, t0
                  ori        a0, s0, -35
                  lui        s10, 197564
                  bne        s2, s3, 2777f
                  mulh       s7, s11, t3
                  c.li       a1, 0
                  mulh       s11, sp, s8
                  c.lui      t3, 3
                  csrrci     t2, 0x340, 1
                  c.ebreak;c.nop;
                  auipc      s0, 224093
                  xor        s10, s8, gp
                  c.andi     a2, -15
2777:             c.sub      a4, a2
                  and        s2, s2, zero
                  rem        zero, s3, t0
                  slli       a4, s10, 11
                  .4byte 0x00100073 # ebreak
                  csrrc      s1, 0x340, t2
                  beq        t6, s3, 2788f
                  add        s1, t0, a5
                  c.li       gp, -4
                  c.bnez     a1, 2794f
                  div        s5, a7, t6
2788:             c.addi     a7, 16
                  nop
                  c.lui      a1, 1
                  c.add      s7, t3
                  mulhsu     s5, s10, a5
                  xor        t6, s8, gp
2794:             c.beqz     a1, 2808f
                  mul        s1, a7, s1
                  csrrs      zero, 0x340, a6
                  bltu       t6, t6, 2813f
                  div        tp, s11, a1
                  xori       a5, s8, 508
                  bne        t2, s9, 2805f
                  csrrs      s2, 0x340, a5
                  c.add      s7, a7
                  c.bnez     a1, 2805f
                  xori       t3, t4, -967
2805:             c.andi     a2, -19
                  c.bnez     a3, 2814f
                  csrrwi     a4, 0x340, 6
2808:             csrrs      ra, 0x340, a4
                  c.srai     a1, 11
                  bge        s10, a7, 2814f
                  c.lui      t6, 28
                  auipc      s6, 321236
2813:             mulh       s4, t1, s4
2814:             c.or       a4, a5
                  beq        gp, t3, 2834f
                  ori        t0, sp, 796
                  c.ebreak;c.nop;
                  beq        a7, s10, 2830f
                  xor        t4, a5, a2
                  andi       s10, t2, 503
                  c.add      t4, s5
                  c.beqz     s0, 2842f
                  sub        a2, s1, sp
                  div        s2, t3, s5
                  csrrwi     a7, 0x340, 25
                  div        a4, a4, s7
                  c.addi     t6, -11
                  c.or       a5, a5
                  bgeu       a3, a7, 2841f
2830:             c.add      s1, t2
                  c.srai     a3, 31
                  c.srai     a3, 11
                  slli       tp, s5, 14
2834:             bge        a0, a0, 2850f
                  c.add      s3, t1
                  csrrc      a1, 0x340, s8
                  srai       a1, a0, 6
                  c.li       a0, 26
                  slli       s1, a2, 4
                  div        s10, a4, a0
2841:             div        t3, a0, t6
2842:             blt        t3, ra, 2861f
                  slt        a1, t1, s5
                  c.xor      a1, a5
                  csrrsi     s2, 0x340, 6
                  sltiu      a1, t4, -73
                  csrrc      a6, 0x340, s1
                  c.and      a1, s1
                  c.add      s3, a5
2850:             remu       a6, t2, s0
                  remu       t2, a7, t0
                  csrrs      s3, 0x340, t4
                  bgeu       s9, s2, 2866f
                  mul        a0, s4, zero
                  beq        a7, s9, 2861f
                  blt        s0, a6, 2862f
                  xor        t5, s4, zero
                  c.or       s0, a2
                  c.srai     s0, 18
                  blt        s4, t2, 2879f
2861:             srai       s2, s5, 31
2862:             csrrwi     ra, 0x340, 6
                  c.andi     a3, 0
                  c.srai     a4, 6
                  csrrc      s5, 0x340, t0
2866:             andi       s5, s6, 292
                  c.slli     s5, 31
                  c.nop
                  addi       a4, s6, 6
                  auipc      s11, 179354
                  mulhu      s5, t2, s3
                  c.srai     a1, 27
                  or         s1, s4, t3
                  ori        s2, t3, -314
                  or         s6, s11, s2
                  c.lui      s2, 11
                  c.bnez     a3, 2885f
                  srli       s11, a6, 4
2879:             c.sub      a3, a3
                  beq        tp, s4, 2884f
                  c.xor      a3, a1
                  sll        t3, a2, s4
                  slt        s2, s6, a3
2884:             xor        t6, a5, t5
2885:             addi       t1, sp, 393
                  bne        t4, s11, 2894f
                  c.ebreak;c.nop;
                  addi       t6, t1, -133
                  c.slli     s2, 3
                  csrrs      a6, 0x340, t2
                  mulhu      s6, s3, a0
                  divu       s1, zero, tp
                  .4byte 0x00100073 # ebreak
2894:             c.andi     a5, -5
                  c.xor      a5, a1
                  c.addi     a0, -28
                  c.srli     a4, 20
                  csrrc      a6, 0x340, tp
                  mulh       t5, s3, t4
                  bne        a3, t1, 2902f
                  c.addi     ra, -20
2902:             c.andi     a5, 25
                  c.and      a4, a1
                  c.and      s0, a3
                  bne        s10, t5, 2921f
                  c.nop
                  csrrci     t1, 0x340, 23
                  andi       s2, s8, -825
                  .4byte 0x00100073 # ebreak
                  mul        a4, sp, s2
                  c.addi     t2, -29
                  csrrwi     a2, 0x340, 14
                  srli       t5, a2, 17
                  auipc      a1, 144172
                  csrrsi     t1, 0x340, 1
                  divu       a5, s10, a7
                  c.add      s11, sp
                  mul        s4, t6, a7
                  mulhsu     a7, s2, s1
                  sra        t5, a0, sp
2921:             csrrci     a7, 0x340, 10
                  c.ebreak;c.nop;
                  sltu       a0, ra, tp
                  slti       s10, a6, 778
                  div        zero, s3, s6
                  csrrsi     s5, 0x340, 10
                  .4byte 0x00100073 # ebreak
                  or         s3, t2, tp
                  add        zero, s6, a4
                  bne        sp, s8, 2949f
                  and        tp, gp, zero
                  c.addi     a0, 25
                  add        s11, a7, s8
                  blt        t0, a6, 2952f
                  srl        zero, zero, ra
                  csrrci     s6, 0x340, 17
                  or         a0, a5, s4
                  bge        a5, s7, 2958f
                  auipc      s1, 245603
                  mulh       t2, a0, s5
                  or         s6, a7, s9
                  sltu       s5, t1, a5
                  csrrci     s3, 0x340, 7
                  divu       zero, a2, s3
                  c.slli     s4, 16
                  auipc      t1, 464925
                  bgeu       s0, t3, 2952f
                  sub        a4, t5, a0
2949:             csrrci     s11, 0x340, 27
                  lui        a2, 513029
                  csrrwi     gp, 0x340, 25
2952:             addi       s2, t3, -598
                  sra        s1, s7, a5
                  slt        s10, a3, s11
                  mulh       a3, a2, s5
                  sltiu      a0, a2, -194
                  c.lui      s10, 3
2958:             csrrwi     s7, 0x340, 17
                  and        t3, t3, s2
                  c.srli     s0, 28
                  csrrs      t2, 0x340, s7
                  mulh       s2, t0, s9
                  bgeu       t6, a7, 2967f
                  and        gp, s11, a6
                  c.and      a0, s1
                  c.add      t4, a7
2967:             andi       t1, s10, -987
                  and        zero, t5, s0
                  bltu       s4, s6, 2979f
                  csrrci     zero, 0x340, 4
                  and        s2, t2, t4
                  c.bnez     a1, 2984f
                  divu       s7, t2, t6
                  sra        gp, s3, tp
                  csrrci     t6, 0x340, 4
                  c.andi     a2, -17
                  xor        s1, s11, t5
                  ori        t0, s2, -150
2979:             lui        s0, 809598
                  c.ebreak;c.nop;
                  bne        tp, a1, 2989f
                  srai       a0, s1, 8
                  or         a4, s4, s7
2984:             divu       a6, a5, s5
                  blt        t5, t3, 2993f
                  mulh       t6, s3, t4
                  csrrs      t5, 0x340, a2
                  c.add      s3, a5
2989:             slti       s10, s9, -528
                  or         s4, s10, ra
                  lui        a3, 883260
                  divu       s0, s8, a5
2993:             slli       t6, t6, 10
                  ori        a4, a5, 568
                  csrrsi     a5, 0x340, 12
                  div        a2, a6, s6
                  c.andi     s1, -32
                  c.xor      a4, a4
                  rem        s3, tp, ra
                  sltiu      s4, t0, 95
                  mulhsu     a6, s1, ra
                  csrrci     a3, 0x340, 15
                  csrrsi     t3, 0x340, 17
                  addi       tp, s10, 621
                  remu       s10, a7, a4
                  c.addi     s1, 9
                  remu       a1, t6, a0
                  .4byte 0x00100073 # ebreak
                  c.lui      a2, 10
                  slli       a3, s6, 7
                  bge        s8, s2, 3013f
                  remu       s5, a5, s5
3013:             mulh       a5, a6, t1
                  c.srai     a3, 25
                  c.ebreak;c.nop;
                  divu       s6, a3, s0
                  sltu       a1, a7, s3
                  bgeu       s11, tp, 3032f
                  srl        a1, a7, a1
                  csrrc      a3, 0x340, a3
                  csrrw      s4, 0x340, t0
                  csrrci     tp, 0x340, 20
                  mul        a1, a5, s10
                  c.and      s0, s1
                  mulhsu     gp, s9, ra
                  c.nop
                  auipc      a7, 642773
                  lui        t0, 217485
                  slti       a2, sp, 641
                  la         a0, region_2+1502 #start load_store_instr_stream_1
                  la         s3, region_3+0 #start load_store_instr_stream_0
                  sb         a2, 11(a0)
                  lb         s5, 36(a0)
                  lb         t5, 35(s3)
                  sb         t0, 12(a0)
                  lb         s4, -21(a0)
                  lbu        a5, 40(a0)
                  sb         s1, 38(s3)
                  sw         s4, 22(a0)
                  lb         t3, -4(a0)
                  lbu        a7, 51(a0)
                  lb         gp, -36(a0)
                  lh         s2, 54(s3)
                  lb         gp, 49(s3)
                  lb         s2, -47(a0) #end load_store_instr_stream_1
                  lbu        t4, 25(s3) #end load_store_instr_stream_0
                  sltiu      s4, t1, 137
                  bltu       a0, s2, 3043f
3032:             remu       t1, t6, t2
                  .4byte 0x00100073 # ebreak
                  c.li       t5, 29
                  lui        s2, 182964
                  mul        t5, s7, a3
                  andi       tp, a1, 754
                  srli       t3, t3, 31
                  mul        s1, s4, a2
                  mul        s11, a0, zero
                  csrrw      a0, 0x340, s8
                  bge        a6, s4, 3056f
3043:             c.lui      a4, 17
                  rem        s11, s0, a2
                  div        s1, sp, a6
sub_1_14:         jal        gp, 3f
0:                c.jal      17f
1:                jal        ra, 10f
2:                c.j        13f
3:                jal        ra, 0b
4:                c.jal      1b
5:                c.jal      15f
6:                c.j        11f
7:                c.j        9f
8:                c.j        12f
9:                c.jal      2b
10:               jal        ra, 16f
11:               c.j        4b
12:               c.jal      14f
13:               c.j        5b
14:               jal        ra, 6b
15:               jal        s11, 18f
16:               jal        ra, 7b
17:               jal        ra, 8b
18:               c.add      s10, a3
                  c.srai     s0, 5
                  c.or       a4, s1
                  c.nop
                  csrrw      ra, 0x340, s7
                  sra        t1, a0, s4
                  csrrsi     s5, 0x340, 0
                  sra        s2, t1, zero
                  mulhu      a2, zero, s7
                  beq        s1, t1, 3074f
                  divu       t3, t4, s5
3056:             .4byte 0x00100073 # ebreak
                  sub        t1, t1, t5
                  srli       s0, a4, 11
                  bgeu       a5, a5, 3064f
                  mulhu      s0, zero, a6
                  divu       s11, a6, a7
                  addi       a3, s1, -743
                  c.and      a2, a0
3064:             c.beqz     a5, 3066f
                  c.beqz     s0, 3077f
3066:             c.xor      a3, a5
                  blt        gp, gp, 3075f
                  mul        t4, t5, ra
                  c.xor      s0, a5
                  xor        gp, t2, s10
                  c.slli     s5, 2
                  c.or       a2, s0
                  andi       a7, s3, 467
3074:             srli       s7, a3, 26
3075:             blt        sp, zero, 3083f
                  mul        a3, s7, s0
3077:             csrrwi     a5, 0x340, 5
                  sub        s11, t2, t4
                  c.beqz     a0, 3087f
                  csrrci     s5, 0x340, 29
                  csrrci     a3, 0x340, 16
                  c.mv       a0, a2
3083:             c.nop
                  c.xor      a3, a4
                  add        s7, a7, t1
                  c.or       a2, s0
3087:             mulhu      t4, a4, t6
                  divu       s3, gp, s11
                  addi       gp, s7, 470
                  c.sub      a3, a2
                  sltu       s4, s6, s1
                  mulhu      s7, s10, s4
                  c.lui      a4, 10
                  c.beqz     a4, 3113f
                  sltiu      s4, s9, 572
                  slli       a7, a2, 21
                  slt        a2, a2, gp
                  c.bnez     a5, 3106f
                  or         s6, s6, a6
                  div        ra, a4, a7
                  nop
                  mulh       s2, a6, a0
                  divu       a2, s9, s9
                  la         t2, region_2+1640 #start load_store_instr_stream_2
                  la         t0, region_2+61 #start load_store_instr_stream_1
                  la         a5, region_2+4330 #start load_store_instr_stream_0
                  lbu        gp, 29(a5)
                  lb         a6, -11(t0)
                  sw         t5, -124(t2)
                  sh         t6, -1(t0)
                  sb         s5, 10(t0)
                  lbu        a1, 16(t0)
                  sh         s5, 242(t2)
                  sb         s10, -7(t0)
                  lw         t6, 2(a5)
                  lb         s7, 154(t2)
                  lb         zero, 91(t2)
                  sb         a0, -13(t0)
                  lhu        t1, -9(t0)
                  lb         a2, 9(t0)
                  lh         a7, 38(a5)
                  lb         a0, 83(t2)
                  sb         sp, -1(a5)
                  lw         tp, -228(t2)
                  sb         t4, -231(t2)
                  sb         gp, -37(a5)
                  lhu        ra, 200(t2)
                  sb         s4, -203(t2)
                  lhu        s3, 15(t0)
                  sb         t3, -15(t0) #end load_store_instr_stream_1
                  lbu        s4, -248(t2) #end load_store_instr_stream_2
                  lbu        s6, -48(a5) #end load_store_instr_stream_0
                  c.nop
                  srli       ra, a2, 11
3106:             c.andi     a4, 5
                  csrrci     a3, 0x340, 0
                  bne        a4, a7, 3110f
                  slli       t3, a0, 10
3110:             auipc      tp, 941196
                  srli       t4, a5, 6
                  slli       t4, s5, 10
3113:             csrrci     s2, 0x340, 16
                  sll        a3, s6, gp
                  andi       a2, a2, -839
                  csrrc      a5, 0x340, s11
                  la         a2, region_0+1585 #start riscv_load_store_rand_instr_stream_10
                  sb         s3, -2(a2)
                  lb         s11, -4(a2)
                  csrrw      a0, 0x340, s1
                  sw         sp, 3(a2)
                  c.ebreak;c.nop;
                  lb         s7, 4(a2)
                  c.and      s1, a4
                  lui        s4, 380563
                  mulhu      a3, s11, a1
                  sb         t3, -16(a2)
                  div        t6, s7, s0
                  rem        a6, zero, a2
                  lbu        t1, -4(a2)
                  lui        s0, 344389
                  sb         ra, -2(a2)
                  c.add      s5, s9
                  c.slli     t5, 27
                  csrrci     a4, 0x340, 16
                  sb         t2, 16(a2)
                  lb         t1, -16(a2)
                  sw         s3, 3(a2)
                  sh         t2, 5(a2)
                  sw         t1, 3(a2)
                  sltiu      a3, s9, -273
                  c.lui      t1, 8
                  lb         s2, 16(a2) #end riscv_load_store_rand_instr_stream_10
                  blt        s0, a3, 3125f
                  csrrc      t1, 0x340, s10
                  srli       a1, s3, 27
                  div        a0, s9, t1
                  sll        s0, s7, a6
                  c.li       a0, -19
                  bne        a4, s2, 3139f
                  .4byte 0x00100073 # ebreak
3125:             bge        t6, t6, 3135f
                  .4byte 0x00100073 # ebreak
                  sltiu      s0, s8, 5
                  slti       a6, t5, -940
                  mulhsu     t6, ra, t6
                  or         s1, t4, s1
                  or         t0, t0, s4
                  srai       a2, a5, 10
                  bne        s8, t6, 3147f
                  bne        s11, t4, 3153f
3135:             mul        t0, a3, tp
                  sll        t1, t2, s11
                  c.ebreak;c.nop;
                  rem        s4, tp, a2
3139:             and        a6, t2, s0
                  lui        t4, 74847
                  xori       gp, t2, 512
                  c.srai     a5, 21
                  c.andi     s1, 0
                  mulhu      t1, t4, s4
                  csrrc      a7, 0x340, tp
                  bge        s10, s6, 3162f
3147:             xor        t2, s10, a2
                  auipc      t6, 891276
                  addi       s10, sp, 184
                  srli       gp, s9, 23
                  c.and      a3, a0
                  slli       s1, s2, 15
3153:             bne        s5, ra, 3166f
                  csrrwi     a0, 0x340, 22
                  add        t1, t5, s2
                  csrrs      t6, 0x340, tp
                  ori        s5, sp, 408
                  c.add      t0, t4
                  beq        s6, a2, 3177f
                  divu       s3, s8, t4
                  beq        a0, s7, 3167f
3162:             xor        a4, t6, a0
                  addi       s11, s0, 536
                  srai       a3, t4, 7
                  mulh       a6, t2, s3
3166:             bgeu       tp, s7, 3172f
3167:             c.li       t1, 2
                  sltu       a2, a3, s5
                  divu       s4, a7, ra
                  c.and      s1, a5
                  mulh       a7, s11, a5
3172:             csrrs      s11, 0x340, s7
                  c.add      s3, s9
                  mulhu      a0, a6, t5
                  div        a2, s3, s6
                  slli       s2, a3, 11
3177:             c.andi     a5, 16
                  srli       t5, tp, 20
                  c.slli     a2, 23
                  beq        t6, zero, 3184f
                  .4byte 0x00100073 # ebreak
                  srai       s4, s6, 23
                  c.srli     s0, 31
3184:             andi       s6, a7, 720
                  ori        a7, tp, -365
                  c.andi     a5, 3
                  slt        t2, a7, gp
                  or         s0, t2, t3
                  c.lui      s11, 2
                  c.li       s0, 31
                  sra        gp, a2, sp
                  and        s6, gp, a4
                  beq        t6, a4, 3213f
                  xori       s1, s2, 815
                  nop
                  auipc      a2, 966775
                  and        t5, a7, s2
                  c.addi     t0, -8
                  srl        s7, s2, a4
                  csrrs      a1, 0x340, t2
                  xor        tp, t1, s10
                  c.xor      a5, a0
                  add        s7, s4, s6
                  and        a0, a0, s4
                  mulhu      s0, gp, t1
                  c.srli     a5, 4
                  .4byte 0x00100073 # ebreak
                  div        a2, s8, t1
                  c.and      a5, a3
                  csrrs      s3, 0x340, t0
                  bgeu       s6, s3, 3215f
                  bne        s0, zero, 3214f
3213:             mulhu      s6, s7, t4
3214:             sra        a0, sp, a6
3215:             c.beqz     s0, 3234f
                  c.bnez     s0, 3236f
                  auipc      s2, 788099
                  srli       t1, a1, 4
                  mulhu      a7, a7, gp
                  blt        a5, s6, 3222f
                  slti       s3, a7, 148
3222:             lui        s2, 121160
                  c.li       a4, -21
                  c.add      a1, t5
                  bltu       a5, s7, 3237f
                  c.sub      a3, a3
                  c.slli     a0, 19
                  or         s3, s8, a7
                  xori       a5, zero, 843
                  xor        a1, t5, gp
                  c.ebreak;c.nop;
                  c.xor      a5, a5
                  sltiu      s10, t0, 997
3234:             divu       s6, t0, t6
                  beq        s1, a5, 3243f
3236:             rem        s6, s3, s5
3237:             sra        t2, s0, a2
                  auipc      ra, 696490
                  remu       s2, gp, s6
                  add        s3, a5, tp
                  srai       zero, gp, 14
                  c.mv       a3, a2
3243:             .4byte 0x00100073 # ebreak
                  csrrw      t3, 0x340, s0
                  c.lui      a1, 8
                  bge        s3, a7, 3258f
                  mulh       s10, a5, s3
                  slti       gp, s0, 301
                  c.or       a5, a5
                  csrrw      ra, 0x340, gp
                  lui        t2, 146886
                  divu       a6, s10, t4
                  slli       a6, a3, 28
                  mulhsu     t2, t0, s8
                  ori        t5, tp, 673
                  c.slli     ra, 17
                  csrrci     a7, 0x340, 19
3258:             add        s1, tp, s0
                  div        a3, s9, a0
                  mul        a2, t4, s10
                  add        a3, tp, s6
                  csrrc      s7, 0x340, a7
                  c.srli     a2, 8
                  lui        s3, 452631
                  c.addi     t3, 28
                  sll        a7, s4, tp
                  csrrc      s7, 0x340, tp
                  csrrs      zero, 0x340, t3
                  srai       tp, s6, 22
                  c.srli     a0, 26
                  mulhsu     s0, a2, s6
                  and        t4, a4, a7
                  slli       a4, s8, 2
                  c.and      a4, a3
                  lui        zero, 839047
                  sra        tp, zero, tp
                  sub        s1, a1, gp
                  mul        t6, t1, s8
                  sltiu      s7, s0, 1002
                  c.addi     t6, 19
                  andi       s5, a0, 891
                  mulhu      a3, a5, s8
                  csrrci     t5, 0x340, 12
                  xor        t0, s6, s7
                  bne        s9, t5, 3293f
                  bne        s3, t1, 3300f
                  c.andi     s0, 5
                  csrrci     s6, 0x340, 26
                  c.addi     a6, 23
                  c.mv       t2, t6
                  addi       a7, s4, 287
                  srl        s10, t4, t1
3293:             c.xor      s1, a4
                  mul        a4, t5, t2
                  bltu       s9, s10, 3307f
                  rem        s6, t4, s6
                  or         zero, a7, tp
                  divu       s4, zero, a0
                  c.slli     ra, 12
3300:             csrrc      a0, 0x340, s8
                  div        s4, s2, sp
                  csrrsi     a0, 0x340, 31
                  div        a1, ra, a6
                  rem        t2, a2, t5
                  bne        s9, tp, 3310f
                  srli       t1, t1, 0
3307:             csrrw      s0, 0x340, s5
                  blt        s6, s0, 3313f
                  srl        s7, s6, a0
3310:             c.mv       ra, s4
                  csrrc      ra, 0x340, t3
                  c.beqz     a0, 3320f
3313:             c.or       s1, s0
                  mulhu      tp, a2, t2
                  c.nop
                  xori       s7, s4, 556
                  mulh       gp, ra, tp
                  c.addi     ra, 9
                  divu       a0, t1, s8
3320:             c.li       t4, 7
                  mul        s0, s2, s6
                  c.srai     a0, 8
                  sra        a7, gp, zero
                  mulhu      a1, s8, s4
                  csrrw      a2, 0x340, s5
                  xor        t4, s9, t2
                  blt        t5, s10, 3333f
                  c.xor      a2, a4
                  csrrs      a0, 0x340, s6
                  c.ebreak;c.nop;
                  csrrsi     t2, 0x340, 12
                  bgeu       a1, s7, 3348f
3333:             div        t3, s0, s7
                  csrrs      t5, 0x340, s3
                  divu       a6, a0, s5
                  c.nop
                  c.addi     s5, 3
                  nop
                  mul        a1, a4, t0
                  bgeu       a3, s5, 3352f
                  c.bnez     a4, 3343f
                  mulhsu     a3, s7, s3
3343:             c.andi     s0, -1
                  beq        s3, s6, 3362f
                  c.nop
                  c.xor      a3, a4
                  or         s10, zero, t0
3348:             xori       s2, a2, -1017
                  div        a2, a7, a0
                  bge        s4, s10, 3358f
                  sub        zero, t1, a6
3352:             c.andi     a0, 25
                  c.lui      gp, 5
                  csrrci     a3, 0x340, 23
                  mulh       t1, s8, a0
                  mulhu      s6, sp, s7
                  slti       tp, s2, 2
3358:             csrrci     a1, 0x340, 8
                  or         s4, gp, t1
                  srai       s11, t0, 12
                  csrrci     s1, 0x340, 2
3362:             c.add      a3, t1
                  ori        t3, a0, 991
                  mulhsu     s0, s9, s6
                  or         a7, ra, a2
                  add        a4, a5, t1
                  bgeu       s3, s11, 3375f
                  mulh       s2, t6, a6
                  c.lui      s3, 14
                  srl        a6, t1, s2
                  c.beqz     s1, 3390f
                  c.ebreak;c.nop;
                  c.or       a4, s0
                  c.ebreak;c.nop;
3375:             mulh       s1, s5, s8
                  auipc      gp, 76569
                  sra        s0, a7, t3
                  c.or       a1, a2
                  slli       s2, t2, 3
                  xori       s0, s6, 787
                  c.srai     s0, 17
                  blt        a6, t4, 3394f
                  c.add      a5, t1
                  mulh       a5, t5, s8
                  c.and      a2, s1
                  sltu       a7, a3, a2
                  beq        t6, s6, 3407f
                  csrrwi     t2, 0x340, 8
                  slli       t4, a4, 23
3390:             mulhsu     s4, a6, zero
                  c.mv       a4, gp
                  bgeu       t5, s10, 3406f
                  c.addi     s0, -18
3394:             sltiu      s2, s11, 215
                  andi       s11, a5, -869
                  mul        s7, s5, t2
                  csrrci     t0, 0x340, 8
                  c.addi     s1, 28
                  add        t1, s3, a7
                  csrrc      a2, 0x340, a0
                  ori        a4, s2, -684
                  and        a4, a2, s5
                  c.li       s5, 3
                  csrrci     tp, 0x340, 6
                  c.addi     a1, -22
3406:             c.bnez     a4, 3418f
3407:             c.sub      s1, a0
                  or         gp, s8, s11
                  slli       s11, s9, 29
                  mulhsu     s7, zero, t1
                  c.add      a0, t6
                  c.lui      t2, 16
                  mulhu      t4, s11, s4
                  and        t5, a1, sp
                  srai       a0, a7, 7
                  nop
                  c.or       s0, a4
3418:             csrrwi     a6, 0x340, 23
                  rem        s7, ra, t2
                  bne        a4, t6, 3439f
                  csrrw      a2, 0x340, s3
                  c.bnez     s1, 3428f
                  or         t1, a0, s10
                  srli       t0, a7, 5
                  slli       a0, a5, 4
                  c.andi     a1, -22
                  mul        ra, sp, s7
3428:             bltu       a5, s9, 3448f
                  divu       a7, t0, t5
                  c.srli     a1, 18
                  sltu       t5, zero, a7
                  csrrwi     s5, 0x340, 17
                  sltiu      a7, t0, -38
                  c.mv       s5, ra
                  c.bnez     a0, 3443f
                  bgeu       a7, s5, 3441f
                  csrrsi     s10, 0x340, 24
                  c.xor      a1, s0
3439:             mulhu      s3, gp, s11
                  and        a4, a6, a0
3441:             slt        s5, ra, zero
                  sub        ra, s6, s10
3443:             beq        gp, s5, 3447f
                  c.bnez     a0, 3463f
                  bge        s10, s7, 3453f
                  csrrwi     s7, 0x340, 4
3447:             or         a1, t0, gp
3448:             bge        a1, a7, 3450f
                  c.bnez     a2, 3451f
3450:             lui        ra, 1044439
3451:             sltiu      t1, a7, 135
                  addi       s3, s2, -296
3453:             srai       t0, s11, 25
                  csrrci     a4, 0x340, 11
                  c.nop
                  c.or       a2, a4
                  c.mv       s11, s0
                  sra        a5, a3, t5
                  ori        ra, s4, 623
                  bltu       a7, a1, 3470f
                  xori       s5, s4, 294
                  slti       tp, s11, -839
3463:             c.and      a1, a0
                  slli       s5, s0, 31
                  slli       a1, a3, 10
                  mul        a1, sp, s6
                  sub        a2, t1, s4
                  mulhu      s6, zero, s1
                  srl        s10, s11, t6
3470:             c.li       a5, -19
                  sub        s0, t3, zero
                  c.mv       t4, s2
                  beq        s0, tp, 3478f
                  mulhu      a1, t2, a1
                  xor        s11, t4, s6
                  bge        ra, s9, 3484f
                  csrrwi     a5, 0x340, 7
3478:             mulh       t5, a3, a3
                  sltiu      s11, ra, 489
                  mul        ra, a4, t2
                  c.addi     s5, -5
                  mul        t3, t0, t2
                  mulhu      t5, s9, a4
3484:             csrrc      t6, 0x340, t4
                  mulhu      zero, a7, zero
                  auipc      a2, 143503
                  csrrs      a5, 0x340, a5
                  sll        s11, a5, s11
                  csrrci     zero, 0x340, 8
                  c.or       s1, a2
                  c.ebreak;c.nop;
                  csrrci     s1, 0x340, 23
                  c.li       t2, 7
                  andi       a0, a3, -634
                  sra        a1, a2, s0
                  beq        s5, t1, 3500f
                  c.srli     a4, 16
                  nop
                  mulhu      t4, tp, t6
3500:             c.li       s3, 25
                  bltu       t0, t1, 3517f
                  srai       t4, sp, 7
                  sll        t3, t1, t3
                  mulhu      s4, t4, s1
                  addi       s1, s10, 968
                  srai       s10, s4, 2
                  c.slli     a2, 12
                  xori       t1, t2, -765
                  c.bnez     a1, 3523f
                  c.xor      s0, a2
                  bltu       t5, s8, 3524f
                  slli       t1, s11, 30
                  and        s0, s2, sp
                  c.srli     a0, 10
                  c.beqz     a5, 3523f
                  c.slli     s7, 30
3517:             mulhu      s7, gp, zero
                  xori       s7, zero, 373
                  c.sub      a0, a0
                  xor        tp, t6, a4
                  bltu       a2, zero, 3526f
                  andi       a3, a1, -18
3523:             blt        t6, t5, 3533f
3524:             c.srai     a3, 24
                  csrrwi     tp, 0x340, 2
3526:             remu       s4, sp, t2
                  sra        s5, t6, t4
                  bltu       a7, s7, 3544f
                  sltu       t1, s11, a2
                  srai       s4, s8, 16
                  c.mv       a0, a5
                  c.add      t3, t0
3533:             add        t6, s5, t6
                  slt        a7, ra, zero
                  c.or       a4, a5
                  sltiu      gp, s4, 80
                  mulhu      a1, s5, s0
                  mul        s6, s1, a4
                  mulh       s7, gp, a2
                  sll        s1, s1, t5
                  c.or       a2, a1
                  sltiu      s7, t4, -436
                  xor        s0, s3, t3
3544:             ori        zero, zero, -6
                  sll        s3, a0, tp
                  c.andi     a3, 16
                  c.sub      a4, a0
                  div        s0, t4, gp
                  mul        s0, s9, t3
                  remu       a4, a6, a4
                  beq        a7, t0, 3553f
                  c.sub      a5, s1
3553:             srli       a7, s4, 3
                  ori        t6, a0, -488
                  csrrwi     t6, 0x340, 15
                  c.srai     s1, 6
                  bltu       sp, t5, 3561f
                  mul        s6, a3, a6
                  c.beqz     a4, 3567f
                  nop
3561:             sub        ra, a3, a5
                  ori        a6, a6, -505
                  slti       s5, s10, 554
                  slli       s11, t4, 21
                  .4byte 0x00100073 # ebreak
                  div        zero, t5, a1
3567:             slli       ra, gp, 12
                  c.andi     a2, 25
                  c.bnez     a0, 3588f
                  divu       s3, s7, zero
                  c.mv       s5, t4
                  ori        s2, s9, 105
                  c.srai     a2, 27
                  rem        s7, s2, a0
                  bltu       ra, s9, 3577f
                  beq        s4, t3, 3590f
3577:             c.bnez     a1, 3589f
                  c.and      a1, a0
                  csrrc      a0, 0x340, t0
                  mulh       a7, s6, s6
                  bgeu       s0, ra, 3594f
                  mulhsu     a7, a1, t2
                  mulhsu     a6, zero, s11
                  c.slli     a1, 8
                  add        t3, a4, a7
                  c.lui      a0, 31
                  sll        t4, a5, sp
3588:             c.li       s7, 28
3589:             bne        sp, s7, 3595f
3590:             auipc      t1, 230378
                  nop
                  mulhsu     s1, s6, t2
                  blt        s5, a3, 3607f
3594:             csrrwi     s5, 0x340, 13
3595:             c.andi     a3, -16
                  slt        s5, zero, s0
                  sltiu      t6, a3, 121
                  sltu       s6, a0, t2
                  divu       s2, s2, t4
                  .4byte 0x00100073 # ebreak
                  bgeu       s10, s1, 3603f
                  ori        t4, s8, 303
3603:             sltiu      a5, t4, 213
                  sltu       a2, t3, a4
                  c.add      tp, s10
                  c.mv       tp, a6
3607:             or         a1, t1, s10
                  mulh       s7, s2, s0
                  add        t1, a1, s1
                  c.or       a0, a4
                  bne        a4, s10, 3619f
                  csrrs      a1, 0x340, a2
                  bgeu       s8, a0, 3621f
                  c.li       t5, 3
                  c.addi     t4, -5
                  sltiu      ra, a7, -209
                  sub        a6, s5, a1
                  c.sub      a2, a1
3619:             srli       s7, sp, 18
                  xori       t6, s7, -317
3621:             ori        gp, s2, 291
                  c.andi     a1, 31
                  and        t1, s8, s1
                  c.addi     s11, -2
                  csrrsi     tp, 0x340, 2
                  blt        a0, ra, 3638f
                  c.nop
                  csrrs      s11, 0x340, s5
                  div        ra, s8, s11
                  srli       a2, s10, 31
                  csrrs      s10, 0x340, a1
                  c.ebreak;c.nop;
                  add        t5, t1, s4
                  c.addi     s0, -16
                  csrrsi     zero, 0x340, 11
                  andi       a5, a3, -669
                  div        a3, t5, t3
3638:             remu       t3, s2, s5
                  c.ebreak;c.nop;
                  xori       s0, gp, 850
                  sll        t2, zero, t2
                  csrrsi     a4, 0x340, 0
                  c.nop
                  mulh       t2, s3, s3
                  bltu       zero, s7, 3664f
                  mulh       s6, t4, a0
                  sltu       t3, a4, sp
                  c.or       s1, a5
                  bgeu       ra, t2, 3654f
                  c.and      s0, a5
                  c.ebreak;c.nop;
                  remu       a6, s7, s1
                  remu       s1, sp, s4
3654:             slt        s11, sp, gp
                  c.or       a1, a4
                  c.addi     a7, 31
                  lui        s5, 673487
                  mulhsu     gp, t6, tp
                  c.slli     tp, 30
                  mulhsu     t2, ra, gp
                  mulhsu     s2, zero, s7
                  add        t0, t1, a4
                  xor        s6, a3, s9
3664:             or         zero, a4, t3
                  bne        sp, sp, 3685f
                  csrrs      t0, 0x340, s1
                  c.slli     s6, 31
                  csrrwi     ra, 0x340, 8
                  csrrc      a4, 0x340, a3
                  and        tp, a1, s11
                  c.addi     t2, 30
                  auipc      t6, 542984
                  rem        a3, a4, t3
                  bltu       s7, t1, 3682f
                  csrrc      a0, 0x340, t6
                  sra        s1, sp, s9
                  add        s3, s4, s6
                  lui        t0, 62162
                  c.andi     a2, 9
                  c.xor      a4, a3
                  mulh       a3, s7, sp
3682:             .4byte 0x00100073 # ebreak
                  c.andi     s1, -29
                  csrrsi     s1, 0x340, 16
3685:             csrrsi     s4, 0x340, 29
                  slti       t6, a3, -480
                  bltu       zero, a7, 3707f
                  c.lui      t2, 13
                  nop
                  div        s6, s4, s1
                  c.xor      a4, a1
                  add        a0, t4, s3
                  bge        s11, a2, 3701f
                  bgeu       s1, s10, 3700f
                  c.or       a4, s0
                  csrrwi     s1, 0x340, 8
                  c.ebreak;c.nop;
                  bge        s8, a2, 3714f
                  c.slli     s6, 24
3700:             blt        t0, a1, 3712f
3701:             mulhu      s5, t6, s5
                  srli       t1, t6, 18
                  csrrsi     a0, 0x340, 21
                  slt        a7, s7, t5
                  andi       a2, t2, 89
                  sll        t1, zero, s0
3707:             srai       t3, ra, 10
                  nop
                  c.lui      t0, 16
                  slt        s0, ra, a4
                  bltu       s0, t2, 3715f
3712:             csrrw      a3, 0x340, zero
                  slt        s11, a3, t2
3714:             remu       a1, s4, s0
3715:             c.or       a2, a4
                  c.beqz     a3, 3734f
                  and        t0, s8, zero
                  and        a6, a2, s8
                  c.addi     a1, 14
                  c.slli     a5, 30
                  addi       s0, a4, -555
                  c.nop
                  mulhu      s0, a4, s10
                  beq        s0, s0, 3732f
                  div        a4, a1, s1
                  csrrsi     gp, 0x340, 10
                  mulhsu     a1, s6, s0
                  c.lui      t1, 16
                  c.and      a1, s0
                  c.addi     t2, 29
                  mulhsu     t1, ra, t1
3732:             c.srli     a0, 27
                  c.xor      a2, a5
3734:             div        s3, s10, a0
                  c.xor      a0, s0
                  bgeu       t6, a5, 3740f
                  beq        t4, t2, 3740f
                  c.slli     s1, 24
                  c.ebreak;c.nop;
3740:             xor        t5, tp, s8
                  c.add      s2, a6
                  sra        s2, a3, t5
                  lw         gp, 4(sp)
                  andi       a6, t4, -220
                  csrrc      s4, 0x340, ra
                  addi       sp, sp, 36
                  lui        t4, 773714
                  c.srli     a1, 18
                  slli       a4, t0, 23
                  srl        tp, a5, ra
                  ori        a2, t5, -627
6211:             c.jr x3
sub_3:            c.andi     a5, 30
                  csrrsi     a0, 0x340, 2
                  c.beqz     a2, sub_3_stack_p
sub_3_stack_p:    addi       sp, sp, -40
                  xor        s7, t2, t5
                  sw         gp, 4(sp)
                  and        a3, a7, a2
                  srai       t5, a3, 30
                  c.add      a0, t0
                  c.slli     s7, 6
                  addi       s1, s7, -423
                  la         a7, sub_4
                  c.lui      a1, 7
                  c.and      a0, s1
                  add        a5, a4, s2
                  addi       a7, a7, 254
                  sub        t3, s9, s10
                  lui        t2, 763957
                  csrrwi     s5, 0x340, 28
                  sltiu      a5, a4, -177
j_sub_3_sub_4_6:  jalr       gp, a7, -254
                  la         s2, region_1+886 #start riscv_load_store_rand_instr_stream_0
                  lbu        t6, -45(s2)
                  div        s7, s1, ra
                  mulhsu     s4, a7, s8
                  sltiu      gp, zero, -704
                  sw         s4, -26(s2)
                  lb         s10, -63(s2)
                  mulhsu     a2, t1, t1
                  lbu        a0, 32(s2)
                  sll        ra, tp, s8
                  c.mv       t0, ra
                  lbu        t0, 57(s2)
                  mul        t2, s6, t0
                  csrrwi     a6, 0x340, 6
                  lbu        t2, 31(s2)
                  c.slli     a0, 16
                  lhu        t2, 44(s2)
                  add        s0, ra, a4
                  lbu        tp, 11(s2)
                  c.and      a4, a1
                  sb         a5, 25(s2)
                  lbu        t2, 12(s2)
                  xor        a3, s8, s9
                  lbu        s3, 12(s2) #end riscv_load_store_rand_instr_stream_0
sub_3_1:          jal        gp, 10f
0:                c.jal      18f
1:                c.j        5f
2:                c.jal      6f
3:                c.j        20f
4:                jal        tp, 25f
5:                c.jal      0b
6:                jal        ra, 13f
7:                jal        ra, 27f
8:                jal        t4, 12f
9:                c.jal      1b
10:               c.jal      2b
11:               c.jal      16f
12:               c.j        14f
13:               jal        s5, 26f
14:               c.j        7b
15:               c.jal      8b
16:               jal        t1, 24f
17:               c.j        19f
18:               c.j        23f
19:               jal        s0, 21f
20:               c.jal      17b
21:               c.j        4b
22:               jal        ra, 9b
23:               c.jal      3b
24:               c.jal      22b
25:               c.jal      15b
26:               c.jal      11b
27:               sll        s1, a0, gp
                  la         t2, region_4+3322 #start load_store_instr_stream_1
                  la         tp, region_4+3186 #start load_store_instr_stream_0
                  sb         s4, -131(tp)
                  lhu        a7, 32(tp)
                  sb         s8, -45(tp)
                  lbu        t0, -26(t2)
                  lb         t5, -102(tp)
                  sb         t5, 14(tp)
                  lb         t4, 196(tp)
                  lbu        s3, 27(t2)
                  lhu        gp, -206(tp)
                  lhu        a0, -36(t2)
                  sb         s0, -43(t2)
                  lh         s6, -20(tp)
                  lhu        t3, -214(tp)
                  lbu        a5, 29(t2) #end load_store_instr_stream_1
                  lb         s0, -130(tp) #end load_store_instr_stream_0
                  addi       s1, zero, 10 #init loop 0 counter
                  c.srai     a3, 26
                  add        tp, s6, s2
                  addi       zero, zero, 0 #init loop 0 limit
sub_3_4_0_t:      sra        t4, tp, t2
                  srai       a3, ra, 20
                  mulhu      t5, s11, t0
                  c.ebreak;c.nop;
                  addi       s1, s1, -5 #update loop 0 counter
                  c.or       a2, a1
                  c.addi     s11, 19
                  csrrci     t2, 0x340, 25
                  sra        a6, a7, s11
                  c.bnez     s1, sub_3_4_0_t #branch for loop 0
                  sltu       t0, t1, s2
                  la         a1, region_3+87 #start load_store_instr_stream_0
                  la         t4, region_2+1844 #start load_store_instr_stream_1
                  lbu        t2, 11(a1)
                  lbu        zero, 50(t4)
                  lhu        s0, 5(a1)
                  lb         t6, 3(t4)
                  lbu        ra, -1(a1)
                  lbu        s5, -44(t4)
                  lw         s6, 12(t4)
                  lbu        s5, -63(t4)
                  sb         a1, -23(t4)
                  lh         s7, -7(a1)
                  sh         tp, -18(t4) #end load_store_instr_stream_1
                  lbu        s11, 9(a1) #end load_store_instr_stream_0
                  mulh       t4, a3, t3
                  srai       gp, tp, 3
                  c.slli     t6, 6
                  div        a1, t6, a7
                  bge        a0, t0, 18f
                  srl        s11, s1, s1
                  or         a7, t4, s0
                  c.addi     a6, -19
                  sltu       a2, ra, a6
                  bne        t4, ra, 24f
                  srli       a7, a0, 30
                  bltu       sp, a2, 23f
                  mulhsu     s6, a1, a7
                  c.xor      a1, s1
                  mulhu      a5, ra, s3
                  c.srai     s1, 13
                  c.nop
                  .4byte 0x00100073 # ebreak
18:               csrrw      s7, 0x340, sp
                  mulh       s10, tp, s4
                  mulhu      t2, a7, a6
                  c.mv       t5, a7
                  c.beqz     a1, 28f
23:               c.xor      a3, a1
24:               mul        t0, a6, a4
                  srli       tp, s6, 12
                  c.srli     a3, 23
                  srli       a0, s5, 23
28:               .4byte 0x00100073 # ebreak
                  c.ebreak;c.nop;
                  c.andi     a2, -5
                  add        a6, t3, a6
                  remu       t1, zero, a5
                  c.andi     a1, 21
                  sra        s11, a1, s4
                  divu       t2, sp, a3
                  bne        gp, a0, 41f
                  mul        s3, gp, s3
                  c.or       a0, a3
                  csrrci     s7, 0x340, 3
                  add        a0, s3, a7
41:               c.xor      a4, a0
                  blt        s1, a6, 57f
                  rem        a4, t3, s1
                  srai       s10, s5, 27
                  or         s4, s1, t4
                  c.bnez     a4, 55f
                  mulhu      t1, s7, gp
                  slt        gp, t4, s3
                  divu       s1, s8, t6
                  andi       a3, t3, -829
                  mulhsu     zero, s9, a7
                  bne        t3, ra, 65f
                  xor        s7, t4, sp
                  c.and      a0, a2
55:               c.lui      a7, 25
                  mulhu      a5, zero, ra
57:               or         gp, s10, t2
                  c.slli     a6, 13
                  sll        s7, ra, t1
                  c.ebreak;c.nop;
                  slli       a1, tp, 5
                  bgeu       a7, s6, 72f
                  c.xor      s1, a4
                  sltu       s11, s2, s7
65:               c.mv       ra, s5
                  bltu       a7, a7, 83f
                  csrrs      t4, 0x340, a4
                  lui        s3, 844062
                  nop
                  srai       s4, tp, 13
                  slti       s0, t2, 651
72:               or         t5, s8, s5
                  mul        tp, s2, s3
                  sltiu      zero, gp, -563
                  remu       a0, t2, gp
                  divu       a2, a3, a4
                  c.add      s5, s0
                  c.nop
                  divu       a4, gp, s4
                  ori        s10, ra, 30
                  csrrsi     t3, 0x340, 24
                  slt        t0, ra, sp
83:               c.bnez     a3, 92f
                  csrrwi     t5, 0x340, 5
                  csrrs      t6, 0x340, t4
                  c.addi     t6, 24
                  auipc      a4, 203769
                  c.srli     a5, 29
                  add        s7, s3, s8
                  c.sub      s0, a1
                  sltu       s11, t6, gp
92:               c.andi     a5, 23
                  andi       a1, s6, 579
                  c.slli     a3, 8
                  c.and      a0, a5
                  bge        s11, zero, 97f
97:               or         s0, t0, tp
                  mulh       a5, a6, s9
                  .4byte 0x00100073 # ebreak
                  xori       s7, s4, -426
                  beq        zero, s5, 121f
                  slti       t1, t3, 806
                  mul        s2, t3, a1
                  c.andi     a5, 0
                  la         a1, sub_5
                  andi       a0, zero, -109
                  sll        t1, a0, s8
                  addi       a1, a1, -290
                  add        a4, s4, a5
                  c.andi     a2, -6
j_sub_3_sub_5_5:  jalr       gp, a1, 290
                  srli       s5, t1, 30
                  csrrs      ra, 0x340, s10
                  c.or       a5, s1
                  or         t1, t5, t4
                  auipc      a3, 687135
                  xori       tp, a7, -654
                  bne        s3, s11, 119f
                  csrrsi     s0, 0x340, 4
                  lui        t6, 770690
                  auipc      tp, 463171
                  mulhsu     a4, a4, s2
                  c.xor      a2, a1
                  srli       t1, t4, 29
                  mulhu      s6, a1, a4
                  divu       a3, s11, a4
                  mulh       s5, a3, a0
                  or         ra, t3, s8
119:              auipc      t3, 140397
                  c.or       a3, s0
121:              sll        s5, a3, a0
                  bgeu       gp, s0, 135f
                  xor        s2, s8, t6
                  slt        t1, s9, t4
                  and        a7, s5, s1
                  bne        sp, t3, 133f
                  xor        s7, t4, ra
                  mul        s7, t6, s11
                  c.slli     ra, 1
                  and        a0, s8, s5
                  c.slli     t0, 22
                  c.ebreak;c.nop;
133:              bge        gp, a7, 147f
                  sltu       s0, gp, a3
135:              nop
                  c.slli     a5, 15
                  mulhu      s10, t6, s0
                  bltu       zero, t3, 147f
                  xori       s11, tp, 2
                  csrrc      a3, 0x340, a5
                  c.nop
                  c.bnez     a1, 144f
                  c.or       a4, s1
144:              xori       a3, t6, 544
                  bge        a6, s11, 162f
                  bltu       s3, t0, 166f
147:              or         t6, s11, s0
                  c.srai     a3, 16
                  c.nop
                  c.beqz     a4, 160f
                  c.mv       a0, s8
                  andi       s4, s10, -253
                  srai       s10, t5, 26
                  or         t1, s2, t2
                  c.lui      a3, 6
                  c.mv       s1, s5
                  la         s4, region_4+1991 #start riscv_hazard_instr_stream_0
                  lbu        t1, 184(s4)
                  lb         t5, 134(s4)
                  lbu        a7, 192(s4)
                  lb         t1, -76(s4)
                  lhu        t6, 89(s4)
                  lb         a7, 44(s4)
                  lbu        a1, -75(s4)
                  lb         t1, -98(s4)
                  lb         a1, -206(s4)
                  c.srai     s0, 2
                  lb         a1, -7(s4)
                  divu       a7, a1, a1
                  lbu        a1, -6(s4)
                  lw         a7, 125(s4)
                  lb         a1, -162(s4)
                  lbu        a7, -42(s4)
                  andi       t6, s0, 512
                  c.lui      a7, 6
                  sb         a7, 138(s4)
                  nop
                  lbu        s0, 3(s4)
                  and        t1, a7, t6
                  lbu        a7, -248(s4)
                  mulh       t5, t1, t5
                  sb         a7, 248(s4)
                  or         a1, t5, t5
                  sw         a7, -139(s4)
                  lw         a7, 25(s4)
                  lbu        a7, 200(s4)
                  lb         t5, 176(s4)
                  lbu        a7, -133(s4)
                  lb         t1, 120(s4)
                  lbu        a7, 68(s4)
                  sb         a1, 82(s4)
                  c.add      t1, a1
                  lbu        t1, 196(s4)
                  c.nop
                  sltu       a1, a7, a7
                  sra        t5, s0, s0
                  lbu        t6, 38(s4)
                  lb         t5, -164(s4) #end riscv_hazard_instr_stream_0
                  c.slli     a0, 13
                  csrrwi     s3, 0x340, 27
                  mulh       a7, s9, t0
160:              mulh       s4, s0, t6
                  c.ebreak;c.nop;
162:              csrrw      s11, 0x340, t2
                  c.li       s11, -11
                  c.and      a5, a5
                  xori       a6, a1, 166
166:              andi       t5, zero, 395
                  divu       a4, t2, t1
                  add        s3, t4, a0
                  and        s1, s9, a5
                  c.nop
                  mulhsu     a5, s3, s9
                  sra        t4, a0, s2
                  or         a5, a2, gp
                  c.addi     s4, -24
                  c.srli     a4, 23
                  slti       t3, t3, 302
                  bltu       a3, s1, 178f
178:              c.and      a0, a2
                  sra        t4, a7, ra
                  csrrw      t3, 0x340, s7
                  add        s1, s5, a1
                  beq        s8, t4, 190f
                  c.sub      a2, s1
                  blt        s10, a2, 201f
                  sltiu      a2, s0, 903
                  c.bnez     a5, 195f
                  c.slli     a0, 23
                  c.srli     a1, 31
                  c.xor      a1, a1
190:              xor        a3, t3, a1
                  div        tp, tp, t5
                  sub        s5, s5, a0
                  csrrwi     a6, 0x340, 20
                  c.nop
195:              c.sub      a0, a4
                  or         s1, t0, s2
                  slli       t2, tp, 2
                  c.srli     a2, 3
                  csrrs      s10, 0x340, a1
                  mulhsu     a7, t6, ra
201:              mulhu      s6, s7, t1
                  c.or       a1, s0
                  csrrci     t6, 0x340, 19
                  divu       s2, t1, s9
                  c.lui      a2, 22
                  or         t0, s10, s0
                  lui        s10, 496633
                  c.andi     a0, -1
                  mulhsu     s7, a7, s7
                  mulh       a6, s11, ra
                  rem        s2, gp, a3
                  c.li       a6, -23
                  sub        a3, t0, s7
                  c.or       a4, a0
                  c.li       gp, 2
                  csrrsi     t3, 0x340, 18
                  c.andi     a1, -18
                  div        a5, s3, s5
                  c.addi     a4, 13
                  mulhu      s4, s10, s11
                  c.ebreak;c.nop;
                  c.or       a4, a0
                  bge        a2, zero, 231f
                  mulhu      a3, a4, a7
                  c.li       a6, 24
                  remu       s0, zero, s4
                  bltu       a2, a6, 230f
                  slt        s2, a2, t0
                  c.ebreak;c.nop;
230:              mul        t0, t2, a3
231:              add        zero, s0, s2
                  c.slli     a2, 1
                  mul        a2, t6, sp
                  nop
                  blt        t0, a6, 242f
                  nop
                  c.addi     s1, -22
                  .4byte 0x00100073 # ebreak
                  csrrw      t1, 0x340, s11
                  sra        s3, a5, t4
                  c.mv       s3, tp
242:              divu       a6, s9, t2
                  srai       ra, a3, 18
                  csrrs      zero, 0x340, sp
                  sltu       a5, t0, s7
                  c.or       s0, s0
                  bltu       a2, s9, 254f
                  csrrs      a2, 0x340, gp
                  c.li       t0, 10
                  addi       s11, s2, -6
                  slli       t6, t1, 18
                  or         a5, s2, a1
                  c.srli     a2, 30
254:              c.slli     a6, 25
                  mulh       a5, a5, t6
                  remu       s4, a2, s0
                  c.add      a0, sp
                  slli       a3, t3, 16
                  bge        s9, a7, 261f
                  mulhu      a2, a4, a2
261:              sltu       t5, s6, s1
                  addi       s2, ra, 358
                  c.xor      s0, s1
                  xor        s10, t0, t6
                  mul        t4, a4, s7
                  ori        t4, s7, 776
                  c.add      a4, s1
                  mulh       s11, a7, a0
                  slti       s6, s1, -222
                  mulhu      zero, t4, t5
                  slt        s2, a7, a6
                  slti       tp, s2, 479
                  c.sub      a0, a5
                  sll        s0, s5, t6
                  andi       s5, s8, 295
                  or         t6, t3, a4
                  remu       t2, gp, s0
                  bne        s0, t5, 286f
                  ori        a2, s1, -249
                  slt        a7, a7, t5
                  csrrw      s3, 0x340, s9
                  blt        s7, t5, 294f
                  c.xor      a0, a0
                  c.andi     a5, -5
                  sub        t2, s2, s0
286:              c.bnez     a3, 295f
                  csrrwi     ra, 0x340, 20
                  c.addi     gp, 21
                  c.slli     t0, 12
                  mulh       s10, a3, s8
                  mulhu      s7, t5, t1
                  mulhsu     s3, t2, a3
                  c.lui      a3, 9
294:              c.add      s11, a4
295:              addi       t4, a7, -494
                  csrrc      t6, 0x340, a7
                  csrrci     t5, 0x340, 28
                  auipc      t5, 800478
                  mulhu      s7, s5, gp
                  blt        t3, s2, 320f
                  mulhsu     ra, a5, s8
                  c.li       gp, -3
                  addi       s5, s3, 354
                  la         s11, sub_4
                  addi       s11, s11, 414
                  bltu       tp, a1, j_sub_3_sub_4_4 #branch to jump instr
                  divu       s3, a4, t6
                  c.addi     t2, -6
                  c.mv       t3, s11
                  slli       s7, a4, 0
j_sub_3_sub_4_4:  jalr       gp, s11, -414
                  add        a7, a6, zero
                  c.ebreak;c.nop;
                  c.and      a3, s0
                  .4byte 0x00100073 # ebreak
                  sll        t1, t3, t2
                  xori       a5, a7, 216
                  xori       gp, sp, 150
                  c.sub      a1, a2
                  mulh       s0, t1, s6
                  bne        t4, a6, 330f
                  c.mv       a4, sp
                  remu       s2, s8, s0
                  csrrw      s11, 0x340, a6
                  mulh       zero, s9, s3
                  addi       t3, zero, 96
                  bltu       zero, s0, 323f
                  addi       s6, t4, 608
                  blt        a4, t2, 333f
                  xor        a7, t0, t1
320:              srai       t1, a1, 31
                  remu       s4, s5, a7
                  mulhsu     t5, t4, a5
323:              c.or       a3, a3
                  bltu       s10, t5, 341f
                  c.bnez     a0, 334f
                  rem        ra, s7, tp
                  c.beqz     a2, 341f
                  c.nop
                  c.sub      a5, a0
330:              c.srai     a5, 13
                  c.nop
                  csrrci     a4, 0x340, 24
333:              slli       t5, a6, 7
334:              nop
                  c.and      a1, a4
                  c.lui      s6, 28
                  mulh       a2, a7, a6
                  nop
                  .4byte 0x00100073 # ebreak
                  bltu       t3, t4, 346f
341:              c.ebreak;c.nop;
                  csrrsi     zero, 0x340, 17
                  lui        a3, 648945
                  c.lui      t0, 26
                  c.srli     a3, 4
346:              bltu       s11, s2, 363f
                  sltu       a3, s9, sp
                  c.add      a6, t1
                  addi       s0, a4, -489
                  c.andi     a2, 0
                  mulhsu     a2, s5, sp
                  bgeu       s3, gp, 359f
                  xor        s0, t0, t0
                  remu       t4, t5, s5
                  remu       t2, t2, s2
                  c.add      a2, a3
                  lui        s0, 907554
                  add        a5, s5, s5
359:              xor        tp, t1, s4
                  divu       t0, t3, a0
                  c.or       s0, a2
                  c.or       a1, a0
363:              c.beqz     a0, 368f
                  srai       s7, a7, 13
                  csrrwi     s11, 0x340, 24
                  c.bnez     a5, 381f
                  divu       a7, t6, t0
368:              csrrs      ra, 0x340, tp
                  csrrwi     a4, 0x340, 31
                  c.srli     a3, 31
                  nop
                  bltu       t0, zero, 380f
                  c.and      a0, s1
                  mulhsu     t3, t4, a7
                  c.xor      a4, s0
                  c.srai     a5, 31
                  c.add      t1, s0
                  mulhsu     gp, t3, a2
                  srai       s10, s9, 27
380:              sub        t2, a5, s10
381:              bltu       t2, a0, 395f
                  bgeu       a1, ra, 391f
                  c.bnez     a5, 384f
384:              mul        t1, s0, a3
                  c.ebreak;c.nop;
                  nop
                  csrrsi     t0, 0x340, 13
                  sub        a6, a6, a3
                  srai       t4, s8, 14
                  c.bnez     s1, 403f
391:              csrrc      s1, 0x340, s11
                  c.srai     a5, 30
                  csrrs      a4, 0x340, s1
                  c.lui      t3, 9
395:              c.nop
                  sub        a0, s5, s10
                  or         t3, gp, a0
                  c.sub      a5, a1
                  .4byte 0x00100073 # ebreak
                  bge        a2, a7, 413f
                  c.bnez     a2, 404f
                  auipc      s5, 901029
403:              xori       a3, t6, -778
404:              csrrw      a6, 0x340, s5
                  sra        zero, a5, t3
                  slli       s1, t0, 21
                  mulhu      s3, t2, a1
                  add        s4, s1, a3
                  or         t4, a6, a0
                  csrrc      s2, 0x340, s8
                  mulhu      a6, s9, s8
                  c.li       a0, 10
413:              c.li       t4, 12
                  rem        a2, t2, s6
                  slli       s1, a4, 17
                  sltiu      t2, s4, 432
                  mulh       t4, a6, a7
                  sub        s4, ra, a6
                  or         s10, a7, a3
                  c.addi     a7, 11
                  and        s0, t5, t4
                  c.beqz     s0, 433f
                  .4byte 0x00100073 # ebreak
                  blt        a1, t1, 425f
425:              remu       a6, t0, a5
                  mulhu      tp, a5, s8
                  csrrwi     t3, 0x340, 7
                  c.sub      a3, a1
                  c.or       a2, a1
                  or         a5, s2, s3
                  .4byte 0x00100073 # ebreak
                  sll        ra, tp, a7
433:              xori       t3, t0, -5
                  sub        s6, t5, a0
                  and        s1, s10, s9
                  c.and      a5, a4
                  csrrw      t4, 0x340, s5
                  nop
                  c.beqz     a5, 449f
                  c.li       t2, 15
                  auipc      s1, 489914
                  csrrc      t2, 0x340, a5
                  add        s10, tp, s1
                  csrrci     a3, 0x340, 26
                  c.slli     s11, 31
                  slti       t0, s1, 956
                  c.mv       a0, a2
                  lui        t1, 966445
449:              xori       t3, zero, 466
                  xor        a6, s0, a6
                  c.and      a1, a3
                  csrrci     s7, 0x340, 1
                  c.andi     a4, -27
                  srl        gp, sp, s7
                  div        s4, t3, a1
                  sub        t6, a7, s3
                  c.add      s2, s0
                  sub        t5, zero, t2
                  sra        t0, s1, a0
                  xori       a6, sp, 887
                  csrrw      ra, 0x340, t0
                  srai       a5, a4, 10
                  lui        a0, 409468
                  c.li       s0, 6
                  lw         gp, 4(sp)
                  addi       sp, sp, 40
                  andi       t1, tp, 957
                  rem        a7, s5, t3
                  xori       s2, ra, 102
                  c.slli     a5, 22
654:              c.jr x3
write_tohost:     
                  sw gp, tohost, t5

_exit:            
                  li a0, 0x20000004
                  li a1, 0
                  sw a1, 0(a0)
                  j write_tohost

init_machine_mode:
                  li x4, 0x101800
                  csrw 0x300, x4 # MSTATUS
                  li x4, 0x0
                  csrw 0x304, x4 # MIE
                  mret
.data
.pushsection .tohost,"aw",@progbits;
.align 6; .global tohost; tohost: .dword 0;
.align 6; .global fromhost; fromhost: .dword 0;
.popsection;
.pushsection .region_0,"aw",@progbits;
region_0:
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.popsection;
.pushsection .region_1,"aw",@progbits;
region_1:
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.popsection;
.pushsection .region_2,"aw",@progbits;
region_2:
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.popsection;
.pushsection .region_3,"aw",@progbits;
region_3:
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.popsection;
.pushsection .region_4,"aw",@progbits;
region_4:
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.word 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f
.word 0x20212223, 0x24252627, 0x28292a2b, 0x2c2d2e2f, 0x30313233, 0x34353637, 0x38393a3b, 0x3c3d3e3f
.word 0x40414243, 0x44454647, 0x48494a4b, 0x4c4d4e4f, 0x50515253, 0x54555657, 0x58595a5b, 0x5c5d5e5f
.word 0x60616263, 0x64656667, 0x68696a6b, 0x6c6d6e6f, 0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f
.word 0x80818283, 0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90919293, 0x94959697, 0x98999a9b, 0x9c9d9e9f
.word 0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab, 0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7, 0xb8b9babb, 0xbcbdbebf
.word 0xc0c1c2c3, 0xc4c5c6c7, 0xc8c9cacb, 0xcccdcecf, 0xd0d1d2d3, 0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf
.word 0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff
.popsection;
.align 4;
.pushsection .user_stack,"aw",@progbits;
.align 12
_user_stack_start:
.rept 4999
.4byte 0x0
.endr
_user_stack_end:
.4byte 0x0
.popsection;
_kernel_instr_start: .align 12
.text
.align 12
mtvec_handler:    
                  csrrw x2, 0x340, x2
                  add x2, x24, zero
                  1: addi x2, x2, -124
                  sw  x1, 4(x2)
                  sw  x2, 8(x2)
                  sw  x3, 12(x2)
                  sw  x4, 16(x2)
                  sw  x5, 20(x2)
                  sw  x6, 24(x2)
                  sw  x7, 28(x2)
                  sw  x8, 32(x2)
                  sw  x9, 36(x2)
                  sw  x10, 40(x2)
                  sw  x11, 44(x2)
                  sw  x12, 48(x2)
                  sw  x13, 52(x2)
                  sw  x14, 56(x2)
                  sw  x15, 60(x2)
                  sw  x16, 64(x2)
                  sw  x17, 68(x2)
                  sw  x18, 72(x2)
                  sw  x19, 76(x2)
                  sw  x20, 80(x2)
                  sw  x21, 84(x2)
                  sw  x22, 88(x2)
                  sw  x23, 92(x2)
                  sw  x24, 96(x2)
                  sw  x25, 100(x2)
                  sw  x26, 104(x2)
                  sw  x27, 108(x2)
                  sw  x28, 112(x2)
                  sw  x29, 116(x2)
                  sw  x30, 120(x2)
                  sw  x31, 124(x2)
                  csrr x4, 0x342 # MCAUSE
                  srli x4, x4, 31
                  bne x4, x0, mmode_intr_handler

mmode_exception_handler:
                  csrr x4, 0x341 # MEPC
                  csrr x4, 0x342 # MCAUSE
                  li x7, 0x3 # BREAKPOINT
                  beq x4, x7, ebreak_handler
                  li x7, 0x8 # ECALL_UMODE
                  beq x4, x7, ecall_handler
                  li x7, 0x9 # ECALL_SMODE
                  beq x4, x7, ecall_handler
                  li x7, 0xb # ECALL_MMODE
                  beq x4, x7, ecall_handler
                  li x7, 0x1
                  beq x4, x7, instr_fault_handler
                  li x7, 0x5
                  beq x4, x7, load_fault_handler
                  li x7, 0x7
                  beq x4, x7, store_fault_handler
                  li x7, 0xc
                  beq x4, x7, pt_fault_handler
                  li x7, 0xd
                  beq x4, x7, pt_fault_handler
                  li x7, 0xf
                  beq x4, x7, pt_fault_handler
                  li x7, 0x2 # ILLEGAL_INSTRUCTION
                  beq x4, x7, illegal_instr_handler
                  csrr x7, 0x343 # MTVAL
                  1: jal x1, test_done 

ebreak_handler:   
                  csrr  x4, mepc
                  addi  x4, x4, 4
                  csrw  mepc, x4
                  lw  x1, 4(x2)
                  lw  x2, 8(x2)
                  lw  x3, 12(x2)
                  lw  x4, 16(x2)
                  lw  x5, 20(x2)
                  lw  x6, 24(x2)
                  lw  x7, 28(x2)
                  lw  x8, 32(x2)
                  lw  x9, 36(x2)
                  lw  x10, 40(x2)
                  lw  x11, 44(x2)
                  lw  x12, 48(x2)
                  lw  x13, 52(x2)
                  lw  x14, 56(x2)
                  lw  x15, 60(x2)
                  lw  x16, 64(x2)
                  lw  x17, 68(x2)
                  lw  x18, 72(x2)
                  lw  x19, 76(x2)
                  lw  x20, 80(x2)
                  lw  x21, 84(x2)
                  lw  x22, 88(x2)
                  lw  x23, 92(x2)
                  lw  x24, 96(x2)
                  lw  x25, 100(x2)
                  lw  x26, 104(x2)
                  lw  x27, 108(x2)
                  lw  x28, 112(x2)
                  lw  x29, 116(x2)
                  lw  x30, 120(x2)
                  lw  x31, 124(x2)
                  addi x2, x2, 124
                  add x24, x2, zero
                  csrrw x2, 0x340, x2
                  mret

ecall_handler:    
                  la x4, _start
                  sw x0, 0(x4)
                  sw x1, 4(x4)
                  sw x2, 8(x4)
                  sw x3, 12(x4)
                  sw x4, 16(x4)
                  sw x5, 20(x4)
                  sw x6, 24(x4)
                  sw x7, 28(x4)
                  sw x8, 32(x4)
                  sw x9, 36(x4)
                  sw x10, 40(x4)
                  sw x11, 44(x4)
                  sw x12, 48(x4)
                  sw x13, 52(x4)
                  sw x14, 56(x4)
                  sw x15, 60(x4)
                  sw x16, 64(x4)
                  sw x17, 68(x4)
                  sw x18, 72(x4)
                  sw x19, 76(x4)
                  sw x20, 80(x4)
                  sw x21, 84(x4)
                  sw x22, 88(x4)
                  sw x23, 92(x4)
                  sw x24, 96(x4)
                  sw x25, 100(x4)
                  sw x26, 104(x4)
                  sw x27, 108(x4)
                  sw x28, 112(x4)
                  sw x29, 116(x4)
                  sw x30, 120(x4)
                  sw x31, 124(x4)
                  j write_tohost
illegal_instr_handler:
                  csrr  x4, mepc
                  addi  x4, x4, 4
                  csrw  mepc, x4
                  lw  x1, 4(x2)
                  lw  x2, 8(x2)
                  lw  x3, 12(x2)
                  lw  x4, 16(x2)
                  lw  x5, 20(x2)
                  lw  x6, 24(x2)
                  lw  x7, 28(x2)
                  lw  x8, 32(x2)
                  lw  x9, 36(x2)
                  lw  x10, 40(x2)
                  lw  x11, 44(x2)
                  lw  x12, 48(x2)
                  lw  x13, 52(x2)
                  lw  x14, 56(x2)
                  lw  x15, 60(x2)
                  lw  x16, 64(x2)
                  lw  x17, 68(x2)
                  lw  x18, 72(x2)
                  lw  x19, 76(x2)
                  lw  x20, 80(x2)
                  lw  x21, 84(x2)
                  lw  x22, 88(x2)
                  lw  x23, 92(x2)
                  lw  x24, 96(x2)
                  lw  x25, 100(x2)
                  lw  x26, 104(x2)
                  lw  x27, 108(x2)
                  lw  x28, 112(x2)
                  lw  x29, 116(x2)
                  lw  x30, 120(x2)
                  lw  x31, 124(x2)
                  addi x2, x2, 124
                  add x24, x2, zero
                  csrrw x2, 0x340, x2
                  mret

instr_fault_handler:
                  lw  x1, 4(x2)
                  lw  x2, 8(x2)
                  lw  x3, 12(x2)
                  lw  x4, 16(x2)
                  lw  x5, 20(x2)
                  lw  x6, 24(x2)
                  lw  x7, 28(x2)
                  lw  x8, 32(x2)
                  lw  x9, 36(x2)
                  lw  x10, 40(x2)
                  lw  x11, 44(x2)
                  lw  x12, 48(x2)
                  lw  x13, 52(x2)
                  lw  x14, 56(x2)
                  lw  x15, 60(x2)
                  lw  x16, 64(x2)
                  lw  x17, 68(x2)
                  lw  x18, 72(x2)
                  lw  x19, 76(x2)
                  lw  x20, 80(x2)
                  lw  x21, 84(x2)
                  lw  x22, 88(x2)
                  lw  x23, 92(x2)
                  lw  x24, 96(x2)
                  lw  x25, 100(x2)
                  lw  x26, 104(x2)
                  lw  x27, 108(x2)
                  lw  x28, 112(x2)
                  lw  x29, 116(x2)
                  lw  x30, 120(x2)
                  lw  x31, 124(x2)
                  addi x2, x2, 124
                  add x24, x2, zero
                  csrrw x2, 0x340, x2
                  mret

load_fault_handler:
                  lw  x1, 4(x2)
                  lw  x2, 8(x2)
                  lw  x3, 12(x2)
                  lw  x4, 16(x2)
                  lw  x5, 20(x2)
                  lw  x6, 24(x2)
                  lw  x7, 28(x2)
                  lw  x8, 32(x2)
                  lw  x9, 36(x2)
                  lw  x10, 40(x2)
                  lw  x11, 44(x2)
                  lw  x12, 48(x2)
                  lw  x13, 52(x2)
                  lw  x14, 56(x2)
                  lw  x15, 60(x2)
                  lw  x16, 64(x2)
                  lw  x17, 68(x2)
                  lw  x18, 72(x2)
                  lw  x19, 76(x2)
                  lw  x20, 80(x2)
                  lw  x21, 84(x2)
                  lw  x22, 88(x2)
                  lw  x23, 92(x2)
                  lw  x24, 96(x2)
                  lw  x25, 100(x2)
                  lw  x26, 104(x2)
                  lw  x27, 108(x2)
                  lw  x28, 112(x2)
                  lw  x29, 116(x2)
                  lw  x30, 120(x2)
                  lw  x31, 124(x2)
                  addi x2, x2, 124
                  add x24, x2, zero
                  csrrw x2, 0x340, x2
                  mret

store_fault_handler:
                  lw  x1, 4(x2)
                  lw  x2, 8(x2)
                  lw  x3, 12(x2)
                  lw  x4, 16(x2)
                  lw  x5, 20(x2)
                  lw  x6, 24(x2)
                  lw  x7, 28(x2)
                  lw  x8, 32(x2)
                  lw  x9, 36(x2)
                  lw  x10, 40(x2)
                  lw  x11, 44(x2)
                  lw  x12, 48(x2)
                  lw  x13, 52(x2)
                  lw  x14, 56(x2)
                  lw  x15, 60(x2)
                  lw  x16, 64(x2)
                  lw  x17, 68(x2)
                  lw  x18, 72(x2)
                  lw  x19, 76(x2)
                  lw  x20, 80(x2)
                  lw  x21, 84(x2)
                  lw  x22, 88(x2)
                  lw  x23, 92(x2)
                  lw  x24, 96(x2)
                  lw  x25, 100(x2)
                  lw  x26, 104(x2)
                  lw  x27, 108(x2)
                  lw  x28, 112(x2)
                  lw  x29, 116(x2)
                  lw  x30, 120(x2)
                  lw  x31, 124(x2)
                  addi x2, x2, 124
                  add x24, x2, zero
                  csrrw x2, 0x340, x2
                  mret

pt_fault_handler: 
                  nop

.align 12
mmode_intr_handler:
                  csrr  x4, 0x300 # MSTATUS;
                  csrr  x4, 0x304 # MIE;
                  csrr  x4, 0x344 # MIP;
                  csrrc x4, 0x344, x4 # MIP;
                  lw  x1, 4(x2)
                  lw  x2, 8(x2)
                  lw  x3, 12(x2)
                  lw  x4, 16(x2)
                  lw  x5, 20(x2)
                  lw  x6, 24(x2)
                  lw  x7, 28(x2)
                  lw  x8, 32(x2)
                  lw  x9, 36(x2)
                  lw  x10, 40(x2)
                  lw  x11, 44(x2)
                  lw  x12, 48(x2)
                  lw  x13, 52(x2)
                  lw  x14, 56(x2)
                  lw  x15, 60(x2)
                  lw  x16, 64(x2)
                  lw  x17, 68(x2)
                  lw  x18, 72(x2)
                  lw  x19, 76(x2)
                  lw  x20, 80(x2)
                  lw  x21, 84(x2)
                  lw  x22, 88(x2)
                  lw  x23, 92(x2)
                  lw  x24, 96(x2)
                  lw  x25, 100(x2)
                  lw  x26, 104(x2)
                  lw  x27, 108(x2)
                  lw  x28, 112(x2)
                  lw  x29, 116(x2)
                  lw  x30, 120(x2)
                  lw  x31, 124(x2)
                  addi x2, x2, 124
                  add x24, x2, zero
                  csrrw x2, 0x340, x2
                  mret;

_kernel_instr_end: nop
.pushsection .kernel_stack,"aw",@progbits;
.align 12
_kernel_stack_start:
.rept 3999
.4byte 0x0
.endr
_kernel_stack_end:
.4byte 0x0
.popsection;
