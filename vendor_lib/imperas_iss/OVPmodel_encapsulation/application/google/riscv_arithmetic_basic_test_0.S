# Google UVM Generated Test

.globl _start
.section .text
.include "user_define.h"
.option norvc;
_start:
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
                  li x4, 0x40000100
                  csrw misa, x4
kernel_sp:
                  la x24, _kernel_stack_end

trap_vec_init:
                  la x4, mtvec_handler
                  ori x4, x4, 1
                  csrw 0x305, x4 # MTVEC

mepc_setup:
                  la x4, _init
                  csrw mepc, x4
                  j init_machine_mode

_init:
                  la x2, _user_stack_end
_main:            ori        s11, a4, 196
                  or         t4, s11, s11
                  slt        a0, t4, t6
                  sll        a1, s6, s2
                  and        a5, s11, a4
                  andi       t0, a6, 148
                  and        a2, t3, gp
                  and        s11, ra, t3
                  and        a4, s8, s3
                  andi       a1, s7, 68
                  sll        a7, t3, s9
                  sltu       a4, s5, s0
                  sub        t3, t5, s9
                  or         tp, t0, s8
                  sltu       gp, s3, gp
                  slti       a5, a5, -253
                  sub        a1, t3, tp
                  auipc      s5, 469948
                  sub        gp, sp, a3
                  slt        a0, t3, s6
                  srli       a3, a1, 16
                  xori       a6, ra, -847
                  sltiu      s11, s1, 227
                  xori       a5, s11, -652
                  and        t6, t4, a5
                  slti       s11, t2, 373
                  xori       t2, s7, -312
                  slt        a6, t5, t1
                  ori        t5, zero, 715
                  srli       t0, s1, 26
                  slli       s3, a0, 8
                  lui        t0, 584794
                  andi       t0, s11, -940
                  sltu       s2, s1, a0
                  slt        s6, sp, gp
                  sltiu      a4, s8, 818
                  sltu       s10, t3, t0
                  sub        s1, t5, t3
                  srli       s2, a3, 23
                  sll        a0, t6, s0
                  and        a2, zero, a0
                  ori        t4, s2, -108
                  xori       t2, s7, -314
                  xor        a4, a1, s7
                  lui        a6, 299001
                  sltiu      t3, t3, -893
                  xor        tp, s8, zero
                  andi       s6, t5, 796
                  sltiu      a3, t0, 701
                  slli       a5, t6, 11
                  srl        a4, s5, zero
                  ori        zero, t3, 242
                  sll        s7, zero, t3
                  sltiu      s2, t5, 792
                  nop
                  slti       zero, a4, -135
                  ori        ra, s10, 836
                  srl        a3, a5, s4
                  auipc      s4, 993269
                  xori       gp, t3, -551
                  lui        s6, 499376
                  srai       gp, ra, 21
                  sll        t6, zero, t2
                  auipc      a5, 92041
                  nop
                  or         s10, a0, s8
                  or         s11, t2, a6
                  slti       s4, s1, 233
                  srli       t4, a6, 1
                  sra        s0, t3, s5
                  srl        s3, tp, t4
                  sub        s0, t6, a6
                  srai       s2, a5, 28
                  slt        s1, ra, a4
                  slli       s5, a0, 0
                  sub        a6, a1, tp
                  slti       s6, a7, 392
                  sltu       t5, s10, a6
                  and        a0, a6, a3
                  sltu       t1, a7, t1
                  slli       s6, s2, 8
                  slt        s5, t3, t4
                  slti       s3, t4, 793
                  slt        a0, t0, t4
                  nop
                  slli       t3, s1, 23
                  slli       a0, ra, 5
                  auipc      s4, 686587
                  srai       gp, s10, 9
                  andi       a2, t0, 294
                  sra        a5, sp, a1
                  addi       gp, a1, 215
                  srai       a2, a4, 14
                  or         t0, t4, s9
                  andi       s4, s10, -503
                  slli       s7, s10, 25
                  srl        t4, a6, ra
                  or         s10, a5, sp
                  xori       s10, ra, 700
                  nop
                  slli       s5, tp, 8
                  ori        s3, s6, -893
                  sll        ra, s5, t2
                  srli       ra, a7, 2
                  slli       a3, t1, 8
                  addi       s1, t2, -117
                  xori       tp, a4, 985
                  add        a7, s5, s6
                  slli       a4, a1, 31
                  srli       ra, s8, 12
                  lui        a1, 406288
                  srl        a5, s11, s4
                  xori       t1, s4, -98
                  xor        gp, s6, a7
                  nop
                  xor        a6, s0, a7
                  slt        t3, t0, a6
                  ori        s3, s0, 733
                  andi       t1, zero, 654
                  lui        s4, 894631
                  sub        gp, t4, ra
                  srai       tp, s8, 23
                  sltiu      s4, t3, -670
                  srli       s1, s11, 28
                  sltiu      s10, s0, 785
                  ori        t0, s11, 1018
                  ori        s5, t3, -893
                  slti       s1, t0, -230
                  andi       a0, s7, 811
                  andi       a0, t6, -250
                  andi       s6, t5, -899
                  slti       t3, a3, -401
                  or         s0, s11, s10
                  srli       a3, t5, 21
                  and        s1, t2, t2
                  srli       s11, a3, 16
                  sub        s6, a5, gp
                  sltu       a1, a1, s7
                  xori       a6, a5, 224
                  sra        a3, a4, a1
                  andi       tp, s11, 698
                  slti       s0, t6, 458
                  sll        t4, s2, t1
                  srl        a0, s7, a6
                  sll        gp, a3, t3
                  addi       s7, t5, -11
                  srli       s5, s1, 28
                  and        s3, a2, t5
                  srai       t6, a4, 8
                  xori       a4, s9, -242
                  nop
                  lui        s5, 137896
                  auipc      a3, 59471
                  add        a3, a3, a2
                  slt        s5, tp, a7
                  xor        zero, t1, s1
                  ori        a2, s8, -575
                  sll        a3, s7, s11
                  sltiu      t0, ra, 887
                  or         t6, tp, s2
                  srli       tp, s8, 23
                  nop
                  or         ra, a2, ra
                  andi       s4, a7, 481
                  lui        s5, 131088
                  or         t4, a1, s1
                  srl        a7, s11, t4
                  auipc      s6, 514664
                  sltiu      s6, a0, 346
                  sltiu      a7, s3, -815
                  slti       a4, t5, -330
                  andi       s7, a5, 235
                  lui        a5, 370779
                  sltu       ra, s1, a0
                  srai       a0, s1, 5
                  and        a1, a5, tp
                  addi       t4, t4, -927
                  lui        a5, 480380
                  addi       a7, t6, -757
                  andi       s11, sp, -292
                  sltiu      s6, a1, 974
                  xori       t5, gp, -792
                  sub        t6, gp, t1
                  srl        s7, a7, a7
                  or         a6, s3, s8
                  srl        a2, a0, s7
                  or         tp, zero, a3
                  or         a5, s1, s10
                  srai       a3, s7, 31
                  and        s6, t3, s2
                  nop
                  and        t3, ra, a2
                  xori       a4, sp, -550
                  sltu       t3, t0, a0
                  nop
                  sll        s1, a4, a4
                  and        t2, s9, s8
                  xor        s2, s1, s3
                  slti       t4, gp, 99
                  auipc      t1, 988881
                  slti       t3, t2, 553
                  sltiu      t2, s3, -864
                  sub        t2, s4, a7
                  auipc      a3, 109266
                  or         t6, zero, a5
                  slti       a4, s2, -528
                  auipc      s3, 387907
                  sltu       t0, t2, a3
                  addi       a0, t6, 668
                  andi       t4, ra, 698
                  srl        t6, a5, a0
                  slti       t2, a2, -113
                  xor        s1, a2, s8
                  andi       t5, s3, -678
                  addi       t0, a5, 271
                  lui        zero, 590239
                  xor        s11, ra, a1
                  sub        s3, a7, a2
                  addi       t0, s4, 6
                  andi       s6, a4, 206
                  sll        gp, zero, s11
                  sltiu      gp, t5, -623
                  srai       t2, s4, 4
                  xori       t3, s1, 157
                  sltiu      a3, a4, 781
                  srli       zero, t4, 10
                  slti       a6, a1, -1005
                  sll        gp, s7, t4
                  slti       gp, a0, 947
                  add        s11, t6, a6
                  or         s10, a6, s4
                  lui        zero, 607099
                  nop
                  auipc      a3, 57259
                  xor        a7, a3, a3
                  add        a6, t5, s11
                  nop
                  xor        s4, a1, s4
                  srai       gp, a1, 11
                  or         s6, a5, a6
                  addi       t3, t1, 506
                  sll        a6, t4, a3
                  slli       t5, t6, 2
                  ori        zero, t2, 409
                  srli       t2, s6, 2
                  slt        s11, s6, s2
                  ori        s7, t0, -2
                  add        t2, t2, a5
                  sub        a2, a6, a4
                  sltiu      t4, s5, -1003
                  add        s2, a3, s8
                  srai       s1, t1, 0
                  sll        s2, s4, s9
                  andi       a2, tp, -818
                  add        a0, t0, s8
                  andi       gp, t0, 83
                  or         tp, s2, s3
                  xor        s5, s3, a0
                  srli       t0, a6, 28
                  andi       zero, a3, 382
                  ori        s10, a4, -660
                  sltiu      t0, t3, -637
                  or         tp, s11, t4
                  slti       s4, s8, 936
                  lui        t3, 688524
                  nop
                  lui        zero, 264177
                  and        s10, t3, ra
                  ori        tp, a2, 593
                  and        s7, a6, s10
                  auipc      a3, 58806
                  xor        t5, t2, s8
                  slt        s4, a7, t6
                  sll        s7, a2, a4
                  sltu       t6, t0, s0
                  nop
                  srl        s0, s2, t4
                  add        s11, s3, a0
                  slt        s11, t2, t4
                  slli       s2, a6, 15
                  andi       a7, s2, 434
                  and        a7, a1, s10
                  xor        a3, t4, s4
                  lui        s7, 1021110
                  and        a7, a3, t6
                  xor        t1, s1, s5
                  lui        t3, 548888
                  add        zero, s1, s10
                  auipc      s2, 1026864
                  slti       s4, a4, -552
                  srai       s1, zero, 16
                  srl        s1, a6, sp
                  or         a0, a5, a0
                  sltu       s1, zero, s7
                  addi       a2, a7, 937
                  add        t1, ra, t4
                  lui        s7, 325651
                  and        t6, a3, a7
                  sll        a2, s5, t3
                  nop
                  srai       a2, s4, 20
                  sltu       t5, zero, s8
                  xor        t3, s10, t2
                  and        a1, a6, s6
                  srai       s4, a3, 29
                  sltu       tp, s7, s6
                  or         t2, s7, s7
                  xori       s3, a0, 379
                  sub        s0, a3, sp
                  nop
                  slt        a1, t4, s1
                  sltiu      a0, a7, -732
                  addi       s11, a5, -369
                  sltu       t4, s8, a0
                  sub        gp, s9, s6
                  addi       a3, s0, 425
                  sltu       t1, a0, a7
                  xor        a4, s5, a7
                  addi       gp, zero, 258
                  sltu       gp, sp, sp
                  slli       s2, s8, 31
                  sub        ra, s8, s5
                  sltiu      t4, s5, -157
                  srli       a1, zero, 19
                  andi       s3, a5, 826
                  srli       a5, ra, 18
                  srl        gp, a3, s5
                  srai       s7, zero, 26
                  srai       a6, t2, 9
                  xor        a1, ra, t0
                  sltu       tp, tp, s5
                  sra        s3, a2, s3
                  sll        gp, s9, a3
                  srl        zero, s4, sp
                  slti       a2, s1, 591
                  srli       t3, s8, 31
                  lui        s11, 76860
                  xori       a4, s8, -814
                  slt        a6, s8, s3
                  addi       t3, t2, -102
                  addi       a1, s6, 504
                  xori       s2, s8, -360
                  lui        t0, 804234
                  sll        tp, a1, a4
                  sltiu      a5, a3, 968
                  add        s2, s0, t1
                  sll        s11, s2, sp
                  ori        s4, tp, -787
                  lui        t1, 182111
                  slli       t0, s9, 28
                  sltiu      a6, s9, -456
                  slt        t6, a0, s1
                  slt        a6, s11, s1
                  srai       s7, s2, 15
                  lui        a4, 879939
                  add        tp, t3, t5
                  srl        s11, a3, s2
                  xori       a1, s2, 224
                  sra        s11, s8, a7
                  slli       gp, s2, 15
                  sltu       zero, a4, a1
                  sra        a0, zero, s1
                  slli       tp, sp, 24
                  and        s10, a2, s8
                  srli       s4, s10, 26
                  sra        a2, s7, a6
                  srl        s5, t3, s4
                  andi       t3, s3, -63
                  addi       a4, t1, -87
                  addi       s11, s7, -114
                  slli       s6, a1, 28
                  addi       s10, s2, 79
                  and        s2, tp, a1
                  ori        s7, a0, 403
                  andi       a6, s10, -238
                  srai       s5, s2, 11
                  slt        zero, a1, a7
                  srl        s0, s10, t1
                  sub        tp, s4, t6
                  srai       s6, a6, 18
                  and        s11, a4, s5
                  slt        a6, a1, s5
                  and        ra, t6, t2
                  xori       s10, s2, 921
                  and        s2, t1, zero
                  addi       tp, ra, 697
                  xori       s6, s3, -503
                  slti       a7, s1, 831
                  sra        t4, zero, a0
                  slli       t0, t4, 22
                  sll        s1, s7, a7
                  sll        a6, a1, gp
                  lui        t6, 484658
                  xor        a4, tp, zero
                  slli       s11, s0, 14
                  sltu       s11, s4, s0
                  andi       s2, s2, 93
                  srli       t0, a6, 10
                  slti       a2, s7, -572
                  addi       t1, t0, 234
                  sll        s4, t6, t3
                  srl        s7, s6, t2
                  srai       s2, a2, 30
                  xor        t1, s3, t1
                  slt        t0, s6, s8
                  xor        t0, s4, a3
                  addi       t3, a3, 831
                  and        t3, a3, s7
                  add        s11, t1, t5
                  srai       a2, t1, 24
                  nop
                  addi       s6, t6, -994
                  srli       a6, a0, 24
                  slli       t3, s1, 1
                  sltu       s11, s8, s10
                  lui        s0, 1010440
                  srai       t3, a7, 27
                  srai       s11, zero, 5
                  nop
                  srli       t3, s9, 30
                  ori        t0, s6, -785
                  add        a5, t0, s10
                  andi       t5, t1, -534
                  srl        t5, zero, a3
                  sltiu      a0, a3, -728
                  srai       gp, t3, 0
                  slli       t2, t3, 18
                  sub        a7, t2, a0
                  sub        a3, s4, s1
                  sub        gp, a1, a3
                  add        a1, s2, t5
                  ori        s7, t3, 1018
                  sltiu      gp, t1, 560
                  sltu       s2, s1, sp
                  or         t1, gp, t4
                  andi       s6, a6, 518
                  ori        gp, t3, 235
                  slli       a4, s6, 26
                  ori        s6, t5, -889
                  sltiu      s10, ra, 850
                  sll        s4, a1, a7
                  srl        t5, s10, s2
                  sltiu      s0, zero, -782
                  sltu       a1, s9, s3
                  sll        zero, ra, gp
                  add        t1, s1, t3
                  auipc      t1, 319343
                  andi       a3, s8, 696
                  and        s10, s10, zero
                  srl        t0, a1, a4
                  nop
                  sra        t6, a6, s11
                  add        ra, a4, t3
                  srl        t3, t0, a1
                  slti       s7, t6, -210
                  andi       s4, t3, 82
                  nop
                  ori        t5, s2, 948
                  addi       t3, s8, 136
                  slti       s2, t2, 145
                  add        a3, t3, t2
                  sra        s1, a5, s0
                  lui        s6, 767617
                  srai       a1, a1, 29
                  sltu       s6, s3, a0
                  lui        s2, 534369
                  sll        a3, t1, s9
                  nop
                  slt        s3, a3, s9
                  auipc      a2, 342983
                  sub        s3, a3, a0
                  slt        a4, t3, t4
                  lui        s7, 789259
                  ori        a1, s4, 269
                  slti       t4, t0, 296
                  slti       s5, s2, 129
                  xor        t0, s7, a4
                  or         t5, ra, a5
                  and        t1, a1, a1
                  lui        a3, 103920
                  sltu       ra, s11, s4
                  xor        s0, s3, s0
                  sub        s7, s9, a7
                  xor        gp, t4, s9
                  add        s3, s10, zero
                  sub        t3, s6, s1
                  xor        s3, gp, s0
                  andi       a3, s4, -980
                  or         t0, t3, ra
                  auipc      tp, 743762
                  ori        s7, t0, 367
                  sltiu      tp, a0, -273
                  slti       t5, tp, 674
                  addi       s2, s1, -307
                  or         a3, s11, s4
                  srli       s1, s7, 15
                  ori        s1, gp, -92
                  sltiu      t6, tp, 329
                  slti       t0, s1, 725
                  auipc      t3, 287015
                  slti       t0, t2, 947
                  addi       t6, t4, 211
                  ori        s0, s11, -781
                  srai       gp, a5, 9
                  sll        a4, t6, tp
                  xori       a4, t3, -668
                  sll        ra, t5, a7
                  xori       s5, s7, 838
                  sll        a0, s6, sp
                  addi       t4, t1, 447
                  slt        gp, t2, t5
                  srl        zero, zero, s7
                  slti       s2, s5, -910
                  xori       a6, s6, 306
                  and        s7, a1, a0
                  srai       s3, s2, 2
                  auipc      t5, 692826
                  auipc      t3, 226962
                  add        t4, s2, t3
                  slt        s2, t2, a3
                  srli       s10, s1, 5
                  srai       gp, s5, 10
                  sub        t0, t6, s11
                  srai       s3, t2, 2
                  ori        s7, a6, 688
                  slli       a2, s11, 20
                  sltu       a3, s11, a2
                  addi       t2, t4, 262
                  ori        t1, s0, 307
                  andi       t0, s3, -120
                  slli       a3, a7, 2
                  sltu       a0, s7, s5
                  sltu       a3, a4, s1
                  lui        a7, 16241
                  srl        a4, a3, s3
                  xor        s5, s0, s7
                  auipc      zero, 727100
                  sll        a4, a1, s5
                  sll        a6, s1, a5
                  lui        ra, 579796
                  addi       ra, a5, -269
                  srli       s1, a5, 21
                  sub        s10, s7, s0
                  xori       s6, s9, 620
                  srai       s2, t2, 4
                  nop
                  srli       s7, ra, 12
                  lui        s3, 320713
                  srai       s1, s10, 1
                  slti       s0, a3, 92
                  slti       t2, s1, 332
                  add        s7, s4, t1
                  and        s0, t4, s8
                  srai       s3, zero, 17
                  lui        s7, 2637
                  lui        s7, 967502
                  slti       s4, s10, -130
                  slt        a7, s9, s6
                  auipc      a5, 712510
                  srli       a0, t0, 14
                  ori        a1, t4, 154
                  srai       s0, zero, 4
                  nop
                  sub        s6, t2, a1
                  or         s2, s6, t4
                  lui        t4, 493509
                  slt        a1, tp, t3
                  ori        t2, a0, -262
                  addi       a5, zero, 838
                  slt        a3, t0, a5
                  sll        a3, zero, a1
                  xori       a3, a2, -281
                  srai       a7, a1, 12
                  ori        s6, s10, 367
                  slti       s6, gp, -783
                  srli       s4, t2, 19
                  sra        a5, t2, s3
                  xori       t6, s1, 783
                  srai       t2, t4, 26
                  slti       ra, t5, 715
                  lui        s3, 261645
                  sll        a3, s8, s7
                  srl        a5, s0, s6
                  sub        ra, t1, s11
                  srl        t1, a4, s10
                  ori        s0, t4, -451
                  andi       t2, ra, -490
                  addi       t4, s7, 693
                  sltu       t6, a6, t3
                  xor        s1, tp, s1
                  addi       tp, s9, 271
                  lui        a1, 429440
                  sll        t5, a7, s8
                  slti       s4, ra, 403
                  slt        s1, s3, t0
                  slti       a4, t1, -197
                  xor        tp, ra, t1
                  nop
                  auipc      t2, 772887
                  srai       s10, s10, 21
                  auipc      a4, 404569
                  sra        a4, a5, s6
                  sltiu      t4, s6, 1003
                  slti       a0, ra, -869
                  srai       t4, ra, 1
                  or         t5, a0, zero
                  sll        s3, s8, s3
                  xori       gp, tp, 449
                  sltu       s3, s5, s3
                  ori        s6, zero, -299
                  or         t6, a1, s5
                  add        t5, a1, ra
                  andi       s1, s2, 845
                  ori        t2, s7, 214
                  srli       t4, t0, 27
                  sub        t1, ra, s1
                  andi       s7, t4, 106
                  andi       s4, a1, -418
                  slti       s10, a5, 48
                  xor        t1, t1, s0
                  sra        t4, a1, a1
                  slti       t1, a5, 940
                  or         a3, s7, s3
                  slli       t1, s10, 19
                  sltu       zero, s4, ra
                  srli       t6, s7, 22
                  xori       s5, s3, 212
                  sltiu      s2, t1, -142
                  ori        t1, s4, -87
                  add        gp, s10, s6
                  lui        t6, 728030
                  srli       s11, tp, 7
                  slt        s11, a6, s5
                  slli       t6, t0, 12
                  ori        t3, s3, 653
                  sltiu      ra, t3, 823
                  add        t6, zero, s10
                  slti       s5, s0, 413
                  lui        s4, 148092
                  sltu       t2, zero, a0
                  auipc      a7, 14709
                  lui        s3, 43369
                  auipc      s3, 120357
                  srai       gp, a1, 24
                  xori       a7, s1, 519
                  srl        s6, s1, t2
                  srl        tp, gp, a4
                  slli       s10, zero, 8
                  sltu       ra, s5, s10
                  srli       s1, ra, 8
                  sltiu      s0, s9, 174
                  srl        gp, s10, t1
                  sra        s5, s9, s3
                  or         a7, s3, t4
                  lui        t5, 724857
                  slt        s1, s4, tp
                  nop
                  slti       a3, a0, 343
                  lui        t4, 494870
                  sll        a5, s1, s3
                  srai       t4, t0, 21
                  sltu       t2, a3, s3
                  slti       tp, s10, -391
                  andi       gp, s8, -29
                  xor        a1, t0, a4
                  auipc      s3, 178335
                  sltiu      a0, s10, -1007
                  xor        s2, s3, ra
                  ori        s5, t5, 533
                  xor        a7, zero, t3
                  xori       a2, a0, 158
                  nop
                  xor        s3, a0, s3
                  andi       tp, s11, -824
                  andi       t5, t1, 175
                  sltu       a5, a6, gp
                  srai       s3, a3, 0
                  sltiu      s4, t1, 1000
                  xori       a5, a4, 560
                  slti       tp, s3, 788
                  xori       s2, zero, 290
                  ori        s7, t5, 282
                  slti       s0, a3, -713
                  srl        a6, s4, s0
                  slt        s4, a2, sp
                  srli       s5, tp, 31
                  and        zero, t6, ra
                  sra        s10, t3, gp
                  addi       s4, t3, -714
                  slli       s2, s6, 6
                  ori        s1, s4, -795
                  sltiu      a2, tp, 756
                  or         s6, sp, t2
                  srli       t6, a5, 4
                  sra        a4, t5, t3
                  sltu       s7, s5, a5
                  slti       t2, s7, 730
                  nop
                  ori        a0, t4, 595
                  andi       a7, s5, 745
                  xori       t4, s1, 395
                  xori       t3, s7, 409
                  or         s1, s3, s11
                  srli       t2, s2, 14
                  or         a3, a4, t3
                  sra        zero, t4, t0
                  andi       gp, s0, -872
                  and        a7, s8, s4
                  srai       s3, tp, 3
                  slti       a1, t0, 578
                  sltu       s10, t1, gp
                  sltu       t4, a7, s6
                  slli       s4, a7, 13
                  nop
                  addi       s0, sp, 695
                  sub        a0, s10, a5
                  nop
                  sub        t0, sp, tp
                  sltiu      s2, zero, 892
                  and        t0, t3, s4
                  sub        t6, s2, s8
                  addi       s5, s2, -621
                  or         t0, s10, a5
                  slti       t0, a7, 869
                  srl        a3, a5, a1
                  srai       a7, a1, 30
                  xor        s6, s3, s8
                  sra        s4, s1, s10
                  sub        gp, a1, zero
                  andi       t3, gp, 337
                  srai       s3, s8, 30
                  auipc      t5, 803481
                  slti       t0, a4, -491
                  and        a7, s6, zero
                  srli       s10, a3, 29
                  ori        s7, a2, -724
                  sra        a3, s7, t0
                  sra        t2, sp, t2
                  auipc      t2, 542112
                  sub        a7, t0, a2
                  sltu       s7, ra, tp
                  sub        t2, s4, t4
                  srai       t3, a5, 14
                  slli       a6, s2, 19
                  and        t2, a7, t2
                  sltiu      t2, a1, 85
                  ori        ra, s0, -975
                  slt        zero, tp, sp
                  ori        a0, a1, 841
                  srai       t3, a3, 12
                  auipc      zero, 362131
                  add        t3, s3, t3
                  sltu       a3, a6, s5
                  auipc      s1, 208637
                  or         a4, t0, s3
                  or         s7, s9, tp
                  srai       t6, t0, 9
                  slt        t5, a5, s8
                  srli       a6, s11, 22
                  nop
                  sub        s11, a0, a3
                  slli       s4, a6, 26
                  srai       a4, t4, 12
                  xori       t0, t0, -920
                  nop
                  slt        t4, s10, a7
                  slti       s3, s4, -154
                  xor        t6, s3, a1
                  and        zero, s7, t4
                  andi       s1, a2, 657
                  sra        s3, a2, s3
                  addi       a7, t6, 591
                  sra        a6, t6, t1
                  slli       a1, t3, 10
                  add        t4, tp, s5
                  addi       s5, s10, 774
                  lui        t5, 578842
                  ori        t6, s1, 456
                  nop
                  xor        t6, s10, s4
                  slti       t0, s7, 1000
                  sub        s3, t3, s7
                  lui        t2, 642263
                  addi       s4, a6, 437
                  xori       tp, s5, 598
                  slt        s1, s1, s10
                  xori       s1, gp, -332
                  xori       t6, s3, 397
                  andi       s10, s6, 557
                  srai       a1, a0, 5
                  andi       gp, zero, 128
                  and        a1, t4, t6
                  add        ra, tp, s11
                  slt        s1, t5, t0
                  srli       a7, s6, 7
                  andi       gp, a1, -776
                  sltu       a2, a6, s6
                  xor        s6, a2, t6
                  xor        s4, a2, s1
                  lui        t6, 454980
                  sra        s10, zero, zero
                  sra        tp, s8, t1
                  sltu       t4, t4, s5
                  xori       a5, s3, -679
                  sltu       a1, s9, a3
                  xori       t5, s8, -649
                  sltu       t4, s6, a4
                  slt        s5, s2, a4
                  xor        gp, a2, s1
                  add        t5, sp, a3
                  ori        t5, a6, -619
                  ori        a7, a5, -159
                  addi       s0, s7, 1003
                  sra        a5, a3, a4
                  nop
                  nop
                  slt        a5, sp, s9
                  srli       s1, a1, 22
                  srl        a2, a1, s9
                  sra        t3, a2, s7
                  sub        a0, a4, s4
                  sltiu      t5, s1, 712
                  add        a4, s6, t6
                  sra        t4, s8, s8
                  ori        a7, s11, 766
                  srai       s0, sp, 12
                  auipc      s5, 264458
                  srai       s0, s6, 14
                  slt        a0, t1, s3
                  srli       t1, s11, 25
                  auipc      a1, 15139
                  or         s11, s0, s8
                  sltiu      a4, t1, 1001
                  or         a5, s6, a7
                  srl        t3, zero, a0
                  sra        s5, tp, s1
                  auipc      t4, 327159
                  auipc      ra, 515126
                  auipc      s1, 420860
                  lui        s7, 784350
                  slt        s7, t3, s10
                  xor        t6, s0, s3
                  andi       gp, a4, 726
                  sltu       gp, t4, s11
                  sll        a6, t5, s11
                  nop
                  xori       s6, s6, 215
                  srli       ra, t5, 21
                  auipc      s6, 1021104
                  srl        a4, t6, t1
                  slt        t6, s10, a2
                  slti       zero, s2, 82
                  auipc      t2, 485707
                  xori       s3, s1, 61
                  sra        t4, s10, ra
                  sub        gp, ra, s2
                  sltiu      a3, tp, -445
                  lui        s1, 280586
                  slti       t6, a4, 584
                  auipc      t4, 209212
                  ori        gp, s4, 257
                  addi       s4, s6, 204
                  addi       t1, s6, -132
                  sltiu      zero, s4, 979
                  sll        t5, tp, s10
                  andi       t0, a2, 336
                  add        t1, sp, a0
                  slli       zero, s11, 17
                  auipc      a6, 144562
                  srl        a5, s3, t5
                  sra        s1, zero, s2
                  nop
                  xori       s10, s9, 527
                  sltiu      s10, s0, -410
                  sll        t2, gp, a1
                  auipc      a1, 959370
                  srai       t6, a4, 3
                  add        a7, a0, s9
                  sltu       a7, s9, t6
                  xor        ra, t3, zero
                  or         t6, s2, t3
                  sll        a2, a6, s5
                  lui        a1, 221277
                  sub        s0, s9, t3
                  srai       t0, s8, 17
                  sub        s2, s11, tp
                  slt        a4, ra, s1
                  ori        s0, s0, -724
                  or         ra, t6, zero
                  and        t5, s2, s2
                  slti       t4, s0, -464
                  add        t2, a4, t2
                  slt        a7, t1, zero
                  srl        a3, a4, t2
                  andi       t3, s2, 636
                  sra        t4, s6, s1
                  slli       t6, a0, 7
                  add        gp, gp, s3
                  xori       s7, s11, 116
                  andi       a4, s7, -812
                  andi       tp, t5, -204
                  andi       t0, zero, 80
                  sub        t2, a6, s5
                  slti       a2, tp, 506
                  sra        t4, a1, s8
                  xori       a7, t1, 760
                  add        t0, t4, a2
                  nop
                  srl        tp, s3, t1
                  sub        t2, gp, s1
                  lui        s11, 479222
                  sll        s11, t1, s11
                  lui        a5, 768703
                  xori       t1, s0, -906
                  xor        s5, s4, a5
                  xor        ra, t3, t4
                  xor        a5, a0, a7
                  slt        s1, s11, s8
                  slti       a6, a3, 294
                  or         a7, gp, a6
                  xor        s6, t2, zero
                  addi       t0, a6, 733
                  xori       ra, t3, -996
                  sltu       t5, s2, zero
                  addi       t5, ra, 9
                  lui        t0, 233225
                  and        s11, a2, s2
                  xor        s0, s10, s0
                  sra        t4, t0, s2
                  xori       s1, s0, -237
                  or         s3, a6, a5
                  add        tp, t1, sp
                  sub        t1, s0, t2
                  srai       s10, t3, 2
                  sra        t1, a6, t5
                  srli       s4, s6, 7
                  srli       t5, t4, 10
                  sra        zero, a3, s4
                  and        t6, a7, tp
                  sltu       s2, s4, a0
                  xori       s1, ra, -749
                  srai       s5, gp, 22
                  slli       tp, t5, 16
                  srai       s5, t1, 24
                  ori        s1, zero, -170
                  and        a5, s4, t4
                  and        t3, t2, t6
                  addi       s5, s3, 585
                  add        gp, a3, a5
                  and        s4, a7, s10
                  andi       s11, t4, 105
                  or         t0, s9, ra
                  slti       t1, s11, 983
                  sltu       a1, t4, t6
                  sra        s6, s3, gp
                  sub        t6, a5, s9
                  slt        t3, t6, s6
                  xori       s10, t2, -1002
                  lui        a1, 212864
                  srl        zero, sp, s3
                  andi       s6, s6, -582
                  slli       s0, t0, 14
                  nop
                  xor        a4, t3, tp
                  or         a4, zero, t3
                  xori       s3, a2, -611
                  and        a4, s5, ra
                  sub        a4, a3, zero
                  slti       t0, s3, 993
                  lui        t1, 1001646
                  xor        a2, zero, s6
                  sltu       a3, gp, t2
                  auipc      a2, 565636
                  sub        a4, t6, a0
                  ori        s5, s10, -757
                  slli       a7, s6, 15
                  ori        ra, s2, -52
                  and        s1, zero, t6
                  slti       s11, s10, 430
                  sltu       s4, a4, sp
                  srai       a5, s2, 26
                  addi       a7, t2, -91
                  andi       t5, t4, 59
                  slli       a6, s1, 31
                  sltu       s6, s2, t6
                  xori       t4, t1, -719
                  sltu       a2, s7, t0
                  slt        s6, t0, s6
                  srl        s4, s9, s8
                  ori        a5, t2, 796
                  addi       s7, t2, -720
                  sll        s5, tp, tp
                  or         s4, zero, t3
                  add        a1, t6, a1
                  sltu       s6, ra, ra
                  and        zero, a1, s3
                  sltiu      t0, t0, 385
                  and        zero, tp, sp
                  srai       s6, tp, 8
                  auipc      s2, 589472
test_done:
                  li gp, 1
                  ecall
write_tohost:
                  sw gp, tohost, t5

_exit:
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
mmode_intr_vector_1:
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
                  srli x4, x4, 0x1f
                  beqz x4, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_2:
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
                  srli x4, x4, 0x1f
                  beqz x4, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_3:
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
                  srli x4, x4, 0x1f
                  beqz x4, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_4:
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
                  srli x4, x4, 0x1f
                  beqz x4, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_5:
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
                  srli x4, x4, 0x1f
                  beqz x4, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_6:
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
                  srli x4, x4, 0x1f
                  beqz x4, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_7:
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
                  srli x4, x4, 0x1f
                  beqz x4, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_8:
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
                  srli x4, x4, 0x1f
                  beqz x4, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_9:
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
                  srli x4, x4, 0x1f
                  beqz x4, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_10:
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
                  srli x4, x4, 0x1f
                  beqz x4, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_11:
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
                  srli x4, x4, 0x1f
                  beqz x4, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_12:
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
                  srli x4, x4, 0x1f
                  beqz x4, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_13:
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
                  srli x4, x4, 0x1f
                  beqz x4, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_14:
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
                  srli x4, x4, 0x1f
                  beqz x4, 1f
                  j mmode_intr_handler
                  1: j test_done

mmode_intr_vector_15:
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
                  srli x4, x4, 0x1f
                  beqz x4, 1f
                  j mmode_intr_handler
                  1: j test_done

.align 12
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

mmode_exception_handler:
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
