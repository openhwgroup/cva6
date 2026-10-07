// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>
//
// The spike style of the disassembler: mnemonics and operands spelled exactly
// as spike-dasm spells them, for the extensions CVA6 implements.
//
// It works the way spike's own disassembler does. Each instruction, and each
// pseudo-instruction, is a row with a match/mask pair and a list of operands;
// rows are tried in the order spike adds them, so a pseudo-instruction placed
// ahead of its base instruction wins. Spike files every row in one of three
// groups by how much of the encoding its mask pins down, and searches the groups
// in turn; the same grouping is kept here, since it decides which row wins when
// two of them match. The match and mask values are those of spike's encoding.h,
// which come from riscv-opcodes.
//
// Adding an instruction means adding its row at the position spike has it, and
// a new kind of operand where none of the existing ones fits.

#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <vector>

#include "rv_disasm.h"

namespace cva6tb_tracer {

namespace {

enum arg_t : uint8_t {
  A_NONE = 0,
  A_XRD, A_XRS1, A_XRS2, A_FRD, A_FRS1, A_FRS2, A_FRS3,
  A_IMM, A_SHAMT, A_BIGIMM, A_ZIMM5, A_CSR, A_IORW,
  A_LOAD_ADDR, A_STORE_ADDR, A_BASE_ONLY, A_BRANCH_TARGET, A_JUMP_TARGET,
  // compressed
  A_C_RS1, A_C_RS2, A_C_FP_RS2, A_C_RS1S, A_C_RS2S, A_C_FP_RS2S, A_C_SP,
  A_C_IMM, A_C_ADDI4SPN_IMM, A_C_ADDI16SP_IMM, A_C_SHAMT, A_C_UIMM,
  A_C_LWSP_ADDR, A_C_LDSP_ADDR, A_C_SWSP_ADDR, A_C_SDSP_ADDR, A_C_LW_ADDR, A_C_LD_ADDR,
  A_C_B_ADDR, A_C_H_ADDR, A_C_BRANCH_TARGET, A_C_JUMP_TARGET, A_CM_JT_INDEX,
};

// When a row applies. Zcmt takes over the encoding of c.fsdsp, so a
// configuration has either Zcmt or the compressed double precision accesses.
// Spike adds the rows of everything else after those, as a fallback; the rows
// marked _ONLY are left out of that fallback too.
enum cond_t : uint8_t { C_ALL, C_RV32, C_RV64, C_RV32_ONLY, C_RV64_ONLY, C_ZCD, C_ZCMT };

struct row_t {
  const char *name;
  uint32_t    match;
  uint32_t    mask;
  cond_t      cond;
  arg_t       args[4];
};

// clang-format off
const row_t k_rows[] = {
    {"unimp",          0xc0001073, 0xffffffff, C_ALL, {}},
    {"c.unimp",        0x00000000, 0x0000ffff, C_ALL, {}},
    {"prefetch.r",     0x00106013, 0x01f07fff, C_ALL, {A_STORE_ADDR}},
    {"prefetch.w",     0x00306013, 0x01f07fff, C_ALL, {A_STORE_ADDR}},
    {"prefetch.i",     0x00006013, 0x01f07fff, C_ALL, {A_STORE_ADDR}},
    {"pause",          0x0100000f, 0xffffffff, C_ALL, {}},
    {"lb",             0x00000003, 0x0000707f, C_ALL, {A_XRD, A_LOAD_ADDR}},
    {"lbu",            0x00004003, 0x0000707f, C_ALL, {A_XRD, A_LOAD_ADDR}},
    {"lh",             0x00001003, 0x0000707f, C_ALL, {A_XRD, A_LOAD_ADDR}},
    {"lhu",            0x00005003, 0x0000707f, C_ALL, {A_XRD, A_LOAD_ADDR}},
    {"lw",             0x00002003, 0x0000707f, C_ALL, {A_XRD, A_LOAD_ADDR}},
    {"sb",             0x00000023, 0x0000707f, C_ALL, {A_XRS2, A_STORE_ADDR}},
    {"sh",             0x00001023, 0x0000707f, C_ALL, {A_XRS2, A_STORE_ADDR}},
    {"sw",             0x00002023, 0x0000707f, C_ALL, {A_XRS2, A_STORE_ADDR}},
    {"lwu",            0x00006003, 0x0000707f, C_RV64, {A_XRD, A_LOAD_ADDR}},
    {"ld",             0x00003003, 0x0000707f, C_RV64, {A_XRD, A_LOAD_ADDR}},
    {"sd",             0x00003023, 0x0000707f, C_RV64, {A_XRS2, A_STORE_ADDR}},
    {"amoadd.w",       0x0000202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoadd.w.rl",    0x0200202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoadd.w.aq",    0x0400202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoadd.w.aqrl",  0x0600202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoswap.w",      0x0800202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoswap.w.rl",   0x0a00202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoswap.w.aq",   0x0c00202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoswap.w.aqrl", 0x0e00202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoand.w",       0x6000202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoand.w.rl",    0x6200202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoand.w.aq",    0x6400202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoand.w.aqrl",  0x6600202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoor.w",        0x4000202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoor.w.rl",     0x4200202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoor.w.aq",     0x4400202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoor.w.aqrl",   0x4600202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoxor.w",       0x2000202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoxor.w.rl",    0x2200202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoxor.w.aq",    0x2400202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoxor.w.aqrl",  0x2600202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomin.w",       0x8000202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomin.w.rl",    0x8200202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomin.w.aq",    0x8400202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomin.w.aqrl",  0x8600202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomax.w",       0xa000202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomax.w.rl",    0xa200202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomax.w.aq",    0xa400202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomax.w.aqrl",  0xa600202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amominu.w",      0xc000202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amominu.w.rl",   0xc200202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amominu.w.aq",   0xc400202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amominu.w.aqrl", 0xc600202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomaxu.w",      0xe000202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomaxu.w.rl",   0xe200202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomaxu.w.aq",   0xe400202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomaxu.w.aqrl", 0xe600202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoadd.d",       0x0000302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoadd.d.rl",    0x0200302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoadd.d.aq",    0x0400302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoadd.d.aqrl",  0x0600302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoswap.d",      0x0800302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoswap.d.rl",   0x0a00302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoswap.d.aq",   0x0c00302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoswap.d.aqrl", 0x0e00302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoand.d",       0x6000302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoand.d.rl",    0x6200302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoand.d.aq",    0x6400302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoand.d.aqrl",  0x6600302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoor.d",        0x4000302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoor.d.rl",     0x4200302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoor.d.aq",     0x4400302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoor.d.aqrl",   0x4600302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoxor.d",       0x2000302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoxor.d.rl",    0x2200302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoxor.d.aq",    0x2400302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amoxor.d.aqrl",  0x2600302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomin.d",       0x8000302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomin.d.rl",    0x8200302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomin.d.aq",    0x8400302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomin.d.aqrl",  0x8600302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomax.d",       0xa000302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomax.d.rl",    0xa200302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomax.d.aq",    0xa400302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomax.d.aqrl",  0xa600302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amominu.d",      0xc000302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amominu.d.rl",   0xc200302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amominu.d.aq",   0xc400302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amominu.d.aqrl", 0xc600302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomaxu.d",      0xe000302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomaxu.d.rl",   0xe200302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomaxu.d.aq",   0xe400302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"amomaxu.d.aqrl", 0xe600302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"lr.w",           0x1000202f, 0xf9f0707f, C_ALL, {A_XRD, A_BASE_ONLY}},
    {"sc.w",           0x1800202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"sc.w.rl",        0x1a00202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"sc.w.aq",        0x1c00202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"sc.w.aqrl",      0x1e00202f, 0xfe00707f, C_ALL, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"lr.d",           0x1000302f, 0xf9f0707f, C_RV64, {A_XRD, A_BASE_ONLY}},
    {"sc.d",           0x1800302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"sc.d.rl",        0x1a00302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"sc.d.aq",        0x1c00302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"sc.d.aqrl",      0x1e00302f, 0xfe00707f, C_RV64, {A_XRD, A_XRS2, A_BASE_ONLY}},
    {"j",              0x0000006f, 0x00000fff, C_ALL, {A_JUMP_TARGET}},
    {"jal",            0x000000ef, 0x00000fff, C_ALL, {A_JUMP_TARGET}},
    {"jal",            0x0000006f, 0x0000007f, C_ALL, {A_XRD, A_JUMP_TARGET}},
    {"beqz",           0x00000063, 0x01f0707f, C_ALL, {A_XRS1, A_BRANCH_TARGET}},
    {"bnez",           0x00001063, 0x01f0707f, C_ALL, {A_XRS1, A_BRANCH_TARGET}},
    {"bltz",           0x00004063, 0x01f0707f, C_ALL, {A_XRS1, A_BRANCH_TARGET}},
    {"bgez",           0x00005063, 0x01f0707f, C_ALL, {A_XRS1, A_BRANCH_TARGET}},
    {"beq",            0x00000063, 0x0000707f, C_ALL, {A_XRS1, A_XRS2, A_BRANCH_TARGET}},
    {"bne",            0x00001063, 0x0000707f, C_ALL, {A_XRS1, A_XRS2, A_BRANCH_TARGET}},
    {"blt",            0x00004063, 0x0000707f, C_ALL, {A_XRS1, A_XRS2, A_BRANCH_TARGET}},
    {"bge",            0x00005063, 0x0000707f, C_ALL, {A_XRS1, A_XRS2, A_BRANCH_TARGET}},
    {"bltu",           0x00006063, 0x0000707f, C_ALL, {A_XRS1, A_XRS2, A_BRANCH_TARGET}},
    {"bgeu",           0x00007063, 0x0000707f, C_ALL, {A_XRS1, A_XRS2, A_BRANCH_TARGET}},
    {"lui",            0x00000037, 0x0000007f, C_ALL, {A_XRD, A_BIGIMM}},
    {"auipc",          0x00000017, 0x0000007f, C_ALL, {A_XRD, A_BIGIMM}},
    {"ret",            0x00008067, 0xffffffff, C_ALL, {}},
    {"jr",             0x00000067, 0xfff07fff, C_ALL, {A_XRS1}},
    {"jalr",           0x000000e7, 0xfff07fff, C_ALL, {A_XRS1}},
    {"jalr",           0x00000067, 0x0000707f, C_ALL, {A_XRD, A_XRS1, A_IMM}},
    {"nop",            0x00000013, 0xffffffff, C_ALL, {}},
    {"li",             0x00000013, 0x000ff07f, C_ALL, {A_XRD, A_IMM}},
    {"mv",             0x00000013, 0xfff0707f, C_ALL, {A_XRD, A_XRS1}},
    {"addi",           0x00000013, 0x0000707f, C_ALL, {A_XRD, A_XRS1, A_IMM}},
    {"slti",           0x00002013, 0x0000707f, C_ALL, {A_XRD, A_XRS1, A_IMM}},
    {"seqz",           0x00103013, 0xfff0707f, C_ALL, {A_XRD, A_XRS1}},
    {"sltiu",          0x00003013, 0x0000707f, C_ALL, {A_XRD, A_XRS1, A_IMM}},
    {"not",            0xfff04013, 0xfff0707f, C_ALL, {A_XRD, A_XRS1}},
    {"xori",           0x00004013, 0x0000707f, C_ALL, {A_XRD, A_XRS1, A_IMM}},
    {"slli",           0x00001013, 0xfc00707f, C_ALL, {A_XRD, A_XRS1, A_SHAMT}},
    {"srli",           0x00005013, 0xfc00707f, C_ALL, {A_XRD, A_XRS1, A_SHAMT}},
    {"srai",           0x40005013, 0xfc00707f, C_ALL, {A_XRD, A_XRS1, A_SHAMT}},
    {"ori",            0x00006013, 0x0000707f, C_ALL, {A_XRD, A_XRS1, A_IMM}},
    {"andi",           0x00007013, 0x0000707f, C_ALL, {A_XRD, A_XRS1, A_IMM}},
    {"sext.w",         0x0000001b, 0xfff0707f, C_RV64, {A_XRD, A_XRS1}},
    {"addiw",          0x0000001b, 0x0000707f, C_RV64, {A_XRD, A_XRS1, A_IMM}},
    {"slliw",          0x0000101b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_SHAMT}},
    {"srliw",          0x0000501b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_SHAMT}},
    {"sraiw",          0x4000501b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_SHAMT}},
    {"addw",           0x0000003b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"subw",           0x4000003b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"sllw",           0x0000103b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"srlw",           0x0000503b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"sraw",           0x4000503b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"add",            0x00000033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"sub",            0x40000033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"sll",            0x00001033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"slt",            0x00002033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"snez",           0x00003033, 0xfe0ff07f, C_ALL, {A_XRD, A_XRS2}},
    {"sltu",           0x00003033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"xor",            0x00004033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"srl",            0x00005033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"sra",            0x40005033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"or",             0x00006033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"and",            0x00007033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"ecall",          0x00000073, 0xffffffff, C_ALL, {}},
    {"ebreak",         0x00100073, 0xffffffff, C_ALL, {}},
    {"mret",           0x30200073, 0xffffffff, C_ALL, {}},
    {"dret",           0x7b200073, 0xffffffff, C_ALL, {}},
    {"wfi",            0x10500073, 0xffffffff, C_ALL, {}},
    {"fence",          0x0000000f, 0x0000707f, C_ALL, {A_IORW}},
    {"fence.i",        0x0000100f, 0x0000707f, C_ALL, {}},
    {"csrr",           0x00002073, 0x000ff07f, C_ALL, {A_XRD, A_CSR}},
    {"csrw",           0x00001073, 0x00007fff, C_ALL, {A_CSR, A_XRS1}},
    {"csrs",           0x00002073, 0x00007fff, C_ALL, {A_CSR, A_XRS1}},
    {"csrc",           0x00003073, 0x00007fff, C_ALL, {A_CSR, A_XRS1}},
    {"csrwi",          0x00005073, 0x00007fff, C_ALL, {A_CSR, A_ZIMM5}},
    {"csrsi",          0x00006073, 0x00007fff, C_ALL, {A_CSR, A_ZIMM5}},
    {"csrci",          0x00007073, 0x00007fff, C_ALL, {A_CSR, A_ZIMM5}},
    {"csrrw",          0x00001073, 0x0000707f, C_ALL, {A_XRD, A_CSR, A_XRS1}},
    {"csrrs",          0x00002073, 0x0000707f, C_ALL, {A_XRD, A_CSR, A_XRS1}},
    {"csrrc",          0x00003073, 0x0000707f, C_ALL, {A_XRD, A_CSR, A_XRS1}},
    {"csrrwi",         0x00005073, 0x0000707f, C_ALL, {A_XRD, A_CSR, A_ZIMM5}},
    {"csrrsi",         0x00006073, 0x0000707f, C_ALL, {A_XRD, A_CSR, A_ZIMM5}},
    {"csrrci",         0x00007073, 0x0000707f, C_ALL, {A_XRD, A_CSR, A_ZIMM5}},
    {"sret",           0x10200073, 0xffffffff, C_ALL, {}},
    {"sfence.vma",     0x12000073, 0xfe007fff, C_ALL, {A_XRS1, A_XRS2}},
    {"mul",            0x02000033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"mulh",           0x02001033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"mulhu",          0x02003033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"mulhsu",         0x02002033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"div",            0x02004033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"divu",           0x02005033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"rem",            0x02006033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"remu",           0x02007033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"mulw",           0x0200003b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"divw",           0x0200403b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"divuw",          0x0200503b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"remw",           0x0200603b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"remuw",          0x0200703b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"sh1add",         0x20002033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"sh2add",         0x20004033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"sh3add",         0x20006033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"slli.uw",        0x0800101b, 0xfc00707f, C_RV64, {A_XRD, A_XRS1, A_SHAMT}},
    {"zext.w",         0x0800003b, 0xfff0707f, C_RV64, {A_XRD, A_XRS1}},
    {"add.uw",         0x0800003b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"sh1add.uw",      0x2000203b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"sh2add.uw",      0x2000403b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"sh3add.uw",      0x2000603b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"ror",            0x60005033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"rol",            0x60001033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"rori",           0x60005013, 0xfc00707f, C_ALL, {A_XRD, A_XRS1, A_SHAMT}},
    {"ctz",            0x60101013, 0xfff0707f, C_ALL, {A_XRD, A_XRS1}},
    {"clz",            0x60001013, 0xfff0707f, C_ALL, {A_XRD, A_XRS1}},
    {"cpop",           0x60201013, 0xfff0707f, C_ALL, {A_XRD, A_XRS1}},
    {"min",            0x0a004033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"minu",           0x0a005033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"max",            0x0a006033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"maxu",           0x0a007033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"andn",           0x40007033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"orn",            0x40006033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"xnor",           0x40004033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"sext.b",         0x60401013, 0xfff0707f, C_ALL, {A_XRD, A_XRS1}},
    {"sext.h",         0x60501013, 0xfff0707f, C_ALL, {A_XRD, A_XRS1}},
    {"rev8",           0x6b805013, 0xfff0707f, C_ALL, {A_XRD, A_XRS1}},
    {"orc.b",          0x28705013, 0xfff0707f, C_ALL, {A_XRD, A_XRS1}},
    // spike knows rev8 by its RV64 encoding only
    {"rev8",           0x69805013, 0xfff0707f, C_RV32_ONLY, {A_XRD, A_XRS1}},
    {"zext.h",         0x08004033, 0xfff0707f, C_RV32_ONLY, {A_XRD, A_XRS1}},
    {"zext.h",         0x0800403b, 0xfff0707f, C_RV64_ONLY, {A_XRD, A_XRS1}},
    {"rorw",           0x6000503b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"rolw",           0x6000103b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_XRS2}},
    {"roriw",          0x6000501b, 0xfe00707f, C_RV64, {A_XRD, A_XRS1, A_SHAMT}},
    {"ctzw",           0x6010101b, 0xfff0707f, C_RV64, {A_XRD, A_XRS1}},
    {"clzw",           0x6000101b, 0xfff0707f, C_RV64, {A_XRD, A_XRS1}},
    {"cpopw",          0x6020101b, 0xfff0707f, C_RV64, {A_XRD, A_XRS1}},
    {"clmul",          0x0a001033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"clmulh",         0x0a003033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"clmulr",         0x0a002033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"bclr",           0x48001033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"binv",           0x68001033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"bset",           0x28001033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"bext",           0x48005033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"bclri",          0x48001013, 0xfc00707f, C_ALL, {A_XRD, A_XRS1, A_SHAMT}},
    {"binvi",          0x68001013, 0xfc00707f, C_ALL, {A_XRD, A_XRS1, A_SHAMT}},
    {"bseti",          0x28001013, 0xfc00707f, C_ALL, {A_XRD, A_XRS1, A_SHAMT}},
    {"bexti",          0x48005013, 0xfc00707f, C_ALL, {A_XRD, A_XRS1, A_SHAMT}},
    {"flw",            0x00002007, 0x0000707f, C_ALL, {A_FRD, A_LOAD_ADDR}},
    {"fsw",            0x00002027, 0x0000707f, C_ALL, {A_FRS2, A_STORE_ADDR}},
    {"fmv.w.x",        0xf0000053, 0xfff0707f, C_ALL, {A_FRD, A_XRS1}},
    {"fmv.x.w",        0xe0000053, 0xfff0707f, C_ALL, {A_XRD, A_FRS1}},
    {"fadd.s",         0x00000053, 0xfe00007f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fsub.s",         0x08000053, 0xfe00007f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fmul.s",         0x10000053, 0xfe00007f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fdiv.s",         0x18000053, 0xfe00007f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fsqrt.s",        0x58000053, 0xfff0007f, C_ALL, {A_FRD, A_FRS1}},
    {"fmin.s",         0x28000053, 0xfe00707f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fmax.s",         0x28001053, 0xfe00707f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fmadd.s",        0x00000043, 0x0600007f, C_ALL, {A_FRD, A_FRS1, A_FRS2, A_FRS3}},
    {"fmsub.s",        0x00000047, 0x0600007f, C_ALL, {A_FRD, A_FRS1, A_FRS2, A_FRS3}},
    {"fnmadd.s",       0x0000004f, 0x0600007f, C_ALL, {A_FRD, A_FRS1, A_FRS2, A_FRS3}},
    {"fnmsub.s",       0x0000004b, 0x0600007f, C_ALL, {A_FRD, A_FRS1, A_FRS2, A_FRS3}},
    {"fsgnj.s",        0x20000053, 0xfe00707f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fsgnjn.s",       0x20001053, 0xfe00707f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fsgnjx.s",       0x20002053, 0xfe00707f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fcvt.s.d",       0x40100053, 0xfff0007f, C_ALL, {A_FRD, A_FRS1}},
    {"fcvt.s.q",       0x40300053, 0xfff0007f, C_ALL, {A_FRD, A_FRS1}},
    {"fcvt.s.w",       0xd0000053, 0xfff0007f, C_ALL, {A_FRD, A_XRS1}},
    {"fcvt.s.wu",      0xd0100053, 0xfff0007f, C_ALL, {A_FRD, A_XRS1}},
    {"fcvt.s.wu",      0xd0100053, 0xfff0007f, C_ALL, {A_FRD, A_XRS1}},
    {"fcvt.w.s",       0xc0000053, 0xfff0007f, C_ALL, {A_XRD, A_FRS1}},
    {"fcvt.wu.s",      0xc0100053, 0xfff0007f, C_ALL, {A_XRD, A_FRS1}},
    {"fclass.s",       0xe0001053, 0xfff0707f, C_ALL, {A_XRD, A_FRS1}},
    {"feq.s",          0xa0002053, 0xfe00707f, C_ALL, {A_XRD, A_FRS1, A_FRS2}},
    {"flt.s",          0xa0001053, 0xfe00707f, C_ALL, {A_XRD, A_FRS1, A_FRS2}},
    {"fle.s",          0xa0000053, 0xfe00707f, C_ALL, {A_XRD, A_FRS1, A_FRS2}},
    {"fcvt.s.l",       0xd0200053, 0xfff0007f, C_RV64, {A_FRD, A_XRS1}},
    {"fcvt.s.lu",      0xd0300053, 0xfff0007f, C_RV64, {A_FRD, A_XRS1}},
    {"fcvt.l.s",       0xc0200053, 0xfff0007f, C_RV64, {A_XRD, A_FRS1}},
    {"fcvt.lu.s",      0xc0300053, 0xfff0007f, C_RV64, {A_XRD, A_FRS1}},
    {"fld",            0x00003007, 0x0000707f, C_ALL, {A_FRD, A_LOAD_ADDR}},
    {"fsd",            0x00003027, 0x0000707f, C_ALL, {A_FRS2, A_STORE_ADDR}},
    {"fmv.d.x",        0xf2000053, 0xfff0707f, C_RV64, {A_FRD, A_XRS1}},
    {"fmv.x.d",        0xe2000053, 0xfff0707f, C_RV64, {A_XRD, A_FRS1}},
    {"fadd.d",         0x02000053, 0xfe00007f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fsub.d",         0x0a000053, 0xfe00007f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fmul.d",         0x12000053, 0xfe00007f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fdiv.d",         0x1a000053, 0xfe00007f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fsqrt.d",        0x5a000053, 0xfff0007f, C_ALL, {A_FRD, A_FRS1}},
    {"fmin.d",         0x2a000053, 0xfe00707f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fmax.d",         0x2a001053, 0xfe00707f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fmadd.d",        0x02000043, 0x0600007f, C_ALL, {A_FRD, A_FRS1, A_FRS2, A_FRS3}},
    {"fmsub.d",        0x02000047, 0x0600007f, C_ALL, {A_FRD, A_FRS1, A_FRS2, A_FRS3}},
    {"fnmadd.d",       0x0200004f, 0x0600007f, C_ALL, {A_FRD, A_FRS1, A_FRS2, A_FRS3}},
    {"fnmsub.d",       0x0200004b, 0x0600007f, C_ALL, {A_FRD, A_FRS1, A_FRS2, A_FRS3}},
    {"fsgnj.d",        0x22000053, 0xfe00707f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fsgnjn.d",       0x22001053, 0xfe00707f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fsgnjx.d",       0x22002053, 0xfe00707f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fcvt.d.s",       0x42000053, 0xfff0007f, C_ALL, {A_FRD, A_FRS1}},
    {"fcvt.d.q",       0x42300053, 0xfff0007f, C_ALL, {A_FRD, A_FRS1}},
    {"fcvt.d.w",       0xd2000053, 0xfff0007f, C_ALL, {A_FRD, A_XRS1}},
    {"fcvt.d.wu",      0xd2100053, 0xfff0007f, C_ALL, {A_FRD, A_XRS1}},
    {"fcvt.d.wu",      0xd2100053, 0xfff0007f, C_ALL, {A_FRD, A_XRS1}},
    {"fcvt.w.d",       0xc2000053, 0xfff0007f, C_ALL, {A_XRD, A_FRS1}},
    {"fcvt.wu.d",      0xc2100053, 0xfff0007f, C_ALL, {A_XRD, A_FRS1}},
    {"fclass.d",       0xe2001053, 0xfff0707f, C_ALL, {A_XRD, A_FRS1}},
    {"feq.d",          0xa2002053, 0xfe00707f, C_ALL, {A_XRD, A_FRS1, A_FRS2}},
    {"flt.d",          0xa2001053, 0xfe00707f, C_ALL, {A_XRD, A_FRS1, A_FRS2}},
    {"fle.d",          0xa2000053, 0xfe00707f, C_ALL, {A_XRD, A_FRS1, A_FRS2}},
    {"fcvt.d.l",       0xd2200053, 0xfff0007f, C_RV64, {A_FRD, A_XRS1}},
    {"fcvt.d.lu",      0xd2300053, 0xfff0007f, C_RV64, {A_FRD, A_XRS1}},
    {"fcvt.l.d",       0xc2200053, 0xfff0007f, C_RV64, {A_XRD, A_FRS1}},
    {"fcvt.lu.d",      0xc2300053, 0xfff0007f, C_RV64, {A_XRD, A_FRS1}},
    {"fadd.h",         0x04000053, 0xfe00007f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fsub.h",         0x0c000053, 0xfe00007f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fmul.h",         0x14000053, 0xfe00007f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fdiv.h",         0x1c000053, 0xfe00007f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fsqrt.h",        0x5c000053, 0xfff0007f, C_ALL, {A_FRD, A_FRS1}},
    {"fmin.h",         0x2c000053, 0xfe00707f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fmax.h",         0x2c001053, 0xfe00707f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fmadd.h",        0x04000043, 0x0600007f, C_ALL, {A_FRD, A_FRS1, A_FRS2, A_FRS3}},
    {"fmsub.h",        0x04000047, 0x0600007f, C_ALL, {A_FRD, A_FRS1, A_FRS2, A_FRS3}},
    {"fnmadd.h",       0x0400004f, 0x0600007f, C_ALL, {A_FRD, A_FRS1, A_FRS2, A_FRS3}},
    {"fnmsub.h",       0x0400004b, 0x0600007f, C_ALL, {A_FRD, A_FRS1, A_FRS2, A_FRS3}},
    {"fsgnj.h",        0x24000053, 0xfe00707f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fsgnjn.h",       0x24001053, 0xfe00707f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fsgnjx.h",       0x24002053, 0xfe00707f, C_ALL, {A_FRD, A_FRS1, A_FRS2}},
    {"fcvt.h.l",       0xd4200053, 0xfff0007f, C_ALL, {A_FRD, A_XRS1}},
    {"fcvt.h.lu",      0xd4300053, 0xfff0007f, C_ALL, {A_FRD, A_XRS1}},
    {"fcvt.h.w",       0xd4000053, 0xfff0007f, C_ALL, {A_FRD, A_XRS1}},
    {"fcvt.h.wu",      0xd4100053, 0xfff0007f, C_ALL, {A_FRD, A_XRS1}},
    {"fcvt.h.wu",      0xd4100053, 0xfff0007f, C_ALL, {A_FRD, A_XRS1}},
    {"fcvt.l.h",       0xc4200053, 0xfff0007f, C_ALL, {A_XRD, A_FRS1}},
    {"fcvt.lu.h",      0xc4300053, 0xfff0007f, C_ALL, {A_XRD, A_FRS1}},
    {"fcvt.w.h",       0xc4000053, 0xfff0007f, C_ALL, {A_XRD, A_FRS1}},
    {"fcvt.wu.h",      0xc4100053, 0xfff0007f, C_ALL, {A_XRD, A_FRS1}},
    {"fclass.h",       0xe4001053, 0xfff0707f, C_ALL, {A_XRD, A_FRS1}},
    {"feq.h",          0xa4002053, 0xfe00707f, C_ALL, {A_XRD, A_FRS1, A_FRS2}},
    {"flt.h",          0xa4001053, 0xfe00707f, C_ALL, {A_XRD, A_FRS1, A_FRS2}},
    {"fle.h",          0xa4000053, 0xfe00707f, C_ALL, {A_XRD, A_FRS1, A_FRS2}},
    {"fcvt.h.s",       0x44000053, 0xfff0007f, C_ALL, {A_FRD, A_FRS1}},
    {"fcvt.h.d",       0x44100053, 0xfff0007f, C_ALL, {A_FRD, A_FRS1}},
    {"fcvt.h.q",       0x44300053, 0xfff0007f, C_ALL, {A_FRD, A_FRS1}},
    {"fcvt.s.h",       0x40200053, 0xfff0007f, C_ALL, {A_FRD, A_FRS1}},
    {"fcvt.d.h",       0x42200053, 0xfff0007f, C_ALL, {A_FRD, A_FRS1}},
    {"fcvt.q.h",       0x46200053, 0xfff0007f, C_ALL, {A_FRD, A_FRS1}},
    {"flh",            0x00001007, 0x0000707f, C_ALL, {A_FRD, A_LOAD_ADDR}},
    {"fsh",            0x00001027, 0x0000707f, C_ALL, {A_FRS2, A_STORE_ADDR}},
    {"fmv.h.x",        0xf4000053, 0xfff0707f, C_ALL, {A_FRD, A_XRS1}},
    {"fmv.x.h",        0xe4000053, 0xfff0707f, C_ALL, {A_XRD, A_FRS1}},
    {"hlv.b",          0x60004073, 0xfff0707f, C_ALL, {A_XRD, A_BASE_ONLY}},
    {"hlv.bu",         0x60104073, 0xfff0707f, C_ALL, {A_XRD, A_BASE_ONLY}},
    {"hlv.h",          0x64004073, 0xfff0707f, C_ALL, {A_XRD, A_BASE_ONLY}},
    {"hlv.hu",         0x64104073, 0xfff0707f, C_ALL, {A_XRD, A_BASE_ONLY}},
    {"hlv.w",          0x68004073, 0xfff0707f, C_ALL, {A_XRD, A_BASE_ONLY}},
    {"hlv.wu",         0x68104073, 0xfff0707f, C_ALL, {A_XRD, A_BASE_ONLY}},
    {"hlv.d",          0x6c004073, 0xfff0707f, C_ALL, {A_XRD, A_BASE_ONLY}},
    {"hlvx.hu",        0x64304073, 0xfff0707f, C_ALL, {A_XRD, A_BASE_ONLY}},
    {"hlvx.wu",        0x68304073, 0xfff0707f, C_ALL, {A_XRD, A_BASE_ONLY}},
    {"hsv.b",          0x62004073, 0xfe007fff, C_ALL, {A_XRS2, A_BASE_ONLY}},
    {"hsv.h",          0x66004073, 0xfe007fff, C_ALL, {A_XRS2, A_BASE_ONLY}},
    {"hsv.w",          0x6a004073, 0xfe007fff, C_ALL, {A_XRS2, A_BASE_ONLY}},
    {"hsv.d",          0x6e004073, 0xfe007fff, C_ALL, {A_XRS2, A_BASE_ONLY}},
    {"hfence.gvma",    0x62000073, 0xfe007fff, C_ALL, {A_XRS1, A_XRS2}},
    {"hfence.vvma",    0x22000073, 0xfe007fff, C_ALL, {A_XRS1, A_XRS2}},
    {"c.ebreak",       0x00009002, 0x0000ffff, C_ALL, {}},
    {"ret",            0x00008082, 0x0000ffff, C_ALL, {}},
    {"c.jr",           0x00008002, 0x0000f07f, C_ALL, {A_C_RS1}},
    {"c.jalr",         0x00009002, 0x0000f07f, C_ALL, {A_C_RS1}},
    {"c.nop",          0x00000001, 0x0000ffff, C_ALL, {}},
    {"c.addi16sp",     0x00006101, 0x0000ef83, C_ALL, {A_C_SP, A_C_ADDI16SP_IMM}},
    {"c.addi4spn",     0x00000000, 0x0000e003, C_ALL, {A_C_RS2S, A_C_SP, A_C_ADDI4SPN_IMM}},
    {"c.li",           0x00004001, 0x0000e003, C_ALL, {A_XRD, A_C_IMM}},
    {"c.lui",          0x00006001, 0x0000e003, C_ALL, {A_XRD, A_C_UIMM}},
    {"c.addi",         0x00000001, 0x0000e003, C_ALL, {A_XRD, A_C_IMM}},
    {"c.slli",         0x00000002, 0x0000e003, C_ALL, {A_C_RS1, A_C_SHAMT}},
    {"c.srli",         0x00008001, 0x0000ec03, C_ALL, {A_C_RS1S, A_C_SHAMT}},
    {"c.srai",         0x00008401, 0x0000ec03, C_ALL, {A_C_RS1S, A_C_SHAMT}},
    {"c.andi",         0x00008801, 0x0000ec03, C_ALL, {A_C_RS1S, A_C_IMM}},
    {"c.mv",           0x00008002, 0x0000f003, C_ALL, {A_XRD, A_C_RS2}},
    {"c.add",          0x00009002, 0x0000f003, C_ALL, {A_XRD, A_C_RS2}},
    {"c.sub",          0x00008c01, 0x0000fc63, C_ALL, {A_C_RS1S, A_C_RS2S}},
    {"c.and",          0x00008c61, 0x0000fc63, C_ALL, {A_C_RS1S, A_C_RS2S}},
    {"c.or",           0x00008c41, 0x0000fc63, C_ALL, {A_C_RS1S, A_C_RS2S}},
    {"c.xor",          0x00008c21, 0x0000fc63, C_ALL, {A_C_RS1S, A_C_RS2S}},
    {"c.lwsp",         0x00004002, 0x0000e003, C_ALL, {A_XRD, A_C_LWSP_ADDR}},
    {"c.swsp",         0x0000c002, 0x0000e003, C_ALL, {A_C_RS2, A_C_SWSP_ADDR}},
    {"c.lw",           0x00004000, 0x0000e003, C_ALL, {A_C_RS2S, A_C_LW_ADDR}},
    {"c.sw",           0x0000c000, 0x0000e003, C_ALL, {A_C_RS2S, A_C_LW_ADDR}},
    {"c.beqz",         0x0000c001, 0x0000e003, C_ALL, {A_C_RS1S, A_C_BRANCH_TARGET}},
    {"c.bnez",         0x0000e001, 0x0000e003, C_ALL, {A_C_RS1S, A_C_BRANCH_TARGET}},
    {"c.j",            0x0000a001, 0x0000e003, C_ALL, {A_C_JUMP_TARGET}},
    {"c.jal",          0x00002001, 0x0000e003, C_RV32_ONLY, {A_C_JUMP_TARGET}},
    {"c.addiw",        0x00002001, 0x0000e003, C_RV64_ONLY, {A_XRD, A_C_IMM}},
    {"c.addw",         0x00009c21, 0x0000fc63, C_RV64, {A_C_RS1S, A_C_RS2S}},
    {"c.subw",         0x00009c01, 0x0000fc63, C_RV64, {A_C_RS1S, A_C_RS2S}},
    {"c.ld",           0x00006000, 0x0000e003, C_RV64_ONLY, {A_C_RS2S, A_C_LD_ADDR}},
    {"c.ldsp",         0x00006002, 0x0000e003, C_RV64_ONLY, {A_XRD, A_C_LDSP_ADDR}},
    {"c.sd",           0x0000e000, 0x0000e003, C_RV64_ONLY, {A_C_RS2S, A_C_LD_ADDR}},
    {"c.sdsp",         0x0000e002, 0x0000e003, C_RV64_ONLY, {A_C_RS2, A_C_SDSP_ADDR}},
    {"c.fld",          0x00002000, 0x0000e003, C_ZCD, {A_C_FP_RS2S, A_C_LD_ADDR}},
    {"c.fldsp",        0x00002002, 0x0000e003, C_ZCD, {A_FRD, A_C_LDSP_ADDR}},
    {"c.fsd",          0x0000a000, 0x0000e003, C_ZCD, {A_C_FP_RS2S, A_C_LD_ADDR}},
    {"c.fsdsp",        0x0000a002, 0x0000e003, C_ZCD, {A_C_FP_RS2, A_C_SDSP_ADDR}},
    {"c.flw",          0x00006000, 0x0000e003, C_RV32, {A_C_FP_RS2S, A_C_LW_ADDR}},
    {"c.flwsp",        0x00006002, 0x0000e003, C_RV32, {A_FRD, A_C_LWSP_ADDR}},
    {"c.fsw",          0x0000e000, 0x0000e003, C_RV32, {A_C_FP_RS2S, A_C_LW_ADDR}},
    {"c.fswsp",        0x0000e002, 0x0000e003, C_RV32, {A_C_FP_RS2, A_C_SWSP_ADDR}},
    {"c.zext.b",       0x00009c61, 0x0000fc7f, C_ALL, {A_C_RS1S}},
    {"c.sext.b",       0x00009c65, 0x0000fc7f, C_ALL, {A_C_RS1S}},
    {"c.zext.h",       0x00009c69, 0x0000fc7f, C_ALL, {A_C_RS1S}},
    {"c.sext.h",       0x00009c6d, 0x0000fc7f, C_ALL, {A_C_RS1S}},
    {"c.zext.w",       0x00009c71, 0x0000fc7f, C_RV64, {A_C_RS1S}},
    {"c.not",          0x00009c75, 0x0000fc7f, C_ALL, {A_C_RS1S}},
    {"c.mul",          0x00009c41, 0x0000fc63, C_ALL, {A_C_RS1S, A_C_RS2S}},
    {"c.lbu",          0x00008000, 0x0000fc03, C_ALL, {A_C_RS2S, A_C_B_ADDR}},
    {"c.lhu",          0x00008400, 0x0000fc43, C_ALL, {A_C_RS2S, A_C_H_ADDR}},
    {"c.lh",           0x00008440, 0x0000fc43, C_ALL, {A_C_RS2S, A_C_H_ADDR}},
    {"c.sb",           0x00008800, 0x0000fc03, C_ALL, {A_C_RS2S, A_C_B_ADDR}},
    {"c.sh",           0x00008c00, 0x0000fc43, C_ALL, {A_C_RS2S, A_C_H_ADDR}},
    {"cm.jt",          0x0000a002, 0x0000ff83, C_ZCMT, {A_CM_JT_INDEX}},
    {"cm.jalt",        0x0000a002, 0x0000fc03, C_ZCMT, {A_CM_JT_INDEX}},
    {"cbo.clean",      0x0010200f, 0xfff07fff, C_ALL, {A_BASE_ONLY}},
    {"cbo.flush",      0x0020200f, 0xfff07fff, C_ALL, {A_BASE_ONLY}},
    {"cbo.inval",      0x0000200f, 0xfff07fff, C_ALL, {A_BASE_ONLY}},
    {"cbo.zero",       0x0040200f, 0xfff07fff, C_ALL, {A_BASE_ONLY}},
    {"czero.eqz",      0x0e005033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
    {"czero.nez",      0x0e007033, 0xfe00707f, C_ALL, {A_XRD, A_XRS1, A_XRS2}},
};
// clang-format on

bool applies(const row_t &r, int xlen, bool zcmt) {
  switch (r.cond) {
    case C_RV32: case C_RV32_ONLY: return xlen == 32;
    case C_RV64: case C_RV64_ONLY: return xlen == 64;
    case C_ZCD: return !zcmt;
    case C_ZCMT: return zcmt;
    default: return true;
  }
}

bool in_fallback(const row_t &r, int xlen) {
  if (r.cond == C_RV32_ONLY) return xlen == 32;
  if (r.cond == C_RV64_ONLY) return xlen == 64;
  return true;
}

// The rows that apply to one configuration, filed the way spike files them:
// by the opcode when the mask covers it, else by the compressed opcode and
// funct3 when the mask covers those, else in a list of their own.
struct index_t {
  std::vector<const row_t *> by_opcode[128];
  std::vector<const row_t *> by_rvc[32];
  std::vector<const row_t *> rest;
};

unsigned rvc_bucket(uint32_t bits) { return (bits & 3) | ((bits >> 11) & 0x1C); }

void file_row(index_t &ix, const row_t &r) {
  if ((r.mask & 0x7F) == 0x7F) ix.by_opcode[r.match & 0x7F].push_back(&r);
  else if ((r.mask & 0xE003) == 0xE003) ix.by_rvc[rvc_bucket(r.match)].push_back(&r);
  else ix.rest.push_back(&r);
}

index_t build_index(int xlen, bool zcmt) {
  index_t ix;
  for (const row_t &r : k_rows)
    if (applies(r, xlen, zcmt)) file_row(ix, r);
  for (const row_t &r : k_rows)
    if (!applies(r, xlen, zcmt) && in_fallback(r, xlen)) file_row(ix, r);
  return ix;
}

const row_t *lookup(uint32_t insn, int xlen, bool zcmt) {
  static const index_t ix[4] = {build_index(32, false), build_index(32, true),
                                build_index(64, false), build_index(64, true)};
  const index_t &i = ix[(xlen == 64 ? 2 : 0) + (zcmt ? 1 : 0)];
  for (const row_t *r : i.by_opcode[insn & 0x7F])
    if ((insn & r->mask) == r->match) return r;
  for (const row_t *r : i.by_rvc[rvc_bucket(insn)])
    if ((insn & r->mask) == r->match) return r;
  for (const row_t *r : i.rest)
    if ((insn & r->mask) == r->match) return r;
  return nullptr;
}

// field extraction, named after spike's insn_t accessors
uint32_t x(uint32_t b, int lo, int len) { return (b >> lo) & ((1u << len) - 1); }
int32_t  xs(uint32_t b, int lo, int len) { return (int32_t)(b << (32 - lo - len)) >> (32 - len); }

const char *xpr(unsigned i) {
  static const char *const n[32] = {"zero", "ra", "sp", "gp", "tp",  "t0",  "t1", "t2",
                                    "s0",   "s1", "a0", "a1", "a2",  "a3",  "a4", "a5",
                                    "a6",   "a7", "s2", "s3", "s4",  "s5",  "s6", "s7",
                                    "s8",   "s9", "s10", "s11", "t3", "t4", "t5", "t6"};
  return n[i & 31];
}

std::string sfmt(const char *f, ...) __attribute__((format(printf, 1, 2)));
std::string sfmt(const char *f, ...) {
  char buf[64];
  va_list ap;
  va_start(ap, f);
  vsnprintf(buf, sizeof(buf), f, ap);
  va_end(ap);
  return buf;
}

std::string pc_relative(int32_t off, bool hex) {
  const unsigned a = (unsigned)(off < 0 ? -off : off);
  return sfmt(hex ? "pc %c 0x%x" : "pc %c %u", off < 0 ? '-' : '+', a);
}

std::string iorw(uint32_t b) {
  static const char type[] = "wroi";
  const uint32_t v = x(b, 20, 8);
  std::string s;
  for (int i = 7; i >= 4; --i)
    if (v & (1u << i)) s += type[i - 4];
  if (!s.empty()) s += ',';
  for (int i = 3; i >= 0; --i)
    if (v & (1u << i)) s += type[i];
  return s;
}

std::string csr_name(uint32_t b) {
  std::string n;
  return rv_csr_lookup((uint16_t)x(b, 20, 12), &n) ? n : sfmt("unknown_%03x", x(b, 20, 12));
}

// One operand. Sets *target for the pc relative ones.
std::string render_arg(arg_t a, uint32_t b, bool *is_target, int32_t *target) {
  const unsigned rd = x(b, 7, 5), rs1 = x(b, 15, 5), rs2 = x(b, 20, 5), rs3 = x(b, 27, 5);
  const unsigned c_rs2 = x(b, 2, 5), c_rs1s = 8 + x(b, 7, 3), c_rs2s = 8 + x(b, 2, 3);
  const int32_t  c_imm = (int32_t)x(b, 2, 5) + (xs(b, 12, 1) << 5);
  switch (a) {
    case A_XRD: return xpr(rd);
    case A_XRS1: return xpr(rs1);
    case A_XRS2: return xpr(rs2);
    case A_FRD: return rv_fpr_name(rd);
    case A_FRS1: return rv_fpr_name(rs1);
    case A_FRS2: return rv_fpr_name(rs2);
    case A_FRS3: return rv_fpr_name(rs3);
    case A_IMM: return sfmt("%d", xs(b, 20, 12));
    case A_SHAMT: return sfmt("%u", x(b, 20, 6));
    case A_BIGIMM: return sfmt("0x%x", b >> 12);
    case A_ZIMM5: return sfmt("%u", rs1);
    case A_CSR: return csr_name(b);
    case A_IORW: return iorw(b);
    case A_LOAD_ADDR: return sfmt("%d(%s)", xs(b, 20, 12), xpr(rs1));
    case A_STORE_ADDR: return sfmt("%d(%s)", (int32_t)x(b, 7, 5) + (xs(b, 25, 7) << 5), xpr(rs1));
    case A_BASE_ONLY: return sfmt("(%s)", xpr(rs1));
    case A_BRANCH_TARGET:
      *is_target = true;
      *target = (int32_t)(x(b, 8, 4) << 1) + (int32_t)(x(b, 25, 6) << 5) +
                (int32_t)(x(b, 7, 1) << 11) + (xs(b, 31, 1) << 12);
      return pc_relative(*target, false);
    case A_JUMP_TARGET:
      *is_target = true;
      *target = (int32_t)(x(b, 21, 10) << 1) + (int32_t)(x(b, 20, 1) << 11) +
                (int32_t)(x(b, 12, 8) << 12) + (xs(b, 31, 1) << 20);
      return pc_relative(*target, true);
    case A_C_RS1: return xpr(rd);
    case A_C_RS2: return xpr(c_rs2);
    case A_C_FP_RS2: return rv_fpr_name(c_rs2);
    case A_C_RS1S: return xpr(c_rs1s);
    case A_C_RS2S: return xpr(c_rs2s);
    case A_C_FP_RS2S: return rv_fpr_name(c_rs2s);
    case A_C_SP: return "sp";
    case A_C_IMM: return sfmt("%d", c_imm);
    case A_C_ADDI4SPN_IMM:
      return sfmt("%u", (x(b, 6, 1) << 2) + (x(b, 5, 1) << 3) + (x(b, 11, 2) << 4) + (x(b, 7, 4) << 6));
    case A_C_ADDI16SP_IMM:
      return sfmt("%d", (int32_t)((x(b, 6, 1) << 4) + (x(b, 2, 1) << 5) + (x(b, 5, 1) << 6) +
                                  (x(b, 3, 2) << 7)) + (xs(b, 12, 1) << 9));
    case A_C_SHAMT: return sfmt("%d", c_imm & 0x3F);
    case A_C_UIMM: return sfmt("0x%x", (uint32_t)c_imm << 12 >> 12);
    case A_C_LWSP_ADDR:
      return sfmt("%u(sp)", (x(b, 4, 3) << 2) + (x(b, 12, 1) << 5) + (x(b, 2, 2) << 6));
    case A_C_LDSP_ADDR:
      return sfmt("%u(sp)", (x(b, 5, 2) << 3) + (x(b, 12, 1) << 5) + (x(b, 2, 3) << 6));
    case A_C_SWSP_ADDR: return sfmt("%u(sp)", (x(b, 9, 4) << 2) + (x(b, 7, 2) << 6));
    case A_C_SDSP_ADDR: return sfmt("%u(sp)", (x(b, 10, 3) << 3) + (x(b, 7, 3) << 6));
    case A_C_LW_ADDR:
      return sfmt("%u(%s)", (x(b, 6, 1) << 2) + (x(b, 10, 3) << 3) + (x(b, 5, 1) << 6), xpr(c_rs1s));
    case A_C_LD_ADDR: return sfmt("%u(%s)", (x(b, 10, 3) << 3) + (x(b, 5, 2) << 6), xpr(c_rs1s));
    case A_C_B_ADDR: return sfmt("%u(%s)", (x(b, 5, 1) << 1) + x(b, 6, 1), xpr(c_rs1s));
    case A_C_H_ADDR: return sfmt("%u(%s)", x(b, 5, 1) << 1, xpr(c_rs1s));
    case A_C_BRANCH_TARGET:
      *is_target = true;
      *target = (int32_t)((x(b, 3, 2) << 1) + (x(b, 10, 2) << 3) + (x(b, 2, 1) << 5) +
                          (x(b, 5, 2) << 6)) + (xs(b, 12, 1) << 8);
      return pc_relative(*target, false);
    case A_C_JUMP_TARGET:
      *is_target = true;
      *target = (int32_t)((x(b, 3, 3) << 1) + (x(b, 11, 1) << 4) + (x(b, 2, 1) << 5) +
                          (x(b, 7, 1) << 6) + (x(b, 6, 1) << 7) + (x(b, 9, 2) << 8) +
                          (x(b, 8, 1) << 10)) + (xs(b, 12, 1) << 11);
      return pc_relative(*target, false);
    case A_CM_JT_INDEX: return sfmt("%u", x(b, 2, 8));
    default: return std::string();
  }
}

}  // namespace

void render_spike(decoded_t &d, uint32_t insn, int xlen, unsigned ext) {
  const uint32_t b = ((insn & 3u) != 3u) ? (insn & 0xFFFFu) : insn;
  const row_t   *r = lookup(b, xlen, (ext & RV_EXT_ZCMT) != 0);
  d.operands.clear();
  if (!r) {
    d.mnemonic = "unknown";
    d.text = d.mnemonic;
    return;
  }
  d.mnemonic = r->name;
  for (unsigned i = 0; i < 4 && r->args[i] != A_NONE; i++) {
    if (i) d.operands += ", ";
    bool    is_target = false;
    int32_t target = 0;
    const size_t pos = d.operands.size();
    d.operands += render_arg(r->args[i], b, &is_target, &target);
    if (is_target) {
      d.has_target = true;
      d.target_offset = target;
      d.target_pos = pos;
    }
  }
  d.text = d.mnemonic;
  if (r->args[0] != A_NONE) {
    d.text.append(d.mnemonic.size() < 8 ? 8 - d.mnemonic.size() : 1, ' ');
    d.text += d.operands;
  }
}

}  // namespace cva6tb_tracer
