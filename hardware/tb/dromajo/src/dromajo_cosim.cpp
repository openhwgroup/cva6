/*
 * API for Dromajo-based cosimulation
 *
 * Copyright (C) 2018,2019, Esperanto Technologies Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License")
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include "dromajo.h"
#include "dromajo_cosim.h"
#include "cutils.h"
#include "iomem.h"
#include "riscv_machine.h"
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <assert.h>

/*
 * dromajo_cosim_init --
 *
 * Creates and initialize the state of the RISC-V ISA golden model
 * Returns NULL upon failure.
 */
dromajo_cosim_state_t *dromajo_cosim_init(int argc, char *argv[])
{
    RISCVMachine *m = virt_machine_main(argc, argv);

#ifdef LIVECACHE
    //m->llc = new LiveCache("LLC", 1024*1024*32); // 32MB LLC (should be ~2x larger than real)
    m->llc = new LiveCache("LLC", 1024*32); // Small 32KB for testing
#endif

    m->common.cosim = true;
    m->common.pending_interrupt = -1;
    m->common.pending_exception = -1;

    return (dromajo_cosim_state_t *)m;
}

void dromajo_cosim_fini(dromajo_cosim_state_t *state)
{
    virt_machine_end((RISCVMachine *)state);
}

static bool is_store_conditional(uint32_t insn)
{
    int opcode = insn & 0x7f, funct3 = insn >> 12 & 7;
    return opcode == 0x2f && insn >> 27 == 3 && (funct3 == 2 || funct3 == 3);
}

static inline uint32_t get_field1(uint32_t val, int src_pos,
                                  int dst_pos, int dst_pos_max)
{
    int mask;
    assert(dst_pos_max >= dst_pos);
    mask = ((1 << (dst_pos_max - dst_pos + 1)) - 1) << dst_pos;
    if (dst_pos >= src_pos)
        return (val << (dst_pos - src_pos)) & mask;
    else
        return (val >> (src_pos - dst_pos)) & mask;
}

/* detect AMO instruction, including LR, but excluding SC */
static inline bool is_amo(uint32_t insn)
{
    int opcode = insn & 0x7f;
    if (opcode != 0x2f)
        return false;

    switch (insn >> 27) {
    case 1: /* amiswap.w */
    case 2: /* lr.w */
    case 0: /* amoadd.w */
    case 4: /* amoxor.w */
    case 0xc: /* amoand.w */
    case 0x8: /* amoor.w */
    case 0x10: /* amomin.w */
    case 0x14: /* amomax.w */
    case 0x18: /* amominu.w */
    case 0x1c: /* amomaxu.w */
        return true;
    default:
        return false;
    }
}

/*
 * is_mmio_load() --
 * calculated the effective address and check if the physical backing
 * is MMIO space.  NB: get_phys_addr() is the identity if the CPU is
 * running without virtual memory enabled.
 */
static inline bool is_mmio_load(RISCVCPUState *s,
                                int            reg,
                                int            offset,
                                uint64_t       mmio_start,
                                uint64_t       mmio_end)
{
    uint64_t pa;
    uint64_t va = riscv_get_reg_previous(s, reg) + offset;

    if(!riscv_cpu_get_phys_addr(s, va, ACCESS_READ, &pa) &&
       mmio_start <= pa && pa < mmio_end) {
        return true;
    }

    if (s->machine->mmio_addrset_size > 0) {
        RISCVMachine *m = s->machine;
        for (size_t i =0; i < m->mmio_addrset_size; ++i) {
            uint64_t start = m->mmio_addrset[i].start;
            uint64_t end = m->mmio_addrset[i].start + m->mmio_addrset[i].size;
            if (!riscv_cpu_get_phys_addr(s, va, ACCESS_READ, &pa) && start <= pa && pa < end)
                return true;
        }
    }

    return false;
}

/*
 * handle_dut_overrides --
 *
 * Certain sequences cannot be simulated faithfully so this function
 * is responsible for detecting them and overriding the simulation
 * with the DUT result.  Cases include interrupts, loads from MMIO
 * space, and certain CRSs like cycle and time.
 *
 * Right now we handle just mcycle.
 */
static inline void handle_dut_overrides(RISCVCPUState *s,
                                        uint64_t mmio_start,
                                        uint64_t mmio_end,
                                        int priv,
                                        uint64_t pc, uint32_t insn,
                                        uint64_t emu_wdata,
                                        uint64_t dut_wdata)
{
    int opcode = insn & 0x7f;
    int csrno  = insn >> 20;
    int rd     = (insn >> 7) & 0x1f;
    int rdc    = ((insn >> 2) & 7) + 8;
    int reg, offset;

    /* Catch reads from CSR mcycle, ucycle, instret, hpmcounters,
     * hpmoverflows, mip, and sip.
     * If the destination register is x0 then it is actually a csr-write
     */
    if (opcode == 0x73 && rd != 0 &&
        (0xB00 <= csrno && csrno < 0xB20 ||
         0xC00 <= csrno && csrno < 0xC20 ||
         (csrno == 0x344 /* mip */ ||
          csrno == 0x144 /* sip */)))
        riscv_set_reg(s, rd, dut_wdata);

    /* Catch loads and amo from MMIO space */
    if ((opcode == 3 || is_amo(insn)) && rd != 0) {
        reg = (insn >> 15) & 0x1f;
        offset = opcode == 3 ? (int32_t) insn >> 20 : 0;
    } else if ((insn & 0xE003) == 0x6000 && rdc != 0) {
        // c.ld  011  uimm[5:3] rs1'[2:0]       uimm[7:6] rd'[2:0] 00
        reg = ((insn >> 7) & 7) + 8;
        offset = get_field1(insn, 10, 3, 5) | get_field1(insn, 5, 6, 7);
        rd = rdc;
    } else if ((insn & 0xE003) == 0x4000 && rdc != 0) {
        // c.lw  010  uimm[5:3] rs1'[2:0] uimm[2] uimm[6] rd'[2:0] 00
        reg = ((insn >> 7) & 7) + 8;
        offset = (get_field1(insn, 10, 3, 5) |
                  get_field1(insn,  6, 2, 2) |
                  get_field1(insn,  5, 6, 6));
        rd = rdc;
    } else
        return;

    if (is_mmio_load(s, reg, offset, mmio_start, mmio_end)) {
        riscv_set_reg(s, rd, dut_wdata);
    }
}

/*
 * dromajo_cosim_raise_trap --
 *
 * DUT raises a trap (exception or interrupt) and provides the cause.
 * MSB indicates an asynchronous interrupt, synchronous exception
 * otherwise.
 */
void dromajo_cosim_raise_trap(dromajo_cosim_state_t *state, int hartid, int64_t cause)
{
    VirtMachine   *m = (VirtMachine  *)state;

    if (cause < 0) {
        assert(m->pending_interrupt == -1);
        m->pending_interrupt = cause & 63;
        fprintf(dromajo_stderr, "DUT raised interrupt %d\n", m->pending_interrupt);
    } else {
        m->pending_exception = cause;
    }
}

/*
 * dromajo_cosim_step --
 *
 * executes exactly one instruction in the golden model and returns
 * zero if the supplied expected values match and execution should
 * continue.  A non-zero value signals termination with the exit code
 * being the upper bits (ie., all but LSB).  Caveat: the DUT provides
 * the instructions bit after expansion, so this is only matched on
 * non-compressed instruction.
 *
 * There are a number of situations where the model cannot match the
 * DUT, such as loads from IO devices, interrupts, and CSRs cycle,
 * time, and instret.  For all these cases the model will override
 * with the expected values.
 */
int dromajo_cosim_step(dromajo_cosim_state_t *state,
                       int                    hartid,
                       uint64_t               dut_pc,
                       uint32_t               dut_insn,
                       uint64_t               dut_wdata,
                       uint64_t               dut_mstatus,
                       bool                   check)
{
    RISCVMachine  *r = (RISCVMachine *)state;
    RISCVCPUState *s = r->cpu_state[hartid];
    uint64_t emu_pc, emu_wdata = 0;
    int      emu_priv;
    uint32_t emu_insn;
    bool     emu_wrote_data = false;
    int      exit_code = 0;
    bool     verbose = true;
    int      iregno, fregno;

    uint32_t tohost;
    bool fail = true;
    tohost = riscv_phys_read_u32(r->cpu_state[hartid], r->htif_tohost_addr, &fail);
    if (!fail && tohost & 1) {
        fprintf(dromajo_stderr, "Done. Cosim passed!\n\n");
        return 2;
    }

    /* Succeed after N instructions without failure. */
    if (r->common.maxinsns == 0) {
        return 1;
    }

    r->common.maxinsns--;

    if (riscv_terminated(s)) {
        return 1;
    }

    /*
     * Execute one instruction in the simulator.  Because exceptions
     * may fire, the current instruction may not be executed, thus we
     * have to iterate until one does.
     */
    iregno = -1;
    fregno = -1;

    for (;;) {
        emu_priv = riscv_get_priv_level(s);
        emu_pc   = riscv_get_pc(s);
        riscv_read_insn(s, &emu_insn, emu_pc);

        if ((emu_insn & 3) != 3)
            emu_insn &= 0xFFFF;

        if (emu_pc == dut_pc && emu_insn == dut_insn &&
            is_store_conditional(emu_insn) && dut_wdata != 0) {

            /* When DUT fails an SC, we must simulate the same behavior */
            iregno = emu_insn >> 7 & 0x1f;
            if (iregno > 0)
                riscv_set_reg(s, iregno, dut_wdata);
            riscv_set_pc(s, emu_pc + 4);
            break;
        }

        if (r->common.pending_interrupt != -1 && r->common.pending_exception != -1) {
            /* On the DUT, the interrupt can race the exception.
               Let's try to match that behavior */

            fprintf(dromajo_stderr, "DUT also raised exception %d\n", r->common.pending_exception);
            riscv_cpu_interp64(s, 1); // Advance into the exception

            int cause = s->priv == PRV_S ? s->scause : s->mcause;

            if (r->common.pending_exception != cause) {
                char priv = s->priv["US?M"];

                /* Unfortunately, handling the error case is awkward,
                 * so we just exit from here */

                fprintf(dromajo_stderr, "%d 0x%016" PRIx64 " ", emu_priv, emu_pc);
                fprintf(dromajo_stderr, "(0x%08x) ", emu_insn);
                fprintf(dromajo_stderr,
                        "[error] EMU %cCAUSE %d != DUT %cCAUSE %d\n",
                        priv, cause, priv, r->common.pending_exception);

                return 0x1FFF;
            }
        }

        if (r->common.pending_interrupt != -1)
            riscv_cpu_set_mip(s, riscv_cpu_get_mip(s) | 1 << r->common.pending_interrupt);

        if (riscv_cpu_interp64(s, 1) != 0) {
            iregno = riscv_get_most_recently_written_reg(s);
            fregno = riscv_get_most_recently_written_fp_reg(s);
            break;
        }

        r->common.pending_interrupt = -1;
        r->common.pending_exception = -1;

    }

    if (check)
        handle_dut_overrides(s, r->mmio_start, r->mmio_end,
                             emu_priv, emu_pc, emu_insn, emu_wdata, dut_wdata);

    if (verbose) {
        fprintf(dromajo_stderr, "%d 0x%016" PRIx64 " ", emu_priv, emu_pc);
        fprintf(dromajo_stderr, "(0x%08x) ", emu_insn);
    }

    if (iregno > 0) {
        emu_wdata = riscv_get_reg(s, iregno);
        emu_wrote_data = 1;
        if (verbose)
            fprintf(dromajo_stderr, "x%-2d 0x%016" PRIx64, iregno, emu_wdata);
    } else if (fregno >= 0) {
        emu_wdata = riscv_get_fpreg(s, fregno);
        emu_wrote_data = 1;
        if (verbose)
            fprintf(dromajo_stderr, "f%-2d 0x%016" PRIx64, fregno, emu_wdata);
    } else
        fprintf(dromajo_stderr, "                      ");

    if (verbose)
        fprintf(dromajo_stderr, " DASM(0x%08x)\n", emu_insn);

    if (!check)
        return 0;

    uint64_t emu_mstatus = riscv_cpu_get_mstatus(s);

    /*
     * Ariane does not commit ecalls and ebreaks. So we dromajo
     * needs to skip this one. TODO: maybe make this part of cfg
     */
    bool skip_commit = false;
    for (uint64_t i = 0; i < r->skip_commit_size; i++) {
      if (r->skip_commit[i] == emu_insn) {
        skip_commit = true;
        break;
      }
    }

    if (skip_commit) {
        fprintf(dromajo_stderr, "skipping emu_insn 0x%08x\n", emu_insn);
        exit_code = 3;
    /*
     * XXX We currently do not compare mstatus because DUT's mstatus
     * varies between pre-commit (all FP instructions) and post-commit
     * (CSR instructions).
     */
    } else if (emu_pc      != dut_pc                           ||
               emu_insn    != dut_insn  && (emu_insn & 3) == 3 || // DUT expands all C instructions
               emu_wdata   != dut_wdata && emu_wrote_data) {

        fprintf(dromajo_stderr, "[error] EMU PC %016" PRIx64 ", DUT PC %016" PRIx64 "\n",
                emu_pc, dut_pc);
        fprintf(dromajo_stderr, "[error] EMU INSN %08x, DUT INSN %08x\n",
                emu_insn, dut_insn);
        if (emu_wrote_data)
            fprintf(dromajo_stderr, "[error] EMU WDATA %016" PRIx64 ", DUT WDATA %016" PRIx64 "\n",
                    emu_wdata, dut_wdata);
        fprintf(dromajo_stderr, "[error] EMU MSTATUS %08" PRIx64 ", DUT MSTATUS %08" PRIx64 "\n",
                emu_mstatus, dut_mstatus);
        fprintf(dromajo_stderr, "[error] DUT pending exception %d pending interrupt %d\n",
                r->common.pending_exception, r->common.pending_interrupt);
        exit_code = 0x1FFF;
    }

    riscv_cpu_sync_regs(s);

    if (exit_code == 0 || skip_commit)
        riscv_cpu_sync_regs(s);

    return exit_code;
}
