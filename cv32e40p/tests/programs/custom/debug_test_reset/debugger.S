
/*
**
** Copyright 2020 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
*******************************************************************************
** Debugger code
*******************************************************************************
*/


.section .debugger, "ax"
.global _debugger_start
.set test_ret_val, 0x20000000
.set test_fail, 0x1
.set test_debugger_ok, 0xa5

_debugger_start:
    // No code should have been run before this
    // check dpc == boot_addr == 0x80
    csrr t1, dpc
    li t2, 0x80 # Boot addr
    bne t1, t2, _debugger_error

    // Write known value to memory
    // We don't have any globals or pointers
    // at this time, so we must rely on
    // memory (hopefully) not being used
    la a0, test_debugger_entry
    li t0, test_debugger_ok
    sw t0, 0(a0)

_debugger_trigger_regs_access:
    # R/W trigger regs otherwise not accessed
    # to close coverage holes
    li t0, 0xff
    csrw 0x7a4, t0 # tinfo
    csrr t0, 0x7a4
    li t1, 4
    bne t0, t1, _debugger_error

    li t0, 0xff
    csrw 0x7a3, t0 # tdata3
    csrr t0, 0x7a3
    bne t0, x0, _debugger_error

    li t0, 0xff
    csrw 0x7a0, t0 # tsel
    csrr t0, 0x7a0
    bne t0, x0, _debugger_error

    # CSR access with all instructions to cover
    # functional coverage
    # TDATA1, CSRRSI
    csrr t1, 0x7A1
    csrrsi t0, 0x7A1, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A1
    li t1, 2<<28 | 1<<27 | 1<<12 | 1<<6 | 1<<2
    bne t0, t1, _debugger_error

    # TDATA1, CSRRCI
    csrr t1, 0x7A1
    csrrci t0, 0x7A1, 0x4 # Clear bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A1
    li t1, 2<<28 | 1<<27 | 1<<12 | 1<<6 | 0<<2
    bne t0, t1, _debugger_error

    # TDATA1, CSRRS
    csrr t1, 0x7A1
    li t0, 0x4
    csrrs t0, 0x7A1, t0 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A1
    li t1, 2<<28 | 1<<27 | 1<<12 | 1<<6 | 1<<2
    bne t0, t1, _debugger_error

    # TDATA1, CSRRC
    csrr t1, 0x7A1
    li t0, 0x4
    csrrc t0, 0x7A1, t0 # Clear bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A1
    li t1, 2<<28 | 1<<27 | 1<<12 | 1<<6 | 0<<2
    bne t0, t1, _debugger_error

    # TDATA1, CSRRWI
    csrr t1, 0x7A1
    csrrwi t0, 0x7A1, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A1
    li t1, 2<<28 | 1<<27 | 1<<12 | 1<<6 | 1<<2
    bne t0, t1, _debugger_error

    # TDATA1, CSRRW
    csrr t1, 0x7A1
    li t0, 0xffffffff
    csrrw t0, 0x7A1, t0
    bne t0, t1, _debugger_error
    csrr t0, 0x7A1
    li t1, 2<<28 | 1<<27 | 1<<12 | 1<<6 | 1<<2
    bne t0, t1, _debugger_error

    # TDATA2, CSRRSI
    csrw 0x7A2, x0 # clear before test
    csrr t1, 0x7A2
    csrrsi t0, 0x7A2, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A2
    li t1,  1<<2
    bne t0, t1, _debugger_error

    # TDATA2, CSRRCI
    csrr t1, 0x7A2
    csrrci t0, 0x7A2, 0x4 # Clear bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A2
    li t1, 0x0
    bne t0, t1, _debugger_error

    # TDATA2, CSRRS
    csrr t1, 0x7A2
    li t0, 0xa5a5a5a5
    csrrs t0, 0x7A2, t0
    bne t0, t1, _debugger_error
    csrr t0, 0x7A2
    li t1,  0xa5a5a5a5
    bne t0, t1, _debugger_error

    # TDATA2, CSRRC
    csrr t1, 0x7A2
    li t0, 0xFFFFFFFF
    csrrc t0, 0x7A2, t0
    bne t0, t1, _debugger_error
    csrr t0, 0x7A2
    li t1,  0x0
    bne t0, t1, _debugger_error

    # TDATA2, CSRRWI
    csrr t1, 0x7A2
    csrrwi t0, 0x7A2, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A2
    li t1,  1<<2
    bne t0, t1, _debugger_error

    # TDATA3, CSRRSI
    csrw 0x7A3, x0 # clear before test
    csrr t1, 0x7A3
    csrrsi t0, 0x7A3, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A3
    li t1, 0
    bne t0, t1, _debugger_error

    # TDATA3, CSRRCI
    csrr t1, 0x7A3
    csrrci t0, 0x7A3, 0x4 # Clear bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A3
    li t1, 0x0
    bne t0, t1, _debugger_error

    # TDATA3, CSRRS
    csrr t1, 0x7A3
    li t0, 0xa5a5a5a5
    csrrs t0, 0x7A3, t0
    bne t0, t1, _debugger_error
    csrr t0, 0x7A3
    li t1,  0x0
    bne t0, t1, _debugger_error

    # TDATA3, CSRRC
    csrr t1, 0x7A3
    li t0, 0xFFFFFFFF
    csrrc t0, 0x7A3, t0
    bne t0, t1, _debugger_error
    csrr t0, 0x7A3
    li t1,  0x0
    bne t0, t1, _debugger_error

    # TDATA3, CSRRWI
    csrr t1, 0x7A3
    csrrwi t0, 0x7A3, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A3
    li t1,  0x0
    bne t0, t1, _debugger_error

    # TINFO, CSRRSI
    csrw 0x7A4, x0 # clear before test
    csrr t1, 0x7A4
    csrrsi t0, 0x7A4, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A4
    li t1, 4
    bne t0, t1, _debugger_error

    # TINFO, CSRRCI
    csrr t1, 0x7A4
    csrrci t0, 0x7A4, 0x4 # Clear bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A4
    li t1, 4
    bne t0, t1, _debugger_error

    # TINFO, CSRRS
    csrr t1, 0x7A4
    li t0, 0xa5a5a5a5
    csrrs t0, 0x7A4, t0
    bne t0, t1, _debugger_error
    csrr t0, 0x7A4
    li t1,  4
    bne t0, t1, _debugger_error

    # TINFO, CSRRC
    csrr t1, 0x7A4
    li t0, 0xFFFFFFFF
    csrrc t0, 0x7A4, t0
    bne t0, t1, _debugger_error
    csrr t0, 0x7A4
    li t1,  4
    bne t0, t1, _debugger_error

    # TINFO, CSRRWI
    csrr t1, 0x7A4
    csrrwi t0, 0x7A4, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A4
    li t1,  4
    bne t0, t1, _debugger_error

    # TSELECT, CSRRSI
    csrw 0x7A0, x0 # clear before test
    csrr t1, 0x7A0
    csrrsi t0, 0x7A0, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A0
    li t1, 0
    bne t0, t1, _debugger_error

    # TSELECT, CSRRCI
    csrr t1, 0x7A0
    csrrci t0, 0x7A0, 0x4 # Clear bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A0
    li t1, 0
    bne t0, t1, _debugger_error

    # TSELECT, CSRRS
    csrr t1, 0x7A0
    li t0, 0xa5a5a5a5
    csrrs t0, 0x7A0, t0
    bne t0, t1, _debugger_error
    csrr t0, 0x7A0
    li t1,  0
    bne t0, t1, _debugger_error

    # TSELECT, CSRRC
    csrr t1, 0x7A0
    li t0, 0xFFFFFFFF
    csrrc t0, 0x7A0, t0
    bne t0, t1, _debugger_error
    csrr t0, 0x7A0
    li t1,  0
    bne t0, t1, _debugger_error

    # TSELECT, CSRRWI
    csrr t1, 0x7A0
    csrrwi t0, 0x7A0, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7A0
    li t1,  0
    bne t0, t1, _debugger_error

    # Store dscratch0
    csrr t2, 0x7B2
    # DSCRATCH0, CSRRSI
    csrw 0x7B2, x0 # clear before test
    csrr t1, 0x7B2
    csrrsi t0, 0x7B2, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7B2
    li t1, 4
    bne t0, t1, _debugger_error

    # DSCRATCH0, CSRRCI
    csrr t1, 0x7B2
    csrrci t0, 0x7B2, 0x4 # Clear bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7B2
    li t1, 0
    bne t0, t1, _debugger_error

    # DSCRATCH0, CSRRS
    csrr t1, 0x7B2
    li t0, 0xa5a5a5a5
    csrrs t0, 0x7B2, t0
    bne t0, t1, _debugger_error
    csrr t0, 0x7B2
    li t1,  0xa5a5a5a5
    bne t0, t1, _debugger_error

    # DSCRATCH0, CSRRC
    csrr t1, 0x7B2
    li t0, 0xFFFFFFFF
    csrrc t0, 0x7B2, t0
    bne t0, t1, _debugger_error
    csrr t0, 0x7B2
    li t1,  0
    bne t0, t1, _debugger_error

    # DSCRATCH0, CSRRWI
    csrr t1, 0x7B2
    csrrwi t0, 0x7B2, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7B2
    li t1,  0x4
    bne t0, t1, _debugger_error
    # Restore dscratch0
    csrw 0x7B2, t2

    # Store dscratch1
    csrr t2, 0x7B3
    # DSCRATCH1, CSRRSI
    csrw 0x7B3, x0 # clear before test
    csrr t1, 0x7B3
    csrrsi t0, 0x7B3, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7B3
    li t1, 4
    bne t0, t1, _debugger_error

    # DSCRATCH1, CSRRCI
    csrr t1, 0x7B3
    csrrci t0, 0x7B3, 0x4 # Clear bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7B3
    li t1, 0
    bne t0, t1, _debugger_error

    # DSCRATCH1, CSRRS
    csrr t1, 0x7B3
    li t0, 0xa5a5a5a5
    csrrs t0, 0x7B3, t0
    bne t0, t1, _debugger_error
    csrr t0, 0x7B3
    li t1,  0xa5a5a5a5
    bne t0, t1, _debugger_error

    # DSCRATCH1, CSRRC
    csrr t1, 0x7B3
    li t0, 0xFFFFFFFF
    csrrc t0, 0x7B3, t0
    bne t0, t1, _debugger_error
    csrr t0, 0x7B3
    li t1,  0
    bne t0, t1, _debugger_error

    # DSCRATCH1, CSRRWI
    csrr t1, 0x7B3
    csrrwi t0, 0x7B3, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7B3
    li t1,  0x4
    bne t0, t1, _debugger_error
    # Restore dscratch1
    csrw 0x7B3, t2

    # Store dpc
    csrr t2, 0x7B1
    # DPC, CSRRSI
    csrw 0x7B1, x0 # clear before test
    csrr t1, 0x7B1
    csrrsi t0, 0x7B1, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7B1
    li t1, 4
    bne t0, t1, _debugger_error

    # DPC, CSRRCI
    csrr t1, 0x7B1
    csrrci t0, 0x7B1, 0x4 # Clear bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7B1
    li t1, 0
    bne t0, t1, _debugger_error

    # DPC, CSRRS
    csrr t1, 0x7B1
    li t0, 0xfffffff0
    csrrs t0, 0x7B1, t0
    bne t0, t1, _debugger_error
    csrr t0, 0x7B1
    li t1,  0xfffffff0
    bne t0, t1, _debugger_error

    # DPC, CSRRC
    csrr t1, 0x7B1
    li t0, 0xFFFFFFFF
    csrrc t0, 0x7B1, t0
    bne t0, t1, _debugger_error
    csrr t0, 0x7B1
    li t1,  0
    bne t0, t1, _debugger_error

    # DPC, CSRRWI
    csrr t1, 0x7B1
    csrrwi t0, 0x7B1, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, 0x7B1
    li t1,  0x4
    bne t0, t1, _debugger_error

    # Restore dpc
    csrw 0x7B1, t2

    # Store dcsr
    csrr t2, dcsr
    # DCSR, CSRRSI
    csrw dcsr, x0 # clear before test
    csrr t1, dcsr
    csrrsi t0, dcsr, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, dcsr
    addi t1, t2, 0x4
    bne t0, t1, _debugger_error

    # DCSR, CSRRCI
    csrr t1, dcsr
    csrrci t0, dcsr, 0x4 # Clear bit 2
    bne t0, t1, _debugger_error
    csrr t0, dcsr
    bne t0, t2, _debugger_error

    # DCSR, CSRRS
    csrr t1, dcsr
    li t0, 0
    addi t0, t2, 4
    csrrs t0, dcsr, t0
    bne t0, t1, _debugger_error
    csrr t0, dcsr
    addi t1, t2, 0x4
    bne t0, t1, _debugger_error

    # DCSR, CSRRC
    csrr t1, dcsr
    li t0, 0x4
    csrrc t0, dcsr, t0
    bne t0, t1, _debugger_error
    csrr t0, dcsr
    bne t0, t2, _debugger_error

    # DCSR, CSRRWI
    csrr t1, dcsr
    csrrwi t0, dcsr, 0x4 # Set bit 2
    bne t0, t1, _debugger_error
    csrr t0, dcsr
    addi t1, t2, 0x4
    bne t0, t1, _debugger_error

    # Restore dpc
    csrw dcsr, t2
    dret

_debugger_error:
    li a0, test_ret_val
    li t0, test_fail
    sw t0, 0(a0)
    dret

.section .data
.global test_debugger_entry
test_debugger_entry:
    .word 0
