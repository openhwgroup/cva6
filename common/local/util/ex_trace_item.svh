// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 17.06.2017
// Description: Instruction tracer single exception item

`ifndef VERILATOR
class ex_trace_item;
    // contains a human readable form of the cause value
    string                  cause_s;
    logic [63:0]            cause;
    logic [63:0]            tval;
    logic [riscv::VLEN-1:0] pc;

    function new (logic [riscv::VLEN-1:0] pc, logic [63:0] cause, logic [63:0] tval);

        this.cause = cause;

        case (cause)
            riscv::INSTR_ADDR_MISALIGNED: this.cause_s = "Instruction Address Misaligned";
            riscv::INSTR_ACCESS_FAULT:    this.cause_s = "Instruction Access Fault";
            riscv::ILLEGAL_INSTR:         this.cause_s = "Illegal Instruction";
            riscv::BREAKPOINT:            this.cause_s = "Breakpoint";
            riscv::LD_ADDR_MISALIGNED:    this.cause_s = "Load Address Misaligned";
            riscv::LD_ACCESS_FAULT:       this.cause_s = "Load Access Fault";
            riscv::ST_ADDR_MISALIGNED:    this.cause_s = "Store Address Misaligned";
            riscv::ST_ACCESS_FAULT:       this.cause_s = "Store Access Fault";
            riscv::ENV_CALL_UMODE:        this.cause_s = "Environment Call User Mode";
            riscv::ENV_CALL_SMODE:        this.cause_s = "Environment Call Supervisor Mode";
            riscv::ENV_CALL_MMODE:        this.cause_s = "Environment Call Machine Mode";
            riscv::INSTR_PAGE_FAULT:      this.cause_s = "Instruction Page Fault";
            riscv::LOAD_PAGE_FAULT:       this.cause_s = "Load Page Fault";
            riscv::STORE_PAGE_FAULT:      this.cause_s = "Store Page Fault";
            riscv::S_SW_INTERRUPT:        this.cause_s = "Supervisor Software Interrupt";
            riscv::M_SW_INTERRUPT:        this.cause_s = "Machine Software Interrupt";
            riscv::S_TIMER_INTERRUPT:     this.cause_s = "Supervisor Timer Interrupt";
            riscv::M_TIMER_INTERRUPT:     this.cause_s = "Machine Timer Interrupt";
            riscv::S_EXT_INTERRUPT:       this.cause_s = "Supervisor External Interrupt";
            riscv::M_EXT_INTERRUPT:       this.cause_s = "Machine External Interrupt";
            riscv::DEBUG_REQUEST:         this.cause_s = "Request Debug Mode";
            default: this.cause_s = "Interrupt";
        endcase

        this.tval = tval;
        this.pc = pc;
    endfunction : new

    function string printException();
        string s;
        s = $sformatf("Exception @%10t, PC: %h, Cause: %s", $time, this.pc, this.cause_s);
        // write out tval if it wasn't an environment call or interrupt, in that case the tval field has no meaning
        if (!(this.cause inside {
                riscv::ENV_CALL_MMODE,
                riscv::ENV_CALL_SMODE,
                riscv::ENV_CALL_UMODE,
                riscv::S_SW_INTERRUPT,
                riscv::M_SW_INTERRUPT,
                riscv::S_TIMER_INTERRUPT,
                riscv::M_TIMER_INTERRUPT,
                riscv::S_EXT_INTERRUPT,
                riscv::M_EXT_INTERRUPT
            }))
            s = $sformatf("%s, \n\t\t\t\ttval: %h", s, this.tval);
        return s;
    endfunction

endclass : ex_trace_item
`endif
