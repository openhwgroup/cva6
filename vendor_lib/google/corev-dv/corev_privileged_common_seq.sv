/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
 * Copyright 2020 OpenHW Group
 * Copyright 2020 Silicon Labs, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//-----------------------------------------------------------------------------------------
// CORE-V privileged mode sequence customizations
//
// Overrides enter_privileged_mode()
//-----------------------------------------------------------------------------------------

class corev_privileged_common_seq extends riscv_privileged_common_seq;

    `uvm_object_utils(corev_privileged_common_seq)

    function new(string name = "");
        super.new(name);
    endfunction

    // Override this function to use "ret" instead of "mret" to exit the function
    // in the assembly.
    // When initializing a mode this section can enable interrupts, which would blow away
    // any value in *epc register.  Therefore a manual j->mret calling routine does not work
    // and can cause infinite loop.
    // Therefore the calling section will use jal and expect a ret to return (using x1)
    virtual function void enter_privileged_mode(input privileged_mode_t mode,
                                                output string instrs[$]);
        string label = format_string({$sformatf("%0sinit_%0s:",
                                    hart_prefix(hart), mode.name())}, LABEL_STR_LEN);
        string ret_instr[] = {"ret"};
        riscv_privil_reg regs[$];
        label = label.tolower();
        setup_mmode_reg(mode, regs);
        if(mode == SUPERVISOR_MODE) begin
            setup_smode_reg(mode, regs);
        end
        if(mode == USER_MODE) begin
            setup_umode_reg(mode, regs);
        end
        if(cfg.virtual_addr_translation_on) begin
            setup_satp(instrs);
        end
        gen_csr_instr(regs, instrs);
        // Use mret/sret to switch to the target privileged mode
        instrs.push_back(ret_instr[0]);
        foreach(instrs[i]) begin
            instrs[i] = {indent, instrs[i]};
        end
        instrs.push_front(label);
    endfunction : enter_privileged_mode

endclass : corev_privileged_common_seq
