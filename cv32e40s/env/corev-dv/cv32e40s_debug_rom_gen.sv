//Copyright 2020 Silicon Labs, Inc.

//This file, and derivatives thereof are licensed under the
//Solderpad License, Version 2.0 (the "License");
//Use of this file means you agree to the terms and conditions
//of the license and are in full compliance with the License.
//You may obtain a copy of the License at
//
//    https://solderpad.org/licenses/SHL-2.0/
//
//Unless required by applicable law or agreed to in writing, software
//and hardware implementations thereof
//distributed under the License is distributed on an "AS IS" BASIS,
//WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//See the License for the specific language governing permissions and
//limitations under the License.
//
//
class cv32e40s_debug_rom_gen extends riscv_debug_rom_gen;
    string debug_dret[$];

    `uvm_object_utils(cv32e40s_debug_rom_gen)

    function new (string name = "");
        super.new(name);
    endfunction

    virtual function void gen_program();
        string sub_program_name[$] = {};
        cv32e40s_instr_gen_config cfg_corev;

        // CORE-V Addition
        // Insert section info so linker can place
        // debug code at the correct adress
        instr_stream.push_back(".section .debugger, \"ax\"");

        // CORE-V Addition
        // Cast CORE-V derived handle to enable fetching core-v config fields
        `DV_CHECK($cast(cfg_corev, cfg))

        // Randomly add a WFI at start of ddebug rom
        // This will be treaed as a NOP always, but added here to close instructon
        // combination coverage (i.e. ebreak->wfi)
        if (!cfg.no_wfi) begin
            randcase
                1:  debug_main.push_back("wfi");
                4: begin /* insert nothing */ end
            endcase
        end

        // The following is directly copied from riscv_debug_rom_gen.sv
        // Changes:
        // - Altering the stack push/pop to use custom debugger stack
        if (!cfg.gen_debug_section) begin
            // If the debug section should not be generated, we just populate it
            // with a dret instruction.
            debug_main = {dret};
            gen_section($sformatf("%0sdebug_rom", hart_prefix(hart)), debug_main);
        end else begin
            // Check the debugger stack pointer to check for a null pointer in cfg.dp
            // and initialize
            debug_main.push_back($sformatf("bne x%0d, zero, dp_init_done # One time initialization of the debug pointer (x%0d)", cfg_corev.dp, cfg_corev.dp));
            debug_main.push_back($sformatf("la  x%0d, debugger_stack_end", cfg_corev.dp));
            debug_main.push_back($sformatf("dp_init_done:"));

            if (cfg.enable_ebreak_in_debug_rom) begin
                debug_main.push_back("# This ebreak header will ensure that re-entry of debug handler will not re-push stack");
                debug_main.push_back("# If dscratch0 is non-zero then jump directly to debug_end to pop stack and end then dret");
                gen_ebreak_header();
            end
            // Need to save off GPRs to avoid modifying program flow
            push_gpr_to_debugger_stack(cfg_corev, debug_main);
            // Signal that the core entered debug rom only if the rom is actually
            // being filled with random instructions to prevent stress tests from
            // having to execute unnecessary push/pop of GPRs on the stack ever
            // time a debug request is sent
            gen_signature_handshake(debug_main, CORE_STATUS, IN_DEBUG_MODE);
            if (cfg.enable_ebreak_in_debug_rom) begin
                // send dpc and dcsr to testbench, as this handshake will be
                // executed twice due to the ebreak loop, there should be no change
                // in their values as by the Debug Mode Spec Ch. 4.1.8
                gen_signature_handshake(.instr(debug_main), .signature_type(WRITE_CSR), .csr(DCSR));
                gen_signature_handshake(.instr(debug_main), .signature_type(WRITE_CSR), .csr(DPC));
            end
            if (cfg.set_dcsr_ebreak) begin
                // We want to set dcsr.ebreak(m/s/u) to 1'b1, depending on what modes
                // are available.
                // TODO(udinator) - randomize the dcsr.ebreak setup
                gen_dcsr_ebreak();
            end
            if (cfg.enable_debug_single_step) begin
                gen_single_step_logic();
            end
            gen_dpc_update();
            // write DCSR to the testbench for any analysis
            gen_signature_handshake(.instr(debug_main), .signature_type(WRITE_CSR), .csr(DCSR));
            if (cfg.enable_ebreak_in_debug_rom || cfg.set_dcsr_ebreak) begin
                gen_increment_ebreak_counter();
            end
            format_section(debug_main);
            gen_sub_program(hart, sub_program[hart], sub_program_name,
                            cfg.num_debug_sub_program, 1'b1, "debug_sub");
            main_program[hart] = riscv_instr_sequence::type_id::create("debug_program");
            main_program[hart].instr_cnt = cfg.debug_program_instr_cnt;
            main_program[hart].is_debug_program = 1;
            main_program[hart].cfg = cfg;
            `DV_CHECK_RANDOMIZE_FATAL(main_program[hart])
            main_program[hart].gen_instr(.is_main_program(1'b1), .no_branch(cfg.no_branch_jump));
            gen_callstack(main_program[hart], sub_program[hart], sub_program_name,
                            cfg.num_debug_sub_program);
            main_program[hart].post_process_instr();
            main_program[hart].generate_instr_stream(.no_label(1'b1));
            insert_sub_program(sub_program[hart], debug_main);
            debug_main = {debug_main, main_program[hart].instr_string_list};


            // Create the ebreak end
            if (cfg.enable_ebreak_in_debug_rom) begin
                gen_ebreak_footer();
            end
            pop_gpr_from_debugger_stack(cfg_corev, debug_end);
            if (cfg.enable_ebreak_in_debug_rom) begin
                gen_restore_ebreak_scratch_reg();
            end

            // Create the debug_dret section
            //pop_gpr_from_debugger_stack(cfg_corev, debug_dret);
            //debug_dret = {debug_dret, dret};

            //format_section(debug_end);
            gen_section($sformatf("%0sdebug_rom", hart_prefix(hart)), debug_main);

            // Randomly add a WFI at end of debug rom
            // This will be treaed as a NOP always, but added here to close instructon
            // combination coverage (i.e. ebreak->wfi)
            if (!cfg.no_wfi) begin
                randcase
                    1:  debug_end.push_back("wfi");
                    4: begin /* insert nothing */ end
                endcase
            end

            debug_end = {debug_end, dret};

            gen_section($sformatf("%0sdebug_end", hart_prefix(hart)), debug_end);
        end
        gen_debug_exception_handler();
    endfunction : gen_program

    virtual function void gen_debug_exception_handler();

        cv32e40s_instr_gen_config cfg_corev;

        // CORE-V Addition
        // Cast CORE-V derived handle to enable fetching core-v config fields
        `DV_CHECK($cast(cfg_corev, cfg))

        // Insert section info so linker can place
        // debug exception code at the correct adress
        instr_stream.push_back(".section .debugger_exception, \"ax\"");

        if (cfg_corev.exit_on_debug_exception) begin
            str = {"la x1, test_done", "jr x1"};
        end
        else begin
            str = {"ebreak"};
        end

        gen_section($sformatf("%0sdebug_exception", hart_prefix(hart)), str);

        // Insert section info to place remaining code in the
        // original section
        instr_stream.push_back(".section text");
    endfunction : gen_debug_exception_handler

endclass : cv32e40s_debug_rom_gen

