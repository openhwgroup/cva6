# Indago waveform probe script
ida_database -open -wave
ida_probe -log -wave=on -wave_probe_args="uvmt_cv32e40s_tb -depth all -all -memories" -sv_all_logs

# If the tracer exists, dump the string of the disassembled instruction
if { [find -scope uvmt_cv32e40s_tb.dut_wrap.cv32e40s_wrapper_i -instance tracer_i] != ""} {
    ida_probe -wave -wave_probe_args="uvmt_cv32e40s_tb.dut_wrap.cv32e40s_wrapper_i.tracer_i.insn_disas -depth 1"    
    ida_probe -wave -wave_probe_args="uvmt_cv32e40s_tb.dut_wrap.cv32e40s_wrapper_i.tracer_i.insn_regs_write -depth 1"    
}

# If the iss_wrap exists dump the string of the ISS disassembled instruction
if { [find -scope uvmt_cv32e40s_tb -instance iss_wrap] != ""} {
    ida_probe -wave -wave_probe_args="uvmt_cv32e40s_tb.iss_wrap.cpu.state.decode -depth 1"    
}

# Only execute if we are not in interactive mode 
# When in interactive (gui) mode the env variable INDAGO_ENABLE_INTERACTIVE_DEBUG will exist
if { ![info exists ::env(INDAGO_ENABLE_INTERACTIVE_DEBUG)] } {
    run
    exit
}

