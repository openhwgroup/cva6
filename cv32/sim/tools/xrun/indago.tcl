# Indago waveform probe script
ida_database -open -wave
ida_probe -log -wave=on -wave_probe_args="uvmt_cv32_tb -depth all -all -memories -packed 2048 -unpacked 2048" -sv_all_logs

# If the tracer exists, dump the string of the disassembled instruction
if { [find -scope uvmt_cv32_tb.dut_wrap.cv32e40p_wrapper_i -instance tracer_i] != ""} {
    ida_probe -wave -wave_probe_args="uvmt_cv32_tb.dut_wrap.cv32e40p_wrapper_i.tracer_i.insn_disas -depth 1"    
    ida_probe -wave -wave_probe_args="uvmt_cv32_tb.dut_wrap.cv32e40p_wrapper_i.tracer_i.insn_regs_write -depth 1"    
}

# If the iss_wrap exists dump the string of the ISS disassembled instruction
if { [find -scope uvmt_cv32_tb -instance iss_wrap] != ""} {
    ida_probe -wave -wave_probe_args="uvmt_cv32_tb.iss_wrap.cpu.Decode -depth 1"
    ida_probe -wave -wave_probe_args="uvmt_cv32_tb.iss_wrap.cpu.Change -depth 1"
}

run
exit
