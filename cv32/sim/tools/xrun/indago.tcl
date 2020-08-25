# Indago waveform probe script
ida_database -open -wave
ida_probe -log -wave=on -wave_probe_args="uvmt_cv32_tb -depth all" -sv_all_logs

# If the tracer exists, dump the string of the disassembled instruction
if { [find -scope uvmt_cv32_tb.dut_wrap.cv32e40p_wrapper_i.core_i -instance tracer_i] != ""} {
    ida_probe -wave -wave_probe_args="uvmt_cv32_tb.dut_wrap.cv32e40p_wrapper_i.core_i.tracer_i.insn_disas -depth 1"
}

run
exit
