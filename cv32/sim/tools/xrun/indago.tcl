# Indago waveform probe script
ida_database -open -wave
ida_probe -log -wave=on -wave_probe_args="uvmt_cv32_tb -depth all" -sv_all_logs
ida_probe -wave -wave_probe_args="uvmt_cv32_tb.dut_wrap.cv32e40p_wrapper_i.core_i.tracer_i.insn_disas -depth 1"

run
exit
