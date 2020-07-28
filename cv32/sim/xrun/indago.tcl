# Indago waveform probe script
ida_database -open -wave
ida_probe -log -wave=on -wave_probe_args="uvmt_cv32_tb -depth all" -sv_all_logs

run
exit
