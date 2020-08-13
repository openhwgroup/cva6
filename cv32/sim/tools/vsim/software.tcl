# add fc execution trace
set rvcores [find instances -recursive -bydu riscv_core -nodu]
set fpuprivate [find instances -recursive -bydu fpu_private]

if {$rvcores ne ""} {

    add wave -group "Software Debugging" $rvcores/clk_i
    add wave -group "Software Debugging" -divider "Instructions at ID stage, sampled half a cycle later"
    add wave -group "Software Debugging" $rvcores/riscv_tracer_i/insn_disas
    add wave -group "Software Debugging" $rvcores/riscv_tracer_i/insn_pc
    add wave -group "Software Debugging" $rvcores/riscv_tracer_i/insn_val
    add wave -group "Software Debugging" -divider "Program counter at ID and IF stage"
    add wave -group "Software Debugging" $rvcores/pc_id
    add wave -group "Software Debugging" $rvcores/pc_if
    add wave -group "Software Debugging" -divider "Register File contents"
    add wave -group "Software Debugging" $rvcores/id_stage_i/registers_i/riscv_register_file_i/mem
    if {$fpuprivate ne ""} {
	add wave -group "Software Debugging" $rvcores/id_stage_i/registers_i/riscv_register_file_i/mem_fp
    }

}

configure wave -namecolwidth  250
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -timelineunits ns
