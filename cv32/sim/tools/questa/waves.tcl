# catch {
#     if {$trdb_all ne ""} {
#	foreach inst $trdb_all {
#	    add wave -group [file tail $inst] $inst/*
#	}
#     }
# } err

# if {$err ne ""} {
#     puts "\[TCL\]: Suppressed error: $err"
# }

# add fc
set rvcores [find instances -recursive -bydu riscv_core -nodu]
set fpuprivate [find instances -recursive -bydu fpu_private]
set tb_top [find instances -recursive -bydu tb_top -nod]
set mm_ram [find instances -recursive -bydu mm_ram -nod]
set dp_ram [find instances -recursive -bydu dp_ram -nod]

if {$tb_top ne ""} {
    foreach inst $tb_top {
	add wave -group [file tail $inst] $inst/*
    }
}

if {$mm_ram ne ""} {
    foreach inst $mm_ram {
	add wave -group [file tail $inst] $inst/*
    }
}

if {$dp_ram ne ""} {
    foreach inst $dp_ram {
	add wave -group [file tail $inst] $inst/*
    }
}

if {$rvcores ne ""} {
  set rvprefetch [find instances -recursive -bydu riscv_prefetch_L0_buffer -nodu]

  add wave -group "Core"                                     $rvcores/*
  add wave -group "IF Stage" -group "Hwlp Ctrl"              $rvcores/if_stage_i/hwloop_controller_i/*
  if {$rvprefetch ne ""} {
    add wave -group "IF Stage" -group "Prefetch" -group "L0"   $rvcores/if_stage_i/prefetch_128/prefetch_buffer_i/L0_buffer_i/*
    add wave -group "IF Stage" -group "Prefetch"               $rvcores/if_stage_i/prefetch_128/prefetch_buffer_i/*
  } {
    add wave -group "IF Stage" -group "Prefetch" -group "FIFO" $rvcores/if_stage_i/prefetch_32/prefetch_buffer_i/fifo_i/*
    add wave -group "IF Stage" -group "Prefetch"               $rvcores/if_stage_i/prefetch_32/prefetch_buffer_i/*
  }
  add wave -group "IF Stage"                                 $rvcores/if_stage_i/*
  add wave -group "ID Stage"                                 $rvcores/id_stage_i/*
  add wave -group "RF"                                       $rvcores/id_stage_i/registers_i/riscv_register_file_i/mem
  add wave -group "RF_FP"                                    $rvcores/id_stage_i/registers_i/riscv_register_file_i/mem_fp
  add wave -group "Decoder"                                  $rvcores/id_stage_i/decoder_i/*
  add wave -group "Controller"                               $rvcores/id_stage_i/controller_i/*
  add wave -group "Int Ctrl"                                 $rvcores/id_stage_i/int_controller_i/*
  add wave -group "Hwloop Regs"                              $rvcores/id_stage_i/hwloop_regs_i/*
  add wave -group "EX Stage" -group "ALU"                    $rvcores/ex_stage_i/alu_i/*
  add wave -group "EX Stage" -group "ALU_DIV"                $rvcores/ex_stage_i/alu_i/int_div/div_i/*
  add wave -group "EX Stage" -group "MUL"                    $rvcores/ex_stage_i/mult_i/*
  if {$fpuprivate ne ""} {
    add wave -group "EX Stage" -group "APU_DISP"             $rvcores/ex_stage_i/genblk1/apu_disp_i/*
    add wave -group "EX Stage" -group "FPU"                  $rvcores/ex_stage_i/genblk1/genblk1/fpu_i/*
  }
  add wave -group "EX Stage"                                 $rvcores/ex_stage_i/*
  add wave -group "LSU"                                      $rvcores/load_store_unit_i/*
  add wave -group "CSR"                                      $rvcores/cs_registers_i/*
}

configure wave -namecolwidth  250
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -timelineunits ns
