
# XM-Sim Command File
# TOOL:	xmsim(64)	19.09-s007
#
#
# You can restore this configuration with:
#
#      xrun -l xrun-hello-world.log -64bit -R -input ../xrun/restore.tcl +UVM_VERBOSITY=UVM_LOW +=+USE_ISS -sv_lib /wrk/gtumbush/mcu/OpenHW/iss_integration_fork/cv32/sim/uvmt_cv32/../../../vendor_lib/imperas/riscv_CV32E40S_OVPsim/bin/Linux64/riscv_CV32E40S.dpi.so +elf_file=/wrk/gtumbush/mcu/OpenHW/iss_integration_fork/cv32/sim/uvmt_cv32/../../../cv32/tests/core/custom/illegal.elf +nm_file=/wrk/gtumbush/mcu/OpenHW/iss_integration_fork/cv32/sim/uvmt_cv32/../../../cv32/tests/core/custom/illegal.nm +UVM_TESTNAME=uvmt_cv32_firmware_test_c +firmware=/wrk/gtumbush/mcu/OpenHW/iss_integration_fork/cv32/sim/uvmt_cv32/../../../cv32/tests/core/custom/illegal.hex -input /wrk/gtumbush/mcu/OpenHW/iss_integration_fork/cv32/sim/xrun/restore.tcl
#

set tcl_prompt1 {puts -nonewline "xcelium> "}
set tcl_prompt2 {puts -nonewline "> "}
set vlog_format %h
set vhdl_format %v
set real_precision 6
set display_unit auto
set time_unit module
set heap_garbage_size -200
set heap_garbage_time 0
set assert_report_level note
set assert_stop_level error
set autoscope yes
set assert_1164_warnings yes
set pack_assert_off {}
set severity_pack_assert_off {note warning}
set assert_output_stop_level failed
set tcl_debug_level 0
set relax_path_name 1
set vhdl_vcdmap XX01ZX01X
set intovf_severity_level ERROR
set probe_screen_format 0
set rangecnst_severity_level ERROR
set textio_severity_level ERROR
set vital_timing_checks_on 1
set vlog_code_show_force 0
set assert_count_attempts 1
set tcl_all64 false
set tcl_runerror_exit false
set assert_report_incompletes 0
set show_force 1
set force_reset_by_reinvoke 0
set tcl_relaxed_literal 0
set probe_exclude_patterns {}
set probe_packed_limit 4k
set probe_unpacked_limit 16k
set assert_internal_msg no
set svseed 1
set assert_reporting_mode 0
alias . run
alias quit exit
stop -create -name Randomize -randomize
database -open -shm -into waves.shm waves -default
probe -create -database waves uvmt_cv32_tb.step_compare.ev_compare uvmt_cv32_tb.step_compare.ev_ovp uvmt_cv32_tb.step_compare.ev_rtl uvmt_cv32_tb.step_compare.miscompare uvmt_cv32_tb.step_compare.ret_ovp uvmt_cv32_tb.step_compare.ret_rtl uvmt_cv32_tb.step_compare.step_ovp uvmt_cv32_tb.step_compare.step_rtl uvmt_cv32_tb.step_compare.Clk uvmt_cv32_tb.step_compare_if.insn_pc uvmt_cv32_tb.step_compare_if.ovp_b1_Step uvmt_cv32_tb.step_compare_if.ovp_b1_Stepping uvmt_cv32_tb.step_compare_if.ovp_cpu_PCr uvmt_cv32_tb.step_compare_if.ovp_cpu_busWait uvmt_cv32_tb.step_compare_if.ovp_cpu_retire uvmt_cv32_tb.step_compare_if.riscv_retire uvmt_cv32_tb.clknrst_if.clk uvmt_cv32_tb.clknrst_if.clk_active uvmt_cv32_tb.clknrst_if.clk_period uvmt_cv32_tb.clknrst_if.reset_n uvmt_cv32_tb.dut_wrap.riscv_core_i.riscv_tracer_i.clk uvmt_cv32_tb.dut_wrap.riscv_core_i.riscv_tracer_i.insn_pc uvmt_cv32_tb.dut_wrap.riscv_core_i.riscv_tracer_i.retire uvmt_cv32_tb.dut_wrap.riscv_core_i.riscv_tracer_i.insn_disas uvmt_cv32_tb.dut_wrap.riscv_core_i.riscv_tracer_i.insn_regs_write uvmt_cv32_tb.dut_wrap.riscv_core_i.id_stage_i.register_file_i.clk uvmt_cv32_tb.dut_wrap.riscv_core_i.id_stage_i.register_file_i.mem uvmt_cv32_tb.iss_wrap.cpu.Retire uvmt_cv32_tb.iss_wrap.b1.Clk uvmt_cv32_tb.iss_wrap.b1.Step uvmt_cv32_tb.iss_wrap.b1.Stepping uvmt_cv32_tb.iss_wrap.cpu.PCr uvmt_cv32_tb.iss_wrap.cpu.GPR uvmt_cv32_tb.step_compare_if.ovp_cpu_GPR uvmt_cv32_tb.step_compare_if.riscy_GPR
probe -create -database waves uvmt_cv32_tb.dut_wrap.riscv_core_i.clk_i uvmt_cv32_tb.dut_wrap.riscv_core_i.clk
probe -create -database waves uvmt_cv32_tb.dut_wrap.ram_i.clk_i uvmt_cv32_tb.dut_wrap.ram_i.data_addr_i uvmt_cv32_tb.dut_wrap.ram_i.data_be_i uvmt_cv32_tb.dut_wrap.ram_i.data_gnt_o uvmt_cv32_tb.dut_wrap.ram_i.data_rdata_o uvmt_cv32_tb.dut_wrap.ram_i.data_req_i uvmt_cv32_tb.dut_wrap.ram_i.data_rvalid_o uvmt_cv32_tb.dut_wrap.ram_i.data_wdata_i uvmt_cv32_tb.dut_wrap.ram_i.data_we_i uvmt_cv32_tb.dut_wrap.ram_i.exit_valid_o uvmt_cv32_tb.dut_wrap.ram_i.exit_value_o uvmt_cv32_tb.dut_wrap.ram_i.instr_addr_i uvmt_cv32_tb.dut_wrap.ram_i.instr_gnt_o uvmt_cv32_tb.dut_wrap.ram_i.instr_rdata_o uvmt_cv32_tb.dut_wrap.ram_i.instr_req_i uvmt_cv32_tb.dut_wrap.ram_i.instr_rvalid_o uvmt_cv32_tb.dut_wrap.ram_i.irq_ack_i uvmt_cv32_tb.dut_wrap.ram_i.irq_id_i uvmt_cv32_tb.dut_wrap.ram_i.irq_id_o uvmt_cv32_tb.dut_wrap.ram_i.irq_o uvmt_cv32_tb.dut_wrap.ram_i.pc_core_id_i uvmt_cv32_tb.dut_wrap.ram_i.rst_ni uvmt_cv32_tb.dut_wrap.ram_i.tests_failed_o uvmt_cv32_tb.dut_wrap.ram_i.tests_passed_o
probe -create -database waves uvmt_cv32_tb.dut_wrap.riscv_core_i.riscv_tracer_i.cycles
probe -create -database waves uvmt_cv32_tb.iss_wrap.cpu.CSR
probe -create -database waves uvmt_cv32_tb.dut_wrap.riscv_core_i.cs_registers_i.mcause_q uvmt_cv32_tb.dut_wrap.riscv_core_i.cs_registers_i.mepc_q uvmt_cv32_tb.dut_wrap.riscv_core_i.cs_registers_i.mstatus_q uvmt_cv32_tb.dut_wrap.riscv_core_i.cs_registers_i.mtvec_q
probe -create -database waves uvmt_cv32_tb.iss_wrap.b1.DData
probe -create -database waves uvmt_cv32_tb.dut_wrap.ram_i.core_data_rdata uvmt_cv32_tb.dut_wrap.ram_i.ram_data_rdata uvmt_cv32_tb.dut_wrap.ram_i.rnd_stall_data_rdata
probe -create -database waves uvmt_cv32_tb.dut_wrap.ram_i.data_random_stalls.data_process.mem_acc
probe -create -database waves uvmt_cv32_tb.dut_wrap.riscv_core_i.id_stage_i.decoder_i.csr_illegal uvmt_cv32_tb.dut_wrap.riscv_core_i.id_stage_i.decoder_i.illegal_insn_o uvmt_cv32_tb.dut_wrap.riscv_core_i.id_stage_i.decoder_i.illegal_c_insn_i
probe -create -database waves uvmt_cv32_tb.dut_wrap.riscv_core_i.id_stage_i.decoder_i.instr_rdata_i
probe -create -database waves uvmt_cv32_tb.iss_wrap.b1.DAddr uvmt_cv32_tb.iss_wrap.b1.DSize uvmt_cv32_tb.iss_wrap.b1.Dbe uvmt_cv32_tb.iss_wrap.b1.Drd uvmt_cv32_tb.iss_wrap.b1.Dwr uvmt_cv32_tb.iss_wrap.b1.IAddr uvmt_cv32_tb.iss_wrap.b1.IData uvmt_cv32_tb.iss_wrap.b1.ISize uvmt_cv32_tb.iss_wrap.b1.Ibe uvmt_cv32_tb.iss_wrap.b1.Ird

simvision -input ../xrun/restore.tcl.svcf
