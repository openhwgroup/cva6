# Author:  Umberto Laghi
# Contact: umberto.laghi2@unibo.it
# Github:  @ubolakes

# commands for questa terminal
questa-cmd += -do 'project new . rv_tracer'
questa-cmd += -do 'project addfile rtl/common_cells/src/counter.sv'
questa-cmd += -do 'project addfile rtl/common_cells/src/cf_math_pkg.sv'
questa-cmd += -do 'project addfile rtl/common_cells/src/sync.sv'
questa-cmd += -do 'project addfile rtl/common_cells/src/sync_wedge.sv'
questa-cmd += -do 'project addfile rtl/common_cells/src/edge_detect.sv'
questa-cmd += -do 'project addfile rtl/tech_cells_generic/src/rtl/tc_clk.sv'
questa-cmd += -do 'project addfile rtl/tech_cells_generic/src/deprecated/pulp_clk_cells.sv'
questa-cmd += -do 'project addfile rtl/common_cells/src/lzc.sv'
questa-cmd += -do 'project addfile include/te_pkg.sv'
questa-cmd += -do 'project addfile rtl/te_branch_map.sv'
questa-cmd += -do 'project addfile rtl/te_filter.sv'
questa-cmd += -do 'project addfile rtl/te_packet_emitter.sv'
questa-cmd += -do 'project addfile rtl/te_priority.sv'
questa-cmd += -do 'project addfile rtl/te_reg.sv'
questa-cmd += -do 'project addfile rtl/te_resync_counter.sv'
questa-cmd += -do 'project addfile rtl/rv_tracer.sv'
questa-cmd += -do 'project addfile tb/tb_rv_tracer.sv'
questa-cmd += -do 'project compileall'
questa-cmd += -do 'vsim -voptargs=+acc work.tb_rv_tracer'
questa-cmd += -do 'log -r /*'
questa-cmd += -do 'run 200'

clean:
	rm -rf transcript
	rm -rf rv_tracer.mpf
	rm -rf rv_tracer.cr.mti
	rm -rf modelsim.ini
	rm -rf work
	rm -rf vsim.wlf
	rm -rf addfiles.do
	rm -rf .bender
	rm -rf Bender.lock

run:
	vlog +acc -sv pulp-platform/common_cells/src/counter.sv
	vlog +acc -sv pulp-platform/common_cells/src/sync.sv
	vlog +acc -sv pulp-platform/common_cells/src/sync_wedge.sv
	vlog +acc -sv pulp-platform/common_cells/src/edge_detect.sv
	vlog +acc -sv pulp-platform/tech_cells_generic/src/rtl/tc_clk.sv
	vlog +acc -sv pulp-platform/tech_cells_generic/src/deprecated/pulp_clk_cells.sv
	
	vlog +acc -sv pulp-platform/common_cells/src/cf_math_pkg.sv
	vlog +acc -sv include/te_pkg.sv
	vlog +acc -sv rtl/lzc.sv
	vlog +acc -sv rtl/te_branch_map.sv
	vlog +acc -sv rtl/te_filter.sv
	vlog +acc -sv rtl/te_packet_emitter.sv
	vlog +acc -sv rtl/te_priority.sv
	vlog +acc -sv rtl/te_reg.sv
	vlog +acc -sv rtl/te_resync_counter.sv
	vlog +acc -sv rtl/rv_tracer.sv
	vlog +acc -sv tb/tb_rv_tracer.sv	
	vsim -voptargs=+acc work.tb_rv_tracer
#python3 generate_do.py
#vsim -do addfiles.do
