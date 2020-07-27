# questa library
library        ?= work
# Top level module to compile
top_level      ?= pmp_tb
# QuestaSim Version
questa_version ?= # -10.7b

compile_flags = +cover -incr -64 -permissive
sim_flags = -t 1ps -debugdb -voptargs="+acc" -do "run -all; quit" 

src = $(wildcard src/*.sv)
inc = $(wildcard include/*.sv)
tb = $(wildcard tb/*.sv)

compile-sim:
	rm -rf ${library}
	vlog${questa_version} -work ${library} ${compile_flags} ${inc}
	vlog${questa_version} -work ${library} ${compile_flags} ${src}
	vlog${questa_version} -work ${library} ${compile_flags} ${tb}

sim: compile-sim
	vsim${questa_version} -c -work ${library} ${sim_flags} ${top_level}

sim-gui:
	rm -rf ${library}
	vlog${questa_version} -work ${library} ${compile_flags} ${src}
	vlog${questa_version} -work ${library} ${compile_flags} ${tb}
	vsim${questa_version} -work ${library} ${sim_flags} ${top_level}

clean:
	@rm -rf ${library} transcript vsim.dbg vsim.wlf