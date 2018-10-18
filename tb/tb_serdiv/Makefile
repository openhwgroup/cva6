library      ?= work
toplevel     ?= tb
src-list     := tb.list
inc-path     := $(shell pwd)/hdl/
src          := $(shell xargs printf '\n%s' < $(src-list)  | cut -b 1-)
compile_flag += +cover+i_dut -incr -64 -nologo 
sim_opts     += -64 -coverage -classdebug -voptargs="+acc"
questa_version ?= ${QUESTASIM_VERSION}


build: clean
	vlib${questa_version} $(library)
	vlog${questa_version} -work $(library) -pedanticerrors $(src) $(compile_flag) +incdir+$(inc-path)
	touch $(library)/.build

sim: build
	vsim${questa_version} -lib $(library) $(toplevel) -do "do wave.do" $(sim_opts)

simc: build
	vsim${questa_version} -lib $(library) $(toplevel) -c -do "run -all; exit" $(sim_opts)

	
clean:
	rm -rf $(library)

.PHONY: clean simc sim build

