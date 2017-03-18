library = work

top_level = alu

src = include/ariane_pkg.svh alu.sv

incdir = ../../../rtl/includes

questa_version = -10.5c

build:
	rm -rf ${library}
	vlog${questa_version} -incr ${src} ${list_incdir}
	vopt${questa_version} ${top_level} -o ${top_level}_optimized +acc -check_synthesis

.PHONY:
	build
