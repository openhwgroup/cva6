# Verilated -*- Makefile -*-
# DESCRIPTION: Verilator output: Make include file with class lists
#
# This file lists generated Verilated files, for including in higher level makefiles.
# See Vcva6_core_only_tb.mk for the caller.

### Switches...
# C11 constructs required?  0/1 (always on now)
VM_C11 = 1
# Coverage output mode?  0/1 (from --coverage)
VM_COVERAGE = 0
# Parallel builds?  0/1 (from --output-split)
VM_PARALLEL_BUILDS = 1
# Threaded output mode?  0/1/N threads (from --threads)
VM_THREADS = 0
# Tracing output mode?  0/1 (from --trace/--trace-fst)
VM_TRACE = 0
# Tracing output mode in FST format?  0/1 (from --trace-fst)
VM_TRACE_FST = 0
# Tracing threaded output mode?  0/1/N threads (from --trace-thread)
VM_TRACE_THREADS = 0
# Separate FST writer thread? 0/1 (from --trace-fst with --trace-thread > 0)
VM_TRACE_FST_WRITER_THREAD = 0

### Object file lists...
# Generated module classes, fast-path, compile with highest optimization
VM_CLASSES_FAST += \
	Vcva6_core_only_tb \
	Vcva6_core_only_tb__1 \
	Vcva6_core_only_tb__2 \
	Vcva6_core_only_tb__3 \
	Vcva6_core_only_tb__4 \
	Vcva6_core_only_tb__5 \
	Vcva6_core_only_tb__6 \
	Vcva6_core_only_tb__7 \
	Vcva6_core_only_tb__8 \
	Vcva6_core_only_tb__9 \
	Vcva6_core_only_tb__10 \
	Vcva6_core_only_tb__11 \
	Vcva6_core_only_tb__12 \
	Vcva6_core_only_tb___024unit \
	Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1 \

# Generated module classes, non-fast-path, compile with low/medium optimization
VM_CLASSES_SLOW += \
	Vcva6_core_only_tb__Slow \
	Vcva6_core_only_tb__1__Slow \
	Vcva6_core_only_tb__2__Slow \
	Vcva6_core_only_tb__3__Slow \
	Vcva6_core_only_tb__4__Slow \
	Vcva6_core_only_tb__5__Slow \
	Vcva6_core_only_tb__6__Slow \
	Vcva6_core_only_tb__7__Slow \
	Vcva6_core_only_tb__8__Slow \
	Vcva6_core_only_tb__9__Slow \
	Vcva6_core_only_tb__10__Slow \
	Vcva6_core_only_tb__11__Slow \
	Vcva6_core_only_tb__12__Slow \
	Vcva6_core_only_tb___024unit__Slow \
	Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1__Slow \

# Generated support classes, fast-path, compile with highest optimization
VM_SUPPORT_FAST += \

# Generated support classes, non-fast-path, compile with low/medium optimization
VM_SUPPORT_SLOW += \
	Vcva6_core_only_tb__Syms \

# Global classes, need linked once per executable, fast-path, compile with highest optimization
VM_GLOBAL_FAST += \
	verilated \
	verilated_vpi \

# Global classes, need linked once per executable, non-fast-path, compile with low/medium optimization
VM_GLOBAL_SLOW += \


# Verilated -*- Makefile -*-
