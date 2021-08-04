Simulation Makefile Directory for CV32E40P UVM Verification Environment
==================================
This is the directory in which you should run all tests of the UVM environment.<br>
All results (compile logs, waveforms, run logs, simulation databases, etc.) will be placed in this directory under $(SIMULATOR)_results<br>


_For directory indepedent execution, please see the makeuvmt utility in the [bin](../../../bin) directory_<br>
_For instructions on invoking and controlling the _uvmt_ testbench, see the [README in the mk/uvmt directory](../../../mk/uvmt)_<br>


Demonstration and development branch for the OBI MEMORY AGENT
==================================
Define macro `USE_OBI_MEM_AGENT` at compile time to use the new OBI MEMORY AGENT.
This macro will be deprecated as soon as the integration of the OBI memory agent into the CV32E40P environment is complete.
The examples below work for DSIM:
```
$ make test TEST=csr_instr_asm WAVES=1 DSIM_DMP_FILE=dsim.fst DSIM_USER_COMPILE_ARGS=+define+USE_OBI_MEM_AGENT
$ make corev-dv
$ make gen_corev-dv test TEST=corev_rand_jump_stress_test
$ make gen_corev-dv test TEST=corev_rand_arithmetic_base_test
```
It is expected that all test-programs that do _not_ attempt non-32-bit aligned loads/stores will pass.
This precludes most preexisting tests, including hello-world:
```
$ make sanity DSIM_USER_COMPILE_ARGS=+define+USE_OBI_MEM_AGENT
```

