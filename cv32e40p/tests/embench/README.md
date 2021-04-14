# EMBench for Core-V-Verif

[EMBench](https://github.com/embench/embench-iot) has been integrated into Core-V-Verif to allow easy benchmarking of the RISC-V cores supported by 
Core-V-Verif. This document explains the usage and implementation of the EMBench scripts and their integration
into the makefile environment of Core-V-Verif.<br><br>


## Quick start guide

For a core that already has the supporting configuration files, running the EMBench Benchmarks can be achieved
in the following manner:<br>
from path:
>/core-v-verif/\[core\]/sim/uvmt

run the following shell command:
>% make embench SIMULATOR=\[available simulator\]

This will run the EMBench default benchmark \(speed\) on the core in the path, with the simulator given in the options.
**Note** that runtime here can be several hours. If you are uncertain if the simulations are running as they
should, the tests can be run outside of the benchmarking script, see [this](#simulate-an-embench-test-outside-of-the-script) section for details.

If you want to set a target score for you benchmark, you can set the option EMB_TARGET, like this:
>% make embench SIMULATOR=\[sim\] EMB_TARGET=\[float\]

The EMBench script will determine if the target has been met, for either a speed or size benchmark, and report 
the result.

To run a size benchmark, set the EMB_TYPE option to *size*:
>% make embench EMB_TYPE=size

**Note** that SIMULATOR is not set when running size, as no simulation is necessary. Also note that when building the tests for the size benchmark, they are built without support files and libraries to match EMBench baseline, so any simulation with these files will fail. <br><br>

 
## Relevant files and directories

- **core-v-verif/bin/run_embench.py**<br>
Main script that builds, runs and evaluates EMBench Benchmarks on the selected core.

- **/core-v-verif/\[core\]/tests/embench/config/**<br>
Core specific configuration required by EMBench

- **/core-v-verif/\[core\]/tests/embench/pylib/run_corev32.py**<br>
Core specific python module required by EMBench

- **/core-v-verif/\[core\]/tests/programs/embench/**<br>
Test directory that is populated by the EMBench script with files necessary to run the EMBench tests
with the *make test ..* method.

- **/core-v-verif/\[core\]/vendor_lib/embench/**<br>
Directory where the EMBench repo is cloned when the script runs<br><br>

## Script options from make environment
The following table lists the available options, their default values and their function. 
**Note** that only options unique to the EMBench scripts are included here, other dependencies, like the 
SIMULATOR option, are omitted.

| Option         | Default    | Description                                                                                                                            |
|----------------|------------|----------------------------------------------------------------------------------------------------------------------------------------|
| EMB_TYPE       | speed      | What benchmark to run. Valid options: speed, size<br>NOTE: type affects build configuration!                                           |
| EMB_BUILD_ONLY | NO         | Set this option to "YES" to only build the benchmarks                                                                                  |
| EMB_TARGET     | 0(not set) | Set a target(float) for your EMBench score<br>Benchmark run will fail if target is not met<br>If no target is set, no checking is done |
| EMB_CPU_MHZ    | 1          | Set the core frequency in MHz \*                                                                                                       |
| EMB_DEBUG      | NO         | Set this option to "YES" to increase verbosity of the script                                                                           |

<br>
* This value is used for calculation in EMBench only. Measurement is done by cycle count, so this does not 
have to match simulation, but can be used to predict results for a system running the core at a 
specific frequency.<br><br>

## Simulate an EMBench test outside of the scripted environment
As the EMBench integration utilizes the *make test* calls already present in Core-V-Verif, the tests can be
simulated separately from the benchmark environment. To accomplish this, complete the following steps:

1. Run the EMBench script with the "EMB_BUILD_ONLY=YES" option. Type must be *speed*, but can be left out as this is the default.
   >% make embench EMB_BUILD_ONLY=YES
2. Run *make test* in the following manner:
   >% make test TEST=emb_\[testname\] SIMULATOR=\[sim\] USE_ISS=NO

This will simulate as any other test. Note that step 1 can be omitted if there has been a previously run 
speed benchmark, and the repository has not been cleaned. At the time of writing, ISS must be disabled
as the accesses to the cycle counter in the mm_ram causes step and compare mismatches. Simulating with ISS 
will also cause a significant increase in runtime.<br><br>

## Extend EMBench integration to a new core
As new core designs are added to Core-V-Verif, we will want to run the Benchmarks on these. This section 
describes the necessary steps to accomplish this. *Note* that this description only includes EMBench 
unique files, dependencies in the core specific makefiles also exist.

Copy the embench configuration directory from cv32e40p to the new core:
>/core-v-verif/\[core\]/tests/embench

Copy the embench makefile defines(EMBENCH_*) from cv32e40p to the new core:
>/core-v-verif/\[core\]/sim/Common.mk

Copy over the embench directory under *programs*. This should be empty except for a readme file.
>/core-v-verif/\[core\]/tests/programs/embench


Make the following changes to the .gitignore files listed:<br>
| File                                         | Add line |
|----------------------------------------------|----------|
| /core-v-verif/\[core\]/tests/.gitignore      | emb_*/   |
| /core-v-verif/\[core\]/vendor_lib/.gitignore | embench/ |



<br>If there are no differences in configuration necessary compared to the cv32e40p, you are now done, 
run the EMBench scripts in the manner described above. However, if there are notable differences, 
a quick description on what to check follows. For full details, please check the EMBench [documentation](https://github.com/embench/embench-iot/blob/master/doc/README.md).<br>

For compiler flags, linker flags or library dependencies, check the follwing files:
>/core-v-verif/\[core\]/tests/embench/config/corev32/chips/size/chip.cfg<br>
>/core-v-verif/\[core\]/tests/embench/config/corev32/chips/speed/chip.cfg

For changes to how the test files communicates with the testbench:
>/core-v-verif/\[core\]/tests/embench/config/corev32/chips/\[type\]/chipsupport.c<br>
>/core-v-verif/\[core\]/tests/embench/config/corev32/chips/\[type\]/chipsupport.h

If the new core has specific requirements to it's *make test* call, check this file:
>/core-v-verif/\[core\]/tests/embench/pylib/run_corev32.py