## corev-dv
This directory contains core-v-verif extensions to [riscv-dv](https://github.com/google/riscv-dv).   The cloned code from Google is not locally
modified, and as much as is possible we attempt to use the latest-and-greatest from Google.  Any core-v-verif
specializations are implemented as either replacements (e.g the manifest) or extensions of specific SV classes.
<br><br>
Compile logs, runtime logs and the generated programs are placed here in the same `out_<YYYY_MM_DD>` directory used by riscv-dv.
<br>
TODO: re-direct the generated assembly language tests-programs to a central location.
<br><br>
The UVM environments in core-v-verif do not use the `run.py` python script to run the generator (although no changes are
made preventing _you_ from doing so).  Check out the appropriate Makefile(s) (e.g. `$PROJ_ROOT/cv32/sim/uvmt_cv32/Makefile`)
for an exmaple of how core-v-verif runs the generator.
