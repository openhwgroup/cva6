## Experimental Stand-alone testbench for the CVA6
This do-nothing TB supports experiments with the CVA6 to develop a standalone testbenech for the CVA6.
It uses a "core-only" manifest file `Flist.cva6`.

### Current status:
Compiles and runs without errors for a few thousand clock cycles under Metrics DSIM.
Currently working on Verilator version (and then Cadence Xcelium).

### To run it:
- set shell environment variable CVA6_RTL_DIR to point to the top of the clone of this repo.
- set shell environment variable CVA6_TB_DIR to point to this directory.
- make (default target is `veri_run`, which compiles and runs under Verilator)
<br>
Example:

```
$ export CVA6_RTL_DIR=/wrk/cva6
$ export CVA6_TB_DIR=/wrk/cva6/cva6_tb
$ make help
$ make veri_run
```
