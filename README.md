# CVA6 cycle-accurate performance model

This repository contains a cycle-accurate performance model of CVA6 control-path.

It was developed to explore microarchitecture changes in CVA6 before implementing them.


## Getting started

### Adapt RVFI trace generation

The regular expression expects the cycle number to be in the RVFI trace.
The value is not used by the model but it is used to compare the model and CVA6.

To emit cycle number in RVFI trace, modify `corev_apu/tb/rvfi_tracer.sv` in CVA6 repository as below.

```diff
-        $fwrite(f, "core   0: 0x%h (0x%h) DASM(%h)\n",
-          pc64, rvfi_i[i].insn, rvfi_i[i].insn);
+        $fwrite(f, "core   0: 0x%h (0x%h) @%d DASM(%h)\n",
+          pc64, rvfi_i[i].insn, cycles, rvfi_i[i].insn);
```


### Generate an RVFI trace

To generate an RVFI trace, follow the instructions in the CVA6 repository to run a simulation.
The RVFI trace will be in `verif/sim/out_<date>/<simulator>/<test-name>.log`.


### Running the model

```bash
python3 model.py verif/sim/out_<date>/<simulator>/<test-name>.log
```


### Exploring design space

In `model.py`, the `main` function runs the model with arguments which override default values.
Generic parameters are available in `Model.__init__`.
You can add new parameters to explore here.

To perform exploration, run the model in a loop, like `issue_commit_graph` does.
The `display_scores` function is meant to print a 3D plot if you have `matplotlib`.
`issue_commit_graph` prints the scores so that you can store it and display the figure without re-running the model.


## Files

| Name            | Description                                              |
| :---            | :---                                                     |
| `cycle_diff.py` | Calculates duration of each instruction in an RVFI trace |
| `isa.py`        | Module to create Python objects from RISC-V instructions |
| `model.py`      | The CVA6 performance model                               |
