# CVA6 cycle-accurate performance model

This repository contains a cycle-accurate performance model of CVA6 control-path.

It was developed to explore microarchitecture changes in CVA6 before implementing them.

To cite this model, please head to the end of this document.


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


## Citing

```bibtex
@inproceedings{cf24,
   author = {Allart, C\^{o}me and Coulon, Jean-Roch and Sintzoff, Andr\'{e} and Potin, Olivier and Rigaud, Jean-Baptiste},
   title = {Using a Performance Model to Implement a Superscalar CVA6},
   year = {2024},
   isbn = {9798400704925},
   publisher = {Association for Computing Machinery},
   url = {https://doi.org/10.1145/3637543.3652871},
   doi = {10.1145/3637543.3652871},
   abstract = {A performance model of CVA6 RISC-V processor is built to evaluate performance-related modifications before implementing them in RTL. Its accuracy is 99.2\% on CoreMark. This model is used to evaluate a superscalar feature for CVA6. During design phase, the model helped detecting and fixing performance bugs. The superscalar feature resulted in a CVA6 performance improvement of 40\% on CoreMark.},
   booktitle = {Proceedings of the 21st ACM International Conference on Computing Frontiers: Workshops and Special Sessions},
   pages = {43–46},
   numpages = {4},
   keywords = {CVA6, Cycle-Based Model, Multi-Issue, Performance, RISC-V, Superscalar},
   location = {Ischia, Italy},
   series = {CF '24 Companion}
}
```
