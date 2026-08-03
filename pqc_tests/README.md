# Simulation Tests

This directory contains test scripts for simulation and profiling.

## Testing Scripts

The shell scripts found in the directory can be used to run test automatically, with a few different options.

To run a script, simply:
```sh
bash ./pqc_tests/<TEST-NAME>.sh
```

Executed file will run the chosen test and will copy it's log files into this directory with the filenames being `<TEST-NAME>.log` etc. There are a few different options to configure the test. You can edit corresponding fields to modify the test configs inside scripts.

You can set the desired target core configuration: (Example: cv32a6_ima_sv32 or cv64a6_imafdc_sv39)
```sh
export DV_TARGET=<TARGET-CORE>
```

The desired simulators can be set:
```sh
export DV_SIMULATORS=veri-testharness,spike
```

It is possible to set the number of jobs to make the simulation faster:
```sh
export NUM_JOBS=8
```

Set `PRINT_CYCLES` to 1 if you want to print clock cycles (through UART). This will create mismatches between spike and verilator logs. After obtaining mismatched results, you might want to clear the logs in the simulation directory so the regression log doesn't print fail messages every time you run a simulation.
```sh
PRINT_CYCLES=1
```
Set `PROFILE` to 1 if you want a detailed report on call counts and ratios. This script will run `profile_csv.py` and read the csv files to produce the report. A verilator only simulation does not generate the csv files, so you need to run spike aswell.
```sh
PROFILE=1
```
Setting `LOG_ALU` to 1 will generate a `<TEST_NAME>_alu_cycle_trace.log` file that shows the values of ALU operands and results in the Execute stage, alongside the clock cycle and the program counter values (for Verilator simulation).
```sh
LOG_ALU=1
```

Finally, there are some additional options for different test, mainly different parameters for the pqc algorithms, which you might want to check out. Resulting log files might be too large, so the testing script might only copy the iss log into this directory.

### TODO
Add Falcon and SPHINCS+.