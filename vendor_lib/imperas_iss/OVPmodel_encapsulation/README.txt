 
  Copyright (c) 2005-2020 Imperas Software Ltd. All Rights Reserved.

  The contents of this file are provided under the Software License
  Agreement that you accepted before downloading this file.

  This source forms part of the Software and can be used for educational,
  training, and demonstration purposes but cannot be used for derivative
  works except in cases where the derivative works require OVP technology
  to run.

  For open source models released under licenses that you can use for
  derivative works, please visit www.ovpworld.org or www.imperas.com
  for the location of the open source models.


FILE:Imperas/Examples/SystemVerilog/OVPmodel_encapsulation/README.txt

INTRODUCTION -------------------------------------------------------
This example shows the use an OVP Fast Processor Model object being 
linked to a SystemVerilog simulator using DPI and encapsulated in a
SystemVerilog module enabling it to run in a SystemVerilog testbench.

DIRECTORIES -------------------------------------------------------
C_OVPmodel
----------
In this directory is the 'wrapper' written in C that uses the 
OVP OP API to instance a RISC-V processor and provide interface to the
SystemVerilog DPI. This is compiled to a shared object that is loaded
into the SystemVerilog simulator.

verilog_OVPmodel
----------------
The file cpu.sv defines the module that makes use of the C_OVPmodel 
object and provides the SystemVerilog access to its capabilities.
monitor.sv contains helper functions and interface.sv includes the 
SystemVerilog interface definition.

verilog_model
-------------
This directory includes modules used in the testbench such as memory.

verilog_testbench
-----------------
dut.sv
    includes the module that instances the memory, monitor
    components and the module containing the encapsulated OVP processor model.
    It also includes simple clocking.
testbench.sv
    instances the dut module and provides optional simple 
    functional coverage.
class_simple_coverage.svh
    contains a class to create very simple instruction
    existence functional coverage. It is enabled with compile and runtime 
    plusargs options.

application
-----------
Provides the C source for the examples such as dhrystone, fibonacci 
and one example of a generated test from the riscv-dv instruction stream 
generator.
There is also pre-compiled compliance suite test.

RUNNING THE SIMULATION EXAMPLES --------------------------------------

> RUN_hello.sh

> RUN_dhrystone.sh

> RUN_google_dv.sh
    Note it shows some of simulators instruction trace capability on
        one of the Google riscv-dv generated random tests.

> RUN_compliance.sh
    One of the risc-v compliance suite tests
    Note the run generates a signature file and verifies this is correct
        by comparing to the reference copied from the compliance suite.

> RUN_dv_coverage.sh
    Runs Dhrystone example with simple instruction functional coverage.
    This functional coverage is just a very simple example.
    See the output log file for your SystemVerilog simulator for results.