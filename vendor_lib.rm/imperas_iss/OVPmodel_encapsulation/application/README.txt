 
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


FILE:Imperas/Examples/SystemVerilog/application/README.txt

INTRODUCTION -------------------------------------------------------

This directory contains a number of directories containing applications
that can be executed by the SystemVerilog examples.

support
  Support routines
  start.S     : Creates code for reset and exception vectors. 
                Defines symbols used for character output to stdout.
  support.c/h : Defines some utility functions for enabling interrupts 
                and vector instructions and writing to stdout.

C_applications
  Simple example applications such as Dhrystone and Fibonacci

compliance
  A test taken from the compliance test suite. These are pre-compiled.
  Also includes reference files to check the signature output

google
  A test taken from the google UVM generated tests.

#
