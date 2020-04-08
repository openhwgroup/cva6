 
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


FILE:Imperas/Examples/SystemVerilog/Setup_and_Checks/README.txt

DESCRIPTION -------------------------------------------------------

This directory contains the variable definitions specific to the 
HDL simulators supported by these examples

Cadence Incisive : defines.INCISIVE.Makefile.include 
Mentor  Questa   : defines.QUESTA.Makefile.include
Mentor  VCS      : defines.VCS.Makefile.include
Metrics DSim     : defines.DSIM.Makefile.include

These are used in the example directories by the Makefiles and set
environment variables up to run the shell script examples.

You will need to ensure that you have an installation of an HDL
simulator that is running. Typically you will need to set up
environment variables such as:
    some form of hdlsim_HOME
    PATH - adding in your installation directory in the search path
    and often an LM_LICENSE_FILE if your simulator uses FLEXlm
    
The script checkEnvironment.sh can be executed and will check that
you have setup an expected environment.

ENVIRONMENT -------------------------------------------------------

  General
    TARGET : selects the HDL simulator
        set to INCISIVE, QUESTA, VCS, DSIM, etc.

  Imperas
    A valid Imperas installation environment must be setup. 
    Use <Imperas install root>/bin/setup.sh

  Verilog Simulators - please look in the include files
    defines.TARGETS.include  lists the supported simulators
    
#
