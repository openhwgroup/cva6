..
   Copyright 2022 Thales DIS design services SAS
   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales



Subsystem
=========

Global functionality
--------------------

The CVA6 is a subsystem composed of the modules and protocol interfaces as illustrated 
The processor is a Harvard-based modern architecture.
Instructions are issued in-order through the DECODE stage and executed out-of-order but committed in-order.
The processor is Single issue, that means that at maximum one instruction per cycle can be issued to the EXECUTE stage.

The CVA6 implements a 6-stage pipeline composed of PC Generation, Instruction Fetch, Instruction Decode, Issue stage, Execute stage and Commit stage.
At least 6 cycles are needed to execute one instruction.

Connection with other sub-systems
---------------------------------

The submodule is connected to :

* NOC interconnect provides memory content
* COPROCESSOR connects through CV-X-IF coprocessor interface protocol
* TRACER provides support for verification
* TRAP provides traps inputs


Parameter configuration
-----------------------


.. include:: parameters_cv32a65x.rst



IO ports
--------

.. include:: port_cva6.rst
