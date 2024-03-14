..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_ISSUE_STAGE:

ISSUE_STAGE Module
==================

Description
-----------

The execution can be roughly divided into four parts: issue(1), read operands(2), execute(3) and write-back(4).
The ISSUE_STAGE module handles step one, two and four.
The ISSUE_STAGE module receives the decoded instructions and issues them to the various functional units.

A data structure called scoreboard is used to keep track of data related to the issue instruction: which functional unit and which destination register they are.
The scoreboard handle the write-back data received from the COMMIT_STAGE module.

Furthermore it contains the CPU’s register file.


The module is connected to:

* TO BE COMPLETED

.. include:: port_issue_stage.rst

Functionality
-------------

TO BE COMPLETED


Submodules
----------

.. figure:: ../images/issue_stage_modules.png
   :name: ISSUE_STAGE submodules
   :align: center
   :alt:

   ISSUE_STAGE submodules

Scoreboard
~~~~~~~~~~

The scoreboard contains a FIFO to store the decoded instructions.
Issued instruction is pushed to the FIFO if it is not full.
It indicates which registers are going to be clobbered by a previously issued instruction.

.. include:: port_scoreboard.rst

Issue_read_operands
~~~~~~~~~~~~~~~~~~~

TO BE COMPLETED

.. include:: port_issue_read_operands.rst
