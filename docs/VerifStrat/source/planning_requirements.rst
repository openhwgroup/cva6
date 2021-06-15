..
   Copyright (c) 2020 OpenHW Group
   
   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at
  
   https://solderpad.org/licenses/
  
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
  
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


.. _planning_requirements:

Verification Planning and Requirements
======================================

A key activity of any verification effort is to capture a Verification
Plan (aka Test Plan or just testplan). This document is not that. The
purpose of a verification plan is to identify what features need to be
verified; the success criteria of the feature and the coverage metrics
for testing the feature. At the time of this writing the verification
plan for the CV32E40P is under active development. It is located in the
core-v-verif GitHub repository at
https://github.com/openhwgroup/core-v-docs/tree/master/verif/CV32E40P/VerificationPlan.

The Verification Strategy (this document) exists to support the
Verification Plan. A trivial example illustrates this point: the
CV32E40P verification plan requires that all RV32I instructions be
generated and their results checked. Obviously, the testbench needs to
have these capabilities and its the purpose of the Verification Strategy
document to explain how that is done. Further, an AC will be required to
implement the testbench code that supports generation of RV32I
instructions and checking of results, and this document defines how
testbench and testcase development is done for the OpenHW projects.

The subsections below summarize the specific features of the CV32E40\*
verification environment as identified in the Verification Plan. It will
be updated as the verification plan is completed.

Base Instruction Set
--------------------

1. Capability to generate all legal RV32I instructions using all
   operands.
2. Ability to check status of GPRs after instruction execution.
3. Ability to check side-effects, most notably underflow/overflow after
   instruction execution.

Privileged Spec
---------------
ToDo

XPULP Instruction Extensions
----------------------------
ToDo

Custom Circuitry
----------------
ToDo

Interrupts
----------
ToDo

Debug
-----
ToDo

RVI-Compliant Interface
-----------------------
ToDo
