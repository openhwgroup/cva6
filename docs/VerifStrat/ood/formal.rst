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


CORE-V Formal Verification
==========================

Formal verification of the CV32E and CVA6 cores is a joint effort of
the OpenHW Group and OneSpin Solutions with the support of multiple
Active Contributors (AC) from other OpenHW Group member companies. This
section specifies the goals, work items, workflow and expected outcomes
of CV32E and CVA6 formal verification.

Goals
-----

Completeness of formal verification is measured in a way similar to
simulation verification. That is, a Verification Plan (Testplan) will be
captured that specifies all features of the cores, and assertions will
be either automatically generated or manually written to cover all items
of the plan. Formal verification is said to be complete when proofs for
all assertions have been run and passed. Code coverage and/or
cone-of-influence coverage will be reviewed to ensure that all logic is
properly covered by at least one assertion in the formal testbench.

Note that proofs may be either bounded or unbounded. Where it is not
practical to achieve an unbounded proof a human analysis is performed to
determine the minimum proof depth required to sign off the assertion in
question. For these bounded proofs, the assertion is considered covered
when the required proof depth has been achieved without detecting a
counterexample (failure).

Formal CORE-V ISA Specifications
--------------------------------

It is believed that the RISC-V Foundation has plans to create formal,
machine readable, versions of the RISC-V ISA and that the implementation
language for this machine readable ISA is
`Sail <https://www.cl.cam.ac.uk/~pes20/sail/>`__. Once complete and
ratified, the formal model(s) will be *the* ISA and the human language
versions of the ISA will be demoted to reference documents. ToDo: find a
reference to confirm this.

Sail is a product of the
`REMS <https://www.cl.cam.ac.uk/~pes20/rems/index.html>`__ group, an
academic group in the UK, which has also created partial Sail models of
the RV32IMAC and RV64IMAC ISAs. These model are maintained in GitHub at
https://github.com/rems-project/sail-riscv and the project is in active
development.

Use of Sail Models in CORE-V Verification
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Three considerations are driving the OpenHW Group’s interest in formal
ISA (Sail) models:

-  Assuming the RISC-V Foundation develops and supports complete ISA
   specification in Sail, the RISC-V community may expect the same of
   OpenHW. Developing, maintaining and supporting formal specifications
   of the CORE-V ISAs will lend credibility to the CORE-V family.
-  A formal model of the ISA supports the creation of a tool-flow that
   can produce “correct-by-construction” software emulators, compilers,
   compliance tests and reference models. This capability will generate
   interest in CORE-V IP from both Industry and Academia.
-  The primary interest in Sail is the\ ** possibility of using a Sail
   model as a reference model for the formal testbench assertions.** The
   assertions will verify that a certain micro-architecture implements
   the ISA from the Sail spec. Essentially, the assertions together with
   the OneSpin GapFree technology perform an equivalence check between
   Sail model and the RTL to ensure that:

   -  everything behaves according to the ISA (Sail model),
   -  nothing on top of what is specified in the ISA (Sail model) is
      implemented in the RTL.

OneSpin is currently investigating how to best make use of the Sail
model. This will be captured in a future release of this document.

Development of Sail Models for CORE-V Cores
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

At the time of this writing [17]_, the completeness of the RV32/64IMAC
Sail models is not known, but is believed to be complete. Extensions of
the models will be required to support Zifencei, Zicsr, Counters and the
XPULP extensions. OpenHW may also wish to include User Mode and PMP
support as well, especially for the CVA6. Its a given that much or all
of the work to create these extensions to the Sail models will need to
be done by the OpenHW Group.

Given that CV32E and CVA6 projects are leveraging pre-existing
specifications and models, it should be possible for the
micro-architecture and Sail models to be developed in parallel and by
different ACs.

Work Items
----------

This sub-section details a set of work items (or deliverables) to be
produced by either the OpenHW Group and/or OneSpin Solutions. Note that
deliverables assigned to OpenHW may be produced solely or jointly by an
employee or contractor of the OpenHW Group, or by an Active Contributor
(AC) provided by another member company.

Table 2: CV32E40P Formal Verification Work Items

+-----+---------------------------------------------------------------------------------+---------------------+-----------------------------------------------------------------------------------------------------------------------------------------------+
| #   | Work Items                                                                      | Provided By         | Comment                                                                                                                                       |
+=====+=================================================================================+=====================+===============================================================================================================================================+
| 1   | CV32E40P User Manual                                                            | OpenHW Group        | Viewable at readthedocs: https://core-v-docs-verif-strat.readthedocs.io/projects/cv32e40p_um/en/latest/                                       |
+-----+---------------------------------------------------------------------------------+---------------------+-----------------------------------------------------------------------------------------------------------------------------------------------+
| 2   | ISA Sail Models                                                                 | OpenHW Group        | Based on the RV64IMAC Sail model developed by the RISC-V Foundation.                                                                          |
|     |                                                                                 |                     | Status information as of 2020-04-20 at https://github.com/rems-project/sail-riscv/blob/master/doc/Status.md                                   |
+-----+---------------------------------------------------------------------------------+---------------------+-----------------------------------------------------------------------------------------------------------------------------------------------+
| 3   | Define the use of Sail ISA specification/model in a formal verification flow.   | OneSpin Solutions   | OneSpin is currently investigating how to best make use of the Sail model. See Section `7.2 <#anchor-14>`__ for a discussion of this topic.   |
+-----+---------------------------------------------------------------------------------+---------------------+-----------------------------------------------------------------------------------------------------------------------------------------------+
| 4   | Compute Infrastructure                                                          | OpenHW Group        | OpenHW will create one or more VMs on the IBM Cloud to support formal verification of both Cores.                                             |
+-----+---------------------------------------------------------------------------------+---------------------+-----------------------------------------------------------------------------------------------------------------------------------------------+
| 5   | Tool Licenses                                                                   | OneSpin Solutions   | OneSpin provides tool licenses in sufficient numbers to allow for "reasonable" regression turn-around time.                                   |
+-----+---------------------------------------------------------------------------------+---------------------+-----------------------------------------------------------------------------------------------------------------------------------------------+
| 6   | Formal Testplan                                                                 | OpenHW Group and    | ToDo: work with OneSpin to define template.                                                                                                   |
|     |                                                                                 | OneSpin Solutions   |                                                                                                                                               |
+-----+---------------------------------------------------------------------------------+---------------------+-----------------------------------------------------------------------------------------------------------------------------------------------+
| 7   | Delivery of Open Source assertion model to support Formal Testplan              | OneSpin Solutions   |                                                                                                                                               |
+-----+---------------------------------------------------------------------------------+---------------------+-----------------------------------------------------------------------------------------------------------------------------------------------+
| 8   | Formal Verification of Cores                                                    | OpenHW Group and    | See the sub-section `7.4 <#anchor-16>`__.                                                                                                     |
|     |                                                                                 | OneSpin Solutions   |                                                                                                                                               |
+-----+---------------------------------------------------------------------------------+---------------------+-----------------------------------------------------------------------------------------------------------------------------------------------+

Specifications
~~~~~~~~~~~~~~

See rows #1 and #2 in , above. The first step of the process is for the
OpenHW Group to develop and deliver:

-  **Micro-architecture specifications** for both cores. This activity
   has started and is proceeding under the direction of Davide
   Schiavone, Director of Engineering for the Cores Task Group.
-  **Sail models** of each core’s ISA. This activity will be managed by
   the Verification Task Group. The expectation is that this
   pre-existing Sail model can be extended for both the CV32E and CVA6
   cores, including the PULP ISA extensions.

Compute and Tool Resources
~~~~~~~~~~~~~~~~~~~~~~~~~~

This is rows #4 and #5 in , above. Tool licenses in sufficient numbers
to allow for "reasonable" regression turn-around time on CVA6 RTL.
These tools will be installed on VMs on the IBM Cloud and will only be
accessible by employees/contractors of the OpenHW Group or select ACs
actively involved in formal verification work.

Formal Testplans
~~~~~~~~~~~~~~~~

OpenHW and OneSpin will jointly develop Formal Testplans for both the
CV32E and CVA6. The high-level goals of the FTBs will be two-fold:

1. Prove that the core designs conform to the RISC-V+Pulp-extended ISA.
   Specifically, every instruction must:

-  

   -  decode properly
   -  perform the correct function
   -  complete as specified (location of results, condition flag
      settings, etc.)

In particular, the above must be true in the presence or absence of
exceptions, interrupts or debug commands.

2. Prove the logical correctness of the implementation with respect to
   the micro-architecture (note that not all of these features are
   support by every CORE-V core):

-  

   -  Interface logic
   -  Pipeline hazards
   -  Exception handling
   -  Interrupt handling
   -  Debug support
   -  Out of order execution
   -  Speculative execution
   -  Memory management

Formal Testbenches
~~~~~~~~~~~~~~~~~~

Conceptually, a formal testbench is a collection of assumptions,
assertions and cover statements. The assumptions provide the necessary
scaffolding logic in order to support the operation of the formal
engines. Examples of these include the identification of clocks, and
resets, constraints on clock and reset cycle timing and input
wire-protocol constraints. Most assertions in the formal testbench exist
to prove one or more items in the Testplan. Covers exist to prove that a
specific function has, in fact, been tested. The formal testbench coding
is considered complete when all assumptions, assertions and covers are
coded.

OneSpin will initiate development of Formal testbenches (FTB) for CV32E
and CVA6 as soon as possible. These FTBs will be open-source, ideally
implemented in SystemVerilog, and may be based on OneSpin’s RISC-V
Verification App [18]_.

It is not expected that OneSpin will deliver a complete formal
testbench. Rather, OneSpin will deliver a formal testbench that has two
specific attributes:

1. Assertions to prove that the core implementation (RTL model) conforms
   to the RISC-V+Pulp-extended ISA. The ISA used for this will be the
   Sail model (see Section X).
2. Sufficient assumptions, assertions and covers such that ACs from
   other OpenHW member companies are able to read the Testplan and add
   the required assumptions, assertions and covers to move the project
   towards completion.

Formal Verification Workflow
----------------------------

ToDo: add a figure here to illustrate the workflow

The workflow for CORE-V formal verification will be similar to that used
by simulation verification. The three key elements of the workflow are:

-  A **GitHub** centralized repository.
-  **Distributing** the work across multiple teams in multiple
   organizations;
-  **Continuous Integration.** Once the compute environment on the IBM
   Cloud is established and OneSpin tools deployed, OneSpin will assist
   OpenHW to generate script-ware to support automated checks whenever a
   new branch or update is pushed to the central repository. Such check
   can pinpoint relatively simple errors without running a lot of
   verification. OpenHW would then maintain these scripts. In addition,
   there will be scripts for more comprehensive/full regression runs
   that OpenHW should maintain after initial delivery (if the file list
   for compilation changes due to RTL re-organization, for example, this
   needs adaption in the respective compile scripts).

The most significant difference between the simulation and formal
verification workflows is that all formal verification will use tools
provided by OneSpin Solutions. OneSpin engineers will run either on
OneSpin’s own compute infrastructure or on the Virtual Machines provided
by IBM and managed by OpenHW. ACs from other member companies will run
on the IBM Cloud and use OneSpin tools.

.. [17]
   First week of January, 2020.

.. [18]
   OneSpin White paper: Assuring the Integrity of RISC-V Cores and SoCs.
   OneSpin Solutions, 2019.
