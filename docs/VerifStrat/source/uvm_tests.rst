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


.. _uvm_tests:

UVM Testcases in the CORE-V-VERIF Environments
==============================================

The overall structure of the CORE-V-VERIF UVM environments should be familiar to anyone with UVM experience.
This section discusses the CORE-V-VERIF specific implementation details that affect test execution, and that are important to test writers.
It attempts to be generic enough to apply to both the CV32E and CVA6 environments.

Before reading this chapter, it is recommended that you read the Test Programs chapter.


Test-Programs in the CORE-V-VERIF UVM Environment
-------------------------------------------------

The UVM environment can support test-programs regardless of how they are created, so long as they are compatible with the BSP.
However, the UVM environment needs to know two things about a test program:

-  Is the program pre-existing, or does it need to be generated at run-time?
-  Is the test program self-checking?
   That is, can it determine, on its own, the pass/fail criteria of a test program and can it signal this to the testbench?

Many of the test programs inherited from the RI5CY project are both pre-existing and self-checking.
It is expected, but not required, that most of the pre-existing test programs will be self-checking.

CORE-V-VERIF incorporates a random instruction stream generator to generate many test programs.
It is expected that most of generated test programs will **not** be self-checking.

The UVM environment is equipped to support four distinct types of test programs:

1. **Pre-existing, self-checking**
   The environment requires a memory image for the program to exist in
   the expected location, and will check the “status flags”
   virtual peripheral for pass/fail information.
2. **Pre-existing, not self-checking**
   The environment requires a memory image for the program to exist in
   the expected location, and will **not** check the “status flags”
   virtual peripheral for pass/fail information.
3. **Generated, self-checking**
   The environment will use its random instruction generator to create a
   test program, and will check the “status flags” virtual peripheral
   for pass/fail information.
4. **Generated, not self-checking**
   The environment will use its random instruction generator to create a
   test program, and will **not** check the “status flags” virtual
   peripheral for pass/fail information.
5. **None**
   It is possible to run a UVM test without running a test program. An
   example might be a test to access CSRs via the debug module interface
   interface in debug mode.

Although five types are supported, it is expected that types 1 and 4
will predominate.

Simulations pass/fail outcomes will also be affected by other
checkers/monitors that are not part of the status flags virtual
peripheral. It is required that any such checkers/monitors shall signal
an error condition with \`uvm\_error(), and these will cause a
simulation test to fail, independent of what the test program may or may
not write to the status flags virtual peripheral.

It is possible to use an instruction generator to write out a set of
test programs, self checking or not, and run these as if they were
pre-existing test programs. From the environment’s perspective, this
indistinguishable from type 1 or type 2.

The programs can be written to execute any legal instruction supported by the core.
Programs have access to the full address range supported by the memory model in the testbench plus a small set of memory-mapped virtual peripherals as described in :ref:`virtual_peripherals`.


UVM Test
--------

A UVM Test is the top-level object in every UVM environment. That is,
the environment object(s) are members of the testcase object, not the
other way around. As such, UVM requires that all tests extend from
*uvm\_test* and the CV32E environment defines a “base test”,
*uvmt\_cv32\_base\_test\_c*, that is a direct extension of *uvm\_test*.
All testcases developed for CV32E should extend from the base test, as
doing so ensures that the proper test flow discussed here is maintained
(it also frees the test writer from much mundane effort and code
duplication). The comment headers in the base test (attempt to) provide
sufficient information for the test writer to understand how to extend
it for their needs.

A typical UVM test for CORE-V will extend three time consuming tasks:

1. **reset_phase():** often, nothing is done here except to call
   *super.reset_phase()* which will invoke the default reset sequence
   (which is a random sequence). Should the test writer wish to, this is
   where a test-specific reset virtual sequence could be invoked.
2. **configure_phase():** in a typical UVM environment, this is a busy
   task. However, assuming the program executed the core does so, the
   core’s CSRs do not require any configuration before execution begins.
   Any test that requires pre-compiled programs to be loaded into
   instruction memory should do that here.
3. **run_phase():** for most tests, this is where the procedural code
   for the test will reside. A typical example of the run-flow here
   would be:
   -  Raise an objection;
   -  Assert the core’s fetch\_en input;
   -  Wait for the core and/or environment(s) to signal completion;
   -  Drop the objection.

Workarounds
~~~~~~~~~~~

The CV32E base test, *uvmt_cv32_base_test_c*, in-lines code (using
**\`include)** from *uvmt_cv32_base_test_workaround.sv*. This file
is a convenient place to put workarounds for defects or incomplete code
in either the environment or RTL that will affect all tests. This file
must be reviewed before the RTL is frozen, and ideally it will be empty
at that time.

Run-flow in a CORE-V Test
-------------------------

The test program in the CORE-V environment directly impacts the usual
run-flow that is familiar to UVM developers. Programs running on the
core are completely self-contained within their extremely simple
execution environment that is wholly defined by the ISA, memory map
supported by the *dp\_mem* and the virtual peripherals supported by
*mm\_mem*\. This execution environment knows nothing about the
UVM environment, so the CORE-V UVM environments are implemented to be
aware of the test program and to respond accordingly as part of the
run-flow.

The UVM Testcases chapter of this document discusses how the configure_phase() and run_phase() manage the interaction between the UVM environment and the test program.
This interaction is depends on the type of test program.
Illustration 8 shows how the CORE-V UVM base test supports a type 1 test program.

.. figure:: ../images/type1.png
   :name: TYPE1_Test_Program
   :align: center
   :alt:

   Illustration 8: Preexisting, Self-checking Test Program (type 1) in a
   CORE-V UVM test

In the self-checking scenario, the testcase is pre-compiled into machine
code and loaded into the *dp_ram* using the **$readmemh()** DPI call.
The next sub-section explains how to select which test program to run
from the command-line. During the configuration phase the test signals
the TB to load the memory. The TB assumes the test file already exists
and will terminate the simulation if it does not.

In the run phase the base test will assert the fetch_en input to the
core which signals it to start running. The timing of this is randomized
but keep in mind that it will always happen after reset is de-asserted
(because resets are done in the reset phase, which always executes
before the run phase).

At this point the run flow will simply wait for the test program to flag
that it is done via the status flags virtual peripheral. The test
program is also expected to properly assert the test pass or test fail
flags. Note that the environment will wait for the test flags to asserts
or until the environment’s watch dog timer fires. A watch-dog firing
will terminate the simulation and is, by definition, a failure.

.. figure:: ../images/type4.png
   :name: TYPE4_Test_Program
   :align: center
   :alt:

   Illustration 9: Generated, non-self-checking (type 4) Test Program in
   a CORE-V UVM test

The flow for a type 4 (generated, non-self checking) test program is
only slightly different as shown in Illustration 9. In these tests the configure phase
will invoke the generator to produce a test program and the toolchain to
compile it before signalling the TB to load the machine code into
testbench memory. As before, the run phase will assert fetch_en to the core
and the program begins execution.

Recall that a type 4 test program will not use the status flags virtual
peripheral to signal test completion. It is therefore up to the UVM
environment to detect end of test. This is done when the various agents
in the environment detect a lack of activity on their respective
interfaces. The primary way to detect this is via the Instruction-Retire
agent (TODO: describe this agent).

In a non-self-checking test program the intelligence to determine
pass/fail must come from the environment. In the CORE-V UVM environments
this is done by scoreboarding the results of the core execution and
those predicted by the ISS as shown in . Note that most UVM tests that
run self-checking test programs will also use the ISS as part of its
pass/fail determination.

CORE-V Testcase Writer’s Guide
------------------------------
TODO

Writing a Test Program
~~~~~~~~~~~~~~~~~~~~~~

This document will probably never include a detailed description for
writing a test program. The core’s ISA is well documented and the
execution environment supported by the testbench is trivial. The best
thing to do is check out the examples at
**$CORE_V_VERIF/cv32e40p/tests/programs**.

Writing a UVM Test to run a Test Program
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The CV32E40P base test, *uvmt_cv32e40p_base_test_c*, has been written to
support all five of the test program types discussed above.

There are pre-existing UVM tests for type 1 (pre-existing,
self-checking) and type 4 (generated, not-self-checking) tests for
CV32E40P in the core-v-verif repository. If you need a type 2 or type 3
test, have a look at these and it should be obvious what to do.

Testcase Scriptware
^^^^^^^^^^^^^^^^^^^

At **$CORE_V_VERIF/cv32e40p/tests/uvmt_cv32e40p/bin/test_template** you will
find a shell script that will generate the shell of a testcase that is
compatible with the base test. This will save you a bit of typing.

Running the testcase
~~~~~~~~~~~~~~~~~~~~

Testcases are intended to be launched from
**$CORE_V_VERIF/cv32e40p/sim/uvmt**.

