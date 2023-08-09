..
   Copyright (c) 2023 OpenHW Group
   Copyright (c) 2023 Thales

   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

.. Level 1
   =======

   Level 2
   -------

   Level 3
   ~~~~~~~

   Level 4
   ^^^^^^^

.. _cva6_cvx_interface_coprocessor:

CV-X-IF Interface and Coprocessor
=================================

CV-X-IF interface specification
-------------------------------

Description
~~~~~~~~~~~
This design specification presents global functionalities of
Core-V-eXtension-Interface (XIF, CVXIF, X-interface) in the CVA6 core.

.. code-block:: text

   The CORE-V X-Interface is a RISC-V eXtension interface that provides a
   generalized framework suitable to implement custom coprocessors and ISA
   extensions for existing RISC-V processors.

   --core-v-xif Readme, https://github.com/openhwgroup/core-v-xif

The specification of the CVXIF bus protocol can be found at: [CV-X-IF]

Core-V-eXtension aims to:

* Create interfaces to connect a coprocessor to the CVA6 to execute instructions.
* Offload CVA6 illegal instrutions to the coprocessor to be executed.
* Get the result offloaded instruction from the coprocessor so it is writeback into the CVA6 register files.
* Add standard RISCV instructions unsupported by CVA6 or custom instructions and implemented those in a coprocessor.
* Kill offloaded instructions to allow speculative execution in the coprocessor. (Unsupported)
* Connect the coprocessor to memory via the Load and Store Unit of the CVA6. (Unsupported)

The coprocessor operates like another functional unit so it is connected to
the CVA6 in the execute stage.

Only the 3 mandatory interfaces from the specification (issue, commit and result
) have been implemented.
Compressed interface, Memory Interface and Memory result interface are not yet
implemented in the CVA6.

Supported Parameters
~~~~~~~~~~~~~~~~~~~~
The following table presents CVXIF parameters supported by CVA6.

=============== =========================== ===============================================
Signal          Value                       Description
=============== =========================== ===============================================
**X_NUM_RS**    int: 2 or 3 (configurable)  | Number of register file read ports that can
                                            | be used by the eXtension interface
**X_ID_WIDTH**  int: 3                      | Identification width for the eXtension
                                            | interface
**X_MEM_WIDTH** n/a (feature not supported) | Memory access width for loads/stores via the
                                            | eXtension interface
**X_RFR_WIDTH** int: XLEN                   | Register file read access width for the
                                            | eXtension interface
**X_RFW_WIDTH** int: XLEN                   | Register file write access width for the
                                            | eXtension interface
**X_MISA**      logic[31:0]: 0x0000_0000    | MISA extensions implemented on the eXtension
                                            | interface
=============== =========================== ===============================================

CVXIF Enabling
~~~~~~~~~~~~~~
CVXIF can be enabled/disabled via the ``CVA6ConfigCvxifEn`` parameters in the ``cva6_config_pkg``.

Illegal instruction decoding
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The CVA6 decoder module detects illegal instructions for the CVA6, prepares exception field
with relevant information (exception code "ILLEGAL INSTRUCTION", instruction value).

The exception valid flag is raised in decoder when CVXIF is disabled. Otherwise
it is not raised at this stage because the decision belongs to the coprocessor
after the offload process.

RS3 support
~~~~~~~~~~~
Number of source registers used by the CVXIF interface is configurable with 2 or
3 source registers.

If CVXIF is enabled and configured with 3 source registers,
a third read port is added to the CVA6 general purpose register file.

Description of interfaces connections between CVA6 and Coprocessor
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In the execute stage, there is a new functional unit dedicated to drive the CVXIF interfaces.
Here is *how* and *to what* CVXIF interfaces are connected to the CVA6.

* Issue interface
   - Request
      + | Operands are connected to ``issue_req.rs`` signals
      + | Scoreboard transaction id is connected to ``issue_req.id`` signal.
        | Therefore scoreboard ids and offloaded instruction ids are linked
        | together (equals in this implementation). It allows the CVA6 to do out
        | of order execution with the coprocessor in the same way as other
        | functional units.
      + | Undecoded instruction is connected to ``issue_req.instruction``
      + | Valid signal for CVXIF functional unit is connected to
        | ``issue_req.valid``
      + | All ``issue_req.rs_valid`` signals are set to 1. Validness of source
        | registers is assured by validness of valid signal sent from issue stage.
   - Response
      + | If ``issue_resp.accept`` is set during a transaction (i.e issue valid
        | and ready are set). Offloaded instruction is accepted by the coprocessor
        | and a result transaction will happen.
      + | If ``issue_resp.accept`` is not set during a transaction, the offloaded
        | instruction is illegal and an illegal instruction exception will be
        | raised as soon as no result transaction are writing on the writeback bus.

* Commit interface
   - | Valid signal of commit interface is connected to the valid signal of
     | issue interface.
   - | Id signal of commit interface is connected to issue interface id signal.
     | (i.e = scoreboard id)
   - | Killing of offload instruction is never set. (Unsupported feature)
   - | Therefore all accepted offloaded instructions are commited to their
     | execution and no killing of instruction is possible in this implementation.

* Result interface
   - Request
      + | Ready signal of result interface is always set as CVA6 is always ready
        | to take a result from coprocessor for accepted offloaded instruction.
   - Response
      + | Result response is directly connected to writeback bus of the CVXIF
        | functionnal unit.
      + | Valid signal of result interface is connected to valid signal of
        | writeback bus.
      + | ID signal of result interface is connected to scoreboard id of
        | writeback bus.
      + | WE signal of result interface is connected to a dedicated CVXIF WE
        | signal in CVA6 which signals scoreboard if a writeback should happen
        | or not in CVA6 register file.
      + | exccode and exc signal of result interface are connected to exception
        | signals of writeback bus. Exception from coprocessor does not write
        | the tval field in exception signal of writeback bus.
      + | Three registers are added to hold illegal instruction information in
        | case a result transaction and a non-accepted issue transaction happen
        | in the same cycle. Result transaction will be written to the writeback
        | bus in this case having priority over the non-accepted instruction due
        | to being linked to an older offloaded instruction. Once the writeback
        | bus is free, an illegal instruction exception will be raised thank to
        | information hold in those three registers.

Coprocessor recommendations for use with CVA6's CVXIF
-----------------------------------------------------

CVA6 supports all coprocessors supporting the Core-V-eXtension specification with the exception of :

* Coprocessor requiring the Memory interface and Memory result interface (Not implemented in CVA6)
   - All memory transaction should happened via the Issue interface, i.e. Load into CVA6 register file
     then initialize an issue transaction.
* Coprocessor requiring the Compressed interface (Not implemented in CVA6)
   - RISCV Compressed extension is already implemented in CVA6. User Space for custom compressed instruction
     is not big enough to have RISCV Compressed extension and a custom compressed extension.
* Not stateless coprocessor.
   - CVA6 will commit on the Commit interface all its issue transactions. Speculation
     informations are only kept in the CVA6 and speculation process is only done in CVA6.
     The Coprocessor should be stateless otherwise it would not be able to kill or change its state in case
     of a misspredict or flush in CVA6.

How to use CVA6 without CV-X-IF interface
-----------------------------------------
Select a configuration with ``CVA6ConfigCvxifEn`` parameter disabled or change it for your configuration.

How to use CV-X-IF with CVA6
----------------------------
We don’t commit yet to write this section. We expect the audience to be power users.

Use CVA6 with CV-X-IF interface
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

How to design a coprocessor for the CV-X-IF interface
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

How to program a CV-X-IF coprocessor
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
