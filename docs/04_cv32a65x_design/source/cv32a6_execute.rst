.. _CVA6_EX_STAGE:

###############
EX_STAGE Module
###############

***********
Description
***********

The EX_STAGE module is a logical stage which implements the execute
stage. It encapsulates the following functional units: ALU, Branch Unit,
CSR buffer, Mult, load and store and CVXIF.

The module is connected to:

* ID_STAGE module provides scoreboard entry.
* 

.. include:: port_ex_stage.rst

*************
Functionality
*************

TO BE COMPLETED

**********
Submodules
**********

.. figure:: ../images/ex_stage_modules.png
   :name: EX_STAGE submodules
   :align: center
   :alt:

   EX_STAGE submodules


ALU
===

The arithmetic logic unit (ALU) is a small piece of hardware which
performs 32 and 64-bit arithmetical operations: subtraction, addition,
shifts, comparisons...
It always completes its operation in a single cycle.

.. include:: port_alu.rst


Branch Unit
===========

The branch unit module manages all kind of control flow changes
i.e.: conditional and unconditional jumps. It calculates the target
address and decides whether to take the branch or not.
It also decides if a branch was mis-predicted or not and reports
corrective actions to the pipeline stages.

.. include:: port_branch_unit.rst


CSR Buffer
==========

The CSR buffer module stores the CSR address at which the
instruction is going to read/write. As the CSR instruction alters the
processor architectural state, this instruction has to be buffered until
the commit stage decides to execute the instruction.

.. include:: port_csr_buffer.rst


Mult
====

The multiplier module supports the division and multiplication
operations.

.. figure:: ../images/mult_modules.png
   :name: mult submodules
   :align: center
   :alt:

   mult submodules

.. include:: port_mult.rst


----------
multiplier
----------

Multiplication is performed in two cycles and is fully pipelined.

.. include:: port_multiplier.rst


------
serdiv
------

The division is a simple serial divider which needs 64 cycles in the
worst case.

.. include:: port_serdiv.rst


Load_Store_Unit (LSU)
=====================

The load store module interfaces with the data memory (D$) to manage the
load and store operations.

The LSU does not handle misaligned accesses: access which are not
aligned to a 64 bit boundary for double word accesses, access which are
not aligned to a 32-bit boundary for word access and the accesses which
are not aligned on 16-bit boundary for half word access. If encounters
such a load or store it will throw a misaligned exception.

.. figure:: ../images/load_store_unit_modules.png
   :name: load_store_unit submodules
   :align: center
   :alt:

   load_store_unit submodules

.. include:: port_load_store_unit.rst


----------
store_unit
----------

The store_unit module manages the data store operations.

As stores can be speculative, the store instructions need to be
committed by ISSUE_STAGE module before possibily altering the processor
state.
Store buffer keeps track of store requests. XXXXXXXXXXX for outstanding store
instructions (which are still speculative) and one buffer for committed
store instructions.
When ISSUE_STAGE module commits a store instruction, outstanding store
becomes committed.

When commit buffer is not empty, the buffer automatically
tries to write the oldest store to the data cache.

Furthermore, the store_unit module provides information to the load_unit
to know if any outstanding store matches load.

.. include:: port_store_unit.rst


---------
load_unit
---------

The load_unit module manages the data load operations.

Before issuing a load, the load unit needs to check the store buffer for
potential aliasing. It wwill insert stalls until it can't satisfy the
current request. This means:
* Two loads to the same address are allowed.
* Two stores to the same address are allowed.
* A store followed by a load to the same address can only be satisfied
if the store has already been committed (marked as committed in the
store buffer).


.. include:: port_load_unit.rst


----------
lsu_bypass
----------

TO BE COMPLETED

.. include:: port_lsu_bypass.rst


CVXIF_fu
========

TO BE COMPLETED

.. include:: port_cvxif_fu.rst

