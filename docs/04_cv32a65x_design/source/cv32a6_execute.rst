.. _CVA6_EX_STAGE:

###############
EX_STAGE Module
###############

***********
Description
***********

The EX_STAGE module is a logical stage which implements the execute stage.
It encapsulates the following functional units:
ALU, Branch Unit, CSR buffer, Mult, load and store and CVXIF.

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

TO BE COMPLETED


Branch Unit
===========

TO BE COMPLETED


CSR Buffer
==========

TO BE COMPLETED


Mult
====

TO BE COMPLETED

.. figure:: ../images/mult_modules.png
   :name: mult submodules
   :align: center
   :alt:

   mult submodules

----------
multiplier
----------

TO BE COMPLETED


------
serdiv
------

TO BE COMPLETED


Load Store Unit (LSU)
=====================

TO BE COMPLETED

.. figure:: ../images/load_store_unit_modules.png
   :name: load_store_unit submodules
   :align: center
   :alt:

   load_store_unit submodules

----------
store_unit
----------

TO BE COMPLETED


---------
load unit
---------

TO BE COMPLETED


----------
lsu_bypass
----------

TO BE COMPLETED



CVXIF_fu
========

TO BE COMPLETED
