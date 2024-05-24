===
csr
===

Register Summary
----------------

+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| Address     | Register Name      | Description                                                                                                                |
+=============+====================+============================================================================================================================+
| 0x300       | mstatus            | The mstatus register keeps track of and controls the hart’s current operating state.                                       |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0x300       | mstatush           | The mstatush register keeps track of and controls the hart’s current operating state.                                      |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0x301       | misa               | misa is a read-write register reporting the ISA supported by the hart.                                                     |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0x304       | mie                | The mie register is an MXLEN-bit read/write register containing interrupt enable bits.                                     |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0x305       | mtvec              | MXLEN-bit read/write register that holds trap vector configuration.                                                        |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0x320       | mcountinhibit      | The mcountinhibit is a 32-bit WARL register that controls which of the hardware performance-monitoring counters increment. |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0x323-0x33f | mhpmevent[3-31]    | The mhpmevent is a MXLEN-bit event register which controls mhpmcounter3.                                                   |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0x340       | mscratch           | The mscratch register is an MXLEN-bit read/write register dedicated for use by machine mode.                               |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0x341       | mepc               | The mepc is a warl register that must be able to hold all valid physical and virtual addresses.                            |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0x342       | mcause             | The mcause register stores the information regarding the trap.                                                             |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0x343       | mtval              | The mtval is a warl register that holds the address of the instruction which caused the exception.                         |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0x344       | mip                | The mip register is an MXLEN-bit read/write register containing information on pending interrupts.                         |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0x3a0-0x3af | pmpcfg[0-15]       | PMP configuration register                                                                                                 |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0x3b0-0x3ef | pmpaddr[0-63]      | Physical memory protection address register                                                                                |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0xb00       | mcycle             | Counts the number of clock cycles executed from an arbitrary point in time.                                                |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0xb02       | minstret           | Counts the number of instructions completed from an arbitrary point in time.                                               |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0xb03-0xb1f | mhpmcounter[3-31]  | The mhpmcounter is a 64-bit counter. Returns lower 32 bits in RV32I mode.                                                  |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0xb80       | mcycleh            | upper 32 bits of mcycle                                                                                                    |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0xb82       | minstreth          | Upper 32 bits of minstret.                                                                                                 |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0xb83-0xb9f | mhpmcounter[3-31]h | The mhpmcounterh returns the upper half word in RV32I systems.                                                             |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0xf11       | mvendorid          | 32-bit read-only register providing the JEDEC manufacturer ID of the provider of the core.                                 |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0xf12       | marchid            | MXLEN-bit read-only register encoding the base microarchitecture of the hart.                                              |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0xf13       | mimpid             | Provides a unique encoding of the version of the processor implementation.                                                 |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+
| 0xf14       | mhartid            | MXLEN-bit read-only register containing the integer ID of the hardware thread running the code.                            |
+-------------+--------------------+----------------------------------------------------------------------------------------------------------------------------+

Register Description
--------------------
mstatus
-------

:Address: 0x300
:Reset Value: 0x00000000
:priviliege mode: M
:Description: The mstatus register keeps track of and controls the
   hart’s current operating state.

+---------+--------------+---------------+--------+----------+---------------+
| Bits    | Field name   | Legalvalues   | Mask   | Access   | Description   |
+=========+==============+===============+========+==========+===============+
| [30:24] | Reserved_24  |               |        | Reserved | Reserved      |
+---------+--------------+---------------+--------+----------+---------------+

mstatush
--------

:Address: 0x300
:Reset Value: 0x00000000
:priviliege mode: M
:Description: The mstatush register keeps track of and controls the
   hart’s current operating state.

+---------+--------------+---------------+--------+----------+---------------+
| Bits    | Field name   | Legalvalues   | Mask   | Access   | Description   |
+=========+==============+===============+========+==========+===============+
| [31:10] | Reserved_10  |               |        | Reserved | Reserved      |
+---------+--------------+---------------+--------+----------+---------------+

misa
----

:Address: 0x301
:Reset Value: 0x40001104
:priviliege mode: M
:Description: misa is a read-write register reporting the ISA supported
   by the hart.

+---------+--------------+---------------+--------+----------+---------------+
| Bits    | Field name   | Legalvalues   | Mask   | Access   | Description   |
+=========+==============+===============+========+==========+===============+
| [29:26] | Reserved_26  |               |        | Reserved | Reserved      |
+---------+--------------+---------------+--------+----------+---------------+

mie
---

:Address: 0x304
:Reset Value: 0x00000000
:priviliege mode: M
:Description: The mie register is an MXLEN-bit read/write register
   containing interrupt enable bits.

+---------+--------------+---------------+--------+----------+---------------+
| Bits    | Field name   | Legalvalues   | Mask   | Access   | Description   |
+=========+==============+===============+========+==========+===============+
| [31:13] | Reserved_13  |               |        | Reserved | Reserved      |
+---------+--------------+---------------+--------+----------+---------------+

mtvec
-----

:Address: 0x305
:Reset Value: 0x80010000
:priviliege mode: M
:Description: MXLEN-bit read/write register that holds trap vector
   configuration.

+--------+--------------+---------------+--------+----------+---------------+
| Bits   | Field name   | Legalvalues   | Mask   | Access   | Description   |
+========+==============+===============+========+==========+===============+
+--------+--------------+---------------+--------+----------+---------------+

mcountinhibit
-------------

:Address: 0x320
:Reset Value: 0x00000000
:priviliege mode: M
:Description: The mcountinhibit is a 32-bit WARL register that controls
   which of the hardware performance-monitoring counters increment.

+--------+---------------+---------------+------------+----------+----------------------------------------------------------------------------------------------------------------------------+
| Bits   | Field name    | Legalvalues   | Mask       | Access   | Description                                                                                                                |
+========+===============+===============+============+==========+============================================================================================================================+
| [31:0] | mcountinhibit | 0x00000000    | 0xFFFFFFFF | RW       | The mcountinhibit is a 32-bit WARL register that controls which of the hardware performance-monitoring counters increment. |
+--------+---------------+---------------+------------+----------+----------------------------------------------------------------------------------------------------------------------------+

mhpmevent[3-31]
---------------

:Address: 0x323-0x33f
:Reset Value: 0x00000000
:priviliege mode: M
:Description: The mhpmevent is a MXLEN-bit event register which controls
   mhpmcounter3.

+--------+--------------+---------------+------------+----------+--------------------------------------------------------------------------+
| Bits   | Field name   | Legalvalues   | Mask       | Access   | Description                                                              |
+========+==============+===============+============+==========+==========================================================================+
| [31:0] | mhpmevent[i] | 0x00000000    | 0xFFFFFFFF | RW       | The mhpmevent is a MXLEN-bit event register which controls mhpmcounter3. |
+--------+--------------+---------------+------------+----------+--------------------------------------------------------------------------+

mscratch
--------

:Address: 0x340
:Reset Value: 0x00000000
:priviliege mode: M
:Description: The mscratch register is an MXLEN-bit read/write register
   dedicated for use by machine mode.

+--------+--------------+---------------+------------+----------+----------------------------------------------------------------------------------------------+
| Bits   | Field name   | Legalvalues   | Mask       | Access   | Description                                                                                  |
+========+==============+===============+============+==========+==============================================================================================+
| [31:0] | mscratch     | 0x00000000    | 0xFFFFFFFF | RW       | The mscratch register is an MXLEN-bit read/write register dedicated for use by machine mode. |
+--------+--------------+---------------+------------+----------+----------------------------------------------------------------------------------------------+

mepc
----

:Address: 0x341
:Reset Value: 0x00000000
:priviliege mode: M
:Description: The mepc is a warl register that must be able to hold all
   valid physical and virtual addresses.

+--------+--------------+---------------+------------+----------+-------------------------------------------------------------------------------------------------+
| Bits   | Field name   | Legalvalues   | Mask       | Access   | Description                                                                                     |
+========+==============+===============+============+==========+=================================================================================================+
| [31:0] | mepc         | 0x00000000    | 0xFFFFFFFF | RW       | The mepc is a warl register that must be able to hold all valid physical and virtual addresses. |
+--------+--------------+---------------+------------+----------+-------------------------------------------------------------------------------------------------+

mcause
------

:Address: 0x342
:Reset Value: 0x00000000
:priviliege mode: M
:Description: The mcause register stores the information regarding the
   trap.

+--------+--------------+---------------+--------+----------+---------------+
| Bits   | Field name   | Legalvalues   | Mask   | Access   | Description   |
+========+==============+===============+========+==========+===============+
+--------+--------------+---------------+--------+----------+---------------+

mtval
-----

:Address: 0x343
:Reset Value: 0x00000000
:priviliege mode: M
:Description: The mtval is a warl register that holds the address of the
   instruction which caused the exception.

+--------+--------------+---------------+------------+----------+----------------------------------------------------------------------------------------------------+
| Bits   | Field name   | Legalvalues   | Mask       | Access   | Description                                                                                        |
+========+==============+===============+============+==========+====================================================================================================+
| [31:0] | mtval        | 0x00000000    | 0xFFFFFFFF | RW       | The mtval is a warl register that holds the address of the instruction which caused the exception. |
+--------+--------------+---------------+------------+----------+----------------------------------------------------------------------------------------------------+

mip
---

:Address: 0x344
:Reset Value: 0x00000000
:priviliege mode: M
:Description: The mip register is an MXLEN-bit read/write register
   containing information on pending interrupts.

+---------+--------------+---------------+--------+----------+---------------+
| Bits    | Field name   | Legalvalues   | Mask   | Access   | Description   |
+=========+==============+===============+========+==========+===============+
| [31:13] | Reserved_13  |               |        | Reserved | Reserved      |
+---------+--------------+---------------+--------+----------+---------------+

pmpcfg[0-15]
------------

:Address: 0x3a0-0x3af
:Reset Value: 0x00000000
:priviliege mode: M
:Description: PMP configuration register

+--------+--------------+---------------+--------+----------+---------------+
| Bits   | Field name   | Legalvalues   | Mask   | Access   | Description   |
+========+==============+===============+========+==========+===============+
+--------+--------------+---------------+--------+----------+---------------+

pmpaddr[0-63]
-------------

:Address: 0x3b0-0x3ef
:Reset Value: 0x00000020
:priviliege mode: M
:Description: Physical memory protection address register

+--------+--------------+---------------+------------+----------+---------------------------------------------+
| Bits   | Field name   | Legalvalues   | Mask       | Access   | Description                                 |
+========+==============+===============+============+==========+=============================================+
| [31:0] | pmpaddr[i]   | 0x00000000    | 0xFFFFFFFF | RW       | Physical memory protection address register |
+--------+--------------+---------------+------------+----------+---------------------------------------------+

mcycle
------

:Address: 0xb00
:Reset Value: 0x00000000
:priviliege mode: M
:Description: Counts the number of clock cycles executed from an
   arbitrary point in time.

+--------+--------------+---------------+------------+----------+-----------------------------------------------------------------------------+
| Bits   | Field name   | Legalvalues   | Mask       | Access   | Description                                                                 |
+========+==============+===============+============+==========+=============================================================================+
| [31:0] | mcycle       | 0x00000000    | 0xFFFFFFFF | RW       | Counts the number of clock cycles executed from an arbitrary point in time. |
+--------+--------------+---------------+------------+----------+-----------------------------------------------------------------------------+

minstret
--------

:Address: 0xb02
:Reset Value: 0x00000000
:priviliege mode: M
:Description: Counts the number of instructions completed from an
   arbitrary point in time.

+--------+--------------+---------------+------------+----------+------------------------------------------------------------------------------+
| Bits   | Field name   | Legalvalues   | Mask       | Access   | Description                                                                  |
+========+==============+===============+============+==========+==============================================================================+
| [31:0] | minstret     | 0x00000000    | 0xFFFFFFFF | RW       | Counts the number of instructions completed from an arbitrary point in time. |
+--------+--------------+---------------+------------+----------+------------------------------------------------------------------------------+

mhpmcounter[3-31]
-----------------

:Address: 0xb03-0xb1f
:Reset Value: 0x00000000
:priviliege mode: M
:Description: The mhpmcounter is a 64-bit counter. Returns lower 32 bits
   in RV32I mode.

+--------+----------------+---------------+------------+----------+---------------------------------------------------------------------------+
| Bits   | Field name     | Legalvalues   | Mask       | Access   | Description                                                               |
+========+================+===============+============+==========+===========================================================================+
| [31:0] | mhpmcounter[i] | 0x00000000    | 0xFFFFFFFF | RW       | The mhpmcounter is a 64-bit counter. Returns lower 32 bits in RV32I mode. |
+--------+----------------+---------------+------------+----------+---------------------------------------------------------------------------+

mcycleh
-------

:Address: 0xb80
:Reset Value: 0x00000000
:priviliege mode: M
:Description: upper 32 bits of mcycle

+--------+--------------+---------------+------------+----------+-------------------------+
| Bits   | Field name   | Legalvalues   | Mask       | Access   | Description             |
+========+==============+===============+============+==========+=========================+
| [31:0] | mcycleh      | 0x00000000    | 0xFFFFFFFF | RW       | upper 32 bits of mcycle |
+--------+--------------+---------------+------------+----------+-------------------------+

minstreth
---------

:Address: 0xb82
:Reset Value: 0x00000000
:priviliege mode: M
:Description: Upper 32 bits of minstret.

+--------+--------------+---------------+------------+----------+----------------------------+
| Bits   | Field name   | Legalvalues   | Mask       | Access   | Description                |
+========+==============+===============+============+==========+============================+
| [31:0] | minstreth    | 0x00000000    | 0xFFFFFFFF | RW       | Upper 32 bits of minstret. |
+--------+--------------+---------------+------------+----------+----------------------------+

mhpmcounter[3-31]h
------------------

:Address: 0xb83-0xb9f
:Reset Value: 0x00000000
:priviliege mode: M
:Description: The mhpmcounterh returns the upper half word in RV32I
   systems.

+--------+-----------------+---------------+------------+----------+----------------------------------------------------------------+
| Bits   | Field name      | Legalvalues   | Mask       | Access   | Description                                                    |
+========+=================+===============+============+==========+================================================================+
| [31:0] | mhpmcounter[i]h | 0x00000000    | 0xFFFFFFFF | RW       | The mhpmcounterh returns the upper half word in RV32I systems. |
+--------+-----------------+---------------+------------+----------+----------------------------------------------------------------+

mvendorid
---------

:Address: 0xf11
:Reset Value: 0xdeadbeef
:priviliege mode: M
:Description: 32-bit read-only register providing the JEDEC manufacturer
   ID of the provider of the core.

+--------+--------------+---------------+--------+----------+--------------------------------------------------------------------------------------------+
| Bits   | Field name   | Legalvalues   | Mask   | Access   | Description                                                                                |
+========+==============+===============+========+==========+============================================================================================+
| [31:0] | mvendorid    | 0xdeadbeef    | 0      | RW       | 32-bit read-only register providing the JEDEC manufacturer ID of the provider of the core. |
+--------+--------------+---------------+--------+----------+--------------------------------------------------------------------------------------------+

marchid
-------

:Address: 0xf12
:Reset Value: 0x00000000
:priviliege mode: M
:Description: MXLEN-bit read-only register encoding the base
   microarchitecture of the hart.

+--------+--------------+---------------+--------+----------+-------------------------------------------------------------------------------+
| Bits   | Field name   | Legalvalues   | Mask   | Access   | Description                                                                   |
+========+==============+===============+========+==========+===============================================================================+
| [31:0] | marchid      | 0x0           | 0      | RW       | MXLEN-bit read-only register encoding the base microarchitecture of the hart. |
+--------+--------------+---------------+--------+----------+-------------------------------------------------------------------------------+

mimpid
------

:Address: 0xf13
:Reset Value: 0x00000000
:priviliege mode: M
:Description: Provides a unique encoding of the version of the processor
   implementation.

+--------+--------------+---------------+--------+----------+----------------------------------------------------------------------------+
| Bits   | Field name   | Legalvalues   | Mask   | Access   | Description                                                                |
+========+==============+===============+========+==========+============================================================================+
| [31:0] | mimpid       | 0x0           | 0      | RW       | Provides a unique encoding of the version of the processor implementation. |
+--------+--------------+---------------+--------+----------+----------------------------------------------------------------------------+

mhartid
-------

:Address: 0xf14
:Reset Value: 0x00000000
:priviliege mode: M
:Description: MXLEN-bit read-only register containing the integer ID of
   the hardware thread running the code.

+--------+--------------+---------------+--------+----------+-------------------------------------------------------------------------------------------------+
| Bits   | Field name   | Legalvalues   | Mask   | Access   | Description                                                                                     |
+========+==============+===============+========+==========+=================================================================================================+
| [31:0] | mhartid      | 0x0           | 0      | RW       | MXLEN-bit read-only register containing the integer ID of the hardware thread running the code. |
+--------+--------------+---------------+--------+----------+-------------------------------------------------------------------------------------------------+

