..
   Copyright 2023 Thales DIS France SAS
   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales



CSR list
========

.. csv-table::
   :widths: auto
   :align: left
   :header: "Name", "Display Name", "Address Offset"

   "``MSTATUS``", "Machine Status Register", "0x300"
   "``MISA``", "Machine ISA Register", "0x301"
   "``MIE``", "Machine Interrupt Enable Register", "0x304"
   "``MTVEC``", "Machine Trap Vector Register", "0x305"
   "``MSTATUSH``", "Upper 32-bits of Machine Status Register", "0x310"
   "``MHPMEVENT3-31``", "Machine HW Perf Monitoring Event Selector", "0x323-0x33f"
   "``MSCRATCH``", "Machine Scratch", "0x340"
   "``MEPC``", "Machine Exception Program Counter", "0x341"
   "``MCAUSE``", "Machine Cause", "0x342"
   "``MTVAL``", "Machine Trap Value", "0x343"
   "``MIP``", "Machine Interrupt Pending", "0x344"
   "``PMPCFG0-3``", "Physical Memory Protection Config 0", "0x3a0-0x3a3"
   "``PMPADDR0-15``", "Physical Memory Protection Address", "0x3b0-0x3bf"
   "``ICACHE``", "Instruction Cache", "0x7C0"
   "``MCYCLE``", "M-mode Cycle counter", "0xB00"
   "``MINSTRET``", "Machine Instruction Retired counter", "0xB02"
   "``MCYCLEH``", "Upper 32-bits of M-mode Cycle counter", "0xB80"
   "``MINSTRETH``", "Upper 32-bits of Machine Instruction Retired counter", "0xB82"
   "``MHPMCOUNTER3-31``", "Machine HW Performance Monitoring Counter", "0xb03-0xb1f"
   "``MHPMCOUNTERH3-31``", "Upper 32 bits of Machine HW Perf Monitoring Counter", "0xb83-0xb9f"
   "``CYCLE``", "Cycle counter", "0xC00"
   "``INSTRET``", "Instruction Retired counter", "0xC02"
   "``CYCLEH``", "Upper 32-bits of Cycle counter", "0xC80"
   "``INSTRETH``", "Upper 32-bits of Instruction Retired counter", "0xC82"
   "``MVENDORID``", "Machine Vendor ID", "0xF11"
   "``MARCHID``", "Machine Architecture ID", "0xF12"
   "``MIMPID``", "Machine Implementation ID", "0xF13"
   "``MHARTID``", "Machine HW Thread ID", "0xF14"
