CV32E40P Change Log
===
Copyright (c) 2005-2021 Imperas Software Ltd., www.imperas.com

This CHANGELOG contains information for the Imperas OVP OpenHW CV32E40P fixed platform which includes information of the OVP Simulator and RISCV processor model

---

- Trigger Module Behaviour
  - tdata1 access only permitted in debug mode, ignored in others

Date 2020-August-06
Version 20200805.1
===
- Trigger Module Behaviour
  - tdata1 execute bit enables address fetch trap on value in tdata2
  - trap causes entry to debug mode and execution from debug vector

Date 2020-August-05
Version 20200805.0
===
- Trigger Module Registers
  - Initial registers added for tselect, tdata1, tdata2, tdata3, tinfo
  - No trigger behaviour added
- Local Interrupt
  - 16 local interrupts are enabled
  - Interrupt acknowledge and Interrupt Id provided
- CSR Registers
  - Add mtval, mcontext, scontext write ignored and read zero

Date 2020-July-29
Version 20200728.2
===
- CSR Registers
   - cycle, intret, cycleh, intereth illegal instruction exception on access


Date 2020-July-28
Version 20200728.1
===

- Add Debug Module
   - Provides input signals haltreq and resethaltreq to enter debnuig mode
   - Provides output DM to provide Debug Mode
- Trigger Module register
   - Add tinfo register writes ignored / read zero
- CSR Registers
   - mcycle, mintret, mcycleh, mintreth behaviour write ignored / read zero
   - cycle, intret, cycleh, intereth  behaviour write ignored / read zero
   - Set PMP undefined to remove pmpcfgN registers

Date 2020-July-23
===

- CSR Configuration updates
  - Enabled mcounten register
  - Set mvendorid to 0x0602
  - Set mcountinhibit reset value 0xd

===