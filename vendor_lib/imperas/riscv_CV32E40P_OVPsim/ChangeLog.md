CV32E40P Change Log
===
Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com

This CHANGELOG contains information for the Imperas OVP OpenHW CV32E40P fixed platform which includes information of the OVP Simulator and RISCV processor model

---
Date 2020-July-28
===

- Add Debug Module
   - Provides input signals haltreq and resethaltreq to enter debnuig mode
   - Provides output DM to provide Debug Mode
- Trigger Module register
   - Add tinfo register writes ignored / read zero
- CSR Registers
   - mcycle, mintret, mcycleh, mintreth behaviour write ignored / read zero
   - Set PMP undefined

Date 2020-July-23
===

- CSR Configuration updates
  - Enabled mcounten register
  - Set mvendorid to 0x0602
  - Set mcountinhibit reset value 0xd

===