---
title: Ariane
permalink: /docs/home/
redirect_from: /docs/index.html
---

This document describes the 6-stage, single issue Ariane CPU which implements the 64-bit RISC-V instruction set. It fully implements I, M and C extensions as specified in Volume I: User-Level ISA V 2.1 as well as the draft privilege extension 1.10. It implements three privilege levels M, S, U to fully support a Unix-like operating system.

### Scope and Purpose

The purpose of the core is to run a full OS at reasonable speed and IPC. To achieve the necessary speed the core features a 6-stage pipelined design. In order to increase the IPC the CPU features a scoreboard which should hide latency to the data RAM (cache) by issuing data-independent instructions.
The instruction RAM has (or L1 instruction cache) an access latency of 1 cycle on a hit, while accesses to the data RAM (or L1 data cache) have a longer latency of 3 cycles on a hit.

![Ariane Block Diagram](../../img/ariane_overview.png)
