..
   Copyright (c) 2023 OpenHW Group
   Copyright (c) 2023 Thales DIS design services SAS

   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

.. Level 1
   =======

   Level 2
   -------

   Level 3
   ~~~~~~~

   Level 4
   ^^^^^^^

.. _cva6_pmp:

PMP
===
The CVA6 includes a Physical Memory Protection (PMP) unit. The PMP is both
statically and dynamically configurable. The static configuration is performed
through the top level parameters ``CVA6Cfg.NrPMPEntries``. The dynamic
configuration is performed through the CSRs described in Control and Status
Registers. A maximum of 16 PMP entries are supported.

All PMP CSRs are always implemented, but CSRs (or bitfields of CSRs) related to
PMP entries with number ``CVA6Cfg.NrPMPEntries`` and above are hardwired to
zero. All PMPs reset to zero.

When the ``L`` (Lock) bit is set, PMPs are also enforced in M-mode.

The PMP grain is ``2**G+2``. Only a PMP granularity of 8 bytes (``G=1``) is
supported in CVA6. PMP address length is equal to the processors physical
address length. Since ``G=1`` the ``NA4`` modes is not selectable.

Writes to ``pmpaddr`` are WARL and depend on the address mode. For naturally
aligned power-of 2 addressing mode (``NAPOT``) it is set to ``1``, for top
boundary of an arbitrary range (``TOR``) or ``OFF`` it is set to ``0``.

If, on write to `pmpcfgX`, ``R=0`` and ``W=1`` are set the CSR will not be
updated.
