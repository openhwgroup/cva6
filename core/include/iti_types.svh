// Copyright (c) 2025 Thales DIS design services SAS
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Author: Maxime Colson - Thales
// Date: 20/03/2025
// Contributors: 
// Darshak Sheladiya, SYSGO GmbH
// Umberto Laghi, UNIBO

`ifndef ITI_TYPES_SVH
`define ITI_TYPES_SVH

`define ITI_TO_ENCODER_T(Cfg) struct packed { \
     logic [Cfg.NrCommitPorts-1:0] valid; \
     logic [Cfg.NrCommitPorts-1:0][iti_pkg::IRETIRE_LEN-1:0] iretire; \
     logic [Cfg.NrCommitPorts-1:0] ilastsize; \
     iti_pkg::itype_t [Cfg.NrCommitPorts-1:0][iti_pkg::ITYPE_LEN-1:0] itype; \
     logic [iti_pkg::CAUSE_LEN-1:0] cause; \
     logic [Cfg.XLEN-1:0] tval; \
     riscv::priv_lvl_t  priv; \
     logic [Cfg.NrCommitPorts-1:0][Cfg.XLEN-1:0] iaddr; \
     logic [63:0] cycles; \
  }

`endif  // ITI_TYPES_SVH
