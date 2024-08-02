// Copyright 2024 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group

/**** Frontend interface with parametrized :  ****/

interface uvmt_frontend_intf #(
   parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty
) (
   input bit clk,
   input bit rst_n
   );

   typedef enum logic [2:0] {
      NoCF,    // No control flow prediction
      Branch,  // Branch
      Jump,    // Jump to address from immediate
      JumpR,   // Jump to address from registers
      Return   // Return Address Prediction
   } cf_t;

   typedef struct packed {
      logic [CVA6Cfg.XLEN-1:0] cause;  // cause of exception
      logic [CVA6Cfg.XLEN-1:0] tval;  // additional information of causing exception (e.g.: instruction causing it),
      // address of LD/ST fault
      logic [CVA6Cfg.GPLEN-1:0] tval2;  // additional information when the causing exception in a guest exception
      logic [31:0] tinst;  // transformed instruction information
      logic gva;  // signals when a guest virtual address is written to tval
      logic valid;
   } exception_t;

   typedef struct packed {
      cf_t                     cf;               // type of control flow prediction
      logic [CVA6Cfg.VLEN-1:0] predict_address;  // target address at which to jump, or not
   } branchpredict_sbe_t;

   typedef  struct packed{
      logic                    valid;           // prediction with all its values is valid
      logic [CVA6Cfg.VLEN-1:0] pc;              // PC of predict or mis-predict
      logic [CVA6Cfg.VLEN-1:0] target_address;  // target address at which to jump, or not
      logic                    is_mispredict;   // set if this was a mis-predict
      logic                    is_taken;        // branch is taken
      cf_t                     cf_type;         // Type of control flow change
   } bp_resolve_t;

   typedef struct packed {
      logic                    req;      // we request a new word
      logic                    kill_s1;  // kill the current request
      logic                    kill_s2;  // kill the last request
      logic                    spec;     // request is speculative
      logic [CVA6Cfg.VLEN-1:0] vaddr;    // 1st cycle: 12 bit index is taken for lookup
   } icache_dreq_t;

   typedef struct packed {
      logic                                ready;  // icache is ready
      logic                                valid;  // signals a valid read
      logic [CVA6Cfg.FETCH_WIDTH-1:0]      data;   // 2+ cycle out: tag
      logic [CVA6Cfg.FETCH_USER_WIDTH-1:0] user;   // User bits
      logic [CVA6Cfg.VLEN-1:0]             vaddr;  // virtual address out
      exception_t                          ex;     // we've encountered an exception
   } icache_drsp_t;

   typedef struct packed {
      logic [CVA6Cfg.VLEN-1:0] address;  // the address of the instructions from below
      logic [31:0] instruction;  // instruction word
      branchpredict_sbe_t     branch_predict; // this field contains branch prediction information regarding the forward branch path
      exception_t             ex;             // this field contains exceptions which might have happened earlier, e.g.: fetch exceptions
   } fetch_entry_t;

   // Next PC when reset - SUBSYSTEM
   logic [CVA6Cfg.VLEN-1:0] boot_addr_i;
   // Flush branch prediction - zero
   logic flush_bp_i;
   // Flush requested by FENCE, mis-predict and exception - CONTROLLER
   logic flush_i;
   // Halt requested by WFI and Accelerate port - CONTROLLER
   logic halt_i;
   // Set COMMIT PC as next PC requested by FENCE, CSR side-effect and Accelerate port - CONTROLLER
   logic set_pc_commit_i;
   // COMMIT PC - COMMIT
   logic [CVA6Cfg.VLEN-1:0] pc_commit_i;
   // Exception event - COMMIT
   logic ex_valid_i;
   // Mispredict event and next PC - EXECUTE
   bp_resolve_t resolved_branch_i;
   // Return from exception event - CSR
   logic eret_i;
   // Next PC when returning from exception - CSR
   logic [CVA6Cfg.VLEN-1:0] epc_i;
   // Next PC when jumping into exception - CSR
   logic [CVA6Cfg.VLEN-1:0] trap_vector_base_i;
   // Debug event - CSR
   logic set_debug_pc_i;
   // Debug mode state - CSR
   logic debug_mode_i;
   // Handshake between CACHE and FRONTEND (fetch) - CACHES
   icache_dreq_t icache_dreq_o;
   // Handshake between CACHE and FRONTEND (fetch) - CACHES
   icache_drsp_t icache_dreq_i;
   // Handshake's data between fetch and decode - ID_STAGE
   fetch_entry_t [CVA6Cfg.NrIssuePorts:0] fetch_entry_o;
   // Handshake's valid between fetch and decode - ID_STAGE
   logic [CVA6Cfg.NrIssuePorts:0] fetch_entry_valid_o;
   // Handshake's ready between fetch and decode - ID_STAGE
   logic [CVA6Cfg.NrIssuePorts:0] fetch_entry_ready_i;

endinterface : uvmt_frontend_intf
