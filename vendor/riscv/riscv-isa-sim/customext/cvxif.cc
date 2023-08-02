// Copyright (C) 2022 Thales DIS Design Services SAS
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0.
//
// Original Author: Zbigniew CHAMSKI <zbigniew.chamski@thalesgroup.com>

#define DECODE_MACRO_USAGE_LOGGED 1
#include "decode_macros.h"
#include "cvxif.h"
#include "mmu.h"
#include <cstring>

// Define custom insns templates.
// The insn-level wrapper is 'c##n' (default implementation,
// writeback disabled), the default implementation
// is 'custom##n': illegal instruction, return 0.
// The writeback controller 'cvxif_extn_t::do_writeback_p'
// is in charge of determining if writeback is required or not.
// Expected instruction encoding is 4 bytes.
#define customX(n) \
static reg_t c##n(processor_t* p, insn_t insn, reg_t pc) \
  { \
    cvxif_t* cvxif = static_cast<cvxif_t*>(p->get_extension()); \
    cvxif_insn_t custom_insn; \
    custom_insn.i = insn; \
    reg_t xd = cvxif->default_custom##n(custom_insn); \
    if (cvxif->do_writeback_p(custom_insn)) \
      WRITE_RD(xd); \
    return pc+4; \
  } \
  \
  reg_t default_custom##n(cvxif_insn_t insn) \
  { \
    return custom##n(insn); \
  }

// This class instantiates the CV-X-IF interface.
class cvxif_t : public cvxif_extn_t
{
 public:
  const char* name() { return "cvxif_spike"; }

  bool do_writeback_p(cvxif_insn_t copro_insn)
  {
    // INSN_R personality serves to simplify access to standard encoding fields.
    cvxif_r_insn_t insn_r = copro_insn.r_type;

   if (insn_r.opcode != 0x7b /* MATCH_CUSTOM3 */)
      return false;
    else switch (insn_r.funct3)
    {
      case FUNC3_0:
        //CUS_NOP have rd equal to zero
        return (insn_r.rd != 0x0);

      case FUNC3_1:
        //Only CUS_ADD
        return true;
      
      case FUNC3_2:
        //Only CUS_EXC
        return false;
      
      default:
        // All other cases: writeback is assumed REQUIRED.
        return false;
    }
  }

  // Custom0 instructions: default behaviour.
  reg_t custom0(cvxif_insn_t incoming_insn)
  {
    illegal_instruction();
    return -1;
  }

  // Custom1 instructions: default behaviour.
  reg_t custom1(cvxif_insn_t incoming_insn)
  {
    illegal_instruction();
    return -1;
  }

  // Custom2 instructions: default behaviour.
  reg_t custom2(cvxif_insn_t incoming_insn)
  {
    illegal_instruction();
    return -1;
  }

  // Custom3 instructions: provide an explicit implementation of decode+exec.
  reg_t custom3(cvxif_insn_t incoming_insn)
  {
    // Assume R-type insn: it shares opcode and funct3 fields with other CVXIF insn formats.
    cvxif_r_insn_t r_insn = incoming_insn.r_type;
    // INSN_T simplifies access to register values.
    insn_t insn = incoming_insn.i;

    switch (r_insn.funct3)
    {
      case FUNC3_0:
        switch (r_insn.funct7 & 0x1) {
          case NO_RS3:
            switch (r_insn.funct7 & 0xe) {
              case CUS_NOP:
                break;
              case CUS_U_ADD:
                if (p -> get_state() -> prv != PRV_U) {
                  illegal_instruction();
                }
                return (reg_t) ((reg_t) RS1 + (reg_t) RS2 + (reg_t) RS3);

              case CUS_S_ADD:
                if (p -> get_state() -> prv != PRV_S) {
                  illegal_instruction();
                }
                return (reg_t) ((reg_t) RS1 + (reg_t) RS2);

              case CUS_ADD_MULTI:
                return (reg_t) ((reg_t) RS1 + (reg_t) RS2);

              default:
                illegal_instruction();
            }
            break;
          case RS3_IN:
            //Actually only CUS_ADD_RS3 using rs3, we don't need to add another switch case
            if (p -> get_nb_register_source() != 3) {
              illegal_instruction();
            }
            return (reg_t) ((reg_t) RS1 + (reg_t) RS2 + (reg_t) RS3);
          default:
            illegal_instruction();
        }
        break;
      case FUNC3_1:
        switch(r_insn.funct7) {
          case 0:
            return (reg_t) ((reg_t) RS1 + (reg_t) RS2);
            break;
          default:
            illegal_instruction();
        }
      
      case FUNC3_2:
        switch (r_insn.funct7) {
          case (0x60):
            if (r_insn.rs2 != 0 || r_insn.rd != 0){
              illegal_instruction();
            } else {
              raise_exception(insn, (reg_t) (r_insn.rs1));
            }
            break;
          default:
            illegal_instruction();
          }
      default:
        illegal_instruction();
    }

    // FORNOW: Return 0xf......f to simplify debugging.
    return (reg_t) -1;
  }

  cvxif_t()
  {
  }

  void raise_exception(insn_t insn, reg_t exc_index)
  {
    switch (exc_index) {
      case CAUSE_MISALIGNED_FETCH:
        throw trap_instruction_address_misaligned((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_FETCH_ACCESS:
        throw trap_instruction_access_fault((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_BREAKPOINT:
        throw trap_breakpoint((p ? p->get_state()->v : false), 1);
      case CAUSE_MISALIGNED_LOAD:
        // Use 0x1 as perfectly unaligned address;-)
        throw trap_load_address_misaligned((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_LOAD_ACCESS:
        // Use 0x1 as invalid address.
        throw trap_load_access_fault((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_MISALIGNED_STORE:
        // Use 0x1 as perfectly unaligned address;-)
        throw trap_store_address_misaligned((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_STORE_ACCESS:
        // Use 0x1 as invalid address.
        throw trap_store_access_fault((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_USER_ECALL:
        throw trap_user_ecall();
      case CAUSE_SUPERVISOR_ECALL:
        throw trap_supervisor_ecall();
      case CAUSE_VIRTUAL_SUPERVISOR_ECALL:
        throw trap_virtual_supervisor_ecall();
      case CAUSE_MACHINE_ECALL:
        throw trap_machine_ecall();
      case CAUSE_FETCH_PAGE_FAULT:
        throw trap_instruction_page_fault((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_LOAD_PAGE_FAULT:
        // Use 0x1 as always-faulting address.
        throw trap_load_page_fault((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_STORE_PAGE_FAULT:
        // Use 0x1 as always-faulting address.
        throw trap_store_page_fault((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_FETCH_GUEST_PAGE_FAULT:
        throw trap_instruction_guest_page_fault(0, 0, 0);
      case CAUSE_LOAD_GUEST_PAGE_FAULT:
        throw trap_load_guest_page_fault(0, 0, 0);
      case CAUSE_VIRTUAL_INSTRUCTION:
        throw trap_virtual_instruction(0);
      case CAUSE_STORE_GUEST_PAGE_FAULT:
        throw trap_store_guest_page_fault(0, 0, 0);
      default:
        throw trap_unknown_instruction(exc_index, (reg_t)0);
    }
  }

  // Define templates of new instructions.
  customX(0)
  customX(1)
  customX(2)
  customX(3)

  // Set instruction handlers for customN opcode patterns.
  // NOTE: This method may need revisiting if multiple custom extensions are to be loaded
  //       simultaneously in the future.
  std::vector<insn_desc_t> get_instructions()
  {
    std::vector<insn_desc_t> insns;
    insns.push_back((insn_desc_t){0x0b, 0x7f, &::illegal_instruction, &::illegal_instruction, &::illegal_instruction, &::illegal_instruction, &::illegal_instruction, &::illegal_instruction, &::illegal_instruction, c0});
    insns.push_back((insn_desc_t){0x2b, 0x7f, &::illegal_instruction, &::illegal_instruction, &::illegal_instruction, &::illegal_instruction, &::illegal_instruction, &::illegal_instruction, &::illegal_instruction, c1});
    insns.push_back((insn_desc_t){0x5b, 0x7f, &::illegal_instruction, &::illegal_instruction, &::illegal_instruction, &::illegal_instruction, &::illegal_instruction, &::illegal_instruction, &::illegal_instruction, c2});
    insns.push_back((insn_desc_t){0x7b, 0x7f, &c3, &c3, &c3, &c3, &c3, &c3, &c3, c3});
    return insns;
  }

private:
  // State variables go here.
};

REGISTER_EXTENSION(cvxif, []() { return new cvxif_t; })
