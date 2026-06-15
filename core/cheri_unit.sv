// Copyright 2022 Bruno Sá and Zero-Day Labs.
// Copyright 2025 Capabilities Limited.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions ansd limitations under the License.
//
// Author: Bruno Sá <bruno.vilaca.sa@gmail.com>
// Acknowledges: Technology Inovation Institute (TII)
//
// Date: 01.01.2025
// Description: CVA6 CHERI Logic Unit

typedef struct packed {
  logic tag;
  logic seal;
  logic bounds;
} cap_check_select_t;

module cheri_unit
  import cva6_cheri_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type fu_data_t = logic,
    parameter type exception_t = logic
) (
    input  logic     clk_i,         // Clock
    input  logic     rst_ni,        // Asynchronous reset active low
    input  logic     v_i,
    input  fu_data_t fu_data_i,
    input  logic     clu_valid_i,
    input  addrw_t   alu_result_i,
    output cap_reg_t clu_result_o   // Return resulting cap
);
  // operand a decode fields
  cap_reg_t operand_a;
  addrw_t operand_a_base;
  addrwe_t operand_a_top;
  addrw_t operand_a_length;
  addrw_t operand_a_address;
  logic operand_a_is_sealed;
  cap_meta_data_t op_a_meta_info;
  logic operand_a_hperms_malformed;
  logic operand_a_bounds_malformed;

  // operand b decode fields
  cap_reg_t operand_b;
  addrw_t operand_b_base;
  addrwe_t operand_b_top;
  addrw_t operand_b_address;
  logic operand_b_is_sealed;
  cap_meta_data_t op_b_meta_info;
  logic operand_b_hperms_malformed;
  logic operand_b_bounds_malformed;

  // Common operations signals
  // Set address operations signals
  addrw_t address;
  cap_reg_t res_set_addr;

  // Tag-clearing check signals
  cap_check_select_t operand_a_violations;
  cap_check_select_t check_operand_a_violations;

  // Output signals
  cap_reg_t clu_result;

  // -----------
  // CHERI ALU main logic circuit
  // -----------
  capw_t cap_mem;
  cap_mem_t cap_mem_null;
  cap_reg_t tmp_cap, req_cap;
  addrwe_t tmp_length;
  always_comb begin
    // exceptions signals reset
    check_operand_a_violations = {1'b0, 1'b0, 1'b0};

    // Set address operation reset signals
    address                    = '{default: 0};

    // Output reset values
    clu_result                 = REG_NULL_CAP;

    // Auxiliar signals
    tmp_cap                    = REG_NULL_CAP;
    cap_mem                    = '0;
    cap_mem_null               = MEM_NULL_CAP;
    tmp_length                 = '0;

    unique case (fu_data_i.operation)
      // AUIPCC
      ariane_pkg::AUIPCC: begin
        address    = alu_result_i;
        clu_result = res_set_addr;
      end
      // CAndPerm
      ariane_pkg::ACPERM: begin
        automatic cap_report_perms_t new_perms;
        check_operand_a_violations.seal = 1'b1;
        tmp_cap = operand_a;
        new_perms = hperms_and_uperms_to_report_perms(operand_a.hperms, operand_a.uperms,
                                                      operand_a_hperms_malformed);
        new_perms &= cap_report_perms_t'(operand_b_address);
        tmp_cap.uperms = new_perms.uperms;
        tmp_cap.hperms = legalize_arch_perms(report_perms_to_hperms(new_perms));
        if (!tmp_cap.hperms.permit_execute) tmp_cap.flags.int_mode = 1'b0;
        clu_result = tmp_cap;
      end
      // CTestSubset
      ariane_pkg::CBLD, ariane_pkg::SCSS: begin
        tmp_cap = operand_b;
        tmp_cap.tag = 1'b1;
        if (fu_data_i.operation == ariane_pkg::SCSS) begin
          if (operand_a.tag != operand_b.tag) begin
            tmp_cap.tag = 1'b0;
          end
        end else begin  // CBLD
          if (!operand_a.tag) begin
            tmp_cap.tag = 1'b0;
          end
          if (operand_a_is_sealed) begin
            tmp_cap.tag = 1'b0;
          end
        end
        if (operand_b_base < operand_a_base) begin
          tmp_cap.tag = 1'b0;
        end
        if (operand_b_top > operand_a_top) begin
          tmp_cap.tag = 1'b0;
        end
        if ((operand_a.uperms & operand_b.uperms) != operand_b.uperms) begin
          tmp_cap.tag = 1'b0;
        end
        if ((operand_a.hperms & operand_b.hperms) != operand_b.hperms) begin
          tmp_cap.tag = 1'b0;
        end
        if (operand_a_bounds_malformed | operand_b_bounds_malformed) begin
          tmp_cap.tag = 1'b0;
        end
        if (operand_a_hperms_malformed | operand_b_hperms_malformed) begin
          tmp_cap.tag = 1'b0;
        end
        if(operand_a.res_lo != 0 | operand_a.res_hi != 0 | operand_b.res_lo != 0 | operand_b.res_hi != 0) begin
          tmp_cap.tag = 1'b0;
        end
        if (fu_data_i.operation == ariane_pkg::CBLD) clu_result = tmp_cap;
        // fu_data_i.operation == ariane_pkg::SCSS
        else
          clu_result = ariane_pkg::x_to_reg({{CVA6Cfg.XLEN - 1{1'b0}}, tmp_cap.tag});
      end
      // CGetBase
      ariane_pkg::GCBASE: begin
        clu_result = ariane_pkg::x_to_reg(operand_a_bounds_malformed ? '0 : operand_a_base);
      end
      // CGetFlags
      ariane_pkg::GCMODE: begin
        clu_result = ariane_pkg::x_to_reg({{CVA6Cfg.XLEN - 1{1'b0}}, get_cap_reg_flags(operand_a)});
      end
      // CGetLength
      ariane_pkg::GCLEN: begin
        clu_result = ariane_pkg::x_to_reg(operand_a_bounds_malformed ? '0 : operand_a_length);
      end
      // CGetHigh
      ariane_pkg::GCHI: begin
        cap_mem = cap_reg_to_cap_mem(operand_a);
        clu_result = ariane_pkg::x_to_reg(cap_mem[((CVA6Cfg.XLEN*2)-1):CVA6Cfg.XLEN]);
      end
      // CGetPerm
      ariane_pkg::GCPERM: begin
        clu_result = ariane_pkg::x_to_reg(
          {
            {CVA6Cfg.XLEN - $bits(cap_report_perms_t) {1'b0}},
            hperms_and_uperms_to_report_perms(
              operand_a.hperms, operand_a.uperms, operand_a_hperms_malformed
            )
          }
        );
      end
      // CGetTag
      ariane_pkg::GCTAG: begin
        clu_result = ariane_pkg::x_to_reg({{CVA6Cfg.XLEN - 1{1'b0}}, operand_a.tag});
      end
      // CGetType
      ariane_pkg::GCTYPE: begin
        clu_result = ariane_pkg::x_to_reg({{CVA6Cfg.XLEN - 1{1'b0}}, operand_a.otype});
      end
      // CIncOffset and CIncOffsetImm
      // TODO-cheri(ninolomata): use ALU to calculate address
      ariane_pkg::CADD: begin
        check_operand_a_violations.seal = 1'b1;
        address                         = operand_a_address + operand_b_address;
        clu_result                      = res_set_addr;
      end
      // CMV
      ariane_pkg::CMV: begin
        clu_result = operand_a;
      end
      // CSealEntry
      ariane_pkg::SENTRY: begin
        clu_result = operand_a;
        check_operand_a_violations.seal = 1'b1;
        clu_result.otype = SENTRY_CAP;
      end
      // CSetAddr
      ariane_pkg::SCADDR: begin
        check_operand_a_violations.seal = 1'b1;
        address                         = operand_b.addr;
        clu_result                      = res_set_addr;
      end
      // CSetBounds, CSetBoundsExact, CSetBoundsImm,
      // CRepresentableAlignmentMask
      ariane_pkg::SCBNDSR, ariane_pkg::SCBNDS, ariane_pkg::CRAM: begin
        automatic cap_reg_set_bounds_ret_t res_set_bounds;
        res_set_bounds =
            set_cap_reg_bounds(operand_a, operand_a_address, {1'b0, operand_b_address});
        check_operand_a_violations.tag = 1'b1;
        check_operand_a_violations.seal = 1'b1;
        check_operand_a_violations.bounds = 1'b1;
        if (fu_data_i.operation == ariane_pkg::CRAM) begin
          clu_result = ariane_pkg::x_to_reg(res_set_bounds.mask);
        end else begin
          clu_result = res_set_bounds.cap;
        end
        // If the result is inexact, and needed to be
        if ((!res_set_bounds.exact && fu_data_i.operation == ariane_pkg::SCBNDS)) begin
          clu_result.tag = 1'b0;
        end
      end
      // CSetEqualExact
      ariane_pkg::SCEQ: begin
        clu_result = ariane_pkg::x_to_reg(
          {
            {CVA6Cfg.XLEN - 1{1'b0}},
            (cap_reg_to_cap_mem(operand_a) == cap_reg_to_cap_mem(operand_b)) ? 1'b1 : 1'b0
          }
        );
      end
      // CSetFlags
      ariane_pkg::SCMODE: begin
        check_operand_a_violations.seal = 1'b1;
        clu_result = (operand_a_hperms_malformed) ? operand_a :
            set_cap_reg_flags(operand_a, operand_b.addr[0]);
      end
      // CSetHigh
      ariane_pkg::SCHI: begin
        cap_mem = cap_reg_to_cap_mem(operand_a);
        cap_mem[((CVA6Cfg.XLEN*2)-1):CVA6Cfg.XLEN] = operand_b[XLEN-1:0];
        clu_result = cap_mem_to_cap_reg(cap_mem);
        clu_result.tag = 1'b0;
      end
      default: ;  // default case to suppress unique warning
    endcase

    // Update destination register

  end

  // ----------------
  // Decode Cap Operands Fields
  // ----------------
  always_comb begin
    operand_a = fu_data_i.operand_a;
    operand_b = fu_data_i.operand_b;
    // Decode capability operand a fields
    op_a_meta_info = get_cap_reg_meta_data(operand_a);
    operand_a_address = operand_a.addr;
    operand_a_base = get_cap_reg_base(operand_a, op_a_meta_info);
    operand_a_top = get_cap_reg_top(operand_a, op_a_meta_info);
    operand_a_length = get_cap_reg_length(operand_a, op_a_meta_info);
    operand_a_is_sealed = (operand_a.otype != UNSEALED_CAP);
    operand_a_hperms_malformed = (operand_a.hperms != legalize_arch_perms(operand_a.hperms)) |
        (!operand_a.hperms.permit_execute & operand_a.flags.int_mode);
    operand_a_bounds_malformed = !are_cap_reg_bounds_valid(operand_a, op_a_meta_info);
    // Decode capability operand b fields
    operand_b_address = operand_b.addr;
    op_b_meta_info = get_cap_reg_meta_data(operand_b);
    operand_b_base = get_cap_reg_base(operand_b, op_b_meta_info);
    operand_b_top = get_cap_reg_top(operand_b, op_b_meta_info);
    operand_b_bounds_malformed = !are_cap_reg_bounds_valid(operand_b, op_b_meta_info);
    operand_b_is_sealed = (operand_b.otype != UNSEALED_CAP);
    operand_b_hperms_malformed = (operand_b.hperms != legalize_arch_perms(operand_b.hperms)) |
        (!operand_b.hperms.permit_execute & operand_b.flags.int_mode);
  end

  // ----------------
  // Common Operations
  // 1. Set address operation
  // 2. Set offset operation
  // ----------------
  always_comb begin
    res_set_addr = set_cap_reg_address(operand_a, address, op_a_meta_info);
  end

  // ----------------
  // Operands Exception Control Checks
  // ----------------
  always_comb begin
    operand_a_violations = {1'b0, 1'b0, 1'b0};
    // Operand a capability checks
    if (!is_cap_reg_valid(fu_data_i.operand_a)) begin
      operand_a_violations.tag = 1'b1;
    end

    if (operand_a_is_sealed) begin
      operand_a_violations.seal = 1'b1;
    end

    if (operand_a_address < operand_a_base) begin
      operand_a_violations.bounds = 1'b1;
    end

    if ((operand_a_address + $unsigned(operand_b_address)) > operand_a_top) begin
      operand_a_violations.bounds = 1'b1;
    end
  end

  // ------------------------
  // CHERI Output Logic
  // ------------------------
  always_comb begin : cheri_output_logic
    clu_result_o = clu_result;
    // Clear result capability tag if there was any violations
    if ((operand_a_violations & check_operand_a_violations) != {1'b0, 1'b0, 1'b0}) begin
      clu_result_o.tag = 1'b0;
    end
  end
endmodule
