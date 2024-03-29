/*
 * Copyright 2018 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// CVA6 class extend from riscv-dv class for all load/store instruction stream

class cva6_load_store_base_instr_stream_c extends riscv_load_store_base_instr_stream;

    cva6_instr_gen_config_c              cfg_cva6;                 // Configuration class handle

  `uvm_object_utils(cva6_load_store_base_instr_stream_c)

  function new(string name = "");
    super.new(name);
  endfunction

  // Generate each load/store instruction
  virtual function void gen_load_store_instr();
    bit enable_compressed_load_store, enable_zcb;
    riscv_instr instr;
    if(avail_regs.size() > 0) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(avail_regs,
                                         unique{avail_regs};
                                         avail_regs[0] inside {[S0 : A5]};
                                         foreach(avail_regs[i]) {
                                           !(avail_regs[i] inside {cfg_cva6.reserved_regs, reserved_rd});
                                         },
                                         "Cannot randomize avail_regs")
    end
    //cast riscv cfg into cva6 cfg
    `DV_CHECK_FATAL($cast(cfg_cva6, cfg), "Could not cast cfg into cfg_cva6")
    if ((rs1_reg inside {[S0 : A5], SP}) && !cfg_cva6.disable_compressed_instr) begin
      enable_compressed_load_store = 1;
    end
    if ((RV32C inside {riscv_instr_pkg::supported_isa}) && cfg_cva6.enable_zcb_extension) begin
      enable_zcb = 1;
    end
    foreach(addr[i]) begin
      // Assign the allowed load/store instructions based on address alignment
      // This is done separately rather than a constraint to improve the randomization performance
      allowed_instr = {LB, LBU, SB};
      if((offset[i] inside {[0:2]}) && enable_compressed_load_store &&
        enable_zcb && rs1_reg != SP) begin
        `uvm_info(`gfn, "Add Zcb byte load/store to allowed instr", UVM_LOW)
        allowed_instr = {C_LBU, C_SB};
      end
      if (!cfg_cva6.enable_unaligned_load_store) begin
        if (addr[i][0] == 1'b0) begin
          allowed_instr = {LH, LHU, SH, allowed_instr};
          if(((offset[i] == 0) || (offset[i] == 2)) && enable_compressed_load_store &&
            enable_zcb && rs1_reg != SP) begin
            `uvm_info(`gfn, "Add Zcb half-word load/store to allowed instr", UVM_LOW)
            allowed_instr = {C_LHU, C_LH, C_SH};
          end
        end
        if (addr[i] % 4 == 0) begin
          allowed_instr = {LW, SW, allowed_instr};
          if (cfg_cva6.enable_floating_point) begin
            allowed_instr = {FLW, FSW, allowed_instr};
          end
          if((offset[i] inside {[0:127]}) && (offset[i] % 4 == 0) &&
             (RV32C inside {riscv_instr_pkg::supported_isa}) &&
             enable_compressed_load_store) begin
            if (rs1_reg == SP) begin
              `uvm_info(`gfn, "Add LWSP/SWSP to allowed instr", UVM_LOW)
              allowed_instr = {C_LWSP, C_SWSP};
            end else begin
              allowed_instr = {C_LW, C_SW, allowed_instr};
              if (cfg_cva6.enable_floating_point && (RV32FC inside {supported_isa})) begin
                allowed_instr = {C_FLW, C_FSW, allowed_instr};
              end
            end
          end
        end
        if ((XLEN >= 64) && (addr[i] % 8 == 0)) begin
          allowed_instr = {LWU, LD, SD, allowed_instr};
          if (cfg_cva6.enable_floating_point && (RV32D inside {supported_isa})) begin
            allowed_instr = {FLD, FSD, allowed_instr};
          end
          if((offset[i] inside {[0:255]}) && (offset[i] % 8 == 0) &&
             (RV64C inside {riscv_instr_pkg::supported_isa} &&
             enable_compressed_load_store)) begin
            if (rs1_reg == SP) begin
              allowed_instr = {C_LDSP, C_SDSP};
            end else begin
              allowed_instr = {C_LD, C_SD, allowed_instr};
              if (cfg_cva6.enable_floating_point && (RV32DC inside {supported_isa})) begin
                allowed_instr = {C_FLD, C_FSD, allowed_instr};
              end
            end
          end
        end
      end else begin // unaligned load/store
        allowed_instr = {LW, SW, LH, LHU, SH, allowed_instr};
        // Compressed load/store still needs to be aligned
        if ((offset[i] inside {[0:127]}) && (offset[i] % 4 == 0) &&
            (RV32C inside {riscv_instr_pkg::supported_isa}) &&
            enable_compressed_load_store) begin
            if (rs1_reg == SP) begin
              allowed_instr = {C_LWSP, C_SWSP};
            end else begin
              allowed_instr = {C_LW, C_SW, allowed_instr};
            end
        end
        if (XLEN >= 64) begin
          allowed_instr = {LWU, LD, SD, allowed_instr};
          if ((offset[i] inside {[0:255]}) && (offset[i] % 8 == 0) &&
              (RV64C inside {riscv_instr_pkg::supported_isa}) &&
              enable_compressed_load_store) begin
              if (rs1_reg == SP) begin
                allowed_instr = {C_LWSP, C_SWSP};
              end else begin
                allowed_instr = {C_LD, C_SD, allowed_instr};
              end
           end
        end
      end
      instr = riscv_instr::get_load_store_instr(allowed_instr);
      instr.has_rs1 = 0;
      instr.has_imm = 0;
      randomize_gpr(instr);
      instr.rs1 = rs1_reg;
      instr.imm_str = $sformatf("%0d", $signed(offset[i]));
      instr.process_load_store = 0;
      instr_list.push_back(instr);
      load_store_instr.push_back(instr);
    end
  endfunction

endclass

// A single load/store instruction
class cva6_single_load_store_instr_stream_c extends cva6_load_store_base_instr_stream_c;

  constraint legal_c {
    num_load_store == 1;
    num_mixed_instr < 5;
  }

  `uvm_object_utils(cva6_single_load_store_instr_stream_c)
  `uvm_object_new

endclass

// Back to back load/store instructions
class cva6_load_store_stress_instr_stream_c extends cva6_load_store_base_instr_stream_c;

  int unsigned max_instr_cnt = 30;
  int unsigned min_instr_cnt = 10;

  constraint legal_c {
    num_load_store inside {[min_instr_cnt:max_instr_cnt]};
    num_mixed_instr == 0;
  }

  `uvm_object_utils(cva6_load_store_stress_instr_stream_c)
  `uvm_object_new

endclass


// Back to back load/store instructions
class cva6_load_store_shared_mem_stream_c extends cva6_load_store_stress_instr_stream_c;

  `uvm_object_utils(cva6_load_store_shared_mem_stream_c)
  `uvm_object_new

  function void pre_randomize();
    load_store_shared_memory = 1;
    super.pre_randomize();
  endfunction

endclass

// Random load/store sequence
// A random mix of load/store instructions and other instructions
class cva6_load_store_rand_instr_stream_c extends cva6_load_store_base_instr_stream_c;

  constraint legal_c {
    num_load_store inside {[10:30]};
    num_mixed_instr inside {[10:30]};
  }

  `uvm_object_utils(cva6_load_store_rand_instr_stream_c)
  `uvm_object_new

endclass

// Use a small set of GPR to create various WAW, RAW, WAR hazard scenario
class cva6_hazard_instr_stream_c extends cva6_load_store_base_instr_stream_c;

  int unsigned num_of_avail_regs = 6;

  constraint legal_c {
    num_load_store inside {[10:30]};
    num_mixed_instr inside {[10:30]};
  }

  `uvm_object_utils(cva6_hazard_instr_stream_c)
  `uvm_object_new

  function void pre_randomize();
    avail_regs = new[num_of_avail_regs];
    super.pre_randomize();
  endfunction

endclass

// Use a small set of address to create various load/store hazard sequence
// This instruction stream focus more on hazard handling of load store unit.
class cva6_load_store_hazard_instr_stream_c extends cva6_load_store_base_instr_stream_c;

  rand int hazard_ratio;

  constraint hazard_ratio_c {
    hazard_ratio inside {[20:100]};
  }

  constraint legal_c {
    num_load_store inside {[10:20]};
    num_mixed_instr inside {[1:7]};
  }

  `uvm_object_utils(cva6_load_store_hazard_instr_stream_c)
  `uvm_object_new

  virtual function void randomize_offset();
    int offset_, addr_;
    offset = new[num_load_store];
    addr = new[num_load_store];
    for (int i = 0; i < num_load_store; i++) begin
      if ((i > 0) && ($urandom_range(0, 100) < hazard_ratio)) begin
        offset[i] = offset[i-1];
        addr[i] = addr[i-1];
      end else begin
        if (!std::randomize(offset_, addr_) with {
          if (locality == NARROW) {
            soft offset_ inside {[-16:16]};
          } else if (locality == HIGH) {
            soft offset_ inside {[-64:64]};
          } else if (locality == MEDIUM) {
            soft offset_ inside {[-256:256]};
          } else if (locality == SPARSE) {
            soft offset_ inside {[-2048:2047]};
          }
          addr_ == base + offset_;
          addr_ inside {[0 : max_load_store_offset - 1]};
        }) begin
          `uvm_fatal(`gfn, "Cannot randomize load/store offset")
        end
        offset[i] = offset_;
        addr[i] = addr_;
      end
    end
  endfunction : randomize_offset

endclass

// Back to back access to multiple data pages
// This is useful to test data TLB switch and replacement
class cva6_multi_page_load_store_instr_stream_c extends riscv_mem_access_stream;

  riscv_load_store_stress_instr_stream load_store_instr_stream[];
  rand int unsigned num_of_instr_stream;
  rand int unsigned data_page_id[];
  rand riscv_reg_t  rs1_reg[];

  constraint default_c {
    foreach(data_page_id[i]) {
      data_page_id[i] < max_data_page_id;
    }
    data_page_id.size() == num_of_instr_stream;
    rs1_reg.size() == num_of_instr_stream;
    unique {rs1_reg};
    foreach(rs1_reg[i]) {
      !(rs1_reg[i] inside {cfg.reserved_regs, ZERO});
    }
  }

  constraint page_c {
    solve num_of_instr_stream before data_page_id;
    num_of_instr_stream inside {[1 : max_data_page_id]};
    unique {data_page_id};
  }

  // Avoid accessing a large number of pages because we may run out of registers for rs1
  // Each page access needs a reserved register as the base address of load/store instruction
  constraint reasonable_c {
    num_of_instr_stream inside {[2:8]};
  }

  `uvm_object_utils(cva6_multi_page_load_store_instr_stream_c)
  `uvm_object_new

  // Generate each load/store seq, and mix them together
  function void post_randomize();
    load_store_instr_stream = new[num_of_instr_stream];
    foreach(load_store_instr_stream[i]) begin
      load_store_instr_stream[i] = riscv_load_store_stress_instr_stream::type_id::
                                   create($sformatf("load_store_instr_stream_%0d", i));
      load_store_instr_stream[i].min_instr_cnt = 5;
      load_store_instr_stream[i].max_instr_cnt = 10;
      load_store_instr_stream[i].cfg = cfg;
      load_store_instr_stream[i].hart = hart;
      load_store_instr_stream[i].sp_c.constraint_mode(0);
      // Make sure each load/store sequence doesn't override the rs1 of other sequences.
      foreach(rs1_reg[j]) begin
        if(i != j) begin
          load_store_instr_stream[i].reserved_rd =
            {load_store_instr_stream[i].reserved_rd, rs1_reg[j]};
        end
      end
      `DV_CHECK_RANDOMIZE_WITH_FATAL(load_store_instr_stream[i],
                                     rs1_reg == local::rs1_reg[i];
                                     data_page_id == local::data_page_id[i];,
                                     "Cannot randomize load/store instruction")
      // Mix the instruction stream of different page access, this could trigger the scenario of
      // frequent data TLB switch
      if(i == 0) begin
        instr_list = load_store_instr_stream[i].instr_list;
      end else begin
        mix_instr_stream(load_store_instr_stream[i].instr_list);
      end
    end
  endfunction

endclass

// Access the different locations of the same memory regions
class cva6_mem_region_stress_test_c extends cva6_multi_page_load_store_instr_stream_c;

  `uvm_object_utils(cva6_mem_region_stress_test_c)
  `uvm_object_new

  constraint page_c {
    num_of_instr_stream inside {[2:5]};
    foreach (data_page_id[i]) {
      if (i > 0) {
        data_page_id[i] == data_page_id[i-1];
      }
    }
  }

endclass

// Random load/store sequence to full address range
// The address range is not preloaded with data pages, use store instruction to initialize first
class cva6_load_store_rand_addr_instr_stream_c extends cva6_load_store_base_instr_stream_c;

  rand bit [XLEN-1:0] addr_offset;

  // Find an unused 4K page from address 1M onward
  constraint addr_offset_c {
    |addr_offset[XLEN-1:20] == 1'b1;
    // TODO(taliu) Support larger address range
    addr_offset[XLEN-1:31] == 0;
    addr_offset[11:0] == 0;
  }

  constraint legal_c {
    num_load_store inside {[5:10]};
    num_mixed_instr inside {[5:10]};
  }

  `uvm_object_utils(cva6_load_store_rand_addr_instr_stream_c)

   virtual function void randomize_offset();
    int offset_, addr_;
    offset = new[num_load_store];
    addr = new[num_load_store];
    for (int i=0; i<num_load_store; i++) begin
      if (!std::randomize(offset_) with {
          offset_ inside {[-2048:2047]};
        }
      ) begin
        `uvm_fatal(`gfn, "Cannot randomize load/store offset")
      end
      offset[i] = offset_;
      addr[i] = addr_offset + offset_;
    end
  endfunction `uvm_object_new

  virtual function void add_rs1_init_la_instr(riscv_reg_t gpr, int id, int base = 0);
    riscv_instr instr[$];
    riscv_pseudo_instr li_instr;
    riscv_instr store_instr;
    riscv_instr add_instr;
    int min_offset[$];
    int max_offset[$];
    min_offset = offset.min();
    max_offset = offset.max();
    // Use LI to initialize the address offset
    li_instr = riscv_pseudo_instr::type_id::create("li_instr");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(li_instr,
       pseudo_instr_name == LI;
       rd inside {cfg.gpr};
       rd != gpr;
    )
    li_instr.imm_str = $sformatf("0x%0x", addr_offset);
    // Add offset to the base address
    add_instr = riscv_instr::get_instr(ADD);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(add_instr,
       rs1 == gpr;
       rs2 == li_instr.rd;
       rd  == gpr;
    )
    instr.push_back(li_instr);
    instr.push_back(add_instr);
    // Create SW instruction template
    store_instr = riscv_instr::get_instr(SB);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(store_instr,
       instr_name == SB;
       rs1 == gpr;
    )
    // Initialize the location which used by load instruction later
    foreach (load_store_instr[i]) begin
      if (load_store_instr[i].category == LOAD) begin
        riscv_instr store;
        store = riscv_instr::type_id::create("store");
        store.copy(store_instr);
        store.rs2 = riscv_reg_t'(i % 32);
        store.imm_str = load_store_instr[i].imm_str;
        // TODO: C_FLDSP is in both rv32 and rv64 ISA
        case (load_store_instr[i].instr_name) inside
          LB, LBU : store.instr_name = SB;
          LH, LHU : store.instr_name = SH;
          LW, C_LW, C_LWSP, FLW, C_FLW, C_FLWSP : store.instr_name = SW;
          LD, C_LD, C_LDSP, FLD, C_FLD, LWU     : store.instr_name = SD;
          default : `uvm_fatal(`gfn, $sformatf("Unexpected op: %0s",
                                               load_store_instr[i].convert2asm()))
        endcase
        instr.push_back(store);
      end
    end
    instr_list = {instr, instr_list};
    super.add_rs1_init_la_instr(gpr, id, 0);
  endfunction

endclass
