//
// -------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2010 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2010 AMD
// Copyright 2015-2018 NVIDIA Corporation
//    All Rights Reserved Worldwide
// 
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
// 

//------------------------------------------------------------------------------
// Class -- NODOCS -- uvm_reg_mem_built_in_seq
//
// Sequence that executes a user-defined selection
// of pre-defined register and memory test sequences.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto E.8.1
class uvm_reg_mem_built_in_seq extends uvm_reg_sequence #(uvm_sequence #(uvm_reg_item));

   `uvm_object_utils(uvm_reg_mem_built_in_seq)

   // @uvm-ieee 1800.2-2017 auto E.8.3.1
   function new(string name="uvm_reg_mem_built_in_seq");
     super.new(name);
   endfunction

   // Variable -- NODOCS -- model
   //
   // The block to be tested. Declared in the base class.
   //
   //| uvm_reg_block model; 


   // Variable -- NODOCS -- tests
   //
   // The pre-defined test sequences to be executed.
   //
   bit [63:0] tests = UVM_DO_ALL_REG_MEM_TESTS;


   // Task -- NODOCS -- body
   //
   // Executes any or all the built-in register and memory sequences.
   // Do not call directly. Use seq.start() instead.
   
   // @uvm-ieee 1800.2-2017 auto E.8.3.2
   virtual task body();

      if (model == null) begin
         `uvm_error("uvm_reg_mem_built_in_seq", "Not block or system specified to run sequence on")
         return;
      end

      uvm_report_info("START_SEQ",{"\n\nStarting ",get_name()," sequence...\n"},UVM_LOW);
      
      if (tests & UVM_DO_REG_HW_RESET &&
          uvm_resource_db#(bit)::get_by_name({"REG::",model.get_full_name()},
                                             "NO_REG_TESTS", 0) == null &&
          uvm_resource_db#(bit)::get_by_name({"REG::",model.get_full_name()},
                                             "NO_REG_HW_RESET_TEST", 0) == null ) begin
        uvm_reg_hw_reset_seq seq = uvm_reg_hw_reset_seq::type_id::create("reg_hw_reset_seq");
        seq.model = model;
        seq.start(null,this);
        `uvm_info("FINISH_SEQ",{"Finished ",seq.get_name()," sequence."},UVM_LOW)
      end

      if (tests & UVM_DO_REG_BIT_BASH &&
          uvm_resource_db#(bit)::get_by_name({"REG::",model.get_full_name()},
                                             "NO_REG_TESTS", 0) == null &&
          uvm_resource_db#(bit)::get_by_name({"REG::",model.get_full_name()},
                                             "NO_REG_BIT_BASH_TEST", 0) == null ) begin
        uvm_reg_bit_bash_seq seq = uvm_reg_bit_bash_seq::type_id::create("reg_bit_bash_seq");
        seq.model = model;
        seq.start(null,this);
        `uvm_info("FINISH_SEQ",{"Finished ",seq.get_name()," sequence."},UVM_LOW)
      end

      if (tests & UVM_DO_REG_ACCESS &&
          uvm_resource_db#(bit)::get_by_name({"REG::",model.get_full_name()},
                                             "NO_REG_TESTS", 0) == null &&
          uvm_resource_db#(bit)::get_by_name({"REG::",model.get_full_name()},
                                             "NO_REG_ACCESS_TEST", 0) == null ) begin
        uvm_reg_access_seq seq = uvm_reg_access_seq::type_id::create("reg_access_seq");
        seq.model = model;
        seq.start(null,this);
        `uvm_info("FINISH_SEQ",{"Finished ",seq.get_name()," sequence."},UVM_LOW)
      end

      if (tests & UVM_DO_MEM_ACCESS &&
          uvm_resource_db#(bit)::get_by_name({"REG::",model.get_full_name()},
                                             "NO_REG_TESTS", 0) == null &&
          uvm_resource_db#(bit)::get_by_name({"REG::",model.get_full_name()},
                                             "NO_MEM_TESTS", 0) == null &&
          uvm_resource_db#(bit)::get_by_name({"REG::",model.get_full_name()},
                                             "NO_MEM_ACCESS_TEST", 0) == null ) begin
        uvm_mem_access_seq seq = uvm_mem_access_seq::type_id::create("mem_access_seq");
        seq.model = model;
        seq.start(null,this);
        `uvm_info("FINISH_SEQ",{"Finished ",seq.get_name()," sequence."},UVM_LOW)
      end

      if (tests & UVM_DO_SHARED_ACCESS &&
          uvm_resource_db#(bit)::get_by_name({"REG::",model.get_full_name()},
                                             "NO_REG_TESTS", 0) == null &&
          uvm_resource_db#(bit)::get_by_name({"REG::",model.get_full_name()},
                                             "NO_REG_SHARED_ACCESS_TEST", 0) == null ) begin
        uvm_reg_mem_shared_access_seq seq = uvm_reg_mem_shared_access_seq::type_id::create("shared_access_seq");
        seq.model = model;
        seq.start(null,this);
        `uvm_info("FINISH_SEQ",{"Finished ",seq.get_name()," sequence."},UVM_LOW)
      end

      if (tests & UVM_DO_MEM_WALK &&
          uvm_resource_db#(bit)::get_by_name({"REG::",model.get_full_name()},
                                             "NO_REG_TESTS", 0) == null &&
          uvm_resource_db#(bit)::get_by_name({"REG::",model.get_full_name()},
                                             "NO_MEM_WALK_TEST", 0) == null ) begin
        uvm_mem_walk_seq seq = uvm_mem_walk_seq::type_id::create("mem_walk_seq");
        seq.model = model;
        seq.start(null,this);
        `uvm_info("FINISH_SEQ",{"Finished ",seq.get_name()," sequence."},UVM_LOW)
      end

   endtask: body

endclass: uvm_reg_mem_built_in_seq
