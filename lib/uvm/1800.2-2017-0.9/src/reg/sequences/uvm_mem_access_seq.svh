// 
// -------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2004-2010 Synopsys, Inc.
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

//
// TITLE -- NODOCS -- Memory Access Test Sequence
//

//
// class -- NODOCS -- uvm_mem_single_access_seq
//
// Verify the accessibility of a memory
// by writing through its default address map
// then reading it via the backdoor, then reversing the process,
// making sure that the resulting value matches the written value.
//
// If bit-type resource named
// "NO_REG_TESTS", "NO_MEM_TESTS", or "NO_MEM_ACCESS_TEST"
// in the "REG::" namespace
// matches the full name of the memory,
// the memory is not tested.
//
//| uvm_resource_db#(bit)::set({"REG::",regmodel.blk.mem0.get_full_name()},
//|                            "NO_MEM_TESTS", 1, this);
//
// Memories without an available backdoor
// cannot be tested.
//
// The DUT should be idle and not modify the memory during this test.
//

// @uvm-ieee 1800.2-2017 auto E.5.1.1
class uvm_mem_single_access_seq extends uvm_reg_sequence #(uvm_sequence #(uvm_reg_item));

   // Variable -- NODOCS -- mem
   //
   // The memory to be tested
   //
   uvm_mem mem;

   `uvm_object_utils(uvm_mem_single_access_seq)

   // @uvm-ieee 1800.2-2017 auto E.5.1.3
   function new(string name="uam_mem_single_access_seq");
     super.new(name);
   endfunction

   virtual task body();
      string mode;
      uvm_reg_map maps[$];
      int n_bits;

      if (mem == null) begin
         `uvm_error("uvm_mem_access_seq", "No register specified to run sequence on")
         return;
      end

      // Memories with some attributes are not to be tested
      if (uvm_resource_db#(bit)::get_by_name({"REG::",mem.get_full_name()},
                                             "NO_REG_TESTS", 0) != null ||
          uvm_resource_db#(bit)::get_by_name({"REG::",mem.get_full_name()},
                                             "NO_MEM_TESTS", 0) != null ||
          uvm_resource_db#(bit)::get_by_name({"REG::",mem.get_full_name()},
                                             "NO_MEM_ACCESS_TEST", 0) != null)
         return;

      // Can only deal with memories with backdoor access
      if (mem.get_backdoor() == null && !mem.has_hdl_path()) begin
         `uvm_error("uvm_mem_access_seq", {"Memory '",mem.get_full_name(),
             "' does not have a backdoor mechanism available"})
         return;
      end

      n_bits = mem.get_n_bits();
      
      // Memories may be accessible from multiple physical interfaces (maps)
      mem.get_maps(maps);

      // Walk the memory via each map
      foreach (maps[j]) begin
         uvm_status_e status;
         uvm_reg_data_t  val, exp, v;
         
         `uvm_info("uvm_mem_access_seq", {"Verifying access of memory '",
             mem.get_full_name(),"' in map '", maps[j].get_full_name(),
             "' ..."}, UVM_LOW)

         mode = mem.get_access(maps[j]);
         
         // The access process is, for address k:
         // - Write random value via front door
         // - Read via backdoor and expect same random value if RW
         // - Write complement of random value via back door
         // - Read via front door and expect inverted random value
         for (int k = 0; k < mem.get_size(); k++) begin
            val = $random & uvm_reg_data_t'((1'b1<<n_bits)-1);
            if (n_bits > 32)
              val = uvm_reg_data_t'(val << 32) | $random;
            if (mode == "RO") begin
               mem.peek(status, k, exp);
               if (status != UVM_IS_OK) begin
                  `uvm_error("uvm_mem_access_seq", $sformatf("Status was %s when reading \"%s[%0d]\" through backdoor.",
                                              status.name(), mem.get_full_name(), k))
               end
            end
            else exp = val;
            
            mem.write(status, k, val, UVM_FRONTDOOR, maps[j], this);
            if (status != UVM_IS_OK) begin
               `uvm_error("uvm_mem_access_seq", $sformatf("Status was %s when writing \"%s[%0d]\" through map \"%s\".",
                                           status.name(), mem.get_full_name(), k, maps[j].get_full_name()))
            end
            #1;
            
            val = 'x;
            mem.peek(status, k, val);
            if (status != UVM_IS_OK) begin
               `uvm_error("uvm_mem_access_seq", $sformatf("Status was %s when reading \"%s[%0d]\" through backdoor.",
                                           status.name(), mem.get_full_name(), k))
            end
            else begin
               if (val !== exp) begin
                  `uvm_error("uvm_mem_access_seq", $sformatf("Backdoor \"%s[%0d]\" read back as 'h%h instead of 'h%h.",
                                              mem.get_full_name(), k, val, exp))
               end
            end
            
            exp = ~exp & ((1'b1<<n_bits)-1);
            mem.poke(status, k, exp);
            if (status != UVM_IS_OK) begin
               `uvm_error("uvm_mem_access_seq", $sformatf("Status was %s when writing \"%s[%0d-1]\" through backdoor.",
                                           status.name(), mem.get_full_name(), k))
            end
            
            mem.read(status, k, val, UVM_FRONTDOOR, maps[j], this);
            if (status != UVM_IS_OK) begin
               `uvm_error("uvm_mem_access_seq", $sformatf("Status was %s when reading \"%s[%0d]\" through map \"%s\".",
                                           status.name(), mem.get_full_name(), k, maps[j].get_full_name()))
            end
            else begin
               if (mode == "WO") begin
                  if (val !== '0) begin
                     `uvm_error("uvm_mem_access_seq", $sformatf("Front door \"%s[%0d]\" read back as 'h%h instead of 'h%h.",
                                                 mem.get_full_name(), k, val, 0))
                  end
               end
               else begin
                  if (val !== exp) begin
                     `uvm_error("uvm_mem_access_seq", $sformatf("Front door \"%s[%0d]\" read back as 'h%h instead of 'h%h.",
                                                 mem.get_full_name(), k, val, exp))
                  end
               end
            end
         end
      end
   endtask: body
endclass: uvm_mem_single_access_seq




//
// class -- NODOCS -- uvm_mem_access_seq
//
// Verify the accessibility of all memories in a block
// by executing the <uvm_mem_single_access_seq> sequence on
// every memory within it.
//
// If bit-type resource named
// "NO_REG_TESTS", "NO_MEM_TESTS", or "NO_MEM_ACCESS_TEST"
// in the "REG::" namespace
// matches the full name of the block,
// the block is not tested.
//
//| uvm_resource_db#(bit)::set({"REG::",regmodel.blk.get_full_name(),".*"},
//|                            "NO_MEM_TESTS", 1, this);
//

// @uvm-ieee 1800.2-2017 auto E.5.2.1
class uvm_mem_access_seq extends uvm_reg_sequence #(uvm_sequence #(uvm_reg_item));

   // Variable -- NODOCS -- model
   //
   // The block to be tested. Declared in the base class.
   //
   //| uvm_reg_block model; 


   // Variable -- NODOCS -- mem_seq
   //
   // The sequence used to test one memory
   //
   protected uvm_mem_single_access_seq mem_seq;

   `uvm_object_utils(uvm_mem_access_seq)

   // @uvm-ieee 1800.2-2017 auto E.5.2.3.1
   function new(string name="uvm_mem_access_seq");
     super.new(name);
   endfunction


   // @uvm-ieee 1800.2-2017 auto E.5.2.3.2
   virtual task body();

      if (model == null) begin
         `uvm_error("uvm_mem_access_seq", "No register model specified to run sequence on")
         return;
      end

      uvm_report_info("STARTING_SEQ",{"\n\nStarting ",get_name()," sequence...\n"},UVM_LOW);
      
      mem_seq = uvm_mem_single_access_seq::type_id::create("single_mem_access_seq");

      this.reset_blk(model);
      model.reset();

      do_block(model);
   endtask: body


   // Task -- NODOCS -- do_block
   //
   // Test all of the memories in a given ~block~
   //
   protected virtual task do_block(uvm_reg_block blk);
      uvm_mem mems[$];
      
      if (uvm_resource_db#(bit)::get_by_name({"REG::",blk.get_full_name()},
                                             "NO_REG_TESTS", 0) != null ||
          uvm_resource_db#(bit)::get_by_name({"REG::",blk.get_full_name()},
                                             "NO_MEM_TESTS", 0) != null ||
          uvm_resource_db#(bit)::get_by_name({"REG::",blk.get_full_name()},
                                             "NO_MEM_ACCESS_TEST", 0) != null )
         return;
      
      // Iterate over all memories, checking accesses
      blk.get_memories(mems, UVM_NO_HIER);
      foreach (mems[i]) begin
         // Registers with some attributes are not to be tested
         if (uvm_resource_db#(bit)::get_by_name({"REG::",mems[i].get_full_name()},
                                                "NO_REG_TESTS", 0) != null ||
             uvm_resource_db#(bit)::get_by_name({"REG::",mems[i].get_full_name()},
                                                "NO_MEM_TESTS", 0) != null ||
	     uvm_resource_db#(bit)::get_by_name({"REG::",mems[i].get_full_name()},
                                                "NO_MEM_ACCESS_TEST", 0) != null )
           continue;
         
         // Can only deal with memories with backdoor access
         if (mems[i].get_backdoor() == null &&
             !mems[i].has_hdl_path()) begin
            `uvm_warning("uvm_mem_access_seq", $sformatf("Memory \"%s\" does not have a backdoor mechanism available",
                                               mems[i].get_full_name()))
            continue;
         end
         
         mem_seq.mem = mems[i];
         mem_seq.start(null, this);
      end

      begin
         uvm_reg_block blks[$];
         
         blk.get_blocks(blks);
         foreach (blks[i]) begin
            do_block(blks[i]);
         end
      end
   endtask: do_block


   // Task -- NODOCS -- reset_blk
   //
   // Reset the DUT that corresponds to the specified block abstraction class.
   //
   // Currently empty.
   // Will rollback the environment's phase to the ~reset~
   // phase once the new phasing is available.
   //
   // In the meantime, the DUT should be reset before executing this
   // test sequence or this method should be implemented
   // in an extension to reset the DUT.
   //
   virtual task reset_blk(uvm_reg_block blk);
   endtask


endclass: uvm_mem_access_seq
