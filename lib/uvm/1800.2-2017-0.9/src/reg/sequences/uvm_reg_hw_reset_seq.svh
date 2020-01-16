// 
// -------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2012 Semifore
// Copyright 2004-2013 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2010 AMD
// Copyright 2014-2018 NVIDIA Corporation
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
// class -- NODOCS -- uvm_reg_hw_reset_seq
// Test the hard reset values of registers
//
// The test sequence performs the following steps
//
// 1. resets the DUT and the
// block abstraction class associated with this sequence.
//
// 2. reads all of the registers in the block,
// via all of the available address maps,
// comparing the value read with the expected reset value.
//
// If bit-type resource named
// "NO_REG_TESTS" or "NO_REG_HW_RESET_TEST"
// in the "REG::" namespace
// matches the full name of the block or register,
// the block or register is not tested.
//
//| uvm_resource_db#(bit)::set({"REG::",regmodel.blk.get_full_name(),".*"},
//|                            "NO_REG_TESTS", 1, this);
//
// This is usually the first test executed on any DUT.
//

// @uvm-ieee 1800.2-2017 auto E.1.1
class uvm_reg_hw_reset_seq extends uvm_reg_sequence #(uvm_sequence #(uvm_reg_item));

   `uvm_object_utils(uvm_reg_hw_reset_seq)

   // @uvm-ieee 1800.2-2017 auto E.1.2.1.1
   function new(string name="uvm_reg_hw_reset_seq");
     super.new(name);
   endfunction


   // Variable -- NODOCS -- model
   //
   // The block to be tested. Declared in the base class.
   //
   //| uvm_reg_block model; 


   // Variable -- NODOCS -- body
   //
   // Executes the Hardware Reset sequence.
   // Do not call directly. Use seq.start() instead.

   // @uvm-ieee 1800.2-2017 auto E.1.2.1.2
   virtual task body();

      if (model == null) begin
         `uvm_error("uvm_reg_hw_reset_seq", "Not block or system specified to run sequence on")
         return;
      end
      `uvm_info("STARTING_SEQ",{"\n\nStarting ",get_name()," sequence...\n"},UVM_LOW)
      
      this.reset_blk(model);
      model.reset();

      do_block(model);
   endtask: body

// Task -- NODOCS -- do_block
   //
   // Test all of the registers in a given ~block~
   //
   protected virtual task do_block(uvm_reg_block blk);
      uvm_reg_map maps[$];
      uvm_reg_map sub_maps[$];
	  uvm_reg regs[$];

      if (uvm_resource_db#(bit)::get_by_name({"REG::",blk.get_full_name()},
                                             "NO_REG_TESTS", 0) != null ||
          uvm_resource_db#(bit)::get_by_name({"REG::",blk.get_full_name()},
                                             "NO_REG_HW_RESET_TEST", 0) != null ) begin
            return;

      end

      blk.get_registers(regs, UVM_NO_HIER);
                                             
      foreach(regs[ridx]) begin
	                if (uvm_resource_db#(bit)::get_by_name({"REG::",regs[ridx].get_full_name()},
                                                 "NO_REG_TESTS", 0) != null ||
		                uvm_resource_db#(bit)::get_by_name({"REG::",regs[ridx].get_full_name()},
                                                 "NO_REG_HW_RESET_TEST", 0) != null )
			                	continue;
	      
	      begin
		      uvm_reg_map rm[$];
		      uvm_status_e status;
		      
		      regs[ridx].get_maps(rm);
		      
		      foreach(rm[midx]) begin
			      `uvm_info(get_type_name(),
				      $sformatf("Verifying reset value of register %s in map \"%s\"...",
					      regs[ridx].get_full_name(), rm[midx].get_full_name()), UVM_LOW)
            
			      regs[ridx].mirror(status, UVM_CHECK, UVM_FRONTDOOR, rm[midx], this);

			      if (status != UVM_IS_OK) begin
             		`uvm_error(get_type_name(),
	             		$sformatf("Status was %s when reading reset value of register \"%s\" through map \"%s\".",
                    	status.name(), regs[ridx].get_full_name(), rm[midx].get_full_name()))
		      end	
	      end	
      	end
      end	
      
      begin
         uvm_reg_block blks[$];
         
         blk.get_blocks(blks);
         foreach (blks[i]) begin
            do_block(blks[i]);
         end
      end

   endtask:do_block


   //
   // task -- NODOCS -- reset_blk
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

endclass: uvm_reg_hw_reset_seq
