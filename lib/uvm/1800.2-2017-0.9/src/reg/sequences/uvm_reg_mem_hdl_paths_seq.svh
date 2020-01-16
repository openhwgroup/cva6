// 
// -------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2010 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
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
// TITLE -- NODOCS -- HDL Paths Checking Test Sequence
//

//
// class -- NODOCS -- uvm_reg_mem_hdl_paths_seq
//
// Verify the correctness of HDL paths specified for registers and memories.
//
// This sequence is be used to check that the specified backdoor paths
// are indeed accessible by the simulator.
// By default, the check is performed for the default design abstraction.
// If the simulation contains multiple models of the DUT,
// HDL paths for multiple design abstractions can be checked.
// 
// If a path is not accessible by the simulator, it cannot be used for 
// read/write backdoor accesses. In that case a warning is produced. 
// A simulator may have finer-grained access permissions such as separate 
// read or write permissions.
// These extra access permissions are NOT checked.
//
// The test is performed in zero time and
// does not require any reads/writes to/from the DUT.
//

// @uvm-ieee 1800.2-2017 auto E.7.1
class uvm_reg_mem_hdl_paths_seq extends uvm_reg_sequence #(uvm_sequence #(uvm_reg_item));
    // Variable -- NODOCS -- abstractions
    // If set, check the HDL paths for the specified design abstractions.
    // If empty, check the HDL path for the default design abstraction,
    // as specified with <uvm_reg_block::set_default_hdl_path()>
    string abstractions[$];
    
    `uvm_object_utils_begin(uvm_reg_mem_hdl_paths_seq)
        `uvm_field_queue_string(abstractions, UVM_DEFAULT)
    `uvm_object_utils_end
    
    // @uvm-ieee 1800.2-2017 auto E.7.3
    function new(string name="uvm_reg_mem_hdl_paths_seq");
        super.new(name);
    endfunction

    virtual task body();

        if (model == null) begin
            uvm_report_error("uvm_reg_mem_hdl_paths_seq", "Register model handle is null");
            return;
        end

       `uvm_info("uvm_reg_mem_hdl_paths_seq",
                 {"checking HDL paths for all registers/memories in ",
                  model.get_full_name()}, UVM_LOW)

       if (abstractions.size() == 0)
          do_block(model, "");
       else begin
          foreach (abstractions[i])
             do_block(model, abstractions[i]);
       end

        `uvm_info("uvm_reg_mem_hdl_paths_seq", "HDL path validation completed ",UVM_LOW)
        
    endtask: body


    // Any additional steps required to reset the block
    // and make it accessible
    virtual task reset_blk(uvm_reg_block blk);
    endtask


    protected virtual function void do_block(uvm_reg_block blk,
                                             string        kind);
        uvm_reg       regs[$];
        uvm_mem       mems[$];

       `uvm_info("uvm_reg_mem_hdl_paths_seq",
                 {"Validating HDL paths in ", blk.get_full_name(),
                  " for ", (kind == "") ? "default" : kind,
                  " design abstraction"}, UVM_MEDIUM) 

       // Iterate over all registers, checking accesses
       blk.get_registers(regs, UVM_NO_HIER);
       foreach (regs[i]) 
          check_reg(regs[i], kind);
       
       blk.get_memories(mems, UVM_NO_HIER);
       foreach (mems[i]) 
          check_mem(mems[i], kind);
    
       begin
          uvm_reg_block blks[$];
          
          blk.get_blocks(blks);
          foreach (blks[i]) begin
             do_block(blks[i], kind);
          end
       end
    endfunction: do_block
    

    protected virtual function void check_reg(uvm_reg r,
                                              string kind);
        uvm_hdl_path_concat paths[$];

	// avoid calling get_full_hdl_path when the register has not path for this abstraction kind
	if(!r.has_hdl_path(kind))
		return;

        r.get_full_hdl_path(paths, kind);
        if (paths.size() == 0) return;

        foreach(paths[p]) begin
            uvm_hdl_path_concat path=paths[p];
            foreach (path.slices[j]) begin
                string p_ = path.slices[j].path;
                uvm_reg_data_t d;
                if (!uvm_hdl_read(p_,d))
                    `uvm_error("uvm_reg_mem_hdl_paths_seq",
                               $sformatf("HDL path \"%s\" for register \"%s\" is not readable",
                                         p_, r.get_full_name()))
                if (!uvm_hdl_check_path(p_))
                    `uvm_error("uvm_reg_mem_hdl_paths_seq",
                               $sformatf("HDL path \"%s\" for register \"%s\" is not accessible",
                                         p_, r.get_full_name()))
            end
        end
    endfunction
 

    protected virtual function void check_mem(uvm_mem m,
                                              string kind);
        uvm_hdl_path_concat paths[$];

	// avoid calling get_full_hdl_path when the register has not path for this abstraction kind
	if(!m.has_hdl_path(kind))
		return;

        m.get_full_hdl_path(paths, kind);
        if (paths.size() == 0) return;

        foreach(paths[p]) begin
            uvm_hdl_path_concat path=paths[p];
            foreach (path.slices[j]) 
            begin
                string p_ = path.slices[j].path;
                if(!uvm_hdl_check_path(p_))
                    `uvm_error("uvm_reg_mem_hdl_paths_seq",
                               $sformatf("HDL path \"%s\" for memory \"%s\" is not accessible",
                                         p_, m.get_full_name()))
            end
        end
    endfunction 
endclass: uvm_reg_mem_hdl_paths_seq
