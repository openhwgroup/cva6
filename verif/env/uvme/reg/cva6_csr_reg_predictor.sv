//
// Copyright 2020 OpenHW Group
// Copyright 2023 Thales DIS
//
// Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

class cva6_csr_reg_predictor #(type BUSTYPE=int) extends uvm_reg_predictor #(BUSTYPE);

   `uvm_component_param_utils(cva6_csr_reg_predictor #(BUSTYPE))
   
   function new (string name = "cva6_csr_reg_predictor", uvm_component parent);
      super.new(name, parent);
   endfunction : new
   
   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
   endfunction: connect_phase
   
   virtual function void write(BUSTYPE tr);      
      uvm_reg_field reg_fields[$];
      string fields_access[$];
      csr_reg rg;

      if (tr.instr.trap != 0)
         return; //Skip on traps

      if (tr.instr.group != uvma_isacov_pkg::CSR_GROUP)
         return; //Skip non CSR instructions
      
      if (!$cast(rg,map.get_reg_by_offset(tr.instr.csr_val)))
         `uvm_fatal("CSR_REG_PREDICTOR", "Error casting bus request")

      `uvm_info("CSR Predictor",$sformatf("Received CSR %s instruction %p", rg!= null? rg.get_name(): "Null", tr.instr), UVM_HIGH)

      //Check if register exist
      if (rg == null) begin
         `uvm_warning("CSR_REG_PREDICTOR", $sformatf("Accessing non-existent CSR with address 0x%0h, Illegal exception should raize", tr.instr.csr_val))
         return;
      end
      
      //Check if write in read only CSR
      if (tr.instr.is_csr_write() && rg.Xget_fields_accessX(map) == "RO")
         `uvm_warning("CSR_REG_PREDICTOR", $sformatf("Write on read-only CSR %s, illegal exception should raize", rg.get_name()))
      
      //Split into 2 transactions READ and/or WRITE depending on instruction
      super.write(tr); //1rst pass: Read operation
      
      //Modify access depending on instruction CSRRS/I or CSRRC/I
      if (tr.instr.name inside {uvma_isacov_pkg::CSRRS, uvma_isacov_pkg::CSRRC, 
                                uvma_isacov_pkg::CSRRSI,uvma_isacov_pkg::CSRRCI}) begin
         rg.get_fields(reg_fields);
         foreach (reg_fields[i]) begin
            fields_access.push_back(reg_fields[i].get_access(map));
            if (reg_fields[i].get_access(map) == "RW") begin
               if (tr.instr.name inside {uvma_isacov_pkg::CSRRS, uvma_isacov_pkg::CSRRSI}) 
                  reg_fields[i].set_access("W1S");
               else if (tr.instr.name inside {uvma_isacov_pkg::CSRRC, uvma_isacov_pkg::CSRRCI})
                  reg_fields[i].set_access("W1C");
            end
         end
      end
      
      super.write(tr); //2nd pass: Write operation
      
      //Revertback original access for instr CSRRS/I or CSRRC/I
      foreach (reg_fields[i])
         reg_fields[i].set_access(fields_access[i]);             
                                   
  endfunction

endclass


