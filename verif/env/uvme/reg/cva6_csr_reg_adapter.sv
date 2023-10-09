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

class cva6_csr_reg_adapter extends uvm_reg_adapter;

  `uvm_object_utils (cva6_csr_reg_adapter)

  function new (string name = "cva6_csr_reg_adapter");
      super.new (name);
   endfunction
  
  function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
    //uvm_reg in passive mode, no implementation needed
  endfunction

  bit req_q[uvma_isacov_mon_trn_c]; //Used to store 1rst and 2nd Pass Read->Write
  
  function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    uvma_isacov_mon_trn_c req;
    rw.addr = 0; // 0 not mapped addr, safe to use as default
    
    if(!$cast(req, bus_item) )
      `uvm_fatal("CSR_REG_ADAPTER", "Error casting bus request")
        
    if (req.instr.group != uvma_isacov_pkg::CSR_GROUP) 
      return;
        
    if (req_q[req] == 0) begin // First pass Read
      req_q[req]=1;
      
      rw.kind = UVM_READ;
      
      if ((req.instr.rd==0) && (req.instr.name inside {uvma_isacov_pkg::CSRRW, uvma_isacov_pkg::CSRRWI}))
         return; //no read when CSRRW/CSRRWI with rd==x0  
         
      rw.data = req.instr.rd_value;    
    
    end else begin  // Second pass Write
      req_q.delete(req);
      
      rw.kind = UVM_WRITE;
      if (req.instr.name inside {uvma_isacov_pkg::CSRRWI, uvma_isacov_pkg::CSRRSI, uvma_isacov_pkg::CSRRCI})
         rw.data = req.instr.rs1;
      else
         rw.data = req.instr.rs1_value;
      
      if ((req.instr.rs1 == 0) && req.instr.name inside {uvma_isacov_pkg::CSRRS, uvma_isacov_pkg::CSRRC, uvma_isacov_pkg::CSRRSI, uvma_isacov_pkg::CSRRCI})
         return; //no write when CSRRS/CSRRC with rs1==0x or CSRRSI/CSRRCI with imm==0  
      
    end
        
    rw.addr   = req.instr.csr_val;
    rw.status = UVM_IS_OK;
    
    `uvm_info("CSR_REG_ADAPTER",$sformatf("Monitored transaction CSR KIND:%s ADDR:0x%0h DATA:0x%0h. Original instruction: INSTR:%s ADDR:0x%0h RS1:0x%0h RD:0x%0h IMMU:0x%0h", rw.kind, rw.addr, rw.data, req.instr.name, req.instr.csr_val,req.instr.rs1_value, req.instr.rd_value, req.instr.immu),UVM_HIGH);
    
  endfunction
endclass
