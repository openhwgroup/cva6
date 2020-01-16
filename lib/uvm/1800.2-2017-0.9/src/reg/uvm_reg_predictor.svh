//
// -------------------------------------------------------------
// Copyright 2014 Semifore
// Copyright 2004-2011 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2014-2018 NVIDIA Corporation
// Copyright 2012 Accellera Systems Initiative
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
// TITLE -- NODOCS -- Explicit Register Predictor
//------------------------------------------------------------------------------
//
// The <uvm_reg_predictor> class defines a predictor component,
// which is used to update the register model's mirror values
// based on transactions explicitly observed on a physical bus. 
//------------------------------------------------------------------------------

class uvm_predict_s;
   bit addr[uvm_reg_addr_t];
   uvm_reg_item reg_item;
endclass

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_reg_predictor
//
// Updates the register model mirror based on observed bus transactions
//
// This class converts observed bus transactions of type ~BUSTYPE~ to generic
// registers transactions, determines the register being accessed based on the
// bus address, then updates the register's mirror value with the observed bus
// data, subject to the register's access mode. See <uvm_reg::predict> for details.
//
// Memories can be large, so their accesses are not predicted.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 19.3.1
class uvm_reg_predictor #(type BUSTYPE=int) extends uvm_component;

  `uvm_component_param_utils(uvm_reg_predictor#(BUSTYPE))

  // Variable -- NODOCS -- bus_in
  //
  // Observed bus transactions of type ~BUSTYPE~ are received from this
  // port and processed.
  //
  // For each incoming transaction, the predictor will attempt to get the
  // register or memory handle corresponding to the observed bus address. 
  //
  // If there is a match, the predictor calls the register or memory's
  // predict method, passing in the observed bus data. The register or
  // memory mirror will be updated with this data, subject to its configured
  // access behavior--RW, RO, WO, etc. The predictor will also convert the
  // bus transaction to a generic <uvm_reg_item> and send it out the
  // ~reg_ap~ analysis port.
  //
  // If the register is wider than the bus, the
  // predictor will collect the multiple bus transactions needed to
  // determine the value being read or written.
  //
  uvm_analysis_imp #(BUSTYPE, uvm_reg_predictor #(BUSTYPE)) bus_in;


  // Variable -- NODOCS -- reg_ap
  //
  // Analysis output port that publishes <uvm_reg_item> transactions
  // converted from bus transactions received on ~bus_in~.
  uvm_analysis_port #(uvm_reg_item) reg_ap;


  // Variable -- NODOCS -- map
  //
  // The map used to convert a bus address to the corresponding register
  // or memory handle. Must be configured before the run phase.
  // 
  uvm_reg_map map;


  // Variable -- NODOCS -- adapter
  //
  // The adapter used to convey the parameters of a bus operation in 
  // terms of a canonical <uvm_reg_bus_op> datum.
  // The <uvm_reg_adapter> must be configured before the run phase.
  //
  uvm_reg_adapter adapter;



  // @uvm-ieee 1800.2-2017 auto 19.3.3.1
  function new (string name, uvm_component parent);
    super.new(name, parent);
    bus_in = new("bus_in", this);
    reg_ap = new("reg_ap", this);
  endfunction

  // This method is documented in uvm_object
`ifdef UVM_ENABLE_DEPRECATED_API
  static string type_name = "";
  virtual function string get_type_name();
    if (type_name == "") begin
      BUSTYPE t;
      t = BUSTYPE::type_id::create("t");
      type_name = {"uvm_reg_predictor #(", t.get_type_name(), ")"};
    end
    return type_name;
  endfunction
`else // !`ifdef UVM_ENABLE_DEPRECATED_API
  // TODO:  Is it better to replace this with:
  //| `uvm_type_name_decl($sformatf("uvm_reg_predictor #(%s)", BUSTYPE::type_name())
  static function string type_name();
    static string m_type_name;
    if (m_type_name == "") begin
      BUSTYPE t;
      t = BUSTYPE::type_id::create("t");
      m_type_name = {"uvm_reg_predictor #(", t.get_type_name(), ")"};
    end
    return m_type_name;
  endfunction // type_name
  virtual function string get_type_name();
    return type_name();
  endfunction : get_type_name

`endif // !`ifdef UVM_ENABLE_DEPRECATED_API

  // @uvm-ieee 1800.2-2017 auto 19.3.3.2
  virtual function void pre_predict(uvm_reg_item rw);
  endfunction

  local uvm_predict_s m_pending[uvm_reg];


  // Function- write
  //
  // not a user-level method. Do not call directly. See documentation
  // for the ~bus_in~ member.
  //
  virtual function void write(BUSTYPE tr);
     uvm_reg rg;
     uvm_reg_bus_op rw;
    if (adapter == null)
     `uvm_fatal("REG/WRITE/NULL","write: adapter handle is null") 

     // In case they forget to set byte_en
     rw.byte_en = -1;
     adapter.bus2reg(tr,rw);
     rg = map.get_reg_by_offset(rw.addr, (rw.kind == UVM_READ));

     // ToDo: Add memory look-up and call <uvm_mem::XsampleX()>

     if (rg != null) begin
       bit found;
       uvm_reg_item reg_item;
       uvm_reg_map local_map;
       uvm_reg_map_info map_info;
       uvm_predict_s predict_info;
       uvm_reg_indirect_data ireg;
       uvm_reg ir;
 
       if (!m_pending.exists(rg)) begin
         uvm_reg_item item = new;
         predict_info =new;
         item.element_kind = UVM_REG;
         item.element      = rg;
         item.path         = UVM_PREDICT;
         item.map          = map;
         item.kind         = rw.kind;
         predict_info.reg_item = item;
         m_pending[rg] = predict_info;
       end
       predict_info = m_pending[rg];
       reg_item = predict_info.reg_item;

       if (predict_info.addr.exists(rw.addr)) begin
          `uvm_error("REG_PREDICT_COLLISION",{"Collision detected for register '",
                     rg.get_full_name(),"'"})
          // TODO: what to do with subsequent collisions?
          m_pending.delete(rg);
       end

       local_map = rg.get_local_map(map);
       map_info = local_map.get_reg_map_info(rg);
       ir=($cast(ireg, rg))?ireg.get_indirect_reg():rg;

       foreach (map_info.addr[i]) begin
         if (rw.addr == map_info.addr[i]) begin
            found = 1;
           reg_item.value[0] |= rw.data << (i * map.get_n_bytes()*8);
           predict_info.addr[rw.addr] = 1;
           if (predict_info.addr.num() == map_info.addr.size()) begin
              // We've captured the entire abstract register transaction.
              uvm_predict_e predict_kind = 
                  (reg_item.kind == UVM_WRITE) ? UVM_PREDICT_WRITE : UVM_PREDICT_READ;

              if (reg_item.kind == UVM_READ &&
                  local_map.get_check_on_read() &&
                  reg_item.status != UVM_NOT_OK) begin
                 void'(rg.do_check(ir.get_mirrored_value(), reg_item.value[0], local_map));
              end
              
              pre_predict(reg_item);

              ir.XsampleX(reg_item.value[0], rw.byte_en,
                          reg_item.kind == UVM_READ, local_map);
              begin
                 uvm_reg_block blk = rg.get_parent();
                 blk.XsampleX(map_info.offset,
                              reg_item.kind == UVM_READ,
                              local_map);
              end

              rg.do_predict(reg_item, predict_kind, rw.byte_en);
              if(reg_item.kind == UVM_WRITE)
                `uvm_info("REG_PREDICT", {"Observed WRITE transaction to register ",
                         ir.get_full_name(), ": value='h",
                         $sformatf("%0h",reg_item.value[0]), " : updated value = 'h", 
                         $sformatf("%0h",ir.get())},UVM_HIGH)
              else
                `uvm_info("REG_PREDICT", {"Observed READ transaction to register ",
                         ir.get_full_name(), ": value='h",
                         $sformatf("%0h",reg_item.value[0])},UVM_HIGH)
              reg_ap.write(reg_item);
              m_pending.delete(rg);
           end
           break;
         end
       end
       if (!found)
         `uvm_error("REG_PREDICT_INTERNAL",{"Unexpected failed address lookup for register '",
                  rg.get_full_name(),"'"})
     end
     else begin
       `uvm_info("REG_PREDICT_NOT_FOR_ME",
          {"Observed transaction does not target a register: ",
            $sformatf("%p",tr)},UVM_FULL)
     end
  endfunction

  
  // Function -- NODOCS -- check_phase
  //
  // Checks that no pending register transactions are still queued.

  // @uvm-ieee 1800.2-2017 auto 19.3.3.3
  virtual function void check_phase(uvm_phase phase);
	 string q[$];
     super.check_phase(phase);
            
     foreach (m_pending[l]) begin
	     uvm_reg rg=l;
         q.push_back($sformatf("\n%s",rg.get_full_name()));
     end
            
    if (m_pending.num() > 0) begin
      `uvm_error("PENDING REG ITEMS",
      	$sformatf("There are %0d incomplete register transactions still pending completion:%s",m_pending.num(),`UVM_STRING_QUEUE_STREAMING_PACK(q)))

    end
  endfunction

endclass
