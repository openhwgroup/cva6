// -------------------------------------------------------------
// Copyright 2010-2018 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2014-2017 Intel Corporation
// Copyright 2004-2018 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2010 AMD
// Copyright 2014-2018 NVIDIA Corporation
// Copyright 2017 Cisco Systems, Inc.
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

// Class -- NODOCS -- uvm_reg_transaction_order_policy
// Not in LRM.
class uvm_reg_map_info;
   uvm_reg_addr_t         offset;
   string                 rights;
   bit                    unmapped;
   uvm_reg_addr_t         addr[];
   uvm_reg_frontdoor      frontdoor;
   uvm_reg_map_addr_range mem_range; 
   
   // if set marks the uvm_reg_map_info as initialized, prevents using an uninitialized map (for instance if the model 
   // has not been locked accidently and the maps have not been computed before)
   bit                    is_initialized;
endclass


// Class -- NODOCS -- uvm_reg_transaction_order_policy
virtual class uvm_reg_transaction_order_policy extends uvm_object;
    function new(string name = "policy");
        super.new(name);
    endfunction
    
    // Function -- NODOCS -- order
    // the order() function may reorder the sequence of bus transactions
    // produced by a single uvm_reg transaction (read/write).
    // This can be used in scenarios when the register width differs from 
    // the bus width and one register access results in a series of bus transactions.
    // the first item (0) of the queue will be the first bus transaction (the last($) 
    // will be the final transaction
    pure virtual function void order(ref uvm_reg_bus_op q[$]);
endclass

// Extends virtual class uvm_sequence_base so that it can be constructed:
class uvm_reg_seq_base extends uvm_sequence_base;
 
   `uvm_object_utils(uvm_reg_seq_base)


function new(string name = "uvm_reg_seq_base");
  super.new(name);
endfunction  

endclass


//------------------------------------------------------------------------------
//
// Class -- NODOCS -- uvm_reg_map
//
// :Address map abstraction class
//
// This class represents an address map.
// An address map is a collection of registers and memories
// accessible via a specific physical interface.
// Address maps can be composed into higher-level address maps.
//
// Address maps are created using the <uvm_reg_block::create_map()>
// method.
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 18.2.1
class uvm_reg_map extends uvm_object;

   `uvm_object_utils(uvm_reg_map)
   
   // info that is valid only if top-level map
   local uvm_reg_addr_t     m_base_addr;
   local int unsigned       m_n_bytes;
   local uvm_endianness_e   m_endian;
   local bit                m_byte_addressing;
   local uvm_object_wrapper m_sequence_wrapper;
   local uvm_reg_adapter    m_adapter;
   local uvm_sequencer_base m_sequencer;
   local bit                m_auto_predict;
   local bit                m_check_on_read;

   local uvm_reg_block      m_parent;

   local int unsigned       m_system_n_bytes;

   local uvm_reg_map        m_parent_map;
   local uvm_reg_addr_t     m_submaps[uvm_reg_map];       // value=offset of submap at this level
   local string             m_submap_rights[uvm_reg_map]; // value=rights of submap at this level

   local uvm_reg_map_info   m_regs_info[uvm_reg];
   local uvm_reg_map_info   m_mems_info[uvm_mem];

   local uvm_reg            m_regs_by_offset[uvm_reg_addr_t];
                            // Use only in addition to above if a RO and a WO
                            // register share the same address.
   local uvm_reg            m_regs_by_offset_wo[uvm_reg_addr_t]; 
   local uvm_mem            m_mems_by_offset[uvm_reg_map_addr_range];

   local uvm_reg_transaction_order_policy policy;

   extern /*local*/ function void Xinit_address_mapX();

   static local uvm_reg_map   m_backdoor;


   // @uvm-ieee 1800.2-2017 auto 18.2.2
   static function uvm_reg_map backdoor();
      if (m_backdoor == null)
        m_backdoor = new("Backdoor");
      return m_backdoor;
   endfunction


   //----------------------
   // Group -- NODOCS -- Initialization
   //----------------------



   // @uvm-ieee 1800.2-2017 auto 18.2.3.1
   extern function new(string name="uvm_reg_map");



   // @uvm-ieee 1800.2-2017 auto 18.2.3.2
   extern function void configure(uvm_reg_block     parent,
                                  uvm_reg_addr_t    base_addr,
                                  int unsigned      n_bytes,
                                  uvm_endianness_e  endian,
                                  bit byte_addressing = 1);


   // @uvm-ieee 1800.2-2017 auto 18.2.3.3
   extern virtual function void add_reg (uvm_reg           rg,
                                         uvm_reg_addr_t    offset,
                                         string            rights = "RW",
                                         bit               unmapped=0,
                                         uvm_reg_frontdoor frontdoor=null);



   // @uvm-ieee 1800.2-2017 auto 18.2.3.4
   extern virtual function void add_mem (uvm_mem        mem,
                                         uvm_reg_addr_t offset,
                                         string         rights = "RW",
                                         bit            unmapped=0,
                                         uvm_reg_frontdoor frontdoor=null);

   

   // NOTE THIS isnt really true because one can add a map only to another map if the 
   // map parent blocks are either the same or the maps parent is an ancestor of the submaps parent
   // also AddressUnitBits needs to match which means essentially that within a block there can only be one 
   // AddressUnitBits
   
   // @uvm-ieee 1800.2-2017 auto 18.2.3.5
   extern virtual function void add_submap (uvm_reg_map    child_map,
                                            uvm_reg_addr_t offset);


   // Function -- NODOCS -- set_sequencer
   //
   // Set the sequencer and adapter associated with this map. This method
   // ~must~ be called before starting any sequences based on uvm_reg_sequence.

   // @uvm-ieee 1800.2-2017 auto 18.2.3.6
   extern virtual function void set_sequencer (uvm_sequencer_base sequencer,
                                               uvm_reg_adapter    adapter=null);



   // Function -- NODOCS -- set_submap_offset
   //
   // Set the offset of the given ~submap~ to ~offset~.

   // @uvm-ieee 1800.2-2017 auto 18.2.3.8
   extern virtual function void set_submap_offset (uvm_reg_map submap,
                                                   uvm_reg_addr_t offset);


   // Function -- NODOCS -- get_submap_offset
   //
   // Return the offset of the given ~submap~.

   // @uvm-ieee 1800.2-2017 auto 18.2.3.7
   extern virtual function uvm_reg_addr_t get_submap_offset (uvm_reg_map submap);


   // Function -- NODOCS -- set_base_addr
   //
   // Set the base address of this map.

   // @uvm-ieee 1800.2-2017 auto 18.2.3.9
   extern virtual function void   set_base_addr (uvm_reg_addr_t  offset);



   // @uvm-ieee 1800.2-2017 auto 18.2.3.10
   extern virtual function void reset(string kind = "SOFT");


   /*local*/ extern virtual function void add_parent_map(uvm_reg_map  parent_map,
                                                         uvm_reg_addr_t offset);

   /*local*/ extern virtual function void Xverify_map_configX();

   /*local*/ extern virtual function void m_set_reg_offset(uvm_reg   rg,
                                                           uvm_reg_addr_t offset,
                                                           bit unmapped);

   /*local*/ extern virtual function void m_set_mem_offset(uvm_mem mem,
                                                           uvm_reg_addr_t offset,
                                                           bit unmapped);


   //---------------------
   // Group -- NODOCS -- Introspection
   //---------------------

   // Function -- NODOCS -- get_name
   //
   // Get the simple name
   //
   // Return the simple object name of this address map.
   //

   // Function -- NODOCS -- get_full_name
   //
   // Get the hierarchical name
   //
   // Return the hierarchal name of this address map.
   // The base of the hierarchical name is the root block.
   //
   extern virtual function string get_full_name();



   // @uvm-ieee 1800.2-2017 auto 18.2.4.1
   extern virtual function uvm_reg_map get_root_map();



   // @uvm-ieee 1800.2-2017 auto 18.2.4.2
   extern virtual function uvm_reg_block get_parent();



   // @uvm-ieee 1800.2-2017 auto 18.2.4.3
   extern virtual function uvm_reg_map           get_parent_map();



   // @uvm-ieee 1800.2-2017 auto 18.2.4.4
   extern virtual function uvm_reg_addr_t get_base_addr (uvm_hier_e hier=UVM_HIER);


   // Function -- NODOCS -- get_n_bytes
   //
   // Get the width in bytes of the bus associated with this map. If ~hier~
   // is ~UVM_HIER~, then gets the effective bus width relative to the system
   // level. The effective bus width is the narrowest bus width from this
   // map to the top-level root map. Each bus access will be limited to this
   // bus width.
   //
   extern virtual function int unsigned get_n_bytes (uvm_hier_e hier=UVM_HIER);


   // Function -- NODOCS -- get_addr_unit_bytes
   //
   // Get the number of bytes in the smallest addressable unit in the map.
   // Returns 1 if the address map was configured using byte-level addressing.
   // Returns <get_n_bytes()> otherwise.
   //
   extern virtual function int unsigned get_addr_unit_bytes();



   // @uvm-ieee 1800.2-2017 auto 18.2.4.7
   extern virtual function uvm_endianness_e get_endian (uvm_hier_e hier=UVM_HIER);



   // @uvm-ieee 1800.2-2017 auto 18.2.4.8
   extern virtual function uvm_sequencer_base get_sequencer (uvm_hier_e hier=UVM_HIER);



   // @uvm-ieee 1800.2-2017 auto 18.2.4.9
   extern virtual function uvm_reg_adapter get_adapter (uvm_hier_e hier=UVM_HIER);



   // @uvm-ieee 1800.2-2017 auto 18.2.4.10
   extern virtual function void  get_submaps (ref uvm_reg_map maps[$],
                                              input uvm_hier_e hier=UVM_HIER);



   // @uvm-ieee 1800.2-2017 auto 18.2.4.11
   extern virtual function void  get_registers (ref uvm_reg regs[$],
                                                input uvm_hier_e hier=UVM_HIER);



   // @uvm-ieee 1800.2-2017 auto 18.2.4.12
   extern virtual function void  get_fields (ref uvm_reg_field fields[$],
                                             input uvm_hier_e hier=UVM_HIER);

   

   // @uvm-ieee 1800.2-2017 auto 18.2.4.13
   extern virtual function void  get_memories (ref uvm_mem mems[$],
                                               input uvm_hier_e hier=UVM_HIER);



   // @uvm-ieee 1800.2-2017 auto 18.2.4.14
   extern virtual function void  get_virtual_registers (ref uvm_vreg regs[$],
                                                        input uvm_hier_e hier=UVM_HIER);



   // @uvm-ieee 1800.2-2017 auto 18.2.4.15
   extern virtual function void  get_virtual_fields (ref uvm_vreg_field fields[$],
                                                     input uvm_hier_e hier=UVM_HIER);


   extern virtual function uvm_reg_map_info get_reg_map_info(uvm_reg rg,  bit error=1);
   extern virtual function uvm_reg_map_info get_mem_map_info(uvm_mem mem, bit error=1);
   extern virtual function int unsigned get_size();


   // @uvm-ieee 1800.2-2017 auto 18.2.4.16
   extern virtual function int get_physical_addresses(uvm_reg_addr_t        base_addr,
                                                      uvm_reg_addr_t        mem_offset,
                                                      int unsigned          n_bytes,
                                                      ref uvm_reg_addr_t    addr[]);
   


   // @uvm-ieee 1800.2-2017 auto 18.2.4.17
   extern virtual function uvm_reg get_reg_by_offset(uvm_reg_addr_t offset,
                                                     bit            read = 1);


   // @uvm-ieee 1800.2-2017 auto 18.2.4.18
   extern virtual function uvm_mem    get_mem_by_offset(uvm_reg_addr_t offset);


   //------------------
   // Group -- NODOCS -- Bus Access
   //------------------

 
   // @uvm-ieee 1800.2-2017 auto 18.2.5.2
   function void set_auto_predict(bit on=1); m_auto_predict = on; endfunction


 
   // @uvm-ieee 1800.2-2017 auto 18.2.5.1
   function bit  get_auto_predict(); return m_auto_predict; endfunction


 
   // @uvm-ieee 1800.2-2017 auto 18.2.5.3
   function void set_check_on_read(bit on=1);
      m_check_on_read = on;
      foreach (m_submaps[submap]) begin
         submap.set_check_on_read(on);
      end
   endfunction


   // Function -- NODOCS -- get_check_on_read
   //
   // Gets the check-on-read mode setting for this map.
   // 
   function bit  get_check_on_read(); return m_check_on_read; endfunction


   
   // Task -- NODOCS -- do_bus_write
   //
   // Perform a bus write operation.
   //
   extern virtual task do_bus_write (uvm_reg_item rw,
                                     uvm_sequencer_base sequencer,
                                     uvm_reg_adapter adapter);


   // Task -- NODOCS -- do_bus_read
   //
   // Perform a bus read operation.
   //
   extern virtual task do_bus_read (uvm_reg_item rw,
                                    uvm_sequencer_base sequencer,
                                    uvm_reg_adapter adapter);


   // Task -- NODOCS -- do_write
   //
   // Perform a write operation.
   //
   extern virtual task do_write(uvm_reg_item rw);


   // Task -- NODOCS -- do_read
   //
   // Perform a read operation.
   //
   extern virtual task do_read(uvm_reg_item rw);

   extern function void Xget_bus_infoX (uvm_reg_item rw,
                                        output uvm_reg_map_info map_info,
                                        output int size,
                                        output int lsb,
                                        output int addr_skip);

   extern virtual function string      convert2string();
   extern virtual function uvm_object  clone();
   extern virtual function void        do_print (uvm_printer printer);
   extern virtual function void        do_copy   (uvm_object rhs);
   //extern virtual function bit       do_compare (uvm_object rhs, uvm_comparer comparer);
   //extern virtual function void      do_pack (uvm_packer packer);
   //extern virtual function void      do_unpack (uvm_packer packer);



    // @uvm-ieee 1800.2-2017 auto 18.2.5.5
    function void set_transaction_order_policy(uvm_reg_transaction_order_policy pol);
        policy = pol;
    endfunction
    

    // @uvm-ieee 1800.2-2017 auto 18.2.5.4
    function uvm_reg_transaction_order_policy get_transaction_order_policy();
        return policy;
    endfunction    
   
// ceil() function
local function automatic int unsigned ceil(int unsigned a, int unsigned b);
	int r = a / b;
	int r0 = a % b;
	return r0 ? (r+1): r;
endfunction
  
 /*
  * translates an access from the current map ~this~ to an address ~base_addr~ (within the current map) with a 
  * length of ~n_bytes~ into an access from map ~parent_map~. 
  * if ~mem~ and ~mem_offset~ are supplied then a memory access is assumed 
  * results: ~addr~ contains the set of addresses and ~byte_offset~ holds the number of bytes the data stream needs to be shifted 
  * 
  * this implementation assumes a packed data access
  */ 
 extern virtual function int get_physical_addresses_to_map(uvm_reg_addr_t     base_addr,
		uvm_reg_addr_t     mem_offset,
		int unsigned       n_bytes,  // number of bytes
		ref uvm_reg_addr_t addr[], // array of addresses 
		input uvm_reg_map parent_map, // translate till parent_map is the parent of the actual map or NULL if this is a root_map
		ref int unsigned byte_offset,
		input uvm_mem mem =null
	 );

// performs all bus operations ~accesses~ generated from ~rw~ via adapter ~adapter~ on sequencer ~sequencer~
extern task perform_accesses(ref uvm_reg_bus_op    accesses[$],
		input uvm_reg_item rw,
		input uvm_reg_adapter adapter,
		input  uvm_sequencer_base sequencer);

// performs all necessary bus accesses defined by ~rw~ on the sequencer ~sequencer~ utilizing the adapter ~adapter~
extern task do_bus_access (uvm_reg_item rw,
                               uvm_sequencer_base sequencer,
                               uvm_reg_adapter adapter);
  
    // unregisters all content from this map recursively
    // it is NOT expected that this leads to a fresh new map 
    // it rather removes all knowledge of this map from other objects 
    // so that they can be reused with a fresh map instance
	// @uvm-ieee 1800.2-2017 auto 18.2.3.11
	virtual function void unregister();
		uvm_reg_block q[$];
		uvm_reg_block::get_root_blocks(q);
		
		foreach(q[idx])
			q[idx].set_lock(0);
		
		foreach(q[idx])
			q[idx].unregister(this);
		
		foreach (m_submaps[map_])
			map_.unregister();

		m_submaps.delete();
		m_submap_rights.delete();


		foreach(m_regs_by_offset[i])
			m_regs_by_offset[i].unregister(this);
		
		m_regs_by_offset.delete();
		m_regs_by_offset_wo.delete();
		m_mems_by_offset.delete();

		m_regs_info.delete();
		m_mems_info.delete();
			
		m_parent_map =null;
	endfunction

	virtual function uvm_reg_map clone_and_update(string rights);
		if(m_parent_map!=null) `uvm_error("UVM/REG/CLONEMAPWITHPARENT","cannot clone a map which already has a parent")
		if(m_submaps.size() != 0) `uvm_error("UVM/REG/CLONEMAPWITHCHILDREN","cannot clone a map which already has children")
		
		begin
			uvm_reg_map m;
			uvm_reg_block b = get_parent();
			uvm_reg qr[$];
			uvm_mem qm[$];
			
			m = b.create_map(get_name(),0,m_n_bytes,m_endian,m_byte_addressing);
			
			foreach(m_regs_by_offset[i]) begin
				uvm_reg rg=m_regs_by_offset[i];
				uvm_reg_map_info info = get_reg_map_info(rg);
				m.add_reg(rg,info.offset,rights, info.unmapped, info.frontdoor);
			end	
			foreach(m_mems_by_offset[i]) begin
				uvm_mem rg=m_mems_by_offset[i];
				uvm_reg_map_info info = get_mem_map_info(rg);
				m.add_mem(rg,info.offset,rights, info.unmapped, info.frontdoor);
			end				
			return m;
		end	
	endfunction
endclass: uvm_reg_map
   


//---------------
// Initialization
//---------------

// new

function uvm_reg_map::new(string name = "uvm_reg_map");
   super.new((name == "") ? "default_map" : name);
   m_auto_predict = 0;
   m_check_on_read = 0;
endfunction


// configure

function void uvm_reg_map::configure(uvm_reg_block    parent,
                                     uvm_reg_addr_t   base_addr,
                                     int unsigned     n_bytes,
                                     uvm_endianness_e endian,
                                     bit              byte_addressing=1);
   m_parent     = parent;
   m_n_bytes    = n_bytes;
   m_endian     = endian;
   m_base_addr  = base_addr;
   m_byte_addressing = byte_addressing;
endfunction: configure


// add_reg

function void uvm_reg_map::add_reg(uvm_reg rg, 
                                   uvm_reg_addr_t offset,
                                   string rights = "RW",
                                   bit unmapped=0,
                                   uvm_reg_frontdoor frontdoor=null);

   if (m_regs_info.exists(rg)) begin
      `uvm_error("RegModel", {"Register '",rg.get_name(),
                 "' has already been added to map '",get_name(),"'"})
      return;
   end

   if (rg.get_parent() != get_parent()) begin
      `uvm_error("RegModel",
         {"Register '",rg.get_full_name(),"' may not be added to address map '",
          get_full_name(),"' : they are not in the same block"})
      return;
   end
   
   rg.add_map(this);

   begin
   uvm_reg_map_info info = new;
   info.offset   = offset;
   info.rights   = rights;
   info.unmapped = unmapped;
   info.frontdoor = frontdoor;
   info.is_initialized=0;
   m_regs_info[rg]=info;	   
   end
endfunction


// m_set_reg_offset

function void uvm_reg_map::m_set_reg_offset(uvm_reg rg, 
                                            uvm_reg_addr_t offset,
                                            bit unmapped);

   if (!m_regs_info.exists(rg)) begin
      `uvm_error("RegModel",
         {"Cannot modify offset of register '",rg.get_full_name(),
         "' in address map '",get_full_name(),
         "' : register not mapped in that address map"})
      return;
   end

   begin
      uvm_reg_map_info info    = m_regs_info[rg];
      uvm_reg_block    blk     = get_parent();
      uvm_reg_map      top_map = get_root_map();
      uvm_reg_addr_t   addrs[];

      // if block is not locked, Xinit_address_mapX will resolve map when block is locked
      if (blk.is_locked()) begin

         // remove any existing cached addresses
         if (!info.unmapped) begin
           foreach (info.addr[i]) begin

              if (!top_map.m_regs_by_offset_wo.exists(info.addr[i])) begin
                 top_map.m_regs_by_offset.delete(info.addr[i]);
              end
              else begin
                 if (top_map.m_regs_by_offset[info.addr[i]] == rg) begin
                    top_map.m_regs_by_offset[info.addr[i]] = 
                      top_map.m_regs_by_offset_wo[info.addr[i]];
                    uvm_reg_read_only_cbs::remove(rg);
                    uvm_reg_write_only_cbs::remove(top_map.m_regs_by_offset[info.addr[i]]);
                 end
                 else begin
                    uvm_reg_write_only_cbs::remove(rg);
                    uvm_reg_read_only_cbs::remove(top_map.m_regs_by_offset[info.addr[i]]);
                 end
                 top_map.m_regs_by_offset_wo.delete(info.addr[i]);
              end
           end
         end

         // if we are remapping...
         if (!unmapped) begin
            string rg_acc = rg.Xget_fields_accessX(this);
            
            // get new addresses
            void'(get_physical_addresses(offset,0,rg.get_n_bytes(),addrs));

            // make sure they do not conflict with others
            foreach (addrs[i]) begin
               uvm_reg_addr_t addr = addrs[i];
               if (top_map.m_regs_by_offset.exists(addr)) begin

                  uvm_reg rg2 = top_map.m_regs_by_offset[addr];
                  string rg2_acc = rg2.Xget_fields_accessX(this);

                  // If the register at the same address is RO or WO
                  // and this register is WO or RO, this is OK
                  if (rg_acc == "RO" && rg2_acc == "WO") begin
                     top_map.m_regs_by_offset[addr]    = rg;
                     uvm_reg_read_only_cbs::add(rg);
                     top_map.m_regs_by_offset_wo[addr] = rg2;
                     uvm_reg_write_only_cbs::add(rg2);
                  end
                  else if (rg_acc == "WO" && rg2_acc == "RO") begin
                     top_map.m_regs_by_offset_wo[addr] = rg;
                     uvm_reg_write_only_cbs::add(rg);
                     uvm_reg_read_only_cbs::add(rg2);
                  end
                  else begin
                     string a;
                     a = $sformatf("%0h",addr);
                     `uvm_warning("RegModel", {"In map '",get_full_name(),"' register '",
                                               rg.get_full_name(), "' maps to same address as register '",
                                               top_map.m_regs_by_offset[addr].get_full_name(),"': 'h",a})
                  end
               end
               else
                  top_map.m_regs_by_offset[addr] = rg;

               foreach (top_map.m_mems_by_offset[range]) begin
                  if (addrs[i] >= range.min && addrs[i] <= range.max) begin
                    string a;
                    a = $sformatf("%0h",addrs[i]);
                    `uvm_warning("RegModel", {"In map '",get_full_name(),"' register '",
                        rg.get_full_name(), "' overlaps with address range of memory '",
                        top_map.m_mems_by_offset[range].get_full_name(),"': 'h",a})
                  end
               end
            end
            info.addr = addrs; // cache it
         end
      end

      if (unmapped) begin
        info.offset   = -1;
        info.unmapped = 1;
      end
      else begin
        info.offset   = offset;
        info.unmapped = 0;
      end
      
   end
endfunction


// add_mem

function void uvm_reg_map::add_mem(uvm_mem mem,
                                   uvm_reg_addr_t offset,
                                   string rights = "RW",
                                   bit unmapped=0,
                                   uvm_reg_frontdoor frontdoor=null);
   if (m_mems_info.exists(mem)) begin
      `uvm_error("RegModel", {"Memory '",mem.get_name(),
                 "' has already been added to map '",get_name(),"'"})
      return;
   end

   if (mem.get_parent() != get_parent()) begin
      `uvm_error("RegModel",
         {"Memory '",mem.get_full_name(),"' may not be added to address map '",
          get_full_name(),"' : they are not in the same block"})
      return;
   end
   
   mem.add_map(this);

   begin
   uvm_reg_map_info info = new;
   info.offset   = offset;
   info.rights   = rights;
   info.unmapped = unmapped;
   info.frontdoor = frontdoor;
   m_mems_info[mem] = info;
   end
endfunction: add_mem



// m_set_mem_offset

function void uvm_reg_map::m_set_mem_offset(uvm_mem mem, 
                                            uvm_reg_addr_t offset,
                                            bit unmapped);

   if (!m_mems_info.exists(mem)) begin
      `uvm_error("RegModel",
         {"Cannot modify offset of memory '",mem.get_full_name(),
         "' in address map '",get_full_name(),
         "' : memory not mapped in that address map"})
      return;
   end

   begin
      uvm_reg_map_info info    = m_mems_info[mem];
      uvm_reg_block    blk     = get_parent();
      uvm_reg_map      top_map = get_root_map();
      uvm_reg_addr_t   addrs[];

      // if block is not locked, Xinit_address_mapX will resolve map when block is locked
      if (blk.is_locked()) begin

         // remove any existing cached addresses
         if (!info.unmapped) begin
           foreach (top_map.m_mems_by_offset[range]) begin
              if (top_map.m_mems_by_offset[range] == mem)
                 top_map.m_mems_by_offset.delete(range);
           end
         end

         // if we are remapping...
         if (!unmapped) begin
            uvm_reg_addr_t addrs[],addrs_max[];
            uvm_reg_addr_t min, max, min2, max2;
            int unsigned stride;

            void'(get_physical_addresses(offset,0,mem.get_n_bytes(),addrs));
            min = (addrs[0] < addrs[addrs.size()-1]) ? addrs[0] : addrs[addrs.size()-1];
            min2 = addrs[0];

            void'(get_physical_addresses(offset,(mem.get_size()-1),
                                         mem.get_n_bytes(),addrs_max));
            max = (addrs_max[0] > addrs_max[addrs_max.size()-1]) ?
               addrs_max[0] : addrs_max[addrs_max.size()-1];
            max2 = addrs_max[0];
            // address interval between consecutive mem locations
            stride = mem.get_n_bytes()/get_addr_unit_bytes();

            // make sure new offset does not conflict with others
            foreach (top_map.m_regs_by_offset[reg_addr]) begin
               if (reg_addr >= min && reg_addr <= max) begin
                  string a,b;
                  a = $sformatf("[%0h:%0h]",min,max);
                  b = $sformatf("%0h",reg_addr);
                  `uvm_warning("RegModel", {"In map '",get_full_name(),"' memory '",
                      mem.get_full_name(), "' with range ",a,
                      " overlaps with address of existing register '",
                      top_map.m_regs_by_offset[reg_addr].get_full_name(),"': 'h",b})
               end
            end

            foreach (top_map.m_mems_by_offset[range]) begin
               if (min <= range.max && max >= range.max ||
                   min <= range.min && max >= range.min ||
                   min >= range.min && max <= range.max) begin
                 string a,b;
                 a = $sformatf("[%0h:%0h]",min,max);
                 b = $sformatf("[%0h:%0h]",range.min,range.max);
                 `uvm_warning("RegModel", {"In map '",get_full_name(),"' memory '",
                     mem.get_full_name(), "' with range ",a,
                     " overlaps existing memory with range '",
                     top_map.m_mems_by_offset[range].get_full_name(),"': ",b})
                 end
            end

            begin
              uvm_reg_map_addr_range range = '{ min, max, stride};
              top_map.m_mems_by_offset[range] = mem;
              info.addr  = addrs;
              info.mem_range = range;
            end

         end
      end

      if (unmapped) begin
        info.offset   = -1;
        info.unmapped = 1;
      end
      else begin
        info.offset   = offset;
        info.unmapped = 0;
      end
      
   end
endfunction


// add_submap

function void uvm_reg_map::add_submap (uvm_reg_map child_map,
                                       uvm_reg_addr_t offset);
   uvm_reg_map parent_map;

   if (child_map == null) begin
      `uvm_error("RegModel", {"Attempting to add NULL map to map '",get_full_name(),"'"})
      return;
   end

   parent_map = child_map.get_parent_map();

   // Cannot have more than one parent (currently)
   if (parent_map != null) begin
      `uvm_error("RegModel", {"Map '", child_map.get_full_name(),
                 "' is already a child of map '",
                 parent_map.get_full_name(),
                 "'. Cannot also be a child of map '",
                 get_full_name(),
                 "'"})
      return;
   end
  
   // this check means that n_bytes cannot change in a map hierarchy, that should work with 5446
   begin : n_bytes_match_check
      if (m_n_bytes > child_map.get_n_bytes(UVM_NO_HIER)) begin
         `uvm_warning("RegModel",
             $sformatf("Adding %0d-byte submap '%s' to %0d-byte parent map '%s'",
                       child_map.get_n_bytes(UVM_NO_HIER), child_map.get_full_name(),
                       m_n_bytes, get_full_name()))
      end
   end

   child_map.add_parent_map(this,offset);

   set_submap_offset(child_map, offset);

endfunction: add_submap


// reset

function void uvm_reg_map::reset(string kind = "SOFT");
   uvm_reg regs[$];

   get_registers(regs);

   foreach (regs[i]) begin
      regs[i].reset(kind);
   end
endfunction


// add_parent_map

function void uvm_reg_map::add_parent_map(uvm_reg_map parent_map, uvm_reg_addr_t offset);

   if (parent_map == null) begin
      `uvm_error("RegModel",
          {"Attempting to add NULL parent map to map '",get_full_name(),"'"})
      return;
   end

   if (m_parent_map != null) begin
      `uvm_error("RegModel",
          $sformatf("Map \"%s\" already a submap of map \"%s\" at offset 'h%h",
                    get_full_name(), m_parent_map.get_full_name(),
                    m_parent_map.get_submap_offset(this)))
      return;
   end

   m_parent_map = parent_map;
   parent_map.m_submaps[this] = offset;

endfunction: add_parent_map


// set_sequencer

function void uvm_reg_map::set_sequencer(uvm_sequencer_base sequencer,
                                         uvm_reg_adapter adapter=null);

   if (sequencer == null) begin
      `uvm_error("REG_NULL_SQR", "Null reference specified for bus sequencer")
      return;
   end

   if (adapter == null) begin
      `uvm_info("REG_NO_ADAPT", {"Adapter not specified for map '",get_full_name(),
        "'. Accesses via this map will send abstract 'uvm_reg_item' items to sequencer '",
        sequencer.get_full_name(),"'"},UVM_MEDIUM)
   end

   m_sequencer = sequencer;
   m_adapter = adapter;
endfunction



//------------
// get methods
//------------

// get_parent

function uvm_reg_block uvm_reg_map::get_parent();
  return m_parent;
endfunction


// get_parent_map

function uvm_reg_map uvm_reg_map::get_parent_map();
  return m_parent_map;
endfunction


// get_root_map

function uvm_reg_map uvm_reg_map::get_root_map();
   return (m_parent_map == null) ? this : m_parent_map.get_root_map();
endfunction: get_root_map


// get_base_addr

function uvm_reg_addr_t  uvm_reg_map::get_base_addr(uvm_hier_e hier=UVM_HIER);
  uvm_reg_map child = this;
  if (hier == UVM_NO_HIER || m_parent_map == null)
    return m_base_addr;
  get_base_addr = m_parent_map.get_submap_offset(this);
  get_base_addr += m_parent_map.get_base_addr(UVM_HIER);
endfunction


// get_n_bytes

function int unsigned uvm_reg_map::get_n_bytes(uvm_hier_e hier=UVM_HIER);
  if (hier == UVM_NO_HIER)
    return m_n_bytes;
  return m_system_n_bytes;
endfunction


// get_addr_unit_bytes

function int unsigned uvm_reg_map::get_addr_unit_bytes();
   return (m_byte_addressing) ? 1 : m_n_bytes;
endfunction


// get_endian

function uvm_endianness_e uvm_reg_map::get_endian(uvm_hier_e hier=UVM_HIER);
  if (hier == UVM_NO_HIER || m_parent_map == null)
    return m_endian;
  return m_parent_map.get_endian(hier);
endfunction


// get_sequencer

function uvm_sequencer_base uvm_reg_map::get_sequencer(uvm_hier_e hier=UVM_HIER);
  if (hier == UVM_NO_HIER || m_parent_map == null)
    return m_sequencer;
  return m_parent_map.get_sequencer(hier);
endfunction


// get_adapter

function uvm_reg_adapter uvm_reg_map::get_adapter(uvm_hier_e hier=UVM_HIER);
  if (hier == UVM_NO_HIER || m_parent_map == null)
    return m_adapter;
  return m_parent_map.get_adapter(hier);
endfunction


// get_submaps

function void uvm_reg_map::get_submaps(ref uvm_reg_map maps[$], input uvm_hier_e hier=UVM_HIER);

   foreach (m_submaps[submap])
     maps.push_back(submap);

   
   if (hier == UVM_HIER)
     foreach (m_submaps[submap_]) begin
       uvm_reg_map submap=submap_;
       submap.get_submaps(maps);
     end
endfunction


// get_registers

function void uvm_reg_map::get_registers(ref uvm_reg regs[$], input uvm_hier_e hier=UVM_HIER);

  foreach (m_regs_info[rg])
    regs.push_back(rg);

  if (hier == UVM_HIER)
    foreach (m_submaps[submap_]) begin
      uvm_reg_map submap=submap_;
      submap.get_registers(regs);
    end

endfunction


// get_fields

function void uvm_reg_map::get_fields(ref uvm_reg_field fields[$], input uvm_hier_e hier=UVM_HIER);

   foreach (m_regs_info[rg_]) begin
     uvm_reg rg = rg_;
     rg.get_fields(fields);
   end
   
   if (hier == UVM_HIER)
     foreach (this.m_submaps[submap_]) begin
       uvm_reg_map submap=submap_;
       submap.get_fields(fields);
     end

endfunction


// get_memories

function void uvm_reg_map::get_memories(ref uvm_mem mems[$], input uvm_hier_e hier=UVM_HIER);

   foreach (m_mems_info[mem])
     mems.push_back(mem);
    
   if (hier == UVM_HIER)
     foreach (m_submaps[submap_]) begin
       uvm_reg_map submap=submap_;
       submap.get_memories(mems);
     end

endfunction


// get_virtual_registers

function void uvm_reg_map::get_virtual_registers(ref uvm_vreg regs[$], input uvm_hier_e hier=UVM_HIER);

  uvm_mem mems[$];
  get_memories(mems,hier);

  foreach (mems[i])
    mems[i].get_virtual_registers(regs);

endfunction


// get_virtual_fields

function void uvm_reg_map::get_virtual_fields(ref uvm_vreg_field fields[$], input uvm_hier_e hier=UVM_HIER);

   uvm_vreg regs[$];
   get_virtual_registers(regs,hier);

   foreach (regs[i])
       regs[i].get_fields(fields);

endfunction



// get_full_name

function string uvm_reg_map::get_full_name();
   if (m_parent == null)
     return get_name();
   else
   	return {m_parent.get_full_name(), ".", get_name()};
endfunction


// get_mem_map_info

function uvm_reg_map_info uvm_reg_map::get_mem_map_info(uvm_mem mem, bit error=1);
  if (!m_mems_info.exists(mem)) begin
    if (error)
      `uvm_error("REG_NO_MAP",{"Memory '",mem.get_name(),"' not in map '",get_name(),"'"})
    return null;
  end
  return m_mems_info[mem];
endfunction


// get_reg_map_info

function uvm_reg_map_info uvm_reg_map::get_reg_map_info(uvm_reg rg, bit error=1);
  uvm_reg_map_info result;
  if (!m_regs_info.exists(rg)) begin
    if (error)
      `uvm_error("REG_NO_MAP",{"Register '",rg.get_name(),"' not in map '",get_name(),"'"})
    return null;
  end
  result = m_regs_info[rg];
  if(!result.is_initialized)
    `uvm_warning("RegModel",{"map '",get_name(),"' does not seem to be initialized correctly, check that the top register model is locked()"})
    
  return result;
endfunction


//----------
// Size and Overlap Detection
//---------

// set_base_addr

function void uvm_reg_map::set_base_addr(uvm_reg_addr_t offset);
   if (m_parent_map != null) begin
      m_parent_map.set_submap_offset(this, offset);
   end
   else begin
      m_base_addr = offset;
      if (m_parent.is_locked()) begin
         uvm_reg_map top_map = get_root_map();
         top_map.Xinit_address_mapX();
      end
   end
endfunction


// get_size

function int unsigned uvm_reg_map::get_size();

  int unsigned max_addr;
  int unsigned addr;

  // get max offset from registers
  foreach (m_regs_info[rg_]) begin
    uvm_reg rg = rg_;
    addr = m_regs_info[rg].offset + ((rg.get_n_bytes()-1)/m_n_bytes);
    if (addr > max_addr) max_addr = addr;
  end

  // get max offset from memories
  foreach (m_mems_info[mem_]) begin
    uvm_mem mem = mem_;
    addr = m_mems_info[mem].offset + (mem.get_size() * (((mem.get_n_bytes()-1)/m_n_bytes)+1)) -1;
    if (addr > max_addr) max_addr = addr;
  end

  // get max offset from submaps
  foreach (m_submaps[submap_]) begin
    uvm_reg_map submap=submap_;
    addr = m_submaps[submap] + submap.get_size();
    if (addr > max_addr) max_addr = addr;
  end

  return max_addr + 1;

endfunction



function void uvm_reg_map::Xverify_map_configX();
   // Make sure there is a generic payload sequence for each map
   // in the model and vice-versa if this is a root sequencer
   bit error;
   uvm_reg_map root_map = get_root_map();

   if (root_map.get_adapter() == null) begin
      `uvm_error("RegModel", {"Map '",root_map.get_full_name(),
                 "' does not have an adapter registered"})
      error++;
   end
   if (root_map.get_sequencer() == null) begin
      `uvm_error("RegModel", {"Map '",root_map.get_full_name(),
                 "' does not have a sequencer registered"})
      error++;
   end
   if (error) begin
      `uvm_fatal("RegModel", {"Must register an adapter and sequencer ",
                 "for each top-level map in RegModel model"})
      return;
   end

endfunction

// NOTE: if multiple memory addresses would fall into one bus word then the memory is addressed 'unpacked'
// ie. every memory location will get an own bus address (and bits on the bus larger than the memory width are discarded
// otherwise the memory access is 'packed' 
// 
// same as get_physical_addresses() but stops at the specified map
function int uvm_reg_map::get_physical_addresses_to_map(uvm_reg_addr_t     base_addr,
		uvm_reg_addr_t     mem_offset,
		int unsigned       n_bytes,  // number of bytes
		ref uvm_reg_addr_t addr[],
		input uvm_reg_map parent_map,
		ref int unsigned byte_offset,
		input uvm_mem mem=null
		);

	int bus_width = get_n_bytes(UVM_NO_HIER);
	uvm_reg_map  up_map;
	uvm_reg_addr_t  local_addr[];
	uvm_reg_addr_t lbase_addr;

//	`uvm_info("UVM/REG/ADDR",$sformatf("this=%p enter base=%0x mem_offset=%0d request=%0dbytes byte_enable=%0d byte-offset=%0d",
//		this,base_addr,mem_offset,n_bytes,m_byte_addressing,byte_offset),UVM_DEBUG)

//	`uvm_info("UVM/REG/ADDR",$sformatf("addressUnitBits=%0d busWidthBits=%0d",get_addr_unit_bytes()*8,bus_width*8),UVM_DEBUG)

	up_map = get_parent_map();
	lbase_addr = up_map==null ?  get_base_addr(UVM_NO_HIER): up_map.get_submap_offset(this);
//	`uvm_info("UVM/REG/ADDR",$sformatf("lbase =%0x",lbase_addr),UVM_DEBUG)

	if(up_map!=parent_map) begin
			uvm_reg_addr_t lb;
			// now just translate first address and request same number of bytes
			// may need to adjust addr,n_bytes if base_addr*AUB is not a multiple of upmap.AUB
			// addr=5,aub=8 and up.aub=16 and n_bytes=1 which is translated addr=2,n_bytes=2
			uvm_reg_addr_t laddr=lbase_addr + base_addr*get_addr_unit_bytes()/up_map.get_addr_unit_bytes();
			lb = (base_addr*get_addr_unit_bytes()) % up_map.get_addr_unit_bytes(); // byte offset of local address in terms of parent addresses
			byte_offset += lb;
		
			return up_map.get_physical_addresses_to_map(laddr, 0, n_bytes+lb, addr,parent_map,byte_offset);
	end else begin
			uvm_reg_addr_t lbase_addr2;
			// first need to compute set of addresses
			// each address is for one full bus width (the last beat may have less bytes to transfer)
			local_addr= new[ceil(n_bytes,bus_width)];

			lbase_addr2 = base_addr;
			if(mem_offset)					
				if(mem!=null && (mem.get_n_bytes() >= get_addr_unit_bytes())) begin // packed model
					lbase_addr2 = base_addr + mem_offset*mem.get_n_bytes()/get_addr_unit_bytes();
					byte_offset += (mem_offset*mem.get_n_bytes() % get_addr_unit_bytes());
				end	 else begin
					lbase_addr2 = base_addr + mem_offset;
				end

//			`uvm_info("UVM/REG/ADDR",$sformatf("gen addrs map-aub(bytes)=%0d addrs=%0d map-bus-width(bytes)=%0d lbase_addr2=%0x",
//				get_addr_unit_bytes(),local_addr.size(),bus_width,lbase_addr2),UVM_DEBUG)

			case (get_endian(UVM_NO_HIER))
				UVM_LITTLE_ENDIAN: begin
					foreach (local_addr[i]) begin
						local_addr[i] = lbase_addr2 + i*bus_width/get_addr_unit_bytes();
					end
				end
				UVM_BIG_ENDIAN: begin
					foreach (local_addr[i]) begin
						local_addr[i] = lbase_addr2 + (local_addr.size()-1-i)*bus_width/get_addr_unit_bytes() ;
					end
				end
				UVM_LITTLE_FIFO: begin
					foreach (local_addr[i]) begin
						local_addr[i] = lbase_addr2;
					end
				end
				UVM_BIG_FIFO: begin
					foreach (local_addr[i]) begin
						local_addr[i] = lbase_addr2;
					end
				end
				default: begin
					`uvm_error("UVM/REG/MAPNOENDIANESS",
						{"Map has no specified endianness. ",
							$sformatf("Cannot access %0d bytes register via its %0d byte \"%s\" interface",
								n_bytes, bus_width, get_full_name())})
				end
			endcase

//			foreach(local_addr[idx])
//				`uvm_info("UVM/REG/ADDR",$sformatf("local_addr idx=%0d addr=%0x",idx,local_addr[idx]),UVM_DEBUG)

			// now need to scale in terms of upper map

			addr = new [local_addr.size()] (local_addr);
			foreach(addr[idx])
				addr[idx] += lbase_addr;
			
//			foreach(addr[idx])
//				`uvm_info("UVM/REG/ADDR",$sformatf("top %0x:",addr[idx]),UVM_DEBUG)
			
		end	
endfunction

// NOTE the map argument could be made an arg with a default value. didnt do that to present the function signature
function int uvm_reg_map::get_physical_addresses(uvm_reg_addr_t     base_addr,
		uvm_reg_addr_t     mem_offset,
		int unsigned       n_bytes,  // number of bytes
		ref uvm_reg_addr_t addr[]);
		int unsigned skip;
		return get_physical_addresses_to_map(base_addr, mem_offset, n_bytes, addr,null,skip);
endfunction


//--------------
// Get-By-Offset
//--------------


// set_submap_offset

function void uvm_reg_map::set_submap_offset(uvm_reg_map submap, uvm_reg_addr_t offset);
  if (submap == null) begin
    `uvm_error("REG/NULL","set_submap_offset: submap handle is null")
    return;
  end
  m_submaps[submap] = offset;
  if (m_parent.is_locked()) begin
    uvm_reg_map root_map = get_root_map();
    root_map.Xinit_address_mapX();
  end
endfunction


// get_submap_offset

function uvm_reg_addr_t uvm_reg_map::get_submap_offset(uvm_reg_map submap);
  if (submap == null) begin
    `uvm_error("REG/NULL","set_submap_offset: submap handle is null")
    return -1;
  end
  if (!m_submaps.exists(submap)) begin
    `uvm_error("RegModel",{"Map '",submap.get_full_name(),
                      "' is not a submap of '",get_full_name(),"'"})
    return -1;
  end
  return m_submaps[submap];
endfunction


// get_reg_by_offset

function uvm_reg uvm_reg_map::get_reg_by_offset(uvm_reg_addr_t offset,
                                                bit            read = 1);
   if (!m_parent.is_locked()) begin
      `uvm_error("RegModel", $sformatf("Cannot get register by offset: Block %s is not locked.", m_parent.get_full_name()))
      return null;
   end

   if (!read && m_regs_by_offset_wo.exists(offset))
     return m_regs_by_offset_wo[offset];
   
   if (m_regs_by_offset.exists(offset))
     return m_regs_by_offset[offset];

   return null;
endfunction


// get_mem_by_offset

function uvm_mem uvm_reg_map::get_mem_by_offset(uvm_reg_addr_t offset);
   if (!m_parent.is_locked()) begin
      `uvm_error("RegModel", $sformatf("Cannot memory register by offset: Block %s is not locked.", m_parent.get_full_name()))
      return null;
   end

   foreach (m_mems_by_offset[range]) begin
      if (range.min <= offset && offset <= range.max) begin
         return m_mems_by_offset[range];
      end
   end
   
   return null;
endfunction


// Xinit_address_mapX

function void uvm_reg_map::Xinit_address_mapX();

   int unsigned bus_width;

   uvm_reg_map top_map = get_root_map();

   if (this == top_map) begin
     top_map.m_regs_by_offset.delete();
     top_map.m_regs_by_offset_wo.delete();
     top_map.m_mems_by_offset.delete();
   end

   foreach (m_submaps[l]) begin
     uvm_reg_map map=l;
     map.Xinit_address_mapX();
   end

   foreach (m_regs_info[rg_]) begin
     uvm_reg rg = rg_;
     m_regs_info[rg].is_initialized=1;
     if (!m_regs_info[rg].unmapped) begin
        string rg_acc = rg.Xget_fields_accessX(this);
       uvm_reg_addr_t addrs[];
        
       bus_width = get_physical_addresses(m_regs_info[rg].offset,0,rg.get_n_bytes(),addrs);
        
       foreach (addrs[i]) begin
         uvm_reg_addr_t addr = addrs[i];

         if (top_map.m_regs_by_offset.exists(addr) && (top_map.m_regs_by_offset[addr] != rg)) begin

            uvm_reg rg2 = top_map.m_regs_by_offset[addr];
            string rg2_acc = rg2.Xget_fields_accessX(this);
            
            // If the register at the same address is RO or WO
            // and this register is WO or RO, this is OK
            if (rg_acc == "RO" && rg2_acc == "WO") begin
               top_map.m_regs_by_offset[addr]    = rg;
               uvm_reg_read_only_cbs::add(rg);
               top_map.m_regs_by_offset_wo[addr] = rg2;
               uvm_reg_write_only_cbs::add(rg2);
            end
            else if (rg_acc == "WO" && rg2_acc == "RO") begin
               top_map.m_regs_by_offset_wo[addr] = rg;
               uvm_reg_write_only_cbs::add(rg);
               uvm_reg_read_only_cbs::add(rg2);
            end
            else begin
               string a;
               a = $sformatf("%0h",addr);
               `uvm_warning("RegModel", {"In map '",get_full_name(),"' register '",
                                         rg.get_full_name(), "' maps to same address as register '",
                                         top_map.m_regs_by_offset[addr].get_full_name(),"': 'h",a})
            end
         end
         else
            top_map.m_regs_by_offset[addr] = rg;
          
         foreach (top_map.m_mems_by_offset[range]) begin
           if (addr >= range.min && addr <= range.max) begin
             string a,b;
             a = $sformatf("%0h",addr);
             b = $sformatf("[%0h:%0h]",range.min,range.max);
             `uvm_warning("RegModel", {"In map '",get_full_name(),"' register '",
                 rg.get_full_name(), "' with address ",a,
                 "maps to same address as memory '",
                 top_map.m_mems_by_offset[range].get_full_name(),"': ",b})
             end
         end
       end
       m_regs_info[rg].addr = addrs;
     end
   end

   foreach (m_mems_info[mem_]) begin
     uvm_mem mem = mem_;
     if (!m_mems_info[mem].unmapped) begin

       uvm_reg_addr_t addrs[],addrs_max[];
       uvm_reg_addr_t min, max, min2, max2;
       int unsigned stride;
	   int unsigned bo;

       bus_width = get_physical_addresses_to_map(m_mems_info[mem].offset,0,mem.get_n_bytes(),addrs,null,bo,mem);
       min = (addrs[0] < addrs[addrs.size()-1]) ? addrs[0] : addrs[addrs.size()-1];
       
//	foreach(addrs[idx])
//	       `uvm_info("UVM/REG/ADDR",$sformatf("idx%0d addr=%0x",idx,addrs[idx]),UVM_DEBUG)

       void'(get_physical_addresses_to_map(m_mems_info[mem].offset,(mem.get_size()-1),mem.get_n_bytes(),addrs_max,null,bo,mem));
       max = (addrs_max[0] > addrs_max[addrs_max.size()-1]) ? addrs_max[0] : addrs_max[addrs_max.size()-1];
	   stride = mem.get_n_bytes()/get_addr_unit_bytes(); 
	    
//       foreach(addrs_max[idx])
//	       `uvm_info("UVM/REG/ADDR",$sformatf("idx%0d addr=%0x",idx,addrs_max[idx]),UVM_DEBUG)
	          
//	   `uvm_info("UVM/REG/ADDR",$sformatf("mem %0d x %0d in map aub(bytes)=%0d n_bytes=%0d",mem.get_size(),mem.get_n_bits(),
//		   get_addr_unit_bytes(),get_n_bytes(UVM_NO_HIER)),UVM_DEBUG)
 
 /*
        if (uvm_report_enabled(UVM_DEBUG, UVM_INFO,"UVM/REG/ADDR")) begin
	   		uvm_reg_addr_t ad[];
	       for(int idx=0;idx<mem.get_size();idx++) begin
		   		void'(get_physical_addresses_to_map(m_mems_info[mem].offset,idx,1,ad,null,bo,mem));
		   
		  		`uvm_info("UVM/REG/ADDR",$sformatf("idx%d addr=%x",idx,ad[0]),UVM_DEBUG)
	       end	
	   end   
*/

		if(mem.get_n_bytes()<get_addr_unit_bytes())
			`uvm_warning("UVM/REG/ADDR",$sformatf("this version of UVM does not properly support memories with \
a smaller word width than the enclosing map. map %s has n_bytes=%0d aub=%0d while the mem has get_n_bytes %0d. \
multiple memory words fall into one bus address. if that happens memory addressing will be unpacked.",
					get_full_name(),get_n_bytes(UVM_NO_HIER),get_addr_unit_bytes(),mem.get_n_bytes()))

		if(mem.get_n_bytes() > get_addr_unit_bytes())
			if(mem.get_n_bytes() % get_addr_unit_bytes())  begin
				`uvm_warning("UVM/REG/ADDR",$sformatf("memory %s is not matching the word width of the enclosing map %s  \
(one memory word not fitting into k map addresses)",
					mem.get_full_name(),get_full_name()))
			end	

		if(mem.get_n_bytes() < get_addr_unit_bytes())
			if(get_addr_unit_bytes() % mem.get_n_bytes()) 
				`uvm_warning("UVM/REG/ADDR",$sformatf("the memory %s is not matching the word width of the enclosing map %s  \
(one map address doesnt cover k memory words)",
					mem.get_full_name(),get_full_name()))

		if(mem.get_n_bits() % 8)
			`uvm_warning("UVM/REG/ADDR",$sformatf("this implementation of UVM requires memory words to be k*8 bits (mem %s \
has %0d bit words)",mem.get_full_name(),mem.get_n_bits()))
		
       foreach (top_map.m_regs_by_offset[reg_addr]) begin
         if (reg_addr >= min && reg_addr <= max) begin
           string a;
           a = $sformatf("%0h",reg_addr);
           `uvm_warning("RegModel", {"In map '",get_full_name(),"' memory '",
               mem.get_full_name(), "' maps to same address as register '",
               top_map.m_regs_by_offset[reg_addr].get_full_name(),"': 'h",a})
         end
       end

       foreach (top_map.m_mems_by_offset[range]) begin
         if (min <= range.max && max >= range.max ||
             min <= range.min && max >= range.min ||
             min >= range.min && max <= range.max) 
	      	if(top_map.m_mems_by_offset[range]!=mem) // do not warn if the same mem is located at the same address via different paths
	         begin
           string a;
           a = $sformatf("[%0h:%0h]",min,max);
           `uvm_warning("RegModel", {"In map '",get_full_name(),"' memory '",
               mem.get_full_name(), "' overlaps with address range of memory '",
               top_map.m_mems_by_offset[range].get_full_name(),"': 'h",a})
           end
       end

       begin
         uvm_reg_map_addr_range range = '{ min, max, stride};
         top_map.m_mems_by_offset[ range ] = mem;
         m_mems_info[mem].addr  = addrs;
         m_mems_info[mem].mem_range = range;
       end
     end
   end

   // If the block has no registers or memories,
   // bus_width won't be set
   if (bus_width == 0) bus_width = m_n_bytes;

   m_system_n_bytes = bus_width;
endfunction


//-----------
// Bus Access
//-----------

function void uvm_reg_map::Xget_bus_infoX(uvm_reg_item rw,
                                          output uvm_reg_map_info map_info,
                                          output int size,
                                          output int lsb,
                                          output int addr_skip);

  if (rw.element_kind == UVM_MEM) begin
    uvm_mem mem;
    if(rw.element == null || !$cast(mem,rw.element))
      `uvm_fatal("REG/CAST", {"uvm_reg_item 'element_kind' is UVM_MEM, ",
                 "but 'element' does not point to a memory: ",rw.get_name()})
    map_info = get_mem_map_info(mem);
    size = mem.get_n_bits();
  end
  else if (rw.element_kind == UVM_REG) begin
    uvm_reg rg;
    if(rw.element == null || !$cast(rg,rw.element))
      `uvm_fatal("REG/CAST", {"uvm_reg_item 'element_kind' is UVM_REG, ",
                 "but 'element' does not point to a register: ",rw.get_name()})
    map_info = get_reg_map_info(rg);
    size = rg.get_n_bits();
  end
  else if (rw.element_kind == UVM_FIELD) begin
    uvm_reg_field field;
    if(rw.element == null || !$cast(field,rw.element))
      `uvm_fatal("REG/CAST", {"uvm_reg_item 'element_kind' is UVM_FIELD, ",
                 "but 'element' does not point to a field: ",rw.get_name()})
    map_info = get_reg_map_info(field.get_parent());
    size = field.get_n_bits();
    lsb = field.get_lsb_pos();
    addr_skip = lsb/(get_n_bytes()*8);
  end
endfunction




// do_write(uvm_reg_item rw)

task uvm_reg_map::do_write(uvm_reg_item rw);

  uvm_sequence_base tmp_parent_seq;
  uvm_reg_map system_map = get_root_map();
  uvm_reg_adapter adapter = system_map.get_adapter();
  uvm_sequencer_base sequencer = system_map.get_sequencer();
  uvm_reg_seq_base parent_proxy;

  if (adapter != null && adapter.parent_sequence != null) begin
    uvm_object o;
    uvm_sequence_base seq;
    o = adapter.parent_sequence.clone();
    if (o == null)
      `uvm_fatal("REG/CLONE",
                 {"failed to clone adapter's parent sequence: '",
                  adapter.parent_sequence.get_full_name(),
                  "' (of type '",
                  adapter.parent_sequence.get_type_name(),
                 "')"})
    if (!$cast(seq, o))
      `uvm_fatal("REG/CAST",
                 {"failed to cast: '",
                  o.get_full_name(), 
                  "' (of type '",
                  o.get_type_name(),
                  "') to uvm_sequence_base!"})
    seq.set_parent_sequence(rw.parent);
    rw.parent = seq;
    tmp_parent_seq = seq;
  end

  if (rw.parent == null) begin
    parent_proxy = new("default_parent_seq");
    rw.parent = parent_proxy;     
    tmp_parent_seq = rw.parent;
  end

  if (adapter == null) begin
    uvm_event#(uvm_object) end_event ;
    uvm_event_pool ep;
    ep = rw.get_event_pool();
    end_event = ep.get("end") ;
    rw.set_sequencer(sequencer);
    rw.parent.start_item(rw,rw.prior);
    rw.parent.finish_item(rw);
    end_event.wait_on();
  end
  else begin
    do_bus_write(rw, sequencer, adapter);
  end

  if (tmp_parent_seq != null)
    sequencer.m_sequence_exiting(tmp_parent_seq);

endtask


// do_read(uvm_reg_item rw)

task uvm_reg_map::do_read(uvm_reg_item rw);

  uvm_sequence_base tmp_parent_seq;
  uvm_reg_map system_map = get_root_map();
  uvm_reg_adapter adapter = system_map.get_adapter();
  uvm_sequencer_base sequencer = system_map.get_sequencer();
  uvm_reg_seq_base parent_proxy;

  if (adapter != null && adapter.parent_sequence != null) begin
    uvm_object o;
    uvm_sequence_base seq;
    o = adapter.parent_sequence.clone();
    if (o == null)
      `uvm_fatal("REG/CLONE",
                 {"failed to clone adapter's parent sequence: '",
                  adapter.parent_sequence.get_full_name(),
                  "' (of type '",
                  adapter.parent_sequence.get_type_name(),
                 "')"})
    if (!$cast(seq, o))
      `uvm_fatal("REG/CAST",
                 {"failed to cast: '",
                  o.get_full_name(), 
                  "' (of type '",
                  o.get_type_name(),
                  "') to uvm_sequence_base!"})
    seq.set_parent_sequence(rw.parent);
    rw.parent = seq;
    tmp_parent_seq = seq;
  end

  if (rw.parent == null) begin
    parent_proxy = new("default_parent_seq");   
    rw.parent = parent_proxy;  
    tmp_parent_seq = rw.parent;
  end

  if (adapter == null) begin
    uvm_event#(uvm_object) end_event ;
    uvm_event_pool ep;
    ep = rw.get_event_pool();
    end_event = ep.get("end") ;
    rw.set_sequencer(sequencer);
    rw.parent.start_item(rw,rw.prior);
    rw.parent.finish_item(rw);
    end_event.wait_on();
  end
  else begin
    do_bus_read(rw, sequencer, adapter);
  end

  if (tmp_parent_seq != null)
    sequencer.m_sequence_exiting(tmp_parent_seq);

endtask


// do_bus_write

task uvm_reg_map::do_bus_write (uvm_reg_item rw,
                                uvm_sequencer_base sequencer,
                                uvm_reg_adapter adapter);

	do_bus_access(rw, sequencer, adapter);
endtask

task uvm_reg_map::perform_accesses(ref uvm_reg_bus_op    accesses[$],
		input uvm_reg_item rw,
		input uvm_reg_adapter adapter,
		input  uvm_sequencer_base sequencer);
	
	string op;
	uvm_reg_data_logic_t data;
        uvm_endianness_e endian;
	
	op=(rw.kind inside {UVM_READ,UVM_BURST_READ}) ? "Read" : "Wrote";
        endian=get_endian(UVM_NO_HIER);
  
	    // if set utilize the order policy
    if(policy!=null)
        policy.order(accesses);
    
    // perform accesses
    foreach(accesses[i]) begin     
      uvm_reg_bus_op rw_access=accesses[i];  
      uvm_sequence_item bus_req;

      if ((rw_access.kind == UVM_WRITE) && (endian == UVM_BIG_ENDIAN)) begin
        { >> { rw_access.data }} = { << byte { rw_access.data}};
      end
          
      adapter.m_set_item(rw);
      bus_req = adapter.reg2bus(rw_access);
      adapter.m_set_item(null);
      
      if (bus_req == null)
        `uvm_fatal("RegMem",{"adapter [",adapter.get_name(),"] didnt return a bus transaction"})
      
      bus_req.set_sequencer(sequencer);
      rw.parent.start_item(bus_req,rw.prior);

      if (rw.parent != null && i == 0)
        rw.parent.mid_do(rw);

      rw.parent.finish_item(bus_req);
      begin
        uvm_event#(uvm_object) end_event ;
	uvm_event_pool ep;
	ep = bus_req.get_event_pool();
        end_event = ep.get("end") ;
        end_event.wait_on();
      end

      if (adapter.provides_responses) begin
        uvm_sequence_item bus_rsp;
        uvm_access_e op;
        // TODO: need to test for right trans type, if not put back in q
        rw.parent.get_base_response(bus_rsp,bus_req.get_transaction_id());
        adapter.bus2reg(bus_rsp,rw_access);
      end
      else begin
        adapter.bus2reg(bus_req,rw_access);
      end

      if ((rw_access.kind == UVM_READ) && (endian == UVM_BIG_ENDIAN)) begin
        { >> { rw_access.data }} = { << byte { rw_access.data}};
      end

      rw.status = rw_access.status;

      begin
       data = rw_access.data & ((1<<get_n_bytes()*8)-1); // mask the upper bits
      
      if(rw.kind inside {UVM_READ,UVM_BURST_READ})
      	if (rw.status == UVM_IS_OK && (^data) === 1'bx)
	      rw.status = UVM_HAS_X;
      	
      	rw_access.data=data;    	
      end	

      `uvm_info("UVM/REG/ADDR",
         $sformatf("%s 'h%0h at 'h%0h via map \"%s\": %s...",op,
            rw_access.data, rw_access.addr, rw.map.get_full_name(), rw.status.name()), UVM_FULL)

      if (rw.status == UVM_NOT_OK)
         break;
        
      if (rw.parent != null && i == accesses.size()-1)
        rw.parent.post_do(rw);
        
      accesses[i]=rw_access;
    end	
endtask

// do_bus_read

task uvm_reg_map::do_bus_access (uvm_reg_item rw,
                               uvm_sequencer_base sequencer,
                               uvm_reg_adapter adapter);

	uvm_reg_addr_t     addrs[$];
	uvm_reg_map        system_map = get_root_map();
	int unsigned       bus_width  = get_n_bytes();
	uvm_reg_byte_en_t  byte_en    = -1;
	uvm_reg_map_info   map_info;
	int                n_bits;
	int                lsb;
	int                skip;
	int unsigned       curr_byte;
	int                n_access_extra, n_access;
	uvm_reg_bus_op    accesses[$];
//	int n_bits_init;
	string op;
	uvm_reg_addr_t adr[];
	int unsigned byte_offset;
	int unsigned num_stream_bytes;
	int unsigned n_bytes;
	int unsigned bytes_per_value;
	int unsigned bit_shift;
	int unsigned extra_byte;
	
	Xget_bus_infoX(rw, map_info, n_bits, lsb, skip);
	addrs=map_info.addr;
	op = (rw.kind inside {UVM_READ,UVM_BURST_READ} ? "Reading" : "Writing");

	case(rw.element_kind)
		UVM_MEM: begin
			uvm_mem mem;
			$cast(mem,rw.element);
			void'(get_physical_addresses_to_map(m_mems_info[mem].offset,rw.offset,rw.value.size()*mem.get_n_bytes(),adr,null,byte_offset,mem));
			num_stream_bytes =rw.value.size()*mem.get_n_bytes();
			n_bytes=mem.get_n_bytes();
			bytes_per_value=mem.get_n_bytes();
		end	
		UVM_FIELD: begin
			uvm_reg_field f;
			uvm_reg_addr_t ad;
			$cast(f,rw.element);

			// adjust adr bit skipped bytes; still need to shift data by byte fractions (lsb)
			void'(get_physical_addresses_to_map(m_regs_info[f.get_parent()].offset+skip,0,ceil(f.get_n_bits(),8),adr,null,byte_offset));
			num_stream_bytes =ceil(f.get_n_bits(),8);
			n_bytes=get_n_bytes(UVM_NO_HIER);	
			bytes_per_value=ceil(f.get_n_bits(),8);
			bit_shift=lsb % (get_n_bytes()*8);
			if(((bit_shift+f.get_n_bits()) /8) !=  ((f.get_n_bits()) /8))
				extra_byte=1;
//			`uvm_info("UVM/REG/ADDR",$sformatf("need to byte skip %0d and bit shift %0d",skip,bit_shift),UVM_DEBUG)
		end	
		UVM_REG: begin
			uvm_reg r;
			uvm_reg_addr_t ad;
			$cast(r,rw.element);

			void'(get_physical_addresses_to_map(m_regs_info[r].offset,0,r.get_n_bytes(),adr,null,byte_offset));
			num_stream_bytes =r.get_n_bytes();
			n_bytes=get_n_bytes(UVM_NO_HIER);
			bytes_per_value=r.get_n_bytes();
		end	
	endcase
	
	begin
		bit be[$];
		byte p[$];

		// adjust bytes if there is a leading bit shift
		num_stream_bytes+=extra_byte;

		repeat(byte_offset) be.push_back(1'b0); // TODO rewrite
		repeat(num_stream_bytes) be.push_back(1'b1);
		repeat(bus_width) be.push_back(1'b0);

		// now shift data to match the alignment
		repeat(byte_offset) p.push_back(8'b0);
		foreach(rw.value[idx])
			for(int i=0;i<bytes_per_value;i++)
				p.push_back(rw.value[idx][8*i+:8]);
			

		if(bit_shift) begin
			uvm_reg_data_t ac;
			ac='0;
			foreach(p[idx]) begin
				uvm_reg_data_t n;
				n = (ac | (p[idx] << bit_shift)) & 'hff;
				ac=(p[idx]>>bit_shift) & 'hff;
				p[idx]=n;
			end
			if(extra_byte)
				p.push_back(ac);
		end	

/*
		 if (uvm_report_enabled(UVM_DEBUG, UVM_INFO, "UVM/REG/ADDR")) begin
		foreach(be[idx])
			`uvm_info("UVM/REG/ADDR",$sformatf("idx %0d en=%0d",idx,be[idx]),UVM_DEBUG)

		foreach(adr[idx])
			`uvm_info("UVM/REG/ADDR",$sformatf("mem-adr %0x byte-offset=%0d",adr[idx],byte_offset),UVM_DEBUG)

		foreach(p[idx])
			`uvm_info("UVM/REG/ADDR",$sformatf("idx %0d data=%x enable=%0d",idx,p[idx],be[idx]),UVM_DEBUG)
		
		foreach(rw.value[idx])
			`uvm_info("UVM/REG/ADDR",$sformatf("original idx=%0d %0x",idx,rw.value[idx]),UVM_DEBUG)
		
		end
*/
		
		// transform into accesses per address
		accesses.delete();
		foreach(adr[i]) begin	
			uvm_reg_bus_op rw_access;
			uvm_reg_data_t data;

			for(int i0=0;i0<bus_width;i0++)
				data[i0*8+:8]=p[i*bus_width+i0];

			`uvm_info("UVM/REG/ADDR",
				$sformatf("%s 'h%0h at 'h%0h via map \"%s\"...",op,
					data, adr[i], rw.map.get_full_name()), UVM_FULL)

			for (int z=0;z<bus_width;z++)
				rw_access.byte_en[z] = be[bus_width*i+z];

			rw_access.kind    = rw.kind;
			rw_access.addr    = adr[i];
			rw_access.data    = data;
			
			rw_access.n_bits=8*bus_width;
			for(int i=bus_width-1;i>=0;i--) begin
				if(rw_access.byte_en[i]==0)
					rw_access.n_bits-=8;
				else
					break;
			end	

			accesses.push_back(rw_access);
		end
		
		perform_accesses(accesses, rw, adapter, sequencer);

		// for reads copy back to rw.value
		if(rw.kind inside {UVM_READ,UVM_BURST_READ}) begin
				p.delete();
				foreach(accesses[i0])
				   for(int i1=0;i1<bus_width;i1++)
					   p.push_back(accesses[i0].data[i1*8+:8]);

				repeat(byte_offset) void'(p.pop_front());
				foreach(rw.value[i]) rw.value[i]=0;

		if(bit_shift) begin
			uvm_reg_data_t ac;
			ac='0;
			for(int i=0;i<p.size();i++) begin
				byte nv;
				nv=(p[i] >> bit_shift);
				if(i!=p.size()-1)
					nv |= (p[i+1]<<bit_shift);
				
				p[i] = nv;
			end
			if(extra_byte)
				void'(p.pop_back());
		end	

				foreach(rw.value[idx])
					for(int i0=0;i0<bytes_per_value;i0++)
						rw.value[idx][i0*8+:8]= p[idx*bytes_per_value+i0];
					
				if(rw.element_kind == UVM_FIELD) begin
						uvm_reg_field f;
						uvm_reg_data_t m;
						$cast(f,rw.element);
						
						m = (1 << f.get_n_bits())-1;
						foreach(rw.value[idx])
							rw.value[idx] &= m;
				end						

/*
				if (uvm_report_enabled(UVM_DEBUG, UVM_INFO, "UVM/REG/ADDR")) 
					foreach(rw.value[idx])
			        `	uvm_info("UVM/REG/ADDR",$sformatf("read return idx=%0d %0x",idx,rw.value[idx]),UVM_DEBUG)
*/
			        
		end
	end
endtask

task uvm_reg_map::do_bus_read (uvm_reg_item rw,
                               uvm_sequencer_base sequencer,
                               uvm_reg_adapter adapter);

do_bus_access(rw, sequencer, adapter);

endtask: do_bus_read



//-------------
// Standard Ops
//-------------

// do_print

function void uvm_reg_map::do_print (uvm_printer printer);
   uvm_reg  regs[$];
   uvm_vreg vregs[$];
   uvm_mem  mems[$];
   uvm_endianness_e endian;
   uvm_reg_map maps[$];
   string prefix;
   uvm_sequencer_base sqr=get_sequencer();
  
   super.do_print(printer);

   endian = get_endian(UVM_NO_HIER);

   printer.print_generic("endian","",-2,endian.name()); 
   printer.print_field_int("n_bytes", get_n_bytes(UVM_NO_HIER), 64, UVM_DEC);
   printer.print_field_int("byte addressing",get_addr_unit_bytes()==1,64,UVM_DEC);

   if(sqr!=null)
    printer.print_generic("effective sequencer",sqr.get_type_name(),-2,sqr.get_full_name());     
             
   get_registers(regs,UVM_NO_HIER);
   foreach (regs[j]) 
        printer.print_generic(regs[j].get_name(), regs[j].get_type_name(),-2,$sformatf("@%0d +'h%0x",regs[j].get_inst_id(),regs[j].get_address(this)));
   
   
   get_memories(mems);
   foreach (mems[j]) 
        printer.print_generic(mems[j].get_name(), mems[j].get_type_name(),-2,$sformatf("@%0d +'h%0x",mems[j].get_inst_id(),mems[j].get_address(0,this)));
   
   get_virtual_registers(vregs);
   foreach (vregs[j]) 
        printer.print_generic(vregs[j].get_name(), vregs[j].get_type_name(),-2,$sformatf("@%0d +'h%0x",vregs[j].get_inst_id(),vregs[j].get_address(0,this)));
    
   get_submaps(maps);
   foreach (maps[j]) 
        printer.print_object(maps[j].get_name(),maps[j]);
endfunction

// convert2string

function string uvm_reg_map::convert2string();
   uvm_reg  regs[$];
   uvm_vreg vregs[$];
   uvm_mem  mems[$];
   uvm_endianness_e endian;
   string prefix;

   $sformat(convert2string, "%sMap %s", prefix, get_full_name());
   endian = get_endian(UVM_NO_HIER);
   $sformat(convert2string, "%s -- %0d bytes (%s)", convert2string,
            get_n_bytes(UVM_NO_HIER), endian.name());
   get_registers(regs);
   foreach (regs[j]) begin
      $sformat(convert2string, "%s\n%s", convert2string,
               regs[j].convert2string());//{prefix, "   "}, this));
   end
   get_memories(mems);
   foreach (mems[j]) begin
      $sformat(convert2string, "%s\n%s", convert2string,
               mems[j].convert2string());//{prefix, "   "}, this));
   end
   get_virtual_registers(vregs);
   foreach (vregs[j]) begin
      $sformat(convert2string, "%s\n%s", convert2string,
               vregs[j].convert2string());//{prefix, "   "}, this));
   end
endfunction


// clone

function uvm_object uvm_reg_map::clone();
   `uvm_fatal("UVM/REGMAP/NOCLONE","uvm_reg_map doesnt support clone()")
   return null;
endfunction


// do_copy

function void uvm_reg_map::do_copy (uvm_object rhs);
  //uvm_reg_map rhs_;
  //if (!$cast(seq, o))
  //  `uvm_fatal(...)

  //rhs_.regs = regs;
  //rhs_.mems = mems;
  //rhs_.vregs = vregs;
  //rhs_.blks = blks;
  //... and so on
endfunction

