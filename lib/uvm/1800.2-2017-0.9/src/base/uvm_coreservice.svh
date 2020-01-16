//----------------------------------------------------------------------
// Copyright 2014 Mentor Graphics Corporation
// Copyright 2015 Analog Devices, Inc.
// Copyright 2014 Semifore
// Copyright 2018 Intel Corporation
// Copyright 2018 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2014-2017 Cisco Systems, Inc.
// Copyright 2017 Verific
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------
typedef class uvm_factory;
typedef class uvm_default_factory;
typedef class uvm_report_server;
typedef class uvm_default_report_server;
typedef class uvm_root;
typedef class uvm_visitor;
typedef class uvm_component_name_check_visitor;
typedef class uvm_component;
typedef class uvm_comparer;
typedef class uvm_copier;
typedef class uvm_packer;
typedef class uvm_printer;
typedef class uvm_table_printer;

typedef class uvm_tr_database;
typedef class uvm_text_tr_database;
typedef class uvm_resource_pool;
`ifdef UVM_ENABLE_DEPRECATED_API
typedef class uvm_object;
`endif


typedef class uvm_default_coreservice_t;

// @uvm-ieee 1800.2-2017 auto F.4.1.1
virtual class uvm_coreservice_t;

	// @uvm-ieee 1800.2-2017 auto F.4.1.4.2
	pure virtual function uvm_factory get_factory();


	// @uvm-ieee 1800.2-2017 auto F.4.1.4.3
	pure virtual function void set_factory(uvm_factory f);


	// @uvm-ieee 1800.2-2017 auto F.4.1.4.4
	pure virtual function uvm_report_server get_report_server();


	// @uvm-ieee 1800.2-2017 auto F.4.1.4.5
	pure virtual function void set_report_server(uvm_report_server server);


	// @uvm-ieee 1800.2-2017 auto F.4.1.4.6
	pure virtual function uvm_tr_database get_default_tr_database();


	// @uvm-ieee 1800.2-2017 auto F.4.1.4.7
	pure virtual function void set_default_tr_database(uvm_tr_database db);


	// @uvm-ieee 1800.2-2017 auto F.4.1.4.9
	pure virtual function void set_component_visitor(uvm_visitor#(uvm_component) v);

	pure virtual function uvm_visitor#(uvm_component) get_component_visitor();


	// @uvm-ieee 1800.2-2017 auto F.4.1.4.1
	pure virtual function uvm_root get_root();

	// @uvm-ieee 1800.2-2017 auto F.4.1.4.10
	pure virtual function void set_phase_max_ready_to_end(int max);

	// @uvm-ieee 1800.2-2017 auto F.4.1.4.11
	pure virtual function int get_phase_max_ready_to_end();

	// @uvm-ieee 1800.2-2017 auto F.4.1.4.12
	pure virtual function void set_default_printer(uvm_printer printer);

	// @uvm-ieee 1800.2-2017 auto F.4.1.4.13
	pure virtual function uvm_printer get_default_printer();

	// @uvm-ieee 1800.2-2017 auto F.4.1.4.14
	pure virtual function void set_default_packer(uvm_packer packer);

	// @uvm-ieee 1800.2-2017 auto F.4.1.4.15
	pure virtual function uvm_packer get_default_packer();

	// @uvm-ieee 1800.2-2017 auto F.4.1.4.16
	pure virtual function void set_default_comparer(uvm_comparer comparer);

	// @uvm-ieee 1800.2-2017 auto F.4.1.4.17
	pure virtual function uvm_comparer get_default_comparer();

	pure virtual function int unsigned get_global_seed();


	// @uvm-ieee 1800.2-2017 auto F.4.1.4.18
	pure virtual function void set_default_copier(uvm_copier copier);

	// @uvm-ieee 1800.2-2017 auto F.4.1.4.19
	pure virtual function uvm_copier get_default_copier();



        // Function: get_uvm_seeding
        // Returns the current UVM seeding ~enable~ value, as set by
        // <set_uvm_seeding>.
        //
        // This pure virtual method provides access to the
        // <uvm_default_coreservice_t::get_uvm_seeding> method as described
        // by F.4.3.
        //
        // It was omitted from the P1800.2 LRM, and is being tracked
        // in Mantis 6417
        pure virtual function bit get_uvm_seeding();

        // Function: set_uvm_seeding
        // Sets the current UVM seeding ~enable~ value, as retrieved by
        // <get_uvm_seeding>.
        //
        // This pure virtual method provides access to the
        // <uvm_default_coreservice_t::set_uvm_seeding> method as described
        // by F.4.4.
        //
        // It was omitted from the P1800.2 LRM, and is being tracked
        // in Mantis 6417
        pure virtual function void set_uvm_seeding(bit enable);
   
	// @uvm-ieee 1800.2-2017 auto F.4.1.4.21
	pure virtual function void set_resource_pool (uvm_resource_pool pool);

	// @uvm-ieee 1800.2-2017 auto F.4.1.4.22
	pure virtual function uvm_resource_pool get_resource_pool();

	// @uvm-ieee 1800.2-2017 auto F.4.1.4.23
	pure virtual function void set_resource_pool_default_precedence(int unsigned precedence);

	pure virtual function int unsigned get_resource_pool_default_precedence();

	local static uvm_coreservice_t inst;

	// @uvm-ieee 1800.2-2017 auto F.4.1.3
	static function uvm_coreservice_t get();
		if(inst==null)
			uvm_init(null);
		
		return inst;
	endfunction // get

	static function void set(uvm_coreservice_t cs);
		inst=cs;
	endfunction
endclass

// @uvm-ieee 1800.2-2017 auto F.4.2.1
class uvm_default_coreservice_t extends uvm_coreservice_t;
	local uvm_factory factory;

	// Function --NODOCS-- get_factory
	//
	// Returns the currently enabled uvm factory.
	// When no factory has been set before, instantiates a uvm_default_factory
	virtual function uvm_factory get_factory();
		if(factory==null) begin
			uvm_default_factory f;
			f=new;
			factory=f;
		end

		return factory;
	endfunction

	// Function --NODOCS-- set_factory
	//
	// Sets the current uvm factory.
	// Please note: it is up to the user to preserve the contents of the original factory or delegate calls to the original factory
	virtual function void set_factory(uvm_factory f);
		factory = f;
	endfunction

	local uvm_tr_database tr_database;
	// Function --NODOCS-- get_default_tr_database
	// returns the current default record database
	//
	// If no default record database has been set before this method
	// is called, returns an instance of <uvm_text_tr_database>
	virtual function uvm_tr_database get_default_tr_database();
		if (tr_database == null) begin
			process p = process::self();
			uvm_text_tr_database tx_db;
			string s;
			if(p != null)
				s = p.get_randstate();

			tx_db = new("default_tr_database");
			tr_database = tx_db;

			if(p != null)
				p.set_randstate(s);
		end
		return tr_database;
	endfunction : get_default_tr_database

	// Function --NODOCS-- set_default_tr_database
	// Sets the current default record database to ~db~
	virtual function void set_default_tr_database(uvm_tr_database db);
		tr_database = db;
	endfunction : set_default_tr_database

	local uvm_report_server report_server;
	// Function --NODOCS-- get_report_server
	// returns the current global report_server
	// if no report server has been set before, returns an instance of
	// uvm_default_report_server
	virtual function uvm_report_server get_report_server();
		if(report_server==null) begin
			uvm_default_report_server f;
			f=new;
			report_server=f;
		end

		return report_server;
	endfunction

	// Function --NODOCS-- set_report_server
	// sets the central report server to ~server~
	virtual function void set_report_server(uvm_report_server server);
		report_server=server;
	endfunction

	virtual function uvm_root get_root();
		return uvm_root::m_uvm_get_root();
	endfunction

	local uvm_visitor#(uvm_component) _visitor;
	// Function --NODOCS-- set_component_visitor
	// sets the component visitor to ~v~
	// (this visitor is being used for the traversal at end_of_elaboration_phase
	// for instance for name checking)
	virtual function void set_component_visitor(uvm_visitor#(uvm_component) v);
		_visitor=v;
	endfunction

	// Function --NODOCS-- get_component_visitor
	// retrieves the current component visitor
	// if unset(or ~null~) returns a <uvm_component_name_check_visitor> instance
	virtual function uvm_visitor#(uvm_component) get_component_visitor();
		if(_visitor==null) begin
			uvm_component_name_check_visitor v = new("name-check-visitor");
			_visitor=v;
		end
		return _visitor;
	endfunction

	local uvm_printer m_printer ;

	virtual function void set_default_printer(uvm_printer printer);
`ifdef UVM_ENABLE_DEPRECATED_API
		uvm_default_printer = printer ;
`else
		m_printer = printer ;
`endif
	endfunction

	virtual function uvm_printer get_default_printer();
`ifdef UVM_ENABLE_DEPRECATED_API
		if (uvm_default_printer == null) begin
			uvm_default_printer =  uvm_table_printer::get_default() ;
		end
		return uvm_default_printer ;
`else
		if (m_printer == null) begin
			m_printer =  uvm_table_printer::get_default() ;
		end
		return m_printer ;
`endif
	endfunction

	local uvm_packer m_packer ;

	virtual function void set_default_packer(uvm_packer packer);
`ifdef UVM_ENABLE_DEPRECATED_API
		uvm_default_packer = packer ;
`else
		m_packer = packer ;

`endif
	endfunction

	virtual function uvm_packer get_default_packer();
`ifdef UVM_ENABLE_DEPRECATED_API
		if (uvm_default_packer == null) begin
			uvm_default_packer =  new() ;
		end
		return uvm_default_packer ;
`else
		if (m_packer == null) begin
         m_packer =  new("uvm_default_packer") ;
		end
		return m_packer ;
`endif
	endfunction

	local uvm_comparer m_comparer ;
	virtual function void set_default_comparer(uvm_comparer comparer);
`ifdef UVM_ENABLE_DEPRECATED_API
		uvm_default_comparer = comparer ;
`else
		m_comparer = comparer ;
`endif
	endfunction
	virtual function uvm_comparer get_default_comparer();
`ifdef UVM_ENABLE_DEPRECATED_API
		if (uvm_default_comparer == null) begin
			uvm_default_comparer =  new() ;
		end
		return uvm_default_comparer ;
`else
		if (m_comparer == null) begin
         m_comparer =  new("uvm_default_comparer") ;
		end
		return m_comparer ;
`endif
	endfunction

	local int m_default_max_ready_to_end_iters = 20;
	virtual function void set_phase_max_ready_to_end(int max);
		m_default_max_ready_to_end_iters = max;
	endfunction

	virtual function int get_phase_max_ready_to_end();
		return m_default_max_ready_to_end_iters;
	endfunction

	local uvm_resource_pool m_rp ;
	virtual function void set_resource_pool (uvm_resource_pool pool);
		m_rp = pool;
	endfunction

	virtual function uvm_resource_pool get_resource_pool();
		if(m_rp == null)
			m_rp = new();
		return m_rp;
	endfunction

	local int unsigned m_default_precedence = 1000;
	virtual function void set_resource_pool_default_precedence(int unsigned precedence);
		m_default_precedence = precedence;
	endfunction

	virtual function int unsigned get_resource_pool_default_precedence();
		return m_default_precedence;
	endfunction

	local int unsigned m_uvm_global_seed = $urandom;
	virtual function int unsigned get_global_seed();
		return m_uvm_global_seed;
	endfunction

`ifndef UVM_ENABLE_DEPRECATED_API
   // This bit is located in uvm_object in deprecated mode
   local bit m_use_uvm_seeding = 1;
`endif
   
   // @uvm-ieee 1800.2-2017 auto F.4.3
   virtual function bit get_uvm_seeding();
`ifdef UVM_ENABLE_DEPRECATED_API
      return uvm_object::use_uvm_seeding;
`else
      return m_use_uvm_seeding;
`endif 
   endfunction : get_uvm_seeding

   // @uvm-ieee 1800.2-2017 auto F.4.4
   virtual function void set_uvm_seeding(bit enable);
`ifdef UVM_ENABLE_DEPRECATED_API
      uvm_object::use_uvm_seeding = enable;
`else
      m_use_uvm_seeding = enable;
`endif
   endfunction : set_uvm_seeding

	local uvm_copier m_copier ;

	virtual function void set_default_copier(uvm_copier copier);
		m_copier = copier ;
	endfunction
	virtual function uvm_copier get_default_copier();
		if (m_copier == null) begin
         m_copier =  new("uvm_default_copier") ;
		end
		return m_copier ;
	endfunction

endclass
