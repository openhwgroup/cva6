//----------------------------------------------------------------------
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2011 AMD
// Copyright 2014-2018 NVIDIA Corporation
// Copyright 2013 Cisco Systems, Inc.
// Copyright 2012 Accellera Systems Initiative
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

// Title -- NODOCS -- UVM Common Phases
// 
// The common phases are the set of function and task phases that all
// <uvm_component>s execute together.
// All <uvm_component>s are always synchronized
// with respect to the common phases.
// 
// The names of the UVM phases (which will be returned by get_name() for a
// phase instance) match the class names specified below with the "uvm_"
// and "_phase" removed.  For example, the build phase corresponds to the 
// uvm_build_phase class below and has the name "build", which means that 
// the following can be used to call foo() at the end of the build phase 
// (after all lower levels have finished build):
//
// | function void phase_ended(uvm_phase phase) ;
// |    if (phase.get_name()=="build") foo() ;
// | endfunction
// 
// The common phases are executed in the sequence they are specified below.
// 
// 
// Class -- NODOCS -- uvm_build_phase
//
// Create and configure of testbench structure
//
// <uvm_topdown_phase> that calls the
// <uvm_component::build_phase> method.
//
// Upon entry:
//  - The top-level components have been instantiated under <uvm_root>.
//  - Current simulation time is still equal to 0 but some "delta cycles" may have occurred
//
// Typical Uses:
//  - Instantiate sub-components.
//  - Instantiate register model.
//  - Get configuration values for the component being built.
//  - Set configuration values for sub-components.
//
// Exit Criteria:
//  - All <uvm_component>s have been instantiated.

// @uvm-ieee 1800.2-2017 auto 9.8.1.1
class uvm_build_phase extends uvm_topdown_phase;
   virtual function void exec_func(uvm_component comp, uvm_phase phase);
      comp.build_phase(phase); 
   endfunction
   local static uvm_build_phase m_inst;
   `uvm_type_name_decl("uvm_build_phase")

   // Function -- NODOCS -- get
   // Returns the singleton phase handle
   //
   static function uvm_build_phase get();
      if(m_inst == null)
         m_inst = new();
      return m_inst; 
   endfunction
   protected function new(string name="build");
      super.new(name); 
   endfunction
endclass

// Class -- NODOCS -- uvm_connect_phase
//
// Establish cross-component connections.
//
// <uvm_bottomup_phase> that calls the
// <uvm_component::connect_phase> method.
//
// Upon Entry:
// - All components have been instantiated.
// - Current simulation time is still equal to 0
//   but some "delta cycles" may have occurred.
//
// Typical Uses:
// - Connect TLM ports and exports.
// - Connect TLM initiator sockets and target sockets.
// - Connect register model to adapter components.
// - Setup explicit phase domains.
//
// Exit Criteria:
// - All cross-component connections have been established.
// - All independent phase domains are set.
//

// @uvm-ieee 1800.2-2017 auto 9.8.1.2
class uvm_connect_phase extends uvm_bottomup_phase;
   virtual function void exec_func(uvm_component comp, uvm_phase phase);
      comp.connect_phase(phase); 
   endfunction
   local static uvm_connect_phase m_inst;
   `uvm_type_name_decl("uvm_connect_phase")

   // Function -- NODOCS -- get
   // Returns the singleton phase handle 
   static function uvm_connect_phase get();
      if(m_inst == null)
         m_inst = new();
      return m_inst; 
   endfunction
   protected function new(string name="connect");
      super.new(name); 
   endfunction
endclass

// Class -- NODOCS -- uvm_end_of_elaboration_phase
//
// Fine-tune the testbench.
//
// <uvm_bottomup_phase> that calls the
// <uvm_component::end_of_elaboration_phase> method.
//
// Upon Entry:
// - The verification environment has been completely assembled.
// - Current simulation time is still equal to 0
//   but some "delta cycles" may have occurred.
//
// Typical Uses:
// - Display environment topology.
// - Open files.
// - Define additional configuration settings for components.
//
// Exit Criteria:
// - None.

// @uvm-ieee 1800.2-2017 auto 9.8.1.3
class uvm_end_of_elaboration_phase extends uvm_bottomup_phase;
   virtual function void exec_func(uvm_component comp, uvm_phase phase);
      comp.end_of_elaboration_phase(phase); 
   endfunction
   local static uvm_end_of_elaboration_phase m_inst;
   `uvm_type_name_decl("uvm_end_of_elaboration_phase")

   // Function -- NODOCS -- get
   // Returns the singleton phase handle 
   static function uvm_end_of_elaboration_phase get();
      if(m_inst == null) begin 
         m_inst = new();
      end
      return m_inst; 
   endfunction
   protected function new(string name="end_of_elaboration");
      super.new(name); 
   endfunction
endclass

// Class -- NODOCS -- uvm_start_of_simulation_phase
//
// Get ready for DUT to be simulated.
//
// <uvm_bottomup_phase> that calls the
// <uvm_component::start_of_simulation_phase> method.
//
// Upon Entry:
// - Other simulation engines, debuggers, hardware assisted platforms and
//   all other run-time tools have been started and synchronized.
// - The verification environment has been completely configured
//   and is ready to start.
// - Current simulation time is still equal to 0
//   but some "delta cycles" may have occurred.
//
// Typical Uses:
// - Display environment topology
// - Set debugger breakpoint
// - Set initial run-time configuration values.
//
// Exit Criteria:
// - None.


// @uvm-ieee 1800.2-2017 auto 9.8.1.4
class uvm_start_of_simulation_phase extends uvm_bottomup_phase;
   virtual function void exec_func(uvm_component comp, uvm_phase phase);
      comp.start_of_simulation_phase(phase); 
   endfunction
   local static uvm_start_of_simulation_phase m_inst;
   `uvm_type_name_decl("uvm_start_of_simulation_phase")

   // Function -- NODOCS -- get
   // Returns the singleton phase handle 
   static function uvm_start_of_simulation_phase get();
      if(m_inst == null)
         m_inst = new();
      return m_inst; 
   endfunction
   protected function new(string name="start_of_simulation");
      super.new(name); 
   endfunction
endclass


// @uvm-ieee 1800.2-2017 auto 9.8.1.5
class uvm_run_phase extends uvm_task_phase; 
   virtual task exec_task(uvm_component comp, uvm_phase phase); 
      comp.run_phase(phase); 
   endtask
   local static uvm_run_phase m_inst;
   `uvm_type_name_decl("uvm_run_phase")

   // Function -- NODOCS -- get
   // Returns the singleton phase handle 
   static function uvm_run_phase get(); 
      if(m_inst == null)
         m_inst = new; 
      return m_inst; 
   endfunction
   protected function new(string name="run"); 
      super.new(name); 
   endfunction
endclass



// @uvm-ieee 1800.2-2017 auto 9.8.1.6
class uvm_extract_phase extends uvm_bottomup_phase;
   virtual function void exec_func(uvm_component comp, uvm_phase phase);
      comp.extract_phase(phase); 
   endfunction
   local static uvm_extract_phase m_inst;
   `uvm_type_name_decl("uvm_extract_phase")

   // Function -- NODOCS -- get
   // Returns the singleton phase handle 
   static function uvm_extract_phase get();
      if(m_inst == null)
         m_inst = new();
      return m_inst; 
   endfunction
   protected function new(string name="extract");
      super.new(name); 
   endfunction
endclass


// @uvm-ieee 1800.2-2017 auto 9.8.1.7
class uvm_check_phase extends uvm_bottomup_phase;
   virtual function void exec_func(uvm_component comp, uvm_phase phase);
      comp.check_phase(phase); 
   endfunction
   local static uvm_check_phase m_inst;
   `uvm_type_name_decl("uvm_check_phase")

   // Function -- NODOCS -- get
   // Returns the singleton phase handle 
   static function uvm_check_phase get();
      if(m_inst == null)
         m_inst = new();
      return m_inst; 
   endfunction
   protected function new(string name="check");
      super.new(name); 
   endfunction
endclass


// @uvm-ieee 1800.2-2017 auto 9.8.1.8
class uvm_report_phase extends uvm_bottomup_phase;
   virtual function void exec_func(uvm_component comp, uvm_phase phase);
      comp.report_phase(phase); 
   endfunction
   local static uvm_report_phase m_inst;
   `uvm_type_name_decl("uvm_report_phase")

   // Function -- NODOCS -- get
   // Returns the singleton phase handle 
   static function uvm_report_phase get();
      if(m_inst == null)
         m_inst = new();
      return m_inst; 
   endfunction
   protected function new(string name="report");
      super.new(name); 
   endfunction
endclass


// Class -- NODOCS -- uvm_final_phase
//
// Tie up loose ends.
//
// <uvm_topdown_phase> that calls the
// <uvm_component::final_phase> method.
//
// Upon Entry:
// - All test-related activity has completed.
//
// Typical Uses:
// - Close files.
// - Terminate co-simulation engines.
//
// Exit Criteria:
// - Ready to exit simulator.
//

// @uvm-ieee 1800.2-2017 auto 9.8.1.9
class uvm_final_phase extends uvm_topdown_phase;
   virtual function void exec_func(uvm_component comp, uvm_phase phase);
      comp.final_phase(phase); 
   endfunction
   local static uvm_final_phase m_inst;
   `uvm_type_name_decl("uvm_final_phase")

   // Function -- NODOCS -- get
   // Returns the singleton phase handle 
   static function uvm_final_phase get();
      if(m_inst == null)
         m_inst = new();
      return m_inst; 
   endfunction
   protected function new(string name="final");
      super.new(name); 
   endfunction
endclass
