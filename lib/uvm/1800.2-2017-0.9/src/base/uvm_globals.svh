// 
//------------------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2014 Intel Corporation
// Copyright 2010-2014 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2010-2012 AMD
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2017 Cisco Systems, Inc.
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
//------------------------------------------------------------------------------

typedef class uvm_root;
typedef class uvm_report_object;
typedef class uvm_report_message;
   
// Title -- NODOCS -- Globals

//------------------------------------------------------------------------------
//
// Group -- NODOCS -- Simulation Control
//
//------------------------------------------------------------------------------

// Task -- NODOCS -- run_test
//
// Convenience function for uvm_top.run_test(). See <uvm_root> for more
// information.

// @uvm-ieee 1800.2-2017 auto F.3.1.2
task run_test (string test_name="");
  uvm_root top;
  uvm_coreservice_t cs;
  cs = uvm_coreservice_t::get();
  top = cs.get_root();
  top.run_test(test_name);
endtask

//----------------------------------------------------------------------------
//
// Group -- NODOCS -- Reporting
//
//----------------------------------------------------------------------------



// @uvm-ieee 1800.2-2017 auto F.3.2.1
function uvm_report_object uvm_get_report_object();
  uvm_root top;
  uvm_coreservice_t cs;
  cs = uvm_coreservice_t::get();
  top = cs.get_root();
  return top;
endfunction


// Function -- NODOCS -- uvm_report_enabled
//
// Returns 1 if the configured verbosity in ~uvm_top~ for this 
// severity/id is greater than or equal to ~verbosity~ else returns 0.
// 
// See also <uvm_report_object::uvm_report_enabled>.
//
// Static methods of an extension of uvm_report_object, e.g. uvm_component-based
// objects, cannot call ~uvm_report_enabled~ because the call will resolve to
// the <uvm_report_object::uvm_report_enabled>, which is non-static.
// Static methods cannot call non-static methods of the same class. 

// @uvm-ieee 1800.2-2017 auto F.3.2.2
function int uvm_report_enabled (int verbosity,
                                 uvm_severity severity=UVM_INFO, string id="");
  uvm_root top;
  uvm_coreservice_t cs;
  cs = uvm_coreservice_t::get();
  top = cs.get_root();
  return top.uvm_report_enabled(verbosity,severity,id);
endfunction

// Function -- NODOCS -- uvm_report

// @uvm-ieee 1800.2-2017 auto F.3.2.3
function void uvm_report( uvm_severity severity,
                          string id,
                          string message,
                          int verbosity = (severity == uvm_severity'(UVM_ERROR)) ? UVM_LOW :
                                          (severity == uvm_severity'(UVM_FATAL)) ? UVM_NONE : UVM_MEDIUM,
                          string filename = "",
                          int line = 0,
                          string context_name = "",
                          bit report_enabled_checked = 0);
  uvm_root top;
  uvm_coreservice_t cs;
  cs = uvm_coreservice_t::get();
  top = cs.get_root();
  top.uvm_report(severity, id, message, verbosity, filename, line, context_name, report_enabled_checked);
endfunction 

// Undocumented DPI available version of uvm_report
export "DPI-C" function m__uvm_report_dpi;
function void m__uvm_report_dpi(int severity,
                                string id,
                                string message,
                                int    verbosity,
                                string filename,
                                int    line);
   uvm_report(uvm_severity'(severity), id, message, verbosity, filename, line);
endfunction : m__uvm_report_dpi

// Function -- NODOCS -- uvm_report_info

// @uvm-ieee 1800.2-2017 auto F.3.2.3
function void uvm_report_info(string id,
			      string message,
                              int verbosity = UVM_MEDIUM,
			      string filename = "",
			      int line = 0,
                              string context_name = "",
                              bit report_enabled_checked = 0);
  uvm_root top;
  uvm_coreservice_t cs;
  cs = uvm_coreservice_t::get();
  top = cs.get_root();
  top.uvm_report_info(id, message, verbosity, filename, line, context_name,
    report_enabled_checked);
endfunction


// Function -- NODOCS -- uvm_report_warning

// @uvm-ieee 1800.2-2017 auto F.3.2.3
function void uvm_report_warning(string id,
                                 string message,
                                 int verbosity = UVM_MEDIUM,
				 string filename = "",
				 int line = 0,
                                 string context_name = "",
                                 bit report_enabled_checked = 0);
  uvm_root top;
  uvm_coreservice_t cs;
  cs = uvm_coreservice_t::get();
  top = cs.get_root();
  top.uvm_report_warning(id, message, verbosity, filename, line, context_name,
    report_enabled_checked);
endfunction


// Function -- NODOCS -- uvm_report_error

// @uvm-ieee 1800.2-2017 auto F.3.2.3
function void uvm_report_error(string id,
                               string message,
                               int verbosity = UVM_NONE,
			       string filename = "",
			       int line = 0,
                               string context_name = "",
                               bit report_enabled_checked = 0);
  uvm_root top;
  uvm_coreservice_t cs;
  cs = uvm_coreservice_t::get();
  top = cs.get_root();
  top.uvm_report_error(id, message, verbosity, filename, line, context_name,
    report_enabled_checked);
endfunction


// Function -- NODOCS -- uvm_report_fatal
//
// These methods, defined in package scope, are convenience functions that
// delegate to the corresponding component methods in ~uvm_top~. They can be
// used in module-based code to use the same reporting mechanism as class-based
// components. See <uvm_report_object> for details on the reporting mechanism. 
//
// *Note:* Verbosity is ignored for warnings, errors, and fatals to ensure users
// do not inadvertently filter them out. It remains in the methods for backward
// compatibility.

// @uvm-ieee 1800.2-2017 auto F.3.2.3
function void uvm_report_fatal(string id,
	                       string message,
                               int verbosity = UVM_NONE,
			       string filename = "",
			       int line = 0,
                               string context_name = "",
                               bit report_enabled_checked = 0);
  uvm_root top;
  uvm_coreservice_t cs;
  cs = uvm_coreservice_t::get();
  top = cs.get_root();
  top.uvm_report_fatal(id, message, verbosity, filename, line, context_name,
    report_enabled_checked);
endfunction


// Function -- NODOCS -- uvm_process_report_message
//
// This method, defined in package scope, is a convenience function that
// delegate to the corresponding component method in ~uvm_top~. It can be
// used in module-based code to use the same reporting mechanism as class-based
// components. See <uvm_report_object> for details on the reporting mechanism.

// @uvm-ieee 1800.2-2017 auto F.3.2.3
function void uvm_process_report_message(uvm_report_message report_message);
  uvm_root top;
  uvm_coreservice_t cs;
  process p;
  p = process::self();
  cs = uvm_coreservice_t::get();
  top = cs.get_root();
  top.uvm_process_report_message(report_message);
endfunction


// TODO merge with uvm_enum_wrapper#(uvm_severity)
function bit uvm_string_to_severity (string sev_str, output uvm_severity sev);
  case (sev_str)
    "UVM_INFO": sev = UVM_INFO;
    "UVM_WARNING": sev = UVM_WARNING;
    "UVM_ERROR": sev = UVM_ERROR;
    "UVM_FATAL": sev = UVM_FATAL;
    default: return 0;
  endcase
  return 1;
endfunction


function automatic bit uvm_string_to_action (string action_str, output uvm_action action);
  string actions[$];
  uvm_split_string(action_str,"|",actions);
  uvm_string_to_action = 1;
  action = 0;
  foreach(actions[i]) begin
    case (actions[i])
      "UVM_NO_ACTION": action |= UVM_NO_ACTION;
      "UVM_DISPLAY":   action |= UVM_DISPLAY;
      "UVM_LOG":       action |= UVM_LOG;
      "UVM_COUNT":     action |= UVM_COUNT;
      "UVM_EXIT":      action |= UVM_EXIT;
      "UVM_CALL_HOOK": action |= UVM_CALL_HOOK;
      "UVM_STOP":      action |= UVM_STOP;
      "UVM_RM_RECORD": action |= UVM_RM_RECORD;
      default: uvm_string_to_action = 0;
    endcase
  end
endfunction

  
//----------------------------------------------------------------------------
//
// Group: Miscellaneous
//
// The library implements the following public API at the package level beyond
// what is documented in IEEE 1800.2.
//----------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto F.3.3.1
function bit uvm_is_match (string expr, string str);
  string s;
  s = uvm_glob_to_re(expr);
  return (uvm_re_match(s, str) == 0);
endfunction


parameter UVM_LINE_WIDTH = `UVM_LINE_WIDTH;
parameter UVM_NUM_LINES = `UVM_NUM_LINES;
parameter UVM_SMALL_STRING = UVM_LINE_WIDTH*8-1;
parameter UVM_LARGE_STRING = UVM_LINE_WIDTH*UVM_NUM_LINES*8-1;


//----------------------------------------------------------------------------
//
// Function -- NODOCS -- uvm_string_to_bits
//
// Converts an input string to its bit-vector equivalent. Max bit-vector
// length is approximately 14000 characters.
//----------------------------------------------------------------------------

function logic[UVM_LARGE_STRING:0] uvm_string_to_bits(string str);
  $swrite(uvm_string_to_bits, "%0s", str);
endfunction

// @uvm-ieee 1800.2-2017 auto F.3.1.1
function uvm_core_state get_core_state();
		return m_uvm_core_state;
endfunction

// @uvm-ieee 1800.2-2017 auto F.3.1.3
function void uvm_init(uvm_coreservice_t cs=null);
	uvm_coreservice_t dcs;
	static bit uvm_init_active;
   
	if(get_core_state()!=UVM_CORE_UNINITIALIZED || uvm_init_active) begin
		`uvm_info("UVM/INIT/MULTI","uvm core already initialized, skipping uvm_init()",UVM_DEBUG)
		return;
	end
		
	if(cs!=null)
		dcs=cs;
	else begin
		uvm_default_coreservice_t ncs;
		ncs=new();
		dcs=ncs;
	end	
	uvm_coreservice_t::set(dcs);
	uvm_init_active=1;

	foreach(uvm_deferred_init[idx]) begin
	   uvm_deferred_init[idx].initialize();
	end
	
	uvm_deferred_init.delete();
	
	void'(uvm_root::get());
	
	m_uvm_core_state=UVM_CORE_INITIALIZED;
endfunction

//----------------------------------------------------------------------------
//
// Function -- NODOCS -- uvm_bits_to_string
//
// Converts an input bit-vector to its string equivalent. Max bit-vector
// length is approximately 14000 characters.
//----------------------------------------------------------------------------

function string uvm_bits_to_string(logic [UVM_LARGE_STRING:0] str);
  $swrite(uvm_bits_to_string, "%0s", str);
endfunction


//----------------------------------------------------------------------------
//
// Task: uvm_wait_for_nba_region
//
// This task will block until SystemVerilog's NBA region (or Re-NBA region if 
// called from a program context).  The purpose is to continue the calling 
// process only after allowing other processes any number of delta cycles (#0) 
// to settle out.
//
//----------------------------------------------------------------------------

task uvm_wait_for_nba_region;

  int nba;
  int next_nba;

  //If `included directly in a program block, can't use a non-blocking assign,
  //but it isn't needed since program blocks are in a separate region.
`ifndef UVM_NO_WAIT_FOR_NBA
  next_nba++;
  nba <= next_nba;
  @(nba);
`else
  repeat(`UVM_POUND_ZERO_COUNT) #0;
`endif


endtask


//----------------------------------------------------------------------------
//
// Function -- NODOCS -- uvm_split_string
//
// Returns a queue of strings, ~values~, that is the result of the ~str~ split
// based on the ~sep~.  For example:
//
//| uvm_split_string("1,on,false", ",", splits);
//
// Results in the 'splits' queue containing the three elements: 1, on and 
// false.
//----------------------------------------------------------------------------

function automatic void uvm_split_string (string str, byte sep, ref string values[$]);
  int s = 0, e = 0;
  values.delete();
  while(e < str.len()) begin
    for(s=e; e<str.len(); ++e)
      if(str[e] == sep) break;
    if(s != e)
      values.push_back(str.substr(s,e-1));
    e++;
  end
endfunction

// Class -- NODOCS -- uvm_enum_wrapper#(T)
//
// The ~uvm_enum_wrapper#(T)~ class is a utility mechanism provided
// as a convenience to the end user.  It provides a <from_name>
// method which is the logical inverse of the System Verilog ~name~ 
// method which is built into all enumerations.

// @uvm-ieee 1800.2-2017 auto F.3.4.1
class uvm_enum_wrapper#(type T=uvm_active_passive_enum);

    protected static T map[string];


    // @uvm-ieee 1800.2-2017 auto F.3.4.2
    static function bit from_name(string name, ref T value);
        if (map.size() == 0)
          m_init_map();

        if (map.exists(name)) begin
            value = map[name];
            return 1;
        end
        else begin
            return 0;
        end
    endfunction : from_name

    // Function- m_init_map
    // Initializes the name map, only needs to be performed once
    protected static function void m_init_map();
        T e = e.first();
        do 
          begin
            map[e.name()] = e;
            e = e.next();
          end
        while (e != e.first());
    endfunction : m_init_map

    // Function- new
    // Prevents accidental instantiations
    protected function new();
    endfunction : new

endclass : uvm_enum_wrapper
