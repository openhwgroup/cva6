//----------------------------------------------------------------------
// Copyright 2018 Synopsys, Inc.
// Copyright 2018 Cadence Design Systems, Inc.
// Copyright 2018 NVIDIA Corporation
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

typedef class uvm_root;

//------------------------------------------------------------------------------
// Class -- NODOCS --  uvm_policy
//
// The abstract uvm_policy class provides a common base from which all UVM policy classes derive
// Implementation as per Section 16.1 UVM Policy
//------------------------------------------------------------------------------
// @uvm-ieee 1800.2-2017 auto 16.1.1
virtual class uvm_policy extends uvm_object;


typedef enum {
        NEVER,
        STARTED,
        FINISHED
} recursion_state_e;


local uvm_object  m_extensions[uvm_object_wrapper];
local uvm_object m_policy_stack[$];




// Function -- NODOCS -- new
// 
// Creates a policy with the specified instance name. If name is not provided, then the policy instance is
// unnamed.

// @uvm-ieee 1800.2-2017 auto 16.1.2.1
function new (string name="");
	super.new(name);
endfunction

// Function -- NODOCS -- flush
//
// The flush method resets the internal state of the policy, such that it can be reused.
// Policy extensions are Not cleared in below method as per 16.1.2.3
// @uvm-ieee 1800.2-2017 auto 16.1.2.2
virtual function void flush();
	m_policy_stack.delete();

endfunction



// Function -- NODOCS -- extension_exists
// Function extension_exists
// Returns 1 if an extension exists within the policy with type matching ext_type; otherwise, returns 0.
// @uvm-ieee 1800.2-2017 auto 16.1.2.3.1
virtual function bit extension_exists( uvm_object_wrapper ext_type );

    if (m_extensions.exists(ext_type)) 
	extension_exists = 1;
   else 
	extension_exists = 0;

endfunction 


// Function -- NODOCS -- set_extension
// 
// Sets the given extension inside of the policy, indexed using return value from extension's get_object_type?
// method (see 5.3.4.6). Only a single instance of an extension is stored per type. If there is an existing
// extension instance matching extension's type, extension replaces the instance and the replaced instance
// handle is returned; otherwise, null is returned.
// @uvm-ieee 1800.2-2017 auto 16.1.2.3.2
virtual function uvm_object set_extension( uvm_object extension );
uvm_object m_set_extension;
	 if ( extension  == null) 
    		uvm_report_fatal("NULLEXT", "Attempting to set  null extension ", UVM_NONE);

	// Case where extension exists.
	if(m_extensions.exists(extension.get_object_type())) begin
      		m_set_extension = m_extensions[extension.get_object_type()] ;
      		m_extensions[extension.get_object_type()] = extension;
		return m_set_extension;	
	end
	else  begin
		// Other case where extension doesnt exist. Nothing to return
      		m_extensions[extension.get_object_type()] = extension;
		return null;
	end

endfunction 


// Function -- NODOCS -- get_extension
//Returns the extension value stored within the policy with type matching ext_type. Returns null if no
// extension exists matching that type.
// @uvm-ieee 1800.2-2017 auto 16.1.2.3.3
virtual function uvm_object get_extension(uvm_object_wrapper ext_type );
    if (m_extensions.exists(ext_type)) begin
     return m_extensions[ext_type];
    end
   else
	return null;
endfunction

// Function -- NODOCS -- clear_extension
// Removes the extension value stored within the policy matching type ext_type. If no extension exists
// matching type ext_type, the request is silently ignored.
// @uvm-ieee 1800.2-2017 auto 16.1.2.3.4
virtual function void clear_extension( uvm_object_wrapper ext_type );
	m_extensions.delete(ext_type);
endfunction 

// Function -- NODOCS -- clear_extensions
// Removes all extensions currently stored within the policy.
// @uvm-ieee 1800.2-2017 auto 16.1.2.3.5
virtual function void clear_extensions();
		m_extensions.delete();
endfunction


// Function -- NODOCS -- push_active_object
// Pushes obj on to the internal object stack for this policy, making it the current active object, as retrieved by
// get_active_object (see 16.1.3.3). An implementation shall generate an error message if obj is null and the
// request will be ignored. Additionally, the policy shall push itself onto the active policy stack for obj using push_active_policy (see
// 5.3.14.1) when push_active_object is called.
// @uvm-ieee 1800.2-2017 auto 16.1.3.1
virtual function void push_active_object( uvm_object obj );
	if(obj != null) 
	m_policy_stack.push_front(obj);
	// Placeholder. Will be removed once uvm_object is updated. That's a seperate mantisi 6438
	// obj.push_active_policy(this);
	// 
	else
	`uvm_error("UVM_POLICY_PUSHNULL", "Attempting to push an null object push_active_object onto the policy stack")
	
endfunction 

// Function -- NODOCS -- pop_active_object
// Pops the current active object off of the internal object stack for this policy and returns the popped off value.
// For additional behaviour descriptions (see
// 5.3.14.2) when pop_active_object is called.
// @uvm-ieee 1800.2-2017 auto 16.1.3.2
virtual function uvm_object pop_active_object();
uvm_object  m_tmp;
	if(m_policy_stack.size() != 0) begin
	m_tmp = m_policy_stack.pop_front();
	return m_tmp;
	end
	else 
	`uvm_info("UVM_POLICY_EMPTY_POPACTIVE_OBJECT", "Attempting to pop an empty policy stack",UVM_DEBUG)

endfunction

// Function -- NODOCS -- get_active_object
// Returns the head of the internal object stack for this policy. 
// empty, null is returned.
// @uvm-ieee 1800.2-2017 auto 16.1.3.3
virtual function uvm_object get_active_object();
	if(m_policy_stack.size() != 0) 
	return m_policy_stack[0];
endfunction

// Function -- NODOCS -- get_active_object_depth
// Returns the current depth of the internal object stack for this policy.
virtual function int unsigned get_active_object_depth();
	return m_policy_stack.size();
endfunction

endclass

