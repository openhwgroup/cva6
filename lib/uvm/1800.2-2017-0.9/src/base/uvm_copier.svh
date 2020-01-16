//-----------------------------------------------------------------------------
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
//-----------------------------------------------------------------------------

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_copier
//
// The uvm_copier class provides a policy object for doing comparisons. The
// policies determine how miscompares are treated and counted. Results of a
// comparison are stored in the copier object. The <uvm_object::compare>
// and <uvm_object::do_compare> methods are passed a uvm_copier policy
// object.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 16.6.1
class uvm_copier extends uvm_policy;
   // @uvm-ieee 1800.2-2017 auto 16.6.2.2
   `uvm_object_utils(uvm_copier)
  // Variable -- NODOCS -- policy
  //
  // Determines whether comparison is UVM_DEEP, UVM_REFERENCE, or UVM_SHALLOW.

    uvm_recursion_policy_enum policy = UVM_DEFAULT_POLICY;


   // @uvm-ieee 1800.2-2017 auto 16.6.2.1
   function new(string name="uvm_copier") ; 
	super.new(name);
   endfunction
	
   // Implementation only.

  // Implementation only. Not present in the LRM.
 //recursion_state_e m_saved_state[uvm_object /*LHS*/][uvm_object /*RHS*/][uvm_recursion_policy_enum /*recursion*/];

   recursion_state_e m_recur_states[uvm_object /*LHS*/][uvm_object /*RHS*/][uvm_recursion_policy_enum /*recursion*/];


  // Function -- copy_object
  //
  // Copies two class objects using the <policy> knob to determine whether the
  // comparison should be deep, shallow, or reference. 
  //
  // The name input is used for purposes of storing and printing a miscompare. 
  //
  // The ~lhs~ and ~rhs~ objects are the two objects used for comparison. 
  //
  // The ~check_type~ determines whether or not to verify the object
  // types match (the return from ~lhs.get_type_name()~ matches
  // ~rhs.get_type_name()~).

  // @uvm-ieee 1800.2-2017 auto 16.6.4.1
  virtual function void copy_object (
                                       uvm_object lhs,
                                       uvm_object rhs);

    uvm_field_op field_op;
    if (get_recursion_policy() == UVM_REFERENCE) begin
      `uvm_error("UVM_COPY_POLICY","Attempting to make a copy of a object which is a reference")
      return;
    end

    if (rhs == null || lhs == null) begin
      `uvm_error("UVM_COPY_NULL_OBJ","Attempting to make a copy of a object with null src/target")
      return;
    end

    push_active_object(lhs);
    m_recur_states[lhs][rhs][get_recursion_policy()] = uvm_policy::STARTED;
    field_op = uvm_field_op::m_get_available_op() ;
    field_op.set(UVM_COPY,this,rhs);
    lhs.do_execute_op(field_op);
    if (field_op.user_hook_enabled()) begin
       lhs.do_copy(rhs);
    end
    field_op.m_recycle();
    m_recur_states[lhs][rhs][get_recursion_policy()] = uvm_policy::FINISHED;
    void'(pop_active_object());
  endfunction
  
   // @uvm-ieee 1800.2-2017 auto 16.6.4.2
   virtual function recursion_state_e object_copied(
	 			uvm_object lhs,
  				uvm_object rhs,
  				uvm_recursion_policy_enum recursion
  );
  if (!m_recur_states.exists(lhs)) return NEVER ;
  else if (!m_recur_states[lhs].exists(rhs)) return NEVER ;
  else if (!m_recur_states[lhs][rhs].exists(recursion)) return NEVER ;
  else begin
     return m_recur_states[lhs][rhs][recursion];
  end
	
endfunction


function void flush();
  m_recur_states.delete();
endfunction

// @uvm-ieee 1800.2-2017 auto 16.6.3
virtual function void set_recursion_policy (uvm_recursion_policy_enum policy);
	this.policy = policy;
endfunction

// @uvm-ieee 1800.2-2017 auto 16.6.3
virtual function uvm_recursion_policy_enum get_recursion_policy();
	  return policy;
endfunction


// @uvm-ieee 1800.2-2017 auto 16.6.2.3
static function void set_default (uvm_copier copier) ;
     uvm_coreservice_t coreservice ;
     coreservice = uvm_coreservice_t::get() ;
     coreservice.set_default_copier(copier) ;
endfunction

// @uvm-ieee 1800.2-2017 auto 16.6.2.4
static function uvm_copier get_default () ;
     uvm_coreservice_t coreservice ;
     coreservice = uvm_coreservice_t::get() ;
     return coreservice.get_default_copier() ;
endfunction
 
endclass
