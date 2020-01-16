//----------------------------------------------------------------------
// Copyright 2018 Synopsys, Inc.
// Copyright 2018 Cadence Design Systems, Inc.
// Copyright 2018 NVIDIA Corporation
// Copyright 2018 Cisco Systems, Inc.
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

//------------------------------------------------------------------------------
// Class - uvm_field_op
//
// uvm_field_op is the UVM class for describing all operations supported by the do_execute_op function
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 5.3.13.2.1
class uvm_field_op extends uvm_object;

   // @uvm-ieee 1800.2-2017 auto 5.3.4.5
   // @uvm-ieee 1800.2-2017 auto 5.3.4.6
   // @uvm-ieee 1800.2-2017 auto 5.3.4.7
   // @uvm-ieee 1800.2-2017 auto 5.3.5.1
   `uvm_object_utils(uvm_field_op)

   local uvm_policy m_policy;
   local bit m_user_hook;
   local uvm_object m_object;
   // Bit m_is_set is set when the set() method is called and acts 
   // like a state variable. It is cleared when flush is called.
   local bit m_is_set;
   local  uvm_field_flag_t m_op_type;


   // Function -- new 
   // 
   // Creates a policy with the specified instance name. If name is not provided, then the policy instance is
   // unnamed.

   // @uvm-ieee 1800.2-2017 auto 5.3.13.2.3
   // @uvm-ieee 1800.2-2017 auto 5.3.2
   function new (string name="");
      super.new(name);
      m_is_set = 1'b0;
      m_user_hook = 1'b1;
   endfunction


   // @uvm-ieee 1800.2-2017 auto 5.3.13.2.4
   virtual function void set( uvm_field_flag_t op_type, uvm_policy policy = null, uvm_object rhs = null);
     string matching_ops[$];
     if (op_type & UVM_COPY)
       matching_ops.push_back("UVM_COPY");
     if (op_type & UVM_COMPARE)
       matching_ops.push_back("UVM_COMPARE");
     if (op_type & UVM_PRINT)
       matching_ops.push_back("UVM_PRINT");
     if (op_type & UVM_RECORD)
       matching_ops.push_back("UVM_RECORD");
     if (op_type & UVM_PACK)
       matching_ops.push_back("UVM_PACK");
     if (op_type & UVM_UNPACK)
       matching_ops.push_back("UVM_UNPACK");
     if (op_type & UVM_SET)
       matching_ops.push_back("UVM_SET");

     if (matching_ops.size() > 1) begin
       string msg_queue[$];
       msg_queue.push_back("(");
       foreach (matching_ops[i]) begin
         msg_queue.push_back(matching_ops[i]);
         if (i != matching_ops.size() - 1)
           msg_queue.push_back(",");
       end
       msg_queue.push_back(")");
       `uvm_error("UVM/FIELD_OP/SET_BAD_OP_TYPE", {"set() was passed op_type matching multiple operations: ", `UVM_STRING_QUEUE_STREAMING_PACK(msg_queue)})
     end

     if(m_is_set == 0) begin
       m_op_type = op_type;
       m_policy = policy;
       m_object = rhs;
       m_is_set = 1'b1;
     end 
     else 
       `uvm_error("UVM/FIELD_OP/SET","Attempting to set values in policy without flushing")
   endfunction 

   // @uvm-ieee 1800.2-2017 auto 5.3.13.2.5
   virtual function string get_op_name();
      case(m_op_type)
        UVM_COPY : return "copy";
        UVM_COMPARE : return "compare";
        UVM_PRINT : return "print";
        UVM_RECORD : return "record";
        UVM_PACK : return "pack";
        UVM_UNPACK : return "unpack";
        UVM_SET : return "set";
        default: return "";
      endcase
   endfunction

   // @uvm-ieee 1800.2-2017 auto 5.3.13.2.6
   virtual function uvm_field_flag_t get_op_type();
      if(m_is_set == 1'b1) 
        return m_op_type;
      else 
        `uvm_error("UVM/FIELD_OP/GET_OP_TYPE","Calling get_op_type() before calling set() is not allowed")
   endfunction


   // @uvm-ieee 1800.2-2017 auto 5.3.13.2.7
   virtual function uvm_policy get_policy();
      if(m_is_set == 1'b1) 
        return m_policy;
      else 
        `uvm_error("UVM/FIELD_OP/GET_POLICY","Attempting to call get_policy() before calling set() is not allowed")
   endfunction

   // @uvm-ieee 1800.2-2017 auto 5.3.13.2.8
   virtual function uvm_object get_rhs();
      if(m_is_set == 1'b1) 
        return m_object;
      else 
        `uvm_error("UVM/FIELD_OP/GET_RHS","Calling get_rhs() before calling set() is not allowed")
   endfunction

   // @uvm-ieee 1800.2-2017 auto 5.3.13.2.9
   function bit user_hook_enabled();
      if(m_is_set == 1'b1) 
        return m_user_hook;
      else 
        `uvm_error("UVM/FIELD_OP/GET_USER_HOOK","Attempting to get_user_hook before calling set() is not allowed")
   endfunction

   // @uvm-ieee 1800.2-2017 auto 5.3.13.2.10
   function void disable_user_hook();
      m_user_hook = 1'b0;
   endfunction

   static uvm_field_op m_recycled_op[$] ; 

   // @uvm-ieee 1800.2-2017 auto 5.3.13.2.11
   virtual function void flush();
      m_policy = null;
      m_object = null;
      m_user_hook = 1'b1;
      m_is_set = 0;
   endfunction

   // API for reusing uvm_field_op instances.  Implementation
   // artifact, should not be used directly by the user.
   function void m_recycle();
     this.flush();
     m_recycled_op.push_back(this);
   endfunction : m_recycle 
 
   static function uvm_field_op m_get_available_op() ;
      uvm_field_op field_op ;
      if (m_recycled_op.size() > 0) field_op = m_recycled_op.pop_back() ;
      else field_op = uvm_field_op::type_id::create("field_op");
      return field_op ;
   endfunction
endclass
