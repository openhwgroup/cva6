//----------------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2018 NVIDIA Corporation
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

// macro - UVM_RESOURCE_GET_FCNS

// When specicializing resources the get_by_name and get_by_type
// functions must be redefined.  The reason is that the version of these
// functions in the base class (uvm_resource#(T)) returns an object of
// type uvm_resource#(T).  In the specializations we must return an
// object of the type of the specialization.  So, we call the base_class
// implementation of these functions and then downcast to the subtype.
//
// This macro is invokved once in each where a resource specialization
// is a class defined as:
//
//|  class <resource_specialization> extends uvm_resource#(T)
//
// where <resource_specialization> is the name of the derived class.
// The argument to this macro is T, the type of the uvm_resource#(T)
// specialization.  The class in which the macro is defined must supply
// a typedef of the specialized class of the form:
//
//|  typedef <resource_specialization> this_subtype;
//
// where <resource_specialization> is the same as above.  The macro
// generates the get_by_name() and get_by_type() functions for the
// specialized resource (i.e. resource subtype).

`define UVM_RESOURCE_GET_FCNS(base_type)                                               \
  static function this_subtype get_by_name(string scope, string name, bit rpterr = 1); \
    this_subtype t;                                                                    \
    uvm_resource_base b = uvm_resource#(base_type)::get_by_name(scope, name, rpterr);  \
    if(!$cast(t, b))                                                                   \
      `uvm_fatal("BADCAST", "cannot cast resource to resource subtype")               \
    return t;                                                                          \
  endfunction                                                                          \
                                                                                       \
  static function this_subtype get_by_type(string scope = "",                          \
                                           uvm_resource_base type_handle);             \
    this_subtype t;                                                                    \
    uvm_resource_base b = uvm_resource#(base_type)::get_by_type(scope, type_handle);   \
    if(!$cast(t, b))                                                                   \
      `uvm_fatal("BADCAST", "cannot cast resource to resource subtype")               \
    return t;                                                                          \
  endfunction


//----------------------------------------------------------------------
// uvm_int_rsrc
//
// specialization of uvm_resource #(T) for T = int
//----------------------------------------------------------------------
class uvm_int_rsrc extends uvm_resource #(int);

  typedef uvm_int_rsrc this_subtype;

  function new(string name, string s = "*");
    uvm_resource_pool rp;
    super.new(name);
    rp = uvm_resource_pool::get();
    rp.set_scope(this, s);
  endfunction

  function string convert2string();
    string s;
    $sformat(s, "%0d", read());
    return s;
  endfunction

`ifdef UVM_ENABLE_DEPRECATED_API
  `UVM_RESOURCE_GET_FCNS(int)
`endif // UVM_ENABLE_DEPRECATED_API

endclass

//----------------------------------------------------------------------
// uvm_string_rsrc
//
// specialization of uvm_resource #(T) for T = string
//----------------------------------------------------------------------
class uvm_string_rsrc extends uvm_resource #(string);

  typedef uvm_string_rsrc this_subtype;

  function new(string name, string s = "*");
    uvm_resource_pool rp;
    super.new(name);
    rp = uvm_resource_pool::get();
    rp.set_scope(this, s);
  endfunction

  function string convert2string();
    return read();
  endfunction

`ifdef UVM_ENABLE_DEPRECATED_API
  `UVM_RESOURCE_GET_FCNS(string)
`endif // UVM_ENABLE_DEPRECATED_API

endclass

//----------------------------------------------------------------------
// uvm_obj_rsrc
//
// specialization of uvm_resource #(T) for T = uvm_object
//----------------------------------------------------------------------
class uvm_obj_rsrc extends uvm_resource #(uvm_object);

  typedef uvm_obj_rsrc this_subtype;

  function new(string name, string s = "*");
    uvm_resource_pool rp;
    super.new(name);
    rp = uvm_resource_pool::get();
    rp.set_scope(this, s);
  endfunction

`ifdef UVM_ENABLE_DEPRECATED_API
  `UVM_RESOURCE_GET_FCNS(uvm_object)
`endif // UVM_ENABLE_DEPRECATED_API

endclass

//----------------------------------------------------------------------
// uvm_bit_rsrc
//
// specialization of uvm_resource #(T) for T = vector of bits
//----------------------------------------------------------------------
class uvm_bit_rsrc #(int unsigned N=1) extends uvm_resource #(bit[N-1:0]);

  typedef uvm_bit_rsrc#(N) this_subtype;

  function new(string name, string s = "*");
    uvm_resource_pool rp;
    super.new(name);
    rp = uvm_resource_pool::get();
    rp.set_scope(this, s);
  endfunction

  function string convert2string();
    string s;
    $sformat(s, "%0b", read());
    return s;
  endfunction

`ifdef UVM_ENABLE_DEPRECATED_API
  `UVM_RESOURCE_GET_FCNS(bit[N-1:0])
`endif // UVM_ENABLE_DEPRECATED_API

endclass

//----------------------------------------------------------------------
// uvm_byte_rsrc
//
// specialization of uvm_resource #T() for T = vector of bytes
//----------------------------------------------------------------------
class uvm_byte_rsrc #(int unsigned N=1) extends uvm_resource #(bit[7:0][N-1:0]);

  typedef uvm_byte_rsrc#(N) this_subtype;

  function new(string name, string s = "*");
    uvm_resource_pool rp;
    super.new(name);
    rp = uvm_resource_pool::get();
    rp.set_scope(this, s);
  endfunction

  function string convert2string();
    string s;
    $sformat(s, "%0x", read());
    return s;
  endfunction

`ifdef UVM_ENABLE_DEPRECATED_API
  `UVM_RESOURCE_GET_FCNS(bit[7:0][N-1:0])
`endif // UVM_ENABLE_DEPRECATED_API

endclass
