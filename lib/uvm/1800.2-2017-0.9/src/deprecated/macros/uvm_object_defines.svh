//------------------------------------------------------------------------------
// Copyright 2012 Aldec
// Copyright 2007-2012 Mentor Graphics Corporation
// Copyright 2014 Intel Corporation
// Copyright 2010-2013 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2012 AMD
// Copyright 2012-2018 NVIDIA Corporation
// Copyright 2012-2018 Cisco Systems, Inc.
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
//------------------------------------------------------------------------------


// This file is the DEPRECATED version of uvm_object_defines.svh
// it contains versions of the macros that support functionality which was
// deprecated between UVM 1.2 and 1800.2-2017.



`ifndef UVM_OBJECT_DEFINES_SVH
`define UVM_OBJECT_DEFINES_SVH

`ifdef UVM_EMPTY_MACROS

`define uvm_field_utils_begin(T) 
`define uvm_field_utils_end 
`define uvm_object_utils(T) 
`define uvm_object_param_utils(T) 
`define uvm_object_utils_begin(T) 
`define uvm_object_param_utils_begin(T) 
`define uvm_object_abstract_utils(T) 
`define uvm_object_abstract_param_utils(T) 
`define uvm_object_abstract_utils_begin(T) 
`define uvm_object_abstract_param_utils_begin(T) 
`define uvm_object_abstract_utils_end
`define uvm_component_utils(T)
`define uvm_component_param_utils(T)
`define uvm_component_utils_begin(T)
`define uvm_component_param_utils_begin(T)
`define uvm_component_abstract_utils(T)
`define uvm_component_abstract_param_utils(T)
`define uvm_component_abstract_utils_begin(T)
`define uvm_component_abstract_param_utils_begin(T)
`define uvm_component_utils_end
`define uvm_field_int(ARG,FLAG)
`define uvm_field_real(ARG,FLAG)
`define uvm_field_enum(T,ARG,FLAG)
`define uvm_field_object(ARG,FLAG)
`define uvm_field_event(ARG,FLAG)
`define uvm_field_string(ARG,FLAG)
`define uvm_field_array_enum(ARG,FLAG)
`define uvm_field_array_int(ARG,FLAG)
`define uvm_field_sarray_int(ARG,FLAG)
`define uvm_field_sarray_enum(ARG,FLAG)
`define uvm_field_array_object(ARG,FLAG)
`define uvm_field_sarray_object(ARG,FLAG)
`define uvm_field_array_string(ARG,FLAG)
`define uvm_field_sarray_string(ARG,FLAG)
`define uvm_field_queue_enum(ARG,FLAG)
`define uvm_field_queue_int(ARG,FLAG)
`define uvm_field_queue_object(ARG,FLAG)
`define uvm_field_queue_string(ARG,FLAG)
`define uvm_field_aa_int_string(ARG, FLAG)
`define uvm_field_aa_string_string(ARG, FLAG)
`define uvm_field_aa_object_string(ARG, FLAG)
`define uvm_field_aa_int_int(ARG, FLAG)
`define uvm_field_aa_int_int(ARG, FLAG)
`define uvm_field_aa_int_int_unsigned(ARG, FLAG)
`define uvm_field_aa_int_integer(ARG, FLAG)
`define uvm_field_aa_int_integer_unsigned(ARG, FLAG)
`define uvm_field_aa_int_byte(ARG, FLAG)
`define uvm_field_aa_int_byte_unsigned(ARG, FLAG)
`define uvm_field_aa_int_shortint(ARG, FLAG)
`define uvm_field_aa_int_shortint_unsigned(ARG, FLAG)
`define uvm_field_aa_int_longint(ARG, FLAG)
`define uvm_field_aa_int_longint_unsigned(ARG, FLAG)
`define uvm_field_aa_int_key(KEY, ARG, FLAG)
`define uvm_field_aa_string_int(ARG, FLAG)
`define uvm_field_aa_object_int(ARG, FLAG)

`else

//------------------------------------------------------------------------------
//
// Title -- NODOCS -- Utility and Field Macros for Components and Objects
//
// Group -- NODOCS -- Utility Macros 
//
// The ~utils~ macros define the infrastructure needed to enable the
// object/component for correct factory operation. See <`uvm_object_utils> and
// <`uvm_component_utils> for details.
//
// A ~utils~ macro should be used inside ~every~ user-defined class that extends
// <uvm_object> directly or indirectly, including <uvm_sequence_item> and
// <uvm_component>.
//
// Below is an example usage of the ~utils~ macro for a user-defined object.
//
//|  class mydata extends uvm_object;
//| 
//|     `uvm_object_utils(mydata)
//|
//|     // declare data properties
//|
//|    function new(string name="mydata_inst");
//|      super.new(name);
//|    endfunction
//|
//|  endclass
//
// Below is an example usage of a ~utils~ macro for a user-defined component. 
//
//|  class my_comp extends uvm_component;
//| 
//|     `uvm_component_utils(my_comp)
//|
//|     // declare data properties
//|
//|    function new(string name, uvm_component parent=null);
//|      super.new(name,parent);
//|    endfunction
//|
//|  endclass
//
//------------------------------------------------------------------------------


// Define - UVM_FIELD_FLAG_SIZE
//
// The macro defines the number of bits in uvm_field_flag_t.  It may be defined by the user but it
// must be at least as large as parameter UVM_FIELD_FLAG_RESERVED_BITS.
//
`ifndef UVM_FIELD_FLAG_SIZE
  `define UVM_FIELD_FLAG_SIZE  UVM_FIELD_FLAG_RESERVED_BITS
`endif


// Definitions for the user to use inside their derived data class declarations.

// MACRO -- NODOCS -- `uvm_field_utils_begin

// MACRO -- NODOCS -- `uvm_field_utils_end
//
// These macros form a block in which `uvm_field_* macros can be placed. 
// Used as
//
//|  `uvm_field_utils_begin(TYPE)
//|    `uvm_field_* macros here
//|  `uvm_field_utils_end
//
// 
// These macros do ~not~ perform factory registration nor implement the
// ~get_type_name~ and ~create~ methods. Use this form when you need custom
// implementations of these two methods, or when you are setting up field macros
// for an abstract class (i.e. virtual class).

`define uvm_field_utils_begin(T)                                                \
function void do_execute_op( uvm_field_op op );                                 \
   uvm_field_flag_t local_op_type__; /* Used to avoid re-querying */            \
   T local_rhs__; /* Used for $casting copy and compare */                      \
   uvm_resource_base local_rsrc__; /* Used for UVM_SET ops */                   \
   string local_rsrc_name__;                                                    \
   uvm_object local_obj__; /* Used when trying to read uvm_object resources */  \
   bit local_success__; /* Used when trying to read resources */                \
   typedef T __local_type__; /* Used for referring to type T in field macros */ \
   int local_size__; /* Used when unpacking size values */                      \
   /* All possible policy classes */                                            \
   /* Using the same name as the do_* methods, allows macro reuse */            \
   uvm_printer printer;                                                         \
   uvm_comparer comparer;                                                       \
   uvm_recorder recorder;                                                       \
   uvm_packer packer;                                                           \
   uvm_copier copier;                                                           \
   /* Base class first */                                                       \
   super.do_execute_op(op);                                                     \
   void'($cast(local_rhs__, op.get_rhs()));                                     \
   if (($cast(local_rsrc__, op.get_rhs())) &&                                   \
       (local_rsrc__ != null))                                                  \
     local_rsrc_name__ = local_rsrc__.get_name();                               \
   local_op_type__ = op.get_op_type();                                          \
   case (local_op_type__)                                                      \
     UVM_PRINT: begin                                                           \
       $cast(printer, op.get_policy());                                         \
     end                                                                        \
     UVM_COMPARE: begin                                                         \
       if (local_rhs__ == null) return;                                         \
       $cast(comparer, op.get_policy());                                        \
     end                                                                        \
     UVM_RECORD: begin                                                          \
       $cast(recorder, op.get_policy());                                        \
     end                                                                        \
     UVM_PACK, UVM_UNPACK: begin                                                \
       $cast(packer, op.get_policy());                                          \
     end                                                                        \
     UVM_COPY: begin                                                            \
       if (local_rhs__ == null) return;                                         \
       $cast(copier, op.get_policy());                                          \
     end                                                                        \
     UVM_SET: begin                                                             \
       if (local_rsrc__ == null) return;                                        \
     end                                                                        \
     default:                                                                   \
       return; /* unknown op, just return */                                    \
   endcase                                                                      \
   
`define uvm_field_utils_end \
endfunction 


// MACRO -- NODOCS -- `uvm_object_utils

// MACRO -- NODOCS -- `uvm_object_param_utils

// MACRO -- NODOCS -- `uvm_object_utils_begin

// MACRO -- NODOCS -- `uvm_object_param_utils_begin

// MACRO -- NODOCS -- `uvm_object_utils_end
//
// <uvm_object>-based class declarations may contain one of the above forms of
// utility macros.
// 
// For simple objects with no field macros, use
//
//|  `uvm_object_utils(TYPE)
//    
// For simple objects with field macros, use
//
//|  `uvm_object_utils_begin(TYPE)
//|    `uvm_field_* macro invocations here
//|  `uvm_object_utils_end
//    
// For parameterized objects with no field macros, use
//
//|  `uvm_object_param_utils(TYPE)
//    
// For parameterized objects, with field macros, use
//
//|  `uvm_object_param_utils_begin(TYPE)
//|    `uvm_field_* macro invocations here
//|  `uvm_object_utils_end
//
// Simple (non-parameterized) objects use the uvm_object_utils* versions, which
// do the following:
//
// o Implements get_type_name, which returns TYPE as a string
//
// o Implements create, which allocates an object of type TYPE by calling its
//   constructor with no arguments. TYPE's constructor, if defined, must have
//   default values on all it arguments.
//
// o Registers the TYPE with the factory, using the string TYPE as the factory
//   lookup string for the type.
//
// o Implements the static get_type() method which returns a factory
//   proxy object for the type.
//
// o Implements the virtual get_object_type() method which works just like the
//   static get_type() method, but operates on an already allocated object.
//
// Parameterized classes must use the uvm_object_param_utils* versions. They
// differ from <`uvm_object_utils> only in that they do not supply a type name
// when registering the object with the factory. As such, name-based lookup with
// the factory for parameterized classes is not possible.
//
// The macros with _begin suffixes are the same as the non-suffixed versions
// except that they also start a block in which `uvm_field_* macros can be
// placed. The block must be terminated by `uvm_object_utils_end.
//

`define uvm_object_utils(T) \
  `m_uvm_object_registry_internal(T,T)  \
  `m_uvm_object_create_func(T) \
  `uvm_type_name_decl(`"T`")

`define uvm_object_param_utils(T) \
  `m_uvm_object_registry_param(T)  \
  `m_uvm_object_create_func(T)

`define uvm_object_utils_begin(T) \
  `uvm_object_utils(T) \
  `uvm_field_utils_begin(T) 

`define uvm_object_param_utils_begin(T) \
  `uvm_object_param_utils(T) \
  `uvm_field_utils_begin(T)

`define uvm_object_abstract_utils(T) \
  `m_uvm_object_abstract_registry_internal(T,T)  \
  `uvm_type_name_decl(`"T`")

`define uvm_object_abstract_param_utils(T) \
  `m_uvm_object_abstract_registry_param(T)

`define uvm_object_abstract_utils_begin(T) \
  `uvm_object_abstract_utils(T) \
  `uvm_field_utils_begin(T)
       
`define uvm_object_abstract_param_utils_begin(T) \
  `uvm_object_abstract_param_utils(T) \
  `uvm_field_utils_begin(T) 
       
`define uvm_object_utils_end \
  `uvm_field_utils_end

// MACRO -- NODOCS -- `uvm_component_utils

// MACRO -- NODOCS -- `uvm_component_param_utils

// MACRO -- NODOCS -- `uvm_component_utils_begin

// MACRO -- NODOCS -- `uvm_component_param_utils_begin

// MACRO -- NODOCS -- `uvm_component_end
//
// uvm_component-based class declarations may contain one of the above forms of
// utility macros.
//
// For simple components with no field macros, use
//
//|  `uvm_component_utils(TYPE)
//
// For simple components with field macros, use
//
//|  `uvm_component_utils_begin(TYPE)
//|    `uvm_field_* macro invocations here
//|  `uvm_component_utils_end
//
// For parameterized components with no field macros, use
//
//|  `uvm_component_param_utils(TYPE)
//
// For parameterized components with field macros, use
//
//|  `uvm_component_param_utils_begin(TYPE)
//|    `uvm_field_* macro invocations here
//|  `uvm_component_utils_end
//
// Simple (non-parameterized) components must use the uvm_components_utils*
// versions, which do the following:
//
// o Implements get_type_name, which returns TYPE as a string.
//
// o Implements create, which allocates a component of type TYPE using a two
//   argument constructor. TYPE's constructor must have a name and a parent
//   argument.
//
// o Registers the TYPE with the factory, using the string TYPE as the factory
//   lookup string for the type.
//
// o Implements the static get_type() method which returns a factory
//   proxy object for the type.
//
// o Implements the virtual get_object_type() method which works just like the
//   static get_type() method, but operates on an already allocated object.
//
// Parameterized classes must use the uvm_object_param_utils* versions. They
// differ from `uvm_object_utils only in that they do not supply a type name
// when registering the object with the factory. As such, name-based lookup with
// the factory for parameterized classes is not possible.
//
// The macros with _begin suffixes are the same as the non-suffixed versions
// except that they also start a block in which `uvm_field_* macros can be
// placed. The block must be terminated by `uvm_component_utils_end.
//

`define uvm_component_utils(T) \
   `m_uvm_component_registry_internal(T,T) \
   `uvm_type_name_decl(`"T`") \

`define uvm_component_param_utils(T) \
   `m_uvm_component_registry_param(T) \

   
`define uvm_component_utils_begin(T) \
   `uvm_component_utils(T) \
   `uvm_field_utils_begin(T) 

`define uvm_component_param_utils_begin(T) \
   `uvm_component_param_utils(T) \
   `uvm_field_utils_begin(T) 

`define uvm_component_abstract_utils(T) \
   `m_uvm_component_abstract_registry_internal(T,T) \
   `uvm_type_name_decl(`"T`") \

`define uvm_component_abstract_param_utils(T) \
   `m_uvm_component_abstract_registry_param(T) \

   
`define uvm_component_abstract_utils_begin(T) \
   `uvm_component_abstract_utils(T) \
   `uvm_field_utils_begin(T) 

`define uvm_component_abstract_param_utils_begin(T) \
   `uvm_component_abstract_param_utils(T) \
   `uvm_field_utils_begin(T) 

`define uvm_component_utils_end \
  `uvm_field_utils_end


// MACRO -- NODOCS -- `uvm_object_registry
//
// Register a uvm_object-based class with the factory
//
//| `uvm_object_registry(T,S)
//
// Registers a uvm_object-based class ~T~ and lookup
// string ~S~ with the factory. ~S~ typically is the
// name of the class in quotes. The <`uvm_object_utils>
// family of macros uses this macro.

`define uvm_object_registry(T,S) \
   typedef uvm_object_registry#(T,S) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction 


// MACRO -- NODOCS -- `uvm_component_registry
//
// Registers a uvm_component-based class with the factory
//
//| `uvm_component_registry(T,S)
//
// Registers a uvm_component-based class ~T~ and lookup
// string ~S~ with the factory. ~S~ typically is the
// name of the class in quotes. The <`uvm_object_utils>
// family of macros uses this macro.

`define uvm_component_registry(T,S) \
   typedef uvm_component_registry #(T,S) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction 


// uvm_new_func
// ------------

`define uvm_new_func \
  function new (string name, uvm_component parent); \
    super.new(name, parent); \
  endfunction


//-----------------------------------------------------------------------------
// INTERNAL MACROS - in support of *_utils macros -- do not use directly
//-----------------------------------------------------------------------------

// m_uvm_object_create_func
// ------------------------

`define m_uvm_object_create_func(T) \
   function uvm_object create (string name=""); \
     T tmp; \
     if (name=="") tmp = new(); \
     else tmp = new(name); \
     return tmp; \
   endfunction

// Macro --NODOCS-- uvm_type_name_decl(TNAME_STRING)
// Potentially public macro for Mantis 5003.
//
// This macro creates a statically accessible
// ~type_name~, and implements the virtual
// <uvm_object::get_type_name> method.
//
// *Note:*  When running with <`UVM_ENABLE_DEPRECATED_API>,
// the ~type_name~ member is declared as:
//| const static string type_name = TNAME_STRING;
// This is unsafe, as static initialization can cause races
// to occur.  When running without <`UVM_ENABLE_DEPRECATED_API>,
// the implementation is an static initialization safe function:
//| static function string type_name(); 
//|   return TNAME_STRING; 
//| endfunction : type_name
// 
`ifdef UVM_ENABLE_DEPRECATED_API
 `define uvm_type_name_decl(TNAME_STRING) \
     const static string type_name = TNAME_STRING; \
     virtual function string get_type_name(); \
       return TNAME_STRING; \
     endfunction : get_type_name
`else
 `define uvm_type_name_decl(TNAME_STRING) \
     static function string type_name(); \
       return TNAME_STRING; \
     endfunction : type_name \
     virtual function string get_type_name(); \
       return TNAME_STRING; \
     endfunction : get_type_name
`endif // !`ifdef UVM_ENABLE_DEPRECATED_API
     
// m_uvm_object_registry_internal
// ------------------------------

//This is needed due to an issue in of passing down strings
//created by args to lower level macros.
`define m_uvm_object_registry_internal(T,S) \
   typedef uvm_object_registry#(T,`"S`") type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction 


// m_uvm_object_registry_param
// ---------------------------

`define m_uvm_object_registry_param(T) \
   typedef uvm_object_registry #(T) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction 

// m_uvm_object_abstract_registry_internal
// ---------------------------------------

//This is needed due to an issue in of passing down strings
//created by args to lower level macros.
`define m_uvm_object_abstract_registry_internal(T,S) \
   typedef uvm_abstract_object_registry#(T,`"S`") type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction 


// m_uvm_object_abstract_registry_param
// ------------------------------------

`define m_uvm_object_abstract_registry_param(T) \
   typedef uvm_abstract_object_registry #(T) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction 


// m_uvm_component_registry_internal
// ---------------------------------

//This is needed due to an issue in of passing down strings
//created by args to lower level macros.
`define m_uvm_component_registry_internal(T,S) \
   typedef uvm_component_registry #(T,`"S`") type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction

// versions of the uvm_component_registry macros to be used with
// parameterized classes

// m_uvm_component_registry_param
// ------------------------------

`define m_uvm_component_registry_param(T) \
   typedef uvm_component_registry #(T) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction

// m_uvm_component_abstract_registry_internal
// ------------------------------------------

//This is needed due to an issue in of passing down strings
//created by args to lower level macros.
`define m_uvm_component_abstract_registry_internal(T,S) \
   typedef uvm_abstract_component_registry #(T,`"S`") type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction

// versions of the uvm_component_abstract_registry macros to be used with
// parameterized classes

// m_uvm_component_abstract_registry_param
// ---------------------------------------

`define m_uvm_component_abstract_registry_param(T) \
   typedef uvm_abstract_component_registry #(T) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function uvm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction



//------------------------------------------------------------------------------
//
// Group -- NODOCS -- Field Macros
//
// The `uvm_field_*  macros are invoked inside of the `uvm_*_utils_begin and
// `uvm_*_utils_end macro blocks to form "automatic" implementations of the
// core data methods: copy, compare, pack, unpack, record, print, and sprint.
//
// By using the macros, you do not have to implement any of the do_* methods 
// inherited from <uvm_object>. However, be aware that the field macros expand
// into general inline code that is not as run-time efficient nor as flexible
// as direct implementations of the do_* methods. 
//
// Below is an example usage of the field macros for a sequence item. 
//
//|  class my_trans extends uvm_sequence_item;
//| 
//|    cmd_t  cmd;
//|    int    addr;
//|    int    data[$];
//|    my_ext ext;
//|    string str;
//|
//|    `uvm_object_utils_begin(my_trans)
//|      `uvm_field_enum     (cmd_t, cmd, UVM_ALL_ON)
//|      `uvm_field_int      (addr, UVM_ALL_ON)
//|      `uvm_field_queue_int(data, UVM_ALL_ON)
//|      `uvm_field_object   (ext,  UVM_ALL_ON)
//|      `uvm_field_string   (str,  UVM_ALL_ON)
//|    `uvm_object_utils_end
//|
//|    function new(string name="mydata_inst");
//|      super.new(name);
//|    endfunction
//|
//|  endclass
//
// Below is an example usage of the field macros for a component.
//
//|  class my_comp extends uvm_component;
//| 
//|    my_comp_cfg  cfg;
//|
//|    `uvm_component_utils_begin(my_comp)
//|      `uvm_field_object   (cfg,  UVM_ALL_ON)
//|    `uvm_object_utils_end
//|
//|    function new(string name="my_comp_inst", uvm_component parent=null);
//|      super.new(name);
//|    endfunction
//|
//|  endclass
//
// Each `uvm_field_* macro is named according to the particular data type it
// handles: integrals, strings, objects, queues, etc., and each has at least two
// arguments: ~ARG~ and ~FLAG~.
//
// ARG -  is the instance name of the variable, whose type must be compatible with
// the macro being invoked. In the example, class variable ~addr~ is an integral type,
// so we use the ~`uvm_field_int~ macro.
//
// FLAG - if set to ~UVM_ALL_ON~, as in the example, the ARG variable will be
// included in all data methods. If FLAG is set to something other than
// ~UVM_ALL_ON~ or ~UVM_DEFAULT~, it specifies which data method implementations will
// ~not~ include the given variable. Thus, if ~FLAG~ is specified as ~NO_COMPARE~,
// the ARG variable will not affect comparison operations, but it will be
// included in everything else.
//
// All possible values for ~FLAG~ are listed and described below. Multiple flag
// values can be bitwise OR'ed together (in most cases they may be added together
// as well, but care must be taken when using the + operator to ensure that the
// same bit is not added more than once).
//
//   UVM_ALL_ON     - Set all operations on.
//   UVM_DEFAULT    - This is the recommended set of flags to pass 
//                      to the field macros.  Currently, it enables
//                      all of the operations, making it functionally
//                      identical to ~UVM_ALL_ON~.  In the future 
//                      however, additional flags could be added with
//                      a recommended default value of ~off~.
//
//   UVM_NOCOPY     - Do not copy this field.
//   UVM_NOCOMPARE  - Do not compare this field.
//   UVM_NOPRINT    - Do not print this field.
//   UVM_NOPACK     - Do not pack or unpack this field.
//
//   UVM_REFERENCE  - For object types, operate only on the handle (e.g. no deep copy)
//
//   UVM_PHYSICAL   - Treat as a physical field. Use physical setting in
//                      policy class for this field.
//   UVM_ABSTRACT   - Treat as an abstract field. Use the abstract setting
//                      in the policy class for this field.
//   UVM_READONLY   - Do not allow setting of this field from the set_*_local
//                      methods or during <uvm_component::apply_config_settings> operation.
//
//
// A radix for printing and recording can be specified by OR'ing one of the
// following constants in the ~FLAG~ argument
//
//   UVM_BIN      - Print / record the field in binary (base-2).
//   UVM_DEC      - Print / record the field in decimal (base-10).
//   UVM_UNSIGNED - Print / record the field in unsigned decimal (base-10).
//   UVM_OCT      - Print / record the field in octal (base-8).
//   UVM_HEX      - Print / record the field in hexadecimal (base-16).
//   UVM_STRING   - Print / record the field in string format.
//   UVM_TIME     - Print / record the field in time format.
//
//   Radix settings for integral types. Hex is the default radix if none is
//   specified.
//
// A UVM component should ~not~ be specified using the `uvm_field_object macro
// unless its flag includes UVM_REFERENCE.  Otherwise, the field macro will 
// implement deep copy, which is an illegal operation for uvm_components.
// You will get a FATAL error if you tried to copy or clone an object containing
// a component handle that was registered with a field macro without the
// UVM_REFERENCE flag. You will also get duplicate entries when printing
// component topology, as this functionality is already provided by UVM. 
//------------------------------------------------------------------------------

//-----------------------------------------------------------------------------
// Group -- NODOCS -- `uvm_field_* macros
//
// Macros that implement data operations for scalar properties.
//
//-----------------------------------------------------------------------------

// The m_uvm_* macros are implementation artifacts.  They are not intended to be
// directly used by the user.

`define m_uvm_field_radix(FLAG) uvm_radix_enum'((FLAG)&(UVM_RADIX))

`define m_uvm_field_recursion(FLAG) uvm_recursion_policy_enum'((FLAG)&(UVM_RECURSION))
     
`define m_uvm_field_begin(ARG, FLAG) \
  begin \
    case (local_op_type__)

`define m_uvm_field_end(ARG) \
    endcase \
  end
     

`define m_uvm_field_op_begin(OP, FLAG) \
UVM_``OP: \
  if (!((FLAG)&UVM_NO``OP)) begin

`define m_uvm_field_op_end(OP) \
  end
   
// MACRO -- NODOCS -- `uvm_field_int
//
// Implements the data operations for any packed integral property.
//
//|  `uvm_field_int(ARG,FLAG)
//
// ~ARG~ is an integral property of the class, and ~FLAG~ is a bitwise OR of
// one or more flag settings as described in <Field Macros> above.

`define uvm_field_int(ARG,FLAG) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_int(ARG, local_rhs__.ARG, `m_uvm_field_radix(FLAG)) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_int(ARG) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_int(ARG) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_int(`"ARG`", \
                      ARG, \
                      $bits(ARG), \
                      `m_uvm_field_radix(FLAG)) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_int(ARG, $bits(ARG), `m_uvm_field_radix(FLAG)) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_builtin_int_read(local_success__, \
                                       local_rsrc__, \
                                       ARG, \
                                       this) \
        /* TODO if(local_success__ && printing matches) */ \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)

// MACRO -- NODOCS -- `uvm_field_object
//
// Implements the data operations for a <uvm_object>-based property.
//
//|  `uvm_field_object(ARG,FLAG)
//
// ~ARG~ is an object property of the class, and ~FLAG~ is a bitwise OR of
// one or more flag settings as described in <Field Macros> above.

`define uvm_field_object(ARG,FLAG) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      `uvm_copy_object(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG)) \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_object(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG)) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
        `uvm_pack_object(ARG) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
        `uvm_unpack_object(ARG) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      recorder.record_object(`"ARG`", ARG); \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_object(ARG, `m_uvm_field_recursion(FLAG)) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_read(local_success__, \
                           local_rsrc__, \
                           uvm_object, \
                           local_obj__, \
                           this) \
        if (local_success__) begin \
          if (local_obj__ == null) begin \
            ARG = null; \
          end else if (!$cast(ARG, local_obj__)) begin \
             `uvm_warning("UVM/FIELDS/OBJ_TYPE", $sformatf("Can't set field '%s' on '%s' with '%s' type", \
                                                           `"ARG`", \
                                                           this.get_full_name(), \
                                                           local_obj__.get_type_name())) \
          end \
          /* TODO if(local_success__ && printing matches) */ \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)


// MACRO -- NODOCS -- `uvm_field_string
//
// Implements the data operations for a string property.
//
//|  `uvm_field_string(ARG,FLAG)
//
// ~ARG~ is a string property of the class, and ~FLAG~ is a bitwise OR of
// one or more flag settings as described in <Field Macros> above.

`define uvm_field_string(ARG,FLAG) \
  `m_uvm_field_begin(ARG, FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_string(ARG, local_rhs__.ARG) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_string(ARG) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_string(ARG) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_string(`"ARG`", ARG) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      printer.print_string(`"ARG`", ARG); \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_read(local_success__, \
                           local_rsrc__, \
                           string, \
                           ARG, \
                           this) \
              /* TODO if(local_success__ && printing matches) */ \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)


// MACRO -- NODOCS -- `uvm_field_enum
// 
// Implements the data operations for an enumerated property.
//
//|  `uvm_field_enum(T,ARG,FLAG)
//
// ~T~ is an enumerated _type_, ~ARG~ is an instance of that type, and
// ~FLAG~ is a bitwise OR of one or more flag settings as described in
// <Field Macros> above.

`define uvm_field_enum(T,ARG,FLAG) \
  `m_uvm_field_begin(ARG, FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_enum(ARG, local_rhs__.ARG, T) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_enum(ARG) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_enum(ARG, T) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_enum(`"ARG`", ARG, T) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      if (`m_uvm_field_radix(FLAG) inside {UVM_NORADIX, UVM_ENUM, UVM_STRING}) \
        `uvm_print_enum(T, ARG) \
      else \
        `uvm_print_int(ARG, $bits(ARG), `m_uvm_field_radix(FLAG)) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_resource_enum_read(local_success__, \
                                 local_rsrc__, \
                                 T, \
                                 ARG, \
                                 this) \
              /* TODO if(local_success__ && printing matches) */ \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)


// MACRO -- NODOCS -- `uvm_field_real
//
// Implements the data operations for any real property.
//
//|  `uvm_field_real(ARG,FLAG)
//
// ~ARG~ is an real property of the class, and ~FLAG~ is a bitwise OR of
// one or more flag settings as described in <Field Macros> above.

`define uvm_field_real(ARG,FLAG) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_real(ARG, local_rhs__.ARG) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_real(ARG) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_real(ARG) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_real(`"ARG`", ARG) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      printer.print_real(`"ARG`", ARG); \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_resource_real_read(local_success__, \
                                 local_rsrc__, \
                                 ARG, \
                                 this) \
              /* TODO if(local_success__ && printing matches) */ \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)

// MACRO -- NODOCS -- `uvm_field_event
//   
// Implements the data operations for an event property.
//
//|  `uvm_field_event(ARG,FLAG)
//
// ~ARG~ is an event property of the class, and ~FLAG~ is a bitwise OR of
// one or more flag settings as described in <Field Macros> above.

`define uvm_field_event(ARG,FLAG) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `m_uvm_compare_begin(ARG, local_rhs__.ARG) \
        comparer.print_msg({`"ARG`", " event miscompare"}); \
      `m_uvm_compare_end \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      printer.print_generic(`"ARG`", "event", -1, ""); \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)


//-----------------------------------------------------------------------------
// Group -- NODOCS -- `uvm_field_sarray_* macros
//                            
// Macros that implement data operations for one-dimensional static array
// properties.
//-----------------------------------------------------------------------------

// MACRO -- NODOCS -- `uvm_field_sarray_int
//
// Implements the data operations for a one-dimensional static array of
// integrals.
//
//|  `uvm_field_sarray_int(ARG,FLAG)
//
// ~ARG~ is a one-dimensional static array of integrals, and ~FLAG~
// is a bitwise OR of one or more flag settings as described in
// <Field Macros> above.

`define uvm_field_sarray_int(ARG,FLAG) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      if ((comparer.physical&&((FLAG)&UVM_PHYSICAL))|| \
          (comparer.abstract&&((FLAG)&UVM_ABSTRACT))|| \
          (!((FLAG)&UVM_PHYSICAL) && !((FLAG)&UVM_ABSTRACT))) \
        `uvm_compare_sarray_int(ARG, local_rhs__.ARG, `m_uvm_field_radix(FLAG)) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_sarray(ARG) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_sarray(ARG) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_int(ARG, `m_uvm_field_radix(FLAG))  \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_sarray_int(ARG, \
                            `m_uvm_field_radix(FLAG)) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/SARRAY_SIZE", $sformatf("Static array '%s.%s' cannot be resized via configuration.",  get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-1); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if ((local_index__ >= $size(ARG)) || (local_index__ < 0)) begin \
              `uvm_warning("UVM/FIELDS/SARRAY_IDX", $sformatf("Index '%d' is not valid for static array '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              $size(ARG))) \
            end \
            else begin \
              `uvm_resource_builtin_int_read(local_success__, \
                                             local_rsrc__, \
                                             ARG[local_index__], \
                                             this) \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)


// MACRO -- NODOCS -- `uvm_field_sarray_object
//
// Implements the data operations for a one-dimensional static array of
// <uvm_object>-based objects.
//
//|  `uvm_field_sarray_object(ARG,FLAG)
//
// ~ARG~ is a one-dimensional static array of <uvm_object>-based objects,
// and ~FLAG~ is a bitwise OR of one or more flag settings as described in
// <Field Macros> above.

`define uvm_field_sarray_object(ARG,FLAG) \
  `m_uvm_field_begin(ARG, FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      foreach(ARG[i]) begin \
        `uvm_copy_object(ARG[i], local_rhs__.ARG[i], `m_uvm_field_recursion(FLAG)) \
      end \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      if ((comparer.physical&&((FLAG)&UVM_PHYSICAL))|| \
          (comparer.abstract&&((FLAG)&UVM_ABSTRACT))|| \
          (!((FLAG)&UVM_PHYSICAL) && !((FLAG)&UVM_ABSTRACT))) \
        `uvm_compare_sarray_object(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG)) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
        foreach(ARG[i])  \
          `uvm_pack_object(ARG[i]) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
        foreach(ARG[i])  \
          `uvm_unpack_object(ARG[i]) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_object(ARG) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_sarray_object(ARG, `m_uvm_field_recursion(FLAG)) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/SARRAY_SIZE", $sformatf("Static array '%s.%s' cannot be resized via configuration.",  get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-1); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if ((local_index__ >= $size(ARG)) || (local_index__ < 0)) begin \
              `uvm_warning("UVM/FIELDS/SARRAY_IDX", $sformatf("Index '%d' is not valid for static array '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              $size(ARG))) \
            end \
            else begin \
              `uvm_resource_read(local_success__, \
                                 local_rsrc__, \
                                 uvm_object, \
                                 local_obj__, \
                                 this) \
              if (local_success__) begin \
                if (local_obj__ == null) begin \
                  ARG[local_index__] = null; \
                end else if (!$cast(ARG[local_index__], local_obj__)) begin \
                  `uvm_warning("UVM/FIELDS/OBJ_TYPE", $sformatf("Can't set field '%s[%d]' on '%s' with '%s' type", \
                                                                `"ARG`", \
                                                                local_index__, \
                                                                this.get_full_name(), \
                                                                local_obj__.get_type_name())) \
                end \
              end \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)   


// MACRO -- NODOCS -- `uvm_field_sarray_string
//
// Implements the data operations for a one-dimensional static array of
// strings.
//
//|  `uvm_field_sarray_string(ARG,FLAG)
//
// ~ARG~ is a one-dimensional static array of strings, and ~FLAG~ is a bitwise
// OR of one or more flag settings as described in <Field Macros> above.

`define uvm_field_sarray_string(ARG,FLAG) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      if ((comparer.physical&&((FLAG)&UVM_PHYSICAL))|| \
          (comparer.abstract&&((FLAG)&UVM_ABSTRACT))|| \
          (!((FLAG)&UVM_PHYSICAL) && !((FLAG)&UVM_ABSTRACT))) \
        `uvm_compare_sarray_string(ARG, local_rhs__.ARG) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      foreach(ARG[i]) \
        `uvm_pack_string(ARG[i]) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      foreach(ARG[i]) \
       `uvm_unpack_string(ARG[i]) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_string(ARG)  \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_sarray_string(ARG) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/SARRAY_SIZE", $sformatf("Static array '%s.%s' cannot be resized via configuration.",  get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-1); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if ((local_index__ >= $size(ARG)) || (local_index__ < 0)) begin \
              `uvm_warning("UVM/FIELDS/SARRAY_IDX", $sformatf("Index '%d' is not valid for static array '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              $size(ARG))) \
            end \
            else begin \
              `uvm_resource_read(local_success__, \
                                 local_rsrc__, \
                                 string, \
                                 ARG[local_index__], \
                                 this) \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)  


// MACRO -- NODOCS -- `uvm_field_sarray_enum
//
// Implements the data operations for a one-dimensional static array of
// enums.
//
//|  `uvm_field_sarray_enum(T,ARG,FLAG)
//
// ~T~ is a one-dimensional dynamic array of enums _type_, ~ARG~ is an
// instance of that type, and ~FLAG~ is a bitwise OR of one or more flag
// settings as described in <Field Macros> above.

`define uvm_field_sarray_enum(T,ARG,FLAG) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      if ((comparer.physical&&((FLAG)&UVM_PHYSICAL))|| \
          (comparer.abstract&&((FLAG)&UVM_ABSTRACT))|| \
          (!((FLAG)&UVM_PHYSICAL) && !((FLAG)&UVM_ABSTRACT))) \
        `uvm_compare_sarray_enum(ARG, local_rhs__.ARG, T) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      foreach (ARG[i]) \
        `uvm_pack_enumN(ARG[i], $bits(T)) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      foreach (ARG[i]) \
        `uvm_unpack_enumN(ARG[i], $bits(T), T) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_enum(ARG, T)  \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_sarray_enum(T, ARG) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/SARRAY_SIZE", $sformatf("Static array '%s.%s' cannot be resized via configuration.",  get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-1); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if ((local_index__ >= $size(ARG)) || (local_index__ < 0)) begin \
              `uvm_warning("UVM/FIELDS/SARRAY_IDX", $sformatf("Index '%d' is not valid for static array '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              $size(ARG))) \
            end \
            else begin \
              `uvm_resource_enum_read(local_success__, \
                                      local_rsrc__, \
                                      T, \
                                      ARG[local_index__], \
                                      this) \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)  


//-----------------------------------------------------------------------------
// Group -- NODOCS -- `uvm_field_array_* macros
//
// Macros that implement data operations for one-dimensional dynamic array
// properties.
//
// Implementation note:
// lines flagged with empty multi-line comments, /**/, are not needed or need
// to be different for fixed arrays, which cannot be resized. Fixed arrays 
// do not need to pack/unpack their size either, because their size is known;
// wouldn't hurt though if it allowed code consolidation. Unpacking would
// necessarily be different. */
// 
//-----------------------------------------------------------------------------

             
// m_uvm_QUEUE_resize
// ------------------

`define m_uvm_queue_resize(ARG, SZ) \
  if (ARG.size() > SZ) \
    ARG  = ARG[0:SZ-1]; \
  else \
    while (ARG.size() < SZ) ARG.push_back(ARG[SZ]);

// m_uvm_da_resize
// ------------------

`define m_uvm_da_resize(ARG, SZ) \
  if (ARG.size() != SZ) ARG = new[SZ](ARG); 


// m_uvm_field_qda_int
// -------------------

`define m_uvm_field_qda_int(TYPE,ARG,FLAG) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      if ((comparer.physical&&((FLAG)&UVM_PHYSICAL))|| \
          (comparer.abstract&&((FLAG)&UVM_ABSTRACT))|| \
          (!((FLAG)&UVM_PHYSICAL) && !((FLAG)&UVM_ABSTRACT))) \
        `uvm_compare_qda_int(ARG, local_rhs__.ARG, `m_uvm_field_radix(FLAG)) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_``TYPE``(ARG) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_``TYPE``(ARG) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_int(ARG, `m_uvm_field_radix(FLAG)) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_qda_int(TYPE, ARG, `m_uvm_field_radix(FLAG)) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_builtin_int_read(local_success__, \
                                       local_rsrc__, \
                                       local_size__, \
                                       this) \
        if (local_success__) \
          `m_uvm_``TYPE``_resize(ARG, local_size__) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-1); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if (local_index__ < 0) begin \
              `uvm_warning("UVM/FIELDS/QDA_IDX", $sformatf("Index '%0d' is not valid for field '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              ARG.size() ) ) \
            end \
            else begin \
              bit tmp_stream__[]; \
              `uvm_resource_builtin_int_read(local_success__, \
                                             local_rsrc__, \
                                             { << bit { tmp_stream__ }}, \
                                             this) \
              if (local_success__) begin \
                if (local_index__ >= ARG.size()) \
                  `m_uvm_``TYPE``_resize(ARG, local_index__ + 1) \
                tmp_stream__ = new[$bits(ARG[local_index__])] (tmp_stream__); \
                ARG[local_index__] = { << bit { tmp_stream__ }}; \
              end \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)

// MACRO -- NODOCS -- `uvm_field_array_int
//
// Implements the data operations for a one-dimensional dynamic array of
// integrals.
//
//|  `uvm_field_array_int(ARG,FLAG)
//
// ~ARG~ is a one-dimensional dynamic array of integrals,
// and ~FLAG~ is a bitwise OR of one or more flag settings as described in
// <Field Macros> above.

`define uvm_field_array_int(ARG,FLAG) \
   `m_uvm_field_qda_int(da,ARG,FLAG) 

`define m_uvm_field_qda_object(TYPE,ARG,FLAG) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      if ((`m_uvm_field_recursion(FLAG) == UVM_REFERENCE) || !local_rhs__.ARG.size()) \
        ARG = local_rhs__.ARG; \
      else begin \
        `m_uvm_``TYPE``_resize(ARG, local_rhs__.ARG.size()) \
        foreach (ARG[i]) \
          `uvm_copy_object(ARG[i], local_rhs__.ARG[i], `m_uvm_field_recursion(FLAG)) \
      end \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      if ((comparer.physical&&((FLAG)&UVM_PHYSICAL))|| \
          (comparer.abstract&&((FLAG)&UVM_ABSTRACT))|| \
          (!((FLAG)&UVM_PHYSICAL) && !((FLAG)&UVM_ABSTRACT))) \
        `uvm_compare_qda_object(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG)) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      packer.pack_field_int(ARG.size(), 32); \
      foreach (ARG[i]) \
        `uvm_pack_object(ARG[i]) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      local_size__ = packer.unpack_field_int(32); \
      `m_uvm_``TYPE``_resize(ARG, local_size__); \
      foreach (ARG[i]) \
        `uvm_unpack_object(ARG[i]) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_object(ARG) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_qda_object(TYPE, ARG, `m_uvm_field_recursion(FLAG)) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_builtin_int_read(local_success__, \
                                       local_rsrc__, \
                                       local_size__, \
                                       this) \
        if (local_success__) \
          `m_uvm_``TYPE``_resize(ARG, local_size__) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-1); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if (local_index__ < 0) begin \
              `uvm_warning("UVM/FIELDS/QDA_IDX", $sformatf("Index '%0d' is not valid for field '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              ARG.size() ) ) \
            end \
            else begin \
              `uvm_resource_read(local_success__, \
                                 local_rsrc__, \
                                 uvm_object, \
                                 local_obj__, \
                                 this) \
              if (local_success__) begin \
                if (local_index__ >= ARG.size()) \
                  `m_uvm_``TYPE``_resize(ARG, local_index__ + 1) \
                if (local_obj__ == null) begin \
                  ARG[local_index__] = null; \
                end else if (!$cast(ARG[local_index__], local_obj__)) begin \
                  `uvm_error("UVM/FIELDS/QDA_OBJ_TYPE", \
                             $sformatf("Can't set field '%s[%0d]' on '%s' with '%s' type", \
                                       `"ARG`", \
                                       local_index__, \
                                       this.get_full_name(), \
                                       local_obj__.get_type_name())) \
                end \
              end \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)

// MACRO -- NODOCS -- `uvm_field_array_object
//
// Implements the data operations for a one-dimensional dynamic array
// of <uvm_object>-based objects.
//
//|  `uvm_field_array_object(ARG,FLAG)
//
// ~ARG~ is a one-dimensional dynamic array of <uvm_object>-based objects,
// and ~FLAG~ is a bitwise OR of one or more flag settings as described in
// <Field Macros> above.

`define uvm_field_array_object(ARG,FLAG) \
  `m_uvm_field_qda_object(da,ARG,FLAG)



// MACRO -- NODOCS -- `uvm_field_array_string
//
// Implements the data operations for a one-dimensional dynamic array 
// of strings.
//
//|  `uvm_field_array_string(ARG,FLAG)
//
// ~ARG~ is a one-dimensional dynamic array of strings, and ~FLAG~ is a bitwise
// OR of one or more flag settings as described in <Field Macros> above.

`define uvm_field_array_string(ARG,FLAG) \
  `m_uvm_field_qda_string(da,ARG,FLAG)

`define m_uvm_field_qda_string(TYPE,ARG,FLAG) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      if ((comparer.physical&&((FLAG)&UVM_PHYSICAL))|| \
          (comparer.abstract&&((FLAG)&UVM_ABSTRACT))|| \
          (!((FLAG)&UVM_PHYSICAL) && !((FLAG)&UVM_ABSTRACT))) \
        `uvm_compare_qda_string(ARG, local_rhs__.ARG) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
       packer.pack_field_int(ARG.size(), 32); \
       foreach (ARG[i]) \
         `uvm_pack_string(ARG[i]) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      local_size__ = packer.unpack_field_int(32); \
      `m_uvm_``TYPE``_resize(ARG, local_size__) \
      foreach (ARG[i]) \
        `uvm_unpack_string(ARG[i]) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_string(ARG) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_qda_string(TYPE, ARG) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_builtin_int_read(local_success__, \
                                       local_rsrc__, \
                                       local_size__, \
                                       this) \
        if (local_success__) \
          `m_uvm_``TYPE``_resize(ARG, local_size__) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-1); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if (local_index__ < 0) begin \
              `uvm_warning("UVM/FIELDS/QDA_IDX", $sformatf("Index '%0d' is not valid for field '%s.%s' of size '%0d'", \
                                                           local_index__, \
                                                           get_full_name(), \
                                                           `"ARG`", \
                                                           ARG.size() ) ) \
            end \
            else begin \
              string tmp_string__; \
              `uvm_resource_read(local_success__, \
                                 local_rsrc__, \
                                 string, \
                                 tmp_string__, \
                                 this) \
              if (local_success__) begin \
                if (local_index__ >= ARG.size()) \
                  `m_uvm_``TYPE``_resize(ARG, local_index__ + 1) \
                ARG[local_index__]  = tmp_string__; \
              end \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)

// MACRO -- NODOCS -- `uvm_field_array_enum
//
// Implements the data operations for a one-dimensional dynamic array of
// enums.
//
//|  `uvm_field_array_enum(T,ARG,FLAG)
//
// ~T~ is a one-dimensional dynamic array of enums _type_,
// ~ARG~ is an instance of that type, and ~FLAG~ is a bitwise OR of
// one or more flag settings as described in <Field Macros> above.

`define uvm_field_array_enum(T,ARG,FLAG) \
  `m_field_qda_enum(da,T,ARG,FLAG) 

`define m_field_qda_enum(TYPE,T,ARG,FLAG) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      if ((comparer.physical&&((FLAG)&UVM_PHYSICAL))|| \
          (comparer.abstract&&((FLAG)&UVM_ABSTRACT))|| \
          (!((FLAG)&UVM_PHYSICAL) && !((FLAG)&UVM_ABSTRACT))) \
        `uvm_compare_qda_enum(ARG, local_rhs__.ARG, T) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
       packer.pack_field_int(ARG.size(), 32); \
       foreach (ARG[i]) \
         `uvm_pack_enumN(ARG[i], $bits(T)) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      local_size__ = packer.unpack_field_int(32); \
      `m_uvm_``TYPE``_resize(ARG, local_size__) \
      foreach (ARG[i]) \
        `uvm_unpack_enumN(ARG[i], $bits(T), T) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_enum(ARG, T) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_qda_enum(TYPE, T, ARG) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_builtin_int_read(local_success__, \
                                       local_rsrc__, \
                                       local_size__, \
                                       this) \
        if (local_success__) \
          `m_uvm_``TYPE``_resize(ARG, local_size__) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-1); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if (local_index__ < 0) begin \
              `uvm_warning("UVM/FIELDS/QDA_IDX", $sformatf("Index '%0d' is not valid for field '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              ARG.size() ) ) \
            end \
            else begin \
              T tmp_enum__; \
              `uvm_resource_enum_read(local_success__, \
                                      local_rsrc__, \
                                      T, \
                                      tmp_enum__, \
                                      this) \
              if (local_success__) begin \
                if (local_index__ >= ARG.size()) \
                  `m_uvm_``TYPE``_resize(ARG, local_index__ + 1) \
                ARG[local_index__] = tmp_enum__; \
              end \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)

//-----------------------------------------------------------------------------
// Group -- NODOCS -- `uvm_field_queue_* macros
//
// Macros that implement data operations for dynamic queues.
//
//-----------------------------------------------------------------------------

// MACRO -- NODOCS -- `uvm_field_queue_int
//
// Implements the data operations for a queue of integrals.
//
//|  `uvm_field_queue_int(ARG,FLAG)
//
// ~ARG~ is a one-dimensional queue of integrals,
// and ~FLAG~ is a bitwise OR of one or more flag settings as described in
// <Field Macros> above.

`define uvm_field_queue_int(ARG,FLAG) \
  `m_uvm_field_qda_int(queue,ARG,FLAG)

// MACRO -- NODOCS -- `uvm_field_queue_object
//
// Implements the data operations for a queue of <uvm_object>-based objects.
//
//|  `uvm_field_queue_object(ARG,FLAG)
//
// ~ARG~ is a one-dimensional queue of <uvm_object>-based objects,
// and ~FLAG~ is a bitwise OR of one or more flag settings as described in
// <Field Macros> above.

`define uvm_field_queue_object(ARG,FLAG) \
  `m_uvm_field_qda_object(queue,ARG,FLAG)


// MACRO -- NODOCS -- `uvm_field_queue_string
//
// Implements the data operations for a queue of strings.
//
//|  `uvm_field_queue_string(ARG,FLAG)
//
// ~ARG~ is a one-dimensional queue of strings, and ~FLAG~ is a bitwise
// OR of one or more flag settings as described in <Field Macros> above.

`define uvm_field_queue_string(ARG,FLAG) \
  `m_uvm_field_qda_string(queue,ARG,FLAG)


// MACRO -- NODOCS -- `uvm_field_queue_enum
//
// Implements the data operations for a one-dimensional queue of enums.
//
//|  `uvm_field_queue_enum(T,ARG,FLAG)
//
// ~T~ is a queue of enums _type_, ~ARG~ is an instance of that type,
// and ~FLAG~ is a bitwise OR of one or more flag settings as described
// in <Field Macros> above.

`define uvm_field_queue_enum(T,ARG,FLAG) \
  `m_field_qda_enum(queue,T,ARG,FLAG)


//-----------------------------------------------------------------------------
// Group -- NODOCS -- `uvm_field_aa_*_string macros
//
// Macros that implement data operations for associative arrays indexed
// by ~string~.
//
//-----------------------------------------------------------------------------

// MACRO -- NODOCS -- `uvm_field_aa_int_string
//
// Implements the data operations for an associative array of integrals indexed
// by ~string~.
//
//|  `uvm_field_aa_int_string(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with string key, and ~FLAG~ is a bitwise OR of one or more flag settings as
// described in <Field Macros> above.

`define uvm_field_aa_int_string(ARG, FLAG) \
  `m_uvm_field_begin(ARG, FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_int_string(ARG, local_rhs__.ARG, `m_uvm_field_radix(FLAG)) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_aa_int_string(ARG) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_aa_int_string(ARG) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_aa_int_string(ARG, `m_uvm_field_radix(FLAG)) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/AA_SIZE", $sformatf("Associative array '%s.%s' cannot be resized via configuration.",  get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index__ = local_rsrc_name__.substr(local_name__.len(), \
                                                          local_rsrc_name__.len()-1); \
          `uvm_resource_builtin_int_read(local_success__, \
                                         local_rsrc__, \
                                         ARG[local_index__], \
                                         this) \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)


// MACRO -- NODOCS -- `uvm_field_aa_object_string
//
// Implements the data operations for an associative array of <uvm_object>-based
// objects indexed by ~string~.
//
//|  `uvm_field_aa_object_string(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of objects
// with string key, and ~FLAG~ is a bitwise OR of one or more flag settings as
// described in <Field Macros> above.

`define uvm_field_aa_object_string(ARG, FLAG) \
  `m_uvm_field_begin(ARG, FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_object_string(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG)) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
        `uvm_pack_aa_object_string(ARG) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
      `uvm_unpack_aa_object_string(ARG) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_aa_object_string(ARG, `m_uvm_field_recursion(FLAG)) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/AA_SIZE", $sformatf("Associative array '%s.%s' cannot be resized via configuration.",  get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index__ = local_rsrc_name__.substr(local_name__.len(), \
                                                          local_rsrc_name__.len()-1); \
          `uvm_resource_read(local_success__, \
                             local_rsrc__, \
                             uvm_object, \
                             local_obj__, \
                             this) \
          if (local_success__) begin \
            if (local_obj__ == null) begin \
              ARG[local_index__] = null; \
            end else if (!$cast(ARG[local_index__], local_obj__)) begin \
              `uvm_warning("UVM/FIELDS/OBJ_TYPE", $sformatf("Can't set field '%s[%s]' on '%s' with '%s' type", \
                                                            `"ARG`", \
                                                            local_index__, \
                                                            this.get_full_name(), \
                                                            local_obj__.get_type_name())) \
            end \
          end \
          /* TODO if(local_success__ && printing matches) */ \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)


// MACRO -- NODOCS -- `uvm_field_aa_string_string
//
// Implements the data operations for an associative array of strings indexed
// by ~string~.
//
//|  `uvm_field_aa_string_string(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of strings
// with string key, and ~FLAG~ is a bitwise OR of one or more flag settings as
// described in <Field Macros> above.

`define uvm_field_aa_string_string(ARG, FLAG) \
  `m_uvm_field_begin(ARG, FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_string_string(ARG, local_rhs__.ARG) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_aa_string_string(ARG) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_aa_string_string(ARG) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_aa_string_string(ARG) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/AA_SIZE", $sformatf("Associative array '%s.%s' cannot be resized via configuration.",  get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index__ = local_rsrc_name__.substr(local_name__.len(), \
                                                          local_rsrc_name__.len()-1); \
          `uvm_resource_read(local_success__, \
                             local_rsrc__, \
                             string, \
                             ARG[local_index__], \
                             this) \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)


//-----------------------------------------------------------------------------
// Group -- NODOCS -- `uvm_field_aa_*_int macros
//
// Macros that implement data operations for associative arrays indexed by an
// integral type.
//
//-----------------------------------------------------------------------------

// MACRO -- NODOCS -- `uvm_field_aa_object_int
//
// Implements the data operations for an associative array of <uvm_object>-based
// objects indexed by the ~int~ data type.
//
//|  `uvm_field_aa_object_int(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of objects
// with ~int~ key, and ~FLAG~ is a bitwise OR of one or more flag settings as
// described in <Field Macros> above.

`define uvm_field_aa_object_int(ARG, FLAG) \
  `m_uvm_field_begin(ARG, FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_object_int(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG)) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      /* Unsupported, unpacking needs explicit index width */ \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      /* Unsupported, unpacking needs explicit index width */ \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_aa_object_int(ARG, `m_uvm_field_recursion(FLAG)) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/AA_SIZE", $sformatf("Associative array '%s.%s' cannot be resized via configuration.",  get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-1); \
          `uvm_warning("UVM/FIELDS/AA_INT_SET", $sformatf("Can't set '%s.%s[%s]' of unknown index type", \
                                                          get_full_name(), \
                                                          `"ARG`", \
                                                          local_index_str__)) \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)

// Not LRM, but supports packing + configuration
`define uvm_field_aa_object_key(KEY, ARG, FLAG) \
  `m_uvm_field_begin(ARG, FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_object_int(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG)) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
        `uvm_pack_aa_object_intN(ARG, $bits(KEY)) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      if (`m_uvm_field_recursion(FLAG) != UVM_REFERENCE) \
        `uvm_unpack_aa_object_intN(ARG, $bits(KEY)) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_aa_object_int(ARG, `m_uvm_field_recursion(FLAG), KEY) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/SARRAY_SIZE", $sformatf("Static array '%s.%s' cannot be resized via configuration.",  get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-1); \
          KEY local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            `uvm_resource_read(local_success__, \
                               local_rsrc__, \
                               uvm_object, \
                               local_obj__, \
                               this) \
            if (local_success__) begin \
              if (local_obj__ == null) begin \
                ARG[local_index__] = null; \
              end else if (!$cast(ARG[local_index__], local_obj__)) begin \
                `uvm_warning("UVM/FIELDS/OBJ_TYPE", $sformatf("Can't set field '%s[%d]' on '%s' with '%s' type", \
                                                              `"ARG`", \
                                                              local_index__, \
                                                              this.get_full_name(), \
                                                              local_obj__.get_type_name())) \
              end \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)

// Not LRM, oversight?
`define uvm_field_aa_string_int(ARG, FLAG) \
  `m_uvm_field_begin(ARG, FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_string_int(ARG, local_rhs__.ARG) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      /* Unsupported, unpacking requires explicit data width */ \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      /* Unsupported, unpacking requires explicit data width */ \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      /* TODO */ \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/AA_SIZE", $sformatf("Associative array '%s.%s' cannot be resized via configuration.",  get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
          `uvm_warning("UVM/FIELDS/AA_INT_SET", $sformatf("Can't set '%s.%s[%s]' of unknown index type", \
                                                          get_full_name(), \
                                                          `"ARG`", \
                                                          local_index_str__)) \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)

// Not LRM, but supports packing + configuration
`define uvm_field_aa_string_key(KEY, ARG, FLAG) \
  `m_uvm_field_begin(ARG, FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_string_int(ARG, local_rhs__.ARG, `m_uvm_field_recursion(FLAG)) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_aa_string_intN(ARG, $bits(KEY)) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_aa_string_intN(ARG, $bits(KEY)) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      /* TODO */ \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/SARRAY_SIZE", $sformatf("Static array '%s.%s' cannot be resized via configuration.",  get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-1); \
          KEY local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            `uvm_resource_read(local_success__, \
                               local_rsrc__, \
                               string, \
                               ARG[local_index__], \
                               this) \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)

// MACRO -- NODOCS -- `uvm_field_aa_int_int
//
// Implements the data operations for an associative array of integral
// types indexed by the ~int~ data type.
//
//|  `uvm_field_aa_int_int(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~int~ key, and ~FLAG~ is a bitwise OR of one or more flag settings as
// described in <Field Macros> above.

`define uvm_field_aa_int_int(ARG, FLAG) \
  `uvm_field_aa_int_key(int, ARG, FLAG) \


// MACRO -- NODOCS -- `uvm_field_aa_int_int_unsigned
//
// Implements the data operations for an associative array of integral
// types indexed by the ~int unsigned~ data type.
//
//|  `uvm_field_aa_int_int_unsigned(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~int unsigned~ key, and ~FLAG~ is a bitwise OR of one or more flag
// settings as described in <Field Macros> above.

`define uvm_field_aa_int_int_unsigned(ARG, FLAG) \
  `uvm_field_aa_int_key(int unsigned, ARG, FLAG)


// MACRO -- NODOCS -- `uvm_field_aa_int_integer
//
// Implements the data operations for an associative array of integral
// types indexed by the ~integer~ data type.
//
//|  `uvm_field_aa_int_integer(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~integer~ key, and ~FLAG~ is a bitwise OR of one or more flag settings
// as described in <Field Macros> above.

`define uvm_field_aa_int_integer(ARG, FLAG) \
  `uvm_field_aa_int_key(integer, ARG, FLAG)


// MACRO -- NODOCS -- `uvm_field_aa_int_integer_unsigned
//
// Implements the data operations for an associative array of integral
// types indexed by the ~integer unsigned~ data type.
//
//|  `uvm_field_aa_int_integer_unsigned(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~integer unsigned~ key, and ~FLAG~ is a bitwise OR of one or more 
// flag settings as described in <Field Macros> above.

`define uvm_field_aa_int_integer_unsigned(ARG, FLAG) \
  `uvm_field_aa_int_key(integer unsigned, ARG, FLAG)


// MACRO -- NODOCS -- `uvm_field_aa_int_byte
//
// Implements the data operations for an associative array of integral
// types indexed by the ~byte~ data type.
//
//|  `uvm_field_aa_int_byte(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~byte~ key, and ~FLAG~ is a bitwise OR of one or more flag settings as
// described in <Field Macros> above.

`define uvm_field_aa_int_byte(ARG, FLAG) \
  `uvm_field_aa_int_key(byte, ARG, FLAG)


// MACRO -- NODOCS -- `uvm_field_aa_int_byte_unsigned
//
// Implements the data operations for an associative array of integral
// types indexed by the ~byte unsigned~ data type.
//
//|  `uvm_field_aa_int_byte_unsigned(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~byte unsigned~ key, and ~FLAG~ is a bitwise OR of one or more flag
// settings as described in <Field Macros> above.

`define uvm_field_aa_int_byte_unsigned(ARG, FLAG) \
  `uvm_field_aa_int_key(byte unsigned, ARG, FLAG)


// MACRO -- NODOCS -- `uvm_field_aa_int_shortint
//
// Implements the data operations for an associative array of integral
// types indexed by the ~shortint~ data type.
//
//|  `uvm_field_aa_int_shortint(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~shortint~ key, and ~FLAG~ is a bitwise OR of one or more flag
// settings as described in <Field Macros> above.

`define uvm_field_aa_int_shortint(ARG, FLAG) \
  `uvm_field_aa_int_key(shortint, ARG, FLAG)


// MACRO -- NODOCS -- `uvm_field_aa_int_shortint_unsigned
//
// Implements the data operations for an associative array of integral
// types indexed by the ~shortint unsigned~ data type.
//
//|  `uvm_field_aa_int_shortint_unsigned(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~shortint unsigned~ key, and ~FLAG~ is a bitwise OR of one or more
// flag settings as described in <Field Macros> above.

`define uvm_field_aa_int_shortint_unsigned(ARG, FLAG) \
  `uvm_field_aa_int_key(shortint unsigned, ARG, FLAG)


// MACRO -- NODOCS -- `uvm_field_aa_int_longint
//
// Implements the data operations for an associative array of integral
// types indexed by the ~longint~ data type.
//
//|  `uvm_field_aa_int_longint(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~longint~ key, and ~FLAG~ is a bitwise OR of one or more flag settings
// as described in <Field Macros> above.

`define uvm_field_aa_int_longint(ARG, FLAG) \
  `uvm_field_aa_int_key(longint, ARG, FLAG)


// MACRO -- NODOCS -- `uvm_field_aa_int_longint_unsigned
//
// Implements the data operations for an associative array of integral
// types indexed by the ~longint unsigned~ data type.
//
//|  `uvm_field_aa_int_longint_unsigned(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~longint unsigned~ key, and ~FLAG~ is a bitwise OR of one or more
// flag settings as described in <Field Macros> above.

`define uvm_field_aa_int_longint_unsigned(ARG, FLAG) \
  `uvm_field_aa_int_key(longint unsigned, ARG, FLAG)


// MACRO -- NODOCS -- `uvm_field_aa_int_key
//
// Implements the data operations for an associative array of integral
// types indexed by any integral key data type. 
//
//|  `uvm_field_aa_int_key(KEY,ARG,FLAG)
//
// ~KEY~ is the data type of the integral key, ~ARG~ is the name of a property 
// that is an associative array of integrals, and ~FLAG~ is a bitwise OR of one 
// or more flag settings as described in <Field Macros> above.

`define uvm_field_aa_int_key(KEY, ARG, FLAG) \
  `m_uvm_field_begin(ARG, FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_int_int(ARG, local_rhs__.ARG, `m_uvm_field_radix(FLAG)) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_aa_int_intN(ARG, $bits(KEY)) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_aa_int_intN(ARG, $bits(KEY)) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_aa_int_int(ARG, `m_uvm_field_radix(FLAG), , KEY) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/AA_SIZE", $sformatf("Associative array '%s.%s' cannot be resized via configuration.",  get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-1); \
          KEY local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            `uvm_resource_int_read(local_success__, \
                                   local_rsrc__, \
                                   KEY, \
                                   ARG[local_index__], \
                                   this) \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)


// MACRO -- NODOCS -- `uvm_field_aa_int_enumkey
//
// Implements the data operations for an associative array of integral
// types indexed by any enumeration key data type. 
//
//|  `uvm_field_aa_int_enumkey(KEY, ARG,FLAG)
//
// ~KEY~ is the enumeration type of the key, ~ARG~ is the name of a property 
// that is an associative array of integrals, and ~FLAG~ is a bitwise OR of one 
// or more flag settings as described in <Field Macros> above.

`define uvm_field_aa_int_enumkey(KEY, ARG, FLAG) \
  `m_uvm_field_begin(ARG, FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      `uvm_compare_aa_int_int(ARG, local_rhs__.ARG, `m_uvm_field_radix(FLAG)) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_aa_int_enum(ARG, KEY) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_aa_int_enum(ARG, KEY) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_aa_int_enum(KEY, ARG, `m_uvm_field_radix(FLAG)) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/AA_SIZE", $sformatf("Associative array '%s.%s' cannot be resized via configuration.",  get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-1); \
          KEY local_index__; \
          bit[$bits(KEY)-1:0] local_bit_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_bit_index__); \
          if (local_code__ > 0) begin \
            local_index__ = KEY'(local_bit_index__); \
            `uvm_resource_int_read(local_success__, \
                                   local_rsrc__, \
                                   KEY, \
                                   ARG[local_index__], \
                                   this) \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)

//-- Field Macros for arrays of real (Non-LRM enhancement)
`define uvm_field_sarray_real(ARG,FLAG) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      if ((comparer.physical&&((FLAG)&UVM_PHYSICAL))|| \
          (comparer.abstract&&((FLAG)&UVM_ABSTRACT))|| \
          (!((FLAG)&UVM_PHYSICAL) && !((FLAG)&UVM_ABSTRACT))) \
        `uvm_compare_sarray_real(ARG, local_rhs__.ARG) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_sarray_real(ARG) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_sarray_real(ARG) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_real(ARG)  \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_sarray_real(ARG) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
         `uvm_warning("UVM/FIELDS/SARRAY_SIZE", $sformatf("Static array '%s.%s' cannot be resized via configuration.",  get_full_name(), `"ARG`") ) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-1); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if ((local_index__ >= $size(ARG)) || (local_index__ < 0)) begin \
              `uvm_warning("UVM/FIELDS/SARRAY_IDX", $sformatf("Index '%d' is not valid for static array '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              $size(ARG))) \
            end \
            else begin \
              `uvm_resource_real_read(local_success__, \
                                      local_rsrc__, \
                                      ARG[local_index__], \
                                      this) \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)

// m_uvm_field_qda_real
// -------------------

`define m_uvm_field_qda_real(TYPE,ARG,FLAG) \
  `m_uvm_field_begin(ARG,FLAG) \
    `m_uvm_field_op_begin(COPY,FLAG) \
      ARG = local_rhs__.ARG; \
    `m_uvm_field_op_end(COPY) \
    `m_uvm_field_op_begin(COMPARE,FLAG) \
      if ((comparer.physical&&((FLAG)&UVM_PHYSICAL))|| \
          (comparer.abstract&&((FLAG)&UVM_ABSTRACT))|| \
          (!((FLAG)&UVM_PHYSICAL) && !((FLAG)&UVM_ABSTRACT))) \
        `uvm_compare_qda_real(ARG, local_rhs__.ARG) \
    `m_uvm_field_op_end(COMPARE) \
    `m_uvm_field_op_begin(PACK,FLAG) \
      `uvm_pack_``TYPE``_real(ARG) \
    `m_uvm_field_op_end(PACK) \
    `m_uvm_field_op_begin(UNPACK,FLAG) \
      `uvm_unpack_``TYPE``_real(ARG) \
    `m_uvm_field_op_end(UNPACK) \
    `m_uvm_field_op_begin(RECORD,FLAG) \
      `uvm_record_qda_real(ARG) \
    `m_uvm_field_op_end(RECORD) \
    `m_uvm_field_op_begin(PRINT,FLAG) \
      `uvm_print_qda_real(TYPE, ARG) \
    `m_uvm_field_op_end(PRINT) \
    `m_uvm_field_op_begin(SET,FLAG) \
      if(local_rsrc_name__ == `"ARG`") begin \
        `uvm_resource_real_read(local_success__, \
                                local_rsrc__, \
                                local_size__, \
                                this) \
        if (local_success__) \
          `m_uvm_``TYPE``_resize(ARG, local_size__) \
      end \
      else begin \
        string local_name__ = {`"ARG`", "["}; \
        if (local_rsrc_name__.len() && \
            local_rsrc_name__[local_rsrc_name__.len()-1] == "]" && \
            local_rsrc_name__.substr(0, local_name__.len()-1) == local_name__) begin \
          string local_index_str__ = local_rsrc_name__.substr(local_name__.len(), \
                                                              local_rsrc_name__.len()-1); \
          int local_index__; \
          /* TODO: Non-decimal indexes */ \
          int local_code__ = $sscanf(local_index_str__, "%d", local_index__); \
          if (local_code__ > 0) begin \
            if (local_index__ < 0) begin \
              `uvm_warning("UVM/FIELDS/QDA_IDX", $sformatf("Index '%0d' is not valid for field '%s.%s' of size '%0d'", \
                                                              local_index__, \
                                                              get_full_name(), \
                                                              `"ARG`", \
                                                              ARG.size() ) ) \
            end \
            else begin \
              real tmp_real__; \
              `uvm_resource_real_read(local_success__, \
                                      local_rsrc__, \
                                      tmp_real__, \
                                      this) \
              if (local_success__) begin \
                if (local_index__ >= ARG.size()) \
                  `m_uvm_``TYPE``_resize(ARG, local_index__ + 1) \
                ARG[local_index__] = tmp_real__; \
              end \
            end \
          end \
        end \
      end \
    `m_uvm_field_op_end(SET) \
  `m_uvm_field_end(ARG)

`define uvm_field_array_real(ARG,FLAG) \
  `m_uvm_field_qda_real(da,ARG,FLAG)

`define uvm_field_queue_real(ARG,FLAG) \
  `m_uvm_field_qda_real(queue,ARG,FLAG)
                                                              
`endif // !`ifdef UVM_EMPTY_MACROS
                                                              
`endif  // UVM_OBJECT_DEFINES_SVH
