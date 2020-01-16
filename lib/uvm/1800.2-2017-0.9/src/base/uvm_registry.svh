//
//------------------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2014 Intel Corporation
// Copyright 2011-2014 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2011 AMD
// Copyright 2014-2018 NVIDIA Corporation
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
//------------------------------------------------------------------------------

`ifndef UVM_REGISTRY_SVH
`define UVM_REGISTRY_SVH

//------------------------------------------------------------------------------
// Title -- NODOCS -- Factory Component and Object Wrappers
//
// Topic: Intro
//
// This section defines the proxy component and object classes used by the
// factory. To avoid the overhead of creating an instance of every component
// and object that get registered, the factory holds lightweight wrappers,
// or proxies. When a request for a new object is made, the factory calls upon
// the proxy to create the object it represents. 
//------------------------------------------------------------------------------

typedef class uvm_registry_common;
typedef class uvm_registry_component_creator;
typedef class uvm_registry_object_creator;

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_component_registry #(T,Tname)
//
// The uvm_component_registry serves as a lightweight proxy for a component of
// type ~T~ and type name ~Tname~, a string. The proxy enables efficient
// registration with the <uvm_factory>. Without it, registration would
// require an instance of the component itself.
//
// See <Usage> section below for information on using uvm_component_registry.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 8.2.3.1
class uvm_component_registry #(type T=uvm_component, string Tname="<unknown>")
                                           extends uvm_object_wrapper;
  typedef uvm_component_registry #(T,Tname) this_type;
  typedef uvm_registry_common#( this_type, uvm_registry_component_creator, T ) common_type;

  // Function -- NODOCS -- create_component
  //
  // Creates a component of type T having the provided ~name~ and ~parent~.
  // This is an override of the method in <uvm_object_wrapper>. It is
  // called by the factory after determining the type of object to create.
  // You should not call this method directly. Call <create> instead.

  // @uvm-ieee 1800.2-2017 auto 8.2.3.2.1
  virtual function uvm_component create_component (string name,
                                                   uvm_component parent);
    T obj;
    obj = new(name, parent);
    return obj;
  endfunction


   static function string type_name();
     return Tname;
   endfunction : type_name

  // Function -- NODOCS -- get_type_name 
  //
  // Returns the value given by the string parameter, ~Tname~. This method
  // overrides the method in <uvm_object_wrapper>.

  // @uvm-ieee 1800.2-2017 auto 8.2.3.2.2
  virtual function string get_type_name();
     common_type common = common_type::get();
     return common.get_type_name();
  endfunction


  static function this_type get();
     static this_type m_inst;
     if (m_inst == null)
       m_inst = new();
    return m_inst;
  endfunction

  // @uvm-ieee 1800.2-2017 auto 8.2.3.2.7
  virtual function void initialize();
     common_type common = common_type::get();
     common.initialize();
  endfunction
  
  
  // Function -- NODOCS -- create
  //
  // Returns an instance of the component type, ~T~, represented by this proxy,
  // subject to any factory overrides based on the context provided by the
  // ~parent~'s full name. The ~contxt~ argument, if supplied, supersedes the
  // ~parent~'s context. The new instance will have the given leaf ~name~
  // and ~parent~.

  // @uvm-ieee 1800.2-2017 auto 8.2.3.2.4
  static function T create(string name, uvm_component parent, string contxt="");
    return common_type::create( name, parent, contxt );
  endfunction


  // Function -- NODOCS -- set_type_override
  //
  // Configures the factory to create an object of the type represented by
  // ~override_type~ whenever a request is made to create an object of the type,
  // ~T~, represented by this proxy, provided no instance override applies. The
  // original type, ~T~, is typically a super class of the override type. 

  // @uvm-ieee 1800.2-2017 auto 8.2.3.2.5
  static function void set_type_override (uvm_object_wrapper override_type,
                                          bit replace=1);
    common_type::set_type_override( override_type, replace );
  endfunction


  // Function -- NODOCS -- set_inst_override
  //
  // Configures the factory to create a component of the type represented by
  // ~override_type~ whenever a request is made to create an object of the type,
  // ~T~, represented by this proxy,  with matching instance paths. The original
  // type, ~T~, is typically a super class of the override type.
  //
  // If ~parent~ is not specified, ~inst_path~ is interpreted as an absolute
  // instance path, which enables instance overrides to be set from outside
  // component classes. If ~parent~ is specified, ~inst_path~ is interpreted
  // as being relative to the ~parent~'s hierarchical instance path, i.e.
  // ~{parent.get_full_name(),".",inst_path}~ is the instance path that is
  // registered with the override. The ~inst_path~ may contain wildcards for
  // matching against multiple contexts.

  // @uvm-ieee 1800.2-2017 auto 8.2.3.2.6
  static function void set_inst_override(uvm_object_wrapper override_type,
                                         string inst_path,
                                         uvm_component parent=null);
    common_type::set_inst_override( override_type, inst_path, parent );
  endfunction

endclass


//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_object_registry #(T,Tname)
//
// The uvm_object_registry serves as a lightweight proxy for a <uvm_object> of
// type ~T~ and type name ~Tname~, a string. The proxy enables efficient
// registration with the <uvm_factory>. Without it, registration would
// require an instance of the object itself.
//
// See <Usage> section below for information on using uvm_component_registry.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 8.2.4.1
class uvm_object_registry #(type T=uvm_object, string Tname="<unknown>")
                                        extends uvm_object_wrapper;
  typedef uvm_object_registry #(T,Tname) this_type;
  typedef uvm_registry_common#( this_type, uvm_registry_object_creator, T ) common_type;

  // Function -- NODOCS -- create_object
  //
  // Creates an object of type ~T~ and returns it as a handle to a
  // <uvm_object>. This is an override of the method in <uvm_object_wrapper>.
  // It is called by the factory after determining the type of object to create.
  // You should not call this method directly. Call <create> instead.

  // @uvm-ieee 1800.2-2017 auto 8.2.4.2.1
  virtual function uvm_object create_object(string name="");
    T obj;
    if (name=="") obj = new();
    else obj = new(name);
    return obj;
  endfunction

  static function string type_name();
     return Tname;
  endfunction : type_name

  // Function -- NODOCS -- get_type_name
  //
  // Returns the value given by the string parameter, ~Tname~. This method
  // overrides the method in <uvm_object_wrapper>.

  // @uvm-ieee 1800.2-2017 auto 8.2.4.2.2
  virtual function string get_type_name();
     common_type common = common_type::get();
     return common.get_type_name();
  endfunction

  //
  // Returns the singleton instance of this type. Type-based factory operation
  // depends on there being a single proxy instance for each registered type. 

  static function this_type get();
     static this_type m_inst;
     if (m_inst == null)
       m_inst = new();
    return m_inst;
  endfunction


  // Function -- NODOCS -- create
  //
  // Returns an instance of the object type, ~T~, represented by this proxy,
  // subject to any factory overrides based on the context provided by the
  // ~parent~'s full name. The ~contxt~ argument, if supplied, supersedes the
  // ~parent~'s context. The new instance will have the given leaf ~name~,
  // if provided.

  // @uvm-ieee 1800.2-2017 auto 8.2.4.2.4
  static function T create (string name="", uvm_component parent=null,
                            string contxt="");
    return common_type::create( name, parent, contxt );
  endfunction


  // Function -- NODOCS -- set_type_override
  //
  // Configures the factory to create an object of the type represented by
  // ~override_type~ whenever a request is made to create an object of the type
  // represented by this proxy, provided no instance override applies. The
  // original type, ~T~, is typically a super class of the override type. 

  // @uvm-ieee 1800.2-2017 auto 8.2.4.2.5
  static function void set_type_override (uvm_object_wrapper override_type,
                                          bit replace=1);
    common_type::set_type_override( override_type, replace );
  endfunction


  // Function -- NODOCS -- set_inst_override
  //
  // Configures the factory to create an object of the type represented by
  // ~override_type~ whenever a request is made to create an object of the type
  // represented by this proxy, with matching instance paths. The original
  // type, ~T~, is typically a super class of the override type.
  //
  // If ~parent~ is not specified, ~inst_path~ is interpreted as an absolute
  // instance path, which enables instance overrides to be set from outside
  // component classes. If ~parent~ is specified, ~inst_path~ is interpreted
  // as being relative to the ~parent~'s hierarchical instance path, i.e.
  // ~{parent.get_full_name(),".",inst_path}~ is the instance path that is
  // registered with the override. The ~inst_path~ may contain wildcards for
  // matching against multiple contexts.

  // @uvm-ieee 1800.2-2017 auto 8.2.4.2.6
  static function void set_inst_override(uvm_object_wrapper override_type,
                                         string inst_path,
                                         uvm_component parent=null);
    common_type::set_inst_override( override_type, inst_path, parent );
  endfunction

  // @uvm-ieee 1800.2-2017 auto 8.2.4.2.7
  virtual function void initialize();
     common_type common = common_type::get();
     common.initialize();
  endfunction
endclass

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_abstract_component_registry #(T,Tname)
//
// The uvm_abstract_component_registry serves as a lightweight proxy for a
// component of type ~T~ and type name ~Tname~, a string. The proxy enables
// efficient registration with the <uvm_factory>. Without it, registration would
// require an instance of the component itself.
//
// See <Usage> section below for information on using
// uvm_abstract_component_registry.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 8.2.5.1.1
class uvm_abstract_component_registry #(type T=uvm_component, string Tname="<unknown>")
                                           extends uvm_object_wrapper;
  typedef uvm_abstract_component_registry #(T,Tname) this_type;
  typedef uvm_registry_common#( this_type, uvm_registry_component_creator, T ) common_type;

  // Function -- NODOCS -- create_component
  //
  // Creates a component of type T having the provided ~name~ and ~parent~.
  // This is an override of the method in <uvm_object_wrapper>. It is
  // called by the factory after determining the type of object to create.
  // You should not call this method directly. Call <create> instead.

  // @uvm-ieee 1800.2-2017 auto 8.2.5.1.2
  virtual function uvm_component create_component (string name,
                                                   uvm_component parent);
    `uvm_error(
      "UVM/ABST_RGTRY/CREATE_ABSTRACT_CMPNT",
      $sformatf( "Cannot create an instance of abstract class %s (with name %s and parent %s). Check for missing factory overrides for %s.", this.get_type_name(), name, parent.get_full_name(), this.get_type_name() )
    )
    return null;
  endfunction

  static function string type_name();
     return Tname;
  endfunction : type_name

  // Function -- NODOCS -- get_type_name
  //
  // Returns the value given by the string parameter, ~Tname~. This method
  // overrides the method in <uvm_object_wrapper>.

  virtual function string get_type_name();
     common_type common = common_type::get();
     return common.get_type_name();
  endfunction


  // Function -- NODOCS -- get
  //
  // Returns the singleton instance of this type. Type-based factory operation
  // depends on there being a single proxy instance for each registered type. 

  static function this_type get();
    static this_type m_inst;
     if (m_inst == null)
       m_inst = new();
    return m_inst;
  endfunction


  // Function -- NODOCS -- create
  //
  // Returns an instance of the component type, ~T~, represented by this proxy,
  // subject to any factory overrides based on the context provided by the
  // ~parent~'s full name. The ~contxt~ argument, if supplied, supersedes the
  // ~parent~'s context. The new instance will have the given leaf ~name~
  // and ~parent~.

  static function T create(string name, uvm_component parent, string contxt="");
    return common_type::create( name, parent, contxt );
  endfunction


  // Function -- NODOCS -- set_type_override
  //
  // Configures the factory to create an object of the type represented by
  // ~override_type~ whenever a request is made to create an object of the type,
  // ~T~, represented by this proxy, provided no instance override applies. The
  // original type, ~T~, is typically a super class of the override type. 

  static function void set_type_override (uvm_object_wrapper override_type,
                                          bit replace=1);
    common_type::set_type_override( override_type, replace );
  endfunction


  // Function -- NODOCS -- set_inst_override
  //
  // Configures the factory to create a component of the type represented by
  // ~override_type~ whenever a request is made to create an object of the type,
  // ~T~, represented by this proxy,  with matching instance paths. The original
  // type, ~T~, is typically a super class of the override type.
  //
  // If ~parent~ is not specified, ~inst_path~ is interpreted as an absolute
  // instance path, which enables instance overrides to be set from outside
  // component classes. If ~parent~ is specified, ~inst_path~ is interpreted
  // as being relative to the ~parent~'s hierarchical instance path, i.e.
  // ~{parent.get_full_name(),".",inst_path}~ is the instance path that is
  // registered with the override. The ~inst_path~ may contain wildcards for
  // matching against multiple contexts.

  static function void set_inst_override(uvm_object_wrapper override_type,
                                         string inst_path,
                                         uvm_component parent=null);
    common_type::set_inst_override( override_type, inst_path, parent );
  endfunction

  virtual function void initialize();
     common_type common = common_type::get();
     common.initialize();
  endfunction
endclass


//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_abstract_object_registry #(T,Tname)
//
// The uvm_abstract_object_registry serves as a lightweight proxy for a
// <uvm_object> of type ~T~ and type name ~Tname~, a string. The proxy enables
// efficient registration with the <uvm_factory>. Without it, registration would
// require an instance of the object itself.
//
// See <Usage> section below for information on using uvm_object_registry.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 8.2.5.2.1
class uvm_abstract_object_registry #(type T=uvm_object, string Tname="<unknown>")
                                        extends uvm_object_wrapper;
  typedef uvm_abstract_object_registry #(T,Tname) this_type;
  typedef uvm_registry_common#( this_type, uvm_registry_object_creator, T ) common_type;

  // Function -- NODOCS -- create_object
  //
  // Creates an object of type ~T~ and returns it as a handle to a
  // <uvm_object>. This is an override of the method in <uvm_object_wrapper>.
  // It is called by the factory after determining the type of object to create.
  // You should not call this method directly. Call <create> instead.

  // @uvm-ieee 1800.2-2017 auto 8.2.5.2.2
  virtual function uvm_object create_object(string name="");
    `uvm_error(
      "UVM/ABST_RGTRY/CREATE_ABSTRACT_OBJ",
      $sformatf( "Cannot create an instance of abstract class %s (with name %s). Check for missing factory overrides for %s.", this.get_type_name(), name, this.get_type_name() )
    )
    return null;
  endfunction

  static function string type_name();
     return Tname;
  endfunction : type_name
      
  // Function -- NODOCS -- get_type_name
  //
  // Returns the value given by the string parameter, ~Tname~. This method
  // overrides the method in <uvm_object_wrapper>.

  virtual function string get_type_name();
     common_type common = common_type::get();
     return common.get_type_name();
  endfunction

  // Function -- NODOCS -- get
  //
  // Returns the singleton instance of this type. Type-based factory operation
  // depends on there being a single proxy instance for each registered type. 

  static function this_type get();
    static this_type m_inst;
     if (m_inst == null)
       m_inst = new();
    return m_inst;
  endfunction


  // Function -- NODOCS -- create
  //
  // Returns an instance of the object type, ~T~, represented by this proxy,
  // subject to any factory overrides based on the context provided by the
  // ~parent~'s full name. The ~contxt~ argument, if supplied, supersedes the
  // ~parent~'s context. The new instance will have the given leaf ~name~,
  // if provided.

  static function T create (string name="", uvm_component parent=null,
                            string contxt="");
    return common_type::create( name, parent, contxt );
  endfunction


  // Function -- NODOCS -- set_type_override
  //
  // Configures the factory to create an object of the type represented by
  // ~override_type~ whenever a request is made to create an object of the type
  // represented by this proxy, provided no instance override applies. The
  // original type, ~T~, is typically a super class of the override type. 

  static function void set_type_override (uvm_object_wrapper override_type,
                                          bit replace=1);
    common_type::set_type_override( override_type, replace );
  endfunction


  // Function -- NODOCS -- set_inst_override
  //
  // Configures the factory to create an object of the type represented by
  // ~override_type~ whenever a request is made to create an object of the type
  // represented by this proxy, with matching instance paths. The original
  // type, ~T~, is typically a super class of the override type.
  //
  // If ~parent~ is not specified, ~inst_path~ is interpreted as an absolute
  // instance path, which enables instance overrides to be set from outside
  // component classes. If ~parent~ is specified, ~inst_path~ is interpreted
  // as being relative to the ~parent~'s hierarchical instance path, i.e.
  // ~{parent.get_full_name(),".",inst_path}~ is the instance path that is
  // registered with the override. The ~inst_path~ may contain wildcards for
  // matching against multiple contexts.

  static function void set_inst_override(uvm_object_wrapper override_type,
                                         string inst_path,
                                         uvm_component parent=null);
    common_type::set_inst_override( override_type, inst_path, parent );
  endfunction
  
  virtual function void initialize();
     common_type common = common_type::get();
     common.initialize();
  endfunction
endclass


//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_registry_common #(T,Tname)
//
// This is a helper class which implements the functioanlity that is identical
// between uvm_component_registry and uvm_abstract_component_registry.
//
//------------------------------------------------------------------------------

class uvm_registry_common #( type Tregistry=int, type Tcreator=int, type Tcreated=int );

  typedef uvm_registry_common#(Tregistry,Tcreator,Tcreated) this_type;

  virtual function string get_type_name();
    return Tregistry::type_name;
  endfunction

  static function this_type get();
     static this_type m_inst;
     if (m_inst == null)
       m_inst = new();
     return m_inst;
  endfunction : get
   
  static function Tcreated create(string name, uvm_component parent, string contxt);
    uvm_object obj;
    if (contxt == "" && parent != null)
      contxt = parent.get_full_name();
    obj = Tcreator::create_by_type( Tregistry::get(), contxt, name, parent );
    if (!$cast(create, obj)) begin
      string msg;
      msg = {"Factory did not return a ", Tcreator::base_type_name(), " of type '",Tregistry::type_name,
        "'. A component of type '",obj == null ? "null" : obj.get_type_name(),
        "' was returned instead. Name=",name," Parent=",
        parent==null?"null":parent.get_type_name()," contxt=",contxt};
      uvm_report_fatal("FCTTYP", msg, UVM_NONE);
    end
  endfunction

  static function void set_type_override (uvm_object_wrapper override_type,
                                          bit replace);
    uvm_factory factory=uvm_factory::get();     

    factory.set_type_override_by_type(Tregistry::get(),override_type,replace);
  endfunction

  static function void set_inst_override(uvm_object_wrapper override_type,
                                         string inst_path,
                                         uvm_component parent);
    string full_inst_path;
    uvm_factory factory=uvm_factory::get();
    	
    if (parent != null) begin
      if (inst_path == "")
        inst_path = parent.get_full_name();
      else
        inst_path = {parent.get_full_name(),".",inst_path};
    end
    factory.set_inst_override_by_type(Tregistry::get(),override_type,inst_path);
  endfunction
  
  static function bit __deferred_init();
     // If the core is uninitialized, we defer initialization
     if (uvm_pkg::get_core_state() == UVM_CORE_UNINITIALIZED) begin
	Tregistry rgtry = Tregistry::get();
	uvm_pkg::uvm_deferred_init.push_back(rgtry);
     end
     // If the core is initialized, then we're static racing,
     // initialize immediately
     else begin
	this_type common;
	common = get();
	common.initialize();
     end
     return 1;
  endfunction
  local static bit m__initialized=__deferred_init();
 
  virtual function void initialize();                                                   
     uvm_factory factory =uvm_factory::get();
     factory.register(Tregistry::get());
  endfunction
endclass


//------------------------------------------------------------------------------
// 
// The next two classes are helper classes passed as type parameters to
// uvm_registry_common.  They abstract away the function calls
// uvm_factory::create_component_by_type  and
// uvm_factory::create_object_by_type.  Choosing between the two is handled at
// compile time..
//
//------------------------------------------------------------------------------

virtual class uvm_registry_component_creator;

  static function uvm_component create_by_type(
    uvm_object_wrapper obj_wrpr,
    string contxt,
    string name,
    uvm_component parent
  );
    uvm_coreservice_t cs = uvm_coreservice_t::get();                                                     
    uvm_factory factory = cs.get_factory();
    return factory.create_component_by_type( obj_wrpr, contxt, name, parent );
  endfunction

  static function string base_type_name();  return "component"; endfunction
endclass

virtual class uvm_registry_object_creator;

  static function uvm_object create_by_type(
    uvm_object_wrapper obj_wrpr,
    string contxt,
    string name,
    uvm_object unused
  );
    uvm_coreservice_t cs = uvm_coreservice_t::get();                                                     
    uvm_factory factory = cs.get_factory();
    unused = unused;  // ... to keep linters happy.
    return factory.create_object_by_type( obj_wrpr, contxt, name );
  endfunction

  static function string base_type_name();  return "object"; endfunction
endclass



// Group -- NODOCS -- Usage
//
// This section describes usage for the uvm_*_registry classes.
//
// The wrapper classes are used to register lightweight proxies of objects and
// components.
//
// To register a particular component type, you need only typedef a
// specialization of its proxy class, which is typically done inside the class.
//
// For example, to register a UVM component of type ~mycomp~
//
//|  class mycomp extends uvm_component;
//|    typedef uvm_component_registry #(mycomp,"mycomp") type_id;
//|  endclass
//
// However, because of differences between simulators, it is necessary to use a
// macro to ensure vendor interoperability with factory registration. To
// register a UVM component of type ~mycomp~ in a vendor-independent way, you
// would write instead:
//
//|  class mycomp extends uvm_component;
//|    `uvm_component_utils(mycomp)
//|    ...
//|  endclass
//
// The <`uvm_component_utils> macro is for non-parameterized classes. In this
// example, the typedef underlying the macro specifies the ~Tname~
// parameter as "mycomp", and ~mycomp~'s get_type_name() is defined to return 
// the same. With ~Tname~ defined, you can use the factory's name-based methods to
// set overrides and create objects and components of non-parameterized types.
//
// For parameterized types, the type name changes with each specialization, so
// you cannot specify a ~Tname~ inside a parameterized class and get the behavior
// you want; the same type name string would be registered for all
// specializations of the class! (The factory would produce warnings for each
// specialization beyond the first.) To avoid the warnings and simulator
// interoperability issues with parameterized classes, you must register
// parameterized classes with a different macro.
//
// For example, to register a UVM component of type driver #(T), you
// would write:
//
//|  class driver #(type T=int) extends uvm_component;
//|    `uvm_component_param_utils(driver #(T))
//|    ...
//|  endclass
//
// The <`uvm_component_param_utils> and <`uvm_object_param_utils> macros are used
// to register parameterized classes with the factory. Unlike the non-param
// versions, these macros do not specify the ~Tname~ parameter in the underlying
// uvm_component_registry typedef, and they do not define the get_type_name
// method for the user class. Consequently, you will not be able to use the
// factory's name-based methods for parameterized classes.
//
// The primary purpose for adding the factory's type-based methods was to
// accommodate registration of parameterized types and eliminate the many sources
// of errors associated with string-based factory usage. Thus, use of name-based
// lookup in <uvm_factory> is no longer recommended.

`endif // UVM_REGISTRY_SVH
