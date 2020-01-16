//
//------------------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2015 Analog Devices, Inc.
// Copyright 2014 Semifore
// Copyright 2017 Intel Corporation
// Copyright 2011 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2013 Verilab
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


typedef class uvm_object;
typedef class uvm_component;
typedef class uvm_object_wrapper;
typedef class uvm_factory_override;

//Instance overrides by requested type lookup
class uvm_factory_queue_class;
  uvm_factory_override queue[$];
endclass

//------------------------------------------------------------------------------
// Title -- NODOCS -- UVM Factory
//
// This page covers the classes that define the UVM factory facility.
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_factory
//
//------------------------------------------------------------------------------
//
// As the name implies, uvm_factory is used to manufacture (create) UVM objects
// and components. Object and component types are registered
// with the factory using lightweight proxies to the actual objects and
// components being created. The <uvm_object_registry #(T,Tname)> and
// <uvm_component_registry #(T,Tname)> class are used to proxy <uvm_objects>
// and <uvm_components>.
//
// The factory provides both name-based and type-based interfaces.
//
// type-based - The type-based interface is far less prone to errors in usage.
//   When errors do occur, they are caught at compile-time.
//
// name-based - The name-based interface is dominated 
//   by string arguments that can be misspelled and provided in the wrong order.
//   Errors in name-based requests might only be caught at the time of the call,
//   if at all. Further, the name-based interface is not portable across
//   simulators when used with parameterized classes.
//
//
// The ~uvm_factory~ is an abstract class which declares many of its methods
// as ~pure virtual~.  The UVM uses the <uvm_default_factory> class
// as its default factory implementation.
//   
// See <uvm_default_factory::Usage> section for details on configuring and using the factory.
//
  
// @uvm-ieee 1800.2-2017 auto 8.3.1.1
virtual class uvm_factory;

  // Group -- NODOCS -- Retrieving the factory

 
         
  // @uvm-ieee 1800.2-2017 auto 8.3.1.2.1
  static function uvm_factory get();
	  	uvm_coreservice_t s;
	  	s = uvm_coreservice_t::get();
	  	return s.get_factory();
  endfunction	
  
  // @uvm-ieee 1800.2-2017 auto 8.3.1.2.2
  static function void set(uvm_factory f);
	  	uvm_coreservice_t s;
	  	s = uvm_coreservice_t::get();
	  	s.set_factory(f);
  endfunction	

  // Group -- NODOCS -- Registering Types

  // Function -- NODOCS -- register
  //
  // Registers the given proxy object, ~obj~, with the factory. The proxy object
  // is a lightweight substitute for the component or object it represents. When
  // the factory needs to create an object of a given type, it calls the proxy's
  // create_object or create_component method to do so.
  //
  // When doing name-based operations, the factory calls the proxy's
  // ~get_type_name~ method to match against the ~requested_type_name~ argument in
  // subsequent calls to <create_component_by_name> and <create_object_by_name>.
  // If the proxy object's ~get_type_name~ method returns the empty string,
  // name-based lookup is effectively disabled.

  // @uvm-ieee 1800.2-2017 auto 8.3.1.3
  pure virtual function void register (uvm_object_wrapper obj);


  // Group -- NODOCS -- Type & Instance Overrides

  // Function -- NODOCS -- set_inst_override_by_type

  pure virtual function
      // @uvm-ieee 1800.2-2017 auto 8.3.1.4.1
      void set_inst_override_by_type (uvm_object_wrapper original_type,
                                      uvm_object_wrapper override_type,
                                      string full_inst_path);

  // Function -- NODOCS -- set_inst_override_by_name
  //
  // Configures the factory to create an object of the override's type whenever
  // a request is made to create an object of the original type using a context
  // that matches ~full_inst_path~. The original type is typically a super class
  // of the override type.
  //
  // When overriding by type, the ~original_type~ and ~override_type~ are
  // handles to the types' proxy objects. Preregistration is not required.
  //
  // When overriding by name, the ~original_type_name~ typically refers to a
  // preregistered type in the factory. It may, however, be any arbitrary
  // string. Future calls to any of the ~create_*~ methods with the same string
  // and matching instance path will produce the type represented by
  // ~override_type_name~, which must be preregistered with the factory.
  //
  // The ~full_inst_path~ is matched against the concatenation of
  // {~parent_inst_path~, ".", ~name~} provided in future create requests. The
  // ~full_inst_path~ may include wildcards (* and ?) such that a single
  // instance override can be applied in multiple contexts. A ~full_inst_path~
  // of "*" is effectively a type override, as it will match all contexts.
  //
  // When the factory processes instance overrides, the instance queue is
  // processed in order of override registrations, and the first override
  // match prevails. Thus, more specific overrides should be registered
  // first, followed by more general overrides.

  pure virtual function
      // @uvm-ieee 1800.2-2017 auto 8.3.1.4.1
      void set_inst_override_by_name (string original_type_name,
                                      string override_type_name,
                                      string full_inst_path);


  // Function -- NODOCS -- set_type_override_by_type

  pure virtual function
      // @uvm-ieee 1800.2-2017 auto 8.3.1.4.2
      void set_type_override_by_type (uvm_object_wrapper original_type,
                                      uvm_object_wrapper override_type,
                                      bit replace=1);

  // Function -- NODOCS -- set_type_override_by_name
  //
  // Configures the factory to create an object of the override's type whenever
  // a request is made to create an object of the original type, provided no
  // instance override applies. The original type is typically a super class of
  // the override type.
  //
  // When overriding by type, the ~original_type~ and ~override_type~ are
  // handles to the types' proxy objects. Preregistration is not required.
  //
  // When overriding by name, the ~original_type_name~ typically refers to a
  // preregistered type in the factory. It may, however, be any arbitrary
  // string. Future calls to any of the ~create_*~ methods with the same string
  // and matching instance path will produce the type represented by
  // ~override_type_name~, which must be preregistered with the factory.
  //
  // When ~replace~ is 1, a previous override on ~original_type_name~ is
  // replaced, otherwise a previous override, if any, remains intact.

  pure virtual function
      // @uvm-ieee 1800.2-2017 auto 8.3.1.4.2
      void set_type_override_by_name (string original_type_name,
                                      string override_type_name,
                                      bit replace=1);


  // Group -- NODOCS -- Creation

  // Function -- NODOCS -- create_object_by_type

  pure virtual function
      // @uvm-ieee 1800.2-2017 auto 8.3.1.5
      uvm_object    create_object_by_type    (uvm_object_wrapper requested_type,  
                                              string parent_inst_path="",
                                              string name=""); 

  // Function -- NODOCS -- create_component_by_type

  pure virtual function
      // @uvm-ieee 1800.2-2017 auto 8.3.1.5
      uvm_component create_component_by_type (uvm_object_wrapper requested_type,  
                                              string parent_inst_path="",
                                              string name, 
                                              uvm_component parent);

  // Function -- NODOCS -- create_object_by_name

  pure virtual function
      // @uvm-ieee 1800.2-2017 auto 8.3.1.5
      uvm_object    create_object_by_name    (string requested_type_name,  
                                              string parent_inst_path="",
                                              string name=""); 

   // Function -- NODOCS -- is_type_name_registered
    
     pure virtual
        // @uvm-ieee 1800.2-2017 auto 8.3.1.7.3
        function bit is_type_name_registered  (string type_name);

 
   // Function -- NODOCS -- is_type_registered 

     pure virtual 
        // @uvm-ieee 1800.2-2017 auto 8.3.1.7.4
        function bit is_type_registered     (uvm_object_wrapper obj); 

    
  //
  // Creates and returns a component or object of the requested type, which may
  // be specified by type or by name. A requested component must be derived
  // from the <uvm_component> base class, and a requested object must be derived
  // from the <uvm_object> base class.
  //
  // When requesting by type, the ~requested_type~ is a handle to the type's
  // proxy object. Preregistration is not required.
  //
  // When requesting by name, the ~request_type_name~ is a string representing
  // the requested type, which must have been registered with the factory with
  // that name prior to the request. If the factory does not recognize the
  // ~requested_type_name~, an error is produced and a ~null~ handle returned.
  //
  // If the optional ~parent_inst_path~ is provided, then the concatenation,
  // {~parent_inst_path~, ".",~name~}, forms an instance path (context) that
  // is used to search for an instance override. The ~parent_inst_path~ is
  // typically obtained by calling the <uvm_component::get_full_name> on the
  // parent.
  //
  // If no instance override is found, the factory then searches for a type
  // override.
  //
  // Once the final override is found, an instance of that component or object
  // is returned in place of the requested type. New components will have the
  // given ~name~ and ~parent~. New objects will have the given ~name~, if
  // provided.
  //
  // Override searches are recursively applied, with instance overrides taking
  // precedence over type overrides. If ~foo~ overrides ~bar~, and ~xyz~
  // overrides ~foo~, then a request for ~bar~ will produce ~xyz~. Recursive
  // loops will result in an error, in which case the type returned will be
  // that which formed the loop. Using the previous example, if ~bar~
  // overrides ~xyz~, then ~bar~ is returned after the error is issued.

  pure virtual function
      // @uvm-ieee 1800.2-2017 auto 8.3.1.5
      uvm_component create_component_by_name (string requested_type_name,  
                                              string parent_inst_path="",
                                              string name, 
                                              uvm_component parent);

  // Group -- NODOCS -- Name Aliases
  
  // Function -- NODOCS -- set_type_alias
  pure virtual function
      // @uvm-ieee 1800.2-2017 auto 8.3.1.6.1
      void set_type_alias(string alias_type_name, 
                          uvm_object_wrapper original_type); 
  
  //Intended to allow overrides by type to use the alias_type_name as an additional name to refer to
  //original_type  
  
  // Function -- NODOCS -- set_inst_alias
  pure virtual function
      // @uvm-ieee 1800.2-2017 auto 8.3.1.6.2
      void set_inst_alias(string alias_type_name,
                          uvm_object_wrapper original_type, string full_inst_path);

  //Intended to allow overrides by name to use the alias_type_name as an additional name to refer to
  //original_type in the context referred to by full_inst_path.  


  // Group -- NODOCS -- Debug

  // Function -- NODOCS -- debug_create_by_type

  pure virtual function
      void debug_create_by_type (uvm_object_wrapper requested_type,
                                 string parent_inst_path="",
                                 string name="");

  // Function -- NODOCS -- debug_create_by_name
  //
  // These methods perform the same search algorithm as the ~create_*~ methods,
  // but they do not create new objects. Instead, they provide detailed
  // information about what type of object it would return, listing each
  // override that was applied to arrive at the result. Interpretation of the
  // arguments are exactly as with the ~create_*~ methods.

  pure virtual function
      void debug_create_by_name (string requested_type_name,
                                 string parent_inst_path="",
                                 string name="");

                   
  // Function -- NODOCS -- find_override_by_type

  pure virtual function
      // @uvm-ieee 1800.2-2017 auto 8.3.1.7.1
      uvm_object_wrapper find_override_by_type (uvm_object_wrapper requested_type,
                                                string full_inst_path);

  // Function -- NODOCS -- find_override_by_name
  //
  // These methods return the proxy to the object that would be created given
  // the arguments. The ~full_inst_path~ is typically derived from the parent's
  // instance path and the leaf name of the object to be created, i.e.
  // { parent.get_full_name(), ".", name }.

  pure virtual function
      // @uvm-ieee 1800.2-2017 auto 8.3.1.7.1
      uvm_object_wrapper find_override_by_name (string requested_type_name,
                                                string full_inst_path);

  // Function -- NODOCS -- find_wrapper_by_name
  //
  // This method returns the <uvm_object_wrapper> associated with a given
  // ~type_name~.  
  pure virtual 
    // @uvm-ieee 1800.2-2017 auto 8.3.1.7.2
    function uvm_object_wrapper find_wrapper_by_name            (string type_name);

  // Function -- NODOCS -- print
  //
  // Prints the state of the uvm_factory, including registered types, instance
  // overrides, and type overrides.
  //
  // When ~all_types~ is 0, only type and instance overrides are displayed. When
  // ~all_types~ is 1 (default), all registered user-defined types are printed as
  // well, provided they have names associated with them. When ~all_types~ is 2,
  // the UVM types (prefixed with uvm_) are included in the list of registered
  // types.

  // @uvm-ieee 1800.2-2017 auto 8.3.1.7.5
  pure  virtual function void print (int all_types=1);
endclass 
    
//------------------------------------------------------------------------------
//
// CLASS: uvm_default_factory
//
//------------------------------------------------------------------------------
//
// Default implementation of the UVM factory.  The library implements the
// following public API beyond what is documented in IEEE 1800.2.
   
// @uvm-ieee 1800.2-2017 auto 8.3.3
class uvm_default_factory extends uvm_factory;

  // Group --NODOCS-- Registering Types

  // Function --NODOCS-- register
  //
  // Registers the given proxy object, ~obj~, with the factory.
   
  extern virtual function void register (uvm_object_wrapper obj);


  // Group --NODOCS-- Type & Instance Overrides

  // Function --NODOCS-- set_inst_override_by_type

  extern virtual function
      void set_inst_override_by_type (uvm_object_wrapper original_type,
                                      uvm_object_wrapper override_type,
                                      string full_inst_path);

  // Function --NODOCS-- set_inst_override_by_name
  //
  // Configures the factory to create an object of the override's type whenever
  // a request is made to create an object of the original type using a context
  // that matches ~full_inst_path~. 
  // 
  // ~original_type_name~ may be the factory-registered type name or an aliased name
  // specified with <set_inst_alias> in the context of ~full_inst_path~.
  extern virtual function
      void set_inst_override_by_name (string original_type_name,
                                      string override_type_name,
                                      string full_inst_path);


  // Function --NODOCS-- set_type_override_by_type

  extern virtual function
      void set_type_override_by_type (uvm_object_wrapper original_type,
                                      uvm_object_wrapper override_type,
                                      bit replace=1);

  // Function --NODOCS-- set_type_override_by_name
  //
  // Configures the factory to create an object of the override's type whenever
  // a request is made to create an object of the original type, provided no
  // instance override applies.
  //
  // ~original_type_name~ may be the factory-registered type name or an aliased name
  // specified with <set_type_alias>.
   
  extern virtual function
      void set_type_override_by_name (string original_type_name,
                                      string override_type_name,
                                      bit replace=1);

  // Function: set_type_alias
  //
  // Intended to allow overrides by type to use the alias_type_name as an additional name to refer to
  // original_type 
  
  extern virtual function
      void set_type_alias(string alias_type_name, 
                          uvm_object_wrapper original_type); 
  
  // Function: set_inst_alias
  //
  // Intended to allow overrides by name to use the alias_type_name as an additional name to refer to
  // original_type in the context referred to by full_inst_path.  

  extern virtual function
      void set_inst_alias(string alias_type_name,
                          uvm_object_wrapper original_type, string full_inst_path);



  // Group --NODOCS-- Creation

  // Function --NODOCS-- create_object_by_type

  extern virtual function
      uvm_object    create_object_by_type    (uvm_object_wrapper requested_type,  
                                              string parent_inst_path="",
                                              string name=""); 

  // Function --NODOCS-- create_component_by_type

  extern virtual function
      uvm_component create_component_by_type (uvm_object_wrapper requested_type,  
                                              string parent_inst_path="",
                                              string name, 
                                              uvm_component parent);

  // Function --NODOCS-- create_object_by_name

  extern virtual function
      uvm_object    create_object_by_name    (string requested_type_name,  
                                              string parent_inst_path="",
                                              string name=""); 

  // Function --NODOCS-- create_component_by_name
  //
  // Creates and returns a component or object of the requested type, which may
  // be specified by type or by name.
   
  extern virtual function
      uvm_component create_component_by_name (string requested_type_name,  
                                              string parent_inst_path="",
                                              string name, 
                                              uvm_component parent);

  // Function --NODOCS-- is_type_name_registered
  //
  // silently check type with a given name was registered in the factory or not
 
  extern virtual
      function bit is_type_name_registered    (string type_name);

   
  // Function --NODOCS-- is_type_registered
  //
  // silently check type is registered in the factory or not
 
  extern virtual
      function bit is_type_registered    (uvm_object_wrapper obj);


  // Function: debug_create_by_type

  extern virtual function
      void debug_create_by_type (uvm_object_wrapper requested_type,
                                 string parent_inst_path="",
                                 string name="");

  // Function: debug_create_by_name
  //
  // These methods perform the same search algorithm as the ~create_*~ methods,
  // but they do not create new objects. 
  extern virtual function
      void debug_create_by_name (string requested_type_name,
                                 string parent_inst_path="",
                                 string name="");

                   
  // Function --NODOCS-- find_override_by_type

  extern virtual function
      uvm_object_wrapper find_override_by_type (uvm_object_wrapper requested_type,
                                                string full_inst_path);

  // Function --NODOCS-- find_override_by_name
  //
  // These methods return the proxy to the object that would be created given
  // the arguments.
   
  extern virtual function
      uvm_object_wrapper find_override_by_name (string requested_type_name,
                                                string full_inst_path);

  extern virtual 
    function uvm_object_wrapper find_wrapper_by_name            (string type_name);

  // Function --NODOCS-- print
  //
  // Prints the state of the uvm_factory, including registered types, instance
  // overrides, and type overrides.
  //
  extern  virtual function void print (int all_types=1);


  //----------------------------------------------------------------------------
  // PRIVATE MEMBERS
  
  extern protected
      function void  m_debug_create (string requested_type_name,
                                     uvm_object_wrapper requested_type,
                                     string parent_inst_path,
                                     string name);
  
  extern protected
      function void  m_debug_display(string requested_type_name,
                                     uvm_object_wrapper result,
                                     string full_inst_path);
                        
  typedef struct  {
    string orig_type_name;
    string alias_type_name;
    string full_inst_path;
  } m_inst_typename_alias_t;
    
  protected bit                  m_types[uvm_object_wrapper];
  protected bit                  m_lookup_strs[string];
  protected uvm_object_wrapper   m_type_names[string];
  protected string               m_type_name_alias[string];
  protected m_inst_typename_alias_t  m_type_name_inst_alias[$];

  protected uvm_factory_override m_type_overrides[$];

  protected uvm_factory_queue_class m_inst_override_queues[uvm_object_wrapper];
  protected uvm_factory_queue_class m_inst_override_name_queues[string];
  protected uvm_factory_override    m_wildcard_inst_overrides[$];

  local uvm_factory_override     m_override_info[$];
  local static bit m_debug_pass;

  extern function bit m_has_wildcard(string nm);

  extern function bit check_inst_override_exists
                                      (uvm_object_wrapper original_type,
                                       uvm_object_wrapper override_type,
                                       string full_inst_path);

endclass


//------------------------------------------------------------------------------
//
// Group -- NODOCS -- Usage
//
// Using the factory involves three basic operations
//
// 1 - Registering objects and components types with the factory
// 2 - Designing components to use the factory to create objects or components
// 3 - Configuring the factory with type and instance overrides, both within and
//     outside components
//
// We'll briefly cover each of these steps here. More reference information can
// be found at <Utility Macros>, <uvm_component_registry #(T,Tname)>,
// <uvm_object_registry #(T,Tname)>, <uvm_component>.
//
// 1 -- Registering objects and component types with the factory:
//
// When defining <uvm_object> and <uvm_component>-based classes, simply invoke
// the appropriate macro. Use of macros are required to ensure portability
// across different vendors' simulators.
//
// Objects that are not parameterized are declared as
//
//|  class packet extends uvm_object;
//|    `uvm_object_utils(packet)
//|  endclass
//|
//|  class packetD extends packet;
//|    `uvm_object_utils(packetD)
//|  endclass
//
// Objects that are parameterized are declared as
//
//|  class packet #(type T=int, int WIDTH=32) extends uvm_object;
//|    `uvm_object_param_utils(packet #(T,WIDTH))
//|   endclass
//
// Components that are not parameterized are declared as
//
//|  class comp extends uvm_component;
//|    `uvm_component_utils(comp)
//|  endclass
//
// Components that are parameterized are declared as
//
//|  class comp #(type T=int, int WIDTH=32) extends uvm_component;
//|    `uvm_component_param_utils(comp #(T,WIDTH))
//|  endclass
//
// The `uvm_*_utils macros for simple, non-parameterized classes will register
// the type with the factory and define the get_type, get_type_name, and create
// virtual methods inherited from <uvm_object>. It will also define a static
// type_name variable in the class, which will allow you to determine the type
// without having to allocate an instance. 
//
// The `uvm_*_param_utils macros for parameterized classes differ from
// `uvm_*_utils classes in the following ways:
//
// - The ~get_type_name~ method and static type_name variable are not defined. You
//   will need to implement these manually.
//
// - A type name is not associated with the type when registering with the
//   factory, so the factory's *_by_name operations will not work with
//   parameterized classes.
//
// - The factory's <print>, <debug_create_by_type>, and <debug_create_by_name>
//   methods, which depend on type names to convey information, will list
//   parameterized types as '<unknown>'.
//
// It is worth noting that environments that exclusively use the type-based
// factory methods (*_by_type) do not require type registration. The factory's
// type-based methods will register the types involved "on the fly," when first
// used. However, registering with the `uvm_*_utils macros enables name-based
// factory usage and implements some useful utility functions.
//
//
// 2 -- Designing components that defer creation to the factory:
//
// Having registered your objects and components with the factory, you can now
// make requests for new objects and components via the factory. Using the factory
// instead of allocating them directly (via new) allows different objects to be
// substituted for the original without modifying the requesting class. The
// following code defines a driver class that is parameterized.
//
//|  class driverB #(type T=uvm_object) extends uvm_driver;
//|
//|    // parameterized classes must use the _param_utils version
//|    `uvm_component_param_utils(driverB #(T))
//|
//|    // our packet type; this can be overridden via the factory
//|    T pkt;
//|
//|    // standard component constructor
//|    function new(string name, uvm_component parent=null);
//|      super.new(name,parent);
//|    endfunction
//|
//|    // get_type_name not implemented by macro for parameterized classes
//|    static function string type_name();
//|      return {"driverB #(",T::type_name(),")"};
//|    endfunction : type_name
//|    virtual function string get_type_name();
//|      return type_name();
//|    endfunction
//|
//|    // using the factory allows pkt overrides from outside the class
//|    virtual function void build_phase(uvm_phase phase);
//|      pkt = packet::type_id::create("pkt",this);
//|    endfunction
//|
//|    // print the packet so we can confirm its type when printing
//|    virtual function void do_print(uvm_printer printer);
//|      printer.print_object("pkt",pkt);
//|    endfunction
//|
//|  endclass
//
// For purposes of illustrating type and instance overrides, we define two
// subtypes of the ~driverB~ class. The subtypes are also parameterized, so
// we must again provide an implementation for <uvm_object::get_type_name>,
// which we recommend writing in terms of a static string constant.
//
//|  class driverD1 #(type T=uvm_object) extends driverB #(T);
//|
//|    `uvm_component_param_utils(driverD1 #(T))
//|
//|    function new(string name, uvm_component parent=null);
//|      super.new(name,parent);
//|    endfunction
//|
//|    static function string type_name();
//|      return {"driverD1 #(",T::type_name,")"};
//|    endfunction : type_name
//|    virtual function string get_type_name();
//|      return type_name();
//|    endfunction
//|
//|  endclass
//|
//|  class driverD2 #(type T=uvm_object) extends driverB #(T);
//|
//|    `uvm_component_param_utils(driverD2 #(T))
//|
//|    function new(string name, uvm_component parent=null);
//|      super.new(name,parent);
//|    endfunction
//|
//|    static function string type_name();
//|      return {"driverD2 #(",T::type_name,")"};
//|    endfunction : type_name
//|    virtual function string get_type_name();
//|      return type_name();
//|    endfunction
//|
//|  endclass
//|
//|  // typedef some specializations for convenience
//|  typedef driverB  #(packet) B_driver;   // the base driver
//|  typedef driverD1 #(packet) D1_driver;  // a derived driver
//|  typedef driverD2 #(packet) D2_driver;  // another derived driver
//
// Next, we'll define a agent component, which requires a utils macro for
// non-parameterized types. Before creating the drivers using the factory, we
// override ~driver0~'s packet type to be ~packetD~.
//
//|  class agent extends uvm_agent;
//|
//|    `uvm_component_utils(agent)
//|    ...
//|    B_driver driver0;
//|    B_driver driver1;
//|
//|    function new(string name, uvm_component parent=null);
//|      super.new(name,parent);
//|    endfunction
//|
//|    virtual function void build_phase(uvm_phase phase);
//|
//|      // override the packet type for driver0 and below
//|      packet::type_id::set_inst_override(packetD::get_type(),"driver0.*");
//|
//|      // create using the factory; actual driver types may be different
//|      driver0 = B_driver::type_id::create("driver0",this);
//|      driver1 = B_driver::type_id::create("driver1",this);
//|
//|    endfunction
//|
//|  endclass
//
// Finally we define an environment class, also not parameterized. Its ~build_phase~
// method shows three methods for setting an instance override on a grandchild
// component with relative path name, ~agent1.driver1~, all equivalent.
//
//|  class env extends uvm_env;
//|
//|    `uvm_component_utils(env)
//|
//|    agent agent0;
//|    agent agent1;
//|
//|    function new(string name, uvm_component parent=null);
//|      super.new(name,parent);
//|    endfunction
//|
//|    virtual function void build_phase(uvm_phase phase);
//|
//|      // three methods to set an instance override for agent1.driver1
//|      // - via component convenience method...
//|      set_inst_override_by_type("agent1.driver1",
//|                                B_driver::get_type(),
//|                                D2_driver::get_type());
//|
//|      // - via the component's proxy (same approach as create)...
//|      B_driver::type_id::set_inst_override(D2_driver::get_type(),
//|                                           "agent1.driver1",this);
//|
//|      // - via a direct call to a factory method...
//|      factory.set_inst_override_by_type(B_driver::get_type(),
//|                                        D2_driver::get_type(),
//|                                        {get_full_name(),".agent1.driver1"});
//|
//|      // create agents using the factory; actual agent types may be different
//|      agent0 = agent::type_id::create("agent0",this);
//|      agent1 = agent::type_id::create("agent1",this);
//|
//|    endfunction
//|
//|    // at end_of_elaboration, print topology and factory state to verify
//|    virtual function void end_of_elaboration_phase(uvm_phase phase);
//|      uvm_top.print_topology();
//|    endfunction
//|
//|    virtual task run_phase(uvm_phase phase);
//|      #100 global_stop_request();
//|    endfunction
//|
//|  endclass
//   
//
// 3 -- Configuring the factory with type and instance overrides:
//
// In the previous step, we demonstrated setting instance overrides and creating
// components using the factory within component classes. Here, we will
// demonstrate setting overrides from outside components, as when initializing
// the environment prior to running the test.
//
//|  module top;
//|
//|    env env0;
//|
//|    initial begin
//|
//|      // Being registered first, the following overrides take precedence
//|      // over any overrides made within env0's construction & build.
//|
//|      // Replace all base drivers with derived drivers...
//|      B_driver::type_id::set_type_override(D_driver::get_type());
//|
//|      // ...except for agent0.driver0, whose type remains a base driver.
//|      //     (Both methods below have the equivalent result.)
//|
//|      // - via the component's proxy (preferred)
//|      B_driver::type_id::set_inst_override(B_driver::get_type(),
//|                                           "env0.agent0.driver0");
//|
//|      // - via a direct call to a factory method
//|      factory.set_inst_override_by_type(B_driver::get_type(),
//|                                        B_driver::get_type(),
//|                                    {get_full_name(),"env0.agent0.driver0"});
//|
//|      // now, create the environment; our factory configuration will
//|      // govern what topology gets created
//|      env0 = new("env0");
//|
//|      // run the test (will execute build phase)
//|      run_test();
//|
//|    end
//|
//|  endmodule
//
// When the above example is run, the resulting topology (displayed via a call to
// <uvm_root::print_topology> in env's <uvm_component::end_of_elaboration_phase> method)
// is similar to the following:
//
//| # UVM_INFO @ 0 [RNTST] Running test ...
//| # UVM_INFO @ 0 [UVMTOP] UVM testbench topology:
//| # ----------------------------------------------------------------------
//| # Name                     Type                Size                Value
//| # ----------------------------------------------------------------------
//| # env0                     env                 -                  env0@2
//| #   agent0                 agent               -                agent0@4
//| #     driver0              driverB #(packet)   -               driver0@8
//| #       pkt                packet              -                  pkt@21
//| #     driver1              driverD #(packet)   -              driver1@14
//| #       pkt                packet              -                  pkt@23
//| #   agent1                 agent               -                agent1@6
//| #     driver0              driverD #(packet)   -              driver0@24
//| #       pkt                packet              -                  pkt@37
//| #     driver1              driverD2 #(packet)  -              driver1@30
//| #       pkt                packet              -                  pkt@39
//| # ----------------------------------------------------------------------
// 
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_object_wrapper
//
// The uvm_object_wrapper provides an abstract interface for creating object and
// component proxies. Instances of these lightweight proxies, representing every
// <uvm_object>-based and <uvm_component>-based object available in the test
// environment, are registered with the <uvm_factory>. When the factory is
// called upon to create an object or component, it finds and delegates the
// request to the appropriate proxy.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 8.3.2.1
virtual class uvm_object_wrapper;

  // Function -- NODOCS -- create_object
  //
  // Creates a new object with the optional ~name~.
  // An object proxy (e.g., <uvm_object_registry #(T,Tname)>) implements this
  // method to create an object of a specific type, T.

  // @uvm-ieee 1800.2-2017 auto 8.3.2.2.1
  virtual function uvm_object create_object (string name="");
    return null;
  endfunction


  // Function -- NODOCS -- create_component
  //
  // Creates a new component, passing to its constructor the given ~name~ and
  // ~parent~. A component proxy (e.g. <uvm_component_registry #(T,Tname)>)
  // implements this method to create a component of a specific type, T.

  // @uvm-ieee 1800.2-2017 auto 8.3.2.2.2
  virtual function uvm_component create_component (string name, 
                                                   uvm_component parent); 
    return null;
  endfunction


  // Function -- NODOCS -- get_type_name
  // 
  // Derived classes implement this method to return the type name of the object
  // created by <create_component> or <create_object>. The factory uses this
  // name when matching against the requested type in name-based lookups.

  // @uvm-ieee 1800.2-2017 auto 8.3.2.2.3
  pure virtual function string get_type_name();

  virtual function void initialize(); endfunction
endclass


//------------------------------------------------------------------------------
//
// CLASS- uvm_factory_override
//
// Internal class.
//------------------------------------------------------------------------------

class uvm_factory_override;
  string full_inst_path;
  string orig_type_name;
  string orig_type_name_alias;
  string ovrd_type_name;
  bit selected;
  int unsigned used;
  uvm_object_wrapper orig_type;
  uvm_object_wrapper ovrd_type;
  function new (string full_inst_path="",
                string orig_type_name="",
                uvm_object_wrapper orig_type=null,
                uvm_object_wrapper ovrd_type,
                string orig_type_name_alias="");
      
    if (ovrd_type == null) begin
      uvm_report_fatal ("NULLWR", "Attempting to register a null override object with the factory", UVM_NONE);
    end
    this.full_inst_path= full_inst_path;
    this.orig_type_name = orig_type == null ? orig_type_name : orig_type.get_type_name();
    this.orig_type      = orig_type;
    this.ovrd_type_name = ovrd_type.get_type_name();
    this.orig_type_name_alias = orig_type_name_alias;
    this.ovrd_type      = ovrd_type;
  endfunction
endclass


//-----------------------------------------------------------------------------
// IMPLEMENTATION
//-----------------------------------------------------------------------------

// register
// --------

function void uvm_default_factory::register (uvm_object_wrapper obj);

  if (obj == null) begin
    uvm_report_fatal ("NULLWR", "Attempting to register a null object with the factory", UVM_NONE);
  end
  if (obj.get_type_name() != "" && obj.get_type_name() != "<unknown>") begin
    if (m_type_names.exists(obj.get_type_name()))
      uvm_report_warning("TPRGED", {"Type name '",obj.get_type_name(),
        "' already registered with factory. No string-based lookup ",
        "support for multiple types with the same type name."}, UVM_NONE);
    else 
      m_type_names[obj.get_type_name()] = obj;
  end

  if (m_types.exists(obj)) begin
    if (obj.get_type_name() != "" && obj.get_type_name() != "<unknown>")
      uvm_report_warning("TPRGED", {"Object type '",obj.get_type_name(),
                         "' already registered with factory. "}, UVM_NONE);
  end
  else begin
    m_types[obj] = 1;
    // If a named override happens before the type is registered, need to copy
    // the override queue.
    // Note:Registration occurs via static initialization, which occurs ahead of
    // procedural (e.g. initial) blocks. There should not be any preexisting overrides.
    if(m_inst_override_name_queues.exists(obj.get_type_name())) begin
       m_inst_override_queues[obj] = new;
       m_inst_override_queues[obj].queue = m_inst_override_name_queues[obj.get_type_name()].queue;
       m_inst_override_name_queues.delete(obj.get_type_name());
    end
    if(m_wildcard_inst_overrides.size()) begin
       if(! m_inst_override_queues.exists(obj)) 
            m_inst_override_queues[obj] = new;
       foreach (m_wildcard_inst_overrides[i]) begin
         if(uvm_is_match( m_wildcard_inst_overrides[i].orig_type_name, obj.get_type_name()))
            m_inst_override_queues[obj].queue.push_back(m_wildcard_inst_overrides[i]);
       end
    end

  end

endfunction


// set_type_override_by_type
// -------------------------

function void uvm_default_factory::set_type_override_by_type (uvm_object_wrapper original_type,
                                                      uvm_object_wrapper override_type,
                                                      bit replace=1);
  bit replaced;

  // check that old and new are not the same
  if (original_type == override_type) begin
    if (original_type.get_type_name() == "" || original_type.get_type_name() == "<unknown>")
      uvm_report_warning("TYPDUP", {"Original and override type ",
                                    "arguments are identical"}, UVM_NONE);
    else
      uvm_report_warning("TYPDUP", {"Original and override type ",
                                    "arguments are identical: ",
                                    original_type.get_type_name()}, UVM_NONE);
  end

  // register the types if not already done so, for the benefit of string-based lookup
  if (!m_types.exists(original_type))
    register(original_type); 

  if (!m_types.exists(override_type))
    register(override_type); 


  // check for existing type override
  foreach (m_type_overrides[index]) begin
    if (m_type_overrides[index].orig_type == original_type ||
        (m_type_overrides[index].orig_type_name != "<unknown>" &&
         m_type_overrides[index].orig_type_name != "" &&
         m_type_overrides[index].orig_type_name == original_type.get_type_name())) begin
      string msg;
      msg = {"Original object type '",original_type.get_type_name(),
             "' already registered to produce '",
             m_type_overrides[index].ovrd_type_name,"'"};
      if (!replace) begin
        msg = {msg, ".  Set 'replace' argument to replace the existing entry."};
        uvm_report_info("TPREGD", msg, UVM_MEDIUM);
        return;
      end
      msg = {msg, ".  Replacing with override to produce type '",
                  override_type.get_type_name(),"'."};
      uvm_report_info("TPREGR", msg, UVM_MEDIUM);
      replaced = 1;
      m_type_overrides[index].orig_type = original_type; 
      m_type_overrides[index].orig_type_name = original_type.get_type_name(); 
      m_type_overrides[index].ovrd_type = override_type; 
      m_type_overrides[index].ovrd_type_name = override_type.get_type_name(); 
    end
  end

  // make a new entry
  if (!replaced) begin
    uvm_factory_override override;
    override = new(.orig_type(original_type),
                   .orig_type_name(original_type.get_type_name()),
                   .full_inst_path("*"),
                   .ovrd_type(override_type));

    m_type_overrides.push_back(override);
  end

endfunction


// set_type_override_by_name
// -------------------------

function void uvm_default_factory::set_type_override_by_name (string original_type_name,
                                                      string override_type_name,
                                                      bit replace=1);
  bit replaced;
  
  uvm_object_wrapper original_type;
  uvm_object_wrapper override_type;
  string orig_type_name, alias_orig_type_name;

  //check first for aliased original type name
  if (m_type_name_alias.exists(original_type_name)) begin
      orig_type_name = m_type_name_alias[original_type_name];
      alias_orig_type_name = original_type_name;
  end
  else
      orig_type_name = original_type_name;


  if(m_type_names.exists(orig_type_name))
    original_type = m_type_names[orig_type_name];

  if(m_type_names.exists(override_type_name))
    override_type = m_type_names[override_type_name];

  // check that type is registered with the factory
  if (override_type == null) begin
      uvm_report_error("TYPNTF", {"Cannot register override for original type '",
      orig_type_name,"' because the override type '",
      orig_type_name, "' is not registered with the factory."}, UVM_NONE);
    return;
  end

  // check that old and new are not the same
  if (orig_type_name == override_type_name) begin
      uvm_report_warning("TYPDUP", {"Requested and actual type name ",
      " arguments are identical: ",orig_type_name,". Ignoring this override."}, UVM_NONE);
    return;
  end

  foreach (m_type_overrides[index]) begin
    if (m_type_overrides[index].orig_type_name == orig_type_name) begin
      if (!replace) begin
        uvm_report_info("TPREGD", {"Original type '",orig_type_name,
          "' already registered to produce '",m_type_overrides[index].ovrd_type_name,
          "'.  Set 'replace' argument to replace the existing entry."}, UVM_MEDIUM);
        return;
      end
      uvm_report_info("TPREGR", {"Original object type '",orig_type_name,
        "' already registered to produce '",m_type_overrides[index].ovrd_type_name,
        "'.  Replacing with override to produce type '",override_type_name,"'."}, UVM_MEDIUM);
      replaced = 1;
      m_type_overrides[index].ovrd_type = override_type; 
      m_type_overrides[index].ovrd_type_name = override_type_name; 
    end
  end

  if (original_type == null)
    m_lookup_strs[orig_type_name] = 1;

  if (!replaced) begin
    uvm_factory_override override;
    override = new(.orig_type(original_type),
                   .orig_type_name(orig_type_name),
                   .full_inst_path("*"),
                   .ovrd_type(override_type),
                   .orig_type_name_alias(alias_orig_type_name)
                   );

    m_type_overrides.push_back(override);
//    m_type_names[original_type_name] = override.ovrd_type;
  end

endfunction


// check_inst_override_exists
// --------------------------
function bit uvm_default_factory::check_inst_override_exists (uvm_object_wrapper original_type,
                                      uvm_object_wrapper override_type,
                                      string full_inst_path);
  uvm_factory_override override;
  uvm_factory_queue_class qc;

  if (m_inst_override_queues.exists(original_type))
    qc = m_inst_override_queues[original_type];
  else
    return 0;

  for (int index=0; index<qc.queue.size(); ++index) begin

    override = qc.queue[index]; 
    if (override.full_inst_path == full_inst_path &&
        override.orig_type == original_type &&
        override.ovrd_type == override_type &&
        override.orig_type_name == original_type.get_type_name()) begin
    uvm_report_info("DUPOVRD",{"Instance override for '",
       original_type.get_type_name(),"' already exists: override type '",
       override_type.get_type_name(),"' with full_inst_path '",
       full_inst_path,"'"},UVM_HIGH);
      return 1;
    end
  end
  return 0;
endfunction

// set_inst_override_by_type
// -------------------------

function void uvm_default_factory::set_inst_override_by_type (uvm_object_wrapper original_type,
                                                      uvm_object_wrapper override_type,
                                                      string full_inst_path);
  
  uvm_factory_override override;

  // register the types if not already done so
  if (!m_types.exists(original_type))
    register(original_type); 

  if (!m_types.exists(override_type))
    register(override_type); 

  if (check_inst_override_exists(original_type,override_type,full_inst_path))
    return;

  if(!m_inst_override_queues.exists(original_type))
    m_inst_override_queues[original_type] = new;

  override = new(.full_inst_path(full_inst_path),
                 .orig_type(original_type),
                 .orig_type_name(original_type.get_type_name()),
                 .ovrd_type(override_type));


  m_inst_override_queues[original_type].queue.push_back(override);

endfunction


// set_inst_override_by_name
// -------------------------

function void uvm_default_factory::set_inst_override_by_name (string original_type_name,
                                                      string override_type_name,
                                                      string full_inst_path);
  
  uvm_factory_override override;
  uvm_object_wrapper original_type;
  uvm_object_wrapper override_type;
  string orig_type_name, alias_orig_type_name;

  m_inst_typename_alias_t  type_alias_inst[$];  
      
  //Search first typename aliases against requested_type_name using pattern match on full_inst_path
  type_alias_inst = m_type_name_inst_alias.find(i) with ((i.alias_type_name == original_type_name) && uvm_is_match(full_inst_path, i.full_inst_path));
  if (type_alias_inst.size() > 0) begin
      orig_type_name = type_alias_inst[0].orig_type_name;
      alias_orig_type_name = type_alias_inst[0].alias_type_name;
  end
  else
      orig_type_name = original_type_name;

  if(m_type_names.exists(orig_type_name))
    original_type = m_type_names[orig_type_name];

  if(m_type_names.exists(override_type_name))
    override_type = m_type_names[override_type_name];

  // check that type is registered with the factory
  if (override_type == null) begin
    uvm_report_error("TYPNTF", {"Cannot register instance override with type name '",
    orig_type_name,"' and instance path '",full_inst_path,"' because the type it's supposed ",
    "to produce, '",override_type_name,"', is not registered with the factory."}, UVM_NONE);
    return;
  end

  if (original_type == null)
      m_lookup_strs[orig_type_name] = 1;

  override = new(.full_inst_path(full_inst_path),
                 .orig_type(original_type),
                 .orig_type_name(orig_type_name),
                 .orig_type_name_alias(alias_orig_type_name),
                 .ovrd_type(override_type));

  if(original_type != null) begin
    if (check_inst_override_exists(original_type,override_type,full_inst_path))
      return;
    if(!m_inst_override_queues.exists(original_type))
      m_inst_override_queues[original_type] = new;
    m_inst_override_queues[original_type].queue.push_back(override);
  end 
  else begin
    if(m_has_wildcard(orig_type_name)) begin
       foreach(m_type_names[i]) begin
         if(uvm_is_match(orig_type_name,i)) begin
           this.set_inst_override_by_name(i, override_type_name, full_inst_path);
         end
       end
       m_wildcard_inst_overrides.push_back(override);
    end
    else begin
      if(!m_inst_override_name_queues.exists(orig_type_name))
        m_inst_override_name_queues[orig_type_name] = new;
      m_inst_override_name_queues[orig_type_name].queue.push_back(override);
    end
  end

endfunction

//set_type_alias
// ---------------------
  
function void uvm_default_factory::set_type_alias(string alias_type_name, 
                          uvm_object_wrapper original_type); 
    if (!is_type_registered(original_type))
       uvm_report_warning("BDTYP",{"Cannot define alias of type '",
       original_type.get_type_name(),"' because it is not registered with the factory."}, UVM_NONE);      
    else begin
        m_type_name_alias[alias_type_name] = original_type.get_type_name();
    end
endfunction

// set_inst_alias
// ---------------------

function void uvm_default_factory::set_inst_alias(string alias_type_name,
                          uvm_object_wrapper original_type, string full_inst_path);
    
    string original_type_name; 
    m_inst_typename_alias_t  orig_type_alias_per_inst;
    
    original_type_name = original_type.get_type_name();
    
    if (!is_type_registered(original_type))
       uvm_report_warning("BDTYP",{"Cannot define alias of type '",
       original_type_name,"' because it is not registered with the factory."}, UVM_NONE);      
    else begin
        orig_type_alias_per_inst.alias_type_name = alias_type_name;
        orig_type_alias_per_inst.full_inst_path = full_inst_path;
        orig_type_alias_per_inst.orig_type_name = original_type_name;
        m_type_name_inst_alias.push_back(orig_type_alias_per_inst);
    end

endfunction

function bit uvm_default_factory::m_has_wildcard(string nm);
  foreach (nm[i]) 
    if(nm[i] == "*" || nm[i] == "?") return 1;
  return 0;
endfunction





// create_object_by_name
// ---------------------

function uvm_object uvm_default_factory::create_object_by_name (string requested_type_name,  
                                                        string parent_inst_path="",  
                                                        string name=""); 

  uvm_object_wrapper wrapper;
  string inst_path;

  if (parent_inst_path == "")
    inst_path = name;
  else if (name != "")
    inst_path = {parent_inst_path,".",name};
  else
    inst_path = parent_inst_path;

  m_override_info.delete();

  wrapper = find_override_by_name(requested_type_name, inst_path);

  // if no override exists, try to use requested_type_name directly
  if (wrapper==null) begin
    if(!m_type_names.exists(requested_type_name)) begin
      uvm_report_warning("BDTYP",{"Cannot create an object of type '",
      requested_type_name,"' because it is not registered with the factory."}, UVM_NONE);
      return null;
    end
    wrapper = m_type_names[requested_type_name];
  end

  return wrapper.create_object(name);

endfunction


// create_object_by_type
// ---------------------

function uvm_object uvm_default_factory::create_object_by_type (uvm_object_wrapper requested_type,  
                                                        string parent_inst_path="",  
                                                        string name=""); 

  string full_inst_path;

  if (parent_inst_path == "")
    full_inst_path = name;
  else if (name != "")
    full_inst_path = {parent_inst_path,".",name};
  else
    full_inst_path = parent_inst_path;

  m_override_info.delete();

  requested_type = find_override_by_type(requested_type, full_inst_path);

  return requested_type.create_object(name);

endfunction

// is_type_name_registered
// ---------------------
function bit uvm_default_factory::is_type_name_registered (string type_name);
  return (m_type_names.exists(type_name));
endfunction


// is_type_registered
// ---------------------
function bit uvm_default_factory::is_type_registered (uvm_object_wrapper obj);
  return (m_types.exists(obj));
endfunction



// create_component_by_name
// ------------------------

function uvm_component uvm_default_factory::create_component_by_name (string requested_type_name,  
                                                              string parent_inst_path="",  
                                                              string name, 
                                                              uvm_component parent);
  uvm_object_wrapper wrapper;
  string inst_path;

  if (parent_inst_path == "")
    inst_path = name;
  else if (name != "")
    inst_path = {parent_inst_path,".",name};
  else
    inst_path = parent_inst_path;

  m_override_info.delete();

  wrapper = find_override_by_name(requested_type_name, inst_path);

  // if no override exists, try to use requested_type_name directly
  if (wrapper == null) begin
    if(!m_type_names.exists(requested_type_name)) begin 
      uvm_report_warning("BDTYP",{"Cannot create a component of type '",
      requested_type_name,"' because it is not registered with the factory."}, UVM_NONE);
      return null;
    end
    wrapper = m_type_names[requested_type_name];
  end

  return wrapper.create_component(name, parent);

endfunction


// create_component_by_type
// ------------------------

function uvm_component uvm_default_factory::create_component_by_type (uvm_object_wrapper requested_type,  
                                                            string parent_inst_path="",  
                                                            string name, 
                                                            uvm_component parent);
  string full_inst_path;

  if (parent_inst_path == "")
    full_inst_path = name;
  else if (name != "")
    full_inst_path = {parent_inst_path,".",name};
  else
    full_inst_path = parent_inst_path;

  m_override_info.delete();

  requested_type = find_override_by_type(requested_type, full_inst_path);

  return requested_type.create_component(name, parent);

endfunction



// find_wrapper_by_name
// ------------

function uvm_object_wrapper uvm_default_factory::find_wrapper_by_name(string type_name);

  if (m_type_names.exists(type_name))
    return m_type_names[type_name];

  uvm_report_warning("UnknownTypeName", {"find_wrapper_by_name: Type name '",type_name,
      "' not registered with the factory."}, UVM_NONE);
  
endfunction


// find_override_by_name
// ---------------------

function uvm_object_wrapper uvm_default_factory::find_override_by_name (string requested_type_name,
                                                                string full_inst_path);
  uvm_object_wrapper rtype;
  uvm_factory_queue_class qc;
  uvm_factory_override lindex;

  uvm_object_wrapper override;
  string req_type_name;
  m_inst_typename_alias_t  type_alias_inst[$];  
      
  //Search first typename aliases against requested_type_name using pattern match on full_inst_path
  type_alias_inst = m_type_name_inst_alias.find(i) with ((i.alias_type_name == requested_type_name) && uvm_is_match(full_inst_path, i.full_inst_path));
  if (type_alias_inst.size() > 0) begin
      req_type_name = type_alias_inst[0].orig_type_name;
  end
  else if (m_type_name_alias.exists(requested_type_name))
      req_type_name = m_type_name_alias[requested_type_name];
  else
      req_type_name = requested_type_name;

  if (m_type_names.exists(req_type_name))
    rtype = m_type_names[req_type_name];

/***
  if(rtype == null) begin
    if(requested_type_name != "") begin
      uvm_report_warning("TYPNTF", {"Requested type name ",
         requested_type_name, " is not registered with the factory. The instance override to ",
         full_inst_path, " is ignored"}, UVM_NONE);
    end
    m_lookup_strs[requested_type_name] = 1;
    return null;
  end
***/

  if (full_inst_path != "") begin
    if(rtype == null) begin
      if(m_inst_override_name_queues.exists(req_type_name))
        qc = m_inst_override_name_queues[req_type_name];
    end
    else begin
      if(m_inst_override_queues.exists(rtype))
        qc = m_inst_override_queues[rtype];
    end
    if(qc != null)
      for(int index = 0; index<qc.queue.size(); ++index) begin
        if (uvm_is_match(qc.queue[index].orig_type_name, req_type_name) &&
            uvm_is_match(qc.queue[index].full_inst_path, full_inst_path)) begin
          m_override_info.push_back(qc.queue[index]);
          if (m_debug_pass) begin
            if (override == null) begin
              override = qc.queue[index].ovrd_type;
              qc.queue[index].selected = 1;
              lindex=qc.queue[index];
            end
          end
          else begin
	        qc.queue[index].used++;
            if (qc.queue[index].ovrd_type.get_type_name() == req_type_name)
              return qc.queue[index].ovrd_type;
            else 
              return find_override_by_type(qc.queue[index].ovrd_type,full_inst_path);
          end
        end
      end
  end

  if(rtype != null && !m_inst_override_queues.exists(rtype) && m_wildcard_inst_overrides.size()) begin
     m_inst_override_queues[rtype] = new;
     foreach (m_wildcard_inst_overrides[i]) begin
       if(uvm_is_match(m_wildcard_inst_overrides[i].orig_type_name, req_type_name))
         m_inst_override_queues[rtype].queue.push_back(m_wildcard_inst_overrides[i]);
     end
  end

  // type override - exact match
  foreach (m_type_overrides[index])
    if (m_type_overrides[index].orig_type_name == req_type_name) begin
      m_override_info.push_back(m_type_overrides[index]);
      if (m_debug_pass) begin
        if (override == null) begin
          override = m_type_overrides[index].ovrd_type;
          m_type_overrides[index].selected = 1;
          lindex=m_type_overrides[index];
        end
      end
      else begin
	    m_type_overrides[index].used++;
        return find_override_by_type(m_type_overrides[index].ovrd_type,full_inst_path);
      end
    end


  if (m_debug_pass && override != null) begin
	lindex.used++;
    return find_override_by_type(override, full_inst_path);
  end	

  // No override found
  return null;


endfunction


// find_override_by_type
// ---------------------

function uvm_object_wrapper uvm_default_factory::find_override_by_type(uvm_object_wrapper requested_type,
                                                               string full_inst_path);

  uvm_object_wrapper override;
  uvm_factory_override lindex;
  
  uvm_factory_queue_class qc;
  qc = m_inst_override_queues.exists(requested_type) ?
       m_inst_override_queues[requested_type] : null;

  foreach (m_override_info[index]) begin
    if ( //index != m_override_info.size()-1 &&
       m_override_info[index].orig_type == requested_type) begin
      uvm_report_error("OVRDLOOP", "Recursive loop detected while finding override.", UVM_NONE);
      if (!m_debug_pass)
        debug_create_by_type (requested_type, full_inst_path);

	  m_override_info[index].used++;
      return requested_type;
    end
  end

  // inst override; return first match; takes precedence over type overrides
  if (full_inst_path != "" && qc != null)
    for (int index = 0; index < qc.queue.size(); ++index) begin
      if ((qc.queue[index].orig_type == requested_type ||
           (qc.queue[index].orig_type_name != "<unknown>" &&
            qc.queue[index].orig_type_name != "" &&
            qc.queue[index].orig_type_name == requested_type.get_type_name())) &&
          uvm_is_match(qc.queue[index].full_inst_path, full_inst_path)) begin
        m_override_info.push_back(qc.queue[index]);
        if (m_debug_pass) begin
          if (override == null) begin
            override = qc.queue[index].ovrd_type;
            qc.queue[index].selected = 1;
            lindex=qc.queue[index];
          end
        end
        else begin
	      qc.queue[index].used++;	        
          if (qc.queue[index].ovrd_type == requested_type)
            return requested_type;
          else
            return find_override_by_type(qc.queue[index].ovrd_type,full_inst_path);
        end
      end
    end

  // type override - exact match
  foreach (m_type_overrides[index]) begin
    if (m_type_overrides[index].orig_type == requested_type ||
        (m_type_overrides[index].orig_type_name != "<unknown>" &&
         m_type_overrides[index].orig_type_name != "" &&
         requested_type != null &&
         m_type_overrides[index].orig_type_name == requested_type.get_type_name())) begin
      m_override_info.push_back(m_type_overrides[index]);
      if (m_debug_pass) begin
        if (override == null) begin
          override = m_type_overrides[index].ovrd_type;
          m_type_overrides[index].selected = 1;
          lindex=m_type_overrides[index];
        end
      end
      else begin
	    m_type_overrides[index].used++;	      
        if (m_type_overrides[index].ovrd_type == requested_type)
          return requested_type;
        else
          return find_override_by_type(m_type_overrides[index].ovrd_type,full_inst_path);
      end
    end
  end

  // type override with wildcard match
  //foreach (m_type_overrides[index])
  //  if (uvm_is_match(index,requested_type.get_type_name())) begin
  //    m_override_info.push_back(m_inst_overrides[index]);
  //    return find_override_by_type(m_type_overrides[index],full_inst_path);
  //  end

  if (m_debug_pass && override != null) begin
    lindex.used++;	  
    if (override == requested_type) begin
      return requested_type;
    end	
    else
      return find_override_by_type(override,full_inst_path);
  end	
  
  return requested_type;

endfunction


// print
// -----

function void uvm_default_factory::print (int all_types=1);

  string key;
  uvm_factory_queue_class sorted_override_queues[string];
  string qs[$];

  string tmp;
  int id;
  uvm_object_wrapper obj;

  //sort the override queues
  foreach (m_inst_override_queues[i]) begin
    obj = i;
    tmp = obj.get_type_name();
    if(tmp == "") $swrite(tmp, "__unnamed_id_%0d", id++);
    sorted_override_queues[tmp] = m_inst_override_queues[i];

  end
  foreach (m_inst_override_name_queues[i]) begin
    sorted_override_queues[i] = m_inst_override_name_queues[i];
  end

  qs.push_back("\n#### Factory Configuration (*)\n\n");

  // print instance overrides
  if(!m_type_overrides.size() && !sorted_override_queues.num())
    qs.push_back("  No instance or type overrides are registered with this factory\n");
  else begin
    int max1,max2,max3;
    string dash = "---------------------------------------------------------------------------------------------------";
    string space= "                                                                                                   ";

    // print instance overrides
    if(!sorted_override_queues.num())
      qs.push_back("No instance overrides are registered with this factory\n");
    else begin
      foreach(sorted_override_queues[j]) begin
        uvm_factory_queue_class qc;
        qc = sorted_override_queues[j];
        for (int i=0; i<qc.queue.size(); ++i) begin
          if (qc.queue[i].orig_type_name.len() > max1)
            max1=qc.queue[i].orig_type_name.len();
          if (qc.queue[i].full_inst_path.len() > max2)
            max2=qc.queue[i].full_inst_path.len();
          if (qc.queue[i].ovrd_type_name.len() > max3)
            max3=qc.queue[i].ovrd_type_name.len();
        end
      end
      if (max1 < 14) max1 = 14;
      if (max2 < 13) max2 = 13;
      if (max3 < 13) max3 = 13;

      qs.push_back("Instance Overrides:\n\n");
      qs.push_back($sformatf("  %0s%0s  %0s%0s  %0s%0s\n","Requested Type",space.substr(1,max1-14),
                                          "Override Path", space.substr(1,max2-13),
                                          "Override Type", space.substr(1,max3-13)));
      qs.push_back($sformatf("  %0s  %0s  %0s\n",dash.substr(1,max1),
                                 dash.substr(1,max2),
                                 dash.substr(1,max3)));

      foreach(sorted_override_queues[j]) begin
        uvm_factory_queue_class qc;
        qc = sorted_override_queues[j];
        for (int i=0; i<qc.queue.size(); ++i) begin
          qs.push_back($sformatf("  %0s%0s  %0s%0s",qc.queue[i].orig_type_name,
                 space.substr(1,max1-qc.queue[i].orig_type_name.len()),
                 qc.queue[i].full_inst_path,
                 space.substr(1,max2-qc.queue[i].full_inst_path.len())));
          qs.push_back($sformatf("  %0s\n",     qc.queue[i].ovrd_type_name));
        end
      end
    end

    // print type overrides
    if (!m_type_overrides.size())
      qs.push_back("\nNo type overrides are registered with this factory\n");
    else begin
      // Resize for type overrides
      if (max1 < 14) max1 = 14;
      if (max2 < 13) max2 = 13;
      if (max3 < 13) max3 = 13;

      foreach (m_type_overrides[i]) begin
        if (m_type_overrides[i].orig_type_name.len() > max1)
          max1=m_type_overrides[i].orig_type_name.len();
        if (m_type_overrides[i].ovrd_type_name.len() > max2)
          max2=m_type_overrides[i].ovrd_type_name.len();
      end
      if (max1 < 14) max1 = 14;
      if (max2 < 13) max2 = 13;
      qs.push_back("\nType Overrides:\n\n");
      qs.push_back($sformatf("  %0s%0s  %0s%0s\n","Requested Type",space.substr(1,max1-14),
                                  "Override Type", space.substr(1,max2-13)));
      qs.push_back($sformatf("  %0s  %0s\n",dash.substr(1,max1),
                            dash.substr(1,max2)));
      foreach (m_type_overrides[index]) 
        qs.push_back($sformatf("  %0s%0s  %0s\n",
                 m_type_overrides[index].orig_type_name,
                 space.substr(1,max1-m_type_overrides[index].orig_type_name.len()),
                 m_type_overrides[index].ovrd_type_name));
    end
  end

  // print all registered types, if all_types >= 1 
  if (all_types >= 1 && m_type_names.first(key)) begin
    bit banner;
    qs.push_back($sformatf("\nAll types registered with the factory: %0d total\n",m_types.num()));
    do begin
      // filter out uvm_ classes (if all_types<2) and non-types (lookup strings)
      if (!(all_types < 2 && uvm_is_match("uvm_*",
           m_type_names[key].get_type_name())) &&
           key == m_type_names[key].get_type_name()) begin
        if (!banner) begin
          qs.push_back("  Type Name\n");
          qs.push_back("  ---------\n");
          banner=1;
        end
        qs.push_back($sformatf("  %s\n", m_type_names[key].get_type_name()));
      end
    end while(m_type_names.next(key));
  end

  qs.push_back("(*) Types with no associated type name will be printed as <unknown>\n\n####\n\n");

  `uvm_info("UVM/FACTORY/PRINT",`UVM_STRING_QUEUE_STREAMING_PACK(qs),UVM_NONE)
endfunction


// debug_create_by_name
// --------------------

function void  uvm_default_factory::debug_create_by_name (string requested_type_name,
                                                  string parent_inst_path="",
                                                  string name="");
  m_debug_create(requested_type_name, null, parent_inst_path, name);
endfunction


// debug_create_by_type
// --------------------

function void  uvm_default_factory::debug_create_by_type (uvm_object_wrapper requested_type,
                                                  string parent_inst_path="",
                                                  string name="");
  m_debug_create("", requested_type, parent_inst_path, name);
endfunction


// m_debug_create
// --------------

function void  uvm_default_factory::m_debug_create (string requested_type_name,
                                            uvm_object_wrapper requested_type,
                                            string parent_inst_path,
                                            string name);

  string full_inst_path;
  uvm_object_wrapper result;
  
  if (parent_inst_path == "")
    full_inst_path = name;
  else if (name != "")
    full_inst_path = {parent_inst_path,".",name};
  else
    full_inst_path = parent_inst_path;

  m_override_info.delete();

  if (requested_type == null) begin
    if (!m_type_names.exists(requested_type_name) &&
      !m_lookup_strs.exists(requested_type_name)) begin
      uvm_report_warning("Factory Warning", {"The factory does not recognize '",
        requested_type_name,"' as a registered type."}, UVM_NONE);
      return;
    end
    m_debug_pass = 1;
    
    result = find_override_by_name(requested_type_name,full_inst_path);
  end
  else begin
    m_debug_pass = 1;
    if (!m_types.exists(requested_type))
      register(requested_type); 
    result = find_override_by_type(requested_type,full_inst_path);
    if (requested_type_name == "")
      requested_type_name = requested_type.get_type_name();
  end

  m_debug_display(requested_type_name, result, full_inst_path);
  m_debug_pass = 0;

  foreach (m_override_info[index])
    m_override_info[index].selected = 0;

endfunction


// m_debug_display
// ---------------

function void  uvm_default_factory::m_debug_display (string requested_type_name,
                                             uvm_object_wrapper result,
                                             string full_inst_path);

  int    max1,max2,max3;
  string dash = "---------------------------------------------------------------------------------------------------";
  string space= "                                                                                                   ";
  string qs[$];

  qs.push_back("\n#### Factory Override Information (*)\n\n");
  qs.push_back(
  	$sformatf("Given a request for an object of type '%s' with an instance\npath of '%s' the factory encountered\n\n",
  		requested_type_name,full_inst_path));

  if (m_override_info.size() == 0)
    qs.push_back("no relevant overrides.\n\n");
  else begin

    qs.push_back("the following relevant overrides. An 'x' next to a match indicates a\nmatch that was ignored.\n\n");

    foreach (m_override_info[i]) begin
      if (m_override_info[i].orig_type_name.len() > max1)
        max1=m_override_info[i].orig_type_name.len();
      if (m_override_info[i].full_inst_path.len() > max2)
        max2=m_override_info[i].full_inst_path.len();
      if (m_override_info[i].ovrd_type_name.len() > max3)
        max3=m_override_info[i].ovrd_type_name.len();
    end

    if (max1 < 13) max1 = 13;
    if (max2 < 13) max2 = 13;
    if (max3 < 13) max3 = 13;

    qs.push_back($sformatf("Original Type%0s  Instance Path%0s  Override Type%0s\n", 
    	space.substr(1,max1-13),space.substr(1,max2-13),space.substr(1,max3-13)));

    qs.push_back($sformatf("  %0s  %0s  %0s\n",dash.substr(1,max1),
                               dash.substr(1,max2),
                               dash.substr(1,max3)));

    foreach (m_override_info[i]) begin
      qs.push_back($sformatf("%s%0s%0s\n",
             m_override_info[i].selected ? "  " : "x ",
             m_override_info[i].orig_type_name,
             space.substr(1,max1-m_override_info[i].orig_type_name.len())));
      qs.push_back($sformatf("  %0s%0s", m_override_info[i].full_inst_path,
             space.substr(1,max2-m_override_info[i].full_inst_path.len())));
      qs.push_back($sformatf("  %0s%0s", m_override_info[i].ovrd_type_name,
             space.substr(1,max3-m_override_info[i].ovrd_type_name.len())));
      if (m_override_info[i].full_inst_path == "*")
        qs.push_back("  <type override>");
      else
        qs.push_back("\n");
    end
    qs.push_back("\n");
  end


  qs.push_back("Result:\n\n");
  qs.push_back($sformatf("  The factory will produce an object of type '%0s'\n", 
           result == null ? requested_type_name : result.get_type_name()));

  qs.push_back("\n(*) Types with no associated type name will be printed as <unknown>\n\n####\n\n");
  
  `uvm_info("UVM/FACTORY/DUMP",`UVM_STRING_QUEUE_STREAMING_PACK(qs),UVM_NONE)
endfunction
