//----------------------------------------------------------------------
// Copyright 2018 Cadence Design Systems, Inc.
// Copyright 2018 NVIDIA Corporation
// Copyright 2017 Cisco Systems, Inc.
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

//----------------------------------------------------------------------
// Title -- NODOCS -- Resources
//
// Topic: Intro
//
// A resource is a parameterized container that holds arbitrary data.
// Resources can be used to configure components, supply data to
// sequences, or enable sharing of information across disparate parts of
// a testbench.  They are stored using scoping information so their
// visibility can be constrained to certain parts of the testbench.
// Resource containers can hold any type of data, constrained only by
// the data types available in SystemVerilog.  Resources can contain
// scalar objects, class handles, queues, lists, or even virtual
// interfaces.
//
// Resources are stored in a resource database so that each resource can
// be retrieved by name or by type. The database has both a name table
// and a type table and each resource is entered into both. The database
// is globally accessible.
//
// Each resource has a set of scopes over which it is visible.  The set
// of scopes is represented as a regular expression.  When a resource is
// looked up the scope of the entity doing the looking up is supplied to
// the lookup function.  This is called the ~current scope~.  If the
// current scope is in the set of scopes over which a resource is
// visible then the resource can be retuned in the lookup.
//
// Resources can be looked up by name or by type. To support type lookup
// each resource has a static type handle that uniquely identifies the
// type of each specialized resource container.
//
// Multiple resources that have the same name are stored in a queue.
// Each resource is pushed into a queue with the first one at the front
// of the queue and each subsequent one behind it.  The same happens for
// multiple resources that have the same type.  The resource queues are
// searched front to back, so those placed earlier in the queue have
// precedence over those placed later.
//
// The precedence of resources with the same name or same type can be
// altered.  One way is to set the ~precedence~ member of the resource
// container to any arbitrary value.  The search algorithm will return
// the resource with the highest precedence.  In the case where there
// are multiple resources that match the search criteria and have the
// same (highest) precedence, the earliest one located in the queue will
// be one returned.  Another way to change the precedence is to use the
// set_priority function to move a resource to either the front or back
// of the queue.
//
// The classes defined here form the low level layer of the resource
// database.  The classes include the resource container and the database
// that holds the containers.  The following set of classes are defined
// here:
//
// <uvm_resource_types>: A class without methods or members, only
// typedefs and enums. These types and enums are used throughout the
// resources facility.  Putting the types in a class keeps them confined
// to a specific name space.
//
// <uvm_resource_options>: policy class for setting options, such
// as auditing, which effect resources.
//
// <uvm_resource_base>: the base (untyped) resource class living in the
// resource database.  This class includes the interface for setting a
// resource as read-only, notification, scope management, altering
// search priority, and managing auditing.
//
// <uvm_resource#(T)>: parameterized resource container.  This class
// includes the interfaces for reading and writing each resource.
// Because the class is parameterized, all the access functions are type
// safe.
//
// <uvm_resource_pool>: the resource database. This is a singleton
// class object.
//----------------------------------------------------------------------

typedef class uvm_resource_base; // forward reference


//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_resource_types
//
// Provides typedefs and enums used throughout the resources facility.
// This class has no members or methods, only typedefs.  It's used in
// lieu of package-scope types.  When needed, other classes can use
// these types by prefixing their usage with uvm_resource_types::.  E.g.
//
//|  uvm_resource_types::rsrc_q_t queue;
//
//----------------------------------------------------------------------
class uvm_resource_types;

  // types uses for setting overrides
  typedef bit[1:0] override_t;
  typedef enum override_t { TYPE_OVERRIDE = 2'b01,
                            NAME_OVERRIDE = 2'b10 } override_e;

   // general purpose queue of resourcex
  typedef uvm_queue#(uvm_resource_base) rsrc_q_t;

  // enum for setting resource search priority
  typedef enum { PRI_HIGH, PRI_LOW } priority_e;

  // access record for resources.  A set of these is stored for each
  // resource by accessing object.  It's updated for each read/write.
  typedef struct
  {
    time read_time;
    time write_time;
    int unsigned read_count;
    int unsigned write_count;
  } access_t;

endclass

//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_resource_options
//
// Provides a namespace for managing options for the
// resources facility.  The only thing allowed in this class is static
// local data members and static functions for manipulating and
// retrieving the value of the data members.  The static local data
// members represent options and settings that control the behavior of
// the resources facility.

// Options include:
//
//  * auditing:  on/off
//
//    The default for auditing is on.  You may wish to turn it off to
//    for performance reasons.  With auditing off memory is not
//    consumed for storage of auditing information and time is not
//    spent collecting and storing auditing information.  Of course,
//    during the period when auditing is off no audit trail information
//    is available
//
//----------------------------------------------------------------------
class uvm_resource_options;

  static local bit auditing = 1;

  // Function -- NODOCS -- turn_on_auditing
  //
  // Turn auditing on for the resource database. This causes all
  // reads and writes to the database to store information about
  // the accesses. Auditing is turned on by default.

  static function void turn_on_auditing();
    auditing = 1;
  endfunction

  // Function -- NODOCS -- turn_off_auditing
  //
  // Turn auditing off for the resource database. If auditing is turned off,
  // it is not possible to get extra information about resource
  // database accesses.

  static function void turn_off_auditing();
    auditing = 0;
  endfunction

  // Function -- NODOCS -- is_auditing
  //
  // Returns 1 if the auditing facility is on and 0 if it is off.

  static function bit is_auditing();
    return auditing;
  endfunction
endclass

//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_resource_base
//
// Non-parameterized base class for resources.  Supports interfaces for
// scope matching, and virtual functions for printing the resource and
// for printing the accessor list
//----------------------------------------------------------------------

//----------------------------------------------------------------------
// Class: uvm_resource_base
//
// The library implements the following public API beyond what is 
// documented in 1800.2.
//----------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto C.2.3.1
virtual class uvm_resource_base extends uvm_object;

`ifdef UVM_ENABLE_DEPRECATED_API
  protected string scope;
`endif // UVM_ENABLE_DEPRECATED_API
  protected bit modified;
  protected bit read_only;

  uvm_resource_types::access_t access[string];

`ifdef UVM_ENABLE_DEPRECATED_API
  // variable -- NODOCS -- precedence
  //
  // This variable is used to associate a precedence that a resource
  // has with respect to other resources which match the same scope
  // and name. Resources are set to the <default_precedence> initially,
  // and may be set to a higher or lower precedence as desired.

  int unsigned precedence;

  // variable -- NODOCS -- default_precedence
  //
  // The default precedence for an resource that has been created.
  // When two resources have the same precedence, the first resource
  // found has precedence.
  //

  static int unsigned default_precedence = 1000;
`endif // UVM_ENABLE_DEPRECATED_API

  // Function -- NODOCS -- new
  //
  // constructor for uvm_resource_base.  The constructor takes two
  // arguments, the name of the resource and a regular expression which
  // represents the set of scopes over which this resource is visible.

`ifdef UVM_ENABLE_DEPRECATED_API
  function new(string name = "", string s = "*");
    super.new(name);
    set_scope(s);
    modified = 0;
    read_only = 0;
    precedence = default_precedence;
  endfunction
`else
  // @uvm-ieee 1800.2-2017 auto C.2.3.2.1
  function new(string name = "");
    super.new(name);
    modified = 0;
    read_only = 0;
  endfunction
`endif // UVM_ENABLE_DEPRECATED_API


  // Function -- NODOCS -- get_type_handle
  //
  // Pure virtual function that returns the type handle of the resource
  // container.

  // @uvm-ieee 1800.2-2017 auto C.2.3.2.2
  pure virtual function uvm_resource_base get_type_handle();


  //---------------------------
  // Group -- NODOCS -- Read-only Interface
  //---------------------------

  // Function -- NODOCS -- set_read_only
  //
  // Establishes this resource as a read-only resource.  An attempt
  // to call <uvm_resource#(T)::write> on the resource will cause an error.

  // @uvm-ieee 1800.2-2017 auto C.2.3.3.1
  function void set_read_only();
    read_only = 1;
  endfunction

  // function set_read_write
  //
  // Returns the resource to normal read-write capability.
  
  // Implementation question: Not sure if this function is necessary.  
  // Once a resource is set to read_only no one should be able to change 
  // that.  If anyone can flip the read_only bit then the resource is not 
  // truly read_only.

  function void set_read_write();
    read_only = 0;
  endfunction


  // @uvm-ieee 1800.2-2017 auto C.2.3.3.2
  function bit is_read_only();
    return read_only;
  endfunction


  //--------------------
  // Group -- NODOCS -- Notification
  //--------------------

  // Task -- NODOCS -- wait_modified
  //
  // This task blocks until the resource has been modified -- that is, a
  // <uvm_resource#(T)::write> operation has been performed.  When a 
  // <uvm_resource#(T)::write> is performed the modified bit is set which 
  // releases the block.  Wait_modified() then clears the modified bit so 
  // it can be called repeatedly.

  // @uvm-ieee 1800.2-2017 auto C.2.3.4
  task wait_modified();
    wait (modified == 1);
    modified = 0;
  endtask

`ifdef UVM_ENABLE_DEPRECATED_API
  //-----------------------
  // Group -- NODOCS -- Scope Interface
  //-----------------------
  //

  // Function -- NODOCS -- set_scope
  //
  // Set the value of the regular expression that identifies the set of
  // scopes over which this resource is visible.  If the supplied
  // argument is a glob it will be converted to a regular expression
  // before it is stored.
  //
  function void set_scope(string s);
    scope = uvm_glob_to_re(s);
  endfunction

  // Function -- NODOCS -- get_scope
  //
  // Retrieve the regular expression string that identifies the set of
  // scopes over which this resource is visible.
  //
  function string get_scope();
    return scope;
  endfunction

  // Function -- NODOCS -- match_scope
  //
  // Using the regular expression facility, determine if this resource
  // is visible in a scope.  Return one if it is, zero otherwise.
  //
  function bit match_scope(string s);
    int match = uvm_is_match(scope, s);
    return match;
  endfunction

  //----------------
  // Group -- NODOCS -- Priority
  //----------------
  //
  // Functions for manipulating the search priority of resources.  The
  // function definitions here are pure virtual and are implemented in
  // derived classes.  The definitons serve as a priority management
  // interface.

  // Function -- NODOCS -- set priority
  //
  // Change the search priority of the resource based on the value of
  // the priority enum argument.
  //
  pure virtual function void set_priority (uvm_resource_types::priority_e pri);
`endif // UVM_ENABLE_DEPRECATED_API

  //-------------------------
  // Group -- NODOCS -- Utility Functions
  //-------------------------

  // function convert2string
  //
  // Create a string representation of the resource value.  By default
  // we don't know how to do this so we just return a "?".  Resource
  // specializations are expected to override this function to produce a
  // proper string representation of the resource value.

  function string convert2string();
    return $sformatf("(%s) %s", m_value_type_name(), m_value_as_string());
  endfunction // convert2string

  // Helper for printing externally, non-LRM
  pure virtual function string m_value_type_name();
  pure virtual function string m_value_as_string();
  
  function void do_print(uvm_printer printer);
    super.do_print(printer);
    printer.print_generic_element("val", m_value_type_name(), "", m_value_as_string());
  endfunction : do_print
  
  
  //-------------------
  // Group -- NODOCS -- Audit Trail
  //-------------------
  //
  // To find out what is happening as the simulation proceeds, an audit 
  // trail of each read and write is kept. The <uvm_resource#(T)::read> and 
  // <uvm_resource#(T)::write> methods each take an accessor argument.  This is a
  // handle to the object that performed that resource access.
  //
  //|    function T read(uvm_object accessor = null);
  //|    function void write(T t, uvm_object accessor = null);
  //
  // The accessor can by anything as long as it is derived from
  // uvm_object.  The accessor object can be a component or a sequence
  // or whatever object from which a read or write was invoked.
  // Typically the ~this~ handle is used as the
  // accessor.  For example:
  //
  //|    uvm_resource#(int) rint;
  //|    int i;
  //|    ...
  //|    rint.write(7, this);
  //|    i = rint.read(this);
  //
  // The accessor's ~get_full_name()~ is stored as part of the audit trail. 
  // This way you can find out what object performed each resource access.
  // Each audit record also includes the time of the access (simulation time)
  // and the particular operation performed (read or write).
  //
  // Auditing is controlled through the <uvm_resource_options> class.

  // function: record_read_access

  function void record_read_access(uvm_object accessor = null);

    string str;
    uvm_resource_types::access_t access_record;

    // If an accessor object is supplied then get the accessor record.
    // Otherwise create a new access record.  In either case populate
    // the access record with information about this access.  Check
    // first to make sure that auditing is turned on.

    if(!uvm_resource_options::is_auditing())
      return;

    // If an accessor is supplied, then use its name
	// as the database entry for the accessor record.
	// Otherwise, use "<empty>" as the database entry.
    if(accessor != null)
      str = accessor.get_full_name();
    else
      str = "<empty>";

    // Create a new accessor record if one does not exist
    if(access.exists(str))
      access_record = access[str];
    else
      init_access_record(access_record);

    // Update the accessor record
    access_record.read_count++;
    access_record.read_time = $realtime;
    access[str] = access_record;

  endfunction

  // function: record_write_access

  function void record_write_access(uvm_object accessor = null);

    string str;

    // If an accessor object is supplied then get the accessor record.
    // Otherwise create a new access record.  In either case populate
    // the access record with information about this access.  Check
    // first that auditing is turned on

    if(uvm_resource_options::is_auditing()) begin
      if(accessor != null) begin
        uvm_resource_types::access_t access_record;
        string str;
        str = accessor.get_full_name();
        if(access.exists(str))
          access_record = access[str];
        else
          init_access_record(access_record);
        access_record.write_count++;
        access_record.write_time = $realtime;
        access[str] = access_record;
      end
    end
  endfunction

  // Function: print_accessors
  //
  // Dump the access records for this resource
  //
  virtual function void print_accessors();

    string str;
    uvm_component comp;
    uvm_resource_types::access_t access_record;
    string qs[$];
    
    if(access.num() == 0)
      return;

    foreach (access[i]) begin
      str = i;
      access_record = access[str];
      qs.push_back($sformatf("%s reads: %0d @ %0t  writes: %0d @ %0t\n",str,
               access_record.read_count,
               access_record.read_time,
               access_record.write_count,
               access_record.write_time));
    end
    `uvm_info("UVM/RESOURCE/ACCESSOR",`UVM_STRING_QUEUE_STREAMING_PACK(qs),UVM_NONE)

  endfunction


  // Function -- NODOCS -- init_access_record
  //
  // Initialize a new access record
  //
  function void init_access_record (inout uvm_resource_types::access_t access_record);
    access_record.read_time = 0;
    access_record.write_time = 0;
    access_record.read_count = 0;
    access_record.write_count = 0;
  endfunction
endclass



