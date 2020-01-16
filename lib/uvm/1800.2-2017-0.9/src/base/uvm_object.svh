//
//-----------------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2010-2018 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2010-2012 AMD
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2017-2018 Cisco Systems, Inc.
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
//-----------------------------------------------------------------------------


typedef class uvm_report_object;
typedef class uvm_object_wrapper;
typedef class uvm_objection;
typedef class uvm_component;
typedef class uvm_resource_base;
typedef class uvm_resource;
typedef class uvm_field_op;

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_object
//
// The uvm_object class is the base class for all UVM data and hierarchical 
// classes. Its primary role is to define a set of methods for such common
// operations as <create>, <copy>, <compare>, <print>, and <record>. Classes
// deriving from uvm_object must implement the pure virtual methods such as 
// <create> and <get_type_name>.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 5.3.1
virtual class uvm_object extends uvm_void;


  // Function -- NODOCS -- new
  //
  // Creates a new uvm_object with the given instance ~name~. If ~name~ is not
  // supplied, the object is unnamed.

  extern function new (string name="");


  // Group -- NODOCS -- Seeding

`ifdef UVM_ENABLE_DEPRECATED_API
  // Variable -- NODOCS -- use_uvm_seeding
  //
  // This bit enables or disables the UVM seeding mechanism. It globally affects
  // the operation of the <reseed> method.
  //
  // When enabled, UVM-based objects are seeded based on their type and full
  // hierarchical name rather than allocation order. This improves random
  // stability for objects whose instance names are unique across each type.
  // The <uvm_component> class is an example of a type that has a unique
  // instance name.

  static bit use_uvm_seeding = 1;
`endif 

  // Function -- NODOCS -- get_uvm_seeding

  // @uvm-ieee 1800.2-2017 auto 5.3.3.1
  extern static function bit get_uvm_seeding();
      
  // Function -- NODOCS -- set_uvm_seeding

  // @uvm-ieee 1800.2-2017 auto 5.3.3.2
  extern static function void set_uvm_seeding(bit enable);
   
  // Function -- NODOCS -- reseed
  //
  // Calls ~srandom~ on the object to reseed the object using the UVM seeding
  // mechanism, which sets the seed based on type name and instance name instead
  // of based on instance position in a thread. 
  //
  // If <get_uvm_seeding> returns 0, then reseed() does
  // not perform any function. 

  // @uvm-ieee 1800.2-2017 auto 5.3.3.3
  extern function void reseed ();


  // Group -- NODOCS -- Identification

  // Function -- NODOCS -- set_name
  //
  // Sets the instance name of this object, overwriting any previously
  // given name.

  // @uvm-ieee 1800.2-2017 auto 5.3.4.1
  extern virtual function void set_name (string name);


  // Function -- NODOCS -- get_name
  //
  // Returns the name of the object, as provided by the ~name~ argument in the
  // <new> constructor or <set_name> method.

  // @uvm-ieee 1800.2-2017 auto 5.3.4.2
  extern virtual function string get_name ();


  // Function -- NODOCS -- get_full_name
  //
  // Returns the full hierarchical name of this object. The default
  // implementation is the same as <get_name>, as uvm_objects do not inherently
  // possess hierarchy. 
  //
  // Objects possessing hierarchy, such as <uvm_components>, override the default
  // implementation. Other objects might be associated with component hierarchy
  // but are not themselves components. For example, <uvm_sequence #(REQ,RSP)>
  // classes are typically associated with a <uvm_sequencer #(REQ,RSP)>. In this
  // case, it is useful to override get_full_name to return the sequencer's
  // full name concatenated with the sequence's name. This provides the sequence
  // a full context, which is useful when debugging.

  // @uvm-ieee 1800.2-2017 auto 5.3.4.3
  extern virtual function string get_full_name ();


  // Function -- NODOCS -- get_inst_id
  //
  // Returns the object's unique, numeric instance identifier.

  // @uvm-ieee 1800.2-2017 auto 5.3.4.4
  extern virtual function int get_inst_id ();


  // Function -- NODOCS -- get_inst_count
  //
  // Returns the current value of the instance counter, which represents the
  // total number of uvm_object-based objects that have been allocated in
  // simulation. The instance counter is used to form a unique numeric instance
  // identifier.

  extern static  function int get_inst_count();


  // Function -- NODOCS -- get_type
  //
  // Returns the type-proxy (wrapper) for this object. The <uvm_factory>'s
  // type-based override and creation methods take arguments of
  // <uvm_object_wrapper>. This method, if implemented, can be used as convenient
  // means of supplying those arguments.
  //
  // The default implementation of this method produces an error and returns
  // ~null~. To enable use of this method, a user's subtype must implement a
  // version that returns the subtype's wrapper.
  //
  // For example:
  //
  //|  class cmd extends uvm_object;
  //|    typedef uvm_object_registry #(cmd) type_id;
  //|    static function type_id get_type();
  //|      return type_id::get();
  //|    endfunction
  //|  endclass
  //
  // Then, to use:
  //
  //|  factory.set_type_override(cmd::get_type(),subcmd::get_type());
  //
  // This function is implemented by the `uvm_*_utils macros, if employed.

  extern static function uvm_object_wrapper get_type ();


  // Function -- NODOCS -- get_object_type
  //
  // Returns the type-proxy (wrapper) for this object. The <uvm_factory>'s
  // type-based override and creation methods take arguments of
  // <uvm_object_wrapper>. This method, if implemented, can be used as convenient
  // means of supplying those arguments. This method is the same as the static
  // <get_type> method, but uses an already allocated object to determine
  // the type-proxy to access (instead of using the static object).
  //
  // The default implementation of this method does a factory lookup of the
  // proxy using the return value from <get_type_name>. If the type returned
  // by <get_type_name> is not registered with the factory, then a ~null~
  // handle is returned.
  //
  // For example:
  //
  //|  class cmd extends uvm_object;
  //|    typedef uvm_object_registry #(cmd) type_id;
  //|    static function type_id get_type();
  //|      return type_id::get();
  //|    endfunction
  //|    virtual function type_id get_object_type();
  //|      return type_id::get();
  //|    endfunction
  //|  endclass
  //
  // This function is implemented by the `uvm_*_utils macros, if employed.

  extern virtual function uvm_object_wrapper get_object_type ();


  // Function -- NODOCS -- get_type_name
  //
  // This function returns the type name of the object, which is typically the
  // type identifier enclosed in quotes. It is used for various debugging
  // functions in the library, and it is used by the factory for creating
  // objects.
  //
  // This function must be defined in every derived class. 
  //
  // A typical implementation is as follows:
  //
  //|  class mytype extends uvm_object;
  //|    ...
  //|    static function string type_name(); return "myType"; endfunction : type_name
  //|
  //|    virtual function string get_type_name();
  //|      return type_name;
  //|    endfunction
  //
  // We define the ~type_name~ static method to enable access to the type name
  // without need of an object of the class, i.e., to enable access via the
  // scope operator, ~mytype::type_name~.

  virtual function string get_type_name (); return "<unknown>"; endfunction


  // Group -- NODOCS -- Creation

  // Function -- NODOCS -- create
  //
  // The ~create~ method allocates a new object of the same type as this object
  // and returns it via a base uvm_object handle. Every class deriving from
  // uvm_object, directly or indirectly, must implement the create method.
  //
  // A typical implementation is as follows:
  //
  //|  class mytype extends uvm_object;
  //|    ...
  //|    virtual function uvm_object create(string name="");
  //|      mytype t = new(name);
  //|      return t;
  //|    endfunction 

  virtual function uvm_object create (string name=""); return null; endfunction

  
  // Function -- NODOCS -- clone
  //
  // The ~clone~ method creates and returns an exact copy of this object.
  // 
  // The default implementation calls <create> followed by <copy>. As clone is
  // virtual, derived classes may override this implementation if desired. 

  // @uvm-ieee 1800.2-2017 auto 5.3.5.2
  extern virtual function uvm_object clone ();


  // Group -- NODOCS -- Printing

  // Function -- NODOCS -- print
  // 
  // The ~print~ method deep-prints this object's properties in a format and
  // manner governed by the given ~printer~ argument; if the ~printer~ argument
  // is not provided, the global <uvm_default_printer> is used. See 
  // <uvm_printer> for more information on printer output formatting. See also
  // <uvm_line_printer>, <uvm_tree_printer>, and <uvm_table_printer> for details
  // on the pre-defined printer "policies," or formatters, provided by the UVM.
  //
  // The ~print~ method is not virtual and must not be overloaded. To include
  // custom information in the ~print~ and <sprint> operations, derived classes
  // must override the <do_print> method and use the provided printer policy
  // class to format the output.

  // @uvm-ieee 1800.2-2017 auto 5.3.6.1
  extern function void print (uvm_printer printer=null);


  // Function -- NODOCS -- sprint
  //
  // The ~sprint~ method works just like the <print> method, except the output
  // is returned in a string rather than displayed. 
  //
  // The ~sprint~ method is not virtual and must not be overloaded. To include
  // additional fields in the <print> and ~sprint~ operation, derived classes
  // must override the <do_print> method and use the provided printer policy
  // class to format the output. The printer policy will manage all string
  // concatenations and provide the string to ~sprint~ to return to the caller.

  // @uvm-ieee 1800.2-2017 auto 5.3.6.2
  extern function string sprint (uvm_printer printer=null); 


  // Function -- NODOCS -- do_print
  //
  // The ~do_print~ method is the user-definable hook called by <print> and
  // <sprint> that allows users to customize what gets printed or sprinted 
  // beyond the field information provided by the `uvm_field_* macros,
  // <Utility and Field Macros for Components and Objects>.
  //
  // The ~printer~ argument is the policy object that governs the format and
  // content of the output. To ensure correct <print> and <sprint> operation,
  // and to ensure a consistent output format, the ~printer~ must be used
  // by all <do_print> implementations. That is, instead of using ~$display~ or
  // string concatenations directly, a ~do_print~ implementation must call
  // through the ~printer's~ API to add information to be printed or sprinted.
  //
  // An example implementation of ~do_print~ is as follows:
  //
  //| class mytype extends uvm_object;
  //|   data_obj data;
  //|   int f1;
  //|   virtual function void do_print (uvm_printer printer);
  //|     super.do_print(printer);
  //|     printer.print_field_int("f1", f1, $bits(f1), UVM_DEC);
  //|     printer.print_object("data", data);
  //|   endfunction
  //
  // Then, to print and sprint the object, you could write:
  //
  //| mytype t = new;
  //| t.print();
  //| uvm_report_info("Received",t.sprint());
  //
  // See <uvm_printer> for information about the printer API.

  // @uvm-ieee 1800.2-2017 auto 5.3.6.3
  extern virtual function void do_print (uvm_printer printer);


  // Function -- NODOCS -- convert2string
  //
  // This virtual function is a user-definable hook, called directly by the
  // user, that allows users to provide object information in the form of
  // a string. Unlike <sprint>, there is no requirement to use a <uvm_printer>
  // policy object. As such, the format and content of the output is fully
  // customizable, which may be suitable for applications not requiring the
  // consistent formatting offered by the <print>/<sprint>/<do_print>
  // API.
  //
  // Fields declared in <Utility Macros> macros (`uvm_field_*), if used, will
  // not automatically appear in calls to convert2string.
  //
  // An example implementation of convert2string follows.
  // 
  //| class base extends uvm_object;
  //|   string field = "foo";
  //|   virtual function string convert2string();
  //|     convert2string = {"base_field=",field};
  //|   endfunction
  //| endclass
  //| 
  //| class obj2 extends uvm_object;
  //|   string field = "bar";
  //|   virtual function string convert2string();
  //|     convert2string = {"child_field=",field};
  //|   endfunction
  //| endclass
  //| 
  //| class obj extends base;
  //|   int addr = 'h123;
  //|   int data = 'h456;
  //|   bit write = 1;
  //|   obj2 child = new;
  //|   virtual function string convert2string();
  //|      convert2string = {super.convert2string(),
  //|        $sformatf(" write=%0d addr=%8h data=%8h ",write,addr,data),
  //|        child.convert2string()};
  //|   endfunction
  //| endclass
  //
  // Then, to display an object, you could write:
  //
  //| obj o = new;
  //| uvm_report_info("BusMaster",{"Sending:\n ",o.convert2string()});
  //
  // The output will look similar to:
  //
  //| UVM_INFO @ 0: reporter [BusMaster] Sending:
  //|    base_field=foo write=1 addr=00000123 data=00000456 child_field=bar


  // @uvm-ieee 1800.2-2017 auto 5.3.6.4
  extern virtual function string convert2string();


  // Group -- NODOCS -- Recording

  // Function -- NODOCS -- record
  //
  // The ~record~ method deep-records this object's properties according to an
  // optional ~recorder~ policy. The method is not virtual and must not be
  // overloaded. To include additional fields in the record operation, derived
  // classes should override the <do_record> method.
  //
  // The optional ~recorder~ argument specifies the recording policy, which
  // governs how recording takes place. See
  // <uvm_recorder> for information.
  //
  // A simulator's recording mechanism is vendor-specific. By providing access
  // via a common interface, the uvm_recorder policy provides vendor-independent
  // access to a simulator's recording capabilities.

  // @uvm-ieee 1800.2-2017 auto 5.3.7.1
  extern function void record (uvm_recorder recorder=null);


  // Function -- NODOCS -- do_record
  //
  // The ~do_record~ method is the user-definable hook called by the <record>
  // method. A derived class should override this method to include its fields
  // in a record operation.
  //
  // The ~recorder~ argument is policy object for recording this object. A
  // do_record implementation should call the appropriate recorder methods for
  // each of its fields. Vendor-specific recording implementations are
  // encapsulated in the ~recorder~ policy, thereby insulating user-code from
  // vendor-specific behavior. See <uvm_recorder> for more information.
  //
  // A typical implementation is as follows:
  //
  //| class mytype extends uvm_object;
  //|   data_obj data;
  //|   int f1;
  //|   function void do_record (uvm_recorder recorder);
  //|     recorder.record_field("f1", f1, $bits(f1), UVM_DEC);
  //|     recorder.record_object("data", data);
  //|   endfunction

  // @uvm-ieee 1800.2-2017 auto 5.3.7.2
  extern virtual function void do_record (uvm_recorder recorder);


  // Group -- NODOCS -- Copying

  // Function -- NODOCS -- copy
  //
  // The copy makes this object a copy of the specified object.
  //
  // The ~copy~ method is not virtual and should not be overloaded in derived
  // classes. To copy the fields of a derived class, that class should override
  // the <do_copy> method.

  // @uvm-ieee 1800.2-2017 auto 5.3.8.1
  extern function void copy (uvm_object rhs, uvm_copier copier=null);


  // Function -- NODOCS -- do_copy
  //
  // The ~do_copy~ method is the user-definable hook called by the <copy> method.
  // A derived class should override this method to include its fields in a <copy>
  // operation.
  //
  // A typical implementation is as follows:
  //
  //|  class mytype extends uvm_object;
  //|    ...
  //|    int f1;
  //|    function void do_copy (uvm_object rhs);
  //|      mytype rhs_;
  //|      super.do_copy(rhs);
  //|      $cast(rhs_,rhs);
  //|      field_1 = rhs_.field_1;
  //|    endfunction
  //
  // The implementation must call ~super.do_copy~, and it must $cast the rhs
  // argument to the derived type before copying. 

  // @uvm-ieee 1800.2-2017 auto 5.3.8.2
  extern virtual function void do_copy (uvm_object rhs);


  // Group -- NODOCS -- Comparing

  // Function -- NODOCS -- compare
  //
  // Deep compares members of this data object with those of the object provided
  // in the ~rhs~ (right-hand side) argument, returning 1 on a match, 0 otherwise.
  //
  // The ~compare~ method is not virtual and should not be overloaded in derived
  // classes. To compare the fields of a derived class, that class should
  // override the <do_compare> method.
  //
  // The optional ~comparer~ argument specifies the comparison policy. It allows
  // you to control some aspects of the comparison operation. It also stores the
  // results of the comparison, such as field-by-field miscompare information
  // and the total number of miscompares. If a compare policy is not provided,
  // then the global ~uvm_default_comparer~ policy is used. See <uvm_comparer> 
  // for more information.

  // @uvm-ieee 1800.2-2017 auto 5.3.9.1
  extern function bit compare (uvm_object rhs, uvm_comparer comparer=null);


  // Function -- NODOCS -- do_compare
  //
  // The ~do_compare~ method is the user-definable hook called by the <compare>
  // method. A derived class should override this method to include its fields
  // in a compare operation. It should return 1 if the comparison succeeds, 0
  // otherwise.
  //
  // A typical implementation is as follows:
  //
  //|  class mytype extends uvm_object;
  //|    ...
  //|    int f1;
  //|    virtual function bit do_compare (uvm_object rhs,uvm_comparer comparer);
  //|      mytype rhs_;
  //|      do_compare = super.do_compare(rhs,comparer);
  //|      $cast(rhs_,rhs);
  //|      do_compare &= comparer.compare_field_int("f1", f1, rhs_.f1);
  //|    endfunction
  //
  // A derived class implementation must call ~super.do_compare()~ to ensure its
  // base class' properties, if any, are included in the comparison. Also, the
  // rhs argument is provided as a generic uvm_object. Thus, you must ~$cast~ it
  // to the type of this object before comparing. 
  //
  // The actual comparison should be implemented using the uvm_comparer object
  // rather than direct field-by-field comparison. This enables users of your
  // class to customize how comparisons are performed and how much miscompare
  // information is collected. See uvm_comparer for more details.

  // @uvm-ieee 1800.2-2017 auto 5.3.9.2
  extern virtual function bit do_compare (uvm_object  rhs,
                                          uvm_comparer comparer);

  // Group -- NODOCS -- Packing

  // Function -- NODOCS -- pack

  // @uvm-ieee 1800.2-2017 auto 5.3.10.1
  extern function int pack (ref bit bitstream[],
                            input uvm_packer packer=null);

  // Function -- NODOCS -- pack_bytes

  // @uvm-ieee 1800.2-2017 auto 5.3.10.1
  extern function int pack_bytes (ref byte unsigned bytestream[],
                                  input uvm_packer packer=null);

  // Function -- NODOCS -- pack_ints
  //
  // The pack methods bitwise-concatenate this object's properties into an array
  // of bits, bytes, or ints. The methods are not virtual and must not be
  // overloaded. To include additional fields in the pack operation, derived
  // classes should override the <do_pack> method.
  //
  // The optional ~packer~ argument specifies the packing policy, which governs
  // the packing operation. If a packer policy is not provided, the global
  // <uvm_default_packer> policy is used. See <uvm_packer> for more information.
  //
  // The return value is the total number of bits packed into the given array.
  // Use the array's built-in ~size~ method to get the number of bytes or ints
  // consumed during the packing process.

  // @uvm-ieee 1800.2-2017 auto 5.3.10.1
  extern function int pack_ints (ref int unsigned intstream[],
                                 input uvm_packer packer=null);
  
  // @uvm-ieee 1800.2-2017 auto 5.3.10.1
  extern function int pack_longints (ref longint unsigned longintstream[],
                                     input uvm_packer packer=null);
  
  
  // Function -- NODOCS -- do_pack
  //
  // The ~do_pack~ method is the user-definable hook called by the <pack> methods.
  // A derived class should override this method to include its fields in a pack
  // operation.
  //
  // The ~packer~ argument is the policy object for packing. The policy object
  // should be used to pack objects. 
  //
  // A typical example of an object packing itself is as follows
  //
  //|  class mysubtype extends mysupertype;
  //|    ...
  //|    shortint myshort;
  //|    obj_type myobj;
  //|    byte myarray[];
  //|    ...
  //|    function void do_pack (uvm_packer packer);
  //|      super.do_pack(packer); // pack mysupertype properties
  //|      packer.pack_field_int(myarray.size(), 32);
  //|      foreach (myarray)
  //|        packer.pack_field_int(myarray[index], 8);
  //|      packer.pack_field_int(myshort, $bits(myshort));
  //|      packer.pack_object(myobj);
  //|    endfunction
  //
  // The implementation must call ~super.do_pack~ so that base class properties
  // are packed as well.
  //
  // If your object contains dynamic data (object, string, queue, dynamic array,
  // or associative array), and you intend to unpack into an equivalent data
  // structure when unpacking, you must include meta-information about the
  // dynamic data when packing as follows.
  //
  //  - For queues, dynamic arrays, or associative arrays, pack the number of
  //    elements in the array in the 32 bits immediately before packing
  //    individual elements, as shown above.
  //
  //  - For string data types, append a zero byte after packing the string
  //    contents.
  //
  //  - For objects, pack 4 bits immediately before packing the object. For ~null~
  //    objects, pack 4'b0000. For non-~null~ objects, pack 4'b0001.
  //
  // When the `uvm_field_* macros are used, 
  // <Utility and Field Macros for Components and Objects>,
  // the above meta information is included.
  //
  // Packing order does not need to match declaration order. However, unpacking
  // order must match packing order.

  // @uvm-ieee 1800.2-2017 auto 5.3.10.2
  extern virtual function void do_pack (uvm_packer packer);


  // Group -- NODOCS -- Unpacking

  // Function -- NODOCS -- unpack

  // @uvm-ieee 1800.2-2017 auto 5.3.11.1
  extern function int unpack (ref   bit        bitstream[],
                              input uvm_packer packer=null);

  // Function -- NODOCS -- unpack_bytes

  // @uvm-ieee 1800.2-2017 auto 5.3.11.1
  extern function int unpack_bytes (ref byte unsigned bytestream[],
                                    input uvm_packer packer=null);
  
  // Function -- NODOCS -- unpack_ints
  //
  // The unpack methods extract property values from an array of bits, bytes, or
  // ints. The method of unpacking ~must~ exactly correspond to the method of
  // packing. This is assured if (a) the same ~packer~ policy is used to pack
  // and unpack, and (b) the order of unpacking is the same as the order of
  // packing used to create the input array.
  //
  // The unpack methods are fixed (non-virtual) entry points that are directly
  // callable by the user. To include additional fields in the <unpack>
  // operation, derived classes should override the <do_unpack> method.
  //
  // The optional ~packer~ argument specifies the packing policy, which governs
  // both the pack and unpack operation. If a packer policy is not provided,
  // then the global ~uvm_default_packer~ policy is used. See uvm_packer for
  // more information.
  //
  // The return value is the actual number of bits unpacked from the given array.
  
  // @uvm-ieee 1800.2-2017 auto 5.3.11.1
  extern function int unpack_ints (ref   int unsigned intstream[],
                                   input uvm_packer packer=null);

  // @uvm-ieee 1800.2-2017 auto 5.3.11.1
  extern function int unpack_longints (ref   longint unsigned longintstream[],
                                       input uvm_packer packer=null);



  // Function -- NODOCS -- do_unpack
  //
  // The ~do_unpack~ method is the user-definable hook called by the <unpack>
  // method. A derived class should override this method to include its fields
  // in an unpack operation.
  //
  // The ~packer~ argument is the policy object for both packing and unpacking.
  // It must be the same packer used to pack the object into bits. Also,
  // do_unpack must unpack fields in the same order in which they were packed.
  // See <uvm_packer> for more information.
  //
  // The following implementation corresponds to the example given in do_pack.
  //
  //|  function void do_unpack (uvm_packer packer);
  //|   int sz;
  //|    super.do_unpack(packer); // unpack super's properties
  //|    sz = packer.unpack_field_int(myarray.size(), 32);
  //|    myarray.delete();
  //|    for(int index=0; index<sz; index++)
  //|      myarray[index] = packer.unpack_field_int(8);
  //|    myshort = packer.unpack_field_int($bits(myshort));
  //|    packer.unpack_object(myobj);
  //|  endfunction
  //
  // If your object contains dynamic data (object, string, queue, dynamic array,
  // or associative array), and you intend to <unpack> into an equivalent data
  // structure, you must have included meta-information about the dynamic data
  // when it was packed. 
  //
  // - For queues, dynamic arrays, or associative arrays, unpack the number of
  //   elements in the array from the 32 bits immediately before unpacking
  //   individual elements, as shown above.
  //
  // - For string data types, unpack into the new string until a ~null~ byte is
  //   encountered.
  //
  // - For objects, unpack 4 bits into a byte or int variable. If the value
  //   is 0, the target object should be set to ~null~ and unpacking continues to
  //   the next property, if any. If the least significant bit is 1, then the
  //   target object should be allocated and its properties unpacked.

  // @uvm-ieee 1800.2-2017 auto 5.3.11.2
  extern virtual function void do_unpack (uvm_packer packer);

  // @uvm-ieee 1800.2-2017 auto 5.3.13.1
  extern virtual function void do_execute_op ( uvm_field_op op);


  // Group -- NODOCS -- Configuration
`ifdef UVM_ENABLE_DEPRECATED_API

  // Function -- NODOCS -- set_int_local

  extern virtual function void  set_int_local    (string      field_name,
                                                  uvm_bitstream_t value,
                                                  bit         recurse=1);

  // Function -- NODOCS -- set_string_local

  extern virtual function void  set_string_local (string field_name,
                                                  string value,
                                                  bit    recurse=1);

  // Function -- NODOCS -- set_object_local
  //
  // These methods provide write access to integral, string, and 
  // uvm_object-based properties indexed by a ~field_name~ string. The object
  // designer choose which, if any, properties will be accessible, and overrides
  // the appropriate methods depending on the properties' types. For objects,
  // the optional ~clone~ argument specifies whether to clone the ~value~
  // argument before assignment.
  //
  // The global <uvm_is_match> function is used to match the field names, so
  // ~field_name~ may contain wildcards.
  //
  // An example implementation of all three methods is as follows.
  //
  //| class mytype extends uvm_object;
  //|
  //|   local int myint;
  //|   local byte mybyte;
  //|   local shortint myshort; // no access
  //|   local string mystring;
  //|   local obj_type myobj;
  //| 
  //|   // provide access to integral properties
  //|   function void set_int_local(string field_name, uvm_bitstream_t value);
  //|     if (uvm_is_match (field_name, "myint"))
  //|       myint = value;
  //|     else if (uvm_is_match (field_name, "mybyte"))
  //|       mybyte = value;
  //|   endfunction
  //| 
  //|   // provide access to string properties
  //|   function void set_string_local(string field_name, string value);
  //|     if (uvm_is_match (field_name, "mystring"))
  //|       mystring = value;
  //|   endfunction
  //| 
  //|   // provide access to sub-objects
  //|   function void set_object_local(string field_name, uvm_object value,
  //|                                  bit clone=1);
  //|     if (uvm_is_match (field_name, "myobj")) begin
  //|       if (value != null) begin
  //|         obj_type tmp;
  //|         // if provided value is not correct type, produce error
  //|         if (!$cast(tmp, value) )
  //|           /* error */
  //|         else begin
  //|           if(clone) 
  //|             $cast(myobj, tmp.clone());
  //|           else
  //|             myobj = tmp;
  //|         end
  //|       end
  //|       else
  //|         myobj = null; // value is null, so simply assign null to myobj
  //|     end
  //|   endfunction
  //|   ...
  //
  // Although the object designer implements these methods to provide outside
  // access to one or more properties, they are intended for internal use (e.g.,
  // for command-line debugging and auto-configuration) and should not be called
  // directly by the user.

  extern virtual function void  set_object_local (string      field_name,
                                                  uvm_object  value,
                                                  bit         clone=1,
                                                  bit         recurse=1);

`endif // UVM_ENABLE_DEPRECATED_API
 
  // @uvm-ieee 1800.2-2017 auto 5.3.12
  extern virtual function void  set_local(uvm_resource_base rsrc) ;

`ifdef UVM_ENABLE_DEPRECATED_API
  // Implementation artifact
  uvm_resource_base m_set_local_rsrc;
`endif
  
  //---------------------------------------------------------------------------
  //                 **** Internal Methods and Properties ***
  //                           Do not use directly
  //---------------------------------------------------------------------------

  extern local function void m_pack        (inout uvm_packer packer);
  extern local function void m_unpack_pre  (inout uvm_packer packer);
  extern local function int m_unpack_post (uvm_packer packer);
  extern virtual function void m_unsupported_set_local(uvm_resource_base rsrc);

  // The print_matches bit causes an informative message to be printed
  // when a field is set using one of the set methods.

  local string m_leaf_name;

  local int m_inst_id;
  static protected int m_inst_count;

  extern virtual function void __m_uvm_field_automation (uvm_object tmp_data__,  
                                                   uvm_field_flag_t what__, 
                                                   string           str__);

  extern protected virtual function uvm_report_object m_get_report_object();

endclass

//------------------------------------------------------------------------------
// IMPLEMENTATION
//------------------------------------------------------------------------------

// new
// ---

function uvm_object::new (string name="");

  m_inst_id = m_inst_count++;
  m_leaf_name = name;
endfunction

// get_uvm_seeding
// ------

function bit uvm_object::get_uvm_seeding();
  uvm_coreservice_t cs = uvm_coreservice_t::get();
  return cs.get_uvm_seeding();
endfunction

// set_uvm_seeding
// ------

function void uvm_object::set_uvm_seeding(bit enable);
  uvm_coreservice_t cs = uvm_coreservice_t::get();
  cs.set_uvm_seeding(enable);
endfunction

// reseed
// ------

function void uvm_object::reseed ();
  if(get_uvm_seeding())
    this.srandom(uvm_create_random_seed(get_type_name(), get_full_name()));
endfunction


// get type
// --------

function uvm_object_wrapper uvm_object::get_type();
  uvm_report_error("NOTYPID", "get_type not implemented in derived class.", UVM_NONE);
  return null;
endfunction


// get inst_id
// -----------

function int uvm_object::get_inst_id();
  return m_inst_id;
endfunction


// get_object_type
// ---------------

function uvm_object_wrapper uvm_object::get_object_type();
  uvm_coreservice_t cs = uvm_coreservice_t::get();                                                     
  uvm_factory factory=cs.get_factory();
  if(get_type_name() == "<unknown>") return null;
  return factory.find_wrapper_by_name(get_type_name());
endfunction


// get inst_count
// --------------

function int uvm_object::get_inst_count();
  return m_inst_count;
endfunction


// get_name
// --------

function string uvm_object::get_name ();
  return m_leaf_name;
endfunction


// get_full_name
// -------------

function string uvm_object::get_full_name ();
  return get_name();
endfunction


// set_name
// --------

function void uvm_object::set_name (string name);
  m_leaf_name = name;
endfunction


// print 
// -----
 
function void uvm_object::print(uvm_printer printer=null);
  if (printer==null) printer = uvm_printer::get_default();
  $fwrite(printer.get_file(),sprint(printer)); 
endfunction


// sprint
// ------

function string uvm_object::sprint(uvm_printer printer=null);
  string name;

  if(printer==null) printer = uvm_printer::get_default();
  if (printer.get_active_object_depth() == 0) begin
    printer.flush() ;
    name  = printer.get_root_enabled() ? get_full_name() : get_name();
  end
  else begin
    name  = get_name();
  end
  
  printer.print_object(name,this);
  
  return printer.emit();

endfunction


// convert2string (virtual)
// --------------

function string uvm_object::convert2string();
  return "";
endfunction

`ifdef UVM_ENABLE_DEPRECATED_API
// set_int_local
// -------------

function void  uvm_object::set_int_local (string      field_name,
                                          uvm_bitstream_t value,
                                          bit         recurse=1);
  uvm_field_op field_op = uvm_field_op::m_get_available_op();
  uvm_resource_base rsrc_base  = m_set_local_rsrc;
  if (rsrc_base == null) begin
    uvm_resource#(uvm_bitstream_t) rsrc = new(field_name);
    rsrc.write(value);
    rsrc_base = rsrc;
  end
  field_op.set(UVM_SET, null, rsrc_base);
  do_execute_op(field_op);
  field_op.m_recycle();
  m_set_local_rsrc = null;
endfunction


// set_object_local
// ----------------

function void  uvm_object::set_object_local (string     field_name,
                                             uvm_object value,
                                             bit        clone=1,
                                             bit        recurse=1);
  uvm_field_op field_op = uvm_field_op::m_get_available_op();
  uvm_resource_base rsrc_base  = m_set_local_rsrc;
  if (rsrc_base == null) begin
    uvm_resource#(uvm_object) rsrc  = new(field_name);
    if (clone && (value != null)) begin
      uvm_object cc  = value.clone();
      if (cc != null) cc.set_name(field_name);
      rsrc.write(cc);
    end
    else
      rsrc.write(value);
    rsrc_base = rsrc;
  end
  field_op.set(UVM_SET, null, rsrc_base);
  do_execute_op(field_op);
  field_op.m_recycle();
  m_set_local_rsrc = null;
endfunction


// set_string_local
// ----------------
function void  uvm_object::set_string_local (string field_name,
                                             string value,
                                             bit    recurse=1);
                                             
  uvm_field_op field_op = uvm_field_op::m_get_available_op();
  uvm_resource_base rsrc_base  = m_set_local_rsrc;
  if (rsrc_base == null) begin
    uvm_resource#(string) rsrc = new(field_name);
    rsrc.write(value);
    rsrc_base = rsrc;
  end
  field_op.set(UVM_SET, null, rsrc_base);
  do_execute_op(field_op);
  field_op.m_recycle();
  m_set_local_rsrc = null;
endfunction
`endif // UVM_ENABLE_DEPRECATED_API


// set_local
// ----------------

function void  uvm_object::set_local(uvm_resource_base rsrc) ;
  if(rsrc==null) begin
    return ;
  end
  else begin
`ifdef UVM_ENABLE_DEPRECATED_API
    bit success;
    uvm_object obj;
    m_set_local_rsrc = rsrc;
    `uvm_resource_read(success,
                       rsrc,
                       uvm_object,
                       obj,
                       this)
    if (success) begin
      set_object_local(rsrc.get_name(), obj, 0);
    end
    else begin
      string str;
      `uvm_resource_read(success,
                         rsrc,
                         string,
                         str,
                         this)
      if (success) begin
        set_string_local(rsrc.get_name(), str);
      end
      else begin
        uvm_bitstream_t bits;
        `uvm_resource_builtin_int_read(success,
                                       rsrc,
                                       bits,
                                       this)
        if (success) begin
          set_int_local(rsrc.get_name(), bits);
        end
      end
    end
    if (!success)
`endif
      
    begin
      uvm_field_op op;
      op  = uvm_field_op::m_get_available_op();
      op.set(UVM_SET,null,rsrc);
      this.do_execute_op(op);
      op.m_recycle();
    end
  end 
endfunction


// m_unsupported_set_local
// ----------------------
//

function void uvm_object::m_unsupported_set_local(uvm_resource_base rsrc);

  return;
endfunction


// clone
// -----

function uvm_object uvm_object::clone();
  uvm_object tmp;
  tmp = this.create(get_name());
  if(tmp == null)
    uvm_report_warning("CRFLD", $sformatf("The create method failed for %s,  object cannot be cloned", get_name()), UVM_NONE);
  else
    tmp.copy(this);
  return(tmp);
endfunction


// copy
// ----

function void uvm_object::copy (uvm_object rhs, uvm_copier copier=null);
uvm_coreservice_t coreservice ;
uvm_copier m_copier;

  if(rhs == null)  begin
	`uvm_error("OBJ/COPY","Passing a null object to be copied")
	return;
  end

  if(copier == null) begin
	coreservice = uvm_coreservice_t::get() ;
       m_copier = coreservice.get_default_copier() ;
 end
   else 
	m_copier = copier;
  // Copier is available. check depth as and flush it. Sec 5.3.8.1
	if(m_copier.get_active_object_depth() == 0) 
		m_copier.flush();

  m_copier.copy_object(this,rhs);
endfunction


// do_copy
// -------

function void uvm_object::do_copy (uvm_object rhs);
  return;
endfunction


// compare
// -------

function bit  uvm_object::compare (uvm_object rhs,
                                   uvm_comparer comparer=null);
  if (comparer == null) comparer = uvm_comparer::get_default();
  if (comparer.get_active_object_depth() == 0) 
    comparer.flush() ;
  compare = comparer.compare_object(get_name(),this,rhs);

endfunction


// do_compare
// ----------

function bit  uvm_object::do_compare (uvm_object rhs,
                                      uvm_comparer comparer);
  return 1;
endfunction


// __m_uvm_field_automation
// ------------------

function void uvm_object::__m_uvm_field_automation (uvm_object tmp_data__,
                                              uvm_field_flag_t what__,
                                              string           str__ );
  return;
endfunction



// do_print (virtual override)
// ------------

function void uvm_object::do_print(uvm_printer printer);
  return;
endfunction


// m_pack
// ------

function void uvm_object::m_pack (inout uvm_packer packer);
  if (packer == null)
    packer  = uvm_packer::get_default();
  if(packer.get_active_object_depth() == 0) 
    packer.flush(); 
  packer.pack_object(this);
  
endfunction
  

// pack
// ---- 
  
function int uvm_object::pack (ref bit bitstream [],
                               input uvm_packer packer =null );
  m_pack(packer);
  packer.get_packed_bits(bitstream);
  return packer.get_packed_size();
endfunction

// pack_bytes
// ----------

function int uvm_object::pack_bytes (ref byte unsigned bytestream [],
                                     input uvm_packer packer=null );
  m_pack(packer);
  packer.get_packed_bytes(bytestream);
  return packer.get_packed_size();
endfunction


// pack_ints
// ---------

function int uvm_object::pack_ints (ref int unsigned intstream [],
                                    input uvm_packer packer=null );
  m_pack(packer);
  packer.get_packed_ints(intstream);
  return packer.get_packed_size();
endfunction

// pack_longints
// ---------

function int uvm_object::pack_longints (ref longint unsigned longintstream [],
                                        input uvm_packer packer=null );
  m_pack(packer);
  packer.get_packed_longints(longintstream);
  return packer.get_packed_size();
endfunction


// do_pack
// -------

function void uvm_object::do_pack (uvm_packer packer );
  if (packer == null)
    `uvm_error("UVM/OBJ/PACK/NULL", "uvm_object::do_pack called with null packer!")
  return;
endfunction


// m_unpack_pre
// ------------
  
function void uvm_object::m_unpack_pre (inout uvm_packer packer);
  if (packer == null)
    packer  = uvm_packer::get_default();
  if(packer.get_active_object_depth() == 0) 
    packer.flush(); 

endfunction
  

// m_unpack_post
// -------------

function int uvm_object::m_unpack_post (uvm_packer packer);
  int size_before_unpack = packer.get_packed_size();
  packer.unpack_object(this);
  return size_before_unpack - packer.get_packed_size();
endfunction


// unpack
// ------

function int uvm_object::unpack (ref    bit        bitstream [],
                                 input  uvm_packer packer=null);
  m_unpack_pre(packer);
  packer.set_packed_bits(bitstream);
  return m_unpack_post(packer);
endfunction


// unpack_bytes
// ------------

function int uvm_object::unpack_bytes (ref    byte unsigned bytestream [],
                                       input  uvm_packer packer=null);
  m_unpack_pre(packer);
  packer.set_packed_bytes(bytestream);
  return m_unpack_post(packer);
endfunction


// unpack_ints
// -----------
  
function int uvm_object::unpack_ints (ref    int unsigned intstream [],
                                      input  uvm_packer packer=null);
  m_unpack_pre(packer);
  packer.set_packed_ints(intstream);
  return m_unpack_post(packer);
endfunction

// unpack_longints
// -----------
  
function int uvm_object::unpack_longints (ref    longint unsigned longintstream [],
                                          input  uvm_packer packer=null);
  m_unpack_pre(packer);
  packer.set_packed_longints(longintstream);
  return m_unpack_post(packer);
endfunction


function void uvm_object::do_execute_op ( uvm_field_op op);

endfunction


// do_unpack
// ---------

function void uvm_object::do_unpack (uvm_packer packer);
  if (packer == null)
    `uvm_error("UVM/OBJ/UNPACK/NULL", "uvm_object::do_unpack called with null packer!")
  return;
endfunction


// record
// ------

function void uvm_object::record (uvm_recorder recorder=null);

  if(recorder == null)
    return;

  recorder.record_object(get_name(), this);
endfunction


// do_record (virtual)
// ---------

function void uvm_object::do_record (uvm_recorder recorder);
  return;
endfunction


// m_get_report_object
// -------------------

function uvm_report_object uvm_object::m_get_report_object();
  return null;
endfunction
