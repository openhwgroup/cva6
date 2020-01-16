//----------------------------------------------------------------------
// Copyright 2010-2011 Paradigm Works
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2015 Analog Devices, Inc.
// Copyright 2017 Intel Corporation
// Copyright 2010-2014 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2011 AMD
// Copyright 2014-2018 NVIDIA Corporation
// Copyright 2017 Cisco Systems, Inc.
// Copyright 2011 Cypress Semiconductor Corp.
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
// Title -- NODOCS -- UVM Resource Database
//
// Topic: Intro
//
// The <uvm_resource_db> class provides a convenience interface for
// the resources facility.  In many cases basic operations such as
// creating and setting a resource or getting a resource could take
// multiple lines of code using the interfaces in <uvm_resource_base> or
// <uvm_resource#(T)>.  The convenience layer in <uvm_resource_db>
// reduces many of those operations to a single line of code.
//
// If the run-time ~+UVM_RESOURCE_DB_TRACE~ command line option is
// specified, all resource DB accesses (read and write) are displayed.
//----------------------------------------------------------------------

typedef class uvm_resource_db_options;
typedef class uvm_cmdline_processor;


// @uvm-ieee 1800.2-2017 auto C.3.2.1
class uvm_resource_db #(type T=uvm_object);

  typedef uvm_resource #(T) rsrc_t;

  protected function new();
  endfunction

  // function -- NODOCS -- get_by_type
  //
  // Get a resource by type.  The type is specified in the db
  // class parameter so the only argument to this function is the
  // ~scope~.

  // @uvm-ieee 1800.2-2017 auto C.3.2.2.5
  static function rsrc_t get_by_type(string scope);
    uvm_resource_pool rp = uvm_resource_pool::get();
    uvm_resource_base rsrc_base;
    rsrc_t rsrc;
    string msg;
    uvm_resource_base type_handle = rsrc_t::get_type();

    if(type_handle == null)
       return null;

    rsrc_base = rp.get_by_type(scope, type_handle);
    if(!$cast(rsrc, rsrc_base)) begin
      $sformat(msg, "Resource with specified type handle in scope %s was not located", scope);
      `uvm_warning("RSRCNF", msg)
      return null;
    end

    return rsrc;
  endfunction

  // function -- NODOCS -- get_by_name
  //
  // Imports a resource by ~name~.  The first argument is the current 
  // ~scope~ of the resource to be retrieved and the second argument is
  // the ~name~. The ~rpterr~ flag indicates whether or not to generate
  // a warning if no matching resource is found.

  // @uvm-ieee 1800.2-2017 auto C.3.2.2.4
  static function rsrc_t get_by_name(string scope,
                                     string name,
                                     bit rpterr=1);

    uvm_resource_pool rp = uvm_resource_pool::get();
    uvm_resource_base rsrc_base;
    rsrc_t rsrc;
    string msg;

    rsrc_base = rp.get_by_name(scope, name, rsrc_t::get_type(), rpterr);
    if(rsrc_base == null)
      return null;

    if(!$cast(rsrc, rsrc_base)) begin
      if(rpterr) begin
        $sformat(msg, "Resource with name %s in scope %s has incorrect type", name, scope);
        `uvm_warning("RSRCTYPE", msg)
      end
      return null;
    end

    return rsrc;
  endfunction

  // function -- NODOCS -- set_default
  //
  // add a new item into the resources database.  The item will not be
  // written to so it will have its default value. The resource is
  // created using ~name~ and ~scope~ as the lookup parameters.

  // @uvm-ieee 1800.2-2017 auto C.3.2.2.2
  static function rsrc_t set_default(string scope, string name);

    rsrc_t r;
    uvm_resource_pool rp = uvm_resource_pool::get();
    
    r = new(name);
    rp.set_scope(r, scope);
    return r;
  endfunction

  // function- show_msg

  // internal helper function to print resource accesses

  protected static function void m_show_msg(
          input string id,
          input string rtype,
          input string action,
          input string scope,
          input string name,
          input uvm_object accessor,
          input rsrc_t rsrc);

          T foo;
          string msg=`uvm_typename(foo);

          $sformat(msg, "%s scope='%s' name='%s' (type %s) %s accessor=%s = %s",
              rtype,scope,name, msg,action,
              (accessor != null) ? accessor.get_full_name() : "<unknown>",
              rsrc==null?"null (failed lookup)":rsrc.convert2string());

          `uvm_info(id, msg, UVM_LOW)
  endfunction


  // @uvm-ieee 1800.2-2017 auto C.3.2.2.1
  static function void set(input string scope, input string name,
                           T val, input uvm_object accessor = null);

    uvm_resource_pool rp = uvm_resource_pool::get();
    rsrc_t rsrc = new(name);
    rsrc.write(val, accessor);
    rp.set_scope(rsrc, scope);

    if(uvm_resource_db_options::is_tracing())
      m_show_msg("RSRCDB/SET", "Resource","set", scope, name, accessor, rsrc);
  endfunction


  // @uvm-ieee 1800.2-2017 auto C.3.2.2.3
  static function void set_anonymous(input string scope,
                                     T val, input uvm_object accessor = null);

    uvm_resource_pool rp = uvm_resource_pool::get();
    rsrc_t rsrc = new("");
    rsrc.write(val, accessor);
    rp.set_scope(rsrc, scope);

    if(uvm_resource_db_options::is_tracing())
      m_show_msg("RSRCDB/SETANON","Resource", "set", scope, "", accessor, rsrc);
  endfunction

  // function set_override
  //
  // Create a new resource, write ~val~ to it, and set it into the
  // database.  Set it at the beginning of the queue in the type map and
  // the name map so that it will be (currently) the highest priority
  // resource with the specified name and type.

  static function void set_override(input string scope, input string name,
                                    T val, uvm_object accessor = null);

    uvm_resource_pool rp = uvm_resource_pool::get();
    rsrc_t rsrc = new(name);
    rsrc.write(val, accessor);
    rp.set_override(rsrc, scope);

    if(uvm_resource_db_options::is_tracing())
      m_show_msg("RSRCDB/SETOVRD", "Resource","set", scope, name, accessor, rsrc);
  endfunction


    
  // function set_override_type
  //
  // Create a new resource, write ~val~ to it, and set it into the
  // database.  Set it at the beginning of the queue in the type map so
  // that it will be (currently) the highest priority resource with the
  // specified type. It will be normal priority (i.e. at the end of the
  // queue) in the name map.

  static function void set_override_type(input string scope, input string name,
                                         T val, uvm_object accessor = null);

    uvm_resource_pool rp = uvm_resource_pool::get();
    rsrc_t rsrc = new(name);
    rsrc.write(val, accessor);
    rp.set_type_override(rsrc, scope);

    if(uvm_resource_db_options::is_tracing())
      m_show_msg("RSRCDB/SETOVRDTYP","Resource", "set", scope, name, accessor, rsrc);
  endfunction

  // function set_override_name
  //
  // Create a new resource, write ~val~ to it, and set it into the
  // database.  Set it at the beginning of the queue in the name map so
  // that it will be (currently) the highest priority resource with the
  // specified name. It will be normal priority (i.e. at the end of the
  // queue) in the type map.

  static function void set_override_name(input string scope, input string name,
                                  T val, uvm_object accessor = null);

    uvm_resource_pool rp = uvm_resource_pool::get();
    rsrc_t rsrc = new(name);
    rsrc.write(val, accessor);
    rp.set_name_override(rsrc, scope);

    if(uvm_resource_db_options::is_tracing())
      m_show_msg("RSRCDB/SETOVRDNAM","Resource", "set", scope, name, accessor, rsrc);
  endfunction


  // function: read_by_name
  //
  // Locates a resource by name and scope and reads its value. The value is returned through the inout argument
  // val. The return value is a bit that indicates whether or not the read was successful. The accessor is available
  // for an implementation to use for debug purposes only; its value shall have no functional effect on outcome
  // of this method.
  //
  // *This function deviates from IEEE 1800.2-2017 LRM as it defines the <val> argument as inout, whereas the*
  // *LRM defines it as an output.* 
  //
  //|   static function bit read_by_name(input string scope,
  //|                                 input string name,
  //|                                 inout T val, input uvm_object accessor = null);
  //
  //  The implementation treats the argument as inout for cases where a read may fail 
  //  and the value will not change from its original supplied value,

  // @uvm-ieee 1800.2-2017 auto C.3.2.2.6
  static function bit read_by_name(input string scope,
                                   input string name,
                                   inout T val, input uvm_object accessor = null);

    rsrc_t rsrc = get_by_name(scope, name);

    if(uvm_resource_db_options::is_tracing())
      m_show_msg("RSRCDB/RDBYNAM","Resource", "read", scope, name, accessor, rsrc);

    if(rsrc == null)
      return 0;

    val = rsrc.read(accessor);

    return 1;
  
  endfunction

  // function: read_by_type
  //
  // Reads a value by type. The value is returned through the inout argument val. The scope is used for the
  // lookup. The return value is a bit that indicates whether or not the read is successful. The accessor is
  // available for an implementation to use for debug purposes only; its value shall have no functional effect on
  // outcome of this method.
  // 
  // *This function deviates from IEEE 1800.2-2017 LRM as it defines the <val> argument as inout, whereas the*
  // *LRM defines it as an output.* 
  //
  //|    static function bit read_by_type(input string scope,
  //|                                 inout T val,
  //|                                 input uvm_object accessor = null);
  //
  // The implementation treats the argument as inout for cases where a read may fail 
  // and the value will not change from its original supplied value,

  // @uvm-ieee 1800.2-2017 auto C.3.2.2.7
  static function bit read_by_type(input string scope,
                                   inout T val,
                                   input uvm_object accessor = null);
    
    rsrc_t rsrc = get_by_type(scope);

    if(uvm_resource_db_options::is_tracing())
      m_show_msg("RSRCDB/RDBYTYP", "Resource","read", scope, "", accessor, rsrc);

    if(rsrc == null)
      return 0;

    val = rsrc.read(accessor);

    return 1;

  endfunction


  // @uvm-ieee 1800.2-2017 auto C.3.2.2.8
  static function bit write_by_name(input string scope, input string name,
                                    input T val, input uvm_object accessor = null);

    rsrc_t rsrc = get_by_name(scope, name);

    if(uvm_resource_db_options::is_tracing())
      m_show_msg("RSRCDB/WR","Resource", "written", scope, name, accessor, rsrc);

    if(rsrc == null)
      return 0;

    rsrc.write(val, accessor);

    return 1;

  endfunction


  // @uvm-ieee 1800.2-2017 auto C.3.2.2.9
  static function bit write_by_type(input string scope,
                                    input T val, input uvm_object accessor = null);

    rsrc_t rsrc = get_by_type(scope);

    if(uvm_resource_db_options::is_tracing())
      m_show_msg("RSRCDB/WRTYP", "Resource","written", scope, "", accessor, rsrc);

    if(rsrc == null)
      return 0;

    rsrc.write(val, accessor);

    return 1;
  endfunction

  // function -- NODOCS -- dump
  //
  // Dump all the resources in the resource pool. This is useful for
  // debugging purposes.  This function does not use the parameter T, so
  // it will dump the same thing -- the entire database -- no matter the
  // value of the parameter.

  static function void dump();
    uvm_resource_pool rp = uvm_resource_pool::get();
    rp.dump();
  endfunction

endclass


