//
//------------------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2010-2014 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2011 AMD
// Copyright 2014-2018 NVIDIA Corporation
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

// Title -- NODOCS -- Pool Classes
// This section defines the <uvm_pool #(KEY, T)> class and derivative.

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_pool #(KEY,T)
//
//------------------------------------------------------------------------------
// Implements a class-based dynamic associative array. Allows sparse arrays to
// be allocated on demand, and passed and stored by reference.
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 11.2.1
class uvm_pool #(type KEY=int, T=uvm_void) extends uvm_object;

  typedef uvm_pool #(KEY,T) this_type;

  static protected this_type m_global_pool;
  protected T pool[KEY];

  `uvm_object_param_utils(uvm_pool #(KEY,T))
  `uvm_type_name_decl("uvm_pool")
  
  // Function -- NODOCS -- new
  //
  // Creates a new pool with the given ~name~.

  // @uvm-ieee 1800.2-2017 auto 11.2.2.1
  function new (string name="");
    super.new(name);
  endfunction


  // Function -- NODOCS -- get_global_pool
  //
  // Returns the singleton global pool for the item type, T. 
  //
  // This allows items to be shared amongst components throughout the
  // verification environment.

  static function this_type get_global_pool ();
    if (m_global_pool==null)
      m_global_pool = new("pool");
    return m_global_pool;
  endfunction


  // Function -- NODOCS -- get_global
  //
  // Returns the specified item instance from the global item pool. 

  // @uvm-ieee 1800.2-2017 auto 11.2.2.3
  static function T get_global (KEY key);
    this_type gpool;
    gpool = get_global_pool(); 
    return gpool.get(key);
  endfunction


  // Function -- NODOCS -- get
  //
  // Returns the item with the given ~key~.
  //
  // If no item exists by that key, a new item is created with that key
  // and returned.

  // @uvm-ieee 1800.2-2017 auto 11.2.2.4
  virtual function T get (KEY key);
    if (!pool.exists(key)) begin
      T default_value;
      pool[key] = default_value;
    end
    return pool[key];
  endfunction
  

  // Function -- NODOCS -- add
  //
  // Adds the given (~key~, ~item~) pair to the pool. If an item already
  // exists at the given ~key~ it is overwritten with the new ~item~.

  // @uvm-ieee 1800.2-2017 auto 11.2.2.5
  virtual function void add (KEY key, T item);
    pool[key] = item;
  endfunction
  

  // Function -- NODOCS -- num
  //
  // Returns the number of uniquely keyed items stored in the pool.

  // @uvm-ieee 1800.2-2017 auto 11.2.2.6
  virtual function int num ();
    return pool.num();
  endfunction


  // Function -- NODOCS -- delete
  //
  // Removes the item with the given ~key~ from the pool.

  // @uvm-ieee 1800.2-2017 auto 11.2.2.7
  virtual function void delete (KEY key);
    if (!exists(key)) begin
      uvm_report_warning("POOLDEL",
        $sformatf("delete: pool key doesn't exist. Ignoring delete request"));
      return;
    end
    pool.delete(key);
  endfunction


  // Function -- NODOCS -- exists
  //
  // Returns 1 if an item with the given ~key~ exists in the pool,
  // 0 otherwise.

  // @uvm-ieee 1800.2-2017 auto 11.2.2.8
  virtual function int exists (KEY key);
    return pool.exists(key);
  endfunction


  // Function -- NODOCS -- first
  //
  // Returns the key of the first item stored in the pool.
  //
  // If the pool is empty, then ~key~ is unchanged and 0 is returned.
  //
  // If the pool is not empty, then ~key~ is key of the first item
  // and 1 is returned.

  // @uvm-ieee 1800.2-2017 auto 11.2.2.9
  virtual function int first (ref KEY key);
    return pool.first(key);
  endfunction


  // Function -- NODOCS -- last
  //
  // Returns the key of the last item stored in the pool.
  //
  // If the pool is empty, then 0 is returned and ~key~ is unchanged. 
  //
  // If the pool is not empty, then ~key~ is set to the last key in
  // the pool and 1 is returned.

  // @uvm-ieee 1800.2-2017 auto 11.2.2.10
  virtual function int last (ref KEY key);
    return pool.last(key);
  endfunction


  // Function -- NODOCS -- next
  //
  // Returns the key of the next item in the pool.
  //
  // If the input ~key~ is the last key in the pool, then ~key~ is
  // left unchanged and 0 is returned. 
  //
  // If a next key is found, then ~key~ is updated with that key
  // and 1 is returned.

  // @uvm-ieee 1800.2-2017 auto 11.2.2.11
  virtual function int next (ref KEY key);
    return pool.next(key);
  endfunction


  // Function -- NODOCS -- prev
  //
  // Returns the key of the previous item in the pool.
  //
  // If the input ~key~ is the first key in the pool, then ~key~ is
  // left unchanged and 0 is returned. 
  //
  // If a previous key is found, then ~key~ is updated with that key
  // and 1 is returned.

  // @uvm-ieee 1800.2-2017 auto 11.2.2.12
  virtual function int prev (ref KEY key);
    return pool.prev(key);
  endfunction

  virtual function void do_copy (uvm_object rhs);
    this_type p;
    KEY key;
    super.do_copy(rhs);
    if (rhs==null || !$cast(p, rhs))
      return;
    pool = p.pool;
  endfunction

  virtual function void do_print (uvm_printer printer);
    string v;
    int cnt;
    string item;
    KEY key;
    printer.print_array_header("pool",pool.num(),"aa_object_string");
    if (pool.first(key))
      do begin
        item.itoa(cnt);
        item = {"[-key",item,"--]"};
        $swrite(v,pool[key]);
        printer.print_generic(item,"",-1,v,"[");
      end
      while (pool.next(key));
    printer.print_array_footer();
  endfunction

endclass


//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_object_string_pool #(T)
//
//------------------------------------------------------------------------------
// This provides a specialization of the generic <uvm_pool #(KEY,T)> class for
// an associative array of <uvm_object>-based objects indexed by string. 
// Specializations of this class include the ~uvm_event_pool~ (a
// uvm_object_string_pool storing ~uvm_event#(uvm_object)~) and
// ~uvm_barrier_pool~ (a uvm_obejct_string_pool storing <uvm_barrier>).
//------------------------------------------------------------------------------

class uvm_object_string_pool #(type T=uvm_object) extends uvm_pool #(string,T);

  typedef uvm_object_string_pool #(T) this_type;
  static protected this_type m_global_pool;

  `uvm_object_param_utils(uvm_object_string_pool#(T))
  `uvm_type_name_decl("uvm_obj_str_pool")

  // Function -- NODOCS -- new
  //
  // Creates a new pool with the given ~name~.

  function new (string name="");
    super.new(name);
  endfunction

  // Function -- NODOCS -- get_global_pool
  //
  // Returns the singleton global pool for the item type, T. 
  //
  // This allows items to be shared amongst components throughout the
  // verification environment.

  static function this_type get_global_pool ();
    if (m_global_pool==null)
      m_global_pool = new("global_pool");
    return m_global_pool;
  endfunction


  // Function -- NODOCS -- get_global
  //
  // Returns the specified item instance from the global item pool. 

  static function T get_global (string key);
    this_type gpool;
    gpool = get_global_pool(); 
    return gpool.get(key);
  endfunction


  // Function -- NODOCS -- get
  //
  // Returns the object item at the given string ~key~.
  //
  // If no item exists by the given ~key~, a new item is created for that key
  // and returned.

  virtual function T get (string key);
    if (!pool.exists(key))
      pool[key] = new (key);
    return pool[key];
  endfunction
  

  // Function -- NODOCS -- delete
  //
  // Removes the item with the given string ~key~ from the pool.

  virtual function void delete (string key);
    if (!exists(key)) begin
      uvm_report_warning("POOLDEL",
        $sformatf("delete: key '%s' doesn't exist", key));
      return;
    end
    pool.delete(key);
  endfunction


  // Function- do_print

  virtual function void do_print (uvm_printer printer);
    string key;
    printer.print_array_header("pool",pool.num(),"aa_object_string");
    if (pool.first(key))
      do
        printer.print_object({"[",key,"]"}, pool[key],"[");
      while (pool.next(key));
    printer.print_array_footer();
  endfunction

endclass


typedef class uvm_barrier;
typedef class uvm_event;

typedef uvm_object_string_pool #(uvm_barrier) uvm_barrier_pool /* @uvm-ieee 1800.2-2017 auto 10.4.2.1*/   ;
typedef uvm_object_string_pool #(uvm_event#(uvm_object)) uvm_event_pool /* @uvm-ieee 1800.2-2017 auto 10.4.1.1*/   ;
