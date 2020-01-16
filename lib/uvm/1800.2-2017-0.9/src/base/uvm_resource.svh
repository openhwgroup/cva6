//----------------------------------------------------------------------
// Copyright 2010-2011 Paradigm Works
// Copyright 2010-2014 Mentor Graphics Corporation
// Copyright 2015 Analog Devices, Inc.
// Copyright 2014 Semifore
// Copyright 2017 Intel Corporation
// Copyright 2010-2014 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2010-2011 AMD
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2017-2018 Cisco Systems, Inc.
// Copyright 2011-2012 Cypress Semiconductor Corp.
// Copyright 2017-2018 Verific
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
// Class - get_t
//
// Instances of get_t are stored in the history list as a record of each
// get.  Failed gets are indicated with rsrc set to ~null~.  This is part
// of the audit trail facility for resources.
//----------------------------------------------------------------------
class get_t;
  string name;
  string scope;
  uvm_resource_base rsrc;
  time t;
endclass

typedef class uvm_tree_printer ;

//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_resource_pool
//
// The global (singleton) resource database.
//
// Each resource is stored both by primary name and by type handle.  The
// resource pool contains two associative arrays, one with name as the
// key and one with the type handle as the key.  Each associative array
// contains a queue of resources.  Each resource has a regular
// expression that represents the set of scopes over which it is visible.
//
//|  +------+------------+                          +------------+------+
//|  | name | rsrc queue |                          | rsrc queue | type |
//|  +------+------------+                          +------------+------+
//|  |      |            |                          |            |      |
//|  +------+------------+                  +-+-+   +------------+------+
//|  |      |            |                  | | |<--+---*        |  T   |
//|  +------+------------+   +-+-+          +-+-+   +------------+------+
//|  |  A   |        *---+-->| | |           |      |            |      |
//|  +------+------------+   +-+-+           |      +------------+------+
//|  |      |            |      |            |      |            |      |
//|  +------+------------+      +-------+  +-+      +------------+------+
//|  |      |            |              |  |        |            |      |
//|  +------+------------+              |  |        +------------+------+
//|  |      |            |              V  V        |            |      |
//|  +------+------------+            +------+      +------------+------+
//|  |      |            |            | rsrc |      |            |      |
//|  +------+------------+            +------+      +------------+------+
//
// The above diagrams illustrates how a resource whose name is A and
// type is T is stored in the pool.  The pool contains an entry in the
// type map for type T and an entry in the name map for name A.  The
// queues in each of the arrays each contain an entry for the resource A
// whose type is T.  The name map can contain in its queue other
// resources whose name is A which may or may not have the same type as
// our resource A.  Similarly, the type map can contain in its queue
// other resources whose type is T and whose name may or may not be A.
//
// Resources are added to the pool by calling <set>; they are retrieved
// from the pool by calling <get_by_name> or <get_by_type>.  When an object 
// creates a new resource and calls <set> the resource is made available to be
// retrieved by other objects outside of itself; an object gets a
// resource when it wants to access a resource not currently available
// in its scope.
//
// The scope is stored in the resource itself (not in the pool) so
// whether you get by name or by type the resource's visibility is
// the same.
//
// As an auditing capability, the pool contains a history of gets.  A
// record of each get, whether by <get_by_type> or <get_by_name>, is stored 
// in the audit record.  Both successful and failed gets are recorded. At
// the end of simulation, or any time for that matter, you can dump the
// history list.  This will tell which resources were successfully
// located and which were not.  You can use this information
// to determine if there is some error in name, type, or
// scope that has caused a resource to not be located or to be incorrectly
// located (i.e. the wrong resource is located).
//
//----------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto C.2.4.1
class uvm_resource_pool;

  uvm_resource_types::rsrc_q_t rtab [string];
  uvm_resource_types::rsrc_q_t ttab [uvm_resource_base];

  // struct for scope and precedence associated with each resource
  typedef struct { 
     string scope ;
     int unsigned precedence;
  } rsrc_info_t ;
  // table to set/get scope and precedence for resources
  static rsrc_info_t ri_tab [uvm_resource_base];

  get_t get_record [$];  // history of gets

  // @uvm-ieee 1800.2-2017 auto C.2.4.2.1
  function new();
  endfunction


  // Function -- NODOCS -- get
  //
  // Returns the singleton handle to the resource pool

  // @uvm-ieee 1800.2-2017 auto C.2.4.2.2
  static function uvm_resource_pool get();
    uvm_resource_pool t_rp;
    uvm_coreservice_t cs = uvm_coreservice_t::get();
    t_rp = cs.get_resource_pool();
    return t_rp;
  endfunction


  // Function -- NODOCS -- spell_check
  //
  // Invokes the spell checker for a string s.  The universe of
  // correctly spelled strings -- i.e. the dictionary -- is the name
  // map.

  function bit spell_check(string s);
    return uvm_spell_chkr#(uvm_resource_types::rsrc_q_t)::check(rtab, s);
  endfunction

  //-----------
  // Group -- NODOCS -- Set
  //-----------

  // Function -- NODOCS -- set
  //
  // Add a new resource to the resource pool.  The resource is inserted
  // into both the name map and type map so it can be located by
  // either.
  //
  // An object creates a resources and ~sets~ it into the resource pool.
  // Later, other objects that want to access the resource must ~get~ it
  // from the pool
  //
  // Overrides can be specified using this interface.  Either a name
  // override, a type override or both can be specified.  If an
  // override is specified then the resource is entered at the front of
  // the queue instead of at the back.  It is not recommended that users
  // specify the override parameter directly, rather they use the
  // <set_override>, <set_name_override>, or <set_type_override>
  // functions.
  //
`ifdef UVM_ENABLE_DEPRECATED_API
  function void set (uvm_resource_base rsrc, 
                     uvm_resource_types::override_t override = 0);

    // If resource handle is ~null~ then there is nothing to do.
    if (rsrc == null) return ;
    if (override) 
        set_override(rsrc, rsrc.get_scope()) ;
    else
        set_scope(rsrc, rsrc.get_scope()) ; 

  endfunction
`endif //UVM_ENABLE_DEPRECATED_API

  // @uvm-ieee 1800.2-2017 auto C.2.4.3.1
  function void set_scope (uvm_resource_base rsrc, string scope); 

    uvm_resource_types::rsrc_q_t rq;
    string name;
    uvm_resource_base type_handle;
    uvm_resource_base r;
    int unsigned i;

    // If resource handle is ~null~ then there is nothing to do.
    if(rsrc == null) begin
      uvm_report_warning("NULLRASRC", "attempting to set scope of a null resource");
      return;
    end

    // Insert into the name map.  Resources with empty names are
    // anonymous resources and are not entered into the name map
    name = rsrc.get_name();
    if ((name != "") && rtab.exists(name)) begin
      rq = rtab[name];

      for(i = 0; i < rq.size(); i++) begin
        r = rq.get(i);
        if(r == rsrc) begin 
          ri_tab[rsrc].scope = uvm_glob_to_re(scope);
          return ;
        end
      end
    end 

    if (rq == null) 
       rq = new(name);

    // Insert the resource into the queue associated with its name.
    // Insert it with low priority (in the back of queue) .
    rq.push_back(rsrc);

    rtab[name] = rq;

    // Insert into the type map
    type_handle = rsrc.get_type_handle();
    if(ttab.exists(type_handle))
      rq = ttab[type_handle];
    else 
      rq = new();

    // Insert the resource into the queue associated with its type.  
    // Insert it with low priority (in the back of queue) .
    rq.push_back(rsrc);
    ttab[type_handle] = rq;

    // Set the scope of resource. 
    ri_tab[rsrc].scope = uvm_glob_to_re(scope);
    ri_tab[rsrc].precedence = get_default_precedence();

  endfunction


  // Function -- NODOCS -- set_override
  //
  // The resource provided as an argument will be entered into the pool
  // and will override both by name and type.
  // Default value to 'scope' argument is violating 1800.2-2017 LRM, but it
  // is added to make the routine backward compatible

  // @uvm-ieee 1800.2-2017 auto C.2.4.3.2
  function void set_override(uvm_resource_base rsrc, string scope = "");
     string s = scope;
`ifdef UVM_ENABLE_DEPRECATED_API
     if ((scope == "") && rsrc) s = rsrc.get_scope();
`endif //UVM_ENABLE_DEPRECATED_API
     set_scope(rsrc, s);
     set_priority(rsrc, uvm_resource_types::PRI_HIGH);
  endfunction


  // Function -- NODOCS -- set_name_override
  //
  // The resource provided as an argument will entered into the pool
  // using normal precedence in the type map and will override the name.
  // Default value to 'scope' argument is violating 1800.2-2017 LRM, but it
  // is added to make the routine backward compatible

  // @uvm-ieee 1800.2-2017 auto C.2.4.3.3
  function void set_name_override(uvm_resource_base rsrc, string scope = "");
    string s = scope;
`ifdef UVM_ENABLE_DEPRECATED_API
    if ((scope == "") && rsrc) s = rsrc.get_scope();
`endif //UVM_ENABLE_DEPRECATED_API
    set_scope(rsrc, s);
    set_priority_name(rsrc, uvm_resource_types::PRI_HIGH);
  endfunction


  // Function -- NODOCS -- set_type_override
  //
  // The resource provided as an argument will be entered into the pool
  // using normal precedence in the name map and will override the type.
  // Default value to 'scope' argument is violating 1800.2-2017 LRM, but it
  // is added to make the routine backward compatible

  // @uvm-ieee 1800.2-2017 auto C.2.4.3.4
  function void set_type_override(uvm_resource_base rsrc, string scope = "");
    string s = scope;
`ifdef UVM_ENABLE_DEPRECATED_API
    if ((scope == "") && rsrc) s = rsrc.get_scope();
`endif //UVM_ENABLE_DEPRECATED_API
    set_scope(rsrc, s);
    set_priority_type(rsrc, uvm_resource_types::PRI_HIGH);
  endfunction

  
  // @uvm-ieee 1800.2-2017 auto C.2.4.3.5
  virtual function bit get_scope(uvm_resource_base rsrc,
                                 output string scope);

    uvm_resource_types::rsrc_q_t rq;
    string name;
    uvm_resource_base r;
    int unsigned i;

    // If resource handle is ~null~ then there is nothing to do.
    if(rsrc == null) 
      return 0;

    // Search the resouce in the name map.  Resources with empty names are
    // anonymous resources and are not entered into the name map
    name = rsrc.get_name();
    if((name != "") && rtab.exists(name)) begin
      rq = rtab[name];

      for(i = 0; i < rq.size(); i++) begin
        r = rq.get(i);
        if(r == rsrc) begin 
          // Resource is in pool, set the scope 
          scope = ri_tab[rsrc].scope;
          return 1;
        end
      end
    end

    // Resource is not in pool
    scope = "";
    return 0;

  endfunction

  // Function -- NODOCS -- delete
  // 
  // If rsrc exists within the pool, then it is removed from all internal maps. If the rsrc is null, or does not exist
  // within the pool, then the request is silently ignored.

 
  // @uvm-ieee 1800.2-2017 auto C.2.4.3.6
  virtual function void delete ( uvm_resource_base rsrc );
    string name;
    uvm_resource_base type_handle;

    if (rsrc != null) begin
      name = rsrc.get_name();
      if(name != "") begin
        if(rtab.exists(name))
          rtab.delete(name);
      end
      
      type_handle = rsrc.get_type_handle();
      if(ttab.exists(type_handle)) begin
          int q_size = ttab[type_handle].size();
          
          if (q_size == 1)
              ttab.delete(type_handle);
          else begin
              int i;
              for (i=0; i<q_size; i++) begin
                  if (ttab[type_handle].get(i) == rsrc) begin
                      ttab[type_handle].delete(i);
                      break;
                  end
              end              
          end   
      end

      if (ri_tab.exists(rsrc))
         ri_tab.delete(rsrc);
    end    
  endfunction


  // function - push_get_record
  //
  // Insert a new record into the get history list.

  function void push_get_record(string name, string scope,
                                  uvm_resource_base rsrc);
    get_t impt;

    // if auditing is turned off then there is no reason
    // to save a get record
    if(!uvm_resource_options::is_auditing())
      return;

    impt = new();

    impt.name  = name;
    impt.scope = scope;
    impt.rsrc  = rsrc;
    impt.t     = $realtime;

    get_record.push_back(impt);
  endfunction

  // function - dump_get_records
  //
  // Format and print the get history list.

  function void dump_get_records();

    get_t record;
    bit success;
    string qs[$];

    qs.push_back("--- resource get records ---\n");
    foreach (get_record[i]) begin
      record = get_record[i];
      success = (record.rsrc != null);
      qs.push_back($sformatf("get: name=%s  scope=%s  %s @ %0t\n",
               record.name, record.scope,
               ((success)?"success":"fail"),
               record.t));
    end
    `uvm_info("UVM/RESOURCE/GETRECORD",`UVM_STRING_QUEUE_STREAMING_PACK(qs),UVM_NONE)
  endfunction

  //--------------
  // Group -- NODOCS -- Lookup
  //--------------
  //
  // This group of functions is for finding resources in the resource database.  
  //
  // <lookup_name> and <lookup_type> locate the set of resources that
  // matches the name or type (respectively) and is visible in the
  // current scope.  These functions return a queue of resources.
  //
  // <get_highest_precedence> traverse a queue of resources and
  // returns the one with the highest precedence -- i.e. the one whose
  // precedence member has the highest value.
  //
  // <get_by_name> and <get_by_type> use <lookup_name> and <lookup_type>
  // (respectively) and <get_highest_precedence> to find the resource with
  // the highest priority that matches the other search criteria.


  // Function -- NODOCS -- lookup_name
  //
  // Lookup resources by ~name~.  Returns a queue of resources that
  // match the ~name~, ~scope~, and ~type_handle~.  If no resources
  // match the queue is returned empty. If ~rpterr~ is set then a
  // warning is issued if no matches are found, and the spell checker is
  // invoked on ~name~.  If ~type_handle~ is ~null~ then a type check is
  // not made and resources are returned that match only ~name~ and
  // ~scope~.

  // @uvm-ieee 1800.2-2017 auto C.2.4.4.1
  function uvm_resource_types::rsrc_q_t lookup_name(string scope = "",
                                                    string name,
                                                    uvm_resource_base type_handle = null,
                                                    bit rpterr = 1);
    uvm_resource_types::rsrc_q_t rq;
    uvm_resource_types::rsrc_q_t q;
    uvm_resource_base rsrc;
    uvm_resource_base r;
    string rsrcs;

     // ensure rand stability during lookup
     begin
	process p = process::self();
	string s;
	if(p!=null) s=p.get_randstate();
	q=new();
	if(p!=null) p.set_randstate(s);
     end

     
    // resources with empty names are anonymous and do not exist in the name map
    if(name == "")
      return q;

    // Does an entry in the name map exist with the specified name?
    // If not, then we're done
    if(!rtab.exists(name)) begin
	    if(rpterr) void'(spell_check(name));	
		return q;
    end	

    rsrc = null;
    rq = rtab[name];
    for(int i=0; i<rq.size(); ++i) begin 
      r = rq.get(i);
      rsrcs = ri_tab.exists(r) ? ri_tab[r].scope: "";
      // does the type and scope match?
      if(((type_handle == null) || (r.get_type_handle() == type_handle)) &&
          uvm_is_match(rsrcs, scope))
        q.push_back(r);
    end

    return q;

  endfunction

  // Function -- NODOCS -- get_highest_precedence
  //
  // Traverse a queue, ~q~, of resources and return the one with the highest
  // precedence.  In the case where there exists more than one resource
  // with the highest precedence value, the first one that has that
  // precedence will be the one that is returned.

  // @uvm-ieee 1800.2-2017 auto C.2.4.4.2
  // @uvm-ieee 1800.2-2017 auto C.2.4.5.8
  static function uvm_resource_base get_highest_precedence(ref uvm_resource_types::rsrc_q_t q);

    uvm_resource_base rsrc;
    uvm_resource_base r;
    int unsigned i;
    int unsigned prec;
    int unsigned c_prec;

    if(q.size() == 0)
      return null;

    // get the first resources in the queue
    rsrc = q.get(0);
    prec = (ri_tab.exists(rsrc)) ? ri_tab[rsrc].precedence: 0;

    // start searching from the second resource
    for(int i = 1; i < q.size(); ++i) begin
      r = q.get(i);
      c_prec = (ri_tab.exists(r)) ? ri_tab[r].precedence: 0;
      if(c_prec > prec) begin
        rsrc = r;
        prec = c_prec;
      end
    end

    return rsrc;

  endfunction

  // Function -- NODOCS -- sort_by_precedence
  //
  // Given a list of resources, obtained for example from <lookup_scope>,
  // sort the resources in  precedence order. The highest precedence
  // resource will be first in the list and the lowest precedence will
  // be last. Resources that have the same precedence and the same name
  // will be ordered by most recently set first.

  // @uvm-ieee 1800.2-2017 auto C.2.4.4.3
  static function void sort_by_precedence(ref uvm_resource_types::rsrc_q_t q);
    uvm_resource_types::rsrc_q_t all[int];
    uvm_resource_base r;
    int unsigned prec;

    for(int i=0; i<q.size(); ++i) begin
      r = q.get(i);
      prec = (ri_tab.exists(r)) ? ri_tab[r].precedence: 0;
      if(!all.exists(prec))
         all[prec] = new;
      all[prec].push_front(r); //since we will push_front in the final
    end
    q.delete();
    foreach(all[i]) begin
      for(int j=0; j<all[i].size(); ++j) begin
        r = all[i].get(j);
        q.push_front(r);
      end
    end
  endfunction


  // Function -- NODOCS -- get_by_name
  //
  // Lookup a resource by ~name~, ~scope~, and ~type_handle~.  Whether
  // the get succeeds or fails, save a record of the get attempt.  The
  // ~rpterr~ flag indicates whether to report errors or not.
  // Essentially, it serves as a verbose flag.  If set then the spell
  // checker will be invoked and warnings about multiple resources will
  // be produced.

  // @uvm-ieee 1800.2-2017 auto C.2.4.4.4
  function uvm_resource_base get_by_name(string scope = "",
                                         string name,
                                         uvm_resource_base type_handle,
                                         bit rpterr = 1);

    uvm_resource_types::rsrc_q_t q;
    uvm_resource_base rsrc;

    q = lookup_name(scope, name, type_handle, rpterr);

    if(q.size() == 0) begin
      push_get_record(name, scope, null);
      return null;
    end

    rsrc = get_highest_precedence(q);
    push_get_record(name, scope, rsrc);
    return rsrc;
    
  endfunction


  // Function -- NODOCS -- lookup_type
  //
  // Lookup resources by type. Return a queue of resources that match
  // the ~type_handle~ and ~scope~.  If no resources match then the returned
  // queue is empty.

  // @uvm-ieee 1800.2-2017 auto C.2.4.4.5
  function uvm_resource_types::rsrc_q_t lookup_type(string scope = "",
                                                    uvm_resource_base type_handle);

    uvm_resource_types::rsrc_q_t q = new();
    uvm_resource_types::rsrc_q_t rq;
    uvm_resource_base r;
    int unsigned i;

    if(type_handle == null || !ttab.exists(type_handle)) begin
      return q;
    end

    rq = ttab[type_handle];
    for(int i = 0; i < rq.size(); ++i) begin 
      r = rq.get(i);
      if(ri_tab.exists(r) && uvm_is_match(ri_tab[r].scope, scope))
        q.push_back(r);
    end

    return q;

  endfunction

  // Function -- NODOCS -- get_by_type
  //
  // Lookup a resource by ~type_handle~ and ~scope~.  Insert a record into
  // the get history list whether or not the get succeeded.

  // @uvm-ieee 1800.2-2017 auto C.2.4.4.6
  function uvm_resource_base get_by_type(string scope = "",
                                         uvm_resource_base type_handle);

    uvm_resource_types::rsrc_q_t q;
    uvm_resource_base rsrc;

    q = lookup_type(scope, type_handle);

    if(q.size() == 0) begin
      push_get_record("<type>", scope, null);
      return null;
    end

    rsrc = q.get(0);
    push_get_record("<type>", scope, rsrc);
    return rsrc;
    
  endfunction

  // Function -- NODOCS -- lookup_regex_names
  //
  // This utility function answers the question, for a given ~name~,
  // ~scope~, and ~type_handle~, what are all of the resources with requested name,
  // a matching scope (where the resource scope may be a
  // regular expression), and a matching type? 
  // ~name~ and ~scope~ are explicit values.

  function uvm_resource_types::rsrc_q_t lookup_regex_names(string scope,
                                                           string name,
                                                           uvm_resource_base type_handle = null);
      return lookup_name(scope, name, type_handle, 0);
  endfunction

  // Function -- NODOCS -- lookup_regex
  //
  // Looks for all the resources whose name matches the regular
  // expression argument and whose scope matches the current scope.

  // @uvm-ieee 1800.2-2017 auto C.2.4.4.7
  function uvm_resource_types::rsrc_q_t lookup_regex(string re, scope);

    uvm_resource_types::rsrc_q_t rq;
    uvm_resource_types::rsrc_q_t result_q;
    int unsigned i;
    uvm_resource_base r;
    string s;

    result_q = new();

    foreach (rtab[name]) begin
      if ( ! uvm_is_match(re, name) )
        continue;
      rq = rtab[name];
      for(i = 0; i < rq.size(); i++) begin
        r = rq.get(i);
        if(ri_tab.exists(r) && uvm_is_match(ri_tab[r].scope, scope))
          result_q.push_back(r);
      end
    end

    return result_q;

  endfunction

  // Function -- NODOCS -- lookup_scope
  //
  // This is a utility function that answers the question: For a given
  // ~scope~, what resources are visible to it?  Locate all the resources
  // that are visible to a particular scope.  This operation could be
  // quite expensive, as it has to traverse all of the resources in the
  // database.

  // @uvm-ieee 1800.2-2017 auto C.2.4.4.8
  function uvm_resource_types::rsrc_q_t lookup_scope(string scope);

    uvm_resource_types::rsrc_q_t rq;
    uvm_resource_base r;
    int unsigned i;

    int unsigned err;
    uvm_resource_types::rsrc_q_t q = new();

    //iterate in reverse order for the special case of autoconfig
    //of arrays. The array name with no [] needs to be higher priority.
    //This has no effect an manual accesses.
    string name;

    if(rtab.last(name)) begin
    do begin
      rq = rtab[name];
      for(int i = 0; i < rq.size(); ++i) begin
        r = rq.get(i);
        if(ri_tab.exists(r) && uvm_is_match(ri_tab[r].scope, scope)) begin
          q.push_back(r);
        end
      end
    end while(rtab.prev(name));
    end

    return q;
    
  endfunction

  //--------------------
  // Group -- NODOCS -- Set Priority
  //--------------------
  //
  // Functions for altering the search priority of resources.  Resources
  // are stored in queues in the type and name maps.  When retrieving
  // resources, either by type or by name, the resource queue is search
  // from front to back.  The first one that matches the search criteria
  // is the one that is returned.  The ~set_priority~ functions let you
  // change the order in which resources are searched.  For any
  // particular resource, you can set its priority to UVM_HIGH, in which
  // case the resource is moved to the front of the queue, or to UVM_LOW in
  // which case the resource is moved to the back of the queue.

  // function- set_priority_queue
  //
  // This function handles the mechanics of moving a resource to either
  // the front or back of the queue.

  local function void set_priority_queue(uvm_resource_base rsrc,
                                         ref uvm_resource_types::rsrc_q_t q,
                                         uvm_resource_types::priority_e pri);

    uvm_resource_base r;
    int unsigned i;

    string msg;
    string name = rsrc.get_name();

    for(i = 0; i < q.size(); i++) begin
      r = q.get(i);
      if(r == rsrc) break;
    end

    if(r != rsrc) begin
      $sformat(msg, "Handle for resource named %s is not in the name name; cannot change its priority", name);
      uvm_report_error("NORSRC", msg);
      return;
    end

    q.delete(i);

    case(pri)
      uvm_resource_types::PRI_HIGH: q.push_front(rsrc);
      uvm_resource_types::PRI_LOW:  q.push_back(rsrc);
    endcase

  endfunction


  // Function -- NODOCS -- set_priority_type
  //
  // Change the priority of the ~rsrc~ based on the value of ~pri~, the
  // priority enum argument.  This function changes the priority only in
  // the type map, leaving the name map untouched.

  // @uvm-ieee 1800.2-2017 auto C.2.4.5.1
  function void set_priority_type(uvm_resource_base rsrc,
                                  uvm_resource_types::priority_e pri);

    uvm_resource_base type_handle;
    string msg;
    uvm_resource_types::rsrc_q_t q;

    if(rsrc == null) begin
      uvm_report_warning("NULLRASRC", "attempting to change the serach priority of a null resource");
      return;
    end

    type_handle = rsrc.get_type_handle();
    if(!ttab.exists(type_handle)) begin
      $sformat(msg, "Type handle for resrouce named %s not found in type map; cannot change its search priority", rsrc.get_name());
      uvm_report_error("RNFTYPE", msg);
      return;
    end

    q = ttab[type_handle];
    set_priority_queue(rsrc, q, pri);
  endfunction


  // Function -- NODOCS -- set_priority_name
  //
  // Change the priority of the ~rsrc~ based on the value of ~pri~, the
  // priority enum argument.  This function changes the priority only in
  // the name map, leaving the type map untouched.

  // @uvm-ieee 1800.2-2017 auto C.2.4.5.2
  function void set_priority_name(uvm_resource_base rsrc,
                                  uvm_resource_types::priority_e pri);

    string name;
    string msg;
    uvm_resource_types::rsrc_q_t q;

    if(rsrc == null) begin
      uvm_report_warning("NULLRASRC", "attempting to change the serach priority of a null resource");
      return;
    end

    name = rsrc.get_name();
    if(!rtab.exists(name)) begin
      $sformat(msg, "Resrouce named %s not found in name map; cannot change its search priority", name);
      uvm_report_error("RNFNAME", msg);
      return;
    end

    q = rtab[name];
    set_priority_queue(rsrc, q, pri);

  endfunction


  // Function -- NODOCS -- set_priority
  //
  // Change the search priority of the ~rsrc~ based on the value of ~pri~,
  // the priority enum argument.  This function changes the priority in
  // both the name and type maps.

  // @uvm-ieee 1800.2-2017 auto C.2.4.5.3
  function void set_priority (uvm_resource_base rsrc,
                              uvm_resource_types::priority_e pri);
    set_priority_type(rsrc, pri);
    set_priority_name(rsrc, pri);
  endfunction


  // @uvm-ieee 1800.2-2017 auto C.2.4.5.4
  static function void set_default_precedence( int unsigned precedence);
    uvm_coreservice_t cs = uvm_coreservice_t::get();
    cs.set_resource_pool_default_precedence(precedence);
  endfunction


  static function int unsigned get_default_precedence();
    uvm_coreservice_t cs = uvm_coreservice_t::get();
    return cs.get_resource_pool_default_precedence(); 
  endfunction

  
  // @uvm-ieee 1800.2-2017 auto C.2.4.5.6
  virtual function void set_precedence(uvm_resource_base r,
                                       int unsigned p=uvm_resource_pool::get_default_precedence());

    uvm_resource_types::rsrc_q_t q;
    string name;
    int unsigned i;
    uvm_resource_base rsrc;

    if(r == null) begin
      uvm_report_warning("NULLRASRC", "attempting to set precedence of a null resource");
      return;
    end

    name = r.get_name();
    if(rtab.exists(name)) begin
      q = rtab[name];

      for(i = 0; i < q.size(); i++) begin
        rsrc = q.get(i);
        if(rsrc == r) break;
      end
    end 
  
    if(r != rsrc) begin
      uvm_report_warning("NORSRC", $sformatf("resource named %s is not placed within the pool", name));
      return;
    end

    ri_tab[r].precedence = p;

  endfunction


  virtual function int unsigned get_precedence(uvm_resource_base r);

    uvm_resource_types::rsrc_q_t q;
    string name;
    int unsigned i;
    uvm_resource_base rsrc;

    if(r == null) begin
      uvm_report_warning("NULLRASRC", "attempting to get precedence of a null resource");
      return uvm_resource_pool::get_default_precedence();
    end

    name = r.get_name();
    if(rtab.exists(name)) begin
      q = rtab[name];

      for(i = 0; i < q.size(); i++) begin
        rsrc = q.get(i);
        if(rsrc == r) break;
      end
    end 
  
    if(r != rsrc) begin
      uvm_report_warning("NORSRC", $sformatf("resource named %s is not placed within the pool", name));
      return uvm_resource_pool::get_default_precedence();
    end

    return ri_tab[r].precedence;

  endfunction


  //--------------------------------------------------------------------
  // Group -- NODOCS -- Debug
  //--------------------------------------------------------------------

`ifdef UVM_ENABLE_DEPRECATED_API
  // Function -- NODOCS -- find_unused_resources
  //
  // Locate all the resources that have at least one write and no reads

  function uvm_resource_types::rsrc_q_t find_unused_resources();

    uvm_resource_types::rsrc_q_t rq;
    uvm_resource_types::rsrc_q_t q = new;
    int unsigned i;
    uvm_resource_base r;
    uvm_resource_types::access_t a;
    int reads;
    int writes;

    foreach (rtab[name]) begin
      rq = rtab[name];
      for(int i=0; i<rq.size(); ++i) begin
        r = rq.get(i);
        reads = 0;
        writes = 0;
        foreach(r.access[str]) begin
          a = r.access[str];
          reads += a.read_count;
          writes += a.write_count;
        end
        if(writes > 0 && reads == 0)
          q.push_back(r);
      end
    end

    return q;

  endfunction
`endif // UVM_ENABLE_DEPRECATED_API

  // Prints resouce queue into ~printer~, non-LRM
  function void m_print_resources(uvm_printer printer,
                                  uvm_resource_types::rsrc_q_t rq,
                                  bit audit = 0);
    
    printer.push_element(rq.get_name(),
                         "uvm_queue#(uvm_resource_base)",
                         $sformatf("%0d",rq.size()),
                         uvm_object_value_str(rq));

    for(int i=0; i<rq.size(); ++i) begin
      uvm_resource_base r;
      string scope;
      printer.push_element($sformatf("[%0d]", i),
                           "uvm_resource",
                           "-",
                           "-");

      r = rq.get(i);
      void'(get_scope(r, scope));
        
      printer.print_string("name", r.get_name());

      printer.print_generic_element("value",
                                    r.m_value_type_name(),
                                    "",
                                    r.m_value_as_string());
                                    
      printer.print_string("scope", scope);

      printer.print_field_int("precedence", get_precedence(r), 32, UVM_UNSIGNED);

      if (audit && r.access.size()) begin
        printer.print_array_header("accesses",
                                  r.access.size(),
                                  "queue");
        foreach(r.access[i]) begin
          printer.print_string($sformatf("[%s]", i),
                               $sformatf("reads: %0d @ %0t  writes: %0d @ %0t",
                                         r.access[i].read_count,
                                         r.access[i].read_time,
                                         r.access[i].write_count,
                                         r.access[i].write_time));
        end // foreach(r.access[i])

        printer.print_array_footer(r.access.size());
      end // (audit && r.access.size())

      printer.pop_element();
    end // int i=0

    printer.pop_element();

  endfunction : m_print_resources
                                  
  
  // Function -- NODOCS -- print_resources
  //
  // Print the resources that are in a single queue, ~rq~.  This is a utility
  // function that can be used to print any collection of resources
  // stored in a queue.  The ~audit~ flag determines whether or not the
  // audit trail is printed for each resource along with the name,
  // value, and scope regular expression.

  function void print_resources(uvm_resource_types::rsrc_q_t rq, bit audit = 0);

    int unsigned i;
    string id;
    static uvm_tree_printer printer = new();

    // Basically this is full implementation of something
    // like uvm_object::print, but we're interleaving
    // scope data, so it's all manual.
    printer.flush();
    if (rq == null)
      printer.print_generic_element("",
                                    "uvm_queue#(uvm_resource_base)",
                                    "",
                                    "<null>");
    else
      m_print_resources(printer, rq, audit);
    `uvm_info("UVM/RESOURCE_POOL/PRINT_QUEUE",
              printer.emit(),
              UVM_NONE)
  endfunction


  // Function -- NODOCS -- dump
  //
  // dump the entire resource pool.  The resource pool is traversed and
  // each resource is printed.  The utility function print_resources()
  // is used to initiate the printing. If the ~audit~ bit is set then
  // the audit trail is dumped for each resource.

  function void dump(bit audit = 0, uvm_printer printer = null);

    string name;
    static uvm_tree_printer m_printer;

    if (m_printer == null) begin
      m_printer = new();
      m_printer.set_type_name_enabled(1);
    end
      

    if (printer == null)
      printer = m_printer;
    
    printer.flush();
    printer.push_element("uvm_resource_pool",
                         "",
                         $sformatf("%0d",rtab.size()),
                         "");
    
    foreach (rtab[name]) begin
      m_print_resources(printer, rtab[name], audit);
    end

    printer.pop_element();
    
    `uvm_info("UVM/RESOURCE/DUMP", printer.emit(), UVM_NONE)

  endfunction
  
endclass

//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_resource #(T)
//
// Parameterized resource.  Provides essential access methods to read
// from and write to the resource database. 
//----------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto C.2.5.1
class uvm_resource #(type T=int) extends uvm_resource_base;

  typedef uvm_resource#(T) this_type;

  // singleton handle that represents the type of this resource
  static this_type my_type = get_type();

  // Can't be rand since things like rand strings are not legal.
  protected T val;

  // Because of uvm_resource#(T)::get_type, we can't use
  // the macros.  We need to do it all manually.
  typedef uvm_object_registry#(this_type) type_id;
  virtual function uvm_object_wrapper get_object_type();
    return type_id::get();
  endfunction : get_object_type
  virtual function uvm_object create (string name="");
    this_type tmp;
    if (name=="") tmp = new();
    else tmp = new(name);
    return tmp;
  endfunction : create
  `uvm_type_name_decl($sformatf("uvm_resource#(%s)", `uvm_typename(T)))
  
  
`ifdef UVM_ENABLE_DEPRECATED_API
  function new(string name="", scope="");
    super.new(name, scope);
  endfunction
`else
  // @uvm-ieee 1800.2-2017 auto C.2.5.2
  function new(string name="");
    super.new(name);
  endfunction
`endif // UVM_ENABLE_DEPRECATED_API

  virtual function string m_value_type_name();
    return `uvm_typename(T);
  endfunction : m_value_type_name
                                    
  virtual function string m_value_as_string();
    return $sformatf("%0p", val);
  endfunction : m_value_as_string
                                    
  //----------------------
  // Group -- NODOCS -- Type Interface
  //----------------------
  //
  // Resources can be identified by type using a static type handle.
  // The parent class provides the virtual function interface
  // <get_type_handle>.  Here we implement it by returning the static type
  // handle.

  // Function -- NODOCS -- get_type
  //
  // Static function that returns the static type handle.  The return
  // type is this_type, which is the type of the parameterized class.

  static function this_type get_type();
    if(my_type == null)
      my_type = new();
    return my_type;
  endfunction

  // Function -- NODOCS -- get_type_handle
  //
  // Returns the static type handle of this resource in a polymorphic
  // fashion.  The return type of get_type_handle() is
  // uvm_resource_base.  This function is not static and therefore can
  // only be used by instances of a parameterized resource.

  // @uvm-ieee 1800.2-2017 auto C.2.5.3.2
  function uvm_resource_base get_type_handle();
    return get_type();
  endfunction

`ifdef UVM_ENABLE_DEPRECATED_API
  //-------------------------
  // Group -- NODOCS -- Set/Get Interface
  //-------------------------
  //
  // uvm_resource#(T) provides an interface for setting and getting a
  // resources.  Specifically, a resource can insert itself into the
  // resource pool.  It doesn't make sense for a resource to get itself,
  // since you can't call a function on a handle you don't have.
  // However, a static get interface is provided as a convenience.  This
  // obviates the need for the user to get a handle to the global
  // resource pool as this is done for him here.

  // Function -- NODOCS -- set
  //
  // Simply put this resource into the global resource pool

  function void set();
    uvm_resource_pool rp = uvm_resource_pool::get();
    rp.set_scope(this, get_scope());
  endfunction

  
  // Function -- NODOCS -- set_override
  //
  // Put a resource into the global resource pool as an override.  This
  // means it gets put at the head of the list and is searched before
  // other existing resources that occupy the same position in the name
  // map or the type map.  The default is to override both the name and
  // type maps.  However, using the ~override~ argument you can specify
  // that either the name map or type map is overridden.

  function void set_override(uvm_resource_types::override_t override = 2'b11);
    uvm_resource_pool rp = uvm_resource_pool::get();
    if(override)
      rp.set_override(this, get_scope());
    else
      rp.set_scope(this, get_scope());
  endfunction

  // Function -- NODOCS -- get_by_name
  //
  // looks up a resource by ~name~ in the name map. The first resource
  // with the specified name, whose type is the current type, and is
  // visible in the specified ~scope~ is returned, if one exists.  The
  // ~rpterr~ flag indicates whether or not an error should be reported
  // if the search fails.  If ~rpterr~ is set to one then a failure
  // message is issued, including suggested spelling alternatives, based
  // on resource names that exist in the database, gathered by the spell
  // checker.

  static function this_type get_by_name(string scope,
                                        string name,
                                        bit rpterr = 1);

    uvm_resource_pool rp = uvm_resource_pool::get();
    uvm_resource_base rsrc_base;
    this_type rsrc;
    string msg;

    rsrc_base = rp.get_by_name(scope, name, my_type, rpterr);
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

  // Function -- NODOCS -- get_by_type
  //
  // looks up a resource by ~type_handle~ in the type map. The first resource
  // with the specified ~type_handle~ that is visible in the specified ~scope~ is
  // returned, if one exists. If there is no resource matching the specifications,
  // ~null~ is returned.

  static function this_type get_by_type(string scope = "",
                                        uvm_resource_base type_handle);

    uvm_resource_pool rp = uvm_resource_pool::get();
    uvm_resource_base rsrc_base;
    this_type rsrc;
    string msg;

    if(type_handle == null)
      return null;

    rsrc_base = rp.get_by_type(scope, type_handle);
    if(rsrc_base == null)
      return null;

    if(!$cast(rsrc, rsrc_base)) begin
      $sformat(msg, "Resource with specified type handle in scope %s was not located", scope);
      `uvm_warning("RSRCNF", msg)
      return null;
    end

    return rsrc;

  endfunction
`endif // UVM_ENABLE_DEPRECATED_API
  
  //----------------------------
  // Group -- NODOCS -- Read/Write Interface
  //----------------------------
  //
  // <read> and <write> provide a type-safe interface for getting and
  // setting the object in the resource container.  The interface is
  // type safe because the value argument for <write> and the return
  // value of <read> are T, the type supplied in the class parameter.
  // If either of these functions is used in an incorrect type context
  // the compiler will complain.

  // Function -- NODOCS -- read
  //
  // Return the object stored in the resource container.  If an ~accessor~
  // object is supplied then also update the accessor record for this
  // resource.

  // @uvm-ieee 1800.2-2017 auto C.2.5.4.1
  function T read(uvm_object accessor = null);
    record_read_access(accessor);
    return val;
  endfunction

  // Function -- NODOCS -- write
  // Modify the object stored in this resource container.  If the
  // resource is read-only then issue an error message and return
  // without modifying the object in the container.  If the resource is
  // not read-only and an ~accessor~ object has been supplied then also
  // update the accessor record.  Lastly, replace the object value in
  // the container with the value supplied as the argument, ~t~, and
  // release any processes blocked on
  // <uvm_resource_base::wait_modified>.  If the value to be written is
  // the same as the value already present in the resource then the
  // write is not done.  That also means that the accessor record is not
  // updated and the modified bit is not set.

  // @uvm-ieee 1800.2-2017 auto C.2.5.4.2
  function void write(T t, uvm_object accessor = null);

    if(is_read_only()) begin
      uvm_report_error("resource", $sformatf("resource %s is read only -- cannot modify", get_name()));
      return;
    end

    // Set the modified bit and record the transaction only if the value
    // has actually changed.
    if(val == t)
      return;

    record_write_access(accessor);

    // set the value and set the dirty bit
    val = t;
    modified = 1;
  endfunction

`ifdef UVM_ENABLE_DEPRECATED_API
  //----------------
  // Group -- NODOCS -- Priority
  //----------------
  //
  // Functions for manipulating the search priority of resources.  These
  // implementations of the interface defined in the base class delegate
  // to the resource pool. 


  // Function -- NODOCS -- set priority
  //
  // Change the search priority of the resource based on the value of
  // the priority enum argument, ~pri~.

  function void set_priority (uvm_resource_types::priority_e pri);
    uvm_resource_pool rp = uvm_resource_pool::get();
    rp.set_priority(this, pri);
  endfunction

`endif // UVM_ENABLE_DEPRECATED_API

  // Function -- NODOCS -- get_highest_precedence
  //
  // In a queue of resources, locate the first one with the highest
  // precedence whose type is T.  This function is static so that it can
  // be called from anywhere.

  static function this_type get_highest_precedence(ref uvm_resource_types::rsrc_q_t q);

    this_type rsrc;
    this_type r;
    uvm_resource_types::rsrc_q_t tq;
    uvm_resource_base rb;
    uvm_resource_pool rp = uvm_resource_pool::get();

    if(q.size() == 0)
      return null;

    tq = new();
    rsrc = null;

    for(int i = 0; i < q.size(); ++i) begin
      if($cast(r, q.get(i))) begin
        tq.push_back(r) ;
      end
    end

    rb = rp.get_highest_precedence(tq);
    if (!$cast(rsrc, rb))
       return null;
 
    return rsrc;

  endfunction

endclass

