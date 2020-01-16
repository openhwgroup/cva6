//
//----------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2014 Intel Corporation
// Copyright 2010-2014 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2010-2012 AMD
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2014 Cisco Systems, Inc.
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

`ifndef UVM_OBJECTION_SVH
`define UVM_OBJECTION_SVH

typedef class uvm_objection_context_object;
typedef class uvm_objection;
typedef class uvm_sequence_base;
typedef class uvm_objection_callback;
typedef uvm_callbacks #(uvm_objection,uvm_objection_callback) uvm_objection_cbs_t;
typedef class uvm_cmdline_processor;

class uvm_objection_events;
  int waiters;
  event raised;
  event dropped;
  event all_dropped;
endclass

//------------------------------------------------------------------------------
// Title -- NODOCS -- Objection Mechanism
//------------------------------------------------------------------------------
// The following classes define the objection mechanism and end-of-test
// functionality, which is based on <uvm_objection>.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//
// Class -- NODOCS -- uvm_objection
//
//------------------------------------------------------------------------------
// Objections provide a facility for coordinating status information between
// two or more participating components, objects, and even module-based IP.
//
// Tracing of objection activity can be turned on to follow the activity of
// the objection mechanism. It may be turned on for a specific objection
// instance with <uvm_objection::trace_mode>, or it can be set for all 
// objections from the command line using the option +UVM_OBJECTION_TRACE.
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 10.5.1
// @uvm-ieee 1800.2-2017 auto 10.5.1.1
class uvm_objection extends uvm_report_object;
  `uvm_register_cb(uvm_objection, uvm_objection_callback)

  protected bit     m_trace_mode;
  protected int     m_source_count[uvm_object];
  protected int     m_total_count [uvm_object];
  protected time    m_drain_time  [uvm_object];
  protected uvm_objection_events m_events [uvm_object];
  /*protected*/ bit     m_top_all_dropped;

  protected uvm_root m_top;
     
  static uvm_objection m_objections[$];

  //// Drain Logic

  // The context pool holds used context objects, so that
  // they're not constantly being recreated.  The maximum
  // number of contexts in the pool is equal to the maximum
  // number of simultaneous drains you could have occuring,
  // both pre and post forks.
  //
  // There's the potential for a programmability within the
  // library to dictate the largest this pool should be allowed
  // to grow, but that seems like overkill for the time being.
  local static uvm_objection_context_object m_context_pool[$];

  // These are the active drain processes, which have been
  // forked off by the background process.  A raise can
  // use this array to kill a drain.
`ifndef UVM_USE_PROCESS_CONTAINER   
  local process m_drain_proc[uvm_object];
`else
  local process_container_c m_drain_proc[uvm_object];
`endif
   
  // These are the contexts which have been scheduled for
  // retrieval by the background process, but which the
  // background process hasn't seen yet.
  local static uvm_objection_context_object m_scheduled_list[$];

  // Once a context is seen by the background process, it is
  // removed from the scheduled list, and placed in the forked
  // list.  At the same time, it is placed in the scheduled
  // contexts array.  A re-raise can use the scheduled contexts
  // array to detect (and cancel) the drain.
  local uvm_objection_context_object m_scheduled_contexts[uvm_object];
  local uvm_objection_context_object m_forked_list[$];

  // Once the forked drain has actually started (this occurs
  // ~1 delta AFTER the background process schedules it), the
  // context is removed from the above array and list, and placed
  // in the forked_contexts list.  
  local uvm_objection_context_object m_forked_contexts[uvm_object];

  protected bit m_prop_mode = 1;
  protected bit m_cleared; /* for checking obj count<0 */


  // Function -- NODOCS -- new
  //
  // Creates a new objection instance. Accesses the command line
  // argument +UVM_OBJECTION_TRACE to turn tracing on for
  // all objection objects.

  // @uvm-ieee 1800.2-2017 auto 10.5.1.2
  function new(string name="");
    uvm_cmdline_processor clp;
    uvm_coreservice_t cs_ ;
    string trace_args[$];
    super.new(name);
    cs_ = uvm_coreservice_t::get();
    m_top  = cs_.get_root();
     
    set_report_verbosity_level(m_top.get_report_verbosity_level());

    // Get the command line trace mode setting
    clp = uvm_cmdline_processor::get_inst();
    if(clp.get_arg_matches("+UVM_OBJECTION_TRACE", trace_args)) begin
      m_trace_mode=1;
    end
    m_objections.push_back(this);
  endfunction


  // Function -- NODOCS -- trace_mode
  //
  // Set or get the trace mode for the objection object. If no
  // argument is specified (or an argument other than 0 or 1)
  // the current trace mode is unaffected. A trace_mode of
  // 0 turns tracing off. A trace mode of 1 turns tracing on.
  // The return value is the mode prior to being reset.

   function bit trace_mode (int mode=-1);
    trace_mode = m_trace_mode;
    if(mode == 0) m_trace_mode = 0;
    else if(mode == 1) m_trace_mode = 1;
   endfunction

  // Function- m_report
  //
  // Internal method for reporting count updates

  function void m_report(uvm_object obj, uvm_object source_obj, string description, int count, string action);
    int _count = m_source_count.exists(obj) ? m_source_count[obj] : 0;
    int _total = m_total_count.exists(obj) ? m_total_count[obj] : 0;
    if (!uvm_report_enabled(UVM_NONE,UVM_INFO,"OBJTN_TRC") || !m_trace_mode) return;

    if (source_obj == obj)

      uvm_report_info("OBJTN_TRC", 
        $sformatf("Object %0s %0s %0d objection(s)%s: count=%0d  total=%0d",
           obj.get_full_name()==""?"uvm_top":obj.get_full_name(), action,
           count, description != ""? {" (",description,")"}:"", _count, _total), UVM_NONE);
    else begin
      int cpath = 0, last_dot=0;
      string sname = source_obj.get_full_name(), nm = obj.get_full_name();
      int max = sname.len() > nm.len() ? nm.len() : sname.len();

      // For readability, only print the part of the source obj hierarchy underneath
      // the current object.
      while((sname[cpath] == nm[cpath]) && (cpath < max)) begin
        if(sname[cpath] == ".") last_dot = cpath;
        cpath++;
      end 

      if(last_dot) sname = sname.substr(last_dot+1, sname.len());
      uvm_report_info("OBJTN_TRC",
        $sformatf("Object %0s %0s %0d objection(s) %0s its total (%s from source object %s%s): count=%0d  total=%0d",
           obj.get_full_name()==""?"uvm_top":obj.get_full_name(), action=="raised"?"added":"subtracted",
            count, action=="raised"?"to":"from", action, sname, 
            description != ""?{", ",description}:"", _count, _total), UVM_NONE);
    end
  endfunction


  // Function- m_get_parent
  //
  // Internal method for getting the parent of the given ~object~.
  // The ultimate parent is uvm_top, UVM's implicit top-level component. 

  function uvm_object m_get_parent(uvm_object obj);
    uvm_component comp;
    uvm_sequence_base seq;
    if ($cast(comp, obj)) begin
      obj = comp.get_parent();
    end
    else if ($cast(seq, obj)) begin
       obj = seq.get_sequencer();
    end
    else
      obj = m_top;
    if (obj == null)
      obj = m_top;
    return obj;
  endfunction


  // Function- m_propagate
  //
  // Propagate the objection to the objects parent. If the object is a
  // component, the parent is just the hierarchical parent. If the object is
  // a sequence, the parent is the parent sequence if one exists, or
  // it is the attached sequencer if there is no parent sequence. 
  //
  // obj : the uvm_object on which the objection is being raised or lowered
  // source_obj : the root object on which the end user raised/lowered the 
  //   objection (as opposed to an anscestor of the end user object)a
  // count : the number of objections associated with the action.
  // raise : indicator of whether the objection is being raised or lowered. A
  //   1 indicates the objection is being raised.

  function void m_propagate (uvm_object obj,
                             uvm_object source_obj,
                             string description,
                             int count,
                             bit raise,
                             int in_top_thread);
    if (obj != null && obj != m_top) begin
      obj = m_get_parent(obj);
      if(raise)
        m_raise(obj, source_obj, description, count);
      else
        m_drop(obj, source_obj, description, count, in_top_thread);
    end
  endfunction


  // Group -- NODOCS -- Objection Control


  // @uvm-ieee 1800.2-2017 auto 10.5.1.3.2
  function void set_propagate_mode (bit prop_mode);
     if (!m_top_all_dropped && (get_objection_total() != 0)) begin
        `uvm_error("UVM/BASE/OBJTN/PROP_MODE",
                   {"The propagation mode of '", this.get_full_name(),
                    "' cannot be changed while the objection is raised ",
                    "or draining!"})
        return;
     end

     m_prop_mode = prop_mode;
  endfunction : set_propagate_mode


  // @uvm-ieee 1800.2-2017 auto 10.5.1.3.1
  function bit get_propagate_mode();
     return m_prop_mode;
  endfunction : get_propagate_mode
   
  // Function -- NODOCS -- raise_objection
  //
  // Raises the number of objections for the source ~object~ by ~count~, which
  // defaults to 1.  The ~object~ is usually the ~this~ handle of the caller.
  // If ~object~ is not specified or ~null~, the implicit top-level component,
  // <uvm_root>, is chosen.
  //
  // Raising an objection causes the following.
  //
  // - The source and total objection counts for ~object~ are increased by
  //   ~count~. ~description~ is a string that marks a specific objection
  //   and is used in tracing/debug.
  //
  // - The objection's <raised> virtual method is called, which calls the
  //   <uvm_component::raised> method for all of the components up the 
  //   hierarchy.
  //

  // @uvm-ieee 1800.2-2017 auto 10.5.1.3.3
  virtual function void raise_objection (uvm_object obj=null,
                                         string description="",
                                         int count=1);
    if(obj == null)
      obj = m_top;
    m_cleared = 0;
    m_top_all_dropped = 0;
    m_raise (obj, obj, description, count);
  endfunction


  // Function- m_raise

  function void m_raise (uvm_object obj,
                         uvm_object source_obj,
                         string description="",
                         int count=1);
    int idx;
    uvm_objection_context_object ctxt;

    // Ignore raise if count is 0
    if (count == 0)
      return;

    if (m_total_count.exists(obj))
      m_total_count[obj] += count;
    else 
      m_total_count[obj] = count;

    if (source_obj==obj) begin
      if (m_source_count.exists(obj))
        m_source_count[obj] += count;
      else
        m_source_count[obj] = count;
    end
  
    if (m_trace_mode)
      m_report(obj,source_obj,description,count,"raised");

    raised(obj, source_obj, description, count);

      // Handle any outstanding drains...

    // First go through the scheduled list
    idx = 0;
    while (idx < m_scheduled_list.size()) begin
        if ((m_scheduled_list[idx].obj == obj) &&
            (m_scheduled_list[idx].objection == this)) begin
            // Caught it before the drain was forked
            ctxt = m_scheduled_list[idx];
            m_scheduled_list.delete(idx);
            break;
        end
        idx++;
    end

    // If it's not there, go through the forked list
    if (ctxt == null) begin
        idx = 0;
        while (idx < m_forked_list.size()) begin
            if (m_forked_list[idx].obj == obj) begin
                // Caught it after the drain was forked,
                // but before the fork started
                ctxt = m_forked_list[idx];
                m_forked_list.delete(idx);
                m_scheduled_contexts.delete(ctxt.obj);
                break;
            end
            idx++;
        end
    end

    // If it's not there, go through the forked contexts
    if (ctxt == null) begin
        if (m_forked_contexts.exists(obj)) begin
            // Caught it with the forked drain running
            ctxt = m_forked_contexts[obj];
            m_forked_contexts.delete(obj);
            // Kill the drain
`ifndef UVM_USE_PROCESS_CONTAINER	   
            m_drain_proc[obj].kill();
            m_drain_proc.delete(obj);
`else
            m_drain_proc[obj].p.kill();
            m_drain_proc.delete(obj);
`endif
	   
        end
    end

    if (ctxt == null) begin
        // If there were no drains, just propagate as usual

        if (!m_prop_mode && obj != m_top)
          m_raise(m_top,source_obj,description,count);
        else if (obj != m_top)
          m_propagate(obj, source_obj, description, count, 1, 0);
    end
    else begin
        // Otherwise we need to determine what exactly happened
        int diff_count;

        // Determine the diff count, if it's positive, then we're
        // looking at a 'raise' total, if it's negative, then
        // we're looking at a 'drop', but not down to 0.  If it's
        // a 0, that means that there is no change in the total.
        diff_count = count - ctxt.count;

        if (diff_count != 0) begin
            // Something changed
            if (diff_count > 0) begin
                // we're looking at an increase in the total
                if (!m_prop_mode && obj != m_top)
                  m_raise(m_top, source_obj, description, diff_count);
                else if (obj != m_top)
                  m_propagate(obj, source_obj, description, diff_count, 1, 0);
            end
            else begin
                // we're looking at a decrease in the total
                // The count field is always positive...
                diff_count = -diff_count;
                if (!m_prop_mode && obj != m_top)
                  m_drop(m_top, source_obj, description, diff_count);
                else if (obj != m_top)
                  m_propagate(obj, source_obj, description, diff_count, 0, 0);
            end
        end

        // Cleanup
        ctxt.clear();
        m_context_pool.push_back(ctxt);
    end
        
  endfunction
  

  // Function -- NODOCS -- drop_objection
  //
  // Drops the number of objections for the source ~object~ by ~count~, which
  // defaults to 1.  The ~object~ is usually the ~this~ handle of the caller.
  // If ~object~ is not specified or ~null~, the implicit top-level component,
  // <uvm_root>, is chosen.
  //
  // Dropping an objection causes the following.
  //
  // - The source and total objection counts for ~object~ are decreased by
  //   ~count~. It is an error to drop the objection count for ~object~ below
  //   zero.
  //
  // - The objection's <dropped> virtual method is called, which calls the
  //   <uvm_component::dropped> method for all of the components up the 
  //   hierarchy.
  //
  // - If the total objection count has not reached zero for ~object~, then
  //   the drop is propagated up the object hierarchy as with
  //   <raise_objection>. Then, each object in the hierarchy will have updated
  //   their ~source~ counts--objections that they originated--and ~total~
  //   counts--the total number of objections by them and all their
  //   descendants.
  //
  // If the total objection count reaches zero, propagation up the hierarchy
  // is deferred until a configurable drain-time has passed and the 
  // <uvm_component::all_dropped> callback for the current hierarchy level
  // has returned. The following process occurs for each instance up
  // the hierarchy from the source caller:
  //
  // A process is forked in a non-blocking fashion, allowing the ~drop~
  // call to return. The forked process then does the following:
  //
  // - If a drain time was set for the given ~object~, the process waits for
  //   that amount of time.
  //
  // - The objection's <all_dropped> virtual method is called, which calls the
  //   <uvm_component::all_dropped> method (if ~object~ is a component).
  //
  // - The process then waits for the ~all_dropped~ callback to complete.
  //
  // - After the drain time has elapsed and all_dropped callback has
  //   completed, propagation of the dropped objection to the parent proceeds
  //   as described in <raise_objection>, except as described below.
  //
  // If a new objection for this ~object~ or any of its descendants is raised
  // during the drain time or during execution of the all_dropped callback at
  // any point, the hierarchical chain described above is terminated and the
  // dropped callback does not go up the hierarchy. The raised objection will
  // propagate up the hierarchy, but the number of raised propagated up is
  // reduced by the number of drops that were pending waiting for the 
  // all_dropped/drain time completion. Thus, if exactly one objection
  // caused the count to go to zero, and during the drain exactly one new
  // objection comes in, no raises or drops are propagated up the hierarchy,
  //
  // As an optimization, if the ~object~ has no set drain-time and no
  // registered callbacks, the forked process can be skipped and propagation
  // proceeds immediately to the parent as described. 

  // @uvm-ieee 1800.2-2017 auto 10.5.1.3.4
  virtual function void drop_objection (uvm_object obj=null,
                                        string description="",
                                        int count=1);
    if(obj == null)
      obj = m_top;
    m_drop (obj, obj, description, count, 0);
  endfunction


  // Function- m_drop

  function void m_drop (uvm_object obj,
                        uvm_object source_obj,
                        string description="",
                        int count=1,
                        int in_top_thread=0);

    // Ignore drops if the count is 0
    if (count == 0)
      return;

    if (!m_total_count.exists(obj) || (count > m_total_count[obj])) begin
      if(m_cleared)
        return;
      uvm_report_fatal("OBJTN_ZERO", {"Object \"", obj.get_full_name(), 
        "\" attempted to drop objection '",this.get_name(),"' count below zero"});
      return;
    end

    if (obj == source_obj) begin
      if (!m_source_count.exists(obj) || (count > m_source_count[obj])) begin
        if(m_cleared)
          return;
        uvm_report_fatal("OBJTN_ZERO", {"Object \"", obj.get_full_name(), 
          "\" attempted to drop objection '",this.get_name(),"' count below zero"});
        return;
      end
      m_source_count[obj] -= count;
    end

    m_total_count[obj] -= count;

    if (m_trace_mode)
      m_report(obj,source_obj,description,count,"dropped");
    
    dropped(obj, source_obj, description, count);
  
    // if count != 0, no reason to fork
    if (m_total_count[obj] != 0) begin
      if (!m_prop_mode && obj != m_top)
        m_drop(m_top,source_obj,description, count, in_top_thread);
      else if (obj != m_top) begin
        this.m_propagate(obj, source_obj, description, count, 0, in_top_thread);
      end

    end
    else begin
        uvm_objection_context_object ctxt;
        if (m_context_pool.size())
          ctxt = m_context_pool.pop_front();
        else
          ctxt = new;

        ctxt.obj = obj;
        ctxt.source_obj = source_obj;
        ctxt.description = description;
        ctxt.count = count;
        ctxt.objection = this;
        // Need to be thread-safe, let the background
        // process handle it.

        // Why don't we look at in_top_thread here?  Because
        // a re-raise will kill the drain at object that it's
        // currently occuring at, and we need the leaf-level kills
        // to not cause accidental kills at branch-levels in
        // the propagation.

        // Using the background process just allows us to
        // separate the links of the chain.
        m_scheduled_list.push_back(ctxt);

    end // else: !if(m_total_count[obj] != 0)

  endfunction



  // @uvm-ieee 1800.2-2017 auto 10.5.1.3.5
  virtual function void clear(uvm_object obj=null);
    string name;
    int  idx;

    if (obj==null)
      obj=m_top;
    name = obj.get_full_name();
    if (name == "")
      name = "uvm_top";
    else
      name = obj.get_full_name();
    if (!m_top_all_dropped && get_objection_total(m_top))
      uvm_report_warning("OBJTN_CLEAR",{"Object '",name,
            "' cleared objection counts for ",get_name()});
    //Should there be a warning if there are outstanding objections?
    m_source_count.delete();
    m_total_count.delete();

    // Remove any scheduled drains from the static queue
    idx = 0;
    while (idx < m_scheduled_list.size()) begin
        if (m_scheduled_list[idx].objection == this) begin
            m_scheduled_list[idx].clear();
            m_context_pool.push_back(m_scheduled_list[idx]);
            m_scheduled_list.delete(idx);
        end
        else begin
            idx++;
        end
    end

    // Scheduled contexts and m_forked_lists have duplicate
    // entries... clear out one, free the other.
    m_scheduled_contexts.delete();
    while (m_forked_list.size()) begin
        m_forked_list[0].clear();
        m_context_pool.push_back(m_forked_list[0]);
        void'(m_forked_list.pop_front());
    end

    // running drains have a context and a process
    foreach (m_forked_contexts[o]) begin
`ifndef UVM_USE_PROCESS_CONTAINER       
        m_drain_proc[o].kill();
        m_drain_proc.delete(o);
`else
        m_drain_proc[o].p.kill();
        m_drain_proc.delete(o);
`endif
       
        m_forked_contexts[o].clear();
        m_context_pool.push_back(m_forked_contexts[o]);
        m_forked_contexts.delete(o);
    end

    m_top_all_dropped = 0;
    m_cleared = 1;
    if (m_events.exists(m_top))
      ->m_events[m_top].all_dropped;

  endfunction

  // m_execute_scheduled_forks
  // -------------------------

  // background process; when non
  static task m_execute_scheduled_forks();
    while(1) begin
      wait(m_scheduled_list.size() != 0);
      if(m_scheduled_list.size() != 0) begin
          uvm_objection_context_object c;
          // Save off the context before the fork
          c = m_scheduled_list.pop_front();
          // A re-raise can use this to figure out props (if any)
          c.objection.m_scheduled_contexts[c.obj] = c;
          // The fork below pulls out from the forked list
          c.objection.m_forked_list.push_back(c);
          // The fork will guard the m_forked_drain call, but
          // a re-raise can kill m_forked_list contexts in the delta
          // before the fork executes.
          fork : guard
              automatic uvm_objection objection = c.objection;
              begin
                  // Check to maike sure re-raise didn't empty the fifo
                  if (objection.m_forked_list.size() > 0) begin
                      uvm_objection_context_object ctxt;
	              ctxt = objection.m_forked_list.pop_front();
                      // Clear it out of scheduled
                      objection.m_scheduled_contexts.delete(ctxt.obj);
                      // Move it in to forked (so re-raise can figure out props)
                      objection.m_forked_contexts[ctxt.obj] = ctxt;
                      // Save off our process handle, so a re-raise can kill it...
`ifndef UVM_USE_PROCESS_CONTAINER		     
                      objection.m_drain_proc[ctxt.obj] = process::self();
`else
		     begin
			process_container_c c = new(process::self());
			objection.m_drain_proc[ctxt.obj]=c;
		     end
`endif		     
                      // Execute the forked drain
                      objection.m_forked_drain(ctxt.obj, ctxt.source_obj, ctxt.description, ctxt.count, 1);
                      // Cleanup if we survived (no re-raises)
                      objection.m_drain_proc.delete(ctxt.obj);
                      objection.m_forked_contexts.delete(ctxt.obj);
                      // Clear out the context object (prevent memory leaks)
                      ctxt.clear();
                      // Save the context in the pool for later reuse
                      m_context_pool.push_back(ctxt);
                  end
              end
          join_none : guard
      end
    end
  endtask


  // m_forked_drain
  // -------------

  task m_forked_drain (uvm_object obj,
                       uvm_object source_obj,
                       string description="",
                       int count=1,
                       int in_top_thread=0);

      if (m_drain_time.exists(obj))
        `uvm_delay(m_drain_time[obj])
      
      if (m_trace_mode)
        m_report(obj,source_obj,description,count,"all_dropped");
      
      all_dropped(obj,source_obj,description, count);
          
          // wait for all_dropped cbs to complete
      wait fork;

      /* NOT NEEDED - Any raise would have killed us!
      if(!m_total_count.exists(obj))
        diff_count = -count;
      else
        diff_count = m_total_count[obj] - count;
      */

      // we are ready to delete the 0-count entries for the current
      // object before propagating up the hierarchy. 
      if (m_source_count.exists(obj) && m_source_count[obj] == 0)
        m_source_count.delete(obj);
          
      if (m_total_count.exists(obj) && m_total_count[obj] == 0)
        m_total_count.delete(obj);

      if (!m_prop_mode && obj != m_top)
        m_drop(m_top,source_obj,description, count, 1);
      else if (obj != m_top)
        m_propagate(obj, source_obj, description, count, 0, 1);

  endtask


  // m_init_objections
  // -----------------

  // Forks off the single background process
  static function void m_init_objections();
    fork 
      uvm_objection::m_execute_scheduled_forks();
    join_none
  endfunction

  // Function -- NODOCS -- set_drain_time
  //
  // Sets the drain time on the given ~object~ to ~drain~.
  //
  // The drain time is the amount of time to wait once all objections have
  // been dropped before calling the all_dropped callback and propagating
  // the objection to the parent. 
  //
  // If a new objection for this ~object~ or any of its descendants is raised
  // during the drain time or during execution of the all_dropped callbacks,
  // the drain_time/all_dropped execution is terminated. 

  // AE: set_drain_time(drain,obj=null)?
  // @uvm-ieee 1800.2-2017 auto 10.5.1.3.7
  function void set_drain_time (uvm_object obj=null, time drain);
    if (obj==null)
      obj = m_top;
    m_drain_time[obj] = drain;
  endfunction
  

  //----------------------
  // Group -- NODOCS -- Callback Hooks
  //----------------------

  // Function -- NODOCS -- raised
  //
  // Objection callback that is called when a <raise_objection> has reached ~obj~.
  // The default implementation calls <uvm_component::raised>.

  // @uvm-ieee 1800.2-2017 auto 10.5.1.4.1
  virtual function void raised (uvm_object obj,
                                uvm_object source_obj,
                                string description,
                                int count);
    uvm_component comp;
    if ($cast(comp,obj))    
      comp.raised(this, source_obj, description, count);
    `uvm_do_callbacks(uvm_objection,uvm_objection_callback,raised(this,obj,source_obj,description,count))
    if (m_events.exists(obj))
       ->m_events[obj].raised;
  endfunction


  // Function -- NODOCS -- dropped
  //
  // Objection callback that is called when a <drop_objection> has reached ~obj~.
  // The default implementation calls <uvm_component::dropped>.

  // @uvm-ieee 1800.2-2017 auto 10.5.1.4.2
  virtual function void dropped (uvm_object obj,
                                 uvm_object source_obj,
                                 string description,
                                 int count);
    uvm_component comp;
    if($cast(comp,obj))    
      comp.dropped(this, source_obj, description, count);
    `uvm_do_callbacks(uvm_objection,uvm_objection_callback,dropped(this,obj,source_obj,description,count))
    if (m_events.exists(obj))
       ->m_events[obj].dropped;
  endfunction


  // Function -- NODOCS -- all_dropped
  //
  // Objection callback that is called when a <drop_objection> has reached ~obj~,
  // and the total count for ~obj~ goes to zero. This callback is executed
  // after the drain time associated with ~obj~. The default implementation 
  // calls <uvm_component::all_dropped>.

  // @uvm-ieee 1800.2-2017 auto 10.5.1.4.3
  virtual task all_dropped (uvm_object obj,
                            uvm_object source_obj,
                            string description,
                            int count);
    uvm_component comp;
    if($cast(comp,obj))    
      comp.all_dropped(this, source_obj, description, count);
    `uvm_do_callbacks(uvm_objection,uvm_objection_callback,all_dropped(this,obj,source_obj,description,count))
    if (m_events.exists(obj))
       ->m_events[obj].all_dropped;
    if (obj == m_top)
      m_top_all_dropped = 1;
  endtask


  //------------------------
  // Group -- NODOCS -- Objection Status
  //------------------------

  // Function -- NODOCS -- get_objectors
  //
  // Returns the current list of objecting objects (objects that
  // raised an objection but have not dropped it).

  // @uvm-ieee 1800.2-2017 auto 10.5.1.5.1
  function void get_objectors(ref uvm_object list[$]);
    list.delete();
    foreach (m_source_count[obj]) list.push_back(obj); 
  endfunction



  // @uvm-ieee 1800.2-2017 auto 10.5.1.5.2
  task wait_for(uvm_objection_event objt_event, uvm_object obj=null);

     if (obj==null)
       obj = m_top;

     if (!m_events.exists(obj)) begin
       m_events[obj] = new;
     end

     m_events[obj].waiters++;
     case (objt_event)
       UVM_RAISED:      @(m_events[obj].raised);
       UVM_DROPPED:     @(m_events[obj].dropped);
       UVM_ALL_DROPPED: @(m_events[obj].all_dropped);
     endcase
     
     m_events[obj].waiters--;

     if (m_events[obj].waiters == 0)
       m_events.delete(obj);

   endtask


   task wait_for_total_count(uvm_object obj=null, int count=0);
     if (obj==null)
       obj = m_top;

     if(!m_total_count.exists(obj) && count == 0)
       return;
     if (count == 0)
        wait (!m_total_count.exists(obj) && count == 0);
     else
        wait (m_total_count.exists(obj) && m_total_count[obj] == count);
   endtask
   

  // Function -- NODOCS -- get_objection_count
  //
  // Returns the current number of objections raised by the given ~object~.

  // @uvm-ieee 1800.2-2017 auto 10.5.1.5.3
  function int get_objection_count (uvm_object obj=null);
    if (obj==null)
      obj = m_top;

    if (!m_source_count.exists(obj))
      return 0;
    return m_source_count[obj];
  endfunction
  

  // Function -- NODOCS -- get_objection_total
  //
  // Returns the current number of objections raised by the given ~object~ 
  // and all descendants.

  // @uvm-ieee 1800.2-2017 auto 10.5.1.5.4
  function int get_objection_total (uvm_object obj=null);
 
    if (obj==null)
      obj = m_top;

    if (!m_total_count.exists(obj))
      return 0;
    else
      return m_total_count[obj];
     
  endfunction
  

  // Function -- NODOCS -- get_drain_time
  //
  // Returns the current drain time set for the given ~object~ (default: 0 ns).

  // @uvm-ieee 1800.2-2017 auto 10.5.1.3.6
  function time get_drain_time (uvm_object obj=null);
    if (obj==null)
      obj = m_top;

    if (!m_drain_time.exists(obj))
      return 0;
    return m_drain_time[obj];
  endfunction


  // m_display_objections

  protected function string m_display_objections(uvm_object obj=null, bit show_header=1);

    static string blank="                                                                                   ";
    
    string s;
    int total;
    uvm_object list[string];
    uvm_object curr_obj;
    int depth;
    string name;
    string this_obj_name;
    string curr_obj_name;
  
    foreach (m_total_count[o]) begin
      uvm_object theobj = o; 
      if ( m_total_count[o] > 0)
        list[theobj.get_full_name()] = theobj;
    end

    if (obj==null)
      obj = m_top;

    total = get_objection_total(obj);
    
    s = $sformatf("The total objection count is %0d\n",total);

    if (total == 0)
      return s;

    s = {s,"---------------------------------------------------------\n"};
    s = {s,"Source  Total   \n"};
    s = {s,"Count   Count   Object\n"};
    s = {s,"---------------------------------------------------------\n"};

  
    this_obj_name = obj.get_full_name();
    curr_obj_name = this_obj_name;

    do begin

      curr_obj = list[curr_obj_name];
  
      // determine depth
      depth=0;
      foreach (curr_obj_name[i])
        if (curr_obj_name[i] == ".")
          depth++;

      // determine leaf name
      name = curr_obj_name;
      for (int i=curr_obj_name.len()-1;i >= 0; i--)
        if (curr_obj_name[i] == ".") begin
           name = curr_obj_name.substr(i+1,curr_obj_name.len()-1); 
           break;
        end
      if (curr_obj_name == "")
        name = "uvm_top";
      else
        depth++;

      // print it
      s = {s, $sformatf("%-6d  %-6d %s%s\n",
         m_source_count.exists(curr_obj) ? m_source_count[curr_obj] : 0,
         m_total_count.exists(curr_obj) ? m_total_count[curr_obj] : 0,
         blank.substr(0,2*depth), name)};

    end while (list.next(curr_obj_name) &&
        curr_obj_name.substr(0,this_obj_name.len()-1) == this_obj_name);
  
    s = {s,"---------------------------------------------------------\n"};

    return s;

  endfunction
  

  function string convert2string();
    return m_display_objections(m_top,1);
  endfunction
  
  
  // Function -- NODOCS -- display_objections
  // 
  // Displays objection information about the given ~object~. If ~object~ is
  // not specified or ~null~, the implicit top-level component, <uvm_root>, is
  // chosen. The ~show_header~ argument allows control of whether a header is
  // output.

  function void display_objections(uvm_object obj=null, bit show_header=1);
	string m = m_display_objections(obj,show_header);
    `uvm_info("UVM/OBJ/DISPLAY",m,UVM_NONE)
  endfunction


  // Below is all of the basic data stuff that is needed for a uvm_object
  // for factory registration, printing, comparing, etc.

  typedef uvm_object_registry#(uvm_objection,"uvm_objection") type_id;
  static function type_id get_type();
    return type_id::get();
  endfunction

  function uvm_object create (string name="");
    uvm_objection tmp = new(name);
    return tmp;
  endfunction

  virtual function string get_type_name ();
    return "uvm_objection";
  endfunction

  function void do_copy (uvm_object rhs);
    uvm_objection _rhs;
    $cast(_rhs, rhs);
    m_source_count = _rhs.m_source_count;
    m_total_count  = _rhs.m_total_count;
    m_drain_time   = _rhs.m_drain_time;
    m_prop_mode    = _rhs.m_prop_mode;
  endfunction

endclass

// TODO: change to plusarg
//`define UVM_DEFAULT_TIMEOUT 9200s

typedef class uvm_cmdline_processor;


`ifdef UVM_ENABLE_DEPRECATED_API
//------------------------------------------------------------------------------
//
// Class- uvm_test_done_objection DEPRECATED
//
// Provides built-in end-of-test coordination
//------------------------------------------------------------------------------

class uvm_test_done_objection extends uvm_objection;

   protected static uvm_test_done_objection m_inst;
  protected bit m_forced;

  // For communicating all objections dropped and end of phasing
  local  bit m_executing_stop_processes;
  local  int m_n_stop_threads;


  // Function- new DEPRECATED
  //
  // Creates the singleton test_done objection. Users must not call
  // this method directly.

  function new(string name="uvm_test_done");
    super.new(name);
  endfunction


  // Function- qualify DEPRECATED
  //
  // Checks that the given ~object~ is derived from either <uvm_component> or
  // <uvm_sequence_base>.

  virtual function void qualify(uvm_object obj=null,
                                bit is_raise,
                                string description);
    uvm_component c;
    uvm_sequence_base s;
    string nm = is_raise ? "raise_objection" : "drop_objection";
    string desc = description == "" ? "" : {" (\"", description, "\")"};
    if(! ($cast(c,obj) || $cast(s,obj))) begin
      uvm_report_error("TEST_DONE_NOHIER", {"A non-hierarchical object, '",
        obj.get_full_name(), "' (", obj.get_type_name(),") was used in a call ",
        "to uvm_test_done.", nm,"(). For this objection, a sequence ",
        "or component is required.", desc });
    end
  endfunction

  // Below are basic data operations needed for all uvm_objects
  // for factory registration, printing, comparing, etc.

  typedef uvm_object_registry#(uvm_test_done_objection,"uvm_test_done") type_id;
  static function type_id get_type();
    return type_id::get();
  endfunction

  function uvm_object create (string name="");
    uvm_test_done_objection tmp = new(name);
    return tmp;
  endfunction

  virtual function string get_type_name ();
    return "uvm_test_done";
  endfunction

  static function uvm_test_done_objection get();
    if(m_inst == null)
      m_inst = uvm_test_done_objection::type_id::create("run");
    return m_inst;
  endfunction

endclass
`endif // UVM_ENABLE_DEPRECATED_API


// Have a pool of context objects to use
class uvm_objection_context_object;
    uvm_object obj;
    uvm_object source_obj;
    string description;
    int    count;
    uvm_objection objection;

    // Clears the values stored within the object,
    // preventing memory leaks from reused objects
    function void clear();
        obj = null;
        source_obj = null;
        description = "";
        count = 0;
        objection = null;
    endfunction : clear
endclass

// Typedef - Exists for backwards compat
typedef uvm_objection uvm_callbacks_objection;
   
//------------------------------------------------------------------------------
//
// Class -- NODOCS -- uvm_objection_callback
//
//------------------------------------------------------------------------------
// The uvm_objection is the callback type that defines the callback 
// implementations for an objection callback. A user uses the callback
// type uvm_objection_cbs_t to add callbacks to specific objections.
//
// For example:
//
//| class my_objection_cb extends uvm_objection_callback;
//|   function new(string name);
//|     super.new(name);
//|   endfunction
//|
//|   virtual function void raised (uvm_objection objection, uvm_object obj, 
//|       uvm_object source_obj, string description, int count);
//|       `uvm_info("RAISED","%0t: Objection %s: Raised for %s", $time, objection.get_name(),
//|       obj.get_full_name());
//|   endfunction
//| endclass
//| ...
//| initial begin
//|   my_objection_cb cb = new("cb");
//|   uvm_objection_cbs_t::add(null, cb); //typewide callback
//| end


// @uvm-ieee 1800.2-2017 auto 10.5.2.1
class uvm_objection_callback extends uvm_callback;
  function new(string name);
    super.new(name);
  endfunction

  // Function -- NODOCS -- raised
  //
  // Objection raised callback function. Called by <uvm_objection::raised>.

  // @uvm-ieee 1800.2-2017 auto 10.5.2.2.1
  virtual function void raised (uvm_objection objection, uvm_object obj, 
      uvm_object source_obj, string description, int count);
  endfunction

  // Function -- NODOCS -- dropped
  //
  // Objection dropped callback function. Called by <uvm_objection::dropped>.

  // @uvm-ieee 1800.2-2017 auto 10.5.2.2.2
  virtual function void dropped (uvm_objection objection, uvm_object obj, 
      uvm_object source_obj, string description, int count);
  endfunction

  // Function -- NODOCS -- all_dropped
  //
  // Objection all_dropped callback function. Called by <uvm_objection::all_dropped>.

  // @uvm-ieee 1800.2-2017 auto 10.5.2.2.3
  virtual task all_dropped (uvm_objection objection, uvm_object obj, 
      uvm_object source_obj, string description, int count);
  endtask

endclass


`endif
