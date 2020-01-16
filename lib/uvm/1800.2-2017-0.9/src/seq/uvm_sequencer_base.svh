//----------------------------------------------------------------------
// Copyright 2007-2017 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2014 Intel Corporation
// Copyright 2010-2017 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2013 Verilab
// Copyright 2010-2012 AMD
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2013-2018 Cisco Systems, Inc.
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
//----------------------------------------------------------------------

typedef uvm_config_db#(uvm_sequence_base) uvm_config_seq;
typedef class uvm_sequence_request;

// Utility class for tracking default_sequences
class uvm_sequence_process_wrapper;
    process pid;
    uvm_sequence_base seq;
endclass : uvm_sequence_process_wrapper

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_sequencer_base
//
// Controls the flow of sequences, which generate the stimulus (sequence item
// transactions) that is passed on to drivers for execution.
//
//------------------------------------------------------------------------------
`ifndef UVM_ENABLE_DEPRECATED_API
virtual
`endif
// @uvm-ieee 1800.2-2017 auto 15.3.1
class uvm_sequencer_base extends uvm_component;

  typedef enum {SEQ_TYPE_REQ,
                SEQ_TYPE_LOCK} seq_req_t; 

// queue of sequences waiting for arbitration
  protected uvm_sequence_request arb_sequence_q[$];

  protected bit                 arb_completed[int];

  protected uvm_sequence_base   lock_list[$];
  protected uvm_sequence_base   reg_sequences[int];
  protected int                 m_sequencer_id;
  protected int                 m_lock_arb_size;  // used for waiting processes
  protected int                 m_arb_size;       // used for waiting processes
  protected int                 m_wait_for_item_sequence_id,
                                m_wait_for_item_transaction_id;
  protected int                 m_wait_relevant_count = 0 ;
  protected int                 m_max_zero_time_wait_relevant_count = 10;
  protected time                m_last_wait_relevant_time = 0 ;

  local uvm_sequencer_arb_mode  m_arbitration = UVM_SEQ_ARB_FIFO;
  local static int              g_request_id;
  local static int              g_sequence_id = 1;
  local static int              g_sequencer_id = 1;


  // Function -- NODOCS -- new
  //
  // Creates and initializes an instance of this class using the normal
  // constructor arguments for uvm_component: name is the name of the
  // instance, and parent is the handle to the hierarchical parent.

  // @uvm-ieee 1800.2-2017 auto 15.3.2.1
  extern function new (string name, uvm_component parent);



  // @uvm-ieee 1800.2-2017 auto 15.3.2.2
  extern function bit is_child (uvm_sequence_base parent, uvm_sequence_base child);



  // @uvm-ieee 1800.2-2017 auto 15.3.2.3
  extern virtual function int user_priority_arbitration(int avail_sequences[$]);


  // Task -- NODOCS -- execute_item
  //
  // Executes the given transaction ~item~ directly on this sequencer. A temporary
  // parent sequence is automatically created for the ~item~.  There is no capability to
  // retrieve responses. If the driver returns responses, they will accumulate in the
  // sequencer, eventually causing response overflow unless
  // <uvm_sequence_base::set_response_queue_error_report_enabled> is called.

  // @uvm-ieee 1800.2-2017 auto 15.3.2.5
  extern virtual task execute_item(uvm_sequence_item item);

  // Hidden array, keeps track of running default sequences
  protected uvm_sequence_process_wrapper m_default_sequences[uvm_phase];

  // Function -- NODOCS -- start_phase_sequence
  //
  // Start the default sequence for this phase, if any.
  // The default sequence is configured via resources using
  // either a sequence instance or sequence type (object wrapper).
  // If both are used,
  // the sequence instance takes precedence. When attempting to override
  // a previous default sequence setting, you must override both
  // the instance and type (wrapper) resources, else your override may not
  // take effect.
  //
  // When setting the resource using ~set~, the 1st argument specifies the
  // context pointer, usually ~this~ for components or ~null~ when executed from
  // outside the component hierarchy (i.e. in module).
  // The 2nd argument is the instance string, which is a path name to the
  // target sequencer, relative to the context pointer.  The path must include
  // the name of the phase with a "_phase" suffix. The 3rd argument is the
  // resource name, which is "default_sequence". The 4th argument is either
  // an object wrapper for the sequence type, or an instance of a sequence.
  //
  // Configuration by instances
  // allows pre-initialization, setting rand_mode, use of inline
  // constraints, etc.
  //
  //| myseq_t myseq = new("myseq");
  //| myseq.randomize() with { ... };
  //| uvm_config_db #(uvm_sequence_base)::set(null, "top.agent.myseqr.main_phase",
  //|                                         "default_sequence",
  //|                                         myseq);
  //
  // Configuration by type is shorter and can be substituted via
  // the factory.
  //
  //| uvm_config_db #(uvm_object_wrapper)::set(null, "top.agent.myseqr.main_phase",
  //|                                          "default_sequence",
  //|                                          myseq_type::type_id::get());
  //
  // The uvm_resource_db can similarly be used.
  //
  //| myseq_t myseq = new("myseq");
  //| myseq.randomize() with { ... };
  //| uvm_resource_db #(uvm_sequence_base)::set({get_full_name(), ".myseqr.main_phase",
  //|                                           "default_sequence",
  //|                                           myseq, this);
  //
  //| uvm_resource_db #(uvm_object_wrapper)::set({get_full_name(), ".myseqr.main_phase",
  //|                                            "default_sequence",
  //|                                            myseq_t::type_id::get(),
  //|                                            this );
  //
  //



  extern virtual function void start_phase_sequence(uvm_phase phase);

  // Function -- NODOCS -- stop_phase_sequence
  //
  // Stop the default sequence for this phase, if any exists, and it
  // is still executing.

  extern virtual function void stop_phase_sequence(uvm_phase phase);



  // Task -- NODOCS -- wait_for_grant
  //
  // This task issues a request for the specified sequence.  If item_priority
  // is not specified, then the current sequence priority will be used by the
  // arbiter.  If a lock_request is made, then the  sequencer will issue a lock
  // immediately before granting the sequence.  (Note that the lock may be
  // granted without the sequence being granted if is_relevant is not asserted).
  //
  // When this method returns, the sequencer has granted the sequence, and the
  // sequence must call send_request without inserting any simulation delay
  // other than delta cycles.  The driver is currently waiting for the next
  // item to be sent via the send_request call.

  // @uvm-ieee 1800.2-2017 auto 15.3.2.6
  extern virtual task wait_for_grant(uvm_sequence_base sequence_ptr,
                                     int item_priority = -1,
                                     bit lock_request = 0);



  // @uvm-ieee 1800.2-2017 auto 15.3.2.7
  extern virtual task wait_for_item_done(uvm_sequence_base sequence_ptr,
                                         int transaction_id);



  // @uvm-ieee 1800.2-2017 auto 15.3.2.8
  extern function bit is_blocked(uvm_sequence_base sequence_ptr);



  // @uvm-ieee 1800.2-2017 auto 15.3.2.9
  extern function bit has_lock(uvm_sequence_base sequence_ptr);



  // @uvm-ieee 1800.2-2017 auto 15.3.2.10
  extern virtual task lock(uvm_sequence_base sequence_ptr);



  // @uvm-ieee 1800.2-2017 auto 15.3.2.11
  extern virtual task grab(uvm_sequence_base sequence_ptr);



  // Function: unlock
  //
  // Implementation of unlock, as defined in P1800.2-2017 section 15.3.2.12.
  // 
  // NOTE: unlock is documented in error as a virtual task, whereas it is 
  // implemented as a virtual function.
  //
  //| extern virtual function void unlock(uvm_sequence_base sequence_ptr);

  // @uvm-ieee 1800.2-2017 auto 15.3.2.12
  extern virtual function void unlock(uvm_sequence_base sequence_ptr);


  // Function: ungrab
  //
  // Implementation of ungrab, as defined in P1800.2-2017 section 15.3.2.13.
  // 
  // NOTE: ungrab is documented in error as a virtual task, whereas it is 
  // implemented as a virtual function.
  //
  //| extern virtual function void ungrab(uvm_sequence_base sequence_ptr);

  // @uvm-ieee 1800.2-2017 auto 15.3.2.13
  extern virtual function void  ungrab(uvm_sequence_base sequence_ptr);



  // @uvm-ieee 1800.2-2017 auto 15.3.2.14
  extern virtual function void stop_sequences();



  // @uvm-ieee 1800.2-2017 auto 15.3.2.15
  extern virtual function bit is_grabbed();



  // @uvm-ieee 1800.2-2017 auto 15.3.2.16
  extern virtual function uvm_sequence_base current_grabber();



  // @uvm-ieee 1800.2-2017 auto 15.3.2.17
  extern virtual function bit has_do_available();

 

  // @uvm-ieee 1800.2-2017 auto 15.3.2.19
  extern function void set_arbitration(UVM_SEQ_ARB_TYPE val);



  // @uvm-ieee 1800.2-2017 auto 15.3.2.18
  extern function UVM_SEQ_ARB_TYPE get_arbitration();


  // Task -- NODOCS -- wait_for_sequences
  //
  // Waits for a sequence to have a new item available. Uses
  // <uvm_wait_for_nba_region> to give a sequence as much time as
  // possible to deliver an item before advancing time.

  extern virtual task wait_for_sequences();


  // Function -- NODOCS -- send_request
  //
  // Derived classes implement this function to send a request item to the
  // sequencer, which will forward it to the driver.  If the rerandomize bit
  // is set, the item will be randomized before being sent to the driver.
  //
  // This function may only be called after a <wait_for_grant> call.

  // @uvm-ieee 1800.2-2017 auto 15.3.2.20
  extern virtual function void send_request(uvm_sequence_base sequence_ptr,
                                            uvm_sequence_item t,
                                            bit rerandomize = 0);


  // @uvm-ieee 1800.2-2017 auto 15.3.2.21
  extern virtual function void set_max_zero_time_wait_relevant_count(int new_val) ;

  // Added in IEEE. Not in UVM 1.2
  // @uvm-ieee 1800.2-2017 auto 15.3.2.4
  extern virtual function uvm_sequence_base get_arbitration_sequence( int index );

  //----------------------------------------------------------------------------
  // INTERNAL METHODS - DO NOT CALL DIRECTLY, ONLY OVERLOAD IF VIRTUAL
  //----------------------------------------------------------------------------

  extern protected function void grant_queued_locks();


  extern protected task          m_select_sequence();
  extern protected function int  m_choose_next_request();
  extern           task          m_wait_for_arbitration_completed(int request_id);
  extern           function void m_set_arbitration_completed(int request_id);


  extern local task m_lock_req(uvm_sequence_base sequence_ptr, bit lock);


  // Task- m_unlock_req
  //
  // Called by a sequence to request an unlock.  This
  // will remove a lock for this sequence if it exists

  extern function void m_unlock_req(uvm_sequence_base sequence_ptr);


  extern local function void remove_sequence_from_queues(uvm_sequence_base sequence_ptr);
  extern function void m_sequence_exiting(uvm_sequence_base sequence_ptr);
  extern function void kill_sequence(uvm_sequence_base sequence_ptr);

  extern virtual function void analysis_write(uvm_sequence_item t);


  extern           function void   do_print (uvm_printer printer);


  extern virtual   function int    m_register_sequence(uvm_sequence_base sequence_ptr);
  extern protected
           virtual function void   m_unregister_sequence(int sequence_id);
  extern protected function
                 uvm_sequence_base m_find_sequence(int sequence_id);

  extern protected function void   m_update_lists();
  extern           function string convert2string();
  extern protected
           virtual function int    m_find_number_driver_connections();
  extern protected task            m_wait_arb_not_equal();
  extern protected task            m_wait_for_available_sequence();
  extern protected function int    m_get_seq_item_priority(uvm_sequence_request seq_q_entry);

  int m_is_relevant_completed;


`ifdef UVM_DISABLE_AUTO_ITEM_RECORDING
  local bit m_auto_item_recording = 0;
`else
  local bit m_auto_item_recording = 1;
`endif


  // Access to following internal methods provided via seq_item_export

  // Function: disable_auto_item_recording
  //
  // Disables auto_item_recording
  // 
  // This function is the actual implementation of the 
  // uvm_sqr_if_base::disable_auto_item_recording() method detailed in
  // IEEE1800.2 section 15.2.1.2.10
  // 
  // This function is implemented here to allow <uvm_push_sequencer#(REQ,RSP)>
  // and <uvm_push_driver#(REQ,RSP)> access to the call.
  //
  virtual function void disable_auto_item_recording();
    m_auto_item_recording = 0;
  endfunction

  // Function: is_auto_item_recording_enabled
  //
  // Returns 1 is auto_item_recording is enabled,
  // otherwise 0
  // 
  // This function is the actual implementation of the 
  // uvm_sqr_if_base::is_auto_item_recording_enabled() method detailed in
  // IEEE1800.2 section 15.2.1.2.11
  // 
  // This function is implemented here to allow <uvm_push_sequencer#(REQ,RSP)>
  // and <uvm_push_driver#(REQ,RSP)> access to the call.
  //
  virtual function bit is_auto_item_recording_enabled();
    return m_auto_item_recording;
  endfunction

  static uvm_sequencer_base all_sequencer_insts[int unsigned];
endclass




//------------------------------------------------------------------------------
// IMPLEMENTATION
//------------------------------------------------------------------------------


// new
// ---

function uvm_sequencer_base::new (string name, uvm_component parent);
  super.new(name, parent);
  m_sequencer_id = g_sequencer_id++;
  m_lock_arb_size = -1;
  all_sequencer_insts[m_sequencer_id]=this;
endfunction


// do_print
// --------

function void uvm_sequencer_base::do_print (uvm_printer printer);
  super.do_print(printer);
  printer.print_array_header("arbitration_queue", arb_sequence_q.size());
  foreach (arb_sequence_q[i])
    printer.print_string($sformatf("[%0d]", i),
       $sformatf("%s@seqid%0d",arb_sequence_q[i].request.name(),arb_sequence_q[i].sequence_id), "[");
  printer.print_array_footer(arb_sequence_q.size());

  printer.print_array_header("lock_queue", lock_list.size());
  foreach(lock_list[i])
    printer.print_string($sformatf("[%0d]", i),
       $sformatf("%s@seqid%0d",lock_list[i].get_full_name(),lock_list[i].get_sequence_id()), "[");
  printer.print_array_footer(lock_list.size());
endfunction


// m_update_lists
// --------------

function void uvm_sequencer_base::m_update_lists();
  m_lock_arb_size++;
endfunction


// convert2string
// ----------------

function string uvm_sequencer_base::convert2string();
  string s;

  $sformat(s, "  -- arb i/id/type: ");
  foreach (arb_sequence_q[i]) begin
    $sformat(s, "%s %0d/%0d/%s ", s, i, arb_sequence_q[i].sequence_id, arb_sequence_q[i].request.name());
  end
  $sformat(s, "%s\n -- lock_list i/id: ", s);
  foreach (lock_list[i]) begin
    $sformat(s, "%s %0d/%0d",s, i, lock_list[i].get_sequence_id());
  end
  return(s);
endfunction



// m_find_number_driver_connections
// --------------------------------

function int  uvm_sequencer_base::m_find_number_driver_connections();
  return 0;
endfunction


// m_register_sequence
// -------------------

function int uvm_sequencer_base::m_register_sequence(uvm_sequence_base sequence_ptr);

  if (sequence_ptr.m_get_sqr_sequence_id(m_sequencer_id, 1) > 0)
    return sequence_ptr.get_sequence_id();

  sequence_ptr.m_set_sqr_sequence_id(m_sequencer_id, g_sequence_id++);
  reg_sequences[sequence_ptr.get_sequence_id()] = sequence_ptr;
  return sequence_ptr.get_sequence_id();
endfunction


// m_find_sequence
// ---------------

function uvm_sequence_base uvm_sequencer_base::m_find_sequence(int sequence_id);
  uvm_sequence_base seq_ptr;
  int           i;

  // When sequence_id is -1, return the first available sequence.  This is used
  // when deleting all sequences
  if (sequence_id == -1) begin
    if (reg_sequences.first(i)) begin
      return(reg_sequences[i]);
    end
    return(null);
  end

  if (!reg_sequences.exists(sequence_id))
    return null;
  return reg_sequences[sequence_id];
endfunction


// m_unregister_sequence
// ---------------------

function void uvm_sequencer_base::m_unregister_sequence(int sequence_id);
  if (!reg_sequences.exists(sequence_id))
    return;
  reg_sequences.delete(sequence_id);
endfunction


// user_priority_arbitration
// -------------------------

function int uvm_sequencer_base::user_priority_arbitration(int avail_sequences[$]);
  return avail_sequences[0];
endfunction


// grant_queued_locks
// ------------------
// Any lock or grab requests that are at the front of the queue will be
// granted at the earliest possible time.  This function grants any queues
// at the front that are not locked out

function void uvm_sequencer_base::grant_queued_locks();
    // remove and report any zombies
    begin
       uvm_sequence_request zombies[$];
       zombies = arb_sequence_q.find(item) with (item.request==SEQ_TYPE_LOCK && item.process_id.status inside {process::KILLED,process::FINISHED});
       foreach(zombies[idx]) begin
          `uvm_error("SEQLCKZMB", $sformatf("The task responsible for requesting a lock on sequencer '%s' for sequence '%s' has been killed, to avoid a deadlock the sequence will be removed from the arbitration queues", this.get_full_name(), zombies[idx].sequence_ptr.get_full_name()))
          remove_sequence_from_queues(zombies[idx].sequence_ptr);
       end
    end
 
    // grant the first lock request that is not blocked, if any
    begin
       int lock_req_indices[$];
       lock_req_indices = arb_sequence_q.find_first_index(item) with (item.request==SEQ_TYPE_LOCK && is_blocked(item.sequence_ptr) == 0);
       if(lock_req_indices.size()) begin
          uvm_sequence_request lock_req = arb_sequence_q[lock_req_indices[0]];
          lock_list.push_back(lock_req.sequence_ptr);
          m_set_arbitration_completed(lock_req.request_id);
          arb_sequence_q.delete(lock_req_indices[0]);
          m_update_lists();
       end
    end
endfunction


// m_select_sequence
// -----------------

task uvm_sequencer_base::m_select_sequence();
   int selected_sequence;

    // Select a sequence
    do begin
      wait_for_sequences();
      selected_sequence = m_choose_next_request();
      if (selected_sequence == -1) begin
        m_wait_for_available_sequence();
      end
    end while (selected_sequence == -1);
    // issue grant
    if (selected_sequence >= 0) begin
      m_set_arbitration_completed(arb_sequence_q[selected_sequence].request_id);
      arb_sequence_q.delete(selected_sequence);
      m_update_lists();
    end
endtask


// m_choose_next_request
// ---------------------
// When a driver requests an operation, this function must find the next
// available, unlocked, relevant sequence.
//
// This function returns -1 if no sequences are available or the entry into
// arb_sequence_q for the chosen sequence

function int uvm_sequencer_base::m_choose_next_request();
  int i, temp;
  int avail_sequence_count;
  int sum_priority_val;
  int avail_sequences[$];
  int highest_sequences[$];
  int highest_pri;
  string  s;

  avail_sequence_count = 0;

  grant_queued_locks();

  i = 0;
  while (i < arb_sequence_q.size()) begin
     if ((arb_sequence_q[i].process_id.status == process::KILLED) ||
         (arb_sequence_q[i].process_id.status == process::FINISHED)) begin
        `uvm_error("SEQREQZMB", $sformatf("The task responsible for requesting a wait_for_grant on sequencer '%s' for sequence '%s' has been killed, to avoid a deadlock the sequence will be removed from the arbitration queues", this.get_full_name(), arb_sequence_q[i].sequence_ptr.get_full_name()))
         remove_sequence_from_queues(arb_sequence_q[i].sequence_ptr);
         continue;
     end

    if (i < arb_sequence_q.size())
      if (arb_sequence_q[i].request == SEQ_TYPE_REQ)
        if (is_blocked(arb_sequence_q[i].sequence_ptr) == 0)
          if (arb_sequence_q[i].sequence_ptr.is_relevant() == 1) begin
            if (m_arbitration == UVM_SEQ_ARB_FIFO) begin
              return i;
            end
            else avail_sequences.push_back(i);
          end

    i++;
  end

  // Return immediately if there are 0 or 1 available sequences
  if (m_arbitration == UVM_SEQ_ARB_FIFO) begin
    return -1;
  end
  if (avail_sequences.size() < 1)  begin
    return -1;
  end

  if (avail_sequences.size() == 1) begin
    return avail_sequences[0];
  end

  // If any locks are in place, then the available queue must
  // be checked to see if a lock prevents any sequence from proceeding
  if (lock_list.size() > 0) begin
    for (i = 0; i < avail_sequences.size(); i++) begin
      if (is_blocked(arb_sequence_q[avail_sequences[i]].sequence_ptr) != 0) begin
        avail_sequences.delete(i);
        i--;
      end
    end
    if (avail_sequences.size() < 1)
      return -1;
    if (avail_sequences.size() == 1)
      return avail_sequences[0];
  end

  //  Weighted Priority Distribution
  // Pick an available sequence based on weighted priorities of available sequences
  if (m_arbitration == UVM_SEQ_ARB_WEIGHTED) begin
    sum_priority_val = 0;
    for (i = 0; i < avail_sequences.size(); i++) begin
      sum_priority_val += m_get_seq_item_priority(arb_sequence_q[avail_sequences[i]]);
    end

    temp = $urandom_range(sum_priority_val-1, 0);

    sum_priority_val = 0;
    for (i = 0; i < avail_sequences.size(); i++) begin
      if ((m_get_seq_item_priority(arb_sequence_q[avail_sequences[i]]) +
           sum_priority_val) > temp) begin
        return avail_sequences[i];
      end
      sum_priority_val += m_get_seq_item_priority(arb_sequence_q[avail_sequences[i]]);
    end
    uvm_report_fatal("Sequencer", "UVM Internal error in weighted arbitration code", UVM_NONE);
  end

  //  Random Distribution
  if (m_arbitration == UVM_SEQ_ARB_RANDOM) begin
    i = $urandom_range(avail_sequences.size()-1, 0);
    return avail_sequences[i];
  end

  //  Strict Fifo
  if ((m_arbitration == UVM_SEQ_ARB_STRICT_FIFO) || m_arbitration == UVM_SEQ_ARB_STRICT_RANDOM) begin
    highest_pri = 0;
    // Build a list of sequences at the highest priority
    for (i = 0; i < avail_sequences.size(); i++) begin
      if (m_get_seq_item_priority(arb_sequence_q[avail_sequences[i]]) > highest_pri) begin
        // New highest priority, so start new list
        highest_sequences.delete();
        highest_sequences.push_back(avail_sequences[i]);
        highest_pri = m_get_seq_item_priority(arb_sequence_q[avail_sequences[i]]);
      end
      else if (m_get_seq_item_priority(arb_sequence_q[avail_sequences[i]]) == highest_pri) begin
        highest_sequences.push_back(avail_sequences[i]);
      end
    end

    // Now choose one based on arbitration type
    if (m_arbitration == UVM_SEQ_ARB_STRICT_FIFO) begin
      return(highest_sequences[0]);
    end

    i = $urandom_range(highest_sequences.size()-1, 0);
    return highest_sequences[i];
  end

  if (m_arbitration == UVM_SEQ_ARB_USER) begin
    i = user_priority_arbitration( avail_sequences);

    // Check that the returned sequence is in the list of available sequences.  Failure to
    // use an available sequence will cause highly unpredictable results.
    highest_sequences = avail_sequences.find with (item == i);
    if (highest_sequences.size() == 0) begin
      uvm_report_fatal("Sequencer",
          $sformatf("Error in User arbitration, sequence %0d not available\n%s",
                    i, convert2string()), UVM_NONE);
    end
    return(i);
  end

  uvm_report_fatal("Sequencer", "Internal error: Failed to choose sequence", UVM_NONE);

endfunction


// m_wait_arb_not_equal
// --------------------

task uvm_sequencer_base::m_wait_arb_not_equal();
  wait (m_arb_size != m_lock_arb_size);
endtask


// m_wait_for_available_sequence
// -----------------------------

task uvm_sequencer_base::m_wait_for_available_sequence();
  int i;
  int is_relevant_entries[$];

  // This routine will wait for a change in the request list, or for
  // wait_for_relevant to return on any non-relevant, non-blocked sequence
  m_arb_size = m_lock_arb_size;

  for (i = 0; i < arb_sequence_q.size(); i++) begin
    if (arb_sequence_q[i].request == SEQ_TYPE_REQ) begin
      if (is_blocked(arb_sequence_q[i].sequence_ptr) == 0) begin
        if (arb_sequence_q[i].sequence_ptr.is_relevant() == 0) begin
          is_relevant_entries.push_back(i);
        end
      end
    end
  end

  // Typical path - don't need fork if all queued entries are relevant
  if (is_relevant_entries.size() == 0) begin
    m_wait_arb_not_equal();
    return;
  end

  fork  // isolate inner fork block for disabling
    begin
      fork
        begin
          fork
              begin
                // One path in fork is for any wait_for_relevant to return
                m_is_relevant_completed = 0;

                for(i = 0; i < is_relevant_entries.size(); i++) begin
                fork
                    automatic int k = i;

                  begin
                    arb_sequence_q[is_relevant_entries[k]].sequence_ptr.wait_for_relevant();
                    if ($realtime != m_last_wait_relevant_time) begin
                       m_last_wait_relevant_time = $realtime ;
                       m_wait_relevant_count = 0 ;
                    end
                    else begin
                       m_wait_relevant_count++ ;
                       if (m_wait_relevant_count > m_max_zero_time_wait_relevant_count) begin
                          `uvm_fatal("SEQRELEVANTLOOP",$sformatf("Zero time loop detected, passed wait_for_relevant %0d times without time advancing",m_wait_relevant_count))
                       end
                    end
                    m_is_relevant_completed = 1;
                  end
                join_none

                end
                wait (m_is_relevant_completed > 0);
              end

            // The other path in the fork is for any queue entry to change
            begin
              m_wait_arb_not_equal();
            end
          join_any
        end
      join_any
      disable fork;
    end
  join
endtask


// m_get_seq_item_priority
// -----------------------

function int uvm_sequencer_base::m_get_seq_item_priority(uvm_sequence_request seq_q_entry);
  // If the priority was set on the item, then that is used
  if (seq_q_entry.item_priority != -1) begin
    if (seq_q_entry.item_priority <= 0) begin
      uvm_report_fatal("SEQITEMPRI",
                    $sformatf("Sequence item from %s has illegal priority: %0d",
                            seq_q_entry.sequence_ptr.get_full_name(),
                            seq_q_entry.item_priority), UVM_NONE);
    end
    return seq_q_entry.item_priority;
  end
  // Otherwise, use the priority of the calling sequence
  if (seq_q_entry.sequence_ptr.get_priority() < 0) begin
    uvm_report_fatal("SEQDEFPRI",
                    $sformatf("Sequence %s has illegal priority: %0d",
                            seq_q_entry.sequence_ptr.get_full_name(),
                            seq_q_entry.sequence_ptr.get_priority()), UVM_NONE);
  end
  return seq_q_entry.sequence_ptr.get_priority();
endfunction


// m_wait_for_arbitration_completed
// --------------------------------

task uvm_sequencer_base::m_wait_for_arbitration_completed(int request_id);
  int lock_arb_size;

  // Search the list of arb_wait_q, see if this item is done
  forever
    begin
      lock_arb_size  = m_lock_arb_size;

      if (arb_completed.exists(request_id)) begin
        arb_completed.delete(request_id);
        return;
      end
      wait (lock_arb_size != m_lock_arb_size);
    end
endtask


// m_set_arbitration_completed
// ---------------------------

function void uvm_sequencer_base::m_set_arbitration_completed(int request_id);
  arb_completed[request_id] = 1;
endfunction


// is_child
// --------

function bit uvm_sequencer_base::is_child (uvm_sequence_base parent,
                                           uvm_sequence_base child);
  uvm_sequence_base child_parent;

  if (child == null) begin
    uvm_report_fatal("uvm_sequencer", "is_child passed null child", UVM_NONE);
  end

  if (parent == null) begin
    uvm_report_fatal("uvm_sequencer", "is_child passed null parent", UVM_NONE);
  end

  child_parent = child.get_parent_sequence();
  while (child_parent != null) begin
    if (child_parent.get_inst_id() == parent.get_inst_id()) begin
      return 1;
    end
    child_parent = child_parent.get_parent_sequence();
  end
  return 0;
endfunction


// execute_item
// ------------

// Implementation artifact, extends virtual class uvm_sequence_base
// so that it can be constructed for execute_item
class m_uvm_sqr_seq_base extends uvm_sequence_base;
   function new(string name="unnamed-m_uvm_sqr_seq_base");
      super.new(name);
   endfunction : new
endclass : m_uvm_sqr_seq_base
   
task uvm_sequencer_base::execute_item(uvm_sequence_item item);
  m_uvm_sqr_seq_base seq;

  seq = new("execute_item_seq");
  item.set_sequencer(this);
  item.set_parent_sequence(seq);
  seq.set_sequencer(this);
  seq.start_item(item);
  seq.finish_item(item);
endtask


// wait_for_grant
// --------------

task uvm_sequencer_base::wait_for_grant(uvm_sequence_base sequence_ptr,
                                        int item_priority = -1,
                                        bit lock_request = 0);
  uvm_sequence_request req_s;
  int my_seq_id;

  if (sequence_ptr == null)
    uvm_report_fatal("uvm_sequencer",
       "wait_for_grant passed null sequence_ptr", UVM_NONE);

  my_seq_id = m_register_sequence(sequence_ptr);

  // If lock_request is asserted, then issue a lock.  Don't wait for the response, since
  // there is a request immediately following the lock request
  if (lock_request == 1) begin
    req_s = new();
    req_s.grant = 0;
    req_s.sequence_id = my_seq_id;
    req_s.request = SEQ_TYPE_LOCK;
    req_s.sequence_ptr = sequence_ptr;
    req_s.request_id = g_request_id++;
    req_s.process_id = process::self();
    arb_sequence_q.push_back(req_s);
  end

  // Push the request onto the queue
  req_s = new();
  req_s.grant = 0;
  req_s.request = SEQ_TYPE_REQ;
  req_s.sequence_id = my_seq_id;
  req_s.item_priority = item_priority;
  req_s.sequence_ptr = sequence_ptr;
  req_s.request_id = g_request_id++;
  req_s.process_id = process::self();
  arb_sequence_q.push_back(req_s);
  m_update_lists();

  // Wait until this entry is granted
  // Continue to point to the element, since location in queue will change
  m_wait_for_arbitration_completed(req_s.request_id);

  // The wait_for_grant_semaphore is used only to check that send_request
  // is only called after wait_for_grant.  This is not a complete check, since
  // requests might be done in parallel, but it will catch basic errors
  req_s.sequence_ptr.m_wait_for_grant_semaphore++;

endtask


// wait_for_item_done
// ------------------

task uvm_sequencer_base::wait_for_item_done(uvm_sequence_base sequence_ptr,
                                            int transaction_id);
  int sequence_id;

  sequence_id = sequence_ptr.m_get_sqr_sequence_id(m_sequencer_id, 1);
  m_wait_for_item_sequence_id = -1;
  m_wait_for_item_transaction_id = -1;

  if (transaction_id == -1)
    wait (m_wait_for_item_sequence_id == sequence_id);
  else
    wait ((m_wait_for_item_sequence_id == sequence_id &&
           m_wait_for_item_transaction_id == transaction_id));
endtask


// is_blocked
// ----------

function bit uvm_sequencer_base::is_blocked(uvm_sequence_base sequence_ptr);

  if (sequence_ptr == null)
    uvm_report_fatal("uvm_sequence_controller",
                     "is_blocked passed null sequence_ptr", UVM_NONE);

    foreach (lock_list[i]) begin
      if ((lock_list[i].get_inst_id() !=
           sequence_ptr.get_inst_id()) &&
          (is_child(lock_list[i], sequence_ptr) == 0)) begin
        return 1;
      end
    end
    return 0;
endfunction


// has_lock
// --------

function bit uvm_sequencer_base::has_lock(uvm_sequence_base sequence_ptr);
  int my_seq_id;

  if (sequence_ptr == null)
    uvm_report_fatal("uvm_sequence_controller",
                     "has_lock passed null sequence_ptr", UVM_NONE);
  my_seq_id = m_register_sequence(sequence_ptr);
    foreach (lock_list[i]) begin
      if (lock_list[i].get_inst_id() == sequence_ptr.get_inst_id()) begin
        return 1;
      end
    end
  return 0;
endfunction


// m_lock_req
// ----------
// Internal method. Called by a sequence to request a lock.
// Puts the lock request onto the arbitration queue.

task uvm_sequencer_base::m_lock_req(uvm_sequence_base sequence_ptr, bit lock);
  int my_seq_id;
  uvm_sequence_request new_req;

  if (sequence_ptr == null)
    uvm_report_fatal("uvm_sequence_controller",
                     "lock_req passed null sequence_ptr", UVM_NONE);

  my_seq_id = m_register_sequence(sequence_ptr);
  new_req = new();
  new_req.grant = 0;
  new_req.sequence_id = sequence_ptr.get_sequence_id();
  new_req.request = SEQ_TYPE_LOCK;
  new_req.sequence_ptr = sequence_ptr;
  new_req.request_id = g_request_id++;
  new_req.process_id = process::self();

  if (lock == 1) begin
    // Locks are arbitrated just like all other requests
    arb_sequence_q.push_back(new_req);
  end else begin
    // Grabs are not arbitrated - they go to the front
    // TODO:
    // Missing: grabs get arbitrated behind other grabs
    arb_sequence_q.push_front(new_req);
    m_update_lists();
  end

  // If this lock can be granted immediately, then do so.
  grant_queued_locks();

  m_wait_for_arbitration_completed(new_req.request_id);
endtask


// m_unlock_req
// ------------
// Called by a sequence to request an unlock.  This
// will remove a lock for this sequence if it exists

function void uvm_sequencer_base::m_unlock_req(uvm_sequence_base sequence_ptr);
  if (sequence_ptr == null) begin
    uvm_report_fatal("uvm_sequencer",
                     "m_unlock_req passed null sequence_ptr", UVM_NONE);
  end

  begin
	  int q[$];
	  int seqid=sequence_ptr.get_inst_id();
	  q=lock_list.find_first_index(item) with (item.get_inst_id() == seqid);
	  if(q.size()==1) begin
	      lock_list.delete(q[0]);
		  grant_queued_locks(); // grant lock requests
		  m_update_lists();
	  end
	  else
		  uvm_report_warning("SQRUNL",
           {"Sequence '", sequence_ptr.get_full_name(),
            "' called ungrab / unlock, but didn't have lock"}, UVM_NONE);

  end
endfunction


// lock
// ----

task uvm_sequencer_base::lock(uvm_sequence_base sequence_ptr);
  m_lock_req(sequence_ptr, 1);
endtask


// grab
// ----

task uvm_sequencer_base::grab(uvm_sequence_base sequence_ptr);
  m_lock_req(sequence_ptr, 0);
endtask


// unlock
// ------

function void uvm_sequencer_base::unlock(uvm_sequence_base sequence_ptr);
  m_unlock_req(sequence_ptr);
endfunction


// ungrab
// ------

function void  uvm_sequencer_base::ungrab(uvm_sequence_base sequence_ptr);
  m_unlock_req(sequence_ptr);
endfunction


// remove_sequence_from_queues
// ---------------------------

function void uvm_sequencer_base::remove_sequence_from_queues(
                                       uvm_sequence_base sequence_ptr);
  int i;
  int seq_id;

  seq_id = sequence_ptr.m_get_sqr_sequence_id(m_sequencer_id, 0);

  // Remove all queued items for this sequence and any child sequences
  i = 0;
  do
    begin
      if (arb_sequence_q.size() > i) begin
        if ((arb_sequence_q[i].sequence_id == seq_id) ||
            (is_child(sequence_ptr, arb_sequence_q[i].sequence_ptr))) begin
          if (sequence_ptr.get_sequence_state() == UVM_FINISHED)
            `uvm_error("SEQFINERR", $sformatf("Parent sequence '%s' should not finish before all items from itself and items from descendent sequences are processed.  The item request from the sequence '%s' is being removed.", sequence_ptr.get_full_name(), arb_sequence_q[i].sequence_ptr.get_full_name()))
          arb_sequence_q.delete(i);
          m_update_lists();
        end
        else begin
          i++;
        end
      end
    end
  while (i < arb_sequence_q.size());

  // remove locks for this sequence, and any child sequences
  i = 0;
  do
    begin
      if (lock_list.size() > i) begin
        if ((lock_list[i].get_inst_id() == sequence_ptr.get_inst_id()) ||
            (is_child(sequence_ptr, lock_list[i]))) begin
          if (sequence_ptr.get_sequence_state() == UVM_FINISHED)
            `uvm_error("SEQFINERR", $sformatf("Parent sequence '%s' should not finish before locks from itself and descedent sequences are removed.  The lock held by the child sequence '%s' is being removed.",sequence_ptr.get_full_name(), lock_list[i].get_full_name()))
          lock_list.delete(i);
          m_update_lists();
        end
        else begin
          i++;
        end
      end
    end
  while (i < lock_list.size());

  // Unregister the sequence_id, so that any returning data is dropped
  m_unregister_sequence(sequence_ptr.m_get_sqr_sequence_id(m_sequencer_id, 1));
endfunction


// stop_sequences
// --------------

function void uvm_sequencer_base::stop_sequences();
  uvm_sequence_base seq_ptr;

  seq_ptr = m_find_sequence(-1);
  while (seq_ptr != null)
    begin
      kill_sequence(seq_ptr);
      seq_ptr = m_find_sequence(-1);
    end
endfunction


// m_sequence_exiting
// ------------------

function void uvm_sequencer_base::m_sequence_exiting(uvm_sequence_base sequence_ptr);
  remove_sequence_from_queues(sequence_ptr);
endfunction


// kill_sequence
// -------------

function void uvm_sequencer_base::kill_sequence(uvm_sequence_base sequence_ptr);
  remove_sequence_from_queues(sequence_ptr);
  sequence_ptr.m_kill();
endfunction


// is_grabbed
// ----------

function bit uvm_sequencer_base::is_grabbed();
  return (lock_list.size() != 0);
endfunction


// current_grabber
// ---------------

function uvm_sequence_base uvm_sequencer_base::current_grabber();
  if (lock_list.size() == 0) begin
    return null;
  end
  return lock_list[lock_list.size()-1];
endfunction


// has_do_available
// ----------------

function bit uvm_sequencer_base::has_do_available();

  foreach (arb_sequence_q[i]) begin
    if ((arb_sequence_q[i].sequence_ptr.is_relevant() == 1) &&
        (is_blocked(arb_sequence_q[i].sequence_ptr) == 0)) begin
      return 1;
    end
  end
  return 0;
endfunction


// set_arbitration
// ---------------

function void uvm_sequencer_base::set_arbitration(UVM_SEQ_ARB_TYPE val);
  m_arbitration = val;
endfunction


// get_arbitration
// ---------------

function UVM_SEQ_ARB_TYPE uvm_sequencer_base::get_arbitration();
  return m_arbitration;
endfunction

// get_arbitration_sequence
// ---------------
function uvm_sequence_base uvm_sequencer_base::get_arbitration_sequence( int index);
  return arb_sequence_q[index].sequence_ptr;
endfunction


// analysis_write
// --------------

function void uvm_sequencer_base::analysis_write(uvm_sequence_item t);
  return;
endfunction


// wait_for_sequences
// ------------------

task uvm_sequencer_base::wait_for_sequences();
  uvm_wait_for_nba_region();
endtask



// send_request
// ------------

function void uvm_sequencer_base::send_request(uvm_sequence_base sequence_ptr,
                                               uvm_sequence_item t,
                                               bit rerandomize = 0);
  return;
endfunction


// set_max_zero_time_wait_relevant_count
// ------------

function void uvm_sequencer_base::set_max_zero_time_wait_relevant_count(int new_val) ;
   m_max_zero_time_wait_relevant_count = new_val ;
endfunction


// start_phase_sequence
// --------------------

function void uvm_sequencer_base::start_phase_sequence(uvm_phase phase);
  uvm_resource_pool            rp = uvm_resource_pool::get();
  uvm_resource_types::rsrc_q_t rq;
  uvm_sequence_base            seq;
  uvm_coreservice_t cs = uvm_coreservice_t::get();
  uvm_factory                  f = cs.get_factory();

  // Has a default sequence been specified?
  rq = rp.lookup_name({get_full_name(), ".", phase.get_name(), "_phase"},
                      "default_sequence", null, 0);
  uvm_resource_pool::sort_by_precedence(rq);

  // Look for the first one if the appropriate type
  for (int i = 0; seq == null && i < rq.size(); i++) begin
    uvm_resource_base rsrc = rq.get(i);

    uvm_resource#(uvm_sequence_base)  sbr;
    uvm_resource#(uvm_object_wrapper) owr;

    // uvm_config_db#(uvm_sequence_base)?
    // Priority is given to uvm_sequence_base because it is a specific sequence instance
    // and thus more specific than one that is dynamically created via the
    // factory and the object wrapper.
    if ($cast(sbr, rsrc) && sbr != null) begin
      seq = sbr.read(this);
      if (seq == null) begin
        `uvm_info("UVM/SQR/PH/DEF/SB/NULL", {"Default phase sequence for phase '",
                                             phase.get_name(),"' explicitly disabled"}, UVM_FULL)
        return;
      end
    end

    // uvm_config_db#(uvm_object_wrapper)?
    else if ($cast(owr, rsrc) && owr != null) begin
      uvm_object_wrapper wrapper;

      wrapper = owr.read(this);
      if (wrapper == null) begin
        `uvm_info("UVM/SQR/PH/DEF/OW/NULL", {"Default phase sequence for phase '",
                                             phase.get_name(),"' explicitly disabled"}, UVM_FULL)
        return;
      end

      if (!$cast(seq, f.create_object_by_type(wrapper, get_full_name(),
                                              wrapper.get_type_name()))
          || seq == null) begin
        `uvm_warning("PHASESEQ", {"Default sequence for phase '",
                                  phase.get_name(),"' %s is not a sequence type"})
        return;
      end
    end
  end

  if (seq == null) begin
    `uvm_info("PHASESEQ", {"No default phase sequence for phase '",
                           phase.get_name(),"'"}, UVM_FULL)
    return;
  end

  `uvm_info("PHASESEQ", {"Starting default sequence '",
                         seq.get_type_name(),"' for phase '", phase.get_name(),"'"}, UVM_FULL)

  seq.print_sequence_info = 1;
  seq.set_sequencer(this);
  seq.reseed();
  seq.set_starting_phase(phase);

  if (seq.get_randomize_enabled() && !seq.randomize()) begin
    `uvm_warning("STRDEFSEQ", {"Randomization failed for default sequence '",
                               seq.get_type_name(),"' for phase '", phase.get_name(),"'"})
    return;
  end

  fork begin
    uvm_sequence_process_wrapper w = new();
    // reseed this process for random stability
    w.pid = process::self();
    w.seq = seq;
    w.pid.srandom(uvm_create_random_seed(seq.get_type_name(), this.get_full_name()));
    m_default_sequences[phase] = w;
    // this will either complete naturally, or be killed later
    seq.start(this);
    m_default_sequences.delete(phase);
  end
  join_none

endfunction

// stop_phase_sequence
// --------------------

function void uvm_sequencer_base::stop_phase_sequence(uvm_phase phase);
    if (m_default_sequences.exists(phase)) begin
        `uvm_info("PHASESEQ",
                  {"Killing default sequence '", m_default_sequences[phase].seq.get_type_name(),
                   "' for phase '", phase.get_name(), "'"}, UVM_FULL)
        m_default_sequences[phase].seq.kill();
    end
    else begin
        `uvm_info("PHASESEQ",
                  {"No default sequence to kill for phase '", phase.get_name(), "'"},
                  UVM_FULL)
    end
endfunction : stop_phase_sequence

//------------------------------------------------------------------------------
//
// Class- uvm_sequence_request
//
//------------------------------------------------------------------------------

class uvm_sequence_request;
  bit        grant;
  int        sequence_id;
  int        request_id;
  int        item_priority;
  process    process_id;
  uvm_sequencer_base::seq_req_t  request;
  uvm_sequence_base sequence_ptr;
endclass
