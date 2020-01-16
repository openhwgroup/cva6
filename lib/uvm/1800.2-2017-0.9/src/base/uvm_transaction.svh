//
//-----------------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2010-2013 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2010 AMD
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2014-2017 Cisco Systems, Inc.
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

typedef class uvm_event;
typedef class uvm_event_pool;
typedef class uvm_component;
typedef class uvm_parent_child_link;
    
//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_transaction
//
// The uvm_transaction class is the root base class for UVM transactions.
// Inheriting all the methods of <uvm_object>, uvm_transaction adds a timing and
// recording interface.
//
// This class provides timestamp properties, notification events, and transaction
// recording support. 
//
// Use of this class as a base for user-defined transactions
// is deprecated. Its subtype, <uvm_sequence_item>, shall be used as the
// base class for all user-defined transaction types. 
// 
// The intended use of this API is via a <uvm_driver #(REQ,RSP)> to call <uvm_component::accept_tr>,
// <uvm_component::begin_tr>, and <uvm_component::end_tr> during the course of
// sequence item execution. These methods in the component base class will
// call into the corresponding methods in this class to set the corresponding
// timestamps (~accept_time~, ~begin_time~, and ~end_time~), trigger the
// corresponding event (<begin_event> and <end_event>, and, if enabled,
// record the transaction contents to a vendor-specific transaction database.
//
// Note that get_next_item/item_done when called on a uvm_seq_item_pull_port
// will automatically trigger the begin_event and end_events via calls to begin_tr and end_tr.
// While convenient, it is generally the responsibility of drivers to mark a
// transaction's progress during execution.  To allow the driver or layering sequence
// to control sequence item timestamps, events, and recording, you must call
// <uvm_sqr_if_base#(REQ,RSP)::disable_auto_item_recording> at the beginning
// of the driver's ~run_phase~ task.
//
// Users may also use the transaction's event pool, <events>,
// to define custom events for the driver to trigger and the sequences to wait on. Any
// in-between events such as marking the beginning of the address and data
// phases of transaction execution could be implemented via the
// <events> pool.
// 
// In pipelined protocols, the driver may release a sequence (return from
// finish_item() or it's `uvm_do macro) before the item has been completed.
// If the driver uses the begin_tr/end_tr API in uvm_component, the sequence can
// wait on the item's <end_event> to block until the item was fully executed,
// as in the following example.
//
//| task uvm_execute(item, ...);
//|     // can use the `uvm_do macros as well
//|     start_item(item);
//|     item.randomize();
//|     finish_item(item);
//|     item.end_event.wait_on();
//|     // get_response(rsp, item.get_transaction_id()); //if needed
//| endtask
//|
//
// A simple two-stage pipeline driver that can execute address and
// data phases concurrently might be implemented as follows: 
//
//| task run();
//|     // this driver supports a two-deep pipeline
//|     fork
//|       do_item();
//|       do_item();
//|     join
//| endtask
//| 
//| 
//| task do_item();
//|     
//|   forever begin
//|     mbus_item req;
//|
//|     lock.get();
//|
//|     seq_item_port.get(req); // Completes the sequencer-driver handshake
//|
//|     accept_tr(req);
//|
//|       // request bus, wait for grant, etc.
//| 
//|     begin_tr(req);
//|
//|       // execute address phase
//|
//|     // allows next transaction to begin address phase
//|     lock.put();
//| 
//|       // execute data phase
//|       // (may trigger custom "data_phase" event here)
//| 
//|     end_tr(req);
//| 
//|   end
//| 
//| endtask: do_item
//
//------------------------------------------------------------------------------
    
// @uvm-ieee 1800.2-2017 auto 5.4.1
virtual class uvm_transaction extends uvm_object;

  // Function -- NODOCS -- new
  //
  // Creates a new transaction object. The name is the instance name of the
  // transaction. If not supplied, then the object is unnamed.
  
  // @uvm-ieee 1800.2-2017 auto 5.4.2.1
  extern function new (string name="", uvm_component initiator=null);


  // Function -- NODOCS -- accept_tr
  //
  // Calling ~accept_tr~ indicates that the transaction item has been received by
  // a consumer component. Typically a <uvm_driver #(REQ,RSP)> would call <uvm_component::accept_tr>,
  // which calls this method-- upon return from a ~get_next_item()~, ~get()~, or ~peek()~
  // call on its sequencer port, <uvm_driver#(REQ,RSP)::seq_item_port>.
  //
  // With some
  // protocols, the received item may not be started immediately after it is
  // accepted. For example, a bus driver, having accepted a request transaction,
  // may still have to wait for a bus grant before beginning to execute
  // the request.
  //
  // This function performs the following actions:
  //
  // - The transaction's internal accept time is set to the current simulation
  //   time, or to accept_time if provided and non-zero. The ~accept_time~ may be
  //   any time, past or future.
  //
  // - The transaction's internal accept event is triggered. Any processes
  //   waiting on the this event will resume in the next delta cycle. 
  //
  // - The <do_accept_tr> method is called to allow for any post-accept
  //   action in derived classes.

  // @uvm-ieee 1800.2-2017 auto 5.4.2.2
  extern function void accept_tr (time accept_time = 0);

  
  // Function -- NODOCS -- do_accept_tr
  //
  // This user-definable callback is called by <accept_tr> just before the accept
  // event is triggered. Implementations should call ~super.do_accept_tr~ to
  // ensure correct operation.

  // @uvm-ieee 1800.2-2017 auto 5.4.2.3
  extern virtual protected function void do_accept_tr ();


  // Function -- NODOCS -- begin_tr
  //
  // This function indicates that the transaction has been started and is not
  // the child of another transaction. Generally, a consumer component begins
  // execution of a transactions it receives. 
  //
  // Typically a <uvm_driver #(REQ,RSP)> would call <uvm_component::begin_tr>, which
  // calls this method, before actual execution of a sequence item transaction.
  // Sequence items received by a driver are always a child of a parent sequence.
  // In this case, begin_tr obtains the parent handle and delegates to <begin_child_tr>.
  //
  // See <accept_tr> for more information on how the
  // begin-time might differ from when the transaction item was received.
  //
  // This function performs the following actions:
  //
  // - The transaction's internal start time is set to the current simulation
  //   time, or to begin_time if provided and non-zero. The begin_time may be
  //   any time, past or future, but should not be less than the accept time.
  //
  // - If recording is enabled, then a new database-transaction is started with
  //   the same begin time as above.
  //
  // - The <do_begin_tr> method is called to allow for any post-begin action in
  //   derived classes.
  //
  // - The transaction's internal begin event is triggered. Any processes
  //   waiting on this event will resume in the next delta cycle. 
  //
  // The return value is a transaction handle, which is valid (non-zero) only if
  // recording is enabled. The meaning of the handle is implementation specific.


  // @uvm-ieee 1800.2-2017 auto 5.4.2.4
  extern function int begin_tr (time begin_time = 0);

  
  // Function -- NODOCS -- begin_child_tr
  //
  // This function indicates that the transaction has been started as a child of
  // a parent transaction given by ~parent_handle~. Generally, a consumer
  // component calls this method via <uvm_component::begin_child_tr> to indicate
  // the actual start of execution of this transaction.
  //
  // The parent handle is obtained by a previous call to begin_tr or
  // begin_child_tr. If the parent_handle is invalid (=0), then this function
  // behaves the same as <begin_tr>. 
  //
  // This function performs the following actions:
  //
  // - The transaction's internal start time is set to the current simulation
  //   time, or to begin_time if provided and non-zero. The begin_time may be
  //   any time, past or future, but should not be less than the accept time.
  //
  // - If recording is enabled, then a new database-transaction is started with
  //   the same begin time as above. The inherited <uvm_object::record> method
  //   is then called, which records the current property values to this new
  //   transaction. Finally, the newly started transaction is linked to the
  //   parent transaction given by parent_handle.
  //
  // - The <do_begin_tr> method is called to allow for any post-begin
  //   action in derived classes.
  //
  // - The transaction's internal begin event is triggered. Any processes
  //   waiting on this event will resume in the next delta cycle. 
  //
  // The return value is a transaction handle, which is valid (non-zero) only if
  // recording is enabled. The meaning of the handle is implementation specific.

  // @uvm-ieee 1800.2-2017 auto 5.4.2.5
  extern function int begin_child_tr (time begin_time = 0, 
                                               int parent_handle = 0);


  // Function -- NODOCS -- do_begin_tr
  //
  // This user-definable callback is called by <begin_tr> and <begin_child_tr> just
  // before the begin event is triggered. Implementations should call
  // ~super.do_begin_tr~ to ensure correct operation.

  // @uvm-ieee 1800.2-2017 auto 5.4.2.6
  extern virtual protected function void do_begin_tr ();


  // Function -- NODOCS -- end_tr
  //
  // This function indicates that the transaction execution has ended.
  // Generally, a consumer component ends execution of the transactions it
  // receives. 
  //
  // You must have previously called <begin_tr> or <begin_child_tr> for this
  // call to be successful.
  //
  // Typically a <uvm_driver #(REQ,RSP)> would call <uvm_component::end_tr>, which
  // calls this method, upon completion of a sequence item transaction.
  // Sequence items received by a driver are always a child of a parent sequence.
  // In this case, begin_tr obtain the parent handle and delegate to <begin_child_tr>.
  //
  // This function performs the following actions:
  //
  // - The transaction's internal end time is set to the current simulation
  //   time, or to ~end_time~ if provided and non-zero. The ~end_time~ may be any
  //   time, past or future, but should not be less than the begin time.
  //
  // - If recording is enabled and a database-transaction is currently active,
  //   then the record method inherited from uvm_object is called, which records
  //   the final property values. The transaction is then ended. If ~free_handle~
  //   is set, the transaction is released and can no longer be linked to (if
  //   supported by the implementation).
  //
  // - The <do_end_tr> method is called to allow for any post-end
  //   action in derived classes.
  //
  // - The transaction's internal end event is triggered. Any processes waiting
  //   on this event will resume in the next delta cycle. 

  // @uvm-ieee 1800.2-2017 auto 5.4.2.7
  extern function void end_tr (time end_time=0, bit free_handle=1);


  // Function -- NODOCS -- do_end_tr
  //
  // This user-definable callback is called by <end_tr> just before the end event
  // is triggered. Implementations should call ~super.do_end_tr~ to ensure correct
  // operation.

  // @uvm-ieee 1800.2-2017 auto 5.4.2.8
  extern virtual protected function void do_end_tr ();


  // Function -- NODOCS -- get_tr_handle
  //
  // Returns the handle associated with the transaction, as set by a previous
  // call to <begin_child_tr> or <begin_tr> with transaction recording enabled.

  // @uvm-ieee 1800.2-2017 auto 5.4.2.9
  extern function int get_tr_handle ();

  
  // Function -- NODOCS -- disable_recording
  //
  // Turns off recording for the transaction stream. This method does not
  // effect a <uvm_component>'s recording streams.

  // @uvm-ieee 1800.2-2017 auto 5.4.2.11
  extern function void disable_recording ();


  // @uvm-ieee 1800.2-2017 auto 5.4.2.10
  extern function void enable_recording (uvm_tr_stream stream);

  // Function -- NODOCS -- is_recording_enabled
  //
  // Returns 1 if recording is currently on, 0 otherwise.

  // @uvm-ieee 1800.2-2017 auto 5.4.2.12
  extern function bit is_recording_enabled();

  
  // Function -- NODOCS -- is_active
  //
  // Returns 1 if the transaction has been started but has not yet been ended.
  // Returns 0 if the transaction has not been started.

  // @uvm-ieee 1800.2-2017 auto 5.4.2.13
  extern function bit is_active ();


  // Function -- NODOCS -- get_event_pool
  //
  // Returns the event pool associated with this transaction. 
  //
  // By default, the event pool contains the events: begin, accept, and end.
  // Events can also be added by derivative objects. An event pool is a
  // specialization of <uvm_pool#(KEY,T)>, e.g. a ~uvm_pool#(uvm_event)~.

  // @uvm-ieee 1800.2-2017 auto 5.4.2.14
  extern function uvm_event_pool get_event_pool ();


  // Function -- NODOCS -- set_initiator
  //
  // Sets initiator as the initiator of this transaction. 
  //
  // The initiator can be the component that produces the transaction. It can
  // also be the component that started the transaction. This or any other
  // usage is up to the transaction designer.

  // @uvm-ieee 1800.2-2017 auto 5.4.2.15
  extern function void set_initiator (uvm_component initiator);

  
  // Function -- NODOCS -- get_initiator
  //
  // Returns the component that produced or started the transaction, as set by
  // a previous call to set_initiator.

  // @uvm-ieee 1800.2-2017 auto 5.4.2.16
  extern function uvm_component get_initiator ();


  // Function -- NODOCS -- get_accept_time

  // @uvm-ieee 1800.2-2017 auto 5.4.2.17
  extern function time   get_accept_time    ();

  // Function -- NODOCS -- get_begin_time

  // @uvm-ieee 1800.2-2017 auto 5.4.2.17
  extern function time   get_begin_time     ();

  // Function -- NODOCS -- get_end_time
  //
  // Returns the time at which this transaction was accepted, begun, or ended, 
  // as by a previous call to <accept_tr>, <begin_tr>, <begin_child_tr>, or <end_tr>.

  // @uvm-ieee 1800.2-2017 auto 5.4.2.17
  extern function time   get_end_time       ();


  // Function -- NODOCS -- set_transaction_id
  //
  // Sets this transaction's numeric identifier to id. If not set via this
  // method, the transaction ID defaults to -1. 
  //
  // When using sequences to generate stimulus, the transaction ID is used along
  // with the sequence ID to route responses in sequencers and to correlate
  // responses to requests.

  // @uvm-ieee 1800.2-2017 auto 5.4.2.18
  extern function void set_transaction_id(int id);


  // Function -- NODOCS -- get_transaction_id
  //
  // Returns this transaction's numeric identifier, which is -1 if not set
  // explicitly by ~set_transaction_id~.
  //
  // When using a <uvm_sequence #(REQ,RSP)> to generate stimulus, the transaction 
  // ID is used along
  // with the sequence ID to route responses in sequencers and to correlate
  // responses to requests.

  // @uvm-ieee 1800.2-2017 auto 5.4.2.19
  extern function int get_transaction_id();

       
  // Variable -- NODOCS -- events
  //
  // The event pool instance for this transaction. This pool is used to track
  // various milestones: by default, begin, accept, and end

`ifdef UVM_ENABLE_DEPRECATED_API
  const uvm_event_pool events = new("events");
`else
  const local uvm_event_pool events = new("events");
`endif 


  // Variable -- NODOCS -- begin_event
  //
  // A ~uvm_event#(uvm_object)~ that is triggered when this transaction's actual execution on the
  // bus begins, typically as a result of a driver calling <uvm_component::begin_tr>. 
  // Processes that wait on this event will block until the transaction has
  // begun. 
  //
  // For more information, see the general discussion for <uvm_transaction>.
  // See <uvm_event#(T)> for details on the event API.
  //
`ifdef UVM_ENABLE_DEPRECATED_API
  uvm_event#(uvm_object) begin_event;
`endif

  // Variable -- NODOCS -- end_event
  //
  // A ~uvm_event#(uvm_object)~ that is triggered when this transaction's actual execution on
  // the bus ends, typically as a result of a driver calling <uvm_component::end_tr>. 
  // Processes that wait on this event will block until the transaction has
  // ended. 
  //
  // For more information, see the general discussion for <uvm_transaction>.
  // See <uvm_event#(T)> for details on the event API.
  //
  //| virtual task my_sequence::body();
  //|  ...
  //|  start_item(item);    \ 
  //|  item.randomize();     } `uvm_do(item)
  //|  finish_item(item);   /
  //|  // return from finish item does not always mean item is completed
  //|  item.end_event.wait_on();
  //|  ...
  // 
`ifdef UVM_ENABLE_DEPRECATED_API
  uvm_event#(uvm_object) end_event;
`endif

  //----------------------------------------------------------------------------
  //
  // Internal methods properties; do not use directly
  //
  //----------------------------------------------------------------------------

  //Override data control methods for internal properties
  extern virtual function void do_print  (uvm_printer printer);
  extern virtual function void do_record (uvm_recorder recorder);
  extern virtual function void do_copy   (uvm_object rhs);


  extern protected function int m_begin_tr (time    begin_time=0, 
                                                int parent_handle=0);

  local int m_transaction_id = -1;

  local time    begin_time=-1;
  local time    end_time=-1;
  local time    accept_time=-1;

  local uvm_component initiator;
  local uvm_tr_stream stream_handle;
  local uvm_recorder      tr_recorder;

endclass


//------------------------------------------------------------------------------
// IMPLEMENTATION
//------------------------------------------------------------------------------


// new
// ---

function uvm_transaction::new (string name="", 
                               uvm_component initiator = null);

  super.new(name);
  this.initiator = initiator;
  m_transaction_id = -1;
`ifdef UVM_ENABLE_DEPRECATED_API
  begin_event = events.get("begin");
  end_event = events.get("end");
`endif
endfunction // uvm_transaction


// set_transaction_id
function void uvm_transaction::set_transaction_id(int id);
    m_transaction_id = id;
endfunction

// get_transaction_id
function int uvm_transaction::get_transaction_id();
    return (m_transaction_id);
endfunction

// set_initiator
// ------------

function void uvm_transaction::set_initiator(uvm_component initiator);
  this.initiator = initiator;
endfunction

// get_initiator
// ------------

function uvm_component uvm_transaction::get_initiator();
  return initiator;
endfunction

// get_event_pool
// --------------

function uvm_event_pool uvm_transaction::get_event_pool();
  return events;
endfunction


// is_active
// ---------

function bit uvm_transaction::is_active();
  return (end_time == -1);
endfunction


// get_begin_time
// --------------

function time uvm_transaction::get_begin_time ();
  return begin_time;
endfunction


// get_end_time
// ------------

function time uvm_transaction::get_end_time ();
  return end_time;
endfunction


// get_accept_time
// ---------------

function time uvm_transaction::get_accept_time ();
  return accept_time;
endfunction


// do_accept_tr
// -------------

function void uvm_transaction::do_accept_tr();
  return;
endfunction


// do_begin_tr
// ------------

function void uvm_transaction::do_begin_tr();
  return;
endfunction


// do_end_tr
// ----------

function void uvm_transaction::do_end_tr();
  return;
endfunction

// do_print
// --------

function void uvm_transaction::do_print (uvm_printer printer);
  string str;
  uvm_component tmp_initiator; //work around $swrite bug
  super.do_print(printer);
  if(accept_time != -1)
    printer.print_time("accept_time", accept_time);
  if(begin_time != -1)
    printer.print_time("begin_time", begin_time);
  if(end_time != -1)
    printer.print_time("end_time", end_time);
  if(initiator != null) begin
    tmp_initiator = initiator;
    $swrite(str,"@%0d", tmp_initiator.get_inst_id());
    printer.print_generic("initiator", initiator.get_type_name(), -1, str);
  end
endfunction

function void uvm_transaction::do_copy (uvm_object rhs);
  uvm_transaction txn;
  super.do_copy(rhs);
  if(rhs == null) return;
  if(!$cast(txn, rhs) ) return;

  accept_time = txn.accept_time;
  begin_time = txn.begin_time;
  end_time = txn.end_time;
  initiator = txn.initiator;
  stream_handle = txn.stream_handle;
  tr_recorder = txn.tr_recorder;
endfunction  

// do_record
// ---------

function void uvm_transaction::do_record (uvm_recorder recorder);
  string s;
  super.do_record(recorder);
  if(accept_time != -1) 
     recorder.record_field("accept_time", accept_time, $bits(accept_time), UVM_TIME);
  if(initiator != null) begin
    uvm_recursion_policy_enum p = recorder.get_recursion_policy();
    recorder.set_recursion_policy(UVM_REFERENCE);
    recorder.record_object("initiator", initiator);
    recorder.set_recursion_policy(p);
  end
endfunction

// get_tr_handle
// ---------

function int uvm_transaction::get_tr_handle ();
   if (tr_recorder != null)
     return tr_recorder.get_handle();
   else 
     return 0;
endfunction


// disable_recording
// -----------------

function void uvm_transaction::disable_recording ();
   this.stream_handle = null;
endfunction


// enable_recording
// ----------------

function void uvm_transaction::enable_recording (uvm_tr_stream stream);
   this.stream_handle = stream;
endfunction : enable_recording
   
// is_recording_enabled
// --------------------

function bit uvm_transaction::is_recording_enabled ();
  return (this.stream_handle != null);
endfunction


// accept_tr
// ---------

function void uvm_transaction::accept_tr (time accept_time = 0);
  uvm_event#(uvm_object) e;
   
  if(accept_time != 0)
    this.accept_time = accept_time;
  else
    this.accept_time = $realtime;

  do_accept_tr();
  e = events.get("accept");

  if(e!=null) 
    e.trigger();
endfunction

// begin_tr
// -----------

function int uvm_transaction::begin_tr (time begin_time=0); 
  return m_begin_tr(begin_time);
endfunction

// begin_child_tr
// --------------

//Use a parent handle of zero to link to the parent after begin
function int uvm_transaction::begin_child_tr (time begin_time=0,
                                                  int parent_handle=0); 
  return m_begin_tr(begin_time, parent_handle);
endfunction

// m_begin_tr
// -----------

function int uvm_transaction::m_begin_tr (time begin_time=0, 
                                              int parent_handle=0);
   time tmp_time = (begin_time == 0) ? $realtime : begin_time;
   uvm_recorder parent_recorder;

   if (parent_handle != 0)
     parent_recorder = uvm_recorder::get_recorder_from_handle(parent_handle);
   
   // If we haven't ended the previous record, end it.
   if (tr_recorder != null)
     // Don't free the handle, someone else may be using it...
     end_tr(tmp_time);

   // May want to establish predecessor/successor relation 
   // (don't free handle until then)
   if(is_recording_enabled()) begin 
      uvm_tr_database db = stream_handle.get_db();
      
      this.end_time = -1;
      this.begin_time = tmp_time;
      
      if(parent_recorder == null)
        tr_recorder = stream_handle.open_recorder(get_type_name(),
                                                  this.begin_time,
                                                  "Begin_No_Parent, Link");
      else begin
         tr_recorder = stream_handle.open_recorder(get_type_name(),
                                                   this.begin_time,
                                                   "Begin_End, Link");

         if (tr_recorder != null)
           db.establish_link(uvm_parent_child_link::get_link(parent_recorder, tr_recorder));
      end

      if (tr_recorder != null)
        m_begin_tr = tr_recorder.get_handle();
      else
        m_begin_tr = 0;
   end
   else begin
      tr_recorder = null;
      this.end_time = -1;
      this.begin_time = tmp_time;

      m_begin_tr = 0;
   end
   
   do_begin_tr(); //execute callback before event trigger
   
   begin
      uvm_event#(uvm_object) begin_event ;
      begin_event = events.get("begin");
      begin_event.trigger();
   end

endfunction


// end_tr
// ------

function void uvm_transaction::end_tr (time end_time=0, bit free_handle=1);
   this.end_time = (end_time == 0) ? $realtime : end_time;

   do_end_tr(); // Callback prior to actual ending of transaction

   if(is_recording_enabled() && (tr_recorder != null)) begin
      record(tr_recorder);

      tr_recorder.close(this.end_time);

      if(free_handle) 
        begin  
           // once freed, can no longer link to
           tr_recorder.free();
        end
   end // if (is_active())

   tr_recorder = null;

   begin
      uvm_event#(uvm_object) end_event ;
      end_event = events.get("end") ;
      end_event.trigger();
   end
endfunction
