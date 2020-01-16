//
//------------------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2010-2013 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2011 AMD
// Copyright 2013-2015 NVIDIA Corporation
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
//------------------------------------------------------------------------------


`define UVM_SEQ_ITEM_TASK_ERROR "Sequencer interface task not implemented"
`define UVM_SEQ_ITEM_FUNCTION_ERROR "Sequencer interface function not implemented"

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_sqr_if_base #(REQ,RSP)
//
// This class defines an interface for sequence drivers to communicate with
// sequencers. The driver requires the interface via a port, and the sequencer
// implements it and provides it via an export.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 15.2.1.1
virtual class uvm_sqr_if_base #(type T1=uvm_object, T2=T1);

  // Task -- NODOCS -- get_next_item
  //
  // Retrieves the next available item from a sequence.  The call will block
  // until an item is available.  The following steps occur on this call:
  //
  // 1 - Arbitrate among requesting, unlocked, relevant sequences - choose the
  //     highest priority sequence based on the current sequencer arbitration
  //     mode. If no sequence is available, wait for a requesting unlocked
  //     relevant sequence,  then re-arbitrate.
  // 2 - The chosen sequence will return from wait_for_grant
  // 3 - The chosen sequence <uvm_sequence_base::pre_do> is called
  // 4 - The chosen sequence item is randomized
  // 5 - The chosen sequence <uvm_sequence_base::post_do> is called
  // 6 - Return with a reference to the item
  //
  // Once <get_next_item> is called, <item_done> must be called to indicate the
  // completion of the request to the sequencer.  This will remove the request
  // item from the sequencer FIFO.

  // @uvm-ieee 1800.2-2017 auto 15.2.1.2.1
  virtual task get_next_item(output T1 t);
    uvm_report_error("get_next_item", `UVM_SEQ_ITEM_TASK_ERROR, UVM_NONE);
  endtask
 

  // Task -- NODOCS -- try_next_item
  //
  // Retrieves the next available item from a sequence if one is available.
  // Otherwise, the function returns immediately with request set to ~null~.
  // The following steps occur on this call:
  //
  // 1 - Arbitrate among requesting, unlocked, relevant sequences - choose the
  //     highest priority sequence based on the current sequencer arbitration
  //     mode. If no sequence is available, return ~null~.
  // 2 - The chosen sequence will return from wait_for_grant
  // 3 - The chosen sequence <uvm_sequence_base::pre_do> is called
  // 4 - The chosen sequence item is randomized
  // 5 - The chosen sequence <uvm_sequence_base::post_do> is called
  // 6 - Return with a reference to the item
  //
  // Once <try_next_item> is called, <item_done> must be called to indicate the
  // completion of the request to the sequencer.  This will remove the request
  // item from the sequencer FIFO.

  // @uvm-ieee 1800.2-2017 auto 15.2.1.2.2
  virtual task try_next_item(output T1 t);
    uvm_report_error("try_next_item", `UVM_SEQ_ITEM_TASK_ERROR, UVM_NONE);
  endtask


  // Function -- NODOCS -- item_done
  //
  // Indicates that the request is completed to the sequencer.  Any 
  // <uvm_sequence_base::wait_for_item_done>
  // calls made by a sequence for this item will return.
  //
  // The current item is removed from the sequencer FIFO.
  //
  // If a response item is provided, then it will be sent back to the requesting
  // sequence. The response item must have its sequence ID and transaction ID
  // set correctly, using the <uvm_sequence_item::set_id_info> method:
  //
  //|  rsp.set_id_info(req);
  //
  // Before <item_done> is called, any calls to peek will retrieve the current
  // item that was obtained by <get_next_item>.  After <item_done> is called, peek
  // will cause the sequencer to arbitrate for a new item.

  // @uvm-ieee 1800.2-2017 auto 15.2.1.2.3
  virtual function void item_done(input T2 t = null);
    uvm_report_error("item_done", `UVM_SEQ_ITEM_FUNCTION_ERROR, UVM_NONE);
  endfunction

  
  // Task -- NODOCS -- wait_for_sequences
  //
  // Waits for a sequence to have a new item available. The default
  // implementation in the sequencer calls
  //  <uvm_wait_for_nba_region>.
  // User-derived sequencers
  // may override its <wait_for_sequences> implementation to perform some other
  // application-specific implementation.

  // @uvm-ieee 1800.2-2017 auto 15.2.1.2.4
  virtual task wait_for_sequences();
    uvm_report_error("wait_for_sequences", `UVM_SEQ_ITEM_TASK_ERROR, UVM_NONE);
  endtask


  // Function -- NODOCS -- has_do_available
  //
  // Indicates whether a sequence item is available for immediate processing.
  // Implementations should return 1 if an item is available, 0 otherwise. 

  // @uvm-ieee 1800.2-2017 auto 15.2.1.2.5
  virtual function bit has_do_available();
    uvm_report_error("has_do_available", `UVM_SEQ_ITEM_FUNCTION_ERROR, UVM_NONE);
    return 0;
  endfunction


  //-----------------------
  // uvm_tlm_blocking_slave_if
  //-----------------------

  // Task -- NODOCS -- get
  //
  // Retrieves the next available item from a sequence.  The call blocks until
  // an item is available. The following steps occur on this call:
  //
  // 1 - Arbitrate among requesting, unlocked, relevant sequences - choose the
  //     highest priority sequence based on the current sequencer arbitration
  //     mode. If no sequence is available, wait for a requesting unlocked
  //     relevant sequence, then re-arbitrate.
  // 2 - The chosen sequence will return from <uvm_sequence_base::wait_for_grant>
  // 3 - The chosen sequence <uvm_sequence_base::pre_do> is called
  // 4 - The chosen sequence item is randomized
  // 5 - The chosen sequence <uvm_sequence_base::post_do> is called
  // 6 - Indicate <item_done> to the sequencer
  // 7 - Return with a reference to the item
  //
  // When get is called, <item_done> may not be called.  A new item can be
  // obtained by calling get again, or a response may be sent using either
  // <put>, or uvm_driver::rsp_port.write().

  // @uvm-ieee 1800.2-2017 auto 15.2.1.2.6
  virtual task get(output T1 t);
    uvm_report_error("get", `UVM_SEQ_ITEM_TASK_ERROR, UVM_NONE);
  endtask

  // Task -- NODOCS -- peek
  //
  // Returns the current request item if one is in the sequencer FIFO.  If no
  // item is in the FIFO, then the call will block until the sequencer has a new
  // request. The following steps will occur if the sequencer FIFO is empty:
  //
  // 1 - Arbitrate among requesting, unlocked, relevant sequences - choose the
  // highest priority sequence based on the current sequencer arbitration mode.
  // If no sequence is available, wait for a requesting unlocked relevant
  // sequence, then re-arbitrate.
  //
  // 2 - The chosen sequence will return from <uvm_sequence_base::wait_for_grant>
  // 3 - The chosen sequence <uvm_sequence_base::pre_do> is called
  // 4 - The chosen sequence item is randomized
  // 5 - The chosen sequence <uvm_sequence_base::post_do> is called
  //
  // Once a request item has been retrieved and is in the sequencer FIFO,
  // subsequent calls to peek will return the same item.  The item will stay in
  // the FIFO until either get or <item_done> is called.

  // @uvm-ieee 1800.2-2017 auto 15.2.1.2.7
  virtual task peek(output T1 t);
    uvm_report_error("peek", `UVM_SEQ_ITEM_TASK_ERROR, UVM_NONE);
  endtask


  // Task -- NODOCS -- put
  //
  // Sends a response back to the sequence that issued the request. Before the
  // response is put, it must have its sequence ID and transaction ID set to
  // match the request.  This can be done using the
  // <uvm_sequence_item::set_id_info> call:
  //
  //   rsp.set_id_info(req);
  //
  // While this is a task, it will not consume time (including delta cycles).
  // The response will be put into the
  // sequence response queue or it will be sent to the
  // sequence response handler.
  //
   

  // @uvm-ieee 1800.2-2017 auto 15.2.1.2.8
  virtual task put(input T2 t);
    uvm_report_error("put", `UVM_SEQ_ITEM_TASK_ERROR, UVM_NONE);
  endtask


  // Function -- NODOCS -- put_response
  //
  // Sends a response back to the sequence that issued the request. Before the
  // response is put, it must have its sequence ID and transaction ID set to
  // match the request.  This can be done using the
  // <uvm_sequence_item::set_id_info> call:
  //
  //   rsp.set_id_info(req);
  //

  // @uvm-ieee 1800.2-2017 auto 15.2.1.2.9
  virtual function void put_response(input T2 t);
    uvm_report_error("put_response", `UVM_SEQ_ITEM_FUNCTION_ERROR, UVM_NONE);
  endfunction

  // Function -- NODOCS -- disable_auto_item_recording
  //
  // By default, item recording is performed automatically when
  // get_next_item() and item_done() are called.
  // However, this works only for simple, in-order, blocking transaction
  // execution. For pipelined and out-of-order transaction execution, the
  // driver must turn off this automatic recording and call
  // <uvm_transaction::accept_tr>, <uvm_transaction::begin_tr>
  // and <uvm_transaction::end_tr> explicitly at appropriate points in time.
  //
  // This methods be called at the beginning of the driver's ~run_phase()~ method.
  // Once disabled, automatic recording cannot be re-enabled.
  //
  // For backward-compatibility, automatic item recording can be globally
  // turned off at compile time by defining UVM_DISABLE_AUTO_ITEM_RECORDING

  // @uvm-ieee 1800.2-2017 auto 15.2.1.2.10
  virtual function void disable_auto_item_recording();
    uvm_report_error("disable_auto_item_recording", `UVM_SEQ_ITEM_FUNCTION_ERROR, UVM_NONE);
  endfunction
  
  // Function -- NODOCS -- is_auto_item_recording_enabled
  //
  // Return TRUE if automatic item recording is enabled for this port instance.

  // @uvm-ieee 1800.2-2017 auto 15.2.1.2.11
  virtual function bit is_auto_item_recording_enabled();
    uvm_report_error("is_auto_item_recording_enabled", `UVM_SEQ_ITEM_FUNCTION_ERROR, UVM_NONE);
    return 0;
  endfunction
endclass
