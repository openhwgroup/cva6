//------------------------------------------------------------------------------
// Copyright 2007-2009 Mentor Graphics Corporation
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2018 AMD
// Copyright 2018 NVIDIA Corporation
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

// Title -- NODOCS -- Sequence-Related Macros



//-----------------------------------------------------------------------------
//
// Group -- NODOCS -- Sequence Action Macros
//
// These macros are used to start sequences and sequence items on the default
// sequencer returned by get_sequencer(). This is determined a number of ways. 
// - the sequencer handle provided in the <uvm_sequence_base::start> method
// - the sequencer used by the parent sequence
// - the sequencer that was set using the <uvm_sequence_item::set_sequencer> method
//-----------------------------------------------------------------------------



// MACRO -- NODOCS -- `uvm_do_pri
//
//| `uvm_do_pri(SEQ_OR_ITEM, PRIORITY)
//
// This is the same as `uvm_do except that the sequence item or sequence is
// executed with the priority specified in the argument

`define uvm_do_pri(SEQ_OR_ITEM, PRIORITY) \
  `uvm_do(SEQ_OR_ITEM, get_sequencer(), PRIORITY, {})


// MACRO -- NODOCS -- `uvm_do_with
//
//| `uvm_do_with(SEQ_OR_ITEM, CONSTRAINTS)
//
// This is the same as `uvm_do except that the constraint block in the 2nd
// argument is applied to the item or sequence in a randomize with statement
// before execution.

`define uvm_do_with(SEQ_OR_ITEM, CONSTRAINTS) \
  `uvm_do(SEQ_OR_ITEM, get_sequencer(), -1, CONSTRAINTS)


// MACRO -- NODOCS -- `uvm_do_pri_with
//
//| `uvm_do_pri_with(SEQ_OR_ITEM, PRIORITY, CONSTRAINTS)
//
// This is the same as `uvm_do_pri except that the given constraint block is
// applied to the item or sequence in a randomize with statement before
// execution.

`define uvm_do_pri_with(SEQ_OR_ITEM, PRIORITY, CONSTRAINTS) \
  `uvm_do(SEQ_OR_ITEM, get_sequencer(), PRIORITY, CONSTRAINTS)


//-----------------------------------------------------------------------------
//
// Group -- NODOCS -- Sequence on Sequencer Action Macros
//
// These macros are used to start sequences and sequence items on a specific
// sequencer. The sequence or item is created and executed on the given
// sequencer.
//-----------------------------------------------------------------------------

// MACRO -- NODOCS -- `uvm_create_on
//
//| `uvm_create_on(SEQ_OR_ITEM, SEQR)
//
// This is the same as <`uvm_create> except that it also sets the parent sequence
// to the sequence in which the macro is invoked, and it sets the sequencer to
// the specified ~SEQR~ argument.

`define uvm_create_on(SEQ_OR_ITEM, SEQR) \
  `uvm_create(SEQ_OR_ITEM, SEQR)


// MACRO -- NODOCS -- `uvm_do_on
//
//| `uvm_do_on(SEQ_OR_ITEM, SEQR)
//
// This is the same as <`uvm_do> except that it also sets the parent sequence to
// the sequence in which the macro is invoked, and it sets the sequencer to the
// specified ~SEQR~ argument.

`define uvm_do_on(SEQ_OR_ITEM, SEQR) \
  `uvm_do(SEQ_OR_ITEM, SEQR, -1, {})


// MACRO -- NODOCS -- `uvm_do_on_pri
//
//| `uvm_do_on_pri(SEQ_OR_ITEM, SEQR, PRIORITY)
//
// This is the same as <`uvm_do_pri> except that it also sets the parent sequence
// to the sequence in which the macro is invoked, and it sets the sequencer to
// the specified ~SEQR~ argument.

`define uvm_do_on_pri(SEQ_OR_ITEM, SEQR, PRIORITY) \
  `uvm_do(SEQ_OR_ITEM, SEQR, PRIORITY, {})


// MACRO -- NODOCS -- `uvm_do_on_with
//
//| `uvm_do_on_with(SEQ_OR_ITEM, SEQR, CONSTRAINTS)
//
// This is the same as <`uvm_do_with> except that it also sets the parent
// sequence to the sequence in which the macro is invoked, and it sets the
// sequencer to the specified ~SEQR~ argument.
// The user must supply brackets around the constraints.

`define uvm_do_on_with(SEQ_OR_ITEM, SEQR, CONSTRAINTS) \
  `uvm_do(SEQ_OR_ITEM, SEQR, -1, CONSTRAINTS)


// MACRO -- NODOCS -- `uvm_do_on_pri_with
//
//| `uvm_do_on_pri_with(SEQ_OR_ITEM, SEQR, PRIORITY, CONSTRAINTS)
//
// This is the same as `uvm_do_pri_with except that it also sets the parent
// sequence to the sequence in which the macro is invoked, and it sets the
// sequencer to the specified ~SEQR~ argument.

`define uvm_do_on_pri_with(SEQ_OR_ITEM, SEQR, PRIORITY, CONSTRAINTS) \
  `uvm_do(SEQ_OR_ITEM, SEQR, PRIORITY, CONSTRAINTS)


//-----------------------------------------------------------------------------
//
// Group -- NODOCS -- Sequence Action Macros for Pre-Existing Sequences
//
// These macros are used to start sequences and sequence items that do not
// need to be created. 
//-----------------------------------------------------------------------------

  

// MACRO -- NODOCS -- `uvm_send_pri
//
//| `uvm_send_pri(SEQ_OR_ITEM, PRIORITY)
//
// This is the same as `uvm_send except that the sequence item or sequence is
// executed with the priority specified in the argument.

`define uvm_send_pri(SEQ_OR_ITEM, PRIORITY) \
  `uvm_send(SEQ_OR_ITEM, PRIORITY)
  


// MACRO -- NODOCS -- `uvm_rand_send_pri
//
//| `uvm_rand_send_pri(SEQ_OR_ITEM, PRIORITY)
//
// This is the same as `uvm_rand_send except that the sequence item or sequence
// is executed with the priority specified in the argument.

`define uvm_rand_send_pri(SEQ_OR_ITEM, PRIORITY) \
  `uvm_rand_send(SEQ_OR_ITEM, PRIORITY, {})


// MACRO -- NODOCS -- `uvm_rand_send_with
//
//| `uvm_rand_send_with(SEQ_OR_ITEM, CONSTRAINTS)
//
// This is the same as `uvm_rand_send except that the given constraint block is
// applied to the item or sequence in a randomize with statement before
// execution.

`define uvm_rand_send_with(SEQ_OR_ITEM, CONSTRAINTS) \
  `uvm_rand_send(SEQ_OR_ITEM, -1, CONSTRAINTS)


// MACRO -- NODOCS -- `uvm_rand_send_pri_with
//
//| `uvm_rand_send_pri_with(SEQ_OR_ITEM, PRIORITY, CONSTRAINTS)
//
// This is the same as `uvm_rand_send_pri except that the given constraint block
// is applied to the item or sequence in a randomize with statement before
// execution.

`define uvm_rand_send_pri_with(SEQ_OR_ITEM, PRIORITY, CONSTRAINTS) \
  `uvm_rand_send(SEQ_OR_ITEM, PRIORITY, CONSTRAINTS)


`define uvm_create_seq(UVM_SEQ, SEQR_CONS_IF) \
  `uvm_create(UVM_SEQ, SEQR_CONS_IF.consumer_seqr) \

`define uvm_do_seq(UVM_SEQ, SEQR_CONS_IF) \
  `uvm_do(UVM_SEQ, SEQR_CONS_IF.consumer_seqr, -1, {}) \

`define uvm_do_seq_with(UVM_SEQ, SEQR_CONS_IF, CONSTRAINTS) \
  `uvm_do(UVM_SEQ, SEQR_CONS_IF.consumer_seqr, -1, CONSTRAINTS) \

