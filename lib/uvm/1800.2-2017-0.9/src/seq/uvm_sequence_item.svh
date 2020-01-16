//----------------------------------------------------------------------
// Copyright 2007-2013 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2010-2013 Synopsys, Inc.
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

typedef class uvm_sequence_base;
typedef class uvm_sequencer_base;


//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_sequence_item
//
// The base class for user-defined sequence items and also the base class for
// the uvm_sequence class. The uvm_sequence_item class provides the basic
// functionality for objects, both sequence items and sequences, to operate in
// the sequence mechanism.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 14.1.1
class uvm_sequence_item extends uvm_transaction;

  local      int                m_sequence_id = -1;
  protected  bit                m_use_sequence_info;
  protected  int                m_depth = -1;
  protected  uvm_sequencer_base m_sequencer;
  protected  uvm_sequence_base  m_parent_sequence;
  static     bit issued1,issued2;
  bit        print_sequence_info;


  // Function -- NODOCS -- new
  //
  // The constructor method for uvm_sequence_item. 
  
  // @uvm-ieee 1800.2-2017 auto 14.1.2.1
  function new (string name = "uvm_sequence_item");
    super.new(name);
  endfunction

  function string get_type_name();
    return "uvm_sequence_item";
  endfunction 

  // Macro for factory creation
  `uvm_object_registry(uvm_sequence_item, "uvm_sequence_item")


  // Function- set_sequence_id

  function void set_sequence_id(int id);
    m_sequence_id = id;
  endfunction


  // Function -- NODOCS -- get_sequence_id
  //
  // private
  //
  // Get_sequence_id is an internal method that is not intended for user code.
  // The sequence_id is not a simple integer.  The get_transaction_id is meant
  // for users to identify specific transactions.
  // 
  // These methods allow access to the sequence_item sequence and transaction
  // IDs. get_transaction_id and set_transaction_id are methods on the
  // uvm_transaction base_class. These IDs are used to identify sequences to
  // the sequencer, to route responses back to the sequence that issued a
  // request, and to uniquely identify transactions.
  //
  // The sequence_id is assigned automatically by a sequencer when a sequence
  // initiates communication through any sequencer calls (i.e. `uvm_do_*,
  // wait_for_grant).  A sequence_id will remain unique for this sequence
  // until it ends or it is killed.  However, a single sequence may have
  // multiple valid sequence ids at any point in time.  Should a sequence 
  // start again after it has ended, it will be given a new unique sequence_id.
  //
  // The transaction_id is assigned automatically by the sequence each time a
  // transaction is sent to the sequencer with the transaction_id in its
  // default (-1) value.  If the user sets the transaction_id to any non-default
  // value, that value will be maintained.
  //
  // Responses are routed back to this sequences based on sequence_id. The
  // sequence may use the transaction_id to correlate responses with their
  // requests.

  function int get_sequence_id();
    return (m_sequence_id);
  endfunction


  // Function -- NODOCS -- set_item_context
  //
  // Set the sequence and sequencer execution context for a sequence item

  // @uvm-ieee 1800.2-2017 auto 14.1.2.2
  function void set_item_context(uvm_sequence_base  parent_seq,
                                 uvm_sequencer_base sequencer = null);
     set_use_sequence_info(1);
     if (parent_seq != null) set_parent_sequence(parent_seq);
     if (sequencer == null && m_parent_sequence != null) sequencer = m_parent_sequence.get_sequencer();
     set_sequencer(sequencer); 
     if (m_parent_sequence != null) set_depth(m_parent_sequence.get_depth() + 1); 
     reseed();      
  endfunction


  // Function -- NODOCS -- set_use_sequence_info
  //

  // @uvm-ieee 1800.2-2017 auto 14.1.2.3
  function void set_use_sequence_info(bit value);
    m_use_sequence_info = value;
  endfunction


  // Function -- NODOCS -- get_use_sequence_info
  //
  // These methods are used to set and get the status of the use_sequence_info
  // bit. Use_sequence_info controls whether the sequence information
  // (sequencer, parent_sequence, sequence_id, etc.) is printed, copied, or
  // recorded. When use_sequence_info is the default value of 0, then the
  // sequence information is not used. When use_sequence_info is set to 1,
  // the sequence information will be used in printing and copying.

  // @uvm-ieee 1800.2-2017 auto 14.1.2.3
  function bit get_use_sequence_info();
    return (m_use_sequence_info);
  endfunction


  // Function -- NODOCS -- set_id_info
  //
  // Copies the sequence_id and transaction_id from the referenced item into
  // the calling item.  This routine should always be used by drivers to
  // initialize responses for future compatibility.

  // @uvm-ieee 1800.2-2017 auto 14.1.2.4
  function void set_id_info(uvm_sequence_item item);
    if (item == null) begin
      uvm_report_fatal(get_full_name(), "set_id_info called with null parameter", UVM_NONE);
    end
    this.set_transaction_id(item.get_transaction_id());
    this.set_sequence_id(item.get_sequence_id());
  endfunction


  // Function -- NODOCS -- set_sequencer
  //
  // Sets the default sequencer for the sequence to sequencer.  It will take
  // effect immediately, so it should not be called while the sequence is
  // actively communicating with the sequencer.

  // @uvm-ieee 1800.2-2017 auto 14.1.2.6
  virtual function void set_sequencer(uvm_sequencer_base sequencer);
    m_sequencer = sequencer;
    m_set_p_sequencer();
  endfunction


  // Function -- NODOCS -- get_sequencer
  //
  // Returns a reference to the default sequencer used by this sequence.

  // @uvm-ieee 1800.2-2017 auto 14.1.2.5
  function uvm_sequencer_base get_sequencer();
    return m_sequencer;
  endfunction


  // Function -- NODOCS -- set_parent_sequence
  //
  // Sets the parent sequence of this sequence_item.  This is used to identify
  // the source sequence of a sequence_item.

  // @uvm-ieee 1800.2-2017 auto 14.1.2.8
  // @uvm-ieee 1800.2-2017 auto 19.1.1.2.10
  function void set_parent_sequence(uvm_sequence_base parent);
    m_parent_sequence = parent;
  endfunction


  // Function -- NODOCS -- get_parent_sequence
  //
  // Returns a reference to the parent sequence of any sequence on which this
  // method was called. If this is a parent sequence, the method returns ~null~.

  // @uvm-ieee 1800.2-2017 auto 14.1.2.7
  // @uvm-ieee 1800.2-2017 auto 19.1.1.2.10
  function uvm_sequence_base get_parent_sequence();
    return (m_parent_sequence);
  endfunction 


  // Function -- NODOCS -- set_depth
  //
  // The depth of any sequence is calculated automatically.  However, the user
  // may use  set_depth to specify the depth of a particular sequence. This
  // method will override the automatically calculated depth, even if it is
  // incorrect.  

  // @uvm-ieee 1800.2-2017 auto 14.1.2.10
  function void set_depth(int value);
    m_depth = value;
  endfunction


  // Function -- NODOCS -- get_depth
  //
  // Returns the depth of a sequence from its parent.  A  parent sequence will
  // have a depth of 1, its child will have a depth  of 2, and its grandchild
  // will have a depth of 3.

  // @uvm-ieee 1800.2-2017 auto 14.1.2.9
  function int get_depth();

    // If depth has been set or calculated, then use that
    if (m_depth != -1) begin
      return (m_depth);
    end

    // Calculate the depth, store it, and return the value
    if (m_parent_sequence == null) begin
      m_depth = 1;
    end else begin
      m_depth = m_parent_sequence.get_depth() + 1;
    end

    return (m_depth);
  endfunction 


  // Function -- NODOCS -- is_item
  //
  // This function may be called on any sequence_item or sequence. It will
  // return 1 for items and 0 for sequences (which derive from this class).

  // @uvm-ieee 1800.2-2017 auto 14.1.2.11
  virtual function bit is_item();
    return(1);
  endfunction


  // Function- get_full_name
  //
  // Internal method; overrides must follow same naming convention

  function string get_full_name();
    if(m_parent_sequence != null) 
      get_full_name = {m_parent_sequence.get_full_name(), "."};
    else if(m_sequencer!=null)
      get_full_name = {m_sequencer.get_full_name(), "."};
    if(get_name() != "") 
      get_full_name = {get_full_name, get_name()};
    else begin
      get_full_name = {get_full_name, "_item"};
    end
  endfunction


  // Function -- NODOCS -- get_root_sequence_name
  //
  // Provides the name of the root sequence (the top-most parent sequence).

  // @uvm-ieee 1800.2-2017 auto 14.1.2.12
  function string get_root_sequence_name();
    uvm_sequence_base root_seq;
    root_seq = get_root_sequence();
    if (root_seq == null)
      return "";
    else
      return root_seq.get_name();
  endfunction


  // Function- m_set_p_sequencer
  //
  // Internal method

  virtual function void m_set_p_sequencer();
    return;
  endfunction  


  // Function -- NODOCS -- get_root_sequence
  //
  // Provides a reference to the root sequence (the top-most parent sequence).

  // @uvm-ieee 1800.2-2017 auto 14.1.2.13
  function uvm_sequence_base get_root_sequence();
    uvm_sequence_item root_seq_base;
    uvm_sequence_base root_seq;
    root_seq_base = this;
    while(1) begin
      if(root_seq_base.get_parent_sequence()!=null) begin
        root_seq_base = root_seq_base.get_parent_sequence();
        $cast(root_seq, root_seq_base);
      end
      else
        return root_seq;
    end
  endfunction


  // Function -- NODOCS -- get_sequence_path
  //
  // Provides a string of names of each sequence in the full hierarchical
  // path. A "." is used as the separator between each sequence.

  // @uvm-ieee 1800.2-2017 auto 14.1.2.14
  function string get_sequence_path();
    uvm_sequence_item this_item;
    string seq_path;
    this_item = this;
    seq_path = this.get_name();
    while(1) begin
      if(this_item.get_parent_sequence()!=null) begin
        this_item = this_item.get_parent_sequence();
        seq_path = {this_item.get_name(), ".", seq_path};
      end
      else
        return seq_path;
    end
  endfunction


  //---------------------------
  // Group -- NODOCS -- Reporting Interface
  //---------------------------
  //
  // Sequence items and sequences will use the sequencer which they are
  // associated with for reporting messages. If no sequencer has been set
  // for the item/sequence using <set_sequencer> or indirectly via 
  // <uvm_sequence_base::start_item> or <uvm_sequence_base::start>),
  // then the global reporter will be used.

  // @uvm-ieee 1800.2-2017 auto 14.1.3.1
  virtual function uvm_report_object uvm_get_report_object();
    if(m_sequencer == null) begin
      uvm_coreservice_t cs = uvm_coreservice_t::get();
       return cs.get_root();
    end else 
      return m_sequencer;
  endfunction

  // @uvm-ieee 1800.2-2017 auto 14.1.3.2
  function int uvm_report_enabled(int verbosity, 
    				  uvm_severity severity=UVM_INFO, string id="");
    uvm_report_object l_report_object = uvm_get_report_object();
    if (l_report_object.get_report_verbosity_level(severity, id) < verbosity)
      return 0;
    return 1;
  endfunction


  // @uvm-ieee 1800.2-2017 auto 14.1.3.3
  virtual function void uvm_report( uvm_severity severity,
                                    string id,
                                    string message,
                                    int verbosity = (severity == uvm_severity'(UVM_ERROR)) ? UVM_LOW :
                                                    (severity == uvm_severity'(UVM_FATAL)) ? UVM_NONE : UVM_MEDIUM,
                                    string filename = "",
                                    int line = 0,
                                    string context_name = "",
                                    bit report_enabled_checked = 0);
    uvm_report_message l_report_message;
    if (report_enabled_checked == 0) begin
      if (!uvm_report_enabled(verbosity, severity, id))
        return;
    end
    l_report_message = uvm_report_message::new_report_message();
    l_report_message.set_report_message(severity, id, message, 
					verbosity, filename, line, context_name);
    uvm_process_report_message(l_report_message);

  endfunction
    
  // Function -- NODOCS -- uvm_report_info

  // @uvm-ieee 1800.2-2017 auto 14.1.3.3
  virtual function void uvm_report_info( string id,
					 string message,
   					 int verbosity = UVM_MEDIUM,
					 string filename = "",
					 int line = 0,
   					 string context_name = "",
					 bit report_enabled_checked = 0);

    this.uvm_report(UVM_INFO, id, message, verbosity, filename, line,
                    context_name, report_enabled_checked);
  endfunction

  // Function -- NODOCS -- uvm_report_warning

  // @uvm-ieee 1800.2-2017 auto 14.1.3.3
  virtual function void uvm_report_warning( string id,
					    string message,
   					    int verbosity = UVM_MEDIUM,
					    string filename = "",
					    int line = 0,
   					    string context_name = "",
					    bit report_enabled_checked = 0);

    this.uvm_report(UVM_WARNING, id, message, verbosity, filename, line,
                    context_name, report_enabled_checked);
  endfunction

  // Function -- NODOCS -- uvm_report_error

  // @uvm-ieee 1800.2-2017 auto 14.1.3.3
  virtual function void uvm_report_error( string id,
					  string message,
   					  int verbosity = UVM_NONE,
					  string filename = "",
					  int line = 0,
   					  string context_name = "",
					  bit report_enabled_checked = 0);

    this.uvm_report(UVM_ERROR, id, message, verbosity, filename, line,
                    context_name, report_enabled_checked);
  endfunction

  // Function -- NODOCS -- uvm_report_fatal
  //
  // These are the primary reporting methods in the UVM. uvm_sequence_item
  // derived types delegate these functions to their associated sequencer
  // if they have one, or to the global reporter. See <uvm_report_object::Reporting>
  // for details on the messaging functions.

  // @uvm-ieee 1800.2-2017 auto 14.1.3.3
  virtual function void uvm_report_fatal( string id,
					  string message,
   					  int verbosity = UVM_NONE,
					  string filename = "",
					  int line = 0,
   					  string context_name = "",
					  bit report_enabled_checked = 0);

    this.uvm_report(UVM_FATAL, id, message, verbosity, filename, line,
                    context_name, report_enabled_checked);
  endfunction

  // @uvm-ieee 1800.2-2017 auto 14.1.3.4
  virtual function void uvm_process_report_message (uvm_report_message report_message);
    uvm_report_object l_report_object = uvm_get_report_object();
    report_message.set_report_object(l_report_object);
    if (report_message.get_context() == "")
      report_message.set_context(get_sequence_path());
    l_report_object.m_rh.process_report_message(report_message);
  endfunction


  // Function- do_print
  //
  // Internal method

  function void do_print (uvm_printer printer);
    string temp_str0, temp_str1;
    int depth = get_depth();
    super.do_print(printer);
    if(print_sequence_info || m_use_sequence_info) begin
      printer.print_field_int("depth", depth, $bits(depth), UVM_DEC, ".", "int");
      if(m_parent_sequence != null) begin
        temp_str0 = m_parent_sequence.get_name();
        temp_str1 = m_parent_sequence.get_full_name();
      end
      printer.print_string("parent sequence (name)", temp_str0);
      printer.print_string("parent sequence (full name)", temp_str1);
      temp_str1 = "";
      if(m_sequencer != null) begin
        temp_str1 = m_sequencer.get_full_name();
      end
      printer.print_string("sequencer", temp_str1);
    end
  endfunction

  /*
  virtual task pre_do(bit is_item);
    return;
  endtask

  virtual task body();
    return;
  endtask  

  virtual function void mid_do(uvm_sequence_item this_item);
    return;
  endfunction
  
  virtual function void post_do(uvm_sequence_item this_item);
    return;
  endfunction

  virtual task wait_for_grant(int item_priority = -1, bit  lock_request = 0);
    return;
  endtask

  virtual function void send_request(uvm_sequence_item request, bit rerandomize = 0);
    return;
  endfunction

  virtual task wait_for_item_done(int transaction_id = -1);
    return;
  endtask
  */

endclass
