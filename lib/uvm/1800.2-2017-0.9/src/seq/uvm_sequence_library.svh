//----------------------------------------------------------------------
// Copyright 2011-2017 Mentor Graphics Corporation
// Copyright 2011-2014 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2012 AMD
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2017 Cisco Systems, Inc.
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


typedef class uvm_sequence_library_cfg;

//
// CLASS -- NODOCS -- uvm_sequence_library
//
// The ~uvm_sequence_library~ is a sequence that contains a list of registered
// sequence types. It can be configured to create and execute these sequences
// any number of times using one of several modes of operation, including a
// user-defined mode.
//
// When started (as any other sequence), the sequence library will randomly
// select and execute a sequence from its ~sequences~ queue. If in
// <UVM_SEQ_LIB_RAND> mode, its <select_rand> property is randomized and used
// as an index into ~sequences~.  When in <UVM_SEQ_LIB_RANDC> mode, the
// <select_randc> property is used. When in <UVM_SEQ_LIB_ITEM> mode, only
// sequence items of the ~REQ~ type are generated and executed--no sequences
// are executed. Finally, when in <UVM_SEQ_LIB_USER> mode, the
// <select_sequence> method is called to obtain the index for selecting the
// next sequence to start. Users can override this method in subtypes to
// implement custom selection algorithms.
//
// Creating a subtype of a sequence library requires invocation of the
// <`uvm_sequence_library_utils> macro in its declaration and calling
// the <init_sequence_library> method in its constructor. The macro
// and function are needed to populate the sequence library with any
// sequences that were statically registered with it or any of its base
// classes.
//
//| class my_seq_lib extends uvm_sequence_library #(my_item);
//|   `uvm_object_utils(my_seq_lib)
//|   `uvm_sequence_library_utils(my_seq_lib)
//|    function new(string name="");
//|      super.new(name);
//|      init_sequence_library();
//|    endfunction
//|    ...
//| endclass
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 14.4.1
class uvm_sequence_library #(type REQ=uvm_sequence_item,RSP=REQ) extends uvm_sequence #(REQ,RSP);


  `uvm_object_param_utils(uvm_sequence_library#(REQ,RSP))
  `uvm_type_name_decl("uvm_sequence_library #(REQ,RSP)")
  
   // @uvm-ieee 1800.2-2017 auto 14.4.2
   // @uvm-ieee 1800.2-2017 auto 14.4.3
   extern function new(string name="");


   //--------------------------
   // Group -- NODOCS -- Sequence selection
   //--------------------------

   // Variable -- NODOCS -- selection_mode
   //
   // Specifies the mode used to select sequences for execution
   //
   // If you do not have access to an instance of the library,
   // use the configuration resource interface.
   //
   // The following example sets the ~config_seq_lib~ as the default
   // sequence for the 'main' phase on the sequencer to be
   // located at "env.agent.sequencer"
   // and set the selection mode to <UVM_SEQ_LIB_RANDC>. If the
   // settings are being done from within a component, the first
   // argument must be ~this~ and the second argument a path
   // relative to that component.
   // 
   //
   //| uvm_config_db #(uvm_object_wrapper)::set(null,
   //|                                    "env.agent.sequencer.main_phase",
   //|                                    "default_sequence",
   //|                                    main_seq_lib::get_type());
   //|
   //| uvm_config_db #(uvm_sequence_lib_mode)::set(null,
   //|                                    "env.agent.sequencer.main_phase",
   //|                                    "default_sequence.selection_mode",
   //|                                    UVM_SEQ_LIB_RANDC);
   //
   // Alternatively, you may create an instance of the sequence library
   // a priori, initialize all its parameters, randomize it, then set it
   // to run as-is on the sequencer. 
   //
   //| main_seq_lib my_seq_lib;
   //| my_seq_lib = new("my_seq_lib");
   //|
   //| my_seq_lib.selection_mode = UVM_SEQ_LIB_RANDC;
   //| my_seq_lib.min_random_count = 500;
   //| my_seq_lib.max_random_count = 1000;
   //| void'(my_seq_lib.randomize());
   //|
   //| uvm_config_db #(uvm_sequence_base)::set(null,
   //|                                    "env.agent.sequencer.main_phase",
   //|                                    "default_sequence",
   //|                                    my_seq_lib);
   //|
   //
   uvm_sequence_lib_mode selection_mode;


   // Variable -- NODOCS -- min_random_count
   //
   // Sets the minimum number of items to execute. Use the configuration
   // mechanism to set. See <selection_mode> for an example.
   //
   int unsigned min_random_count=10;


   // Variable -- NODOCS -- max_random_count
   //
   // Sets the maximum number of items to execute. Use the configuration
   // mechanism to set. See <selection_mode> for an example.
   //
   //
   int unsigned max_random_count=10;



   // Variable -- NODOCS -- sequences_executed
   //
   // Indicates the number of sequences executed, not including the
   // currently executing sequence, if any.
   //
   protected int unsigned sequences_executed;


   // Variable -- NODOCS -- sequence_count
   //
   // Specifies the number of sequences to execute when this sequence
   // library is started. If in <UVM_SEQ_LIB_ITEM> mode, specifies the
   // number of sequence items that will be generated.
   //
   rand  int unsigned sequence_count = 10;


   // Variable -- NODOCS -- select_rand
   //
   // The index variable that is randomized to select the next sequence
   // to execute when in UVM_SEQ_LIB_RAND mode
   //
   // Extensions may place additional constraints on this variable.
   //
   rand  int unsigned select_rand;


   // Variable -- NODOCS -- select_randc
   //
   // The index variable that is randomized to select the next sequence
   // to execute when in UVM_SEQ_LIB_RANDC mode
   //
   // Extensions may place additional constraints on this variable.
   //
   randc bit [15:0] select_randc;



   // Variable- seqs_distrib
   //
   //
   //
   protected int seqs_distrib[string]  = '{default:0};


   // Variable- sequences
   //
   // The container of all registered sequence types. For <sequence_count>
   // times, this sequence library will randomly select and execute a
   // sequence from this list of sequence types.
   //
   protected uvm_object_wrapper sequences[$];



   // Constraint: valid_rand_selection
   //
   // Constrains <select_rand> to be a valid index into the ~sequences~ array
   //
   constraint valid_rand_selection {
         select_rand inside {[0:sequences.size()-1]};
   }



   // Constraint: valid_randc_selection
   //
   // Constrains <select_randc> to be a valid index into the ~sequences~ array
   //
   constraint valid_randc_selection {
         select_randc inside {[0:sequences.size()-1]};
   }


   // Constraint: valid_sequence_count
   //
   // Constrains <sequence_count> to lie within the range defined by
   // <min_random_count> and <max_random_count>.
   //
   constraint valid_sequence_count {
      sequence_count inside {[min_random_count:max_random_count]};
   }



   // Function -- NODOCS -- select_sequence
   //
   // Generates an index used to select the next sequence to execute. 
   // Overrides must return a value between 0 and ~max~, inclusive.
   // Used only for <UVM_SEQ_LIB_USER> selection mode. The
   // default implementation returns 0, incrementing on successive calls,
   // wrapping back to 0 when reaching ~max~.
   //
   extern virtual function int unsigned select_sequence(int unsigned max);



   //-----------------------------
   // Group -- NODOCS -- Sequence registration
   //-----------------------------

   // Function -- NODOCS -- add_typewide_sequence
   //
   // Registers the provided sequence type with this sequence library
   // type. The sequence type will be available for selection by all instances
   // of this class. Sequence types already registered are silently ignored.
   //
   extern static function void add_typewide_sequence(uvm_object_wrapper seq_type);




   // @uvm-ieee 1800.2-2017 auto 14.4.5.2
   extern static function void add_typewide_sequences(uvm_object_wrapper seq_types[$]);



   // @uvm-ieee 1800.2-2017 auto 14.4.5.3
   extern function void add_sequence(uvm_object_wrapper seq_type);



   // @uvm-ieee 1800.2-2017 auto 14.4.5.4
   extern virtual function void add_sequences(uvm_object_wrapper seq_types[$]);



   // @uvm-ieee 1800.2-2017 auto 14.4.5.5
   extern virtual function void remove_sequence(uvm_object_wrapper seq_type);



   // @uvm-ieee 1800.2-2017 auto 14.4.5.6
   extern virtual function void get_sequences(ref uvm_object_wrapper seq_types[$]);
   
   // @uvm-ieee 1800.2-2017 auto 14.4.4.10
   extern virtual function uvm_object_wrapper get_sequence(int unsigned idx);


   // Function -- NODOCS -- init_sequence_library
   //
   // All subtypes of this class must call init_sequence_library in its
   // constructor.
   extern function void init_sequence_library();

   // Macro -- NODOCS -- uvm_sequence_library_utils
   //
   // All subtypes of this class must invoke the `uvm_sequence_library_utils
   // macro.
   //
   //| class my_seq_lib extends uvm_sequence_library #(my_item);
   //|   `uvm_object_utils(my_seq_lib)
   //|   `uvm_sequence_library_utils(my_seq_lib)
   //|    function new(string name="");
   //|      super.new(name);
   //|      init_sequence_library();
   //|    endfunction
   //|    ...
   //| endclass

   //------------------------------------------
   // PRIVATE - INTERNAL - NOT PART OF STANDARD
   //------------------------------------------

   typedef uvm_sequence_library #(REQ,RSP) this_type;

   static protected uvm_object_wrapper m_typewide_sequences[$];
   bit m_abort;

   extern static   function bit  m_static_check(uvm_object_wrapper seq_type);
   extern static   function bit  m_check(uvm_object_wrapper seq_type, this_type lib);
   extern          function bit  m_dyn_check(uvm_object_wrapper seq_type);
   extern          function void m_get_config();
   extern static   function bit  m_add_typewide_sequence(uvm_object_wrapper seq_type);
   extern virtual  task          execute(uvm_object_wrapper wrap);

   extern virtual  task          body();
   extern virtual  function void do_print(uvm_printer printer);
   extern          function void pre_randomize();

endclass



//------------------------------------------------------------------------------
//
// Class -- NODOCS -- uvm_sequence_library_cfg
//
// A convenient container class for configuring all the sequence library
// parameters using a single ~set~ command.
//
//| uvm_sequence_library_cfg cfg;
//| cfg = new("seqlib_cfg", UVM_SEQ_LIB_RANDC, 1000, 2000);
//|
//| uvm_config_db #(uvm_sequence_library_cfg)::set(null,
//|                                    "env.agent.sequencer.main_ph",
//|                                    "default_sequence.config",
//|                                    cfg);
//|
//------------------------------------------------------------------------------

class uvm_sequence_library_cfg extends uvm_object;
  `uvm_object_utils(uvm_sequence_library_cfg)
  uvm_sequence_lib_mode selection_mode;
  int unsigned min_random_count;
  int unsigned max_random_count;
  function new(string name="",
               uvm_sequence_lib_mode mode=UVM_SEQ_LIB_RAND,
               int unsigned min=1,
               int unsigned max=10);
    super.new(name);
    selection_mode = mode;
    min_random_count = min;
    max_random_count = max;
  endfunction
endclass



//------------------------------------------------------------------------------
// IMPLEMENTATION
//------------------------------------------------------------------------------

// new
// ---

function uvm_sequence_library::new(string name="");
   super.new(name);
   init_sequence_library();
   valid_rand_selection.constraint_mode(0);
   valid_randc_selection.constraint_mode(0);
endfunction


// m_add_typewide_sequence
// -----------------------

function bit uvm_sequence_library::m_add_typewide_sequence(uvm_object_wrapper seq_type);
  this_type::add_typewide_sequence(seq_type);
  return 1;
endfunction


// add_typewide_sequence
// ---------------------

function void uvm_sequence_library::add_typewide_sequence(uvm_object_wrapper seq_type);
  if (m_static_check(seq_type))
    m_typewide_sequences.push_back(seq_type);
endfunction


// add_typewide_sequences
// ----------------------

function void uvm_sequence_library::add_typewide_sequences(uvm_object_wrapper seq_types[$]);
  foreach (seq_types[i])
    add_typewide_sequence(seq_types[i]);
endfunction


// add_sequence
// ------------

function void uvm_sequence_library::add_sequence(uvm_object_wrapper seq_type);
  if (m_dyn_check(seq_type))
    sequences.push_back(seq_type);
endfunction


// add_sequences
// -------------

function void uvm_sequence_library::add_sequences(uvm_object_wrapper seq_types[$]);
  foreach (seq_types[i])
    add_sequence(seq_types[i]);
endfunction


// remove_sequence
// ---------------

function void uvm_sequence_library::remove_sequence(uvm_object_wrapper seq_type);
  foreach (sequences[i])
    if (sequences[i] == seq_type) begin
      sequences.delete(i);
      return;
    end
endfunction


// get_sequences
// -------------

function void uvm_sequence_library::get_sequences(ref uvm_object_wrapper seq_types[$]);
  foreach (sequences[i])
    seq_types.push_back(sequences[i]);
endfunction

// get_sequence
// ------------

function uvm_object_wrapper uvm_sequence_library::get_sequence(int unsigned idx);
  if(idx < sequences.size())
    return sequences[idx];
  else begin
    `uvm_error("SEQ_LIB/GET_SEQ", $sformatf("idx %0d > number of sequences in library", idx))
    return null;
  end

endfunction

// select_sequence
// ---------------

function int unsigned uvm_sequence_library::select_sequence(int unsigned max);
  static int unsigned counter;
  select_sequence = counter;
  counter++;
  if (counter >= max)
    counter = 0;
endfunction


//----------//
// INTERNAL //
//----------//


// init_sequence_library
// ---------------------

function void uvm_sequence_library::init_sequence_library();
  foreach (this_type::m_typewide_sequences[i])
    sequences.push_back(this_type::m_typewide_sequences[i]);
endfunction



// m_static_check
// --------------


function bit uvm_sequence_library::m_static_check(uvm_object_wrapper seq_type);
  if (!m_check(seq_type,null))
    return 0;
  foreach (m_typewide_sequences[i])
    if (m_typewide_sequences[i] == seq_type)
      return 0;
  return 1;
endfunction


// m_dyn_check
// -----------

function bit uvm_sequence_library::m_dyn_check(uvm_object_wrapper seq_type);
  if (!m_check(seq_type,this))
    return 0;
  foreach (sequences[i])
    if (sequences[i] == seq_type)
      return 0;
  return 1;
endfunction


// m_check
// -------

function bit uvm_sequence_library::m_check(uvm_object_wrapper seq_type, this_type lib);
  uvm_object obj;
  uvm_sequence_base seq;
  uvm_root top;
  uvm_coreservice_t cs;   
  string name;
  string typ;
  obj = seq_type.create_object();
`ifdef UVM_ENABLE_DEPRECATED_API
  name = (lib == null) ? type_name : lib.get_full_name();
  typ = (lib == null) ? type_name : lib.get_type_name();
`else
  name = (lib == null) ? type_name() : lib.get_full_name();
  typ = (lib == null) ? type_name() : lib.get_type_name();
`endif
  cs = uvm_coreservice_t::get();   
  top = cs.get_root();

  if (!$cast(seq, obj)) begin
    `uvm_error_context("SEQLIB/BAD_SEQ_TYPE",
        {"Object '",obj.get_type_name(),
        "' is not a sequence. Cannot add to sequence library '",name,
        "'"},top)
     return 0;
  end
  return 1;
endfunction


// pre_randomize
// -------------

function void uvm_sequence_library::pre_randomize();
  m_get_config();
endfunction


// m_get_config
// ------------

function void uvm_sequence_library::m_get_config();

  uvm_sequence_library_cfg cfg;
  string phase_name;
  uvm_phase starting_phase = get_starting_phase();
   
  if (starting_phase != null) begin
    phase_name = {starting_phase.get_name(),"_phase"};
  end
  if (uvm_config_db #(uvm_sequence_library_cfg)::get(m_sequencer, 
                                        phase_name,
                                        "default_sequence.config",
                                        cfg) ) begin
    selection_mode = cfg.selection_mode; 
    min_random_count = cfg.min_random_count; 
    max_random_count = cfg.max_random_count; 
  end
  else begin
    void'(uvm_config_db #(int unsigned)::get(m_sequencer, 
                                        phase_name,
                                        "default_sequence.min_random_count",
                                        min_random_count) );

    void'(uvm_config_db #(int unsigned)::get(m_sequencer, 
                                        phase_name,
                                        "default_sequence.max_random_count",
                                        max_random_count) );

    void'(uvm_config_db #(uvm_sequence_lib_mode)::get(m_sequencer, 
                                        phase_name,
                                        "default_sequence.selection_mode",
                                        selection_mode) );
  end

  if (max_random_count == 0) begin
    `uvm_warning("SEQLIB/MAX_ZERO",
       $sformatf("max_random_count (%0d) zero. Nothing will be done.",
       max_random_count))
    if (min_random_count > max_random_count)
      min_random_count = max_random_count;
  end
  else if (min_random_count > max_random_count) begin
    `uvm_error("SEQLIB/MIN_GT_MAX",
       $sformatf("min_random_count (%0d) greater than max_random_count (%0d). Setting min to max.",
       min_random_count,max_random_count))
    min_random_count = max_random_count;
  end
  else begin
    if (selection_mode == UVM_SEQ_LIB_ITEM) begin
      uvm_sequencer #(REQ,RSP) seqr;
      uvm_object_wrapper lhs = REQ::get_type();
      uvm_object_wrapper rhs = uvm_sequence_item::get_type();
      if (lhs == rhs) begin
        `uvm_error("SEQLIB/BASE_ITEM", {"selection_mode cannot be UVM_SEQ_LIB_ITEM when ",
          "the REQ type is the base uvm_sequence_item. Using UVM_SEQ_LIB_RAND mode"})
        selection_mode = UVM_SEQ_LIB_RAND;
      end
      if (m_sequencer == null || !$cast(seqr,m_sequencer)) begin
        `uvm_error("SEQLIB/VIRT_SEQ", {"selection_mode cannot be UVM_SEQ_LIB_ITEM when ",
          "running as a virtual sequence. Using UVM_SEQ_LIB_RAND mode"})
        selection_mode = UVM_SEQ_LIB_RAND;
      end
    end
  end

endfunction


// body
// ----

task uvm_sequence_library::body();

  uvm_object_wrapper wrap;
  uvm_phase starting_phase = get_starting_phase();
   
  if (m_sequencer == null) begin
    `uvm_fatal("SEQLIB/VIRT_SEQ", {"Sequence library 'm_sequencer' handle is null ",
      " no current support for running as a virtual sequence."})
     return;
  end

  if (sequences.size() == 0) begin
    `uvm_error("SEQLIB/NOSEQS", "Sequence library does not contain any sequences. Did you forget to call init_sequence_library() in the constructor?")
    return;
  end

  if (!get_randomize_enabled())
    m_get_config();

  m_safe_raise_starting_phase({"starting sequence library ",get_full_name()," (", get_type_name(),")"});

  `uvm_info("SEQLIB/START",
     $sformatf("Starting sequence library %s in %s phase: %0d iterations in mode %s",
      get_type_name(),
      (starting_phase != null ? starting_phase.get_name() : "unknown"),
      sequence_count, selection_mode.name()),UVM_LOW)

   `uvm_info("SEQLIB/SPRINT",{"\n",sprint(uvm_table_printer::get_default())},UVM_FULL)

    case (selection_mode)

      UVM_SEQ_LIB_RAND: begin
        valid_rand_selection.constraint_mode(1);
        valid_sequence_count.constraint_mode(0);
        for (int i=1; i<=sequence_count; i++) begin
          if (!randomize(select_rand)) begin
            `uvm_error("SEQLIB/RAND_FAIL", "Random sequence selection failed")
            break;
          end
          else begin
            wrap = sequences[select_rand];
          end
          execute(wrap);
        end
        valid_rand_selection.constraint_mode(0);
        valid_sequence_count.constraint_mode(1);
      end

      UVM_SEQ_LIB_RANDC: begin
        uvm_object_wrapper q[$];
        valid_randc_selection.constraint_mode(1);
        valid_sequence_count.constraint_mode(0);
        for (int i=1; i<=sequence_count; i++) begin
          if (!randomize(select_randc)) begin
            `uvm_error("SEQLIB/RANDC_FAIL", "Random sequence selection failed")
            break;
          end
          else begin
            wrap = sequences[select_randc];
          end
          q.push_back(wrap);
        end
        valid_randc_selection.constraint_mode(0);
        valid_sequence_count.constraint_mode(1);
        foreach(q[i])
          execute(q[i]);
        valid_randc_selection.constraint_mode(0);
        valid_sequence_count.constraint_mode(1);
      end

      UVM_SEQ_LIB_ITEM: begin
        for (int i=1; i<=sequence_count; i++) begin
          wrap = REQ::get_type();
          execute(wrap);
        end
      end

      UVM_SEQ_LIB_USER: begin
        for (int i=1; i<=sequence_count; i++) begin
          int user_selection;
          user_selection = select_sequence(sequences.size()-1);
          if (user_selection >= sequences.size()) begin
            `uvm_error("SEQLIB/USER_FAIL", "User sequence selection out of range")
            wrap = REQ::get_type();
          end
          else begin
            wrap = sequences[user_selection];
          end
          execute(wrap);
        end
      end

      default: begin
        `uvm_fatal("SEQLIB/RAND_MODE", 
           $sformatf("Unknown random sequence selection mode: %0d",selection_mode))
      end
     endcase

  `uvm_info("SEQLIB/END",{"Ending sequence library in phase ",
            (starting_phase != null ? starting_phase.get_name() : "unknown")},UVM_LOW)
 
  `uvm_info("SEQLIB/DSTRB",$sformatf("%p",seqs_distrib),UVM_HIGH)

  m_safe_drop_starting_phase({"starting sequence library ",get_full_name()," (", get_type_name(),")"});

endtask


// execute
// -------

task uvm_sequence_library::execute(uvm_object_wrapper wrap);

  uvm_object obj;
  uvm_sequence_item seq_or_item;
  uvm_sequence_base seq_base;
  REQ req_item;
  
  uvm_coreservice_t cs = uvm_coreservice_t::get();                                                     
  uvm_factory factory=cs.get_factory();

  obj = factory.create_object_by_type(wrap,get_full_name(),
           $sformatf("%s:%0d",wrap.get_type_name(),sequences_executed+1));

  if (!$cast(seq_base, obj)) begin
     // If we're executing an item (not a sequence)
     if (!$cast(req_item, obj)) begin
        // But it's not our item type (This can happen if we were parameterized with
        // a pure virtual type, because we're getting get_type() from the base class)
        `uvm_error("SEQLIB/WRONG_ITEM_TYPE", {"The item created by '", get_full_name(), "' when in 'UVM_SEQ_LIB_ITEM' mode doesn't match the REQ type which  was passed in to the uvm_sequence_library#(REQ[,RSP]), this can happen if the REQ type which was passed in was a pure-virtual type.  Either configure the factory overrides to properly generate items for this sequence library, or do not execute this sequence library in UVM_SEQ_LIB_ITEM mode."})
         return;
     end
  end
   
  void'($cast(seq_or_item,obj)); // already qualified, 
   
  `uvm_info("SEQLIB/EXEC",{"Executing ",(seq_or_item.is_item() ? "item " : "sequence "),seq_or_item.get_name(),
                           " (",seq_or_item.get_type_name(),")"},UVM_FULL)
  seq_or_item.print_sequence_info = 1;
  `uvm_rand_send(seq_or_item)
  seqs_distrib[seq_or_item.get_type_name()] = seqs_distrib[seq_or_item.get_type_name()]+1;

  sequences_executed++;

endtask
  


// do_print
// --------

function void uvm_sequence_library::do_print(uvm_printer printer);
   printer.print_field_int("min_random_count",min_random_count,32,UVM_DEC,,"int unsigned");
   printer.print_field_int("max_random_count",max_random_count,32,UVM_DEC,,"int unsigned");
   printer.print_generic("selection_mode","uvm_sequence_lib_mode",32,selection_mode.name());
   printer.print_field_int("sequence_count",sequence_count,32,UVM_DEC,,"int unsigned");

   printer.print_array_header("typewide_sequences",m_typewide_sequences.size(),"queue_object_types");
   foreach (m_typewide_sequences[i])
     printer.print_generic($sformatf("[%0d]",i),"uvm_object_wrapper","-",m_typewide_sequences[i].get_type_name());
   printer.print_array_footer();

   printer.print_array_header("sequences",sequences.size(),"queue_object_types");
   foreach (sequences[i])
     printer.print_generic($sformatf("[%0d]",i),"uvm_object_wrapper","-",sequences[i].get_type_name());
   printer.print_array_footer();

   printer.print_array_header("seqs_distrib",seqs_distrib.num(),"as_int_string");
   foreach (seqs_distrib[typ]) begin
     printer.print_field_int({"[",typ,"]"},seqs_distrib[typ],32,,UVM_DEC,"int unsigned");
   end
   printer.print_array_footer();
endfunction
