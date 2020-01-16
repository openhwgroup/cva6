//
//------------------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2010-2014 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2013 Verilab
// Copyright 2010-2012 AMD
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2012-2018 Cisco Systems, Inc.
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

//------------------------------------------------------------------------------
//
// Section --NODOCS-- Types and Enumerations
//
//------------------------------------------------------------------------------

//------------------------
// Group --NODOCS-- Field automation
//------------------------


parameter UVM_STREAMBITS = `UVM_MAX_STREAMBITS; 


// Type --NODOCS-- uvm_bitstream_t
//
// The bitstream type is used as a argument type for passing integral values
// in such methods as <uvm_object::set_int_local>, <uvm_config_int>, 
// <uvm_printer::print_field>, <uvm_recorder::record_field>, 
// <uvm_packer::pack_field> and <uvm_packer::unpack_field>.

typedef logic signed [UVM_STREAMBITS-1:0] uvm_bitstream_t;

// Type --NODOCS-- uvm_integral_t
//
// The integral type is used as a argument type for passing integral values
// of 64 bits or less in such methods as 
// <uvm_printer::print_field_int>, <uvm_recorder::record_field_int>, 
// <uvm_packer::pack_field_int> and <uvm_packer::unpack_field_int>.
//

typedef logic signed [63:0] uvm_integral_t;



// The number of least significant bits of uvm_field_flag_t which are reserved for this
// implementation.  Derived from the value of UVM_RADIX which uses the most significant subset.
parameter UVM_FIELD_FLAG_RESERVED_BITS = 28;

// The type for storing flag values passed to the uvm_field_* macros.
typedef bit [`UVM_FIELD_FLAG_SIZE-1 : 0] uvm_field_flag_t;

// Enum -- NODOCS -- uvm_radix_enum
//
// Specifies the radix to print or record in.
//
// UVM_BIN       - Selects binary (%b) format
// UVM_DEC       - Selects decimal (%d) format
// UVM_UNSIGNED  - Selects unsigned decimal (%u) format
// UVM_UNFORMAT2 - Selects unformatted 2 value data (%u) format
// UVM_UNFORMAT4 - Selects unformatted 4 value data (%z) format
// UVM_OCT       - Selects octal (%o) format
// UVM_HEX       - Selects hexadecimal (%h) format
// UVM_STRING    - Selects string (%s) format
// UVM_TIME      - Selects time (%t) format
// UVM_ENUM      - Selects enumeration value (name) format
// UVM_REAL      - Selects real (%g) in exponential or decimal format,
//                 whichever format results in the shorter printed output
// UVM_REAL_DEC  - Selects real (%f) in decimal format
// UVM_REAL_EXP  - Selects real (%e) in exponential format

typedef enum uvm_field_flag_t {
   UVM_BIN       = 'h1000000,
   UVM_DEC       = 'h2000000,
   UVM_UNSIGNED  = 'h3000000,
   UVM_UNFORMAT2 = 'h4000000,
   UVM_UNFORMAT4 = 'h5000000,
   UVM_OCT       = 'h6000000,
   UVM_HEX       = 'h7000000,
   UVM_STRING    = 'h8000000,
   UVM_TIME      = 'h9000000,
   UVM_ENUM      = 'ha000000,
   UVM_REAL      = 'hb000000,
   UVM_REAL_DEC  = 'hc000000,
   UVM_REAL_EXP  = 'hd000000,
   UVM_NORADIX   = 0
} uvm_radix_enum;

parameter UVM_RADIX = 'hf000000; //4 bits setting the radix


// Function- uvm_radix_to_string

function string uvm_radix_to_string(uvm_radix_enum radix);
  case(radix)
    UVM_BIN:        return "b";
    UVM_OCT:        return "o";
    UVM_DEC:        return "d";
    UVM_HEX:        return "h";
    UVM_UNSIGNED:   return "u";
    UVM_UNFORMAT2:  return "u";
    UVM_UNFORMAT4:  return "z";
    UVM_STRING:     return "s";
    UVM_TIME:       return "t";
    UVM_ENUM:       return "s";
    UVM_REAL:       return "g";
    UVM_REAL_DEC:   return "f";
    UVM_REAL_EXP:   return "e";
    default:        return "x"; //hex
  endcase
endfunction


// Enum --NODOCS-- uvm_recursion_policy_enum
//
// Specifies the policy for copying objects.
//
// UVM_DEEP      - Objects are deep copied (object must implement <uvm_object::copy> method)
// UVM_SHALLOW   - Objects are shallow copied using default SV copy.
// UVM_REFERENCE - Only object handles are copied.

typedef enum uvm_field_flag_t { 
  UVM_DEFAULT_POLICY = 0, 
  UVM_DEEP           = (1<<16), 
  UVM_SHALLOW        = (1<<17), 
  UVM_REFERENCE      = (1<<18)
 } uvm_recursion_policy_enum;

// UVM_RECURSION is a mask for uvm_recursion_policy_enum, similar to
// UVM_RADIX for uvm_radix_enum.  Flags can be AND'd with the mask
// before casting into the enum, a`la:
// 
//| uvm_recursion_policy_enum foo;
//| foo = uvm_recursion_policy_enum'(flags&UVM_RECURSION);
//
parameter UVM_RECURSION = (UVM_DEEP|UVM_SHALLOW|UVM_REFERENCE);


// Enum --NODOCS-- uvm_active_passive_enum
//
// Convenience value to define whether a component, usually an agent,
// is in "active" mode or "passive" mode.
//
// UVM_PASSIVE - "Passive" mode
// UVM_ACTIVE  - "Active" mode
typedef enum bit { UVM_PASSIVE=0, UVM_ACTIVE=1 } uvm_active_passive_enum;


// Parameter --NODOCS-- `uvm_field_* macro flags
//
// Defines what operations a given field should be involved in.
// Bitwise OR all that apply.
//
// UVM_DEFAULT   - All field operations turned on
// UVM_COPY      - Field will participate in <uvm_object::copy>
// UVM_COMPARE   - Field will participate in <uvm_object::compare>
// UVM_PRINT     - Field will participate in <uvm_object::print>
// UVM_RECORD    - Field will participate in <uvm_object::record>
// UVM_PACK      - Field will participate in <uvm_object::pack>
//
// UVM_NOCOPY    - Field will not participate in <uvm_object::copy>
// UVM_NOCOMPARE - Field will not participate in <uvm_object::compare>
// UVM_NOPRINT   - Field will not participate in <uvm_object::print>
// UVM_NORECORD  - Field will not participate in <uvm_object::record>
// UVM_NOPACK    - Field will not participate in <uvm_object::pack>
//
// UVM_DEEP      - Object field will be deep copied
// UVM_SHALLOW   - Object field will be shallow copied
// UVM_REFERENCE - Object field will copied by reference
//
// UVM_READONLY  - Object field will NOT be automatically configured.

parameter uvm_field_flag_t UVM_MACRO_NUMFLAGS    = 19;
//A=ABSTRACT Y=PHYSICAL
//F=REFERENCE, S=SHALLOW, D=DEEP
//K=PACK, R=RECORD, P=PRINT, M=COMPARE, C=COPY
//--------------------------- AYFSD K R P M C
parameter uvm_field_flag_t UVM_DEFAULT     = 'b000010101010101;
parameter uvm_field_flag_t UVM_ALL_ON      = 'b000000101010101;
parameter uvm_field_flag_t UVM_FLAGS_ON    = 'b000000101010101;
parameter uvm_field_flag_t UVM_FLAGS_OFF   = 0;

//Values are OR'ed into a 32 bit value
//and externally
parameter uvm_field_flag_t UVM_COPY         = (1<<0);
parameter uvm_field_flag_t UVM_NOCOPY       = (1<<1);
parameter uvm_field_flag_t UVM_COMPARE      = (1<<2);
parameter uvm_field_flag_t UVM_NOCOMPARE    = (1<<3);
parameter uvm_field_flag_t UVM_PRINT        = (1<<4);
parameter uvm_field_flag_t UVM_NOPRINT      = (1<<5);
parameter uvm_field_flag_t UVM_RECORD       = (1<<6);
parameter uvm_field_flag_t UVM_NORECORD     = (1<<7);
parameter uvm_field_flag_t UVM_PACK         = (1<<8);
parameter uvm_field_flag_t UVM_NOPACK       = (1<<9);
parameter uvm_field_flag_t UVM_UNPACK       = (1<<10);
parameter uvm_field_flag_t UVM_NOUNPACK     = UVM_NOPACK;
parameter uvm_field_flag_t UVM_SET          = (1<<11);
parameter uvm_field_flag_t UVM_NOSET        = (1<<12);
`ifdef UVM_ENABLE_DEPRECATED_API
parameter uvm_field_flag_t UVM_PHYSICAL     = (1<<13);
parameter uvm_field_flag_t UVM_ABSTRACT     = (1<<14);
parameter uvm_field_flag_t UVM_READONLY     = UVM_NOSET;
`endif
parameter uvm_field_flag_t UVM_NODEFPRINT   = (1<<15); //??
//parameter UVM_DEEP         = (1<<16);
//parameter UVM_SHALLOW      = (1<<17);
//parameter UVM_REFERENCE    = (1<<18);

//Extra values that are used for extra methods
parameter uvm_field_flag_t UVM_MACRO_EXTRAS  = (1<<UVM_MACRO_NUMFLAGS);
parameter uvm_field_flag_t UVM_FLAGS         = UVM_MACRO_EXTRAS+1;
parameter uvm_field_flag_t UVM_CHECK_FIELDS  = UVM_MACRO_EXTRAS+2;
parameter uvm_field_flag_t UVM_END_DATA_EXTRA = UVM_MACRO_EXTRAS+3;


//Get and set methods (in uvm_object). Used by the set/get* functions
//to tell the object what operation to perform on the fields.
parameter uvm_field_flag_t UVM_START_FUNCS   = UVM_END_DATA_EXTRA+1;
parameter uvm_field_flag_t UVM_END_FUNCS     = UVM_START_FUNCS+1;

//Global string variables
string uvm_aa_string_key;



//-----------------
// Group --NODOCS-- Reporting
//-----------------

// Enum --NODOCS-- uvm_severity
//
// Defines all possible values for report severity.
//
//   UVM_INFO    - Informative message.
//   UVM_WARNING - Indicates a potential problem.
//   UVM_ERROR   - Indicates a real problem. Simulation continues subject
//                 to the configured message action.
//   UVM_FATAL   - Indicates a problem from which simulation cannot
//                 recover. Simulation exits via $finish after a #0 delay.

typedef enum bit [1:0]
{
  UVM_INFO,
  UVM_WARNING,
  UVM_ERROR,
  UVM_FATAL
} uvm_severity;

// Enum --NODOCS-- uvm_action
//
// Defines all possible values for report actions. Each report is configured
// to execute one or more actions, determined by the bitwise OR of any or all
// of the following enumeration constants.
//
//   UVM_NO_ACTION - No action is taken
//   UVM_DISPLAY   - Sends the report to the standard output
//   UVM_LOG       - Sends the report to the file(s) for this (severity,id) pair
//   UVM_COUNT     - Counts the number of reports with the COUNT attribute.
//                   When this value reaches max_quit_count, the simulation terminates
//   UVM_EXIT      - Terminates the simulation immediately.
//   UVM_CALL_HOOK - Callback the report hook methods 
//   UVM_STOP      - Causes ~$stop~ to be executed, putting the simulation into
//                   interactive mode.
//   UVM_RM_RECORD - Sends the report to the recorder


typedef int uvm_action;

typedef enum
{
  UVM_NO_ACTION = 'b0000000,
  UVM_DISPLAY   = 'b0000001,
  UVM_LOG       = 'b0000010,
  UVM_COUNT     = 'b0000100,
  UVM_EXIT      = 'b0001000,
  UVM_CALL_HOOK = 'b0010000,
  UVM_STOP      = 'b0100000,
  UVM_RM_RECORD = 'b1000000
} uvm_action_type;


// Enum --NODOCS-- uvm_verbosity
//
// Defines standard verbosity levels for reports.
//
//  UVM_NONE   - Report is always printed. Verbosity level setting cannot
//               disable it.
//  UVM_LOW    - Report is issued if configured verbosity is set to UVM_LOW
//               or above.
//  UVM_MEDIUM - Report is issued if configured verbosity is set to UVM_MEDIUM
//               or above.
//  UVM_HIGH   - Report is issued if configured verbosity is set to UVM_HIGH
//               or above.
//  UVM_FULL   - Report is issued if configured verbosity is set to UVM_FULL
//               or above.

typedef enum
{
  UVM_NONE   = 0,
  UVM_LOW    = 100,
  UVM_MEDIUM = 200,
  UVM_HIGH   = 300,
  UVM_FULL   = 400,
  UVM_DEBUG  = 500
} uvm_verbosity;



//-----------------
// Group --NODOCS-- Port Type
//-----------------

// Enum --NODOCS-- uvm_port_type_e
//
// Specifies the type of port
//
// UVM_PORT           - The port requires the interface that is its type
//                      parameter.
// UVM_EXPORT         - The port provides the interface that is its type
//                      parameter via a connection to some other export or
//                      implementation.
// UVM_IMPLEMENTATION - The port provides the interface that is its type
//                      parameter, and it is bound to the component that
//                      implements the interface.

typedef enum
{
  UVM_PORT ,
  UVM_EXPORT ,
  UVM_IMPLEMENTATION
} uvm_port_type_e;


//-----------------
// Group --NODOCS-- Sequences
//-----------------

// Enum --NODOCS-- uvm_sequencer_arb_mode
//
// Specifies a sequencer's arbitration mode
//
// UVM_SEQ_ARB_FIFO          - Requests are granted in FIFO order (default)
// UVM_SEQ_ARB_WEIGHTED      - Requests are granted randomly by weight
// UVM_SEQ_ARB_RANDOM        - Requests are granted randomly
// UVM_SEQ_ARB_STRICT_FIFO   - Requests at highest priority granted in fifo order
// UVM_SEQ_ARB_STRICT_RANDOM - Requests at highest priority granted in randomly
// UVM_SEQ_ARB_USER          - Arbitration is delegated to the user-defined 
//                             function, user_priority_arbitration. That function
//                             will specify the next sequence to grant.


typedef enum
{
  UVM_SEQ_ARB_FIFO,
  UVM_SEQ_ARB_WEIGHTED,
  UVM_SEQ_ARB_RANDOM,
  UVM_SEQ_ARB_STRICT_FIFO,
  UVM_SEQ_ARB_STRICT_RANDOM,
  UVM_SEQ_ARB_USER
} uvm_sequencer_arb_mode;


typedef uvm_sequencer_arb_mode UVM_SEQ_ARB_TYPE; // backward compat


// Enum --NODOCS-- uvm_sequence_state_enum
//
// Defines current sequence state
//
// UVM_CREATED            - The sequence has been allocated.
// UVM_PRE_START          - The sequence is started and the
//                          <uvm_sequence_base::pre_start()> task is
//                          being executed.
// UVM_PRE_BODY           - The sequence is started and the
//                          <uvm_sequence_base::pre_body()> task is
//                           being executed.
// UVM_BODY               - The sequence is started and the
//                          <uvm_sequence_base::body()> task is
//                          being executed.
// UVM_ENDED              - The sequence has completed the execution of the 
//                          <uvm_sequence_base::body()> task.
// UVM_POST_BODY          - The sequence is started and the
//                          <uvm_sequence_base::post_body()> task is
//                           being executed.
// UVM_POST_START         - The sequence is started and the
//                          <uvm_sequence_base::post_start()> task is
//                          being executed.
// UVM_STOPPED            - The sequence has been forcibly ended by issuing a
//                          <uvm_sequence_base::kill()> on the sequence.
// UVM_FINISHED           - The sequence is completely finished executing.

typedef enum
{
  UVM_CREATED   = 1,
  UVM_PRE_START = 2,
  UVM_PRE_BODY  = 4,
  UVM_BODY      = 8,
  UVM_POST_BODY = 16,
  UVM_POST_START= 32,
  UVM_ENDED     = 64,
  UVM_STOPPED   = 128,
  UVM_FINISHED  = 256
} uvm_sequence_state;

typedef uvm_sequence_state uvm_sequence_state_enum; // backward compat


// Enum --NODOCS-- uvm_sequence_lib_mode
//
// Specifies the random selection mode of a sequence library
//
// UVM_SEQ_LIB_RAND  - Random sequence selection
// UVM_SEQ_LIB_RANDC - Random cyclic sequence selection
// UVM_SEQ_LIB_ITEM  - Emit only items, no sequence execution
// UVM_SEQ_LIB_USER  - Apply a user-defined random-selection algorithm

typedef enum
{
  UVM_SEQ_LIB_RAND,
  UVM_SEQ_LIB_RANDC,
  UVM_SEQ_LIB_ITEM,
  UVM_SEQ_LIB_USER
} uvm_sequence_lib_mode;



//---------------
// Group --NODOCS-- Phasing
//---------------

// Enum --NODOCS-- uvm_phase_type
//
// This is an attribute of a <uvm_phase> object which defines the phase
// type. 
//
//   UVM_PHASE_IMP      - The phase object is used to traverse the component
//                        hierarchy and call the component phase method as
//                        well as the ~phase_started~ and ~phase_ended~ callbacks.
//                        These nodes are created by the phase macros,
//                        `uvm_builtin_task_phase, `uvm_builtin_topdown_phase,
//                        and `uvm_builtin_bottomup_phase. These nodes represent
//                        the phase type, i.e. uvm_run_phase, uvm_main_phase.
//
//   UVM_PHASE_NODE     - The object represents a simple node instance in
//                        the graph. These nodes will contain a reference to
//                        their corresponding IMP object. 
//
//   UVM_PHASE_SCHEDULE - The object represents a portion of the phasing graph,
//                        typically consisting of several NODE types, in series,
//                        parallel, or both.
//
//   UVM_PHASE_TERMINAL - This internal object serves as the termination NODE
//                        for a SCHEDULE phase object.
//
//   UVM_PHASE_DOMAIN   - This object represents an entire graph segment that
//                        executes in parallel with the 'run' phase.
//                        Domains may define any network of NODEs and
//                        SCHEDULEs. The built-in domain, ~uvm~, consists
//                        of a single schedule of all the run-time phases,
//                        starting with ~pre_reset~ and ending with
//                        ~post_shutdown~.
//
typedef enum { UVM_PHASE_IMP,
               UVM_PHASE_NODE,
               UVM_PHASE_TERMINAL,
               UVM_PHASE_SCHEDULE,
               UVM_PHASE_DOMAIN,
               UVM_PHASE_GLOBAL
} uvm_phase_type;


// Enum --NODOCS-- uvm_phase_state
// ---------------------
//
// The set of possible states of a phase. This is an attribute of a schedule
// node in the graph, not of a phase, to maintain independent per-domain state
//
//   UVM_PHASE_UNINITIALIZED - The state is uninitialized.  This is the default
//             state for phases, and for nodes which have not yet been added to
//             a schedule.
//
//   UVM_PHASE_DORMANT -  The schedule is not currently operating on the phase
//             node, however it will be scheduled at some point in the future.
//
//   UVM_PHASE_SCHEDULED - At least one immediate predecessor has completed.
//              Scheduled phases block until all predecessors complete or
//              until a jump is executed.
//
//   UVM_PHASE_SYNCING - All predecessors complete, checking that all synced
//              phases (e.g. across domains) are at or beyond this point
//
//   UVM_PHASE_STARTED - phase ready to execute, running phase_started() callback
//
//   UVM_PHASE_EXECUTING - An executing phase is one where the phase callbacks are
//              being executed. Its process is tracked by the phaser.
//
//   UVM_PHASE_READY_TO_END - no objections remain in this phase or in any
//              predecessors of its successors or in any sync'd phases. This 
//              state indicates an opportunity for any phase that needs extra  
//              time for a clean exit to raise an objection, thereby causing a 
//              return to UVM_PHASE_EXECUTING.  If no objection is raised, state
//              will transition to UVM_PHASE_ENDED after a delta cycle.
//              (An example of predecessors of successors: The successor to
//              phase 'run' is 'extract', whose predecessors are 'run' and 
//              'post_shutdown'. Therefore, 'run' will go to this state when
//              both its objections and those of 'post_shutdown' are all dropped.
//
//   UVM_PHASE_ENDED - phase completed execution, now running phase_ended() callback
//
//   UVM_PHASE_JUMPING - all processes related to phase are being killed and all
//                       predecessors are forced into the DONE state.
//
//   UVM_PHASE_CLEANUP - all processes related to phase are being killed
//
//   UVM_PHASE_DONE - A phase is done after it terminated execution.  Becoming
//              done may enable a waiting successor phase to execute.
//
//    The state transitions occur as follows:
//
//|   UNINITIALIZED -> DORMANT -> SCHED -> SYNC -> START -> EXEC -> READY -> END -+-> CLEAN -> DONE
//|                       ^                                                       |
//|                       |                      <-- jump_to                      |
//|                       +-------------------------------------------- JUMPING< -+

   typedef enum { UVM_PHASE_UNINITIALIZED = 0,
                  UVM_PHASE_DORMANT      = 1,
                  UVM_PHASE_SCHEDULED    = 2,
                  UVM_PHASE_SYNCING      = 4,
                  UVM_PHASE_STARTED      = 8,
                  UVM_PHASE_EXECUTING    = 16,
                  UVM_PHASE_READY_TO_END = 32,
                  UVM_PHASE_ENDED        = 64,
                  UVM_PHASE_CLEANUP      = 128,
                  UVM_PHASE_DONE         = 256,
                  UVM_PHASE_JUMPING      = 512
                  } uvm_phase_state;



// Enum --NODOCS-- uvm_wait_op
//
// Specifies the operand when using methods like <uvm_phase::wait_for_state>.
//
// UVM_EQ  - equal
// UVM_NE  - not equal
// UVM_LT  - less than
// UVM_LTE - less than or equal to
// UVM_GT  - greater than
// UVM_GTE - greater than or equal to
//
typedef enum { UVM_LT,
               UVM_LTE,
               UVM_NE,
               UVM_EQ,
               UVM_GT,
               UVM_GTE
} uvm_wait_op;


//------------------
// Group --NODOCS-- Objections
//------------------

// Enum --NODOCS-- uvm_objection_event
//
// Enumerated the possible objection events one could wait on. See
// <uvm_objection::wait_for>.
//
// UVM_RAISED      - an objection was raised
// UVM_DROPPED     - an objection was raised
// UVM_ALL_DROPPED - all objections have been dropped
//
typedef enum { UVM_RAISED      = 'h01, 
               UVM_DROPPED     = 'h02,
               UVM_ALL_DROPPED = 'h04
} uvm_objection_event;

`ifdef UVM_ENABLE_DEPRECATED_API

//------------------------------
// Group --NODOCS-- Default Policy Classes
//------------------------------
//
// Policy classes copying, comparing, packing, unpacking, and recording
// <uvm_object>-based objects.


typedef class uvm_printer;
typedef class uvm_table_printer;
typedef class uvm_tree_printer;
typedef class uvm_line_printer;
typedef class uvm_comparer;
typedef class uvm_packer;
typedef class uvm_tr_database;
typedef class uvm_text_tr_database;
typedef class uvm_recorder;


// Variable --NODOCS-- uvm_default_table_printer
//
// The table printer is a global object that can be used with
// <uvm_object::do_print> to get tabular style printing.

uvm_table_printer uvm_default_table_printer = new();


// Variable --NODOCS-- uvm_default_tree_printer
//
// The tree printer is a global object that can be used with
// <uvm_object::do_print> to get multi-line tree style printing.

uvm_tree_printer uvm_default_tree_printer  = new();


// Variable --NODOCS-- uvm_default_line_printer
//
// The line printer is a global object that can be used with
// <uvm_object::do_print> to get single-line style printing.

uvm_line_printer uvm_default_line_printer  = new();


// Variable --NODOCS-- uvm_default_printer
//
// The default printer policy. Used when calls to <uvm_object::print>
// or <uvm_object::sprint> do not specify a printer policy.
//
// The default printer may be set to any legal <uvm_printer> derived type,
// including the global line, tree, and table printers described above.

uvm_printer uvm_default_printer = uvm_default_table_printer;


// Variable --NODOCS-- uvm_default_packer
//
// The default packer policy. Used when calls to <uvm_object::pack>
// and <uvm_object::unpack> do not specify a packer policy.

uvm_packer uvm_default_packer = new();


// Variable --NODOCS-- uvm_default_comparer
//
//
// The default compare policy. Used when calls to <uvm_object::compare>
// do not specify a comparer policy.

uvm_comparer uvm_default_comparer = new(); // uvm_comparer::init();

`endif //UVM_ENABLE_DEPRECATED_API

typedef int UVM_FILE;

parameter UVM_FILE UVM_STDIN  = 32'h8000_0000;
parameter UVM_FILE UVM_STDOUT = 32'h8000_0001;
parameter UVM_FILE UVM_STDERR = 32'h8000_0002;

typedef enum {
	UVM_CORE_UNINITIALIZED,
	UVM_CORE_INITIALIZED,
	UVM_CORE_PRE_RUN,
	UVM_CORE_RUNNING,
	UVM_CORE_POST_RUN,
	UVM_CORE_FINISHED,
	UVM_CORE_PRE_ABORT,
	UVM_CORE_ABORTED	
} uvm_core_state;

uvm_core_state m_uvm_core_state = UVM_CORE_UNINITIALIZED;

typedef class uvm_object_wrapper;
uvm_object_wrapper uvm_deferred_init[$];
