//
//-----------------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2015 Analog Devices, Inc.
// Copyright 2011-2018 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2012 AMD
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2017-2018 Cisco Systems, Inc.
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

typedef class uvm_report_message;

// File -- NODOCS -- UVM Recorders
//
// The uvm_recorder class serves two purposes:
//  - Firstly, it is an abstract representation of a record within a
//    <uvm_tr_stream>.
//  - Secondly, it is a policy object for recording fields ~into~ that
//    record within the ~stream~.
//

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_recorder
//
// Abstract class which defines the ~recorder~ API.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 16.4.1
virtual class uvm_recorder extends uvm_policy;

   `uvm_object_abstract_utils(uvm_recorder)

  // Variable- m_stream_dap
  // Data access protected reference to the stream
  local uvm_set_before_get_dap#(uvm_tr_stream) m_stream_dap;

  // Variable- m_warn_null_stream
  // Used to limit the number of warnings 
  local bit m_warn_null_stream;

  // Variable- m_is_opened
  // Used to indicate recorder is open
  local bit m_is_opened;
   
  // Variable- m_is_closed
  // Used to indicate recorder is closed
  local bit m_is_closed;

  // !m_is_opened && !m_is_closed == m_is_freed

  // Variable- m_open_time
  // Used to store the open_time
  local time m_open_time;

  // Variable- m_close_time
  // Used to store the close_time
  local time m_close_time;
   
  // Variable- recording_depth
  int recording_depth;

  // Variable -- NODOCS -- default_radix
  //
  // This is the default radix setting if <record_field> is called without
  // a radix.

  uvm_radix_enum default_radix = UVM_HEX;

`ifdef UVM_ENABLE_DEPRECATED_API
   
  // Variable -- NODOCS -- physical
  //
  // This bit provides a filtering mechanism for fields. 
  //
  // The <abstract> and physical settings allow an object to distinguish between
  // two different classes of fields. 
  //
  // It is up to you, in the <uvm_object::do_record> method, to test the
  // setting of this field if you want to use the physical trait as a filter.

  bit physical = 1;


  // Variable -- NODOCS -- abstract
  //
  // This bit provides a filtering mechanism for fields. 
  //
  // The abstract and physical settings allow an object to distinguish between
  // two different classes of fields. 
  //
  // It is up to you, in the <uvm_object::do_record> method, to test the
  // setting of this field if you want to use the abstract trait as a filter.

  bit abstract = 1;

`endif //  `ifdef UVM_ENABLE_DEPRECATED_API
   
  // Variable -- NODOCS -- identifier
  //
  // This bit is used to specify whether or not an object's reference should be
  // recorded when the object is recorded. 

  bit identifier = 1;


  // Variable -- NODOCS -- recursion_policy
  //
  // Sets the recursion policy for recording objects. 
  //
  // The default policy is deep (which means to recurse an object).

`ifndef UVM_ENABLE_DEPRECATED_API
  local
`endif
  uvm_recursion_policy_enum policy = UVM_DEFAULT_POLICY;

  // @uvm-ieee 1800.2-2017 auto 16.4.2.1
  virtual function void set_recursion_policy(uvm_recursion_policy_enum policy);
    this.policy  = policy;
  endfunction : set_recursion_policy

  // @uvm-ieee 1800.2-2017 auto 16.4.2.1
  virtual function uvm_recursion_policy_enum get_recursion_policy();
    return this.policy;
  endfunction : get_recursion_policy

  // @uvm-ieee 1800.2-2017 auto 16.4.4.1
  virtual function void flush();
    policy      = UVM_DEFAULT_POLICY;
    identifier  = 1;
    free();
  endfunction : flush
  
   // Variable- m_ids_by_recorder
   // An associative array of int, indexed by uvm_recorders.  This
   // provides a unique 'id' or 'handle' for each recorder, which can be
   // used to identify the recorder.
   //
   // By default, neither ~m_ids_by_recorder~ or ~m_recorders_by_id~ are
   // used.  Recorders are only placed in the arrays when the user
   // attempts to determine the id for a recorder.
   local static int m_ids_by_recorder[uvm_recorder];


  function new(string name = "uvm_recorder");
     super.new(name);
     m_stream_dap = new("stream_dap");
     m_warn_null_stream = 1;
  endfunction

   // Group -- NODOCS -- Configuration API
   

   // @uvm-ieee 1800.2-2017 auto 16.4.3
   function uvm_tr_stream get_stream();
      if (!m_stream_dap.try_get(get_stream)) begin
         if (m_warn_null_stream == 1) 
           `uvm_warning("UVM/REC/NO_CFG",
                        $sformatf("attempt to retrieve STREAM from '%s' before it was set!",
                                  get_name()))
         m_warn_null_stream = 0;
      end
   endfunction : get_stream

   // Group -- NODOCS -- Transaction Recorder API
   //
   // Once a recorder has been opened via <uvm_tr_stream::open_recorder>, the user
   // can ~close~ the recorder.
   //
   // Due to the fact that many database implementations will require crossing
   // a language boundary, an additional step of ~freeing~ the recorder is required.
   //
   // A ~link~ can be established within the database any time between ~open~ and
   // ~free~, however it is illegal to establish a link after ~freeing~ the recorder.
   //


   // @uvm-ieee 1800.2-2017 auto 16.4.4.2
   function void close(time close_time = 0);
      if (close_time == 0)
        close_time = $realtime;

      if (!is_open())
        return;

      do_close(close_time);
      
      m_is_opened = 0;
      m_is_closed = 1;
      m_close_time = close_time;
   endfunction : close


   // @uvm-ieee 1800.2-2017 auto 16.4.4.3
   function void free(time close_time = 0);
	   process p=process::self();
	   string s;
	
       uvm_tr_stream stream;
       
      if (!is_open() && !is_closed())
        return;

      if (is_open()) begin
         close(close_time);
      end

      do_free();

      // Clear out internal state
      stream = get_stream();
      
      m_is_closed = 0;
      if(p != null)
      	s=p.get_randstate();
      m_stream_dap = new("stream_dap");
      if(p != null)
      	p.set_randstate(s);
      m_warn_null_stream = 1;
      if (m_ids_by_recorder.exists(this))
        m_free_id(m_ids_by_recorder[this]);

      // Clear out stream state
      if (stream != null)
        stream.m_free_recorder(this);
   endfunction : free
      

   // @uvm-ieee 1800.2-2017 auto 16.4.4.4
   function bit is_open();
      return m_is_opened;
   endfunction : is_open


   // @uvm-ieee 1800.2-2017 auto 16.4.4.5
   function time get_open_time();
      return m_open_time;
   endfunction : get_open_time


   // @uvm-ieee 1800.2-2017 auto 16.4.4.6
   function bit is_closed();
      return m_is_closed;
   endfunction : is_closed
    

   // @uvm-ieee 1800.2-2017 auto 16.4.4.7
   function time get_close_time();
      return m_close_time;
   endfunction : get_close_time

  // Function- m_do_open
  // Initializes the internal state of the recorder.
  //
  // Parameters -- NODOCS --
  // stream - The stream which spawned this recorder
  //
  // This method will trigger a <do_open> call.
  //
  // An error will be asserted if:
  // - ~m_do_open~ is called more than once without the
  //  recorder being ~freed~ in between.
  // - ~stream~ is ~null~
  function void m_do_open(uvm_tr_stream stream, time open_time, string type_name);
     uvm_tr_stream m_stream;
     if (stream == null) begin
        `uvm_error("UVM/REC/NULL_STREAM",
                   $sformatf("Illegal attempt to set STREAM for '%s' to '<null>'",
                             this.get_name()))
        return;
     end

     if (m_stream_dap.try_get(m_stream)) begin
        `uvm_error("UVM/REC/RE_INIT",
                   $sformatf("Illegal attempt to re-initialize '%s'",
                             this.get_name()))
        return;
     end

     m_stream_dap.set(stream);
     m_open_time = open_time;
     m_is_opened = 1;
     
     do_open(stream, open_time, type_name);
  endfunction : m_do_open

   // Group -- NODOCS -- Handles


   // Variable- m_recorders_by_id
   // A corollary to ~m_ids_by_recorder~, this indexes the recorders by their
   // unique ids.
   local static uvm_recorder m_recorders_by_id[int];

   // Variable- m_id
   // Static int marking the last assigned id.
   local static int m_id;

   // Function- m_free_id
   // Frees the id/recorder link (memory cleanup)
   //
   static function void m_free_id(int id);
      uvm_recorder recorder;
      if ((!$isunknown(id)) && (m_recorders_by_id.exists(id)))
        recorder = m_recorders_by_id[id];

      if (recorder != null) begin
         m_recorders_by_id.delete(id);
         m_ids_by_recorder.delete(recorder);
      end
   endfunction : m_free_id
            

   // @uvm-ieee 1800.2-2017 auto 16.4.5.1
   function int get_handle();
      if (!is_open() && !is_closed()) begin
         return 0;
      end
      else begin
         int handle = get_inst_id();

         // Check for the weird case where our handle changed.
         if (m_ids_by_recorder.exists(this) && m_ids_by_recorder[this] != handle)
           m_recorders_by_id.delete(m_ids_by_recorder[this]);
           
         m_recorders_by_id[handle] = this;
         m_ids_by_recorder[this] = handle;

         return handle;
      end
   endfunction : get_handle


   // @uvm-ieee 1800.2-2017 auto 16.4.5.2
   static function uvm_recorder get_recorder_from_handle(int id);
      if (id == 0)
        return null;

      if (($isunknown(id)) || (!m_recorders_by_id.exists(id)))
        return null;

      return m_recorders_by_id[id];
   endfunction : get_recorder_from_handle

   // Group -- NODOCS -- Attribute Recording
   

   // @uvm-ieee 1800.2-2017 auto 16.4.6.1
   function void record_field(string name,
                              uvm_bitstream_t value,
                              int size,
                              uvm_radix_enum radix=UVM_NORADIX);
      if (get_stream() == null) begin
         return;
      end
      do_record_field(name, value, size, radix);
   endfunction : record_field


   // @uvm-ieee 1800.2-2017 auto 16.4.6.2
   function void record_field_int(string name,
                                  uvm_integral_t value,
                                  int size,
                                  uvm_radix_enum radix=UVM_NORADIX);
        if (get_stream() == null) begin
         return;
      end
      do_record_field_int(name, value, size, radix);
   endfunction : record_field_int


   // @uvm-ieee 1800.2-2017 auto 16.4.6.3
   function void record_field_real(string name,
                                   real value);
      if (get_stream() == null) begin
         return;
      end
      do_record_field_real(name, value);
   endfunction : record_field_real

   // @uvm-ieee 1800.2-2017 auto 16.4.6.4
   function void record_object(string name,
                               uvm_object value);
      if (get_stream() == null) begin
         return;
      end

      push_active_object(value);
      do_record_object(name, value);
      void'(pop_active_object());
   endfunction : record_object


   // @uvm-ieee 1800.2-2017 auto 16.4.6.5
   function void record_string(string name,
                               string value);
      if (get_stream() == null) begin
         return;
      end

      do_record_string(name, value);
   endfunction : record_string
   

   // @uvm-ieee 1800.2-2017 auto 16.4.6.6
   function void record_time(string name,
                             time value);
      if (get_stream() == null) begin
         return;
      end

      do_record_time(name, value);
   endfunction : record_time
   

   // @uvm-ieee 1800.2-2017 auto 16.4.6.7
   function void record_generic(string name,
                                string value,
                                string type_name="");
      if (get_stream() == null) begin
         return;
      end

      do_record_generic(name, value, type_name);
   endfunction : record_generic


  // @uvm-ieee 1800.2-2017 auto 16.4.6.8
  virtual function bit use_record_attribute();
     return 0;
  endfunction : use_record_attribute


   // @uvm-ieee 1800.2-2017 auto 16.4.6.9
   virtual function int get_record_attribute_handle();
      return get_handle();
   endfunction : get_record_attribute_handle
   
   // Group -- NODOCS -- Implementation Agnostic API


   // @uvm-ieee 1800.2-2017 auto 16.4.7.1
   protected virtual function void do_open(uvm_tr_stream stream,
                                             time open_time,
                                             string type_name);
   endfunction : do_open


   // @uvm-ieee 1800.2-2017 auto 16.4.7.2
   protected virtual function void do_close(time close_time);
   endfunction : do_close


   // @uvm-ieee 1800.2-2017 auto 16.4.7.3
   protected virtual function void do_free();
   endfunction : do_free
   

   // @uvm-ieee 1800.2-2017 auto 16.4.7.4
   pure virtual protected function void do_record_field(string name,
                                                        uvm_bitstream_t value,
                                                        int size,
                                                        uvm_radix_enum radix);


   // @uvm-ieee 1800.2-2017 auto 16.4.7.5
   pure virtual protected function void do_record_field_int(string name,
                                                            uvm_integral_t value,
                                                            int          size,
                                                            uvm_radix_enum radix);
   

   // @uvm-ieee 1800.2-2017 auto 16.4.7.6
   pure virtual protected function void do_record_field_real(string name,
                                                             real value);


   // Function : do_record_object
   // The library implements do_record_object as virtual even though the LRM
   // calls for pure virtual. Mantis 6591 calls for the LRM to move to
   // virtual.  The implemented signature is:
   // virtual protected function void do_record_object(string name, uvm_object value);
  
   // @uvm-ieee 1800.2-2017 auto 16.4.7.7
   virtual protected function void do_record_object(string name,
                                                    uvm_object value);
     if ((get_recursion_policy() != UVM_REFERENCE) &&
         (value != null)) begin
       uvm_field_op field_op = uvm_field_op::m_get_available_op();
       field_op.set(UVM_RECORD, this, null);
       value.do_execute_op(field_op);
       if (field_op.user_hook_enabled())
         value.do_record(this);
       field_op.m_recycle();
     end 
   endfunction : do_record_object


   // @uvm-ieee 1800.2-2017 auto 16.4.7.9
   pure virtual protected function void do_record_string(string name,
                                                         string value);


   // @uvm-ieee 1800.2-2017 auto 16.4.7.10
   pure virtual protected function void do_record_time(string name,
                                                       time value);


   // @uvm-ieee 1800.2-2017 auto 16.4.7.11
   pure virtual protected function void do_record_generic(string name,
                                                          string value,
                                                          string type_name);


   // The following code is primarily for backwards compat. purposes.  "Transaction
   // Handles" are useful when connecting to a backend, but when passing the information
   // back and forth within simulation, it is safer to user the ~recorder~ itself
   // as a reference to the transaction within the database.

   //------------------------------
   // Group- Vendor-Independent API
   //------------------------------


  // UVM provides only a text-based default implementation.
  // Vendors provide subtype implementations and overwrite the
  // <uvm_default_recorder> handle.


  // Function- open_file
  //
  // Opens the file in the <filename> property and assigns to the
  // file descriptor <file>.
  //
  virtual function bit open_file();
     return 0;
  endfunction

  // Function- create_stream
  //
  //
  virtual function int create_stream (string name,
                                          string t,
                                          string scope);
     return -1;
  endfunction

   
  // Function- m_set_attribute
  //
  //
  virtual function void m_set_attribute (int txh,
                                 string nm,
                                 string value);
  endfunction
  
  
  // Function- set_attribute
  //
  virtual function void set_attribute (int txh,
                               string nm,
                               logic [1023:0] value,
                               uvm_radix_enum radix,
                               int numbits=1024);
  endfunction
  
  
  // Function- check_handle_kind
  //
  //
  virtual function int check_handle_kind (string htype, int handle);
     return 0;
  endfunction
  
  
  // Function- begin_tr
  //
  //
  virtual function int begin_tr(string txtype,
                                     int stream,
                                     string nm,
                                     string label="",
                                     string desc="",
                                     time begin_time=0);
    return -1;
  endfunction
  
  
  // Function- end_tr
  //
  //
  virtual function void end_tr (int handle, time end_time=0);
  endfunction
  
  
  // Function- link_tr
  //
  //
  virtual function void link_tr(int h1,
                                 int h2,
                                 string relation="");
  endfunction
  
  
  
  // Function- free_tr
  //
  //
  virtual function void free_tr(int handle);
  endfunction
  
endclass // uvm_recorder

//------------------------------------------------------------------------------
//
// CLASS: uvm_text_recorder
//
// The ~uvm_text_recorder~ is the default recorder implementation for the
// <uvm_text_tr_database>.
//

class uvm_text_recorder extends uvm_recorder;

   `uvm_object_utils(uvm_text_recorder)

   // Variable- m_text_db
   //
   // Reference to the text database backend
   uvm_text_tr_database m_text_db;

   // Function --NODOCS-- new
   // Constructor
   //
   // Parameters --NODOCS--
   // name - Instance name
   function new(string name="unnamed-uvm_text_recorder");
      super.new(name);
   endfunction : new

   // Group --NODOCS-- Implementation Agnostic API

   // Function --NODOCS-- do_open
   // Callback triggered via <uvm_tr_stream::open_recorder>.
   //
   // Text-backend specific implementation.
   protected virtual function void do_open(uvm_tr_stream stream,
                                             time open_time,
                                             string type_name);
      $cast(m_text_db, stream.get_db());
      if (m_text_db.open_db())
        $fdisplay(m_text_db.m_file, 
                  "    OPEN_RECORDER @%0t {TXH:%0d STREAM:%0d NAME:%s TIME:%0t TYPE=\"%0s\"}",
                  $realtime,
                  this.get_handle(),
                  stream.get_handle(),
                  this.get_name(),
                  open_time,
                  type_name);
   endfunction : do_open

   // Function --NODOCS-- do_close
   // Callback triggered via <uvm_recorder::close>.
   //
   // Text-backend specific implementation.
   protected virtual function void do_close(time close_time);
      if (m_text_db.open_db()) begin
         $fdisplay(m_text_db.m_file, 
                   "    CLOSE_RECORDER @%0t {TXH:%0d TIME=%0t}",
                   $realtime,
                   this.get_handle(),
                   close_time);
         
      end
   endfunction : do_close

   // Function --NODOCS-- do_free
   // Callback triggered via <uvm_recorder::free>.
   //
   // Text-backend specific implementation.
   protected virtual function void do_free();
      if (m_text_db.open_db()) begin
         $fdisplay(m_text_db.m_file, 
                   "    FREE_RECORDER @%0t {TXH:%0d}",
                   $realtime,
                   this.get_handle());
      end
      m_text_db = null;
   endfunction : do_free
   
   // Function --NODOCS-- do_record_field
   // Records an integral field (less than or equal to 4096 bits).
   //
   // Text-backend specific implementation.
   protected virtual function void do_record_field(string name,
                                                   uvm_bitstream_t value,
                                                   int size,
                                                   uvm_radix_enum radix);
      if (!radix)
        radix = default_radix;

      write_attribute(m_current_context(name),
                      value,
                      radix,
                      size);

   endfunction : do_record_field
  
   
   // Function --NODOCS-- do_record_field_int
   // Records an integral field (less than or equal to 64 bits).
   //
   // Text-backend specific implementation.
   protected virtual function void do_record_field_int(string name,
                                                       uvm_integral_t value,
                                                       int          size,
                                                       uvm_radix_enum radix);
      if (!radix)
        radix = default_radix;

      write_attribute_int(m_current_context(name),
                          value,
                          radix,
                          size);

   endfunction : do_record_field_int


   // Function --NODOCS-- do_record_field_real
   // Record a real field.
   //
   // Text-backened specific implementation.
   protected virtual function void do_record_field_real(string name,
                                                        real value);
      bit [63:0] ival = $realtobits(value);

      write_attribute_int(m_current_context(name),
                          ival,
                          UVM_REAL,
                          64);
   endfunction : do_record_field_real

  // Stores the passed-in names of the objects in the hierarchy
  local string m_object_names[$];
  local function string m_current_context(string name="");
    if (m_object_names.size()  == 0)
      return name; //??
    else if ((m_object_names.size() == 1) && (name==""))
      return m_object_names[0];
    else begin
      string     full_name;
      foreach(m_object_names[i]) begin
        if (i == m_object_names.size() - 1)
          full_name = {full_name, m_object_names[i]};
        else
          full_name  = {full_name, m_object_names[i], "."};
      end
      if (name != "")
        return {full_name, ".", name};
      else
        return full_name;
    end
  endfunction : m_current_context

  
   // Function --NODOCS-- do_record_object
   // Record an object field.
   //
   // Text-backend specific implementation.
   //
   // The method uses ~identifier~ to determine whether or not to
   // record the object instance id, and ~recursion_policy~ to
   // determine whether or not to recurse into the object.
   protected virtual function void do_record_object(string name,
                                                    uvm_object value);
      int            v;
      string         str;
      
      if(identifier) begin 
         if(value != null) begin
           v = value.get_inst_id(); 
         end
         write_attribute_int("inst_id", 
                             v, 
                             UVM_DEC, 
                             32);
      end

      if (get_active_object_depth() > 1)
        m_object_names.push_back(name);
      super.do_record_object(name, value);
      if (get_active_object_depth() > 1)
        void'(m_object_names.pop_back());
   endfunction : do_record_object

   // Function --NODOCS-- do_record_string
   // Records a string field.
   //
   // Text-backend specific implementation.
   protected virtual function void do_record_string(string name,
                                                    string value);
      if (m_text_db.open_db()) begin
         $fdisplay(m_text_db.m_file, 
                   "      SET_ATTR @%0t {TXH:%0d NAME:%s VALUE:%s   RADIX:%s BITS=%0d}",
                   $realtime,
                   this.get_handle(),
                   m_current_context(name),
                   value,
                   "UVM_STRING",
                   8+value.len());
      end
   endfunction : do_record_string

   // Function --NODOCS-- do_record_time
   // Records a time field.
   //
   // Text-backend specific implementation.
   protected virtual function void do_record_time(string name,
                                                    time value);
      write_attribute_int(m_current_context(name), 
                          value,
                          UVM_TIME, 
                          64);
   endfunction : do_record_time

   // Function --NODOCS-- do_record_generic
   // Records a name/value pair, where ~value~ has been converted to a string.
   //
   // Text-backend specific implementation.
   protected virtual function void do_record_generic(string name,
                                                     string value,
                                                     string type_name);
      write_attribute(m_current_context(name), 
                      uvm_string_to_bits(value), 
                      UVM_STRING, 
                      8+value.len());
   endfunction : do_record_generic

   // Group: Implementation Specific API
   
   // Function: write_attribute
   // Outputs an integral attribute to the textual log
   //
   // Parameters:
   // nm - Name of the attribute
   // value - Value
   // radix - Radix of the output
   // numbits - number of valid bits
   function void write_attribute(string nm,
                                 uvm_bitstream_t value,
                                 uvm_radix_enum radix,
                                 int numbits=$bits(uvm_bitstream_t));
      if (m_text_db.open_db()) begin
         $fdisplay(m_text_db.m_file, 
                   "      SET_ATTR @%0t {TXH:%0d NAME:%s VALUE:%s   RADIX:%s BITS=%0d}",
                   $realtime,
                   this.get_handle(),
                   nm,
                   uvm_bitstream_to_string(value, numbits, radix),
                    radix.name(),
                   numbits);
      end
   endfunction : write_attribute

   // Function: write_attribute_int
   // Outputs an integral attribute to the textual log
   //
   // Parameters:
   // nm - Name of the attribute
   // value - Value
   // radix - Radix of the output
   // numbits - number of valid bits
   function void write_attribute_int(string  nm,
                                     uvm_integral_t value,
                                     uvm_radix_enum radix,
                                     int numbits=$bits(uvm_bitstream_t));
      if (m_text_db.open_db()) begin
         $fdisplay(m_text_db.m_file, 
                   "      SET_ATTR @%0t {TXH:%0d NAME:%s VALUE:%s   RADIX:%s BITS=%0d}",
                   $realtime,
                   this.get_handle(),
                   nm,
                   uvm_integral_to_string(value, numbits, radix),
                   radix.name(),
                   numbits);
      end
   endfunction : write_attribute_int

   /// LEFT FOR BACKWARDS COMPAT ONLY!!!!!!!!

   //------------------------------
   // Group- Vendor-Independent API
   //------------------------------


  // UVM provides only a text-based default implementation.
  // Vendors provide subtype implementations and overwrite the
  // <uvm_default_recorder> handle.

   string                                                   filename;
   bit                                                      filename_set;

  // Function- open_file
  //
  // Opens the file in the <filename> property and assigns to the
  // file descriptor <file>.
  //
  virtual function bit open_file();
     if (!filename_set) begin
        m_text_db.set_file_name(filename);
     end
     return m_text_db.open_db();
  endfunction


  // Function- create_stream
  //
  //
  virtual function int create_stream (string name,
                                          string t,
                                          string scope);
     uvm_text_tr_stream stream;
     if (open_file()) begin
        $cast(stream,m_text_db.open_stream(name, scope, t));
        return stream.get_handle();
     end
     return 0;
  endfunction

   
  // Function- m_set_attribute
  //
  //
  virtual function void m_set_attribute (int txh,
                                 string nm,
                                 string value);
     if (open_file()) begin
        UVM_FILE file = m_text_db.m_file;
        $fdisplay(file,"      SET_ATTR @%0t {TXH:%0d NAME:%s VALUE:%s}", $realtime,txh,nm,value);
     end
  endfunction
  
  
  // Function- set_attribute
  //
  //
  virtual function void set_attribute (int txh,
                               string nm,
                               logic [1023:0] value,
                               uvm_radix_enum radix,
                               int numbits=1024);
     if (open_file()) begin
        UVM_FILE file = m_text_db.m_file;
         $fdisplay(file, 
                   "      SET_ATTR @%0t {TXH:%0d NAME:%s VALUE:%s   RADIX:%s BITS=%0d}",
                   $realtime,
                   txh,
                   nm,
                   uvm_bitstream_to_string(value, numbits, radix),
                   radix.name(),
                   numbits);
        
     end
  endfunction
  
  
  // Function- check_handle_kind
  //
  //
  virtual function int check_handle_kind (string htype, int handle);
     return ((uvm_recorder::get_recorder_from_handle(handle) != null) ||
             (uvm_tr_stream::get_stream_from_handle(handle) != null));
  endfunction
  
  
  // Function- begin_tr
  //
  //
  virtual function int begin_tr(string txtype,
                                     int stream,
                                     string nm,
                                     string label="",
                                     string desc="",
                                     time begin_time=0);
     if (open_file()) begin
        uvm_tr_stream stream_obj = uvm_tr_stream::get_stream_from_handle(stream);
        uvm_recorder recorder;
  
        if (stream_obj == null)
          return -1;

        recorder = stream_obj.open_recorder(nm, begin_time, txtype);

        return recorder.get_handle();
     end
     return -1;
  endfunction
  
  
  // Function- end_tr
  //
  //
  virtual function void end_tr (int handle, time end_time=0);
     if (open_file()) begin
        uvm_recorder record = uvm_recorder::get_recorder_from_handle(handle);
        if (record != null) begin
           record.close(end_time);
        end
     end
  endfunction
  
  
  // Function- link_tr
  //
  //
  virtual function void link_tr(int h1,
                                 int h2,
                                 string relation="");
    if (open_file())
      $fdisplay(m_text_db.m_file,"  LINK @%0t {TXH1:%0d TXH2:%0d RELATION=%0s}", $realtime,h1,h2,relation);
  endfunction
  
  
  
  // Function- free_tr
  //
  //
  virtual function void free_tr(int handle);
     if (open_file()) begin
        uvm_recorder record = uvm_recorder::get_recorder_from_handle(handle);
        if (record != null) begin
           record.free();
        end
     end
  endfunction // free_tr

endclass : uvm_text_recorder

  
   
