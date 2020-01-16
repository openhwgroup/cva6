//
//------------------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2010-2014 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2010-2012 AMD
// Copyright 2013-2017 NVIDIA Corporation
// Copyright 2017 Cisco Systems, Inc.
// Copyright 2011 Cypress Semiconductor Corp.
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
//------------------------------------------------------------------------------

`ifndef UVM_REPORT_HANDLER_SVH
`define UVM_REPORT_HANDLER_SVH

typedef class uvm_report_object;
typedef class uvm_report_server;
typedef uvm_pool#(string, uvm_action) uvm_id_actions_array;
typedef uvm_pool#(string, UVM_FILE) uvm_id_file_array;
typedef uvm_pool#(string, int) uvm_id_verbosities_array;
typedef uvm_pool#(uvm_severity, uvm_severity) uvm_sev_override_array;

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_report_handler
//
// The uvm_report_handler is the class to which most methods in
// <uvm_report_object> delegate. It stores the maximum verbosity, actions,
// and files that affect the way reports are handled. 
//
// The report handler is not intended for direct use. See <uvm_report_object>
// for information on the UVM reporting mechanism.
//
// The relationship between <uvm_report_object> (a base class for uvm_component)
// and uvm_report_handler is typically one to one, but it can be many to one
// if several uvm_report_objects are configured to use the same
// uvm_report_handler_object. See <uvm_report_object::set_report_handler>.
//
// The relationship between uvm_report_handler and <uvm_report_server> is many
// to one. 
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 6.4.1
class uvm_report_handler extends uvm_object;

  // internal variables

  int m_max_verbosity_level;

  // id verbosity settings : default and severity
  uvm_id_verbosities_array id_verbosities;
  uvm_id_verbosities_array severity_id_verbosities[uvm_severity];

  // actions
  uvm_id_actions_array id_actions;
  uvm_action severity_actions[uvm_severity];
  uvm_id_actions_array severity_id_actions[uvm_severity];

  // severity overrides
  uvm_sev_override_array sev_overrides;
  uvm_sev_override_array sev_id_overrides [string];

  // file handles : default, severity, action, (severity,id)
  UVM_FILE default_file_handle;
  uvm_id_file_array id_file_handles;
  UVM_FILE severity_file_handles[uvm_severity];
  uvm_id_file_array severity_id_file_handles[uvm_severity];


  `uvm_object_utils(uvm_report_handler)


  // Function -- NODOCS -- new
  // 
  // Creates and initializes a new uvm_report_handler object.

  // @uvm-ieee 1800.2-2017 auto 6.4.2.1
  function new(string name = "uvm_report_handler");
    super.new(name);
    initialize();
  endfunction


  // Function -- NODOCS -- print
  //
  // The uvm_report_handler implements the <uvm_object::do_print()> such that
  // ~print~ method provides UVM printer formatted output
  // of the current configuration.  A snippet of example output is shown here:
  //
  // |uvm_test_top                uvm_report_handler  -     @555                    
  // |  max_verbosity_level       uvm_verbosity       32    UVM_FULL                
  // |  id_verbosities            uvm_pool            3     -                       
  // |    [ID1]                   uvm_verbosity       32    UVM_LOW                 
  // |  severity_id_verbosities   array               4     -                       
  // |    [UVM_INFO:ID4]          int                 32    501                     
  // |  id_actions                uvm_pool            2     -                       
  // |    [ACT_ID]                uvm_action          32    DISPLAY LOG COUNT       
  // |  severity_actions          array               4     -                       
  // |    [UVM_INFO]              uvm_action          32    DISPLAY                 
  // |    [UVM_WARNING]           uvm_action          32    DISPLAY RM_RECORD COUNT 
  // |    [UVM_ERROR]             uvm_action          32    DISPLAY COUNT           
  // |    [UVM_FATAL]             uvm_action          32    DISPLAY EXIT            
  // |  default_file_handle       int                 32    'h1                     

  // @uvm-ieee 1800.2-2017 auto 6.4.2.2
  virtual function void do_print (uvm_printer printer);

    uvm_verbosity l_verbosity;
    uvm_severity l_severity;
    string idx;
    int l_int;

    // max verb
    if ($cast(l_verbosity, m_max_verbosity_level))
      printer.print_generic("max_verbosity_level", "uvm_verbosity", 32, 
        l_verbosity.name());
    else
      printer.print_field("max_verbosity_level", m_max_verbosity_level, 32, UVM_DEC,
        ".", "int");

    // id verbs
    if(id_verbosities.first(idx)) begin
      printer.print_array_header("id_verbosities",id_verbosities.num(),
        "uvm_pool");
      do begin
        l_int = id_verbosities.get(idx);
        if ($cast(l_verbosity, l_int))
          printer.print_generic($sformatf("[%s]", idx), "uvm_verbosity", 32, 
            l_verbosity.name());
        else begin
          string l_str;
          l_str.itoa(l_int);
          printer.print_generic($sformatf("[%s]", idx), "int", 32, 
            l_str);
        end
      end while(id_verbosities.next(idx));
      printer.print_array_footer();
    end

    // sev and id verbs
    if(severity_id_verbosities.size() != 0) begin
      int _total_cnt;
      foreach (severity_id_verbosities[l_severity])
        _total_cnt += severity_id_verbosities[l_severity].num();
      printer.print_array_header("severity_id_verbosities", _total_cnt,
        "array");
      if(severity_id_verbosities.first(l_severity)) begin
        do begin
          uvm_id_verbosities_array id_v_ary = severity_id_verbosities[l_severity];
          if(id_v_ary.first(idx))
          do begin
            l_int = id_v_ary.get(idx);
            if ($cast(l_verbosity, l_int))
              printer.print_generic($sformatf("[%s:%s]", l_severity.name(), idx), 
				    "uvm_verbosity", 32, l_verbosity.name());
            else begin
              string l_str;
              l_str.itoa(l_int);
              printer.print_generic($sformatf("[%s:%s]", l_severity.name(), idx), 
				    "int", 32, l_str);
            end
          end while(id_v_ary.next(idx));
        end while(severity_id_verbosities.next(l_severity));
      end
      printer.print_array_footer();
    end

    // id actions
    if(id_actions.first(idx)) begin
      printer.print_array_header("id_actions",id_actions.num(),
        "uvm_pool");
      do begin
        l_int = id_actions.get(idx);
        printer.print_generic($sformatf("[%s]", idx), "uvm_action", 32, 
          format_action(l_int));
      end while(id_actions.next(idx));
      printer.print_array_footer();
    end

    // severity actions
    if(severity_actions.first(l_severity)) begin
      printer.print_array_header("severity_actions",4,"array");
      do begin
        printer.print_generic($sformatf("[%s]", l_severity.name()), "uvm_action", 32, 
          format_action(severity_actions[l_severity]));
      end while(severity_actions.next(l_severity));
      printer.print_array_footer();
    end

    // sev and id actions 
    if(severity_id_actions.size() != 0) begin
      int _total_cnt;
      foreach (severity_id_actions[l_severity])
        _total_cnt += severity_id_actions[l_severity].num();
      printer.print_array_header("severity_id_actions", _total_cnt,
        "array");
      if(severity_id_actions.first(l_severity)) begin
        do begin
          uvm_id_actions_array id_a_ary = severity_id_actions[l_severity];
          if(id_a_ary.first(idx))
          do begin
            printer.print_generic($sformatf("[%s:%s]", l_severity.name(), idx), 
				  "uvm_action", 32, format_action(id_a_ary.get(idx)));
          end while(id_a_ary.next(idx));
        end while(severity_id_actions.next(l_severity));
      end
      printer.print_array_footer();
    end

    // sev overrides
    if(sev_overrides.first(l_severity)) begin
      printer.print_array_header("sev_overrides",sev_overrides.num(),
        "uvm_pool");
      do begin
        uvm_severity l_severity_new = sev_overrides.get(l_severity);
        printer.print_generic($sformatf("[%s]", l_severity.name()),
          "uvm_severity", 32, l_severity_new.name());
      end while(sev_overrides.next(l_severity));
      printer.print_array_footer();
    end

    // sev and id overrides
    if(sev_id_overrides.size() != 0) begin
      int _total_cnt;
      foreach (sev_id_overrides[idx])
        _total_cnt += sev_id_overrides[idx].num();
      printer.print_array_header("sev_id_overrides", _total_cnt,
        "array");
      if(sev_id_overrides.first(idx)) begin
        do begin
          uvm_sev_override_array sev_o_ary = sev_id_overrides[idx];
          if(sev_o_ary.first(l_severity))
          do begin
            uvm_severity new_sev = sev_o_ary.get(l_severity);
            printer.print_generic($sformatf("[%s:%s]", l_severity.name(), idx), 
              "uvm_severity", 32, new_sev.name());
          end while(sev_o_ary.next(l_severity));
        end while(sev_id_overrides.next(idx));
      end
      printer.print_array_footer();
    end

    // default file handle
    printer.print_field("default_file_handle", default_file_handle, 32, UVM_HEX,
      ".", "int");

    // id files 
    if(id_file_handles.first(idx)) begin
      printer.print_array_header("id_file_handles",id_file_handles.num(),
        "uvm_pool");
      do begin
        printer.print_field($sformatf("[%s]", idx), id_file_handles.get(idx), 32,
          UVM_HEX, ".", "UVM_FILE");
      end while(id_file_handles.next(idx));
      printer.print_array_footer();
    end

    // severity files
    if(severity_file_handles.first(l_severity)) begin
      printer.print_array_header("severity_file_handles",4,"array");
      do begin
        printer.print_field($sformatf("[%s]", l_severity.name()), 
          severity_file_handles[l_severity], 32, UVM_HEX, ".", "UVM_FILE");
      end while(severity_file_handles.next(l_severity));
      printer.print_array_footer();
    end

    // sev and id files
    if(severity_id_file_handles.size() != 0) begin
      int _total_cnt;
      foreach (severity_id_file_handles[l_severity])
        _total_cnt += severity_id_file_handles[l_severity].num();
      printer.print_array_header("severity_id_file_handles", _total_cnt,
        "array");
      if(severity_id_file_handles.first(l_severity)) begin
        do begin
          uvm_id_file_array id_f_ary = severity_id_file_handles[l_severity];
          if(id_f_ary.first(idx))
          do begin
            printer.print_field($sformatf("[%s:%s]", l_severity.name(), idx),
              id_f_ary.get(idx), 32, UVM_HEX, ".", "UVM_FILE");
          end while(id_f_ary.next(idx));
        end while(severity_id_file_handles.next(l_severity));
      end
      printer.print_array_footer();
    end

  endfunction

  
  //----------------------------------------------------------------------------
  // Group -- NODOCS -- Message Processing
  //----------------------------------------------------------------------------


  // Function -- NODOCS -- process_report_message
  //
  // This is the common handler method used by the four core reporting methods
  // (e.g. <uvm_report_error>) in <uvm_report_object>.

  // @uvm-ieee 1800.2-2017 auto 6.4.7
  virtual function void process_report_message(uvm_report_message report_message);
    process p = process::self();
    uvm_report_server srvr = uvm_report_server::get_server();
    string id = report_message.get_id();
    uvm_severity severity = report_message.get_severity();

    // Check for severity overrides and apply them before calling the server.
    // An id specific override has precedence over a generic severity override.
    if(sev_id_overrides.exists(id)) begin
      if(sev_id_overrides[id].exists(uvm_severity'(severity))) begin
        severity = sev_id_overrides[id].get(severity);
        report_message.set_severity(severity);
      end
    end
    else begin
      if(sev_overrides.exists(severity)) begin
        severity = sev_overrides.get(severity);
        report_message.set_severity(severity);
      end
    end
    report_message.set_file(get_file_handle(severity, id));
    report_message.set_report_handler(this);
    report_message.set_action(get_action(severity, id));
    srvr.process_report_message(report_message);
    
  endfunction


  //----------------------------------------------------------------------------
  // Group -- NODOCS -- Convenience Methods
  //----------------------------------------------------------------------------


  // Function -- NODOCS -- format_action
  //
  // Returns a string representation of the ~action~, e.g., "DISPLAY".

  static function string format_action(uvm_action action);
    string s;

    if(uvm_action_type'(action) == UVM_NO_ACTION) begin
      s = "NO ACTION";
    end
    else begin
      s = "";
      if(action & UVM_DISPLAY)   s = {s, "DISPLAY "};
      if(action & UVM_LOG)       s = {s, "LOG "};
      if(action & UVM_RM_RECORD) s = {s, "RM_RECORD "};
      if(action & UVM_COUNT)     s = {s, "COUNT "};
      if(action & UVM_CALL_HOOK) s = {s, "CALL_HOOK "};
      if(action & UVM_EXIT)      s = {s, "EXIT "};
      if(action & UVM_STOP)      s = {s, "STOP "};
    end

    return s;
  endfunction


  // Function- initialize
  //
  // Internal method for initializing report handler.

  function void initialize();

    set_default_file(0);
    m_max_verbosity_level = UVM_MEDIUM;

    id_actions=new();
    id_verbosities=new();
    id_file_handles=new();
    sev_overrides=new();

    set_severity_action(UVM_INFO,    UVM_DISPLAY);
    set_severity_action(UVM_WARNING, UVM_DISPLAY);
    set_severity_action(UVM_ERROR,   UVM_DISPLAY | UVM_COUNT);
    set_severity_action(UVM_FATAL,   UVM_DISPLAY | UVM_EXIT);

    set_severity_file(UVM_INFO, default_file_handle);
    set_severity_file(UVM_WARNING, default_file_handle);
    set_severity_file(UVM_ERROR,   default_file_handle);
    set_severity_file(UVM_FATAL,   default_file_handle);

  endfunction

  
  // Function- get_severity_id_file
  //
  // Return the file id based on the severity and the id

  local function UVM_FILE get_severity_id_file(uvm_severity severity, string id);

    uvm_id_file_array array;

    if(severity_id_file_handles.exists(severity)) begin
      array = severity_id_file_handles[severity];      
      if(array.exists(id))
        return array.get(id);
    end


    if(id_file_handles.exists(id))
      return id_file_handles.get(id);

    if(severity_file_handles.exists(severity))
      return severity_file_handles[severity];

    return default_file_handle;

  endfunction


  // Function- set_verbosity_level
  //
  // Internal method called by uvm_report_object.

  // @uvm-ieee 1800.2-2017 auto 6.4.3.2
  function void set_verbosity_level(int verbosity_level);
    m_max_verbosity_level = verbosity_level;
  endfunction


  // Function- get_verbosity_level
  //
  // Returns the verbosity associated with the given ~severity~ and ~id~.
  // 
  // First, if there is a verbosity associated with the ~(severity,id)~ pair,
  // return that.  Else, if there is a verbosity associated with the ~id~, return
  // that.  Else, return the max verbosity setting.

  // @uvm-ieee 1800.2-2017 auto 6.4.3.1
  function int get_verbosity_level(uvm_severity severity=UVM_INFO, string id="" );

    uvm_id_verbosities_array array;
    if(severity_id_verbosities.exists(severity)) begin
      array = severity_id_verbosities[severity];
      if(array.exists(id)) begin
        return array.get(id);
      end
    end

    if(id_verbosities.exists(id)) begin
      return id_verbosities.get(id);
    end

    return m_max_verbosity_level;

  endfunction


  // Function- get_action
  //
  // Returns the action associated with the given ~severity~ and ~id~.
  // 
  // First, if there is an action associated with the ~(severity,id)~ pair,
  // return that.  Else, if there is an action associated with the ~id~, return
  // that.  Else, if there is an action associated with the ~severity~, return
  // that. Else, return the default action associated with the ~severity~.

  // @uvm-ieee 1800.2-2017 auto 6.4.4.1
  function uvm_action get_action(uvm_severity severity, string id);

    uvm_id_actions_array array;
    if(severity_id_actions.exists(severity)) begin
      array = severity_id_actions[severity];
      if(array.exists(id))
        return array.get(id);
    end

    if(id_actions.exists(id))
      return id_actions.get(id);

    return severity_actions[severity];

  endfunction


  // Function- get_file_handle
  //
  // Returns the file descriptor associated with the given ~severity~ and ~id~.
  //
  // First, if there is a file handle associated with the ~(severity,id)~ pair,
  // return that. Else, if there is a file handle associated with the ~id~, return
  // that. Else, if there is an file handle associated with the ~severity~, return
  // that. Else, return the default file handle.

  // @uvm-ieee 1800.2-2017 auto 6.4.5.1
  function UVM_FILE get_file_handle(uvm_severity severity, string id);
    UVM_FILE file;
  
    file = get_severity_id_file(severity, id);
    if (file != 0)
      return file;
  
    if (id_file_handles.exists(id)) begin
      file = id_file_handles.get(id);
      if (file != 0)
        return file;
    end

    if (severity_file_handles.exists(severity)) begin
      file = severity_file_handles[severity];
      if(file != 0)
        return file;
    end

    return default_file_handle;
  endfunction


  // Function- set_severity_action
  // Function- set_id_action
  // Function- set_severity_id_action
  // Function- set_id_verbosity
  // Function- set_severity_id_verbosity
  //
  // Internal methods called by uvm_report_object.

  // @uvm-ieee 1800.2-2017 auto 6.4.4.2
  function void set_severity_action(input uvm_severity severity,
                                    input uvm_action action);
    severity_actions[severity] = action;
  endfunction

  // @uvm-ieee 1800.2-2017 auto 6.4.4.2
  function void set_id_action(input string id, input uvm_action action);
    id_actions.add(id, action);
  endfunction

  // @uvm-ieee 1800.2-2017 auto 6.4.4.2
  function void set_severity_id_action(uvm_severity severity,
                                       string id,
                                       uvm_action action);
    if(!severity_id_actions.exists(severity))
      severity_id_actions[severity] = new;
    severity_id_actions[severity].add(id,action);
  endfunction
  
  // @uvm-ieee 1800.2-2017 auto 6.4.3.3
  function void set_id_verbosity(input string id, input int verbosity);
    id_verbosities.add(id, verbosity);
  endfunction

  // @uvm-ieee 1800.2-2017 auto 6.4.3.3
  function void set_severity_id_verbosity(uvm_severity severity,
                                       string id,
                                       int verbosity);
    if(!severity_id_verbosities.exists(severity))
      severity_id_verbosities[severity] = new;
    severity_id_verbosities[severity].add(id,verbosity);
  endfunction

  // Function- set_default_file
  // Function- set_severity_file
  // Function- set_id_file
  // Function- set_severity_id_file
  //
  // Internal methods called by uvm_report_object.

  // @uvm-ieee 1800.2-2017 auto 6.4.5.2
  function void set_default_file (UVM_FILE file);
    default_file_handle = file;
  endfunction

  // @uvm-ieee 1800.2-2017 auto 6.4.5.2
  function void set_severity_file (uvm_severity severity, UVM_FILE file);
    severity_file_handles[severity] = file;
  endfunction

  // @uvm-ieee 1800.2-2017 auto 6.4.5.2
  function void set_id_file (string id, UVM_FILE file);
    id_file_handles.add(id, file);
  endfunction

  // @uvm-ieee 1800.2-2017 auto 6.4.5.2
  function void set_severity_id_file(uvm_severity severity,
                                     string id, UVM_FILE file);
    if(!severity_id_file_handles.exists(severity))
      severity_id_file_handles[severity] = new;
    severity_id_file_handles[severity].add(id, file);
  endfunction

  // @uvm-ieee 1800.2-2017 auto 6.4.6
  function void set_severity_override(uvm_severity cur_severity,
                                      uvm_severity new_severity);
    sev_overrides.add(cur_severity, new_severity);
  endfunction

  // @uvm-ieee 1800.2-2017 auto 6.4.6
  function void set_severity_id_override(uvm_severity cur_severity,
                                         string id,
                                         uvm_severity new_severity);
    // has precedence over set_severity_override
    // silently override previous setting
    uvm_sev_override_array arr;
    if(!sev_id_overrides.exists(id))
      sev_id_overrides[id] = new;
 
    sev_id_overrides[id].add(cur_severity, new_severity);
  endfunction

  

  // Function- report
  //
  // This is the common handler method used by the four core reporting methods
  // (e.g., uvm_report_error) in <uvm_report_object>.

  virtual function void report(
      uvm_severity severity,
      string name,
      string id,
      string message,
      int verbosity_level=UVM_MEDIUM,
      string filename="",
      int line=0,
      uvm_report_object client=null
      );

    bit l_report_enabled = 0;
    uvm_report_message l_report_message;
    uvm_coreservice_t cs;
    cs = uvm_coreservice_t::get();
    if (!uvm_report_enabled(verbosity_level, UVM_INFO, id))
      return;

    if (client==null) 
      client = cs.get_root();

    l_report_message = uvm_report_message::new_report_message();
    l_report_message.set_report_message(severity, id, message, 
					verbosity_level, filename, line, name);
    l_report_message.set_report_object(client);
    l_report_message.set_action(get_action(severity,id));
    process_report_message(l_report_message);

  endfunction

endclass : uvm_report_handler

`endif //UVM_REPORT_HANDLER_SVH
