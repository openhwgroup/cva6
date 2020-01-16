//
//------------------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2010-2014 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2010-2012 AMD
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2013 Cisco Systems, Inc.
// Copyright 2017 Verific
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

`ifndef UVM_REPORT_CLIENT_SVH
`define UVM_REPORT_CLIENT_SVH

typedef class uvm_component;
typedef class uvm_env;
typedef class uvm_root;

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_report_object
//
//------------------------------------------------------------------------------
//
// The uvm_report_object provides an interface to the UVM reporting facility.
// Through this interface, components issue the various messages that occur
// during simulation. Users can configure what actions are taken and what
// file(s) are output for individual messages from a particular component
// or for all messages from all components in the environment. Defaults are
// applied where there is no explicit configuration.
//
// Most methods in uvm_report_object are delegated to an internal instance of a
// <uvm_report_handler>, which stores the reporting configuration and determines
// whether an issued message should be displayed based on that configuration.
// Then, to display a message, the report handler delegates the actual
// formatting and production of messages to a central <uvm_report_server>.
//
// A report consists of an id string, severity, verbosity level, and the textual
// message itself. They may optionally include the filename and line number from
// which the message came. If the verbosity level of a report is greater than the
// configured maximum verbosity level of its report object, it is ignored.
// If a report passes the verbosity filter in effect, the report's action is
// determined. If the action includes output to a file, the configured file
// descriptor(s) are determined. 
//
// Actions - can be set for (in increasing priority) severity, id, and
// (severity,id) pair. They include output to the screen <UVM_DISPLAY>,
// whether the message counters should be incremented <UVM_COUNT>, and
// whether a $finish should occur <UVM_EXIT>.
//
// Default Actions - The following provides the default actions assigned to
// each severity. These can be overridden by any of the ~set_*_action~ methods.
//|    UVM_INFO -       UVM_DISPLAY
//|    UVM_WARNING -    UVM_DISPLAY
//|    UVM_ERROR -      UVM_DISPLAY | UVM_COUNT
//|    UVM_FATAL -      UVM_DISPLAY | UVM_EXIT
//
// File descriptors - These can be set by (in increasing priority) default,
// severity level, an id, or (severity,id) pair.  File descriptors are
// standard SystemVerilog file descriptors; they may refer to more than one file.
// It is the user's responsibility to open and close them.
//
// Default file handle - The default file handle is 0, which means that reports
// are not sent to a file even if a UVM_LOG attribute is set in the action
// associated with the report. This can be overridden by any of the ~set_*_file~
// methods.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 6.3.1
class uvm_report_object extends uvm_object;

  uvm_report_handler m_rh;


  // Function -- NODOCS -- new
  //
  // Creates a new report object with the given name. This method also creates
  // a new <uvm_report_handler> object to which most tasks are delegated.

  // @uvm-ieee 1800.2-2017 auto 6.3.2
  function new(string name = "");
    super.new(name);
    m_rh = uvm_report_handler::type_id::create(name);
  endfunction


  //----------------------------------------------------------------------------
  // Group -- NODOCS -- Reporting
  //----------------------------------------------------------------------------

  // Function -- NODOCS -- uvm_get_report_object
  //
  // Returns the nearest uvm_report_object when called.  From inside a
  // uvm_component, the method simply returns ~this~.
  // 
  // See also the global version of <uvm_get_report_object>.

  // @uvm-ieee 1800.2-2017 auto 6.3.3.1
  function uvm_report_object uvm_get_report_object();
    return this;
  endfunction

  // Function -- NODOCS -- uvm_report_enabled
  //
  // Returns 1 if the configured verbosity for this severity/id is greater than 
  // or equal to ~verbosity~ else returns 0.
  // 
  // See also <get_report_verbosity_level> and the global version of 
  // <uvm_report_enabled>.

  // @uvm-ieee 1800.2-2017 auto 6.3.3.2
  function int uvm_report_enabled(int verbosity, 
  				  uvm_severity severity = UVM_INFO, string id = "");
    if (get_report_verbosity_level(severity, id) < verbosity)
      return 0;
    return 1;
  endfunction

  // Function -- NODOCS -- uvm_report

  // @uvm-ieee 1800.2-2017 auto 6.3.3.3
  virtual function void uvm_report( uvm_severity severity,
                                    string id,
                                    string message,
                                    int verbosity = (severity == uvm_severity'(UVM_ERROR)) ? UVM_LOW :
                                                    (severity == uvm_severity'(UVM_FATAL)) ? UVM_NONE : UVM_MEDIUM,
                                    string filename = "",
                                    int line = 0,
                                    string context_name = "",
                                    bit report_enabled_checked =0);
    uvm_report_message l_report_message;
    if ((severity == UVM_INFO) && (report_enabled_checked == 0)) begin
      if (!uvm_report_enabled(verbosity, severity, id))
        return;
    end
    l_report_message = uvm_report_message::new_report_message();
    l_report_message.set_report_message(severity, id, message, 
					verbosity, filename, line, context_name);
    uvm_process_report_message(l_report_message);
  endfunction 


  // Function -- NODOCS -- uvm_report_info

  // @uvm-ieee 1800.2-2017 auto 6.3.3.3
  virtual function void uvm_report_info( string id,
					 string message,
					 int verbosity = UVM_MEDIUM,
					 string filename = "",
					 int line = 0,
    					 string context_name = "",
					 bit report_enabled_checked = 0);

    uvm_report (UVM_INFO, id, message, verbosity, 
                filename, line, context_name, report_enabled_checked);
  endfunction

  // Function -- NODOCS -- uvm_report_warning

  // @uvm-ieee 1800.2-2017 auto 6.3.3.3
  virtual function void uvm_report_warning( string id,
					    string message,
    					    int verbosity = UVM_MEDIUM,
					    string filename = "",
					    int line = 0,
    					    string context_name = "",
					    bit report_enabled_checked = 0);

    uvm_report (UVM_WARNING, id, message, verbosity,
                filename, line, context_name, report_enabled_checked);
  endfunction

  // Function -- NODOCS -- uvm_report_error

  // @uvm-ieee 1800.2-2017 auto 6.3.3.3
  virtual function void uvm_report_error( string id,
					  string message,
   					  int verbosity = UVM_NONE,
					  string filename = "",
					  int line = 0,
   					  string context_name = "",
					  bit report_enabled_checked = 0);

    uvm_report (UVM_ERROR, id, message, verbosity,
                filename, line, context_name, report_enabled_checked);
  endfunction

  // Function -- NODOCS -- uvm_report_fatal
  //
  // These are the primary reporting methods in the UVM. Using these instead
  // of ~$display~ and other ad hoc approaches ensures consistent output and
  // central control over where output is directed and any actions that
  // result. All reporting methods have the same arguments, although each has
  // a different default verbosity:
  //
  //   id        - a unique id for the report or report group that can be used
  //               for identification and therefore targeted filtering. You can
  //               configure an individual report's actions and output file(s)
  //               using this id string.
  //
  //   message   - the message body, preformatted if necessary to a single
  //               string.
  //
  //   verbosity - the verbosity of the message, indicating its relative
  //               importance. If this number is less than or equal to the
  //               effective verbosity level, see <set_report_verbosity_level>,
  //               then the report is issued, subject to the configured action
  //               and file descriptor settings.  Verbosity is ignored for 
  //               warnings, errors, and fatals. However, if a warning, error
  //               or fatal is demoted to an info message using the
  //               <uvm_report_catcher>, then the verbosity is taken into
  //               account.
  //
  //   filename/line - (Optional) The location from which the report was issued.
  //               Use the predefined macros, `__FILE__ and `__LINE__.
  //               If specified, it is displayed in the output.
  //
  //   context_name - (Optional) The string context from where the message is
  //               originating.  This can be the %m of a module, a specific
  //               method, etc.
  //
  //   report_enabled_checked - (Optional) This bit indicates whether the
  //               currently provided message has been checked as to whether
  //               the message should be processed. If it hasn't been checked, 
  //               it will be checked inside the uvm_report function.

  // @uvm-ieee 1800.2-2017 auto 6.3.3.3
  virtual function void uvm_report_fatal( string id,
					  string message,
   					  int verbosity = UVM_NONE,
					  string filename = "",
					  int line = 0,
   					  string context_name = "",
					  bit report_enabled_checked = 0);

    uvm_report (UVM_FATAL, id, message, verbosity,
                filename, line, context_name, report_enabled_checked);
  endfunction

  // Function -- NODOCS -- uvm_process_report_message
  //
  // This method takes a preformed uvm_report_message, populates it with 
  // the report object and passes it to the report handler for processing.
  // It is expected to be checked for verbosity and populated.

  // @uvm-ieee 1800.2-2017 auto 6.3.3.4
  virtual function void uvm_process_report_message(uvm_report_message report_message);
    report_message.set_report_object(this);
    m_rh.process_report_message(report_message);
  endfunction


  //----------------------------------------------------------------------------
  // Group -- NODOCS -- Verbosity Configuration
  //----------------------------------------------------------------------------


  // Function -- NODOCS -- get_report_verbosity_level
  //
  // Gets the verbosity level in effect for this object. Reports issued
  // with verbosity greater than this will be filtered out. The severity
  // and tag arguments check if the verbosity level has been modified for
  // specific severity/tag combinations.

  // @uvm-ieee 1800.2-2017 auto 6.3.4.1
  function int get_report_verbosity_level(uvm_severity severity=UVM_INFO, string id="");
    return m_rh.get_verbosity_level(severity, id);
  endfunction


  // Function -- NODOCS -- get_report_max_verbosity_level
  //
  // Gets the maximum verbosity level in effect for this report object.
  // Any report from this component whose verbosity exceeds this maximum will
  // be ignored.

  // @uvm-ieee 1800.2-2017 auto 6.3.4.2
  function int get_report_max_verbosity_level();
    return m_rh.m_max_verbosity_level;
  endfunction


  // Function -- NODOCS -- set_report_verbosity_level
  //
  // This method sets the maximum verbosity level for reports for this component.
  // Any report from this component whose verbosity exceeds this maximum will
  // be ignored.

  // @uvm-ieee 1800.2-2017 auto 6.3.4.3
  function void set_report_verbosity_level (int verbosity_level);
    m_rh.set_verbosity_level(verbosity_level);
  endfunction


  // @uvm-ieee 1800.2-2017 auto 6.3.4.4
  function void set_report_id_verbosity (string id, int verbosity);
    m_rh.set_id_verbosity(id, verbosity);
  endfunction

  // Function -- NODOCS -- set_report_severity_id_verbosity
  //
  // These methods associate the specified verbosity threshold with reports of the
  // given ~severity~, ~id~, or ~severity-id~ pair. This threshold is compared with
  // the verbosity originally assigned to the report to decide whether it gets
  // processed.  A verbosity threshold associated with a particular ~severity-id~ 
  // pair takes precedence over a verbosity threshold associated with ~id~, which 
  // takes precedence over a verbosity threshold associated with a ~severity~.
  //
  // The ~verbosity~ argument can be any integer, but is most commonly a
  // predefined <uvm_verbosity> value, <UVM_NONE>, <UVM_LOW>, <UVM_MEDIUM>,
  // <UVM_HIGH>, <UVM_FULL>.

  // @uvm-ieee 1800.2-2017 auto 6.3.4.4
  function void set_report_severity_id_verbosity (uvm_severity severity,
                                               string id, int verbosity);
    m_rh.set_severity_id_verbosity(severity, id, verbosity);
  endfunction


  //----------------------------------------------------------------------------
  // Group -- NODOCS -- Action Configuration
  //----------------------------------------------------------------------------


  // Function -- NODOCS -- get_report_action
  //
  // Gets the action associated with reports having the given ~severity~
  // and ~id~.

  // @uvm-ieee 1800.2-2017 auto 6.3.5.1
  function int get_report_action(uvm_severity severity, string id);
    return m_rh.get_action(severity,id);
  endfunction



  // @uvm-ieee 1800.2-2017 auto 6.3.5.2
  function void set_report_severity_action (uvm_severity severity,
                                            uvm_action action);
    m_rh.set_severity_action(severity, action);
  endfunction


  // @uvm-ieee 1800.2-2017 auto 6.3.5.2
  function void set_report_id_action (string id, uvm_action action);
    m_rh.set_id_action(id, action);
  endfunction

  // Function -- NODOCS -- set_report_severity_id_action
  //
  // These methods associate the specified action or actions with reports of the
  // given ~severity~, ~id~, or ~severity-id~ pair. An action associated with a
  // particular ~severity-id~ pair takes precedence over an action associated with
  // ~id~, which takes precedence over an action associated with a ~severity~.
  //
  // The ~action~ argument can take the value <UVM_NO_ACTION>, or it can be a
  // bitwise OR of any combination of <UVM_DISPLAY>, <UVM_LOG>, <UVM_COUNT>,
  // <UVM_STOP>, <UVM_EXIT>, and <UVM_CALL_HOOK>.

  // @uvm-ieee 1800.2-2017 auto 6.3.5.2
  function void set_report_severity_id_action (uvm_severity severity,
                                               string id, uvm_action action);
    m_rh.set_severity_id_action(severity, id, action);
  endfunction


  //----------------------------------------------------------------------------
  // Group -- NODOCS -- File Configuration
  //----------------------------------------------------------------------------


  // Function -- NODOCS -- get_report_file_handle
  //
  // Gets the file descriptor associated with reports having the given
  // ~severity~ and ~id~.

  // @uvm-ieee 1800.2-2017 auto 6.3.6.1
  function int get_report_file_handle(uvm_severity severity, string id);
    return m_rh.get_file_handle(severity,id);
  endfunction


  // Function -- NODOCS -- set_report_default_file
  
  // @uvm-ieee 1800.2-2017 auto 6.3.6.2
  function void set_report_default_file (UVM_FILE file);
    m_rh.set_default_file(file);
  endfunction

  // Function -- NODOCS -- set_report_id_file
  
  // @uvm-ieee 1800.2-2017 auto 6.3.6.2
  function void set_report_id_file (string id, UVM_FILE file);
    m_rh.set_id_file(id, file);
  endfunction


  // @uvm-ieee 1800.2-2017 auto 6.3.6.2
  function void set_report_severity_file (uvm_severity severity, UVM_FILE file);
    m_rh.set_severity_file(severity, file);
  endfunction

  // Function -- NODOCS -- set_report_severity_id_file
  //
  // These methods configure the report handler to direct some or all of its
  // output to the given file descriptor. The ~file~ argument must be a
  // multi-channel descriptor (mcd) or file id compatible with $fdisplay.
  //
  // A FILE descriptor can be associated with reports of
  // the given ~severity~, ~id~, or ~severity-id~ pair.  A FILE associated with
  // a particular ~severity-id~ pair takes precedence over a FILE associated
  // with ~id~, which take precedence over an a FILE associated with a 
  // ~severity~, which takes precedence over the default FILE descriptor.
  //
  // When a report is issued and its associated action has the UVM_LOG bit
  // set, the report will be sent to its associated FILE descriptor.
  // The user is responsible for opening and closing these files.

  // @uvm-ieee 1800.2-2017 auto 6.3.6.2
  function void set_report_severity_id_file (uvm_severity severity, string id,
                                             UVM_FILE file);
    m_rh.set_severity_id_file(severity, id, file);
  endfunction


  //----------------------------------------------------------------------------
  // Group -- NODOCS -- Override Configuration
  //----------------------------------------------------------------------------



  // @uvm-ieee 1800.2-2017 auto 6.3.7
  function void set_report_severity_override(uvm_severity cur_severity,
                                             uvm_severity new_severity);
    m_rh.set_severity_override(cur_severity, new_severity);
  endfunction


  // @uvm-ieee 1800.2-2017 auto 6.3.7
  function void set_report_severity_id_override(uvm_severity cur_severity,
                                                string id, 
                                                uvm_severity new_severity);
    m_rh.set_severity_id_override(cur_severity, id, new_severity);
  endfunction


  //----------------------------------------------------------------------------
  // Group -- NODOCS -- Report Handler Configuration
  //----------------------------------------------------------------------------

  // Function -- NODOCS -- set_report_handler
  //
  // Sets the report handler, overwriting the default instance. This allows
  // more than one component to share the same report handler.

  // @uvm-ieee 1800.2-2017 auto 6.3.8.2
  function void set_report_handler(uvm_report_handler handler);
    m_rh = handler;
  endfunction


  // Function -- NODOCS -- get_report_handler
  //
  // Returns the underlying report handler to which most reporting tasks
  // are delegated.

  // @uvm-ieee 1800.2-2017 auto 6.3.8.1
  function uvm_report_handler get_report_handler();
    return m_rh;
  endfunction


  // Function -- NODOCS -- reset_report_handler
  //
  // Resets the underlying report handler to its default settings. This clears
  // any settings made with the ~set_report_*~ methods (see below).

  // @uvm-ieee 1800.2-2017 auto 6.3.8.3
  function void reset_report_handler;
    m_rh.initialize();
  endfunction

endclass

`endif // UVM_REPORT_CLIENT_SVH
