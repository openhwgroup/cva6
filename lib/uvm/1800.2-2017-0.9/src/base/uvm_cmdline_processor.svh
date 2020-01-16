//
//------------------------------------------------------------------------------
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2010-2012 AMD
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2017 Cisco Systems, Inc.
// Copyright 2015 Analog Devices, Inc.
// Copyright 2011 Synopsys, Inc.
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

class uvm_cmd_line_verb;
  string comp_path;
  string id;
  uvm_verbosity verb;
  int exec_time;
endclass

// Class -- NODOCS -- uvm_cmdline_processor
//
// This class provides an interface to the command line arguments that 
// were provided for the given simulation.  The class is intended to be
// used as a singleton, but that isn't required.  The generation of the
// data structures which hold the command line argument information 
// happens during construction of the class object.  A global variable 
// called ~uvm_cmdline_proc~ is created at initialization time and may 
// be used to access command line information.
//
// The uvm_cmdline_processor class also provides support for setting various UVM
// variables from the command line such as components' verbosities and configuration
// settings for integral types and strings.  Each of these capabilities is described 
// in the Built-in UVM Aware Command Line Arguments section.
//

// @uvm-ieee 1800.2-2017 auto G.1.1
class uvm_cmdline_processor extends uvm_report_object;

  static local uvm_cmdline_processor m_inst;

  // Group -- NODOCS -- Singleton 

  // Function -- NODOCS -- get_inst
  //
  // Returns the singleton instance of the UVM command line processor.

  // @uvm-ieee 1800.2-2017 auto G.1.2
  static function uvm_cmdline_processor get_inst();
    if(m_inst == null) 
      m_inst = new("uvm_cmdline_proc");
    return m_inst;
  endfunction

  protected string m_argv[$]; 
  protected string m_plus_argv[$];
  protected string m_uvm_argv[$];

  // Group -- NODOCS -- Basic Arguments
  
  // Function -- NODOCS -- get_args
  //
  // This function returns a queue with all of the command line
  // arguments that were used to start the simulation. Note that
  // element 0 of the array will always be the name of the 
  // executable which started the simulation.

  // @uvm-ieee 1800.2-2017 auto G.1.3.1
  function void get_args (output string args[$]);
    args = m_argv;
  endfunction

  // Function -- NODOCS -- get_plusargs
  //
  // This function returns a queue with all of the plus arguments
  // that were used to start the simulation. Plusarguments may be
  // used by the simulator vendor, or may be specific to a company
  // or individual user. Plusargs never have extra arguments
  // (i.e. if there is a plusarg as the second argument on the
  // command line, the third argument is unrelated); this is not
  // necessarily the case with vendor specific dash arguments.

  // @uvm-ieee 1800.2-2017 auto G.1.3.2
  function void get_plusargs (output string args[$]);
    args = m_plus_argv;
  endfunction

  // Function -- NODOCS -- get_uvmargs
  //
  // This function returns a queue with all of the uvm arguments
  // that were used to start the simulation. A UVM argument is
  // taken to be any argument that starts with a - or + and uses
  // the keyword UVM (case insensitive) as the first three
  // letters of the argument.

  // @uvm-ieee 1800.2-2017 auto G.1.3.3
  function void get_uvm_args (output string args[$]);
    args = m_uvm_argv;
  endfunction

  // Function -- NODOCS -- get_arg_matches
  //
  // This function loads a queue with all of the arguments that
  // match the input expression and returns the number of items
  // that matched. If the input expression is bracketed
  // with //, then it is taken as an extended regular expression 
  // otherwise, it is taken as the beginning of an argument to match.
  // For example:
  //
  //| string myargs[$]
  //| initial begin
  //|    void'(uvm_cmdline_proc.get_arg_matches("+foo",myargs)); //matches +foo, +foobar
  //|                                                            //doesn't match +barfoo
  //|    void'(uvm_cmdline_proc.get_arg_matches("/foo/",myargs)); //matches +foo, +foobar,
  //|                                                             //foo.sv, barfoo, etc.
  //|    void'(uvm_cmdline_proc.get_arg_matches("/^foo.*\.sv",myargs)); //matches foo.sv
  //|                                                                   //and foo123.sv,
  //|                                                                   //not barfoo.sv.

  // @uvm-ieee 1800.2-2017 auto G.1.3.4
  function int get_arg_matches (string match, ref string args[$]);
    bit match_is_regex = (match.len() > 2) && (match[0] == "/") && (match[match.len()-1] == "/");
    int len = match.len();

    args.delete();
    foreach (m_argv[i]) begin
      if ( match_is_regex && uvm_is_match( match, m_argv[i] ) ) begin
        args.push_back( m_argv[i] );
      end
      else if((m_argv[i].len() >= len) && (m_argv[i].substr(0,len - 1) == match)) begin
        args.push_back(m_argv[i]);
      end
    end

    return args.size();
  endfunction


  // Group -- NODOCS -- Argument Values

  // Function -- NODOCS -- get_arg_value
  //
  // This function finds the first argument which matches the ~match~ arg and
  // returns the suffix of the argument. This is similar to the $value$plusargs
  // system task, but does not take a formatting string. The return value is
  // the number of command line arguments that match the ~match~ string, and
  // ~value~ is the value of the first match.
  
  // @uvm-ieee 1800.2-2017 auto G.1.4.1
  function int get_arg_value (string match, ref string value);
    int chars = match.len();
    get_arg_value = 0;
    foreach (m_argv[i]) begin
      if(m_argv[i].len() >= chars) begin
        if(m_argv[i].substr(0,chars-1) == match) begin
          get_arg_value++;
          if(get_arg_value == 1)
            value = m_argv[i].substr(chars,m_argv[i].len()-1);
        end
      end
    end
  endfunction

  // Function -- NODOCS -- get_arg_values
  //
  // This function finds all the arguments which matches the ~match~ arg and
  // returns the suffix of the arguments in a list of values. The return
  // value is the number of matches that were found (it is the same as
  // values.size() ).
  // For example if '+foo=1,yes,on +foo=5,no,off' was provided on the command
  // line and the following code was executed:
  //
  //| string foo_values[$]
  //| initial begin
  //|    void'(uvm_cmdline_proc.get_arg_values("+foo=",foo_values));
  //|
  //
  // The foo_values queue would contain two entries.  These entries are shown
  // here:
  //
  //   0 - "1,yes,on"
  //   1 - "5,no,off"
  //
  // Splitting the resultant string is left to user but using the
  // uvm_split_string() function is recommended.

  // @uvm-ieee 1800.2-2017 auto G.1.4.2
  function int get_arg_values (string match, ref string values[$]);
    int chars = match.len();

    values.delete();
    foreach (m_argv[i]) begin
      if(m_argv[i].len() >= chars) begin
        if(m_argv[i].substr(0,chars-1) == match)
          values.push_back(m_argv[i].substr(chars,m_argv[i].len()-1));
      end
    end
    return values.size();
  endfunction

  // Group -- NODOCS -- Tool information

  // Function -- NODOCS -- get_tool_name
  //
  // Returns the simulation tool that is executing the simulation.
  // This is a vendor specific string.

  function string get_tool_name ();
    return uvm_dpi_get_tool_name();
  endfunction

  // Function -- NODOCS -- get_tool_version
  //
  // Returns the version of the simulation tool that is executing the simulation.
  // This is a vendor specific string.

  function string  get_tool_version ();
    return uvm_dpi_get_tool_version();
  endfunction

  // constructor

  function new(string name = "");
    string s;
    string sub;
    int doInit=1;
    super.new(name);
    do begin
      s = uvm_dpi_get_next_arg(doInit);
      doInit=0;
      if(s!="") begin
        m_argv.push_back(s);
        if(s[0] == "+") begin
          m_plus_argv.push_back(s);
        end 
        if(s.len() >= 4 && (s[0]=="-" || s[0]=="+")) begin
          sub = s.substr(1,3);
          sub = sub.toupper();
          if(sub == "UVM")
            m_uvm_argv.push_back(s);
        end 
      end
    end while(s!=""); 

  endfunction

  function bit m_convert_verb(string verb_str, output uvm_verbosity verb_enum);
    case (verb_str)
      "NONE"       : begin verb_enum = UVM_NONE;   return 1; end
      "UVM_NONE"   : begin verb_enum = UVM_NONE;   return 1; end
      "LOW"        : begin verb_enum = UVM_LOW;    return 1; end
      "UVM_LOW"    : begin verb_enum = UVM_LOW;    return 1; end
      "MEDIUM"     : begin verb_enum = UVM_MEDIUM; return 1; end
      "UVM_MEDIUM" : begin verb_enum = UVM_MEDIUM; return 1; end
      "HIGH"       : begin verb_enum = UVM_HIGH;   return 1; end
      "UVM_HIGH"   : begin verb_enum = UVM_HIGH;   return 1; end
      "FULL"       : begin verb_enum = UVM_FULL;   return 1; end
      "UVM_FULL"   : begin verb_enum = UVM_FULL;   return 1; end
      "DEBUG"      : begin verb_enum = UVM_DEBUG;  return 1; end
      "UVM_DEBUG"  : begin verb_enum = UVM_DEBUG;  return 1; end
      default      : begin                         return 0; end
    endcase
  endfunction

endclass
