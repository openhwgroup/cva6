// 
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// 
// Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// 


`ifndef __UVML_RS_JSON_SV__
`define __UVML_RS_JSON_SV__


/**
 * Replacement for uvm_report_server to log messages to a JSON format
 * that can be more easily reused and manipulated by external tools/ viewers
 */
class uvml_logs_rs_json_c extends uvm_default_report_server;

   uvm_report_server  old_report_server;
   uvm_report_server  global_server;

   int logfile_handle;


   /**
    *
    */
   extern function new(string name="uvml_logs_rs_json", log_filename="log.json");

   /**
    *
    */
   extern function void install_server();

   /**
    * Helper function to convert verbosity value to appropriate string, based on uvm_verbosity enum if an equivalent level
    */
   extern function string convert_verbosity_to_string(int verbosity);

   /**
    * Output standard XML header to log file
    */
   extern function void report_header(UVM_FILE file=0);

   /**
    * Output XML closing tags to log file
    */
   extern function void report_footer(UVM_FILE file=0);

   /**
    * tidy up logging and restore global report server
    */
   extern virtual function void report_summarize(UVM_FILE file=0);

   /**
    *
    */
   // Waiving Verissimo linter SVTB.32.2.0: Pass strings by reference unless otherwise needed
   extern virtual function string compose_report_message(uvm_report_message report_message, string report_object_name=""); //@DVT_LINTER_WAIVER "MT20211228_6" disable SVTB.32.2.0

endclass : uvml_logs_rs_json_c


function uvml_logs_rs_json_c::new(string name="uvml_logs_rs_json", log_filename="log.json");

   super.new(name);

   global_server = uvm_report_server::get_server();
   install_server();
   logfile_handle = $fopen(log_filename, "w");
   report_header(logfile_handle);

endfunction : new


function void uvml_logs_rs_json_c::install_server();

   old_report_server = global_server;
   uvm_report_server::set_server(this);

endfunction : install_server


function string uvml_logs_rs_json_c::convert_verbosity_to_string(int verbosity);

   uvm_verbosity  l_verbosity;

   if ($cast(l_verbosity, verbosity)) begin
      convert_verbosity_to_string = l_verbosity.name();
   end
   else begin
      string l_str;
      l_str.itoa(verbosity);
      convert_verbosity_to_string = l_str;
   end

endfunction : convert_verbosity_to_string


function void uvml_logs_rs_json_c::report_header(UVM_FILE file=0);

   f_display(file, "[");

endfunction


function void uvml_logs_rs_json_c::report_footer(UVM_FILE file=0);

   f_display(file, "]");

endfunction


function void uvml_logs_rs_json_c::report_summarize(UVM_FILE file=0);

   report_footer(logfile_handle);
   global_server.set_server(old_report_server);
   $fclose(logfile_handle);
   old_report_server.report_summarize(file);

endfunction : report_summarize


function string uvml_logs_rs_json_c::compose_report_message(uvm_report_message report_message, string report_object_name="");

   string final_msg_str;

   string severity_str;
   string verbosity_str;

   uvm_severity temp_sev;

   temp_sev = report_message.get_severity();
   severity_str  = temp_sev.name();
   verbosity_str = convert_verbosity_to_string(report_message.get_verbosity());

   final_msg_str = {"{",
      $sformatf("\"time\":\"%0t\","    , $realtime()                  ),
      $sformatf("\"id\":\"%s\","       , report_message.get_id()      ),
      $sformatf("\"msg\":\"%s\","      , report_message.get_message() ),
      $sformatf("\"verbosity\":\"%s\",", verbosity_str                ),
      $sformatf("\"severity\":\"%s\"," , severity_str                 ),
      $sformatf("\"file\":\"%s\","     , report_message.get_filename()),
      $sformatf("\"line\":%0d,"        , report_message.get_line()    ),
      $sformatf("\"context\":\"%s\""   , report_message.get_context() ),
   "}"};

   return final_msg_str;

endfunction : compose_report_message


`endif // __UVML_RS_JSON_SV__
