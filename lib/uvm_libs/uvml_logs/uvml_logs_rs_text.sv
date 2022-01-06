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


`ifndef __UVML_LOGS_RS_TEXT_SV__
`define __UVML_LOGS_RS_TEXT_SV__


/**
 * Replacement for uvm_report_server to log messages to a JSON format
 * that can be more easily reused and manipulated by external tools/ viewers
 */
class uvml_logs_rs_text_c extends uvm_default_report_server;
   
   /**
    * 
    */
   extern function new(string name="uvml_logs_rs_text");
   
   /**
    * 
    */
   // Waiving Verissimo linter SVTB.32.2.0: Pass strings by reference unless otherwise needed
   extern virtual function string compose_report_message(uvm_report_message report_message, string report_object_name=""); //@DVT_LINTER_WAIVER "MT20211228_5" disable SVTB.32.2.0
   
   /**
    * 
    */
   extern virtual function void report_summarize(UVM_FILE file=0);
   
endclass : uvml_logs_rs_text_c


function uvml_logs_rs_text_c::new(string name="uvml_logs_rs_text");

   super.new(name);
   
endfunction : new


function string uvml_logs_rs_text_c::compose_report_message(uvm_report_message report_message, string report_object_name="");
   
   string sev_string;
   uvm_severity l_severity;
   uvm_verbosity l_verbosity;
   string reduced_filename;
   string filename_line_string;
   string time_str;
   string line_str;
   string context_str;
   string verbosity_str;
   string terminator_str;
   string msg_body_str;
   uvm_report_message_element_container el_container;
   string prefix;
   uvm_report_handler l_report_handler;
   
   l_severity = report_message.get_severity();
   sev_string = l_severity.name();
   
   if (report_message.get_filename() != "") begin
      reduced_filename = report_message.get_filename();
      for (int unsigned ii=(reduced_filename.len()-1); ii>0; ii--) begin
         if (reduced_filename.getc(ii) == "/") begin
            reduced_filename = reduced_filename.substr(ii+1, (reduced_filename.len()-1));
            break;
         end
      end
      line_str.itoa(report_message.get_line());
      filename_line_string = {reduced_filename, "(", line_str, ")"};
   end
   
   // Make definable in terms of units.
   $swrite(time_str, "%0t", $realtime);
   
   if (report_message.get_context() != "") begin
      context_str = {"@@", report_message.get_context()};
   end
   
   if (show_verbosity) begin
      if ($cast(l_verbosity, report_message.get_verbosity()))
         verbosity_str = l_verbosity.name();
      else
         verbosity_str.itoa(report_message.get_verbosity());
      verbosity_str = {"(", verbosity_str, ")"};
   end
   
   if (show_terminator) begin
      terminator_str = {" -",sev_string};
   end
   
   el_container = report_message.get_element_container();
   if (el_container.size() == 0) begin
      msg_body_str = report_message.get_message();
   end
   else begin
      prefix = uvm_default_printer.knobs.prefix;
      uvm_default_printer.knobs.prefix = " +";
      msg_body_str = {report_message.get_message(), "\n", el_container.sprint()};
      uvm_default_printer.knobs.prefix = prefix;
   end
   
   if (report_object_name == "") begin
      l_report_handler = report_message.get_report_handler();
      report_object_name = l_report_handler.get_full_name();
   end
   
   compose_report_message = {sev_string, verbosity_str, " @ ", time_str, " : ", filename_line_string
    , " ", report_object_name, context_str,
     " [", report_message.get_id(), "] ", msg_body_str, terminator_str};
   
endfunction : compose_report_message


function void uvml_logs_rs_text_c::report_summarize(UVM_FILE file=0);
   
   super.report_summarize(file);
   
   /*string id;
   string name;
   string output_str;
   string q[$];
   
   uvm_report_catcher::summarize();
   q.push_back("\n--- UVM Report Summary ---\n\n");
   
   if (m_max_quit_count != 0) begin
      if (m_quit_count >= m_max_quit_count) begin
         q.push_back("Quit count reached!\n");
      end
      q.push_back($sformatf("Quit count : %5d of %5d\n",m_quit_count, m_max_quit_count));
   end
   
   q.push_back("** Report counts by severity\n");
   foreach (m_severity_count[s]) begin
      q.push_back($sformatf("%s :%5d\n", s.name(), m_severity_count[s]));
   end
   
   if (enable_report_id_count_summary) begin
      q.push_back("** Report counts by id\n");
      foreach(m_id_count[id]) begin
         q.push_back($sformatf("[%s] %5d\n", id, m_id_count[id]));
      end
   end
   
   `uvm_info("UVM/REPORT/SERVER", `UVM_STRING_QUEUE_STREAMING_PACK(q), UVM_LOW)*/
   
endfunction : report_summarize


`endif // __UVML_LOGS_RS_TEXT_SV__
