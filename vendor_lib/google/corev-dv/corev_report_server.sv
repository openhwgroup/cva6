class corev_report_server extends uvm_default_report_server;
   
   extern function new(string name="corev_report_server");
      
   extern virtual function string compose_report_message(uvm_report_message report_message, string report_object_name="");   
   extern virtual function void report_summarize(UVM_FILE file=0);
endclass : corev_report_server

function corev_report_server::new(string name = "corev_report_server");
   super.new(name);
endfunction : new


function string corev_report_server::compose_report_message(uvm_report_message report_message, string report_object_name="");
   
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


function void corev_report_server::report_summarize(UVM_FILE file=0);
   
   super.report_summarize(file);
  
endfunction : report_summarize

