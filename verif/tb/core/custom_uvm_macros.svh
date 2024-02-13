`ifdef UVM_REPORT_DISABLE_FILE
`define uvm_file ""
`else
`define uvm_file `__FILE__
`endif

`ifdef UVM_REPORT_DISABLE_LINE
`define uvm_line 0
`else
`define uvm_line `__LINE__
`endif

typedef enum
{
      UVM_NONE   = 0,
      UVM_LOW    = 100,
      UVM_MEDIUM = 200,
      UVM_HIGH   = 300,
      UVM_FULL   = 400,
      UVM_DEBUG  = 500
} uvm_verbosity;

`define uvm_info(TOP, MSG, LVL) \
    begin \
        uvm_report_info(TOP, MSG, LVL, `uvm_file, `uvm_line); \
    end

`define uvm_warning(TOP, MSG, LVL) \
    begin \
        uvm_report_warning(TOP, MSG, LVL, `uvm_file, `uvm_line); \
    end

`define uvm_error(TOP, MSG) \
    begin \
        uvm_report_error(TOP, MSG, UVM_NONE, `uvm_file, `uvm_line); \
    end
`define uvm_fatal(TOP, MSG) \
    begin \
        uvm_report_fatal(TOP, MSG, UVM_NONE, `uvm_file, `uvm_line); \
    end


function void uvm_report_info(string id,
                  string message,
                  int verbosity = UVM_MEDIUM,
                  string filename = "",
                  int line = 0);
        $display($sformatf("UVM_INFO @ %t ns : %s %s", $time, id, message));
endfunction


function void uvm_report_warning(string id,
                                 string message,
                                 int verbosity = UVM_MEDIUM,
                                 string filename = "",
                                 int line = 0);
    $display($sformatf("UVM_WARNING @ %t ns : %s %s", $time, id , message));
endfunction


function void uvm_report_error(string id,
                               string message,
                               int verbosity = UVM_LOW,
                   string filename = "",
                   int line = 0);
    $display($sformatf("UVM_ERROR @ %t ns : %s %s", $time, id , message));
endfunction

function void uvm_report_fatal(string id,
                           string message,
                               int verbosity = UVM_NONE,
                   string filename = "",
                   int line = 0);
    $display($sformatf("UVM_FATAL @ %t ns : %s %s", $time, id , message));
    $finish();
endfunction
