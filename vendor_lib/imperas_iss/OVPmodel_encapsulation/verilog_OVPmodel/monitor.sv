/*
 *
 * Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com
 *
 * The contents of this file are provided under the Software License
 * Agreement that you accepted before downloading this file.
 *
 * This source forms part of the Software and can be used for educational,
 * training, and demonstration purposes but cannot be used for derivative
 * works except in cases where the derivative works require OVP technology
 * to run.
 *
 * For open source models released under licenses that you can use for
 * derivative works, please visit www.OVPworld.org or www.imperas.com
 * for the location of the open source models.
 *
 */

 
`include "typedefs.sv"

module MONITOR 
#(
    parameter ID         = 0,
    parameter VARIANT    = "VARIANT",
    parameter STOPONTRAP = 1
)
(
    BUS SysBus
);
    int     fd_sym;
    string  fn_sym;
    string  type_sym[string];
    int     addr_sym[string];

    watchT begin_signature;
    watchT end_signature;
    watchT _test_stdout;
    watchT _test_exit;
    watchT trap_vector;
    //watchT zero;
    
    int fd_signature, fd_stdout;
    
    function automatic void split_string (
        output string out [$],
        input string in,
        input string separator = ",",
        input bit drop_blank = 1
    );
        string val;
        bit flag;
        in = {in,separator};
        out.delete();
        foreach (in[i]) begin
            if (drop_blank && in[i] == " ") continue;
            if (in[i] == separator[0]) begin
                if (flag) begin
                    flag = 0;
                end else if (val != "") begin
                    out.push_back(val);
                end
                val = "";
            end else begin
                val = {val, in[i]};
            end
        end
    endfunction
    
    function automatic void nm_get(string name_sym, ref watchT watch);
        if (addr_sym.exists(name_sym)) begin
            watch.addr   = addr_sym[name_sym];
            watch.enable = 1;
        end else begin
            watch.enable = 0;
        end
    endfunction
    
    function automatic void nm_load();
        int i, j;
        string line;
        string linesplit[$];
        string name_sym;
        
        if (!($value$plusargs("nm_file=%s", fn_sym))) begin
            $display("FATAL: +nm_file=<nm filename> is required");
            $fatal;
        end
        fd_sym = $fopen(fn_sym, "r");
        if (fd_sym == 0) begin
            $display("FATAL: nm_file(%0s) can not be opened for reading", fn_sym);
            $fatal;
        end
        
        while ($fgets(line, fd_sym)) begin
            j = line.len() - 2;
            line = line.substr(0, j);
            
            split_string(linesplit, line, " ", 0);
            name_sym = linesplit[2];
            
            addr_sym[name_sym] = linesplit[0].atohex();
            type_sym[name_sym] = linesplit[1];
        end
        $fclose(fd_sym);
    endfunction
    
    // Generate a signature dump file
    function automatic void dumpSignature();
        automatic int addr = begin_signature.addr;
        automatic string sig_file;
        automatic string sig_file_stub;
        
        if (!begin_signature.enable) return;

        if ($value$plusargs("sig_file=%s", sig_file_stub)) begin
            $sformat(sig_file,"%s.%s.%0d.sig",sig_file_stub,VARIANT,ID);
    
            $display("[%m] Writing signature %s", sig_file);
            
            $display("[%m] Dump Signature 0x%x -> 0x%x", begin_signature.addr, end_signature.addr);
    
            fd_signature = $fopen(sig_file, "w");
    
            while (addr < end_signature.addr) begin
                $fwrite(fd_signature, "%x\n", ram.mem[addr>>2]);
                addr = addr + 4;
            end
      
            $fclose(fd_signature);
        end
    endfunction
    
    function void openStdout();
        automatic string stdout_file;
        automatic string stdout_file_stub;
        if ($value$plusargs("stdout_file=%s", stdout_file_stub)) begin
            $sformat(stdout_file,"%s.%s.%0d.stdout",stdout_file_stub,VARIANT,ID);
    
            $display("[%m] Opening stdout %s", stdout_file);
        
            fd_stdout = $fopen(stdout_file, "w");
        end
    endfunction
    
    function void closeStdout();
        if(fd_stdout) $fclose(fd_stdout);
    endfunction

    initial begin
        //nm_load();
        
        nm_get("trap_vector"    , trap_vector);
        nm_get("begin_signature", begin_signature);
        nm_get("end_signature"  , end_signature);
        nm_get("_test_stdout"   , _test_stdout);
        nm_get("_test_exit"     , _test_exit);

        if (trap_vector.enable)     $display("[%m] trap_vector     = 0x%x",  trap_vector.addr);
        if (begin_signature.enable) $display("[%m] begin_signature = 0x%x",  begin_signature.addr);
        if (end_signature.enable)   $display("[%m] end_signature   = 0x%x",  end_signature.addr);
        if (_test_stdout.enable)    $display("[%m] _test_stdout    = 0x%x", _test_stdout.addr);
        if (_test_exit.enable)      $display("[%m] _test_exit      = 0x%x", _test_exit.addr);
        //zero.addr   = 0;
        //zero.enable = 1;
        
        openStdout();
    end
    
    bit [31:0] Addr;
    bit [31:0] Data;
    bit [3:0]  Dbe;
    bit [2:0]  Size;
    bit RD, WR, IF, LD, ST;
    bit MSWInt, USWInt, SSWInt;
    bit MTInt, UTInt, STInt;
    bit MEInt, UEInt, SEInt;
    always @(*) begin
        Addr   = SysBus.Addr;
        Data   = SysBus.Data;
        Dbe    = SysBus.Dbe;
        Size   = SysBus.Size;
        MSWInt = SysBus.MSWInterrupt;
        USWInt = SysBus.USWInterrupt;
        SSWInt = SysBus.SSWInterrupt;
        MTInt  = SysBus.MTimerInterrupt;
        UTInt  = SysBus.UTimerInterrupt;
        STInt  = SysBus.STimerInterrupt;
        MEInt  = SysBus.MExternalInterrupt;
        UEInt  = SysBus.UExternalInterrupt;
        SEInt  = SysBus.SExternalInterrupt;

        IF     = (SysBus.Transfer==Fetch);
        LD     = (SysBus.Transfer==Load);
        ST     = (SysBus.Transfer==Store);
        RD     = IF | LD;
        WR     = ST;
    end
    
    always @(posedge SysBus.Clk) begin
        case (SysBus.Transfer)
            Fetch: begin
                // EXIT
                if (_test_exit.enable && SysBus.Addr==_test_exit.addr) begin
                    $display("[%m] Fetch: Exit Label");
                    SysBus.Shutdown = 1;
                    //$finish();
                end
                // TRAP
                if (trap_vector.enable && SysBus.Addr==trap_vector.addr) begin
                    $display("[%m] Fetch: Trap Label");
                    if(STOPONTRAP)  SysBus.Shutdown = 1;
                end
                //// @zero default reset
                //if (zero.enable && SysBus.Addr==zero.addr) begin
                //    $display("[%m] Fetch: Reset");
                //end
            end
            Load: begin
            end
            Store: begin
                // STDOUT
                if (_test_stdout.enable && SysBus.Addr==_test_stdout.addr) begin
                    automatic int c = SysBus.Data&'hff;
                    $write("%c", c);
                    if(fd_stdout) begin
                        $fwrite(fd_stdout, "%c", c);
                        $fflush(fd_stdout);
                    end
                end
            end
            default: begin
            end
        endcase
    end
        
    final begin
        dumpSignature();
        closeStdout();
    end
endmodule
