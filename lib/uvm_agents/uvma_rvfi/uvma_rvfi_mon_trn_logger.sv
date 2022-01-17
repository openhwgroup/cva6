// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
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


`ifndef __UVMA_RVFI_MON_TRN_LOGGER_SV__
`define __UVMA_RVFI_MON_TRN_LOGGER_SV__

/**
 * Component writing Rvfi monitor transactions rvfi data to disk as plain text.
 */
class uvma_rvfi_mon_trn_logger_c#(int ILEN=DEFAULT_ILEN,
                                  int XLEN=DEFAULT_XLEN) extends uvml_logs_mon_trn_logger_c#(
   .T_TRN  (uvml_trn_seq_item_c),
   .T_CFG  (uvma_rvfi_cfg_c    ),
   .T_CNTXT(uvma_rvfi_cntxt_c  )
);

   uvm_analysis_imp_rvfi_instr#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvma_rvfi_mon_trn_logger_c) instr_export;

   const string format_header_str = "%15s | RVFI | %8s | %6s | %8s | %8s | %s | %03s | %08s | %03s | %08s | %03s | %08s | %03s | %08s | %08s | %s";
   const string format_instr_str  = "%15s | RVFI | %8d | %6d | %8x | %8s | %s | x%-2d | %08x | x%-2d | %08x | x%-2d | %08x";
   const string format_mem_str    = "| %02s | %08x | %08s |";

   uvma_rvfi_instr_table_seq_item_c#(ILEN,XLEN) instr_table[bit[XLEN-1:0]];

   `uvm_component_param_utils(uvma_rvfi_mon_trn_logger_c)

   /**
    * Default constructor.
    */
   function new(string name="uvma_rvfi_mon_trn_logger", uvm_component parent=null);

      super.new(name, parent);

      instr_export = new("instr_export", this);

   endfunction : new

   /**
    * Build phase - attempt to load a firmware itb file (instruction table file)
    */
   function void build_phase(uvm_phase phase);

      read_itb_file();

   endfunction : build_phase

   /**
    * Read the itb file and build an instruction library
    */
   function void read_itb_file();

      string file;

      if ($value$plusargs("itb_file=%s", file)) begin
         int unsigned itb_lineno;
         int fh;

         fh = $fopen(file, "r");
         if (fh == 0) begin
            `uvm_fatal("RVFIMONLOG", $sformatf("Could not open itb file: %s", file));
         end

         while (!$feof(fh)) begin
            string       str;

            int unsigned num;
            int unsigned c;
            string       src_code_q[$];
            uvma_rvfi_instr_table_seq_item_c instr;

            itb_lineno++;
            c = $fscanf(fh, "%1s%d", str, num);
            instr = uvma_rvfi_instr_table_seq_item_c#(ILEN,XLEN)::type_id::create("instr");

            `uvm_info("RVFIMONLOG", $sformatf("Parsing line_num: %0d with %0d lines of src", itb_lineno, num), UVM_HIGH)
            if (c == -1) begin
               break;
            end
            else if (num == 0) begin
               src_code_q.push_back("*** N/A ***");
            end
            else begin
               // Accumulate the source code
               repeat (num) begin
                  itb_lineno++;
                  c = $fscanf(fh, "%1s", str);
                  c = $fgets(str, fh);

                  src_code_q.push_back(str.substr(0,str.len()-1));
               end
            end

            instr.src_code = new[src_code_q.size()](src_code_q);

            // Parse the context of the source code
            c = $fscanf(fh, "%d %s %s %d %s %d", instr.addr, instr.src_function, instr.filename, instr.lineno, instr.mcode, num);
            for (int i = 0; i < num; i++) begin
               string asm_str;

               c = $fscanf(fh, "%s", asm_str);
               if (i == 0)
                  instr.asm = asm_str;
               else
                  instr.asm = { instr.asm, " ", asm_str };
            end
            itb_lineno++;

            // Fatal error if instruction already exists at the respective address
            if (instr_table.exists(instr.addr)) begin
               `uvm_info("RVFIMONLOG", $sformatf("%s", instr_table[instr.addr].sprint()), UVM_LOW);
               `uvm_info("RVFIMONLOG", $sformatf("%s", instr.sprint()), UVM_LOW);
               `uvm_fatal("RVFIMONLOG", $sformatf("%0d: Instruction at address: 0x%08x already exists in instruction table", itb_lineno, instr.addr));
            end
            instr_table[instr.addr] = instr;

            `uvm_info("RVFIMONLOG", $sformatf("%s", instr.sprint()), UVM_DEBUG);
         end
      end

   endfunction : read_itb_file

   /**
    * Writes contents of t to disk
    */
   virtual function void write(uvml_trn_seq_item_c t);
   endfunction : write

   virtual function void write_rvfi_instr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t);
      string instr;

      instr = $sformatf(format_instr_str, $sformatf("%t", $time),
                        t.cycle_cnt,
                        t.order,
                        t.pc_rdata,
                        t.get_insn_word_str(),
                        get_mode_str(t.mode),
                        t.rs1_addr, t.rs1_rdata,
                        t.rs2_addr, t.rs2_rdata,
                        t.rd1_addr, t.rd1_wdata);

      if (t.mem_wmask)
         instr = $sformatf({"%s ", format_mem_str}, instr, " WR", t.mem_addr, t.get_mem_data_string());
      else if (t.mem_rmask)
         instr = $sformatf({"%s ", format_mem_str}, instr, " RD", t.mem_addr, t.get_mem_data_string());
      else
         instr = $sformatf("%s |  -- | -------- | -------- |", instr);

      if (t.insn_interrupt)
         instr = $sformatf("%s INTR %0d", instr, t.insn_interrupt_id);
      if (t.insn_nmi_load_fault)
         instr = $sformatf("%s NMI LOAD", instr);
      if (t.insn_nmi_store_fault)
         instr = $sformatf("%s NMI STORE", instr);
      if (t.dbg)
         instr = $sformatf("%s DEBUG", instr);

      if (instr_table.exists(t.pc_rdata)) begin
         instr = $sformatf("%s %s %s %0d - %s",
                           instr,
                           instr_table[t.pc_rdata].src_function,
                           instr_table[t.pc_rdata].filename,
                           instr_table[t.pc_rdata].lineno,
                           instr_table[t.pc_rdata].asm);
      end

      fwrite(instr);

   endfunction : write_rvfi_instr

   /**
    * Writes log header to disk
    */
   virtual function void print_header();

      string banner = {160{"-"}};

      fwrite(banner);
      fwrite($sformatf(format_header_str,
                       " TIME", "CYCLE", "ORDER", "PC", "INSTR", "M", "RS1", "RS1_DATA", "RS2", "RS2_DATA", "RD",
                       "RD_DATA", "MEM", "MEM_ADDR", "MEM_DATA", "INSTRUCTION"));
      fwrite(banner);

   endfunction : print_header

endclass : uvma_rvfi_mon_trn_logger_c


`endif // __UVMA_RVFI_MON_TRN_LOGGER_SV__

