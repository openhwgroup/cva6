// Copyright 2024 Thales DIS SAS
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
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group

`ifndef __UVME_CVA6_FRONTEND_MODEL_SV__
`define __UVME_CVA6_FRONTEND_MODEL_SV__


// Return Address Stack class model
// The class contains a queue with a length equal to RASDepth to store the addresses of JALR instructions.
// The class provides a coverage model to cover all possible cases of push and pop operations.
class uvme_ras_sb_c extends uvm_scoreboard;

   // Objects
   uvme_cva6_cfg_c    cfg;

   // Address queue
   bit[RTLCVA6Cfg.VLEN-1:0]      ras_lifo[$];

   `uvm_component_utils_begin(uvme_ras_sb_c)
   `uvm_component_utils_end

   covergroup frontend_ras_cg with function sample(bit push_n_pop, int ras_size); //AZ
      push_ras_cp : coverpoint ras_size {
          bins push      = {[0:RTLCVA6Cfg.RASDepth-1]} iff(push_n_pop);
          bins push_full = {RTLCVA6Cfg.RASDepth} iff(push_n_pop);
      }
      pop_ras_cp : coverpoint ras_size { 
          bins pop       = {[1:RTLCVA6Cfg.RASDepth]} iff(!push_n_pop);
          bins pop_empty = {0} iff(!push_n_pop);
      }
   endgroup

   /**
    * Default constructor.
    */
   function new(string name="uvme_ras_sb", uvm_component parent=null);
         super.new(name, parent);
         frontend_ras_cg = new();
   endfunction

   /**
    * Create and configures RAS via:
    */
   virtual function void build_phase(uvm_phase phase);
      void'(uvm_config_db#(uvme_cva6_cfg_c)::get(this, "", "cfg", cfg));
         if (!cfg) begin
            `uvm_fatal("CFG", "Configuration handle is null")
         end
   endfunction

   /**
    * Push address to the RAS queue
    */
   virtual function void add_address(bit[RTLCVA6Cfg.VLEN-1:0] ret_address, bit enable);
      if(enable) begin
         frontend_ras_cg.sample(1, ras_lifo.size());
         if(ras_lifo.size() == RTLCVA6Cfg.RASDepth) begin
            ras_lifo.delete(0);
            ras_lifo.push_back(ret_address);
         end else begin
            ras_lifo.push_back(ret_address);
         end
      end
   endfunction

   /**
    * Pop address from the RAS queue
    */
   virtual function uvme_frontend_ras_t pop_address(bit enable);
      uvme_frontend_ras_t ras_predicted;

      if(enable) begin
         frontend_ras_cg.sample(0, ras_lifo.size());
         if(ras_lifo.size() > 0) begin
            ras_predicted.valid = '1;
            ras_predicted.predicted_address = ras_lifo[ras_lifo.size()-1];
            ras_lifo.delete(ras_lifo.size()-1);
         end else begin
            ras_predicted.valid = '0;
            ras_predicted.predicted_address = '0;
         end
      end else begin
         ras_predicted.valid = '0;
         ras_predicted.predicted_address = '0;
      end

      return ras_predicted;
   endfunction

   /**
    * Flush the RAS queue
    */
   virtual function bit[1:0] flush_ras();
      ras_lifo.delete();
   endfunction

endclass : uvme_ras_sb_c


// Branch History Table class model
// The class contains a two-dimensional table of addresses and index, with a length dependent on BHTDepth and INSTR_PER_FETCH.
// The table type includes a two-bit counter and the prediction status, indicating whether it is valid or not.
// The class provides a coverage model to cover all possible cases of BHT updates and branch predictions.
class uvme_bht_sb_c extends uvm_scoreboard;

   // Objects
   uvme_cva6_cfg_c    cfg;

   uvme_frontend_bht_t         branch_prediction[RTLCVA6Cfg.BHTEntries/RTLCVA6Cfg.INSTR_PER_FETCH][RTLCVA6Cfg.INSTR_PER_FETCH];

   `uvm_component_utils_begin(uvme_bht_sb_c)
   `uvm_component_utils_end
   
   covergroup frontend_bht_mispredict_cg with function sample(int update_pc, int update_row, int saturation); //AZ
      pc_cp        : coverpoint update_pc {
         bins pc[] = {[0:RTLCVA6Cfg.BHTEntries/RTLCVA6Cfg.INSTR_PER_FETCH-1]};
      }
      row_cp       : coverpoint update_row {
         bins pc[] = {[0:RTLCVA6Cfg.INSTR_PER_FETCH-1]};
      }
      saturation_cp : coverpoint saturation {
         bins pc[] = {[0:3]};
      }
      cross pc_cp, row_cp, saturation_cp;
   endgroup
   
   covergroup frontend_bht_predict_cg with function sample(bit prediction, bit taken); //AZ
     prediction_cp : coverpoint prediction;
     taken_cp      : coverpoint taken;
     cross prediction_cp, taken_cp;
   endgroup

   /**
    * Default constructor.
    */
   function new(string name="uvme_bht_sb", uvm_component parent=null);
         super.new(name, parent);
         frontend_bht_mispredict_cg = new();
         frontend_bht_predict_cg = new();
   endfunction

   /**
    * Create and configures BHT via:
    */
   virtual function void build_phase(uvm_phase phase);
      void'(uvm_config_db#(uvme_cva6_cfg_c)::get(this, "", "cfg", cfg));
         if (!cfg) begin
            `uvm_fatal("CFG", "Configuration handle is null")
         end
   endfunction

   /**
    * This function update the BHT table in case of valid mispredict in a branch
    * The function take in input the mispredict information provided by frontend and he recalculate the access address
    * The valid states of BHT boxes change if it's is the first time we access to an address
    * Updating the two bit counter by the successive execution of the instructions
    */
   virtual function void update_bht(uvme_frontend_bp_resolve_t bp);
      int      update_pc;
      int      update_row;
      int      upper_index;
      int      lower_index;
      int      index = 0;

      if(RTLCVA6Cfg.BHTEntries) begin
         upper_index = $clog2(RTLCVA6Cfg.BHTEntries / RTLCVA6Cfg.INSTR_PER_FETCH) + (RTLCVA6Cfg.RVC == 1'b1 ? 1 : 2) + $clog2(RTLCVA6Cfg.INSTR_PER_FETCH);
         lower_index = (RTLCVA6Cfg.RVC == 1'b1 ? 1 : 2) + $clog2(RTLCVA6Cfg.INSTR_PER_FETCH);
         for(int i = lower_index; i < upper_index; i++) begin
            update_pc[index]  = bp.pc[i];
            index++;
         end

         update_row = bp.pc[($clog2(RTLCVA6Cfg.INSTR_PER_FETCH) + (RTLCVA6Cfg.RVC == 1'b1 ? 1 : 2) - 1) :(RTLCVA6Cfg.RVC == 1'b1 ? 1 : 2)];
         branch_prediction[update_pc][update_row].valid = 1;

         if(branch_prediction[update_pc][update_row].saturation == 3) begin
            if(!bp.is_taken)
               branch_prediction[update_pc][update_row].saturation--;
         end else if(branch_prediction[update_pc][update_row].saturation == 0) begin
            if(bp.is_taken)
               branch_prediction[update_pc][update_row].saturation++;
         end else begin
            if(bp.is_taken)
               branch_prediction[update_pc][update_row].saturation++;
            else
               branch_prediction[update_pc][update_row].saturation--;
         end
         frontend_bht_mispredict_cg.sample(update_pc, update_row, branch_prediction[update_pc][update_row].saturation);
      end
   endfunction

   /**
    * This function provides the taken or not prediction.
    * The function take in input the address of fetch and he recalculate the access address, and instruction immediat.
    * The prediction is valid if the address is in the BHT if not the instruction immediat is used to provide the prediction
    */
   virtual function bit[1:0] bht_prediction(bit[RTLCVA6Cfg.VLEN-1:0] vpc ,bit[RTLCVA6Cfg.VLEN-1:0] imm, int index);
      bit[RTLCVA6Cfg.VLEN:0]  pc_index;
      int              pc_row;
      bit[1:0]         prediction; 
      int              upper_index;
      int              lower_index;
      int              index_pc;

      if(RTLCVA6Cfg.BHTEntries) begin
         upper_index = $clog2(RTLCVA6Cfg.BHTEntries / RTLCVA6Cfg.INSTR_PER_FETCH) + (RTLCVA6Cfg.RVC == 1'b1 ? 1 : 2) + $clog2(RTLCVA6Cfg.INSTR_PER_FETCH);
         lower_index = (RTLCVA6Cfg.RVC == 1'b1 ? 1 : 2) + $clog2(RTLCVA6Cfg.INSTR_PER_FETCH);
         index_pc = 0;
         for(int i = lower_index; i < upper_index; i++) begin
            pc_index[index_pc]  = vpc[i];
            index_pc++;
         end
         for(int i = 0; i < RTLCVA6Cfg.INSTR_PER_FETCH; i++) begin
         end
         pc_row   = vpc[1];
         if(branch_prediction[pc_index][index].valid) begin
            prediction[0] = 1;
         end
      end else begin
         prediction[0] = 0;
      end

      if(prediction[0] == 1) begin
         if(branch_prediction[pc_index][index].saturation[1])
            prediction[1] = 1;
      end else begin
         if(imm[RTLCVA6Cfg.VLEN-1] == 1)
            prediction[1] = 1;
         else
            prediction[1] = 0;
      end

      frontend_bht_predict_cg.sample(prediction[0], prediction[1]);
      return prediction;
   endfunction

   /**
    * Instanciate the BHT
    */
   virtual function bit[1:0] init_bht();
      for (int i = 0; i < (RTLCVA6Cfg.BHTEntries / RTLCVA6Cfg.INSTR_PER_FETCH); i++) begin
        for (int j = 0; j < RTLCVA6Cfg.INSTR_PER_FETCH; j++) begin
          branch_prediction[i][j].valid      = 1'b0;
          branch_prediction[i][j].saturation = 2'b00;
        end
      end
   endfunction

   /**
    * Flush the BHT
    */
   virtual function bit[1:0] flush_bht();
      for (int i = 0; i < (RTLCVA6Cfg.BHTEntries / RTLCVA6Cfg.INSTR_PER_FETCH); i++) begin
        for (int j = 0; j < RTLCVA6Cfg.INSTR_PER_FETCH; j++) begin
          branch_prediction[i][j].valid      = 1'b0;
          branch_prediction[i][j].saturation = 2'b10;
        end
      end
   endfunction

endclass : uvme_bht_sb_c


// Instruction queue class model
// The class contains a queue of instruction that is ready to be sent to the Decode.
// The queue type includes the instruction with the address of fetch and the type of prediction with the prediction address.
// The class contain the status of the instruction queue the check the capability to push the data, and the status of address queue to check capability to push the data in case of prediction.
// The queue can hold up to 4*INSTR_PER_FETCH data entries, including maximum two prediction addresses.
// The class provides a coverage model to cover all possible cases of push and pop operations.
class uvme_queue_sb_c extends uvm_scoreboard;

   // Objects
   uvme_cva6_cfg_c    cfg;

   uvme_frontend_fetched_data_t       data_queue[$];

   int              count_address; // counter of valid prediction address
   bit              instr_queue_available;
   bit              address_queue_available;
   bit              previous_prediction;
   int              instr_queue_depth;

   `uvm_component_utils_begin(uvme_queue_sb_c)
   `uvm_component_utils_end

   covergroup frontend_queue_cg with function sample(bit push_n_pop, int queue_size); //AZ
      push_queue_cp : coverpoint queue_size {
          bins push      = {[0:FETCH_FIFO_DEPTH * RTLCVA6Cfg.INSTR_PER_FETCH-1]} iff(push_n_pop);
          bins push_full = {FETCH_FIFO_DEPTH * RTLCVA6Cfg.INSTR_PER_FETCH} iff(push_n_pop);
      }
      pop_queue_cp : coverpoint queue_size { 
          bins pop       = {[1:FETCH_FIFO_DEPTH * RTLCVA6Cfg.INSTR_PER_FETCH]} iff(!push_n_pop);
          illegal_bins ILLEGAL_BINS = {0} iff(!push_n_pop);
      }
   endgroup

   /**
    * Default constructor.
    */
   function new(string name="uvme_queue_sb", uvm_component parent=null);
         super.new(name, parent);
         frontend_queue_cg = new();
   endfunction

   /**
    * Create and configures instr_queue via:
    */
   virtual function void build_phase(uvm_phase phase);
      instr_queue_depth = FETCH_FIFO_DEPTH * RTLCVA6Cfg.INSTR_PER_FETCH;
      void'(uvm_config_db#(uvme_cva6_cfg_c)::get(this, "", "cfg", cfg));
         if (!cfg) begin
            `uvm_fatal("CFG", "Configuration handle is null")
         end
   endfunction

   /**
    * Push instruction into the queue
    * Update instr_queue_available and address_queue_available
    */
   virtual function int update_queue(uvme_frontend_fetched_data_t instr);
      int valid_push;

      frontend_queue_cg.sample(1, data_queue.size());
      if(instr.predict) begin
         if(count_address < ADDRESS_FIFO_DEPTH && data_queue.size() < instr_queue_depth) begin
            data_queue.push_back(instr);
            valid_push = 1;
            count_address++;
         end else begin
            valid_push = -1;
         end
      end else begin
         if(data_queue.size() < instr_queue_depth) begin
            data_queue.push_back(instr);
            valid_push = 1;
         end else begin
            valid_push = -1;
         end
      end

      if(data_queue.size() > 1) begin
         if(previous_prediction) begin
            data_queue[data_queue.size()-1].address = data_queue[data_queue.size()-2].address + ((data_queue[data_queue.size()-2].instruction[1:0] != 3) ? 2 : 4);
         end
         if(data_queue[data_queue.size()-2].predict) begin
            data_queue[data_queue.size()-1].address = data_queue[data_queue.size()-2].predicted_address;
            previous_prediction = 1;
         end
      end

      if(count_address < ADDRESS_FIFO_DEPTH)
         address_queue_available = 1;
      else
         address_queue_available = 0;

      if(data_queue.size() < instr_queue_depth) begin
         instr_queue_available = 1;
      end else begin
         instr_queue_available = 0;
         address_queue_available = 0;
      end
      
      return valid_push;
   endfunction

   /**
    * Pop instruction from the queue
    * Update instr_queue_available and address_queue_available
    */
   virtual function uvme_frontend_fetched_data_t pop_instruction();
      uvme_frontend_fetched_data_t instr;

      frontend_queue_cg.sample(0, data_queue.size());
      if(data_queue.size() > 0) begin
         //instr = frontend_out.pop_front();
         instr = data_queue[0];
         data_queue.delete(0);
         if(instr.predict) begin
            count_address--;
         end
      end else begin
         `uvm_fatal(get_type_name(), "ERROR -> Zero instruction is ready to be send to decode")
      end

      if(count_address < ADDRESS_FIFO_DEPTH)
         address_queue_available = 1;
      else
         address_queue_available = 0;

      if(data_queue.size() < instr_queue_depth) begin
         instr_queue_available = 1;
      end else begin
         instr_queue_available = 0;
         address_queue_available = 0;
      end

      return instr;
   endfunction

   /**
    * Flush into the instruction queue
    */
   virtual function bit[1:0] flush_queue();
      data_queue.delete();
      count_address           = 0;
      instr_queue_available   = 1;
      address_queue_available = 1;
      previous_prediction     = 0;
   endfunction

endclass : uvme_queue_sb_c


// Frontend class model
// This class models the behavior of the frontend, providing the same frontend output and using the same input. It is also configurable with the same CVA6 parameters.
// The model contains all the components needed to calculate the instructions supplied to the Decode stage.
// It retrieves inputs from the monitor through an analysis port in the form of transactions, then aligns the instructions, pre-decodes them,
// calculates the prediction address if there is a branch or jump, and places the processed instructions in the queue.
// The model detects if a response is sent on the bus to the Decode stage and compares it with the first element in the queue.
// It also calculates the next PC, taking into account previous instructions and given input, and compares the calculated PC with the PC sent to the cache every cycle
class uvme_cva6_frontend_model_c extends uvm_scoreboard;

   // Objects
   uvme_cva6_cfg_c    cfg;
   
   //Handles to sequencer FIFOS
   uvm_tlm_analysis_fifo #(uvme_cva6_frontend_transaction_c)    mon2mod_fifo_port;

   //Handles to sequencer port connected to the FIFOS
   uvm_analysis_export   #(uvme_cva6_frontend_transaction_c)    mon2mod_export;

   uvme_bht_sb_c   bht_sb;
   uvme_ras_sb_c   ras_sb;
   uvme_queue_sb_c instr_queue_sb;

   logic[RTLCVA6Cfg.FETCH_WIDTH-1:0]     fetched_data;
   logic[RTLCVA6Cfg.VLEN-1:0]            fetched_address;
   bit[RTLCVA6Cfg.INSTR_PER_FETCH-1:0]   valid_fetch;
   bit[ILEN-1:0]                         valid_data[RTLCVA6Cfg.INSTR_PER_FETCH-1:0];
   bit[RTLCVA6Cfg.VLEN-1:0]              valid_address[RTLCVA6Cfg.INSTR_PER_FETCH-1:0];
   uvme_frontend_fetched_data_t          decode_entry;
   uvme_frontend_icache_rsp_t            cache_entry;
   logic[RTLCVA6Cfg.VLEN-1:0]            next_pc;
   logic[RTLCVA6Cfg.VLEN-1:0]            next_predicted_address;
   int                                   valid_push;
   int                                   bp_valid;
   int                                   next_bp_valid;
   int                                   next_kill_s1 = 0;
   int                                   next_kill_s2 = 0;
   
   bit                       unalined_access;
   bit[RTLCVA6Cfg.VLEN-1:0]  unaligned_address;
   bit[ILEN-1:0]             unaligned_data;
   
   uvme_cva6_frontend_transaction_c   frontend_transaction;  // transaction sent by the monitor

   // JR compressed instruction
   bit rvc_jr[RTLCVA6Cfg.INSTR_PER_FETCH];
   // -1 : compressed / 0 : not / 1 : not compressed
   // Branch compressed instruction
   int branch[RTLCVA6Cfg.INSTR_PER_FETCH];
   // Unconditional jump compressed instruction
   int jump[RTLCVA6Cfg.INSTR_PER_FETCH];
   // Return compressed instruction
   int ret[RTLCVA6Cfg.INSTR_PER_FETCH];
   // JALR compressed instruction
   int jalr[RTLCVA6Cfg.INSTR_PER_FETCH];
   // JAL compressed instruction
   int call[RTLCVA6Cfg.INSTR_PER_FETCH];
   // Instruction compressed immediat
   bit [RTLCVA6Cfg.VLEN:0] rvc_imm[RTLCVA6Cfg.INSTR_PER_FETCH];
   // Instruction compressed immediat
   bit [RTLCVA6Cfg.VLEN:0] rvi_imm[RTLCVA6Cfg.INSTR_PER_FETCH];

   bit[1:0]         bht_bp;
   bit              resolve_aligned;

   `uvm_component_utils_begin(uvme_cva6_frontend_model_c)
   `uvm_component_utils_end

   covergroup frontend_decode_cg with function sample(uvme_frontend_fetched_data_t decode_entry);
     addr_cp            : coverpoint decode_entry.address[2:1];

     compressed_cp      : coverpoint decode_entry.instruction[1:0] {
        bins compressed   = {[0:2]};
        bins Ncompressed  = {3};
     }

     predict_cp         : coverpoint decode_entry.predict {
        ignore_bins IGN_BINS     = {3} iff(!RTLCVA6Cfg.BTBEntries);
     }

     cross addr_cp, compressed_cp, predict_cp;
   endgroup

   covergroup frontend_flush_cg with function sample(bit flush, bit flush_bp); //AZ
      flush_cp: coverpoint flush;
      // Not Supported By CVA6
      // flush_bp_cp : coverpoint flush_bp;
      // cross flush_cp, flush_bp_cp;
   endgroup

   covergroup frontend_cache_cg with function sample(uvme_cva6_frontend_transaction_c  frontend_transaction, bit bp_valid, bit replay_addr);

     reset           : coverpoint frontend_transaction.boot_valid;
     prediction      : coverpoint bp_valid;
     Default         : coverpoint frontend_transaction.icache_req.ready && frontend_transaction.icache_rsp.req;
     replay_request  : coverpoint replay_addr;
     mispredict      : coverpoint (frontend_transaction.resolve_branch.valid && frontend_transaction.resolve_branch.is_mispredict);
     env_call        : coverpoint frontend_transaction.eret;
     interrupt       : coverpoint frontend_transaction.ex_valid;
     pipeline_flush  : coverpoint frontend_transaction.set_pc_commit;
     Debug           : coverpoint frontend_transaction.set_debug_pc {
        ignore_bins IGN_BINS     = {1} iff(!RTLCVA6Cfg.DebugEn);
     }

     cross reset, prediction, Default, replay_request, mispredict, env_call, interrupt, pipeline_flush, Debug;
   endgroup

   covergroup frontend_execut_cg with function sample(uvme_cva6_frontend_transaction_c  frontend_transaction);

     bht_mispredict  : coverpoint (frontend_transaction.resolve_branch.cf_type == 1);

     ras_mispredict  : coverpoint (frontend_transaction.resolve_branch.cf_type == 4);

     taken           : coverpoint frontend_transaction.resolve_branch.is_taken;

     mispredict      : coverpoint frontend_transaction.resolve_branch.is_mispredict;

     cross bht_mispredict, mispredict, taken {
        ignore_bins IGN_BINS     = binsof(bht_mispredict) intersect{0} &&
                              binsof(taken) intersect{0};
     }

     cross ras_mispredict, mispredict;
   endgroup

   /**
    * Default constructor.
    */
   function new(string name="uvme_cva6_frontend_model_c", uvm_component parent=null);
         super.new(name, parent);
         frontend_decode_cg = new();
         frontend_flush_cg  = new();
         frontend_cache_cg  = new();
         frontend_execut_cg = new();
   endfunction

   /**
    * Create and configures sub-Frontend via:
    */
   virtual function void build_phase(uvm_phase phase);

      void'(uvm_config_db#(uvme_cva6_cfg_c)::get(this, "", "cfg", cfg));
      if (!cfg)
         `uvm_fatal("CFG", "Configuration handle is null")

      this.mon2mod_fifo_port   = new("mon2mod_fifo_port", this);
      this.mon2mod_export      = new("mon2mod_export", this);

      instr_queue_sb = uvme_queue_sb_c::type_id::create("instr_queue_sb", this);
      bht_sb         = uvme_bht_sb_c::type_id::create("bht_sb", this);

      if (RTLCVA6Cfg.RASDepth != 0) begin
         ras_sb         = uvme_ras_sb_c::type_id::create("ras_sb", this);
      end

   endfunction

   /**
    * Connect get ports to FIFO get peek_export ports
    */
   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      // Connect get ports to FIFO get peek_export ports
      this.mon2mod_export.connect(this.mon2mod_fifo_port.analysis_export);
   endfunction

   /**
    * Frontend run phase.
    * instantiate all the component.
    * Start geting transaction from monitor.
    */
   task run_phase(uvm_phase phase);
      super.run_phase(phase);
      instr_queue_sb.flush_queue();
      bht_sb.init_bht();
      if (RTLCVA6Cfg.RASDepth != 0) begin
         ras_sb.flush_ras();
      end
      forever begin
         modeling_frontend_module();
      end
   endtask

   task modeling_frontend_module();

      mon2mod_fifo_port.get(frontend_transaction);
      check_decode_req_out();
      misprediction();
      receive_frontend_input();
      perform_cache_entry();
      check_cache_req_out();

   endtask

   /**
    * Fetch Stage flow
    * Decide which function will handle the alignment.
    * Pre-decode only the valid instructions, prepare the instruction with all related prediction information
    * Push all the valid instruction into the queue.
    */
   task receive_frontend_input();
      bit[RTLCVA6Cfg.VLEN-1:0]  predicted_address;
      bit[RTLCVA6Cfg.VLEN-1:0]  ras_addr;
      uvme_frontend_ras_t       ras_prediction;
      bit[1:0]           branch_predict;
      int branch_index;

      if(RTLCVA6Cfg.FETCH_WIDTH == 32)
         align_fetched_data_32();
      else
         align_fetched_data_64();

      decode_entry = '0;

      for(int i = 0; i < RTLCVA6Cfg.INSTR_PER_FETCH; i++) begin
         if(i != 0 && decode_entry.predict != 0) begin
            for(int j = i; j < RTLCVA6Cfg.INSTR_PER_FETCH; j++) begin
               valid_fetch[j] = 0;
            end
         end
         frontend_decode_instr(i, valid_data[i]);
         // if there is a JUMP we change the prediction type and the prediction address equal to the fetch address + instruction immediat
         if(jump[i] != 0) begin
           decode_entry.predict = Jump;
           if(jump[i] == 1) predicted_address = valid_address[i] + rvi_imm[i];
           else if (jump[i] == -1) predicted_address = valid_address[i] + rvc_imm[i];
         end
         // if there is a RET we change the prediction type and the prediction address is poped from the RAS. if the RAS is empty prediction address equal to 0
         else if(ret[i] != 0) begin
            decode_entry.predict = Return;
            if(RTLCVA6Cfg.RASDepth && valid_fetch[i]) begin
               ras_prediction = ras_sb.pop_address(instr_queue_sb.address_queue_available);
               predicted_address = ras_prediction.predicted_address;
            end
         end
         // if there is a BRANCH we check if there is an outstanding unaligned access or not to see whish address we will use
         else if(branch[i] != 0) begin
            // if the access is not aligned we use the address of the first access to calculate the prediction
            if(resolve_aligned && valid_fetch[i]) begin
               if(bht_bp[0] == 1) decode_entry.predict = (bht_bp[1] == 1) ? 1 : 0;
               else decode_entry.predict = (rvi_imm[i][RTLCVA6Cfg.VLEN-1] == 1) ? 1 : 0;
               predicted_address = valid_address[i] + ((decode_entry.predict == 1) ? rvi_imm[i] : 0);
            // if the access is aligned we use the current address to calculate the prediction
            end else begin
               branch_index = valid_address[i][$clog2(RTLCVA6Cfg.INSTR_PER_FETCH):1];
               if(valid_data[i][1:0] != 3) begin
                  branch_predict = bht_sb.bht_prediction(fetched_address ,rvc_imm[i], branch_index);
                  predicted_address = valid_address[i] + ((branch_predict[1] == 1) ? rvc_imm[i] : 0);
               end else begin
                  branch_predict = bht_sb.bht_prediction(fetched_address, rvi_imm[i], branch_index);
                  predicted_address = valid_address[i] + ((branch_predict[1] == 1) ? rvi_imm[i] : 0);
               end
               decode_entry.predict = (branch_predict[1] == 1) ? 1 : 0;
               if(unalined_access) begin
                  bht_bp = branch_predict;
               end
            end
         end
         // TODO : Jalr is not supported
         else if(jalr[i] != 0 && RTLCVA6Cfg.BTBEntries) begin
            decode_entry.predict = JumpR;
         end
         else begin
            decode_entry.predict = NoCF;
            predicted_address = 0;
         end
         // If there is a CALL we push the fetch address into the RAS
         if(call[i] != 0 && valid_fetch[i] && RTLCVA6Cfg.RASDepth) begin
            ras_addr = valid_address[i] + ((call[i] == -1) ? 2 : 4);
            ras_sb.add_address(ras_addr, instr_queue_sb.address_queue_available);
         end

         // Push the instruction type in to the instruction queue
         if(valid_fetch[i]) begin            
            resolve_aligned = 0;
            decode_entry.predicted_address = predicted_address;
            decode_entry.address = valid_address[i];
            decode_entry.instruction = valid_data[i];
            valid_push = instr_queue_sb.update_queue(decode_entry);
            frontend_decode_cg.sample(decode_entry);
            
            if((decode_entry.predict != 0 && decode_entry.predict != 4) || (decode_entry.predict == 4 && ras_prediction.valid)) begin
               next_bp_valid = 1;
               next_kill_s2 = 1;
            end
            if(valid_push == -1) begin
               next_kill_s1 = 1;
               break;
            end
         end
      end
      for(int i = 0; i < RTLCVA6Cfg.INSTR_PER_FETCH; i++) begin
         valid_fetch[i]   = 0;
         valid_data[i]    = 0;
         valid_address[i] = 0;
      end
      flush_frontend();
      if(cache_entry.kill_s1) begin
         cache_entry.kill_s2 = 1;
      end

   endtask : receive_frontend_input

   /**
    * Flush the frontend sub-moduls
    */
   function void flush_frontend();

      if(frontend_transaction.flush) begin
         instr_queue_sb.flush_queue();
         cache_entry.kill_s1 = 1;
      end

      if(frontend_transaction.flush_bp) begin
         if (RTLCVA6Cfg.RASDepth != 0) begin
            ras_sb.flush_ras();
         end
         bht_sb.flush_bht();
      end
      frontend_flush_cg.sample(frontend_transaction.flush, frontend_transaction.flush_bp);

   endfunction : flush_frontend

   /**
    * Detect misprediction to update the BHT
    */
   function void misprediction();

      if(frontend_transaction.resolve_branch.valid) begin
         frontend_execut_cg.sample(frontend_transaction);
         if(frontend_transaction.resolve_branch.is_mispredict) begin
            cache_entry.kill_s1 = 1;
         end
         if(frontend_transaction.resolve_branch.cf_type == 1) begin
            bht_sb.update_bht(frontend_transaction.resolve_branch);
         end
      end

   endfunction : misprediction

   /**
    * PC Gen flow
    * Calculate the next PC each clock cycle
    */
   function void perform_cache_entry();
      bit replay;

      replay = (valid_push == -1);
      if (frontend_transaction.boot_valid == 1) begin
         next_pc           = cfg.boot_addr;
         cache_entry.vaddr = cfg.boot_addr;
      end else begin
         cache_entry.vaddr = next_pc;
      end

      // 0. Branch Prediction
      if (bp_valid) begin
         next_pc = next_predicted_address;
         cache_entry.vaddr = next_predicted_address;
      end
      // 1. Default assignment
      if (frontend_transaction.icache_req.ready && frontend_transaction.icache_rsp.req) begin
         next_pc = {
           cache_entry.vaddr[RTLCVA6Cfg.VLEN-1:RTLCVA6Cfg.FETCH_ALIGN_BITS] + 1, {RTLCVA6Cfg.FETCH_ALIGN_BITS{1'b0}}
         };
      end
      // 2. Replay instruction fetch
      if (replay) begin
         next_pc = decode_entry.address;
         valid_push = 0;
      end
      // 3. Mispredict
      if (frontend_transaction.resolve_branch.valid && frontend_transaction.resolve_branch.is_mispredict)
         next_pc = frontend_transaction.resolve_branch.target_address;
      // 4. Return from environment call
      if (frontend_transaction.eret)
         next_pc = frontend_transaction.epc;
      // 5. Exception/Interrupt
      if (frontend_transaction.ex_valid)
         next_pc = frontend_transaction.trap_vector_base;
      // 6. Pipeline Flush
      if (frontend_transaction.set_pc_commit)
         next_pc = frontend_transaction.pc_commit + (frontend_transaction.halt ? '0 : {{RTLCVA6Cfg.VLEN - 3{1'b0}}, 3'b100});
      // 7. Debug
      if (RTLCVA6Cfg.DebugEn && frontend_transaction.set_debug_pc)
         next_pc = RTLCVA6Cfg.DmBaseAddress[RTLCVA6Cfg.VLEN-1:0] + RTLCVA6Cfg.HaltAddress[RTLCVA6Cfg.VLEN-1:0];

      frontend_cache_cg.sample(frontend_transaction, bp_valid, replay);
      bp_valid = 0;

   endfunction : perform_cache_entry

   /**
    * Compare the instruction sent to the Decode with the two first instruction poped from the instruction queue
    */
   function void check_decode_req_out();
      uvme_frontend_fetched_data_t   frontend_output;

      for(int i = 0; i < RTLCVA6Cfg.NrIssuePorts; i++) begin
         if(frontend_transaction.fetch_valid[i] && frontend_transaction.fetch_ready[i]) begin
            frontend_output = instr_queue_sb.pop_instruction();
            if(frontend_output.address != frontend_transaction.fetch_instr[i].address) `uvm_error(get_type_name(), "ERROR -> Wrong address")
            if(frontend_output.instruction != frontend_transaction.fetch_instr[i].instruction) `uvm_error(get_type_name(), "ERROR -> Wrong instruction")
            if(frontend_transaction.fetch_instr[i].predict != 0 && frontend_output.predicted_address != frontend_transaction.fetch_instr[i].predicted_address) `uvm_error(get_type_name(), "ERROR -> Wrong predicted address")
            if(frontend_output.predict != frontend_transaction.fetch_instr[i].predict) `uvm_error(get_type_name(), "ERROR -> Wrong prediction")
         end
      end

   endfunction : check_decode_req_out

   /**
    * Check the next PC and all the information performed by the Frontend
    */
   function void check_cache_req_out();

      if(cache_entry.kill_s1 != frontend_transaction.icache_rsp.kill_s1)   `uvm_error(get_type_name(), "ERROR -> the frontend sent wrong kill_s1")
      if(cache_entry.kill_s2 != frontend_transaction.icache_rsp.kill_s2)   `uvm_error(get_type_name(), "ERROR -> the frontend sent wrong kill_s2")
      if(frontend_transaction.icache_rsp.req) begin
         if(cache_entry.vaddr   != frontend_transaction.icache_rsp.vaddr)     `uvm_error(get_type_name(), "ERROR -> the frontend sent wrong npc")
      end

      cache_entry.kill_s1 = next_kill_s1;
      cache_entry.kill_s2 = next_kill_s2;
      bp_valid = next_bp_valid;
      next_predicted_address = decode_entry.predicted_address;
      next_kill_s1 = 0;
      next_kill_s2 = 0;
      next_bp_valid = 0;

   endfunction : check_cache_req_out

   /**
    * Decode the instruction if it's compressed or not
    * calculate to instruction immediat
    */
   function void frontend_decode_instr(int i, bit[31:0] instr);
      bit[RTLCVA6Cfg.VLEN-1:0] uj_imm, sb_imm;
      if(instr[1:0] == 2'b11) begin
         branch[i] = (instr[6:0] == 7'b11_000_11) ? 1 : 0;
         jalr[i]   = (instr[6:0] == 7'b11_001_11) ? 1 : 0;
         jump[i]   = ((instr[6:0] == 7'b11_011_11) | (instr[31:30] == 2'b00 & instr[28:0] == 29'b10000001000000000000001110011)) ? 1 : 0;
         ret[i] = ((jalr[i] == 1) & ((instr[19:15] == 5'd1) | instr[19:15] == 5'd5) & (instr[19:15] != instr[11:7])) ? 1 : 0;
         call[i]   = ((jalr[i] == 1 | jump[i] == 1) & ((instr[11:7] == 5'd1) | instr[11:7] == 5'd5)) ? 1 : 0;

         uj_imm = {{44 + RTLCVA6Cfg.VLEN - 64{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
         sb_imm = {{51 + RTLCVA6Cfg.VLEN - 64{instr[31]}}, instr[31], instr[7],  instr[30:25], instr[11:8], 1'b0};
         rvi_imm[i]= (instr[31:30] == 2'b00 & instr[28:0] == 29'b10000001000000000000001110011) ? '0 : (instr[3]) ? uj_imm : sb_imm;
      end else begin
         jump[i]   = (((instr[15:13] == 3'b101) & (instr[1:0] == 2'b01)) | ((RTLCVA6Cfg.XLEN == 32) & ((instr[15:13] == 3'b001) & (instr[1:0] == 2'b01)))) ? -1 : 0;
         rvc_jr[i] = ((instr[15:13] == 3'b100) & (instr[6:2] == 5'b00000) & (instr[1:0] == 2'b10) & ~instr[12]) ? 1 : 0;
         jalr[i]   = ((instr[15:13] == 3'b100) & (instr[6:2] == 5'b00000) & (instr[1:0] == 2'b10) & instr[12]) ? -1 : 0;
         call[i]   = ((jalr[i] == -1) | ((RTLCVA6Cfg.XLEN == 32) & ((instr[15:13] == 3'b001) & (instr[1:0] == 2'b01)))) ? -1 : 0;
         branch[i] = (((instr[15:13] == 3'b110) | (instr[15:13] == 3'b111)) & (instr[1:0] == 2'b01))? -1 : 0;
         ret[i] = (((instr[11:7] == 5'd1) | (instr[11:7] == 5'd5)) & rvc_jr[i]) ? -1 : 0;
         rvc_imm[i]= (instr[14]) ? {{(56+RTLCVA6Cfg.VLEN-64){instr[12]}}, instr[6:5], instr[2], instr[11:10], instr[4:3], 1'b0}
                                   : {{(53+RTLCVA6Cfg.VLEN-64){instr[12]}}, instr[8], instr[10:9], instr[6], instr[7], instr[2], instr[11], instr[5:3], 1'b0};
      end

   endfunction : frontend_decode_instr

   /**
    * Detect the valid instruction from the fetched data (32 bits)
    */
   function void align_fetched_data_32();

      if(frontend_transaction.icache_rsp.kill_s2) begin
         unalined_access = 0;
      end else if(frontend_transaction.icache_req.valid) begin
         fetched_address = frontend_transaction.icache_req.vaddr;
         fetched_data = frontend_transaction.icache_req.data >> {fetched_address[$clog2(RTLCVA6Cfg.INSTR_PER_FETCH):1], 4'b0};
         if(unalined_access) begin
            valid_fetch[0]   = 1;
            valid_fetch[1]   = 0;
            valid_data[0]    = {fetched_data[15:0], unaligned_data[15:0]};
            valid_data[1]    = 0;
            valid_address[0] = unaligned_address;
            valid_address[1] = {fetched_address[31:2], 2'b10};
            unalined_access = 0;
            if(fetched_address[1]) begin
               if(fetched_data[1:0] != 3) begin
                  valid_fetch = 2'b01;
               end else begin
                  valid_fetch = '0;
                  unalined_access = 1;
                  unaligned_address = {fetched_address[31:2], 2'b10};
                  unaligned_data    = fetched_data[15:0];
                  valid_data[1]     = {'0, unaligned_data[15:0]};
               end
            end else begin
               if(fetched_data[17:16] != 3) begin
                  unalined_access = 0;
                  valid_fetch[1]  = 1;
                  valid_data[1]   = {16'b0, fetched_data[31:16]};
               end else begin
                  unalined_access = 1'b1;
                  unaligned_data = fetched_data[31:16];
                  unaligned_address = {fetched_address[31:2], 2'b10};
                  valid_data[1]    = {'0, unaligned_data[15:0]};
               end
            end
            resolve_aligned = 1;
         end else begin
            valid_fetch[0]   = 1;
            valid_fetch[1]   = 0;
            valid_data[0]    = fetched_data;
            valid_data[1]    = 0;
            valid_address[0] = fetched_address;
            valid_address[1] = {fetched_address[31:2], 2'b10};
            if(fetched_address[1]) begin
               if(fetched_data[1:0] != 3) begin
                  valid_fetch = 2'b01;
               end else begin
                  valid_fetch = '0;
                  unalined_access = 1;
                  unaligned_address = {fetched_address[31:2], 2'b10};
                  unaligned_data = fetched_data[15:0];
                  valid_data[1]    = {'0, unaligned_data[15:0]};
               end
            end else begin
               if(fetched_data[1:0] != 3) begin
                  if(fetched_data[17:16] != 3) begin
                     unalined_access = 0;
                     valid_fetch[1]  = 1;
                     valid_data[1]   = {16'b0, fetched_data[31:16]};
                  end else begin
                     unalined_access = 1'b1;
                     unaligned_data = fetched_data[31:16];
                     unaligned_address = {fetched_address[31:2], 2'b10};
                     valid_data[1]    = {'0, unaligned_data[15:0]};
                  end
               end
            end
         end
      end
   endfunction : align_fetched_data_32

   /**
    * Detect the valid instruction from the fetched data (64 bits)
    */
   function void align_fetched_data_64();

      if(frontend_transaction.icache_rsp.kill_s2) begin
         unalined_access = 0;
      end else if(frontend_transaction.icache_req.valid) begin
	     fetched_address   = frontend_transaction.icache_req.vaddr;
         fetched_data      = frontend_transaction.icache_req.data >> {fetched_address[$clog2(RTLCVA6Cfg.INSTR_PER_FETCH):1], 4'b0};
         valid_fetch       = '0;
         valid_data[0]     = '0;
         valid_address[0]  = '0;
         valid_data[1]     = '0;
         valid_address[1]  = '0;
         valid_data[2]     = '0;
         valid_address[2]  = '0;
         valid_data[3]     = {16'b0, fetched_data[63:48]};
         valid_address[3]  = {fetched_address[31:3], 3'b110};

         case (fetched_address[2:1])
           2'b00: begin
             valid_fetch[0]  = 1;
             valid_fetch[1]  = 1;
             if (unalined_access) begin
               resolve_aligned = 1;

               valid_data[0] = {fetched_data[15:0], unaligned_data[15:0]};
               valid_address[0]  = unaligned_address;

               valid_data[1] = fetched_data[47:16];
               valid_address[1]  = {fetched_address[31:3], 3'b010};

               if (fetched_data[17:16] != 3) begin
                 valid_data[2] = fetched_data[63:32];
                 valid_address[2]  = {fetched_address[31:3], 3'b100};
                 valid_fetch[2] = 1;

                 if (fetched_data[33:32] != 3) begin
                   if (fetched_data[49:48] != 3) begin
                     unalined_access = 1'b0;
                     valid_fetch[3]  = 1;
                   end else begin
                     unaligned_data   = valid_data[3];
                     unaligned_address = valid_address[3];
                   end
                 end else begin
                   unalined_access = 1'b0;
                 end
               end else begin
                 valid_data[2] = valid_data[3];
                 valid_address[2]  = valid_address[3];
                 if (fetched_data[49:48] != 3) begin
                   unalined_access = 1'b0;
                   valid_fetch[2]  = 1;
                 end else begin
                   unaligned_data   = valid_data[3];
                   unaligned_address = valid_address[3];
                 end
               end
             end else begin
               valid_data[0] = fetched_data[31:0];
               valid_address[0]  = fetched_address;

               if (fetched_data[1:0] != 3) begin
                 valid_data[1] = fetched_data[47:16];
                 valid_address[1]  = {fetched_address[31:3], 3'b010};
                 if (fetched_data[17:16] != 3) begin
                   valid_data[2] = fetched_data[63:32];
                   valid_address[2]  = {fetched_address[RTLCVA6Cfg.VLEN-1:3], 3'b100};
                   valid_fetch[2] = 1;

                   if (fetched_data[33:32] != 3) begin
                     if (fetched_data[49:48] != 3) begin
                       valid_fetch[3] = 1;
                     end else begin
                       unalined_access         = 1'b1;
                       unaligned_data   = valid_data[3];
                       unaligned_address = valid_address[3];
                     end
                   end
                 end else begin
                   valid_data[2] = valid_data[3];
                   valid_address[2]  = valid_address[3];

                   if (fetched_data[49:48] != 3) begin
                     valid_fetch[2] = 1;
                   end else begin
                     unalined_access         = 1'b1;
                     unaligned_data   = valid_data[3];
                     unaligned_address = valid_address[3];
                   end
                 end
               end else begin
                 valid_data[1] = fetched_data[63:32];
                 valid_address[1]  = {fetched_address[31:3], 3'b100};

                 valid_data[2] = valid_data[3];
                 valid_address[2]  = valid_address[3];

                 if (fetched_data[33:32] != 3) begin
                   if (fetched_data[49:48] != 3) begin
                     valid_fetch[2] = 1;
                   end else begin
                     unalined_access         = 1'b1;
                     unaligned_data   = valid_data[3];
                     unaligned_address = valid_address[3];
                   end
                 end
               end
             end
           end
           2'b01: begin

             valid_data[0] = fetched_data[31:0];
             valid_address[0]  = {fetched_address[31:3], 3'b010};
             valid_fetch[0] = 1;
	     
             valid_data[2] = fetched_data[63:32];
             valid_address[2]  = {fetched_address[31:3], 3'b110};
	     
             if (fetched_data[1:0] != 3) begin
               valid_data[1] = fetched_data[47:16];
               valid_address[1]  = {fetched_address[31:3], 3'b100};
               valid_fetch[1] = 1;
	     
               if (fetched_data[17:16] != 3) begin
                 if (fetched_data[33:32] != 3) begin
                   valid_fetch[2] = 1;
                 end else begin
                   unalined_access         = 1'b1;
                   unaligned_data   = valid_data[2];
                   unaligned_address = valid_address[2];
                 end
               end
             end else begin
               valid_data[1] = valid_data[2];
               valid_address[1]  = valid_address[2];
	     
               if (fetched_data[33:32] != 3) begin
                 valid_fetch[1] = 1;
               end else begin
                 unalined_access         = 1'b1;
                 unaligned_data   = valid_data[2];
                 unaligned_address = valid_address[2];
               end
             end
           end
           2'b10: begin

             valid_data[0] = fetched_data[31:0];
             valid_address[0]  = {fetched_address[31:3], 3'b100};
             valid_fetch[0] = 1;
	     
             valid_data[1] = fetched_data[47:16];
             valid_address[1]  = {fetched_address[31:3], 3'b110};
	     
             if (fetched_data[1:0] != 3) begin
               if (fetched_data[17:16] != 3) begin
                 valid_fetch[1] = 1;
               end else begin
                 unalined_access         = 1'b1;
                 unaligned_data   = valid_data[1];
                 unaligned_address = valid_address[1];
               end
             end
           end
           2'b11: begin
             valid_data[0] = fetched_data[31:0];
             valid_address[0]  = {fetched_address[31:3], 3'b110};
             if (fetched_data[1:0] != 3) begin
               valid_fetch[0] = 1;
             end else begin
               unalined_access         = 1'b1;
               unaligned_data   = valid_data[0];
               unaligned_address = valid_address[0];
             end
           end
         endcase
      end

   endfunction : align_fetched_data_64

endclass : uvme_cva6_frontend_model_c

`endif // __UVME_CVA6_FRONTEND_MODEL_SV__

