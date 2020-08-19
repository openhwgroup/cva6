// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVME_CV32_INTERRUPT_NOISE_SV__
`define __UVME_CV32_INTERRUPT_NOISE_SV__

/**
 * Virtual sequence responsible for starting the system clock and issuing
 * the initial reset pulse to the DUT.
 */
class uvme_cv32_interrupt_noise_c extends uvme_cv32_base_vseq_c;

   rand int unsigned short_delay_wgt;
   rand int unsigned med_delay_wgt;
   rand int unsigned long_delay_wgt;
   rand bit [31:0]   reserved_irq_mask;

   `uvm_object_utils_begin(uvme_cv32_interrupt_noise_c)
   `uvm_object_utils_end
   
   constraint default_delay {
     soft short_delay_wgt == 1;
     soft med_delay_wgt == 4;
     soft long_delay_wgt == 3;
   }

   constraint valid_delay {
     short_delay_wgt != 0 || med_delay_wgt != 0 || long_delay_wgt != 0;
   }

   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32_interrupt_noise");
   
   /**
    * Starts the clock, waits, then resets the DUT.
    */
   extern virtual task body();
   extern virtual task rand_delay();
endclass : uvme_cv32_interrupt_noise_c

function uvme_cv32_interrupt_noise_c::new(string name="uvme_cv32_interrupt_noise");
   
   super.new(name);
   
endfunction : new

task uvme_cv32_interrupt_noise_c::rand_delay();
  randcase
    short_delay_wgt: #($urandom_range(1_000,1));
    med_delay_wgt: #($urandom_range(10_000,1_000));    
    long_delay_wgt: #($urandom_range(50_000,10_000));
  endcase 
endtask : rand_delay

task uvme_cv32_interrupt_noise_c::body();
  #1us;
  
  fork 
    while(1) begin
      uvma_interrupt_seq_item_c irq_req;
      
      `uvm_do_on_with(irq_req, p_sequencer.interrupt_sequencer, {
        action        == UVMA_INTERRUPT_SEQ_ITEM_ACTION_ASSERT_UNTIL_ACK;
        repeat_count dist { 0 :/ 9, [2:3] :/ 1 };
        (irq_mask & local::reserved_irq_mask) == 0;
      });

      rand_delay();      
    end  
  
    while(1) begin
      uvma_interrupt_seq_item_c irq_req;
      
      `uvm_do_on_with(irq_req, p_sequencer.interrupt_sequencer, {        
        action        == UVMA_INTERRUPT_SEQ_ITEM_ACTION_DEASSERT;
        (irq_mask & local::reserved_irq_mask) == 0;
      })   

      rand_delay();
    end  
  join
endtask : body

`endif // __UVME_CV32_INTERRUPT_NOISE_SV__
