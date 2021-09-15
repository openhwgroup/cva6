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


`ifndef __UVME_CV32E40X_INTERRUPT_NOISE_SV__
`define __UVME_CV32E40X_INTERRUPT_NOISE_SV__

/**
 * Virtual sequence responsible for starting the system clock and issuing
 * the initial reset pulse to the DUT.
 */
class uvme_cv32e40x_interrupt_noise_c extends uvme_cv32e40x_base_vseq_c;

   rand int unsigned short_delay_wgt;
   rand int unsigned med_delay_wgt;
   rand int unsigned long_delay_wgt;
   rand int unsigned initial_delay_assert_until_ack;
   rand int unsigned initial_delay_assert;
   rand int unsigned initial_delay_deassert;

   rand bit [31:0]   reserved_irq_mask;

   `uvm_object_utils_begin(uvme_cv32e40x_interrupt_noise_c)
   `uvm_object_utils_end

   constraint default_delay_c {
     soft short_delay_wgt == 2;
     soft med_delay_wgt == 5;
     soft long_delay_wgt == 3;
   }

   constraint valid_delay_c {
     short_delay_wgt != 0 || med_delay_wgt != 0 || long_delay_wgt != 0;
   }

   constraint valid_initial_delay_assert_until_ack_c {
     initial_delay_assert_until_ack dist { 0 :/ 1,
                                           [10:500] :/ 4,
                                           [500:1000] :/ 3};
   }

   constraint valid_initial_delay_assert_c {
     initial_delay_assert dist { 0 :/ 2,
                                 [10:500] :/ 4,
                                 [500:1000] :/ 3};
   }

   constraint valid_initial_delay_deassert_c {
     initial_delay_deassert dist { 0 :/ 2,
                                   [10:500] :/ 4,
                                   [500:1000] :/ 3};
   }

   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40x_interrupt_noise");

   /**
    * Starts the clock, waits, then resets the DUT.
    */
   extern virtual task body();
   extern virtual task rand_delay();
endclass : uvme_cv32e40x_interrupt_noise_c

function uvme_cv32e40x_interrupt_noise_c::new(string name="uvme_cv32e40x_interrupt_noise");

   super.new(name);

endfunction : new

task uvme_cv32e40x_interrupt_noise_c::rand_delay();
  randcase
    short_delay_wgt: repeat($urandom_range(100,1)) @(cntxt.interrupt_cntxt.vif.drv_cb);
    med_delay_wgt: repeat($urandom_range(500,100)) @(cntxt.interrupt_cntxt.vif.drv_cb);
    long_delay_wgt: repeat($urandom_range(10_000,5_000)) @(cntxt.interrupt_cntxt.vif.drv_cb);
  endcase
endtask : rand_delay

task uvme_cv32e40x_interrupt_noise_c::body();

  fork
    begin : gen_assert_until_ack

      repeat (initial_delay_assert_until_ack) @(cntxt.interrupt_cntxt.vif.drv_cb);

      while(1) begin
        uvma_interrupt_seq_item_c irq_req;

        `uvm_create_on(irq_req, p_sequencer.interrupt_sequencer);
        start_item(irq_req);
        irq_req.default_repeat_count_c.constraint_mode(0);
        assert(irq_req.randomize() with {
          action        == UVMA_INTERRUPT_SEQ_ITEM_ACTION_ASSERT_UNTIL_ACK;
          repeat_count dist { 1 :/ 9, [2:3] :/ 1 };

          (irq_mask & local::reserved_irq_mask) == 0;
        });
        finish_item(irq_req);

        rand_delay();

      end
    end

    begin : gen_assert

      repeat (initial_delay_assert) @(cntxt.interrupt_cntxt.vif.drv_cb);

      while(1) begin
        uvma_interrupt_seq_item_c irq_req;

        `uvm_do_on_with(irq_req, p_sequencer.interrupt_sequencer, {
          action        == UVMA_INTERRUPT_SEQ_ITEM_ACTION_DEASSERT;
          (irq_mask & local::reserved_irq_mask) == 0;
        })

        rand_delay();

      end
    end

    begin : gen_deassert

      repeat (initial_delay_deassert) @(cntxt.interrupt_cntxt.vif.drv_cb);

      while(1) begin
        uvma_interrupt_seq_item_c irq_req;

        `uvm_do_on_with(irq_req, p_sequencer.interrupt_sequencer, {
          action        == UVMA_INTERRUPT_SEQ_ITEM_ACTION_ASSERT;
          (irq_mask & local::reserved_irq_mask) == 0;
        })

        rand_delay();

      end
    end
  join
endtask : body

`endif // __UVME_CV32E40X_INTERRUPT_NOISE_SV__
