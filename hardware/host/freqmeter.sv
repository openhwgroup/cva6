// Copyright 2021 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
`timescale 1ns/1ns

module freq_meter
#(
    parameter FLL_NAME = "CLK_FLL",
    parameter MAX_SAMPLE = 1024
)
(
    input clk
);
`ifndef TARGET_SYNTHESIS  
  real  past_time;
  real  current_time;
  real  PERIOD;
  real  SAMPLES [MAX_SAMPLE];
  real  TOTAL_PERIOD;
  int  unsigned counter_SAMPLES;
  logic print_freq;
  logic rstn;
  integer     FILE;

  string filename = {FLL_NAME,".log"};

  initial
  begin
    FILE = $fopen(filename,"w");
    rstn = 0;
    #100 rstn = 1;
  end

  always_ff @(posedge clk or negedge rstn)
  begin
    if(!rstn)
    begin
      current_time <= 0;
      past_time    <= 0;
    end
    else
    begin
      current_time <= $time();
      past_time    <= current_time;
    end
  end

  always_comb
  begin
      PERIOD = current_time - past_time;
  end



  always_ff @(posedge clk or negedge rstn)
  begin
    if (!rstn)
    begin
      print_freq <= 0;
      counter_SAMPLES <= 'h0;
    end
    else
    begin
      SAMPLES[counter_SAMPLES] <=  PERIOD;

      if(counter_SAMPLES < MAX_SAMPLE - 1)
      begin
        counter_SAMPLES <= counter_SAMPLES + 1;
        print_freq      <= 1'b0;
      end
      else
      begin
        print_freq      <= 1'b1;
        counter_SAMPLES <= 0;
      end
    end
  end

  always_comb
  begin
    if(print_freq)
    begin
      TOTAL_PERIOD = 0;
      for (int i = 0; i < MAX_SAMPLE; i++) begin
        TOTAL_PERIOD = TOTAL_PERIOD + SAMPLES[i];
      end
      $fdisplay(FILE, "[%s  Frequecy]  is %f [MHz]\t @ %t [ns]" , FLL_NAME, (1000.0*1000.0*MAX_SAMPLE/(TOTAL_PERIOD)), $time()/1000.0);
      $fflush(FILE);
    end
  end
`endif
endmodule // freq_meter
