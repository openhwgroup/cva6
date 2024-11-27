// (C) 2001-2024 Intel Corporation. All rights reserved.
// Your use of Intel Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files from any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Intel Program License Subscription 
// Agreement, Intel FPGA IP License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Intel and sold by 
// Intel or its authorized distributors.  Please refer to the applicable 
// agreement for further details.


// $Id: //acds/main/ip/sopc/components/primitives/altera_std_synchronizer/altera_std_synchronizer.v#8 $
// $Revision: #8 $
// $Date: 2009/02/18 $
// $Author: pscheidt $
//-----------------------------------------------------------------------------
//
// File: altera_std_synchronizer_nocut.v
//
// Abstract: Single bit clock domain crossing synchronizer. Exactly the same
//           as altera_std_synchronizer.v, except that the embedded false
//           path constraint is removed in this module. If you use this
//           module, you will have to apply the appropriate timing
//           constraints.
//
//           We expect to make this a standard Quartus atom eventually.
//
//           Composed of two or more flip flops connected in series.
//           Random metastable condition is simulated when the 
//           __ALTERA_STD__METASTABLE_SIM macro is defined.
//           Use +define+__ALTERA_STD__METASTABLE_SIM argument 
//           on the Verilog simulator compiler command line to 
//           enable this mode. In addition, define the macro
//           __ALTERA_STD__METASTABLE_SIM_VERBOSE to get console output 
//           with every metastable event generated in the synchronizer.
//
// Copyright (C) Altera Corporation 2009, All Rights Reserved
//-----------------------------------------------------------------------------

`timescale 1ns / 1ns

module altera_std_synchronizer_nocut (
                                clk, 
                                reset_n, 
                                din, 
                                dout
                                );

   parameter depth = 3; // This value must be >= 2 !
   parameter rst_value = 0;

  //when enabled, this will allow retiming for the sync depth >3.
   parameter retiming_reg_en = 0;
     
   input   clk;
   input   reset_n;    
   input   din;
   output  dout;
   
   // QuartusII synthesis directives:
   //     1. Preserve all registers ie. do not touch them.
   //     2. Do not merge other flip-flops with synchronizer flip-flops.
   // QuartusII TimeQuest directives:
   //     1. Identify all flip-flops in this module as members of the synchronizer 
   //        to enable automatic metastability MTBF analysis.

   (* altera_attribute = {"-name ADV_NETLIST_OPT_ALLOWED NEVER_ALLOW; -name SYNCHRONIZER_IDENTIFICATION FORCED; -name DONT_MERGE_REGISTER ON; -name PRESERVE_REGISTER ON  "} *) reg din_s1;

   (* altera_attribute = {"-name ADV_NETLIST_OPT_ALLOWED NEVER_ALLOW; -name DONT_MERGE_REGISTER ON; -name PRESERVE_REGISTER ON"} *) reg [depth-2:0] dreg;    

   //synthesis translate_off
   `ifndef QUARTUS_CDC
   initial begin
     if (retiming_reg_en == 0 ) begin
       if (depth <2) begin 
         $display("%m: Error: synchronizer length: %0d less than 2.", depth);
       end
      end
     else begin
       if (depth <4) begin 
         $display("%m: Error: synchronizer length: %0d less than 4 with retiming enabled.", depth);
       end
     end
   end
   `endif 

   // the first synchronizer register is either a simple D flop for synthesis
   // and non-metastable simulation or a D flop with a method to inject random
   // metastable events resulting in random delay of [0,1] cycles
   
`ifdef __ALTERA_STD__METASTABLE_SIM

   reg[31:0]  RANDOM_SEED = 123456;      
   wire  next_din_s1;
   wire  dout;
   reg   din_last;
   reg          random;
   event metastable_event; // hook for debug monitoring

   initial begin
      $display("%m: Info: Metastable event injection simulation mode enabled");
      random = $random;
   end
   
   always @(posedge clk) begin
      if (reset_n == 0)
        random <= $random(RANDOM_SEED);
      else
        random <= $random;
   end

   assign next_din_s1 = (din_last ^ din) ? random : din;   

   always @(posedge clk or negedge reset_n) begin
       if (reset_n == 0) 
         din_last <= (rst_value == 0)? 1'b0 : 1'b1;
       else
         din_last <= din;
   end

   always @(posedge clk or negedge reset_n) begin
       if (reset_n == 0) 
         din_s1 <= (rst_value == 0)? 1'b0 : 1'b1;
       else
         din_s1 <= next_din_s1;
   end
   
`else 

   //synthesis translate_on   
   generate if (rst_value == 0)
       always @(posedge clk or negedge reset_n) begin
           if (reset_n == 0) 
             din_s1 <= 1'b0;
           else
             din_s1 <= din;
       end
   endgenerate
   
   generate if (rst_value == 1)
       always @(posedge clk or negedge reset_n) begin
           if (reset_n == 0) 
             din_s1 <= 1'b1;
           else
             din_s1 <= din;
       end
   endgenerate
   //synthesis translate_off      

`endif

`ifdef __ALTERA_STD__METASTABLE_SIM_VERBOSE
   always @(*) begin
      if (reset_n && (din_last != din) && (random != din)) begin
         $display("%m: Verbose Info: metastable event @ time %t", $time);
         ->metastable_event;
      end
   end      
`endif

   //synthesis translate_on

   // the remaining synchronizer registers form a simple shift register
   // of length depth-1
   generate if (rst_value == 0) begin
      if (retiming_reg_en == 0) begin
         if (depth < 3) begin
            always @(posedge clk or negedge reset_n) begin
               if (reset_n == 0) 
                 dreg <= {depth-1{1'b0}};            
               else
                 dreg <= din_s1;
            end         
         end else begin
            always @(posedge clk or negedge reset_n) begin
               if (reset_n == 0) 
                 dreg <= {depth-1{1'b0}};
               else
                 dreg <= {dreg[depth-3:0], din_s1};
            end
         end

         assign dout = dreg[depth-2];
       end

       else begin //This part is enabled when we set retiming_reg_en =1
          (* altera_attribute = {"-name ADV_NETLIST_OPT_ALLOWED NEVER_ALLOW; -name DONT_MERGE_REGISTER ON; -name PRESERVE_REGISTER ON"} *) reg [1:0] dreg1;
          reg [depth-4:0] dreg2;
          wire [depth-2:0] dreg3;

          assign dreg3 = {dreg2,dreg1};

          if (depth <= 3) begin
             always @(posedge clk or negedge reset_n) begin
                if (reset_n == 0)
                  dreg1 <= {depth-1{1'b0}};
                else
                  dreg1 <= din_s1;
               end
           end
           else begin
              always @(posedge clk or negedge reset_n) begin
                if (reset_n == 0)
                  {dreg2,dreg1} <= {depth-1{1'b0}};
                else
                  {dreg2,dreg1} <= {dreg3[depth-3:0], din_s1};
              end
           end
           assign dout = dreg3[depth-2];
       end
    end

   
   else begin
      if (retiming_reg_en == 0) begin
         if (depth < 3) begin
            always @(posedge clk or negedge reset_n) begin
               if (reset_n == 0) 
                 dreg <= {depth-1{1'b1}};            
               else
                 dreg <= din_s1;
             end         
         end else begin
            always @(posedge clk or negedge reset_n) begin
               if (reset_n == 0) 
                 dreg <= {depth-1{1'b1}};
               else
                 dreg <= {dreg[depth-3:0], din_s1};
            end
         end
       assign dout = dreg[depth-2];
    end

      else begin
         (* altera_attribute = {"-name ADV_NETLIST_OPT_ALLOWED NEVER_ALLOW; -name DONT_MERGE_REGISTER ON; -name PRESERVE_REGISTER ON"} *) reg [1:0] dreg1;
         reg [depth-4:0] dreg2;
         wire [depth-2:0] dreg3;

         assign dreg3 = {dreg2,dreg1};

           if (depth <= 3) begin
               always @(posedge clk or negedge reset_n) begin
                  if (reset_n == 0)
                    dreg1 <= {depth-1{1'b1}};
                  else
                    dreg1 <= din_s1;
               end
           end
           else begin
               always @(posedge clk or negedge reset_n) begin
                  if (reset_n == 0)
                    {dreg2,dreg1} <= {depth-1{1'b1}};
                  else
                    {dreg2,dreg1} <= {dreg3[depth-3:0], din_s1};
               end
            end  
          assign dout = dreg3[depth-2];
        end
     end
   endgenerate

endmodule 
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "aBtvkOB0rVavpqYSnxGbfcYBNx6OkCwAi2K9gh9Y53caqg+VfzD4if1Wx+NybTLcpY+PnuQz6pp9KScOY4ye64zeX7CBjYAFsecofqjfk4a1c+382xda6/OF2dJrJri51Uq3eJPH2tWhlL9RydkIvKPJDVVgsS6+mu9Mhzg00gJFu3PHFz80h2m0h/O4E8aAn998tC3clvatEJIWGp/WDkQ+DABTXAmgzljq9l00wHHlQKp4dZWIzdPxUtrHxAa3x1dtnlScSyYYyx2fXHeg/nh3nZxYZ4QbQ7MBw0OMADXU0N8CpFFQljG99TZjQBJdLBLJRYSY71DTm85eCDqeM1MOSgf3F47ZHihaaJgfOK5Qy1myN8Un9uiKFilNXwp8mpHadYS4Z582GkRuV6zlovrdby/xESUQf1/DWgC0CF/vlTsP8Jpw3vTPq2h1bILGPzTrQpJqQFSASl6pC69qTXRxUAh5vV7FgwSd7BcKB24KtZcsMlqlEZvLfurZLUo+yj86zGm/S0rFIVbBSCuY+J9OMaOEloV7WkDREZ6lR6KN97Ry3IsHnr03SMgkFAPTubk1EEO+6cOkjYaxemUs6vsbyan5i9VbF88m1X5ITFRfOCNB4p5eWppdirYruL+EkSudlEj7XjY08nJg3IDo/8DRr5yqp7t9WybAm5vHsd3rgb7ruVFAjP8KoedXf5gwhkslO8NcZqADGNh/3I21On06VBJ0Tmh7mOQjzUKdeMLzyzRegco5pWDphgD51Iej5wZOoJLzyZbJkRN+h+o74LNmZE22KRWx6bdS2eNx08/dmLBAY2JB6P7xAgfxalYQY5FyWXWVlw9DiHqRuGOtJRI0Rf8hudKDET6LnVXRYnjAM5x/Kxw3VW8e1lX8zKCnP42NZ+Cs7+SMc3xkDdndFQOErW1eGLxV4poLgtp2LYn58ff9E21ixrxe6l6n73D6INSQXyh+399nt2zmXfmZ/CluDKJOOSHBulbzntO6ctpcKUjU+bz6yYn+oddPmMzo"
`endif