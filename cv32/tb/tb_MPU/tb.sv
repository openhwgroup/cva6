`timescale 1ns/1ps
`define SOD 2

`define DIS 2'b00
`define TOR 2'b01
`define NA4 2'b10
`define NAP 2'b11



module tb;
   parameter N_PMP_ENTRIES = 16;
   parameter CLK_PERIOD    = 25;
   parameter MAX_CNT       = 4096;

   logic                             clk;
   logic                             rst_n;
   logic                             pmp_privil_mode;
   logic  [N_PMP_ENTRIES-1:0] [31:0] pmp_addr;
   logic  [N_PMP_ENTRIES-1:0] [7:0]  pmp_cfg;

   // data side : if TO pipeline
   logic                            data_req_i;
   logic [31:0]                     data_addr_i;
   logic                            data_we_i;
   logic                            data_gnt_o;
   // if to Memory
   logic                            data_req_o;
   logic                            data_gnt_i;
   logic [31:0]                     data_addr_o;
   logic                            data_err_o;

   // fetch side : if TO pipeline
   logic                            instr_req_i;
   logic [31:0]                     instr_addr_i;
   logic                            instr_gnt_o;
   // fetch to PF buffer
   logic                            instr_req_o;
   logic                            instr_gnt_i;
   logic [31:0]                     instr_addr_o;
   logic                            instr_err_o;


   logic  [N_PMP_ENTRIES-1:0] [7:0]  exp_data_match;
   logic                             exp_error;

   event trans_OK;


    riscv_pmp
    #(
       .N_PMP_ENTRIES(N_PMP_ENTRIES)
    )
    DUT
    (
       .clk               ( clk               ),
       .rst_n             ( rst_n             ),

       .pmp_privil_mode_i ( pmp_privil_mode   ),

       .pmp_addr_i        ( pmp_addr          ),
       .pmp_cfg_i         ( pmp_cfg           ),

       .data_req_i        ( data_req_i        ),
       .data_addr_i       ( data_addr_i       ),
       .data_we_i         ( data_we_i         ),
       .data_gnt_o        ( data_gnt_o        ),

       .data_req_o        ( data_req_o        ),
       .data_gnt_i        ( data_gnt_i        ),
       .data_addr_o       ( data_addr_o       ),
       .data_err_o        ( data_err_o        ),


       .instr_req_i       ( instr_req_i       ),
       .instr_addr_i      ( instr_addr_i      ),
       .instr_gnt_o       ( instr_gnt_o       ),
       .instr_req_o       ( instr_req_o       ),
       .instr_gnt_i       ( instr_gnt_i       ),
       .instr_addr_o      ( instr_addr_o      ),
       .instr_err_o       ( instr_err_o       )
    );


   always
   begin
      #(CLK_PERIOD/2.0);
      clk = ~clk;
   end

   always @(posedge clk)
   begin
        if((data_err_o == 1'b1 ) && (data_req_i == 1'b1) && (data_req_o == 1'b1))
            $error("Requested in not Blocked during acces on a forbidded region");

        if( (data_err_o == 1'b1 ))
            if(data_gnt_o == 1)
                $error("Grant is 1 durig ERROR");

        if( (data_req_i == 1'b1 ) && (data_err_o == 1'b0 ))
            if(data_gnt_o != data_gnt_i)
                $error("Grant is not propagated with TRANS OK");


        if((data_err_o == 1'b0 ) && (data_req_i == 1'b1) && (data_err_o == 1'b1))
            -> trans_OK;
   end

   initial
   begin
      clk = 1'b0;
      rst_n = 1'b1;


      pmp_privil_mode = 1'b0;

      data_req_i  = '0;
      data_addr_i = '0;
      data_we_i   = '0;
      data_gnt_i  = '0;

      instr_req_i  = '0;
      instr_addr_i = '0;
      instr_gnt_i  = '0;

      @(posedge  clk);
      @(posedge  clk);
      @(posedge  clk);
      @(negedge  clk);
      rst_n = 1'b0;
      /// test DISABLE
      pmp_addr[0]  = 32'h1000_0000 >> 2 | 16'h000F;
      pmp_addr[1]  = 32'h1100_0000 >> 2;
      pmp_addr[2]  = 32'h1200_0000 >> 2;
      pmp_addr[3]  = 32'h1300_0000 >> 2;
      pmp_addr[4]  = 32'h1400_0000 >> 2;
      pmp_addr[5]  = 32'h1500_0000 >> 2;
      pmp_addr[6]  = 32'h1600_0000 >> 2;
      pmp_addr[7]  = 32'h1700_0000 >> 2;
      pmp_addr[8]  = 32'h1800_0000 >> 2;
      pmp_addr[9]  = 32'h1900_0000 >> 2;
      pmp_addr[10] = 32'h1A00_0000 >> 2;
      pmp_addr[11] = 32'h1B00_0000 >> 2;
      pmp_addr[12] = 32'h1C00_0000 >> 2 | 16'h000F;
      pmp_addr[13] = 32'h1D00_0000 >> 2;
      pmp_addr[14] = 32'h1E00_0000 >> 2;
      pmp_addr[15] = 32'h1F00_0000 >> 2 | 16'hFFFF;
                 //  {LOCK_rule[i],WIRI_rule[i],MODE_rule[i],X_rule[i], W_rule[i], R_rule[i] }
      pmp_cfg[0]   = {2'b00,       1'b0,        `DIS,        1'b1,      1'b1,      1'b1      };
      pmp_cfg[1]   = {2'b00,       1'b0,        `DIS,        1'b0,      1'b1,      1'b0      };
      pmp_cfg[2]   = {2'b00,       1'b0,        `DIS,        1'b0,      1'b1,      1'b1      };
      pmp_cfg[3]   = {2'b00,       1'b0,        `DIS,        1'b0,      1'b1,      1'b0      };
      pmp_cfg[4]   = {2'b00,       1'b0,        `DIS,        1'b0,      1'b1,      1'b1      };
      pmp_cfg[5]   = {2'b00,       1'b0,        `DIS,        1'b0,      1'b1,      1'b0      };
      pmp_cfg[6]   = {2'b00,       1'b0,        `DIS,        1'b0,      1'b1,      1'b1      };
      pmp_cfg[7]   = {2'b00,       1'b0,        `DIS,        1'b0,      1'b1,      1'b0      };
      pmp_cfg[8]   = {2'b00,       1'b0,        `DIS,        1'b0,      1'b1,      1'b1      };
      pmp_cfg[9]   = {2'b00,       1'b0,        `DIS,        1'b0,      1'b1,      1'b0      };
      pmp_cfg[10]  = {2'b00,       1'b0,        `DIS,        1'b1,      1'b1,      1'b1      };
      pmp_cfg[11]  = {2'b00,       1'b0,        `DIS,        1'b0,      1'b1,      1'b0      };
      pmp_cfg[12]  = {2'b00,       1'b0,        `NAP,        1'b0,      1'b1,      1'b1      };
      pmp_cfg[13]  = {2'b00,       1'b0,        `DIS,        1'b0,      1'b1,      1'b0      };
      pmp_cfg[14]  = {2'b00,       1'b0,        `DIS,        1'b0,      1'b1,      1'b1      };
      pmp_cfg[15]  = {2'b00,       1'b0,        `DIS,        1'b0,      1'b1,      1'b0      };
      @(posedge  clk);
      @(posedge  clk);
      @(posedge  clk);
      @(negedge  clk);
      rst_n = 1'b1;

      #(100);
      @(posedge  clk);
      #(`SOD);

      // for(int unsigned i=0; i<MAX_CNT; i++)
      // begin
      //       //$display("Iteration %d",i);
      //       data_req_i  = $random()%2;
      //       data_addr_i = (data_req_i) ? $random() & 32'h1FFF_FFFC  : 'X ;
      //       data_gnt_i  = $random()%2;
      //       data_we_i  = (data_req_i) ? $random()%2 : 1'b0;
      //       @(posedge  clk);
      //       #(`SOD);
      //       //check_rules

      //       if(data_err_o != exp_error)
      //           $error("Unexpected ERROR detected on data");
      //       @(posedge  clk);
      //       #(`SOD);
      // end

      for(int unsigned i=0; i<MAX_CNT; i++)
      begin
            //$display("Iteration %d",i);
            data_req_i  = 1;
            data_addr_i = (data_req_i) ? 32'h1C00_0000 + i*4 : 'X ;
            data_gnt_i  = $random()%2;
            data_we_i  = (data_req_i) ? $random()%2 : 1'b0;
            @(posedge  clk);
            #(`SOD);
      end

      $stop;


   end





/*
       for(int unsigned index = 0; i<N_PMP_ENTRIES;i++)
            begin
                case (pmp_cfg[index][4:3])
                `DIS: begin exp_data_match[index] = '0; end
                `TOR: begin
                    if(index == 0)
                    begin
                        exp_data_match[index] = ( data_req_i &
                                            ( data_wen_i & pmp_cfg[index][0]) |(~data_wen_i & pmp_cfg[index][1])) &
                                            (data_addr_i<= pmp_addr[index]) && (data_addr_i >= '0);
                    end
                    else
                    begin
                        exp_data_match[index] = ( data_req_i &
                                            (( data_wen_i & pmp_cfg[index][0]) |(~data_wen_i & pmp_cfg[index][1])) &
                                            (data_addr_i<= pmp_addr[index]) && (data_addr_i >= pmp_addr[index-1]) );
                    end
                end

                `NA4: exp_data_match[index] = ( data_req_i & (( data_wen_i & pmp_cfg[index][0]) | (~data_wen_i & pmp_cfg[index][1])) & (data_addr_i == pmp_addr[index]) );

                `NAP: begin
                      int unsigned first_zero;
                      logic [31:0] start_addr;
                      logic [31:0] end_addr;
                      logic [31:0] mask_start_addr;
                      mask_start_addr = '1;

                      for(int unsigned j=0; j<32;j++)
                      begin
                        if(pmp_addr[index][31-j] == 1'b0)
                               first_zero = 31-j;
                      end

                      for(int unsigned j=0; j<first_zero;j++)
                      begin
                        mask_start_addr[j] = '0;
                      end
                      end_addr   = pmp_addr[index];
                      start_addr = pmp_addr[index] & mask_start_addr;



                      exp_data_match[index] = (   data_req_i &
                                               (( data_wen_i & pmp_cfg[index][0]) | (~data_wen_i & pmp_cfg[index][1])) &
                                                (data_addr_i <= end_addr) & (data_addr_i >= start_addr));
                end
                endcase


            end
*/

endmodule // tb
