// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


module pad_frame
    (
     // HYPERBUS
     input logic [1:0]   hyper_cs_ni ,
     input logic         hyper_ck_i ,
     input logic         hyper_ck_ni ,
     input logic [1:0]   hyper_rwds_i ,
     output logic        hyper_rwds_o ,
     input logic [1:0]   hyper_rwds_oe_i ,
     output logic [15:0] hyper_dq_o ,
     input logic [15:0]  hyper_dq_i ,
     input logic [1:0]   hyper_dq_oe_i ,
     input logic         hyper_reset_ni ,

     inout wire [7:0]    pad_hyper_dq0 ,
     inout wire [7:0]    pad_hyper_dq1 ,
     inout wire          pad_hyper_ck ,
     inout wire          pad_hyper_ckn ,
     inout wire          pad_hyper_csn0 ,
     inout wire          pad_hyper_csn1 ,
     inout wire          pad_hyper_rwds0 ,
     inout wire          pad_hyper_rwds1 ,
     inout wire          pad_hyper_reset ,

     //I2C
     inout wire          pad_i2c_sda     ,
     inout wire          pad_i2c_scl     ,

     //SPI MASTER
     inout wire          pad_spim_sdio0   ,
     inout wire          pad_spim_sdio1   ,
     inout wire          pad_spim_sdio2   ,
     inout wire          pad_spim_sdio3   ,
     inout wire          pad_spim_csn0    ,
     inout wire          pad_spim_sck     ,

     // HYPERBUS
     input logic [1:0]   axi_hyper_cs_ni ,
     input logic         axi_hyper_ck_i ,
     input logic         axi_hyper_ck_ni ,
     input logic         axi_hyper_rwds_i ,
     output logic        axi_hyper_rwds_o ,
     input logic         axi_hyper_rwds_oe_i ,
     output logic [7:0]  axi_hyper_dq_o ,
     input logic [7:0]   axi_hyper_dq_i ,
     input logic         axi_hyper_dq_oe_i ,
     input logic         axi_hyper_reset_ni ,

     //I2C
     input logic         i2c_sda_oe_i ,
     input logic         i2c_scl_oe_i ,
     input logic         i2c_sda_out_i ,
     input logic         i2c_scl_out_i ,
     output logic        i2c_in_sda_o ,
     output logic        i2c_in_scl_o ,

     //SPI MASTER
     input logic         oen_spim_sdio0_i  ,
     input logic         oen_spim_sdio1_i  ,
     input logic         oen_spim_sdio2_i  ,
     input logic         oen_spim_sdio3_i  ,

     output logic        in_spim_sdio0_o  ,
     output logic        in_spim_sdio1_o  ,
     output logic        in_spim_sdio2_o  ,
     output logic        in_spim_sdio3_o  ,

     input logic         out_spim_sdio0_i ,
     input logic         out_spim_sdio1_i ,
     input logic         out_spim_sdio2_i ,
     input logic         out_spim_sdio3_i ,

     input logic         out_spim_csn1_i  ,
     input logic         out_spim_csn0_i  ,
     input logic         out_spim_sck_i   ,
                         
     inout wire [7:0]    pad_axi_hyper_dq0 ,
     inout wire [7:0]    pad_axi_hyper_dq1 ,
     inout wire          pad_axi_hyper_ck ,
     inout wire          pad_axi_hyper_ckn ,
     inout wire          pad_axi_hyper_csn0 ,
     inout wire          pad_axi_hyper_csn1 ,
     inout wire          pad_axi_hyper_rwds0 ,
     inout wire          pad_axi_hyper_rwds1 ,
     inout wire          pad_axi_hyper_reset ,

     input wire [63:0]   gpio_pad_out,
     output wire [63:0]  gpio_pad_in,
     input wire [63:0]   gpio_pad_dir,

     inout wire [63:0]   pad_gpio
     );

`ifndef FPGA_EMUL  

    //HYPER
    pad_functional_pu padinst_hyper_csno0  (.OEN( 1'b0              ), .I( hyper_cs_ni[0]     ), .O(                   ), .PAD( pad_hyper_csn0    ), .PEN(1'b1 ) );
    pad_functional_pu padinst_hyper_csno1  (.OEN( 1'b0              ), .I( hyper_cs_ni[1]     ), .O(                   ), .PAD( pad_hyper_csn1    ), .PEN(1'b1 ) );
    pad_functional_pu padinst_hyper_ck     (.OEN( 1'b0              ), .I( hyper_ck_i         ), .O(                   ), .PAD( pad_hyper_ck      ), .PEN(1'b1 ) );
    pad_functional_pu padinst_hyper_ckno   (.OEN( 1'b0              ), .I( hyper_ck_ni        ), .O(                   ), .PAD( pad_hyper_ckn     ), .PEN(1'b1 ) );
    pad_functional_pu padinst_hyper_rwds0  (.OEN(~hyper_rwds_oe_i[0]), .I( hyper_rwds_i[0]    ), .O( hyper_rwds_o      ), .PAD( pad_hyper_rwds0   ), .PEN(1'b1 ) );
    pad_functional_pu padinst_hyper_rwds1  (.OEN(~hyper_rwds_oe_i[1]), .I( hyper_rwds_i[1]    ), .O(                   ), .PAD( pad_hyper_rwds1   ), .PEN(1'b1 ) );
    pad_functional_pu padinst_hyper_resetn (.OEN( 1'b0              ), .I( hyper_reset_ni     ), .O(                   ), .PAD( pad_hyper_reset   ), .PEN(1'b1 ) );

    genvar j;
    generate
       for (j=0; j<8; j++) begin
                pad_functional_pu padinst_hyper_dqio0  (.OEN(~hyper_dq_oe_i[0]   ), .I( hyper_dq_i[j]   ), .O( hyper_dq_o[j]  ), .PAD( pad_hyper_dq0[j]   ), .PEN(1'b1 ) );
        end
    endgenerate

    //I2C
    pad_functional_pu padinst_i2c_sda     (.OEN( ~i2c_sda_oe_i ), .I( i2c_sda_out_i ), .O( i2c_in_sda_o ), .PAD( pad_i2c_sda ), .PEN( 1'b0 ) );
    pad_functional_pu padinst_i2c_scl     (.OEN( ~i2c_scl_oe_i ), .I( i2c_scl_out_i ), .O( i2c_in_scl_o ), .PAD( pad_i2c_scl ), .PEN( 1'b0 ) );

    //SPI MASTER
    pad_functional_pd padinst_spim_sck    (.OEN( 1'b0   ), .I( out_spim_sck_i   ), .O(   ), .PAD( pad_spim_sck   ), .PEN( 1'b0 ) );
    pad_functional_pd padinst_spim_csn0   (.OEN( 1'b0  ),  .I( out_spim_csn0_i  ), .O(   ), .PAD( pad_spim_csn0  ), .PEN( 1'b0 ) );
    pad_functional_pd padinst_spim_sdio0  (.OEN( oen_spim_sdio0_i ), .I( out_spim_sdio0_i ), .O( in_spim_sdio0_o ), .PAD( pad_spim_sdio0 ), .PEN( 1'b0 ) );
    pad_functional_pd padinst_spim_sdio1  (.OEN( oen_spim_sdio1_i ), .I( out_spim_sdio1_i ), .O( in_spim_sdio1_o ), .PAD( pad_spim_sdio1 ), .PEN( 1'b0 ) );
    pad_functional_pd padinst_spim_sdio2  (.OEN( oen_spim_sdio2_i ), .I( out_spim_sdio2_i ), .O( in_spim_sdio2_o ), .PAD( pad_spim_sdio2 ), .PEN( 1'b0 ) );
    pad_functional_pd padinst_spim_sdio3  (.OEN( oen_spim_sdio3_i ), .I( out_spim_sdio3_i ), .O( in_spim_sdio3_o ), .PAD( pad_spim_sdio3 ), .PEN( 1'b0 ) );


`endif //  `ifndef FPGA_EMUL
   
    pad_functional_pu padinst_axi_hyper_csno0  (.OEN( 1'b0                  ), .I( axi_hyper_cs_ni[0]  ), .O(                   ), .PAD( pad_axi_hyper_csn0    ), .PEN(1'b1 ) );
    pad_functional_pu padinst_axi_hyper_csno1  (.OEN( 1'b0                  ), .I( axi_hyper_cs_ni[1]  ), .O(                   ), .PAD( pad_axi_hyper_csn1    ), .PEN(1'b1 ) );
    pad_functional_pu padinst_axi_hyper_ck     (.OEN( 1'b0                  ), .I( axi_hyper_ck_i      ), .O(                   ), .PAD( pad_axi_hyper_ck      ), .PEN(1'b1 ) );
    pad_functional_pu padinst_axi_hyper_ckno   (.OEN( 1'b0                  ), .I( axi_hyper_ck_ni     ), .O(                   ), .PAD( pad_axi_hyper_ckn     ), .PEN(1'b1 ) );
    pad_functional_pu padinst_axi_hyper_rwds0  (.OEN(~axi_hyper_rwds_oe_i   ), .I( axi_hyper_rwds_i    ), .O( axi_hyper_rwds_o  ), .PAD( pad_axi_hyper_rwds0   ), .PEN(1'b1 ) );
    pad_functional_pu padinst_axi_hyper_resetn (.OEN( 1'b0                  ), .I( axi_hyper_reset_ni  ), .O(                   ), .PAD( pad_axi_hyper_reset   ), .PEN(1'b1 ) );

    genvar k;
    generate
       for (k=0; k<8; k++) begin
                pad_functional_pu padinst_axi_hyper_dqio0  (.OEN(~axi_hyper_dq_oe_i   ), .I( axi_hyper_dq_i[k]   ), .O( axi_hyper_dq_o[k]  ), .PAD( pad_axi_hyper_dq0[k]   ), .PEN(1'b1 ) );
        end
    endgenerate
   
`ifndef FPGA_EMUL       
    genvar i;
    generate
       for (i=0; i<64; i++) begin
                pad_functional_pu padinst_gpio  (.OEN(~gpio_pad_dir[i]   ), .I( gpio_pad_out[i]   ), .O( gpio_pad_in[i]  ), .PAD( pad_gpio[i]   ), .PEN(1'b1 ) );
        end
    endgenerate
`endif
   
endmodule
