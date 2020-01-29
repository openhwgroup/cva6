/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the "License"); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File: $filename.v
 *
 * Description: Auto-generated bootrom
 */

// Auto-generated code
module bootrom (
   input  logic         clk_i,
   input  logic         req_i,
   input  logic [63:0]  addr_i,
   output logic [63:0]  rdata_o
);
    localparam int RomSize = 354;

    const logic [RomSize-1:0][63:0] mem = {
        64'h46454443_42413938,
        64'h37363534_33323130,
        64'h00000000_20000000,
        64'h00000000_20008000,
        64'h00000000_000a786c,
        64'h25783020_3a6d7366,
        64'h5f6e6172_74202073,
        64'h25203a65_74617473,
        64'h5f6e6172_74202078,
        64'h6c257830_203a6d73,
        64'h665f7469_6e692020,
        64'h20200a78_6c257830,
        64'h203a7265_746e756f,
        64'h63202073_25203a65,
        64'h74617473_5f74696e,
        64'h69202078_6c257830,
        64'h203a6365_765f7073,
        64'h65722020_20200a73,
        64'h25203a73_75746174,
        64'h7320786c_25783020,
        64'h3a665f61_6d642020,
        64'h786c2578_3020203a,
        64'h665f6473_20202020,
        64'h00000078_6c257830,
        64'h00544345_54454420,
        64'h00000043_58434820,
        64'h00000000_0000454e,
        64'h4f445f54_494e4920,
        64'h00000000_00000000,
        64'h5944525f_51455220,
        64'h00515249_5f445320,
        64'h004e455f_51524920,
        64'h0052575f_51455220,
        64'h0044525f_51455220,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_a001981f,
        64'hf0effe94_17e3fb4f,
        64'hf0ef0ff5_7513ff25,
        64'h0de3842a_8fdff0ef,
        64'h44b5597d_b23ff0ef,
        64'h450105fe_46014685,
        64'h4585acdf_f0ef4501,
        64'h931ff0ef_ff6ff0ef,
        64'he822e04a_e426ec06,
        64'h08050513_20058593,
        64'h110102fa_f53765f1,
        64'hbf650106_80230785,
        64'h00f706b3_0006c803,
        64'h00f586b3_b7e900f5,
        64'h0733963a_95be078e,
        64'h02e78733_57610036,
        64'h5793fed7_65e340f6,
        64'h06b30106_b02307a1,
        64'h00f506b3_0006b803,
        64'h00f586b3_808202f6,
        64'h1b634781_872acf99,
        64'h471d8b9d_00b567b3,
        64'h00b50b63_b7f5feb7,
        64'h8fa30785_bfe9fee7,
        64'hbc2307a1_808200c7,
        64'h9763963e_963a97aa,
        64'h078e02e7_87335761,
        64'h00365793_0106ee63,
        64'h40f88833_469d00c5,
        64'h08b387aa_ffed8f55,
        64'h37fd0722_0ff5f693,
        64'h47a1eb05_87aa0075,
        64'h7713bfcd_07858082,
        64'h40a78533_e7010007,
        64'hc70387aa_bfcd0505,
        64'hdffd8082_00b79363,
        64'h00054783_0ff5f593,
        64'h8082f2fd_0705e119,
        64'h4185551b_0187951b,
        64'h40f687bb_05850005,
        64'hc7830007_4683872a,
        64'h8082fbf5_fef70fa3,
        64'h07050585_0005c783,
        64'hfee50785_873e0007,
        64'hc68387aa_8082fb75,
        64'hfee78fa3_07850585,
        64'h0005c703_87aa8082,
        64'h61356452_852260f2,
        64'h97dff0ef_0808842a,
        64'he3fff0ef_e436eec6,
        64'heac2e6be_e2baea22,
        64'hee060808_10000593,
        64'h1234862a_fe36fa32,
        64'hf62e710d_80826161,
        64'h60e2e69f_f0efe436,
        64'he4c6e0c2_fc3ef83a,
        64'hec061000_05931014,
        64'h862ef436_f032715d,
        64'h80826161_60e2e8df,
        64'hf0efe436_e4c6e0c2,
        64'hfc3ef83a_ec061034,
        64'hf436715d_bf8d4601,
        64'h46850038_00840b13,
        64'hbdf9845a_d61ff0ef,
        64'h00840b13_02010393,
        64'h00044503_b7e18522,
        64'h02010393_0005059b,
        64'h108000ef_85220124,
        64'h74336000_00840b13,
        64'hf4f514e3_07300793,
        64'hfae504e3_07800713,
        64'hfce50ae3_07500713,
        64'ha099dddf_f0ef0028,
        64'h02010393_0005059b,
        64'he3fff0ef_400845a9,
        64'h46010015_36930038,
        64'h00840b13_f8b50513,
        64'hf8e514e3_06400713,
        64'hb74d048d_0024c503,
        64'ha01545c1_00153613,
        64'h46850038_00840b13,
        64'hfa850513_fae516e3,
        64'h05800713_d15902a6,
        64'he56308d5_09630630,
        64'h069306a6_e3630ad5,
        64'h09630700_06930489,
        64'h0014c503_478100f6,
        64'hf36346a5_0ff7f793,
        64'hfd07879b_dbdd0004,
        64'hc7830355_10634781,
        64'h04890545_0f630014,
        64'hc503b7c1_e41ff0ef,
        64'h02010393_04850135,
        64'h0863fcd7_ffe39381,
        64'h17827682_0017079b,
        64'h80826109_0007051b,
        64'h6b066aa6_6a4669e6,
        64'h790674a6_744670e6,
        64'hed098f1d_0004c503,
        64'h77a27742_02095913,
        64'h03000a93_06c00a13,
        64'h02500993_f82af02e,
        64'hf42afc3e_843684b2,
        64'he0dafc86_e4d6e8d2,
        64'heccef4a6_f8a2597d,
        64'h011cf0ca_7119b7e1,
        64'h01178023_00660023,
        64'h06850006_48830007,
        64'hc30300d7_063397ba,
        64'h93811782_40f807bb,
        64'hbf4dfe66_0fa30605,
        64'hbf6900c8_063b8082,
        64'h00b7ea63_0006879b,
        64'hfff5081b_46810015,
        64'h559b0006_802340e6,
        64'h853b0685_00f68023,
        64'h02d00793_00088763,
        64'h96aa9101_02079513,
        64'h9f8d00b7_e6634501,
        64'h04f56263_00c8053b,
        64'h03000313_40e0083b,
        64'h863640e6_85bbfcb3,
        64'h7fe302b3_553b0685,
        64'h00c68023_0ff67613,
        64'h0306061b_06ae6563,
        64'h0ff57613_02b5753b,
        64'h0005031b_385986ba,
        64'h4e250ff6_f8130410,
        64'h0693c219_06100693,
        64'h488540a0_053be681,
        64'h00055663_4881bfe1,
        64'h00c70023_07850006,
        64'h460300f6_863300c3,
        64'hb8230017_06138082,
        64'h00070023_00a66563,
        64'h0103b703_0007861b,
        64'h478140f5_853b35fd,
        64'h00c77563_92018f1d,
        64'hfff58713_02051613,
        64'h8f990003_b583852e,
        64'h86aa0103_b7830083,
        64'hb7038082_45018082,
        64'h00078023_45050103,
        64'hb78300a7_002300f3,
        64'hb8230017_079300d7,
        64'hfe639381_17822785,
        64'h40f707b3_0003b683,
        64'h0083b783_0103b703,
        64'h80826105_64a26442,
        64'h60e2557d_e31ff0ef,
        64'h00940563_45018ce1,
        64'h408000ef_200085b7,
        64'h92010206_96130096,
        64'h969b6f84_0007bc23,
        64'hdf758b41_6b980cc0,
        64'h000fef98_347d852e,
        64'h470500d4_143beb98,
        64'h44059301_0007b423,
        64'h02069713_e3909201,
        64'h200007b7_e426ec06,
        64'he8221602_1101bfe9,
        64'h87a28082_61054501,
        64'h690264a2_644260e2,
        64'he9dff0ef_00941b63,
        64'hea5ff0ef_00878f63,
        64'h24010209_34030f00,
        64'h04932000_093757fd,
        64'h0cc0000f_fb984705,
        64'h0207b823_0207b423,
        64'h0207b023_0007bc23,
        64'h0007b823_0007b423,
        64'h0007b023_200007b7,
        64'he04ae426_e822ec06,
        64'h11018082_610d690a,
        64'h64aa644a_60ea3ce0,
        64'h00ef66a5_051387a6,
        64'h0834e43e_e04a0000,
        64'h0517603c_03043883,
        64'h02843803_6c186410,
        64'h600c3ce0_00ef854a,
        64'h68058593_00000597,
        64'h01048913_7c103e20,
        64'h00ef8526_69458593,
        64'h00000597_84c48493,
        64'h00001497_70102000,
        64'h043746a0_00ef0828,
        64'h6a858593_00000597,
        64'hc8010804_741347e0,
        64'h00ef0828_6b458593,
        64'h00000597_cb810404,
        64'h77934920_00ef0828,
        64'h6b858593_00000597,
        64'hcb810204_77934a60,
        64'h00ef0828_6bc58593,
        64'h00000597_cb810104,
        64'h77934ba0_00ef0828,
        64'h6c858593_00000597,
        64'hcb810084_77934ce0,
        64'h00ef0828_6d458593,
        64'h00000597_cb810044,
        64'h77934e20_00ef0828,
        64'h6e058593_00000597,
        64'hcb810024_77934f60,
        64'h00ef0828_6ec58593,
        64'h00000597_cb818b85,
        64'h00010c23_e14ae526,
        64'h0007841b_ed06e922,
        64'h71356b9c_200007b7,
        64'h80820207_a0231000,
        64'h07b78082_25014388,
        64'hc390c38c_c3880107,
        64'ha023c398_0117a023,
        64'hc3940067_a02301c7,
        64'ha023c394_c398c398,
        64'h01d7a023_01e7a023,
        64'hc3d04629_c3cc45b5,
        64'hc3c80210_05130107,
        64'ha2230640_0813c3d8,
        64'h0117a223_07200893,
        64'hc3d40067_a2230570,
        64'h031301c7_a2230200,
        64'h0e13c3d4_06f00693,
        64'hc3d8c3d8_06c00713,
        64'h01d7a223_06500e93,
        64'h01e7a223_04800f13,
        64'h100007b7_80820ff5,
        64'h75130007_4503c789,
        64'h8b85557d_01474783,
        64'h10000737_80826105,
        64'h60e2ed1f_f0ef0091,
        64'h4503ed9f_f0ef0081,
        64'h4503f55f_f0efec06,
        64'h002c1101_80826145,
        64'h694264e2_740270a2,
        64'hff2410e3_efbff0ef,
        64'h00914503_f03ff0ef,
        64'h34610081_4503f81f,
        64'hf0ef0ff5_7513002c,
        64'h0084d533_59610380,
        64'h041384aa_f406e84a,
        64'hec26f022_71798082,
        64'h61456942_64e27402,
        64'h70a2ff24_10e3f3df,
        64'hf0ef0091_4503f45f,
        64'hf0ef3461_00814503,
        64'hfc3ff0ef_0ff57513,
        64'h002c0084_d53b5961,
        64'h446184aa_f406e84a,
        64'hec26f022_71798082,
        64'h00f58023_0007c783,
        64'h00e580a3_97aa8111,
        64'h00074703_973e00f5,
        64'h77139727_87930000,
        64'h1797b7f5_0405f95f,
        64'hf0ef8082_01416402,
        64'h60a2e509_00044503,
        64'h842ae406_e0221141,
        64'h808200e7_88230200,
        64'h071300e7_8423571d,
        64'h00e78623_470d00a7,
        64'h82230ff5_751300e7,
        64'h80230085_551b0ff5,
        64'h771300e7_8623f800,
        64'h07130007_82231000,
        64'h07b702b5_553b0045,
        64'h959b8082_00a70023,
        64'hdfe50207_f7930147,
        64'h47831000_07378082,
        64'h02057513_0147c503,
        64'h100007b7_80820ff5,
        64'h75130005_45038082,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'hffdff06f_10500073,
        64'h34102373_342022f3,
        64'h07d000ef_30579073,
        64'h01078793_00000797,
        64'hfec6c6e3_02068693,
        64'h0006bc23_0006b823,
        64'h0006b423_0006b023,
        64'h000580b3_01f59593,
        64'h0010059b_000600e7,
        64'h40e60633_f9c70713,
        64'h00000717_00e60633,
        64'h01c70713_00000717,
        64'h01f61613_0010061b,
        64'hfcc5cce3_02068693,
        64'h02058593_00e6bc23,
        64'h0185b703_00e6b823,
        64'h0105b703_00e6b423,
        64'h0085b703_00e6b023,
        64'h0005b703_01f69693,
        64'h0010069b_00c58633,
        64'h00008637_ff458593,
        64'h00000597_ff810113,
        64'h01b11113_0110011b
    };

    logic [$clog2(RomSize)-1:0] addr_q;

    always_ff @(posedge clk_i) begin
        if (req_i) begin
            addr_q <= addr_i[$clog2(RomSize)-1+3:3];
        end
    end

    // this prevents spurious Xes from propagating into
    // the speculative fetch stage of the core
    assign rdata_o = (addr_q < RomSize) ? mem[addr_q] : '0;
endmodule
