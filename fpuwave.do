onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /ariane_tb/dut/i_ariane/ex_stage_i/pc_i
add wave -noupdate -divider {HandShake In}
add wave -noupdate /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/Op_SI
add wave -noupdate /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/InValid_SI
add wave -noupdate /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/InReady_SO
add wave -noupdate /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/A_DI
add wave -noupdate /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/B_DI
add wave -noupdate /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/C_DI
add wave -noupdate /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/Tag_DI
add wave -noupdate -divider {HandShake Out}
add wave -noupdate /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/OutValid_SO
add wave -noupdate /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/OutReady_SI
add wave -noupdate /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/result_o
add wave -noupdate /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/Tag_DO
add wave -noupdate -divider Unit
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/Clk_CI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/Reset_RBI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/A_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/B_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/C_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/ABox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/BBox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/CBox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/RoundMode_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/Op_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/OpMod_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/VectorialOp_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/FpFmt_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/Tag_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/InValid_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/InReady_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/Flush_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/Z_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/Status_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/Tag_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/Zext_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/OutValid_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/OutReady_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/FmtInReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/FmtOutResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/FmtOutStatus_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/FmtOutTags_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/FmtOutValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/FmtOutReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/FmtOutResult2d_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/ArbInResults_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/FmtOutTags2d_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/ArbInStatus_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/ArbInTags_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/ArbInValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/ArbInReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/OutValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/OutputProcessed_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/RoundRobin_SP
add wave -noupdate -expand -group Wrapper -expand -group Top -group AddMul /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_addmul_block/RoundRobin_SN
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/Clk_CI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/Reset_RBI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/A_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/ABox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/RoundMode_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/SrcFmt_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/DstFmt_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/Tag_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/InValid_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/InReady_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/Flush_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/Z_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/Status_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/Tag_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/Zext_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/OutValid_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/OutReady_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/SrcFmt_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/DstFmt_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/Sign_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f -expand /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/FmtInputExp_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/InputExp_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f -expand /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/FmtInputMant_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/InputMant_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/InputMantZero_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/InputZero_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/InputInf_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/InputNan_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/SigNan_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/InputNormal_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/OFBeforeRound_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/OFAfterRound_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/UFAfterRound_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/SpecialRes_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/SpecialResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/SpecialStatus_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/MantLeadingZeroes_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/ExpNormShift_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/InternalExp_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/InternalMant_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f -radix decimal /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/DestExp_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/FinalExp_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/MantPreshift_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/ShiftedMant_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/FinalMant_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f -radix decimal /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/MantShamt_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/FmtPreRndRes_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/PreRndRes_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/RoundSticky_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/ResRounded_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/ResRoundedSignCorr_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/RegularStatus_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/Result_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -group f2f /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/g_f2f/i_fp_f2fcasts/Status_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 -divider <NULL>
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/Clk_CI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/Reset_RBI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/A_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/ABox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/RoundMode_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/Op_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/OpMod_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/FpFmt_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/FpFmt2_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/IntFmt_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/Tag_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/InValid_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/InReady_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/Flush_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/Z_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/Status_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/Tag_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/Zext_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/OutValid_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/OutReady_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/OutReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2IInValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/I2FInValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2FInValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2IInReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/I2FInReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2FInReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2IOutResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/I2FOutResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2FOutResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2IOutStatus_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/I2FOutStatus_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2FOutStatus_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2IResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/I2FResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2FResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2IOutTag_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/I2FOutTag_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2FOutTag_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2IZext_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/I2FZext_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2FZext_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2IOutValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/I2FOutValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/F2FOutValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/Result_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/Status_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/Zext_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/TagInt_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/TagIntPiped_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi -group Lane0 /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_conv_multi/OutValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/Clk_CI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/Reset_RBI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/A_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/B_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/C_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/ABox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/BBox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/CBox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/RoundMode_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/Op_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/OpMod_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/FpFmt_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/FpFmt2_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/IntFmt_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/VectorialOp_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/Tag_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/InValid_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/InReady_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/Flush_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/Z_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/Status_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/Tag_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/Zext_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/OutValid_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/OutReady_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/Target_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/SrcFmtWidth_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/DstFmtSlv_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/IsDstFmtInt_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/SrcShift_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/DstShift_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/DstCPK_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/TagInt_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/VecTag_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/DstVecTag_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/VectorialOp_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/TargetInValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/TargetOutReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/FmtOpResults_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/IntFmtOpResults_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/LaneResults_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/ResultVectorial_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/IsResultFmtInt_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/IsResultCPK_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/ResultShift_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/ResultFpFmt_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/ResultIntFmt_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/LaneStatus_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/LaneOutValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/LaneInReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/LaneZext_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/LaneTags_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/TargetDelayed_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv -expand -group Multi /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/g_mergedOps/i_conv_multifmt_slice/PackedResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/Clk_CI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/Reset_RBI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/A_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/B_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/C_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/ABox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/BBox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/CBox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/RoundMode_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/Op_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/OpMod_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/FpFmt_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/FpFmt2_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/IntFmt_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/VectorialOp_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/Tag_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/InValid_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/InReady_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/Flush_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/Z_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/Status_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/Tag_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/Zext_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/OutValid_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/OutReady_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/FmtInReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/FmtOutResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/FmtOutStatus_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/FmtOutTags_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/FmtOutZext_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/FmtOutValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/FmtOutReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/FmtOutResult2d_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/ArbInResults_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/FmtOutTags2d_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/ArbInStatus_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/ArbInTags_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/ArbInValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/ArbInReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/OutValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/OutputProcessed_S
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/ArbOutTag_D
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/RoundRobin_SP
add wave -noupdate -expand -group Wrapper -expand -group Top -group Conv /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_conv_block/RoundRobin_SN
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Clk_CI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Rst_RBI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Div_start_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Sqrt_start_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Operand_a_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Operand_b_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/RM_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Precision_ctl_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Format_sel_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Kill_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Result_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Fflags_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Ready_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Done_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Exp_a_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Exp_b_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Mant_a_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Mant_b_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Exp_z_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Mant_z_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Sign_z_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Start_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/RM_dly_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Div_enable_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Sqrt_enable_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Inf_a_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Inf_b_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Zero_a_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Zero_b_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/NaN_a_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/NaN_b_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/SNaN_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Special_case_SB
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Special_case_dly_SB
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/Full_precision_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/FP32_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/FP64_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/FP16_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -expand -group divsqrt_inst /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_divsqrt/FP16ALT_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/Clk_CI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/Reset_RBI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/A_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/B_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/ABox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/BBox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/RoundMode_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/Op_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/OpMod_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/FpFmt_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/Tag_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/InValid_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/InReady_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/Flush_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/Z_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/Status_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/Tag_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/Zext_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/OutValid_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/OutReady_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/InReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/IsInFP8_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/DivValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/SqrtValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/DivSqrtReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/A_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/B_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/Fmt_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/DivSqrtDone_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/DivSqrtResultPre_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/DivSqrtResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/DivSqrtStatusSlv_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/DivSqrtStatus_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/CurrentTag_DP
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/IsOutFP8_SP
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/HoldResult_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/HoldResult_DP
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/HoldStatus_DP
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/PipeInValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/PipeInReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/PipeInDataSel_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/PipeInResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/PipeInStatus_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/State_DP
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/State_DN
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/Clk_CI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/Reset_RBI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/Result_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/Status_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/Tag_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/InValid_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/InReady_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/Flush_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/ResultPiped_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/StatusPiped_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/TagPiped_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/OutValid_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/OutReady_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/ResPipe_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/StatPipe_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe -expand /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/TagPipe_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/ValidPipe_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt -expand -group Wrapper -group divPipe /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/g_mergedOps/i_divsqrt_multifmt_slice/g_sliceLanes(0)/g_laneInst/i_fp_divsqrt_multi/i_fp_pipe/StageReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/Clk_CI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/Reset_RBI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/A_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/B_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/C_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/ABox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/BBox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/CBox_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/RoundMode_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/OpMod_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/FpFmt_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/VectorialOp_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/Tag_DI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/Flush_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/Z_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/Status_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/Tag_DO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/Zext_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/OutValid_SO
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/OutReady_SI
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/FmtInReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/FmtOutResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/FmtOutStatus_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/FmtOutTags_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/FmtOutZext_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/FmtOutValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/FmtOutReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/FmtOutResult2d_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/ArbInResults_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/FmtOutTags2d_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/ArbInStatus_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/ArbInTags_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/ArbInValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/ArbInReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/OutValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/OutputProcessed_S
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/ArbOutTag_D
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/RoundRobin_SP
add wave -noupdate -expand -group Wrapper -expand -group Top -expand -group DivSqrt /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/i_divsqrt_block/RoundRobin_SN
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/Clk_CI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/Reset_RBI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/A_DI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/B_DI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/C_DI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/RoundMode_SI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/Op_SI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/OpMod_SI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/VectorialOp_SI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/FpFmt_SI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/FpFmt2_SI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/IntFmt_SI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/Tag_DI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/Flush_SI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/InValid_SI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/InReady_SO
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/Z_DO
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/Status_DO
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/OutValid_SO
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/OutReady_SI
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/Tag_DO
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/OpGrpInValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/OpGrpInReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/ABox_S
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/BBox_S
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/CBox_S
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/AddMulResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/DivSqrtResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/NonCompResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/ConvResult_D
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/OpGrpOutResults_D
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/OpGrpOutStatuses_D
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/OpGrpOutTags_D
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/OpGrpOutZext_S
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/OpGrpOutValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/OpGrpOutReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/ArbInResults_D
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/ArbInStatuses_D
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/ArbInTags_D
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/ArbInValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/ArbInReady_S
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/OutValid_S
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/OutputProcessed_S
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/RoundRobin_SP
add wave -noupdate -expand -group Wrapper -expand -group Top /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/RoundRobin_SN
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/clk_i
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/rst_ni
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/flush_i
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/trans_id_i
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fu_i
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_valid_i
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_ready_o
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/operator_i
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/operand_a_i
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/operand_b_i
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/operand_c_i
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_fmt_i
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_rm_i
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_frm_i
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_trans_id_o
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/result_o
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_valid_o
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_exception_o
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/operand_a_d
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/operand_a_q
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/operand_a
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/operand_b_d
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/operand_b_q
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/operand_b
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/operand_c_d
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/operand_c_q
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/operand_c
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_op_d
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_op_q
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_op
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_op_mod_d
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_op_mod_q
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_op_mod
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_fmt_d
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_fmt_q
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_fmt
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_fmt2_d
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_fmt2_q
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_fmt2
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_ifmt_d
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_ifmt_q
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_ifmt
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_rm_d
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_rm_q
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_rm
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_vec_op_d
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_vec_op_q
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_vec_op
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_tag_d
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_tag_q
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_tag
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_in_ready
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_in_valid
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_out_ready
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_out_valid
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/fpu_status
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/state_q
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/state_d
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/hold_inputs
add wave -noupdate -expand -group Wrapper /ariane_tb/dut/i_ariane/ex_stage_i/fpu_gen/fpu_i/use_hold
add wave -noupdate -divider Ariane
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/clk_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/rst_ni
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/flush_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/issue_instr_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/issue_instr_valid_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/issue_ack_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/rs1_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/rs1_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/rs1_valid_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/rs2_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/rs2_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/rs2_valid_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/rs3_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/rs3_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/rs3_valid_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/rd_clobber_gpr_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/rd_clobber_fpr_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fu_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/operator_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/operand_a_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/operand_b_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/imm_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/trans_id_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/pc_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/is_compressed_instr_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/alu_ready_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/alu_valid_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/branch_valid_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/branch_predict_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/lsu_ready_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/lsu_valid_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/mult_ready_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/mult_valid_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fpu_ready_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fpu_valid_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fpu_fmt_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fpu_rm_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/csr_valid_o
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/waddr_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/wdata_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/we_gpr_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/we_fpr_i
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/stall
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fu_busy
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/operand_a_regfile
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/operand_b_regfile
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/operand_c_regfile
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/operand_a_n
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/operand_a_q
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/operand_b_n
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/operand_b_q
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/imm_n
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/imm_q
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/alu_valid_n
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/alu_valid_q
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/mult_valid_n
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/mult_valid_q
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fpu_valid_n
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fpu_valid_q
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fpu_fmt_n
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fpu_fmt_q
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fpu_rm_n
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fpu_rm_q
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/lsu_valid_n
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/lsu_valid_q
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/csr_valid_n
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/csr_valid_q
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/branch_valid_n
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/branch_valid_q
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/trans_id_n
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/trans_id_q
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/operator_n
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/operator_q
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fu_n
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fu_q
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/forward_rs1
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/forward_rs2
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/forward_rs3
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/orig_instr
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/rdata
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/raddr_pack
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/waddr_pack
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/wdata_pack
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/we_pack
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands -expand /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fprdata
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fp_raddr_pack
add wave -noupdate -expand -group {Issue stage} -group Issue_Read_Operands /ariane_tb/dut/i_ariane/issue_stage_i/i_issue_read_operands/fp_wdata_pack
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/clk_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/rst_ni
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/flush_unissued_instr_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/flush_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/decoded_instr_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/decoded_instr_valid_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/is_ctrl_flow_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/decoded_instr_ack_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/fu_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/operator_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/operand_a_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/operand_b_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/imm_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/trans_id_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/pc_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/is_compressed_instr_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/alu_ready_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/alu_valid_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/resolve_branch_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/lsu_ready_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/lsu_valid_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/branch_valid_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/branch_predict_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/mult_ready_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/mult_valid_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/fpu_ready_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/fpu_valid_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/fpu_fmt_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/fpu_rm_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/csr_valid_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/trans_id_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/resolved_branch_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/wbdata_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/ex_ex_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/wb_valid_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/waddr_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/wdata_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/we_gpr_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/we_fpr_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/commit_instr_o
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/commit_ack_i
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/rd_clobber_gpr_sb_iro
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/rd_clobber_fpr_sb_iro
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/rs1_iro_sb
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/rs1_sb_iro
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/rs1_valid_sb_iro
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/rs2_iro_sb
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/rs2_sb_iro
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/rs2_valid_iro_sb
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/rs3_iro_sb
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/rs3_sb_iro
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/rs3_valid_iro_sb
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/issue_instr_rename_sb
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/issue_instr_valid_rename_sb
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/issue_ack_sb_rename
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/issue_instr_sb_iro
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/issue_instr_valid_sb_iro
add wave -noupdate -expand -group {Issue stage} /ariane_tb/dut/i_ariane/issue_stage_i/issue_ack_iro_sb
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/clk_i
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/rst_ni
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/flush_unissued_instr_i
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/flush_i
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/unresolved_branch_i
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/rd_clobber_gpr_o
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/rd_clobber_fpr_o
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/rs1_i
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/rs1_o
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/rs1_valid_o
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/rs2_i
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/rs2_o
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/rs2_valid_o
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/rs3_i
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/rs3_o
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/rs3_valid_o
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/commit_instr_o
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/commit_ack_i
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/decoded_instr_i
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/decoded_instr_valid_i
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/decoded_instr_ack_o
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/issue_instr_o
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/issue_instr_valid_o
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/issue_ack_i
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/trans_id_i
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/wbdata_i
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/ex_i
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/wb_valid_i
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/issue_cnt_n
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/issue_cnt_q
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/issue_pointer_n
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/issue_pointer_q
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/commit_pointer_n
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/commit_pointer_q
add wave -noupdate -expand -group {Issue stage} -group ScoreBoard /ariane_tb/dut/i_ariane/issue_stage_i/i_scoreboard/issue_full
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/clk_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/rst_ni
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/flush_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/fu_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/operator_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/operand_a_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/operand_b_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/imm_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/trans_id_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/pc_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/is_compressed_instr_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/alu_ready_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/alu_valid_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/alu_valid_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/alu_result_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/alu_trans_id_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/alu_exception_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/branch_valid_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/branch_predict_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/resolved_branch_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/resolve_branch_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/csr_valid_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/csr_addr_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/csr_commit_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/lsu_ready_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/lsu_valid_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/lsu_valid_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/lsu_result_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/lsu_trans_id_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/lsu_commit_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/lsu_commit_ready_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/lsu_exception_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/no_st_pending_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/amo_valid_commit_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/mult_ready_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/mult_valid_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/mult_trans_id_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/mult_result_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/mult_valid_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/fpu_ready_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/fpu_valid_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/fpu_fmt_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/fpu_rm_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/fpu_frm_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/fpu_trans_id_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/fpu_result_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/fpu_valid_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/fpu_exception_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/enable_translation_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/en_ld_st_translation_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/flush_tlb_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/priv_lvl_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/ld_st_priv_lvl_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/sum_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/mxr_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/satp_ppn_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/asid_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/icache_areq_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/icache_areq_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/dcache_req_ports_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/dcache_req_ports_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/amo_req_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/amo_resp_i
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/itlb_miss_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/dtlb_miss_o
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/alu_branch_res
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/alu_data
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/mult_data
add wave -noupdate -group {EX stage} /ariane_tb/dut/i_ariane/ex_stage_i/lsu_data
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/pc_i
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/is_compressed_i
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/is_illegal_i
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/instruction_i
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/branch_predict_i
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/ex_i
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/priv_lvl_i
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/debug_mode_i
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/fs_i
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/frm_i
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/tvm_i
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/tw_i
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/tsr_i
add wave -noupdate -expand -group Decoder -expand /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/instruction_o
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/is_control_flow_instr_o
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/illegal_instr
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/ecall
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/ebreak
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/check_fprm
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/instr
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/imm_select
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/imm_i_type
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/imm_s_type
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/imm_sb_type
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/imm_u_type
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/imm_uj_type
add wave -noupdate -expand -group Decoder /ariane_tb/dut/i_ariane/id_stage_i/decoder_i/imm_bi_type
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 6} {25911563 ns} 1} {{Cursor 3} {25812676 ns} 0}
quietly wave cursor active 2
configure wave -namecolwidth 259
configure wave -valuecolwidth 178
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {25810978 ns} {25815752 ns}
