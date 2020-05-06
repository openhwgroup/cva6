onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb/AcqTrig_T
add wave -noupdate /tb/C_ACQ_DEL
add wave -noupdate /tb/C_APPL_DEL
add wave -noupdate /tb/C_CLK_HI
add wave -noupdate /tb/C_CLK_LO
add wave -noupdate /tb/C_LOG_WIDTH
add wave -noupdate /tb/C_WIDTH
add wave -noupdate /tb/Clk_CI
add wave -noupdate /tb/EndOfSim_T
add wave -noupdate /tb/InRdy_SO
add wave -noupdate /tb/InVld_SI
add wave -noupdate /tb/NumStim_T
add wave -noupdate /tb/OpA_DI
add wave -noupdate /tb/OpA_T
add wave -noupdate /tb/OpBShift_DI
add wave -noupdate /tb/OpBSign_SI
add wave -noupdate /tb/OpB_DI
add wave -noupdate /tb/OpB_T
add wave -noupdate /tb/OpCode_SI
add wave -noupdate /tb/OutRdy_SI
add wave -noupdate /tb/OutVld_SO
add wave -noupdate /tb/Res_DO
add wave -noupdate /tb/Rst_RBI
add wave -noupdate /tb/StimEnd_T
add wave -noupdate /tb/StimStart_T
add wave -noupdate /tb/TestName_T
add wave -noupdate -divider internal
add wave -noupdate /tb/i_mut/Clk_CI
add wave -noupdate /tb/i_mut/Rst_RBI
add wave -noupdate /tb/i_mut/OpA_DI
add wave -noupdate /tb/i_mut/OpB_DI
add wave -noupdate -radix unsigned /tb/i_mut/OpBShift_DI
add wave -noupdate /tb/i_mut/OpBSign_SI
add wave -noupdate /tb/OpBIsZero_SI
add wave -noupdate /tb/i_mut/OpCode_SI
add wave -noupdate /tb/i_mut/InVld_SI
add wave -noupdate /tb/i_mut/InRdy_SO
add wave -noupdate /tb/i_mut/OutRdy_SI
add wave -noupdate /tb/i_mut/OutVld_SO
add wave -noupdate -radix decimal /tb/i_mut/Res_DO
add wave -noupdate /tb/i_mut/ResReg_DN
add wave -noupdate /tb/i_mut/ResReg_DP
add wave -noupdate /tb/i_mut/AReg_DN
add wave -noupdate -radix decimal /tb/i_mut/AReg_DP
add wave -noupdate /tb/i_mut/BReg_DN
add wave -noupdate -radix decimal /tb/i_mut/BReg_DP
add wave -noupdate /tb/i_mut/RemSel_SN
add wave -noupdate /tb/i_mut/RemSel_SP
add wave -noupdate /tb/i_mut/CompInv_SN
add wave -noupdate /tb/i_mut/CompInv_SP
add wave -noupdate /tb/i_mut/ResInv_SN
add wave -noupdate /tb/i_mut/ResInv_SP
add wave -noupdate /tb/i_mut/AddMux_D
add wave -noupdate /tb/i_mut/AddOut_D
add wave -noupdate /tb/i_mut/BMux_D
add wave -noupdate /tb/i_mut/OutMux_D
add wave -noupdate /tb/i_mut/Cnt_DN
add wave -noupdate /tb/i_mut/Cnt_DP
add wave -noupdate /tb/i_mut/CntZero_S
add wave -noupdate /tb/i_mut/ARegEn_S
add wave -noupdate /tb/i_mut/BRegEn_S
add wave -noupdate /tb/i_mut/ResRegEn_S
add wave -noupdate /tb/i_mut/ABComp_S
add wave -noupdate /tb/i_mut/PmSel_S
add wave -noupdate /tb/i_mut/State_SN
add wave -noupdate /tb/i_mut/State_SP
add wave -noupdate /tb/OpA_DI
add wave -noupdate /tb/OpB_DI
add wave -noupdate /tb/Res_DO
add wave -noupdate /tb/Clk_CI
add wave -noupdate /tb/Rst_RBI
add wave -noupdate /tb/StimStart_T
add wave -noupdate /tb/StimEnd_T
add wave -noupdate /tb/EndOfSim_T
add wave -noupdate /tb/NumStim_T
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {89306315 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 348
configure wave -valuecolwidth 194
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
configure wave -timelineunits ps
update
WaveRestoreZoom {186977012 ps} {187704368 ps}
