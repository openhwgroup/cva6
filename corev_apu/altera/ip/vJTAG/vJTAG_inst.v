	vJTAG u0 (
		.tdi                (_connected_to_tdi_),                //  output,   width = 1, jtag.tdi
		.tdo                (_connected_to_tdo_),                //   input,   width = 1,     .tdo
		.ir_in              (_connected_to_ir_in_),              //  output,  width = 10,     .ir_in
		.ir_out             (_connected_to_ir_out_),             //   input,  width = 10,     .ir_out
		.virtual_state_cdr  (_connected_to_virtual_state_cdr_),  //  output,   width = 1,     .virtual_state_cdr
		.virtual_state_sdr  (_connected_to_virtual_state_sdr_),  //  output,   width = 1,     .virtual_state_sdr
		.virtual_state_e1dr (_connected_to_virtual_state_e1dr_), //  output,   width = 1,     .virtual_state_e1dr
		.virtual_state_pdr  (_connected_to_virtual_state_pdr_),  //  output,   width = 1,     .virtual_state_pdr
		.virtual_state_e2dr (_connected_to_virtual_state_e2dr_), //  output,   width = 1,     .virtual_state_e2dr
		.virtual_state_udr  (_connected_to_virtual_state_udr_),  //  output,   width = 1,     .virtual_state_udr
		.virtual_state_cir  (_connected_to_virtual_state_cir_),  //  output,   width = 1,     .virtual_state_cir
		.virtual_state_uir  (_connected_to_virtual_state_uir_),  //  output,   width = 1,     .virtual_state_uir
		.tms                (_connected_to_tms_),                //  output,   width = 1,     .tms
		.jtag_state_tlr     (_connected_to_jtag_state_tlr_),     //  output,   width = 1,     .jtag_state_tlr
		.jtag_state_rti     (_connected_to_jtag_state_rti_),     //  output,   width = 1,     .jtag_state_rti
		.jtag_state_sdrs    (_connected_to_jtag_state_sdrs_),    //  output,   width = 1,     .jtag_state_sdrs
		.jtag_state_cdr     (_connected_to_jtag_state_cdr_),     //  output,   width = 1,     .jtag_state_cdr
		.jtag_state_sdr     (_connected_to_jtag_state_sdr_),     //  output,   width = 1,     .jtag_state_sdr
		.jtag_state_e1dr    (_connected_to_jtag_state_e1dr_),    //  output,   width = 1,     .jtag_state_e1dr
		.jtag_state_pdr     (_connected_to_jtag_state_pdr_),     //  output,   width = 1,     .jtag_state_pdr
		.jtag_state_e2dr    (_connected_to_jtag_state_e2dr_),    //  output,   width = 1,     .jtag_state_e2dr
		.jtag_state_udr     (_connected_to_jtag_state_udr_),     //  output,   width = 1,     .jtag_state_udr
		.jtag_state_sirs    (_connected_to_jtag_state_sirs_),    //  output,   width = 1,     .jtag_state_sirs
		.jtag_state_cir     (_connected_to_jtag_state_cir_),     //  output,   width = 1,     .jtag_state_cir
		.jtag_state_sir     (_connected_to_jtag_state_sir_),     //  output,   width = 1,     .jtag_state_sir
		.jtag_state_e1ir    (_connected_to_jtag_state_e1ir_),    //  output,   width = 1,     .jtag_state_e1ir
		.jtag_state_pir     (_connected_to_jtag_state_pir_),     //  output,   width = 1,     .jtag_state_pir
		.jtag_state_e2ir    (_connected_to_jtag_state_e2ir_),    //  output,   width = 1,     .jtag_state_e2ir
		.jtag_state_uir     (_connected_to_jtag_state_uir_),     //  output,   width = 1,     .jtag_state_uir
		.tck                (_connected_to_tck_)                 //  output,   width = 1,  tck.clk
	);

