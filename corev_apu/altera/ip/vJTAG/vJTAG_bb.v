module vJTAG (
		output wire       tdi,                // jtag.tdi
		input  wire       tdo,                //     .tdo
		output wire [9:0] ir_in,              //     .ir_in
		input  wire [9:0] ir_out,             //     .ir_out
		output wire       virtual_state_cdr,  //     .virtual_state_cdr
		output wire       virtual_state_sdr,  //     .virtual_state_sdr
		output wire       virtual_state_e1dr, //     .virtual_state_e1dr
		output wire       virtual_state_pdr,  //     .virtual_state_pdr
		output wire       virtual_state_e2dr, //     .virtual_state_e2dr
		output wire       virtual_state_udr,  //     .virtual_state_udr
		output wire       virtual_state_cir,  //     .virtual_state_cir
		output wire       virtual_state_uir,  //     .virtual_state_uir
		output wire       tms,                //     .tms
		output wire       jtag_state_tlr,     //     .jtag_state_tlr
		output wire       jtag_state_rti,     //     .jtag_state_rti
		output wire       jtag_state_sdrs,    //     .jtag_state_sdrs
		output wire       jtag_state_cdr,     //     .jtag_state_cdr
		output wire       jtag_state_sdr,     //     .jtag_state_sdr
		output wire       jtag_state_e1dr,    //     .jtag_state_e1dr
		output wire       jtag_state_pdr,     //     .jtag_state_pdr
		output wire       jtag_state_e2dr,    //     .jtag_state_e2dr
		output wire       jtag_state_udr,     //     .jtag_state_udr
		output wire       jtag_state_sirs,    //     .jtag_state_sirs
		output wire       jtag_state_cir,     //     .jtag_state_cir
		output wire       jtag_state_sir,     //     .jtag_state_sir
		output wire       jtag_state_e1ir,    //     .jtag_state_e1ir
		output wire       jtag_state_pir,     //     .jtag_state_pir
		output wire       jtag_state_e2ir,    //     .jtag_state_e2ir
		output wire       jtag_state_uir,     //     .jtag_state_uir
		output wire       tck                 //  tck.clk
	);
endmodule

