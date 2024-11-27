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


`timescale 1 ps / 1 ps

(* altera_attribute = "-name UNCONNECTED_OUTPUT_PORT_MESSAGE_LEVEL OFF" *)
module altera_gpio_one_bit(
	ck,
	ck_in,
	ck_out,
	ck_fr,
	ck_fr_in,
	ck_fr_out,
	ck_hr,
	ck_hr_in,
	ck_hr_out,
	oe,
	din,
	dout,
	pad,
	pad_b,
	terminationcontrol,
	aclr,
	aset,
	sclr,
	sset,
	cke
);

	parameter PIN_TYPE = "output"; 
	parameter BUFFER_TYPE = "single-ended"; 
	parameter PSEUDO_DIFF = "false"; 
	parameter REGISTER_MODE = "none"; 
	parameter HALF_RATE = "false"; 
	parameter SEPARATE_I_O_CLOCKS = "false"; 
	parameter ARESET_MODE = "none"; 
	parameter SRESET_MODE = "none"; 
	parameter BUS_HOLD = "false"; 
	parameter OPEN_DRAIN = "false"; 
	parameter ENABLE_CKE = "false"; 
	parameter ENABLE_OE = "false"; 
	parameter ENABLE_TERM = "false"; 

	localparam OE_SIZE = (HALF_RATE == "true") ? 2 : 1;
	localparam DATA_SIZE = (REGISTER_MODE == "ddr") ? 
			(HALF_RATE == "true") ? 
				4 : 2
			: 1;

	input ck;
	input ck_in;
	input ck_out;
	input ck_fr;
	input ck_fr_in;
	input ck_fr_out;
	input ck_hr;
	input ck_hr_in;
	input ck_hr_out;
	input [OE_SIZE - 1:0] oe;
	input [DATA_SIZE - 1:0] din;
	output [DATA_SIZE - 1:0] dout;
	inout pad;	
	inout pad_b;
	input terminationcontrol;
	input aclr;
	input aset;
	input sclr;
	input sset;
	input cke;

	wire hr_out_clk;
	wire fr_out_clk;
	wire hr_in_clk;
	wire fr_in_clk;

	wire din_ddr;
	wire buf_in;

	wire areset;
	wire sreset;

	generate
		if(ARESET_MODE == "preset") begin
			assign areset = ~aset;
		end
		else begin
			assign areset = ~aclr;
		end
	endgenerate

	generate
		if(SRESET_MODE == "preset") begin
			assign sreset = sset;
		end
		else begin
			assign sreset = sclr;
		end
	endgenerate

	generate
		if(SEPARATE_I_O_CLOCKS == "true") 
		begin
			if(HALF_RATE == "true") begin
				assign hr_out_clk = ck_hr_out;
				assign fr_out_clk = ck_fr_out;
				assign hr_in_clk = ck_hr_in;
				assign fr_in_clk = ck_fr_in;
			end
			else begin
				assign fr_out_clk = ck_out;
				assign fr_in_clk = ck_in;
			end
		end
		else begin
			if(HALF_RATE == "true") begin
				assign hr_out_clk = ck_hr;
				assign fr_out_clk = ck_fr;
				assign hr_in_clk = ck_hr;
				assign fr_in_clk = ck_fr;
			end
			else begin
				assign fr_out_clk = ck;
				assign fr_in_clk = ck;
			end
		end
	endgenerate

    generate
        if (PIN_TYPE == "output" || PIN_TYPE == "bidir")
        begin: out_path
			wire [1:0] din_fr;

            if (HALF_RATE == "true")
            begin: out_path_hr
                tennm_ddio_out
                #(
                	.half_rate_mode("true"),
                	.async_mode(ARESET_MODE)
                ) iodout_hr_ddio_0 (		
			.areset(areset),
                	.datainhi(din[2]),
                	.datainlo(din[0]),
                	.dataout(din_fr[0]),
                	.clk (hr_out_clk)
                );
                
                tennm_ddio_out
                #(
                	.half_rate_mode("true"),
                	.async_mode(ARESET_MODE)
                ) iodout_hr_ddio_1 (	
			.areset(areset),
                	.datainhi(din[3]),
                	.datainlo(din[1]),
                	.dataout(din_fr[1]),
                	.clk (hr_out_clk)
                );
            end
            else
            begin: out_path_hr_byp
                assign din_fr[DATA_SIZE - 1:0] = din;
            end

            if (REGISTER_MODE == "ddr")
            begin: out_path_fr
                tennm_ddio_out
                #(
                	.half_rate_mode("false"),
                	.async_mode(ARESET_MODE),
					.sync_mode(SRESET_MODE)
                ) fr_out_data_ddio (	
			.ena(cke),
			.areset(areset),
			.sreset(sreset),
                	.datainhi(din_fr[1]),
                	.datainlo(din_fr[0]),
                	.dataout(din_ddr),
                	.clk (fr_out_clk)
                );
            end
            else if (REGISTER_MODE == "sdr")
            begin: out_path_reg
                reg reg_data_out;
                always @(posedge fr_out_clk)
                    reg_data_out <= din_fr[0];

                assign din_ddr = reg_data_out;
            end
            else  
            begin: out_path_byp
                assign din_ddr = din_fr[0];
            end
        end
    endgenerate

    generate
		wire oe_fr;
		wire oe_ddr;

        if (PIN_TYPE == "bidir" || ENABLE_OE == "true")
        begin: oe_path
            if (HALF_RATE == "true")
            begin: oe_path_hr
                tennm_ddio_out
                #(
                	.half_rate_mode("true")
                ) oe_in_hr_ddio (
                	.datainhi(oe[1]),
                	.datainlo(oe[0]),
                	.dataout(oe_fr),
                	.clk (hr_out_clk)
                );
            end
            else
            begin: oe_path_hr_byp
                assign oe_fr = oe[0];
            end

            if (REGISTER_MODE == "sdr" || REGISTER_MODE == "ddr")
            begin: oe_path_fr
	            reg oe_reg;
                always @(posedge fr_out_clk) oe_reg <= oe_fr;
                assign oe_ddr = oe_reg;
            end
            else 
            begin: oe_path_byp
                assign oe_ddr = oe_fr;
            end
        end
        else if (PIN_TYPE == "output")  
        begin
            assign oe_ddr = 1'b1;
        end
        else    
        begin
            assign oe_ddr = 1'b0;
        end
    endgenerate

    generate
        if (PIN_TYPE == "input" || PIN_TYPE == "bidir")
        begin : input_path
            wire [1:0] buf_in_fr;

            if (REGISTER_MODE == "ddr")
            begin: in_path_fr
                tennm_ddio_in
                #(
                	.async_mode(ARESET_MODE),
                	.sync_mode(SRESET_MODE)
                ) buffer_data_in_fr_ddio (
			.ena(cke),
			.areset(areset),
			.sreset(sreset),
                	.datain(buf_in),
                	.clk (fr_in_clk),
                	.regouthi(buf_in_fr[1]),
                	.regoutlo(buf_in_fr[0])
                );
            end
            else if (REGISTER_MODE == "sdr")
            begin: in_path_reg
                reg ro;
                always @(posedge fr_in_clk) begin
                    ro <= buf_in;
                end
                assign buf_in_fr[0] = ro;
            end
            else
            begin: in_byp
                assign buf_in_fr[0] = buf_in;
            end
            
            if (HALF_RATE == "true")
            begin: in_path_hr
                tennm_ddio_in
                #(
                	.async_mode(ARESET_MODE),
                	.sync_mode("none")
                ) buffer_data_in_hr_ddio_0 (
			.areset(areset),
                	.datain(buf_in_fr[0]),
                	.clk (hr_in_clk),
                	.regouthi(dout[2]),
                	.regoutlo(dout[0])
                );
                
                tennm_ddio_in
                #(
                	.async_mode(ARESET_MODE),
                	.sync_mode("none")
                ) buffer_data_in_hr_ddio_1 (
			.areset(areset),
                	.datain(buf_in_fr[1]),
                	.clk (hr_in_clk),
                	.regouthi(dout[3]),
                	.regoutlo(dout[1])
                );
            end
            else
            begin: in_path_hr_byp
                assign dout[DATA_SIZE - 1:0] = buf_in_fr[DATA_SIZE - 1:0];
            end
        end
    endgenerate

	generate
		if (PIN_TYPE == "output" || PIN_TYPE == "bidir")
		begin : output_buffer
			if(BUFFER_TYPE == "differential") begin
				wire obuf_din; 
				wire obuf_din_b; 
				wire obuf_oe; 
				wire obuf_oe_b; 

				if(PSEUDO_DIFF == "true") begin
					if (PIN_TYPE == "output" && ENABLE_OE == "false")
					begin : oe_path
						tennm_pseudo_diff_out pseudo_diff_out(
							.i(din_ddr),
							.o(obuf_din),
							.obar(obuf_din_b)
						);

						if (ENABLE_TERM == "true") begin
							tennm_io_obuf #(
								.open_drain_output(OPEN_DRAIN),
								.bus_hold(BUS_HOLD)
							) obuf_0 (
								.term_in(terminationcontrol),
								.i(obuf_din), 
								.o(pad)
							); 		
							
							tennm_io_obuf #(
								.open_drain_output(OPEN_DRAIN),
								.bus_hold(BUS_HOLD)
							) obuf_1 (
								.term_in(terminationcontrol),
								.i(obuf_din_b), 
								.o(pad_b)
							); 		
						end
						else begin
							tennm_io_obuf #(
								.open_drain_output(OPEN_DRAIN),
								.bus_hold(BUS_HOLD)
							) obuf_0 (
								.i(obuf_din), 
								.o(pad)
							); 		
							
							tennm_io_obuf #(
								.open_drain_output(OPEN_DRAIN),
								.bus_hold(BUS_HOLD)
							) obuf_1 (
								.i(obuf_din_b), 
								.o(pad_b)
							); 	
						end
					end
					else begin
						tennm_pseudo_diff_out pseudo_diff_out(
							.i(din_ddr),
							.o(obuf_din),
							.obar(obuf_din_b),
							.oein(oe_ddr),
							.oeout(obuf_oe),
							.oebout(obuf_oe_b)
						);
						if (ENABLE_TERM == "true") begin
							tennm_io_obuf #(
								.open_drain_output(OPEN_DRAIN),
								.bus_hold(BUS_HOLD)
							) obuf_0 (
								.term_in(terminationcontrol),
								.i(obuf_din), 
								.oe(obuf_oe),
								.o(pad)
							);
							
							tennm_io_obuf #(
								.open_drain_output(OPEN_DRAIN),
								.bus_hold(BUS_HOLD)
							) obuf_1 (
								.term_in(terminationcontrol),
								.i(obuf_din_b), 
								.oe(obuf_oe_b),
								.o(pad_b)
							); 	
						end
						else begin
							tennm_io_obuf #(
								.open_drain_output(OPEN_DRAIN),
								.bus_hold(BUS_HOLD)
							) obuf_0 (
								.i(obuf_din), 
								.oe(obuf_oe),
								.o(pad)
							);
							
							tennm_io_obuf #(
								.open_drain_output(OPEN_DRAIN),
								.bus_hold(BUS_HOLD)
							) obuf_1 (
								.i(obuf_din_b), 
								.oe(obuf_oe_b),
								.o(pad_b)
							); 	
						end
					end
				end
				else begin
					if (ENABLE_TERM == "true") begin
						tennm_io_obuf #(
							.open_drain_output(OPEN_DRAIN),
							.bus_hold(BUS_HOLD)
						) obuf_0 (
							.term_in(terminationcontrol),
							.i(din_ddr), 
							.o(pad),
							.obar(pad_b)
						); 		
					end
					else begin
						tennm_io_obuf #(
							.open_drain_output(OPEN_DRAIN),
							.bus_hold(BUS_HOLD)
						) obuf_0 (
							.i(din_ddr), 
							.o(pad),
							.obar(pad_b)
						); 
					end

				end
			end
			else begin
				if (PIN_TYPE == "bidir" || ENABLE_OE == "true") begin
					if (ENABLE_TERM == "true") begin
						tennm_io_obuf #(
							.open_drain_output(OPEN_DRAIN),
							.bus_hold(BUS_HOLD)
						) obuf (
							.term_in(terminationcontrol),
							.i(din_ddr), 
							.oe(oe_ddr),
							.o(pad)
						); 		
					end
					else begin
						tennm_io_obuf #(
							.open_drain_output(OPEN_DRAIN),
							.bus_hold(BUS_HOLD)
						) obuf (
							.i(din_ddr), 
							.oe(oe_ddr),
							.o(pad)
						); 
					end
				end
				else begin
					if (ENABLE_TERM == "true") begin
					tennm_io_obuf #(
						.open_drain_output(OPEN_DRAIN),
						.bus_hold(BUS_HOLD)
					) obuf (
						.term_in(terminationcontrol),
						.i(din_ddr), 
						.o(pad)
					); 		
					end
					else begin
						tennm_io_obuf #(
							.open_drain_output(OPEN_DRAIN),
							.bus_hold(BUS_HOLD)
						) obuf (
							.i(din_ddr), 
							.o(pad)
						); 
					end
				end
			end
		end
	endgenerate

	generate
		if (PIN_TYPE == "input" || PIN_TYPE == "bidir")
		begin : input_buffer
			if(BUFFER_TYPE == "differential") begin
				if (ENABLE_TERM == "true") begin
					tennm_io_ibuf 
					#(
						.differential_mode("true"),
						.bus_hold(BUS_HOLD)
					) ibuf (
						.i(pad),
						.ibar(pad_b),
						.term_in(terminationcontrol),
						.o(buf_in)
					);         
				end
				else begin
					tennm_io_ibuf 
					#(
						.differential_mode("true"),
						.bus_hold(BUS_HOLD)
					) ibuf (
						.i(pad),
						.ibar(pad_b),
						.o(buf_in)
					);         
				end
			end
			else begin
				if (ENABLE_TERM == "true") begin
					tennm_io_ibuf 
					#(
						.differential_mode("false"),
						.bus_hold(BUS_HOLD)
					) ibuf (
						.i(pad),
						.term_in(terminationcontrol),
						.o(buf_in)
					);         
				end
				else begin
					tennm_io_ibuf 
					#(
						.differential_mode("false"),
						.bus_hold(BUS_HOLD)
					) ibuf (
						.i(pad),
						.o(buf_in)
					);  
				end
			end
		end
	endgenerate

endmodule

(* altera_attribute = "-name UNCONNECTED_OUTPUT_PORT_MESSAGE_LEVEL OFF" *)
module altera_gpio(
	ck,
	ck_in,
	ck_out,
	ck_fr,
	ck_fr_in,
	ck_fr_out,
	ck_hr,
	ck_hr_in,
	ck_hr_out,
	oe,
	din,
	dout,
	pad_io,
	pad_io_b,
	pad_in,
	pad_in_b,
	pad_out,
	pad_out_b,
	terminationcontrol,
	aclr,
	aset,
	sclr,
	sset,
	cke
);

	parameter PIN_TYPE = "output"; 
	parameter BUFFER_TYPE = "single-ended"; 
	parameter PSEUDO_DIFF = "false"; 
	parameter REGISTER_MODE = "none"; 
	parameter HALF_RATE = "false"; 
	parameter SEPARATE_I_O_CLOCKS = "false"; 
	parameter SIZE = 4;
	parameter ARESET_MODE = "none"; 
	parameter SRESET_MODE = "none"; 
	parameter BUS_HOLD = "false"; 
	parameter OPEN_DRAIN = "false"; 
	parameter ENABLE_CKE = "false"; 
	parameter ENABLE_OE = "false"; 
	parameter ENABLE_TERM = "false"; 
	parameter DDIO_WITH_DELAY = "false"; 
	
	localparam OE_SIZE = (HALF_RATE == "true") ? 2 : 1;
	localparam DATA_SIZE = (REGISTER_MODE == "ddr") ? 
			(HALF_RATE == "true") ? 
				4 : 2
			: 1;

	input ck;
	input ck_in;
	input ck_out;
	input ck_fr;
	input ck_fr_in;
	input ck_fr_out;
	input ck_hr;
	input ck_hr_in;
	input ck_hr_out;
	input [SIZE * OE_SIZE - 1:0] oe;
	input [SIZE * DATA_SIZE - 1:0] din;
	output [SIZE * DATA_SIZE - 1:0] dout;
	input terminationcontrol;
	inout [SIZE - 1:0] pad_io;	
	inout [SIZE - 1:0] pad_io_b;
	input [SIZE - 1:0] pad_in;	
	input [SIZE - 1:0] pad_in_b;
	output [SIZE - 1:0] pad_out;	
	output [SIZE - 1:0] pad_out_b;	
	input aclr;
	input aset;
	input sclr;
	input sset;
	input cke;

	wire [SIZE * OE_SIZE - 1:0] oe_reordered;
	wire [SIZE * DATA_SIZE - 1:0] din_reordered;
	wire [SIZE * DATA_SIZE - 1:0] dout_reordered;
	wire [SIZE - 1:0] pad_io;	
	wire [SIZE - 1:0] pad_io_b;
	
	generate
		if (PIN_TYPE == "input")
		begin
			assign pad_io = pad_in;
			assign pad_io_b = pad_in_b;
		end
		else if (PIN_TYPE == "output")
		begin
			assign pad_out = pad_io;
			assign pad_out_b = pad_io_b;
		end
	endgenerate

	genvar j, k;
	generate
			for(j = 0; j < SIZE ; j = j + 1) begin : j_loop
				for(k = 0; k < DATA_SIZE; k = k + 1) begin : k_d_loop
					assign din_reordered[j * DATA_SIZE + k] = din[j + k * SIZE];
					assign dout[j + k * SIZE] = dout_reordered[j * DATA_SIZE + k];
				end
				for(k = 0; k < OE_SIZE; k = k + 1) begin : k_oe_loop
					assign oe_reordered[j * OE_SIZE + k] = oe[j + k * SIZE];
				end
			end
	endgenerate

	genvar i;
	generate
			for(i = 0 ; i < SIZE ; i = i + 1) begin : i_loop
				altera_gpio_one_bit #(
					.PIN_TYPE(PIN_TYPE),
					.BUFFER_TYPE(BUFFER_TYPE),
					.PSEUDO_DIFF(PSEUDO_DIFF),
					.REGISTER_MODE(REGISTER_MODE),
					.HALF_RATE(HALF_RATE),
					.SEPARATE_I_O_CLOCKS(SEPARATE_I_O_CLOCKS),
					.ARESET_MODE(ARESET_MODE),
					.SRESET_MODE(SRESET_MODE),
					.BUS_HOLD(BUS_HOLD),
					.OPEN_DRAIN(OPEN_DRAIN),
					.ENABLE_CKE(ENABLE_CKE),
					.ENABLE_OE(ENABLE_OE),
					.ENABLE_TERM(ENABLE_TERM)
				) altera_gpio_bit_i (
					.ck(ck),
					.ck_in(ck_in),
					.ck_out(ck_out),
					.ck_fr(ck_fr),
					.ck_fr_in(ck_fr_in),
					.ck_fr_out(ck_fr_out),
					.ck_hr(ck_hr),
					.ck_hr_in(ck_hr_in),
					.ck_hr_out(ck_hr_out),
					.oe(oe_reordered[(i + 1) * OE_SIZE - 1 : i * OE_SIZE]),
					.din(din_reordered[(i + 1) * DATA_SIZE - 1 : i * DATA_SIZE]),
					.dout(dout_reordered[(i + 1) * DATA_SIZE - 1 : i * DATA_SIZE]),
					.pad(pad_io[i]),
					.pad_b(pad_io_b[i]),
					.terminationcontrol(terminationcontrol),
					.aclr(aclr),
					.aset(aset),
					.sclr(sclr),
					.sset(sset),
					.cke(cke)
				);
			end
	endgenerate

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "Xw7zHY4BqltP71AyShWqYISoLhZT3SxrpyEl7BQuEYmT9aXwFInZOB1+8NAM9Abxac/nqs+RlyE9whduUc9F1yz69gW4lO+wlI8NI9FlvhMmczOfpPoswd02wxY1mC0KUEBF6UVmqVmGgPRlVgar5aXf/783J2fwrQfqbxgQXykWiGLaQMHxcul/bgoN4hFEn1TMYUy/tTE8m8koc22984w19xYrqWuXU/0ySEZYOIJoZBnitKgbUBY3rDzQ99Qg6tQmDbxcCCc6z9INYtbZjIF888CRyYARe9DOQqPTCv6nAt5dj9MQAds4YCMxEsm/ilQC6lg9f2Hk9/Lnn4DeJsk/LyWFN4dH5y3vUGWAYvFdPxB3itFnRFHPeuSxjpmbRXFgSdt5Us1xo5IrPuTTs0p8YAvpbK7GNhnxmBBQ9XNe2afXMLKKrTIYBi7oQIyumhDsvAGNG15ikezHkiJxkQjs4gKtz8RaPx8/4Gg8kkzzKu0wvztFnLqWYq7A1HIP6SRHKHG/174lC6asBipM4vS/iIpoEVsMUoBakLAuhoYLGJdWzqqLyOFIIaiRYuRMgS8aNVlHPBLmKaw+2xiWb0T7NkSgk/c2m/pWV2IZxY9VZMOQM3mzJNtKEzfK+k++EYqyPByvqplT1MqLNRuUhN/vr2A1kGjk9O96NP9YMJROxPvNo+pyzL23l9MIAanx058zhdxd/405zzFUan7ijQ/E4D7UbPwP8kLAlnC0PiRsdyXNUR4nzDJ0iv6esmOYjFDnaplTxRHNkyHS1nAdPgGm7moCYQa50uWfqzpwq5dwC2OMZ6Oiuj/fSU5rQt87X5EyLOHBDPsqG35YFBjKIVoJQfiM9c61EQ2uSrjrBssFfB17FNs1EnHQmaDyJNrBDx8VioA83cj24TL+zDzdYdZEdmIvsNahsOSSrIZsdxqLKLgUPw4JzJ1Mb8i39r/a/0OfC5QryVXDrsbU1XROXFX9IQ7ugnw6fhgFFgvW3AZDOFa2GDcTvxHHE3rvj8wf"
`endif