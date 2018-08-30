
module register #(
	XLEN = 4
)
(
	input clk,
	input rstn,
	input en,
	input [XLEN-1:0] d,
	output [XLEN-1:0] q
);


genvar i;
generate
	for(i = 0; i < XLEN; i++)
	begin: r
		dff r(.clk(clk), .rstn(rstn), .en(en), .d(d[i]), .q(q[i]));
	end
endgenerate

endmodule
