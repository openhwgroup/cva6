module dff(
input clk,
input rstn,
input en,
input d,
output logic q
);

always @(posedge clk or negedge rstn)
begin
	if(!rstn)
		q <= 0;
	else
	begin
		if(en)
			q <= d;
		else
			q <= q; //prevents the creation of latches
	end
end


endmodule
