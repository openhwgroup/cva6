import ariane_pkg::*;

module spram #(
        parameter XLEN = 64,
        parameter DEPTH = 512,
        parameter ADDR = $clog2(DEPTH)
)
(
    input clk,
    input rstn,

    input en,
    input [ADDR-1:0] addr,
    input [XELN-1:0] datain,
    input write,
    output logic [XLEN-1:0] dataout
);


logic [XLEN-1:0] mem [0:DEPTH-1];


always @ ( posedge clk or negedge rstn )
begin
    if(!rstn)
    begin
        dataout <= '{default:0};
    end
    begin
        if(en)
        begin
            if(write)
                mem[addr] <= datain;
            dataout <= mem[addr];
        end
        else
        begin
            dataout <= '{default:0};
        end
    end

end


endmodule
