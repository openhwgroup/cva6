import ariane_pkg::*;

module dpram #(
        parameter XLEN = 64,
        parameter DEPTH = 512,
        parameter ADDR = $clog2(DEPTH)
)
(

    input rstn,

    input clk1,
    input en1,
    input [ADDR-1:0] addr1,
    input [XELN-1:0] datain1,
    input write1,
    output logic [XLEN-1:0] dataout1,

    input clk2,
    input en2,
    input [ADDR-1:0] addr2,
    input [XELN-1:0] datain2,
    input write2,
    output logic [XLEN-1:0] dataout2

);

logic [XLEN-1:0] mem [0:DEPTH-1];


always @ ( posedge clk1 or negedge rstn )
begin
    if(!rstn)
    begin
        dataout1 <= '{default:0};
    end
    begin
        if(en1)
        begin
            if(write1)
                mem[addr1] <= datain1;
            dataout1 <= mem[addr];
        end
        else
        begin
            dataout1 <= '{default:0};
        end
    end

end


always @ ( posedge clk2 or negedge rstn )
begin
    if(!rstn)
    begin
        dataout2 <= '{default:0};
    end
    begin
        if(en2)
        begin
            if(write2)
                mem[addr2] <= datain2;
            dataout2 <= mem[addr2];
        end
        else
        begin
            dataout2 <= '{default:0};
        end
    end

end
endmodule
