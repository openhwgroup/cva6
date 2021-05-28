module pulp_isolation_0
(
  input  logic data_i,
  input  logic ena_i,
  output logic data_o
);
 
  assign data_o = ena_i ? data_i : 1'b0;
   
endmodule