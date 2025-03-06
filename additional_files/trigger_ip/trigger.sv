module trigger #(
	parameter int unsigned AXI_ADDR_WIDTH  = 32,
	localparam int unsigned AXI_DATA_WIDTH = 32, 
	parameter int unsigned AXI_ID_WIDTH    = 1,
	parameter int unsigned AXI_USER_WIDTH  = 1
  ) (
    input  logic  clk_i,         // Clock
    input  logic  rst_ni,        // Asynchronous reset active low
    input  logic  trigger_on_i,  // Trigger input-on
    input  logic  trigger_off_i, // Trigger input off
    output logic  gpio_o         // GPIO output
);

    logic gpio_reg;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            gpio_reg <= 0;
        end else if (trigger_on_i) begin
            gpio_reg <= 1;
        end else if (trigger_off_i) begin
            gpio_reg <= 0;
        end
    end

    // Assign GPIO output
    assign gpio_o = gpio_reg;

endmodule



