// Author: Valerio Di Domenico <didomenico.valerio@virgilio.it>

// Description:
// This module implements a memory protocol converter from MEM protocol (used by MPT) to DCACHE protocol

// Import headers
`include "uninasoc_mem.svh" 

module mem_to_dcache_converter 
    import ariane_pkg::*; 
    # ( 
        parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
        parameter type dcache_req_i_t = logic,
        parameter type dcache_req_o_t = logic
    ) (
        input logic clk_i,
        input logic rst_ni,
        // MEM slave ports
        `DEFINE_MEM_SLAVE_PORTS(s),                             
        // Data cache request out - CACHES
        input dcache_req_o_t req_port_i,
        // Data cache request in - CACHES
        output dcache_req_i_t req_port_o
    );

    enum logic {
        IDLE,
        SEND_TAG
    } state_d, state_q;

    always_comb begin 
        req_port_o.data_req       = s_mem_req;
        s_mem_gnt                 = req_port_i.data_gnt;
        s_mem_valid               = req_port_i.data_rvalid;
        req_port_o.address_tag    = s_mem_addr[CVA6Cfg.DCACHE_TAG_WIDTH + CVA6Cfg.DCACHE_INDEX_WIDTH-1 : CVA6Cfg.DCACHE_INDEX_WIDTH]; //44'h00000080025;
        req_port_o.address_index  = s_mem_addr[CVA6Cfg.DCACHE_INDEX_WIDTH-1:0];                                                       //12'hF50;s_mem_addr[CVA6Cfg.DCACHE_INDEX_WIDTH-1:0];
        s_mem_rdata               = req_port_i.data_rdata;
        req_port_o.data_wdata     = s_mem_wdata;
        req_port_o.data_we        = s_mem_we; 
        req_port_o.data_be        = s_mem_be;
        state_d                   = state_q;

        case (state_q)
            // Wait for a MEM request
            IDLE: begin
                req_port_o.tag_valid = 1'b0;
                if (s_mem_req) begin
                    if (req_port_i.data_gnt) begin
                        // Now  we can send the tag in the next cycle
                        state_d = SEND_TAG;
                    end
                end 
            end
            SEND_TAG: begin
                req_port_o.tag_valid = 1'b1;
                state_d = IDLE;
            end
        endcase 
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            state_q <= IDLE;
        end else begin
            state_q <= state_d;
        end
    end

endmodule