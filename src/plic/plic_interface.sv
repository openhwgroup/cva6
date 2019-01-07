// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
//-------------------------------------------------------------------------------
//-- Title      : Register Interface
//-- File       : plic_target_slice.sv
//-- Author     : Gian Marti      <gimarti.student.ethz.ch>
//-- Author     : Thomas Kramer   <tkramer.student.ethz.ch>
//-- Author     : Thomas E. Benz  <tbenz.student.ethz.ch>
//-- Company    : Integrated Systems Laboratory, ETH Zurich
//-- Created    : 2018-03-31
//-- Last update: 2018-03-31
//-- Platform   : ModelSim (simulation), Synopsys (synthesis)
//-- Standard   : SystemVerilog IEEE 1800-2012
//-------------------------------------------------------------------------------
//-- Description: Implementation of the plic's register interface
//-------------------------------------------------------------------------------
//-- Revisions  :
//-- Date        Version  Author  Description
//-- 2018-03-31  2.0      tbenz   Created header
//-------------------------------------------------------------------------------

module plic_interface #(
    parameter int ADDR_WIDTH         = 32,   // width of external address bus
    parameter int DATA_WIDTH         = 32,   // width of external data bus
    parameter int ID_BITWIDTH        = 10,   // width of the gateway indecies
    parameter int PARAMETER_BITWIDTH =  3,   // width of the internal parameter e.g. priorities
    parameter int NUM_TARGETS        =  1,   // number of target slices
    parameter int NUM_GATEWAYS       =  1    // number of gateways
)(
    input  logic                         clk_i,                                     // the clock signal
    input  logic                         rst_ni,                                    // asynchronous reset active low
    input  logic[ID_BITWIDTH-1:0]        id_of_largest_priority_i[NUM_TARGETS],     // input array id of largest priority
    input  logic                         pending_array_i[NUM_GATEWAYS],             // array with the interrupt pending , idx0 is gateway 1
    output reg [PARAMETER_BITWIDTH-1:0]  thresholds_o[NUM_TARGETS],                 // save internally the thresholds, communicate values over this port to the core
    output reg [PARAMETER_BITWIDTH-1:0]  gateway_priorities_o[NUM_GATEWAYS],        // save internally the the priorities, communicate values
    output logic                         irq_enables_o[NUM_GATEWAYS][NUM_TARGETS],  // communicate enable bits over this port
    output logic                         target_irq_claims_o[NUM_TARGETS],          // claim signals
    output logic                         target_irq_completes_o[NUM_TARGETS],       // complete signals
    output logic[ID_BITWIDTH-1:0]        target_irq_completes_id_o[NUM_TARGETS],    // the id of the gateway to be completed
    REG_BUS.in                           external_bus_io                            // the bus
);

    //define ennumerated types
    enum logic [2:0] {INV, PRI, IPA, IEB, THR, CCP} funct;   // the address mapping will primarily check what
                                                             // function should be performed
                                                             // INV: invalid, PRI: priorities, IPA: interrupt pending
                                                             // IEB: interrupt enable, THR: threshold and claim/complete
                                                             // CCP: claim/clear pulses

        //calculate some parameter needed later
    localparam int num_gateway_bundles = (NUM_GATEWAYS-1) / DATA_WIDTH + 1;       // how many bundles we have to consider
    localparam int bpw                 = DATA_WIDTH / 8;                          // how many bytes a data word consist of
    //internal signals
    logic [ADDR_WIDTH-12-1:0     ]  page_address;       // the upper part of the address
    logic [11:0                  ]  page_offset;        // the lowest 12 bit describes the page offset
    logic [11-$clog2(bpw):0      ]  page_word_offset;   // the word address of each page offset
    logic [$clog2(bpw)-1:0       ]  word_offset;        // the byte in the word

    logic [DATA_WIDTH/8-1:0      ]  write_active;       // 0 if inactive, else what byte ahs to be written
    logic                           read_active;        // 0 if inactive, 1 when reading the word
    //bundle definitions
    logic [DATA_WIDTH-1:0        ]  irq_pending_bundle[num_gateway_bundles];

    //registers
    logic [PARAMETER_BITWIDTH-1:0]  thresholds_d[NUM_TARGETS];
    logic [PARAMETER_BITWIDTH-1:0]  thresholds_q[NUM_TARGETS];

    logic [PARAMETER_BITWIDTH-1:0]  priorities_d[NUM_GATEWAYS];
    logic [PARAMETER_BITWIDTH-1:0]  priorities_q[NUM_GATEWAYS];

    logic [ID_BITWIDTH-1:0       ]  id_of_largest_priority_d[NUM_TARGETS];
    logic [ID_BITWIDTH-1:0       ]  id_of_largest_priority_q[NUM_TARGETS];

    logic [DATA_WIDTH/bpw-1:0    ]  ena_bundles_d[num_gateway_bundles][NUM_TARGETS][DATA_WIDTH/8];
    logic [DATA_WIDTH/bpw-1:0    ]  ena_bundles_q[num_gateway_bundles][NUM_TARGETS][DATA_WIDTH/8];

    // assignments
    assign id_of_largest_priority_d = id_of_largest_priority_i;

    // assign addresses
    assign page_address      = external_bus_io.addr[ADDR_WIDTH-1:12];
    assign page_offset       = external_bus_io.addr[11:0           ];
    assign page_word_offset  = external_bus_io.addr[11:$clog2(bpw) ];
    assign word_offset       = external_bus_io.addr[$clog2(bpw)-1:0];

    assign write_active      = (external_bus_io.valid &  external_bus_io.write) ? external_bus_io.wstrb : '0;
    assign read_active       = external_bus_io.valid  & !external_bus_io.write;

    // bundle signals
    for (genvar bundle = 0; bundle < num_gateway_bundles; bundle++) begin
        for (genvar ip_bit = 0; ip_bit < DATA_WIDTH; ip_bit++) begin
            if (bundle * DATA_WIDTH + ip_bit < NUM_GATEWAYS) begin
                assign irq_pending_bundle[bundle][ip_bit] = pending_array_i[bundle * DATA_WIDTH + ip_bit];
            end else begin
                assign irq_pending_bundle[bundle][ip_bit] = '0;
            end
        end
    end

    for (genvar bundle = 0; bundle < num_gateway_bundles; bundle++) begin
        for (genvar target = 0; target < NUM_TARGETS; target++) begin
            for (genvar byte_in_word = 0; byte_in_word < DATA_WIDTH/8; byte_in_word++) begin
                for (genvar enable_bit = 0; enable_bit < 8; enable_bit++) begin
                    assign irq_enables_o[bundle * DATA_WIDTH + enable_bit + byte_in_word * 8][target] =
                                                            ena_bundles_q[bundle][target][byte_in_word][enable_bit];
                end
            end
        end
    end

    // determine the function to be performed
    always_comb begin : proc_address_map
        // default values
        funct = INV;
        // only aligned access is allowed:
        if (word_offset == '0) begin
            // we have now an word alligned access -> check out page offset to determine
            // what type of access this is.
            if (page_address[13:0] == 0) begin // we access the gateway priority bits
                // the page_word_offset tells us now which gateway we consider
                // in order to grant or deny access, we have to check if the gateway
                // in question really exist.
                // Gateway 0 does not exist, so return an error
                if (page_word_offset <= NUM_GATEWAYS && page_word_offset > 0) begin //the gateway in question exists
                    // set the current operation to be an access to the priority registers
                    funct = PRI;
                end
            // we now access the IP Bits, read only
            end else if (page_address[13:0] == 1) begin
                // the page_word_offset tells us now, which word we have to consider,
                // the word, which includes the IP bit in question should be returned
                if (page_word_offset<num_gateway_bundles) begin
                    funct = IPA;
                end
            // access of the enable bits for each target
            end else if (page_address[13:9] == 0) begin
                // the bottom part page_word_offset now tells us which gateway bundle we have to consider
                // part of the page_address and the upper part of the page_word_offset give us the target nr.
                if (page_offset[6:$clog2(bpw)] < num_gateway_bundles) begin
                    if (({page_address[8:0], page_offset[11:7]} - 64) < NUM_TARGETS) begin
                        funct = IEB;
                    end
                end
            // priority / claim / complete
            end else begin
                // page address - 0h20 gives the target number
                if (page_address[13:0] - 'h200 < NUM_TARGETS) begin
                    // check lowest bit of the page_word_offset to get the exact function
                    if (page_word_offset == 0) begin
                        funct = THR;
                    end else if (page_word_offset == 1) begin
                        funct = CCP;
                    end
                end
            end
        end
    end

    always_comb begin : proc_read_write
        // defalt values
        external_bus_io.rdata = 0;
        external_bus_io.error = 0;
        external_bus_io.ready = 0;

        for (integer target = 0; target<NUM_TARGETS; target++) begin
            target_irq_claims_o      [target] = '0;
            target_irq_completes_o   [target] = '0;
            target_irq_completes_id_o[target] = '0;
        end

        //just keep the values untouched as default
        priorities_d  = priorities_q;
        ena_bundles_d = ena_bundles_q;
        thresholds_d  = thresholds_q;

        case (funct)
            PRI: begin
                // read case
                if (read_active != 0) begin
                    external_bus_io.rdata = priorities_q[page_word_offset-1];
                    external_bus_io.ready = 1;
                // write case
                end else if (write_active[0] == 1) begin
                    priorities_d[page_word_offset-1] = external_bus_io.wdata[PARAMETER_BITWIDTH-1:0];
                    external_bus_io.ready = 1;
                end
            end

            IPA: begin
                // read case
                if (read_active != 0) begin
                    external_bus_io.rdata = irq_pending_bundle[page_word_offset];
                    external_bus_io.ready = 1;
                // write case
                end else if (write_active != 0) begin
                    external_bus_io.error = 1;  //not allowed
                end
            end

            IEB: begin
                // read case
                if (read_active != 0) begin
                    for (integer byte_in_word = 0; byte_in_word < DATA_WIDTH/8; byte_in_word++) begin
                        external_bus_io.rdata[8*(byte_in_word) +: 8] =  ena_bundles_q[page_offset[6:$clog2(bpw)]][({page_address[8:0], page_offset[11:7]} - 64)][byte_in_word];
                    end
                    external_bus_io.ready = 1;
                // write case
                end else if(write_active != 0) begin
                    for (integer byte_in_word=0; byte_in_word<DATA_WIDTH/8; byte_in_word++) begin
                        if(write_active[byte_in_word]) begin
                            ena_bundles_d[page_offset[6:$clog2(bpw)]][({page_address[8:0], page_offset[11:7]} - 64)][byte_in_word] = external_bus_io.wdata[8*(byte_in_word) +: 8];
                        end
                    end
                    external_bus_io.ready = 1;
                end
            end

            THR: begin
                // read case
                if (read_active != 0) begin
                    external_bus_io.rdata[PARAMETER_BITWIDTH-1:0] = thresholds_q[(page_address[13:0] - 'h200)];
                    external_bus_io.ready = 1;
                // write case
                end else if (write_active != 0) begin
                    thresholds_d[(page_address[13:0] - 'h200)] = external_bus_io.wdata[PARAMETER_BITWIDTH-1:0];
                    external_bus_io.ready = 1;
                end
            end

            CCP: begin
                // read case
                if (read_active != 0) begin
                    target_irq_claims_o[(page_address[13:0] - 'h200)] = 1;
                    external_bus_io.rdata[ID_BITWIDTH-1:0] = id_of_largest_priority_q[(page_address[13:0] - 'h200)];
                    external_bus_io.ready = 1;
                // write case
                end else if (write_active != 0) begin
                    target_irq_completes_o[(page_address[13:0] - 'h200)] = 1;
                    target_irq_completes_id_o[(page_address[13:0] - 'h200)] = external_bus_io.wdata[ID_BITWIDTH-1:0];
                    external_bus_io.ready = 1;
                end
            end

            default : begin
                //per default: error
                external_bus_io.error = 1;
                external_bus_io.ready = 1;
            end
        endcase // funct
    end

    // store data in flip flops
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_update_ff
        if (~rst_ni) begin // set all registers to 0
            for (integer gateway = 0; gateway < NUM_GATEWAYS; gateway++)
                priorities_q[gateway] <= 0;

            for (integer bundle = 0; bundle < num_gateway_bundles; bundle++)
                for (integer target = 0; target < NUM_TARGETS; target++)
                    for (integer byte_in_word = 0; byte_in_word < DATA_WIDTH/8; byte_in_word++)
                        ena_bundles_q[bundle][target][byte_in_word] <= 0;

            for (integer target = 0; target < NUM_TARGETS; target++) begin
                thresholds_q[target]             <= 0;
                id_of_largest_priority_q[target] <= 0;
            end
        end else begin
            priorities_q             <= priorities_d;
            ena_bundles_q            <= ena_bundles_d;
            thresholds_q             <= thresholds_d;
            id_of_largest_priority_q <= id_of_largest_priority_d;
        end
    end

    //assign outputs
    assign thresholds_o         = thresholds_q;
    assign gateway_priorities_o = priorities_q;

    // pragma translate_off
    `ifndef VERILATOR
    initial begin
        assert ((ADDR_WIDTH==32) | (ADDR_WIDTH==64)) else $error("Address width has to bei either 32 or 64 bit");
        assert ((DATA_WIDTH==32) | (DATA_WIDTH==64)) else $error("Data width has to bei either 32 or 64 bit");
        assert (ID_BITWIDTH>0)                       else $error("ID_BITWIDTH has to be larger than 1");
        assert (ID_BITWIDTH<10)                      else $error("ID_BITWIDTH has to be smaller than 10");
        assert (PARAMETER_BITWIDTH>0)                else $error("PARAMETER_BITWIDTH has to be larger than 1");
        assert (PARAMETER_BITWIDTH<8)                else $error("PARAMETER_BITWIDTH has to be smaller than 8");
        assert (NUM_GATEWAYS>0)                      else $error("Num od Gateways has to be larger than 1");
        assert (NUM_GATEWAYS<512)                    else $error("Num of Gateways has to be smaller than 512");
        assert (NUM_TARGETS>0)                       else $error("Num Target slices has to be larger than 1");
        assert (NUM_TARGETS<15872)                   else $error("Num target slices has to be smaller than 15872");
    end
    `endif
    // pragma translate_on

endmodule
