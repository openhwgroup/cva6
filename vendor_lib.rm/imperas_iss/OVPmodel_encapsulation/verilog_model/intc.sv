/*
 *
 * Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com
 *
 * The contents of this file are provided under the Software License
 * Agreement that you accepted before downloading this file.
 *
 * This source forms part of the Software and can be used for educational,
 * training, and demonstration purposes but cannot be used for derivative
 * works except in cases where the derivative works require OVP technology
 * to run.
 *
 * For open source models released under licenses that you can use for
 * derivative works, please visit www.OVPworld.org or www.imperas.com
 * for the location of the open source models.
 *
 */

 
module INTC
(
    BUS MemBus
);
/*
    initial begin
        forever begin
            #200000;
            MemBus.reset = 1;
            #100;
            MemBus.reset = 0;
        end
    end
    initial begin
        #1000000;
        MemBus.MExternalInterrupt = 1;
        #10000;
        MemBus.MExternalInterrupt = 0;
    end
*/
endmodule
