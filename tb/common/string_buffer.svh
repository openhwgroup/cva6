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
// Author: Florian Zaruba, ETH Zurich
// Date: 13.07.2017
// Description: Buffers a string until a new line appears.

class string_buffer extends uvm_component;

    /*-------------------------------------------------------------------------------
    -- Interface, port, fields
    -------------------------------------------------------------------------------*/
    // string buffer
    byte buffer [$];
    // name to display in console
    string logger_name;
    /*-------------------------------------------------------------------------------
    -- UVM Factory register
    -------------------------------------------------------------------------------*/
        // Provide implementations of virtual methods such as get_type_name and create
        `uvm_component_utils(string_buffer)

    /*-------------------------------------------------------------------------------
    -- Functions
    -------------------------------------------------------------------------------*/
        // Constructor
        function new(string name = "string_buffer", uvm_component parent=null);
            super.new(name, parent);
            // default logger name
            logger_name = "String Buffer";
        endfunction : new

        function void set_logger(string logger_name);
            this.logger_name = logger_name;
        endfunction : set_logger

        function void flush();
            string s;
            // dump the buffer out the whole buffer
            foreach (buffer[i]) begin
                s = $sformatf("%s%c",s, buffer[i]);
            end

            uvm_report_info(logger_name, s, UVM_LOW);

            // clear buffer afterwards
            buffer = {};
        endfunction : flush

        // put a char to the buffer
        function void append(byte ch);

            // wait for the new line
            if (ch == 8'hA)
                this.flush();
            else
                buffer.push_back(ch);

        endfunction : append
endclass : string_buffer
