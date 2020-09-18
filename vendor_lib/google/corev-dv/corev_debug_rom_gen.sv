//Copyright 2020 Silicon Labs, Inc.
  
//This file, and derivatives thereof are licensed under the
//Solderpad License, Version 2.0 (the "License");
//Use of this file means you agree to the terms and conditions
//of the license and are in full compliance with the License.
//You may obtain a copy of the License at
//  
//    https://solderpad.org/licenses/SHL-2.0/
//  
//Unless required by applicable law or agreed to in writing, software
//and hardware implementations thereof
//distributed under the License is distributed on an "AS IS" BASIS,
//WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//See the License for the specific language governing permissions and
//limitations under the License.
//
//
class corev_debug_rom_gen extends riscv_debug_rom_gen;

    `uvm_object_utils(corev_debug_rom_gen)

    function new (string name = "");
        super.new(name);
    endfunction


    virtual function void gen_program();
        // Insert section info so linker can place
        // debug code at the correct adress
        instr_stream.push_back(".section .debugger, \"ax\"");
        super.gen_program();
    endfunction

    virtual function void gen_debug_exception_handler();
        // Insert section info so linker can place
        // debug exception code at the correct adress
        instr_stream.push_back(".section .debugger_exception, \"ax\"");
        super.gen_debug_exception_handler();

        // Inser section info to place remaining code in the 
        // original section
        instr_stream.push_back(".section text");
    endfunction

endclass
