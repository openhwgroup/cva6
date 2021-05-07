// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table implementation internals

#include "Vcva6_core_only_tb__Syms.h"
#include "Vcva6_core_only_tb.h"
#include "Vcva6_core_only_tb___024unit.h"
#include "Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1.h"



// FUNCTIONS
Vcva6_core_only_tb__Syms::~Vcva6_core_only_tb__Syms()
{
    
    // Tear down scope hierarchy
    
}

Vcva6_core_only_tb__Syms::Vcva6_core_only_tb__Syms(Vcva6_core_only_tb* topp, const char* namep)
    // Setup locals
    : __Vm_namep(namep)
    , __Vm_didInit(false)
    // Setup submodule names
    , TOP__cva6_core_only_tb__DOT__cva6_axi_bus(Verilated::catName(topp->name(), "cva6_core_only_tb.cva6_axi_bus"))
{
    // Pointer to top level
    TOPp = topp;
    // Setup each module's pointers to their submodules
    TOPp->__PVT__cva6_core_only_tb__DOT__cva6_axi_bus = &TOP__cva6_core_only_tb__DOT__cva6_axi_bus;
    // Setup each module's pointer back to symbol table (for public functions)
    TOPp->__Vconfigure(this, true);
    TOP__cva6_core_only_tb__DOT__cva6_axi_bus.__Vconfigure(this, true);
    // Setup scopes
    __Vscope_cva6_core_only_tb.configure(this, name(), "cva6_core_only_tb", "cva6_core_only_tb", -12, VerilatedScope::SCOPE_OTHER);
    
    // Set up scope hierarchy
    
}
