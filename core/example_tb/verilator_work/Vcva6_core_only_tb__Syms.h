// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef _VCVA6_CORE_ONLY_TB__SYMS_H_
#define _VCVA6_CORE_ONLY_TB__SYMS_H_  // guard

#include "verilated_heavy.h"

// INCLUDE MODULE CLASSES
#include "Vcva6_core_only_tb.h"
#include "Vcva6_core_only_tb___024unit.h"
#include "Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1.h"

// SYMS CLASS
class Vcva6_core_only_tb__Syms : public VerilatedSyms {
  public:
    
    // LOCAL STATE
    const char* __Vm_namep;
    bool __Vm_didInit;
    
    // SUBCELL STATE
    Vcva6_core_only_tb*            TOPp;
    Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1 TOP__cva6_core_only_tb__DOT__cva6_axi_bus;
    
    // SCOPE NAMES
    VerilatedScope __Vscope_cva6_core_only_tb;
    
    // SCOPE HIERARCHY
    VerilatedHierarchy __Vhier;
    
    // CREATORS
    Vcva6_core_only_tb__Syms(Vcva6_core_only_tb* topp, const char* namep);
    ~Vcva6_core_only_tb__Syms();
    
    // METHODS
    inline const char* name() { return __Vm_namep; }
    
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

#endif  // guard
