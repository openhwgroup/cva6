// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vcva6_core_only_tb.h for the primary calling header

#ifndef _VCVA6_CORE_ONLY_TB___024UNIT_H_
#define _VCVA6_CORE_ONLY_TB___024UNIT_H_  // guard

#include "verilated_heavy.h"

//==========

class Vcva6_core_only_tb__Syms;

//----------

VL_MODULE(Vcva6_core_only_tb___024unit) {
  public:
    
    // INTERNAL VARIABLES
  private:
    Vcva6_core_only_tb__Syms* __VlSymsp;  // Symbol table
  public:
    
    // CONSTRUCTORS
  private:
    VL_UNCOPYABLE(Vcva6_core_only_tb___024unit);  ///< Copying not allowed
  public:
    Vcva6_core_only_tb___024unit(const char* name = "TOP");
    ~Vcva6_core_only_tb___024unit();
    
    // INTERNAL METHODS
    void __Vconfigure(Vcva6_core_only_tb__Syms* symsp, bool first);
  private:
    void _ctor_var_reset() VL_ATTR_COLD;
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

//----------


#endif  // guard
