// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vcva6_core_only_tb.h for the primary calling header

#ifndef _VCVA6_CORE_ONLY_TB_AXI_BUS__A40_AB40_AC5_AD1_H_
#define _VCVA6_CORE_ONLY_TB_AXI_BUS__A40_AB40_AC5_AD1_H_  // guard

#include "verilated_heavy.h"

//==========

class Vcva6_core_only_tb__Syms;

//----------

VL_MODULE(Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1) {
  public:
    
    // LOCAL SIGNALS
    CData/*0:0*/ aw_ready;
    CData/*0:0*/ w_ready;
    CData/*4:0*/ b_id;
    CData/*0:0*/ b_valid;
    CData/*0:0*/ ar_ready;
    CData/*4:0*/ r_id;
    CData/*0:0*/ r_last;
    CData/*0:0*/ r_valid;
    QData/*63:0*/ r_data;
    
    // INTERNAL VARIABLES
  private:
    Vcva6_core_only_tb__Syms* __VlSymsp;  // Symbol table
  public:
    
    // CONSTRUCTORS
  private:
    VL_UNCOPYABLE(Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1);  ///< Copying not allowed
  public:
    Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1(const char* name = "TOP");
    ~Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1();
    
    // INTERNAL METHODS
    void __Vconfigure(Vcva6_core_only_tb__Syms* symsp, bool first);
  private:
    void _ctor_var_reset() VL_ATTR_COLD;
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

//----------


#endif  // guard
