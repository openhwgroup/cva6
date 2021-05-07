// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vcva6_core_only_tb.h for the primary calling header

#include "Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1.h"
#include "Vcva6_core_only_tb__Syms.h"

//==========

VL_CTOR_IMP(Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1) {
    // Reset internal values
    // Reset structure values
    _ctor_var_reset();
}

void Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1::__Vconfigure(Vcva6_core_only_tb__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
}

Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1::~Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1() {
}

void Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+          Vcva6_core_only_tb_AXI_BUS__A40_AB40_AC5_AD1::_ctor_var_reset\n"); );
    // Body
    aw_ready = VL_RAND_RESET_I(1);
    w_ready = VL_RAND_RESET_I(1);
    b_id = VL_RAND_RESET_I(5);
    b_valid = VL_RAND_RESET_I(1);
    ar_ready = VL_RAND_RESET_I(1);
    r_id = VL_RAND_RESET_I(5);
    r_data = VL_RAND_RESET_Q(64);
    r_last = VL_RAND_RESET_I(1);
    r_valid = VL_RAND_RESET_I(1);
}
