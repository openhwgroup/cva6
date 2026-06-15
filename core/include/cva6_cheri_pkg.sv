/* Copyright 2022 Bruno Sá and Zero-Day, Labs.
// Copyright 2025 Capabilities Limited.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   zcheri_pkg.sv
 * Authors: Bruno Sá <bruno.vilaca.sa@gmail.com>
 * Date:   01.01.2025
 *
 * Description: Contains CHERI related structures and interfaces
 * Adapted from the CHERI Capability Library (https://github.com/CTSRD-CHERI/cheri-cap-lib)
 */


package cva6_cheri_pkg;

  /* CHERI Constants */
  localparam XLEN = cva6_config_pkg::CVA6ConfigXlen;
  localparam CLEN = 2 * XLEN;  // Capability length two times the normal width
  localparam CTLEN = 2 * XLEN + 1;  // Capability + Tag bit
  localparam CAP_ADDR_WIDTH = XLEN;  // Capability address width
  localparam CAP_UPERMS_WIDTH = 4;
  localparam CAP_UPERMS_SHIFT = 6;
  localparam CAP_RSERV_HI_WIDTH = 7;
  localparam CAP_RSERV_LO_WIDTH = 15;
  localparam CAP_M_WIDTH = 14;
  localparam CAP_E_WIDTH = 6;
  localparam CAP_E_HALF_WIDTH = CAP_E_WIDTH / 2;
  localparam CAP_OTYPE_WIDTH = 1;
  localparam CAP_RESET_EXP = 0;
  localparam CAP_MAX_EXP = 52;
  localparam CAP_RESET_TOP = {2'b01, {CAP_M_WIDTH - 2{1'b0}}};

  /* Capabilities RISC-V Exception Trap Encoding Extension */

  localparam logic [XLEN-1:0] CAP_EXCEPTION = 28;
  localparam logic [XLEN-1:0] CAP_GUEST_EXCEPTION = 31;

  /* Capabilities Exception Codes */

  localparam logic [3:0] CAP_INSTR_FETCH_FAULT = 0;
  localparam logic [3:0] CAP_DATA_ACCESS_FAULT = 1;
  localparam logic [3:0] CAP_JUMP_BRANCH_FAULT = 2;

  localparam logic [3:0] CAP_TAG_VIOLATION = 0;
  localparam logic [3:0] CAP_SEAL_VIOLATION = 1;
  localparam logic [3:0] CAP_PERM_VIOLATION = 2;
  localparam logic [3:0] CAP_INVALID_ADDRESS_VIOLATION = 3;
  localparam logic [3:0] CAP_BOUNDS_VIOLATION = 4;

  /* Capabilities OType Encoding */

  localparam logic [CAP_OTYPE_WIDTH-1:0] UNSEALED_CAP = 0;
  localparam logic [CAP_OTYPE_WIDTH-1:0] SENTRY_CAP = 1;

  /* Types definition */

  typedef logic bool_t;
  typedef logic [CTLEN-1:0] capw_t;
  typedef logic [CAP_ADDR_WIDTH-1:0] addrw_t;
  typedef logic [CAP_ADDR_WIDTH:0] addrwe_t;
  typedef logic [CAP_ADDR_WIDTH+1:0] addrwe2_t;
  typedef logic [CAP_ADDR_WIDTH - CAP_M_WIDTH - 1:0] addrmw_t;
  typedef logic [CAP_ADDR_WIDTH - (CAP_M_WIDTH - 1):0] addrmwm2_t;
  typedef logic [CAP_RSERV_LO_WIDTH-1:0] resw_lo_t;
  typedef logic [CAP_RSERV_HI_WIDTH-1:0] resw_hi_t;
  typedef logic [CAP_OTYPE_WIDTH-1:0] otypew_t;
  typedef logic [CAP_UPERMS_WIDTH-1:0] upermsw_t;
  typedef logic [CAP_M_WIDTH-1:0] mw_t;
  typedef logic [CAP_M_WIDTH:0] mwe_t;
  typedef logic [CAP_M_WIDTH+1:0] mwe2_t;
  typedef logic [CAP_M_WIDTH-3:0] cmw_t;
  typedef logic [((CAP_M_WIDTH-CAP_E_HALF_WIDTH)-1):0] hmw_t;
  typedef logic [((CAP_M_WIDTH -(CAP_E_HALF_WIDTH+2))-1):0] hcmw_t;
  typedef logic [CAP_E_WIDTH-1:0] ew_t;
  typedef logic [CAP_E_HALF_WIDTH-1:0] hew_t;

  /**
      * CHERI exception tval layout fields
      */
  typedef struct packed {
    logic [3:0] fault_type;   /* Type of check being performed */
    logic [3:0] fault_cause;  /* Reason for failed check */
  } cap_tval2_t;

  function automatic logic [cva6_config_pkg::CVA6ConfigXlen-1:0] embed_cap_tval2(
      cap_tval2_t cap_tval2);
    return {
      {cva6_config_pkg::CVA6ConfigXlen - 22{1'b0}},
      cap_tval2.fault_type,
      12'b0,
      cap_tval2.fault_cause,
      2'b0
    };
  endfunction

  /**
      * Capability encoded architectural permission bits
      */
  typedef struct packed {
    // Allow loading capabilities with non-zero cap_level
    bool_t permit_store_level;
    // Allow loading capabilities with permit_store_level greater than this one
    bool_t permit_elevate_level;
    // Allow loading writeable capabilites through unwriteable ones.
    bool_t permit_load_mutable;
    /**
          * Allows access to privileged processor permitted by the architecture
          * (e.g., by virtue of being in supervisor mode), with architecture-specific
          * implications. This bit limits access to features such as MMU manipulation,
          * interrupt management, processor reset, and so on. The operating system
          * can remove this permission to implement constrained compartments within
          * the kernel.
          */
    bool_t access_sys_regs;
    /**
        * Allow this capability to be used in the PCC register as a capability
        * for the program counter, constraining control flow.
        */
    bool_t permit_execute;
    /// Allow this capability to be used to load untagged data.
    bool_t permit_load;
    /// Allow this capability to be used to store untagged data
    bool_t permit_store;
    /// Permit capability memory operations (respecting permit_load/store)
    bool_t permit_cap;
    // Allow this capability to be loaded without permit_store_level
    bool_t cap_level;
  } cap_hperms_t;
  /**
      * Capability reported architectural permission bits
      */
  typedef struct packed {
    logic [3:0]                     reserved_hi;
    bool_t                          permit_load;
    bool_t                          permit_execute;
    bool_t                          access_sys_regs;
    logic [10-CAP_UPERMS_WIDTH-1:0] reserved_lo;
    upermsw_t                       uperms;
    bool_t                          permit_cap;
    bool_t                          cap_level;
    bool_t                          permit_store_level;
    bool_t                          permit_elevate_level;
    bool_t                          permit_load_mutable;
    bool_t                          permit_store;
  } cap_report_perms_t;

  /* Capability flags definition */
  typedef struct packed {
    /**
          * RISC-V Encoding mode for PCC
          * 0 - Conventional RISC-V execution mode, in which address operands
          *     to existing RISC-V load and store opcodes contain integer addresses.
          * 1 - CHERI capability encoding mode, in which address operands
          *     to existing RISC-V load and store opcodes contain capabilities.
          */
    bool_t int_mode;
  } cap_flags_t;

  /* Capability bounds definition */
  typedef struct packed {
    ew_t exp;
    mw_t top_bits;
    mw_t base_bits;
  } cap_bounds_t;

  /* Capability format definition */
  typedef enum logic {
    EMBEDDED_EXP = 0,
    IMPLIED_EXP  = 1
  } cap_fmt_t  /*verilator public*/;

  /* Capability format IMPLIED_EXP definition */
  typedef struct packed {
    cmw_t top;
    mw_t  base;
  } cap_implied_exp_fmt_t;

  /* Capability format EMBEDDED_EXP definition */
  typedef struct packed {
    hcmw_t top_bits;
    hew_t  exp_top_bits;
    hmw_t  base_bits;
    hew_t  exp_base_bits;
  } cap_embedded_exp_fmt_t;

  /* Capability memory compressed bounds definition */

  typedef union packed {
    struct packed {
      cmw_t top_bits;
      mw_t  base_bits;
    } cbounds;
    cap_implied_exp_fmt_t  impl_exp_fmt;
    cap_embedded_exp_fmt_t emb_exp_fmt;
  } cap_cbounds_t;

  /* Capability decoding meta fields */
  typedef struct packed {
    logic [CAP_M_WIDTH-1:0] r;
    bool_t                  top_hi_r;
    bool_t                  base_hi_r;
    bool_t                  addr_hi_r;
    logic [1:0]             ct;
    logic [1:0]             cb;
  } cap_meta_data_t;

  /* Capability definition in memory */
  typedef struct packed {
    bool_t        tag;
    resw_hi_t     res_hi;
    upermsw_t     uperms;
    cap_flags_t   flags;
    cap_hperms_t  hperms;
    resw_lo_t     res_lo;
    otypew_t      otype;
    cap_fmt_t     EF;
    cap_cbounds_t bounds;
    addrw_t       addr;
  } cap_mem_t;

  /* Capability definition in register */
  typedef struct packed {
    bool_t       tag;
    resw_hi_t    res_hi;
    upermsw_t    uperms;
    cap_flags_t  flags;
    cap_hperms_t hperms;
    resw_lo_t    res_lo;
    otypew_t     otype;
    cap_fmt_t    EF;
    cap_bounds_t bounds;
    addrw_t      addr;
  } cap_reg_t;

  /* Capability set bounds return */
  typedef struct packed {
    cap_reg_t cap;
    bool_t    exact;
    addrw_t   mask;
  } cap_reg_set_bounds_ret_t;

  /* Capability default values for bounds and compressed bounds */
  localparam cap_bounds_t DEFAULT_BOUNDS_CAP = '{
      exp          : CAP_RESET_EXP,
      top_bits     : CAP_RESET_TOP,
      base_bits    : '{default: 0}
  };
  localparam cap_cbounds_t DEFAULT_CBOUNDS_CAP = '0;
  /* Capability default root capability and null capabilities for PCC and capability registers */
  localparam cap_reg_t REG_ROOT_CAP = '{
      tag             : 1'b1,
      addr            : '{default: 0},
      uperms          : '{default: '1},
      hperms          : '{default: '1},
      flags           : 1'b1,
      res_hi          : '0,
      res_lo          : '0,
      otype           : UNSEALED_CAP,
      EF              : EMBEDDED_EXP,
      bounds          : DEFAULT_BOUNDS_CAP
  };

  localparam cap_reg_t REG_NULL_CAP = '{
      tag             : 1'b0,
      addr            : '{default: 0},
      uperms          : '{default: 0},
      hperms          : '{default: 0},
      flags           : 1'b0,
      res_hi          : '0,
      res_lo          : '0,
      otype           : UNSEALED_CAP,
      EF              : EMBEDDED_EXP,
      bounds          : DEFAULT_BOUNDS_CAP
  };

  localparam cap_mem_t MEM_NULL_CAP = '{
      tag             : 1'b0,
      res_hi          : '0,
      uperms          : '{default: 0},
      flags           : 1'b0,
      hperms          : '{default: 0},
      res_lo          : '0,
      otype           : UNSEALED_CAP,
      EF              : EMBEDDED_EXP,
      bounds          : encode_bounds(DEFAULT_BOUNDS_CAP, EMBEDDED_EXP),
      addr            : '{default: 0}
  };

  /* Capability memory interface */

  function automatic bool_t is_cap_mem_valid(capw_t cap);
    cap_mem_t ret = cap_mem_t'(cap);
    return ret.tag;
  endfunction

  function automatic capw_t set_cap_mem_valid(capw_t cap, bool_t tag);
    cap_mem_t ret = cap;
    ret.tag = tag;
    return ret;
  endfunction

  function automatic cap_flags_t get_cap_mem_flags(capw_t cap);
    cap_mem_t ret = cap;
    return ret.flags;
  endfunction

  function automatic capw_t set_cap_mem_flags(capw_t cap, cap_flags_t flags);
    cap_mem_t ret = cap;
    ret.flags = flags;
    return ret;
  endfunction

  function automatic cap_hperms_t legalize_arch_perms(cap_hperms_t p);
    cap_hperms_t ap = p;
    ap.permit_cap = (ap.permit_load || ap.permit_store) ? ap.permit_cap : 0;
    ap.permit_elevate_level = (ap.permit_cap && ap.permit_load) ? ap.permit_elevate_level : 0;
    ap.permit_load_mutable = (ap.permit_cap && ap.permit_load) ? ap.permit_load_mutable : 0;
    ap.permit_store_level = ap.permit_cap ? ap.permit_store_level : 0;
    ap.access_sys_regs = p.permit_execute ? p.access_sys_regs : 0;
    return ap;
  endfunction

  function automatic addrw_t get_cap_mem_addr(capw_t cap);
    cap_mem_t ret = cap;
    return ret.addr;
  endfunction

  function automatic capw_t set_cap_mem_addr_unsafe(capw_t cap, addrw_t addr);
    cap_mem_t ret = cap;
    ret.addr = addr;
    return ret;
  endfunction

  function automatic capw_t set_cap_mem_addr_inc(capw_t cap, logic [11:0] inc);
    addrw_t addr = get_cap_mem_addr(cap);
    addrw_t sgn_ext_inc = {{CAP_ADDR_WIDTH - 12{inc[11]}}, inc};
    return set_cap_mem_addr_unsafe(cap, addr + sgn_ext_inc);
  endfunction

  /**
      * Capability Register Interface
      */

  /**
      * @brief Function check if capability valid.
      * @param cap capability in register format.
      * @returns 1 if capability is valid and 0 otherwise.
      */
  function automatic bool_t is_cap_reg_valid(cap_reg_t cap);
    return cap.tag;
  endfunction

  /**
      * @brief Function set capability tag bit.
      * @param cap capability in register format.
      * @param tag bool type bit to set the capability tag.
      * @returns capability cap with valid bit set to the input tag.
      */
  function automatic cap_reg_t set_cap_reg_valid(cap_reg_t cap, bool_t tag);
    cap_reg_t ret = cap;
    ret.tag = tag;
    return ret;
  endfunction

  function automatic cap_reg_t seal(cap_reg_t cap, otypew_t otype);
    cap_reg_t ret = cap;
    // Update the fields of the new sealed capability (otype)
    ret.otype = otype;
    return ret;
  endfunction

  /**
      * @brief Function to unseal the input capabilitu.
      * @param cap capability in register format.
      * @returns capability cap with otype field set to UNSEALED_CAP.
      */
  function automatic cap_reg_t unseal(cap_reg_t cap);
    cap_reg_t ret = cap;
    ret.otype = UNSEALED_CAP;
    return ret;
  endfunction

  /**
      * @brief Function to get the capability meta data using CHERI concentrate 128-bit decoding.
      * @param cap capability in register format.
      * @returns the capability meta data top and base corrections (ct and cb)
      *          , comparison values of A3 < R, T3 < R and B3 < R and the value
      *          of the representable region R.
      */
  function automatic cap_meta_data_t get_cap_reg_meta_data(cap_reg_t cap);

    cap_meta_data_t ret_info;
    ew_t exp = (cap.bounds.exp > CAP_MAX_EXP) ? CAP_MAX_EXP : cap.bounds.exp;
    logic [CAP_M_WIDTH-1:0] t = cap.bounds.top_bits;
    logic [CAP_M_WIDTH-1:0] b = cap.bounds.base_bits;
    logic [XLEN+1:0] addr_ext = {2'b00, cap.addr};
    logic [CAP_M_WIDTH-1:0] a = addr_ext[XLEN+1-exp-:CAP_M_WIDTH];
    logic [CAP_M_WIDTH-1:0] r = cap.bounds.base_bits - 14'b01000000000000;
    logic top_hi_r = t < r;
    logic base_hi_r = b < r;
    logic addr_hi_r = a < r;
    logic [1:0] ct = (top_hi_r == addr_hi_r) ? 0 : (top_hi_r && !addr_hi_r) ? 1 : -1;
    logic [1:0] cb = (base_hi_r == addr_hi_r) ? 0 : (base_hi_r && !addr_hi_r) ? 1 : -1;
    ret_info = '{
        r         : r,
        top_hi_r  : top_hi_r,
        base_hi_r : base_hi_r,
        addr_hi_r : addr_hi_r,
        ct        : ct,
        cb        : cb
    };
    return ret_info;
  endfunction

  typedef struct packed {
    addrwe_t top;
    addrw_t  base;
    bool_t   bounds_valid;
  } top_base_t;

  function automatic top_base_t get_cap_reg_top_base(cap_reg_t cap, cap_meta_data_t cap_meta_data);
    ew_t exp = cap.bounds.exp;
    addrw_t addr_bits = CAP_ADDR_WIDTH'({2'b0, cap.addr} & ~(~66'b0 >> exp)); // mask in relevant addr bits
    // base
    addrw_t base_corr_bits = CAP_ADDR_WIDTH'($signed({cap_meta_data.cb, 66'b0}) >>> exp);
    addrw_t base_bits = CAP_ADDR_WIDTH'({cap.bounds.base_bits, 52'b0} >> exp);
    addrw_t base = (addr_bits + base_corr_bits) | base_bits;
    // are the bounds a valid set of bounds (not malformed)
    bool_t malformed_msb =    ((exp == 0) && (cap.bounds.base_bits != 0))
                               || ((exp == 1) && (cap.bounds.base_bits[CAP_M_WIDTH-1] != 0));
    bool_t malformed_lsb = (exp > CAP_MAX_EXP);
    bool_t bounds_valid = (cap.EF == IMPLIED_EXP) || (!malformed_msb && !malformed_lsb);
    // top
    addrwe_t top_bits = (CAP_ADDR_WIDTH + 1)'({cap.bounds.top_bits, 52'b0} >> exp);
    addrwe_t top_corr_bits = (CAP_ADDR_WIDTH + 1)'($signed({cap_meta_data.ct, 66'b0}) >>> exp);
    addrwe_t top = (addr_bits + top_corr_bits) | top_bits;
    logic [1:0] diff = top[CAP_ADDR_WIDTH:CAP_ADDR_WIDTH-1] - {1'b0, base[CAP_ADDR_WIDTH-1]};
    if ((exp > 1) && (diff > 1)) top[CAP_ADDR_WIDTH] = ~top[CAP_ADDR_WIDTH];
    // return
    return '{top: top, base: base, bounds_valid: bounds_valid};
  endfunction

  function automatic bool_t are_cap_reg_bounds_valid(cap_reg_t cap, cap_meta_data_t cap_meta_data);
    top_base_t tb = get_cap_reg_top_base(cap, cap_meta_data);
    return tb.bounds_valid;
  endfunction

  function automatic bool_t are_cap_reg_bounds_root(cap_reg_t cap, cap_meta_data_t cap_meta_data);
    return (are_cap_reg_bounds_valid(cap, cap_meta_data) && cap.bounds.exp == CAP_RESET_EXP);
  endfunction

  function automatic cap_flags_t get_cap_reg_flags(cap_reg_t cap);
    cap_hperms_t perms = legalize_arch_perms(cap.hperms);
    return (perms == cap.hperms && perms.permit_execute) ? cap.flags : 1'b0;
  endfunction

  function automatic cap_reg_t set_cap_reg_flags(cap_reg_t cap, cap_flags_t flags);
    cap_reg_t ret = cap;
    cap_hperms_t perms = legalize_arch_perms(cap.hperms);
    ret.flags = (perms.permit_execute) ? flags : 1'b0;
    return ret;
  endfunction

  /**
      * @brief Function to compute the capability base address.
      * @param cap capability in register format.
      * @returns the base address with size [CAP_ADDR_WIDTH-1:0].
      */
  function automatic addrw_t get_cap_reg_base(cap_reg_t cap, cap_meta_data_t cap_meta_data);
    top_base_t tb = get_cap_reg_top_base(cap, cap_meta_data);
    return tb.base;
  endfunction

  /**
      * @brief Function to compute the capability top address.
      * @param cap capability in register format.
      * @returns the top address with size [CAP_ADDR_WIDTH:0].
      */
  function automatic addrwe_t get_cap_reg_top(cap_reg_t cap, cap_meta_data_t cap_meta_data);
    top_base_t tb = get_cap_reg_top_base(cap, cap_meta_data);
    return tb.top;
  endfunction

  /**
      * @brief Function to compute the capability length address.
      * @param cap capability in register format.
      * @param dec_bounds decounds bounds meta data.
      * @returns the capability length with size [CAP_ADDR_WIDTH:0].
      */
  function automatic addrw_t get_cap_reg_length(cap_reg_t cap, cap_meta_data_t cap_meta_data);
    mwe2_t  top = {cap_meta_data.ct, cap.bounds.top_bits};
    mwe2_t  base = {cap_meta_data.cb, cap.bounds.base_bits};
    addrw_t length = CAP_ADDR_WIDTH'({(top - base), 52'b0} >> cap.bounds.exp);
    // TODO: same saturation behaviour as bsv... "short of being correct"
    return (cap.bounds.exp == CAP_RESET_EXP) ? ~0 : length;
  endfunction

  /**
      * @brief Function sets the capability address and check if is representable.
      * @param cap capability in register format.
      * @param cursor target address for the resulting capability.
      * @param cap_meta_data capability decounds bounds meta data.
      * @returns the input capability with address set to cursor and clear the tag
      *          if the capability is not representable.
      */
  function automatic cap_reg_t set_cap_reg_address(cap_reg_t cap, addrw_t address,
                                                   cap_meta_data_t cap_meta_data);
    localparam T_W = CAP_ADDR_WIDTH - CAP_M_WIDTH;
    cap_reg_t ret = cap;
    ew_t e = cap.bounds.exp;

    mw_t newAddrMid = extract_addr_mid(address, e);
    bool_t newAddrHi = newAddrMid < cap_meta_data.r;
    logic [1:0] diffTmp = {1'b0, newAddrHi} - {1'b0, cap_meta_data.addr_hi_r};
    logic [T_W-1:0] deltaAddrHi = T_W'($signed({diffTmp, {T_W + 2{1'b0}}}) >>> e);

    logic [T_W-1:0] newAddrTruncLSB = address[CAP_ADDR_WIDTH-1:CAP_M_WIDTH];
    logic [T_W-1:0] oldAddrTruncLSB = cap.addr[CAP_ADDR_WIDTH-1:CAP_M_WIDTH];
    logic [T_W-1:0] mask = T_W'(~({T_W + 2{1'b1}} >> e));
    logic [T_W-1:0] deltaAddrUpper = (newAddrTruncLSB & mask) - (oldAddrTruncLSB & mask);

    bool_t is_rep = deltaAddrHi == deltaAddrUpper;
    ret.addr = address;
    // The exp out-of-range check is required for formal bsv equivalence.
    if (!is_rep || e > CAP_MAX_EXP) ret.tag = 1'b0;
    return ret;
  endfunction

  /**
      * @brief Function sets the capability address without representable checking.
      * @param cap capability in register format.
      * @param cursor target address for the resulting capability.
      * @returns the input capability with address set to cursor
      */
  function automatic cap_reg_t set_cap_reg_addr(cap_reg_t cap, addrw_t address);
    cap_reg_t ret = cap;
    ew_t exp = (cap.bounds.exp > CAP_MAX_EXP) ? CAP_MAX_EXP : cap.bounds.exp;
    ret.addr = address;
    return ret;
  endfunction

  /**
      * @brief Function to compute the in limit check
      * @param offset capability offset.
      * @param exp capability E.
      * @returns 0 - if not in limit and 1 - if in limit
      */
  function automatic bool_t is_offset_in_range(addrw_t offset, ew_t exp);
    bool_t  ret;
    addrw_t offset_msb;
    logic   cmp_top;

    offset_msb = $signed(offset >> (exp + CAP_M_WIDTH));
    cmp_top = |offset_msb;
    if (cmp_top == 0) ret = 1'b1;
    ret = 1'b0;
    return ret;
  endfunction

  // helpers for set_cap_reg_bounds
  function automatic mw_t bot3z(bool_t cond, mw_t val);
    return (cond) ? (val & (~0 << 3)) : val;
  endfunction
  function automatic mw_t add_b1000(bool_t cond, mw_t val);
    return (cond) ? (val + 'b1000) : val;
  endfunction
  /**
      * @brief Function to set the capability bounds
      * @param cap capability in register format.
      * @param base capability base address to be set.
      * @param lengthfull length of the capability to be set
      *                   top = base + length
      * @returns the capability with bounds set to base and length,
      *          a bool stating if the capability was exact aligned a 2*E+3,
      *          representable length and mask of the capability.
      */
  function automatic cap_reg_set_bounds_ret_t set_cap_reg_bounds(cap_reg_t cap, addrw_t base,
                                                                 addrwe_t lengthfull);
    cap_reg_set_bounds_ret_t ret = '{cap     : cap, exact   : 1'b0, mask    : '0};

    // derive candidate exponent from the lenght (numer of leading zeros)
    // XXX bsv uses a CAP_ADDR_WIDTH - (CAP_M_WIDTH - 1) width
    //          not a CAP_ADDR_WIDTH - (CAP_M_WIDTH - 2)
    ////////////////////////////////////////////////////////////////////////
    // count the leading zeros in the length. By adding one zero msb, we
    // account for the len msb to hang to the left of the lower 12
    // mantissa bits. The detected exponent here is at least 1, and may
    // fall to 0 later if need for rounding arises
    addrmwm2_t length_msb_bits = lengthfull[CAP_ADDR_WIDTH:CAP_M_WIDTH-1];
    ew_t msb_zeros = count_zeros_msb(length_msb_bits);
    ew_t exp = msb_zeros;

    // we must track an internal exponent unless the length is small
    // enough
    ////////////////////////////////////////////////////////////////////////
    bool_t int_exp = !((exp == CAP_MAX_EXP) && (lengthfull[CAP_M_WIDTH-2] == 1'b0));

    // prepare the new base and the mantissa-width bits version
    ////////////////////////////////////////////////////////////////////////
    addrwe2_t new_base = {2'b00, base};
    mwe_t new_base_bits = (CAP_M_WIDTH + 1)'(new_base >> (CAP_ADDR_WIDTH + 2 - CAP_M_WIDTH - exp));

    // prepare the new top and the mantissa-width bits version
    ////////////////////////////////////////////////////////////////////////
    addrwe2_t new_top = (CAP_ADDR_WIDTH + 2)'({2'b00, lengthfull} + new_base);
    mwe_t new_top_bits = (CAP_M_WIDTH + 1)'(new_top >> (CAP_ADDR_WIDTH + 2 - CAP_M_WIDTH - exp));

    // check if significant bits are lost from the bits used to store the
    // internal exponent...
    ////////////////////////////////////////////////////////////////////////
    // first, prepare masks
    addrwe2_t lmask = {1'b0, ~(65'b0)} >> exp;  // all bits bellow (including) len msb
    // with len msb shifted just below the mantissa and up 3 (internal exp)
    addrwe2_t lmask_lo = lmask >> (CAP_M_WIDTH - 1 - 3); // -1 drops the 0 in 14th bit of the length slice, -3 drops the exp bits
    // check for significant bits in the len, top and base
    bool_t lost_sig_top = ((new_top & lmask_lo) != 0) && int_exp;
    bool_t lost_sig_base = ((new_base & lmask_lo) != 0) && int_exp;

    // prepare values associated with rounded up exponent in case
    // necessary (due to updated length's msb being pushed up by one from
    // potential overflow)
    ////////////////////////////////////////////////////////////////////////
    mw_t new_top_bits_ovflw = new_top_bits[CAP_M_WIDTH:1];
    addrwe2_t lmask_lo_ovflw = lmask >> (CAP_M_WIDTH - 1 - 3 - 1); // -1 drops the 0 in 14th bit of the length slice, -3 drops the exp bits
    bool_t lost_sig_top_ovflw = ((new_top & lmask_lo_ovflw) != 0) && int_exp;

    // determine whether the exponent needs rounding up
    ////////////////////////////////////////////////////////////////////////
    addrwe2_t mw_lsb_mask = lmask_lo ^ lmask_lo_ovflw;
    bool_t len_carry_in = (mw_lsb_mask & new_top) != ((mw_lsb_mask & new_base) ^ (mw_lsb_mask & {1'b0, lengthfull}));
    bool_t len_round_up = lost_sig_top;
    bool_t len_max = ({1'b0, lengthfull} & ~lmask_lo) == (lmask ^ lmask_lo);
    bool_t len_max_less_1 = ({1'b0, lengthfull} & ~lmask_lo) == (lmask ^ lmask_lo_ovflw);

    bool_t len_ovflw = (len_max && (len_carry_in || len_round_up)) ? 1'b1
                         : (len_max_less_1 && len_carry_in && len_round_up) ? 1'b1
                         : 1'b0;

    // derive final exp, top and base values based on presence of overflow
    ////////////////////////////////////////////////////////////////////////
    ew_t final_exp = (len_ovflw && int_exp) ? exp - 1 : exp;
    mw_t final_top_bits = bot3z(
        int_exp
        , (len_ovflw && int_exp) ? add_b1000(
            lost_sig_top_ovflw, new_top_bits_ovflw
        ) : add_b1000(
            lost_sig_top, new_top_bits[CAP_M_WIDTH-1:0])
    );
    mw_t base_bits = (len_ovflw && int_exp) ? new_base_bits[CAP_M_WIDTH:1] : new_base_bits[CAP_M_WIDTH-1:0];
    mw_t final_base_bits = bot3z(int_exp, base_bits);

    bool_t exact = !(lost_sig_base || lost_sig_top);
    cap_fmt_t fmt = (int_exp) ? EMBEDDED_EXP : IMPLIED_EXP;

    // derive new length value and base mask
    ////////////////////////////////////////////////////////////////////////
    addrwe2_t length_lsb_set = (lmask ^ (lmask >> 1)) >> (CAP_M_WIDTH - 2 - 3);
    addrwe2_t base_mask =
          (int_exp) ? ( (len_max && lost_sig_top) ? ~lmask_lo_ovflw
                                                  : ~lmask_lo )
                    : {CAP_ADDR_WIDTH + 2{1'b1}};

    // perform well-formed checks on the result cap
    ////////////////////////////////////////////////////////////////////////
    if (final_exp == 6'd0 && base[CAP_ADDR_WIDTH-1-:CAP_M_WIDTH-2] != '0) begin
      ret.cap.tag = 1'b0;
    end

    // fold in return values and return
    ////////////////////////////////////////////////////////////////////////
    ret.cap.EF = fmt;
    ret.cap.bounds.exp = final_exp;
    ret.cap.bounds.top_bits = final_top_bits;
    ret.cap.bounds.base_bits = final_base_bits;
    ret.exact = exact;
    ret.mask = base_mask[CAP_ADDR_WIDTH-1:0];
    return ret;

  endfunction

  /**
      * @brief Function to set the capability object type to a arbitrary value.
      * @param cap capability in register format.
      * @param otype target object type for the capability.
      * @returns the input capability cap with otype field equal to the input otype.
      */
  function automatic cap_reg_t set_cap_reg_otype(cap_reg_t cap, otypew_t otype);
    cap_reg_t ret = cap;
    ret.otype = otype;
    return ret;
  endfunction

  /**
      * @brief Function to compute the capability offset address.
      * @param cap capability in register format.
      * @param dec_bounds decounds bounds meta data.
      * @returns the capability offset with size [CAP_ADDR_WIDTH-1:0].
      */
  function automatic capw_t cap_reg_to_cap_mem(cap_reg_t cap);
    cap_mem_t cap_mem = '{
        tag: cap.tag,
        uperms: cap.uperms,
        hperms: cap.hperms,
        res_hi: cap.res_hi,
        res_lo: cap.res_lo,
        flags: cap.flags,
        otype: cap.otype,
        EF: cap.EF,
        bounds: encode_bounds(cap.bounds, cap.EF),
        addr: cap.addr
    };
    return capw_t'(cap_mem);
  endfunction

  /**
      * @brief Function to compute the capability offset address.
      * @param cap capability in register format.
      * @param dec_bounds decounds bounds meta data.
      * @returns the capability offset with size [CAP_ADDR_WIDTH-1:0].
      */
  function automatic cap_reg_t cap_mem_to_cap_reg(cap_mem_t cap);
    cap_reg_t ret;
    cap_bounds_t bounds = decode_bounds(cap.bounds, cap.EF);
    ew_t exp = (bounds.exp > CAP_MAX_EXP) ? CAP_MAX_EXP : bounds.exp;
    ret = '{
        tag: cap.tag,
        uperms: cap.uperms,
        hperms: cap.hperms,
        flags: cap.flags,
        res_hi: cap.res_hi,
        res_lo: cap.res_lo,
        otype: cap.otype,
        EF: cap.EF,
        bounds: bounds,
        addr: cap.addr
    };
    return ret;
  endfunction

  /**
      * @brief Function to convert from encoded hperms and uperms field to format for reporting with gcperm.
      * @param hardware permissions in encoded format.
      * @param user/software permissions.
      * @returns permissions in the report format for gcperms.
      */
  function automatic cap_report_perms_t hperms_and_uperms_to_report_perms(
      cap_hperms_t hp_raw, upermsw_t up, logic perms_are_malformed);
    cap_hperms_t hp = perms_are_malformed ? '0 : hp_raw;
    cap_report_perms_t rp = '{
        reserved_hi          : 0,  //Newer spec:'1,
        permit_load          : hp.permit_load,
        permit_execute       : hp.permit_execute,
        access_sys_regs      : hp.access_sys_regs,
        reserved_lo          : 0,  //Newer spec:'1,
        uperms               : up,
        permit_cap           : hp.permit_cap,
        cap_level            : hp_raw.cap_level,  // Not a permission, so not legalised
        permit_store_level   : hp.permit_store_level,
        permit_elevate_level : hp.permit_elevate_level,
        permit_load_mutable  : hp.permit_load_mutable,
        permit_store         : hp.permit_store
    };
    return rp;
  endfunction

  /**
      * @brief Function to convert from reported permissions format for andperms to encoded hardware permissions.
      * @param permissions in the report format for ACPERM.
      * @returns hardware permissions in encoded format. Note that legalisation must be performed outside.
      */
  function automatic cap_hperms_t report_perms_to_hperms(cap_report_perms_t rp);
    cap_hperms_t hp = '{
        permit_store_level   : rp.permit_store_level,
        permit_elevate_level : rp.permit_elevate_level,
        permit_load_mutable  : rp.permit_load_mutable,
        access_sys_regs      : rp.access_sys_regs,
        permit_execute       : rp.permit_execute,
        permit_load          : rp.permit_load,
        permit_store         : rp.permit_store,
        permit_cap           : rp.permit_cap,
        cap_level            : rp.cap_level
    };
    return hp;
  endfunction

  /**
      * Capability Auxiliary functions
      */

  /**
      * @brief Function that creates a mask from the msb set to 1 till 0
      * @param x value to extract mask from.
      * @returns a mask with all 1 from the msb bit set to 1 till 0.
      */
  function automatic addrwe2_t smearMSBRight(addrwe2_t x);
    addrwe2_t res = x;
    for (int i = 0; i < $clog2(CAP_ADDR_WIDTH + 2) - 1; i = i + 1) res = res | (res >> 2 ** i);
    return res;
  endfunction

  /**
      * @brief Function counts the number of 0 from [64:13]
      * @param val value to extract count the zerios.
      * @returns the number of zeros from [64:13].
      */
  function automatic ew_t count_zeros_msb(addrmwm2_t val);
    ew_t res = 0;
    for (int i = CAP_ADDR_WIDTH - (CAP_M_WIDTH - 1); i >= 0; i = i - 1) begin
      if (!val[i]) res = res + 1;
      else return res;
    end
    return res;
  endfunction


  /**
      * @brief Extract mantissa-relevant bits from an address
      * @param addr Address to extract from
      * @param exp Exponent to use for shift
      * @returns the mantissa_width slice referred to by exp
      */
  function automatic mw_t extract_addr_mid(addrw_t addr, ew_t exp);
    automatic addrwe2_t shifted_value = {2'b0, addr} << exp;
    return shifted_value[CAP_ADDR_WIDTH+1-:CAP_M_WIDTH];
  endfunction

  /**
      * @brief Function to decode from compressed bounds to decoded bounds
      * @param cbounds compressed bounds in memory.
      * @param format  bounds format
      * @returns the decoded bounds.
      */
  function automatic cap_bounds_t decode_bounds(cap_cbounds_t cbounds, cap_fmt_t format);
    cap_bounds_t       cap_bounds = DEFAULT_BOUNDS_CAP;
    logic        [1:0] l_carry_out = 2'b00;
    logic        [1:0] l_msb = 2'b00;
    logic        [1:0] dec_top_bits = 2'b00;

    case (format)
      EMBEDDED_EXP: begin
        cap_bounds.exp = {cbounds.emb_exp_fmt.exp_top_bits, cbounds.emb_exp_fmt.exp_base_bits};
        cap_bounds.top_bits = {2'b00, cbounds.emb_exp_fmt.top_bits, 3'b000};
        cap_bounds.base_bits = {cbounds.emb_exp_fmt.base_bits, 3'b000};
      end
      IMPLIED_EXP: begin
        cap_bounds.exp       = CAP_MAX_EXP;
        cap_bounds.top_bits  = {2'b00, cbounds.impl_exp_fmt.top[11:0]};
        cap_bounds.base_bits = cbounds.impl_exp_fmt.base;
      end
      default: ;
    endcase

    l_carry_out = (cap_bounds.top_bits[11:0] < cap_bounds.base_bits[11:0]) ? 2'b01 : 2'b00;
    l_msb = (format == IMPLIED_EXP) ? 2'b00 : 2'b01;
    dec_top_bits = cap_bounds.base_bits[13:12] + l_carry_out + l_msb;

    cap_bounds.top_bits = {dec_top_bits, cap_bounds.top_bits[11:0]};
    return cap_bounds;
  endfunction

  /**
      * @brief Function to encode from decoded bounds to compressed bounds
      * @param bounds decoded bounds in register capability.
      * @param format bounds format
      * @returns the compressed bounds encoded format.
      */
  function automatic cap_cbounds_t encode_bounds(cap_bounds_t bounds, cap_fmt_t format);
    cap_cbounds_t cap_cbounds = DEFAULT_CBOUNDS_CAP;
    hew_t exp_msb = bounds.exp[CAP_E_WIDTH-1:CAP_E_HALF_WIDTH];
    hew_t exp_lsb = bounds.exp[CAP_E_HALF_WIDTH-1:0];
    hcmw_t top_bits = bounds.top_bits[CAP_M_WIDTH-3:CAP_E_HALF_WIDTH];
    hmw_t base_bits = bounds.base_bits[CAP_M_WIDTH-1:CAP_E_HALF_WIDTH];

    /* if (bounds.exp > CAP_RESET_EXP) begin
            exp_msb = 3'b110;
            exp_lsb = 3'b100;
        end */

    case (format)
      IMPLIED_EXP: begin
        cap_cbounds.cbounds.top_bits  = bounds.top_bits[CAP_M_WIDTH-3:0];
        cap_cbounds.cbounds.base_bits = bounds.base_bits;
      end
      EMBEDDED_EXP: begin
        cap_cbounds.cbounds.top_bits  = {top_bits, exp_msb};
        cap_cbounds.cbounds.base_bits = {base_bits, exp_lsb};
      end
      default: ;
    endcase
    return cap_cbounds;
  endfunction
  //TODO-cheri(ninolomata): Wrappers for the CHERI API standard
endpackage
