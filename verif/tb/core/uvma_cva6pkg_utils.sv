
function st_core_cntrl_cfg cva6pkg_to_core_cntrl_cfg(st_core_cntrl_cfg base);

    automatic config_pkg::cva6_cfg_t CVA6Cfg = build_config_pkg::build_config(cva6_config_pkg::cva6_cfg);

    $cast(base.xlen, cva6_config_pkg::CVA6ConfigXlen);

    base.ilen = cva6_config_pkg::CVA6ConfigXlen;

    base.ext_i_supported = 1;
    base.ext_a_supported = CVA6Cfg.RVA;
    base.ext_m_supported = 1;
    base.ext_c_supported = CVA6Cfg.RVC;
    base.ext_p_supported = 1;
    base.ext_v_supported = CVA6Cfg.RVV;
    base.ext_f_supported = CVA6Cfg.RVF | CVA6Cfg.FpuEn;
    base.ext_d_supported = CVA6Cfg.RVD;
    base.ext_zba_supported = cva6_config_pkg::CVA6ConfigBExtEn;
    base.ext_zbb_supported = cva6_config_pkg::CVA6ConfigBExtEn;
    base.ext_zbc_supported = cva6_config_pkg::CVA6ConfigBExtEn;
    base.ext_zbe_supported = cva6_config_pkg::CVA6ConfigBExtEn;
    base.ext_zbf_supported = 0;
    base.ext_zbm_supported = 0;
    base.ext_zbp_supported = 0;
    base.ext_zbr_supported = 0;
    base.ext_zbs_supported = cva6_config_pkg::CVA6ConfigBExtEn;
    base.ext_zbt_supported = 0;
    base.ext_zcb_supported = CVA6Cfg.RVZCB;
    base.ext_zifencei_supported = 1;
    base.ext_zicsr_supported = 1;
    base.ext_zicntr_supported = 1;

    base.mode_s_supported = CVA6Cfg.RVS;
    base.mode_u_supported = CVA6Cfg.RVU;

    base.pmp_supported = (CVA6Cfg.NrPMPEntries > 0);
    base.pmp_regions = CVA6Cfg.NrPMPEntries;
    base.debug_supported = CVA6Cfg.DebugEn;

    return base;

endfunction : cva6pkg_to_core_cntrl_cfg

