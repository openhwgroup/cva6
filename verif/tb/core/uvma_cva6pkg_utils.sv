
function st_core_cntrl_cfg cva6pkg_to_core_cntrl_cfg(st_core_cntrl_cfg base);

    $cast(base.xlen, cva6_config_pkg::CVA6ConfigXlen);

    base.ilen = cva6_config_pkg::CVA6ConfigXlen;

    base.ext_i_supported = 1;
    base.ext_a_supported = cva6_config_pkg::cva6_cfg.RVA;
    base.ext_m_supported = 1;
    base.ext_c_supported = cva6_config_pkg::cva6_cfg.RVC;
    base.ext_p_supported = 1;
    base.ext_v_supported = cva6_config_pkg::cva6_cfg.RVV;
    base.ext_f_supported = cva6_config_pkg::cva6_cfg.RVF | cva6_config_pkg::cva6_cfg.FpuEn;
    base.ext_d_supported = cva6_config_pkg::cva6_cfg.RVD;
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
    base.ext_zcb_supported = cva6_config_pkg::cva6_cfg.RVZCB;
    base.ext_zifencei_supported = 1;
    base.ext_zicsr_supported = 1;
    base.ext_zicntr_supported = 1;

    base.mode_s_supported = cva6_config_pkg::cva6_cfg.RVS;
    base.mode_u_supported = cva6_config_pkg::cva6_cfg.RVU;

    base.pmp_supported = (cva6_config_pkg::cva6_cfg.NrPMPEntries > 0);
    base.pmp_regions = cva6_config_pkg::cva6_cfg.NrPMPEntries;
    base.debug_supported = cva6_config_pkg::cva6_cfg.DebugEn;

    return base;

endfunction : cva6pkg_to_core_cntrl_cfg

