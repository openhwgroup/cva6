import "DPI-C" function void spike_set_param_uint64_t(string base, string name, longint unsigned value);
import "DPI-C" function void spike_set_param_str(string base, string name, string value);
import "DPI-C" function void spike_set_param_bool(string base, string name, bit value);
import "DPI-C" function void spike_set_default_params(string profile);

function st_core_cntrl_cfg cva6pkg_to_core_cntrl_cfg(st_core_cntrl_cfg cfg);

    string base;

    base = $sformatf("/top/core/%0d/", cfg.mhartid);

    void'(spike_set_param_bool(base, "hide_csrs_based_on_priv", 1));
    void'(spike_set_param_uint64_t(base, "mtvec_vectored_alignment", 64 * 4));
    void'(spike_set_param_str(base, "extensions", "cv32a60x"));

    // All enabled except XS and TW bits
    void'(spike_set_param_uint64_t(base, "mstatus_write_mask", 'hFFDE_7FFF));

    if (cfg.DirectVecOnly) begin
      void'(spike_set_param_uint64_t(base, "mtvec_write_mask", 32'hFFFF_FFFC));
    end

    void'(spike_set_param_uint64_t(base, "misa_override_value", get_misa(cfg)));
    void'(spike_set_param_uint64_t(base, "misa_override_mask", 64'h0FFF_FFFF));
    void'(spike_set_param_bool    (base, "misa_we_enable", 1'b1));
    void'(spike_set_param_bool    (base, "misa_we", 1'b0));

    if (!cfg.TvalEn) begin
      void'(spike_set_param_bool    (base, "mtval_we_enable", 1'b1));
      void'(spike_set_param_bool    (base, "mtval_we", 1'b0));
    end

    return cfg;

endfunction : cva6pkg_to_core_cntrl_cfg
