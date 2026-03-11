# CLIC
if {![info exists clic]} {
    set clic "/test/i_dut/i_clic"
}

add wave -group CLIC ${clic}/clk_i
add wave -group CLIC ${clic}/rst_ni
add wave -group CLIC ${clic}/reg_req_i
add wave -group CLIC ${clic}/reg_rsp_o
add wave -group CLIC ${clic}/intr_src_i
add wave -group CLIC ${clic}/irq_valid_o
add wave -group CLIC ${clic}/irq_ready_i
add wave -group CLIC ${clic}/irq_id_o
add wave -group CLIC ${clic}/irq_level_o
add wave -group CLIC ${clic}/irq_shv_o
add wave -group CLIC ${clic}/irq_priv_o
add wave -group CLIC ${clic}/irq_v_o
add wave -group CLIC ${clic}/irq_vsid_o
add wave -group CLIC ${clic}/irq_kill_req_o
add wave -group CLIC ${clic}/irq_kill_ack_i
add wave -group CLIC ${clic}/irq_max
add wave -group CLIC ${clic}/irq_mode
add wave -group CLIC ${clic}/ie
add wave -group CLIC ${clic}/ip
add wave -group CLIC ${clic}/ip_sw
add wave -group CLIC ${clic}/shv
