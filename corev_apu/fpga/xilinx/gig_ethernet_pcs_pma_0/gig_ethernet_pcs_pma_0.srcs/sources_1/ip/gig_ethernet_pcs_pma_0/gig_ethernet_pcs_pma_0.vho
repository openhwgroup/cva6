-- (c) Copyright 1995-2026 Xilinx, Inc. All rights reserved.
-- 
-- This file contains confidential and proprietary information
-- of Xilinx, Inc. and is protected under U.S. and
-- international copyright and other intellectual property
-- laws.
-- 
-- DISCLAIMER
-- This disclaimer is not a license and does not grant any
-- rights to the materials distributed herewith. Except as
-- otherwise provided in a valid license issued to you by
-- Xilinx, and to the maximum extent permitted by applicable
-- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
-- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
-- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
-- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
-- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
-- (2) Xilinx shall not be liable (whether in contract or tort,
-- including negligence, or under any other theory of
-- liability) for any loss or damage of any kind or nature
-- related to, arising under or in connection with these
-- materials, including for any direct, or any indirect,
-- special, incidental, or consequential loss or damage
-- (including loss of data, profits, goodwill, or any type of
-- loss or damage suffered as a result of any action brought
-- by a third party) even if such damage or loss was
-- reasonably foreseeable or Xilinx had been advised of the
-- possibility of the same.
-- 
-- CRITICAL APPLICATIONS
-- Xilinx products are not designed or intended to be fail-
-- safe, or for use in any application requiring fail-safe
-- performance, such as life-support or safety devices or
-- systems, Class III medical devices, nuclear facilities,
-- applications related to the deployment of airbags, or any
-- other applications that could lead to death, personal
-- injury, or severe property or environmental damage
-- (individually and collectively, "Critical
-- Applications"). Customer assumes the sole risk and
-- liability of any use of Xilinx products in Critical
-- Applications, subject only to applicable laws and
-- regulations governing limitations on product liability.
-- 
-- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
-- PART OF THIS FILE AT ALL TIMES.
-- 
-- DO NOT MODIFY THIS FILE.

-- IP VLNV: xilinx.com:ip:gig_ethernet_pcs_pma:16.2
-- IP Revision: 0

-- The following code must appear in the VHDL architecture header.

------------- Begin Cut here for COMPONENT Declaration ------ COMP_TAG
COMPONENT gig_ethernet_pcs_pma_0
  PORT (
    gtrefclk_p : IN STD_LOGIC;
    gtrefclk_n : IN STD_LOGIC;
    gtrefclk_out : OUT STD_LOGIC;
    gtrefclk_bufg_out : OUT STD_LOGIC;
    txn : OUT STD_LOGIC;
    txp : OUT STD_LOGIC;
    rxn : IN STD_LOGIC;
    rxp : IN STD_LOGIC;
    independent_clock_bufg : IN STD_LOGIC;
    userclk_out : OUT STD_LOGIC;
    userclk2_out : OUT STD_LOGIC;
    rxuserclk_out : OUT STD_LOGIC;
    rxuserclk2_out : OUT STD_LOGIC;
    resetdone : OUT STD_LOGIC;
    pma_reset_out : OUT STD_LOGIC;
    mmcm_locked_out : OUT STD_LOGIC;
    sgmii_clk_r : OUT STD_LOGIC;
    sgmii_clk_f : OUT STD_LOGIC;
    sgmii_clk_en : OUT STD_LOGIC;
    gmii_txd : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
    gmii_tx_en : IN STD_LOGIC;
    gmii_tx_er : IN STD_LOGIC;
    gmii_rxd : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    gmii_rx_dv : OUT STD_LOGIC;
    gmii_rx_er : OUT STD_LOGIC;
    gmii_isolate : OUT STD_LOGIC;
    configuration_vector : IN STD_LOGIC_VECTOR(4 DOWNTO 0);
    an_interrupt : OUT STD_LOGIC;
    an_adv_config_vector : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    an_restart_config : IN STD_LOGIC;
    speed_is_10_100 : IN STD_LOGIC;
    speed_is_100 : IN STD_LOGIC;
    status_vector : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    reset : IN STD_LOGIC;
    signal_detect : IN STD_LOGIC;
    gt0_qplloutclk_out : OUT STD_LOGIC;
    gt0_qplloutrefclk_out : OUT STD_LOGIC
  );
END COMPONENT;
-- COMP_TAG_END ------ End COMPONENT Declaration ------------

-- The following code must appear in the VHDL architecture
-- body. Substitute your own instance name and net names.

------------- Begin Cut here for INSTANTIATION Template ----- INST_TAG
your_instance_name : gig_ethernet_pcs_pma_0
  PORT MAP (
    gtrefclk_p => gtrefclk_p,
    gtrefclk_n => gtrefclk_n,
    gtrefclk_out => gtrefclk_out,
    gtrefclk_bufg_out => gtrefclk_bufg_out,
    txn => txn,
    txp => txp,
    rxn => rxn,
    rxp => rxp,
    independent_clock_bufg => independent_clock_bufg,
    userclk_out => userclk_out,
    userclk2_out => userclk2_out,
    rxuserclk_out => rxuserclk_out,
    rxuserclk2_out => rxuserclk2_out,
    resetdone => resetdone,
    pma_reset_out => pma_reset_out,
    mmcm_locked_out => mmcm_locked_out,
    sgmii_clk_r => sgmii_clk_r,
    sgmii_clk_f => sgmii_clk_f,
    sgmii_clk_en => sgmii_clk_en,
    gmii_txd => gmii_txd,
    gmii_tx_en => gmii_tx_en,
    gmii_tx_er => gmii_tx_er,
    gmii_rxd => gmii_rxd,
    gmii_rx_dv => gmii_rx_dv,
    gmii_rx_er => gmii_rx_er,
    gmii_isolate => gmii_isolate,
    configuration_vector => configuration_vector,
    an_interrupt => an_interrupt,
    an_adv_config_vector => an_adv_config_vector,
    an_restart_config => an_restart_config,
    speed_is_10_100 => speed_is_10_100,
    speed_is_100 => speed_is_100,
    status_vector => status_vector,
    reset => reset,
    signal_detect => signal_detect,
    gt0_qplloutclk_out => gt0_qplloutclk_out,
    gt0_qplloutrefclk_out => gt0_qplloutrefclk_out
  );
-- INST_TAG_END ------ End INSTANTIATION Template ---------

-- You must compile the wrapper file gig_ethernet_pcs_pma_0.vhd when simulating
-- the core, gig_ethernet_pcs_pma_0. When compiling the wrapper file, be sure to
-- reference the VHDL simulation library.

