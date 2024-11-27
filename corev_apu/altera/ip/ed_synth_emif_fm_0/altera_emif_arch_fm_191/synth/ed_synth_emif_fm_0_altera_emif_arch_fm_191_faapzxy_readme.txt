---------------------
; Table of Contents ;
---------------------
  1. About this file
  2. Outputs of IP generation
  3. Instantiating IP in a Quartus Prime project
  4. Board Signal Integrity Analysis
  5. I/O assignments
  6. Pin locations
  7. Sharing core clocks between interfaces
  8. Sharing PLL reference clock pin between interfaces
  9. Local reset request. Output signal from local_reset_combiner 
 10. Local reset status. Input signal to the local_reset_combiner
 11. PLL reference clock input
 12. PLL locked signal
 13. On-Chip Termination (OCT) interface
 14. Interface between FPGA and external memory
 15. PHY calibration status interface
 16. User clock domain reset interface
 17. User clock interface
 18. Controller Avalon Streaming command interface 0
 19. Controller Avalon Streaming write data interface 0
 20. Controller Avalon Streaming read data interface 0
 21. Controller ECC interface 0
 22. EMIF calibration component interface
 23. EMIF calibration component clock input interface
 24. Instantiating IP in a simulation project
 25. Full-calibration versus skip-calibration simulation
 26. IP Settings


------------------------
;   1. About this file ;
------------------------

   This is the readme file for the Intel External Memory Interface (EMIF) IP v24.1.
   
   The file provides a high-level overview of the IP. For details, refer to the
   handbook chapter on Agilex DDR4 External Memory Interface.
   
   This file was auto-generated.


---------------------------------
;   2. Outputs of IP generation ;
---------------------------------

   IP generation supports the following output filesets:
   
      Synthesis            - This is the fileset you should use when instantiating the IP in
                             your Quartus Prime project. RTL files in this fileset can be
                             simulated, but your simulator must support SystemVerilog.
                             Simulating the synthesis files yields identical results as
                             simulating the simulation files.
   
      Simulation           - This fileset contains scripts and source files to help you
                             integrate the IP into your simulation project targeting a
                             3rd-party simulator of your choice. If you select VHDL
                             during IP generation, the fileset contains IEEE-encrypted
                             Verilog files that can be used in VHDL-only simulators, such
                             as ModelSim - Intel FPGA edition. All source files in the simulation
                             filesets are functionally equivalent to the synthesis fileset.
   
      Signal Integrity     - This fileset contains SPICE simulation decks and compliance
                             mask information for evaluating if your PCB meets the signal
                             integrity requirements of your desired interface. It is
                             strongly recommended that customers obtain 12-line extractions of
                             their PCBs and evaluate them using this flow in order to
                             reduce the risk of encountering signal-integrity issues
                             in their memory interface design. SPICE decks are provided to
                             generate eye diagrams at the receiver for the address/command
                             channel, the data write channel, and the data read channel.
   
      Example Design       - This fileset contains scripts to generate example Quartus Prime project
                             and simulation projects for 3rd-party simulators. An example
                             design contains an instantiation of the IP, a simple traffic
                             generator, and in the case of a simulation example design, a
                             simple memory model.


----------------------------------------------------
;   3. Instantiating IP in a Quartus Prime project ;
----------------------------------------------------

   If you instantiate the IP as part of a Platform Designer system, follow the Platform Designer
   documentation on how to instantiate the system in a Quartus Prime project.
   
   If the IP was generated as a standalone component, it is sufficient to add
   the generated .qip file from the synthesis fileset to your Quartus Prime project.
   The .qip file allows the Quartus Prime software to locate all the files of
   the IP, including RTL files, SDC files, hex files, and timing scripts. Once the
   .qip file is added, you can instantiate the memory interface in your RTL.


----------------------------------------
;   4. Board Signal Integrity Analysis ;
----------------------------------------

   The Board Signal Integrity analysis allows you to evaluate whether or not your
   External Memory Interface channel meets the impedance, crosstalk and ISI requirements
   to operate your memory interface at the target frequency while meeting the minimum
   data eye height and width requirements for reliable data capture.
   The analysis environment takes into account the signal integrity settings you have
   selected in the IP GUI for FPGA-side drive/receive strength, memory-side termination
   settings, and where applicable, termination settings for channels with multiple memory
   ranks (including the associated dynamic/nominal/park termination settings).
   Customers must supply the location of the FPGA and memory IBIS models, as well as the
   location of the 12-line PCB extraction models for the interface address/command and
   data channel models.  Package RLC values for the FPGA and memory must also be specified
   for accurate simulation.
   
   To run signal integrity analysis:
   
      1) Open the EMIF IP GUI
      2) Select all of the FPGA and Memory drive strength and termination settings for your design
      3) Select the "Signal Integrity" checkbox under the "Example Designs" tab
      4) Generate the IP or click the "Generate Example Design" button
      5) Locate the *_spice_files.zip and *_ip_parameters.dat files
      6) Update the *_ip_parameters.dat file with the location of your IBIS models and RLC values
      7) Unzip the *_spice_files.zip file, update the top-level SPICE decks to include the *.dat file
         above, and run the simulations for Address/Command, Data Write and Data Read channels.
   
   Note that most of the settings that are relevant to this instance of IP are contained within the
   auto-generated *_ip_parameters.dat file.  If you modify this file, please be sure to save a backup
   copy in case you need to restore the original simulation parameters.  The *_spice_files.zip file
   contails files that are common to all instances of IP, with the exception of the file
   "pin_parasitics.dat", which must be updated with the pin RLC parasitic information for both the
   FPGA and memory devices.  Consult the EMIF IP Handbook for further details.


------------------------
;   5. I/O assignments ;
------------------------

   The generated .qip file in the synthesis fileset contains the I/O standard and input/output
   termination assignments required by the memory interface pins to function correctly.
   The values to the assignments are based on user inputs provided during generation.
   
   Unlike previous EMIF IP, there is no need to manually run a *_pin_assignments.tcl
   script to annotate the assignments into the project's .qsf file.
   Assignments in the .qip file are read and applied during every compilation, regardless
   of how you name the memory interface pins in your design top-level component. No new
   assignment is created in the project's .qsf file during the process.
   
   You should never edit the generated .qip file, because changes made to this file
   are overwritten when you regenerate the IP. To override an I/O assignment made in
   the .qip file, simply add an assignment to the project's .qsf file. Assignments in
   the .qsf file always take precedence over those in the .qip file. Note that I/O
   assignments in the .qsf file must specify the names of your top-level pins as
   target (i.e. -to), and you must not use the -entity and -library options.
   
   Consult the .qip file for the set of I/O assignments that come with the IP.


----------------------
;   6. Pin locations ;
----------------------

   The Agilex I/O subsystem is located in the I/O rows.
   
   The pins of a memory interface must be placed within a single I/O row. A memory
   interface can occupy one or more banks. When multiple banks are needed, the banks must
   be consecutive.
   
   All address/command pins of a memory interface must be placed within a single bank.
   This bank is denoted as the "address/command" bank. While any physical bank within
   an I/O row can be used as an "address/command" bank, for a multi-bank memory
   interface, the "address/command" bank must be at the center of the interface.
   
   Address/command pins within the "address/command" bank must follow a fixed pinout
   scheme within the bank. Note that the pinout scheme used is dependent on the topology
   of the memory interface, and is a hardware requirement. An I/O lane unused in the
   "address/command" bank can be used to implement a data group (e.g. a x8 DQS group).
   
   A read data group must be placed based on the DQS/CQ/QK grouping in the pin table.
   Specifically, read data strobes/clocks must be placed at physical pins capable of
   functioning as DQS/CK/QK for a specific read data group size, and the associated
   data pins must be placed within the same group.
   A x8/x9 read data group occupies one lane; a x16/x18 read data group occupies either
   the top or bottom 2 lanes of a bank; a x36 read data group occupies all four lanes of
   a bank. For protocols/topologies where a write data group consists of multiple read data
   groups, the read data groups should be placed in the same bank to improve I/O timing.
   
   I/Os that are unused by memory interface pins can be used as general-purpose I/Os with
   compatible I/O standard and termination settings.
   
   The following shows one possible grouping of memory interface pins into logical banks. To
   implement the scheme in your Quartus Prime project, you need to:
   
      1) Decide which physical I/O banks the logical banks occupy.
      2) Add location assignments for the following pins:
            All read data strobes/clocks (e.g. DQS/CQ/DQ)
            One of the address/command pins
            PLL reference clock pins (unless using a shared PLL reference clock pin in another interface)
            RZQ pin
         The Quartus Prime Fitter automatically places the remaining pins.
   
   The current memory interface occupies 4 banks.
   
   Note that this is only an example and other possible schemes may exist. The example
   is functionally correct and legal, but is not necessarily optimal from the resource
   consumption, timing, and board routability perspective.
   
   Logical bank 3:
   ----------------------
   
      Lane index      Pin index       Port                  
      -------------------------------------------------------
      3               47              -
      .               46              -
      .               45              -
      .               44              -
      .               43              -
      .               42              -
      .               41              -
      .               40              -
      .               39              -
      .               38              -
      .               37              -
      .               36              -
      2               35              -
      .               34              -
      .               33              -
      .               32              -
      .               31              -
      .               30              -
      .               29              -
      .               28              -
      .               27              -
      .               26              -
      .               25              -
      .               24              -
      1               23              -
      .               22              -
      .               21              -
      .               20              -
      .               19              -
      .               18              -
      .               17              -
      .               16              -
      .               15              -
      .               14              -
      .               13              -
      .               12              -
      0               11              mem_dq[71]
      .               10              mem_dq[70]
      .               9               mem_dq[69]
      .               8               mem_dq[68]
      .               7               -
      .               6               mem_dbi_n[8]
      .               5               mem_dqs_n[8]
      .               4               mem_dqs[8]
      .               3               mem_dq[67]
      .               2               mem_dq[66]
      .               1               mem_dq[65]
      .               0               mem_dq[64]
   
   Logical bank 2:
   ----------------------
   
      Lane index      Pin index       Port                  
      -------------------------------------------------------
      3               47              mem_dq[63]
      .               46              mem_dq[62]
      .               45              mem_dq[61]
      .               44              mem_dq[60]
      .               43              -
      .               42              mem_dbi_n[7]
      .               41              mem_dqs_n[7]
      .               40              mem_dqs[7]
      .               39              mem_dq[59]
      .               38              mem_dq[58]
      .               37              mem_dq[57]
      .               36              mem_dq[56]
      2               35              mem_dq[55]
      .               34              mem_dq[54]
      .               33              mem_dq[53]
      .               32              mem_dq[52]
      .               31              -
      .               30              mem_dbi_n[6]
      .               29              mem_dqs_n[6]
      .               28              mem_dqs[6]
      .               27              mem_dq[51]
      .               26              mem_dq[50]
      .               25              mem_dq[49]
      .               24              mem_dq[48]
      1               23              mem_dq[47]
      .               22              mem_dq[46]
      .               21              mem_dq[45]
      .               20              mem_dq[44]
      .               19              -
      .               18              mem_dbi_n[5]
      .               17              mem_dqs_n[5]
      .               16              mem_dqs[5]
      .               15              mem_dq[43]
      .               14              mem_dq[42]
      .               13              mem_dq[41]
      .               12              mem_dq[40]
      0               11              mem_dq[39]
      .               10              mem_dq[38]
      .               9               mem_dq[37]
      .               8               mem_dq[36]
      .               7               -
      .               6               mem_dbi_n[4]
      .               5               mem_dqs_n[4]
      .               4               mem_dqs[4]
      .               3               mem_dq[35]
      .               2               mem_dq[34]
      .               1               mem_dq[33]
      .               0               mem_dq[32]
   
   Logical bank 1 (address/command bank):
   --------------------------------------------
   
      Address/command pinout scheme  : DDR4 Scheme 1A: Component and DIMM (with A17)
      Number of address/command lanes: 4
   
      Lane index      Pin index       Port                  
      -------------------------------------------------------
      3               47              -
      .               46              -
      .               45              -
      .               44              mem_alert_n[0]
      .               43              -
      .               42              -
      .               41              -
      .               40              -
      .               39              -
      .               38              -
      .               37              -
      .               36              -
      2               35              mem_bg[0]
      .               34              mem_ba[1]
      .               33              mem_ba[0]
      .               32              -
      .               31              mem_a[16]
      .               30              mem_a[15]
      .               29              mem_a[14]
      .               28              mem_a[13]
      .               27              mem_a[12]
      .               26              oct_rzqin - if needed
      .               25              pll_ref_clk (negative leg) - if needed
      .               24              pll_ref_clk (positive leg) - if needed
      1               23              mem_a[11]
      .               22              mem_a[10]
      .               21              mem_a[9]
      .               20              mem_a[8]
      .               19              mem_a[7]
      .               18              mem_a[6]
      .               17              mem_a[5]
      .               16              mem_a[4]
      .               15              mem_a[3]
      .               14              mem_a[2]
      .               13              mem_a[1]
      .               12              mem_a[0]
      0               11              mem_par[0]
      .               10              -
      .               9               mem_ck_n[0]
      .               8               mem_ck[0]
      .               7               -
      .               6               mem_cke[0]
      .               5               -
      .               4               mem_odt[0]
      .               3               mem_act_n[0]
      .               2               mem_cs_n[0]
      .               1               mem_reset_n[0]
      .               0               mem_bg[1]
   
   Logical bank 0:
   ----------------------
   
      Lane index      Pin index       Port                  
      -------------------------------------------------------
      3               47              mem_dq[31]
      .               46              mem_dq[30]
      .               45              mem_dq[29]
      .               44              mem_dq[28]
      .               43              -
      .               42              mem_dbi_n[3]
      .               41              mem_dqs_n[3]
      .               40              mem_dqs[3]
      .               39              mem_dq[27]
      .               38              mem_dq[26]
      .               37              mem_dq[25]
      .               36              mem_dq[24]
      2               35              mem_dq[23]
      .               34              mem_dq[22]
      .               33              mem_dq[21]
      .               32              mem_dq[20]
      .               31              -
      .               30              mem_dbi_n[2]
      .               29              mem_dqs_n[2]
      .               28              mem_dqs[2]
      .               27              mem_dq[19]
      .               26              mem_dq[18]
      .               25              mem_dq[17]
      .               24              mem_dq[16]
      1               23              mem_dq[15]
      .               22              mem_dq[14]
      .               21              mem_dq[13]
      .               20              mem_dq[12]
      .               19              -
      .               18              mem_dbi_n[1]
      .               17              mem_dqs_n[1]
      .               16              mem_dqs[1]
      .               15              mem_dq[11]
      .               14              mem_dq[10]
      .               13              mem_dq[9]
      .               12              mem_dq[8]
      0               11              mem_dq[7]
      .               10              mem_dq[6]
      .               9               mem_dq[5]
      .               8               mem_dq[4]
      .               7               -
      .               6               mem_dbi_n[0]
      .               5               mem_dqs_n[0]
      .               4               mem_dqs[0]
      .               3               mem_dq[3]
      .               2               mem_dq[2]
      .               1               mem_dq[1]
      .               0               mem_dq[0]


-----------------------------------------------
;   7. Sharing core clocks between interfaces ;
-----------------------------------------------

   When a design contains multiple memory interfaces of the same protocol, rate,
   frequency, and PLL reference clock source, it is possible for these interfaces
   to share a common set of core clock signals. Core clocks sharing allows your
   logic to use a single clock domain to synchronously access all interfaces.
   The feature also reduces the number of core clock networks required.
   
   In order for multiple memory interfaces to share core clocks, one of the interfaces
   must be specified as "Master" using the "Core clocks sharing" setting during
   generation, and the remaining interfaces must be denoted as "Slave". There is no
   preference to which interface needs to be a master. In the RTL, connect the
   clks_sharing_master_out signal from the master interface to the clks_sharing_slave_in
   signal of all the slave interfaces. Note that both the master and slave interfaces
   expose their own output clock ports in the RTL (e.g. emif_usr_clk, afi_clk), but the
   physical signals are equivalent and so it does not matter whether a clock port from a
   master or a slave is used.
   
   Core clocks sharing necessitates PLL reference clock sharing. Therefore,
   only the master interface exposes an input port for the PLL reference clock. The
   same PLL reference clock signal is used by all the slave interfaces. See section
   on PLL reference clock sharing for additional requirements.
   
   The core clocks sharing mode of the current IP is "No Sharing"


-----------------------------------------------------------
;   8. Sharing PLL reference clock pin between interfaces ;
-----------------------------------------------------------

   To share a single PLL reference clock signal between multiple memory interfaces,
   simply connect the same PLL reference clock signal to all interfaces in the RTL.
   
   Interfaces that share the same PLL reference clock signal must be placed in the
   same I/O row and must occupy consecutive banks.


----------------------------------------------------------------------
;   9. Local reset request. Output signal from local_reset_combiner  ;
----------------------------------------------------------------------

   Port                           Width   Direction   Description                                        
   ------------------------------------------------------------------------------------------------------
   local_reset_req                1       input       Signal from user logic to request the memory interface to be reset and recalibrated. Reset request is sent by transitioning the local_reset_req signal from low to high, then keeping the signal at the high state for a minimum of 2 EMIF core clock cycles, then transitioning the signal from high to low. local_reset_req is asynchronous in that there is no setup/hold timing to meet, but it must meet the minimum pulse width requirement of 2 EMIF core clock cycles.  


---------------------------------------------------------------------
;  10. Local reset status. Input signal to the local_reset_combiner ;
---------------------------------------------------------------------

   Port                           Width   Direction   Description                                        
   ------------------------------------------------------------------------------------------------------
   local_reset_done               1       output      Signal from memory interface to indicate whether it has completed a reset sequence, is currently out of reset, and is ready for a new reset request.  When local_reset_done is low, the memory interface is in reset.


----------------------------------
;  11. PLL reference clock input ;
----------------------------------

   Port                           Width   Direction   Description                                        
   ------------------------------------------------------------------------------------------------------
   pll_ref_clk                    1       input       PLL reference clock input


--------------------------
;  12. PLL locked signal ;
--------------------------

   Port                           Width   Direction   Description                                        
   ------------------------------------------------------------------------------------------------------
   pll_locked                     1       output      PLL lock signal to indicate whether the PLL has locked


--------------------------------------------
;  13. On-Chip Termination (OCT) interface ;
--------------------------------------------

   Port                           Width   Direction   Description                                        
   ------------------------------------------------------------------------------------------------------
   oct_rzqin                      1       input       Calibrated On-Chip Termination (OCT) RZQ input pin


---------------------------------------------------
;  14. Interface between FPGA and external memory ;
---------------------------------------------------

   Port                           Width   Direction   Description                                        
   ------------------------------------------------------------------------------------------------------
   mem_ck                         1       output      CK clock
   mem_ck_n                       1       output      CK clock (negative leg)
   mem_a                          17      output      Address
   mem_act_n                      1       output      Activation command
   mem_ba                         2       output      Bank address
   mem_bg                         2       output      Bank group
   mem_cke                        1       output      Clock enable
   mem_cs_n                       1       output      Chip select
   mem_odt                        1       output      On-die termination
   mem_reset_n                    1       output      Asynchronous reset
   mem_par                        1       output      Command and address parity
   mem_alert_n                    1       input       Alert flag
   mem_dqs                        9       bidir       Data strobe
   mem_dqs_n                      9       bidir       Data strobe (negative leg)
   mem_dq                         72      bidir       Read/write data
   mem_dbi_n                      9       bidir       Acts as either the data bus inversion pin, or the data mask pin, depending on configuration. 


-----------------------------------------
;  15. PHY calibration status interface ;
-----------------------------------------

   Port                           Width   Direction   Description                                        
   ------------------------------------------------------------------------------------------------------
   local_cal_success              1       output      When high, indicates that PHY calibration was successful
   local_cal_fail                 1       output      When high, indicates that PHY calibration failed


------------------------------------------
;  16. User clock domain reset interface ;
------------------------------------------

   Port                           Width   Direction   Description                                        
   ------------------------------------------------------------------------------------------------------
   emif_usr_reset_n               1       output      Reset for the user clock domain. Asynchronous assertion and synchronous deassertion


-----------------------------
;  17. User clock interface ;
-----------------------------

   Port                           Width   Direction   Description                                        
   ------------------------------------------------------------------------------------------------------
   emif_usr_clk                   1       output      User clock domain


--------------------------------------------------------
;  18. Controller Avalon Streaming command interface 0 ;
--------------------------------------------------------

   Port                           Width   Direction   Description                                        
   ------------------------------------------------------------------------------------------------------
   ast_cmd_valid_0                1       input       Indicates whether command is valid
   ast_cmd_ready_0                1       output      Comand request signal
   ast_cmd_data_0                 61      input       Command data


-----------------------------------------------------------
;  19. Controller Avalon Streaming write data interface 0 ;
-----------------------------------------------------------

   Port                           Width   Direction   Description                                        
   ------------------------------------------------------------------------------------------------------
   ast_wr_valid_0                 1       input       Indicates whether write data is valid
   ast_wr_ready_0                 1       output      Write request signal
   ast_wr_data_0                  648     input       Write data


----------------------------------------------------------
;  20. Controller Avalon Streaming read data interface 0 ;
----------------------------------------------------------

   Port                           Width   Direction   Description                                        
   ------------------------------------------------------------------------------------------------------
   ast_rd_valid_0                 1       output      Read request signal
   ast_rd_ready_0                 1       input       Indicates whether read data is valid
   ast_rd_data_0                  576     output      Read data


-----------------------------------
;  21. Controller ECC interface 0 ;
-----------------------------------

   Port                           Width   Direction   Description                                        
   ------------------------------------------------------------------------------------------------------
   ctrl_ecc_write_info_0          15      input       ctrl_ecc_write_info_0
   ctrl_ecc_rdata_id_0            13      output      ctrl_ecc_rdata_id_0
   ctrl_ecc_read_info_0           3       output      ctrl_ecc_read_info_0
   ctrl_ecc_cmd_info_0            3       output      ctrl_ecc_cmd_info_0
   ctrl_ecc_idle_0                1       output      ctrl_ecc_idle_0
   ctrl_ecc_wr_pointer_info_0     12      output      ctrl_ecc_wr_pointer_info_0


---------------------------------------------
;  22. EMIF calibration component interface ;
---------------------------------------------

   Port                           Width   Direction   Description                                        
   ------------------------------------------------------------------------------------------------------
   calbus_read                    1       output      EMIF Calibration component bus for read
   calbus_write                   1       output      EMIF Calibration component bus for write
   calbus_address                 20      output      EMIF Calibration component bus for address
   calbus_wdata                   32      output      EMIF Calibration component bus for write data
   calbus_rdata                   32      input       EMIF Calibration component bus for read data
   calbus_seq_param_tbl           4096    input       EMIF Calibration component bus for parameter table data


---------------------------------------------------------
;  23. EMIF calibration component clock input interface ;
---------------------------------------------------------

   Port                           Width   Direction   Description                                        
   ------------------------------------------------------------------------------------------------------
   calbus_clk                     1       output      EMIF Calibration component bus for the clock


-------------------------------------------------
;  24. Instantiating IP in a simulation project ;
-------------------------------------------------

   The simulation fileset as well as the simulation example design contain scripts
   that illustrate what files are required when including the EMIF IP for simulation.
   The scripts are customized for all the 3rd-party simulators supported. It is highly
   recommended that you use these scripts as reference when setting up your simulation
   environment.


------------------------------------------------------------
;  25. Full-calibration versus skip-calibration simulation ;
------------------------------------------------------------

   During generation, you can specify the default RTL simulation behavior for PHY calibration.
   If you specify full-calibration simulation, the simulation time can take a very long time
   because all the stages and the detailed behavior of PHY calibration are simulated. If you
   specify skip-calibration simulation, the detailed behavior of PHY calibration is not
   simulated. Skip-calibration simulation is recommended unless you suspect a functional
   issue with the PHY calibration algorithm. Note however, that RTL simulation is a zero-delay
   simulation, and so timing-related calibration failures on hardware do not manifest themselves
   during RTL simulations.
   
   The setting that controls the calibration mode is encoded within the *_seq_params_sim.hex file
   and the *_seq_params_synth.hex file. When the IP is compiled under the Quartus Prime software,
   synthesis-directive causes the *_seq_params_synth.hex file to always be used. Outside of the
   Quartus Prime software (e.g. 3rd-party simulator), the *_seq_params_sim.hex file is always used.
   The behavior is the same regardless of which fileset is being synthesized or simulated.
   The calibration mode setting specified during generation only affects the *_seq_params_sim.hex
   file. The *_seq_params_synth.hex file always specifies full-calibration since full calibration
   is key to functional hardware.
   The RTL simulation behavior of the current IP is "Skip Calibration"


--------------------
;  26. IP Settings ;
--------------------

   SYS_INFO_DEVICE_FAMILY                            : Agilex 7
   SYS_INFO_DEVICE                                   : AGFB014R24B2E2V
   SYS_INFO_DEVICE_SPEEDGRADE                        : 2
   SYS_INFO_DEVICE_TEMPERATURE_GRADE                 : EXTENDED
   SYS_INFO_DEVICE_POWER_MODEL                       : STANDARD_POWER
   SYS_INFO_DEVICE_DIE_REVISIONS                     : HSSI_WHR_REVA HSSI_CRETE3_REVA MAIN_FM6_REVB
   FAMILY_ENUM                                       : FAMILY_AGILEX
   TRAIT_SUPPORTS_VID                                : 1
   TRAIT_IOBANK_REVISION                             : IO96A_REVB2
   PROTOCOL_ENUM                                     : PROTOCOL_DDR4
   IS_ED_SLAVE                                       : false
   INTERNAL_TESTING_MODE                             : false
   CAL_DEBUG_CLOCK_FREQUENCY                         : 50000000
   SYS_INFO_UNIQUE_ID                                : ed_synth_emif_fm_0_emif_fm_0
   PREV_PROTOCOL_ENUM                                : PROTOCOL_DDR4
   PHY_FPGA_SPEEDGRADE_GUI                           : E2V (ES3) - change device under 'View'->'Device Family'
   PHY_TARGET_SPEEDGRADE                             : E2V
   PHY_TARGET_IS_ES                                  : false
   PHY_TARGET_IS_ES2                                 : false
   PHY_TARGET_IS_ES3                                 : true
   PHY_TARGET_IS_PRODUCTION                          : false
   PHY_CONFIG_ENUM                                   : CONFIG_PHY_AND_HARD_CTRL
   PHY_PING_PONG_EN                                  : false
   PHY_CLAMSHELL_EN                                  : false
   PHY_RATE_ENUM                                     : RATE_QUARTER
   PHY_MEM_CLK_FREQ_MHZ                              : 1200.0
   PHY_REF_CLK_FREQ_MHZ                              : 33.333
   PHY_REF_CLK_JITTER_PS                             : 10.0
   PHY_DLL_CORE_UPDN_EN                              : false
   PHY_CORE_CLKS_SHARING_ENUM                        : CORE_CLKS_SHARING_DISABLED
   PHY_CORE_CLKS_SHARING_EXPOSE_SLAVE_OUT            : false
   PHY_CALIBRATED_OCT                                : true
   PHY_AC_CALIBRATED_OCT                             : true
   PHY_CK_CALIBRATED_OCT                             : true
   PHY_DATA_CALIBRATED_OCT                           : true
   PHY_RZQ                                           : 240
   PHY_HPS_ENABLE_EARLY_RELEASE                      : false
   PHY_USER_PERIODIC_OCT_RECAL_ENUM                  : PERIODIC_OCT_RECAL_AUTO
   PHY_AC_IO_STD_ENUM                                : IO_STD_SSTL_12
   PHY_CK_IO_STD_ENUM                                : IO_STD_SSTL_12
   PHY_DATA_IO_STD_ENUM                              : IO_STD_POD_12
   PHY_AC_MODE_ENUM                                  : OUT_OCT_40_CAL
   PHY_CK_MODE_ENUM                                  : OUT_OCT_40_CAL
   PHY_AC_DEEMPHASIS_ENUM                            : DEEMPHASIS_MODE_OFF
   PHY_CK_DEEMPHASIS_ENUM                            : DEEMPHASIS_MODE_OFF
   PHY_DATA_OUT_DEEMPHASIS_ENUM                      : DEEMPHASIS_MODE_HIGH
   PHY_DATA_OUT_SLEW_RATE_ENUM                       : 
   PHY_DATA_OUT_MODE_ENUM                            : OUT_OCT_40_CAL
   PHY_MIMIC_HPS_EMIF                                : false
   PLL_ADD_EXTRA_CLKS                                : false
   PLL_USER_NUM_OF_EXTRA_CLKS                        : 0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_GUI_0               : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_GUI_0               : 0.0
   PLL_EXTRA_CLK_DESIRED_FREQ_MHZ_GUI_0              : 0.0
   PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_0              : ps
   PLL_EXTRA_CLK_DESIRED_PHASE_GUI_0                 : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_DEG_GUI_0              : 0.0
   PLL_EXTRA_CLK_DESIRED_DUTY_CYCLE_GUI_0            : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_GUI_0             : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_0                 : 50.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_GUI_1               : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_GUI_1               : 0.0
   PLL_EXTRA_CLK_DESIRED_FREQ_MHZ_GUI_1              : 0.0
   PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_1              : ps
   PLL_EXTRA_CLK_DESIRED_PHASE_GUI_1                 : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_DEG_GUI_1              : 0.0
   PLL_EXTRA_CLK_DESIRED_DUTY_CYCLE_GUI_1            : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_GUI_1             : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_1                 : 50.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_GUI_2               : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_GUI_2               : 0.0
   PLL_EXTRA_CLK_DESIRED_FREQ_MHZ_GUI_2              : 0.0
   PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_2              : ps
   PLL_EXTRA_CLK_DESIRED_PHASE_GUI_2                 : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_DEG_GUI_2              : 0.0
   PLL_EXTRA_CLK_DESIRED_DUTY_CYCLE_GUI_2            : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_GUI_2             : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_2                 : 50.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_GUI_3               : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_GUI_3               : 0.0
   PLL_EXTRA_CLK_DESIRED_FREQ_MHZ_GUI_3              : 0.0
   PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_3              : ps
   PLL_EXTRA_CLK_DESIRED_PHASE_GUI_3                 : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_DEG_GUI_3              : 0.0
   PLL_EXTRA_CLK_DESIRED_DUTY_CYCLE_GUI_3            : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_GUI_3             : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_3                 : 50.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_GUI_4               : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_GUI_4               : 0.0
   PLL_EXTRA_CLK_DESIRED_FREQ_MHZ_GUI_4              : 0.0
   PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_4              : ps
   PLL_EXTRA_CLK_DESIRED_PHASE_GUI_4                 : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_DEG_GUI_4              : 0.0
   PLL_EXTRA_CLK_DESIRED_DUTY_CYCLE_GUI_4            : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_GUI_4             : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_4                 : 50.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_GUI_5               : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_GUI_5               : 0.0
   PLL_EXTRA_CLK_DESIRED_FREQ_MHZ_GUI_5              : 0.0
   PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_5              : ps
   PLL_EXTRA_CLK_DESIRED_PHASE_GUI_5                 : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_DEG_GUI_5              : 0.0
   PLL_EXTRA_CLK_DESIRED_DUTY_CYCLE_GUI_5            : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_GUI_5             : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_5                 : 50.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_GUI_6               : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_GUI_6               : 0.0
   PLL_EXTRA_CLK_DESIRED_FREQ_MHZ_GUI_6              : 0.0
   PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_6              : ps
   PLL_EXTRA_CLK_DESIRED_PHASE_GUI_6                 : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_DEG_GUI_6              : 0.0
   PLL_EXTRA_CLK_DESIRED_DUTY_CYCLE_GUI_6            : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_GUI_6             : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_6                 : 50.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_GUI_7               : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_GUI_7               : 0.0
   PLL_EXTRA_CLK_DESIRED_FREQ_MHZ_GUI_7              : 0.0
   PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_7              : ps
   PLL_EXTRA_CLK_DESIRED_PHASE_GUI_7                 : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_DEG_GUI_7              : 0.0
   PLL_EXTRA_CLK_DESIRED_DUTY_CYCLE_GUI_7            : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_GUI_7             : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_7                 : 50.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_GUI_8               : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_GUI_8               : 0.0
   PLL_EXTRA_CLK_DESIRED_FREQ_MHZ_GUI_8              : 0.0
   PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_8              : ps
   PLL_EXTRA_CLK_DESIRED_PHASE_GUI_8                 : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_DEG_GUI_8              : 0.0
   PLL_EXTRA_CLK_DESIRED_DUTY_CYCLE_GUI_8            : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_GUI_8             : 50.0
   PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_8                 : 50.0
   PLL_VCO_CLK_FREQ_MHZ                              : 1200.0
   PLL_NUM_OF_EXTRA_CLKS                             : 0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_0                   : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_0                   : 0.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_1                   : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_1                   : 0.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_2                   : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_2                   : 0.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_3                   : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_3                   : 0.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_4                   : 0.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_4                   : 0.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_5                   : 1200.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_5                   : 0.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_6                   : 1200.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_6                   : 0.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_7                   : 1200.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_7                   : 0.0
   PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_8                   : 1200.0
   PLL_EXTRA_CLK_ACTUAL_PHASE_PS_8                   : 0.0
   PHY_DDR4_CONFIG_ENUM                              : CONFIG_PHY_AND_HARD_CTRL
   PHY_DDR4_USER_PING_PONG_EN                        : false
   PHY_DDR4_USER_CLAMSHELL_EN                        : false
   PHY_DDR4_USER_DLL_CORE_UPDN_EN                    : true
   PHY_DDR4_MEM_CLK_FREQ_MHZ                         : 1200.0
   PHY_DDR4_DEFAULT_REF_CLK_FREQ                     : false
   PHY_DDR4_USER_REF_CLK_FREQ_MHZ                    : 33.333
   PHY_DDR4_REF_CLK_JITTER_PS                        : 10.0
   PHY_DDR4_RATE_ENUM                                : RATE_QUARTER
   PHY_DDR4_CORE_CLKS_SHARING_ENUM                   : CORE_CLKS_SHARING_DISABLED
   PHY_DDR4_CORE_CLKS_SHARING_EXPOSE_SLAVE_OUT       : false
   PHY_DDR4_IO_VOLTAGE                               : 1.2
   PHY_DDR4_DEFAULT_IO                               : false
   PHY_DDR4_HPS_ENABLE_EARLY_RELEASE                 : false
   PHY_DDR4_USER_PERIODIC_OCT_RECAL_ENUM             : PERIODIC_OCT_RECAL_AUTO
   PHY_DDR4_MIMIC_HPS_EMIF                           : false
   PHY_DDR4_ALLOW_72_DQ_WIDTH                        : false
   PHY_DDR4_REF_CLK_FREQ_MHZ                         : 33.333
   PHY_DDR4_PING_PONG_EN                             : false
   PHY_DDR4_CLAMSHELL_EN                             : false
   PHY_DDR4_USER_AC_IO_STD_ENUM                      : IO_STD_SSTL_12
   PHY_DDR4_USER_AC_MODE_ENUM                        : OUT_OCT_40_CAL
   PHY_DDR4_USER_AC_SLEW_RATE_ENUM                   : unset
   PHY_DDR4_USER_AC_DEEMPHASIS_ENUM                  : unset
   PHY_DDR4_USER_CK_IO_STD_ENUM                      : IO_STD_SSTL_12
   PHY_DDR4_USER_CK_MODE_ENUM                        : OUT_OCT_40_CAL
   PHY_DDR4_USER_CK_SLEW_RATE_ENUM                   : unset
   PHY_DDR4_USER_CK_DEEMPHASIS_ENUM                  : unset
   PHY_DDR4_USER_DATA_IO_STD_ENUM                    : IO_STD_POD_12
   PHY_DDR4_USER_DATA_OUT_MODE_ENUM                  : OUT_OCT_40_CAL
   PHY_DDR4_USER_DATA_OUT_SLEW_RATE_ENUM             : unset
   PHY_DDR4_USER_DATA_OUT_DEEMPHASIS_ENUM            : unset
   PHY_DDR4_USER_DATA_IN_MODE_ENUM                   : IN_OCT_60_CAL
   PHY_DDR4_USER_AUTO_STARTING_VREFIN_EN             : true
   PHY_DDR4_USER_STARTING_VREFIN                     : 70.0
   PHY_DDR4_USER_PLL_REF_CLK_IO_STD_ENUM             : IO_STD_TRUE_DIFF_SIGNALING
   PHY_DDR4_USER_RZQ_IO_STD_ENUM                     : IO_STD_CMOS_12
   PHY_DDR4_AC_IO_STD_ENUM                           : IO_STD_SSTL_12
   PHY_DDR4_AC_MODE_ENUM                             : OUT_OCT_40_CAL
   PHY_DDR4_AC_SLEW_RATE_ENUM                        : SLEW_RATE_FM_FAST
   PHY_DDR4_AC_DEEMPHASIS_ENUM                       : DEEMPHASIS_MODE_OFF
   PHY_DDR4_CK_IO_STD_ENUM                           : IO_STD_SSTL_12
   PHY_DDR4_CK_MODE_ENUM                             : OUT_OCT_40_CAL
   PHY_DDR4_CK_SLEW_RATE_ENUM                        : SLEW_RATE_FM_FAST
   PHY_DDR4_CK_DEEMPHASIS_ENUM                       : DEEMPHASIS_MODE_OFF
   PHY_DDR4_DATA_IO_STD_ENUM                         : IO_STD_POD_12
   PHY_DDR4_DATA_OUT_MODE_ENUM                       : OUT_OCT_40_CAL
   PHY_DDR4_DATA_OUT_SLEW_RATE_ENUM                  : SLEW_RATE_FM_FAST
   PHY_DDR4_DATA_OUT_DEEMPHASIS_ENUM                 : DEEMPHASIS_MODE_HIGH
   PHY_DDR4_DATA_IN_MODE_ENUM                        : IN_OCT_60_CAL
   PHY_DDR4_AUTO_STARTING_VREFIN_EN                  : true
   PHY_DDR4_STARTING_VREFIN                          : 68.0
   PHY_DDR4_PLL_REF_CLK_IO_STD_ENUM                  : IO_STD_TRUE_DIFF_SIGNALING
   PHY_DDR4_RZQ_IO_STD_ENUM                          : IO_STD_CMOS_12
   MEM_FORMAT_ENUM                                   : MEM_FORMAT_RDIMM
   MEM_READ_LATENCY                                  : 23.0
   MEM_WRITE_LATENCY                                 : 18
   MEM_BURST_LENGTH                                  : 8
   MEM_DATA_MASK_EN                                  : true
   MEM_HAS_SIM_SUPPORT                               : true
   MEM_HAS_BSI_SUPPORT                               : true
   MEM_NUM_OF_PHYSICAL_RANKS                         : 1
   MEM_NUM_OF_LOGICAL_RANKS                          : 1
   MEM_NUM_OF_DATA_ENDPOINTS                         : 1
   MEM_TTL_DATA_WIDTH                                : 72
   MEM_TTL_NUM_OF_READ_GROUPS                        : 9
   MEM_TTL_NUM_OF_WRITE_GROUPS                       : 9
   MEM_DDR4_FORMAT_ENUM                              : MEM_FORMAT_RDIMM
   MEM_DDR4_DQ_WIDTH                                 : 72
   MEM_DDR4_DQ_PER_DQS                               : 8
   MEM_DDR4_DISCRETE_CS_WIDTH                        : 1
   MEM_DDR4_NUM_OF_DIMMS                             : 1
   MEM_DDR4_CHIP_ID_WIDTH                            : 0
   MEM_DDR4_RANKS_PER_DIMM                           : 1
   MEM_DDR4_CKE_PER_DIMM                             : 1
   MEM_DDR4_CK_WIDTH                                 : 1
   MEM_DDR4_ROW_ADDR_WIDTH                           : 16
   MEM_DDR4_COL_ADDR_WIDTH                           : 10
   MEM_DDR4_BANK_ADDR_WIDTH                          : 2
   MEM_DDR4_BANK_GROUP_WIDTH                         : 2
   MEM_DDR4_DM_EN                                    : true
   MEM_DDR4_ALERT_PAR_EN                             : true
   MEM_DDR4_ALERT_N_PLACEMENT_ENUM                   : DDR4_ALERT_N_PLACEMENT_FM_LANE3
   MEM_DDR4_ALERT_N_DQS_GROUP                        : 0
   MEM_DDR4_ALERT_N_AC_LANE                          : 3
   MEM_DDR4_ALERT_N_AC_PIN                           : 8
   MEM_DDR4_DISCRETE_MIRROR_ADDRESSING_EN            : false
   MEM_DDR4_MIRROR_ADDRESSING_EN                     : true
   MEM_DDR4_HIDE_ADV_MR_SETTINGS                     : true
   MEM_DDR4_INTEL_DEFAULT_TERM                       : true
   MEM_DDR4_BL_ENUM                                  : DDR4_BL_BL8
   MEM_DDR4_BT_ENUM                                  : DDR4_BT_SEQUENTIAL
   MEM_DDR4_TCL                                      : 21
   MEM_DDR4_RTT_NOM_ENUM                             : DDR4_RTT_NOM_RZQ_4
   MEM_DDR4_DLL_EN                                   : true
   MEM_DDR4_ATCL_ENUM                                : DDR4_ATCL_DISABLED
   MEM_DDR4_DRV_STR_ENUM                             : DDR4_DRV_STR_RZQ_7
   MEM_DDR4_ASR_ENUM                                 : DDR4_ASR_MANUAL_NORMAL
   MEM_DDR4_RTT_WR_ENUM                              : DDR4_RTT_WR_ODT_DISABLED
   MEM_DDR4_WTCL                                     : 16
   MEM_DDR4_WRITE_CRC                                : false
   MEM_DDR4_GEARDOWN                                 : DDR4_GEARDOWN_HR
   MEM_DDR4_PER_DRAM_ADDR                            : false
   MEM_DDR4_TEMP_SENSOR_READOUT                      : false
   MEM_DDR4_FINE_GRANULARITY_REFRESH                 : DDR4_FINE_REFRESH_FIXED_1X
   MEM_DDR4_MPR_READ_FORMAT                          : DDR4_MPR_READ_FORMAT_SERIAL
   MEM_DDR4_MAX_POWERDOWN                            : false
   MEM_DDR4_TEMP_CONTROLLED_RFSH_RANGE               : DDR4_TEMP_CONTROLLED_RFSH_NORMAL
   MEM_DDR4_TEMP_CONTROLLED_RFSH_ENA                 : false
   MEM_DDR4_INTERNAL_VREFDQ_MONITOR                  : false
   MEM_DDR4_CAL_MODE                                 : 0
   MEM_DDR4_SELF_RFSH_ABORT                          : false
   MEM_DDR4_READ_PREAMBLE_TRAINING                   : false
   MEM_DDR4_READ_PREAMBLE                            : 2
   MEM_DDR4_WRITE_PREAMBLE                           : 1
   MEM_DDR4_AC_PARITY_LATENCY                        : DDR4_AC_PARITY_LATENCY_DISABLE
   MEM_DDR4_ODT_IN_POWERDOWN                         : true
   MEM_DDR4_RTT_PARK                                 : DDR4_RTT_PARK_ODT_DISABLED
   MEM_DDR4_AC_PERSISTENT_ERROR                      : false
   MEM_DDR4_WRITE_DBI                                : false
   MEM_DDR4_READ_DBI                                 : true
   MEM_DDR4_DEFAULT_VREFOUT                          : true
   MEM_DDR4_USER_VREFDQ_TRAINING_VALUE               : 56.0
   MEM_DDR4_USER_VREFDQ_TRAINING_RANGE               : DDR4_VREFDQ_TRAINING_RANGE_1
   MEM_DDR4_RCD_CA_IBT_ENUM                          : DDR4_RCD_CA_IBT_100
   MEM_DDR4_RCD_CS_IBT_ENUM                          : DDR4_RCD_CS_IBT_100
   MEM_DDR4_RCD_CKE_IBT_ENUM                         : DDR4_RCD_CKE_IBT_100
   MEM_DDR4_RCD_ODT_IBT_ENUM                         : DDR4_RCD_ODT_IBT_100
   MEM_DDR4_DB_RTT_NOM_ENUM                          : DDR4_DB_RTT_NOM_ODT_DISABLED
   MEM_DDR4_DB_RTT_WR_ENUM                           : DDR4_DB_RTT_WR_RZQ_3
   MEM_DDR4_DB_RTT_PARK_ENUM                         : DDR4_DB_RTT_PARK_ODT_DISABLED
   MEM_DDR4_DB_DQ_DRV_ENUM                           : DDR4_DB_DRV_STR_RZQ_7
   MEM_DDR4_SPD_137_RCD_CA_DRV                       : 101
   MEM_DDR4_SPD_138_RCD_CK_DRV                       : 5
   MEM_DDR4_SPD_140_DRAM_VREFDQ_R0                   : 29
   MEM_DDR4_SPD_141_DRAM_VREFDQ_R1                   : 29
   MEM_DDR4_SPD_142_DRAM_VREFDQ_R2                   : 29
   MEM_DDR4_SPD_143_DRAM_VREFDQ_R3                   : 29
   MEM_DDR4_SPD_144_DB_VREFDQ                        : 37
   MEM_DDR4_SPD_145_DB_MDQ_DRV                       : 21
   MEM_DDR4_SPD_148_DRAM_DRV                         : 0
   MEM_DDR4_SPD_149_DRAM_RTT_WR_NOM                  : 20
   MEM_DDR4_SPD_152_DRAM_RTT_PARK                    : 39
   MEM_DDR4_SPD_155_DB_VREFDQ_RANGE                  : 0
   MEM_DDR4_SPD_133_RCD_DB_VENDOR_LSB                : 0
   MEM_DDR4_SPD_134_RCD_DB_VENDOR_MSB                : 0
   MEM_DDR4_SPD_135_RCD_REV                          : 0
   MEM_DDR4_SPD_139_DB_REV                           : 0
   MEM_DDR4_LRDIMM_ODT_LESS_BS                       : true
   MEM_DDR4_LRDIMM_ODT_LESS_BS_PARK_OHM              : 240
   MEM_DDR4_DQS_WIDTH                                : 9
   MEM_DDR4_CS_WIDTH                                 : 1
   MEM_DDR4_CS_PER_DIMM                              : 1
   MEM_DDR4_CKE_WIDTH                                : 1
   MEM_DDR4_ODT_WIDTH                                : 1
   MEM_DDR4_ADDR_WIDTH                               : 17
   MEM_DDR4_RM_WIDTH                                 : 0
   MEM_DDR4_NUM_OF_PHYSICAL_RANKS                    : 1
   MEM_DDR4_NUM_OF_LOGICAL_RANKS                     : 1
   MEM_DDR4_IDEAL_VREF_IN_PCT                        : 68.0
   MEM_DDR4_IDEAL_VREF_OUT_PCT                       : 70.0
   MEM_DDR4_VREFDQ_TRAINING_VALUE                    : 70.0
   MEM_DDR4_VREFDQ_TRAINING_RANGE                    : DDR4_VREFDQ_TRAINING_RANGE_0
   MEM_DDR4_VREFDQ_TRAINING_RANGE_DISP               : Range 1 - 60% to 92.5%
   MEM_DDR4_INTEL_DEFAULT_DRV_STR_ENUM               : DDR4_DRV_STR_RZQ_7
   MEM_DDR4_INTEL_DEFAULT_RTT_WR_ENUM                : DDR4_RTT_WR_ODT_DISABLED
   MEM_DDR4_INTEL_DEFAULT_RTT_NOM_ENUM               : DDR4_RTT_NOM_ODT_DISABLED
   MEM_DDR4_INTEL_DEFAULT_RTT_PARK_ENUM              : DDR4_RTT_PARK_RZQ_4
   MEM_DDR4_INTEL_DEFAULT_DRV_STR_ENUM_DISP          : RZQ/7 (34 Ohm)
   MEM_DDR4_INTEL_DEFAULT_RTT_WR_ENUM_DISP           : Dynamic ODT off
   MEM_DDR4_INTEL_DEFAULT_RTT_NOM_ENUM_DISP          : ODT Disabled
   MEM_DDR4_INTEL_DEFAULT_RTT_PARK_ENUM_DISP         : RZQ/4 (60 Ohm)
   MEM_DDR4_INTEL_DEFAULT_DB_RTT_NOM_ENUM            : DDR4_DB_RTT_NOM_ODT_DISABLED
   MEM_DDR4_INTEL_DEFAULT_DB_RTT_WR_ENUM             : DDR4_DB_RTT_WR_RZQ_3
   MEM_DDR4_INTEL_DEFAULT_DB_RTT_PARK_ENUM           : DDR4_DB_RTT_PARK_ODT_DISABLED
   MEM_DDR4_INTEL_DEFAULT_DB_DQ_DRV_ENUM             : DDR4_DB_DRV_STR_RZQ_7
   MEM_DDR4_INTEL_DEFAULT_DB_RTT_NOM_ENUM_DISP       : RTT_NOM disabled
   MEM_DDR4_INTEL_DEFAULT_DB_RTT_WR_ENUM_DISP        : RZQ/3 (80 Ohm)
   MEM_DDR4_INTEL_DEFAULT_DB_RTT_PARK_ENUM_DISP      : RTT_PARK disabled
   MEM_DDR4_INTEL_DEFAULT_DB_DQ_DRV_ENUM_DISP        : RZQ/7 (34 Ohm)
   MEM_DDR4_TTL_DQS_WIDTH                            : 9
   MEM_DDR4_TTL_DQ_WIDTH                             : 72
   MEM_DDR4_TTL_CS_WIDTH                             : 1
   MEM_DDR4_TTL_CK_WIDTH                             : 1
   MEM_DDR4_TTL_CKE_WIDTH                            : 1
   MEM_DDR4_TTL_ODT_WIDTH                            : 1
   MEM_DDR4_TTL_BANK_ADDR_WIDTH                      : 2
   MEM_DDR4_TTL_BANK_GROUP_WIDTH                     : 2
   MEM_DDR4_TTL_CHIP_ID_WIDTH                        : 0
   MEM_DDR4_TTL_ADDR_WIDTH                           : 17
   MEM_DDR4_TTL_RM_WIDTH                             : 0
   MEM_DDR4_TTL_NUM_OF_DIMMS                         : 1
   MEM_DDR4_TTL_NUM_OF_PHYSICAL_RANKS                : 1
   MEM_DDR4_TTL_NUM_OF_LOGICAL_RANKS                 : 1
   MEM_DDR4_MR0                                      : 0x874
   MEM_DDR4_MR1                                      : 0x10001
   MEM_DDR4_MR2                                      : 0x20028
   MEM_DDR4_MR3                                      : 0x30400
   MEM_DDR4_MR4                                      : 0x40800
   MEM_DDR4_MR5                                      : 0x51460
   MEM_DDR4_MR6                                      : 0x6080f
   MEM_DDR4_RDIMM_CONFIG                             : 00000020000000003900000D40030B0F556000
   MEM_DDR4_LRDIMM_EXTENDED_CONFIG                   : 
   MEM_DDR4_ADDRESS_MIRROR_BITVEC                    : 0
   MEM_DDR4_RCD_PARITY_CONTROL_WORD                  : 13
   MEM_DDR4_RCD_COMMAND_LATENCY                      : 1
   MEM_DDR4_USE_DEFAULT_ODT                          : true
   MEM_DDR4_R_ODTN_1X1                               : {Rank 0}
   MEM_DDR4_R_ODT0_1X1                               : off
   MEM_DDR4_W_ODTN_1X1                               : {Rank 0}
   MEM_DDR4_W_ODT0_1X1                               : on
   MEM_DDR4_R_ODTN_2X2                               : {Rank 0} {Rank 1}
   MEM_DDR4_R_ODT0_2X2                               : off off
   MEM_DDR4_R_ODT1_2X2                               : off off
   MEM_DDR4_W_ODTN_2X2                               : {Rank 0} {Rank 1}
   MEM_DDR4_W_ODT0_2X2                               : on off
   MEM_DDR4_W_ODT1_2X2                               : off on
   MEM_DDR4_R_ODTN_4X2                               : {Rank 0} {Rank 1} {Rank 2} {Rank 3}
   MEM_DDR4_R_ODT0_4X2                               : off off on on
   MEM_DDR4_R_ODT1_4X2                               : on on off off
   MEM_DDR4_W_ODTN_4X2                               : {Rank 0} {Rank 1} {Rank 2} {Rank 3}
   MEM_DDR4_W_ODT0_4X2                               : off off on on
   MEM_DDR4_W_ODT1_4X2                               : on on off off
   MEM_DDR4_R_ODTN_4X4                               : {Rank 0} {Rank 1} {Rank 2} {Rank 3}
   MEM_DDR4_R_ODT0_4X4                               : off off on off
   MEM_DDR4_R_ODT1_4X4                               : off off off on
   MEM_DDR4_R_ODT2_4X4                               : on off off off
   MEM_DDR4_R_ODT3_4X4                               : off on off off
   MEM_DDR4_W_ODTN_4X4                               : {Rank 0} {Rank 1} {Rank 2} {Rank 3}
   MEM_DDR4_W_ODT0_4X4                               : on off on off
   MEM_DDR4_W_ODT1_4X4                               : off on off on
   MEM_DDR4_W_ODT2_4X4                               : on off on off
   MEM_DDR4_W_ODT3_4X4                               : off on off on
   MEM_DDR4_R_DERIVED_ODTN                           : {Rank 0} - - -
   MEM_DDR4_R_DERIVED_ODT0                           : {(Drive) RZQ/7 (34 Ohm)} - - -
   MEM_DDR4_R_DERIVED_ODT1                           : - - - -
   MEM_DDR4_R_DERIVED_ODT2                           : - - - -
   MEM_DDR4_R_DERIVED_ODT3                           : - - - -
   MEM_DDR4_R_DERIVED_BODTN                          : 
   MEM_DDR4_R_DERIVED_BODT0                          : 
   MEM_DDR4_R_DERIVED_BODT1                          : 
   MEM_DDR4_W_DERIVED_ODTN                           : {Rank 0} - - -
   MEM_DDR4_W_DERIVED_ODT0                           : {(Park) RZQ/4 (60 Ohm)} - - -
   MEM_DDR4_W_DERIVED_ODT1                           : - - - -
   MEM_DDR4_W_DERIVED_ODT2                           : - - - -
   MEM_DDR4_W_DERIVED_ODT3                           : - - - -
   MEM_DDR4_W_DERIVED_BODTN                          : 
   MEM_DDR4_W_DERIVED_BODT0                          : 
   MEM_DDR4_W_DERIVED_BODT1                          : 
   MEM_DDR4_SEQ_ODT_TABLE_LO                         : 0
   MEM_DDR4_SEQ_ODT_TABLE_HI                         : 0
   MEM_DDR4_CTRL_CFG_READ_ODT_CHIP                   : 0
   MEM_DDR4_CTRL_CFG_WRITE_ODT_CHIP                  : 0
   MEM_DDR4_CTRL_CFG_READ_ODT_RANK                   : 0
   MEM_DDR4_CTRL_CFG_WRITE_ODT_RANK                  : 0
   MEM_DDR4_SPEEDBIN_ENUM                            : DDR4_SPEEDBIN_2666
   MEM_DDR4_TIS_PS                                   : 62
   MEM_DDR4_TIS_AC_MV                                : 100
   MEM_DDR4_TIH_PS                                   : 87
   MEM_DDR4_TIH_DC_MV                                : 75
   MEM_DDR4_TDIVW_TOTAL_UI                           : 0.2
   MEM_DDR4_VDIVW_TOTAL                              : 130
   MEM_DDR4_TDQSQ_UI                                 : 0.14
   MEM_DDR4_TQH_UI                                   : 0.74
   MEM_DDR4_TDVWP_UI                                 : 0.72
   MEM_DDR4_TDQSCK_PS                                : 175
   MEM_DDR4_TDQSS_CYC                                : 0.27
   MEM_DDR4_TQSH_CYC                                 : 0.4
   MEM_DDR4_TDSH_CYC                                 : 0.18
   MEM_DDR4_TDSS_CYC                                 : 0.18
   MEM_DDR4_TWLS_CYC                                 : 0.13
   MEM_DDR4_TWLH_CYC                                 : 0.13
   MEM_DDR4_TINIT_US                                 : 500
   MEM_DDR4_TMRD_CK_CYC                              : 8
   MEM_DDR4_TRAS_NS                                  : 32.0
   MEM_DDR4_TRCD_NS                                  : 14.16
   MEM_DDR4_TRP_NS                                   : 14.16
   MEM_DDR4_TREFI_US                                 : 7.8
   MEM_DDR4_TRFC_NS                                  : 350.0
   MEM_DDR4_TWR_NS                                   : 15.0
   MEM_DDR4_TWTR_L_CYC                               : 9
   MEM_DDR4_TWTR_S_CYC                               : 3
   MEM_DDR4_TFAW_NS                                  : 21.0
   MEM_DDR4_TRRD_L_CYC                               : 6
   MEM_DDR4_TRRD_S_CYC                               : 4
   MEM_DDR4_TCCD_L_CYC                               : 6
   MEM_DDR4_TCCD_S_CYC                               : 4
   MEM_DDR4_TRFC_DLR_NS                              : 90.0
   MEM_DDR4_TFAW_DLR_CYC                             : 16
   MEM_DDR4_TRRD_DLR_CYC                             : 4
   MEM_DDR4_TDIVW_DJ_CYC                             : 0.1
   MEM_DDR4_TDQSQ_PS                                 : 66
   MEM_DDR4_TQH_CYC                                  : 0.38
   MEM_DDR4_TINIT_CK                                 : 600000
   MEM_DDR4_TDQSCK_DERV_PS                           : 2
   MEM_DDR4_TDQSCKDS                                 : 450
   MEM_DDR4_TDQSCKDM                                 : 900
   MEM_DDR4_TDQSCKDL                                 : 1200
   MEM_DDR4_TRAS_CYC                                 : 39
   MEM_DDR4_TRCD_CYC                                 : 17
   MEM_DDR4_TRP_CYC                                  : 17
   MEM_DDR4_TRFC_CYC                                 : 420
   MEM_DDR4_TWR_CYC                                  : 18
   MEM_DDR4_TRTP_CYC                                 : 9
   MEM_DDR4_TFAW_CYC                                 : 26
   MEM_DDR4_TREFI_CYC                                : 9360
   MEM_DDR4_WRITE_CMD_LATENCY                        : 6
   MEM_DDR4_TRFC_DLR_CYC                             : 108
   MEM_DDR4_CFG_GEN_SBE                              : false
   MEM_DDR4_CFG_GEN_DBE                              : false
   MEM_DDR4_LRDIMM_VREFDQ_VALUE                      : 
   MEM_DDR4_TWLS_PS                                  : 0.0
   MEM_DDR4_TWLH_PS                                  : 0.0
   BOARD_DDR4_USE_DEFAULT_SLEW_RATES                 : true
   BOARD_DDR4_USE_DEFAULT_ISI_VALUES                 : true
   BOARD_DDR4_USER_CK_SLEW_RATE                      : 4.0
   BOARD_DDR4_USER_AC_SLEW_RATE                      : 2.0
   BOARD_DDR4_USER_RCLK_SLEW_RATE                    : 8.0
   BOARD_DDR4_USER_WCLK_SLEW_RATE                    : 4.0
   BOARD_DDR4_USER_RDATA_SLEW_RATE                   : 4.0
   BOARD_DDR4_USER_WDATA_SLEW_RATE                   : 2.0
   BOARD_DDR4_USER_AC_ISI_NS                         : 0.0
   BOARD_DDR4_USER_RCLK_ISI_NS                       : 0.0
   BOARD_DDR4_USER_WCLK_ISI_NS                       : 0.0
   BOARD_DDR4_USER_RDATA_ISI_NS                      : 0.0
   BOARD_DDR4_USER_WDATA_ISI_NS                      : 0.0
   BOARD_DDR4_IS_SKEW_WITHIN_DQS_DESKEWED            : true
   BOARD_DDR4_BRD_SKEW_WITHIN_DQS_NS                 : 0.02
   BOARD_DDR4_PKG_BRD_SKEW_WITHIN_DQS_NS             : 0.02
   BOARD_DDR4_IS_SKEW_WITHIN_AC_DESKEWED             : false
   BOARD_DDR4_BRD_SKEW_WITHIN_AC_NS                  : 0.02
   BOARD_DDR4_PKG_BRD_SKEW_WITHIN_AC_NS              : 0.02
   BOARD_DDR4_DQS_TO_CK_SKEW_NS                      : 0.02
   BOARD_DDR4_SKEW_BETWEEN_DIMMS_NS                  : 0.05
   BOARD_DDR4_SKEW_BETWEEN_DQS_NS                    : 0.02
   BOARD_DDR4_AC_TO_CK_SKEW_NS                       : 0.0
   BOARD_DDR4_MAX_CK_DELAY_NS                        : 0.6
   BOARD_DDR4_MAX_DQS_DELAY_NS                       : 0.6
   BOARD_DDR4_TIS_DERATING_PS                        : 0
   BOARD_DDR4_TIH_DERATING_PS                        : 0
   BOARD_DDR4_CK_SLEW_RATE                           : 4.0
   BOARD_DDR4_AC_SLEW_RATE                           : 2.0
   BOARD_DDR4_RCLK_SLEW_RATE                         : 8.0
   BOARD_DDR4_WCLK_SLEW_RATE                         : 4.0
   BOARD_DDR4_RDATA_SLEW_RATE                        : 4.0
   BOARD_DDR4_WDATA_SLEW_RATE                        : 2.0
   BOARD_DDR4_AC_ISI_NS                              : 0.15
   BOARD_DDR4_RCLK_ISI_NS                            : 0.15
   BOARD_DDR4_WCLK_ISI_NS                            : 0.06
   BOARD_DDR4_RDATA_ISI_NS                           : 0.12
   BOARD_DDR4_WDATA_ISI_NS                           : 0.13
   BOARD_DDR4_SKEW_WITHIN_DQS_NS                     : 0.02
   BOARD_DDR4_SKEW_WITHIN_AC_NS                      : 0.18
   CTRL_ECC_EN                                       : true
   CTRL_MMR_EN                                       : false
   CTRL_AUTO_PRECHARGE_EN                            : false
   CTRL_USER_PRIORITY_EN                             : false
   CTRL_REORDER_EN                                   : true
   CTRL_ECC_READDATAERROR_EN                         : false
   CTRL_ECC_STATUS_EN                                : false
   CTRL_DDR4_AVL_PROTOCOL_ENUM                       : CTRL_AVL_PROTOCOL_MM
   CTRL_DDR4_SELF_REFRESH_EN                         : false
   CTRL_DDR4_AUTO_POWER_DOWN_EN                      : false
   CTRL_DDR4_AUTO_POWER_DOWN_CYCS                    : 32
   CTRL_DDR4_USER_REFRESH_EN                         : false
   CTRL_DDR4_USER_PRIORITY_EN                        : false
   CTRL_DDR4_AUTO_PRECHARGE_EN                       : false
   CTRL_DDR4_ADDR_ORDER_ENUM                         : DDR4_CTRL_ADDR_ORDER_CS_R_B_C_BG
   CTRL_DDR4_ECC_EN                                  : true
   CTRL_DDR4_ECC_AUTO_CORRECTION_EN                  : false
   CTRL_DDR4_ECC_READDATAERROR_EN                    : false
   CTRL_DDR4_ECC_STATUS_EN                           : false
   CTRL_DDR4_REORDER_EN                              : true
   CTRL_DDR4_STARVE_LIMIT                            : 10
   CTRL_DDR4_MMR_EN                                  : false
   CTRL_DDR4_MAJOR_MODE_EN                           : false
   CTRL_DDR4_POST_REFRESH_EN                         : true
   CTRL_DDR4_POST_REFRESH_LOWER_LIMIT                : 0
   CTRL_DDR4_POST_REFRESH_UPPER_LIMIT                : 2
   CTRL_DDR4_PRE_REFRESH_EN                          : false
   CTRL_DDR4_PRE_REFRESH_UPPER_LIMIT                 : 1
   CTRL_DDR4_RD_TO_WR_SAME_CHIP_DELTA_CYCS           : 0
   CTRL_DDR4_WR_TO_RD_SAME_CHIP_DELTA_CYCS           : 0
   CTRL_DDR4_RD_TO_RD_DIFF_CHIP_DELTA_CYCS           : 0
   CTRL_DDR4_RD_TO_WR_DIFF_CHIP_DELTA_CYCS           : 0
   CTRL_DDR4_WR_TO_WR_DIFF_CHIP_DELTA_CYCS           : 0
   CTRL_DDR4_WR_TO_RD_DIFF_CHIP_DELTA_CYCS           : 0
   DIAG_SIM_REGTEST_MODE                             : false
   DIAG_TIMING_REGTEST_MODE                          : false
   DIAG_SYNTH_FOR_SIM                                : false
   DIAG_FAST_SIM_OVERRIDE                            : FAST_SIM_OVERRIDE_DEFAULT
   DIAG_SEQ_RESET_AUTO_RELEASE                       : avl
   DIAG_DB_RESET_AUTO_RELEASE                        : avl_release
   DIAG_ADD_READY_PIPELINE                           : true
   DIAG_EXPOSE_EARLY_READY                           : false
   DIAG_EXPOSE_RD_TYPE                               : false
   DIAG_VERBOSE_IOAUX                                : false
   DIAG_ECLIPSE_DEBUG                                : false
   DIAG_EXPORT_VJI                                   : false
   DIAG_ENABLE_JTAG_UART                             : false
   DIAG_ENABLE_JTAG_UART_HEX                         : false
   DIAG_ENABLE_HPS_EMIF_DEBUG                        : false
   DIAG_SOFT_NIOS_MODE                               : SOFT_NIOS_MODE_DISABLED
   DIAG_SOFT_NIOS_CLOCK_FREQUENCY                    : 100
   DIAG_USE_RS232_UART                               : false
   DIAG_RS232_UART_BAUDRATE                          : 57600
   DIAG_EX_DESIGN_ADD_TEST_EMIFS                     : 
   DIAG_EX_DESIGN_SEPARATE_RESETS                    : false
   DIAG_EXPOSE_DFT_SIGNALS                           : false
   DIAG_EXTRA_CONFIGS                                : 
   DIAG_USE_BOARD_DELAY_MODEL                        : false
   DIAG_BOARD_DELAY_CONFIG_STR                       : 
   DIAG_TG_AVL_2_NUM_CFG_INTERFACES                  : 0
   DIAG_EXPORT_PLL_REF_CLK_OUT                       : false
   DIAG_EXPORT_PLL_LOCKED                            : true
   DIAG_HMC_HRC                                      : auto
   SHORT_QSYS_INTERFACE_NAMES                        : true
   DIAG_EXT_DOCS                                     : false
   DIAG_SIM_CAL_MODE_ENUM                            : SIM_CAL_MODE_SKIP
   DIAG_EXPORT_SEQ_AVALON_SLAVE                      : CAL_DEBUG_EXPORT_MODE_JTAG
   DIAG_EXPORT_SEQ_AVALON_MASTER                     : false
   DIAG_EXPORT_SEQ_AVALON_HEAD_OF_CHAIN              : true
   DIAG_EX_DESIGN_NUM_OF_SLAVES                      : 1
   DIAG_EX_DESIGN_ISSP_EN                            : true
   DIAG_INTERFACE_ID                                 : 0
   DIAG_EFFICIENCY_MONITOR                           : EFFMON_MODE_DISABLED
   DIAG_USE_NEW_EFFMON_S10                           : false
   DIAG_USE_ABSTRACT_PHY                             : false
   DIAG_SIM_MEMORY_PRELOAD                           : false
   DIAG_SIM_MEMORY_PRELOAD_PRI_EMIF_FILE             : 
   DIAG_SIM_MEMORY_PRELOAD_PRI_ECC_FILE              : 
   DIAG_SIM_MEMORY_PRELOAD_PRI_MEM_FILE              : 
   DIAG_SIM_MEMORY_PRELOAD_PRI_ABPHY_FILE            : 
   DIAG_SIM_MEMORY_PRELOAD_SEC_EMIF_FILE             : 
   DIAG_SIM_MEMORY_PRELOAD_SEC_ECC_FILE              : 
   DIAG_SIM_MEMORY_PRELOAD_SEC_MEM_FILE              : 
   DIAG_SIM_MEMORY_PRELOAD_SEC_ABPHY_FILE            : 
   DIAG_USE_SIM_MEMORY_VALIDATION_TG                 : false
   DIAG_SIM_VERBOSE_LEVEL                            : 5
   DIAG_FAST_SIM                                     : true
   DIAG_USE_TG_AVL_2                                 : false
   DIAG_TG2_TEST_DURATION                            : SHORT
   DIAG_USE_TG_HBM                                   : false
   DIAG_EXPORT_TG_CFG_AVALON_SLAVE                   : TG_CFG_AMM_EXPORT_MODE_EXPORT
   DIAG_ENABLE_DEFAULT_MODE                          : false
   DIAG_ENABLE_USER_MODE                             : true
   DIAG_ENABLE_SOFT_M20K                             : false
   DIAG_SIM_CHECKER_SKIP_TG                          : false
   DIAG_AC_PARITY_ERR                                : false
   DIAG_DISABLE_AFI_P2C_REGISTERS                    : false
   DIAG_EX_DESIGN_SEPARATE_RZQS                      : true
   DIAG_DDR4_SIM_CAL_MODE_ENUM                       : SIM_CAL_MODE_SKIP
   DIAG_DDR4_EXPORT_SEQ_AVALON_SLAVE                 : CAL_DEBUG_EXPORT_MODE_JTAG
   DIAG_DDR4_EXPORT_SEQ_AVALON_MASTER                : false
   DIAG_DDR4_EXPORT_SEQ_AVALON_HEAD_OF_CHAIN         : true
   DIAG_DDR4_EX_DESIGN_NUM_OF_SLAVES                 : 1
   DIAG_DDR4_EX_DESIGN_ISSP_EN                       : true
   DIAG_DDR4_INTERFACE_ID                            : 0
   DIAG_DDR4_EFFICIENCY_MONITOR                      : EFFMON_MODE_DISABLED
   DIAG_DDR4_USE_NEW_EFFMON_S10                      : false
   DIAG_DDR4_USER_SIM_MEMORY_PRELOAD                 : false
   DIAG_DDR4_USER_SIM_MEMORY_PRELOAD_PRI_EMIF_FILE   : EMIF_PRI_PRELOAD.txt
   DIAG_DDR4_USER_SIM_MEMORY_PRELOAD_SEC_EMIF_FILE   : EMIF_SEC_PRELOAD.txt
   DIAG_DDR4_USER_USE_SIM_MEMORY_VALIDATION_TG       : true
   DIAG_DDR4_USE_TG_AVL_2                            : false
   DIAG_DDR4_USE_TG_HBM                              : false
   DIAG_DDR4_ABSTRACT_PHY                            : false
   DIAG_DDR4_ENABLE_DEFAULT_MODE                     : false
   DIAG_DDR4_ENABLE_USER_MODE                        : true
   DIAG_DDR4_EXPORT_TG_CFG_AVALON_SLAVE              : TG_CFG_AMM_EXPORT_MODE_EXPORT
   DIAG_DDR4_TG2_TEST_DURATION                       : SHORT
   DIAG_DDR4_SEPARATE_READ_WRITE_ITFS                : false
   DIAG_DDR4_DISABLE_AFI_P2C_REGISTERS               : false
   DIAG_DDR4_AC_PARITY_ERR                           : false
   DIAG_DDR4_SIM_MEMORY_PRELOAD                      : false
   DIAG_DDR4_SIM_MEMORY_PRELOAD_PRI_EMIF_FILE        : 
   DIAG_DDR4_SIM_MEMORY_PRELOAD_SEC_EMIF_FILE        : 
   DIAG_DDR4_USE_SIM_MEMORY_VALIDATION_TG            : false
   DIAG_DDR4_EX_DESIGN_SEPARATE_RZQS                 : true
   DIAG_DDR4_SIM_VERBOSE                             : true
   DIAG_DDR4_SKIP_CA_LEVEL                           : false
   DIAG_DDR4_SKIP_CA_DESKEW                          : false
   DIAG_DDR4_SKIP_VREF_CAL                           : false
   DIAG_DDR4_SKIP_AC_PARITY_CHECK                    : false
   DIAG_DDR4_CAL_ADDR0                               : 0
   DIAG_DDR4_CAL_ADDR1                               : 8
   DIAG_DDR4_CAL_ENABLE_NON_DES                      : false
   DIAG_DDR4_CAL_FULL_CAL_ON_RESET                   : true
   NUM_IPS                                           : 1
   EMIF_0_CONN_TO_CALIP                              : CALIP_0
   EMIF_0_STORED_PARAM                               : 
   EMIF_0_REF_CLK_SHARING                            : EXPORTED
   EMIF_1_CONN_TO_CALIP                              : CALIP_0
   EMIF_1_STORED_PARAM                               : 
   EMIF_1_REF_CLK_SHARING                            : EXPORTED
   EMIF_2_CONN_TO_CALIP                              : CALIP_0
   EMIF_2_STORED_PARAM                               : 
   EMIF_2_REF_CLK_SHARING                            : EXPORTED
   EMIF_3_CONN_TO_CALIP                              : CALIP_0
   EMIF_3_STORED_PARAM                               : 
   EMIF_3_REF_CLK_SHARING                            : EXPORTED
   EMIF_4_CONN_TO_CALIP                              : CALIP_0
   EMIF_4_STORED_PARAM                               : 
   EMIF_4_REF_CLK_SHARING                            : EXPORTED
   EMIF_5_CONN_TO_CALIP                              : CALIP_0
   EMIF_5_STORED_PARAM                               : 
   EMIF_5_REF_CLK_SHARING                            : EXPORTED
   EMIF_6_CONN_TO_CALIP                              : CALIP_0
   EMIF_6_STORED_PARAM                               : 
   EMIF_6_REF_CLK_SHARING                            : EXPORTED
   EMIF_7_CONN_TO_CALIP                              : CALIP_0
   EMIF_7_STORED_PARAM                               : 
   EMIF_7_REF_CLK_SHARING                            : EXPORTED
   EMIF_8_CONN_TO_CALIP                              : CALIP_0
   EMIF_8_STORED_PARAM                               : 
   EMIF_8_REF_CLK_SHARING                            : EXPORTED
   EMIF_9_CONN_TO_CALIP                              : CALIP_0
   EMIF_9_STORED_PARAM                               : 
   EMIF_9_REF_CLK_SHARING                            : EXPORTED
   EMIF_10_CONN_TO_CALIP                             : CALIP_0
   EMIF_10_STORED_PARAM                              : 
   EMIF_10_REF_CLK_SHARING                           : EXPORTED
   EMIF_11_CONN_TO_CALIP                             : CALIP_0
   EMIF_11_STORED_PARAM                              : 
   EMIF_11_REF_CLK_SHARING                           : EXPORTED
   EMIF_12_CONN_TO_CALIP                             : CALIP_0
   EMIF_12_STORED_PARAM                              : 
   EMIF_12_REF_CLK_SHARING                           : EXPORTED
   EMIF_13_CONN_TO_CALIP                             : CALIP_0
   EMIF_13_STORED_PARAM                              : 
   EMIF_13_REF_CLK_SHARING                           : EXPORTED
   EMIF_14_CONN_TO_CALIP                             : CALIP_0
   EMIF_14_STORED_PARAM                              : 
   EMIF_14_REF_CLK_SHARING                           : EXPORTED
   EMIF_15_CONN_TO_CALIP                             : CALIP_0
   EMIF_15_STORED_PARAM                              : 
   EMIF_15_REF_CLK_SHARING                           : EXPORTED
   EX_DESIGN_GUI_GEN_SIM                             : true
   EX_DESIGN_GUI_GEN_SYNTH                           : true
   EX_DESIGN_GUI_GEN_BSI                             : false
   EX_DESIGN_GUI_GEN_CDC                             : false
   EX_DESIGN_GUI_TARGET_DEV_KIT                      : TARGET_DEV_KIT_NONE
   NUM_IPS_SAVED                                     : 0
   EX_DESIGN_GUI_PREV_PRESET                         : TARGET_DEV_KIT_NONE
   EX_DESIGN_GUI_DDR4_SEL_DESIGN                     : AVAIL_EX_DESIGNS_GEN_DESIGN
   EX_DESIGN_GUI_DDR4_GEN_SIM                        : true
   EX_DESIGN_GUI_DDR4_GEN_SYNTH                      : true
   EX_DESIGN_GUI_DDR4_GEN_BSI                        : false
   EX_DESIGN_GUI_DDR4_GEN_CDC                        : false
   EX_DESIGN_GUI_DDR4_HDL_FORMAT                     : HDL_FORMAT_VERILOG
   EX_DESIGN_GUI_DDR4_TARGET_DEV_KIT                 : TARGET_DEV_KIT_NONE
   EX_DESIGN_GUI_DDR4_PREV_PRESET                    : TARGET_DEV_KIT_NONE


