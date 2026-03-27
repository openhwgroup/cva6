# Program configuration memory (flash) via JTAG
#
# Supports VC707 (BPI x16), Genesys 2 / KC705 / Nexys Video (SPI x4)

open_hw_manager
connect_hw_server -url localhost:3121

if {$::env(BOARD) eq "genesys2"} {
    set device_name xc7k325t_0
    set flash_type s25fl256sxxxxxx0-spi-x1_x2_x4
} elseif {$::env(BOARD) eq "vc707"} {
    set device_name xc7vx485t_0
    set flash_type mt28gu01gaax1e-bpi-x16
} elseif {$::env(BOARD) eq "kc705"} {
    set device_name xc7k325t_0
    set flash_type s25fl256sxxxxxx0-spi-x1_x2_x4
} elseif {$::env(BOARD) eq "nexys_video"} {
    set device_name xc7a200t_0
    set flash_type s25fl256sxxxxxx0-spi-x1_x2_x4
} else {
    puts "ERROR: Unknown BOARD=$::env(BOARD)"
    exit 1
}

# Auto-detect the hardware target containing our device
foreach target [get_hw_targets] {
    open_hw_target $target
    if {[llength [get_hw_devices $device_name]] > 0} {
        break
    }
    close_hw_target
}

current_hw_device [get_hw_devices $device_name]
refresh_hw_device -update_hw_probes false [current_hw_device]

# Create the flash device and configure programming options
set mcsfile work-fpga/ariane_xilinx.mcs
create_hw_cfgmem -hw_device [current_hw_device] [lindex [get_cfgmem_parts $flash_type] 0]
set cfgmem [get_property PROGRAM.HW_CFGMEM [current_hw_device]]
set_property PROGRAM.FILES [list $mcsfile] $cfgmem
set_property PROGRAM.PRM_FILE {} $cfgmem
set_property PROGRAM.ADDRESS_RANGE {use_file} $cfgmem
set_property PROGRAM.BLANK_CHECK 0 $cfgmem
set_property PROGRAM.ERASE 1 $cfgmem
set_property PROGRAM.CFG_PROGRAM 1 $cfgmem
set_property PROGRAM.VERIFY 1 $cfgmem
set_property PROGRAM.CHECKSUM 0 $cfgmem

if {$::env(BOARD) eq "vc707"} {
    set_property PROGRAM.BPI_RS_PINS {none} $cfgmem
    set_property PROGRAM.UNUSED_PIN_TERMINATION {pull-none} $cfgmem
}

# Load flash-programming bitstream into FPGA, then program flash
create_hw_bitstream -hw_device [current_hw_device] [get_property PROGRAM.HW_CFGMEM_BITFILE [current_hw_device]]
program_hw_devices [current_hw_device]
refresh_hw_device [current_hw_device]
program_hw_cfgmem -hw_cfgmem $cfgmem
