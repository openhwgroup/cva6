# Generic Technology Cells (API to Cell Library)

Maintainer: Nils Wistoff <nwistoff@iis.ee.ethz.ch>

This repository contains technology related cells like SRAMs, clock-gating cells, power management cells. The description here are:

- **Behavioral**: Meant for RTL simulation only.
- **FPGA**: Meant for FPGA implementation. Currently we only support Xilinx FPGAs. But we are happy to accept patches for Altera or other devices.

It is the purpose of your technology specific file to include the cells with correct drive strength. We do not make the assumption in the front-end anymore.

> As this layer needs to be re-implemented for every new technology keep it thin!

## Cell Contents

If you want to get started in your own technology (either an unsupported FPGA or an ASIC technology) please provide implementations for the cells in this repository.

### Clock Cells

Clock cells usually are care-fully designed cells which do not exhibit any glitches. Therefore they need to be manually instantiated in ASIC designs. All clock cells can be found in `tc_clk.sv`.

| Name              | Description                  | Status | Xilinx             |
|-------------------|------------------------------|--------|--------------------|
| `tc_clk_and2`     | Clock and gate               | active | :white_check_mark: |
| `tc_clk_buffer`   | Clock buffer                 | active | :white_check_mark: |
| `tc_clk_gating`   | Integrated clock gating cell | active | :white_check_mark: |
| `tc_clk_inverter` | Clock inverter               | active | :white_check_mark: |
| `tc_clk_mux2`     | Clock Mux with two inputs    | active | :white_check_mark: |
| `tc_clk_xor2`     | Clock Xor                    | active | :white_check_mark: |
| `tc_clk_or2`      | Clock Or                     | active | :white_check_mark: |
| `tc_clk_delay`    | Programmable clock-delay     | active |                    |

### Memory

|    Name   |                       Description                        | Status |       Xilinx       |
|-----------|----------------------------------------------------------|--------|--------------------|
| `tc_sram` | Configurable SRAM                                        | active | :white_check_mark: |

### Power Cells

Power cells are mostly used for advanced power gating features and not used in any of our open-source IPs. However, feel-free to re-use them. All clock cells can be found in `tc_pwr.sv`.

|                 Name                |             Description              | Status |
|-------------------------------------|--------------------------------------|--------|
| `tc_pwr_level_shifter_in`           | Level Shifter                        | active |
| `tc_pwr_level_shifter_in_clamp_lo`  | Level Shifter w/ clamp to `1'b0`     | active |
| `tc_pwr_level_shifter_in_clamp_hi`  | Level Shifter w/ clamp to `1'b1`     | active |
| `tc_pwr_level_shifter_out`          | Level Shifter                        | active |
| `tc_pwr_level_shifter_out_clamp_lo` | Level Shifter w/ clamp to `1'b0`     | active |
| `tc_pwr_level_shifter_out_clamp_hi` | Level Shifter w/ clamp to `1'b1`     | active |
| `tc_pwr_power_gating`               | Power Gate with ctrl and status pins | active |
| `tc_pwr_isolation_lo`               | Isolation Cell w/ isolate to `1'b0`  | active |
| `tc_pwr_isolation_hi`               | Isolation Cell w/ isolate to `1'b1`  | active |
