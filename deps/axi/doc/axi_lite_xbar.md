# AXI4-Lite Fully-Connected Crossbar

`axi_lite_xbar` is a fully-connected crossbar that implements the AXI4-Lite specification.

## Design Overview

`axi_lite_xbar` is a fully-connected crossbar, which means that each master module that is connected to a *slave port* for of the crossbar has direct wires to all slave modules that are connected to the *master ports* of the crossbar.
A block-diagram of the crossbar is shown below:

![Block-diagram showing the design of the full AXI4-Lite Crossbar.](axi_lite_xbar.png  "Block-diagram showing the design of the full AXI4-Lite Crossbar.")

The crossbar has a configurable number of slave and master ports.

## Address Map

`axi_lite_xbar` uses the [same address decoding scheme](axi_xbar.md#address-map) as `axi_xbar`.

## Decode Errors and Default Slave Port

Each slave port has its own internal *decode error slave* module.  If the address of a transaction does not match any rule, the transaction is routed to that decode error slave module.  That module absorbs each transaction and responds with a decode error (with the proper number of beats).  The data of each read response beat is `32'hBADCAB1E` (zero-extended or truncated to match the data width).

Each slave port can have a default master port.  If the default master port is enabled for a slave port, any address on that slave port that does not match any rule is routed to the default master port instead of the decode error slave.  The default master port can be enabled and changed at run time (it is an input signal to the crossbar), and the same restrictions as for the address map apply.


## Configuration

The crossbar is configured through the `Cfg` parameter with a `axi_pkg::xbar_cfg_t` struct.  That struct has the following fields:

| Name                 | Type               | Definition                                                                                                                                                                                                                                                        |
|:---------------------|:-------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `NoSlvPorts`         | `int unsigned`     | The number of AXI4-Lite slave ports of the crossbar (in other words, how many AXI4-Lite master modules can be attached).                                                                                                                                          |
| `NoMstPorts`         | `int unsigned`     | The number of AXI4-Lite master ports of the crossbar (in other words, how many AXI4-Lite slave modules can be attached).                                                                                                                                          |
| `MaxMstTrans`        | `int unsigned`     | Each slave port can have at most this many transactions [in flight](../doc#in-flight).                                                                                                                                                                            |
| `MaxSlvTrans`        | `int unsigned`     | Each master port can have at most this many transactions [in flight](../doc#in-flight).                                                                                                                                                                           |
| `FallThrough`        | `bit`              | Routing decisions on the AW channel fall through to the W channel.  Enabling this allows the crossbar to accept a W beat in the same cycle as the corresponding AW beat, but it increases the combinatorial path of the W channel with logic from the AW channel. |
| `LatencyMode`        | `enum logic [9:0]` | Latency on the individual channels, defined in detail in section *Pipelining and Latency* below.                                                                                                                                                                  |
| `AxiIdWidthSlvPorts` | `int unsigned`     | Not used by the AXI4-Lite crossbar. Set `default: '0`.                                                                                                                                                                                                            |
| `AxiIdUsedSlvPorts`  | `int unsigned`     | Not used by the AXI4-Lite crossbar. Set `default: '0`.                                                                                                                                                                                                            |
| `AxiAddrWidth`       | `int unsigned`     | The AXI4-Lite address width.                                                                                                                                                                                                                                      |
| `AxiDataWidth`       | `int unsigned`     | The AXI4-Lite data width.                                                                                                                                                                                                                                         |
| `NoAddrRules`        | `int unsigned`     | The number of address map rules.                                                                                                                                                                                                                                  |

The other parameters are types to define the ports of the crossbar.  The `*_chan_t` and `*_req_t`/`*_resp_t` types must be bound in accordance to the configuration with the `AXI_TYPEDEF` macros defined in `axi/typedef.svh`.  The `rule_t` type must be bound to an address decoding rule with the same address width as in the configuration, and `axi_pkg` contains definitions for 64- and 32-bit addresses.

### Pipelining and Latency

The `LatencyMode` parameter allows to insert spill registers after each channel (AW, W, B, AR, and R) of each master port (i.e., each multiplexer) and before each channel of each slave port (i.e., each demultiplexer).  Spill registers cut combinatorial paths, so this parameter reduces the length of combinatorial paths through the crossbar.

Some common configurations are given in the `xbar_latency_e` `enum`.  The recommended configuration (`CUT_ALL_AX`) is to have a latency of 2 on the AW and AR channels because these channels have the most combinatorial logic on them.  Additionally, `FallThrough` should be set to `0` to prevent logic on the AW channel from extending combinatorial paths on the W channel.  However, it is possible to run the crossbar in a fully combinatorial configuration by setting `LatencyMode` to `NO_LATENCY` and `FallThrough` to `1`.
If two crossbars are connected in both directions, meaning both have one of their master_ports connected to a slave_port of the other, it is required to have either `CUT_SLV_PORTS`, `CUT_MST_PORTS` or `CUT_ALL_PORTS` as the configuration of the two crossbars. This is to prevent timing loops. The other configurations will lead to timing loops in simulation and synthesis on the not cut channels between the two crossbars.

## Ports

| Name                    | Description                                                                                                                                                                   |
|:------------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `clk_i`                 | Clock to which all other signals (except `rst_ni`) are synchronous.                                                                                                           |
| `rst_ni`                | Reset, asynchronous, active-low.                                                                                                                                              |
| `test_i`                | Test mode enable (active-high).                                                                                                                                               |
| `slv_ports_*`           | Array of slave ports of the crossbar.  The array index of each port is the index of the slave port.  This index will be prepended to all requests at one of the master ports. |
| `mst_ports_*`           | Array of master ports of the crossbar.  The array index of each port is the index of the master port.                                                                         |
| `addr_map_i`            | Address map of the crossbar (see section *Address Map* above).                                                                                                                |
| `en_default_mst_port_i` | One bit per slave port that defines whether the default master port is active for that slave port (see section *Decode Errors and Default Slave Port* above).                 |
| `default_mst_port_i`    | One master port index per slave port that defines the default master port for that slave port (if active).                                                                    |


## Ordering and Stalls

The ordering inside the crossbar is organized by a network of FIFO's ensuring the in order transaction transmission. It is possible to have multiple transactions to different master ports in flight, however when one of the slave modules connected to these master ports stalls, other consecutive in fight transaction will also be stalled.

## Verification Methodology

This module has been verified with a directed random verification testbench, described and implemented in `test/tb_axi_lite_xbar.sv`.


## Design Rationale for No Pipelining Inside Crossbar

This is identical to the issue described in [`axi_xbar`](axi_xbar.md#design-rationale-for-no-pipelining-inside-crossbar).
