# AXI4-Lite Demultiplexer

`axi_lite_demux` splits one AXI4-Lite connection into multiple ones.

## Design Overview

The demultiplexer has one *slave port* and a configurable number of *master ports*.

The AW and AR channels each have a *select* input, to determine the master port to which they are sent. The select can, for example, be driven by an (external) address decoder to map address ranges to different AXI4-Lite slaves.

Beats on the W channel are routed by the demultiplexer with the same selection as the corresponding AW beat.

Beats on the B and R channel are multiplexed from the master ports by the switching decision saved in their respective FIFO's.


## Configuration

This demultiplexer is configured through the parameters listed in the following table:

| Name                 | Type               | Definition                                                                                                                                                                                                                                                                                             |
|:---------------------|:-------------------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `NoMstPorts`         | `int unsigned`     | The number of AXI4-Lite master ports of the demultiplexer (in other words, how many AXI4-Lite slave modules can be attached).                                                                                                                                                                          |
| `MaxTrans`           | `int unsigned`     | The slave port can have at most this many transactions [in flight](../doc#in-flight).                                                                                                                                                                                                                  |
| `FallThrough`        | `bit`              | Routing decisions on the AW channel fall through to the W channel (i.e. don't consume a cycle).  Enabling this allows the demultiplexer to accept a W beat in the same cycle as the corresponding AW beat, but it increases the combinatorial path of the W channel with logic from `slv_aw_select_i`. |
| `SpillXX`            | `bit`              | Inserts one spill register on the respective channel (AW, W, B, AR, and R) before the demultiplexer.                                                                                                                                                                                                   |

The other parameters are types to define the ports of the demultiplexer.  The `_*chan_t` types must be bound in accordance to the configuration using the `AXI_TYPEDEF` macros defined in `axi/typedef.svh`.

### Pipelining and Latency

The `SpillXX` parameters allow to insert spill register before each channel of the demultiplexer.  Spill registers cut all combinatorial paths of a channel (i.e., both payload and handshake).  Thus, they add one cycle of latency per channel but do not impair throughput.

If all `SpillXX` and `FallThrough` are disabled, all paths through this multiplexer are combinatorial (i.e., have zero latency).

## Ports

| Name                              | Description                                                                                                                                                                                      |
|:----------------------------------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `clk_i`                           | Clock to which all other signals (except `rst_ni`) are synchronous.                                                                                                                              |
| `rst_ni`                          | Reset, asynchronous, active-low.                                                                                                                                                                 |
| `test_i`                          | Test mode enable (active-high).                                                                                                                                                                  |
| `slv_*` (except `slv_*_select_i`) | Single slave port of the demultiplexer.                                                                                                                                                          |
| `slv_{aw,ar}_select_i`            | Index of the master port to which a write or read, respectively, is demultiplexed.  This signal must be stable while a handshake on the AW respectively AR channel is [pending](../doc#pending). |
| `mst_*`                           | Array of master ports of the demultiplexer.  The array index of each port is the index of the master port.                                                                                       |


### Implementation

W beats are routed to the master port defined by the value of `slv_aw_select_i` for the corresponding AW.  As the order of the W transactions is given by the order of the AWs, the select signals are stored in a FIFO.  This FIFO is pushed upon a handshake on the AW slave channel and popped upon a handshake of the corresponding W transaction.

The demultiplexer saves the routing decision in their respective FIFO for the response routing.
