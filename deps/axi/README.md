# AXI

This is the implementation of the AMBA AXI protocol developed as part of the PULP platform as ETH Zurich. We implement AXI4+ATOPs and AXI4-Lite.


## List of Modules

| Name                                                 | Description                                                                                       | Doc                            |
|------------------------------------------------------|---------------------------------------------------------------------------------------------------|--------------------------------|
| [`axi_atop_filter`](src/axi_atop_filter.sv)          | Filters atomic operations (ATOPs), i.e., write transactions that have a non-zero `aw_atop` value. |                                |
| [`axi_burst_splitter`](src/axi_burst_splitter.sv)    | Split AXI4 burst transfers into single-beat transactions.                                         |                                |
| [`axi_cdc`](src/axi_cdc.sv)                          | AXI clock domain crossing based on a Gray FIFO implementation.                                    |                                |
| [`axi_cut`](src/axi_cut.sv)                          | Breaks all combinatorial paths between its input and output.                                      |                                |
| [`axi_delayer`](src/axi_delayer.sv)                  | Synthesizable module which can (randomly) delays AXI channels.                                    |                                |
| [`axi_demux`](src/axi_demux.sv)                      | Demultiplexes an AXI bus from one slave port to multiple master ports.                            | [Doc](doc/axi_demux.md)        |
| [`axi_dw_converter.sv`](src/axi_dw_converter.sv)     | A data width converter between AXI interfaces of any data width.                                  |                                |
| [`axi_dw_downsizer.sv`](src/axi_dw_downsizer.sv)     | A data width converter between a wide AXI slave and a narrower AXI master.                        |                                |
| [`axi_dw_upsizer.sv`](src/axi_dw_upsizer.sv)         | A data width converter between a narrow AXI slave and a wider AXI master.                         |                                |
| [`axi_err_slv`](src/axi_err_slv.sv)                  | Always responds with an AXI decode/slave error for transactions which are sent to it.             |                                |
| [`axi_id_prepend`](src/axi_id_prepend.sv)            | This module prepends/strips the MSB from the AXI IDs.                                             |                                |
| [`axi_intf`](src/axi_intf.sv)                        | This file defines the interfaces we support.                                                      |                                |
| [`axi_join`](src/axi_join.sv)                        | A connector that joins two AXI interfaces.                                                        |                                |
| [`axi_lite_demux`](src/axi_lite_demux.sv)            | Demultiplexes an AXI4-Lite bus from one slave port to multiple master ports.                      | [Doc](doc/axi_lite_demux.md)   |
| [`axi_lite_join`](src/axi_lite_join.sv)              | A connector that joins two AXI-Lite interfaces.                                                   |                                |
| [`axi_lite_mailbox`](src/axi_lite_mailbox.sv)        | A AXI4-Lite Mailbox with two slave ports and usage triggered irq.                                 | [Doc](doc/axi_lite_mailbox.md) |
| [`axi_lite_mux`](src/axi_lite_mux.sv)                | Multiplexes AXI4-Lite slave ports down to one master port.                                        | [Doc](doc/axi_lite_mux.md)     |
| [`axi_lite_to_apb`](src/axi_lite_to_apb.sv)          | AXI4-Lite to APB4 protocol converter.                                                             |                                |
| [`axi_lite_to_axi`](src/axi_lite_to_axi.sv)          | AXI4-Lite to AXI4 protocol converter.                                                             |                                |
| [`axi_lite_xbar`](src/axi_lite_xbar.sv)              | Fully-connected AXI4-Lite crossbar with an arbitrary number of slave and master ports.            | [Doc](doc/axi_lite_xbar.md)    |
| [`axi_modify_address`](src/axi_modify_address.sv)    | A connector that allows addresses of AXI requests to be changed.                                  |                                |
| [`axi_multicut`](src/axi_multicut.sv)                | AXI register which can be used to relax timing pressure on long AXI buses.                        |                                |
| [`axi_mux`](src/axi_mux.sv)                          | Multiplexes the AXI4 slave ports down to one master port.                                         | [Doc](doc/axi_mux.md)          |
| [`axi_pkg`](src/axi_pkg.sv)                          | Contains AXI definitions, common structs, and useful helper functions.                            |                                |
| [`axi_test`](src/axi_test.sv)                        | A set of testbench utilities for AXI interfaces.                                                  |                                |
| [`axi_to_axi_lite`](src/axi_to_axi_lite.sv)          | AXI4 to AXI4-Lite protocol converter.                                                             |                                |
| [`axi_xbar`](src/axi_xbar.sv)                        | Fully-connected AXI4+ATOP crossbar with an arbitrary number of slave and master ports.            | [Doc](doc/axi_xbar.md)         |

## Atomic Operations

AXI4+ATOPs means the full AXI4 specification plus atomic operations (ATOPs) as defined in Section E2.1 of the AMBA5 specification. This has the following implications for modules that do not implement ATOPs and systems that include such modules:

- Masters that do not issue ATOPs can simply permanently set `aw_atop` to `0`.
- Slaves that do not support ATOPs must specify this in their interface documentation and can ignore the `aw_atop` signal.
- System designers are responsible for ensuring that slaves that do not support ATOPs are behind an [`axi_atop_filter`](src/axi_atop_filter.sv) if any master could issue an ATOP to such slaves.

Masters and slaves that do support ATOPs must adhere to Section E2.1 of the AMBA5 specification.
