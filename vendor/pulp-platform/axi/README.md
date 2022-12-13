# AXI SystemVerilog Modules for High-Performance On-Chip Communication
[![CI status](https://akurth.net/usrv/ig/shields/pipeline/akurth/axi/master.svg)](https://iis-git.ee.ethz.ch/akurth/axi/commits/master)
[![GitHub tag (latest SemVer)](https://img.shields.io/github/v/tag/pulp-platform/axi?color=blue&label=current&sort=semver)](CHANGELOG.md)
[![SHL-0.51 license](https://img.shields.io/badge/license-SHL--0.51-green)](LICENSE)

This repository provides modules to build on-chip communication networks adhering to the [AXI4 or AXI4-Lite standards](https://developer.arm.com/documentation/ihi0022/f-b).  For high-performance communication, we implement AXI4[+ATOPs from AXI5](#atomic-operations).  For lightweight communication, we implement AXI4-Lite.  We aim to provide a complete end-to-end communication platform, including endpoints such as DMA engines and on-chip memory controllers.

Our **design goals** are:
- **Topology Independence**: We provide elementary building blocks such as protocol [multiplexers](src/axi_mux.sv) and [demultiplexers](src/axi_demux.sv) that allow users to implement any network topology.  We also provide commonly used interconnecting components such as a [crossbar](src/axi_xbar.sv).
- **Modularity**: We favor design by composition over design by configuration where possible.  We strive to apply the *Unix philosophy* to hardware: make each module do one thing well.  This means you will more often instantiate our modules back-to-back than change a parameter value to build more specialized networks.
- **Fit for Heterogeneous Networks**: Our modules are parametrizable in terms of data width and transaction concurrency.  This allows to create optimized networks for a wide range of performance (e.g., bandwidth, concurrency, timing), power, and area requirements.  We provide modules such as [data width converters](src/axi_dw_converter.sv) and [ID width converters](src/axi_iw_converter.sv) that allow to join subnetworks with different properties, creating heterogeneous on-chip networks.
- **Full AXI Standard Compliance**.
- **Compatibility** with a [wide range of (recent versions of) EDA tools](#which-eda-tools-are-supported) and implementation in standardized synthesizable SystemVerilog.

The **design and microarchitecture** of the modules in this repository is described in [**this paper**](https://ieeexplore.ieee.org/document/9522037) ([preprint](https://arxiv.org/pdf/2009.05334)).  If you use our work in your research, please cite it.


## List of Modules

In addition to the documents linked in the following table, we are setting up [documentation auto-generated from inline docstrings](https://pulp-platform.github.io/axi/master).  (Replace `master` in that URL with a tag to get the documentation for a specific version.)

| Name                                                 | Description                                                                                       | Doc                            |
|------------------------------------------------------|---------------------------------------------------------------------------------------------------|--------------------------------|
| [`axi_atop_filter`](src/axi_atop_filter.sv)          | Filters atomic operations (ATOPs), i.e., write transactions that have a non-zero `aw_atop` value. |                                |
| [`axi_burst_splitter`](src/axi_burst_splitter.sv)    | Split AXI4 burst transfers into single-beat transactions.                                         |                                |
| [`axi_cdc`](src/axi_cdc.sv)                          | AXI clock domain crossing based on a Gray FIFO implementation.                                    |                                |
| [`axi_cut`](src/axi_cut.sv)                          | Breaks all combinatorial paths between its input and output.                                      |                                |
| [`axi_delayer`](src/axi_delayer.sv)                  | Synthesizable module which can (randomly) delays AXI channels.                                    |                                |
| [`axi_demux`](src/axi_demux.sv)                      | Demultiplexes an AXI bus from one slave port to multiple master ports.                            | [Doc](doc/axi_demux.md)        |
| [`axi_dw_converter`](src/axi_dw_converter.sv)        | A data width converter between AXI interfaces of any data width.                                  |                                |
| [`axi_dw_downsizer`](src/axi_dw_downsizer.sv)        | A data width converter between a wide AXI master and a narrower AXI slave.                        |                                |
| [`axi_dw_upsizer`](src/axi_dw_upsizer.sv)            | A data width converter between a narrow AXI master and a wider AXI slave.                         |                                |
| [`axi_err_slv`](src/axi_err_slv.sv)                  | Always responds with an AXI decode/slave error for transactions which are sent to it.             |                                |
| [`axi_id_prepend`](src/axi_id_prepend.sv)            | This module prepends/strips the MSB from the AXI IDs.                                             |                                |
| [`axi_id_remap`](src/axi_id_remap.sv)                | Remap AXI IDs from wide IDs at the slave port to narrower IDs at the master port.                 | [Doc][doc.axi_id_remap]        |
| [`axi_id_serialize`](src/axi_id_serialize.sv)        | Reduce AXI IDs by serializing transactions when necessary.                                        | [Doc][doc.axi_id_serialize]    |
| [`axi_intf`](src/axi_intf.sv)                        | This file defines the interfaces we support.                                                      |                                |
| [`axi_isolate`](src/axi_isolate.sv)                  | A module that can isolate downstream slaves from receiving new AXI4 transactions.                 |                                |
| [`axi_iw_converter`](src/axi_iw_converter.sv)        | Convert between any two AXI ID widths.                                                            | [Doc][doc.axi_iw_converter]    |
| [`axi_join`](src/axi_join.sv)                        | A connector that joins two AXI interfaces.                                                        |                                |
| [`axi_lite_demux`](src/axi_lite_demux.sv)            | Demultiplexes an AXI4-Lite bus from one slave port to multiple master ports.                      | [Doc](doc/axi_lite_demux.md)   |
| [`axi_lite_join`](src/axi_lite_join.sv)              | A connector that joins two AXI-Lite interfaces.                                                   |                                |
| [`axi_lite_mailbox`](src/axi_lite_mailbox.sv)        | A AXI4-Lite Mailbox with two slave ports and usage triggered irq.                                 | [Doc](doc/axi_lite_mailbox.md) |
| [`axi_lite_mux`](src/axi_lite_mux.sv)                | Multiplexes AXI4-Lite slave ports down to one master port.                                        | [Doc](doc/axi_lite_mux.md)     |
| [`axi_lite_regs`](src/axi_lite_regs.sv)              | AXI4-Lite registers with optional read-only and protection features.                              | [Doc][doc.axi_lite_regs]       |
| [`axi_lite_to_apb`](src/axi_lite_to_apb.sv)          | AXI4-Lite to APB4 protocol converter.                                                             |                                |
| [`axi_lite_to_axi`](src/axi_lite_to_axi.sv)          | AXI4-Lite to AXI4 protocol converter.                                                             |                                |
| [`axi_lite_xbar`](src/axi_lite_xbar.sv)              | Fully-connected AXI4-Lite crossbar with an arbitrary number of slave and master ports.            | [Doc](doc/axi_lite_xbar.md)    |
| [`axi_modify_address`](src/axi_modify_address.sv)    | A connector that allows addresses of AXI requests to be changed.                                  |                                |
| [`axi_multicut`](src/axi_multicut.sv)                | AXI register which can be used to relax timing pressure on long AXI buses.                        |                                |
| [`axi_mux`](src/axi_mux.sv)                          | Multiplexes the AXI4 slave ports down to one master port.                                         | [Doc](doc/axi_mux.md)          |
| [`axi_pkg`](src/axi_pkg.sv)                          | Contains AXI definitions, common structs, and useful helper functions.                            |                                |
| [`axi_serializer`](src/axi_serializer.sv)            | Serializes transactions with different IDs to the same ID.                                        |                                |
| [`axi_test`](src/axi_test.sv)                        | A set of testbench utilities for AXI interfaces.                                                  |                                |
| [`axi_to_axi_lite`](src/axi_to_axi_lite.sv)          | AXI4 to AXI4-Lite protocol converter.                                                             |                                |
| [`axi_xbar`](src/axi_xbar.sv)                        | Fully-connected AXI4+ATOP crossbar with an arbitrary number of slave and master ports.            | [Doc](doc/axi_xbar.md)         |

### Simulation-Only Modules

In addition to the modules above, which are available in synthesis and simulation, the following modules are available only in simulation.  Those modules are widely used in our testbenches, but they are also suitable to build testbenches for AXI modules and systems outside this repository.

| Name                                                 | Description                                                                                            |
|------------------------------------------------------|--------------------------------------------------------------------------------------------------------|
| [`axi_chan_logger`](src/axi_test.sv)                 | Logs the transactions of an AXI4(+ATOPs) port to files.                                                |
| [`axi_driver`](src/axi_test.sv)                      | Low-level driver for AXI4(+ATOPs) that can send and receive individual beats on any channel.           |
| [`axi_lite_driver`](src/axi_test.sv)                 | Low-level driver for AXI4-Lite that can send and receive individual beats on any channel.              |
| [`axi_lite_rand_master`](src/axi_test.sv)            | AXI4-Lite master component that issues random transactions within user-defined constraints.            |
| [`axi_lite_rand_slave`](src/axi_test.sv)             | AXI4-Lite slave component that responds to transactions with constrainable random delays and data.     |
| [`axi_rand_master`](src/axi_test.sv)                 | AXI4(+ATOPs) master component that issues random transactions within user-defined constraints.         |
| [`axi_rand_slave`](src/axi_test.sv)                  | AXI4(+ATOPs) slave component that responds to transactions with constrainable random delays and data.  |
| [`axi_scoreboard`](src/axi_test.sv)                  | Scoreboard that models a memory that only gets changed by the monitored AXI4(+ATOPs) port.             |
| [`axi_sim_mem`](src/axi_sim_mem.sv)                  | Infinite memory with AXI4 slave port.                                                                  |



## Atomic Operations

AXI4+ATOPs means the full AXI4 specification plus atomic operations (ATOPs) as defined in Section E2.1 of the AMBA5 specification. This has the following implications for modules that do not implement ATOPs and systems that include such modules:

- Masters that do not issue ATOPs must set `aw_atop` to `'0`.
- Slaves that do not support ATOPs must specify this in their interface documentation and can ignore the `aw_atop` signal.
- System designers are responsible for ensuring that
  1. slaves that do not support ATOPs are behind an [`axi_atop_filter`](src/axi_atop_filter.sv) if any master could issue an ATOP to such slaves and
  2. the `aw_atop` signal is well-defined at the input of any (non-AXI4-Lite) module in this repository.

Masters and slaves that do support ATOPs must adhere to Section E2.1 of the AMBA5 specification.


## Which EDA Tools Are Supported?

Our code is written in standard SystemVerilog ([IEEE 1800-2012][], to be precise), so the more important question is: Which subset of SystemVerilog does your EDA tool support?

We aim to be compatible with a wide range of EDA tools.  For this reason, we strive to use as simple language constructs as possible, especially for our synthesizable modules.  We encourage contributions that further simplify our code to make it compatible with even more EDA tools.  We also welcome contributions that work around problems that specific EDA tools may have with our code, as long as:
- the EDA tool is reasonably widely used,
- recent versions of the EDA tool are affected,
- the workaround does not break functionality in other tools, and
- the workaround does not significantly complicate code or add maintenance overhead.

All code in each release and on the default branch is tested on a recent version of at least one industry-standard RTL simulator and synthesizer.  You can examine the [CI settings](./.gitlab-ci.yml) to find out which version of which tool we are running.


[IEEE 1800-2012]: https://standards.ieee.org/standard/1800-2012.html
[doc.axi_id_remap]: https://pulp-platform.github.io/axi/master/module.axi_id_remap
[doc.axi_id_serialize]: https://pulp-platform.github.io/axi/master/module.axi_id_serialize
[doc.axi_iw_converter]: https://pulp-platform.github.io/axi/master/module.axi_iw_converter
[doc.axi_lite_regs]: https://pulp-platform.github.io/axi/master/module.axi_lite_regs
