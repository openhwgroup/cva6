# AXI

This is the implementation of the AMBA AXI protocol developed as part of the PULP platform as ETH Zurich. This repository will eventually contain interface definitions, crossbars, data width converters, traffic generators, and testbench utilities.

We implement AXI4+ATOPs and AXI4-Lite.

AXI4+ATOPs means the full AXI4 specification plus atomic operations (ATOPs) as defined in Section E2.1 of the AMBA5 specification. This has the following implications for modules that do not implement ATOPs and systems that include such modules:

- Masters that do not issue ATOPs can simply permanently set `aw_atop` to `0`.
- Slaves that do not support ATOPs must specify this in their interface documentation and can ignore the `aw_atop` signal.
- System designers are responsible for ensuring that slaves that do not support ATOPs are behind an [`axi_atop_filter`](src/axi_atop_filter.sv) if any master could issue an ATOP to such slaves.

Masters and slaves that do support ATOPs must adhere to Section E2.1 of the AMBA5 specification.
