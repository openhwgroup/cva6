# Ideas

## Dual Issue Implementation

By widening the fetch interface to 64bit we could theoretically fetch two and more instructions with a single fetch. Doubling the (compressed) decoder would result in a dual issue architecture.

## Power-down Mode

The CSR’s APB interface would allow for storing the CPU state (registers, CSR registers, etc.) to a state retentive memory when the core is in complete power down.
