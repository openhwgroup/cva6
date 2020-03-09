# Documentation of AXI Modules

This folder contains the documentation of the following modules:

- [AXI Crossbar (`axi_xbar`)](axi_xbar.md)
- [AXI Demultiplexer (`axi_demux`)](axi_demux.md)
- [AXI Multiplexer (`axi_mux`)](axi_mux.md)
- [AXI4-Lite Mailbox (`axi_lite_mailbox`)](axi_lite_mailbox.md)


## Relevant Specifications

We adhere to the *AMBA AXI and ACE Protocol Specification, Issue F.b*, abbreviated as *AXI Spec* in these documents.


## Terminology

We follow the terminology defined in the AXI Glossary (see p. 433 of the AXI Spec).

Additionally, we define the following terms.

### Handshake

On a channel with valid and ready signals, a *handshake* occurs when both valid and ready are high on a clock edge.  See section A3.2.1 of the AXI Spec for details on the handshake process.

### In Flight

A transaction is *in flight* for a given interface when the handshake of the `Ax` beat of a transaction has occurred on that interface but the handshake of the (last) response of that transaction has not yet occurred on that interface.

### Pending

A handshake is *pending* for a given channel when the valid signal is high and the ready signal is low.
