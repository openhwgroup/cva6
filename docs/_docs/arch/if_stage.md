---
title: Instruction Fetch
permalink: /docs/if_stage/
---

Instruction Fetch stage (IF) gets its information from the PC Gen stage.
This information includes information about branch prediction (was it a
predicted branch? which is the target address? was it predicted to be
taken?), the current PC (word-aligned if it was a consecutive fetch) and
whether this request is valid. The IF stage asks the MMU to do address
translation on the requested PC and controls the I\$ (or just an
instruction memory) interface. The instruction memory interface is
described in more detail in .

The delicate part of the instruction fetch is that it is very timing
critical. This fact prevents us from implementing some more elaborate
handshake protocol (as round-times would be too large). Therefore the IF
stage signals the I\$ interface that it wants to do a fetch request to
memory. Depending on the cache's state this request may be granted or
not. If it was granted the instruction fetch stage puts the request in
an internal FIFO. It needs to do so as it has to know at any point in
time how many transactions are outstanding. This is mostly due to the
fact that instruction fetch happens on a very speculative basis because
of branch prediction. It can always be the case that the controller
decides to flush the instruction fetch stage in which case it needs to
discard all outstanding transactions.

The current implementation allows for a maximum of two outstanding
transaction. If there are more than two the IF stage will simply not
acknowledge any new request from PC Gen. As soon as a valid answer from
memory returns (and the request is not considered out-dated because of a
flush) the answer is put into a FIFO together with the fetch address and
the branch prediction information.

Together with the answer from memory the MMU will also signal potential
exceptions. Therefore this is the first place where exceptions can
potentially happen (bus errors, invalid accesses and instruction page
faults).

#### Fetch FIFO {#ssub:fetch_fifo}

The fetch FIFO contains all requested (valid) fetches from instruction
memory. The FIFO currently has one write port and two read ports (of
which only one is used). In a future implementation the second read port
could potentially be used to implement macro-op fusion or widen the
issue interface to cover two instructions.

The fetch FIFO also fully decouples the processor's front-end and its
back-end. On a flush request the whole fetch FIFO is reset.
