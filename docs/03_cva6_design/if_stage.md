# Instruction Fetch Stage

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

The data fetched at this point can contain compressed instructions,
in order to send valid instrctions to the Instruction Decode (ID) stage,
we need to chech for compressed instructions and re-align them.
This is the role of the Iistruction re-aligner.

#### Instruction Re-aligner

![Instruction re-alignment Process](_static/instr_realign.png)

As mentioned above the instruction re-aligner checks the incoming data
stream for compressed instructions. Compressed instruction have their
last bit unequal to 11 while normal 32-bit instructions have their last
two bit set to 11. The main complication arises from the fact that a
compressed instruction can make a normal instruction unaligned (e.g.:
the instruction starts at a half word boundary). This can (in the worst
case) mandate two memory accesses before the instruction can be fully
decoded. We therefore need to make sure that the fetch FIFO has enough
space to keep the second part of the instruction. Therefore the
instruction re-aligner needs to keep track of whether the previous
instruction was unaligned or compressed to correctly decide what to do
with the upcoming instruction.

Furthermore, the branch-prediction information is used to only output
the correct instruction to the issue stage. As we only predict on
word-aligned PCs the passed on branch prediction information needs to be
investigated to rule out which instruction we are actually need, in case
there are two instructions (compressed or unaligned) present. This means
that we potentially have to discard one of the two instructions (the
instruction before the branch target). For that reason the instruction
re-aligner also needs to check whether this fetch entry contains a valid
and taken branch. Depending on whether it is predicted on the upper 16
bit it has to discard the lower 16 bit accordingly. This process is
illustrate in .

#### Fetch FIFO

The fetch FIFO contains all requested (valid) fetches from instruction
memory. The FIFO currently has one write port and two read ports (of
which only one is used). In a future implementation the second read port
could potentially be used to implement macro-op fusion or widen the
issue interface to cover two instructions.

The fetch FIFO also fully decouples the processor's front-end and its
back-end. On a flush request the whole fetch FIFO is reset.
