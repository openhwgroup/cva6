# General Architecture

## Scoreboarding

The scoreboards main purpose is to decouple the check for data (WAW, WAR) and structural hazards and issue instructions to the various functional units. It does so by taking full responsibility for instruction issue and execution. This also includes detecting the two aforementioned hazards.

The scoreboard enables utilization of all available functional units as well as efficient usage of pipelined functional units which take a couple of cycles before the instruction finishes. The scoreboard tracks all instructions which are currently being processed in all functional units.

Because the scoreboard is in full control over the functional units it also controls the forwarding path and write back of all functional units.

1. **Issue**: If a functional unit for the instruction is free and no other active instruction has the same  destination register, the scoreboard issues the instruction to the functional unit. If a WAW hazard is present, the instruction issue will stall until the hazard has been cleared. Should the issue stage stall the instruction buffer in the ID stage fills until it is full.
2. **Read operand**: The scoreboard monitors the availability of the source operands. A source operand is available if no earlier issued active instruction is going to write it. When the source operands are available (either through the register file or through a forwarding path from any of the other functional units or an already completed instruction), the scoreboard tells the FUs to proceed to read the operands. The scoreboard resolves RAW hazards dynamically in this step.
3. **Execution**: The FU begins execution upon receiving operands. When the result is ready, it notifies the scoreboard. Any instruction can take multiple cycles.
4. **Write Back**: Once the scoreboard is aware that the functional unit has completed execution, it commits the result in-order to either the architectural register file, CSR register file, floating point register file or data memory. If there are no structural dependencies on the write path the scoreboard can write more than one result at a time.

The scoreboard maintains a connection to each functional unit and each architectural state holding element. For Ariane there is the plan to include the following FUs: ALU, Multiplier and LSU. If it should turn out to be necessary additional ALUs or multipliers can be easily added.
TODO: Detailed Bookkeeping

> While it will be possible that the execute stage houses more than one ALU or multiplier, this is not going to be the case for the load store unit (LSU). The current assumption will be, that the LSU is like any other functional unit (using a variable amount of cycles to perform its operation), but it should also be in full control over the data memories state. It therefore takes a special role in the whole design.

The scoreboard has the following entries:

|            **Name**           | **Abbr.** |                                           **Description**                                           |
| ----------------------------- | --------- | --------------------------------------------------------------------------------------------------- |
| Program Counter               | PC        | Program counter of instruction                                                                      |
| Functional Unit               | FU        | Which type of  functional unit this instruction is going to need                                    |
| FU Result                     | FUR       | Which functional unit the result is coming from                                                     |
| Operation                     | OP        | Which operation the functional unit is going to perform on it                                       |
| Destination Register          | RD        | Destination register address of instruction                                                         |
| Value of destination register | VAL(RD)   | Result written by the functional unit. The result in here is valid only if the finished bit is set. |
| Immediate                     | IMM       | Immediate Field                                                                                     |
| Source Register 1             | RS1       | First source registers address of instruction                                                       |
| Source Register 2             | RS2       | Second source registers address of instruction                                                      |
| In Flight                     | IF        | Set to one if the instruction is currently being processed                                          |
| Valid                         | VALID     | The instruction has been executed and the result is valid                                           |
| Exception Valid               | ISEXCPT   | Set if an exception occurred.                                                                       |
| Exception Cause               | ECAUSE    | Exception cause as listed in privileged specification                                               |

Register addresses can be of type: CSR, Regfile (x0,.., x31), None (immediate), current PC
TODO: Register Encoding, OP encoding


### Exception Propagation

In order to simplify hardware design exceptions are only considered at commit time. Therefore, the scoreboard provides an exception field. If an exception has been present prior to issue (for example in the fetch or decode step) it has been propagated to this point. An instruction that has the exception flag set is considered as completed by the scoreboard and can be retired as soon as every instruction prior to this one has been committed.

### Scoreboard Implementation

The scoreboard is implemented as a circular buffer with two pointers. The first pointer being the commit point. Everything above this pointer is save to be reused for new instructions arriving. The issue pointer points to the top of the buffer, e.g.: always to the latest issued instruction. The scoreboard therefore keeps track of instruction ordering.

### Functional Units

The FU are not supposed to have inter-unit dependencies for the moment, e.g.: every FU must be able to perform its operation independently of every other unit. The following interface is proposed to keep maximum interoperability. A minimum set of port definitions would be:

| **Signal** | **Direction** |                **Description**                |
| ---------- | ------------- | --------------------------------------------- |
| clk_i      | Input         | Global clock signal                           |
| rst_ni     | Input         | Reset the functional unit to a specific state |
| operator_i | Input         | Operation to perform                          |
| operand_ai | Input         | Operand A                                     |
| operand_bi | Input         | Operand B                                     |
| result_o   | Output        | Result Output                                 |
| valid_i    | Input         | Data is valid from ID/Scoreboard              |
| ready_o    | Output        | Ready signal to ID/Scoreboard                 |
| ready_i    | Input         | Ready signal from WB/Scoreboard               |
| valid_o    | Output        | Data is valid to WB/Scoreboard                |

TODO: Details about comparisons and branches.

### LSU

Loads can be issued immediately while stores need to wait for the commit signal from the scoreboard. They are kept in a store address queue (SAQ) for the time being.

### Commit Point

The scoreboard is the only way to update the architectural state. This simplifies the controller design significantly since this is the only point where an exception is known to be taken.

### Issue Window

Currently the idea is to not speculate past branches or jumps. So the issue window is the size of a basic block. Theoretically it could be possible to speculate past one branch.

If the scoreboard encounters a branch it does not accept new instructions from ID. Executes the branch instruction. In the next cycle the speculated pc is compared to the calculated PC. If they match the scoreboard starts to issue instructions again. If not, a miss-predict is signaled and all fetched instructions are killed prior to the execute stage. The pipeline fills from the new address. Branch prediction data structures are updated accordingly.

## Load Store Unit
The load store unit is similar to every other functional unit. In addition, it has to manage the interface to the data memory. In particular, it houses the DTLB (Data Translation Lookaside Buffer) and the page table walker (PTW). It arbitrates the access to data memory, giving precedence to PTW lookups. This is done in order to unstall TLB misses as soon as possible.

The load store unit can issue load request immediately while stores need to be kept back as long as the scoreboard does not issue a commit signal. Therefore, upon a load, the LSU also needs to check its SAQ for potential data words. Should it find uncommitted data it stalls, since it can’t satisfy the current request. This means:

- Two loads to the same address are allowed. They will return in issue order.
- Two stores to the same address are allowed. They are issued in-order by the scoreboard and stored in the SAQ as long as the scoreboard didn’t give the grant to commit them.
- A store followed by a load to the same address can only be satisfied if the store has already been committed (marked as committed in the SAQ). Otherwise the LSU stalls until the scoreboard commits the instruction. We cannot guarantee that the store will eventually be committed (e.g.: an exception occurred).

For the moment being, the LSU does not handle misaligned accesses (e.g.: access which are not aligned at a 64bit boundary). It simply issues a misaligned exception and lets the exception handler resolve the LD/ST. Furthermore, it can issue a load access exception.
If an exception was signaled by the WB stage, the LSU kills all entries in its store queue except those that have been marked as committed.

The LSU of the core takes care of accessing the data memory. Load and stores on words (32 bit), half words (16 bit) and bytes (8 bit) are supported.
Table 3 describes the signals that are used by the LSU.

|     **Signal**     | **Direction** |                                                    **Description**                                                     |
| ------------------ | ------------- | ---------------------------------------------------------------------------------------------------------------------- |
| data_req_o         | output        | Request ready, must stay high until data_gnt_i is high for one cycle                                                   |
| data_addr_o[31:0]  | output        | Address                                                                                                                |
| data_we_o          | output        | Write Enable, high for writes, low for reads. Sent together with data_req_o                                            |
| data_be_o[3:0]     | output        | Byte Enable. Is set for the bytes to write/read, sent together with data_req_o                                         |
| data_wdata_o[31:0] | output        | Data to be written to memory, sent together with data_req_o                                                            |
| data_rdata_i[31:0] | input         | Data read from memory                                                                                                  |
| data_rvalid_i      | input         | data_rdata_is holds valid data when data_rvalid_i is high. This signal will be high for exactly one cycle per request. |
| data_gnt_i         | input         | The other side accepted the request. data_addr_o may change in the next cycle                                          |

## Protocol

The protocol that is used by the LSU to communicate with a memory works as follows:

The LSU provides a valid address in data_addr_o and sets data_req_o high. The memory then answers with a data_gnt_i set high as soon as it is ready to serve the request. This may happen in the same cycle as the request was sent or any number of cycles later. After a grant was received, the address may be changed in the next cycle by the LSU. In addition, the data_wdata_o, data_we_o and data_be_o signals may be changed as it is assumed that the memory has already processed and stored that information. After receiving a grant, the memory answers with a data_rvalid_i set high if data_rdata_i is valid. This may happen one or more cycles after the grant has been received. Note that data_rvalid_i must also be set when a write was performed, although the data_rdata_i has no meaning in this case.
