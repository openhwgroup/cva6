
# Block Details

The processor has 5-stages:

## Next PC Generation (PC Gen)

PC gen is responsible for generating the next program counter. All program counters are logical addressed. If the logical to physical mapping changes a fence instruction should flush the pipeline, caches (?) and TLB.
This stage contains speculation on the next branch target as well as the information if the branch target is taken or not. In addition, it provides ports to the branch history table (BHT) and branch target buffer (BTB).

<!-- If the ID stage decodes a jump and link instruction it sets PC+4 in the RAS. If it the decode stage decodes a return instruction the decode stage kills the program counter in the IF stage and the return address stack is popped accordingly.
 -->
If the branch target buffer decodes a certain PC as a jump the BHT decides if the branch is taken or not.
Because of the various state-full memory structures this stage is split into two pipeline stages. It also provides a handshaking signal to the decode stage to stall the pipeline if this should be necessary (back-pressure).

The next PC can originate from the following sources:

1.  Exception (including interrupts): This also means to figure out to which exception handler the delegate registers are pointing to. If an exception is taken, disable interrupts.
2.  Debug
3.  Request from execute stage (jump, branch) which was not detected as one by the BHT.
4.  Predicted PC (BHT and BTB)
5.  Environment Call (`ecall) instruction. Read the CSRs to figure out where to jump.
6.  Miss-predict: This triggers a pipeline flush and the PC Gen stage starts fetching from there.

### ITLB

## Instruction Fetch (IF)

In the IF stage we already know the physical PC. The request of the instruction is on its way to the instruction memory. We know the result of the BHT and can set the next PC accordingly. At the end of this stage the instruction PC is passed on to the ID stage. Retrieved instructions are stored in an instruction queue.
It is possible that a TLB or cache miss occurred. If this is the case the IF stage signals that it is not ready. The pipeline in the direction of the ID stage will empty itself.

### BTB

### BHT

### Instruction Queue

The instruction queue is part of the IF stage. Its purpose is to decouple the instruction fetch unit as much as possible from the rest of the pipeline.

### Interface

|      **Signal**     | **Direction** |            **Description**             |         **Category**        |
| ------------------- | ------------- | -------------------------------------- | --------------------------- |
| epc_i               | Input         | EPC from CSR registers                 | CSR Regs                    |
| ecall_i             | Input         | Ecall request from WB                  | WB/Commit                   |
| mtvec_i             | Input         | Base of machine trap vector            | CSR Regs                    |
| stvec_i             | Input         | Base of supervisor trap vector         | CSR Regs                    |
| epc_wb_i            | Input         | EPC Writeback                          | WB/Commit                   |
| epc_wb_valid_i      | Input         | EPC from WB is valid                   | WB/Commit                   |
|                     |               |                                        |                             |
| flush_s1_i          | Input         | Flush PC Gen stage                     | Control                     |
| flush_s2_i          | Input         | Flush fetch stage                      | Control                     |
| bp_pc_i             | Input         | Branch prediction PC, from EX stage    | EX -- Update BP/take branch |
| bp_misspredict_i    | Input         | Branch was misspredicted               | EX -- Update BP/take branch |
| bp_target_address_i | Input         | Target address of miss-predicted  jump | EX -- Update BP/take branch |
| instr_req_o         | Output        | Request to ICache                      | ICache                      |
| instr_addr_o        | Output        | Instruction address                    | ICache                      |
| instr_rdata_i       | Input         | Instruction data in                    | ICache                      |
|                     |               |                                        |                             |
| dbg_addr_i          | Input         | Fetch address from debug               | Debug                       |
| instr_valid_o       | Output        | Instruction is valid                   | To ID                       |
| instr_rdata_o       | Output        | Instruction                            | To ID                       |
| pc_o                | Output        | PC of instruction                      | To ID                       |
| is_spec_branch_o    | Output        | Is a speculative branch instruction    | To ID                       |
| spec_branch_pc_o    | Output        | Speculated branch target               | To ID                       |
| busy_o              | Output        | If is busy                             | To ID                       |
| ready_i             | Input         | ID is ready                            | From ID                     |

## Instruction Decode (ID)

The ID stage contains the instruction decode logic (including the planned compressed decoder) as well as the register files (CSR, floating point and regular register file). The decoded instruction is committed to the scoreboard. The scoreboard decides which instruction it can issues next to the execute stage.

### Compressed Decoder
The compressed decoders purpose is to expand a compressed instruction (16 bit) to its 32 bit equivalent.


### Interface

| **Signal** | **Direction** |    **Description**     | **Category** |
| ---------- | ------------- | ---------------------- | ------------ |
| flush_i    | Input         | EPC from CSR registers | CSR Regs     |


## Execute Stage (EX)

### Interface

| **Signal** | **Direction** |    **Description**     | **Category** |
| ---------- | ------------- | ---------------------- | ------------ |
| flush_i    | Input         | EPC from CSR registers | CSR Regs     |

## Writeback Stage (WB)

The writeback stage is the single commit point in the whole architecture. Everything prior to this stage was just computed in a temporary fashion. This is also the only point where an exception can occur.

### CSR Register File

The CSR register file contains all registers which are not directly related to arithmetic instructions. It contains the following registers supervisor registers:

| **Register** | **Address** |                      **Description**                      |
| ------------ | ----------- | --------------------------------------------------------- |
| sstatus      | 0x100       | Supervisor status register                                |
| sedeleg      | 0x102       | Supervisor exception delegation register (maybe external) |
| sideleg      | 0x103       | Supervisor interrupt delegation register (maybe external) |
| sie          | 0x104       | Supervisor interrupt-enable register (maybe external)     |
| stvec        | 0x105       | Supervisor trap handler base address                      |
| sscratch     | 0x140       | Scratch register for supervisor trap handler              |
| sepc         | 0x141       | Supervisor exception program counter                      |
| scause       | 0x142       | Supervisor trap cause                                     |
| stval        | 0x143       | Supervisor bad address or instruction                     |
| sip          | 0x144       | Supervisor interrupt pending (maybe external)             |
| sptbr        | 0x180       | Page-table base register                                  |

And the following machine mode CSR registers:

|     **Register**    |  **Address**   |                    **Description**                     |
| ------------------- | -------------- | ------------------------------------------------------ |
| mvendorid           | 0xF11          | Vendor ID                                              |
| marchid             | 0xF12          | Architecture ID                                        |
| mimpid              | 0xF13          | Implementation ID                                      |
| mhartid             | 0xF14          | Hardware thread ID                                     |
| mstatus             | 0x300          | Machine status register                                |
| medeleg             | 0x302          | Machine exception delegation register (maybe external) |
| mideleg             | 0x303          | Machine interrupt delegation register (maybe external) |
| mie                 | 0x304          | Machine interrupt-enable register (maybe external)     |
| mtvec               | 0x305          | Machine trap handler base address                      |
| mscratch            | 0x340          | Machine register for machine trap handler              |
| mepc                | 0x341          | Machine exception program counter                      |
| mcause              | 0x342          | Machine trap cause                                     |
| mtval               | 0x343          | Machine bad address or instruction                     |
| mip                 | 0x344          | Machine interrupt pending (maybe external)             |
| mcycle              | 0xB00          | Machine cycle counter                                  |
| minstret            | 0xB02          | Machine instruction-retired counter                    |
| Performance Counter | 0xB03 -- 0xB9F | Machine performance-monitoring counter                 |

### Interface

| **Signal** | **Direction** |    **Description**     | **Category** |
| ---------- | ------------- | ---------------------- | ------------ |
| flush_i    | Input         | EPC from CSR registers | CSR Regs     |


## MMU

|      **Signal**      | **Direction** |                                     **Description**                                      |
| -------------------- | ------------- | ---------------------------------------------------------------------------------------- |
| enable_translation_i | Input         | Enables translation, coming from CSR file.                                               |
| ireq_o               | Output        |                                                                                          |
| ivalid_i             | Output        |                                                                                          |
| ierr_i               | Input         |                                                                                          |
| ipaddr_o             | Output        | Physical address out                                                                     |
| fetch_req_i          | Input         | Fetch request in                                                                         |
| fetch_gnt_o          | Output        | Fetch request granted                                                                    |
| fetch_valid_o        | Output        | The output is valid                                                                      |
| fetch_err_o          | Output        | Fetch error                                                                              |
| fetch_vaddr_i        | Input         | Virtual address in                                                                       |
| dreq_o               | Output        | Request to data memory                                                                   |
| dgnt_i               | Input         | Grant from data memory                                                                   |
| dvalid_i             | Input         | Data from data memory is valid                                                           |
| dwe_o                | Output        | Write enable to data memory                                                              |
| dbe_o                | Output        | Byte enable to data memory                                                               |
| dpaddr_o             | Output        | Physical address to data memory                                                          |
| ddata_i              | Input         | Data from data memory                                                                    |
| lsu_req_i            | Input         | Request from LSU                                                                         |
| lsu_gnt_o            | Output        | Request granted to LSU                                                                   |
| lsu_valid_o          | Output        | Data to LSU is valid                                                                     |
| lsu_we_i             | Input         | Write enable from LSU                                                                    |
| lsu_err_o            | Output        | Error to LSU                                                                             |
| lsu_be_i             | Input         | Byte enable from LSU                                                                     |
| lsu_vaddr_i          | Input         | Virtual address from LSU                                                                 |
| priv_lvl_i           | Input         | Current Privilige Level                                                                  |
| flag_pum_i           | Input         | PUM (Protected User Mode) Flag, prevents S-mode code to alter user mode code -- from CSR |
| flag_mxr_i           | Input         | MXR (Make eXecutable Readable), makes it possible to read executable only pages          |
| pd_ppn_i             | Input         | Physical page number                                                                     |
| asid_i               | Input         | ASID (address space identifier)                                                          |
| flush_tlb_i          | Input         | Flush TLB                                                                                |
| lsu_ready_wb_i       | Input         | LSU is ready to accept new data                                                          |
