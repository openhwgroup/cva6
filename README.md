# Ariane RISC-V CPU

6 stage, scoreboard based, RISC-V CPU (pcgen, if, id, ex, mem, commit).

## Processor Design

This section describes the pipeline stages of Ariane.

### PC Gen

PC gen is responsible for generating the next program counter. All program counters are logical addressed. If the logical to physical mapping changes a fence instruction should flush the pipeline, caches (?) and TLB.

This stage can contain speculation on the next branch target as well as the information if the branch target is taken or not. In addition it provides ports to update the return address stack (RAS) as well as the branch history table (BHT).

If the ID stage decodes a jump and link instruction it sets `PC+4` in the the RAS. If it the decode stage decodes a return instruction the decode stage kills the program counter in the IF stage and the return address stack is popped accordingly.

If the branch target buffer decodes a certain PC as a jump the BHT decides if the branch is taken or not.

Because of the various state-full memory structures this stage is split into two pipeline stages. It also provides a handshaking signal to the decode stage to stall the pipeline if this should be necessary (back-pressure).

The next PC can originate from the following sources:

- Exception (including interrupts)
- Debug
- Request from execute stage
- ecall instruction
- miss-predict

### IF Stage

In the IF stage we already now the physical PC. The request of the instruction is on its way to the instruction memory. We know the result of the BHT and kill the current request to the instruction memory or just let it pass on. At the end of this stage the instruction is passed on to the ID stage. Retrieved instructions are stored in an *instruction queue*.

It is possible that a TLB or cache miss occured. If this is the case the IF stage signals that it is not ready. The pipeline in the direction of the ID stage will empty itself.

### ID Stage

The ID stage contains the instruction decode logic (including the compressed decoder) as well as the register files (CSR, floating point and regular register file). The decoded instruction is committed to the scoreboard. The scoreboard decides which instruction it can issues next to execute stage.

#### Compressed Decoder

The compressed decoder is from RISCY.

#### Scoreboard

The scoreboard gets the instruction from the ID stage (the instruction commit part resides in the ID stage). The scoreboard keeps track of each instruction, the functional unit it needs to use (and if this particular FU is ready). The scoreboard has as many write ports as FU exist. It also keeps track of exceptions that have happened during any of the previous stages. If such an exception has occured the instruction is considered as executed and can directly pass on to the commit stage, where the control flow is changed.

#### Regfile

The register file has two read ports and one write port.

#### CSR Registers

The CSR register file is from RISCY.

### Execute Stage

The execute stage gets its instructions from the scoreboard (in no particular order). Every functional unit can need as many cycles as it needs to execute the instruction. Results are written to the scoreboard (note that many results can be ready concurrently). It is the scoreboards purpose to keep track of the initial ordering.

#### ALU

The ALU is a simplified version (e.g. without the vector operations) from RI5CY. In addition it support operations on 64-bit registers.

#### Multiplier

#### Load Store Unit

The LSU unit manages the access to the data memory. It supports misaligned load in which case it simple performs a second memory request. Note: Alternatively we could also load a wider word (e.g.: 128 bit), in which case probably a lot of unnecessary data will be retrieved.

The LSU does not directly output its address and data to the instruction memory but the result registered to the memory stage. In order to make the access to the data memory non-critical. Furthermore the LSU also arbitrates access from the PTW to the data memory, giving precedence to the PTW's access.

### Memory Stage

The memory stage makes the data request to the data memory. The result is received in the commit stage.

### Commit Stage

## Coding Style

- Keep the files tidy. No superfluous line breaks, align ports on a common boundary.
- All signal and module names should be lower case with underscores as whitespace replacements (e.g.: `fetch_busy`).
- Instantiation of modules should be postfix with `_i`, e.g.: `prefetcher_i`
- For port definitions keep a post-fix direction (`_o`, `_i`).
- For active low signals put an additional (`_no`, `_ni`).
- Denote output of ff with `_q` and the input with `_n`.
- Do not put overly large comment headers. Nevertheless, try to structure your HDL code, e.g.:
```
  // ------------------------------------
  // CSR - Control and Status Registers
  // ------------------------------------
```

### Git Considerations

- Do not push to master, if you want to add a feature do it in your branch
- Separate subject from body with a blank line
- Limit the subject line to 50 characters
- Capitalize the subject line
- Do not end the subject line with a period
- Use the imperative mood in the subject line
- Wrap the body at 72 characters
- Use the body to explain what and why vs. how

For a detailed why and how please refer to one of the multiple [resources](https://chris.beams.io/posts/git-commit/) regarding git commit messages.

If you use `vi` for your commit message, consider to put the following snippet inside your `~/.vimrc`:
```
autocmd Filetype gitcommit setlocal spell textwidth=72s
```