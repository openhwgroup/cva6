# Ariane RISC-V CPU

6 stage, scoreboard based RISC-V CPU (pcgen, if, id, ex, mem, commit).

## Processor Design

This section describes the pipeline stages of Ariane.

### PC Gen

PC gen is responsible for generating the next program counter. All program counters are logical addresses. If the logical to physical mapping changes a fence instruction should flush the pipeline, caches and TLB.

This stage can contain speculation on the next branch target as well as if the branch target is taken or not. In addition it provides ports to update the return address stack (RAS) as well as the branch history table (BHT).

If the ID stage decodes a jump and link instruction it sets `PC+4` in the the RAS. If it decodes a return instruction the decode stage kills the program counter in the IF stage and the return address stack is popped accordingly.

If the branch target buffer decodes a certain PC as a jump the BHT decides if the branch is taken or not.

Because of the various state-full memory structures this stage is split into two pipeline stages. It also provides a handshaking signal to the decode stage to stall the pipeline if this should be necessary (back-pressure).

### ID Stage

#### Regfile

The register file has two read ports and one write port.

#### CSR Registers

### Execute Stage

#### ALU

The ALU is a simplified version (e.g. without the vector operations) from RI5CY. In addition it support operations on 64-bit registers.

#### Multiplier

#### Load Store Unit

### Memory Stage

### Commit Stage

## Coding Style

- Keep the files tidy. No superfluous line breaks, align ports on a common boundary.
- All signal and module names should be lower case with underscores as whitespace replacements (e.g.: `fetch_busy`).
- Instantiation of modules should be postfix with `_i`, e.g.: `prefetcher_i`
- For port definitions keep a post-fix direction (`_o`, `_i`).
- For active low signals put an additional (`_no`, `_ni`).
- Denote output of ff with `_q` and the input with `_n`.

### Git Considerations

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