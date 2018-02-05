# Styleguides

## TL;DR - Absolute Minimum

- If the existing coding style is sane, stick to it.
- Avoid `defines` and `ifdefs` as much as possible.
- Do not use tabs, use spaces.
- Use 4 spaces to open a new indentation level.
- Names of signals, modules, and structs should be *lower case with underscores* as whitespace replacements (e.g.: `fetch_busy`). Names of constants and parameters should be upper case with underscores. **Never use CamelCase**.
- Instantiation of modules should be prefixed with `i_`, e.g.: `i_prefetcher`.
- For port definitions keep a post-fix direction (`_o`, `_i`, `_io`).
- For active low signals put an additional (`n` for internal signals, `_no`, `_ni`, `_nio` for interface ones).
- Denote output of a register with `_q` and the input with `_d`.

## Coding Style

- Keep the files tidy. No superfluous line breaks, align ports on a common boundary.
- Do not use tabs, use spaces. If you really want to use tabs, use them consistently.
- Name dedicated signals wiring `module foo` (output) with `module bar` (input) `signal_foo_bar`
- Within an IP, use Interfaces to connect component instances whenever possible.
- Use Interfaces at the top-level interface of the IP, but also provide a wrapper that “unrolls” the Interfaces into input and output ports.
- Do not put overly large comment headers. Nevertheless, try to structure your HDL code, e.g.:

    ```
    // ------------------------------------
    // CSR - Control and Status Registers
    // ------------------------------------
    ```

- Specify memory map and integration rules while coding, using the `crazy88` (TODO: Link to Documentation) syntax.
- Put `begin` statements on the same level as the block qualifier, for example:

    ```verilog
    module A (
        input logic flush_i
    );

        logic whatever_signal;

        always_comb begin
            if (flush_i) begin
                // do some stuff here
            end else if (whatever_signal) begin
                // do some other stuff
            end
        end
    endmodule
    ```

- The exception to the former rule are `always` blocks, where the `begin` can be placed on a new line, for example (K&R):

    ```verilog
    module A (
        input logic flush_i
    );

        logic whatever_signal;

        always_comb
        begin
            if (flush_i) begin
                // do some stuff here
            end else if (whatever_signal) begin
                // do some other stuff
            end
        end
    endmodule
    ```

- For `case`, always use `begin` and `end` and follow the K&R style:

    ```verilog
        case (foo_i)
            8'h0 : begin
                // case 0
            end
            8'h1 : begin
                // case 1
            end
        endcase
    ```

- For `if`-`else` chains, use K&R style:

    ```verilog
        if (foo_i) begin
            // do stuff
        end else if (bar_i) begin
            // do some other stuff
        end
    ```

    As a variant, you can also put the end on its own line:

    ```verilog
        if (foo_i) begin
            // do stuff
        end
        else if (bar_i) begin
            // do some other stuff
        end
    ```

    > The rationale is that extra lines for `begin/else/end` carry no information at all. They even may prevent parts of the code to not have enough space on some screens. Process blocks on the other hand are more self-contained and multiple process blocks are not required to be visible at the same time.
    > The intention behind this is to keep code which is closely related together (like the code in an `always` block). It then should easily fit on a single screen.

- Give generics a meaningful type e.g.: `parameter int unsigned ASID_WIDTH = 1`. The default type is a signed integer which in most of the time does not make an awful lot of sense for hardware.
- Always name control blocks within a `generate`:

    ```verilog
        generate
            for (genvar i=0; i<10; i++) begin : ten_times_gen
                // something to generate 10x
            end // ten_times_gen

            if (PARAM == 0) begin : no_param_gen
                // something
            end // no_param_gen
            else begin : param_gen
                // something else
            end // param_gen
        endgenerate
    ```

-  Name `structs` which are used as types with a post-fix `_t`:

    ```verilog
    typedef struct packed {
        logic [1:0]  rw;
        priv_lvl_t   priv_lvl;
        logic  [7:0] address;
    } csr_addr_t;
    ```
    ```verilog
    module A (
        input logic [11:0] address_i
    );

        csr_addr_t csr_addr;

        assign csr_addr = csr_addr_t'(address_i);

        always_comb begin
            if (csr_addr.priv_lvl == U_MODE) begin
                // do something fancy with this signal
            end
        end
    endmodule
    ```

- Consider using [EditorConfig](http://editorconfig.org/):

    ```
    # top-most EditorConfig file
    root = true

    # Unix-style newlines with a newline ending every file
    [*]
    end_of_line = lf
    insert_final_newline = true
    trim_trailing_whitespace = true
    max_line_length = off
    # 4 space indentation
    [*.{sv, svh, v, vhd}]
    indent_style = space
    indent_size = 4
    ```

    There are plug-ins for almost any sane editor. The same example `.editorconfig` can also be found in this repository.

## Git Considerations

- Do not push to master, if you want to add a feature do it in your branch.
- Separate subject from body with a blank line.
- Limit the subject line to 50 characters.
- Capitalize the subject line.
- Do not end the subject line with a period.
- Use the imperative mood in the subject line.
- Use the present tense ("Add feature" not "Added feature").
- Wrap the body at 72 characters.
- Use the body to explain what and why vs. how.
- Consider starting the commit message with an applicable emoji:
    * :art: `:art:` when improving the format/structure of the code
    * :racehorse: `:racehorse:` when improving performance
    * :memo: `:memo:` when writing docs
    * :penguin: `:penguin:` when fixing something on Linux
    * :apple: `:apple:` when fixing something on macOS
    * :checkered_flag: `:checkered_flag:` when fixing something on Windows
    * :bug: `:bug:` when fixing a bug
    * :fire: `:fire:` when removing code or files
    * :green_heart: `:green_heart:` when fixing the CI build
    * :white_check_mark: `:white_check_mark:` when adding tests
    * :lock: `:lock:` when dealing with security
    * :arrow_up: `:arrow_up:` when upgrading dependencies
    * :arrow_down: `:arrow_down:` when downgrading dependencies
    * :shirt: `:shirt:` when removing linter warnings
    * :scissors: `:scissors:` when restructuring your HDL
    * :space_invader: `:space_invader:` when fixing something synthesis related

For a detailed why and how please refer to one of the multiple [resources](https://chris.beams.io/posts/git-commit/) regarding git commit messages.

If you use `vi` for your commit message, consider to put the following snippet inside your `~/.vimrc`:

```
autocmd Filetype gitcommit setlocal spell textwidth=72s
```
