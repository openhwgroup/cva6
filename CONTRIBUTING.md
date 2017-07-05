# Styleguides

## Coding Style

- Keep the files tidy. No superfluous line breaks, align ports on a common boundary.
- Don't use tabs, use spaces.
- Use 4 spaces to open a new indentation level.
- All signal and module names should be lower case with underscores as whitespace replacements (e.g.: `fetch_busy`).
- Instantiation of modules should be postfix with `_i`, e.g.: `prefetcher_i`
- For port definitions keep a post-fix direction (`_o`, `_i`).
- For active low signals put an additional (`_no`, `_ni`).
- Denote output of ff with `_q` and the input with `_n`.
- Name dedicated signals wiring `module A` (output) with `module B` (input) `signal_a_b`
- Do not use CamelCase!
- Do not put overly large comment headers. Nevertheless, try to structure your HDL code, e.g.:
```
  // ------------------------------------
  // CSR - Control and Status Registers
  // ------------------------------------
```

## Git Considerations

- Do not push to master, if you want to add a feature do it in your branch
- Separate subject from body with a blank line
- Limit the subject line to 50 characters
- Capitalize the subject line
- Do not end the subject line with a period
- Use the imperative mood in the subject line
- Use the present tense ("Add feature" not "Added feature")
- Wrap the body at 72 characters
- Use the body to explain what and why vs. how
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
