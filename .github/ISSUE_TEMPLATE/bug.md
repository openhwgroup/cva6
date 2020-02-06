# Template for CORE-V-Verif Issues
Verification code can have just as many bugs (issues) as RTL.  So we treat
verification bugs the same way we treat RTL bugs and track them both
with GitHub issues.

Please use this file as a template for filing issues against any of the
code in this repository.
<br>**Hint**: click on the edit symbol (looks like a pencil) and then
edit the markdown text.
<br>**Note**: do _not_ create bugs against the RTL here.  Go to the
appropriate GitHub repository (e.g. https://github.com/openhwgroup/core-v-cores)
and generate your issue there.

## Bug Title
A clear and concise description of what the bug is.

### Type
Indicate whether the type of problem you found:
* Compile error (hopefully nobody has committed anything that doesn't compile!)
* Functionally incorrect behavior
* Confusing or extraneous status or error messages
* Code style violations (e.g. using $display instead of `uvm_info() in a UVM environment)
* Other.

### Steps to Reproduce
Please provide:
1. URL to branch that exhibits the issue.
2. Command line  (e.g. `make xrun-riscv-compliance`)
3. Logfile and/or wave-dump info (screen shots can be useful)

### Additional context
Add any other context about the problem here.
