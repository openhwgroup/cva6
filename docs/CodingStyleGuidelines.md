<!---
// Copyright 2015, 2016 Brian Hunter
//
// Original text extracted from "Advanced UVM", (c) 2015, 2016 Brian Hunter,
// who owns all the rights thereto.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
--->


# CORE-V-VERIF Coding Guidelines for SystemVerilog/UVM code

> "Code is read much more often than it is written"
>
> ~ pep8

Every organization — even a company of one — should have a set of coding guidelines if for no other reason than to maintain consistency and readability.
These guidelines are specific to code developed for design verification using SystemVerilog and the Universal Verification Methodology.
For RTL code, the OpenHW Group uses the [the lowRISC Verilog coding style guide](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md),
and this may also be used for CORE-V-VERIF code when implementing testbench components from SystemVerilog modules.

The original text of these guidlines is extracted, with permission, from *Advanced UVM*, (c) 2015, 2016 Brian Hunter, who owns all the rights thereto.

1. **General Conventions**

This document uses specific verbs to have specific meaning that is similar, but not identical to, that which is used by the [IEEE Standards Style Manaul](https://mentor.ieee.org/myproject/Public/mytools/draft/styleman.pdf) (section 9).<br>
* **Shall** indicates a mandatory requirement.
* **Should** indicates a recommendation may be used interchangibly with the verb **Recommended**.
* **May** indicates a permissible action, and is sometimes used to suggest ways to fulfill a recommendation.
* **Can** indicates possibility and/or a capability.

1.1. **Common Header**

1.1.1. All files shall begin with a common header. The initial author, filename, and a brief description shall be filled out as basic documentation.
All headers shall have an SPDX-License-Identifier comment line such as below:
```
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
```
Please contract the OpenHW Group for a list of licenses we can accept.


1.2. **Indentation**

1.2.1. All SystemVerilog files shall have a common indentation level of 3 spaces.

1.2.2. TABs shall **never** be used.

1.3. **Naming Conventions**

1.3.1. All identifiers shall use `lower_case_with_underscores`, except for the following:

1.3.2. All parameters and `` `defines `` shall use `UPPER_CASE_WITH_UNDERSCORES`.

1.3.3. *Recommended*: Macros may use `lower_case_with_underscores` if they provide procedural code.

Examples:

```v
`cmn_dbg(300, ("Hello, world"))
`FOO_NUM_DAVES(dave_mode)
```

1.3.4. *Recommended*: All method arguments should use `_preceded_by_underscore`.

1.3.5. *Recommended*: When accessing member variables and methods within the class scope, the `this` handle may be used to distinguish class members from function variables with automatic scope.

1.4. **File Structure**

1.4.1. *Recommended*: All files shall contain one and only one class, interface, package, or module. Cases where items are very small and can be neatly grouped together may be placed in the same file (for example, sequence libraries).

Files should contain the following, in order:

  1. Common header (see Common Header).
  2. Include guards (except for files containing packages or modules).
  3. `` `includes ``. Include all files that this file requires. For most cases, cyclical imports are not a problem in SystemVerilog, so let the compiler figure it out. There are some cases, however (see Handling Cyclical Includes).
  4. The `class`, `interface`, `package`, or `module`.
  5. `` `endif `` to finish the include guard.


1.5. **File Naming**

1.5.1. The following chart details how files should be named with respect to what they contain.

**Table 1: File and Class Naming Conventions**

| Location             | Item Type           | Item Name           | File Name              |
| -------------------- | ------------------- | ------------------- | ---------------------- |
| `verif/vkits/<vkit>` | Package             | `<vkit>_pkg`        | `<vkit>_pkg.sv`        |
| `verif/vkits/<vkit>` | Interface           | `<iface_name>_intf` | `<iface_name>_intf.sv` |
| `verif/vkits/<vkit>` | Class               | `<classname>_c`     | `<vkit>_<classname>_c` |
| `verif/vkits/<vkit>` | Flist File          | N/A                 | `<sim>.flist`          |
| `verif/<tb>`         | Top-level Testbench | `<tb>_tb_top`       | `<tb>_tb_top.sv`       |
| `verif/<tb>`         | Class               | `<classname>_c`     | `<classname>.sv`       |
| `verif/<tb>`         | Flist File          | N/A                 | `<sim>.flist`          |
| `verif/<tb>/tests`   | Base Test           | `base_test_c`       | `base_test.sv`         |
| `verif/<tb>/tests`   | Test                | `<testname>_test_c` | `<testname>.sv`        |
|                      |                     |                     |                        |

The `<sim>.flist` allows different flist file for each simulator used by the company, should they be necessary.

1.6. **Include Guards**

1.6.1. Use `` `include `` guards for files containing classes and interfaces.

1.6.2. Package files will be compiled directly via the flist and do not need `` `include `` guards.

1.6.3. When using include guards, the name of the include guard should be the "seasoned" version of the file name, where leading and trailing double-underscores are added to the capitalized filename.

For example:

```v
foo_drv.sv:

`ifndef __FOO_DRV_SV__
`define __FOO_DRV_SV__
 ...
`endif // __FOO_DRV_SV__
```

1.7. **Type Suffixes**

1.7.1. All declared types have a short suffix as described in the table below.

**Table 2: SystemVerilog Type Suffixes**

| Suffix  | Type                        | Suffix   | Type                  |
| ------- | --------------------------- | -------- | --------------------- |
| `_c`    | Classes                     | `_t`     | Typedefs, Misc. Types |
| `_e`    | Enumerated Types            | `_s`     | Structs               |
| `_pkg`  | Packages                    | `_cb`    | Clocking Blocks       |
| `_intf` | Interface  Types            | `_mp`    | Modports              |
| `_i`    | Interface Instances         | `_cnstr` | Constraints           |
| `_vi`   | Virtual Interface Instances | `_cg`    | Covergroups           |
|         |                             |          |                       |

The purpose of these suffixes is:

* To help quickly identify what type an identifier represents; and
* To help differentiate between the type and the instance names, which otherwise would often be the same. Some tools would not permit the following, nor would it be particularly readable:

```v
// BAD!
foo foo;
```

Inventing a meaningless prefix can just create greater confusion and inconsistency:

```v
// BAD!
foo my_foo;
```

Instead, the types themselves shall have the suffixes from Table 3. So, the above example of instantiating a foo class would be:

```v
// GOOD!
foo_c foo;
```

1.8. **UVM Suffixes**

1.8.1. In addition to the above suffixes, extensions to standard UVM classes shall be appended with short identifiers to help clearly distinguish them from one another, as described in Table 3.

**Table 3: UVM Type Suffixes**

| Suffix     | UVM Type          | Suffix    | UVM Type                |
| ---------- | ----------------- | --------- | ----------------------- |
| `_env_c`   | `uvm_env`         | `_vsqr_c` | `virtual uvm_sequencer` |
| `_test_c`  | `uvm_test`        | `_seq_c`  | `uvm_sequence`          |
| `_agent_c` | `uvm_agent`       | `_item_c` | `uvm_sequence_item`     |
| `_drv_c`   | `uvm_driver`      | `_vseq_c` | `virtual uvm_sequence`  |
| `_mon_c`   | `uvm_monitor`     | `_cseq_c` | Chaining sequence       |
| `_sqr_c`   | `uvm_sequencer`   | `_sb_c`   | `uvm_scoreboard`        |
| `_csqr_c`  | Chained Sequencer | `_cb_c`   | UVM callback classes    |
|            |                   |           |                         |

1.8.2. Instantiations of UVM classes will use the same suffixes as mandated by 1.8.1.

For example, the instance of `foo_agent_c` is `foo_agent`.

1.8.3. *Recommended*: The suffix alone should be the full name (removing leading underscore) *if it is not ambiguous*.

For example, if `foo_agent_c` is the only agent within the `foo` package, then it should simply be called `agent_c`.

1.8.4. *Recommended*: TLM instances should have the following suffixes to help identify them:

**Table 4: TLM Instance Suffixes**

| Suffix    | TLM Instance |
| --------- | ------------ |
| `_port`   | TLM Port     |
| `_export` | TLM Export   |
| `_imp`    | TLM Imp      |
| `_socket` | TLM2 Socket  |
|           |              |

1.9. **Comments**

1.9.1. As a goal of these guidelines is to promote reuse through the use of consistent methodologies, code should be consistently documented. These guidelines advocate the use of a documentation generator that produces readable, searchable content that can be accessible by all. The NaturalDocs generator is the one used by UVM and is recommended by these guidelines.

1.9.2. Documentation shall be consistent with the [NaturalDocs][1] documentation generator, as described on its website.

1.9.3. The overarching purpose of comments is not to remind the individual who wrote the code of what *she* wrote, but to educate *others*. Therefore, it is important to document the code to *explain the code for other readers*.

1.9.4 *Recommended*: Classes, fields, methods, types, interfaces, and any other APIs that should be understood by others using your code should be documented thoroughly.

1.9.5. *Recommended*: General README text of a vkit should be placed in the vkit's package file, in the About section of the header.

For example:

```v
/* About: foo Package

 These are the details on the foo vkit.
 Here's how the vkit is intended to be used...

  *************************************************************************/
```

1.10. **Code blocks**

All code blocks shall be delimited with begin..end keywords.

2. **Verification Kits**

Note: the concept if `Verification Kits` as defined in the `Advanced UVM` textbook is not explicitly supported in CORE-V-VERIF.
A future reversion of these guidelines will update this section to explain how vkits are implemented in this repo.

2.1. **Organization**

Verification code is to be organized into two types of verification directories within the project: testbench directories and vkits.

```sh
chip/
    verif/
        dave/
            tests/
        foo/
            tests/
        ...
        vkits/
            dave/
            pcie/
            foo/
            uvm/
            ...
    rtl/
        ...
    ...
```

The testbench directories (`verif/dave`, `verif/foo`, etc.) contain the testbench code for each block. These are the working directories where compilation and simulation are performed. The tests directories within each testbench directory contain the base test file and tests that extend the base test.

The `verif/vkits` directory contains the reusable verification kits. These kits do not stand alone and are not meant to be compiled within their directories (exceptions can be made for simple package-level tests for standalone testing of packages.) A kit gets compiled when it is used by a testbench.

The question to ask when deciding whether some code should be in a vkit or a testbench directory is, _"Will this code be used (or, potentially used) in more than one testbench?"_ If the answer is "yes," then it should be in a vkit directory.

2.1.1. Code that resides in a testbench directory shall not use code from another testbench directory. Only code from vkit directories shall be visible to a testbench.

Compared to the vkits directories, testbench directories should be relatively thin on code content. Examples of verif directory contents:

* Testbench hook up file, tb_top.sv.
* Testbench-only sequences.
* Testbench tests.

2.2. **Verification Kit Dependencies**

Testbench directories typically depend on one or more vkit packages to provide the needed code and on one or more RTL directories to provide the RTL that is being verified. These vkit packages in turn may depend on other vkit packages. At the risk of stating the obvious, these dependency relationships must form a directed graph; there must be no circular dependencies between packages.

**Kit Prefixes**

2.2.1. Each verification kit shall have a unique identifier that shall be used as a prefix for file names, package names, interface names, and macros.

Using a unique prefix prevents name clashes when multiple verification packages are used together on a project.

2.2.2. The prefix shall not contain any underscore ("_") characters, as the first underscore in a name marks the end of the prefix portion of that name.

2.2.3. *Recommended*: Limit prefixes to 3-4 characters for readability.

2.3. **Directory and File Names**

2.3.1. All of the SystemVerilog files that make up a verification kit shall reside under the directory `verif/vkits/<prefix>`, where `<prefix>` is the kit prefix, and they shall have names starting with "`<prefix>_`" (note that this is consistent with the guidelines in File Naming; note also the underscore.)

For example, the FOO kit might contain these files:

```sh
verif/vkits/foo/
   mentor.flist
   foo_agent.sv
   foo_drv.sv
   foo_intf.sv
   foo_item.sv
   foo_macros.sv
   foo_mon.sv
   foo_pkg.sv
   foo_sqr.sv
   vcs.flist
```

**2.4 Packages and Classes**

SystemVerilog Packages are intended to provide a scope to contain declarations that can be shared between other packages. In this way, they are similar to C++ namespaces.

Packages make up the heart of most vkits. All class definitions, typedefs, enumerated type definitions, and global variables and constants that are part of a vkit shall be defined inside of a package (basically, everything except modules, interfaces, and macro definitions, which are not permitted by the language to be defined inside of packages.)

2.4.1. All class definitions, typedefs, enumerated type definitions, and global variables and constants that are part of a vkit shall be defined inside of a package.

Package names must be prefixed with `<prefix>_`, where `<prefix>` is the vkit prefix. Typically, a vkit will contain a single package definition named `<prefix>_pkg`.

**Package File Structure**

2.4.2 A package shall be defined for each vkit. It shall be named `<prefix>_pkg` and shall be defined in the `<prefix>_pkg.sv` file.

_Macro Includes_

2.4.3. *Recommended*: The package file should first `` `include `` any macro definitions from itself and other vkits used by this package.

These `` `includes `` happen before the package declaration:

```v
// common header here
`include "uvm_macros.svh"
`include "cmn_macros.sv"
`include "foo_macros.sv"

package foo_pkg;
   ...
endpackage : foo_pkg
```


_Imported Packages_

2.4.4. *Recommended*: After the package declaration, the package shall then import the UVM package using the wildcard notation:

```v// common header here
`include "uvm_macros.svh"
`include "cmn_macros.sv"
`include "foo_macros.sv"
package foo_pkg;
   import uvm_pkg::*;
   ...
endpackage : foo_pkg
```

2.4.5. uvm_pkg is the only package that a vkit package shall import.

An import of this type eliminates the need to specify the scope everywhere (`uvm_pkg::uvm_driver` can be shortened to just uvm_driver, for example). However, to prevent namespace pollution, `uvm_pkg` is the **only** package that will be permitted to be imported with wildcard notation. All other package dependencies shall be resolved explicitly with use of the scope name. This reliance will be handled by ordering in an `flist` file (see 2.7 Flist File).

2.4.6. There shall be no cyclical requirements between packages.

If there is a cyclical requirement, then it **must** be eliminated.

_Package Includes_

All of the contents of a package must be compiled as a single file. Since all of the `class`, `typedef`, and global variable definitions that make up a package are defined in separate files, the only way that they can be compiled as a single file is to `` `include `` them in the package file.

2.4.7 *Recommended*: After prerequisite imports, the package should then `` `include `` all of the files that define the classes, typedefs, global variables, etc. in the package.

The order in which these `` `includes `` occur should be irrelevant. In fact, they may be in alphabetical order or they may be in the chronological order in which they were created. So long as the files themselves used include guards and they include their own dependencies, the simulator will determine things correctly.

The final package example is as follows:

```v
// common header here
`include "uvm_macros.svh"
`include "cmn_macros.sv"
`include "foo_macros.sv"

package foo_pkg;
   import uvm_pkg::*;
   `include "foo_agent.sv"
   `include "foo_drv.sv"
   `include "foo_item.sv"
   `include "foo_mon.sv"
   `include "foo_sqr.sv"
   ...
endpackage : foo_pkg
```

**Class Definitions**

As per 1.4.1. and 1.4.2., each class should be in its own separate file. (See File Structure.)

2.4.8. The name of the class should not use the vkit prefix at the beginning of its name.

Because the name of the class is contained within the namespace provided by the package, there is no possibility of name collisions when vkits are used together in a testbench.

2.4.9. The name of the file containing the class shall have a name starting with `<prefix>`. (See Directory and File Names.)

The file name should be `<prefix>_<class_name_without_c>.sv`.

From other classes within `foo_pkg`, the class can be referred to as `agent_c`. From outside of the package, it must be referred to as `foo_pkg::agent_c`.

__Handling Cyclical Includes__

One example of a cyclical include is a sequencer and a sequence library. The sequencer class may need to know about the sequences available to it if, for example, it needs to start one of the sequences on its own. The sequences in the sequencer library need to know about the sequencer class to define the `p_sequencer` variable as a reference to the sequencer class. This is an example of a cyclical import problem.

In cases such as this, because SystemVerilog compilers support late binding, it is often sufficient to create a forward `typedef` of the sequencer in the sequence library file:

```v
typedef class foo_sqr_c;
```

See the SystemVerilog standard 1800-2012, section 6.18, for more information on forward typedefs.

2.5. **Interface Definitions**

Interfaces cannot be defined inside of a package, so they are compiled separately.

2.5.1. The name of the interface shall be `<prefix>_<name>_intf`, where `<prefix>` is the kit prefix.

2.5.2. *Recommended*: The name of the file containing the interface definition should be `<prefix>_<name>_intf.sv`.

2.5.3. *Recommended*: `<name>_` is unnecessary if there is only one interface defined in the verification kit. This alternative also applies to 2.6.1. (See File Naming.)

An interface is its own compilation unit, so it must include macro files from itself and any other verification kits on which it depends.

2.6. **Macro Definitions**

2.6.1. ll macro names shall be prefixed with `<prefix>_` or `<PREFIX>_`, where `<prefix>_` is the vkit prefix.

2.6.2. If a vkit provides macros for use outside the vkit, there shall be a file named `<prefix>_macros.sv` that, when `` `included ``, defines all of the provided macros.

2.6.3. Files whose purpose is to provide a vkit's macros as described in 2.7.2. shall only contain macros.

2.6.4. Multiple macro definition files are allowed; the `<prefix>_macros.sv` file must `` `include `` them all.

2.6.5. All macro definition files shall use include guards.

2.6.6. The macro definitions file should not be in the package's flist. Instead, this file gets included by any other package that is reusing this package.

2.6.7. *Recommended*: No semicolons are used when calling macros (don't terminate macros with semicolons, put the semicolon in the macro definition).

These rules are necessary to enable the single file compilation unit model.

2.7. **The Flist File**

2.7.1. Each vkit shall have an flist file that can be specified with the dash-f (`-f`) option on the simulator command line.

2.7.2. The flist file shall be named `<sim>.flist`, where `<sim>` is the name of the simulator being used.

The simulation requirement is only necessary when different simulators are used, and when these simulators require different command-line arguments. For example, the PAT package might have an flist file named `vcs.flist`, which would contain the following:

```sh
verif/vkits/foo/vcs.flist:
+incdir+../../verif/vkits/foo
../../verif/vkits/foo/foo_intf.sv
../../verif/vkits/foo/foo_pkg.sv
```

Some things to notice:

* The package definition (`foo_pkg.sv`) is specified, but class definition files are not. Class definition files are already `` `included `` by the package definition file.

* A `+incdir` is specified to point to the `foo` vkit directory. This is necessary for two reasons:
  * Includes in `foo_pkg.sv` need to find their files; and
  * Verification code that depends on the `PAT` vkit must include `foo_macros.sv`, and those `` `includes `` need to find the `foo_macros.sv` file.
* The `foo_macros.sv` file is not listed in the flist file. It is included by each compilation unit that needs it. (See Using a Verification Kit.)
* Interface definition files are specified separately from the top level package file.

2.8. **Using a Verification Kit**

2.8.1. Testbenches dependent on a vkit must include the vkit's `<prefix>_macros.sv` file (if it exists) at the beginning of each module and interface file.

2.8.2. Every compilation unit that requires the vkit's macros must include the `<prefix>_macros.sv` file.

This enables a single file compilation unit model of SystemVerilog compilation. Include guards in the `<prefix>_macros.sv` file will prevent it from being compiled multiple times when the multiple file compilation unit model is used.

2.8.3. Testbenches dependent on a vkit must add the vkit's flist file to the testbench Makefile.

When another vkit needs to use a vkit, it must do the following:

2.8.4. When vkit [A] depends on vkit [B], [A] must include the vkit [B] `<prefix>_macros.sv` file (if it exists) at the beginning of each package and interface file.

2.8.5. When vkit [A] depends on vkit [B], the testbench must compile [B] first by specifying its flist file to the simulator in the proper order.

SystemVerilog does not support "late binding" for packages, so the dependent package must be compiled **after** the package that it depends upon.

A verification kit represents an atomic unit of reuse.

2.8.6. Never directly include files from a vkit in another package or in the testbench.

3. **Classes**

3.1. **Class Headers**

SystemVerilog provides the ability to supply class prototypes and header files. In C/C++ these provide a means to perform incremental compilation. The other benefit of header files in languages such as C/C++ is that they expose a programming interface while hiding the implementation details. Header files, though, come at the expense of code bloat and the violation of the "Don't Repeat Yourself" rule.

SystemVerilog does not provide a true incremental compilation benefit from header files, though. And automatically hiding the implementation details of methods is trivial in editors such as emacs (when a strict indentation policy
is followed) or other modern editors.

3.1.1. Header files shall not be used for SystemVerilog classes. Instead, all fields and methods shall be fully specified in the class definition.

3.2. **Order of Appearance**

3.2.1. *Recommended*: A typical class definition shall have its sections appear in the following order.

  1. Class Declaration
  2. Typedefs, Enumerations
  3. UVM Object/Component/Field Macros
  4. Configuration Fields. Constraints on random fields shall be kept locally with the fields.
  5. TLM Interfaces. Ports, exports, imps, and sockets.
  6. Other Class Fields
  7. New Function and Phase Methods. Starting with the `new()` function, the phase methods should appear in chronological order. Empty methods may appear or may be eliminated.
  8. Other Class Methods
  9. `endclass`

The purpose of this ordering is to expose the programming interface as early in the class definition as possible, and to logically show the order of UVM phases in the methods. Here is an example of a simple class definition, with
some details hidden:

```v
class foo_drv_c extends uvm_driver;
   //****************************************************************************************
   // Group: Types

   // Types should be defined first
   typedef bit [31:0] dword_t;

   `uvm_component_utils_begin(foo_drv_c)
      `uvm_field_enum(uvm_active_passive_enum, active, UVM_COMPONENT)
   `uvm_component_utils_end

   //****************************************************************************************
   // Group: Configuration Fields

   // var: is_active
   // Delay between transactions (in clocks)
   uvm_active_passive_enum active = UVM_ACTIVE;

   //****************************************************************************************
   // Group: TLM Interfaces

   // var: trans_port
   // Transmits all driven transactions to listeners
   uvm_analysis_port#(trans_c) trans_port;

   //****************************************************************************************
   // Group: Fields

   // var: delay
   // Delay between driven transactions (in clocks)
   rand int delay;
   constraint delay_cnstr {
      delay inside {[0:10]};
   }

   //****************************************************************************************
   // Group: Methods
   function new(string name="foo_drv",
                uvm_component parent=null);
      super.new(name, parent);
      ...
   endfunction : new

   ////////////////////////////////////////////
   // func: build_phase
   virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      ...
   endfunction : build_phase

   ...
endclass : foo_drv_c
```

3.3. **Class Properties**


In SystemVerilog, class member fields are known as properties (see SystemVerilog LRM 1800-2012, section 8.2).

3.3.1. *Recommended*: Class properties shall be named meaningfully so that readers understand their purpose. Single letter member names such as `i` or `k` shall not be permitted.

3.3.2. *Recommended*: Class properties shall be named with `lower_case_with_underscores` style.

3.3.3. *Recommended*: Class properties shall have at least one line of documentation describing their purpose.

3.3.4. *Recommended*: Do not label random parameters "`local`" because it prevents randomization outside of the class using a "`with`" clause.

3.4. **Methods**

Class tasks and functions are collectively known as methods.

3.4.1. All class methods shall have at least one line of documentation to describe their purpose. The lone exception is methods such as new or standard UVM methods such as `build_phase`, `run_phase`, or `end_of_elaboration_phase` whose purposes and arguments are implicitly understood. In such cases, the author may provide documentation.

3.4.2. Class method arguments shall be documented when their purpose is not immediately clear.

3.4.3. Class method arguments shall be named with `_preceded_by_underscore` style.

3.4.4. *Recommended*: The algorithm of a class method should be documented when it is considered complex.

3.4.5. *Recommended*: A differentiation must be made to distinguish between class and automatic scope, and this must be consistent throughout a vkit.

3.5. **Method Calls**

Although SystemVerilog permits the parentheses to be missing in method calls without arguments

3.5.1. All method calls shall have parentheses to distinguish them from variables.

For example, don't do the following:

```v
int smallest = array.min;
```

Instead:

```v
int smallest = array.min();
```

SystemVerilog allows keyword-arguments, which help with readability when the order of arguments is not implicitly known.

3.5.2. *Recommended*: When the number of arguments exceeds two or three, method calls should be made with keyword-arguments to enhance readability.


For example:

```v
send_command(._transaction(trans),
             ._delay_ps(my_delay),
             ._override(1'b0),
             ._interleave(1'b1),
             ._send_with_errors(1'b0));
```

Is much more readable than:

```v
send_command(trans, my_delay, 0, 1, 0);
```

3.5.3. If the code within a package follows 1.3.5, all method calls within class scope in that package should follow 1.3.5.

3.6. **Inheritance**

3.6.1. *Recommended*: Do not redefine variables in derived classes.

3.6.2. If the base definition of member is `virtual` then the extended version should also use the `virtual` keyword.

4. **Testbench Hierarchy**

All testbenches should be organized in a similar fashion. Doing so helps ensure that engineers are using "best-practices" and facilitates merging of testbench components into higher-level testbenches.

UVM's configuration mechanism permits maximum flexibility by allowing higher-level components to configure lower-level ones. In order to use this, however, the testbench must be organized properly, and all configurable `uvm_objects` must be new'ed by using the `::type_id::create()` mechanism.

4.1.1. Testbench authors shall organize their testbenches in the following manner:

* There shall be one test which is the root of all other tests, and it shall be known as `base_test_c`. It shall inherit from `uvm_test` and live in the `tests/base_test.sv` file.
* The base test instantiates the environments and various other agents from the vkits it depends upon. Usually, most of this knitting together is already done in a reusable testbench vkit, in which case the base test shall instantiate this.
* The base test shall configure the environment and its components in the most typical manner for all tests. The goal of the base test is to consolidate the most typical configurations that all tests share.
* The base test shall instantiate both the register block(s), `reg_block_c`, and any block configuration classes, `cfg_c`.
* All tests shall inherit from the `base_test_c` class, or from another test which inherits from `base_test_c`. During their build phases, tests may call the `uvm_config_db::set()` configuration function to modify the testbench as necessary.
* The `global_pkg::env_c` environment is instantiated in the global scope, but must be created by the testbench's `base_test_c`, with a parent of null (`uvm_top`). Instantiating it in the global scope allows it to be referred to by any package which is compiled after it.

4.2. **Top-Level Testbench Module**

4.2.1. The very top of the testbench hierarchy is the verilog module named `tb_top`.

In this module, the DUT is instantiated (or, a wrapper module that instantiates the DUT), interfaces and other modules are instantiated, and other miscellaneous logical connections are made.

4.3. **Base Tests**

4.3.1. The testbench's environment is laid out by the `base_test_c` class, which all subsequent tests shall extend.

4.3.2. The base test shall instantiate the random configuration class(es), the register block(s), the environment(s), the clock driver(s), the reset driver(s), and any other components that will live at the base test level.

4.3.3. The base test shall create all objects in 4.3.1. in the correct order.

4.3.4. The base test shall randomize the configuration class and the register block, and push these into the configuration database.

4.3.5. The base test shall start any basic sequences used by all subsequent tests, such as the configuration sequence.

4.3.6. The base test shall contain a virtual function named `randomize_cfg()` which shall call randomize on the base test and all of its random variables.

4.4. **Configuring Virtual Interfaces**

4.4.1. *Recommended*: The `tb_top` module shall instantiate all interfaces that connect to the DUT and provide virtual interfaces that point to these interfaces to the verification environment via the UVM resource database.

4.4.2. *Recommended*: Use the macro `` `cmn_set_intf `` to push virtual interface handles into the resource database.

```v
module tb_top;
   foo_intf foo_i;

   blk_wrapper dut_wrapper(.foo_intf  (foo_i));

   function void pre_run_test();
      `cmn_set_intf(virtual foo_intf, "foo_pkg::intf", "foo_vi", foo_i);
   endfunction : pre_run_test

   initial begin
      pre_run_test();
      run_test();
   end
endmodule : tb_top
```


In this example, `foo_pkg::intf` is the scope, and `foo_vi` is the name, under which the virtual interface is stored in the UVM resource database.

Within the module `tb_top`, the structure of the UVM component hierarchy is not necessarily known, which is why the UVM configuration database is not used. Instead, virtual interfaces are put into the UVM resource database, essentially making them globally visible to all UVM components.

In the example above, the scope name ("`foo_pkg::intf`") is a name that is required by the foo verification kit. (The `FOO` vkit is hardcoded to look for its interfaces using that scope name.) Note that the scope name starts with `<prefix>_pkg`, as required.

The name ("`foo_vi`" in the example) is a name that is provided by the `tb_top`. The `base_test_c` has knowledge of these names, since it is part of the same testbench as `tb_top`.

The `base_test_c` knows the UVM component hierarchy, so it can provide the interface names to the appropriate UVM components through the UVM configuration database:

```v
class base_test_c;
   foo_pkg::env_c foo_env;

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      foo_env = foo_pkg::env_c::type_id::create("foo_env", this);
      uvm_config_db#(string)::set(this, "foo_env", "intf_name", "foo_vi");
      …
```

**Requirements for Components**

The above method for passing virtual interfaces to the verification environment imposes some requirements on the UVM components:

4.4.3. Components only get handles to virtual interfaces from the UVM resource database.

4.4.4. The component defines a string configuration field that is used to look up the virtual interface (`intf_name`, by custom).

4.4.5. The vkit defines a scope name under which all virtual interfaces for all instances of the verification kit are stored.

4.4.6. *Recommended*: Use the macro `` `cmn_get_intf `` to pull virtual interface handles from the resource database.

4.4.7. *Recommended*: Components should use the `` `uvm_component_utils `` macros to declare configurable variables which perform database lookups during the build phase. Such variables should have the `UVM_COMPONENT` flag attached.

Extending the example from above, the `foo_pkg::env_c` class has a configuration field called "`intf_name`". Wherever a FOO class needs to get the virtual interface to a `foo_intf`, it knows to look in the UVM resource database under the scope `foo_pkg::intf`, and the name specified by the `intf_name` field. If the interface was not registered or was registered with a different name, a fatal error prints out and reports that `<UNSPECIFIED>` is not found in the database.

```v
class env_c;
   `uvm_component_utils_begin(env_c)
      `uvm_field_string(intf_name, UVM_COMPONENT)
      //...

   string intf_name = "<UNSPECIFIED>";
   virtual foo_intf foo_vi;

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `cmn_get_intf(virtual foo_intf, "foo_pkg::intf", intf_name, foo_vi)
      //...
```

The `UVM_COMPONENT` macro is configured with `UVM_NOCOPY`, `UVM_NOCOMPARE`, and `UVM_NOPACK` to eliminate automated code bloat.

5. **Random Configurations**

A testbench's random configuration variables may control how the testbench is built out, how the DUT is configured, and how random traffic is generated.

Testbench random configuration variables should take advantage of SystemVerilog's powerful constraints and functional coverage as much as possible.
They should also be consistently declared from testbench to testbench.

Tests should constrain random variables through inheritance. Child tests can then control the environment with minimal effort.

5.1. **Creation, Instantiation, and Randomization**

5.1.1. Each verification kit shall create a configuration class which derives from `uvm_object`.

5.1.2. The name of a vkit’s top-level configuration class shall be `cfg_c`.

5.1.3. When associated with one, the configuration class shall instantiate a randomized version of the `reg_block`, but shall not `::create` or `new` it.

5.1.4. The top-level configuration class(es) shall be instantiated by the `base_test_c` class.

5.1.5. The base test shall randomize the configuration block, and the register block along with it, before creating the rest of the environment.

```v
class cfg_c extends uvm_object;
   `uvm_object_utils_begin(blk_pkg::cfg_c)
      `uvm_field_object(reg_block, UVM_DEFAULT)
      `uvm_field_int(my_var,       UVM_DEFAULT)
   `uvm_object_utils_end

   // var: reg_block
   // randomized register block
   rand reg_block_c reg_block;

   // var: my_var
   // random variables declared here as rand
   rand int my_var;

   // base constraints go here, too
   constraint my_var_cnstr {
      my_var inside {[0:4]};
   }
endclass : cfg_c
```

5.1.6. Classes which need to peek or poke into the configuration class shall contain a reference to the class, and not a clone.

```v
class foo_agent_c extends uvm_agent;
   `uvm_component_utils_begin(foo_agent_c)
      `uvm_field_object(cfg, UVM_COMPONENT | UVM_NOPRINT)
   `uvm_component_utils_end

   // cfg is never new'ed. instead, it is pulled out of the configuration database as a reference
   cfg_c cfg;

   virtual void function build_phase(uvm_phase phase);
      super.build_phase(phase);  // <-- cfg filled in!
   endfunction : build_phase
endclass : foo_agent_c
```

5.1.7 Randomization results shall be checked and failures shall result in a fatal error

```v
if (!my_vseq.randomize()) begin
    `uvm_fatal("TEST", "Cannot randomize my sequence")
end
```

5.1.8 Use of random number system functions and methods
<br>
Use of $urandom(), $urandom_range(), $random(), $dist_uniform(), $dist_normal(),
$dist_exponential(), $dist_poisson(), $dist_chi_square(), $dist_t() and
$dist_erlang() should be avoided because members randomized with these calls
cannot be constrained.

This rule may be waived if the randomization of a member using one of these system methods is controlled by a member that is constrainable.
For example:

```
    if (cfg.drive_random_rdata) begin
       slv_mp.drv_slv_cb.rdata <= $urandom();
    end
```

5.2. **Test Constraints**

Tests are greatly simplified and highly re-usable when they are primarily composed of configuration and constraint overrides.
By instantiating the configuration class as a random field of the base test, derivative tests can add their own constraints and/or disable the base constraints.
Disabling constraints is best done by overriding the `randomize_cfg()` function.

```v
class my_test_c extends exer_test_c;
   `uvm_component_utils(my_test_c)
   constraint my_test_cnstr {
      foo_cfg.my_var == 5;
   }

   // disable a constraint in exer test
   function void randomize_cfg();
      foo_cfg.my_var_cnstr.constraint_mode(0);
      super.randomize_cfg();
   endfunction : randomize_cfg

   ...
```

5.3. **Functional Coverage**

5.3.1. CFG (knobs) classes shall implement their own functional coverage covergroups.

5.3.2. Agents, including drivers and monitors, shall implement their own functional coverage covergroups where useful.

5.3.3. Every class that has any coverage shall include a class variable `coverage_enable` to control coverage functions.

5.3.4. Classes derived from `uvm_component` will have this set correctly via the `uvm_config_db`. An example is shown below.

```v
class agent_c extends uvm_agent;
   `uvm_component_utils_begin(dave_pkg::agent_c)
     `uvm_field_int(coverage_enable, UVM_COMPONENT)
  `uvm_component_utils_end

   //--------------------------------------------------------------------------
   // Group: Configuration Fields

   // Field: coverage_enable
   // If 1, then functional coverage will be collected in this agent.
   bit coverage_enable = 0;
```

5.3.5. Classes derived from `uvm_object` will need to set the `coverage_enable` value by reading the `uvm_resource_db` during construction.

An example is shown here:

```v
// class: cfg_c
// THS vkit's cfg class
class cfg_c extends uvm_object;
   `uvm_object_utils_begin(pat_pkg::cfg_c)
      `uvm_field_int(coverage_enable, UVM_DEFAULT)
   `uvm_object_utils_end

   //----------------------------------------------------------------------------------------
   // Group: Methods
   function new(string name="cfg");
     super.new(name);
     uvm_resource_db#(int)::read_by_name("uvm_root", "coverage_enable", coverage_enable, this);
     if(coverage_enable) begin
        cg = new();
        cg.set_inst_name({get_full_name(), ".cg"});
     end
  endfunction : new

   //----------------------------------------------------------------------------------------
   // Group: Functional Coverage
   covergroup cg;
      ...
   endgroup : cg
```

5.3.6. Coverage subscriber construction during the build phase for `uvm_components`, or during the construction using the `new()` method for `uvm_objects` shall be conditional on the class variable `coverage_enable`.

5.3.7. Coverage subscribers for agents or other classes which will be instantiated more than once in any testbench shall set the name from the instance name to facilitate per instance monitoring.

The following code illustrates these rules:

```v
// Class: foo_cov_coll_c
// Object for collecting functional coverage on <foo_c>.
// We could have defined the covergroup in the <foo_c> class, but defining
// it in a separate, persistent uvm_component gives us the ability to collect
// sensible per-instance coverage, since each
// <foo_cov_coll_c> is an instance for coverage purposes, rather
// than each <foo_c>.
class foo_cov_coll_c extends uvm_subscriber;
   `uvm_component_utils(coverage_collector_c)

   //--------------------------------------------------------------------------
   // Group: Fields

   // Temporary variable to hold a req for coverage sampling.
   req_c sample_req;

   //--------------------------------------------------------------------------
   // Group: Covergroup *cg*
   covergroup cg;
      ...
   endgroup

   ////////////////////////////////////////////
   // func: new
   function new(string name="cov_coll",
                uvm_component parent=null);
      super.new(name, parent);

      // Create the covergroup and name the instance after the UVM component
      // hierarchy.
      cg = new();
      cg.set_inst_name(get_full_name());
   endfunction : new

   ////////////////////////////////////////////
   // func: write
   // Receive the subscribed request
   function void write(req_c req);
      sample_req = req;
      cg.sample();
   endfunction : write
endclass : foo_cov_coll_c
```

6. **Phases**

Phase objections exist to ensure that various independent components do not get ahead of one another. It would be inappropriate to start sending packets into a DUT before reset was complete, for example. How those objections are raised and dropped depends on which phase they are in.

6.1.1. The reset and configuration phases' objections shall be raised/dropped by the component(s) that contribute to those phases' progress.

6.1.2. The main phase's objection shall only be raised/dropped in that phase's default sequence for any sequencers that provide stimulus. The main phase’s objection shall also only be raised by components such as top-level tests that create and start their own stimulus sequences.

6.1.3. The shutdown phase's objection shall only be raised/dropped by predictive elements (monitors, scoreboards, subscribers, etc.) that are waiting for expected responses to drain.

7. **Deadlock Monitoring**

The global environment should contain a heartbeat monitor, as presented in Recipe 10.7, that checks for a deadlock scenario through the life of the test.

7.1.1. Environment components that monitor responses from the DUT and that are in a position to say that the simulation is not deadlocked will register themselves with the heartbeat monitor during the `end_of_elaboration` phase, and may specify their required sample time.

7.1.2. Components registered with the heartbeat monitor shall provide heartbeat information on all responses to stimulus received from the DUT.

To help track what caused the deadlock, components should emit errors in the check_phase for all expected outstanding activity.

7.1.3. Predictive components shall perform end-of-run checks in the `check_phase`.

7.1.4. *Recommended*: End-of-run tasks that consume time should be placed in the `post_shutdown_phase`.

8. **Miscellaneous**

8.1.1. Testbenches and vkits shall not use `` `define `` macros for constants or enumerated types. Use SystemVerilog constants and enumerated types instead.

Constants and enumerations are properly scoped inside of packages, thus avoiding global namespace pollution. They are also not subject to order-of-compilation issues.

8.2. **Timescales, Timeunits, and Timeprecision**

Verilog has `` `timescale `` directives. SystemVerilog added `timeunit` and `timeprecision`. All of these are among the worst things ever invented because they permit code to be written in an implicit fashion rather than an explicit one.

```v
#(1);  // I have no idea how long this is
```

8.2.1 Explicit timing delays shall be used. SystemVerilog’s `` `timescale ``, `timeunit`, or `timeprecision` keywords shall not be used.

The following is both more readable and more accurate, as it is not subject to being overridden by another package's directives:

```v
#(1ns); // This is clear and unambiguous
```

8.2.2. When a time delay is controlled by a variable (random or otherwise), use an `int` or a `real` and use a naming convention that indicates the precision that shall be applied to it:

```v
rand int delay_ps;
delay_ps.randomize() with { delay_ps inside {[0:10]} };
#(delay_ps * 1ps);
```

UVM does supply the `uvm_tlm_time` class, or one could be created. However, this class is typically more trouble than it is worth.

8.3. **Single-Line Printing of Objects**

Objects that are printed to the logfile, such as transactions or data cycles, print by default in a large table format when their sprint function is called. It is often convenient to reduce these tables to a single-line synopsis of the object, so that streams of objects can be seen in the logfile. For example:

```
18132ns} Monitored: ST  | blk_id:00 | BYTE8 | addr_type:1 | 0000001630 | data: 00 00 00 00 00 00 55 55
18144ns} Monitored: DONE| blk_id:00 | BYTE1 | addr_type:0 | 0000000000
18160ns} Monitored: LD  | blk_id:00 | BYTE8 | addr_type:1 | 0000001630
18188ns} Monitored: RSP | blk_id:00 | BYTE8 | addr_type:0 | 0000000000 | data: 00 00 00 00 00 00 01 01
```

This stream is considerably easier to read than the following, which while more complete takes up considerably more screen real-estate:

```
%I-( pat_mon.sv:  119) [env.pat_agent.mon ] { 18132ns} Monitored:
----------------------------------------
Name          Type          Size  Value
----------------------------------------
trans         pat_trans_c   -     @1099
  blk_id      integral      8     'h0
  xfr_size    xfr_size_e    2     BYTE8
  addr_type   integral      1     'h1
  zero_bits   integral      2     'h0
  trans_type  trans_type_e  3     ST
  addr        integral      40    'h1630
  data_len    integral      32    'h8
  data        da(integral)  8     -
    [0]       integral      8     'h0
    [1]       integral      8     'h0
    [2]       integral      8     'h0
    [3]       integral      8     'h0
    [4]       integral      8     'h0
    [5]       integral      8     'h0
    [6]       integral      8     'h55
    [7]       integral      8     'h55
----------------------------------------
```

UVM objects have an empty `convert2string` function that UVM provides. These guidelines co-opt this function to provide a single-line printing.

8.3.1. *Recommended*: Objects and transactions that would benefit from single-line printing shall override the virtual function `convert2string` to return a single-line synopsis of the object.

For example:

```v
virtual function string convert2string();
   convert2string = $sformatf("%s | blk_id:%02X | %s | addr_type:%0d | %012X",
            trans_type, blk_id, xfr_size, addr_type, addr);
   if(data_len) begin
      convert2string = $sformat(convert2string, "%s | data:", convert2string);
      foreach(data[x])
         convert2string = $sformat(convert2string, "%s %02X", convert2string, data[x]);
   end
endfunction : convert2string
```

8.4. **The UVM Resource Database**

The UVM resource database is a convenient mechanism for storing configuration information that is not associated with any part of the UVM component hierarchy, i.e., "global" configuration information. As with all global constructs, this should be used sparingly and with great care.

The UVM resource database stores configuration items under a scope and a name, both of which are free-form strings. In order to avoid resource name collisions, the following requirement applies when verification kits make use of the UVM resource database:

8.4.1. When a vkit stores or fetches an item in the UVM resource database, it shall do so using a scope name that starts with `<prefix>_pkg`, where `<prefix>` is the vkit's prefix.

8.4.2. *Recommended*: The most common and only use of the UVM resource database by vkits should be for getting virtual interfaces from the testbench, as detailed in Configuring Virtual Interfaces.

8.4.3. *Recommended*: Anything that extends `uvm_object` should use the factory, except in instances where it is not likely that another object will be derived from it.

8.4.4. All component access to the configuration database must pass the `this` pointer for debugging purposes.

8.5. **Banned UVM Items**

These items are banned because they are or have been deprecated:

8.5.1. Never use the `uvm_transaction` class. Instead use `uvm_sequence_item`.

8.5.2. Never use `set_config_int`, `set_config_string`, or `set_config_object`.

Instead, use the following:

```v
uvm_config_db#(int)::set(this, "*", "int_field_name", value);
uvm_config_db#(string)::set(this, "*", "str_field_name", "value");
uvm_config_db#(uvm_object)::set(this, "*", "obj_field_name", obj);
```

Note that adding `uvm_objects` to the configuration database in this fashion will not clone those objects, but will instead push a reference, as is desired.

8.5.3. Never use the `starting_phase` variable to raise and drop objections in sequences. Use the macros `` `cmn_seq_raise `` and `` `cmn_seq_drop `` instead.

8.5.4. Never use the `static factory` instance variable. Use `uvm_factory::get()` instead.

8.5.5. Never use `soft` or `default` constraints. Instead, write constraints explicitly.


---


[1]: http://www.naturaldocs.org.


