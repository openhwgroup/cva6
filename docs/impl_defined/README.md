
[//]: # (Copyright 2024 Thales DIS France SAS                                     )
[//]: # (                                                                         )
[//]: # (Licensed under the Apache License, Version 2.0 (the "License");          )
[//]: # (you may not use this file except in compliance with the License.         )
[//]: # (You may obtain a copy of the License at                                  )
[//]: # (                                                                         )
[//]: # (    http://www.apache.org/licenses/LICENSE-2.0                           )
[//]: # (                                                                         )
[//]: # (Unless required by applicable law or agreed to in writing, software      )
[//]: # (distributed under the License is distributed on an "AS IS" BASIS,        )
[//]: # (WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. )
[//]: # (See the License for the specific language governing permissions and      )
[//]: # (limitations under the License.                                           )
[//]: # (                                                                         )
[//]: # (Original Author: Zbigniew CHAMSKI - Thales                               )

***NOTE:** This is a working document and may undergo major incompatible changes...*

# Introduction

This directory contains experimental data and code related to central configuration management for CVA6 SystemVerilog code, its reference models (Spike) and all associated documentation:

- implementation-defined behaviors (as described in the RISC-V ISA specifications)
- platform configurations
- text snippets for the User Manuals
- text snippets for the Design Documents
- code snippets for IP-XACT specifications
- ... and probably more.

# Background and requirements

When verifyng hardware implementations supposed conforming to an external specification against a reference model, it is necessary to ensure consistency between the three elements at play:

- the specification,
- the implementation,
- the reference model.

Usually, external specifications are not complete and explicitly leave freedom to implementors in the form of so-called **implementation-defined** behaviors/properties.  Therefore, it is necessary to:

- identify the places in the public specification that leave such freedom (typically expressed using words "can", "may", "could" and "might");
- for each implementation:
  - describe the choices made by the implementors wrt. each freedom point;
  - for both the hardware implementation and the reference model, provide a means of enforcing the implementors' choice;
  - document each choice in a consistent and user-friendly way across all associated documentation.

Furthermore, both the hardware implementation and the reference model may need additional configuration information not defined by the specification and left to the implementors' discretion, for example the nature, size and base addresses of memories in a computer system.  This additional information will be called **platform specification**.

Hence, a complete specification of a hardware configuration (and of its reference model) must combine:

- the external specification;
- the implementation choices;
- the platform specification.

The resulting information needs to be translated in an unequivocal way into the behaviors of the hardware implementation and the reference model, and expressed in the associated human-readable documents.  Therefore, the complete specification document should associate each implementation choice and each parameter occurring in the platform specification with the necessary parameters for the hardware implementation and the necessary human-readable documentation fragments. 

# Prerequisites

The Yaml schemas use several Python features and libraries available as packages:

- `dataclasses`: the standard dataclasses resource
- `typing`: the standard type management resource
- `variconf`: a lightweight library on top of `omegaconf` library
- `omegaconf`: a library for managing configuration files expressed in various text formats.

Packages `dataclasses` and `typing` are part of standard Python distributions, whereas `variconf` and `omegaconf` are available from the PyPi servers.

# Directory structure

The current directory (as of this writing: `<CVA6_HOME>/docs/impl_defined`) is laid out as follows:

- `README.md`: this file;
- `example.py`: a simple example of loading and accessing the list of sentences of RISC-V spec vol. II containing the string 'implement' (the initial list was created manually);
- `sandbox`: a directory for technology evaluation on simple examples;
- `schemas`: directory containing Yaml schemas of various files expressed using features from `dataclasses` and `typing`;
- `spec_inventory`: Yaml descriptions of implementation freedom points in the official RISC-V specs;
- `templates`: directory containing fragments of documentation that can serve as templates for doc generation.

# Getting started with Yaml configurations

1. Make sure you installed the prerequisites: packages `omegaconf` and `variconf`.
1. Go to the directory `<CVA6_HOME>/docs/impl_defined`.
1. Run the command `python3 example.py`.
1. To look around with the Python data structures still in place, run the previous command in interactive mode with `-i` option: `python3 -i example.py`
1. Type `quit()` to exit the interactive Python section.
