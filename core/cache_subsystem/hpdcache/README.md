# OpenHW Core-V High-Performance L1 Dcache (CV-HPDcache)

![HPDcache CI](https://github.com/openhwgroup/cv-hpdcache/actions/workflows/test.yml/badge.svg)

The HPDcache is an open-source High-Performance, Multi-requester, Out-of-Order L1 Dcache for RISC-V cores and accelerators.


## Directory Structure

<table>
  <tr>
    <th style="text-align:left;width:20%">Directory</th>
    <th style="text-align:left">Description</th>
  </tr>
  <tr>
    <td>rtl</td>
    <td>Contains the file lists to be used for the compiling of the HPDcache</td>
  </tr>
  <tr>
    <td>rtl/src</td>
    <td>Contains the SystemVerilog RTL sources of the HPDcache</td>
  </tr>
  <tr>
    <td>rtl/lint</td>
    <td>Contains a linter wrapper and a Mafile to run a lint tool on the RTL</td>
  </tr>
  <tr>
    <td>rtl/tb</td>
    <td>Contains a HPDcache standalone testbench for validation of the RTL</td>
  </tr>
  <tr>
    <td>docs</td>
    <td>Contains documentation of the HPDcache</td>
  </tr>
</table>


## Documentation

The HPDcache User Guide document can be found in the *docs* folder.
It is written in reStructuredText format.

If you need to compile the User Guide document, a dedicated *Makefile* is in the *docs* folder.

You can find some pre-compiled User Guide documents (in both HTML or PDF) in [Releases](https://github.com/openhwgroup/cv-hpdcache/releases)


## Licensing

The HPDcache is released under the Solderpad Hardware License (version 2.1).
Please refer to the [LICENSE](LICENSE) file for further information.


## Integration Examples of the HPDcache

### CVA6

The HPDcache is integrated with the CVA6 core.
The HPDcache repository (this repository) is included as a submodule of the CVA6 Git.
After you clone the [CVA6](https://github.com/openhwgroup/cva6) repository, be sure to pass the ``config_pkg::HPDCACHE`` value to the ``DCacheType`` parameter.
This selects the HPDcache as the L1 Data Cache of the core.
For example, the CVA6 configuration package [cv64a6_imafdc_sv39_hpdcache_config_pkg.sv](https://github.com/openhwgroup/cva6/blob/master/core/include/cv64a6_imafdc_sv39_hpdcache_config_pkg.sv) does this.

The HPDcache is instantiated in the [cva6_hpdcache_subsystem.sv](https://github.com/openhwgroup/cva6/blob/master/core/cache_subsystem/cva6_hpdcache_subsystem.sv) file.
You may take a look if you want to integrate the HPDcache with another core.

### Integration Template

You may look into the docs/lint subdirectory of this repository to see an integration example of the HPDcache ([hpdcache_lint.sv](docs/lint/hpdcache_lint.sv)).

This example uses the macros defined in the [hpdcache_typedef.svh](rtl/include/hpdcache_typedef.svh) file.
These macros ease the definition of types required by the interface of the HPDcache module.

## HPDcache Validation and Verification

For a complete UVM testbench of the HPDcache, please see the [HPDcache Verif](https://github.com/openhwgroup/cv-hpdcache-verif) repository.

There is another simpler testbench (hence not as complete as the one above) into the `rtl/tb` subdirectory of this repository .
This testbench is compatible with the [Verilator](https://www.veripool.org/verilator/) simulation tool.


## HPDcache Publications & Tutorials

- Technical Paper: César Fuguet. 2023. HPDcache: Open-Source High-Performance L1 Data Cache for RISC-V Cores. In Proceedings of the 20th ACM International Conference on Computing Frontiers (CF '23). Association for Computing Machinery, New York, NY, USA, 377–378. <https://doi.org/10.1145/3587135.3591413>

- Technical Paper: D. Million, N. Oliete-Escuín and C. Fuguet, "Breaking the Memory Wall with a Flexible Open-Source L1 Data-Cache," 2024 Design, Automation & Test in Europe Conference & Exhibition (DATE), Valencia, Spain, 2024, pp. 1-2, <https://doi.org/10.23919/DATE58400.2024.10546547>

- Video: César Fuguet. 2023. High Performance L1 Dcache for RISC-V Cores. TRISTAN Workshop. RISC-V Summit Europe 2023. <https://www.youtube.com/watch?v=3r5STMiUq9s>

- Video: Christian Fabre, César Fuguet. 2023. One Year of Improvements on OpenHW Group's HPDCache. RISC-V Summit US 2023. <https://www.youtube.com/watch?v=ODHA-wPOmW0>
