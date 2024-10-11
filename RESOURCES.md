# CVA6 Ecosystem and Resources

The CORE-V CVA6 core is part of a large open-source ecosystem. In this page, we collect pointers to this ecosystem, so that CVA6 users can find their way.

Please help improve this page, by filing an [issue](https://github.com/openhwgroup/cva6/issues) or a [pull request](https://github.com/openhwgroup/cva6/pulls). For pull requests, you need to sign the [Eclipse Contributor Agreement](https://www.eclipse.org/legal/ECA.php).

> [!NOTE]
> We only collect here pointers to resources that are mature enough to be used by external users.
> Resources that reach the TRL-5 maturity (ready to integrate into productions ICs) are clearly mentioned.
> Otherwise, you can assume a TRL-4 maturity.

> [!WARNING]  
> The CVA6 team is not liable for the other repositories.
> Assess their content and make sure they fit your needs and are mature enough for design.
> Plese direct your issues or pull requests to these external repositories.

## Our legacy

CVA6 was designed by the [PULP Platform team](https://www.pulp-platform.org/). You can integrate it with many other PULP designs from [github.com/pulp-platform](https://github.com/pulp-platform).

## Technical resources

### SW Tools and OSes

RISC-V tools for CVA6 and Buildroot Linux support are available [here](https://github.com/openhwgroup/cva6-sdk).

Yocto Linux support for CVA6 is available [here](https://github.com/openhwgroup/meta-cva6-yocto).

FreeRTOS support for CVA6 is available [here](https://github.com/FreeRTOS/FreeRTOS-Partner-Supported-Demos/tree/main/RISC-V_cva6).

Zephyr support for CV64A6 will soon be available.

This [tutorial](https://github.com/ThalesGroup/cva6-eclipse-demo) offers resources to debug CVA6 under Eclipse IDE.

The OS ports below are on Digilent Genesys 2 board.

### Related building blocks

These building blocks fit very nicely with CVA6:

- [OpenPiton](https://github.com/PrincetonUniversity/openpiton) is a many-core framework that supports CVA6.
- [Culsans/CV-TCCC](https://github.com/pulp-platform/culsans) is a multi-core infrastructure for a few CVA6 cores.
- [ARA/CV-VEC](https://github.com/pulp-platform/ara) is a vector unit for CVA6.
- [HPDcache](https://github.com/openhwgroup/cv-hpdcache) is a flexible (highly configurable) and high-throughput L1 cache.

### Design examples (FPGA)

The CVA6 repository contains the CVA6 core and a basic CPU design, the "APU" and its implementation on a Digilent Genesys 2 FPGA board. Here is a list of other CVA6-based FPGA designs:

The [technical kits](https://github.com/thalesgroup/cva6-softcore-contest) of a student contest organized in France can be used as educational resources or as an easy way to get CVA6 up and running with a cheaper Digilent Zybo Z7-20 board. You will find in it:
- The 2020-2021 contest, focusing on PPA optimization;
- The 2021-2022 contest, focusing on energy optimization;
- The 2022-2023 contest, focusing on cybersecurity, including a port of Zephyr OS;
- The 2023-2024 contest, focusing on the acceleration of the MNIST digit recognition with custom extensions;
- The 2024-2025 contest, focusing on the frequency increase (_not released yet_);
- A treat with the support of Linux and a VGA output.

[CVA6 with Xilinx Ethernet](https://github.com/cispa/CVA6-Vivado-Project-with-Xilinx-AXI-Ethernet/) is an alternative design which implements Xilinx 1G/2.5G Ethernet Subsystem on the Digilent Genesys 2 FPGA board. It has been tested with TFTP boot in u-boot and SSH in Linux.

### Designs (ASIC)

Here are open-source ASIC designs based on CVA6:

[Polara APU](https://github.com/openhwgroup/core-v-polara-apu) is a 4-core processor made with OpenPiton, ARA and CVA6.

To be completed

## Business resources

### Service offer

These companies are OpenHW members, have a good CVA6 knowledge, and offer CVA6-related service:

**Zero-Day Labs** provides design and development services primarily related to embedded software/firmware security and hardware (RTL) for RISC-V.
With major contributions in the scope of RISC-V virtualization, the company has developed and maintains the RISC-V Hypervisor extension in CVA6
and has recently made open-source the RISC-V AIA and IOMMU IPs.
Contact: [geral@zero-day-labs.com](mailto:geral@zero-day-labs.com).

RISC-V made easy - experienced ASIC/FPGA service providers, [**PlanV**](https://planv.tech/) will help you navigate the IP landscape,
optimize your design workflows, and bring your RISC-V chip to life.

[**MU-Electronics**](https://www.mu-e.com/) is a services company having its design center in Rabat-Morocco since 2003, specialized in ICs design from datasheet to GDSII generation
(RTL design, DFT, verification, full custom layout, place and route), firmware, driver & application development, test & validation, security implementation & support to certification.
MU-E has designed IPs and Chips down to 7nm. MU-E is participating in the European TRISTAN project and working for Thales on the verification of CVA6.

[**10xEngineers**](https://10xengineers.ai/) is a design and verification services company focused on RISC-V. We contribute to compiler enablement, RTL design,
and verification efforts within the OpenHW ecosystem. Our work on CVA6 includes architectural and microarchitectural verification of MMU
and implementation of multiple RISC-V extensions, such as Bitmanip, Zicond, Zcb, and Zcmp. Our expert team assists companies in integrating,
customizing, and optimizing CVA6 to meet their unique requirements.

 _(To be completed based on companies's requests. Max 1 URL and 60 words per company)_

### Product ICs

If you have integrated CVA6 into a production IC, we'd like to hear from you and mention it here.

