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

### Software

[github.com/openhwgroup/cva6-sdk](https://github.com/openhwgroup/cva6-sdk) contains the RISC-V tools for CVA6 and Buildroot Linux support.

[github.com/openhwgroup/meta-cva6-yocto](https://github.com/openhwgroup/meta-cva6-yocto) contains Yocto Linux support for CVA6.

### Tutorials

[github.com/ThalesGroup/cva6-eclipse-demo](https://github.com/ThalesGroup/cva6-eclipse-demo) offers resources to debug CVA6 under Eclipse IDE.

### Related building blocks

These building blocks fit very nicely with CVA6:

- [OpenPiton](https://github.com/PrincetonUniversity/openpiton) is a many-core framework that supports CVA6.
- [Culsans/CV-TCCC](https://github.com/pulp-platform/culsans) is a multi-core infrastructure for a few CVA6 cores.
- [ARA/CV-VEC](https://github.com/pulp-platform/ara) is a vector unit for CVA6.

### Design examples (FPGA)

The CVA6 repository contains the CVA6 core and a basic CPU design, the "APU" and its implementation on a Digilent Genesys 2 FPGA board. Here is a list of other CVA6-based FPGA designs:


[github.com/thalesgroup/cva6-softcore-contest](https://github.com/thalesgroup/cva6-softcore-contest) is the reference for a student contest in France. It can be used as an educational resource and as an easy way to get CVA6 up and running with a cheaper Digilent Zybo Z7-20 board. You will find in it:
- The 2020-2021 contest, focusing on PPA optimization;
- The 2021-2022 contest, focusing on energy optimization;
- The 2022-2023 contest, focusing on cybersecurity, including a port of Zephyr OS;
- The 2023-2024 contest, focusing on the acceleration of the MNIST digit recognition with custom extensions;
- The 2024-2025 contest, focusing on the frequency increase (_not released yet_);
- A treat with the support of Linux and a VGA output.

[github.com/cispa/CVA6-Vivado-Project-with-Xilinx-AXI-Ethernet/](https://github.com/cispa/CVA6-Vivado-Project-with-Xilinx-AXI-Ethernet/) is an alternative design which implements [Xilinx 1G/2.5G Ethernet Subsystem](https://www.xilinx.com/products/intellectual-property/axi_ethernet.html) on the Digilent Genesys 2 FPGA board. It has been tested with TFTP boot in u-boot and SSH in Linux.

### Designs (ASIC)

Here are open-source ASIC designs based on CVA6:

[Polara APU](https://github.com/openhwgroup/core-v-polara-apu) is a 4-core processor made with OpenPiton, ARA and CVA6.

To be completed

## Business resources

### Service offer

These companies are OpenHW members, have a good CVA6 knowledge, and offer CVA6-related service:

 (To be completed based on companies's requests. Max 1 URL and 60 words per company)

### Product ICs

If you have integrated CVA6 into a production IC, we'd like to hear from you and mention it here.

