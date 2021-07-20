## Toolchain Installation Instructions

### CORE-V Toolchain
The recommended toolchain for all CORE-V cores is available
[here](https://www.embecosm.com/resources/tool-chain-downloads/#corev).
It is recommended that you install this at /opt/corev, add it to your path and
create a shell variable COREV to YES:
```
$ PATH="/opt/corev/bin:$PATH"
$ export COREV="YES"
```
Search for "Toolchain" in `../../mk/Common.mk` for guidance on how to get a custom
installation to work with the Makefiles.

### PULP Toolchain
If you are using the PULP instruction extensions, you will need access to the PULP toolchain.  **Note** that this toolchain is
out-of-date and cannot compile all test-programs for the CV32E40S, so it is recommended to use the COREV toolchain by
default and the PULP toolchain as needed.  The see the comment header in `Common.mk` (in this directory) to
see how to set this up.

#### Pre-built PULP Toolchain
The PULP toolchain for CV32E40S is available [here](https://www.embecosm.com/resources/tool-chain-downloads/#pulp).
It is recommended that you install this at /opt/pulp.

#### Building the PULP Toolchain from source
What follows is a set of commands that can be used to install the Toolchain from the PULP-Platform team.
If you use these commands verbatim you should not encounter any issues.  If you do, please open an issue and assign it to @MikeOpenHWGroup.
<br><br>
The process takes about two hours
<br><br>
Please note that the OpenHW Group expects to update the recommended Toolchain in the near future.
```
# Create directory for the toolchain
$ sudo mkdir /opt/pulp
# Create shell ENV variables to point to it (put this in .bashrc)
$ PATH="/opt/pulp/bin:$PATH"
$ export PULP="YES"
# Get prerequists
$ sudo apt-get update
$ sudo apt-get install autoconf automake autotools-dev curl libmpc-dev \
               libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf \
               libtool patchutils bc zlib1g-dev
# Clone the toolchain repo (assumes you are placing the cloned code in
# ~GitHubRepos/pulp-platform/pulp-riscv-gnu-toolchain/master).
$ cd ~GitHubRepos/pulp-platform/pulp-riscv-gnu-toolchain
$ git clone --recursive \
            https://github.com/pulp-platform/pulp-riscv-gnu-toolchain \
            master
$ cd master
# Build the toolchain
$ ./configure --prefix=/opt/pulp  --with-arch=rv32imc \
              --with-cmodel=medlow --enable-multilib
$ sudo make
# Wait about 2 hours (seriously, it takes that long)
```
