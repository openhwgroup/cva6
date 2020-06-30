## Toolchain Installation Instructions
What follows is a set of commands that can be used to install the RISCV GNU Toolchain from the PULP-Platform team.
If you use these commands verbatim you should not encounter any issues.  If you do, please open an issue and assign it to @MikeOpenHWGroup.
<br><br>
The process takes about two hours
<br><br>
Please note that the OpenHW Group expects to update the recommended Toolchain in the near future.
```
# Create directory for the toolchain
$ sudo mkdir /opt/riscv
# Create shell ENV variables to point to it (put this in .bashrc)
$ PATH="/opt/riscv/bin:$PATH"
$ export RISCV="/opt/riscv"
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
$ ./configure --prefix=/opt/riscv  --with-arch=rv32imc \
              --with-cmodel=medlow --enable-multilib
$ sudo make
# Wait about 2 hours (seriously, it takes that long)
```
