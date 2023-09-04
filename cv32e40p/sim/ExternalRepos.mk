###############################################################################
# Variables to determine the the command to clone external repositories.
# For each repo there are a set of variables:
#      *_REPO:   URL to the repository in GitHub.
#      *_BRANCH: Name of the branch you wish to clone;
#                Set to 'master' to pull the master branch.
#      *_HASH:   Value of the specific hash you wish to clone;
#                Set to 'head' to pull the head of the branch you want.
# THe CV32E40P repo also has a variable to clone a specific tag:
#      *_TAG:    Value of the specific tag you wish to clone;
#                Will override the HASH unless set to "none".
#

export SHELL = /bin/bash

CV_CORE_REPO   ?= https://github.com/openhwgroup/cv32e40p
CV_CORE_BRANCH ?= master
CV_CORE_HASH   ?= fcd5968
CV_CORE_TAG    ?= none
# The CV_CORE_HASH above points to version of the RTL that is newer, but
# logically equivalent RTL with respect to v1.0.0 RTL freeze version.
# There are some implementation and testbench updates in the above hash.
# Set CV_CORE_TAG as below to point to the exact cv32e40p repo as that used at RTL freeze
#CV_CORE_TAG    ?= cv32e40p_v1.0.0

RISCVDV_REPO    ?= https://github.com/google/riscv-dv
RISCVDV_BRANCH  ?= master
RISCVDV_HASH    ?= 0b625258549e733082c12e5dc749f05aefb07d5a

EMBENCH_REPO    ?= https://github.com/embench/embench-iot.git
EMBENCH_BRANCH  ?= master
EMBENCH_HASH    ?= 6934ddd1ff445245ee032d4258fdeb9828b72af4

COMPLIANCE_REPO   ?= https://github.com/riscv/riscv-compliance
COMPLIANCE_BRANCH ?= master
# 2020-08-19
COMPLIANCE_HASH   ?= c21a2e86afa3f7d4292a2dd26b759f3f29cde497

# This Spike repo is only cloned when the DPI disassembler needs to be rebuilt.
# Typically users can simply use the checked-in shared library.
# Should you need to, the command is "make dpi_dasm".
DPI_DASM_SPIKE_REPO   ?= https://github.com/riscv/riscv-isa-sim.git
DPI_DASM_SPIKE_BRANCH ?= master
DPI_DASM_SPIKE_HASH   ?= 8faa928819fb551325e76b463fc0c978e22f5be3

# SVLIB
SVLIB_REPO       ?= https://bitbucket.org/verilab/svlib/src/master/svlib
SVLIB_BRANCH     ?= master
SVLIB_HASH       ?= c25509a7e54a880fe8f58f3daa2f891d6ecf6428
