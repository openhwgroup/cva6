###############################################################################
# Variables to determine the the command to clone external repositories.
# For each repo there are a set of variables:
#      *_REPO:   URL to the repository in GitHub.
#      *_BRANCH: Name of the branch you wish to clone;
#                Set to 'master' to pull the master branch.
#      *_HASH:   Value of the specific hash you wish to clone;
#                Set to 'head' to pull the head of the branch you want.
# THe CV32E40X repo also has a variable to clone a specific tag:
#      *_TAG:    Value of the specific tag you wish to clone;
#                Will override the HASH unless set to "none".
#

export SHELL = /bin/bash

CV_CORE_REPO   ?= https://github.com/openhwgroup/cv32e40x
CV_CORE_BRANCH ?= master
CV_CORE_HASH   ?= af71c0ec7754fd87ce25335ef584de605aa68ca9
CV_CORE_TAG    ?= none

RISCVDV_REPO    ?= https://github.com/google/riscv-dv
RISCVDV_BRANCH  ?= master
RISCVDV_HASH    ?= f255eac0e011a95f1ae9d510adb24458b98600f3

EMBENCH_REPO    ?= https://github.com/embench/embench-iot.git
EMBENCH_BRANCH  ?= master
EMBENCH_HASH	?= 6934ddd1ff445245ee032d4258fdeb9828b72af4

COMPLIANCE_REPO   ?= https://github.com/strichmo/riscv-arch-test.git
COMPLIANCE_BRANCH ?= strichmo/pr/cv32e40x_initial_old_compliance
# 2020-08-19
COMPLIANCE_HASH   ?= cf29051b177ba61b8c39de91c33d20d202697423

# This Spike repo is only cloned when the DPI disassembler needs to be rebuilt
# Typically users can simply use the checked-in shared library
DPI_DASM_SPIKE_REPO   ?= https://github.com/riscv/riscv-isa-sim.git
DPI_DASM_SPIKE_BRANCH ?= master
DPI_DASM_SPIKE_HASH   ?= 8faa928819fb551325e76b463fc0c978e22f5be3

# SVLIB
SVLIB_REPO       ?= https://bitbucket.org/verilab/svlib/src/master/svlib
SVLIB_BRANCH     ?= master
SVLIB_HASH       ?= c25509a7e54a880fe8f58f3daa2f891d6ecf6428
