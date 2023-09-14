#############################################################################
#
# Copyright 2020-2023 Thales
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
#############################################################################
#
# Original Author: Zbigniew CHAMSKI, Thales Silicon Security
#
#############################################################################

# Name of the target to use for the toolchain.
export TARGET=riscv-none-elf

# ======= Source code setup: path, repo, commit, configure options ========

# Each *_COMMIT variable can designate any valid 'commit-ish' entity:
# typically a tag, a commit or the output of "git describe" of a Git tree.

# Binutils
BINUTILS_DIR=src/binutils-gdb
BINUTILS_REPO=https://sourceware.org/git/binutils-gdb.git
BINUTILS_COMMIT=binutils-2_40
BINUTILS_CONFIGURE_OPTS="\
	--prefix=$PREFIX \
	--target=$TARGET \
	--disable-nls \
	--disable-werror"

# GCC
GCC_DIR=src/gcc
GCC_REPO=https://github.com/gcc-mirror/gcc.git
GCC_COMMIT=releases/gcc-13.1.0
GCC_CONFIGURE_OPTS="\
	--prefix=$PREFIX \
	--target=$TARGET \
	--enable-languages=c \
	--disable-libssp \
	--disable-libgomp \
	--disable-libmudflap"

# newlib
NEWLIB_DIR=src/newlib
NEWLIB_REPO=https://sourceware.org/git/newlib-cygwin.git
NEWLIB_COMMIT=newlib-4.3.0

NEWLIB_CONFIGURE_OPTS="\
	--prefix=$PREFIX \
	--target=$TARGET \
	--enable-multilib"
