#!/bin/sh

#############################################################################
#
# Copyright 2024 Thales DIS France SAS
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
# Adapted by Mathieu Gouttenoire, Thales DIS France SAS
#
#############################################################################

# Prerequisites:
#
# - autotools
# - GNU make
# - flex
# - bison
# - isl
# - gmp
# - mpz
# - mpc
# - texinfo
# - 5.5 GB of disk space

# Paths in config files are relative to this directory.
ROOT_DIR=$(dirname $(readlink -f $0))

# Load global config
. $ROOT_DIR/config/global.sh


# Helper function to print usage information.
print_usage()
{
    echo Usage:
    echo "        your-favorite-shell $0 [CONFIG_NAME]"
    echo ""
    echo "        CONFIG_NAME    Use configuration from file config/CONFIG_NAME.sh"
}

# Helper function to parse the cmdline args.
# Takes the complete list of positional args as input, drops them locally as they get parsed.
parse_cmdline()
{
    # There must be exactly one positional arg.
    if [ $# -gt 1 ]; then
	echo "*** Incorrect number of cmdline arguments ($#), exiting!"
	echo ""
	print_usage
	exit 11
    fi

    # The only, optional arg is supposed to be the config name.
    if [ $# -eq 1 ]; then
	CONFIG_NAME=$1
	shift
    fi
}

# ======== Default settings: GCC 13.1.0 baremetal ========
# - toolchain configuration
#   NOTE: config/$CONFIG_NAME.sh can be a symbolic link.
CONFIG_NAME="gcc-13.1.0-baremetal"

# ======== Parse the command line ========
parse_cmdline "$@"

# ======== Read configuration information =========
# Check for the presence of source code and build configuration file.

CONFIG_FILE="$ROOT_DIR/config/$CONFIG_NAME.sh"

if [ -f $CONFIG_FILE ]; then
    # File present: read the settings.
    . $CONFIG_FILE
else
    echo "*** Configuration file '$CONFIG_FILE' missing, bailing out!"
    echo ""
    print_usage
    exit 12
fi
# ========= Populate/update the directories =========

# Hook for the future tarball-only option
# if [ $# -lt 2 -o $1 == "git"]; then
#    # populate directories from Git
# else
#    # populate directories from tarballs
# fi

# Overall directory infrastructure: make sure `pwd`/src exists.
[ ! -d "$SRC_DIR" ] && mkdir "$SRC_DIR"

# All Git-based source trees are handled in the same way.
# Positional args:
# - $1: the Git repository to use
# - $2: the local directory for the source code
# - $3: the actual commit to check out (SHA1, tag, etc.)
setup_sources_from_git()
{
    # make sure the source directory exists and is populated
    # with Git information.  If a stale non-Git directory exits,
    # remove it unless it is write-protected.
    [ -d $SRC_DIR/$2 -a -d $SRC_DIR/$2/.git ] || \
    { rm -rf $SRC_DIR/$2 &&  \
	  git clone --depth=1 --branch="$3" $1 $SRC_DIR/$2 ; }

    # Check out the required revision as local branch (the shallow clone
    # leaves a "detached HEAD" state.)
    cd $SRC_DIR/$2
    LOCAL_BRANCH="${3}-local"
    { git branch | grep -q "$LOCAL_BRANCH" ; } || git checkout -b "$LOCAL_BRANCH"
    git checkout "$LOCAL_BRANCH"
    # Pull any updates available upstream (useful for 'master' branches).
    git pull origin "$3"
    cd -
}

# Get Binutils sources
echo "# Step 1: Obtaining sources of binutils..."
setup_sources_from_git $BINUTILS_REPO $BINUTILS_DIR $BINUTILS_COMMIT

if [[ $CONFIG_NAME == "gcc"* ]]; then
    # Get GCC sources
    echo "# Step 2: Obtaining sources of GCC..."
    setup_sources_from_git $GCC_REPO $GCC_DIR $GCC_COMMIT
else
    # Get LLVM sources
    echo "# Step 2: Obtaining sources of LLVM..."
    setup_sources_from_git $LLVM_REPO $LLVM_DIR $LLVM_COMMIT
fi

# Get Newlib sources
echo "# Step 3: Obtaining sources of newlib..."
setup_sources_from_git $NEWLIB_REPO $NEWLIB_DIR $NEWLIB_COMMIT

# Exit happily.
exit 0

