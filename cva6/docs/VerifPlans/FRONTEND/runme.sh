#############################################################################
# Copyright (C) 2022 Thales DIS France SAS
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0.
#
# Original Author: Zbigniew Chamski (zbigniew.chamski@thalesgroup.com)
#############################################################################
#!/bin/sh

# Root of the example directories.  VPTOOL is located in '../vptool' relative
# to the location of 'vptool-example.sh'.
ROOTDIR=`readlink -f $(dirname $0)`

# Set up platform location.  It can be anywhere but should contain
# a valid `vp_config.py` file in `vptool` directory.
# Here we use the verification tree from the example directory.
export PLATFORM_TOP_DIR="$ROOTDIR"

# Set a meaningful name for the example project.
export PROJECT_NAME="FRONTEND"

export PYTHONPATH=`pwd`

# Run VPTOOL overriding the default theme from Yaml config with 'winxpblue'.
python3 $ROOTDIR/../../../../tools/vptool/vptool/vp.py -t winxpblue
