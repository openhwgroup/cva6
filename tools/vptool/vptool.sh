#############################################################################
# Copyright (C) 2023 Thales DIS France SAS
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0.
#
# Original Author: Zbigniew Chamski (zbigniew.chamski@thalesgroup.com)
#############################################################################
#!/bin/sh

# Set the canonical path of the current script.
VPTOOL_DIR=$(dirname $(readlink -f $0))

# Install any missing dependencies.
# - check if tkinter module is available (its installation requires super-user privileges.)
#   If not, provide installation hints.
echo "import tkinter" | python3 || \
{
  echo "*** Missing system-wide dependency: Python3 module 'tkinter' not installed."
  echo "*** Please ask your administrator to install the required package:"
  echo "***   - Debian, Ubuntu:             'python3-tk'"
  echo "***   - RedHat EL, CentOS, Fedora:  'python3-tkinter'"
  exit 1;
}

# - install Python3 required modules in user space.
python3 -m pip install -q -r $VPTOOL_DIR/vptool/requirements.txt

# Run VPTOOL with the arguments as supplied by the caller.
python3 $VPTOOL_DIR/vptool/vp.py $*
