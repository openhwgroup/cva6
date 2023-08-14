#!/bin/sh

#############################################################################
# Copyright (C) 2022 Thales DIS France SAS
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0.
#
# Original Author: Zbigniew Chamski (zbigniew.chamski@thalesgroup.com)
#############################################################################
# Make sure all necessary components are installed/available.
#
# Install Python dependencies. We can extract the full path of the script only
# when invoked using '$SHELL <script>' syntax.  With "source" and "dot" invocation
# methods (basename of $0 equal to $SHELL), the script must be run from the
# directory containing 'requirements.txt'.
[ $(basename $SHELL) = $0 ] && { \
  echo "Please run this script from the directory in which it is located,"
  echo "or use the syntax '"$0 path-to-script"'"
  return 1
}
python3 -m pip install -q -r $(dirname $(readlink -f $0))/requirements.txt

# Check for a LaTeX installation.
which latex > /dev/null || { \
  echo "*** LaTeX ecosystem missing on you machine!"
  echo "*** Please install a LaTeX distribution if you intend to produce DV plans in PDF and/or ePub formats."
  return 1
}

# Check for latexmk which is required for printable output.
which latexmk > /dev/null || { \
  echo "*** LaTeX wrapper 'latexmk' missing!"
  echo "*** Please install it if you intend to produce DV plans in PDF and/or ePub formats."
  return 1
}

echo "All dependencies for human-readable Verification Plan generation are OK."
