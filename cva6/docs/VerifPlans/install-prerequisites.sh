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
# Install Python dependencies.
for REQT in `cat requirements.txt` ; do
  python3 -m pip install $REQT
done

# Check for a LaTeX installation.
which latex > /dev/null || { \
  echo "*** LaTeX ecosystem missing on you machine!"
  echo "*** Please install a LaTeX distribution if you intend to produce DV plans in PDF and/or ePub formats."
}

# Check for latexmk which is required for printable output.
which latexmk > /dev/null || { \
  echo "*** LaTeX wrapper 'latexmk' missing!"
  echo "*** Please install it if you intend to produce DV plans in PDF and/or ePub formats."
}
