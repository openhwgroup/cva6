#############################################################################
# Copyright (C) 2022 Thales DIS France SAS
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0.
#
# Original Author: Zbigniew Chamski (zbigniew.chamski@thalesgroup.com)
#############################################################################

import re, os, glob, sys
import subprocess

#####################################
# Default initialization
VP_PLATFORM_TOP_DIR = ""

## Want to load/save db in/from a unique file (False), or with split files, one per Feature(True)
SPLIT_SAVE = True

##########################################################################
##########################################################################
##### PROJECT SETUP

##########################################################################
#####  Default paths are relative to the value of env variable PLATFORM_TOP_DIR.
if "PLATFORM_TOP_DIR" in os.environ:  ## Env Variable existence Check
    VP_PLATFORM_TOP_DIR = os.environ["PLATFORM_TOP_DIR"]
else:
    print(
        "--- Error: Project location not set, please define PLATFORM_TOP_DIR env variable!"
    )
    sys.exit()

# Name of the project (can be empty if the variable is not defined in environment.)
if "PROJECT_NAME" in os.environ:
    PROJECT_NAME = os.environ["PROJECT_NAME"]
else:
    print("--- Error: Project name not set, please define PROJECT_NAME env variable!")
    sys.exit()

# Identifier of the project, to be used when constructing file names,
# tag identifiers, etc.
if "PROJECT_IDENT" in os.environ:
    PROJECT_IDENT = os.environ["PROJECT_IDENT"]
else:
    print(
        "--- Error: Project identifier not set, please define PROJECT_IDENT env variable!"
    )
    sys.exit()

# Location of database files
SAVED_DB_LOCATION = os.path.join(VP_PLATFORM_TOP_DIR, "*.pck")

# Location of Markdown output file(s)
if "MARKDOWN_OUTPUT_DIR" in os.environ:
    MARKDOWN_OUTPUT_DIR = os.environ["MARKDOWN_OUTPUT_DIR"]
else:
    MARKDOWN_OUTPUT_DIR = VP_PLATFORM_TOP_DIR

# Location of the Pickle file containing the current IP/Feature lock info.
LOCKED_IP_LOCATION = os.path.join(VP_PLATFORM_TOP_DIR, "locked_ip.pick")

# Default Git revision
io_fmt_gitrev = ""
config_gitrev = "$Id$"

# Globally accessible YAML config
def init_yaml_config(config):
    global yaml_config
    yaml_config = config
