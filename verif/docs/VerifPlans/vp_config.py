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

#####################################
#####  Paths are relative to the value of env variable PLATFORM_TOP_DIR
if "PLATFORM_TOP_DIR" in os.environ:  ## Env Variable existence Check
    VP_PLATFORM_TOP_DIR = os.environ["PLATFORM_TOP_DIR"]
    # Name of the project (can be empty if the variable is not defined in environment.)
    PROJECT_NAME = os.environ["PROJECT_NAME"]
    # Location of database files
    SAVED_DB_LOCATION = os.path.join(VP_PLATFORM_TOP_DIR, "*.pck")
    # Location of the Pickle file containing the current IP/Feature lock info.
    LOCKED_IP_LOCATION = os.path.join(VP_PLATFORM_TOP_DIR, "locked_ip.pick")
else:
    print("--- Error: Please define PLATFORM_TOP_DIR env variable")
    sys.exit()

# Globally accessible YAML config
def init_yaml_config(config):
    global yaml_config
    yaml_config = config
