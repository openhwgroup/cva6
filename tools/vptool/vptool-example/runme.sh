#!/bin/sh

# Root of the example directories.  VPTOOL is located in '../vptool' relative
# to the location of 'vptool-example.sh'.
ROOTDIR=`readlink -f $(dirname $0)`

# Set up platform location.  It can be anywhere but should contain
# a valid `vp_config.py` file in `vptool` directory.
# Here we use the verification tree from the example directory.
export PLATFORM_TOP_DIR="$ROOTDIR/example-database"

# Let the user know about the env variable settings.
echo "export PLATFORM_TOP_DIR=$PLATFORM_TOP_DIR"

# Set a meaningful name for the example project.
export PROJECT_NAME="VPTOOL example project"
echo 'export PROJECT_NAME="VPTOOL example project"'

# Run VPTOOL overriding the default theme from Yaml config with 'winxpblue'.
echo "python3 $ROOTDIR/../vptool/vp.py -t winxpblue"
python3 $ROOTDIR/../vptool/vp.py -t winxpblue

