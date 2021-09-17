#!/bin/sh

#
# This script will download the TLA+ tools to the current directory.
#
# You can verify the download worked successfully by running:
# 
#   java -cp tla2tools.jar tlc2.TLC
#

tla_tools_link="https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"
echo "Downloading the TLA+ tools from '$tla_tools_link'."
wget $tla_tools_link