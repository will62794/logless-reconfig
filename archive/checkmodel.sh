#!/bin/sh

#
# Command line arguments.
# 
# usage: ./checkmodel.sh <config_file> <spec_file> <worker_count>
#
CONFIG=$1
SPEC=$2
WORKERS=$3

tlc="java -XX:MaxDirectMemorySize=4g -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -cp tla2tools.jar tlc2.TLC"

# Create output file to store results.
mkdir -p "tlc-results"
outfilename="$(date +%F)_$(date +%s)_$SPEC".out
outfile="tlc-results/$outfilename"
touch $outfile

# Save some info about the run.
GIT_REV=`git rev-parse --short HEAD`
INFO=`uname -a`

# First for Linux, second for Mac.
CPUNAMELinux=`grep -m 1 'model name' /proc/cpuinfo`
CPUCORESLinux=`nproc`
CPUNAMEMac=`sysctl -n machdep.cpu.brand_string`
CPUCORESMac=`sysctl -n machdep.cpu.thread_count`

echo "Git Revision: $GIT_REV" >> $outfile
echo "Platform: $INFO" >> $outfile
echo "CPU Info Linux: $CPUNAMELinux" >> $outfile
echo "CPU Cores Linux: $CPUCORESLinux" >> $outfile
echo "CPU Info Mac: $CPUNAMEMac" >> $outfile
echo "CPU Cores Mac: $CPUCORESMac" >> $outfile
echo "Spec: $SPEC.tla" >> $outfile
echo "Config: $CONFIG" >> $outfile
echo "----" >> $outfile
cat $CONFIG >> $outfile
echo "" >> $outfile
echo "----" >> $outfile
echo "" >> $outfile

# Run the model checker.
$tlc -gzip -workers $WORKERS -config $CONFIG "$SPEC.tla" | tee -a $outfile