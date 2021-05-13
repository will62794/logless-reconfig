#!/bin/sh

#
# Command line arguments.
# 
# usage: ./tlcrun.sh <config_file> <spec_file> <worker_count>
#
CONFIG=$1
SPEC=$2
WORKERS=$3

tlc="java -XX:MaxDirectMemorySize=4g -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -cp tla2tools.jar tlc2.TLC"

# Create output file to store results.
results_dir="tlc-results"
mkdir -p $results_dir
outdir="$results_dir/$(date +%F)_$(date +%s)_$SPEC"
mkdir $outdir

# Copy the complete spec and config to the out directory.
cp "$SPEC.tla" $outdir
cp $CONFIG $outdir

# Save metadata about the run.
infofile="$outdir/info.txt"
touch $infofile

# Save some info about the run.
GIT_REV=`git rev-parse --short HEAD`
INFO=`uname -a`

# First for Linux, second for Mac.
CPUNAMELinux=`grep -m 1 'model name' /proc/cpuinfo`
CPUCORESLinux=`nproc`
CPUNAMEMac=`sysctl -n machdep.cpu.brand_string`
CPUCORESMac=`sysctl -n machdep.cpu.thread_count`

echo "Git Revision: $GIT_REV" >> $infofile
echo "Platform: $INFO" >> $infofile
echo "CPU Info Linux: $CPUNAMELinux" >> $infofile
echo "CPU Cores Linux: $CPUCORESLinux" >> $infofile
echo "CPU Info Mac: $CPUNAMEMac" >> $infofile
echo "CPU Cores Mac: $CPUCORESMac" >> $infofile

# Run the model checker.
tlcoutfile="$outdir/tlc.out"
$tlc -gzip -workers $WORKERS -config $CONFIG "$SPEC.tla" | tee $tlcoutfile