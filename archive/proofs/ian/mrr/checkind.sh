#!/bin/sh

#
# Check that the inductive invariant for MongoRaftReconfig is actually an invariant
# and that it is inductive. 
#

jopts="-XX:MaxDirectMemorySize=4g -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet"
tlc="java $jopts -cp tla2tools.jar tlc2.TLC -noGenerateSpecTE"

# Check that inductive invariant is actually an invariant.
$tlc -workers 4 -config MongoRaftReconfig.cfg MongoRaftReconfigProofs

# Check that the inductive invariant is actually inductive.
$tlc -deadlock -metadir "states/$RANDOM$RANDOM" -workers 4 MongoRaftReconfigProofs

