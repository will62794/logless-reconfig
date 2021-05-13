#!/bin/sh

tlc="java -XX:MaxDirectMemorySize=4g -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -cp tla2tools.jar tlc2.TLC -noGenerateSpecTE"


# Check inductive invariant.
$tlc -deadlock -metadir "states/$RANDOM$RANDOM" -workers 4 MongoRaftReconfigProofs

# Check that inductive invariant is actually an invariant.
$tlc -workers 4 -config MongoRaftReconfig.cfg MongoRaftReconfigProofs