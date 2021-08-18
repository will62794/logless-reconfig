#!/bin/sh
tlc="java -cp ../dynamic/tla2tools.jar tlc2.TLC -noGenerateSpecTE"

mkdir -p cex-tikz

# Election safety counterexamples.
$tlc -config cex-models/MongoLoglessDynamicRaft-elecsafety-no-config-check.cfg MongoLoglessDynamicRaft.tla | python trace.py > cex-tikz/elecsafety-no-config-check.tex
$tlc -config cex-models/MongoLoglessDynamicRaft-elecsafety-no-term-check.cfg MongoLoglessDynamicRaft.tla | python trace.py > cex-tikz/elecsafety-no-term-check.tex

# Leader completeness counterexamples.
$tlc -config cex-models/MongoRaftReconfig-leadercompl-no-log-prop.cfg MongoRaftReconfig.tla | python trace.py > cex-tikz/leadercompl-no-log-prop.tex
$tlc -config cex-models/MongoRaftReconfig-leadercompl-no-term-check.cfg MongoRaftReconfig.tla | python trace.py > cex-tikz/leadercompl-no-term-check.tex
