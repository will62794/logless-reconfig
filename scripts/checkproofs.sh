#!/bin/sh

#
# Check all TLAPS proofs for establishing safety of MongoRaftReconfig.
#

tlapm --stretch 3 -v --cleanfp --timing -I ../ AuxLemmas.tla
tlapm --stretch 3 -v --cleanfp --timing -I ../ BasicQuorumsLib.tla
tlapm --stretch 3 -v --cleanfp --timing -I ../ ElectionSafetyLemmas.tla
tlapm --stretch 3 -v --cleanfp --timing -I ../ LeaderCompletenessLemmas.tla
tlapm --stretch 3 -v --cleanfp --timing -I ../ LeaderCompletenessLib.tla
tlapm --stretch 3 -v --cleanfp --timing -I ../ Lib.tla
tlapm --stretch 3 -v --cleanfp --timing -I ../ LogLemmas.tla
tlapm --stretch 3 -v --cleanfp --timing -I ../ MongoRaftReconfigProofs.tla
tlapm --stretch 3 -v --cleanfp --timing -I ../ StateMachineSafetyLemmas.tla
tlapm --stretch 3 -v --cleanfp --timing -I ../ TypeOK.tla
