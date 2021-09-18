#!/bin/sh

#
# Check all TLAPS proofs for establishing safety of MongoRaftReconfig.
#

tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ AuxLemmas.tla
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ BasicQuorumsLib.tla
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ ElectionSafetyLemmas.tla
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ LeaderCompletenessLemmas.tla
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ LeaderCompletenessLib.tla
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ Lib.tla
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ LogLemmas.tla
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ MongoRaftReconfigProofs.tla
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ StateMachineSafetyLemmas.tla
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ TypeOK.tla
