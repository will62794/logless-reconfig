#!/bin/sh

#
# Check all TLAPS proofs for establishing safety of MongoRaftReconfig.
#

echo "" > checkproofs.log

# Check all proofs.
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ AuxLemmas.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ BasicQuorumsLib.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ ElectionSafetyLemmas.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ LeaderCompletenessLemmas.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ LeaderCompletenessLib.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ Lib.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ LogLemmas.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ MongoRaftReconfigProofs.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ StateMachineSafetyLemmas.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ TypeOK.tla 2>&1 | tee -a checkproofs.log

# Check for failure to prove any proof obligations.
echo "========================================"
echo "TLAPS Proof obligation failures:"
grep -B 3 -A 3 "status:failed" checkproofs.log