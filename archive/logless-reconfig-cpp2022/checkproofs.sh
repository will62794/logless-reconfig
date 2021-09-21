#!/bin/sh

#
# Check all TLAPS proofs for establishing safety of MongoRaftReconfig.
#

echo "" > checkproofs.log

# Check all proofs.
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing AuxLemmas.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing BasicQuorumsLib.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing ElectionSafetyLemmas.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing LeaderCompletenessLemmas.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing LeaderCompletenessLib.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing Lib.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing LogLemmas.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing MongoRaftReconfigProofs.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing StateMachineSafetyLemmas.tla 2>&1 | tee -a checkproofs.log
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing TypeOK.tla 2>&1 | tee -a checkproofs.log

# Check for failure to prove any proof obligations.
echo "========================================"
echo "TLAPS Proof obligation failures:"
grep -B 3 -A 3 "status:failed" checkproofs.log
