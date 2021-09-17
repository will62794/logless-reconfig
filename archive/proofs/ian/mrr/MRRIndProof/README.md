# Mongo Raft Reconfig TLAPS Proofs

## Important note for setting up the proofs in the Toolbox
It is necessary to add the MRR spec files to the project path.  You can do this by right clicking on your spec (in the spec explorer) and clicking "Properties" in the menu.  Click on the button "Add Directory..." and locate the following directory on your local machine: "logless-reconfig/specs/proofs/ian/mrr/MRRIndProof".  The absolute path should appear in the "TLA+ library path locations:" text box.  

## Theorems
1. IndIsInductiveInvariant (in IndProof.tla)
1. MRRImpliesLeaderCompleteness (in MRRTheorems.tla)
1. MRRImpliesStateMachineSafety (in MRRTheorems.tla)
