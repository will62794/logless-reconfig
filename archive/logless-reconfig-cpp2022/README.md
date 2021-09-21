# MongoRaftReconfig TLAPS Safety Proofs

This directory contains the TLAPS safety proofs for the MongoRaftReconfig  protocol. The two high level safety properties that are proven are *LeaderCompleteness* and *StateMachineSafety*. The statements of the theorems establishing these properties are given in [`MongoRaftReconfigProofs.tla`](MongoRaftReconfigProofs.tla). The statement of the properties themselves are contained in [`MongoRaftReconfig.tla`](MongoRaftReconfig.tla). The proofs of safety rely on an inductive invariant which is stated formally in [`MongoRaftReconfigIndInv.tla`](MongoRaftReconfigIndInv.tla).

## Checking the Proofs

To check the proofs in this directory, you must install TLAPS, the TLA+ proof system. Installation instructions can be found [here](https://tla.msr-inria.inria.fr/tlaps/content/Download/Binaries.html). Once TLAPS is installed correctly, you can either utilize the graphical user interface of the TLA+ Toolbox to check the proofs, or you can check the proofs using the command line version of TLAPS. Instructions for both are given below.

### Using the Command Line

To check the proofs from the command line, you can run the ``checkproofs.sh`` script, which should check all proofs from the relevant TLA+ modules in this directory. This makes use of the `tlapm` binary, which should be installed and accessible if you have successfully installed TLAPS. Checking the proofs from scratch can be an expensive operation. It may take several minutes or even hours, depending on the speed of your machine. 

### Using the TLA+ Toolbox

Instructions for installing the TLA+ Toolbox can be found [here](https://lamport.azurewebsites.net/tla/toolbox.html). You can create a new Toolbox project and select MongoRaftReconfigProofs.tla as the root module file. In many cases you must also manually add the TLAPS standard library to the local toolbox path. You can do this by right clicking on your spec (in the Toolbox's spec explorer) and clicking "Properties" in the menu.  Click on the "Add Directory..." button and locate the tlaps folder that is installed on your local machine. On windows the path is typically `C:\cygwin\usr\local\lib\tlaps`, and on a UNIX based system this path is typically `/usr/local/lib/tlaps`. The absolute path should appear in the "TLA+ library path locations:" text box.

Once you have loaded a TLA+ module in the Toolbox that contains TLAPS proofs, you can select all text in the module, right click, and select the "TLA Proof Manager > Prove Step or Module" option. This should check all proofs in the current file, and you should see sections of each proof eventually be highlighted in green, indicating they were successfully checked by TLAPS. 

<!-- ## Theorems
1. IndIsInductiveInvariant (in IndProof.tla)
2. MRRImpliesLeaderCompleteness (in MRRTheorems.tla)
3. MRRImpliesStateMachineSafety (in MRRTheorems.tla) -->
