# MongoRaftReconfig TLAPS Safety Proofs

This directory contains TLAPS safety proofs of the MongoRaftReconfig dynamic reconfiguration protocol, in addition to a formally stated inductive invariant that is used in these proofs. The two high level safety properties that are proven are *LeaderCompleteness* and *StateMachineSafety*. At a high level, the important files are as follows:

- [`MongoRaftReconfigIndInv.tla`](MongoRaftReconfigIndInv.tla) - 
contains the statement of our inductive invariant, `Ind`, which is used for 
proving safety of MongoRaftReconfig. 
- [`MongoRaftReconfigProofs.tla`](MongoRaftReconfigProofs.tla) - contains the theorems `MRRImpliesLeaderCompleteness` and `MRRImpliesStateMachineSafety` which, respectively, establish *LeaderCompleteness* and *StateMachineSafety* for MongoRaftReconfig. It also contains the theorem `IndIsInductiveInvariant`, which proves our inductive invariant.
- [`MongoRaftReconfig.tla`](../MongoRaftReconfig.tla) - the formal specification of MongoRaftReconfig, which also includes the definitions of the *LeaderCompleteness* and *StateMachineSafety* properties.

`MongoRaftReconfigProofs.tla` contains the key, high level safety results, which are the safety proofs of *LeaderCompleteness* and *StateMachineSafety*, and the proof of our inductive invariant. The theorems proved in `MongoRaftReconfigProofs.tla`, however, depend on many auxiliary lemmas and axioms, which are stated and proven in several, separate files in this directory. Specifically, these auxiliary lemmas and axioms appear in the following files:

- [`ElectionSafetyLemmas.tla`](ElectionSafetyLemmas.tla) 
- [`LogLemmas.tla`](LogLemmas.tla)
- [`LeaderCompletenessLemmas.tla`](LeaderCompletenessLemmas.tla) 
- [`LeaderCompletenessLib.tla`](LeaderCompletenessLib.tla)
- [`StateMachineSafetyLemmas.tla`](StateMachineSafetyLemmas.tla)
- [`BasicQuorumsLib.tla`](BasicQuorumsLib.tla)
- [`AuxLemmas.tla`](AuxLemmas.tla)
- [`Lib.tla`](Lib.tla)
- [`TypeOK.tla`](TypeOK.tla)
- [`Assumptions.tla`](Assumptions.tla)

The results proven in `MongoRaftReconfigProofs.tla` only hold under the assumption that the lemmas and axioms in these auxiliary files hold. Below we describe how to mechanically check our proofs, which requires checking the top level results of `MongoRaftReconfigProofs.tla`, along with the proofs of the auxiliary lemmas in the files listed above.

## Checking the TLAPS Proofs

### Setup

To check the proofs in this directory, you must first install the following tools:

- The TLA+ Toolbox ([installation instructions](https://lamport.azurewebsites.net/tla/toolbox.html)).
- The TLA+ proof system ([installation instructions](https://tla.msr-inria.inria.fr/tlaps/content/Download/Binaries.html)).

Both of these tools should work on Linux, Windows, or Mac platforms. Once the TLA+ Toolbox and the TLA+ proof system are installed, you can use the graphical user interface of the TLA+ Toolbox to check the proofs establishing the safety of MongoRaftReconfig, 

To do this, you can start by opening the TLA+ Toolbox and creating a new TLA+ Toolbox project, by selecting `Open Spec > Add New Spec...` in the menu bar. Then, select the location of `MongoRaftReconfigProofs.tla` as the root module file of the project when prompted. You must also add the top level directory of the overall repository (`../`) to the path where the Toolbox searches for TLA+ modules to import. You can do this by right clicking on your spec (in the Toolbox's spec explorer) and clicking "Properties" in the menu.  Click on the `Add Directory...` button and locate the top level directory of this repository on your local machine. For example, if the current directory is located at `/home/user/logless-reconfig/proofs`, you should select the path `/home/user/logless-reconfig`. After doing this the absolute path should appear in the `TLA+ library path locations:` text box. 

### Proof Checking

When viewing a TLA+ file that contains TLAPS proofs in the Toolbox, to check the proofs in that file, you can select all text in the file, right click, and select the `TLA Proof Manager > Prove Step or Module` option. This should check all proofs in the current file, and you should see sections of each proof be incrementally highlighted in green, indicating they were successfully checked by TLAPS. Once the top level theorem or lemma statement is highlighted in green, this means the proof has been successfully checked.

As explained in the prior section, the TLAPS proofs contained in this repository are spread across several files, so to verify that our overall safety results hold, you must check the proofs of each relevant file. This must be done manually since, by default, the current version of the TLA+ Toolbox does not automatically check the proofs of all lemmas that a proof depends on. The proofs in the files listed below must be checked in order to establish the top level theorems stated in `MongoRaftReconfigProofs.tla`:

- `MongoRaftReconfigProofs.tla` (92 secs.)
- `ElectionSafetyLemmas.tla` (488 secs.)
- `LogLemmas.tla` (651 secs.)
- `LeaderCompletenessLemmas.tla `(635 secs.)
- `LeaderCompletenessLib.tla` (179 secs.)
- `StateMachineSafetyLemmas.tla` (69 secs.)
- `BasicQuorumsLib.tla` (15 secs.)
- `AuxLemmas.tla` (13 secs.)
- `Lib.tla` (115 secs.)
- `TypeOK.tla` (14 secs.)
- `Assumptions.tla` (1 secs.)

Next to each file we give an estimate of how long it takes to check the proofs in the file, which is taken from from a run of proof checking on a 2020 M1 Macbook Air with 8 CPU cores. The sum of the proof checking times listed above is 2271 seconds, which is approximately 38 minutes. Note that TLAPS will utilize all available CPU cores by default. Proof checking can be a fairly computationally expensive task, so we recommend doing this on a machine that is relatively unloaded with other tasks. The exact time it takes to check the proofs will vary based on the speed of your local machine, but we were generally able to check all proofs in less than 1 hour using relatively modern laptop machines. 

### Addressing Proof Checking Failures

If part of a TLAPS proof happens to fail, the failed steps will be highlighted in red in the Toolbox interface. This may occur if your machine is too slow relative to the default timeouts used for the internal queries made by TLAPS. If this occurs, you can try re-checking the proofs in a file with larger timeout values. You can do this by re-checking the proofs in a file with the following steps:
- Select all text in the file whose proofs you want to check.
- Right click on the selected file text and select the `TLA Proof Manager > Launch Prover...` option. This should bring up a prompt window.
- In the prompt window, there is a text entry field labeled `Enter additional tlapm command-line arguments`. In this field, enter the text `--stretch 3`. This will multiply all of the default timeouts used by TLAPS by a factor of 3. 
- In the same prompt window, there is also a button option labeled `Forget all previous results`. Select this option. This will ensure the proofs are checked from scratch, without relying on cached proof results.
- Then, click `OK`, and the proofs in that file should start being checked.

If some of the proofs in a file still fail, you can try again with a larger `--stretch` parameter, increasing it until the proofs succeed. In our local runs, we were able to check the proofs with the default timeouts (equivalent to `--stretch 1`), so on a modern machine we expect that a stretch value more than 2 or 3 likely shouldn't be needed. On a much slower or loaded machine, however, it may need to be set higher.



<!--


# MongoRaftReconfig TLAPS Safety Proofs

This directory contains the TLAPS safety proofs for the MongoRaftReconfig  protocol. The two high level safety properties that are proven are *LeaderCompleteness* and *StateMachineSafety*. The statements of the theorems establishing these properties are given in [`MongoRaftReconfigProofs.tla`](MongoRaftReconfigProofs.tla). The statement of the properties themselves are contained in [`MongoRaftReconfig.tla`](../MongoRaftReconfig.tla). The proofs of safety rely on an inductive invariant which is stated formally in [`MongoRaftReconfigIndInv.tla`](MongoRaftReconfigIndInv.tla).

## Checking the Proofs

To check the proofs in this directory, you must install TLAPS, the TLA+ proof system. Installation instructions can be found [here](https://tla.msr-inria.inria.fr/tlaps/content/Download/Binaries.html). Once TLAPS is installed correctly, you can either utilize the graphical user interface of the TLA+ Toolbox to check the proofs, or you can check the proofs using the command line version of TLAPS. Instructions for both are given below.

### Using the Command Line

To check the proofs from the command line, you can run the ``../scripts/checkproofs.sh`` script, which should check all proofs from the relevant TLA+ modules in this directory. This makes use of the `tlapm` binary, which should be installed and accessible if you have successfully installed TLAPS. Checking the proofs from scratch can be an expensive operation. It may take several minutes or even hours, depending on the speed of your machine. 

### Using the TLA+ Toolbox

Instructions for installing the TLA+ Toolbox can be found [here](https://lamport.azurewebsites.net/tla/toolbox.html). You can create a new Toolbox project and select MongoRaftReconfigProofs.tla as the root module file. You must also add the top level directory of this repository (`../`) to the path where the Toolbox searches for TLA+ modules to import. You can do this by right clicking on your spec (in the Toolbox's spec explorer) and clicking "Properties" in the menu.  Click on the "Add Directory..." button and locate the top level directory of this repository on your local machine. For example, if the current directory is located at `/home/user/logless-reconfig/proofs`, you should select the path `/home/user/logless-reconfig`. The absolute path should appear in the "TLA+ library path locations:" text box. Note that you will also have to add the path to the TLAPS standard library of theorems. On a UNIX based system, this path should be  `/usr/local/lib/tlaps`.

Once you have loaded a TLA+ module in the Toolbox that contains TLAPS proofs, you can select all text in the module, right click, and select the "TLA Proof Manager > Prove Step or Module" option. This should check all proofs in the current file, and you should see sections of each proof eventually be highlighted in green, indicating they were successfully checked by TLAPS. 

-->
