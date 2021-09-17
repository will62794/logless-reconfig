There are four high level steps for running the MSR proof:
1. Download the Toolbox
2. Download TLAPS
3. Create a new project in the Toolbox for MSR
4. Prove MSR

Here are the details:
1. Download the Toolbox
  Model checking at the command line is very lightweight and easy.  Unfortunately I do not know of a way to prove TLA theorems at the command line so we need the IDE (called Toolbox).  There's instructions for downloading the Toolbox here: https://lamport.azurewebsites.net/tla/toolbox.html

2. Download TLAPS
  It looks like TLAPS has an installer: https://tla.msr-inria.inria.fr/tlaps/content/Download/Binaries.html

  Sometimes this isn't enough to get TLAPS working, especially on Windows.  Here are two additional items you should try:
  1. Go to: File > Preferences > TLAPS.  Under "Location of tlapm" you can add the executable, for example: C:\cygwin\usr\local\bin\tlapm.exe
  2. On Windows: try adding the full path to /bin, /usr/bin, and /usr/local/bin to the PATH environment variable.  You can do this by going to "System Properties" and clicking on "Environment Variables" then, under "User variables for *your name*" select "Path" and click "Edit".  You can add the three paths here.  For more info: https://github.com/tlaplus/tlapm/issues/36#issuecomment-825695489
      For example, you could add: C:\cygwin\bin, C:\cygwin\usr\bin, and C:\cygwin\usr\local\bin

3. Create a new project in the Toolbox for MSR
  a. Clone logless-reconfig to your local machine if you haven't already.  You can use git clone for this repo: https://github.com/will62794/logless-reconfig
  b. Create a new spec (project).  In the Toolbox, click: File > Open Spec > Add New Spec...
  c. Fill out the "New TLA+ Specification" dialog:
     Root-module file: The path to one of the files you want to prove
       The file you want to select for "Root-module file" is: https://github.com/will62794/logless-reconfig/tree/master/specs/proofs/ian/static-raft-msr/MongoStaticRaftProofsSMS_LC_II.tla (but wherever you saved it locally from step 3a).
     Specification name: The project name
       "Specification name" is the project name and is ususally the name of the file with no extension
     An example is:
       Root-module file: C:\Users\ianda\Documents\school\MastersResearch\tla\logless-reconfig\specs\proofs\ian\static-raft-msr\MongoStaticRaftProofsSMS_LC_II.tla
       Specification name: MongoStaticRaftProofsSMS_LC_II
  d. Open up the modules that you want to prove.  
     There are three modules you want to open:
      - MongoStaticRaftProofsLemmaBasic
      - MongoStaticRaftProofsLemmaSecondariesFollowPrimary
      - MongoStaticRaftProofsSMS_LC_II
     You can open these specs from the "Spec Explorer" sidebar (on the left) and double clicking on the "modules" that you want

4. Prove MSR
  To prove every theorem in a file:
    a. ctrl+a (select all)
    b. ctrl+gg (prove)
  Notes for proving:
    a. It can take a really long time to prove.  I recommend not touching the Toolbox while it's proving because it gets cranky.
    b. Some proofs will inevitably fail the first time around.  If you see any theorems highlighted in red when the Toolbox is done proving a file, just reprove these theorems individually until they become green.  You can do this by clicking (placing your cursor) on the name of the theorem and hitting "ctrl+gg".  This should reprove the entire theorem from scratch.
