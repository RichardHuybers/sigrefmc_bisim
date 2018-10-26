The SigrefMC package has been extended to include the algorithms and BDD operations developed for
the master thesis "A Parallel Relation-Based Algorithm for Symbolic Bisimulation Minimization".
For more information on the SigrefMC package read the other README file.

Algorithms and BDD operations
=============================
The "bisim" and "bisim2" algorithms and the "converse" BDD operation can be found in /tool/src/bisim_lts2.cpp
The "forall_preimage" and "relcomp" BDD operations can be found in /tool/sylvan/src/sylvan_bdd.c

Experiment
==========
The original experiment from the SigrefMC package has been altered such that it only runs the algorithms
"bisim", "bisim2", and the sigrefmc algorithm for strong bisimulation on LTSs.

To reproduce the results, start with a clean `out` directory and run:

```
exp.py run
```

Note that the memory requirements for both the unique table and operation cache is set to 84GB. This can be
adjusted in the /tool/src/sigrefmc.cpp file
