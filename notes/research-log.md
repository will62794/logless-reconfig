# Research Log

## 2021-01-25

Working on defining the refinement mapping between MongoLoglessDynamicRaft and MongoSafeWeakRaft. Noticed a quirk of how `IsNewerConfig` is defined, which allows configs to be >= i.e.
```tla
IsNewerConfig(i, j) ==
    \/ configTerm[i] > configTerm[j]
    \/ /\ configTerm[i] = configTerm[j]
       /\ configVersion[i] >= configVersion[j]
```
If we change this to be strictly greater than, it appears to create a liveness issue i.e. the protocol deadlocks in all initial states. Would like to understand why this is occurring. It seems like it may have to do with the fact that `SendConfig` implicitly allows for term updates if `IsNewerConfig` allows the action to be taken even when configs are equal:
```tla
SendConfig(i, j) ==
    (* PRE *)
    /\ state[j] = Secondary
    /\ IsNewerConfig(i, j)
    (* POST *)
    /\ UpdateTerms(i, j)
    /\ configVersion' = [configVersion EXCEPT ![j] = configVersion[i]]
    /\ configTerm' = [configTerm EXCEPT ![j] = configTerm[i]]
    /\ config' = [config EXCEPT ![j] = config[i]]
```
Turns out it was actually due to the definition of `CanVoteForConfig`, which limited candidates to only vote for those in strictly newer configs:
```tla
CanVoteForConfig(i, j, term) ==
    /\ currentTerm[i] < term
    /\ IsNewerConfig(j, i)
```

Outstanding question: does `SendConfig` need to update terms of each nodes for safety, or is it only needed for a liveness condition?

To define the refinement mapping from *MongoLoglessDynamicRaft* to *MongoSafeWeakRaft*, I have defined *MongoLoglessDynamicRaftRefinement*, which extends *MongoLoglessDynamicRaft* to include auxiliary variables for defining this refinement mapping. We can check the refinement *MongoLoglessDynamicRaft => MongoSafeWeakRaft* using this spec, in addition to checking that the *WeakQuorumCondition* holds, which can be simply checked as an invariant.

Considering utilize the *TermSafetyCondition* directly instead of using the more concrete *WeakQuorumCondition*. I have given an initial TLA+ definition here:

```tla
\* Term Safety Condition

\* If an election has occurred in term T, no other elections can ever occur in term T.
T1 == \A e1,e2 \in elections : (e1.term = e2.term) => (e1.leader = e2.leader)

\* If an election has occurred in term T, no primary can ever commit in a term < T.
T2 == \A e \in elections : \A s \in Server : 
        (state[s] = Primary /\ currentTerm[s] < e.term) => \A Q \in MWR!QuorumsAt(s) : ~ENABLED MWR!CommitEntry(s, Q)

\* If an entry E has been committed in term T, any leader in term > T will contain the entry in its log.
T3 == \A s \in Server : \A c \in committed :
        (state[s]=Primary /\ c.term < currentTerm[s]) => MWR!InLog(c.entry, s)
```

## 2021-01-29

### Soundness of our Specification Abstractions

In a fail-stop, asynchronous, message passing system model, nodes communicate by sending messages over the network, and nodes can fail by stopping at any time. The basic, defining characteristics of this model include the following:

- Node failure
- Message loss/duplication
- Message Delay (Asynchrony)

Let's consider how each of these aspects affect reasoning about correctness and verification of a system and how it's treated in our abstract TLA+ specs.

**Node Failure**

If a node fails and recovers at some later point, this should be equivalent to a behavior where the node simply did not send or receive any message for some period of time, which is always possible in the non-deterministic specification i.e. the model checker will always explore behaviors where a certain node is "unscheduled" (doesn't execute any actions) for an arbitrary period of time. If too many nodes stay permanently failed, this obviously presents liveness issues, but we are focused on safety verification.

**Message Loss**

If a node A sends a message to node B in an asynchronous network, this message could be lost. If the sending of a message does not modify any local state of node A, though (i.e. it only modifies the network), then this (send, drop) pair of events are effectively nilpotent i.e they have no effect on the state of nodes, which is what matters for safety. That is, it's equivalent to the node having never sent a message at all, which are scenarios that are covered by the model checker i.e. it just chooses not to schedule a certain action. Message loss is important to consider when reasoning about liveness/progress, but we are concerned with safety.

**Message Duplication**

If the network can spontaneously duplicate messages, does this present any fundamentally new considerations for modeling/verification? It seems like message duplication would about checking idempotency issues i.e. if a node processing the same message would lead to bugs. It seems like this idempotency is sort of implicitly verified in our specs simply by action preconditions i.e. if an action precondition is "not idempotent" meaning it could allow the same action A to occur twice in a row, the model checker would exercise this case, in behaviors where such actions occur repeatedly. Could think about this more but it doesn't feel too problematic.

**Message Delay (Asynchrony)**

A big difference is that our specification models message transmission synchronously i.e. there is no separation between a 'send' and 'receive' event. In the fully asynchronous model, this means that a node may be able to receive a stale message i.e. one from arbitrarily far back in the past, though our specification doesn't model this explicitly through an async network. represent this. But, our models should actually exercise cases where nodes can hear about arbitrarily stale information e.g. if there is some node that is "partitioned" (conceptually), and it's state has not been updated in many transitions. At a later time, it could then try to communicate with another node, which would seem to be nearly equivalent to the case of a stale message hanging around in the network indefinitely and being delivered at a later time.

Is this important? TODO: Something about monotonicity?????

In our spec, SendConfig/BecomeLeader are the two actions that model message send/receipt. Let's examine SendConfig. We know that for SendConfig, nodes will only accept configurations newer than their own. Messages coming from arbitrarily far back in the past could be modeled in our spec by nodes that are indefinitely stale i.e. they have become "partitioned" and haven't updated their state in arbitrarily long. I think this should be sufficient in our model to capture these "stale" messages cases. 

**Atomic Elections**

The BecomeLeader action is modeled as a single atomic action, rather than a round of separate vote requests and responses. How does this affect soundness? It does model the case of two concurrent primaries, but it doesn't model the case of two  elections happening concurrently. If two elections were happening concurrently in two non overlapping configs, this could be a problem? 

```
|------| E1
    |------| E2
```
What happens if two elections overlap?

## 2021-05-31

Stavros' summary of today's discussion and current progress:

1. we have two protocols, which i will call MongoStaticRaftWithOutLogMatching (MSR) and MongoStaticRaftWithLogMatching (MSRLM)
2. we have a property which i will call Ian's Inductive Invariant (I3)
3. Ian has proven that I3 is indeed an inductive invariant for MSR
4. Ian will also prove that I3 is an inductive invariant for MSRLM
5. we have two safety properties, which I will call StateMachineSafety (SMS), and LogMatchingSafety (LMS)
6. Ian believes that I3 implies SMS and is in the process of proving that
7. Ian believes that I3 does not imply LMS
8. we have another protocol called MongoRaftReconfig (MRR) 
9. we have another property, which i will call Will's Inductive Invariant (W2)
10. we believe that W2 is an inductive invariant for MRR but this remains to be shown
11. we also believe that W2 implies SMS but this also remains to be seen
12. it seems that W2 implies LMS because LMS is one of the conjuncts of W2 

Ian will now prioritize 4 and 6, and then start with 10, 11, 12.

## 2021-06-10

Had a thought about checking inductive invariants automatically using TLAPS. As it's currently designed, you can try to use TLAPS to automatically prove that an invariant is inductive, but, in practice it seems that the backend solvers will likely be overwhelmed for any non-trivial invariants (see [note](https://groups.google.com/g/tlaplus/c/pZN-48a8Lrs) here). Giving the entire inductive invariant to TLAPS to prove is a big query for the backend SMT solvers, and by default [TLAPS gives the solver a timeout](https://tla.msr-inria.inria.fr/tlaps/content/Documentation/Tutorial/Tactics.html) of 5 seconds before returning a failure to the user. This timeout can be be increased manually, but it may not always be clear how big to make it. On the other hand, proving an inductive invariant can usually be decomposed into several, smaller sub-problems. Consider an invariant we want to show is inductive:

```tla
Ind == 
    /\ S
    /\ C1
    /\ C2
    /\ C3
```

with transition relation `Next` defined as:

```tla
Next ==
    \/ A1
    \/ A2
    \/ A3
```
where `A1,A2,A3` are disjoint actions of the protocol. Proving inductiveness requires establishing validity of the formula:

```tla
Ind /\ Next => Ind'  (1)
```
We can break this down into smaller queries, though, by substituting definitions of the property and the transition relation:

```tla
Ind /\ Next => Ind'
Ind /\ (A1 \/ A2 \/ A3) => Ind'
(S /\ C1 /\ C2 \/ C3) /\ (A1 \/ A2 \/ A3) => (S /\ C1 /\ C2 \/ C3)'   (2)
```
We do a basic, naive logical decomposition of formula (2), which gives the following 12 subgoals:
```tla
(S /\ C1 /\ C2 \/ C3) /\ A1 => S'
(S /\ C1 /\ C2 \/ C3) /\ A1 => C1'
(S /\ C1 /\ C2 \/ C3) /\ A1 => C2'
(S /\ C1 /\ C2 \/ C3) /\ A1 => C3'

(S /\ C1 /\ C2 \/ C3) /\ A2 => S'
(S /\ C1 /\ C2 \/ C3) /\ A2 => C1'
(S /\ C1 /\ C2 \/ C3) /\ A2 => C2'
(S /\ C1 /\ C2 \/ C3) /\ A2 => C3'

(S /\ C1 /\ C2 \/ C3) /\ A3 => S'
(S /\ C1 /\ C2 \/ C3) /\ A3 => C1'
(S /\ C1 /\ C2 \/ C3) /\ A3 => C2'
(S /\ C1 /\ C2 \/ C3) /\ A3 => C3'
```
I wonder if, in some/many cases, if you do this mechanical decomposition and pass each of these smaller goals to TLAPS to check automatically, how many it succeeds on. It's very possible that if you give the full, monolithic formula (1) to TLAPS, the best SMT solvers (e.g. Z3) will already be smart enough to do this kind of case decomposition internally, but it may also be the case that they would need a much higher timeout than the default 5 seconds to work through all cases. So, maybe you could try just increasing the timeout to a large amount. On the other hand, the benefit of this mechanical case decomposition is that, if some cases can be proved automatically and others can't, it gives you a better sense of where the backend solver is struggling. That is, it provides more of an "incremental" way to work through proof obligations for the user. Note that the TLA+ Toolbox should be able to do most of this kind of case decomposition automatically i.e. the Toolbox has a "Decompose Proof" command which should let you automatically break down disjunctions/conjunctions like the case described above.

Another note on this in relation to other tools that discover and/or check inductive invariants (e.g. [ic3po](https://github.com/aman-goel/ic3po), [ivy](https://cs.stanford.edu/~padon/ivy.pdf), [mypyvy](https://github.com/wilcoxjay/mypyvy)). At the end of the day, checking that an invariant is inductive seems to boil down to a basic problem of checking validity of a first order logic formula (at least for most standard system modeling paradigms that don't use some crazy logics or something). As far as I understand, all of the tools listed use an SMT solver (Z3 in most cases, it seems) to check the validity of such a formula. For infinite state systems, there seems no way to get around this in general i.e. checking the validity of such a formula is undecidable so an SMT solver seems the best (or only) approach. For finite state systems, the problem technically becomes decidable (I believe it's [coNP-complete](https://www.di.ubi.pt/~desousa/2012-2013/CF/ValidityChecking.pdf)?), but it may still be too hard to feasibly check efficiently. Although the problem is undecidable in the general case, it seems you can get clever and try to find special cases where the problem is decidable, or at least more "efficient" to check. This is part of the [cleverness](http://microsoft.github.io/ivy/decidability.html) of Ivy. The underlying problem (checking inductive invariance) remains the same, but Ivy restricts your modeling language in a way that makes things decidable. There's still a question, though, of how you know whether your problem can be suitably modeled inside this decidable "fragment" of logic. This seems a tricky rough edge of Ivy, and, if viewed from a critical perspective, it might be argued that the whole "decidable fragment" approach to some extent pushes some burden off of the SMT solver and onto the human, in the sense that the human now has an extra task of potentially figuring out how to model things in a "decidable" way. I've tried reading portions of Ivy's [documentation](http://microsoft.github.io/ivy/decidability.html) on this, and it seems very much non-trivial (e.g. see [*Paxos Made EPR*](https://dl.acm.org/doi/10.1145/3140568)). If you get lucky, though, perhaps your system naturally falls into this fragment and you're good to go. This seems to be part of the premise of Ivy's real world applicability i.e. there are a fair number of interesting systems that fall into this category. Ultimately, though, the tradeoffs of Ivy's approach are understandable, since it seems you always have to contend with the underlying undecidability of the problem in some clever way. For Ivy, it's about changing the modeling paradigm. For ic3po, I suppose it's about reasoning in finite domains and hoping that the results generalize to infinite domains. With TLA+ and TLC, there is yet another possible approach/heuristic, which is providing [probabilistic guarantees](https://lamport.azurewebsites.net/tla/inductive-invariant.pdf) of inductiveness. It may give you a reasonable level of confidence your invariant is inductive, but not a proof of that fact.

A couple of comments by Stavros (feel free to remove from here if you don't want them here): 
1. yes indeed we should definitely try the decomposition method you outline above! in fact we should time for a non-trivial invariant (e.g., MongoStaticRaft or some other) how much time the "monolithic" method takes (I suppose this is the current method we use) vs. how much total time the "decompositional" method as outlined above by Will takes. Ian: could you please do that?
2. for finite-state systems checking inductiveness can in principle be reduced to SAT (Boolean, not SMT) solving
3. decidable is great, but some decidable problems are still hard to compute in practice. without having looked at Ivy, it would be interesting to find out what it can do, even for its decidable fragment.

## 2021-08-06

In standard Raft, when an election in term T occurs, it serves to prevent two things:

1. Future elections in terms <= T.
2. Future commitment of writes in terms < T.

The first is ensured since any election must query the term of a quorum of nodes to garner votes. The second is ensured since any primary in term U that tries to commit a write must get it replicated to a quorum of nodes that are *all currently in term U*. So, if we move a quorum of nodes to a term newer than U, this primary can never commit writes in its own term again.

In the logless reconfig protocol, before allowing primaries to execute reconfigurations, there are two kinds of preconditions that must be satisfied. 

1. First, the current config of the primary must be replicated to a quorum of servers in that config. This serves to "disable" any older configs that overlap with it. This is ensured since part of the election precondition is that a candidate's config is newer than a voter's config. If we move a quorum of nodes in a config to that config, then it prevents any older configs that overlap with it from holding successful elections.
2. Second, older configs must be prevented from future commits. This can be done by moving a quorum of nodes in the config to the term of the current config (i.e. the primary).

Question: Even in standard Raft, does the quorum of nodes that replicate a write necessarily need to be the same as the quorum of nodes that record the term of that write? For example, if one quorum replicates a log entry (10,2), and a different quorum moves to current term 2, can the write of (10,2) safely be considered committed? Not clear on the answer.

## 2021-08-08

Alternate inductive invariant that uses the following two conjuncts

```tla
ActiveConfigSet == {s \in Server : ~ConfigDisabled(s)}

ActiveConfigsOverlap == 
    \A s,t \in ActiveConfigSet : QuorumsOverlap(config[s], config[t])

ActiveConfigsSafeAtTerms == 
    \A s \in Server : 
    \A t \in ActiveConfigSet :
        \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] >= configTerm[s]
```
instead of 
```tla
/\ NewerConfigDisablesOlderNonoverlappingConfigs
/\ NewerConfigDisablesTermsOfOlderNonDisabledConfigs
```
appears to be valid using TLC to check inductiveness even with four nodes. Will have to run further to make sure.

## 2021-08-19

Idea: Once you've developed an inductive invariant, use the model checker to help you do a manual proof by automatically checking *which* conjuncts of the inductive invariant a particular conjunct depends on. Theoretically helps you to know exactly which facts are needed to prove a particular conjunct.

## 2021-08-21

Can add `ConfigsNonEmpty` conjunct to latest version of `IndAlt` inductive invariant and it doesn't break things. So, it seems it's possible to take it or leave it. May consider including it since configs being non empty seems like a basic invariant we should establish.

Examples of log states that satisfy `LogMatching` but not `TermsOfEntriesGrowMonotonically`:

```tla
/\ log = (n1 :> <<1, 2>> @@ n2 :> <<2, 1>> @@ n3 :> <<2, 0>>)
/\ log = (n1 :> <<1>> @@ n2 :> <<0, 1>> @@ n3 :> <<2, 0>>)
/\ log = (n1 :> <<1>> @@ n2 :> <<1>> @@ n3 :> <<1, 0>>)
/\ log = (n1 :> <<2, 0>> @@ n2 :> << >> @@ n3 :> << >>)
/\ log = (n1 :> <<2, 0>> @@ n2 :> <<1, 1>> @@ n3 :> <<1, 1>>)
/\ log = (n1 :> <<2, 0>> @@ n2 :> <<1, 2>> @@ n3 :> << >>)
/\ log = (n1 :> <<2, 0>> @@ n2 :> <<1>> @@ n3 :> <<0>>)
/\ log = (n1 :> <<2, 0>> @@ n2 :> <<2, 0>> @@ n3 :> <<0>>)
/\ log = (n1 :> <<2, 0>> @@ n2 :> <<2, 0>> @@ n3 :> <<1, 1>>)
/\ log = (n1 :> <<2, 0>> @@ n2 :> <<2, 0>> @@ n3 :> <<2, 0>>)
/\ log = (n1 :> <<2, 1>> @@ n2 :> << >> @@ n3 :> <<0, 0>>)
/\ log = (n1 :> <<2, 1>> @@ n2 :> <<0>> @@ n3 :> <<0>>)
/\ log = (n1 :> <<2, 1>> @@ n2 :> <<1>> @@ n3 :> <<1>>)
/\ log = (n1 :> <<2, 1>> @@ n2 :> <<2, 1>> @@ n3 :> <<0, 0>>)
/\ log = (n1 :> <<2, 1>> @@ n2 :> <<2, 1>> @@ n3 :> <<1, 2>>)
/\ log = (n1 :> <<2, 1>> @@ n2 :> <<2, 1>> @@ n3 :> <<2, 0>>)
/\ log = (n1 :> <<2, 1>> @@ n2 :> <<2, 1>> @@ n3 :> <<2, 1>>)
/\ log = (n1 :> <<2, 1>> @@ n2 :> <<2>> @@ n3 :> <<2, 2>>)
/\ log = (n1 :> <<2, 2>> @@ n2 :> <<1, 0>> @@ n3 :> << >>)
/\ log = (n1 :> <<2, 2>> @@ n2 :> <<1, 0>> @@ n3 :> <<0, 1>>)
/\ log = (n1 :> <<2, 2>> @@ n2 :> <<1, 0>> @@ n3 :> <<1, 0>>)
/\ log = (n1 :> <<2>> @@ n2 :> <<0, 1>> @@ n3 :> <<2, 0>>)
/\ log = (n1 :> <<2>> @@ n2 :> <<1,
/\ log = (n1 :> <<2>> @@ n2 :> <<1, 0>> @@ n3 :> <<1, 0>>)
/\ log = (n1 :> <<2>> @@ n2 :> <<1, 0>> @@ n3 :> <<2, 1>>)
```
Examples of states that satisfy `LogMatching /\ TermsOfEntriesGrowMonotonically` but not `UniformLogEntriesInTerm`:

```tla
/\ log = (n1 :> << >> @@ n2 :> <<0, 1>> @@ n3 :> <<1, 2>>)
/\ log = (n1 :> <<0, 1>> @@ n2 :> <<0, 1>> @@ n3 :> <<1>>)
/\ log = (n1 :> <<0, 1>> @@ n2 :> <<1>> @@ n3 :> <<2>>)
/\ log = (n1 :> <<0, 2>> @@ n2 :> <<0, 0>> @@ n3 :> <<2>>)
/\ log = (n1 :> <<0, 2>> @@ n2 :> <<2>> @@ n3 :> <<2>>)
/\ log = (n1 :> <<0>> @@ n2 :> <<0, 1>> @@ n3 :> <<1, 2>>)
/\ log = (n1 :> <<0>> @@ n2 :> <<2>> @@ n3 :> <<0, 2>>)
/\ log = (n1 :> <<1, 2>> @@ n2 :> <<0, 0>> @@ n3 :> <<0, 1>>)
/\ log = (n1 :> <<1>> @@ n2 :> << >> @@ n3 :> <<0, 1>>)
/\ log = (n1 :> <<2>> @@ n2 :> <<1, 2>> @@ n3 :> <<1>>)
/\ log = (n1 :> <<2>> @@ n2 :> <<2>> @@ n3 :> <<1, 2>>)
```

Examples of states that satisfy `LogMatching /\ TermsOfEntriesGrowMonotonically /\ UniformLogEntriesInTerm`:

```tla
/\ log = (n1 :> <<0, 1, 1>> @@ n2 :> <<0, 1, 1>> @@ n3 :> <<0, 0>>)
/\ log = (n1 :> << >> @@ n2 :> <<1, 2>> @@ n3 :> <<1>>)
/\ log = (n1 :> <<2, 2, 2>> @@ n2 :> <<0, 1, 1>> @@ n3 :> <<2, 2, 2>>)
/\ log = (n1 :> <<0>> @@ n2 :> <<0, 1, 1>> @@ n3 :> <<2>>)
/\ log = (n1 :> <<0, 2, 2>> @@ n2 :> <<1, 1>> @@ n3 :> <<0>>)
/\ log = (n1 :> <<1>> @@ n2 :> <<2, 2>> @@ n3 :> <<1, 1>>)
/\ log = (n1 :> << >> @@ n2 :> <<2, 2>> @@ n3 :> <<0, 0>>)
/\ log = (n1 :> << >> @@ n2 :> <<2>> @@ n3 :> <<2, 2>>)
/\ log = (n1 :> <<1>> @@ n2 :> <<1>> @@ n3 :> <<2, 2>>)
```

## 2021-08-22

`OnePrimaryPerTerm` doesn't appear to depend directly on `ActiveConfigsOverlap`. That is, if all other conjuncts of the `OnePrimaryPerTerm` inductive invariant hold, there doesn't appear to be any 1-step counterexamples to induction that violate `OnePrimaryPerTerm`. Would need to check this more thoroughly, but this would align with what appeared in the manual proof i.e. proof of `OnePrimaryPerTerm` didn't utilize `ActiveConfigsOverlap` lemma.

## 2021-08-23

Updating the main spec to use the `ConfigCommittedAlt` definition for `Reconfig` precondition, which is how it is being explained in the paper. Also modifying `MongoStaticRaft` spec to include "prefix committed" entries in the commited set when we commit an entry via a `CommitEntry` action. Note that the prefix commitment change may affect the inductive invariant that was developed. It may need to be modified slightly.

## 2021-08-31

Discovered a minor anomaly that now explains why the version of `OplogCommitment` used to look the way it did. The latest definition was as follows:

```tla
OplogCommitment(s) == 
    \* The primary has committed at least one entry in its term.
    /\ \E c \in committed : (c.term = currentTerm[s])
    \* All entries committed in the primary's term are committed in its current config.
    /\ \A c \in committed : (c.term = currentTerm[s]) => IsCommitted(c.entry[1], s)
```
The first condition requires that some entry is committed in the term of a primary before it can satisfy `OplogCommitment` and do a reconfig. But, in the case where no log entries have been committed yet (i.e. `committed = {}`), it should be safe to do the reconfiguration even if no entries have been committed in the term of the primary yet. This gives the alternate definition:
```tla
OplogCommitment(s) == 
    \* The primary has committed at least one entry in its term.
    /\ (committed # {}) => \E c \in committed : (c.term = currentTerm[s])
    \* All entries committed in the primary's term are committed in its current config.
    /\ \A c \in committed : (c.term = currentTerm[s]) => IsCommitted(c.entry[1], s)
```
This was interacting oddly with models whose state constraint sets `MaxLogLen=0`. It was not allowing reconfigurations to occur unless some log entries were written.

## 2021-09-13

[Ind](https://github.com/will62794/logless-reconfig/blob/dcf172d0f08184df9bb607aa1954635dc2d989e2/specs/proofs/ian/mrr/MRRIndProof/Defs.tla#L236) is now proved to be inductive invariant for MongoRaftReconfig.  The entire proof is contained within the [MRRIndProof](https://github.com/will62794/logless-reconfig/tree/master/specs/proofs/ian/mrr/MRRIndProof) folder, and the top level theorem is [IndIsInductiveInvariant](https://github.com/will62794/logless-reconfig/blob/dcf172d0f08184df9bb607aa1954635dc2d989e2/specs/proofs/ian/mrr/MRRIndProof/IndProof.tla#L82).  Two additional notes:
1. The MongoRaftReconfig transition relation needs to be synced with the latest version.  It's close but I believe there's at least a few small differences.  
1. Ideally I would like to prove the three unproven [quorum lemmas](https://github.com/will62794/logless-reconfig/blob/dcf172d0f08184df9bb607aa1954635dc2d989e2/specs/proofs/ian/mrr/MRRIndProof/Lib.tla#L152) in Lib.tla.  They're obvious results but I still think they are worth trying to prove.  

## 2021-09-16

Will has been able to check the following proof modules locally with TLAPS from the Toolbox (i.e. they've gone green):

- AuxLemmas
- BasicQuorumsLib
- ElectionSafetyLemmas
- IndProof
- MRRTheorems
- LeaderCompletenessLemmas
- LeaderCompletenessLemmasCtd
- LogPropertiesLemmas
- Lib (except for yellow QuorumsIdentical and QuorumsOverlapIdentical, but I think we are just assuming thm)

We can also check each module containing proofs from the command line using TLAPS. This helps to give a more precise sense of how long a set of theorems takes to prove from scratch for TLAPS on a given machine. Here is an example command to check the proofs in a module from scratch (removing any existing fingerprints), and have it report timing statistics:
```
tlapm -v --cleanfp --timing -I ../ IndProof.tla
```
and an abbreviated sample output showing timing statistics:
```
(* created new "IndProof.tlaps/IndProof.thy" *)
(* fingerprints written in "IndProof.tlaps/fingerprints" *)
(*      operation | time (seconds) *)
(* ---------------+--------------- *)
(*        parsing | 0.300884       *)
(*       analysis | 0.398562       *)
(*     generation | 0.000000       *)
(* simplification | 0.000042       *)
(*     formatting | 0.000000       *)
(*    interaction | 80.257432      *)
(*       checking | 0.000000       *)
(*     fp_loading | 0.000000       *)
(*      fp_saving | 0.000000       *)
(*     fp_compute | 0.000000       *)
(*          other | 0.046104       *)
(* ---------------+--------------- *)
(*          total | 81.003029      *)
```
Time to check latest version of proofs from command line on 8-core 2020 M1 Macbook Air, using following commands:

```bash
tlapm --stretch 2 -v --cleanfp --timing -I ../ AuxLemmas.tla
tlapm --stretch 2 -v --cleanfp --timing -I ../ BasicQuorumsLib.tla
tlapm --stretch 2 -v --cleanfp --timing -I ../ ElectionSafetyLemmas.tla
tlapm --stretch 2 -v --cleanfp --timing -I ../ IndProof.tla
tlapm --stretch 2 -v --cleanfp --timing -I ../ LeaderCompletenessLemmas.tla
tlapm --stretch 2 -v --cleanfp --timing -I ../ LeaderCompletenessLemmasCtd.tla
tlapm --stretch 2 -v --cleanfp --timing -I ../ LeaderCompletenessLemmasLib.tla
tlapm --stretch 2 -v --cleanfp --timing -I ../ Lib.tla
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ LogPropertiesLemmas.tla
tlapm --toolbox 0 0 --stretch 3 -v --cleanfp --timing -I ../ MRRTheorems.tla
```

| Module  | Time (seconds) |
| ------------- | ------------- |
| AuxLemmas.tla  | 15  |
| BasicQuorumsLib.tla  | 17  |
| ElectionSafetyLemmas.tla  | 469  |
| IndProof.tla  | 80  |
| LeaderCompletenessLemmas.tla  | 250  |
| LeaderCompletenessLemmasCtd.tla  | 331  |
| LeaderCompletenessLib.tla  | 241  |
| Lib.tla  | 128  |
| LogPropertiesLemmas.tla  | 669 |
| MRRTheorems.tla  | 110  |
| **Total** | 2310 | 

## 2021-09-19

Proof checking times with latest version of the repo, using these commands on M1 Macbook Air:

```bash
tlapm --toolbox 0 0 --stretch 2 -v --cleanfp --timing -I ../ AuxLemmas.tla
tlapm --toolbox 0 0 --stretch 2 -v --cleanfp --timing -I ../ BasicQuorumsLib.tla
tlapm --toolbox 0 0 --stretch 2 -v --cleanfp --timing -I ../ ElectionSafetyLemmas.tla
tlapm --toolbox 0 0 --stretch 2 -v --cleanfp --timing -I ../ LeaderCompletenessLemmas.tla
tlapm --toolbox 0 0 --stretch 2 -v --cleanfp --timing -I ../ LeaderCompletenessLib.tla
tlapm --toolbox 0 0 --stretch 2 -v --cleanfp --timing -I ../ Lib.tla
tlapm --toolbox 0 0 --stretch 2 -v --cleanfp --timing -I ../ LogLemmas.tla
tlapm --toolbox 0 0 --stretch 2 -v --cleanfp --timing -I ../ MongoRaftReconfigProofs.tla
tlapm --toolbox 0 0 --stretch 2 -v --cleanfp --timing -I ../ StateMachineSafetyLemmas.tla
tlapm --toolbox 0 0 --stretch 2 -v --cleanfp --timing -I ../ TypeOK.tla
```

| Module  | Time (seconds) |
| ------------- | ------------- |
| AuxLemmas.tla  | 14  |
| BasicQuorumsLib.tla  | 16  |
| ElectionSafetyLemmas.tla  | 438  |
| LeaderCompletenessLemmas.tla  | 575 |
| LeaderCompletenessLib.tla  | 224 |
| Lib.tla  | 115 |
| LogLemmas.tla  | 615 |
| MongoRaftReconfigProofs.tla  | 86  |
| StateMachineSafetyLemma.tla  | 67  |
| TypeOK.tla  | 14  |
| **Total** | 2164 | 

2164 seconds = 36 minutes

## 2021-09-20

To zip up the Git repo:

```bash
git archive --format=zip --output=../repo.zip HEAD
```