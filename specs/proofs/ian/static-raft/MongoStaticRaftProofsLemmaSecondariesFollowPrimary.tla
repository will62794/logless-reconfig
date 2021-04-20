------------------- MODULE MongoStaticRaftProofsLemmaSecondariesFollowPrimaries ---------------

\* Finding inductive invariants for MongoStaticRaft protocol.

EXTENDS MongoStaticRaft, MongoStaticRaftProofsLemmaBasic, SequenceTheorems, FunctionTheorems, FiniteSetTheorems


LemmaSecondariesFollowPrimary ==
    /\ LemmaBasic
    /\ SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
    /\ SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm

AXIOM PrimaryAndSecondaryAreDifferent == Primary # Secondary
AXIOM ServerIsFinite == IsFiniteSet(Server)

THEOREM EXCEPT_Eq ==
ASSUME NEW f,
       NEW k \in DOMAIN f, NEW u
PROVE [f EXCEPT![k] = u][k] = u
PROOF OBVIOUS

THEOREM EXCEPT_Neq ==
ASSUME NEW f, NEW k, NEW u,
       NEW g, g = [f EXCEPT![k] = u]
PROVE \A i \in DOMAIN g : i # k => g[i] = f[i]
PROOF OBVIOUS

THEOREM EXCEPT_Domain ==
ASSUME NEW f, NEW k \in DOMAIN f, NEW u,
       NEW g, g = [f EXCEPT![k] = u]
PROVE DOMAIN g = DOMAIN f
PROOF OBVIOUS


-----------------------------------------------------------------------------------

(* Overall Result *)

THEOREM LemmaBasicAndNext ==
ASSUME TypeOK, LemmaBasic, Next
PROVE TypeOK' /\ LemmaBasic'
PROOF BY InitImpliesTypeOK, InitImpliesLemmaBasic, TypeOKAndNext,
         CurrentTermAtLeastAsLargeAsLogTermsForPrimaryAndNext,
         TermsOfEntriesGrowMonotonicallyAndNext,
         OnePrimaryPerTermAndNext,
         NonZeroLogsImplyExistsPrimaryAndNext,
         AllSecondariesImplyInitialStateAndNext,
         LargestPrimaryMustHaveAQuorumInTermAndNext,
         LogsMustBeSmallerThanOrEqualToLargestTermAndNext,
         AllConfigsAreServerAndNext
      DEF LemmaBasic

THEOREM LemmaBasicIsInductiveInvariant ==
ASSUME TRUE
PROVE /\ Init => (TypeOK /\ LemmaBasic)
      /\ (TypeOK /\ LemmaBasic /\ Next) => (TypeOK /\ LemmaBasic)'
PROOF BY InitImpliesTypeOK, InitImpliesLemmaBasic, TypeOKAndNext, LemmaBasicAndNext

=============================================================================

