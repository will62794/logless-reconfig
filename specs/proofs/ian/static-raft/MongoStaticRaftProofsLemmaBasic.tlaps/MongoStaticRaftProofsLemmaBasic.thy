(* automatically generated -- do not edit manually *)
theory MongoStaticRaftProofsLemmaBasic imports Constant Zenon begin
ML_command {* writeln ("*** TLAPS PARSED\n"); *}
consts
  "isReal" :: c
  "isa_slas_a" :: "[c,c] => c"
  "isa_bksl_diva" :: "[c,c] => c"
  "isa_perc_a" :: "[c,c] => c"
  "isa_peri_peri_a" :: "[c,c] => c"
  "isInfinity" :: c
  "isa_lbrk_rbrk_a" :: "[c] => c"
  "isa_less_more_a" :: "[c] => c"

lemma ob'131:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Server
fixes Secondary
fixes Primary
fixes Nil
fixes currentTerm currentTerm'
fixes state state'
fixes log log'
fixes config config'
fixes elections elections'
fixes committed committed'
(* usable definition vars suppressed *)
(* usable definition Empty suppressed *)
(* usable definition InLog suppressed *)
(* usable definition LastTerm suppressed *)
(* usable definition LastEntry suppressed *)
(* usable definition GetTerm suppressed *)
(* usable definition LogTerm suppressed *)
(* usable definition Quorums suppressed *)
(* usable definition QuorumsAt suppressed *)
(* usable definition CanRollback suppressed *)
(* usable definition CanVoteForOplog suppressed *)
(* usable definition ImmediatelyCommitted suppressed *)
(* usable definition UpdateTermsExpr suppressed *)
(* usable definition ClientRequest suppressed *)
(* usable definition GetEntries suppressed *)
(* usable definition RollbackEntries suppressed *)
(* usable definition CommitEntry suppressed *)
(* usable definition UpdateTerms suppressed *)
(* usable definition Init suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ElectionSafety suppressed *)
(* usable definition LeaderCompleteness suppressed *)
(* usable definition StateMachineSafety suppressed *)
(* usable definition EqualUpTo suppressed *)
(* usable definition LogMatching suppressed *)
(* usable definition Max suppressed *)
(* usable definition ExistsPrimary suppressed *)
(* usable definition AllConfigsAreServer suppressed *)
(* usable definition CurrentTermAtLeastAsLargeAsLogTermsForPrimary suppressed *)
(* usable definition TermsOfEntriesGrowMonotonically suppressed *)
(* usable definition OnePrimaryPerTerm suppressed *)
(* usable definition ExistsQuorumInLargestTerm suppressed *)
(* usable definition LogsMustBeSmallerThanOrEqualToLargestTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm suppressed *)
(* usable definition CommittedTermMatchesEntry suppressed *)
(* usable definition LogsLaterThanCommittedMustHaveCommitted suppressed *)
(* usable definition LogsEqualToCommittedMustHaveCommittedIfItFits suppressed *)
(* usable definition CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens suppressed *)
(* usable definition CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms suppressed *)
(* usable definition LeaderCompletenessGeneralized suppressed *)
(* usable definition CommittedEntriesMustHaveQuorums suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
fixes MaxLogLen
fixes MaxTerm
fixes NumRandSubsets
(* usable definition StateConstraint suppressed *)
(* usable definition LemmaBasic suppressed *)
assumes v'253: "((((currentTerm) \<in> ([(Server) \<rightarrow> (Nat)]))) & (((state) \<in> ([(Server) \<rightarrow> ({(Secondary), (Primary)})]))) & (((log) \<in> ([(Server) \<rightarrow> ((Seq ((Nat))))]))) & (((config) \<in> ([(Server) \<rightarrow> ((SUBSET (Server)))]))) & (((elections) \<in> ((SUBSET ([''leader'' : (Server), ''term'' : (Nat)]))))) & (((committed) \<in> ((SUBSET ([''entry'' : (((Nat) \<times> (Nat))), ''term'' : (Nat)]))))))"
assumes v'254: "(Next)"
assumes v'255: "((((currentTerm) \<in> ([(Server) \<rightarrow> (Nat)]))) & (((state) \<in> ([(Server) \<rightarrow> ({(Secondary), (Primary)})]))) & (((log) \<in> ([(Server) \<rightarrow> ((Seq ((Nat))))]))) & (((config) \<in> ([(Server) \<rightarrow> ((SUBSET (Server)))]))) & (((elections) \<in> ((SUBSET ([''leader'' : (Server), ''term'' : (Nat)]))))) & (((committed) \<in> ((SUBSET ([''entry'' : (((Nat) \<times> (Nat))), ''term'' : (Nat)]))))))"
assumes v'256: "(Next)"
assumes v'264: "(\<exists> s \<in> (Server) : (\<exists> Q \<in> ((QuorumsAt ((s)))) : ((((s) \<in> (Q))) & (\<forall> v \<in> (Q) : ((CanVoteForOplog ((v), (s), ((arith_add ((fapply ((currentTerm), (s))), ((Succ[0]))))))))) & ((((a_currentTermhash_primea :: c)) = ([ s_1 \<in> (Server)  \<mapsto> (cond((((s_1) \<in> (Q))), ((arith_add ((fapply ((currentTerm), (s))), ((Succ[0]))))), (fapply ((currentTerm), (s_1)))))]))) & ((((a_statehash_primea :: c)) = ([ s_1 \<in> (Server)  \<mapsto> (cond((((s_1) = (s))), (Primary), (cond((((s_1) \<in> (Q))), (Secondary), (fapply ((state), (s_1)))))))]))) & ((((a_electionshash_primea :: c)) = (((elections) \<union> ({(((''leader'' :> (s)) @@ (''term'' :> ((arith_add ((fapply ((currentTerm), (s))), ((Succ[0]))))))))}))))) & (((((a_loghash_primea :: c)) = ([(log) EXCEPT ![(s)] = ((Append ((fapply ((log), (s))), ((arith_add ((fapply ((currentTerm), (s))), ((Succ[0]))))))))]))) | ((((a_loghash_primea :: c)) = (log)))) & (((((a_confighash_primea :: c)) = (config))) & ((((a_committedhash_primea :: c)) = (committed)))))))"
fixes s
assumes s_in : "(s \<in> (Server))"
assumes v'269: "(\<exists> Q \<in> ((QuorumsAt ((s)))) : ((((s) \<in> (Q))) & (\<forall> v \<in> (Q) : ((CanVoteForOplog ((v), (s), ((arith_add ((fapply ((currentTerm), (s))), ((Succ[0]))))))))) & ((((a_currentTermhash_primea :: c)) = ([ s_1 \<in> (Server)  \<mapsto> (cond((((s_1) \<in> (Q))), ((arith_add ((fapply ((currentTerm), (s))), ((Succ[0]))))), (fapply ((currentTerm), (s_1)))))]))) & ((((a_statehash_primea :: c)) = ([ s_1 \<in> (Server)  \<mapsto> (cond((((s_1) = (s))), (Primary), (cond((((s_1) \<in> (Q))), (Secondary), (fapply ((state), (s_1)))))))]))) & ((((a_electionshash_primea :: c)) = (((elections) \<union> ({(((''leader'' :> (s)) @@ (''term'' :> ((arith_add ((fapply ((currentTerm), (s))), ((Succ[0]))))))))}))))) & (((((a_loghash_primea :: c)) = ([(log) EXCEPT ![(s)] = ((Append ((fapply ((log), (s))), ((arith_add ((fapply ((currentTerm), (s))), ((Succ[0]))))))))]))) | ((((a_loghash_primea :: c)) = (log)))) & (((((a_confighash_primea :: c)) = (config))) & ((((a_committedhash_primea :: c)) = (committed))))))"
fixes Q
assumes Q_in : "(Q \<in> ((QuorumsAt ((s)))))"
assumes v'274: "((((s) \<in> (Q))) & (\<forall> v \<in> (Q) : ((CanVoteForOplog ((v), (s), ((arith_add ((fapply ((currentTerm), (s))), ((Succ[0]))))))))) & (((((a_loghash_primea :: c)) = ([(log) EXCEPT ![(s)] = ((Append ((fapply ((log), (s))), ((arith_add ((fapply ((currentTerm), (s))), ((Succ[0]))))))))]))) | ((((a_loghash_primea :: c)) = (log)))))"
assumes v'275: "((((a_currentTermhash_primea :: c)) = ([ s_1 \<in> (Server)  \<mapsto> (cond((((s_1) \<in> (Q))), ((arith_add ((fapply ((currentTerm), (s))), ((Succ[0]))))), (fapply ((currentTerm), (s_1)))))])))"
assumes v'276: "((((a_statehash_primea :: c)) = ([ s_1 \<in> (Server)  \<mapsto> (cond((((s_1) = (s))), (Primary), (cond((((s_1) \<in> (Q))), (Secondary), (fapply ((state), (s_1)))))))])))"
assumes v'277: "((((a_electionshash_primea :: c)) = (((elections) \<union> ({(((''leader'' :> (s)) @@ (''term'' :> ((arith_add ((fapply ((currentTerm), (s))), ((Succ[0]))))))))})))))"
assumes v'278: "((((a_confighash_primea :: c)) = (config)))"
assumes v'279: "((((a_committedhash_primea :: c)) = (committed)))"
assumes v'288: "((((arith_add ((fapply ((currentTerm), (s))), ((Succ[0]))))) \<in> (Nat)))"
assumes v'289: "((\<And> a_log1a :: c. a_log1a \<in> ([(Server) \<rightarrow> ((Seq ((Nat))))]) \<Longrightarrow> (\<And> s_1 :: c. s_1 \<in> (Server) \<Longrightarrow> (\<And> n :: c. n \<in> (Nat) \<Longrightarrow> (\<And> a_log2a :: c. ((((a_log2a) = ([(a_log1a) EXCEPT ![(s_1)] = ((Append ((fapply ((a_log1a), (s_1))), (n))))]))) \<Longrightarrow> (((a_log2a) \<in> ([(Server) \<rightarrow> ((Seq ((Nat))))])))))))))"
shows "((((a_loghash_primea :: c)) \<in> ([(Server) \<rightarrow> ((Seq ((Nat))))])))"(is "PROP ?ob'131")
proof -
ML_command {* writeln "*** TLAPS ENTER 131"; *}
show "PROP ?ob'131"

(* BEGIN ZENON INPUT
;; file=MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_d015be.znn; winfile="`cygpath -a -w "MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_d015be.znn"`"; PATH='/usr/bin:/cygdrive/c/Program Files (x86)/Common Files/Oracle/Java/javapath:/cygdrive/c/WINDOWS/system32:/cygdrive/c/WINDOWS:/cygdrive/c/WINDOWS/System32/Wbem:/cygdrive/c/WINDOWS/System32/WindowsPowerShell/v1.0:/cygdrive/c/WINDOWS/System32/OpenSSH:/cygdrive/c/Program Files/Git/cmd:/cygdrive/c/Program Files/PuTTY:/cygdrive/c/Program Files/CMake/bin:/cygdrive/c/Program Files/Java/jdk-14.0.2/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32/Scripts:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32:/cygdrive/c/Users/ianda/AppData/Local/Microsoft/WindowsApps:/cygdrive/c/Users/ianda/AppData/Local/Programs/MiKTeX 2.9/miktex/bin/x64:/cygdrive/c/Program Files (x86)/GnuWin32/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Microsoft VS Code/bin:/cygdrive/c/MinGW/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_d015be.znn.out
;; obligation #131
$hyp "v'253" (/\ (TLA.in currentTerm (TLA.FuncSet Server arith.N))
(TLA.in state (TLA.FuncSet Server (TLA.set Secondary Primary))) (TLA.in log
(TLA.FuncSet Server (TLA.Seq arith.N))) (TLA.in config
(TLA.FuncSet Server (TLA.SUBSET Server))) (TLA.in elections
(TLA.SUBSET (TLA.recordset "leader" Server "term" arith.N)))
(TLA.in committed
(TLA.SUBSET (TLA.recordset "entry" (TLA.prod arith.N arith.N) "term" arith.N))))
$hyp "v'254" Next
$hyp "v'255" (/\ (TLA.in currentTerm (TLA.FuncSet Server arith.N))
(TLA.in state (TLA.FuncSet Server (TLA.set Secondary Primary))) (TLA.in log
(TLA.FuncSet Server (TLA.Seq arith.N))) (TLA.in config
(TLA.FuncSet Server (TLA.SUBSET Server))) (TLA.in elections
(TLA.SUBSET (TLA.recordset "leader" Server "term" arith.N)))
(TLA.in committed
(TLA.SUBSET (TLA.recordset "entry" (TLA.prod arith.N arith.N) "term" arith.N))))
$hyp "v'256" Next
$hyp "v'264" (TLA.bEx Server ((s) (TLA.bEx (QuorumsAt s) ((Q) (/\ (TLA.in s
Q) (TLA.bAll Q ((v) (CanVoteForOplog v s
(arith.add (TLA.fapply currentTerm s) (TLA.fapply TLA.Succ 0)))))
(= a_currentTermhash_primea (TLA.Fcn Server ((s_1) (TLA.cond (TLA.in s_1
Q) (arith.add (TLA.fapply currentTerm s)
(TLA.fapply TLA.Succ 0)) (TLA.fapply currentTerm s_1)))))
(= a_statehash_primea (TLA.Fcn Server ((s_1) (TLA.cond (= s_1
s) Primary (TLA.cond (TLA.in s_1 Q) Secondary (TLA.fapply state s_1))))))
(= a_electionshash_primea (TLA.cup elections
(TLA.set (TLA.record "leader" s "term" (arith.add (TLA.fapply currentTerm s)
(TLA.fapply TLA.Succ 0)))))) (\/ (= a_loghash_primea
(TLA.except log s (TLA.Append (TLA.fapply log s)
(arith.add (TLA.fapply currentTerm s) (TLA.fapply TLA.Succ 0)))))
(= a_loghash_primea log)) (/\ (= a_confighash_primea config)
(= a_committedhash_primea
committed)))))))
$hyp "s_in" (TLA.in s Server)
$hyp "v'269" (TLA.bEx (QuorumsAt s) ((Q) (/\ (TLA.in s Q)
(TLA.bAll Q ((v) (CanVoteForOplog v s (arith.add (TLA.fapply currentTerm s)
(TLA.fapply TLA.Succ 0))))) (= a_currentTermhash_primea
(TLA.Fcn Server ((s_1) (TLA.cond (TLA.in s_1
Q) (arith.add (TLA.fapply currentTerm s)
(TLA.fapply TLA.Succ 0)) (TLA.fapply currentTerm s_1)))))
(= a_statehash_primea (TLA.Fcn Server ((s_1) (TLA.cond (= s_1
s) Primary (TLA.cond (TLA.in s_1 Q) Secondary (TLA.fapply state s_1))))))
(= a_electionshash_primea (TLA.cup elections
(TLA.set (TLA.record "leader" s "term" (arith.add (TLA.fapply currentTerm s)
(TLA.fapply TLA.Succ 0)))))) (\/ (= a_loghash_primea
(TLA.except log s (TLA.Append (TLA.fapply log s)
(arith.add (TLA.fapply currentTerm s) (TLA.fapply TLA.Succ 0)))))
(= a_loghash_primea log)) (/\ (= a_confighash_primea config)
(= a_committedhash_primea
committed)))))
$hyp "Q_in" (TLA.in Q (QuorumsAt s))
$hyp "v'274" (/\ (TLA.in s Q) (TLA.bAll Q ((v) (CanVoteForOplog v s
(arith.add (TLA.fapply currentTerm s) (TLA.fapply TLA.Succ 0)))))
(\/ (= a_loghash_primea (TLA.except log s (TLA.Append (TLA.fapply log s)
(arith.add (TLA.fapply currentTerm s) (TLA.fapply TLA.Succ 0)))))
(= a_loghash_primea log)))
$hyp "v'275" (= a_currentTermhash_primea
(TLA.Fcn Server ((s_1) (TLA.cond (TLA.in s_1
Q) (arith.add (TLA.fapply currentTerm s)
(TLA.fapply TLA.Succ 0)) (TLA.fapply currentTerm s_1)))))
$hyp "v'276" (= a_statehash_primea (TLA.Fcn Server ((s_1) (TLA.cond (= s_1
s) Primary (TLA.cond (TLA.in s_1
Q) Secondary (TLA.fapply state s_1))))))
$hyp "v'277" (= a_electionshash_primea (TLA.cup elections
(TLA.set (TLA.record "leader" s "term" (arith.add (TLA.fapply currentTerm s)
(TLA.fapply TLA.Succ 0))))))
$hyp "v'278" (= a_confighash_primea
config)
$hyp "v'279" (= a_committedhash_primea
committed)
$hyp "v'288" (TLA.in (arith.add (TLA.fapply currentTerm s)
(TLA.fapply TLA.Succ 0))
arith.N)
$hyp "v'289" (TLA.bAll (TLA.FuncSet Server (TLA.Seq arith.N)) ((a_log1a) (TLA.bAll Server ((s_1) (TLA.bAll arith.N ((n) (A. ((a_log2a) (=> (= a_log2a
(TLA.except a_log1a s_1 (TLA.Append (TLA.fapply a_log1a s_1)
n))) (TLA.in a_log2a
(TLA.FuncSet Server (TLA.Seq arith.N))))))))))))
$goal (TLA.in a_loghash_primea
(TLA.FuncSet Server (TLA.Seq arith.N)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((currentTerm \\in FuncSet(Server, Nat))&((state \\in FuncSet(Server, {Secondary, Primary}))&((log \\in FuncSet(Server, Seq(Nat)))&((config \\in FuncSet(Server, SUBSET(Server)))&((elections \\in SUBSET([''leader'' : (Server), ''term'' : (Nat)]))&(committed \\in SUBSET([''entry'' : (prod(Nat, Nat)), ''term'' : (Nat)])))))))" (is "?z_hp&?z_hu")
 using v'255 by blast
 have z_He:"bEx(QuorumsAt(s), (\<lambda>Q. ((s \\in Q)&(bAll(Q, (\<lambda>v. CanVoteForOplog(v, s, ((currentTerm[s]) + 1))))&((a_currentTermhash_primea=Fcn(Server, (\<lambda>s_1. cond((s_1 \\in Q), ((currentTerm[s]) + 1), (currentTerm[s_1])))))&((a_statehash_primea=Fcn(Server, (\<lambda>s_1. cond((s_1=s), Primary, cond((s_1 \\in Q), Secondary, (state[s_1]))))))&((a_electionshash_primea=(elections \\cup {(''leader'' :> (s) @@ ''term'' :> (((currentTerm[s]) + 1)))}))&(((a_loghash_primea=except(log, s, Append((log[s]), ((currentTerm[s]) + 1))))|(a_loghash_primea=log))&((a_confighash_primea=config)&(a_committedhash_primea=committed))))))))))" (is "?z_he")
 using v'269 by blast
 have z_Hd:"(s \\in Server)" (is "?z_hd")
 using s_in by blast
 have z_Hm:"(((currentTerm[s]) + 1) \\in Nat)" (is "?z_hm")
 using v'288 by blast
 have z_Hn:"bAll(FuncSet(Server, Seq(Nat)), (\<lambda>a_log1a. bAll(Server, (\<lambda>s_1. bAll(Nat, (\<lambda>n. (\\A a_log2a:((a_log2a=except(a_log1a, s_1, Append((a_log1a[s_1]), n)))=>(a_log2a \\in FuncSet(Server, Seq(Nat)))))))))))" (is "?z_hn")
 using v'289 by blast
 have zenon_L1_: "(~(a_loghash_primea \\in FuncSet(Server, Seq(Nat)))) ==> (log \\in FuncSet(Server, Seq(Nat))) ==> (a_loghash_primea=log) ==> FALSE" (is "?z_ho ==> ?z_hbc ==> ?z_hdo ==> FALSE")
 proof -
  assume z_Ho:"?z_ho" (is "~?z_heh")
  assume z_Hbc:"?z_hbc"
  assume z_Hdo:"?z_hdo"
  show FALSE
  proof (rule notE [OF z_Ho])
   have z_Hei: "(log=a_loghash_primea)"
   by (rule sym [OF z_Hdo])
   have z_Heh: "?z_heh"
   by (rule subst [where P="(\<lambda>zenon_Vpz. (zenon_Vpz \\in FuncSet(Server, Seq(Nat))))", OF z_Hei], fact z_Hbc)
   thus "?z_heh" .
  qed
 qed
 assume z_Ho:"(~(a_loghash_primea \\in FuncSet(Server, Seq(Nat))))" (is "~?z_heh")
 have z_Hu: "?z_hu" (is "?z_hv&?z_hbb")
 by (rule zenon_and_1 [OF z_Ha])
 have z_Hbb: "?z_hbb" (is "?z_hbc&?z_hbg")
 by (rule zenon_and_1 [OF z_Hu])
 have z_Hbc: "?z_hbc"
 by (rule zenon_and_0 [OF z_Hbb])
 have z_Hem_z_He: "(\\E x:((x \\in QuorumsAt(s))&((s \\in x)&(bAll(x, (\<lambda>v. CanVoteForOplog(v, s, ((currentTerm[s]) + 1))))&((a_currentTermhash_primea=Fcn(Server, (\<lambda>s_1. cond((s_1 \\in x), ((currentTerm[s]) + 1), (currentTerm[s_1])))))&((a_statehash_primea=Fcn(Server, (\<lambda>s_1. cond((s_1=s), Primary, cond((s_1 \\in x), Secondary, (state[s_1]))))))&((a_electionshash_primea=(elections \\cup {(''leader'' :> (s) @@ ''term'' :> (((currentTerm[s]) + 1)))}))&(((a_loghash_primea=except(log, s, Append((log[s]), ((currentTerm[s]) + 1))))|(a_loghash_primea=log))&((a_confighash_primea=config)&(a_committedhash_primea=committed)))))))))) == ?z_he" (is "?z_hem == _")
 by (unfold bEx_def)
 have z_Hem: "?z_hem" (is "\\E x : ?z_hfg(x)")
 by (unfold z_Hem_z_He, fact z_He)
 have z_Hfh: "?z_hfg((CHOOSE x:((x \\in QuorumsAt(s))&((s \\in x)&(bAll(x, (\<lambda>v. CanVoteForOplog(v, s, ((currentTerm[s]) + 1))))&((a_currentTermhash_primea=Fcn(Server, (\<lambda>s_1. cond((s_1 \\in x), ((currentTerm[s]) + 1), (currentTerm[s_1])))))&((a_statehash_primea=Fcn(Server, (\<lambda>s_1. cond((s_1=s), Primary, cond((s_1 \\in x), Secondary, (state[s_1]))))))&((a_electionshash_primea=(elections \\cup {(''leader'' :> (s) @@ ''term'' :> (((currentTerm[s]) + 1)))}))&(((a_loghash_primea=except(log, s, Append((log[s]), ((currentTerm[s]) + 1))))|(a_loghash_primea=log))&((a_confighash_primea=config)&(a_committedhash_primea=committed)))))))))))" (is "?z_hfj&?z_hfk")
 by (rule zenon_ex_choose_0 [of "?z_hfg", OF z_Hem])
 have z_Hfk: "?z_hfk" (is "?z_hfl&?z_hfm")
 by (rule zenon_and_1 [OF z_Hfh])
 have z_Hfm: "?z_hfm" (is "?z_hfn&?z_hfo")
 by (rule zenon_and_1 [OF z_Hfk])
 have z_Hfo: "?z_hfo" (is "?z_hfp&?z_hfq")
 by (rule zenon_and_1 [OF z_Hfm])
 have z_Hfq: "?z_hfq" (is "?z_hfr&?z_hdc")
 by (rule zenon_and_1 [OF z_Hfo])
 have z_Hdc: "?z_hdc" (is "?z_hj&?z_hdh")
 by (rule zenon_and_1 [OF z_Hfq])
 have z_Hdh: "?z_hdh" (is "?z_hdi&?z_hdp")
 by (rule zenon_and_1 [OF z_Hdc])
 have z_Hdi: "?z_hdi" (is "?z_hdj|?z_hdo")
 by (rule zenon_and_0 [OF z_Hdh])
 have z_Hfs_z_Hn: "(\\A x:((x \\in FuncSet(Server, Seq(Nat)))=>bAll(Server, (\<lambda>s_1. bAll(Nat, (\<lambda>n. (\\A a_log2a:((a_log2a=except(x, s_1, Append((x[s_1]), n)))=>(a_log2a \\in FuncSet(Server, Seq(Nat))))))))))) == ?z_hn" (is "?z_hfs == _")
 by (unfold bAll_def)
 have z_Hfs: "?z_hfs" (is "\\A x : ?z_hgf(x)")
 by (unfold z_Hfs_z_Hn, fact z_Hn)
 show FALSE
 proof (rule zenon_or [OF z_Hdi])
  assume z_Hdj:"?z_hdj" (is "_=?z_hdl")
  have z_Hgg: "?z_hgf(log)" (is "_=>?z_hgh")
  by (rule zenon_all_0 [of "?z_hgf" "log", OF z_Hfs])
  show FALSE
  proof (rule zenon_imply [OF z_Hgg])
   assume z_Hgi:"(~?z_hbc)"
   show FALSE
   by (rule notE [OF z_Hgi z_Hbc])
  next
   assume z_Hgh:"?z_hgh"
   have z_Hgj_z_Hgh: "(\\A x:((x \\in Server)=>bAll(Nat, (\<lambda>n. (\\A a_log2a:((a_log2a=except(log, x, Append((log[x]), n)))=>(a_log2a \\in FuncSet(Server, Seq(Nat))))))))) == ?z_hgh" (is "?z_hgj == _")
   by (unfold bAll_def)
   have z_Hgj: "?z_hgj" (is "\\A x : ?z_hgu(x)")
   by (unfold z_Hgj_z_Hgh, fact z_Hgh)
   have z_Hgv: "?z_hgu(s)" (is "_=>?z_hgw")
   by (rule zenon_all_0 [of "?z_hgu" "s", OF z_Hgj])
   show FALSE
   proof (rule zenon_imply [OF z_Hgv])
    assume z_Hgx:"(~?z_hd)"
    show FALSE
    by (rule notE [OF z_Hgx z_Hd])
   next
    assume z_Hgw:"?z_hgw"
    have z_Hgy_z_Hgw: "(\\A x:((x \\in Nat)=>(\\A a_log2a:((a_log2a=except(log, s, Append((log[s]), x)))=>(a_log2a \\in FuncSet(Server, Seq(Nat))))))) == ?z_hgw" (is "?z_hgy == _")
    by (unfold bAll_def)
    have z_Hgy: "?z_hgy" (is "\\A x : ?z_hhg(x)")
    by (unfold z_Hgy_z_Hgw, fact z_Hgw)
    have z_Hhh: "?z_hhg(((currentTerm[s]) + 1))" (is "_=>?z_hhi")
    by (rule zenon_all_0 [of "?z_hhg" "((currentTerm[s]) + 1)", OF z_Hgy])
    show FALSE
    proof (rule zenon_imply [OF z_Hhh])
     assume z_Hhj:"(~?z_hm)"
     show FALSE
     by (rule notE [OF z_Hhj z_Hm])
    next
     assume z_Hhi:"?z_hhi" (is "\\A x : ?z_hhk(x)")
     have z_Hhl: "?z_hhk(a_loghash_primea)"
     by (rule zenon_all_0 [of "?z_hhk" "a_loghash_primea", OF z_Hhi])
     show FALSE
     proof (rule zenon_imply [OF z_Hhl])
      assume z_Hhm:"(a_loghash_primea~=?z_hdl)"
      show FALSE
      by (rule notE [OF z_Hhm z_Hdj])
     next
      assume z_Heh:"?z_heh"
      show FALSE
      by (rule notE [OF z_Ho z_Heh])
     qed
    qed
   qed
  qed
 next
  assume z_Hdo:"?z_hdo"
  show FALSE
  by (rule zenon_L1_ [OF z_Ho z_Hbc z_Hdo])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 131"; *} qed
lemma ob'144:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Server
fixes Secondary
fixes Primary
fixes Nil
fixes currentTerm currentTerm'
fixes state state'
fixes log log'
fixes config config'
fixes elections elections'
fixes committed committed'
(* usable definition vars suppressed *)
(* usable definition Empty suppressed *)
(* usable definition InLog suppressed *)
(* usable definition LastTerm suppressed *)
(* usable definition LastEntry suppressed *)
(* usable definition GetTerm suppressed *)
(* usable definition LogTerm suppressed *)
(* usable definition Quorums suppressed *)
(* usable definition QuorumsAt suppressed *)
(* usable definition CanRollback suppressed *)
(* usable definition CanVoteForOplog suppressed *)
(* usable definition ImmediatelyCommitted suppressed *)
(* usable definition ClientRequest suppressed *)
(* usable definition GetEntries suppressed *)
(* usable definition RollbackEntries suppressed *)
(* usable definition BecomeLeader suppressed *)
(* usable definition CommitEntry suppressed *)
(* usable definition Init suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ElectionSafety suppressed *)
(* usable definition LeaderCompleteness suppressed *)
(* usable definition StateMachineSafety suppressed *)
(* usable definition EqualUpTo suppressed *)
(* usable definition LogMatching suppressed *)
(* usable definition Max suppressed *)
(* usable definition ExistsPrimary suppressed *)
(* usable definition AllConfigsAreServer suppressed *)
(* usable definition CurrentTermAtLeastAsLargeAsLogTermsForPrimary suppressed *)
(* usable definition TermsOfEntriesGrowMonotonically suppressed *)
(* usable definition OnePrimaryPerTerm suppressed *)
(* usable definition ExistsQuorumInLargestTerm suppressed *)
(* usable definition LogsMustBeSmallerThanOrEqualToLargestTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm suppressed *)
(* usable definition CommittedTermMatchesEntry suppressed *)
(* usable definition LogsLaterThanCommittedMustHaveCommitted suppressed *)
(* usable definition LogsEqualToCommittedMustHaveCommittedIfItFits suppressed *)
(* usable definition CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens suppressed *)
(* usable definition CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms suppressed *)
(* usable definition LeaderCompletenessGeneralized suppressed *)
(* usable definition CommittedEntriesMustHaveQuorums suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
fixes MaxLogLen
fixes MaxTerm
fixes NumRandSubsets
(* usable definition StateConstraint suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition LemmaBasic suppressed *)
assumes v'253: "(TypeOK)"
assumes v'254: "(Next)"
assumes v'255: "(TypeOK)"
assumes v'256: "(Next)"
assumes v'266: "(\<exists> s \<in> (Server) : (\<exists> t \<in> (Server) : ((((greater ((fapply ((currentTerm), (s))), (fapply ((currentTerm), (t)))))) & ((((a_currentTermhash_primea :: c)) = ([(currentTerm) EXCEPT ![(t)] = (fapply ((currentTerm), (s)))]))) & ((((a_statehash_primea :: c)) = ([(state) EXCEPT ![(t)] = (Secondary)])))) & (((((a_loghash_primea :: c)) = (log))) & ((((a_confighash_primea :: c)) = (config))) & ((((a_electionshash_primea :: c)) = (elections))) & ((((a_committedhash_primea :: c)) = (committed)))))))"
fixes s
assumes s_in : "(s \<in> (Server))"
fixes t
assumes t_in : "(t \<in> (Server))"
assumes v'272: "((greater ((fapply ((currentTerm), (s))), (fapply ((currentTerm), (t))))))"
assumes v'273: "((((a_currentTermhash_primea :: c)) = ([(currentTerm) EXCEPT ![(t)] = (fapply ((currentTerm), (s)))])))"
assumes v'274: "((((a_statehash_primea :: c)) = ([(state) EXCEPT ![(t)] = (Secondary)])))"
assumes v'275: "((((a_loghash_primea :: c)) = (log)))"
assumes v'276: "((((a_confighash_primea :: c)) = (config)))"
assumes v'277: "((((a_electionshash_primea :: c)) = (elections)))"
assumes v'278: "((((a_committedhash_primea :: c)) = (committed)))"
shows "((((a_currentTermhash_primea :: c)) = ([(currentTerm) EXCEPT ![(t)] = (fapply ((currentTerm), (s)))])))"(is "PROP ?ob'144")
proof -
ML_command {* writeln "*** TLAPS ENTER 144"; *}
show "PROP ?ob'144"

(* BEGIN ZENON INPUT
;; file=MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_ce6b4d.znn; winfile="`cygpath -a -w "MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_ce6b4d.znn"`"; PATH='/usr/bin:/cygdrive/c/Program Files (x86)/Common Files/Oracle/Java/javapath:/cygdrive/c/WINDOWS/system32:/cygdrive/c/WINDOWS:/cygdrive/c/WINDOWS/System32/Wbem:/cygdrive/c/WINDOWS/System32/WindowsPowerShell/v1.0:/cygdrive/c/WINDOWS/System32/OpenSSH:/cygdrive/c/Program Files/Git/cmd:/cygdrive/c/Program Files/PuTTY:/cygdrive/c/Program Files/CMake/bin:/cygdrive/c/Program Files/Java/jdk-14.0.2/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32/Scripts:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32:/cygdrive/c/Users/ianda/AppData/Local/Microsoft/WindowsApps:/cygdrive/c/Users/ianda/AppData/Local/Programs/MiKTeX 2.9/miktex/bin/x64:/cygdrive/c/Program Files (x86)/GnuWin32/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Microsoft VS Code/bin:/cygdrive/c/MinGW/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_ce6b4d.znn.out
;; obligation #144
$hyp "v'253" TypeOK
$hyp "v'254" Next
$hyp "v'255" TypeOK
$hyp "v'256" Next
$hyp "v'266" (TLA.bEx Server ((s) (TLA.bEx Server ((t) (/\ (/\ (arith.lt (TLA.fapply currentTerm t)
(TLA.fapply currentTerm s)) (= a_currentTermhash_primea
(TLA.except currentTerm t (TLA.fapply currentTerm s))) (= a_statehash_primea
(TLA.except state t Secondary))) (/\ (= a_loghash_primea log)
(= a_confighash_primea config) (= a_electionshash_primea elections)
(= a_committedhash_primea
committed)))))))
$hyp "s_in" (TLA.in s Server)
$hyp "t_in" (TLA.in t Server)
$hyp "v'272" (arith.lt (TLA.fapply currentTerm t)
(TLA.fapply currentTerm s))
$hyp "v'273" (= a_currentTermhash_primea
(TLA.except currentTerm t (TLA.fapply currentTerm s)))
$hyp "v'274" (= a_statehash_primea
(TLA.except state t Secondary))
$hyp "v'275" (= a_loghash_primea log)
$hyp "v'276" (= a_confighash_primea
config)
$hyp "v'277" (= a_electionshash_primea
elections)
$hyp "v'278" (= a_committedhash_primea
committed)
$goal (= a_currentTermhash_primea
(TLA.except currentTerm t (TLA.fapply currentTerm s)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hg:"(a_currentTermhash_primea=except(currentTerm, t, (currentTerm[s])))" (is "_=?z_ho")
 using v'273 by blast
 assume z_Hm:"(a_currentTermhash_primea~=?z_ho)"
 show FALSE
 by (rule notE [OF z_Hm z_Hg])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 144"; *} qed
lemma ob'141:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Server
fixes Secondary
fixes Primary
fixes Nil
fixes currentTerm currentTerm'
fixes state state'
fixes log log'
fixes config config'
fixes elections elections'
fixes committed committed'
(* usable definition vars suppressed *)
(* usable definition Empty suppressed *)
(* usable definition InLog suppressed *)
(* usable definition LastTerm suppressed *)
(* usable definition LastEntry suppressed *)
(* usable definition GetTerm suppressed *)
(* usable definition LogTerm suppressed *)
(* usable definition Quorums suppressed *)
(* usable definition QuorumsAt suppressed *)
(* usable definition CanRollback suppressed *)
(* usable definition CanVoteForOplog suppressed *)
(* usable definition ImmediatelyCommitted suppressed *)
(* usable definition UpdateTermsExpr suppressed *)
(* usable definition ClientRequest suppressed *)
(* usable definition GetEntries suppressed *)
(* usable definition RollbackEntries suppressed *)
(* usable definition BecomeLeader suppressed *)
(* usable definition CommitEntry suppressed *)
(* usable definition UpdateTerms suppressed *)
(* usable definition Init suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ElectionSafety suppressed *)
(* usable definition LeaderCompleteness suppressed *)
(* usable definition StateMachineSafety suppressed *)
(* usable definition EqualUpTo suppressed *)
(* usable definition LogMatching suppressed *)
(* usable definition Max suppressed *)
(* usable definition ExistsPrimary suppressed *)
(* usable definition AllConfigsAreServer suppressed *)
(* usable definition CurrentTermAtLeastAsLargeAsLogTermsForPrimary suppressed *)
(* usable definition TermsOfEntriesGrowMonotonically suppressed *)
(* usable definition OnePrimaryPerTerm suppressed *)
(* usable definition ExistsQuorumInLargestTerm suppressed *)
(* usable definition LogsMustBeSmallerThanOrEqualToLargestTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm suppressed *)
(* usable definition CommittedTermMatchesEntry suppressed *)
(* usable definition LogsLaterThanCommittedMustHaveCommitted suppressed *)
(* usable definition LogsEqualToCommittedMustHaveCommittedIfItFits suppressed *)
(* usable definition CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens suppressed *)
(* usable definition CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms suppressed *)
(* usable definition LeaderCompletenessGeneralized suppressed *)
(* usable definition CommittedEntriesMustHaveQuorums suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
fixes MaxLogLen
fixes MaxTerm
fixes NumRandSubsets
(* usable definition StateConstraint suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition LemmaBasic suppressed *)
assumes v'254: "(TypeOK)"
assumes v'255: "(Next)"
assumes v'256: "(TypeOK)"
assumes v'257: "(Next)"
assumes v'267: "(\<exists> s \<in> (Server) : (\<exists> t \<in> (Server) : ((UpdateTerms ((s), (t))))))"
fixes s
assumes s_in : "(s \<in> (Server))"
fixes t
assumes t_in : "(t \<in> (Server))"
assumes v'273: "((UpdateTerms ((s), (t))))"
assumes v'278: "((((a_currentTermhash_primea :: c)) = ([(currentTerm) EXCEPT ![(t)] = (fapply ((currentTerm), (s)))])))"
assumes v'281: "((((DOMAIN ((a_currentTermhash_primea :: c)))) = (Server)))"
assumes v'282: "(((setOfAll(((DOMAIN ((a_currentTermhash_primea :: c)))), %x. (fapply (((a_currentTermhash_primea :: c)), (x))))) \<in> ((SUBSET (Nat)))))"
shows "((((a_currentTermhash_primea :: c)) \<in> ([(Server) \<rightarrow> (Nat)])))"(is "PROP ?ob'141")
proof -
ML_command {* writeln "*** TLAPS ENTER 141"; *}
show "PROP ?ob'141"

(* BEGIN ZENON INPUT
;; file=MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_203af5.znn; winfile="`cygpath -a -w "MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_203af5.znn"`"; PATH='/usr/bin:/cygdrive/c/Program Files (x86)/Common Files/Oracle/Java/javapath:/cygdrive/c/WINDOWS/system32:/cygdrive/c/WINDOWS:/cygdrive/c/WINDOWS/System32/Wbem:/cygdrive/c/WINDOWS/System32/WindowsPowerShell/v1.0:/cygdrive/c/WINDOWS/System32/OpenSSH:/cygdrive/c/Program Files/Git/cmd:/cygdrive/c/Program Files/PuTTY:/cygdrive/c/Program Files/CMake/bin:/cygdrive/c/Program Files/Java/jdk-14.0.2/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32/Scripts:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32:/cygdrive/c/Users/ianda/AppData/Local/Microsoft/WindowsApps:/cygdrive/c/Users/ianda/AppData/Local/Programs/MiKTeX 2.9/miktex/bin/x64:/cygdrive/c/Program Files (x86)/GnuWin32/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Microsoft VS Code/bin:/cygdrive/c/MinGW/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_203af5.znn.out
;; obligation #141
$hyp "v'254" TypeOK
$hyp "v'255" Next
$hyp "v'256" TypeOK
$hyp "v'257" Next
$hyp "v'267" (TLA.bEx Server ((s) (TLA.bEx Server ((t) (UpdateTerms s
t)))))
$hyp "s_in" (TLA.in s Server)
$hyp "t_in" (TLA.in t Server)
$hyp "v'273" (UpdateTerms s t)
$hyp "v'278" (= a_currentTermhash_primea
(TLA.except currentTerm t (TLA.fapply currentTerm s)))
$hyp "v'281" (= (TLA.DOMAIN a_currentTermhash_primea)
Server)
$hyp "v'282" (TLA.in (TLA.setOfAll (TLA.DOMAIN a_currentTermhash_primea) ((x) (TLA.fapply a_currentTermhash_primea x)))
(TLA.SUBSET arith.N))
$goal (TLA.in a_currentTermhash_primea
(TLA.FuncSet Server arith.N))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"(DOMAIN(a_currentTermhash_primea)=Server)" (is "?z_hk=_")
 using v'281 by blast
 have z_Hg:"(a_currentTermhash_primea=except(currentTerm, t, (currentTerm[s])))" (is "_=?z_hn")
 using v'278 by blast
 have z_Hi:"(setOfAll(?z_hk, (\<lambda>x. (a_currentTermhash_primea[x]))) \\in SUBSET(Nat))" (is "?z_hi")
 using v'282 by blast
 have z_Hd:"(s \\in Server)" (is "?z_hd")
 using s_in by blast
 have zenon_L1_: "(~isAFcn(?z_hn)) ==> FALSE" (is "?z_hy ==> FALSE")
 proof -
  assume z_Hy:"?z_hy" (is "~?z_hz")
  show FALSE
  by (rule zenon_notisafcn_except [of "currentTerm" "t" "(currentTerm[s])", OF z_Hy])
 qed
 have zenon_L2_: "(DOMAIN(?z_hn)~=DOMAIN(currentTerm)) ==> FALSE" (is "?z_hba ==> FALSE")
 proof -
  assume z_Hba:"?z_hba" (is "?z_hbb~=?z_hbc")
  have z_Hbd: "(?z_hbc~=?z_hbc)"
  by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vqx. (zenon_Vqx~=?z_hbc))" "currentTerm" "t" "(currentTerm[s])", OF z_Hba])
  show FALSE
  by (rule zenon_noteq [OF z_Hbd])
 qed
 have zenon_L3_: "(a_currentTermhash_primea=?z_hn) ==> (\\A x:((x \\in setOfAll(?z_hk, (\<lambda>x. (a_currentTermhash_primea[x]))))=>(x \\in Nat))) ==> (s \\in DOMAIN(currentTerm)) ==> (s \\in ?z_hk) ==> (~((currentTerm[s]) \\in Nat)) ==> FALSE" (is "?z_hg ==> ?z_hbh ==> ?z_hbl ==> ?z_hbm ==> ?z_hbn ==> FALSE")
 proof -
  assume z_Hg:"?z_hg"
  assume z_Hbh:"?z_hbh" (is "\\A x : ?z_hbp(x)")
  assume z_Hbl:"?z_hbl"
  assume z_Hbm:"?z_hbm"
  assume z_Hbn:"?z_hbn" (is "~?z_hbo")
  have z_Hbq: "?z_hbp((currentTerm[s]))" (is "?z_hbr=>_")
  by (rule zenon_all_0 [of "?z_hbp" "(currentTerm[s])", OF z_Hbh])
  show FALSE
  proof (rule zenon_imply [OF z_Hbq])
   assume z_Hbs:"(~?z_hbr)"
   have z_Hbt: "(~(\\E zenon_Vwn:((zenon_Vwn \\in ?z_hk)&((currentTerm[s])=(a_currentTermhash_primea[zenon_Vwn])))))" (is "~(\\E x : ?z_hca(x))")
   by (rule zenon_notin_setofall_0 [of "(currentTerm[s])" "?z_hk" "(\<lambda>x. (a_currentTermhash_primea[x]))", OF z_Hbs])
   have z_Hcb: "~?z_hca(s)" (is "~(_&?z_hcc)")
   by (rule zenon_notex_0 [of "?z_hca" "s", OF z_Hbt])
   show FALSE
   proof (rule zenon_notand [OF z_Hcb])
    assume z_Hcd:"(~?z_hbm)"
    show FALSE
    by (rule notE [OF z_Hcd z_Hbm])
   next
    assume z_Hce:"((currentTerm[s])~=(a_currentTermhash_primea[s]))" (is "?z_hq~=?z_hcf")
    have z_Hcg: "(?z_hq~=(?z_hn[s]))" (is "_~=?z_hch")
    by (rule subst [where P="(\<lambda>zenon_Vuic. (?z_hq~=(zenon_Vuic[s])))", OF z_Hg z_Hce])
    show FALSE
    proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vjx. (?z_hq~=zenon_Vjx))" "currentTerm" "t" "?z_hq" "s", OF z_Hcg])
     assume z_Hbl:"?z_hbl"
     assume z_Hcp:"(t=s)"
     assume z_Hcq:"(?z_hq~=?z_hq)"
     show FALSE
     by (rule zenon_noteq [OF z_Hcq])
    next
     assume z_Hbl:"?z_hbl"
     assume z_Hcr:"(t~=s)"
     assume z_Hcq:"(?z_hq~=?z_hq)"
     show FALSE
     by (rule zenon_noteq [OF z_Hcq])
    next
     assume z_Hcs:"(~?z_hbl)"
     show FALSE
     by (rule notE [OF z_Hcs z_Hbl])
    qed
   qed
  next
   assume z_Hbo:"?z_hbo"
   show FALSE
   by (rule notE [OF z_Hbn z_Hbo])
  qed
 qed
 have zenon_L4_: "(a_currentTermhash_primea=?z_hn) ==> (\\A x:((x \\in setOfAll(DOMAIN(currentTerm), (\<lambda>x. (a_currentTermhash_primea[x]))))=>(x \\in Nat))) ==> (t~=(CHOOSE zenon_Vik:(~((zenon_Vik \\in DOMAIN(currentTerm))=>((?z_hn[zenon_Vik]) \\in Nat))))) ==> ((CHOOSE zenon_Vik:(~((zenon_Vik \\in DOMAIN(currentTerm))=>((?z_hn[zenon_Vik]) \\in Nat)))) \\in DOMAIN(currentTerm)) ==> (~((currentTerm[(CHOOSE zenon_Vik:(~((zenon_Vik \\in DOMAIN(currentTerm))=>((?z_hn[zenon_Vik]) \\in Nat))))]) \\in Nat)) ==> FALSE" (is "?z_hg ==> ?z_hct ==> ?z_hcx ==> ?z_hdf ==> ?z_hdg ==> FALSE")
 proof -
  assume z_Hg:"?z_hg"
  assume z_Hct:"?z_hct" (is "\\A x : ?z_hdj(x)")
  assume z_Hcx:"?z_hcx" (is "_~=?z_hcy")
  assume z_Hdf:"?z_hdf"
  assume z_Hdg:"?z_hdg" (is "~?z_hdh")
  have z_Hdk: "?z_hdj((currentTerm[?z_hcy]))" (is "?z_hdl=>_")
  by (rule zenon_all_0 [of "?z_hdj" "(currentTerm[?z_hcy])", OF z_Hct])
  show FALSE
  proof (rule zenon_imply [OF z_Hdk])
   assume z_Hdm:"(~?z_hdl)"
   have z_Hdn: "(~(\\E zenon_Vno:((zenon_Vno \\in DOMAIN(currentTerm))&((currentTerm[?z_hcy])=(a_currentTermhash_primea[zenon_Vno])))))" (is "~(\\E x : ?z_hdu(x))")
   by (rule zenon_notin_setofall_0 [of "(currentTerm[?z_hcy])" "DOMAIN(currentTerm)" "(\<lambda>x. (a_currentTermhash_primea[x]))", OF z_Hdm])
   have z_Hdv: "~?z_hdu(?z_hcy)" (is "~(_&?z_hdw)")
   by (rule zenon_notex_0 [of "?z_hdu" "?z_hcy", OF z_Hdn])
   show FALSE
   proof (rule zenon_notand [OF z_Hdv])
    assume z_Hdx:"(~?z_hdf)"
    show FALSE
    by (rule notE [OF z_Hdx z_Hdf])
   next
    assume z_Hdy:"((currentTerm[?z_hcy])~=(a_currentTermhash_primea[?z_hcy]))" (is "?z_hdi~=?z_hdz")
    have z_Hea: "(?z_hdi~=(?z_hn[?z_hcy]))" (is "_~=?z_heb")
    by (rule subst [where P="(\<lambda>zenon_Vwic. (?z_hdi~=(zenon_Vwic[?z_hcy])))", OF z_Hg z_Hdy])
    show FALSE
    proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vyua. (?z_hdi~=zenon_Vyua))" "currentTerm" "t" "(currentTerm[s])" "?z_hcy", OF z_Hea])
     assume z_Hdf:"?z_hdf"
     assume z_Hej:"(t=?z_hcy)"
     assume z_Hek:"(?z_hdi~=(currentTerm[s]))" (is "_~=?z_hq")
     show FALSE
     by (rule notE [OF z_Hcx z_Hej])
    next
     assume z_Hdf:"?z_hdf"
     assume z_Hcx:"?z_hcx"
     assume z_Hel:"(?z_hdi~=?z_hdi)"
     show FALSE
     by (rule zenon_noteq [OF z_Hel])
    next
     assume z_Hdx:"(~?z_hdf)"
     show FALSE
     by (rule notE [OF z_Hdx z_Hdf])
    qed
   qed
  next
   assume z_Hdh:"?z_hdh"
   show FALSE
   by (rule notE [OF z_Hdg z_Hdh])
  qed
 qed
 assume z_Hj:"(~(a_currentTermhash_primea \\in FuncSet(Server, Nat)))" (is "~?z_hem")
 have z_Heo: "(setOfAll(?z_hk, (\<lambda>x. (a_currentTermhash_primea[x]))) \\subseteq Nat)" (is "?z_heo")
 by (rule zenon_in_SUBSET_0 [of "setOfAll(?z_hk, (\<lambda>x. (a_currentTermhash_primea[x])))" "Nat", OF z_Hi])
 have z_Hep_z_Heo: "bAll(setOfAll(?z_hk, (\<lambda>x. (a_currentTermhash_primea[x]))), (\<lambda>x. (x \\in Nat))) == ?z_heo" (is "?z_hep == _")
 by (unfold subset_def)
 have z_Hep: "?z_hep"
 by (unfold z_Hep_z_Heo, fact z_Heo)
 have z_Hbh_z_Hep: "(\\A x:((x \\in setOfAll(?z_hk, (\<lambda>x. (a_currentTermhash_primea[x]))))=>(x \\in Nat))) == ?z_hep" (is "?z_hbh == _")
 by (unfold bAll_def)
 have z_Hbh: "?z_hbh" (is "\\A x : ?z_hbp(x)")
 by (unfold z_Hbh_z_Hep, fact z_Hep)
 have z_Her: "bAll(setOfAll(DOMAIN(?z_hn), (\<lambda>x. (a_currentTermhash_primea[x]))), (\<lambda>x. (x \\in Nat)))" (is "?z_her")
 by (rule subst [where P="(\<lambda>zenon_Viic. bAll(setOfAll(DOMAIN(zenon_Viic), (\<lambda>x. (a_currentTermhash_primea[x]))), (\<lambda>x. (x \\in Nat))))", OF z_Hg z_Hep])
 have z_Hey: "bAll(setOfAll(DOMAIN(currentTerm), (\<lambda>x. (a_currentTermhash_primea[x]))), (\<lambda>x. (x \\in Nat)))" (is "?z_hey")
 by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vfa. bAll(setOfAll(zenon_Vfa, (\<lambda>x. (a_currentTermhash_primea[x]))), (\<lambda>x. (x \\in Nat))))" "currentTerm" "t" "(currentTerm[s])", OF z_Her])
 have z_Hct_z_Hey: "(\\A x:((x \\in setOfAll(DOMAIN(currentTerm), (\<lambda>x. (a_currentTermhash_primea[x]))))=>(x \\in Nat))) == ?z_hey" (is "?z_hct == _")
 by (unfold bAll_def)
 have z_Hct: "?z_hct" (is "\\A x : ?z_hdj(x)")
 by (unfold z_Hct_z_Hey, fact z_Hey)
 have z_Hbm: "(s \\in ?z_hk)" (is "?z_hbm")
 by (rule ssubst [where P="(\<lambda>zenon_Vp. (s \\in zenon_Vp))", OF z_Hh z_Hd])
 have z_Hfg: "(s \\in DOMAIN(?z_hn))" (is "?z_hfg")
 by (rule subst [where P="(\<lambda>zenon_Vmfc. (s \\in DOMAIN(zenon_Vmfc)))", OF z_Hg z_Hbm])
 have z_Hbl: "(s \\in DOMAIN(currentTerm))" (is "?z_hbl")
 by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vp. (s \\in zenon_Vp))" "currentTerm" "t" "(currentTerm[s])", OF z_Hfg])
 have z_Hfl: "(~(?z_hn \\in FuncSet(Server, Nat)))" (is "~?z_hfm")
 by (rule subst [where P="(\<lambda>zenon_Vfgc. (~(zenon_Vfgc \\in FuncSet(Server, Nat))))", OF z_Hg z_Hj])
 have z_Hfr: "(~(?z_hn \\in FuncSet(?z_hk, Nat)))" (is "~?z_hfs")
 by (rule ssubst [where P="(\<lambda>zenon_Vvj. (~(?z_hn \\in FuncSet(zenon_Vvj, Nat))))", OF z_Hh z_Hfl])
 have z_Hfz: "(~(?z_hn \\in FuncSet(DOMAIN(?z_hn), Nat)))" (is "~?z_hga")
 by (rule subst [where P="(\<lambda>zenon_Vkgc. (~(?z_hn \\in FuncSet(DOMAIN(zenon_Vkgc), Nat))))", OF z_Hg z_Hfr])
 have z_Hgi: "(~(?z_hn \\in FuncSet(DOMAIN(currentTerm), Nat)))" (is "~?z_hgj")
 by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vvj. (~(?z_hn \\in FuncSet(zenon_Vvj, Nat))))" "currentTerm" "t" "(currentTerm[s])", OF z_Hfz])
 show FALSE
 proof (rule zenon_notin_funcset [of "?z_hn" "DOMAIN(currentTerm)" "Nat", OF z_Hgi])
  assume z_Hy:"(~isAFcn(?z_hn))" (is "~?z_hz")
  show FALSE
  by (rule zenon_L1_ [OF z_Hy])
 next
  assume z_Hba:"(DOMAIN(?z_hn)~=DOMAIN(currentTerm))" (is "?z_hbb~=?z_hbc")
  show FALSE
  by (rule zenon_L2_ [OF z_Hba])
 next
  assume z_Hgl:"(~(\\A zenon_Vik:((zenon_Vik \\in DOMAIN(currentTerm))=>((?z_hn[zenon_Vik]) \\in Nat))))" (is "~(\\A x : ?z_hgn(x))")
  have z_Hgo: "(\\E zenon_Vik:(~((zenon_Vik \\in DOMAIN(currentTerm))=>((?z_hn[zenon_Vik]) \\in Nat))))" (is "\\E x : ?z_hgp(x)")
  by (rule zenon_notallex_0 [of "?z_hgn", OF z_Hgl])
  have z_Hgq: "?z_hgp((CHOOSE zenon_Vik:(~((zenon_Vik \\in DOMAIN(currentTerm))=>((?z_hn[zenon_Vik]) \\in Nat)))))" (is "~(?z_hdf=>?z_hgr)")
  by (rule zenon_ex_choose_0 [of "?z_hgp", OF z_Hgo])
  have z_Hdf: "?z_hdf"
  by (rule zenon_notimply_0 [OF z_Hgq])
  have z_Hgs: "(~?z_hgr)"
  by (rule zenon_notimply_1 [OF z_Hgq])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vjk. (~(zenon_Vjk \\in Nat)))" "currentTerm" "t" "(currentTerm[s])" "(CHOOSE zenon_Vik:(~((zenon_Vik \\in DOMAIN(currentTerm))=>((?z_hn[zenon_Vik]) \\in Nat))))", OF z_Hgs])
   assume z_Hdf:"?z_hdf"
   assume z_Hej:"(t=(CHOOSE zenon_Vik:(~((zenon_Vik \\in DOMAIN(currentTerm))=>((?z_hn[zenon_Vik]) \\in Nat)))))" (is "_=?z_hcy")
   assume z_Hbn:"(~((currentTerm[s]) \\in Nat))" (is "~?z_hbo")
   show FALSE
   by (rule zenon_L3_ [OF z_Hg z_Hbh z_Hbl z_Hbm z_Hbn])
  next
   assume z_Hdf:"?z_hdf"
   assume z_Hcx:"(t~=(CHOOSE zenon_Vik:(~((zenon_Vik \\in DOMAIN(currentTerm))=>((?z_hn[zenon_Vik]) \\in Nat)))))" (is "_~=?z_hcy")
   assume z_Hdg:"(~((currentTerm[?z_hcy]) \\in Nat))" (is "~?z_hdh")
   show FALSE
   by (rule zenon_L4_ [OF z_Hg z_Hct z_Hcx z_Hdf z_Hdg])
  next
   assume z_Hdx:"(~?z_hdf)"
   show FALSE
   by (rule notE [OF z_Hdx z_Hdf])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 141"; *} qed
lemma ob'148:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Server
fixes Secondary
fixes Primary
fixes Nil
fixes currentTerm currentTerm'
fixes state state'
fixes log log'
fixes config config'
fixes elections elections'
fixes committed committed'
(* usable definition vars suppressed *)
(* usable definition Empty suppressed *)
(* usable definition InLog suppressed *)
(* usable definition LastTerm suppressed *)
(* usable definition LastEntry suppressed *)
(* usable definition GetTerm suppressed *)
(* usable definition LogTerm suppressed *)
(* usable definition Quorums suppressed *)
(* usable definition QuorumsAt suppressed *)
(* usable definition CanRollback suppressed *)
(* usable definition CanVoteForOplog suppressed *)
(* usable definition ImmediatelyCommitted suppressed *)
(* usable definition UpdateTermsExpr suppressed *)
(* usable definition ClientRequest suppressed *)
(* usable definition GetEntries suppressed *)
(* usable definition RollbackEntries suppressed *)
(* usable definition BecomeLeader suppressed *)
(* usable definition CommitEntry suppressed *)
(* usable definition UpdateTerms suppressed *)
(* usable definition Init suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ElectionSafety suppressed *)
(* usable definition LeaderCompleteness suppressed *)
(* usable definition StateMachineSafety suppressed *)
(* usable definition EqualUpTo suppressed *)
(* usable definition LogMatching suppressed *)
(* usable definition Max suppressed *)
(* usable definition ExistsPrimary suppressed *)
(* usable definition AllConfigsAreServer suppressed *)
(* usable definition CurrentTermAtLeastAsLargeAsLogTermsForPrimary suppressed *)
(* usable definition TermsOfEntriesGrowMonotonically suppressed *)
(* usable definition OnePrimaryPerTerm suppressed *)
(* usable definition ExistsQuorumInLargestTerm suppressed *)
(* usable definition LogsMustBeSmallerThanOrEqualToLargestTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm suppressed *)
(* usable definition CommittedTermMatchesEntry suppressed *)
(* usable definition LogsLaterThanCommittedMustHaveCommitted suppressed *)
(* usable definition LogsEqualToCommittedMustHaveCommittedIfItFits suppressed *)
(* usable definition CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens suppressed *)
(* usable definition CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms suppressed *)
(* usable definition LeaderCompletenessGeneralized suppressed *)
(* usable definition CommittedEntriesMustHaveQuorums suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
fixes MaxLogLen
fixes MaxTerm
fixes NumRandSubsets
(* usable definition StateConstraint suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition LemmaBasic suppressed *)
assumes v'254: "(TypeOK)"
assumes v'255: "(Next)"
assumes v'256: "(TypeOK)"
assumes v'257: "(Next)"
assumes v'267: "(\<exists> s \<in> (Server) : (\<exists> t \<in> (Server) : ((UpdateTerms ((s), (t))))))"
fixes s
assumes s_in : "(s \<in> (Server))"
fixes t
assumes t_in : "(t \<in> (Server))"
assumes v'273: "((UpdateTerms ((s), (t))))"
assumes v'279: "((((a_statehash_primea :: c)) = ([(state) EXCEPT ![(t)] = (Secondary)])))"
assumes v'282: "((((DOMAIN ((a_statehash_primea :: c)))) = (Server)))"
assumes v'283: "(((setOfAll(((DOMAIN ((a_statehash_primea :: c)))), %x. (fapply (((a_statehash_primea :: c)), (x))))) \<in> ((SUBSET ({(Secondary), (Primary)})))))"
shows "((((a_statehash_primea :: c)) \<in> ([(Server) \<rightarrow> ({(Secondary), (Primary)})])))"(is "PROP ?ob'148")
proof -
ML_command {* writeln "*** TLAPS ENTER 148"; *}
show "PROP ?ob'148"

(* BEGIN ZENON INPUT
;; file=MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_7541da.znn; winfile="`cygpath -a -w "MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_7541da.znn"`"; PATH='/usr/bin:/cygdrive/c/Program Files (x86)/Common Files/Oracle/Java/javapath:/cygdrive/c/WINDOWS/system32:/cygdrive/c/WINDOWS:/cygdrive/c/WINDOWS/System32/Wbem:/cygdrive/c/WINDOWS/System32/WindowsPowerShell/v1.0:/cygdrive/c/WINDOWS/System32/OpenSSH:/cygdrive/c/Program Files/Git/cmd:/cygdrive/c/Program Files/PuTTY:/cygdrive/c/Program Files/CMake/bin:/cygdrive/c/Program Files/Java/jdk-14.0.2/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32/Scripts:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32:/cygdrive/c/Users/ianda/AppData/Local/Microsoft/WindowsApps:/cygdrive/c/Users/ianda/AppData/Local/Programs/MiKTeX 2.9/miktex/bin/x64:/cygdrive/c/Program Files (x86)/GnuWin32/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Microsoft VS Code/bin:/cygdrive/c/MinGW/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_7541da.znn.out
;; obligation #148
$hyp "v'254" TypeOK
$hyp "v'255" Next
$hyp "v'256" TypeOK
$hyp "v'257" Next
$hyp "v'267" (TLA.bEx Server ((s) (TLA.bEx Server ((t) (UpdateTerms s
t)))))
$hyp "s_in" (TLA.in s Server)
$hyp "t_in" (TLA.in t Server)
$hyp "v'273" (UpdateTerms s t)
$hyp "v'279" (= a_statehash_primea
(TLA.except state t Secondary))
$hyp "v'282" (= (TLA.DOMAIN a_statehash_primea)
Server)
$hyp "v'283" (TLA.in (TLA.setOfAll (TLA.DOMAIN a_statehash_primea) ((x) (TLA.fapply a_statehash_primea x)))
(TLA.SUBSET (TLA.set Secondary Primary)))
$goal (TLA.in a_statehash_primea
(TLA.FuncSet Server (TLA.set Secondary Primary)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hg:"(a_statehash_primea=except(state, t, Secondary))" (is "_=?z_hl")
 using v'279 by blast
 have z_Hh:"(DOMAIN(a_statehash_primea)=Server)" (is "?z_hp=_")
 using v'282 by blast
 have z_Hi:"(setOfAll(?z_hp, (\<lambda>x. (a_statehash_primea[x]))) \\in SUBSET({Secondary, Primary}))" (is "?z_hi")
 using v'283 by blast
 have zenon_L1_: "(~isAFcn(?z_hl)) ==> FALSE" (is "?z_hy ==> FALSE")
 proof -
  assume z_Hy:"?z_hy" (is "~?z_hz")
  show FALSE
  by (rule zenon_notisafcn_except [of "state" "t" "Secondary", OF z_Hy])
 qed
 have zenon_L2_: "(DOMAIN(?z_hl)~=DOMAIN(state)) ==> FALSE" (is "?z_hba ==> FALSE")
 proof -
  assume z_Hba:"?z_hba" (is "?z_hbb~=?z_hbc")
  have z_Hbd: "(?z_hbc~=?z_hbc)"
  by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vkfa. (zenon_Vkfa~=?z_hbc))" "state" "t" "Secondary", OF z_Hba])
  show FALSE
  by (rule zenon_noteq [OF z_Hbd])
 qed
 have zenon_L3_: "(a_statehash_primea=?z_hl) ==> (~((?z_hl[(CHOOSE zenon_Vik:(~((zenon_Vik \\in DOMAIN(state))=>((?z_hl[zenon_Vik]) \\in {Secondary, Primary}))))]) \\in {Secondary, Primary})) ==> ((CHOOSE zenon_Vik:(~((zenon_Vik \\in DOMAIN(state))=>((?z_hl[zenon_Vik]) \\in {Secondary, Primary})))) \\in DOMAIN(state)) ==> (\\A x:((x \\in setOfAll(DOMAIN(state), (\<lambda>x. (a_statehash_primea[x]))))=>(x \\in {Secondary, Primary}))) ==> (t~=(CHOOSE zenon_Vik:(~((zenon_Vik \\in DOMAIN(state))=>((?z_hl[zenon_Vik]) \\in {Secondary, Primary}))))) ==> FALSE" (is "?z_hg ==> ?z_hbh ==> ?z_hbr ==> ?z_hbs ==> ?z_hbx ==> FALSE")
 proof -
  assume z_Hg:"?z_hg"
  assume z_Hbh:"?z_hbh" (is "~?z_hbi")
  assume z_Hbr:"?z_hbr"
  assume z_Hbs:"?z_hbs" (is "\\A x : ?z_hby(x)")
  assume z_Hbx:"?z_hbx" (is "_~=?z_hbk")
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vjk. (~(zenon_Vjk \\in {Secondary, Primary})))" "state" "t" "Secondary" "?z_hbk", OF z_Hbh])
   assume z_Hbr:"?z_hbr"
   assume z_Hcd:"(t=?z_hbk)"
   assume z_Hce:"(~(Secondary \\in {Secondary, Primary}))" (is "~?z_hcf")
   show FALSE
   by (rule notE [OF z_Hbx z_Hcd])
  next
   assume z_Hbr:"?z_hbr"
   assume z_Hbx:"?z_hbx"
   assume z_Hcg:"(~((state[?z_hbk]) \\in {Secondary, Primary}))" (is "~?z_hch")
   have z_Hcj: "?z_hby((state[?z_hbk]))" (is "?z_hck=>_")
   by (rule zenon_all_0 [of "?z_hby" "(state[?z_hbk])", OF z_Hbs])
   show FALSE
   proof (rule zenon_imply [OF z_Hcj])
    assume z_Hcl:"(~?z_hck)"
    have z_Hcm: "(~(\\E zenon_Voq:((zenon_Voq \\in DOMAIN(state))&((state[?z_hbk])=(a_statehash_primea[zenon_Voq])))))" (is "~(\\E x : ?z_hct(x))")
    by (rule zenon_notin_setofall_0 [of "(state[?z_hbk])" "DOMAIN(state)" "(\<lambda>x. (a_statehash_primea[x]))", OF z_Hcl])
    have z_Hcu: "~?z_hct(?z_hbk)" (is "~(_&?z_hcv)")
    by (rule zenon_notex_0 [of "?z_hct" "?z_hbk", OF z_Hcm])
    show FALSE
    proof (rule zenon_notand [OF z_Hcu])
     assume z_Hcw:"(~?z_hbr)"
     show FALSE
     by (rule notE [OF z_Hcw z_Hbr])
    next
     assume z_Hcx:"((state[?z_hbk])~=(a_statehash_primea[?z_hbk]))" (is "?z_hci~=?z_hcy")
     have z_Hcz: "(?z_hci~=(?z_hl[?z_hbk]))" (is "_~=?z_hbj")
     by (rule subst [where P="(\<lambda>zenon_Vtsb. (?z_hci~=(zenon_Vtsb[?z_hbk])))", OF z_Hg z_Hcx])
     show FALSE
     proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vxea. (?z_hci~=zenon_Vxea))" "state" "t" "Secondary" "?z_hbk", OF z_Hcz])
      assume z_Hbr:"?z_hbr"
      assume z_Hcd:"(t=?z_hbk)"
      assume z_Hdh:"(?z_hci~=Secondary)"
      show FALSE
      by (rule notE [OF z_Hbx z_Hcd])
     next
      assume z_Hbr:"?z_hbr"
      assume z_Hbx:"?z_hbx"
      assume z_Hdi:"(?z_hci~=?z_hci)"
      show FALSE
      by (rule zenon_noteq [OF z_Hdi])
     next
      assume z_Hcw:"(~?z_hbr)"
      show FALSE
      by (rule notE [OF z_Hcw z_Hbr])
     qed
    qed
   next
    assume z_Hch:"?z_hch"
    show FALSE
    by (rule notE [OF z_Hcg z_Hch])
   qed
  next
   assume z_Hcw:"(~?z_hbr)"
   show FALSE
   by (rule notE [OF z_Hcw z_Hbr])
  qed
 qed
 assume z_Hj:"(~(a_statehash_primea \\in FuncSet(Server, {Secondary, Primary})))" (is "~?z_hdj")
 have z_Hdl: "(setOfAll(?z_hp, (\<lambda>x. (a_statehash_primea[x]))) \\subseteq {Secondary, Primary})" (is "?z_hdl")
 by (rule zenon_in_SUBSET_0 [of "setOfAll(?z_hp, (\<lambda>x. (a_statehash_primea[x])))" "{Secondary, Primary}", OF z_Hi])
 have z_Hdm_z_Hdl: "bAll(setOfAll(?z_hp, (\<lambda>x. (a_statehash_primea[x]))), (\<lambda>x. (x \\in {Secondary, Primary}))) == ?z_hdl" (is "?z_hdm == _")
 by (unfold subset_def)
 have z_Hdm: "?z_hdm"
 by (unfold z_Hdm_z_Hdl, fact z_Hdl)
 have z_Hdo: "bAll(setOfAll(DOMAIN(?z_hl), (\<lambda>x. (a_statehash_primea[x]))), (\<lambda>x. (x \\in {Secondary, Primary})))" (is "?z_hdo")
 by (rule subst [where P="(\<lambda>zenon_Vehb. bAll(setOfAll(DOMAIN(zenon_Vehb), (\<lambda>x. (a_statehash_primea[x]))), (\<lambda>x. (x \\in {Secondary, Primary}))))", OF z_Hg z_Hdm])
 have z_Hdv: "bAll(setOfAll(DOMAIN(state), (\<lambda>x. (a_statehash_primea[x]))), (\<lambda>x. (x \\in {Secondary, Primary})))" (is "?z_hdv")
 by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vfa. bAll(setOfAll(zenon_Vfa, (\<lambda>x. (a_statehash_primea[x]))), (\<lambda>x. (x \\in {Secondary, Primary}))))" "state" "t" "Secondary", OF z_Hdo])
 have z_Hbs_z_Hdv: "(\\A x:((x \\in setOfAll(DOMAIN(state), (\<lambda>x. (a_statehash_primea[x]))))=>(x \\in {Secondary, Primary}))) == ?z_hdv" (is "?z_hbs == _")
 by (unfold bAll_def)
 have z_Hbs: "?z_hbs" (is "\\A x : ?z_hby(x)")
 by (unfold z_Hbs_z_Hdv, fact z_Hdv)
 have z_Hea: "(~(?z_hl \\in FuncSet(Server, {Secondary, Primary})))" (is "~?z_heb")
 by (rule subst [where P="(\<lambda>zenon_Vkfb. (~(zenon_Vkfb \\in FuncSet(Server, {Secondary, Primary}))))", OF z_Hg z_Hj])
 have z_Heg: "(~(?z_hl \\in FuncSet(?z_hp, {Secondary, Primary})))" (is "~?z_heh")
 by (rule ssubst [where P="(\<lambda>zenon_Vvj. (~(?z_hl \\in FuncSet(zenon_Vvj, {Secondary, Primary}))))", OF z_Hh z_Hea])
 have z_Heo: "(~(?z_hl \\in FuncSet(DOMAIN(?z_hl), {Secondary, Primary})))" (is "~?z_hep")
 by (rule subst [where P="(\<lambda>zenon_Vieb. (~(?z_hl \\in FuncSet(DOMAIN(zenon_Vieb), {Secondary, Primary}))))", OF z_Hg z_Heg])
 have z_Hex: "(~(?z_hl \\in FuncSet(DOMAIN(state), {Secondary, Primary})))" (is "~?z_hey")
 by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vvj. (~(?z_hl \\in FuncSet(zenon_Vvj, {Secondary, Primary}))))" "state" "t" "Secondary", OF z_Heo])
 show FALSE
 proof (rule zenon_notin_funcset [of "?z_hl" "DOMAIN(state)" "{Secondary, Primary}", OF z_Hex])
  assume z_Hy:"(~isAFcn(?z_hl))" (is "~?z_hz")
  show FALSE
  by (rule zenon_L1_ [OF z_Hy])
 next
  assume z_Hba:"(DOMAIN(?z_hl)~=DOMAIN(state))" (is "?z_hbb~=?z_hbc")
  show FALSE
  by (rule zenon_L2_ [OF z_Hba])
 next
  assume z_Hfa:"(~(\\A zenon_Vik:((zenon_Vik \\in DOMAIN(state))=>((?z_hl[zenon_Vik]) \\in {Secondary, Primary}))))" (is "~(\\A x : ?z_hfc(x))")
  have z_Hfd: "(\\E zenon_Vik:(~((zenon_Vik \\in DOMAIN(state))=>((?z_hl[zenon_Vik]) \\in {Secondary, Primary}))))" (is "\\E x : ?z_hfe(x)")
  by (rule zenon_notallex_0 [of "?z_hfc", OF z_Hfa])
  have z_Hff: "?z_hfe((CHOOSE zenon_Vik:(~((zenon_Vik \\in DOMAIN(state))=>((?z_hl[zenon_Vik]) \\in {Secondary, Primary})))))" (is "~(?z_hbr=>?z_hbi)")
  by (rule zenon_ex_choose_0 [of "?z_hfe", OF z_Hfd])
  have z_Hbr: "?z_hbr"
  by (rule zenon_notimply_0 [OF z_Hff])
  have z_Hbh: "(~?z_hbi)"
  by (rule zenon_notimply_1 [OF z_Hff])
  have z_Hfg: "((?z_hl[(CHOOSE zenon_Vik:(~((zenon_Vik \\in DOMAIN(state))=>((?z_hl[zenon_Vik]) \\in {Secondary, Primary}))))])~=Secondary)" (is "?z_hbj~=_")
  by (rule zenon_notin_addElt_0 [of "?z_hbj" "Secondary" "{Primary}", OF z_Hbh])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vpl. (zenon_Vpl~=Secondary))" "state" "t" "Secondary" "(CHOOSE zenon_Vik:(~((zenon_Vik \\in DOMAIN(state))=>((?z_hl[zenon_Vik]) \\in {Secondary, Primary}))))", OF z_Hfg])
   assume z_Hbr:"?z_hbr"
   assume z_Hcd:"(t=(CHOOSE zenon_Vik:(~((zenon_Vik \\in DOMAIN(state))=>((?z_hl[zenon_Vik]) \\in {Secondary, Primary})))))" (is "_=?z_hbk")
   assume z_Hfl:"(Secondary~=Secondary)"
   show FALSE
   by (rule zenon_noteq [OF z_Hfl])
  next
   assume z_Hbr:"?z_hbr"
   assume z_Hbx:"(t~=(CHOOSE zenon_Vik:(~((zenon_Vik \\in DOMAIN(state))=>((?z_hl[zenon_Vik]) \\in {Secondary, Primary})))))" (is "_~=?z_hbk")
   assume z_Hdh:"((state[?z_hbk])~=Secondary)" (is "?z_hci~=_")
   show FALSE
   by (rule zenon_L3_ [OF z_Hg z_Hbh z_Hbr z_Hbs z_Hbx])
  next
   assume z_Hcw:"(~?z_hbr)"
   show FALSE
   by (rule notE [OF z_Hcw z_Hbr])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 148"; *} qed
lemma ob'151:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Server
fixes Secondary
fixes Primary
fixes Nil
fixes currentTerm currentTerm'
fixes state state'
fixes log log'
fixes config config'
fixes elections elections'
fixes committed committed'
(* usable definition vars suppressed *)
(* usable definition Empty suppressed *)
(* usable definition InLog suppressed *)
(* usable definition LastTerm suppressed *)
(* usable definition LastEntry suppressed *)
(* usable definition GetTerm suppressed *)
(* usable definition LogTerm suppressed *)
(* usable definition Quorums suppressed *)
(* usable definition QuorumsAt suppressed *)
(* usable definition CanRollback suppressed *)
(* usable definition CanVoteForOplog suppressed *)
(* usable definition ImmediatelyCommitted suppressed *)
(* usable definition ClientRequest suppressed *)
(* usable definition GetEntries suppressed *)
(* usable definition RollbackEntries suppressed *)
(* usable definition BecomeLeader suppressed *)
(* usable definition CommitEntry suppressed *)
(* usable definition Init suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ElectionSafety suppressed *)
(* usable definition LeaderCompleteness suppressed *)
(* usable definition StateMachineSafety suppressed *)
(* usable definition EqualUpTo suppressed *)
(* usable definition LogMatching suppressed *)
(* usable definition Max suppressed *)
(* usable definition ExistsPrimary suppressed *)
(* usable definition AllConfigsAreServer suppressed *)
(* usable definition CurrentTermAtLeastAsLargeAsLogTermsForPrimary suppressed *)
(* usable definition TermsOfEntriesGrowMonotonically suppressed *)
(* usable definition OnePrimaryPerTerm suppressed *)
(* usable definition ExistsQuorumInLargestTerm suppressed *)
(* usable definition LogsMustBeSmallerThanOrEqualToLargestTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm suppressed *)
(* usable definition CommittedTermMatchesEntry suppressed *)
(* usable definition LogsLaterThanCommittedMustHaveCommitted suppressed *)
(* usable definition LogsEqualToCommittedMustHaveCommittedIfItFits suppressed *)
(* usable definition CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens suppressed *)
(* usable definition CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms suppressed *)
(* usable definition LeaderCompletenessGeneralized suppressed *)
(* usable definition CommittedEntriesMustHaveQuorums suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
fixes MaxLogLen
fixes MaxTerm
fixes NumRandSubsets
(* usable definition StateConstraint suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition LemmaBasic suppressed *)
assumes v'253: "(TypeOK)"
assumes v'254: "(Next)"
assumes v'255: "(TypeOK)"
assumes v'256: "(Next)"
assumes v'266: "(\<exists> s \<in> (Server) : (\<exists> t \<in> (Server) : ((((greater ((fapply ((currentTerm), (s))), (fapply ((currentTerm), (t)))))) & ((((a_currentTermhash_primea :: c)) = ([(currentTerm) EXCEPT ![(t)] = (fapply ((currentTerm), (s)))]))) & ((((a_statehash_primea :: c)) = ([(state) EXCEPT ![(t)] = (Secondary)])))) & (((((a_loghash_primea :: c)) = (log))) & ((((a_confighash_primea :: c)) = (config))) & ((((a_electionshash_primea :: c)) = (elections))) & ((((a_committedhash_primea :: c)) = (committed)))))))"
fixes s
assumes s_in : "(s \<in> (Server))"
fixes t
assumes t_in : "(t \<in> (Server))"
assumes v'272: "((greater ((fapply ((currentTerm), (s))), (fapply ((currentTerm), (t))))))"
assumes v'273: "((((a_currentTermhash_primea :: c)) = ([(currentTerm) EXCEPT ![(t)] = (fapply ((currentTerm), (s)))])))"
assumes v'274: "((((a_statehash_primea :: c)) = ([(state) EXCEPT ![(t)] = (Secondary)])))"
assumes v'275: "((((a_loghash_primea :: c)) = (log)))"
assumes v'276: "((((a_confighash_primea :: c)) = (config)))"
assumes v'277: "((((a_electionshash_primea :: c)) = (elections)))"
assumes v'278: "((((a_committedhash_primea :: c)) = (committed)))"
shows "((((a_statehash_primea :: c)) = ([(state) EXCEPT ![(t)] = (Secondary)])))"(is "PROP ?ob'151")
proof -
ML_command {* writeln "*** TLAPS ENTER 151"; *}
show "PROP ?ob'151"

(* BEGIN ZENON INPUT
;; file=MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_f71946.znn; winfile="`cygpath -a -w "MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_f71946.znn"`"; PATH='/usr/bin:/cygdrive/c/Program Files (x86)/Common Files/Oracle/Java/javapath:/cygdrive/c/WINDOWS/system32:/cygdrive/c/WINDOWS:/cygdrive/c/WINDOWS/System32/Wbem:/cygdrive/c/WINDOWS/System32/WindowsPowerShell/v1.0:/cygdrive/c/WINDOWS/System32/OpenSSH:/cygdrive/c/Program Files/Git/cmd:/cygdrive/c/Program Files/PuTTY:/cygdrive/c/Program Files/CMake/bin:/cygdrive/c/Program Files/Java/jdk-14.0.2/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32/Scripts:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32:/cygdrive/c/Users/ianda/AppData/Local/Microsoft/WindowsApps:/cygdrive/c/Users/ianda/AppData/Local/Programs/MiKTeX 2.9/miktex/bin/x64:/cygdrive/c/Program Files (x86)/GnuWin32/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Microsoft VS Code/bin:/cygdrive/c/MinGW/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_f71946.znn.out
;; obligation #151
$hyp "v'253" TypeOK
$hyp "v'254" Next
$hyp "v'255" TypeOK
$hyp "v'256" Next
$hyp "v'266" (TLA.bEx Server ((s) (TLA.bEx Server ((t) (/\ (/\ (arith.lt (TLA.fapply currentTerm t)
(TLA.fapply currentTerm s)) (= a_currentTermhash_primea
(TLA.except currentTerm t (TLA.fapply currentTerm s))) (= a_statehash_primea
(TLA.except state t Secondary))) (/\ (= a_loghash_primea log)
(= a_confighash_primea config) (= a_electionshash_primea elections)
(= a_committedhash_primea
committed)))))))
$hyp "s_in" (TLA.in s Server)
$hyp "t_in" (TLA.in t Server)
$hyp "v'272" (arith.lt (TLA.fapply currentTerm t)
(TLA.fapply currentTerm s))
$hyp "v'273" (= a_currentTermhash_primea
(TLA.except currentTerm t (TLA.fapply currentTerm s)))
$hyp "v'274" (= a_statehash_primea
(TLA.except state t Secondary))
$hyp "v'275" (= a_loghash_primea log)
$hyp "v'276" (= a_confighash_primea
config)
$hyp "v'277" (= a_electionshash_primea
elections)
$hyp "v'278" (= a_committedhash_primea committed)
$goal (= a_statehash_primea
(TLA.except state t Secondary))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"(a_statehash_primea=except(state, t, Secondary))" (is "_=?z_ho")
 using v'274 by blast
 assume z_Hm:"(a_statehash_primea~=?z_ho)"
 show FALSE
 by (rule notE [OF z_Hm z_Hh])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 151"; *} qed
lemma ob'334:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Server
fixes Secondary
fixes Primary
fixes Nil
fixes currentTerm currentTerm'
fixes state state'
fixes log log'
fixes config config'
fixes elections elections'
fixes committed committed'
(* usable definition vars suppressed *)
(* usable definition Empty suppressed *)
(* usable definition InLog suppressed *)
(* usable definition LastTerm suppressed *)
(* usable definition LastEntry suppressed *)
(* usable definition GetTerm suppressed *)
(* usable definition LogTerm suppressed *)
(* usable definition Quorums suppressed *)
(* usable definition QuorumsAt suppressed *)
(* usable definition CanRollback suppressed *)
(* usable definition CanVoteForOplog suppressed *)
(* usable definition ImmediatelyCommitted suppressed *)
(* usable definition UpdateTermsExpr suppressed *)
(* usable definition ClientRequest suppressed *)
(* usable definition GetEntries suppressed *)
(* usable definition RollbackEntries suppressed *)
(* usable definition BecomeLeader suppressed *)
(* usable definition CommitEntry suppressed *)
(* usable definition UpdateTerms suppressed *)
(* usable definition Init suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ElectionSafety suppressed *)
(* usable definition LeaderCompleteness suppressed *)
(* usable definition StateMachineSafety suppressed *)
(* usable definition EqualUpTo suppressed *)
(* usable definition LogMatching suppressed *)
(* usable definition Max suppressed *)
(* usable definition ExistsPrimary suppressed *)
(* usable definition AllConfigsAreServer suppressed *)
(* usable definition CurrentTermAtLeastAsLargeAsLogTermsForPrimary suppressed *)
(* usable definition TermsOfEntriesGrowMonotonically suppressed *)
(* usable definition OnePrimaryPerTerm suppressed *)
(* usable definition ExistsQuorumInLargestTerm suppressed *)
(* usable definition LogsMustBeSmallerThanOrEqualToLargestTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm suppressed *)
(* usable definition CommittedTermMatchesEntry suppressed *)
(* usable definition LogsLaterThanCommittedMustHaveCommitted suppressed *)
(* usable definition LogsEqualToCommittedMustHaveCommittedIfItFits suppressed *)
(* usable definition CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens suppressed *)
(* usable definition CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms suppressed *)
(* usable definition LeaderCompletenessGeneralized suppressed *)
(* usable definition CommittedEntriesMustHaveQuorums suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
fixes MaxLogLen
fixes MaxTerm
fixes NumRandSubsets
(* usable definition StateConstraint suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition LemmaBasic suppressed *)
assumes v'258: "(LemmaBasic)"
assumes v'259: "(TypeOK)"
assumes v'260: "(Next)"
assumes v'261: "(\<forall> s \<in> (Server) : (((((fapply (((a_loghash_primea :: c)), (s))) = (fapply ((log), (s))))) \<Rightarrow> (\<forall> i \<in> ((DOMAIN (fapply (((a_loghash_primea :: c)), (s))))) : (\<forall> j \<in> ((DOMAIN (fapply (((a_loghash_primea :: c)), (s))))) : ((((leq ((i), (j)))) \<Rightarrow> ((leq ((fapply ((fapply (((a_loghash_primea :: c)), (s))), (i))), (fapply ((fapply (((a_loghash_primea :: c)), (s))), (j)))))))))))))"
assumes v'262: "((((((a_loghash_primea :: c)) = (log))) \<Rightarrow> ((a_hb977ca9e2ca1e0e08e524e321e42b0a :: c))))"
fixes s
assumes s_in : "(s \<in> (Server))"
assumes v'266: "((ClientRequest ((s))))"
assumes v'269: "(((fapply ((state), (s))) = (Primary)))"
assumes v'275: "(((fapply (((a_loghash_primea :: c)), (s))) = ((Append ((fapply ((log), (s))), (fapply ((currentTerm), (s))))))))"
assumes v'276: "(\<forall> i \<in> ((DOMAIN (fapply ((log), (s))))) : ((leq ((fapply ((fapply ((log), (s))), (i))), (fapply ((currentTerm), (s)))))))"
assumes v'277: "(((TypeOK) \<Longrightarrow> ((Next) \<Longrightarrow> ((LemmaBasic) \<Longrightarrow> (\<And> s_1 :: c. s_1 \<in> (Server) \<Longrightarrow> (\<And> newEntry :: c. ((((fapply (((a_loghash_primea :: c)), (s_1))) = ((Append ((fapply ((log), (s_1))), (newEntry)))))) \<Longrightarrow> ((\<forall> i \<in> ((DOMAIN (fapply ((log), (s_1))))) : ((leq ((fapply ((fapply ((log), (s_1))), (i))), (newEntry))))) \<Longrightarrow> (\<forall> i \<in> ((DOMAIN (fapply (((a_loghash_primea :: c)), (s_1))))) : (\<forall> j \<in> ((DOMAIN (fapply (((a_loghash_primea :: c)), (s_1))))) : ((((leq ((i), (j)))) \<Rightarrow> ((leq ((fapply ((fapply (((a_loghash_primea :: c)), (s_1))), (i))), (fapply ((fapply (((a_loghash_primea :: c)), (s_1))), (j))))))))))))))))))"
shows "(\<forall> i \<in> ((DOMAIN (fapply (((a_loghash_primea :: c)), (s))))) : (\<forall> j \<in> ((DOMAIN (fapply (((a_loghash_primea :: c)), (s))))) : ((((leq ((i), (j)))) \<Rightarrow> ((leq ((fapply ((fapply (((a_loghash_primea :: c)), (s))), (i))), (fapply ((fapply (((a_loghash_primea :: c)), (s))), (j))))))))))"(is "PROP ?ob'334")
proof -
ML_command {* writeln "*** TLAPS ENTER 334"; *}
show "PROP ?ob'334"

(* BEGIN ZENON INPUT
;; file=MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_690f26.znn; winfile="`cygpath -a -w "MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_690f26.znn"`"; PATH='/usr/bin:/cygdrive/c/Program Files (x86)/Common Files/Oracle/Java/javapath:/cygdrive/c/WINDOWS/system32:/cygdrive/c/WINDOWS:/cygdrive/c/WINDOWS/System32/Wbem:/cygdrive/c/WINDOWS/System32/WindowsPowerShell/v1.0:/cygdrive/c/WINDOWS/System32/OpenSSH:/cygdrive/c/Program Files/Git/cmd:/cygdrive/c/Program Files/PuTTY:/cygdrive/c/Program Files/CMake/bin:/cygdrive/c/Program Files/Java/jdk-14.0.2/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32/Scripts:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32:/cygdrive/c/Users/ianda/AppData/Local/Microsoft/WindowsApps:/cygdrive/c/Users/ianda/AppData/Local/Programs/MiKTeX 2.9/miktex/bin/x64:/cygdrive/c/Program Files (x86)/GnuWin32/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Microsoft VS Code/bin:/cygdrive/c/MinGW/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_690f26.znn.out
;; obligation #334
$hyp "v'258" LemmaBasic
$hyp "v'259" TypeOK
$hyp "v'260" Next
$hyp "v'261" (TLA.bAll Server ((s) (=> (= (TLA.fapply a_loghash_primea s)
(TLA.fapply log s))
(TLA.bAll (TLA.DOMAIN (TLA.fapply a_loghash_primea s)) ((i) (TLA.bAll (TLA.DOMAIN (TLA.fapply a_loghash_primea s)) ((j) (=> (arith.le i
j) (arith.le (TLA.fapply (TLA.fapply a_loghash_primea s) i)
(TLA.fapply (TLA.fapply a_loghash_primea s) j))))))))))
$hyp "v'262" (=> (= a_loghash_primea log)
a_hb977ca9e2ca1e0e08e524e321e42b0a)
$hyp "s_in" (TLA.in s Server)
$hyp "v'266" (ClientRequest s)
$hyp "v'269" (= (TLA.fapply state s)
Primary)
$hyp "v'275" (= (TLA.fapply a_loghash_primea s)
(TLA.Append (TLA.fapply log s)
(TLA.fapply currentTerm s)))
$hyp "v'276" (TLA.bAll (TLA.DOMAIN (TLA.fapply log s)) ((i) (arith.le (TLA.fapply (TLA.fapply log s) i)
(TLA.fapply currentTerm s))))
$hyp "v'277" (=> TypeOK (=> Next (=> LemmaBasic (TLA.bAll Server ((s_1) (A. ((newEntry) (=> (= (TLA.fapply a_loghash_primea s_1)
(TLA.Append (TLA.fapply log s_1)
newEntry)) (=> (TLA.bAll (TLA.DOMAIN (TLA.fapply log s_1)) ((i) (arith.le (TLA.fapply (TLA.fapply log s_1) i)
newEntry))) (TLA.bAll (TLA.DOMAIN (TLA.fapply a_loghash_primea s_1)) ((i) (TLA.bAll (TLA.DOMAIN (TLA.fapply a_loghash_primea s_1)) ((j) (=> (arith.le i
j) (arith.le (TLA.fapply (TLA.fapply a_loghash_primea s_1) i)
(TLA.fapply (TLA.fapply a_loghash_primea s_1) j))))))))))))))))
$goal (TLA.bAll (TLA.DOMAIN (TLA.fapply a_loghash_primea s)) ((i) (TLA.bAll (TLA.DOMAIN (TLA.fapply a_loghash_primea s)) ((j) (=> (arith.le i
j) (arith.le (TLA.fapply (TLA.fapply a_loghash_primea s) i)
(TLA.fapply (TLA.fapply a_loghash_primea s) j)))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hk:"(TypeOK=>(Next=>(LemmaBasic=>bAll(Server, (\<lambda>s_1. (\\A newEntry:(((a_loghash_primea[s_1])=Append((log[s_1]), newEntry))=>(bAll(DOMAIN((log[s_1])), (\<lambda>i. (((log[s_1])[i]) <= newEntry)))=>bAll(DOMAIN((a_loghash_primea[s_1])), (\<lambda>i. bAll(DOMAIN((a_loghash_primea[s_1])), (\<lambda>j. ((i <= j)=>(((a_loghash_primea[s_1])[i]) <= ((a_loghash_primea[s_1])[j])))))))))))))))" (is "_=>?z_hm")
 using v'277 by blast
 have z_Hb:"TypeOK"
 using v'259 by blast
 have z_Hc:"Next"
 using v'260 by blast
 have z_Ha:"LemmaBasic"
 using v'258 by blast
 have z_Hj:"bAll(DOMAIN((log[s])), (\<lambda>i. (((log[s])[i]) <= (currentTerm[s]))))" (is "?z_hj")
 using v'276 by blast
 have z_Hi:"((a_loghash_primea[s])=Append((log[s]), (currentTerm[s])))" (is "?z_hcb=?z_hcc")
 using v'275 by blast
 have z_Hf:"(s \\in Server)" (is "?z_hf")
 using s_in by blast
 assume z_Hl:"(~bAll(DOMAIN(?z_hcb), (\<lambda>i. bAll(DOMAIN(?z_hcb), (\<lambda>j. ((i <= j)=>((?z_hcb[i]) <= (?z_hcb[j]))))))))" (is "~?z_hcd")
 show FALSE
 proof (rule zenon_imply [OF z_Hk])
  assume z_Hcm:"(~TypeOK)"
  show FALSE
  by (rule notE [OF z_Hcm z_Hb])
 next
  assume z_Hm:"?z_hm" (is "_=>?z_hn")
  show FALSE
  proof (rule zenon_imply [OF z_Hm])
   assume z_Hcn:"(~Next)"
   show FALSE
   by (rule notE [OF z_Hcn z_Hc])
  next
   assume z_Hn:"?z_hn" (is "_=>?z_ho")
   show FALSE
   proof (rule zenon_imply [OF z_Hn])
    assume z_Hco:"(~LemmaBasic)"
    show FALSE
    by (rule notE [OF z_Hco z_Ha])
   next
    assume z_Ho:"?z_ho"
    have z_Hcp_z_Ho: "(\\A x:((x \\in Server)=>(\\A newEntry:(((a_loghash_primea[x])=Append((log[x]), newEntry))=>(bAll(DOMAIN((log[x])), (\<lambda>i. (((log[x])[i]) <= newEntry)))=>bAll(DOMAIN((a_loghash_primea[x])), (\<lambda>i. bAll(DOMAIN((a_loghash_primea[x])), (\<lambda>j. ((i <= j)=>(((a_loghash_primea[x])[i]) <= ((a_loghash_primea[x])[j])))))))))))) == ?z_ho" (is "?z_hcp == _")
    by (unfold bAll_def)
    have z_Hcp: "?z_hcp" (is "\\A x : ?z_hdo(x)")
    by (unfold z_Hcp_z_Ho, fact z_Ho)
    have z_Hdp: "?z_hdo(s)" (is "_=>?z_hdq")
    by (rule zenon_all_0 [of "?z_hdo" "s", OF z_Hcp])
    show FALSE
    proof (rule zenon_imply [OF z_Hdp])
     assume z_Hdr:"(~?z_hf)"
     show FALSE
     by (rule notE [OF z_Hdr z_Hf])
    next
     assume z_Hdq:"?z_hdq" (is "\\A x : ?z_hds(x)")
     have z_Hdt: "?z_hds((currentTerm[s]))" (is "?z_hi=>?z_hdu")
     by (rule zenon_all_0 [of "?z_hds" "(currentTerm[s])", OF z_Hdq])
     show FALSE
     proof (rule zenon_imply [OF z_Hdt])
      assume z_Hdv:"(?z_hcb~=?z_hcc)"
      show FALSE
      by (rule notE [OF z_Hdv z_Hi])
     next
      assume z_Hdu:"?z_hdu"
      show FALSE
      proof (rule zenon_imply [OF z_Hdu])
       assume z_Hdw:"(~?z_hj)"
       show FALSE
       by (rule notE [OF z_Hdw z_Hj])
      next
       assume z_Hcd:"?z_hcd"
       show FALSE
       by (rule notE [OF z_Hl z_Hcd])
      qed
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 334"; *} qed
lemma ob'433:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Server
fixes Secondary
fixes Primary
fixes Nil
fixes currentTerm currentTerm'
fixes state state'
fixes log log'
fixes config config'
fixes elections elections'
fixes committed committed'
(* usable definition vars suppressed *)
(* usable definition Empty suppressed *)
(* usable definition InLog suppressed *)
(* usable definition LastTerm suppressed *)
(* usable definition LastEntry suppressed *)
(* usable definition GetTerm suppressed *)
(* usable definition LogTerm suppressed *)
(* usable definition Quorums suppressed *)
(* usable definition QuorumsAt suppressed *)
(* usable definition CanRollback suppressed *)
(* usable definition CanVoteForOplog suppressed *)
(* usable definition ImmediatelyCommitted suppressed *)
(* usable definition UpdateTermsExpr suppressed *)
(* usable definition ClientRequest suppressed *)
(* usable definition GetEntries suppressed *)
(* usable definition RollbackEntries suppressed *)
(* usable definition BecomeLeader suppressed *)
(* usable definition CommitEntry suppressed *)
(* usable definition UpdateTerms suppressed *)
(* usable definition Init suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ElectionSafety suppressed *)
(* usable definition LeaderCompleteness suppressed *)
(* usable definition StateMachineSafety suppressed *)
(* usable definition EqualUpTo suppressed *)
(* usable definition LogMatching suppressed *)
(* usable definition Max suppressed *)
(* usable definition ExistsPrimary suppressed *)
(* usable definition AllConfigsAreServer suppressed *)
(* usable definition CurrentTermAtLeastAsLargeAsLogTermsForPrimary suppressed *)
(* usable definition TermsOfEntriesGrowMonotonically suppressed *)
(* usable definition ExistsQuorumInLargestTerm suppressed *)
(* usable definition LogsMustBeSmallerThanOrEqualToLargestTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm suppressed *)
(* usable definition CommittedTermMatchesEntry suppressed *)
(* usable definition LogsLaterThanCommittedMustHaveCommitted suppressed *)
(* usable definition LogsEqualToCommittedMustHaveCommittedIfItFits suppressed *)
(* usable definition CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens suppressed *)
(* usable definition CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms suppressed *)
(* usable definition LeaderCompletenessGeneralized suppressed *)
(* usable definition CommittedEntriesMustHaveQuorums suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
fixes MaxLogLen
fixes MaxTerm
fixes NumRandSubsets
(* usable definition StateConstraint suppressed *)
(* usable definition TypeOK suppressed *)
assumes v'257: "((CurrentTermAtLeastAsLargeAsLogTermsForPrimary) & (TermsOfEntriesGrowMonotonically) & (\<forall> s \<in> (Server) : (((((fapply ((state), (s))) = (Primary))) \<Rightarrow> (\<forall> t \<in> (Server) : (((((((fapply ((state), (t))) = (Primary))) \<and> (((fapply ((currentTerm), (s))) = (fapply ((currentTerm), (t))))))) \<Rightarrow> (((s) = (t))))))))) & (ExistsQuorumInLargestTerm) & (LogsMustBeSmallerThanOrEqualToLargestTerm) & (AllConfigsAreServer))"
assumes v'258: "(TypeOK)"
assumes v'259: "(Next)"
fixes p
assumes p_in : "(p \<in> (Server))"
fixes Q
assumes Q_in : "(Q \<in> ((QuorumsAt ((p)))))"
assumes v'267: "((BecomeLeader ((p), (Q))))"
assumes v'270: "(\<forall> t \<in> (Server) : ((geq ((fapply ((currentTerm), (p))), (fapply ((currentTerm), (t)))))))"
assumes v'271: "(((fapply (((a_statehash_primea :: c)), (p))) = (Primary)))"
fixes s
assumes s_in : "(s \<in> (Server))"
assumes v'276: "(((fapply (((a_statehash_primea :: c)), (s))) = (Primary)))"
assumes v'277: "(((s) \<notin> (Q)))"
fixes t
assumes t_in : "(t \<in> (Server))"
assumes v'279: "(((fapply (((a_statehash_primea :: c)), (t))) = (Primary)))"
assumes v'280: "(((t) \<notin> (Q)))"
assumes v'281: "(((fapply (((a_currentTermhash_primea :: c)), (t))) = (fapply (((a_currentTermhash_primea :: c)), (s)))))"
assumes v'284: "(((fapply (((a_statehash_primea :: c)), (s))) = (fapply ((state), (s)))))"
assumes v'285: "(((fapply ((currentTerm), (s))) = (fapply (((a_currentTermhash_primea :: c)), (s)))))"
assumes v'286: "(((fapply (((a_statehash_primea :: c)), (t))) = (fapply ((state), (t)))))"
assumes v'287: "(((fapply ((currentTerm), (t))) = (fapply (((a_currentTermhash_primea :: c)), (t)))))"
shows "(\<forall> u \<in> (Server) : (((((((fapply ((state), (u))) = (Primary))) \<and> (((u) \<notin> (Q))))) \<Rightarrow> (((((((fapply ((state), (s))) = (Primary))) \<and> (((fapply ((currentTerm), (s))) = (fapply ((currentTerm), (u))))))) \<Rightarrow> (((s) = (u))))))))"(is "PROP ?ob'433")
proof -
ML_command {* writeln "*** TLAPS ENTER 433"; *}
show "PROP ?ob'433"

(* BEGIN ZENON INPUT
;; file=MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_08c2ee.znn; winfile="`cygpath -a -w "MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_08c2ee.znn"`"; PATH='/usr/bin:/cygdrive/c/Program Files (x86)/Common Files/Oracle/Java/javapath:/cygdrive/c/WINDOWS/system32:/cygdrive/c/WINDOWS:/cygdrive/c/WINDOWS/System32/Wbem:/cygdrive/c/WINDOWS/System32/WindowsPowerShell/v1.0:/cygdrive/c/WINDOWS/System32/OpenSSH:/cygdrive/c/Program Files/Git/cmd:/cygdrive/c/Program Files/PuTTY:/cygdrive/c/Program Files/CMake/bin:/cygdrive/c/Program Files/Java/jdk-14.0.2/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32/Scripts:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32:/cygdrive/c/Users/ianda/AppData/Local/Microsoft/WindowsApps:/cygdrive/c/Users/ianda/AppData/Local/Programs/MiKTeX 2.9/miktex/bin/x64:/cygdrive/c/Program Files (x86)/GnuWin32/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Microsoft VS Code/bin:/cygdrive/c/MinGW/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_08c2ee.znn.out
;; obligation #433
$hyp "v'257" (/\ CurrentTermAtLeastAsLargeAsLogTermsForPrimary
TermsOfEntriesGrowMonotonically
(TLA.bAll Server ((s) (=> (= (TLA.fapply state s) Primary)
(TLA.bAll Server ((t) (=> (/\ (= (TLA.fapply state t) Primary)
(= (TLA.fapply currentTerm s) (TLA.fapply currentTerm t))) (= s t)))))))
ExistsQuorumInLargestTerm LogsMustBeSmallerThanOrEqualToLargestTerm
AllConfigsAreServer)
$hyp "v'258" TypeOK
$hyp "v'259" Next
$hyp "p_in" (TLA.in p Server)
$hyp "Q_in" (TLA.in Q (QuorumsAt p))
$hyp "v'267" (BecomeLeader p
Q)
$hyp "v'270" (TLA.bAll Server ((t) (arith.le (TLA.fapply currentTerm t)
(TLA.fapply currentTerm p))))
$hyp "v'271" (= (TLA.fapply a_statehash_primea p)
Primary)
$hyp "s_in" (TLA.in s Server)
$hyp "v'276" (= (TLA.fapply a_statehash_primea s)
Primary)
$hyp "v'277" (-. (TLA.in s
Q))
$hyp "t_in" (TLA.in t Server)
$hyp "v'279" (= (TLA.fapply a_statehash_primea t)
Primary)
$hyp "v'280" (-. (TLA.in t
Q))
$hyp "v'281" (= (TLA.fapply a_currentTermhash_primea t)
(TLA.fapply a_currentTermhash_primea s))
$hyp "v'284" (= (TLA.fapply a_statehash_primea s)
(TLA.fapply state s))
$hyp "v'285" (= (TLA.fapply currentTerm s)
(TLA.fapply a_currentTermhash_primea s))
$hyp "v'286" (= (TLA.fapply a_statehash_primea t)
(TLA.fapply state t))
$hyp "v'287" (= (TLA.fapply currentTerm t)
(TLA.fapply a_currentTermhash_primea t))
$goal (TLA.bAll Server ((u) (=> (/\ (= (TLA.fapply state u) Primary)
(-. (TLA.in u Q))) (=> (/\ (= (TLA.fapply state s) Primary)
(= (TLA.fapply currentTerm s) (TLA.fapply currentTerm u))) (= s
u)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(CurrentTermAtLeastAsLargeAsLogTermsForPrimary&(TermsOfEntriesGrowMonotonically&(bAll(Server, (\<lambda>s. (((state[s])=Primary)=>bAll(Server, (\<lambda>t. ((((state[t])=Primary)&((currentTerm[s])=(currentTerm[t])))=>(s=t)))))))&(ExistsQuorumInLargestTerm&(LogsMustBeSmallerThanOrEqualToLargestTerm&AllConfigsAreServer)))))" (is "_&?z_hv")
 using v'257 by blast
 have z_Hi:"(s \\in Server)" (is "?z_hi")
 using s_in by blast
 assume z_Ht:"(~bAll(Server, (\<lambda>u. ((((state[u])=Primary)&(~(u \\in Q)))=>((((state[s])=Primary)&((currentTerm[s])=(currentTerm[u])))=>(s=u))))))" (is "~?z_hby")
 have z_Hv: "?z_hv" (is "_&?z_hx")
 by (rule zenon_and_1 [OF z_Ha])
 have z_Hx: "?z_hx" (is "?z_hy&?z_hbt")
 by (rule zenon_and_1 [OF z_Hv])
 have z_Hy: "?z_hy"
 by (rule zenon_and_0 [OF z_Hx])
 have z_Hcn_z_Hy: "(\\A x:((x \\in Server)=>(((state[x])=Primary)=>bAll(Server, (\<lambda>t. ((((state[t])=Primary)&((currentTerm[x])=(currentTerm[t])))=>(x=t))))))) == ?z_hy" (is "?z_hcn == _")
 by (unfold bAll_def)
 have z_Hcn: "?z_hcn" (is "\\A x : ?z_hdb(x)")
 by (unfold z_Hcn_z_Hy, fact z_Hy)
 have z_Hdc_z_Ht: "(~(\\A x:((x \\in Server)=>((((state[x])=Primary)&(~(x \\in Q)))=>((((state[s])=Primary)&((currentTerm[s])=(currentTerm[x])))=>(s=x)))))) == (~?z_hby)" (is "?z_hdc == ?z_ht")
 by (unfold bAll_def)
 have z_Hdc: "?z_hdc" (is "~(\\A x : ?z_hdn(x))")
 by (unfold z_Hdc_z_Ht, fact z_Ht)
 have z_Hdo: "(\\E x:(~((x \\in Server)=>((((state[x])=Primary)&(~(x \\in Q)))=>((((state[s])=Primary)&((currentTerm[s])=(currentTerm[x])))=>(s=x))))))" (is "\\E x : ?z_hdq(x)")
 by (rule zenon_notallex_0 [of "?z_hdn", OF z_Hdc])
 have z_Hdr: "?z_hdq((CHOOSE x:(~((x \\in Server)=>((((state[x])=Primary)&(~(x \\in Q)))=>((((state[s])=Primary)&((currentTerm[s])=(currentTerm[x])))=>(s=x)))))))" (is "~(?z_hdt=>?z_hdu)")
 by (rule zenon_ex_choose_0 [of "?z_hdq", OF z_Hdo])
 have z_Hdt: "?z_hdt"
 by (rule zenon_notimply_0 [OF z_Hdr])
 have z_Hdv: "(~?z_hdu)" (is "~(?z_hdw=>?z_hdx)")
 by (rule zenon_notimply_1 [OF z_Hdr])
 have z_Hdw: "?z_hdw" (is "?z_hdy&?z_hdz")
 by (rule zenon_notimply_0 [OF z_Hdv])
 have z_Hea: "(~?z_hdx)" (is "~(?z_heb=>?z_hec)")
 by (rule zenon_notimply_1 [OF z_Hdv])
 have z_Heb: "?z_heb" (is "?z_hbc&?z_hed")
 by (rule zenon_notimply_0 [OF z_Hea])
 have z_Hee: "(s~=(CHOOSE x:(~((x \\in Server)=>((((state[x])=Primary)&(~(x \\in Q)))=>((?z_hbc&((currentTerm[s])=(currentTerm[x])))=>(s=x)))))))" (is "_~=?z_hds")
 by (rule zenon_notimply_1 [OF z_Hea])
 have z_Hbc: "?z_hbc" (is "?z_hbd=_")
 by (rule zenon_and_0 [OF z_Heb])
 have z_Hed: "?z_hed" (is "?z_hbp=?z_hef")
 by (rule zenon_and_1 [OF z_Heb])
 have z_Hdy: "?z_hdy" (is "?z_heg=_")
 by (rule zenon_and_0 [OF z_Hdw])
 have z_Heh: "?z_hdb(?z_hds)" (is "_=>?z_hei")
 by (rule zenon_all_0 [of "?z_hdb" "?z_hds", OF z_Hcn])
 show FALSE
 proof (rule zenon_imply [OF z_Heh])
  assume z_Hej:"(~?z_hdt)"
  show FALSE
  by (rule notE [OF z_Hej z_Hdt])
 next
  assume z_Hei:"?z_hei" (is "_=>?z_hek")
  show FALSE
  proof (rule zenon_imply [OF z_Hei])
   assume z_Hel:"(?z_heg~=Primary)"
   show FALSE
   by (rule notE [OF z_Hel z_Hdy])
  next
   assume z_Hek:"?z_hek"
   have z_Hem: "((?z_hbc&(?z_hef=?z_hbp))=>(?z_hds=s))" (is "?z_hen=>?z_hep")
   by (rule zenon_all_in_0 [of "Server" "(\<lambda>t. ((((state[t])=Primary)&(?z_hef=(currentTerm[t])))=>(?z_hds=t)))", OF z_Hek z_Hi])
   show FALSE
   proof (rule zenon_imply [OF z_Hem])
    assume z_Hev:"(~?z_hen)" (is "~(_&?z_heo)")
    show FALSE
    proof (rule zenon_notand [OF z_Hev])
     assume z_Hew:"(?z_hbd~=Primary)"
     show FALSE
     by (rule notE [OF z_Hew z_Hbc])
    next
     assume z_Hex:"(?z_hef~=?z_hbp)"
     show FALSE
     by (rule zenon_eqsym [OF z_Hed z_Hex])
    qed
   next
    assume z_Hep:"?z_hep"
    show FALSE
    by (rule zenon_eqsym [OF z_Hep z_Hee])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 433"; *} qed
lemma ob'532:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Server
fixes Secondary
fixes Primary
fixes Nil
fixes currentTerm currentTerm'
fixes state state'
fixes log log'
fixes config config'
fixes elections elections'
fixes committed committed'
(* usable definition vars suppressed *)
(* usable definition Empty suppressed *)
(* usable definition InLog suppressed *)
(* usable definition LastTerm suppressed *)
(* usable definition LastEntry suppressed *)
(* usable definition GetTerm suppressed *)
(* usable definition LogTerm suppressed *)
(* usable definition Quorums suppressed *)
(* usable definition QuorumsAt suppressed *)
(* usable definition CanRollback suppressed *)
(* usable definition CanVoteForOplog suppressed *)
(* usable definition ImmediatelyCommitted suppressed *)
(* usable definition UpdateTermsExpr suppressed *)
(* usable definition ClientRequest suppressed *)
(* usable definition GetEntries suppressed *)
(* usable definition RollbackEntries suppressed *)
(* usable definition BecomeLeader suppressed *)
(* usable definition CommitEntry suppressed *)
(* usable definition UpdateTerms suppressed *)
(* usable definition Init suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ElectionSafety suppressed *)
(* usable definition LeaderCompleteness suppressed *)
(* usable definition StateMachineSafety suppressed *)
(* usable definition EqualUpTo suppressed *)
(* usable definition LogMatching suppressed *)
(* usable definition Max suppressed *)
(* usable definition ExistsPrimary suppressed *)
(* usable definition AllConfigsAreServer suppressed *)
(* usable definition CurrentTermAtLeastAsLargeAsLogTermsForPrimary suppressed *)
(* usable definition TermsOfEntriesGrowMonotonically suppressed *)
(* usable definition OnePrimaryPerTerm suppressed *)
(* usable definition ExistsQuorumInLargestTerm suppressed *)
(* usable definition LogsMustBeSmallerThanOrEqualToLargestTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm suppressed *)
(* usable definition SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm suppressed *)
(* usable definition CommittedTermMatchesEntry suppressed *)
(* usable definition LogsLaterThanCommittedMustHaveCommitted suppressed *)
(* usable definition LogsEqualToCommittedMustHaveCommittedIfItFits suppressed *)
(* usable definition CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens suppressed *)
(* usable definition CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms suppressed *)
(* usable definition LeaderCompletenessGeneralized suppressed *)
(* usable definition CommittedEntriesMustHaveQuorums suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
fixes MaxLogLen
fixes MaxTerm
fixes NumRandSubsets
(* usable definition StateConstraint suppressed *)
(* usable definition LemmaBasic suppressed *)
assumes v'262: "(LemmaBasic)"
assumes v'263: "((((currentTerm) \<in> ([(Server) \<rightarrow> (Nat)]))) & (((state) \<in> ([(Server) \<rightarrow> ({(Secondary), (Primary)})]))) & (((log) \<in> ([(Server) \<rightarrow> ((Seq ((Nat))))]))) & (((config) \<in> ([(Server) \<rightarrow> ((SUBSET (Server)))]))) & (((elections) \<in> ((SUBSET ([''leader'' : (Server), ''term'' : (Nat)]))))) & (((committed) \<in> ((SUBSET ([''entry'' : (((Nat) \<times> (Nat))), ''term'' : (Nat)]))))))"
assumes v'264: "(Next)"
fixes s
assumes s_in : "(s \<in> (Server))"
assumes v'268: "((ClientRequest ((s))))"
assumes v'274: "((((a_loghash_primea :: c)) = ([(log) EXCEPT ![(s)] = ((Append ((fapply ((log), (s))), (fapply ((currentTerm), (s))))))])))"
assumes v'275: "((geq ((fapply ((currentTerm), (s))), (fapply ((currentTerm), (s))))))"
assumes v'276: "((((a_currentTermhash_primea :: c)) = (currentTerm)))"
assumes v'277: "((((((currentTerm) \<in> ([(Server) \<rightarrow> (Nat)]))) & (((state) \<in> ([(Server) \<rightarrow> ({(Secondary), (Primary)})]))) & (((log) \<in> ([(Server) \<rightarrow> ((Seq ((Nat))))]))) & (((config) \<in> ([(Server) \<rightarrow> ((SUBSET (Server)))]))) & (((elections) \<in> ((SUBSET ([''leader'' : (Server), ''term'' : (Nat)]))))) & (((committed) \<in> ((SUBSET ([''entry'' : (((Nat) \<times> (Nat))), ''term'' : (Nat)])))))) \<Longrightarrow> ((Next) \<Longrightarrow> ((LemmaBasic) \<Longrightarrow> (\<And> s_1 :: c. s_1 \<in> (Server) \<Longrightarrow> (\<And> newEntry :: c. (((((a_loghash_primea :: c)) = ([(log) EXCEPT ![(s_1)] = ((Append ((fapply ((log), (s_1))), (newEntry))))]))) \<Longrightarrow> (((((a_currentTermhash_primea :: c)) = (currentTerm))) \<Longrightarrow> (((\<exists> t \<in> (Server) : ((geq ((fapply ((currentTerm), (t))), (newEntry))))) \<Rightarrow> ((a_h9780c447f1ffed8e26022e32154760a :: c))))))))))))"
shows "((a_h9780c447f1ffed8e26022e32154760a :: c))"(is "PROP ?ob'532")
proof -
ML_command {* writeln "*** TLAPS ENTER 532"; *}
show "PROP ?ob'532"

(* BEGIN ZENON INPUT
;; file=MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_1ddeb0.znn; winfile="`cygpath -a -w "MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_1ddeb0.znn"`"; PATH='/usr/bin:/cygdrive/c/Program Files (x86)/Common Files/Oracle/Java/javapath:/cygdrive/c/WINDOWS/system32:/cygdrive/c/WINDOWS:/cygdrive/c/WINDOWS/System32/Wbem:/cygdrive/c/WINDOWS/System32/WindowsPowerShell/v1.0:/cygdrive/c/WINDOWS/System32/OpenSSH:/cygdrive/c/Program Files/Git/cmd:/cygdrive/c/Program Files/PuTTY:/cygdrive/c/Program Files/CMake/bin:/cygdrive/c/Program Files/Java/jdk-14.0.2/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32/Scripts:/cygdrive/c/Users/ianda/AppData/Local/Programs/Python/Python38-32:/cygdrive/c/Users/ianda/AppData/Local/Microsoft/WindowsApps:/cygdrive/c/Users/ianda/AppData/Local/Programs/MiKTeX 2.9/miktex/bin/x64:/cygdrive/c/Program Files (x86)/GnuWin32/bin:/cygdrive/c/Users/ianda/AppData/Local/Programs/Microsoft VS Code/bin:/cygdrive/c/MinGW/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >MongoStaticRaftProofsLemmaBasic.tlaps/tlapm_1ddeb0.znn.out
;; obligation #532
$hyp "v'262" LemmaBasic
$hyp "v'263" (/\ (TLA.in currentTerm (TLA.FuncSet Server arith.N))
(TLA.in state (TLA.FuncSet Server (TLA.set Secondary Primary))) (TLA.in log
(TLA.FuncSet Server (TLA.Seq arith.N))) (TLA.in config
(TLA.FuncSet Server (TLA.SUBSET Server))) (TLA.in elections
(TLA.SUBSET (TLA.recordset "leader" Server "term" arith.N)))
(TLA.in committed
(TLA.SUBSET (TLA.recordset "entry" (TLA.prod arith.N arith.N) "term" arith.N))))
$hyp "v'264" Next
$hyp "s_in" (TLA.in s Server)
$hyp "v'268" (ClientRequest s)
$hyp "v'274" (= a_loghash_primea
(TLA.except log s (TLA.Append (TLA.fapply log s)
(TLA.fapply currentTerm s))))
$hyp "v'275" (arith.le (TLA.fapply currentTerm s)
(TLA.fapply currentTerm s))
$hyp "v'276" (= a_currentTermhash_primea
currentTerm)
$hyp "v'277" (=> (/\ (TLA.in currentTerm (TLA.FuncSet Server arith.N))
(TLA.in state (TLA.FuncSet Server (TLA.set Secondary Primary))) (TLA.in log
(TLA.FuncSet Server (TLA.Seq arith.N))) (TLA.in config
(TLA.FuncSet Server (TLA.SUBSET Server))) (TLA.in elections
(TLA.SUBSET (TLA.recordset "leader" Server "term" arith.N)))
(TLA.in committed
(TLA.SUBSET (TLA.recordset "entry" (TLA.prod arith.N arith.N) "term" arith.N)))) (=> Next (=> LemmaBasic (TLA.bAll Server ((s_1) (A. ((newEntry) (=> (= a_loghash_primea
(TLA.except log s_1 (TLA.Append (TLA.fapply log s_1)
newEntry))) (=> (= a_currentTermhash_primea
currentTerm) (=> (TLA.bEx Server ((t) (arith.le newEntry
(TLA.fapply currentTerm t))))
a_h9780c447f1ffed8e26022e32154760a))))))))))
$goal a_h9780c447f1ffed8e26022e32154760a
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"((currentTerm \\in FuncSet(Server, Nat))&((state \\in FuncSet(Server, {Secondary, Primary}))&((log \\in FuncSet(Server, Seq(Nat)))&((config \\in FuncSet(Server, SUBSET(Server)))&((elections \\in SUBSET([''leader'' : (Server), ''term'' : (Nat)]))&(committed \\in SUBSET([''entry'' : (prod(Nat, Nat)), ''term'' : (Nat)])))))))" (is "?z_hk&?z_hp")
 using v'263 by blast
 have z_Hi:"((?z_hk&?z_hp)=>(Next=>(LemmaBasic=>bAll(Server, (\<lambda>s_1. (\\A newEntry:((a_loghash_primea=except(log, s_1, Append((log[s_1]), newEntry)))=>((a_currentTermhash_primea=currentTerm)=>(bEx(Server, (\<lambda>t. (newEntry <= (currentTerm[t]))))=>a_h9780c447f1ffed8e26022e32154760a)))))))))" (is "?z_hb=>?z_hbt")
 using v'277 by blast
 have z_Hc:"Next"
 using v'264 by blast
 have z_Ha:"LemmaBasic"
 using v'262 by blast
 have z_Hh:"(a_currentTermhash_primea=currentTerm)"
 using v'276 by blast
 have z_Hf:"(a_loghash_primea=except(log, s, Append((log[s]), (currentTerm[s]))))" (is "_=?z_hcp")
 using v'274 by blast
 have z_Hg:"((currentTerm[s]) <= (currentTerm[s]))" (is "?z_hg")
 using v'275 by blast
 have z_Hd:"(s \\in Server)" (is "?z_hd")
 using s_in by blast
 assume z_Hj:"(~a_h9780c447f1ffed8e26022e32154760a)"
 have z_Hk: "?z_hk"
 by (rule zenon_and_0 [OF z_Hb])
 have z_Hp: "?z_hp" (is "?z_hq&?z_hw")
 by (rule zenon_and_1 [OF z_Hb])
 have z_Hq: "?z_hq"
 by (rule zenon_and_0 [OF z_Hp])
 have z_Hw: "?z_hw" (is "?z_hx&?z_hbb")
 by (rule zenon_and_1 [OF z_Hp])
 have z_Hx: "?z_hx"
 by (rule zenon_and_0 [OF z_Hw])
 have z_Hbb: "?z_hbb" (is "?z_hbc&?z_hbg")
 by (rule zenon_and_1 [OF z_Hw])
 have z_Hbc: "?z_hbc"
 by (rule zenon_and_0 [OF z_Hbb])
 have z_Hbg: "?z_hbg" (is "?z_hbh&?z_hbn")
 by (rule zenon_and_1 [OF z_Hbb])
 have z_Hbh: "?z_hbh"
 by (rule zenon_and_0 [OF z_Hbg])
 have z_Hbn: "?z_hbn"
 by (rule zenon_and_1 [OF z_Hbg])
 show FALSE
 proof (rule zenon_imply [OF z_Hi])
  assume z_Hcu:"(~?z_hb)"
  show FALSE
  proof (rule zenon_notand [OF z_Hcu])
   assume z_Hcv:"(~?z_hk)"
   show FALSE
   by (rule notE [OF z_Hcv z_Hk])
  next
   assume z_Hcw:"(~?z_hp)"
   show FALSE
   proof (rule zenon_notand [OF z_Hcw])
    assume z_Hcx:"(~?z_hq)"
    show FALSE
    by (rule notE [OF z_Hcx z_Hq])
   next
    assume z_Hcy:"(~?z_hw)"
    show FALSE
    proof (rule zenon_notand [OF z_Hcy])
     assume z_Hcz:"(~?z_hx)"
     show FALSE
     by (rule notE [OF z_Hcz z_Hx])
    next
     assume z_Hda:"(~?z_hbb)"
     show FALSE
     proof (rule zenon_notand [OF z_Hda])
      assume z_Hdb:"(~?z_hbc)"
      show FALSE
      by (rule notE [OF z_Hdb z_Hbc])
     next
      assume z_Hdc:"(~?z_hbg)"
      show FALSE
      proof (rule zenon_notand [OF z_Hdc])
       assume z_Hdd:"(~?z_hbh)"
       show FALSE
       by (rule notE [OF z_Hdd z_Hbh])
      next
       assume z_Hde:"(~?z_hbn)"
       show FALSE
       by (rule notE [OF z_Hde z_Hbn])
      qed
     qed
    qed
   qed
  qed
 next
  assume z_Hbt:"?z_hbt" (is "_=>?z_hbu")
  show FALSE
  proof (rule zenon_imply [OF z_Hbt])
   assume z_Hdf:"(~Next)"
   show FALSE
   by (rule notE [OF z_Hdf z_Hc])
  next
   assume z_Hbu:"?z_hbu" (is "_=>?z_hbv")
   show FALSE
   proof (rule zenon_imply [OF z_Hbu])
    assume z_Hdg:"(~LemmaBasic)"
    show FALSE
    by (rule notE [OF z_Hdg z_Ha])
   next
    assume z_Hbv:"?z_hbv"
    have z_Hdh_z_Hbv: "(\\A x:((x \\in Server)=>(\\A newEntry:((a_loghash_primea=except(log, x, Append((log[x]), newEntry)))=>((a_currentTermhash_primea=currentTerm)=>(bEx(Server, (\<lambda>t. (newEntry <= (currentTerm[t]))))=>a_h9780c447f1ffed8e26022e32154760a)))))) == ?z_hbv" (is "?z_hdh == _")
    by (unfold bAll_def)
    have z_Hdh: "?z_hdh" (is "\\A x : ?z_hdr(x)")
    by (unfold z_Hdh_z_Hbv, fact z_Hbv)
    have z_Hds: "?z_hdr(s)" (is "_=>?z_hdt")
    by (rule zenon_all_0 [of "?z_hdr" "s", OF z_Hdh])
    show FALSE
    proof (rule zenon_imply [OF z_Hds])
     assume z_Hdu:"(~?z_hd)"
     show FALSE
     by (rule notE [OF z_Hdu z_Hd])
    next
     assume z_Hdt:"?z_hdt" (is "\\A x : ?z_hdv(x)")
     have z_Hdw: "?z_hdv((currentTerm[s]))" (is "?z_hf=>?z_hdx")
     by (rule zenon_all_0 [of "?z_hdv" "(currentTerm[s])", OF z_Hdt])
     show FALSE
     proof (rule zenon_imply [OF z_Hdw])
      assume z_Hdy:"(a_loghash_primea~=?z_hcp)"
      show FALSE
      by (rule notE [OF z_Hdy z_Hf])
     next
      assume z_Hdx:"?z_hdx" (is "?z_hh=>?z_hdz")
      show FALSE
      proof (rule zenon_imply [OF z_Hdx])
       assume z_Hea:"(a_currentTermhash_primea~=currentTerm)"
       show FALSE
       by (rule notE [OF z_Hea z_Hh])
      next
       assume z_Hdz:"?z_hdz" (is "?z_heb=>_")
       show FALSE
       proof (rule zenon_imply [OF z_Hdz])
        assume z_Hec:"(~?z_heb)"
        have z_Hed_z_Hec: "(~(\\E x:((x \\in Server)&((currentTerm[s]) <= (currentTerm[x]))))) == (~?z_heb)" (is "?z_hed == ?z_hec")
        by (unfold bEx_def)
        have z_Hed: "?z_hed" (is "~(\\E x : ?z_hei(x))")
        by (unfold z_Hed_z_Hec, fact z_Hec)
        have z_Hej: "~?z_hei(s)"
        by (rule zenon_notex_0 [of "?z_hei" "s", OF z_Hed])
        show FALSE
        proof (rule zenon_notand [OF z_Hej])
         assume z_Hdu:"(~?z_hd)"
         show FALSE
         by (rule notE [OF z_Hdu z_Hd])
        next
         assume z_Hek:"(~?z_hg)"
         show FALSE
         by (rule notE [OF z_Hek z_Hg])
        qed
       next
        assume z_Hco:"a_h9780c447f1ffed8e26022e32154760a"
        show FALSE
        by (rule notE [OF z_Hj z_Hco])
       qed
      qed
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 532"; *} qed
end
