theory NonClassical
  imports Principles
begin

text \<open>
  Non-classical families, registry 0.3.0-draft (pending review). Three groups.

  Strong Kleene truth (Kripke 1975 as presented by fine2010 sect. 8, pp. 110-115):
  SK.PROP, SK.QUANT, TS.KF, SK.GAP. T stays the metalevel predicate "is true"; a
  proposition p is false when neg p is true, and a gap when neither is true. CL.PROP is
  SK.PROP plus bivalence (cl_sk below).

  Self-reference: SR.LIAR (a proposition identical to the negation of its own truth),
  SR.FINE15 (fine2010 fn. 15, p. 117: a disjunction one of whose disjuncts is the truth
  of the disjunction itself).

  Korbmacher's untyped response (korbmacher2015 slides 3, 11-12): DISJ.GRD (disjunction
  grounding restricted to grounded disjuncts), FOUND (every truth is fundamental or
  grounded; fundamental read as atomic), DIAG.K (his diagonal sentence as a witness
  hypothesis, as in Korbmacher_Checks.thy, now required to be non-atomic).

  Nothing here is an axiom.
\<close>

section \<open>Definitions\<close>

definition SK_PROP :: bool where
  "SK_PROP \<longleftrightarrow> (\<forall>p q. \<not> (T p \<and> T (neg p))
     \<and> (T (neg (neg p)) \<longleftrightarrow> T p)
     \<and> (T (conj p q) \<longleftrightarrow> T p \<and> T q) \<and> (T (neg (conj p q)) \<longleftrightarrow> T (neg p) \<or> T (neg q))
     \<and> (T (disj p q) \<longleftrightarrow> T p \<or> T q) \<and> (T (neg (disj p q)) \<longleftrightarrow> T (neg p) \<and> T (neg q)))"

definition SK_QUANT :: bool where
  "SK_QUANT \<longleftrightarrow> (\<forall>f. (T (exq f) \<longleftrightarrow> (\<exists>a. T (app f a))) \<and> (T (neg (exq f)) \<longleftrightarrow> (\<forall>a. T (neg (app f a))))
     \<and> (T (allq f) \<longleftrightarrow> (\<forall>a. T (app f a))) \<and> (T (neg (allq f)) \<longleftrightarrow> (\<exists>a. T (neg (app f a)))))"

definition TS_KF :: bool where
  "TS_KF \<longleftrightarrow> (\<forall>p. (T (tr p) \<longleftrightarrow> T p) \<and> (T (neg (tr p)) \<longleftrightarrow> T (neg p)))"

definition SK_GAP :: bool where
  "SK_GAP \<longleftrightarrow> (\<exists>p. \<not> T p \<and> \<not> T (neg p))"

definition SR_LIAR :: bool where
  "SR_LIAR \<longleftrightarrow> (\<exists>l. l = neg (tr l))"

definition SR_FINE15 :: bool where
  "SR_FINE15 \<longleftrightarrow> (\<exists>c t. T t \<and> c = disj t (tr c))"

definition DISJ_GRD :: bool where
  "DISJ_GRD \<longleftrightarrow> (\<forall>p q. ((\<exists>x. PG x p) \<longrightarrow> G {p} (disj p q)) \<and> ((\<exists>x. PG x q) \<longrightarrow> G {q} (disj p q)))"

definition FOUND :: bool where
  "FOUND \<longleftrightarrow> (\<forall>p. T p \<longrightarrow> p \<in> range atom \<or> (\<exists>x. PG x p))"

definition DIAG_K :: bool where
  "DIAG_K \<longleftrightarrow> (\<exists>d. d \<notin> range atom \<and> (T d \<longleftrightarrow> \<not> PG d (disj d d)))"

section \<open>Order: classical truth is strong Kleene truth plus bivalence\<close>

lemma cl_sk: "CL_PROP \<Longrightarrow> SK_PROP"
  unfolding CL_PROP_def SK_PROP_def by simp

lemma cl_sk_quant: "CL_PROP \<Longrightarrow> CL_QUANT \<Longrightarrow> SK_QUANT"
  unfolding CL_PROP_def CL_QUANT_def SK_QUANT_def by simp

lemma cl_ts_kf: "CL_PROP \<Longrightarrow> TS_FULL \<Longrightarrow> TS_KF"
  unfolding CL_PROP_def TS_FULL_def TS_KF_def by simp

lemma ts_kf_full: "TS_KF \<Longrightarrow> TS_FULL"
  unfolding TS_KF_def TS_FULL_def by simp

lemma sk_quant_cl: "SK_QUANT \<Longrightarrow> (\<forall>f. (T (exq f) \<longleftrightarrow> (\<exists>a. T (app f a))) \<and> (T (allq f) \<longleftrightarrow> (\<forall>a. T (app f a))))"
  unfolding SK_QUANT_def by simp

lemma cl_no_gap: "CL_PROP \<Longrightarrow> \<not> SK_GAP"
  unfolding CL_PROP_def SK_GAP_def by simp

lemma sk_bivalent_cl: "SK_PROP \<Longrightarrow> (\<forall>p. T p \<or> T (neg p)) \<Longrightarrow> CL_PROP"
  unfolding SK_PROP_def CL_PROP_def by metis

section \<open>The liar\<close>

theorem liar_classical: "SR_LIAR \<Longrightarrow> CL_PROP \<Longrightarrow> TS_FULL \<Longrightarrow> False"
  unfolding SR_LIAR_def CL_PROP_def TS_FULL_def by metis

text \<open>Under strong Kleene truth with Kripke's two-sided truth schema the liar is a gap,
  so SR.LIAR forces SK.GAP (fine2010 p. 114: Universal Middle "will fail ... when
  instanced with the Liar").\<close>

theorem liar_gap: "SR_LIAR \<Longrightarrow> SK_PROP \<Longrightarrow> TS_KF \<Longrightarrow> SK_GAP"
proof -
  assume l: SR_LIAR and sk: SK_PROP and kf: TS_KF
  obtain l where L: "l = neg (tr l)" using l unfolding SR_LIAR_def by blast
  have a: "T l \<longleftrightarrow> T (neg l)" using kf L unfolding TS_KF_def by metis
  have nl: "\<not> T l" using a sk unfolding SK_PROP_def by blast
  have "T (neg l) \<longleftrightarrow> T l"
  proof -
    have "T (neg l) \<longleftrightarrow> T (neg (neg (tr l)))" using L by metis
    also have "\<dots> \<longleftrightarrow> T (tr l)" using sk unfolding SK_PROP_def by blast
    also have "\<dots> \<longleftrightarrow> T l" using kf unfolding TS_KF_def by blast
    finally show ?thesis .
  qed
  thus SK_GAP using nl unfolding SK_GAP_def by blast
qed

section \<open>Fine's universal argument with the weak disjunction rule (fine2010 p. 109)\<close>

text \<open>Fine: "we cannot save ourselves from the Universal Argument for Propositions in
  this even way ... only one of the disjuncts is the case" (p. 109). Checked: the
  classical package with DISJ.WEAK in place of DISJ.ONE is still refuted.\<close>

theorem fine_universal_weak:
  assumes FACT C1 BETA_ID CL_PROP CL_QUANT TS_FULL ALL_INST DISJ_WEAK TR_FULL TRANS_P IRR_F
  shows False
proof -
  have fid: "app f_tem p = disj (tr p) (neg (tr p))" for p
    using assms(3) unfolding BETA_ID_def f_tem_def by simp
  have ad: "adm f_tem" using assms(2) unfolding C1_def by blast
  have cl: "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p" "\<forall>p q. T (disj p q) \<longleftrightarrow> T p \<or> T q"
    using assms(4) unfolding CL_PROP_def by blast+
  have ts: "\<forall>p. T (tr p) \<longleftrightarrow> T p" using assms(6) unfolding TS_FULL_def .
  let ?s = "allq f_tem" and ?d = "disj (tr (allq f_tem)) (neg (tr (allq f_tem)))"
  have vals: "\<forall>a. T (app f_tem a)" using fid cl by simp
  hence Ts: "T ?s" using assms(5) unfolding CL_QUANT_def by blast
  have "G (inst f_tem) ?s" using assms(7) ad vals unfolding ALL_INST_def by blast
  moreover have "?d \<in> inst f_tem" unfolding inst_def by (metis fid rangeI)
  ultimately have d_s: "PG ?d ?s" unfolding PG_def by blast
  have Ttr: "T (tr ?s)" using ts Ts by blast
  have Td: "T ?d" using cl Ttr by blast
  have "PG (tr ?s) ?d \<or> PG (neg (tr ?s)) ?d" using assms(8) Td unfolding DISJ_WEAK_def by blast
  moreover have "\<not> PG (neg (tr ?s)) ?d"
    using assms(1) cl Ttr unfolding FACT_def PG_def by blast
  ultimately have tr_d: "PG (tr ?s) ?d" by blast
  have s_tr: "PG ?s (tr ?s)" using assms(9) Ts unfolding TR_FULL_def PG_def by blast
  have "PG ?s ?s" using assms(10) s_tr tr_d d_s unfolding TRANS_P_def by blast
  thus False using assms(11) unfolding IRR_F_def PG_def by blast
qed

section \<open>A universal argument that needs only positive truth clauses\<close>

text \<open>With definable comprehension and beta identity, the function \<lambda>p. p \<or> t, for a
  truth t, is admissible. Its universal s is true on every truth-value logic whose
  disjunction is true when a disjunct is and whose universal is true when every instance
  is; no excluded middle, negation or truth predicate is used. s is a true disjunct of its
  own instance s \<or> t. So strong Kleene truth does not by itself block Fine's universal
  argument once comprehension supplies a parameter: DISJ.ONE and ALL.INST collide under
  transitivity and irreflexivity at non-triviality N1. INFERENCE (not checked against the
  literature in this form): a variant of the universal arguments in fine2010 pp. 102-107.\<close>

theorem positive_universal:
  assumes FACT C3d BETA_ID SK_PROP SK_QUANT ALL_INST DISJ_ONE TRANS_P IRR_F N1
  shows False
proof -
  obtain \<Gamma> p0 where "G \<Gamma> p0" using assms(10) unfolding N1_def by blast
  hence t: "T p0" using assms(1) unfolding FACT_def by blast
  define v where "v = (\<lambda>n::nat. p0)"
  define f where "f = lam 0 (Disj (Var 0) (Var 1)) v"
  have ad: "adm f" using assms(2) unfolding C3d_def f_def by blast
  have fapp: "app f a = disj a p0" for a
    using assms(3) unfolding BETA_ID_def f_def v_def by simp
  have dj: "\<forall>p q. T (disj p q) \<longleftrightarrow> T p \<or> T q" using assms(4) unfolding SK_PROP_def by blast
  have vals: "\<forall>a. T (app f a)" using fapp dj t by simp
  let ?s = "allq f"
  have Ts: "T ?s" using assms(5) vals unfolding SK_QUANT_def by blast
  have "G (inst f) ?s" using assms(6) ad vals unfolding ALL_INST_def by blast
  moreover have "disj ?s p0 \<in> inst f" unfolding inst_def by (metis fapp rangeI)
  ultimately have i_s: "PG (disj ?s p0) ?s" unfolding PG_def by blast
  have "G {?s} (disj ?s p0)" using assms(7) Ts unfolding DISJ_ONE_def by blast
  hence s_i: "PG ?s (disj ?s p0)" unfolding PG_def by blast
  have "PG ?s ?s" using assms(8) s_i i_s unfolding TRANS_P_def by blast
  thus False using assms(9) unfolding IRR_F_def PG_def by blast
qed

section \<open>Fine's footnote 15\<close>

text \<open>fine2010 fn. 15 (p. 117): for c denoting "(\<forall>x(x = x) \<or> T(c))", "\<forall>x(x = x) will
  ground (\<forall>x(x = x) \<or> T(c)) but T(c) will not, even though it is true." Checked: if
  some such c exists (SR.FINE15, with any truth t for \<forall>x(x = x)), DISJ.ONE is refuted by
  TR.FULL, the truth schema, transitivity and irreflexivity; no bivalence is used.\<close>

theorem fine_fn15:
  assumes SR_FINE15 SK_PROP TS_FULL DISJ_ONE TR_FULL TRANS_P IRR_F
  shows False
proof -
  obtain c t where ct: "T t" "c = disj t (tr c)" using assms(1) unfolding SR_FINE15_def by blast
  have Tc: "T c" using ct assms(2) unfolding SK_PROP_def by metis
  have Ttc: "T (tr c)" using Tc assms(3) unfolding TS_FULL_def by blast
  have "G {tr c} (disj t (tr c))" using assms(4) Ttc unfolding DISJ_ONE_def by blast
  hence a: "PG (tr c) c" using ct(2) unfolding PG_def by auto
  have b: "PG c (tr c)" using assms(5) Tc unfolding TR_FULL_def PG_def by blast
  have "PG c c" using assms(6) a b unfolding TRANS_P_def by blast
  thus False using assms(7) unfolding IRR_F_def PG_def by blast
qed

section \<open>Korbmacher's untyped response and foundation\<close>

text \<open>korbmacher2015 slide 12: with disjunction grounding restricted to grounded
  disjuncts, the diagonal sentence d is ungrounded (checked in Korbmacher_Checks.thy).
  Slide 3 writes, as an example of what the predicate approach can express,
  "\<forall>x(Tr(x) \<leftrightarrow> Fund(x) \<or> \<exists>y (y \<lhd> x))". Taking its left-to-right half as a principle
  (FOUND, with the fundamental truths read as the atomic ones) and d non-atomic, the
  untyped package is inconsistent again: d cannot be true (it would be fundamental or
  grounded) and cannot be untrue (it would then partially ground d \<or> d, hence be true by
  factivity). Korbmacher does not assert FOUND on the slides; the 2018 papers were not
  available to check whether he discusses this.\<close>

theorem korbmacher_found:
  assumes FACT DISJ_GRD FOUND DIAG_K
  shows False
proof -
  obtain d where d: "d \<notin> range atom" "T d \<longleftrightarrow> \<not> PG d (disj d d)"
    using assms(4) unfolding DIAG_K_def by blast
  have fact: "\<And>x y. PG x y \<Longrightarrow> T x" using assms(1) unfolding FACT_def PG_def by blast
  have ung: "\<not> (\<exists>y. PG y d)"
  proof
    assume "\<exists>y. PG y d"
    hence "G {d} (disj d d)" using assms(2) unfolding DISJ_GRD_def by blast
    hence pg: "PG d (disj d d)" unfolding PG_def by blast
    hence "T d" by (rule fact)
    with pg d(2) show False by blast
  qed
  have nT: "\<not> T d" using assms(3) d(1) ung unfolding FOUND_def by blast
  hence "PG d (disj d d)" using d(2) by blast
  hence "T d" by (rule fact)
  with nT show False by blast
qed

end
