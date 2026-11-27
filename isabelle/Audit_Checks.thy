theory Audit_Checks
  imports Order
begin

text \<open>
  Machine-checked evidence for the faithfulness audit of 2026-11-27
  (docs/audit-2026-11-27.md). Nothing here changes a registry entry or a status
  label. Each lemma records a property of the CURRENT encoding (registry
  v0.2.1-draft, Principles.thy) that the audit reports.
\<close>

section \<open>A1. The restricted entries collapse into the unrestricted ones\<close>

text \<open>
  EX.PRED, EX.LEV, TS.TYPED and TR.TYPED restrict a principle to propositions
  denoted by a formula a with lvl a = 0 (or tfree a) under SOME environment. The
  formula Var 0 has level 0 and is truth-free, and under the environment that maps 0
  to q it denotes q. So every proposition meets the restriction, and each
  restricted entry is equivalent to its unrestricted counterpart.
\<close>

lemma EX_PRED_FULL: "EX_PRED \<Longrightarrow> EX_FULL"
  unfolding EX_PRED_def EX_FULL_def
proof (intro allI impI)
  fix f q
  assume H: "\<forall>f a w. adm f \<and> lvl a = 0 \<and> T (app f (den w a)) \<longrightarrow> G {app f (den w a)} (exq f)"
     and A: "adm f \<and> T (app f q)"
  have "adm f \<and> lvl (Var 0) = 0 \<and> T (app f (den (\<lambda>_. q) (Var 0)))" using A by simp
  hence "G {app f (den (\<lambda>_. q) (Var 0))} (exq f)" using H by blast
  thus "G {app f q} (exq f)" by simp
qed

theorem EX_PRED_iff_FULL: "EX_PRED \<longleftrightarrow> EX_FULL"
  using EX_PRED_FULL EX_FULL_PRED by blast

lemma TS_TYPED_FULL: "TS_TYPED \<Longrightarrow> TS_FULL"
  unfolding TS_TYPED_def TS_FULL_def
proof
  fix p
  assume H: "\<forall>a v. tfree a \<longrightarrow> (T (tr (den v a)) \<longleftrightarrow> T (den v a))"
  have "tfree (Var 0)" by simp
  hence "T (tr (den (\<lambda>_. p) (Var 0))) \<longleftrightarrow> T (den (\<lambda>_. p) (Var 0))" using H by blast
  thus "T (tr p) \<longleftrightarrow> T p" by simp
qed

theorem TS_TYPED_iff_FULL: "TS_TYPED \<longleftrightarrow> TS_FULL"
  using TS_TYPED_FULL TS_FULL_TYPED by blast

lemma TR_TYPED_FULL: "TR_TYPED \<Longrightarrow> TR_FULL"
  unfolding TR_TYPED_def TR_FULL_def
proof (intro allI impI)
  fix p
  assume H: "\<forall>a v. tfree a \<and> T (den v a) \<longrightarrow> G {den v a} (tr (den v a))" and t: "T p"
  have "tfree (Var 0) \<and> T (den (\<lambda>_. p) (Var 0))" using t by simp
  hence "G {den (\<lambda>_. p) (Var 0)} (tr (den (\<lambda>_. p) (Var 0)))" using H by blast
  thus "G {p} (tr p)" by simp
qed

theorem TR_TYPED_iff_FULL: "TR_TYPED \<longleftrightarrow> TR_FULL"
  using TR_TYPED_FULL TR_FULL_TYPED by blast

text \<open>EX.LEV: the bound lvl a < lvl (Ex x b) is met by a = Var 0 for every b, so
  EX.LEV is EX.FULL for every admissible function that is a lambda term (all of them
  under C1, C2 and C3d).\<close>
lemma EX_LEV_FULL:
  assumes lev: "EX_LEV" and lamb: "\<forall>f. adm f \<longrightarrow> (\<exists>x b v. f = lam x b v)"
  shows "EX_FULL"
  unfolding EX_FULL_def
proof (intro allI impI)
  fix f q assume A: "adm f \<and> T (app f q)"
  then obtain x b v where f: "f = lam x b v" using lamb by blast
  have "adm (lam x b v) \<and> lvl (Var 0) < lvl (Ex x b) \<and> T (app (lam x b v) (den (\<lambda>_. q) (Var 0)))"
    using A f by simp
  hence "G {app (lam x b v) (den (\<lambda>_. q) (Var 0))} (exq (lam x b v))"
    using lev unfolding EX_LEV_def by blast
  thus "G {app f q} (exq f)" using f by simp
qed

section \<open>A2. CL.QUANT alone yields a truth; Kr\"amer's package needs no CL.PROP\<close>

text \<open>The third clause of CL.QUANT makes the conjunction of an empty satisfier set
  true, so CL.QUANT is inconsistent with "nothing is true".\<close>
lemma CL_QUANT_truth: assumes "CL_QUANT" shows "\<exists>p. T p"
proof (rule ccontr)
  assume n: "\<not> (\<exists>p. T p)"
  have "T (bigconj f) \<longleftrightarrow> (\<forall>q\<in>sat f. T q)" for f using assms unfolding CL_QUANT_def by blast
  moreover have "sat f = {}" for f unfolding sat_def using n by blast
  ultimately have "T (bigconj f)" for f by simp
  thus False using n by blast
qed

text \<open>The registry target P.KRAMER, exactly as listed (no CL.PROP), is refuted
  outright. The search recorded this package as "trivial-only".\<close>
theorem kramer_target_as_listed:
  assumes "C1" "BETA_ID" "CL_QUANT" "EX_FULL" "IRR_F"
  shows False
proof -
  have id: "\<forall>p. app f_id p = p" using assms(2) beta_id_f_id by blast
  have ad: "adm f_id" using assms(1) unfolding C1_def by blast
  obtain q where "T q" using CL_QUANT_truth[OF assms(3)] by blast
  hence "T (app f_id q)" using id by simp
  hence "T (exq f_id)" using assms(3) unfolding CL_QUANT_def by blast
  hence "T (app f_id (exq f_id))" using id by simp
  hence "G {app f_id (exq f_id)} (exq f_id)" using assms(4) ad unfolding EX_FULL_def by blast
  hence "G {exq f_id} (exq f_id)" using id by simp
  thus False using assms(5) unfolding IRR_F_def by blast
qed

text \<open>Consequence of A1: Kr\"amer's own escape route, restricting existential
  grounding to quantifier-free instances, does not escape in this encoding.\<close>
theorem kramer_not_blocked_by_EX_PRED:
  assumes "C1" "BETA_ID" "CL_QUANT" "EX_PRED" "IRR_F"
  shows False
  using kramer_target_as_listed[OF assms(1,2,3) EX_PRED_FULL[OF assms(4)] assms(5)] .

section \<open>A3. Fine's universal argument needs only partial ground of instances\<close>

text \<open>
  Fine 2010 p. 100 states Universal Grounding for partial ground: each instance
  helps ground the universal truth. ALL.INST (all instances are a full ground) and
  ALL.TOT (instances plus a totality fact) both imply it, so the registry's two
  "alternatives" share this weaker core, which has no entry of its own.
\<close>
definition ALL_PART :: bool where
  "ALL_PART \<longleftrightarrow> (\<forall>f a. adm f \<and> (\<forall>b. T (app f b)) \<longrightarrow> PG (app f a) (allq f))"

lemma ALL_INST_PART: "ALL_INST \<Longrightarrow> ALL_PART"
  unfolding ALL_INST_def ALL_PART_def PG_def inst_def by blast

lemma ALL_TOT_PART: "ALL_TOT \<Longrightarrow> ALL_PART"
  unfolding ALL_TOT_def ALL_PART_def PG_def inst_def
proof (intro allI impI)
  fix f a
  assume H: "\<forall>f. adm f \<and> (\<forall>a. T (app f a)) \<longrightarrow> T (tot f) \<and> G (insert (tot f) (range (app f))) (allq f)"
     and A: "adm f \<and> (\<forall>b. T (app f b))"
  have g: "G (insert (tot f) (range (app f))) (allq f)" using H A by blast
  have m: "app f a \<in> insert (tot f) (range (app f))" by simp
  show "\<exists>\<Gamma>. app f a \<in> \<Gamma> \<and> G \<Gamma> (allq f)" using conjI[OF m g] by (rule exI)
qed

text \<open>Fine's Universal Argument for Propositions (2010, pp. 102-103) in the v0.2
  encoding, from partial-ground premises only: each instance helps ground the
  universal (step 4), a true disjunct helps ground the disjunction (step 6), a truth
  helps ground its truth ascription (step 7).\<close>
theorem fine_universal_partial:
  assumes c1: "C1" and beta: "BETA_ID" and cl: "CL_PROP" and clq: "CL_QUANT" and ts: "TS_FULL"
      and ug: "ALL_PART"
      and dg: "\<forall>p q. T p \<longrightarrow> PG p (disj p q)"
      and pg: "\<forall>p. T p \<longrightarrow> PG p (tr p)"
      and tra: "TRANS_P" and irr: "IRR_F"
  shows False
proof -
  let ?s = "allq f_tem"
  let ?d = "disj (tr ?s) (neg (tr ?s))"
  have app: "\<forall>p. app f_tem p = disj (tr p) (neg (tr p))"
    using beta unfolding BETA_ID_def f_tem_def by simp
  have ad: "adm f_tem" using c1 unfolding C1_def by blast
  have cd: "T (disj p q) \<longleftrightarrow> T p \<or> T q" for p q using cl unfolding CL_PROP_def by blast
  have cn: "T (neg p) \<longleftrightarrow> \<not> T p" for p using cl unfolding CL_PROP_def by blast
  have em: "T (disj x (neg x))" for x using cd cn by blast
  have vals: "\<forall>b. T (app f_tem b)" using app em by simp
  hence Ts: "T ?s" using clq unfolding CL_QUANT_def by blast
  have "PG (app f_tem ?s) ?s" using ug ad vals unfolding ALL_PART_def by blast
  hence d_s: "PG ?d ?s" using app by simp
  have "T (tr ?s)" using ts Ts unfolding TS_FULL_def by blast
  hence tr_d: "PG (tr ?s) ?d" using dg by blast
  have s_tr: "PG ?s (tr ?s)" using pg Ts by blast
  have "PG ?s ?s" using tra s_tr tr_d d_s unfolding TRANS_P_def by blast
  thus False using irr unfolding IRR_F_def PG_def by blast
qed

text \<open>So the universal puzzle is not escaped by adding a totality fact.\<close>
theorem fine_universal_with_ALL_TOT:
  assumes "C1" "BETA_ID" "CL_PROP" "CL_QUANT" "TS_FULL" "ALL_TOT" "DISJ_ONE" "TR_FULL"
          "TRANS_P" "IRR_F"
  shows False
proof -
  have dg: "\<forall>p q. T p \<longrightarrow> PG p (disj p q)"
    using assms(7) unfolding DISJ_ONE_def PG_def by blast
  have pg: "\<forall>p. T p \<longrightarrow> PG p (tr p)"
    using assms(8) unfolding TR_FULL_def PG_def by blast
  show False
    using fine_universal_partial[OF assms(1-5) ALL_TOT_PART[OF assms(6)] dg pg assms(9,10)] .
qed

section \<open>A4. Amalgamation turns DISJ.ONE into DISJ.BOTH\<close>

text \<open>The registry records this as an inference (AMALG.FIN, readings). Fine argues
  the same way for the collective rule (Guide, p. 58).\<close>
lemma AMALG_DISJ_ONE_BOTH: assumes am: "AMALG_FIN" and d: "DISJ_ONE" shows "DISJ_BOTH"
  unfolding DISJ_BOTH_def
proof (intro allI impI)
  fix p q assume t: "T p \<and> T q"
  have a: "G {p} (disj p q)" and b: "G {q} (disj p q)" using d t unfolding DISJ_ONE_def by blast+
  have "G ({p} \<union> {q}) (disj p q)" using am a b unfolding AMALG_FIN_def by blast
  moreover have "{p} \<union> {q} = {p, q}" by auto
  ultimately show "G {p, q} (disj p q)" by simp
qed

end
