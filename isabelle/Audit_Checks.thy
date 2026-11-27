theory Audit_Checks
  imports Puzzle_Packages
begin

text \<open>
  Machine-checked evidence for the faithfulness audit of 2026-11-27
  (docs/audit-2026-11-27.md), which examined registry v0.2.1-draft. The repairs the
  audit proposed were applied in registry v0.3.0-draft (decision D5). This theory keeps
  the evidence for the findings about the OLD encoding, restated for definitions that
  are copied here from v0.2.1-draft, and points to where each repair is checked.

    A1  collapse of the restricted entries: below, for the v0.2.1 definitions.
        Repair: closed formulas (Principles.thy). Non-collapse of the repaired entries:
        Restricted_Models.thy (MG_package).
    A3  CL.QUANT alone yields a truth: Order.thy (CL_QUANT_truth). Kr\"amer's package as
        listed is refuted outright: Puzzle_Packages.thy (kramer_package_full).
    A4  the partial universal entry: Principles.thy (ALL_PART), Order.thy
        (ALL_INST_PART, ALL_TOT_PART), Puzzle_Packages.thy (fine_universal_package,
        fine_universal_ALL_TOT).
\<close>

section \<open>A1. In v0.2.1-draft the restricted entries collapsed into the unrestricted ones\<close>

text \<open>
  The v0.2.1 definitions restricted a principle to propositions denoted by a formula a
  with lvl a = 0 (or tfree a) under SOME environment, with free variables allowed. The
  formula Var 0 has level 0 and is truth-free, and under the environment that maps 0
  to q it denotes q. So every proposition met the restriction.
\<close>

definition TS_TYPED_v021 :: bool where
  "TS_TYPED_v021 \<longleftrightarrow> (\<forall>a v. tfree a \<longrightarrow> (T (tr (den v a)) \<longleftrightarrow> T (den v a)))"
definition TR_TYPED_v021 :: bool where
  "TR_TYPED_v021 \<longleftrightarrow> (\<forall>a v. tfree a \<and> T (den v a) \<longrightarrow> G {den v a} (tr (den v a)))"
definition EX_PRED_v021 :: bool where
  "EX_PRED_v021 \<longleftrightarrow> (\<forall>f a w. adm f \<and> lvl a = 0 \<and> T (app f (den w a)) \<longrightarrow> G {app f (den w a)} (exq f))"
definition EX_LEV_v021 :: bool where
  "EX_LEV_v021 \<longleftrightarrow> (\<forall>x b v a w. adm (lam x b v) \<and> lvl a < lvl (Ex x b) \<and> T (app (lam x b v) (den w a))
     \<longrightarrow> G {app (lam x b v) (den w a)} (exq (lam x b v)))"

lemma EX_PRED_v021_FULL: "EX_PRED_v021 \<Longrightarrow> EX_FULL"
  unfolding EX_PRED_v021_def EX_FULL_def
proof (intro allI impI)
  fix f q
  assume H: "\<forall>f a w. adm f \<and> lvl a = 0 \<and> T (app f (den w a)) \<longrightarrow> G {app f (den w a)} (exq f)"
     and A: "adm f \<and> T (app f q)"
  have "adm f \<and> lvl (Var 0) = 0 \<and> T (app f (den (\<lambda>_. q) (Var 0)))" using A by simp
  hence "G {app f (den (\<lambda>_. q) (Var 0))} (exq f)" using H by blast
  thus "G {app f q} (exq f)" by simp
qed

theorem EX_PRED_v021_iff_FULL: "EX_PRED_v021 \<longleftrightarrow> EX_FULL"
  using EX_PRED_v021_FULL unfolding EX_PRED_v021_def EX_FULL_def by blast

lemma TS_TYPED_v021_FULL: "TS_TYPED_v021 \<Longrightarrow> TS_FULL"
  unfolding TS_TYPED_v021_def TS_FULL_def
proof
  fix p
  assume H: "\<forall>a v. tfree a \<longrightarrow> (T (tr (den v a)) \<longleftrightarrow> T (den v a))"
  have "tfree (Var 0)" by simp
  hence "T (tr (den (\<lambda>_. p) (Var 0))) \<longleftrightarrow> T (den (\<lambda>_. p) (Var 0))" using H by blast
  thus "T (tr p) \<longleftrightarrow> T p" by simp
qed

theorem TS_TYPED_v021_iff_FULL: "TS_TYPED_v021 \<longleftrightarrow> TS_FULL"
  using TS_TYPED_v021_FULL unfolding TS_TYPED_v021_def TS_FULL_def by blast

lemma TR_TYPED_v021_FULL: "TR_TYPED_v021 \<Longrightarrow> TR_FULL"
  unfolding TR_TYPED_v021_def TR_FULL_def
proof (intro allI impI)
  fix p
  assume H: "\<forall>a v. tfree a \<and> T (den v a) \<longrightarrow> G {den v a} (tr (den v a))" and t: "T p"
  have "tfree (Var 0) \<and> T (den (\<lambda>_. p) (Var 0))" using t by simp
  hence "G {den (\<lambda>_. p) (Var 0)} (tr (den (\<lambda>_. p) (Var 0)))" using H by blast
  thus "G {p} (tr p)" by simp
qed

theorem TR_TYPED_v021_iff_FULL: "TR_TYPED_v021 \<longleftrightarrow> TR_FULL"
  using TR_TYPED_v021_FULL unfolding TR_TYPED_v021_def TR_FULL_def by blast

text \<open>EX.LEV (v0.2.1): the bound lvl a < lvl (Ex x b) is met by a = Var 0 for every b,
  so it gave EX.FULL for every admissible function that is a lambda term (all of them
  under C1, C2 and C3d).\<close>
lemma EX_LEV_v021_FULL:
  assumes lev: "EX_LEV_v021" and lamb: "\<forall>f. adm f \<longrightarrow> (\<exists>x b v. f = lam x b v)"
  shows "EX_FULL"
  unfolding EX_FULL_def
proof (intro allI impI)
  fix f q assume A: "adm f \<and> T (app f q)"
  then obtain x b v where f: "f = lam x b v" using lamb by blast
  have "adm (lam x b v) \<and> lvl (Var 0) < lvl (Ex x b) \<and> T (app (lam x b v) (den (\<lambda>_. q) (Var 0)))"
    using A f by simp
  hence "G {app (lam x b v) (den (\<lambda>_. q) (Var 0))} (exq (lam x b v))"
    using lev unfolding EX_LEV_v021_def by blast
  thus "G {app f q} (exq f)" using f by simp
qed

text \<open>Consequence for v0.2.1: Kr\"amer's own escape route, restricting existential
  grounding to quantifier-free instances, did not escape. With the repaired EX.PRED the
  same package has a model (Restricted_Models.thy, MG_package).\<close>
theorem kramer_not_blocked_v021:
  assumes "C1" "BETA_ID" "CL_QUANT" "EX_PRED_v021" "IRR_F"
  shows False
  using kramer_package_full[OF assms(1,2,3) EX_PRED_v021_FULL[OF assms(4)] assms(5)] .

text \<open>The repaired entries are the old ones restricted to closed formulas, so each is
  implied by its v0.2.1 form.\<close>
lemma v021_implies_repaired:
  "TS_TYPED_v021 \<Longrightarrow> TS_TYPED" "TR_TYPED_v021 \<Longrightarrow> TR_TYPED"
  "EX_PRED_v021 \<Longrightarrow> EX_PRED" "EX_LEV_v021 \<Longrightarrow> EX_LEV"
  unfolding TS_TYPED_v021_def TS_TYPED_def TR_TYPED_v021_def TR_TYPED_def
            EX_PRED_v021_def EX_PRED_def EX_LEV_v021_def EX_LEV_def by blast+

section \<open>Amalgamation turns DISJ.ONE into DISJ.BOTH\<close>

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
