theory Fritz2020_Checks
  imports Principles
begin

text \<open>
  Fritz, "On higher-order logical grounds" (Analysis, doi:10.1093/analys/anz085;
  final draft pp. 3-5). Read with the formula layer: Fritz's non-schematic
  principle (EQ), "for all X and p, Xp grounds EX if true", is EX_FULL quantifying
  over pfun; his truth property (lambda p. p) is f_id; beta-conversion (betaC) is
  BETA_ID and beta-grounding (betaG) is BETA_GROUND (D3). He argues that (EQ) yields
  T(ET) grounds ET, which is harmless unless T(ET) = ET, and that both betaC and
  betaG reinstate the problem: betaC against irreflexivity, betaG against asymmetry
  (and, with transitivity, against irreflexivity). The betaC case is kramer_v2 in
  Signature.thy. The betaG cases are checked here. "Something is true" is assumed
  directly (Fritz: "there is surely some truth").
\<close>

theorem fritz2020_betaG_asym:
  assumes c1: "C1" and lc: "LAM_CORE" and bg: "BETA_GROUND"
      and ex: "EX_FULL" and clq: "CL_QUANT" and asym: "ASYM_P"
      and some: "\<exists>p. T p"
  shows False
proof -
  let ?E = "exq f_id" and ?TE = "app f_id (exq f_id)"
  have ad: "adm f_id" using c1 unfolding C1_def by blast
  have den: "\<And>p. den (e0(0:=p)) (Var 0) = p" by simp
  have Tapp: "\<And>p. T (app f_id p) \<longleftrightarrow> T p"
    using lc unfolding LAM_CORE_def f_id_def by (metis den)
  obtain q where "T q" using some by blast
  hence TE: "T ?E" using clq Tapp unfolding CL_QUANT_def by blast
  have td: "T (den (e0(0:=?E)) (Var 0))" using TE by simp
  have "app (lam 0 (Var 0) e0) ?E \<noteq> den (e0(0:=?E)) (Var 0)
        \<and> G {den (e0(0:=?E)) (Var 0)} (app (lam 0 (Var 0) e0) ?E)"
    by (rule bg[unfolded BETA_GROUND_def, rule_format, OF td])
  hence g1': "G {?E} ?TE" unfolding f_id_def by simp
  have "T ?TE" using Tapp TE by blast
  hence g2: "G {?TE} ?E" using ex ad unfolding EX_FULL_def by blast
  have "PG ?E ?TE" "PG ?TE ?E" using g1' g2 unfolding PG_def by blast+
  thus False using asym unfolding ASYM_P_def by blast
qed

theorem fritz2020_betaG_trans_irr:
  assumes c1: "C1" and lc: "LAM_CORE" and bg: "BETA_GROUND"
      and ex: "EX_FULL" and clq: "CL_QUANT" and tr: "TRANS_P" and irr: "IRR_F"
      and some: "\<exists>p. T p"
  shows False
proof -
  let ?E = "exq f_id" and ?TE = "app f_id (exq f_id)"
  have ad: "adm f_id" using c1 unfolding C1_def by blast
  have den: "\<And>p. den (e0(0:=p)) (Var 0) = p" by simp
  have Tapp: "\<And>p. T (app f_id p) \<longleftrightarrow> T p"
    using lc unfolding LAM_CORE_def f_id_def by (metis den)
  obtain q where "T q" using some by blast
  hence TE: "T ?E" using clq Tapp unfolding CL_QUANT_def by blast
  have td: "T (den (e0(0:=?E)) (Var 0))" using TE by simp
  have "app (lam 0 (Var 0) e0) ?E \<noteq> den (e0(0:=?E)) (Var 0)
        \<and> G {den (e0(0:=?E)) (Var 0)} (app (lam 0 (Var 0) e0) ?E)"
    by (rule bg[unfolded BETA_GROUND_def, rule_format, OF td])
  hence g1: "G {?E} ?TE" unfolding f_id_def by simp
  have "T ?TE" using Tapp TE by blast
  hence g2: "G {?TE} ?E" using ex ad unfolding EX_FULL_def by blast
  have "PG ?E ?TE" "PG ?TE ?E" using g1 g2 unfolding PG_def by blast+
  hence "PG ?E ?E" using tr unfolding TRANS_P_def by blast
  thus False using irr unfolding IRR_F_def PG_def by blast
qed

text \<open>
  The premise "something is true" is not needed in this encoding: CL_QUANT includes
  the clause for arbitrary conjunction, T (bigconj f) iff every member of sat f is
  true, and if nothing were true then sat f would be empty, so bigconj f would be
  true. So the listed package is refuted outright. (The same lemma is
  Order.CL_QUANT_truth on the audit branch; it is restated here under its own name.)
\<close>

lemma fritz2020_CL_QUANT_truth: assumes "CL_QUANT" shows "\<exists>p. T p"
proof (rule ccontr)
  assume n: "\<not> (\<exists>p. T p)"
  have "T (bigconj f) \<longleftrightarrow> (\<forall>q\<in>sat f. T q)" for f using assms unfolding CL_QUANT_def by blast
  moreover have "sat f = {}" for f unfolding sat_def using n by blast
  ultimately have "T (bigconj f)" for f by simp
  thus False using n by blast
qed

corollary fritz2020_betaG_asym_package:
  assumes "C1" "LAM_CORE" "BETA_GROUND" "EX_FULL" "CL_QUANT" "ASYM_P"
  shows False
  using fritz2020_betaG_asym[OF assms fritz2020_CL_QUANT_truth[OF assms(5)]] .

corollary fritz2020_betaG_trans_irr_package:
  assumes "C1" "LAM_CORE" "BETA_GROUND" "EX_FULL" "CL_QUANT" "TRANS_P" "IRR_F"
  shows False
  using fritz2020_betaG_trans_irr[OF assms fritz2020_CL_QUANT_truth[OF assms(5)]] .

end
