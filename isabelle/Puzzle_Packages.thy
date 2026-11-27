theory Puzzle_Packages
  imports Order
begin

text \<open>
  Registry 0.3.0-draft. Each published puzzle of puzzles.targets, proved from the
  registry's own constants (Principles.thy) for exactly the package the registry lists.
  The earlier checks (Russell_Checks, Fine_Checks) predate the formula layer and state
  their hypotheses directly; these theorems are about the entries the search uses.

  Fine 2010 and Kr\"amer 2013 state their grounding principles for partial ground, so
  the packages use the partial entries DISJ.PART, EX.PART, ALL.PART and TR.PART. Each
  full entry implies its partial one (Order.thy), so every package below is also
  refuted with DISJ.ONE, EX.FULL, ALL.INST or ALL.TOT, and TR.FULL in their place.
\<close>

lemma C1_adm: assumes "C1"
  shows "adm f_id" "adm f_tr" "adm f_em" "adm f_tem"
  using assms unfolding C1_def by blast+

lemma BETA_apps: assumes "BETA_ID"
  shows "app f_id p = p" "app f_tr p = tr p" "app f_em p = disj p (neg p)"
        "app f_tem p = disj (tr p) (neg (tr p))"
  using assms unfolding BETA_ID_def f_id_def f_tr_def f_em_def f_tem_def by simp_all

section \<open>Kr\"amer 2013\<close>

text \<open>P.KRAMER. The existential \<exists>p p is true and is its own instance. No classical
  clause for the connectives is used: the truth comes from CL.QUANT (Order.CL_QUANT_truth);
  Kr\"amer's premise is that \<exists>p p is a theorem of logic.\<close>
theorem kramer_package:
  assumes "C1" "BETA_ID" "CL_QUANT" "EX_PART" "IRR_F"
  shows False
proof -
  obtain q where "T q" using CL_QUANT_truth[OF assms(3)] by blast
  hence "T (app f_id q)" using BETA_apps(1)[OF assms(2)] by simp
  hence "T (exq f_id)" using assms(3) unfolding CL_QUANT_def by blast
  hence "T (app f_id (exq f_id))" using BETA_apps(1)[OF assms(2)] by simp
  hence "PG (app f_id (exq f_id)) (exq f_id)"
    using assms(4) C1_adm(1)[OF assms(1)] unfolding EX_PART_def by blast
  hence "PG (exq f_id) (exq f_id)" using BETA_apps(1)[OF assms(2)] by simp
  thus False using assms(5) unfolding IRR_F_def PG_def by blast
qed

corollary kramer_package_full:
  assumes "C1" "BETA_ID" "CL_QUANT" "EX_FULL" "IRR_F"
  shows False
  using kramer_package[OF assms(1,2,3) EX_FULL_PART[OF assms(4)] assms(5)] .

section \<open>Fine 2010\<close>

text \<open>P.FINE.UNIVERSAL: the Universal Argument for Propositions (pp. 102-103), steps
  (4), (6), (7), (8), from partial-ground premises.\<close>
theorem fine_universal_package:
  assumes c1: "C1" and beta: "BETA_ID" and cl: "CL_PROP" and clq: "CL_QUANT" and ts: "TS_FULL"
      and ug: "ALL_PART" and dg: "DISJ_PART" and pg: "TR_PART"
      and tra: "TRANS_P" and irr: "IRR_F"
  shows False
proof -
  let ?s = "allq f_tem"
  let ?d = "disj (tr ?s) (neg (tr ?s))"
  have app: "\<forall>p. app f_tem p = disj (tr p) (neg (tr p))" using BETA_apps(4)[OF beta] by simp
  have ad: "adm f_tem" using C1_adm(4)[OF c1] .
  have cd: "T (disj p q) \<longleftrightarrow> T p \<or> T q" for p q using cl unfolding CL_PROP_def by blast
  have cn: "T (neg p) \<longleftrightarrow> \<not> T p" for p using cl unfolding CL_PROP_def by blast
  have em: "T (disj x (neg x))" for x using cd cn by blast
  have vals: "\<forall>b. T (app f_tem b)" using app em by simp
  hence Ts: "T ?s" using clq unfolding CL_QUANT_def by blast
  have "PG (app f_tem ?s) ?s" using ug ad vals unfolding ALL_PART_def by blast
  hence d_s: "PG ?d ?s" using app by simp
  have "T (tr ?s)" using ts Ts unfolding TS_FULL_def by blast
  hence tr_d: "PG (tr ?s) ?d" using dg unfolding DISJ_PART_def by blast
  have s_tr: "PG ?s (tr ?s)" using pg Ts unfolding TR_PART_def by blast
  have "PG ?s ?s" using tra s_tr tr_d d_s unfolding TRANS_P_def by blast
  thus False using irr unfolding IRR_F_def PG_def by blast
qed

text \<open>The registry's two full universal entries both give the puzzle.\<close>
corollary fine_universal_ALL_INST:
  assumes "C1" "BETA_ID" "CL_PROP" "CL_QUANT" "TS_FULL" "ALL_INST" "DISJ_ONE" "TR_FULL"
          "TRANS_P" "IRR_F"
  shows False
  using fine_universal_package[OF assms(1-5) ALL_INST_PART[OF assms(6)]
        DISJ_ONE_PART[OF assms(7)] TR_FULL_PART[OF assms(8)] assms(9,10)] .

corollary fine_universal_ALL_TOT:
  assumes "C1" "BETA_ID" "CL_PROP" "CL_QUANT" "TS_FULL" "ALL_TOT" "DISJ_ONE" "TR_FULL"
          "TRANS_P" "IRR_F"
  shows False
  using fine_universal_package[OF assms(1-5) ALL_TOT_PART[OF assms(6)]
        DISJ_ONE_PART[OF assms(7)] TR_FULL_PART[OF assms(8)] assms(9,10)] .

text \<open>P.FINE.PARTICULAR.PROPS: the Particular Argument for Propositions. Fine gives
  no steps for it, only "similar versions" (p. 103); this proof is a reconstruction.\<close>
theorem fine_particular_props_package:
  assumes c1: "C1" and beta: "BETA_ID" and cl: "CL_PROP" and clq: "CL_QUANT" and ts: "TS_FULL"
      and eg: "EX_PART" and dg: "DISJ_PART" and pg: "TR_PART"
      and tra: "TRANS_P" and irr: "IRR_F"
  shows False
proof -
  let ?s = "exq f_tem"
  let ?d = "disj (tr ?s) (neg (tr ?s))"
  have app: "\<forall>p. app f_tem p = disj (tr p) (neg (tr p))" using BETA_apps(4)[OF beta] by simp
  have ad: "adm f_tem" using C1_adm(4)[OF c1] .
  have cd: "T (disj p q) \<longleftrightarrow> T p \<or> T q" for p q using cl unfolding CL_PROP_def by blast
  have cn: "T (neg p) \<longleftrightarrow> \<not> T p" for p using cl unfolding CL_PROP_def by blast
  have em: "T (disj x (neg x))" for x using cd cn by blast
  have Td: "T (app f_tem ?s)" using app em by simp
  hence Ts: "T ?s" using clq unfolding CL_QUANT_def by blast
  have "PG (app f_tem ?s) ?s" using eg ad Td unfolding EX_PART_def by blast
  hence d_s: "PG ?d ?s" using app by simp
  have "T (tr ?s)" using ts Ts unfolding TS_FULL_def by blast
  hence tr_d: "PG (tr ?s) ?d" using dg unfolding DISJ_PART_def by blast
  have s_tr: "PG ?s (tr ?s)" using pg Ts unfolding TR_PART_def by blast
  have "PG ?s ?s" using tra s_tr tr_d d_s unfolding TRANS_P_def by blast
  thus False using irr unfolding IRR_F_def PG_def by blast
qed

text \<open>P.FINE.PARTICULAR, "something is true" (Fine p. 106 with Transitivity and
  Irreflexivity; Kr\"amer's Finean counterpart and Lovett p. 2544 with Asymmetry). The
  common core is a two-membered circle of partial ground.\<close>
lemma something_true_circle:
  assumes c1: "C1" and beta: "BETA_ID" and clq: "CL_QUANT" and ts: "TS_FULL"
      and eg: "EX_PART" and pg: "TR_PART"
  shows "PG (tr (exq f_tr)) (exq f_tr) \<and> PG (exq f_tr) (tr (exq f_tr))"
proof -
  let ?s = "exq f_tr"
  have app: "\<forall>p. app f_tr p = tr p" using BETA_apps(2)[OF beta] by simp
  have ad: "adm f_tr" using C1_adm(2)[OF c1] .
  obtain q where "T q" using CL_QUANT_truth[OF clq] by blast
  hence "T (app f_tr q)" using app ts unfolding TS_FULL_def by simp
  hence Ts: "T ?s" using clq unfolding CL_QUANT_def by blast
  hence Ttr: "T (app f_tr ?s)" using app ts unfolding TS_FULL_def by simp
  have "PG (app f_tr ?s) ?s" using eg ad Ttr unfolding EX_PART_def by blast
  hence a: "PG (tr ?s) ?s" using app by simp
  have b: "PG ?s (tr ?s)" using pg Ts unfolding TR_PART_def by blast
  show ?thesis using a b by blast
qed

theorem something_true_trans_package:
  assumes "C1" "BETA_ID" "CL_QUANT" "TS_FULL" "EX_PART" "TR_PART" "TRANS_P" "IRR_F"
  shows False
proof -
  have "PG (exq f_tr) (exq f_tr)"
    using something_true_circle[OF assms(1-6)] assms(7) unfolding TRANS_P_def by blast
  thus False using assms(8) unfolding IRR_F_def PG_def by blast
qed

theorem something_true_asym_package:
  assumes "C1" "BETA_ID" "CL_QUANT" "TS_FULL" "EX_PART" "TR_PART" "ASYM_P"
  shows False
  using something_true_circle[OF assms(1-6)] assms(7) unfolding ASYM_P_def by blast

text \<open>P.FINE.UNIVERSAL.SP: the sentence-position variant with \<forall>p (p \<or> \<not>p) (instance
  from Woods p. 645). CL.PROP is needed: without it the instances of f_em are not
  known to be true. (The 0.2.1-draft target listed the package without CL.PROP.)\<close>
theorem fine_universal_sp_package:
  assumes c1: "C1" and beta: "BETA_ID" and cl: "CL_PROP" and clq: "CL_QUANT"
      and ug: "ALL_PART" and dg: "DISJ_PART" and tra: "TRANS_P" and irr: "IRR_F"
  shows False
proof -
  let ?s = "allq f_em"
  let ?d = "disj ?s (neg ?s)"
  have app: "\<forall>p. app f_em p = disj p (neg p)" using BETA_apps(3)[OF beta] by simp
  have ad: "adm f_em" using C1_adm(3)[OF c1] .
  have cd: "T (disj p q) \<longleftrightarrow> T p \<or> T q" for p q using cl unfolding CL_PROP_def by blast
  have cn: "T (neg p) \<longleftrightarrow> \<not> T p" for p using cl unfolding CL_PROP_def by blast
  have em: "T (disj x (neg x))" for x using cd cn by blast
  have vals: "\<forall>b. T (app f_em b)" using app em by simp
  hence Ts: "T ?s" using clq unfolding CL_QUANT_def by blast
  have "PG (app f_em ?s) ?s" using ug ad vals unfolding ALL_PART_def by blast
  hence d_s: "PG ?d ?s" using app by simp
  have s_d: "PG ?s ?d" using dg Ts unfolding DISJ_PART_def by blast
  have "PG ?s ?s" using tra s_d d_s unfolding TRANS_P_def by blast
  thus False using irr unfolding IRR_F_def PG_def by blast
qed

section \<open>Search rows formerly classed trivial-only that are refuted outright\<close>

text \<open>Both use the truth that CL.QUANT supplies (registry finding F6). The search had
  refuted these packages only together with N1.\<close>

theorem quant_disjweak_idac_irr:
  assumes "CL_QUANT" "DISJ_WEAK" "ID_AC" "IRR_F"
  shows False
proof -
  obtain t where t: "T t" using CL_QUANT_truth[OF assms(1)] by blast
  have "disj t t = t" using assms(3) unfolding ID_AC_def by blast
  hence "PG t t" using assms(2) t unfolding DISJ_WEAK_def by metis
  thus False using assms(4) unfolding IRR_F_def PG_def by blast
qed

theorem quant_negdn_trneg_tsid_irr:
  assumes "FACT" "CL_QUANT" "NEG_DN" "TR_NEG" "TS_ID" "IRR_F"
  shows False
proof -
  obtain t where t: "T t" using CL_QUANT_truth[OF assms(2)] by blast
  have "G {t} (neg (neg t))" using assms(3) t unfolding NEG_DN_def by blast
  hence "T (neg (neg t))" using assms(1) unfolding FACT_def by blast
  hence "G {neg (neg t)} (neg (tr (neg t)))" using assms(4) unfolding TR_NEG_def by blast
  moreover have "tr (neg t) = neg t" using assms(5) unfolding TS_ID_def by blast
  ultimately have "G {neg (neg t)} (neg (neg t))" by simp
  thus False using assms(6) unfolding IRR_F_def by blast
qed

end
