theory Order
  imports Principles
begin

text \<open>
  Step 4: the strength order the search may use. The enumeration propagates a
  refutation upward and a model downward only along implications proved here; the
  registry's rank numbers are not used on their own. Conditional implications carry
  their side conditions explicitly.
\<close>

lemma IRR_F_W: "IRR_F \<Longrightarrow> IRR_W" unfolding IRR_F_def IRR_W_def by blast
lemma IRR_F_MEM: "IRR_F \<Longrightarrow> IRR_MEM" unfolding IRR_F_def IRR_MEM_def by blast

lemma ASYM_P_ANTI: "ASYM_P \<Longrightarrow> ASYM_ANTI" unfolding ASYM_P_def ASYM_ANTI_def by blast
lemma ASYM_P_IRR_F: "ASYM_P \<Longrightarrow> IRR_F" unfolding ASYM_P_def IRR_F_def PG_def by blast

lemma TRANS_CUT_P: assumes cut: "TRANS_CUT" shows "TRANS_P"
  unfolding TRANS_P_def
proof (intro allI impI)
  fix p q r assume "PG p q \<and> PG q r"
  then obtain \<Gamma> \<Delta> where a: "p \<in> \<Gamma>" "G \<Gamma> q" and b: "q \<in> \<Delta>" "G \<Delta> r"
    unfolding PG_def by blast
  have inst: "G \<Delta> r \<and> {q} \<subseteq> \<Delta> \<and> (\<forall>x\<in>{q}. G \<Gamma> x) \<longrightarrow> G ((\<Delta> - {q}) \<union> (\<Union>x\<in>{q}. \<Gamma>)) r"
    using cut[unfolded TRANS_CUT_def, THEN spec[where x=\<Delta>], THEN spec[where x="{q}"],
              THEN spec[where x="\<lambda>_. \<Gamma>"], THEN spec[where x=r]] .
  have "G \<Delta> r \<and> {q} \<subseteq> \<Delta> \<and> (\<forall>x\<in>{q}. G \<Gamma> x)" using a b by blast
  with inst have g: "G ((\<Delta> - {q}) \<union> (\<Union>x\<in>{q}. \<Gamma>)) r" by (rule mp)
  have m: "p \<in> (\<Delta> - {q}) \<union> (\<Union>x\<in>{q}. \<Gamma>)" using a(1) by simp
  show "PG p r" unfolding PG_def using conjI[OF m g] by (rule exI)
qed

lemma AMALG_INF_FIN: "AMALG_INF \<Longrightarrow> AMALG_FIN"
  unfolding AMALG_INF_def AMALG_FIN_def
proof (intro allI impI)
  fix \<Gamma> \<Delta> p
  assume inf: "\<forall>F p. F \<noteq> {} \<and> (\<forall>\<Gamma>\<in>F. G \<Gamma> p) \<longrightarrow> G (\<Union>F) p" and g: "G \<Gamma> p \<and> G \<Delta> p"
  have "G (\<Union>{\<Gamma>, \<Delta>}) p" using inf[rule_format, of "{\<Gamma>, \<Delta>}" p] g by blast
  thus "G (\<Gamma> \<union> \<Delta>) p" by simp
qed

lemma TS_ID_FULL: "TS_ID \<Longrightarrow> TS_FULL" unfolding TS_ID_def TS_FULL_def by simp
lemma TS_FULL_TYPED: "TS_FULL \<Longrightarrow> TS_TYPED" unfolding TS_FULL_def TS_TYPED_def by blast
lemma TR_FULL_TYPED: "TR_FULL \<Longrightarrow> TR_TYPED" unfolding TR_FULL_def TR_TYPED_def by blast

lemma EX_FULL_LEV: "EX_FULL \<Longrightarrow> EX_LEV" unfolding EX_FULL_def EX_LEV_def by blast
lemma EX_FULL_PRED: "EX_FULL \<Longrightarrow> EX_PRED" unfolding EX_FULL_def EX_PRED_def by blast

text \<open>EX.LEV implies EX.PRED when every admissible function is a lambda term,
  which holds under C1, C2 k and C3d but not C3s.\<close>
lemma EX_LEV_PRED:
  assumes "EX_LEV" and lamb: "\<forall>f. adm f \<longrightarrow> (\<exists>x b v. f = lam x b v)"
  shows "EX_PRED"
  unfolding EX_PRED_def
proof (intro allI impI, elim conjE)
  fix f a w assume ad: "adm f" and l0: "lvl a = 0" and t: "T (app f (den w a))"
  obtain x b v where f: "f = lam x b v" using lamb ad by blast
  have "lvl a < lvl (Ex x b)" using l0 by simp
  thus "G {app f (den w a)} (exq f)" using assms(1) ad t f unfolding EX_LEV_def by blast
qed

lemma C1_lamb: assumes "C1" shows "\<forall>f. adm f \<longrightarrow> (\<exists>x b v. f = lam x b v)"
proof (intro allI impI)
  fix f assume "adm f"
  then have "f \<in> {f_id, f_tr, f_em, f_tem}" using assms unfolding C1_def by blast
  then show "\<exists>x b v. f = lam x b v" unfolding f_id_def f_tr_def f_em_def f_tem_def by auto
qed
lemma C2_lamb: "C2 k \<Longrightarrow> \<forall>f. adm f \<longrightarrow> (\<exists>x b v. f = lam x b v)"
  unfolding C2_def by blast
lemma C3d_lamb: "C3d \<Longrightarrow> \<forall>f. adm f \<longrightarrow> (\<exists>x b v. f = lam x b v)"
  unfolding C3d_def by blast

lemma FIN_B3_FIN: "FIN_B3 \<Longrightarrow> FIN_FIN" unfolding FIN_B3_def FIN_FIN_def by blast

lemma DISJ_ONE_WEAK: assumes cl: "CL_PROP" and d: "DISJ_ONE" shows "DISJ_WEAK"
  unfolding DISJ_WEAK_def
proof (intro allI impI)
  fix p q assume "T (disj p q)"
  then have "T p \<or> T q" using cl unfolding CL_PROP_def by blast
  then show "PG p (disj p q) \<or> PG q (disj p q)"
  proof
    assume "T p" then have "G {p} (disj p q)" using d unfolding DISJ_ONE_def by blast
    then show ?thesis unfolding PG_def by blast
  next
    assume "T q" then have "G {q} (disj p q)" using d unfolding DISJ_ONE_def by blast
    then show ?thesis unfolding PG_def by blast
  qed
qed

lemma EX_FULL_WEAK: assumes cl: "CL_QUANT" and e: "EX_FULL" shows "EX_WEAK"
  unfolding EX_WEAK_def
proof (intro allI impI, elim conjE)
  fix f assume ad: "adm f" and "T (exq f)"
  then obtain a where t: "T (app f a)" using cl unfolding CL_QUANT_def by blast
  then have "G {app f a} (exq f)" using e ad unfolding EX_FULL_def by blast
  then show "\<exists>a. PG (app f a) (exq f)" unfolding PG_def by blast
qed

lemma EMPTY_excl: "EMPTY_NONE \<longleftrightarrow> \<not> EMPTY_SOME" unfolding EMPTY_NONE_def EMPTY_SOME_def by blast

end
