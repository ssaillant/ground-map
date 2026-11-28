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
  fix f a w assume ad: "adm f" and l0: "lvl a = 0" and cl: "fv a = {}"
    and t: "T (app f (den w a))"
  obtain x b v where f: "f = lam x b v" using lamb ad by blast
  have "lvl a < lvl (Ex x b)" using l0 by simp
  thus "G {app f (den w a)} (exq f)" using assms(1) ad t f cl unfolding EX_LEV_def by blast
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

text \<open>Partial-ground entries (Fine 2010, pp. 100-101): each is implied by the full-ground
  entry of its family, and the two universal entries share the partial one.\<close>
lemma DISJ_ONE_PART: "DISJ_ONE \<Longrightarrow> DISJ_PART"
  unfolding DISJ_ONE_def DISJ_PART_def PG_def by blast
lemma EX_FULL_PART: "EX_FULL \<Longrightarrow> EX_PART"
  unfolding EX_FULL_def EX_PART_def PG_def by blast
lemma TR_FULL_PART: "TR_FULL \<Longrightarrow> TR_PART"
  unfolding TR_FULL_def TR_PART_def PG_def by blast
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

text \<open>Conditional: the partial entries give Fine's weak ones under classical truth.\<close>
lemma DISJ_PART_WEAK: assumes cl: "CL_PROP" and d: "DISJ_PART" shows "DISJ_WEAK"
  unfolding DISJ_WEAK_def
proof (intro allI impI)
  fix p q assume "T (disj p q)"
  then have "T p \<or> T q" using cl unfolding CL_PROP_def by blast
  then show "PG p (disj p q) \<or> PG q (disj p q)" using d unfolding DISJ_PART_def by blast
qed
lemma EX_PART_WEAK: assumes cl: "CL_QUANT" and e: "EX_PART" shows "EX_WEAK"
  unfolding EX_WEAK_def
proof (intro allI impI, elim conjE)
  fix f assume ad: "adm f" and "T (exq f)"
  then obtain a where t: "T (app f a)" using cl unfolding CL_QUANT_def by blast
  then have "PG (app f a) (exq f)" using e ad unfolding EX_PART_def by blast
  then show "\<exists>a. PG (app f a) (exq f)" by blast
qed

text \<open>Given LAM.ENV, the denotation of a formula depends only on the values of its
  free variables, so a closed formula denotes the same proposition under every
  environment. This is why the restricted entries are read on closed formulas
  (registry decision D5): a closed formula of level 0, or without Tr, is a sentence
  with that property, and what it denotes is fixed.\<close>
lemma den_fv:
  assumes core: "LAM_CORE" and ag: "\<forall>y\<in>fv a. v y = w y"
  shows "den v a = den w a"
proof -
  have le: "lam x b v = lam x b w" if "\<forall>y\<in>fv b - {x}. v y = w y" for x b
    using that core unfolding LAM_CORE_def by blast
  show ?thesis using ag
  proof (induction a)
    case (Ex x a)
    then have "lam x a v = lam x a w" by (intro le) simp
    then show ?case by simp
  next
    case (All x a)
    then have "lam x a v = lam x a w" by (intro le) simp
    then show ?case by simp
  next
    case (BigC x a)
    then have "lam x a v = lam x a w" by (intro le) simp
    then show ?case by simp
  qed auto
qed

corollary den_closed: "LAM_CORE \<Longrightarrow> fv a = {} \<Longrightarrow> den v a = den w a"
  by (rule den_fv) auto

text \<open>CL.QUANT alone yields a truth: its third clause makes the conjunction of an
  empty satisfier set true (audit finding A3, registry finding F6).\<close>
lemma CL_QUANT_truth: assumes "CL_QUANT" shows "\<exists>p. T p"
proof (rule ccontr)
  assume n: "\<not> (\<exists>p. T p)"
  have "T (bigconj f) \<longleftrightarrow> (\<forall>q\<in>sat f. T q)" for f using assms unfolding CL_QUANT_def by blast
  moreover have "sat f = {}" for f unfolding sat_def using n by blast
  ultimately have "T (bigconj f)" for f by simp
  thus False using n by blast
qed

lemma EMPTY_excl: "EMPTY_NONE \<longleftrightarrow> \<not> EMPTY_SOME" unfolding EMPTY_NONE_def EMPTY_SOME_def by blast

text \<open>BETA.ID and BETA.GROUND exclude each other as soon as some proposition is true:
  the lambda term for the identity body applied to a truth p would be both identical
  to p and distinct from it. CL.QUANT supplies a truth.\<close>
lemma BETA_excl: assumes id: "BETA_ID" and gr: "BETA_GROUND" and t: "T p" shows False
proof -
  let ?v = "\<lambda>_::nat. p"
  have d: "den (?v(0 := p)) (Var 0) = p" by simp
  have "app (lam 0 (Var 0) ?v) p = den (?v(0 := p)) (Var 0)"
    using id unfolding BETA_ID_def by blast
  moreover have "app (lam 0 (Var 0) ?v) p \<noteq> den (?v(0 := p)) (Var 0)"
    using gr t d unfolding BETA_GROUND_def by metis
  ultimately show False by blast
qed

corollary BETA_excl_CL_QUANT: "BETA_ID \<Longrightarrow> BETA_GROUND \<Longrightarrow> CL_QUANT \<Longrightarrow> False"
  using BETA_excl CL_QUANT_truth by blast

text \<open>The binary clause of CONJ.GRAIN follows from Fritz's (\<and>1) and (\<and>2) once
  conjunction is truth-functional: the immediate partial grounds of a true conjunction
  are exactly its two conjuncts, so equal true conjunctions have the same conjuncts.\<close>
lemma grain_bin_from_FRITZ7:
  assumes cl: "CL_PROP" and f7: "IMM_FRITZ7"
      and t: "T (conj p q)" and e: "conj p q = conj p' q'"
  shows "{p, q} = {p', q'}"
proof -
  have i1: "T a \<and> T b \<Longrightarrow> IPG a (conj a b) \<and> IPG b (conj a b)" for a b
    using f7 unfolding IMM_FRITZ7_def by blast
  have i2: "IPG r (conj a b) \<Longrightarrow> r = a \<or> r = b" for r a b
    using f7 unfolding IMM_FRITZ7_def by blast
  have c: "T (conj a b) \<longleftrightarrow> T a \<and> T b" for a b using cl unfolding CL_PROP_def by blast
  have t1: "T p \<and> T q" using t c by blast
  have t2: "T p' \<and> T q'" using t e c by metis
  have "IPG p (conj p' q') \<and> IPG q (conj p' q')" using i1[OF t1] e by simp
  hence a: "(p = p' \<or> p = q') \<and> (q = p' \<or> q = q')" using i2 by blast
  have "IPG p' (conj p q) \<and> IPG q' (conj p q)" using i1[OF t2] e by simp
  hence b: "(p' = p \<or> p' = q) \<and> (q' = p \<or> q' = q)" using i2 by blast
  from a b show ?thesis by auto
qed

section \<open>Every comprehension level implies the four witness entries\<close>

lemma C1_W: assumes "C1" shows "W_ID" "W_TR" "W_EM" "W_TEM"
  using assms unfolding C1_def W_ID_def W_TR_def W_EM_def W_TEM_def by blast+

text \<open>The four witnesses are lambda terms whose bodies have level 0.\<close>
lemma C2_W: assumes "C2 k" shows "W_ID" "W_TR" "W_EM" "W_TEM"
proof -
  have a: "\<And>b. lvl b = 0 \<Longrightarrow> adm (lam 0 b e0)"
  proof -
    fix b :: fm assume "lvl b = 0"
    hence "\<exists>x a v. lvl a \<le> k \<and> lam 0 b e0 = lam x a v" by (intro exI[of _ 0] exI[of _ b] exI[of _ e0]) simp
    thus "adm (lam 0 b e0)" using assms unfolding C2_def by blast
  qed
  show "W_ID" unfolding W_ID_def f_id_def by (rule a) simp
  show "W_TR" unfolding W_TR_def f_tr_def by (rule a) simp
  show "W_EM" unfolding W_EM_def f_em_def by (rule a) simp
  show "W_TEM" unfolding W_TEM_def f_tem_def by (rule a) simp
qed

lemma C3d_W: assumes "C3d" shows "W_ID" "W_TR" "W_EM" "W_TEM"
  using assms unfolding C3d_def W_ID_def W_TR_def W_EM_def W_TEM_def
    f_id_def f_tr_def f_em_def f_tem_def by blast+

lemma C3s_W: assumes "C3s" shows "W_ID" "W_TR" "W_EM" "W_TEM"
  using assms unfolding C3s_def W_ID_def W_TR_def W_EM_def W_TEM_def by blast+

end
