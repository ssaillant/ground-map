theory No_Finite_Models
  imports Signature
begin

text \<open>
  Step 3 finding for the search design (step 4): once a truth exists, any package with
  transitivity and irreflexivity and one "successor" introduction rule (CONJ.BIN applied to
  p and p, or TR.FULL, or DISJ.ONE applied to p and p) has no finite model, because the
  chain p, s p, s (s p), ... must repeat. Nitpick can therefore only find models of packages
  that drop one of these; all others need infinite-model certificates.
\<close>

lemma chain_no_finite:
  fixes s :: "prp \<Rightarrow> prp"
  assumes fin: "finite (UNIV :: prp set)"
      and c: "T c"
      and step: "\<And>p. T p \<Longrightarrow> T (s p) \<and> PG p (s p)"
      and TRANS_P: "\<forall>p q r. PG p q \<and> PG q r \<longrightarrow> PG p r"
      and IRR_F: "\<forall>\<Gamma> x. G \<Gamma> x \<longrightarrow> x \<notin> \<Gamma>"
  shows False
proof -
  define ch where "ch n = (s ^^ n) c" for n
  have Tch: "T (ch n)" for n by (induct n) (simp_all add: ch_def c step)
  have up: "PG (ch i) (ch (i + Suc k))" for i k
  proof (induct k)
    case 0 show ?case using step Tch unfolding ch_def by simp
  next
    case (Suc k)
    have "PG (ch (i + Suc k)) (ch (i + Suc (Suc k)))" using step Tch unfolding ch_def by simp
    thus ?case using Suc TRANS_P by blast
  qed
  have "\<not> inj ch"
  proof
    assume "inj ch"
    moreover have "finite (range ch)" using fin by (rule finite_subset[OF subset_UNIV])
    ultimately have "finite (UNIV :: nat set)" using finite_imageD by blast
    thus False by simp
  qed
  then obtain i j where ij: "i \<noteq> j" "ch i = ch j" unfolding inj_def by blast
  have "\<exists>m k. ch m = ch (m + Suc k)"
  proof (cases "i < j")
    case True
    then obtain k where "j = Suc (i + k)" using less_imp_Suc_add by blast
    hence "ch i = ch (i + Suc k)" using ij(2) by simp
    thus ?thesis by blast
  next
    case False
    hence "j < i" using ij(1) by simp
    then obtain k where "i = Suc (j + k)" using less_imp_Suc_add by blast
    hence "ch j = ch (j + Suc k)" using ij(2) by simp
    thus ?thesis by blast
  qed
  then obtain m k where e: "ch m = ch (m + Suc k)" by blast
  have "PG (ch m) (ch (m + Suc k))" by (rule up)
  hence "PG (ch m) (ch m)" using e by simp
  thus False using IRR_F unfolding PG_def by blast
qed

theorem no_finite_model_conj:
  assumes "finite (UNIV :: prp set)"
      and CL_neg: "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_conj: "\<forall>p q. T (conj p q) \<longleftrightarrow> T p \<and> T q"
      and CONJ_BIN: "\<forall>p q. T p \<and> T q \<longrightarrow> G {p, q} (conj p q)"
      and TRANS_P: "\<forall>p q r. PG p q \<and> PG q r \<longrightarrow> PG p r"
      and IRR_F: "\<forall>\<Gamma> x. G \<Gamma> x \<longrightarrow> x \<notin> \<Gamma>"
  shows False
proof -
  obtain c where c: "T c" using CL_neg by metis
  have step: "T p \<Longrightarrow> T (conj p p) \<and> PG p (conj p p)" for p
    using CL_conj CONJ_BIN unfolding PG_def by fastforce
  show False using chain_no_finite[OF assms(1) c step TRANS_P IRR_F] .
qed

theorem no_finite_model_tr:
  assumes "finite (UNIV :: prp set)"
      and CL_neg: "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and TS_FULL: "\<forall>p. T (tr p) \<longleftrightarrow> T p"
      and TR_FULL: "\<forall>p. T p \<longrightarrow> G {p} (tr p)"
      and TRANS_P: "\<forall>p q r. PG p q \<and> PG q r \<longrightarrow> PG p r"
      and IRR_F: "\<forall>\<Gamma> x. G \<Gamma> x \<longrightarrow> x \<notin> \<Gamma>"
  shows False
proof -
  obtain c where c: "T c" using CL_neg by metis
  have step: "T p \<Longrightarrow> T (tr p) \<and> PG p (tr p)" for p
    using TS_FULL TR_FULL unfolding PG_def by blast
  show False using chain_no_finite[OF assms(1) c step TRANS_P IRR_F] .
qed

theorem no_finite_model_disj:
  assumes "finite (UNIV :: prp set)"
      and CL_neg: "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_disj: "\<forall>p q. T (disj p q) \<longleftrightarrow> T p \<or> T q"
      and DISJ_ONE: "\<forall>p q. T p \<longrightarrow> G {p} (disj p q)"
      and TRANS_P: "\<forall>p q r. PG p q \<and> PG q r \<longrightarrow> PG p r"
      and IRR_F: "\<forall>\<Gamma> x. G \<Gamma> x \<longrightarrow> x \<notin> \<Gamma>"
  shows False
proof -
  obtain c where c: "T c" using CL_neg by metis
  have step: "T p \<Longrightarrow> T (disj p p) \<and> PG p (disj p p)" for p
    using CL_disj DISJ_ONE unfolding PG_def by blast
  show False using chain_no_finite[OF assms(1) c step TRANS_P IRR_F] .
qed

end
