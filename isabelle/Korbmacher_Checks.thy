theory Korbmacher_Checks
  imports Signature
begin

text \<open>
  Korbmacher's puzzle (SOPhiA 2015 slides, "Yet Another Puzzle of Ground",
  slides 8-9; journal version Kriterion 29(2) 2015, not received). Over PA with a
  ground predicate, the diagonal lemma gives a sentence d equivalent to
  "d does not partially ground d or d". Factivity plus disjunction grounding then
  yields a contradiction; the same holds with double-negation grounding.

  Here propositions are a base type, so there is no diagonal lemma. The diagonal
  sentence becomes an explicit witness hypothesis DIAG (a named-witness
  comprehension assumption in the style of C1): some proposition is true exactly
  when it does not partially ground its own self-disjunction. Nothing is an axiom.
\<close>

definition FACT_L :: bool where
  "FACT_L \<longleftrightarrow> (\<forall>\<Gamma> q. G \<Gamma> q \<longrightarrow> (\<forall>p\<in>\<Gamma>. T p))"

definition DISJ_ONE_L :: bool where
  "DISJ_ONE_L \<longleftrightarrow> (\<forall>p q. T p \<longrightarrow> G {p} (disj p q))"

definition NEG_DN :: bool where
  "NEG_DN \<longleftrightarrow> (\<forall>p. T p \<longrightarrow> G {p} (neg (neg p)))"

lemma PG_fact:
  assumes "FACT_L" "PG p q" shows "T p"
  using assms unfolding FACT_L_def PG_def by blast

theorem korbmacher_disj:
  assumes fact: "FACT_L" and disj: "DISJ_ONE_L"
      and diag: "T d \<longleftrightarrow> \<not> PG d (disj d d)"
  shows False
proof -
  have notT: "\<not> T d"
  proof
    assume "T d"
    then have "G {d} (disj d d)" using disj unfolding DISJ_ONE_L_def by blast
    then have "PG d (disj d d)" unfolding PG_def by blast
    with \<open>T d\<close> diag show False by blast
  qed
  then have "PG d (disj d d)" using diag by blast
  then have "T d" using PG_fact[OF fact] by blast
  with notT show False by blast
qed

theorem korbmacher_dn:
  assumes fact: "FACT_L" and dn: "NEG_DN"
      and diag: "T d \<longleftrightarrow> \<not> PG d (neg (neg d))"
  shows False
proof -
  have notT: "\<not> T d"
  proof
    assume "T d"
    then have "G {d} (neg (neg d))" using dn unfolding NEG_DN_def by blast
    then have "PG d (neg (neg d))" unfolding PG_def by blast
    with \<open>T d\<close> diag show False by blast
  qed
  then have "PG d (neg (neg d))" using diag by blast
  then have "T d" using PG_fact[OF fact] by blast
  with notT show False by blast
qed

text \<open>
  Korbmacher's untyped response (slide 12) restricts disjunction grounding to
  grounded disjuncts. His observation: the restricted rule plus factivity proves
  that d is ungrounded. Checked here in the same encoding.
\<close>

definition DISJ_ONE_GROUNDED :: bool where
  "DISJ_ONE_GROUNDED \<longleftrightarrow> (\<forall>p q. (\<exists>x. PG x p) \<longrightarrow> G {p} (disj p q))"

theorem korbmacher_untyped_ungrounded:
  assumes fact: "FACT_L" and disj: "DISJ_ONE_GROUNDED"
      and diag: "T d \<longleftrightarrow> \<not> PG d (disj d d)"
  shows "\<not> (\<exists>y. PG y d)"
proof
  assume g: "\<exists>y. PG y d"
  then have "G {d} (disj d d)" using disj unfolding DISJ_ONE_GROUNDED_def by blast
  then have pg: "PG d (disj d d)" unfolding PG_def by blast
  then have "T d" using PG_fact[OF fact] by blast
  with pg diag show False by blast
qed

end
