theory Russell_Checks
  imports Main
begin

text \<open>
  Ground Map, pre-step-2 checks (registry v0.1.0-draft, 2026-11-26).
  No axioms: every principle is an explicit hypothesis of the theorem that uses it.
  Signature as in principles/registry.yaml, restricted to what these checks need.
\<close>

typedecl prp
typedecl pfun

consts
  T       :: "prp \<Rightarrow> bool"
  neg     :: "prp \<Rightarrow> prp"
  app     :: "pfun \<Rightarrow> prp \<Rightarrow> prp"
  exq      :: "pfun \<Rightarrow> prp"
  allq     :: "pfun \<Rightarrow> prp"
  bigconj :: "pfun \<Rightarrow> prp"
  G       :: "prp set \<Rightarrow> prp \<Rightarrow> bool"

definition inst :: "pfun \<Rightarrow> prp set" where
  "inst f = range (app f)"

text \<open>Conjuncts of the conjunction of f: the propositions that satisfy f (corrected reading).\<close>
definition sat :: "pfun \<Rightarrow> prp set" where
  "sat f = {p. T (app f p)}"

lemma some_truth:
  assumes CL_neg: "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
  obtains q where "T q"
  using CL_neg by metis

text \<open>Kr\"amer's puzzle: C1 (identity witness, i.e. beta-identity), CL, EX.FULL, IRR.F.\<close>
theorem kramer:
  assumes C1_id:   "\<forall>p. app f_id p = p"
      and CL_neg:  "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_ex:   "\<forall>f. T (exq f) \<longleftrightarrow> (\<exists>a. T (app f a))"
      and EX_FULL: "\<forall>f a. T (app f a) \<longrightarrow> G {app f a} (exq f)"
      and IRR_F:   "\<forall>\<Gamma> c. G \<Gamma> c \<longrightarrow> c \<notin> \<Gamma>"
  shows False
proof -
  obtain q where q: "T q" using some_truth CL_neg by blast
  have "T (exq f_id)" using CL_ex C1_id q by metis
  hence "G {app f_id (exq f_id)} (exq f_id)" using EX_FULL C1_id by metis
  hence "G {exq f_id} (exq f_id)" using C1_id by simp
  thus False using IRR_F by blast
qed

text \<open>X.RUSSELL.ALL, simplified: the universal whose instances are exactly the truths.
  Needs C3s (every function, here one defined by cases on truth), CL, ALL.INST, IRR.F.\<close>
theorem universal_of_truths:
  assumes C3s:      "\<forall>h. \<exists>f. app f = h"
      and CL_neg:   "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_all:   "\<forall>f. T (allq f) \<longleftrightarrow> (\<forall>a. T (app f a))"
      and ALL_INST: "\<forall>f. (\<forall>a. T (app f a)) \<longrightarrow> G (inst f) (allq f)"
      and IRR_F:    "\<forall>\<Gamma> c. G \<Gamma> c \<longrightarrow> c \<notin> \<Gamma>"
  shows False
proof -
  obtain q where q: "T q" using some_truth CL_neg by blast
  obtain g where g: "app g = (\<lambda>x. if T x then x else q)" using C3s by blast
  have vals: "\<forall>a. T (app g a)" using g q by simp
  hence Tall: "T (allq g)" using CL_all by blast
  have "app g (allq g) = allq g" using g Tall by simp
  hence mem: "allq g \<in> inst g" unfolding inst_def by (metis rangeI)
  have "G (inst g) (allq g)" using ALL_INST vals by blast
  thus False using IRR_F mem by blast
qed

text \<open>Conjunction of all truths (corrected satisfier reading): C1, CL, CONJ.INF, IRR.F.\<close>
theorem conjunction_of_truths:
  assumes C1_id:    "\<forall>p. app f_id p = p"
      and CL_neg:   "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_conj:  "\<forall>f. T (bigconj f) \<longleftrightarrow> (\<forall>p\<in>sat f. T p)"
      and CONJ_INF: "\<forall>f. sat f \<noteq> {} \<and> (\<forall>p\<in>sat f. T p) \<longrightarrow> G (sat f) (bigconj f)"
      and IRR_F:    "\<forall>\<Gamma> c. G \<Gamma> c \<longrightarrow> c \<notin> \<Gamma>"
  shows False
proof -
  obtain q where q: "T q" using some_truth CL_neg by blast
  have sat_id: "sat f_id = {p. T p}" unfolding sat_def using C1_id by simp
  have Tc: "T (bigconj f_id)" using CL_conj sat_id by simp
  have ne: "sat f_id \<noteq> {}" using sat_id q by auto
  have all_true: "\<forall>p\<in>sat f_id. T p" using sat_id by simp
  have "G (sat f_id) (bigconj f_id)" using CONJ_INF ne all_true by blast
  moreover have "bigconj f_id \<in> sat f_id" using sat_id Tc by simp
  ultimately show False using IRR_F by blast
qed

end
