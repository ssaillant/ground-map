theory Fine_Checks
  imports Main
begin

text \<open>
  Ground Map, Fine (2010) and Lovett (2019/2020) puzzles in their propositional form
  (registry v0.1.2-draft, 2026-11-26). No axioms: every principle is an explicit
  hypothesis. Fine's ground is partial (A \<prec> B); here it is PG, defined from full ground G.
  Fine's existence premises E(y) and Propositional Existence hold trivially in HOL.
\<close>

typedecl prp
typedecl pfun

consts
  T    :: "prp \<Rightarrow> bool"
  neg  :: "prp \<Rightarrow> prp"
  disj :: "prp \<Rightarrow> prp \<Rightarrow> prp"
  tr   :: "prp \<Rightarrow> prp"
  app  :: "pfun \<Rightarrow> prp \<Rightarrow> prp"
  exq  :: "pfun \<Rightarrow> prp"
  allq :: "pfun \<Rightarrow> prp"
  G    :: "prp set \<Rightarrow> prp \<Rightarrow> bool"

definition inst :: "pfun \<Rightarrow> prp set" where "inst f = range (app f)"
definition PG :: "prp \<Rightarrow> prp \<Rightarrow> bool" where "PG p q \<longleftrightarrow> (\<exists>\<Gamma>. p \<in> \<Gamma> \<and> G \<Gamma> q)"

lemma PG_single: "G {p} q \<Longrightarrow> PG p q" unfolding PG_def by blast

text \<open>Fine 2010 pp. 102-103, Universal Argument for Propositions:
  P0 = every proposition is true or not true; witness f_tem p = tr p \<or> \<not> tr p.\<close>
theorem fine_universal_props:
  assumes C1_tem:   "\<forall>p. app f_tem p = disj (tr p) (neg (tr p))"
      and CL_neg:   "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_disj:  "\<forall>p q. T (disj p q) \<longleftrightarrow> T p \<or> T q"
      and CL_all:   "\<forall>f. T (allq f) \<longleftrightarrow> (\<forall>a. T (app f a))"
      and TS_FULL:  "\<forall>p. T (tr p) \<longleftrightarrow> T p"
      and ALL_INST: "\<forall>f. (\<forall>a. T (app f a)) \<longrightarrow> G (inst f) (allq f)"
      and DISJ_ONE: "\<forall>p q. T p \<longrightarrow> G {p} (disj p q)"
      and TR_FULL:  "\<forall>p. T p \<longrightarrow> G {p} (tr p)"
      and TRANS_P:  "\<forall>p q r. PG p q \<and> PG q r \<longrightarrow> PG p r"
      and IRR_F:    "\<forall>\<Gamma> c. G \<Gamma> c \<longrightarrow> c \<notin> \<Gamma>"
  shows False
proof -
  let ?s = "allq f_tem"
  let ?d = "disj (tr ?s) (neg (tr ?s))"
  have vals: "\<forall>a. T (app f_tem a)" using C1_tem CL_disj CL_neg by simp
  hence Ts: "T ?s" using CL_all by blast
  have "G (inst f_tem) ?s" using ALL_INST vals by blast
  moreover have "?d \<in> inst f_tem" unfolding inst_def using C1_tem by (metis rangeI)
  ultimately have d_s: "PG ?d ?s" unfolding PG_def by blast
  have "T (tr ?s)" using TS_FULL Ts by blast
  hence tr_d: "PG (tr ?s) ?d" using DISJ_ONE PG_single by blast
  have s_tr: "PG ?s (tr ?s)" using TR_FULL Ts PG_single by blast
  have "PG ?s ?s" using TRANS_P s_tr tr_d d_s by blast
  thus False using IRR_F unfolding PG_def by blast
qed

text \<open>Fine 2010 p. 103, Particular Argument for Propositions:
  P1 = some proposition is true or not true.\<close>
theorem fine_particular_props:
  assumes C1_tem:   "\<forall>p. app f_tem p = disj (tr p) (neg (tr p))"
      and CL_neg:   "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_disj:  "\<forall>p q. T (disj p q) \<longleftrightarrow> T p \<or> T q"
      and CL_ex:    "\<forall>f. T (exq f) \<longleftrightarrow> (\<exists>a. T (app f a))"
      and TS_FULL:  "\<forall>p. T (tr p) \<longleftrightarrow> T p"
      and EX_FULL:  "\<forall>f a. T (app f a) \<longrightarrow> G {app f a} (exq f)"
      and DISJ_ONE: "\<forall>p q. T p \<longrightarrow> G {p} (disj p q)"
      and TR_FULL:  "\<forall>p. T p \<longrightarrow> G {p} (tr p)"
      and TRANS_P:  "\<forall>p q r. PG p q \<and> PG q r \<longrightarrow> PG p r"
      and IRR_F:    "\<forall>\<Gamma> c. G \<Gamma> c \<longrightarrow> c \<notin> \<Gamma>"
  shows False
proof -
  let ?s = "exq f_tem"
  let ?d = "disj (tr ?s) (neg (tr ?s))"
  have Td: "T ?d" using CL_disj CL_neg by simp
  have Ts: "T ?s" using CL_ex C1_tem Td by metis
  have d_s: "PG ?d ?s" using EX_FULL C1_tem Td PG_single by metis
  have "T (tr ?s)" using TS_FULL Ts by blast
  hence tr_d: "PG (tr ?s) ?d" using DISJ_ONE PG_single by blast
  have s_tr: "PG ?s (tr ?s)" using TR_FULL Ts PG_single by blast
  have "PG ?s ?s" using TRANS_P s_tr tr_d d_s by blast
  thus False using IRR_F unfolding PG_def by blast
qed

text \<open>"Something is true": Fine 2010 p. 106 (facts as propositions, obtaining as truth),
  Kr\"amer's Finean counterpart, Lovett p. 2541. Witness f_tr p = tr p.
  Version (a): asymmetry alone. Version (b): transitivity and irreflexivity.\<close>
theorem something_true_asym:
  assumes C1_tr:   "\<forall>p. app f_tr p = tr p"
      and CL_neg:  "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_ex:   "\<forall>f. T (exq f) \<longleftrightarrow> (\<exists>a. T (app f a))"
      and TS_FULL: "\<forall>p. T (tr p) \<longleftrightarrow> T p"
      and EX_FULL: "\<forall>f a. T (app f a) \<longrightarrow> G {app f a} (exq f)"
      and TR_FULL: "\<forall>p. T p \<longrightarrow> G {p} (tr p)"
      and ASYM_P:  "\<forall>p q. PG p q \<longrightarrow> \<not> PG q p"
  shows False
proof -
  obtain q where q: "T q" using CL_neg by metis
  let ?s = "exq f_tr"
  have Ts: "T ?s" using CL_ex C1_tr TS_FULL q by metis
  have Ttr: "T (tr ?s)" using TS_FULL Ts by blast
  have a: "PG (tr ?s) ?s" using EX_FULL C1_tr Ttr PG_single by metis
  have b: "PG ?s (tr ?s)" using TR_FULL Ts PG_single by blast
  show False using ASYM_P a b by blast
qed

theorem something_true_trans:
  assumes C1_tr:   "\<forall>p. app f_tr p = tr p"
      and CL_neg:  "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_ex:   "\<forall>f. T (exq f) \<longleftrightarrow> (\<exists>a. T (app f a))"
      and TS_FULL: "\<forall>p. T (tr p) \<longleftrightarrow> T p"
      and EX_FULL: "\<forall>f a. T (app f a) \<longrightarrow> G {app f a} (exq f)"
      and TR_FULL: "\<forall>p. T p \<longrightarrow> G {p} (tr p)"
      and TRANS_P: "\<forall>p q r. PG p q \<and> PG q r \<longrightarrow> PG p r"
      and IRR_F:   "\<forall>\<Gamma> c. G \<Gamma> c \<longrightarrow> c \<notin> \<Gamma>"
  shows False
proof -
  obtain q where q: "T q" using CL_neg by metis
  let ?s = "exq f_tr"
  have Ts: "T ?s" using CL_ex C1_tr TS_FULL q by metis
  have Ttr: "T (tr ?s)" using TS_FULL Ts by blast
  have a: "PG (tr ?s) ?s" using EX_FULL C1_tr Ttr PG_single by metis
  have b: "PG ?s (tr ?s)" using TR_FULL Ts PG_single by blast
  have "PG ?s ?s" using TRANS_P a b by blast
  thus False using IRR_F unfolding PG_def by blast
qed

text \<open>Sentence-position variant of Fine's universal argument (instance via Woods p. 645):
  s = (\<forall>p. p \<or> \<not>p). Witness f_em p = p \<or> \<not>p.\<close>
theorem fine_universal_sp:
  assumes C1_em:    "\<forall>p. app f_em p = disj p (neg p)"
      and CL_neg:   "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_disj:  "\<forall>p q. T (disj p q) \<longleftrightarrow> T p \<or> T q"
      and CL_all:   "\<forall>f. T (allq f) \<longleftrightarrow> (\<forall>a. T (app f a))"
      and ALL_INST: "\<forall>f. (\<forall>a. T (app f a)) \<longrightarrow> G (inst f) (allq f)"
      and DISJ_ONE: "\<forall>p q. T p \<longrightarrow> G {p} (disj p q)"
      and TRANS_P:  "\<forall>p q r. PG p q \<and> PG q r \<longrightarrow> PG p r"
      and IRR_F:    "\<forall>\<Gamma> c. G \<Gamma> c \<longrightarrow> c \<notin> \<Gamma>"
  shows False
proof -
  let ?s = "allq f_em"
  let ?d = "disj ?s (neg ?s)"
  have vals: "\<forall>a. T (app f_em a)" using C1_em CL_disj CL_neg by simp
  hence Ts: "T ?s" using CL_all by blast
  have "G (inst f_em) ?s" using ALL_INST vals by blast
  moreover have "?d \<in> inst f_em" unfolding inst_def using C1_em by (metis rangeI)
  ultimately have d_s: "PG ?d ?s" unfolding PG_def by blast
  have s_d: "PG ?s ?d" using DISJ_ONE Ts PG_single by blast
  have "PG ?s ?s" using TRANS_P s_d d_s by blast
  thus False using IRR_F unfolding PG_def by blast
qed

end
