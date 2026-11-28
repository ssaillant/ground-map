theory Principles
  imports Signature Fritz_Main
begin

text \<open>
  Step 4: every registry entry (v0.3.0-draft) as a closed boolean constant, so that a
  package is a conjunction of constants and the driver can ask for refutations and
  models. Statements follow principles/registry.yaml verbatim where possible. By D3,
  principles about quantifiers range over admissible functions (adm f); CL.QUANT is
  exempt. FACT and LAM_CORE are the core clauses, assumed in every package.
  Nothing here is an axiom.

  Every entry is standalone: no definition includes another entry of its family. The
  only order between entries is the set of implications proved in Order.thy.

  Restricted entries (D5, registry 0.3.0-draft). TS.TYPED, TR.TYPED, EX.PRED and EX.LEV
  restrict a principle to propositions presented by a CLOSED formula (fv a = {}) with
  the stated property. In 0.2.1-draft the formula could have free variables, and each
  restricted entry was then equivalent to its unrestricted counterpart, because Var 0
  denotes every proposition under some environment (Audit_Checks.thy keeps that proof
  for the old definitions).
\<close>

consts tot :: "pfun \<Rightarrow> prp"

definition FACT :: bool where
  "FACT \<longleftrightarrow> (\<forall>\<Gamma> p. G \<Gamma> p \<longrightarrow> T p \<and> (\<forall>q\<in>\<Gamma>. T q))"

section \<open>IRR, ASYM, TRANS, AMALG\<close>

definition IRR_W :: bool where
  "IRR_W \<longleftrightarrow> (\<forall>\<Gamma> c. G \<Gamma> c \<and> c \<in> \<Gamma> \<longrightarrow> vacW c \<Gamma> c)"
definition IRR_F :: bool where
  "IRR_F \<longleftrightarrow> (\<forall>\<Gamma> c. G \<Gamma> c \<longrightarrow> c \<notin> \<Gamma>)"
definition vacM :: "prp set \<Rightarrow> prp \<Rightarrow> prp \<Rightarrow> bool" where
  "vacM \<Gamma> a c \<longleftrightarrow> a \<in> \<Gamma> \<and> (\<forall>b. T b \<longrightarrow> G (insert b (\<Gamma> - {a})) c)"
definition IRR_MEM :: bool where
  "IRR_MEM \<longleftrightarrow> (\<forall>\<Gamma> c. G \<Gamma> c \<and> c \<in> \<Gamma> \<longrightarrow> vacM \<Gamma> c c)"

definition ASYM_ANTI :: bool where
  "ASYM_ANTI \<longleftrightarrow> (\<forall>p q. PG p q \<and> PG q p \<longrightarrow> p = q)"
definition ASYM_P :: bool where
  "ASYM_P \<longleftrightarrow> (\<forall>p q. PG p q \<longrightarrow> \<not> PG q p)"

definition TRANS_P :: bool where
  "TRANS_P \<longleftrightarrow> (\<forall>p q r. PG p q \<and> PG q r \<longrightarrow> PG p r)"
definition TRANS_CUT :: bool where
  "TRANS_CUT \<longleftrightarrow> (\<forall>\<Gamma> \<Delta> H q. G \<Gamma> q \<and> \<Delta> \<subseteq> \<Gamma> \<and> (\<forall>p\<in>\<Delta>. G (H p) p)
       \<longrightarrow> G ((\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)) q)"

definition AMALG_FIN :: bool where
  "AMALG_FIN \<longleftrightarrow> (\<forall>\<Gamma> \<Delta> p. G \<Gamma> p \<and> G \<Delta> p \<longrightarrow> G (\<Gamma> \<union> \<Delta>) p)"
definition AMALG_INF :: bool where
  "AMALG_INF \<longleftrightarrow> (\<forall>F p. F \<noteq> {} \<and> (\<forall>\<Gamma>\<in>F. G \<Gamma> p) \<longrightarrow> G (\<Union>F) p)"

section \<open>Classical truth, truth schema, identities\<close>

definition CL_PROP :: bool where
  "CL_PROP \<longleftrightarrow> (\<forall>p q. (T (neg p) \<longleftrightarrow> \<not> T p) \<and> (T (conj p q) \<longleftrightarrow> T p \<and> T q)
                     \<and> (T (disj p q) \<longleftrightarrow> T p \<or> T q))"
definition CL_QUANT :: bool where
  "CL_QUANT \<longleftrightarrow> (\<forall>f. (T (exq f) \<longleftrightarrow> (\<exists>a. T (app f a))) \<and> (T (allq f) \<longleftrightarrow> (\<forall>a. T (app f a)))
                     \<and> (T (bigconj f) \<longleftrightarrow> (\<forall>q\<in>sat f. T q)))"

definition TS_TYPED :: bool where
  "TS_TYPED \<longleftrightarrow> (\<forall>a v. tfree a \<and> fv a = {} \<longrightarrow> (T (tr (den v a)) \<longleftrightarrow> T (den v a)))"
definition TS_FULL :: bool where
  "TS_FULL \<longleftrightarrow> (\<forall>p. T (tr p) \<longleftrightarrow> T p)"
definition TS_ID :: bool where
  "TS_ID \<longleftrightarrow> (\<forall>p. tr p = p)"

definition ID_AC :: bool where
  "ID_AC \<longleftrightarrow> (\<forall>p q r. conj p q = conj q p \<and> disj p q = disj q p
     \<and> conj p (conj q r) = conj (conj p q) r \<and> disj p (disj q r) = disj (disj p q) r
     \<and> conj p p = p \<and> disj p p = p)"
definition ID_DN :: bool where
  "ID_DN \<longleftrightarrow> (\<forall>p. neg (neg p) = p)"

section \<open>Introduction principles\<close>

definition CONJ_BIN :: bool where
  "CONJ_BIN \<longleftrightarrow> (\<forall>p q. T p \<and> T q \<longrightarrow> G {p, q} (conj p q))"
definition CONJ_INF :: bool where
  "CONJ_INF \<longleftrightarrow> (\<forall>f. adm f \<and> sat f \<noteq> {} \<and> (\<forall>q\<in>sat f. T q) \<longrightarrow> G (sat f) (bigconj f))"
definition CONJ_GRAIN :: bool where
  "CONJ_GRAIN \<longleftrightarrow> (\<forall>p q p' q'. T (conj p q) \<and> conj p q = conj p' q' \<longrightarrow> {p, q} = {p', q'})
     \<and> (\<forall>f g. adm f \<and> adm g \<and> (\<forall>q\<in>sat f. T q) \<and> (\<forall>q\<in>sat g. T q) \<and> bigconj f = bigconj g
            \<longrightarrow> sat f = sat g)"

definition DISJ_ONE :: bool where
  "DISJ_ONE \<longleftrightarrow> (\<forall>p q. (T p \<longrightarrow> G {p} (disj p q)) \<and> (T q \<longrightarrow> G {q} (disj p q)))"
definition DISJ_BOTH :: bool where
  "DISJ_BOTH \<longleftrightarrow> (\<forall>p q. T p \<and> T q \<longrightarrow> G {p, q} (disj p q))"
definition DISJ_PART :: bool where
  "DISJ_PART \<longleftrightarrow> (\<forall>p q. (T p \<longrightarrow> PG p (disj p q)) \<and> (T q \<longrightarrow> PG q (disj p q)))"
definition DISJ_WEAK :: bool where
  "DISJ_WEAK \<longleftrightarrow> (\<forall>p q. T (disj p q) \<longrightarrow> PG p (disj p q) \<or> PG q (disj p q))"

definition NEG_DN :: bool where
  "NEG_DN \<longleftrightarrow> (\<forall>p. T p \<longrightarrow> G {p} (neg (neg p)))"
definition NEG_DM :: bool where
  "NEG_DM \<longleftrightarrow> (\<forall>p q. (T (neg p) \<longrightarrow> G {neg p} (neg (conj p q)))
     \<and> (T (neg q) \<longrightarrow> G {neg q} (neg (conj p q)))
     \<and> (T (neg p) \<and> T (neg q) \<longrightarrow> G {neg p, neg q} (neg (disj p q))))"

definition EX_PRED :: bool where
  "EX_PRED \<longleftrightarrow> (\<forall>f a w. adm f \<and> lvl a = 0 \<and> fv a = {} \<and> T (app f (den w a))
     \<longrightarrow> G {app f (den w a)} (exq f))"
definition EX_LEV :: bool where
  "EX_LEV \<longleftrightarrow> (\<forall>x b v a w. adm (lam x b v) \<and> lvl a < lvl (Ex x b) \<and> fv a = {}
     \<and> T (app (lam x b v) (den w a))
     \<longrightarrow> G {app (lam x b v) (den w a)} (exq (lam x b v)))"
definition EX_FULL :: bool where
  "EX_FULL \<longleftrightarrow> (\<forall>f a. adm f \<and> T (app f a) \<longrightarrow> G {app f a} (exq f))"
definition EX_PART :: bool where
  "EX_PART \<longleftrightarrow> (\<forall>f a. adm f \<and> T (app f a) \<longrightarrow> PG (app f a) (exq f))"
definition EX_WEAK :: bool where
  "EX_WEAK \<longleftrightarrow> (\<forall>f. adm f \<and> T (exq f) \<longrightarrow> (\<exists>a. PG (app f a) (exq f)))"

definition ALL_PART :: bool where
  "ALL_PART \<longleftrightarrow> (\<forall>f a. adm f \<and> (\<forall>b. T (app f b)) \<longrightarrow> PG (app f a) (allq f))"
definition ALL_INST :: bool where
  "ALL_INST \<longleftrightarrow> (\<forall>f. adm f \<and> (\<forall>a. T (app f a)) \<longrightarrow> G (inst f) (allq f))"
definition ALL_TOT :: bool where
  "ALL_TOT \<longleftrightarrow> (\<forall>f. adm f \<and> (\<forall>a. T (app f a)) \<longrightarrow> T (tot f) \<and> G (insert (tot f) (inst f)) (allq f))"

definition TR_TYPED :: bool where
  "TR_TYPED \<longleftrightarrow> (\<forall>a v. tfree a \<and> fv a = {} \<and> T (den v a) \<longrightarrow> G {den v a} (tr (den v a)))"
definition TR_PART :: bool where
  "TR_PART \<longleftrightarrow> (\<forall>p. T p \<longrightarrow> PG p (tr p))"
definition TR_FULL :: bool where
  "TR_FULL \<longleftrightarrow> (\<forall>p. T p \<longrightarrow> G {p} (tr p))"
definition TR_NEG :: bool where
  "TR_NEG \<longleftrightarrow> (\<forall>p. T (neg p) \<longrightarrow> G {neg p} (neg (tr p)))"

section \<open>Empty and infinitary grounds\<close>

definition EMPTY_NONE :: bool where "EMPTY_NONE \<longleftrightarrow> (\<forall>p. \<not> G {} p)"
definition EMPTY_SOME :: bool where "EMPTY_SOME \<longleftrightarrow> (\<exists>p. G {} p)"
definition FIN_FIN :: bool where "FIN_FIN \<longleftrightarrow> (\<forall>\<Gamma> p. G \<Gamma> p \<longrightarrow> finite \<Gamma>)"
definition FIN_B3 :: bool where "FIN_B3 \<longleftrightarrow> (\<forall>\<Gamma> p. G \<Gamma> p \<longrightarrow> finite \<Gamma> \<and> card \<Gamma> \<le> 3)"

section \<open>Immediate ground (D1)\<close>

definition IMM_CONJ :: bool where
  "IMM_CONJ \<longleftrightarrow> (\<forall>f. adm f \<and> (\<forall>r\<in>sat f. T r) \<longrightarrow> (\<forall>p. IPG p (bigconj f) \<longleftrightarrow> p \<in> sat f))"
definition IMM_FRITZ7 :: bool where
  "IMM_FRITZ7 \<longleftrightarrow>
     (\<forall>p q. T p \<and> T q \<longrightarrow> IPG p (conj p q) \<and> IPG q (conj p q))
   \<and> (\<forall>r p q. IPG r (conj p q) \<longrightarrow> r = p \<or> r = q)
   \<and> (\<forall>p q. T (disj p q) \<longrightarrow> IPG p (disj p q) \<or> IPG q (disj p q))
   \<and> (\<forall>r p q. IPG r (disj p q) \<longrightarrow> r = p \<or> r = q)
   \<and> (\<forall>g x. adm g \<and> T (allq g) \<longrightarrow> IPG (app g x) (allq g))
   \<and> (\<forall>g q. adm g \<and> IPG q (allq g) \<and> (\<forall>x. q \<noteq> app g x) \<longrightarrow> q = tt)
   \<and> \<not> (\<forall>p q. T p \<and> T q \<longrightarrow> IPG p q)"

section \<open>Non-triviality (cumulative, k = 3, d = 3)\<close>

definition N1 :: bool where "N1 \<longleftrightarrow> (\<exists>\<Gamma> p. G \<Gamma> p)"
definition N2 :: bool where
  "N2 \<longleftrightarrow> N1 \<and> (\<exists>a b c. distinct [a, b, c] \<and> T a \<and> T b \<and> T c)"
text \<open>N4 without its cumulative part (N3 has no formal statement): one of the four pairs of
  classically equivalent shapes listed in the registry is distinct and has different sets of
  full grounds.\<close>
definition N4_pairs :: bool where
  "N4_pairs \<longleftrightarrow> (\<exists>x y. ((\<exists>p. x = p \<and> y = neg (neg p)) \<or> (\<exists>p q. x = conj p q \<and> y = conj q p)
       \<or> (\<exists>p. x = p \<and> y = conj p p) \<or> (\<exists>p q. x = disj p q \<and> y = disj q p))
     \<and> x \<noteq> y \<and> {\<Gamma>. G \<Gamma> x} \<noteq> {\<Gamma>. G \<Gamma> y})"
definition N5_chain :: bool where
  "N5_chain \<longleftrightarrow> (\<exists>x0 x1 x2 x3. distinct [x0, x1, x2, x3] \<and> PG x0 x1 \<and> PG x1 x2 \<and> PG x2 x3)"

section \<open>Witness entries: lower bounds on comprehension (decision D9)\<close>

text \<open>Each entry says that one named propositional function is admissible and nothing
  about any other. They can be combined with one another, and each follows from every
  comprehension level C1 to C3s (Order.thy).\<close>
definition W_ID :: bool where "W_ID \<longleftrightarrow> adm f_id"
definition W_TR :: bool where "W_TR \<longleftrightarrow> adm f_tr"
definition W_EM :: bool where "W_EM \<longleftrightarrow> adm f_em"
definition W_TEM :: bool where "W_TEM \<longleftrightarrow> adm f_tem"

end
