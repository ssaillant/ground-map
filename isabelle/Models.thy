theory Models
  imports Principles
begin

text \<open>
  Infinite-model certificates (decision D4).

  The principles in Principles.thy are statements about uninterpreted constants (T, G,
  neg, ..., over the declared types prp and pfun). To certify a package as consistent we
  restate the principles over an arbitrary structure S (a record of the same operations
  over arbitrary types 'p and 'f), prove that the restatement at the structure S0 of the
  constants is literally the original principle (fidelity lemmas, below), and exhibit a
  concrete structure satisfying the package.

  Metatheory (not checked by Isabelle): no axiom constrains the constants or the types prp
  and pfun, so a HOL proof that the original package is inconsistent would generalise to
  every structure, contradicting the model. The model therefore certifies consistency.
  Section M1 gives the first such model (registry finding F3); the last section mechanizes
  Goodman 2023's negation variant of Kr\"amer's puzzle (finding F4).
\<close>

section \<open>Structures\<close>

record ('p, 'f) gstr =
  sT    :: "'p \<Rightarrow> bool"
  sG    :: "'p set \<Rightarrow> 'p \<Rightarrow> bool"
  satom :: "nat \<Rightarrow> 'p"
  sneg  :: "'p \<Rightarrow> 'p"
  sconj :: "'p \<Rightarrow> 'p \<Rightarrow> 'p"
  sdisj :: "'p \<Rightarrow> 'p \<Rightarrow> 'p"
  strr  :: "'p \<Rightarrow> 'p"
  sapp  :: "'f \<Rightarrow> 'p \<Rightarrow> 'p"
  sexq  :: "'f \<Rightarrow> 'p"
  sallq :: "'f \<Rightarrow> 'p"
  sbig  :: "'f \<Rightarrow> 'p"
  slam  :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> 'p) \<Rightarrow> 'f"
  sadm  :: "'f \<Rightarrow> bool"

primrec sden :: "('p, 'f) gstr \<Rightarrow> (nat \<Rightarrow> 'p) \<Rightarrow> fm \<Rightarrow> 'p" where
  "sden S v (Var n) = v n"
| "sden S v (Cst n) = satom S n"
| "sden S v (Neg a) = sneg S (sden S v a)"
| "sden S v (Conj a b) = sconj S (sden S v a) (sden S v b)"
| "sden S v (Disj a b) = sdisj S (sden S v a) (sden S v b)"
| "sden S v (Tr a) = strr S (sden S v a)"
| "sden S v (Ex x a) = sexq S (slam S x a v)"
| "sden S v (All x a) = sallq S (slam S x a v)"
| "sden S v (BigC x a) = sbig S (slam S x a v)"

definition S0 :: "(prp, pfun) gstr" where
  "S0 = \<lparr>sT = T, sG = G, satom = atom, sneg = neg, sconj = conj, sdisj = disj, strr = tr,
         sapp = app, sexq = exq, sallq = allq, sbig = bigconj, slam = lam, sadm = adm\<rparr>"

lemma S0_sel [simp]:
  "sT S0 = T" "sG S0 = G" "satom S0 = atom" "sneg S0 = neg" "sconj S0 = conj" "sdisj S0 = disj"
  "strr S0 = tr" "sapp S0 = app" "sexq S0 = exq" "sallq S0 = allq" "sbig S0 = bigconj"
  "slam S0 = lam" "sadm S0 = adm"
  by (simp_all add: S0_def)

lemma sden_S0: "sden S0 v a = den v a"
  by (induct a arbitrary: v) simp_all

section \<open>Principles over a structure\<close>

definition "pPG S p q \<longleftrightarrow> (\<exists>\<Gamma>. p \<in> \<Gamma> \<and> sG S \<Gamma> q)"
definition "psat S f = {p. sT S (sapp S f p)}"
definition "pinst S f = range (sapp S f)"

definition "pFACT S \<longleftrightarrow> (\<forall>\<Gamma> p. sG S \<Gamma> p \<longrightarrow> sT S p \<and> (\<forall>q\<in>\<Gamma>. sT S q))"
definition "pLAM_CORE S \<longleftrightarrow>
     (\<forall>x a v p. sT S (sapp S (slam S x a v) p) \<longleftrightarrow> sT S (sden S (v(x:=p)) a))
   \<and> (\<forall>x a v w. (\<forall>y\<in>fv a - {x}. v y = w y) \<longrightarrow> slam S x a v = slam S x a w)"
definition "pIRR_F S \<longleftrightarrow> (\<forall>\<Gamma> c. sG S \<Gamma> c \<longrightarrow> c \<notin> \<Gamma>)"
definition "pASYM_P S \<longleftrightarrow> (\<forall>p q. pPG S p q \<longrightarrow> \<not> pPG S q p)"
definition "pTRANS_P S \<longleftrightarrow> (\<forall>p q r. pPG S p q \<and> pPG S q r \<longrightarrow> pPG S p r)"
definition "pTRANS_CUT S \<longleftrightarrow> (\<forall>\<Gamma> \<Delta> H q. sG S \<Gamma> q \<and> \<Delta> \<subseteq> \<Gamma> \<and> (\<forall>p\<in>\<Delta>. sG S (H p) p)
       \<longrightarrow> sG S ((\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)) q)"
definition "pAMALG_INF S \<longleftrightarrow> (\<forall>F p. F \<noteq> {} \<and> (\<forall>\<Gamma>\<in>F. sG S \<Gamma> p) \<longrightarrow> sG S (\<Union>F) p)"
definition "pCL_PROP S \<longleftrightarrow> (\<forall>p q. (sT S (sneg S p) \<longleftrightarrow> \<not> sT S p)
     \<and> (sT S (sconj S p q) \<longleftrightarrow> sT S p \<and> sT S q) \<and> (sT S (sdisj S p q) \<longleftrightarrow> sT S p \<or> sT S q))"
definition "pCL_QUANT S \<longleftrightarrow> (\<forall>f. (sT S (sexq S f) \<longleftrightarrow> (\<exists>a. sT S (sapp S f a)))
     \<and> (sT S (sallq S f) \<longleftrightarrow> (\<forall>a. sT S (sapp S f a)))
     \<and> (sT S (sbig S f) \<longleftrightarrow> (\<forall>q\<in>psat S f. sT S q)))"
definition "pTS_FULL S \<longleftrightarrow> (\<forall>p. sT S (strr S p) \<longleftrightarrow> sT S p)"
definition "pCONJ_BIN S \<longleftrightarrow> (\<forall>p q. sT S p \<and> sT S q \<longrightarrow> sG S {p, q} (sconj S p q))"
definition "pCONJ_GRAIN S \<longleftrightarrow>
     (\<forall>p q p' q'. sT S (sconj S p q) \<and> sconj S p q = sconj S p' q' \<longrightarrow> {p, q} = {p', q'})
   \<and> (\<forall>f g. sadm S f \<and> sadm S g \<and> (\<forall>q\<in>psat S f. sT S q) \<and> (\<forall>q\<in>psat S g. sT S q)
          \<and> sbig S f = sbig S g \<longrightarrow> psat S f = psat S g)"
definition "pDISJ_ONE S \<longleftrightarrow> (\<forall>p q. (sT S p \<longrightarrow> sG S {p} (sdisj S p q)) \<and> (sT S q \<longrightarrow> sG S {q} (sdisj S p q)))"
definition "pDISJ_BOTH S \<longleftrightarrow> (\<forall>p q. sT S p \<and> sT S q \<longrightarrow> sG S {p, q} (sdisj S p q))"
definition "pNEG_DN S \<longleftrightarrow> (\<forall>p. sT S p \<longrightarrow> sG S {p} (sneg S (sneg S p)))"
definition "pNEG_DM S \<longleftrightarrow> (\<forall>p q. (sT S (sneg S p) \<longrightarrow> sG S {sneg S p} (sneg S (sconj S p q)))
     \<and> (sT S (sneg S q) \<longrightarrow> sG S {sneg S q} (sneg S (sconj S p q)))
     \<and> (sT S (sneg S p) \<and> sT S (sneg S q) \<longrightarrow> sG S {sneg S p, sneg S q} (sneg S (sdisj S p q))))"
definition "pEX_FULL S \<longleftrightarrow> (\<forall>f a. sadm S f \<and> sT S (sapp S f a) \<longrightarrow> sG S {sapp S f a} (sexq S f))"
definition "pALL_INST S \<longleftrightarrow> (\<forall>f. sadm S f \<and> (\<forall>a. sT S (sapp S f a)) \<longrightarrow> sG S (pinst S f) (sallq S f))"
definition "pTR_FULL S \<longleftrightarrow> (\<forall>p. sT S p \<longrightarrow> sG S {p} (strr S p))"
definition "pTR_NEG S \<longleftrightarrow> (\<forall>p. sT S (sneg S p) \<longrightarrow> sG S {sneg S p} (sneg S (strr S p)))"
definition "pEMPTY_NONE S \<longleftrightarrow> (\<forall>p. \<not> sG S {} p)"
definition "pC3d S \<longleftrightarrow> (\<forall>f. sadm S f \<longleftrightarrow> (\<exists>x a v. f = slam S x a v))"
definition "pBETA_ID S \<longleftrightarrow> (\<forall>x a v p. sapp S (slam S x a v) p = sden S (v(x:=p)) a)"
definition "pN1 S \<longleftrightarrow> (\<exists>\<Gamma> p. sG S \<Gamma> p)"
definition "pN2 S \<longleftrightarrow> pN1 S \<and> (\<exists>a b c. distinct [a, b, c] \<and> sT S a \<and> sT S b \<and> sT S c)"
definition "pN4_pairs S \<longleftrightarrow> (\<exists>x y. ((\<exists>p. x = p \<and> y = sneg S (sneg S p))
       \<or> (\<exists>p q. x = sconj S p q \<and> y = sconj S q p) \<or> (\<exists>p. x = p \<and> y = sconj S p p)
       \<or> (\<exists>p q. x = sdisj S p q \<and> y = sdisj S q p))
     \<and> x \<noteq> y \<and> {\<Gamma>. sG S \<Gamma> x} \<noteq> {\<Gamma>. sG S \<Gamma> y})"
definition "pN5_chain S \<longleftrightarrow> (\<exists>x0 x1 x2 x3. distinct [x0, x1, x2, x3]
     \<and> pPG S x0 x1 \<and> pPG S x1 x2 \<and> pPG S x2 x3)"

section \<open>Fidelity: at S0 each restated principle is the original\<close>

lemma PG_S0: "pPG S0 = PG" by (rule ext)+ (simp add: pPG_def PG_def)
lemma sat_S0: "psat S0 = sat" by (rule ext) (simp add: psat_def sat_def)
lemma inst_S0: "pinst S0 = inst" by (rule ext) (simp add: pinst_def inst_def)

lemmas S0_simps = PG_S0 sat_S0 inst_S0 sden_S0

lemma fidelity:
  "pFACT S0 = FACT" "pLAM_CORE S0 = LAM_CORE" "pIRR_F S0 = IRR_F" "pASYM_P S0 = ASYM_P"
  "pTRANS_P S0 = TRANS_P" "pTRANS_CUT S0 = TRANS_CUT" "pAMALG_INF S0 = AMALG_INF"
  "pCL_PROP S0 = CL_PROP" "pCL_QUANT S0 = CL_QUANT" "pTS_FULL S0 = TS_FULL"
  "pCONJ_BIN S0 = CONJ_BIN" "pCONJ_GRAIN S0 = CONJ_GRAIN" "pDISJ_ONE S0 = DISJ_ONE"
  "pDISJ_BOTH S0 = DISJ_BOTH" "pNEG_DN S0 = NEG_DN" "pNEG_DM S0 = NEG_DM"
  "pEX_FULL S0 = EX_FULL" "pALL_INST S0 = ALL_INST" "pTR_FULL S0 = TR_FULL"
  "pTR_NEG S0 = TR_NEG" "pEMPTY_NONE S0 = EMPTY_NONE" "pC3d S0 = C3d" "pBETA_ID S0 = BETA_ID"
  "pN1 S0 = N1" "pN2 S0 = N2" "pN5_chain S0 = N5_chain" "pN4_pairs S0 = N4_pairs"
  by (simp_all only: pFACT_def FACT_def pLAM_CORE_def LAM_CORE_def pIRR_F_def IRR_F_def
      pASYM_P_def ASYM_P_def pTRANS_P_def TRANS_P_def pTRANS_CUT_def TRANS_CUT_def
      pAMALG_INF_def AMALG_INF_def pCL_PROP_def CL_PROP_def pCL_QUANT_def CL_QUANT_def
      pTS_FULL_def TS_FULL_def pCONJ_BIN_def CONJ_BIN_def pCONJ_GRAIN_def CONJ_GRAIN_def
      pDISJ_ONE_def DISJ_ONE_def pDISJ_BOTH_def DISJ_BOTH_def pNEG_DN_def NEG_DN_def
      pNEG_DM_def NEG_DM_def pEX_FULL_def EX_FULL_def pALL_INST_def ALL_INST_def
      pTR_FULL_def TR_FULL_def pTR_NEG_def TR_NEG_def pEMPTY_NONE_def EMPTY_NONE_def
      pC3d_def C3d_def pBETA_ID_def BETA_ID_def pN1_def N1_def pN2_def N2_def pN5_chain_def N5_chain_def pN4_pairs_def N4_pairs_def
      S0_simps S0_sel)

section \<open>M1: a term model with hyperintensional application\<close>

text \<open>
  Propositions are closed terms. Application of a propositional function to a proposition
  is a term constructor of its own (PApp), so app f p is never identical to the result of
  substituting p (BETA_ID fails) and it depends on nothing. This is the escape Fritz 2020
  (sec. 6) suggests for Kr\"amer's puzzle; M1 makes it precise and adds ground for
  universals, transitivity and impredicative comprehension (C3d).
\<close>

datatype ptm = PAtom nat | PNeg ptm | PConj ptm ptm | PDisj ptm ptm | PTr ptm
             | PEx pf | PAll pf | PBig pf | PApp pf ptm
     and pf = PLam nat fm "nat \<Rightarrow> ptm"

text \<open>Truth. Formulas are evaluated with a Boolean environment; propositional quantifiers
  range over truth values, which matches quantification over terms because every truth
  value is the value of some term (eval_surj).\<close>

primrec evalfm :: "(nat \<Rightarrow> bool) \<Rightarrow> fm \<Rightarrow> bool" where
  "evalfm e (Var n) = e n"
| "evalfm e (Cst n) = (n = 0)"
| "evalfm e (Neg a) = (\<not> evalfm e a)"
| "evalfm e (Conj a b) = (evalfm e a \<and> evalfm e b)"
| "evalfm e (Disj a b) = (evalfm e a \<or> evalfm e b)"
| "evalfm e (Tr a) = evalfm e a"
| "evalfm e (Ex x a) = (\<exists>b. evalfm (e(x:=b)) a)"
| "evalfm e (All x a) = (\<forall>b. evalfm (e(x:=b)) a)"
| "evalfm e (BigC x a) = (\<forall>b. evalfm (e(x:=b)) a \<longrightarrow> b)"

primrec eval :: "ptm \<Rightarrow> bool" and evalq :: "pf \<Rightarrow> bool \<Rightarrow> bool" where
  "eval (PAtom n) = (n = 0)"
| "eval (PNeg p) = (\<not> eval p)"
| "eval (PConj p q) = (eval p \<and> eval q)"
| "eval (PDisj p q) = (eval p \<or> eval q)"
| "eval (PTr p) = eval p"
| "eval (PEx f) = (\<exists>b. evalq f b)"
| "eval (PAll f) = (\<forall>b. evalq f b)"
| "eval (PBig f) = (\<forall>b. evalq f b \<longrightarrow> b)"
| "eval (PApp f p) = evalq f (eval p)"
| "evalq (PLam x a v) = (\<lambda>b. evalfm ((eval \<circ> v)(x:=b)) a)"

lemma eval_surj: "eval (if b then PAtom 0 else PAtom 1) = b"
  by simp

lemma q_ex: "(\<exists>b. evalq f b) \<longleftrightarrow> (\<exists>p. evalq f (eval p))" by (metis eval_surj)
lemma q_all: "(\<forall>b. evalq f b) \<longleftrightarrow> (\<forall>p. evalq f (eval p))" by (metis eval_surj)
lemma q_big: "(\<forall>b. evalq f b \<longrightarrow> b) \<longleftrightarrow> (\<forall>p. evalq f (eval p) \<longrightarrow> eval p)"
  by (metis eval_surj)

lemma evalfm_fv: "(\<forall>y\<in>fv a. e y = e' y) \<Longrightarrow> evalfm e a = evalfm e' a"
proof (induct a arbitrary: e e')
  case (Ex x a)
  have "\<And>b. evalfm (e(x:=b)) a = evalfm (e'(x:=b)) a"
    by (rule Ex.hyps) (use Ex.prems in auto)
  then show ?case by simp
next
  case (All x a)
  have "\<And>b. evalfm (e(x:=b)) a = evalfm (e'(x:=b)) a"
    by (rule All.hyps) (use All.prems in auto)
  then show ?case by simp
next
  case (BigC x a)
  have "\<And>b. evalfm (e(x:=b)) a = evalfm (e'(x:=b)) a"
    by (rule BigC.hyps) (use BigC.prems in auto)
  then show ?case by simp
next
  case (Neg a)
  have "evalfm e a = evalfm e' a" by (rule Neg.hyps) (use Neg.prems in auto)
  then show ?case by simp
next
  case (Tr a)
  have "evalfm e a = evalfm e' a" by (rule Tr.hyps) (use Tr.prems in auto)
  then show ?case by simp
next
  case (Conj a b)
  have "evalfm e a = evalfm e' a" by (rule Conj.hyps(1)) (use Conj.prems in auto)
  moreover have "evalfm e b = evalfm e' b" by (rule Conj.hyps(2)) (use Conj.prems in auto)
  ultimately show ?case by simp
next
  case (Disj a b)
  have "evalfm e a = evalfm e' a" by (rule Disj.hyps(1)) (use Disj.prems in auto)
  moreover have "evalfm e b = evalfm e' b" by (rule Disj.hyps(2)) (use Disj.prems in auto)
  ultimately show ?case by simp
qed simp_all

text \<open>Lambda abstraction forgets the environment outside the free variables, so
  LAM_CORE's extensionality clause holds; admissible functions are exactly the
  lambda terms (C3d).\<close>

definition mlam :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> ptm) \<Rightarrow> pf" where
  "mlam x a v = PLam x a (\<lambda>n. if n \<in> fv a - {x} then v n else PAtom 0)"

definition madm :: "pf \<Rightarrow> bool" where
  "madm f \<longleftrightarrow> (\<exists>x a v. f = mlam x a v)"

text \<open>Dependence. imm p q says that p is among the propositions q is immediately
  about, read with Fine's polarity clauses: a negated conjunction depends on the negated
  conjuncts, and so on. An instance app f a is an immediate dependee of each quantification
  over f, and depends on nothing itself. This is what blocks the regress of Kr\"amer's and
  Fritz's puzzles: exq f may be the argument of app f, but app f (exq f) does not depend
  on it.\<close>

inductive imm :: "ptm \<Rightarrow> ptm \<Rightarrow> bool" where
  "imm p (PConj p q)" | "imm q (PConj p q)"
| "imm p (PDisj p q)" | "imm q (PDisj p q)"
| "imm p (PTr p)" | "imm p (PNeg (PNeg p))"
| "imm (PNeg p) (PNeg (PConj p q))" | "imm (PNeg q) (PNeg (PConj p q))"
| "imm (PNeg p) (PNeg (PDisj p q))" | "imm (PNeg q) (PNeg (PDisj p q))"
| "imm (PNeg p) (PNeg (PTr p))"
| "imm (PApp f a) (PEx f)" | "imm (PApp f a) (PAll f)" | "imm (PApp f a) (PBig f)"

primrec rank :: "ptm \<Rightarrow> nat" where
  "rank (PAtom n) = 0"
| "rank (PNeg p) = Suc (rank p)"
| "rank (PConj p q) = Suc (max (rank p) (rank q))"
| "rank (PDisj p q) = Suc (max (rank p) (rank q))"
| "rank (PTr p) = Suc (rank p)"
| "rank (PEx f) = 1"
| "rank (PAll f) = 1"
| "rank (PBig f) = 1"
| "rank (PApp f p) = 0"

abbreviation cst :: "ptm \<Rightarrow> ptm \<Rightarrow> bool" where "cst \<equiv> imm\<^sup>+\<^sup>+"

lemma imm_rank: "imm p q \<Longrightarrow> rank p < rank q"
  by (induct rule: imm.induct) auto

lemma cst_rank: "cst p q \<Longrightarrow> rank p < rank q"
  by (induct rule: tranclp.induct) (auto dest: imm_rank)

lemma cst_imm: "imm p q \<Longrightarrow> cst p q"
  by (rule tranclp.r_into_trancl)

text \<open>Ground. gr is the least relation closed under the introduction principles of the
  package, transitivity (cut) and amalgamation, defined impredicatively as the
  intersection of all closed relations. So every grounding fact of M1 is one the package
  itself demands; nothing is grounded by stipulation.\<close>

definition closed :: "(ptm set \<Rightarrow> ptm \<Rightarrow> bool) \<Rightarrow> bool" where
  "closed R \<longleftrightarrow>
     (\<forall>p q. eval p \<and> eval q \<longrightarrow> R {p, q} (PConj p q))
   \<and> (\<forall>p q. eval p \<longrightarrow> R {p} (PDisj p q))
   \<and> (\<forall>p q. eval q \<longrightarrow> R {q} (PDisj p q))
   \<and> (\<forall>p q. eval p \<and> eval q \<longrightarrow> R {p, q} (PDisj p q))
   \<and> (\<forall>p. eval p \<longrightarrow> R {p} (PNeg (PNeg p)))
   \<and> (\<forall>p q. eval (PNeg p) \<longrightarrow> R {PNeg p} (PNeg (PConj p q)))
   \<and> (\<forall>p q. eval (PNeg q) \<longrightarrow> R {PNeg q} (PNeg (PConj p q)))
   \<and> (\<forall>p q. eval (PNeg p) \<and> eval (PNeg q) \<longrightarrow> R {PNeg p, PNeg q} (PNeg (PDisj p q)))
   \<and> (\<forall>f a. madm f \<and> eval (PApp f a) \<longrightarrow> R {PApp f a} (PEx f))
   \<and> (\<forall>f. madm f \<and> (\<forall>a. eval (PApp f a)) \<longrightarrow> R (range (PApp f)) (PAll f))
   \<and> (\<forall>p. eval p \<longrightarrow> R {p} (PTr p))
   \<and> (\<forall>p. eval (PNeg p) \<longrightarrow> R {PNeg p} (PNeg (PTr p)))
   \<and> (\<forall>\<Gamma> \<Delta> H q. R \<Gamma> q \<and> \<Delta> \<subseteq> \<Gamma> \<and> (\<forall>p\<in>\<Delta>. R (H p) p) \<longrightarrow> R ((\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)) q)
   \<and> (\<forall>F p. F \<noteq> {} \<and> (\<forall>\<Gamma>\<in>F. R \<Gamma> p) \<longrightarrow> R (\<Union>F) p)"

definition gr :: "ptm set \<Rightarrow> ptm \<Rightarrow> bool" where
  "gr \<Gamma> q \<longleftrightarrow> (\<forall>R. closed R \<longrightarrow> R \<Gamma> q)"

lemmas closedD =
  closed_def[THEN iffD1, THEN conjunct1]
  closed_def[THEN iffD1, THEN conjunct2, THEN conjunct1]
  closed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  closed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  closed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  closed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  closed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  closed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  closed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  closed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  closed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  closed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  closed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  closed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]

lemma g_conj: "eval p \<Longrightarrow> eval q \<Longrightarrow> gr {p, q} (PConj p q)"
  unfolding gr_def by (blast dest: closedD(1))
lemma g_disjL: "eval p \<Longrightarrow> gr {p} (PDisj p q)"
  unfolding gr_def by (blast dest: closedD(2))
lemma g_disjR: "eval q \<Longrightarrow> gr {q} (PDisj p q)"
  unfolding gr_def by (blast dest: closedD(3))
lemma g_disjB: "eval p \<Longrightarrow> eval q \<Longrightarrow> gr {p, q} (PDisj p q)"
  unfolding gr_def by (blast dest: closedD(4))
lemma g_dn: "eval p \<Longrightarrow> gr {p} (PNeg (PNeg p))"
  unfolding gr_def by (blast dest: closedD(5))
lemma g_dmL: "eval (PNeg p) \<Longrightarrow> gr {PNeg p} (PNeg (PConj p q))"
  unfolding gr_def by (blast dest: closedD(6))
lemma g_dmR: "eval (PNeg q) \<Longrightarrow> gr {PNeg q} (PNeg (PConj p q))"
  unfolding gr_def by (blast dest: closedD(7))
lemma g_dmD: "eval (PNeg p) \<Longrightarrow> eval (PNeg q) \<Longrightarrow> gr {PNeg p, PNeg q} (PNeg (PDisj p q))"
  unfolding gr_def by (blast dest: closedD(8))
lemma g_ex: "madm f \<Longrightarrow> eval (PApp f a) \<Longrightarrow> gr {PApp f a} (PEx f)"
  unfolding gr_def by (blast dest: closedD(9))
lemma g_all: "madm f \<Longrightarrow> (\<forall>a. eval (PApp f a)) \<Longrightarrow> gr (range (PApp f)) (PAll f)"
  unfolding gr_def by (blast dest: closedD(10))
lemma g_tr: "eval p \<Longrightarrow> gr {p} (PTr p)"
  unfolding gr_def by (blast dest: closedD(11))
lemma g_trneg: "eval (PNeg p) \<Longrightarrow> gr {PNeg p} (PNeg (PTr p))"
  unfolding gr_def by (blast dest: closedD(12))

lemma g_cut:
  assumes "gr \<Gamma> q" "\<Delta> \<subseteq> \<Gamma>" "\<forall>p\<in>\<Delta>. gr (H p) p"
  shows "gr ((\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)) q"
  unfolding gr_def
proof (intro allI impI)
  fix R assume c: "closed R"
  with assms have "R \<Gamma> q" "\<forall>p\<in>\<Delta>. R (H p) p" unfolding gr_def by blast+
  with closedD(13)[OF c] assms(2) show "R ((\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)) q" by blast
qed

lemma g_amalg:
  assumes "F \<noteq> {}" "\<forall>\<Gamma>\<in>F. gr \<Gamma> p"
  shows "gr (\<Union>F) p"
  unfolding gr_def
proof (intro allI impI)
  fix R assume c: "closed R"
  with assms have "\<forall>\<Gamma>\<in>F. R \<Gamma> p" unfolding gr_def by blast
  with closedD(14)[OF c] assms(1) show "R (\<Union>F) p" by blast
qed

text \<open>Soundness of gr: every ground is a non-empty set of truths on which the grounded
  truth (transitively) depends.\<close>

definition ginv :: "ptm set \<Rightarrow> ptm \<Rightarrow> bool" where
  "ginv \<Gamma> q \<longleftrightarrow> \<Gamma> \<noteq> {} \<and> eval q \<and> (\<forall>p\<in>\<Gamma>. eval p \<and> cst p q)"

lemma ginv_cut:
  assumes "ginv \<Gamma> q" "\<Delta> \<subseteq> \<Gamma>" "\<forall>p\<in>\<Delta>. ginv (H p) p"
  shows "ginv ((\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)) q"
proof -
  have ne: "(\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p) \<noteq> {}"
  proof (cases "\<Gamma> - \<Delta> = {}")
    case True
    with assms(2) have "\<Delta> = \<Gamma>" by blast
    with assms(1) obtain p where p: "p \<in> \<Delta>" unfolding ginv_def by blast
    with assms(3) have "ginv (H p) p" by blast
    then obtain r where "r \<in> H p" unfolding ginv_def by blast
    with p have "r \<in> (\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)" by (intro UnI2 UN_I)
    then show ?thesis by (intro notI) simp
  next
    case False
    then obtain r where "r \<in> \<Gamma> - \<Delta>" by blast
    then have "r \<in> (\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)" by (rule UnI1)
    then show ?thesis by (intro notI) simp
  qed
  have all: "\<forall>r\<in>(\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p). eval r \<and> cst r q"
  proof
    fix r assume "r \<in> (\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)"
    then show "eval r \<and> cst r q"
    proof
      assume "r \<in> \<Gamma> - \<Delta>"
      then have "r \<in> \<Gamma>" by simp
      with assms(1) show ?thesis unfolding ginv_def by blast
    next
      assume "r \<in> (\<Union>p\<in>\<Delta>. H p)"
      then obtain p where p: "p \<in> \<Delta>" "r \<in> H p" by (rule UN_E)
      from assms(3) p(1) have "ginv (H p) p" by (rule bspec)
      with p(2) have r: "eval r" "cst r p" unfolding ginv_def by blast+
      from p(1) assms(2) have "p \<in> \<Gamma>" by (rule subsetD[rotated])
      with assms(1) have "cst p q" unfolding ginv_def by blast
      with r show ?thesis by (meson tranclp_trans)
    qed
  qed
  from assms(1) have "eval q" unfolding ginv_def by blast
  with ne all show ?thesis unfolding ginv_def by (intro conjI)
qed

lemma ginv_amalg: "F \<noteq> {} \<Longrightarrow> \<forall>\<Gamma>\<in>F. ginv \<Gamma> p \<Longrightarrow> ginv (\<Union>F) p"
  unfolding ginv_def by blast

lemma closed_ginv: "closed ginv"
proof -
  note d = ginv_def cst_imm imm.intros
  have c1: "\<forall>p q. eval p \<and> eval q \<longrightarrow> ginv {p, q} (PConj p q)" by (simp add: d)
  have c2: "\<forall>p q. eval p \<longrightarrow> ginv {p} (PDisj p q)" by (simp add: d)
  have c3: "\<forall>p q. eval q \<longrightarrow> ginv {q} (PDisj p q)" by (simp add: d)
  have c4: "\<forall>p q. eval p \<and> eval q \<longrightarrow> ginv {p, q} (PDisj p q)" by (simp add: d)
  have c5: "\<forall>p. eval p \<longrightarrow> ginv {p} (PNeg (PNeg p))" by (simp add: d)
  have c6: "\<forall>p q. eval (PNeg p) \<longrightarrow> ginv {PNeg p} (PNeg (PConj p q))" by (simp add: d)
  have c7: "\<forall>p q. eval (PNeg q) \<longrightarrow> ginv {PNeg q} (PNeg (PConj p q))" by (simp add: d)
  have c8: "\<forall>p q. eval (PNeg p) \<and> eval (PNeg q) \<longrightarrow> ginv {PNeg p, PNeg q} (PNeg (PDisj p q))"
    by (simp add: d)
  have c9: "\<forall>f a. madm f \<and> eval (PApp f a) \<longrightarrow> ginv {PApp f a} (PEx f)"
    by (auto simp: d q_ex)
  have c10: "\<forall>f. madm f \<and> (\<forall>a. eval (PApp f a)) \<longrightarrow> ginv (range (PApp f)) (PAll f)"
    by (auto simp: d q_all)
  have c11: "\<forall>p. eval p \<longrightarrow> ginv {p} (PTr p)" by (simp add: d)
  have c12: "\<forall>p. eval (PNeg p) \<longrightarrow> ginv {PNeg p} (PNeg (PTr p))" by (simp add: d)
  have c13: "\<forall>\<Gamma> \<Delta> H q. ginv \<Gamma> q \<and> \<Delta> \<subseteq> \<Gamma> \<and> (\<forall>p\<in>\<Delta>. ginv (H p) p)
      \<longrightarrow> ginv ((\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)) q" using ginv_cut by blast
  have c14: "\<forall>F p. F \<noteq> {} \<and> (\<forall>\<Gamma>\<in>F. ginv \<Gamma> p) \<longrightarrow> ginv (\<Union>F) p" using ginv_amalg by blast
  show ?thesis unfolding closed_def
    by (intro conjI; fact c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14)
qed

lemma gr_ginv: "gr \<Gamma> q \<Longrightarrow> ginv \<Gamma> q"
  using closed_ginv unfolding gr_def by blast

lemma gr_sound: "gr \<Gamma> q \<Longrightarrow> \<Gamma> \<noteq> {} \<and> eval q \<and> (\<forall>p\<in>\<Gamma>. eval p \<and> cst p q)"
  using gr_ginv unfolding ginv_def by blast

definition M1 :: "(ptm, pf) gstr" where
  "M1 = \<lparr>sT = eval, sG = gr, satom = PAtom, sneg = PNeg, sconj = PConj, sdisj = PDisj,
         strr = PTr, sapp = PApp, sexq = PEx, sallq = PAll, sbig = PBig, slam = mlam,
         sadm = madm\<rparr>"

lemma M1_sel [simp]:
  "sT M1 = eval" "sG M1 = gr" "satom M1 = PAtom" "sneg M1 = PNeg" "sconj M1 = PConj"
  "sdisj M1 = PDisj" "strr M1 = PTr" "sapp M1 = PApp" "sexq M1 = PEx" "sallq M1 = PAll"
  "sbig M1 = PBig" "slam M1 = mlam" "sadm M1 = madm"
  by (simp_all add: M1_def)

lemma eval_mlam: "evalq (mlam x a v) b = evalfm ((eval \<circ> v)(x:=b)) a"
  unfolding mlam_def by simp (rule evalfm_fv, auto)

lemma comp_upd: "(eval \<circ> v)(x := eval p) = eval \<circ> (v(x := p))"
  by (rule ext) simp



lemma eval_sden: "eval (sden M1 v a) = evalfm (eval \<circ> v) a"
proof (induct a arbitrary: v)
  case (Ex x a) show ?case by (simp add: eval_mlam comp_def)
next
  case (All x a) show ?case by (simp add: eval_mlam comp_def)
next
  case (BigC x a) show ?case by (simp add: eval_mlam comp_def)
qed simp_all

lemma PG_M1: "pPG M1 p q \<Longrightarrow> eval p \<and> eval q \<and> cst p q"
  unfolding pPG_def by (auto dest: gr_sound)

section \<open>The certificate\<close>

lemma M1_FACT: "pFACT M1" unfolding pFACT_def M1_sel by (blast dest: gr_sound)

lemma M1_LAM_CORE: "pLAM_CORE M1" unfolding pLAM_CORE_def
proof (intro conjI allI impI)
  fix x a v p
  show "sT M1 (sapp M1 (slam M1 x a v) p) = sT M1 (sden M1 (v(x := p)) a)"
    by (simp add: eval_mlam eval_sden comp_upd)
next
  fix x a and v w :: "nat \<Rightarrow> ptm" assume "\<forall>y\<in>fv a - {x}. v y = w y"
  then show "slam M1 x a v = slam M1 x a w" unfolding M1_sel mlam_def by (simp cong: if_cong)
qed

lemma M1_C3d: "pC3d M1" unfolding pC3d_def by (simp add: madm_def)
lemma M1_CL_PROP: "pCL_PROP M1" unfolding pCL_PROP_def by simp
lemma M1_CL_QUANT: "pCL_QUANT M1" unfolding pCL_QUANT_def psat_def by (simp add: q_ex q_all q_big)
lemma M1_TS_FULL: "pTS_FULL M1" unfolding pTS_FULL_def by simp

lemma M1_IRR_F: "pIRR_F M1" unfolding pIRR_F_def M1_sel
proof (intro allI impI notI)
  fix \<Gamma> c assume "gr \<Gamma> c" "c \<in> \<Gamma>"
  then have "cst c c" by (blast dest: gr_sound)
  then show False by (auto dest: cst_rank)
qed

lemma M1_ASYM_P: "pASYM_P M1" unfolding pASYM_P_def
proof (intro allI impI notI)
  fix p q assume "pPG M1 p q" "pPG M1 q p"
  then have "rank p < rank q" "rank q < rank p" by (auto dest!: PG_M1 cst_rank)
  then show False by simp
qed

lemma M1_TRANS_CUT: "pTRANS_CUT M1" unfolding pTRANS_CUT_def M1_sel
proof (intro allI impI, elim conjE)
  fix \<Gamma> \<Delta> H q assume "gr \<Gamma> q" "\<Delta> \<subseteq> \<Gamma>" "\<forall>p\<in>\<Delta>. gr (H p) p"
  then show "gr ((\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)) q" by (rule g_cut)
qed

lemma M1_TRANS_P: "pTRANS_P M1" unfolding pTRANS_P_def pPG_def M1_sel
proof (intro allI impI, elim conjE exE)
  fix p q r \<Gamma> \<Delta> assume a: "p \<in> \<Gamma>" "gr \<Gamma> q" "q \<in> \<Delta>" "gr \<Delta> r"
  from a(3) have sub: "{q} \<subseteq> \<Delta>" by simp
  from a(2) have h: "\<forall>x\<in>{q}. gr \<Gamma> x" by simp
  have g: "gr ((\<Delta> - {q}) \<union> (\<Union>x\<in>{q}. \<Gamma>)) r" by (rule g_cut[OF a(4) sub h])
  from a(1) have "p \<in> (\<Delta> - {q}) \<union> (\<Union>x\<in>{q}. \<Gamma>)" by simp
  with g show "\<exists>\<Gamma>. p \<in> \<Gamma> \<and> gr \<Gamma> r" by (intro exI conjI)
qed

lemma M1_AMALG_INF: "pAMALG_INF M1" unfolding pAMALG_INF_def M1_sel
proof (intro allI impI, elim conjE)
  fix F p assume "F \<noteq> {}" "\<forall>\<Gamma>\<in>F. gr \<Gamma> p"
  then show "gr (\<Union>F) p" by (rule g_amalg)
qed

lemma M1_EMPTY_NONE: "pEMPTY_NONE M1" unfolding pEMPTY_NONE_def M1_sel by (blast dest: gr_sound)
lemma M1_CONJ_BIN: "pCONJ_BIN M1" unfolding pCONJ_BIN_def M1_sel by (blast intro: g_conj)
lemma M1_CONJ_GRAIN: "pCONJ_GRAIN M1" unfolding pCONJ_GRAIN_def M1_sel by simp
lemma M1_DISJ_ONE: "pDISJ_ONE M1" unfolding pDISJ_ONE_def M1_sel by (blast intro: g_disjL g_disjR)
lemma M1_DISJ_BOTH: "pDISJ_BOTH M1" unfolding pDISJ_BOTH_def M1_sel by (blast intro: g_disjB)
lemma M1_NEG_DN: "pNEG_DN M1" unfolding pNEG_DN_def M1_sel by (blast intro: g_dn)
lemma M1_NEG_DM: "pNEG_DM M1" unfolding pNEG_DM_def M1_sel by (blast intro: g_dmL g_dmR g_dmD)
lemma M1_EX_FULL: "pEX_FULL M1" unfolding pEX_FULL_def M1_sel by (blast intro: g_ex)
lemma M1_ALL_INST: "pALL_INST M1" unfolding pALL_INST_def pinst_def M1_sel by (blast intro: g_all)
lemma M1_TR_FULL: "pTR_FULL M1" unfolding pTR_FULL_def M1_sel by (blast intro: g_tr)
lemma M1_TR_NEG: "pTR_NEG M1" unfolding pTR_NEG_def M1_sel by (blast intro: g_trneg)

lemma M1_chain: "gr {PAtom 0} (PTr (PAtom 0))" "gr {PTr (PAtom 0)} (PTr (PTr (PAtom 0)))"
  "gr {PTr (PTr (PAtom 0))} (PTr (PTr (PTr (PAtom 0))))" by (simp_all add: g_tr)

lemma M1_N1: "pN1 M1" unfolding pN1_def M1_sel using M1_chain(1) by blast

lemma M1_N2: "pN2 M1"
proof -
  have "distinct [PAtom 0, PTr (PAtom 0), PTr (PTr (PAtom 0))]
      \<and> eval (PAtom 0) \<and> eval (PTr (PAtom 0)) \<and> eval (PTr (PTr (PAtom 0)))" by simp
  with M1_N1 show ?thesis unfolding pN2_def M1_sel by blast
qed

lemma M1_N5_chain: "pN5_chain M1"
proof -
  have "distinct [PAtom 0, PTr (PAtom 0), PTr (PTr (PAtom 0)), PTr (PTr (PTr (PAtom 0)))]" by simp
  moreover have "pPG M1 (PAtom 0) (PTr (PAtom 0))" "pPG M1 (PTr (PAtom 0)) (PTr (PTr (PAtom 0)))"
    "pPG M1 (PTr (PTr (PAtom 0))) (PTr (PTr (PTr (PAtom 0))))"
    unfolding pPG_def M1_sel using M1_chain by blast+
  ultimately show ?thesis unfolding pN5_chain_def by blast
qed

text \<open>N3 (registry, nontriviality; no formal statement): every introduction entry of the
  package has an instance whose antecedent holds, with pairwise distinct relata, and whose
  grounded proposition is not among its grounds. One instance per entry.\<close>

definition "f_em1 = mlam 0 (Disj (Var 0) (Neg (Var 0))) (\<lambda>_. PAtom 0)"
definition "f_id1 = mlam 0 (Var 0) (\<lambda>_. PAtom 0)"

lemma M1_N3:
  shows N3_CONJ_BIN: "eval (PAtom 0) \<and> eval (PTr (PAtom 0)) \<and> distinct [PAtom 0, PTr (PAtom 0), PConj (PAtom 0) (PTr (PAtom 0))]
      \<and> gr {PAtom 0, PTr (PAtom 0)} (PConj (PAtom 0) (PTr (PAtom 0)))"
    and N3_DISJ_ONE: "eval (PAtom 0) \<and> distinct [PAtom 0, PAtom 1, PDisj (PAtom 0) (PAtom 1)]
      \<and> gr {PAtom 0} (PDisj (PAtom 0) (PAtom 1))"
    and N3_DISJ_BOTH: "eval (PAtom 0) \<and> eval (PTr (PAtom 0)) \<and> distinct [PAtom 0, PTr (PAtom 0), PDisj (PAtom 0) (PTr (PAtom 0))]
      \<and> gr {PAtom 0, PTr (PAtom 0)} (PDisj (PAtom 0) (PTr (PAtom 0)))"
    and N3_NEG_DN: "eval (PAtom 0) \<and> PAtom 0 \<noteq> PNeg (PNeg (PAtom 0)) \<and> gr {PAtom 0} (PNeg (PNeg (PAtom 0)))"
    and N3_NEG_DM: "eval (PNeg (PAtom 1)) \<and> eval (PNeg (PAtom 2))
      \<and> distinct [PNeg (PAtom 1), PNeg (PAtom 2), PNeg (PConj (PAtom 1) (PAtom 2)), PNeg (PDisj (PAtom 1) (PAtom 2))]
      \<and> gr {PNeg (PAtom 1)} (PNeg (PConj (PAtom 1) (PAtom 2)))
      \<and> gr {PNeg (PAtom 2)} (PNeg (PConj (PAtom 1) (PAtom 2)))
      \<and> gr {PNeg (PAtom 1), PNeg (PAtom 2)} (PNeg (PDisj (PAtom 1) (PAtom 2)))"
    and N3_EX_FULL: "madm f_id1 \<and> eval (PApp f_id1 (PAtom 0)) \<and> PApp f_id1 (PAtom 0) \<noteq> PEx f_id1
      \<and> gr {PApp f_id1 (PAtom 0)} (PEx f_id1)"
    and N3_ALL_INST: "madm f_em1 \<and> (\<forall>a. eval (PApp f_em1 a)) \<and> PAll f_em1 \<notin> range (PApp f_em1)
      \<and> gr (range (PApp f_em1)) (PAll f_em1)"
    and N3_TR_FULL: "eval (PAtom 0) \<and> PAtom 0 \<noteq> PTr (PAtom 0) \<and> gr {PAtom 0} (PTr (PAtom 0))"
    and N3_TR_NEG: "eval (PNeg (PAtom 1)) \<and> PNeg (PAtom 1) \<noteq> PNeg (PTr (PAtom 1))
      \<and> gr {PNeg (PAtom 1)} (PNeg (PTr (PAtom 1)))"
proof -
  have id: "madm f_id1" "madm f_em1" unfolding madm_def f_id1_def f_em1_def by blast+
  have e1: "eval (PApp f_id1 (PAtom 0))" by (simp add: f_id1_def eval_mlam)
  have e2: "\<forall>a. eval (PApp f_em1 a)" by (simp add: f_em1_def eval_mlam)
  show "eval (PAtom 0) \<and> eval (PTr (PAtom 0)) \<and> distinct [PAtom 0, PTr (PAtom 0), PConj (PAtom 0) (PTr (PAtom 0))]
      \<and> gr {PAtom 0, PTr (PAtom 0)} (PConj (PAtom 0) (PTr (PAtom 0)))" by (simp add: g_conj)
  show "eval (PAtom 0) \<and> distinct [PAtom 0, PAtom 1, PDisj (PAtom 0) (PAtom 1)]
      \<and> gr {PAtom 0} (PDisj (PAtom 0) (PAtom 1))" by (simp add: g_disjL)
  show "eval (PAtom 0) \<and> eval (PTr (PAtom 0)) \<and> distinct [PAtom 0, PTr (PAtom 0), PDisj (PAtom 0) (PTr (PAtom 0))]
      \<and> gr {PAtom 0, PTr (PAtom 0)} (PDisj (PAtom 0) (PTr (PAtom 0)))" by (simp add: g_disjB)
  show "eval (PAtom 0) \<and> PAtom 0 \<noteq> PNeg (PNeg (PAtom 0)) \<and> gr {PAtom 0} (PNeg (PNeg (PAtom 0)))"
    by (simp add: g_dn)
  show "eval (PNeg (PAtom 1)) \<and> eval (PNeg (PAtom 2))
      \<and> distinct [PNeg (PAtom 1), PNeg (PAtom 2), PNeg (PConj (PAtom 1) (PAtom 2)), PNeg (PDisj (PAtom 1) (PAtom 2))]
      \<and> gr {PNeg (PAtom 1)} (PNeg (PConj (PAtom 1) (PAtom 2)))
      \<and> gr {PNeg (PAtom 2)} (PNeg (PConj (PAtom 1) (PAtom 2)))
      \<and> gr {PNeg (PAtom 1), PNeg (PAtom 2)} (PNeg (PDisj (PAtom 1) (PAtom 2)))"
    by (simp add: g_dmL g_dmR g_dmD)
  show "madm f_id1 \<and> eval (PApp f_id1 (PAtom 0)) \<and> PApp f_id1 (PAtom 0) \<noteq> PEx f_id1
      \<and> gr {PApp f_id1 (PAtom 0)} (PEx f_id1)" using id e1 by (simp add: g_ex)
  show "madm f_em1 \<and> (\<forall>a. eval (PApp f_em1 a)) \<and> PAll f_em1 \<notin> range (PApp f_em1)
      \<and> gr (range (PApp f_em1)) (PAll f_em1)" using id e2 by (auto intro: g_all)
  show "eval (PAtom 0) \<and> PAtom 0 \<noteq> PTr (PAtom 0) \<and> gr {PAtom 0} (PTr (PAtom 0))" by (simp add: g_tr)
  show "eval (PNeg (PAtom 1)) \<and> PNeg (PAtom 1) \<noteq> PNeg (PTr (PAtom 1))
      \<and> gr {PNeg (PAtom 1)} (PNeg (PTr (PAtom 1)))" by (simp add: g_trneg)
qed

text \<open>N4 (registry, with D8: M1 satisfies CL.PROP): the pair (p, neg (neg p)) at an atom.
  The atom has no full ground at all, since nothing it depends on exists; its double
  negation is grounded in it.\<close>

lemma atom_ungrounded: "\<not> gr \<Gamma> (PAtom n)"
proof
  assume "gr \<Gamma> (PAtom n)"
  then have "\<Gamma> \<noteq> {}" "\<forall>r\<in>\<Gamma>. cst r (PAtom n)" by (auto dest: gr_sound)
  then obtain r where "cst r (PAtom n)" by blast
  then show False by (auto dest: cst_rank)
qed

lemma M1_N4_pairs: "pN4_pairs M1"
proof -
  have "{\<Gamma>. gr \<Gamma> (PAtom 0)} = {}" using atom_ungrounded by blast
  moreover have "{PAtom 0} \<in> {\<Gamma>. gr \<Gamma> (PNeg (PNeg (PAtom 0)))}" by (simp add: g_dn)
  ultimately have d: "{\<Gamma>. gr \<Gamma> (PAtom 0)} \<noteq> {\<Gamma>. gr \<Gamma> (PNeg (PNeg (PAtom 0)))}" by blast
  have sh: "\<exists>p. PAtom 0 = p \<and> PNeg (PNeg (PAtom 0)) = PNeg (PNeg p)" by blast
  show ?thesis unfolding pN4_pairs_def M1_sel
    by (rule exI[of _ "PAtom 0"], rule exI[of _ "PNeg (PNeg (PAtom 0))"]) (use sh d in simp)
qed

theorem M1_package:
  "pFACT M1" "pLAM_CORE M1" "pC3d M1" "pCL_PROP M1" "pCL_QUANT M1" "pTS_FULL M1"
  "pIRR_F M1" "pASYM_P M1" "pTRANS_P M1" "pTRANS_CUT M1" "pAMALG_INF M1" "pEMPTY_NONE M1"
  "pCONJ_BIN M1" "pCONJ_GRAIN M1" "pDISJ_ONE M1" "pDISJ_BOTH M1" "pNEG_DN M1" "pNEG_DM M1"
  "pEX_FULL M1" "pALL_INST M1" "pTR_FULL M1" "pTR_NEG M1"
  "pN1 M1" "pN2 M1" "pN4_pairs M1" "pN5_chain M1"
  by (fact M1_FACT M1_LAM_CORE M1_C3d M1_CL_PROP M1_CL_QUANT M1_TS_FULL M1_IRR_F M1_ASYM_P
      M1_TRANS_P M1_TRANS_CUT M1_AMALG_INF M1_EMPTY_NONE M1_CONJ_BIN M1_CONJ_GRAIN M1_DISJ_ONE
      M1_DISJ_BOTH M1_NEG_DN M1_NEG_DM M1_EX_FULL M1_ALL_INST M1_TR_FULL M1_TR_NEG M1_N1 M1_N2
      M1_N4_pairs M1_N5_chain)+

text \<open>What M1 gives up: application is not substitution, and an instance is not grounded
  in what it would denote by beta-conversion.\<close>

lemma M1_not_BETA_ID: "\<not> pBETA_ID M1"
proof
  assume "pBETA_ID M1"
  then have "sapp M1 (slam M1 0 (Cst 0) (\<lambda>_. PAtom 0)) (PAtom 0)
           = sden M1 ((\<lambda>_. PAtom 0)(0 := PAtom 0)) (Cst 0)"
    unfolding pBETA_ID_def by blast
  then show False by simp
qed

lemma M1_app_ungrounded: "\<not> gr \<Gamma> (PApp f p)"
proof
  assume "gr \<Gamma> (PApp f p)"
  then have "\<Gamma> \<noteq> {}" "\<forall>r\<in>\<Gamma>. cst r (PApp f p)" by (auto dest: gr_sound)
  then obtain r where "cst r (PApp f p)" by blast
  then show False by (auto dest: cst_rank)
qed

section \<open>What M1 depends on: negation is not a propositional function\<close>

text \<open>
  Goodman 2023 (sec. 2) observes that if negation contributes structure and is itself a
  property, Kr\"amer's puzzle recurs with negation in place of (\<lambda>p. p): the instance
  of \<open>\<exists>\<not>\<close> at \<open>\<not>E\<close> is \<open>\<not>\<not>E\<close>, which grounds E by EX.FULL and is grounded in E by
  NEG.DN. M1 escapes only because no admissible function applies as negation does: every
  application is a PApp term. The lemma below states the dependence: add one admissible
  f with app f p = neg p for all p, and the package refutes itself. Neither N1 nor FACT
  is needed.
\<close>

lemma neg_as_function_refutes:
  assumes cp: "CL_PROP" and cq: "CL_QUANT" and ex: "EX_FULL" and dn: "NEG_DN" and asym: "ASYM_P"
      and f: "adm f" "\<forall>p. app f p = neg p"
  shows False
proof -
  have negT: "\<And>p. T (neg p) \<longleftrightarrow> \<not> T p" using cp unfolding CL_PROP_def by blast
  have "T (atom 0) \<or> T (neg (atom 0))" using negT by blast
  then obtain q where q: "T q" by blast
  have "T (app f (neg q))" using f(2) negT q by simp
  then have E: "T (exq f)" using cq unfolding CL_QUANT_def by blast
  have inst: "T (app f (neg (exq f)))" using f(2) negT E by simp
  have g1: "G {neg (neg (exq f))} (exq f)"
    using ex f inst unfolding EX_FULL_def by (metis)
  have g2: "G {exq f} (neg (neg (exq f)))" using dn E unfolding NEG_DN_def by blast
  have "PG (neg (neg (exq f))) (exq f)" "PG (exq f) (neg (neg (exq f)))"
    using g1 g2 unfolding PG_def by blast+
  with asym show False unfolding ASYM_P_def by blast
qed

end
