theory Antisymmetry_Collapse
  imports Woods_Models
begin

text \<open>
  Antisymmetry and contingency (finding F27).

  The argument checked here. Let E be the proposition that something is the case
  (exq f_id, with app f_id p = p), and let q be any truth.
    (1) E helps ground E \<and> q                     CONJ.BIN
    (2) E \<and> q helps ground E                     EX.PART at f_id, with BETA.ID
    (3) so E \<and> q = E                             ASYM.ANTI
    (4) E is true at every world, so E \<and> q is, so q is.
  Steps (1)-(3) are about the one world of the registry and use registry entries only
  (Part 1). Step (4) needs worlds, which the registry does not have. Part 2 adds the
  least that is needed: a valuation V :: 'w \<Rightarrow> prp \<Rightarrow> bool giving truth at a world. The
  propositions stay the registry's base type, so one proposition has a truth value at
  every world and identity is the identity of HOL.

  READINGS CHOSEN, each flagged in the registry entry of the finding.
  (i) Kr\"amer's rule (EG-S), "From \<phi>(\<alpha>), infer \<phi>(\<alpha>) \<prec> \<exists>p \<phi>(p)" with the null context
      (Kr\"amer 2013, eprint p. 4), is EX.PART at the identity function f_id together
      with BETA.ID: the instance of "something is the case" at p is p itself.
  (ii) Antisymmetry is ASYM.ANTI for the registry's partial ground PG, which is strict
      (defined from strict full ground G) and factive; no irreflexivity entry is assumed,
      so reflexive cases are allowed. This is the reading of Woods 2018 fn. 4 (p. 632),
      which names antisymmetry and does not write it out.
  (iii) "Necessary" is truth at every world of V. Nothing is assumed about how ground
      behaves at other worlds: G and T are the registry's one-world constants throughout.
  (iv) Identity. Because V w is a function of the proposition, identical propositions
      are true at the same worlds. Part 3 isolates this: with antisymmetry stated for an
      arbitrary relation I in place of identity, the argument needs exactly that
      I-related propositions are alike in being necessary.

  Nothing here is an axiom. The countermodels of Part 6 are for the lean signature of
  that part (a conjunction, one existential proposition, a ground relation, two
  worlds), not for the registry's full signature.
\<close>

section \<open>Part 1. One world: what antisymmetry identifies\<close>

lemma PG_fact:
  assumes "FACT" "PG p q"
  shows "T p" "T q"
  using assms unfolding FACT_def PG_def by blast+

text \<open>Steps (1)-(3). Entries used: W.ID, BETA.ID, FACT, CONJ.BIN, EX.PART, ASYM.ANTI.
  Not used: any irreflexivity entry, TRANS.P, TRANS.CUT, CL.PROP, CL.QUANT.\<close>
theorem anti_ex_conj:
  assumes wid: "W_ID" and beta: "BETA_ID" and fact: "FACT"
      and cj: "CONJ_BIN" and ex: "EX_PART" and anti: "ASYM_ANTI" and q: "T q"
  shows "conj (exq f_id) q = exq f_id"
proof -
  let ?E = "exq f_id"
  have ad: "adm f_id" using wid unfolding W_ID_def .
  have app: "app f_id p = p" for p using BETA_apps(1)[OF beta] .
  have inst: "PG p ?E" if "T p" for p
  proof -
    have "T (app f_id p)" using that app by simp
    hence "PG (app f_id p) ?E" using ex ad unfolding EX_PART_def by blast
    thus ?thesis using app by simp
  qed
  have TE: "T ?E" using PG_fact(2)[OF fact inst[OF q]] .
  have "G {?E, q} (conj ?E q)" using cj TE q unfolding CONJ_BIN_def by blast
  hence up: "PG ?E (conj ?E q)" unfolding PG_def by blast
  have "T (conj ?E q)" using PG_fact(2)[OF fact up] .
  hence down: "PG (conj ?E q) ?E" using inst by blast
  have "?E = conj ?E q" using anti up down unfolding ASYM_ANTI_def by blast
  thus ?thesis by simp
qed

text \<open>The same with disjunction, for every r, true or not (q only witnesses that
  something is true). Goodman 2023 sect. 5.2 uses this circle, with the existential
  generalization of disjunction, against asymmetry. Under antisymmetry it gives an
  identity between propositions that are true at the same worlds, so nothing modal
  follows from it.\<close>
theorem anti_ex_disj:
  assumes wid: "W_ID" and beta: "BETA_ID" and fact: "FACT"
      and dj: "DISJ_PART" and ex: "EX_PART" and anti: "ASYM_ANTI" and q: "T q"
  shows "disj (exq f_id) r = exq f_id"
proof -
  let ?E = "exq f_id"
  have ad: "adm f_id" using wid unfolding W_ID_def .
  have app: "app f_id p = p" for p using BETA_apps(1)[OF beta] .
  have inst: "PG p ?E" if "T p" for p
  proof -
    have "T (app f_id p)" using that app by simp
    hence "PG (app f_id p) ?E" using ex ad unfolding EX_PART_def by blast
    thus ?thesis using app by simp
  qed
  have TE: "T ?E" using PG_fact(2)[OF fact inst[OF q]] .
  have up: "PG ?E (disj ?E r)" using dj TE unfolding DISJ_PART_def by blast
  have "T (disj ?E r)" using PG_fact(2)[OF fact up] .
  hence down: "PG (disj ?E r) ?E" using inst by blast
  have "?E = disj ?E r" using anti up down unfolding ASYM_ANTI_def by blast
  thus ?thesis by simp
qed

text \<open>So all conjunctions of E with a truth are one proposition.\<close>
corollary anti_ex_conj_all_one:
  assumes "W_ID" "BETA_ID" "FACT" "CONJ_BIN" "EX_PART" "ASYM_ANTI" "T q" "T r"
  shows "conj (exq f_id) q = conj (exq f_id) r"
  using anti_ex_conj[OF assms(1-6)] assms(7,8) by simp

section \<open>Part 2. Worlds: every truth is necessary\<close>

text \<open>V w p: the proposition p is true at the world w. The clauses below are all that
  is assumed about V, each named so that a theorem shows which it uses.\<close>

definition NEC :: "('w \<Rightarrow> prp \<Rightarrow> bool) \<Rightarrow> prp \<Rightarrow> bool" where
  "NEC V p \<longleftrightarrow> (\<forall>w. V w p)"
text \<open>ACT: the registry's truth predicate is truth at the world a.\<close>
definition ACT :: "('w \<Rightarrow> prp \<Rightarrow> bool) \<Rightarrow> 'w \<Rightarrow> bool" where
  "ACT V a \<longleftrightarrow> (\<forall>p. V a p \<longleftrightarrow> T p)"
text \<open>M_CONJ: at every world a true conjunction has a true second conjunct.\<close>
definition M_CONJ :: "('w \<Rightarrow> prp \<Rightarrow> bool) \<Rightarrow> bool" where
  "M_CONJ V \<longleftrightarrow> (\<forall>w p q. V w (conj p q) \<longrightarrow> V w q)"
text \<open>M_EX: at every world an existential with a true instance is true.\<close>
definition M_EX :: "('w \<Rightarrow> prp \<Rightarrow> bool) \<Rightarrow> bool" where
  "M_EX V \<longleftrightarrow> (\<forall>w f p. V w (app f p) \<longrightarrow> V w (exq f))"
text \<open>M_SOME: at every world something is the case.\<close>
definition M_SOME :: "('w \<Rightarrow> prp \<Rightarrow> bool) \<Rightarrow> bool" where
  "M_SOME V \<longleftrightarrow> (\<forall>w. \<exists>p. V w p)"
text \<open>M_NEG: at no world are a proposition and its negation both true.\<close>
definition M_NEG :: "('w \<Rightarrow> prp \<Rightarrow> bool) \<Rightarrow> bool" where
  "M_NEG V \<longleftrightarrow> (\<forall>w p. V w (neg p) \<longrightarrow> \<not> V w p)"

text \<open>The necessity of E is not a separate premise: it follows from M_EX and M_SOME.\<close>
lemma NEC_E:
  assumes "BETA_ID" "M_EX V" "M_SOME V"
  shows "NEC V (exq f_id)"
proof -
  have "V w (exq f_id)" for w
  proof -
    obtain p where "V w p" using assms(3) unfolding M_SOME_def by blast
    hence "V w (app f_id p)" using BETA_apps(1)[OF assms(1)] by simp
    thus ?thesis using assms(2) unfolding M_EX_def by blast
  qed
  thus ?thesis unfolding NEC_def by blast
qed

text \<open>Step (4). Every truth is true at every world. Beyond Part 1 the theorem uses the
  necessity of E and M_CONJ, and nothing else about worlds: not ACT, no principle that
  grounds necessitate what they ground, no principle that ground or identity is
  necessary.\<close>
theorem anti_necessitation:
  assumes "W_ID" "BETA_ID" "FACT" "CONJ_BIN" "EX_PART" "ASYM_ANTI"
      and nec: "NEC V (exq f_id)" and mc: "M_CONJ V" and q: "T q"
  shows "NEC V q"
proof -
  have "conj (exq f_id) q = exq f_id" using anti_ex_conj[OF assms(1-6) q] .
  hence "NEC V (conj (exq f_id) q)" using nec by simp
  thus ?thesis using mc unfolding NEC_def M_CONJ_def by blast
qed

text \<open>No truth is contingent: with ACT, no proposition true at the actual world is
  false at another.\<close>
corollary anti_no_contingent_truth:
  assumes "W_ID" "BETA_ID" "FACT" "CONJ_BIN" "EX_PART" "ASYM_ANTI"
      and "M_EX V" "M_SOME V" "M_CONJ V" "ACT V a"
  shows "\<not> (\<exists>q w. V a q \<and> \<not> V w q)"
proof -
  have nec: "NEC V (exq f_id)" using NEC_E[OF assms(2,7,8)] .
  have "NEC V q" if "T q" for q using anti_necessitation[OF assms(1-6) nec assms(9) that] .
  thus ?thesis using assms(10) unfolding ACT_def NEC_def by blast
qed

text \<open>Collapse. If, in addition, every proposition or its negation is true (from CL.PROP)
  and no world makes both true (M_NEG), then every world agrees with the registry's truth
  predicate on every proposition: nothing is contingent, true or false.\<close>
theorem anti_modal_collapse:
  assumes "W_ID" "BETA_ID" "FACT" "CONJ_BIN" "EX_PART" "ASYM_ANTI"
      and cl: "CL_PROP" and "M_EX V" "M_SOME V" and mc: "M_CONJ V" and mn: "M_NEG V"
  shows "V w p \<longleftrightarrow> T p"
proof -
  have nec: "NEC V (exq f_id)" using NEC_E[OF assms(2,8,9)] .
  have up: "NEC V q" if "T q" for q using anti_necessitation[OF assms(1-6) nec mc that] .
  show ?thesis
  proof
    assume "V w p"
    show "T p"
    proof (rule ccontr)
      assume "\<not> T p"
      hence "T (neg p)" using cl unfolding CL_PROP_def by blast
      hence "V w (neg p)" using up unfolding NEC_def by blast
      thus False using mn \<open>V w p\<close> unfolding M_NEG_def by blast
    qed
  next
    assume "T p" thus "V w p" using up unfolding NEC_def by blast
  qed
qed

text \<open>The modal premises add nothing that a classical one-world model lacks: the constant
  valuation satisfies all of them. So the premises of anti_modal_collapse are jointly
  consistent whenever the one-world package is, and that package (with ASYM.ANTI, at N5)
  has the model MY of Woods_Models.thy. In such a model there is one world in effect.\<close>
lemma constant_valuation:
  assumes cl: "CL_PROP" and clq: "CL_QUANT"
  shows "ACT (\<lambda>w. T) a" "M_CONJ (\<lambda>w. T)" "M_EX (\<lambda>w. T)" "M_SOME (\<lambda>w. T)" "M_NEG (\<lambda>w. T)"
proof -
  show "ACT (\<lambda>w. T) a" unfolding ACT_def by simp
  show "M_CONJ (\<lambda>w. T)" using cl unfolding M_CONJ_def CL_PROP_def by blast
  show "M_EX (\<lambda>w. T)" using clq unfolding M_EX_def CL_QUANT_def by blast
  show "M_SOME (\<lambda>w. T)" using CL_QUANT_truth[OF clq] unfolding M_SOME_def by blast
  show "M_NEG (\<lambda>w. T)" using cl unfolding M_NEG_def CL_PROP_def by blast
qed

section \<open>Part 3. The premise about identity\<close>

text \<open>Antisymmetry with an arbitrary relation I in the place of identity (a "just is"
  connective, or factual equivalence). The argument then needs one thing of I: if p and
  r are I-related and p is necessary, r is necessary (SUBST). For identity this is
  Leibniz's law applied once, to an identity that holds at the actual world, inside the
  context "necessarily". The necessity of identity is not used, and neither is any
  converse (that necessarily equivalent propositions are identical).\<close>
definition ANTI_REL :: "(prp \<Rightarrow> prp \<Rightarrow> bool) \<Rightarrow> bool" where
  "ANTI_REL I \<longleftrightarrow> (\<forall>p q. PG p q \<and> PG q p \<longrightarrow> I p q)"
definition SUBST :: "('w \<Rightarrow> prp \<Rightarrow> bool) \<Rightarrow> (prp \<Rightarrow> prp \<Rightarrow> bool) \<Rightarrow> bool" where
  "SUBST V I \<longleftrightarrow> (\<forall>p r. I p r \<and> NEC V p \<longrightarrow> NEC V r)"

lemma ANTI_REL_identity: "ANTI_REL (=) \<longleftrightarrow> ASYM_ANTI"
  unfolding ANTI_REL_def ASYM_ANTI_def by simp
lemma SUBST_identity: "SUBST V (=)"
  unfolding SUBST_def by simp

theorem anti_necessitation_rel:
  assumes wid: "W_ID" and beta: "BETA_ID" and fact: "FACT"
      and cj: "CONJ_BIN" and ex: "EX_PART" and anti: "ANTI_REL I" and sub: "SUBST V I"
      and nec: "NEC V (exq f_id)" and mc: "M_CONJ V" and q: "T q"
  shows "NEC V q"
proof -
  let ?E = "exq f_id"
  have ad: "adm f_id" using wid unfolding W_ID_def .
  have app: "app f_id p = p" for p using BETA_apps(1)[OF beta] .
  have inst: "PG p ?E" if "T p" for p
  proof -
    have "T (app f_id p)" using that app by simp
    hence "PG (app f_id p) ?E" using ex ad unfolding EX_PART_def by blast
    thus ?thesis using app by simp
  qed
  have TE: "T ?E" using PG_fact(2)[OF fact inst[OF q]] .
  have "G {?E, q} (conj ?E q)" using cj TE q unfolding CONJ_BIN_def by blast
  hence up: "PG ?E (conj ?E q)" unfolding PG_def by blast
  have "T (conj ?E q)" using PG_fact(2)[OF fact up] .
  hence down: "PG (conj ?E q) ?E" using inst by blast
  have "I ?E (conj ?E q)" using anti up down unfolding ANTI_REL_def by blast
  hence "NEC V (conj ?E q)" using sub nec unfolding SUBST_def by blast
  thus ?thesis using mc unfolding NEC_def M_CONJ_def by blast
qed

section \<open>Part 4. Other routes to the same identity\<close>

text \<open>(a) Without the existential entry, through Fine's sentence-position universal
  U = \<forall>p(p \<or> \<not>p). Every truth helps ground U (fine_sp_every_truth, which uses TRANS.P),
  and U helps ground U \<and> q. So restricting or rejecting the existential rule does not by
  itself avoid the result; the universal and disjunction rules with transitivity give
  it again.\<close>
theorem anti_all_conj:
  assumes wem: "W_EM" and beta: "BETA_ID" and cl: "CL_PROP" and clq: "CL_QUANT"
      and ug: "ALL_PART" and dg: "DISJ_PART" and tra: "TRANS_P"
      and cj: "CONJ_BIN" and anti: "ASYM_ANTI" and q: "T q"
  shows "conj (allq f_em) q = allq f_em"
proof -
  let ?U = "allq f_em"
  have ad: "adm f_em" using wem unfolding W_EM_def .
  have TU: "T ?U" using fine_sp_circle(1)[OF ad beta cl clq ug dg] .
  have "G {?U, q} (conj ?U q)" using cj TU q unfolding CONJ_BIN_def by blast
  hence up: "PG ?U (conj ?U q)" unfolding PG_def by blast
  have "T (conj ?U q)" using cl TU q unfolding CL_PROP_def by blast
  hence down: "PG (conj ?U q) ?U" using fine_sp_every_truth[OF ad beta cl clq ug dg tra] by blast
  have "?U = conj ?U q" using anti up down unfolding ASYM_ANTI_def by blast
  thus ?thesis by simp
qed

theorem anti_necessitation_all:
  assumes "W_EM" "BETA_ID" "CL_PROP" "CL_QUANT" "ALL_PART" "DISJ_PART" "TRANS_P"
          "CONJ_BIN" "ASYM_ANTI"
      and nec: "NEC V (allq f_em)" and mc: "M_CONJ V" and q: "T q"
  shows "NEC V q"
proof -
  have "conj (allq f_em) q = allq f_em" using anti_all_conj[OF assms(1-9) q] .
  hence "NEC V (conj (allq f_em) q)" using nec by simp
  thus ?thesis using mc unfolding NEC_def M_CONJ_def by blast
qed

text \<open>(b) With \<beta>-grounding in place of \<beta>-identity (Fine's \<lambda>-rule, BETA.GROUND): the
  instance of E at p is then a different proposition, which p grounds. With TRANS.P the
  identity returns. So on the existential side the escape is to deny both \<beta>-identity and
  \<beta>-grounding, which is the position of Fritz 2020 and of Goodman 2023 sects. 2-3.\<close>
theorem anti_ex_conj_beta_ground:
  assumes wid: "W_ID" and bg: "BETA_GROUND" and fact: "FACT"
      and cj: "CONJ_BIN" and ex: "EX_PART" and tra: "TRANS_P" and anti: "ASYM_ANTI"
      and q: "T q"
  shows "conj (exq f_id) q = exq f_id"
proof -
  let ?E = "exq f_id"
  have ad: "adm f_id" using wid unfolding W_ID_def .
  have step: "G {p} (app f_id p)" if "T p" for p
  proof -
    have "T (den (e0(0:=p)) (Var 0))" using that by simp
    hence "G {den (e0(0:=p)) (Var 0)} (app (lam 0 (Var 0) e0) p)"
      using bg unfolding BETA_GROUND_def by blast
    thus ?thesis unfolding f_id_def by simp
  qed
  have inst: "PG p ?E" if "T p" for p
  proof -
    have g: "G {p} (app f_id p)" using step[OF that] .
    hence a: "PG p (app f_id p)" unfolding PG_def by blast
    have "T (app f_id p)" using fact g unfolding FACT_def by blast
    hence "PG (app f_id p) ?E" using ex ad unfolding EX_PART_def by blast
    thus ?thesis using tra a unfolding TRANS_P_def by blast
  qed
  have TE: "T ?E" using PG_fact(2)[OF fact inst[OF q]] .
  have "G {?E, q} (conj ?E q)" using cj TE q unfolding CONJ_BIN_def by blast
  hence up: "PG ?E (conj ?E q)" unfolding PG_def by blast
  have "T (conj ?E q)" using PG_fact(2)[OF fact up] .
  hence down: "PG (conj ?E q) ?E" using inst by blast
  have "?E = conj ?E q" using anti up down unfolding ASYM_ANTI_def by blast
  thus ?thesis by simp
qed

section \<open>Part 5. Non-factive ground: a contradiction without worlds\<close>

text \<open>The registry's ground is factive (FACT). Lovett 2020 states his rules for
  non-factive ground, without premises (p. 2544). Read that way - a conjunct helps
  ground its conjunction and an instance helps ground its existential, whether or not
  they are true - antisymmetry contradicts classical truth outright: E is true, E \<and> u is
  false for a false u, and they would be one proposition. The two rules are local
  hypotheses here, not registry entries. Compare Lovett's remark that mutual weak
  partial ground "doesn't even guarantee that A and B are materially equivalent"
  (fn. 33, p. 2558).\<close>
theorem anti_nonfactive_refuted:
  assumes wid: "W_ID" and beta: "BETA_ID" and cl: "CL_PROP" and clq: "CL_QUANT"
      and cjn: "\<forall>p q. PG p (conj p q)"
      and exn: "\<forall>f p. adm f \<longrightarrow> PG (app f p) (exq f)"
      and anti: "ASYM_ANTI"
  shows False
proof -
  let ?E = "exq f_id"
  have ad: "adm f_id" using wid unfolding W_ID_def .
  have app: "app f_id p = p" for p using BETA_apps(1)[OF beta] .
  obtain t where t: "T t" using CL_QUANT_truth[OF clq] by blast
  hence "T (app f_id t)" using app by simp
  hence TE: "T ?E" using clq unfolding CL_QUANT_def by blast
  let ?u = "neg t"
  have nu: "\<not> T ?u" using cl t unfolding CL_PROP_def by blast
  have up: "PG ?E (conj ?E ?u)" using cjn by blast
  have "PG (app f_id (conj ?E ?u)) ?E" using exn ad by blast
  hence down: "PG (conj ?E ?u) ?E" using app by simp
  have "?E = conj ?E ?u" using anti up down unfolding ASYM_ANTI_def by blast
  hence "T (conj ?E ?u)" using TE by simp
  thus False using cl nu unfolding CL_PROP_def by blast
qed

section \<open>Part 6. Which premises are needed: lean models with two worlds\<close>

text \<open>
  A lean signature: truth at a world, an actual world, a conjunction, a negation, one
  proposition E, and full ground at the actual world. The clauses are the instances of
  the registry entries that the argument uses. L_EX is EX.FULL at f_id with BETA.ID.
  These models show which of the argument's premises carry the result; they are not
  models of the registry's packages, which have the whole formula layer.
\<close>

locale lean =
  fixes V :: "'w \<Rightarrow> 'p \<Rightarrow> bool" and a :: 'w
    and cj :: "'p \<Rightarrow> 'p \<Rightarrow> 'p" and ng :: "'p \<Rightarrow> 'p" and E :: 'p
    and Gr :: "'p set \<Rightarrow> 'p \<Rightarrow> bool"
begin
definition PGr :: "'p \<Rightarrow> 'p \<Rightarrow> bool" where "PGr p q \<longleftrightarrow> (\<exists>\<Gamma>. p \<in> \<Gamma> \<and> Gr \<Gamma> q)"
definition L_FACT :: bool where
  "L_FACT \<longleftrightarrow> (\<forall>\<Gamma> p. Gr \<Gamma> p \<longrightarrow> V a p \<and> (\<forall>q\<in>\<Gamma>. V a q))"
definition L_CONJ :: bool where
  "L_CONJ \<longleftrightarrow> (\<forall>p q. V a p \<and> V a q \<longrightarrow> Gr {p, q} (cj p q))"
definition L_EX :: bool where
  "L_EX \<longleftrightarrow> (\<forall>p. V a p \<longrightarrow> Gr {p} E)"
definition L_ANTI :: bool where
  "L_ANTI \<longleftrightarrow> (\<forall>p q. PGr p q \<and> PGr q p \<longrightarrow> p = q)"
definition L_ASYM :: bool where
  "L_ASYM \<longleftrightarrow> (\<forall>p q. PGr p q \<longrightarrow> \<not> PGr q p)"
definition L_TRANS :: bool where
  "L_TRANS \<longleftrightarrow> (\<forall>p q r. PGr p q \<and> PGr q r \<longrightarrow> PGr p r)"
text \<open>Classical truth at every world, and E true exactly where something is.\<close>
definition L_CL :: bool where
  "L_CL \<longleftrightarrow> (\<forall>w p q. (V w (cj p q) \<longleftrightarrow> V w p \<and> V w q) \<and> (V w (ng p) \<longleftrightarrow> \<not> V w p))
          \<and> (\<forall>w. V w E \<longleftrightarrow> (\<exists>p. V w p))"
definition CONTINGENT :: bool where
  "CONTINGENT \<longleftrightarrow> (\<exists>p w. V a p \<and> \<not> V w p)"
text \<open>Reflexive ground only where the ground is replaceable by any truth (the one-world,
  membership form of Woods's vacuity; compare IRR.MEM).\<close>
definition L_IRR_VAC :: bool where
  "L_IRR_VAC \<longleftrightarrow> (\<forall>\<Gamma> c. Gr \<Gamma> c \<and> c \<in> \<Gamma> \<longrightarrow> (\<forall>b. V a b \<longrightarrow> Gr (insert b (\<Gamma> - {c})) c))"
text \<open>Antisymmetry restricted in the same spirit: two propositions that help ground each
  other are one, unless each is fully grounded by every truth on its own.\<close>
definition L_ANTI_VAC :: bool where
  "L_ANTI_VAC \<longleftrightarrow> (\<forall>p q. PGr p q \<and> PGr q p \<longrightarrow>
       p = q \<or> (\<forall>b. V a b \<longrightarrow> Gr {b} p \<and> Gr {b} q))"

text \<open>The argument in the lean signature.\<close>
theorem lean_collapse:
  assumes "L_FACT" "L_CONJ" "L_EX" "L_ANTI" "L_CL"
  shows "\<not> CONTINGENT"
proof
  assume "CONTINGENT"
  then obtain q w where q: "V a q" and nq: "\<not> V w q" unfolding CONTINGENT_def by blast
  have TE: "V a E" using assms(5) q unfolding L_CL_def by blast
  have "Gr {E, q} (cj E q)" using assms(2) TE q unfolding L_CONJ_def by blast
  hence up: "PGr E (cj E q)" unfolding PGr_def by blast
  have "V a (cj E q)" using assms(5) TE q unfolding L_CL_def by blast
  hence "Gr {cj E q} E" using assms(3) unfolding L_EX_def by blast
  hence down: "PGr (cj E q) E" unfolding PGr_def by blast
  have eq: "E = cj E q" using assms(4) up down unfolding L_ANTI_def by blast
  have "V w E" using assms(5) q unfolding L_CL_def by blast
  hence "V w (cj E q)" using eq by simp
  thus False using assms(5) nq unfolding L_CL_def by blast
qed
end

subsection \<open>Model LA: every premise but antisymmetry, with a contingent truth\<close>

text \<open>
  Worlds are the two truth values, True the actual one. A proposition is a pair of
  truth values (at the actual and at the other world) with a tier, Lo n or Hi. A
  non-empty set of actual truths fully grounds an actual truth c when c is in the tier
  Hi or every member has a lower tier than c. E is (True, True, Hi). This is the model
  MV of Woods_Models.thy cut down to the lean signature and given a second world.
\<close>

datatype tier = Lo nat | Hi

fun below :: "tier \<Rightarrow> tier \<Rightarrow> bool" where
  "below t Hi = True"
| "below (Lo m) (Lo n) = (m < n)"
| "below Hi (Lo n) = False"

fun upt :: "tier \<Rightarrow> tier" where "upt (Lo n) = Lo (Suc n)" | "upt Hi = Hi"
fun mxt :: "tier \<Rightarrow> tier \<Rightarrow> tier" where
  "mxt (Lo m) (Lo n) = Lo (max m n)" | "mxt Hi t = Hi" | "mxt (Lo m) Hi = Hi"

lemma below_upt: "below t (upt t)" by (cases t) simp_all
lemma below_mx1: "below s (upt (mxt s t))" by (cases s; cases t) simp_all
lemma below_mx2: "below t (upt (mxt s t))" by (cases s; cases t) simp_all
lemma below_trans: "below r s \<Longrightarrow> below s t \<Longrightarrow> below r t"
  by (cases r; cases s; cases t) simp_all
lemma below_both: "below s t \<Longrightarrow> below t s \<Longrightarrow> s = Hi \<and> t = Hi"
  by (cases s; cases t) simp_all

record pl =
  act :: bool
  oth :: bool
  tie :: tier

definition VL :: "bool \<Rightarrow> pl \<Rightarrow> bool" where "VL w p = (if w then act p else oth p)"
definition cjL :: "pl \<Rightarrow> pl \<Rightarrow> pl" where
  "cjL p q = \<lparr>act = act p \<and> act q, oth = oth p \<and> oth q, tie = upt (mxt (tie p) (tie q))\<rparr>"
definition ngL :: "pl \<Rightarrow> pl" where
  "ngL p = \<lparr>act = \<not> act p, oth = \<not> oth p, tie = upt (tie p)\<rparr>"
definition EL :: pl where "EL = \<lparr>act = True, oth = True, tie = Hi\<rparr>"
definition GA :: "pl set \<Rightarrow> pl \<Rightarrow> bool" where
  "GA \<Gamma> c \<longleftrightarrow> \<Gamma> \<noteq> {} \<and> (\<forall>p\<in>\<Gamma>. act p) \<and> act c \<and> (tie c = Hi \<or> (\<forall>p\<in>\<Gamma>. below (tie p) (tie c)))"

interpretation LA: lean VL True cjL ngL EL GA .

lemma LA_PG: "LA.PGr p q \<longleftrightarrow> act p \<and> act q \<and> below (tie p) (tie q)"
proof
  assume "LA.PGr p q"
  then obtain \<Gamma> where "p \<in> \<Gamma>" "GA \<Gamma> q" unfolding LA.PGr_def by blast
  thus "act p \<and> act q \<and> below (tie p) (tie q)" unfolding GA_def by (cases "tie q") auto
next
  assume h: "act p \<and> act q \<and> below (tie p) (tie q)"
  hence "GA {p} q" unfolding GA_def by simp
  thus "LA.PGr p q" unfolding LA.PGr_def by blast
qed

lemma LA_FACT: "LA.L_FACT" unfolding LA.L_FACT_def unfolding GA_def VL_def by auto
lemma LA_CONJ: "LA.L_CONJ"
  unfolding LA.L_CONJ_def unfolding GA_def VL_def cjL_def using below_mx1 below_mx2 by auto
lemma LA_EX: "LA.L_EX" unfolding LA.L_EX_def unfolding GA_def VL_def EL_def by simp
lemma LA_TRANS: "LA.L_TRANS" unfolding LA.L_TRANS_def LA_PG using below_trans by blast
lemma LA_CL: "LA.L_CL"
proof -
  have "\<exists>p. VL w p" for w
    by (rule exI[of _ EL]) (simp add: VL_def EL_def)
  thus ?thesis unfolding LA.L_CL_def unfolding VL_def cjL_def ngL_def EL_def by auto
qed

definition qL :: pl where "qL = \<lparr>act = True, oth = False, tie = Lo 0\<rparr>"

lemma LA_CONTINGENT: "LA.CONTINGENT"
  unfolding LA.CONTINGENT_def
  by (rule exI[of _ qL], rule exI[of _ False]) (simp add: VL_def qL_def)

lemma LA_circle:
  "LA.PGr EL (cjL EL qL)" "LA.PGr (cjL EL qL) EL" "cjL EL qL \<noteq> EL"
  "VL False EL" "\<not> VL False (cjL EL qL)"
  unfolding LA_PG by (simp_all add: cjL_def EL_def qL_def VL_def)

lemma LA_not_ANTI: "\<not> LA.L_ANTI"
  using LA_circle(1-3) unfolding LA.L_ANTI_def by metis

text \<open>The model is Woods-like: a truth is among its own grounds only if it is in the
  tier Hi, where any truth could take its place; and two truths help ground each other
  only if both are in that tier.\<close>
lemma LA_IRR_VAC: "LA.L_IRR_VAC"
proof -
  have "GA (insert b (\<Gamma> - {c})) c" if g: "GA \<Gamma> c" and m: "c \<in> \<Gamma>" and b: "VL True b" for \<Gamma> c b
  proof -
    have "tie c = Hi \<or> below (tie c) (tie c)" using g m unfolding GA_def by blast
    hence hi: "tie c = Hi" using below_both by blast
    show ?thesis using g b hi unfolding GA_def VL_def by auto
  qed
  thus ?thesis unfolding LA.L_IRR_VAC_def by blast
qed

lemma LA_ANTI_VAC: "LA.L_ANTI_VAC"
proof -
  have "GA {b} p \<and> GA {b} q" if "LA.PGr p q" "LA.PGr q p" "VL True b" for p q b
  proof -
    have "tie p = Hi \<and> tie q = Hi" using that(1,2) below_both unfolding LA_PG by blast
    thus ?thesis using that unfolding LA_PG GA_def VL_def by simp
  qed
  thus ?thesis unfolding LA.L_ANTI_VAC_def by blast
qed

theorem LA_model:
  "LA.L_FACT \<and> LA.L_CONJ \<and> LA.L_EX \<and> LA.L_TRANS \<and> LA.L_CL \<and> LA.CONTINGENT
   \<and> \<not> LA.L_ANTI \<and> LA.L_IRR_VAC \<and> LA.L_ANTI_VAC"
  using LA_FACT LA_CONJ LA_EX LA_TRANS LA_CL LA_CONTINGENT LA_not_ANTI LA_IRR_VAC LA_ANTI_VAC
  by blast

subsection \<open>Model LB: every premise but the unrestricted existential rule\<close>

text \<open>The same propositions with natural-number tiers only and a strict order: a
  non-empty set of actual truths grounds an actual truth of higher tier. E has tier 1,
  so only truths of tier 0 ground it (a predicative restriction, as in EX.PRED). Ground
  is asymmetric, so antisymmetric, and there is a contingent truth.\<close>

record pb =
  actb :: bool
  othb :: bool
  lev :: nat

definition VB :: "bool \<Rightarrow> pb \<Rightarrow> bool" where "VB w p = (if w then actb p else othb p)"
definition cjB :: "pb \<Rightarrow> pb \<Rightarrow> pb" where
  "cjB p q = \<lparr>actb = actb p \<and> actb q, othb = othb p \<and> othb q, lev = Suc (max (lev p) (lev q))\<rparr>"
definition ngB :: "pb \<Rightarrow> pb" where
  "ngB p = \<lparr>actb = \<not> actb p, othb = \<not> othb p, lev = Suc (lev p)\<rparr>"
definition EB :: pb where "EB = \<lparr>actb = True, othb = True, lev = 1\<rparr>"
definition GB :: "pb set \<Rightarrow> pb \<Rightarrow> bool" where
  "GB \<Gamma> c \<longleftrightarrow> \<Gamma> \<noteq> {} \<and> (\<forall>p\<in>\<Gamma>. actb p) \<and> actb c \<and> (\<forall>p\<in>\<Gamma>. lev p < lev c)"

interpretation LB: lean VB True cjB ngB EB GB .

lemma LB_PG: "LB.PGr p q \<longleftrightarrow> actb p \<and> actb q \<and> lev p < lev q"
proof
  assume "LB.PGr p q"
  then obtain \<Gamma> where "p \<in> \<Gamma>" "GB \<Gamma> q" unfolding LB.PGr_def by blast
  thus "actb p \<and> actb q \<and> lev p < lev q" unfolding GB_def by auto
next
  assume "actb p \<and> actb q \<and> lev p < lev q"
  hence "GB {p} q" unfolding GB_def by simp
  thus "LB.PGr p q" unfolding LB.PGr_def by blast
qed

definition qB :: pb where "qB = \<lparr>actb = True, othb = False, lev = 0\<rparr>"

theorem LB_model:
  "LB.L_FACT \<and> LB.L_CONJ \<and> LB.L_ASYM \<and> LB.L_ANTI \<and> LB.L_TRANS \<and> LB.L_CL \<and> LB.CONTINGENT
   \<and> \<not> LB.L_EX \<and> (\<forall>p. VB True p \<and> lev p = 0 \<longrightarrow> GB {p} EB)"
proof -
  have f: "LB.L_FACT" unfolding LB.L_FACT_def unfolding GB_def VB_def by auto
  have c: "LB.L_CONJ" unfolding LB.L_CONJ_def unfolding GB_def VB_def cjB_def by auto
  have as: "LB.L_ASYM" unfolding LB.L_ASYM_def LB_PG by auto
  have an: "LB.L_ANTI" unfolding LB.L_ANTI_def LB_PG by auto
  have t: "LB.L_TRANS" unfolding LB.L_TRANS_def LB_PG by auto
  have "\<exists>p. VB w p" for w by (rule exI[of _ EB]) (simp add: VB_def EB_def)
  hence cl: "LB.L_CL" unfolding LB.L_CL_def unfolding VB_def cjB_def ngB_def EB_def by auto
  have ct: "LB.CONTINGENT" unfolding LB.CONTINGENT_def
    by (rule exI[of _ qB], rule exI[of _ False]) (simp add: VB_def qB_def)
  have "VB True EB" "\<not> GB {EB} EB" unfolding VB_def GB_def EB_def by simp_all
  hence nex: "\<not> LB.L_EX" unfolding LB.L_EX_def by blast
  have pr: "\<forall>p. VB True p \<and> lev p = 0 \<longrightarrow> GB {p} EB" unfolding VB_def GB_def EB_def by simp
  show ?thesis using f c as an t cl ct nex pr by blast
qed

subsection \<open>Model LC: every premise but the conjunction rule\<close>

text \<open>The propositions of LB, with E the only grounded proposition: every non-empty set
  of actual truths grounds E and nothing else is grounded. The existential rule holds
  without restriction, the only mutual ground is of E with itself, and there is a
  contingent truth.\<close>

definition GC :: "pb set \<Rightarrow> pb \<Rightarrow> bool" where
  "GC \<Gamma> c \<longleftrightarrow> \<Gamma> \<noteq> {} \<and> (\<forall>p\<in>\<Gamma>. actb p) \<and> c = EB"

interpretation LC: lean VB True cjB ngB EB GC .

lemma LC_PG: "LC.PGr p q \<longleftrightarrow> actb p \<and> q = EB"
proof
  assume "LC.PGr p q"
  then obtain \<Gamma> where "p \<in> \<Gamma>" "GC \<Gamma> q" unfolding LC.PGr_def by blast
  thus "actb p \<and> q = EB" unfolding GC_def by auto
next
  assume "actb p \<and> q = EB"
  hence "GC {p} q" unfolding GC_def by simp
  thus "LC.PGr p q" unfolding LC.PGr_def by blast
qed

theorem LC_model:
  "LC.L_FACT \<and> LC.L_EX \<and> LC.L_ANTI \<and> LC.L_TRANS \<and> LC.L_CL \<and> LC.CONTINGENT \<and> \<not> LC.L_CONJ"
proof -
  have f: "LC.L_FACT" unfolding LC.L_FACT_def unfolding GC_def VB_def EB_def by auto
  have e: "LC.L_EX" unfolding LC.L_EX_def unfolding GC_def VB_def by simp
  have an: "LC.L_ANTI" unfolding LC.L_ANTI_def LC_PG by auto
  have t: "LC.L_TRANS" unfolding LC.L_TRANS_def LC_PG by auto
  have "\<exists>p. VB w p" for w by (rule exI[of _ EB]) (simp add: VB_def EB_def)
  hence cl: "LC.L_CL" unfolding LC.L_CL_def unfolding VB_def cjB_def ngB_def EB_def by auto
  have ct: "LC.CONTINGENT" unfolding LC.CONTINGENT_def
    by (rule exI[of _ qB], rule exI[of _ False]) (simp add: VB_def qB_def)
  have "VB True EB" "\<not> GC {EB, EB} (cjB EB EB)" unfolding VB_def GC_def EB_def cjB_def by simp_all
  hence nc: "\<not> LC.L_CONJ" unfolding LC.L_CONJ_def by blast
  show ?thesis using f e an t cl ct nc by blast
qed

end
