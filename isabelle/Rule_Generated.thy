theory Rule_Generated
  imports Woods_Models
begin

text \<open>
  Woods's substantive irreflexivity without totality facts, where grounds are only what
  the rules generate (requested by the reviewer, 2026-11-28).

  The models of Woods_Models.thy satisfy IRR.W because they contain grounding facts
  that no introduction rule delivers: in MV every non-empty set of truths grounds every
  true quantified proposition. This theory builds the opposite model, MR.

    Propositions are structured. A proposition is an atom, a negation, conjunction,
    disjunction or truth ascription of propositions, or a quantified proposition, which
    is a bound variable, a formula and an environment for the formula's other
    variables. Distinct constructions are distinct propositions.

    Truth is classical. A quantifier ranges over the two truth values, which agrees
    with ranging over all propositions because the truth value of an instance depends
    only on the truth value of what is put for the variable.

    Ground is the LEAST relation closed under the registry's full-strength
    introduction entries EX.FULL, ALL.INST, CONJ.BIN, DISJ.ONE, DISJ.BOTH, TR.FULL,
    TR.NEG, NEG.DN, NEG.DM and the structural entries TRANS.CUT and AMALG.INF. There is
    no totality fact and no other grounding fact.

  MR satisfies the package of the sentence-position puzzle and those of the other
  targets, without any irreflexivity entry. Result: IRR.W fails in MR (MR_not_IRR_W).
  The universal truth U = \<forall>p(p \<or> \<not>p) is among its own grounds, by ALL.INST, DISJ.ONE
  and TRANS.CUT, and it does not occur there vacuously: every rule-generated ground of
  U contains U or the instance U \<or> \<not>U (GR_universal), and putting another truth for U
  removes both, under every presentation of the grounds that the vacuity test allows.

  The basic reflexive facts of the existential cases, Woods's Objection 3 among them,
  are vacuous in MR (MR_existential_vacuous). Whether every reflexive fact with an existential conclusion
  is vacuous in MR is not settled here.

  Method as in Model_Certificates.thy: MR is an interpretation of the locale gsig. No
  axioms and no unfinished proofs.
\<close>

section \<open>Structured propositions\<close>

datatype rp = RA nat | RN rp | RC rp rp | RD rp rp | RT rp
  | RE nat fm "nat \<Rightarrow> rp" | RU nat fm "nat \<Rightarrow> rp" | RB nat fm "nat \<Rightarrow> rp"

text \<open>A propositional function is a closure: a variable, a formula, an environment.\<close>
datatype rf = Clo nat fm "nat \<Rightarrow> rp"

text \<open>Environments are normalised, so that a quantified proposition does not depend on
  the values of variables that do not occur free in its formula.\<close>
definition nrm :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> rp) \<Rightarrow> nat \<Rightarrow> rp" where
  "nrm x a v = (\<lambda>y. if y \<in> fv a - {x} then v y else RA 0)"

primrec dR :: "(nat \<Rightarrow> rp) \<Rightarrow> fm \<Rightarrow> rp" where
  "dR v (Var n) = v n"
| "dR v (Cst n) = RA n"
| "dR v (Neg a) = RN (dR v a)"
| "dR v (Conj a b) = RC (dR v a) (dR v b)"
| "dR v (Disj a b) = RD (dR v a) (dR v b)"
| "dR v (Tr a) = RT (dR v a)"
| "dR v (Ex x a) = RE x a (nrm x a v)"
| "dR v (All x a) = RU x a (nrm x a v)"
| "dR v (BigC x a) = RB x a (nrm x a v)"

text \<open>Truth value of a formula under an assignment of truth values.\<close>
primrec tvR :: "(nat \<Rightarrow> bool) \<Rightarrow> fm \<Rightarrow> bool" where
  "tvR e (Var n) = e n"
| "tvR e (Cst n) = True"
| "tvR e (Neg a) = (\<not> tvR e a)"
| "tvR e (Conj a b) = (tvR e a \<and> tvR e b)"
| "tvR e (Disj a b) = (tvR e a \<or> tvR e b)"
| "tvR e (Tr a) = tvR e a"
| "tvR e (Ex x a) = (\<exists>b. tvR (e(x:=b)) a)"
| "tvR e (All x a) = (\<forall>b. tvR (e(x:=b)) a)"
| "tvR e (BigC x a) = (\<forall>b. tvR (e(x:=b)) a \<longrightarrow> b)"

primrec TR :: "rp \<Rightarrow> bool" where
  "TR (RA n) = True"
| "TR (RN p) = (\<not> TR p)"
| "TR (RC p q) = (TR p \<and> TR q)"
| "TR (RD p q) = (TR p \<or> TR q)"
| "TR (RT p) = TR p"
| "TR (RE x a v) = (\<exists>b. tvR ((\<lambda>y. TR (v y))(x:=b)) a)"
| "TR (RU x a v) = (\<forall>b. tvR ((\<lambda>y. TR (v y))(x:=b)) a)"
| "TR (RB x a v) = (\<forall>b. tvR ((\<lambda>y. TR (v y))(x:=b)) a \<longrightarrow> b)"

primrec appR :: "rf \<Rightarrow> rp \<Rightarrow> rp" where "appR (Clo x a v) p = dR (v(x:=p)) a"
primrec exqR :: "rf \<Rightarrow> rp" where "exqR (Clo x a v) = RE x a v"
primrec allqR :: "rf \<Rightarrow> rp" where "allqR (Clo x a v) = RU x a v"
primrec bigR :: "rf \<Rightarrow> rp" where "bigR (Clo x a v) = RB x a v"
definition lamR :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> rp) \<Rightarrow> rf" where "lamR x a v = Clo x a (nrm x a v)"
definition admR :: "rf \<Rightarrow> bool" where "admR f \<longleftrightarrow> (\<exists>x a v. f = lamR x a v)"

lemma nrm_cong: "\<forall>y\<in>fv a - {x}. v y = w y \<Longrightarrow> nrm x a v = nrm x a w"
  by (auto simp: nrm_def fun_eq_iff)

lemma tv_fv: "(\<forall>y\<in>fv a. e y = e' y) \<Longrightarrow> tvR e a = tvR e' a"
proof (induct a arbitrary: e e')
  case (Ex x a)
  have "\<And>b. tvR (e(x:=b)) a = tvR (e'(x:=b)) a"
    by (rule Ex.hyps) (use Ex.prems in auto)
  then show ?case by simp
next
  case (All x a)
  have "\<And>b. tvR (e(x:=b)) a = tvR (e'(x:=b)) a"
    by (rule All.hyps) (use All.prems in auto)
  then show ?case by simp
next
  case (BigC x a)
  have "\<And>b. tvR (e(x:=b)) a = tvR (e'(x:=b)) a"
    by (rule BigC.hyps) (use BigC.prems in auto)
  then show ?case by simp
next
  case (Neg a)
  have "tvR e a = tvR e' a" by (rule Neg.hyps) (use Neg.prems in auto)
  then show ?case by simp
next
  case (Tr a)
  have "tvR e a = tvR e' a" by (rule Tr.hyps) (use Tr.prems in auto)
  then show ?case by simp
next
  case (Conj a b)
  have "tvR e a = tvR e' a" by (rule Conj.hyps(1)) (use Conj.prems in auto)
  moreover have "tvR e b = tvR e' b" by (rule Conj.hyps(2)) (use Conj.prems in auto)
  ultimately show ?case by simp
next
  case (Disj a b)
  have "tvR e a = tvR e' a" by (rule Disj.hyps(1)) (use Disj.prems in auto)
  moreover have "tvR e b = tvR e' b" by (rule Disj.hyps(2)) (use Disj.prems in auto)
  ultimately show ?case by simp
qed simp_all

lemma dR_fv: "(\<forall>y\<in>fv a. v y = w y) \<Longrightarrow> dR v a = dR w a"
proof (induct a)
  case (Ex x a)
  have "nrm x a v = nrm x a w" by (rule nrm_cong) (use Ex.prems in auto)
  then show ?case by simp
next
  case (All x a)
  have "nrm x a v = nrm x a w" by (rule nrm_cong) (use All.prems in auto)
  then show ?case by simp
next
  case (BigC x a)
  have "nrm x a v = nrm x a w" by (rule nrm_cong) (use BigC.prems in auto)
  then show ?case by simp
next
  case (Neg a)
  have "dR v a = dR w a" by (rule Neg.hyps) (use Neg.prems in auto)
  then show ?case by simp
next
  case (Tr a)
  have "dR v a = dR w a" by (rule Tr.hyps) (use Tr.prems in auto)
  then show ?case by simp
next
  case (Conj a b)
  have "dR v a = dR w a" by (rule Conj.hyps(1)) (use Conj.prems in auto)
  moreover have "dR v b = dR w b" by (rule Conj.hyps(2)) (use Conj.prems in auto)
  ultimately show ?case by simp
next
  case (Disj a b)
  have "dR v a = dR w a" by (rule Disj.hyps(1)) (use Disj.prems in auto)
  moreover have "dR v b = dR w b" by (rule Disj.hyps(2)) (use Disj.prems in auto)
  ultimately show ?case by simp
qed simp_all

text \<open>Truth is compositional: the truth value of what a formula denotes is its truth
  value under the truth values of what its variables denote.\<close>
lemma tv_nrm: "tvR ((\<lambda>y. TR (nrm x a v y))(x:=b)) a = tvR ((\<lambda>y. TR (v y))(x:=b)) a"
  by (rule tv_fv) (simp add: nrm_def)

lemma truth_den: "TR (dR v a) = tvR (\<lambda>y. TR (v y)) a"
  by (induct a arbitrary: v) (simp_all add: tv_nrm)

lemma upd_truth: "(\<lambda>y. TR ((v(x:=p)) y)) = (\<lambda>y. TR (v y))(x:=TR p)"
  by (rule ext) simp

lemma app_truth: "TR (appR (Clo x a v) p) = tvR ((\<lambda>y. TR (v y))(x:=TR p)) a"
  by (simp only: appR.simps truth_den upd_truth)

lemma tv_real: "\<exists>p. TR p = b"
proof (cases b)
  case True thus ?thesis by (intro exI[of _ "RA 0"]) simp
next
  case False thus ?thesis by (intro exI[of _ "RN (RA 0)"]) simp
qed

lemma bool_all: "(\<forall>b::bool. P b) \<longleftrightarrow> (\<forall>p. P (TR p))"
proof
  assume "\<forall>b. P b" thus "\<forall>p. P (TR p)" by simp
next
  assume a: "\<forall>p. P (TR p)"
  show "\<forall>b. P b"
  proof
    fix b obtain p where "TR p = b" using tv_real by blast
    with a show "P b" by auto
  qed
qed

lemma bool_ex: "(\<exists>b::bool. P b) \<longleftrightarrow> (\<exists>p. P (TR p))"
proof
  assume "\<exists>b. P b"
  then obtain b where b: "P b" ..
  obtain p where "TR p = b" using tv_real by blast
  with b show "\<exists>p. P (TR p)" by auto
next
  assume "\<exists>p. P (TR p)" thus "\<exists>b. P b" by blast
qed

lemma ex_truth: "TR (exqR f) = (\<exists>p. TR (appR f p))"
proof (cases f)
  case (Clo x a v)
  have "(\<exists>b. tvR ((\<lambda>y. TR (v y))(x:=b)) a) = (\<exists>p. tvR ((\<lambda>y. TR (v y))(x:=TR p)) a)"
    by (rule bool_ex)
  thus ?thesis unfolding Clo by (simp only: exqR.simps TR.simps app_truth)
qed

lemma all_truth: "TR (allqR f) = (\<forall>p. TR (appR f p))"
proof (cases f)
  case (Clo x a v)
  have "(\<forall>b. tvR ((\<lambda>y. TR (v y))(x:=b)) a) = (\<forall>p. tvR ((\<lambda>y. TR (v y))(x:=TR p)) a)"
    by (rule bool_all)
  thus ?thesis unfolding Clo by (simp only: allqR.simps TR.simps app_truth)
qed

lemma big_truth: "TR (bigR f) = (\<forall>p. TR (appR f p) \<longrightarrow> TR p)"
proof (cases f)
  case (Clo x a v)
  have "(\<forall>b. tvR ((\<lambda>y. TR (v y))(x:=b)) a \<longrightarrow> b)
      = (\<forall>p. tvR ((\<lambda>y. TR (v y))(x:=TR p)) a \<longrightarrow> TR p)"
    by (rule bool_all)
  thus ?thesis unfolding Clo by (simp only: bigR.simps TR.simps app_truth)
qed

section \<open>Rule-generated ground\<close>

text \<open>The least relation closed under the rules. Each rule is the registry entry of the
  same name, with its truth and admissibility conditions.\<close>
inductive GR :: "rp set \<Rightarrow> rp \<Rightarrow> bool" where
  ex: "admR f \<Longrightarrow> TR (appR f a) \<Longrightarrow> GR {appR f a} (exqR f)"
| all: "admR f \<Longrightarrow> \<forall>a. TR (appR f a) \<Longrightarrow> GR (range (appR f)) (allqR f)"
| conj: "TR p \<Longrightarrow> TR q \<Longrightarrow> GR {p, q} (RC p q)"
| disjL: "TR p \<Longrightarrow> GR {p} (RD p q)"
| disjR: "TR q \<Longrightarrow> GR {q} (RD p q)"
| disjB: "TR p \<Longrightarrow> TR q \<Longrightarrow> GR {p, q} (RD p q)"
| tr: "TR p \<Longrightarrow> GR {p} (RT p)"
| trneg: "TR (RN p) \<Longrightarrow> GR {RN p} (RN (RT p))"
| dn: "TR p \<Longrightarrow> GR {p} (RN (RN p))"
| dm1: "TR (RN p) \<Longrightarrow> GR {RN p} (RN (RC p q))"
| dm2: "TR (RN q) \<Longrightarrow> GR {RN q} (RN (RC p q))"
| dm3: "TR (RN p) \<Longrightarrow> TR (RN q) \<Longrightarrow> GR {RN p, RN q} (RN (RD p q))"
| cut: "GR \<Gamma> q \<Longrightarrow> \<Delta> \<subseteq> \<Gamma> \<Longrightarrow> \<forall>p\<in>\<Delta>. GR (H p) p \<Longrightarrow> GR ((\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)) q"
| amalg: "F \<noteq> {} \<Longrightarrow> \<forall>\<Gamma>\<in>F. GR \<Gamma> p \<Longrightarrow> GR (\<Union>F) p"

interpretation MR: gsig TR RA RN RC RD RT appR exqR allqR bigR lamR admR GR "\<lambda>_. RA 0" "RA 0" .

lemma q_lam: "exqR (lamR x a v) = RE x a (nrm x a v)" "allqR (lamR x a v) = RU x a (nrm x a v)"
  "bigR (lamR x a v) = RB x a (nrm x a v)"
  unfolding lamR_def by simp_all

lemma MR_den: "MR.den = dR"
proof (intro ext)
  fix v a show "MR.den v a = dR v a"
    by (induction a) (simp_all add: q_lam)
qed

lemma GR_fact: "GR \<Gamma> q \<Longrightarrow> TR q \<and> (\<forall>p\<in>\<Gamma>. TR p)"
proof (induction rule: GR.induct)
  case (ex f a) thus ?case using ex_truth by auto
next
  case (all f) thus ?case using all_truth by auto
next
  case (cut \<Gamma> q \<Delta> H) thus ?case by blast
next
  case (amalg F p) thus ?case by blast
qed simp_all

section \<open>MR is a model of the packages without an irreflexivity entry\<close>

lemma MR_BETA_ID: "MR.BETA_ID"
proof -
  have "appR (lamR x a v) p = dR (v(x:=p)) a" for x a v p
  proof -
    have "dR ((nrm x a v)(x:=p)) a = dR (v(x:=p)) a" by (rule dR_fv) (simp add: nrm_def)
    thus ?thesis by (simp add: lamR_def)
  qed
  thus ?thesis by (simp add: MR.BETA_ID_def MR_den)
qed

lemma MR_core: "MR.FACT" "MR.LAM_CORE" "MR.C3d"
proof -
  show "MR.FACT" unfolding MR.FACT_def using GR_fact by blast
  have "lamR x a v = lamR x a w" if "\<forall>y\<in>fv a - {x}. v y = w y" for x a v w
    using nrm_cong[OF that] by (simp add: lamR_def)
  thus "MR.LAM_CORE" unfolding MR.LAM_CORE_def using MR_BETA_ID[unfolded MR.BETA_ID_def]
    by metis
  show "MR.C3d" by (simp add: MR.C3d_def admR_def)
qed

lemma MR_W: "MR.W_ID" "MR.W_TR" "MR.W_EM" "MR.W_TEM"
  unfolding MR.W_ID_def MR.W_TR_def MR.W_EM_def MR.W_TEM_def admR_def
            MR.f_id_def MR.f_tr_def MR.f_em_def MR.f_tem_def by blast+

lemma MR_classical: "MR.CL_PROP" "MR.CL_QUANT" "MR.TS_FULL"
  by (simp_all add: MR.CL_PROP_def MR.CL_QUANT_def MR.TS_FULL_def MR.sat_def
        ex_truth all_truth big_truth)

lemma MR_intro: "MR.EX_FULL" "MR.ALL_INST" "MR.CONJ_BIN" "MR.DISJ_ONE" "MR.DISJ_BOTH"
  "MR.TR_FULL" "MR.TR_NEG" "MR.NEG_DN" "MR.NEG_DM"
proof -
  show "MR.EX_FULL" unfolding MR.EX_FULL_def using GR.ex by blast
  show "MR.ALL_INST" unfolding MR.ALL_INST_def MR.inst_def using GR.all by blast
  show "MR.CONJ_BIN" unfolding MR.CONJ_BIN_def using GR.conj by blast
  show "MR.DISJ_ONE" unfolding MR.DISJ_ONE_def using GR.disjL GR.disjR by blast
  show "MR.DISJ_BOTH" unfolding MR.DISJ_BOTH_def using GR.disjB by blast
  show "MR.TR_FULL" unfolding MR.TR_FULL_def using GR.tr by blast
  show "MR.TR_NEG" unfolding MR.TR_NEG_def using GR.trneg by blast
  show "MR.NEG_DN" unfolding MR.NEG_DN_def using GR.dn by blast
  show "MR.NEG_DM" unfolding MR.NEG_DM_def using GR.dm1 GR.dm2 GR.dm3 by blast
qed

lemma MR_structural: "MR.TRANS_CUT" "MR.AMALG_INF" "MR.TRANS_P"
proof -
  show "MR.TRANS_CUT" unfolding MR.TRANS_CUT_def using GR.cut by blast
  show "MR.AMALG_INF" unfolding MR.AMALG_INF_def using GR.amalg by blast
  show "MR.TRANS_P" unfolding MR.TRANS_P_def
  proof (intro allI impI)
    fix p q r assume "MR.PG p q \<and> MR.PG q r"
    then obtain \<Gamma>1 \<Gamma>2 where a: "p \<in> \<Gamma>1" "GR \<Gamma>1 q" "q \<in> \<Gamma>2" "GR \<Gamma>2 r"
      unfolding MR.PG_def by blast
    let ?\<Gamma> = "(\<Gamma>2 - {q}) \<union> (\<Union>s\<in>{q}. \<Gamma>1)"
    have g: "GR ?\<Gamma> r" by (rule GR.cut[OF a(4)]) (use a in auto)
    have m: "p \<in> ?\<Gamma>" using a(1) by simp
    have "\<exists>\<Gamma>. p \<in> \<Gamma> \<and> GR \<Gamma> r" by (rule exI[of _ ?\<Gamma>]) (rule conjI[OF m g])
    thus "MR.PG p r" unfolding MR.PG_def .
  qed
qed

section \<open>The universal truth and its rule-generated grounds\<close>

definition aEM :: fm where "aEM = Disj (Var 0) (Neg (Var 0))"
definition fEM :: rf where "fEM = Clo 0 aEM (\<lambda>_. RA 0)"
definition UR :: rp where "UR = RU 0 aEM (\<lambda>_. RA 0)"
definition VR :: rp where "VR = RD UR (RN UR)"

lemma nrm_em: "nrm 0 aEM v = (\<lambda>_. RA 0)" by (simp add: nrm_def aEM_def fun_eq_iff)
lemma fv_aEM: "fv aEM = {0}" by (simp add: aEM_def)
lemma fEM_lam: "fEM = lamR 0 aEM v" by (simp add: fEM_def lamR_def nrm_em)
lemma fEM_f_em: "MR.f_em = fEM" unfolding MR.f_em_def using fEM_lam[symmetric] by (simp add: aEM_def)
lemma fEM_adm: "admR fEM" unfolding admR_def using fEM_lam by blast
lemma fEM_app: "appR fEM p = RD p (RN p)" by (simp add: fEM_def aEM_def)
lemma fEM_all: "allqR fEM = UR" by (simp add: fEM_def UR_def)
lemma UR_true: "TR UR" by (simp add: UR_def aEM_def)
lemma UR_VR: "UR \<noteq> VR" by (simp add: UR_def VR_def)
lemma VR_inst: "VR = appR fEM UR" by (simp add: fEM_app VR_def)

text \<open>The reflexive fact. All instances of p \<or> \<not>p ground U (ALL.INST); U grounds the
  instance U \<or> \<not>U (DISJ.ONE); so the instances other than that one, with U, ground U
  (TRANS.CUT).\<close>
definition G0 :: "rp set" where "G0 = (range (appR fEM) - {VR}) \<union> {UR}"

lemma G0_ground: "GR G0 UR" and G0_mem: "UR \<in> G0" and G0_VR: "VR \<notin> G0"
proof -
  have a: "GR (range (appR fEM)) UR"
    using GR.all[OF fEM_adm] fEM_all by (simp add: fEM_app)
  have b: "{VR} \<subseteq> range (appR fEM)" using VR_inst by blast
  have c: "\<forall>p\<in>{VR}. GR ((\<lambda>_. {UR}) p) p" using GR.disjL[OF UR_true, of "RN UR"] by (simp add: VR_def)
  have "GR ((range (appR fEM) - {VR}) \<union> (\<Union>p\<in>{VR}. (\<lambda>_. {UR}) p)) UR"
    by (rule GR.cut[OF a b c])
  thus "GR G0 UR" by (simp add: G0_def)
  show "UR \<in> G0" by (simp add: G0_def)
  show "VR \<notin> G0" using UR_VR by (simp add: G0_def)
qed

text \<open>Every rule-generated ground of U, and of the instance U \<or> \<not>U, contains U or that
  instance. The only rule whose conclusion is U is ALL.INST for the function p \<or> \<not>p,
  whose instances include U \<or> \<not>U; the only rule whose conclusion is U \<or> \<not>U and whose
  condition holds is DISJ.ONE from U; the structural rules preserve the property.\<close>
lemma GR_universal: "GR \<Gamma> q \<Longrightarrow> q = UR \<or> q = VR \<Longrightarrow> UR \<in> \<Gamma> \<or> VR \<in> \<Gamma>"
proof (induction rule: GR.induct)
  case (ex f a) thus ?case by (cases f) (simp add: UR_def VR_def)
next
  case (all f)
  show ?case
  proof (cases f)
    case (Clo x a v)
    have "allqR f = UR" using all.prems by (simp add: Clo VR_def)
    hence "f = fEM" by (simp add: Clo UR_def fEM_def)
    have "VR \<in> range (appR fEM)" unfolding VR_inst by (rule rangeI)
    thus ?thesis using \<open>f = fEM\<close> by blast
  qed
next
  case (conj p q) thus ?case by (simp add: UR_def VR_def)
next
  case (disjL p q) thus ?case by (simp add: UR_def VR_def)
next
  case (disjR q p)
  have "q \<noteq> RN UR" using disjR.hyps UR_true by auto
  thus ?case using disjR.prems by (simp add: UR_def VR_def)
next
  case (disjB p q) thus ?case by (simp add: UR_def VR_def)
next
  case (tr p) thus ?case by (simp add: UR_def VR_def)
next
  case (trneg p) thus ?case by (simp add: UR_def VR_def)
next
  case (dn p) thus ?case by (simp add: UR_def VR_def)
next
  case (dm1 p q) thus ?case by (simp add: UR_def VR_def)
next
  case (dm2 q p) thus ?case by (simp add: UR_def VR_def)
next
  case (dm3 p q) thus ?case by (simp add: UR_def VR_def)
next
  case (cut \<Gamma> q \<Delta> H)
  obtain m where m: "m \<in> \<Gamma>" "m = UR \<or> m = VR" using cut by blast
  show ?case
  proof (cases "m \<in> \<Delta>")
    case False thus ?thesis using m by blast
  next
    case True
    hence "UR \<in> H m \<or> VR \<in> H m" using cut m(2) by blast
    thus ?thesis using True by blast
  qed
next
  case (amalg F p)
  obtain \<Gamma> where "\<Gamma> \<in> F" using amalg by blast
  thus ?case using amalg by blast
qed

section \<open>The vacuity test fails for the reflexive universal fact\<close>

text \<open>Two facts about presentations. If a formula denotes U once B, a proposition other
  than U, is put for the marked variable z, then it has a subformula without z that
  denotes U; such a subformula is what clause (iii) of vacW forbids. Likewise for the
  instance U \<or> \<not>U, unless the formula does not contain z at all.\<close>
lemma den_UR:
  assumes "dR (v(z:=B)) \<phi> = UR" "B \<noteq> UR"
  shows "\<exists>\<psi>\<in>subf \<phi>. z \<notin> fv \<psi> \<and> dR (v(z:=UR)) \<psi> = UR"
proof (cases \<phi>)
  case (Var y)
  have "y \<noteq> z" using assms Var by auto
  hence "z \<notin> fv \<phi> \<and> dR (v(z:=UR)) \<phi> = UR" using assms(1) Var by simp
  thus ?thesis using subf_self by blast
next
  case (All x a)
  have e: "x = 0" "a = aEM" using assms(1) All by (simp_all add: UR_def)
  have "z \<notin> fv \<phi> \<and> dR (v(z:=UR)) \<phi> = UR"
    unfolding All e by (simp add: nrm_em UR_def fv_aEM)
  thus ?thesis using subf_self by blast
qed (use assms(1) in \<open>simp_all add: UR_def\<close>)

lemma den_VR:
  assumes "dR (v(z:=B)) \<phi> = VR" "B \<noteq> UR" "B \<noteq> VR"
  shows "(\<exists>\<psi>\<in>subf \<phi>. z \<notin> fv \<psi> \<and> dR (v(z:=UR)) \<psi> = UR)
       \<or> (z \<notin> fv \<phi> \<and> dR (v(z:=UR)) \<phi> = VR)"
proof (cases \<phi>)
  case (Var y)
  have "y \<noteq> z" using assms Var by auto
  thus ?thesis using assms(1) Var by simp
next
  case (Disj \<alpha> \<beta>)
  have "dR (v(z:=B)) \<alpha> = UR" using assms(1) Disj by (simp add: VR_def)
  then obtain \<psi> where "\<psi> \<in> subf \<alpha>" "z \<notin> fv \<psi> \<and> dR (v(z:=UR)) \<psi> = UR"
    using den_UR assms(2) by blast
  thus ?thesis unfolding Disj by auto
qed (use assms(1) in \<open>simp_all add: VR_def\<close>)

theorem MR_not_vacuous: "\<not> MR.vacW UR G0 UR"
proof
  assume "MR.vacW UR G0 UR"
  then obtain \<Phi> v z where
        pres: "G0 = (\<lambda>\<phi>. dR (v(z:=UR)) \<phi>) ` \<Phi>"
    and mark: "\<forall>\<phi>\<in>\<Phi>. \<forall>\<psi>\<in>subf \<phi>. z \<notin> fv \<psi> \<longrightarrow> dR (v(z:=UR)) \<psi> \<noteq> UR"
    and sub: "\<forall>B. (\<forall>\<phi>\<in>\<Phi>. TR (dR (v(z:=B)) \<phi>)) \<longrightarrow> GR ((\<lambda>\<phi>. dR (v(z:=B)) \<phi>) ` \<Phi>) UR"
    unfolding MR.vacW_def MR_den by blast
  let ?B = "RA 1"
  have B: "?B \<noteq> UR" "?B \<noteq> VR" "TR ?B" by (simp_all add: UR_def VR_def)
  have env: "(\<lambda>y. TR ((v(z:=?B)) y)) = (\<lambda>y. TR ((v(z:=UR)) y))"
    by (rule ext) (simp add: UR_true)
  have true: "\<forall>\<phi>\<in>\<Phi>. TR (dR (v(z:=?B)) \<phi>)"
  proof
    fix \<phi> assume "\<phi> \<in> \<Phi>"
    hence "dR (v(z:=UR)) \<phi> \<in> G0" using pres by blast
    hence "TR (dR (v(z:=UR)) \<phi>)" using GR_fact[OF G0_ground] by blast
    thus "TR (dR (v(z:=?B)) \<phi>)" by (simp only: truth_den env)
  qed
  have none: "dR (v(z:=?B)) \<phi> \<noteq> UR \<and> dR (v(z:=?B)) \<phi> \<noteq> VR" if ph: "\<phi> \<in> \<Phi>" for \<phi>
  proof (intro conjI notI)
    assume "dR (v(z:=?B)) \<phi> = UR"
    from den_UR[OF this B(1)] show False using mark ph by blast
  next
    assume "dR (v(z:=?B)) \<phi> = VR"
    from den_VR[OF this B(1) B(2)] have e: "dR (v(z:=UR)) \<phi> = VR"
      using mark ph by blast
    have "dR (v(z:=UR)) \<phi> \<in> (\<lambda>\<phi>. dR (v(z:=UR)) \<phi>) ` \<Phi>" using ph by (rule imageI)
    hence "VR \<in> G0" unfolding e pres[symmetric] .
    thus False using G0_VR by blast
  qed
  have "GR ((\<lambda>\<phi>. dR (v(z:=?B)) \<phi>) ` \<Phi>) UR" using sub true by blast
  hence "UR \<in> (\<lambda>\<phi>. dR (v(z:=?B)) \<phi>) ` \<Phi> \<or> VR \<in> (\<lambda>\<phi>. dR (v(z:=?B)) \<phi>) ` \<Phi>"
    using GR_universal by blast
  then obtain \<phi> where "\<phi> \<in> \<Phi>" "dR (v(z:=?B)) \<phi> = UR \<or> dR (v(z:=?B)) \<phi> = VR" by auto
  thus False using none by blast
qed

theorem MR_not_IRR_W: "\<not> MR.IRR_W"
  unfolding MR.IRR_W_def using G0_ground G0_mem MR_not_vacuous by blast

text \<open>The same for the control entry IRR.MEM, which replaces the member only, and for
  strict irreflexivity.\<close>
theorem MR_not_IRR_MEM: "\<not> MR.IRR_MEM"
proof
  assume "MR.IRR_MEM"
  hence "MR.vacM G0 UR UR" unfolding MR.IRR_MEM_def using G0_ground G0_mem by blast
  moreover have "TR (RA 1)" by simp
  ultimately have "GR (insert (RA 1) (G0 - {UR})) UR" unfolding MR.vacM_def by blast
  hence "UR \<in> insert (RA 1) (G0 - {UR}) \<or> VR \<in> insert (RA 1) (G0 - {UR})"
    using GR_universal by blast
  thus False using G0_VR by (simp add: UR_def VR_def)
qed

theorem MR_not_IRR_F: "\<not> MR.IRR_F"
  unfolding MR.IRR_F_def using G0_ground G0_mem by blast

section \<open>The existential cases\<close>

text \<open>Kr\"amer's case, "something is true", and Woods's Objection 3. The existential
  truth grounds itself, and every truth grounds it by the rules alone, so the reflexive
  fact is vacuous in MR. This covers these three reflexive facts only.\<close>
definition fID :: rf where "fID = Clo 0 (Var 0) (\<lambda>_. RA 0)"
definition fTR :: rf where "fTR = Clo 0 (Tr (Var 0)) (\<lambda>_. RA 0)"

lemma fID_facts: "admR fID" "appR fID p = p"
proof -
  have "nrm 0 (Var 0) v = (\<lambda>_. RA 0)" for v by (simp add: nrm_def fun_eq_iff)
  hence "fID = lamR 0 (Var 0) (\<lambda>_. RA 0)" by (simp add: fID_def lamR_def)
  thus "admR fID" unfolding admR_def by blast
  show "appR fID p = p" by (simp add: fID_def)
qed

lemma fTR_facts: "admR fTR" "appR fTR p = RT p"
proof -
  have "nrm 0 (Tr (Var 0)) v = (\<lambda>_. RA 0)" for v by (simp add: nrm_def fun_eq_iff)
  hence "fTR = lamR 0 (Tr (Var 0)) (\<lambda>_. RA 0)" by (simp add: fTR_def lamR_def)
  thus "admR fTR" unfolding admR_def by blast
  show "appR fTR p = RT p" by (simp add: fTR_def)
qed

lemma every_truth_grounds_ex: "TR B \<Longrightarrow> GR {B} (exqR fID)"
  using GR.ex[OF fID_facts(1), of B] by (simp add: fID_facts(2))

lemma every_truth_grounds_true: "TR B \<Longrightarrow> GR {B} (exqR fTR)"
proof -
  assume B: "TR B"
  have a: "GR {RT B} (exqR fTR)" using GR.ex[OF fTR_facts(1), of B] B by (simp add: fTR_facts(2))
  have "GR (({RT B} - {RT B}) \<union> (\<Union>p\<in>{RT B}. (\<lambda>_. {B}) p)) (exqR fTR)"
    by (rule GR.cut[OF a]) (use GR.tr[OF B] in auto)
  thus ?thesis by simp
qed

text \<open>Woods's Objection 3 (p. 643): the existential \<exists>p(p \<or> A), for any proposition A.
  Its instance at itself is grounded by it (DISJ.ONE), so it is among its own grounds;
  and any truth B grounds B \<or> A, an instance, hence the existential.\<close>
definition fOR :: "rp \<Rightarrow> rf" where
  "fOR A = lamR 0 (Disj (Var 0) (Var 1)) ((\<lambda>_. RA 0)(1 := A))"

lemma fOR_facts: "admR (fOR A)" "appR (fOR A) p = RD p A"
proof -
  show "admR (fOR A)" unfolding admR_def fOR_def by blast
  have "appR (lamR x a v) q = dR (v(x:=q)) a" for x a v q
    using MR_BETA_ID unfolding MR.BETA_ID_def MR_den by blast
  thus "appR (fOR A) p = RD p A" unfolding fOR_def by simp
qed

lemma every_truth_grounds_or: "TR B \<Longrightarrow> GR {B} (exqR (fOR A))"
proof -
  assume B: "TR B"
  have a: "GR {RD B A} (exqR (fOR A))"
    using GR.ex[OF fOR_facts(1)[of A], of B] B by (simp add: fOR_facts(2))
  have "GR (({RD B A} - {RD B A}) \<union> (\<Union>p\<in>{RD B A}. (\<lambda>_. {B}) p)) (exqR (fOR A))"
    by (rule GR.cut[OF a]) (use GR.disjL[OF B, of A] in auto)
  thus ?thesis by simp
qed

lemma singleton_vacuous:
  assumes "\<And>B. TR B \<Longrightarrow> GR {B} c"
  shows "MR.vacW c {c} c"
proof -
  have "{c} = (\<lambda>\<phi>. dR ((\<lambda>_. RA 0)(0:=c)) \<phi>) ` {Var 0}" by simp
  moreover have "\<exists>\<phi>\<in>{Var 0}. (0::nat) \<in> fv \<phi>" by simp
  moreover have "\<forall>\<phi>\<in>{Var 0}. \<forall>\<psi>\<in>subf \<phi>. (0::nat) \<notin> fv \<psi> \<longrightarrow> dR ((\<lambda>_. RA 0)(0:=c)) \<psi> \<noteq> c"
    by simp
  moreover have "\<forall>B. (\<forall>\<phi>\<in>{Var 0}. TR (dR ((\<lambda>_. RA 0)(0:=B)) \<phi>))
                   \<longrightarrow> GR ((\<lambda>\<phi>. dR ((\<lambda>_. RA 0)(0:=B)) \<phi>) ` {Var 0}) c"
    using assms by simp
  ultimately have "{c} = (\<lambda>\<phi>. dR ((\<lambda>_. RA 0)(0:=c)) \<phi>) ` {Var 0}
    \<and> (\<exists>\<phi>\<in>{Var 0}. (0::nat) \<in> fv \<phi>)
    \<and> (\<forall>\<phi>\<in>{Var 0}. \<forall>\<psi>\<in>subf \<phi>. (0::nat) \<notin> fv \<psi> \<longrightarrow> dR ((\<lambda>_. RA 0)(0:=c)) \<psi> \<noteq> c)
    \<and> (\<forall>B. (\<forall>\<phi>\<in>{Var 0}. TR (dR ((\<lambda>_. RA 0)(0:=B)) \<phi>))
                   \<longrightarrow> GR ((\<lambda>\<phi>. dR ((\<lambda>_. RA 0)(0:=B)) \<phi>) ` {Var 0}) c)" by blast
  thus ?thesis unfolding MR.vacW_def MR_den
    by (intro exI[of _ "{Var 0}"] exI[of _ "\<lambda>_. RA 0"] exI[of _ "0::nat"])
qed

theorem MR_existential_vacuous:
  "GR {exqR fID} (exqR fID) \<and> MR.vacW (exqR fID) {exqR fID} (exqR fID)"
  "GR {exqR fTR} (exqR fTR) \<and> MR.vacW (exqR fTR) {exqR fTR} (exqR fTR)"
  "GR {exqR (fOR A)} (exqR (fOR A)) \<and> MR.vacW (exqR (fOR A)) {exqR (fOR A)} (exqR (fOR A))"
proof -
  have t1: "TR (exqR fID)" unfolding ex_truth by (rule exI[of _ "RA 0"]) (simp add: fID_facts(2))
  have t2: "TR (exqR fTR)" unfolding ex_truth by (rule exI[of _ "RA 0"]) (simp add: fTR_facts(2))
  have v1: "MR.vacW (exqR fID) {exqR fID} (exqR fID)"
    by (rule singleton_vacuous) (rule every_truth_grounds_ex)
  have v2: "MR.vacW (exqR fTR) {exqR fTR} (exqR fTR)"
    by (rule singleton_vacuous) (rule every_truth_grounds_true)
  show "GR {exqR fID} (exqR fID) \<and> MR.vacW (exqR fID) {exqR fID} (exqR fID)"
    using every_truth_grounds_ex[OF t1] v1 by (rule conjI)
  show "GR {exqR fTR} (exqR fTR) \<and> MR.vacW (exqR fTR) {exqR fTR} (exqR fTR)"
    using every_truth_grounds_true[OF t2] v2 by (rule conjI)
  have t3: "TR (exqR (fOR A))" unfolding ex_truth
    by (rule exI[of _ "RA 0"]) (simp add: fOR_facts(2))
  have v3: "MR.vacW (exqR (fOR A)) {exqR (fOR A)} (exqR (fOR A))"
    by (rule singleton_vacuous) (rule every_truth_grounds_or)
  show "GR {exqR (fOR A)} (exqR (fOR A)) \<and> MR.vacW (exqR (fOR A)) {exqR (fOR A)} (exqR (fOR A))"
    using every_truth_grounds_or[OF t3] v3 by (rule conjI)
qed

section \<open>Non-triviality\<close>

lemma GR_no_atom: "GR \<Gamma> q \<Longrightarrow> q \<noteq> RA n"
proof (induction rule: GR.induct)
  case (ex f a) thus ?case by (cases f) simp
next
  case (all f) thus ?case by (cases f) simp
next
  case (amalg F p) thus ?case by blast
qed simp_all

lemma MR_levels: "MR.N1" "MR.N2" "MR.N4_pairs" "MR.N5_chain"
proof -
  have g: "GR {p} (RT p)" if "TR p" for p using GR.tr[OF that] .
  show n1: "MR.N1" unfolding MR.N1_def using g[of "RA 0"] by auto
  have "\<exists>a b c. distinct [a, b, c] \<and> TR a \<and> TR b \<and> TR c"
    by (rule exI[of _ "RA 0"], rule exI[of _ "RA 1"], rule exI[of _ "RA 2"]) simp
  thus "MR.N2" unfolding MR.N2_def using n1 by blast
  have "{RA 0} \<in> {\<Gamma>. GR \<Gamma> (RN (RN (RA 0)))}" using GR.dn[of "RA 0"] by simp
  moreover have "{RA 0} \<notin> {\<Gamma>. GR \<Gamma> (RA 0)}" using GR_no_atom by blast
  ultimately have "MR.N4_pair (RA 0) (RN (RN (RA 0)))" unfolding MR.N4_pair_def by auto
  thus "MR.N4_pairs" by (rule MR.N4_dn)
  have pg: "MR.PG p (RT p)" if "TR p" for p unfolding MR.PG_def using g[OF that] by blast
  show "MR.N5_chain" unfolding MR.N5_chain_def
    by (intro exI[of _ "RA 0"] exI[of _ "RT (RA 0)"] exI[of _ "RT (RT (RA 0))"]
          exI[of _ "RT (RT (RT (RA 0)))"]) (simp add: pg)
qed

lemma GR_nonempty: "GR \<Gamma> q \<Longrightarrow> \<Gamma> \<noteq> {}"
proof (induction rule: GR.induct)
  case (cut \<Gamma> q \<Delta> H)
  show ?case
  proof (cases "\<Gamma> - \<Delta> = {}")
    case True
    then obtain p where "p \<in> \<Delta>" using cut by blast
    hence "H p \<noteq> {}" using cut by blast
    thus ?thesis using \<open>p \<in> \<Delta>\<close> by blast
  qed blast
next
  case (amalg F p) thus ?case by blast
qed simp_all

lemma MR_EMPTY_NONE: "MR.EMPTY_NONE"
  unfolding MR.EMPTY_NONE_def using GR_nonempty by blast

text \<open>N3: for each introduction entry an instance whose grounded proposition is not
  among its grounds.\<close>
lemma MR_N3:
  "GR {RA 0} (exqR fID) \<and> exqR fID \<noteq> RA 0"
  "GR (range (appR fEM)) UR \<and> UR \<notin> range (appR fEM)"
  "GR {RA 0, RA 1} (RC (RA 0) (RA 1))"
  "GR {RA 0} (RD (RA 0) (RA 1))"
  "GR {RA 0, RA 1} (RD (RA 0) (RA 1))"
  "GR {RA 0} (RT (RA 0))"
  "GR {RN (RN (RA 0))} (RN (RT (RN (RA 0))))"
  "GR {RA 0} (RN (RN (RA 0)))"
  "GR {RN (RN (RA 0))} (RN (RC (RN (RA 0)) (RA 1)))"
  "GR {RN (RN (RA 0)), RN (RN (RA 1))} (RN (RD (RN (RA 0)) (RN (RA 1))))"
proof -
  show "GR {RA 0} (exqR fID) \<and> exqR fID \<noteq> RA 0"
    using every_truth_grounds_ex[of "RA 0"] by (simp add: fID_def)
  have "GR (range (appR fEM)) UR" using GR.all[OF fEM_adm] fEM_all by (simp add: fEM_app)
  moreover have "UR \<notin> range (appR fEM)" by (auto simp: fEM_app UR_def)
  ultimately show "GR (range (appR fEM)) UR \<and> UR \<notin> range (appR fEM)" by blast
  show "GR {RA 0, RA 1} (RC (RA 0) (RA 1))" by (rule GR.conj) simp_all
  show "GR {RA 0} (RD (RA 0) (RA 1))" by (rule GR.disjL) simp
  show "GR {RA 0, RA 1} (RD (RA 0) (RA 1))" by (rule GR.disjB) simp_all
  show "GR {RA 0} (RT (RA 0))" by (rule GR.tr) simp
  show "GR {RN (RN (RA 0))} (RN (RT (RN (RA 0))))" by (rule GR.trneg) simp
  show "GR {RA 0} (RN (RN (RA 0)))" by (rule GR.dn) simp
  show "GR {RN (RN (RA 0))} (RN (RC (RN (RA 0)) (RA 1)))" by (rule GR.dm1) simp
  show "GR {RN (RN (RA 0)), RN (RN (RA 1))} (RN (RD (RN (RA 0)) (RN (RA 1))))"
    by (rule GR.dm3) simp_all
qed

section \<open>The certificate\<close>

theorem MR_package:
  "MR.FACT \<and> MR.LAM_CORE \<and> MR.C3d \<and> MR.W_ID \<and> MR.W_TR \<and> MR.W_EM \<and> MR.W_TEM \<and> MR.BETA_ID
   \<and> MR.CL_PROP \<and> MR.CL_QUANT \<and> MR.TS_FULL \<and> MR.TS_KF
   \<and> MR.EX_FULL \<and> MR.ALL_INST \<and> MR.CONJ_BIN \<and> MR.DISJ_ONE \<and> MR.DISJ_BOTH
   \<and> MR.TR_FULL \<and> MR.TR_NEG \<and> MR.NEG_DN \<and> MR.NEG_DM
   \<and> MR.TRANS_CUT \<and> MR.AMALG_INF \<and> MR.TRANS_P \<and> MR.EMPTY_NONE
   \<and> MR.N1 \<and> MR.N2 \<and> MR.N4_pairs \<and> MR.N5_chain
   \<and> \<not> MR.IRR_W \<and> \<not> MR.IRR_MEM \<and> \<not> MR.IRR_F"
  using MR_core MR_W MR_BETA_ID MR_classical MR.cl_ts_kf MR_intro MR_structural MR_levels MR_EMPTY_NONE
    MR_not_IRR_W MR_not_IRR_MEM MR_not_IRR_F by blast

end
