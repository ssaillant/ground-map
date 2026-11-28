theory Restricted_Models
  imports Model_Certificates
begin

text \<open>
  Registry 0.3.0-draft, decision D5. The restricted entries TS.TYPED, TR.TYPED, EX.PRED
  and EX.LEV now quantify over CLOSED formulas. This theory shows that the repair has
  the intended effect: one finite model MG, with classical truth, satisfies the four
  restricted entries together with C1, BETA.ID, CL.PROP, CL.QUANT, IRR.F, ASYM.P and
  TRANS.P, and fails each unrestricted counterpart (EX.FULL, TS.FULL, TR.FULL). So

    (a) none of the four restricted entries implies its unrestricted counterpart, and
    (b) Kr\"amer's package with EX.PRED (or EX.LEV) in place of EX.FULL is consistent,
        which is the escape route Kr\"amer describes; with the 0.2.1-draft definitions
        the same package was refuted (Audit_Checks.thy, kramer_not_blocked_v021).

  Method as in Model_Certificates.thy: an interpretation of the locale gsig, whose
  definitions are proved identical to the registry's (K_faithful, K_faithful_more).
\<close>

section \<open>Further registry entries restated in the locale\<close>

text \<open>The primed names avoid a clash with definitions of the same entries that a
  parallel change adds to gsig; K_faithful_more proves each is the registry's entry.\<close>
context gsig
begin
definition CL_PROP' :: bool where
  "CL_PROP' \<longleftrightarrow> (\<forall>p q. (T (neg p) \<longleftrightarrow> \<not> T p) \<and> (T (conj p q) \<longleftrightarrow> T p \<and> T q)
                     \<and> (T (disj p q) \<longleftrightarrow> T p \<or> T q))"
definition CL_QUANT' :: bool where
  "CL_QUANT' \<longleftrightarrow> (\<forall>f. (T (exq f) \<longleftrightarrow> (\<exists>a. T (app f a))) \<and> (T (allq f) \<longleftrightarrow> (\<forall>a. T (app f a)))
                     \<and> (T (bigconj f) \<longleftrightarrow> (\<forall>q\<in>sat f. T q)))"
definition TS_FULL' :: bool where
  "TS_FULL' \<longleftrightarrow> (\<forall>p. T (tr p) \<longleftrightarrow> T p)"
definition TR_FULL :: bool where
  "TR_FULL \<longleftrightarrow> (\<forall>p. T p \<longrightarrow> G {p} (tr p))"
definition ASYM_P :: bool where
  "ASYM_P \<longleftrightarrow> (\<forall>p q. PG p q \<longrightarrow> \<not> PG q p)"
definition TRANS_P :: bool where
  "TRANS_P \<longleftrightarrow> (\<forall>p q r. PG p q \<and> PG q r \<longrightarrow> PG p r)"
end

lemma K_faithful_more:
  "K.CL_PROP' = CL_PROP" "K.CL_QUANT' = CL_QUANT" "K.TS_FULL' = TS_FULL" "K.TR_FULL = TR_FULL"
  "K.ASYM_P = ASYM_P" "K.TRANS_P = TRANS_P"
  by (simp_all add: K_aux K.CL_PROP'_def CL_PROP_def K.CL_QUANT'_def CL_QUANT_def
        K.TS_FULL'_def TS_FULL_def K.TR_FULL_def TR_FULL_def K.ASYM_P_def ASYM_P_def
        K.TRANS_P_def TRANS_P_def)

section \<open>Model G: truth values with a rank\<close>

text \<open>
  A proposition is a truth value with one of five ranks. The rank records how the
  proposition was built: R0 for atoms and the outputs of the connectives, R1 for a
  truth ascription to an R0 proposition, R2 for a truth ascription to an R1 or R2
  proposition, R3 for quantified propositions, R4 for a truth ascription to a
  quantified proposition. A truth ascription to an R4 proposition is false, so the
  truth schema fails there. Propositional functions are all functions on the ten
  propositions; a lambda term denotes the function its body computes, so BETA.ID holds.
  A true proposition is a full ground, on its own, of every true proposition of
  higher rank, and nothing else grounds anything.
\<close>

datatype rk = R0 | R1 | R2 | R3 | R4

fun rn :: "rk \<Rightarrow> nat" where
  "rn R0 = 0" | "rn R1 = 1" | "rn R2 = 2" | "rn R3 = 3" | "rn R4 = 4"

type_synonym pg = "bool \<times> rk"

definition ngG :: "pg \<Rightarrow> pg" where "ngG p = (\<not> fst p, R0)"
definition cjG :: "pg \<Rightarrow> pg \<Rightarrow> pg" where "cjG p q = (fst p \<and> fst q, R0)"
definition djG :: "pg \<Rightarrow> pg \<Rightarrow> pg" where "djG p q = (fst p \<or> fst q, R0)"

fun trG :: "pg \<Rightarrow> pg" where
  "trG (t, R0) = (t, R1)"
| "trG (t, R1) = (t, R2)"
| "trG (t, R2) = (t, R2)"
| "trG (t, R3) = (t, R4)"
| "trG (t, R4) = (False, R4)"

primrec dG :: "(nat \<Rightarrow> pg) \<Rightarrow> fm \<Rightarrow> pg" where
  "dG v (Var n) = v n"
| "dG v (Cst n) = (True, R0)"
| "dG v (Neg a) = ngG (dG v a)"
| "dG v (Conj a b) = cjG (dG v a) (dG v b)"
| "dG v (Disj a b) = djG (dG v a) (dG v b)"
| "dG v (Tr a) = trG (dG v a)"
| "dG v (Ex x a) = ((\<exists>p. fst (dG (v(x:=p)) a)), R3)"
| "dG v (All x a) = ((\<forall>p. fst (dG (v(x:=p)) a)), R3)"
| "dG v (BigC x a) = ((\<forall>p. fst (dG (v(x:=p)) a) \<longrightarrow> fst p), R3)"

definition lamG :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> pg) \<Rightarrow> pg \<Rightarrow> pg" where
  "lamG x a v = (\<lambda>p. dG (v(x:=p)) a)"
definition exqG :: "(pg \<Rightarrow> pg) \<Rightarrow> pg" where "exqG f = ((\<exists>p. fst (f p)), R3)"
definition allqG :: "(pg \<Rightarrow> pg) \<Rightarrow> pg" where "allqG f = ((\<forall>p. fst (f p)), R3)"
definition bigG :: "(pg \<Rightarrow> pg) \<Rightarrow> pg" where "bigG f = ((\<forall>p. fst (f p) \<longrightarrow> fst p), R3)"

text \<open>The four C1 witnesses, as functions.\<close>
definition admG :: "(pg \<Rightarrow> pg) \<Rightarrow> bool" where
  "admG f \<longleftrightarrow> f \<in> {(\<lambda>p. p), trG, (\<lambda>p. djG p (ngG p)), (\<lambda>p. djG (trG p) (ngG (trG p)))}"

definition GG :: "pg set \<Rightarrow> pg \<Rightarrow> bool" where
  "GG \<Gamma> q \<longleftrightarrow> (\<exists>p. \<Gamma> = {p} \<and> fst p \<and> fst q \<and> rn (snd p) < rn (snd q))"

interpretation MG: gsig "fst :: pg \<Rightarrow> bool" "\<lambda>_. (True, R0)" ngG cjG djG trG
  "\<lambda>(f :: pg \<Rightarrow> pg) p. f p" exqG allqG bigG lamG admG GG "\<lambda>_. (True, R0)" "(True, R0)" .

lemma quantG:
  "exqG (lamG x a v) = ((\<exists>p. fst (dG (v(x:=p)) a)), R3)"
  "allqG (lamG x a v) = ((\<forall>p. fst (dG (v(x:=p)) a)), R3)"
  "bigG (lamG x a v) = ((\<forall>p. fst (dG (v(x:=p)) a) \<longrightarrow> fst p), R3)"
  by (simp_all add: lamG_def exqG_def allqG_def bigG_def)

lemma MG_den: "MG.den = dG"
proof (intro ext)
  fix v a show "MG.den v a = dG v a"
    by (induction a) (simp_all add: quantG)
qed

lemma dG_fv: "(\<forall>y\<in>fv a. v y = w y) \<Longrightarrow> dG v a = dG w a"
proof (induct a arbitrary: v w)
  case (Ex x a)
  have "\<And>p. dG (v(x:=p)) a = dG (w(x:=p)) a"
    by (rule Ex.hyps) (use Ex.prems in auto)
  then show ?case by simp
next
  case (All x a)
  have "\<And>p. dG (v(x:=p)) a = dG (w(x:=p)) a"
    by (rule All.hyps) (use All.prems in auto)
  then show ?case by simp
next
  case (BigC x a)
  have "\<And>p. dG (v(x:=p)) a = dG (w(x:=p)) a"
    by (rule BigC.hyps) (use BigC.prems in auto)
  then show ?case by simp
next
  case (Neg a)
  have "dG v a = dG w a" by (rule Neg.hyps) (use Neg.prems in auto)
  then show ?case by simp
next
  case (Tr a)
  have "dG v a = dG w a" by (rule Tr.hyps) (use Tr.prems in auto)
  then show ?case by simp
next
  case (Conj a b)
  have "dG v a = dG w a" by (rule Conj.hyps(1)) (use Conj.prems in auto)
  moreover have "dG v b = dG w b" by (rule Conj.hyps(2)) (use Conj.prems in auto)
  ultimately show ?case by simp
next
  case (Disj a b)
  have "dG v a = dG w a" by (rule Disj.hyps(1)) (use Disj.prems in auto)
  moreover have "dG v b = dG w b" by (rule Disj.hyps(2)) (use Disj.prems in auto)
  ultimately show ?case by simp
qed simp_all

lemma lamG_fv: "\<forall>y\<in>fv a - {x}. v y = w y \<Longrightarrow> lamG x a v = lamG x a w"
  unfolding lamG_def by (intro ext dG_fv) auto

section \<open>Ranks of the propositions that closed formulas present\<close>

lemma trG_low: "rn (snd p) \<le> 2 \<Longrightarrow> rn (snd (trG p)) \<le> 2 \<and> fst (trG p) = fst p"
  by (cases p rule: trG.cases) auto

lemma trG_ne0: "snd (trG p) \<noteq> R0"
  by (cases p rule: trG.cases) auto

lemma trG_trG: "trG (trG p) \<noteq> (t, R1)"
  by (cases p rule: trG.cases) auto

text \<open>A closed quantifier-free formula presents a proposition of rank at most 2.\<close>
lemma closed_lvl0_rank: "fv a = {} \<Longrightarrow> lvl a = 0 \<Longrightarrow> rn (snd (dG v a)) \<le> 2"
  by (induction a) (auto simp: ngG_def cjG_def djG_def trG_low)

text \<open>A closed truth-free formula presents a proposition of rank 0 or 3.\<close>
lemma closed_tfree_rank: "fv a = {} \<Longrightarrow> tfree a \<Longrightarrow> snd (dG v a) = R0 \<or> snd (dG v a) = R3"
  by (cases a) (auto simp: ngG_def cjG_def djG_def)

lemma adm_low: "admG f \<Longrightarrow> rn (snd c) \<le> 2 \<Longrightarrow> rn (snd (f c)) \<le> 2"
  unfolding admG_def by (auto simp: djG_def trG_low)

section \<open>Which formulas present an admissible function\<close>

text \<open>The identity function is presented only by the bound variable, and the truth
  function only by Tr applied to it; every other body of an admissible function has
  rank R0 everywhere. This is what makes EX.LEV hold: a body of higher level cannot
  present the identity function and so raise the level bound for its instances.\<close>

lemma adm_cases:
  assumes "admG F"
  shows "F = (\<lambda>p. p) \<or> F = trG \<or> (\<forall>p. F p = (True, R0))"
  using assms unfolding admG_def by (auto simp: djG_def ngG_def)

lemma tr_shape:
  assumes H: "\<forall>p. trG (dG (v(x:=p)) b) = trG p"
  shows "b = Var x"
proof -
  have h0: "trG (dG (v(x:=(True, R0))) b) = (True, R1)" using H by simp
  have h0f: "trG (dG (v(x:=(False, R0))) b) = (False, R1)" using H by simp
  have h3: "trG (dG (v(x:=(True, R3))) b) = (True, R4)" using H by simp
  show ?thesis
  proof (cases b)
    case (Var z)
    show ?thesis
    proof (cases "z = x")
      case True with Var show ?thesis by simp
    next
      case False with Var h0 h0f show ?thesis by simp
    qed
  next
    case (Cst n) with h3 show ?thesis by simp
  next
    case (Neg a) with h3 show ?thesis by (simp add: ngG_def)
  next
    case (Conj a c) with h3 show ?thesis by (simp add: cjG_def)
  next
    case (Disj a c) with h3 show ?thesis by (simp add: djG_def)
  next
    case (Tr a) with h0 trG_trG show ?thesis by simp
  next
    case (Ex y a) with h0 show ?thesis by simp
  next
    case (All y a) with h0 show ?thesis by simp
  next
    case (BigC y a) with h0 show ?thesis by simp
  qed
qed

lemma adm_shape:
  assumes ad: "admG (lamG x b v)"
  shows "b = Var x \<or> b = Tr (Var x) \<or> (\<forall>p. snd (dG (v(x:=p)) b) = R0)"
proof -
  let ?F = "\<lambda>p. dG (v(x:=p)) b"
  have "?F = (\<lambda>p. p) \<or> ?F = trG \<or> (\<forall>p. ?F p = (True, R0))"
    using adm_cases[OF ad] unfolding lamG_def .
  hence c: "(\<forall>p. ?F p = p) \<or> (\<forall>p. ?F p = trG p) \<or> (\<forall>p. ?F p = (True, R0))"
    by (auto simp: fun_eq_iff)
  text \<open>What an admissible function does to the propositions (True, R0) and (False, R0).\<close>
  have pts: "(?F (True, R0) = (True, R0) \<and> ?F (False, R0) = (False, R0))
           \<or> (?F (True, R0) = (True, R1) \<and> ?F (False, R0) = (False, R1))
           \<or> (\<forall>p. ?F p = (True, R0))"
    using c by auto
  show ?thesis
  proof (cases b)
    case (Var z)
    show ?thesis
    proof (cases "z = x")
      case True with Var show ?thesis by simp
    next
      case False with Var pts show ?thesis by auto
    qed
  next
    case (Cst n) thus ?thesis by simp
  next
    case (Neg a) thus ?thesis by (simp add: ngG_def)
  next
    case (Conj a d) thus ?thesis by (simp add: cjG_def)
  next
    case (Disj a d) thus ?thesis by (simp add: djG_def)
  next
    case (Tr a)
    have n0: "snd (?F (True, R0)) \<noteq> R0" using Tr trG_ne0 by simp
    from c show ?thesis
    proof (elim disjE)
      assume "\<forall>p. ?F p = p"
      hence "?F (True, R0) = (True, R0)" by blast
      with n0 show ?thesis by simp
    next
      assume "\<forall>p. ?F p = trG p"
      with Tr have "\<forall>p. trG (dG (v(x:=p)) a) = trG p" by simp
      hence "a = Var x" by (rule tr_shape)
      with Tr show ?thesis by simp
    next
      assume "\<forall>p. ?F p = (True, R0)"
      hence "?F (True, R0) = (True, R0)" by blast
      with n0 show ?thesis by simp
    qed
  next
    case (Ex y a)
    hence "snd (?F (True, R0)) = R3" by simp
    with pts show ?thesis by auto
  next
    case (All y a)
    hence "snd (?F (True, R0)) = R3" by simp
    with pts show ?thesis by auto
  next
    case (BigC y a)
    hence "snd (?F (True, R0)) = R3" by simp
    with pts show ?thesis by auto
  qed
qed

section \<open>The package holds in MG\<close>

lemma MG_PG: "MG.PG p q \<longleftrightarrow> fst p \<and> fst q \<and> rn (snd p) < rn (snd q)"
proof
  assume "MG.PG p q"
  thus "fst p \<and> fst q \<and> rn (snd p) < rn (snd q)" unfolding MG.PG_def GG_def by auto
next
  assume A: "fst p \<and> fst q \<and> rn (snd p) < rn (snd q)"
  have "p \<in> {p} \<and> GG {p} q" using A unfolding GG_def by blast
  thus "MG.PG p q" unfolding MG.PG_def by (rule exI)
qed

lemma MG_core: "MG.FACT" "MG.LAM_CORE" "MG.N1" "MG.N2" "MG.N5_chain"
  and MG_N4: "MG.N4_pair (True, R1) (ngG (ngG (True, R1)))"
proof -
  show "MG.FACT" by (auto simp: MG.FACT_def GG_def)
  show "MG.LAM_CORE" unfolding MG.LAM_CORE_def MG_den using lamG_fv by (simp add: lamG_def)
  have g: "GG {(True, R0)} (True, R1)" by (simp add: GG_def)
  show "MG.N1" unfolding MG.N1_def using g by blast
  thus "MG.N2" unfolding MG.N2_def
    by (intro conjI exI[of _ "(True, R0)"] exI[of _ "(True, R1)"] exI[of _ "(True, R2)"]) simp_all
  show "MG.N5_chain" unfolding MG.N5_chain_def
    by (intro exI[of _ "(True, R0)"] exI[of _ "(True, R1)"] exI[of _ "(True, R2)"]
          exI[of _ "(True, R3)"]) (simp add: MG_PG)
  have "{(True, R0)} \<in> {\<Gamma>. GG \<Gamma> (True, R1)}" "{(True, R0)} \<notin> {\<Gamma>. GG \<Gamma> (True, R0)}"
    by (auto simp: GG_def)
  thus "MG.N4_pair (True, R1) (ngG (ngG (True, R1)))"
    unfolding MG.N4_pair_def by (auto simp: ngG_def)
qed

lemma MG_N4s: "MG.N4_pairs" using MG.N4_dn[OF MG_N4] .

lemma MG_C1: "MG.C1"
  by (simp add: MG.C1_def admG_def MG.f_id_def MG.f_tr_def MG.f_em_def MG.f_tem_def lamG_def)

lemma MG_BETA_ID: "MG.BETA_ID"
  by (simp add: MG.BETA_ID_def MG_den lamG_def)

lemma MG_classical: "MG.CL_PROP'" "MG.CL_QUANT'"
  by (simp_all add: MG.CL_PROP'_def MG.CL_QUANT'_def ngG_def cjG_def djG_def
        exqG_def allqG_def bigG_def MG.sat_def)

lemma MG_order: "MG.IRR_F" "MG.ASYM_P" "MG.TRANS_P"
proof -
  show "MG.IRR_F" by (auto simp: MG.IRR_F_def GG_def)
  show "MG.ASYM_P" by (auto simp: MG.ASYM_P_def MG_PG)
  show "MG.TRANS_P" by (auto simp: MG.TRANS_P_def MG_PG)
qed

lemma MG_TS_TYPED: "MG.TS_TYPED"
  unfolding MG.TS_TYPED_def MG_den
proof (intro allI impI)
  fix a v assume "tfree a \<and> fv a = {}"
  hence "snd (dG v a) = R0 \<or> snd (dG v a) = R3" using closed_tfree_rank by blast
  thus "fst (trG (dG v a)) \<longleftrightarrow> fst (dG v a)" by (cases "dG v a") auto
qed

lemma MG_TR_TYPED: "MG.TR_TYPED"
  unfolding MG.TR_TYPED_def MG_den
proof (intro allI impI)
  fix a v assume A: "tfree a \<and> fv a = {} \<and> fst (dG v a)"
  hence "snd (dG v a) = R0 \<or> snd (dG v a) = R3" using closed_tfree_rank by blast
  thus "GG {dG v a} (trG (dG v a))" using A by (cases "dG v a") (auto simp: GG_def)
qed

lemma GG_exq:
  assumes "fst (f c)" "rn (snd (f c)) \<le> 2"
  shows "GG {f c} (exqG f)"
proof -
  have "\<exists>p. fst (f p)" using assms(1) by (rule exI)
  hence e: "exqG f = (True, R3)" unfolding exqG_def by simp
  show ?thesis unfolding e GG_def using assms by simp
qed

lemma MG_EX_PRED: "MG.EX_PRED"
  unfolding MG.EX_PRED_def MG_den
proof (intro allI impI)
  fix f a w
  assume A: "admG f \<and> lvl a = 0 \<and> fv a = {} \<and> fst (f (dG w a))"
  have "rn (snd (dG w a)) \<le> 2" using A closed_lvl0_rank by blast
  hence "rn (snd (f (dG w a))) \<le> 2" using A adm_low by blast
  thus "GG {f (dG w a)} (exqG f)" using A GG_exq by blast
qed

lemma MG_EX_LEV: "MG.EX_LEV"
  unfolding MG.EX_LEV_def MG_den
proof (intro allI impI)
  fix x b v a w
  assume A: "admG (lamG x b v) \<and> lvl a < lvl (Ex x b) \<and> fv a = {} \<and> fst (lamG x b v (dG w a))"
  let ?c = "dG w a"
  have low: "rn (snd (lamG x b v ?c)) \<le> 2"
  proof -
    from adm_shape[of x b v] A
    have "b = Var x \<or> b = Tr (Var x) \<or> (\<forall>p. snd (dG (v(x:=p)) b) = R0)" by blast
    thus ?thesis
    proof (elim disjE)
      assume b: "b = Var x"
      hence "lvl a = 0" using A by simp
      hence "rn (snd ?c) \<le> 2" using A closed_lvl0_rank by blast
      thus ?thesis using b by (simp add: lamG_def)
    next
      assume b: "b = Tr (Var x)"
      hence "lvl a = 0" using A by simp
      hence "rn (snd ?c) \<le> 2" using A closed_lvl0_rank by blast
      thus ?thesis using b trG_low by (simp add: lamG_def)
    next
      assume "\<forall>p. snd (dG (v(x:=p)) b) = R0"
      hence "snd (dG (v(x:=?c)) b) = R0" by (rule spec)
      thus ?thesis by (simp add: lamG_def)
    qed
  qed
  show "GG {lamG x b v ?c} (exqG (lamG x b v))" using A low GG_exq by blast
qed

section \<open>The unrestricted counterparts fail in MG\<close>

lemma MG_not_EX_FULL: "\<not> MG.EX_FULL"
proof
  assume A: "MG.EX_FULL"
  have ad: "admG (\<lambda>p. p)" by (simp add: admG_def)
  have "GG {(True, R3)} (exqG (\<lambda>p. p))"
    using A[unfolded MG.EX_FULL_def, rule_format, of "\<lambda>p. p" "(True, R3)"] ad by simp
  thus False by (simp add: GG_def exqG_def)
qed

lemma MG_not_TS_FULL: "\<not> MG.TS_FULL'"
proof
  assume A: "MG.TS_FULL'"
  have "fst (trG (True, R4)) \<longleftrightarrow> fst ((True, R4) :: pg)"
    using A[unfolded MG.TS_FULL'_def, rule_format, of "(True, R4)"] .
  thus False by simp
qed

lemma MG_not_TR_FULL: "\<not> MG.TR_FULL"
proof
  assume A: "MG.TR_FULL"
  have "GG {(True, R2)} (trG (True, R2))"
    using A[unfolded MG.TR_FULL_def, rule_format, of "(True, R2)"] by simp
  thus False by (simp add: GG_def)
qed

section \<open>Non-triviality instances\<close>

text \<open>N3 for the three introduction entries of the package. EX.PRED and EX.LEV: the
  closed quantifier-free formula Cst 0 presents (True, R0), a true instance of the
  identity function, which grounds the distinct proposition exq (\<lambda>p. p) = (True, R3).
  TR.TYPED: (True, R0) grounds its truth ascription (True, R1).\<close>
lemma MG_N3:
  "lvl (Cst 0) = 0 \<and> fv (Cst 0) = {} \<and> lvl (Cst 0) < lvl (Ex 0 (Var 0)) \<and> tfree (Cst 0)
   \<and> dG w (Cst 0) = (True, R0) \<and> admG (\<lambda>p. p) \<and> lamG 0 (Var 0) v = (\<lambda>p. p)
   \<and> exqG (\<lambda>p. p) = (True, R3) \<and> GG {(True, R0)} (True, R3) \<and> (True, R3) \<notin> {(True, R0) :: pg}
   \<and> trG (True, R0) = (True, R1) \<and> GG {(True, R0)} (True, R1) \<and> (True, R1) \<notin> {(True, R0) :: pg}"
  by (auto simp: admG_def lamG_def exqG_def GG_def)

text \<open>The whole certificate in one statement.\<close>
theorem MG_package:
  "MG.FACT \<and> MG.LAM_CORE \<and> MG.C1 \<and> MG.BETA_ID \<and> MG.CL_PROP' \<and> MG.CL_QUANT'
   \<and> MG.TS_TYPED \<and> MG.TR_TYPED \<and> MG.EX_PRED \<and> MG.EX_LEV
   \<and> MG.IRR_F \<and> MG.ASYM_P \<and> MG.TRANS_P \<and> MG.N1 \<and> MG.N2 \<and> MG.N5_chain
   \<and> \<not> MG.EX_FULL \<and> \<not> MG.TS_FULL' \<and> \<not> MG.TR_FULL"
  using MG_core MG_C1 MG_BETA_ID MG_classical MG_TS_TYPED MG_TR_TYPED MG_EX_PRED MG_EX_LEV
        MG_order MG_not_EX_FULL MG_not_TS_FULL MG_not_TR_FULL by blast

end
