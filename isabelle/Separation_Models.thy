theory Separation_Models
  imports Restricted_Models No_Finite_Models Order
begin

text \<open>
  Registry 0.3.1-draft. Two questions that the repair of 0.3.0-draft left open are
  settled here by models, built as interpretations of the locale gsig (method of
  Model_Certificates.thy).

    MH  EX.PART holds and EX.PRED, EX.LEV (and EX.FULL) fail. So the partial
        existential principle implies neither restricted one. With MG, which satisfies
        EX.PRED and EX.LEV and fails EX.PART, the three are pairwise independent
        except for the proved implications from EX.FULL.

    MS  The sentence-position universal package as registry 0.2.x listed it,
        C1, BETA.ID, CL.QUANT, ALL.INST, DISJ.ONE, TRANS.P, IRR.F, without CL.PROP,
        has a model. So that listing omitted a premise the argument needs; what it
        needs is excluded middle (Puzzle_Packages.thy, fine_universal_sp_em). The
        model is infinite, and the package has no finite model.
\<close>

section \<open>Further registry entries restated in the locale\<close>

context gsig
begin
definition DISJ_ONE :: bool where
  "DISJ_ONE \<longleftrightarrow> (\<forall>p q. (T p \<longrightarrow> G {p} (disj p q)) \<and> (T q \<longrightarrow> G {q} (disj p q)))"
definition ALL_INST :: bool where
  "ALL_INST \<longleftrightarrow> (\<forall>f. adm f \<and> (\<forall>a. T (app f a)) \<longrightarrow> G (inst f) (allq f))"
definition EX_PART :: bool where
  "EX_PART \<longleftrightarrow> (\<forall>f a. adm f \<and> T (app f a) \<longrightarrow> PG (app f a) (exq f))"
definition IMM_CONJ :: bool where
  "IMM_CONJ \<longleftrightarrow> (\<forall>f. adm f \<and> (\<forall>r\<in>sat f. T r) \<longrightarrow> (\<forall>p. IPG p (bigconj f) \<longleftrightarrow> p \<in> sat f))"
end

lemma K_faithful_sep:
  "K.DISJ_ONE = DISJ_ONE" "K.ALL_INST = ALL_INST" "K.EX_PART = EX_PART" "K.IMM_CONJ = IMM_CONJ"
  by (simp_all add: K_aux K.DISJ_ONE_def DISJ_ONE_def K.ALL_INST_def ALL_INST_def
        K.EX_PART_def EX_PART_def K.IMM_CONJ_def IMM_CONJ_def)

section \<open>Model E satisfies IMM.FRITZ7 and fails IMM.CONJ\<close>

text \<open>ME (Model_Certificates.thy) has one propositional function, the identity, and its
  arbitrary conjunction is the false term Qu 2. The satisfiers of that function are the
  truths, so IMM.CONJ would make every truth an immediate partial ground of Qu 2, and
  in ME only conjunctions of truths have immediate grounds. So IMM.FRITZ7 does not
  imply IMM.CONJ. The separation is cheap: ME is not classical and its arbitrary
  conjunction is not truth-functional, so it says nothing about the two entries
  under CL.PROP and CL.QUANT.\<close>
lemma ME_not_IMM_CONJ: "\<not> ME.IMM_CONJ"
proof
  assume A: "ME.IMM_CONJ"
  have s: "ME.sat () = {p. TE p}" by (simp add: ME.sat_def)
  have "ME.IPG (At 0) (Qu 2)"
    using A[unfolded ME.IMM_CONJ_def, rule_format, of "()" "At 0"] s by simp
  thus False by (simp add: ME_IPG)
qed

theorem ME_separates_IMM: "ME.FACT \<and> ME.IMM_FRITZ7 \<and> ME.N1 \<and> \<not> ME.IMM_CONJ"
  using ME_core(1,2) ME_IMM_FRITZ7 ME_not_IMM_CONJ by blast

section \<open>Model H: partial existential grounding without the restricted principles\<close>

text \<open>The propositions, connectives, quantifiers and lambda terms of model MG
  (Restricted_Models.thy), with a different ground: any two distinct truths are,
  together, a full ground of any truth, and nothing else grounds anything. So every
  truth is a partial ground of every truth, and no singleton is a full ground.\<close>

definition GH :: "pg set \<Rightarrow> pg \<Rightarrow> bool" where
  "GH \<Gamma> q \<longleftrightarrow> fst q \<and> (\<exists>p p'. \<Gamma> = {p, p'} \<and> p \<noteq> p' \<and> fst p \<and> fst p')"

interpretation MH: gsig "fst :: pg \<Rightarrow> bool" "\<lambda>_. (True, R0)" ngG cjG djG trG
  "\<lambda>(f :: pg \<Rightarrow> pg) p. f p" exqG allqG bigG lamG admG GH "\<lambda>_. (True, R0)" "(True, R0)" .

lemma MH_den: "MH.den = dG"
proof (intro ext)
  fix v a show "MH.den v a = dG v a"
    by (induction a) (simp_all add: quantG)
qed

lemma GH_single: "\<not> GH {p} q"
  unfolding GH_def by (auto simp: doubleton_eq_iff)

lemma MH_PG: assumes "fst p" "fst q" shows "MH.PG p q"
proof -
  obtain p' :: pg where p': "p' \<noteq> p" "fst p'"
  proof (cases "p = (True, R0)")
    case True
    show ?thesis by (rule that[of "(True, R1)"]) (simp_all add: True)
  next
    case False
    show ?thesis by (rule that[of "(True, R0)"]) (use False in simp_all)
  qed
  have "GH {p, p'} q" unfolding GH_def using assms p' by blast
  thus ?thesis unfolding MH.PG_def by blast
qed

lemma MH_core: "MH.FACT" "MH.LAM_CORE" "MH.N1"
proof -
  show "MH.FACT" by (auto simp: MH.FACT_def GH_def)
  show "MH.LAM_CORE" unfolding MH.LAM_CORE_def MH_den using lamG_fv by (simp add: lamG_def)
  have "MH.PG (True, R0) (True, R0)" by (rule MH_PG) simp_all
  thus "MH.N1" unfolding MH.N1_def MH.PG_def by blast
qed

lemma MH_EX_PART: "MH.EX_PART"
  unfolding MH.EX_PART_def
proof (intro allI impI)
  fix f :: "pg \<Rightarrow> pg" and a
  assume A: "admG f \<and> fst (f a)"
  hence "\<exists>p. fst (f p)" by blast
  hence "fst (exqG f)" by (simp add: exqG_def)
  thus "MH.PG (f a) (exqG f)" using A MH_PG by blast
qed

lemma MH_not_EX_PRED: "\<not> MH.EX_PRED"
proof
  assume A: "MH.EX_PRED"
  have ad: "admG (\<lambda>p. p)" by (simp add: admG_def)
  have "GH {dG (\<lambda>_. (True, R0)) (Cst 0)} (exqG (\<lambda>p. p))"
    using A[unfolded MH.EX_PRED_def MH_den, rule_format, of "\<lambda>p. p" "Cst 0" "\<lambda>_. (True, R0)"] ad
    by simp
  thus False using GH_single by blast
qed

lemma MH_not_EX_LEV: "\<not> MH.EX_LEV"
proof
  assume A: "MH.EX_LEV"
  let ?v = "\<lambda>_::nat. (True, R0) :: pg"
  have l: "lamG 0 (Var 0) ?v = (\<lambda>p. p)" by (simp add: lamG_def)
  have ad: "admG (lamG 0 (Var 0) ?v)" unfolding l by (simp add: admG_def)
  have "GH {lamG 0 (Var 0) ?v (dG ?v (Cst 0))} (exqG (lamG 0 (Var 0) ?v))"
    using A[unfolded MH.EX_LEV_def MH_den, rule_format, of 0 "Var 0" ?v "Cst 0" ?v] ad
    by (simp add: l)
  thus False using GH_single by blast
qed

lemma MH_not_EX_FULL: "\<not> MH.EX_FULL"
proof
  assume A: "MH.EX_FULL"
  have ad: "admG (\<lambda>p. p)" by (simp add: admG_def)
  have "GH {(True, R0)} (exqG (\<lambda>p. p))"
    using A[unfolded MH.EX_FULL_def, rule_format, of "\<lambda>p. p" "(True, R0)"] ad by simp
  thus False using GH_single by blast
qed

theorem MH_package:
  "MH.FACT \<and> MH.LAM_CORE \<and> MH.EX_PART \<and> MH.N1
   \<and> \<not> MH.EX_PRED \<and> \<not> MH.EX_LEV \<and> \<not> MH.EX_FULL"
  using MH_core MH_EX_PART MH_not_EX_PRED MH_not_EX_LEV MH_not_EX_FULL by blast

section \<open>Model S: the sentence-position package without classical connectives\<close>

text \<open>
  A proposition is a truth value with a natural-number rank. Conjunction and
  disjunction have the classical truth value and a rank above both arguments. Truth
  ascription keeps the truth value and gives rank 1. Negation is classical except at
  the one proposition (False, 0), whose negation is also false; so excluded middle
  fails there and CL.PROP fails. A universal proposition has rank 4. A true proposition
  is, on its own, a full ground of every true proposition of higher rank.

  Of the four C1 witnesses only f_tem is true of everything: its value is (True, 3)
  everywhere, and that one instance grounds the universal truth (True, 4). The other
  three witnesses have a false instance, so ALL.INST has nothing to say about them.
  In particular the universal closure of f_em, the proposition the sentence-position
  argument is about, is false.
\<close>

type_synonym ps = "bool \<times> nat"

definition ngS :: "ps \<Rightarrow> ps" where
  "ngS p = (if p = (False, 0) then (False, 1) else (\<not> fst p, Suc (snd p)))"
definition cjS :: "ps \<Rightarrow> ps \<Rightarrow> ps" where "cjS p q = (fst p \<and> fst q, Suc (max (snd p) (snd q)))"
definition djS :: "ps \<Rightarrow> ps \<Rightarrow> ps" where "djS p q = (fst p \<or> fst q, Suc (max (snd p) (snd q)))"
definition trS :: "ps \<Rightarrow> ps" where "trS p = (fst p, 1)"

primrec dS :: "(nat \<Rightarrow> ps) \<Rightarrow> fm \<Rightarrow> ps" where
  "dS v (Var n) = v n"
| "dS v (Cst n) = (True, 0)"
| "dS v (Neg a) = ngS (dS v a)"
| "dS v (Conj a b) = cjS (dS v a) (dS v b)"
| "dS v (Disj a b) = djS (dS v a) (dS v b)"
| "dS v (Tr a) = trS (dS v a)"
| "dS v (Ex x a) = ((\<exists>p. fst (dS (v(x:=p)) a)), 0)"
| "dS v (All x a) = ((\<forall>p. fst (dS (v(x:=p)) a)), 4)"
| "dS v (BigC x a) = ((\<forall>p. fst (dS (v(x:=p)) a) \<longrightarrow> fst p), 0)"

definition lamS :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> ps) \<Rightarrow> ps \<Rightarrow> ps" where
  "lamS x a v = (\<lambda>p. dS (v(x:=p)) a)"
definition exqS :: "(ps \<Rightarrow> ps) \<Rightarrow> ps" where "exqS f = ((\<exists>p. fst (f p)), 0)"
definition allqS :: "(ps \<Rightarrow> ps) \<Rightarrow> ps" where "allqS f = ((\<forall>p. fst (f p)), 4)"
definition bigS :: "(ps \<Rightarrow> ps) \<Rightarrow> ps" where "bigS f = ((\<forall>p. fst (f p) \<longrightarrow> fst p), 0)"

definition admS :: "(ps \<Rightarrow> ps) \<Rightarrow> bool" where
  "admS f \<longleftrightarrow> f \<in> {(\<lambda>p. p), trS, (\<lambda>p. djS p (ngS p)), (\<lambda>p. djS (trS p) (ngS (trS p)))}"

definition GS :: "ps set \<Rightarrow> ps \<Rightarrow> bool" where
  "GS \<Gamma> q \<longleftrightarrow> (\<exists>p. \<Gamma> = {p} \<and> fst p \<and> fst q \<and> snd p < snd q)"

interpretation MS: gsig "fst :: ps \<Rightarrow> bool" "\<lambda>_. (True, 0)" ngS cjS djS trS
  "\<lambda>(f :: ps \<Rightarrow> ps) p. f p" exqS allqS bigS lamS admS GS "\<lambda>_. (True, 0)" "(True, 0)" .

lemma quantS:
  "exqS (lamS x a v) = ((\<exists>p. fst (dS (v(x:=p)) a)), 0)"
  "allqS (lamS x a v) = ((\<forall>p. fst (dS (v(x:=p)) a)), 4)"
  "bigS (lamS x a v) = ((\<forall>p. fst (dS (v(x:=p)) a) \<longrightarrow> fst p), 0)"
  by (simp_all add: lamS_def exqS_def allqS_def bigS_def)

lemma MS_den: "MS.den = dS"
proof (intro ext)
  fix v a show "MS.den v a = dS v a"
    by (induction a) (simp_all add: quantS)
qed

lemma dS_fv: "(\<forall>y\<in>fv a. v y = w y) \<Longrightarrow> dS v a = dS w a"
proof (induct a arbitrary: v w)
  case (Ex x a)
  have "\<And>p. dS (v(x:=p)) a = dS (w(x:=p)) a"
    by (rule Ex.hyps) (use Ex.prems in auto)
  then show ?case by simp
next
  case (All x a)
  have "\<And>p. dS (v(x:=p)) a = dS (w(x:=p)) a"
    by (rule All.hyps) (use All.prems in auto)
  then show ?case by simp
next
  case (BigC x a)
  have "\<And>p. dS (v(x:=p)) a = dS (w(x:=p)) a"
    by (rule BigC.hyps) (use BigC.prems in auto)
  then show ?case by simp
next
  case (Neg a)
  have "dS v a = dS w a" by (rule Neg.hyps) (use Neg.prems in auto)
  then show ?case by simp
next
  case (Tr a)
  have "dS v a = dS w a" by (rule Tr.hyps) (use Tr.prems in auto)
  then show ?case by simp
next
  case (Conj a b)
  have "dS v a = dS w a" by (rule Conj.hyps(1)) (use Conj.prems in auto)
  moreover have "dS v b = dS w b" by (rule Conj.hyps(2)) (use Conj.prems in auto)
  ultimately show ?case by simp
next
  case (Disj a b)
  have "dS v a = dS w a" by (rule Disj.hyps(1)) (use Disj.prems in auto)
  moreover have "dS v b = dS w b" by (rule Disj.hyps(2)) (use Disj.prems in auto)
  ultimately show ?case by simp
qed simp_all

lemma lamS_fv: "\<forall>y\<in>fv a - {x}. v y = w y \<Longrightarrow> lamS x a v = lamS x a w"
  unfolding lamS_def by (intro ext dS_fv) auto

lemma MS_PG: "MS.PG p q \<longleftrightarrow> fst p \<and> fst q \<and> snd p < snd q"
proof
  assume "MS.PG p q"
  thus "fst p \<and> fst q \<and> snd p < snd q" unfolding MS.PG_def GS_def by auto
next
  assume A: "fst p \<and> fst q \<and> snd p < snd q"
  have "p \<in> {p} \<and> GS {p} q" using A unfolding GS_def by blast
  thus "MS.PG p q" unfolding MS.PG_def by (rule exI)
qed

text \<open>The value of the witness f_tem is (True, 3) everywhere.\<close>
lemma tem_const: "djS (trS p) (ngS (trS p)) = (True, 3)"
  by (cases p) (auto simp: djS_def trS_def ngS_def)

lemma MS_core: "MS.FACT" "MS.LAM_CORE" "MS.N1" "MS.N2" "MS.N5_chain"
  and MS_N4: "MS.N4_pair (True, 0) (ngS (ngS (True, 0)))"
proof -
  show "MS.FACT" by (auto simp: MS.FACT_def GS_def)
  show "MS.LAM_CORE" unfolding MS.LAM_CORE_def MS_den using lamS_fv by (simp add: lamS_def)
  have g: "GS {(True, 0)} (True, 1)" by (simp add: GS_def)
  show "MS.N1" unfolding MS.N1_def using g by blast
  thus "MS.N2" unfolding MS.N2_def
    by (intro conjI exI[of _ "(True, 0::nat)"] exI[of _ "(True, 1::nat)"] exI[of _ "(True, 2::nat)"])
       simp_all
  show "MS.N5_chain" unfolding MS.N5_chain_def
    by (intro exI[of _ "(True, 0::nat)"] exI[of _ "(True, 1::nat)"] exI[of _ "(True, 2::nat)"]
          exI[of _ "(True, 3::nat)"]) (simp add: MS_PG)
  have n: "ngS (ngS (True, 0)) = (True, 2)" by (simp add: ngS_def)
  have m1: "GS {(True, 0)} (True, 2)" by (simp add: GS_def)
  have m2: "\<not> GS {(True, 0)} (True, 0)" by (simp add: GS_def)
  have "{\<Gamma>. GS \<Gamma> (True, 0)} \<noteq> {\<Gamma>. GS \<Gamma> (True, 2)}" using m1 m2 by blast
  thus "MS.N4_pair (True, 0) (ngS (ngS (True, 0)))"
    unfolding MS.N4_pair_def n by simp
qed

lemma MS_C1: "MS.C1"
  by (simp add: MS.C1_def admS_def MS.f_id_def MS.f_tr_def MS.f_em_def MS.f_tem_def lamS_def)

lemma MS_BETA_ID: "MS.BETA_ID"
  by (simp add: MS.BETA_ID_def MS_den lamS_def)

lemma MS_CL_QUANT: "MS.CL_QUANT'"
  by (simp add: MS.CL_QUANT'_def exqS_def allqS_def bigS_def MS.sat_def)

lemma MS_order: "MS.IRR_F" "MS.ASYM_P" "MS.TRANS_P"
proof -
  show "MS.IRR_F" by (auto simp: MS.IRR_F_def GS_def)
  show "MS.ASYM_P" by (auto simp: MS.ASYM_P_def MS_PG)
  show "MS.TRANS_P" by (auto simp: MS.TRANS_P_def MS_PG)
qed

lemma MS_DISJ_ONE: "MS.DISJ_ONE"
  by (auto simp: MS.DISJ_ONE_def GS_def djS_def)

lemma MS_not_EM: "\<not> fst (djS (False, 0) (ngS (False, 0)))"
  by (simp add: djS_def ngS_def)

lemma MS_ALL_INST: "MS.ALL_INST"
  unfolding MS.ALL_INST_def
proof (intro allI impI)
  fix f :: "ps \<Rightarrow> ps"
  assume A: "admS f \<and> (\<forall>a. fst (f a))"
  have f0: "fst (f (False, 0))" using A by blast
  have d: "f = (\<lambda>p. p) \<or> f = trS \<or> f = (\<lambda>p. djS p (ngS p))
           \<or> f = (\<lambda>p. djS (trS p) (ngS (trS p)))"
    using A unfolding admS_def by blast
  have "f = (\<lambda>p. djS (trS p) (ngS (trS p)))"
    using d
  proof (elim disjE)
    assume "f = (\<lambda>p. p)" with f0 show ?thesis by simp
  next
    assume "f = trS" with f0 show ?thesis by (simp add: trS_def)
  next
    assume "f = (\<lambda>p. djS p (ngS p))" with f0 MS_not_EM show ?thesis by simp
  next
    assume "f = (\<lambda>p. djS (trS p) (ngS (trS p)))" thus ?thesis .
  qed
  hence c: "f = (\<lambda>p. (True, 3))" using tem_const by simp
  have i: "MS.inst f = {(True, 3)}" unfolding MS.inst_def c by auto
  have a: "allqS f = (True, 4)" unfolding c allqS_def by simp
  show "GS (MS.inst f) (allqS f)" unfolding i a by (simp add: GS_def)
qed

text \<open>Excluded middle fails at (False, 0), so CL.PROP fails; the universal closure
  of f_em is false.\<close>
lemma MS_not_CL_PROP: "\<not> MS.CL_PROP'"
proof
  assume A: "MS.CL_PROP'"
  have "fst (ngS (False, 0)) \<longleftrightarrow> \<not> fst ((False, 0) :: ps)"
    using A[unfolded MS.CL_PROP'_def, rule_format, of "(False, 0)" "(False, 0)"] by blast
  thus False by (simp add: ngS_def)
qed

lemma MS_f_em_false: "\<not> fst (allqS MS.f_em)"
proof -
  have "MS.f_em = (\<lambda>p. djS p (ngS p))" by (simp add: MS.f_em_def lamS_def)
  thus ?thesis using MS_not_EM by (auto simp: allqS_def)
qed

text \<open>N3 instances. DISJ.ONE: (True, 0) grounds the distinct proposition
  (True, 0) \<or> (True, 0) = (True, 1). ALL.INST: the one instance (True, 3) of f_tem
  grounds its universal closure (True, 4).\<close>
lemma MS_N3:
  "djS (True, 0) (True, 0) = (True, 1) \<and> GS {(True, 0)} (djS (True, 0) (True, 0))
   \<and> admS MS.f_tem \<and> MS.inst MS.f_tem = {(True, 3)} \<and> allqS MS.f_tem = (True, 4)
   \<and> GS (MS.inst MS.f_tem) (allqS MS.f_tem)"
proof -
  have t: "MS.f_tem = (\<lambda>p. (True, 3))" using tem_const by (simp add: MS.f_tem_def lamS_def)
  have ad: "admS MS.f_tem" using MS_C1 unfolding MS.C1_def by simp
  have i: "MS.inst MS.f_tem = {(True, 3)}" unfolding MS.inst_def t by auto
  have a: "allqS MS.f_tem = (True, 4)" unfolding t allqS_def by simp
  show ?thesis using ad i a by (simp add: djS_def GS_def)
qed

theorem MS_package:
  "MS.FACT \<and> MS.LAM_CORE \<and> MS.C1 \<and> MS.BETA_ID \<and> MS.CL_QUANT' \<and> MS.ALL_INST \<and> MS.DISJ_ONE
   \<and> MS.TRANS_P \<and> MS.IRR_F \<and> MS.ASYM_P \<and> MS.N1 \<and> MS.N2 \<and> MS.N5_chain \<and> \<not> MS.CL_PROP'"
  using MS_core MS_C1 MS_BETA_ID MS_CL_QUANT MS_ALL_INST MS_DISJ_ONE MS_order MS_not_CL_PROP
  by blast

section \<open>The package has no finite model\<close>

text \<open>With FACT, a truth t and DISJ.ONE give the truths t, t \<or> t, (t \<or> t) \<or> (t \<or> t), ...,
  each a partial ground of the next; in a finite domain the chain repeats, which
  transitivity and irreflexivity forbid (the argument of finding F1, which here needs
  no classical clause because factivity supplies the truth of each disjunction).
  CL.QUANT supplies the first truth.\<close>
theorem sp_package_no_finite_model:
  assumes fin: "finite (UNIV :: prp set)"
      and "FACT" "CL_QUANT" "DISJ_ONE" "TRANS_P" "IRR_F"
  shows False
proof -
  obtain t where t: "T t" using CL_QUANT_truth[OF assms(3)] by blast
  have step: "T p \<Longrightarrow> T (disj p p) \<and> PG p (disj p p)" for p
  proof -
    assume "T p"
    hence g: "G {p} (disj p p)" using assms(4) unfolding DISJ_ONE_def by blast
    hence "T (disj p p)" using assms(2) unfolding FACT_def by blast
    moreover have "PG p (disj p p)" using g unfolding PG_def by blast
    ultimately show ?thesis by blast
  qed
  have tr: "\<forall>p q r. PG p q \<and> PG q r \<longrightarrow> PG p r" using assms(5) unfolding TRANS_P_def .
  have ir: "\<forall>\<Gamma> x. G \<Gamma> x \<longrightarrow> x \<notin> \<Gamma>" using assms(6) unfolding IRR_F_def .
  show False
  proof (rule chain_no_finite[where s="\<lambda>p. disj p p", OF fin t _ tr ir])
    fix p assume "T p" thus "T (disj p p) \<and> PG p (disj p p)" by (rule step)
  qed
qed

end
