theory Separation_Models
  imports Restricted_Models No_Finite_Models Order
begin

text \<open>
  Registry 0.3.1-draft. Questions that the repair of 0.3.0-draft left open are
  settled here by models, built as interpretations of the locale gsig (method of
  Model_Certificates.thy).

    MH  EX.PART holds and EX.PRED, EX.LEV (and EX.FULL) fail. So the partial
        existential principle implies neither restricted one. With MG, which satisfies
        EX.PRED and EX.LEV and fails EX.PART, the three are pairwise independent
        except for the proved implications from EX.FULL.

    MT  Fine's universal package with TR.TYPED in place of TR.PART, with f_id, f_tr and
        f_tem admissible and f_em not, has a model (findings F8, F9).

    MU  Registry 0.3.2-draft, decision D9. With f_tr and f_tem admissible and f_id and
        f_em not, the existential entries hold as well. MU contains "something is
        true" and both of Fine's arguments for propositions, each with TR.TYPED in
        place of TR.PART (finding F9).

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
definition ALL_PART :: bool where
  "ALL_PART \<longleftrightarrow> (\<forall>f a. adm f \<and> (\<forall>b. T (app f b)) \<longrightarrow> PG (app f a) (allq f))"
definition DISJ_PART :: bool where
  "DISJ_PART \<longleftrightarrow> (\<forall>p q. (T p \<longrightarrow> PG p (disj p q)) \<and> (T q \<longrightarrow> PG q (disj p q)))"
definition TR_PART :: bool where
  "TR_PART \<longleftrightarrow> (\<forall>p. T p \<longrightarrow> PG p (tr p))"
text \<open>Not a registry entry: C1 with the witness f_em left out.\<close>
definition C1_NO_EM :: bool where
  "C1_NO_EM \<longleftrightarrow> (\<forall>f. adm f \<longleftrightarrow> f \<in> {f_id, f_tr, f_tem})"
text \<open>The witness entries (decision D9).\<close>
definition W_ID :: bool where "W_ID \<longleftrightarrow> adm f_id"
definition W_TR :: bool where "W_TR \<longleftrightarrow> adm f_tr"
definition W_EM :: bool where "W_EM \<longleftrightarrow> adm f_em"
definition W_TEM :: bool where "W_TEM \<longleftrightarrow> adm f_tem"
definition IMM_CONJ :: bool where
  "IMM_CONJ \<longleftrightarrow> (\<forall>f. adm f \<and> (\<forall>r\<in>sat f. T r) \<longrightarrow> (\<forall>p. IPG p (bigconj f) \<longleftrightarrow> p \<in> sat f))"
end

lemma K_faithful_sep:
  "K.DISJ_ONE = DISJ_ONE" "K.ALL_INST = ALL_INST" "K.EX_PART = EX_PART" "K.IMM_CONJ = IMM_CONJ"
  "K.ALL_PART = ALL_PART" "K.DISJ_PART = DISJ_PART" "K.TR_PART = TR_PART"
  "K.W_ID = W_ID" "K.W_TR = W_TR" "K.W_EM = W_EM" "K.W_TEM = W_TEM"
  by (simp_all add: K_aux K.DISJ_ONE_def DISJ_ONE_def K.ALL_INST_def ALL_INST_def
        K.EX_PART_def EX_PART_def K.IMM_CONJ_def IMM_CONJ_def K.ALL_PART_def ALL_PART_def
        K.DISJ_PART_def DISJ_PART_def K.TR_PART_def TR_PART_def
        K.W_ID_def W_ID_def K.W_TR_def W_TR_def K.W_EM_def W_EM_def K.W_TEM_def W_TEM_def
        K.f_id_def f_id_def K.f_tr_def f_tr_def K.f_em_def f_em_def K.f_tem_def f_tem_def)

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

section \<open>Model T: Fine's universal argument without f_em, with typed grounding of truth\<close>

text \<open>
  Fine's universal package is refuted under C1 whatever truth entries it lists, because
  C1 admits f_em (Puzzle_Packages.thy, fine_universal_typed_refuted). This model answers
  the question that remains when f_em is not admissible. The admissible functions are
  f_id, f_tr and f_tem. The model satisfies BETA.ID, CL.PROP, CL.QUANT, the full truth
  schema TS.FULL, ALL.INST, DISJ.ONE, TRANS.P, IRR.F and ASYM.P, and TR.TYPED in place
  of TR.PART. So Fine's own route (fine_universal_witness) is blocked by typing the
  grounding of truth ascriptions alone; the truth schema need not be typed.

  A proposition is a truth value with a rank, and a rank is a pair of numbers ordered
  lexicographically: the ranks (0, n) lie below the ranks (1, n). Connectives are
  classical and raise the rank within its tier. A truth ascription has rank (1, 0), above
  every rank of the lower tier. Propositional functions are closures: a variable, a
  formula and an environment cut down to the formula's parameters. An existential or
  universal proposition has rank (0, 0) when its body is truth-free and rank (1, 3)
  otherwise; an arbitrary conjunction has rank (0, 0).
  So every closed truth-free formula denotes a proposition of the lower tier, and its
  truth ascription lies above it. The universal closure s of f_tem has rank (1, 3); its
  one instance has rank (1, 2) and the truth ascription to s has rank (1, 0), below s.
  A truth is, on its own, a full ground of every truth of higher rank.
\<close>

type_synonym rk = "nat \<times> nat"
type_synonym pt = "bool \<times> rk"
type_synonym ft = "nat \<times> fm \<times> (nat \<Rightarrow> pt)"

definition lt :: "rk \<Rightarrow> rk \<Rightarrow> bool" where
  "lt r s \<longleftrightarrow> fst r < fst s \<or> (fst r = fst s \<and> snd r < snd s)"
definition up :: "rk \<Rightarrow> rk \<Rightarrow> rk" where
  "up r s = (max (fst r) (fst s), Suc (max (snd r) (snd s)))"

lemma lt_trans: "lt r s \<Longrightarrow> lt s t \<Longrightarrow> lt r t" by (auto simp: lt_def)
lemma lt_up: "lt r (up r s)" "lt s (up r s)" by (auto simp: lt_def up_def max_def)

definition ngT :: "pt \<Rightarrow> pt" where "ngT p = (\<not> fst p, (fst (snd p), Suc (snd (snd p))))"
definition cjT :: "pt \<Rightarrow> pt \<Rightarrow> pt" where "cjT p q = (fst p \<and> fst q, up (snd p) (snd q))"
definition djT :: "pt \<Rightarrow> pt \<Rightarrow> pt" where "djT p q = (fst p \<or> fst q, up (snd p) (snd q))"
definition trT :: "pt \<Rightarrow> pt" where "trT p = (fst p, (1, 0))"
definition qrk :: "fm \<Rightarrow> rk" where "qrk a = (if tfree a then (0, 0) else (1, 3))"

primrec dT :: "(nat \<Rightarrow> pt) \<Rightarrow> fm \<Rightarrow> pt" where
  "dT v (Var n) = v n"
| "dT v (Cst n) = (True, (0, 0))"
| "dT v (Neg a) = ngT (dT v a)"
| "dT v (Conj a b) = cjT (dT v a) (dT v b)"
| "dT v (Disj a b) = djT (dT v a) (dT v b)"
| "dT v (Tr a) = trT (dT v a)"
| "dT v (Ex x a) = ((\<exists>p. fst (dT (v(x:=p)) a)), qrk a)"
| "dT v (All x a) = ((\<forall>p. fst (dT (v(x:=p)) a)), qrk a)"
| "dT v (BigC x a) = ((\<forall>p. fst (dT (v(x:=p)) a) \<longrightarrow> fst p), (0, 0))"

lemma dT_fv: "(\<forall>y\<in>fv a. v y = w y) \<Longrightarrow> dT v a = dT w a"
proof (induct a arbitrary: v w)
  case (Ex x a)
  have "\<And>p. dT (v(x:=p)) a = dT (w(x:=p)) a"
    by (rule Ex.hyps) (use Ex.prems in auto)
  then show ?case by simp
next
  case (All x a)
  have "\<And>p. dT (v(x:=p)) a = dT (w(x:=p)) a"
    by (rule All.hyps) (use All.prems in auto)
  then show ?case by simp
next
  case (BigC x a)
  have "\<And>p. dT (v(x:=p)) a = dT (w(x:=p)) a"
    by (rule BigC.hyps) (use BigC.prems in auto)
  then show ?case by simp
next
  case (Neg a)
  have "dT v a = dT w a" by (rule Neg.hyps) (use Neg.prems in auto)
  then show ?case by simp
next
  case (Tr a)
  have "dT v a = dT w a" by (rule Tr.hyps) (use Tr.prems in auto)
  then show ?case by simp
next
  case (Conj a b)
  have "dT v a = dT w a" by (rule Conj.hyps(1)) (use Conj.prems in auto)
  moreover have "dT v b = dT w b" by (rule Conj.hyps(2)) (use Conj.prems in auto)
  ultimately show ?case by simp
next
  case (Disj a b)
  have "dT v a = dT w a" by (rule Disj.hyps(1)) (use Disj.prems in auto)
  moreover have "dT v b = dT w b" by (rule Disj.hyps(2)) (use Disj.prems in auto)
  ultimately show ?case by simp
qed simp_all

text \<open>A truth-free formula whose parameters have lower-tier values has a lower-tier
  value. Quantified subformulas need no induction hypothesis: their rank is fixed by
  the syntax of the body.\<close>
lemma tfree_low: "tfree a \<Longrightarrow> (\<forall>y\<in>fv a. fst (snd (v y)) = 0) \<Longrightarrow> fst (snd (dT v a)) = 0"
proof (induct a arbitrary: v)
  case (Neg a)
  have "fst (snd (dT v a)) = 0" by (rule Neg.hyps) (use Neg.prems in auto)
  then show ?case by (simp add: ngT_def)
next
  case (Conj a b)
  have "fst (snd (dT v a)) = 0" by (rule Conj.hyps(1)) (use Conj.prems in auto)
  moreover have "fst (snd (dT v b)) = 0" by (rule Conj.hyps(2)) (use Conj.prems in auto)
  ultimately show ?case by (simp add: cjT_def up_def)
next
  case (Disj a b)
  have "fst (snd (dT v a)) = 0" by (rule Disj.hyps(1)) (use Disj.prems in auto)
  moreover have "fst (snd (dT v b)) = 0" by (rule Disj.hyps(2)) (use Disj.prems in auto)
  ultimately show ?case by (simp add: djT_def up_def)
next
  case (All x a)
  then show ?case by (simp add: qrk_def)
next
  case (Ex x a)
  then show ?case by (simp add: qrk_def)
qed simp_all

definition cut :: "fm \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> pt) \<Rightarrow> (nat \<Rightarrow> pt)" where
  "cut a x v = (\<lambda>y. if y \<in> fv a - {x} then v y else (True, (0, 0)))"
definition lamT :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> pt) \<Rightarrow> ft" where "lamT x a v = (x, a, cut a x v)"
definition appT :: "ft \<Rightarrow> pt \<Rightarrow> pt" where
  "appT f p = dT ((snd (snd f))(fst f := p)) (fst (snd f))"
definition exqT :: "ft \<Rightarrow> pt" where "exqT f = ((\<exists>p. fst (appT f p)), qrk (fst (snd f)))"
definition allqT :: "ft \<Rightarrow> pt" where "allqT f = ((\<forall>p. fst (appT f p)), qrk (fst (snd f)))"
definition bigT :: "ft \<Rightarrow> pt" where "bigT f = ((\<forall>p. fst (appT f p) \<longrightarrow> fst p), (0, 0))"

definition temB :: fm where "temB = Disj (Tr (Var 0)) (Neg (Tr (Var 0)))"
definition e0T :: "nat \<Rightarrow> pt" where "e0T = (\<lambda>_. (True, (0, 0)))"
definition admT :: "ft \<Rightarrow> bool" where
  "admT f \<longleftrightarrow> f \<in> {lamT 0 (Var 0) e0T, lamT 0 (Tr (Var 0)) e0T, lamT 0 temB e0T}"
definition GT :: "pt set \<Rightarrow> pt \<Rightarrow> bool" where
  "GT \<Gamma> q \<longleftrightarrow> (\<exists>p. \<Gamma> = {p} \<and> fst p \<and> fst q \<and> lt (snd p) (snd q))"

interpretation MT: gsig "fst :: pt \<Rightarrow> bool" "\<lambda>_. (True, (0, 0))" ngT cjT djT trT
  appT exqT allqT bigT lamT admT GT e0T "(True, (0, 0))" .

lemma app_lam: "appT (lamT x a v) p = dT (v(x:=p)) a"
proof -
  have "dT ((cut a x v)(x:=p)) a = dT (v(x:=p)) a" by (rule dT_fv) (auto simp: cut_def)
  thus ?thesis by (simp add: appT_def lamT_def)
qed

lemma lam_body: "fst (snd (lamT x a v)) = a" by (simp add: lamT_def)

lemma lamT_fv: "\<forall>y\<in>fv a - {x}. v y = w y \<Longrightarrow> lamT x a v = lamT x a w"
  by (auto simp: lamT_def cut_def fun_eq_iff)

lemma quantT:
  "exqT (lamT x a v) = ((\<exists>p. fst (dT (v(x:=p)) a)), qrk a)"
  "allqT (lamT x a v) = ((\<forall>p. fst (dT (v(x:=p)) a)), qrk a)"
  "bigT (lamT x a v) = ((\<forall>p. fst (dT (v(x:=p)) a) \<longrightarrow> fst p), (0, 0))"
  by (simp_all add: exqT_def allqT_def bigT_def app_lam lam_body)

lemma MT_den: "MT.den = dT"
proof (intro ext)
  fix v a show "MT.den v a = dT v a"
    by (induction a arbitrary: v) (simp_all add: quantT)
qed

lemma MT_PG: "MT.PG p q \<longleftrightarrow> fst p \<and> fst q \<and> lt (snd p) (snd q)"
proof
  assume "MT.PG p q"
  thus "fst p \<and> fst q \<and> lt (snd p) (snd q)" unfolding MT.PG_def GT_def by auto
next
  assume A: "fst p \<and> fst q \<and> lt (snd p) (snd q)"
  have "p \<in> {p} \<and> GT {p} q" using A unfolding GT_def by blast
  thus "MT.PG p q" unfolding MT.PG_def by (rule exI)
qed

text \<open>The witnesses. f_tem is constant with value (True, (1, 2)); its universal closure
  is (True, (1, 3)).\<close>
lemma MT_wit:
  "MT.f_id = lamT 0 (Var 0) e0T" "MT.f_tr = lamT 0 (Tr (Var 0)) e0T"
  "MT.f_tem = lamT 0 temB e0T" "MT.f_em = lamT 0 (Disj (Var 0) (Neg (Var 0))) e0T"
  by (simp_all add: MT.f_id_def MT.f_tr_def MT.f_tem_def MT.f_em_def temB_def)

lemma wit_app:
  "appT (lamT 0 (Var 0) e0T) p = p" "appT (lamT 0 (Tr (Var 0)) e0T) p = trT p"
  "appT (lamT 0 temB e0T) p = (True, (1, 2))"
  by (auto simp: app_lam temB_def djT_def trT_def ngT_def up_def)

lemma tem_all: "allqT (lamT 0 temB e0T) = (True, (1, 3))"
proof -
  have "qrk temB = (1, 3)" by (simp add: qrk_def temB_def)
  thus ?thesis by (simp add: allqT_def wit_app lam_body)
qed

lemma MT_adm: "MT.C1_NO_EM" "\<not> admT MT.f_em"
proof -
  show "MT.C1_NO_EM" by (simp add: MT.C1_NO_EM_def admT_def MT_wit)
  show "\<not> admT MT.f_em" by (simp add: admT_def MT_wit lamT_def temB_def)
qed

lemma MT_core: "MT.FACT" "MT.LAM_CORE" "MT.N1" "MT.N2" "MT.N5_chain"
  and MT_N4: "MT.N4_pair (True, (0, 0)) (ngT (ngT (True, (0, 0))))"
proof -
  show "MT.FACT" by (auto simp: MT.FACT_def GT_def)
  show "MT.LAM_CORE" unfolding MT.LAM_CORE_def MT_den using lamT_fv by (simp add: app_lam)
  have g: "GT {(True, (0, 0))} (True, (0, 1))" by (simp add: GT_def lt_def)
  show "MT.N1" unfolding MT.N1_def using g by blast
  thus "MT.N2" unfolding MT.N2_def
    by (intro conjI exI[of _ "(True, (0, 0)) :: pt"] exI[of _ "(True, (0, 1)) :: pt"]
          exI[of _ "(True, (0, 2)) :: pt"]) simp_all
  show "MT.N5_chain" unfolding MT.N5_chain_def
    by (intro exI[of _ "(True, (0, 0)) :: pt"] exI[of _ "(True, (0, 1)) :: pt"]
          exI[of _ "(True, (0, 2)) :: pt"] exI[of _ "(True, (0, 3)) :: pt"])
       (simp add: MT_PG lt_def)
  have n: "ngT (ngT (True, (0, 0))) = (True, (0, 2))" by (simp add: ngT_def)
  have m1: "GT {(True, (0, 0))} (True, (0, 2))" by (simp add: GT_def lt_def)
  have m2: "\<not> GT {(True, (0, 0))} (True, (0, 0))" by (simp add: GT_def lt_def)
  have "{\<Gamma>. GT \<Gamma> (True, (0, 0))} \<noteq> {\<Gamma>. GT \<Gamma> (True, (0, 2))}" using m1 m2 by blast
  thus "MT.N4_pair (True, (0, 0)) (ngT (ngT (True, (0, 0))))"
    unfolding MT.N4_pair_def n by simp
qed

lemma MT_BETA_ID: "MT.BETA_ID" by (simp add: MT.BETA_ID_def MT_den app_lam)

lemma MT_classical: "MT.CL_PROP'" "MT.CL_QUANT'" "MT.TS_FULL'" "MT.TS_TYPED"
proof -
  show "MT.CL_PROP'" by (simp add: MT.CL_PROP'_def ngT_def cjT_def djT_def)
  show "MT.CL_QUANT'" by (simp add: MT.CL_QUANT'_def exqT_def allqT_def bigT_def MT.sat_def)
  show "MT.TS_FULL'" by (simp add: MT.TS_FULL'_def trT_def)
  show "MT.TS_TYPED" by (simp add: MT.TS_TYPED_def trT_def)
qed

lemma MT_TR_TYPED: "MT.TR_TYPED"
  unfolding MT.TR_TYPED_def MT_den
proof (intro allI impI)
  fix a :: fm and v :: "nat \<Rightarrow> pt"
  assume A: "tfree a \<and> fv a = {} \<and> fst (dT v a)"
  have low: "fst (snd (dT v a)) = 0" by (rule tfree_low) (use A in auto)
  show "GT {dT v a} (trT (dT v a))" using A low by (simp add: GT_def trT_def lt_def)
qed

lemma MT_order: "MT.IRR_F" "MT.ASYM_P" "MT.TRANS_P"
proof -
  show "MT.IRR_F" by (auto simp: MT.IRR_F_def GT_def lt_def)
  show "MT.ASYM_P" by (auto simp: MT.ASYM_P_def MT_PG lt_def)
  show "MT.TRANS_P" unfolding MT.TRANS_P_def MT_PG using lt_trans by blast
qed

lemma MT_DISJ: "MT.DISJ_ONE" "MT.DISJ_PART"
proof -
  show "MT.DISJ_ONE" by (auto simp: MT.DISJ_ONE_def GT_def djT_def lt_up)
  show "MT.DISJ_PART" by (auto simp: MT.DISJ_PART_def MT_PG djT_def lt_up)
qed

text \<open>Of the admissible functions only f_tem is true of everything, so the universal
  entries concern it alone.\<close>
lemma adm_total_tem:
  assumes "admT f" "\<forall>a. fst (appT f a)" shows "f = lamT 0 temB e0T"
proof -
  have f0: "fst (appT f (False, (0, 0)))" using assms(2) by blast
  have d: "f = lamT 0 (Var 0) e0T \<or> f = lamT 0 (Tr (Var 0)) e0T \<or> f = lamT 0 temB e0T"
    using assms(1) unfolding admT_def by blast
  show ?thesis using d
  proof (elim disjE)
    assume "f = lamT 0 (Var 0) e0T" with f0 show ?thesis by (simp add: wit_app)
  next
    assume "f = lamT 0 (Tr (Var 0)) e0T" with f0 show ?thesis by (simp add: wit_app trT_def)
  next
    assume "f = lamT 0 temB e0T" thus ?thesis .
  qed
qed

lemma MT_ALL: "MT.ALL_INST" "MT.ALL_PART"
proof -
  show "MT.ALL_INST" unfolding MT.ALL_INST_def
  proof (intro allI impI)
    fix f :: ft assume A: "admT f \<and> (\<forall>a. fst (appT f a))"
    have e: "f = lamT 0 temB e0T" using adm_total_tem A by blast
    have i: "MT.inst f = {(True, (1, 2))}" unfolding MT.inst_def e by (auto simp: wit_app)
    show "GT (MT.inst f) (allqT f)" unfolding i unfolding e tem_all by (simp add: GT_def lt_def)
  qed
  show "MT.ALL_PART" unfolding MT.ALL_PART_def
  proof (intro allI impI)
    fix f :: ft and a :: pt assume A: "admT f \<and> (\<forall>b. fst (appT f b))"
    have e: "f = lamT 0 temB e0T" using adm_total_tem A by blast
    show "MT.PG (appT f a) (allqT f)" unfolding e tem_all wit_app MT_PG by (simp add: lt_def)
  qed
qed

text \<open>The step of Fine's argument that fails: the universal closure s of f_tem is true
  and does not ground its own truth ascription. So TR.PART and TR.FULL fail.\<close>
lemma MT_not_TR_PART:
  "fst (allqT MT.f_tem)" "\<not> MT.PG (allqT MT.f_tem) (trT (allqT MT.f_tem))" "\<not> MT.TR_PART"
proof -
  have s: "allqT MT.f_tem = (True, (1, 3))" by (simp add: MT_wit tem_all)
  show t: "fst (allqT MT.f_tem)" by (simp add: s)
  show n: "\<not> MT.PG (allqT MT.f_tem) (trT (allqT MT.f_tem))"
    by (simp add: s MT_PG trT_def lt_def)
  show "\<not> MT.TR_PART"
  proof
    assume A: "MT.TR_PART"
    have "MT.PG (allqT MT.f_tem) (trT (allqT MT.f_tem))"
      using A[unfolded MT.TR_PART_def, rule_format, of "allqT MT.f_tem"] t by blast
    thus False using n by blast
  qed
qed

text \<open>N3 instances. DISJ.ONE: (True, (0, 0)) grounds its self-disjunction (True, (0, 1)).
  ALL.INST: the one instance of f_tem grounds its universal closure. TR.TYPED: the
  truth denoted by the closed truth-free formula Cst 0 grounds its truth ascription.\<close>
lemma MT_N3:
  "GT {(True, (0, 0))} (djT (True, (0, 0)) (True, (0, 0)))
   \<and> admT MT.f_tem \<and> MT.inst MT.f_tem = {(True, (1, 2))} \<and> allqT MT.f_tem = (True, (1, 3))
   \<and> GT (MT.inst MT.f_tem) (allqT MT.f_tem)
   \<and> GT {dT e0T (Cst 0)} (trT (dT e0T (Cst 0))) \<and> dT e0T (Cst 0) \<noteq> trT (dT e0T (Cst 0))"
proof -
  have ad: "admT MT.f_tem" by (simp add: admT_def MT_wit)
  have i: "MT.inst MT.f_tem = {(True, (1, 2))}"
    unfolding MT.inst_def by (auto simp: MT_wit wit_app)
  have a: "allqT MT.f_tem = (True, (1, 3))" by (simp add: MT_wit tem_all)
  show ?thesis using ad i a by (simp add: djT_def up_def GT_def trT_def lt_def)
qed

theorem MT_package:
  "MT.FACT \<and> MT.LAM_CORE \<and> MT.C1_NO_EM \<and> MT.BETA_ID \<and> MT.CL_PROP' \<and> MT.CL_QUANT'
   \<and> MT.TS_FULL' \<and> MT.TS_TYPED \<and> MT.TR_TYPED \<and> MT.ALL_INST \<and> MT.ALL_PART
   \<and> MT.DISJ_ONE \<and> MT.DISJ_PART \<and> MT.TRANS_P \<and> MT.IRR_F \<and> MT.ASYM_P
   \<and> MT.N1 \<and> MT.N2 \<and> MT.N5_chain \<and> \<not> MT.TR_PART \<and> \<not> admT MT.f_em"
  using MT_core MT_adm MT_BETA_ID MT_classical MT_TR_TYPED MT_ALL MT_DISJ MT_order
    MT_not_TR_PART(3)
  by blast

text \<open>MT and the witness entries of decision D9.\<close>
theorem MT_W: "MT.W_ID \<and> MT.W_TR \<and> MT.W_TEM \<and> \<not> MT.W_EM"
  by (simp add: MT.W_ID_def MT.W_TR_def MT.W_TEM_def MT.W_EM_def admT_def MT_wit lamT_def
        temB_def)

section \<open>Model U: existential and universal grounding with typed grounding of truth\<close>

text \<open>
  Model T with a smaller set of admissible functions: f_tr and f_tem are admissible,
  f_id and f_em are not. Everything else is as in model T. With f_id not admissible the
  existential entries can hold as well: a true instance of f_tr or f_tem has rank (1, 0)
  or (1, 2), and its existential closure has rank (1, 3). So the model satisfies, with
  W.TR and W.TEM, the "something is true" package, Fine's particular argument for
  propositions and his universal argument, each with TR.TYPED in place of TR.PART.
  In each the step from a quantified truth to its truth ascription fails:
  "something is true" is grounded in its own truth ascription and does not ground it.
\<close>

definition admU :: "ft \<Rightarrow> bool" where
  "admU f \<longleftrightarrow> f \<in> {lamT 0 (Tr (Var 0)) e0T, lamT 0 temB e0T}"

interpretation MU: gsig "fst :: pt \<Rightarrow> bool" "\<lambda>_. (True, (0, 0))" ngT cjT djT trT
  appT exqT allqT bigT lamT admU GT e0T "(True, (0, 0))" .

lemma MU_den: "MU.den = dT"
proof (intro ext)
  fix v a show "MU.den v a = dT v a"
    by (induction a arbitrary: v) (simp_all add: quantT)
qed

lemma MU_PG: "MU.PG p q \<longleftrightarrow> fst p \<and> fst q \<and> lt (snd p) (snd q)"
proof
  assume "MU.PG p q"
  thus "fst p \<and> fst q \<and> lt (snd p) (snd q)" unfolding MU.PG_def GT_def by auto
next
  assume A: "fst p \<and> fst q \<and> lt (snd p) (snd q)"
  have "p \<in> {p} \<and> GT {p} q" using A unfolding GT_def by blast
  thus "MU.PG p q" unfolding MU.PG_def by (rule exI)
qed

lemma MU_wit:
  "MU.f_id = lamT 0 (Var 0) e0T" "MU.f_tr = lamT 0 (Tr (Var 0)) e0T"
  "MU.f_tem = lamT 0 temB e0T" "MU.f_em = lamT 0 (Disj (Var 0) (Neg (Var 0))) e0T"
  by (simp_all add: MU.f_id_def MU.f_tr_def MU.f_tem_def MU.f_em_def temB_def)

lemma MU_core: "MU.FACT" "MU.LAM_CORE" "MU.N1" "MU.N2" "MU.N5_chain"
  and MU_N4: "MU.N4_pair (True, (0, 0)) (ngT (ngT (True, (0, 0))))"
proof -
  show "MU.FACT" by (auto simp: MU.FACT_def GT_def)
  show "MU.LAM_CORE" unfolding MU.LAM_CORE_def MU_den using lamT_fv by (simp add: app_lam)
  have g: "GT {(True, (0, 0))} (True, (0, 1))" by (simp add: GT_def lt_def)
  show "MU.N1" unfolding MU.N1_def using g by blast
  thus "MU.N2" unfolding MU.N2_def
    by (intro conjI exI[of _ "(True, (0, 0)) :: pt"] exI[of _ "(True, (0, 1)) :: pt"]
          exI[of _ "(True, (0, 2)) :: pt"]) simp_all
  show "MU.N5_chain" unfolding MU.N5_chain_def
    by (intro exI[of _ "(True, (0, 0)) :: pt"] exI[of _ "(True, (0, 1)) :: pt"]
          exI[of _ "(True, (0, 2)) :: pt"] exI[of _ "(True, (0, 3)) :: pt"])
       (simp add: MU_PG lt_def)
  have n: "ngT (ngT (True, (0, 0))) = (True, (0, 2))" by (simp add: ngT_def)
  have m1: "GT {(True, (0, 0))} (True, (0, 2))" by (simp add: GT_def lt_def)
  have m2: "\<not> GT {(True, (0, 0))} (True, (0, 0))" by (simp add: GT_def lt_def)
  have "{\<Gamma>. GT \<Gamma> (True, (0, 0))} \<noteq> {\<Gamma>. GT \<Gamma> (True, (0, 2))}" using m1 m2 by blast
  thus "MU.N4_pair (True, (0, 0)) (ngT (ngT (True, (0, 0))))"
    unfolding MU.N4_pair_def n by simp
qed

lemma MU_BETA_ID: "MU.BETA_ID" by (simp add: MU.BETA_ID_def MU_den app_lam)

lemma MU_classical: "MU.CL_PROP'" "MU.CL_QUANT'" "MU.TS_FULL'" "MU.TS_TYPED"
proof -
  show "MU.CL_PROP'" by (simp add: MU.CL_PROP'_def ngT_def cjT_def djT_def)
  show "MU.CL_QUANT'" by (simp add: MU.CL_QUANT'_def exqT_def allqT_def bigT_def MU.sat_def)
  show "MU.TS_FULL'" by (simp add: MU.TS_FULL'_def trT_def)
  show "MU.TS_TYPED" by (simp add: MU.TS_TYPED_def trT_def)
qed

lemma MU_TR_TYPED: "MU.TR_TYPED"
  unfolding MU.TR_TYPED_def MU_den
proof (intro allI impI)
  fix a :: fm and v :: "nat \<Rightarrow> pt"
  assume A: "tfree a \<and> fv a = {} \<and> fst (dT v a)"
  have low: "fst (snd (dT v a)) = 0" by (rule tfree_low) (use A in auto)
  show "GT {dT v a} (trT (dT v a))" using A low by (simp add: GT_def trT_def lt_def)
qed

lemma MU_order: "MU.IRR_F" "MU.ASYM_P" "MU.TRANS_P"
proof -
  show "MU.IRR_F" by (auto simp: MU.IRR_F_def GT_def lt_def)
  show "MU.ASYM_P" by (auto simp: MU.ASYM_P_def MU_PG lt_def)
  show "MU.TRANS_P" unfolding MU.TRANS_P_def MU_PG using lt_trans by blast
qed

lemma MU_DISJ: "MU.DISJ_ONE" "MU.DISJ_PART"
proof -
  show "MU.DISJ_ONE" by (auto simp: MU.DISJ_ONE_def GT_def djT_def lt_up)
  show "MU.DISJ_PART" by (auto simp: MU.DISJ_PART_def MU_PG djT_def lt_up)
qed


theorem MU_W: "MU.W_TR \<and> MU.W_TEM \<and> \<not> MU.W_ID \<and> \<not> MU.W_EM"
  by (simp add: MU.W_ID_def MU.W_TR_def MU.W_TEM_def MU.W_EM_def admU_def MU_wit lamT_def
        temB_def)

lemma admU_total_tem:
  assumes "admU f" "\<forall>a. fst (appT f a)" shows "f = lamT 0 temB e0T"
proof -
  have f0: "fst (appT f (False, (0, 0)))" using assms(2) by blast
  have d: "f = lamT 0 (Tr (Var 0)) e0T \<or> f = lamT 0 temB e0T"
    using assms(1) unfolding admU_def by blast
  show ?thesis using d
  proof (elim disjE)
    assume "f = lamT 0 (Tr (Var 0)) e0T" with f0 show ?thesis by (simp add: wit_app trT_def)
  next
    assume "f = lamT 0 temB e0T" thus ?thesis .
  qed
qed

lemma MU_ALL: "MU.ALL_INST" "MU.ALL_PART"
proof -
  show "MU.ALL_INST" unfolding MU.ALL_INST_def
  proof (intro allI impI)
    fix f :: ft assume A: "admU f \<and> (\<forall>a. fst (appT f a))"
    have e: "f = lamT 0 temB e0T" using admU_total_tem A by blast
    have i: "MU.inst f = {(True, (1, 2))}" unfolding MU.inst_def e by (auto simp: wit_app)
    show "GT (MU.inst f) (allqT f)" unfolding i unfolding e tem_all by (simp add: GT_def lt_def)
  qed
  show "MU.ALL_PART" unfolding MU.ALL_PART_def
  proof (intro allI impI)
    fix f :: ft and a :: pt assume A: "admU f \<and> (\<forall>b. fst (appT f b))"
    have e: "f = lamT 0 temB e0T" using admU_total_tem A by blast
    show "MU.PG (appT f a) (allqT f)" unfolding e tem_all wit_app MU_PG by (simp add: lt_def)
  qed
qed

text \<open>The existential closures of the two admissible functions are true and have
  rank (1, 3).\<close>
lemma tr_ex: "exqT (lamT 0 (Tr (Var 0)) e0T) = (True, (1, 3))"
proof -
  have "fst (appT (lamT 0 (Tr (Var 0)) e0T) (True, (0, 0)))" by (simp add: wit_app trT_def)
  hence "\<exists>p. fst (appT (lamT 0 (Tr (Var 0)) e0T) p)" by (rule exI)
  thus ?thesis by (simp add: exqT_def lam_body qrk_def)
qed

lemma tem_ex: "exqT (lamT 0 temB e0T) = (True, (1, 3))"
proof -
  have "qrk temB = (1, 3)" by (simp add: qrk_def temB_def)
  thus ?thesis by (simp add: exqT_def wit_app lam_body)
qed

lemma MU_EX: "MU.EX_FULL" "MU.EX_PART"
proof -
  have k: "GT {appT f a} (exqT f)" if ad: "admU f" and t: "fst (appT f a)" for f a
  proof -
    have d: "f = lamT 0 (Tr (Var 0)) e0T \<or> f = lamT 0 temB e0T"
      using ad unfolding admU_def by blast
    show ?thesis using d
    proof (elim disjE)
      assume e: "f = lamT 0 (Tr (Var 0)) e0T"
      have "fst a" using t unfolding e wit_app by (simp add: trT_def)
      thus ?thesis unfolding e tr_ex wit_app by (simp add: GT_def trT_def lt_def)
    next
      assume e: "f = lamT 0 temB e0T"
      show ?thesis unfolding e tem_ex wit_app by (simp add: GT_def lt_def)
    qed
  qed
  show "MU.EX_FULL" unfolding MU.EX_FULL_def using k by blast
  show "MU.EX_PART" unfolding MU.EX_PART_def MU.PG_def
  proof (intro allI impI)
    fix f :: ft and a :: pt assume A: "admU f \<and> fst (appT f a)"
    have "appT f a \<in> {appT f a} \<and> GT {appT f a} (exqT f)" using k A by simp
    thus "\<exists>\<Gamma>. appT f a \<in> \<Gamma> \<and> GT \<Gamma> (exqT f)" by (rule exI)
  qed
qed

text \<open>Where the circle of "something is true" breaks. E, the existential closure of
  f_tr, is true; its truth ascription grounds it (an instance, by EX.FULL); E does not
  ground its truth ascription. So TR.PART fails, and with it TR.FULL.\<close>
lemma MU_not_TR_PART:
  "fst (exqT MU.f_tr)" "MU.PG (trT (exqT MU.f_tr)) (exqT MU.f_tr)"
  "\<not> MU.PG (exqT MU.f_tr) (trT (exqT MU.f_tr))" "\<not> MU.TR_PART"
proof -
  have s: "exqT MU.f_tr = (True, (1, 3))" by (simp add: MU_wit tr_ex)
  show t: "fst (exqT MU.f_tr)" by (simp add: s)
  show "MU.PG (trT (exqT MU.f_tr)) (exqT MU.f_tr)" by (simp add: s MU_PG trT_def lt_def)
  show n: "\<not> MU.PG (exqT MU.f_tr) (trT (exqT MU.f_tr))"
    by (simp add: s MU_PG trT_def lt_def)
  show "\<not> MU.TR_PART"
  proof
    assume A: "MU.TR_PART"
    have "MU.PG (exqT MU.f_tr) (trT (exqT MU.f_tr))"
      using A[unfolded MU.TR_PART_def, rule_format, of "exqT MU.f_tr"] t by blast
    thus False using n by blast
  qed
qed

text \<open>N3 instances for the entries that model T does not have. EX.FULL: the true
  instance tr (True, (0, 0)) of f_tr grounds the existential closure and differs from
  it. The instances for DISJ.ONE, ALL.INST and TR.TYPED are those of MT_N3, which
  mention no admissibility except that of f_tem.\<close>
lemma MU_N3:
  "admU MU.f_tr \<and> fst (appT MU.f_tr (True, (0, 0)))
   \<and> GT {appT MU.f_tr (True, (0, 0))} (exqT MU.f_tr)
   \<and> appT MU.f_tr (True, (0, 0)) \<noteq> exqT MU.f_tr
   \<and> admU MU.f_tem \<and> GT (MU.inst MU.f_tem) (allqT MU.f_tem)
   \<and> GT {(True, (0, 0))} (djT (True, (0, 0)) (True, (0, 0)))
   \<and> GT {dT e0T (Cst 0)} (trT (dT e0T (Cst 0)))"
proof -
  have i: "MU.inst MU.f_tem = {(True, (1, 2))}"
    unfolding MU.inst_def by (auto simp: MU_wit wit_app)
  have a: "allqT MU.f_tem = (True, (1, 3))" by (simp add: MU_wit tem_all)
  have x: "exqT MU.f_tr = (True, (1, 3))" by (simp add: MU_wit tr_ex)
  have y: "appT MU.f_tr (True, (0, 0)) = (True, (1, 0))" by (simp add: MU_wit wit_app trT_def)
  have ad: "admU MU.f_tr" "admU MU.f_tem" by (simp_all add: admU_def MU_wit)
  show ?thesis using ad unfolding i a x y by (simp add: djT_def up_def GT_def trT_def lt_def)
qed

theorem MU_package:
  "MU.FACT \<and> MU.LAM_CORE \<and> MU.W_TR \<and> MU.W_TEM \<and> MU.BETA_ID \<and> MU.CL_PROP' \<and> MU.CL_QUANT'
   \<and> MU.TS_FULL' \<and> MU.TS_TYPED \<and> MU.TR_TYPED \<and> MU.EX_FULL \<and> MU.EX_PART
   \<and> MU.ALL_INST \<and> MU.ALL_PART \<and> MU.DISJ_ONE \<and> MU.DISJ_PART
   \<and> MU.TRANS_P \<and> MU.IRR_F \<and> MU.ASYM_P \<and> MU.N1 \<and> MU.N2 \<and> MU.N5_chain
   \<and> \<not> MU.TR_PART \<and> \<not> MU.W_ID \<and> \<not> MU.W_EM"
  using MU_core MU_W MU_BETA_ID MU_classical MU_TR_TYPED MU_EX MU_ALL MU_DISJ MU_order
    MU_not_TR_PART(4)
  by blast

end
