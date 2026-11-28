theory Korbmacher_Typed
  imports Separation_Models Puzzle_Packages
begin

text \<open>
  Registry 0.8.0-draft (decision D10). Korbmacher 2018b blocks Fine's circle by typing the
  truth predicate. Tr_1 applies only to arithmetic sentences (T3, p. 204), so
  Tr_1(\<exists>xTr_1(x)) is untrue and is not an instance that grounds \<exists>xTr_1(x). The
  Aristotelian principle still holds at every level (APU, p. 207).

  This theory transcribes his two-level theory PGA_2 as far as the registry's one truth
  operator allows. The registry's T plays the part of truth at some level, tr plays Tr_1,
  and truth-free formulas play L_0. The new entry TS.T3 states Korbmacher's T3. It is
  incompatible with TS.FULL (TS_T3_not_FULL) and forces a grain on propositions
  (TS_T3_grain).

    MK  Model of the target P.KORBMACHER.2018B.TYPED (finding F22). W.TR, W.TEM,
        BETA.ID, CL.PROP, CL.QUANT, TS.TYPED, TS.T3, TR.TYPED, EX.FULL, ALL.INST,
        DISJ.ONE, NEG.DN, CONJ.BIN, TRANS.P, IRR.F and ASYM.P hold, at N5. TS.FULL and
        TR.PART fail. MK is model MU with two changes: a truth ascription is true only of
        a true proposition of the lower tier, and ground may have several premises.

  In MK "something is true" is not grounded in its own truth ascription, which is untrue
  (MK_blocks). And the non-truth of the universal closure s of f_tem helps ground s
  (MK_neg_tr_grounds). Fine 2010 p. 104 calls that unacceptable in his principle (*).
\<close>

section \<open>TS.T3 against TS.FULL and against coarse propositions\<close>

theorem TS_T3_not_FULL:
  assumes t3: "TS_T3" and ts: "TS_FULL" and clq: "CL_QUANT" and beta: "BETA_ID"
      and lc: "LAM_CORE"
  shows False
proof -
  let ?f = "lam 0 (Tr (Var 0)) e0"
  obtain q where q: "T q" using CL_QUANT_truth[OF clq] by blast
  have "app ?f q = tr q" using beta unfolding BETA_ID_def by simp
  hence "T (app ?f q)" using ts q unfolding TS_FULL_def by simp
  hence ex: "T (exq ?f)" using clq unfolding CL_QUANT_def by blast
  have "den e0 (Ex 0 (Tr (Var 0))) = exq ?f" by simp
  moreover have "\<not> tfree (Ex 0 (Tr (Var 0)))" "fv (Ex 0 (Tr (Var 0))) = {}" by simp_all
  ultimately have "\<not> T (tr (exq ?f))" using t3 unfolding TS_T3_def by metis
  thus False using ts ex unfolding TS_FULL_def by blast
qed

text \<open>The grain TS.T3 forces. A true proposition presented by a closed truth-free formula
  is not presented by any closed formula that mentions truth.\<close>
theorem TS_T3_grain:
  assumes "TS_TYPED" "TS_T3" "tfree a" "fv a = {}" "\<not> tfree b" "fv b = {}" "T (den v a)"
  shows "den v a \<noteq> den w b"
proof
  assume e: "den v a = den w b"
  have "T (tr (den v a))" using assms(1,3,4,7) unfolding TS_TYPED_def by blast
  moreover have "\<not> T (tr (den w b))" using assms(2,5,6) unfolding TS_T3_def by blast
  ultimately show False using e by simp
qed

section \<open>Further entries restated in the locale\<close>

context gsig
begin
definition NEG_DN_K :: bool where
  "NEG_DN_K \<longleftrightarrow> (\<forall>p. T p \<longrightarrow> G {p} (neg (neg p)))"
definition CONJ_BIN_K :: bool where
  "CONJ_BIN_K \<longleftrightarrow> (\<forall>p q. T p \<and> T q \<longrightarrow> G {p, q} (conj p q))"
definition TS_T3_K :: bool where
  "TS_T3_K \<longleftrightarrow> (\<forall>a v. \<not> tfree a \<and> fv a = {} \<longrightarrow> \<not> T (tr (den v a)))"

text \<open>The Aristotelian principle with the antecedent of the sources. Fine's Propositional
  Grounding (fine2010 p. 101) and Kr\"amer's (A) ("If <p> is true then p \<prec> <p> is true",
  kramer2013) and Korbmacher's APT (korbmacher2018b p. 198) all have the truth of the truth
  ascription as antecedent. The registry's TR.PART and TR.FULL have T p instead (reading
  "antecedent" on TR.PART). Defined here for finding F20; not a registry entry.\<close>
definition TR_PART_A :: bool where
  "TR_PART_A \<longleftrightarrow> (\<forall>p. T (tr p) \<longrightarrow> PG p (tr p))"
definition TR_FULL_A :: bool where
  "TR_FULL_A \<longleftrightarrow> (\<forall>p. T (tr p) \<longrightarrow> G {p} (tr p))"

text \<open>With FACT the registry's TR.PART yields truth introduction, the half of TS.FULL that
  the old target proofs used. Under TS.FULL the two antecedents coincide.\<close>
lemma TR_PART_TI: "FACT \<Longrightarrow> TR_PART \<Longrightarrow> T p \<Longrightarrow> T (tr p)"
  unfolding FACT_def TR_PART_def PG_def by blast

lemma TR_PART_A_iff: "TS_FULL' \<Longrightarrow> TR_PART_A \<longleftrightarrow> TR_PART"
  unfolding TS_FULL'_def TR_PART_A_def TR_PART_def by blast

lemma TR_FULL_A_PART_A: "TR_FULL_A \<Longrightarrow> TR_PART_A"
  unfolding TR_FULL_A_def TR_PART_A_def PG_def by blast

text \<open>The partial entries from the full ones, restated in the locale (cf. Order.thy).\<close>
lemma EX_FULL_PART_K: "EX_FULL \<Longrightarrow> EX_PART"
  unfolding EX_FULL_def EX_PART_def PG_def by blast
lemma ALL_INST_PART_K: "ALL_INST \<Longrightarrow> ALL_PART"
  unfolding ALL_INST_def ALL_PART_def PG_def inst_def by blast
lemma DISJ_ONE_PART_K: "DISJ_ONE \<Longrightarrow> DISJ_PART"
  unfolding DISJ_ONE_def DISJ_PART_def PG_def by blast
end

lemma K_faithful_korb:
  "K.NEG_DN_K = NEG_DN" "K.CONJ_BIN_K = CONJ_BIN" "K.TS_T3_K = TS_T3"
  by (simp_all add: K_den K.NEG_DN_K_def NEG_DN_def K.CONJ_BIN_K_def CONJ_BIN_def
        K.TS_T3_K_def TS_T3_def)

section \<open>Model K: two tiers, typed truth ascriptions\<close>

text \<open>Propositions, ranks and connectives are those of MT and MU (Separation_Models.thy).
  What changes is the truth ascription. trK p is true iff p is true and of the lower tier,
  and it has rank (1, 0). A quantified or arbitrary-conjunction proposition whose body
  mentions truth has rank (1, 3). Ground: a non-empty set of truths fully grounds every
  truth of higher rank than each of them.\<close>

definition trK :: "pt \<Rightarrow> pt" where "trK p = (fst p \<and> fst (snd p) = 0, (1, 0))"

primrec dK :: "(nat \<Rightarrow> pt) \<Rightarrow> fm \<Rightarrow> pt" where
  "dK v (Var n) = v n"
| "dK v (Cst n) = (True, (0, 0))"
| "dK v (Neg a) = ngT (dK v a)"
| "dK v (Conj a b) = cjT (dK v a) (dK v b)"
| "dK v (Disj a b) = djT (dK v a) (dK v b)"
| "dK v (Tr a) = trK (dK v a)"
| "dK v (Ex x a) = ((\<exists>p. fst (dK (v(x:=p)) a)), qrk a)"
| "dK v (All x a) = ((\<forall>p. fst (dK (v(x:=p)) a)), qrk a)"
| "dK v (BigC x a) = ((\<forall>p. fst (dK (v(x:=p)) a) \<longrightarrow> fst p), qrk a)"

lemma dK_fv: "(\<forall>y\<in>fv a. v y = w y) \<Longrightarrow> dK v a = dK w a"
proof (induct a arbitrary: v w)
  case (Ex x a)
  have "\<And>p. dK (v(x:=p)) a = dK (w(x:=p)) a"
    by (rule Ex.hyps) (use Ex.prems in auto)
  then show ?case by simp
next
  case (All x a)
  have "\<And>p. dK (v(x:=p)) a = dK (w(x:=p)) a"
    by (rule All.hyps) (use All.prems in auto)
  then show ?case by simp
next
  case (BigC x a)
  have "\<And>p. dK (v(x:=p)) a = dK (w(x:=p)) a"
    by (rule BigC.hyps) (use BigC.prems in auto)
  then show ?case by simp
next
  case (Neg a)
  have "dK v a = dK w a" by (rule Neg.hyps) (use Neg.prems in auto)
  then show ?case by simp
next
  case (Tr a)
  have "dK v a = dK w a" by (rule Tr.hyps) (use Tr.prems in auto)
  then show ?case by simp
next
  case (Conj a b)
  have "dK v a = dK w a" by (rule Conj.hyps(1)) (use Conj.prems in auto)
  moreover have "dK v b = dK w b" by (rule Conj.hyps(2)) (use Conj.prems in auto)
  ultimately show ?case by simp
next
  case (Disj a b)
  have "dK v a = dK w a" by (rule Disj.hyps(1)) (use Disj.prems in auto)
  moreover have "dK v b = dK w b" by (rule Disj.hyps(2)) (use Disj.prems in auto)
  ultimately show ?case by simp
qed simp_all

text \<open>A truth-free formula whose parameters lie in the lower tier denotes a proposition of
  the lower tier. A formula that mentions truth denotes one of the upper tier, whatever
  its parameters.\<close>
lemma tfree_lowK: "tfree a \<Longrightarrow> (\<forall>y\<in>fv a. fst (snd (v y)) = 0) \<Longrightarrow> fst (snd (dK v a)) = 0"
proof (induct a arbitrary: v)
  case (Neg a)
  have "fst (snd (dK v a)) = 0" by (rule Neg.hyps) (use Neg.prems in auto)
  then show ?case by (simp add: ngT_def)
next
  case (Conj a b)
  have "fst (snd (dK v a)) = 0" by (rule Conj.hyps(1)) (use Conj.prems in auto)
  moreover have "fst (snd (dK v b)) = 0" by (rule Conj.hyps(2)) (use Conj.prems in auto)
  ultimately show ?case by (simp add: cjT_def up_def)
next
  case (Disj a b)
  have "fst (snd (dK v a)) = 0" by (rule Disj.hyps(1)) (use Disj.prems in auto)
  moreover have "fst (snd (dK v b)) = 0" by (rule Disj.hyps(2)) (use Disj.prems in auto)
  ultimately show ?case by (simp add: djT_def up_def)
qed (simp_all add: qrk_def)

lemma ntfree_highK: "\<not> tfree a \<Longrightarrow> 0 < fst (snd (dK v a))"
proof (induct a arbitrary: v)
  case (Neg a) then show ?case by (simp add: ngT_def)
next
  case (Conj a b)
  show ?case
  proof (cases "tfree a")
    case True
    hence "\<not> tfree b" using Conj.prems by simp
    hence "0 < fst (snd (dK v b))" by (rule Conj.hyps(2))
    thus ?thesis by (simp add: cjT_def up_def)
  next
    case False
    hence "0 < fst (snd (dK v a))" by (rule Conj.hyps(1))
    thus ?thesis by (simp add: cjT_def up_def)
  qed
next
  case (Disj a b)
  show ?case
  proof (cases "tfree a")
    case True
    hence "\<not> tfree b" using Disj.prems by simp
    hence "0 < fst (snd (dK v b))" by (rule Disj.hyps(2))
    thus ?thesis by (simp add: djT_def up_def)
  next
    case False
    hence "0 < fst (snd (dK v a))" by (rule Disj.hyps(1))
    thus ?thesis by (simp add: djT_def up_def)
  qed
qed (simp_all add: trK_def qrk_def)

definition appK :: "ft \<Rightarrow> pt \<Rightarrow> pt" where
  "appK f p = dK ((snd (snd f))(fst f := p)) (fst (snd f))"
definition exqK :: "ft \<Rightarrow> pt" where "exqK f = ((\<exists>p. fst (appK f p)), qrk (fst (snd f)))"
definition allqK :: "ft \<Rightarrow> pt" where "allqK f = ((\<forall>p. fst (appK f p)), qrk (fst (snd f)))"
definition bigK :: "ft \<Rightarrow> pt" where
  "bigK f = ((\<forall>p. fst (appK f p) \<longrightarrow> fst p), qrk (fst (snd f)))"

definition admK :: "ft \<Rightarrow> bool" where
  "admK f \<longleftrightarrow> f \<in> {lamT 0 (Tr (Var 0)) e0T, lamT 0 temB e0T}"
definition GK :: "pt set \<Rightarrow> pt \<Rightarrow> bool" where
  "GK \<Gamma> q \<longleftrightarrow> \<Gamma> \<noteq> {} \<and> fst q \<and> (\<forall>p\<in>\<Gamma>. fst p \<and> lt (snd p) (snd q))"

interpretation MK: gsig "fst :: pt \<Rightarrow> bool" "\<lambda>_. (True, (0, 0))" ngT cjT djT trK
  appK exqK allqK bigK lamT admK GK e0T "(True, (0, 0))" .

lemma app_lamK: "appK (lamT x a v) p = dK (v(x:=p)) a"
proof -
  have "dK ((cut a x v)(x:=p)) a = dK (v(x:=p)) a" by (rule dK_fv) (auto simp: cut_def)
  thus ?thesis by (simp add: appK_def lamT_def)
qed

lemma quantK:
  "exqK (lamT x a v) = ((\<exists>p. fst (dK (v(x:=p)) a)), qrk a)"
  "allqK (lamT x a v) = ((\<forall>p. fst (dK (v(x:=p)) a)), qrk a)"
  "bigK (lamT x a v) = ((\<forall>p. fst (dK (v(x:=p)) a) \<longrightarrow> fst p), qrk a)"
  by (simp_all add: exqK_def allqK_def bigK_def app_lamK lam_body)

lemma MK_den: "MK.den = dK"
proof (intro ext)
  fix v a show "MK.den v a = dK v a"
    by (induction a arbitrary: v) (simp_all add: quantK)
qed

lemma MK_PG: "MK.PG p q \<longleftrightarrow> fst p \<and> fst q \<and> lt (snd p) (snd q)"
proof
  assume "MK.PG p q"
  thus "fst p \<and> fst q \<and> lt (snd p) (snd q)" unfolding MK.PG_def GK_def by auto
next
  assume A: "fst p \<and> fst q \<and> lt (snd p) (snd q)"
  have "p \<in> {p} \<and> GK {p} q" using A unfolding GK_def by blast
  thus "MK.PG p q" unfolding MK.PG_def by (rule exI)
qed

lemma MK_wit:
  "MK.f_id = lamT 0 (Var 0) e0T" "MK.f_tr = lamT 0 (Tr (Var 0)) e0T"
  "MK.f_tem = lamT 0 temB e0T" "MK.f_em = lamT 0 (Disj (Var 0) (Neg (Var 0))) e0T"
  by (simp_all add: MK.f_id_def MK.f_tr_def MK.f_tem_def MK.f_em_def temB_def)

lemma wit_appK:
  "appK (lamT 0 (Tr (Var 0)) e0T) p = trK p"
  "appK (lamT 0 temB e0T) p = (True, (1, 2))"
  by (auto simp: app_lamK temB_def djT_def trK_def ngT_def up_def)

lemma quant_valK:
  "exqK (lamT 0 (Tr (Var 0)) e0T) = (True, (1, 3))"
  "exqK (lamT 0 temB e0T) = (True, (1, 3))"
  "allqK (lamT 0 temB e0T) = (True, (1, 3))"
  "allqK (lamT 0 (Tr (Var 0)) e0T) = (False, (1, 3))"
proof -
  have q1: "qrk (Tr (Var 0)) = (1, 3)" "qrk temB = (1, 3)" by (simp_all add: qrk_def temB_def)
  have t: "fst (appK (lamT 0 (Tr (Var 0)) e0T) (True, (0, 0)))" by (simp add: wit_appK trK_def)
  have f: "\<not> fst (appK (lamT 0 (Tr (Var 0)) e0T) (False, (0, 0)))" by (simp add: wit_appK trK_def)
  show "exqK (lamT 0 (Tr (Var 0)) e0T) = (True, (1, 3))"
    using t q1 by (auto simp: exqK_def lam_body)
  show "exqK (lamT 0 temB e0T) = (True, (1, 3))" using q1 by (simp add: exqK_def lam_body wit_appK)
  show "allqK (lamT 0 temB e0T) = (True, (1, 3))" using q1 by (simp add: allqK_def lam_body wit_appK)
  show "allqK (lamT 0 (Tr (Var 0)) e0T) = (False, (1, 3))"
    using f q1 by (auto simp: allqK_def lam_body)
qed

theorem MK_W: "MK.W_TR \<and> MK.W_TEM \<and> \<not> MK.W_ID \<and> \<not> MK.W_EM"
  by (simp add: MK.W_ID_def MK.W_TR_def MK.W_TEM_def MK.W_EM_def admK_def MK_wit lamT_def
        temB_def)

lemma MK_core: "MK.FACT" "MK.LAM_CORE" "MK.N1" "MK.N2" "MK.N5_chain"
  and MK_N4: "MK.N4_pair (True, (0, 0)) (ngT (ngT (True, (0, 0))))"
proof -
  show "MK.FACT" by (auto simp: MK.FACT_def GK_def)
  show "MK.LAM_CORE" unfolding MK.LAM_CORE_def MK_den using lamT_fv by (simp add: app_lamK)
  have g: "GK {(True, (0, 0))} (True, (0, 1))" by (simp add: GK_def lt_def)
  show "MK.N1" unfolding MK.N1_def using g by blast
  thus "MK.N2" unfolding MK.N2_def
    by (intro conjI exI[of _ "(True, (0, 0)) :: pt"] exI[of _ "(True, (0, 1)) :: pt"]
          exI[of _ "(True, (0, 2)) :: pt"]) simp_all
  show "MK.N5_chain" unfolding MK.N5_chain_def
    by (intro exI[of _ "(True, (0, 0)) :: pt"] exI[of _ "(True, (0, 1)) :: pt"]
          exI[of _ "(True, (0, 2)) :: pt"] exI[of _ "(True, (0, 3)) :: pt"])
       (simp add: MK_PG lt_def)
  have n: "ngT (ngT (True, (0, 0))) = (True, (0, 2))" by (simp add: ngT_def)
  have m1: "GK {(True, (0, 0))} (True, (0, 2))" by (simp add: GK_def lt_def)
  have m2: "\<not> GK {(True, (0, 0))} (True, (0, 0))" by (simp add: GK_def lt_def)
  have "{\<Gamma>. GK \<Gamma> (True, (0, 0))} \<noteq> {\<Gamma>. GK \<Gamma> (True, (0, 2))}" using m1 m2 by blast
  thus "MK.N4_pair (True, (0, 0)) (ngT (ngT (True, (0, 0))))"
    unfolding MK.N4_pair_def n by simp
qed

lemma MK_N4s: "MK.N4_pairs" using MK.N4_dn[OF MK_N4] .

lemma MK_BETA_ID: "MK.BETA_ID" by (simp add: MK.BETA_ID_def MK_den app_lamK)

lemma MK_classical: "MK.CL_PROP'" "MK.CL_QUANT'"
proof -
  show "MK.CL_PROP'" by (simp add: MK.CL_PROP'_def ngT_def cjT_def djT_def)
  show "MK.CL_QUANT'" by (simp add: MK.CL_QUANT'_def exqK_def allqK_def bigK_def MK.sat_def)
qed

lemma MK_truth: "MK.TS_TYPED" "MK.TS_T3_K" "MK.TR_TYPED"
proof -
  show "MK.TS_TYPED" unfolding MK.TS_TYPED_def MK_den
  proof (intro allI impI)
    fix a v assume A: "tfree a \<and> fv a = {}"
    have "fst (snd (dK v a)) = 0" by (rule tfree_lowK) (use A in auto)
    thus "fst (trK (dK v a)) \<longleftrightarrow> fst (dK v a)" by (simp add: trK_def)
  qed
  show "MK.TS_T3_K" unfolding MK.TS_T3_K_def MK_den
  proof (intro allI impI)
    fix a v assume A: "\<not> tfree a \<and> fv a = {}"
    have "0 < fst (snd (dK v a))" using ntfree_highK A by blast
    thus "\<not> fst (trK (dK v a))" by (simp add: trK_def)
  qed
  show "MK.TR_TYPED" unfolding MK.TR_TYPED_def MK_den
  proof (intro allI impI)
    fix a v assume A: "tfree a \<and> fv a = {} \<and> fst (dK v a)"
    have low: "fst (snd (dK v a)) = 0" by (rule tfree_lowK) (use A in auto)
    show "GK {dK v a} (trK (dK v a))" using A low by (simp add: GK_def trK_def lt_def)
  qed
qed

lemma MK_order: "MK.IRR_F" "MK.ASYM_P" "MK.TRANS_P"
proof -
  show "MK.IRR_F" by (auto simp: MK.IRR_F_def GK_def lt_def)
  show "MK.ASYM_P" by (auto simp: MK.ASYM_P_def MK_PG lt_def)
  show "MK.TRANS_P" unfolding MK.TRANS_P_def MK_PG using lt_trans by blast
qed

lemma MK_conn: "MK.DISJ_ONE" "MK.NEG_DN_K" "MK.CONJ_BIN_K"
proof -
  show "MK.DISJ_ONE" by (auto simp: MK.DISJ_ONE_def GK_def djT_def lt_up)
  show "MK.NEG_DN_K" by (auto simp: MK.NEG_DN_K_def GK_def ngT_def lt_def)
  show "MK.CONJ_BIN_K" by (auto simp: MK.CONJ_BIN_K_def GK_def cjT_def lt_up)
qed

lemma admK_total_tem:
  assumes "admK f" "\<forall>a. fst (appK f a)" shows "f = lamT 0 temB e0T"
proof -
  have f0: "fst (appK f (False, (0, 0)))" using assms(2) by blast
  have d: "f = lamT 0 (Tr (Var 0)) e0T \<or> f = lamT 0 temB e0T"
    using assms(1) unfolding admK_def by blast
  show ?thesis using d
  proof (elim disjE)
    assume "f = lamT 0 (Tr (Var 0)) e0T" with f0 show ?thesis by (simp add: wit_appK trK_def)
  next
    assume "f = lamT 0 temB e0T" thus ?thesis .
  qed
qed

lemma MK_quant: "MK.EX_FULL" "MK.ALL_INST"
proof -
  show "MK.EX_FULL" unfolding MK.EX_FULL_def
  proof (intro allI impI)
    fix f a assume A: "admK f \<and> fst (appK f a)"
    have d: "f = lamT 0 (Tr (Var 0)) e0T \<or> f = lamT 0 temB e0T"
      using A unfolding admK_def by blast
    show "GK {appK f a} (exqK f)" using d
    proof (elim disjE)
      assume e: "f = lamT 0 (Tr (Var 0)) e0T"
      have "fst (trK a)" using A unfolding e wit_appK by simp
      thus ?thesis unfolding e quant_valK wit_appK by (simp add: GK_def trK_def lt_def)
    next
      assume e: "f = lamT 0 temB e0T"
      show ?thesis unfolding e quant_valK wit_appK by (simp add: GK_def lt_def)
    qed
  qed
  show "MK.ALL_INST" unfolding MK.ALL_INST_def
  proof (intro allI impI)
    fix f assume A: "admK f \<and> (\<forall>a. fst (appK f a))"
    have e: "f = lamT 0 temB e0T" using admK_total_tem A by blast
    have i: "MK.inst f = {(True, (1, 2))}" unfolding MK.inst_def e by (auto simp: wit_appK)
    show "GK (MK.inst f) (allqK f)" unfolding i unfolding e quant_valK by (simp add: GK_def lt_def)
  qed
qed

text \<open>The circles that MK escapes, and what it costs. E, "something is true", is true,
  and its truth ascription is untrue, so it is no true instance of E and grounds nothing.
  The universal closure s of f_tem is true and its truth ascription is untrue. The
  negation of that ascription is true and helps ground s, through the instance
  tr s \<or> \<not> tr s.\<close>
lemma MK_blocks:
  "fst (exqK MK.f_tr)" "\<not> fst (trK (exqK MK.f_tr))"
  "\<not> MK.PG (trK (exqK MK.f_tr)) (exqK MK.f_tr)"
  "fst (allqK MK.f_tem)" "\<not> fst (trK (allqK MK.f_tem))"
  by (simp_all add: MK_wit quant_valK trK_def MK_PG)

lemma MK_neg_tr_grounds:
  "MK.PG (ngT (trK (allqK MK.f_tem))) (djT (trK (allqK MK.f_tem)) (ngT (trK (allqK MK.f_tem))))"
  "MK.PG (djT (trK (allqK MK.f_tem)) (ngT (trK (allqK MK.f_tem)))) (allqK MK.f_tem)"
  "MK.PG (ngT (trK (allqK MK.f_tem))) (allqK MK.f_tem)"
  by (simp_all add: MK_wit quant_valK trK_def ngT_def djT_def up_def MK_PG lt_def)

text \<open>MK satisfies the Aristotelian principle in the sources' form, for every
  proposition: a true truth ascription is true of a true lower-tier proposition, which
  lies below it. So the truth targets with TR.PART in that form and without TS.FULL are
  modelled (finding F20), and Korbmacher's solution keeps his APT at level 1 unrestricted.\<close>
lemma MK_TR_A: "MK.TR_FULL_A" "MK.TR_PART_A"
proof -
  show "MK.TR_FULL_A"
    by (auto simp: MK.TR_FULL_A_def trK_def GK_def lt_def)
  thus "MK.TR_PART_A" by (rule MK.TR_FULL_A_PART_A)
qed

lemma MK_fails: "\<not> MK.TS_FULL'" "\<not> MK.TR_PART"
proof -
  show "\<not> MK.TS_FULL'"
  proof
    assume "MK.TS_FULL'"
    hence "fst (trK (True, (1, 0))) \<longleftrightarrow> fst ((True, (1, 0)) :: pt)"
      unfolding MK.TS_FULL'_def by blast
    thus False by (simp add: trK_def)
  qed
  show "\<not> MK.TR_PART"
  proof
    assume A: "MK.TR_PART"
    have t: "fst ((True, (1, 0)) :: pt)" by simp
    have "MK.PG (True, (1, 0)) (trK (True, (1, 0)))"
      using A t unfolding MK.TR_PART_def by blast
    thus False by (simp add: MK_PG trK_def)
  qed
qed

text \<open>N3 instances, one for each introduction entry of the package, with distinct relata.\<close>
lemma MK_N3:
  "GK {appK MK.f_tr (True, (0, 0))} (exqK MK.f_tr) \<and> fst (appK MK.f_tr (True, (0, 0)))
   \<and> appK MK.f_tr (True, (0, 0)) \<noteq> exqK MK.f_tr
   \<and> GK (MK.inst MK.f_tem) (allqK MK.f_tem) \<and> MK.inst MK.f_tem = {(True, (1, 2))}
   \<and> GK {(True, (0, 0))} (djT (True, (0, 0)) (True, (0, 1)))
   \<and> distinct [(True, (0, 0)), (True, (0, 1)), djT (True, (0, 0)) (True, (0, 1))]
   \<and> GK {(True, (0, 0))} (ngT (ngT (True, (0, 0)))) \<and> ngT (ngT (True, (0, 0))) \<noteq> (True, (0, 0))
   \<and> GK {(True, (0, 0)), (True, (0, 1))} (cjT (True, (0, 0)) (True, (0, 1)))
   \<and> distinct [(True, (0, 0)), (True, (0, 1)), cjT (True, (0, 0)) (True, (0, 1))]
   \<and> GK {dK e0T (Cst 0)} (trK (dK e0T (Cst 0))) \<and> dK e0T (Cst 0) \<noteq> trK (dK e0T (Cst 0))"
proof -
  have i: "MK.inst MK.f_tem = {(True, (1, 2))}"
    unfolding MK.inst_def by (auto simp: MK_wit wit_appK)
  show ?thesis using i
    by (simp add: MK_wit wit_appK quant_valK GK_def trK_def lt_def djT_def cjT_def ngT_def up_def)
qed

text \<open>Finding F20, caveat. The three truth targets with the Aristotelian principle in
  the sources' form (TR.PART.A for TR.PART) and without TS.FULL hold together in MK: the
  entries of P.FINE.PARTICULAR, P.FINE.UNIVERSAL and P.FINE.PARTICULAR.PROPS, so read.\<close>
theorem MK_truth_targets_source_form:
  "MK.W_TR \<and> MK.W_TEM \<and> MK.BETA_ID \<and> MK.CL_PROP' \<and> MK.CL_QUANT'
   \<and> MK.TR_PART_A \<and> MK.EX_PART \<and> MK.ALL_PART \<and> MK.DISJ_PART
   \<and> MK.TRANS_P \<and> MK.IRR_F \<and> MK.ASYM_P \<and> \<not> MK.TS_FULL'"
  using MK_W MK_BETA_ID MK_classical MK_TR_A(2) MK.EX_FULL_PART_K[OF MK_quant(1)]
    MK.ALL_INST_PART_K[OF MK_quant(2)] MK.DISJ_ONE_PART_K[OF MK_conn(1)] MK_order MK_fails(1)
  by blast

theorem MK_package:
  "MK.FACT \<and> MK.LAM_CORE \<and> MK.W_TR \<and> MK.W_TEM \<and> MK.BETA_ID \<and> MK.CL_PROP' \<and> MK.CL_QUANT'
   \<and> MK.TS_TYPED \<and> MK.TS_T3_K \<and> MK.TR_TYPED \<and> MK.EX_FULL \<and> MK.ALL_INST
   \<and> MK.DISJ_ONE \<and> MK.NEG_DN_K \<and> MK.CONJ_BIN_K
   \<and> MK.TRANS_P \<and> MK.IRR_F \<and> MK.ASYM_P \<and> MK.N1 \<and> MK.N2 \<and> MK.N4_pairs \<and> MK.N5_chain
   \<and> \<not> MK.TS_FULL' \<and> \<not> MK.TR_PART \<and> \<not> MK.W_ID \<and> \<not> MK.W_EM"
  using MK_core MK_W MK_BETA_ID MK_classical MK_truth MK_quant MK_conn MK_order MK_N4s
    MK_fails
  by blast

end
