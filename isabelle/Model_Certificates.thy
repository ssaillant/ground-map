theory Model_Certificates
  imports Principles
begin

text \<open>
  Model certificates built in Isabelle, for the registry entries that the search left
  unknown when tested alone (first issued for registry 0.2.1-draft): C1, C2, C3d, BETA.ID, BETA.GROUND,
  EX.PRED, EX.LEV, TS.TYPED, TR.TYPED, FIN.B3, IMM.FRITZ7, and IRR.W (never queried alone).
  Nitpick cannot certify these: all but FIN.B3 and IMM.FRITZ7 quantify over the infinite
  datatype fm, so its models are only "potentially spurious", and IMM.FRITZ7 has no
  finite model at all (theorem imm_fritz7_no_finite_model below).

  Method. The signature of Signature.thy and Principles.thy is fixed by consts over the
  type declaration prp, so a model cannot be given by instantiating them. The locale gsig
  restates the signature with every constant as a parameter, over arbitrary types 'p
  (propositions) and 'f (propositional functions), and copies each definition needed
  here verbatim. The interpretation K at the actual constants, and the lemmas K_* below,
  prove that each copied definition is identical to the registry's. A model is then an
  interpretation of gsig at concrete types for which the package is proved; this is a
  model of the package in the standard semantics of HOL. The datatype fm stays the
  real, infinite datatype, so the formula layer is handled by proof, not by search.
  No axioms and no unfinished proofs.
\<close>

section \<open>The signature with its constants as parameters\<close>

locale gsig =
  fixes T :: "'p \<Rightarrow> bool"
    and atom :: "nat \<Rightarrow> 'p"
    and neg :: "'p \<Rightarrow> 'p"
    and conj :: "'p \<Rightarrow> 'p \<Rightarrow> 'p"
    and disj :: "'p \<Rightarrow> 'p \<Rightarrow> 'p"
    and tr :: "'p \<Rightarrow> 'p"
    and app :: "'f \<Rightarrow> 'p \<Rightarrow> 'p"
    and exq :: "'f \<Rightarrow> 'p"
    and allq :: "'f \<Rightarrow> 'p"
    and bigconj :: "'f \<Rightarrow> 'p"
    and lam :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> 'p) \<Rightarrow> 'f"
    and adm :: "'f \<Rightarrow> bool"
    and G :: "'p set \<Rightarrow> 'p \<Rightarrow> bool"
    and e0 :: "nat \<Rightarrow> 'p"
    and tt :: "'p"
begin

primrec den :: "(nat \<Rightarrow> 'p) \<Rightarrow> fm \<Rightarrow> 'p" where
  "den v (Var n) = v n"
| "den v (Cst n) = atom n"
| "den v (Neg a) = neg (den v a)"
| "den v (Conj a b) = conj (den v a) (den v b)"
| "den v (Disj a b) = disj (den v a) (den v b)"
| "den v (Tr a) = tr (den v a)"
| "den v (Ex x a) = exq (lam x a v)"
| "den v (All x a) = allq (lam x a v)"
| "den v (BigC x a) = bigconj (lam x a v)"

definition inst :: "'f \<Rightarrow> 'p set" where "inst f = range (app f)"
definition sat  :: "'f \<Rightarrow> 'p set" where "sat f = {p. T (app f p)}"
definition PG :: "'p \<Rightarrow> 'p \<Rightarrow> bool" where "PG p q \<longleftrightarrow> (\<exists>\<Gamma>. p \<in> \<Gamma> \<and> G \<Gamma> q)"
definition IG :: "'p set \<Rightarrow> 'p \<Rightarrow> bool" where
  "IG \<Gamma> q \<longleftrightarrow> G \<Gamma> q \<and> (\<forall>\<Delta>. G \<Delta> q \<longrightarrow> (\<forall>p\<in>\<Gamma> - \<Delta>. \<exists>\<Delta>'\<subseteq>\<Delta>. G \<Delta>' p))"
definition IPG :: "'p \<Rightarrow> 'p \<Rightarrow> bool" where "IPG p q \<longleftrightarrow> (\<exists>\<Gamma>. p \<in> \<Gamma> \<and> IG \<Gamma> q)"

definition vacW :: "'p \<Rightarrow> 'p set \<Rightarrow> 'p \<Rightarrow> bool" where
  "vacW A \<Gamma> c \<longleftrightarrow> (\<exists>\<Phi> v z.
      \<Gamma> = (\<lambda>\<phi>. den (v(z:=A)) \<phi>) ` \<Phi>
    \<and> (\<exists>\<phi>\<in>\<Phi>. z \<in> fv \<phi>)
    \<and> (\<forall>\<phi>\<in>\<Phi>. \<forall>\<psi>\<in>subf \<phi>. z \<notin> fv \<psi> \<longrightarrow> den (v(z:=A)) \<psi> \<noteq> A)
    \<and> (\<forall>B. (\<forall>\<phi>\<in>\<Phi>. T (den (v(z:=B)) \<phi>)) \<longrightarrow> G ((\<lambda>\<phi>. den (v(z:=B)) \<phi>) ` \<Phi>) c))"

definition LAM_CORE :: bool where
  "LAM_CORE \<longleftrightarrow>
     (\<forall>x a v p. T (app (lam x a v) p) \<longleftrightarrow> T (den (v(x:=p)) a))
   \<and> (\<forall>x a v w. (\<forall>y\<in>fv a - {x}. v y = w y) \<longrightarrow> lam x a v = lam x a w)"

definition f_id :: 'f where "f_id  = lam 0 (Var 0) e0"
definition f_tr :: 'f where "f_tr  = lam 0 (Tr (Var 0)) e0"
definition f_em :: 'f where "f_em  = lam 0 (Disj (Var 0) (Neg (Var 0))) e0"
definition f_tem :: 'f where "f_tem = lam 0 (Disj (Tr (Var 0)) (Neg (Tr (Var 0)))) e0"

definition C1 :: bool where "C1 \<longleftrightarrow> (\<forall>f. adm f \<longleftrightarrow> f \<in> {f_id, f_tr, f_em, f_tem})"
definition C2 :: "nat \<Rightarrow> bool" where
  "C2 k \<longleftrightarrow> (\<forall>f. adm f \<longleftrightarrow> (\<exists>x a v. lvl a \<le> k \<and> f = lam x a v))"
definition C3d :: bool where "C3d \<longleftrightarrow> (\<forall>f. adm f \<longleftrightarrow> (\<exists>x a v. f = lam x a v))"

definition BETA_ID :: bool where
  "BETA_ID \<longleftrightarrow> (\<forall>x a v p. app (lam x a v) p = den (v(x:=p)) a)"
definition BETA_GROUND :: bool where
  "BETA_GROUND \<longleftrightarrow> (\<forall>x a v p. T (den (v(x:=p)) a) \<longrightarrow>
      app (lam x a v) p \<noteq> den (v(x:=p)) a \<and> G {den (v(x:=p)) a} (app (lam x a v) p))"

definition FACT :: bool where
  "FACT \<longleftrightarrow> (\<forall>\<Gamma> p. G \<Gamma> p \<longrightarrow> T p \<and> (\<forall>q\<in>\<Gamma>. T q))"
definition IRR_W :: bool where
  "IRR_W \<longleftrightarrow> (\<forall>\<Gamma> c. G \<Gamma> c \<and> c \<in> \<Gamma> \<longrightarrow> vacW c \<Gamma> c)"
definition IRR_F :: bool where
  "IRR_F \<longleftrightarrow> (\<forall>\<Gamma> c. G \<Gamma> c \<longrightarrow> c \<notin> \<Gamma>)"
definition TS_TYPED :: bool where
  "TS_TYPED \<longleftrightarrow> (\<forall>a v. tfree a \<and> fv a = {} \<longrightarrow> (T (tr (den v a)) \<longleftrightarrow> T (den v a)))"
definition TR_TYPED :: bool where
  "TR_TYPED \<longleftrightarrow> (\<forall>a v. tfree a \<and> fv a = {} \<and> T (den v a) \<longrightarrow> G {den v a} (tr (den v a)))"
definition EX_PRED :: bool where
  "EX_PRED \<longleftrightarrow> (\<forall>f a w. adm f \<and> lvl a = 0 \<and> fv a = {} \<and> T (app f (den w a))
     \<longrightarrow> G {app f (den w a)} (exq f))"
definition EX_LEV :: bool where
  "EX_LEV \<longleftrightarrow> (\<forall>x b v a w. adm (lam x b v) \<and> lvl a < lvl (Ex x b) \<and> fv a = {}
     \<and> T (app (lam x b v) (den w a))
     \<longrightarrow> G {app (lam x b v) (den w a)} (exq (lam x b v)))"
definition EX_FULL :: bool where
  "EX_FULL \<longleftrightarrow> (\<forall>f a. adm f \<and> T (app f a) \<longrightarrow> G {app f a} (exq f))"
definition FIN_B3 :: bool where "FIN_B3 \<longleftrightarrow> (\<forall>\<Gamma> p. G \<Gamma> p \<longrightarrow> finite \<Gamma> \<and> card \<Gamma> \<le> 3)"
definition IMM_FRITZ7 :: bool where
  "IMM_FRITZ7 \<longleftrightarrow>
     (\<forall>p q. T p \<and> T q \<longrightarrow> IPG p (conj p q) \<and> IPG q (conj p q))
   \<and> (\<forall>r p q. IPG r (conj p q) \<longrightarrow> r = p \<or> r = q)
   \<and> (\<forall>p q. T (disj p q) \<longrightarrow> IPG p (disj p q) \<or> IPG q (disj p q))
   \<and> (\<forall>r p q. IPG r (disj p q) \<longrightarrow> r = p \<or> r = q)
   \<and> (\<forall>g x. adm g \<and> T (allq g) \<longrightarrow> IPG (app g x) (allq g))
   \<and> (\<forall>g q. adm g \<and> IPG q (allq g) \<and> (\<forall>x. q \<noteq> app g x) \<longrightarrow> q = tt)
   \<and> \<not> (\<forall>p q. T p \<and> T q \<longrightarrow> IPG p q)"

definition N1 :: bool where "N1 \<longleftrightarrow> (\<exists>\<Gamma> p. G \<Gamma> p)"
definition N2 :: bool where
  "N2 \<longleftrightarrow> N1 \<and> (\<exists>a b c. distinct [a, b, c] \<and> T a \<and> T b \<and> T c)"
definition N5_chain :: bool where
  "N5_chain \<longleftrightarrow> (\<exists>x0 x1 x2 x3. distinct [x0, x1, x2, x3] \<and> PG x0 x1 \<and> PG x1 x2 \<and> PG x2 x3)"

text \<open>N4 (registry, nontriviality): some pair of classically equivalent propositions
  from the listed shapes is distinct and has different sets of full grounds. Stated with
  the witness pair as an argument; each model below names its pair.\<close>
definition N4_pair :: "'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "N4_pair x y \<longleftrightarrow> x \<noteq> y \<and> {\<Gamma>. G \<Gamma> x} \<noteq> {\<Gamma>. G \<Gamma> y}"
definition N4_pairs :: bool where
  "N4_pairs \<longleftrightarrow> (\<exists>x y. ((\<exists>p. x = p \<and> y = neg (neg p)) \<or> (\<exists>p q. x = conj p q \<and> y = conj q p)
       \<or> (\<exists>p. x = p \<and> y = conj p p) \<or> (\<exists>p q. x = disj p q \<and> y = disj q p))
     \<and> x \<noteq> y \<and> {\<Gamma>. G \<Gamma> x} \<noteq> {\<Gamma>. G \<Gamma> y})"

lemma N4_dn:
  assumes "N4_pair p (neg (neg p))" shows "N4_pairs"
proof -
  have "\<exists>p'. p = p' \<and> neg (neg p) = neg (neg p')" by blast
  hence sh: "(\<exists>p'. p = p' \<and> neg (neg p) = neg (neg p')) \<or> (\<exists>p' q. p = conj p' q \<and> neg (neg p) = conj q p')
       \<or> (\<exists>p'. p = p' \<and> neg (neg p) = conj p' p') \<or> (\<exists>p' q. p = disj p' q \<and> neg (neg p) = disj q p')"
    by (rule disjI1)
  show ?thesis unfolding N4_pairs_def
    by (rule exI[of _ p], rule exI[of _ "neg (neg p)"]) (use sh assms in \<open>simp add: N4_pair_def\<close>)
qed
lemma N4_cc:
  assumes "N4_pair p (conj p p)" shows "N4_pairs"
proof -
  have sh: "(\<exists>p'. p = p' \<and> conj p p = neg (neg p')) \<or> (\<exists>p' q. p = conj p' q \<and> conj p p = conj q p')
       \<or> (\<exists>p'. p = p' \<and> conj p p = conj p' p') \<or> (\<exists>p' q. p = disj p' q \<and> conj p p = disj q p')"
    by (rule disjI2, rule disjI2, rule disjI1, blast)
  show ?thesis unfolding N4_pairs_def
    by (rule exI[of _ p], rule exI[of _ "conj p p"]) (use sh assms in \<open>simp add: N4_pair_def\<close>)
qed

definition CL_PROP :: bool where
  "CL_PROP \<longleftrightarrow> (\<forall>p q. (T (neg p) \<longleftrightarrow> \<not> T p) \<and> (T (conj p q) \<longleftrightarrow> T p \<and> T q)
                     \<and> (T (disj p q) \<longleftrightarrow> T p \<or> T q))"
definition CL_QUANT :: bool where
  "CL_QUANT \<longleftrightarrow> (\<forall>f. (T (exq f) \<longleftrightarrow> (\<exists>a. T (app f a))) \<and> (T (allq f) \<longleftrightarrow> (\<forall>a. T (app f a)))
                     \<and> (T (bigconj f) \<longleftrightarrow> (\<forall>q\<in>sat f. T q)))"
definition TS_FULL :: bool where
  "TS_FULL \<longleftrightarrow> (\<forall>p. T (tr p) \<longleftrightarrow> T p)"

end

section \<open>Faithfulness: the locale at the actual constants is the registry\<close>

interpretation K: gsig T atom neg conj disj tr app exq allq bigconj lam adm G e0 tt .

lemma K_den: "K.den = den"
proof (intro ext)
  fix v a show "K.den v a = den v a" by (induction a) simp_all
qed

lemma K_aux:
  "K.inst = inst" "K.sat = sat" "K.PG = PG" "K.IG = IG" "K.IPG = IPG"
  by (intro ext; simp add: K.inst_def inst_def K.sat_def sat_def K.PG_def PG_def
        K.IG_def IG_def K.IPG_def IPG_def)+

lemma K_vacW: "K.vacW = vacW"
  by (intro ext) (simp add: K.vacW_def vacW_def K_den)

lemma K_faithful:
  "K.LAM_CORE = LAM_CORE" "K.C1 = C1" "K.C2 = C2" "K.C3d = C3d"
  "K.BETA_ID = BETA_ID" "K.BETA_GROUND = BETA_GROUND" "K.FACT = FACT"
  "K.IRR_W = IRR_W" "K.IRR_F = IRR_F" "K.TS_TYPED = TS_TYPED" "K.TR_TYPED = TR_TYPED"
  "K.EX_PRED = EX_PRED" "K.EX_LEV = EX_LEV" "K.EX_FULL = EX_FULL" "K.FIN_B3 = FIN_B3"
  "K.IMM_FRITZ7 = IMM_FRITZ7" "K.N1 = N1" "K.N2 = N2" "K.N5_chain = N5_chain"
  "K.N4_pairs = N4_pairs" "K.CL_PROP = CL_PROP" "K.CL_QUANT = CL_QUANT" "K.TS_FULL = TS_FULL"
  by (simp_all add: K_den K_aux K_vacW fun_eq_iff
        K.LAM_CORE_def LAM_CORE_def K.C1_def C1_def K.C2_def C2_def K.C3d_def C3d_def
        K.f_id_def f_id_def K.f_tr_def f_tr_def K.f_em_def f_em_def K.f_tem_def f_tem_def
        K.BETA_ID_def BETA_ID_def K.BETA_GROUND_def BETA_GROUND_def K.FACT_def FACT_def
        K.IRR_W_def IRR_W_def K.IRR_F_def IRR_F_def K.TS_TYPED_def TS_TYPED_def
        K.TR_TYPED_def TR_TYPED_def K.EX_PRED_def EX_PRED_def K.EX_LEV_def EX_LEV_def
        K.EX_FULL_def EX_FULL_def K.FIN_B3_def FIN_B3_def K.IMM_FRITZ7_def IMM_FRITZ7_def
        K.N1_def N1_def K.N2_def N2_def K.N5_chain_def N5_chain_def K.N4_pairs_def N4_pairs_def
        K.CL_PROP_def CL_PROP_def K.CL_QUANT_def CL_QUANT_def K.TS_FULL_def TS_FULL_def)

section \<open>Five propositions on a cycle\<close>

datatype pr5 = P0 | P1 | P2 | P3 | P4

fun nx :: "pr5 \<Rightarrow> pr5" where
  "nx P0 = P1" | "nx P1 = P2" | "nx P2 = P3" | "nx P3 = P4" | "nx P4 = P0"

lemma nx_neq: "nx p \<noteq> p" by (cases p) simp_all

text \<open>Base grounding relation: each proposition is the sole full ground of its successor.\<close>
definition GB :: "pr5 set \<Rightarrow> pr5 \<Rightarrow> bool" where
  "GB \<Gamma> q \<longleftrightarrow> (\<exists>p. \<Gamma> = {p} \<and> q = nx p)"

section \<open>Model B: C1, C2, C3d, TS.TYPED, TR.TYPED, FIN.B3, IRR.W\<close>

text \<open>Finite carriers: five propositions, all true; one propositional function (unit),
  so every lambda-term denotes it; negation and truth ascription are the successor map.\<close>

interpretation MB: gsig "\<lambda>_::pr5. True" "\<lambda>_. P0" nx "\<lambda>_ _. P0" "\<lambda>_ _. P0" nx
  "\<lambda>(_::unit) p. p" "\<lambda>_. P0" "\<lambda>_. P0" "\<lambda>_. P0" "\<lambda>_ _ _. ()" "\<lambda>_. True" GB "\<lambda>_. P0" P0 .

lemma MB_core: "MB.FACT" "MB.LAM_CORE" "MB.N1" "MB.N2" "MB.N5_chain"
  and MB_N4: "MB.N4_pair P1 (nx (nx P1))"
proof -
  have g: "GB {p} (nx p)" for p unfolding GB_def by blast
  show "MB.FACT" by (simp add: MB.FACT_def)
  show "MB.LAM_CORE" by (simp add: MB.LAM_CORE_def)
  show "MB.N1" unfolding MB.N1_def using g by blast
  thus "MB.N2" unfolding MB.N2_def by (intro conjI exI[of _ P0] exI[of _ P1] exI[of _ P2]) simp_all
  have "MB.PG P0 P1" "MB.PG P1 P2" "MB.PG P2 P3"
    unfolding MB.PG_def using g[of P0] g[of P1] g[of P2] by auto
  thus "MB.N5_chain" unfolding MB.N5_chain_def
    by (intro exI[of _ P0] exI[of _ P1] exI[of _ P2] exI[of _ P3]) simp
  have "GB {P0} P1" "\<not> GB {P0} P3" unfolding GB_def by auto
  thus "MB.N4_pair P1 (nx (nx P1))" unfolding MB.N4_pair_def by auto
qed

lemma MB_N4s: "MB.N4_pairs" using MB.N4_dn[OF MB_N4] .

lemma MB_C1: "MB.C1" by (simp add: MB.C1_def)
lemma MB_C2: "MB.C2 1" unfolding MB.C2_def by (auto intro!: exI[of _ "Var 0"])
lemma MB_C3d: "MB.C3d" unfolding MB.C3d_def by auto
lemma MB_TS_TYPED: "MB.TS_TYPED" by (simp add: MB.TS_TYPED_def)
lemma MB_TR_TYPED: "MB.TR_TYPED" by (simp add: MB.TR_TYPED_def GB_def)
lemma MB_FIN_B3: "MB.FIN_B3" by (auto simp: MB.FIN_B3_def GB_def)
lemma MB_IRR_F: "MB.IRR_F" using nx_neq by (auto simp: MB.IRR_F_def GB_def)
lemma MB_IRR_W: "MB.IRR_W" using nx_neq by (auto simp: MB.IRR_W_def GB_def)

text \<open>N3 instance for TR.TYPED (the only introduction entry among these): the closed
  formula Cst 0 is truth-free, its value P0 is true, the relata P0 and tr P0 = P1 are
  distinct, and the grounded proposition is not among its grounds. (Registry 0.3.0-draft:
  the presenting formula must be closed; the instance used Var 0 before.) TR.FULL also
  holds in this model, so it does not separate the two entries; Restricted_Models.thy does.\<close>
lemma MB_N3_TR_TYPED:
  "tfree (Cst 0) \<and> fv (Cst 0) = {} \<and> MB.den v (Cst 0) = P0 \<and> P0 \<noteq> nx P0
   \<and> GB {P0} (nx P0) \<and> nx P0 \<notin> {P0}"
  by (simp add: GB_def)

section \<open>Model A: EX.PRED, EX.LEV (indeed EX.FULL)\<close>

text \<open>As model B, but the one existential proposition, exq () = P0, is also fully
  grounded by each proposition alone.\<close>
definition GA :: "pr5 set \<Rightarrow> pr5 \<Rightarrow> bool" where
  "GA \<Gamma> q \<longleftrightarrow> (\<exists>p. \<Gamma> = {p} \<and> (q = nx p \<or> q = P0))"

interpretation MA: gsig "\<lambda>_::pr5. True" "\<lambda>_. P0" nx "\<lambda>_ _. P0" "\<lambda>_ _. P0" nx
  "\<lambda>(_::unit) p. p" "\<lambda>_. P0" "\<lambda>_. P0" "\<lambda>_. P0" "\<lambda>_ _ _. ()" "\<lambda>_. True" GA "\<lambda>_. P0" P0 .

lemma MA_core: "MA.FACT" "MA.LAM_CORE" "MA.N1" "MA.N2" "MA.N5_chain"
  and MA_N4: "MA.N4_pair P1 (nx (nx P1))"
proof -
  have g: "GA {p} (nx p)" for p unfolding GA_def by blast
  show "MA.FACT" by (simp add: MA.FACT_def)
  show "MA.LAM_CORE" by (simp add: MA.LAM_CORE_def)
  show "MA.N1" unfolding MA.N1_def using g by blast
  thus "MA.N2" unfolding MA.N2_def by (intro conjI exI[of _ P0] exI[of _ P1] exI[of _ P2]) simp_all
  have "MA.PG P0 P1" "MA.PG P1 P2" "MA.PG P2 P3"
    unfolding MA.PG_def using g[of P0] g[of P1] g[of P2] by auto
  thus "MA.N5_chain" unfolding MA.N5_chain_def
    by (intro exI[of _ P0] exI[of _ P1] exI[of _ P2] exI[of _ P3]) simp
  have "GA {P0} P1" "\<not> GA {P0} P3" unfolding GA_def by auto
  thus "MA.N4_pair P1 (nx (nx P1))" unfolding MA.N4_pair_def by auto
qed

lemma MA_N4s: "MA.N4_pairs" using MA.N4_dn[OF MA_N4] .

lemma MA_EX_FULL: "MA.EX_FULL" by (simp add: MA.EX_FULL_def GA_def)
lemma MA_EX_PRED: "MA.EX_PRED" by (simp add: MA.EX_PRED_def GA_def)
lemma MA_EX_LEV: "MA.EX_LEV" by (simp add: MA.EX_LEV_def GA_def)

text \<open>N3 instances: the closed level-0 formula Neg (Cst 0), whose value is P1; the
  relata P1 and exq () = P0 are distinct and P0 is not among the grounds {P1}. For EX.LEV
  the quantified formula is Ex 0 (Var 0), of level 1. (Registry 0.3.0-draft: the instance
  must be presented by a closed formula; it used Var 0 before.) EX.FULL also holds in
  this model, so it does not separate the entries; Restricted_Models.thy does.\<close>
lemma MA_N3_EX:
  "lvl (Neg (Cst 0)) = 0 \<and> fv (Neg (Cst 0)) = {} \<and> lvl (Neg (Cst 0)) < lvl (Ex 0 (Var 0))
   \<and> MA.den w (Neg (Cst 0)) = P1 \<and> P1 \<noteq> P0 \<and> GA {P1} P0 \<and> P0 \<notin> {P1}"
  by (simp add: GA_def)

section \<open>Models C and D: BETA.ID and BETA.GROUND\<close>

text \<open>Propositional functions are the functions pr5 => pr5 (finite carriers again);
  a lambda-term denotes the function its body computes.\<close>

primrec dC :: "(nat \<Rightarrow> pr5) \<Rightarrow> fm \<Rightarrow> pr5" where
  "dC v (Var n) = v n"
| "dC v (Cst n) = P0"
| "dC v (Neg a) = nx (dC v a)"
| "dC v (Conj a b) = P0"
| "dC v (Disj a b) = P0"
| "dC v (Tr a) = nx (dC v a)"
| "dC v (Ex x a) = P0"
| "dC v (All x a) = P0"
| "dC v (BigC x a) = P0"

lemma dC_fv: "\<forall>y\<in>fv a. v y = w y \<Longrightarrow> dC v a = dC w a"
  by (induction a) simp_all

definition lamC :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> pr5) \<Rightarrow> pr5 \<Rightarrow> pr5" where
  "lamC x a v = (\<lambda>p. dC (v(x:=p)) a)"

lemma lamC_fv: "\<forall>y\<in>fv a - {x}. v y = w y \<Longrightarrow> lamC x a v = lamC x a w"
  unfolding lamC_def by (intro ext dC_fv) auto

text \<open>Model C: application is function application, so BETA.ID holds.\<close>
interpretation MC: gsig "\<lambda>_::pr5. True" "\<lambda>_. P0" nx "\<lambda>_ _. P0" "\<lambda>_ _. P0" nx
  "\<lambda>(f::pr5 \<Rightarrow> pr5) p. f p" "\<lambda>_. P0" "\<lambda>_. P0" "\<lambda>_. P0" lamC "\<lambda>_. True" GB "\<lambda>_. P0" P0 .

lemma MC_den: "MC.den = dC"
proof (intro ext)
  fix v a show "MC.den v a = dC v a" by (induction a) simp_all
qed

lemma MC_core: "MC.FACT" "MC.LAM_CORE" "MC.N1" "MC.N2" "MC.N5_chain"
  and MC_N4: "MC.N4_pair P1 (nx (nx P1))"
proof -
  have g: "GB {p} (nx p)" for p unfolding GB_def by blast
  show "MC.FACT" by (simp add: MC.FACT_def)
  show "MC.LAM_CORE" unfolding MC.LAM_CORE_def using lamC_fv by blast
  show "MC.N1" unfolding MC.N1_def using g by blast
  thus "MC.N2" unfolding MC.N2_def by (intro conjI exI[of _ P0] exI[of _ P1] exI[of _ P2]) simp_all
  have "MC.PG P0 P1" "MC.PG P1 P2" "MC.PG P2 P3"
    unfolding MC.PG_def using g[of P0] g[of P1] g[of P2] by auto
  thus "MC.N5_chain" unfolding MC.N5_chain_def
    by (intro exI[of _ P0] exI[of _ P1] exI[of _ P2] exI[of _ P3]) simp
  have "GB {P0} P1" "\<not> GB {P0} P3" unfolding GB_def by auto
  thus "MC.N4_pair P1 (nx (nx P1))" unfolding MC.N4_pair_def by auto
qed

lemma MC_N4s: "MC.N4_pairs" using MC.N4_dn[OF MC_N4] .

lemma MC_BETA_ID: "MC.BETA_ID" by (simp add: MC.BETA_ID_def MC_den lamC_def)

text \<open>Model D: applying a function adds one step, app f p = nx (f p); the redex is then
  distinct from the reduct and grounded by it, so BETA.GROUND holds.\<close>
interpretation MD: gsig "\<lambda>_::pr5. True" "\<lambda>_. P0" nx "\<lambda>_ _. P0" "\<lambda>_ _. P0" nx
  "\<lambda>(f::pr5 \<Rightarrow> pr5) p. nx (f p)" "\<lambda>_. P0" "\<lambda>_. P0" "\<lambda>_. P0" lamC "\<lambda>_. True" GB "\<lambda>_. P0" P0 .

lemma MD_den: "MD.den = dC"
proof (intro ext)
  fix v a show "MD.den v a = dC v a" by (induction a) simp_all
qed

lemma MD_core: "MD.FACT" "MD.LAM_CORE" "MD.N1" "MD.N2" "MD.N5_chain"
  and MD_N4: "MD.N4_pair P1 (nx (nx P1))"
proof -
  have g: "GB {p} (nx p)" for p unfolding GB_def by blast
  show "MD.FACT" by (simp add: MD.FACT_def)
  show "MD.LAM_CORE" unfolding MD.LAM_CORE_def using lamC_fv by blast
  show "MD.N1" unfolding MD.N1_def using g by blast
  thus "MD.N2" unfolding MD.N2_def by (intro conjI exI[of _ P0] exI[of _ P1] exI[of _ P2]) simp_all
  have "MD.PG P0 P1" "MD.PG P1 P2" "MD.PG P2 P3"
    unfolding MD.PG_def using g[of P0] g[of P1] g[of P2] by auto
  thus "MD.N5_chain" unfolding MD.N5_chain_def
    by (intro exI[of _ P0] exI[of _ P1] exI[of _ P2] exI[of _ P3]) simp
  have "GB {P0} P1" "\<not> GB {P0} P3" unfolding GB_def by auto
  thus "MD.N4_pair P1 (nx (nx P1))" unfolding MD.N4_pair_def by auto
qed

lemma MD_N4s: "MD.N4_pairs" using MD.N4_dn[OF MD_N4] .

lemma MD_BETA_GROUND: "MD.BETA_GROUND"
  using nx_neq by (simp add: MD.BETA_GROUND_def MD_den lamC_def GB_def)

section \<open>IMM.FRITZ7: no finite model, and an infinite model\<close>

text \<open>Only (\<and>1), (\<and>2) and (nt) are used. By (\<and>1) and (\<and>2) the immediate partial
  grounds of conj p q are exactly p and q whenever both are true, so conj maps the
  one- and two-element sets of truths injectively into the truths; (nt) rules out a
  single truth. Neither N1 nor LAM_CORE is assumed.\<close>

theorem imm_fritz7_no_finite_model:
  assumes "FACT" "IMM_FRITZ7"
  shows "infinite {p. T p}"
proof
  assume fin: "finite {p. T p}"
  define S where "S = {p. T p}"
  have finS: "finite S" using fin unfolding S_def .
  have A1: "\<And>p q. T p \<Longrightarrow> T q \<Longrightarrow> IPG p (conj p q) \<and> IPG q (conj p q)"
    using assms(2) unfolding IMM_FRITZ7_def by blast
  have A2: "\<And>r p q. IPG r (conj p q) \<Longrightarrow> r = p \<or> r = q"
    using assms(2) unfolding IMM_FRITZ7_def by blast
  have NT: "\<exists>a b. T a \<and> T b \<and> \<not> IPG a b"
    using assms(2) unfolding IMM_FRITZ7_def by blast
  have IPG_T: "\<And>p q. IPG p q \<Longrightarrow> T q"
    using assms(1) unfolding IPG_def IG_def FACT_def by blast
  have cT: "\<And>p q. T p \<Longrightarrow> T q \<Longrightarrow> T (conj p q)" using A1 IPG_T by blast
  define \<sigma> where "\<sigma> r = {s. IPG s r}" for r
  have sig: "\<And>p q. T p \<Longrightarrow> T q \<Longrightarrow> \<sigma> (conj p q) = {p, q}"
    unfolding \<sigma>_def using A1 A2 by blast
  define P where "P = {X. \<exists>p\<in>S. \<exists>q\<in>S. X = {p, q}}"
  have PS: "P \<subseteq> \<sigma> ` S"
  proof
    fix X assume "X \<in> P"
    then obtain p q where pq: "p \<in> S" "q \<in> S" "X = {p, q}" unfolding P_def by blast
    hence "X = \<sigma> (conj p q)" "conj p q \<in> S" using sig cT unfolding S_def by auto
    thus "X \<in> \<sigma> ` S" by blast
  qed
  have finP: "finite P" using finite_subset[OF PS finite_imageI[OF finS]] .
  have le1: "card P \<le> card (\<sigma> ` S)" by (rule card_mono[OF finite_imageI[OF finS] PS])
  have le2: "card (\<sigma> ` S) \<le> card S" by (rule card_image_le[OF finS])
  obtain a b where ab: "T a" "T b" "\<not> IPG a b" using NT by blast
  obtain c where c: "T c" "c \<noteq> a"
  proof (cases "\<exists>c. T c \<and> c \<noteq> a")
    case True thus ?thesis using that by blast
  next
    case False
    hence all: "\<And>c. T c \<Longrightarrow> c = a" by blast
    have "b = a" using all ab(2) .
    moreover have "conj a a = a" using all cT[OF ab(1) ab(1)] .
    ultimately have "IPG a b" using A1[OF ab(1) ab(1)] by simp
    thus ?thesis using ab(3) by contradiction
  qed
  define U where "U = (\<lambda>p. {p}) ` S"
  have UP: "U \<subseteq> P"
  proof
    fix X assume "X \<in> U"
    then obtain p where p: "p \<in> S" "X = {p, p}" unfolding U_def by auto
    thus "X \<in> P" unfolding P_def by blast
  qed
  have acP: "{a, c} \<in> P" unfolding P_def S_def using ab(1) c(1) by blast
  have notin: "{a, c} \<notin> U"
  proof
    assume "{a, c} \<in> U"
    then obtain p where "{a, c} = {p}" unfolding U_def by blast
    hence "a = c" by (metis insertI1 insert_commute singletonD)
    thus False using c(2) by simp
  qed
  have cardU: "card U = card S" unfolding U_def by (rule card_image) (simp add: inj_on_def)
  have "card (insert {a, c} U) = Suc (card U)"
    by (rule card_insert_disjoint[OF _ notin]) (simp add: U_def finS)
  moreover have "card (insert {a, c} U) \<le> card P"
    by (rule card_mono[OF finP]) (simp add: UP acP)
  ultimately show False using le1 le2 cardU by linarith
qed

corollary imm_fritz7_prp_infinite:
  assumes "FACT" "IMM_FRITZ7" shows "infinite (UNIV :: prp set)"
  using infinite_super[OF subset_UNIV imm_fritz7_no_finite_model[OF assms]] .

text \<open>The infinite model: a term algebra. Atoms and conjunctions of truths are true;
  disjunctions, negations, truth ascriptions and quantified propositions are false, so
  the clauses (\<or>1) and (\<forall>1) hold vacuously. A conjunction of truths is fully grounded
  by its two conjuncts, and nothing else grounds anything. Truth is therefore not
  classical in this model (negation and disjunction are not truth-functional); the model
  certifies IMM.FRITZ7 alone, not with CL.PROP.\<close>

datatype tm = At nat | Cj tm tm | Dj tm tm | Ng tm | Tc tm | Qu nat

primrec TE :: "tm \<Rightarrow> bool" where
  "TE (At n) = True" | "TE (Cj a b) = (TE a \<and> TE b)" | "TE (Dj a b) = False"
| "TE (Ng a) = False" | "TE (Tc a) = False" | "TE (Qu n) = False"

definition GE :: "tm set \<Rightarrow> tm \<Rightarrow> bool" where
  "GE \<Gamma> q \<longleftrightarrow> (\<exists>a b. q = Cj a b \<and> TE a \<and> TE b \<and> \<Gamma> = {a, b})"

interpretation ME: gsig TE At Ng Cj Dj Tc "\<lambda>(_::unit) p. p" "\<lambda>_. Qu 0" "\<lambda>_. Qu 1" "\<lambda>_. Qu 2"
  "\<lambda>_ _ _. ()" "\<lambda>_. True" GE "\<lambda>_. At 0" "At 0" .

lemma GE_unique: "GE \<Gamma> q \<Longrightarrow> GE \<Delta> q \<Longrightarrow> \<Delta> = \<Gamma>"
  unfolding GE_def by fastforce

lemma ME_IG: "ME.IG \<Gamma> q \<longleftrightarrow> GE \<Gamma> q"
proof
  assume "ME.IG \<Gamma> q" thus "GE \<Gamma> q" by (simp add: ME.IG_def)
next
  assume g: "GE \<Gamma> q"
  have H: "\<forall>\<Delta>. GE \<Delta> q \<longrightarrow> (\<forall>p\<in>\<Gamma> - \<Delta>. \<exists>\<Delta>'\<subseteq>\<Delta>. GE \<Delta>' p)"
  proof (intro allI impI ballI)
    fix \<Delta> p assume d: "GE \<Delta> q" and p: "p \<in> \<Gamma> - \<Delta>"
    have "\<Delta> = \<Gamma>" using GE_unique[OF g d] .
    thus "\<exists>\<Delta>'\<subseteq>\<Delta>. GE \<Delta>' p" using p by simp
  qed
  show "ME.IG \<Gamma> q" unfolding ME.IG_def using g H by (rule conjI)
qed

lemma ME_IPG: "ME.IPG r q \<longleftrightarrow> (\<exists>a b. q = Cj a b \<and> TE a \<and> TE b \<and> (r = a \<or> r = b))"
  unfolding ME.IPG_def ME_IG GE_def by auto

lemma ME_IMM_FRITZ7: "ME.IMM_FRITZ7"
proof -
  have "\<not> ME.IPG (At 0) (At 1)" by (simp add: ME_IPG)
  hence nt: "\<not> (\<forall>p q. TE p \<and> TE q \<longrightarrow> ME.IPG p q)" by force
  show ?thesis unfolding ME.IMM_FRITZ7_def using nt by (auto simp: ME_IPG)
qed

text \<open>N3 instance, if (\<and>1) is counted as an introduction entry (the registry's N3 list
  names CONJ, not IMM): distinct relata, and the conjunction is not among its grounds.\<close>
lemma ME_N3_conj:
  "TE (At 0) \<and> TE (At 1) \<and> ME.IPG (At 0) (Cj (At 0) (At 1)) \<and> ME.IPG (At 1) (Cj (At 0) (At 1))
   \<and> distinct [At 0, At 1, Cj (At 0) (At 1)] \<and> GE {At 0, At 1} (Cj (At 0) (At 1))"
  by (simp add: ME_IPG GE_def)

lemma ME_core: "ME.FACT" "ME.N1" "ME.N2" "ME.N5_chain"
  and ME_N4: "ME.N4_pair (At 0) (Cj (At 0) (At 0))"
  and ME_infinite: "infinite (UNIV :: tm set)"
proof -
  show "ME.FACT" unfolding ME.FACT_def GE_def by auto
  have g: "GE {x} (Cj x x)" if "TE x" for x unfolding GE_def using that by simp
  have pg: "ME.PG x (Cj x x)" if "TE x" for x unfolding ME.PG_def using g[OF that] by blast
  show n1: "ME.N1" unfolding ME.N1_def using g[of "At 0"] by auto
  have "distinct [At 0, At 1, At 2]" "TE (At 0)" "TE (At 1)" "TE (At 2)" by simp_all
  thus "ME.N2" unfolding ME.N2_def using n1 by blast
  define x1 where "x1 = Cj (At 0) (At 0)"
  define x2 where "x2 = Cj x1 x1"
  define x3 where "x3 = Cj x2 x2"
  have T: "TE (At 0)" "TE x1" "TE x2" unfolding x1_def x2_def by simp_all
  have "ME.PG (At 0) x1" "ME.PG x1 x2" "ME.PG x2 x3"
    using pg[OF T(1)] pg[OF T(2)] pg[OF T(3)] unfolding x1_def x2_def x3_def by simp_all
  moreover have "distinct [At 0, x1, x2, x3]" unfolding x1_def x2_def x3_def by simp
  ultimately show "ME.N5_chain" unfolding ME.N5_chain_def by blast
  have e: "\<not> GE \<Gamma> (At 0)" for \<Gamma> unfolding GE_def by simp
  have "{\<Gamma>. GE \<Gamma> (At 0)} \<noteq> {\<Gamma>. GE \<Gamma> (Cj (At 0) (At 0))}" using e g[of "At 0"] by auto
  moreover have "At 0 \<noteq> Cj (At 0) (At 0)" by simp
  ultimately show "ME.N4_pair (At 0) (Cj (At 0) (At 0))" unfolding ME.N4_pair_def by blast
  have "inj At" by (simp add: inj_def)
  have "\<not> finite (range At)"
  proof
    assume "finite (range At)"
    hence "finite (UNIV :: nat set)" using finite_imageD[OF _ \<open>inj At\<close>] by blast
    thus False by simp
  qed
  thus "infinite (UNIV :: tm set)" using finite_subset[OF subset_UNIV] by blast
qed

lemma ME_N4s: "ME.N4_pairs" using ME.N4_cc[OF ME_N4] .

section \<open>IMM.FRITZ7 with classical truth: CL.PROP, CL.QUANT and TS.FULL\<close>

text \<open>Model F. The same term algebra, now with classical truth: an atom At n is true iff n is
  even, the connectives and the truth ascription Tc are truth-functional, and the three
  quantified propositions get the truth values CL.QUANT requires for the single
  propositional function (the identity): exq and bigconj true, allq false. A true
  conjunction is fully grounded by its two conjuncts; a true disjunction by the set of its
  true disjuncts (one or both). Nothing else grounds anything. Each proposition has at most
  one full ground, so immediate and mediate ground coincide. Fritz's main result
  (P.FRITZ.MAIN) adds C3s; this model has one propositional function and so fails C3s.\<close>

primrec TF :: "tm \<Rightarrow> bool" where
  "TF (At n) = even n" | "TF (Cj a b) = (TF a \<and> TF b)" | "TF (Dj a b) = (TF a \<or> TF b)"
| "TF (Ng a) = (\<not> TF a)" | "TF (Tc a) = TF a" | "TF (Qu n) = (n \<noteq> 1)"

definition GF :: "tm set \<Rightarrow> tm \<Rightarrow> bool" where
  "GF \<Gamma> q \<longleftrightarrow> (\<exists>a b. q = Cj a b \<and> TF a \<and> TF b \<and> \<Gamma> = {a, b})
             \<or> (\<exists>a b. q = Dj a b \<and> (TF a \<or> TF b) \<and> \<Gamma> = {x. (x = a \<or> x = b) \<and> TF x})"

interpretation MF: gsig TF At Ng Cj Dj Tc "\<lambda>(_::unit) p. p" "\<lambda>_. Qu 0" "\<lambda>_. Qu 1" "\<lambda>_. Qu 2"
  "\<lambda>_ _ _. ()" "\<lambda>_. True" GF "\<lambda>_. At 0" "At 0" .

lemma GF_unique: "GF \<Gamma> q \<Longrightarrow> GF \<Delta> q \<Longrightarrow> \<Delta> = \<Gamma>"
  unfolding GF_def by (elim disjE exE conjE) simp_all

lemma MF_IG: "MF.IG \<Gamma> q \<longleftrightarrow> GF \<Gamma> q"
proof
  assume "MF.IG \<Gamma> q" thus "GF \<Gamma> q" by (simp add: MF.IG_def)
next
  assume g: "GF \<Gamma> q"
  have H: "\<forall>\<Delta>. GF \<Delta> q \<longrightarrow> (\<forall>p\<in>\<Gamma> - \<Delta>. \<exists>\<Delta>'\<subseteq>\<Delta>. GF \<Delta>' p)"
  proof (intro allI impI ballI)
    fix \<Delta> p assume d: "GF \<Delta> q" and p: "p \<in> \<Gamma> - \<Delta>"
    have "\<Delta> = \<Gamma>" using GF_unique[OF g d] .
    thus "\<exists>\<Delta>'\<subseteq>\<Delta>. GF \<Delta>' p" using p by simp
  qed
  show "MF.IG \<Gamma> q" unfolding MF.IG_def using g H by (rule conjI)
qed

lemma MF_IPG: "MF.IPG r q \<longleftrightarrow>
    (\<exists>a b. q = Cj a b \<and> TF a \<and> TF b \<and> (r = a \<or> r = b)) \<or> (\<exists>a b. q = Dj a b \<and> TF r \<and> (r = a \<or> r = b))"
  unfolding MF.IPG_def MF_IG GF_def by auto

lemma MF_IMM_FRITZ7: "MF.IMM_FRITZ7"
proof -
  have "\<not> MF.IPG (At 0) (At 2)" by (simp add: MF_IPG)
  hence nt: "\<not> (\<forall>p q. TF p \<and> TF q \<longrightarrow> MF.IPG p q)" by force
  show ?thesis unfolding MF.IMM_FRITZ7_def using nt by (auto simp: MF_IPG)
qed

lemma MF_classical: "MF.CL_PROP" "MF.CL_QUANT" "MF.TS_FULL"
proof -
  show "MF.CL_PROP" by (simp add: MF.CL_PROP_def)
  show "MF.TS_FULL" by (simp add: MF.TS_FULL_def)
  have "TF (At 0)" "\<not> TF (At 1)" by simp_all
  hence "\<exists>a. TF a" "\<not> (\<forall>a. TF a)" by blast+
  moreover have "\<forall>q\<in>MF.sat f. TF q" for f by (simp add: MF.sat_def)
  ultimately show "MF.CL_QUANT" unfolding MF.CL_QUANT_def by simp
qed

lemma MF_core: "MF.FACT" "MF.N1" "MF.N2" "MF.N5_chain" "MF.N4_pairs"
  and MF_N4: "MF.N4_pair (At 0) (Cj (At 0) (At 0))"
proof -
  show "MF.FACT" unfolding MF.FACT_def GF_def by auto
  have g: "GF {x} (Cj x x)" if "TF x" for x unfolding GF_def using that by simp
  have pg: "MF.PG x (Cj x x)" if "TF x" for x unfolding MF.PG_def using g[OF that] by blast
  show n1: "MF.N1" unfolding MF.N1_def using g[of "At 0"] by auto
  have "distinct [At 0, At 2, At 4]" "TF (At 0)" "TF (At 2)" "TF (At 4)" by simp_all
  thus "MF.N2" unfolding MF.N2_def using n1 by blast
  define x1 where "x1 = Cj (At 0) (At 0)"
  define x2 where "x2 = Cj x1 x1"
  define x3 where "x3 = Cj x2 x2"
  have T: "TF (At 0)" "TF x1" "TF x2" unfolding x1_def x2_def by simp_all
  have "MF.PG (At 0) x1" "MF.PG x1 x2" "MF.PG x2 x3"
    using pg[OF T(1)] pg[OF T(2)] pg[OF T(3)] unfolding x1_def x2_def x3_def by simp_all
  moreover have "distinct [At 0, x1, x2, x3]" unfolding x1_def x2_def x3_def by simp
  ultimately show "MF.N5_chain" unfolding MF.N5_chain_def by blast
  have e: "\<not> GF \<Gamma> (At 0)" for \<Gamma> unfolding GF_def by simp
  have "{\<Gamma>. GF \<Gamma> (At 0)} \<noteq> {\<Gamma>. GF \<Gamma> (Cj (At 0) (At 0))}" using e g[of "At 0"] by auto
  moreover have "At 0 \<noteq> Cj (At 0) (At 0)" by simp
  ultimately show N4: "MF.N4_pair (At 0) (Cj (At 0) (At 0))" unfolding MF.N4_pair_def by blast
  thus "MF.N4_pairs" by (rule MF.N4_cc)
qed

text \<open>N3 instances for the classical model, if the IMM clauses count as introduction entries:
  a conjunction of two distinct truths, and a disjunction with exactly one true disjunct.\<close>
lemma MF_N3:
  "MF.IPG (At 0) (Cj (At 0) (At 2)) \<and> MF.IPG (At 2) (Cj (At 0) (At 2)) \<and> distinct [At 0, At 2, Cj (At 0) (At 2)]
   \<and> GF {At 0} (Dj (At 0) (At 1)) \<and> distinct [At 0, Dj (At 0) (At 1)]"
proof -
  have "{x. (x = At 0 \<or> x = At 1) \<and> TF x} = {At 0}" by auto
  thus ?thesis by (simp add: MF_IPG GF_def)
qed

end
