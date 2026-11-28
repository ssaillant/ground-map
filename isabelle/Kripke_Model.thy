theory Kripke_Model
  imports NonClassical Models "HOL-Library.Extended_Nat"
begin

text \<open>
  K1: a strong Kleene term model with beta identity, after Fine 2010 sect. 8
  (pp. 110-115). Fine reads Kripke's fixed-point construction "in proof-theoretic
  fashion" (p. 110) and takes A to ground B when A is used in an "efficient" derivation
  of B, one that derives each truth at the earliest stage (p. 112, and fn. 13: "each
  sentence is assigned a minimal rank"). He claims that under the strong Kleene tables
  this gives an irreflexive and transitive ground for which Universal Grounding and the
  weak disjunctive and existential principles hold, and the strong ones fail
  (pp. 112-114). K1 makes this precise for the registry's signature.

  Propositions are closed terms; propositional quantifiers are closures of a formula
  under an environment, and application is substitution, so BETA.ID holds and every
  lambda term is admissible (C3d). Each term gets a pair of stages (t, f) in enat:
  t is the stage at which it becomes true, f the stage at which it becomes false, and
  \<infinity> means never. Stages are computed by recursion on terms. The step that makes this
  possible is monotonicity (sf_mono): a quantifier's instances are no harder to settle
  than its instance at a gap, so a universal is true at stage 1 + (stage of its instance
  at a gap), and an existential is true at 1 + (the smaller stage of its instances at a
  true and at a false atom). Ground is the least relation closed under the package's
  introduction rules restricted to efficient premises (premise stage below conclusion
  stage), cut and amalgamation; soundness (kgr_sound) shows every ground has strictly
  earlier premises, which gives IRR.F and ASYM.P.

  Atom 0 is true at stage 0, atom 1 false at stage 0, every other atom is a gap.
  infinitary conjunction (bigconj) is a gap throughout: SK.QUANT says nothing about it.
\<close>

declare not_infinity_eq [iff del]

section \<open>Restated principles for the new entries\<close>

definition "pSK_PROP S \<longleftrightarrow> (\<forall>p q. \<not> (sT S p \<and> sT S (sneg S p))
     \<and> (sT S (sneg S (sneg S p)) \<longleftrightarrow> sT S p)
     \<and> (sT S (sconj S p q) \<longleftrightarrow> sT S p \<and> sT S q)
     \<and> (sT S (sneg S (sconj S p q)) \<longleftrightarrow> sT S (sneg S p) \<or> sT S (sneg S q))
     \<and> (sT S (sdisj S p q) \<longleftrightarrow> sT S p \<or> sT S q)
     \<and> (sT S (sneg S (sdisj S p q)) \<longleftrightarrow> sT S (sneg S p) \<and> sT S (sneg S q)))"
definition "pSK_QUANT S \<longleftrightarrow> (\<forall>f. (sT S (sexq S f) \<longleftrightarrow> (\<exists>a. sT S (sapp S f a)))
     \<and> (sT S (sneg S (sexq S f)) \<longleftrightarrow> (\<forall>a. sT S (sneg S (sapp S f a))))
     \<and> (sT S (sallq S f) \<longleftrightarrow> (\<forall>a. sT S (sapp S f a)))
     \<and> (sT S (sneg S (sallq S f)) \<longleftrightarrow> (\<exists>a. sT S (sneg S (sapp S f a)))))"
definition "pTS_KF S \<longleftrightarrow> (\<forall>p. (sT S (strr S p) \<longleftrightarrow> sT S p) \<and> (sT S (sneg S (strr S p)) \<longleftrightarrow> sT S (sneg S p)))"
definition "pSK_GAP S \<longleftrightarrow> (\<exists>p. \<not> sT S p \<and> \<not> sT S (sneg S p))"
definition "pDISJ_WEAK S \<longleftrightarrow> (\<forall>p q. sT S (sdisj S p q) \<longrightarrow> pPG S p (sdisj S p q) \<or> pPG S q (sdisj S p q))"
definition "pEX_WEAK S \<longleftrightarrow> (\<forall>f. sadm S f \<and> sT S (sexq S f) \<longrightarrow> (\<exists>a. pPG S (sapp S f a) (sexq S f)))"

lemma fidelity_nc:
  "pSK_PROP S0 = SK_PROP" "pSK_QUANT S0 = SK_QUANT" "pTS_KF S0 = TS_KF" "pSK_GAP S0 = SK_GAP"
  "pDISJ_WEAK S0 = DISJ_WEAK" "pEX_WEAK S0 = EX_WEAK"
  by (simp_all only: pSK_PROP_def SK_PROP_def pSK_QUANT_def SK_QUANT_def pTS_KF_def TS_KF_def
      pSK_GAP_def SK_GAP_def pDISJ_WEAK_def DISJ_WEAK_def pEX_WEAK_def EX_WEAK_def S0_simps S0_sel)

section \<open>Stages\<close>

type_synonym info = "enat \<times> enat"

definition TI :: info where "TI = (0, \<infinity>)"
definition FI :: info where "FI = (\<infinity>, 0)"
definition NI :: info where "NI = (\<infinity>, \<infinity>)"
definition atinfo :: "nat \<Rightarrow> info" where
  "atinfo n = (if n = 0 then TI else if n = 1 then FI else NI)"

primrec sf :: "(nat \<Rightarrow> info) \<Rightarrow> fm \<Rightarrow> info" where
  "sf e (Var n) = e n"
| "sf e (Cst n) = atinfo n"
| "sf e (Neg a) = (eSuc (snd (sf e a)), eSuc (fst (sf e a)))"
| "sf e (Conj a b) = (eSuc (max (fst (sf e a)) (fst (sf e b))), eSuc (min (snd (sf e a)) (snd (sf e b))))"
| "sf e (Disj a b) = (eSuc (min (fst (sf e a)) (fst (sf e b))), eSuc (max (snd (sf e a)) (snd (sf e b))))"
| "sf e (Tr a) = (eSuc (fst (sf e a)), eSuc (snd (sf e a)))"
| "sf e (Ex x a) = (eSuc (min (fst (sf (e(x:=TI)) a)) (fst (sf (e(x:=FI)) a))), eSuc (snd (sf (e(x:=NI)) a)))"
| "sf e (All x a) = (eSuc (fst (sf (e(x:=NI)) a)), eSuc (min (snd (sf (e(x:=TI)) a)) (snd (sf (e(x:=FI)) a))))"
| "sf e (BigC x a) = NI"

datatype ktm = KAtom nat | KNeg ktm | KConj ktm ktm | KDisj ktm ktm | KTr ktm
  | KEx nat fm "nat \<Rightarrow> ktm" | KAll nat fm "nat \<Rightarrow> ktm" | KBig nat fm "nat \<Rightarrow> ktm"

datatype kfn = KLam nat fm "nat \<Rightarrow> ktm"

primrec st :: "ktm \<Rightarrow> info" where
  "st (KAtom n) = atinfo n"
| "st (KNeg p) = (eSuc (snd (st p)), eSuc (fst (st p)))"
| "st (KConj p q) = (eSuc (max (fst (st p)) (fst (st q))), eSuc (min (snd (st p)) (snd (st q))))"
| "st (KDisj p q) = (eSuc (min (fst (st p)) (fst (st q))), eSuc (max (snd (st p)) (snd (st q))))"
| "st (KTr p) = (eSuc (fst (st p)), eSuc (snd (st p)))"
| "st (KEx x a v) = sf (st \<circ> v) (Ex x a)"
| "st (KAll x a v) = sf (st \<circ> v) (All x a)"
| "st (KBig x a v) = NI"

definition KT :: "ktm \<Rightarrow> bool" where "KT p \<longleftrightarrow> fst (st p) \<noteq> \<infinity>"
abbreviation stT :: "ktm \<Rightarrow> enat" where "stT p \<equiv> fst (st p)"

section \<open>Facts about enat used below\<close>

lemma eSuc_inf_iff [simp]: "eSuc a = \<infinity> \<longleftrightarrow> a = \<infinity>"
  by (cases a) (simp_all add: eSuc_enat)

lemma max_inf_iff [simp]: "max a b = (\<infinity>::enat) \<longleftrightarrow> a = \<infinity> \<or> b = \<infinity>"
  by (cases "a \<le> b") (auto simp: max_def)

lemma min_inf_iff [simp]: "min a b = (\<infinity>::enat) \<longleftrightarrow> a = \<infinity> \<and> b = \<infinity>"
  by (cases "a \<le> b") (auto simp: min_def)

lemma lt_eSuc: "a \<noteq> \<infinity> \<Longrightarrow> a < eSuc a"
  by (cases a) (simp_all add: eSuc_enat)

lemma le_fin: "(a::enat) \<le> b \<Longrightarrow> b \<noteq> \<infinity> \<Longrightarrow> a \<noteq> \<infinity>"
  by (cases a; cases b) simp_all

lemma lt_fin: "(a::enat) < b \<Longrightarrow> a \<noteq> \<infinity>"
  by (cases a; cases b) simp_all

section \<open>Environment agreement and monotonicity\<close>

lemma sf_fv: "(\<forall>y\<in>fv a. e y = e' y) \<Longrightarrow> sf e a = sf e' a"
proof (induct a arbitrary: e e')
  case (Ex x a)
  have "\<And>i. sf (e(x:=i)) a = sf (e'(x:=i)) a" by (rule Ex.hyps) (use Ex.prems in auto)
  then show ?case by simp
next
  case (All x a)
  have "\<And>i. sf (e(x:=i)) a = sf (e'(x:=i)) a" by (rule All.hyps) (use All.prems in auto)
  then show ?case by simp
next
  case (Neg a)
  have "sf e a = sf e' a" by (rule Neg.hyps) (use Neg.prems in auto)
  then show ?case by simp
next
  case (Tr a)
  have "sf e a = sf e' a" by (rule Tr.hyps) (use Tr.prems in auto)
  then show ?case by simp
next
  case (Conj a b)
  have "sf e a = sf e' a" by (rule Conj.hyps(1)) (use Conj.prems in auto)
  moreover have "sf e b = sf e' b" by (rule Conj.hyps(2)) (use Conj.prems in auto)
  ultimately show ?case by simp
next
  case (Disj a b)
  have "sf e a = sf e' a" by (rule Disj.hyps(1)) (use Disj.prems in auto)
  moreover have "sf e b = sf e' b" by (rule Disj.hyps(2)) (use Disj.prems in auto)
  ultimately show ?case by simp
qed simp_all

text \<open>ile i j: j carries at least the information of i (each stage no later).\<close>
definition ile :: "info \<Rightarrow> info \<Rightarrow> bool" where
  "ile i j \<longleftrightarrow> fst j \<le> fst i \<and> snd j \<le> snd i"

lemma ile_refl [simp]: "ile i i" unfolding ile_def by simp
lemma ile_NI [simp]: "ile NI i" unfolding ile_def NI_def by simp

lemma ile_fst_fin: "ile i j \<Longrightarrow> fst i \<noteq> \<infinity> \<Longrightarrow> fst j \<noteq> \<infinity>"
  unfolding ile_def using le_fin by blast
lemma ile_snd_fin: "ile i j \<Longrightarrow> snd i \<noteq> \<infinity> \<Longrightarrow> snd j \<noteq> \<infinity>"
  unfolding ile_def using le_fin by blast

lemma ile_upd: "(\<forall>n. ile (e n) (e' n)) \<Longrightarrow> \<forall>n. ile ((e(x:=i)) n) ((e'(x:=i)) n)"
  by simp

lemma sf_mono: "(\<forall>n. ile (e n) (e' n)) \<Longrightarrow> ile (sf e a) (sf e' a)"
proof (induct a arbitrary: e e')
  case (Var n) then show ?case by simp
next
  case (Cst n) then show ?case by simp
next
  case (Neg a)
  then have "ile (sf e a) (sf e' a)" by blast
  then show ?case unfolding ile_def by simp
next
  case (Tr a)
  then have "ile (sf e a) (sf e' a)" by blast
  then show ?case unfolding ile_def by simp
next
  case (Conj a b)
  then have "ile (sf e a) (sf e' a)" "ile (sf e b) (sf e' b)" by blast+
  then show ?case unfolding ile_def by (auto simp: le_max_iff_disj min_le_iff_disj)
next
  case (Disj a b)
  then have "ile (sf e a) (sf e' a)" "ile (sf e b) (sf e' b)" by blast+
  then show ?case unfolding ile_def by (auto simp: le_max_iff_disj min_le_iff_disj)
next
  case (Ex x a)
  have h: "\<And>i. ile (sf (e(x:=i)) a) (sf (e'(x:=i)) a)"
    by (rule Ex.hyps) (rule ile_upd[OF Ex.prems])
  from h[of TI] h[of FI] h[of NI] show ?case unfolding ile_def by (auto simp: min_le_iff_disj)
next
  case (All x a)
  have h: "\<And>i. ile (sf (e(x:=i)) a) (sf (e'(x:=i)) a)"
    by (rule All.hyps) (rule ile_upd[OF All.prems])
  from h[of TI] h[of FI] h[of NI] show ?case unfolding ile_def by (auto simp: min_le_iff_disj)
next
  case (BigC x a) then show ?case by simp
qed

lemma sf_mono_at: "ile i j \<Longrightarrow> ile (sf (e(x:=i)) a) (sf (e(x:=j)) a)"
  by (rule sf_mono) simp

section \<open>Consistency: nothing is both true and false\<close>

definition cons :: "info \<Rightarrow> bool" where "cons i \<longleftrightarrow> fst i = \<infinity> \<or> snd i = \<infinity>"

lemma cons_TI [simp]: "cons TI" and cons_FI [simp]: "cons FI" and cons_NI [simp]: "cons NI"
  unfolding cons_def TI_def FI_def NI_def by simp_all

lemma cons_atinfo [simp]: "cons (atinfo n)" unfolding atinfo_def by simp

lemma ile_NI_TI: "ile NI TI" and ile_NI_FI: "ile NI FI" by simp_all

lemma sf_cons: "(\<forall>n. cons (e n)) \<Longrightarrow> cons (sf e a)"
proof (induct a arbitrary: e)
  case (Var n) then show ?case by simp
next
  case (Cst n) then show ?case by simp
next
  case (Neg a) then have "cons (sf e a)" by blast
  then show ?case unfolding cons_def by auto
next
  case (Tr a) then have "cons (sf e a)" by blast
  then show ?case unfolding cons_def by auto
next
  case (Conj a b) then have "cons (sf e a)" "cons (sf e b)" by blast+
  then show ?case unfolding cons_def by auto
next
  case (Disj a b) then have "cons (sf e a)" "cons (sf e b)" by blast+
  then show ?case unfolding cons_def by auto
next
  case (Ex x a)
  have c: "\<And>i. cons i \<Longrightarrow> cons (sf (e(x:=i)) a)"
    by (rule Ex.hyps) (use Ex.prems in simp)
  have mT: "ile (sf (e(x:=NI)) a) (sf (e(x:=TI)) a)" by (rule sf_mono_at) simp
  have mF: "ile (sf (e(x:=NI)) a) (sf (e(x:=FI)) a)" by (rule sf_mono_at) simp
  show ?case unfolding cons_def
  proof (rule disjCI)
    assume "\<not> snd (sf e (Ex x a)) = \<infinity>"
    then have n: "snd (sf (e(x:=NI)) a) \<noteq> \<infinity>" by simp
    have "snd (sf (e(x:=TI)) a) \<noteq> \<infinity>" using ile_snd_fin[OF mT n] .
    then have "fst (sf (e(x:=TI)) a) = \<infinity>" using c[OF cons_TI] unfolding cons_def by simp
    moreover have "snd (sf (e(x:=FI)) a) \<noteq> \<infinity>" using ile_snd_fin[OF mF n] .
    then have "fst (sf (e(x:=FI)) a) = \<infinity>" using c[OF cons_FI] unfolding cons_def by simp
    ultimately show "fst (sf e (Ex x a)) = \<infinity>" by simp
  qed
next
  case (All x a)
  have c: "\<And>i. cons i \<Longrightarrow> cons (sf (e(x:=i)) a)"
    by (rule All.hyps) (use All.prems in simp)
  have mT: "ile (sf (e(x:=NI)) a) (sf (e(x:=TI)) a)" by (rule sf_mono_at) simp
  have mF: "ile (sf (e(x:=NI)) a) (sf (e(x:=FI)) a)" by (rule sf_mono_at) simp
  show ?case unfolding cons_def
  proof (rule disjCI)
    assume "\<not> snd (sf e (All x a)) = \<infinity>"
    then have "snd (sf (e(x:=TI)) a) \<noteq> \<infinity> \<or> snd (sf (e(x:=FI)) a) \<noteq> \<infinity>" by simp
    then have "fst (sf (e(x:=TI)) a) = \<infinity> \<or> fst (sf (e(x:=FI)) a) = \<infinity>"
      using c[OF cons_TI] c[OF cons_FI] unfolding cons_def by blast
    then have "fst (sf (e(x:=NI)) a) = \<infinity>"
      using ile_fst_fin[OF mT] ile_fst_fin[OF mF] by blast
    then show "fst (sf e (All x a)) = \<infinity>" by simp
  qed
next
  case (BigC x a) then show ?case by simp
qed

lemma st_cons: "cons (st p)"
proof (induct p)
  case (KEx x a v)
  then have "\<forall>n. cons ((st \<circ> v) n)" by simp
  then show ?case by (simp add: sf_cons del: sf.simps)
next
  case (KAll x a v)
  then have "\<forall>n. cons ((st \<circ> v) n)" by simp
  then show ?case by (simp add: sf_cons del: sf.simps)
qed (auto simp: cons_def NI_def atinfo_def TI_def FI_def)

lemma cons_below: "cons i \<Longrightarrow> ile i TI \<or> ile i FI"
  unfolding cons_def ile_def TI_def FI_def by auto

section \<open>Denotation, lambda, application\<close>

definition nv :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> ktm) \<Rightarrow> nat \<Rightarrow> ktm" where
  "nv x a v = (\<lambda>n. if n \<in> fv a - {x} then v n else KAtom 0)"

definition klam :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> ktm) \<Rightarrow> kfn" where
  "klam x a v = KLam x a (nv x a v)"

primrec kden :: "(nat \<Rightarrow> ktm) \<Rightarrow> fm \<Rightarrow> ktm" where
  "kden v (Var n) = v n"
| "kden v (Cst n) = KAtom n"
| "kden v (Neg a) = KNeg (kden v a)"
| "kden v (Conj a b) = KConj (kden v a) (kden v b)"
| "kden v (Disj a b) = KDisj (kden v a) (kden v b)"
| "kden v (Tr a) = KTr (kden v a)"
| "kden v (Ex x a) = KEx x a (nv x a v)"
| "kden v (All x a) = KAll x a (nv x a v)"
| "kden v (BigC x a) = KBig x a (nv x a v)"

fun kapp :: "kfn \<Rightarrow> ktm \<Rightarrow> ktm" where "kapp (KLam x a v) p = kden (v(x:=p)) a"
fun kexq :: "kfn \<Rightarrow> ktm" where "kexq (KLam x a v) = KEx x a v"
fun kallq :: "kfn \<Rightarrow> ktm" where "kallq (KLam x a v) = KAll x a v"
fun kbig :: "kfn \<Rightarrow> ktm" where "kbig (KLam x a v) = KBig x a v"

definition kadm :: "kfn \<Rightarrow> bool" where "kadm f \<longleftrightarrow> (\<exists>x a v. f = klam x a v)"

lemma st_nv: "sf (st \<circ> nv x a v) (Ex x a) = sf (st \<circ> v) (Ex x a)"
             "sf (st \<circ> nv x a v) (All x a) = sf (st \<circ> v) (All x a)"
  by (rule sf_fv, simp add: nv_def)+

lemma st_kden: "st (kden v a) = sf (st \<circ> v) a"
proof (induct a arbitrary: v)
  case (Ex x a) show ?case by (simp only: kden.simps st.simps st_nv)
next
  case (All x a) show ?case by (simp only: kden.simps st.simps st_nv)
next
  case (BigC x a) show ?case by simp
qed simp_all

lemma comp_upd_st: "(st \<circ> v)(x := st p) = st \<circ> (v(x := p))"
  by (rule ext) simp

lemma st_kapp: "st (kapp (KLam x a v) p) = sf ((st \<circ> v)(x := st p)) a"
  by (simp only: kapp.simps st_kden comp_upd_st)

lemma kden_fv: "(\<forall>y\<in>fv a. v y = w y) \<Longrightarrow> kden v a = kden w a"
proof (induct a arbitrary: v w)
  case (Ex x a) then show ?case by (simp add: nv_def cong: if_cong)
next
  case (All x a) then show ?case by (simp add: nv_def cong: if_cong)
next
  case (BigC x a) then show ?case by (simp add: nv_def cong: if_cong)
qed auto

text \<open>Truth conditions of the quantifiers, from monotonicity: every term's stages are
  no less informative than a gap, and at least as informative as a true or a false atom
  only in the direction of its own value.\<close>

lemma atinfo_simps [simp]: "atinfo 0 = TI" "atinfo (Suc 0) = FI" "atinfo 2 = NI"
  by (simp_all add: atinfo_def)

lemma st_atoms: "st (KAtom 0) = TI" "st (KAtom (Suc 0)) = FI" "st (KAtom 2) = NI"
  by simp_all

lemma kq_ex: "KT (kexq f) \<longleftrightarrow> (\<exists>p. KT (kapp f p))"
proof (cases f)
  case (KLam x a v)
  let ?e = "st \<circ> v"
  have L: "KT (kexq f) \<longleftrightarrow> min (fst (sf (?e(x:=TI)) a)) (fst (sf (?e(x:=FI)) a)) \<noteq> \<infinity>"
    using KLam by (simp add: KT_def)
  have R: "\<And>p. KT (kapp f p) \<longleftrightarrow> fst (sf (?e(x:=st p)) a) \<noteq> \<infinity>"
    using KLam by (simp add: KT_def st_kapp del: sf.simps kapp.simps)
  show ?thesis
  proof
    assume "KT (kexq f)"
    then have "fst (sf (?e(x:=TI)) a) \<noteq> \<infinity> \<or> fst (sf (?e(x:=FI)) a) \<noteq> \<infinity>" using L by simp
    then show "\<exists>p. KT (kapp f p)"
    proof
      assume "fst (sf (?e(x:=TI)) a) \<noteq> \<infinity>"
      then have "KT (kapp f (KAtom 0))" using R[of "KAtom 0"] by simp
      then show ?thesis by blast
    next
      assume "fst (sf (?e(x:=FI)) a) \<noteq> \<infinity>"
      then have "KT (kapp f (KAtom (Suc 0)))" using R[of "KAtom (Suc 0)"] by simp
      then show ?thesis by blast
    qed
  next
    assume "\<exists>p. KT (kapp f p)"
    then obtain p where p: "fst (sf (?e(x:=st p)) a) \<noteq> \<infinity>" using R by blast
    from cons_below[OF st_cons[of p]] have "ile (st p) TI \<or> ile (st p) FI" .
    then have "fst (sf (?e(x:=TI)) a) \<noteq> \<infinity> \<or> fst (sf (?e(x:=FI)) a) \<noteq> \<infinity>"
    proof
      assume "ile (st p) TI"
      then have "ile (sf (?e(x:=st p)) a) (sf (?e(x:=TI)) a)" by (rule sf_mono_at)
      then show ?thesis using p ile_fst_fin by blast
    next
      assume "ile (st p) FI"
      then have "ile (sf (?e(x:=st p)) a) (sf (?e(x:=FI)) a)" by (rule sf_mono_at)
      then show ?thesis using p ile_fst_fin by blast
    qed
    then show "KT (kexq f)" using L by simp
  qed
qed

lemma kq_all: "KT (kallq f) \<longleftrightarrow> (\<forall>p. KT (kapp f p))"
proof (cases f)
  case (KLam x a v)
  let ?e = "st \<circ> v"
  have L: "KT (kallq f) \<longleftrightarrow> fst (sf (?e(x:=NI)) a) \<noteq> \<infinity>" using KLam by (simp add: KT_def)
  have R: "\<And>p. KT (kapp f p) \<longleftrightarrow> fst (sf (?e(x:=st p)) a) \<noteq> \<infinity>"
    using KLam by (simp add: KT_def st_kapp del: sf.simps kapp.simps)
  show ?thesis
  proof
    assume "KT (kallq f)"
    then have n: "fst (sf (?e(x:=NI)) a) \<noteq> \<infinity>" using L by simp
    show "\<forall>p. KT (kapp f p)"
    proof
      fix p
      have "ile (sf (?e(x:=NI)) a) (sf (?e(x:=st p)) a)" by (rule sf_mono_at) simp
      then show "KT (kapp f p)" using n R ile_fst_fin by blast
    qed
  next
    assume "\<forall>p. KT (kapp f p)"
    then have "KT (kapp f (KAtom 2))" by blast
    then show "KT (kallq f)" using L R[of "KAtom 2"] by simp
  qed
qed

definition KF :: "ktm \<Rightarrow> bool" where "KF p \<longleftrightarrow> snd (st p) \<noteq> \<infinity>"

lemma KT_neg [simp]: "KT (KNeg p) \<longleftrightarrow> KF p" unfolding KT_def KF_def by simp

lemma kq_negex: "KF (kexq f) \<longleftrightarrow> (\<forall>p. KF (kapp f p))"
proof (cases f)
  case (KLam x a v)
  let ?e = "st \<circ> v"
  have L: "KF (kexq f) \<longleftrightarrow> snd (sf (?e(x:=NI)) a) \<noteq> \<infinity>" using KLam by (simp add: KF_def)
  have R: "\<And>p. KF (kapp f p) \<longleftrightarrow> snd (sf (?e(x:=st p)) a) \<noteq> \<infinity>"
    using KLam by (simp add: KF_def st_kapp del: sf.simps kapp.simps)
  show ?thesis
  proof
    assume "KF (kexq f)"
    then have n: "snd (sf (?e(x:=NI)) a) \<noteq> \<infinity>" using L by simp
    show "\<forall>p. KF (kapp f p)"
    proof
      fix p
      have "ile (sf (?e(x:=NI)) a) (sf (?e(x:=st p)) a)" by (rule sf_mono_at) simp
      then show "KF (kapp f p)" using n R ile_snd_fin by blast
    qed
  next
    assume "\<forall>p. KF (kapp f p)"
    then have "KF (kapp f (KAtom 2))" by blast
    then show "KF (kexq f)" using L R[of "KAtom 2"] by simp
  qed
qed

lemma kq_negall: "KF (kallq f) \<longleftrightarrow> (\<exists>p. KF (kapp f p))"
proof (cases f)
  case (KLam x a v)
  let ?e = "st \<circ> v"
  have L: "KF (kallq f) \<longleftrightarrow> min (snd (sf (?e(x:=TI)) a)) (snd (sf (?e(x:=FI)) a)) \<noteq> \<infinity>"
    using KLam by (simp add: KF_def)
  have R: "\<And>p. KF (kapp f p) \<longleftrightarrow> snd (sf (?e(x:=st p)) a) \<noteq> \<infinity>"
    using KLam by (simp add: KF_def st_kapp del: sf.simps kapp.simps)
  show ?thesis
  proof
    assume "KF (kallq f)"
    then have "snd (sf (?e(x:=TI)) a) \<noteq> \<infinity> \<or> snd (sf (?e(x:=FI)) a) \<noteq> \<infinity>" using L by simp
    then show "\<exists>p. KF (kapp f p)"
    proof
      assume "snd (sf (?e(x:=TI)) a) \<noteq> \<infinity>"
      then have "KF (kapp f (KAtom 0))" using R[of "KAtom 0"] by simp
      then show ?thesis by blast
    next
      assume "snd (sf (?e(x:=FI)) a) \<noteq> \<infinity>"
      then have "KF (kapp f (KAtom (Suc 0)))" using R[of "KAtom (Suc 0)"] by simp
      then show ?thesis by blast
    qed
  next
    assume "\<exists>p. KF (kapp f p)"
    then obtain p where p: "snd (sf (?e(x:=st p)) a) \<noteq> \<infinity>" using R by blast
    from cons_below[OF st_cons[of p]] have "ile (st p) TI \<or> ile (st p) FI" .
    then have "snd (sf (?e(x:=TI)) a) \<noteq> \<infinity> \<or> snd (sf (?e(x:=FI)) a) \<noteq> \<infinity>"
    proof
      assume "ile (st p) TI"
      then have "ile (sf (?e(x:=st p)) a) (sf (?e(x:=TI)) a)" by (rule sf_mono_at)
      then show ?thesis using p ile_snd_fin by blast
    next
      assume "ile (st p) FI"
      then have "ile (sf (?e(x:=st p)) a) (sf (?e(x:=FI)) a)" by (rule sf_mono_at)
      then show ?thesis using p ile_snd_fin by blast
    qed
    then show "KF (kallq f)" using L by simp
  qed
qed

text \<open>Every instance of a true universal is true strictly earlier; an existential truth
  has an instance (at a true or a false atom) that is true strictly earlier.\<close>

lemma all_inst_earlier:
  assumes "KT (kallq f)" shows "stT (kapp f p) < stT (kallq f)"
proof (cases f)
  case (KLam x a v)
  let ?e = "st \<circ> v"
  have n: "fst (sf (?e(x:=NI)) a) \<noteq> \<infinity>" using assms KLam by (simp add: KT_def)
  have "ile (sf (?e(x:=NI)) a) (sf (?e(x:=st p)) a)" by (rule sf_mono_at) simp
  then have "stT (kapp f p) \<le> fst (sf (?e(x:=NI)) a)"
    using KLam by (simp add: ile_def st_kapp del: sf.simps kapp.simps)
  also have "\<dots> < eSuc (fst (sf (?e(x:=NI)) a))" using n by (rule lt_eSuc)
  also have "\<dots> = stT (kallq f)" using KLam by simp
  finally show ?thesis .
qed

lemma ex_inst_earlier:
  assumes "KT (kexq f)" shows "\<exists>p. KT (kapp f p) \<and> stT (kapp f p) < stT (kexq f)"
proof (cases f)
  case (KLam x a v)
  let ?e = "st \<circ> v"
  let ?t = "fst (sf (?e(x:=TI)) a)" and ?u = "fst (sf (?e(x:=FI)) a)"
  have m: "min ?t ?u \<noteq> \<infinity>" using assms KLam by (simp add: KT_def)
  have S: "stT (kexq f) = eSuc (min ?t ?u)" using KLam by simp
  have A0: "stT (kapp f (KAtom 0)) = ?t" and A1: "stT (kapp f (KAtom (Suc 0))) = ?u"
    using KLam by (simp_all add: st_kapp del: sf.simps kapp.simps)
  show ?thesis
  proof (cases "?t \<le> ?u")
    case True
    then have "min ?t ?u = ?t" by (simp add: min_def)
    then show ?thesis using m S A0 lt_eSuc[of ?t] unfolding KT_def by (intro exI[of _ "KAtom 0"]) simp
  next
    case False
    then have "min ?t ?u = ?u" by (simp add: min_def)
    then show ?thesis using m S A1 lt_eSuc[of ?u] unfolding KT_def by (intro exI[of _ "KAtom (Suc 0)"]) simp
  qed
qed

section \<open>Ground: efficient premises only\<close>

definition kclosed :: "(ktm set \<Rightarrow> ktm \<Rightarrow> bool) \<Rightarrow> bool" where
  "kclosed R \<longleftrightarrow>
     (\<forall>p q. KT p \<and> KT q \<longrightarrow> R {p, q} (KConj p q))
   \<and> (\<forall>p q. KT p \<and> stT p < stT (KDisj p q) \<longrightarrow> R {p} (KDisj p q))
   \<and> (\<forall>p q. KT q \<and> stT q < stT (KDisj p q) \<longrightarrow> R {q} (KDisj p q))
   \<and> (\<forall>p. KT p \<longrightarrow> R {p} (KNeg (KNeg p)))
   \<and> (\<forall>f a. kadm f \<and> KT (kapp f a) \<and> stT (kapp f a) < stT (kexq f) \<longrightarrow> R {kapp f a} (kexq f))
   \<and> (\<forall>f. kadm f \<and> (\<forall>a. KT (kapp f a)) \<longrightarrow> R (range (kapp f)) (kallq f))
   \<and> (\<forall>p. KT p \<longrightarrow> R {p} (KTr p))
   \<and> (\<forall>p. KT (KNeg p) \<longrightarrow> R {KNeg p} (KNeg (KTr p)))
   \<and> (\<forall>\<Gamma> \<Delta> H q. R \<Gamma> q \<and> \<Delta> \<subseteq> \<Gamma> \<and> (\<forall>p\<in>\<Delta>. R (H p) p) \<longrightarrow> R ((\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)) q)
   \<and> (\<forall>F p. F \<noteq> {} \<and> (\<forall>\<Gamma>\<in>F. R \<Gamma> p) \<longrightarrow> R (\<Union>F) p)"

definition kgr :: "ktm set \<Rightarrow> ktm \<Rightarrow> bool" where
  "kgr \<Gamma> q \<longleftrightarrow> (\<forall>R. kclosed R \<longrightarrow> R \<Gamma> q)"

lemmas kclosedD =
  kclosed_def[THEN iffD1, THEN conjunct1]
  kclosed_def[THEN iffD1, THEN conjunct2, THEN conjunct1]
  kclosed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  kclosed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  kclosed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  kclosed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  kclosed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  kclosed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  kclosed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  kclosed_def[THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]

lemma kg_conj: "KT p \<Longrightarrow> KT q \<Longrightarrow> kgr {p, q} (KConj p q)"
  unfolding kgr_def by (blast dest: kclosedD(1))
lemma kg_disjL: "KT p \<Longrightarrow> stT p < stT (KDisj p q) \<Longrightarrow> kgr {p} (KDisj p q)"
  unfolding kgr_def by (blast dest: kclosedD(2))
lemma kg_disjR: "KT q \<Longrightarrow> stT q < stT (KDisj p q) \<Longrightarrow> kgr {q} (KDisj p q)"
  unfolding kgr_def by (blast dest: kclosedD(3))
lemma kg_dn: "KT p \<Longrightarrow> kgr {p} (KNeg (KNeg p))"
  unfolding kgr_def by (blast dest: kclosedD(4))
lemma kg_ex: "kadm f \<Longrightarrow> KT (kapp f a) \<Longrightarrow> stT (kapp f a) < stT (kexq f) \<Longrightarrow> kgr {kapp f a} (kexq f)"
  unfolding kgr_def by (blast dest: kclosedD(5))
lemma kg_all: "kadm f \<Longrightarrow> \<forall>a. KT (kapp f a) \<Longrightarrow> kgr (range (kapp f)) (kallq f)"
  unfolding kgr_def by (blast dest: kclosedD(6))
lemma kg_tr: "KT p \<Longrightarrow> kgr {p} (KTr p)"
  unfolding kgr_def by (blast dest: kclosedD(7))
lemma kg_trneg: "KT (KNeg p) \<Longrightarrow> kgr {KNeg p} (KNeg (KTr p))"
  unfolding kgr_def by (blast dest: kclosedD(8))

lemma kg_cut:
  assumes "kgr \<Gamma> q" "\<Delta> \<subseteq> \<Gamma>" "\<forall>p\<in>\<Delta>. kgr (H p) p"
  shows "kgr ((\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)) q"
  unfolding kgr_def
proof (intro allI impI)
  fix R assume c: "kclosed R"
  with assms have "R \<Gamma> q" "\<forall>p\<in>\<Delta>. R (H p) p" unfolding kgr_def by blast+
  with kclosedD(9)[OF c] assms(2) show "R ((\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)) q" by blast
qed

lemma kg_amalg:
  assumes "F \<noteq> {}" "\<forall>\<Gamma>\<in>F. kgr \<Gamma> p"
  shows "kgr (\<Union>F) p"
  unfolding kgr_def
proof (intro allI impI)
  fix R assume c: "kclosed R"
  with assms have "\<forall>\<Gamma>\<in>F. R \<Gamma> p" unfolding kgr_def by blast
  with kclosedD(10)[OF c] assms(1) show "R (\<Union>F) p" by blast
qed

text \<open>Soundness: every ground is a non-empty set of truths, each true strictly earlier
  than the grounded truth.\<close>

definition kinv :: "ktm set \<Rightarrow> ktm \<Rightarrow> bool" where
  "kinv \<Gamma> q \<longleftrightarrow> \<Gamma> \<noteq> {} \<and> KT q \<and> (\<forall>p\<in>\<Gamma>. KT p \<and> stT p < stT q)"

lemma kinv_cut:
  assumes "kinv \<Gamma> q" "\<Delta> \<subseteq> \<Gamma>" "\<forall>p\<in>\<Delta>. kinv (H p) p"
  shows "kinv ((\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)) q"
proof -
  have ne: "(\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p) \<noteq> {}"
  proof (cases "\<Gamma> - \<Delta> = {}")
    case True
    with assms(2) have "\<Delta> = \<Gamma>" by blast
    with assms(1) obtain p where p: "p \<in> \<Delta>" unfolding kinv_def by blast
    with assms(3) have "kinv (H p) p" by blast
    then obtain r where "r \<in> H p" unfolding kinv_def by blast
    with p show ?thesis by blast
  next
    case False then show ?thesis by blast
  qed
  have all: "\<forall>r\<in>(\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p). KT r \<and> stT r < stT q"
  proof
    fix r assume "r \<in> (\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)"
    then show "KT r \<and> stT r < stT q"
    proof
      assume "r \<in> \<Gamma> - \<Delta>"
      with assms(1) show ?thesis unfolding kinv_def by blast
    next
      assume "r \<in> (\<Union>p\<in>\<Delta>. H p)"
      then obtain p where p: "p \<in> \<Delta>" "r \<in> H p" by blast
      from assms(3) p(1) have "kinv (H p) p" by blast
      with p(2) have r: "KT r" "stT r < stT p" unfolding kinv_def by blast+
      from p(1) assms(2) have "p \<in> \<Gamma>" by blast
      with assms(1) have "stT p < stT q" unfolding kinv_def by blast
      with r show ?thesis by (blast intro: less_trans)
    qed
  qed
  from assms(1) have "KT q" unfolding kinv_def by blast
  with ne all show ?thesis unfolding kinv_def by blast
qed

lemma KT_fin: "KT p \<Longrightarrow> stT p \<noteq> \<infinity>" unfolding KT_def by simp

lemma kinv_conj: "KT p \<Longrightarrow> KT q \<Longrightarrow> kinv {p, q} (KConj p q)"
proof -
  assume a: "KT p" "KT q"
  then have f: "stT p \<noteq> \<infinity>" "stT q \<noteq> \<infinity>" unfolding KT_def by simp_all
  let ?m = "max (stT p) (stT q)"
  have m: "?m \<noteq> \<infinity>" using f by simp
  have s: "stT (KConj p q) = eSuc ?m" by simp
  have "stT p \<le> ?m" "stT q \<le> ?m" by simp_all
  then have "stT p < eSuc ?m" "stT q < eSuc ?m" using lt_eSuc[OF m] by (blast intro: le_less_trans)+
  moreover have "KT (KConj p q)" unfolding KT_def using s m by simp
  ultimately show ?thesis unfolding kinv_def using a s by simp
qed

lemma kinv_disj: "KT p \<Longrightarrow> stT p < stT (KDisj p q) \<Longrightarrow> kinv {p} (KDisj p q)"
  "KT q \<Longrightarrow> stT q < stT (KDisj p q) \<Longrightarrow> kinv {q} (KDisj p q)"
proof -
  assume a: "KT p" "stT p < stT (KDisj p q)"
  have "min (stT p) (stT q) \<noteq> \<infinity>" using a(1) unfolding KT_def by simp
  then have "KT (KDisj p q)" unfolding KT_def by simp
  with a show "kinv {p} (KDisj p q)" unfolding kinv_def by simp
next
  assume a: "KT q" "stT q < stT (KDisj p q)"
  have "min (stT p) (stT q) \<noteq> \<infinity>" using a(1) unfolding KT_def by simp
  then have "KT (KDisj p q)" unfolding KT_def by simp
  with a show "kinv {q} (KDisj p q)" unfolding kinv_def by simp
qed

lemma kinv_dn: "KT p \<Longrightarrow> kinv {p} (KNeg (KNeg p))"
proof -
  assume a: "KT p"
  then have f: "stT p \<noteq> \<infinity>" unfolding KT_def .
  have s: "stT (KNeg (KNeg p)) = eSuc (eSuc (stT p))" by simp
  have "stT p < eSuc (stT p)" using f by (rule lt_eSuc)
  also have "\<dots> < eSuc (eSuc (stT p))" using f by (intro lt_eSuc) simp
  finally have l: "stT p < stT (KNeg (KNeg p))" using s by simp
  have "KT (KNeg (KNeg p))" unfolding KT_def using s f by simp
  with a l show ?thesis unfolding kinv_def by simp
qed

lemma kinv_ex: "KT (kapp f a) \<Longrightarrow> stT (kapp f a) < stT (kexq f) \<Longrightarrow> kinv {kapp f a} (kexq f)"
proof -
  assume a: "KT (kapp f a)" "stT (kapp f a) < stT (kexq f)"
  have "KT (kexq f)" using kq_ex a(1) by blast
  with a show ?thesis unfolding kinv_def by simp
qed

lemma kinv_all: "\<forall>a. KT (kapp f a) \<Longrightarrow> kinv (range (kapp f)) (kallq f)"
proof -
  assume a: "\<forall>a. KT (kapp f a)"
  then have t: "KT (kallq f)" using kq_all by blast
  have "\<forall>p\<in>range (kapp f). KT p \<and> stT p < stT (kallq f)"
  proof
    fix p assume "p \<in> range (kapp f)"
    then obtain b where "p = kapp f b" by blast
    then show "KT p \<and> stT p < stT (kallq f)" using a all_inst_earlier[OF t, of b] by simp
  qed
  then show ?thesis using t unfolding kinv_def by simp
qed

lemma kinv_tr: "KT p \<Longrightarrow> kinv {p} (KTr p)"
proof -
  assume a: "KT p"
  then have f: "stT p \<noteq> \<infinity>" unfolding KT_def .
  have "stT p < eSuc (stT p)" using f by (rule lt_eSuc)
  moreover have "KT (KTr p)" unfolding KT_def using f by simp
  ultimately show ?thesis using a unfolding kinv_def by simp
qed

lemma kinv_trneg: "KT (KNeg p) \<Longrightarrow> kinv {KNeg p} (KNeg (KTr p))"
proof -
  assume a: "KT (KNeg p)"
  then have f: "snd (st p) \<noteq> \<infinity>" by (simp add: KF_def)
  have s1: "stT (KNeg p) = eSuc (snd (st p))" by simp
  have s2: "stT (KNeg (KTr p)) = eSuc (eSuc (snd (st p)))" by simp
  have "eSuc (snd (st p)) < eSuc (eSuc (snd (st p)))" using f by (intro lt_eSuc) simp
  then have l: "stT (KNeg p) < stT (KNeg (KTr p))" using s1 s2 by simp
  have "KT (KNeg (KTr p))" unfolding KT_def using s2 f by simp
  with a l show ?thesis unfolding kinv_def by simp
qed

lemma kinv_amalg: "F \<noteq> {} \<Longrightarrow> \<forall>\<Gamma>\<in>F. kinv \<Gamma> p \<Longrightarrow> kinv (\<Union>F) p"
proof -
  assume F: "F \<noteq> {}" and a: "\<forall>\<Gamma>\<in>F. kinv \<Gamma> p"
  obtain \<Gamma> where g: "\<Gamma> \<in> F" using F by blast
  then have k: "kinv \<Gamma> p" using a by blast
  then obtain r where "r \<in> \<Gamma>" unfolding kinv_def by blast
  with g have ne: "\<Union>F \<noteq> {}" by blast
  have t: "KT p" using k unfolding kinv_def by blast
  have "\<forall>r\<in>\<Union>F. KT r \<and> stT r < stT p"
  proof
    fix r assume "r \<in> \<Union>F"
    then obtain \<Delta> where "\<Delta> \<in> F" "r \<in> \<Delta>" by blast
    with a show "KT r \<and> stT r < stT p" unfolding kinv_def by blast
  qed
  with ne t show ?thesis unfolding kinv_def by blast
qed

lemma kclosed_kinv: "kclosed kinv"
proof -
  have c1: "\<forall>p q. KT p \<and> KT q \<longrightarrow> kinv {p, q} (KConj p q)" using kinv_conj by blast
  have c2: "\<forall>p q. KT p \<and> stT p < stT (KDisj p q) \<longrightarrow> kinv {p} (KDisj p q)" using kinv_disj(1) by blast
  have c3: "\<forall>p q. KT q \<and> stT q < stT (KDisj p q) \<longrightarrow> kinv {q} (KDisj p q)" using kinv_disj(2) by blast
  have c4: "\<forall>p. KT p \<longrightarrow> kinv {p} (KNeg (KNeg p))" using kinv_dn by blast
  have c5: "\<forall>f a. kadm f \<and> KT (kapp f a) \<and> stT (kapp f a) < stT (kexq f) \<longrightarrow> kinv {kapp f a} (kexq f)"
    using kinv_ex by blast
  have c6: "\<forall>f. kadm f \<and> (\<forall>a. KT (kapp f a)) \<longrightarrow> kinv (range (kapp f)) (kallq f)"
    using kinv_all by blast
  have c7: "\<forall>p. KT p \<longrightarrow> kinv {p} (KTr p)" using kinv_tr by blast
  have c8: "\<forall>p. KT (KNeg p) \<longrightarrow> kinv {KNeg p} (KNeg (KTr p))" using kinv_trneg by blast
  have c9: "\<forall>\<Gamma> \<Delta> H q. kinv \<Gamma> q \<and> \<Delta> \<subseteq> \<Gamma> \<and> (\<forall>p\<in>\<Delta>. kinv (H p) p)
      \<longrightarrow> kinv ((\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)) q" using kinv_cut by blast
  have c10: "\<forall>F p. F \<noteq> {} \<and> (\<forall>\<Gamma>\<in>F. kinv \<Gamma> p) \<longrightarrow> kinv (\<Union>F) p"
    using kinv_amalg by blast
  show ?thesis unfolding kclosed_def
    by (intro conjI; fact c1 c2 c3 c4 c5 c6 c7 c8 c9 c10)
qed

lemma kgr_sound: "kgr \<Gamma> q \<Longrightarrow> \<Gamma> \<noteq> {} \<and> KT q \<and> (\<forall>p\<in>\<Gamma>. KT p \<and> stT p < stT q)"
  using kclosed_kinv unfolding kgr_def kinv_def by blast

section \<open>The structure K1\<close>

definition K1 :: "(ktm, kfn) gstr" where
  "K1 = \<lparr>sT = KT, sG = kgr, satom = KAtom, sneg = KNeg, sconj = KConj, sdisj = KDisj,
         strr = KTr, sapp = kapp, sexq = kexq, sallq = kallq, sbig = kbig, slam = klam,
         sadm = kadm\<rparr>"

lemma K1_sel [simp]:
  "sT K1 = KT" "sG K1 = kgr" "satom K1 = KAtom" "sneg K1 = KNeg" "sconj K1 = KConj"
  "sdisj K1 = KDisj" "strr K1 = KTr" "sapp K1 = kapp" "sexq K1 = kexq" "sallq K1 = kallq"
  "sbig K1 = kbig" "slam K1 = klam" "sadm K1 = kadm"
  by (simp_all add: K1_def)

lemma sden_K1: "sden K1 v a = kden v a"
  by (induct a arbitrary: v) (simp_all add: klam_def)

lemma PG_K1: "pPG K1 p q \<Longrightarrow> KT p \<and> KT q \<and> stT p < stT q"
  unfolding pPG_def by (auto dest: kgr_sound)

section \<open>The certificate\<close>

lemma K1_FACT: "pFACT K1" unfolding pFACT_def K1_sel by (blast dest: kgr_sound)

lemma K1_BETA_ID: "pBETA_ID K1" unfolding pBETA_ID_def K1_sel sden_K1
proof (intro allI)
  fix x a v p
  show "kapp (klam x a v) p = kden (v(x := p)) a"
    unfolding klam_def by (simp, rule kden_fv) (simp add: nv_def)
qed

lemma K1_LAM_CORE: "pLAM_CORE K1" unfolding pLAM_CORE_def
proof (intro conjI allI impI)
  fix x a v p
  show "sT K1 (sapp K1 (slam K1 x a v) p) = sT K1 (sden K1 (v(x := p)) a)"
    using K1_BETA_ID unfolding pBETA_ID_def by simp
next
  fix x a and v w :: "nat \<Rightarrow> ktm" assume "\<forall>y\<in>fv a - {x}. v y = w y"
  then show "slam K1 x a v = slam K1 x a w" unfolding K1_sel klam_def nv_def by (simp cong: if_cong)
qed

lemma K1_C3d: "pC3d K1" unfolding pC3d_def by (simp add: kadm_def)

lemma K1_SK_PROP: "pSK_PROP K1" unfolding pSK_PROP_def K1_sel
proof (intro allI conjI)
  fix p q :: ktm
  show "\<not> (KT p \<and> KT (KNeg p))" using st_cons[of p] unfolding cons_def KT_def KF_def KT_neg by simp
qed (simp_all add: KT_def KF_def)

lemma K1_SK_QUANT: "pSK_QUANT K1" unfolding pSK_QUANT_def K1_sel KT_neg
  using kq_ex kq_all kq_negex kq_negall by blast

lemma K1_TS_KF: "pTS_KF K1" unfolding pTS_KF_def K1_sel by (simp add: KT_def KF_def)
lemma K1_TS_FULL: "pTS_FULL K1" unfolding pTS_FULL_def K1_sel by (simp add: KT_def)

lemma K1_SK_GAP: "pSK_GAP K1" unfolding pSK_GAP_def K1_sel
  by (intro exI[of _ "KAtom 2"]) (simp add: KT_def KF_def NI_def)

lemma K1_IRR_F: "pIRR_F K1" unfolding pIRR_F_def K1_sel
proof (intro allI impI notI)
  fix \<Gamma> c assume "kgr \<Gamma> c" "c \<in> \<Gamma>"
  then have "stT c < stT c" by (blast dest: kgr_sound)
  then show False by simp
qed

lemma K1_ASYM_P: "pASYM_P K1" unfolding pASYM_P_def
proof (intro allI impI notI)
  fix p q assume "pPG K1 p q" "pPG K1 q p"
  then have "stT p < stT q" "stT q < stT p" by (auto dest!: PG_K1)
  then show False by simp
qed

lemma K1_TRANS_CUT: "pTRANS_CUT K1" unfolding pTRANS_CUT_def K1_sel
  using kg_cut by blast

lemma K1_TRANS_P: "pTRANS_P K1" unfolding pTRANS_P_def pPG_def K1_sel
proof (intro allI impI, elim conjE exE)
  fix p q r \<Gamma> \<Delta> assume a: "p \<in> \<Gamma>" "kgr \<Gamma> q" "q \<in> \<Delta>" "kgr \<Delta> r"
  from a(3) have sub: "{q} \<subseteq> \<Delta>" by simp
  from a(2) have h: "\<forall>x\<in>{q}. kgr \<Gamma> x" by simp
  have g: "kgr ((\<Delta> - {q}) \<union> (\<Union>x\<in>{q}. \<Gamma>)) r" by (rule kg_cut[OF a(4) sub h])
  from a(1) have "p \<in> (\<Delta> - {q}) \<union> (\<Union>x\<in>{q}. \<Gamma>)" by simp
  with g show "\<exists>\<Gamma>. p \<in> \<Gamma> \<and> kgr \<Gamma> r" by (intro exI conjI)
qed

lemma K1_AMALG_INF: "pAMALG_INF K1" unfolding pAMALG_INF_def K1_sel using kg_amalg by blast
lemma K1_EMPTY_NONE: "pEMPTY_NONE K1" unfolding pEMPTY_NONE_def K1_sel by (blast dest: kgr_sound)
lemma K1_CONJ_BIN: "pCONJ_BIN K1" unfolding pCONJ_BIN_def K1_sel by (blast intro: kg_conj)
lemma K1_NEG_DN: "pNEG_DN K1" unfolding pNEG_DN_def K1_sel by (blast intro: kg_dn)
lemma K1_TR_FULL: "pTR_FULL K1" unfolding pTR_FULL_def K1_sel by (blast intro: kg_tr)
lemma K1_TR_NEG: "pTR_NEG K1" unfolding pTR_NEG_def K1_sel by (blast intro: kg_trneg)
lemma K1_ALL_INST: "pALL_INST K1" unfolding pALL_INST_def pinst_def K1_sel by (blast intro: kg_all)

lemma K1_DISJ_WEAK: "pDISJ_WEAK K1" unfolding pDISJ_WEAK_def pPG_def K1_sel
proof (intro allI impI)
  fix p q assume t: "KT (KDisj p q)"
  then have m: "min (stT p) (stT q) \<noteq> \<infinity>" unfolding KT_def by simp
  have S: "stT (KDisj p q) = eSuc (min (stT p) (stT q))" by simp
  show "(\<exists>\<Gamma>. p \<in> \<Gamma> \<and> kgr \<Gamma> (KDisj p q)) \<or> (\<exists>\<Gamma>. q \<in> \<Gamma> \<and> kgr \<Gamma> (KDisj p q))"
  proof (cases "stT p \<le> stT q")
    case True
    then have e: "min (stT p) (stT q) = stT p" by (simp add: min_def)
    then have "KT p" "stT p < stT (KDisj p q)" using m S lt_eSuc[of "stT p"] unfolding KT_def by simp_all
    then have "kgr {p} (KDisj p q)" by (rule kg_disjL)
    then show ?thesis by blast
  next
    case False
    then have e: "min (stT p) (stT q) = stT q" by (simp add: min_def)
    then have "KT q" "stT q < stT (KDisj p q)" using m S lt_eSuc[of "stT q"] unfolding KT_def by simp_all
    then have "kgr {q} (KDisj p q)" by (rule kg_disjR)
    then show ?thesis by blast
  qed
qed

lemma K1_EX_WEAK: "pEX_WEAK K1" unfolding pEX_WEAK_def pPG_def K1_sel
proof (intro allI impI, elim conjE)
  fix f assume ad: "kadm f" and t: "KT (kexq f)"
  from ex_inst_earlier[OF t] obtain a where "KT (kapp f a)" "stT (kapp f a) < stT (kexq f)" by blast
  with ad have "kgr {kapp f a} (kexq f)" by (rule kg_ex)
  then show "\<exists>a \<Gamma>. kapp f a \<in> \<Gamma> \<and> kgr \<Gamma> (kexq f)" by blast
qed

lemma K1_chain: "kgr {KAtom 0} (KTr (KAtom 0))" "kgr {KTr (KAtom 0)} (KTr (KTr (KAtom 0)))"
  "kgr {KTr (KTr (KAtom 0))} (KTr (KTr (KTr (KAtom 0))))"
  by (simp_all add: kg_tr KT_def TI_def)

lemma K1_N1: "pN1 K1" unfolding pN1_def K1_sel using K1_chain(1) by blast

lemma K1_N2: "pN2 K1"
proof -
  have "distinct [KAtom 0, KTr (KAtom 0), KTr (KTr (KAtom 0))]
      \<and> KT (KAtom 0) \<and> KT (KTr (KAtom 0)) \<and> KT (KTr (KTr (KAtom 0)))" by (simp add: KT_def TI_def)
  with K1_N1 show ?thesis unfolding pN2_def K1_sel by blast
qed

lemma K1_N5_chain: "pN5_chain K1"
proof -
  have "distinct [KAtom 0, KTr (KAtom 0), KTr (KTr (KAtom 0)), KTr (KTr (KTr (KAtom 0)))]" by simp
  moreover have "pPG K1 (KAtom 0) (KTr (KAtom 0))" "pPG K1 (KTr (KAtom 0)) (KTr (KTr (KAtom 0)))"
    "pPG K1 (KTr (KTr (KAtom 0))) (KTr (KTr (KTr (KAtom 0))))"
    unfolding pPG_def K1_sel using K1_chain by blast+
  ultimately show ?thesis unfolding pN5_chain_def by blast
qed

theorem K1_package:
  "pFACT K1" "pLAM_CORE K1" "pC3d K1" "pBETA_ID K1" "pSK_PROP K1" "pSK_QUANT K1" "pTS_KF K1"
  "pTS_FULL K1" "pSK_GAP K1" "pIRR_F K1" "pASYM_P K1" "pTRANS_P K1" "pTRANS_CUT K1"
  "pAMALG_INF K1" "pEMPTY_NONE K1" "pCONJ_BIN K1" "pDISJ_WEAK K1" "pNEG_DN K1" "pEX_WEAK K1"
  "pALL_INST K1" "pTR_FULL K1" "pTR_NEG K1" "pN1 K1" "pN2 K1" "pN5_chain K1"
  by (fact K1_FACT K1_LAM_CORE K1_C3d K1_BETA_ID K1_SK_PROP K1_SK_QUANT K1_TS_KF K1_TS_FULL
      K1_SK_GAP K1_IRR_F K1_ASYM_P K1_TRANS_P K1_TRANS_CUT K1_AMALG_INF K1_EMPTY_NONE
      K1_CONJ_BIN K1_DISJ_WEAK K1_NEG_DN K1_EX_WEAK K1_ALL_INST K1_TR_FULL K1_TR_NEG
      K1_N1 K1_N2 K1_N5_chain)+

section \<open>What K1 gives up, as Fine says it must\<close>

text \<open>DISJ.ONE fails at Fine's own example (fn. 13, p. 116): "\<forall>x(x = x) \<or> T(\<forall>x(x = x))"
  is derived directly from its first disjunct, so the true second disjunct is no ground.
  Here atom 0 plays \<forall>x(x = x).\<close>

lemma K1_not_DISJ_ONE: "\<not> pDISJ_ONE K1"
proof
  assume "pDISJ_ONE K1"
  then have "kgr {KTr (KAtom 0)} (KDisj (KAtom 0) (KTr (KAtom 0)))"
    unfolding pDISJ_ONE_def K1_sel by (simp add: KT_def TI_def)
  then have "stT (KTr (KAtom 0)) < stT (KDisj (KAtom 0) (KTr (KAtom 0)))" by (blast dest: kgr_sound)
  then show False by (simp add: TI_def)
qed

text \<open>EX.FULL fails: the instance T(atom 0) of \<exists>p p is true but is settled no earlier
  than \<exists>p p itself (cf. Fine p. 114: "there is no efficient derivation of \<exists>x T(x) ...
  from T(\<exists>x T(x))").\<close>

lemma K1_not_EX_FULL: "\<not> pEX_FULL K1"
proof
  assume a: "pEX_FULL K1"
  let ?f = "klam 0 (Var 0) (\<lambda>_. KAtom 0)" and ?p = "KTr (KAtom 0)"
  have ad: "kadm ?f" unfolding kadm_def by blast
  have ap: "kapp ?f ?p = ?p" unfolding klam_def by simp
  have "KT ?p" by (simp add: KT_def TI_def)
  then have "KT (kapp ?f ?p)" by (simp only: ap)
  then have "kgr {kapp ?f ?p} (kexq ?f)" using a ad unfolding pEX_FULL_def K1_sel by blast
  then have "stT (kapp ?f ?p) < stT (kexq ?f)" by (blast dest: kgr_sound)
  then show False unfolding klam_def nv_def by (simp add: TI_def FI_def)
qed

text \<open>K1's gap is an atom, not a liar: no term is the negation of its own truth.\<close>

lemma K1_no_liar: "l \<noteq> KNeg (KTr l)"
proof
  assume "l = KNeg (KTr l)"
  then have "size l = size (KNeg (KTr l))" by simp
  then show False by simp
qed

end
