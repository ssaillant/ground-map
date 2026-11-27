theory Signature
  imports Main
begin

text \<open>
  Ground Map signature, registry v0.2.0-draft (2026-11-26): decisions 1-3 implemented.
  Propositions stay a base type; ground relates sets of propositions. A layer of
  formulas with a denotation map is used only by the restricted principles,
  comprehension, BETA and Woods's substitution. Nothing here is an axiom: core
  clauses are bundled as a locale-free definition and assumed as hypotheses.
\<close>

typedecl prp
typedecl pfun

datatype fm = Var nat | Cst nat | Neg fm | Conj fm fm | Disj fm fm | Tr fm
            | Ex nat fm | All nat fm | BigC nat fm

consts
  T       :: "prp \<Rightarrow> bool"
  atom    :: "nat \<Rightarrow> prp"
  neg     :: "prp \<Rightarrow> prp"
  conj    :: "prp \<Rightarrow> prp \<Rightarrow> prp"
  disj    :: "prp \<Rightarrow> prp \<Rightarrow> prp"
  tr      :: "prp \<Rightarrow> prp"
  app     :: "pfun \<Rightarrow> prp \<Rightarrow> prp"
  exq     :: "pfun \<Rightarrow> prp"
  allq    :: "pfun \<Rightarrow> prp"
  bigconj :: "pfun \<Rightarrow> prp"
  lam     :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> prp) \<Rightarrow> pfun"
  adm     :: "pfun \<Rightarrow> bool"
  G       :: "prp set \<Rightarrow> prp \<Rightarrow> bool"

primrec den :: "(nat \<Rightarrow> prp) \<Rightarrow> fm \<Rightarrow> prp" where
  "den v (Var n) = v n"
| "den v (Cst n) = atom n"
| "den v (Neg a) = neg (den v a)"
| "den v (Conj a b) = conj (den v a) (den v b)"
| "den v (Disj a b) = disj (den v a) (den v b)"
| "den v (Tr a) = tr (den v a)"
| "den v (Ex x a) = exq (lam x a v)"
| "den v (All x a) = allq (lam x a v)"
| "den v (BigC x a) = bigconj (lam x a v)"

primrec fv :: "fm \<Rightarrow> nat set" where
  "fv (Var n) = {n}"
| "fv (Cst n) = {}"
| "fv (Neg a) = fv a"
| "fv (Conj a b) = fv a \<union> fv b"
| "fv (Disj a b) = fv a \<union> fv b"
| "fv (Tr a) = fv a"
| "fv (Ex x a) = fv a - {x}"
| "fv (All x a) = fv a - {x}"
| "fv (BigC x a) = fv a - {x}"

primrec subf :: "fm \<Rightarrow> fm set" where
  "subf (Var n) = {Var n}"
| "subf (Cst n) = {Cst n}"
| "subf (Neg a) = insert (Neg a) (subf a)"
| "subf (Conj a b) = insert (Conj a b) (subf a \<union> subf b)"
| "subf (Disj a b) = insert (Disj a b) (subf a \<union> subf b)"
| "subf (Tr a) = insert (Tr a) (subf a)"
| "subf (Ex x a) = insert (Ex x a) (subf a)"
| "subf (All x a) = insert (All x a) (subf a)"
| "subf (BigC x a) = insert (BigC x a) (subf a)"

text \<open>Quantifier level (Kr\"amer) and truth-freeness (Korbmacher), on formulas.\<close>
primrec lvl :: "fm \<Rightarrow> nat" where
  "lvl (Var n) = 0"
| "lvl (Cst n) = 0"
| "lvl (Neg a) = lvl a"
| "lvl (Conj a b) = max (lvl a) (lvl b)"
| "lvl (Disj a b) = max (lvl a) (lvl b)"
| "lvl (Tr a) = lvl a"
| "lvl (Ex x a) = Suc (lvl a)"
| "lvl (All x a) = Suc (lvl a)"
| "lvl (BigC x a) = Suc (lvl a)"

primrec tfree :: "fm \<Rightarrow> bool" where
  "tfree (Var n) = True"
| "tfree (Cst n) = True"
| "tfree (Neg a) = tfree a"
| "tfree (Conj a b) = (tfree a \<and> tfree b)"
| "tfree (Disj a b) = (tfree a \<and> tfree b)"
| "tfree (Tr a) = False"
| "tfree (Ex x a) = tfree a"
| "tfree (All x a) = tfree a"
| "tfree (BigC x a) = tfree a"

definition inst :: "pfun \<Rightarrow> prp set" where "inst f = range (app f)"
definition sat  :: "pfun \<Rightarrow> prp set" where "sat f = {p. T (app f p)}"
definition PG :: "prp \<Rightarrow> prp \<Rightarrow> bool" where "PG p q \<longleftrightarrow> (\<exists>\<Gamma>. p \<in> \<Gamma> \<and> G \<Gamma> q)"

text \<open>Decision 1: immediate full ground defined from mediate full ground
  (Fritz 2022 p. 322 support proposal; the conjunct G \<Gamma> q is our reading).\<close>
definition IG :: "prp set \<Rightarrow> prp \<Rightarrow> bool" where
  "IG \<Gamma> q \<longleftrightarrow> G \<Gamma> q \<and> (\<forall>\<Delta>. G \<Delta> q \<longrightarrow> (\<forall>p\<in>\<Gamma> - \<Delta>. \<exists>\<Delta>'\<subseteq>\<Delta>. G \<Delta>' p))"
definition IPG :: "prp \<Rightarrow> prp \<Rightarrow> bool" where "IPG p q \<longleftrightarrow> (\<exists>\<Gamma>. p \<in> \<Gamma> \<and> IG \<Gamma> q)"

text \<open>Decision 2: Woods's vacuity by uniform substitution on formulas (one-world
  approximation of his modal test). \<Phi> presents the grounds with the parameter z
  marking the occurrences of A; no z-free subformula may denote A, so every
  occurrence is marked (uniformity, embedded occurrences included).\<close>
definition vacW :: "prp \<Rightarrow> prp set \<Rightarrow> prp \<Rightarrow> bool" where
  "vacW A \<Gamma> c \<longleftrightarrow> (\<exists>\<Phi> v z.
      \<Gamma> = (\<lambda>\<phi>. den (v(z:=A)) \<phi>) ` \<Phi>
    \<and> (\<exists>\<phi>\<in>\<Phi>. z \<in> fv \<phi>)
    \<and> (\<forall>\<phi>\<in>\<Phi>. \<forall>\<psi>\<in>subf \<phi>. z \<notin> fv \<psi> \<longrightarrow> den (v(z:=A)) \<psi> \<noteq> A)
    \<and> (\<forall>B. (\<forall>\<phi>\<in>\<Phi>. T (den (v(z:=B)) \<phi>)) \<longrightarrow> G ((\<lambda>\<phi>. den (v(z:=B)) \<phi>) ` \<Phi>) c))"

text \<open>Core clauses for the formula layer (assumed as hypotheses, never as axioms).\<close>
definition LAM_CORE :: bool where
  "LAM_CORE \<longleftrightarrow>
     (\<forall>x a v p. T (app (lam x a v) p) \<longleftrightarrow> T (den (v(x:=p)) a))
   \<and> (\<forall>x a v w. (\<forall>y\<in>fv a - {x}. v y = w y) \<longrightarrow> lam x a v = lam x a w)"

text \<open>Named witnesses (C1) as lambda terms over a fixed environment e0.\<close>
consts e0 :: "nat \<Rightarrow> prp"
definition "f_id  = lam 0 (Var 0) e0"
definition "f_tr  = lam 0 (Tr (Var 0)) e0"
definition "f_em  = lam 0 (Disj (Var 0) (Neg (Var 0))) e0"
definition "f_tem = lam 0 (Disj (Tr (Var 0)) (Neg (Tr (Var 0)))) e0"

text \<open>Comprehension levels: which propositional functions the grounding
  principles quantify over.\<close>
definition C1 :: bool where "C1 \<longleftrightarrow> (\<forall>f. adm f \<longleftrightarrow> f \<in> {f_id, f_tr, f_em, f_tem})"
definition C2 :: "nat \<Rightarrow> bool" where
  "C2 k \<longleftrightarrow> (\<forall>f. adm f \<longleftrightarrow> (\<exists>x a v. lvl a \<le> k \<and> f = lam x a v))"
definition C3d :: bool where "C3d \<longleftrightarrow> (\<forall>f. adm f \<longleftrightarrow> (\<exists>x a v. f = lam x a v))"
definition C3s :: bool where "C3s \<longleftrightarrow> (\<forall>f. adm f) \<and> (\<forall>h. \<exists>f. app f = h)"

definition BETA_ID :: bool where
  "BETA_ID \<longleftrightarrow> (\<forall>x a v p. app (lam x a v) p = den (v(x:=p)) a)"
definition BETA_GROUND :: bool where
  "BETA_GROUND \<longleftrightarrow> (\<forall>x a v p. T (den (v(x:=p)) a) \<longrightarrow>
      app (lam x a v) p \<noteq> den (v(x:=p)) a \<and> G {den (v(x:=p)) a} (app (lam x a v) p))"

lemma beta_id_f_id: "BETA_ID \<Longrightarrow> app f_id p = p"
  unfolding BETA_ID_def f_id_def by simp

text \<open>Sanity check of the new encoding: Kr\"amer's puzzle with C1 + BETA.ID.\<close>
theorem kramer_v2:
  assumes "C1" "BETA_ID"
      and CL_neg:  "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_ex:   "\<forall>f. T (exq f) \<longleftrightarrow> (\<exists>a. T (app f a))"
      and EX_FULL: "\<forall>f a. adm f \<and> T (app f a) \<longrightarrow> G {app f a} (exq f)"
      and IRR_F:   "\<forall>\<Gamma> c. G \<Gamma> c \<longrightarrow> c \<notin> \<Gamma>"
  shows False
proof -
  have id: "\<forall>p. app f_id p = p" using assms(2) beta_id_f_id by blast
  have ad: "adm f_id" using assms(1) unfolding C1_def by blast
  obtain q where "T q" using CL_neg by metis
  hence "T (exq f_id)" using CL_ex id by metis
  hence "G {exq f_id} (exq f_id)" using EX_FULL ad id by metis
  thus False using IRR_F by blast
qed

text \<open>Decision 2 sanity check: in Kr\"amer's case the self-ground of \<exists>p p is vacuous in
  Woods's sense (Woods p. 640), so IRR.W does not refute C1 + BETA.ID + EX.FULL here.\<close>
lemma kramer_vacuous:
  assumes "C1" "BETA_ID"
      and EX_FULL: "\<forall>f a. adm f \<and> T (app f a) \<longrightarrow> G {app f a} (exq f)"
  shows "vacW (exq f_id) {exq f_id} (exq f_id)"
proof -
  have id: "\<forall>p. app f_id p = p" using assms(2) beta_id_f_id by blast
  have ad: "adm f_id" using assms(1) unfolding C1_def by blast
  let ?v = "(\<lambda>_. exq f_id) :: nat \<Rightarrow> prp"
  have "\<forall>B. T B \<longrightarrow> G {B} (exq f_id)" using EX_FULL ad id by metis
  hence "(\<forall>B. (\<forall>\<phi>\<in>{Var 0}. T (den (?v(0:=B)) \<phi>)) \<longrightarrow> G ((\<lambda>\<phi>. den (?v(0:=B)) \<phi>) ` {Var 0}) (exq f_id))"
    by simp
  moreover have "{exq f_id} = (\<lambda>\<phi>. den (?v(0:=exq f_id)) \<phi>) ` {Var 0}" by simp
  moreover have "\<exists>\<phi>\<in>{Var 0}. (0::nat) \<in> fv \<phi>" by simp
  moreover have "\<forall>\<phi>\<in>{Var 0}. \<forall>\<psi>\<in>subf \<phi>. (0::nat) \<notin> fv \<psi> \<longrightarrow> den (?v(0:=exq f_id)) \<psi> \<noteq> exq f_id" by simp
  ultimately show ?thesis unfolding vacW_def by blast
qed

text \<open>Decision 1 checks. Fritz's conjunction principle for the defined immediate ground.\<close>
definition CONJ_IMM :: bool where
  "CONJ_IMM \<longleftrightarrow> (\<forall>f. adm f \<and> (\<forall>r\<in>sat f. T r) \<longrightarrow> (\<forall>p. IPG p (bigconj f) \<longleftrightarrow> p \<in> sat f))"

theorem grain_from_conj_imm:
  assumes CONJ_IMM and "adm f" "adm g" "\<forall>r\<in>sat f. T r" "\<forall>r\<in>sat g. T r"
      and "bigconj f = bigconj g"
  shows "sat f = sat g"
proof -
  have F: "\<forall>p. IPG p (bigconj f) \<longleftrightarrow> p \<in> sat f"
    using assms(1,2,4) unfolding CONJ_IMM_def by blast
  have Gg: "\<forall>p. IPG p (bigconj g) \<longleftrightarrow> p \<in> sat g"
    using assms(1,3,5) unfolding CONJ_IMM_def by blast
  show ?thesis using F Gg assms(6) by auto
qed

text \<open>Fritz's Cantorian argument (p. 306-307) with grain derived, not stipulated.
  No irreflexivity is used.\<close>
theorem fritz_cantor_imm:
  assumes "C3s" "CONJ_IMM"
      and CL_neg:  "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_conj: "\<forall>f. T (bigconj f) \<longleftrightarrow> (\<forall>r\<in>sat f. T r)"
  shows False
proof -
  obtain t where t: "T t" using CL_neg by metis
  have bt: "\<not> T (neg t)" using CL_neg t by blast
  let ?S = "{p. T p}"
  define mk where "mk X = (SOME f. app f = (\<lambda>p. if p \<in> X then t else neg t))" for X
  have app_mk: "app (mk X) = (\<lambda>p. if p \<in> X then t else neg t)" for X
  proof -
    have "\<exists>f. app f = (\<lambda>p. if p \<in> X then t else neg t)"
      using assms(1) unfolding C3s_def by blast
    thus ?thesis unfolding mk_def by (rule someI_ex)
  qed
  have sat_mk: "sat (mk X) = X" for X
  proof
    show "sat (mk X) \<subseteq> X"
    proof
      fix p assume "p \<in> sat (mk X)"
      hence "T (if p \<in> X then t else neg t)" unfolding sat_def using app_mk by simp
      thus "p \<in> X" using bt by (cases "p \<in> X") simp_all
    qed
    show "X \<subseteq> sat (mk X)"
    proof
      fix p assume "p \<in> X"
      thus "p \<in> sat (mk X)" unfolding sat_def using app_mk t by simp
    qed
  qed
  have adm_all: "adm f" for f using assms(1) unfolding C3s_def by blast
  define g where "g X = bigconj (mk X)" for X
  have g_in: "g X \<in> ?S" if "X \<subseteq> ?S" for X
    unfolding g_def using CL_conj sat_mk that by auto
  have g_inj: "X = Y" if XY: "X \<subseteq> ?S" "Y \<subseteq> ?S" "g X = g Y" for X Y
  proof -
    have tx: "\<forall>r\<in>sat (mk X). T r" using XY(1) sat_mk by blast
    have ty: "\<forall>r\<in>sat (mk Y). T r" using XY(2) sat_mk by blast
    have "sat (mk X) = sat (mk Y)"
      using grain_from_conj_imm[OF assms(2) adm_all adm_all tx ty] XY(3) unfolding g_def by blast
    thus ?thesis using sat_mk by simp
  qed
  define D where "D = {p \<in> ?S. \<exists>X\<subseteq>?S. g X = p \<and> p \<notin> X}"
  have DS: "D \<subseteq> ?S" unfolding D_def by blast
  show False
  proof (cases "g D \<in> D")
    case True
    then obtain X where X: "X \<subseteq> ?S" "g X = g D" "g D \<notin> X" unfolding D_def by blast
    hence "X = D" using g_inj DS by blast
    thus False using X True by blast
  next
    case False
    hence "g D \<in> D" using g_in DS unfolding D_def by blast
    thus False using False by blast
  qed
qed

text \<open>Fritz's predicative variant (p. 315) for the defined immediate ground:
  the conjunction of the truths that are not immediate partial grounds of themselves.\<close>
theorem fritz_p315_imm:
  assumes "C3s" "CONJ_IMM"
      and CL_neg:  "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_conj: "\<forall>f. T (bigconj f) \<longleftrightarrow> (\<forall>r\<in>sat f. T r)"
  shows False
proof -
  obtain t where t: "T t" using CL_neg by metis
  have bt: "\<not> T (neg t)" using CL_neg t by blast
  let ?R = "{p. T p \<and> \<not> IPG p p}"
  obtain f where f: "app f = (\<lambda>p. if p \<in> ?R then t else neg t)"
    using assms(1) unfolding C3s_def by blast
  have sf: "sat f = ?R"
  proof
    show "sat f \<subseteq> ?R"
    proof
      fix p assume "p \<in> sat f"
      hence "T (if p \<in> ?R then t else neg t)" unfolding sat_def using f by simp
      thus "p \<in> ?R" using bt by (auto split: if_split_asm)
    qed
    show "?R \<subseteq> sat f" unfolding sat_def using f t by auto
  qed
  have ad: "adm f" using assms(1) unfolding C3s_def by blast
  have allT: "\<forall>r\<in>sat f. T r" using sf by blast
  hence Tc: "T (bigconj f)" using CL_conj by blast
  have "\<forall>p. IPG p (bigconj f) \<longleftrightarrow> p \<in> sat f"
    using assms(2) ad allT unfolding CONJ_IMM_def by blast
  hence H: "IPG (bigconj f) (bigconj f) \<longleftrightarrow> bigconj f \<in> sat f" by blast
  have M: "bigconj f \<in> sat f \<longleftrightarrow> T (bigconj f) \<and> \<not> IPG (bigconj f) (bigconj f)"
    unfolding sf by simp
  show False using H M Tc by blast
qed

end
