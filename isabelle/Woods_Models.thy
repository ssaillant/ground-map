theory Woods_Models
  imports Separation_Models Puzzle_Packages NonClassical
begin

text \<open>
  Woods's weakened irreflexivity (IRR.W) against the puzzles of ground.

  Part 1 proves, from the registry's own constants, what IRR.W demands of a package
  with classical truth: a truth that helps ground itself has, for every truth B, a full
  ground in which B takes its place (woods_classical). It also reproduces Woods's
  Objection 3 and the controls. Part 2 is a finite model MW of the registry target
  P.WOODS.CHECK. Part 3 is an infinite model MV of all five Kr\"amer and Fine targets
  with IRR.W in place of IRR.F, in their full-ground versions and with every
  propositional function admissible. Part 4 reads MV at the comprehension levels C1,
  C2 and C3d. Part 5 is the model MY of the same packages with antisymmetry. Parts 6
  to 10 cover single further entries: MZ (one-membered grounds; FIN.B3), TS.KF in every
  model, ALL.TOT in MV, MQ (a zero-grounded truth; EMPTY.SOME), and the flat model MX
  (TS.ID, ID.AC, ID.DN).

  Method as in Model_Certificates.thy: a model is an interpretation of the locale gsig,
  whose definitions are proved identical to the registry's (K_faithful, K_faithful_more,
  K_faithful_sep, K_faithful_woods, K_faithful_ts_kf, K_faithful_ids, ALL_TOT_faithful). No axioms and no unfinished proofs.

  Limit that applies to every result here (registry decision D2): vacW is a one-world
  approximation of Woods's test, which quantifies over worlds (Woods 2018 fn. 27,
  p. 640). A model of IRR.W is therefore weaker evidence for Woods's proposal than a
  refutation would be evidence against it.
\<close>

section \<open>Further registry entries restated in the locale\<close>

context gsig
begin
definition C3s :: bool where "C3s \<longleftrightarrow> (\<forall>f. adm f) \<and> (\<forall>h. \<exists>f. app f = h)"
definition TRANS_CUT :: bool where
  "TRANS_CUT \<longleftrightarrow> (\<forall>\<Gamma> \<Delta> H q. G \<Gamma> q \<and> \<Delta> \<subseteq> \<Gamma> \<and> (\<forall>p\<in>\<Delta>. G (H p) p)
       \<longrightarrow> G ((\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)) q)"
definition AMALG_INF :: bool where
  "AMALG_INF \<longleftrightarrow> (\<forall>F p. F \<noteq> {} \<and> (\<forall>\<Gamma>\<in>F. G \<Gamma> p) \<longrightarrow> G (\<Union>F) p)"
definition ASYM_ANTI :: bool where
  "ASYM_ANTI \<longleftrightarrow> (\<forall>p q. PG p q \<and> PG q p \<longrightarrow> p = q)"
definition vacM :: "'p set \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "vacM \<Gamma> a c \<longleftrightarrow> a \<in> \<Gamma> \<and> (\<forall>b. T b \<longrightarrow> G (insert b (\<Gamma> - {a})) c)"
definition IRR_MEM :: bool where
  "IRR_MEM \<longleftrightarrow> (\<forall>\<Gamma> c. G \<Gamma> c \<and> c \<in> \<Gamma> \<longrightarrow> vacM \<Gamma> c c)"
definition CONJ_BIN :: bool where
  "CONJ_BIN \<longleftrightarrow> (\<forall>p q. T p \<and> T q \<longrightarrow> G {p, q} (conj p q))"
definition CONJ_INF :: bool where
  "CONJ_INF \<longleftrightarrow> (\<forall>f. adm f \<and> sat f \<noteq> {} \<and> (\<forall>q\<in>sat f. T q) \<longrightarrow> G (sat f) (bigconj f))"
definition DISJ_BOTH :: bool where
  "DISJ_BOTH \<longleftrightarrow> (\<forall>p q. T p \<and> T q \<longrightarrow> G {p, q} (disj p q))"
definition NEG_DN :: bool where
  "NEG_DN \<longleftrightarrow> (\<forall>p. T p \<longrightarrow> G {p} (neg (neg p)))"
definition NEG_DM :: bool where
  "NEG_DM \<longleftrightarrow> (\<forall>p q. (T (neg p) \<longrightarrow> G {neg p} (neg (conj p q)))
     \<and> (T (neg q) \<longrightarrow> G {neg q} (neg (conj p q)))
     \<and> (T (neg p) \<and> T (neg q) \<longrightarrow> G {neg p, neg q} (neg (disj p q))))"
definition TR_NEG :: bool where
  "TR_NEG \<longleftrightarrow> (\<forall>p. T (neg p) \<longrightarrow> G {neg p} (neg (tr p)))"
definition EMPTY_NONE :: bool where "EMPTY_NONE \<longleftrightarrow> (\<forall>p. \<not> G {} p)"
definition TS_KF :: bool where
  "TS_KF \<longleftrightarrow> (\<forall>p. (T (tr p) \<longleftrightarrow> T p) \<and> (T (neg (tr p)) \<longleftrightarrow> T (neg p)))"

definition TS_ID :: bool where "TS_ID \<longleftrightarrow> (\<forall>p. tr p = p)"
definition ID_AC :: bool where
  "ID_AC \<longleftrightarrow> (\<forall>p q r. conj p q = conj q p \<and> disj p q = disj q p
     \<and> conj p (conj q r) = conj (conj p q) r \<and> disj p (disj q r) = disj (disj p q) r
     \<and> conj p p = p \<and> disj p p = p)"
definition ID_DN :: bool where "ID_DN \<longleftrightarrow> (\<forall>p. neg (neg p) = p)"
definition EMPTY_SOME :: bool where "EMPTY_SOME \<longleftrightarrow> (\<exists>p. G {} p)"

text \<open>A way to prove IRR.W in a model whose propositions can be numbered. Present the
  grounds \<Gamma> of a reflexive fact by the variables Var (idx p), p in \<Gamma>, under the
  environment dec, and let Var (idx c) mark c. Then IRR.W holds if, for every reflexive
  fact, the set \<Gamma> with B in place of c grounds c whenever its members are true.\<close>
lemma IRR_W_coded:
  fixes idx :: "'p \<Rightarrow> nat" and dec :: "nat \<Rightarrow> 'p"
  assumes di: "\<And>p. dec (idx p) = p"
    and sub: "\<And>\<Gamma> c B. G \<Gamma> c \<Longrightarrow> c \<in> \<Gamma> \<Longrightarrow> \<forall>q\<in>(\<lambda>p. if p = c then B else p) ` \<Gamma>. T q
                 \<Longrightarrow> G ((\<lambda>p. if p = c then B else p) ` \<Gamma>) c"
  shows IRR_W
  unfolding IRR_W_def
proof (intro allI impI)
  fix \<Gamma> c assume A: "G \<Gamma> c \<and> c \<in> \<Gamma>"
  have inj: "idx p = idx q \<Longrightarrow> p = q" for p q using di by metis
  let ?\<Phi> = "Var ` idx ` \<Gamma>"
  let ?z = "idx c"
  have val: "den (dec(?z:=B)) (Var (idx p)) = (if p = c then B else p)" for B p
    using inj di by auto
  have img: "(\<lambda>\<phi>. den (dec(?z:=B)) \<phi>) ` ?\<Phi> = (\<lambda>p. if p = c then B else p) ` \<Gamma>" for B
    unfolding image_image using val by simp
  have c1: "\<Gamma> = (\<lambda>\<phi>. den (dec(?z:=c)) \<phi>) ` ?\<Phi>" unfolding img by auto
  have c2: "\<exists>\<phi>\<in>?\<Phi>. ?z \<in> fv \<phi>" using A by auto
  have c3: "\<forall>\<phi>\<in>?\<Phi>. \<forall>\<psi>\<in>subf \<phi>. ?z \<notin> fv \<psi> \<longrightarrow> den (dec(?z:=c)) \<psi> \<noteq> c"
  proof (intro ballI impI)
    fix \<phi> \<psi> assume "\<phi> \<in> ?\<Phi>" "\<psi> \<in> subf \<phi>" "?z \<notin> fv \<psi>"
    then obtain p where p: "\<psi> = Var (idx p)" "idx c \<noteq> idx p" by auto
    hence "p \<noteq> c" by blast
    thus "den (dec(?z:=c)) \<psi> \<noteq> c" unfolding p(1) val by simp
  qed
  have c4: "\<forall>B. (\<forall>\<phi>\<in>?\<Phi>. T (den (dec(?z:=B)) \<phi>))
              \<longrightarrow> G ((\<lambda>\<phi>. den (dec(?z:=B)) \<phi>) ` ?\<Phi>) c"
  proof (intro allI impI)
    fix B assume T: "\<forall>\<phi>\<in>?\<Phi>. T (den (dec(?z:=B)) \<phi>)"
    have "\<forall>q\<in>(\<lambda>\<phi>. den (dec(?z:=B)) \<phi>) ` ?\<Phi>. T q" using T by blast
    hence "\<forall>q\<in>(\<lambda>p. if p = c then B else p) ` \<Gamma>. T q" unfolding img .
    thus "G ((\<lambda>\<phi>. den (dec(?z:=B)) \<phi>) ` ?\<Phi>) c" unfolding img using sub A by blast
  qed
  show "vacW c \<Gamma> c" unfolding vacW_def using c1 c2 c3 c4 by blast
qed

text \<open>With ID.AC and ID.DN together, each of the four pairs of N4 is a pair of identical
  propositions, so no model of both reaches N4.\<close>
lemma ids_no_N4: "ID_AC \<Longrightarrow> ID_DN \<Longrightarrow> \<not> N4_pairs"
  unfolding ID_AC_def ID_DN_def N4_pairs_def by metis

text \<open>The counterpart of NonClassical.cl_ts_kf in the locale: with classical negation,
  TS.FULL gives the Kripke-Feferman truth clauses.\<close>
lemma cl_ts_kf: "CL_PROP \<Longrightarrow> TS_FULL \<Longrightarrow> TS_KF"
  unfolding CL_PROP_def TS_FULL_def TS_KF_def by simp
end

lemma K_faithful_ts_kf: "K.TS_KF = TS_KF"
  by (simp add: K_aux K.TS_KF_def TS_KF_def)

lemma K_faithful_ids:
  "K.TS_ID = TS_ID" "K.ID_AC = ID_AC" "K.ID_DN = ID_DN" "K.EMPTY_SOME = EMPTY_SOME"
  by (simp_all add: K_aux K.TS_ID_def TS_ID_def K.ID_AC_def ID_AC_def K.ID_DN_def ID_DN_def
        K.EMPTY_SOME_def EMPTY_SOME_def)

text \<open>ALL.TOT mentions the constant tot, which is not a parameter of the locale gsig and
  occurs in no other entry. ALL_TOT_at states the entry for given interpretations of the
  constants it mentions; at the registry's constants it is ALL.TOT.\<close>
definition ALL_TOT_at ::
  "('p \<Rightarrow> bool) \<Rightarrow> ('f \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow> ('f \<Rightarrow> 'p) \<Rightarrow> ('f \<Rightarrow> bool) \<Rightarrow> ('p set \<Rightarrow> 'p \<Rightarrow> bool)
     \<Rightarrow> ('f \<Rightarrow> 'p) \<Rightarrow> bool" where
  "ALL_TOT_at T' app' allq' adm' G' tot' \<longleftrightarrow>
     (\<forall>f. adm' f \<and> (\<forall>a. T' (app' f a)) \<longrightarrow> T' (tot' f) \<and> G' (insert (tot' f) (range (app' f))) (allq' f))"

lemma ALL_TOT_faithful: "ALL_TOT_at T app allq adm G tot = ALL_TOT"
  unfolding ALL_TOT_at_def ALL_TOT_def inst_def by simp

lemma K_faithful_woods:
  "K.C3s = C3s" "K.TRANS_CUT = TRANS_CUT" "K.AMALG_INF = AMALG_INF" "K.ASYM_ANTI = ASYM_ANTI"
  "K.IRR_MEM = IRR_MEM" "K.CONJ_BIN = CONJ_BIN" "K.CONJ_INF = CONJ_INF" "K.DISJ_BOTH = DISJ_BOTH"
  "K.NEG_DN = NEG_DN" "K.NEG_DM = NEG_DM" "K.TR_NEG = TR_NEG" "K.EMPTY_NONE = EMPTY_NONE"
  by (simp_all add: K_aux fun_eq_iff K.C3s_def C3s_def K.TRANS_CUT_def TRANS_CUT_def
        K.AMALG_INF_def AMALG_INF_def K.ASYM_ANTI_def ASYM_ANTI_def
        K.IRR_MEM_def IRR_MEM_def K.vacM_def vacM_def K.CONJ_BIN_def CONJ_BIN_def
        K.CONJ_INF_def CONJ_INF_def K.DISJ_BOTH_def DISJ_BOTH_def K.NEG_DN_def NEG_DN_def
        K.NEG_DM_def NEG_DM_def K.TR_NEG_def TR_NEG_def K.EMPTY_NONE_def EMPTY_NONE_def)

section \<open>Part 1. What IRR.W demands when truth is classical\<close>

lemma subf_self: "a \<in> subf a" by (cases a) simp_all

text \<open>With CL.PROP, CL.QUANT, TS.FULL and the core clause LAM_CORE, the truth value of
  what a formula denotes depends only on the truth values of what its variables denote.\<close>
lemma classical_truth_env:
  assumes core: "LAM_CORE" and clp: "CL_PROP" and clq: "CL_QUANT" and ts: "TS_FULL"
  shows "(\<forall>n. T (v n) \<longleftrightarrow> T (w n)) \<Longrightarrow> T (den v a) \<longleftrightarrow> T (den w a)"
proof (induction a arbitrary: v w)
  case (Var n) thus ?case by simp
next
  case (Cst n) thus ?case by simp
next
  case (Neg a)
  have "T (den v a) \<longleftrightarrow> T (den w a)" by (rule Neg.IH) (rule Neg.prems)
  thus ?case using clp unfolding CL_PROP_def by simp
next
  case (Conj a b)
  have "T (den v a) \<longleftrightarrow> T (den w a)" "T (den v b) \<longleftrightarrow> T (den w b)"
    by (rule Conj.IH, rule Conj.prems)+
  thus ?case using clp unfolding CL_PROP_def by simp
next
  case (Disj a b)
  have "T (den v a) \<longleftrightarrow> T (den w a)" "T (den v b) \<longleftrightarrow> T (den w b)"
    by (rule Disj.IH, rule Disj.prems)+
  thus ?case using clp unfolding CL_PROP_def by simp
next
  case (Tr a)
  have "T (den v a) \<longleftrightarrow> T (den w a)" by (rule Tr.IH) (rule Tr.prems)
  thus ?case using ts unfolding TS_FULL_def by simp
next
  case (Ex x a)
  have ih: "T (den (v(x:=p)) a) \<longleftrightarrow> T (den (w(x:=p)) a)" for p
    by (rule Ex.IH) (use Ex.prems in simp)
  have "T (exq (lam x a u)) \<longleftrightarrow> (\<exists>p. T (den (u(x:=p)) a))" for u
    using clq core unfolding CL_QUANT_def LAM_CORE_def by simp
  thus ?case using ih by simp
next
  case (All x a)
  have ih: "T (den (v(x:=p)) a) \<longleftrightarrow> T (den (w(x:=p)) a)" for p
    by (rule All.IH) (use All.prems in simp)
  have "T (allq (lam x a u)) \<longleftrightarrow> (\<forall>p. T (den (u(x:=p)) a))" for u
    using clq core unfolding CL_QUANT_def LAM_CORE_def by simp
  thus ?case using ih by simp
next
  case (BigC x a)
  have ih: "T (den (v(x:=p)) a) \<longleftrightarrow> T (den (w(x:=p)) a)" for p
    by (rule BigC.IH) (use BigC.prems in simp)
  have s: "sat (lam x a u) = {p. T (den (u(x:=p)) a)}" for u
    using core unfolding sat_def LAM_CORE_def by simp
  have "T (bigconj (lam x a u)) \<longleftrightarrow> (\<forall>q\<in>sat (lam x a u). T q)" for u
    using clq unfolding CL_QUANT_def by simp
  thus ?case using ih s by simp
qed

text \<open>The demand. Let c be among the members of a full ground \<Gamma> of c. IRR.W gives a
  presentation \<Phi> of \<Gamma> in which every occurrence of c is marked by z. Then some member
  \<phi> of \<Phi> has z free and denotes c when z denotes c, and for EVERY truth B the set got
  by putting B for c is a full ground of c. The side condition of vacW, that the
  modified grounds are true, is met by every truth, because truth is compositional.
  So the content of c plays no role in the fact that c helps ground c, which is what
  Woods asks (p. 640); and every truth B, in the place \<phi> marks, helps ground c.\<close>
theorem woods_classical:
  assumes fact: "FACT" and core: "LAM_CORE" and clp: "CL_PROP" and clq: "CL_QUANT"
      and ts: "TS_FULL" and irr: "IRR_W" and g: "G \<Gamma> c" and mem: "c \<in> \<Gamma>"
  shows "\<exists>\<Phi> v z \<phi>. \<phi> \<in> \<Phi> \<and> z \<in> fv \<phi> \<and> den (v(z:=c)) \<phi> = c
           \<and> \<Gamma> = (\<lambda>\<psi>. den (v(z:=c)) \<psi>) ` \<Phi>
           \<and> (\<forall>B. T B \<longrightarrow> G ((\<lambda>\<psi>. den (v(z:=B)) \<psi>) ` \<Phi>) c \<and> PG (den (v(z:=B)) \<phi>) c)"
proof -
  have "vacW c \<Gamma> c" using irr g mem unfolding IRR_W_def by blast
  then obtain \<Phi> v z where
        pres: "\<Gamma> = (\<lambda>\<psi>. den (v(z:=c)) \<psi>) ` \<Phi>"
    and mark: "\<forall>\<psi>\<in>\<Phi>. \<forall>\<chi>\<in>subf \<psi>. z \<notin> fv \<chi> \<longrightarrow> den (v(z:=c)) \<chi> \<noteq> c"
    and sub: "\<forall>B. (\<forall>\<psi>\<in>\<Phi>. T (den (v(z:=B)) \<psi>)) \<longrightarrow> G ((\<lambda>\<psi>. den (v(z:=B)) \<psi>) ` \<Phi>) c"
    unfolding vacW_def by blast
  obtain \<phi> where phi: "\<phi> \<in> \<Phi>" "den (v(z:=c)) \<phi> = c" using mem pres by auto
  have zf: "z \<in> fv \<phi>" using mark phi subf_self by blast
  have Tc: "T c" using fact g unfolding FACT_def by blast
  have Tg: "\<forall>\<psi>\<in>\<Phi>. T (den (v(z:=c)) \<psi>)" using fact g pres unfolding FACT_def by blast
  have all: "G ((\<lambda>\<psi>. den (v(z:=B)) \<psi>) ` \<Phi>) c \<and> PG (den (v(z:=B)) \<phi>) c" if B: "T B" for B
  proof -
    have env: "\<forall>n. T ((v(z:=B)) n) \<longleftrightarrow> T ((v(z:=c)) n)" using B Tc by simp
    have "T (den (v(z:=B)) \<psi>) \<longleftrightarrow> T (den (v(z:=c)) \<psi>)" for \<psi>
      by (rule classical_truth_env[OF core clp clq ts env])
    hence "\<forall>\<psi>\<in>\<Phi>. T (den (v(z:=B)) \<psi>)" using Tg by simp
    hence gb: "G ((\<lambda>\<psi>. den (v(z:=B)) \<psi>) ` \<Phi>) c" using sub by blast
    moreover have "den (v(z:=B)) \<phi> \<in> (\<lambda>\<psi>. den (v(z:=B)) \<psi>) ` \<Phi>" using phi(1) by blast
    ultimately show ?thesis unfolding PG_def by blast
  qed
  show ?thesis using phi zf pres all by blast
qed

text \<open>If c is not what any formula denotes that contains the marked variable properly,
  the marked member is the variable itself, and every truth helps ground c. The
  hypothesis holds where propositions are as fine as the formulas that present them; it
  fails in the models below, which identify many propositions.\<close>
corollary woods_classical_every_truth:
  assumes "FACT" "LAM_CORE" "CL_PROP" "CL_QUANT" "TS_FULL" "IRR_W" and pg: "PG c c"
      and wf: "\<forall>\<phi> v z. z \<in> fv \<phi> \<and> den (v(z:=c)) \<phi> = c \<longrightarrow> \<phi> = Var z"
  shows "\<forall>B. T B \<longrightarrow> PG B c"
proof -
  obtain \<Gamma> where g: "G \<Gamma> c" "c \<in> \<Gamma>" using pg unfolding PG_def by blast
  obtain \<Phi> v z \<phi> where p: "z \<in> fv \<phi>" "den (v(z:=c)) \<phi> = c"
      "\<forall>B. T B \<longrightarrow> PG (den (v(z:=B)) \<phi>) c"
    using woods_classical[OF assms(1-6) g] by blast
  have "\<phi> = Var z" using wf p(1,2) by blast
  thus ?thesis using p(3) by simp
qed

subsection \<open>The self-grounds that the puzzle packages force, without any irreflexivity\<close>

text \<open>Kr\"amer's case. Every truth helps ground \<exists>p p, so with TRANS.P every truth helps
  ground whatever \<exists>p p helps ground. This part of the models below is forced.\<close>
lemma kramer_cluster:
  assumes ad: "adm f_id" and beta: "BETA_ID" and ex: "EX_PART" and tra: "TRANS_P"
      and p: "T p" and r: "PG (exq f_id) r"
  shows "PG p r"
proof -
  have "app f_id p = p" using BETA_apps(1)[OF beta] .
  hence "PG p (exq f_id)" using ex ad p unfolding EX_PART_def by metis
  thus ?thesis using tra r unfolding TRANS_P_def by blast
qed

text \<open>Fine's sentence-position universal case (the instance of Woods's Objection 5, p. 645):
  s = \<forall>p(p \<or> \<not>p) and its own instance d = s \<or> \<not>s help ground each other.\<close>
lemma fine_sp_circle:
  assumes ad: "adm f_em" and beta: "BETA_ID" and cl: "CL_PROP" and clq: "CL_QUANT"
      and ug: "ALL_PART" and dg: "DISJ_PART"
  shows "T (allq f_em)"
    and "PG (allq f_em) (disj (allq f_em) (neg (allq f_em)))"
    and "PG (disj (allq f_em) (neg (allq f_em))) (allq f_em)"
proof -
  let ?s = "allq f_em"
  have app: "\<forall>p. app f_em p = disj p (neg p)" using BETA_apps(3)[OF beta] by simp
  have em: "T (disj x (neg x))" for x using cl unfolding CL_PROP_def by blast
  have vals: "\<forall>b. T (app f_em b)" using app em by simp
  thus Ts: "T ?s" using clq unfolding CL_QUANT_def by blast
  show "PG ?s (disj ?s (neg ?s))" using dg Ts unfolding DISJ_PART_def by blast
  have "PG (app f_em ?s) ?s" using ug ad vals unfolding ALL_PART_def by blast
  thus "PG (disj ?s (neg ?s)) ?s" using app by simp
qed

text \<open>Every truth B helps ground \<forall>p(p \<or> \<not>p): B is a true disjunct of the instance
  B \<or> \<not>B. This needs no irreflexivity principle. So at the level of partial ground
  the universal truth is replaceable by any truth among its own partial grounds, as
  Woods's reply to Objection 5 says (p. 645). What IRR.W adds is the same for FULL grounds
  (woods_classical): the set got by the replacement must itself be a full ground.\<close>
theorem fine_sp_every_truth:
  assumes ad: "adm f_em" and beta: "BETA_ID" and cl: "CL_PROP" and clq: "CL_QUANT"
      and ug: "ALL_PART" and dg: "DISJ_PART" and tra: "TRANS_P" and B: "T B"
  shows "PG B (allq f_em)"
proof -
  have app: "\<forall>p. app f_em p = disj p (neg p)" using BETA_apps(3)[OF beta] by simp
  have em: "T (disj x (neg x))" for x using cl unfolding CL_PROP_def by blast
  have vals: "\<forall>b. T (app f_em b)" using app em by simp
  have "PG (app f_em B) (allq f_em)" using ug ad vals unfolding ALL_PART_def by blast
  hence "PG (disj B (neg B)) (allq f_em)" using app by simp
  moreover have "PG B (disj B (neg B))" using dg B unfolding DISJ_PART_def by blast
  ultimately show ?thesis using tra unfolding TRANS_P_def by blast
qed

text \<open>Woods's Objection 3 (p. 643) and his reply, from the registry's entries. Let g be
  the propositional function p \<or> A, for an atom A. Then \<exists>p(p \<or> A) is true, helps ground
  itself, and every truth B helps ground it, which is the fact Woods's reply rests on
  ("B < \<exists>p(p \<or> A)" for every B; here for every true B, since ground is factive).\<close>
theorem woods_obj3:
  assumes ad: "adm (lam 0 (Disj (Var 0) (Cst n)) v)" and beta: "BETA_ID" and cl: "CL_PROP"
      and clq: "CL_QUANT" and ex: "EX_PART" and dg: "DISJ_PART" and tra: "TRANS_P"
  shows "T (exq (lam 0 (Disj (Var 0) (Cst n)) v))"
    and "\<forall>B. T B \<longrightarrow> PG B (exq (lam 0 (Disj (Var 0) (Cst n)) v))"
    and "PG (exq (lam 0 (Disj (Var 0) (Cst n)) v)) (exq (lam 0 (Disj (Var 0) (Cst n)) v))"
proof -
  let ?g = "lam 0 (Disj (Var 0) (Cst n)) v"
  have app: "app ?g p = disj p (atom n)" for p using beta unfolding BETA_ID_def by simp
  have dj: "T p \<Longrightarrow> T (disj p (atom n))" for p using cl unfolding CL_PROP_def by blast
  obtain t where t: "T t" using CL_QUANT_truth[OF clq] by blast
  have "T (app ?g t)" using app dj t by simp
  thus Te: "T (exq ?g)" using clq unfolding CL_QUANT_def by blast
  show all: "\<forall>B. T B \<longrightarrow> PG B (exq ?g)"
  proof (intro allI impI)
    fix B assume B: "T B"
    have "T (app ?g B)" using app dj B by simp
    hence "PG (app ?g B) (exq ?g)" using ex ad unfolding EX_PART_def by blast
    hence "PG (disj B (atom n)) (exq ?g)" using app by simp
    moreover have "PG B (disj B (atom n))" using dg B unfolding DISJ_PART_def by blast
    ultimately show "PG B (exq ?g)" using tra unfolding TRANS_P_def by blast
  qed
  show "PG (exq ?g) (exq ?g)" using all Te by blast
qed

text \<open>Objection 3 as a puzzle: with strict irreflexivity the package is refuted. (At C2
  it also contains Kr\"amer's package; this proof does not use f_id.)\<close>
theorem woods_obj3_refuted:
  assumes "C2 1" "BETA_ID" "CL_PROP" "CL_QUANT" "EX_PART" "DISJ_PART" "TRANS_P" "IRR_F"
  shows False
proof -
  have "lvl (Disj (Var 0) (Cst 0)) \<le> 1" by simp
  hence ad: "adm (lam 0 (Disj (Var 0) (Cst 0)) e0)" using assms(1) unfolding C2_def by blast
  have "PG (exq (lam 0 (Disj (Var 0) (Cst 0)) e0)) (exq (lam 0 (Disj (Var 0) (Cst 0)) e0))"
    using woods_obj3(3)[OF ad assms(2-7)] .
  thus False using assms(8) unfolding IRR_F_def PG_def by blast
qed

subsection \<open>Entries that make every truth help ground itself\<close>

text \<open>With the identities ID.AC every truth p is p \<or> p, and with TS.ID it is its own
  truth ascription. The disjunction or truth entry then makes every truth help ground
  itself, so IRR.W must be met at every truth, not only on the circles of the puzzles
  (and IRR.F is refuted outright).\<close>
lemma id_ac_all_reflexive: "ID_AC \<Longrightarrow> DISJ_PART \<Longrightarrow> T p \<Longrightarrow> PG p p"
  unfolding ID_AC_def DISJ_PART_def by metis
lemma ts_id_all_reflexive: "TS_ID \<Longrightarrow> TR_PART \<Longrightarrow> T p \<Longrightarrow> PG p p"
  unfolding TS_ID_def TR_PART_def by metis

text \<open>With ID.AC and ID.DN together, each of the four pairs of N4 is a pair of identical
  propositions, so no model of both reaches N4.\<close>
lemma id_ac_dn_no_N4: "ID_AC \<Longrightarrow> ID_DN \<Longrightarrow> \<not> N4_pairs"
  unfolding ID_AC_def ID_DN_def N4_pairs_def by metis

subsection \<open>Controls: asymmetry still refutes each package\<close>

text \<open>IRR.W replaces IRR.F only. ASYM.P implies IRR.F (Order.ASYM_P_IRR_F), so adding it
  to a package with IRR.W brings the puzzle back.\<close>
theorem kramer_W_asym:
  assumes "W_ID" "BETA_ID" "CL_QUANT" "EX_PART" "ASYM_P" shows False
  using kramer_W[OF assms(1-4) ASYM_P_IRR_F[OF assms(5)]] .

theorem fine_universal_W_asym:
  assumes "W_TEM" "BETA_ID" "CL_PROP" "CL_QUANT" "TS_FULL" "ALL_PART" "DISJ_PART" "TR_PART"
          "TRANS_P" "ASYM_P"
  shows False
  using fine_universal_W[OF assms(1-9) ASYM_P_IRR_F[OF assms(10)]] .

theorem fine_particular_props_W_asym:
  assumes "W_TEM" "BETA_ID" "CL_PROP" "CL_QUANT" "TS_FULL" "EX_PART" "DISJ_PART" "TR_PART"
          "TRANS_P" "ASYM_P"
  shows False
  using fine_particular_props_W[OF assms(1-9) ASYM_P_IRR_F[OF assms(10)]] .

theorem fine_universal_sp_W_asym:
  assumes "W_EM" "BETA_ID" "CL_PROP" "CL_QUANT" "ALL_PART" "DISJ_PART" "TRANS_P" "ASYM_P"
  shows False
  using fine_universal_sp_W[OF assms(1-7) ASYM_P_IRR_F[OF assms(8)]] .

theorem woods_obj3_asym:
  assumes "C2 1" "BETA_ID" "CL_PROP" "CL_QUANT" "EX_PART" "DISJ_PART" "TRANS_P" "ASYM_P"
  shows False
  using woods_obj3_refuted[OF assms(1-7) ASYM_P_IRR_F[OF assms(8)]] .

text \<open>With ASYM.ANTI in place of ASYM.P (Woods's weakening of asymmetry), the package
  forces the universal truth and its own instance to be one proposition.\<close>
theorem fine_sp_anti_collapse:
  assumes "W_EM" "BETA_ID" "CL_PROP" "CL_QUANT" "ALL_PART" "DISJ_PART" "ASYM_ANTI"
  shows "disj (allq f_em) (neg (allq f_em)) = allq f_em"
proof -
  have ad: "adm f_em" using assms(1) unfolding W_EM_def .
  show ?thesis
    using fine_sp_circle(2,3)[OF ad assms(2-6)] assms(7) unfolding ASYM_ANTI_def by blast
qed

section \<open>Part 2. Model MW: the target P.WOODS.CHECK\<close>

text \<open>
  P.WOODS.CHECK = C1, BETA.ID, CL.QUANT, EX.FULL, IRR.W, TRANS.P. The model is model MG
  of Restricted_Models.thy with two changes. Existential propositions get the top
  rank R4 (universal and conjunctive ones stay at R3), and a true proposition of rank
  R4 is fully grounded by every truth on its own. So EX.FULL holds without restriction.
  The only reflexive grounding fact is that (True, R4), the one true existential
  proposition, grounds itself, and it is vacuous in Woods's sense because every truth
  grounds it. Truth ascription keeps the truth value, so TS.FULL holds too.
\<close>

fun trW :: "pg \<Rightarrow> pg" where
  "trW (t, R0) = (t, R1)"
| "trW (t, R1) = (t, R2)"
| "trW (t, R2) = (t, R2)"
| "trW (t, R3) = (t, R3)"
| "trW (t, R4) = (t, R4)"

primrec dW :: "(nat \<Rightarrow> pg) \<Rightarrow> fm \<Rightarrow> pg" where
  "dW v (Var n) = v n"
| "dW v (Cst n) = (True, R0)"
| "dW v (Neg a) = ngG (dW v a)"
| "dW v (Conj a b) = cjG (dW v a) (dW v b)"
| "dW v (Disj a b) = djG (dW v a) (dW v b)"
| "dW v (Tr a) = trW (dW v a)"
| "dW v (Ex x a) = ((\<exists>p. fst (dW (v(x:=p)) a)), R4)"
| "dW v (All x a) = ((\<forall>p. fst (dW (v(x:=p)) a)), R3)"
| "dW v (BigC x a) = ((\<forall>p. fst (dW (v(x:=p)) a) \<longrightarrow> fst p), R3)"

definition lamW :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> pg) \<Rightarrow> pg \<Rightarrow> pg" where
  "lamW x a v = (\<lambda>p. dW (v(x:=p)) a)"
definition exqW :: "(pg \<Rightarrow> pg) \<Rightarrow> pg" where "exqW f = ((\<exists>p. fst (f p)), R4)"
definition allqW :: "(pg \<Rightarrow> pg) \<Rightarrow> pg" where "allqW f = ((\<forall>p. fst (f p)), R3)"
definition bigW :: "(pg \<Rightarrow> pg) \<Rightarrow> pg" where "bigW f = ((\<forall>p. fst (f p) \<longrightarrow> fst p), R3)"

definition admW :: "(pg \<Rightarrow> pg) \<Rightarrow> bool" where
  "admW f \<longleftrightarrow> f \<in> {(\<lambda>p. p), trW, (\<lambda>p. djG p (ngG p)), (\<lambda>p. djG (trW p) (ngG (trW p)))}"

definition GW :: "pg set \<Rightarrow> pg \<Rightarrow> bool" where
  "GW \<Gamma> q \<longleftrightarrow> (\<exists>p. \<Gamma> = {p} \<and> fst p \<and> fst q \<and> (rn (snd p) < rn (snd q) \<or> snd q = R4))"

interpretation MW: gsig "fst :: pg \<Rightarrow> bool" "\<lambda>_. (True, R0)" ngG cjG djG trW
  "\<lambda>(f :: pg \<Rightarrow> pg) p. f p" exqW allqW bigW lamW admW GW "\<lambda>_. (True, R0)" "(True, R0)" .

lemma quantW:
  "exqW (lamW x a v) = ((\<exists>p. fst (dW (v(x:=p)) a)), R4)"
  "allqW (lamW x a v) = ((\<forall>p. fst (dW (v(x:=p)) a)), R3)"
  "bigW (lamW x a v) = ((\<forall>p. fst (dW (v(x:=p)) a) \<longrightarrow> fst p), R3)"
  by (simp_all add: lamW_def exqW_def allqW_def bigW_def)

lemma MW_den: "MW.den = dW"
proof (intro ext)
  fix v a show "MW.den v a = dW v a"
    by (induction a) (simp_all add: quantW)
qed

lemma dW_fv: "(\<forall>y\<in>fv a. v y = w y) \<Longrightarrow> dW v a = dW w a"
proof (induct a arbitrary: v w)
  case (Ex x a)
  have "\<And>p. dW (v(x:=p)) a = dW (w(x:=p)) a"
    by (rule Ex.hyps) (use Ex.prems in auto)
  then show ?case by simp
next
  case (All x a)
  have "\<And>p. dW (v(x:=p)) a = dW (w(x:=p)) a"
    by (rule All.hyps) (use All.prems in auto)
  then show ?case by simp
next
  case (BigC x a)
  have "\<And>p. dW (v(x:=p)) a = dW (w(x:=p)) a"
    by (rule BigC.hyps) (use BigC.prems in auto)
  then show ?case by simp
next
  case (Neg a)
  have "dW v a = dW w a" by (rule Neg.hyps) (use Neg.prems in auto)
  then show ?case by simp
next
  case (Tr a)
  have "dW v a = dW w a" by (rule Tr.hyps) (use Tr.prems in auto)
  then show ?case by simp
next
  case (Conj a b)
  have "dW v a = dW w a" by (rule Conj.hyps(1)) (use Conj.prems in auto)
  moreover have "dW v b = dW w b" by (rule Conj.hyps(2)) (use Conj.prems in auto)
  ultimately show ?case by simp
next
  case (Disj a b)
  have "dW v a = dW w a" by (rule Disj.hyps(1)) (use Disj.prems in auto)
  moreover have "dW v b = dW w b" by (rule Disj.hyps(2)) (use Disj.prems in auto)
  ultimately show ?case by simp
qed simp_all

lemma lamW_fv: "\<forall>y\<in>fv a - {x}. v y = w y \<Longrightarrow> lamW x a v = lamW x a w"
  unfolding lamW_def by (intro ext dW_fv) auto

lemma trW_fst: "fst (trW p) = fst p"
  by (cases p rule: trW.cases) auto

lemma MW_PG: "MW.PG p q \<longleftrightarrow> fst p \<and> fst q \<and> (rn (snd p) < rn (snd q) \<or> snd q = R4)"
proof
  assume "MW.PG p q"
  thus "fst p \<and> fst q \<and> (rn (snd p) < rn (snd q) \<or> snd q = R4)"
    unfolding MW.PG_def GW_def by auto
next
  assume A: "fst p \<and> fst q \<and> (rn (snd p) < rn (snd q) \<or> snd q = R4)"
  have "p \<in> {p} \<and> GW {p} q" using A unfolding GW_def by blast
  thus "MW.PG p q" unfolding MW.PG_def by (rule exI)
qed

lemma rn_top: "rn r \<le> 4" by (cases r) simp_all
lemma rn_R4: "rn r = 4 \<longleftrightarrow> r = R4" by (cases r) simp_all

lemma MW_core: "MW.FACT" "MW.LAM_CORE" "MW.N1" "MW.N2" "MW.N5_chain"
  and MW_N4: "MW.N4_pair (True, R1) (ngG (ngG (True, R1)))"
proof -
  show "MW.FACT" by (auto simp: MW.FACT_def GW_def)
  show "MW.LAM_CORE" unfolding MW.LAM_CORE_def MW_den using lamW_fv by (simp add: lamW_def)
  have g: "GW {(True, R0)} (True, R1)" by (simp add: GW_def)
  show "MW.N1" unfolding MW.N1_def using g by blast
  thus "MW.N2" unfolding MW.N2_def
    by (intro conjI exI[of _ "(True, R0)"] exI[of _ "(True, R1)"] exI[of _ "(True, R2)"]) simp_all
  show "MW.N5_chain" unfolding MW.N5_chain_def
    by (intro exI[of _ "(True, R0)"] exI[of _ "(True, R1)"] exI[of _ "(True, R2)"]
          exI[of _ "(True, R3)"]) (simp add: MW_PG)
  have "{(True, R0)} \<in> {\<Gamma>. GW \<Gamma> (True, R1)}" "{(True, R0)} \<notin> {\<Gamma>. GW \<Gamma> (True, R0)}"
    by (auto simp: GW_def)
  thus "MW.N4_pair (True, R1) (ngG (ngG (True, R1)))"
    unfolding MW.N4_pair_def by (auto simp: ngG_def)
qed

lemma MW_N4s: "MW.N4_pairs" using MW.N4_dn[OF MW_N4] .

lemma MW_C1: "MW.C1"
  by (simp add: MW.C1_def admW_def MW.f_id_def MW.f_tr_def MW.f_em_def MW.f_tem_def lamW_def)

lemma MW_BETA_ID: "MW.BETA_ID"
  by (simp add: MW.BETA_ID_def MW_den lamW_def)

lemma MW_classical: "MW.CL_PROP" "MW.CL_QUANT" "MW.TS_FULL"
  by (simp_all add: MW.CL_PROP_def MW.CL_QUANT_def MW.TS_FULL_def ngG_def cjG_def djG_def
        exqW_def allqW_def bigW_def MW.sat_def trW_fst)

lemma MW_EX_FULL: "MW.EX_FULL"
  unfolding MW.EX_FULL_def
proof (intro allI impI)
  fix f a assume A: "admW f \<and> fst (f a)"
  hence "\<exists>p. fst (f p)" by blast
  hence e: "exqW f = (True, R4)" unfolding exqW_def by simp
  show "GW {f a} (exqW f)" unfolding e GW_def using A by simp
qed

lemma MW_TRANS_P: "MW.TRANS_P"
  unfolding MW.TRANS_P_def MW_PG using rn_top rn_R4
  by (metis le_antisym less_imp_le_nat less_trans not_less)

text \<open>IRR.W. A reflexive fact has the form: {c} grounds c, with c true of rank R4. Present
  the grounds by the one formula Var 0. Putting any truth B for c gives {B}, which
  grounds c.\<close>
lemma MW_IRR_W: "MW.IRR_W"
  unfolding MW.IRR_W_def
proof (intro allI impI)
  fix \<Gamma> c assume A: "GW \<Gamma> c \<and> c \<in> \<Gamma>"
  hence g: "\<Gamma> = {c}" "fst c" "snd c = R4" unfolding GW_def by auto
  have all: "GW {B} c" if "fst B" for B unfolding GW_def using that g by simp
  have "\<Gamma> = (\<lambda>\<phi>. MW.den ((\<lambda>_. c)(0:=c)) \<phi>) ` {Var 0}
      \<and> (\<exists>\<phi>\<in>{Var 0}. (0::nat) \<in> fv \<phi>)
      \<and> (\<forall>\<phi>\<in>{Var 0}. \<forall>\<psi>\<in>subf \<phi>. (0::nat) \<notin> fv \<psi> \<longrightarrow> MW.den ((\<lambda>_. c)(0:=c)) \<psi> \<noteq> c)
      \<and> (\<forall>B. (\<forall>\<phi>\<in>{Var 0}. fst (MW.den ((\<lambda>_. c)(0:=B)) \<phi>))
            \<longrightarrow> GW ((\<lambda>\<phi>. MW.den ((\<lambda>_. c)(0:=B)) \<phi>) ` {Var 0}) c)"
    using g(1) all by simp
  thus "MW.vacW c \<Gamma> c" unfolding MW.vacW_def by blast
qed

text \<open>The reflexive fact is there: strict irreflexivity and asymmetry fail, as they must
  (kramer_W). Woods's antisymmetry holds.\<close>
lemma MW_reflexive: "GW {(True, R4)} (True, R4)" "\<not> MW.IRR_F" "\<not> MW.ASYM_P"
proof -
  show g: "GW {(True, R4)} (True, R4)" by (simp add: GW_def)
  show "\<not> MW.IRR_F" unfolding MW.IRR_F_def using g by blast
  have "MW.PG (True, R4) (True, R4)" by (simp add: MW_PG)
  thus "\<not> MW.ASYM_P" unfolding MW.ASYM_P_def by blast
qed

lemma MW_ASYM_ANTI: "MW.ASYM_ANTI"
  unfolding MW.ASYM_ANTI_def MW_PG
proof (intro allI impI)
  fix p q :: pg
  assume A: "(fst p \<and> fst q \<and> (rn (snd p) < rn (snd q) \<or> snd q = R4))
           \<and> (fst q \<and> fst p \<and> (rn (snd q) < rn (snd p) \<or> snd p = R4))"
  have "snd p = R4 \<and> snd q = R4" using A rn_top[of "snd p"] rn_top[of "snd q"] rn_R4
    by (metis le_antisym less_imp_le_nat not_less)
  thus "p = q" using A by (simp add: prod_eq_iff)
qed

text \<open>N3 for EX.FULL, the one introduction entry of the target: the true instance
  (True, R0) of the identity function grounds the distinct proposition \<exists>p p = (True, R4).\<close>
lemma MW_N3:
  "admW (\<lambda>p. p) \<and> MW.f_id = (\<lambda>p. p) \<and> exqW (\<lambda>p. p) = (True, R4)
   \<and> GW {(True, R0)} (True, R4) \<and> (True, R4) \<notin> {(True, R0) :: pg}"
  by (auto simp: admW_def MW.f_id_def lamW_def exqW_def GW_def)

theorem MW_package:
  "MW.FACT \<and> MW.LAM_CORE \<and> MW.C1 \<and> MW.BETA_ID \<and> MW.CL_PROP \<and> MW.CL_QUANT \<and> MW.TS_FULL
   \<and> MW.EX_FULL \<and> MW.IRR_W \<and> MW.TRANS_P \<and> MW.ASYM_ANTI
   \<and> MW.N1 \<and> MW.N2 \<and> MW.N4_pairs \<and> MW.N5_chain \<and> \<not> MW.IRR_F \<and> \<not> MW.ASYM_P"
  using MW_core MW_N4s MW_C1 MW_BETA_ID MW_classical MW_EX_FULL MW_IRR_W MW_TRANS_P
        MW_ASYM_ANTI MW_reflexive by blast

section \<open>Part 3. Model MV: the Kr\"amer and Fine targets with IRR.W for IRR.F\<close>

text \<open>
  A proposition is a truth value with a level. Levels come in two tiers: L n, the
  ordinary tier, and Top n, the tier of the propositions that help ground themselves.
  Every connective and the truth ascription give a level one above the highest level
  of their arguments, and stay in the tier Top once an argument is there. Every
  quantified proposition (existential, universal, arbitrary conjunction) has level
  Top 0. A non-empty set of truths is a full ground of a truth q when q is in the tier
  Top, or when every member has an ordinary level below the ordinary level of q.

  So on the ordinary tier ground is a strict order by level, and every true proposition
  of the tier Top is fully grounded by every non-empty set of truths. That is what makes
  each reflexive fact vacuous. Part of it is forced: by kramer_cluster every truth helps
  ground whatever \<exists>p p helps ground, and by woods_classical a truth that helps ground
  itself has grounds with any truth in its place.

  Unlike MW, the model keeps the propositions of each puzzle apart: \<forall>p(p \<or> \<not>p) is
  (True, Top 0), its own instance is (True, Top 2), and the truth ascription to it is
  (True, Top 1) (MV_circles). Propositional functions are all functions on
  propositions and every one is admissible, so C3s holds.
\<close>

datatype lv = L nat | Top nat

fun upV :: "lv \<Rightarrow> lv" where
  "upV (L n) = L (Suc n)" | "upV (Top k) = Top (Suc k)"
fun mxV :: "lv \<Rightarrow> lv \<Rightarrow> lv" where
  "mxV (L m) (L n) = L (max m n)"
| "mxV (Top j) (Top k) = Top (max j k)"
| "mxV (Top j) (L n) = Top j"
| "mxV (L m) (Top k) = Top k"
fun blw :: "lv \<Rightarrow> lv \<Rightarrow> bool" where
  "blw a (Top k) = True"
| "blw (L m) (L n) = (m < n)"
| "blw (Top j) (L n) = False"

lemma blw_up: "blw a (upV a)" by (cases a) simp_all
lemma blw_up2: "blw a (upV (upV a))" by (cases a) simp_all
lemma blw_mx1: "blw a (upV (mxV a b))" by (cases a; cases b) simp_all
lemma blw_mx2: "blw b (upV (mxV a b))" by (cases a; cases b) simp_all
lemma blw_mx1': "blw (upV a) (upV (upV (mxV a b)))" by (cases a; cases b) simp_all
lemma blw_mx2': "blw (upV b) (upV (upV (mxV a b)))" by (cases a; cases b) simp_all
lemma blw_trans: "blw a b \<Longrightarrow> blw b c \<Longrightarrow> blw a c" by (cases a; cases b; cases c) simp_all
lemma blw_refl: "blw a a \<Longrightarrow> \<exists>k. a = Top k" by (cases a) simp_all

type_synonym pv = "bool \<times> lv"

definition ngV :: "pv \<Rightarrow> pv" where "ngV p = (\<not> fst p, upV (snd p))"
definition cjV :: "pv \<Rightarrow> pv \<Rightarrow> pv" where "cjV p q = (fst p \<and> fst q, upV (mxV (snd p) (snd q)))"
definition djV :: "pv \<Rightarrow> pv \<Rightarrow> pv" where "djV p q = (fst p \<or> fst q, upV (mxV (snd p) (snd q)))"
definition trV :: "pv \<Rightarrow> pv" where "trV p = (fst p, upV (snd p))"

primrec dV :: "(nat \<Rightarrow> pv) \<Rightarrow> fm \<Rightarrow> pv" where
  "dV v (Var n) = v n"
| "dV v (Cst n) = (True, L 0)"
| "dV v (Neg a) = ngV (dV v a)"
| "dV v (Conj a b) = cjV (dV v a) (dV v b)"
| "dV v (Disj a b) = djV (dV v a) (dV v b)"
| "dV v (Tr a) = trV (dV v a)"
| "dV v (Ex x a) = ((\<exists>p. fst (dV (v(x:=p)) a)), Top 0)"
| "dV v (All x a) = ((\<forall>p. fst (dV (v(x:=p)) a)), Top 0)"
| "dV v (BigC x a) = ((\<forall>p. fst (dV (v(x:=p)) a) \<longrightarrow> fst p), Top 0)"

definition lamV :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> pv) \<Rightarrow> pv \<Rightarrow> pv" where
  "lamV x a v = (\<lambda>p. dV (v(x:=p)) a)"
definition exqV :: "(pv \<Rightarrow> pv) \<Rightarrow> pv" where "exqV f = ((\<exists>p. fst (f p)), Top 0)"
definition allqV :: "(pv \<Rightarrow> pv) \<Rightarrow> pv" where "allqV f = ((\<forall>p. fst (f p)), Top 0)"
definition bigV :: "(pv \<Rightarrow> pv) \<Rightarrow> pv" where "bigV f = ((\<forall>p. fst (f p) \<longrightarrow> fst p), Top 0)"

definition GV :: "pv set \<Rightarrow> pv \<Rightarrow> bool" where
  "GV \<Gamma> q \<longleftrightarrow> \<Gamma> \<noteq> {} \<and> fst q \<and> (\<forall>p\<in>\<Gamma>. fst p \<and> blw (snd p) (snd q))"

interpretation MV: gsig "fst :: pv \<Rightarrow> bool" "\<lambda>_. (True, L 0)" ngV cjV djV trV
  "\<lambda>(f :: pv \<Rightarrow> pv) p. f p" exqV allqV bigV lamV "\<lambda>_. True" GV "\<lambda>_. (True, L 0)" "(True, L 0)" .

lemma quantV:
  "exqV (lamV x a v) = ((\<exists>p. fst (dV (v(x:=p)) a)), Top 0)"
  "allqV (lamV x a v) = ((\<forall>p. fst (dV (v(x:=p)) a)), Top 0)"
  "bigV (lamV x a v) = ((\<forall>p. fst (dV (v(x:=p)) a) \<longrightarrow> fst p), Top 0)"
  by (simp_all add: lamV_def exqV_def allqV_def bigV_def)

lemma MV_den: "MV.den = dV"
proof (intro ext)
  fix v a show "MV.den v a = dV v a"
    by (induction a) (simp_all add: quantV)
qed

lemma dV_fv: "(\<forall>y\<in>fv a. v y = w y) \<Longrightarrow> dV v a = dV w a"
proof (induct a arbitrary: v w)
  case (Ex x a)
  have "\<And>p. dV (v(x:=p)) a = dV (w(x:=p)) a"
    by (rule Ex.hyps) (use Ex.prems in auto)
  then show ?case by simp
next
  case (All x a)
  have "\<And>p. dV (v(x:=p)) a = dV (w(x:=p)) a"
    by (rule All.hyps) (use All.prems in auto)
  then show ?case by simp
next
  case (BigC x a)
  have "\<And>p. dV (v(x:=p)) a = dV (w(x:=p)) a"
    by (rule BigC.hyps) (use BigC.prems in auto)
  then show ?case by simp
next
  case (Neg a)
  have "dV v a = dV w a" by (rule Neg.hyps) (use Neg.prems in auto)
  then show ?case by simp
next
  case (Tr a)
  have "dV v a = dV w a" by (rule Tr.hyps) (use Tr.prems in auto)
  then show ?case by simp
next
  case (Conj a b)
  have "dV v a = dV w a" by (rule Conj.hyps(1)) (use Conj.prems in auto)
  moreover have "dV v b = dV w b" by (rule Conj.hyps(2)) (use Conj.prems in auto)
  ultimately show ?case by simp
next
  case (Disj a b)
  have "dV v a = dV w a" by (rule Disj.hyps(1)) (use Disj.prems in auto)
  moreover have "dV v b = dV w b" by (rule Disj.hyps(2)) (use Disj.prems in auto)
  ultimately show ?case by simp
qed simp_all

lemma lamV_fv: "\<forall>y\<in>fv a - {x}. v y = w y \<Longrightarrow> lamV x a v = lamV x a w"
  unfolding lamV_def by (intro ext dV_fv) auto

lemma GV_single: "GV {p} q \<longleftrightarrow> fst p \<and> fst q \<and> blw (snd p) (snd q)"
  unfolding GV_def by auto

lemma MV_PG: "MV.PG p q \<longleftrightarrow> fst p \<and> fst q \<and> blw (snd p) (snd q)"
proof
  assume "MV.PG p q"
  thus "fst p \<and> fst q \<and> blw (snd p) (snd q)" unfolding MV.PG_def GV_def by auto
next
  assume A: "fst p \<and> fst q \<and> blw (snd p) (snd q)"
  have "p \<in> {p} \<and> GV {p} q" using A by (simp add: GV_single)
  thus "MV.PG p q" unfolding MV.PG_def by (rule exI)
qed

subsection \<open>Core clauses, comprehension, truth\<close>

lemma MV_core: "MV.FACT" "MV.LAM_CORE" "MV.N1" "MV.N2" "MV.N5_chain"
  and MV_N4: "MV.N4_pair (True, L 0) (ngV (ngV (True, L 0)))"
proof -
  show "MV.FACT" by (auto simp: MV.FACT_def GV_def)
  show "MV.LAM_CORE" unfolding MV.LAM_CORE_def MV_den using lamV_fv by (simp add: lamV_def)
  have g: "GV {(True, L 0)} (True, L 1)" by (simp add: GV_single)
  show "MV.N1" unfolding MV.N1_def using g by blast
  thus "MV.N2" unfolding MV.N2_def
    by (intro conjI exI[of _ "(True, L 0)"] exI[of _ "(True, L 1)"] exI[of _ "(True, L 2)"]) simp_all
  show "MV.N5_chain" unfolding MV.N5_chain_def
    by (intro exI[of _ "(True, L 0)"] exI[of _ "(True, L 1)"] exI[of _ "(True, L 2)"]
          exI[of _ "(True, L 3)"]) (simp add: MV_PG)
  have "{(True, L 1)} \<in> {\<Gamma>. GV \<Gamma> (True, L 2)}" "{(True, L 1)} \<notin> {\<Gamma>. GV \<Gamma> (True, L 0)}"
    by (auto simp: GV_single)
  thus "MV.N4_pair (True, L 0) (ngV (ngV (True, L 0)))"
    unfolding MV.N4_pair_def by (auto simp: ngV_def numeral_2_eq_2)
qed

lemma MV_N4s: "MV.N4_pairs" using MV.N4_dn[OF MV_N4] .

lemma MV_C3s: "MV.C3s" unfolding MV.C3s_def by auto

lemma MV_W: "MV.W_ID" "MV.W_TR" "MV.W_EM" "MV.W_TEM"
  by (simp_all add: MV.W_ID_def MV.W_TR_def MV.W_EM_def MV.W_TEM_def)

lemma MV_BETA_ID: "MV.BETA_ID"
  by (simp add: MV.BETA_ID_def MV_den lamV_def)

lemma MV_classical: "MV.CL_PROP" "MV.CL_QUANT" "MV.TS_FULL"
  by (simp_all add: MV.CL_PROP_def MV.CL_QUANT_def MV.TS_FULL_def ngV_def cjV_def djV_def
        trV_def exqV_def allqV_def bigV_def MV.sat_def)

subsection \<open>Introduction entries, at full strength\<close>

lemma MV_EX_FULL: "MV.EX_FULL"
  unfolding MV.EX_FULL_def
proof (intro allI impI)
  fix f :: "pv \<Rightarrow> pv" and a assume A: "True \<and> fst (f a)"
  hence "\<exists>p. fst (f p)" by blast
  hence e: "exqV f = (True, Top 0)" unfolding exqV_def by simp
  show "GV {f a} (exqV f)" unfolding e using A by (simp add: GV_single)
qed

lemma MV_ALL_INST: "MV.ALL_INST"
  unfolding MV.ALL_INST_def
proof (intro allI impI)
  fix f :: "pv \<Rightarrow> pv" assume A: "True \<and> (\<forall>a. fst (f a))"
  hence e: "allqV f = (True, Top 0)" unfolding allqV_def by simp
  show "GV (MV.inst f) (allqV f)" unfolding e GV_def MV.inst_def using A by auto
qed

lemma MV_CONJ_INF: "MV.CONJ_INF"
  unfolding MV.CONJ_INF_def
proof (intro allI impI)
  fix f :: "pv \<Rightarrow> pv" assume A: "True \<and> MV.sat f \<noteq> {} \<and> (\<forall>q\<in>MV.sat f. fst q)"
  hence e: "bigV f = (True, Top 0)" unfolding bigV_def MV.sat_def by auto
  show "GV (MV.sat f) (bigV f)" unfolding e GV_def using A by auto
qed

lemma MV_DISJ: "MV.DISJ_ONE" "MV.DISJ_BOTH"
  by (auto simp: MV.DISJ_ONE_def MV.DISJ_BOTH_def GV_def djV_def blw_mx1 blw_mx2)

lemma MV_CONJ_BIN: "MV.CONJ_BIN"
  by (auto simp: MV.CONJ_BIN_def GV_def cjV_def blw_mx1 blw_mx2)

lemma MV_TR: "MV.TR_FULL" "MV.TR_NEG"
  by (auto simp: MV.TR_FULL_def MV.TR_NEG_def GV_single trV_def ngV_def blw_up)

lemma MV_NEG: "MV.NEG_DN" "MV.NEG_DM"
  by (auto simp: MV.NEG_DN_def MV.NEG_DM_def GV_def ngV_def cjV_def djV_def blw_up2
        blw_mx1' blw_mx2')

subsection \<open>Structural entries\<close>

lemma MV_TRANS_P: "MV.TRANS_P"
  unfolding MV.TRANS_P_def MV_PG using blw_trans by blast

lemma MV_TRANS_CUT: "MV.TRANS_CUT"
  unfolding MV.TRANS_CUT_def
proof (intro allI impI)
  fix \<Gamma> \<Delta> :: "pv set" and H :: "pv \<Rightarrow> pv set" and q
  assume A: "GV \<Gamma> q \<and> \<Delta> \<subseteq> \<Gamma> \<and> (\<forall>p\<in>\<Delta>. GV (H p) p)"
  let ?N = "(\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)"
  have ne: "?N \<noteq> {}"
  proof (cases "\<Gamma> - \<Delta> = {}")
    case False thus ?thesis by blast
  next
    case True
    obtain p where p: "p \<in> \<Gamma>" using A unfolding GV_def by blast
    hence "p \<in> \<Delta>" using True by blast
    moreover have "H p \<noteq> {}" using A \<open>p \<in> \<Delta>\<close> unfolding GV_def by blast
    ultimately show ?thesis by blast
  qed
  have mem: "fst r \<and> blw (snd r) (snd q)" if rN: "r \<in> ?N" for r
  proof (cases "r \<in> \<Gamma> - \<Delta>")
    case True thus ?thesis using A unfolding GV_def by blast
  next
    case False
    with rN obtain p where p: "p \<in> \<Delta>" "r \<in> H p" by blast
    have "fst r \<and> blw (snd r) (snd p)" using A p unfolding GV_def by blast
    moreover have "blw (snd p) (snd q)" using A p(1) unfolding GV_def by blast
    ultimately show ?thesis using blw_trans by blast
  qed
  have "fst q" using A unfolding GV_def by blast
  thus "GV ?N q" unfolding GV_def using ne mem by blast
qed

lemma MV_AMALG_INF: "MV.AMALG_INF"
  unfolding MV.AMALG_INF_def GV_def by blast

lemma MV_EMPTY_NONE: "MV.EMPTY_NONE"
  by (simp add: MV.EMPTY_NONE_def GV_def)

subsection \<open>IRR.W\<close>

text \<open>A code for propositions as numbers, so that any set of propositions can be
  presented by a set of variables under one environment.\<close>
fun cdl :: "lv \<Rightarrow> nat" where "cdl (L n) = 2 * n" | "cdl (Top k) = Suc (2 * k)"
definition idx :: "pv \<Rightarrow> nat" where "idx p = 2 * cdl (snd p) + (if fst p then 1 else 0)"
definition dcl :: "nat \<Rightarrow> lv" where "dcl m = (if even m then L (m div 2) else Top (m div 2))"
definition dec :: "nat \<Rightarrow> pv" where "dec k = (odd k, dcl (k div 2))"

lemma dcl_cdl: "dcl (cdl l) = l" by (cases l) (simp_all add: dcl_def)
lemma dec_idx: "dec (idx p) = p"
  by (cases p) (simp add: dec_def idx_def dcl_cdl)
lemma idx_inj: "idx p = idx q \<Longrightarrow> p = q" by (metis dec_idx)

text \<open>A reflexive fact has a conclusion c in the tier Top. Present its grounds \<Gamma> by the
  variables Var (idx p), p in \<Gamma>, under the environment dec, and let Var (idx c) mark c.
  Putting a truth B for c gives the set \<Gamma> with B in place of c, a non-empty set of
  truths, which grounds c because c is in the tier Top.\<close>
lemma MV_IRR_W: "MV.IRR_W"
  unfolding MV.IRR_W_def
proof (intro allI impI)
  fix \<Gamma> c assume A: "GV \<Gamma> c \<and> c \<in> \<Gamma>"
  hence tc: "fst c" and ne: "\<Gamma> \<noteq> {}" unfolding GV_def by blast+
  have "blw (snd c) (snd c)" using A unfolding GV_def by blast
  then obtain k where top: "snd c = Top k" using blw_refl by blast
  let ?\<Phi> = "Var ` idx ` \<Gamma>"
  let ?z = "idx c"
  have val: "MV.den (dec(?z:=B)) (Var (idx p)) = (if p = c then B else p)" for B p
    using idx_inj dec_idx by auto
  have img: "(\<lambda>\<phi>. MV.den (dec(?z:=B)) \<phi>) ` ?\<Phi> = (\<lambda>p. if p = c then B else p) ` \<Gamma>" for B
    unfolding image_image using val by simp
  have c1: "\<Gamma> = (\<lambda>\<phi>. MV.den (dec(?z:=c)) \<phi>) ` ?\<Phi>" unfolding img by auto
  have c2: "\<exists>\<phi>\<in>?\<Phi>. ?z \<in> fv \<phi>" using A by auto
  have c3: "\<forall>\<phi>\<in>?\<Phi>. \<forall>\<psi>\<in>subf \<phi>. ?z \<notin> fv \<psi> \<longrightarrow> MV.den (dec(?z:=c)) \<psi> \<noteq> c"
  proof (intro ballI impI)
    fix \<phi> \<psi> assume "\<phi> \<in> ?\<Phi>" "\<psi> \<in> subf \<phi>" "?z \<notin> fv \<psi>"
    then obtain p where p: "\<psi> = Var (idx p)" "idx c \<noteq> idx p" by auto
    hence "p \<noteq> c" by blast
    thus "MV.den (dec(?z:=c)) \<psi> \<noteq> c" unfolding p(1) val by simp
  qed
  have c4: "\<forall>B. (\<forall>\<phi>\<in>?\<Phi>. fst (MV.den (dec(?z:=B)) \<phi>))
              \<longrightarrow> GV ((\<lambda>\<phi>. MV.den (dec(?z:=B)) \<phi>) ` ?\<Phi>) c"
  proof (intro allI impI)
    fix B assume T: "\<forall>\<phi>\<in>?\<Phi>. fst (MV.den (dec(?z:=B)) \<phi>)"
    have "\<forall>q\<in>(\<lambda>\<phi>. MV.den (dec(?z:=B)) \<phi>) ` ?\<Phi>. fst q" using T by blast
    moreover have "(\<lambda>\<phi>. MV.den (dec(?z:=B)) \<phi>) ` ?\<Phi> \<noteq> {}" using ne by blast
    ultimately show "GV ((\<lambda>\<phi>. MV.den (dec(?z:=B)) \<phi>) ` ?\<Phi>) c"
      unfolding GV_def using tc top by simp
  qed
  show "MV.vacW c \<Gamma> c" unfolding MV.vacW_def using c1 c2 c3 c4 by blast
qed

text \<open>The control entry IRR.MEM holds as well, for the same reason.\<close>
lemma MV_IRR_MEM: "MV.IRR_MEM"
  unfolding MV.IRR_MEM_def MV.vacM_def
proof (intro allI impI conjI)
  fix \<Gamma> c assume A: "GV \<Gamma> c \<and> c \<in> \<Gamma>"
  show "c \<in> \<Gamma>" using A by blast
  fix b :: pv assume b: "fst b"
  have "blw (snd c) (snd c)" using A unfolding GV_def by blast
  then obtain k where top: "snd c = Top k" using blw_refl by blast
  show "GV (insert b (\<Gamma> - {c})) c" unfolding GV_def using A b top unfolding GV_def by auto
qed

subsection \<open>The circles of the puzzles are in the model, with distinct propositions\<close>

text \<open>s = \<forall>p(p \<or> \<not>p), its instance d = s \<or> \<not>s, u = \<forall>p(Tp \<or> \<not>Tp) with the truth
  ascription Tu and the instance Tu \<or> \<not>Tu, and e = \<exists>p p. Strict irreflexivity,
  asymmetry and antisymmetry fail.\<close>
lemma MV_circles:
  fixes s d u :: pv
  defines "s \<equiv> allqV (\<lambda>p. djV p (ngV p))"
      and "u \<equiv> allqV (\<lambda>p. djV (trV p) (ngV (trV p)))"
  defines "d \<equiv> djV s (ngV s)"
  shows "s = (True, Top 0)" "d = (True, Top 2)" "MV.PG s d" "MV.PG d s" "MV.PG s s"
    and "trV u = (True, Top 1)" "djV (trV u) (ngV (trV u)) = (True, Top 3)"
    and "MV.PG u (trV u)" "MV.PG (trV u) (djV (trV u) (ngV (trV u)))"
        "MV.PG (djV (trV u) (ngV (trV u))) u"
    and "exqV (\<lambda>p. p) = (True, Top 0)" "GV {exqV (\<lambda>p. p)} (exqV (\<lambda>p. p))"
proof -
  show s: "s = (True, Top 0)" unfolding s_def allqV_def by (simp add: djV_def ngV_def)
  have u: "u = (True, Top 0)" unfolding u_def allqV_def by (simp add: djV_def ngV_def trV_def)
  show d: "d = (True, Top 2)" unfolding d_def s by (simp add: djV_def ngV_def numeral_2_eq_2)
  show "MV.PG s d" "MV.PG d s" "MV.PG s s" unfolding s d by (simp_all add: MV_PG)
  show tu: "trV u = (True, Top 1)" unfolding u by (simp add: trV_def)
  show du: "djV (trV u) (ngV (trV u)) = (True, Top 3)"
    unfolding tu by (simp add: djV_def ngV_def numeral_3_eq_3)
  show "MV.PG u (trV u)" "MV.PG (trV u) (djV (trV u) (ngV (trV u)))"
       "MV.PG (djV (trV u) (ngV (trV u))) u"
    unfolding du unfolding tu unfolding u by (simp_all add: MV_PG)
  show e: "exqV (\<lambda>p. p) = (True, Top 0)" unfolding exqV_def by auto
  show "GV {exqV (\<lambda>p. p)} (exqV (\<lambda>p. p))" unfolding e by (simp add: GV_single)
qed

lemma MV_fails: "\<not> MV.IRR_F" "\<not> MV.ASYM_P" "\<not> MV.ASYM_ANTI"
proof -
  have g: "GV {(True, Top 0)} (True, Top 0)" by (simp add: GV_single)
  show "\<not> MV.IRR_F" unfolding MV.IRR_F_def using g by blast
  have pg: "MV.PG (True, Top 0) (True, Top 1)" "MV.PG (True, Top 1) (True, Top 0)"
    by (simp_all add: MV_PG)
  show "\<not> MV.ASYM_P" unfolding MV.ASYM_P_def using pg by blast
  show "\<not> MV.ASYM_ANTI" unfolding MV.ASYM_ANTI_def using pg by fastforce
qed

subsection \<open>Non-triviality instances\<close>

text \<open>N3, one instance for each introduction entry, with pairwise distinct relata and the
  grounded proposition not among its grounds. For ALL.INST the function is the one of
  the sentence-position puzzle, p \<or> \<not>p: its universal closure (True, Top 0) is not one of
  its instances, although the instance at the closure itself, (True, Top 2), is one of
  the grounds.\<close>
lemma MV_N3:
  "GV {(True, L 0)} (exqV (\<lambda>p. p)) \<and> exqV (\<lambda>p. p) \<notin> {(True, L 0) :: pv}"
  "GV (MV.inst (\<lambda>p. djV p (ngV p))) (allqV (\<lambda>p. djV p (ngV p)))
     \<and> allqV (\<lambda>p. djV p (ngV p)) \<notin> MV.inst (\<lambda>p. djV p (ngV p))"
  "GV {(True, L 0)} (djV (True, L 0) (False, L 1)) \<and> djV (True, L 0) (False, L 1) = (True, L 2)"
  "GV {(True, L 0), (True, L 1)} (cjV (True, L 0) (True, L 1))
     \<and> cjV (True, L 0) (True, L 1) = (True, L 2)"
  "GV {(True, L 0)} (trV (True, L 0)) \<and> trV (True, L 0) = (True, L 1)"
  "GV {(True, L 0)} (ngV (ngV (True, L 0))) \<and> ngV (ngV (True, L 0)) = (True, L 2)"
proof -
  have e: "exqV (\<lambda>p. p) = (True, Top 0)" unfolding exqV_def by auto
  show "GV {(True, L 0)} (exqV (\<lambda>p. p)) \<and> exqV (\<lambda>p. p) \<notin> {(True, L 0) :: pv}"
    unfolding e by (simp add: GV_single)
  have a: "allqV (\<lambda>p. djV p (ngV p)) = (True, Top 0)"
    unfolding allqV_def by (simp add: djV_def ngV_def)
  have ni: "(True, Top 0) \<noteq> djV p (ngV p)" for p
    by (cases p; cases "snd p") (simp_all add: djV_def ngV_def)
  have "GV (MV.inst (\<lambda>p. djV p (ngV p))) (True, Top 0)"
    unfolding GV_def MV.inst_def by (auto simp: djV_def ngV_def)
  moreover have "(True, Top 0) \<notin> MV.inst (\<lambda>p. djV p (ngV p))"
    unfolding MV.inst_def using ni by blast
  ultimately show "GV (MV.inst (\<lambda>p. djV p (ngV p))) (allqV (\<lambda>p. djV p (ngV p)))
     \<and> allqV (\<lambda>p. djV p (ngV p)) \<notin> MV.inst (\<lambda>p. djV p (ngV p))" unfolding a by blast
  show "GV {(True, L 0)} (djV (True, L 0) (False, L 1)) \<and> djV (True, L 0) (False, L 1) = (True, L 2)"
    by (simp add: GV_single djV_def numeral_2_eq_2)
  show "GV {(True, L 0), (True, L 1)} (cjV (True, L 0) (True, L 1))
     \<and> cjV (True, L 0) (True, L 1) = (True, L 2)"
    by (simp add: GV_def cjV_def numeral_2_eq_2)
  show "GV {(True, L 0)} (trV (True, L 0)) \<and> trV (True, L 0) = (True, L 1)"
    by (simp add: GV_single trV_def)
  show "GV {(True, L 0)} (ngV (ngV (True, L 0))) \<and> ngV (ngV (True, L 0)) = (True, L 2)"
    by (simp add: GV_single ngV_def numeral_2_eq_2)
qed

text \<open>The limit of the model, stated as a theorem: every truth helps ground every true
  quantified proposition, and every true proposition that is built from one.\<close>
lemma MV_top_universal:
  "fst b \<Longrightarrow> fst (exqV f) \<Longrightarrow> MV.PG b (exqV f)"
  "fst b \<Longrightarrow> fst (allqV f) \<Longrightarrow> MV.PG b (allqV f)"
  by (simp_all add: MV_PG exqV_def allqV_def)

theorem MV_package:
  "MV.FACT \<and> MV.LAM_CORE \<and> MV.C3s \<and> MV.W_ID \<and> MV.W_TR \<and> MV.W_EM \<and> MV.W_TEM \<and> MV.BETA_ID
   \<and> MV.CL_PROP \<and> MV.CL_QUANT \<and> MV.TS_FULL
   \<and> MV.EX_FULL \<and> MV.ALL_INST \<and> MV.CONJ_INF \<and> MV.CONJ_BIN \<and> MV.DISJ_ONE \<and> MV.DISJ_BOTH
   \<and> MV.TR_FULL \<and> MV.TR_NEG \<and> MV.NEG_DN \<and> MV.NEG_DM
   \<and> MV.TRANS_P \<and> MV.TRANS_CUT \<and> MV.AMALG_INF \<and> MV.EMPTY_NONE \<and> MV.IRR_W \<and> MV.IRR_MEM
   \<and> MV.N1 \<and> MV.N2 \<and> MV.N4_pairs \<and> MV.N5_chain
   \<and> \<not> MV.IRR_F \<and> \<not> MV.ASYM_P \<and> \<not> MV.ASYM_ANTI"
  using MV_core MV_N4s MV_C3s MV_W MV_BETA_ID MV_classical MV_EX_FULL MV_ALL_INST MV_CONJ_INF
        MV_CONJ_BIN MV_DISJ MV_TR MV_NEG MV_TRANS_P MV_TRANS_CUT MV_AMALG_INF MV_EMPTY_NONE
        MV_IRR_W MV_IRR_MEM MV_fails by blast


section \<open>Part 4. The same model at the comprehension levels C1, C2 and C3d\<close>

text \<open>
  The entries C1, C2 and C3d say exactly which propositional functions are admissible,
  so MV, where all are, does not satisfy them. The introduction entries of MV hold for
  every function whatever is admissible, so the model can be read at each level by
  changing the admissibility predicate only. Every other constant is that of MV, and
  the entries that do not mention admissibility are literally the same statements.
\<close>

lemma GV_exq: "fst (f a) \<Longrightarrow> GV {f a} (exqV f)"
proof -
  assume A: "fst (f a)"
  hence "\<exists>p. fst (f p)" by blast
  hence e: "exqV f = (True, Top 0)" unfolding exqV_def by simp
  show "GV {f a} (exqV f)" unfolding e using A by (simp add: GV_single)
qed

lemma GV_allq: "\<forall>a. fst (f a) \<Longrightarrow> GV (range f) (allqV f)"
proof -
  assume A: "\<forall>a. fst (f a)"
  hence e: "allqV f = (True, Top 0)" unfolding allqV_def by simp
  show "GV (range f) (allqV f)" unfolding e GV_def using A by auto
qed

definition admV1 :: "(pv \<Rightarrow> pv) \<Rightarrow> bool" where
  "admV1 f \<longleftrightarrow> f \<in> {(\<lambda>p. p), trV, (\<lambda>p. djV p (ngV p)), (\<lambda>p. djV (trV p) (ngV (trV p)))}"
definition admV2 :: "(pv \<Rightarrow> pv) \<Rightarrow> bool" where
  "admV2 f \<longleftrightarrow> (\<exists>x a v. lvl a \<le> 1 \<and> f = lamV x a v)"
definition admV3 :: "(pv \<Rightarrow> pv) \<Rightarrow> bool" where
  "admV3 f \<longleftrightarrow> (\<exists>x a v. f = lamV x a v)"

interpretation MV1: gsig "fst :: pv \<Rightarrow> bool" "\<lambda>_. (True, L 0)" ngV cjV djV trV
  "\<lambda>(f :: pv \<Rightarrow> pv) p. f p" exqV allqV bigV lamV admV1 GV "\<lambda>_. (True, L 0)" "(True, L 0)" .
interpretation MV2: gsig "fst :: pv \<Rightarrow> bool" "\<lambda>_. (True, L 0)" ngV cjV djV trV
  "\<lambda>(f :: pv \<Rightarrow> pv) p. f p" exqV allqV bigV lamV admV2 GV "\<lambda>_. (True, L 0)" "(True, L 0)" .
interpretation MV3: gsig "fst :: pv \<Rightarrow> bool" "\<lambda>_. (True, L 0)" ngV cjV djV trV
  "\<lambda>(f :: pv \<Rightarrow> pv) p. f p" exqV allqV bigV lamV admV3 GV "\<lambda>_. (True, L 0)" "(True, L 0)" .

lemma MV1_C1: "MV1.C1"
  by (simp add: MV1.C1_def admV1_def MV1.f_id_def MV1.f_tr_def MV1.f_em_def MV1.f_tem_def
        lamV_def MV_den)
lemma MV2_C2: "MV2.C2 1" by (simp add: MV2.C2_def admV2_def)
lemma MV3_C3d: "MV3.C3d" by (simp add: MV3.C3d_def admV3_def)

lemma MV1_W: "MV1.W_ID" "MV1.W_TR" "MV1.W_EM" "MV1.W_TEM"
  using MV1_C1 unfolding MV1.C1_def MV1.W_ID_def MV1.W_TR_def MV1.W_EM_def MV1.W_TEM_def by blast+

lemma MV2_W: "MV2.W_ID" "MV2.W_TR" "MV2.W_EM" "MV2.W_TEM"
proof -
  have "admV2 (lamV x a v)" if "lvl a \<le> 1" for x a v unfolding admV2_def using that by blast
  thus "MV2.W_ID" "MV2.W_TR" "MV2.W_EM" "MV2.W_TEM"
    unfolding MV2.W_ID_def MV2.W_TR_def MV2.W_EM_def MV2.W_TEM_def
              MV2.f_id_def MV2.f_tr_def MV2.f_em_def MV2.f_tem_def by simp_all
qed

lemma MV3_W: "MV3.W_ID" "MV3.W_TR" "MV3.W_EM" "MV3.W_TEM"
  unfolding MV3.W_ID_def MV3.W_TR_def MV3.W_EM_def MV3.W_TEM_def admV3_def
            MV3.f_id_def MV3.f_tr_def MV3.f_em_def MV3.f_tem_def by blast+

lemma MV1_intro: "MV1.EX_FULL" "MV1.ALL_INST"
  unfolding MV1.EX_FULL_def MV1.ALL_INST_def MV1.inst_def using GV_exq GV_allq by blast+
lemma MV2_intro: "MV2.EX_FULL" "MV2.ALL_INST"
  unfolding MV2.EX_FULL_def MV2.ALL_INST_def MV2.inst_def using GV_exq GV_allq by blast+
lemma MV3_intro: "MV3.EX_FULL" "MV3.ALL_INST"
  unfolding MV3.EX_FULL_def MV3.ALL_INST_def MV3.inst_def using GV_exq GV_allq by blast+

text \<open>CONJ.INF mentions admissibility only as a hypothesis, and in MV every function is
  admissible, so the entry of MV gives the entry of each variant.\<close>
lemma MV_variants_CONJ_INF: "MV1.CONJ_INF" "MV2.CONJ_INF" "MV3.CONJ_INF"
  using MV_CONJ_INF unfolding MV.CONJ_INF_def MV1.CONJ_INF_def MV2.CONJ_INF_def MV3.CONJ_INF_def
  by blast+

text \<open>Woods's Objection 3 (p. 643): the existential of p \<or> A helps ground itself. Its
  propositional function is admissible at C2 and C3d, and the reflexive fact is in the
  model.\<close>
lemma MV2_obj3:
  "admV2 (lamV 0 (Disj (Var 0) (Cst 0)) v)"
  "lamV 0 (Disj (Var 0) (Cst 0)) v = (\<lambda>p. djV p (True, L 0))"
  "MV.PG (exqV (\<lambda>p. djV p (True, L 0))) (exqV (\<lambda>p. djV p (True, L 0)))"
proof -
  show "admV2 (lamV 0 (Disj (Var 0) (Cst 0)) v)" unfolding admV2_def
    by (intro exI[of _ 0] exI[of _ "Disj (Var 0) (Cst 0)"] exI[of _ v]) simp
  show "lamV 0 (Disj (Var 0) (Cst 0)) v = (\<lambda>p. djV p (True, L 0))" by (simp add: lamV_def)
  have "exqV (\<lambda>p. djV p (True, L 0)) = (True, Top 0)" unfolding exqV_def by (simp add: djV_def)
  thus "MV.PG (exqV (\<lambda>p. djV p (True, L 0))) (exqV (\<lambda>p. djV p (True, L 0)))"
    by (simp add: MV_PG)
qed

text \<open>The certificates. The entries without admissibility are those of MV_package.\<close>
theorem MV1_package:
  "MV1.FACT \<and> MV1.LAM_CORE \<and> MV1.C1 \<and> MV1.W_ID \<and> MV1.W_TR \<and> MV1.W_EM \<and> MV1.W_TEM \<and> MV1.BETA_ID
   \<and> MV1.CL_PROP \<and> MV1.CL_QUANT \<and> MV1.TS_FULL \<and> MV1.EX_FULL \<and> MV1.ALL_INST \<and> MV1.CONJ_INF \<and> MV1.CONJ_BIN
   \<and> MV1.DISJ_ONE \<and> MV1.DISJ_BOTH \<and> MV1.TR_FULL \<and> MV1.TR_NEG \<and> MV1.NEG_DN \<and> MV1.NEG_DM
   \<and> MV1.TRANS_P \<and> MV1.TRANS_CUT \<and> MV1.AMALG_INF \<and> MV1.EMPTY_NONE \<and> MV1.IRR_W \<and> MV1.IRR_MEM
   \<and> MV1.N1 \<and> MV1.N2 \<and> MV1.N4_pairs \<and> MV1.N5_chain"
  using MV_package MV1_C1 MV1_W MV1_intro MV_variants_CONJ_INF by blast

theorem MV2_package:
  "MV2.FACT \<and> MV2.LAM_CORE \<and> MV2.C2 1 \<and> MV2.W_ID \<and> MV2.W_TR \<and> MV2.W_EM \<and> MV2.W_TEM \<and> MV2.BETA_ID
   \<and> MV2.CL_PROP \<and> MV2.CL_QUANT \<and> MV2.TS_FULL \<and> MV2.EX_FULL \<and> MV2.ALL_INST \<and> MV2.CONJ_INF \<and> MV2.CONJ_BIN
   \<and> MV2.DISJ_ONE \<and> MV2.DISJ_BOTH \<and> MV2.TR_FULL \<and> MV2.TR_NEG \<and> MV2.NEG_DN \<and> MV2.NEG_DM
   \<and> MV2.TRANS_P \<and> MV2.TRANS_CUT \<and> MV2.AMALG_INF \<and> MV2.EMPTY_NONE \<and> MV2.IRR_W \<and> MV2.IRR_MEM
   \<and> MV2.N1 \<and> MV2.N2 \<and> MV2.N4_pairs \<and> MV2.N5_chain"
  using MV_package MV2_C2 MV2_W MV2_intro MV_variants_CONJ_INF by blast

theorem MV3_package:
  "MV3.FACT \<and> MV3.LAM_CORE \<and> MV3.C3d \<and> MV3.W_ID \<and> MV3.W_TR \<and> MV3.W_EM \<and> MV3.W_TEM \<and> MV3.BETA_ID
   \<and> MV3.CL_PROP \<and> MV3.CL_QUANT \<and> MV3.TS_FULL \<and> MV3.EX_FULL \<and> MV3.ALL_INST \<and> MV3.CONJ_INF \<and> MV3.CONJ_BIN
   \<and> MV3.DISJ_ONE \<and> MV3.DISJ_BOTH \<and> MV3.TR_FULL \<and> MV3.TR_NEG \<and> MV3.NEG_DN \<and> MV3.NEG_DM
   \<and> MV3.TRANS_P \<and> MV3.TRANS_CUT \<and> MV3.AMALG_INF \<and> MV3.EMPTY_NONE \<and> MV3.IRR_W \<and> MV3.IRR_MEM
   \<and> MV3.N1 \<and> MV3.N2 \<and> MV3.N4_pairs \<and> MV3.N5_chain"
  using MV_package MV3_C3d MV3_W MV3_intro MV_variants_CONJ_INF by blast

section \<open>Part 5. Model MY: the same packages with antisymmetry (ASYM.ANTI)\<close>

text \<open>
  Woods weakens asymmetry to antisymmetry (fn. 4). With ASYM.ANTI the packages force the
  propositions on each circle to be one proposition (fine_sp_anti_collapse), so MV,
  which keeps them apart, fails ASYM.ANTI. MY is MV with a single top level Om in place
  of the tier Top n: there is exactly one true proposition at the top, (True, Om), and
  every circle collapses into it. Mutual partial ground then holds only between
  (True, Om) and itself.
\<close>

datatype lw = Lw nat | Om

fun upY :: "lw \<Rightarrow> lw" where
  "upY (Lw n) = Lw (Suc n)" | "upY Om = Om"
fun mxY :: "lw \<Rightarrow> lw \<Rightarrow> lw" where
  "mxY (Lw m) (Lw n) = Lw (max m n)"
| "mxY Om b = Om"
| "mxY (Lw m) Om = Om"
fun blY :: "lw \<Rightarrow> lw \<Rightarrow> bool" where
  "blY a Om = True"
| "blY (Lw m) (Lw n) = (m < n)"
| "blY Om (Lw n) = False"

lemma blY_up: "blY a (upY a)" by (cases a) simp_all
lemma blY_mx1: "blY a (upY (mxY a b))" by (cases a; cases b) simp_all
lemma blY_mx2: "blY b (upY (mxY a b))" by (cases a; cases b) simp_all
lemma blY_trans: "blY a b \<Longrightarrow> blY b c \<Longrightarrow> blY a c" by (cases a; cases b; cases c) simp_all
lemma blY_refl: "blY a a \<Longrightarrow> a = Om" by (cases a) simp_all
lemma blY_anti: "blY a b \<Longrightarrow> blY b a \<Longrightarrow> a = Om \<and> b = Om" by (cases a; cases b) simp_all

type_synonym py = "bool \<times> lw"

definition ngY :: "py \<Rightarrow> py" where "ngY p = (\<not> fst p, upY (snd p))"
definition cjY :: "py \<Rightarrow> py \<Rightarrow> py" where "cjY p q = (fst p \<and> fst q, upY (mxY (snd p) (snd q)))"
definition djY :: "py \<Rightarrow> py \<Rightarrow> py" where "djY p q = (fst p \<or> fst q, upY (mxY (snd p) (snd q)))"
definition trY :: "py \<Rightarrow> py" where "trY p = (fst p, upY (snd p))"

primrec dY :: "(nat \<Rightarrow> py) \<Rightarrow> fm \<Rightarrow> py" where
  "dY v (Var n) = v n"
| "dY v (Cst n) = (True, Lw 0)"
| "dY v (Neg a) = ngY (dY v a)"
| "dY v (Conj a b) = cjY (dY v a) (dY v b)"
| "dY v (Disj a b) = djY (dY v a) (dY v b)"
| "dY v (Tr a) = trY (dY v a)"
| "dY v (Ex x a) = ((\<exists>p. fst (dY (v(x:=p)) a)), Om)"
| "dY v (All x a) = ((\<forall>p. fst (dY (v(x:=p)) a)), Om)"
| "dY v (BigC x a) = ((\<forall>p. fst (dY (v(x:=p)) a) \<longrightarrow> fst p), Om)"

definition lamY :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> py) \<Rightarrow> py \<Rightarrow> py" where
  "lamY x a v = (\<lambda>p. dY (v(x:=p)) a)"
definition exqY :: "(py \<Rightarrow> py) \<Rightarrow> py" where "exqY f = ((\<exists>p. fst (f p)), Om)"
definition allqY :: "(py \<Rightarrow> py) \<Rightarrow> py" where "allqY f = ((\<forall>p. fst (f p)), Om)"
definition bigY :: "(py \<Rightarrow> py) \<Rightarrow> py" where "bigY f = ((\<forall>p. fst (f p) \<longrightarrow> fst p), Om)"

definition GY :: "py set \<Rightarrow> py \<Rightarrow> bool" where
  "GY \<Gamma> q \<longleftrightarrow> \<Gamma> \<noteq> {} \<and> fst q \<and> (\<forall>p\<in>\<Gamma>. fst p \<and> blY (snd p) (snd q))"

definition admY2 :: "(py \<Rightarrow> py) \<Rightarrow> bool" where
  "admY2 f \<longleftrightarrow> (\<exists>x a v. lvl a \<le> 1 \<and> f = lamY x a v)"

interpretation MY: gsig "fst :: py \<Rightarrow> bool" "\<lambda>_. (True, Lw 0)" ngY cjY djY trY
  "\<lambda>(f :: py \<Rightarrow> py) p. f p" exqY allqY bigY lamY "\<lambda>_. True" GY "\<lambda>_. (True, Lw 0)" "(True, Lw 0)" .
interpretation MY2: gsig "fst :: py \<Rightarrow> bool" "\<lambda>_. (True, Lw 0)" ngY cjY djY trY
  "\<lambda>(f :: py \<Rightarrow> py) p. f p" exqY allqY bigY lamY admY2 GY "\<lambda>_. (True, Lw 0)" "(True, Lw 0)" .

lemma quantY:
  "exqY (lamY x a v) = ((\<exists>p. fst (dY (v(x:=p)) a)), Om)"
  "allqY (lamY x a v) = ((\<forall>p. fst (dY (v(x:=p)) a)), Om)"
  "bigY (lamY x a v) = ((\<forall>p. fst (dY (v(x:=p)) a) \<longrightarrow> fst p), Om)"
  by (simp_all add: lamY_def exqY_def allqY_def bigY_def)

lemma MY_den: "MY.den = dY"
proof (intro ext)
  fix v a show "MY.den v a = dY v a"
    by (induction a) (simp_all add: quantY)
qed

lemma dY_fv: "(\<forall>y\<in>fv a. v y = w y) \<Longrightarrow> dY v a = dY w a"
proof (induct a arbitrary: v w)
  case (Ex x a)
  have "\<And>p. dY (v(x:=p)) a = dY (w(x:=p)) a"
    by (rule Ex.hyps) (use Ex.prems in auto)
  then show ?case by simp
next
  case (All x a)
  have "\<And>p. dY (v(x:=p)) a = dY (w(x:=p)) a"
    by (rule All.hyps) (use All.prems in auto)
  then show ?case by simp
next
  case (BigC x a)
  have "\<And>p. dY (v(x:=p)) a = dY (w(x:=p)) a"
    by (rule BigC.hyps) (use BigC.prems in auto)
  then show ?case by simp
next
  case (Neg a)
  have "dY v a = dY w a" by (rule Neg.hyps) (use Neg.prems in auto)
  then show ?case by simp
next
  case (Tr a)
  have "dY v a = dY w a" by (rule Tr.hyps) (use Tr.prems in auto)
  then show ?case by simp
next
  case (Conj a b)
  have "dY v a = dY w a" by (rule Conj.hyps(1)) (use Conj.prems in auto)
  moreover have "dY v b = dY w b" by (rule Conj.hyps(2)) (use Conj.prems in auto)
  ultimately show ?case by simp
next
  case (Disj a b)
  have "dY v a = dY w a" by (rule Disj.hyps(1)) (use Disj.prems in auto)
  moreover have "dY v b = dY w b" by (rule Disj.hyps(2)) (use Disj.prems in auto)
  ultimately show ?case by simp
qed simp_all

lemma lamY_fv: "\<forall>y\<in>fv a - {x}. v y = w y \<Longrightarrow> lamY x a v = lamY x a w"
  unfolding lamY_def by (intro ext dY_fv) auto

lemma GY_single: "GY {p} q \<longleftrightarrow> fst p \<and> fst q \<and> blY (snd p) (snd q)"
  unfolding GY_def by auto

lemma MY_PG: "MY.PG p q \<longleftrightarrow> fst p \<and> fst q \<and> blY (snd p) (snd q)"
proof
  assume "MY.PG p q"
  thus "fst p \<and> fst q \<and> blY (snd p) (snd q)" unfolding MY.PG_def GY_def by auto
next
  assume A: "fst p \<and> fst q \<and> blY (snd p) (snd q)"
  have "p \<in> {p} \<and> GY {p} q" using A by (simp add: GY_single)
  thus "MY.PG p q" unfolding MY.PG_def by (rule exI)
qed

lemma MY_core: "MY.FACT" "MY.LAM_CORE" "MY.N1" "MY.N2" "MY.N5_chain"
  and MY_N4: "MY.N4_pair (True, Lw 0) (ngY (ngY (True, Lw 0)))"
proof -
  show "MY.FACT" by (auto simp: MY.FACT_def GY_def)
  show "MY.LAM_CORE" unfolding MY.LAM_CORE_def MY_den using lamY_fv by (simp add: lamY_def)
  have g: "GY {(True, Lw 0)} (True, Lw 1)" by (simp add: GY_single)
  show "MY.N1" unfolding MY.N1_def using g by blast
  thus "MY.N2" unfolding MY.N2_def
    by (intro conjI exI[of _ "(True, Lw 0)"] exI[of _ "(True, Lw 1)"] exI[of _ "(True, Lw 2)"]) simp_all
  show "MY.N5_chain" unfolding MY.N5_chain_def
    by (intro exI[of _ "(True, Lw 0)"] exI[of _ "(True, Lw 1)"] exI[of _ "(True, Lw 2)"]
          exI[of _ "(True, Lw 3)"]) (simp add: MY_PG)
  have "{(True, Lw 1)} \<in> {\<Gamma>. GY \<Gamma> (True, Lw 2)}" "{(True, Lw 1)} \<notin> {\<Gamma>. GY \<Gamma> (True, Lw 0)}"
    by (auto simp: GY_single)
  thus "MY.N4_pair (True, Lw 0) (ngY (ngY (True, Lw 0)))"
    unfolding MY.N4_pair_def by (auto simp: ngY_def numeral_2_eq_2)
qed

lemma MY_N4s: "MY.N4_pairs" using MY.N4_dn[OF MY_N4] .

lemma MY_C3s: "MY.C3s" unfolding MY.C3s_def by auto
lemma MY2_C2: "MY2.C2 1" by (simp add: MY2.C2_def admY2_def)

lemma MY_W: "MY.W_ID" "MY.W_TR" "MY.W_EM" "MY.W_TEM"
  by (simp_all add: MY.W_ID_def MY.W_TR_def MY.W_EM_def MY.W_TEM_def)

lemma MY2_W: "MY2.W_ID" "MY2.W_TR" "MY2.W_EM" "MY2.W_TEM"
proof -
  have "admY2 (lamY x a v)" if "lvl a \<le> 1" for x a v unfolding admY2_def using that by blast
  thus "MY2.W_ID" "MY2.W_TR" "MY2.W_EM" "MY2.W_TEM"
    unfolding MY2.W_ID_def MY2.W_TR_def MY2.W_EM_def MY2.W_TEM_def
              MY2.f_id_def MY2.f_tr_def MY2.f_em_def MY2.f_tem_def by simp_all
qed

lemma MY_BETA_ID: "MY.BETA_ID"
  by (simp add: MY.BETA_ID_def MY_den lamY_def)

lemma MY_classical: "MY.CL_PROP" "MY.CL_QUANT" "MY.TS_FULL"
  by (simp_all add: MY.CL_PROP_def MY.CL_QUANT_def MY.TS_FULL_def ngY_def cjY_def djY_def
        trY_def exqY_def allqY_def bigY_def MY.sat_def)

lemma GY_exq: "fst (f a) \<Longrightarrow> GY {f a} (exqY f)"
proof -
  assume A: "fst (f a)"
  hence "\<exists>p. fst (f p)" by blast
  hence e: "exqY f = (True, Om)" unfolding exqY_def by simp
  show "GY {f a} (exqY f)" unfolding e using A by (simp add: GY_single)
qed

lemma GY_allq: "\<forall>a. fst (f a) \<Longrightarrow> GY (range f) (allqY f)"
proof -
  assume A: "\<forall>a. fst (f a)"
  hence e: "allqY f = (True, Om)" unfolding allqY_def by simp
  show "GY (range f) (allqY f)" unfolding e GY_def using A by auto
qed

lemma MY_intro: "MY.EX_FULL" "MY.ALL_INST"
  unfolding MY.EX_FULL_def MY.ALL_INST_def MY.inst_def using GY_exq GY_allq by blast+
lemma MY2_intro: "MY2.EX_FULL" "MY2.ALL_INST"
  unfolding MY2.EX_FULL_def MY2.ALL_INST_def MY2.inst_def using GY_exq GY_allq by blast+

lemma MY_DISJ: "MY.DISJ_ONE" "MY.DISJ_BOTH"
  by (auto simp: MY.DISJ_ONE_def MY.DISJ_BOTH_def GY_def djY_def blY_mx1 blY_mx2)

lemma MY_CONJ_BIN: "MY.CONJ_BIN"
  by (auto simp: MY.CONJ_BIN_def GY_def cjY_def blY_mx1 blY_mx2)

lemma MY_TR_FULL: "MY.TR_FULL"
  by (auto simp: MY.TR_FULL_def GY_single trY_def blY_up)

lemma MY_TRANS_P: "MY.TRANS_P"
  unfolding MY.TRANS_P_def MY_PG using blY_trans by blast

lemma MY_TRANS_CUT: "MY.TRANS_CUT"
  unfolding MY.TRANS_CUT_def
proof (intro allI impI)
  fix \<Gamma> \<Delta> :: "py set" and H :: "py \<Rightarrow> py set" and q
  assume A: "GY \<Gamma> q \<and> \<Delta> \<subseteq> \<Gamma> \<and> (\<forall>p\<in>\<Delta>. GY (H p) p)"
  let ?N = "(\<Gamma> - \<Delta>) \<union> (\<Union>p\<in>\<Delta>. H p)"
  have ne: "?N \<noteq> {}"
  proof (cases "\<Gamma> - \<Delta> = {}")
    case False thus ?thesis by blast
  next
    case True
    obtain p where p: "p \<in> \<Gamma>" using A unfolding GY_def by blast
    hence "p \<in> \<Delta>" using True by blast
    moreover have "H p \<noteq> {}" using A \<open>p \<in> \<Delta>\<close> unfolding GY_def by blast
    ultimately show ?thesis by blast
  qed
  have mem: "fst r \<and> blY (snd r) (snd q)" if rN: "r \<in> ?N" for r
  proof (cases "r \<in> \<Gamma> - \<Delta>")
    case True thus ?thesis using A unfolding GY_def by blast
  next
    case False
    with rN obtain p where p: "p \<in> \<Delta>" "r \<in> H p" by blast
    have "fst r \<and> blY (snd r) (snd p)" using A p unfolding GY_def by blast
    moreover have "blY (snd p) (snd q)" using A p(1) unfolding GY_def by blast
    ultimately show ?thesis using blY_trans by blast
  qed
  have "fst q" using A unfolding GY_def by blast
  thus "GY ?N q" unfolding GY_def using ne mem by blast
qed

lemma MY_AMALG_INF: "MY.AMALG_INF"
  unfolding MY.AMALG_INF_def GY_def by blast

lemma MY_EMPTY_NONE: "MY.EMPTY_NONE"
  by (simp add: MY.EMPTY_NONE_def GY_def)

lemma MY_ASYM_ANTI: "MY.ASYM_ANTI"
  unfolding MY.ASYM_ANTI_def MY_PG
proof (intro allI impI)
  fix p q :: py
  assume A: "(fst p \<and> fst q \<and> blY (snd p) (snd q)) \<and> (fst q \<and> fst p \<and> blY (snd q) (snd p))"
  hence "snd p = Om \<and> snd q = Om" using blY_anti by blast
  thus "p = q" using A by (simp add: prod_eq_iff)
qed

fun cdY :: "lw \<Rightarrow> nat" where "cdY (Lw n) = Suc n" | "cdY Om = 0"
definition idxY :: "py \<Rightarrow> nat" where "idxY p = 2 * cdY (snd p) + (if fst p then 1 else 0)"
definition dclY :: "nat \<Rightarrow> lw" where "dclY m = (case m of 0 \<Rightarrow> Om | Suc n \<Rightarrow> Lw n)"
definition decY :: "nat \<Rightarrow> py" where "decY k = (odd k, dclY (k div 2))"

lemma dclY_cdY: "dclY (cdY l) = l" by (cases l) (simp_all add: dclY_def)
lemma decY_idxY: "decY (idxY p) = p"
  by (cases p) (simp add: decY_def idxY_def dclY_cdY)
lemma idxY_inj: "idxY p = idxY q \<Longrightarrow> p = q" by (metis decY_idxY)

lemma MY_IRR_W: "MY.IRR_W"
  unfolding MY.IRR_W_def
proof (intro allI impI)
  fix \<Gamma> c assume A: "GY \<Gamma> c \<and> c \<in> \<Gamma>"
  hence tc: "fst c" and ne: "\<Gamma> \<noteq> {}" unfolding GY_def by blast+
  have "blY (snd c) (snd c)" using A unfolding GY_def by blast
  hence top: "snd c = Om" using blY_refl by blast
  let ?\<Phi> = "Var ` idxY ` \<Gamma>"
  let ?z = "idxY c"
  have val: "MY.den (decY(?z:=B)) (Var (idxY p)) = (if p = c then B else p)" for B p
    using idxY_inj decY_idxY by auto
  have img: "(\<lambda>\<phi>. MY.den (decY(?z:=B)) \<phi>) ` ?\<Phi> = (\<lambda>p. if p = c then B else p) ` \<Gamma>" for B
    unfolding image_image using val by simp
  have c1: "\<Gamma> = (\<lambda>\<phi>. MY.den (decY(?z:=c)) \<phi>) ` ?\<Phi>" unfolding img by auto
  have c2: "\<exists>\<phi>\<in>?\<Phi>. ?z \<in> fv \<phi>" using A by auto
  have c3: "\<forall>\<phi>\<in>?\<Phi>. \<forall>\<psi>\<in>subf \<phi>. ?z \<notin> fv \<psi> \<longrightarrow> MY.den (decY(?z:=c)) \<psi> \<noteq> c"
  proof (intro ballI impI)
    fix \<phi> \<psi> assume "\<phi> \<in> ?\<Phi>" "\<psi> \<in> subf \<phi>" "?z \<notin> fv \<psi>"
    then obtain p where p: "\<psi> = Var (idxY p)" "idxY c \<noteq> idxY p" by auto
    hence "p \<noteq> c" by blast
    thus "MY.den (decY(?z:=c)) \<psi> \<noteq> c" unfolding p(1) val by simp
  qed
  have c4: "\<forall>B. (\<forall>\<phi>\<in>?\<Phi>. fst (MY.den (decY(?z:=B)) \<phi>))
              \<longrightarrow> GY ((\<lambda>\<phi>. MY.den (decY(?z:=B)) \<phi>) ` ?\<Phi>) c"
  proof (intro allI impI)
    fix B assume T: "\<forall>\<phi>\<in>?\<Phi>. fst (MY.den (decY(?z:=B)) \<phi>)"
    have "\<forall>q\<in>(\<lambda>\<phi>. MY.den (decY(?z:=B)) \<phi>) ` ?\<Phi>. fst q" using T by blast
    moreover have "(\<lambda>\<phi>. MY.den (decY(?z:=B)) \<phi>) ` ?\<Phi> \<noteq> {}" using ne by blast
    ultimately show "GY ((\<lambda>\<phi>. MY.den (decY(?z:=B)) \<phi>) ` ?\<Phi>) c"
      unfolding GY_def using tc top by simp
  qed
  show "MY.vacW c \<Gamma> c" unfolding MY.vacW_def using c1 c2 c3 c4 by blast
qed

text \<open>The collapse: the universal truth of the sentence-position puzzle is its own
  instance, and the same proposition as \<exists>p p. N3 for ALL.INST therefore uses another
  function, the constant one (vacuous quantification), whose only instance (True, Lw 0)
  differs from its universal closure.\<close>
lemma MY_collapse:
  "allqY (\<lambda>p. djY p (ngY p)) = (True, Om)"
  "djY (allqY (\<lambda>p. djY p (ngY p))) (ngY (allqY (\<lambda>p. djY p (ngY p)))) = allqY (\<lambda>p. djY p (ngY p))"
  "exqY (\<lambda>p. p) = (True, Om)" "GY {(True, Om)} (True, Om)" "\<not> MY.IRR_F"
proof -
  show a: "allqY (\<lambda>p. djY p (ngY p)) = (True, Om)" unfolding allqY_def by (simp add: djY_def ngY_def)
  show "djY (allqY (\<lambda>p. djY p (ngY p))) (ngY (allqY (\<lambda>p. djY p (ngY p)))) = allqY (\<lambda>p. djY p (ngY p))"
    unfolding a by (simp add: djY_def ngY_def)
  show "exqY (\<lambda>p. p) = (True, Om)" unfolding exqY_def by auto
  show g: "GY {(True, Om)} (True, Om)" by (simp add: GY_single)
  show "\<not> MY.IRR_F" unfolding MY.IRR_F_def using g by blast
qed

lemma MY_N3:
  "GY {(True, Lw 0)} (exqY (\<lambda>p. p)) \<and> exqY (\<lambda>p. p) \<notin> {(True, Lw 0) :: py}"
  "GY (MY.inst (\<lambda>p. (True, Lw 0))) (allqY (\<lambda>p. (True, Lw 0)))
     \<and> allqY (\<lambda>p. (True, Lw 0)) \<notin> MY.inst (\<lambda>p. (True, Lw 0))
     \<and> lamY 0 (Cst 0) v = (\<lambda>p. (True, Lw 0))"
  "GY {(True, Lw 0)} (djY (True, Lw 0) (False, Lw 1)) \<and> djY (True, Lw 0) (False, Lw 1) = (True, Lw 2)"
  "GY {(True, Lw 0)} (trY (True, Lw 0)) \<and> trY (True, Lw 0) = (True, Lw 1)"
proof -
  have e: "exqY (\<lambda>p. p) = (True, Om)" unfolding exqY_def by auto
  show "GY {(True, Lw 0)} (exqY (\<lambda>p. p)) \<and> exqY (\<lambda>p. p) \<notin> {(True, Lw 0) :: py}"
    unfolding e by (simp add: GY_single)
  show "GY (MY.inst (\<lambda>p. (True, Lw 0))) (allqY (\<lambda>p. (True, Lw 0)))
     \<and> allqY (\<lambda>p. (True, Lw 0)) \<notin> MY.inst (\<lambda>p. (True, Lw 0))
     \<and> lamY 0 (Cst 0) v = (\<lambda>p. (True, Lw 0))"
    by (auto simp: GY_def MY.inst_def allqY_def lamY_def)
  show "GY {(True, Lw 0)} (djY (True, Lw 0) (False, Lw 1)) \<and> djY (True, Lw 0) (False, Lw 1) = (True, Lw 2)"
    by (simp add: GY_single djY_def numeral_2_eq_2)
  show "GY {(True, Lw 0)} (trY (True, Lw 0)) \<and> trY (True, Lw 0) = (True, Lw 1)"
    by (simp add: GY_single trY_def)
qed

theorem MY_package:
  "MY.FACT \<and> MY.LAM_CORE \<and> MY.C3s \<and> MY.W_ID \<and> MY.W_TR \<and> MY.W_EM \<and> MY.W_TEM \<and> MY.BETA_ID
   \<and> MY.CL_PROP \<and> MY.CL_QUANT \<and> MY.TS_FULL \<and> MY.EX_FULL \<and> MY.ALL_INST \<and> MY.CONJ_BIN
   \<and> MY.DISJ_ONE \<and> MY.DISJ_BOTH \<and> MY.TR_FULL
   \<and> MY.TRANS_P \<and> MY.TRANS_CUT \<and> MY.AMALG_INF \<and> MY.EMPTY_NONE \<and> MY.IRR_W \<and> MY.ASYM_ANTI
   \<and> MY.N1 \<and> MY.N2 \<and> MY.N4_pairs \<and> MY.N5_chain \<and> \<not> MY.IRR_F"
  using MY_core MY_N4s MY_C3s MY_W MY_BETA_ID MY_classical MY_intro MY_CONJ_BIN MY_DISJ
        MY_TR_FULL MY_TRANS_P MY_TRANS_CUT MY_AMALG_INF MY_EMPTY_NONE MY_IRR_W MY_ASYM_ANTI
        MY_collapse(5) by blast

theorem MY2_package:
  "MY2.FACT \<and> MY2.LAM_CORE \<and> MY2.C2 1 \<and> MY2.W_ID \<and> MY2.W_TR \<and> MY2.W_EM \<and> MY2.W_TEM \<and> MY2.BETA_ID
   \<and> MY2.CL_PROP \<and> MY2.CL_QUANT \<and> MY2.TS_FULL \<and> MY2.EX_FULL \<and> MY2.ALL_INST \<and> MY2.CONJ_BIN
   \<and> MY2.DISJ_ONE \<and> MY2.DISJ_BOTH \<and> MY2.TR_FULL
   \<and> MY2.TRANS_P \<and> MY2.TRANS_CUT \<and> MY2.AMALG_INF \<and> MY2.EMPTY_NONE \<and> MY2.IRR_W \<and> MY2.ASYM_ANTI
   \<and> MY2.N1 \<and> MY2.N2 \<and> MY2.N4_pairs \<and> MY2.N5_chain"
  using MY_package MY2_C2 MY2_W MY2_intro by blast

section \<open>Part 6. Model MZ: the packages with bounded finite grounds (FIN.B3)\<close>

text \<open>
  MV has infinite grounds (ALL.INST). The targets themselves use the partial entries,
  for which one-membered grounds suffice. MZ has the propositions and operations of MV
  and keeps only its one-membered grounds: {p} grounds q when both are true and q is in
  the top tier or the level of p is below that of q. Partial ground is the same
  relation as in MV. ALL.INST, CONJ.BIN and the other entries that need grounds with
  several members are not claimed.
\<close>

definition GZ :: "pv set \<Rightarrow> pv \<Rightarrow> bool" where
  "GZ \<Gamma> q \<longleftrightarrow> (\<exists>p. \<Gamma> = {p} \<and> fst p \<and> fst q \<and> blw (snd p) (snd q))"

interpretation MZ: gsig "fst :: pv \<Rightarrow> bool" "\<lambda>_. (True, L 0)" ngV cjV djV trV
  "\<lambda>(f :: pv \<Rightarrow> pv) p. f p" exqV allqV bigV lamV "\<lambda>_. True" GZ "\<lambda>_. (True, L 0)" "(True, L 0)" .
interpretation MZ2: gsig "fst :: pv \<Rightarrow> bool" "\<lambda>_. (True, L 0)" ngV cjV djV trV
  "\<lambda>(f :: pv \<Rightarrow> pv) p. f p" exqV allqV bigV lamV admV2 GZ "\<lambda>_. (True, L 0)" "(True, L 0)" .

lemma GZ_single: "GZ {p} q \<longleftrightarrow> fst p \<and> fst q \<and> blw (snd p) (snd q)"
  unfolding GZ_def by auto

lemma MZ_PG: "MZ.PG p q \<longleftrightarrow> fst p \<and> fst q \<and> blw (snd p) (snd q)"
proof
  assume "MZ.PG p q"
  thus "fst p \<and> fst q \<and> blw (snd p) (snd q)" unfolding MZ.PG_def GZ_def by auto
next
  assume A: "fst p \<and> fst q \<and> blw (snd p) (snd q)"
  have "p \<in> {p} \<and> GZ {p} q" using A by (simp add: GZ_single)
  thus "MZ.PG p q" unfolding MZ.PG_def by (rule exI)
qed

lemma MZ_core: "MZ.FACT" "MZ.N1" "MZ.N2" "MZ.N5_chain"
  and MZ_N4: "MZ.N4_pair (True, L 0) (ngV (ngV (True, L 0)))"
proof -
  show "MZ.FACT" by (auto simp: MZ.FACT_def GZ_def)
  have g: "GZ {(True, L 0)} (True, L 1)" by (simp add: GZ_single)
  show "MZ.N1" unfolding MZ.N1_def using g by blast
  thus "MZ.N2" unfolding MZ.N2_def
    by (intro conjI exI[of _ "(True, L 0)"] exI[of _ "(True, L 1)"] exI[of _ "(True, L 2)"]) simp_all
  show "MZ.N5_chain" unfolding MZ.N5_chain_def
    by (intro exI[of _ "(True, L 0)"] exI[of _ "(True, L 1)"] exI[of _ "(True, L 2)"]
          exI[of _ "(True, L 3)"]) (simp add: MZ_PG)
  have "{(True, L 1)} \<in> {\<Gamma>. GZ \<Gamma> (True, L 2)}" "{(True, L 1)} \<notin> {\<Gamma>. GZ \<Gamma> (True, L 0)}"
    by (auto simp: GZ_single)
  thus "MZ.N4_pair (True, L 0) (ngV (ngV (True, L 0)))"
    unfolding MZ.N4_pair_def by (auto simp: ngV_def numeral_2_eq_2)
qed

lemma MZ_N4s: "MZ.N4_pairs" using MZ.N4_dn[OF MZ_N4] .

lemma GZ_exq: "fst (f a) \<Longrightarrow> GZ {f a} (exqV f)"
proof -
  assume A: "fst (f a)"
  hence "\<exists>p. fst (f p)" by blast
  hence e: "exqV f = (True, Top 0)" unfolding exqV_def by simp
  show "GZ {f a} (exqV f)" unfolding e using A by (simp add: GZ_single)
qed

lemma MZ_allq: "\<forall>b. fst (f b) \<Longrightarrow> MZ.PG (f a) (allqV f)"
proof -
  assume A: "\<forall>b. fst (f b)"
  hence e: "allqV f = (True, Top 0)" unfolding allqV_def by simp
  have "fst (f a)" using A by blast
  thus "MZ.PG (f a) (allqV f)" unfolding e MZ_PG by simp
qed

lemma MZ_intro: "MZ.EX_FULL" "MZ.ALL_PART"
  unfolding MZ.EX_FULL_def MZ.ALL_PART_def using GZ_exq MZ_allq by blast+
lemma MZ2_intro: "MZ2.EX_FULL" "MZ2.ALL_PART"
  unfolding MZ2.EX_FULL_def MZ2.ALL_PART_def using GZ_exq MZ_allq by blast+

lemma MZ_rules: "MZ.DISJ_ONE" "MZ.TR_FULL" "MZ.TR_NEG" "MZ.NEG_DN"
  by (auto simp: MZ.DISJ_ONE_def MZ.TR_FULL_def MZ.TR_NEG_def MZ.NEG_DN_def GZ_single
        djV_def trV_def ngV_def blw_mx1 blw_mx2 blw_up blw_up2)

lemma MZ_TRANS_P: "MZ.TRANS_P"
  unfolding MZ.TRANS_P_def MZ_PG using blw_trans by blast

lemma MZ_FIN_B3: "MZ.FIN_B3" by (auto simp: MZ.FIN_B3_def GZ_def)
lemma MZ_EMPTY_NONE: "MZ.EMPTY_NONE" by (simp add: MZ.EMPTY_NONE_def GZ_def)

lemma MZ_IRR_W: "MZ.IRR_W"
  unfolding MZ.IRR_W_def
proof (intro allI impI)
  fix \<Gamma> c assume A: "GZ \<Gamma> c \<and> c \<in> \<Gamma>"
  hence g: "\<Gamma> = {c}" "fst c" "blw (snd c) (snd c)" unfolding GZ_def by auto
  obtain k where top: "snd c = Top k" using g(3) blw_refl by blast
  have all: "GZ {B} c" if "fst B" for B using that g(2) top by (simp add: GZ_single)
  have "\<Gamma> = (\<lambda>\<phi>. MZ.den ((\<lambda>_. c)(0:=c)) \<phi>) ` {Var 0}
      \<and> (\<exists>\<phi>\<in>{Var 0}. (0::nat) \<in> fv \<phi>)
      \<and> (\<forall>\<phi>\<in>{Var 0}. \<forall>\<psi>\<in>subf \<phi>. (0::nat) \<notin> fv \<psi> \<longrightarrow> MZ.den ((\<lambda>_. c)(0:=c)) \<psi> \<noteq> c)
      \<and> (\<forall>B. (\<forall>\<phi>\<in>{Var 0}. fst (MZ.den ((\<lambda>_. c)(0:=B)) \<phi>))
            \<longrightarrow> GZ ((\<lambda>\<phi>. MZ.den ((\<lambda>_. c)(0:=B)) \<phi>) ` {Var 0}) c)"
    using g(1) all by simp
  thus "MZ.vacW c \<Gamma> c" unfolding MZ.vacW_def by blast
qed

text \<open>The entries that mention neither ground nor admissibility are those of MV; the
  witness entries at C2 are those of MV2.\<close>
theorem MZ_package:
  "MZ.FACT \<and> MZ.LAM_CORE \<and> MZ.C3s \<and> MZ.W_ID \<and> MZ.W_TR \<and> MZ.W_EM \<and> MZ.W_TEM \<and> MZ.BETA_ID
   \<and> MZ.CL_PROP \<and> MZ.CL_QUANT \<and> MZ.TS_FULL \<and> MZ.EX_FULL \<and> MZ.ALL_PART \<and> MZ.DISJ_ONE
   \<and> MZ.TR_FULL \<and> MZ.TR_NEG \<and> MZ.NEG_DN \<and> MZ.TRANS_P \<and> MZ.FIN_B3 \<and> MZ.EMPTY_NONE \<and> MZ.IRR_W
   \<and> MZ.N1 \<and> MZ.N2 \<and> MZ.N4_pairs \<and> MZ.N5_chain"
  using MV_package MZ_core MZ_N4s MZ_intro MZ_rules MZ_TRANS_P MZ_FIN_B3 MZ_EMPTY_NONE MZ_IRR_W
  by blast

theorem MZ2_package:
  "MZ2.FACT \<and> MZ2.LAM_CORE \<and> MZ2.C2 1 \<and> MZ2.W_ID \<and> MZ2.W_TR \<and> MZ2.W_EM \<and> MZ2.W_TEM \<and> MZ2.BETA_ID
   \<and> MZ2.CL_PROP \<and> MZ2.CL_QUANT \<and> MZ2.TS_FULL \<and> MZ2.EX_FULL \<and> MZ2.ALL_PART \<and> MZ2.DISJ_ONE
   \<and> MZ2.TR_FULL \<and> MZ2.TR_NEG \<and> MZ2.NEG_DN \<and> MZ2.TRANS_P \<and> MZ2.FIN_B3 \<and> MZ2.EMPTY_NONE \<and> MZ2.IRR_W
   \<and> MZ2.N1 \<and> MZ2.N2 \<and> MZ2.N4_pairs \<and> MZ2.N5_chain"
  using MZ_package MV2_package MZ2_intro by blast

text \<open>N3 for the entries of MZ: the instances of MV_N3 with one-membered grounds, and for
  ALL.PART the instance (True, L 2) of p \<or> \<not>p at (True, L 0).\<close>
lemma MZ_N3:
  "GZ {(True, L 0)} (exqV (\<lambda>p. p)) \<and> exqV (\<lambda>p. p) \<noteq> (True, L 0)"
  "MZ.PG (djV (True, L 0) (ngV (True, L 0))) (allqV (\<lambda>p. djV p (ngV p)))
     \<and> djV (True, L 0) (ngV (True, L 0)) = (True, L 2) \<and> allqV (\<lambda>p. djV p (ngV p)) = (True, Top 0)"
  "GZ {(True, L 0)} (djV (True, L 0) (False, L 1)) \<and> djV (True, L 0) (False, L 1) = (True, L 2)"
  "GZ {(True, L 0)} (trV (True, L 0)) \<and> trV (True, L 0) = (True, L 1)"
proof -
  have e: "exqV (\<lambda>p. p) = (True, Top 0)" unfolding exqV_def by auto
  show "GZ {(True, L 0)} (exqV (\<lambda>p. p)) \<and> exqV (\<lambda>p. p) \<noteq> (True, L 0)"
    unfolding e by (simp add: GZ_single)
  have a: "allqV (\<lambda>p. djV p (ngV p)) = (True, Top 0)"
    unfolding allqV_def by (simp add: djV_def ngV_def)
  have d: "djV (True, L 0) (ngV (True, L 0)) = (True, L 2)"
    by (simp add: djV_def ngV_def numeral_2_eq_2)
  show "MZ.PG (djV (True, L 0) (ngV (True, L 0))) (allqV (\<lambda>p. djV p (ngV p)))
     \<and> djV (True, L 0) (ngV (True, L 0)) = (True, L 2) \<and> allqV (\<lambda>p. djV p (ngV p)) = (True, Top 0)"
    unfolding a d by (simp add: MZ_PG)
  show "GZ {(True, L 0)} (djV (True, L 0) (False, L 1)) \<and> djV (True, L 0) (False, L 1) = (True, L 2)"
    by (simp add: GZ_single djV_def numeral_2_eq_2)
  show "GZ {(True, L 0)} (trV (True, L 0)) \<and> trV (True, L 0) = (True, L 1)"
    by (simp add: GZ_single trV_def)
qed

section \<open>Part 7. TS.KF in the models\<close>

text \<open>Every model of this theory has CL.PROP and TS.FULL, hence TS.KF (gsig.cl_ts_kf).\<close>
theorem woods_models_TS_KF:
  "MW.TS_KF" "MV.TS_KF" "MV1.TS_KF" "MV2.TS_KF" "MV3.TS_KF" "MY.TS_KF" "MY2.TS_KF"
  "MZ.TS_KF" "MZ2.TS_KF"
  using MW_package MW.cl_ts_kf apply blast
  using MV_package MV.cl_ts_kf apply blast
  using MV1_package MV1.cl_ts_kf apply blast
  using MV2_package MV2.cl_ts_kf apply blast
  using MV3_package MV3.cl_ts_kf apply blast
  using MY_package MY.cl_ts_kf apply blast
  using MY2_package MY2.cl_ts_kf apply blast
  using MZ_package MZ.cl_ts_kf apply blast
  using MZ2_package MZ2.cl_ts_kf by blast

section \<open>Part 8. ALL.TOT in MV\<close>

text \<open>Interpret tot by a constant function whose value is a truth of the lowest level.
  In MV a true universal proposition is grounded by every non-empty set of truths, so
  the instances together with the totality fact ground it, whatever functions are
  admissible. Since tot occurs in no other entry, the packages of MV, MV1, MV2 and MV3
  hold together with ALL.TOT.

  This settles the registry entry only. It does not test Woods's reply to Objection 5
  (p. 645), where the totality fact is itself rewritten when a ground is replaced: the
  formula language has no constructor for totality facts, so vacW cannot mark an
  occurrence inside one.\<close>
theorem MV_ALL_TOT:
  "ALL_TOT_at (fst :: pv \<Rightarrow> bool) (\<lambda>(f :: pv \<Rightarrow> pv) p. f p) allqV adm' GV (\<lambda>_. (True, L 0))"
  unfolding ALL_TOT_at_def
proof (intro allI impI conjI)
  fix f :: "pv \<Rightarrow> pv" assume A: "adm' f \<and> (\<forall>a. fst (f a))"
  show "fst (True, L 0)" by simp
  have e: "allqV f = (True, Top 0)" unfolding allqV_def using A by simp
  have "\<forall>p\<in>insert (True, L 0) (range f). fst p" using A by auto
  thus "GV (insert (True, L 0) (range f)) (allqV f)" unfolding e GV_def by simp
qed

section \<open>Part 9. Model MQ: a zero-grounded truth (EMPTY.SOME)\<close>

text \<open>MV with one more grounding fact: the empty set grounds the atom (True, L 0). Partial
  ground is unchanged, because the new fact has no members; so are the reflexive facts.\<close>
definition GQ :: "pv set \<Rightarrow> pv \<Rightarrow> bool" where
  "GQ \<Gamma> q \<longleftrightarrow> GV \<Gamma> q \<or> (\<Gamma> = {} \<and> q = (True, L 0))"

interpretation MQ: gsig "fst :: pv \<Rightarrow> bool" "\<lambda>_. (True, L 0)" ngV cjV djV trV
  "\<lambda>(f :: pv \<Rightarrow> pv) p. f p" exqV allqV bigV lamV "\<lambda>_. True" GQ "\<lambda>_. (True, L 0)" "(True, L 0)" .
interpretation MQ2: gsig "fst :: pv \<Rightarrow> bool" "\<lambda>_. (True, L 0)" ngV cjV djV trV
  "\<lambda>(f :: pv \<Rightarrow> pv) p. f p" exqV allqV bigV lamV admV2 GQ "\<lambda>_. (True, L 0)" "(True, L 0)" .

lemma GQ_mono: "GV \<Gamma> q \<Longrightarrow> GQ \<Gamma> q" unfolding GQ_def by blast
lemma GQ_mem: "GQ \<Gamma> q \<Longrightarrow> p \<in> \<Gamma> \<Longrightarrow> GV \<Gamma> q" unfolding GQ_def by blast

lemma MQ_PG: "MQ.PG p q \<longleftrightarrow> MV.PG p q"
  unfolding MQ.PG_def MV.PG_def using GQ_mono GQ_mem by blast

lemma MQ_core: "MQ.FACT" "MQ.N1" "MQ.N2" "MQ.N5_chain" "MQ.EMPTY_SOME"
  and MQ_N4: "MQ.N4_pair (True, L 0) (ngV (ngV (True, L 0)))"
proof -
  show "MQ.FACT" by (auto simp: MQ.FACT_def GQ_def GV_def)
  have g: "GQ {(True, L 0)} (True, L 1)" by (simp add: GQ_def GV_single)
  show "MQ.N1" unfolding MQ.N1_def using g by blast
  thus "MQ.N2" unfolding MQ.N2_def
    by (intro conjI exI[of _ "(True, L 0)"] exI[of _ "(True, L 1)"] exI[of _ "(True, L 2)"]) simp_all
  show "MQ.N5_chain" unfolding MQ.N5_chain_def
    by (intro exI[of _ "(True, L 0)"] exI[of _ "(True, L 1)"] exI[of _ "(True, L 2)"]
          exI[of _ "(True, L 3)"]) (simp add: MQ_PG MV_PG)
  show "MQ.EMPTY_SOME" unfolding MQ.EMPTY_SOME_def GQ_def by blast
  have "{(True, L 1)} \<in> {\<Gamma>. GQ \<Gamma> (True, L 2)}" "{(True, L 1)} \<notin> {\<Gamma>. GQ \<Gamma> (True, L 0)}"
    by (auto simp: GQ_def GV_single)
  thus "MQ.N4_pair (True, L 0) (ngV (ngV (True, L 0)))"
    unfolding MQ.N4_pair_def by (auto simp: ngV_def numeral_2_eq_2)
qed

lemma MQ_N4s: "MQ.N4_pairs" using MQ.N4_dn[OF MQ_N4] .

lemma MQ_intro: "MQ.EX_FULL" "MQ.ALL_INST"
  unfolding MQ.EX_FULL_def MQ.ALL_INST_def MQ.inst_def using GV_exq GV_allq GQ_mono by blast+
lemma MQ2_intro: "MQ2.EX_FULL" "MQ2.ALL_INST"
  unfolding MQ2.EX_FULL_def MQ2.ALL_INST_def MQ2.inst_def using GV_exq GV_allq GQ_mono by blast+

lemma MQ_rules: "MQ.DISJ_ONE" "MQ.TR_FULL"
proof -
  have "MV.DISJ_ONE" "MV.TR_FULL" using MV_package by blast+
  thus "MQ.DISJ_ONE" "MQ.TR_FULL"
    unfolding MV.DISJ_ONE_def MV.TR_FULL_def MQ.DISJ_ONE_def MQ.TR_FULL_def
    using GQ_mono by blast+
qed

lemma MQ_TRANS_P: "MQ.TRANS_P"
proof -
  have "MV.TRANS_P" using MV_package by blast
  thus ?thesis unfolding MV.TRANS_P_def MQ.TRANS_P_def MQ_PG .
qed

text \<open>A reflexive fact of MQ is one of MV, so its conclusion is in the tier Top, and
  the grounds with a truth put for the conclusion ground it (IRR_W_coded).\<close>
lemma MQ_IRR_W: "MQ.IRR_W"
proof (rule MQ.IRR_W_coded[of dec idx])
  show "dec (idx p) = p" for p by (rule dec_idx)
next
  fix \<Gamma> :: "pv set" and c B
  assume g: "GQ \<Gamma> c" and m: "c \<in> \<Gamma>" and t: "\<forall>q\<in>(\<lambda>p. if p = c then B else p) ` \<Gamma>. fst q"
  have gv: "GV \<Gamma> c" using g m GQ_mem by blast
  hence "blw (snd c) (snd c)" using m unfolding GV_def by blast
  then obtain k where top: "snd c = Top k" using blw_refl by blast
  have ne: "(\<lambda>p. if p = c then B else p) ` \<Gamma> \<noteq> {}" using m by blast
  have "fst c" using gv unfolding GV_def by blast
  hence "GV ((\<lambda>p. if p = c then B else p) ` \<Gamma>) c" unfolding GV_def using ne t top by simp
  thus "GQ ((\<lambda>p. if p = c then B else p) ` \<Gamma>) c" by (rule GQ_mono)
qed

theorem MQ_package:
  "MQ.FACT \<and> MQ.LAM_CORE \<and> MQ.C3s \<and> MQ.W_ID \<and> MQ.W_TR \<and> MQ.W_EM \<and> MQ.W_TEM \<and> MQ.BETA_ID
   \<and> MQ.CL_PROP \<and> MQ.CL_QUANT \<and> MQ.TS_FULL \<and> MQ.TS_KF \<and> MQ.EX_FULL \<and> MQ.ALL_INST \<and> MQ.DISJ_ONE
   \<and> MQ.TR_FULL \<and> MQ.TRANS_P \<and> MQ.EMPTY_SOME \<and> MQ.IRR_W
   \<and> MQ.N1 \<and> MQ.N2 \<and> MQ.N4_pairs \<and> MQ.N5_chain"
  using MV_package woods_models_TS_KF(2) MQ_core MQ_N4s MQ_intro MQ_rules MQ_TRANS_P MQ_IRR_W
  by blast

theorem MQ2_package:
  "MQ2.FACT \<and> MQ2.LAM_CORE \<and> MQ2.C2 1 \<and> MQ2.W_ID \<and> MQ2.W_TR \<and> MQ2.W_EM \<and> MQ2.W_TEM \<and> MQ2.BETA_ID
   \<and> MQ2.CL_PROP \<and> MQ2.CL_QUANT \<and> MQ2.TS_FULL \<and> MQ2.TS_KF \<and> MQ2.EX_FULL \<and> MQ2.ALL_INST \<and> MQ2.DISJ_ONE
   \<and> MQ2.TR_FULL \<and> MQ2.TRANS_P \<and> MQ2.EMPTY_SOME \<and> MQ2.IRR_W
   \<and> MQ2.N1 \<and> MQ2.N2 \<and> MQ2.N4_pairs \<and> MQ2.N5_chain"
  using MQ_package MV2_package MQ2_intro by blast

section \<open>Part 10. Model MX: the identity entries TS.ID, ID.AC and ID.DN\<close>

text \<open>A flat model. Propositions are a truth value with a number; negation flips the
  truth value and keeps the number, conjunction and disjunction take the maximum, the
  truth operator is the identity, and quantified propositions have number 0. Every
  non-empty set of truths grounds every truth. All three identity entries hold.

  Level: N4 fails, and must fail in any model of ID.AC with ID.DN (id_ac_dn_no_N4). In
  MX it fails more simply, since all truths have the same full grounds. N3 holds for the
  quantifier and disjunction entries (MX_N3) and fails for the truth entry, whose
  instances have the form: p grounds p.\<close>
type_synonym px = "bool \<times> nat"
definition ngX :: "px \<Rightarrow> px" where "ngX p = (\<not> fst p, snd p)"
definition cjX :: "px \<Rightarrow> px \<Rightarrow> px" where "cjX p q = (fst p \<and> fst q, max (snd p) (snd q))"
definition djX :: "px \<Rightarrow> px \<Rightarrow> px" where "djX p q = (fst p \<or> fst q, max (snd p) (snd q))"

primrec dX :: "(nat \<Rightarrow> px) \<Rightarrow> fm \<Rightarrow> px" where
  "dX v (Var n) = v n"
| "dX v (Cst n) = (True, 0)"
| "dX v (Neg a) = ngX (dX v a)"
| "dX v (Conj a b) = cjX (dX v a) (dX v b)"
| "dX v (Disj a b) = djX (dX v a) (dX v b)"
| "dX v (Tr a) = dX v a"
| "dX v (Ex x a) = ((\<exists>p. fst (dX (v(x:=p)) a)), 0)"
| "dX v (All x a) = ((\<forall>p. fst (dX (v(x:=p)) a)), 0)"
| "dX v (BigC x a) = ((\<forall>p. fst (dX (v(x:=p)) a) \<longrightarrow> fst p), 0)"

definition lamX :: "nat \<Rightarrow> fm \<Rightarrow> (nat \<Rightarrow> px) \<Rightarrow> px \<Rightarrow> px" where
  "lamX x a v = (\<lambda>p. dX (v(x:=p)) a)"
definition exqX :: "(px \<Rightarrow> px) \<Rightarrow> px" where "exqX f = ((\<exists>p. fst (f p)), 0)"
definition allqX :: "(px \<Rightarrow> px) \<Rightarrow> px" where "allqX f = ((\<forall>p. fst (f p)), 0)"
definition bigX :: "(px \<Rightarrow> px) \<Rightarrow> px" where "bigX f = ((\<forall>p. fst (f p) \<longrightarrow> fst p), 0)"
definition GX :: "px set \<Rightarrow> px \<Rightarrow> bool" where
  "GX \<Gamma> q \<longleftrightarrow> \<Gamma> \<noteq> {} \<and> fst q \<and> (\<forall>p\<in>\<Gamma>. fst p)"
definition admX2 :: "(px \<Rightarrow> px) \<Rightarrow> bool" where
  "admX2 f \<longleftrightarrow> (\<exists>x a v. lvl a \<le> 1 \<and> f = lamX x a v)"

interpretation MX: gsig "fst :: px \<Rightarrow> bool" "\<lambda>_. (True, 0)" ngX cjX djX "\<lambda>p. p"
  "\<lambda>(f :: px \<Rightarrow> px) p. f p" exqX allqX bigX lamX "\<lambda>_. True" GX "\<lambda>_. (True, 0)" "(True, 0)" .
interpretation MX2: gsig "fst :: px \<Rightarrow> bool" "\<lambda>_. (True, 0)" ngX cjX djX "\<lambda>p. p"
  "\<lambda>(f :: px \<Rightarrow> px) p. f p" exqX allqX bigX lamX admX2 GX "\<lambda>_. (True, 0)" "(True, 0)" .

lemma quantX:
  "exqX (lamX x a v) = ((\<exists>p. fst (dX (v(x:=p)) a)), 0)"
  "allqX (lamX x a v) = ((\<forall>p. fst (dX (v(x:=p)) a)), 0)"
  "bigX (lamX x a v) = ((\<forall>p. fst (dX (v(x:=p)) a) \<longrightarrow> fst p), 0)"
  by (simp_all add: lamX_def exqX_def allqX_def bigX_def)

lemma MX_den: "MX.den = dX"
proof (intro ext)
  fix v a show "MX.den v a = dX v a"
    by (induction a) (simp_all add: quantX)
qed

lemma dX_fv: "(\<forall>y\<in>fv a. v y = w y) \<Longrightarrow> dX v a = dX w a"
proof (induct a arbitrary: v w)
  case (Ex x a)
  have "\<And>p. dX (v(x:=p)) a = dX (w(x:=p)) a"
    by (rule Ex.hyps) (use Ex.prems in auto)
  then show ?case by simp
next
  case (All x a)
  have "\<And>p. dX (v(x:=p)) a = dX (w(x:=p)) a"
    by (rule All.hyps) (use All.prems in auto)
  then show ?case by simp
next
  case (BigC x a)
  have "\<And>p. dX (v(x:=p)) a = dX (w(x:=p)) a"
    by (rule BigC.hyps) (use BigC.prems in auto)
  then show ?case by simp
next
  case (Neg a)
  have "dX v a = dX w a" by (rule Neg.hyps) (use Neg.prems in auto)
  then show ?case by simp
next
  case (Tr a)
  have "dX v a = dX w a" by (rule Tr.hyps) (use Tr.prems in auto)
  then show ?case by simp
next
  case (Conj a b)
  have "dX v a = dX w a" by (rule Conj.hyps(1)) (use Conj.prems in auto)
  moreover have "dX v b = dX w b" by (rule Conj.hyps(2)) (use Conj.prems in auto)
  ultimately show ?case by simp
next
  case (Disj a b)
  have "dX v a = dX w a" by (rule Disj.hyps(1)) (use Disj.prems in auto)
  moreover have "dX v b = dX w b" by (rule Disj.hyps(2)) (use Disj.prems in auto)
  ultimately show ?case by simp
qed simp_all

lemma lamX_fv: "\<forall>y\<in>fv a - {x}. v y = w y \<Longrightarrow> lamX x a v = lamX x a w"
  unfolding lamX_def by (intro ext dX_fv) auto

lemma GX_single: "GX {p} q \<longleftrightarrow> fst p \<and> fst q" unfolding GX_def by auto

lemma MX_PG: "MX.PG p q \<longleftrightarrow> fst p \<and> fst q"
proof
  assume "MX.PG p q"
  thus "fst p \<and> fst q" unfolding MX.PG_def GX_def by auto
next
  assume A: "fst p \<and> fst q"
  have "p \<in> {p} \<and> GX {p} q" using A by (simp add: GX_single)
  thus "MX.PG p q" unfolding MX.PG_def by (rule exI)
qed

lemma MX_core: "MX.FACT" "MX.LAM_CORE" "MX.N1" "MX.N2" "MX.N5_chain"
proof -
  show "MX.FACT" by (auto simp: MX.FACT_def GX_def)
  show "MX.LAM_CORE" unfolding MX.LAM_CORE_def MX_den using lamX_fv by (simp add: lamX_def)
  have g: "GX {(True, 0)} (True, 1)" by (simp add: GX_single)
  show "MX.N1" unfolding MX.N1_def using g by blast
  thus "MX.N2" unfolding MX.N2_def
    by (intro conjI exI[of _ "(True, 0)"] exI[of _ "(True, 1)"] exI[of _ "(True, 2)"]) simp_all
  show "MX.N5_chain" unfolding MX.N5_chain_def
    by (intro exI[of _ "(True, 0)"] exI[of _ "(True, 1)"] exI[of _ "(True, 2)"]
          exI[of _ "(True, 3)"]) (simp add: MX_PG)
qed

lemma MX_C3s: "MX.C3s" unfolding MX.C3s_def by auto
lemma MX_W: "MX.W_ID" "MX.W_TR" "MX.W_EM" "MX.W_TEM"
  by (simp_all add: MX.W_ID_def MX.W_TR_def MX.W_EM_def MX.W_TEM_def)
lemma MX_BETA_ID: "MX.BETA_ID" by (simp add: MX.BETA_ID_def MX_den lamX_def)
lemma MX_classical: "MX.CL_PROP" "MX.CL_QUANT" "MX.TS_FULL"
  by (simp_all add: MX.CL_PROP_def MX.CL_QUANT_def MX.TS_FULL_def ngX_def cjX_def djX_def
        exqX_def allqX_def bigX_def MX.sat_def)

lemma MX_ids: "MX.TS_ID" "MX.ID_AC" "MX.ID_DN"
  by (auto simp: MX.TS_ID_def MX.ID_AC_def MX.ID_DN_def ngX_def cjX_def djX_def)

lemma GX_exq: "fst (f a) \<Longrightarrow> GX {f a} (exqX f)"
proof -
  assume A: "fst (f a)"
  hence "\<exists>p. fst (f p)" by blast
  hence e: "exqX f = (True, 0)" unfolding exqX_def by simp
  show "GX {f a} (exqX f)" unfolding e using A by (simp add: GX_single)
qed

lemma GX_allq: "\<forall>a. fst (f a) \<Longrightarrow> GX (range f) (allqX f)"
proof -
  assume A: "\<forall>a. fst (f a)"
  hence e: "allqX f = (True, 0)" unfolding allqX_def by simp
  show "GX (range f) (allqX f)" unfolding e GX_def using A by auto
qed

lemma MX_intro: "MX.EX_FULL" "MX.ALL_INST"
  unfolding MX.EX_FULL_def MX.ALL_INST_def MX.inst_def using GX_exq GX_allq by blast+
lemma MX2_intro: "MX2.EX_FULL" "MX2.ALL_INST"
  unfolding MX2.EX_FULL_def MX2.ALL_INST_def MX2.inst_def using GX_exq GX_allq by blast+

lemma MX_rules: "MX.DISJ_ONE" "MX.DISJ_BOTH" "MX.CONJ_BIN" "MX.TR_FULL" "MX.NEG_DN"
  by (auto simp: MX.DISJ_ONE_def MX.DISJ_BOTH_def MX.CONJ_BIN_def MX.TR_FULL_def MX.NEG_DN_def
        GX_def djX_def cjX_def ngX_def)

lemma MX_TRANS_P: "MX.TRANS_P" unfolding MX.TRANS_P_def MX_PG by blast

definition idxX :: "px \<Rightarrow> nat" where "idxX p = 2 * snd p + (if fst p then 1 else 0)"
definition decX :: "nat \<Rightarrow> px" where "decX k = (odd k, k div 2)"
lemma decX_idxX: "decX (idxX p) = p" by (cases p) (simp add: decX_def idxX_def)

lemma MX_IRR_W: "MX.IRR_W"
proof (rule MX.IRR_W_coded[of decX idxX])
  show "decX (idxX p) = p" for p by (rule decX_idxX)
next
  fix \<Gamma> :: "px set" and c B
  assume g: "GX \<Gamma> c" and "c \<in> \<Gamma>" and t: "\<forall>q\<in>(\<lambda>p. if p = c then B else p) ` \<Gamma>. fst q"
  have "(\<lambda>p. if p = c then B else p) ` \<Gamma> \<noteq> {}" using g unfolding GX_def by blast
  thus "GX ((\<lambda>p. if p = c then B else p) ` \<Gamma>) c" using g t unfolding GX_def by blast
qed

lemma MX_N4_fails: "\<not> MX.N4_pairs" using MX.ids_no_N4 MX_ids by blast

theorem MX_package:
  "MX.FACT \<and> MX.LAM_CORE \<and> MX.C3s \<and> MX.W_ID \<and> MX.W_TR \<and> MX.W_EM \<and> MX.W_TEM \<and> MX.BETA_ID
   \<and> MX.CL_PROP \<and> MX.CL_QUANT \<and> MX.TS_FULL \<and> MX.TS_ID \<and> MX.ID_AC \<and> MX.ID_DN
   \<and> MX.EX_FULL \<and> MX.ALL_INST \<and> MX.DISJ_ONE \<and> MX.DISJ_BOTH \<and> MX.CONJ_BIN \<and> MX.TR_FULL \<and> MX.NEG_DN
   \<and> MX.TRANS_P \<and> MX.IRR_W \<and> MX.N1 \<and> MX.N2 \<and> MX.N5_chain \<and> \<not> MX.N4_pairs"
  using MX_core MX_C3s MX_W MX_BETA_ID MX_classical MX_ids MX_intro MX_rules MX_TRANS_P MX_IRR_W
    MX_N4_fails by blast

lemma MX2_C2: "MX2.C2 1" by (simp add: MX2.C2_def admX2_def)
lemma MX2_W: "MX2.W_ID" "MX2.W_TR" "MX2.W_EM" "MX2.W_TEM"
proof -
  have "admX2 (lamX x a v)" if "lvl a \<le> 1" for x a v unfolding admX2_def using that by blast
  thus "MX2.W_ID" "MX2.W_TR" "MX2.W_EM" "MX2.W_TEM"
    unfolding MX2.W_ID_def MX2.W_TR_def MX2.W_EM_def MX2.W_TEM_def
              MX2.f_id_def MX2.f_tr_def MX2.f_em_def MX2.f_tem_def by simp_all
qed

theorem MX2_package:
  "MX2.FACT \<and> MX2.LAM_CORE \<and> MX2.C2 1 \<and> MX2.W_ID \<and> MX2.W_TR \<and> MX2.W_EM \<and> MX2.W_TEM \<and> MX2.BETA_ID
   \<and> MX2.CL_PROP \<and> MX2.CL_QUANT \<and> MX2.TS_FULL \<and> MX2.TS_ID \<and> MX2.ID_AC \<and> MX2.ID_DN
   \<and> MX2.EX_FULL \<and> MX2.ALL_INST \<and> MX2.DISJ_ONE \<and> MX2.DISJ_BOTH \<and> MX2.CONJ_BIN \<and> MX2.TR_FULL \<and> MX2.NEG_DN
   \<and> MX2.TRANS_P \<and> MX2.IRR_W \<and> MX2.N1 \<and> MX2.N2 \<and> MX2.N5_chain \<and> \<not> MX2.N4_pairs"
  using MX_package MX2_C2 MX2_W MX2_intro by blast

text \<open>N3 for the quantifier entries and DISJ.ONE: instances whose grounded proposition
  is not among its grounds. For ALL.INST the function is a constant one, which a formula
  of level 0 presents under a suitable environment, so it is admissible in MX2 as well.
  No such instance exists for TR.FULL (tr p = p), NEG.DN (\<not>\<not>p = p), CONJ.BIN or DISJ.BOTH
  (the compound of two truths is one of them).\<close>
lemma MX_N3:
  "GX {(True, 1)} (exqX (\<lambda>p. p)) \<and> exqX (\<lambda>p. p) \<noteq> (True, 1)"
  "GX (range (\<lambda>p :: px. (True, 1 :: nat))) (allqX (\<lambda>p. (True, 1)))
     \<and> allqX (\<lambda>p. (True, 1)) \<notin> range (\<lambda>p :: px. (True, 1 :: nat))"
  "admX2 (\<lambda>p. (True, 1))"
  "GX {(True, 0)} (djX (True, 0) (False, 1)) \<and> djX (True, 0) (False, 1) = (True, 1)"
proof -
  have e: "exqX (\<lambda>p. p) = (True, 0)" unfolding exqX_def by auto
  show "GX {(True, 1)} (exqX (\<lambda>p. p)) \<and> exqX (\<lambda>p. p) \<noteq> (True, 1)"
    unfolding e by (simp add: GX_single)
  have a: "allqX (\<lambda>p. (True, 1)) = (True, 0)" unfolding allqX_def by simp
  show "GX (range (\<lambda>p :: px. (True, 1 :: nat))) (allqX (\<lambda>p. (True, 1)))
     \<and> allqX (\<lambda>p. (True, 1)) \<notin> range (\<lambda>p :: px. (True, 1 :: nat))"
    unfolding a GX_def by auto
  have "lamX 0 (Var 1) (\<lambda>_. (True, 1)) = (\<lambda>p. (True, 1))" by (simp add: lamX_def)
  moreover have "lvl (Var 1) \<le> 1" by simp
  ultimately show "admX2 (\<lambda>p. (True, 1))" unfolding admX2_def by metis
  show "GX {(True, 0)} (djX (True, 0) (False, 1)) \<and> djX (True, 0) (False, 1) = (True, 1)"
    by (simp add: GX_single djX_def)
qed

end
