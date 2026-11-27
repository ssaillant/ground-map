theory Fritz_Main
  imports Signature
begin

text \<open>
  Fritz 2022 sect. 2.4 (pp. 308-310): the seven principles of immediate partial ground
  of sect. 2.2 (pp. 304-305) are inconsistent, without irreflexivity. Proved first for an
  arbitrary factive relation R, then for the defined immediate partial ground IPG (D1).
  Pluralities are sets of propositions; the proposition "p is one of X" is app (mem X) p
  for a function mem X given by C3s. tt is Fritz's constant t (the "that's all" truth or an
  arbitrary proposition). No axioms: all principles are hypotheses.
\<close>

consts tt :: prp

definition sq :: "prp \<Rightarrow> prp" where "sq x = conj x x"

locale fritz7 =
  fixes R :: "prp \<Rightarrow> prp \<Rightarrow> bool" and a b :: prp
  assumes FACT_R: "\<And>p q. R p q \<Longrightarrow> T p \<and> T q"
      and CL_neg: "\<And>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_conj: "\<And>p q. T (conj p q) \<longleftrightarrow> T p \<and> T q"
      and CL_disj: "\<And>p q. T (disj p q) \<longleftrightarrow> T p \<or> T q"
      and CL_all: "\<And>g. T (allq g) \<longleftrightarrow> (\<forall>x. T (app g x))"
      and A1: "\<And>p q. T p \<Longrightarrow> T q \<Longrightarrow> R p (conj p q) \<and> R q (conj p q)"
      and A2: "\<And>p q r. R r (conj p q) \<Longrightarrow> r = p \<or> r = q"
      and O1: "\<And>p q. T (disj p q) \<Longrightarrow> R p (disj p q) \<or> R q (disj p q)"
      and O2: "\<And>p q r. R r (disj p q) \<Longrightarrow> r = p \<or> r = q"
      and U1: "\<And>g x. T (allq g) \<Longrightarrow> R (app g x) (allq g)"
      and U2: "\<And>g q. R q (allq g) \<Longrightarrow> (\<forall>x. q \<noteq> app g x) \<Longrightarrow> q = tt"
      and Ta: "T a" and Tb: "T b" and ab: "a \<noteq> b"
begin

definition hc :: "prp \<Rightarrow> prp \<Rightarrow> prp" where
  "hc x y = conj (conj (conj a b) (sq x)) (conj (sq a) (sq y))"
definition hd :: "prp \<Rightarrow> prp \<Rightarrow> prp" where
  "hd x y = disj (conj (conj a b) (sq x)) (conj (sq a) (sq y))"

lemma T_sq: "T (sq x) \<longleftrightarrow> T x" unfolding sq_def using CL_conj by blast
lemma Tab: "T (conj a b)" using CL_conj Ta Tb by blast

lemma sq_ground: "T x \<Longrightarrow> R x (sq x)" unfolding sq_def using A1 by blast
lemma sq_only: "R r (sq x) \<Longrightarrow> r = x" unfolding sq_def using A2 by blast

lemma sq_inj: "T x \<Longrightarrow> sq x = sq y \<Longrightarrow> x = y"
  using sq_ground sq_only by metis

lemma ab_not_sq: "conj a b \<noteq> sq c"
proof
  assume e: "conj a b = sq c"
  have "R a (conj a b)" "R b (conj a b)" using A1 Ta Tb by blast+
  hence "a = c" "b = c" using e sq_only by metis+
  thus False using ab by simp
qed

lemma T_hc: "T (hc x y) \<longleftrightarrow> T x \<and> T y"
  unfolding hc_def using CL_conj T_sq Ta Tb by auto
lemma T_hd: "T (hd x y) \<longleftrightarrow> T x \<or> T y"
  unfolding hd_def using CL_conj CL_disj T_sq Ta Tb by auto

text \<open>The left block (a and b) and x-squared never equals a right block a-squared and y-squared once one side is true.\<close>
lemma left_ne_right:
  assumes "T x \<or> T y'"
  shows "conj (conj a b) (sq x) \<noteq> conj (sq a) (sq y')"
proof
  assume e: "conj (conj a b) (sq x) = conj (sq a) (sq y')"
  show False
  proof (cases "T x")
    case True
    hence "R (conj a b) (conj (conj a b) (sq x))" using A1 Tab T_sq by blast
    hence "conj a b = sq a \<or> conj a b = sq y'" using e A2 by metis
    thus False using ab_not_sq by blast
  next
    case False
    hence Ty: "T y'" using assms by blast
    hence "R (sq y') (conj (sq a) (sq y'))" using A1 T_sq Ta by blast
    hence "sq y' = conj a b \<or> sq y' = sq x" using e A2 by metis
    hence "sq y' = sq x" using ab_not_sq by metis
    hence "y' = x" using sq_inj Ty by metis
    thus False using False Ty by simp
  qed
qed

lemma left_inj:
  assumes "T x" "conj (conj a b) (sq x) = conj (conj a b) (sq x')"
  shows "x = x'"
proof -
  have "R (sq x) (conj (conj a b) (sq x))" using A1 Tab T_sq assms(1) by blast
  hence "sq x = conj a b \<or> sq x = sq x'" using assms(2) A2 by metis
  hence "sq x = sq x'" using ab_not_sq by metis
  thus ?thesis using sq_inj assms(1) by blast
qed

lemma right_inj:
  assumes "T y" "conj (sq a) (sq y) = conj (sq a) (sq y')"
  shows "y = y'"
proof -
  have "T (conj (sq a) (sq y))" using CL_conj T_sq Ta assms(1) by blast
  hence "T (conj (sq a) (sq y'))" using assms(2) by simp
  hence Ty': "T y'" using CL_conj T_sq by blast
  have "R (sq y) (conj (sq a) (sq y))" using A1 T_sq Ta assms(1) by blast
  hence 1: "sq y = sq a \<or> sq y = sq y'" using assms(2) A2 by metis
  have "R (sq y') (conj (sq a) (sq y'))" using A1 T_sq Ta Ty' by blast
  hence 2: "sq y' = sq a \<or> sq y' = sq y" using assms(2) A2 by metis
  have "sq y = sq y'" using 1 2 by metis
  thus ?thesis using sq_inj assms(1) by blast
qed

text \<open>Fritz's hat-conjunction principle, p. 309.\<close>
lemma hc_inj:
  assumes "T x" "T y" "hc x y = hc x' y'"
  shows "x = x' \<and> y = y'"
proof -
  have "T (hc x' y')" using assms T_hc by (metis (no_types))
  hence T': "T x'" "T y'" using T_hc by blast+
  have L: "R (conj (conj a b) (sq x)) (hc x y)" and Rr: "R (conj (sq a) (sq y)) (hc x y)"
    unfolding hc_def using A1 CL_conj Tab T_sq Ta assms(1,2) by blast+
  have "conj (conj a b) (sq x) = conj (conj a b) (sq x') \<or> conj (conj a b) (sq x) = conj (sq a) (sq y')"
    using L assms(3) A2 unfolding hc_def by metis
  hence "conj (conj a b) (sq x) = conj (conj a b) (sq x')" using left_ne_right assms(1) by blast
  hence xx: "x = x'" using left_inj assms(1) by blast
  have "conj (sq a) (sq y) = conj (conj a b) (sq x') \<or> conj (sq a) (sq y) = conj (sq a) (sq y')"
    using Rr assms(3) A2 unfolding hc_def by metis
  hence "conj (sq a) (sq y) = conj (sq a) (sq y')" using left_ne_right T'(1) by metis
  hence "y = y'" using right_inj assms(2) by blast
  thus ?thesis using xx by blast
qed

text \<open>Fritz's hat-disjunction principle, p. 309.\<close>
lemma hd_left:
  assumes "T x" "\<not> T y" "hd x y = hd x' y'"
  shows "x = x'"
proof -
  have "\<not> T (conj (sq a) (sq y))" using assms(2) CL_conj T_sq by blast
  hence nR: "\<not> R (conj (sq a) (sq y)) (hd x y)" using FACT_R by blast
  have "T (hd x y)" using T_hd assms(1) by blast
  hence "R (conj (conj a b) (sq x)) (hd x y)" using O1 nR unfolding hd_def by metis
  hence "conj (conj a b) (sq x) = conj (conj a b) (sq x') \<or> conj (conj a b) (sq x) = conj (sq a) (sq y')"
    using assms(3) O2 unfolding hd_def by metis
  hence "conj (conj a b) (sq x) = conj (conj a b) (sq x')" using left_ne_right assms(1) by blast
  thus ?thesis using left_inj assms(1) by blast
qed

lemma hd_right:
  assumes "T y" "\<not> T x" "hd x y = hd x' y'"
  shows "y = y'"
proof -
  have "\<not> T (conj (conj a b) (sq x))" using assms(2) CL_conj T_sq by blast
  hence nR: "\<not> R (conj (conj a b) (sq x)) (hd x y)" using FACT_R by blast
  have "T (hd x y)" using T_hd assms(1) by blast
  hence Rr: "R (conj (sq a) (sq y)) (hd x y)" using O1 nR unfolding hd_def by metis
  hence dj: "conj (sq a) (sq y) = conj (conj a b) (sq x') \<or> conj (sq a) (sq y) = conj (sq a) (sq y')"
    using assms(3) O2 unfolding hd_def by metis
  have Tr: "T (conj (sq a) (sq y))" using CL_conj T_sq Ta assms(1) by blast
  have ne: "conj (sq a) (sq y) \<noteq> conj (conj a b) (sq x')"
  proof
    assume e: "conj (sq a) (sq y) = conj (conj a b) (sq x')"
    hence "T (conj (conj a b) (sq x'))" using Tr by simp
    hence "T x'" using CL_conj T_sq by blast
    hence "conj (conj a b) (sq x') \<noteq> conj (sq a) (sq y)" using left_ne_right by blast
    thus False using e by simp
  qed
  have "conj (sq a) (sq y) = conj (sq a) (sq y')" using dj ne by blast
  thus ?thesis using right_inj assms(1) by blast
qed

text \<open>The formula phi(p, X) of p. 309, with "r is one of X" as the proposition m r.\<close>
definition phi :: "(prp \<Rightarrow> prp) \<Rightarrow> prp \<Rightarrow> prp" where
  "phi m p = hd (hc p (hd (m p) (neg (m p)))) (neg p)"

lemma T_phi: "T (phi m p)"
  unfolding phi_def using T_hd T_hc CL_neg by metis

text \<open>Fritz's lemma (L-phi), p. 309.\<close>
lemma L_phi:
  assumes "T p" "phi m p = phi m' q"
  shows "T (m p) \<longleftrightarrow> T (m' p)"
proof -
  have nn: "\<not> T (neg p)" using CL_neg assms(1) by blast
  have Tin: "T (hd (m p) (neg (m p)))" using T_hd CL_neg by blast
  have "T (hc p (hd (m p) (neg (m p))))" using T_hc assms(1) Tin by blast
  hence "hc p (hd (m p) (neg (m p))) = hc q (hd (m' q) (neg (m' q)))"
    using hd_left nn assms(2) unfolding phi_def by blast
  hence pq: "p = q" and e: "hd (m p) (neg (m p)) = hd (m' q) (neg (m' q))"
    using hc_inj assms(1) Tin by blast+
  show ?thesis
  proof (cases "T (m p)")
    case True
    hence "\<not> T (neg (m p))" using CL_neg by blast
    hence "m p = m' q" using hd_left True e by blast
    thus ?thesis using True pq by simp
  next
    case False
    hence "T (neg (m p))" using CL_neg by blast
    hence "neg (m p) = neg (m' q)" using hd_right False e by blast
    hence "T (neg (m' p))" using \<open>T (neg (m p))\<close> pq by simp
    thus ?thesis using False CL_neg by blast
  qed
qed

text \<open>(S-psi) and (T-psi), p. 310, for psi = allq g with app g = phi m.\<close>
lemma S_psi:
  assumes g: "app g = phi m" and g': "app g' = phi m'"
      and eq: "allq g = allq g'" and p: "T p" "T (m p)" "\<not> T (m' p)"
  shows False
proof -
  have Tg: "T (allq g)" using CL_all g T_phi by simp
  have Tg': "T (allq g')" using CL_all g' T_phi by simp
  have r1: "R (phi m p) (allq g')" using U1[OF Tg, of p] g eq by simp
  have "\<forall>x. phi m p \<noteq> app g' x"
  proof
    fix x show "phi m p \<noteq> app g' x"
    proof
      assume "phi m p = app g' x"
      hence "phi m p = phi m' x" using g' by simp
      thus False using L_phi p by blast
    qed
  qed
  hence t1: "phi m p = tt" using U2 r1 by blast
  have r2: "R (phi m' p) (allq g)" using U1[OF Tg', of p] g' eq by simp
  have "\<forall>x. phi m' p \<noteq> app g x"
  proof
    fix x show "phi m' p \<noteq> app g x"
    proof
      assume "phi m' p = app g x"
      hence "phi m' p = phi m x" using g by simp
      thus False using L_phi p by blast
    qed
  qed
  hence t2: "phi m' p = tt" using U2 r2 by blast
  have "phi m p = phi m' p" using t1 t2 by simp
  thus False using L_phi p by blast
qed

end

text \<open>The Cantorian step (p. 308), with plural comprehension given by C3s.\<close>
theorem fritz_main_generic:
  assumes "fritz7 R a b" and C3: "\<forall>h. \<exists>f. app f = h"
  shows False
proof -
  interpret F: fritz7 R a b by fact
  have bt: "\<not> T (neg a)" using F.CL_neg F.Ta by blast
  define mem where "mem X = (SOME f. app f = (\<lambda>p. if p \<in> X then a else neg a))" for X
  have app_mem: "app (mem X) = (\<lambda>p. if p \<in> X then a else neg a)" for X
  proof -
    have "\<exists>f. app f = (\<lambda>p. if p \<in> X then a else neg a)" using C3 by blast
    thus ?thesis unfolding mem_def by (rule someI_ex)
  qed
  have T_mem: "T (app (mem X) p) \<longleftrightarrow> p \<in> X" for X p
    using app_mem F.Ta bt by simp
  define gg where "gg X = (SOME g. app g = F.phi (app (mem X)))" for X
  have app_gg: "app (gg X) = F.phi (app (mem X))" for X
  proof -
    have "\<exists>g. app g = F.phi (app (mem X))" using C3 by blast
    thus ?thesis unfolding gg_def by (rule someI_ex)
  qed
  define psi where "psi X = allq (gg X)" for X
  let ?S = "{p. T p}"
  have psi_T: "psi X \<in> ?S" for X
    unfolding psi_def using F.CL_all app_gg F.T_phi by simp
  have psi_inj: "X = Y" if XY: "X \<subseteq> ?S" "Y \<subseteq> ?S" "psi X = psi Y" for X Y
  proof (rule ccontr)
    assume "X \<noteq> Y"
    then obtain p where "p \<in> X \<and> p \<notin> Y \<or> p \<in> Y \<and> p \<notin> X" by blast
    thus False
    proof
      assume p: "p \<in> X \<and> p \<notin> Y"
      have Tp: "T p" using p XY(1) by blast
      have e: "allq (gg X) = allq (gg Y)" using XY(3) unfolding psi_def .
      have "T (app (mem X) p)" "\<not> T (app (mem Y) p)" using p T_mem by blast+
      thus False using F.S_psi[OF app_gg[of X] app_gg[of Y] e Tp] by blast
    next
      assume p: "p \<in> Y \<and> p \<notin> X"
      have Tp: "T p" using p XY(2) by blast
      have e: "allq (gg Y) = allq (gg X)" using XY(3) unfolding psi_def by simp
      have "T (app (mem Y) p)" "\<not> T (app (mem X) p)" using p T_mem by blast+
      thus False using F.S_psi[OF app_gg[of Y] app_gg[of X] e Tp] by blast
    qed
  qed
  define D where "D = {p \<in> ?S. \<exists>X\<subseteq>?S. psi X = p \<and> p \<notin> X}"
  have DS: "D \<subseteq> ?S" unfolding D_def by blast
  show False
  proof (cases "psi D \<in> D")
    case True
    then obtain X where X: "X \<subseteq> ?S" "psi X = psi D" "psi D \<notin> X" unfolding D_def by blast
    hence "X = D" using psi_inj DS by blast
    thus False using X True by blast
  next
    case False
    hence "psi D \<in> D" using psi_T DS unfolding D_def by blast
    thus False using False by blast
  qed
qed

text \<open>Two distinct truths, from (nt), (and-1) and one truth (p. 308).\<close>
lemma two_truths:
  assumes CL_neg: "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_conj: "\<forall>p q. T (conj p q) \<longleftrightarrow> T p \<and> T q"
      and A1: "\<forall>p q. T p \<and> T q \<longrightarrow> R p (conj p q) \<and> R q (conj p q)"
      and NT: "\<not> (\<forall>p q. T p \<and> T q \<longrightarrow> R p q)"
  obtains a b where "T a" "T b" "a \<noteq> b"
proof -
  obtain c where c: "T c" using CL_neg by metis
  obtain p q where pq: "T p" "T q" "\<not> R p q" using NT by blast
  have "\<exists>a b. T a \<and> T b \<and> a \<noteq> b"
  proof (rule ccontr)
    assume "\<not> (\<exists>a b. T a \<and> T b \<and> a \<noteq> b)"
    hence one: "\<And>x y. T x \<Longrightarrow> T y \<Longrightarrow> x = y" by blast
    have "T (conj c c)" using CL_conj c by blast
    hence "conj c c = c" using one c by blast
    moreover have "R c (conj c c)" using A1 c by blast
    ultimately have "R c c" by simp
    moreover have "p = c" "q = c" using one pq c by blast+
    ultimately show False using pq by simp
  qed
  thus ?thesis using that by blast
qed

text \<open>Fritz's main result for the defined immediate partial ground IPG (D1).\<close>
lemma IPG_fact:
  assumes FACT: "\<forall>\<Gamma> p. G \<Gamma> p \<longrightarrow> T p \<and> (\<forall>q\<in>\<Gamma>. T q)"
  shows "IPG p q \<Longrightarrow> T p \<and> T q"
  using FACT unfolding IPG_def IG_def by blast

theorem fritz_main_imm:
  assumes FACT: "\<forall>\<Gamma> p. G \<Gamma> p \<longrightarrow> T p \<and> (\<forall>q\<in>\<Gamma>. T q)"
      and C3: "C3s"
      and CL_neg: "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and CL_conj: "\<forall>p q. T (conj p q) \<longleftrightarrow> T p \<and> T q"
      and CL_disj: "\<forall>p q. T (disj p q) \<longleftrightarrow> T p \<or> T q"
      and CL_all: "\<forall>g. T (allq g) \<longleftrightarrow> (\<forall>x. T (app g x))"
      and A1: "\<forall>p q. T p \<and> T q \<longrightarrow> IPG p (conj p q) \<and> IPG q (conj p q)"
      and A2: "\<forall>p q r. IPG r (conj p q) \<longrightarrow> r = p \<or> r = q"
      and O1: "\<forall>p q. T (disj p q) \<longrightarrow> IPG p (disj p q) \<or> IPG q (disj p q)"
      and O2: "\<forall>p q r. IPG r (disj p q) \<longrightarrow> r = p \<or> r = q"
      and U1: "\<forall>g x. adm g \<and> T (allq g) \<longrightarrow> IPG (app g x) (allq g)"
      and U2: "\<forall>g q. adm g \<and> IPG q (allq g) \<and> (\<forall>x. q \<noteq> app g x) \<longrightarrow> q = tt"
      and NT: "\<not> (\<forall>p q. T p \<and> T q \<longrightarrow> IPG p q)"
  shows False
proof -
  obtain a b where ab: "T a" "T b" "a \<noteq> b"
    using two_truths[of IPG] CL_neg CL_conj A1 NT by blast
  have adm: "\<forall>g. adm g" using C3 unfolding C3s_def by blast
  have "fritz7 IPG a b"
  proof (unfold_locales)
    fix p q assume "IPG p q" thus "T p \<and> T q" using IPG_fact[OF FACT] by blast
  next
    fix p show "T (neg p) \<longleftrightarrow> \<not> T p" using CL_neg by blast
  next
    fix p q show "T (conj p q) \<longleftrightarrow> T p \<and> T q" using CL_conj by blast
  next
    fix p q show "T (disj p q) \<longleftrightarrow> T p \<or> T q" using CL_disj by blast
  next
    fix g show "T (allq g) \<longleftrightarrow> (\<forall>x. T (app g x))" using CL_all by blast
  next
    fix p q assume "T p" "T q" thus "IPG p (conj p q) \<and> IPG q (conj p q)" using A1 by blast
  next
    fix p q r assume "IPG r (conj p q)" thus "r = p \<or> r = q" using A2 by blast
  next
    fix p q assume "T (disj p q)" thus "IPG p (disj p q) \<or> IPG q (disj p q)" using O1 by blast
  next
    fix p q r assume "IPG r (disj p q)" thus "r = p \<or> r = q" using O2 by blast
  next
    fix g x assume "T (allq g)" thus "IPG (app g x) (allq g)" using U1 adm by blast
  next
    fix g q assume "IPG q (allq g)" "\<forall>x. q \<noteq> app g x" thus "q = tt" using U2 adm by blast
  next
    show "T a" "T b" "a \<noteq> b" using ab by blast+
  qed
  moreover have "\<forall>h. \<exists>f. app f = h" using C3 unfolding C3s_def by blast
  ultimately show False using fritz_main_generic by blast
qed

end
