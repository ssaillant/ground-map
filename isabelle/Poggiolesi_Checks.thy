theory Poggiolesi_Checks
  imports Signature
begin

text \<open>
  Wilhelm's inconsistency and Poggiolesi's repair (poggiolesi2022, Logic and Logical
  Philosophy, doi:10.12775/LLP.2022.012; pages are the article's own, 1-6).

  Poggiolesi's language has atoms, the classical connectives, a relation symbol for
  immediate partial ground and one for ground-theoretic propositional identity, never
  nested (p. 2). We deep-embed the propositional part (atoms, negation, conjunction,
  disjunction; the conditional and biconditional occur in no condition and are left out)
  and treat the two relation symbols as arbitrary relations R (ground) and Q (identity)
  on formulas. A classical valuation e gives the truth of a formula.

  Three results.
  (A) Wilhelm's derivation, as Poggiolesi reconstructs it (p. 2), refutes conditions
      (1), (4), (5), (6), (7) for every R and Q such that Q is reflexive and symmetric and
      R respects Q in both places. A prp-level version for the defined immediate partial
      ground IPG, with identity of propositions as Q, follows.
  (B) The interpretation Poggiolesi gives (p. 5) violates condition (1). The
      counterexample needs only that her relation \<doteq> contains \<cong> (p. 4), so it holds
      on every reading of "the closure of \<cong> under (7') and (8')".
  (C) Her theorem (p. 4) is nevertheless true: a normal-form interpretation satisfies
      (1), (2'), (3), (4'), (5), (6), (7') and (8'), with Q an equivalence relation that is
      a congruence for conjunction, disjunction, double negation and the star operation
      and that R and truth respect. This is our reading of her Leibniz's law (p. 4).
  Nothing here is an axiom.
\<close>

datatype lf = LV nat | LN lf | LC lf lf | LD lf lf

primrec ev :: "(nat \<Rightarrow> bool) \<Rightarrow> lf \<Rightarrow> bool" where
  "ev e (LV n) = e n"
| "ev e (LN a) = (\<not> ev e a)"
| "ev e (LC a b) = (ev e a \<and> ev e b)"
| "ev e (LD a b) = (ev e a \<or> ev e b)"

text \<open>The star operation (p. 3): for A = (n negations) E with E not a negation, A* has
  n - 1 negations before E if n is odd and n + 1 if n is even.\<close>

fun star :: "lf \<Rightarrow> lf" where
  "star (LN (LN a)) = LN (LN (star a))"
| "star (LN (LV n)) = LV n"
| "star (LN (LC a b)) = LC a b"
| "star (LN (LD a b)) = LD a b"
| "star (LV n) = LN (LV n)"
| "star (LC a b) = LN (LC a b)"
| "star (LD a b) = LN (LD a b)"

lemma star_star [simp]: "star (star a) = a"
  by (induct a rule: star.induct) simp_all

lemma ev_star [simp]: "ev e (star a) = (\<not> ev e a)"
  by (induct a rule: star.induct) simp_all

lemma size_star: "size (star a) \<le> Suc (size a)"
  by (induct a rule: star.induct) simp_all

lemma size_starL: "size (star a) < Suc (Suc (size a + size b))"
  using size_star[of a] by linarith
lemma size_starR: "size (star b) < Suc (Suc (size a + size b))"
  using size_star[of b] by linarith

section \<open>(A) Wilhelm's inconsistency\<close>

text \<open>The conditions (p. 2), for a valuation e. Truth of a formula is ev e.\<close>

definition "W1 e R Q \<longleftrightarrow> (\<forall>a b c. R a (LC b c) \<longleftrightarrow> ev e (LC b c) \<and> (Q a b \<or> Q a c))"
definition "W2 e R Q \<longleftrightarrow> (\<forall>a b c. R a (LN (LC b c)) \<longleftrightarrow> ev e a \<and> (Q a (LN b) \<or> Q a (LN c)))"
definition "W3 e R Q \<longleftrightarrow> (\<forall>a b c. R a (LD b c) \<longleftrightarrow> ev e a \<and> (Q a b \<or> Q a c))"
definition "W4 e R Q \<longleftrightarrow> (\<forall>a b c. R a (LN (LD b c)) \<longleftrightarrow> ev e (LN (LD b c)) \<and> (Q a (LN b) \<or> Q a (LN c)))"
definition "W5 e R Q \<longleftrightarrow> (\<forall>a b. R a (LN (LN b)) \<longleftrightarrow> ev e a \<and> Q a b)"
definition "W6 e R \<longleftrightarrow> (\<exists>n. e n \<and> \<not> R (LV n) (LV n))"
definition "W7 Q \<longleftrightarrow> (\<forall>a b. Q (LC a b) (LN (LD (LN a) (LN b))))"
definition "W8 Q \<longleftrightarrow> (\<forall>a b. Q (LD a b) (LN (LC (LN a) (LN b))))"

text \<open>Leibniz's law, in the only form the derivation uses: R respects Q in each place.\<close>
definition "RESP_Q R Q \<longleftrightarrow> (\<forall>a a' b b'. Q a a' \<and> Q b b' \<longrightarrow> (R a b \<longleftrightarrow> R a' b'))"
definition "REFLSYM_Q Q \<longleftrightarrow> (\<forall>a. Q a a) \<and> (\<forall>a b. Q a b \<longrightarrow> Q b a)"

theorem wilhelm_inconsistency:
  assumes "W1 e R Q" "W4 e R Q" "W5 e R Q" "W6 e R" "W7 Q" "RESP_Q R Q" "REFLSYM_Q Q"
  shows False
proof -
  obtain n where n: "e n" "\<not> R (LV n) (LV n)" using assms(4) unfolding W6_def by blast
  let ?p = "LV n"
  have rq: "\<forall>a. Q a a" "\<forall>a b. Q a b \<longrightarrow> Q b a" using assms(7) unfolding REFLSYM_Q_def by blast+
  have resp: "\<And>a a' b b'. Q a a' \<Longrightarrow> Q b b' \<Longrightarrow> R a b \<longleftrightarrow> R a' b'"
    using assms(6) unfolding RESP_Q_def by blast
  \<comment> \<open>(4): \<not>\<not>p grounds \<not>(\<not>p \<or> \<not>p)\<close>
  have g1: "R (LN (LN ?p)) (LN (LD (LN ?p) (LN ?p)))"
    using assms(2) n(1) rq(1) unfolding W4_def by simp
  \<comment> \<open>(7): p \<and> p is \<not>(\<not>p \<or> \<not>p); Leibniz's law moves the ground\<close>
  have q7: "Q (LN (LD (LN ?p) (LN ?p))) (LC ?p ?p)"
    using assms(5) rq(2) unfolding W7_def by blast
  have g2: "R (LN (LN ?p)) (LC ?p ?p)" using resp[OF rq(1)[rule_format] q7] g1 by blast
  \<comment> \<open>(1): so \<not>\<not>p is p\<close>
  have q1: "Q (LN (LN ?p)) ?p" using assms(1) g2 unfolding W1_def by blast
  \<comment> \<open>(5): p grounds \<not>\<not>p, hence p grounds p\<close>
  have g3: "R ?p (LN (LN ?p))" using assms(3) n(1) rq(1) unfolding W5_def by simp
  have "R ?p ?p" using resp[OF rq(1)[rule_format] q1] g3 by blast
  with n(2) show False by blast
qed

text \<open>The same conditions for the map's own notions: immediate partial ground IPG
  (defined from G, decision D1) and identity of propositions. CL_PROP-style truth for
  the connectives used is assumed for the instances only.\<close>

theorem wilhelm_prp:
  assumes T_neg: "\<forall>p. T (neg p) \<longleftrightarrow> \<not> T p"
      and T_disj: "\<forall>p q. T (disj p q) \<longleftrightarrow> T p \<or> T q"
      and W1p: "\<forall>a b c. IPG a (conj b c) \<longleftrightarrow> T (conj b c) \<and> (a = b \<or> a = c)"
      and W4p: "\<forall>a b c. IPG a (neg (disj b c)) \<longleftrightarrow> T (neg (disj b c)) \<and> (a = neg b \<or> a = neg c)"
      and W5p: "\<forall>a b. IPG a (neg (neg b)) \<longleftrightarrow> T a \<and> a = b"
      and W6p: "\<exists>p. T p \<and> \<not> IPG p p"
      and W7p: "\<forall>a b. conj a b = neg (disj (neg a) (neg b))"
  shows False
proof -
  obtain p where p: "T p" "\<not> IPG p p" using W6p by blast
  have "T (neg (disj (neg p) (neg p)))" using p(1) T_neg T_disj by simp
  hence "IPG (neg (neg p)) (neg (disj (neg p) (neg p)))" using W4p by blast
  hence "IPG (neg (neg p)) (conj p p)" using W7p by simp
  hence "neg (neg p) = p" using W1p by blast
  moreover have "IPG p (neg (neg p))" using W5p p(1) by blast
  ultimately show False using p(2) by simp
qed

section \<open>(B) Poggiolesi's interpretation violates condition (1)\<close>

text \<open>Her relation \<cong> (p. 4): A \<cong> B iff B is A or A*. Her \<doteq> is "the closure of \<cong> under
  (7') and (8')"; we leave it as a parameter E and assume only that it contains \<cong>.
  S_E B is the set of immediate g-subformulas of B (p. 5); IP E e and IQ E are her
  interpretations of the ground and identity symbols (p. 5, clauses (i)-(v)).\<close>

definition "cong0 a b \<longleftrightarrow> b = a \<or> b = star a"

definition gsub :: "(lf \<Rightarrow> lf \<Rightarrow> bool) \<Rightarrow> lf \<Rightarrow> lf set" where
  "gsub E b = {x. (\<exists>c. E b (LN (LN c)) \<and> E x c)
                 \<or> (\<exists>c d. (E b (LC c d) \<or> E b (LD c d)) \<and> (E x c \<or> E x d))}"

definition "valid a \<longleftrightarrow> (\<forall>e. ev e a)"

fun conjlike :: "lf \<Rightarrow> bool" where
  "conjlike (LC c d) = True"
| "conjlike (LN (LD c d)) = True"
| "conjlike _ = False"

definition IP :: "(lf \<Rightarrow> lf \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> lf \<Rightarrow> lf \<Rightarrow> bool" where
  "IP E e a b \<longleftrightarrow> a \<in> gsub E b
     \<and> (if conjlike b then ev e b else ev e a)
     \<and> ((\<forall>e'. ev e' a \<longrightarrow> ev e' b) \<or> (\<forall>e'. \<not> ev e' a \<longrightarrow> \<not> ev e' b))"

definition IQ :: "(lf \<Rightarrow> lf \<Rightarrow> bool) \<Rightarrow> lf \<Rightarrow> lf \<Rightarrow> bool" where
  "IQ E a b \<longleftrightarrow> (\<forall>e'. ev e' a = ev e' b) \<and> gsub E a = gsub E b"

text \<open>Counterexample: B = p \<or> \<not>p, C = q, A = B* = \<not>(p \<or> \<not>p). A is an immediate
  g-subformula of B \<and> C (A \<cong> B), B \<and> C is true, and A classically implies B \<and> C because A
  is unsatisfiable; so the interpretation makes A a ground of B \<and> C. But A is equivalent
  neither to B nor to C, so the right-hand side of (1) is false. The interpretation also
  makes a falsehood a ground.\<close>

theorem poggiolesi_interpretation_violates_1:
  assumes E: "\<forall>x y. cong0 x y \<longrightarrow> E x y"
  defines "e \<equiv> (\<lambda>_::nat. True)"
  shows "\<not> W1 e (IP E e) (IQ E)"
proof
  assume w1: "W1 e (IP E e) (IQ E)"
  let ?b = "LD (LV 0) (LN (LV 0))" and ?c = "LV 1"
  let ?a = "star ?b"
  have a_def: "?a = LN (LD (LV 0) (LN (LV 0)))" by simp
  have Ebb: "E (LC ?b ?c) (LC ?b ?c)" using E unfolding cong0_def by blast
  have "cong0 ?a ?b" unfolding cong0_def by simp
  hence Eab: "E ?a ?b" using E by blast
  have "?a \<in> gsub E (LC ?b ?c)" unfolding gsub_def using Ebb Eab by blast
  moreover have "ev e (LC ?b ?c)" unfolding e_def by simp
  moreover have "\<forall>e'. ev e' ?a \<longrightarrow> ev e' (LC ?b ?c)" by simp
  ultimately have lhs: "IP E e ?a (LC ?b ?c)" unfolding IP_def by simp
  have "ev (\<lambda>_. True) ?a \<noteq> ev (\<lambda>_. True) ?b" by simp
  hence nb: "\<not> IQ E ?a ?b" unfolding IQ_def by blast
  have "ev (\<lambda>_. True) ?a \<noteq> ev (\<lambda>_. True) ?c" by simp
  hence nc: "\<not> IQ E ?a ?c" unfolding IQ_def by blast
  from w1 lhs have "IQ E ?a ?b \<or> IQ E ?a ?c" unfolding W1_def by blast
  with nb nc show False by blast
qed

corollary poggiolesi_interpretation_not_factive:
  assumes E: "\<forall>x y. cong0 x y \<longrightarrow> E x y"
  shows "IP E (\<lambda>_. True) (LN (LD (LV 0) (LN (LV 0)))) (LC (LD (LV 0) (LN (LV 0))) (LV 1))
       \<and> \<not> ev (\<lambda>_. True) (LN (LD (LV 0) (LN (LV 0))))"
proof -
  let ?b = "LD (LV 0) (LN (LV 0))" and ?c = "LV 1"
  have Ebb: "E (LC ?b ?c) (LC ?b ?c)" using E unfolding cong0_def by blast
  have "cong0 (LN ?b) ?b" unfolding cong0_def by simp
  hence "E (LN ?b) ?b" using E by blast
  hence "LN ?b \<in> gsub E (LC ?b ?c)" unfolding gsub_def using Ebb by blast
  thus ?thesis unfolding IP_def by simp
qed

section \<open>(C) A normal-form interpretation that satisfies the repaired conditions\<close>

text \<open>nf pushes a single negation of a conjunction or disjunction inwards by the star
  operation (so \<not>(B \<and> C) becomes B* \<or> C*) and keeps double negations as structure,
  following Poggiolesi's view that \<not>\<not>A sits a level above A (p. 2).\<close>

function nf :: "lf \<Rightarrow> lf" where
  "nf (LV n) = LV n"
| "nf (LN (LV n)) = LN (LV n)"
| "nf (LN (LN a)) = LN (LN (nf a))"
| "nf (LN (LC a b)) = LD (nf (star a)) (nf (star b))"
| "nf (LN (LD a b)) = LC (nf (star a)) (nf (star b))"
| "nf (LC a b) = LC (nf a) (nf b)"
| "nf (LD a b) = LD (nf a) (nf b)"
  by pat_completeness auto
termination
  by (relation "measure size") (simp_all add: size_starL size_starR)

lemma ev_nf [simp]: "ev e (nf a) = ev e a"
  by (induct a rule: nf.induct) simp_all

text \<open>Star on normal forms.\<close>
fun starN :: "lf \<Rightarrow> lf" where
  "starN (LV n) = LN (LV n)"
| "starN (LN (LV n)) = LV n"
| "starN (LN (LN x)) = LN (LN (starN x))"
| "starN (LC x y) = LD (starN x) (starN y)"
| "starN (LD x y) = LC (starN x) (starN y)"
| "starN (LN (LC x y)) = LN (LC x y)"
| "starN (LN (LD x y)) = LN (LD x y)"

lemma nf_star: "nf (star a) = starN (nf a)"
proof (induct a rule: nf.induct)
  case (4 a b)
  then show ?case by simp
next
  case (5 a b)
  then show ?case by simp
qed simp_all

definition "NQ a b \<longleftrightarrow> nf a = nf b"

text \<open>x is an immediate g-subformula of y, for normal forms.\<close>
fun immN :: "lf \<Rightarrow> lf \<Rightarrow> bool" where
  "immN x (LC u v) = (x = u \<or> x = v)"
| "immN x (LD u v) = (x = u \<or> x = v)"
| "immN x (LN (LN u)) = (x = u)"
| "immN x _ = False"

definition "NR e a b \<longleftrightarrow> ev e a \<and> ev e b \<and> immN (nf a) (nf b)"

text \<open>The repaired conditions (p. 3): (2') and (4') use star; (7') and (8') are the
  star versions of De Morgan.\<close>

definition "P2 e R Q \<longleftrightarrow> (\<forall>a b c. R a (LN (LC b c)) \<longleftrightarrow> ev e a \<and> (Q a (star b) \<or> Q a (star c)))"
definition "P4 e R Q \<longleftrightarrow> (\<forall>a b c. R a (LN (LD b c)) \<longleftrightarrow> ev e (LN (LD b c)) \<and> (Q a (star b) \<or> Q a (star c)))"
definition "P7 Q \<longleftrightarrow> (\<forall>a b. Q (LC a b) (star (LD (star a) (star b))))"
definition "P8 Q \<longleftrightarrow> (\<forall>a b. Q (LD a b) (star (LC (star a) (star b))))"

text \<open>Leibniz's law as we read Poggiolesi (p. 4): identity is an equivalence relation and
  a congruence for conjunction, disjunction, double negation and star (not for single
  negation); ground and truth respect it.\<close>

definition "LEIBNIZ e R Q \<longleftrightarrow>
     (\<forall>a. Q a a) \<and> (\<forall>a b. Q a b \<longrightarrow> Q b a) \<and> (\<forall>a b c. Q a b \<and> Q b c \<longrightarrow> Q a c)
   \<and> (\<forall>a a' b b'. Q a a' \<and> Q b b' \<longrightarrow> Q (LC a b) (LC a' b') \<and> Q (LD a b) (LD a' b'))
   \<and> (\<forall>a b. Q a b \<longrightarrow> Q (LN (LN a)) (LN (LN b)) \<and> Q (star a) (star b))
   \<and> RESP_Q R Q
   \<and> (\<forall>a b. Q a b \<longrightarrow> ev e a = ev e b)"

theorem poggiolesi_conditions_consistent:
  fixes e :: "nat \<Rightarrow> bool"
  assumes "e 0"
  shows "W1 e (NR e) NQ" "P2 e (NR e) NQ" "W3 e (NR e) NQ" "P4 e (NR e) NQ"
        "W5 e (NR e) NQ" "W6 e (NR e)" "P7 NQ" "P8 NQ" "LEIBNIZ e (NR e) NQ"
proof -
  show "W1 e (NR e) NQ"
    unfolding W1_def NR_def NQ_def by (auto dest: arg_cong[where f = "ev e"])
  show "P2 e (NR e) NQ"
    unfolding P2_def NR_def NQ_def by (auto dest: arg_cong[where f = "ev e"])
  show "W3 e (NR e) NQ"
    unfolding W3_def NR_def NQ_def by (auto dest: arg_cong[where f = "ev e"])
  show "P4 e (NR e) NQ"
    unfolding P4_def NR_def NQ_def by (auto dest: arg_cong[where f = "ev e"])
  show "W5 e (NR e) NQ"
    unfolding W5_def NR_def NQ_def by (auto dest: arg_cong[where f = "ev e"])
  show "W6 e (NR e)" unfolding W6_def NR_def using assms by auto
  show "P7 NQ" unfolding P7_def NQ_def by simp
  show "P8 NQ" unfolding P8_def NQ_def by simp
  show "LEIBNIZ e (NR e) NQ"
    unfolding LEIBNIZ_def RESP_Q_def NQ_def NR_def
    by (auto simp: nf_star dest: arg_cong[where f = "ev e"])
qed

text \<open>The normal-form interpretation is also factive and irreflexive: every ground is
  true, and no formula is an immediate ground of anything with the same normal form.\<close>

lemma immN_size: "immN x y \<Longrightarrow> size x < size y"
  by (induct x y rule: immN.induct) auto

lemma NR_factive_irreflexive: "NR e a b \<Longrightarrow> ev e a \<and> \<not> NQ a b"
  unfolding NR_def NQ_def using immN_size by fastforce

end
