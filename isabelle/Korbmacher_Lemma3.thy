theory Korbmacher_Lemma3
  imports Main
begin

text \<open>
  Finding C of docs/korbmacher-2018b.md (registry finding F25): a schematic check that
  printed instances of Korbmacher 2018b's Lemma 3 (p. 210), T3 (p. 204), T1 (p. 204),
  APD_F (p. 207) and G3a (p. 203) are jointly inconsistent, and that so are the
  instances of Lemma 3, T3 and RP11 (p. 208).

  This is NOT a formalization of PGA.  Codes are an abstract type, the truth predicates
  Tr_1, Tr_2 and the ground predicate are uninterpreted, and the arithmetic facts the
  derivation needs (what PA proves about Sent) are premises.  What is checked is only
  that the stated instances, read as below, entail False.  Whether they are the right
  instances of the printed schemata is a reading of the page, recorded in the registry.

  Reading: tr1 t is the code of Tr_1(t-dot); neg x is the code of the negation of x;
  e is the code of 0 = 0; S0 is Sent_<1 (arithmetic sentences), S1 is Sent_<2.
\<close>

section \<open>The two inconsistencies\<close>

theorem korbmacher_lemma3_APDF:
  fixes Tr1 Tr2 S0 S1 :: "'c \<Rightarrow> bool" and Gr :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and neg tr1 :: "'c \<Rightarrow> 'c" and e :: 'c
  assumes L3:   "\<forall>t. Tr2 (neg (tr1 t)) \<longleftrightarrow> \<not> Tr1 t"           (* Lemma 3, phi(x) = not Tr_1(x), gamma = beta = 2 *)
      and T3:   "\<forall>x. Tr1 x \<longrightarrow> S0 x"                          (* T3^1 *)
      and T1:   "Tr1 e"                                          (* T1^1 at 0 = 0 *)
      and APDF: "\<forall>x. Tr2 (neg (tr1 x)) \<longrightarrow> Gr (neg x) (neg (tr1 x))" (* APD_F^{2,1} *)
      and G3a:  "\<forall>x y. Gr x y \<longrightarrow> (S1 x \<longrightarrow> Tr2 x)"            (* G3a^2 *)
      and PA1:  "\<not> S0 (tr1 e)"                                   (* Tr_1(0=0) is not arithmetic *)
      and PA2:  "S1 (neg (tr1 e))"                               (* not Tr_1(0=0) is in L_<2 *)
  shows False
proof -
  let ?c = "tr1 e"
  have "\<not> Tr1 ?c" using T3 PA1 by blast                       (* step 2 *)
  hence "Tr2 (neg (tr1 ?c))" using L3 by blast                 (* step 1 *)
  hence "Gr (neg ?c) (neg (tr1 ?c))" using APDF by blast       (* step 3 *)
  hence "Tr2 (neg (tr1 e))" using G3a PA2 by blast             (* step 4 *)
  hence "\<not> Tr1 e" using L3 by blast                           (* step 5 *)
  thus False using T1 by blast
qed

theorem korbmacher_lemma3_RP11:
  fixes Tr1 Tr2 S0 :: "'c \<Rightarrow> bool" and neg tr1 :: "'c \<Rightarrow> 'c" and c :: 'c
  assumes L3:   "\<forall>t. Tr2 (neg (tr1 t)) \<longleftrightarrow> \<not> Tr1 t"
      and T3:   "\<forall>x. Tr1 x \<longrightarrow> S0 x"
      and RP11: "\<forall>x. Tr2 (neg (tr1 x)) \<longleftrightarrow> Tr1 (neg x)"         (* RP11^2 with gamma = 1 *)
      and PA1:  "\<not> S0 c"
      and PA2:  "\<not> S0 (neg c)"
  shows False
  using assms by blast

section \<open>Each repair restores consistency of the instances\<close>

text \<open>
  A toy code language: the equation 0 = 0, negation, and Tr_1 applied to a code.
  Every code is a sentence of L_<2 (there is no Tr_2 code), so S1 is everywhere true.
\<close>

datatype code = Eq | NegC code | Tr1C code

fun S0 :: "code \<Rightarrow> bool" where
  "S0 Eq = True"
| "S0 (NegC x) = S0 x"
| "S0 (Tr1C x) = False"

fun val0 :: "code \<Rightarrow> bool" where
  "val0 Eq = True"
| "val0 (NegC x) = (\<not> val0 x)"
| "val0 (Tr1C x) = False"

definition Tr1 :: "code \<Rightarrow> bool" where
  "Tr1 x \<longleftrightarrow> S0 x \<and> val0 x"

subsection \<open>Repair A: keep the printed axioms, drop Lemma 3 (positive reading)\<close>

fun posTr2 :: "code \<Rightarrow> bool" where
  "posTr2 Eq = True"
| "posTr2 (Tr1C x) = Tr1 x"
| "posTr2 (NegC Eq) = False"
| "posTr2 (NegC (NegC x)) = posTr2 x"
| "posTr2 (NegC (Tr1C x)) = Tr1 (NegC x)"

definition GrA :: "code \<Rightarrow> code \<Rightarrow> bool" where
  "GrA x y \<longleftrightarrow> (\<exists>z. y = NegC (Tr1C z) \<and> x = NegC z \<and> Tr1 (NegC z))"

lemma posTr2_S0: "S0 x \<Longrightarrow> posTr2 x = val0 x"
  by (induction x rule: posTr2.induct) auto

theorem repairA_consistent:
  "(\<forall>x. Tr1 x \<longrightarrow> S0 x)"
  "Tr1 Eq"
  "\<forall>x. posTr2 (NegC (Tr1C x)) \<longrightarrow> GrA (NegC x) (NegC (Tr1C x))"
  "\<forall>x y. GrA x y \<longrightarrow> (True \<longrightarrow> posTr2 x)"
  "\<forall>x. posTr2 (NegC (Tr1C x)) \<longleftrightarrow> Tr1 (NegC x)"
  "\<not> S0 (Tr1C Eq)"
  by (auto simp: Tr1_def GrA_def posTr2_S0)

theorem repairA_lemma3_fails:
  "\<not> (posTr2 (NegC (Tr1C (Tr1C Eq))) \<longleftrightarrow> \<not> Tr1 (Tr1C Eq))"
  by (simp add: Tr1_def)

subsection \<open>Repair B: keep Lemma 3, restrict APD_F and RP11 to Sent_<1 (classical reading)\<close>

fun clTr2 :: "code \<Rightarrow> bool" where
  "clTr2 Eq = True"
| "clTr2 (NegC x) = (\<not> clTr2 x)"
| "clTr2 (Tr1C x) = Tr1 x"

definition GrB :: "code \<Rightarrow> code \<Rightarrow> bool" where
  "GrB x y \<longleftrightarrow> (\<exists>z. S0 z \<and> y = NegC (Tr1C z) \<and> x = NegC z \<and> \<not> Tr1 z)"

lemma clTr2_S0: "S0 x \<Longrightarrow> clTr2 x = val0 x"
  by (induction x) auto

theorem repairB_consistent:
  "\<forall>t. clTr2 (NegC (Tr1C t)) \<longleftrightarrow> \<not> Tr1 t"
  "(\<forall>x. Tr1 x \<longrightarrow> S0 x)"
  "Tr1 Eq"
  "\<forall>x. S0 x \<longrightarrow> clTr2 (NegC (Tr1C x)) \<longrightarrow> GrB (NegC x) (NegC (Tr1C x))"
  "\<forall>x y. GrB x y \<longrightarrow> (True \<longrightarrow> clTr2 x)"
  "\<forall>x. S0 x \<longrightarrow> (clTr2 (NegC (Tr1C x)) \<longleftrightarrow> Tr1 (NegC x))"
  "\<not> S0 (Tr1C Eq)"
  by (auto simp: Tr1_def GrB_def clTr2_S0)

theorem repairB_unrestricted_APDF_fails:
  "clTr2 (NegC (Tr1C (Tr1C Eq))) \<and> \<not> GrB (NegC (Tr1C Eq)) (NegC (Tr1C (Tr1C Eq)))"
  by (simp add: Tr1_def GrB_def)

end
