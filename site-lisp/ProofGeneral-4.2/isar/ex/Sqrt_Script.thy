(*  Title:      HOL/ex/Sqrt_Script.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge
*)

header {* Square roots of primes are irrational (script version) *}

theory Sqrt_Script
imports Complex_Main "~~/src/HOL/Number_Theory/Primes"
begin

text {*
  \medskip Contrast this linear Isabelle/Isar script with Markus
  Wenzel's more mathematical version.
*}

subsection {* Preliminaries *}

lemma prime_nonzero:  "prime (p::nat) \<Longrightarrow> p \<noteq> 0"
  by (force simp add: prime_nat_def)

lemma prime_dvd_other_side:
    "(n::nat) * n = p * (k * k) \<Longrightarrow> prime p \<Longrightarrow> p dvd n"
  apply (subgoal_tac "p dvd n * n", blast dest: prime_dvd_mult_nat)
  apply auto
  done

lemma reduction: "prime (p::nat) \<Longrightarrow>
    0 < k \<Longrightarrow> k * k = p * (j * j) \<Longrightarrow> k < p * j \<and> 0 < j"
  apply (rule ccontr)
  apply (simp add: linorder_not_less)
  apply (erule disjE)
   apply (frule mult_le_mono, assumption)
   apply auto
  apply (force simp add: prime_nat_def)
  done

lemma rearrange: "(j::nat) * (p * j) = k * k \<Longrightarrow> k * k = p * (j * j)"
  by (simp add: mult_ac)

lemma prime_not_square:
    "prime (p::nat) \<Longrightarrow> (\<And>k. 0 < k \<Longrightarrow> m * m \<noteq> p * (k * k))"
  apply (induct m rule: nat_less_induct)
  apply clarify
  apply (frule prime_dvd_other_side, assumption)
  apply (erule dvdE)
  apply (simp add: nat_mult_eq_cancel_disj prime_nonzero)
  apply (blast dest: rearrange reduction)
  done


subsection {* Main theorem *}

text {*
  The square root of any prime number (including @{text 2}) is
  irrational.
*}

theorem prime_sqrt_irrational:
    "prime (p::nat) \<Longrightarrow> x * x = real p \<Longrightarrow> 0 \<le> x \<Longrightarrow> x \<notin> \<rat>"
  apply (rule notI)
  apply (erule Rats_abs_nat_div_natE)
  apply (simp del: real_of_nat_mult
              add: abs_if divide_eq_eq prime_not_square real_of_nat_mult [symmetric])
  done

lemmas two_sqrt_irrational =
  prime_sqrt_irrational [OF two_is_prime_nat]

end
