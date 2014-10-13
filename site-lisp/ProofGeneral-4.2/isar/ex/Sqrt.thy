(*  Title:      HOL/ex/Sqrt.thy
    Author:     Markus Wenzel, TU Muenchen
*)

header {*  Square roots of primes are irrational *}

theory Sqrt
imports Complex_Main "~~/src/HOL/Number_Theory/Primes"
begin

text {*
  The square root of any prime number (including @{text 2}) is
  irrational.
*}

theorem sqrt_prime_irrational:
  assumes "prime (p::nat)"
  shows "sqrt (real p) \<notin> \<rat>"
proof
  from `prime p` have p: "1 < p" by (simp add: prime_nat_def)
  assume "sqrt (real p) \<in> \<rat>"
  then obtain m n :: nat where
      n: "n \<noteq> 0" and sqrt_rat: "\<bar>sqrt (real p)\<bar> = real m / real n"
    and gcd: "gcd m n = 1" by (rule Rats_abs_nat_div_natE)
  have eq: "m\<twosuperior> = p * n\<twosuperior>"
  proof -
    from n and sqrt_rat have "real m = \<bar>sqrt (real p)\<bar> * real n" by simp
    then have "real (m\<twosuperior>) = (sqrt (real p))\<twosuperior> * real (n\<twosuperior>)"
      by (auto simp add: power2_eq_square)
    also have "(sqrt (real p))\<twosuperior> = real p" by simp
    also have "\<dots> * real (n\<twosuperior>) = real (p * n\<twosuperior>)" by simp
    finally show ?thesis ..
  qed
  have "p dvd m \<and> p dvd n"
  proof
    from eq have "p dvd m\<twosuperior>" ..
    with `prime p` pos2 show "p dvd m" by (rule prime_dvd_power_nat)
    then obtain k where "m = p * k" ..
    with eq have "p * n\<twosuperior> = p\<twosuperior> * k\<twosuperior>" by (auto simp add: power2_eq_square mult_ac)
    with p have "n\<twosuperior> = p * k\<twosuperior>" by (simp add: power2_eq_square)
    then have "p dvd n\<twosuperior>" ..
    with `prime p` pos2 show "p dvd n" by (rule prime_dvd_power_nat)
  qed
  then have "p dvd gcd m n" ..
  with gcd have "p dvd 1" by simp
  then have "p \<le> 1" by (simp add: dvd_imp_le)
  with p show False by simp
qed

corollary "sqrt (real (2::nat)) \<notin> \<rat>"
  by (rule sqrt_prime_irrational) (rule two_is_prime_nat)


subsection {* Variations *}

text {*
  Here is an alternative version of the main proof, using mostly
  linear forward-reasoning.  While this results in less top-down
  structure, it is probably closer to proofs seen in mathematics.
*}

theorem
  assumes "prime (p::nat)"
  shows "sqrt (real p) \<notin> \<rat>"
proof
  from `prime p` have p: "1 < p" by (simp add: prime_nat_def)
  assume "sqrt (real p) \<in> \<rat>"
  then obtain m n :: nat where
      n: "n \<noteq> 0" and sqrt_rat: "\<bar>sqrt (real p)\<bar> = real m / real n"
    and gcd: "gcd m n = 1" by (rule Rats_abs_nat_div_natE)
  from n and sqrt_rat have "real m = \<bar>sqrt (real p)\<bar> * real n" by simp
  then have "real (m\<twosuperior>) = (sqrt (real p))\<twosuperior> * real (n\<twosuperior>)"
    by (auto simp add: power2_eq_square)
  also have "(sqrt (real p))\<twosuperior> = real p" by simp
  also have "\<dots> * real (n\<twosuperior>) = real (p * n\<twosuperior>)" by simp
  finally have eq: "m\<twosuperior> = p * n\<twosuperior>" ..
  then have "p dvd m\<twosuperior>" ..
  with `prime p` pos2 have dvd_m: "p dvd m" by (rule prime_dvd_power_nat)
  then obtain k where "m = p * k" ..
  with eq have "p * n\<twosuperior> = p\<twosuperior> * k\<twosuperior>" by (auto simp add: power2_eq_square mult_ac)
  with p have "n\<twosuperior> = p * k\<twosuperior>" by (simp add: power2_eq_square)
  then have "p dvd n\<twosuperior>" ..
  with `prime p` pos2 have "p dvd n" by (rule prime_dvd_power_nat)
  with dvd_m have "p dvd gcd m n" by (rule gcd_greatest_nat)
  with gcd have "p dvd 1" by simp
  then have "p \<le> 1" by (simp add: dvd_imp_le)
  with p show False by simp
qed

end
