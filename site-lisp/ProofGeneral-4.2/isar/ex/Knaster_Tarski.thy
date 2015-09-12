(********** 
  This file is copied from Isabelle2011.
 **********)

(*  Title:      HOL/Isar_Examples/Knaster_Tarski.thy
    Author:     Markus Wenzel, TU Muenchen

Typical textbook proof example.
*)

header {* Textbook-style reasoning: the Knaster-Tarski Theorem *}

theory Knaster_Tarski
imports Main "~~/src/HOL/Library/Lattice_Syntax"
begin


subsection {* Prose version *}

text {* According to the textbook \cite[pages
  93--94]{davey-priestley}, the Knaster-Tarski fixpoint theorem is as
  follows.\footnote{We have dualized the argument, and tuned the
  notation a little bit.}

  \textbf{The Knaster-Tarski Fixpoint Theorem.}  Let @{text L} be a
  complete lattice and @{text "f: L \<rightarrow> L"} an order-preserving map.
  Then @{text "\<Sqinter>{x \<in> L | f(x) \<le> x}"} is a fixpoint of @{text f}.

  \textbf{Proof.} Let @{text "H = {x \<in> L | f(x) \<le> x}"} and @{text "a =
  \<Sqinter>H"}.  For all @{text "x \<in> H"} we have @{text "a \<le> x"}, so @{text
  "f(a) \<le> f(x) \<le> x"}.  Thus @{text "f(a)"} is a lower bound of @{text
  H}, whence @{text "f(a) \<le> a"}.  We now use this inequality to prove
  the reverse one (!) and thereby complete the proof that @{text a} is
  a fixpoint.  Since @{text f} is order-preserving, @{text "f(f(a)) \<le>
  f(a)"}.  This says @{text "f(a) \<in> H"}, so @{text "a \<le> f(a)"}. *}


subsection {* Formal versions *}

text {* The Isar proof below closely follows the original
  presentation.  Virtually all of the prose narration has been
  rephrased in terms of formal Isar language elements.  Just as many
  textbook-style proofs, there is a strong bias towards forward proof,
  and several bends in the course of reasoning. *}

theorem Knaster_Tarski:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes "mono f"
  shows "\<exists>a. f a = a"
proof
  let ?H = "{u. f u \<le> u}"
  let ?a = "\<Sqinter>?H"
  show "f ?a = ?a"
  proof -
    {
      fix x
      assume "x \<in> ?H"
      then have "?a \<le> x" by (rule Inf_lower)
      with `mono f` have "f ?a \<le> f x" ..
      also from `x \<in> ?H` have "\<dots> \<le> x" ..
      finally have "f ?a \<le> x" .
    }
    then have "f ?a \<le> ?a" by (rule Inf_greatest)
    {
      also presume "\<dots> \<le> f ?a"
      finally (order_antisym) show ?thesis .
    }
    from `mono f` and `f ?a \<le> ?a` have "f (f ?a) \<le> f ?a" ..
    then have "f ?a \<in> ?H" ..
    then show "?a \<le> f ?a" by (rule Inf_lower)
  qed
qed

text {* Above we have used several advanced Isar language elements,
  such as explicit block structure and weak assumptions.  Thus we have
  mimicked the particular way of reasoning of the original text.

  In the subsequent version the order of reasoning is changed to
  achieve structured top-down decomposition of the problem at the
  outer level, while only the inner steps of reasoning are done in a
  forward manner.  We are certainly more at ease here, requiring only
  the most basic features of the Isar language. *}

theorem Knaster_Tarski':
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes "mono f"
  shows "\<exists>a. f a = a"
proof
  let ?H = "{u. f u \<le> u}"
  let ?a = "\<Sqinter>?H"
  show "f ?a = ?a"
  proof (rule order_antisym)
    show "f ?a \<le> ?a"
    proof (rule Inf_greatest)
      fix x
      assume "x \<in> ?H"
      then have "?a \<le> x" by (rule Inf_lower)
      with `mono f` have "f ?a \<le> f x" ..
      also from `x \<in> ?H` have "\<dots> \<le> x" ..
      finally show "f ?a \<le> x" .
    qed
    show "?a \<le> f ?a"
    proof (rule Inf_lower)
      from `mono f` and `f ?a \<le> ?a` have "f (f ?a) \<le> f ?a" ..
      then show "f ?a \<in> ?H" ..
    qed
  qed
qed

end
