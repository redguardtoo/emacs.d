(********** 
  This file is copied from Isabelle2011. 
  It has been beautified with Tokens -> Replace Shortcuts
 **********)

(*  Title:      HOL/ex/Tarski.thy
    Author:     Florian Kammüller, Cambridge University Computer Laboratory
*)

header {* The Full Theorem of Tarski *}

theory Tarski
imports Main "~~/src/HOL/Library/FuncSet"
begin

text {*
  Minimal version of lattice theory plus the full theorem of Tarski:
  The fixedpoints of a complete lattice themselves form a complete
  lattice.

  Illustrates first-class theories, using the Sigma representation of
  structures.  Tidied and converted to Isar by lcp.
*}

record 'a potype =
  pset  :: "'a set"
  order :: "('a * 'a) set"

definition
  monotone :: "['a \<Rightarrow> 'a, 'a set, ('a *'a)set] \<Rightarrow> bool" where
  "monotone f A r = (\<forall>x\<in>A. \<forall>y\<in>A. (x, y): r \<longrightarrow> ((f x), (f y)) : r)"

definition
  least :: "['a \<Rightarrow> bool, 'a potype] \<Rightarrow> 'a" where
  "least P po = (SOME x. x: pset po & P x &
                       (\<forall>y \<in> pset po. P y \<longrightarrow> (x,y): order po))"

definition
  greatest :: "['a \<Rightarrow> bool, 'a potype] \<Rightarrow> 'a" where
  "greatest P po = (SOME x. x: pset po & P x &
                          (\<forall>y \<in> pset po. P y \<longrightarrow> (y,x): order po))"

definition
  lub  :: "['a set, 'a potype] \<Rightarrow> 'a" where
  "lub S po = least (%x. \<forall>y\<in>S. (y,x): order po) po"

definition
  glb  :: "['a set, 'a potype] \<Rightarrow> 'a" where
  "glb S po = greatest (%x. \<forall>y\<in>S. (x,y): order po) po"

definition
  isLub :: "['a set, 'a potype, 'a] \<Rightarrow> bool" where
  "isLub S po = (%L. (L: pset po & (\<forall>y\<in>S. (y,L): order po) &
                   (\<forall>z\<in>pset po. (\<forall>y\<in>S. (y,z): order po) \<longrightarrow> (L,z): order po)))"

definition
  isGlb :: "['a set, 'a potype, 'a] \<Rightarrow> bool" where
  "isGlb S po = (%G. (G: pset po & (\<forall>y\<in>S. (G,y): order po) &
                 (\<forall>z \<in> pset po. (\<forall>y\<in>S. (z,y): order po) \<longrightarrow> (z,G): order po)))"

definition
  "fix"    :: "[('a \<Rightarrow> 'a), 'a set] \<Rightarrow> 'a set" where
  "fix f A  = {x. x: A & f x = x}"

definition
  interval :: "[('a*'a) set,'a, 'a ] \<Rightarrow> 'a set" where
  "interval r a b = {x. (a,x): r & (x,b): r}"


definition
  Bot :: "'a potype \<Rightarrow> 'a" where
  "Bot po = least (%x. True) po"

definition
  Top :: "'a potype \<Rightarrow> 'a" where
  "Top po = greatest (%x. True) po"

definition
  PartialOrder :: "('a potype) set" where
  "PartialOrder = {P. refl_on (pset P) (order P) & antisym (order P) &
                       trans (order P)}"

definition
  CompleteLattice :: "('a potype) set" where
  "CompleteLattice = {cl. cl: PartialOrder &
                        (\<forall>S. S \<subseteq> pset cl \<longrightarrow> (\<exists>L. isLub S cl L)) &
                        (\<forall>S. S \<subseteq> pset cl \<longrightarrow> (\<exists>G. isGlb S cl G))}"

definition
  CLF_set :: "('a potype * ('a \<Rightarrow> 'a)) set" where
  "CLF_set = (SIGMA cl: CompleteLattice.
            {f. f: pset cl \<rightarrow> pset cl & monotone f (pset cl) (order cl)})"

definition
  induced :: "['a set, ('a * 'a) set] \<Rightarrow> ('a *'a)set" where
  "induced A r = {(a,b). a : A & b: A & (a,b): r}"


definition
  sublattice :: "('a potype * 'a set)set" where
  "sublattice =
      (SIGMA cl: CompleteLattice.
          {S. S \<subseteq> pset cl &
           \<lparr> pset = S, order = induced S (order cl) \<rparr>: CompleteLattice})"

abbreviation
  sublat :: "['a set, 'a potype] \<Rightarrow> bool"  ("_ \<guillemotleft>= _" [51,50]50) where
  "S \<guillemotleft>= cl \<equiv> S : sublattice `` {cl}"

definition
  dual :: "'a potype \<Rightarrow> 'a potype" where
  "dual po = \<lparr> pset = pset po, order = converse (order po) \<rparr>"

locale S =
  fixes cl :: "'a potype"
    and A  :: "'a set"
    and r  :: "('a * 'a) set"
  defines A_def: "A \<equiv> pset cl"
     and  r_def: "r \<equiv> order cl"

locale PO = S +
  assumes cl_po:  "cl : PartialOrder"

locale CL = S +
  assumes cl_co:  "cl : CompleteLattice"

sublocale CL < PO
apply (simp_all add: A_def r_def)
apply unfold_locales
using cl_co unfolding CompleteLattice_def by auto

locale CLF = S +
  fixes f :: "'a \<Rightarrow> 'a"
    and P :: "'a set"
  assumes f_cl:  "(cl,f) : CLF_set" (*was the equivalent "f : CLF_set``{cl}"*)
  defines P_def: "P \<equiv> fix f A"

sublocale CLF < CL
apply (simp_all add: A_def r_def)
apply unfold_locales
using f_cl unfolding CLF_set_def by auto

locale Tarski = CLF +
  fixes Y     :: "'a set"
    and intY1 :: "'a set"
    and v     :: "'a"
  assumes
    Y_ss: "Y \<subseteq> P"
  defines
    intY1_def: "intY1 \<equiv> interval r (lub Y cl) (Top cl)"
    and v_def: "v \<equiv> glb {x. ((%x: intY1. f x) x, x): induced intY1 r &
                             x: intY1}
                      \<lparr> pset=intY1, order=induced intY1 r\<rparr>"


subsection {* Partial Order *}

lemma (in PO) dual:
  "PO (dual cl)"
apply unfold_locales
using cl_po
unfolding PartialOrder_def dual_def
by auto

lemma (in PO) PO_imp_refl_on [simp]: "refl_on A r"
apply (insert cl_po)
apply (simp add: PartialOrder_def A_def r_def)
done

lemma (in PO) PO_imp_sym [simp]: "antisym r"
apply (insert cl_po)
apply (simp add: PartialOrder_def r_def)
done

lemma (in PO) PO_imp_trans [simp]: "trans r"
apply (insert cl_po)
apply (simp add: PartialOrder_def r_def)
done

lemma (in PO) reflE: "x \<in> A \<Longrightarrow> (x, x) \<in> r"
apply (insert cl_po)
apply (simp add: PartialOrder_def refl_on_def A_def r_def)
done

lemma (in PO) antisymE: "\<lbrakk> (a, b) \<in> r; (b, a) \<in> r \<rbrakk> \<Longrightarrow> a = b"
apply (insert cl_po)
apply (simp add: PartialOrder_def antisym_def r_def)
done

lemma (in PO) transE: "\<lbrakk> (a, b) \<in> r; (b, c) \<in> r\<rbrakk> \<Longrightarrow> (a,c) \<in> r"
apply (insert cl_po)
apply (simp add: PartialOrder_def r_def)
apply (unfold trans_def, fast)
done

lemma (in PO) monotoneE:
     "\<lbrakk> monotone f A r;  x \<in> A; y \<in> A; (x, y) \<in> r \<rbrakk> \<Longrightarrow> (f x, f y) \<in> r"
by (simp add: monotone_def)

lemma (in PO) po_subset_po:
     "S \<subseteq> A \<Longrightarrow> \<lparr> pset = S, order = induced S r \<rparr> \<in> PartialOrder"
apply (simp (no_asm) add: PartialOrder_def)
apply auto
-- {* refl *}
apply (simp add: refl_on_def induced_def)
apply (blast intro: reflE)
-- {* antisym *}
apply (simp add: antisym_def induced_def)
apply (blast intro: antisymE)
-- {* trans *}
apply (simp add: trans_def induced_def)
apply (blast intro: transE)
done

lemma (in PO) indE: "\<lbrakk> (x, y) \<in> induced S r; S \<subseteq> A \<rbrakk> \<Longrightarrow> (x, y) \<in> r"
by (simp add: add: induced_def)

lemma (in PO) indI: "\<lbrakk> (x, y) \<in> r; x \<in> S; y \<in> S \<rbrakk> \<Longrightarrow> (x, y) \<in> induced S r"
by (simp add: add: induced_def)

lemma (in CL) CL_imp_ex_isLub: "S \<subseteq> A \<Longrightarrow> \<exists>L. isLub S cl L"
apply (insert cl_co)
apply (simp add: CompleteLattice_def A_def)
done

declare (in CL) cl_co [simp]

lemma isLub_lub: "(\<exists>L. isLub S cl L) = isLub S cl (lub S cl)"
by (simp add: lub_def least_def isLub_def some_eq_ex [symmetric])

lemma isGlb_glb: "(\<exists>G. isGlb S cl G) = isGlb S cl (glb S cl)"
by (simp add: glb_def greatest_def isGlb_def some_eq_ex [symmetric])

lemma isGlb_dual_isLub: "isGlb S cl = isLub S (dual cl)"
by (simp add: isLub_def isGlb_def dual_def converse_def)

lemma isLub_dual_isGlb: "isLub S cl = isGlb S (dual cl)"
by (simp add: isLub_def isGlb_def dual_def converse_def)

lemma (in PO) dualPO: "dual cl \<in> PartialOrder"
apply (insert cl_po)
apply (simp add: PartialOrder_def dual_def refl_on_converse
                 trans_converse antisym_converse)
done

lemma Rdual:
     "\<forall>S. (S \<subseteq> A \<longrightarrow>( \<exists>L. isLub S \<lparr> pset = A, order = r\<rparr> L))
      \<Longrightarrow> \<forall>S. (S \<subseteq> A \<longrightarrow> (\<exists>G. isGlb S \<lparr> pset = A, order = r\<rparr> G))"
apply safe
apply (rule_tac x = "lub {y. y \<in> A & (\<forall>k \<in> S. (y, k) \<in> r)}
                      \<lparr>pset = A, order = r\<rparr> " in exI)
apply (drule_tac x = "{y. y \<in> A & (\<forall>k \<in> S. (y,k) \<in> r) }" in spec)
apply (drule mp, fast)
apply (simp add: isLub_lub isGlb_def)
apply (simp add: isLub_def, blast)
done

lemma lub_dual_glb: "lub S cl = glb S (dual cl)"
by (simp add: lub_def glb_def least_def greatest_def dual_def converse_def)

lemma glb_dual_lub: "glb S cl = lub S (dual cl)"
by (simp add: lub_def glb_def least_def greatest_def dual_def converse_def)

lemma CL_subset_PO: "CompleteLattice \<subseteq> PartialOrder"
by (simp add: PartialOrder_def CompleteLattice_def, fast)

lemmas CL_imp_PO = CL_subset_PO [THEN subsetD]

(*declare CL_imp_PO [THEN PO.PO_imp_refl, simp]
declare CL_imp_PO [THEN PO.PO_imp_sym, simp]
declare CL_imp_PO [THEN PO.PO_imp_trans, simp]*)

lemma (in CL) CO_refl_on: "refl_on A r"
by (rule PO_imp_refl_on)

lemma (in CL) CO_antisym: "antisym r"
by (rule PO_imp_sym)

lemma (in CL) CO_trans: "trans r"
by (rule PO_imp_trans)

lemma CompleteLatticeI:
     "\<lbrakk> po \<in> PartialOrder; (\<forall>S. S \<subseteq> pset po \<longrightarrow> (\<exists>L. isLub S po L));
         (\<forall>S. S \<subseteq> pset po \<longrightarrow> (\<exists>G. isGlb S po G))\<rbrakk>
      \<Longrightarrow> po \<in> CompleteLattice"
apply (unfold CompleteLattice_def, blast)
done

lemma (in CL) CL_dualCL: "dual cl \<in> CompleteLattice"
apply (insert cl_co)
apply (simp add: CompleteLattice_def dual_def)
apply (fold dual_def)
apply (simp add: isLub_dual_isGlb [symmetric] isGlb_dual_isLub [symmetric]
                 dualPO)
done

lemma (in PO) dualA_iff: "pset (dual cl) = pset cl"
by (simp add: dual_def)

lemma (in PO) dualr_iff: "((x, y) \<in> (order(dual cl))) = ((y, x) \<in> order cl)"
by (simp add: dual_def)

lemma (in PO) monotone_dual:
     "monotone f (pset cl) (order cl) 
     \<Longrightarrow> monotone f (pset (dual cl)) (order(dual cl))"
by (simp add: monotone_def dualA_iff dualr_iff)

lemma (in PO) interval_dual:
     "\<lbrakk> x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> interval r x y = interval (order(dual cl)) y x"
apply (simp add: interval_def dualr_iff)
apply (fold r_def, fast)
done

lemma (in PO) trans:
  "(x, y) \<in> r \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> (x, z) \<in> r"
using cl_po apply (auto simp add: PartialOrder_def r_def)
unfolding trans_def by blast 

lemma (in PO) interval_not_empty:
  "interval r a b \<noteq> {} \<Longrightarrow> (a, b) \<in> r"
apply (simp add: interval_def)
using trans by blast

lemma (in PO) interval_imp_mem: "x \<in> interval r a b \<Longrightarrow> (a, x) \<in> r"
by (simp add: interval_def)

lemma (in PO) left_in_interval:
     "\<lbrakk> a \<in> A; b \<in> A; interval r a b \<noteq> {} \<rbrakk> \<Longrightarrow> a \<in> interval r a b"
apply (simp (no_asm_simp) add: interval_def)
apply (simp add: PO_imp_trans interval_not_empty)
apply (simp add: reflE)
done

lemma (in PO) right_in_interval:
     "\<lbrakk> a \<in> A; b \<in> A; interval r a b \<noteq> {} \<rbrakk> \<Longrightarrow> b \<in> interval r a b"
apply (simp (no_asm_simp) add: interval_def)
apply (simp add: PO_imp_trans interval_not_empty)
apply (simp add: reflE)
done


subsection {* sublattice *}

lemma (in PO) sublattice_imp_CL:
     "S \<guillemotleft>= cl  \<Longrightarrow> \<lparr> pset = S, order = induced S r \<rparr> \<in> CompleteLattice"
by (simp add: sublattice_def CompleteLattice_def r_def)

lemma (in CL) sublatticeI:
     "\<lbrakk> S \<subseteq> A; \<lparr> pset = S, order = induced S r \<rparr> \<in> CompleteLattice \<rbrakk>
      \<Longrightarrow> S \<guillemotleft>= cl"
by (simp add: sublattice_def A_def r_def)

lemma (in CL) dual:
  "CL (dual cl)"
apply unfold_locales
using cl_co unfolding CompleteLattice_def
apply (simp add: dualPO isGlb_dual_isLub [symmetric] isLub_dual_isGlb [symmetric] dualA_iff)
done


subsection {* lub *}

lemma (in CL) lub_unique: "\<lbrakk> S \<subseteq> A; isLub S cl x; isLub S cl L\<rbrakk> \<Longrightarrow> x = L"
apply (rule antisymE)
apply (auto simp add: isLub_def r_def)
done

lemma (in CL) lub_upper: "\<lbrakk>S \<subseteq> A; x \<in> S\<rbrakk> \<Longrightarrow> (x, lub S cl) \<in> r"
apply (rule CL_imp_ex_isLub [THEN exE], assumption)
apply (unfold lub_def least_def)
apply (rule some_equality [THEN ssubst])
  apply (simp add: isLub_def)
 apply (simp add: lub_unique A_def isLub_def)
apply (simp add: isLub_def r_def)
done

lemma (in CL) lub_least:
     "\<lbrakk> S \<subseteq> A; L \<in> A; \<forall>x \<in> S. (x,L) \<in> r \<rbrakk> \<Longrightarrow> (lub S cl, L) \<in> r"
apply (rule CL_imp_ex_isLub [THEN exE], assumption)
apply (unfold lub_def least_def)
apply (rule_tac s=x in some_equality [THEN ssubst])
  apply (simp add: isLub_def)
 apply (simp add: lub_unique A_def isLub_def)
apply (simp add: isLub_def r_def A_def)
done

lemma (in CL) lub_in_lattice: "S \<subseteq> A \<Longrightarrow> lub S cl \<in> A"
apply (rule CL_imp_ex_isLub [THEN exE], assumption)
apply (unfold lub_def least_def)
apply (subst some_equality)
apply (simp add: isLub_def)
prefer 2 apply (simp add: isLub_def A_def)
apply (simp add: lub_unique A_def isLub_def)
done

lemma (in CL) lubI:
     "\<lbrakk> S \<subseteq> A; L \<in> A; \<forall>x \<in> S. (x,L) \<in> r;
         \<forall>z \<in> A. (\<forall>y \<in> S. (y,z) \<in> r) \<longrightarrow> (L,z) \<in> r \<rbrakk> \<Longrightarrow> L = lub S cl"
apply (rule lub_unique, assumption)
apply (simp add: isLub_def A_def r_def)
apply (unfold isLub_def)
apply (rule conjI)
apply (fold A_def r_def)
apply (rule lub_in_lattice, assumption)
apply (simp add: lub_upper lub_least)
done

lemma (in CL) lubIa: "\<lbrakk> S \<subseteq> A; isLub S cl L \<rbrakk> \<Longrightarrow> L = lub S cl"
by (simp add: lubI isLub_def A_def r_def)

lemma (in CL) isLub_in_lattice: "isLub S cl L \<Longrightarrow> L \<in> A"
by (simp add: isLub_def  A_def)

lemma (in CL) isLub_upper: "\<lbrakk>isLub S cl L; y \<in> S\<rbrakk> \<Longrightarrow> (y, L) \<in> r"
by (simp add: isLub_def r_def)

lemma (in CL) isLub_least:
     "\<lbrakk> isLub S cl L; z \<in> A; \<forall>y \<in> S. (y, z) \<in> r\<rbrakk> \<Longrightarrow> (L, z) \<in> r"
by (simp add: isLub_def A_def r_def)

lemma (in CL) isLubI:
     "\<lbrakk> L \<in> A; \<forall>y \<in> S. (y, L) \<in> r;
         (\<forall>z \<in> A. (\<forall>y \<in> S. (y, z):r) \<longrightarrow> (L, z) \<in> r)\<rbrakk> \<Longrightarrow> isLub S cl L"
by (simp add: isLub_def A_def r_def)


subsection {* glb *}

lemma (in CL) glb_in_lattice: "S \<subseteq> A \<Longrightarrow> glb S cl \<in> A"
apply (subst glb_dual_lub)
apply (simp add: A_def)
apply (rule dualA_iff [THEN subst])
apply (rule CL.lub_in_lattice)
apply (rule dual)
apply (simp add: dualA_iff)
done

lemma (in CL) glb_lower: "\<lbrakk>S \<subseteq> A; x \<in> S\<rbrakk> \<Longrightarrow> (glb S cl, x) \<in> r"
apply (subst glb_dual_lub)
apply (simp add: r_def)
apply (rule dualr_iff [THEN subst])
apply (rule CL.lub_upper)
apply (rule dual)
apply (simp add: dualA_iff A_def, assumption)
done

text {*
  Reduce the sublattice property by using substructural properties;
  abandoned see @{text "Tarski_4.ML"}.
*}

lemma (in CLF) [simp]:
    "f: pset cl \<rightarrow> pset cl & monotone f (pset cl) (order cl)"
apply (insert f_cl)
apply (simp add: CLF_set_def)
done

declare (in CLF) f_cl [simp]


lemma (in CLF) f_in_funcset: "f \<in> A \<rightarrow> A"
by (simp add: A_def)

lemma (in CLF) monotone_f: "monotone f A r"
by (simp add: A_def r_def)

lemma (in CLF) CLF_dual: "(dual cl, f) \<in> CLF_set"
apply (simp add: CLF_set_def  CL_dualCL monotone_dual)
apply (simp add: dualA_iff)
done

lemma (in CLF) dual:
  "CLF (dual cl) f"
apply (rule CLF.intro)
apply (rule CLF_dual)
done


subsection {* fixed points *}

lemma fix_subset: "fix f A \<subseteq> A"
by (simp add: fix_def, fast)

lemma fix_imp_eq: "x \<in> fix f A \<Longrightarrow> f x = x"
by (simp add: fix_def)

lemma fixf_subset:
     "\<lbrakk> A \<subseteq> B; x \<in> fix (%y: A. f y) A \<rbrakk> \<Longrightarrow> x \<in> fix f B"
by (simp add: fix_def, auto)


subsection {* lemmas for Tarski, lub *}
lemma (in CLF) lubH_le_flubH:
     "H = {x. (x, f x) \<in> r & x \<in> A} \<Longrightarrow> (lub H cl, f (lub H cl)) \<in> r"
apply (rule lub_least, fast)
apply (rule f_in_funcset [THEN funcset_mem])
apply (rule lub_in_lattice, fast)
-- {* @{text "\<forall>x:H. (x, f (lub H r)) \<in> r"} *}
apply (rule ballI)
apply (rule transE)
-- {* instantiates @{text "(x, ???z) \<in> order cl to (x, f x)"}, *}
-- {* because of the def of @{text H} *}
apply fast
-- {* so it remains to show @{text "(f x, f (lub H cl)) \<in> r"} *}
apply (rule_tac f = "f" in monotoneE)
apply (rule monotone_f, fast)
apply (rule lub_in_lattice, fast)
apply (rule lub_upper, fast)
apply assumption
done

lemma (in CLF) flubH_le_lubH:
     "\<lbrakk>  H = {x. (x, f x) \<in> r & x \<in> A} \<rbrakk> \<Longrightarrow> (f (lub H cl), lub H cl) \<in> r"
apply (rule lub_upper, fast)
apply (rule_tac t = "H" in ssubst, assumption)
apply (rule CollectI)
apply (rule conjI)
apply (rule_tac [2] f_in_funcset [THEN funcset_mem])
apply (rule_tac [2] lub_in_lattice)
prefer 2 apply fast
apply (rule_tac f = "f" in monotoneE)
apply (rule monotone_f)
  apply (blast intro: lub_in_lattice)
 apply (blast intro: lub_in_lattice f_in_funcset [THEN funcset_mem])
apply (simp add: lubH_le_flubH)
done

lemma (in CLF) lubH_is_fixp:
     "H = {x. (x, f x) \<in> r & x \<in> A} \<Longrightarrow> lub H cl \<in> fix f A"
apply (simp add: fix_def)
apply (rule conjI)
apply (rule lub_in_lattice, fast)
apply (rule antisymE)
apply (simp add: flubH_le_lubH)
apply (simp add: lubH_le_flubH)
done

lemma (in CLF) fix_in_H:
     "\<lbrakk> H = {x. (x, f x) \<in> r & x \<in> A};  x \<in> P \<rbrakk> \<Longrightarrow> x \<in> H"
by (simp add: P_def fix_imp_eq [of _ f A] reflE CO_refl_on
                    fix_subset [of f A, THEN subsetD])

lemma (in CLF) fixf_le_lubH:
     "H = {x. (x, f x) \<in> r & x \<in> A} \<Longrightarrow> \<forall>x \<in> fix f A. (x, lub H cl) \<in> r"
apply (rule ballI)
apply (rule lub_upper, fast)
apply (rule fix_in_H)
apply (simp_all add: P_def)
done

lemma (in CLF) lubH_least_fixf:
     "H = {x. (x, f x) \<in> r & x \<in> A}
      \<Longrightarrow> \<forall>L. (\<forall>y \<in> fix f A. (y,L) \<in> r) \<longrightarrow> (lub H cl, L) \<in> r"
apply (rule allI)
apply (rule impI)
apply (erule bspec)
apply (rule lubH_is_fixp, assumption)
done

subsection {* Tarski fixpoint theorem 1, first part *}
lemma (in CLF) T_thm_1_lub: "lub P cl = lub {x. (x, f x) \<in> r & x \<in> A} cl"
apply (rule sym)
apply (simp add: P_def)
apply (rule lubI)
apply (rule fix_subset)
apply (rule lub_in_lattice, fast)
apply (simp add: fixf_le_lubH)
apply (simp add: lubH_least_fixf)
done

lemma (in CLF) glbH_is_fixp: "H = {x. (f x, x) \<in> r & x \<in> A} \<Longrightarrow> glb H cl \<in> P"
  -- {* Tarski for glb *}
apply (simp add: glb_dual_lub P_def A_def r_def)
apply (rule dualA_iff [THEN subst])
apply (rule CLF.lubH_is_fixp)
apply (rule dual)
apply (simp add: dualr_iff dualA_iff)
done

lemma (in CLF) T_thm_1_glb: "glb P cl = glb {x. (f x, x) \<in> r & x \<in> A} cl"
apply (simp add: glb_dual_lub P_def A_def r_def)
apply (rule dualA_iff [THEN subst])
apply (simp add: CLF.T_thm_1_lub [of _ f, OF dual]
                 dualPO CL_dualCL CLF_dual dualr_iff)
done

subsection {* interval *}

lemma (in CLF) rel_imp_elem: "(x, y) \<in> r \<Longrightarrow> x \<in> A"
apply (insert CO_refl_on)
apply (simp add: refl_on_def, blast)
done

lemma (in CLF) interval_subset: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> interval r a b \<subseteq> A"
apply (simp add: interval_def)
apply (blast intro: rel_imp_elem)
done

lemma (in CLF) intervalI:
     "\<lbrakk> (a, x) \<in> r; (x, b) \<in> r \<rbrakk> \<Longrightarrow> x \<in> interval r a b"
by (simp add: interval_def)

lemma (in CLF) interval_lemma1:
     "\<lbrakk> S \<subseteq> interval r a b; x \<in> S \<rbrakk> \<Longrightarrow> (a, x) \<in> r"
by (unfold interval_def, fast)

lemma (in CLF) interval_lemma2:
     "\<lbrakk> S \<subseteq> interval r a b; x \<in> S \<rbrakk> \<Longrightarrow> (x, b) \<in> r"
by (unfold interval_def, fast)

lemma (in CLF) a_less_lub:
     "\<lbrakk> S \<subseteq> A; S \<noteq> {};
         \<forall>x \<in> S. (a,x) \<in> r; \<forall>y \<in> S. (y, L) \<in> r \<rbrakk> \<Longrightarrow> (a,L) \<in> r"
by (blast intro: transE)

lemma (in CLF) glb_less_b:
     "\<lbrakk> S \<subseteq> A; S \<noteq> {};
         \<forall>x \<in> S. (x,b) \<in> r; \<forall>y \<in> S. (G, y) \<in> r \<rbrakk> \<Longrightarrow> (G,b) \<in> r"
by (blast intro: transE)

lemma (in CLF) S_intv_cl:
     "\<lbrakk> a \<in> A; b \<in> A; S \<subseteq> interval r a b \<rbrakk>\<Longrightarrow> S \<subseteq> A"
by (simp add: subset_trans [OF _ interval_subset])

lemma (in CLF) L_in_interval:
     "\<lbrakk> a \<in> A; b \<in> A; S \<subseteq> interval r a b;
         S \<noteq> {}; isLub S cl L; interval r a b \<noteq> {} \<rbrakk> \<Longrightarrow> L \<in> interval r a b"
apply (rule intervalI)
apply (rule a_less_lub)
prefer 2 apply assumption
apply (simp add: S_intv_cl)
apply (rule ballI)
apply (simp add: interval_lemma1)
apply (simp add: isLub_upper)
-- {* @{text "(L, b) \<in> r"} *}
apply (simp add: isLub_least interval_lemma2)
done

lemma (in CLF) G_in_interval:
     "\<lbrakk> a \<in> A; b \<in> A; interval r a b \<noteq> {}; S \<subseteq> interval r a b; isGlb S cl G;
         S \<noteq> {} \<rbrakk> \<Longrightarrow> G \<in> interval r a b"
apply (simp add: interval_dual)
apply (simp add: CLF.L_in_interval [of _ f, OF dual]
                 dualA_iff A_def isGlb_dual_isLub)
done

lemma (in CLF) intervalPO:
     "\<lbrakk> a \<in> A; b \<in> A; interval r a b \<noteq> {} \<rbrakk>
      \<Longrightarrow> \<lparr> pset = interval r a b, order = induced (interval r a b) r \<rparr>
          \<in> PartialOrder"
apply (rule po_subset_po)
apply (simp add: interval_subset)
done

lemma (in CLF) intv_CL_lub:
 "\<lbrakk> a \<in> A; b \<in> A; interval r a b \<noteq> {} \<rbrakk>
  \<Longrightarrow> \<forall>S. S \<subseteq> interval r a b \<longrightarrow>
          (\<exists>L. isLub S \<lparr> pset = interval r a b,
                          order = induced (interval r a b) r \<rparr>  L)"
apply (intro strip)
apply (frule S_intv_cl [THEN CL_imp_ex_isLub])
prefer 2 apply assumption
apply assumption
apply (erule exE)
-- {* define the lub for the interval as *}
apply (rule_tac x = "if S = {} then a else L" in exI)
apply (simp (no_asm_simp) add: isLub_def split del: split_if)
apply (intro impI conjI)
-- {* @{text "(if S = {} then a else L) \<in> interval r a b"} *}
apply (simp add: CL_imp_PO L_in_interval)
apply (simp add: left_in_interval)
-- {* lub prop 1 *}
apply (case_tac "S = {}")
-- {* @{text "S = {}, y \<in> S = False \<Rightarrow> everything"} *}
apply fast
-- {* @{text "S \<noteq> {}"} *}
apply simp
-- {* @{text "\<forall>y:S. (y, L) \<in> induced (interval r a b) r"} *}
apply (rule ballI)
apply (simp add: induced_def  L_in_interval)
apply (rule conjI)
apply (rule subsetD)
apply (simp add: S_intv_cl, assumption)
apply (simp add: isLub_upper)
-- {* @{text "\<forall>z:interval r a b. (\<forall>y:S. (y, z) \<in> induced (interval r a b) r \<longrightarrow> (if S = {} then a else L, z) \<in> induced (interval r a b) r"} *}
apply (rule ballI)
apply (rule impI)
apply (case_tac "S = {}")
-- {* @{text "S = {}"} *}
apply simp
apply (simp add: induced_def  interval_def)
apply (rule conjI)
apply (rule reflE, assumption)
apply (rule interval_not_empty)
apply (simp add: interval_def)
-- {* @{text "S \<noteq> {}"} *}
apply simp
apply (simp add: induced_def  L_in_interval)
apply (rule isLub_least, assumption)
apply (rule subsetD)
prefer 2 apply assumption
apply (simp add: S_intv_cl, fast)
done

lemmas (in CLF) intv_CL_glb = intv_CL_lub [THEN Rdual]

lemma (in CLF) interval_is_sublattice:
     "\<lbrakk> a \<in> A; b \<in> A; interval r a b \<noteq> {} \<rbrakk>
        \<Longrightarrow> interval r a b \<guillemotleft>= cl"
apply (rule sublatticeI)
apply (simp add: interval_subset)
apply (rule CompleteLatticeI)
apply (simp add: intervalPO)
 apply (simp add: intv_CL_lub)
apply (simp add: intv_CL_glb)
done

lemmas (in CLF) interv_is_compl_latt =
    interval_is_sublattice [THEN sublattice_imp_CL]


subsection {* Top and Bottom *}
lemma (in CLF) Top_dual_Bot: "Top cl = Bot (dual cl)"
by (simp add: Top_def Bot_def least_def greatest_def dualA_iff dualr_iff)

lemma (in CLF) Bot_dual_Top: "Bot cl = Top (dual cl)"
by (simp add: Top_def Bot_def least_def greatest_def dualA_iff dualr_iff)

lemma (in CLF) Bot_in_lattice: "Bot cl \<in> A"
apply (simp add: Bot_def least_def)
apply (rule_tac a="glb A cl" in someI2)
apply (simp_all add: glb_in_lattice glb_lower 
                     r_def [symmetric] A_def [symmetric])
done

lemma (in CLF) Top_in_lattice: "Top cl \<in> A"
apply (simp add: Top_dual_Bot A_def)
apply (rule dualA_iff [THEN subst])
apply (rule CLF.Bot_in_lattice [OF dual])
done

lemma (in CLF) Top_prop: "x \<in> A \<Longrightarrow> (x, Top cl) \<in> r"
apply (simp add: Top_def greatest_def)
apply (rule_tac a="lub A cl" in someI2)
apply (rule someI2)
apply (simp_all add: lub_in_lattice lub_upper 
                     r_def [symmetric] A_def [symmetric])
done

lemma (in CLF) Bot_prop: "x \<in> A \<Longrightarrow> (Bot cl, x) \<in> r"
apply (simp add: Bot_dual_Top r_def)
apply (rule dualr_iff [THEN subst])
apply (rule CLF.Top_prop [OF dual])
apply (simp add: dualA_iff A_def)
done

lemma (in CLF) Top_intv_not_empty: "x \<in> A  \<Longrightarrow> interval r x (Top cl) \<noteq> {}"
apply (rule notI)
apply (drule_tac a = "Top cl" in equals0D)
apply (simp add: interval_def)
apply (simp add: refl_on_def Top_in_lattice Top_prop)
done

lemma (in CLF) Bot_intv_not_empty: "x \<in> A \<Longrightarrow> interval r (Bot cl) x \<noteq> {}"
apply (simp add: Bot_dual_Top)
apply (subst interval_dual)
prefer 2 apply assumption
apply (simp add: A_def)
apply (rule dualA_iff [THEN subst])
apply (rule CLF.Top_in_lattice [OF dual])
apply (rule CLF.Top_intv_not_empty [OF dual])
apply (simp add: dualA_iff A_def)
done

subsection {* fixed points form a partial order *}

lemma (in CLF) fixf_po: "\<lparr> pset = P, order = induced P r\<rparr> \<in> PartialOrder"
by (simp add: P_def fix_subset po_subset_po)

lemma (in Tarski) Y_subset_A: "Y \<subseteq> A"
apply (rule subset_trans [OF _ fix_subset])
apply (rule Y_ss [simplified P_def])
done

lemma (in Tarski) lubY_in_A: "lub Y cl \<in> A"
  by (rule Y_subset_A [THEN lub_in_lattice])

lemma (in Tarski) lubY_le_flubY: "(lub Y cl, f (lub Y cl)) \<in> r"
apply (rule lub_least)
apply (rule Y_subset_A)
apply (rule f_in_funcset [THEN funcset_mem])
apply (rule lubY_in_A)
-- {* @{text "Y \<subseteq> P \<Longrightarrow> f x = x"} *}
apply (rule ballI)
apply (rule_tac t = "x" in fix_imp_eq [THEN subst])
apply (erule Y_ss [simplified P_def, THEN subsetD])
-- {* @{text "reduce (f x, f (lub Y cl)) \<in> r to (x, lub Y cl) \<in> r"} by monotonicity *}
apply (rule_tac f = "f" in monotoneE)
apply (rule monotone_f)
apply (simp add: Y_subset_A [THEN subsetD])
apply (rule lubY_in_A)
apply (simp add: lub_upper Y_subset_A)
done

lemma (in Tarski) intY1_subset: "intY1 \<subseteq> A"
apply (unfold intY1_def)
apply (rule interval_subset)
apply (rule lubY_in_A)
apply (rule Top_in_lattice)
done

lemmas (in Tarski) intY1_elem = intY1_subset [THEN subsetD]

lemma (in Tarski) intY1_f_closed: "x \<in> intY1 \<Longrightarrow> f x \<in> intY1"
apply (simp add: intY1_def  interval_def)
apply (rule conjI)
apply (rule transE)
apply (rule lubY_le_flubY)
-- {* @{text "(f (lub Y cl), f x) \<in> r"} *}
apply (rule_tac f=f in monotoneE)
apply (rule monotone_f)
apply (rule lubY_in_A)
apply (simp add: intY1_def interval_def  intY1_elem)
apply (simp add: intY1_def  interval_def)
-- {* @{text "(f x, Top cl) \<in> r"} *}
apply (rule Top_prop)
apply (rule f_in_funcset [THEN funcset_mem])
apply (simp add: intY1_def interval_def  intY1_elem)
done

lemma (in Tarski) intY1_mono:
     "monotone (%x: intY1. f x) intY1 (induced intY1 r)"
apply (auto simp add: monotone_def induced_def intY1_f_closed)
apply (blast intro: intY1_elem monotone_f [THEN monotoneE])
done

lemma (in Tarski) intY1_is_cl:
    "\<lparr> pset = intY1, order = induced intY1 r \<rparr> \<in> CompleteLattice"
apply (unfold intY1_def)
apply (rule interv_is_compl_latt)
apply (rule lubY_in_A)
apply (rule Top_in_lattice)
apply (rule Top_intv_not_empty)
apply (rule lubY_in_A)
done

lemma (in Tarski) v_in_P: "v \<in> P"
apply (unfold P_def)
apply (rule_tac A = "intY1" in fixf_subset)
apply (rule intY1_subset)
unfolding v_def
apply (rule CLF.glbH_is_fixp [OF CLF.intro, unfolded CLF_set_def, of "\<lparr>pset = intY1, order = induced intY1 r\<rparr>", simplified])
apply auto
apply (rule intY1_is_cl)
apply (erule intY1_f_closed)
apply (rule intY1_mono)
done

lemma (in Tarski) z_in_interval:
     "\<lbrakk> z \<in> P; \<forall>y\<in>Y. (y, z) \<in> induced P r \<rbrakk> \<Longrightarrow> z \<in> intY1"
apply (unfold intY1_def P_def)
apply (rule intervalI)
prefer 2
 apply (erule fix_subset [THEN subsetD, THEN Top_prop])
apply (rule lub_least)
apply (rule Y_subset_A)
apply (fast elim!: fix_subset [THEN subsetD])
apply (simp add: induced_def)
done

lemma (in Tarski) f'z_in_int_rel: "\<lbrakk> z \<in> P; \<forall>y\<in>Y. (y, z) \<in> induced P r \<rbrakk>
      \<Longrightarrow> ((%x: intY1. f x) z, z) \<in> induced intY1 r"
apply (simp add: induced_def  intY1_f_closed z_in_interval P_def)
apply (simp add: fix_imp_eq [of _ f A] fix_subset [of f A, THEN subsetD]
                 reflE)
done

lemma (in Tarski) tarski_full_lemma:
     "\<exists>L. isLub Y \<lparr> pset = P, order = induced P r \<rparr> L"
apply (rule_tac x = "v" in exI)
apply (simp add: isLub_def)
-- {* @{text "v \<in> P"} *}
apply (simp add: v_in_P)
apply (rule conjI)
-- {* @{text v} is lub *}
-- {* @{text "1. \<forall>y:Y. (y, v) \<in> induced P r"} *}
apply (rule ballI)
apply (simp add: induced_def subsetD v_in_P)
apply (rule conjI)
apply (erule Y_ss [THEN subsetD])
apply (rule_tac b = "lub Y cl" in transE)
apply (rule lub_upper)
apply (rule Y_subset_A, assumption)
apply (rule_tac b = "Top cl" in interval_imp_mem)
apply (simp add: v_def)
apply (fold intY1_def)
apply (rule CL.glb_in_lattice [OF CL.intro [OF intY1_is_cl], simplified])
apply auto
apply (rule indI)
  prefer 3 apply assumption
 prefer 2 apply (simp add: v_in_P)
apply (unfold v_def)
apply (rule indE)
apply (rule_tac [2] intY1_subset)
apply (rule CL.glb_lower [OF CL.intro [OF intY1_is_cl], simplified])
  apply (simp add: CL_imp_PO intY1_is_cl)
 apply force
apply (simp add: induced_def intY1_f_closed z_in_interval)
apply (simp add: P_def fix_imp_eq [of _ f A] reflE
                 fix_subset [of f A, THEN subsetD])
done

lemma CompleteLatticeI_simp:
     "\<lbrakk> \<lparr> pset = A, order = r \<rparr> \<in> PartialOrder;
         \<forall>S. S \<subseteq> A \<longrightarrow> (\<exists>L. isLub S \<lparr> pset = A, order = r \<rparr>  L) \<rbrakk>
    \<Longrightarrow> \<lparr> pset = A, order = r \<rparr> \<in> CompleteLattice"
by (simp add: CompleteLatticeI Rdual)

theorem (in CLF) Tarski_full:
     "\<lparr> pset = P, order = induced P r\<rparr> \<in> CompleteLattice"
apply (rule CompleteLatticeI_simp)
apply (rule fixf_po, clarify)
apply (simp add: P_def A_def r_def)
apply (rule Tarski.tarski_full_lemma [OF Tarski.intro [OF _ Tarski_axioms.intro]])
proof - show "CLF cl f" .. qed

end
