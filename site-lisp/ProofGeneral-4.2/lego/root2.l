(************************************************************************
   Conor McBride's proof that 2 has no rational root.

   This proof is accepted by LEGO version 1.3.1 with its standard library.
*************************************************************************)

Make lib_nat; (* loading basic logic, nat, plus, times etc *)

(* note, plus and times are defined by recursion on their first arg *)


(************************************************************************
   Alternative eliminators for nat

   LEGO's induction tactic figures out which induction principle to use
   by looking at the type of the variable on which we're doing induction.
   Consequently, we can persuade the tactic to use an alternative induction
   principle if we alias the type.

   Nat_elim is just the case analysis principle for natural numbers---the
   same as the induction principle except that there's no inductive hypothesis
   in the step case. It's intended to be used in combination with...

   ...NAT_elim, which performs no case analysis but says you can have an
   inductive hypothesis for any smaller value, where y is smaller than
   suc (plus x y). This is `well-founded induction' for the < relation,
   but expressed more concretely.

   The effect is very similar to that of `Case' and `Fix' in Coq.
************************************************************************)

[Nat = nat];
[NAT = Nat];

(* case analysis: just a weakening of induction *)

Goal Nat_elim : {Phi:nat->Type}
                {phiz:Phi zero}
                {phis:{n:Nat}Phi (suc n)}
                {n:Nat}Phi n;
intros ___;
  Expand Nat; Induction n;
    Immed;
    intros; Immed;
Save;

(* suc-plus guarded induction: the usual proof *)

Goal NAT_elim :
     {Phi:nat->Type}
     {phi:{n:Nat}
          {ih:{x,y|Nat}(Eq n (suc (plus x y)))->Phi y}
          Phi n}
     {n:NAT}Phi n;
intros Phi phi n';
(* claim that we can build the hypothesis collector for each n *)
Claim {n:nat}{x,y|Nat}(Eq n (suc (plus x y)))->Phi y;
(* use phi on the claimed collector *)
Refine phi n' (?+1 n');
(* now build the collector by one-step induction *)
  Induction n;
    Qnify; (* nothing to collect for zero *)
    intros n nhyp;
      Induction x; (* case analysis on the slack *)
        Qnify;
          Refine phi;  (* if the bound is tight, use phi to         *)
            Immed;     (* generate the new member of the collection *)
        Qnify;
          Refine nhyp; (* otherwise, we've already collected it *)
            Immed;
Save;


(***************************************************************************
   Equational laws governing plus and times:
   some of these are doubtless in the library, but it takes longer to
   remember their names than to prove them again.
****************************************************************************)

Goal plusZero : {x:nat}Eq (plus x zero) x;
Induction x;
  Refine Eq_refl;
  intros;
    Refine Eq_resp suc;
      Immed;
Save;

Goal plusSuc : {x,y:nat}Eq (plus x (suc y)) (suc (plus x y));
Induction x;
  intros; Refine Eq_refl;
  intros;
    Refine Eq_resp suc;
      Immed;
Save;

Goal plusAssoc : {x,y,z:nat}Eq (plus (plus x y) z) (plus x (plus y z));
Induction x;
  intros; Refine Eq_refl;
  intros;
    Refine Eq_resp suc;
      Immed;
Save;

Goal plusComm : {x,y:nat}Eq (plus x y) (plus y x);
Induction y;
  Refine plusZero;
  intros y yh x;
    Refine Eq_trans (plusSuc x y);
      Refine Eq_resp suc;
        Immed;
Save;

Goal plusCommA : {x,y,z:nat}Eq (plus x (plus y z)) (plus y (plus x z));
intros;
  Refine Eq_trans ? (plusAssoc ???);
    Refine Eq_trans (Eq_sym (plusAssoc ???));
      Refine Eq_resp ([w:nat]plus w z);
        Refine plusComm;
Save;

Goal timesZero : {x:nat}Eq (times x zero) zero;
Induction x;
  Refine Eq_refl;
    intros;
      Immed;
Save;

Goal timesSuc : {x,y:nat}Eq (times x (suc y)) (plus x (times x y));
Induction x;
  intros; Refine Eq_refl;
  intros x xh y;
    Equiv Eq (suc (plus y (times x (suc y)))) ?;
      Equiv Eq ? (suc (plus x (plus y (times x y))));
        Refine Eq_resp;
          Qrepl xh y;
            Refine plusCommA;
Save;

Goal timesComm : {x,y:nat}Eq (times x y) (times y x);
Induction y;
  Refine timesZero;
  intros y yh x;
    Refine Eq_trans (timesSuc ??);
      Refine Eq_resp (plus x);
        Immed;
Save;

Goal timesDistL : {x,y,z:nat}Eq (times (plus x y) z)
                                (plus (times x z) (times y z));
Induction x;
  intros; Refine Eq_refl;
    intros x xh y z;
      Refine Eq_trans (Eq_resp (plus z) (xh y z));
        Refine Eq_sym (plusAssoc ???);
Save;

Goal timesAssoc : {x,y,z:nat}Eq (times (times x y) z) (times x (times y z));
Induction x;
  intros; Refine Eq_refl;
  intros x xh y z;
    Refine Eq_trans (timesDistL ???);
      Refine Eq_resp (plus (times y z));
        Immed;
Save;

(**********************************************************************
   Inversion principles for equations governing plus and times:
   these aren't in the library, at least not in this form.
***********************************************************************)

[Phi|Type]; (* Inversion principles are polymorphic in any goal *)

Goal plusCancelL : {y,z|nat}{phi:{q':Eq y z}Phi}{x|nat}
                   {q:Eq (plus x y) (plus x z)}Phi;
intros ___;
Induction x;
  intros;
    Refine phi q;
  intros x xh; Qnify;
    Refine xh;
      Immed;
Save;

Goal timesToZero : {a,b|Nat}
                   {phiL:(Eq a zero)->Phi}
                   {phiR:(Eq b zero)->Phi}
                   {tz:Eq (times a b) zero}
                   Phi;
Induction a;
  intros; Refine phiL (Eq_refl ?);
  intros a;
    Induction b;
      intros; Refine phiR (Eq_refl ?);
      Qnify;
Save;

Goal timesToNonZero : {x,y|nat}
                      {phi:{x',y'|nat}(Eq x (suc x'))->(Eq y (suc y'))->Phi}
                      {z|nat}{q:Eq (times x y) (suc z)}Phi;
Induction x;
  Qnify;
  intros x xh;
    Induction y;
      intros __; Qrepl timesZero (suc x); Qnify;
      intros;
        [EQR=Eq_refl]; Refine phi Then Immed;
Save;

(* I actually want plusDivisionL, but plusDivisionR is easier to prove,
   because here we do induction where times does computation. *)
Goal plusDivisionR : {b|nat}{a,x,c|Nat}
                     {phi:{c'|nat}(Eq (times c' (suc x)) c)->
                                  (Eq a (plus b c'))->Phi}
                     {q:Eq (times a (suc x)) (plus (times b (suc x)) c)}
                     Phi;
Induction b;
  intros _____; Refine phi;
    Immed;
    Refine Eq_refl;
  intros b bh;
    Induction a;
      Qnify;
      intros a x c phi;
        Qrepl plusAssoc (suc x) (times b (suc x)) c;
          Refine plusCancelL;
            Refine bh;
              intros c q1 q2; Refine phi q1;
                Refine Eq_resp ? q2;
Save;

(* A bit of timesComm gives us the one we really need. *)
Goal plusDivisionL : {b|nat}{a,x,c|Nat}
                     {phi:{c'|nat}(Eq (times (suc x) c') c)->
                                  (Eq a (plus b c'))->Phi}
                     {q:Eq (times (suc x) a) (plus (times (suc x) b) c)}
                     Phi;
intros _____;
  Qrepl timesComm (suc x) a; Qrepl timesComm (suc x) b;
    Refine plusDivisionR;
      intros c'; Qrepl timesComm c' (suc x);
        Immed;
Save;

Discharge Phi;


(**************************************************************************
   Definition of primality:

   This choice of definition makes primality easy to exploit
   (especially as it's presented as an inversion principle), but hard to
   establish.
***************************************************************************)

[Prime = [p:nat]
         {a|NAT}{b,x|Nat}{Phi|Prop}
         {q:Eq (times p x) (times a b)}
         {phiL:{a':nat}
               (Eq a (times p a'))->(Eq x (times a' b))->Phi}
         {phiR:{b':nat}
               (Eq b (times p b'))->(Eq x (times a b'))->Phi}
         Phi
];


(**************************************************************************
   Proof that 2 is Prime. Nontrivial because of the above definition.
   Manageable because 1 is the only number between 0 and 2.
***************************************************************************)

Goal doublePlusGood : {x,y:nat}Eq (times (suc (suc x)) y)
                                  (plus (times two y) (times x y));
intros __;
  Refine Eq_trans ? (Eq_sym (plusAssoc ???));
    Refine Eq_resp (plus y);
      Refine Eq_trans ? (Eq_sym (plusAssoc ???));
        Refine Eq_refl;
Save;

Goal twoPrime : Prime two;
Expand Prime;
  Induction a;
    Induction n;
      intros useless b x _;
        Refine timesToZero Then Expand Nat Then Qnify;
                            (* Qnify needs to know it's a nat *)
          intros; Refine phiL;
            Refine +1 (Eq_sym (timesZero ?));
            Refine Eq_refl;
      Induction n;
        intros useless b x _;
          Qrepl plusZero b;
            intros; Refine phiR;
              Refine +1 Eq_sym q;
              Refine Eq_sym (plusZero x);
        intros n nhyp b x _;
          Qrepl doublePlusGood n b;
            Refine plusDivisionL;
              intros c q1 q2; Qrepl q2; intros __;
                Refine nhyp|one (Eq_refl ?) q1;
                  intros a' q3 q4; Refine phiL (suc a');
                    Refine Eq_resp suc;
                      Refine Eq_trans ? (Eq_sym (plusSuc ??));
                        Refine Eq_resp ? q3;
                    Refine Eq_resp (plus b) q4;
                  intros b' q3 q4; Refine phiR b';
                    Immed;
                    Qrepl q3; Qrepl q4;
                      Refine Eq_sym (doublePlusGood ??);
Save;


(**************************************************************************
   Now the proof that primes (>=2) have no rational root. It's the
   classic `minimal counterexample' proof unwound as an induction: we
   apply the inductive hypothesis to the smaller counterexample we
   construct.
***************************************************************************)

[pm2:nat]
[p=suc (suc pm2)] (* p is at least 2 *)
[Pp:Prime p];

Goal noRatRoot : {b|NAT}{a|Nat}{q:Eq (times p (times a a)) (times b b)}
                          and (Eq a zero) (Eq b zero);
Induction b;
  Induction n; (* if b is zero, so is a, and the result holds *)
    intros useless;
      intros a;
        Refine timesToZero;
          Expand Nat; Qnify;
          Refine timesToZero; Refine ?+1;
            intros; Refine pair; Immed; Refine Eq_refl;
    intros b hyp a q; (* otherwise, build a smaller counterexample *)
      Refine Pp q; (* use primality once *)
        Refine cut ?+1; (* standard technique for exploiting symmetry *)
          intros H a' aq1 aq2; Refine H;
            Immed;
            Refine Eq_trans aq2;
              Refine timesComm;
        intros c bq; Qrepl bq; Qrepl timesAssoc p c c;
          Refine timesToNonZero ? (Eq_sym bq); (* need c to be nonzero *)
            intros p' c' dull cq; Qrepl cq; intros q2;
              Refine Pp (Eq_sym q2); (* use primality twice *)
                Refine cut ?+1; (* symmetry again *)
                  intros H a' aq1 aq2; Refine H;
                    Immed;
                    Refine Eq_trans aq2;
                      Refine timesComm;
                intros d aq; Qrepl aq; Qrepl timesAssoc p d d;
                  intros q3;
                    Refine hyp ? (Eq_sym q3); (* now use ind hyp *)
                      Next +2; Expand NAT Nat; Qnify; (* trivial solution *)
                      Next +1; (* show induction was properly guarded *)
                        Refine Eq_trans bq; Expand p; Qrepl cq;
                          Refine plusComm;
Save;

Discharge pm2;

(**********************************************************************
   Putting it all together
***********************************************************************)

[noRatRootTwo = noRatRoot zero twoPrime
  : {b|nat}{a|nat}(Eq (times two (times a a)) (times b b))->
     (Eq a zero /\ Eq b zero)];

