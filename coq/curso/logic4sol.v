(** * Relations as propositions
    *** Version of 10/30/2008
*)

(* A proposition parameterized over a number (like [evenI])
   can be thought of as a PREDICATE -- i.e., the subset of
   [nat] for which the proposition is provable.

   A two-argument proposition can be thought of as a
   RELATION -- i.e., the set of pairs for which the
   proposition is provable. 

   In this chapter, we explore this idea in detail.
*)

Require Export logic2.  (* We'll skip logic3 *)

(* For example, here is the "less than or equal" relation on
   numbers. *)
Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m:nat, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(* Note that the left-hand argument [n] to [le] is the same
   everywhere in the definition, so we've made it a general
   parameter.  This leads to a simpler induction
   principle. *)

(* THOUGHT EXERCISE: Print out the induction principle for
   [le] and check that you understand it.  Then try
   redefining [le] with [n] as an index rather than a
   general parameter (i.e., write the first line as
   [Inductive le : nat -> nat -> Prop]) and check how the
   generated induction principle changes. *)

(* Some sanity checks on the definition.  (Notice that,
   although these are the same kind of simple "unit tests"
   as we gave for the testing functions we wrote in the
   first few lectures, we must construct their proofs
   explicitly -- [simpl] doesn't do the job for us. *)
Lemma test_le1 :
  3 <= 3.
Proof.
  apply le_n.
Qed.
Lemma test_le2 :
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n.
Qed.
Lemma test_le3 :
  ~ (2 <= 1).
Proof.
  intros H. inversion H. inversion H1.
Qed.

(* The "strictly less than" relation [n < m] can now be
   defined on top of [le]. *)
Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(* Here are a few more simple relations on numbers *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (times n n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : evenI (S n) -> next_even n (S n)
  | ne_2 : evenI (S (S n)) -> next_even n (S (S n)).

(* EXERCISE: define an inductive relation [total_relation]
   that holds between every pair of natural numbers. *)
(* SOLUTION *)
Inductive total_relation : nat -> nat -> Prop :=
  tot : forall n m : nat, total_relation n m.

(* EXERCISE: define an inductive relation [empty_relation] (on
   numbers) that never holds. *)
(* SOLUTION *)
Inductive empty_relation : nat -> nat -> Prop :=
  .


(* --------------------------------------------------------- *)
(* Relations, in general *)

(* We've now defined a few particular relations.  As you may
   remember from an undergraduate discrete math course,
   there are a lot of ways of discussing and describing
   relations *in general* -- ways of classifying
   relations (are they reflexive, transitive, etc.),
   theorems that can be proved generically about classes of
   relations, constructions that build one relation from
   another, etc.  Let us pause here to review a few of these
   that will be useful in what follows. *)

(* A RELATION on a set [X] is a proposition parameterized by
   two [X]s -- i.e., it is a logical assertion involving two
   values from the set [X]. *)
Definition relation (X: Set) := X->X->Prop.

(* A relation [R] on a set [X] is a PARTIAL FUNCTION if, for
   every [x : X], there is at most one [y] such that [R x
   y] -- or, to put it differently, if [R x y1] and [R x y2]
   together imply [y1 = y2]. *)
Definition partial_function (X: Set) (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.
Implicit Arguments partial_function [X]. 

Lemma next_nat_partial_function : 
   partial_function next_nat.
Proof. 
  unfold partial_function.
  intros x y1 y2 P Q. 
  inversion P. inversion Q.
  reflexivity.
Qed.

Lemma le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros H.
  assert (1 = 2) as Nonsense.
   Case "Proof of assertion".
   apply H with 0. 
     apply le_S. apply le_n. 
     apply le_S. apply le_S. apply le_n. 
  inversion Nonsense. 
Qed.

(* EXERCISE: Show that the [total_relation] you defined
   above is not a partial function, but that
   [empty_relation] is. *)
(* SOLUTION *)
Lemma total_relation_not_a_partial_function :
  ~ (partial_function total_relation).
Proof.
  unfold not. unfold partial_function. intros H.
  assert (1 = 2) as Nonsense.
    Case "Proof of assertion". apply H with 0. 
      apply tot. 
      apply tot.
  inversion Nonsense.
Qed.
Lemma empty_relation_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function. intros n y1 y2 H1 H2. inversion H1.
Qed.

Definition reflexive (X: Set) (R: relation X) :=
  forall a : X, R a a.
Implicit Arguments reflexive [X]. 

Lemma le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n.
Qed.

Definition transitive (X: Set) (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).
Implicit Arguments transitive [X]. 

Lemma le_transitive :
  transitive le.
Proof.
  intros m n o Hmn Hno.
  induction Hno.
    apply Hmn.
    apply le_S. apply IHHno.
Qed.

Lemma lt_transitive:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros m n o Hmn Hno.
  destruct o. 
  Case "le_n".
    inversion Hno.
  Case "le_S".
    apply le_S in Hmn.
    apply le_transitive with (a := (S m)) (b := (S n)) (c := (S o)).
    apply Hmn. apply Hno.
Qed.


(* We can also prove lt_transitive more laboriously by induction, 
   without using le_transitive. *)
Lemma lt_transitive' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that [n] is 
     less than [o] *)
  unfold lt. unfold transitive.
  intros m n o Hmn Hno.
  induction Hno.
    (* SOLUTION *)
    Case "le_n". apply le_S in Hmn. apply Hmn.
    Case "le_S". apply le_S in IHHno. apply IHHno.
Qed.

Lemma lt_transitive'' :
  transitive lt.
Proof.
  (* Prove the same thing again by induction on [o] *)
  unfold lt. unfold transitive.
  intros m n o Hmn Hno.
  induction o.
    (* SOLUTION *)
    Case "O". inversion Hno.
    Case "S". inversion Hno.
      SCase "le_n". rewrite -> H0 in Hmn. apply le_S in Hmn. apply Hmn.
      SCase "le_S". apply IHo in H0. apply le_S in H0. apply H0.
Qed.


(* The transitivity of [le], in turn, can be used to prove some
   facts that are useful for the proof of antisymmetry below... *)
Lemma le_S_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_transitive with (b := S n).
    apply le_S. apply le_n.
    apply H.
Qed.

Lemma Sn_le_Sm__n_le_m : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros n m H. inversion H.
    apply le_n.
    apply le_S_le. apply H1.
Qed.

Lemma Sn_not_le_n : forall n,
  ~ (S n <= n).
Proof.
  induction n.
    Case "O". intros H. inversion H.
    Case "S". intros H. unfold not in IHn. apply IHn.
      apply Sn_le_Sm__n_le_m. apply H.
Qed.

Definition symmetric (X: Set) (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).
Implicit Arguments symmetric [X]. 

Lemma le_not_symmetric :
  ~ (symmetric le).
Proof.
  (* SOLUTION *)
  unfold symmetric. intros H.
  assert (1 <= 0) as Nonsense. 
    Case "Proof of assertion.". apply H. apply le_S. apply le_n.
  inversion Nonsense.
Qed.

Definition antisymmetric (X: Set) (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.
Implicit Arguments antisymmetric [X]. 

Lemma le_antisymmetric :
  antisymmetric le.
Proof.
  (* SOLUTION *)
  (* Here is a pretty proof due to Jianzhou Zhao: *)
  unfold antisymmetric. induction a.
    Case "O". intros b H1 H2. inversion H2. reflexivity.
    Case "S". destruct b.  
      SCase "O". intros H1 H2. inversion H1.
      SCase "S". intros H1 H2.
         apply  Sn_le_Sm__n_le_m in H1.
         apply  Sn_le_Sm__n_le_m in H2.
         apply IHa in H1.
            rewrite H1. reflexivity.
            apply H2.
Qed.
(* An uglier proof: *)
Lemma le_antisymmetric' : 
  antisymmetric le.
Proof.
  unfold antisymmetric. intros a b Hab Hba.
  inversion Hab.
    Case "le_n". reflexivity.
    Case "le_S". inversion Hba.
      SCase "le_n". rewrite <- H1. apply sym_eq. apply H0.
      SCase "le_S".
        rewrite <- H2 in H.
        rewrite <- H0 in H1.
        assert (S m0 <= m0) as bad.
          SSCase "Proof of assertion".
            apply le_transitive with (b:=m).
              SSSCase "S m0 <= m". apply H.
              SSSCase "m <= m0". apply le_transitive with (b:=S m).
                SSSSCase "m <= S m". apply le_S. apply le_n.
                SSSSCase "S m <= m0". apply H1.
        assert (~ (S m0 <= m0)) as L.
          SSCase "Proof of assertion". apply Sn_not_le_n.
        unfold not in L.
        apply L in bad. inversion bad.
Qed.

Definition equivalence (X:Set) (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).
Implicit Arguments equivalence [X]. 

Definition partial_order (X:Set) (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).
Implicit Arguments partial_order [X]. 

Definition preorder (X:Set) (R: relation X) :=
  (reflexive R) /\ (transitive R).
Implicit Arguments preorder [X]. 

Lemma le_partial_order :
  partial_order le.
Proof.
  unfold partial_order. split. 
    Case "refl". apply le_reflexive.
    split. 
      Case "antisym". apply le_antisymmetric. 
      Case "transitive.". apply le_transitive.
Qed.



(* Now we'll show a way to build one relation from another *)

Inductive refl_trans_closure (X:Set) (R: relation X) 
                  : X -> X -> Prop :=
  | rtc_R     : 
      forall (x y : X), R x y -> refl_trans_closure X R x y
  | rtc_refl  : 
      forall (x : X), refl_trans_closure X R x x
  | rtc_trans : 
      forall (x y z : X),
           refl_trans_closure X R x y
        -> refl_trans_closure X R y z
        -> refl_trans_closure X R x z.
Implicit Arguments refl_trans_closure [X]. 

(* For example, the reflexive and transitive closure of the [next_nat]
   relation "is" [le]. Note how we show these two relations "are" the
   same using <-> *)
Lemma next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((refl_trans_closure next_nat) n m).
Proof.
  intros n m. split.
    Case "->".
      intro H. induction H. 
         apply rtc_refl.
         apply rtc_trans with m. apply IHle. apply rtc_R. apply nn.
    Case "<-".
      intro H.  induction H.
        SCase "rtc_R".  inversion H. apply le_S.  apply le_n. 
        SCase "rtc_refl". apply le_n. 
        SCase "rtc_trans". 
           apply le_transitive with y.  apply IHrefl_trans_closure1. apply IHrefl_trans_closure2.
Qed.
Lemma rtc_idempotent : forall (X:Set) (R: relation X) (x y: X),
   refl_trans_closure (refl_trans_closure R) x y <-> refl_trans_closure R x y.
Proof.
  (* SOLUTION *)
  intros X R x y. 
   split. 
     intro P. induction P.
        apply H. 
        apply rtc_refl. 
        apply rtc_trans with y. apply IHP1. apply IHP2.
     intro P. induction P. 
        apply rtc_R. apply rtc_R. apply H. 
        apply rtc_refl. 
        apply rtc_trans with y. apply IHP1. apply IHP2. 
Qed.

(* Define what it means for a relation to preserve a property *)
Definition preserves (X: Set) (R: relation X) (P: X->Prop) :=
  forall (x y : X), P x -> R x y -> P y.
Implicit Arguments preserves [X]. 

Lemma rtc_preserves : forall (X: Set) (R: relation X) (P: X->Prop),
  preserves R P -> preserves (refl_trans_closure R) P.
Proof.
  (* SOLUTION *)
  intros X R P HR. unfold preserves. intros x y HPx Htc. induction Htc.
    Case "tc_R". unfold preserves in HR. apply HR with (x:=x)(y:=y).
      apply HPx. apply H.
    Case "tc_refl". apply HPx.
    Case "tc_trans". apply IHHtc2. apply IHHtc1. apply HPx.
Qed.

(* This definition of reflexive, transitive closure is the
   natural one -- it says, explicitly, that the reflexive
   and transitive closure of [R] is the least relation that
   includes [R] and that is closed under rules of
   reflexivity and transitivity.  But this definition turns
   out not always to be convenient for doing proofs -- the
   "nondeterminism" of the rtc_trans rule can sometimes lead
   to tricky inductions.  Here is a more useful
   definition... *)

Inductive refl_step_closure (X:Set) (R: relation X) 
                            : X -> X -> Prop :=
  | refl  : forall (x : X),
                 refl_step_closure X R x x
  | step : forall (x y z : X),
                    R x y
                 -> refl_step_closure X R y z
                 -> refl_step_closure X R x z.
Implicit Arguments refl_step_closure [X]. 

(* This new definition "bundles together" the rtc_R and
   rtc_trans rules into the single rule step.  The left-hand
   premise of this step is a single use of R, leading to a
   much simpler induction principle.

   Before we go on, we should check that the 2 definitions
   do indeed define the same relation... *)

Lemma rsc_transitive : 
  forall (X:Set) (R: relation X) (x y z : X),
      refl_step_closure R x y 
   -> refl_step_closure R y z
   -> refl_step_closure R x z.
Proof.
  (* SOLUTION *)
  intros X R x y z G H.
  induction G.
    Case "refl". assumption.
    Case "step". 
      eapply step. eassumption. 
      apply IHG. assumption.
Qed.

Lemma two_versions_of_rtc_coincide : 
         forall (X:Set) (R: relation X) (x y : X),
  refl_trans_closure R x y <-> refl_step_closure R x y.
Proof.
  (* SOLUTION *)
  intros X R x y.
  unfold iff. apply conj.
    Case "->".
      intros H. induction H.
        SCase "rtc_R".
          apply step with y. assumption. apply refl.
        SCase "rtc_refl".
          apply refl.
        SCase "rtc_trans".
          apply rsc_transitive with y. assumption. assumption.
    Case "<-".
      intros H. induction H.
        SCase "refl". apply rtc_refl.
        SCase "step". apply rtc_trans with y. apply rtc_R. 
          assumption. apply IHrefl_step_closure.
Qed. 
Inductive composition (X: Set) (Q R: relation X) 
             : X -> X -> Prop :=
  comp : forall x z, 
            (exists y, Q x y /\ R y z) 
         -> composition X Q R x z.



