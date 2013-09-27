Require Export opsem1. 

(* In this lecture we'll continue with a few more results
   about the extremely simple programming language that
   we've been working with for the last couple of lectures
   and then move on to a slightly larger and more
   interesting language... *)

(* ------------------------------------------------------ *)
(** * Multi-step Reduction *)

Module SimpleArithStepContd'.
Export SimpleArithStepContd.

(* Until now, we've been working with the SINGLE-STEP
   REDUCTION RELATION [step], which formalizes the
   individual steps of ABSTRACT MACHINE for executing
   programs.  It is also interesting to use this machine to
   evaluate programs to completion, to find out what final
   result they yield.  This can be formalized in two steps.

   First, we define a MULTI-STEP REDUCTION relation
   [stepmany], which relates terms [t] and [t'] if [t] can
   reach [t'] by any number (including 0) of single reduction 
   steps. 

   It turns out that it will be easier later on if we
   define [stepmany] using [refl_step_closure] rather than
   [refl_transitive_closure].  But don't get confused:
   [step]  is one of the constructors of [refl_step_closure]
   (the other is [refl]), which is NOT at all the same thing
   as our one-step reduction relation [step1].
*)

Notation stepmany := (refl_step_closure step1).

(* Note that we use Notation instead of Definition here.
   This means that [stepmany] will be automatically unfolded
   by Coq, which will simplify some of the proof automation
   later on. *)


(* We'll find the following Lemma useful.  Together with 
[rsc_transitive], it allows us to work establish rsc's as
as easily as rtc's. *)

Lemma rsc_R : forall (X:Set) (R:relation X) (x y : X),
       R x y -> refl_step_closure R x y.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* A few examples... *)
Lemma test_stepmany_1:
    stepmany
      (tm_plus
        (tm_plus (tm_const 0) (tm_const 3))
        (tm_plus (tm_const 2) (tm_const 4)))
      (tm_const (plus (plus 0 3) (plus 2 4))).
Proof.
  apply step with 
            (tm_plus
                (tm_const (plus 0 3))
                (tm_plus (tm_const 2) (tm_const 4))).
  apply E_Plus1. apply E_PlusConstConst.
  apply step with
            (tm_plus
                (tm_const (plus 0 3))
                (tm_const (plus 2 4))).
  apply E_Plus2. apply v_const. 
  apply E_PlusConstConst. 
  apply rsc_R. 
  apply E_PlusConstConst.
Qed.

Lemma test_stepmany_2:
    stepmany
      (tm_const 3)
      (tm_const 3).
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma test_stepmany_3:
    stepmany
      (tm_plus (tm_const 0) (tm_const 3))
      (tm_plus (tm_const 0) (tm_const 3)).
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma test_stepmany_4:
    stepmany
      (tm_plus
        (tm_const 0)
        (tm_plus
          (tm_const 2)
          (tm_plus (tm_const 0) (tm_const 3))))
      (tm_plus
        (tm_const 0)
        (tm_const (plus 2 (plus 0 3)))).
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* The second step is to define a "result" of a term [t] as
   a normal form that [t] can reach by some number of reduction
   steps.  Formally, we write [normal_form_of t t']
   to mean that [t'] is a normal form reachable from [t] by
   many-step reduction. *)

(* Writing "normal_form step1 t" all the time gets a bit
   ugly.  Let's introduce a more pronounceable shorthand: *)
Notation step1_normal_form := (normal_form step1).

Definition normal_form_of (t t' : tm) :=
  (stepmany t t' /\ step1_normal_form t').

(* We have already seen that single-step reduction is
   deterministic -- i.e., a given term can take a single
   step in at most one way.  It follows from this that, if
   [t] can reach a normal form, then this normal form is
   unique -- i.e., [normal_form_of] is a partial
   function. *)

Theorem normal_forms_unique:
  partial_function normal_form_of.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* Indeed, something stronger is true for this
   language (though not for all programming languages!): the
   reduction of ANY term [t] will eventually reach a normal
   form -- i.e., [normal_form_of] is a TOTAL function.
   Formally, we say the [step1] relation is NORMALIZING. 
*)

Definition normalizing (X:Set) (R:relation X) :=
  forall t, exists t',
    (refl_step_closure R) t t' /\ normal_form R t'.
Implicit Arguments normalizing [X]. 

(* To prove that [step1] is normalizing, we need a few
   lemmas.  First, we observe that, if [t] reduces to [t']
   in many steps, then the same sequence of reduction steps
   is possible when [t] appears as the left-hand child of a
   [tm_plus] node, and similarly when [t] appears as the
   right-hand child of a [tm_plus] node whose left-hand
   child is a value. *)

Lemma stepmany_congr_1 : forall t1 t1' t2,
     stepmany t1 t1'
  -> stepmany (tm_plus t1 t2) (tm_plus t1' t2).
Proof.
  intros t1 t1' t2 H. induction H.
    Case "rsc_refl". apply refl. 
    Case "rsc_step". apply step with (tm_plus y t2). 
        apply E_Plus1. apply H. 
        apply IHrefl_step_closure.
Qed.

Lemma stepmany_congr_2 : forall t1 t2 t2',
     value t1
  -> stepmany t2 t2'
  -> stepmany (tm_plus t1 t2) (tm_plus t1 t2').
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.


Theorem step1_normalizing :
  normalizing step1.
Proof.
  unfold normalizing.
  induction t.
    Case "tm_const". 
      exists (tm_const n). 
      split.
      SCase "l". apply refl. 
      SCase "r". apply value_is_nf. apply v_const.
    Case "tm_plus".
      destruct IHt1 as [t1' H1]. destruct IHt2 as [t2' H2].
      destruct H1 as [H11 H12]. destruct H2 as [H21 H22].
      apply nf_is_value in H12. apply nf_is_value in H22.
      inversion H12. inversion H22. 
      rewrite <- H in H11. 
      rewrite <- H0 in H21.
      exists (tm_const (plus n n0)).
      split.
        SCase "l". 
          apply rsc_transitive with (tm_plus (tm_const n) t2).
          apply stepmany_congr_1. apply H11.
          apply rsc_transitive with 
             (tm_plus (tm_const n) (tm_const n0)).
          apply stepmany_congr_2. apply v_const. apply H21.
          apply rsc_R. apply E_PlusConstConst.
        SCase "r". 
          apply value_is_nf. apply v_const.
Qed.

Lemma normal_form_to_forall : forall t,
  step1_normal_form t ->
  forall u, ~ step1 t u.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma normal_form_from_forall : forall t,
  (forall u, ~ step1 t u) ->
  step1_normal_form t.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

End SimpleArithStepContd'.
Notation normalizing := SimpleArithStepContd'.normalizing.

(* ================================================== *)

(* OK, enough about this ridiculously simple language!
   Let's move on to something a tiny bit more
   interesting... *)

(* -------------------------------------------------- *)
(** * The full arithmetic language *)

Module FullArith.

Inductive tm : Set :=
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_zero : tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_iszero : tm -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue tm_true
  | bv_false : bvalue tm_false.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tm_zero
  | nv_succ : forall t, nvalue t -> nvalue (tm_succ t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Inductive step1 : tm -> tm -> Prop :=
  | E_IfTrue : forall t1 t2,
        step1 (tm_if tm_true t1 t2)
             t1
  | E_IfFalse : forall t1 t2,
        step1 (tm_if tm_false t1 t2)
             t2
  | E_If : forall t1 t1' t2 t3,
        step1 t1 t1'
     -> step1 (tm_if t1 t2 t3)
             (tm_if t1' t2 t3)
  | E_Succ : forall t1 t1',
        step1 t1 t1'
     -> step1 (tm_succ t1)
             (tm_succ t1')
  | E_PredZero :
        step1 (tm_pred tm_zero)
             tm_zero
  | E_PredSucc : forall t1,
        nvalue t1
     -> step1 (tm_pred (tm_succ t1))
             t1
  | E_Pred : forall t1 t1',
        step1 t1 t1'
     -> step1 (tm_pred t1)
             (tm_pred t1')
  | E_IszeroZero :
        step1 (tm_iszero tm_zero)
             tm_true
  | E_IszeroSucc : forall t1,
        nvalue t1
     -> step1 (tm_iszero (tm_succ t1))
             tm_false
  | E_Iszero : forall t1 t1',
        step1 t1 t1'
     -> step1 (tm_iszero t1)
             (tm_iszero t1').

Notation step1_normal_form := (normal_form step1).

(* The first interesting thing about this language is that
   the progress theorem fails!  That is, there are terms
   that are normal forms -- they can't take a reduction
   step -- but not values -- i.e., we have not included them
   in our definition of possible "results of evaluation."
   Such terms are said to be STUCK. *)

Definition stuck (t:tm) : Prop :=
  step1_normal_form t /\ ~ value t.

Theorem not_step1_progress :
  exists t, stuck t.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* Fortunately, things are not completely messed up: values
   and normal forms are not the same in this language, but
   at least the former set is included in the latter (i.e.,
   we did not accidentally define things so that some value
   could still take a step). *)

Lemma value_is_nf : forall t,
  value t -> step1_normal_form t.
Proof.
  (* Hint: You will reach a point in this proof where you
     need to use an induction to reason about a term that is
     known to be a numeric value.  This induction can be
     performed either over the term itself or over the
     evidence that it is a numeric value.  The proof goes
     through in either case, but you will find that one way
     is quite a bit shorter than the other.  For the sake of
     the exercise, try to complete the proof both ways. *)
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* Here is a lemma that is a corollary of the previous
   fact (i.e., that follows immediately from it) but
   repackages its content in a way that will be convenient
   to use in later proofs. *)
Lemma values_don't_step : forall t t' P,
  value t -> step1 t t' -> P.
Proof.
  intros t t' P Hv He.
  apply value_is_nf in Hv. unfold normal_form in Hv. 
  impossible. 
  apply Hv. 
  exists t'. apply He. 
Qed.


(* The next thing to show is that the reduction relation
   for this larger language is still deterministic.  Since
   this involves a case analysis of two reduction
   derivations, each of which may end with any of 10
   constructors, this proof starts to get a little long!
   This is a good opportunity to really start using the 
   automation features we learned recently. 

   And here's another one: it often arises that the
   context contains a contradictory assumption and we want
   to use [inversion] on it to solve the goal.  We'd like to
   be able to say to Coq, "find a contradictory assumption
   and invert it" without giving its name explicitly.

   Unfortunately (and a bit surprisingly), Coq does not
   provide a built-in tactic that does this.  However, it is
   not too hard to define one ourselves.  (Thanks to Aaron
   Bohannon [at Penn] for this nice hack.) *)

Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; t ]
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

(* Again, the details of how the [Ltac] definition works are
   not important.  All we need to know is that doing [solve
   by inversion] will find a hypothesis that can be inverted
   to solve the goal, if there is one.  The tactics [solve
   by inversion 2] and [solve by inversion 3] are slightly
   fancier versions which will perform two or three
   inversions in a row, if necessary, to solve the goal. *)


(* OK: now for the theorem: *)


Theorem step1_deterministic:
  partial_function step1.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.





End FullArith.
