(** * A Small-Step Abstract Machine
    *** Version of 11/5/2008
*)



Require Export logic5. 


(* Let's define an extremely simple programming language... *)
Inductive tm : Set :=
  | tm_const : nat -> tm
  | tm_plus : tm -> tm -> tm. 


(* .. and a couple of ways to give SEMANTICS (meaning) to this language. *)

(* One way is to give an INTERPRETER that maps each term to a number. *)
Fixpoint interp (t:tm) {struct t} : nat :=
  match t with
  | tm_const n => n
  | tm_plus t1 t2 => plus (interp t1) (interp t2)
  end.


Module SimpleArithStep.

(* Another approach is give a REDUCTION RELATION that converts
   terms to simpler terms.  By repeated application of this
   relation, we can reach terms that represent values (numbers). *)

Inductive step1 : tm -> tm -> Prop :=
  | E_PlusConstConst : forall n1 n2,
        step1 (tm_plus (tm_const n1) (tm_const n2))
             (tm_const (plus n1 n2))
  | E_Plus1 : forall t1 t1' t2,
        (step1 t1 t1')
     -> step1 (tm_plus t1 t2)
             (tm_plus t1' t2)
  | E_Plus2 : forall n1 t2 t2',
        (step1 t2 t2')
     -> step1 (tm_plus (tm_const n1) t2)
             (tm_plus (tm_const n1) t2').

(* THOUGHT EXERCISE: What induction principle is generated
   for [step1]? *)

(* Let's write some tests tht explore the behavior of the [step1]
   relation. *)

(* If [t1] can take a step to [t1'], then [tm_plus t1 t2]
   steps to [plus t1' t2]: *)
Lemma test_step1_2 : 
    step1
      (tm_plus 
        (tm_plus (tm_const 0) (tm_const 3))
        (tm_plus (tm_const 2) (tm_const 4)))
      (tm_plus 
        (tm_const (plus 0 3))
        (tm_plus (tm_const 2) (tm_const 4))).
Proof.
  apply E_Plus1. apply E_PlusConstConst.
Qed.

(* Right-hand sides of sums can take a step only when the
   left-hand side is finished: if [t2] can take a step to
   [t2'], then [tm_plus (tm_const n) t2] steps to
   [tm_plus (tm_const n) t2']: *)
Lemma test_step1_3: 
    step1
      (tm_plus 
        (tm_const 0)
        (tm_plus 
          (tm_const 2) 
          (tm_plus (tm_const 0) (tm_const 3))))
      (tm_plus 
        (tm_const 0)
        (tm_plus 
          (tm_const 2) 
          (tm_const (plus 0 3)))).
Proof. 
  (* SOLUTION *)
  apply E_Plus2. apply E_Plus2. apply E_PlusConstConst.
Qed.

(* Proofs of simple facts like this -- term [t] takes a step
   to become [t'] -- consist of sequences of applications of
   the three constructors of [step1] that, essentially,
   construct a data structure -- a tree whose single leaf is
   labeled E_PlusConstConst and whose internal nodes are
   labeled either [E_Plus1] or [E_Plus2] -- to serve as
   evidence for the assertion [step1 t t'].

   We use the term "tree" here even though each internal
   node has exactly one child (because the constructors
   [E_Plus1] and [E_Plus2] each take only one argument) so
   that the same terminology will apply to other inductive
   definitions where constructors take multiple arguments.

   These "evidence trees" are commonly called DERIVATIONS. *)

(* We can check that the [step1] relation preserves the 
   meaning of terms as defined by the [interp] function. *)
Theorem step1_preserves_interp : forall t t',
     step1 t t'
  -> interp t = interp t'.
Proof.
  intros t t' E. induction E.
    Case "E_PlusConstConst". reflexivity.
    Case "EPlus1". simpl. rewrite -> IHE. reflexivity.
    Case "E_Plus2". simpl. rewrite -> IHE. reflexivity.
Qed.


(* Side note: Formally, [Theorem] means precisely the same
   as [Lemma].  Calling something a [Theorem] is a signal to
   the human reader of a proof script that the assertion
   being proved is a particularly important or interesting
   one. *)

(* OPTIONAL EXERCISE: Is the word "preserves" in the name of
   this lemma being used in precisely the same sense as we
   did earlier?  That is, can the statement of the lemma be
   written in terms of the constant [preserves] that we
   defined above?  If yes, do so and give a proof.  If no,
   explain why not. *)

Theorem step1_preserves_interp_take2 : forall n,
     preserves step1 (fun t => interp t = n).
Proof.
  intros n. unfold preserves. intros t t' H1 H2. rewrite <- H1.
  apply sym_eq. apply step1_preserves_interp. apply H2.
Qed.


(* One interesting property of the [step1] relation is that
   it is DETERMINISTIC: for each [t], there is at most one
   [t'] such that [step1 t t'] is provable.  Formally, this
   is the same as saying that [step1] is a partial
   function. *)

Theorem step1_deterministic :
  partial_function step1.
Proof.
  (* Proof sketch: We must show that if [x] steps to
     both [y1] and [y2] then [y1] and [y2] are equal.
     Consider the last constructors used in the derivations
     of [step1 x y1] and [step1 x y2].
      - If both are [E_PlusConstConst], the result is
        immediate.
      - It cannot happen that one is [E_PlusConstConst] and
        the other is [E_Plus1] or [E_Plus2], since this
        would imply that [x] has the form [tm_plus t1 t2]
        where both [t1] and [t2] are constants (by
        [E_PlusConstConst]) AND one of [t1] or [t2] has the
        form [tm_plus ...].
      - Similarly, it cannot happen that one is [E_Plus1]
        and the other is [E_Plus2], since this would imply
        that [x] has the form [tm_plus t1 t2] where [t1] has
        both the form [tm_plus t1 t2] and the form [tm_const
        n].
      - The cases when both derivations end with [E_Plus1]
        or [E_Plus2] follow by the induction hypothesis. *)
  unfold partial_function. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1.
    Case "E_PlusConstConst". intros y2 Hy2. inversion Hy2.
      SCase "E_PlusConstConst". reflexivity.
      SCase "E_Plus1". inversion H2.
      SCase "E_Plus2". inversion H2.
    Case "E_Plus1". intros y2 Hy2. inversion Hy2.
      SCase "E_PlusConstConst".
        rewrite <- H0 in Hy1. inversion Hy1.
      SCase "E_Plus1".
        apply IHHy1 in H2. 
        rewrite <- H2. reflexivity.
      SCase "E_Plus2". rewrite <- H in Hy1. inversion Hy1.
    Case "E_Plus2". intros y2 Hy2. inversion Hy2.
      SCase "E_PlusConstConst". 
        rewrite <- H1 in Hy1. inversion Hy1.
      SCase "E_Plus1". 
        inversion H2.
      SCase "E_Plus2".
        apply IHHy1 in H2. 
        rewrite <- H2. reflexivity.
Qed.

End SimpleArithStep.

Module SimpleArithStepAgain.


(* Before we move on, let's take a moment to slightly
   generalize the way we state the definition of single-step
   reduction.

   It is useful to think of the [step1] relation as defining
   a sort of ABSTRACT MACHINE for evaluating programs:
      - At any moment, the STATE of the machine is a term.
      - A STEP of the machine is an atomic unit of
        computation -- a single "add" operation, in the case
        of the present tiny programming language.
      - The FINAL STATES of the machine are ones where there
        is no more computation to be done.

   We can then think about "executing" a term [t] as follows:
      - Take [t] as the starting state of the machine.
      - Repeatedly use the [step1] relation to find a
        sequence of machine states such that each steps
        to the next.
      - When no more reduction is possible, "read out" the
        final state of the machine as the result of
        execution.

   Intuitively, it is clear that the final states of the
   machine are always terms of the form [tm_const n] for
   some [n].  We call such terms VALUES. *)

Inductive value : tm -> Prop :=
  v_const : forall n, value (tm_const n).

(* Having introduced the idea of VALUES, we can use it in
   the definition of the [step1] relation to write [E_Plus2]
   rule in a slightly more intuitive way: *)

Inductive step1 : tm -> tm -> Prop :=
  | E_PlusConstConst : forall n1 n2,
        step1 (tm_plus (tm_const n1) (tm_const n2))
             (tm_const (plus n1 n2))
  | E_Plus1 : forall t1 t1' t2,
        (step1 t1 t1')
     -> step1 (tm_plus t1 t2)
             (tm_plus t1' t2)
  | E_Plus2 : forall v1 t2 t2',
        (value v1)                        (* <----- *)
     -> (step1 t2 t2')
     -> step1 (tm_plus v1 t2)
             (tm_plus v1 t2').

(* As a sanity check on this change, let's re-verify the
   properties we proved a few minutes ago... *)

Theorem step1_preserves_interp : forall t t',
     step1 t t'
  -> interp t = interp t'.
Proof.
  (* Like the one for the earlier definition of [step1], this
     proof is easy.  Try to do it without peeking. *)
  (* SOLUTION *)
  intros t t' E. induction E.
    Case "E_PlusConstConst". reflexivity.
    Case "EPlus1". simpl. rewrite -> IHE. reflexivity.
    Case "E_Plus2". simpl. rewrite -> IHE. reflexivity.
Qed.

Theorem step1_deterministic :
  partial_function step1.
Proof.
  (* Proof sketch: We must show that if [x] steps to
     both [y1] and [y2] then [y1] and [y2] are equal.
     Consider the last constructors used in the derivations
     of [step1 x y1] and [step1 x y2].
      - If both are [E_PlusConstConst], the result is
        immediate.
      - It cannot happen that one is [E_PlusConstConst] and
        the other is [E_Plus1] or [E_Plus2], since this
        would imply that [x] has the form [tm_plus t1 t2]
        where both [t1] and [t2] are constants (by
        [E_PlusConstConst]) AND one of [t1] or [t2] has the
        form [tm_plus ...].
      - Similarly, it cannot happen that one is [E_Plus1]
        and the other is [E_Plus2], since this would imply
        that [x] has the form [tm_plus t1 t2] where [t1]
        both has the form [tm_plus t1 t2] and is a
        value (hence has the form [tm_const n]).
      - The cases when both derivations end with [E_Plus1]
        or [E_Plus2] follow by the induction hypothesis. *)
  (* Most of this proof is the same as the one above.  But
     to get maximum benefit from the exercise you should try
     to write it from scratch and just use the earlier one
     if you get stuck. *)
  (* SOLUTION *)
  unfold partial_function. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1.
    Case "E_PlusConstConst". intros y2 Hy2. inversion Hy2.
      SCase "E_PlusConstConst". reflexivity.
      SCase "E_Plus1". inversion H2.
      SCase "E_Plus2". inversion H3.
    Case "E_Plus1". intros y2 Hy2. inversion Hy2.
      SCase "E_PlusConstConst". rewrite <- H0 in Hy1.
        inversion Hy1.
      SCase "E_Plus1".
        assert (t1' = t1'0) as eq.
          SSCase "Proof of assertion". apply IHHy1. apply H2.
        rewrite <- eq. reflexivity.
      SCase "E_Plus2". inversion H1. rewrite <- H4 in Hy1. inversion Hy1.
    Case "E_Plus2". intros y2 Hy2. inversion Hy2.
      SCase "E_PlusConstConst". rewrite <- H2 in Hy1. inversion Hy1.
      SCase "E_Plus1". inversion H. rewrite <- H4 in H3. inversion H3.
      SCase "E_Plus2".
        assert (t2' = t2'0) as eq.
          SSCase "Proof of assertion". apply IHHy1. apply H4.
        rewrite <- eq. reflexivity.
Qed.

End SimpleArithStepAgain.


Module SimpleArithStepContd.
Export SimpleArithStepAgain.

(* ------------------------------------------------ *)
(* Normal forms *)
(* In this language, every term is either a value or it can
   "make progress" by stepping to some other term. *)
Theorem progress : forall t,
  value t \/ (exists t', step1 t t').
Proof.  
  (* Proof sketch: By induction on [t].
        - If [t] is a constant, then it is a value.
        - If [t = tm_plus t1 t2], then by the IH [t1] and
          [t2] are either values or can take steps under
          [step1].
            - If [t1] and [t2] are both values, then [t] can
              take a step, by [E_PlusConstConst].
            - If [t1] is a value and [t2] can take a step,
              then so can [t], by [E_Plus2].
            - If [t1] can take a step, then so can [t], by
              [E_Plus1]. *)
  induction t.
    Case "tm_const". left. apply v_const.
    Case "tm_plus". right. inversion IHt1.
      SCase "l". inversion IHt2.
        SSCase "l". inversion H. inversion H0.
          exists (tm_const (plus n n0)).
          apply E_PlusConstConst.
        SSCase "r". inversion H0 as [t' H1].
          exists (tm_plus t1 t').
          apply E_Plus2. apply H. apply H1.
      SCase "r". inversion H as [t' H0]. 
          exists (tm_plus t' t2).
          apply E_Plus1. apply H0.
Qed.

(* This property can be extended to tell us something very
   interesting about values: they are EXACTLY the terms that
   cannot make progress in this sense.

   To state this fact, let's begin by giving a name to terms
   that cannot make progress: We'll call them NORMAL
   FORMS. *)
Definition normal_form (X:Set) (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.
Implicit Arguments normal_form [X].

(* We've actually defined what it is to be a normal form for
   an arbitrary relation [R] over an arbitrary set [X], not
   just for the particular reduction relation over terms
   that we are interested in at the moment.  We'll re-use
   the same terminology for talking about other relations
   later. *)

(* We can use this terminology to generalize the observation
   we made in Lemma [progress]: normal forms and values
   are actually the same thing. 

   Note that we state and prove this result as two different
   lemmas, rather than using an if-and-only-if (<->).
   That's because it will be easier to apply the separate
   lemmas later on; as noted before, Coq's facilities for
   dealing "in-line" with <> statements are a little awkward.
*)


Lemma value_is_nf : forall t,
  value t -> normal_form step1 t.
Proof.
  intros t H. unfold normal_form. intros contra. inversion H.
  rewrite <- H0 in contra. destruct contra as [t' P]. inversion P. 
Qed.

Lemma nf_is_value : forall t,
  normal_form step1 t -> value t.
  (* Proof sketch: This is a corollary of [progress]. *)
  intros t H.
  unfold normal_form in H.
  assert (value t \/ exists t', step1 t t') as G.
    SCase "Proof of assertion". apply progress.
  inversion G.
    SCase "l". apply H0.
    SCase "r". impossible. apply H. auto. 
Qed.

(* Why is these interesting facts?  For two reasons:
     - 1. Because [value] is a syntactic concept -- it is a
          defined by looking at the form of a term -- while
          [normal_form] is a semantic one -- it is defined
          by looking at how the term steps.  Is it not
          obvious that these concepts should coincide.
     - 2. Indeed, there are lots of languages in which the
          concepts of normal form and value do NOT coincide.

   Let's examine how this can happen... *)

(* We might, for example, accidentally define [value] so
   that it includes some terms that are not finished
   reducing. *)

Module Temp1. (* Open an inner module so we can redefine [value] 
                 and [step1]. *)

Inductive value : tm -> Prop :=
| v_const : forall n, value (tm_const n)
| v_funny : forall t1 n2,                       (* <---- *)
              value (tm_plus t1 (tm_const n2)).  

Inductive step1 : tm -> tm -> Prop :=
  | E_PlusConstConst : forall n1 n2,
        step1 (tm_plus (tm_const n1) (tm_const n2))
             (tm_const (plus n1 n2))
  | E_Plus1 : forall t1 t1' t2,
        (step1 t1 t1')
     -> step1 (tm_plus t1 t2)
             (tm_plus t1' t2)
  | E_Plus2 : forall v1 t2 t2',
        (value v1)
     -> (step1 t2 t2')
     -> step1 (tm_plus v1 t2)
             (tm_plus v1 t2').

Lemma value_not_same_as_normal_form :
  exists t, value t /\ ~ normal_form step1 t.
Proof.
  (* SOLUTION *)
   exists (tm_plus (tm_const 0) (tm_const 0)).
  split.
    Case "l". apply v_funny.
    Case "r". unfold normal_form. unfold not. intros H. apply H.
      exists (tm_const (plus 0 0)).
      apply E_PlusConstConst.
Qed.

End Temp1.

(* Alternatively, we might accidentally define [step1] so
   that it permits something designated as a value to
   reduce further. *)

Module Temp2.

Inductive value : tm -> Prop :=
| v_const : forall n, value (tm_const n).

Inductive step1 : tm -> tm -> Prop :=
  | E_Funny : forall n,                         (* <---- *)
        step1 (tm_const n)
             (tm_plus (tm_const n) (tm_const 0))
  | E_PlusConstConst : forall n1 n2,
        step1 (tm_plus (tm_const n1) (tm_const n2))
             (tm_const (plus n1 n2))
  | E_Plus1 : forall t1 t1' t2,
        (step1 t1 t1')
     -> step1 (tm_plus t1 t2)
             (tm_plus t1' t2)
  | E_Plus2 : forall v1 t2 t2',
        (value v1)
     -> (step1 t2 t2')
     -> step1 (tm_plus v1 t2)
             (tm_plus v1 t2').

Lemma value_not_same_as_normal_form :
  exists t, value t /\ ~ normal_form step1 t.
Proof.
  (* SOLUTION *)
  exists (tm_const 5).
  split.
    Case "l". apply v_const.
    Case "r". unfold normal_form. unfold not. intros H. apply H.
      exists (tm_plus (tm_const 5) (tm_const 0)).
      apply E_Funny.
Qed.

End Temp2.

(* Finally, we might accidentally define [value] and [step1]
   so that there is some term that is not a value but that
   cannot take a step in the [step1] relation.  Such terms
   are said to be STUCK. *)

Module Temp3.

Inductive value : tm -> Prop :=
| v_const : forall n, value (tm_const n).

Inductive step1 : tm -> tm -> Prop :=
  | E_PlusConstConst : forall n1 n2,
        step1 (tm_plus (tm_const n1) (tm_const n2))
             (tm_const (plus n1 n2))
  | E_Plus1 : forall t1 t1' t2,
        (step1 t1 t1')
     -> step1 (tm_plus t1 t2)
             (tm_plus t1' t2).
  (* <---- note that E_Plus2 is missing  *)

Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step1 t.
Proof.
  (* SOLUTION *)
  exists (tm_plus (tm_const 5)
                  (tm_plus (tm_const 6) (tm_const 7))).
  split.
    Case "l". intros H. inversion H.
    Case "r". unfold normal_form. unfold not. intros H. inversion H. 
      inversion H0. inversion H4.
Qed.

End Temp3.

End SimpleArithStepContd.

(* Copy definition of [normal_form] into the top-level
   environment so we can refer to it later. *)
Notation normal_form := SimpleArithStepContd.normal_form.

