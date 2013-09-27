(** * Logical Connectives
    *** Version of 10/20/2008
*)

(* Like its built-in programming language, Coq's built-in
   logic is extremely small: universal
   quantification ([forall]) and implication ([->]) are
   primitive, but all the other familiar logical
   connectives (conjunction, disjunction, negation, and
   existential quantification) can be defined using just
   these together with [Inductive]. *)

Require Export logic1.

(* ----------------------------------------------------- *)
(* Conjunction *)

(* The logical conjunction of propositions [A] and [B] is
   represented by the following inductively defined
   proposition. Note that definition is parameterized,
   in much the same we parameterized the inductive definition
   of the List type in Set. *)
Inductive and (A B : Prop) : Prop :=
  conj : A -> B -> (and A B). 

(* Intuition: To construct evidence for [and A B], we simply
   provide evidence for [A] and evidence for [B].

   More precisely:
      - [conj e1 e2] can be taken as evidence for [and A B]
        if [e1] is evidence for [A] and [e2] is evidence for
        [B]; and
      - this is the ONLY way to give evidence for [and A
        B] -- that is, if someone gives us evidence for [and
        A B], we know it must have the form [conj e1 e2],
        where [e1] is evidence for [A] and [e2] is evidence
        for [B]. *)



(* More familiar syntax: *)
Notation "A /\ B" := (and A B) : type_scope.

(* THOUGHT EXERCISE: See if you can predict the induction
   principle for conjunction. *)
Check and_ind.

(* What's nice about defining conjunction in this way is
   that we can prove statements involving conjunction using
   the tactics that we already know.  For example, if the
   goal statement is a conjuction, we can prove
   it ("backward") by applying the single constructor
   [conj], which (as can be seen from the type of [conj])
   solves the current goal and leaves the two parts of the
   conjunction as subgoals to be proved separately. *)
Lemma and_example : 
  (evenI 0) /\ (evenI 4).
Proof.
  apply conj.
    Case "left". apply even_0.
    Case "right". apply even_SS. apply even_SS. apply even_0. 
Qed.

(* Conversely, the [inversion] tactic can be used to
   investigate a conjunction hypothesis in the context and
   calculate what evidence must have been used to build
   it. *)
Lemma and_1 : forall A B : Prop, 
  A /\ B -> A.
Proof.
  intros A B H. 
  inversion H. 
  apply H0.
Qed.

(* In general, the [inversion] tactic 
      - takes a hypothesis H whose type is some inductively
        defined proposition A
      - for each constructor C in A's definition
          - generates a new subgoal in which we assume H was
            built with C
          - adds the arguments (premises) of C to the
            context of the subgoal as extra hypotheses
          - matches the conclusion (result type) of C
            against the current goal and calculates a set of
            equalities that must hold in order for C to be
            applicable
          - adds these equalities to the context of the
            subgoal
          - if the equalities are not satisfiable (e.g.,
            they involve things like [S n = O], immediately
            solves the subgoal.

   (This may look a bit different from the way we used
   [inversion] in earlier lectures, to extract additional
   equalities from an equality hypothesis by using the facts
   that the constructors of an inductive type are disjoint
   and injective.  But the fundamental mechanism is exactly
   the same.)

   In the case of [and], there is only one constructor, so
   only one subgoal gets generated.  And the
   conclusion (result type) of the constructor -- [A /\ B] 
   -- doesn't place any restrictions on the form of A and
   B, so we don't get any extra equalities in the context of
   the subgoal.  The constructor does have two arguments,
   though, and these can be seen in the context in the
   subgoal. *)

Lemma and_2 : forall A B : Prop, 
  A /\ B -> B.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* Here we use the [split] tactic, which is a convenient
   shorthand for [apply conj]. *)
Lemma and_commut : forall A B : Prop, 
  A /\ B -> B /\ A.
Proof.
  intros A B H.
  split.  
    Case "left". apply and_2 with (A:=A). apply H.
    Case "right". apply and_1 with (B:=B). apply H.
Qed.

Lemma and_assoc : forall A B C : Prop, 
  A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* Now we are in a position to prove the other direction of
   the equivalence of [evenE] and [evenI].  Notice that the
   left-hand conjunct here is the statement we are actually
   interested in; the right-hand conjunct is needed in order
   to make the induction hypothesis strong enough that we
   can carry out the reasoning in the inductive step.  (To
   see why this is needed, try proving the left conjunct by
   itself and observe where things get stuck.) *)
Lemma evenE_evenI : forall n : nat,
  (evenE n -> evenI n) /\ (evenE (S n) -> evenI (S n)).
Proof.
  (* Hint: Use induction on [n]. *)
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* ------------------------------------------------------ *)
(* Iff *)
(* The familiar logical "iff" is just the conjunction of two
   implications. *)

Definition iff (A B : Prop) := (A -> B) /\ (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.

Lemma iff_implies : forall A B : Prop, 
  (A <-> B) -> A -> B.
Proof.  
  intros A B H. 
  inversion H. apply H0.
Qed.

Lemma iff_sym : forall A B : Prop, 
  (A <-> B) -> (B <-> A).
Proof.
  intros A B H. 
  inversion H. 
  split. (* Note that [split] is just a bit smarter than [apply conj],
            which would have required an [unfold iff] first. *)
    Case "->". apply H1.
    Case "<-". apply H0.
Qed.


Lemma iff_refl : forall A : Prop, 
  A <-> A.
Proof. 
  (* OPTIONAL EXERCISE *) Admitted.

Lemma iff_trans : forall A B C : Prop, 
  (A <-> B) -> (B <-> C) -> (A <-> C).
Proof.
  (* Hint: If you have an iff hypothesis in the context, you
     can use [inversion] to break it into two separate
     implications.  (Think about why this works.) *)
  (* OPTIONAL EXERCISE *) Admitted.

(* Comment: propositions phrased with <-> are quite hard to use 
   as hypotheses or lemmas, because they have to be deconstructed
   into their two directed components in order to be applied.
   So many Coq developments avoid <->, despite its appealing compactness. *)


(* ------------------------------------------------------------ *)
(* Disjunction *)

(* Disjunction ("logical or") can also be defined as an inductive
   proposition. *)

Inductive or (A B : Prop) : Prop :=
  | or_introl : A -> or A B
  | or_intror : B -> or A B. 

Notation "A \/ B" := (or A B) : type_scope.

(* Intuition: There are two ways of giving evidence for [A \/ B]:
      - give evidence for [A] (and say that it is [A] you
        are giving evidence for! -- this is the function of
        the [or_introl] constructor)
      - give evidence for [B], tagged with the [or_intror]
        constructor. *)

(* Thought exercise: See if you can predict the induction
   principle for disjunction. *)
Check or_ind.

(* Since [A \/ B] has two constructors, doing [inversion] on
   a hypothesis of type [A \/ B] yields two subgoals. *)
Lemma or_commut : forall A B : Prop,
  A \/ B  -> B \/ A.
Proof.
  intros A B H.
  inversion H.
    Case "left". apply or_intror. apply H0.
    Case "right". apply or_introl. apply H0.
Qed.

(* From here on, we'll use the handy tactics [left] and 
[right] in place of [apply or_introl] and [apply or_intror]. *)

Lemma or_distributes_over_and_1 : forall A B C : Prop,
  A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
  intros A B C. intros H. inversion H. 
    Case "left". split.
      SCase "left". left. apply H0.
      SCase "right". left. apply H0.
    Case "right". split.
      SCase "left". right. inversion H0. apply H1.
      SCase "right". right. inversion H0. apply H2.
Qed.

Lemma or_distributes_over_and_2 : forall A B C : Prop,
  (A \/ B) /\ (A \/ C) -> A \/ (B /\ C).
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma or_distributes_over_and : forall A B C : Prop,
  A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C).
Proof.
  (* OPTIONAL EXERCISE *) Admitted.

(* [False] is an inductively defined proposition with no
constructors!  *)
Inductive False : Prop :=
  . 

(* Intuition: [False] is a proposition for which there is no
   way to give evidence. *)

(* THOUGHT EXERCISE: Can you predict the induction principle
   for falsehood? *)
Check False_ind.

Lemma False_implies_nonsense :
  False -> plus 2 2 = 5.
Proof.
  intros contra.
  inversion contra.
Qed. 

(* It *is* sometimes possible to prove the goal [False], but
   only if the context contains a contradiction (i.e., if
   the context allows us to prove anything at all). *)
Lemma nonsense_implies_False :
  plus 2 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.
Qed.

(* Truth *)
(* EXERCISE: [True] is another inductively defined proposition. 
   Define it!  Hint: the intution is that [True] should be a proposition
   for which it is always trivial to give evidence. 
*)
(* FILL IN HERE *)

(* Note that [True] isn't of tremendous practical use: it is
   trivial to prove as a goal, and it carries no useful information
   as a hypothesis.... *)

(* ---------------------------------------------------- *)
(* Negation *)

(* [not A], written [~A], is the logical negation of [A] *)
Definition not (A:Prop) := A -> False.

Notation "~ x" := (not x) : type_scope.

(* Intuition: If we could prove [A], then we could prove
   [False] (and hence we could prove anything at all). *)

Lemma not_False : 
  ~ False.
Proof.
  unfold not. intros H. inversion H.
Qed.

Lemma contradiction : forall A B : Prop,
  (A /\ ~A) -> B.
Proof.
  intros A B H. inversion H. unfold not in H1. 
  apply H1 in H0. inversion H0.
Qed.

Lemma double_neg : forall A : Prop,
  A -> ~~A.
Proof.
  intros A H. unfold not. intros G. apply G. apply H.
Qed.

Lemma contrapositive : forall A B : Prop,
  (A -> B) -> (~B -> ~A).
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma not_both_true_and_false : forall A : Prop,
  ~ (A /\ ~A).
Proof.
  (* OPTIONAL EXERCISE *) Admitted.

Lemma five_not_even :  
  ~ evenI 5.
Proof.
  unfold not. intros H. inversion H. inversion H1. inversion H3.
Qed.

Lemma even_not_even_S : forall n,
  evenI n -> ~ evenI (S n).
Proof.
  unfold not. intros n H. induction H. (* not n! *)
  (* OPTIONAL EXERCISE *) Admitted.

(* An optional exercise for those who like a challenge (from Coq'Art p. 123).
   The following five statements are often considered as
   characterizations of classical logic (as opposed to
   constructive logic, which is what is "built in" to Coq).
   We can't prove these in Coq, but we can add any one of them
   as an unproven axiom if we wish to work in classical logic.
   Prove that these five propositions are equivalent. *)
Definition peirce := forall P Q: Prop, ((P->Q)->P)->P.
Definition classic := forall P:Prop, ~~P -> P.
Definition excluded_middle := forall P:Prop, P \/~P.
Definition de_morgan_not_and_not := forall P Q:Prop, ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, (P->Q) -> (~P\/Q). 

(* ---------------------------------------------------------- *)
(* Inequality *)

(* Saying [x <> y] is just the same as saying [~ (x = y)]. *)
Notation "x <> y" := (~ (x = y)) : type_scope.

Lemma Sn_neq_n : forall n : nat,
  beq_nat (S n) n <> true.
Proof.
  intros n. induction n.
    Case "O". simpl. unfold not. intros H. inversion H. 
    Case "S". unfold not. intros H. unfold not in IHn. 
      apply IHn. apply H.
Qed.

Lemma not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
    Case "true". reflexivity.
    Case "false". unfold not in H. 
      assert False as contra. 
      SCase "Proof of assertion". 
        apply H. reflexivity. 
      inversion contra.
Qed.


(* That was pretty ugly.  We really want a nicer way to 
   replace an unprovable goal with False. Coq has one;
   we give it a memorable name. *)

Ltac impossible := elimtype False.

(* It never hurts to use this tactic as soon as you realize
   the goal is nonsense.  Once again...    *)
Lemma not_false_then_true' : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
    Case "true". reflexivity.
    Case "false". unfold not in H.  (* this is actually optional *)
      impossible.
      apply H. reflexivity. 
Qed.

Lemma beq_nat_n_n' : forall n n' : nat,
     n <> n'
  -> beq_nat n n' = false.
Proof.
  intros n n' H. unfold not in H. 
  remember (beq_nat n n') as e. destruct e. 
    (* Case "true (contradictory)". *)
      impossible. apply H. 
      apply sym_eq in Heqe. 
      apply beq_nat_true in Heqe. apply Heqe. 
    (* Case "false". *)
      reflexivity.
Qed.

Lemma beq_nat_false : forall m n,
  beq_nat m n = false -> m <> n.
Proof.
  (* OPTIONAL EXERCISE *) Admitted.


(* ------------------------------------------------------------ *)
(* Existential quantification *)

(* We saw a couple of lectures ago how a variety of logical
   connectives ([and], [or], etc.) can be encoded in Coq as
   inductively defined propositions.  Here is an inductive
   definition of one more important connective: existential
   quantification. *)

Inductive ex (X : Type) (P : X -> Prop) : Prop :=
  ex_intro : forall witness:X, P witness -> ex X P.

(* The intuition is that, in order to give evidence for the
   assertion "there is some x for which P holds" we must
   actually name a WITNESS
   -- a specific value x for which we can give evidence that
   P holds. *)

(* Next we add some convenient notation for the [ex] type.
   The details of how this works are not important: the
   critical point is that it allows us to write [exists x,
   P] or [exists x:t, P], just as we do with the [forall]
   quantifier.  *)
Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : t , p" := (ex _ (fun x:t => p))
  (at level 200, x ident, right associativity) : type_scope.

(* We can use the same set of tactics to manipulate
   existentials as we have been using all along.  For
   example, if to prove an existential, we [apply] the
   constructor [ex_intro].  Since the premise of [ex_intro]
   involves a variable ([witness]) that does not appear in
   its conclusion, we need to explicitly give its value when
   we use [apply]. *)
Lemma exists_example_1 : 
  exists n, plus n (times n n) = 6.
Proof.
  apply ex_intro with 2. 
  reflexivity.
Qed.

(* On the other hand, if we have an existential hypothesis
   in the context, we can eliminate it with [inversion]. *)
Lemma exists_example_2 : forall m,
     (exists n, m = plus 4 n)
  -> (exists o, m = plus 2 o).
Proof.
  intros m H.
  inversion H. 
  exists (plus 2 witness).  (* A handy shorthand tactic *)
  (* apply ex_intro with (witness := plus 2 witness). *)
  apply H0.
Qed.

Lemma dist_exists_or : forall (X:Set) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma dist_not_exists : forall (X:Set) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  (* OPTIONAL EXERCISE *) Admitted.


(* ------------------------------------------------------ *)
(* Equality. *)

(* As we mentioned near the beginning, even Coq's equality
relation is not really built in.  It has the following
inductive definition. (Again, we enclose this in a module to avoid
confusion with the standard library equality.) 
More about the mysterious Type annotation later. *)

Module MyEquality.

Inductive eq (A:Type) (x:A) : A -> Prop :=
    refl_equal : eq A x x.

(* This is a slightly weird-looking definition.  [eq] is
a proposition parameterized by three things: a type A
and two things of type A.  The first of these gets the
explicit name [x].  The definition says that 
the only acceptable evidence for two things being 
in the relation [eq] is that they are syntactically
identical.  This is the force of the repeated [x] in the
pattern for the [eq] constructor. *)

(* The induction principle for [eq] says that it 
represents so-called "Leibniz equality:" if two things are
equal and some predicate holds on one of them, then it
holds on the other too.*)
Check eq_ind.

End MyEquality.

