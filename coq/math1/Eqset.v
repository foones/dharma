
(**** Sets with an equivalence relation. ****)

Definition binary_relation A := A -> A -> Prop.

Definition reflexive_relation A (R : binary_relation A) := forall x, R x x.

Definition symmetric_relation A (R : binary_relation A) := forall x y, R x y -> R y x.

Definition transitive_relation A (R : binary_relation A) :=
  forall x y z, R x y -> R y z -> R x z.

Definition equivalence_relation A (R : binary_relation A) :=
     reflexive_relation A R /\
     symmetric_relation A R /\
     transitive_relation A R.

Structure higher_order_eqset (he_set : Type) :=
  mk_higher_order_eqset {
     he_eq : binary_relation he_set ;
     he_equivalence : equivalence_relation he_set he_eq
  }.

Structure eqset := mk_eqset {
     e_set : Type ;
     e_hoeqset : higher_order_eqset e_set
  }.

Definition mk_eqset_0 (e_set : Type)
                      (e_eq : binary_relation e_set)
                      (e_equivalence : equivalence_relation e_set e_eq)
  := mk_eqset
       e_set 
       (mk_higher_order_eqset
          e_set
          e_eq
          e_equivalence).

Definition e_eq A : binary_relation (e_set A) :=
  he_eq (e_set A) (e_hoeqset A).

Definition e_equivalence A : equivalence_relation (e_set A) (e_eq A) :=
  he_equivalence (e_set A) (e_hoeqset A).

Notation "a == b" := (e_eq _ a b) (at level 45).

Lemma e_reflexive : forall A (x : e_set A), x == x.
Proof.
  intros A x.
  assert (reflexive_relation (e_set A) (e_eq A)).
  apply e_equivalence.
  apply H.
Qed.

Lemma e_symmetric : forall A (x y : e_set A), x == y -> y == x.
Proof.
  intros A x y x_eq_y.
  assert (symmetric_relation (e_set A) (e_eq A)).
  apply e_equivalence.
  apply H.
  assumption.
Qed.

Lemma e_transitive : forall A (x y z : e_set A), x == y -> y == z -> x == z.
Proof.
  intros A x y z x_eq_y y_eq_z.
  assert (transitive_relation (e_set A) (e_eq A)).
  apply e_equivalence.
  apply H with y.
  assumption.
  assumption.
Qed.

Definition e_function_set (A B : eqset) : Type := 
  { f : e_set A -> e_set B |
      forall x y, x == y -> f x == f y }.

Definition e_function_eq A B (f g : e_function_set A B) : Prop :=
  forall x, e_eq B (proj1_sig f x) (proj1_sig g x).

Lemma e_function_eq_equivalence A B :
          equivalence_relation (e_function_set A B) (e_function_eq A B).
Proof.
  assert (equivalence_relation (e_set B) (e_eq B)) as eqB_equivalence.
    apply e_equivalence.
  destruct eqB_equivalence as (refl, (sym, trans)).
  unfold equivalence_relation.
  split.
    (* refl *)
    unfold reflexive_relation.
    unfold e_function_eq. 
    intros.
    apply refl.
  split.
    (* sym *)
    unfold symmetric_relation.
    unfold e_function_eq.
    intros f g H x.
    apply sym.
    specialize H with x.
    assumption.
    (* trans *)
    unfold transitive_relation.
    unfold e_function_eq.
    intros f g h Hfg Hgh x.
    apply trans with (proj1_sig g x).
    specialize Hfg with x.
    assumption.
    specialize Hgh with x.
    assumption.
Qed.

Definition e_function (A B : eqset) : eqset :=
  mk_eqset_0 (e_function_set A B)
             (e_function_eq A B)
             (e_function_eq_equivalence A B).

Notation "A ==> B" := (e_function A B) (at level 35, right associativity).

Definition e_apply A B (f : e_set (A ==> B)) (x : e_set A) :=
  proj1_sig f x.

Notation "f $ x" := (e_apply _ _ f x) (at level 35).

Lemma eq_equivalence : forall A, equivalence_relation A eq.
Proof.
  intros.
  unfold equivalence_relation.
  split.
    (* refl *)
    unfold reflexive_relation.
    intros.
    apply eq_refl.
  split.
    (* sym *)
    unfold symmetric_relation.
    intros.
    apply eq_sym.
    assumption.
    (* trans *)
    intros x y z.
    intros.
    apply eq_trans with y.
    assumption.
    assumption.
Qed.

Definition e_lift (A : Type) : eqset := mk_eqset_0 A eq (eq_equivalence A).

Definition e_lift_function A B (f : A -> B) : e_set (e_lift A ==> e_lift B).
  simpl.
  unfold e_function_set.
  exists f.
  intros x y x_eq_y.
  compute.
  compute in x_eq_y.
  apply f_equal.
  assumption.
Defined.

Lemma iff_equivalence : equivalence_relation Prop iff.
Proof.
  unfold equivalence_relation. 
  split.
  unfold reflexive_relation. apply iff_refl.
  split.
  unfold symmetric_relation. apply iff_sym.
  unfold transitive_relation. apply iff_trans.
Qed.

Definition e_Prop := mk_eqset_0 Prop iff iff_equivalence.

Definition e_subset_set A (P : e_set (A ==> e_Prop)) := {x | (P $ x)}.

Definition e_subset_eq A P (x y : e_subset_set A P) : Prop :=
  e_eq A (proj1_sig x) (proj1_sig y).

Lemma e_subset_eq_equivalence A P :
  equivalence_relation (e_subset_set A P) (e_subset_eq A P).
Proof.
  assert (equivalence_relation (e_set A) (e_eq A)) as eq_equivalence.
    apply e_equivalence.
  unfold equivalence_relation in eq_equivalence.
  destruct eq_equivalence as (refl, (sym, trans)).
  unfold equivalence_relation. 
  split.
    (* refl *) 
    unfold reflexive_relation.
    intros.
    apply refl.
  split.
    (* sym *) 
    unfold symmetric_relation.
    intros.
    apply sym.
    assumption.
    (* trans *) 
    unfold transitive_relation.
    intros x y z.
    intros.
    unfold e_subset_eq.
    apply trans with (proj1_sig y).
    assumption.
    assumption.
Qed.

Definition e_mk_subset A (P : e_set (A ==> e_Prop)) : eqset :=
  mk_eqset_0 (e_subset_set A P)
             (e_subset_eq A P)
             (e_subset_eq_equivalence A P).

Definition e_binary_relation A := A ==> A ==> e_Prop.

Definition e_apply_binary_relation A :
             e_set (e_binary_relation A) -> binary_relation (e_set A) :=
  fun R x y => R $ x $ y.

Definition e_equivalence_relation A (R : e_set (e_binary_relation A)) :=
  equivalence_relation (e_set A) (e_apply_binary_relation A R).

Definition e_mk_quotient A Eq (Eq_equivalence : e_equivalence_relation A Eq) :=
  mk_eqset_0 (e_set A) (e_apply_binary_relation A Eq) Eq_equivalence.

Definition removal_function A (x : e_set A) : e_set (A ==> e_Prop).
  simpl.
  unfold e_function_set.
  exists (fun y => ~(x == y)).
  intros x1 y x1_eq_y.
  split.
    (* -> *)
    intros H1 H2.
    assert (x == x1).
    apply e_transitive with y. 
    assumption.
    apply e_symmetric; assumption.
    contradiction.
    (* <- *)
    intros H1 H2.
    assert (x == y).
    apply e_transitive with x1. 
    assumption.
    assumption.
    contradiction.
Defined.

Definition eqset_remove A (x : e_set A) := e_mk_subset A (removal_function A x).