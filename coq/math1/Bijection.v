
Load "Eqset".

(**** Bijections ****)

Definition bijection A B (f : e_set (A ==> B)) : Type :=
  forall b, { a | f $ a == b /\ forall a', f $ a' == b -> a == a' }.

Lemma bijection_injective :
  forall A B f (f_bij : bijection A B f) x y,
    f $ x == f $ y -> x == y.
Proof.
  intros A B f f_bij x y fx_eq_fy.
  unfold bijection in f_bij.
  elim f_bij with (f $ x).
  intros x0 Hx0.
  destruct Hx0 as (fx0_eq_fx, Hx1).
  apply e_transitive with x0.
  (* x == x0 *)
  specialize Hx1 with x.
  apply e_symmetric.
  apply Hx1.
  apply e_reflexive.
  (* x0 == y *)
  specialize Hx1 with y.
  apply Hx1.
  apply e_symmetric.
  assumption.
Qed.

(** Identity bijection **)

Definition e_bijection_identity A : e_set (A ==> A).
  simpl.
  unfold e_function_set.
  exists (fun a => a).
  intros.
  assumption.
Defined.

Lemma e_bijection_identity_is_bijection :
             forall A,
               bijection A A (e_bijection_identity A).
Proof.
  intro A.
  unfold bijection.
  intro a.
  exists a.
  split.
    simpl.
    apply e_reflexive.
    intro a'.
    simpl.
    intro.
    apply e_symmetric.
    assumption.
Qed.

(** Inverse of a bijection **)

Definition bijection_inverse_function A B f (f_bij : bijection A B f) b :
                                { a | f $ a == b /\
                                      forall a', f $ a' == b -> a == a'}.
  unfold bijection in f_bij.
  specialize f_bij with b.
  elim f_bij.
  intro a.  
  intro.
  exists a.
  assumption.
Defined.

Lemma bijection_inverse_left :
  forall A B f f_bij a,
      proj1_sig (bijection_inverse_function A B f f_bij (f $ a)) == a.
Proof.
  intros A B f f_bij a.
  case (bijection_inverse_function A B f f_bij (f $ a)).
  intros a0 a0_prop.
  destruct a0_prop as (fa0_eq_fa, a0_uniq).
  simpl.
  apply a0_uniq.
  apply e_reflexive.
Qed.
   
Lemma bijection_inverse_right :
  forall A B f f_bij b,
      f $ (proj1_sig (bijection_inverse_function A B f f_bij b)) == b.
Proof.
  intros A B f f_bij b.
  case (bijection_inverse_function A B f f_bij b).
  intros a0 a0_prop.
  destruct a0_prop.
  simpl.
  assumption.
Qed.

Definition e_bijection_inverse A B f (f_bij : bijection A B f) : e_set (B ==> A).
  simpl.
  unfold e_function_set.
  exists (fun b => proj1_sig (bijection_inverse_function A B f f_bij b)).
  intros.
  apply bijection_injective with (B := B) (f := f). 
  assumption.
  apply e_transitive with x.
  apply bijection_inverse_right.
  apply e_transitive with y.
  assumption.
  apply e_symmetric.
  apply bijection_inverse_right.
Defined.

Lemma e_bijection_inverse_is_bijection :
          forall A B f (f_bij : bijection A B f),
           bijection B A (e_bijection_inverse A B f f_bij).
Proof.
  intros A B f f_bij.
  unfold bijection.
  intros b.
  exists (f $ b).
  split.
    apply bijection_inverse_left.
    intros a a_prop.
    apply e_transitive with (f $ (e_bijection_inverse A B f f_bij $ a)).
    apply (proj2_sig f).
    apply e_symmetric.
    assumption.
    apply bijection_inverse_right.
Qed.

(** Composition of bijections **)

Definition e_bijection_composition
                      A B C f g
                      (f_bij : bijection B C f)
                      (g_bij : bijection A B g) : e_set (A ==> C).
  simpl.
  unfold e_function_set.
  exists (fun a => f $ (g $ a)).
  intros.
  apply (proj2_sig f).
  apply (proj2_sig g).
  assumption.
Defined.

Lemma e_bijection_composition_is_bijection :
          forall A B C f g
                 (f_bij : bijection B C f)
                 (g_bij : bijection A B g),
                   bijection A C (e_bijection_composition A B C f g f_bij g_bij).
Proof.
  intros A B C f g f_bij g_bij.
  unfold bijection.
  intro c.
  unfold bijection in f_bij.
  (* exists b,  c = f(b) *)
  elim f_bij with c.
  intros b b_prop.
  destruct b_prop as (fb_eq_c, b_uniq).
  (* exists a,  b = g(a) *)
  elim g_bij with b.
  intros a a_prop.
  destruct a_prop as (fa_eq_b, a_uniq).
  (**)
  exists a.
  split.
    simpl.
    apply e_transitive with (f $ b).
    apply (proj2_sig f).
    assumption.
    assumption.
    intros a2 a2_prop.
    simpl in a2_prop.
    assert (g $ a2 == b).
      apply bijection_injective with (B := C) (f := f).
      assumption.
      apply e_transitive with c. assumption.
      apply e_symmetric. assumption.
      apply bijection_injective with (B := B) (f := g).
      assumption.
      apply e_transitive with b. assumption.
      apply e_symmetric. assumption.
Qed.

(** Cardinal numbers **)

Definition eq_cardinal (A B : eqset) : Prop :=
  exists f : e_set (A ==> B), inhabited (bijection A B f).

Lemma eq_cardinal_reflexive : reflexive_relation eqset eq_cardinal.
Proof.
  unfold reflexive_relation.
  intro A.
  exists (e_bijection_identity A).
  apply inhabits.
  apply e_bijection_identity_is_bijection.
Qed.

Lemma eq_cardinal_symmetric : symmetric_relation eqset eq_cardinal.
Proof.
  unfold symmetric_relation.
  intros A B.
  intro bijAB; destruct bijAB as (f, inh_f_bij); elim inh_f_bij; intro f_bij.
  exists (e_bijection_inverse A B f f_bij).
  apply inhabits.
  apply e_bijection_inverse_is_bijection.
Qed.

Lemma eq_cardinal_transitive : transitive_relation eqset eq_cardinal.
Proof.
  unfold transitive_relation.
  intros A B C.
  intro bijAB; destruct bijAB as (g, inh_g_bij); elim inh_g_bij; intro g_bij.
  intro bijBC; destruct bijBC as (f, inh_f_bij); elim inh_f_bij; intro f_bij.
  exists (e_bijection_composition A B C f g f_bij g_bij).
  apply inhabits.
  apply e_bijection_composition_is_bijection.
Qed.

Lemma eq_cardinal_equivalence : equivalence_relation eqset eq_cardinal.
Proof.
  unfold equivalence_relation.
  split.
  apply eq_cardinal_reflexive.
  split.
  apply eq_cardinal_symmetric.
  apply eq_cardinal_transitive.
Qed.

(* Cannot define an eqset [ Error: Universe inconsistency ] *)
Definition cardinal : higher_order_eqset eqset :=
             mk_higher_order_eqset
                eqset
                eq_cardinal
                eq_cardinal_equivalence.
