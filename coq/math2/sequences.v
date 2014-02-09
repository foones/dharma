Require Import Rdefinitions.
Require Import RIneq.

Require Import Description.
  (* constructive_definite_description  [[ exists! x, P x -> { x | P x } ]] *)
Require Import Classical.
  (* NNPP [double negation] *)
Require Import ClassicalDescription.
  (* excluded_middle_informative : {P} + {~P} *)

Open Scope R.

Definition Rpositive : Type := { x : R | x > 0 }.

Definition sequence (A : Type) : Type := nat -> A.

Definition dist_lt (a b c : R) := b - c < a /\ a < b + c.

Lemma dist_lt_sym : forall a b c, dist_lt a b c -> dist_lt b a c.
Proof.
  intros a b c.
  unfold dist_lt.
  intro H.
  destruct H as (bmc_lt_a, a_lt_bpc).
  split.
  apply Rplus_lt_reg_r with c.
  rewrite Rplus_minus.
  rewrite Rplus_comm.
  assumption.
  apply Rplus_lt_reg_r with (- c).
  rewrite Rplus_comm.
  replace (a + c) with (a - - c).
  replace (b + - c) with (b - c).
  rewrite Rplus_minus.
  assumption.
  unfold Rminus.
  reflexivity.
  unfold Rminus.
  rewrite Ropp_involutive.
  reflexivity.
Qed.

Lemma dist_lt_triang : forall a b c d1 d2,
                         dist_lt a b d1 ->
                         dist_lt b c d2 ->
                         dist_lt a c (d1 + d2).
Proof.
  intros a b c d1 d2.
  unfold dist_lt.
  intros dab dbc.
  split.
  unfold Rminus.
  rewrite Ropp_plus_distr.
  rewrite Rplus_comm.
  rewrite Rplus_assoc.
  assert (- d2 + c = c - d2) as H.
    rewrite Rplus_comm; unfold Rminus; reflexivity.
  rewrite H.
  apply Rlt_trans with (- d1 + b).
  rewrite Rplus_comm. 
  replace (- d1 + b) with (b  + - d1).
  apply Rplus_lt_compat_r.
  apply dbc.
  apply Rplus_comm.
  rewrite Rplus_comm.
  apply dab.
  replace (c + (d1 + d2)) with ((c + d2) + d1).
  apply Rlt_trans with (b + d1).
  apply dab.
  apply Rplus_lt_compat_r.
  apply dbc.
  rewrite Rplus_assoc. 
  replace (d1 + d2) with (d2 + d1).
  reflexivity.
  apply Rplus_comm.
Qed.   

Definition strictly_increasing (f : nat -> nat) : Prop :=
  forall n m, lt n m -> lt (f n) (f m).
   
Definition subsequence (s sub : sequence R) : Prop :=
  exists n_ : nat -> nat,
    strictly_increasing n_ /\ forall k, sub k = s (n_ k).

Definition upper_bound (s : sequence R) M : Prop :=
  forall n, s n <= M.

Definition least_upper_bound (s : sequence R) lub : Prop :=
  upper_bound s lub /\
  forall lub', upper_bound s lub' -> lub <= lub'.

Definition nat_ge (n_0 : nat) : Type := { n : nat | ge n n_0 }.

Definition converges (s : sequence R) limit : Prop :=
                     forall eps : Rpositive,
                       exists n_0 : nat, forall n : nat_ge n_0,
                         dist_lt limit (s (proj1_sig n)) (proj1_sig eps).

Lemma sig_to_exists :
  forall A P, { x : A | P x } -> exists x : A, P x.
Proof.
  intros A P S.
  exists (proj1_sig S).
  apply (proj2_sig S).
Qed.

Definition ubounded_sequence := { s : sequence R & { M : R | upper_bound s M } }.

Notation "seq $ n" := (projT1 seq n) (at level 35).

Lemma ubounded_has_lub :
  forall seq : ubounded_sequence,
    exists supremum, least_upper_bound (projT1 seq) supremum.
Proof.
  (*** seq = s M M_bound ***)
  intros seq. apply sig_to_exists.
  assert { m : R | is_lub (fun x => exists n, seq $ n = x) m} as has_lub.
    apply completeness.
    (* bound *)
    unfold bound. exists (proj1_sig (projT2 seq)).
    unfold is_upper_bound. intros x x_eq_sn_prop.
    elim x_eq_sn_prop. intros n sn_eq_x. rewrite <- sn_eq_x.
    apply (proj2_sig (projT2 seq)).
    (* nonempty *)
    exists (seq $ 0%nat). exists 0%nat. reflexivity.
  assert (is_lub (fun x => exists n, seq $ n = x) (proj1_sig has_lub))
      as has_lub_prop.
    apply (proj2_sig has_lub).
  exists (proj1_sig has_lub). unfold is_lub in has_lub_prop.
  destruct has_lub_prop as (has_lub_upper, has_lub_least).
  unfold least_upper_bound. split. unfold is_upper_bound in has_lub_upper.
  unfold upper_bound. intro n. specialize has_lub_upper with (seq $ n).
  apply has_lub_upper. exists n.
  reflexivity.
  intro lub2. specialize has_lub_least with lub2. intro lub2_bound.
  apply has_lub_least. unfold is_upper_bound. intros x x_shape.
  elim x_shape. intros n sn_eq_x. rewrite <- sn_eq_x.
  unfold upper_bound in lub2_bound. specialize lub2_bound with n.
  apply lub2_bound.
Qed.

Lemma ubounded_has_unique_lub :
  forall seq : ubounded_sequence,
    exists! supremum, least_upper_bound (projT1 seq) supremum.
Proof.
  intros seq.
  assert (exists supremum, least_upper_bound (projT1 seq) supremum) as sup_exists.
    apply ubounded_has_lub.
  elim sup_exists.
  intros sup sup_is_lub.
  exists sup.
  unfold unique.
  split.
  assumption.
  intros sup2 sup2_is_lub.
  apply Rle_antisym.
  apply sup_is_lub. apply sup2_is_lub.
  apply sup2_is_lub. apply sup_is_lub.
Qed.

Definition increasing_R (s : sequence R) :=
  forall n m, le n m -> s n <= s m.

Definition sup (seq : ubounded_sequence) : R.
  apply proj1_sig with (least_upper_bound (projT1 seq)).
  apply constructive_definite_description.
  apply (ubounded_has_unique_lub seq).
Defined.

Lemma sup_is_lub : forall seq : ubounded_sequence,
                     least_upper_bound (projT1 seq) (sup seq).
Proof.
  intros seq.
  unfold sup.
  apply (proj2_sig (constructive_definite_description
                      (least_upper_bound (projT1 seq))
                      (ubounded_has_unique_lub seq))).
Qed.

Lemma sup_epsilon_property :
  forall seq : ubounded_sequence,
    forall eps : Rpositive,
      exists n, (seq $ n) > sup seq - proj1_sig eps.
Proof.
  intros seq eps.
  apply not_all_not_ex.
  intro H.
  assert (forall n, seq $ n <= sup seq - proj1_sig eps).
  intro n.
  apply Rnot_lt_le.
  apply H.
  assert (sup seq <= sup seq - proj1_sig eps) as H_sup_le.
  apply sup_is_lub.
  assumption.
  assert (sup seq > sup seq - proj1_sig eps) as H_sup_gt.
  apply tech_Rgt_minus.
  apply (proj2_sig eps).
  apply Rlt_not_le in H_sup_gt. 
  contradiction.
Qed.

Lemma dneg_inv : forall P : Prop, P -> ~ ~ P.
Proof.
  intros P H.
  intro.
  contradiction.
Qed.

Definition eventually (s : sequence R) (P : R -> Prop) :=
  exists n0, forall n : nat_ge n0, P (s (proj1_sig n)).

Definition finitely_many (s : sequence R) (P : R -> Prop) :=
  eventually s (fun x => not (P x)).

Definition infinitely_many (s : sequence R) (P : R -> Prop) :=
  forall n0, exists n : nat_ge n0, P (s (proj1_sig n)).

Lemma infinitely_not_finitely_equiv :
  forall (s : sequence R) (P : R -> Prop),
    infinitely_many s P <-> ~finitely_many s P.
Proof.
  unfold infinitely_many.
  unfold finitely_many.
  unfold eventually.
  intros s P.
  split.
  (* -> *)
    intro H. apply all_not_not_ex. intro n. specialize H with n.
    elim H. intros n0 Pn0. intro HH. specialize HH with n0.
    contradiction.
  (* <- *)
    intro H.
    assert ((~exists n0: nat, forall n: nat_ge n0, ~P (s (proj1_sig n)))
           -> 
            (forall n0: nat, ~forall n: nat_ge n0, ~P (s (proj1_sig n))))
        as Impl.
      apply (not_ex_all_not nat (fun n0 => forall n : nat_ge n0, ~ P (s (proj1_sig n)))).
    assert (forall n0: nat, ~forall n: nat_ge n0, ~P (s (proj1_sig n)))
        as H2.
      apply Impl.
      apply H.
    apply not_ex_not_all. intro HH. elim HH. intro n. specialize H2 with n.
    apply dneg_inv. apply not_all_not_ex in H2.
    assumption.
Qed.

Lemma finitely_infinitely_PEM :
  forall (s : sequence R) (P : R -> Prop),
    { finitely_many s P } + { infinitely_many s P }.
Proof.
  intros.
  assert ({ finitely_many s P } + { ~finitely_many s P }) as H.
    apply excluded_middle_informative.
  destruct H.
  left; assumption.
  right; apply infinitely_not_finitely_equiv; assumption.
Qed.

Lemma Rlt_add_lt_sub_l : forall x y z,
                           x - y < z -> x < z + y.
Proof.
  intros x y z.
  intro H.
  apply Rplus_lt_reg_r with (-y).
  replace (- y + x) with (x - y).
  replace (-y + (z + y)) with z.
  assumption.
  rewrite <- Rplus_assoc.
  rewrite Rplus_comm.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_l.
  reflexivity.
  rewrite Rplus_comm.
  unfold Rminus.
  reflexivity.
Qed.

Lemma Rminus_pos_lt : forall eps : Rpositive,
                        forall x, x - proj1_sig eps < x.
Proof.
  intros eps x.
  apply Rplus_lt_reg_r with (-x).
  unfold Rminus.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  apply Ropp_lt_gt_0_contravar.
  apply (proj2_sig eps).
Qed.

Lemma ubounded_increasing_converges_to_sup :
  forall seq : ubounded_sequence,
      increasing_R (projT1 seq) ->
      converges (projT1 seq) (sup seq).
Proof.
  intros seq seq_increasing.
  unfold converges.
  intro eps.
  assert (forall n : nat, seq $ n <= proj1_sig (projT2 seq)).
    apply (proj2_sig (projT2 seq)).
  assert (exists n0 : nat, sup seq - proj1_sig eps < seq $ n0)
      as ex_n0.
    apply sup_epsilon_property.
  elim ex_n0.
  intros n0 sup_minus_eps_lt_seq_n0.
  exists n0.
  intro n.
  split.
  (* 1 *)
  apply Rlt_le_trans with (seq $ proj1_sig n).
  apply Rminus_pos_lt.
  apply sup_is_lub.
  (* 2 *)
  apply Rlt_le_trans with (seq $ n0 + proj1_sig eps).
  apply Rlt_add_lt_sub_l.
  assumption.
  apply Rplus_le_compat_r.
  apply seq_increasing.
  apply (proj2_sig n).
 Qed.
