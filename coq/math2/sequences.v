Require Import Rdefinitions.
Require Import RIneq.

Require Import Description.
  (* constructive_definite_description  [[ exists! x, P x -> { x | P x } ]] *)
Require Import Classical.
  (* NNPP [double negation] *)
Require Import ClassicalDescription.
  (* excluded_middle_informative : {P} + {~P} *)
Require Import ClassicalEpsilon.
  (* constructive_indefinite_description : exists x, P x -> { x | P x } *)

(**** Auxiliary definitions and lemmas ****)

Definition nat_ge (n_0 : nat) : Type := { n : nat | ge n n_0 }.
  
Lemma nat_ge_max_l : forall m n, (max m n >= m)%nat.
Proof. intros m n. apply Max.le_max_l. Qed.

Lemma nat_ge_max_r : forall m n, (max m n >= n)%nat.
Proof. intros m n. apply Max.le_max_r. Qed.

Lemma dneg_inv : forall P : Prop, P -> ~ ~ P.
Proof.
  intros P H.
  intro.
  contradiction.
Qed.

Lemma sig_to_exists :
  forall A P, { x : A | P x } -> exists x : A, P x.
Proof.
  intros A P S.
  exists (proj1_sig S).
  apply (proj2_sig S).
Qed.

(**** Abstract sequences on a generic type A ****)

Section Sequences.

  Variable A : Type.

  Definition sequence : Type := nat -> A.

  Definition eventually (s : sequence) (P : A -> Prop) :=
    exists n0, forall n : nat_ge n0, P (s (proj1_sig n)).

  Definition finitely_many (s : sequence) (P : A -> Prop) :=
    eventually s (fun x => not (P x)).

  Definition infinitely_many (s : sequence) (P : A -> Prop) :=
    forall n0, exists n : nat_ge n0, P (s (proj1_sig n)).

  Lemma infinitely_not_finitely_equiv :
    forall (s : sequence) (P : A -> Prop),
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
    forall (s : sequence) (P : A -> Prop),
      { finitely_many s P } + { infinitely_many s P }.
  Proof.
    intros.
    assert ({ finitely_many s P } + { ~finitely_many s P }) as H.
      apply excluded_middle_informative.
    destruct H.
    left; assumption.
    right; apply infinitely_not_finitely_equiv; assumption.
  Qed.

  (* Given a decidable property P : R -> Prop
   * on terms of a sequence,
   * either P(a_n) holds for infinitely many values of n
   * or    ~P(a_n) holds for infinitely many values of n
   * these conditions are not necessarily exclusive.
   *)
  Lemma infinitely_many_PEM :
    forall (s : sequence) (P : A -> Prop),
      { infinitely_many s P } + { infinitely_many s (fun x => ~(P x)) }.
  Proof.
    intros.
    assert ({ finitely_many s P } + { infinitely_many s P }) as H.
      apply finitely_infinitely_PEM.
    destruct H as [fin | infin].
    right.
      unfold finitely_many in fin.
      unfold eventually in fin.
      unfold infinitely_many.
      intro n0.
      destruct fin as (m0, H).
      unfold nat_ge in H.
      specialize H with (exist _ (max n0 m0) (nat_ge_max_r n0 m0)).
      exists (exist _ (max n0 m0) (nat_ge_max_l n0 m0)).
      assumption.
    left. assumption.
  Qed.

  Lemma infinitely_many_implies :
    forall s : sequence, forall P Q : A -> Prop,
    (forall x : A, P x -> Q x) ->
      infinitely_many s P -> infinitely_many s Q.
  Proof.
    intros s P Q impl inf_P.
    unfold infinitely_many in inf_P.  
    unfold infinitely_many.
    intro n0.
    specialize inf_P with n0.
    elim inf_P.
    intros m0 P_m0.
    exists m0.
    apply impl.
    assumption.
  Qed.

  Definition strictly_increasing (f : nat -> nat) : Prop :=
    forall n m, lt n m -> lt (f n) (f m).

  Definition is_subsequence (s sub : sequence) : Prop :=
    exists n_ : nat -> nat,
      strictly_increasing n_ /\ forall k, sub k = s (n_ k).

  Lemma infinitely_many_next_index :
          forall (s : sequence) (P : A -> Prop)
                 (inf_P : infinitely_many s P) (n0 : nat),
             { n : nat | ge n n0 /\ P (s n) }.
  Proof.
    intros s P inf_P n0.
    unfold infinitely_many in inf_P.
    specialize inf_P with n0.
    assert ({ n : nat_ge n0 | P (s (proj1_sig n)) }) as inf_P_witness.
      apply constructive_indefinite_description.
      assumption.
    elim inf_P_witness.
    intros ng ng_prop.
    exists (proj1_sig ng).
    split.
    apply (proj2_sig ng).
    assumption.
  Qed.

  Definition infinitely_many_ith_index
          (s : sequence) (P : A -> Prop)
          (inf_P : infinitely_many s P) (i : nat) : { n : nat | P (s n) }.
    induction i.
    (* base case *)
    exists (proj1_sig (infinitely_many_next_index s P inf_P 0)).
    apply (proj2_sig (infinitely_many_next_index s P inf_P 0)).
    (* induction *)
    exists (proj1_sig (infinitely_many_next_index s P inf_P (S (proj1_sig IHi)))).
    apply (proj2_sig (infinitely_many_next_index s P inf_P (S (proj1_sig IHi)))).
  Defined.

  Lemma infinitely_many_ith_index_strictly_increasing_step :
          forall (s : sequence) (P : A -> Prop)
                 (inf_P : infinitely_many s P) (i : nat),
            lt
              (proj1_sig (infinitely_many_ith_index s P inf_P i))
              (proj1_sig (infinitely_many_ith_index s P inf_P (S i))).
  Proof.
    intros s P inf_P i.
    induction i.
    (* base *)
    simpl. 
      apply lt_le_trans with (S (proj1_sig (infinitely_many_next_index s P inf_P 0))).
      apply lt_n_Sn.
      apply (proj2_sig (infinitely_many_next_index s P inf_P
                         (S (proj1_sig (infinitely_many_next_index s P inf_P 0))))).
    (* induction *)
    simpl.
      apply lt_le_trans
       with (S (proj1_sig (infinitely_many_next_index s P inf_P
                 (S (proj1_sig (infinitely_many_ith_index s P inf_P i)))))).
      apply lt_n_Sn.
      apply (proj2_sig (infinitely_many_next_index s P inf_P
                (S (proj1_sig (infinitely_many_next_index s P inf_P
                     (S (proj1_sig (infinitely_many_ith_index s P inf_P i)))))))).
  Qed.

  Lemma infinitely_many_ith_index_increasing_steps :
          forall (s : sequence) (P : A -> Prop)
                 (inf_P : infinitely_many s P) (n k : nat),
                le
                  (proj1_sig (infinitely_many_ith_index s P inf_P n) + k)
                  (proj1_sig (infinitely_many_ith_index s P inf_P (plus n k))).
  Proof.
    intros s P inf_P.
    unfold strictly_increasing.
    intros n k.
    induction k.
    (* base *)
      rewrite plus_0_r.
      rewrite plus_0_r.
      apply le_refl.
    (* induction *)
      rewrite plus_comm.
      rewrite plus_Sn_m.
      rewrite plus_comm.
      assert (plus n (S k) = S (plus n k)) as H.
        rewrite plus_n_Sm.
        reflexivity.
      rewrite H.
      apply lt_le_trans with (S (proj1_sig (infinitely_many_ith_index s P inf_P (n + k)))).
      apply le_lt_n_Sm.
      apply IHk.
      apply lt_le_S.
      apply infinitely_many_ith_index_strictly_increasing_step.
  Qed.

  Lemma nat_dist_diff :
    forall n m : nat, le n m -> m = plus n (minus m n).
  Proof.
    intros.
    rewrite NPeano.Nat.add_sub_assoc.
    rewrite plus_comm.
    rewrite NPeano.Nat.add_sub.
    reflexivity.
    assumption.
  Qed.

  Lemma infinitely_many_ith_index_strictly_increasing :
          forall (s : sequence) (P : A -> Prop)
                 (inf_P : infinitely_many s P),
              strictly_increasing
                (fun i : nat => proj1_sig (infinitely_many_ith_index s P inf_P i)).
  Proof.
    intros s P inf_P.
    unfold strictly_increasing.
    intros n m n_lt_m.
    assert (m = plus n (minus m n)) as H.
      apply nat_dist_diff.
      apply lt_le_weak.
      assumption.
    rewrite -> H.
    apply lt_le_trans
     with (plus
             (proj1_sig (infinitely_many_ith_index s P inf_P n))
             (minus m n)).
    apply NPeano.Nat.lt_add_pos_r.
    SearchAbout plus.
    apply plus_lt_reg_l with n.
    rewrite plus_0_r.
    rewrite NPeano.Nat.add_sub_assoc.
    rewrite plus_comm.
    rewrite NPeano.Nat.add_sub.
    assumption.
    apply lt_le_weak.
    assumption.
    apply infinitely_many_ith_index_increasing_steps.
  Qed.  

  Lemma increasing_function_growth :
          forall f : nat -> nat, strictly_increasing f ->
            forall x, le x (f x).
  Proof.
    intros f f_increasing.
    induction x.
      (* base *)
      apply le_0_n.
      (* induction *)
      apply le_trans with (S (f x)).
      apply le_n_S.
      assumption.
      apply f_increasing.
      apply lt_n_Sn.
  Qed.

  Lemma subsequence_ith_index :
          forall s sub, is_subsequence s sub -> forall i : nat,
                       { n : nat | le i n /\ sub i = s n }.
  Proof.
    intros s sub sub_subsequence i.
    unfold is_subsequence in sub_subsequence.
    assert ({ n_ : nat -> nat |
              strictly_increasing n_ /\
              forall k : nat, sub k = s (n_ k) })
        as sub_subsequence_witness.
      apply constructive_indefinite_description.
      assumption.
    destruct sub_subsequence_witness as (nk_, (nk_increasing, subk_eq_snkk)).
    exists (nk_ i).
    split.
    apply increasing_function_growth.
    assumption.
    apply subk_eq_snkk.
  Qed.

  (*
   * Infinitely many terms of a sequence a_n have a property P
   * if and only if
   * there exists a subsequence of terms, all having the property P
   *)
  Theorem infinitely_many_iff_subsequence :
    forall s P, infinitely_many s P <->
                (exists sub, is_subsequence s sub /\ forall n, P (sub n)).
  Proof.
    intros s P.
    split.
    (* -> *)
    intro inf_P.
    exists (fun i : nat => s (proj1_sig (infinitely_many_ith_index s P inf_P i))).
    unfold is_subsequence.
    split.
      (* is a subsequence *)
      exists (fun i : nat => proj1_sig (infinitely_many_ith_index s P inf_P i)).
      split.
      apply infinitely_many_ith_index_strictly_increasing.
      intro. reflexivity.
      (* every term has the property *)
      intro n.
      apply (proj2_sig (infinitely_many_ith_index s P inf_P n)).
    (* <- *)
    intro exists_sub.
    unfold infinitely_many.
    intro n0.
    elim exists_sub.
    intros sub sub_prop.
    destruct sub_prop as (sub_is_subsequence, sub_has_P).
    unfold nat_ge.
    exists (exist _
              (proj1_sig (subsequence_ith_index s sub sub_is_subsequence n0))
              (proj1 (proj2_sig (subsequence_ith_index s sub sub_is_subsequence n0)))).
    simpl. 
    replace (P (s (proj1_sig (subsequence_ith_index s sub sub_is_subsequence n0))))
       with (P (sub n0)).
    apply sub_has_P.
    apply f_equal.
    apply (proj2_sig (subsequence_ith_index s sub sub_is_subsequence n0)).
  Qed.

  Lemma subsequence_transitive :
          forall s1 s2 s3 : sequence,
            is_subsequence s1 s2 ->
            is_subsequence s2 s3 ->
            is_subsequence s1 s3.
  Proof.
    intros s1 s2 s3 s1_s2 s2_s3.
    unfold is_subsequence.
    unfold is_subsequence in s1_s2. elim s1_s2.
    intros f f_prop. destruct f_prop as (f_increasing, f_eq).
    unfold is_subsequence in s2_s3. elim s2_s3.
    intros g g_prop. destruct g_prop as (g_increasing, g_eq).
    exists (fun x => f (g x)).
    split.
      (* increasing *)
      unfold strictly_increasing.
      intros n m n_lt_m.
      apply f_increasing.
      apply g_increasing.
      assumption.
      (* equality *)
      intro k.
      rewrite g_eq.
      rewrite f_eq.
      reflexivity.
  Qed.

  Lemma all_P_infinitely_many_Q_implies_infinitely_many_PQ :
    forall (s : sequence) (P Q : A -> Prop)
           (sub : sequence) (sub_subsequence : is_subsequence s sub)
           (all_P : forall n : nat, P (sub n))
           (inf_Q : infinitely_many sub Q),
           infinitely_many s (fun x => P x /\ Q x).
  Proof.
    intros s P Q sub sub_subsequence all_P inf_Q.
    (* There is a subsequence "sub2" of "sub" such that both P and Q
     * hold for every term. *)
    assert (exists sub2 : sequence,
              is_subsequence sub sub2 /\ forall n, P (sub2 n) /\ Q (sub2 n))
        as exists_sub2.
    apply (proj1 (infinitely_many_iff_subsequence sub (fun x => P x /\ Q x))).
    unfold infinitely_many in inf_Q.
    unfold infinitely_many.
    intro n0.
    specialize inf_Q with n0.
    elim inf_Q.
    intros n1 Q_holds.
    exists n1.
    split.
      apply all_P.
      apply Q_holds.
    elim exists_sub2.
    intros sub2 prop_sub2.
    destruct prop_sub2 as (sub2_subsequence_sub, sub2_has_PQ). 
    (* By composing "sub" and "sub2" we obtain a subsequence of "s" *)
    assert (exists sub2 : sequence,
              is_subsequence s sub2 /\ forall n, P (sub2 n) /\ Q (sub2 n))
        as exists_sub2_as_a_subsequence_of_s.
    exists sub2.
    split.
      apply (subsequence_transitive s sub sub2).
      assumption.
      assumption.
      assumption.
    (* Hence there are infinitely many terms of "s" having P /\ Q *)
    apply infinitely_many_iff_subsequence.
    assumption.
  Qed.

  (* Stronger version of the "infinitely_many_PEM" lemma:
   * if P holds for infinitely many terms, then either:
   *     P /\ Q  holds for infinitely many terms; or
   *     P /\ ~Q holds for infinitely many terms
   *)
  Theorem infinitely_many_PEM_strong :
    forall (s : sequence) (P : A -> Prop) (Q : A -> Prop),
      infinitely_many s P ->
      { infinitely_many s (fun x => P x /\ Q x) } +
      { infinitely_many s (fun x => P x /\ ~Q x) }.
  Proof.
    intros s P Q inf_P.
    (* By "infinitely_many_iff_subsequence", there is a subsequence "sub" of "s"
     * such that P holds for every term. *)
    assert ({ sub : sequence | is_subsequence s sub /\ forall n, P (sub n) })
        as exists_sub.
      apply constructive_indefinite_description.
      apply infinitely_many_iff_subsequence.
      assumption.
    elim exists_sub.
    intros sub sub_prop.
    destruct sub_prop as (sub_subsequence, sub_has_P).
    (* By "infinitely_many_PEM", either Q holds for infinitely many
     * terms of "sub", or ~Q holds for infinitely many terms of "sub" *)
    assert ({infinitely_many sub Q} + {infinitely_many sub (fun x => ~Q x)})
        as inf_QnQ.
      apply infinitely_many_PEM.
    destruct inf_QnQ as [inf_Q | inf_nQ].
    (* If Q holds for infinitely many terms of sub, there is a subsequence
     * "sub2" of "sub" such that both P and Q hold for every term. *)
    left.
      apply (all_P_infinitely_many_Q_implies_infinitely_many_PQ s P Q sub).
      assumption.
      assumption.
      assumption.
    right.
      apply (all_P_infinitely_many_Q_implies_infinitely_many_PQ s P (fun x => ~ Q x) sub).
      assumption.
      assumption.
      assumption.
  Qed.

  Lemma infinitely_many_proj1 :
          forall (s : sequence) (P Q : A -> Prop),
            infinitely_many s (fun x => P x /\ Q x) ->
            infinitely_many s P.
  Proof.
    intros s P Q inf_PQ.
    apply (infinitely_many_implies s (fun x => P x /\ Q x) P).
    intros x PQ.
    destruct PQ.
    assumption.
    assumption.
  Qed.

  Lemma infinitely_many_proj2 :
          forall (s : sequence) (P Q : A -> Prop),
            infinitely_many s (fun x => P x /\ Q x) ->
            infinitely_many s Q.
  Proof.
    intros s P Q inf_PQ.
    apply (infinitely_many_implies s (fun x => P x /\ Q x) Q).
    intros x PQ.
    destruct PQ.
    assumption.
    assumption.
  Qed.

End Sequences.
  
Lemma infinitely_many_iff_subsequence_variant :
  forall (A : Type) (P : nat -> sequence A -> Prop) (s : sequence A), (
    (forall (n0 : nat), exists n : nat_ge n0, P (proj1_sig n) s)
    <->
    (exists sub : sequence A, is_subsequence A s sub /\ forall k : nat, P k sub) 
 (**
     (exists (n_ : nat -> nat),
       strictly_increasing n_ /\
       forall k : nat, P (n_ k) s)
    **)     

  ).
Proof.
  intros A P s.
  split.
  (* -> *)
  intro infH.
  assert (infinitely_many Prop (fun n => P n s) (fun x => x)) as H.
  assumption.
  assert (exists sub : sequence Prop,
            is_subsequence Prop (fun n => P n s) sub /\
            forall n, sub n) as H2.
    apply (infinitely_many_iff_subsequence Prop (fun n => P n s) (fun x => x)).
    assumption.
  elim H2.
  intros sub sub_prop.
  destruct sub_prop as (sub_subsequence_s, sub_holds).
  unfold is_subsequence in sub_subsequence_s.
  elim sub_subsequence_s.
  intros f_ f_prop. 
  destruct f_prop as (f_increasing, f_holds).
  exists (fun n => s (f_ n)).
  split.
    unfold is_subsequence.
    exists f_.
    split.
        apply f_increasing.
        intro k.
        reflexivity.
    intro k.
    rewrite <- f_holds.
    apply sub_holds.
  (* <- *)



(**** Real sequences ****)

Open Scope R.

Definition Rpositive : Type := { x : R | x > 0 }.

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

Definition lower_bound (s : sequence R) M : Prop :=
  forall n, M <= s n.

Definition upper_bound (s : sequence R) M : Prop :=
  forall n, s n <= M.

Definition least_upper_bound (s : sequence R) lub : Prop :=
  upper_bound s lub /\
  forall lub', upper_bound s lub' -> lub <= lub'.

Definition converges (s : sequence R) limit : Prop :=
                     forall eps : Rpositive,
                       exists n_0 : nat, forall n : nat_ge n_0,
                         dist_lt limit (s (proj1_sig n)) (proj1_sig eps).

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

(*
 * Every bounded increasing sequence
 * converges to its supremum.
 *)
Theorem ubounded_increasing_converges_to_sup :
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

Definition m L U := L + (U - L) / 2.

Lemma range_other_half :
  forall a b x, a <= x <= b ->
                ~(a <= x <= m a b) ->
                (m a b <= x <= b).
Proof.
  intros a b x x_in_ab x_not_in_ac.
  assert (x > a + (b - a) / 2) as cond.
    apply Rnot_le_gt.
    intro.
    assert (a <= x <= a + (b - a) / 2).
      split.
      apply x_in_ab.
      assumption.
    contradiction.
  split.
  apply Rlt_le.
  assumption.
  apply x_in_ab.
Qed.

Lemma infinitely_many_bisection :
    forall s : sequence R, forall L U : R,
      infinitely_many R s (fun a_n => L <= a_n <= U) ->
      { infinitely_many R s (fun a_n => L <= a_n <= m L U) } +
      { infinitely_many R s (fun a_n => m L U <= a_n <= U) }.
Proof.
  intros s L U infH.
  assert ({ infinitely_many R s (fun a_n =>
                                  L <= a_n <= U /\
                                  L <= a_n <= m L U) } +
          { infinitely_many R s (fun a_n =>
                                  L <= a_n <= U /\
                                 ~(L <= a_n <= m L U)) }).
  apply infinitely_many_PEM_strong.
  assumption.
  destruct H as [ inf_lower | inf_upper ].
  left. apply (infinitely_many_proj2 R s _ _ inf_lower).
  right.
    apply infinitely_many_implies
     with (s := s)
          (P := fun x => L <= x <= U /\ ~(L <= x <= m L U))
          (Q := fun x => m L U <= x <= U).
    intros x H.
    apply range_other_half.
    apply H.
    apply H.
    assumption.
Qed.

(** Subsequence **)

Definition subsequence (s : sequence R) : Type :=
  { sub : sequence R | is_subsequence R s sub }.

Definition bounded_sequence :=
  { s : sequence R &
    { L : R & { U : R | lower_bound s L /\ upper_bound s U } } }.

Definition convergent (s : sequence R) : Prop :=
  exists limit : R, converges s limit.



Definition bounded_convergent_subseq_indices
             (seq : bounded_sequence) :
             { n_ : nat -> nat | strictly_increasing n_ }.
Proof.
  unfold bounded_sequence in seq.
  destruct seq as (seq, (L, (U, LU_bounds))).
  assert (forall eps : Rpositive,
            infinitely_many seq
                            (fun a_n => )).

Definition bounded_convergent_subseq :

Theorem bounded_has_convergent_subseq :
        forall seq : bounded_sequence,
          exists subseq : subsequence (projT1 seq),
            convergent (proj1_sig subseq).
Proof.
  intro seq.


(*
acotada     tiene subsuc convergente
convergente tiene subsuc monotona
=>
acotada tiene subsuc monotona
*)

Lemma bounded_ :