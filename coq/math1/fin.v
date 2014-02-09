Require Import ZArith.
Require Import NPeano.

Load "Bijection".

Definition nat_lt N := e_lift {n : nat | n < N}.

Definition finite (A : eqset) : Type :=
  { n : nat | eq_cardinal A (nat_lt n) }.

Lemma finite_nat_lt : forall N, finite (nat_lt N).
Proof.
  intro N.
  unfold finite.
  exists N.
  apply eq_cardinal_reflexive.
Qed.

Definition finite_cardinal A (A_finite : finite A) : nat.
  elim A_finite.
  intro n.
  intros.
  apply n.
Defined.

Lemma _nat_lt_ge_dec : forall n m : nat, {n < m} + {n >= m}.
Proof.
  intros n m.
  assert ({n < m} + {n = m} + {n > m}) as nm_opts.
  apply lt_eq_lt_dec.
  destruct nm_opts as [[n_lt_m | n_eq_m] | n_gt_m].
  left; assumption.
  right; apply Nat.eq_le_incl; symmetry; assumption.
  right; apply lt_le_weak; assumption.
Qed.

Lemma eq_in_lift : forall A (x y : e_set (e_lift A)), x == y -> x = y. 
Proof.
  intros A x y H.
  compute in H.
  assumption.
Qed.

(*
 * 0 1 2 ... x-1 x x+1     N-1
 *
 * 0 1 2 ... x-1 x x+1 ... N-1 N
 * 0 1 2 ... x-1   x+1 ... N-1 N
 *)
Definition bijection_n_Sn_removal_function N (x : e_set (nat_lt (S N))) :
               e_set (nat_lt N) -> e_set (eqset_remove (nat_lt (S N)) x).
  intro y.
  assert ({proj1_sig y < proj1_sig x} + {proj1_sig y >= proj1_sig x})
      as xy_opts.
    apply _nat_lt_ge_dec.
  destruct xy_opts as [y_lt_x | y_ge_x].
  (* y < x *)
  assert (proj1_sig y < S N) as hyp_LT.
    apply lt_trans with (proj1_sig x).
    assumption.
    apply (proj2_sig x).
  exists (exist (fun z => z < S N) (proj1_sig y) hyp_LT).
  simpl.
  compute.
  intro x_eq_fy.
  assert (proj1_sig x = proj1_sig (exist (fun z : nat => z < S N) (proj1_sig y) hyp_LT))
      as H. apply f_equal. assumption.
  simpl in H.
  assert (proj1_sig x <> proj1_sig y).
    apply not_eq_sym.
    apply Nat.lt_neq.
    assumption.
  contradiction.
  (* y >= x *)
  assert (proj1_sig y + 1 < S N) as hyp_LT.
    rewrite plus_comm.
    simpl.
    apply lt_n_S.
    apply (proj2_sig y).
  exists (exist (fun z => z < S N) (proj1_sig y + 1) hyp_LT).
  simpl.
  compute.
  intro x_eq_fy.
  assert (proj1_sig x = proj1_sig (exist (fun z : nat => z < S N) (proj1_sig y + 1) hyp_LT))
      as H. apply f_equal. assumption.
  simpl in H.
  assert (proj1_sig x <> proj1_sig y + 1).
    apply le_gt_S in y_ge_x.
    rewrite plus_comm.
    simpl.
    apply Nat.lt_neq.
    assumption.
  contradiction.
Defined.

Definition bijection_n_Sn_removal_functional N (x : e_set (nat_lt (S N))) :
               e_set (nat_lt N ==> eqset_remove (nat_lt (S N)) x).
  simpl.
  unfold e_function_set.
  exists (bijection_n_Sn_removal_function N x).
  intros y1 y2 y1_eq_y2.
  compute in y1_eq_y2.
  replace y2 with y1.
  apply e_reflexive.
Defined.

Lemma bijection_n_Sn_removal :
  forall N (x : e_set (nat_lt (S N))),
    eq_cardinal (nat_lt N) (eqset_remove (nat_lt (S N)) x).
Proof.                                       
  intros N x.
  unfold eq_cardinal.
  exists (bijection_n_Sn_removal_functional N x).
  apply inhabits.
  unfold bijection.
  intro fy.
  assert ({proj1_sig (proj1_sig fy) < proj1_sig x} +
          {proj1_sig (proj1_sig fy) = proj1_sig x} +
          {proj1_sig (proj1_sig fy) > proj1_sig x})
      as fy_opts.
    apply lt_eq_lt_dec.
  case fy_opts as [[fy_lt_x | fy_eq_x ] | fy_gt_x].
    (* fy < x *)
    admit.
    (* fy = x *)
    assert (~(x == proj1_sig fy)) as H.
      apply (proj2_sig fy).
      (** TODO **)
    (* fy > x *)
    admit.
Qed.

  

Lemma eq_cardinal_imp_eq_nat :
        forall N M, eq_cardinal (nat_lt N) (nat_lt M) -> N = M.
Proof.
  intro N.
  induction N.
  
  (* 0 *)
  intros M eq_card_N_M.
  unfold eq_cardinal in eq_card_N_M.
  elim eq_card_N_M.
  intros f inh_f_bij; case inh_f_bij; intro f_bij.
  assert ({0 = M} + {0 <> M}) as M_cases.
    apply eq_nat_dec.
  case M_cases.
  tauto.
  intro neq_0_M.
  assert (M > 0) as gt_0_M.
  apply neq_0_lt.
  assumption.
  unfold bijection in f_bij.
  elim f_bij with (exist (fun n => n < M) 0 gt_0_M).
  intro impossible_element.
  simpl in impossible_element.
  assert (proj1_sig impossible_element < 0).
  apply (proj2_sig impossible_element).
  assert (~proj1_sig impossible_element < 0).
  apply lt_n_0.
  contradiction.
  
  (* S N *)
  intros M eq_card_N_M.
  unfold eq_cardinal in eq_card_N_M.
  elim eq_card_N_M.
  intros f inh_f_bij; case inh_f_bij; intro f_bij.

  
Qed.

Lemma finite_cardinal_well_defined :
  forall A (A_fin1 A_fin2 : finite A),
    finite_cardinal A A_fin1 = finite_cardinal A A_fin2.
Proof.
  intros A A_fin1 A_fin2.
  unfold finite in A_fin1.
  elim A_fin1; intros n bijection_A_n.
  elim A_fin2; intros m bijection_A_m.
  induction n.
    (* 0 *)
    simpl.
    

     
    (* S n *)


(*** TODO :

     Demostrar que si tengo dos demostraciones de que un conjunto
     es finito, la primera componente (su cardinal), siempre coincide.
     Por induccion.

 ***)

(**** Groups ****)

Structure group :=
  mk_group {
      g_eqset : eqset ;
      g_unit : e_set g_eqset ;
      g_op : e_set g_eqset -> e_set g_eqset -> e_set g_eqset ;
      g_inv : e_set g_eqset -> e_set g_eqset ;
      g_unit_l : forall x, g_op g_unit x == x ;
      g_unit_r : forall x, g_op x g_unit == x ;
      g_assoc : forall x y z, g_op x (g_op y z) == g_op (g_op x y) z ;
      g_inv_r : forall x, g_op x (g_inv x) == g_unit
  }.

Notation "[ G ]" := (e_set (g_eqset G)).
Notation "a ** b" := (g_op _ a b) (at level 35).
Notation "a !" := (g_inv _ a) (at level 25).

Definition g_finite (G : group) := finite (e_set (g_eqset G)).

Definition g_order G (G_finite : g_finite G) : nat.
  unfold g_finite in G_finite.
  unfold finite in G_finite.
  elim G_finite.
  intros n _.
  apply n.
Defined.


Definition subgroup (H G : group) : Prop :=
  e_subset (g_eqset H) (g_eqset G).

(****)

Inductive Z2_set := Z2_0 | Z2_1.

Definition Z2_op (a b : Z2_set) :=
  match a with
  | Z2_0 => b
  | Z2_1 => (match b with
             | Z2_0 => Z2_1
             | Z2_1 => Z2_0
             end)
  end.

Definition Z2_inv (a : Z2_set) := a.

Lemma Z2_unit_l : forall x, Z2_op Z2_0 x = x.
Proof.
  intro x.
  case x.
  compute; reflexivity.
  compute; reflexivity.
Qed.

Lemma Z2_unit_r : forall x, Z2_op x Z2_0 = x.
Proof.
  intro x.
  case x.
  compute; reflexivity.
  compute; reflexivity.
Qed.

Lemma Z2_assoc : forall x y z, Z2_op x (Z2_op y z) = Z2_op (Z2_op x y) z.
Proof.
  intros x y z.
  case x.
  case y.
  compute; reflexivity.
  compute; reflexivity.
  case y.
  compute; reflexivity.
  case z.
  compute; reflexivity.
  compute; reflexivity.
Qed.

Lemma Z2_inv_r : forall x, Z2_op x (Z2_inv x) = Z2_0.
Proof.
  intro x.  
  case x.
  compute; reflexivity.
  compute; reflexivity.
Qed.

Definition Z2 : group := mk_group 
      Z2_set
      Z2_0
      Z2_op
      Z2_inv
      Z2_unit_l
      Z2_unit_r
      Z2_assoc
      Z2_inv_r.

Lemma nat_lt_2_cases : forall x : nat_lt 2, {proj1_sig x = 0} + {proj1_sig x = 1}.
Proof.
  intro x.
  assert (proj1_sig x <= 1) as x_shape.
    unfold nat_lt in x.
    elim x.
    intros x_value x_prop.
    simpl.
    apply lt_n_Sm_le.
    assumption.
  SearchAbout lt.
  rewrite <- NPeano.Nat.lt_1_r.
  replace (proj1_sig x = 0) with (proj1_sig x < 1).
  apply le_lt_eq_dec.
  assumption.
Qed.

Definition Z2_enum (x : nat_lt 2) : Z2_set.
  assert (proj1_sig x = 0 \/ proj1_sig x = 1) as x_cases.
  apply nat_lt_2_cases.
  case x_cases.


Lemma Z2_set_finite : finite Z2_set.
Proof.
  unfold finite.
  exists 2.
  exists (fun x => nat_lt_2 x).
