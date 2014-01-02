Require Import Arith.
Require Import Recdef.

Definition nat_leb := leb.

Require Import Bool.

Inductive nat_list : Set :=
    nil : nat_list 
  | cons : nat -> nat_list -> nat_list.

Inductive is_sorted : nat_list -> Prop :=
    s_nil       : is_sorted nil
  | s_singleton : forall x, is_sorted (cons x nil)
  | s_cons      : forall x y ys, x <= y -> is_sorted (cons y ys) -> is_sorted (cons x (cons y ys)).

Lemma test_is_sorted : is_sorted (cons 1 (cons 2 nil)).
Proof.
  apply s_cons.
  auto.
  apply s_singleton.
Qed.

Fixpoint less_than_list (x : nat) (xs : nat_list) : bool :=
  match xs with
  | nil       => true
  | cons y ys => andb (nat_leb x y) (less_than_list x ys)
  end.

Fixpoint append (xs : nat_list) (ys : nat_list) : nat_list :=
  match xs with
  | nil       => ys
  | cons z zs => cons z (append zs ys)
  end.

Fixpoint noccs (x : nat) (xs : nat_list) : nat :=
  match xs with
  | nil       => 0
  | cons y ys => noccs x ys + if beq_nat x y then 1 else 0
  end.

Definition perm (xs : nat_list) (ys : nat_list) :=
  forall x, noccs x xs = noccs x ys.

Fixpoint nat_list_min (xs : nat_list) : nat :=
  match xs with
  | nil        => 0 
  | cons y ys  =>
    (match ys with
    | nil      => y
    | cons _ _ => min y (nat_list_min ys)
    end)
  end.

Lemma noccs_gt_0_cons :
  forall x y xs,
    noccs y (cons x xs) > 0 -> (y = x \/ noccs y xs > 0).
Proof.
  unfold noccs; fold noccs.
  intros x y xs H.
  case_eq (beq_nat y x).
    (* true *)
    intro. left.
    apply beq_nat_true; assumption.
    (* false *)
    intro. right.
    replace (beq_nat y x) with false in H.
    replace (noccs y xs + 0) with (noccs y xs) in H.
    assumption.
    apply plus_n_O.
Qed.

Lemma nat_list_min_is_min :
  forall (xs : nat_list) (x : nat),
    noccs x xs > 0 -> nat_list_min xs <= x.
Proof.
  intros xs x noccs_gt_0.
  induction xs.
    (* nil *)
    apply le_Sn_0 in noccs_gt_0.
    contradiction.
    (* cons *)
    unfold nat_list_min; fold nat_list_min.
    apply noccs_gt_0_cons in noccs_gt_0.
    case noccs_gt_0.
      (* x = n *)
      intro.
      replace n with x.
      induction xs.
        apply le_refl.
        apply Min.le_min_l.
      (* noccs x xs > 0 *)
      intro.
      apply le_trans with (nat_list_min xs).
      induction xs.
        apply le_Sn_0 in H; contradiction.
      apply Min.le_min_r.
      apply IHxs.
      assumption.
Qed.

Fixpoint nat_list_remove1 (x : nat) (xs : nat_list) : nat_list :=
  match xs with
  | nil       => nil
  | cons y ys =>
    if beq_nat x y
     then ys
     else cons y (nat_list_remove1 x ys)
  end.

Fixpoint nat_list_len (xs : nat_list) :=
  match xs with
  | nil       => 0
  | cons _ ys => 1 + nat_list_len ys
  end.

Lemma leqmin_imp_eqmin :
  forall n m, n <= min n m -> n = min n m.
Proof.
  intros n m.
  intro.
  symmetry.
  apply min_l.
  apply Min.min_glb_r with n.
  assumption.
Qed.

Lemma remove_different_cons :
  forall x y xs,
  y <> x -> nat_list_remove1 y (cons x xs) = cons x (nat_list_remove1 y xs).
Proof.
  intros.
  simpl.
  replace (beq_nat y x) with false.
  reflexivity.
  symmetry.
  apply beq_nat_false_iff.
  assumption.
Qed.

Lemma list_length_after_removal :
  forall xs, xs <> nil ->
  nat_list_len (nat_list_remove1 (nat_list_min xs) xs)
  < nat_list_len xs.
Proof.
  induction xs.
    (* nil *)
    intro H; elim H; reflexivity.
    (* cons *)
    intro.
    unfold nat_list_min; fold nat_list_min.
    case_eq xs.
      (* nil *)
      simpl.
      rewrite <- beq_nat_refl.
      simpl.
      intro.
      apply lt_0_Sn.
      (* cons *)
      intros y ys shape_xs.
      assert ({n <= nat_list_min (cons y ys)} +
              {n > nat_list_min (cons y ys)})
             as n_options.
      apply le_gt_dec.
      case n_options.
        (* case n is min *)
        intro.
        replace (min n (nat_list_min (cons y ys))) with n.
        simpl.
        rewrite <- beq_nat_refl.
        simpl.
        apply lt_n_S.
        apply lt_n_Sn.
        symmetry.
        apply min_l.
        assumption.
        (* case (nat_list_min (cons n0 xs)) is min *)
        intro.
        replace (min n (nat_list_min (cons y ys))) with (nat_list_min (cons y ys)).
          replace (cons y ys) with xs.
          rewrite remove_different_cons.
            apply lt_n_S.
            fold nat_list_len.
            apply IHxs.
            replace xs with (cons y ys).
            discriminate.
            replace xs with (cons y ys).
            apply NPeano.Nat.lt_neq.
            assumption.
          (* proof that (min n (nat_list_min (cons y ys))) = (nat_list_min (cons y ys)) *)
          symmetry.
          apply min_r.
          apply lt_le_weak in g.
          assumption.
Qed.            

Function selection_sort (xs : nat_list)
    { measure nat_list_len xs } : nat_list :=
  match xs with
  | nil       => nil
  | cons y ys =>
      let m := nat_list_min (cons y ys) in
        cons m (selection_sort (nat_list_remove1 m (cons y ys)))
  end.
  intros.
  apply list_length_after_removal.
  discriminate.
Defined.

Eval compute in (selection_sort (cons 2 (cons 3 (cons 1 nil)))).

Definition is_permutation xs ys := forall x, noccs x xs = noccs x ys.

Lemma eq_neq_dec : forall x y : nat, {x <> y} + {x = y}.
Proof.
  intros x y.
  assert ({x < y} + {x = y} + {x > y}) as xy_options.
  apply lt_eq_lt_dec.
  case xy_options. intro xy_options2; case xy_options2.
  (* x < y *)
  left.
  apply NPeano.Nat.lt_neq.
  assumption.
  (* x = y *)
  right.
  assumption.
  (* x > y *)
  left.
  apply not_eq_sym.
  apply NPeano.Nat.lt_neq.
  assumption.
Qed.

Lemma noccs_remove_present :
  forall x xs,
    noccs x xs > 0 ->
    noccs x xs = noccs x (nat_list_remove1 x xs) + 1.
Proof.
  induction xs.  
  (* nil *)
  intro. compute in H. apply le_Sn_0 in H; contradiction.
  (* cons *)
  intro.
  assert ({x <> n} + {x = n}) as x_options.
  apply eq_neq_dec.
  case x_options.
  (* x <> n *)
    intro.
    unfold nat_list_remove1; fold nat_list_remove1.
    assert (beq_nat x n = false).
      apply beq_nat_false_iff.
      assumption.
    replace (beq_nat x n) with false.
    unfold noccs; fold noccs.
    replace (beq_nat x n) with false.
    rewrite plus_0_r.
    rewrite plus_0_r.
    apply IHxs.
    unfold noccs in H; fold noccs in H.
    replace (beq_nat x n) with false in H.
    rewrite plus_0_r in H.
    assumption.
  (* x = n *)
    intro.
    unfold nat_list_remove1; fold nat_list_remove1.
    assert (beq_nat x n = true).
      apply beq_nat_true_iff.
      assumption.
    replace (beq_nat x n) with true.
    unfold noccs; fold noccs.
    replace (beq_nat x n) with true.
    reflexivity.
Qed.

Lemma plus_compat :
  forall x y z, x = y -> x + z = y + z.
Proof.
  induction z.
  (* base *)
  intro.
  rewrite plus_0_r.
  rewrite plus_0_r.
  assumption.
  (* ind *)
  intro.
  rewrite <- plus_n_Sm.
  rewrite <- plus_n_Sm.
  apply eq_S.
  apply IHz.
  assumption.
Qed.

Lemma noccs_remove_not_present :
  forall x y xs,
    x <> y ->
    noccs y xs > 0 ->
    noccs x xs = noccs x (nat_list_remove1 y xs).
Proof.
  intros x y xs H0 H1.
  induction xs.
  (* nil *)
  compute in H1. apply le_Sn_0 in H1; contradiction.
  (* cons *)
  unfold nat_list_remove1; fold nat_list_remove1.
  assert ({y <> n} + {y = n}) as y_options.
  apply eq_neq_dec.
  case y_options.
  (* y <> n *)
  intro.
  assert (beq_nat y n = false).
    apply beq_nat_false_iff.
    assumption.
  replace (beq_nat y n) with false.
  unfold noccs; fold noccs.
  apply plus_compat.
  apply IHxs.
  unfold noccs in H1; fold noccs in H1.
  replace (beq_nat y n) with false in H1.
  rewrite plus_0_r in H1.
  assumption.
  (* y = n *)
  intro.
  assert (beq_nat y n = true).
    apply beq_nat_true_iff.
    assumption.
  replace (beq_nat y n) with true.
  unfold noccs; fold noccs.
  assert (beq_nat x n = false).
    apply beq_nat_false_iff.
    replace n with y.
    assumption.
  replace (beq_nat x n) with false.
  rewrite plus_0_r.
  reflexivity.
Qed.

Lemma min_neq_l : forall x y, min x y <> x -> y <= x.
Proof.
  intros x y.
  intro.
  assert ({min x y = x} + {min x y = y}) as min_options.
    apply Min.min_case.
    left. reflexivity.
    right. reflexivity.
  case min_options. 
  (* min x y = x *)
    intro. elim H; assumption.  
  (* min x y = y *)
    intro.
    apply Min.min_glb_l with y.
    replace (min x y) with y.
    apply le_refl.
Qed.

Lemma min_of_cons :
  forall x xs,
  nat_list_min (cons x xs) <> x -> 
  nat_list_min (cons x xs) = nat_list_min xs.
Proof.
  intro.
  unfold nat_list_min; fold nat_list_min.
  intro xs.
  case xs.
  (* nil *)
  intro H; elim H; reflexivity.
  (* cons *)
  intros y ys.
  intro.
  apply min_r.
  apply min_neq_l.
  assumption.
Qed.
  
Lemma min_in_list :
  forall xs,
    xs <> nil -> noccs (nat_list_min xs) xs > 0.
Proof.
  induction xs.
  (* nil *)
  intro H. elim H. reflexivity.
  (* cons *)
  case_eq xs.
    (* nil *)
    intros.
    unfold nat_list_min; fold nat_list_min.
    simpl.
    assert (beq_nat n n = true).
      apply beq_nat_true_iff.
      reflexivity.
    replace (beq_nat n n) with true.
    apply lt_0_Sn.
    (* cons *)
    intros y ys.
    intros.
    assert ({n <> nat_list_min (cons n (cons y ys))} +
            {n = nat_list_min (cons n (cons y ys))})
        as n_options.
      apply eq_neq_dec.
    case n_options.
    (* n <> nat_list_min ... *)
    intro.
    replace (cons y ys) with xs.
    unfold noccs; fold noccs.
    assert (beq_nat (nat_list_min (cons n xs)) n = false).
      apply beq_nat_false_iff.
      apply not_eq_sym.
      replace xs with (cons y ys).
      assumption.
    replace (beq_nat (nat_list_min (cons n xs)) n) with false.
    rewrite plus_0_r.
    replace xs with (cons y ys).
    replace xs with (cons y ys) in IHxs.
    rewrite min_of_cons.
      apply IHxs.
      discriminate.
      apply not_eq_sym.
      assumption.
    (* n = nat_list_min ... *)
      intro n_shape.
      rewrite <- n_shape.
      unfold noccs; fold noccs.
      assert (beq_nat n n = true).
        apply beq_nat_true_iff.
        reflexivity.
      replace (beq_nat n n) with true.
        rewrite plus_comm.
        simpl.
        apply lt_0_Sn.
 Qed.

Lemma remove_min_perm :
  forall xs,
    xs <> nil ->
    is_permutation xs (cons (nat_list_min xs) (nat_list_remove1 (nat_list_min xs) xs)).
Proof.
  intro xs.
  case_eq xs.
  (* nil *)
  intro xs_shape. intro H; elim H; reflexivity.
  (* cons *)
  intros y ys xs_shape.
  intro.
  replace (cons y ys) with xs.
  unfold is_permutation.
  intro x.
  assert ({x <> nat_list_min xs} +
          {x = nat_list_min xs})
      as x_options.
    apply eq_neq_dec.
  case x_options.
  (* x <> nat_list_min xs *)
    intro.
    unfold noccs; fold noccs.
    assert (beq_nat x (nat_list_min xs) = false).
      apply beq_nat_false_iff.
      assumption.
    replace (beq_nat x (nat_list_min xs)) with false.
    rewrite plus_0_r.
    apply noccs_remove_not_present.
    assumption.
    apply min_in_list.
    rewrite xs_shape.
    discriminate.
  (* x = nat_list_min xs *)
    intro.
    unfold noccs; fold noccs.
    assert (beq_nat x (nat_list_min xs) = true).
      apply beq_nat_true_iff.
      assumption.
    replace (beq_nat x (nat_list_min xs)) with true.
    replace x with (nat_list_min xs).
    apply noccs_remove_present.
    apply min_in_list.
    rewrite xs_shape.
    discriminate.
Qed.      

Lemma cons_is_not_perm_nil :
  forall x xs,
  ~is_permutation (cons x xs) nil.
Proof.
  intros x xs.
  unfold is_permutation.
  intro H.
  specialize H with x.
  unfold noccs in H; fold noccs in H.
  assert (beq_nat x x = true).
    apply beq_nat_true_iff.
    reflexivity.
  replace (beq_nat x x) with true in H.
  rewrite plus_comm in H.
  simpl in H. 
  apply eq_sym in H.
  apply O_S in H.
  contradiction.
Qed.

Lemma permutation_cons :
  forall x xs ys,
  is_permutation xs ys ->
  is_permutation (cons x xs) (cons x ys).
Proof.
  intros x xs ys.
  unfold is_permutation.
  intro H.
  intro y.
  unfold noccs; fold noccs.
  apply plus_compat.
  specialize H with y.
  assumption.
Qed.

Lemma permutation_equiv :
  forall x xs ys zs,
  is_permutation xs ys ->
  is_permutation (cons x xs) zs ->
  is_permutation (cons x ys) zs.
Proof. 
  intros x xs ys zs perm_xs_ys perm_xxs_zs.
  unfold is_permutation.
  intro y.
  assert (is_permutation (cons x xs) (cons x ys)) as perm_xxs_xys.
    apply permutation_cons.
    assumption.
  unfold is_permutation in perm_xxs_xys.
  specialize perm_xxs_xys with y.
  transitivity (noccs y (cons x xs)).
  symmetry.
  assumption.
  unfold is_permutation in perm_xxs_zs.
  specialize perm_xxs_zs with y.
  assumption.
Qed. 

Lemma permutation_symm :
  forall xs ys,
    is_permutation xs ys -> is_permutation ys xs.
Proof.
  intros xs ys H.
  unfold is_permutation.
  intro x.
  unfold is_permutation in H.
  specialize H with x.
  symmetry.
  assumption.
Qed.

Lemma selection_sort_is_permutation :
  forall xs, is_permutation (selection_sort xs) xs.
Proof.
  intro.
  functional induction selection_sort xs.
  (* nil *)
  compute.
  reflexivity.
  (* cons *)
  apply permutation_equiv
   with (xs := (nat_list_remove1 (nat_list_min (cons y ys)) (cons y ys))).
  apply permutation_symm.
  apply IHn.
  apply permutation_symm.
  apply remove_min_perm.
  discriminate.
Qed.  

Lemma selection_sort_cons :
  forall xs,
    ~(xs = nil) ->
    selection_sort xs =
    cons (nat_list_min xs)
         (selection_sort (nat_list_remove1 (nat_list_min xs) xs)).
 Proof.
   intro xs.
   functional induction selection_sort xs.
   (* nil *)
   intro H; elim H; reflexivity.
   (* cons *)
   intro xs_shape.
   reflexivity.
Qed.
 
Lemma nat_list_remove_not_nil :
  forall x y xs,
    xs <> nil ->
    nat_list_remove1 y (cons x xs) <> nil.
 Proof.
   intros x y xs xs_not_nil.
   unfold nat_list_remove1.
   assert ({x <> y} + {x = y}) as xy_options.
     apply eq_neq_dec.
   case xy_options. 
   (* x <> y *)
     intro.
     assert (beq_nat y x = false).
       apply beq_nat_false_iff.
       apply not_eq_sym.
       assumption.
     replace (beq_nat y x) with false.
     discriminate.
   (* x = y *)
     intro.
     assert (beq_nat y x = true).
       apply beq_nat_true_iff.
       symmetry.
       assumption.
     replace (beq_nat y x) with true.
     assumption.
Qed.
 
Lemma noccs_in_remove :
  forall x y xs,
    noccs y (nat_list_remove1 x xs) > 0 ->
    noccs y xs > 0.
Proof.
  intros x y xs.
  induction xs.
  (* nil *)
  intro H.
  simpl in H.
  apply lt_irrefl in H.
  contradiction.
  (* cons *)
  intro H. 
  assert ({x <> n} + {x = n}) as x_options.
    apply eq_neq_dec.
  case x_options.
  (* x <> n *)
    intro.
    unfold nat_list_remove1 in H; fold nat_list_remove1 in H.
    assert (beq_nat x n = false).
      apply beq_nat_false_iff.
      assumption.
     replace (beq_nat x n) with false in H.
     unfold noccs; fold noccs.
     unfold noccs in H; fold noccs in H.
     (* case y *)
     assert ({y <> n} + {y = n}) as y_options.
       apply eq_neq_dec.
       case y_options.
       (* y <> n *)
       intro.
       assert (beq_nat y n = false). apply beq_nat_false_iff. assumption.
       replace (beq_nat y n) with false in H.
       replace (beq_nat y n) with false.
       rewrite plus_0_r in H.
       rewrite plus_0_r.
       apply IHxs.
       assumption.
       (* y = n *)
       intro.
       assert (beq_nat y n = true). apply beq_nat_true_iff. assumption.
       replace (beq_nat y n) with true.
       rewrite plus_comm.
       simpl.
       apply lt_0_Sn.
  (* x = n *)
    intro.
    unfold nat_list_remove1 in H; fold nat_list_remove1 in H.
    assert (beq_nat x n = true). apply beq_nat_true_iff. assumption.
    replace (beq_nat x n) with true in H.
    unfold noccs; fold noccs.
    apply lt_plus_trans.
    assumption.
Qed.

Lemma selection_sort_sorts :
  forall xs, is_sorted (selection_sort xs).
Proof.
  intro.
  functional induction selection_sort xs.
  (* nil *)
  apply s_nil.
  (* cons *)
  case_eq ys.
  (* cons / nil *)
    intro ys_shape.
    unfold nat_list_min.
    unfold nat_list_remove1.
    assert (beq_nat y y = true).
      apply beq_nat_true_iff.
      reflexivity.
    replace (beq_nat y y) with true.
    apply s_singleton.
  (* cons / cons *)
    intros z zs ys_shape.
    replace (cons z zs) with ys.
    rewrite selection_sort_cons.
    apply s_cons.
      (* [1] first element is lesser than the second *)
      assert (noccs
                (nat_list_min (nat_list_remove1 (nat_list_min (cons y ys)) (cons y ys)))
                (nat_list_remove1 (nat_list_min (cons y ys)) (cons y ys))
                > 0) as noccs_min2_in_list1.
        apply min_in_list.
        apply nat_list_remove_not_nil.
        rewrite ys_shape.               
        discriminate.
      apply nat_list_min_is_min.
      apply noccs_in_remove with (x := (nat_list_min (cons y ys))).
      assumption.
      (* [2] remainder of the list is sorted *)
      rewrite selection_sort_cons in IHn.
      assumption.
      (* trivial conditions of non-emptiness *)
      apply nat_list_remove_not_nil.
      rewrite ys_shape; discriminate.
      apply nat_list_remove_not_nil.
      rewrite ys_shape; discriminate.
Qed.