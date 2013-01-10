Require Import ListSet.
Require Import Arith.
Require Import List.

(* Auxiliary nat lemmas *)

Lemma nat_eq_implies_le : forall x y : nat, x = y -> x <= y.
Proof.
    intros x y.
    intro Heq.
    replace y with x.
    apply le_n.
Qed.

Lemma nat_gt_implies_not_le : forall x y : nat, x > y -> not (x <= y).
Proof.
  compute.
  intros x y H1 H2.
  assert (S y <= y) as Hc.
    apply (le_trans (S y) x y).
    assumption. assumption.
  apply le_Sn_n in Hc.
  contradiction.
Qed.

(* Auxiliary list lemmas *)
Lemma list_eq_iff_head_tail_eq :
        forall A : Type,
          forall x y : A, forall xs ys : List.list A,
            x = y -> xs = ys -> List.cons x xs = List.cons y ys.
Proof.
  intros A x y xs ys Hxy Hxys.
  replace y with x.
  replace ys with xs.
  reflexivity.
Qed.

Lemma list_not_in_list_implies_not_in_tail :
        forall A : Type,
          forall y x : A, forall xs : List.list A,
            not (List.In y (List.cons x xs)) ->
            not (List.In y xs).
Proof.
  intros A y x xs y_not_in_list y_in_tail.
  assert (List.In y (List.cons x xs)).
      apply List.in_cons.
      assumption.
  contradiction.
Qed.

(* Identifiers *)
Definition id := nat.
Definition id_eq_dec := eq_nat_dec.

(* Sets of identifiers *)
Definition ids : Type := set id.
Definition ids_empty : ids := empty_set id.
Definition ids_add : id -> ids -> ids := set_add id_eq_dec.
Definition ids_union : ids -> ids -> ids := set_union id_eq_dec.
Definition ids_diff : ids -> ids -> ids := set_diff id_eq_dec.
Definition ids_inter : ids -> ids -> ids := set_inter id_eq_dec.
Definition ids_In (x : id) (a : ids) : Prop := set_In x a.
Definition ids_mem : id -> ids -> bool := set_mem id_eq_dec.
Fixpoint ids_union_map (f : id -> ids) (a : ids) : ids :=
    match a with
    | List.nil       => ids_empty
    | List.cons x xs => ids_union (f x) (ids_union_map f xs)
    end.
Definition ids_is_empty (a : ids) : Prop := forall x : id, not (ids_In x a).
Definition ids_disjoint (a b : ids) : Prop := ids_is_empty (ids_inter a b).
(* Another characterization of set disjointness *)
Definition ids_disjoint2 (a b : ids) : Prop :=
  forall x : id, ids_In x a -> not (ids_In x b).
Definition ids_includes (a b : ids) : Prop :=
  forall x : id, ids_In x b -> ids_In x a.

Lemma ids_disjoint_implies_ids_disjoint2 :
    forall A B : ids,
      ids_disjoint A B -> ids_disjoint2 A B.
Proof.
  intros A B hyp.
  unfold ids_disjoint2.
  intros x H H2.
  unfold ids_disjoint, ids_is_empty in hyp.
  specialize hyp with x.
  unfold ids_In in hyp.
  assert (set_In x (ids_inter A B)).
      apply (set_inter_intro id_eq_dec).
      assumption. assumption.
  contradiction.
Qed.

Lemma ids_disjoint2_implies_ids_disjoint :
    forall A B : ids,
      ids_disjoint2 A B -> ids_disjoint A B.
Proof.
  intros A B hyp.
  unfold ids_disjoint, ids_inter, ids_is_empty.
  intros x H.
  unfold ids_disjoint2 in hyp.
  specialize hyp with x.
  unfold ids_In in H.
  assert (set_In x A /\ set_In x B) as H_conj.
      apply (set_inter_elim id_eq_dec).
      assumption.
  decompose [and] H_conj.
  assert (~(set_In x B)).
      apply hyp. assumption.
  contradiction.
Qed.

Lemma ids_includes_transitivity :
    forall A B C : ids,
      ids_includes A B ->
      ids_includes B C ->
      ids_includes A C.
Proof.
  intros A B C AB BC.
  unfold ids_includes.
  intros x xC.
  unfold ids_includes in AB, BC.
  specialize AB with x.
  specialize BC with x.
  apply AB. apply BC. assumption.
Qed.

Lemma ids_union_intro1 :
  forall A B : ids,
  forall x : id,
    ids_In x A -> ids_In x (ids_union A B).
Proof.
  intros A B x x_in_A.
  unfold ids_In in x_in_A.
  unfold ids_In, ids_union.
  apply set_union_intro1.
  assumption.
Qed.

Lemma ids_union_intro2 :
  forall A B : ids,
  forall x : id,
    ids_In x B -> ids_In x (ids_union A B).
Proof.
  intros A B x x_in_B.
  unfold ids_In in x_in_B.
  unfold ids_In, ids_union.
  apply set_union_intro2.
  assumption.
Qed.

Lemma ids_includes_union1 :
  forall A B : ids,
    ids_includes (ids_union A B) A.
Proof.
  intros A B.
  unfold ids_includes.
  intros x xA.
  apply set_union_intro1.
  assumption.
Qed.

Lemma ids_includes_union2 :
  forall A B : ids,
    ids_includes (ids_union A B) B.
Proof.
  intros A B.
  unfold ids_includes.
  intros x xB.
  apply set_union_intro2.
  assumption.
Qed.

(* Cardinality of a set *)
Definition ids_card (a : ids) : nat := List.length a.

(*
 * Returns the set of the first "n" identifiers in the
 * variable universe.
 *)
Fixpoint ids_up_to (n : nat) : ids :=
  match n with
  | O     => ids_empty
  | (S m) => ids_add (S m) (ids_up_to m)
  end.

(*
 * Returns "n" elements of the given set.
 *)
Fixpoint ids_take (n : nat) (a : ids) : ids :=
  match n with
  | O   => ids_empty
  | S m => match a with
           | List.nil       => ids_empty
           | List.cons x xs => ids_add x (ids_take m xs)
           end
  end.

(*
 * Returns a set of "n" ids not in the forbidden set.
 *)
Fixpoint fresh_ids (n : nat) (forbidden : ids) :=
  ids_take n (ids_diff (ids_up_to (ids_card forbidden + n)) forbidden).

Lemma ids_up_to_bounded :
  forall n : nat, forall x : id, ids_In x (ids_up_to n) -> x <= n.
Proof.
  intros n x.
  induction n.
    (* Base case *)
    compute.
    intro. contradiction.
    (* Induction *)
    unfold ids_up_to. fold ids_up_to.
    unfold ids_In, ids_add.
    intro hyp.
    apply set_add_elim in hyp.
    decompose [or] hyp.
        (* x is the given id *)
        apply nat_eq_implies_le. assumption.
        (* x is the recursive result *)
        unfold ids_In in IHn.
        apply lt_le_weak.
        apply le_lt_n_Sm.
        apply IHn. assumption.
Qed.

Lemma Sn_not_in_ids_up_to_n : forall n : nat,
                                not (ids_In (S n) (ids_up_to n)).
Proof.
    intros n hyp.
    assert (S n <= n).
        apply ids_up_to_bounded.
        assumption.
    assert (not (S n <= n)).
        apply le_Sn_n.
    contradiction.
Qed.

Lemma ids_add_not_in_set :
      forall x : id, forall A : ids,
        not (ids_In x A) ->
        ids_add x A = List.app A (List.cons x List.nil).
Proof.
  intros x A x_not_in_aA.
  induction A.
    (* Base case *)
    compute. trivial.
    (* Induction *)
    unfold ids_add.
    unfold set_add.
    case (id_eq_dec x a).
        (* x = a *)
        intro.
        assert (ids_In x (List.cons a A)).
            unfold ids_In, set_In, List.In.
            left. symmetry. assumption.
        contradiction.
        (* x <> a *)
        intro x_neq_a.
        transitivity (List.cons a (List.app A (List.cons x List.nil))).
        apply list_eq_iff_head_tail_eq.
            reflexivity.
            apply IHA.
            apply (list_not_in_list_implies_not_in_tail id x a A).
            assumption.
        apply List.app_comm_cons.
Qed.     

Lemma ids_card_not_in_set :
        forall x : id, forall a : ids,
          not (ids_In x a) ->
          ids_card (ids_add x a) = S (ids_card a).
Proof.
  intros x a x_in_a.
  replace (ids_add x a) with (List.app a (List.cons x List.nil)).
    unfold ids_card.
    transitivity (length a + length (List.cons x List.nil)).
        apply List.app_length.
        simpl length.
        apply plus_comm.        
    symmetry.
    apply ids_add_not_in_set.
    assumption.
Qed.

Lemma ids_up_to_card :
  forall n : nat, ids_card (ids_up_to n) = n.
Proof.
  intros n.
  unfold ids_up_to.
  induction n.
    (* Base case *)
    compute. trivial.
    (* Induction *)
    fold ids_up_to in IHn.
    fold ids_up_to.
    replace (ids_card (ids_add (S n) (ids_up_to n)))
        with (S (ids_card (ids_up_to n))).
        apply eq_S.
        apply IHn.
        symmetry.
        apply ids_card_not_in_set.
        apply Sn_not_in_ids_up_to_n.
Qed.

Lemma ids_diff_card :
  forall a b : ids, ids_card (ids_diff a b) >= ids_card a - ids_card b.
Proof.
  intros a b.
  induction a.
    compute. trivial.
    unfold ids_diff.
    

Lemma fresh_ids_card :
        forall n : nat, forall forbidden : ids,
          ids_card (fresh_ids n forbidden) = n.
Proof.
  intros n forbidden.
  
