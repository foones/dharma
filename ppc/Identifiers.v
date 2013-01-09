Require Import ListSet.
Require Import Arith.

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
Definition ids_union_map (f : id -> ids) (a : ids) : ids :=
    set_fold_right ids_union (set_map f a) ids_empty.
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
 * universe
 *)
Fixpoint ids_up_to (n : nat) : ids :=
  match n with
  | O     => ids_empty
  | (S m) => ids_add (S m) (ids_up_to m)
  end.

(*
Fixpoint ids_least (

Fixpoint ids_take (n : nat) (a : ids) : ids :=
  match n with
  | O => empty_set
  | 
*)

(*
 * Returns a set of "n" ids not in the forbidden set.
 *)
(*
Fixpoint fresh_ids (n : nat) (forbidden : ids) :=
  ids_take n (ids_diff (ids_up_to (ids_card forbidden + n)) forbidden).

Lemma 
*)