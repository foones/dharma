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

(* Terms *)
Inductive term : Type :=
  | ConT : term
  | VarT : id -> term
  | LamT : term -> ids -> term -> term
  | AppT : term -> term -> term.

Fixpoint free_vars (t : term) : ids :=
  match t with
  | ConT        => ids_empty
  | VarT x      => ids_add x ids_empty
  | LamT p th a => ids_diff (ids_union (free_vars p) (free_vars a)) th
  | AppT a b    => ids_union (free_vars a) (free_vars b)
  end.

Fixpoint bound_vars (t : term) : ids :=
  match t with
  | ConT        => ids_empty
  | VarT x      => ids_empty
  | LamT p th a => ids_union (ids_union (bound_vars p) (bound_vars a)) th
  | AppT a b    => ids_union (bound_vars a) (bound_vars b)
  end.

(* Substitutions *)
Inductive subst : Type :=
  | Subst (domain : ids) (mapping : id -> term) : subst
  | None  : subst.

Definition subst_domain (s : subst) : ids :=
  match s with
  | Subst dom _ => dom
  | None        => ids_empty
  end.

Fixpoint subst_free_vars (s : subst) : ids :=
  match s with
  | Subst dom f => ids_union_map (fun x : id => free_vars (f x)) dom
  | None        => ids_empty
  end.

Definition subst_variables (s : subst) : ids :=
  ids_union (subst_domain s) (subst_free_vars s).

Definition subst_apply_to_id (s : subst) (x : id) : term :=
  match s with
  | Subst _ f => f x
  | None      => VarT x
  end.

(*
 * To model application of a substitution to a term, we follow
 * these steps:
 *
 * - First, define the *safe* application of a substitution to
 *   a term. An application is safe if it can assume that variables
 *   are renamed apart. (It shall receive a proof of the fact that
 *   variables are renamed apart).
 *
 * - Define alpha-equivalence and renaming in terms of the
 *   safe substitution.
 *
 * - Define the general application of a substitution to a term,
 *   which composes the safe application with a previous step of
 *   renaming bound variables in the term, for them to be renamed
 *   apart.
 *
 *)

(*
 * A substitution and a term are *apart* if the bound
 * variables of the term do not occur in the substitution
 * (either in the domain, or as free variables in the
 * codomain).
 *
 *)
Definition apart (s : subst) (t : term) :=
  ids_disjoint (subst_variables s) (bound_vars t).

(*
 * Given a substitution "s" apart from a given term,
 * "s" is also apart from a term with less bound variables.
 *)
Lemma apart_weakening :
    forall s : subst,
    forall t1 t2 : term,
      ids_includes (bound_vars t1) (bound_vars t2) ->
      apart s t1 -> apart s t2.
Proof.
  (* Unfold equivalent disjoint definitions *)
  intros s t1 t2 incl hyp.
  unfold apart.
  unfold apart in hyp.
  assert (ids_disjoint2 (subst_variables s)
                        (bound_vars t1))
         as hyp2.
      apply ids_disjoint_implies_ids_disjoint2.
      assumption.
  unfold ids_disjoint2 in hyp2.
  apply ids_disjoint2_implies_ids_disjoint.
  unfold ids_disjoint2.
  unfold ids_includes in incl.

  (* Suppose x is both in the substitution and in BV(t2) *)
  intros x x_in_s x_in_bv_t2.
  (* x is in BV(t1) *)
  assert (ids_In x (bound_vars t1)).
      specialize incl with x.
      apply incl.
      assumption.
  (* x is not in BV(t1) *)
  specialize hyp2 with x.
  assert (~ ids_In x (bound_vars t1)).
      apply hyp2.
      assumption.
  contradiction.
Qed.

Lemma bound_vars_lam_pattern :
  

(*
 * Given a substitution apart from "(p ->th a)"
 * it is also apart from "p" and from "a".
 *)
Lemma apart_lam_pattern :
    forall s : subst,
    forall p : term, forall th : ids, forall a : term,
      apart s (LamT p th a) ->
      (apart s p /\ apart s a).
Proof.
  (* Unfold equivalent disjoint definitions *)
  intros s p th a h_lam.
  unfold apart.
  unfold apart in h_lam.
  assert (ids_disjoint2 (subst_variables s)
                        (bound_vars (LamT p th a)))
         as h_lam2.
      apply ids_disjoint_implies_ids_disjoint2.
      assumption.
  unfold bound_vars in h_lam2.
  fold bound_vars in h_lam2.
  unfold ids_disjoint2 in h_lam2.

  split.
  (* Apart from "p" *)

      apply ids_disjoint2_implies_ids_disjoint.
      unfold ids_disjoint2.
      (* Suppose x is both in the substitution and in BV( p ) *)
      intros x x_in_s x_in_bvp.
      (* x is in BV( p ->th a ) *)
      assert (ids_In x (ids_union
                           (ids_union (bound_vars p)
                                      (bound_vars a))
                           th)).
          apply set_union_intro1.
          apply set_union_intro1.
          assumption.
      (* x is not in BV( p ->th a ) *)
      specialize h_lam2 with x.
      assert (~ ids_In x (ids_union (ids_union (bound_vars p)
                                               (bound_vars a))
                                    th)).
          apply h_lam2.
          assumption.
      contradiction.
Qed.

Fixpoint subst_apply_safe
              (s : subst)
              (t : term)
              (apart_st : apart s t)
              : term :=
  match t with
  | ConT       => ConT
  | VarT x     => if ids_mem x (subst_domain s)
                   then subst_apply_to_id s x
                   else VarT x
  | LamT p th a => LamT
                     (subst_apply_safe s p disj) th (subst_apply_safe s a disj)
  | AppT a b    => ConT
  end.


Fixpoint rename_apart (t : term) (forbidden : ids) : term :=
  match t with
  | ConT        => ConT
  | VarT x      => VarT x
  | LamT p th a => 

Fixpoint alpha_equivalent (t1 : term) (t2 : term) :=
  match t1 with
  

Check LamT (VarT 1) ids_empty (VarT 1).
Check Subst (ids_add 1 ids_empty) (fun x : id => VarT x).