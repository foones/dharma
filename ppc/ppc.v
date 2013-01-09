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

(* A substitution and a term are *apart* if the bound
   variables of the term do not occur in the substitution
*)
Definition apart (s : subst) (t : term) :=
  ids_disjoint (subst_variables s) (bound_vars t).

Lemma apart_iff_disjoint
           (A B : ids)
           (hyp : forall x : id, ids_In x A -> not (ids_In x B))
           : ids_disjoint A B.
Proof.
  intros A B hyp.
  unfold ids_disjoint, ids_inter, ids_is_empty.
  intros x H.
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

Lemma apart_lam_pattern :
          forall s : subst,
          forall p : term, forall th : ids, forall a : term,
          apart s (LamT p th a) ->
          apart s p.
Proof.
  intros s p th a h_lam.
  unfold apart.
  SearchAbout empty_set.

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