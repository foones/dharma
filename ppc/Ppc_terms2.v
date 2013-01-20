Load Identifiers.
Require Import List.

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

Fixpoint all_vars (t : term) : ids :=
  match t with
  | ConT        => ids_empty
  | VarT x      => ids_add x ids_empty
  | LamT p th a => ids_union (ids_union (all_vars p) (all_vars a)) th
  | AppT a b    => ids_union (all_vars a) (all_vars b)
  end.

(*
Lemma all_vars_eq_free_union_bound :
  forall t : term,
  all_vars t = ids_union (free_vars t) (bound_vars t).
Proof.
  induction t.
  (* ConT *)
  compute. trivial.
  (* VarT *)
  compute. trivial.
  (* LamT *)
  unfold all_vars. fold all_vars.
  unfold free_vars. fold free_vars.
  unfold bound_vars. fold bound_vars.
    (* ... *)
  (* AppT *)
  unfold all_vars. fold all_vars.
  unfold free_vars. fold free_vars.
  unfold bound_vars. fold bound_vars.
    (* ... *)
*)

(* Bound variables of subterms *)

Lemma bound_vars_lam :
    forall p : term, forall th : ids, forall a : term,
      ids_includes (bound_vars (LamT p th a))
                   (ids_union (bound_vars p)
                              (bound_vars a)).
Proof.
  intros p th a.
  unfold ids_includes.
  intros x x_in_bvp.
  unfold bound_vars. fold bound_vars.
  apply ids_union_intro1.
  assumption.
Qed.

Lemma bound_vars_lam_pattern :
    forall p : term, forall th : ids, forall a : term,
      ids_includes (bound_vars (LamT p th a))
                   (bound_vars p).
Proof.
  intros p th a.
  apply ids_includes_transitivity
     with (B := (ids_union (bound_vars p) (bound_vars a))).
  apply bound_vars_lam.
  apply ids_includes_union1.
Qed.

Lemma bound_vars_lam_body :
    forall p : term, forall th : ids, forall a : term,
      ids_includes (bound_vars (LamT p th a))
                   (bound_vars a).
Proof.
  intros p th a.
  apply ids_includes_transitivity
     with (B := (ids_union (bound_vars p) (bound_vars a))).
  apply bound_vars_lam.
  apply ids_includes_union2.
Qed.

Lemma bound_vars_app1 :
  forall t1 t2 : term,
    ids_includes (bound_vars (AppT t1 t2))
                 (bound_vars t1).
Proof.
  intros t1 t2.
  unfold ids_includes.
  intros x x_in_bv_t1.
  unfold bound_vars. fold bound_vars.
  apply ids_union_intro1.
  assumption.
Qed.

Lemma bound_vars_app2 :
  forall t1 t2 : term,
    ids_includes (bound_vars (AppT t1 t2))
                 (bound_vars t2).
Proof.
  intros t1 t2.
  unfold ids_includes.
  intros x x_in_bv_t2.
  unfold bound_vars. fold bound_vars.
  apply ids_union_intro2.
  assumption.
Qed.

(* Substitutions *)
Inductive subst : Type :=
  | SubstS (domain : ids) (mapping : id -> term) : subst
  | NoneS  : subst.

Definition subst_domain (s : subst) : ids :=
  match s with
  | SubstS dom _ => dom
  | NoneS        => ids_empty
  end.

Fixpoint subst_free_vars (s : subst) : ids :=
  match s with
  | SubstS dom f => ids_union_map (fun x : id => free_vars (f x)) dom
  | NoneS        => ids_empty
  end.

Definition subst_variables (s : subst) : ids :=
  ids_union (subst_domain s) (subst_free_vars s).

Definition subst_apply_to_id (s : subst) (x : id) : term :=
  match s with
  | SubstS _ f => f x
  | NoneS      => VarT x
  end.

Lemma subst_free_vars_monotone :
  forall dom1 dom2 mapping,
  ids_includes dom1 dom2 ->
  ids_includes (subst_free_vars (SubstS dom1 mapping))
               (subst_free_vars (SubstS dom2 mapping)).
Proof.
  intros dom1 dom2 mapping dom1_includes_dom2.
  induction dom1.
    (* nil *)
    apply ids_includes_nil in dom1_includes_dom2.
    replace dom2 with ids_empty.
    compute. trivial.
    (* a :: dom1 *)
  


(*
 * To model application of a substitution to a term, we follow
 * these steps:
 *
 * - First, define the *safe* application of a substitution to
 *   a term. An application is safe if it can assume that variables
 *   are renamed apart. (It shall receive a proof of this fact).
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

(* apart: weakening of terms *)

(*
 * Given a substitution "s" apart from a given term,
 * "s" is also apart from a term with less bound variables.
 *)
Lemma apart_weakening :
    forall t1 t2 : term,
      ids_includes (bound_vars t1) (bound_vars t2) ->
      forall s : subst, apart s t1 -> apart s t2.
Proof.
  (* Unfold equivalent disjoint definitions *)
  intros t1 t2 inclusion s hyp.
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
  unfold ids_includes in inclusion.

  (* Suppose x is both in the substitution and in BV(t2) *)
  intros x x_in_s x_in_bv_t2.
  (* x is in BV(t1) *)
  assert (ids_In x (bound_vars t1)).
      specialize inclusion with x.
      apply inclusion.
      assumption.
  (* x is not in BV(t1) *)
  specialize hyp2 with x.
  assert (~ ids_In x (bound_vars t1)).
      apply hyp2.
      assumption.
  contradiction.
Qed.

Definition apart_weakening_lam_pattern
             (p : term) (th : ids) (a : term) :
             forall s : subst,
                 apart s (LamT p th a) -> apart s p
  := apart_weakening (LamT p th a) p (bound_vars_lam_pattern p th a).

Definition apart_weakening_lam_body
             (p : term) (th : ids) (a : term) :
             forall s : subst,
                 apart s (LamT p th a) -> apart s a
  := apart_weakening (LamT p th a) a (bound_vars_lam_body p th a).

Definition apart_weakening_app1
             (t1 t2 : term) :
             forall s : subst,
                 apart s (AppT t1 t2) -> apart s t1
  := apart_weakening (AppT t1 t2) t1 (bound_vars_app1 t1 t2).

Definition apart_weakening_app2
             (t1 t2 : term) :
             forall s : subst,
                 apart s (AppT t1 t2) -> apart s t2
  := apart_weakening (AppT t1 t2) t2 (bound_vars_app2 t1 t2).

(* apart: weakening of substitutions *)

Lemma apart_weakening_domain :
  forall dom1 dom2 mapping t,
    ids_includes dom1 dom2 ->
    apart (SubstS dom1 mapping) t ->
    apart (SubstS dom2 mapping) t.
Proof.
  intros dom1 dom2 mapping t dom1_includes_dom2 apart_s1_t.
  unfold apart, subst_variables.
  apply ids_disjoint_union_complete.
  unfold apart, subst_variables in apart_s1_t.
  apply ids_disjoint_union_correct in apart_s1_t.
  destruct apart_s1_t as (apart_dom1_t, apart_fv1_t).
  split.
    (* domain *)
    unfold subst_domain.
    unfold subst_domain in apart_dom1_t.
    apply ids_disjoint_weakening with (A := dom1). 
    assumption. assumption.
    (* free variables *)
    unfold subst_free_vars.
    

(*
 * "subst_apply_safe" takes a substitution "s" and a term "t"
 * and returns a resulting function.
 *
 * The resulting function requires a proof that
 * "s" and "t" are renamed apart, and returns the
 * result of applying "s" to "t".
 *)
Fixpoint subst_apply_safe (s : subst) (t : term) : apart s t -> term :=
  match s with
  | NoneS      => fun _ => t
  | SubstS _ _ =>
      match t return apart s t -> term with
      | ConT        => fun _ => ConT

      | VarT x      => fun _ =>
                          if ids_mem x (subst_domain s)
                              then subst_apply_to_id s x
                              else VarT x

      | LamT p th a => fun apart_st =>
                         LamT
                           (subst_apply_safe s p
                             (apart_weakening_lam_pattern p th a s apart_st))
                           th
                           (subst_apply_safe s a
                             (apart_weakening_lam_body p th a s apart_st))

      | AppT a b    => fun apart_st =>
                         AppT
                           (subst_apply_safe s a
                             (apart_weakening_app1 a b s apart_st))
                           (subst_apply_safe s b
                             (apart_weakening_app2 a b s apart_st))
      end
  end.

(*********************************************************************************)

Fixpoint replace_var_in_set (th : ids) (x : id) (y : id) : ids :=
  match th with
  | nil       => ids_empty
  | z :: zs => (if id_eq z x
                 then y
                 else z) :: replace_var_in_set zs x y
  end.

Fixpoint replace_var_in_term (t : term) (x : id) (y : id) : term :=
  match t with
  | ConT        => ConT
  | VarT z      => if id_eq z x
                    then VarT y
                    else VarT z
  | LamT p th a => if ids_mem x th
                    then LamT p th a
                    else LamT (replace_var_in_term p x y)
                              (replace_var_in_set th x y)
                              (replace_var_in_term a x y)
  | AppT a b    => AppT (replace_var_in_term a x y)
                        (replace_var_in_term b x y)
  end.

Inductive alpha_equivalent (t1 t2 : term) :=
  | alpha_axiom :
      forall x y p th a, not (ids_In y (ids_union (free_vars p)
                                                  (free_vars a)))
                         -> t1 = LamT p th a
                         -> t2 = LamT
                                   (replace_var_in_term p x y)
                                   (replace_var_in_set th x y)
                                   (replace_var_in_term a x y)
                         -> alpha_equivalent t1 t2
  | alpha_refl  : t1 = t2 -> alpha_equivalent t1 t2
  | alpha_symm  : alpha_equivalent t2 t1 -> alpha_equivalent t1 t2
  | alpha_trans : forall t3 : term,
                    alpha_equivalent t1 t3 ->
                    alpha_equivalent t2 t3 ->
                    alpha_equivalent t1 t2
  | alpha_congr_lam_pattern :
                  forall p1 p2 th a,
                  alpha_equivalent p1 p2 ->
                  t1 = LamT p1 th a ->
                  t2 = LamT p2 th a ->
                  alpha_equivalent t1 t2
  | alpha_congr_lam_body :
                  forall p th a1 a2,
                  alpha_equivalent a1 a2 ->
                  t1 = LamT p th a1 ->
                  t2 = LamT p th a2 ->
                  alpha_equivalent t1 t2
  | alpha_congr_app1 :
                  forall a1 a2 b,
                  alpha_equivalent a1 a2 ->
                  t1 = AppT a1 b ->
                  t2 = AppT a2 b ->
                  alpha_equivalent t1 t2
  | alpha_congr_app2 :
                  forall a b1 b2,
                  alpha_equivalent b1 b2 ->
                  t1 = AppT a b1 ->
                  t2 = AppT a b2 ->
                  alpha_equivalent t1 t2.
 
Lemma apart_nilsubst :
  forall t mapping, apart (SubstS nil mapping) t.
Proof.
  intros t mapping.
  compute.
  contradiction.
Qed.

Lemma subst_apply_nilsubst :
  forall t mapping ap,
    subst_apply_safe (SubstS nil mapping) t ap = t.
Proof.
  intros t mapping ap.
  induction t.
  (* ConT *)
  compute. trivial.
  (* VarT *)
  compute. trivial.
  (* LamT *)
  unfold subst_apply_safe.
  fold subst_apply_safe.
    rewrite IHt1. rewrite IHt2. trivial.
  (* AppT *)
  unfold subst_apply_safe.
  fold subst_apply_safe.
    rewrite IHt1. rewrite IHt2. trivial.
Qed.

(*
Lemma subst_apply_nonnilsubst :
  forall t mapping ap,
    subst_apply_safe (SubstS (cons x xs) mapping) t ap
    = subst_apply_safe (SubstS xs mapping) (replace_var_in_term t x (mapping xs)) ....
Proof.
*)

Lemma subst_defined_implies_alpha_equivalent :
  forall s t1 t2
         (ap1: apart s t1)
         (ap2: apart s t2),
     alpha_equivalent t1 t2 ->
     alpha_equivalent (subst_apply_safe s t1 ap1) (subst_apply_safe s t2 ap2).
Proof.
  intros s t1 t2 ap1 ap2 eq_t1_t2.
  induction s.
      (* SubstS *)
      induction domain.
          (* nil domain *)
          rewrite subst_apply_nilsubst.
          rewrite subst_apply_nilsubst.
          assumption.
          (* cons x xs domain *)
          induction t1.
