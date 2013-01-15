Load Identifiers.

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

Definition context := List.list id.

Fixpoint context_rename_id (ctx : context) (x : id) : option id :=
  match ctx with
  | List.nil       => None
  | List.cons y ys =>
      match context_rename_id ys x with
      | Some z => Some (z + 1)
      | None   => if id_eq x y
                   then Some 0
                   else None
      end
  end.

Fixpoint context_rename_term (t : term) (base : id) (ctx : context) : term :=
  match t with
  | ConT        => ConT
  | VarT x      => match context_rename_id ctx x with
                   | None   => VarT x
                   | Some z => VarT (base + z)
                   end
  | LamT p th a => let ctx2 := List.app ctx th in
                     LamT (context_rename_term p base ctx2)
                          (seq (base + List.length ctx) (ids_card th))
                          (context_rename_term a base ctx2)
  | AppT a b    => AppT (context_rename_term a base ctx)
                        (context_rename_term b base ctx)
  end.

Lemma list_not_In_nil : forall A : Type, forall x : A,
                          not (List.In x List.nil).
Proof.
  intros A x.
  unfold In.
  intro Hyp.
  contradiction.
Qed.

Lemma context_rename_bound_vars_VarT :
  forall v : id,
  forall base : id,
  forall x : id,
  forall ctx : context,
  ids_In x (bound_vars (context_rename_term (VarT v) base ctx)) ->
  x >= base.
Proof.
  intros v base x ctx x_in_bound_vars.
  unfold context_rename_term in x_in_bound_vars.
  induction (context_rename_id ctx v).
      apply (list_not_In_nil id x) in x_in_bound_vars.
      contradiction.
      apply (list_not_In_nil id x) in x_in_bound_vars.
      contradiction.
Qed.

Lemma nat_In_seq_is_geq_start :
  forall x len start : id, List.In x (seq start len) -> x >= start.
Proof.
  intros x len.
  induction len.
    (* Base case *)
    intro start.
    compute. intro. contradiction.
    (* Induction step *)
    intro start.
    unfold seq. fold seq.
    unfold In.
    intro. destruct H.
      replace start with x.
      apply le_refl.
      assert (x >= S start).
        apply IHlen. assumption.
        apply (le_trans start (S start) x).
        apply le_n_Sn. assumption.
Qed.

Lemma context_rename_bound_vars_LamT :
    forall pat : term, forall th : ids, forall body : term,
    forall base : id,
    forall x : id,
    forall HI_pat :
          forall ctx : context,
          ids_In x (bound_vars (context_rename_term pat base ctx)) ->
          x >= base,
    forall HI_body :
          forall ctx : context,
          ids_In x (bound_vars (context_rename_term body base ctx)) ->
          x >= base,
    forall ctx : context,
    ids_In x (bound_vars (context_rename_term (LamT pat th body) base ctx)) ->
    x >= base.
Proof.
   intros pat th body base x HI_pat HI_body ctx x_in_bound_vars_lam.
   unfold context_rename_term in x_in_bound_vars_lam.
   fold context_rename_term in x_in_bound_vars_lam.
   unfold bound_vars in x_in_bound_vars_lam.
   fold bound_vars in x_in_bound_vars_lam.
   apply ids_union_elim3 in x_in_bound_vars_lam.
   destruct x_in_bound_vars_lam.
   destruct H.
     apply HI_pat with (ctx := List.app ctx th). assumption.
     apply HI_body with (ctx := List.app ctx th). assumption.
     apply (le_trans base (base + length ctx) x).
         apply le_plus_l.
         apply nat_In_seq_is_geq_start with (len := ids_card th).
         assumption.
Qed.

Lemma context_rename_bound_vars_AppT :
  forall a b : term,
  forall base : id,
  forall x : id,
  forall HI_a :
      forall ctx : context,
      ids_In x (bound_vars (context_rename_term a base ctx)) ->
      x >= base,
  forall HI_b :
      forall ctx : context,
      ids_In x (bound_vars (context_rename_term b base ctx)) ->
      x >= base,
  forall ctx : context,
  ids_In x (bound_vars (context_rename_term (AppT a b) base ctx)) ->
  x >= base.
Proof.
  intros a b x base HI_a HI_b ctx x_in_bound_vars_app.
  unfold context_rename_term in x_in_bound_vars_app.
  fold context_rename_term in x_in_bound_vars_app.
  unfold bound_vars in x_in_bound_vars_app.
  fold bound_vars in x_in_bound_vars_app.
  apply ids_union_elim2 in x_in_bound_vars_app.
  destruct x_in_bound_vars_app.
      apply HI_a with (ctx := ctx). assumption.
      apply HI_b with (ctx := ctx). assumption.
Qed.  

Lemma context_rename_bound_vars :
  forall t : term, forall base : id,
  forall x : id,
  forall ctx : context,
  ids_In x (bound_vars (context_rename_term t base ctx)) ->
  x >= base.
Proof.
  intros t base x.
  induction t.
    (* ConT *)
    intros ctx x_in_bound_vars.
    unfold context_rename_term, bound_vars, ids_In, set_In, ids_empty, empty_set in x_in_bound_vars.
    apply (list_not_In_nil id x) in x_in_bound_vars.
    contradiction.
    (* VarT *)
    intros ctx x_in_bound_vars.
    apply context_rename_bound_vars_VarT with (v := i) (ctx := ctx).
        assumption.
    (* LamT *)
    intros ctx x_in_bound_vars.
    apply context_rename_bound_vars_LamT
     with (pat := t1)
          (th := i)
          (body := t2)
          (ctx := ctx).
    assumption. assumption. assumption.
    (* AppT *)
    intros ctx x_in_bound_vars.
    apply context_rename_bound_vars_AppT
     with (a := t1)
          (b := t2)
          (ctx := ctx).
    assumption. assumption. assumption.
Qed.   

Eval compute in
    (context_rename_term
         (AppT (VarT 7)
               (LamT (AppT (VarT 2) (VarT 7))
                     (ids_add 9 (ids_add 7 ids_empty))
                     (AppT (VarT 9) (VarT 7))))
         1000
         List.nil
    ).

Eval compute in
    (context_rename_term
         (LamT ConT
               (ids_add 2 ids_empty)
               (AppT (LamT ConT
                        (ids_add 2 ids_empty)
                        (VarT 2))
                     (VarT 2)))
         1000
         List.nil
    ).
