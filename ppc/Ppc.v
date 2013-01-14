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
  | List.cons y ys => if id_eq x y
                       then Some 0
                       else
                         match context_rename_id ys x with
                         | None   => None
                         | Some z => Some (z + 1)
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

Lemma context_rename_bound_vars :
  forall t : term, forall base : id,
  forall x : id,
    ids_In x (bound_vars (context_rename_term t base List.nil)) ->
    x >= base.
Proof.
  intros t base x x_in_bound_vars.
  induction t.
    (* ConT *)
    unfold context_rename_term, bound_vars, ids_In, set_In, ids_empty, empty_set in x_in_bound_vars.
    apply (list_not_In_nil id x) in x_in_bound_vars.
    contradiction.
    (* VarT *)
    unfold context_rename_term in x_in_bound_vars.
      induction (context_rename_id nil i).
          (* var is in the context *)
          unfold bound_vars, ids_In, set_In, ids_empty, empty_set in x_in_bound_vars.
          apply (list_not_In_nil id x) in x_in_bound_vars.
          contradiction.
          (* var is not in the context *)
          unfold bound_vars, ids_In, set_In, ids_empty, empty_set in x_in_bound_vars.
          apply (list_not_In_nil id x) in x_in_bound_vars.
          contradiction.
    (* LamT *)
    unfold context_rename_term in x_in_bound_vars.
    fold context_rename_term in x_in_bound_vars.
    unfold bound_vars in x_in_bound_vars.
    fold bound_vars in x_in_bound_vars.
    
    SearchAbout set.
    
    

Eval compute in
    (context_rename_term
         (AppT (VarT 7)
               (LamT (AppT (VarT 2) (VarT 7))
                     (ids_add 9 (ids_add 7 ids_empty))
                     (AppT (VarT 9) (VarT 7))))
         1000
         List.nil
    ).




Fixpoint rename_var (t : term) (x : id) (y : id) : term :=
  match t with
  | ConT        => ConT
  | VarT z      => if id_eq x z
                    then VarT y
                    else VarT z
  | LamT p th a => if ids_mem x th
                    then LamT p th a
                    else LamT (rename_var p x y)
                              th
                              (rename_var a x y)
  | AppT a b    => AppT (rename_var a x y)
                        (rename_var b x y)
  end.

Fixpoint rename_vars (t : term) (Xs : ids) (Ys : ids) : term :=
  match Xs with
  | List.nil       => t
  | List.cons x xs =>
      match Ys with
      | List.nil       => t
      | List.cons y ys => rename_vars (rename_var t x y) xs ys
      end
  end.

Fixpoint rename_apart (t : term) (forbidden : ids) :=
  match t with
  | ConT        => ConT
  | VarT z      => VarT z
  | LamT p th a => let fresh := ids_fresh (ids_card th) (ids_union forbidden (free_vars (LamT p th a))) in
                   let forbidden2 := ids_union forbidden fresh in
                   let p2 := rename_apart p forbidden2 in
                   let a2 := rename_apart a forbidden2 in
                     LamT (rename_vars p2 th fresh)
                          fresh
                          (rename_vars a2 th fresh)
  | AppT a b    => AppT (rename_apart a forbidden)
                        (rename_apart b forbidden)
  end.

Eval compute in
    (rename_apart
         (AppT (VarT 7)
               (LamT (AppT (VarT 2) (VarT 7)) (ids_add 7 ids_empty) (AppT (VarT 9) (VarT 7))))
         (ids_add 1 ids_empty)
    ).

(*************************************************************************)

Definition ids_mapping_extend (mp : id -> id) (x : id) (y : id) : id -> id
  := fun z : id =>
         if id_eq x z
          then y
          else mp z.

Fixpoint ids_mapping_build (old : ids) (new : ids) : id -> id :=
  match old with
  | List.nil  => fun z : id => z
  | List.cons x xs =>
       match new with
       | List.nil       => fun z : id => z
       | List.cons y ys => ids_mapping_extend (ids_mapping_build xs ys) x y
       end
  end.


(*
 * "substitution_fresh_ids" takes a set of "source" ids and a set
 * of "forbidden" ids and returns a substitution "s" s.t.:
 * "s" maps distinct source ids to distinct variables, which are
 * not in the forbidden set.
 *)
Definition substitution_fresh_ids (source : ids) (forbidden : ids) :=
  subst_build source (ids_fresh (ids_card source) forbidden).

(*
  match t with
  | ConT        => ConT
  | VarT x      => VarT x
  | LamT p th a => 
*)

Fixpoint alpha_equivalent (t1 : term) (t2 : term) :=
  match t1 with
  

Check LamT (VarT 1) ids_empty (VarT 1).
Check Subst (ids_add 1 ids_empty) (fun x : id => VarT x).
