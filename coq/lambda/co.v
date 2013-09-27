Require Import ZArith.
Require Import ListSet.

(** Terms **)

Definition id := nat.

Inductive lterm : Set :=
   lvar : id -> lterm
 | llam : id -> lterm -> lterm
 | lapp : lterm -> lterm -> lterm.

(** Fresh variables **)

Fixpoint is_fresh (t: lterm) (x: id) : Prop :=
  match t with
  | lvar y     => x <> y
  | llam y t'  => x <> y /\ is_fresh t' x
  | lapp t1 t2 => is_fresh t1 x /\ is_fresh t2 x
  end.

Lemma is_fresh_lam: forall (y: id) (t': lterm) (x: id),
                   is_fresh (llam y t') x -> is_fresh t' x.
Proof.
  intros y t' x H. unfold is_fresh in H; fold is_fresh in H.
  decompose [and] H; assumption.
Qed.

Lemma is_fresh_app1: forall (t1 t2: lterm) (x: id),
                    is_fresh (lapp t1 t2) x -> is_fresh t1 x.
Proof.
  unfold is_fresh; fold is_fresh. intros t1 t2 x H.
  decompose [and] H; assumption.
Qed.

Lemma is_fresh_app2: forall (t1 t2: lterm) (x: id),
                    is_fresh (lapp t1 t2) x -> is_fresh t2 x.
Proof.
  unfold is_fresh; fold is_fresh. intros t1 t2 x H.
  decompose [and] H; assumption.
Qed.

(** Substitution of a single fresh variable **)

Fixpoint subst_var (t : lterm) (y : id) (x : id) : is_fresh t x -> lterm :=
  let translate z := if beq_nat y z
                      then x
                      else z
  in match t with
     | lvar z     => fun _ => lvar (translate z)
     | lapp t1 t2 =>
         fun x_is_fresh : is_fresh (lapp t1 t2) x =>
           lapp (subst_var t1 y x (is_fresh_app1 t1 t2 x x_is_fresh))
                (subst_var t2 y x (is_fresh_app2 t1 t2 x x_is_fresh))
     | llam z t'  =>
         fun x_is_fresh : is_fresh (llam z t') x =>
           llam (translate z)
                (subst_var t' y x (is_fresh_lam z t' x x_is_fresh))
     end.

(** Inductive definition of an alpha equivalence judgment **)

Inductive alpha_equiv : lterm -> lterm -> Prop :=
    alpha_refl :
      forall (t1 t2 : lterm), (t1 = t2) -> alpha_equiv t1 t2
  | alpha_symm :
      forall (t1 t2 : lterm), alpha_equiv t1 t2 -> alpha_equiv t2 t1
  | alpha_trans :
      forall (t1 t2 t3 : lterm),
        alpha_equiv t1 t2 -> alpha_equiv t2 t3 ->
        alpha_equiv t1 t3
  | alpha_app :
      forall (t1 t1' t2 t2' : lterm),
        alpha_equiv t1 t1' -> alpha_equiv t2 t2' ->
        alpha_equiv (lapp t1 t2) (lapp t1' t2')
  | alpha_lam :
      forall (t1 t2 : lterm)
             (y1 y2 x : id)
             (is_fresh1: is_fresh t1 x)
             (is_fresh2: is_fresh t2 x),
        alpha_equiv (subst_var t1 y1 x is_fresh1)
                    (subst_var t2 y2 x is_fresh2) ->
        alpha_equiv (llam y1 t1) (llam y2 t2).

Notation "t1 =alpha t2" := (alpha_equiv t1 t2) (at level 35).

(** Example:   \1->1 =alpha \2->2 **)
Lemma is_fresh_l11_3 : is_fresh (lvar 1) 3.
Proof. compute; discriminate. Qed.
Lemma is_fresh_l22_3 : is_fresh (lvar 2) 3.
Proof. compute; discriminate. Qed.
Lemma example_l11_alpha_l22:
  alpha_equiv (llam 1 (lvar 1)) (llam 2 (lvar 2)).
Proof.
  apply alpha_lam
    with (x := 3)
         (is_fresh1 := is_fresh_l11_3)
         (is_fresh2 := is_fresh_l22_3).
  compute.
  apply alpha_refl.
  reflexivity.
Qed.

Fixpoint is_var (t: lterm) (x: id) : Prop :=
  match t with
  | lvar y     => x = y
  | llam y t'  => x = y \/ is_var t' x
  | lapp t1 t2 => is_var t1 x \/ is_var t2 x
  end.

Fixpoint is_boundvar (t: lterm) (x: id) : Prop :=
  match t with
  | lvar y     => False
  | llam y t'  => x = y \/ is_boundvar t' x
  | lapp t1 t2 => is_boundvar t1 x \/ is_boundvar t2 x
  end.

Lemma _suc_plus : forall n : nat, S n = n + 1.
Proof.
  intro n.
  induction n. 
  compute. reflexivity.
  compute. apply eq_S. apply IHn.
Qed.

Lemma _var_leq_lambda_implies_var_leq_body :
  forall t: lterm, forall m: id, forall y: id,
    (forall x: id, is_var (llam y t) x -> x < m) ->
    (forall x: id, is_var t x -> x < m + 1).
Proof.
  intros t m y H x.
  specialize H with x.
  intro.
  assert (is_var (llam y t) x).
    unfold is_var; fold is_var. right. assumption.
  apply lt_trans with (m := m).
    apply H. assumption.
    replace (m + 1) with (S m).
    apply lt_n_Sn.
    apply _suc_plus.
Qed.

Lemma _var_lt_boundvar_ge_implies_fresh :
  forall t: lterm, forall m: id,
  (forall x: id, is_var t x      -> x < m) ->
  (forall x: id, is_boundvar t x -> x >= m) ->
  is_fresh t m.
Proof.
  intros t m Hvar Hbvar.
  induction t.
  (* lvar *)
  assert (i < m).
    specialize Hvar with i.
    apply Hvar. unfold is_var. reflexivity.
  compute. intro.
  assert (i >= m).
    SearchAbout le.


Lemma exists_alpha_equiv_with_large_boundvars :
  forall t: lterm,
  forall m: id,
    (forall x: id, is_var t x -> x < m) ->
    {s: lterm |    t =alpha s
                /\ forall x: id, is_boundvar s x -> x >= m}.
Proof.
  intros t.
  induction t.
  (* lvar *)
  intro. intro. apply exist with (lvar i).
  split. apply alpha_refl. reflexivity.
  compute. intros. contradiction.
  (* llam *)
  intro. intro.
  specialize IHt with (m + 1).
    assert {s : lterm | t =alpha s /\ (forall x: id, is_boundvar s x -> x >= m + 1)}
        as H_var_leq_body.
      apply IHt. apply (_var_leq_lambda_implies_var_leq_body t m i H).
    assert (is_fresh (proj1_sig H_var_leq_body) m) as m_is_fresh.
      
    apply exist
     with (llam m (subst_var (proj1_sig H0) i m m_is_fresh)).
    (*apply _var_leq_lambda_implies_var_leq_body t*)
    
  apply IHt with H.
  apply exist with (llam m ).
  
Qed.

(** Substitution **)

Fixpoint subst (t: term) (x: var) (s : term) : term :=
  match t with
  | 
