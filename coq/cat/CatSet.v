Load Category.

(** Set **)

Definition set_comp (X Y Z : Set) (f : Y -> Z) (g : X -> Y) (x : X) := f (g x).
Notation "f ∘ g"  := (set_comp _ _ _ f g) (at level 25).

Definition SetCategoryDefinition := mkCategoryDefinition
  Set
  (fun X Y: Set, X -> Y)
  (fun (X: Set) (x: X), x)
  set_comp.

Lemma Set_comp_id : comp_id SetCategoryDefinition.
Proof. compute. intros. symmetry. apply eta_expansion. Qed.

Lemma Set_id_comp : id_comp SetCategoryDefinition.
Proof. compute. intros. symmetry. apply eta_expansion. Qed.

Lemma Set_comp_assoc : comp_assoc SetCategoryDefinition.
Proof. compute. reflexivity. Qed.

Definition SetCategory := mkCategory
  SetCategoryDefinition
  Set_comp_id
  Set_id_comp
  Set_comp_assoc.

(* Initial object *)

Section SetInitialObject.

  Inductive set_initial_object : Set := .

  Let I : Set := set_initial_object.

  Let inj (X : Set) : I -> X.
    intros. case H.
  Defined.

  Proposition prop_set_initial_object : initial_object SetCategory I.
  Proof.
    compute. intro X.
    apply exist with (inj X).
    split. trivial.
    intros.
    apply functional_extensionality.
    intro x.
    case x.
  Qed.

End SetInitialObject.

(* Terminal object *)

Section SetTerminalObject.

  Inductive set_terminal_object : Set := mkSingleton : set_terminal_object.

  Let T : Set := set_terminal_object.

  Let proj (X : Set) : X -> T :=
    fun _, mkSingleton.

  Proposition prop_set_terminal_object :
    terminal_object SetCategory T.
  Proof.
    compute. intro X.
    apply exist with (proj X).
    split. trivial.
    intros.
    apply functional_extensionality.
    intro x.
    case (y x).
    case (proj X x).
    trivial.
  Qed.

End SetTerminalObject.

(* Product *)

Section SetProduct.

  Variable A B : Set.

  Inductive set_product : Set := mk_set_product : A -> B -> set_product.

  Let P := set_product.

  Let pi1 (p : P) : A :=
    match p with
    | mk_set_product a _ => a
    end.

  Let pi2 (p : P) : B :=
    match p with
    | mk_set_product _ b => b
    end.

  Proposition prop_set_product :
    product SetCategory A B P pi1 pi2.
  Proof.
    compute.
    intros X f1 f2.
    apply exist with (fun x: X, mk_set_product (f1 x) (f2 x)).
    split. split.
    symmetry; apply eta_expansion.
    symmetry; apply eta_expansion.
    intros phi' H12.
    decompose [and] H12.
    apply functional_extensionality.
    intro x.
    symmetry in H; rewrite H.
    symmetry in H0; rewrite H0.
    case (phi' x). reflexivity.
  Qed.

End SetProduct.

(* Coproduct *)

Section SetCoproduct.

  Variable A B : Set.

  Inductive set_coproduct : Set :=
      set_inl : A -> set_coproduct
    | set_inr : B -> set_coproduct.

  Let C : Set := set_coproduct.

  Proposition prop_set_coproduct :
    coproduct SetCategory A B C set_inl set_inr.
  Proof.
    compute.
    intros X g1 g2.
    apply exist with (fun aub: C,
                       match aub with
                       | set_inl a => g1 a
                       | set_inr b => g2 b
                       end).
    split. split.
    symmetry; apply eta_expansion.
    symmetry; apply eta_expansion.
    intros phi' H12.
    decompose [and] H12.
    apply functional_extensionality.
    intro x.
    symmetry in H; rewrite H.
    symmetry in H0; rewrite H0.
    case x.
    reflexivity.
    reflexivity.
  Qed.

End SetCoproduct.

(* Equalizer *)

Section SetEqualizer.

  Variable A B : Set.
  Variable f g : A -> B.

  Definition set_equalizer : Set := { a | f a = g a }.

  Let E : Set := set_equalizer.

  Let eq : E -> A.
    apply proj1_sig with (P := fun a : A, f a = g a).
  Defined.

  Let equalizes (X : Set) (xa : X -> A) := f ∘ xa = g ∘ xa.

  Let eq_equalizes : equalizes E eq.
  Proof.
    apply functional_extensionality.
    apply proj2_sig with (P := fun a : A, f a = g a).
  Qed.

  Let phi (X : Set) (xa : X -> A) (xa_equalize : equalizes X xa) (x : X) : E.
    intros.
    apply exist with (xa x).
    apply equal_f with x in xa_equalize.
    assumption.
  Defined.

  Let eq_phi_xa
          (X : Set) (xa : X -> A) (xa_equalize : equalizes X xa) :
          eq ∘ (phi X xa xa_equalize) = xa.
  Proof.
    intros.
    compute.
    apply functional_extensionality.
    reflexivity.
  Qed.

  Let sig_eq_implies_witness_eq :
    forall (A : Type) (P : A -> Prop) (x y : A) (px : P x) (py : P y),
      exist P x px = exist P y py -> x = y.
  Proof.
    intros.
    replace x with (proj1_sig (exist P x px)).
    replace y with (proj1_sig (exist P y py)).
    apply f_equal.
    assumption.
    unfold proj1_sig; reflexivity.
    unfold proj1_sig; reflexivity.
  Qed. 

  Proposition prop_set_equalizer :
    equalizer SetCategory A B f g E eq eq_equalizes.
  Proof.
    unfold equalizer.
    intros.
    apply exist with (phi X xa xa_equalize).
    split.
    apply (eq_phi_xa X xa xa_equalize).

    intros yinj yinjH.
    compute.
    apply functional_extensionality.
    intro x.
   (*
    * The following Coq syntax: "induction term as []_eqn:<identifier>"
    * is used instead of "induction term as naming_intro_pattern"
    * which does not work. See:
    *
    * http://www.lix.polytechnique.fr/coq/bugs/show_bug.cgi?id=2741
    *)
    induction (yinj x) as (x0, px0)_eqn:yinj_x_equality.
    assert (x0 = xa x).
        replace xa with (eq ∘ yinj).
        unfold eq, set_comp.
        assert (f (proj1_sig (yinj x)) = g (proj1_sig (yinj x))) as f_eq_g.
          replace (proj1_sig (yinj x)) with ((eq ∘ yinj) x).
          replace (eq ∘ yinj) with xa.
          replace (f (xa x)) with ((f ∘ xa) x).
          replace (g (xa x)) with ((g ∘ xa) x).
          apply equal_f.
          assumption.
          unfold set_comp; reflexivity.
          unfold set_comp; reflexivity.
          unfold set_comp, eq; reflexivity.
        apply sig_eq_implies_witness_eq
         with (P  := fun a : A, f a = g a)
              (px := px0)
              (py := f_eq_g).
        replace (exist (fun a : A => f a = g a) x0 px0).
        induction (yinj x).
        apply f_equal.
        apply proof_irrelevance.
    subst x0.
    apply f_equal.
    apply proof_irrelevance.
  Qed.

End SetEqualizer.

(* Pullback *)

Section SetPullback.

  Variable A B C : Set.
  Variable f : A -> C.
  Variable g : B -> C.

  Definition set_pullback : Set := { ab : A * B | f (fst ab) = g (snd ab) }.

  Let P : Set := set_pullback.

  Let pa (p : P) : A := fst (proj1_sig p).
  Let pb (p : P) : B := snd (proj1_sig p).

  Let p_commute : f ∘ pa = g ∘ pb.
  Proof.
    apply functional_extensionality.
    unfold set_comp.
    intro x.
    unfold pa, pb.
    apply (proj2_sig x).
  Qed.

  Let phi (X : Set)
          (xa : X -> A) (xb : X -> B)
          (x_commute : f ∘ xa = g ∘ xb)
          (x : X) : P.
    intros.
    apply exist with (xa x, xb x).
    compute.
    replace (f (xa x)) with ((f ∘ xa) x).
    replace (g (xb x)) with ((g ∘ xb) x).
    apply equal_f; assumption.
    compute; reflexivity.
    compute; reflexivity.
  Defined.

  Proposition prop_set_pullback :
    pullback SetCategory A B C f g P pa pb p_commute.
  Proof.
    intros X xa xb x_commute.
    apply exist with (phi X xa xb x_commute).
    split.
    split.
    compute; symmetry; apply eta_expansion.
    compute; symmetry; apply eta_expansion.
    intros psi psi_comm.
    compute. apply functional_extensionality.
    intro x.
    induction (psi x) as (x0, px0)_eqn:yinj_x_equality.
    compute.
    induction x0 as (a0, b0).
    assert (xa x = a0) as Ha.
      replace xa with (pa ∘ psi).
      compute.
      rewrite yinj_x_equality.
      reflexivity.
      decompose [and] psi_comm; assumption.
    assert (xb x = b0) as Hb.
      replace xb with (pb ∘ psi).
      compute.
      rewrite yinj_x_equality.
      reflexivity.
      decompose [and] psi_comm; assumption.
    subst.
    apply f_equal; apply proof_irrelevance.
  Qed.
    
End SetPullback.
