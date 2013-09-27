
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Definition ex1 {A : Type} (P : A -> Prop) : Type :=
  { x : A | P x /\ forall y : A, P y -> x = y }.

(** Abstract categories **)

Section AbstractCategory.

  Structure CategoryDefinition : Type := mkCategoryDefinition {
    ob   : Type ;
    hom  : ob -> ob -> Type ;
    id   : forall X: ob, hom X X ;
    comp : forall (X Y Z: ob) (f: hom Y Z) (g: hom X Y), hom X Z
  }.

  Definition comp_id (def : CategoryDefinition) : Prop :=
    forall (X Y: ob def) (f: hom def X Y),
     comp def X X Y f (id def X) = f.

  Definition id_comp (def : CategoryDefinition) : Prop :=
    forall (X Y: ob def) (f: hom def X Y),
     comp def X Y Y (id def Y) f = f.

  Definition comp_assoc (def : CategoryDefinition) : Prop :=
    forall (W X Y Z : ob def)
           (f : hom def Y Z)
           (g : hom def X Y)
           (h : hom def W X),
             comp def W Y Z f (comp def W X Y g h)
           = comp def W X Z (comp def X Y Z f g) h.

  Structure Category : Type := mkCategory {
    def        : CategoryDefinition ;
    Comp_id    : comp_id def ;
    Id_comp    : id_comp def ;
    Comp_assoc : comp_assoc def
  }.

End AbstractCategory.

Notation "f ** g"  := (comp (def _) _ _ _ f g) (at level 25).
Notation "X ~~> Y" := (hom (def _) X Y) (at level 35).

Section AbstractCategoryDefs.

  Variable c : Category.

  Definition Ob   := ob (def c).
  Definition Hom  := hom (def c).
  Definition Id   := id (def c).
  Definition Comp := comp (def c).

  Definition initial_object (I : Ob) :=
    forall X: Ob,
      ex1 (fun f: I ~~> X, True).

  Definition terminal_object (T : Ob) :=
    forall X: Ob,
      ex1 (fun f: X ~~> T, True).

  Definition product (A B AxB : Ob)
                     (pi1 : AxB ~~> A)
                     (pi2 : AxB ~~> B) :=
    forall (X: Ob) (f1 : X ~~> A) (f2 : X ~~> B),
      ex1 (fun phi : X ~~> AxB,
              pi1 ** phi = f1 /\
              pi2 ** phi = f2
      ).

  Definition coproduct (A B AuB : Ob)
                       (in1 : A ~~> AuB)
                       (in2 : B ~~> AuB) :=
      forall (X : Ob) (g1 : A ~~> X) (g2 : B ~~> X),
      ex1 (fun phi : AuB ~~> X,
              phi ** in1 = g1 /\
              phi ** in2 = g2
      ).

  Definition equalizer (A B : Ob) (f g : A ~~> B)
                       (E : Ob) (ea : E ~~> A)
                       (ea_equalize: f ** ea = g ** ea)
                       :=
      forall (X : Ob) (xa : X ~~> A) (xa_equalize : f ** xa = g ** xa),
        ex1 (fun phi : X ~~> E, ea ** phi = xa).

  Definition pullback (A B C : Ob) (f : A ~~> C) (g : B ~~> C)
                      (P : Ob) (pa : P ~~> A) (pb : P ~~> B)
                      (p_commute : f ** pa = g ** pb) :=
      forall (X : Ob) (xa : X ~~> A) (xb : X ~~> B)
             (x_commute : f ** xa = g ** xb),
        ex1 (fun phi : X ~~> P, pa ** phi = xa /\ pb ** phi = xb).

End AbstractCategoryDefs.
