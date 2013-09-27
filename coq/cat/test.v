Require Import FunctionalExtensionality.

Section Equalizer.

    Variable A B : Set.
    Variable f g : A -> B.

    Definition E : Set := { a : A | f a = g a }.
    Definition eq (e : E) : A := proj1_sig e.

    Variable X : Set.
    Variable phi : X -> A.
    Hypothesis phi_equalize : (fun x : X => f (phi x)) = (fun x : X => g (phi x)).

    Variable psi : X -> E.
    Hypothesis psi_commute : (fun x : X, eq (psi x)) = phi.

    Lemma psi_unique : forall x : X,
      psi x = exist (fun a : A => f a = g a) (phi x) (equal_f phi_equalize x).
    Proof.
      intro.
      assert ((fun x : X => eq (psi x)) = phi) as psi_commute_2.
        apply psi_commute.
      subst.
      symmetry.
      apply sig_ind.
      intros a0 p.
      rewrite -> (functional_extensionality x) in psi_commute_2.
      
      
      

End Equalizer.