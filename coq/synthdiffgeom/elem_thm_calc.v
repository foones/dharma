Require Import FunctionalExtensionality.

Section RealLine.

    Variable R : Set.

    Variable add : R -> R -> R.
    Variable zero : R.
    Hypothesis add_zero_l : forall x, add zero x = x.
    Hypothesis add_comm   : forall x y, add x y = add y x.

    Lemma add_zero_r : forall x, add x zero = x.
      intro x.
      transitivity (add zero x).
      apply add_comm.
      apply add_zero_l.
    Qed.

    Hypothesis add_assoc  : forall x y z, add x (add y z) = add (add x y) z.
    Variable opp : R -> R.
    Hypothesis add_opp_eq_zero : forall x, add x (opp x) = zero.

    Variable mul : R -> R -> R.
    Variable one : R.
    Hypothesis mul_one_l  : forall x, mul one x = x.
    Hypothesis mul_comm   : forall x y, mul x y = mul y x.
    Hypothesis mul_assoc  : forall x y z, mul x (mul y z) = mul (mul x y) z.
    Variable inv : R -> R.
    Hypothesis mul_inv_eq_one : forall x, x = zero \/ mul x (inv x) = one.

    Hypothesis distr : forall x y z, mul x (add y z) = add (mul x y) (mul x z).

    (* Slopes at 0 -- axioms *)

    Variable slope0 : (R -> R) -> R.

    Let is_slope0 (f : R -> R) (sl : R) : Prop :=
        forall eps, mul eps eps = zero ->
          f eps = add (f zero) (mul sl eps).
 
    Hypothesis koch_lauvere0 : forall f : R -> R, is_slope0 f (slope0 f).
    
    Hypothesis slope0_unique :
      forall f : R -> R,
        forall sl, is_slope0 f sl -> sl = slope0 f.

    (* Slopes at X0 -- lemmas *)

    Let slide (f : R -> R) (x0 : R) : R -> R := fun x => f (add x x0).

    Let is_slopeX0 (f : R -> R) (sl : R) (x0 : R) : Prop :=
        forall eps, mul eps eps = zero ->
          f (add x0 eps) = add (f x0) (mul sl eps).

    Let slopeX0 (f : R -> R) (x0 : R) := slope0 (slide f x0).

    Lemma koch_lauvereX0 : forall f : R -> R, forall x0 : R,
      is_slopeX0 f (slopeX0 f x0) x0.
    Proof.
      intros f x0.
      intros eps eps_nil.
      replace (f (add x0 eps)) with (slide f x0 eps).
        unfold slopeX0.
        replace (f x0) with (slide f x0 zero).
        apply koch_lauvere0. assumption.
        unfold slide. apply f_equal. apply add_zero_l.
        compute. apply f_equal. apply add_comm.
    Qed.

    Lemma slopeX0_unique : forall f : R -> R, forall sl: R, forall x0 : R,
      is_slopeX0 f sl x0 -> sl = slopeX0 f x0.
    Proof.
      intros f sl x0 is_sl.
      unfold is_slopeX0 in is_sl.
      unfold slopeX0.
      assert (is_slope0 (slide f x0) sl).
      intro eps.
      specialize is_sl with eps.
      intro eps_nil.
      replace (slide f x0 zero) with (f x0).
        unfold slide. rewrite add_comm. apply is_sl. assumption.
        compute; apply f_equal; symmetry; apply add_zero_l.
      apply slope0_unique. assumption.
    Qed.

    (* Areas *)

    Let is_area (area : (R -> R) -> R -> R) :=
      forall f, forall x,
      forall eps, mul eps eps = zero ->
        area f (add x eps) =
        add (area f x) (add (mul (f x) eps)
                            (mul (mul (slopeX0 f x) eps) (inv (add one one)))).

    Lemma fund_thm_calc1 :
      forall a f, is_area a -> slopeX0 (a f) = f.
    Proof.
      intros a f is_a.
      apply functional_extensionality.
      intro x0.
      symmetry. apply slopeX0_unique.
      intros eps eps_nil.
      rewrite (is_area a f x0 eps). 
      replace (add (a f x0) (mul (f x0) eps)) with
              (add (a f x0) (add (mul (f x0) eps)
                            (mul (mul (slopeX0 f x0) eps) (inv (add one one))))).
      admit.
      apply f_equal2.
        reflexivity.
        replace (mul (mul (slopeX0 f x0) eps)
                     (inv (add one one)))
           with zero.
        rewrite add_zero_r. reflexivity.
        

      

End RealLine.