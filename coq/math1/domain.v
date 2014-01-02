
Require Import Arith.
Require Import FunctionalExtensionality.

Structure partial_order :=
  mk_partial_order {
      po_set     : Type ;
      po_le      : po_set -> po_set -> Prop ;
      po_refl    : forall a, po_le a a ;
      po_antisym : forall a b,
                     po_le a b ->
                     po_le b a ->
                     a = b ;
      po_trans   : forall a b c,
                     po_le a b ->
                     po_le b c ->
                     po_le a c
  }.

Notation "x << y" := (po_le _ x y) (at level 35).

Definition subset (A : Type) := A -> Prop.


Definition po_upper_bound po (S : subset (po_set po)) (bound : po_set po) :=
  forall x, S x -> x << bound.

Definition po_least_upper_bound po (S : subset (po_set po)) (lub : po_set po) :=
  po_upper_bound po S lub /\
  forall bound, po_upper_bound po S bound -> lub << bound.

Definition po_monotonic A B (f : po_set A -> po_set B) :=
  forall x y, x << y -> f x << f y.

Definition f_ap (A B : Type) (f : A -> B) (S : subset A) :=
  fun b : B => exists a : A, S a /\ b = f a.

Notation "f !! S" := (f_ap _ _ f S) (at level 35).

(**
 **   \/ (f !! S)  <<  f (\/ S)
 **)
Lemma lub_f_vs_f_lub :
  forall A B f,
    po_monotonic A B f ->
    forall (S : subset (po_set A)),
      forall lubA lubB,
        po_least_upper_bound A S lubA ->
        po_least_upper_bound B (f !! S) lubB ->
        lubB << f lubA.
Proof.
  intros A B f f_monotonic S lubA lubB lubA_prop lubB_prop.
  unfold po_least_upper_bound in lubB_prop.
  destruct lubB_prop as (lubB_upper, lubB_least).
  apply lubB_least.
  unfold po_upper_bound.
  intros x x_in_fS.
  unfold f_ap in x_in_fS.
  elim x_in_fS.
  intros y y_prop.
  destruct y_prop as (y_in_S, x_eq_fy).
  replace x with (f y).
  apply f_monotonic.
  unfold po_least_upper_bound in lubA_prop.
  destruct lubA_prop as (lubA_upper, lubA_least).
  apply lubA_upper.
  assumption.
Qed.

(** Filters **)

Definition po_filter po (F : subset (po_set po)) :=
   forall a b, F a -> F b ->
               exists c,
                 F c
                 /\ a << c
                 /\ b << c.

Definition singleton (A : Type) (S : subset A) :=
  forall x y, S x -> S y -> x = y.

Lemma filter_singleton : forall po S, singleton (po_set po) S -> po_filter po S.
Proof.
  unfold po_filter.
  intros po S S_singleton a b a_in_S b_in_S.
  exists a.
  split.
  assumption.
  split.
  apply po_refl.
  replace b with a. 
  apply po_refl.
  apply S_singleton.
  assumption.
  assumption.
Qed.

Structure domain :=
  mk_domain {
      d_po        : partial_order ;
      d_bot       : po_set d_po ;
      d_bot_prop  : forall x, d_bot << x ;
      d_lub       : forall F, po_filter d_po F -> po_set d_po ;
      d_lub_prop  : forall F (F_filter : po_filter d_po F),
                        po_least_upper_bound d_po F (d_lub F F_filter)
  }.

Definition stream_le po I (f : I -> po_set po) (g : I -> po_set po) :=
  forall x, f x << g x.

Lemma stream_refl : forall po I f, stream_le po I f f.
Proof.
  intros.
  unfold stream_le.
  intro.
  apply po_refl.
Qed.

Lemma stream_antisym :
  forall po I f g,
    stream_le po I f g ->
    stream_le po I g f ->
    f = g.
Proof.
  intros po I f g f_le_g g_le_f.
  apply functional_extensionality.
  intro.
  apply po_antisym.
  apply f_le_g.
  apply g_le_f.
Qed.

Lemma stream_trans :
  forall po I f g h,
    stream_le po I f g ->
    stream_le po I g h ->
    stream_le po I f h.
Proof.
  intros po I f g h f_le_g g_le_h.
  unfold stream_le.
  intro.
  apply po_trans with (g x).
  apply f_le_g.
  apply g_le_h.
Qed.

Definition stream po I :=
  mk_partial_order
      (I -> po_set po)
      (stream_le po I)
      (stream_refl po I)
      (stream_antisym po I)
      (stream_trans po I).

Definition stream_bot (D : domain) I : po_set (stream (d_po D) I) :=
  fun _ => d_bot D.

Lemma stream_bot_prop (D : domain) I :
  forall f : po_set (stream (d_po D) I), stream_bot D I << f.
Proof.
  intro f.
  simpl; unfold stream_le.
  intro x.
  unfold stream_bot.
  apply d_bot_prop.
Qed.

Lemma stream_lub_inner_prop
      (D : domain) I
      (F : subset (po_set (stream (d_po D) I)))
      (F_filter : po_filter (stream (d_po D) I) F)
      (x : I) :
      po_filter (d_po D) (fun y => exists f, F f /\ f x = y).
Proof.
  unfold po_filter.
  intros a b a_shape b_shape.
  elim a_shape.
    intro f.
    intro a_shape2.
    destruct a_shape2 as (f_in_F, fx_eq_a).
  elim b_shape.
    intro g.
    intro b_shape2.
    destruct b_shape2 as (g_in_F, gx_eq_b).
  assert (exists h, F h /\ f << h /\ g << h) as exists_h.
    unfold po_filter in F_filter.
    apply F_filter.
    assumption.
    assumption.
  elim exists_h.
  intro hh.
  intro hh_prop.
  destruct hh_prop as (hh_in_F, fg_le_hh).
  destruct fg_le_hh as (f_le_hh, g_le_hh).
  exists (hh x).
  split.
    exists hh.
    split.
    assumption.
    reflexivity.
    replace a with (f x).
    replace b with (g x).
    split.
    apply f_le_hh.
    apply g_le_hh.
Qed.    

Definition stream_lub (D : domain) I
                      (F : subset (po_set (stream (d_po D) I)))
                      (F_filter : po_filter (stream (d_po D) I) F)
                      : po_set (stream (d_po D) I)
                      :=
  fun x : I =>
    d_lub D
          (fun y => exists f, F f /\ f x = y)
          (stream_lub_inner_prop D I F F_filter x).

Lemma stream_lub_prop
      (D : domain) I
      (F : subset (po_set (stream (d_po D) I)))
      (F_filter : po_filter (stream (d_po D) I) F) :
        po_least_upper_bound (stream (d_po D) I) F (stream_lub D I F F_filter).
Proof.
  split.
  (* upper *)
  unfold po_upper_bound.
  intro f.
  intro f_in_F.
  simpl.
  unfold stream_le.
  intro x.
  unfold stream_lub.
  apply d_lub_prop.  
  exists f.
  split.
  assumption.
  reflexivity.
  (* least *)
  intros f_bound f_bound_upper_bound.
  simpl.
  unfold stream_le.
  intro x.
  apply d_lub_prop.
  unfold po_upper_bound.
  intro y.
  intro y_shape.
  elim y_shape.
  intro f.
  intro f_prop.
  destruct f_prop as (f_in_F, fx_eq_y).
  replace y with (f x).
  apply f_bound_upper_bound.
  assumption.
Qed.  

Definition stream_domain (D : domain) I :=
    mk_domain
      (stream (d_po D) I)
      (stream_bot D I)
      (stream_bot_prop D I)
      (stream_lub D I)
      (stream_lub_prop D I).

(** Continuous functions **)

Definition d_set D := po_set (d_po D).
Definition d_monotonic D E (f : d_set D -> d_set E) := po_monotonic (d_po D) (d_po E) f.
Definition d_filter D (F : subset (d_set D)) := po_filter (d_po D) F.
Definition d_least_upper_bound D S lub := po_least_upper_bound (d_po D) S lub.

Definition d_continuous D E f (f_monotonic : d_monotonic D E f) :=
  forall F (F_filter : d_filter D F),
    forall lubD, d_least_upper_bound D F lubD ->
      forall lubE, d_least_upper_bound E (fun x => exists y, F y /\ f y = x) lubE ->
        lubE = f lubD.
 
Check stream_domain.




(** Examples **)
 
Definition poset_nat :=
  mk_partial_order
    nat
    le
    le_refl
    le_antisym
    le_trans.

Definition s123 : subset nat :=
  fun x =>
    x = 1 \/ x = 2 \/ x = 3.

Lemma lub_s123 : least_upper_bound poset_nat s123 3.
Proof.
  unfold least_upper_bound.
  split.
  (* upper bound *)
    unfold po_upper_bound.
    intros x x_cases.
    unfold s123 in x_cases.
    case x_cases.
      intro; compute; replace x with 1; auto.
    intro x_cases2.
    case x_cases2.
      intro; compute; replace x with 2; auto.
      intro; compute; replace x with 3; auto.
  (* least *)
    intros b b_upper_bound.
    compute.
    unfold po_upper_bound in b_upper_bound.
    compute in b_upper_bound.
    specialize b_upper_bound with 3.
    apply b_upper_bound.
    right. right.
    reflexivity.
Qed.

