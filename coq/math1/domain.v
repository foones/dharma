
Require Import Arith.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

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

Lemma po_lub_unique : forall po S lub1 lub2,
                        po_least_upper_bound po S lub1 ->
                        po_least_upper_bound po S lub2 ->
                        lub1 = lub2.
Proof.
  intros po S lub1 lub2 lub1_prop lub2_prop.
  apply po_antisym.
  apply lub1_prop.
  apply lub2_prop.
  apply lub2_prop.
  apply lub1_prop.
Qed.

Definition po_monotonic A B (f : po_set A -> po_set B) :=
  forall x y, x << y -> f x << f y.

Definition f_ap (A B : Type) (f : A -> B) (S : subset A) : subset B :=
  fun b : B => exists a : A, S a /\ f a = b.

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

Definition d_function_space (D E : domain) :=
  { f : d_set D -> d_set E |
    { f_monotonic : d_monotonic D E f & d_continuous D E f f_monotonic }
  }.

Notation "D =>> E" := (d_function_space D E) (at level 35).

Definition d_function_ap D E (f : D =>> E) (x : d_set D) := proj1_sig f x.

Notation "f $ x" := (d_function_ap _ _ f x) (at level 25).

Definition d_function_le D E (f g : D =>> E) := forall x, f $ x << g $ x.

Lemma d_function_le_refl D E (f : D =>> E) : d_function_le D E f f.
Proof.
  intro.
  apply po_refl.
Qed.

Lemma d_functional_extensionality :
  forall D E (f g : D =>> E),
    (forall x, f $ x = g $ x) -> f = g.
Proof.
  intros D E f g fx_eq_gx.
  case_eq f. intros f_function f_continuous f_shape.
  case_eq g. intros g_function g_continuous g_shape.
  cut (f_function = g_function); [ intro H; destruct H | ].
  cut (f_continuous = g_continuous); [ intro H; destruct H | ].
  reflexivity.
  apply proof_irrelevance.
  rewrite f_shape in fx_eq_gx.
  rewrite g_shape in fx_eq_gx.
  simpl in fx_eq_gx.
  apply functional_extensionality.
  assumption.
Qed.

Lemma d_le_extensional :
  forall D E (f g : D =>> E) x, d_function_le D E f g -> f $ x << g $ x.
Proof.
  intros D E f g x H.
  unfold d_function_le in H.
  specialize H with x.
  assumption.
Qed.

Lemma d_function_le_antisym D E (f g : D =>> E) :
  d_function_le D E f g ->
  d_function_le D E g f ->
  f = g.
Proof.
  unfold d_function_le.
  intros f_le_g g_le_f.
  apply d_functional_extensionality.
  intro x.
  apply po_antisym.
  specialize f_le_g with x.
  assumption.
  specialize g_le_f with x.
  assumption.
Qed.

Lemma d_function_le_trans D E (f g h : D =>> E) :
  d_function_le D E f g ->
  d_function_le D E g h ->
  d_function_le D E f h.
Proof.
  intros f_le_g g_le_h.
  unfold d_function_le in *.
  intro x.
  specialize f_le_g with x.
  specialize g_le_h with x.
  apply po_trans with (g $ x).
  assumption.
  assumption.
Qed.

Definition d_function_space_partial_order (D E : domain) : partial_order :=
  mk_partial_order
    (d_function_space D E)
    (d_function_le D E)
    (d_function_le_refl D E)
    (d_function_le_antisym D E)
    (d_function_le_trans D E).

Definition d_function_domain_bot_function D E : d_set D -> d_set E :=
  fun _ : d_set D => d_bot E.

Lemma d_function_domain_bot_monotonic D E :
  d_monotonic D E (d_function_domain_bot_function D E).
Proof.
  unfold d_monotonic.
  unfold po_monotonic.
  intros x y x_le_y.
  apply po_refl. 
Qed.

Lemma d_function_domain_bot_continuous D E :
  d_continuous D E
               (d_function_domain_bot_function D E)
               (d_function_domain_bot_monotonic D E).
Proof.
  unfold d_continuous. 
  intros F F_filter lubD lubD_lub lubE lubE_lub.
  unfold d_function_domain_bot_function.  
  apply po_lub_unique
   with (S :=
         fun x : po_set (d_po E) =>
           exists y : d_set D,
             F y /\ d_function_domain_bot_function D E y = x).
  apply lubE_lub.
  unfold po_least_upper_bound.
  split.
    (* bot is upper bound *)
    unfold po_upper_bound.
    intros x x_prop.
    elim x_prop.
    intros y x_shape.
    destruct x_shape as (Fy, dom_bot_func_y_eq_x).
    rewrite <- dom_bot_func_y_eq_x.
    unfold d_function_domain_bot_function.
    apply po_refl.
    (* bot is least upper bound *)
    intros.
    apply d_bot_prop.
Qed.

Definition d_function_domain_bot D E : po_set (d_function_space_partial_order D E).
  exists (d_function_domain_bot_function D E).
  exists (d_function_domain_bot_monotonic D E).
  apply d_function_domain_bot_continuous.
Defined.
  
Lemma d_function_domain_bot_apply :
  forall D E x,
    d_function_domain_bot D E $ x = d_bot E.
Proof.
  intros.
  unfold d_function_ap.
  unfold d_function_domain_bot.
  unfold proj1_sig.
  reflexivity.
Qed.

Lemma d_function_domain_bot_prop D E :
  forall f : po_set (d_function_space_partial_order D E),
    d_function_domain_bot D E << f.
Proof.
  intros.
  simpl.
  unfold d_function_le.
  intros.
  rewrite d_function_domain_bot_apply.
  apply d_bot_prop.
Qed.

Lemma d_function_domain_lub_function_filter :
  forall D E F (F_filter : po_filter (d_function_space_partial_order D E) F) x,
    po_filter (d_po E) (fun y : d_set E => exists f, F f /\ f $ x = y).
Proof.
  intros D E F F_filter x.
  unfold po_filter.
  intros y1 y2.
  intros y1_prop y2_prop.
  elim y1_prop; intros f1 y1_shape.
  elim y2_prop; intros f2 y2_shape.
  destruct y1_shape as (f1_in_F, f1_x_eq_y1).
  destruct y2_shape as (f2_in_F, f2_x_eq_y2).
  assert (exists g, F g /\ f1 << g /\ f2 << g) as exists_g.
    apply F_filter.
    assumption.
    assumption.
  elim exists_g; intros g g_prop.
  exists (g $ x).
  split.
    exists g.
    split.
    apply g_prop.
    reflexivity.
    replace y1 with (f1 $ x).
    replace y2 with (f2 $ x).
    destruct g_prop as (g_in_F, (f1_le_g, f2_le_g)).
    
    split.
       apply d_le_extensional; assumption.
       apply d_le_extensional; assumption.
Qed.

Definition d_function_domain_lub_function 
           D E F (F_filter : po_filter (d_function_space_partial_order D E) F) :
           d_set D -> d_set E :=
  fun x : d_set D =>
    d_lub E
          (fun y : d_set E => exists f, F f /\ f $ x = y)
          (d_function_domain_lub_function_filter D E F F_filter x).

Lemma d_functional_monotonic :
  forall D E (f : D =>> E), d_monotonic D E (proj1_sig f).
Proof.
  intros D E f.
  case f.
  simpl.
  intros f_function f_shape.
  destruct f_shape.
  assumption.
Qed.

Lemma d_functional_continuous :
  forall D E (f : D =>> E), d_continuous D E
                                         (proj1_sig f)
                                         (d_functional_monotonic D E f).
Proof.
  intros D E f.
  case f.
  simpl.
  intros f_function f_prop.
  destruct f_prop.
  assumption.
Qed.

Lemma d_function_domain_lub_monotonic
           D E F (F_filter : po_filter (d_function_space_partial_order D E) F) :
             d_monotonic D E (d_function_domain_lub_function D E F F_filter).
Proof.
  unfold d_monotonic.
  unfold po_monotonic.
  intros x y x_le_y.
  unfold d_function_domain_lub_function.
  simpl.
  apply d_lub_prop.
  unfold po_upper_bound.
  intros fx fx_prop.
  elim fx_prop. intros f fx_shape.
  destruct fx_shape as (f_in_F, f_ap_x_eq_fx).
  apply po_trans with (f $ y).
  rewrite <- f_ap_x_eq_fx.
  assert (d_monotonic D E (proj1_sig f)) as f_monotonic.
    apply d_functional_monotonic.
  apply f_monotonic.
  assumption.
  apply d_lub_prop.
  exists f.
  split.
  assumption.
  reflexivity.
Qed.

Lemma d_functional_preserves_filter :
  forall D E (f : D =>> E) F, d_filter D F -> d_filter E (proj1_sig f !! F).
Proof.
  intros D E f F F_filter.
  unfold d_filter.
  unfold po_filter.
  intros a b a_prop b_prop.
  unfold f_ap in a_prop.
  unfold f_ap in b_prop.
  elim a_prop.
  intros a_pre a_shape.
  elim b_prop.
  intros b_pre b_shape.
  destruct a_shape as (a_pre_in_F, a_eq_f_a_pre).
  destruct b_shape as (b_pre_in_F, b_eq_f_b_pre).
  assert (exists c_pre, F c_pre /\ a_pre << c_pre /\ b_pre << c_pre)
      as exists_c_pre.
    apply F_filter.
    assumption.
    assumption.
  elim exists_c_pre.
  intros c_pre c_pre_shape.
  destruct c_pre_shape as (c_pre_in_F, (a_pre_le_c_pre, b_pre_le_c_pre)).
  exists (proj1_sig f c_pre).
  assert (d_monotonic D E (proj1_sig f)) as f_monotonic.
    apply d_functional_monotonic.
  split.
    unfold f_ap.
    exists c_pre. 
    split. assumption. reflexivity.
    split.
    rewrite <- a_eq_f_a_pre. 
    apply f_monotonic.
    assumption.
    rewrite <- b_eq_f_b_pre. 
    apply f_monotonic.
    assumption.
Qed.

Lemma d_function_domain_lub_continuous
           D E F (F_filter : po_filter (d_function_space_partial_order D E) F) :
             d_continuous D E
                          (d_function_domain_lub_function D E F F_filter)
                          (d_function_domain_lub_monotonic D E F F_filter).
Proof.
  unfold d_continuous.
  intros G G_filter lubD lubD_lub lubE lubE_lub.
  apply po_lub_unique
   with (S := fun x : d_set E =>
                exists y : d_set D,
                  G y /\ d_function_domain_lub_function D E F F_filter y = x).
  assumption.
  unfold po_least_upper_bound.
  split.
  (* upper bound *)
  unfold po_upper_bound.
  intros lub_fx lub_fx_prop.
  elim lub_fx_prop.
  intros x lub_fx_shape.
  destruct lub_fx_shape as (x_in_G, lub_f_ap_x_eq_lub_fx).
  rewrite <- lub_f_ap_x_eq_lub_fx.
  apply d_lub_prop.
  unfold po_upper_bound.
  intros f_ap_x f_ap_x_prop.
  elim f_ap_x_prop.
  intros f f_ap_x_shape.
  destruct f_ap_x_shape as (f_in_F, f_x_eq_f_ap_x).
  rewrite <- f_x_eq_f_ap_x.
  apply po_trans with (f $ lubD).
  assert (d_monotonic D E (proj1_sig f)) as f_monotonic.
    apply d_functional_monotonic.
  apply f_monotonic.
  apply lubD_lub.
  assumption.
  apply d_lub_prop.
  exists f.
  split.
  assumption.
  reflexivity.
  (* least *)
  intros z z_prop.
  apply d_lub_prop.
  unfold po_upper_bound.
  intros flubD flubD_prop.
  elim flubD_prop.
  intros f f_shape.
  destruct f_shape as (f_in_F, f_lubD_eq_flubD).
  rewrite <- f_lubD_eq_flubD.
  (* using the fact that f is continuous *)
  assert (d_continuous D E (proj1_sig f) (d_functional_monotonic D E f))
      as f_continuous.
    apply d_functional_continuous.
  unfold d_continuous in f_continuous.
  unfold d_function_ap.
  rewrite <- f_continuous
     with (F := G)
          (lubE := d_lub E
                     (proj1_sig f !! G)
                     (d_functional_preserves_filter D E f G G_filter)).
    (* (1) *)
    apply d_lub_prop.
      unfold po_upper_bound.
      intros fx fx_in_fG.
      unfold f_ap in fx_in_fG.
      elim fx_in_fG.
      intros x fx_shape.
      destruct fx_shape as (x_in_G, fx_eq_f_x).
      rewrite <- fx_eq_f_x.
      apply po_trans
       with (d_lub E
                   (fun y => exists f, F f /\ f $ x = y)
                   (d_function_domain_lub_function_filter D E F F_filter x)).
      (* trans1 *)
        apply d_lub_prop.
        exists f.
        split.
        assumption.
        unfold d_function_ap.
        reflexivity.
      (* trans2 *)
        apply z_prop.
        exists x. 
        split.
        assumption.
        unfold d_function_domain_lub_function.        
        reflexivity.
    (* (2) *)
    assumption.
    (* (3) *)
    assumption.
    (* (4) *)
    unfold f_ap.
    apply d_lub_prop.
Qed.

Definition d_function_domain_lub
             D E F (F_filter : po_filter (d_function_space_partial_order D E) F) :
             po_set (d_function_space_partial_order D E).
  exists (d_function_domain_lub_function D E F F_filter).
  exists (d_function_domain_lub_monotonic D E F F_filter).
  apply (d_function_domain_lub_continuous D E F F_filter).
Defined.

Definition d_function_domain_lub_prop
             D E F (F_filter : po_filter (d_function_space_partial_order D E) F) :
             po_least_upper_bound (d_function_space_partial_order D E)
                                  F (d_function_domain_lub D E F F_filter).
  unfold po_least_upper_bound.
  split.
  (* upper *)
    unfold po_upper_bound.
    intros f f_in_F.
    simpl.
    unfold d_function_le.
    intro.
    simpl.
    unfold d_function_domain_lub_function.
    apply d_lub_prop.
    exists f. 
    split.
    assumption.
    reflexivity.
  (* least *)
    intros g g_upper_bound.
    simpl. 
    unfold d_function_le.
    intro x.
    simpl.
    unfold d_function_domain_lub_function.
    apply d_lub_prop.
    unfold po_upper_bound.
    intro fx.
    intro fx_prop.
    elim fx_prop.
    intros f fx_shape.
    destruct fx_shape as (f_in_F, f_x_eq_fx).
    rewrite <- f_x_eq_fx.
    apply d_le_extensional.
    apply g_upper_bound.
    assumption.
Defined.
 
Definition d_function_domain (D E : domain) :=
  mk_domain
    (d_function_space_partial_order D E)
    (d_function_domain_bot D E)
    (d_function_domain_bot_prop D E)
    (d_function_domain_lub D E)
    (d_function_domain_lub_prop D E).
