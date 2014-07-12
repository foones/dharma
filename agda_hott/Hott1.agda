
module Hott1 where

open import Basic

J : {li lj : L} {A : Set li}
    (C : (x y : A) -> x == y -> Set lj) ->
    ({x : A} -> C x x refl) ->
    {x y : A} -> (p : x == y) -> C x y p
J C P refl = P

---- Properties of transitivity

trans_refl_neut_r : {li : L} {A : Set li} {x y : A} (p : x == y) -> p == (p • refl)
trans_refl_neut_r refl = refl

trans_refl_neut_l : {li : L} {A : Set li} {x y : A} (p : x == y) -> p == (refl • p)
trans_refl_neut_l refl = refl

trans_refl_inv_l : {li : L} {A : Set li} {x y : A} (p : x == y) -> ((p)⁻¹ • p) == refl
trans_refl_inv_l refl = refl

trans_refl_inv_r : {li : L} {A : Set li} {x y : A} (p : x == y) -> (p • (p ⁻¹)) == refl
trans_refl_inv_r refl = refl

trans_refl_inv_inv : {li : L} {A : Set li} {x y : A} (p : x == y) -> (p ⁻¹) ⁻¹ == p
trans_refl_inv_inv refl = refl

trans_assoc : {li : L} {A : Set li} {x y z w : A} (p : x == y) (q : y == z) (r : z == w) ->
                  (p • (q • r)) == ((p • q) • r)
trans_assoc refl refl refl = refl

---- Digression: Eckman-Hilton

-- \Omega
Ω : {li : L} {A : Set li} (a : A) -> Set (lsuc li)
Ω a = a == a

-- \Omega^2
Ω² : {li : L} {A : Set li} (a : A) → Set (lsuc (lsuc li))
Ω² a = Ω (refl {_} {_} {a})

-- right whiskering
_•r_ : {li : L} {A : Set li} {a b c : A}
       {p : a == b} {q : a == b} (α : p == q)
       (r : b == c) →
       (p • r) == (q • r)
refl •r refl = refl

-- left whiskering
_•l_ : {li : L} {A : Set li} {a b c : A}
       (p : a == b)
       {r : b == c} {s : b == c} (β : r == s) →
       (p • r) == (p • s)
refl •l refl = refl

--
Eckman-Hilton : {li : L} {A : Set li} {a : A} (α : Ω² a) (β : Ω² a) → (α • β) == (β • α)
Eckman-Hilton α β = (★1-trans α β)⁻¹ • (★1-★2 α β • ★2-trans-rev α β)
  where
    -- definition of \bigstar 1
    _★1_ : {li : L} {A : Set li} {a b c : A}
          {p : a == b} {q : a == b} (α : p == q)
          {r : b == c} {s : b == c} (β : r == s) →
          (p • r) == (q • s)
    _★1_ {_} {_} {_} {_} {_} {p} α {_} {s} β = (p •l β) • (α •r s)

    -- definition of \bigstar 2
    _★2_ : {li : L} {A : Set li} {a b c : A}
          {p : a == b} {q : a == b} (α : p == q)
          {r : b == c} {s : b == c} (β : r == s) →
          (p • r) == (q • s)
    _★2_ {_} {_} {_} {_} {_} {_} {q} α {r} β = (α •r r) • (q •l β)

    -- auxiliary lemmas
    ★1-trans : {li : L} {A : Set li} {a : A}
               (α : refl {_} {_} {a} == refl {_} {_} {a})
               (β : refl {_} {_} {a} == refl {_} {_} {a}) →
               (α ★1 β) == (α • β)
    ★1-trans refl refl = refl

    ★2-trans-rev : {li : L} {A : Set li} {a : A}
                   (α : refl {_} {_} {a} == refl {_} {_} {a})
                   (β : refl {_} {_} {a} == refl {_} {_} {a}) →
                   (α ★2 β) == (β • α)
    ★2-trans-rev refl refl = refl

    ★1-★2 : {li : L} {A : Set li} {a : A}
            (α : refl {_} {_} {a} == refl {_} {_} {a})
            (β : refl {_} {_} {a} == refl {_} {_} {a}) →
            (α ★1 β) == (α ★2 β)
    ★1-★2 refl refl = refl

---- Properties of ap

ap_trans : {li : L} {A B : Set li} {f : A -> B} {x y z : A} (p : x == y) (q : y == z) ->
             ap f (p • q) == (ap f p • ap f q)
ap_trans refl refl = refl

ap_sym : {li : L} {A B : Set li} {f : A -> B} {x y : A} (p : x == y) ->
             ap f (p ⁻¹) == (ap f p)⁻¹
ap_sym refl = refl

ap_ap : {li : L} {A B C : Set li} {f : A -> B} {g : B -> C} {x y : A} (p : x == y) ->
             ap g (ap f p) == ap (g ∘ f) p
ap_ap refl = refl

ap_id : {li : L} {A : Set li} {x y : A} (p : x == y) ->
             ap id p == p
ap_id refl = refl

---- Path lifting property

path_lift : {li : L} {A : Set li} {P : A -> Set li} {x y : A} {u : P x} (p : x == y) ->
           _==_ {_} {Σ A P} (x , u) (y , tr p u)
path_lift refl = refl

---- Transport const

tr_const : {li : L} {A : Set li} {B : Set li} {x y : A} {b : B} (p : x == y) ->
                     tr^ (λ _ -> B) p b == b
tr_const refl = refl

---- Lemma 2.3.8 -- apd vs. tr_const
apd_tr_const : {li : L} {A B : Set li} {x y : A} {f : A -> B} (p : x == y) ->
                   apd f p == (tr_const {_} {_} {_} {_} {_} {f x} p • ap f p)
apd_tr_const refl = refl

---- Lemma 2.3.9
tr_trans : {li : L} {A : Set li} {P : A -> Set li} {x y z : A}
             (p : x == y) (q : y == z) (u : P x) ->
             tr^ P q (tr^ P p u) == tr^ P (p • q) u
tr_trans refl refl _ = refl

---- Lemma 2.3.10
tr_compose : {li : L} {A B : Set li} {P : B -> Set li} {x y : A} (f : A -> B) (p : x == y) (u : P (f x)) ->
                 tr^ (λ x -> P (f x)) p u == tr^ P (ap f p) u
tr_compose _ refl _ = refl

---- Lemma 2.3.11
tr_commute : {li : L} {A : Set li} {P Q : A -> Set li}
             {x y : A}
             {f : {x : A} -> P x -> Q x} (p : x == y) (u : P x) ->
             tr^ Q p (f {x} u) == f {y} (tr^ P p u)
tr_commute refl _ = refl
