
module Hott3 where

open import Basic
open import Hott1
open import Hott2

---- Cartesian product types

---- why does this work?!
---- shouldn't we pattern match on x / y?
×-pair= : {li : L} {A B : Set li} {x y : A × B} → ((π1 x == π1 y) × (π2 x == π2 y)) → x == y
×-pair= (refl , refl) = refl

-- Theorem 2.6.2
×-pair=-equiv : {li : L} {A B : Set li} {x y : A × B} →
                    (x == y) ≃ ((π1 x == π1 y) × (π2 x == π2 y))
×-pair=-equiv {li} {A} {B} {x} {y} = ( f ,
                                       qinv-to-isequiv {_} {_} {_} {f} (
                                         ×-pair= {li} {A} {B} {x} {y}
                                         ,
                                         (fg , gf)
                                       )
                                     )
  where
        f : {li : L} {A B : Set li} {x y : A × B} →
            x == y → ((π1 x == π1 y) × (π2 x == π2 y))
        f p = (ap π1 p , ap π2 p)
        ----
        fg : {li : L} {A B : Set li} {x y : A × B} (p : ((π1 x == π1 y) × (π2 x == π2 y))) → f (×-pair= p) == p
        fg (refl , refl) = refl
        ----
        gf : {li : L} {A B : Set li} {x y : A × B} (p : x == y) → ×-pair= (f p) == p
        gf refl = refl

-- Theorem 2.6.4
×-pair=-transport : {li : L} {Z : Set li} {A B : Z → Set li} {z w : Z} →
                    (p : z == w) (x : A z × B z) → 
                        tr^ (λ z → A z × B z) p x ==
                        (tr^ A p (π1 x) , tr^ B p (π2 x))
×-pair=-transport refl (a , b) = refl

-- Theorem 2.6.5
_×-××_ : {li : L} {A B A' B' : Set li} (g : A → A') (h : B → B') → A × B → A' × B'
(g ×-×× h) (a , b) = g a , h b

×-pair=-ap-functorial : {li : L} {A B A' B' : Set li}
                        {g : A → A'}
                        {h : B → B'}
                        {x y : A × B}
                        (p : π1 x == π1 y)
                        (q : π2 x == π2 y) →
                        ap (g ×-×× h) (×-pair= (p , q)) ==
                        ×-pair= (ap g p , ap h q)
×-pair=-ap-functorial refl refl = refl

---- Σ-types

pair= : {li : L} {A : Set li} {B : A → Set li} {x y : Σ A B} →
        (Σ (π1 x == π1 y) (λ p → tr^ B p (π2 x) == π2 y))
        → x == y
pair= (refl , refl) = refl


pair=-equiv : {li : L} {A : Set li} {B : A → Set li} {x y : Σ A B} →
                  (x == y) ≃ Σ (π1 x == π1 y) (λ p → tr^ B p (π2 x) == π2 y)
pair=-equiv {li} {A} {B} {x} {y} = f , qinv-to-isequiv {_} {_} {_} {f} (g , (fg {li} {A} {B} {x} {y} , gf))
  where
    f : {li : L} {A : Set li} {B : A → Set li} {x y : Σ A B} →
          (x == y) → Σ (π1 x == π1 y) (λ p → tr^ B p (π2 x) == π2 y)
    f {li} {A} {B} refl = refl , refl

    g : {li : L} {A : Set li} {B : A → Set li} {x y : Σ A B} →
          Σ (π1 x == π1 y) (λ p → tr^ B p (π2 x) == π2 y) → (x == y)
    g ( refl , refl ) = refl

    gf : {li : L} {A : Set li} {B : A → Set li} {x y : Σ A B} →
          (g ∘ f {li} {A} {B} {x} {y}) ~ id
    gf refl = refl

    fg : {li : L} {A : Set li} {B : A → Set li} {x y : Σ A B} →
          (f {li} {A} {B} {x} {y} ∘ g) ~ id
    fg (refl , refl) = refl

-- Corollary 2.7.3

pair=-uniqueness : {li : L} {A : Set li} {B : A → Set li} {z : Σ A B} -> z == (π1 z , π2 z)
pair=-uniqueness = pair= (refl , refl)

-- Theorem 2.7.4

pair=-transport : {li : L} {A : Set li} {P : A → Set li} {Q : Σ A P → Set li} {x y : A}
                  (p : x == y) (w : Σ (P x) (λ u → Q (x , u))) →
                       tr^ (λ x → Σ (P x) (λ u → Q (x , u))) p w
                       ==
                       (
                        tr^ P p (π1 w) , 
                        tr^ Q (pair= {li} {A} {P} (p , refl {li} {P y} {tr^ P p (π1 w)})) (π2 w)
                       )
pair=-transport refl _ = refl

_××_ : {li : L}
       {A A' : Set li}
       {B  : A → Set li}
       {B' : A' → Set li}
       (g : A → A') →
       ((a : A) → B a → B' (g a)) →
       Σ A B → Σ A' B'
(g ×× h) (a , b) = g a , h a b

-- Auxiliary "bi-dependent" function
apd2 : {li : L}
       {A A' : Set li}
       {B  : A → Set li}
       {B' : A' → Set li}
       {a1 a2 : A}
       {b1 : B a1} {b2 : B a2}
       (p : a1 == a2)
       (q : tr^ B p b1 == b2)
       {g : A → A'}
       {h : (a : A) → B a → B' (g a)}
       → let P = ap g p in
           tr^ B' P (h a1 b1) == h a2 b2
apd2 refl refl = refl

-- Generalization of Theorem 2.6.5
-- as requested in p. 85 or Exercise 2.7
pair=-ap-functorial : {li : L}
                      {A A' : Set li}
                      {B  : A → Set li}
                      {B' : A' → Set li}
                      {x y : Σ A B}
                      (p : π1 x == π1 y)
                      (q : tr^ B p (π2 x) == π2 y)
                      {g : A → A'}
                      {h : (a : A) → B a → B' (g a)}
                      → ap (_××_ {li} {A} {A'} {B} {B'} g h) (pair= (p , q)) ==
                        pair= (ap g p , apd2 {li} {A} {A'} {B} {B'} {π1 x} {π1 y} {π2 x} {π2 y} p q {g} {h})
pair=-ap-functorial refl refl = refl
