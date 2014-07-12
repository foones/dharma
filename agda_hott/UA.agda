module UA where

open import Basic

data _~_ {li : L} {A B : Set li} : (A -> B) -> (A -> B) -> Set (lsuc li) where
  happly : {f g : A -> B} -> ({x : A} -> f x == g x) -> f ~ g

-- type equivalence (\simeq)
data _≃_ {li : L} (A B : Set li) : Set (lsuc li) where
  iso : (f : A -> B) (g : B -> A) -> (f ∘ g) ~ id -> (g ∘ f) ~ id -> A ≃ B

--------------------------------------------------------------------------------

-- Univalence axiom

record Lift {li : L} (lj : L) (A : Set li) : Set (lmax li lj) where
  constructor lift
  field lower : A

postulate
  ua : {li : L} {A B : Set li} -> (A == B) ≃ (Lift (lsuc (lsuc li)) (A ≃ B))

ua_iso_eq : {li : L} {A B : Set li} -> (A ≃ B) -> A == B
ua_iso_eq p = f p ua
  where
    f : {li : L} {A B : Set li} -> A ≃ B -> (A == B) ≃ (Lift (lsuc (lsuc li)) (A ≃ B)) -> A == B
    f p (iso _ g _ _) = g (lift p)

ua_eq_iso : {li : L} {A B : Set li} -> A == B -> A ≃ B
ua_eq_iso refl = iso id id (happly id_id) (happly id_id)
