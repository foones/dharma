
module Hott2 where

open import Basic
open import Hott1

-- homotopy (~, not \sim)
_~_ : {li : L} {A B : Set li} -> (A -> B) -> (A -> B) -> Set (lsuc li)
_~_ {_} {A} {B} f g  = Π A (λ x -> f x == g x)

---- ~ is an equivalence relation
homotopy-refl : {li : L} {A B : Set li} {f : A -> B} → f ~ f
homotopy-refl {_} {_} {_} {f} x = refl {_} {_} {f x}

homotopy-sym : {li : L} {A B : Set li} → {f g : A -> B} -> f ~ g -> g ~ f
homotopy-sym fg a = (fg a)⁻¹

homotopy-trans : {li : L} {A B : Set li} → {f g h : A -> B} -> f ~ g -> g ~ h -> f ~ h
homotopy-trans fg gh a = fg a • gh a

homotopy-trans-explicit : {li : L} {A B : Set li} → (f g h : A -> B) -> f ~ g -> g ~ h -> f ~ h
homotopy-trans-explicit _ _ _ fg gh a = fg a • gh a

homotopy-left-compose : {li : L} {A B C : Set li} → {f g : A → B} {h : B → C} -> f ~ g -> (h ∘ f) ~ (h ∘ g)
homotopy-left-compose {_} {_} {_} {_} {_} {_} {h} H a = ap h (H a)

homotopy-right-compose : {li : L} {A B C : Set li} → {f g : B → C} {h : A → B} -> f ~ g -> (f ∘ h) ~ (g ∘ h)
homotopy-right-compose {_} {_} {_} {_} {_} {_} {h} H a = H (h a)

homotopy-left-compose-explicit : {li : L} {A B C : Set li} → {f g : A → B} (h : B → C) -> f ~ g -> (h ∘ f) ~ (h ∘ g)
homotopy-left-compose-explicit h H a = ap h (H a)

homotopy-right-compose-explicit : {li : L} {A B C : Set li} → {f g : B → C} (h : A → B) -> f ~ g -> (f ∘ h) ~ (g ∘ h)
homotopy-right-compose-explicit h H a = H (h a)

---- Lemma 2.4.3
homotopy-comm : {li : L} {A B : Set li} {f g : A -> B} {x y : A} (H : f ~ g) (p : x == y) ->
                    (H x • ap g p) == (ap f p • H y)
homotopy-comm H (refl {x}) = (trans_refl_neut_r (H x))⁻¹ • trans_refl_neut_l (H x)

---- Corollary 2.4.4
homotopy-comm-f : {li : L} {A : Set li} {f : A -> A} (H : f ~ id) {a : A} ->
                      H (f a) == ap f (H a)
homotopy-comm-f {li} {A} {f} H {a} = θ H {a}
  where
    α : {li : L} {A : Set li} {f : A -> A} (H : f ~ id) {a : A} ->
          (H (f a) • ap id (H a)) == (ap f (H a) • H a)
    α H {a} = homotopy-comm H (H a)
    --
    β : {li : L} {A : Set li} {f : A -> A} (H : f ~ id) {a : A} ->
          ((H (f a) • ap id (H a)) • (ap id (H a))⁻¹) == ((ap f (H a) • H a) • (ap id (H a))⁻¹)
    β H {a} = ap (λ p -> p • (ap id (H a))⁻¹) (α H {a})
    --
    γ : {li : L} {A : Set li} {f : A -> A} (H : f ~ id) {a : A} ->
          (H (f a) • (ap id (H a) • (ap id (H a))⁻¹)) == (ap f (H a) • (H a • (ap id (H a))⁻¹))
    γ H {a} = (trans_assoc _ _ _ • β H {a}) • (trans_assoc _ _ _)⁻¹
    --
    δ : {li : L} {A : Set li} {f : A -> A} (H : f ~ id) {a : A} ->
          (H (f a) • refl) == (ap f (H a) • (H a • (ap id (H a))⁻¹))
    δ {_} {_} {f} H {a} = ap (λ p -> H (f a) • p) ((trans_refl_inv_r _)⁻¹) • γ H {a}
    --
    ε : {li : L} {A : Set li} {f : A -> A} (H : f ~ id) {a : A} ->
          H (f a) == (ap f (H a) • (H a • (ap id (H a))⁻¹))
    ε {_} {_} {f} H {a} = trans_refl_neut_r _ • δ H {a}
    --
    ζ : {li : L} {A : Set li} {f : A -> A} (H : f ~ id) {a : A} ->
          H (f a) == (ap f (H a) • (H a • (H a)⁻¹))
    ζ {_} {_} {f} H {a} = ε H {a} • ap (λ x -> ap f (H a) • (H a • (x ⁻¹)))
                                       (ap_id (H a))
    --
    η : {li : L} {A : Set li} {f : A -> A} (H : f ~ id) {a : A} ->
          H (f a) == (ap f (H a) • refl)
    η {_} {_} {f} H {a} = ζ H {a} • ap (λ x -> ap f (H a) • x) (trans_refl_inv_r _)
    --
    θ : {li : L} {A : Set li} {f : A -> A} (H : f ~ id) {a : A} ->
          H (f a) == ap f (H a)
    θ H {a} = η H {a} • (trans_refl_neut_r _) ⁻¹

---- Definition 2.4.6
qinv : {li : L} {A B : Set li} (f : A → B) → Set (lsuc li)
qinv {_} {A} {B} f = Σ (B → A) (λ g -> ((f ∘ g) ~ id) × ((g ∘ f) ~ id))

isequiv : {li : L} {A B : Set li} (f : A → B) → Set (lsuc li)
isequiv {_} {A} {B} f = (Σ (B → A) (λ g → ((f ∘ g) ~ id))) × (Σ (B → A) (λ h → ((h ∘ f) ~ id)))

qinv-to-isequiv : {li : L} {A B : Set li} {f : A → B} → qinv f → isequiv f
qinv-to-isequiv {_} {_} {_} {f} ( g , (α , β) ) = ((g , α) , (g , β))

isequiv-to-qinv : {li : L} {A B : Set li} {f : A → B} → isequiv f → qinv f
isequiv-to-qinv {_} {_} {_} {f} ((g , α), (h , β)) =
                                let γ1 : g ~ (h ∘ (f ∘ g))
                                    γ1 = homotopy-trans-explicit g (id ∘ g) (h ∘ (f ∘ g))
                                           homotopy-refl
                                           (homotopy-trans-explicit (id ∘ g) ((h ∘ f) ∘ g) (h ∘ (f ∘ g))
                                             (homotopy-sym (homotopy-right-compose β))
                                             homotopy-refl)
                                    γ2 : (h ∘ (f ∘ g)) ~ h
                                    γ2 = homotopy-trans-explicit (h ∘ (f ∘ g)) (h ∘ id) h
                                           (homotopy-left-compose α)
                                           homotopy-refl
                                    γ : g ~ h
                                    γ = homotopy-trans γ1 γ2
                                    β' : (g ∘ f) ~ id
                                    β' = homotopy-trans-explicit (g ∘ f) (h ∘ f) id
                                           (homotopy-right-compose γ)
                                           β
                                 in
                                   (g , (α , β'))

-- type equivalence (\simeq)

_≃_ : {li : L} (A B : Set li) → Set (lsuc li)
A ≃ B = Σ (A → B) isequiv

---- ≃ is an equivalence relation

equiv-refl : {li : L} {A : Set li} → A ≃ A
equiv-refl {_} {A} = (id , ((id , homotopy-refl) , (id , homotopy-refl)))

equiv-sym : {li : L} {A B : Set li} → A ≃ B → B ≃ A
equiv-sym {li} {A} {B} (f , fequiv) = unqinv {_} {_} {_} {f} (isequiv-to-qinv {li} {A} {B} {f} fequiv)
  where
    unqinv : {li : L} {A B : Set li} {f : A → B} → qinv f → B ≃ A
    unqinv {_} {_} {_} {f} (g , (α , β)) = (g , ((f , β) , (f , α)))

equiv-trans : {li : L} {A B C : Set li} → A ≃ B → B ≃ C → A ≃ C
equiv-trans {li} {A} {B} {C} (f , fequiv) (g , gequiv) = unqinv {li} {A} {B} {C} {f} {g}
                                                           (isequiv-to-qinv {li} {A} {B} {f} fequiv)
                                                           (isequiv-to-qinv {li} {B} {C} {g} gequiv)
  where
    inv : {li : L} {A B C : Set li} {f : A → B} {g : B → C} {f⁻¹ : B → A} {g⁻¹ : C → B}
                                    (ff⁻¹ : (f ∘ f⁻¹) ~ id)
                                    (gg⁻¹ : (g ∘ g⁻¹) ~ id)
                                    → ((g ∘ f) ∘ (f⁻¹ ∘ g⁻¹)) ~ id
    inv {li} {A} {B} {C} {f} {g} {f⁻¹} {g⁻¹} ff⁻¹ gg⁻¹ =
         homotopy-trans-explicit ((g ∘ f) ∘ (f⁻¹ ∘ g⁻¹)) (g ∘ ((f ∘ f⁻¹) ∘ g⁻¹)) id
                                   homotopy-refl
                                   (homotopy-trans-explicit (g ∘ ((f ∘ f⁻¹) ∘ g⁻¹)) (g ∘ g⁻¹) id
                                     (homotopy-sym
                                       (homotopy-left-compose-explicit g
                                         (homotopy-trans-explicit g⁻¹ (id ∘ g⁻¹) ((f ∘ f⁻¹) ∘ g⁻¹)
                                           homotopy-refl
                                           (homotopy-right-compose-explicit g⁻¹ (homotopy-sym ff⁻¹)))))
                                     gg⁻¹)
    unqinv : {li : L} {A B C : Set li} {f : A → B} {g : B → C} → qinv f → qinv g → A ≃ C
    unqinv {li} {A} {B} {C} {f} {g} (f⁻¹ , (ff⁻¹ , f⁻¹f)) (g⁻¹ , (gg⁻¹ , g⁻¹g)) =
      ((g ∘ f) , qinv-to-isequiv {li} {A} {C} {g ∘ f}
                   ((f⁻¹ ∘ g⁻¹) , (
                         inv {li} {A} {B} {C} {f} {g} {f⁻¹} {g⁻¹} ff⁻¹ gg⁻¹
                         ,
                         inv {li} {C} {B} {A} {g⁻¹} {f⁻¹} {g} {f} g⁻¹g f⁻¹f)))

