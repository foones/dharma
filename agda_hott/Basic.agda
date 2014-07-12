
module Basic where

postulate
  L     : Set
  lzero : L
  lsuc  : L -> L
  lmax  : L -> L -> L
  
{-# BUILTIN LEVEL     L #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  lmax  #-}

--------------------------------------------------------------------------------

-- Dependent product types (\Pi)

Π : {li lj : L} (A : Set li) (B : A -> Set lj) -> Set (lmax li lj)
Π A B = (a : A) -> B a

-- Dependent pair types (\Sigma)

record Σ {li lj : L} (A : Set li) (B : A -> Set lj) : Set (lmax li lj) where
  constructor _,_
  field
    π1 : A
    π2 : B π1
open Σ public

-- Empty type (0)

data Empty {li : L} : Set li where

-- Unit type (1)

-- constructor: \st
data Unit {li : L} : Set li where
  ⋆ : Unit

-- Negation \neg
¬ : {li : L} -> Set li -> Set li
¬ {li} A = (A -> Empty {li})

-- Pairs
_×_ : {li lj : L} (A : Set li) (B : Set lj) -> Set (lmax li lj)
A × B = Σ A (λ _ -> B)

--------------------------------------------------------------------------------

data _==_ {li : L} {A : Set li} : A -> A -> Set (lsuc li) where
  refl : {x : A} -> x == x

-- symmetry (^-^1)
_⁻¹ : {li : L} {A : Set li} {x y : A} -> x == y -> y == x
(refl)⁻¹ = refl

-- transitivity (\bu)
_•_ : {li : L} {A : Set li} {x y z : A} -> x == y -> y == z -> x == z
refl • refl = refl

infixr 2 _•_

-- application
ap : {li : L} {A B : Set li} {x y : A} (f : A -> B) -> x == y -> f x == f y
ap f (refl {x}) = refl {_} {_} {f x}

-- transport
tr : {li : L} {A : Set li} {B : A -> Set li} {x y : A} -> x == y -> B x -> B y
tr refl Bx = Bx

tr^ : {li : L} {A : Set li} (B : A -> Set li) {x y : A} -> x == y -> B x -> B y
tr^ {li} {A} B {x} {y} p Bx = tr {li} {A} {B} {x} {y} p Bx

-- dependent application
apd : {li : L} {A : Set li} {B : A -> Set li} {x y : A} (f : (a : A) -> B a) -> (p : x == y) ->
          tr^ B p (f x) == f y
apd f (refl {x}) = refl {_} {_} {f x}

-- identity and composition

id : {li : L} {A : Set li} -> A -> A
id x = x

id_id : {li : L} {A : Set li} -> {x : A} -> x == x
id_id = refl

_∘_ : {li : L} {A B C : Set li} -> (B -> C) -> (A -> B) -> A -> C
(g ∘ f) x = g (f x)

-- Equational reasoning
_≡<_>_ : {li : L} {A : Set li} (x : A) {y z : A} -> (x == y) -> (y == z) -> (x == z)
_ ≡< refl > refl = refl

infixr 2 _≡<_>_

-- Universe lifting

record Lift {li : L} (lj : L) (A : Set li) : Set (lmax li lj) where
  constructor lift
  field lower : A

