
module Examples where

open import Basic

Magma : {li : L} -> Set (lsuc li)
Magma {li} = Σ (Set li) (λ A -> (A -> A -> A))

-- Natural numbers

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero   + m = m
succ n + m = succ (n + m)

add_n_zero : {n : Nat} -> n == (n + zero)
add_n_zero {zero}   = refl
add_n_zero {succ n} = ap succ (add_n_zero {n}) • refl

add_succ : {n m : Nat} -> (succ n + m) == (n + succ m)
add_succ {zero}   {m} = refl
add_succ {succ n} {m} = ap succ (add_succ {n} {m}) • refl

add_comm : {n m : Nat} -> (n + m) == (m + n)
add_comm {zero}   {_} = add_n_zero
add_comm {succ n} {m} = ap succ (add_comm {n} {m}) • add_succ {m} {n}
  
-- Sums
  
data Either (A B : Set) : Set where
  inl : A -> Either A B
  inr : B -> Either A B

-- Type isomorphisms

AxB_iso_BxA : {A B : Set} -> (A × B) ≃ (B × A)
AxB_iso_BxA = iso swap
                  swap
                  (happly swap_swap)
                  (happly swap_swap)
  where
    swap : {A B : Set} -> (A × B) -> (B × A)
    swap (x , y) = y , x

    swap_swap : {A B : Set} {p : A × B} -> swap (swap p) == p
    swap_swap {_} {_} {x , y} = refl

AsB_iso_BsA : {A B : Set} -> Either A B ≃ Either B A
AsB_iso_BsA = iso swap
                  swap
                  (happly swap_swap)
                  (happly swap_swap)
  where                   
    swap : {A B : Set} -> Either A B -> Either B A
    swap (inl a) = inr a
    swap (inr b) = inl b

    swap_swap : {A B : Set} {s : Either A B} -> swap (swap s) == s
    swap_swap {_} {_} {inl a} = refl
    swap_swap {_} {_} {inr b} = refl

{-

ua_iso_eq : {li : L} {A B : Set li} -> EqT A B -> Eq A B
postulate
  extensionality : {li : L} {A B : Set li} {f g : A -> B} -> EqF f g -> Eq f g

{-
AxB_arrow_right : {A B C : Set} -> EqT (A -> (Pair B C)) (Pair (A -> B) (A -> C))
AxB_arrow_right = iso z unz (happly z_unz) {!!}
  where
    z : {A B C : Set} -> (A -> Pair B C) -> Pair (A -> B) (A -> C)
    z f = pair (pi1 * f) (pi2 * f)

    unz : {A B C : Set} -> Pair (A -> B) (A -> C) -> A -> Pair B C
    unz (pair f g) a = pair (f a) (g a)

    z_unz : {A B C : Set} {f : Pair (A -> B) (A -> C)} -> Eq (z (unz f)) f
    z_unz {_} {_} {_} {pair f1 f2} = refl

    unz_z : {A B C : Set} {f : A -> Pair B C} -> Eq (unz (z f)) f
    unz_z {_} {_} {_} {f} = extensionality (happly (λ {a} -> {!!}))
-}

-}
