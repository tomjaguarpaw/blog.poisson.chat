module Heads where

open import Data.List

{- Other common definitions of head

-- Partial function (illegal)
head : ∀ {a : Set} → List a → a

-- From Agda's stdlib, Data.List
head : ∀ {a : Set} → List a → Maybe a

-- From Agda's stdlib, Data.List.NonEmpty
head : ∀ {a : Set} → List⁺ a → a

-}

data Failure : Set where
  ERROR : Failure

_`ifNotEmpty`_ : ∀ {a : Set} (b : Set) (xs : List a) → Set
b `ifNotEmpty` (_ ∷ _) = b
b `ifNotEmpty` [] = Failure

headTotal : ∀ {a} (xs : List a) → a `ifNotEmpty` xs
headTotal (x ∷ _) = x
headTotal [] = ERROR

tailTotal : ∀ {a} (xs : List a) → List a `ifNotEmpty` xs
tailTotal (_ ∷ xs) = xs
tailTotal [] = ERROR

-- Unit tests

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

some_number : Nat
some_number = headTotal (1 ∷ 2 ∷ 3 ∷ [])

some_list : List Nat
some_list = tailTotal (1 ∷ 2 ∷ 3 ∷ [])

what_is_some_number : some_number ≡ 1
what_is_some_number = refl

what_is_some_list : some_list ≡ (2 ∷ 3 ∷ [])
what_is_some_list = refl
