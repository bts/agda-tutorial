module Sets.Indexed where

open import Data.Empty using (⊥)
open import Data.Unit  using (⊤; tt)
open import Data.Sum   using (_⊎_; inj₁; inj₂)
open import Data.Bool  using (Bool; true; false)
open import Data.Nat   using (ℕ; zero; suc)

-- Fin, family of finite sets
--   Fin n has exactly n elements

data Fin : ℕ → Set where
  zero : (n : ℕ)         → Fin (suc n)
  suc  : (n : ℕ) → Fin n → Fin (suc n)

-- zero 0 : Fin 1

-- zero 1 : Fin 2
-- suc 1 (zero 0) : Fin 2

-- zero 2 : Fin 3
-- suc 2 (zero 1) : Fin 3
-- suc 2 (suc 1 (zero 0)) : Fin 3

-- Exercise: Define a Bool indexed family of sets such that the set indexed by
-- false contains no elements and the set indexed by true contains one element!

data Foo : Bool → Set where
  foo : Foo true

-- Exercise: Define a ℕ indexed family of sets such that the sets indexed by
-- even numbers contain one element and the others are empty!

data Bar : ℕ → Set where
  zero : Bar zero
  suc  : (n : ℕ) → Bar n → Bar (suc (suc n))

-- Vec A n ∼ Aⁿ

data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  cons : (n : ℕ) → A → Vec A n → Vec A (suc n)

-- data X PARAMETER : INDEX → X where

-- Exercise: Define a Bool indexed family of sets with two parameters, A and B,
-- such that the set indexed by false contains an A element and the set indexed
-- by true contains a B element!

data Baz (A B : Set) : Bool → Set where
  baz₁ : A → Baz A B false
  baz₂ : B → Baz A B true
