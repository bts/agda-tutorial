module TermInference where

open import Data.Empty using (⊥)
open import Data.Unit  using (⊤; tt)
open import Data.Sum   using (_⊎_; inj₁; inj₂)
open import Data.Nat   using (ℕ; suc; zero)

-- Term inference

data Fin′ : ℕ → Set where
  zero : (n : _)          → Fin′ (suc n) -- ℕ is inferred
  suc  : (n : _) → Fin′ n → Fin′ (suc n) -- ℕ is inferred

x : Fin′ 3
x = suc _ (zero _) -- 2 and 1 are inferred

-- Implicit args

data Fin : ℕ → Set where
  zero : {n : _}         → Fin (suc n)
  suc  : {n : _} → Fin n → Fin (suc n)

x′ : Fin 3
x′ = suc {_} (zero {_})

x″ : Fin 3
x″ = suc zero

-- "Although zero : Fin 1 and zero : Fin 2, zero does not have multiple
--  different types; the implicit arguments make the types unique."

-- "Variables with inferred types can be introduced by ∀":

data Fin₁ : ℕ → Set where
  zero : ∀ n → Fin₁ (suc n)
  suc  : ∀ n → Fin₁ n → Fin₁ (suc n)

data Fin₂ : ℕ → Set where
  zero : ∀ {n} → Fin₂ (suc n)
  suc  : ∀ {n} → Fin₂ n → Fin₂ (suc n)
