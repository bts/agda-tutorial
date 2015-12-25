module Sets.Mutual where

open import Sets.Enumerated using (Bool; true; false)
open import Syntax.DecimalNaturals using (ℕ; zero; suc)

data L : Set
data M : Set

data L where
  nil : L
  _∷_ : ℕ → M → L

data M where
  _∷_ : Bool → L → M

-- What are the elements of L and M? - alternating bool-and-nat lists

-- L can be empty

x₀ : M
x₀ = true ∷ nil

x₁ : L
x₁ = 5 ∷ x₀

x₂ : M
x₂ = false ∷ x₁

x₃ : L
x₃ = 10 ∷ x₂

-- "Define trees with nodes with finite children (0, 1, 2, ...)!"

-- with parametric polymorphism? or...:

data ListTree : Set
data Tree : Set

data ListTree where
  nil : ListTree
  _∷_ : Tree → ListTree → ListTree

data Tree where
  node : ListTree -> Tree
  leaf : Tree

-- "Define a small grammar!"

data Term : Set where
  lit : ℕ → Term
  add : Term → Term → Term
  mul : Term → Term → Term
