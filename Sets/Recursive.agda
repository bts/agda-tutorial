module Sets.Recursive where

open import Sets.Enumerated using (Bool; true; false)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

-- SPC m n   to normalize a term

-- A binary representation of ℕ
data ℕ⁺ : Set where
  one : ℕ⁺
  double : ℕ⁺ → ℕ⁺
  double+1 : ℕ⁺ → ℕ⁺

data ℕ₂ : Set where
  zero : ℕ₂   -- this is valid thanks to type-directed name resolution
  id : ℕ⁺ → ℕ₂

-- We'll prove that ℕ and ℕ₂ are isomorphic.

-- 9 represented in ℕ₂ is:
--   id (double+1 (double (double one)))

-- Which representation (ℕ or ℕ₂) is best for the following tasks?
--   Computing n * 2? ℕ₂
--   Computing ⌊n / 2⌋? ℕ₂
--   Deciding whether the number is odd? ℕ₂
--   Computing n + m? ℕ
--   Computing n * m? ℕ
--   Proving that n + m = m + n for all m and n? ℕ
--   Storing the number? ℕ₂ (uses less space)?

data ℤ : Set where
  negate : ℕ⁺ → ℤ
  id : ℕ⁺ → ℤ
  zero : ℤ

-- binary tree without data
data BinTree₀ : Set where
  leaf : BinTree₀
  node : BinTree₀ → BinTree₀ → BinTree₀

-- binary tree with data at the leaves
data BinTree₁ : Set where
  leaf : ℕ → BinTree₁
  node : BinTree₁ → BinTree₁ → BinTree₁

-- binary tree with data at the nodes
data BinTree₂ : Set where
  leaf : BinTree₂
  node : ℕ → BinTree₂ → BinTree₂ → BinTree₂

-- with booleans in the nodes and nats in the leaves
data BinTree₃ : Set where
  leaf : ℕ → BinTree₃
  node : Bool → BinTree₃ → BinTree₃ → BinTree₃

-- lists of natural numbers
data NatList : Set where
  _::_ : ℕ → NatList → NatList
  nil : NatList

-- non-empty lists of natural numbers
data SomeNats : Set where
  _::_ : ℕ → SomeNats → SomeNats
  last : ℕ → SomeNats
