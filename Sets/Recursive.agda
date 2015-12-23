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
  negate : ℕ → ℤ
  id : ℕ → ℤ
