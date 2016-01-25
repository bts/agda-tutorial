module Functions.Recursive where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; zero)

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc n + k = suc (n + k)

pred : ℕ → ℕ      -- predecessor (pred 0 = 0)
pred 0 = 0
pred (suc n) = n

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ  -- subtraction (0 ∸ n = n)
0 ∸ n = n
n ∸ 0 = n
(suc x) ∸ (suc y) = x ∸ y

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ  -- multiplication
0 * n = 0
n * 0 = 0 -- not necessary but more efficient
(suc n) * k = (n * k) + k

infixl 6 _⊔_
_⊔_ : ℕ → ℕ → ℕ  -- maximum
0 ⊔ k = k
k ⊔ 0 = k
(suc n) ⊔ (suc k) = suc (n ⊔ k)

infixl 7 _⊓_
_⊓_ : ℕ → ℕ → ℕ  -- minimum
0 ⊓ k             = 0
k ⊓ 0             = 0
(suc n) ⊓ (suc k) = suc (n ⊓ k)

⌊_/2⌋ : ℕ → ℕ
⌊ 0 /2⌋ = 0
⌊ 1 /2⌋ = 0
⌊ (suc (suc n)) /2⌋ = suc (⌊ n /2⌋)

odd : ℕ → Bool
odd 0 = false
odd 1 = true
odd (suc (suc n)) = odd n

even : ℕ → Bool
even n = odd (suc n)

mutual
  odd′ : ℕ → Bool
  odd′ 0 = false
  odd′ (suc n) = even′ n

  even′ : ℕ → Bool
  even′ 0 = true
  even′ (suc n) = odd′ n

_≡?_ : ℕ → ℕ → Bool
0 ≡? 0 = true
_ ≡? 0 = false
0 ≡? _ = false
suc n ≡? suc k = n ≡? k

_≤?_ : ℕ → ℕ → Bool
0 ≤? _ = true
_ ≤? 0 = false
suc n ≤? suc k = n ≤? k

open import Sets.Recursive using (ℕ⁺; one; double; double+1; ℕ₂; zero; id)

from : ℕ₂ → ℕ
from zero = zero
from (id one) = suc zero
from (id (double n)) = 2 * (from (id n))
from (id (double+1 n)) = 1 + (2 * (from (id n)))

-- Exercise: Define ℤ and some operations on it (_+_, _-_, _*_)

open import Sets.Recursive using (ℤ; negate; zero; id)

-- ℕ⁺-suc : ℕ⁺ → ℕ⁺
-- ℕ⁺-suc one = double one
-- ℕ⁺-suc (double x) = double+1 x
-- ℕ⁺-suc (double+1 x) = double (ℕ⁺-suc x)
--
-- to : ℕ → ℕ₂
-- to zero = zero
-- to (suc zero) = id one
-- -- to (suc (suc zero)) = id (double one)
-- to n with even n | to ⌊ n /2⌋
-- ... | true  | zero    = zero
-- ... | true  | id quot = id (double quot)
-- ... | false | zero    = id one
-- ... | false | id quot = id (double+1 quot)

-- inj-ℕ₂ : ℕ₂ → ℤ
--
-- _ℤ+_ : ℤ → ℤ → ℤ
-- zero ℤ+ x = x
-- x ℤ+ zero = x
-- (negate x⁺) ℤ+ (negate y⁺) = negate (_ (to ((from (id x⁺)) + (from (id y⁺)))))

-- NOTE: i think this is harder than the tutorial author anticipates.

-- _ℕ⁺+_ : ℕ⁺ → ℕ⁺ → ℕ⁺
--
-- _ℤ+_ : ℤ → ℤ → ℤ
-- zero ℤ+ x = x
-- x ℤ+ zero = x
-- (negate x⁺) ℤ+ (negate y⁺) = negate (x⁺ ℕ⁺+ y⁺)
-- (id x⁺) ℤ+ (id y⁺) = id (x⁺ ℕ⁺+ y⁺)
-- (negate x⁺) ℤ+ (id y⁺) = negate (y⁺ ℕ⁺- x⁺)

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

-- Exercise: define (recursive) mirroring of binary trees

mirror : BinTree → BinTree
mirror leaf = leaf
mirror (node left right) = node (mirror right) (mirror left)
