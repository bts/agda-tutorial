module Sets.Propositions where

open import Data.Nat using (ℕ; zero; suc)
open import Sets.Recursive using (ℕ⁺; one; double; double+1)

-- Proofs as data
--   "The proofs of each proposition will have a distinct type."

data ⊤ : Set where
  tt : ⊤ -- The trivial proof of ⊤ ("trivially true")

data ⊥ : Set where
  -- does not have any proofs

data _×_ (A B : Set) : Set where -- A ∧ B
  _,_ : A → B → A × B -- proofs of A, B ⇒ A ∧ B

infixr 4 _,_
infixr 2 _×_

data _⊎_ (A B : Set) : Set where -- A ∨ B
  inj₁ : A → A ⊎ B -- proof 1: from proof a of A
  inj₂ : B → A ⊎ B -- proof 2: from proof b of B

infixr 1 _⊎_

-- "_⊎_ represents constructive disjunction; we represent classical disjunction
--  later and compare them."

-- Exercise: Construct one proof for each proposition if possible:

⊤×⊤ : ⊤ × ⊤
⊤×⊤ = tt , tt

-- ⊤ × ⊥ has no proof

-- ⊥ × ⊥ has no proof

⊤⊎⊤ : ⊤ ⊎ ⊤
⊤⊎⊤ = inj₁ tt

⊤⊎⊥ : ⊤ ⊎ ⊥
⊤⊎⊥ = inj₁ tt

-- ⊥ ⊎ ⊥ has no proof

xyz : ⊥ ⊎ ⊤ ⊎ ⊤ × (⊥ ⊎ ⊥) ⊎ ⊤
xyz = inj₂ (inj₁ tt)

-- Less-or-equal predicate

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n}           → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

-- z≤n {0} : 0 ≤ 0
-- z≤n {1} : 0 ≤ 1
-- ...
-- s≤s (z≤n {0}) : 1 ≤ 1
-- s≤s (z≤n {1}) : 1 ≤ 2
-- proof : proposition

-- (1 ≤ 0) is a valid expression which denotes an empty set.

-- Proving non-emptiness

1≤10 : 1 ≤ 10
1≤10 = s≤s z≤n

-- Exercise: prove that 3 ≤ 7.

3≤7 : 3 ≤ 7
3≤7 = s≤s (s≤s (s≤s z≤n))

-- Proving emptiness

7≰3 : 7 ≤ 3 → ⊥
7≰3 (s≤s (s≤s (s≤s ()))) -- rhs omitted when there's an absurd pattern in lhs

-- Exercise: prove that 4 ≤ 2 is empty.

4≰2 : 4 ≤ 2 → ⊥
4≰2 (s≤s (s≤s ()))

-- "Note that emptiness proofs can be used in other emptiness proofs:"

8≰4 : 8 ≤ 4 → ⊥
8≰4 (s≤s x) = 7≰3 x

-- Exercise: guess which kind of code can be generated from emptiness proofs.

-- More emptiness proofs, inductively?

-- Exercise: Define an indexed set _isDoubleOf_ : ℕ → ℕ → Set such that m
-- isDoubleOf n is non-empty iff m is the double of n.
--   Prove that 8 isDoubleOf 4 is non-empty.
--   Prove that 9 isDoubleOf 4 is empty.

data _isDoubleOf_ : ℕ → ℕ → Set where
  doubled0 : 0 isDoubleOf 0
  double : ∀ {m n} → m isDoubleOf n → (suc (suc m)) isDoubleOf (suc n)

8IsDoubleOf4 : 8 isDoubleOf 4
8IsDoubleOf4 = double (double (double (double doubled0)))

9IsntDoubleOf4 : 9 isDoubleOf 4 → ⊥
9IsntDoubleOf4 (double (double (double (double ()))))

-- Exercise: Define an indexed set Odd : ℕ → Set such that Odd n is non-empty
-- iff n is odd.
-- Prove that Odd 9 is non-empty.
-- Prove that Odd 8 is empty.

data Odd : ℕ → Set where
  oneOdd : Odd 1
  nextOdd : ∀ {n} → Odd n → Odd (suc (suc n))

odd9 : Odd 9
odd9 = nextOdd (nextOdd (nextOdd (nextOdd oneOdd)))

notOdd8 : Odd 8 → ⊥
notOdd8 (nextOdd (nextOdd (nextOdd (nextOdd ()))))

-- Exercise: Define Even : ℕ → Set and Odd : ℕ → Set mutually.

data Odd′ : ℕ → Set
data Even′ : ℕ → Set

data Odd′ where
  next′ : ∀ {n} → Even′ n → Odd′ (suc n)

data Even′ where
  zeroEven :                  Even′ 0
  next′    : ∀ {n} → Odd′ n → Even′ (suc n)

-- Exercise: Define equality _≡_ : ℕ → ℕ → Set.

data _≡_ : ℕ → ℕ → Set where
  ≡-refl : ∀ {n} → n ≡ n
  -- 0≡0 : 0 ≡ 0
  -- s≡s : ∀ {n} → n ≡ n → (suc n) ≡ (suc n)

-- Exercise: Define non-equality _≠_ : ℕ → ℕ → Set.

data _≠_ : ℕ → ℕ → Set where
  0≠s   : ∀ {n}           → 0 ≠ (suc n)
  s≠0   : ∀ {n}           → (suc n) ≠ 0
  ≠-suc : ∀ {m n} → m ≠ n → (suc m) ≠ (suc n)

-- Alternative representation of ≤:

data _≤′_ : ℕ → ℕ → Set where
  ≤′-refl : ∀ {n}   → n ≤′ n
  ≤′-step : ∀ {m n} → m ≤′ suc n

-- different representations are good for different tasks

-- Addition predicate

data _+_≡_ : ℕ → ℕ → ℕ → Set where
  znn : ∀ {n}                 → 0 + n ≡ n
  sns : ∀ {a b c} → a + b ≡ c → (suc a) + b ≡ (suc c)

-- Exercise: Prove that 5 + 5 ≡ 10.

5+5≡10 : 5 + 5 ≡ 10
5+5≡10 = sns (sns (sns (sns (sns znn))))

-- Exercise: Prove that 2 + 2 ≠ 5.

2+2≠5 : 2 + 2 ≡ 5 → ⊥
2+2≠5 (sns (sns ()))

-- Exercise: Define _⊓_≡_ : ℕ → ℕ → ℕ → Set such that m ⊓ n ≡ k iff k is the
-- minimum of m and n.
--   Prove that both 3 ⊓ 5 ≡ 3 and 5 ⊓ 3 ≡ 3 are non-empty.
--   Prove that 3 ⊓ 5 ≡ 5 is empty.

data _⊓_≡_ : ℕ → ℕ → ℕ → Set where
  znz : ∀ {n}                 → 0 ⊓ n ≡ 0
  nzz : ∀ {n}                 → n ⊓ 0 ≡ 0
  sss : ∀ {a b c} → a ⊓ b ≡ c → suc a ⊓ suc b ≡ suc c

3⊓5≡3 : 3 ⊓ 5 ≡ 3
3⊓5≡3 = sss (sss (sss znz))

5⊓3≡3 : 5 ⊓ 3 ≡ 3
5⊓3≡3 = sss (sss (sss nzz))

3⊓5≠5 : 3 ⊓ 5 ≡ 5 → ⊥
3⊓5≠5 (sss (sss (sss ())))

-- Exercise: Define _⊔_≡_ : ℕ → ℕ → ℕ → Set such that m ⊔ n ≡ k iff k is the
-- maximum of m and n.
--   Prove that 3 ⊔ 5 ≡ 5 is non-empty.
--   Prove that 3 ⊔ 5 ≡ 3 is empty.

data _⊔_≡_ : ℕ → ℕ → ℕ → Set where
  znn : ∀ {n}                 → 0 ⊔ n ≡ n
  nzn : ∀ {n}                 → n ⊔ 0 ≡ n
  sss : ∀ {a b c} → a ⊔ b ≡ c → suc a ⊔ suc b ≡ suc c

3⊔5≡5 : 3 ⊔ 5 ≡ 5
3⊔5≡5 = sss (sss (sss znn))

3⊔5≡3 : 3 ⊔ 5 ≡ 3 → ⊥
3⊔5≡3 (sss (sss (sss ())))

-- Reusing definitions

data _≤″_ : ℕ → ℕ → Set where
  ≤+ : ∀ {m n k} → m + n ≡ k → m ≤″ k

-- Exercise: Define _isDoubleOf_ : ℕ → ℕ → Set atop _+_≡_.
--   Prove that 8 isDoubleOf 4 is non-empty.
--   Prove that 9 isDoubleOf 4 is empty.

data _isDoubleOf′_ : ℕ → ℕ → Set where
  double′ : ∀ {n k} → n + n ≡ k → k isDoubleOf′ n

8IsDoubleOf4′ : 8 isDoubleOf′ 4
8IsDoubleOf4′ = double′ (sns (sns (sns (sns znn))))

9IsntDoubleOf4′ : 9 isDoubleOf′ 4 → ⊥
9IsntDoubleOf4′ (double′ (sns (sns (sns (sns ())))))

-- Exercise: Define _*_≡_ : ℕ → ℕ → ℕ → Set with the help of _+_≡_.
--   Prove that 3 * 3 ≡ 9 is non-empty.
--   Prove that 3 * 3 ≡ 8 is empty.

data _*_≡_ : ℕ → ℕ → ℕ → Set where
  *-zero : ∀ {n}                               → 0 * n ≡ 0
  *-suc  : ∀ {a b c d} → a * b ≡ c → b + c ≡ d → (suc a) * b ≡ d

3*3≡9 : 3 * 3 ≡ 9
3*3≡9 = *-suc 2*3≡6 3+n
  where
    3+n : ∀ {n} → 3 + n ≡ suc (suc (suc n))
    3+n = sns (sns (sns znn))
    1*3≡3 = *-suc *-zero 3+n
    2*3≡6 = *-suc 1*3≡3 3+n

-- TODO: prove 3*3=8 is empty

3*3≠8 : 3 * 3 ≡ 8 → ⊥
3*3≠8 (*-suc x (sns (sns (sns znn)))) = 2*3≠5 x
  where
    -- TODO: figure out how we can use 3+n as we do above.
    1*3≠2 : 1 * 3 ≡ 2 → ⊥
    1*3≠2 (*-suc *-zero (sns (sns ())))
    2*3≠5 : 2 * 3 ≡ 5 → ⊥
    2*3≠5 (*-suc x (sns (sns (sns znn)))) = 1*3≠2 x

-- Exercise: Define _≈_ : ℕ → ℕ⁺ → Set that represents the (canonical)
-- isomorphism between ℕ and ℕ⁺.
--   Prove that 5 ≈ double+1 (double one) is non-empty.
--   Prove that 4 ≈ double+1 (double one) is empty.

-- data _≈_ : ℕ → ℕ⁺ → Set where
--   ≈-one      : suc zero ≈ one
--   ≈-two      : suc (suc zero) ≈ double one
--   ≈-double   : ∀ {n n⁺} → n ≈ double n⁺ → suc n ≈ double+1 n⁺
--   ≈-double+1 : ∀ {n n⁺} → n ≈ (double+1 n⁺) → suc n   ≈ double+1 n⁺

data _≈_ : ℕ → ℕ⁺ → Set where
  ≈-one    :                                     suc zero ≈ one
  ≈-double : ∀ {n n⁺ 2n} → n ≈ n⁺ → n + n ≡ 2n → 2n ≈ double n⁺
  ≈-+1     : ∀ {n n⁺} → n ≈ (double n⁺)        → suc n ≈ double+1 n⁺

5≈5 : 5 ≈ double+1 (double one)
5≈5 = ≈-+1 (≈-double 2≈2 2+2≡4)
  where
    1+1≡2 = sns znn
    2≈2 = ≈-double ≈-one 1+1≡2
    2+2≡4 = sns (sns znn)

4≉5 : 4 ≈ double+1 (double one) → ⊥
4≉5 (≈-+1 (≈-double _ (sns (sns (sns ())))))
