module Sets.ParametersVsIndices where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)
open import Sets.Propositions using (_+_≡_)
open import Data.Empty using (⊥)

-- "The first index can be turned into a new parameter if each constructor has
-- the same variable on the first index position (that is, in the result type)."

-- Example 1:

data _≤′_ : ℕ → ℕ → Set where
  ≤′-refl : {m : ℕ} →                       m ≤′ m
  ≤′-step : {m : ℕ} → {n : ℕ} →  m ≤′ n  →  m ≤′ suc n

-- can become:

data _≤″_ (m : ℕ) : ℕ → Set where
  ≤″-refl :                       m ≤″ m
  ≤″-step : {n : ℕ} →  m ≤″ n  →  m ≤″ suc n

-- Example 2:

data _≤‴_ : ℕ → ℕ → Set where
  ≤+ : ∀ {m n k} → m + n ≡ k → m ≤‴ k

-- can become:

data _≤⁗_ (m : ℕ) (k : ℕ) : Set where
  ≤+ : ∀ {n} → m + n ≡ k → m ≤⁗ k

-- It is always a better to use a parameter instead of an index, because:

-- We suggest more about the structure of the set. In turn, the Agda compiler
-- can infer more properties of this set.

-- Cleaner syntax: each constructor has one parameter less.


data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

data _∈_ {A : Set} (x : A) : List A → Set where
  first : ∀ {xs} →            x ∈ x ∷ xs
  later : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

infix 4 _∈_

-- Exercise: Define _⊆_ {A : Set} : List A → List A → Set!
--  Prove that 1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ []!
--  Prove that 1 ∷ 2 ∷ 3 ∷ [] ⊆ 1 ∷ 2 ∷ [] is false!

data _⊆_ {A : Set} : List A → List A → Set where
  ⊆-base : ∀ {ys} →                             [] ⊆ ys
  ⊆-step : ∀ {xs ys a} → xs ⊆ ys → a ∈ ys → a ∷ xs ⊆ ys

infix 4 _⊆_

12⊆123 : 1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ []
12⊆123 = ⊆-step 2⊆123 first
  where
    2⊆123 = ⊆-step ⊆-base (later first)

3∉12 : 3 ∈ 1 ∷ 2 ∷ [] → ⊥
3∉12 (later (later ()))

3⊈12 : 3 ∷ [] ⊆ 1 ∷ 2 ∷ [] → ⊥
3⊈12 (⊆-step ⊆-base (later (later ())))

23⊈12 : 2 ∷ 3 ∷ [] ⊆ 1 ∷ 2 ∷ [] → ⊥
23⊈12 (⊆-step x _) = 3⊈12 x

123⊈12 : 1 ∷ 2 ∷ 3 ∷ [] ⊆ 1 ∷ 2 ∷ [] → ⊥
123⊈12 (⊆-step (⊆-step (⊆-step _ (later (later ()))) _) _)
-- instead of using _ here, we can provide multiple patterns


-- Exercise: Define a permutation predicate

data _perm_ {A : Set} (xs : List A) (ys : List A) : Set where
  id : xs ⊆ ys → ys ⊆ xs → xs perm ys

-- Exercise: Define a sort predicate

data sorted : List ℕ → Set where
  sorted-0 : sorted []
  sorted-1 : ∀ {x} → sorted (x ∷ [])
  sorted-n : ∀ {x xs a} → sorted (x ∷ xs) → a ≤ x → sorted (a ∷ x ∷ xs)
