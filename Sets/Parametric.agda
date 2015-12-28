module Sets.Parametric where

open import Data.Nat
open import Data.Bool

-- Parametric List

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

-- Exercise: What is the connection between List ⊤ and ℕ?
-- They're isomorphic.

-- Exercise: Define a Maybe set (lists with 0 or 1 elements)!
data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

-- Exercise: Define parametric trees (various sorts)!
data BinTree (A : Set) : Set where
  node : A → BinTree A → BinTree A → BinTree A
  leaf : BinTree A

data Tree (A : Set) : Set where
  node : A → List (Tree A) -> Tree A
  leaf : Tree A

-- Cartesian Product

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

-- Exercise: How many elements are there in ⊤ × ⊤, ⊤ × ⊥, ⊥ × ⊤ and ⊥ × ⊥?
-- 1, 0, 0, 0

-- Exercise: How should we define Top so that ∀ A : Set. Top × A would be isomorphic to A (neutral element of _×_)?
data Top : Set where
  tt : Top

-- Disjoint Union (Sum)

data _⨄_ (A B : Set) : Set where
  inj₁ : A → A ⨄ B
  inj₂ : B → A ⨄ B

infixr 1 _⨄_

-- Exercise: What are the elements of Bool ⊎ ⊤?
-- inj₁ true; inj₁ false; inj₂ tt

-- Exercise: What are the elements of ⊤ ⊎ (⊤ ⊎ ⊤)?
-- inj₁ tt; inj₂ (inj₁ tt); inj₂ (inj₂ tt)

-- Exercise: Name an already learned isomorphic type to ⊤ ⊎ ⊤!
-- Bool

-- Exercise: How should we define Bottom so that ∀ A : Set. Bottom ⊎ A would be isomorphic to A (Neutral element of _⊎_)?
data Bottom : Set where

-- Exercise: Give an isomorphic definition of Maybe A with the help of _⊎_ and ⊤!
-- A ⨄ ⊤

-- Mutually-recursive sets

data List₁ (A B : Set) : Set
data List₂ (A B : Set) : Set

data List₁ (A B : Set) where
  []  :                 List₁ A B
  _∷_ : A → List₂ A B → List₁ A B

data List₂ (A B : Set) where
  _∷_ : B → List₁ A B → List₂ A B

-- Exercise: list the smallest first 5 elements of List₁ ⊤ Bool!
--   []
--   tt ∷ true ∷ []
--   tt ∷ false ∷ []
--   tt ∷ true ∷ tt ∷ true ∷ []
--   tt ∷ true ∷ tt ∷ false ∷ []

-- Non-regular recursive set

data AlterList (A B : Set) : Set where
  []  :                     AlterList A B
  _∷_ : A → AlterList B A → AlterList A B

-- Exercise: List the first smallest 4 (+4) elements of (AlterList ⊤ Bool) and (AlterList Bool ⊤)

-- For (AlterList ⊤ Bool):
--   []
--   ⊤ ∷ []
--   ⊤ ∷ []
--   ⊤ ∷ false ∷ []

-- For (AlterList Bool ⊤):
--   []
--   false ∷ []
--   true ∷ []
--   false ∷ tt ∷ []

-- Nested set

data T4 (A : Set) : Set where
  quad : A → A → A → A → T4 A

data Square (A : Set) : Set where
  zero :             A → Square A -- 2^0 rows
  suc  : Square (T4 A) → Square A -- 2^(n+1) rows

-- "Nested sets are special non-regular sets."
-- "Nested sets can be translated to mutually recursive regular sets."
