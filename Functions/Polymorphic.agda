module Functions.Polymorphic where

open import Data.Nat
open import Data.Unit using (⊤; tt)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

-- Exercise: Define two functions which define the isomorphism between List ⊤
-- and ℕ

fromList : List ⊤ → ℕ
fromList [] = zero
fromList (tt ∷ tts) = suc (fromList tts)

toList : ℕ → List ⊤
toList zero = []
toList (suc xs) = tt ∷ (toList xs)

-- Exercise: Show on a sheet of paper with equational reasoning that the
-- fromList function is a bijection and it preserves the _+_ and _++_ operations
-- (that is, ∀ a, b ∈ List ⊤ . fromList (a ++ b) = fromList a + fromList b).

-- fromList (as ++ bs) = fromList as + fromList bs
-- fromList ((a ∷ as′) ++ bs) = fromList as + fromList bs
-- fromList (a ∷ (as′ ++ bs)) = fromList as + fromList bs
-- suc (fromList (as′ ++ bs)) = fromList as + fromList bs
-- suc (fromList (as′ ++ bs)) = suc (fromList as′) + fromList bs
-- suc (fromList (as′ ++ bs)) = suc (fromList as′ + fromList bs)

-- Exercise: Define a Maybe set (lists with 0 or 1 elements) and head and tail
-- functions for the polymorphic List type with the help of Maybe.

data Maybe (A : Set) : Set where
  nothing :     Maybe A
  just    : A → Maybe A

head : {A : Set} → List A → Maybe A
head [] = nothing
head (x ∷ xs) = just x

tail : {A : Set} → List A → Maybe (List A)
tail [] = nothing
tail (x ∷ xs) = just xs

-- Exercise: Define the following functions on lists:

map  : {A B : Set} → (A → B)      → List A → List B -- regular map
map f []       = []
map f (x ∷ xs) = (f x) ∷ map f xs

maps : {A B : Set} → List (A → B) → List A → List B -- pairwise map
maps fs []             = []
maps [] xs             = []
maps (f ∷ fs) (x ∷ xs) = (f x) ∷ maps fs xs

-- Exercise: Define the singleton list function:

[_] : {A : Set} → A → List A
[ x ] = x ∷ []

--

id : {A : Set} → A → A
id a = a

one = id (suc zero)
one′ = id {ℕ} (suc zero)

-- Exercise: Define const

const : {A B : Set} → A → B → A
const a b = a

-- Exercise: Define flip

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b

--

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

-- Exercise: Define a function which swaps the two elements

swap : {A B : Set} → A × B → B × A
swap (x , y) = y , x

-- Exercise: Define projection functions

proj₁ : {A B : Set} → A × B → A
proj₁ (a , b) = a

proj₂ : {A B : Set} → A × B → B
proj₂ (a , b) = b

--

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

-- Exercise: Define a function which swaps the two elements

swap′ : {A B : Set} → A ⊎ B → B ⊎ A
swap′ (inj₁ a) = inj₂ a
swap′ (inj₂ b) = inj₁ b

-- Exercise: Define the eliminator function for disjoint union

[_,_] : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
[ elimA , elimB ] = λ { (inj₁ a) → elimA a
                      ; (inj₂ b) → elimB b
                      }
