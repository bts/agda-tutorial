module Sets.Enumerated where

data Bool : Set where
  true : Bool
  false : Bool

data Answer : Set where
  yes : Answer
  no : Answer
  maybe : Answer

data Quarter : Set where
  east west north south : Quarter

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

-- Set is the type of types.
