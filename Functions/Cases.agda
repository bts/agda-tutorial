module Functions.Cases where

open import Sets.Enumerated using (Bool; true; false)

not : Bool → Bool
not true = false
not false = true

-- functions have /computational content/ -- `not` defines not just a relation
-- between Bool and Bool, but also an algorithm how to compute the negated value

_∧_ : Bool → Bool → Bool
true  ∧ x = x
false ∧ _ = false

infixr 6 _∧_

-- Exercise: Define logical OR

_∨_ : Bool → Bool → Bool
true  ∨ _ = true
false ∨ x = x

-- Exercise: Define logical OR with one case, using `not` and `_∧_`

_∨′_ : Bool → Bool → Bool
x ∨′ y = not (not x ∧ not y)

-- Exercise: Define a set named Answer with three elements, yes, no, and maybe
--   Define logical operations on Answer

data Answer : Set where
  yes no maybe : Answer

_and_ : Answer → Answer → Answer
yes and yes = yes
no and no = no
_ and _ = maybe

_or_ : Answer → Answer → Answer
yes or _ = yes
_ or yes = yes
maybe or _ = maybe
_ or maybe = maybe
no or no = no

not′ : Answer → Answer
not′ yes = no
not′ no = yes
not′ maybe = maybe

-- Exercise: Define a set named Quarter with four elements, east, west, north and south.
--   Define a function turnLeft : Quarter → Quarter.
--   Define the functions turnBack and turnRight with the help of turnLeft! (By either pattern matching or defining a specific function composition function.)

data Quarter : Set where
  east west north south : Quarter

turnLeft : Quarter → Quarter
turnLeft north = west
turnLeft west = south
turnLeft south = east
turnLeft east = north

turnBack : Quarter → Quarter
turnBack x = turnLeft (turnLeft x)

turnRight : Quarter → Quarter
turnRight x = turnBack (turnLeft x)
