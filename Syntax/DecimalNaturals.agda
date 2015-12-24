module Syntax.DecimalNaturals where

data ℕ : Set where
  zero :     ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
