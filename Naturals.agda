{-# OPTIONS --safe --warning=error --without-K #-}

module Naturals where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+N_ : ℕ → ℕ → ℕ
zero +N b = b
succ a +N b = succ (a +N b)
