{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive

module Basic where

data False : Set where

record True : Set where

data _||_ {a b : _} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : A → A || B
  inr : B → A || B
infix 1 _||_
