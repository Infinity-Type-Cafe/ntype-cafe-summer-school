{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

module Synthetic.Axiom.Base where
open import Synthetic.PartialFunction

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import CubicalExt.Functions.Logic.Iff

private variable
  ℓ : Level
  A : Type ℓ

_[_]-reflects_ : ℕ → (ℕ → ℕ → part A) → (ℕ → part A) → Type _
c [ Θ ]-reflects f = ∀ x y → Θ c x ≐ y ↔ f x ≐ y

universal : (ℕ → ℕ → part A) → Type _
universal {A} Θ = (f : ℕ → part A) → ∃ ℕ (_[ Θ ]-reflects f)

EPFᴺ : Type _
EPFᴺ = Σ (ℕ → ℕ → part ℕ) universal

EPFᴮ : Type _
EPFᴮ = Σ (ℕ → ℕ → part Bool) universal
