{-# OPTIONS --cubical --safe #-}

module CubicalExt.Relation.Nullary where

open import Cubical.Foundations.Prelude hiding (_≡_)
open import Cubical.Data.Equality
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Relation.Nullary public

private variable
  ℓ : Level
  A : Type ℓ

DiscreteEq : Type ℓ → Type ℓ
DiscreteEq A = (x y : A) → Dec (x ≡ y)

DiscreteEq→Discrete : DiscreteEq A → Discrete A
DiscreteEq→Discrete Adis x y with Adis x y
... | yes p = yes (eqToPath p)
... | no ¬p = no λ q → ¬p (pathToEq q)

Discrete→DiscreteEq : Discrete A → DiscreteEq A
Discrete→DiscreteEq Adis x y with Adis x y
... | yes p = yes (pathToEq p)
... | no ¬p = no λ q → ¬p (eqToPath q)

DiscreteEq→isSet : DiscreteEq A → isSet A
DiscreteEq→isSet = Discrete→isSet ∘ DiscreteEq→Discrete
