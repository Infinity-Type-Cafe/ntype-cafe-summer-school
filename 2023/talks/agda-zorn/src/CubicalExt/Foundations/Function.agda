
{-# OPTIONS --cubical --safe #-}

module CubicalExt.Foundations.Function where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function public

private variable
  ℓ : Level
  A : Type ℓ
  B : A → Type ℓ
  C : (x : A) → B x → Type ℓ

------------------------------------------------------------------------
-- Some simple functions

id : A → A
id x = x

------------------------------------------------------------------------
-- Converting between implicit and explicit function spaces.

_$- : ((x : A) → B x) → ({x : A} → B x)
f $- = f _
{-# INLINE _$- #-}

_$-- : ((x : A) → (y : B x) → C x y) → ({x : A} → {y : B x} → C x y)
f $-- = f _ _
{-# INLINE _$-- #-}

λ- : ({x : A} → B x) → ((x : A) → B x)
λ- f = λ x → f
{-# INLINE λ- #-}

λ-- : ({x : A} → {y : B x} → C x y) → ((x : A) → (y : B x) → C x y)
λ-- f = λ x y → f
{-# INLINE λ-- #-}

------------------------------------------------------------------------
-- Construct an element of the given type by instance search.

it : {A : Type ℓ} → ⦃ A ⦄ → A
it ⦃ x ⦄ = x
