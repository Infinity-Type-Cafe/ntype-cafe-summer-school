{-# OPTIONS --cubical --safe #-}

module CubicalExt.Foundations.Id where

open import Cubical.Foundations.Prelude renaming (_≡_ to _≡ₚ_)
open import Cubical.Foundations.Id public
open import Cubical.Foundations.Isomorphism using (isoToPath; iso)

path≡Id-termLevel : ∀ {ℓ} {A : Type ℓ} {x y : A} → (x ≡ₚ y) ≡ₚ (x ≡ y)
path≡Id-termLevel = isoToPath (iso pathToId idToPath idToPathToId pathToIdToPath)
