{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

module Synthetic.Definitions.Prophood where
open import Synthetic.PartialFunction
open import Synthetic.Definitions.Base
open import Synthetic.Definitions.DecIso using (DecIsoDecidable)
open import Synthetic.Definitions.DecIso using (isPropDecides) public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation
open import CubicalExt.Functions.Logic.Iff

private variable
  ℓ : Level
  A A' : Type ℓ
  B B₁ B₂ : A → Type ℓ
  fᵈ⁻ : A → ℕ → Bool
  fₚ : A → part Bool
  fₑ : ℕ → Maybe A
  fᵣ : A → A'

isPropDecidable : isPredicate B → isProp (decidable B)
isPropDecidable pred = subst isProp
  (isoToPath (DecIsoDecidable pred))
  (isPropΠ (λ _ → isPropDec (pred _)))

isPropDiscrete : isSet A → isProp (discrete A)
isPropDiscrete Aset = isPropDecidable λ _ → Aset _ _

isPropSemiDecides : isPredicate B → isProp (fᵈ⁻ semiDecides B)
isPropSemiDecides pred = isPropΠ (λ _ → isProp↔ (pred _) squash₁)

isPropDecidableₚ : isPredicate B → isProp (fₚ decidesₚ B)
isPropDecidableₚ {fₚ} pred = isPropΠ λ x → isProp↔ (pred _) (isProp≐ isSetBool (fₚ x) _)

isPropSeparates : isPredicate B₁ → isPredicate B₂ → isProp (fₚ separates B₁ and B₂)
isPropSeparates {fₚ} pred₁ pred₂ = isProp×
  (isPropΠ (λ x → isProp↔ (pred₁ x) (isProp≐ isSetBool (fₚ x) _)))
  (isPropΠ (λ x → isProp↔ (pred₂ x) (isProp≐ isSetBool (fₚ x) _)))

isPropEnumerates : isPredicate B → isProp (fₑ enumerates B)
isPropEnumerates pred = isPropΠ (λ _ → isProp↔ (pred _) squash₁)

isPropReducts : isPredicate B₁ → isPredicate B₂ → isProp (fᵣ reducts B₁ to B₂)
isPropReducts pred₁ pred₂ = isPropΠ λ _ → isProp↔ (pred₁ _) (pred₂ _)
