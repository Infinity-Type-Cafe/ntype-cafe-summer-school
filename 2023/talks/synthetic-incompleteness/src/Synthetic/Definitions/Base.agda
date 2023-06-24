{-# OPTIONS --cubical --safe #-}

module Synthetic.Definitions.Base where
open import Synthetic.PartialFunction

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import CubicalExt.Functions.Logic.Iff

private variable
  ℓ ℓ' : Level
  A A' : Type ℓ

isPredicate : (A → Type ℓ) → Type _
isPredicate B = ∀ x → isProp (B x)

_decides_ : (A → Bool) → (A → Type ℓ) → Type _
fᵈ decides B = ∀ x → B x ↔ fᵈ x ≡ true

decidable : (A → Type ℓ) → Type _
decidable B = Σ _ (_decides B)

discrete : Type ℓ → Type _
discrete A = decidable {A = A × A} λ (x , y) → x ≡ y

_semidecides_ : (A → ℕ → Bool) → (A → Type ℓ) → Type _
fᵈ⁻ semidecides B = ∀ x → B x ↔ ∃ _ λ n → fᵈ⁻ x n ≡ true

Semidecision : (A → Type ℓ) → Type _
Semidecision B = Σ _ (_semidecides B)

semidecidable : (A → Type ℓ) → Type _
semidecidable B = ∥ Semidecision B ∥₁

_decidesₚ_ : (A → Part Bool) → (A → Type ℓ) → Type _
fₚ decidesₚ B = ∀ x → B x ↔ fₚ x ≐ true

_decidesₚ⁰_ : (A → Part Bool) → (A → Type ℓ) → Type _
fₚ decidesₚ⁰ B = ∀ x → B x ↔ fₚ x ≐ false

_separates_and_ : (A → Part Bool) → (A → Type ℓ) → (A → Type ℓ') → Type _
fₚ separates B₁ and B₂ = fₚ decidesₚ B₁ × fₚ decidesₚ⁰ B₂

Separation : (A → Type ℓ) → (A → Type ℓ') → Type _
Separation B₁ B₂ = Σ _ (_separates B₁ and B₂)

separatable : (A → Type ℓ) → (A → Type ℓ') → Type _
separatable B₁ B₂ = ∥ Separation B₁ B₂ ∥₁

_enumerates_ : (ℕ → Maybe A) → (A → Type ℓ) → Type _
fₑ enumerates B = ∀ x → B x ↔ ∃ _ λ n → fₑ n ≡ just x

Enumeration : (A → Type ℓ) → Type _
Enumeration B = Σ _ (_enumerates B)

enumerable : (A → Type ℓ) → Type _
enumerable B = ∥ Enumeration B ∥₁

_reducts_to_ : (fᵣ : A → A') (B : A → Type ℓ) → (B' : A' → Type ℓ') → Type _
fᵣ reducts B to B' = ∀ x → B x ↔ B' (fᵣ x)

_⪯_ : (A → Type ℓ) → (A' → Type ℓ') → Type _
B ⪯ B' = Σ _ (_reducts B to B')
