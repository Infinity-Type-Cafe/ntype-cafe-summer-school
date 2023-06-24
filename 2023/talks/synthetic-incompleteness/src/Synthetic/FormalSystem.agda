{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --hidden-argument-puns #-}

module Synthetic.FormalSystem where
open import Synthetic.PartialFunction
open import Synthetic.Definitions.Base
open import Synthetic.Definitions.Properties
open import Synthetic.Definitions.Prophood

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Equality using (eqToPath)
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff

record FormalSystem {ℓ} (Sentence : Type ℓ) (¬_ : Sentence → Sentence) : Type (ℓ-suc ℓ) where
  field
    ⊢_ : Sentence → Type
    ⊢-isPred : isPredicate ⊢_
    ⊢-semiDec : Semidecision ⊢_
    consistent : ∀ φ → ⊢ φ → ⊢ (¬ φ) → ⊥

  ⊬_ : Sentence → Type
  ⊬_ φ = ⊢ φ → ⊥

  complete : Type _
  complete = ∀ φ → ∥ (⊢ φ) ⊎ (⊢ ¬ φ) ∥₁

  independent : Type _
  independent = ∀ φ → (⊬ φ) × (⊬ ¬ φ)

  ⊢¬-semiDec : Semidecision (⊢_ ∘ ¬_)
  ⊢¬-semiDec = semiDecReduction (¬_ , (λ _ → ↔-refl)) ⊢-semiDec

  ⊢-⊢¬-sep : Separation (⊢_) (⊢_ ∘ ¬_)
  ⊢-⊢¬-sep = semiDec→sep ⊢-isPred (λ _ → ⊢-isPred _) consistent ⊢-semiDec ⊢¬-semiDec

  complete→⊢-dec : complete → decidable (⊢_)
  complete→⊢-dec compl with ⊢-⊢¬-sep
  ... | (fₚ , Hₚ) = f , H
    where
    fₚ-total : ∀ φ → defined (fₚ φ)
    fₚ-total φ = ∥₁.rec (isPropDefined (fₚ φ)) (aux φ) (compl φ) where
      aux : ∀ φ → (⊢ φ) ⊎ (⊢ ¬ φ) → defined (fₚ φ)
      aux φ (inl ⊢φ)  = Hₚ .fst φ .to ⊢φ .fst
      aux φ (inr ⊢¬φ) = Hₚ .snd φ .to ⊢¬φ .fst
    f : Sentence → Bool
    f = fst ∘ totalise fₚ fₚ-total
    fₚ≐ : (φ : Sentence) → fₚ φ ≐ f φ
    fₚ≐ = snd ∘ totalise fₚ fₚ-total
    H : f decides ⊢_
    H φ with f φ in α
    ... | true  = →: (λ _ → refl)
                  ←: (λ _ → Hₚ .fst φ .from ≐true)
      where
      ≐true : fₚ φ ≐ true
      ≐true = subst (fₚ φ ≐_) (eqToPath α) (fₚ≐ φ)
    ... | false = →: (λ ⊢φ → ≐-functional (fₚ φ) ≐false (≐true ⊢φ))
                  ←: (λ H → ⊥.rec $ false≢true H)
      where
      ≐true : ⊢ φ → fₚ φ ≐ true
      ≐true = Hₚ .fst φ .to
      ≐false : fₚ φ ≐ false
      ≐false = subst (fₚ φ ≐_) (eqToPath α) (fₚ≐ φ)

open FormalSystem using (complete; independent; complete→⊢-dec) public

private variable
  ℓ : Level
  A Sentence : Type ℓ
  ¬_ : Sentence → Sentence

_⊢_ : FormalSystem Sentence ¬_ → Sentence → Type
FS ⊢ φ = ⊢ φ where open FormalSystem FS

_⊬_ : FormalSystem Sentence ¬_ → Sentence → Type
FS ⊬ φ = ⊬_ φ where open FormalSystem FS

_⊑_ : FormalSystem Sentence ¬_ → FormalSystem Sentence ¬_ → Type _
FS₁ ⊑ FS₂ = ∀ φ → FS₁ ⊢ φ → FS₂ ⊢ φ

⊑-refl : {FS : FormalSystem Sentence ¬_} → FS ⊑ FS
⊑-refl _ = idfun _

_represents_by_ : FormalSystem Sentence ¬_ → (A → Type ℓ) → (A → Sentence) → Type _
FS represents N by fᵣ = fᵣ reducts N to (FS ⊢_)

_represents_ : FormalSystem Sentence ¬_ → (A → Type ℓ) → Type _
FS represents N = N ⪯ (FS ⊢_)

_soundFor_by_ : FormalSystem Sentence ¬_ → (A → Type ℓ) → (A → Sentence) → Type _
FS soundFor N by fᵣ = ∀ n → FS ⊢ (fᵣ n) → N n

_soundFor_ : FormalSystem Sentence ¬_ → (A → Type ℓ) → Type _
FS soundFor N = Σ _ λ fᵣ → FS soundFor N by fᵣ

private variable
  FS FS₁ FS₂ : FormalSystem Sentence ¬_
  B : A → Type ℓ
  fᵣ : A → Sentence

represent→sound : FS represents B → FS soundFor B
represent→sound (fᵣ , H) = fᵣ , λ n → H n .from

⊑-⊢dec→repr→dec : FS₁ ⊑ FS₂ → decidable (FS₂ ⊢_) → isPredicate B →
  FS₁ represents B by fᵣ → FS₂ soundFor B by fᵣ → decidable B
⊑-⊢dec→repr→dec {fᵣ} ext (fᵈ , Hᵈ) pred H₁ H₂ = fᵈ ∘ fᵣ , λ n →
  →: (λ H → Hᵈ _ .to $ ext _ $ H₁ _ .to H)
  ←: λ H → H₂ n $ Hᵈ _ .from H

⊑-com→repr→dec : FS₁ ⊑ FS₂ → complete FS₂ → isPredicate B →
  FS₁ represents B by fᵣ → FS₂ soundFor B by fᵣ → decidable B
⊑-com→repr→dec {FS₂} ext compl pred = ⊑-⊢dec→repr→dec ext (complete→⊢-dec FS₂ compl) pred

com→repr→dec : complete FS → isPredicate B → FS represents B by fᵣ → decidable B
com→repr→dec compl pred Hᵣ = ⊑-com→repr→dec ⊑-refl compl pred Hᵣ λ n → Hᵣ n .from
