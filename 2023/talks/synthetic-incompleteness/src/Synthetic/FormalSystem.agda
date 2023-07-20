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
    consistent : ∀ φ → ⊢ φ → ⊢ ¬ φ → ⊥

  complete : Type _
  complete = ∀ φ → ∥ (⊢ φ) ⊎ (⊢ ¬ φ) ∥₁

  ⊢¬-semiDec : Semidecision (⊢_ ∘ ¬_)
  ⊢¬-semiDec = semiDecReduction (¬_ , λ x → ↔-refl) ⊢-semiDec

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

open FormalSystem using (complete; complete→⊢-dec) public

module _ {ℓₛ : Level} {Sentence : Type ℓₛ} {¬_ : Sentence → Sentence} where
  private Fml = FormalSystem Sentence ¬_

  private variable
    ℓ : Level
    A : Type ℓ
    B : A → Type ℓ
    ℱ ℱ₁ ℱ₂ : Fml
    fᵣ : A → Sentence

  _⊢_ : Fml → Sentence → Type
  ℱ ⊢ φ = ⊢ φ where open FormalSystem ℱ

  _represents⟨_⟩_ : Fml → (A → Sentence) → (A → Type ℓ) → Type _
  ℱ represents⟨ fᵣ ⟩ N = fᵣ reducts N to (ℱ ⊢_)

  _represents_ : Fml → (A → Type ℓ) → Type _
  ℱ represents N = N ⪯ (ℱ ⊢_)

  repr→dec⊢→decPred : isPredicate B → ℱ represents⟨ fᵣ ⟩ B → decidable (ℱ ⊢_) → decidable B
  repr→dec⊢→decPred {fᵣ} pred Hᵣ (fᵈ , Hᵈ) = fᵈ ∘ fᵣ , λ n →
    →: (Hᵈ _ .to   ∘ Hᵣ n .to)
    ←: (Hᵣ n .from ∘ Hᵈ _ .from)
