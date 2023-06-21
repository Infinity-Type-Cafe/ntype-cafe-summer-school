{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Synthetic.Axiom.Base
module Synthetic.Halting ((Θ , Θ-universal) : EPFᴮ) where

open import Synthetic.PartialFunction
open import Synthetic.Definitions.Base
open import Synthetic.Definitions.Properties

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import CubicalExt.Data.Bool
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff

-- halting problem by self-reference
Kᶿ : ℕ → Type
Kᶿ c = ∃ _ (Θ c c ≐_)

Kᶿ-divergent : ∀ fₚ → fₚ decidesₚ Kᶿ → ∃ _ λ c → undefined (fₚ c)
Kᶿ-divergent fₚ Hₚ = flip map (Θ-universal gₚ) λ { (c , Hc) → c ,
  λ { true fₚc≐T → ∥₁.rec isProp⊥
      (λ { (b , Θcc≐b) → true→undef fₚc≐T b (Hc c b .to Θcc≐b) })
      (Hₚ c .from fₚc≐T)
    ; false fₚc≐F → let
        fₚc≐T : fₚ c ≐ true
        fₚc≐T = Hₚ c .to ∣ true , Hc c true .from (false→true fₚc≐F) ∣₁
      in ⊥.rec $ true≢false $ ≐-functional (fₚ c) fₚc≐T fₚc≐F
    } }
  where
  gₚ : ℕ → part Bool
  gₚ n = (Σ P (T ∘ not ∘ b) , isPropΣ Pprop λ _ → isPropT _) , not ∘ b ∘ fst where
    P = ⟨ fₚ n .fst ⟩
    Pprop = str $ fₚ n .fst
    b = value (fₚ n)
  true→undef : ∀ {c} → fₚ c ≐ true → undefined (gₚ c)
  true→undef {c} (p , ≡T) b ((q , H) , _) = subst (T ∘ not) eq H where
    eq : value (fₚ c) q ≡ true
    eq = cong (value (fₚ c)) (isPropDefined (fₚ c) _ _) ∙ ≡T
  false→true : ∀ {c} → fₚ c ≐ false → gₚ c ≐ true
  false→true {c} (p , ≡F) = (p , (subst (T ∘ not) (sym ≡F) tt)) , subst (λ b → not b ≡ true) (sym ≡F) refl

Kᶿ-¬dec : ¬ decidable Kᶿ
Kᶿ-¬dec dec@(fᵈ , _) = let (fₚ , Hₚ) = dec→pDec (λ _ → squash₁) dec in
  ∥₁.rec isProp⊥ (λ (c , undef) → undef (fᵈ c) (tt* , refl)) (Kᶿ-divergent fₚ Hₚ)
