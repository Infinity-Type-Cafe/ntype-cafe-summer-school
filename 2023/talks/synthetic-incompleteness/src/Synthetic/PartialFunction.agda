{-# OPTIONS --cubical --safe #-}

module Synthetic.PartialFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Logic.ConstructiveEpsilon

private variable
  ℓ : Level
  A B : Type ℓ

deterministic : (A → Maybe B) → Type _
deterministic f = ∀ {n m x y} → f n ≡ just x → f m ≡ just y → x ≡ y

record part (A : Type) : Type where
  constructor mkPart
  field
    eval : ℕ → Maybe A
    proper : deterministic eval

  evalTo : A → Type
  evalTo x = ∃ _ λ k → eval k ≡ just x

  functional : isSet A → ∀ {x y} → evalTo x → evalTo y → x ≡ y
  functional Aset = rec2 (Aset _ _)
    (λ { (_ , Hn) (_ , Hm) → proper Hn Hm })

  opaque
    totalise : isSet A → ∃ _ evalTo → Σ _ evalTo
    totalise Aset xₚ = σ .snd .fst , ∣ σ .fst , σ .snd .snd ∣₁ where
      swapevalTo : ∃ _ evalTo → ∃ _ λ k → Σ _ λ x → eval k ≡ just x
      swapevalTo = ∥₁.rec squash₁ λ (x , ea) → map (λ (n , H) → n , x , H) ea
      Σ[x] : ℕ → Type
      Σ[x] n = Σ _ λ x → eval n ≡ just x
      isSetΣ[x] : ∀ n → isSet (Σ[x] n)
      isSetΣ[x] _ = isSetΣ Aset λ _ → isProp→isSet (isOfHLevelMaybe 0 (λ _ _ → Aset _ _) _ _)
      DecΣ[x] : ∀ n → Dec (Σ[x] n)
      DecΣ[x] n with eval n
      ... | nothing = no λ (_ , H) → ⊥.rec (¬nothing≡just H)
      ... | just x = yes (x , refl)
      σ : Σ _ Σ[x]
      σ = ε isSetΣ[x] DecΣ[x] (swapevalTo xₚ)

_≐_ : part A → A → Type
xₚ ≐ x = part.evalTo xₚ x

≐-proper : isSet A → (xₚ : part A) {x y : A} → xₚ ≐ x → xₚ ≐ y → x ≡ y
≐-proper Aset xₚ = rec2 (Aset _ _) λ (n , Hn) (m , Hm) → part.proper xₚ Hn Hm

convergent : part A → Type
convergent xₚ = ∃ _ (xₚ ≐_)

divergent : part A → Type
divergent xₚ = ∀ x → ¬ xₚ ≐ x

total : (eval : A → part B) → Type _
total eval = ∀ x → convergent (eval x)

totalise : (eval : A → part B) → total eval → isSet B → (∀ x → Σ _ (eval x ≐_))
totalise eval H Bset x = part.totalise (eval x) Bset (H x)

partialise : (A → B) → A → part B
partialise eval x = mkPart (λ _ → just (eval x)) (λ p q → just-inj _ _ ((sym p) ∙ q))

--------------------------------------------------------------------------------
-- sethood of part

partΣ : Type → Type
partΣ A = Σ (ℕ → Maybe A) deterministic

partΣIsoPart : Iso (partΣ A) (part A)
Iso.fun       partΣIsoPart (eval , p) = mkPart eval p
Iso.inv       partΣIsoPart xₚ = part.eval xₚ , part.proper xₚ
Iso.leftInv   partΣIsoPart a = refl
Iso.rightInv  partΣIsoPart b = refl

partΣ≡Part : partΣ A ≡ part A
partΣ≡Part = isoToPath partΣIsoPart

isSetPartΣ : isSet A → isSet (partΣ A)
isSetPartΣ Aset = isSetΣ (isSet→ (isOfHLevelMaybe 0 Aset))
  λ _ → isSetImplicitΠ λ _ → isSetImplicitΠ λ _ → isSetImplicitΠ λ _ → isSetImplicitΠ
    λ _ → isSet→ $ isSet→ $ isProp→isSet $ Aset _ _

isSetPart : isSet A → isSet (part A)
isSetPart Aset = subst isSet partΣ≡Part (isSetPartΣ Aset)
