{-# OPTIONS --cubical --safe #-}

module CubicalExt.Axiom.Choice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Surjection
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation

private variable
  ℓ ℓ' ℓ'' : Level
  A  : Type ℓ
  A' : Type ℓ'
  B : A → Type ℓ'
  P : ∀ x → B x → Type ℓ''

--------------------------------------------------
-- Definition

-- HoTT Book 2.15.7
quasiAC : (∀ x → Σ[ y ∈ B x ] P x y) → Σ[ f ∈ (∀ x → B x) ] ∀ x → P x (f x)
quasiAC H = fst ∘ H , snd ∘ H

-- HoTT Book 3.8.1
ACDep : (ℓ ℓ' ℓ'' : Level) → Type _
ACDep ℓ ℓ' ℓ'' = {A : Type ℓ} {B : A → Type ℓ'} {P : ∀ x → B x → Type ℓ''} →
  isSet A → (∀ x → isSet (B x)) → (∀ x (y : B x) → isProp (P x y)) →
  (∀ x → ∃[ y ∈ B x ] P x y) → ∃[ f ∈ (∀ x → B x) ] ∀ x → P x (f x)

ACRel : (ℓ ℓ' ℓ'' : Level) → Type _
ACRel ℓ ℓ' ℓ'' = {A : Type ℓ} {B : Type ℓ'} {P : A → B → Type ℓ''} →
  isSet A → isSet B → (∀ x y → isProp (P x y)) →
  (∀ x → ∃[ y ∈ B ] P x y) → ∃[ f ∈ (A → B) ] ∀ x → P x (f x)

-- HoTT Book 3.8.3
AC : (ℓ ℓ' : Level) → Type _
AC ℓ ℓ' = {A : Type ℓ} {B : A → Type ℓ'} → isSet A → (∀ x → isSet (B x)) →
  (∀ x → ∥ B x ∥₁) → ∥ (∀ x → B x) ∥₁

SurjectionHasRightInverse : (ℓ ℓ' : Level) → Type _
SurjectionHasRightInverse ℓ ℓ' = {A : Type ℓ} {B : Type ℓ'} {f : A → B} → isSet A → isSet B →
  isSurjection f → ∃[ g ∈ (B → A) ] section f g

--------------------------------------------------
-- Lemmas

∃→∥₁ : (∃[ x ∈ A ] ∀ (_ : A') → Unit* {ℓ}) → ∥ A ∥₁
∃→∥₁ = rec squash₁ (∣_∣₁ ∘ fst)

∥₁→∃ : ∥ A ∥₁ → ∃[ x ∈ A ] Unit* {ℓ}
∥₁→∃ = rec squash₁ (λ x → ∣ x , tt* ∣₁)

--------------------------------------------------
-- Implications

ACDep→ACRel : ACDep ℓ ℓ' ℓ'' → ACRel ℓ ℓ' ℓ''
ACDep→ACRel acDep {A} {C} Aset Bset = acDep {A} {λ _ → C} Aset (λ _ → Bset)

-- HoTT Book 3.8.2
ACDep→AC : ACDep ℓ ℓ' ℓ'' → AC ℓ ℓ'
ACDep→AC acDep Aset Bset [Bx] = ∃→∥₁ $ acDep Aset Bset (λ _ _ → isPropUnit*) $ ∥₁→∃ ∘ [Bx]

AC→ACDep : AC ℓ (ℓ-max ℓ' ℓ'') → ACDep ℓ ℓ' ℓ''
AC→ACDep ac {A} {C} {P} Aset Bset Pprop = map (quasiAC {B = C} {P = P}) ∘
  ac {B = λ x → Σ-syntax (C x) λ y → P x y} Aset λ _ → isSetΣ (Bset _) λ _ → isProp→isSet (Pprop _ _)

AC→ACRel : AC ℓ (ℓ-max ℓ' ℓ'') → ACRel ℓ ℓ' ℓ''
AC→ACRel = ACDep→ACRel ∘ AC→ACDep

ACRel→SurjectionHasRightInverse : ACRel ℓ' ℓ ℓ' → SurjectionHasRightInverse ℓ ℓ'
ACRel→SurjectionHasRightInverse acRel Aset Bset sur = acRel Bset Aset (λ _ _ → Bset _ _) sur
