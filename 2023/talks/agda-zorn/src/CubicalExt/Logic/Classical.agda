{-# OPTIONS --cubical --safe #-}

open import CubicalExt.Axiom.ExcludedMiddle
module CubicalExt.Logic.Classical ⦃ em : ∀ {ℓ} → EM ℓ ⦄ where

open import Cubical.Foundations.Prelude hiding (_∨_; _∧_)
open import Cubical.Foundations.Function using (_∘_; _$_)
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Foundations.Isomorphism using (Iso; iso; _Iso⟨_⟩_; _∎Iso; invIso)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import CubicalExt.Functions.Logic using (_∨_; inl; inr; _∧_; ⊤; ⊥)
open import CubicalExt.Functions.Logic.Iff using (hPropExt; →:_←:_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit using (tt*)
import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma using (∃-syntax)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁)
open import CubicalExt.Relation.Nullary

private variable
  ℓ ℓ' : Level
  A : Type ℓ
  B : A → Type ℓ
  P Q : hProp ℓ

isSet→Discrete : isSet A → Discrete A
isSet→Discrete Aset x y = em ⦃ Aset x y _ _ ⦄

isSet→DiscreteEq : isSet A → DiscreteEq A
isSet→DiscreteEq = Discrete→DiscreteEq ∘ isSet→Discrete

hPropIsoBool : ∀ ℓ → Iso (hProp ℓ) Bool
hPropIsoBool ℓ = iso to from to∘from from∘to where
  to : (hProp ℓ) → Bool
  to P with em ⦃ P .snd _ _ ⦄
  ... | yes _ = true
  ... | no  _ = false

  from : Bool → (hProp ℓ)
  from true = ⊤
  from false = ⊥

  to∘from : (b : Bool) → to (from b) ≡ b
  to∘from true  with em {ℓ} ⦃ ⊤ .snd _ _ ⦄
  ... | yes _ = refl
  ... | no ¬p = ⊥.rec $ ¬p tt*
  to∘from false with em {ℓ} ⦃ ⊥ .snd _ _ ⦄
  ... | no  _ = refl

  from∘to : (P : hProp ℓ) → from (to P) ≡ P
  from∘to P with em ⦃ P .snd _ _ ⦄
  ... | yes p = hPropExt $ →: (λ _ → p) ←: (λ _ → tt*)
  ... | no ¬p = hPropExt $ →: (λ ()) ←: (λ p → lift $ ¬p p)

impredicativity : Iso (hProp ℓ) (hProp ℓ-zero)
impredicativity {ℓ} = hProp ℓ Iso⟨ hPropIsoBool ℓ ⟩ Bool
  Iso⟨ invIso $ hPropIsoBool ℓ-zero ⟩ hProp ℓ-zero ∎Iso

abstract
  Resize : hProp ℓ → hProp ℓ-zero
  Resize = impredicativity .Iso.fun

  resize : ⟨ P ⟩ → ⟨ Resize P ⟩
  resize {P = P} p with em ⦃ P .snd _ _ ⦄
  ... | yes _ = tt*
  ... | no ¬p = lift $ ¬p p

  unresize : ⟨ Resize P ⟩ → ⟨ P ⟩
  unresize {P = P} _ with em ⦃ P .snd _ _ ⦄
  ... | yes p = p

module _ ⦃ Aprop : isPropImplicit A ⦄ where

  byContra : (¬ ¬ A) → A
  byContra ¬A⇒⊥ with em ⦃ Aprop ⦄
  ... | yes p = p
  ... | no ¬p = ⊥.rec (¬A⇒⊥ ¬p)

  byContra* : (¬ A → ⊥.⊥* {ℓ}) → A
  byContra* ¬A⇒⊥ with em ⦃ Aprop ⦄
  ... | yes p = p
  ... | no ¬p = ⊥.rec* (¬A⇒⊥ ¬p)

module _ (A : Type ℓ) ⦃ Aprop : isPropImplicit A ⦄ (B : Type ℓ') ⦃ Bprop : isPropImplicit B ⦄ where

  ¬→→∧ : ¬ (A → B) → A ∧ ¬ B
  ¬→→∧ ¬→ = (byContra λ ¬a → ¬→ λ a → ⊥.rec $ ¬a a) , (λ b → ¬→ λ _ → b)

  ¬∧-demorgen : ¬ (A ∧ B) → (¬ A) ∨ (¬ B)
  ¬∧-demorgen ¬∧ with em {P = A} | em {P = B}
  ... | yes a | yes b = ⊥.rec $ ¬∧ (a , b)
  ... | yes a | no ¬b = inr ¬b
  ... | no ¬a | _     = inl ¬a

module _ ⦃ Pprop : {x : A} → isPropImplicit (B x) ⦄ where

  ¬∀→∃¬ : (¬ ∀ x → B x) → ∃[ x ∈ A ] ¬ B x
  ¬∀→∃¬ ¬∀xBx = byContra ⦃ squash₁ _ _ ⦄ λ ¬∃x¬Bx → ¬∀xBx λ x → byContra λ ¬Bx → ¬∃x¬Bx ∣ x , ¬Bx ∣₁
