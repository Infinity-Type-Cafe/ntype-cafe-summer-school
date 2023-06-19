{-# OPTIONS --cubical --safe #-}

module CubicalExt.Functions.Logic.Iff where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels using (hProp; isProp→; isPropΣ)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; isoToPath)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Functions.Logic using (∥_∥ₚ; ⇒∶_⇐∶_)
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁; rec; map)
open import Cubical.Reflection.RecordEquiv using (declareRecordIsoΣ)

private variable
  ℓ ℓ' : Level
  A B C D : Type ℓ
  f g : A → Type ℓ
  P Q : hProp ℓ

--------------------------------------------------------------------------------
-- Bi-implication (iff) of Type (usually with a seperate proof of prop-hood)

infix 3 _↔_
record _↔_ (From : Type ℓ) (To : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    to   : From → To
    from : To → From

open _↔_ public

--------------------------------------------------------------------------------
-- Mixfix notations for iff construction

infix 9 →:_←:_ ←:_→:_

→:_←:_ : (A → B) → (B → A) → A ↔ B
→: to ←: from = record { from = from ; to = to }

←:_→:_ : (B → A) → (A → B) → A ↔ B
←: from →: to = record { from = from ; to = to }

--------------------------------------------------------------------------------
-- Iff is an equivalence relation

↔-refl : A ↔ A
↔-refl = →: idfun _ ←: idfun _

↔-sym : A ↔ B → B ↔ A
↔-sym A↔B = →: from A↔B ←: to A↔B

↔-trans : A ↔ B → B ↔ C → A ↔ C
↔-trans A↔B B↔C = →: to B↔C ∘ to A↔B ←: from A↔B ∘ from B↔C

--------------------------------------------------------------------------------
-- Interactions of iff with equality

≡-↔-trans : A ≡ B → B ↔ C → A ↔ C
≡-↔-trans A≡B B↔C = subst (_↔ _) (sym A≡B) B↔C

↔-≡-trans : A ↔ B → B ≡ C → A ↔ C
↔-≡-trans A↔B B≡C = subst (_ ↔_) B≡C A↔B

--------------------------------------------------------------------------------
-- Syntax for chains of iff reasoning

infixr 2 step-↔ step-↔˘ step-↔≡ step-↔≡˘ _↔⟨⟩_
infix  3 _↔∎

step-↔ : (A : Type ℓ) → B ↔ C → A ↔ B → A ↔ C
step-↔ _ = flip ↔-trans

syntax step-↔ A B p = A ↔⟨ p ⟩ B

step-↔˘ : (A : Type ℓ) → B ↔ C → B ↔ A → A ↔ C
step-↔˘ _ = flip (↔-trans ∘ ↔-sym)

syntax step-↔˘ A B p = A ↔˘⟨ p ⟩ B

step-↔≡ : (A : Type ℓ) → B ↔ C → A ≡ B → A ↔ C
step-↔≡ _ = flip ≡-↔-trans

syntax step-↔≡ A B p = A ↔≡⟨ p ⟩ B

step-↔≡˘ : (A : Type ℓ) → B ↔ C → B ≡ A → A ↔ C
step-↔≡˘ _ = flip (≡-↔-trans ∘ sym)

syntax step-↔≡˘ A B p = A ↔≡˘⟨ p ⟩ B

_↔⟨⟩_ : (A : Type ℓ) → A ↔ B → A ↔ B
_ ↔⟨⟩ A↔B = A↔B

_↔∎ : (A : Type ℓ) → A ↔ A
_ ↔∎ = ↔-refl

--------------------------------------------------------------------------------
-- Some congruence properties of iff

≡↔≡ : ∀ {a b c d : A} → a ≡ b → c ≡ d → (a ≡ c) ↔ (b ≡ d)
≡↔≡ a≡b c≡d = →: (λ a≡c → sym a≡b ∙ a≡c ∙ c≡d)
              ←: (λ b≡d → a≡b     ∙ b≡d ∙ sym c≡d)

→↔→ : A ↔ B → C ↔ D → (A → C) ↔ (B → D)
→↔→ A↔B C↔D = →: (λ f x → to   C↔D (f $ from A↔B x))
              ←: (λ g x → from C↔D (g $ to   A↔B x))

Π↔Π : (∀ x → f x ↔ g x) → (∀ x → f x) ↔ (∀ x → g x)
Π↔Π ↔ = →: (λ f x → to   (↔ x) $ f x)
        ←: (λ g x → from (↔ x) $ g x)

--------------------------------------------------------------------------------
-- Proof of prop-hood

unquoteDecl iffIsoΣ = declareRecordIsoΣ iffIsoΣ (quote _↔_)

isProp↔ : isProp A → isProp B → isProp (A ↔ B)
isProp↔ propA propB = subst (λ X → isProp X) (sym (isoToPath iffIsoΣ)) $
  isPropΣ (isProp→ propB) λ _ → isProp→ propA

∥∥-↔ : ∥ A ↔ B ∥₁ → ∥ A ∥₁ ↔ ∥ B ∥₁
∥∥-↔ = rec (isProp↔ squash₁ squash₁) λ iff →
  →: rec squash₁ (λ x → ∣ to   iff x ∣₁)
  ←: rec squash₁ (λ x → ∣ from iff x ∣₁)

--------------------------------------------------------------------------------
-- Propositional extensionality

hPropExt : ⟨ P ⟩ ↔ ⟨ Q ⟩ → P ≡ Q
hPropExt iff = ⇒∶ to iff ⇐∶ from iff

hPropExt⁻ : P ≡ Q → ⟨ P ⟩ ↔ ⟨ Q ⟩
hPropExt⁻ {P = P} P≡Q = subst (λ X → ⟨ P ⟩ ↔ ⟨ X ⟩) P≡Q ↔-refl

hPropTruncExt : A ↔ B → ∥ A ∥ₚ ≡ ∥ B ∥ₚ
hPropTruncExt iff = Σ≡Prop (λ _ → isPropIsProp) $ isoToPath $ iso
  (map $ to iff) (map $ from iff) (λ x → squash₁ _ x) (λ x → squash₁ _ x)
