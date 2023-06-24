{-# OPTIONS --cubical --safe #-}

module Synthetic.Definitions.Properties where
open import Synthetic.PartialFunction
open import Synthetic.Definitions.Base
open import Synthetic.Definitions.Prophood

open import Cubical.Foundations.Prelude hiding (_∨_)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic using (∥_∥ₚ; ⊤)
open import Data.Nat hiding (_≟_)
open import CubicalExt.Data.Bool renaming (_≟_ to discreteBool)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe as ⁇
open import Cubical.Data.Sigma hiding (_∨_)
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Equality using (pathToEq; eqToPath) renaming (refl to reflEq)
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff
open import CubicalExt.Logic.ConstructiveEpsilon

private variable
  ℓ ℓ' : Level
  A A' : Type ℓ
  B B' : A → Type ℓ

decReduction : isPredicate B → B ⪯ B' → decidable B' → decidable B
decReduction {B = B} {B' = B'} pred (fᵣ , Hᵣ) (fᵈ , Hᵈ) =  fᵈ ∘ fᵣ , λ x →
  B x               ↔⟨ Hᵣ x ⟩
  B' (fᵣ x)         ↔⟨ Hᵈ (fᵣ x) ⟩
  fᵈ (fᵣ x) ≡ true  ↔∎

semiDecReduction : B ⪯ B' → Semidecision B' → Semidecision B
semiDecReduction {B = B} {B' = B'} (fᵣ , Hᵣ) (fᵈ , Hᵈ) = fᵈ ∘ fᵣ , λ x →
  B x                             ↔⟨ Hᵣ x ⟩
  B' (fᵣ x)                       ↔⟨ Hᵈ (fᵣ x) ⟩
  ∃ ℕ (λ n → fᵈ (fᵣ x) n ≡ true)  ↔∎

discreteℕ : discrete ℕ
discreteℕ = (λ (n , m) → n ≡ᵇ m)
          , (λ (n , m) → →: ≡→≡ᵇ ←: ≡ᵇ→≡)
  where
  ≡→≡ᵇ : {n m : ℕ} → n ≡ m → (n ≡ᵇ m) ≡ true
  ≡→≡ᵇ {n} path with pathToEq path
  ... | reflEq = ≡ᵇ-refl n where
    ≡ᵇ-refl : (n : ℕ) → (n ≡ᵇ n) ≡ true
    ≡ᵇ-refl zero = refl
    ≡ᵇ-refl (suc n) = ≡ᵇ-refl n
  ≡ᵇ→≡ : {n m : ℕ} → (n ≡ᵇ m) ≡ true → n ≡ m
  ≡ᵇ→≡ {zero} {zero} _ = refl
  ≡ᵇ→≡ {zero} {suc m} H = ⊥.rec $ false≢true H
  ≡ᵇ→≡ {suc n} {zero} H = ⊥.rec $ false≢true H
  ≡ᵇ→≡ {suc n} {suc m} H = cong suc (≡ᵇ→≡ H)

enum→semiDec : {B : A → Type ℓ} → discrete A → Enumeration B → Semidecision B
enum→semiDec {_} {A} (fᵈ , Hᵈ) (fₑ , Hₑ) =
  fᵈ⁻ , λ x → ↔-trans (Hₑ x) $
    →: map (λ (n , H) → n , subst (λ x → ⁇.rec _ _ x ≡ _) (sym H) (≡→≟ x))
    ←: map (λ (n , H) → n , ≟→≡ x (fₑ n) H)
  where
  _≟_ : A → Maybe A → Bool
  _≟_ x = ⁇.rec false (λ y → fᵈ (x , y))
  ≡→≟ : ∀ x → x ≟ just x ≡ true
  ≡→≟ x = Hᵈ _ .to refl
  ≟→≡ : ∀ x x? → x ≟ x? ≡ true → x? ≡ just x
  ≟→≡ x nothing H = ⊥.rec $ false≢true H
  ≟→≡ x (just _) H = cong just $ sym $ Hᵈ _ .from H
  fᵈ⁻ : A → ℕ → Bool
  fᵈ⁻ x n = x ≟ fₑ n

semiDec→sep : {B₁ : A → Type ℓ} {B₂ : A → Type ℓ'} →
  isPredicate B₁ → isPredicate B₂ → (∀ x → B₁ x → B₂ x → ⊥.⊥) →
  Semidecision B₁ → Semidecision B₂ → Separation B₁ B₂
semiDec→sep {_} {A} {_} {_} {B₁} {B₂} pred₁ pred₂ disjoint (f , Hf) (g , Hg) =
  fₚ , (λ x → →: H₁ x ←: H₃ x), (λ x → →: H₂ x ←: H₄ x)
  where
  P : A → Type
  P x = (Σ ℕ λ n → f x n ≡ true) ⊎ (Σ ℕ λ n → g x n ≡ true)
  fₚ : A → Part Bool
  fₚ x = ∥ P x ∥ₚ , rec→Set isSetBool eval 2const where
    eval : P x → Bool
    eval (inl _) = true
    eval (inr _) = false
    2const : 2-Constant eval
    2const (inl _) (_⊎_.inl _) = refl
    2const (inr _) (_⊎_.inr _) = refl
    2const (inl p) (_⊎_.inr q) = ⊥.rec (disjoint x (Hf x .from ∣ p ∣₁) (Hg x .from ∣ q ∣₁))
    2const (inr p) (_⊎_.inl q) = ⊥.rec (disjoint x (Hf x .from ∣ q ∣₁) (Hg x .from ∣ p ∣₁))
  H₁ : ∀ x → B₁ x → fₚ x ≐ true
  H₁ x B₁x = ∣ inl $ ε (λ _ → isProp→isSet (isSetBool _ _)) (λ _ → discreteBool _ _) (Hf x .to B₁x) ∣₁ , refl
  H₂ : ∀ x → B₂ x → fₚ x ≐ false
  H₂ x B₂x = ∣ inr $ ε (λ _ → isProp→isSet (isSetBool _ _)) (λ _ → discreteBool _ _) (Hg x .to B₂x) ∣₁ , refl
  H₃ : ∀ x → fₚ x ≐ true → B₁ x
  H₃ x (def , val) = ∥₁.rec (pred₁ _) (λ p → aux p (cong (value (fₚ x)) (squash₁ ∣ p ∣₁ def) ∙ val)) def where
    aux : (p : P x) → value (fₚ x) ∣ p ∣₁ ≡ true → B₁ x
    aux (inl p) H = Hf x .from ∣ p ∣₁
    aux (inr p) H = ⊥.rec $ false≢true H
  H₄ : ∀ x → fₚ x ≐ false → B₂ x
  H₄ x (def , val) = ∥₁.rec (pred₂ _) (λ p → aux p (cong (value (fₚ x)) (squash₁ ∣ p ∣₁ def) ∙ val)) def where
    aux : (p : P x) → value (fₚ x) ∣ p ∣₁ ≡ false → B₂ x
    aux (inl p) H = ⊥.rec $ true≢false H
    aux (inr p) H = Hg x .from ∣ p ∣₁
