{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Synthetic.Axiom.Base
module Synthetic.Halting ((Θ , Θ-universal) : EPFᴮ) where

open import Synthetic.PartialFunction
open import Synthetic.Definitions.Base
open import Synthetic.Definitions.Properties

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Equality using (eqToPath)
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff

-- halting problem by self-reference
Kᶿ : ℕ → Type
Kᶿ c = ∃ _ (Θ c c ≐_)

Kᶿ-divergent : ∀ fₚ → fₚ decidesₚ Kᶿ → ∃ _ λ c → divergent (fₚ c)
Kᶿ-divergent fₚ Hₚ = flip map (Θ-universal gₚ) λ { (c , Hc) → c ,
  λ { true fₚc≐T → ∥₁.rec isProp⊥
      (λ { (b , Θcc≐b) → true→nothing fₚc≐T (Hc c b .to Θcc≐b) })
      (Hₚ c .from fₚc≐T)
    ; false fₚc≐F → let
        fₚc≐T : fₚ c ≐ true
        fₚc≐T = Hₚ c .to ∣ true , Hc c true .from (false→true fₚc≐F) ∣₁
      in ⊥.rec $ true≢false $ ≐-proper isSetBool (fₚ c) fₚc≐T fₚc≐F
    } }
  where
  gₚ : ℕ → part Bool
  gₚ n = mkPart (eval n) (proper n) where
    eval : ℕ → ℕ → Maybe Bool
    eval n m with fₚ n .part.eval m
    ... | just true = nothing
    ... | just false = just true
    ... | nothing = nothing
    proper : ∀ n → deterministic (eval n)
    proper n {m₁} {m₂} p q with fₚ n .part.eval m₁ | fₚ n .part.eval m₂
    ... | just true  | just true  = just-inj _ _ $ (sym p) ∙ q
    ... | just false | just false = just-inj _ _ $ (sym p) ∙ q
    ... | just true  | just false = ⊥.rec $ ¬nothing≡just p
    ... | just false | just true  = ⊥.rec $ ¬nothing≡just q
    ... | nothing    | _          = ⊥.rec $ ¬nothing≡just p
    ... | _          | nothing    = ⊥.rec $ ¬nothing≡just q
  true→nothing : ∀ {c b} → fₚ c ≐ true → gₚ c ≐ b → ⊥
  true→nothing {c} {b} = rec2 isProp⊥ λ (n , Hn) (m , Hm) → aux Hn Hm where
    aux : ∀ {n m} → part.eval (fₚ c) n ≡ just true → part.eval (gₚ c) m ≡ just b → ⊥
    aux {n} {m} Hn Hm with part.eval (fₚ c) m in α
    ... | just true  = ⊥.rec $ ¬nothing≡just Hm
    ... | just false = ⊥.rec $ true≢false $ part.proper (fₚ c) Hn (eqToPath α)
    ... | nothing    = ⊥.rec $ ¬nothing≡just Hm
  false→true : ∀ {c} → fₚ c ≐ false → gₚ c ≐ true
  false→true {c} = ∥₁.rec squash₁ λ { (n , Hn) → ∣ n , aux Hn ∣₁ } where
    aux : ∀ {n} → part.eval (fₚ c) n ≡ just false → part.eval (gₚ c) n ≡ just true
    aux {n} Hn with part.eval (fₚ c) n
    ... | just true  = ⊥.rec $ true≢false $ just-inj _ _ Hn
    ... | just false = refl
    ... | nothing    = ⊥.rec $ ¬nothing≡just Hn

Kᶿ-¬dec : ¬ decidable Kᶿ
Kᶿ-¬dec dec@(fᵈ , _) = let (fₚ , Hₚ) = dec→pDec (λ _ → squash₁) dec in
  ∥₁.rec isProp⊥ (λ (c , conv) → conv (fᵈ c) ∣ 0 , refl ∣₁) (Kᶿ-divergent fₚ Hₚ)
