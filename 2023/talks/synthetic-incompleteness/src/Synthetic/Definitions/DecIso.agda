{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

module Synthetic.Definitions.DecIso where
open import Synthetic.PartialFunction
open import Synthetic.Definitions.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Equality using (eqToPath)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Relation.Nullary
open import CubicalExt.Functions.Logic.Iff

module _ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} (pred : isPredicate B) where

  isPropDecides : {f : A → Bool} → isPredicate B → isProp (f decides B)
  isPropDecides pred = isPropΠ λ _ → isProp↔ (pred _) (isSetBool _ _)

  Dec→decidable : (∀ x → Dec (B x)) → decidable B
  Dec→decidable dec = f , H where
    f : A → Bool
    f x with dec x
    ... | yes p = true
    ... | no ¬p = false
    H : f decides B
    H x with dec x
    ... | yes p = →: (λ _ → refl) ←: λ _ → p
    ... | no ¬p = →: (λ p → ⊥.rec $ ¬p p) ←: λ H → ⊥.rec $ false≢true H

  decidable→Dec : decidable B → (∀ x → Dec (B x))
  decidable→Dec (f , H) x with f x in α
  ... | true  = yes $ H x .from $ eqToPath α
  ... | false = no $ λ p → ⊥.rec $ false≢true $ sym (eqToPath α) ∙ H x .to p

  decidable→Dec→Dec : retract Dec→decidable decidable→Dec
  decidable→Dec→Dec dec = funExt aux where
    aux : (x : A) → decidable→Dec (Dec→decidable dec) x ≡ dec x
    aux x with decidable→Dec (Dec→decidable dec) x
    ... | yes p with dec x
    ... | yes q = cong yes $ pred x p q
    ... | no ¬q = ⊥.rec $ ¬q p
    aux x | no ¬p with dec x
    ... | yes q = ⊥.rec $ ¬p q
    ... | no ¬q = cong no $ isProp→ isProp⊥ ¬p ¬q

  Dec→decidable→Dec : section Dec→decidable decidable→Dec
  Dec→decidable→Dec (f , H) = ΣPathP $ funExt aux , isProp→PathP (λ _ → isPropDecides pred) _ _ where
    dec : decidable _
    dec = Dec→decidable $ decidable→Dec (f , H)
    aux : (x : A) → fst dec x ≡ f x
    aux x with fst dec x | snd dec x
    ... | true  | iff = sym $ H x .to $ iff .from refl
    ... | false | iff with f x in α
    ... | true  = iff .to $ H x .from (eqToPath α)
    ... | false = refl

  DecIsoDecidable : Iso (∀ x → Dec (B x)) (decidable B)
  Iso.fun       DecIsoDecidable = Dec→decidable
  Iso.inv       DecIsoDecidable = decidable→Dec
  Iso.leftInv   DecIsoDecidable = decidable→Dec→Dec
  Iso.rightInv  DecIsoDecidable = Dec→decidable→Dec
