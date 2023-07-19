{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Synthetic.FormalSystem using (FormalSystem)

module Synthetic.Incompleteness where
open import Synthetic.Definitions.Base
open import Synthetic.FormalSystem

open import Cubical.Foundations.Function
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as ∥₁

module _ {ℓ ℓ′}
  {Sentence : Type ℓ} {~_ : Sentence → Sentence} (ℱ : FormalSystem Sentence ~_)
  {K : ℕ → Type ℓ′} (predK : isPredicate K) (undec : ¬ decidable K) where

  Gödel’sIncompleteness : ℱ represents K → ¬ complete ℱ
  Gödel’sIncompleteness repr compl = undec $ com→repr→dec compl predK (repr .snd)
