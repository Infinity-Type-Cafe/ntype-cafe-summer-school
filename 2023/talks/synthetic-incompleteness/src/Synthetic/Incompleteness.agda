{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Synthetic.Axiom.Base
open import Synthetic.FormalSystem using (FormalSystem)
module Synthetic.Incompleteness (epf : EPFᴮ)
  {ℓ} {Sentence : Type ℓ} {~_ : Sentence → Sentence}
  (FS : FormalSystem Sentence ~_) where

open import Synthetic.FormalSystem
open FormalSystem FS using (⊢_)

open import Synthetic.Definitions.Base
open import Synthetic.Halting epf

open import Cubical.Foundations.Function
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff

Gödel’sIncompleteness : FS represents Kᶿ → ¬ complete FS
Gödel’sIncompleteness repr compl = Kᶿ-¬dec $ com→repr→dec compl (λ _ → squash₁) (repr .snd)
