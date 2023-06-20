{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
module CubicalExt.Logic.Diaconescu {ℓ} {P : Type ℓ} (Pprop : isProp P) where

open import Cubical.Foundations.Function using (_∘_; _$_)
open import Cubical.Foundations.Isomorphism using (section)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; _≟_)
open import Cubical.Data.Unit using (tt*; Unit*; isPropUnit*)
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/; squash/; []surjective; effective)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; squash₁; rec)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no; isPropDec)
open import Cubical.Relation.Binary
open import CubicalExt.Axiom.Choice
open import CubicalExt.Axiom.ExcludedMiddle
import Cubical.Data.Sum as ⊎
open BinaryRelation

_~_ : Rel Bool Bool ℓ
true  ~ true  = Unit*
false ~ false = Unit*
_     ~ _     = P

isPropValued~ : isPropValued _~_
isPropValued~ true  true  = isPropUnit*
isPropValued~ false false = isPropUnit*
isPropValued~ true  false = Pprop
isPropValued~ false true  = Pprop

isRefl~ : isRefl _~_
isRefl~ true  = tt*
isRefl~ false = tt*

isSym~ : isSym _~_
isSym~ true  true  tt* = tt*
isSym~ false false tt* = tt*
isSym~ true  false p   = p
isSym~ false true  p   = p

isTrans~ : isTrans _~_
isTrans~ true  _     true  _ _ = tt*
isTrans~ false _     false _ _ = tt*
isTrans~ true  false false p _ = p
isTrans~ false true  true  p _ = p
isTrans~ true  true  false _ p = p
isTrans~ false false true  _ p = p

isEquivRel~ : isEquivRel _~_
isEquivRel~ = equivRel isRefl~ isSym~ isTrans~

RightInverse : Type ℓ
RightInverse = Σ[ g ∈ (Bool / _~_ → Bool) ] section [_] g

RightInverse→DecP : RightInverse → Dec P
RightInverse→DecP (g , sec) with g [ true ] ≟ g [ false ]
... | yes p = yes $ effective isPropValued~ isEquivRel~ _ _ $
  sym (sec [ true ]) ∙ cong [_] p ∙ sec [ false ]
... | no ¬p = no $ ¬p ∘ cong g ∘ eq/ _ _

module _ (ac : SurjectionHasRightInverse ℓ-zero ℓ) where

  existsRightInverse : ∥ RightInverse ∥₁
  existsRightInverse = ac isSetBool squash/ []surjective

  diaconescu : Dec P
  diaconescu = rec (isPropDec Pprop) RightInverse→DecP existsRightInverse
