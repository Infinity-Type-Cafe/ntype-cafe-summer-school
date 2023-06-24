{-# OPTIONS --cubical --safe #-}

module CubicalExt.Data.Bool where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.Bool public
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary

infixr 6 _∧_
infixr 5 _∨_ _xor_

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false

_∨_ : Bool → Bool → Bool
true  ∨ b = true
false ∨ b = b

_xor_ : Bool → Bool → Bool
true  xor b = not b
false xor b = b

T : Bool → Set
T true  = Unit
T false = ⊥

isPropT : ∀ b → isProp (T b)
isPropT true = isPropUnit
isPropT false = isProp⊥

DecT : ∀ b → Dec (T b)
DecT true = yes tt
DecT false = no λ ()
