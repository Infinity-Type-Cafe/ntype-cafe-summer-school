---
title: 偏函数
---

# 偏函数

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

module Synthetic.PartialFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import CubicalExt.Functions.Logic using (⊤; ⊥)
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥ using (rec)
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Equality using (eqToPath)
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as ∥₁

private variable
  ℓ ℓ' : Level
  A B : Type ℓ
```

传统数学广泛使用偏函数, 本讲亦是如此. 由于类型论中的函数默认是全函数, 这就要求我们首先要定义什么是偏函数. 实现这一目标的方法众多, 我们采用与泛等基础比较兼容的方法, 使偏函数的主要性质和相关构造不依赖于目标类型的同伦层级.

## 偏函数的定义

对任意类型 `A`, 我们定义一个偏类型 `Part A`. 而 `A` 到 `B` 的偏函数则写作 `A → Part B`.

```agda
Part : Type ℓ → Type _
```

偏类型 `Part A` 的项 (以下称偏元素) 是一个二元组 `(P , f)`, 其中 `P` 是一个命题, 而 `f` 是一个函数, 它接受 `P` 的证明, 并返回一个 `A` 的元素. 由于 `P` 是一个命题, 所以 `P` 的证明是唯一的, 从而 `f` 的返回值也是唯一的.

```agda
Part A = Σ (hProp ℓ-zero) λ P → ⟨ P ⟩ → A
```

我们说偏元素有定义, 当且仅当二元组中的那个 `P` 成立.

```agda
defined : Part A → Type _
defined (P , _) = ⟨ P ⟩
```

"有定义"是一个谓词, 因为 `P` 是命题.

```agda
isPropDefined : (x : Part A) → isProp (defined x)
isPropDefined (P , _) = str P
```

如果偏元素有定义, 我们就可以拿到定义值.

```agda
value : (xₚ : Part A) → defined xₚ → A
value (_ , f) H = f H
```

## 偏类型单子

以下三项表明 `Part` 是一个单子, 这从另一个角度说明了我们的定义是恰当的. 不理解这一点也不影响后续内容的理解.

```agda
∅ : Part A
∅ = ⊥ , λ ()

return : A → Part A
return x = ⊤ , λ _ → x

_>>=_ : Part A → (A → Part B) → Part B
(P , f) >>= g = (Σ ⟨ P ⟩ (defined ∘ g ∘ f) , isPropΣ (str P) (isPropDefined ∘ g ∘ f)) ,
  uncurry λ p def → value (g (f p)) def
```

## 定义值的判别

我们说偏元素 `xₚ` "等于" `x` (记作 `xₚ ≐ x`), 当且仅当 `xₚ` 有定义, 且 `xₚ` 的定义值等于 `x`.

```agda
_≐_ : Part A → A → Type _
xₚ ≐ x = Σ (defined xₚ) λ H → value xₚ H ≡ x
```

`≐` 还有一种等价定义但不方便处理.

```agda
_≐'_ : Part A → A → Type _
xₚ ≐' x = xₚ ≡ return x
```

可以证明 `≐` 是一个具有函数性的关系.

```agda
≐-functional : (xₚ : Part A) {x y : A} → xₚ ≐ x → xₚ ≐ y → x ≡ y
≐-functional (P , f) (p , fp≡x) (q , fq≡y) = sym fp≡x ∙ (cong f (str P p q)) ∙ fq≡y
```

我们说一个偏元素是未定义的, 当且仅当对任意元素 `x` 都不满足 `xₚ ≐ x`.

```agda
undefined : Part A → Type _
undefined xₚ = ∀ x → ¬ xₚ ≐ x
```

## 定义域与值域

```agda
module _ (f : A → Part B) where

  domain : A → Type _
  domain x = defined (f x)

  range : B → Type _
  range y = ∃ A λ x → f x ≐ y
```

## 与全函数的相互转化

给定偏函数 `f : A → Part B`, 我们说它是全的, 当且仅当任意 `f x` 都有定义.

```agda
total : (A → Part B) → Type _
total f = ∀ x → defined (f x)
```

我们可以把一个全的偏函数转化为全函数.

```agda
totalise : (f : A → Part B) → total f → (∀ x → Σ _ (f x ≐_))
totalise f H x = value (f x) (H x) , H x , refl
```

反过来, 任意全函数都可以转化为全的偏函数.

```agda
partialise : (A → B) → A → Part B
partialise f x = return (f x)

total-partialise : (f : A → B) → total (partialise f)
total-partialise _ _ = tt*
```

## 偏类型的同伦层级

偏类型与基底类型具有相同的同伦层级, 且至少是集合.

```agda
isOfHLevelPart : ∀ n → isOfHLevel (suc (suc n)) A → isOfHLevel (suc (suc n)) (Part A)
isOfHLevelPart n lA = isOfHLevelΣ (suc (suc n))
  (isOfHLevelPlus' 2 isSetHProp) λ _ → isOfHLevelΠ (suc (suc n)) λ _ → lA

isSetPart : isSet A → isSet (Part A)
isSetPart = isOfHLevelPart 0
```

`≐` 的同伦层级比基底类型低一级. 如果基底类型是集合, 那么 `≐` 是命题.

```agda
isOfHLevel≐ : ∀ n → isOfHLevel (suc (suc n)) A → (xₚ : Part A) (x : A) → isOfHLevel (suc n) (xₚ ≐ x)
isOfHLevel≐ n lA (P , f) x = isOfHLevelΣ (suc n)
  (isOfHLevelPlus' 1 (str P)) λ _ → lA _ _

isProp≐ : isSet A → (xₚ : Part A) (x : A) → isProp (xₚ ≐ x)
isProp≐ = isOfHLevel≐ 0
```
