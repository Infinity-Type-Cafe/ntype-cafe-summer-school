```agda
module plfa.part1.NegationLecture where
```

## Imports

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import plfa.part1.IsomorphismLecture
open import plfa.part1.ConnectivesLecture using (extensionality)
```

## 否定

```agda
¬_ : Set → Set
¬ A = A → ⊥
```

```agda
¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x
```

```agda
infix 3 ¬_
```

```agda
¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro a ¬a = ¬a a
```

我们无法证明 `¬ ¬ A` 蕴涵 `A`，但可以证明 `¬ ¬ ¬ A` 蕴涵 `¬ A`：

```agda
¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x = λ x → ¬¬¬x (¬¬-intro x)
```

另一个逻辑规则是**换质换位律（contraposition）**，它陈述了若 `A` 蕴涵 `B`，
则 `¬ B` 蕴涵 `¬ A`：

```agda
contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)
```

```agda
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  = (x ≡ y) → ⊥
```

要证明不同的数不相等很简单：

```agda
_ : 1 ≢ 2
_ = λ()
```

这是我们第一次在 λ-表达式中使用谬模式（Absurd Pattern）。类型 `M ≡ N`
只有在 `M` 和 `N` 可被化简为相同的项时才能居留。由于 `1` 和 `2`
会化简为不同的正规形式，因此 Agda 判定没有证据可证明 `1 ≡ 2`。
第二个例子是，很容易验证皮亚诺公理中「零不是任何数的后继数」的假设：

```agda
peano : ∀ {m : ℕ} → zero ≢ suc m
peano ()
```

确实，只有一个 `⊥ → ⊥` 的证明。我们可以用两种方式写出此证明：

```agda
id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()
```

不过使用外延性，我们可以证明二者相等：

```agda
id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())
```

```agda
assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))
```

## 排中律是不可辩驳的

```agda
em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable ¬[A⊎¬A] = ¬[A⊎¬A] (inj₂ (λ a → ¬[A⊎¬A] (inj₁ a)))
```

下面的故事说明了我们创建的项的行为。

曾经有一个恶魔向一个男人提议：「
要么 (a) 我给你 10 亿美元
要么 (b) 如果你付给我 10 亿美元，我可以实现你的任何一个愿望
当然，得是我决定提供 (a) 还是 (b)。」

男人很谨慎。他需要付出他的灵魂吗？
恶魔说不用，他只要接受这个提议就行。

于是男人思索着，如果恶魔向他提供 (b)，那么他不太可能付得起这个愿望。
不过倘若真是如此的话，能有什么坏处吗？

「我接受」，男人回答道，「我能得到 (a) 还是 (b)？」

恶魔顿了顿。「我提供 (b)。」

男人很失望，但并不惊讶。「果然是这样」，他想。
但是这个提议折磨着他。想想他都能用这个愿望做些什么！
多年以后，男人开始积累钱财。为了得到这笔钱，他有时会做坏事，
而且他隐约意识到这一定是魔鬼所想到的。最后他攒够了 10 亿美元，恶魔再次出现了。

「这是 10 亿美元」，男人说着，交出一个手提箱。「实现我的愿望吧！」

恶魔接过了手提箱。然后他说道，「哦？我之前说的是 (b) 吗？抱歉，我说的是 (a)。
很高兴能给你 10 亿美元。」

于是恶魔将那个手提箱又还给了他。

```agda
postulate
  em : ∀ {A : Set} → A ⊎ ¬ A
```

## 标准库

```agda
import Relation.Nullary using (¬_)
import Relation.Nullary.Negation using (contraposition)
```

## Unicode

    ¬  U+00AC  否定符号 (\neg)
    ≢  U+2262  不等价于 (\==n)
