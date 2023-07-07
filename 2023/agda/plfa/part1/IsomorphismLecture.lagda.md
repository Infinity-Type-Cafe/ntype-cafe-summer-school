```agda
module plfa.part1.IsomorphismLecture where
```

## 导入

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
```

## 函数组合 （Function Composition）

```agda
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

import Function using (_∘_)
```

## 同构（Isomorphism）

```agda
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_
```

  1. 从 `A` 到 `B` 的函数 `to`
  2. 从 `B` 回到 `A` 的函数 `from`
  3. `from` 是 `to` 的**左逆（left-inverse）**的证明 `from∘to`
  4. `from` 是 `to` 的**右逆（right-inverse）**的证明 `to∘from`

这是我们第一次使用**记录（Record）**。记录声明的行为类似于一个单构造子的数据声明

```agda
data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g
```

我们用下面的语法来构造一个记录类型的值：

    record
      { to    = f
      ; from  = g
      ; from∘to = g∘f
      ; to∘from = f∘g
      }

这与使用相应的归纳类型的构造子对应：

    mk-≃′ f g g∘f f∘g

其中 `f`、`g`、`g∘f` 和 `f∘g` 是相应类型的值。


## 同构是一个等价关系

等价关系:自反、对称、传递

```agda
≃-refl : ∀ {A : Set}
    -----
  → A ≃ A
≃-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{y → refl}
    }
```

```agda
≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A
≃-sym A≃B =
  record
    { to      = from A≃B
    ; from    = to   A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }
```

```agda
≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans A≃B B≃C =
  record
    { to       = to   B≃C ∘ to   A≃B
    ; from     = from A≃B ∘ from B≃C
    ; from∘to  = λ{x →
        begin
          (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
        ≡⟨⟩
          from A≃B (from B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
          from A≃B (to A≃B x)
        ≡⟨ from∘to A≃B x ⟩
          x
        ∎}
    ; to∘from = λ{y →
        begin
          (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
        ≡⟨⟩
          to B≃C (to A≃B (from A≃B (from B≃C y)))
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
          to B≃C (from B≃C y)
        ≡⟨ to∘from B≃C y ⟩
          y
        ∎}
     }
```

## 同构的相等性论证

```agda
module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning
```

## 标准库

标准库中可以找到与本章节中相似的定义：

```agda
import Function using (_∘_)
import Function.Inverse using (_↔_)
import Function.LeftInverse using (_↞_)
```

标准库中的 `_↔_` 和 `_↞_` 分别对应了我们定义的 `_≃_` 和 `_≲_`，
但是标准库中的定义使用起来不如我们的定义方便，因为标准库中的定义依赖于一个嵌套的记录结构，
并可以由任何相等性的记法来参数化。

## Unicode

本章节使用了如下 Unicode：

    ∘  U+2218  环运算符 (\o, \circ, \comp)
    λ  U+03BB  小写希腊字母 LAMBDA (\lambda, \Gl)
    ≃  U+2243  渐进相等 (\~-)
    ≲  U+2272  小于或等价于 (\<~)
    ⇔  U+21D4  左右双箭头 (\<=>)
