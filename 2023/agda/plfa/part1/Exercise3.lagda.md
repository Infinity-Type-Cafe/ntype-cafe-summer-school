```agda
module plfa.part1.Exercise3 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import plfa.part1.IsomorphismLecture
open import plfa.part1.ConnectivesLecture
open import plfa.part1.NegationLecture
open import plfa.part1.QuantifiersLecture
```

## 嵌入（Embedding）

```agda
infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_
```

```agda
≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to      = λ{x → to   B≲C (to   A≲B x)}
    ; from    = λ{y → from A≲B (from B≲C y)}
    ; from∘to = λ{x →
        begin
          from A≲B (from B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
          from A≲B (to A≲B x)
        ≡⟨ from∘to A≲B x ⟩
          x
        ∎}
     }
```

如果两个类型相互嵌入，且其嵌入函数相互对应，那么它们是同构的。
这个一种反对称性的弱化形式：

```agda
≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
    -------------------
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to =
  record
    { to      = to A≲B
    ; from    = from A≲B
    ; from∘to = from∘to A≲B
    ; to∘from = λ{y →
        begin
          to A≲B (from A≲B y)
        ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
          to A≲B (to B≲A y)
        ≡⟨ cong-app to≡from (to B≲A y) ⟩
          from B≲A (to B≲A y)
        ≡⟨ from∘to B≲A y ⟩
          y
        ∎}
    }
```

## 嵌入的相等性论证

```agda
module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
      -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning
```

#### 练习 `≃-implies-≲`（实践）

证明每个同构蕴涵了一个嵌入。

```agda
postulate
  ≃-implies-≲ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≲ B
```

```agda
-- 请将代码写在此处。
```

#### 练习 `_⇔_`（实践） {#iff}

按下列形式定义命题的等价性（又名「当且仅当」）：

```agda
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
```

证明等价性是自反、对称和传递的。

```agda
-- 请将代码写在此处。
```

#### 练习 `Bin-embedding` （延伸） {#Bin-embedding}

回忆练习 [Bin](/Naturals/#Bin) 和
[Bin-laws](/Induction/#Bin-laws)，
我们定义了比特串数据类型 `Bin` 来表示自然数，并要求你来定义下列函数：


    to : ℕ → Bin
    from : Bin → ℕ

它们满足如下性质：

    from (to n) ≡ n

使用上述条件，证明存在一个从 `ℕ` 到 `Bin` 的嵌入。

```agda
-- 请将代码写在此处。
```

为什么 `to` 和 `from` 不能构造一个同构？

#### 练习 `⇔≃×` （推荐）

<!--
Show that `A ⇔ B` as defined [earlier](/Isomorphism/#iff)
is isomorphic to `(A → B) × (B → A)`.
-->

证明[之前](/Isomorphism/#iff)定义的 `A ⇔ B` 与 `(A → B) × (B → A)` 同构。

```agda
-- 请将代码写在此处。
```

#### 练习 `⊎-comm` （推荐）

证明和类型在同构意义下满足交换律。

```agda
-- 请将代码写在此处。
```

#### 练习 `⊎-assoc`（实践）

证明和类型在同构意义下满足结合律。

```agda
-- 请将代码写在此处。
```

#### 练习 `⊥-identityˡ` （推荐）

证明空在同构意义下是和的左幺元。

```agda
-- 请将代码写在此处。
```

#### 练习 `⊥-identityʳ`（实践）

证明空在同构意义下是和的右幺元。

```agda
-- 请将代码写在此处。
```

#### 练习 `⊎×-implies-×⊎`（实践）

证明合取的析取蕴涵了析取的合取：

```agda
postulate
  ⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
```

反命题成立吗？如果成立，给出证明；如果不成立，给出反例。

```agda
-- 请将代码写在此处。
```

#### 练习 `<-irreflexive`（推荐）

利用否定证明[严格不等性](/Relations/#strict-inequality)满足非自反性，
即 `n < n` 对于任何 `n` 都不成立。

```agda
-- 请将代码写在此处
```

#### 练习 `trichotomy`（实践）

请证明严格不等性满足[三分律](/Relations/#trichotomy)，
即对于任何自然数 `m` 和 `n`，以下三条刚好只有一条成立：

* `m < n`
* `m ≡ n`
* `m > n`


「刚好只有一条」的意思是，三者中不仅有一条成立，而且当其中一条成立时，
其它二者的否定也必定成立。

```agda
-- 请将代码写在此处
```

#### 练习 `⊎-dual-×`（推荐）

请证明合取、析取和否定可通过以下版本的德摩根定律（De Morgan's Law）关联在一起。

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

此结果是我们之前证明的定理的简单推论。

```agda
-- 请将代码写在此处
```

以下命题也成立吗？

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

若成立，请证明；若不成立，你能给出一个比同构更弱的关系将两边关联起来吗？

#### 练习 `Classical`（延伸）

考虑以下定律：

  * 排中律：对于所有 `A`，`A ⊎ ¬ A`。
  * 双重否定消去：对于所有的 `A`，`¬ ¬ A → A`。
  * 皮尔士定律：对于所有的 `A` 和 `B`，`((A → B) → A) → A`。
  * 蕴涵表示为析取：对于所有的 `A` 和 `B`，`(A → B) → ¬ A ⊎ B`。
  * 德摩根定律：对于所有的 `A` 和 `B`，`¬ (¬ A × ¬ B) → A ⊎ B`。

请证明其中任意一条定律都蕴涵其它所有定律。

```agda
-- 请将代码写在此处
```

#### 联系 `Stable`（延伸）

若双重否定消去对某个式子成立，我们就说它是**稳定（Stable）**的：

```agda
Stable : Set → Set
Stable A = ¬ ¬ A → A
```

请证明任何否定式都是稳定的，并且两个稳定式的合取也是稳定的。

```agda
-- 请将代码写在此处
```

#### 练习 `∀-distrib-×` （推荐）

证明全称量词对于合取满足分配律：

```agda
postulate
  ∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
```

将这个结果与 [Connectives](/Connectives/)
章节中的 (`→-distrib-×`) 结果对比。

#### 练习 `⊎∀-implies-∀⊎`（实践）

证明全称命题的析取蕴涵了析取的全称命题：

```agda
postulate
  ⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
```

逆命题成立么？如果成立，给出证明。如果不成立，解释为什么。

#### 练习 `∀-×`（实践）

令 `B` 作为由 `Tri` 索引的一个类型，也就是说 `B : Tri → Set`。
证明 `∀ (x : Tri) → B x` 和 `B aa × B bb × B cc` 是同构的。
提示：你需要引入一个可应用于依赖函数的外延性公设。

#### 练习 `∃-distrib-⊎` （推荐）

证明存在量词对于析取满足分配律：

```agda
postulate
  ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
```

#### 练习 `∃×-implies-×∃`（实践）

证明合取的存在命题蕴涵了存在命题的合取：

```agda
postulate
  ∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
```

逆命题成立么？如果成立，给出证明。如果不成立，解释为什么。

#### 练习 `∃-⊎`（实践）

沿用练习 `∀-×` 中的 `Tri` 和 `B` 。
证明 `∃[ x ] B x` 与 `B aa ⊎ B bb ⊎ B cc` 是同构的。

#### 练习 `∃-+-≤`（实践）

证明当且仅当存在一个 `x` 使得 `x + y ≡ z` 成立时 `y ≤ z` 成立。

```agda
-- 请将代码写在此处。
```

#### 练习 `∃¬-implies-¬∀` （推荐）

证明否定的存在量化蕴涵了全称量化的否定：

```agda
postulate
  ∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
    → ∃[ x ] (¬ B x)
      --------------
    → ¬ (∀ x → B x)
```

逆命题成立吗？如果成立，给出证明。如果不成立，解释为什么。

#### 练习 `Bin-isomorphism` （延伸） {#Bin-isomorphism}

回忆在练习 [Bin](/Naturals/#Bin)、
[Bin-laws](/Induction/#Bin-laws) 和
[Bin-predicates](/Relations/#Bin-predicates) 中，
我们定义了比特串数据类型 `Bin` 来表示自然数，并要求你定义了下列函数和谓词：

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

以及证明了下列性质：

    from (to n) ≡ n

    ----------
    Can (to n)

    Can b
    ---------------
    to (from b) ≡ b

使用上述，证明 `ℕ` 与 `∃[ b ](Can b)` 之间存在同构。

我们建议证明以下引理，它描述了对于给定的二进制数 `b`，`One b` 只有一个证明，
`Can b`，也是如此。

    ≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′

    ≡Can : ∀ {b : Bin} (cb cb′ : Can b) → cb ≡ cb′

Many of the alternatives for proving `to∘from` turn out to be tricky.
However, the proof can be straightforward if you use the following lemma,
which is a corollary of `≡Can`.

    proj₁≡→Can≡ : {cb cb′ : ∃[ b ] Can b} → proj₁ cb ≡ proj₁ cb′ → cb ≡ cb′

```agda
-- 请将代码写在此处。
```
