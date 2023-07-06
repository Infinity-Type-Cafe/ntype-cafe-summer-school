```agda
module plfa.part1.RelationsLecture where
```

## 导入

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)
```

## 定义关系

小于等于这个关系有无穷个实例，如下所示：


    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

但是，我们仍然可以用几行有限的定义来表示所有的实例，如下文所示的一对推理规则：

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

以及其 Agda 定义：

```agda
data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n
```

我们在这里以推理规则的形式写出 `2 ≤ 4` 的证明：

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

下面是对应的 Agda 证明：

```agda
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)
```

## 隐式参数

```agda
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))
```

也可以额外加上参数的名字：

```agda
_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))
```

在后者的形式中，也可以选择只声明一部分隐式参数：

```agda
_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)
```

但是不可以改变隐式参数的顺序，即便加上了名字。

我们可以为命题 `+-identityʳ` 定义一个带有隐式参数的变体：

```agda
+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _
```

## 优先级

```agda
infix 4 _≤_
```

`1 + 2 ≤ 3` 将被解析为 `(1 + 2) ≤ 3`

`1 ≤ 2 ≤ 3` 解析为 `(1 ≤ 2) ≤ 3` 或者 `1 ≤ (2 ≤ 3)` 都没有意义。

## 反演

```agda
inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n
```

```agda
inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl
```

## 序关系的性质

* **自反（Reflexive）**：对于所有的 `n`，关系 `n ≤ n` 成立。
* **传递（Transitive）**：对于所有的 `m`、 `n` 和 `p`，如果 `m ≤ n` 和 `n ≤ p`
  成立，那么 `m ≤ p` 也成立。
* **反对称（Anti-symmetric）**：对于所有的 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ m`
  同时成立，那么 `m ≡ n` 成立。
* **完全（Total）**：对于所有的 `m` 和 `n`，`m ≤ n` 或者 `n ≤ m` 成立。

* **预序（Preorder）**：满足自反和传递的关系。
* **偏序（Partial Order）**：满足反对称的预序。
* **全序（Total Order）**：满足完全的偏序。

## 自反性

```agda
≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl
```

## 传递性

```agda
≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)
```

我们也可以将隐式参数显式地声明。

```agda
≤-trans′ : ∀ (m n p : ℕ)
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans′ zero    _       _       z≤n       _          =  z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans′ m n p m≤n n≤p)
```

有人说这样的证明更加的清晰，也有人说这个更长的证明让人难以抓住证明的重点。
我们一般选择使用简短的证明。

## 反对称性

```agda
≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)
```

## 完全性

我们首先来说明怎么样不等式才是完全的：

```agda
data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n
```

这是我们第一次使用带*参数*的数据类型，这里 `m` 和 `n` 是参数。这等同于下面的索引数据类型：

```agda
data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
      ----------
    → Total′ m n

  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
      ----------
    → Total′ m n
```

```agda
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)
```

使用 `with` 语句等同于定义一个辅助函数。比如说，上面的定义和下面的等价：

```agda
≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)
```

```agda
≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m       zero                      =  flipped z≤n
≤-total″ zero    (suc n)                   =  forward z≤n
≤-total″ (suc m) (suc n) with ≤-total″ m n
...                         | forward m≤n  =  forward (s≤s m≤n)
...                         | flipped n≤m  =  flipped (s≤s n≤m)
```

## 单调性

```agda
+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)
```

```agda
+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n
```

```agda
+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)
```

## 严格不等关系 {#strict-inequality}

(不讲)

## 奇和偶 {#even-and-odd}

作为一个额外的例子，我们来定义奇数和偶数。不等关系和严格不等关系是**二元关系**，而奇偶性
是**一元关系**，有时也被叫做**谓词（Predicate）**：

**mutual induction**
**constructor overloading**

```agda
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc  : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
```

```agda
e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)
```

## 标准库

```agda
import Data.Nat using (_≤_; z≤n; s≤s)
import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;
                                  +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
```

在标准库中，`≤-total` 是使用析取定义的（我们将在 [Connectives](/Connectives/) 章节定义）。
`+-monoʳ-≤`、`+-monoˡ-≤` 和 `+-mono-≤` 的证明方法和本书不同。
更多的参数是隐式申明的。

## Unicode

本章使用了如下 Unicode 符号：

    ≤  U+2264  小于等于 (\<=, \le)
    ≥  U+2265  大于等于 (\>=, \ge)
    ˡ  U+02E1  小写字母 L 标识符 (\^l)
    ʳ  U+02B3  小写字母 R 标识符 (\^r)
