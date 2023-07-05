```agda
module plfa.part1.Exercise1 where

import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
```

#### 练习 `seven`（实践） {#seven}

请写出 `7` 的完整定义。

```agda
-- 请将代码写在此处。
```

你需要为 `seven` 给出类型签名以及定义。在 Emacs 中使用 `C-c C-l` 来让 Agda
重新加载。

#### 练习 `+-example`（实践） {#plus-example}

计算 `3 + 4`，将你的推导过程写成等式链，为 `+` 使用等式。

```agda
-- 请将代码写在此处。
```

#### 练习 `*-example`（实践） {#times-example}

计算 `3 * 4`，将你的推导过程写成等式链，为 `*` 使用等式。
（不必写出 `+` 求值的每一步。）

```agda
-- 请将代码写在此处。
```

#### 练习 `_^_`（推荐） {#power}

根据以下等式写出乘方的定义。

    m ^ 0        =  1
    m ^ (1 + n)  =  m * (m ^ n)

检查 `3 ^ 4` 是否等于 `81`。

```agda
-- 请将代码写在此处。
```

#### 练习 `∸-example₁` 和 `∸-example₂`（推荐） {#monus-examples}

计算 `5 ∸ 3` 和 `3 ∸ 5`，将你的推导过程写成等式链。

```agda
-- 请将代码写在此处。
```

#### 练习 `Bin`（拓展） {#Bin}

使用二进制系统能提供比一进制系统更高效的自然数表示。我们可以用一个比特串来表示一个数：

```agda
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin
```

例如，以下比特串

    1011

代表数字十一被编码为了

    ⟨⟩ I O I I

由于前导零的存在，表示并不是唯一的。因此，十一同样可以
表示成 `001011`，编码为：

    ⟨⟩ O O I O I I

定义这样一个函数

    inc : Bin → Bin

将一个比特串转换成下一个数的比特串。比如，`1100` 编码了十二，我们就应该有：

    inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O

实现这个函数，并验证它对于表示零到四的比特串都能给出正确结果。

使用以上的定义，再定义一对函数用于在两种表示间转换。

    to   : ℕ → Bin
    from : Bin → ℕ

对于前者，用没有前导零的比特串来表示正数，并用 `⟨⟩ O` 表示零。
验证这两个函数都能对零到四给出正确结果。

```agda
-- 请将代码写在此处。
```

#### 练习：`+-swap`（推荐） {#plus-swap}

请证明对于所有的自然数 `m`、`n` 和 `p`，

    m + (n + p) ≡ n + (m + p)

成立。无需归纳证明，只需应用前面满足结合律和交换律的结果即可。

```agda
-- 请将代码写在此处。
```

#### 练习 `*-distrib-+`（推荐） {#times-distrib-plus}

请证明乘法对加法满足分配律，即对于所有的自然数 `m`、`n` 和 `p`，

    (m + n) * p ≡ m * p + n * p

成立。

```agda
-- 请将代码写在此处。
```

#### 练习 `*-assoc`（推荐） {#times-assoc}

请证明乘法满足结合律，即对于所有的自然数 `m`、`n` 和 `p`，

    (m * n) * p ≡ m * (n * p)

成立。

```agda
-- 请将代码写在此处。
```

#### 练习 `*-comm`（实践） {#times-comm}

请证明乘法满足交换律，即对于所有的自然数 `m` 和 `n`，

    m * n ≡ n * m

成立。和加法交换律一样，你需要陈述并证明配套的引理。

```agda
-- 请将代码写在此处。
```

#### 练习 `0∸n≡0`（实践） {#zero-monus}

请证明对于所有的自然数 `n`，

    zero ∸ n ≡ zero

成立。你的证明需要归纳法吗？

```agda
-- 请将代码写在此处。
```

#### 练习 `∸-+-assoc`（实践） {#monus-plus-assoc}

请证明饱和减法与加法满足结合律，即对于所有的自然数 `m`、`n` 和 `p`，

    m ∸ n ∸ p ≡ m ∸ (n + p)

成立。

```agda
-- 请将代码写在此处。
```

#### 练习 `+*^` （延伸）

证明下列三条定律

     m ^ (n + p) ≡ (m ^ n) * (m ^ p)  (^-distribˡ-+-*)
     (m * n) ^ p ≡ (m ^ p) * (n ^ p)  (^-distribʳ-*)
     (m ^ n) ^ p ≡ m ^ (n * p)        (^-*-assoc)

对于所有 `m`、`n` 和 `p` 成立。

```agda
-- 请将代码写在此处。
```

#### 练习 `Bin-laws`（延伸） {#Bin-laws}

回想练习 [Bin](/Naturals/#Bin)
中定义的一种表示自然数的比特串数据类型 `Bin`
以及要求你定义的函数：

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

考虑以下定律，其中 `n` 表示自然数，`b` 表示比特串：

    from (inc b) ≡ suc (from b)
    to (from b) ≡ b
    from (to n) ≡ n

对于每一条定律：若它成立，请证明；若不成立，请给出一个反例。

```agda
-- 请将代码写在此处。
```
