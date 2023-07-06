```agda
module plfa.part1.Exercise2 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-comm; +-identityʳ;
  ≤-refl; ≤-trans; ≤-antisym; ≤-total; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)

open import plfa.part1.RelationsLecture
```

#### 练习 `orderings`（实践） {#orderings}

给出一个不是偏序的预序的例子。

```agda
-- 请将代码写在此处。
```

给出一个不是全序的偏序的例子。

```agda
-- 请将代码写在此处。
```

#### 练习 `≤-antisym-cases`（实践） {#leq-antisym-cases}

`≤-antisym` 的证明中省略了一个参数是 `z≤n`，另一个参数是 `s≤s` 的情况。为什么可以省略这种情况？

```agda
-- 请将代码写在此处。
```

#### 练习 `o+o≡e` (延伸) {#odd-plus-odd}

证明两个奇数之和为偶数。

```agda
-- 请将代码写在此处。
```

#### 练习 `Bin-predicates` (延伸) {#Bin-predicates}

回忆我们在练习 [Bin](/Naturals/#Bin) 中定义了一个数据类型 `Bin` 来用二进制字符串表示自然数。
这个表达方法不是唯一的，因为我们在开头加任意个 0。因此，11 可以由以下方法表示：

    ⟨⟩ I O I I
    ⟨⟩ O O I O I I

定义一个谓词

    Can : Bin → Set

其在一个二进制字符串的表示是标准的（Canonical）时成立，表示它没有开头的 0。在两个 11 的表达方式中，
第一个是标准的，而第二个不是。在定义这个谓词时，你需要一个辅助谓词：

    One : Bin → Set

其仅在一个二进制字符串开头为 1 时成立。一个二进制字符串是标准的，如果它开头是 1 （表示一个正数），
或者它仅是一个 0 （表示 0）。

证明递增可以保持标准性。

    Can b
    ------------
    Can (inc b)

证明从自然数转换成的二进制字符串是标准的。

    ----------
    Can (to n)

证明将一个标准的二进制字符串转换成自然数之后，再转换回二进制字符串与原二进制字符串相同。

    Can b
    ---------------
    to (from b) ≡ b

（提示：对于每一条习题，先从 `One` 的性质开始。此外，你或许还需要证明若
`One b` 成立，则 `1` 小于或等于 `from b` 的结果。）

```agda
open import plfa.part1.Exercise1
-- 请将代码写在此处。
```
