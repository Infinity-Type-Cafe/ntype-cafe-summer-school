```agda
module plfa.part1.QuantifiersLecture where
```

## 导入

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.IsomorphismLecture using (_≃_)
open import plfa.part1.ConnectivesLecture using (extensionality)
open import Function using (_∘_)
```

## 全称量化

```agda
∀-elim : ∀ {A : Set} {B : A → Set}
  → (H : ∀ (x : A) → B x)
  → (a : A)
    -----------------
  → B a
∀-elim H a = H a
```

## 存在量化

```agda
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B
```

```agda
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
```

这是我们第一次使用语法声明，其表示左手边的项可以以右手边的语法来书写。
这种特殊语法只有在标识符 `Σ-syntax` 被导入时可用。

我们也可以用记录类型来等价地定义存在量化。

```agda
record Σ′ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁′ : A
    proj₂′ : B proj₁′
```

这里的记录构造

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

对应了项

    (M , N)

```agda
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B
```

```agda
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f (x , y) = f x y
```

```agda
∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ (x , y) → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g (x , y) }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ (x , y) → refl }}
    }
```

## 存在量化、全称量化和否定

存在量化的否定与否定的全称量化是同构的。考虑到存在量化是析构的推广，全称量化是合构的推广，
这样的结果与析构的否定与否定的合构是同构的结果相似。

```agda
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy (x , y) }
    ; from    =  λ{ ∀¬xy (x , y) → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ (x , y) → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }
```

--∃¬≃¬∀则要排中律

## 标准库

标准库中可以找到与本章中相似的定义：

```agda
import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
```

## Unicode

本章节使用下列 Unicode：

    Π  U+03A0  大写希腊字母 PI (\Pi)
    Σ  U+03A3  大写希腊字母 SIGMA (\Sigma)
    ∃  U+2203  存在 (\ex, \exists)
