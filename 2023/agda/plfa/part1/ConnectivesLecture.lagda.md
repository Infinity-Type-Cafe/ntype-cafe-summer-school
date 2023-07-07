```agda
module plfa.part1.ConnectivesLecture where

open import plfa.part1.IsomorphismLecture using (_≃_)
open plfa.part1.IsomorphismLecture.≃-Reasoning
```

本章节介绍基础的逻辑运算符。我们使用逻辑运算符与数据类型之间的对应关系，
即**命题即类型（Propositions as Types）**原理。

  * **合取（Conjunction）**即是**积（Product）**
  * **析取（Disjunction）**即是**和（Sum）**
  * **真（True）**即是**单元类型（Unit Type）**
  * **假（False）**即是**空类型（Empty Type）**
  * **蕴涵（Implication）**即是**函数空间（Function Space）**

## 导入

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
```

## 合取即是积

```agda
data _×_ (A B : Set) : Set where
  _,_ :
      A
    → B
      -----
    → A × B
```

```agda
_ : ℕ × ℕ
_ = 3 , 22
```

```agda
--fst
proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ (x , _) = x

--snd
proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ (x , y) = y
```

```agda
η-× : ∀ {A B : Set} (w : A × B) → (proj₁ w , proj₂ w) ≡ w
η-× (x , y) = refl
```

```agda
record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_
```

```agda
--2
data Bool : Set where
  true  : Bool
  false : Bool

--3
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
```

那么，`Bool × Tri` 类型有如下的六个成员：

    (true  , aa)    (true  , bb)    (true ,  cc)
    (false , aa)    (false , bb)    (false , cc)

下面的函数枚举了所有类型为 `Bool × Tri` 的参数：

```agda
×-count : Bool × Tri → ℕ
×-count (true , aa) = 1
×-count (true , bb) = 2
×-count (true , cc) = 3
×-count (false , aa) = 4
×-count (false , bb) = 5
×-count (false , cc) = 6
```

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)

## 真即是单元类型

```agda
data ⊤ : Set where

  tt :
    --
    ⊤
```

```agda
⊤-count : ⊤ → ℕ
⊤-count tt = 1
```

```agda
η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl
```

```agda
record ⊤′ : Set where
  --no-eta-equality
  constructor tt′
```

```agda
η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl
```

```agda
truth : ⊤
truth = tt

truth′ : ⊤′
truth′ = _
```

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A

## 析取即是和

```agda
data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B
```

```agda
case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y
```

```agda
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl
```

```agda
infixr 1 _⊎_
```

因此 `A × C ⊎ B × C` 解析为 `(A × C) ⊎ (B × C)`。

```agda
⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5
```

类型上的和与数的和有相似的性质——它们满足交换律和结合律。
更确切地说，和在**在同构意义下**是交换和结合的。

## 假即是空类型

```agda
data ⊥ : Set where
  -- 没有语句！
```

```agda
⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()
```

这是我们第一次使**用荒谬模式（Absurd Pattern）** `()`。在这里，因为 `⊥`
是一个没有成员的类型，我们用 `()` 模式来指明这里不可能匹配任何这个类型的值。

```agda
⊥-count : ⊥ → ℕ
⊥-count ()
```

对于数来说，0 是加法的幺元。对应地，空是和的幺元（**在同构意义下**）。

## 蕴涵即是函数 {#implication}

```agda
→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M
```

```agda
η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl
```

```agda
→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          | aa     | aa      =   1
...          | aa     | bb      =   2
...          | aa     | cc      =   3
...          | bb     | aa      =   4
...          | bb     | bb      =   5
...          | bb     | cc      =   6
...          | cc     | aa      =   7
...          | cc     | bb      =   8
...          | cc     | cc      =   9
```

(p ^ n) ^ m  ≡  p ^ (n * m)

```agda
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```

```agda
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ f → λ{ (x , y) → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g (x , y) }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ (x , y) → refl }}
    }
```

p ^ (n + m) = (p ^ n) * (p ^ m)

```agda
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ((f ∘ inj₁) , (f ∘ inj₂)) }
    ; from    = λ{ (g , h) → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ (g , h) → refl }
    }
```

## 标准库

```agda
import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Data.Unit using (⊤; tt)
import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Data.Empty using (⊥; ⊥-elim)
import Function.Equivalence using (_⇔_)
```

## Unicode

    ×  U+00D7  乘法符号 (\x)
    ⊎  U+228E  多重集并集 (\u+)
    ⊤  U+22A4  向下图钉 (\top)
    ⊥  U+22A5  向上图钉 (\bot)
    η  U+03B7  希腊小写字母 ETA (\eta)
    ₁  U+2081  下标 1 (\_1)
    ₂  U+2082  下标 2 (\_2)
    ⇔  U+21D4  左右双箭头 (\<=>)
