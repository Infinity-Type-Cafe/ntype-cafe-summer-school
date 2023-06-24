---
title: Agda综合哥德尔不完备 (0) 目录
---

# Agda综合哥德尔不完备 (0) 目录

(前言)

```agda
{-# OPTIONS --cubical --safe #-}

module Synthetic.Everything where
```

## (1) 偏函数

```agda
open import Synthetic.PartialFunction public
```

## (2) 递归论的基本概念

```agda
open import Synthetic.Definitions.Base public
open import Synthetic.Definitions.Properties public
```

## (3) 抽象形式系统

```agda
open import Synthetic.FormalSystem public
```

## (4) 哥德尔不完备定理

```agda
open import Synthetic.Incompleteness public
```

## 注意事项

宇宙层级在本次的形式化中无关紧要, 可以直接无视. 代码中出现宇宙层级参数 `ℓ` 只是为了让整个形式化可以发生在任意层级.
