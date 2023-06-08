---
layout: page
title: 如何学习类型论？
---

有许多人都对类型论比较好奇，但是对 "应该从哪个方向去了解呢？" 和 "学之前应当具备哪些的数学知识？" 诸如此类的问题比较模糊。 当你看见这里的时候，如果你也有类似问题，那么希望下面的内容对你有一些些帮助。

---

## 其他人谈如何学习类型论

可以听一听其他人在谈学习类型论时会说什么。

* 千里冰封, [怎么学类型论](https://cha.fan/articles/5u9DV2LWWcjgJ8c7ha7T)

---

## 证明助手

学习类型论时手边一定不能缺一个证明助手。

* Coq

    TODO: 介绍补充

    * [官方网站](https://coq.inria.fr/)

* Agda
    
    TODO: 介绍补充

    * [官方网站](https://wiki.portal.chalmers.se/agda/pmwiki.php)

* Lean

    TODO: 介绍补充

    * [官方网站](https://leanprover.github.io/)

---

## 课程与讲义

* TODO: 待推荐课程

---

## 书籍

---

### 类型论

* [HoTT book](https://homotopytypetheory.org/book/)

    同类型类型论的官方书籍，第一章是类型论入门非常好的内容，第二章就开始涉及一些同伦论的知识了。TODO: 介绍补充


* Trebor, [类型论简史](https://github.com/Trebor-Huang/history)

    一篇对类型论的中文介绍，包含了许多基本概念的梳理、对更多好的参考资料的收集、解释了部分常见的误解、介绍了一些对于类型论的更加现代的高观点，还有一些历史方面的内容。这主要面向数学方向的人，但是CS方向应该也可以读一读。

* Robert Harper, [Practical Foundations of Programming Languages (PFPL)](http://www.cs.cmu.edu/~rwh/pfpl/2nded.pdf)    

    TODO: 介绍补充

* Benjamin C. Pierce, [Types and Programming Languages (TAPL)](https://github.com/MPRI/M2-4-2/blob/master/Types%20and%20Programming%20Languages.pdf)

    一篇面向计算机系同学的比较友好地介绍类型的书。TODO: 介绍补充

---

### 范畴论

* TODO: 待推荐书籍

---

### 证明论

* Sara Negri, Jan von Plato, [Structural Proof Theory](https://github.com/m4p1e/ntype-cafe-summer-school/blob/main/resources/Structural%20Proof%20Theory.pdf)

    一篇介绍结构证明论非常好的书籍。你可以从最基础的证明演算自然演绎(natural deduction)学起，了解什么是推理规则(inference rule)，有哪些不同种类的推理规则(introduction / elimination等)，一棵证明树长什么样子，一个证明系统的基本性质(一致性和完备性)，那么你就对结构证明论研究的东西有了一个基本印象。在此过程中你逐步体会到使用自然演绎来做推理的时候会遇到一些很麻烦的东西(不同类型的推理规则有不同的使用方向)，这个时候引入相继演算式(sequent calculus)会很好的解决这些问题。一定要在里面学到一些非常重要的证明方法比如结构归纳法。然后你可能会迷失在一个又一个不同的基于相继演算式的证明系统里面，这是因为往一个证明系统里面即使添加一个规则，也有可能会带来天翻地覆的变化，而文中一直在做的事就是研究前后两个系统之间关系，这实际是相等乏味的。这个时候如果你已经熟悉了某个证明系统例如关于直觉逻辑的G3ip，就可以从结构证明论里面跳出来了，因为它对于你学习往后学习类型论的帮助已经不大了。

---

## 博客

* [HoTT博客](https://homotopytypetheory.org/blog/)

    TODO: 介绍补充

* [Xena项目](https://xenaproject.wordpress.com/)

    TODO: 介绍补充

---

## 项目

* [泛等数学](https://unimath.github.io/agda-unimath/)

    TODO: 介绍补充

---

## 相关经典问题指南

* [对path induction的困惑你不孤单](https://github.com/HoTT/book/issues/460)