/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Submonoids of archimedean monoids

This file defines the instances that show that the (mul)archimedean property is retained in a
submonoid of the ambient group.

## Main statements

* `SubmonoidClass.instMulArchimedean`: the submonoid (and similar subobjects) of a mul-archimedean
  group retains the mul-archimedean property when restricted to the submonoid.
* `AddSubmonoidClass.instArchimedean`: the additive submonoid (and similar subobjects) of an
  archimedean additive group retains the archimedean property when restricted to the additive
  submonoid.
-/

public section

assert_not_exists Finset

@[to_additive]
/-
**SubmonoidClass.instMulArchimedean** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SubmonoidClass.instMulArchimedean {M S : Type*} [SetLike S M] [CommMonoid 
M] [PartialOrder M] [SubmonoidClass S M] [MulArchimedean M] (H : S) : MulArchime
dean H
参数：H : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MulArchimedean.arch`：∀ {R : Type u_2} {inst : CommMonoid R} {inst_1 : Pa
rtialOrder R} [self : MulArchimedean R] (x : R) {y : R},   1 < y → ∃ n, x ≤ y ^ 
n
-/
instance SubmonoidClass.instMulArchimedean {M S : Type*} [SetLike S M]
    [CommMonoid M] [PartialOrder M]
    [SubmonoidClass S M] [MulArchimedean M] (H : S) : MulArchimedean H := by
  constructor
  rintro x _
  simp only [← Subtype.coe_lt_coe, OneMemClass.coe_one]
  exact MulArchimedean.arch x.val
