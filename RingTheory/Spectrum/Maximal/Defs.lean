/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.RingTheory.Ideal.Maximal

/-!
# Maximal spectrum of a commutative (semi)ring

The maximal spectrum of a commutative (semi)ring is the type of all maximal ideals.
It is naturally a subset of the prime spectrum endowed with the subspace topology.

## Main definitions

* `MaximalSpectrum R`: The maximal spectrum of a commutative (semi)ring `R`,
  i.e., the set of all maximal ideals of `R`.
-/

public section

/-- The maximal spectrum of a commutative (semi)ring `R` is the type of all
maximal ideals of `R`. -/
@[ext]
/-
**MaximalSpectrum** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [CommSemiring R] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximal spectrum of a commutative (semi)ring `R` is the type of all
maximal ideals of `R`.
-/
structure MaximalSpectrum (R : Type*) [CommSemiring R] where
  asIdeal : Ideal R
  isMaximal : asIdeal.IsMaximal

attribute [instance] MaximalSpectrum.isMaximal
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type*) [CommSemiring R] : Coe (MaximalSpectrum R) (Ideal R) where
  coe P := P.asIdeal
