/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# The Krull dimension of a field

This file proves that the Krull dimension of a field is zero.
-/

public section

open Order

@[simp]
/-
**ringKrullDim_eq_zero_of_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ringKrullDim_eq_zero_of_field (F : Type*) [Field F] : ringKrullDim F = 0
参数：F : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.krullDim_eq_zero_of_unique`：krullDim_eq_zero_of_unique [Unique α] 
: krullDim α = 0
-/
theorem ringKrullDim_eq_zero_of_field (F : Type*) [Field F] : ringKrullDim F = 0 :=
  krullDim_eq_zero_of_unique
/-
**ringKrullDim_eq_zero_of_isField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ringKrullDim_eq_zero_of_isField {F : Type*} [CommRing F] (hF : IsField F) 
: ringKrullDim F = 0
参数：hF : IsField F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.krullDim_eq_zero_of_unique`：krullDim_eq_zero_of_unique [Unique α] 
: krullDim α = 0
-/
theorem ringKrullDim_eq_zero_of_isField {F : Type*} [CommRing F] (hF : IsField F) :
    ringKrullDim F = 0 :=
  @krullDim_eq_zero_of_unique _ _ <| @PrimeSpectrum.instUnique _ hF.toField
