/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex J. Best
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Pointwise set operations on `MeasurableSet`s

In this file we prove several versions of the following fact: if `s` is a measurable set, then so is
`a • s`. Note that the pointwise product of two measurable sets need not be measurable, so there is
no `MeasurableSet.mul` etc.
-/

public section


open scoped Pointwise

open Set

@[to_additive]
/-
**MeasurableSet.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.const_smul {G α : Type*} [Group G] [MulAction G α] [Measurab
leSpace α] [MeasurableConstSMul G α] {s : Set α} (hs : MeasurableSet s) (a : G) 
: MeasurableSet (a • s)
参数：hs : MeasurableSet s；a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_smul_inv`：preimage_smul_inv (a : α) (t : Set β) : (fun x =>
 a⁻¹ • x) ⁻¹' t = a • t
· 使用定理 `MeasurableConstSMul.measurable_const_smul`：∀ {M : Type u_2} {α : Type u_
3} {inst : SMul M α} {inst_1 : MeasurableSpace α} [self : MeasurableConstSMul M 
α] (c : M),   Measurable fun x …
-/
theorem MeasurableSet.const_smul {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] [MeasurableConstSMul G α] {s : Set α} (hs : MeasurableSet s) (a : G) :
    MeasurableSet (a • s) := by
  rw [← preimage_smul_inv]
  exact measurable_const_smul _ hs
/-
**MeasurableSet.const_smul_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.const_smul_of_ne_zero {G₀ α : Type*} [GroupWithZero G₀] [Mul
Action G₀ α] [MeasurableSpace α] [MeasurableConstSMul G₀ α] {s : Set α} (hs : Me
asurableSet s) {a : G₀} (ha : a != 0) : MeasurableSet (a • s)
参数：hs : MeasurableSet s；ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.preimage_smul_inv₀`：preimage_smul_inv₀ (ha : a != 0) (t : Set β) : (
fun x => a⁻¹ • x) ⁻¹' t = a • t
· 使用定理 `MeasurableConstSMul.measurable_const_smul`：∀ {M : Type u_2} {α : Type u_
3} {inst : SMul M α} {inst_1 : MeasurableSpace α} [self : MeasurableConstSMul M 
α] (c : M),   Measurable fun x …
-/
theorem MeasurableSet.const_smul_of_ne_zero {G₀ α : Type*} [GroupWithZero G₀] [MulAction G₀ α]
    [MeasurableSpace α] [MeasurableConstSMul G₀ α] {s : Set α}
    (hs : MeasurableSet s) {a : G₀} (ha : a ≠ 0) : MeasurableSet (a • s) := by
  rw [← preimage_smul_inv₀ ha]
  exact measurable_const_smul _ hs
/-
**MeasurableSet.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.const_smul {G α : Type*} [Group G] [MulAction G α] [Measurab
leSpace α] [MeasurableConstSMul G α] {s : Set α} (hs : MeasurableSet s) (a : G) 
: MeasurableSet (a • s)
参数：hs : MeasurableSet s；a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_smul_inv`：preimage_smul_inv (a : α) (t : Set β) : (fun x =>
 a⁻¹ • x) ⁻¹' t = a • t
· 使用定理 `MeasurableConstSMul.measurable_const_smul`：∀ {M : Type u_2} {α : Type u_
3} {inst : SMul M α} {inst_1 : MeasurableSpace α} [self : MeasurableConstSMul M 
α] (c : M),   Measurable fun x …
-/
theorem MeasurableSet.const_smul₀ {G₀ α : Type*} [GroupWithZero G₀] [Zero α]
    [MulActionWithZero G₀ α] [MeasurableSpace α] [MeasurableConstSMul G₀ α]
    [MeasurableSingletonClass α] {s : Set α} (hs : MeasurableSet s) (a : G₀) :
    MeasurableSet (a • s) := by
  rcases eq_or_ne a 0 with (rfl | ha)
  exacts [(subsingleton_zero_smul_set s).measurableSet, hs.const_smul_of_ne_zero ha]
