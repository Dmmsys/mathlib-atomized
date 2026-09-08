/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Algebra.Order.Interval.Set.Monoid
public import Mathlib.Order.Interval.Set.OrderIso
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# (Pre)images of intervals

In this file we prove a bunch of trivial lemmas like “if we add `a` to all points of `[b, c]`,
then we get `[a + b, a + c]`”. For the functions `x ↦ x ± a`, `x ↦ a ± x`, and `x ↦ -x` we prove
lemmas about preimages and images of all intervals. We also prove a few lemmas about images under
`x ↦ a * x`, `x ↦ x * a` and `x ↦ x⁻¹`.
-/

public section


open Interval Pointwise

variable {α : Type*}

namespace Set

/-! ### Binary pointwise operations

Note that the subset operations below only cover the cases with the largest possible intervals on
the LHS: to conclude that `Ioo a b * Ioo c d ⊆ Ioo (a * c) (c * d)`, you can use monotonicity of `*`
and `Set.Ico_mul_Ioc_subset`.

TODO: repeat these lemmas for the generality of `mul_le_mul` (which assumes nonnegativity), which
the unprimed names have been reserved for
-/

section ContravariantLE

variable [Mul α] [Preorder α] [MulLeftMono α] [MulRightMono α]

@[to_additive Icc_add_Icc_subset]
/-
**Set.Icc_mul_Icc_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_mul_Icc_subset' (a b c d : α) : Icc a b * Icc c d subseteq Icc (a * c)
 (b * d)
参数：a b c d : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
-/
theorem Icc_mul_Icc_subset' (a b c d : α) : Icc a b * Icc c d ⊆ Icc (a * c) (b * d) := by
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_le_mul' hyb hzd⟩

@[to_additive Iic_add_Iic_subset]
/-
**Set.Iic_mul_Iic_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_mul_Iic_subset' (a b : α) : Iic a * Iic b subseteq Iic (a * b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
-/
theorem Iic_mul_Iic_subset' (a b : α) : Iic a * Iic b ⊆ Iic (a * b) := by
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_le_mul' hya hzb

@[to_additive Ici_add_Ici_subset]
/-
**Set.Ici_mul_Ici_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ici_mul_Ici_subset' (a b : α) : Ici a * Ici b subseteq Ici (a * b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
-/
theorem Ici_mul_Ici_subset' (a b : α) : Ici a * Ici b ⊆ Ici (a * b) := by
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_le_mul' hya hzb

end ContravariantLE

section ContravariantLT

variable [Mul α] [PartialOrder α] [MulLeftStrictMono α] [MulRightStrictMono α]

@[to_additive Icc_add_Ico_subset]
/-
**Set.Icc_mul_Ico_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_mul_Ico_subset' (a b c d : α) : Icc a b * Ico c d subseteq Ico (a * c)
 (b * d)
参数：a b c d : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulLeftMono_of_mulLeftStrictMono`：mulLeftMono_of_mulLeftStrictMono (M) [
Mul M] [PartialOrder M] [MulLeftStrictMono M] : MulLeftMono M
· 使用定理 `mulRightMono_of_mulRightStrictMono`：mulRightMono_of_mulRightStrictMono (
M) [Mul M] [PartialOrder M] [MulRightStrictMono M] : MulRightMono M
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `mul_lt_mul_of_le_of_lt`：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [Mu
lRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
-/
theorem Icc_mul_Ico_subset' (a b c d : α) : Icc a b * Ico c d ⊆ Ico (a * c) (b * d) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_lt_mul_of_le_of_lt hyb hzd⟩

@[to_additive Ico_add_Icc_subset]
/-
**Set.Ico_mul_Icc_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_mul_Icc_subset' (a b c d : α) : Ico a b * Icc c d subseteq Ico (a * c)
 (b * d)
参数：a b c d : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulLeftMono_of_mulLeftStrictMono`：mulLeftMono_of_mulLeftStrictMono (M) [
Mul M] [PartialOrder M] [MulLeftStrictMono M] : MulLeftMono M
· 使用定理 `mulRightMono_of_mulRightStrictMono`：mulRightMono_of_mulRightStrictMono (
M) [Mul M] [PartialOrder M] [MulRightStrictMono M] : MulRightMono M
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
-/
theorem Ico_mul_Icc_subset' (a b c d : α) : Ico a b * Icc c d ⊆ Ico (a * c) (b * d) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_lt_mul_of_lt_of_le hyb hzd⟩

@[to_additive Ioc_add_Ico_subset]
/-
**Set.Ioc_mul_Ico_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_mul_Ico_subset' (a b c d : α) : Ioc a b * Ico c d subseteq Ioo (a * c)
 (b * d)
参数：a b c d : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulLeftMono_of_mulLeftStrictMono`：mulLeftMono_of_mulLeftStrictMono (M) [
Mul M] [PartialOrder M] [MulLeftStrictMono M] : MulLeftMono M
· 使用定理 `mulRightMono_of_mulRightStrictMono`：mulRightMono_of_mulRightStrictMono (
M) [Mul M] [PartialOrder M] [MulRightStrictMono M] : MulRightMono M
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
· 使用定理 `mul_lt_mul_of_le_of_lt`：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [Mu
lRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
-/
theorem Ioc_mul_Ico_subset' (a b c d : α) : Ioc a b * Ico c d ⊆ Ioo (a * c) (b * d) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_lt_mul_of_lt_of_le hya hzc, mul_lt_mul_of_le_of_lt hyb hzd⟩

@[to_additive Ico_add_Ioc_subset]
/-
**Set.Ico_mul_Ioc_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_mul_Ioc_subset' (a b c d : α) : Ico a b * Ioc c d subseteq Ioo (a * c)
 (b * d)
参数：a b c d : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulLeftMono_of_mulLeftStrictMono`：mulLeftMono_of_mulLeftStrictMono (M) [
Mul M] [PartialOrder M] [MulLeftStrictMono M] : MulLeftMono M
· 使用定理 `mulRightMono_of_mulRightStrictMono`：mulRightMono_of_mulRightStrictMono (
M) [Mul M] [PartialOrder M] [MulRightStrictMono M] : MulRightMono M
· 使用定理 `mul_lt_mul_of_le_of_lt`：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [Mu
lRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
-/
theorem Ico_mul_Ioc_subset' (a b c d : α) : Ico a b * Ioc c d ⊆ Ioo (a * c) (b * d) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_lt_mul_of_le_of_lt hya hzc, mul_lt_mul_of_lt_of_le hyb hzd⟩

@[to_additive Iic_add_Iio_subset]
/-
**Set.Iic_mul_Iio_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_mul_Iio_subset' (a b : α) : Iic a * Iio b subseteq Iio (a * b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulRightMono_of_mulRightStrictMono`：mulRightMono_of_mulRightStrictMono (
M) [Mul M] [PartialOrder M] [MulRightStrictMono M] : MulRightMono M
· 使用定理 `mul_lt_mul_of_le_of_lt`：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [Mu
lRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
-/
theorem Iic_mul_Iio_subset' (a b : α) : Iic a * Iio b ⊆ Iio (a * b) := by
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_le_of_lt hya hzb

@[to_additive Iio_add_Iic_subset]
/-
**Set.Iio_mul_Iic_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_mul_Iic_subset' (a b : α) : Iio a * Iic b subseteq Iio (a * b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulLeftMono_of_mulLeftStrictMono`：mulLeftMono_of_mulLeftStrictMono (M) [
Mul M] [PartialOrder M] [MulLeftStrictMono M] : MulLeftMono M
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
-/
theorem Iio_mul_Iic_subset' (a b : α) : Iio a * Iic b ⊆ Iio (a * b) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_lt_of_le hya hzb

@[to_additive Ioi_add_Ici_subset]
/-
**Set.Ioi_mul_Ici_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_mul_Ici_subset' (a b : α) : Ioi a * Ici b subseteq Ioi (a * b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulLeftMono_of_mulLeftStrictMono`：mulLeftMono_of_mulLeftStrictMono (M) [
Mul M] [PartialOrder M] [MulLeftStrictMono M] : MulLeftMono M
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
-/
theorem Ioi_mul_Ici_subset' (a b : α) : Ioi a * Ici b ⊆ Ioi (a * b) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_lt_of_le hya hzb

@[to_additive Ici_add_Ioi_subset]
/-
**Set.Ici_mul_Ioi_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ici_mul_Ioi_subset' (a b : α) : Ici a * Ioi b subseteq Ioi (a * b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulRightMono_of_mulRightStrictMono`：mulRightMono_of_mulRightStrictMono (
M) [Mul M] [PartialOrder M] [MulRightStrictMono M] : MulRightMono M
· 使用定理 `mul_lt_mul_of_le_of_lt`：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [Mu
lRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
-/
theorem Ici_mul_Ioi_subset' (a b : α) : Ici a * Ioi b ⊆ Ioi (a * b) := by
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_le_of_lt hya hzb

end ContravariantLT

section LinearOrderedCommMonoid
variable [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α] [MulLeftReflectLE α] [ExistsMulOfLE α]
  {a b c d : α}

-- TODO: Generalise to arbitrary actions using a `smul` version of `MulLeftMono`
@[to_additive (attr := simp)]
/-
**Set.smul_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_Icc (a b c : α) : a • Icc b c = Icc (a * b) (a * c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `exists_one_le_mul_of_le`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 :
 Preorder α] [ExistsMulOfLE α] {a b : α} [MulLeftReflectLE α],   a ≤ b → ∃ c, 1 
≤ c ∧ a * c =…
· 使用定理 `le_mul_of_one_le_right'`：le_mul_of_one_le_right' [MulLeftMono α] {a b : 
α} (h : 1 <= b) : a <= a * b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_le_mul_iff_left`：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflect
LE α] (a : α) {b c : α} : a * b <= a * c ↔ b <= c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma smul_Icc (a b c : α) : a • Icc b c = Icc (a * b) (a * c) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hby, hyc⟩, rfl⟩
    dsimp
    constructor <;> gcongr
  · rintro ⟨habx, hxac⟩
    obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le habx
    refine ⟨b * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, (mul_assoc ..).symm⟩
    rwa [mul_assoc, mul_le_mul_iff_left] at hxac

@[to_additive]
/-
**Set.Icc_mul_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Icc_mul_Icc (hab : a <= b) (hcd : c <= d) : Icc a b * Icc c d = Icc (a * c
) (b * d)
参数：hab : a <= b；hcd : c <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.Icc_mul_Icc_subset'`：Icc_mul_Icc_subset' (a b c d : α) : Icc a b * I
cc c d subseteq Icc (a * c) (b * d)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `exists_one_le_mul_of_le`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 :
 Preorder α] [ExistsMulOfLE α] {a b : α} [MulLeftReflectLE α],   a ≤ b → ∃ c, 1 
≤ c ∧ a * c =…
· 使用定理 `le_mul_of_one_le_right'`：le_mul_of_one_le_right' [MulLeftMono α] {a b : 
α} (h : 1 <= b) : a <= a * b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `mul_le_mul_iff_left`：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflect
LE α] (a : α) {b c : α} : a * b <= a * c ↔ b <= c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Icc_mul_Icc (hab : a ≤ b) (hcd : c ≤ d) : Icc a b * Icc c d = Icc (a * c) (b * d) := by
  refine (Icc_mul_Icc_subset' _ _ _ _).antisymm fun x ⟨hacx, hxbd⟩ ↦ ?_
  obtain hxbc | hbcx := le_total x (b * c)
  · obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le hacx
    refine ⟨a * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, c, left_mem_Icc.2 hcd, mul_right_comm ..⟩
    rwa [mul_right_comm, mul_le_mul_iff_right] at hxbc
  · obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le hbcx
    refine ⟨b, right_mem_Icc.2 hab, c * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, (mul_assoc ..).symm⟩
    rwa [mul_assoc, mul_le_mul_iff_left] at hxbd

end LinearOrderedCommMonoid

section OrderedCommGroup
variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

/-
**Set.inv_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrder α] [IsOrdered
Monoid α] (a : α), (Set.Ici a)⁻¹ = Set.Iic a⁻¹
参数：a : α；Set.Ici a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `le_inv'`：le_inv' : a <= b⁻¹ ↔ b <= a⁻¹
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive (attr := simp)] lemma inv_Ici (a : α) : (Ici a)⁻¹ = Iic a⁻¹ := ext fun _x ↦ le_inv'
/-
**Set.inv_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrder α] [IsOrdered
Monoid α] (a : α), (Set.Iic a)⁻¹ = Set.Ici a⁻¹
参数：a : α；Set.Iic a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `inv_le'`：inv_le' : a⁻¹ <= b ↔ b⁻¹ <= a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive (attr := simp)] lemma inv_Iic (a : α) : (Iic a)⁻¹ = Ici a⁻¹ := ext fun _x ↦ inv_le'
/-
**Set.inv_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrder α] [IsOrdered
Monoid α] (a : α), (Set.Ioi a)⁻¹ = Set.Iio a⁻¹
参数：a : α；Set.Ioi a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `lt_inv'`：lt_inv' : a < b⁻¹ ↔ b < a⁻¹
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
-/
@[to_additive (attr := simp)] lemma inv_Ioi (a : α) : (Ioi a)⁻¹ = Iio a⁻¹ := ext fun _x ↦ lt_inv'
/-
**Set.inv_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrder α] [IsOrdered
Monoid α] (a : α), (Set.Iio a)⁻¹ = Set.Ioi a⁻¹
参数：a : α；Set.Iio a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `inv_lt'`：inv_lt' : a⁻¹ < b ↔ b⁻¹ < a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
-/
@[to_additive (attr := simp)] lemma inv_Iio (a : α) : (Iio a)⁻¹ = Ioi a⁻¹ := ext fun _x ↦ inv_lt'

@[to_additive (attr := simp)]
/-
**Set.inv_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inv_Icc (a b : α) : (Icc a b)⁻¹ = Icc b⁻¹ a⁻¹
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_inv`：inter_inv : (s inter t)⁻¹ = s⁻¹ inter t⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.inv_Ici`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Ici a)⁻¹ = Set.Iic a⁻¹
· 使用定理 `Set.inv_Iic`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Iic a)⁻¹ = Set.Ici a⁻¹
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_Icc (a b : α) : (Icc a b)⁻¹ = Icc b⁻¹ a⁻¹ := by simp [← Ici_inter_Iic, inter_comm]

@[to_additive (attr := simp)]
/-
**Set.inv_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inv_Ico (a b : α) : (Ico a b)⁻¹ = Ioc b⁻¹ a⁻¹
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_inv`：inter_inv : (s inter t)⁻¹ = s⁻¹ inter t⁻¹
· 使用定理 `Set.inv_Ici`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Ici a)⁻¹ = Set.Iic a⁻¹
· 使用定理 `Set.inv_Iio`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Iio a)⁻¹ = Set.Ioi a⁻¹
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_Ico (a b : α) : (Ico a b)⁻¹ = Ioc b⁻¹ a⁻¹ := by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, inter_comm]

@[to_additive (attr := simp)]
/-
**Set.inv_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inv_Ioc (a b : α) : (Ioc a b)⁻¹ = Ico b⁻¹ a⁻¹
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_inv`：inter_inv : (s inter t)⁻¹ = s⁻¹ inter t⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.inv_Iic`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Iic a)⁻¹ = Set.Ici a⁻¹
· 使用定理 `Set.inv_Ioi`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Ioi a)⁻¹ = Set.Iio a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_Ioc (a b : α) : (Ioc a b)⁻¹ = Ico b⁻¹ a⁻¹ := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[to_additive (attr := simp)]
/-
**Set.inv_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inv_Ioo (a b : α) : (Ioo a b)⁻¹ = Ioo b⁻¹ a⁻¹
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_inv`：inter_inv : (s inter t)⁻¹ = s⁻¹ inter t⁻¹
· 使用定理 `Set.inv_Iio`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Iio a)⁻¹ = Set.Ioi a⁻¹
· 使用定理 `Set.inv_Ioi`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Ioi a)⁻¹ = Set.Iio a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_Ioo (a b : α) : (Ioo a b)⁻¹ = Ioo b⁻¹ a⁻¹ := by simp [← Ioi_inter_Iio, inter_comm]

/-!
### Preimages under `x ↦ a * x`
-/

@[to_additive (attr := simp)]
/-
**Set.preimage_const_mul_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ici : (fun x => a * x) ⁻¹' Ici b = Ici (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `div_le_iff_le_mul'`：div_le_iff_le_mul' : a / b <= c ↔ a <= b * c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α

--- 原说明 ---
### Preimages under `x ↦ a * x`
-/
theorem preimage_const_mul_Ici : (fun x => a * x) ⁻¹' Ici b = Ici (b / a) :=
  ext fun _x => div_le_iff_le_mul'.symm

@[to_additive (attr := simp)]
/-
**Set.preimage_const_mul_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ioi : (fun x => a * x) ⁻¹' Ioi b = Ioi (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `div_lt_iff_lt_mul'`：div_lt_iff_lt_mul' : a / b < c ↔ a < b * c
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_const_mul_Ioi : (fun x => a * x) ⁻¹' Ioi b = Ioi (b / a) :=
  ext fun _x => div_lt_iff_lt_mul'.symm

@[to_additive (attr := simp)]
/-
**Set.preimage_const_mul_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Iic : (fun x => a * x) ⁻¹' Iic b = Iic (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `le_div_iff_mul_le'`：le_div_iff_mul_le' : b <= c / a ↔ a * b <= c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_const_mul_Iic : (fun x => a * x) ⁻¹' Iic b = Iic (b / a) :=
  ext fun _x => le_div_iff_mul_le'.symm

@[to_additive (attr := simp)]
/-
**Set.preimage_const_mul_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Iio : (fun x => a * x) ⁻¹' Iio b = Iio (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `lt_div_iff_mul_lt'`：lt_div_iff_mul_lt' : b < c / a ↔ a * b < c
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_const_mul_Iio : (fun x => a * x) ⁻¹' Iio b = Iio (b / a) :=
  ext fun _x => lt_div_iff_mul_lt'.symm

@[to_additive (attr := simp)]
/-
**Set.preimage_const_mul_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Icc : (fun x => a * x) ⁻¹' Icc b c = Icc (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_const_mul_Ici`：preimage_const_mul_Ici : (fun x => a * x) ⁻¹
' Ici b = Ici (b / a)
· 使用定理 `Set.preimage_const_mul_Iic`：preimage_const_mul_Iic : (fun x => a * x) ⁻¹
' Iic b = Iic (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_const_mul_Icc : (fun x => a * x) ⁻¹' Icc b c = Icc (b / a) (c / a) := by
  simp [← Ici_inter_Iic]

@[to_additive (attr := simp)]
/-
**Set.preimage_const_mul_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ico : (fun x => a * x) ⁻¹' Ico b c = Ico (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_const_mul_Ici`：preimage_const_mul_Ici : (fun x => a * x) ⁻¹
' Ici b = Ici (b / a)
· 使用定理 `Set.preimage_const_mul_Iio`：preimage_const_mul_Iio : (fun x => a * x) ⁻¹
' Iio b = Iio (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_const_mul_Ico : (fun x => a * x) ⁻¹' Ico b c = Ico (b / a) (c / a) := by
  simp [← Ici_inter_Iio]

@[to_additive (attr := simp)]
/-
**Set.preimage_const_mul_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ioc : (fun x => a * x) ⁻¹' Ioc b c = Ioc (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_const_mul_Ioi`：preimage_const_mul_Ioi : (fun x => a * x) ⁻¹
' Ioi b = Ioi (b / a)
· 使用定理 `Set.preimage_const_mul_Iic`：preimage_const_mul_Iic : (fun x => a * x) ⁻¹
' Iic b = Iic (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_const_mul_Ioc : (fun x => a * x) ⁻¹' Ioc b c = Ioc (b / a) (c / a) := by
  simp [← Ioi_inter_Iic]

@[to_additive (attr := simp)]
/-
**Set.preimage_const_mul_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ioo : (fun x => a * x) ⁻¹' Ioo b c = Ioo (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_const_mul_Ioi`：preimage_const_mul_Ioi : (fun x => a * x) ⁻¹
' Ioi b = Ioi (b / a)
· 使用定理 `Set.preimage_const_mul_Iio`：preimage_const_mul_Iio : (fun x => a * x) ⁻¹
' Iio b = Iio (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_const_mul_Ioo : (fun x => a * x) ⁻¹' Ioo b c = Ioo (b / a) (c / a) := by
  simp [← Ioi_inter_Iio]

/-!
### Preimages under `x ↦ x * a`
-/

@[to_additive (attr := simp)]
/-
**Set.preimage_mul_const_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Ici : (fun x => x * a) ⁻¹' Ici b = Ici (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `div_le_iff_le_mul`：div_le_iff_le_mul : a / c <= b ↔ a <= b * c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α

--- 原说明 ---
### Preimages under `x ↦ x * a`
-/
theorem preimage_mul_const_Ici : (fun x => x * a) ⁻¹' Ici b = Ici (b / a) :=
  ext fun _x => div_le_iff_le_mul.symm

@[to_additive (attr := simp)]
/-
**Set.preimage_mul_const_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Ioi : (fun x => x * a) ⁻¹' Ioi b = Ioi (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `div_lt_iff_lt_mul`：div_lt_iff_lt_mul : a / c < b ↔ a < b * c
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_mul_const_Ioi : (fun x => x * a) ⁻¹' Ioi b = Ioi (b / a) :=
  ext fun _x => div_lt_iff_lt_mul.symm

@[to_additive (attr := simp)]
/-
**Set.preimage_mul_const_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Iic : (fun x => x * a) ⁻¹' Iic b = Iic (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `le_div_iff_mul_le`：le_div_iff_mul_le : a <= c / b ↔ a * b <= c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_mul_const_Iic : (fun x => x * a) ⁻¹' Iic b = Iic (b / a) :=
  ext fun _x => le_div_iff_mul_le.symm

@[to_additive (attr := simp)]
/-
**Set.preimage_mul_const_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Iio : (fun x => x * a) ⁻¹' Iio b = Iio (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `lt_div_iff_mul_lt`：lt_div_iff_mul_lt : a < c / b ↔ a * b < c
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_mul_const_Iio : (fun x => x * a) ⁻¹' Iio b = Iio (b / a) :=
  ext fun _x => lt_div_iff_mul_lt.symm

@[to_additive (attr := simp)]
/-
**Set.preimage_mul_const_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Icc : (fun x => x * a) ⁻¹' Icc b c = Icc (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_mul_const_Ici`：preimage_mul_const_Ici : (fun x => x * a) ⁻¹
' Ici b = Ici (b / a)
· 使用定理 `Set.preimage_mul_const_Iic`：preimage_mul_const_Iic : (fun x => x * a) ⁻¹
' Iic b = Iic (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_mul_const_Icc : (fun x => x * a) ⁻¹' Icc b c = Icc (b / a) (c / a) := by
  simp [← Ici_inter_Iic]

@[to_additive (attr := simp)]
/-
**Set.preimage_mul_const_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Ico : (fun x => x * a) ⁻¹' Ico b c = Ico (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_mul_const_Ici`：preimage_mul_const_Ici : (fun x => x * a) ⁻¹
' Ici b = Ici (b / a)
· 使用定理 `Set.preimage_mul_const_Iio`：preimage_mul_const_Iio : (fun x => x * a) ⁻¹
' Iio b = Iio (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_mul_const_Ico : (fun x => x * a) ⁻¹' Ico b c = Ico (b / a) (c / a) := by
  simp [← Ici_inter_Iio]

@[to_additive (attr := simp)]
/-
**Set.preimage_mul_const_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Ioc : (fun x => x * a) ⁻¹' Ioc b c = Ioc (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_mul_const_Ioi`：preimage_mul_const_Ioi : (fun x => x * a) ⁻¹
' Ioi b = Ioi (b / a)
· 使用定理 `Set.preimage_mul_const_Iic`：preimage_mul_const_Iic : (fun x => x * a) ⁻¹
' Iic b = Iic (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_mul_const_Ioc : (fun x => x * a) ⁻¹' Ioc b c = Ioc (b / a) (c / a) := by
  simp [← Ioi_inter_Iic]

@[to_additive (attr := simp)]
/-
**Set.preimage_mul_const_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Ioo : (fun x => x * a) ⁻¹' Ioo b c = Ioo (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_mul_const_Ioi`：preimage_mul_const_Ioi : (fun x => x * a) ⁻¹
' Ioi b = Ioi (b / a)
· 使用定理 `Set.preimage_mul_const_Iio`：preimage_mul_const_Iio : (fun x => x * a) ⁻¹
' Iio b = Iio (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_mul_const_Ioo : (fun x => x * a) ⁻¹' Ioo b c = Ioo (b / a) (c / a) := by
  simp [← Ioi_inter_Iio]

/-!
### Preimages under `x ↦ x / a`
-/

@[to_additive (attr := simp)]
/-
**Set.preimage_div_const_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_div_const_Ici : (fun x => x / a) ⁻¹' Ici b = Ici (b * a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.preimage_mul_const_Ici`：preimage_mul_const_Ici : (fun x => x * a) ⁻¹
' Ici b = Ici (b / a)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Preimages under `x ↦ x / a`
-/
theorem preimage_div_const_Ici : (fun x => x / a) ⁻¹' Ici b = Ici (b * a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Set.preimage_div_const_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_div_const_Ioi : (fun x => x / a) ⁻¹' Ioi b = Ioi (b * a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.preimage_mul_const_Ioi`：preimage_mul_const_Ioi : (fun x => x * a) ⁻¹
' Ioi b = Ioi (b / a)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_div_const_Ioi : (fun x => x / a) ⁻¹' Ioi b = Ioi (b * a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Set.preimage_div_const_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_div_const_Iic : (fun x => x / a) ⁻¹' Iic b = Iic (b * a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.preimage_mul_const_Iic`：preimage_mul_const_Iic : (fun x => x * a) ⁻¹
' Iic b = Iic (b / a)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_div_const_Iic : (fun x => x / a) ⁻¹' Iic b = Iic (b * a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Set.preimage_div_const_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_div_const_Iio : (fun x => x / a) ⁻¹' Iio b = Iio (b * a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.preimage_mul_const_Iio`：preimage_mul_const_Iio : (fun x => x * a) ⁻¹
' Iio b = Iio (b / a)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_div_const_Iio : (fun x => x / a) ⁻¹' Iio b = Iio (b * a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Set.preimage_div_const_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_div_const_Icc : (fun x => x / a) ⁻¹' Icc b c = Icc (b * a) (c * a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.preimage_mul_const_Icc`：preimage_mul_const_Icc : (fun x => x * a) ⁻¹
' Icc b c = Icc (b / a) (c / a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_div_const_Icc : (fun x => x / a) ⁻¹' Icc b c = Icc (b * a) (c * a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Set.preimage_div_const_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_div_const_Ico : (fun x => x / a) ⁻¹' Ico b c = Ico (b * a) (c * a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.preimage_mul_const_Ico`：preimage_mul_const_Ico : (fun x => x * a) ⁻¹
' Ico b c = Ico (b / a) (c / a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_div_const_Ico : (fun x => x / a) ⁻¹' Ico b c = Ico (b * a) (c * a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Set.preimage_div_const_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_div_const_Ioc : (fun x => x / a) ⁻¹' Ioc b c = Ioc (b * a) (c * a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.preimage_mul_const_Ioc`：preimage_mul_const_Ioc : (fun x => x * a) ⁻¹
' Ioc b c = Ioc (b / a) (c / a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_div_const_Ioc : (fun x => x / a) ⁻¹' Ioc b c = Ioc (b * a) (c * a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Set.preimage_div_const_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_div_const_Ioo : (fun x => x / a) ⁻¹' Ioo b c = Ioo (b * a) (c * a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.preimage_mul_const_Ioo`：preimage_mul_const_Ioo : (fun x => x * a) ⁻¹
' Ioo b c = Ioo (b / a) (c / a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_div_const_Ioo : (fun x => x / a) ⁻¹' Ioo b c = Ioo (b * a) (c * a) := by
  simp [div_eq_mul_inv]

/-!
### Preimages under `x ↦ a / x`
-/

@[to_additive (attr := simp)]
/-
**Set.preimage_const_div_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_div_Ici : (fun x => a / x) ⁻¹' Ici b = Iic (a / b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `le_div_comm`：le_div_comm : a <= b / c ↔ c <= b / a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α

--- 原说明 ---
### Preimages under `x ↦ a / x`
-/
theorem preimage_const_div_Ici : (fun x => a / x) ⁻¹' Ici b = Iic (a / b) :=
  ext fun _x => le_div_comm

@[to_additive (attr := simp)]
/-
**Set.preimage_const_div_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_div_Iic : (fun x => a / x) ⁻¹' Iic b = Ici (a / b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `div_le_comm`：div_le_comm : a / b <= c ↔ a / c <= b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_const_div_Iic : (fun x => a / x) ⁻¹' Iic b = Ici (a / b) :=
  ext fun _x => div_le_comm

@[to_additive (attr := simp)]
/-
**Set.preimage_const_div_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_div_Ioi : (fun x => a / x) ⁻¹' Ioi b = Iio (a / b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `lt_div_comm`：lt_div_comm : a < b / c ↔ c < b / a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_const_div_Ioi : (fun x => a / x) ⁻¹' Ioi b = Iio (a / b) :=
  ext fun _x => lt_div_comm

@[to_additive (attr := simp)]
/-
**Set.preimage_const_div_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_div_Iio : (fun x => a / x) ⁻¹' Iio b = Ioi (a / b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `div_lt_comm`：div_lt_comm : a / b < c ↔ a / c < b
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_const_div_Iio : (fun x => a / x) ⁻¹' Iio b = Ioi (a / b) :=
  ext fun _x => div_lt_comm

@[to_additive (attr := simp)]
/-
**Set.preimage_const_div_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_div_Icc : (fun x => a / x) ⁻¹' Icc b c = Icc (a / c) (a / b
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_const_div_Ici`：preimage_const_div_Ici : (fun x => a / x) ⁻¹
' Ici b = Iic (a / b)
· 使用定理 `Set.preimage_const_div_Iic`：preimage_const_div_Iic : (fun x => a / x) ⁻¹
' Iic b = Ici (a / b)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_const_div_Icc : (fun x => a / x) ⁻¹' Icc b c = Icc (a / c) (a / b) := by
  simp [← Ici_inter_Iic, inter_comm]

@[to_additive (attr := simp)]
/-
**Set.preimage_const_div_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_div_Ico : (fun x => a / x) ⁻¹' Ico b c = Ioc (a / c) (a / b
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_const_div_Ici`：preimage_const_div_Ici : (fun x => a / x) ⁻¹
' Ici b = Iic (a / b)
· 使用定理 `Set.preimage_const_div_Iio`：preimage_const_div_Iio : (fun x => a / x) ⁻¹
' Iio b = Ioi (a / b)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_const_div_Ico : (fun x => a / x) ⁻¹' Ico b c = Ioc (a / c) (a / b) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[to_additive (attr := simp)]
/-
**Set.preimage_const_div_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_div_Ioc : (fun x => a / x) ⁻¹' Ioc b c = Ico (a / c) (a / b
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_const_div_Iic`：preimage_const_div_Iic : (fun x => a / x) ⁻¹
' Iic b = Ici (a / b)
· 使用定理 `Set.preimage_const_div_Ioi`：preimage_const_div_Ioi : (fun x => a / x) ⁻¹
' Ioi b = Iio (a / b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_const_div_Ioc : (fun x => a / x) ⁻¹' Ioc b c = Ico (a / c) (a / b) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[to_additive (attr := simp)]
/-
**Set.preimage_const_div_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_div_Ioo : (fun x => a / x) ⁻¹' Ioo b c = Ioo (a / c) (a / b
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.preimage_const_div_Iio`：preimage_const_div_Iio : (fun x => a / x) ⁻¹
' Iio b = Ioi (a / b)
· 使用定理 `Set.preimage_const_div_Ioi`：preimage_const_div_Ioi : (fun x => a / x) ⁻¹
' Ioi b = Iio (a / b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_const_div_Ioo : (fun x => a / x) ⁻¹' Ioo b c = Ioo (a / c) (a / b) := by
  simp [← Ioi_inter_Iio, inter_comm]

/-!
### Images under `x ↦ a * x`
-/

-- simp can prove this modulo `mul_comm`
@[to_additive]
/-
**Set.image_const_mul_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_const_mul_Iic : (fun x => a * x) '' Iic b = Iic (a * b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Iic`：preimage_mul_const_Iic : (fun x => x * a) ⁻¹
' Iic b = Iic (b / a)
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_const_mul_Iic : (fun x => a * x) '' Iic b = Iic (a * b) := by simp [mul_comm]

-- simp can prove this modulo `mul_comm`
@[to_additive]
/-
**Set.image_const_mul_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_const_mul_Iio : (fun x => a * x) '' Iio b = Iio (a * b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Iio`：preimage_mul_const_Iio : (fun x => x * a) ⁻¹
' Iio b = Iio (b / a)
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_const_mul_Iio : (fun x => a * x) '' Iio b = Iio (a * b) := by simp [mul_comm]

/-!
### Images under `x ↦ x * a`
-/

@[to_additive]
/-
**Set.image_mul_const_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_const_Iic : (fun x => x * a) '' Iic b = Iic (b * a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `Set.preimage_mul_const_Iic`：preimage_mul_const_Iic : (fun x => x * a) ⁻¹
' Iic b = Iic (b / a)
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Images under `x ↦ x * a`
-/
theorem image_mul_const_Iic : (fun x => x * a) '' Iic b = Iic (b * a) := by simp

@[to_additive]
/-
**Set.image_mul_const_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_const_Iio : (fun x => x * a) '' Iio b = Iio (b * a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `Set.preimage_mul_const_Iio`：preimage_mul_const_Iio : (fun x => x * a) ⁻¹
' Iio b = Iio (b / a)
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_mul_const_Iio : (fun x => x * a) '' Iio b = Iio (b * a) := by simp


/-!
### Images under `x ↦ x⁻¹`
-/

@[to_additive]
/-
**Set.image_inv_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_inv_Ici : Inv.inv '' Ici a = Iic (a⁻¹)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Set.inv_Ici`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Ici a)⁻¹ = Set.Iic a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Images under `x ↦ x⁻¹`
-/
theorem image_inv_Ici : Inv.inv '' Ici a = Iic (a⁻¹) := by simp

@[to_additive]
/-
**Set.image_inv_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_inv_Iic : Inv.inv '' Iic a = Ici (a⁻¹)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Set.inv_Iic`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Iic a)⁻¹ = Set.Ici a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_inv_Iic : Inv.inv '' Iic a = Ici (a⁻¹) := by simp

@[to_additive]
/-
**Set.image_inv_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_inv_Ioi : Inv.inv '' Ioi a = Iio (a⁻¹)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Set.inv_Ioi`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Ioi a)⁻¹ = Set.Iio a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_inv_Ioi : Inv.inv '' Ioi a = Iio (a⁻¹) := by simp

@[to_additive]
/-
**Set.image_inv_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_inv_Iio : Inv.inv '' Iio a = Ioi (a⁻¹)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Set.inv_Iio`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Iio a)⁻¹ = Set.Ioi a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_inv_Iio : Inv.inv '' Iio a = Ioi (a⁻¹) := by simp

@[to_additive]
/-
**Set.image_inv_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_inv_Icc : Inv.inv '' Icc a b = Icc (b⁻¹) (a⁻¹)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用引理 `Set.inv_Icc`：inv_Icc (a b : α) : (Icc a b)⁻¹ = Icc b⁻¹ a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_inv_Icc : Inv.inv '' Icc a b = Icc (b⁻¹) (a⁻¹) := by simp

@[to_additive]
/-
**Set.image_inv_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_inv_Ico : Inv.inv '' Ico a b = Ioc (b⁻¹) (a⁻¹)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用引理 `Set.inv_Ico`：inv_Ico (a b : α) : (Ico a b)⁻¹ = Ioc b⁻¹ a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_inv_Ico : Inv.inv '' Ico a b = Ioc (b⁻¹) (a⁻¹) := by simp

@[to_additive]
/-
**Set.image_inv_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_inv_Ioc : Inv.inv '' Ioc a b = Ico (b⁻¹) (a⁻¹)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用引理 `Set.inv_Ioc`：inv_Ioc (a b : α) : (Ioc a b)⁻¹ = Ico b⁻¹ a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_inv_Ioc : Inv.inv '' Ioc a b = Ico (b⁻¹) (a⁻¹) := by simp

@[to_additive]
/-
**Set.image_inv_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_inv_Ioo : Inv.inv '' Ioo a b = Ioo (b⁻¹) (a⁻¹)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用引理 `Set.inv_Ioo`：inv_Ioo (a b : α) : (Ioo a b)⁻¹ = Ioo b⁻¹ a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_inv_Ioo : Inv.inv '' Ioo a b = Ioo (b⁻¹) (a⁻¹) := by simp



/-!
### Images under `x ↦ a / x`
-/

@[to_additive (attr := simp)]
/-
**Set.image_const_div_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_const_div_Ici : (fun x => a / x) '' Ici b = Iic (a / b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Set.inv_Ici`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Ici a)⁻¹ = Set.Iic a⁻¹
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Iic`：preimage_mul_const_Iic : (fun x => x * a) ⁻¹
' Iic b = Iic (b / a)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Images under `x ↦ a / x`
-/
theorem image_const_div_Ici : (fun x => a / x) '' Ici b = Iic (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]
/-
**Set.image_const_div_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_const_div_Iic : (fun x => a / x) '' Iic b = Ici (a / b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Set.inv_Iic`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Iic a)⁻¹ = Set.Ici a⁻¹
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Ici`：preimage_mul_const_Ici : (fun x => x * a) ⁻¹
' Ici b = Ici (b / a)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_const_div_Iic : (fun x => a / x) '' Iic b = Ici (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]
/-
**Set.image_const_div_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_const_div_Ioi : (fun x => a / x) '' Ioi b = Iio (a / b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Set.inv_Ioi`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Ioi a)⁻¹ = Set.Iio a⁻¹
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Iio`：preimage_mul_const_Iio : (fun x => x * a) ⁻¹
' Iio b = Iio (b / a)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_const_div_Ioi : (fun x => a / x) '' Ioi b = Iio (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]
/-
**Set.image_const_div_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_const_div_Iio : (fun x => a / x) '' Iio b = Ioi (a / b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Set.inv_Iio`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Iio a)⁻¹ = Set.Ioi a⁻¹
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Ioi`：preimage_mul_const_Ioi : (fun x => x * a) ⁻¹
' Ioi b = Ioi (b / a)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_const_div_Iio : (fun x => a / x) '' Iio b = Ioi (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]
/-
**Set.image_const_div_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_const_div_Icc : (fun x => a / x) '' Icc b c = Icc (a / c) (a / b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用引理 `Set.inv_Icc`：inv_Icc (a b : α) : (Icc a b)⁻¹ = Icc b⁻¹ a⁻¹
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Icc`：preimage_mul_const_Icc : (fun x => x * a) ⁻¹
' Icc b c = Icc (b / a) (c / a)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_const_div_Icc : (fun x => a / x) '' Icc b c = Icc (a / c) (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]
/-
**Set.image_const_div_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_const_div_Ico : (fun x => a / x) '' Ico b c = Ioc (a / c) (a / b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用引理 `Set.inv_Ico`：inv_Ico (a b : α) : (Ico a b)⁻¹ = Ioc b⁻¹ a⁻¹
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Ioc`：preimage_mul_const_Ioc : (fun x => x * a) ⁻¹
' Ioc b c = Ioc (b / a) (c / a)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_const_div_Ico : (fun x => a / x) '' Ico b c = Ioc (a / c) (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]
/-
**Set.image_const_div_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_const_div_Ioc : (fun x => a / x) '' Ioc b c = Ico (a / c) (a / b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用引理 `Set.inv_Ioc`：inv_Ioc (a b : α) : (Ioc a b)⁻¹ = Ico b⁻¹ a⁻¹
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Ico`：preimage_mul_const_Ico : (fun x => x * a) ⁻¹
' Ico b c = Ico (b / a) (c / a)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_const_div_Ioc : (fun x => a / x) '' Ioc b c = Ico (a / c) (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]
/-
**Set.image_const_div_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_const_div_Ioo : (fun x => a / x) '' Ioo b c = Ioo (a / c) (a / b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用引理 `Set.inv_Ioo`：inv_Ioo (a b : α) : (Ioo a b)⁻¹ = Ioo b⁻¹ a⁻¹
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Ioo`：preimage_mul_const_Ioo : (fun x => x * a) ⁻¹
' Ioo b c = Ioo (b / a) (c / a)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_const_div_Ioo : (fun x => a / x) '' Ioo b c = Ioo (a / c) (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

/-!
### Images under `x ↦ x / a`
-/

@[to_additive (attr := simp)]
/-
**Set.image_div_const_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_div_const_Ici : (fun x => x / a) '' Ici b = Ici (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Set.preimage_mul_const_Ici`：preimage_mul_const_Ici : (fun x => x * a) ⁻¹
' Ici b = Ici (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Images under `x ↦ x / a`
-/
theorem image_div_const_Ici : (fun x => x / a) '' Ici b = Ici (b / a) := by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Set.image_div_const_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_div_const_Iic : (fun x => x / a) '' Iic b = Iic (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Set.preimage_mul_const_Iic`：preimage_mul_const_Iic : (fun x => x * a) ⁻¹
' Iic b = Iic (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_div_const_Iic : (fun x => x / a) '' Iic b = Iic (b / a) := by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Set.image_div_const_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_div_const_Ioi : (fun x => x / a) '' Ioi b = Ioi (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Set.preimage_mul_const_Ioi`：preimage_mul_const_Ioi : (fun x => x * a) ⁻¹
' Ioi b = Ioi (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_div_const_Ioi : (fun x => x / a) '' Ioi b = Ioi (b / a) := by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Set.image_div_const_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_div_const_Iio : (fun x => x / a) '' Iio b = Iio (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Set.preimage_mul_const_Iio`：preimage_mul_const_Iio : (fun x => x * a) ⁻¹
' Iio b = Iio (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_div_const_Iio : (fun x => x / a) '' Iio b = Iio (b / a) := by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Set.image_div_const_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_div_const_Icc : (fun x => x / a) '' Icc b c = Icc (b / a) (c / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Set.preimage_mul_const_Icc`：preimage_mul_const_Icc : (fun x => x * a) ⁻¹
' Icc b c = Icc (b / a) (c / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_div_const_Icc : (fun x => x / a) '' Icc b c = Icc (b / a) (c / a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Set.image_div_const_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_div_const_Ico : (fun x => x / a) '' Ico b c = Ico (b / a) (c / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Set.preimage_mul_const_Ico`：preimage_mul_const_Ico : (fun x => x * a) ⁻¹
' Ico b c = Ico (b / a) (c / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_div_const_Ico : (fun x => x / a) '' Ico b c = Ico (b / a) (c / a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Set.image_div_const_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_div_const_Ioc : (fun x => x / a) '' Ioc b c = Ioc (b / a) (c / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Set.preimage_mul_const_Ioc`：preimage_mul_const_Ioc : (fun x => x * a) ⁻¹
' Ioc b c = Ioc (b / a) (c / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_div_const_Ioc : (fun x => x / a) '' Ioc b c = Ioc (b / a) (c / a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Set.image_div_const_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_div_const_Ioo : (fun x => x / a) '' Ioo b c = Ioo (b / a) (c / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Set.preimage_mul_const_Ioo`：preimage_mul_const_Ioo : (fun x => x * a) ⁻¹
' Ioo b c = Ioo (b / a) (c / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_div_const_Ioo : (fun x => x / a) '' Ioo b c = Ioo (b / a) (c / a) := by
  simp [div_eq_mul_inv]

/-!
### Bijections
-/

@[to_additive]
/-
**Set.Iic_mul_bij** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_mul_bij : BijOn (· * a) (Iic b) (Iic (b * a))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.bijOn_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → Set.BijOn f s (f '' s)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `Set.image_mul_const_Iic`：image_mul_const_Iic : (fun x => x * a) '' Iic b
 = Iic (b * a)

--- 原说明 ---
### Bijections
-/
theorem Iic_mul_bij : BijOn (· * a) (Iic b) (Iic (b * a)) :=
  image_mul_const_Iic a b ▸ (mul_left_injective _).injOn.bijOn_image

@[to_additive]
/-
**Set.Iio_mul_bij** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_mul_bij : BijOn (· * a) (Iio b) (Iio (b * a))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.bijOn_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → Set.BijOn f s (f '' s)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `Set.image_mul_const_Iio`：image_mul_const_Iio : (fun x => x * a) '' Iio b
 = Iio (b * a)
-/
theorem Iio_mul_bij : BijOn (· * a) (Iio b) (Iio (b * a)) :=
  image_mul_const_Iio a b ▸ (mul_left_injective _).injOn.bijOn_image

end OrderedCommGroup

section LinearOrderedCommGroup
variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

@[to_additive (attr := simp)]
/-
**Set.inv_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inv_uIcc (a b : α) : [[a, b]]⁻¹ = [[a⁻¹, b⁻¹]]
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.inv_Icc`：inv_Icc (a b : α) : (Icc a b)⁻¹ = Icc b⁻¹ a⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_sup`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeft
Mono α] [MulRightMono α] (a b : α), (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `inv_inf`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeft
Mono α] [MulRightMono α] (a b : α), (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_uIcc (a b : α) : [[a, b]]⁻¹ = [[a⁻¹, b⁻¹]] := by
  simp only [uIcc, inv_Icc, inv_sup, inv_inf]

end LinearOrderedCommGroup

section LinearOrderedAddCommGroup

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b c d : α)

@[simp]
/-
**Set.preimage_const_add_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_add_uIcc : (fun x => a + x) ⁻¹' [[b, c]] = [[b - a, c - a]]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_const_add_Icc`：∀ {α : Type u_1} [inst : AddCommGroup α] [in
st_1 : PartialOrder α] [IsOrderedAddMonoid α] (a b c : α),   (fun x => a + x) ⁻¹
' Set.Icc b c = …
· 使用定理 `min_sub_sub_right`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Li
nearOrder α] [IsOrderedAddMonoid α] (a b c : α),   min (a - c) (b - c) = min a b
 - c
· 使用定理 `max_sub_sub_right`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Li
nearOrder α] [IsOrderedAddMonoid α] (a b c : α),   max (a - c) (b - c) = max a b
 - c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_const_add_uIcc : (fun x => a + x) ⁻¹' [[b, c]] = [[b - a, c - a]] := by
  simp only [← Icc_min_max, preimage_const_add_Icc, min_sub_sub_right, max_sub_sub_right]

@[simp]
/-
**Set.preimage_add_const_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_add_const_uIcc : (fun x => x + a) ⁻¹' [[b, c]] = [[b - a, c - a]]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Set.preimage_const_add_uIcc`：preimage_const_add_uIcc : (fun x => a + x) 
⁻¹' [[b, c]] = [[b - a, c - a]]
-/
theorem preimage_add_const_uIcc : (fun x => x + a) ⁻¹' [[b, c]] = [[b - a, c - a]] := by
  simpa only [add_comm] using preimage_const_add_uIcc a b c

@[simp]
/-
**Set.preimage_sub_const_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_sub_const_uIcc : (fun x => x - a) ⁻¹' [[b, c]] = [[b + a, c + a]]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Set.preimage_add_const_uIcc`：preimage_add_const_uIcc : (fun x => x + a) 
⁻¹' [[b, c]] = [[b - a, c - a]]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_sub_const_uIcc : (fun x => x - a) ⁻¹' [[b, c]] = [[b + a, c + a]] := by
  simp [sub_eq_add_neg]

@[simp]
/-
**Set.preimage_const_sub_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_sub_uIcc : (fun x => a - x) ⁻¹' [[b, c]] = [[a - b, a - c]]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_const_sub_Icc`：∀ {α : Type u_1} [inst : AddCommGroup α] [in
st_1 : PartialOrder α] [IsOrderedAddMonoid α] (a b c : α),   (fun x => a - x) ⁻¹
' Set.Icc b c = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `min_add_add_left`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Add 
α] [AddLeftMono α] (a b c : α), min (a + b) (a + c) = a + min b c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `min_neg_neg`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOr
der α] [IsOrderedAddMonoid α] (a b : α),   min (-a) (-b) = -max a b
· 使用定理 `max_add_add_left`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Add 
α] [AddLeftMono α] (a b c : α), max (a + b) (a + c) = a + max b c
· 使用定理 `max_neg_neg`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOr
der α] [IsOrderedAddMonoid α] (a b : α),   max (-a) (-b) = -min a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_const_sub_uIcc : (fun x => a - x) ⁻¹' [[b, c]] = [[a - b, a - c]] := by
  simp_rw [← Icc_min_max, preimage_const_sub_Icc]
  simp only [sub_eq_add_neg, min_add_add_left, max_add_add_left, min_neg_neg, max_neg_neg]

-- simp can prove this modulo `add_comm`
/-
**Set.image_const_add_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_const_add_uIcc : (fun x => a + x) '' [[b, c]] = [[a + b, a + c]]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Set.preimage_add_const_uIcc`：preimage_add_const_uIcc : (fun x => x + a) 
⁻¹' [[b, c]] = [[b - a, c - a]]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_const_add_uIcc : (fun x => a + x) '' [[b, c]] = [[a + b, a + c]] := by simp [add_comm]
/-
**Set.image_add_const_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_add_const_uIcc : (fun x => x + a) '' [[b, c]] = [[b + a, c + a]]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_add_right`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {b
 : α}, (fun x => x + b) '' t = (fun x => x + -b) ⁻¹' t
· 使用定理 `Set.preimage_add_const_uIcc`：preimage_add_const_uIcc : (fun x => x + a) 
⁻¹' [[b, c]] = [[b - a, c - a]]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_add_const_uIcc : (fun x => x + a) '' [[b, c]] = [[b + a, c + a]] := by simp

@[simp]
/-
**Set.image_const_sub_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_const_sub_uIcc : (fun x => a - x) '' [[b, c]] = [[a - b, a - c]]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Set.image_neg_eq_neg`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s : Set
 α}, (fun x => -x) '' s = -s
· 使用定理 `Set.neg_uIcc`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearO
rder α] [IsOrderedAddMonoid α] (a b : α),   -Set.uIcc a b = Set.uIcc (-a) (-b)
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Set.preimage_add_const_uIcc`：preimage_add_const_uIcc : (fun x => x + a) 
⁻¹' [[b, c]] = [[b - a, c - a]]
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_const_sub_uIcc : (fun x => a - x) '' [[b, c]] = [[a - b, a - c]] := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp_def] at this
  simp [sub_eq_add_neg, this, add_comm]

@[simp]
/-
**Set.image_sub_const_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_sub_const_uIcc : (fun x => x - a) '' [[b, c]] = [[b - a, c - a]]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Set.image_add_right`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {b
 : α}, (fun x => x + b) '' t = (fun x => x + -b) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Set.preimage_const_add_uIcc`：preimage_const_add_uIcc : (fun x => a + x) 
⁻¹' [[b, c]] = [[b - a, c - a]]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_sub_const_uIcc : (fun x => x - a) '' [[b, c]] = [[b - a, c - a]] := by
  simp [sub_eq_add_neg, add_comm]
/-
**Set.image_neg_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_neg_uIcc : Neg.neg '' [[a, b]] = [[-a, -b]]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_neg_eq_neg`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s : Set
 α}, (fun x => -x) '' s = -s
· 使用定理 `Set.neg_uIcc`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearO
rder α] [IsOrderedAddMonoid α] (a b : α),   -Set.uIcc a b = Set.uIcc (-a) (-b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_neg_uIcc : Neg.neg '' [[a, b]] = [[-a, -b]] := by simp

variable {a b c d}

/-- If `[c, d]` is a subinterval of `[a, b]`, then the distance between `c` and `d` is less than or
equal to that of `a` and `b` -/
/-
**Set.abs_sub_le_of_uIcc_subset_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：abs_sub_le_of_uIcc_subset_uIcc (h : [[c, d]] subseteq [[a, b]]) : |d - c| 
<= |b - a|
参数：h : [[c, d]] subseteq [[a, b]]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `max_sub_min_eq_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : Linea
rOrder α] [AddLeftMono α] [AddRightMono α] (a b : α),   max a b - min a b = |b -
 a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sub_le_sub`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b c d : α},   a ≤ b → c ≤ d → a - d ≤ b - c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Set.uIcc_subset_uIcc_iff_le`：uIcc_subset_uIcc_iff_le : [[a₁, b₁]] subset
eq [[a₂, b₂]] ↔ min a₂ b₂ <= min a₁ b₁ ∧ max a₁ b₁ <= max a₂ b₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If `[c, d]` is a subinterval of `[a, b]`, then the distance between `c` and `d` 
is less than or
equal to that of `a` and `b`
-/
theorem abs_sub_le_of_uIcc_subset_uIcc (h : [[c, d]] ⊆ [[a, b]]) : |d - c| ≤ |b - a| := by
  rw [← max_sub_min_eq_abs, ← max_sub_min_eq_abs]
  rw [uIcc_subset_uIcc_iff_le] at h
  exact sub_le_sub h.2 h.1

/-- If `c ∈ [a, b]`, then the distance between `a` and `c` is less than or equal to
that of `a` and `b` -/
/-
**Set.abs_sub_left_of_mem_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：abs_sub_left_of_mem_uIcc (h : c in [[a, b]]) : |c - a| <= |b - a|
参数：h : c in [[a, b]]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.abs_sub_le_of_uIcc_subset_uIcc`：abs_sub_le_of_uIcc_subset_uIcc (h : 
[[c, d]] subseteq [[a, b]]) : |d - c| <= |b - a|
· 使用引理 `Set.uIcc_subset_uIcc_left`：uIcc_subset_uIcc_left (h : x in [[a, b]]) : [
[a, x]] subseteq [[a, b]]

--- 原说明 ---
If `c ∈ [a, b]`, then the distance between `a` and `c` is less than or equal to
that of `a` and `b`
-/
theorem abs_sub_left_of_mem_uIcc (h : c ∈ [[a, b]]) : |c - a| ≤ |b - a| :=
  abs_sub_le_of_uIcc_subset_uIcc <| uIcc_subset_uIcc_left h

/-- If `x ∈ [a, b]`, then the distance between `c` and `b` is less than or equal to
that of `a` and `b` -/
/-
**Set.abs_sub_right_of_mem_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：abs_sub_right_of_mem_uIcc (h : c in [[a, b]]) : |b - c| <= |b - a|
参数：h : c in [[a, b]]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.abs_sub_le_of_uIcc_subset_uIcc`：abs_sub_le_of_uIcc_subset_uIcc (h : 
[[c, d]] subseteq [[a, b]]) : |d - c| <= |b - a|
· 使用引理 `Set.uIcc_subset_uIcc_right`：uIcc_subset_uIcc_right (h : x in [[a, b]]) :
 [[x, b]] subseteq [[a, b]]

--- 原说明 ---
If `x ∈ [a, b]`, then the distance between `c` and `b` is less than or equal to
that of `a` and `b`
-/
theorem abs_sub_right_of_mem_uIcc (h : c ∈ [[a, b]]) : |b - c| ≤ |b - a| :=
  abs_sub_le_of_uIcc_subset_uIcc <| uIcc_subset_uIcc_right h

end LinearOrderedAddCommGroup

section GroupWithZero

section MulPos

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}

@[simp]
/-
**Set.preimage_mul_const_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Iic : (fun x => x * a) ⁻¹' Iic b = Iic (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `le_div_iff_mul_le`：le_div_iff_mul_le : a <= c / b ↔ a * b <= c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_mul_const_Iic₀ (a : G₀) (h : 0 < c) : (· * c) ⁻¹' Iic a = Iic (a / c) := by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Iic a

@[simp]
/-
**Set.preimage_mul_const_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Ici : (fun x => x * a) ⁻¹' Ici b = Ici (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `div_le_iff_le_mul`：div_le_iff_le_mul : a / c <= b ↔ a <= b * c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_mul_const_Ici₀ (a : G₀) (h : 0 < c) : (· * c) ⁻¹' Ici a = Ici (a / c) := by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Ici a

@[simp]
/-
**Set.preimage_mul_const_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Ioi : (fun x => x * a) ⁻¹' Ioi b = Ioi (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `div_lt_iff_lt_mul`：div_lt_iff_lt_mul : a / c < b ↔ a < b * c
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_mul_const_Ioi₀ (a : G₀) (h : 0 < c) : (· * c) ⁻¹' Ioi a = Ioi (a / c) := by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Ioi a

@[simp]
/-
**Set.preimage_mul_const_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Iio : (fun x => x * a) ⁻¹' Iio b = Iio (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `lt_div_iff_mul_lt`：lt_div_iff_mul_lt : a < c / b ↔ a * b < c
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_mul_const_Iio₀ (a : G₀) (h : 0 < c) : (· * c) ⁻¹' Iio a = Iio (a / c) := by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Iio a

@[simp]
/-
**Set.preimage_mul_const_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Icc : (fun x => x * a) ⁻¹' Icc b c = Icc (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_mul_const_Ici`：preimage_mul_const_Ici : (fun x => x * a) ⁻¹
' Ici b = Ici (b / a)
· 使用定理 `Set.preimage_mul_const_Iic`：preimage_mul_const_Iic : (fun x => x * a) ⁻¹
' Iic b = Iic (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_mul_const_Icc₀ (a b : G₀) (h : 0 < c) :
    (· * c) ⁻¹' Icc a b = Icc (a / c) (b / c) := by simp [← Ici_inter_Iic, h]

@[simp]
/-
**Set.preimage_mul_const_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Ioo : (fun x => x * a) ⁻¹' Ioo b c = Ioo (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_mul_const_Ioi`：preimage_mul_const_Ioi : (fun x => x * a) ⁻¹
' Ioi b = Ioi (b / a)
· 使用定理 `Set.preimage_mul_const_Iio`：preimage_mul_const_Iio : (fun x => x * a) ⁻¹
' Iio b = Iio (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_mul_const_Ioo₀ (a b : G₀) (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ioo a b = Ioo (a / c) (b / c) := by simp [← Ioi_inter_Iio, h]

@[simp]
/-
**Set.preimage_mul_const_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Ioc : (fun x => x * a) ⁻¹' Ioc b c = Ioc (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_mul_const_Ioi`：preimage_mul_const_Ioi : (fun x => x * a) ⁻¹
' Ioi b = Ioi (b / a)
· 使用定理 `Set.preimage_mul_const_Iic`：preimage_mul_const_Iic : (fun x => x * a) ⁻¹
' Iic b = Iic (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_mul_const_Ioc₀ (a b : G₀) (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ioc a b = Ioc (a / c) (b / c) := by simp [← Ioi_inter_Iic, h]

@[simp]
/-
**Set.preimage_mul_const_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Ico : (fun x => x * a) ⁻¹' Ico b c = Ico (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_mul_const_Ici`：preimage_mul_const_Ici : (fun x => x * a) ⁻¹
' Ici b = Ici (b / a)
· 使用定理 `Set.preimage_mul_const_Iio`：preimage_mul_const_Iio : (fun x => x * a) ⁻¹
' Iio b = Iio (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_mul_const_Ico₀ (a b : G₀) (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ico a b = Ico (a / c) (b / c) := by simp [← Ici_inter_Iio, h]
/-
**Set.image_mul_right_Icc'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_right_Icc' (a b : G₀) (h : 0 < c) : (· * c) '' Icc a b = Icc (a 
* c) (b * c)
参数：a b : G₀；h : 0 < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.image_Icc`：image_Icc (e : α ≃o β) (a b : α) : e '' Icc a b = Ic
c (e a) (e b)
-/
theorem image_mul_right_Icc' (a b : G₀) (h : 0 < c) :
    (· * c) '' Icc a b = Icc (a * c) (b * c) :=
  (OrderIso.mulRight₀ c h).image_Icc a b
/-
**Set.image_mul_right_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_right_Icc (hab : a <= b) (hc : 0 <= c) : (· * c) '' Icc a b = Ic
c (a * c) (b * c)
参数：hab : a <= b；hc : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.image_mul_right_Icc'`：image_mul_right_Icc' (a b : G₀) (h : 0 < c) : 
(· * c) '' Icc a b = Icc (a * c) (b * c)
-/
theorem image_mul_right_Icc (hab : a ≤ b) (hc : 0 ≤ c) :
    (· * c) '' Icc a b = Icc (a * c) (b * c) := by
  cases eq_or_lt_of_le hc
  · subst c
    simp [(nonempty_Icc.2 hab).image_const]
  exact image_mul_right_Icc' a b ‹0 < c›
/-
**Set.image_mul_right_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_right_Ioo (a b : G₀) (h : 0 < c) : (fun x => x * c) '' Ioo a b =
 Ioo (a * c) (b * c)
参数：a b : G₀；h : 0 < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.image_Ioo`：image_Ioo (e : α ≃o β) (a b : α) : e '' Ioo a b = Io
o (e a) (e b)
-/
theorem image_mul_right_Ioo (a b : G₀) (h : 0 < c) :
    (fun x => x * c) '' Ioo a b = Ioo (a * c) (b * c) :=
  (OrderIso.mulRight₀ c h).image_Ioo a b
/-
**Set.image_mul_right_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_right_Ico (a b : G₀) (h : 0 < c) : (fun x => x * c) '' Ico a b =
 Ico (a * c) (b * c)
参数：a b : G₀；h : 0 < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.image_Ico`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] 
[inst_1 : Preorder β] (e : α ≃o β) (b a : α),   ⇑e '' Set.Ico b a = Set.Ico (e b
) (e a)
-/
theorem image_mul_right_Ico (a b : G₀) (h : 0 < c) :
    (fun x => x * c) '' Ico a b = Ico (a * c) (b * c) :=
  (OrderIso.mulRight₀ c h).image_Ico a b
/-
**Set.image_mul_right_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_right_Ioc (a b : G₀) (h : 0 < c) : (fun x => x * c) '' Ioc a b =
 Ioc (a * c) (b * c)
参数：a b : G₀；h : 0 < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.image_Ioc`：image_Ioc (e : α ≃o β) (a b : α) : e '' Ioc a b = Io
c (e a) (e b)
-/
theorem image_mul_right_Ioc (a b : G₀) (h : 0 < c) :
    (fun x => x * c) '' Ioc a b = Ioc (a * c) (b * c) :=
  (OrderIso.mulRight₀ c h).image_Ioc a b

end MulPos

section PosMul

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

/-
**Set.image_mul_left_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_left_Ici (h : 0 < a) (b : G₀) : (a * ·) '' Ici b = Ici (a * b)
参数：h : 0 < a；b : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.image_Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] 
[inst_1 : Preorder β] (e : α ≃o β) (a : α),   ⇑e '' Set.Ici a = Set.Ici (e a)
-/
theorem image_mul_left_Ici (h : 0 < a) (b : G₀) : (a * ·) '' Ici b = Ici (a * b) :=
  (OrderIso.mulLeft₀ a h).image_Ici b
/-
**Set.image_mul_left_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_left_Iic (h : 0 < a) (b : G₀) : (a * ·) '' Iic b = Iic (a * b)
参数：h : 0 < a；b : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.image_Iic`：image_Iic (e : α ≃o β) (a : α) : e '' Iic a = Iic (e
 a)
-/
theorem image_mul_left_Iic (h : 0 < a) (b : G₀) : (a * ·) '' Iic b = Iic (a * b) :=
  (OrderIso.mulLeft₀ a h).image_Iic b
/-
**Set.image_mul_left_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_left_Ioi (h : 0 < a) (b : G₀) : (a * ·) '' Ioi b = Ioi (a * b)
参数：h : 0 < a；b : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.image_Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] 
[inst_1 : Preorder β] (e : α ≃o β) (a : α),   ⇑e '' Set.Ioi a = Set.Ioi (e a)
-/
theorem image_mul_left_Ioi (h : 0 < a) (b : G₀) : (a * ·) '' Ioi b = Ioi (a * b) :=
  (OrderIso.mulLeft₀ a h).image_Ioi b
/-
**Set.image_mul_left_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_left_Iio (h : 0 < a) (b : G₀) : (a * ·) '' Iio b = Iio (a * b)
参数：h : 0 < a；b : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.image_Iio`：image_Iio (e : α ≃o β) (a : α) : e '' Iio a = Iio (e
 a)
-/
theorem image_mul_left_Iio (h : 0 < a) (b : G₀) : (a * ·) '' Iio b = Iio (a * b) :=
  (OrderIso.mulLeft₀ a h).image_Iio b
/-
**Set.image_mul_left_Icc'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_left_Icc' (h : 0 < a) (b c : G₀) : (a * ·) '' Icc b c = Icc (a *
 b) (a * c)
参数：h : 0 < a；b c : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.image_Icc`：image_Icc (e : α ≃o β) (a b : α) : e '' Icc a b = Ic
c (e a) (e b)
-/
theorem image_mul_left_Icc' (h : 0 < a) (b c : G₀) :
    (a * ·) '' Icc b c = Icc (a * b) (a * c) :=
  (OrderIso.mulLeft₀ a h).image_Icc b c
/-
**Set.image_mul_left_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_left_Icc (ha : 0 <= a) (hbc : b <= c) : (a * ·) '' Icc b c = Icc
 (a * b) (a * c)
参数：ha : 0 <= a；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.image_mul_left_Icc'`：image_mul_left_Icc' (h : 0 < a) (b c : G₀) : (a
 * ·) '' Icc b c = Icc (a * b) (a * c)
-/
theorem image_mul_left_Icc (ha : 0 ≤ a) (hbc : b ≤ c) :
    (a * ·) '' Icc b c = Icc (a * b) (a * c) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [(nonempty_Icc.2 hbc).image_const]
  · exact image_mul_left_Icc' ha b c
/-
**Set.image_mul_left_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_left_Ioo (h : 0 < a) (b c : G₀) : (a * ·) '' Ioo b c = Ioo (a * 
b) (a * c)
参数：h : 0 < a；b c : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.image_Ioo`：image_Ioo (e : α ≃o β) (a b : α) : e '' Ioo a b = Io
o (e a) (e b)
-/
theorem image_mul_left_Ioo (h : 0 < a) (b c : G₀) : (a * ·) '' Ioo b c = Ioo (a * b) (a * c) :=
  (OrderIso.mulLeft₀ a h).image_Ioo b c
/-
**Set.image_mul_left_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_left_Ico (h : 0 < a) (b c : G₀) : (a * ·) '' Ico b c = Ico (a * 
b) (a * c)
参数：h : 0 < a；b c : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.image_Ico`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] 
[inst_1 : Preorder β] (e : α ≃o β) (b a : α),   ⇑e '' Set.Ico b a = Set.Ico (e b
) (e a)
-/
theorem image_mul_left_Ico (h : 0 < a) (b c : G₀) :
    (a * ·) '' Ico b c = Ico (a * b) (a * c) :=
  (OrderIso.mulLeft₀ a h).image_Ico b c
/-
**Set.image_mul_left_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_left_Ioc (h : 0 < a) (b c : G₀) : (a * ·) '' Ioc b c = Ioc (a * 
b) (a * c)
参数：h : 0 < a；b c : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.image_Ioc`：image_Ioc (e : α ≃o β) (a b : α) : e '' Ioc a b = Io
c (e a) (e b)
-/
theorem image_mul_left_Ioc (h : 0 < a) (b c : G₀) :
    (a * ·) '' Ioc b c = Ioc (a * b) (a * c) :=
  (OrderIso.mulLeft₀ a h).image_Ioc b c
/-
**Set.image_const_mul_Ioi_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_const_mul_Ioi_zero (ha : 0 < a) : (a * ·) '' Ioi 0 = Ioi 0
参数：ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_left_Ioi`：image_mul_left_Ioi (h : 0 < a) (b : G₀) : (a * ·
) '' Ioi b = Ioi (a * b)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem image_const_mul_Ioi_zero (ha : 0 < a) :
    (a * ·) '' Ioi 0 = Ioi 0 := by
  rw [image_mul_left_Ioi ha, mul_zero]

end PosMul

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀]
  [MulPosReflectLT G₀] {a : G₀}

/-- The (pre)image under `inv` of `Ioo 0 a` is `Ioi a⁻¹`. -/
/-
**Set.inv_Ioo_0_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inv_Ioo_0_left (ha : 0 < a) : (Ioo 0 a)⁻¹ = Ioi a⁻¹
参数：ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `inv_lt_of_inv_lt₀`：inv_lt_of_inv_lt₀ (ha : 0 < a) (h : a⁻¹ < b) : b⁻¹ < 
a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c

--- 原说明 ---
The (pre)image under `inv` of `Ioo 0 a` is `Ioi a⁻¹`.
-/
theorem inv_Ioo_0_left (ha : 0 < a) : (Ioo 0 a)⁻¹ = Ioi a⁻¹ := by
  ext x
  exact ⟨fun h ↦ inv_lt_of_inv_lt₀ (inv_pos.1 h.1) h.2,
         fun h ↦ ⟨inv_pos.2 <| (inv_pos.2 ha).trans h, inv_lt_of_inv_lt₀ ha h⟩⟩
/-
**Set.inv_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrder α] [IsOrdered
Monoid α] (a : α), (Set.Ioi a)⁻¹ = Set.Iio a⁻¹
参数：a : α；Set.Ioi a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `lt_inv'`：lt_inv' : a < b⁻¹ ↔ b < a⁻¹
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
-/
theorem inv_Ioi₀ (ha : 0 < a) : (Ioi a)⁻¹ = Ioo 0 a⁻¹ := by
  rw [inv_eq_iff_eq_inv, inv_Ioo_0_left (inv_pos.2 ha), inv_inv]

end GroupWithZero

/-!
### Commutative group with zero

The only reason why we need `G₀` to be commutative in this section
is that we write `a / c`, not `c⁻¹ * a`.

TODO: decide if we should reformulate the lemmas in terms of `c⁻¹ * a`
instead of depending on commutativity.
-/

section CommGroupWithZero

variable {G₀ : Type*} [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

@[simp]
/-
**Set.preimage_const_mul_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Iic : (fun x => a * x) ⁻¹' Iic b = Iic (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `le_div_iff_mul_le'`：le_div_iff_mul_le' : b <= c / a ↔ a * b <= c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_const_mul_Iic₀ (a : G₀) (h : 0 < c) : (c * ·) ⁻¹' Iic a = Iic (a / c) :=
  ext fun _x => (le_div_iff₀' h).symm

@[simp]
/-
**Set.preimage_const_mul_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ici : (fun x => a * x) ⁻¹' Ici b = Ici (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `div_le_iff_le_mul'`：div_le_iff_le_mul' : a / b <= c ↔ a <= b * c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_const_mul_Ici₀ (a : G₀) (h : 0 < c) : (c * ·) ⁻¹' Ici a = Ici (a / c) :=
  ext fun _x => (div_le_iff₀' h).symm

@[simp]
/-
**Set.preimage_const_mul_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Icc : (fun x => a * x) ⁻¹' Icc b c = Icc (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_const_mul_Ici`：preimage_const_mul_Ici : (fun x => a * x) ⁻¹
' Ici b = Ici (b / a)
· 使用定理 `Set.preimage_const_mul_Iic`：preimage_const_mul_Iic : (fun x => a * x) ⁻¹
' Iic b = Iic (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_const_mul_Icc₀ (a b : G₀) {c : G₀} (h : 0 < c) :
    (c * ·) ⁻¹' Icc a b = Icc (a / c) (b / c) := by simp [← Ici_inter_Iic, h]

@[simp]
/-
**Set.preimage_const_mul_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Iio : (fun x => a * x) ⁻¹' Iio b = Iio (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `lt_div_iff_mul_lt'`：lt_div_iff_mul_lt' : b < c / a ↔ a * b < c
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_const_mul_Iio₀ (a : G₀) (h : 0 < c) : (c * ·) ⁻¹' Iio a = Iio (a / c) :=
  ext fun _x => (lt_div_iff₀' h).symm

@[simp]
/-
**Set.preimage_const_mul_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ioi : (fun x => a * x) ⁻¹' Ioi b = Ioi (b / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `div_lt_iff_lt_mul'`：div_lt_iff_lt_mul' : a / b < c ↔ a < b * c
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem preimage_const_mul_Ioi₀ (a : G₀) (h : 0 < c) : (c * ·) ⁻¹' Ioi a = Ioi (a / c) :=
  ext fun _x => (div_lt_iff₀' h).symm

@[simp]
/-
**Set.preimage_const_mul_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ioo : (fun x => a * x) ⁻¹' Ioo b c = Ioo (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_const_mul_Ioi`：preimage_const_mul_Ioi : (fun x => a * x) ⁻¹
' Ioi b = Ioi (b / a)
· 使用定理 `Set.preimage_const_mul_Iio`：preimage_const_mul_Iio : (fun x => a * x) ⁻¹
' Iio b = Iio (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_const_mul_Ioo₀ (a b : G₀) (h : 0 < c) :
    (c * ·) ⁻¹' Ioo a b = Ioo (a / c) (b / c) := by simp [← Ioi_inter_Iio, h]

@[simp]
/-
**Set.preimage_const_mul_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ioc : (fun x => a * x) ⁻¹' Ioc b c = Ioc (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_const_mul_Ioi`：preimage_const_mul_Ioi : (fun x => a * x) ⁻¹
' Ioi b = Ioi (b / a)
· 使用定理 `Set.preimage_const_mul_Iic`：preimage_const_mul_Iic : (fun x => a * x) ⁻¹
' Iic b = Iic (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_const_mul_Ioc₀ (a b : G₀) (h : 0 < c) :
    (c * ·) ⁻¹' Ioc a b = Ioc (a / c) (b / c) := by simp [← Ioi_inter_Iic, h]

@[simp]
/-
**Set.preimage_const_mul_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ico : (fun x => a * x) ⁻¹' Ico b c = Ico (b / a) (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_const_mul_Ici`：preimage_const_mul_Ici : (fun x => a * x) ⁻¹
' Ici b = Ici (b / a)
· 使用定理 `Set.preimage_const_mul_Iio`：preimage_const_mul_Iio : (fun x => a * x) ⁻¹
' Iio b = Iio (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_const_mul_Ico₀ (a b : G₀) (h : 0 < c) :
    (c * ·) ⁻¹' Ico a b = Ico (a / c) (b / c) := by simp [← Ici_inter_Iio, h]

end CommGroupWithZero

/-!
### Images under `x ↦ a * x + b` in a semifield
-/

section OrderedSemifield

variable {K : Type*} [DivisionSemiring K] [PartialOrder K] [PosMulReflectLT K]
  [IsOrderedCancelAddMonoid K] [ExistsAddOfLE K] {a : K}

@[simp]
/-
**Set.image_affine_Icc'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_affine_Icc' (h : 0 < a) (b c d : K) : (a * · + b) '' Icc c d = Icc (
a * c + b) (a * d + b)
参数：h : 0 < a；b c d : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_left_Icc'`：image_mul_left_Icc' (h : 0 < a) (b c : G₀) : (a
 * ·) '' Icc b c = Icc (a * b) (a * c)
· 使用定理 `Set.image_add_const_Icc`：image_add_const_Icc : (fun x => x + a) '' Icc b
 c = Icc (b + a) (c + a)
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem image_affine_Icc' (h : 0 < a) (b c d : K) :
    (a * · + b) '' Icc c d = Icc (a * c + b) (a * d + b) := by
  suffices (· + b) '' (a * ·) '' Icc c d = Icc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Icc' h, image_add_const_Icc]

@[simp]
/-
**Set.image_affine_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_affine_Ico (h : 0 < a) (b c d : K) : (a * · + b) '' Ico c d = Ico (a
 * c + b) (a * d + b)
参数：h : 0 < a；b c d : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_left_Ico`：image_mul_left_Ico (h : 0 < a) (b c : G₀) : (a *
 ·) '' Ico b c = Ico (a * b) (a * c)
· 使用定理 `Set.image_add_const_Ico`：image_add_const_Ico : (fun x => x + a) '' Ico b
 c = Ico (b + a) (c + a)
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem image_affine_Ico (h : 0 < a) (b c d : K) :
    (a * · + b) '' Ico c d = Ico (a * c + b) (a * d + b) := by
  suffices (· + b) '' (a * ·) '' Ico c d = Ico (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Ico h, image_add_const_Ico]

@[simp]
/-
**Set.image_affine_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_affine_Ioc (h : 0 < a) (b c d : K) : (a * · + b) '' Ioc c d = Ioc (a
 * c + b) (a * d + b)
参数：h : 0 < a；b c d : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_left_Ioc`：image_mul_left_Ioc (h : 0 < a) (b c : G₀) : (a *
 ·) '' Ioc b c = Ioc (a * b) (a * c)
· 使用定理 `Set.image_add_const_Ioc`：image_add_const_Ioc : (fun x => x + a) '' Ioc b
 c = Ioc (b + a) (c + a)
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem image_affine_Ioc (h : 0 < a) (b c d : K) :
    (a * · + b) '' Ioc c d = Ioc (a * c + b) (a * d + b) := by
  suffices (· + b) '' (a * ·) '' Ioc c d = Ioc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Ioc h, image_add_const_Ioc]

@[simp]
/-
**Set.image_affine_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_affine_Ioo (h : 0 < a) (b c d : K) : (a * · + b) '' Ioo c d = Ioo (a
 * c + b) (a * d + b)
参数：h : 0 < a；b c d : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_left_Ioo`：image_mul_left_Ioo (h : 0 < a) (b c : G₀) : (a *
 ·) '' Ioo b c = Ioo (a * b) (a * c)
· 使用定理 `Set.image_add_const_Ioo`：image_add_const_Ioo : (fun x => x + a) '' Ioo b
 c = Ioo (b + a) (c + a)
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem image_affine_Ioo (h : 0 < a) (b c d : K) :
    (a * · + b) '' Ioo c d = Ioo (a * c + b) (a * d + b) := by
  suffices (· + b) '' (a * ·) '' Ioo c d = Ioo (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Ioo h, image_add_const_Ioo]

end OrderedSemifield

/-!
### Multiplication and inverse in a field
-/

section LinearOrderedField

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

@[simp]
/-
**Set.preimage_mul_const_Iio_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Iio_of_neg (a : α) {c : α} (h : c < 0) : (fun x => x * 
c) ⁻¹' Iio a = Ioi (a / c)
参数：a : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `div_lt_iff_of_neg`：div_lt_iff_of_neg (hc : c < 0) : b / c < a ↔ a * c < 
b where mp h
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem preimage_mul_const_Iio_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Iio a = Ioi (a / c) :=
  ext fun _x => (div_lt_iff_of_neg h).symm

@[simp]
/-
**Set.preimage_mul_const_Ioi_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Ioi_of_neg (a : α) {c : α} (h : c < 0) : (fun x => x * 
c) ⁻¹' Ioi a = Iio (a / c)
参数：a : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `lt_div_iff_of_neg`：lt_div_iff_of_neg (hc : c < 0) : a < b / c ↔ b < a * 
c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem preimage_mul_const_Ioi_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioi a = Iio (a / c) :=
  ext fun _x => (lt_div_iff_of_neg h).symm

@[simp]
/-
**Set.preimage_mul_const_Iic_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Iic_of_neg (a : α) {c : α} (h : c < 0) : (fun x => x * 
c) ⁻¹' Iic a = Ici (a / c)
参数：a : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `div_le_iff_of_neg`：div_le_iff_of_neg (hc : c < 0) : b / c <= a ↔ a * c <
= b where mp h
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem preimage_mul_const_Iic_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Iic a = Ici (a / c) :=
  ext fun _x => (div_le_iff_of_neg h).symm

@[simp]
/-
**Set.preimage_mul_const_Ici_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Ici_of_neg (a : α) {c : α} (h : c < 0) : (fun x => x * 
c) ⁻¹' Ici a = Iic (a / c)
参数：a : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `le_div_iff_of_neg`：le_div_iff_of_neg (hc : c < 0) : a <= b / c ↔ b <= a 
* c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem preimage_mul_const_Ici_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ici a = Iic (a / c) :=
  ext fun _x => (le_div_iff_of_neg h).symm

@[simp]
/-
**Set.preimage_mul_const_Ioo_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Ioo_of_neg (a b : α) {c : α} (h : c < 0) : (fun x => x 
* c) ⁻¹' Ioo a b = Ioo (b / c) (a / c)
参数：a b : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.preimage_mul_const_Iio_of_neg`：preimage_mul_const_Iio_of_neg (a : α)
 {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Iio a = Ioi (a / c)
· 使用定理 `Set.preimage_mul_const_Ioi_of_neg`：preimage_mul_const_Ioi_of_neg (a : α)
 {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Ioi a = Iio (a / c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_mul_const_Ioo_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioo a b = Ioo (b / c) (a / c) := by simp [← Ioi_inter_Iio, h, inter_comm]

@[simp]
/-
**Set.preimage_mul_const_Ioc_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Ioc_of_neg (a b : α) {c : α} (h : c < 0) : (fun x => x 
* c) ⁻¹' Ioc a b = Ico (b / c) (a / c)
参数：a b : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_mul_const_Iic_of_neg`：preimage_mul_const_Iic_of_neg (a : α)
 {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Iic a = Ici (a / c)
· 使用定理 `Set.preimage_mul_const_Ioi_of_neg`：preimage_mul_const_Ioi_of_neg (a : α)
 {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Ioi a = Iio (a / c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_mul_const_Ioc_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioc a b = Ico (b / c) (a / c) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, h, inter_comm]

@[simp]
/-
**Set.preimage_mul_const_Ico_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Ico_of_neg (a b : α) {c : α} (h : c < 0) : (fun x => x 
* c) ⁻¹' Ico a b = Ioc (b / c) (a / c)
参数：a b : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_mul_const_Ici_of_neg`：preimage_mul_const_Ici_of_neg (a : α)
 {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Ici a = Iic (a / c)
· 使用定理 `Set.preimage_mul_const_Iio_of_neg`：preimage_mul_const_Iio_of_neg (a : α)
 {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Iio a = Ioi (a / c)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_mul_const_Ico_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ico a b = Ioc (b / c) (a / c) := by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, h, inter_comm]

@[simp]
/-
**Set.preimage_mul_const_Icc_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_Icc_of_neg (a b : α) {c : α} (h : c < 0) : (fun x => x 
* c) ⁻¹' Icc a b = Icc (b / c) (a / c)
参数：a b : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_mul_const_Ici_of_neg`：preimage_mul_const_Ici_of_neg (a : α)
 {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Ici a = Iic (a / c)
· 使用定理 `Set.preimage_mul_const_Iic_of_neg`：preimage_mul_const_Iic_of_neg (a : α)
 {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Iic a = Ici (a / c)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_mul_const_Icc_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Icc a b = Icc (b / c) (a / c) := by simp [← Ici_inter_Iic, h, inter_comm]

@[simp]
/-
**Set.preimage_const_mul_Iio_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Iio_of_neg (a : α) {c : α} (h : c < 0) : (c * ·) ⁻¹' Ii
o a = Ioi (a / c)
参数：a : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Iio_of_neg`：preimage_mul_const_Iio_of_neg (a : α)
 {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Iio a = Ioi (a / c)
-/
theorem preimage_const_mul_Iio_of_neg (a : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Iio a = Ioi (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Iio_of_neg a h

@[simp]
/-
**Set.preimage_const_mul_Ioi_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ioi_of_neg (a : α) {c : α} (h : c < 0) : (c * ·) ⁻¹' Io
i a = Iio (a / c)
参数：a : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Ioi_of_neg`：preimage_mul_const_Ioi_of_neg (a : α)
 {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Ioi a = Iio (a / c)
-/
theorem preimage_const_mul_Ioi_of_neg (a : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ioi a = Iio (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioi_of_neg a h

@[simp]
/-
**Set.preimage_const_mul_Iic_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Iic_of_neg (a : α) {c : α} (h : c < 0) : (c * ·) ⁻¹' Ii
c a = Ici (a / c)
参数：a : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Iic_of_neg`：preimage_mul_const_Iic_of_neg (a : α)
 {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Iic a = Ici (a / c)
-/
theorem preimage_const_mul_Iic_of_neg (a : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Iic a = Ici (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Iic_of_neg a h

@[simp]
/-
**Set.preimage_const_mul_Ici_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ici_of_neg (a : α) {c : α} (h : c < 0) : (c * ·) ⁻¹' Ic
i a = Iic (a / c)
参数：a : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Ici_of_neg`：preimage_mul_const_Ici_of_neg (a : α)
 {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Ici a = Iic (a / c)
-/
theorem preimage_const_mul_Ici_of_neg (a : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ici a = Iic (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ici_of_neg a h

@[simp]
/-
**Set.preimage_const_mul_Ioo_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ioo_of_neg (a b : α) {c : α} (h : c < 0) : (c * ·) ⁻¹' 
Ioo a b = Ioo (b / c) (a / c)
参数：a b : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Ioo_of_neg`：preimage_mul_const_Ioo_of_neg (a b : 
α) {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Ioo a b = Ioo (b / c) (a / c)
-/
theorem preimage_const_mul_Ioo_of_neg (a b : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ioo a b = Ioo (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioo_of_neg a b h

@[simp]
/-
**Set.preimage_const_mul_Ioc_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ioc_of_neg (a b : α) {c : α} (h : c < 0) : (c * ·) ⁻¹' 
Ioc a b = Ico (b / c) (a / c)
参数：a b : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Ioc_of_neg`：preimage_mul_const_Ioc_of_neg (a b : 
α) {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Ioc a b = Ico (b / c) (a / c)
-/
theorem preimage_const_mul_Ioc_of_neg (a b : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ioc a b = Ico (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioc_of_neg a b h

@[simp]
/-
**Set.preimage_const_mul_Ico_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ico_of_neg (a b : α) {c : α} (h : c < 0) : (c * ·) ⁻¹' 
Ico a b = Ioc (b / c) (a / c)
参数：a b : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Ico_of_neg`：preimage_mul_const_Ico_of_neg (a b : 
α) {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Ico a b = Ioc (b / c) (a / c)
-/
theorem preimage_const_mul_Ico_of_neg (a b : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ico a b = Ioc (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ico_of_neg a b h

@[simp]
/-
**Set.preimage_const_mul_Icc_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Icc_of_neg (a b : α) {c : α} (h : c < 0) : (c * ·) ⁻¹' 
Icc a b = Icc (b / c) (a / c)
参数：a b : α；h : c < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Icc_of_neg`：preimage_mul_const_Icc_of_neg (a b : 
α) {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Icc a b = Icc (b / c) (a / c)
-/
theorem preimage_const_mul_Icc_of_neg (a b : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Icc a b = Icc (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Icc_of_neg a b h

@[simp]
/-
**Set.preimage_mul_const_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mul_const_uIcc (ha : a != 0) (b c : α) : (· * a) ⁻¹' [[b, c]] = [
[b / a, c / a]]
参数：ha : a != 0；b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_mul_const_Icc_of_neg`：preimage_mul_const_Icc_of_neg (a b : 
α) {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' Icc a b = Icc (b / c) (a / c)
· 使用定理 `min_div_div_right_of_nonpos`：min_div_div_right_of_nonpos (hc : c <= 0) (
a b : α) : min (a / c) (b / c) = max a b / c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `max_div_div_right_of_nonpos`：max_div_div_right_of_nonpos (hc : c <= 0) (
a b : α) : max (a / c) (b / c) = min a b / c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.preimage_mul_const_Icc₀`：preimage_mul_const_Icc₀ (a b : G₀) (h : 0 <
 c) : (· * c) ⁻¹' Icc a b = Icc (a / c) (b / c)
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `min_div_div_right`：min_div_div_right {c : α} (hc : 0 <= c) (a b : α) : m
in (a / c) (b / c) = min a b / c
· 使用定理 `max_div_div_right`：max_div_div_right {c : α} (hc : 0 <= c) (a b : α) : m
ax (a / c) (b / c) = max a b / c
-/
theorem preimage_mul_const_uIcc (ha : a ≠ 0) (b c : α) :
    (· * a) ⁻¹' [[b, c]] = [[b / a, c / a]] :=
  (lt_or_gt_of_ne ha).elim
    (fun h => by
      simp [← Icc_min_max, h, h.le, min_div_div_right_of_nonpos, max_div_div_right_of_nonpos])
    fun ha : 0 < a => by simp [← Icc_min_max, ha, ha.le, min_div_div_right, max_div_div_right]

@[simp]
/-
**Set.preimage_const_mul_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_uIcc (ha : a != 0) (b c : α) : (a * ·) ⁻¹' [[b, c]] = [
[b / a, c / a]]
参数：ha : a != 0；b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_mul_const_uIcc`：preimage_mul_const_uIcc (ha : a != 0) (b c 
: α) : (· * a) ⁻¹' [[b, c]] = [[b / a, c / a]]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_const_mul_uIcc (ha : a ≠ 0) (b c : α) :
    (a * ·) ⁻¹' [[b, c]] = [[b / a, c / a]] := by
  simp only [← preimage_mul_const_uIcc ha, mul_comm]

@[simp]
/-
**Set.preimage_div_const_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_div_const_uIcc (ha : a != 0) (b c : α) : (fun x => x / a) ⁻¹' [[b
, c]] = [[b * a, c * a]]
参数：ha : a != 0；b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.preimage_mul_const_uIcc`：preimage_mul_const_uIcc (ha : a != 0) (b c 
: α) : (· * a) ⁻¹' [[b, c]] = [[b / a, c / a]]
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_div_const_uIcc (ha : a ≠ 0) (b c : α) :
    (fun x => x / a) ⁻¹' [[b, c]] = [[b * a, c * a]] := by
  simp only [div_eq_mul_inv, preimage_mul_const_uIcc (inv_ne_zero ha), inv_inv]
/-
**Set.preimage_const_mul_Ioi_or_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：preimage_const_mul_Ioi_or_Iio (hb : a != 0) {U V : Set α} (hU : U in {s | 
exists a, s = Ioi a ∨ s = Iio a}) (hV : V = (a * ·) ⁻¹' U) : V in {s | exists a,
 s = Ioi a ∨ s = Iio a}
参数：hb : a != 0；hU : U in {s | exists a, s = Ioi a ∨ s = Iio a}；hV : V = (a * ·) 
⁻¹' U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `Set.preimage_const_mul_Ioi_of_neg`：preimage_const_mul_Ioi_of_neg (a : α)
 {c : α} (h : c < 0) : (c * ·) ⁻¹' Ioi a = Iio (a / c)
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Set.preimage_const_mul_Ioi₀`：preimage_const_mul_Ioi₀ (a : G₀) (h : 0 < c
) : (c * ·) ⁻¹' Ioi a = Ioi (a / c)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Set.preimage_const_mul_Iio_of_neg`：preimage_const_mul_Iio_of_neg (a : α)
 {c : α} (h : c < 0) : (c * ·) ⁻¹' Iio a = Ioi (a / c)
· 使用定理 `Set.preimage_const_mul_Iio₀`：preimage_const_mul_Iio₀ (a : G₀) (h : 0 < c
) : (c * ·) ⁻¹' Iio a = Iio (a / c)
-/
lemma preimage_const_mul_Ioi_or_Iio (hb : a ≠ 0) {U V : Set α}
    (hU : U ∈ {s | ∃ a, s = Ioi a ∨ s = Iio a}) (hV : V = (a * ·) ⁻¹' U) :
    V ∈ {s | ∃ a, s = Ioi a ∨ s = Iio a} := by
  obtain ⟨aU, (haU | haU)⟩ := hU <;>
  simp only [hV, haU, mem_ofPred_eq] <;>
  use a⁻¹ * aU <;>
  rcases lt_or_gt_of_ne hb with (hb | hb)
  · right; rw [Set.preimage_const_mul_Ioi_of_neg _ hb, div_eq_inv_mul]
  · left; rw [Set.preimage_const_mul_Ioi₀ _ hb, div_eq_inv_mul]
  · left; rw [Set.preimage_const_mul_Iio_of_neg _ hb, div_eq_inv_mul]
  · right; rw [Set.preimage_const_mul_Iio₀ _ hb, div_eq_inv_mul]

@[simp]
/-
**Set.image_mul_const_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mul_const_uIcc (a b c : α) : (· * a) '' [[b, c]] = [[b * a, c * a]]
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.preimage_div_const_uIcc`：preimage_div_const_uIcc (ha : a != 0) (b c 
: α) : (fun x => x / a) ⁻¹' [[b, c]] = [[b * a, c * a]]
-/
theorem image_mul_const_uIcc (a b c : α) : (· * a) '' [[b, c]] = [[b * a, c * a]] :=
  if ha : a = 0 then by simp [ha]
  else calc
    (fun x => x * a) '' [[b, c]] = (· * a⁻¹) ⁻¹' [[b, c]] :=
      (Units.mk0 a ha).mulRight.image_eq_preimage_symm _
    _ = (fun x => x / a) ⁻¹' [[b, c]] := by simp only [div_eq_mul_inv]
    _ = [[b * a, c * a]] := preimage_div_const_uIcc ha _ _

@[simp]
/-
**Set.image_const_mul_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_const_mul_uIcc (a b c : α) : (a * ·) '' [[b, c]] = [[a * b, a * c]]
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.image_mul_const_uIcc`：image_mul_const_uIcc (a b c : α) : (· * a) '' 
[[b, c]] = [[b * a, c * a]]
-/
theorem image_const_mul_uIcc (a b c : α) : (a * ·) '' [[b, c]] = [[a * b, a * c]] := by
  simpa only [mul_comm] using image_mul_const_uIcc a b c

@[simp]
/-
**Set.image_div_const_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_div_const_uIcc (a b c : α) : (fun x => x / a) '' [[b, c]] = [[b / a,
 c / a]]
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_mul_const_uIcc`：image_mul_const_uIcc (a b c : α) : (· * a) '' 
[[b, c]] = [[b * a, c * a]]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_div_const_uIcc (a b c : α) : (fun x => x / a) '' [[b, c]] = [[b / a, c / a]] := by
  simp only [div_eq_mul_inv, image_mul_const_uIcc]

/-- The (pre)image under `inv` of `Ioo a 0` is `Iio a⁻¹`. -/
/-
**Set.inv_Ioo_0_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inv_Ioo_0_right {a : α} (ha : a < 0) : (Ioo a 0)⁻¹ = Iio a⁻¹
参数：ha : a < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_inv_of_neg`：lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a < b⁻¹ ↔ b < a
⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inv_neg''`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : LinearO
rder G₀] {a : G₀} [PosMulMono G₀], a⁻¹ < 0 ↔ a < 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c

--- 原说明 ---
The (pre)image under `inv` of `Ioo a 0` is `Iio a⁻¹`.
-/
theorem inv_Ioo_0_right {a : α} (ha : a < 0) : (Ioo a 0)⁻¹ = Iio a⁻¹ := by
  ext x
  refine ⟨fun h ↦ (lt_inv_of_neg (inv_neg''.1 h.2) ha).2 h.1, fun h ↦ ?_⟩
  have h' := (h.trans (inv_neg''.2 ha))
  exact ⟨(lt_inv_of_neg ha h').2 h, inv_neg''.2 h'⟩
/-
**Set.inv_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrder α] [IsOrdered
Monoid α] (a : α), (Set.Iio a)⁻¹ = Set.Ioi a⁻¹
参数：a : α；Set.Iio a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `inv_lt'`：inv_lt' : a⁻¹ < b ↔ b⁻¹ < a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
-/
theorem inv_Iio₀ {a : α} (ha : a < 0) : (Iio a)⁻¹ = Ioo a⁻¹ 0 := by
  rw [inv_eq_iff_eq_inv, inv_Ioo_0_right (inv_neg''.2 ha), inv_inv]

end LinearOrderedField

section CanonicallyOrdered

variable {α : Type*} [Monoid α]
variable [Preorder α] [CanonicallyOrderedMul α] [MulRightMono α]

@[to_additive]
/-
**Set.Ici_mul_Ici_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ici_mul_Ici_eq {a b : α} : Ici a * Ici b = Ici (a * b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.Ici_mul_Ici_subset'`：Ici_mul_Ici_subset' (a b : α) : Ici a * Ici b s
ubseteq Ici (a * b)
· 使用定理 `CanonicallyOrderedMul.toMulLeftMono`：∀ {α : Type u} [inst : Semigroup α]
 [inst_1 : LE α] [CanonicallyOrderedMul α], MulLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_mul`：mem_mul : a in s * t ↔ exists x in s, exists y in t, x * y 
= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ExistsMulOfLE.exists_mul_of_le`：∀ {α : Type u} {inst : Mul α} {inst_1 : 
LE α} [self : ExistsMulOfLE α] {a b : α}, a ≤ b → ∃ c, b = a * c
· 使用定理 `CanonicallyOrderedMul.toExistsMulOfLE`：∀ {α : Type u_1} {inst : Mul α} {
inst_1 : LE α} [self : CanonicallyOrderedMul α], ExistsMulOfLE α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ici
 b ↔ b ≤ x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_def`：subset_def : (s subseteq t) = forall x, x in s -> x in t
-/
theorem Ici_mul_Ici_eq {a b : α} :
    Ici a * Ici b = Ici (a * b) := by
  refine Subset.antisymm (Ici_mul_Ici_subset' ..) (subset_def ▸ fun c c_in ↦
    mem_mul.mpr ⟨a, ⟨by simp, ?_⟩⟩)
  obtain ⟨d, hd⟩ := exists_mul_of_le <| mem_Ici.mp c_in
  exact ⟨b * d, by simp [← mul_assoc, hd]⟩

@[to_additive]
/-
**Set.Ici_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : Preorder α] [CanonicallyOrder
edMul α] [MulRightMono α] {a : α} (n : ℕ),   n ≠ 0 → Set.Ici a ^ n = Set.Ici (a 
^ n)
参数：n : ℕ；a ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ici_pow_eq {a : α} :
    ∀ n ≠ 0, Ici a ^ n = Ici (a ^ n)
  | 1, _ => by simp
  | n + 2, _ => by simp [pow_succ _ n.succ, Ici_pow_eq, Ici_mul_Ici_eq]

end CanonicallyOrdered

end Set

