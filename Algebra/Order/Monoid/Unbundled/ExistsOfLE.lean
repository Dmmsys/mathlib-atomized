/-
Copyright (c) 2021 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Order.MinMax

/-!
# Unbundled and weaker forms of canonically ordered monoids

This file provides a Prop-valued mixin for monoids satisfying a one-sided cancellativity property,
namely that there is some `c` such that `b = a + c` if `a ≤ b`. This is particularly useful for
generalising statements from groups/rings/fields that don't mention negation or subtraction to
monoids/semirings/semifields.
-/

public section

universe u
variable {α : Type u}

/-- An ordered additive monoid with one-sided 'subtraction' in the sense that
if `a ≤ b`, then there is some `c` for which `a + c = b`. This is a weaker version
of the condition on canonical orderings defined by `CanonicallyOrderedAdd`. -/
/-
**ExistsAddOfLE** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [Add α] → [LE α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered additive monoid with one-sided 'subtraction' in the sense that
if `a ≤ b`, then there is some `c` for which `a + c = b`. This is a weaker versi
on
of the condition on canonical orderings defined by `CanonicallyOrderedAdd`.
-/
class ExistsAddOfLE (α : Type u) [Add α] [LE α] : Prop where
  /-- For `a ≤ b`, there is a `c` so `b = a + c`. -/
  exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a + c

/-- An ordered monoid with one-sided 'division' in the sense that
if `a ≤ b`, there is some `c` for which `a * c = b`. This is a weaker version
of the condition on canonical orderings defined by `CanonicallyOrderedMul`. -/
@[to_additive]
/-
**ExistsMulOfLE** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [Mul α] → [LE α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered monoid with one-sided 'division' in the sense that
if `a ≤ b`, there is some `c` for which `a * c = b`. This is a weaker version
of the condition on canonical orderings defined by `CanonicallyOrderedMul`.
-/
class ExistsMulOfLE (α : Type u) [Mul α] [LE α] : Prop where
  /-- For `a ≤ b`, `a` left divides `b` -/
  exists_mul_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a * c

export ExistsMulOfLE (exists_mul_of_le)
export ExistsAddOfLE (exists_add_of_le)

-- See note [lower instance priority]
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Group.existsMulOfLE (α : Type u) [Group α] [LE α] : ExistsMulOfLE α :=
  ⟨fun {a b} _ => ⟨a⁻¹ * b, (mul_inv_cancel_left _ _).symm⟩⟩

section MulOneClass
variable [MulOneClass α] [Preorder α] [ExistsMulOfLE α] {a b : α}

/-
**exists_one_le_mul_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : Preorder α] [ExistsMulOfLE
 α] {a b : α} [MulLeftReflectLE α],   a ≤ b → ∃ c, 1 ≤ c ∧ a * c = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsMulOfLE.exists_mul_of_le`：∀ {α : Type u} {inst : Mul α} {inst_1 : 
LE α} [self : ExistsMulOfLE α] {a b : α}, a ≤ b → ∃ c, b = a * c
· 使用定理 `one_le_of_le_mul_right`：one_le_of_le_mul_right [MulLeftReflectLE α] {a b
 : α} (h : a <= a * b) : 1 <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[to_additive] lemma exists_one_le_mul_of_le [MulLeftReflectLE α] (h : a ≤ b) :
    ∃ c, 1 ≤ c ∧ a * c = b := by
  obtain ⟨c, rfl⟩ := exists_mul_of_le h; exact ⟨c, one_le_of_le_mul_right h, rfl⟩
/-
**exists_one_lt_mul_of_lt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : Preorder α] [ExistsMulOfLE
 α] {a b : α} [MulLeftReflectLT α],   a < b → ∃ c, 1 < c ∧ a * c = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsMulOfLE.exists_mul_of_le`：∀ {α : Type u} {inst : Mul α} {inst_1 : 
LE α} [self : ExistsMulOfLE α] {a b : α}, a ≤ b → ∃ c, b = a * c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `one_lt_of_lt_mul_right`：one_lt_of_lt_mul_right [MulLeftReflectLT α] {a b
 : α} (h : a < a * b) : 1 < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[to_additive] lemma exists_one_lt_mul_of_lt' [MulLeftReflectLT α] (h : a < b) :
    ∃ c, 1 < c ∧ a * c = b := by
  obtain ⟨c, rfl⟩ := exists_mul_of_le h.le; exact ⟨c, one_lt_of_lt_mul_right h, rfl⟩
/-
**le_iff_exists_one_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : Preorder α] [ExistsMulOfLE
 α] {a b : α} [MulLeftMono α]   [MulLeftReflectLE α], a ≤ b ↔ ∃ c, 1 ≤ c ∧ a * c
 = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_one_le_mul_of_le`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 :
 Preorder α] [ExistsMulOfLE α] {a b : α} [MulLeftReflectLE α],   a ≤ b → ∃ c, 1 
≤ c ∧ a * c =…
· 使用定理 `le_mul_of_one_le_right'`：le_mul_of_one_le_right' [MulLeftMono α] {a b : 
α} (h : 1 <= b) : a <= a * b
-/
@[to_additive] lemma le_iff_exists_one_le_mul [MulLeftMono α]
    [MulLeftReflectLE α] : a ≤ b ↔ ∃ c, 1 ≤ c ∧ a * c = b :=
  ⟨exists_one_le_mul_of_le, by rintro ⟨c, hc, rfl⟩; exact le_mul_of_one_le_right' hc⟩
/-
**lt_iff_exists_one_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : Preorder α] [ExistsMulOfLE
 α] {a b : α} [MulLeftStrictMono α]   [MulLeftReflectLT α], a < b ↔ ∃ c, 1 < c ∧
 a * c = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_one_lt_mul_of_lt'`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 
: Preorder α] [ExistsMulOfLE α] {a b : α} [MulLeftReflectLT α],   a < b → ∃ c, 1
 < c ∧ a * c =…
· 使用定理 `lt_mul_of_one_lt_right'`：lt_mul_of_one_lt_right' [MulLeftStrictMono α] (
a : α) {b : α} (h : 1 < b) : a < a * b
-/
@[to_additive] lemma lt_iff_exists_one_lt_mul [MulLeftStrictMono α]
    [MulLeftReflectLT α] : a < b ↔ ∃ c, 1 < c ∧ a * c = b :=
  ⟨exists_one_lt_mul_of_lt', by rintro ⟨c, hc, rfl⟩; exact lt_mul_of_one_lt_right' _ hc⟩

end MulOneClass

section ExistsMulOfLE

variable [LinearOrder α] [DenselyOrdered α] [Monoid α] [ExistsMulOfLE α]
  [MulLeftReflectLT α] {a b : α}

@[to_additive]
/-
**le_of_forall_one_lt_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_forall_one_lt_le_mul (h : forall ε : α, 1 < ε -> a <= b * ε) : a <= 
b
参数：h : forall ε : α, 1 < ε -> a <= b * ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_gt_imp_ge_of_dense`：le_of_forall_gt_imp_ge_of_dense (h : fo
rall a, a₂ < a -> a₁ <= a) : a₁ <= a₂
· 使用定理 `ExistsMulOfLE.exists_mul_of_le`：∀ {α : Type u} {inst : Mul α} {inst_1 : 
LE α} [self : ExistsMulOfLE α] {a b : α}, a ≤ b → ∃ c, b = a * c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `one_lt_of_lt_mul_right`：one_lt_of_lt_mul_right [MulLeftReflectLT α] {a b
 : α} (h : a < a * b) : 1 < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_of_forall_one_lt_le_mul (h : ∀ ε : α, 1 < ε → a ≤ b * ε) : a ≤ b :=
  le_of_forall_gt_imp_ge_of_dense fun x hxb => by
    obtain ⟨ε, rfl⟩ := exists_mul_of_le hxb.le
    exact h _ (one_lt_of_lt_mul_right hxb)

@[to_additive]
/-
**le_of_forall_one_lt_lt_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_forall_one_lt_lt_mul' (h : forall ε : α, 1 < ε -> a < b * ε) : a <= 
b
参数：h : forall ε : α, 1 < ε -> a < b * ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_one_lt_le_mul`：le_of_forall_one_lt_le_mul (h : forall ε : α
, 1 < ε -> a <= b * ε) : a <= b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem le_of_forall_one_lt_lt_mul' (h : ∀ ε : α, 1 < ε → a < b * ε) : a ≤ b :=
  le_of_forall_one_lt_le_mul fun ε hε => (h ε hε).le

@[to_additive]
/-
**le_iff_forall_one_lt_lt_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_forall_one_lt_lt_mul' [MulLeftStrictMono α] : a <= b ↔ forall ε, 1 
< ε -> a < b * ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_mul_of_le_of_one_lt`：lt_mul_of_le_of_one_lt [MulLeftStrictMono α] {a 
b c : α} (hbc : b <= c) (ha : 1 < a) : b < c * a
· 使用定理 `le_of_forall_one_lt_lt_mul'`：le_of_forall_one_lt_lt_mul' (h : forall ε :
 α, 1 < ε -> a < b * ε) : a <= b
-/
theorem le_iff_forall_one_lt_lt_mul' [MulLeftStrictMono α] :
    a ≤ b ↔ ∀ ε, 1 < ε → a < b * ε :=
  ⟨fun h _ => lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul'⟩

@[to_additive]
/-
**le_iff_forall_one_lt_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_forall_one_lt_le_mul [MulLeftStrictMono α] : a <= b ↔ forall ε, 1 <
 ε -> a <= b * ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_mul_of_le_of_one_lt`：lt_mul_of_le_of_one_lt [MulLeftStrictMono α] {a 
b c : α} (hbc : b <= c) (ha : 1 < a) : b < c * a
· 使用定理 `le_of_forall_one_lt_le_mul`：le_of_forall_one_lt_le_mul (h : forall ε : α
, 1 < ε -> a <= b * ε) : a <= b
-/
theorem le_iff_forall_one_lt_le_mul [MulLeftStrictMono α] :
    a ≤ b ↔ ∀ ε, 1 < ε → a ≤ b * ε :=
  ⟨fun h _ hε ↦ lt_mul_of_le_of_one_lt h hε |>.le, le_of_forall_one_lt_le_mul⟩

end ExistsMulOfLE

