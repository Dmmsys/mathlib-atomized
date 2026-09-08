/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Absolute values in ordered groups

The absolute value of an element in a group which is also a lattice is its supremum with its
negation. This generalizes the usual absolute value on real numbers (`|x| = max x (-x)`).

## Notation

- `|a|`: The *absolute value* of an element `a` of an additive lattice ordered group
- `|a|ₘ`: The *absolute value* of an element `a` of a multiplicative lattice ordered group
-/

public section

open Function

variable {G : Type*}

section LinearOrderedCommGroup
variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

/-
**mabs_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_1} [inst : CommGroup G] [inst_1 : LinearOrder G] [IsOrderedM
onoid G] (n : ℕ) (a : G), |a ^ n|ₘ = |a|ₘ ^ n
参数：n : ℕ；a : G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_of_le_one`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], a ≤ 1 → |a|ₘ = a⁻¹
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mabs_inv`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α)
, |a⁻¹|ₘ = |a|ₘ
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `mabs_of_one_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], 1 ≤ a → |a|ₘ = a
· 使用定理 `one_le_pow_of_one_le'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preo
rder M] [MulLeftMono M] {a : M}, 1 ≤ a → ∀ (n : ℕ), 1 ≤ a ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `one_le_inv'`：∀ {α : Type u} [inst : Group α] [inst_1 : LE α] [MulLeftMon
o α] {a : α}, 1 ≤ a⁻¹ ↔ a ≤ 1
-/
@[to_additive] lemma mabs_pow (n : ℕ) (a : G) : |a ^ n|ₘ = |a|ₘ ^ n := by
  obtain ha | ha := le_total a 1
  · rw [mabs_of_le_one ha, ← mabs_inv, ← inv_pow, mabs_of_one_le]
    exact one_le_pow_of_one_le' (one_le_inv'.2 ha) n
  · rw [mabs_of_one_le ha, mabs_of_one_le (one_le_pow_of_one_le' ha n)]
/-
**mabs_mul_eq_mul_mabs_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] private lemma mabs_mul_eq_mul_mabs_le (hab : a ≤ b) :
    |a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 ≤ a ∧ 1 ≤ b ∨ a ≤ 1 ∧ b ≤ 1 := by
  obtain ha | ha := le_or_gt 1 a <;> obtain hb | hb := le_or_gt 1 b
  · simp [ha, hb, mabs_of_one_le, one_le_mul ha hb]
  · exact (lt_irrefl (1 : G) <| ha.trans_lt <| hab.trans_lt hb).elim
  swap
  · simp [ha.le, hb.le, mabs_of_le_one, mul_le_one', mul_comm]
  have : (|a * b|ₘ = a⁻¹ * b ↔ b ≤ 1) ↔
    (|a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 ≤ a ∧ 1 ≤ b ∨ a ≤ 1 ∧ b ≤ 1) := by
    simp [ha.le, ha.not_ge, hb, mabs_of_le_one, mabs_of_one_le]
  refine this.mp ⟨fun h ↦ ?_, fun h ↦ by simp only [h.antisymm hb, mabs_of_lt_one ha, mul_one]⟩
  obtain ab | ab := le_or_gt (a * b) 1
  · refine (eq_one_of_inv_eq' ?_).le
    rwa [mabs_of_le_one ab, mul_inv_rev, mul_comm, mul_right_inj] at h
  · rw [mabs_of_one_lt ab, mul_left_inj] at h
    rw [eq_one_of_inv_eq' h.symm] at ha
    cases ha.false
/-
**mabs_mul_eq_mul_mabs_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_1} [inst : CommGroup G] [inst_1 : LinearOrder G] [IsOrderedM
onoid G] (a b : G),   |a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 ≤ a ∧ 1 ≤ b ∨ a ≤ 1 ∧ b ≤ 1
参数：a b : G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `_private.Mathlib.Algebra.Order.Group.Abs.0.mabs_mul_eq_mul_mabs_le`：∀ {G
 : Type u_1} [inst : CommGroup G] [inst_1 : LinearOrder G] [IsOrderedMonoid G] {
a b : G},   a ≤ b → (|a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 ≤ a ∧ 1 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
@[to_additive] lemma mabs_mul_eq_mul_mabs_iff (a b : G) :
    |a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 ≤ a ∧ 1 ≤ b ∨ a ≤ 1 ∧ b ≤ 1 := by
  obtain ab | ab := le_total a b
  · exact mabs_mul_eq_mul_mabs_le ab
  · simpa only [mul_comm, and_comm] using mabs_mul_eq_mul_mabs_le ab

@[to_additive]
/-
**mabs_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_le : |a|ₘ <= b ↔ b⁻¹ <= a ∧ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_le'`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {a b : 
α}, |a|ₘ ≤ b ↔ a ≤ b ∧ a⁻¹ ≤ b
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `inv_le'`：inv_le' : a⁻¹ <= b ↔ b⁻¹ <= a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mabs_le : |a|ₘ ≤ b ↔ b⁻¹ ≤ a ∧ a ≤ b := by rw [mabs_le', and_comm, inv_le']

@[to_additive]
/-
**le_mabs'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mabs' : a <= |b|ₘ ↔ b <= a⁻¹ ∨ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_mabs`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] {a b
 : α}, a ≤ |b|ₘ ↔ a ≤ b ∨ a ≤ b⁻¹
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `le_inv'`：le_inv' : a <= b⁻¹ ↔ b <= a⁻¹
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_mabs' : a ≤ |b|ₘ ↔ b ≤ a⁻¹ ∨ a ≤ b := by rw [le_mabs, or_comm, le_inv']

@[to_additive]
/-
**inv_le_of_mabs_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_le_of_mabs_le (h : |a|ₘ <= b) : b⁻¹ <= a
参数：h : |a|ₘ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mabs_le`：mabs_le : |a|ₘ <= b ↔ b⁻¹ <= a ∧ a <= b
-/
theorem inv_le_of_mabs_le (h : |a|ₘ ≤ b) : b⁻¹ ≤ a :=
  (mabs_le.mp h).1

@[to_additive]
/-
**le_of_mabs_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_mabs_le (h : |a|ₘ <= b) : a <= b
参数：h : |a|ₘ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mabs_le`：mabs_le : |a|ₘ <= b ↔ b⁻¹ <= a ∧ a <= b
-/
theorem le_of_mabs_le (h : |a|ₘ ≤ b) : a ≤ b :=
  (mabs_le.mp h).2

@[to_additive]
/-
**mabs_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_mul' (a b : G) : |a|ₘ <= |b|ₘ * |b * a|ₘ
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mabs_inv`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α)
, |a⁻¹|ₘ = |a|ₘ
· 使用引理 `mabs_mul_le`：mabs_mul_le (a b : α) : |a * b|ₘ <= |a|ₘ * |b|ₘ
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem mabs_mul' (a b : G) : |a|ₘ ≤ |b|ₘ * |b * a|ₘ := by simpa using mabs_mul_le b⁻¹ (b * a)

@[to_additive]
/-
**mabs_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_div (a b : G) : |a / b|ₘ <= |a|ₘ * |b|ₘ
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mabs_inv`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α)
, |a⁻¹|ₘ = |a|ₘ
· 使用引理 `mabs_mul_le`：mabs_mul_le (a b : α) : |a * b|ₘ <= |a|ₘ * |b|ₘ
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem mabs_div (a b : G) : |a / b|ₘ ≤ |a|ₘ * |b|ₘ := by
  rw [div_eq_mul_inv, ← mabs_inv b]
  exact mabs_mul_le a _

@[to_additive]
/-
**mabs_div_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_div_le_iff : |a / b|ₘ <= c ↔ a / b <= c ∧ b / a <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_le`：mabs_le : |a|ₘ <= b ↔ b⁻¹ <= a ∧ a <= b
· 使用定理 `inv_le_div_iff_le_mul`：inv_le_div_iff_le_mul : b⁻¹ <= a / c ↔ c <= a * b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `div_le_iff_le_mul'`：div_le_iff_le_mul' : a / b <= c ↔ a <= b * c
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mabs_div_le_iff : |a / b|ₘ ≤ c ↔ a / b ≤ c ∧ b / a ≤ c := by
  rw [mabs_le, inv_le_div_iff_le_mul, div_le_iff_le_mul', and_comm, div_le_iff_le_mul']

@[to_additive]
/-
**mabs_div_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_div_lt_iff : |a / b|ₘ < c ↔ a / b < c ∧ b / a < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_lt`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [Mul
LeftMono α] {a b : α} [MulRightMono α],   |a|ₘ < b ↔ b⁻¹ < a ∧ a < b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `inv_lt_div_iff_lt_mul'`：inv_lt_div_iff_lt_mul' : b⁻¹ < a / c ↔ c < a * b
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `div_lt_iff_lt_mul'`：div_lt_iff_lt_mul' : a / b < c ↔ a < b * c
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mabs_div_lt_iff : |a / b|ₘ < c ↔ a / b < c ∧ b / a < c := by
  rw [mabs_lt, inv_lt_div_iff_lt_mul', div_lt_iff_lt_mul', and_comm, div_lt_iff_lt_mul']

@[to_additive]
/-
**div_le_of_mabs_div_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_of_mabs_div_le_left (h : |a / b|ₘ <= c) : b / c <= a
参数：h : |a / b|ₘ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `div_le_comm`：div_le_comm : a / b <= c ↔ a / c <= b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mabs_div_le_iff`：mabs_div_le_iff : |a / b|ₘ <= c ↔ a / b <= c ∧ b / a <=
 c
-/
theorem div_le_of_mabs_div_le_left (h : |a / b|ₘ ≤ c) : b / c ≤ a :=
  div_le_comm.1 <| (mabs_div_le_iff.1 h).2

@[to_additive]
/-
**div_le_of_mabs_div_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_of_mabs_div_le_right (h : |a / b|ₘ <= c) : a / c <= b
参数：h : |a / b|ₘ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_le_of_mabs_div_le_left`：div_le_of_mabs_div_le_left (h : |a / b|ₘ <= 
c) : b / c <= a
· 使用定理 `mabs_div_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a
 b : α), |a / b|ₘ = |b / a|ₘ
-/
theorem div_le_of_mabs_div_le_right (h : |a / b|ₘ ≤ c) : a / c ≤ b :=
  div_le_of_mabs_div_le_left (mabs_div_comm a b ▸ h)

@[to_additive]
/-
**div_lt_of_mabs_div_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_lt_of_mabs_div_lt_left (h : |a / b|ₘ < c) : b / c < a
参数：h : |a / b|ₘ < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `div_lt_comm`：div_lt_comm : a / b < c ↔ a / c < b
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mabs_div_lt_iff`：mabs_div_lt_iff : |a / b|ₘ < c ↔ a / b < c ∧ b / a < c
-/
theorem div_lt_of_mabs_div_lt_left (h : |a / b|ₘ < c) : b / c < a :=
  div_lt_comm.1 <| (mabs_div_lt_iff.1 h).2

@[to_additive]
/-
**div_lt_of_mabs_div_lt_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_lt_of_mabs_div_lt_right (h : |a / b|ₘ < c) : a / c < b
参数：h : |a / b|ₘ < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_lt_of_mabs_div_lt_left`：div_lt_of_mabs_div_lt_left (h : |a / b|ₘ < c
) : b / c < a
· 使用定理 `mabs_div_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a
 b : α), |a / b|ₘ = |b / a|ₘ
-/
theorem div_lt_of_mabs_div_lt_right (h : |a / b|ₘ < c) : a / c < b :=
  div_lt_of_mabs_div_lt_left (mabs_div_comm a b ▸ h)

@[to_additive]
/-
**mabs_div_mabs_le_mabs_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_div_mabs_le_mabs_div (a b : G) : |a|ₘ / |b|ₘ <= |a / b|ₘ
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_le_iff_le_mul`：div_le_iff_le_mul : a / c <= b ↔ a <= b * c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用引理 `mabs_mul_le`：mabs_mul_le (a b : α) : |a * b|ₘ <= |a|ₘ * |b|ₘ
-/
theorem mabs_div_mabs_le_mabs_div (a b : G) : |a|ₘ / |b|ₘ ≤ |a / b|ₘ :=
  div_le_iff_le_mul.2 <|
    calc
      |a|ₘ = |a / b * b|ₘ := by rw [div_mul_cancel]
      _ ≤ |a / b|ₘ * |b|ₘ := mabs_mul_le _ _

@[to_additive]
/-
**mabs_div_mabs_le_mabs_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_div_mabs_le_mabs_mul (a b : G) : |a|ₘ / |b|ₘ <= |a * b|ₘ
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mabs_div_mabs_le_mabs_div`：mabs_div_mabs_le_mabs_div (a b : G) : |a|ₘ / 
|b|ₘ <= |a / b|ₘ
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `mabs_inv`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α)
, |a⁻¹|ₘ = |a|ₘ
-/
theorem mabs_div_mabs_le_mabs_mul (a b : G) : |a|ₘ / |b|ₘ ≤ |a * b|ₘ :=
  mabs_inv b ▸ div_inv_eq_mul a b ▸ mabs_div_mabs_le_mabs_div a b⁻¹

@[to_additive]
/-
**mabs_mabs_div_mabs_le_mabs_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_mabs_div_mabs_le_mabs_div (a b : G) : |(|a|ₘ / |b|ₘ)|ₘ <= |a / b|ₘ
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mabs_div_le_iff`：mabs_div_le_iff : |a / b|ₘ <= c ↔ a / b <= c ∧ b / a <=
 c
· 使用定理 `mabs_div_mabs_le_mabs_div`：mabs_div_mabs_le_mabs_div (a b : G) : |a|ₘ / 
|b|ₘ <= |a / b|ₘ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_div_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a
 b : α), |a / b|ₘ = |b / a|ₘ
-/
theorem mabs_mabs_div_mabs_le_mabs_div (a b : G) : |(|a|ₘ / |b|ₘ)|ₘ ≤ |a / b|ₘ :=
  mabs_div_le_iff.2
    ⟨mabs_div_mabs_le_mabs_div _ _, by rw [mabs_div_comm]; apply mabs_div_mabs_le_mabs_div⟩

/-- `|a / b|ₘ ≤ n` if `1 ≤ a ≤ n` and `1 ≤ b ≤ n`. -/
@[to_additive /-- `|a - b| ≤ n` if `0 ≤ a ≤ n` and `0 ≤ b ≤ n`. -/]
/-
**mabs_div_le_of_one_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_div_le_of_one_le_of_le {a b n : G} (one_le_a : 1 <= a) (a_le_n : a <=
 n) (one_le_b : 1 <= b) (b_le_n : b <= n) : |a / b|ₘ <= n
参数：one_le_a : 1 <= a；a_le_n : a <= n；one_le_b : 1 <= b；b_le_n : b <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_div_le_iff`：mabs_div_le_iff : |a / b|ₘ <= c ↔ a / b <= c ∧ b / a <=
 c
· 使用定理 `div_le_iff_le_mul`：div_le_iff_le_mul : a / c <= b ↔ a <= b * c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `le_mul_of_le_of_one_le`：le_mul_of_le_of_one_le [MulLeftMono α] {a b c : 
α} (hbc : b <= c) (ha : 1 <= a) : b <= c * a

--- 原说明 ---
`|a / b|ₘ ≤ n` if `1 ≤ a ≤ n` and `1 ≤ b ≤ n`.
-/
theorem mabs_div_le_of_one_le_of_le {a b n : G} (one_le_a : 1 ≤ a) (a_le_n : a ≤ n)
    (one_le_b : 1 ≤ b) (b_le_n : b ≤ n) : |a / b|ₘ ≤ n := by
  rw [mabs_div_le_iff, div_le_iff_le_mul, div_le_iff_le_mul]
  exact ⟨le_mul_of_le_of_one_le a_le_n one_le_b, le_mul_of_le_of_one_le b_le_n one_le_a⟩

/-- `|a / b|ₘ < n` if `1 ≤ a < n` and `1 ≤ b < n`. -/
@[to_additive /-- `|a - b| < n` if `0 ≤ a < n` and `0 ≤ b < n`. -/]
/-
**mabs_div_lt_of_one_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_div_lt_of_one_le_of_lt {a b n : G} (one_le_a : 1 <= a) (a_lt_n : a < 
n) (one_le_b : 1 <= b) (b_lt_n : b < n) : |a / b|ₘ < n
参数：one_le_a : 1 <= a；a_lt_n : a < n；one_le_b : 1 <= b；b_lt_n : b < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_div_lt_iff`：mabs_div_lt_iff : |a / b|ₘ < c ↔ a / b < c ∧ b / a < c
· 使用定理 `div_lt_iff_lt_mul`：div_lt_iff_lt_mul : a / c < b ↔ a < b * c
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `lt_mul_of_lt_of_one_le`：lt_mul_of_lt_of_one_le [MulLeftMono α] {a b c : 
α} (hbc : b < c) (ha : 1 <= a) : b < c * a

--- 原说明 ---
`|a / b|ₘ < n` if `1 ≤ a < n` and `1 ≤ b < n`.
-/
theorem mabs_div_lt_of_one_le_of_lt {a b n : G} (one_le_a : 1 ≤ a) (a_lt_n : a < n)
    (one_le_b : 1 ≤ b) (b_lt_n : b < n) : |a / b|ₘ < n := by
  rw [mabs_div_lt_iff, div_lt_iff_lt_mul, div_lt_iff_lt_mul]
  exact ⟨lt_mul_of_lt_of_one_le a_lt_n one_le_b, lt_mul_of_lt_of_one_le b_lt_n one_le_a⟩

@[to_additive]
/-
**mabs_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_eq (hb : 1 <= b) : |a|ₘ = b ↔ a = b ∨ a = b⁻¹
参数：hb : 1 <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_eq_inv_of_mabs_eq`：∀ {α : Type u_1} [inst : Group α] [inst_1 : Lin
earOrder α] {a b : α}, |a|ₘ = b → a = b ∨ a = b⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_of_one_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], 1 ≤ a → |a|ₘ = a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mabs_inv`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α)
, |a⁻¹|ₘ = |a|ₘ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mabs_eq (hb : 1 ≤ b) : |a|ₘ = b ↔ a = b ∨ a = b⁻¹ := by
  refine ⟨eq_or_eq_inv_of_mabs_eq, ?_⟩
  rintro (rfl | rfl) <;> simp only [mabs_inv, mabs_of_one_le hb]

@[to_additive]
/-
**mabs_le_max_mabs_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_le_max_mabs_mabs (hab : a <= b) (hbc : b <= c) : |b|ₘ <= max |a|ₘ |c|
ₘ
参数：hab : a <= b；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mabs_le'`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {a b : 
α}, |a|ₘ ≤ b ↔ a ≤ b ∧ a⁻¹ ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_mabs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a 
: α), a ≤ |a|ₘ
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_le_inv_iff`：inv_le_inv_iff : a⁻¹ <= b⁻¹ ↔ b <= a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `inv_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a :
 α), a⁻¹ ≤ |a|ₘ
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem mabs_le_max_mabs_mabs (hab : a ≤ b) (hbc : b ≤ c) : |b|ₘ ≤ max |a|ₘ |c|ₘ :=
  mabs_le'.2
    ⟨by simp [hbc.trans (le_mabs_self c)], by
      simp [(inv_le_inv_iff.mpr hab).trans (inv_le_mabs a)]⟩

omit [IsOrderedMonoid G] in
@[to_additive]
/-
**min_mabs_mabs_le_mabs_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_mabs_mabs_le_mabs_max : min |a|ₘ |b|ₘ <= |max a b|ₘ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
theorem min_mabs_mabs_le_mabs_max : min |a|ₘ |b|ₘ ≤ |max a b|ₘ :=
  (le_total a b).elim (fun h => (min_le_right _ _).trans_eq <| congr_arg _ (max_eq_right h).symm)
    fun h => (min_le_left _ _).trans_eq <| congr_arg _ (max_eq_left h).symm

omit [IsOrderedMonoid G] in
@[to_additive]
/-
**min_mabs_mabs_le_mabs_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_mabs_mabs_le_mabs_min : min |a|ₘ |b|ₘ <= |min a b|ₘ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
-/
theorem min_mabs_mabs_le_mabs_min : min |a|ₘ |b|ₘ ≤ |min a b|ₘ :=
  (le_total a b).elim (fun h => (min_le_left _ _).trans_eq <| congr_arg _ (min_eq_left h).symm)
    fun h => (min_le_right _ _).trans_eq <| congr_arg _ (min_eq_right h).symm

omit [IsOrderedMonoid G] in
@[to_additive]
/-
**mabs_max_le_max_mabs_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_max_le_max_mabs_mabs : |max a b|ₘ <= max |a|ₘ |b|ₘ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem mabs_max_le_max_mabs_mabs : |max a b|ₘ ≤ max |a|ₘ |b|ₘ :=
  (le_total a b).elim (fun h => (congr_arg _ <| max_eq_right h).trans_le <| le_max_right _ _)
    fun h => (congr_arg _ <| max_eq_left h).trans_le <| le_max_left _ _

omit [IsOrderedMonoid G] in
@[to_additive]
/-
**mabs_min_le_max_mabs_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_min_le_max_mabs_mabs : |min a b|ₘ <= max |a|ₘ |b|ₘ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem mabs_min_le_max_mabs_mabs : |min a b|ₘ ≤ max |a|ₘ |b|ₘ :=
  (le_total a b).elim (fun h => (congr_arg _ <| min_eq_left h).trans_le <| le_max_left _ _) fun h =>
    (congr_arg _ <| min_eq_right h).trans_le <| le_max_right _ _

@[to_additive]
/-
**eq_of_mabs_div_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_mabs_div_eq_one {a b : G} (h : |a / b|ₘ = 1) : a = b
参数：h : |a / b|ₘ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `div_eq_one`：div_eq_one : a / b = 1 ↔ a = b
· 使用定理 `mabs_eq_one`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] 
[MulLeftMono α] {a : α} [MulRightMono α], |a|ₘ = 1 ↔ a = 1
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem eq_of_mabs_div_eq_one {a b : G} (h : |a / b|ₘ = 1) : a = b :=
  div_eq_one.1 <| mabs_eq_one.1 h

@[to_additive]
/-
**mabs_div_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_div_le (a b c : G) : |a / c|ₘ <= |a / b|ₘ * |b / c|ₘ
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_div_cancel`：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a
 / c
· 使用引理 `mabs_mul_le`：mabs_mul_le (a b : α) : |a * b|ₘ <= |a|ₘ * |b|ₘ
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem mabs_div_le (a b c : G) : |a / c|ₘ ≤ |a / b|ₘ * |b / c|ₘ :=
  calc
    |a / c|ₘ = |a / b * (b / c)|ₘ := by rw [div_mul_div_cancel]
    _ ≤ |a / b|ₘ * |b / c|ₘ := mabs_mul_le _ _

@[to_additive]
/-
**mabs_div_le_max_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_div_le_max_div {a b c : G} (hac : a <= b) (hcd : b <= c) (d : G) : |b
 / d|ₘ <= max (c / d) (d / a)
参数：hac : a <= b；hcd : b <= c；d : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_of_one_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], 1 ≤ a → |a|ₘ = a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `one_le_div'`：one_le_div' : 1 <= a / b ↔ b <= a
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `div_le_div_right'`：div_le_div_right' (h : a <= b) (c : α) : a / c <= b /
 c
· 使用定理 `mabs_of_le_one`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], a ≤ 1 → |a|ₘ = a⁻¹
· 使用定理 `div_le_one'`：div_le_one' : a / b <= 1 ↔ a <= b
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用定理 `div_le_div_left'`：div_le_div_left' (h : a <= b) (c : α) : c / b <= c / a
-/
theorem mabs_div_le_max_div {a b c : G} (hac : a ≤ b) (hcd : b ≤ c) (d : G) :
    |b / d|ₘ ≤ max (c / d) (d / a) := by
  rcases le_total d b with h | h
  · rw [mabs_of_one_le <| one_le_div'.mpr h]
    exact le_max_of_le_left <| div_le_div_right' hcd _
  · rw [mabs_of_le_one <| div_le_one'.mpr h, inv_div]
    exact le_max_of_le_right <| div_le_div_left' hac _

@[to_additive]
/-
**mabs_mul_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_mul_three (a b c : G) : |a * b * c|ₘ <= |a|ₘ * |b|ₘ * |c|ₘ
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `mabs_mul_le`：mabs_mul_le (a b : α) : |a * b|ₘ <= |a|ₘ * |b|ₘ
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
-/
theorem mabs_mul_three (a b c : G) : |a * b * c|ₘ ≤ |a|ₘ * |b|ₘ * |c|ₘ := by
  grw [mabs_mul_le, mabs_mul_le]

@[to_additive]
/-
**mabs_div_le_of_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_div_le_of_le_of_le {a b lb ub : G} (hal : lb <= a) (hau : a <= ub) (h
bl : lb <= b) (hbu : b <= ub) : |a / b|ₘ <= ub / lb
参数：hal : lb <= a；hau : a <= ub；hbl : lb <= b；hbu : b <= ub。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mabs_div_le_iff`：mabs_div_le_iff : |a / b|ₘ <= c ↔ a / b <= c ∧ b / a <=
 c
· 使用定理 `div_le_div''`：div_le_div'' (hab : a <= b) (hcd : c <= d) : a / d <= b / 
c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem mabs_div_le_of_le_of_le {a b lb ub : G} (hal : lb ≤ a) (hau : a ≤ ub) (hbl : lb ≤ b)
    (hbu : b ≤ ub) : |a / b|ₘ ≤ ub / lb :=
  mabs_div_le_iff.2 ⟨div_le_div'' hau hbl, div_le_div'' hbu hal⟩

@[to_additive]
/-
**eq_of_mabs_div_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_mabs_div_le_one (h : |a / b|ₘ <= 1) : a = b
参数：h : |a / b|ₘ <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_mabs_div_eq_one`：eq_of_mabs_div_eq_one {a b : G} (h : |a / b|ₘ = 1
) : a = b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `one_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [Mul
LeftMono α] [MulRightMono α] (a : α), 1 ≤ |a|ₘ
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem eq_of_mabs_div_le_one (h : |a / b|ₘ ≤ 1) : a = b :=
  eq_of_mabs_div_eq_one (le_antisymm h (one_le_mabs (a / b)))

@[to_additive]
/-
**eq_of_mabs_div_lt_all** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_of_mabs_div_lt_all {x y : G} (h : forall ε > 1, |x / y|ₘ < ε) : x = y
参数：h : forall ε > 1, |x / y|ₘ < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_mabs_div_le_one`：eq_of_mabs_div_le_one (h : |a / b|ₘ <= 1) : a = b
· 使用定理 `le_of_forall_gt`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, (∀ (
c : α), a < c → b < c) → b ≤ a
-/
lemma eq_of_mabs_div_lt_all {x y : G} (h : ∀ ε > 1, |x / y|ₘ < ε) : x = y :=
  eq_of_mabs_div_le_one <| le_of_forall_gt h

@[to_additive]
/-
**eq_of_mabs_div_le_all** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_of_mabs_div_le_all [DenselyOrdered G] {x y : G} (h : forall ε > 1, |x /
 y|ₘ <= ε) : x = y
参数：h : forall ε > 1, |x / y|ₘ <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_mabs_div_le_one`：eq_of_mabs_div_le_one (h : |a / b|ₘ <= 1) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `forall_gt_imp_ge_iff_le_of_dense`：forall_gt_imp_ge_iff_le_of_dense : (fo
rall a, a₂ < a -> a₁ <= a) ↔ a₁ <= a₂
-/
lemma eq_of_mabs_div_le_all [DenselyOrdered G] {x y : G} (h : ∀ ε > 1, |x / y|ₘ ≤ ε) : x = y :=
  eq_of_mabs_div_le_one <| forall_gt_imp_ge_iff_le_of_dense.mp h

@[to_additive]
/-
**mabs_div_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_div_le_one : |a / b|ₘ <= 1 ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_mabs_div_le_one`：eq_of_mabs_div_le_one (h : |a / b|ₘ <= 1) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `mabs_one`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLef
tMono α], |1|ₘ = 1
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mabs_div_le_one : |a / b|ₘ ≤ 1 ↔ a = b :=
  ⟨eq_of_mabs_div_le_one, by rintro rfl; rw [div_self', mabs_one]⟩

@[to_additive]
/-
**mabs_div_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_div_pos : 1 < |a / b|ₘ ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `mabs_div_le_one`：mabs_div_le_one : |a / b|ₘ <= 1 ↔ a = b
-/
theorem mabs_div_pos : 1 < |a / b|ₘ ↔ a ≠ b :=
  not_le.symm.trans mabs_div_le_one.not

@[to_additive (attr := simp)]
/-
**mabs_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_eq_self : |a|ₘ = a ↔ 1 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_eq_max_inv`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder
 α] {a : α}, |a|ₘ = max a a⁻¹
· 使用定理 `max_eq_left_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b : α}, max a 
b = a ↔ b ≤ a
· 使用定理 `inv_le_self_iff`：inv_le_self_iff : a⁻¹ <= a ↔ 1 <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mabs_eq_self : |a|ₘ = a ↔ 1 ≤ a := by
  rw [mabs_eq_max_inv, max_eq_left_iff, inv_le_self_iff]

@[to_additive (attr := simp)]
/-
**mabs_eq_inv_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_eq_inv_self : |a|ₘ = a⁻¹ ↔ a <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mabs_eq_max_inv`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder
 α] {a : α}, |a|ₘ = max a a⁻¹
· 使用定理 `max_eq_right_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b : α}, max a
 b = b ↔ a ≤ b
· 使用定理 `le_inv_self_iff`：le_inv_self_iff : a <= a⁻¹ ↔ a <= 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mabs_eq_inv_self : |a|ₘ = a⁻¹ ↔ a ≤ 1 := by
  rw [mabs_eq_max_inv, max_eq_right_iff, le_inv_self_iff]

/-- For an element `a` of a multiplicative linear ordered group,
either `|a|ₘ = a` and `1 ≤ a`, or `|a|ₘ = a⁻¹` and `a < 1`. -/
@[to_additive
  /-- For an element `a` of an additive linear ordered group,
  either `|a| = a` and `0 ≤ a`, or `|a| = -a` and `a < 0`.
  Use cases on this lemma to automate linarith in inequalities -/]
/-
**mabs_cases** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_cases (a : G) : |a|ₘ = a ∧ 1 <= a ∨ |a|ₘ = a⁻¹ ∧ a < 1
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem mabs_cases (a : G) : |a|ₘ = a ∧ 1 ≤ a ∨ |a|ₘ = a⁻¹ ∧ a < 1 := by
  cases le_or_gt 1 a <;> simp [*, le_of_lt]

@[to_additive (attr := simp)]
/-
**max_one_mul_max_inv_one_eq_mabs_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_one_mul_max_inv_one_eq_mabs_self (a : G) : max a 1 * max a⁻¹ 1 = |a|ₘ
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem max_one_mul_max_inv_one_eq_mabs_self (a : G) : max a 1 * max a⁻¹ 1 = |a|ₘ := by
  symm
  rcases le_total 1 a with (ha | ha) <;> simp [ha]

end LinearOrderedCommGroup

section LinearOrderedAddCommGroup

variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] {a b c : G}

@[to_additive]
/-
**apply_abs_le_mul_of_one_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：apply_abs_le_mul_of_one_le' {H : Type*} [MulOneClass H] [LE H] [MulLeftMon
o H] [MulRightMono H] {f : G -> H} {a : G} (h₁ : 1 <= f a) (h₂ : 1 <= f (-a)) : 
f |a| <= f a * f (-a)
参数：h₁ : 1 <= f a；h₂ : 1 <= f (-a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_mul_of_one_le_left'`：le_mul_of_one_le_left' [MulRightMono α] {a b : α
} (h : 1 <= b) : a <= b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_mul_of_one_le_right'`：le_mul_of_one_le_right' [MulLeftMono α] {a b : 
α} (h : 1 <= b) : a <= a * b
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
-/
theorem apply_abs_le_mul_of_one_le' {H : Type*} [MulOneClass H] [LE H]
    [MulLeftMono H] [MulRightMono H] {f : G → H}
    {a : G} (h₁ : 1 ≤ f a) (h₂ : 1 ≤ f (-a)) : f |a| ≤ f a * f (-a) :=
  (le_total a 0).rec (fun ha => (abs_of_nonpos ha).symm ▸ le_mul_of_one_le_left' h₁) fun ha =>
    (abs_of_nonneg ha).symm ▸ le_mul_of_one_le_right' h₂

@[to_additive]
/-
**apply_abs_le_mul_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：apply_abs_le_mul_of_one_le {H : Type*} [MulOneClass H] [LE H] [MulLeftMono
 H] [MulRightMono H] {f : G -> H} (h : forall x, 1 <= f x) (a : G) : f |a| <= f 
a * f (-a)
参数：h : forall x, 1 <= f x；a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `apply_abs_le_mul_of_one_le'`：apply_abs_le_mul_of_one_le' {H : Type*} [Mu
lOneClass H] [LE H] [MulLeftMono H] [MulRightMono H] {f : G -> H} {a : G} (h₁ : 
1 <= f a) (h₂ : 1…
-/
theorem apply_abs_le_mul_of_one_le {H : Type*} [MulOneClass H] [LE H]
    [MulLeftMono H] [MulRightMono H] {f : G → H}
    (h : ∀ x, 1 ≤ f x) (a : G) : f |a| ≤ f a * f (-a) :=
  apply_abs_le_mul_of_one_le' (h _) (h _)

end LinearOrderedAddCommGroup

