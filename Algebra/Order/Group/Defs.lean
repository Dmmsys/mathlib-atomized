/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Sub.Defs

/-!
# Ordered groups

This file defines bundled ordered groups and develops a few basic results.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/

public section

/-
`NeZero` theory should not be needed at this point in the ordered algebraic hierarchy.
-/
assert_not_imported Mathlib.Algebra.NeZero

open Function

universe u

variable {α : Type u}

alias OrderedCommGroup.le_of_mul_le_mul_left := le_of_mul_le_mul_left'

attribute [to_additive] OrderedCommGroup.le_of_mul_le_mul_left

alias OrderedCommGroup.lt_of_mul_lt_mul_left := lt_of_mul_lt_mul_left'

attribute [to_additive] OrderedCommGroup.lt_of_mul_lt_mul_left

-- See note [lower instance priority]
@[to_additive IsOrderedAddMonoid.toIsOrderedCancelAddMonoid]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsOrderedMonoid.toIsOrderedCancelMonoid
    [CommGroup α] [Preorder α] [IsOrderedMonoid α] : IsOrderedCancelMonoid α where
  le_of_mul_le_mul_left a b c bc := by simpa using mul_le_mul_right bc a⁻¹
  le_of_mul_le_mul_right a b c bc := by simpa using mul_le_mul_right bc a⁻¹

/-- Assuming `α` equipped with `LinearOrder` is `CancelCommMonoid` and `IsOrderedMonoid`, it is
also `IsOrderedCancelMonoid`.

TODO: make it an `instance`. To avoid slowdown, it was not an instance when it was submitted. See
https://github.com/leanprover-community/mathlib4/pull/32828. -/
@[to_additive IsOrderedAddMonoid.toIsOrderedCancelAddMonoid'
  /-- Assuming `α` equipped with `LinearOrder` is `AddCancelCommMonoid` and `IsAddOrderedMonoid`, it
  is also `IsAddOrderedCancelMonoid`.

  TODO: make it an `instance`. To avoid slowdown, it was not an instance when it was submitted. See
  https://github.com/leanprover-community/mathlib4/pull/32828. -/]
/-
**IsOrderedMonoid.toIsOrderedCancelMonoid'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOrderedMonoid.toIsOrderedCancelMonoid' [CancelCommMonoid α] [LinearOrder
 α] [IsOrderedMonoid α] : IsOrderedCancelMonoid α where le_of_mul_le_mul_left _ 
_ _ h
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_mul_le_mul_left'`：le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b
 c : α} (bc : a * b <= a * c) : b <= c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem IsOrderedMonoid.toIsOrderedCancelMonoid'
    [CancelCommMonoid α] [LinearOrder α] [IsOrderedMonoid α] : IsOrderedCancelMonoid α where
  le_of_mul_le_mul_left _ _ _ h := le_of_mul_le_mul_left' h

/-!
### Linearly ordered commutative groups
-/
/- `LinearOrderedCommGroup` and `LinearOrderedAddCommGroup` no longer exist,
but we still use the namespaces.

TODO: everything in these namespaces should be renamed; even if these typeclasses still existed,
it's unconventional to put theorems in namespaces named after them. -/
insert_to_additive_translation LinearOrderedCommGroup LinearOrderedAddCommGroup

section LinearOrderedCommGroup

variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] {a : α}

@[to_additive eq_zero_of_neg_eq]
/-
**eq_one_of_inv_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_one_of_inv_eq' (h : a⁻¹ = a) : a = 1
参数：h : a⁻¹ = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `one_lt_inv_of_inv`：∀ {α : Type u} [inst : Group α] [inst_1 : LT α] [MulL
eftStrictMono α] {a : α}, a < 1 → 1 < a⁻¹
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `LT.lt.asymm`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b 
< a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_lt_one'`：∀ {α : Type u} [inst : Group α] [inst_1 : LT α] [MulLeftStr
ictMono α] {a : α}, a⁻¹ < 1 ↔ 1 < a
-/
theorem eq_one_of_inv_eq' (h : a⁻¹ = a) : a = 1 :=
  match lt_trichotomy a 1 with
  | Or.inl h₁ =>
    have : 1 < a := h ▸ one_lt_inv_of_inv h₁
    absurd h₁ this.asymm
  | Or.inr (Or.inl h₁) => h₁
  | Or.inr (Or.inr h₁) =>
    have : a < 1 := h ▸ inv_lt_one'.mpr h₁
    absurd h₁ this.asymm

@[to_additive exists_zero_lt]
/-
**exists_one_lt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_one_lt' [Nontrivial α] : exists a : α, 1 < a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.exists_ne`：∀ {α : Type u_1} [Nontrivial α] [DecidableEq α] (x 
: α), ∃ y, y ≠ x
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `one_lt_inv'`：∀ {α : Type u} [inst : Group α] [inst_1 : LT α] [MulLeftStr
ictMono α] {a : α}, 1 < a⁻¹ ↔ a < 1
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem exists_one_lt' [Nontrivial α] : ∃ a : α, 1 < a := by
  obtain ⟨y, hy⟩ := Decidable.exists_ne (1 : α)
  obtain h | h := hy.lt_or_gt
  · exact ⟨y⁻¹, one_lt_inv'.mpr h⟩
  · exact ⟨y, h⟩

-- see Note [lower instance priority]
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) LinearOrderedCommGroup.to_noMaxOrder [Nontrivial α] : NoMaxOrder α :=
  ⟨by
    obtain ⟨y, hy⟩ : ∃ a : α, 1 < a := exists_one_lt'
    exact fun a => ⟨a * y, lt_mul_of_one_lt_right' a hy⟩⟩

-- see Note [lower instance priority]
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) LinearOrderedCommGroup.to_noMinOrder [Nontrivial α] : NoMinOrder α :=
  ⟨by
    obtain ⟨y, hy⟩ : ∃ a : α, 1 < a := exists_one_lt'
    exact fun a => ⟨a / y, (div_lt_self_iff a).mpr hy⟩⟩

@[to_additive (attr := simp)]
/-
**inv_le_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_le_self_iff : a⁻¹ <= a ↔ 1 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inv_le_self_iff : a⁻¹ ≤ a ↔ 1 ≤ a := by simp [inv_le_iff_one_le_mul']

@[to_additive (attr := simp)]
/-
**inv_lt_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_lt_self_iff : a⁻¹ < a ↔ 1 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inv_lt_self_iff : a⁻¹ < a ↔ 1 < a := by simp [inv_lt_iff_one_lt_mul]

@[to_additive (attr := simp)]
/-
**le_inv_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_inv_self_iff : a <= a⁻¹ ↔ a <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_lt_self_iff`：inv_lt_self_iff : a⁻¹ < a ↔ 1 < a
-/
theorem le_inv_self_iff : a ≤ a⁻¹ ↔ a ≤ 1 := by contrapose!; exact inv_lt_self_iff

@[to_additive (attr := simp)]
/-
**lt_inv_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_inv_self_iff : a < a⁻¹ ↔ a < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_le_self_iff`：inv_le_self_iff : a⁻¹ <= a ↔ 1 <= a
-/
theorem lt_inv_self_iff : a < a⁻¹ ↔ a < 1 := by contrapose!; exact inv_le_self_iff

end LinearOrderedCommGroup

section NormNumLemmas

/- The following lemmas are stated so that the `norm_num` tactic can use them with the
expected signatures. -/
variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {a b : α}

@[to_additive (attr := gcongr) neg_le_neg]
/-
**inv_le_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_le_inv' : a <= b -> b⁻¹ <= a⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_le_inv_iff`：inv_le_inv_iff : a⁻¹ <= b⁻¹ ↔ b <= a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem inv_le_inv' : a ≤ b → b⁻¹ ≤ a⁻¹ :=
  inv_le_inv_iff.mpr

@[to_additive (attr := gcongr) neg_lt_neg]
/-
**inv_lt_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_lt_inv' : a < b -> b⁻¹ < a⁻¹
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_lt_inv_iff`：inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a
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
theorem inv_lt_inv' : a < b → b⁻¹ < a⁻¹ :=
  inv_lt_inv_iff.mpr

--  The additive version is also a `linarith` lemma.
@[to_additive]
/-
**inv_lt_one_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_lt_one_of_one_lt : 1 < a -> a⁻¹ < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_lt_one_iff_one_lt`：∀ {α : Type u} [inst : Group α] [inst_1 : LT α] [
MulLeftStrictMono α] {a : α}, a⁻¹ < 1 ↔ 1 < a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem inv_lt_one_of_one_lt : 1 < a → a⁻¹ < 1 :=
  inv_lt_one_iff_one_lt.mpr

--  The additive version is also a `linarith` lemma.
@[to_additive]
/-
**inv_le_one_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_le_one_of_one_le : 1 <= a -> a⁻¹ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_le_one'`：∀ {α : Type u} [inst : Group α] [inst_1 : LE α] [MulLeftMon
o α] {a : α}, a⁻¹ ≤ 1 ↔ 1 ≤ a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem inv_le_one_of_one_le : 1 ≤ a → a⁻¹ ≤ 1 :=
  inv_le_one'.mpr

@[to_additive neg_nonneg_of_nonpos]
/-
**one_le_inv_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_inv_of_le_one : a <= 1 -> 1 <= a⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `one_le_inv'`：∀ {α : Type u} [inst : Group α] [inst_1 : LE α] [MulLeftMon
o α] {a : α}, 1 ≤ a⁻¹ ↔ a ≤ 1
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem one_le_inv_of_le_one : a ≤ 1 → 1 ≤ a⁻¹ :=
  one_le_inv'.mpr

end NormNumLemmas

