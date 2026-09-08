/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Disjointed
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Big operators indexed by intervals

This file proves lemmas about `∏ x ∈ Ixx a b, f x` and `∑ x ∈ Ixx a b, f x`.
-/

public section

open Order

variable {α M : Type*} [CommMonoid M] {f : α → M} {a b : α}

namespace Finset
section PartialOrder
variable [PartialOrder α]

section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

@[to_additive]
/-
**Finset.mul_prod_Ico_eq_prod_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mul_prod_Ico_eq_prod_Icc (h : a <= b) : f b * ∏ x in Ico a b, f x = ∏ x in
 Icc a b, f x
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.right_notMem_Ico`：right_notMem_Ico : b ∉ Ico a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Icc_eq_cons_Ico`：Icc_eq_cons_Ico (h : a <= b) : Icc a b = (Ico a 
b).cons b right_notMem_Ico
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
-/
lemma mul_prod_Ico_eq_prod_Icc (h : a ≤ b) : f b * ∏ x ∈ Ico a b, f x = ∏ x ∈ Icc a b, f x := by
  rw [Icc_eq_cons_Ico h, prod_cons]

@[to_additive]
/-
**Finset.prod_Ico_mul_eq_prod_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_Ico_mul_eq_prod_Icc (h : a <= b) : (∏ x in Ico a b, f x) * f b = ∏ x 
in Icc a b, f x
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Finset.mul_prod_Ico_eq_prod_Icc`：mul_prod_Ico_eq_prod_Icc (h : a <= b) :
 f b * ∏ x in Ico a b, f x = ∏ x in Icc a b, f x
-/
lemma prod_Ico_mul_eq_prod_Icc (h : a ≤ b) : (∏ x ∈ Ico a b, f x) * f b = ∏ x ∈ Icc a b, f x := by
  rw [mul_comm, mul_prod_Ico_eq_prod_Icc h]

@[to_additive]
/-
**Finset.mul_prod_Ioc_eq_prod_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mul_prod_Ioc_eq_prod_Icc (h : a <= b) : f a * ∏ x in Ioc a b, f x = ∏ x in
 Icc a b, f x
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.left_notMem_Ioc`：left_notMem_Ioc : a ∉ Ioc a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Icc_eq_cons_Ioc`：Icc_eq_cons_Ioc (h : a <= b) : Icc a b = (Ioc a 
b).cons a left_notMem_Ioc
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
-/
lemma mul_prod_Ioc_eq_prod_Icc (h : a ≤ b) : f a * ∏ x ∈ Ioc a b, f x = ∏ x ∈ Icc a b, f x := by
  rw [Icc_eq_cons_Ioc h, prod_cons]

@[to_additive]
/-
**Finset.prod_Ioc_mul_eq_prod_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_Ioc_mul_eq_prod_Icc (h : a <= b) : (∏ x in Ioc a b, f x) * f a = ∏ x 
in Icc a b, f x
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Finset.mul_prod_Ioc_eq_prod_Icc`：mul_prod_Ioc_eq_prod_Icc (h : a <= b) :
 f a * ∏ x in Ioc a b, f x = ∏ x in Icc a b, f x
-/
lemma prod_Ioc_mul_eq_prod_Icc (h : a ≤ b) : (∏ x ∈ Ioc a b, f x) * f a = ∏ x ∈ Icc a b, f x := by
  rw [mul_comm, mul_prod_Ioc_eq_prod_Icc h]

@[to_additive]
/-
**Finset.mul_prod_Ioo_eq_prod_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mul_prod_Ioo_eq_prod_Ico (h : a < b) : f a * ∏ x in Ioo a b, f x = ∏ x in 
Ico a b, f x
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.left_notMem_Ioo`：left_notMem_Ioo : a ∉ Ioo a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Ico_eq_cons_Ioo`：Ico_eq_cons_Ioo (h : a < b) : Ico a b = (Ioo a b
).cons a left_notMem_Ioo
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
-/
lemma mul_prod_Ioo_eq_prod_Ico (h : a < b) : f a * ∏ x ∈ Ioo a b, f x = ∏ x ∈ Ico a b, f x := by
  rw [Ico_eq_cons_Ioo h, prod_cons]

@[to_additive]
/-
**Finset.prod_Ioo_mul_eq_prod_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_Ioo_mul_eq_prod_Ico (h : a < b) : (∏ x in Ioo a b, f x) * f a = ∏ x i
n Ico a b, f x
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Finset.mul_prod_Ioo_eq_prod_Ico`：mul_prod_Ioo_eq_prod_Ico (h : a < b) : 
f a * ∏ x in Ioo a b, f x = ∏ x in Ico a b, f x
-/
lemma prod_Ioo_mul_eq_prod_Ico (h : a < b) : (∏ x ∈ Ioo a b, f x) * f a = ∏ x ∈ Ico a b, f x := by
  rw [mul_comm, mul_prod_Ioo_eq_prod_Ico h]

@[to_additive]
/-
**Finset.mul_prod_Ioo_eq_prod_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mul_prod_Ioo_eq_prod_Ioc (h : a < b) : f b * ∏ x in Ioo a b, f x = ∏ x in 
Ioc a b, f x
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.right_notMem_Ioo`：right_notMem_Ioo : b ∉ Ioo a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Ioc_eq_cons_Ioo`：Ioc_eq_cons_Ioo (h : a < b) : Ioc a b = (Ioo a b
).cons b right_notMem_Ioo
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
-/
lemma mul_prod_Ioo_eq_prod_Ioc (h : a < b) : f b * ∏ x ∈ Ioo a b, f x = ∏ x ∈ Ioc a b, f x := by
  rw [Ioc_eq_cons_Ioo h, prod_cons]

@[to_additive]
/-
**Finset.prod_Ioo_mul_eq_prod_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_Ioo_mul_eq_prod_Ioc (h : a < b) : (∏ x in Ioo a b, f x) * f b = ∏ x i
n Ioc a b, f x
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Finset.mul_prod_Ioo_eq_prod_Ioc`：mul_prod_Ioo_eq_prod_Ioc (h : a < b) : 
f b * ∏ x in Ioo a b, f x = ∏ x in Ioc a b, f x
-/
lemma prod_Ioo_mul_eq_prod_Ioc (h : a < b) : (∏ x ∈ Ioo a b, f x) * f b = ∏ x ∈ Ioc a b, f x := by
  rw [mul_comm, mul_prod_Ioo_eq_prod_Ioc h]

variable [AddMonoidWithOne α] [SuccAddOrder α]

@[to_additive]
/-
**Finset.prod_eq_prod_Ico_succ_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_eq_prod_Ico_succ_bot {a b : Nat} (hab : a < b) (f : Nat -> M) : ∏ k i
n Ico a b, f k = f a * ∏ k in Ico (a + 1) b, f k
参数：hab : a < b；f : Nat -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用引理 `Finset.insert_Ico_add_one_left_eq_Ico`：insert_Ico_add_one_left_eq_Ico (h
 : a < b) : insert a (Ico (a + 1) b) = Ico a b
-/
theorem prod_eq_prod_Ico_succ_bot {a b : ℕ} (hab : a < b) (f : ℕ → M) :
    ∏ k ∈ Ico a b, f k = f a * ∏ k ∈ Ico (a + 1) b, f k := by
  have ha : a ∉ Ico (a + 1) b := by simp
  rw [← prod_insert ha, Finset.insert_Ico_add_one_left_eq_Ico hab]

end LocallyFiniteOrder

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α]

@[to_additive]
/-
**Finset.mul_prod_Ioi_eq_prod_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mul_prod_Ioi_eq_prod_Ici (a : α) : f a * ∏ x in Ioi a, f x = ∏ x in Ici a,
 f x
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_Ioi_self`：notMem_Ioi_self {b : α} : b ∉ Ioi b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Ici_eq_cons_Ioi`：Ici_eq_cons_Ioi (a : α) : Ici a = (Ioi a).cons a
 notMem_Ioi_self
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
-/
lemma mul_prod_Ioi_eq_prod_Ici (a : α) : f a * ∏ x ∈ Ioi a, f x = ∏ x ∈ Ici a, f x := by
  rw [Ici_eq_cons_Ioi, prod_cons]

@[to_additive]
/-
**Finset.prod_Ioi_mul_eq_prod_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_Ioi_mul_eq_prod_Ici (a : α) : (∏ x in Ioi a, f x) * f a = ∏ x in Ici 
a, f x
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Finset.mul_prod_Ioi_eq_prod_Ici`：mul_prod_Ioi_eq_prod_Ici (a : α) : f a 
* ∏ x in Ioi a, f x = ∏ x in Ici a, f x
-/
lemma prod_Ioi_mul_eq_prod_Ici (a : α) : (∏ x ∈ Ioi a, f x) * f a = ∏ x ∈ Ici a, f x := by
  rw [mul_comm, mul_prod_Ioi_eq_prod_Ici]

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

@[to_additive]
/-
**Finset.mul_prod_Iio_eq_prod_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mul_prod_Iio_eq_prod_Iic (a : α) : f a * ∏ x in Iio a, f x = ∏ x in Iic a,
 f x
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_Iio_self`：notMem_Iio_self {b : α} : b ∉ Iio b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Iic_eq_cons_Iio`：Iic_eq_cons_Iio (b : α) : Iic b = (Iio b).cons b
 notMem_Iio_self
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
-/
lemma mul_prod_Iio_eq_prod_Iic (a : α) : f a * ∏ x ∈ Iio a, f x = ∏ x ∈ Iic a, f x := by
  rw [Iic_eq_cons_Iio, prod_cons]

@[to_additive]
/-
**Finset.prod_Iio_mul_eq_prod_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_Iio_mul_eq_prod_Iic (a : α) : (∏ x in Iio a, f x) * f a = ∏ x in Iic 
a, f x
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Finset.mul_prod_Iio_eq_prod_Iic`：mul_prod_Iio_eq_prod_Iic (a : α) : f a 
* ∏ x in Iio a, f x = ∏ x in Iic a, f x
-/
lemma prod_Iio_mul_eq_prod_Iic (a : α) : (∏ x ∈ Iio a, f x) * f a = ∏ x ∈ Iic a, f x := by
  rw [mul_comm, mul_prod_Iio_eq_prod_Iic]

end LocallyFiniteOrderBot

end PartialOrder

section LinearOrder
variable [LinearOrder α]

section LocallyFiniteOrder
variable [LocallyFiniteOrder α] [AddMonoidWithOne α] [SuccAddOrder α] [NoMaxOrder α]

@[to_additive (dont_translate := α) sum_Ico_add_eq_sum_Ico_add_one]
/-
**Finset.prod_Ico_mul_eq_prod_Ico_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_Ico_mul_eq_prod_Ico_add_one (hab : a <= b) (f : α -> M) : (∏ x in Ico
 a b, f x) * f b = ∏ x in Ico a (b + 1), f x
参数：hab : a <= b；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.insert_Ico_right_eq_Ico_add_one`：insert_Ico_right_eq_Ico_add_one 
(h : a <= b) : insert b (Ico a b) = Ico a (b + 1)
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.right_notMem_Ico`：right_notMem_Ico : b ∉ Ico a b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma prod_Ico_mul_eq_prod_Ico_add_one (hab : a ≤ b) (f : α → M) :
    (∏ x ∈ Ico a b, f x) * f b = ∏ x ∈ Ico a (b + 1), f x := by
  rw [← Finset.insert_Ico_right_eq_Ico_add_one hab, prod_insert right_notMem_Ico, mul_comm]

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

@[to_additive (dont_translate := α)]
/-
**Finset.prod_Iio_add_one_comm** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_Iio_add_one_comm [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] (a :
 α) (f : α -> M) : ∏ i < a + 1, f i = f a * (∏ i < a, f i)
参数：a : α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Finset.Iio_add_one_eq_Iic`：Iio_add_one_eq_Iic (b : α) : Iio (b + 1) = Ii
c b
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_Iio_add_one_comm [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
    (a : α) (f : α → M) : ∏ i < a + 1, f i = f a * (∏ i < a, f i) := by
  simp [Iio_add_one_eq_Iic, ← Iio_insert, Finset.prod_insert]

@[to_additive (dont_translate := α) (attr := simp)]
/-
**Finset.prod_Iio_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_Iio_add_one [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] (a : α) (
f : α -> M) : ∏ i < a + 1, f i = (∏ i < a, f i) * f a
参数：a : α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.prod_Iio_add_one_comm`：prod_Iio_add_one_comm [Add α] [One α] [Suc
cAddOrder α] [NoMaxOrder α] (a : α) (f : α -> M) : ∏ i < a + 1, f i = f a * (∏ i
 < a, f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_Iio_add_one [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
    (a : α) (f : α → M) : ∏ i < a + 1, f i = (∏ i < a, f i) * f a := by
  simp_rw [prod_Iio_add_one_comm, mul_comm]

@[to_additive (dont_translate := α)]
/-
**Finset.prod_Iic_add_one_comm** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_Iic_add_one_comm [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] (a :
 α) (f : α -> M) : ∏ i <= a + 1, f i = f (a + 1) * (∏ i <= a, f i)
参数：a : α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Finset.prod_Iio_add_one_comm`：prod_Iio_add_one_comm [Add α] [One α] [Suc
cAddOrder α] [NoMaxOrder α] (a : α) (f : α -> M) : ∏ i < a + 1, f i = f a * (∏ i
 < a, f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_Iic_add_one_comm [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
    (a : α) (f : α → M) : ∏ i ≤ a + 1, f i = f (a + 1) * (∏ i ≤ a, f i) := by
  simp only [← Iio_insert, mem_Iio, lt_self_iff_false, not_false_eq_true, prod_insert,
    prod_Iio_add_one_comm]

@[to_additive (dont_translate := α) (attr := simp)]
/-
**Finset.prod_Iic_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_Iic_add_one [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] (a : α) (
f : α -> M) : ∏ i <= a + 1, f i = (∏ i <= a, f i) * f (a + 1)
参数：a : α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.prod_Iic_add_one_comm`：prod_Iic_add_one_comm [Add α] [One α] [Suc
cAddOrder α] [NoMaxOrder α] (a : α) (f : α -> M) : ∏ i <= a + 1, f i = f (a + 1)
 * (∏ i <= a, f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_Iic_add_one [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
    (a : α) (f : α → M) : ∏ i ≤ a + 1, f i = (∏ i ≤ a, f i) * f (a + 1) := by
  simp_rw [prod_Iic_add_one_comm, mul_comm]

end LocallyFiniteOrderBot

section LocallyFiniteOrderTopBot
variable [Fintype α] [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

@[to_additive]
/-
**Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag** 是 Mathlib 中的一个引理，位于命名空间 `Fins
et`。
形式化陈述：prod_prod_Ioi_mul_eq_prod_prod_off_diag (f : α -> α -> M) : ∏ i, ∏ j in Io
i i, f j i * f i j = ∏ i, ∏ j in {i}ᶜ, f j i
参数：f : α -> α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.disjoint_Ioi_Iio`：disjoint_Ioi_Iio (a : α) : Disjoint (Ioi a) (Ii
o a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_disjUnion`：prod_disjUnion (h) : ∏ x in s₁.disjUnion s₂ h, f 
x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Finset.prod_sigma'`：prod_sigma' {σ : α -> Type*} (s : Finset α) (t : for
all a, Finset (σ a)) (f : forall a, σ a -> β) : (∏ a in s, ∏ s in t a, f a s) = 
∏ x in s…
· 使用引理 `Finset.prod_nbij'`：prod_nbij' (i : ι -> κ) (j : κ -> ι) (hi : forall a i
n s, i a in t) (hj : forall a in t, j a in s) (left_inv : forall a in s, j (i a)
 = a) (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_prod_Ioi_mul_eq_prod_prod_off_diag (f : α → α → M) :
    ∏ i, ∏ j ∈ Ioi i, f j i * f i j = ∏ i, ∏ j ∈ {i}ᶜ, f j i := by
  simp_rw [← Ioi_disjUnion_Iio, prod_disjUnion, prod_mul_distrib]
  congr 1
  rw [prod_sigma', prod_sigma']
  refine prod_nbij' (fun i ↦ ⟨i.2, i.1⟩) (fun i ↦ ⟨i.2, i.1⟩) ?_ ?_ ?_ ?_ ?_ <;> simp

end LocallyFiniteOrderTopBot

end LinearOrder

set_option backward.isDefEq.respectTransparency false in
/-- Given a sequence of finite sets `s₀ ⊆ s₁ ⊆ s₂ ⋯`, the product of `gᵢ` over `i ∈ sₙ` is equal
to `∏_{i ∈ s₀} gᵢ` * `∏_{j < n, i ∈ sⱼ₊₁ \ sⱼ} gᵢ`. -/
@[to_additive /-- Given a sequence of finite sets `s₀ ⊆ s₁ ⊆ s₂ ⋯`, the sum of `gᵢ` over `i ∈ sₙ` is
equal to `∑_{i ∈ s₀} gᵢ` + `∑_{j < n, i ∈ sⱼ₊₁ \ sⱼ} gᵢ`.-/]
/-
**Finset.prod_eq_prod_range_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_eq_prod_range_sdiff {α β : Type*} [DecidableEq α] [CommMonoid β] (s :
 Nat -> Finset α) (hs : Monotone s) (g : α -> β) (n : Nat) : ∏ i in s n, g i = (
∏ i in s 0, g i) * ∏ i in range n, ∏ j in s (i + 1) \ s i, g j
参数：s : Nat -> Finset α；hs : Monotone s；g : α -> β；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.partialSups_eq`：Monotone.partialSups_eq {f : ι -> α} (hf : Mono
tone f) : partialSups f = f
· 使用定理 `Pairwise.set_pairwise`：Pairwise.set_pairwise (hl : Pairwise R l) [Std.Sy
mm R] : { x | x in l }.Pairwise R
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
· 使用引理 `Finset.disjiUnion_Iic_disjointed`：Finset.disjiUnion_Iic_disjointed [Deci
dableEq α] (n : ι) (t : ι -> Finset α) : (Iic n).disjiUnion (disjointed t) ((dis
joint_disjointed t).se…
· 使用定理 `Finset.Iic_eq_Icc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] [inst_2 : OrderBot α] (a : α),   Finset.Iic a = Finset.Icc ⊥ a
· 使用定理 `Finset.prod_disjiUnion`：prod_disjiUnion (s : Finset κ) (t : κ -> Finset 
ι) (h) : ∏ x in s.disjiUnion t h, f x = ∏ i in s, ∏ x in t i, f x
· 使用定理 `Nat.bot_eq_zero`：⊥ = 0
· 使用定理 `Nat.range_succ_eq_Icc_zero`：range_succ_eq_Icc_zero (n : Nat) : range (n 
+ 1) = Icc 0 n
· 使用定理 `Finset.prod_range_succ'`：∀ {M : Type u_4} [inst : CommMonoid M] (f : ℕ →
 M) (n : ℕ),   ∏ k ∈ Finset.range (n + 1), f k = (∏ k ∈ Finset.range n, f (k + 1
)) * f 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `disjointed_zero`：disjointed_zero (f : Nat -> α) : disjointed f 0 = f 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.apply_sup_eq_sup_comp_of_nonempty`：apply_sup_eq_sup_comp_of_nonem
pty [OrderBot α] [SemilatticeSup β] [OrderBot β] {g : α -> β} (mono_g : Monotone
 g) (H : s.Nonempty) : g (s.su…
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用定理 `Finset.sup_Iic`：∀ {α : Type u_2} [inst : SemilatticeSup α] [inst_1 : Loc
allyFiniteOrderBot α] [inst_2 : OrderBot α] (a : α),   (Finset.Iic a).sup id = a
-/
lemma prod_eq_prod_range_sdiff
    {α β : Type*} [DecidableEq α] [CommMonoid β] (s : ℕ → Finset α) (hs : Monotone s)
    (g : α → β) (n : ℕ) :
    ∏ i ∈ s n, g i = (∏ i ∈ s 0, g i) * ∏ i ∈ range n, ∏ j ∈ s (i + 1) \ s i, g j := by
  conv_lhs => rw [← hs.partialSups_eq, ← disjiUnion_Iic_disjointed, Iic_eq_Icc,
    prod_disjiUnion, Nat.bot_eq_zero, ← Nat.range_succ_eq_Icc_zero, prod_range_succ', mul_comm]
  congrm (∏ x ∈ ?_, g x) * ∏ k ∈ range n, ∏ x ∈ s (k + 1) \ ?_, g x
  · simp
  · change (Iic k).sup (s ∘ id) = s k
    rw [← apply_sup_eq_sup_comp_of_nonempty hs nonempty_Iic, sup_Iic]

end Finset

