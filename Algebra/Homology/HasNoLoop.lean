/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Complex shapes with no loop

Let `c : ComplexShape ι`. We define a type class `c.HasNoLoop`
which expresses that `¬ c.Rel i i` for all `i : ι`.

-/

public section

namespace ComplexShape

variable {ι : Type*}

/-- The condition that `c.Rel i i` does not hold for any `i`. -/
/-
**ComplexShape.HasNoLoop** 是 Mathlib 中的一个归纳类型，位于命名空间 `ComplexShape`。
形式化陈述：{ι : Type u_1} → ComplexShape ι → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that `c.Rel i i` does not hold for any `i`.
-/
class HasNoLoop (c : ComplexShape ι) : Prop where
  not_rel_self (i : ι) : ¬ c.Rel i i

section

variable (c : ComplexShape ι) [c.HasNoLoop] (j : ι)

/-
**ComplexShape.not_rel_self** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape`。
形式化陈述：not_rel_self : ¬ c.Rel j j
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.HasNoLoop.not_rel_self`：∀ {ι : Type u_1} {c : ComplexShape 
ι} [self : c.HasNoLoop] (i : ι), ¬c.Rel i i
-/
lemma not_rel_self : ¬ c.Rel j j :=
  HasNoLoop.not_rel_self j

variable {j} in
/-
**ComplexShape.not_rel_of_eq** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape`。
形式化陈述：not_rel_of_eq {j' : ι} (h : j = j') : ¬ c.Rel j j'
参数：h : j = j'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.not_rel_self`：not_rel_self : ¬ c.Rel j j
-/
lemma not_rel_of_eq {j' : ι} (h : j = j') : ¬ c.Rel j j' := by
  subst h
  exact c.not_rel_self j
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : c.symm.HasNoLoop where
  not_rel_self j := c.not_rel_self j
/-
**ComplexShape.exists_distinct_prev_or** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape`。
形式化陈述：exists_distinct_prev_or : (exists (k : ι), c.Rel j k ∧ j != k) ∨ forall (k
 : ι), ¬ c.Rel j k
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_distinct_prev_or :
    (∃ (k : ι), c.Rel j k ∧ j ≠ k) ∨ ∀ (k : ι), ¬ c.Rel j k := by
  grind +splitIndPred
/-
**ComplexShape.exists_distinct_next_or** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape`。
形式化陈述：exists_distinct_next_or : (exists (i : ι), c.Rel i j ∧ i != j) ∨ forall (i
 : ι), ¬ c.Rel i j
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_distinct_next_or :
    (∃ (i : ι), c.Rel i j ∧ i ≠ j) ∨ ∀ (i : ι), ¬ c.Rel i j := by
  grind +splitIndPred
/-
**ComplexShape.hasNoLoop_up'** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape`。
形式化陈述：hasNoLoop_up' {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCan
celAdd α] (a : α) (ha : a != 0) : (up' a).HasNoLoop where not_rel_self i (hi : _
 = _)
参数：a : α；ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma hasNoLoop_up' {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    (a : α) (ha : a ≠ 0) :
    (up' a).HasNoLoop where
  not_rel_self i (hi : _ = _) :=
    ha (add_left_cancel (by rw [add_zero, hi]))
/-
**ComplexShape.hasNoLoop_down'** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape`。
形式化陈述：hasNoLoop_down' {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftC
ancelAdd α] (a : α) (ha : a != 0) : (down' a).HasNoLoop
参数：a : α；ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.hasNoLoop_up'`：hasNoLoop_up' {α : Type*} [AddZeroClass α] [
IsRightCancelAdd α] [IsLeftCancelAdd α] (a : α) (ha : a != 0) : (up' a).HasNoLoo
p where not_rel_…
-/
lemma hasNoLoop_down' {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    (a : α) (ha : a ≠ 0) :
    (down' a).HasNoLoop := by
  have := hasNoLoop_up' a ha
  exact inferInstanceAs (up' a).symm.HasNoLoop
/-
**ComplexShape.hasNoLoop_up** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape`。
形式化陈述：hasNoLoop_up {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCanc
elAdd α] [One α] (ha : (1 : α) != 0) : (up α).HasNoLoop
参数：ha : (1 : α) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.hasNoLoop_up'`：hasNoLoop_up' {α : Type*} [AddZeroClass α] [
IsRightCancelAdd α] [IsLeftCancelAdd α] (a : α) (ha : a != 0) : (up' a).HasNoLoo
p where not_rel_…
-/
lemma hasNoLoop_up {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    [One α] (ha : (1 : α) ≠ 0) :
    (up α).HasNoLoop :=
  hasNoLoop_up' _ ha
/-
**ComplexShape.hasNoLoop_down** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape`。
形式化陈述：hasNoLoop_down {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCa
ncelAdd α] [One α] (ha : (1 : α) != 0) : (down α).HasNoLoop
参数：ha : (1 : α) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.hasNoLoop_down'`：hasNoLoop_down' {α : Type*} [AddZeroClass 
α] [IsRightCancelAdd α] [IsLeftCancelAdd α] (a : α) (ha : a != 0) : (down' a).Ha
sNoLoop
-/
lemma hasNoLoop_down {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    [One α] (ha : (1 : α) ≠ 0) :
    (down α).HasNoLoop :=
  hasNoLoop_down' _ ha

end

/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (up ℤ).HasNoLoop := hasNoLoop_up (by simp)
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (up ℕ).HasNoLoop := hasNoLoop_up (by simp)
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (down ℤ).HasNoLoop := hasNoLoop_down (by simp)
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (down ℕ).HasNoLoop := hasNoLoop_down (by simp)

end ComplexShape

