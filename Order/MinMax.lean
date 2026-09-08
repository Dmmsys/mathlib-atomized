/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.OpClass
public import Mathlib.Order.Lattice

/-!
# `max` and `min`

This file proves basic properties about maxima and minima on a `LinearOrder`.

## Tags

min, max
-/

public section


universe u v

variable {α : Type u} {β : Type v}

section

variable [LinearOrder α] [LinearOrder β] {f : α → β} {s : Set α} {a b c d : α}

-- translate from lattices to linear orders (sup → max, inf → min)
@[to_dual max_le_iff]
/-
**le_min_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_min_iff : c <= min a b ↔ c <= a ∧ c <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
-/
theorem le_min_iff : c ≤ min a b ↔ c ≤ a ∧ c ≤ b :=
  le_inf_iff

@[to_dual min_le_iff]
/-
**le_max_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_iff`：le_sup_iff : a <= b ⊔ c ↔ a <= b ∨ a <= c
-/
theorem le_max_iff : a ≤ max b c ↔ a ≤ b ∨ a ≤ c :=
  le_sup_iff

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.LawfulOrderSup α where
  max_le_iff _ _ _ := max_le_iff

@[to_dual max_lt_iff]
/-
**lt_min_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_min_iff : a < min b c ↔ a < b ∧ a < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_inf_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, a < min b
 c ↔ a < b ∧ a < c
-/
theorem lt_min_iff : a < min b c ↔ a < b ∧ a < c :=
  lt_inf_iff

@[to_dual min_lt_iff]
/-
**lt_max_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_max_iff : a < max b c ↔ a < b ∨ a < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_sup_iff`：lt_sup_iff : a < b ⊔ c ↔ a < b ∨ a < c
-/
theorem lt_max_iff : a < max b c ↔ a < b ∨ a < c :=
  lt_sup_iff

@[to_dual]
/-
**max_le_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_le_max : a <= c -> b <= d -> max a b <= max c d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
-/
theorem max_le_max : a ≤ c → b ≤ d → max a b ≤ max c d :=
  sup_le_sup

@[to_dual]
/-
**max_le_max_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_le_max_left (c) (h : a <= b) : max c a <= max c b
参数：c；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup_left`：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
-/
theorem max_le_max_left (c) (h : a ≤ b) : max c a ≤ max c b := sup_le_sup_left h c

@[to_dual]
/-
**max_le_max_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_le_max_right (c) (h : a <= b) : max a c <= max b c
参数：c；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup_right`：sup_le_sup_right (h₁ : a <= b) (c) : a ⊔ c <= b ⊔ c
-/
theorem max_le_max_right (c) (h : a ≤ b) : max a c ≤ max b c := sup_le_sup_right h c

@[to_dual min_le_of_left_le]
/-
**le_max_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_max_of_le_left : a <= b -> a <= max b c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
-/
theorem le_max_of_le_left : a ≤ b → a ≤ max b c :=
  le_sup_of_le_left

@[to_dual min_le_of_right_le]
/-
**le_max_of_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_max_of_le_right : a <= c -> a <= max b c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
-/
theorem le_max_of_le_right : a ≤ c → a ≤ max b c :=
  le_sup_of_le_right

@[to_dual min_lt_of_left_lt]
/-
**lt_max_of_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_max_of_lt_left (h : a < b) : a < max b c
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem lt_max_of_lt_left (h : a < b) : a < max b c :=
  h.trans_le (le_max_left b c)

@[to_dual min_lt_of_right_lt]
/-
**lt_max_of_lt_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_max_of_lt_right (h : a < c) : a < max b c
参数：h : a < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem lt_max_of_lt_right (h : a < c) : a < max b c :=
  h.trans_le (le_max_right b c)

@[to_dual]
/-
**max_min_distrib_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：max_min_distrib_left (a b c : α) : max a (min b c) = min (max a b) (max a 
c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
-/
lemma max_min_distrib_left (a b c : α) : max a (min b c) = min (max a b) (max a c) :=
  sup_inf_left _ _ _

@[to_dual]
/-
**max_min_distrib_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：max_min_distrib_right (a b c : α) : max (min a b) c = min (max a c) (max b
 c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
-/
lemma max_min_distrib_right (a b c : α) : max (min a b) c = min (max a c) (max b c) :=
  sup_inf_right _ _ _
/-
**min_le_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_le_max : min a b <= max a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem min_le_max : min a b ≤ max a b :=
  le_trans (min_le_left a b) (le_max_left a b)

@[to_dual]
/-
**min_eq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_eq_left_iff : min a b = a ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
-/
theorem min_eq_left_iff : min a b = a ↔ a ≤ b :=
  inf_eq_left

@[to_dual]
/-
**min_eq_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_eq_right_iff : min a b = b ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
-/
theorem min_eq_right_iff : min a b = b ↔ b ≤ a :=
  inf_eq_right

/-- For elements `a` and `b` of a linear order, either `min a b = a` and `a ≤ b`,
or `min a b = b` and `b < a`.
Use cases on this lemma to automate linarith in inequalities -/
@[to_dual
/-- For elements `a` and `b` of a linear order, either `max a b = a` and `b ≤ a`,
or `max a b = b` and `a < b`.
Use cases on this lemma to automate linarith in inequalities -/]
/-
**min_cases** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_cases (a b : α) : min a b = a ∧ a <= b ∨ min a b = b ∧ b < a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem min_cases (a b : α) : min a b = a ∧ a ≤ b ∨ min a b = b ∧ b < a := by
  grind

@[to_dual]
/-
**min_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_eq_iff : min a b = c ↔ a = c ∧ a <= b ∨ b = c ∧ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem min_eq_iff : min a b = c ↔ a = c ∧ a ≤ b ∨ b = c ∧ b ≤ a := by
  grind

@[to_dual]
/-
**min_lt_min_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_lt_min_left_iff : min a c < min b c ↔ a < b ∧ a < c
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem min_lt_min_left_iff : min a c < min b c ↔ a < b ∧ a < c := by
  grind

@[to_dual]
/-
**min_lt_min_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_lt_min_right_iff : min a b < min a c ↔ b < c ∧ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem min_lt_min_right_iff : min a b < min a c ↔ b < c ∧ b < a := by
  grind

/-- An instance asserting that `max a a = a` -/
@[to_dual /-- An instance asserting that `min a a = a` -/]
/-
**max_idem** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：max_idem : Std.IdempotentOp (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
An instance asserting that `max a a = a`
-/
instance max_idem : Std.IdempotentOp (α := α) max where
  idempotent := by simp
/-
**min_lt_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_lt_max : min a b < max a b ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_lt_sup`：∀ {α : Type u} [inst : Lattice α] {a b : α}, a ⊓ b < a ⊔ b ↔
 a ≠ b
-/
theorem min_lt_max : min a b < max a b ↔ a ≠ b :=
  inf_lt_sup

@[to_dual]
/-
**max_lt_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_lt_max (h₁ : a < c) (h₂ : b < d) : max a b < max c d
参数：h₁ : a < c；h₂ : b < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `lt_max_of_lt_left`：lt_max_of_lt_left (h : a < b) : a < max b c
· 使用定理 `lt_max_of_lt_right`：lt_max_of_lt_right (h : a < c) : a < max b c
-/
theorem max_lt_max (h₁ : a < c) (h₂ : b < d) : max a b < max c d :=
  max_lt (lt_max_of_lt_left h₁) (lt_max_of_lt_right h₂)

@[to_dual]
/-
**min_right_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_right_comm (a b c : α) : min (min a b) c = min (min a c) b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_assoc`：min_assoc (a b c : α) : min (min a b) c = min a (min b c)
· 使用引理 `min_comm`：min_comm (a b : α) : min a b = min b a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma min_right_comm (a b c : α) : min (min a b) c = min (min a c) b := by
  rw [min_assoc, min_comm b, ← min_assoc]

@[deprecated (since := "2026-03-22")] alias Max.left_comm := max_left_comm
@[deprecated (since := "2026-03-22")] alias Max.right_comm := max_right_comm

@[to_dual]
/-
**MonotoneOn.map_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.map_max (hf : MonotoneOn f s) (ha : a in s) (hb : b in s) : f (
max a b) = max (f a) (f b)
参数：hf : MonotoneOn f s；ha : a in s；hb : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
theorem MonotoneOn.map_max (hf : MonotoneOn f s) (ha : a ∈ s) (hb : b ∈ s) : f (max a b) =
    max (f a) (f b) := by
  rcases le_total a b with h | h <;>
    simp only [max_eq_right, max_eq_left, hf ha hb, hf hb ha, h]

@[to_dual]
/-
**AntitoneOn.map_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.map_max (hf : AntitoneOn f s) (ha : a in s) (hb : b in s) : f (
max a b) = min (f a) (f b)
参数：hf : AntitoneOn f s；ha : a in s；hb : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.map_max`：MonotoneOn.map_max (hf : MonotoneOn f s) (ha : a in 
s) (hb : b in s) : f (max a b) = max (f a) (f b)
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…
-/
theorem AntitoneOn.map_max (hf : AntitoneOn f s) (ha : a ∈ s) (hb : b ∈ s) : f (max a b) =
    min (f a) (f b) := hf.dual_right.map_max ha hb

@[to_dual]
/-
**Monotone.map_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.map_max (hf : Monotone f) : f (max a b) = max (f a) (f b)
参数：hf : Monotone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
-/
theorem Monotone.map_max (hf : Monotone f) : f (max a b) = max (f a) (f b) := by
  rcases le_total a b with h | h <;> simp [h, hf h]

@[to_dual]
/-
**Antitone.map_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.map_max (hf : Antitone f) : f (max a b) = min (f a) (f b)
参数：hf : Antitone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
-/
theorem Antitone.map_max (hf : Antitone f) : f (max a b) = min (f a) (f b) := by
  rcases le_total a b with h | h <;> simp [h, hf h]

@[to_dual]
/-
**min_choice** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_choice (a b : α) : min a b = a ∨ min a b = b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem min_choice (a b : α) : min a b = a ∨ min a b = b := by cases le_total a b <;> simp [*]

@[to_dual le_of_le_min_left]
/-
**le_of_max_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_max_le_left {a b c : α} (h : max a b <= c) : a <= c
参数：h : max a b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem le_of_max_le_left {a b c : α} (h : max a b ≤ c) : a ≤ c :=
  le_trans (le_max_left _ _) h

@[to_dual le_of_le_min_right]
/-
**le_of_max_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_max_le_right {a b c : α} (h : max a b <= c) : b <= c
参数：h : max a b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem le_of_max_le_right {a b c : α} (h : max a b ≤ c) : b ≤ c :=
  le_trans (le_max_right _ _) h
/-
**instCommutativeMax** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : LinearOrder α], Std.Commutative max
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
-/
@[to_dual] instance instCommutativeMax : Std.Commutative (α := α) max where comm := max_comm
/-
**instAssociativeMax** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : LinearOrder α], Std.Associative max
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_assoc`：∀ {α : Type u_1} [inst : LinearOrder α] (a b c : α), max (max
 a b) c = max a (max b c)
-/
@[to_dual] instance instAssociativeMax : Std.Associative (α := α) max where assoc := max_assoc

@[to_dual]
/-
**max_left_commutative** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_left_commutative : LeftCommutative (max : α -> α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_left_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b c : α), max 
a (max b c) = max b (max a c)
-/
theorem max_left_commutative : LeftCommutative (max : α → α → α) := ⟨max_left_comm⟩

end

