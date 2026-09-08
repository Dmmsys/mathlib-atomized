/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.SuccPred.Basic

/-!
# Set intervals in a successor-predecessor order

This file proves relations between the various set intervals in a successor/predecessor order.

## Notes

Please keep in sync with:
* `Mathlib/Algebra/Order/Interval/Finset/SuccPred.lean`
* `Mathlib/Algebra/Order/Interval/Set/SuccPred.lean`
* `Mathlib/Order/Interval/Finset/SuccPred.lean`

## TODO

Copy over `insert` lemmas from `Mathlib/Order/Interval/Finset/Nat.lean`.
-/

public section

assert_not_exists MonoidWithZero

open Order

namespace Set
variable {α : Type*} [LinearOrder α]

/-! ### Two-sided intervals -/

section SuccOrder
variable [SuccOrder α] {a b : α}

/-!
#### Orders possibly with maximal elements

##### Equalities of intervals
-/

/-
**Set.Ico_succ_left_eq_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ico_succ_left_eq_Ioo (a b : α) : Ico (succ a) b = Ioo a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用定理 `IsMax.not_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, IsMax a → 
¬a < b
· 使用定理 `IsMax.mono`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, IsMax a → a 
≤ b → IsMax b
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
co a b ↔ a ≤ x ∧ x < b
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
· 使用定理 `Order.succ_le_iff_of_not_isMax`：succ_le_iff_of_not_isMax (ha : ¬IsMax a)
 : succ a <= b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
#### Orders possibly with maximal elements

##### Equalities of intervals
-/
lemma Ico_succ_left_eq_Ioo (a b : α) : Ico (succ a) b = Ioo a b := by
  by_cases ha : IsMax a
  · rw [Ico_eq_empty (ha.mono <| le_succ _).not_lt, Ioo_eq_empty ha.not_lt]
  · ext x
    rw [mem_Ico, mem_Ioo, succ_le_iff_of_not_isMax ha]
/-
**Set.Icc_succ_left_eq_Ioc_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Icc_succ_left_eq_Ioc_of_not_isMax (ha : ¬ IsMax a) (b : α) : Icc (succ a) 
b = Ioc a b
参数：ha : ¬ IsMax a；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `Set.mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oc a b ↔ a < x ∧ x ≤ b
· 使用定理 `Order.succ_le_iff_of_not_isMax`：succ_le_iff_of_not_isMax (ha : ¬IsMax a)
 : succ a <= b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Icc_succ_left_eq_Ioc_of_not_isMax (ha : ¬ IsMax a) (b : α) : Icc (succ a) b = Ioc a b := by
  ext x; rw [mem_Icc, mem_Ioc, succ_le_iff_of_not_isMax ha]
/-
**Set.Ico_succ_right_eq_Icc_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ico_succ_right_eq_Icc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico a (succ 
b) = Icc a b
参数：hb : ¬ IsMax b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
co a b ↔ a ≤ x ∧ x < b
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Ico_succ_right_eq_Icc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico a (succ b) = Icc a b := by
  ext x; rw [mem_Ico, mem_Icc, lt_succ_iff_of_not_isMax hb]
/-
**Set.Ioo_succ_right_eq_Ioc_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioo_succ_right_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ioo a (succ 
b) = Ioc a b
参数：hb : ¬ IsMax b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
· 使用定理 `Set.mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oc a b ↔ a < x ∧ x ≤ b
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Ioo_succ_right_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ioo a (succ b) = Ioc a b := by
  ext x; rw [mem_Ioo, mem_Ioc, lt_succ_iff_of_not_isMax hb]
/-
**Set.Ico_succ_succ_eq_Ioc_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ico_succ_succ_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico (succ a) 
(succ b) = Ioc a b
参数：hb : ¬ IsMax b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.Ico_succ_left_eq_Ioo`：Ico_succ_left_eq_Ioo (a b : α) : Ico (succ a) 
b = Ioo a b
· 使用引理 `Set.Ioo_succ_right_eq_Ioc_of_not_isMax`：Ioo_succ_right_eq_Ioc_of_not_isM
ax (hb : ¬ IsMax b) (a : α) : Ioo a (succ b) = Ioc a b
-/
lemma Ico_succ_succ_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) :
    Ico (succ a) (succ b) = Ioc a b := by
  rw [Ico_succ_left_eq_Ioo, Ioo_succ_right_eq_Ioc_of_not_isMax hb]

/-! ##### Inserting into intervals -/

/-
**Set.insert_Icc_succ_left_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Icc_succ_left_eq_Icc (h : a <= b) : insert a (Icc (succ a) b) = Icc
 a b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
##### Inserting into intervals
-/
lemma insert_Icc_succ_left_eq_Icc (h : a ≤ b) : insert a (Icc (succ a) b) = Icc a b := by
  ext x; simp [or_and_left, eq_comm, ← le_iff_eq_or_succ_le]; aesop
/-
**Set.insert_Icc_right_eq_Icc_succ** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Icc_right_eq_Icc_succ (h : a <= succ b) : insert (succ b) (Icc a b)
 = Icc a (succ b)
参数：h : a <= succ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma insert_Icc_right_eq_Icc_succ (h : a ≤ succ b) :
    insert (succ b) (Icc a b) = Icc a (succ b) := by
  ext x; simp [or_and_left, le_succ_iff_eq_or_le]; simp_all
/-
**Set.insert_Ico_right_eq_Ico_succ_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Ico_right_eq_Ico_succ_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) : 
insert b (Ico a b) = Ico a (succ b)
参数：h : a <= b；hb : ¬ IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.Ico_succ_right_of_not_isMax`：Ico_succ_right_of_not_isMax (hb : ¬Is
Max b) : Ico a (succ b) = Icc a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ico_insert_right`：Ico_insert_right (h : a <= b) : insert b (Ico a b)
 = Icc a b
-/
lemma insert_Ico_right_eq_Ico_succ_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert b (Ico a b) = Ico a (succ b) := by
  rw [Ico_succ_right_of_not_isMax hb, ← Ico_insert_right h]
/-
**Set.insert_Ico_succ_left_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Ico_succ_left_eq_Ico (h : a < b) : insert a (Ico (succ a) b) = Ico 
a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.Ico_succ_left_of_not_isMax`：Ico_succ_left_of_not_isMax (ha : ¬IsMa
x a) : Ico (succ a) b = Ioo a b
· 使用定理 `LT.lt.not_isMax`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b →
 ¬IsMax a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioo_insert_left`：Ioo_insert_left (h : a < b) : insert a (Ioo a b) = 
Ico a b
-/
lemma insert_Ico_succ_left_eq_Ico (h : a < b) : insert a (Ico (succ a) b) = Ico a b := by
  rw [Ico_succ_left_of_not_isMax h.not_isMax, ← Ioo_insert_left h]
/-
**Set.insert_Ioc_right_eq_Ioc_succ_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Ioc_right_eq_Ioc_succ_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) : 
insert (succ b) (Ioc a b) = Ioc a (succ b)
参数：h : a <= b；hb : ¬ IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Order.lt_succ_of_le_of_not_isMax`：lt_succ_of_le_of_not_isMax (hab : b <=
 a) (ha : ¬IsMax a) : b < succ a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma insert_Ioc_right_eq_Ioc_succ_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert (succ b) (Ioc a b) = Ioc a (succ b) := by
  ext x; simp +contextual [or_and_left, le_succ_iff_eq_or_le, lt_succ_of_le_of_not_isMax h hb]
/-
**Set.insert_Ioc_succ_left_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Ioc_succ_left_eq_Ioc (h : a < b) : insert (succ a) (Ioc (succ a) b)
 = Ioc a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ioc_insert_left`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 b ≤ a → insert b (Set.Ioc b a) = Set.Icc b a
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `Order.Icc_succ_left_of_not_isMax`：Icc_succ_left_of_not_isMax (ha : ¬IsMa
x a) : Icc (succ a) b = Ioc a b
· 使用定理 `LT.lt.not_isMax`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b →
 ¬IsMax a
-/
lemma insert_Ioc_succ_left_eq_Ioc (h : a < b) : insert (succ a) (Ioc (succ a) b) = Ioc a b := by
  rw [Ioc_insert_left (succ_le_of_lt h), Icc_succ_left_of_not_isMax h.not_isMax]

/-!
#### Orders with no maximal elements

##### Equalities of intervals
-/

variable [NoMaxOrder α]

/-
**Set.Icc_succ_left_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Icc_succ_left_eq_Ioc (a b : α) : Icc (succ a) b = Ioc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Icc_succ_left_eq_Ioc_of_not_isMax`：Icc_succ_left_eq_Ioc_of_not_isMax
 (ha : ¬ IsMax a) (b : α) : Icc (succ a) b = Ioc a b
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
lemma Icc_succ_left_eq_Ioc (a b : α) : Icc (succ a) b = Ioc a b :=
  Icc_succ_left_eq_Ioc_of_not_isMax (not_isMax _) _
/-
**Set.Ico_succ_right_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ico_succ_right_eq_Icc (a b : α) : Ico a (succ b) = Icc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Ico_succ_right_eq_Icc_of_not_isMax`：Ico_succ_right_eq_Icc_of_not_isM
ax (hb : ¬ IsMax b) (a : α) : Ico a (succ b) = Icc a b
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
lemma Ico_succ_right_eq_Icc (a b : α) : Ico a (succ b) = Icc a b :=
  Ico_succ_right_eq_Icc_of_not_isMax (not_isMax _) _
/-
**Set.Ioo_succ_right_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioo_succ_right_eq_Ioc (a b : α) : Ioo a (succ b) = Ioc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Ioo_succ_right_eq_Ioc_of_not_isMax`：Ioo_succ_right_eq_Ioc_of_not_isM
ax (hb : ¬ IsMax b) (a : α) : Ioo a (succ b) = Ioc a b
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
lemma Ioo_succ_right_eq_Ioc (a b : α) : Ioo a (succ b) = Ioc a b :=
  Ioo_succ_right_eq_Ioc_of_not_isMax (not_isMax _) _
/-
**Set.Ico_succ_succ_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ico_succ_succ_eq_Ioc (a b : α) : Ico (succ a) (succ b) = Ioc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Ico_succ_succ_eq_Ioc_of_not_isMax`：Ico_succ_succ_eq_Ioc_of_not_isMax
 (hb : ¬ IsMax b) (a : α) : Ico (succ a) (succ b) = Ioc a b
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
lemma Ico_succ_succ_eq_Ioc (a b : α) : Ico (succ a) (succ b) = Ioc a b :=
  Ico_succ_succ_eq_Ioc_of_not_isMax (not_isMax _) _

/-! ##### Inserting into intervals -/

/-
**Set.insert_Ico_right_eq_Ico_succ** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Ico_right_eq_Ico_succ (h : a <= b) : insert b (Ico a b) = Ico a (su
cc b)
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.insert_Ico_right_eq_Ico_succ_of_not_isMax`：insert_Ico_right_eq_Ico_s
ucc_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) : insert b (Ico a b) = Ico a (suc
c b)
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a

--- 原说明 ---
##### Inserting into intervals
-/
lemma insert_Ico_right_eq_Ico_succ (h : a ≤ b) : insert b (Ico a b) = Ico a (succ b) :=
  insert_Ico_right_eq_Ico_succ_of_not_isMax h (not_isMax _)
/-
**Set.insert_Ioc_right_eq_Ioc_succ** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Ioc_right_eq_Ioc_succ (h : a <= b) : insert (succ b) (Ioc a b) = Io
c a (succ b)
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.insert_Ioc_right_eq_Ioc_succ_of_not_isMax`：insert_Ioc_right_eq_Ioc_s
ucc_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) : insert (succ b) (Ioc a b) = Ioc
 a (succ b)
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
lemma insert_Ioc_right_eq_Ioc_succ (h : a ≤ b) : insert (succ b) (Ioc a b) = Ioc a (succ b) :=
  insert_Ioc_right_eq_Ioc_succ_of_not_isMax h (not_isMax _)

end SuccOrder

section PredOrder
variable [PredOrder α] {a b : α}

/-!
#### Orders possibly with minimal elements

##### Equalities of intervals
-/

/-
**Set.Ioc_pred_right_eq_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioc_pred_right_eq_Ioo (a b : α) : Ioc a (pred b) = Ioo a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `IsMin.not_lt`：IsMin.not_lt (h : IsMin a) : ¬b < a
· 使用定理 `IsMin.mono`：IsMin.mono (ha : IsMin a) (h : b <= a) : IsMin b
· 使用定理 `Order.pred_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredOrder 
α] (a : α), Order.pred a ≤ a
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oc a b ↔ a < x ∧ x ≤ b
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
· 使用定理 `Order.le_pred_iff_of_not_isMin`：∀ {α : Type u_1} [inst : Preorder α] [in
st_1 : PredOrder α] {a b : α}, ¬IsMin a → (b ≤ Order.pred a ↔ b < a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
#### Orders possibly with minimal elements

##### Equalities of intervals
-/
lemma Ioc_pred_right_eq_Ioo (a b : α) : Ioc a (pred b) = Ioo a b := by
  by_cases hb : IsMin b
  · rw [Ioc_eq_empty (hb.mono <| pred_le _).not_lt, Ioo_eq_empty hb.not_lt]
  · ext x
    rw [mem_Ioc, mem_Ioo, le_pred_iff_of_not_isMin hb]
/-
**Set.Icc_pred_right_eq_Ico_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Icc_pred_right_eq_Ico_of_not_isMin (hb : ¬ IsMin b) (a : α) : Icc a (pred 
b) = Ico a b
参数：hb : ¬ IsMin b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `Set.mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
co a b ↔ a ≤ x ∧ x < b
· 使用定理 `Order.le_pred_iff_of_not_isMin`：∀ {α : Type u_1} [inst : Preorder α] [in
st_1 : PredOrder α] {a b : α}, ¬IsMin a → (b ≤ Order.pred a ↔ b < a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Icc_pred_right_eq_Ico_of_not_isMin (hb : ¬ IsMin b) (a : α) : Icc a (pred b) = Ico a b := by
  ext x; rw [mem_Icc, mem_Ico, le_pred_iff_of_not_isMin hb]
/-
**Set.Ioc_pred_left_eq_Icc_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioc_pred_left_eq_Icc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (pred a) 
b = Icc a b
参数：ha : ¬ IsMin a；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oc a b ↔ a < x ∧ x ≤ b
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `Order.pred_lt_iff_of_not_isMin`：∀ {α : Type u_1} [inst : LinearOrder α] 
[inst_1 : PredOrder α] {a b : α}, ¬IsMin a → (Order.pred a < b ↔ a ≤ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Ioc_pred_left_eq_Icc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (pred a) b = Icc a b := by
  ext x; rw [mem_Ioc, mem_Icc, pred_lt_iff_of_not_isMin ha]
/-
**Set.Ioo_pred_left_eq_Ioc_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioo_pred_left_eq_Ioc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioo (pred a) 
b = Ico a b
参数：ha : ¬ IsMin a；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
· 使用定理 `Set.mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
co a b ↔ a ≤ x ∧ x < b
· 使用定理 `Order.pred_lt_iff_of_not_isMin`：∀ {α : Type u_1} [inst : LinearOrder α] 
[inst_1 : PredOrder α] {a b : α}, ¬IsMin a → (Order.pred a < b ↔ a ≤ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Ioo_pred_left_eq_Ioc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioo (pred a) b = Ico a b := by
  ext x; rw [mem_Ioo, mem_Ico, pred_lt_iff_of_not_isMin ha]
/-
**Set.Ioc_pred_pred_eq_Ico_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioc_pred_pred_eq_Ico_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (pred a) 
(pred b) = Ico a b
参数：ha : ¬ IsMin a；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.Ioc_pred_right_eq_Ioo`：Ioc_pred_right_eq_Ioo (a b : α) : Ioc a (pred
 b) = Ioo a b
· 使用引理 `Set.Ioo_pred_left_eq_Ioc_of_not_isMin`：Ioo_pred_left_eq_Ioc_of_not_isMin
 (ha : ¬ IsMin a) (b : α) : Ioo (pred a) b = Ico a b
-/
lemma Ioc_pred_pred_eq_Ico_of_not_isMin (ha : ¬ IsMin a) (b : α) :
    Ioc (pred a) (pred b) = Ico a b := by
  rw [Ioc_pred_right_eq_Ioo, Ioo_pred_left_eq_Ioc_of_not_isMin ha]

/-! ##### Inserting into intervals -/

/-
**Set.insert_Icc_pred_right_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Icc_pred_right_eq_Icc (h : a <= b) : insert b (Icc a (pred b)) = Ic
c a b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
##### Inserting into intervals
-/
lemma insert_Icc_pred_right_eq_Icc (h : a ≤ b) : insert b (Icc a (pred b)) = Icc a b := by
  ext x; simp [or_and_left, ← le_iff_eq_or_le_pred]; simp_all
/-
**Set.insert_Icc_left_eq_Icc_pred** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Icc_left_eq_Icc_pred (h : pred a <= b) : insert (pred a) (Icc a b) 
= Icc (pred a) b
参数：h : pred a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma insert_Icc_left_eq_Icc_pred (h : pred a ≤ b) :
    insert (pred a) (Icc a b) = Icc (pred a) b := by
  ext x; simp [or_and_left, pred_le_iff_eq_or_le]; simp_all
/-
**Set.insert_Ioc_left_eq_Ioc_pred_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Ioc_left_eq_Ioc_pred_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) : i
nsert a (Ioc a b) = Ioc (pred a) b
参数：h : a <= b；ha : ¬ IsMin a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.Ioc_pred_left_of_not_isMin`：∀ {α : Type u_1} [inst : LinearOrder α
] [inst_1 : PredOrder α] {a b : α},   ¬IsMin b → Set.Ioc (Order.pred b) a = Set.
Icc b a
· 使用定理 `Set.Ioc_insert_left`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 b ≤ a → insert b (Set.Ioc b a) = Set.Icc b a
-/
lemma insert_Ioc_left_eq_Ioc_pred_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert a (Ioc a b) = Ioc (pred a) b := by
  rw [Ioc_pred_left_of_not_isMin ha, Ioc_insert_left h]
/-
**Set.insert_Ioc_pred_right_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Ioc_pred_right_eq_Ioc (h : a < b) : insert b (Ioc a (pred b)) = Ioc
 a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.Ioc_pred_right_of_not_isMin`：∀ {α : Type u_1} [inst : Preorder α] 
[inst_1 : PredOrder α] {a b : α}, ¬IsMin a → Set.Ioc b (Order.pred a) = Set.Ioo 
b a
· 使用定理 `LT.lt.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a →
 ¬IsMin a
· 使用定理 `Set.Ioo_insert_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}
, b < a → insert a (Set.Ioo b a) = Set.Ioc b a
-/
lemma insert_Ioc_pred_right_eq_Ioc (h : a < b) : insert b (Ioc a (pred b)) = Ioc a b := by
  rw [Ioc_pred_right_of_not_isMin h.not_isMin, Ioo_insert_right h]
/-
**Set.insert_Ico_left_eq_Ico_pred_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Ico_left_eq_Ico_pred_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) : i
nsert (pred a) (Ico a b) = Ico (pred a) b
参数：h : a <= b；ha : ¬ IsMin a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Order.pred_lt_of_le_of_not_isMin`：∀ {α : Type u_1} [inst : Preorder α] [
inst_1 : PredOrder α] {a b : α}, a ≤ b → ¬IsMin a → Order.pred a < b
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma insert_Ico_left_eq_Ico_pred_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert (pred a) (Ico a b) = Ico (pred a) b := by
  ext x; simp +contextual [or_and_left, pred_le_iff_eq_or_le, pred_lt_of_le_of_not_isMin h ha]
/-
**Set.insert_Ico_pred_right_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Ico_pred_right_eq_Ico (h : a < b) : insert (pred b) (Ico a (pred b)
) = Ico a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ico_insert_right`：Ico_insert_right (h : a <= b) : insert b (Ico a b)
 = Icc a b
· 使用定理 `Order.le_pred_of_lt`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Pred
Order α] {a b : α}, b < a → b ≤ Order.pred a
· 使用定理 `Order.Icc_pred_right_of_not_isMin`：∀ {α : Type u_1} [inst : Preorder α] 
[inst_1 : PredOrder α] {a b : α}, ¬IsMin a → Set.Icc b (Order.pred a) = Set.Ico 
b a
· 使用定理 `LT.lt.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a →
 ¬IsMin a
-/
lemma insert_Ico_pred_right_eq_Ico (h : a < b) : insert (pred b) (Ico a (pred b)) = Ico a b := by
  rw [Ico_insert_right (le_pred_of_lt h), Icc_pred_right_of_not_isMin h.not_isMin]

/-!
#### Orders with no minimal elements

##### Equalities of intervals
-/

variable [NoMinOrder α]

/-
**Set.Icc_pred_right_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Icc_pred_right_eq_Ico (a b : α) : Icc a (pred b) = Ico a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Icc_pred_right_eq_Ico_of_not_isMin`：Icc_pred_right_eq_Ico_of_not_isM
in (hb : ¬ IsMin b) (a : α) : Icc a (pred b) = Ico a b
· 使用定理 `not_isMin`：not_isMin [NoMinOrder α] (a : α) : ¬IsMin a
-/
lemma Icc_pred_right_eq_Ico (a b : α) : Icc a (pred b) = Ico a b :=
  Icc_pred_right_eq_Ico_of_not_isMin (not_isMin _) _
/-
**Set.Ioc_pred_left_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioc_pred_left_eq_Icc (a b : α) : Ioc (pred a) b = Icc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Ioc_pred_left_eq_Icc_of_not_isMin`：Ioc_pred_left_eq_Icc_of_not_isMin
 (ha : ¬ IsMin a) (b : α) : Ioc (pred a) b = Icc a b
· 使用定理 `not_isMin`：not_isMin [NoMinOrder α] (a : α) : ¬IsMin a
-/
lemma Ioc_pred_left_eq_Icc (a b : α) : Ioc (pred a) b = Icc a b :=
  Ioc_pred_left_eq_Icc_of_not_isMin (not_isMin _) _
/-
**Set.Ioo_pred_left_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioo_pred_left_eq_Ioc (a b : α) : Ioo (pred a) b = Ico a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Ioo_pred_left_eq_Ioc_of_not_isMin`：Ioo_pred_left_eq_Ioc_of_not_isMin
 (ha : ¬ IsMin a) (b : α) : Ioo (pred a) b = Ico a b
· 使用定理 `not_isMin`：not_isMin [NoMinOrder α] (a : α) : ¬IsMin a
-/
lemma Ioo_pred_left_eq_Ioc (a b : α) : Ioo (pred a) b = Ico a b :=
  Ioo_pred_left_eq_Ioc_of_not_isMin (not_isMin _) _
/-
**Set.Ioc_pred_pred_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioc_pred_pred_eq_Ico (a b : α) : Ioc (pred a) (pred b) = Ico a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Ioc_pred_pred_eq_Ico_of_not_isMin`：Ioc_pred_pred_eq_Ico_of_not_isMin
 (ha : ¬ IsMin a) (b : α) : Ioc (pred a) (pred b) = Ico a b
· 使用定理 `not_isMin`：not_isMin [NoMinOrder α] (a : α) : ¬IsMin a
-/
lemma Ioc_pred_pred_eq_Ico (a b : α) : Ioc (pred a) (pred b) = Ico a b :=
  Ioc_pred_pred_eq_Ico_of_not_isMin (not_isMin _) _

/-! ##### Inserting into intervals -/

/-
**Set.insert_Ioc_left_eq_Ioc_pred** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Ioc_left_eq_Ioc_pred (h : a <= b) : insert a (Ioc a b) = Ioc (pred 
a) b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.insert_Ioc_left_eq_Ioc_pred_of_not_isMin`：insert_Ioc_left_eq_Ioc_pre
d_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) : insert a (Ioc a b) = Ioc (pred a)
 b
· 使用定理 `not_isMin`：not_isMin [NoMinOrder α] (a : α) : ¬IsMin a

--- 原说明 ---
##### Inserting into intervals
-/
lemma insert_Ioc_left_eq_Ioc_pred (h : a ≤ b) : insert a (Ioc a b) = Ioc (pred a) b :=
  insert_Ioc_left_eq_Ioc_pred_of_not_isMin h (not_isMin _)
/-
**Set.insert_Ico_left_eq_Ico_pred** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：insert_Ico_left_eq_Ico_pred (h : a <= b) : insert (pred a) (Ico a b) = Ico
 (pred a) b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.insert_Ico_left_eq_Ico_pred_of_not_isMin`：insert_Ico_left_eq_Ico_pre
d_of_not_isMin (h : a <= b) (ha : ¬ IsMin a) : insert (pred a) (Ico a b) = Ico (
pred a) b
· 使用定理 `not_isMin`：not_isMin [NoMinOrder α] (a : α) : ¬IsMin a
-/
lemma insert_Ico_left_eq_Ico_pred (h : a ≤ b) : insert (pred a) (Ico a b) = Ico (pred a) b :=
  insert_Ico_left_eq_Ico_pred_of_not_isMin h (not_isMin _)

end PredOrder

section SuccPredOrder
variable [SuccOrder α] [PredOrder α] [Nontrivial α]

/-
**Set.Icc_succ_pred_eq_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Icc_succ_pred_eq_Ioo (a b : α) : Icc (succ a) (pred b) = Ioo a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_eq_empty`：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
· 使用定理 `Order.not_isMin_succ`：not_isMin_succ [Nontrivial α] (a : α) : ¬ IsMin (s
ucc a)
· 使用定理 `IsMin.mono`：IsMin.mono (ha : IsMin a) (h : b <= a) : IsMin b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.pred_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredOrder 
α] (a : α), Order.pred a ≤ a
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `IsMin.not_lt`：IsMin.not_lt (h : IsMin a) : ¬b < a
· 使用引理 `Set.Icc_pred_right_eq_Ico_of_not_isMin`：Icc_pred_right_eq_Ico_of_not_isM
in (hb : ¬ IsMin b) (a : α) : Icc a (pred b) = Ico a b
· 使用引理 `Set.Ico_succ_left_eq_Ioo`：Ico_succ_left_eq_Ioo (a b : α) : Ico (succ a) 
b = Ioo a b
-/
lemma Icc_succ_pred_eq_Ioo (a b : α) : Icc (succ a) (pred b) = Ioo a b := by
  by_cases hb : IsMin b
  · rw [Icc_eq_empty, Ioo_eq_empty hb.not_lt]
    exact fun h ↦ not_isMin_succ _ <| hb.mono <| h.trans <| pred_le _
  · rw [Icc_pred_right_eq_Ico_of_not_isMin hb, Ico_succ_left_eq_Ioo]

end SuccPredOrder

/-! ### One-sided interval towards `⊥` -/

section SuccOrder
variable [SuccOrder α] {b : α}

/-
**Set.Iio_succ_eq_Iic_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Iio_succ_eq_Iic_of_not_isMax (hb : ¬ IsMax b) : Iio (succ b) = Iic b
参数：hb : ¬ IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `Set.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic
 b ↔ x ≤ b
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Iio_succ_eq_Iic_of_not_isMax (hb : ¬ IsMax b) : Iio (succ b) = Iic b := by
  ext x; rw [mem_Iio, mem_Iic, lt_succ_iff_of_not_isMax hb]

variable [NoMaxOrder α]
/-
**Set.Iio_succ_eq_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Iio_succ_eq_Iic (b : α) : Iio (succ b) = Iic b
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Iio_succ_eq_Iic_of_not_isMax`：Iio_succ_eq_Iic_of_not_isMax (hb : ¬ I
sMax b) : Iio (succ b) = Iic b
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
lemma Iio_succ_eq_Iic (b : α) : Iio (succ b) = Iic b := Iio_succ_eq_Iic_of_not_isMax (not_isMax _)

end SuccOrder

section PredOrder
variable [PredOrder α] {a b : α}

/-
**Set.Iic_pred_eq_Iio_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Iic_pred_eq_Iio_of_not_isMin (hb : ¬ IsMin b) : Iic (pred b) = Iio b
参数：hb : ¬ IsMin b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic
 b ↔ x ≤ b
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `Order.le_pred_iff_of_not_isMin`：∀ {α : Type u_1} [inst : Preorder α] [in
st_1 : PredOrder α] {a b : α}, ¬IsMin a → (b ≤ Order.pred a ↔ b < a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Iic_pred_eq_Iio_of_not_isMin (hb : ¬ IsMin b) : Iic (pred b) = Iio b := by
  ext x; rw [mem_Iic, mem_Iio, le_pred_iff_of_not_isMin hb]

variable [NoMinOrder α]
/-
**Set.Iic_pred_eq_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Iic_pred_eq_Iio (b : α) : Iic (pred b) = Iio b
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Iic_pred_eq_Iio_of_not_isMin`：Iic_pred_eq_Iio_of_not_isMin (hb : ¬ I
sMin b) : Iic (pred b) = Iio b
· 使用定理 `not_isMin`：not_isMin [NoMinOrder α] (a : α) : ¬IsMin a
-/
lemma Iic_pred_eq_Iio (b : α) : Iic (pred b) = Iio b := Iic_pred_eq_Iio_of_not_isMin (not_isMin _)

end PredOrder

/-! ### One-sided interval towards `⊤` -/

section SuccOrder
variable [SuccOrder α] {a : α}

/-
**Set.Ici_succ_eq_Ioi_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ici_succ_eq_Ioi_of_not_isMax (ha : ¬ IsMax a) : Ici (succ a) = Ioi a
参数：ha : ¬ IsMax a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ici
 b ↔ b ≤ x
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `Order.succ_le_iff_of_not_isMax`：succ_le_iff_of_not_isMax (ha : ¬IsMax a)
 : succ a <= b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Ici_succ_eq_Ioi_of_not_isMax (ha : ¬ IsMax a) : Ici (succ a) = Ioi a := by
  ext x; rw [mem_Ici, mem_Ioi, succ_le_iff_of_not_isMax ha]

variable [NoMaxOrder α]
/-
**Set.Ici_succ_eq_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ici_succ_eq_Ioi (a : α) : Ici (succ a) = Ioi a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Ici_succ_eq_Ioi_of_not_isMax`：Ici_succ_eq_Ioi_of_not_isMax (ha : ¬ I
sMax a) : Ici (succ a) = Ioi a
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
lemma Ici_succ_eq_Ioi (a : α) : Ici (succ a) = Ioi a := Ici_succ_eq_Ioi_of_not_isMax (not_isMax _)

end SuccOrder

section PredOrder
variable [PredOrder α] {a a : α}

/-
**Set.Ioi_pred_eq_Ici_of_not_isMin** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioi_pred_eq_Ici_of_not_isMin (ha : ¬ IsMin a) : Ioi (pred a) = Ici a
参数：ha : ¬ IsMin a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `Set.mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ici
 b ↔ b ≤ x
· 使用定理 `Order.pred_lt_iff_of_not_isMin`：∀ {α : Type u_1} [inst : LinearOrder α] 
[inst_1 : PredOrder α] {a b : α}, ¬IsMin a → (Order.pred a < b ↔ a ≤ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Ioi_pred_eq_Ici_of_not_isMin (ha : ¬ IsMin a) : Ioi (pred a) = Ici a := by
  ext x; rw [mem_Ioi, mem_Ici, pred_lt_iff_of_not_isMin ha]

variable [NoMinOrder α]
/-
**Set.Ioi_pred_eq_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioi_pred_eq_Ici (a : α) : Ioi (pred a) = Ici a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Ioi_pred_eq_Ici_of_not_isMin`：Ioi_pred_eq_Ici_of_not_isMin (ha : ¬ I
sMin a) : Ioi (pred a) = Ici a
· 使用定理 `not_isMin`：not_isMin [NoMinOrder α] (a : α) : ¬IsMin a
-/
lemma Ioi_pred_eq_Ici (a : α) : Ioi (pred a) = Ici a := Ioi_pred_eq_Ici_of_not_isMin (not_isMin _)

end PredOrder
end Set

