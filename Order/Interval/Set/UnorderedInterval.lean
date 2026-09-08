/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
module

public import Mathlib.Data.Set.Order
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Interval.Set.Image
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Tactic.Common
public import Mathlib.Order.MinMax

/-!
# Intervals without endpoints ordering

In any lattice `α`, we define `uIcc a b` to be `Icc (a ⊓ b) (a ⊔ b)`, which in a linear order is
the set of elements lying between `a` and `b`.

`Icc a b` requires the assumption `a ≤ b` to be meaningful, which is sometimes inconvenient. The
interval as defined in this file is always the set of things lying between `a` and `b`, regardless
of the relative order of `a` and `b`.

For real numbers, `uIcc a b` is the same as `segment ℝ a b`.

In a product or pi type, `uIcc a b` is the smallest box containing `a` and `b`. For example,
`uIcc (1, -1) (-1, 1) = Icc (-1, -1) (1, 1)` is the square of vertices `(1, -1)`, `(-1, -1)`,
`(-1, 1)`, `(1, 1)`.

In `Finset α` (seen as a hypercube of dimension `Fintype.card α`), `uIcc a b` is the smallest
subcube containing both `a` and `b`.

## Notation

We use the localized notation `[[a, b]]` for `uIcc a b`. One can open the scope `Interval` to
make the notation available.

-/

@[expose] public section


open Function

open OrderDual (toDual ofDual)

variable {α β : Type*}

namespace Set

section Lattice

variable [Lattice α] [Lattice β] {a a₁ a₂ b b₁ b₂ x : α}

/-- `uIcc a b` is the set of elements lying between `a` and `b`, with `a` and `b` included.
Note that we define it more generally in a lattice as `Set.Icc (a ⊓ b) (a ⊔ b)`. In a product type,
`uIcc` corresponds to the bounding box of the two elements. -/
/-
**Set.uIcc** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：uIcc (a b : α) : Set α
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`uIcc a b` is the set of elements lying between `a` and `b`, with `a` and `b` in
cluded.
Note that we define it more generally in a lattice as `Set.Icc (a ⊓ b) (a ⊔ b)`.
 In a product type,
`uIcc` corresponds to the bounding box of the two elements.
-/
def uIcc (a b : α) : Set α := Icc (a ⊓ b) (a ⊔ b)

/-- `[[a, b]]` denotes the set of elements lying between `a` and `b`, inclusive. -/
scoped[Interval] notation "[[" a ", " b "]]" => Set.uIcc a b

open Interval

@[simp]
/-
**Set.uIcc_toDual** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_toDual (a b : α) : [[toDual a, toDual b]] = ofDual ⁻¹' [[a, b]]
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_toDual`：Icc_toDual : Icc (toDual a) (toDual b) = ofDual ⁻¹' Icc 
b a
-/
lemma uIcc_toDual (a b : α) : [[toDual a, toDual b]] = ofDual ⁻¹' [[a, b]] :=
  -- Note: needed to hint `(α := α)` after https://github.com/leanprover-community/mathlib4/pull/8386 (elaboration order?)
  Icc_toDual (α := α)

@[simp]
/-
**Set.uIcc_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：uIcc_ofDual (a b : αᵒᵈ) : [[ofDual a, ofDual b]] = toDual ⁻¹' [[a, b]]
参数：a b : αᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_ofDual`：Icc_ofDual {x y : αᵒᵈ} : Icc (ofDual y) (ofDual x) = toD
ual ⁻¹' Icc x y
-/
theorem uIcc_ofDual (a b : αᵒᵈ) : [[ofDual a, ofDual b]] = toDual ⁻¹' [[a, b]] :=
  Icc_ofDual

@[simp]
/-
**Set.uIcc_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIcc.eq_1`：∀ {α : Type u_1} [inst : Lattice α] (a b : α), Set.uIcc a
 b = Set.Icc (a ⊓ b) (a ⊔ b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
-/
lemma uIcc_of_le (h : a ≤ b) : [[a, b]] = Icc a b := by rw [uIcc, inf_eq_left.2 h, sup_eq_right.2 h]

@[simp]
/-
**Set.uIcc_of_ge** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIcc.eq_1`：∀ {α : Type u_1} [inst : Lattice α] (a b : α), Set.uIcc a
 b = Set.Icc (a ⊓ b) (a ⊔ b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
-/
lemma uIcc_of_ge (h : b ≤ a) : [[a, b]] = Icc b a := by rw [uIcc, inf_eq_right.2 h, sup_eq_left.2 h]
/-
**Set.uIcc_comm** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_comm (a b : α) : [[a, b]] = [[b, a]]
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uIcc_comm (a b : α) : [[a, b]] = [[b, a]] := by simp_rw [uIcc, inf_comm, sup_comm]
/-
**Set.uIcc_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_of_lt (h : a < b) : [[a, b]] = Icc a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma uIcc_of_lt (h : a < b) : [[a, b]] = Icc a b := uIcc_of_le h.le
/-
**Set.uIcc_of_gt** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_of_gt (h : b < a) : [[a, b]] = Icc b a
参数：h : b < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.uIcc_of_ge`：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma uIcc_of_gt (h : b < a) : [[a, b]] = Icc b a := uIcc_of_ge h.le
/-
**Set.uIcc_self** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_self : [[a, a]] = {a}
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
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uIcc_self : [[a, a]] = {a} := by simp [uIcc]
/-
**Set.nonempty_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, (Set.uIcc a b).Nonempty
参数：Set.uIcc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
· 使用定理 `inf_le_sup`：inf_le_sup : a ⊓ b <= a ⊔ b
-/
@[simp] lemma nonempty_uIcc : [[a, b]].Nonempty := nonempty_Icc.2 inf_le_sup
/-
**Set.Icc_subset_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Icc_subset_uIcc : Icc a b subseteq [[a, b]]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc
 a₁ b₁ subseteq Icc a₂ b₂
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma Icc_subset_uIcc : Icc a b ⊆ [[a, b]] := Icc_subset_Icc inf_le_left le_sup_right
/-
**Set.Icc_subset_uIcc'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Icc_subset_uIcc' : Icc b a subseteq [[a, b]]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc
 a₁ b₁ subseteq Icc a₂ b₂
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
lemma Icc_subset_uIcc' : Icc b a ⊆ [[a, b]] := Icc_subset_Icc inf_le_right le_sup_left
/-
**Set.left_mem_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, a ∈ Set.uIcc a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
@[simp] lemma left_mem_uIcc : a ∈ [[a, b]] := ⟨inf_le_left, le_sup_left⟩
/-
**Set.right_mem_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, b ∈ Set.uIcc a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
@[simp] lemma right_mem_uIcc : b ∈ [[a, b]] := ⟨inf_le_right, le_sup_right⟩
/-
**Set.mem_uIcc_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_uIcc_of_le (ha : a <= x) (hb : x <= b) : x in [[a, b]]
参数：ha : a <= x；hb : x <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Icc_subset_uIcc`：Icc_subset_uIcc : Icc a b subseteq [[a, b]]
-/
lemma mem_uIcc_of_le (ha : a ≤ x) (hb : x ≤ b) : x ∈ [[a, b]] := Icc_subset_uIcc ⟨ha, hb⟩
/-
**Set.mem_uIcc_of_ge** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_uIcc_of_ge (hb : b <= x) (ha : x <= a) : x in [[a, b]]
参数：hb : b <= x；ha : x <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Icc_subset_uIcc'`：Icc_subset_uIcc' : Icc b a subseteq [[a, b]]
-/
lemma mem_uIcc_of_ge (hb : b ≤ x) (ha : x ≤ a) : x ∈ [[a, b]] := Icc_subset_uIcc' ⟨hb, ha⟩
/-
**Set.uIcc_subset_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_subset_uIcc (h₁ : a₁ in [[a₂, b₂]]) (h₂ : b₁ in [[a₂, b₂]]) : [[a₁, b
₁]] subseteq [[a₂, b₂]]
参数：h₁ : a₁ in [[a₂, b₂]]；h₂ : b₁ in [[a₂, b₂]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc
 a₁ b₁ subseteq Icc a₂ b₂
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma uIcc_subset_uIcc (h₁ : a₁ ∈ [[a₂, b₂]]) (h₂ : b₁ ∈ [[a₂, b₂]]) :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] :=
  Icc_subset_Icc (le_inf h₁.1 h₂.1) (sup_le h₁.2 h₂.2)
/-
**Set.uIcc_subset_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_subset_Icc (ha : a₁ in Icc a₂ b₂) (hb : b₁ in Icc a₂ b₂) : [[a₁, b₁]]
 subseteq Icc a₂ b₂
参数：ha : a₁ in Icc a₂ b₂；hb : b₁ in Icc a₂ b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc
 a₁ b₁ subseteq Icc a₂ b₂
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma uIcc_subset_Icc (ha : a₁ ∈ Icc a₂ b₂) (hb : b₁ ∈ Icc a₂ b₂) :
    [[a₁, b₁]] ⊆ Icc a₂ b₂ :=
  Icc_subset_Icc (le_inf ha.1 hb.1) (sup_le ha.2 hb.2)
/-
**Set.uIcc_subset_uIcc_iff_mem** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_subset_uIcc_iff_mem : [[a₁, b₁]] subseteq [[a₂, b₂]] ↔ a₁ in [[a₂, b₂
]] ∧ b₁ in [[a₂, b₂]]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.left_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, a ∈ Se
t.uIcc a b
· 使用定理 `Set.right_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, b ∈ S
et.uIcc a b
· 使用引理 `Set.uIcc_subset_uIcc`：uIcc_subset_uIcc (h₁ : a₁ in [[a₂, b₂]]) (h₂ : b₁ 
in [[a₂, b₂]]) : [[a₁, b₁]] subseteq [[a₂, b₂]]
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma uIcc_subset_uIcc_iff_mem :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] ↔ a₁ ∈ [[a₂, b₂]] ∧ b₁ ∈ [[a₂, b₂]] :=
  Iff.intro (fun h => ⟨h left_mem_uIcc, h right_mem_uIcc⟩) fun h =>
    uIcc_subset_uIcc h.1 h.2
/-
**Set.uIcc_subset_uIcc_iff_le'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_subset_uIcc_iff_le' : [[a₁, b₁]] subseteq [[a₂, b₂]] ↔ a₂ ⊓ b₂ <= a₁ 
⊓ b₁ ∧ a₁ ⊔ b₁ <= a₂ ⊔ b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_subset_Icc_iff`：Icc_subset_Icc_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ s
ubseteq Icc a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
· 使用定理 `inf_le_sup`：inf_le_sup : a ⊓ b <= a ⊔ b
-/
lemma uIcc_subset_uIcc_iff_le' :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] ↔ a₂ ⊓ b₂ ≤ a₁ ⊓ b₁ ∧ a₁ ⊔ b₁ ≤ a₂ ⊔ b₂ :=
  Icc_subset_Icc_iff inf_le_sup
/-
**Set.uIcc_subset_uIcc_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_subset_uIcc_right (h : x in [[a, b]]) : [[x, b]] subseteq [[a, b]]
参数：h : x in [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.uIcc_subset_uIcc`：uIcc_subset_uIcc (h₁ : a₁ in [[a₂, b₂]]) (h₂ : b₁ 
in [[a₂, b₂]]) : [[a₁, b₁]] subseteq [[a₂, b₂]]
· 使用定理 `Set.right_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, b ∈ S
et.uIcc a b
-/
lemma uIcc_subset_uIcc_right (h : x ∈ [[a, b]]) : [[x, b]] ⊆ [[a, b]] :=
  uIcc_subset_uIcc h right_mem_uIcc
/-
**Set.uIcc_subset_uIcc_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_subset_uIcc_left (h : x in [[a, b]]) : [[a, x]] subseteq [[a, b]]
参数：h : x in [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.uIcc_subset_uIcc`：uIcc_subset_uIcc (h₁ : a₁ in [[a₂, b₂]]) (h₂ : b₁ 
in [[a₂, b₂]]) : [[a₁, b₁]] subseteq [[a₂, b₂]]
· 使用定理 `Set.left_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, a ∈ Se
t.uIcc a b
-/
lemma uIcc_subset_uIcc_left (h : x ∈ [[a, b]]) : [[a, x]] ⊆ [[a, b]] :=
  uIcc_subset_uIcc left_mem_uIcc h
/-
**Set.bdd_below_bdd_above_iff_subset_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：bdd_below_bdd_above_iff_subset_uIcc (s : Set α) : BddBelow s ∧ BddAbove s 
↔ exists a b, s subseteq [[a, b]]
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `bddBelow_bddAbove_iff_subset_Icc`：bddBelow_bddAbove_iff_subset_Icc : Bdd
Below s ∧ BddAbove s ↔ exists a b, s subseteq Icc a b
· 使用引理 `Set.Icc_subset_uIcc`：Icc_subset_uIcc : Icc a b subseteq [[a, b]]
-/
lemma bdd_below_bdd_above_iff_subset_uIcc (s : Set α) :
    BddBelow s ∧ BddAbove s ↔ ∃ a b, s ⊆ [[a, b]] :=
  bddBelow_bddAbove_iff_subset_Icc.trans
    ⟨fun ⟨a, b, h⟩ => ⟨a, b, fun _ hx => Icc_subset_uIcc (h hx)⟩, fun ⟨_, _, h⟩ => ⟨_, _, h⟩⟩

section Prod

@[simp]
/-
**Set.uIcc_prod_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：uIcc_prod_uIcc (a₁ a₂ : α) (b₁ b₂ : β) : [[a₁, a₂]] ×ˢ [[b₁, b₂]] = [[(a₁,
 b₁), (a₂, b₂)]]
参数：a₁ a₂ : α；b₁ b₂ : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_prod_Icc`：Icc_prod_Icc (a₁ a₂ : α) (b₁ b₂ : β) : Icc a₁ a₂ ×ˢ Ic
c b₁ b₂ = Icc (a₁, b₁) (a₂, b₂)
-/
theorem uIcc_prod_uIcc (a₁ a₂ : α) (b₁ b₂ : β) :
    [[a₁, a₂]] ×ˢ [[b₁, b₂]] = [[(a₁, b₁), (a₂, b₂)]] :=
  Icc_prod_Icc _ _ _ _
/-
**Set.uIcc_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：uIcc_prod_eq (a b : α × β) : [[a, b]] = [[a.1, b.1]] ×ˢ [[a.2, b.2]]
参数：a b : α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIcc_prod_uIcc`：uIcc_prod_uIcc (a₁ a₂ : α) (b₁ b₂ : β) : [[a₁, a₂]] 
×ˢ [[b₁, b₂]] = [[(a₁, b₁), (a₂, b₂)]]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uIcc_prod_eq (a b : α × β) : [[a, b]] = [[a.1, b.1]] ×ˢ [[a.2, b.2]] := by simp

end Prod

end Lattice

open Interval

section DistribLattice

variable [DistribLattice α] {a b c : α}

/-
**Set.eq_of_mem_uIcc_of_mem_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：eq_of_mem_uIcc_of_mem_uIcc (ha : a in [[b, c]]) (hb : b in [[a, c]]) : a =
 b
参数：ha : a in [[b, c]]；hb : b in [[a, c]]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_inf_eq_sup_eq`：eq_of_inf_eq_sup_eq {a b c : α} (h₁ : b ⊓ a = c ⊓ a
) (h₂ : b ⊔ a = c ⊔ a) : b = c
· 使用定理 `inf_congr_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α}, b
 ⊓ c ≤ a → a ⊓ c ≤ b → a ⊓ c = b ⊓ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sup_congr_right`：sup_congr_right (ha : a <= b ⊔ c) (hb : b <= a ⊔ c) : a
 ⊔ c = b ⊔ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma eq_of_mem_uIcc_of_mem_uIcc (ha : a ∈ [[b, c]]) (hb : b ∈ [[a, c]]) : a = b :=
  eq_of_inf_eq_sup_eq (inf_congr_right ha.1 hb.1) <| sup_congr_right ha.2 hb.2
/-
**Set.eq_of_mem_uIcc_of_mem_uIcc'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：eq_of_mem_uIcc_of_mem_uIcc' : b in [[a, c]] -> c in [[a, b]] -> b = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_comm`：uIcc_comm (a b : α) : [[a, b]] = [[b, a]]
· 使用引理 `Set.eq_of_mem_uIcc_of_mem_uIcc`：eq_of_mem_uIcc_of_mem_uIcc (ha : a in [[
b, c]]) (hb : b in [[a, c]]) : a = b
-/
lemma eq_of_mem_uIcc_of_mem_uIcc' : b ∈ [[a, c]] → c ∈ [[a, b]] → b = c := by
  simpa only [uIcc_comm a] using eq_of_mem_uIcc_of_mem_uIcc
/-
**Set.uIcc_injective_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_injective_right (a : α) : Injective fun b => uIcc b a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.eq_of_mem_uIcc_of_mem_uIcc`：eq_of_mem_uIcc_of_mem_uIcc (ha : a in [[
b, c]]) (hb : b in [[a, c]]) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Set.left_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, a ∈ Se
t.uIcc a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma uIcc_injective_right (a : α) : Injective fun b => uIcc b a := fun b c h => by
  rw [Set.ext_iff] at h
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc)
/-
**Set.uIcc_injective_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_injective_left (a : α) : Injective (uIcc a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.uIcc_comm`：uIcc_comm (a b : α) : [[a, b]] = [[b, a]]
· 使用引理 `Set.uIcc_injective_right`：uIcc_injective_right (a : α) : Injective fun b
 => uIcc b a
-/
lemma uIcc_injective_left (a : α) : Injective (uIcc a) := by
  simpa only [uIcc_comm] using uIcc_injective_right a

end DistribLattice

section LinearOrder
variable [LinearOrder α]

section Lattice
variable [Lattice β] {f : α → β} {a b : α}

/-
**Set._root_.MonotoneOn.mapsTo_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MonotoneOn.mapsTo_uIcc (hf : MonotoneOn f (uIcc a b)) :
    MapsTo f (uIcc a b) (uIcc (f a) (f b)) := by
  rw [uIcc, uIcc, ← hf.map_sup, ← hf.map_inf] <;>
    apply_rules [left_mem_uIcc, right_mem_uIcc, hf.mapsTo_Icc]
/-
**Set._root_.AntitoneOn.mapsTo_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AntitoneOn.mapsTo_uIcc (hf : AntitoneOn f (uIcc a b)) :
    MapsTo f (uIcc a b) (uIcc (f a) (f b)) := by
  rw [uIcc, uIcc, ← hf.map_sup, ← hf.map_inf] <;>
    apply_rules [left_mem_uIcc, right_mem_uIcc, hf.mapsTo_Icc]
/-
**Set._root_.Monotone.mapsTo_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.mapsTo_uIcc (hf : Monotone f) : MapsTo f (uIcc a b) (uIcc (f a) (f b)) :=
  (hf.monotoneOn _).mapsTo_uIcc
/-
**Set._root_.Antitone.mapsTo_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Antitone.mapsTo_uIcc (hf : Antitone f) : MapsTo f (uIcc a b) (uIcc (f a) (f b)) :=
  (hf.antitoneOn _).mapsTo_uIcc
/-
**Set._root_.MonotoneOn.image_uIcc_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MonotoneOn.image_uIcc_subset (hf : MonotoneOn f (uIcc a b)) :
    f '' uIcc a b ⊆ uIcc (f a) (f b) := hf.mapsTo_uIcc.image_subset
/-
**Set._root_.AntitoneOn.image_uIcc_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AntitoneOn.image_uIcc_subset (hf : AntitoneOn f (uIcc a b)) :
    f '' uIcc a b ⊆ uIcc (f a) (f b) := hf.mapsTo_uIcc.image_subset
/-
**Set._root_.Monotone.image_uIcc_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.image_uIcc_subset (hf : Monotone f) : f '' uIcc a b ⊆ uIcc (f a) (f b) :=
  (hf.monotoneOn _).image_uIcc_subset
/-
**Set._root_.Antitone.image_uIcc_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Antitone.image_uIcc_subset (hf : Antitone f) : f '' uIcc a b ⊆ uIcc (f a) (f b) :=
  (hf.antitoneOn _).image_uIcc_subset

end Lattice

variable [LinearOrder β] {f : α → β} {s : Set α} {a a₁ a₂ b b₁ b₂ c : α}

/-
**Set.Icc_min_max** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_min_max : Icc (min a b) (max a b) = [[a, b]]
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_min_max : Icc (min a b) (max a b) = [[a, b]] :=
  rfl
/-
**Set.uIcc_of_not_le** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_of_not_le (h : ¬a <= b) : [[a, b]] = Icc b a
参数：h : ¬a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.uIcc_of_gt`：uIcc_of_gt (h : b < a) : [[a, b]] = Icc b a
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
-/
lemma uIcc_of_not_le (h : ¬a ≤ b) : [[a, b]] = Icc b a := uIcc_of_gt <| lt_of_not_ge h
/-
**Set.uIcc_of_not_ge** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_of_not_ge (h : ¬b <= a) : [[a, b]] = Icc a b
参数：h : ¬b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.uIcc_of_lt`：uIcc_of_lt (h : a < b) : [[a, b]] = Icc a b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
-/
lemma uIcc_of_not_ge (h : ¬b ≤ a) : [[a, b]] = Icc a b := uIcc_of_lt <| lt_of_not_ge h
/-
**Set.uIcc_eq_union** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_eq_union : [[a, b]] = Icc a b union Icc b a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_union_Icc'`：Icc_union_Icc' (h₁ : c <= b) (h₂ : a <= d) : Icc a b
 union Icc c d = Icc (min a c) (max b d)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
-/
lemma uIcc_eq_union : [[a, b]] = Icc a b ∪ Icc b a := by rw [Icc_union_Icc', max_comm] <;> rfl
/-
**Set.mem_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_uIcc : a in [[b, c]] ↔ b <= a ∧ a <= c ∨ c <= a ∧ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_eq_union`：uIcc_eq_union : [[a, b]] = Icc a b union Icc b a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_uIcc : a ∈ [[b, c]] ↔ b ≤ a ∧ a ≤ c ∨ c ≤ a ∧ a ≤ b := by simp [uIcc_eq_union]
/-
**Set.notMem_uIcc_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：notMem_uIcc_of_lt (ha : c < a) (hb : c < b) : c ∉ [[a, b]]
参数：ha : c < a；hb : c < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.notMem_Icc_of_lt`：notMem_Icc_of_lt (ha : c < a) : c ∉ Icc a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_min_iff`：lt_min_iff : a < min b c ↔ a < b ∧ a < c
-/
lemma notMem_uIcc_of_lt (ha : c < a) (hb : c < b) : c ∉ [[a, b]] :=
  notMem_Icc_of_lt <| lt_min_iff.mpr ⟨ha, hb⟩
/-
**Set.notMem_uIcc_of_gt** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：notMem_uIcc_of_gt (ha : a < c) (hb : b < c) : c ∉ [[a, b]]
参数：ha : a < c；hb : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.notMem_Icc_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, 
a < c → c ∉ Set.Icc b a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
-/
lemma notMem_uIcc_of_gt (ha : a < c) (hb : b < c) : c ∉ [[a, b]] :=
  notMem_Icc_of_gt <| max_lt_iff.mpr ⟨ha, hb⟩
/-
**Set.uIcc_subset_uIcc_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_subset_uIcc_iff_le : [[a₁, b₁]] subseteq [[a₂, b₂]] ↔ min a₂ b₂ <= mi
n a₁ b₁ ∧ max a₁ b₁ <= max a₂ b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.uIcc_subset_uIcc_iff_le'`：uIcc_subset_uIcc_iff_le' : [[a₁, b₁]] subs
eteq [[a₂, b₂]] ↔ a₂ ⊓ b₂ <= a₁ ⊓ b₁ ∧ a₁ ⊔ b₁ <= a₂ ⊔ b₂
-/
lemma uIcc_subset_uIcc_iff_le :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] ↔ min a₂ b₂ ≤ min a₁ b₁ ∧ max a₁ b₁ ≤ max a₂ b₂ :=
  uIcc_subset_uIcc_iff_le'

/-- A sort of triangle inequality. -/
/-
**Set.uIcc_subset_uIcc_union_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIcc_subset_uIcc_union_uIcc : [[a, c]] subseteq [[a, b]] union [[b, c]]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b

--- 原说明 ---
A sort of triangle inequality.
-/
lemma uIcc_subset_uIcc_union_uIcc : [[a, c]] ⊆ [[a, b]] ∪ [[b, c]] := fun x => by
  simp only [mem_uIcc, mem_union]
  rcases le_total x b with h2 | h2 <;> tauto
/-
**Set.monotone_or_antitone_iff_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：monotone_or_antitone_iff_uIcc : Monotone f ∨ Antitone f ↔ forall a b c, c 
in [[a, b]] -> f c in [[f a, f b]]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Antitone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Antitone f → f (min a b) = max (f
 a) (f…
· 使用定理 `Antitone.map_max`：Antitone.map_max (hf : Antitone f) : f (max a b) = min
 (f a) (f b)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `not_monotone_not_antitone_iff_exists_le_le`：not_monotone_not_antitone_if
f_exists_le_le : ¬ Monotone f ∧ ¬ Antitone f ↔ exists a b c, a <= b ∧ b <= c ∧ (
(f a < f b ∧ f c < f b) ∨ (f b <…
· 使用引理 `Set.Icc_subset_uIcc`：Icc_subset_uIcc : Icc a b subseteq [[a, b]]
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
-/
lemma monotone_or_antitone_iff_uIcc :
    Monotone f ∨ Antitone f ↔ ∀ a b c, c ∈ [[a, b]] → f c ∈ [[f a, f b]] := by
  constructor
  · rintro (hf | hf) a b c <;> simp_rw [← Icc_min_max, ← hf.map_min, ← hf.map_max]
    exacts [fun hc => ⟨hf hc.1, hf hc.2⟩, fun hc => ⟨hf hc.2, hf hc.1⟩]
  contrapose!
  rw [not_monotone_not_antitone_iff_exists_le_le]
  rintro ⟨a, b, c, hab, hbc, ⟨hfab, hfcb⟩ | ⟨hfba, hfbc⟩⟩
  · exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, fun h => h.2.not_gt <| max_lt hfab hfcb⟩
  · exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, fun h => h.1.not_gt <| lt_min hfba hfbc⟩
/-
**Set.monotoneOn_or_antitoneOn_iff_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：monotoneOn_or_antitoneOn_iff_uIcc : MonotoneOn f s ∨ AntitoneOn f s ↔ fora
llᵉ (a in s) (b in s) (c in s), c in [[a, b]] -> f c in [[f a, f b]]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monotoneOn_or_antitoneOn_iff_uIcc :
    MonotoneOn f s ∨ AntitoneOn f s ↔
      ∀ᵉ (a ∈ s) (b ∈ s) (c ∈ s), c ∈ [[a, b]] → f c ∈ [[f a, f b]] := by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, monotone_or_antitone_iff_uIcc,
    mem_uIcc]

/-- The open-closed uIcc with unordered bounds. -/
/-
**Set.uIoc** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：uIoc : α -> α -> Set α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The open-closed uIcc with unordered bounds.
-/
def uIoc : α → α → Set α := fun a b => Ioc (min a b) (max a b)

-- Below is a capital iota
/-- `Ι a b` denotes the open-closed interval with unordered bounds. Here, `Ι` is a capital iota,
distinguished from a capital `i`. -/
scoped[Interval] notation "Ι" => Set.uIoc

open scoped Interval

/-
**Set.uIoc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b → Set.uIoc a b = 
Set.Ioc a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, grind =] lemma uIoc_of_le (h : a ≤ b) : Ι a b = Ioc a b := by simp [uIoc, h]
/-
**Set.uIoc_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → Set.uIoc a b = 
Set.Ioc b a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, grind =] lemma uIoc_of_ge (h : b ≤ a) : Ι a b = Ioc b a := by simp [uIoc, h]
/-
**Set.uIoc_eq_union** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoc_eq_union : Ι a b = Ioc a b union Ioc b a
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
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
-/
lemma uIoc_eq_union : Ι a b = Ioc a b ∪ Ioc b a := by
  cases le_total a b <;> simp [uIoc, *]
/-
**Set.mem_uIoc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_uIoc : a in Ι b c ↔ b < a ∧ a <= c ∨ c < a ∧ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIoc_eq_union`：uIoc_eq_union : Ι a b = Ioc a b union Ioc b a
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `Set.mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oc a b ↔ a < x ∧ x ≤ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_uIoc : a ∈ Ι b c ↔ b < a ∧ a ≤ c ∨ c < a ∧ a ≤ b := by
  rw [uIoc_eq_union, mem_union, mem_Ioc, mem_Ioc]
/-
**Set.notMem_uIoc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：notMem_uIoc : a ∉ Ι b c ↔ a <= b ∧ a <= c ∨ c < a ∧ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.uIoc_eq_union`：uIoc_eq_union : Ι a b = Ioc a b union Ioc b a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
-/
lemma notMem_uIoc : a ∉ Ι b c ↔ a ≤ b ∧ a ≤ c ∨ c < a ∧ b < a := by
  simp only [uIoc_eq_union, mem_union, mem_Ioc, ← not_le]
  tauto
/-
**Set.left_mem_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ∈ Set.uIoc a b ↔ b < 
a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma left_mem_uIoc : a ∈ Ι a b ↔ b < a := by simp [mem_uIoc]
/-
**Set.right_mem_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ∈ Set.uIoc a b ↔ a < 
b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma right_mem_uIoc : b ∈ Ι a b ↔ a < b := by simp [mem_uIoc]
/-
**Set.forall_uIoc_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：forall_uIoc_iff {P : α -> Prop} : (forall x in Ι a b, P x) ↔ (forall x in 
Ioc a b, P x) ∧ forall x in Ioc b a, P x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Set.uIoc_eq_union`：uIoc_eq_union : Ι a b = Ioc a b union Ioc b a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma forall_uIoc_iff {P : α → Prop} :
    (∀ x ∈ Ι a b, P x) ↔ (∀ x ∈ Ioc a b, P x) ∧ ∀ x ∈ Ioc b a, P x := by
  simp only [uIoc_eq_union, mem_union, or_imp, forall_and]
/-
**Set.uIoc_subset_uIoc_of_uIcc_subset_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoc_subset_uIoc_of_uIcc_subset_uIcc {a b c d : α} (h : [[a, b]] subseteq 
[[c, d]]) : Ι a b subseteq Ι c d
参数：h : [[a, b]] subseteq [[c, d]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioc_subset_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b₁ b₂ : 
α}, b₂ ≤ b₁ → a₁ ≤ a₂ → Set.Ioc b₁ a₁ ⊆ Set.Ioc b₂ a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.uIcc_subset_uIcc_iff_le`：uIcc_subset_uIcc_iff_le : [[a₁, b₁]] subset
eq [[a₂, b₂]] ↔ min a₂ b₂ <= min a₁ b₁ ∧ max a₁ b₁ <= max a₂ b₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma uIoc_subset_uIoc_of_uIcc_subset_uIcc {a b c d : α}
    (h : [[a, b]] ⊆ [[c, d]]) : Ι a b ⊆ Ι c d :=
  Ioc_subset_Ioc (uIcc_subset_uIcc_iff_le.1 h).1 (uIcc_subset_uIcc_iff_le.1 h).2
/-
**Set.uIoc_comm** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoc_comm (a b : α) : Ι a b = Ι b a
参数：a b : α。
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
· 使用引理 `min_comm`：min_comm (a b : α) : min a b = min b a
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uIoc_comm (a b : α) : Ι a b = Ι b a := by simp only [uIoc, min_comm a b, max_comm a b]
/-
**Set.Ioc_subset_uIoc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioc_subset_uIoc : Ioc a b subseteq Ι a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioc_subset_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b₁ b₂ : 
α}, b₂ ≤ b₁ → a₁ ≤ a₂ → Set.Ioc b₁ a₁ ⊆ Set.Ioc b₂ a₂
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
lemma Ioc_subset_uIoc : Ioc a b ⊆ Ι a b := Ioc_subset_Ioc (min_le_left _ _) (le_max_right _ _)
/-
**Set.Ioc_subset_uIoc'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioc_subset_uIoc' : Ioc a b subseteq Ι b a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioc_subset_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b₁ b₂ : 
α}, b₂ ≤ b₁ → a₁ ≤ a₂ → Set.Ioc b₁ a₁ ⊆ Set.Ioc b₂ a₂
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
lemma Ioc_subset_uIoc' : Ioc a b ⊆ Ι b a := Ioc_subset_Ioc (min_le_right _ _) (le_max_left _ _)
/-
**Set.uIoc_subset_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoc_subset_uIcc : Ι a b subseteq uIcc a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
lemma uIoc_subset_uIcc : Ι a b ⊆ uIcc a b := Ioc_subset_Icc_self
/-
**Set.eq_of_mem_uIoc_of_mem_uIoc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：eq_of_mem_uIoc_of_mem_uIoc : a in Ι b c -> b in Ι a c -> a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
lemma eq_of_mem_uIoc_of_mem_uIoc : a ∈ Ι b c → b ∈ Ι a c → a = b := by
  simp_rw [mem_uIoc]; rintro (⟨_, _⟩ | ⟨_, _⟩) (⟨_, _⟩ | ⟨_, _⟩) <;> apply le_antisymm <;>
    first | assumption | exact le_of_lt ‹_› | exact le_trans ‹_› (le_of_lt ‹_›)
/-
**Set.eq_of_mem_uIoc_of_mem_uIoc'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：eq_of_mem_uIoc_of_mem_uIoc' : b in Ι a c -> c in Ι a b -> b = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIoc_comm`：uIoc_comm (a b : α) : Ι a b = Ι b a
· 使用引理 `Set.eq_of_mem_uIoc_of_mem_uIoc`：eq_of_mem_uIoc_of_mem_uIoc : a in Ι b c 
-> b in Ι a c -> a = b
-/
lemma eq_of_mem_uIoc_of_mem_uIoc' : b ∈ Ι a c → c ∈ Ι a b → b = c := by
  simpa only [uIoc_comm a] using eq_of_mem_uIoc_of_mem_uIoc
/-
**Set.eq_of_notMem_uIoc_of_notMem_uIoc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：eq_of_notMem_uIoc_of_notMem_uIoc (ha : a <= c) (hb : b <= c) : a ∉ Ι b c -
> b ∉ Ι a c -> a = b
参数：ha : a <= c；hb : b <= c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eq_of_notMem_uIoc_of_notMem_uIoc (ha : a ≤ c) (hb : b ≤ c) :
    a ∉ Ι b c → b ∉ Ι a c → a = b := by
  grind
/-
**Set.uIoc_injective_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoc_injective_right (a : α) : Injective fun b => Ι b a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `LE.le.eq_of_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, 
a ≤ b → ¬a < b → a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `Set.eq_of_mem_uIoc_of_mem_uIoc`：eq_of_mem_uIoc_of_mem_uIoc : a in Ι b c 
-> b in Ι a c -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_uIoc`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a 
∈ Set.uIoc a b ↔ b < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
lemma uIoc_injective_right (a : α) : Injective fun b => Ι b a := by
  rintro b c h
  rw [Set.ext_iff] at h
  obtain ha | ha := le_or_gt b a
  · have hb := (h b).not
    simp only [ha, left_mem_uIoc, true_iff, notMem_uIoc, ← not_le,
      and_true, not_true, false_and, not_false_iff, or_false] at hb
    refine hb.eq_of_not_lt fun hc => ?_
    simpa [ha, and_iff_right hc, ← @not_le _ _ _ a, iff_not_self, -not_le] using h c
  · refine
      eq_of_mem_uIoc_of_mem_uIoc ((h _).1 <| left_mem_uIoc.2 ha)
        ((h _).2 <| left_mem_uIoc.2 <| ha.trans_le ?_)
    simpa [ha, ha.not_ge, mem_uIoc] using h b
/-
**Set.uIoc_injective_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoc_injective_left (a : α) : Injective (Ι a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.uIoc_comm`：uIoc_comm (a b : α) : Ι a b = Ι b a
· 使用引理 `Set.uIoc_injective_right`：uIoc_injective_right (a : α) : Injective fun b
 => Ι b a
-/
lemma uIoc_injective_left (a : α) : Injective (Ι a) := by
  simpa only [uIoc_comm] using uIoc_injective_right a
/-
**Set.uIoc_union_uIoc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoc_union_uIoc (h : b in [[a, c]]) : Ι a b union Ι b c = Ι a c
参数：h : b in [[a, c]]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Ioc_union_Ioc_eq_Ioc`：Ioc_union_Ioc_eq_Ioc (h₁ : a <= b) (h₂ : b <= 
c) : Ioc a b union Ioc b c = Ioc a c
· 使用引理 `Set.uIoc_comm`：uIoc_comm (a b : α) : Ι a b = Ι b a
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用引理 `Set.uIcc_comm`：uIcc_comm (a b : α) : [[a, b]] = [[b, a]]
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
lemma uIoc_union_uIoc (h : b ∈ [[a, c]]) : Ι a b ∪ Ι b c = Ι a c := by
  wlog hac : a ≤ c generalizing a c
  · rw [uIoc_comm, union_comm, uIoc_comm, this _ (le_of_not_ge hac), uIoc_comm]
    rwa [uIcc_comm]
  rw [uIcc_of_le hac] at h
  rw [uIoc_of_le h.1, uIoc_of_le h.2, uIoc_of_le hac, Ioc_union_Ioc_eq_Ioc h.1 h.2]

section uIoo

/-- `uIoo a b` is the set of elements lying between `a` and `b`, with `a` and `b` not included.
Note that we define it more generally in a lattice as `Set.Ioo (a ⊓ b) (a ⊔ b)`. In a product type,
`uIoo` corresponds to the bounding box of the two elements. -/
/-
**Set.uIoo** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：uIoo (a b : α) : Set α
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`uIoo a b` is the set of elements lying between `a` and `b`, with `a` and `b` no
t included.
Note that we define it more generally in a lattice as `Set.Ioo (a ⊓ b) (a ⊔ b)`.
 In a product type,
`uIoo` corresponds to the bounding box of the two elements.
-/
def uIoo (a b : α) : Set α := Ioo (a ⊓ b) (a ⊔ b)

@[simp]
/-
**Set.uIoo_toDual** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoo_toDual (a b : α) : uIoo (toDual a) (toDual b) = ofDual ⁻¹' uIoo a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo_toDual`：Ioo_toDual : Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo 
b a
-/
lemma uIoo_toDual (a b : α) : uIoo (toDual a) (toDual b) = ofDual ⁻¹' uIoo a b :=
  Ioo_toDual (α := α)

@[simp]
/-
**Set.uIoo_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：uIoo_ofDual (a b : αᵒᵈ) : uIoo (ofDual a) (ofDual b) = toDual ⁻¹' uIoo a b
参数：a b : αᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo_ofDual`：Ioo_ofDual {x y : αᵒᵈ} : Ioo (ofDual y) (ofDual x) = toD
ual ⁻¹' Ioo x y
-/
theorem uIoo_ofDual (a b : αᵒᵈ) : uIoo (ofDual a) (ofDual b) = toDual ⁻¹' uIoo a b :=
  Ioo_ofDual
/-
**Set.uIoo_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b → Set.uIoo a b = 
Set.Ioo a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIoo.eq_1`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), Set.uI
oo a b = Set.Ioo (min a b) (max a b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
-/
@[simp] lemma uIoo_of_le (h : a ≤ b) : uIoo a b = Ioo a b := by
  rw [uIoo, inf_eq_left.2 h, sup_eq_right.2 h]
/-
**Set.uIoo_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → Set.uIoo a b = 
Set.Ioo b a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIoo.eq_1`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), Set.uI
oo a b = Set.Ioo (min a b) (max a b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
-/
@[simp] lemma uIoo_of_ge (h : b ≤ a) : uIoo a b = Ioo b a := by
  rw [uIoo, inf_eq_right.2 h, sup_eq_left.2 h]
/-
**Set.uIoo_comm** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoo_comm (a b : α) : uIoo a b = uIoo b a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uIoo_comm (a b : α) : uIoo a b = uIoo b a := by simp_rw [uIoo, inf_comm, sup_comm]
/-
**Set.uIoo_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoo_of_lt (h : a < b) : uIoo a b = Ioo a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.uIoo_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoo a b = Set.Ioo a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma uIoo_of_lt (h : a < b) : uIoo a b = Ioo a b := uIoo_of_le h.le
/-
**Set.uIoo_of_gt** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoo_of_gt (h : b < a) : uIoo a b = Ioo b a
参数：h : b < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.uIoo_of_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a
 → Set.uIoo a b = Set.Ioo b a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma uIoo_of_gt (h : b < a) : uIoo a b = Ioo b a := uIoo_of_ge h.le
/-
**Set.uIoo_self** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoo_self : uIoo a a = ∅
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
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uIoo_self : uIoo a a = ∅ := by simp [uIoo]
/-
**Set.left_notMem_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ∉ Set.uIoo a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma left_notMem_uIoo : a ∉ uIoo a b := by simp +contextual [uIoo, le_of_lt]
/-
**Set.right_notMem_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ∉ Set.uIoo a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma right_notMem_uIoo : b ∉ uIoo a b := by simp +contextual [uIoo, le_of_lt]
/-
**Set.Ioo_subset_uIoo** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioo_subset_uIoo : Ioo a b subseteq uIoo a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo
 a₁ b₁ subseteq Ioo a₂ b₂
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma Ioo_subset_uIoo : Ioo a b ⊆ uIoo a b := Ioo_subset_Ioo inf_le_left le_sup_right

/-- Same as `Ioo_subset_uIoo` but with `Ioo a b` replaced by `Ioo b a`. -/
/-
**Set.Ioo_subset_uIoo'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioo_subset_uIoo' : Ioo b a subseteq uIoo a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo
 a₁ b₁ subseteq Ioo a₂ b₂
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b

--- 原说明 ---
Same as `Ioo_subset_uIoo` but with `Ioo a b` replaced by `Ioo b a`.
-/
lemma Ioo_subset_uIoo' : Ioo b a ⊆ uIoo a b := Ioo_subset_Ioo inf_le_right le_sup_left

variable {x : α}
/-
**Set.mem_uIoo_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_uIoo_of_lt (ha : a < x) (hb : x < b) : x in uIoo a b
参数：ha : a < x；hb : x < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Ioo_subset_uIoo`：Ioo_subset_uIoo : Ioo a b subseteq uIoo a b
-/
lemma mem_uIoo_of_lt (ha : a < x) (hb : x < b) : x ∈ uIoo a b := Ioo_subset_uIoo ⟨ha, hb⟩
/-
**Set.mem_uIoo_of_gt** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_uIoo_of_gt (hb : b < x) (ha : x < a) : x in uIoo a b
参数：hb : b < x；ha : x < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Ioo_subset_uIoo'`：Ioo_subset_uIoo' : Ioo b a subseteq uIoo a b
-/
lemma mem_uIoo_of_gt (hb : b < x) (ha : x < a) : x ∈ uIoo a b := Ioo_subset_uIoo' ⟨hb, ha⟩

variable {a b : α}
/-
**Set.Ioo_min_max** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_min_max : Ioo (min a b) (max a b) = uIoo a b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioo_min_max : Ioo (min a b) (max a b) = uIoo a b := rfl
/-
**Set.uIoo_of_not_le** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoo_of_not_le (h : ¬a <= b) : uIoo a b = Ioo b a
参数：h : ¬a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.uIoo_of_gt`：uIoo_of_gt (h : b < a) : uIoo a b = Ioo b a
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
-/
lemma uIoo_of_not_le (h : ¬a ≤ b) : uIoo a b = Ioo b a := uIoo_of_gt <| lt_of_not_ge h
/-
**Set.uIoo_of_not_ge** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoo_of_not_ge (h : ¬b <= a) : uIoo a b = Ioo a b
参数：h : ¬b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.uIoo_of_lt`：uIoo_of_lt (h : a < b) : uIoo a b = Ioo a b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
-/
lemma uIoo_of_not_ge (h : ¬b ≤ a) : uIoo a b = Ioo a b := uIoo_of_lt <| lt_of_not_ge h
/-
**Set.uIoo_subset_uIcc_self** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoo_subset_uIcc_self : uIoo a b subseteq uIcc a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma uIoo_subset_uIcc_self : uIoo a b ⊆ uIcc a b := by
  simp [uIoo, uIcc, Ioo_subset_Icc_self]
/-
**Set.uIoo_subset_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoo_subset_Ioo (ha : a₁ in Icc a₂ b₂) (hb : b₁ in Icc a₂ b₂) : uIoo a₁ b₁
 subseteq Ioo a₂ b₂
参数：ha : a₁ in Icc a₂ b₂；hb : b₁ in Icc a₂ b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo
 a₁ b₁ subseteq Ioo a₂ b₂
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma uIoo_subset_Ioo (ha : a₁ ∈ Icc a₂ b₂) (hb : b₁ ∈ Icc a₂ b₂) : uIoo a₁ b₁ ⊆ Ioo a₂ b₂ :=
  Ioo_subset_Ioo (le_inf ha.1 hb.1) (sup_le ha.2 hb.2)
/-
**Set.nonempty_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α} [DenselyOrdered α], (Set
.uIoo a b).Nonempty ↔ a ≠ b
参数：Set.uIoo a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma nonempty_uIoo [DenselyOrdered α] : (uIoo a b).Nonempty ↔ a ≠ b := by
  simp [uIoo, eq_comm]
/-
**Set.nonempty_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, (Set.uIoc a b).Nonempty
 ↔ a ≠ b
参数：Set.uIoc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma nonempty_uIoc : (uIoc a b).Nonempty ↔ a ≠ b := by
  simp [uIoc, eq_comm]
/-
**Set.uIoo_eq_union** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uIoo_eq_union : uIoo a b = Ioo a b union Ioo b a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIoo_of_lt`：uIoo_of_lt (h : a < b) : uIoo a b = Ioo a b
· 使用定理 `Set.Ioo_eq_empty_of_le`：Ioo_eq_empty_of_le (h : b <= a) : Ioo a b = ∅
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.uIoo_of_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a
 → Set.uIoo a b = Set.Ioo b a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
-/
lemma uIoo_eq_union : uIoo a b = Ioo a b ∪ Ioo b a := by
  rcases lt_or_ge a b with h | h
  · simp [uIoo_of_lt, h, Ioo_eq_empty_of_le h.le]
  · simp [uIoo_of_ge, h]

end uIoo

end LinearOrder

end Set

