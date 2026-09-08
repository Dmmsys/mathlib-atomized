/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Priestley spaces

This file defines Priestley spaces. A Priestley space is an ordered compact topological space such
that any two distinct points can be separated by a clopen upper set.

## Main declarations

* `PriestleySpace`: Prop-valued mixin stating the Priestley separation axiom: Any two distinct
  points can be separated by a clopen upper set.

## Implementation notes

We do not include compactness in the definition, so a Priestley space is to be declared as follows:
`[Preorder α] [TopologicalSpace α] [CompactSpace α] [PriestleySpace α]`

## References

* [Wikipedia, *Priestley space*](https://en.wikipedia.org/wiki/Priestley_space)
* [Davey, Priestley *Introduction to Lattices and Order*][davey_priestley]
-/

public section


open Set

variable {α : Type*}

/-- A Priestley space is an ordered topological space such that any two distinct points can be
separated by a clopen upper set. Compactness is often assumed, but we do not include it here. -/
/-
**PriestleySpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [Preorder α] → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Priestley space is an ordered topological space such that any two distinct poi
nts can be
separated by a clopen upper set. Compactness is often assumed, but we do not inc
lude it here.
-/
class PriestleySpace (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  priestley {x y : α} : ¬x ≤ y → ∃ U : Set α, IsClopen U ∧ IsUpperSet U ∧ x ∈ U ∧ y ∉ U

variable [TopologicalSpace α]

section Preorder

variable [Preorder α] [PriestleySpace α] {x y : α}

/-
**exists_isClopen_upper_of_not_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isClopen_upper_of_not_le : ¬x <= y -> exists U : Set α, IsClopen U 
∧ IsUpperSet U ∧ x in U ∧ y ∉ U
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PriestleySpace.priestley`：∀ {α : Type u_2} {inst : Preorder α} {inst_1 :
 TopologicalSpace α} [self : PriestleySpace α] {x y : α},   ¬x ≤ y → ∃ U, IsClop
en U ∧ IsUpper…
-/
theorem exists_isClopen_upper_of_not_le :
    ¬x ≤ y → ∃ U : Set α, IsClopen U ∧ IsUpperSet U ∧ x ∈ U ∧ y ∉ U :=
  PriestleySpace.priestley
/-
**exists_isClopen_lower_of_not_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isClopen_lower_of_not_le (h : ¬x <= y) : exists U : Set α, IsClopen
 U ∧ IsLowerSet U ∧ x ∉ U ∧ y in U
参数：h : ¬x <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_isClopen_upper_of_not_le`：exists_isClopen_upper_of_not_le : ¬x <=
 y -> exists U : Set α, IsClopen U ∧ IsUpperSet U ∧ x in U ∧ y ∉ U
· 使用定理 `IsClopen.compl`：IsClopen.compl (hs : IsClopen s) : IsClopen sᶜ
· 使用定理 `IsUpperSet.compl`：IsUpperSet.compl (hs : IsUpperSet s) : IsLowerSet sᶜ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem exists_isClopen_lower_of_not_le (h : ¬x ≤ y) :
    ∃ U : Set α, IsClopen U ∧ IsLowerSet U ∧ x ∉ U ∧ y ∈ U :=
  let ⟨U, hU, hU', hx, hy⟩ := exists_isClopen_upper_of_not_le h
  ⟨Uᶜ, hU.compl, hU'.compl, Classical.not_not.2 hx, hy⟩

end Preorder

section PartialOrder

variable [PartialOrder α] [PriestleySpace α] {x y : α}

/-
**exists_isClopen_upper_or_lower_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isClopen_upper_or_lower_of_ne (h : x != y) : exists U : Set α, IsCl
open U ∧ (IsUpperSet U ∨ IsLowerSet U) ∧ x in U ∧ y ∉ U
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.not_le_or_not_ge`：Ne.not_le_or_not_ge (h : a != b) : ¬a <= b ∨ ¬b <= 
a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `And.imp_left`：∀ {a b c : Prop}, (a → b) → a ∧ c → b ∧ c
· 使用定理 `exists_isClopen_upper_of_not_le`：exists_isClopen_upper_of_not_le : ¬x <=
 y -> exists U : Set α, IsClopen U ∧ IsUpperSet U ∧ x in U ∧ y ∉ U
· 使用定理 `exists_isClopen_lower_of_not_le`：exists_isClopen_lower_of_not_le (h : ¬x
 <= y) : exists U : Set α, IsClopen U ∧ IsLowerSet U ∧ x ∉ U ∧ y in U
-/
theorem exists_isClopen_upper_or_lower_of_ne (h : x ≠ y) :
    ∃ U : Set α, IsClopen U ∧ (IsUpperSet U ∨ IsLowerSet U) ∧ x ∈ U ∧ y ∉ U := by
  obtain h | h := h.not_le_or_not_ge
  · exact (exists_isClopen_upper_of_not_le h).imp fun _ ↦ And.imp_right <| And.imp_left Or.inl
  · obtain ⟨U, hU, hU', hy, hx⟩ := exists_isClopen_lower_of_not_le h
    exact ⟨U, hU, Or.inr hU', hx, hy⟩

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PriestleySpace.toTotallySeparatedSpace : TotallySeparatedSpace α where
  isTotallySeparated_univ _ _ _ _ h :=
    (exists_isClopen_upper_or_lower_of_ne h).elim fun U ⟨hU, _, hx, hy⟩ =>
      ⟨U, Uᶜ, hU.isOpen, hU.compl.isOpen, hx, hy,
        union_compl_self U ▸ subset_rfl, disjoint_compl_right⟩

end PartialOrder

