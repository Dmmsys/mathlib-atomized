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

/--
Definition of `PriestleySpace` / `PriestleySpace` 的定义

English:
class PriestleySpace
  parameters: (α : Type*) [Preorder α] [TopologicalSpace α]
  axioms and operations (1):
    - priestley({x y : α}) : ¬x <= y -> exists U : Set α, IsClopen U ∧ IsUpperSet U ∧ x in U ∧ y ∉ U

中文:
类 PriestleySpace
  参数: (α : 类型) [Preorder α] [TopologicalSpace α]
  公理与运算 (1 个):
    - priestley({x y : α}) : ¬x <= y -> 存在 U : Set α, IsClopen U ∧ IsUpperSet U ∧ x in U ∧ y ∉ U
-/
class PriestleySpace (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  priestley {x y : α} : ¬x <= y -> exists U : Set α, IsClopen U ∧ IsUpperSet U ∧ x in U ∧ y ∉ U

variable [TopologicalSpace α]

section Preorder

variable [Preorder α] [PriestleySpace α] {x y : α}

/--
theorem `exists_isClopen_upper_of_not_le` / 定理 `exists_isClopen_upper_of_not_le`

English:
theorem exists_isClopen_upper_of_not_le
  proof: PriestleySpace.priestley

中文:
定理 exists_isClopen_upper_of_not_le
  证明: PriestleySpace.priestley

Depends on / 依赖: PriestleySpace, PriestleySpace.priestley, priestley
-/
theorem exists_isClopen_upper_of_not_le :
    ¬x <= y -> exists U : Set α, IsClopen U ∧ IsUpperSet U ∧ x in U ∧ y ∉ U :=
  PriestleySpace.priestley

/--
theorem `exists_isClopen_lower_of_not_le` / 定理 `exists_isClopen_lower_of_not_le`

English:
theorem exists_isClopen_lower_of_not_le
  given: (h : ¬x <= y)
  proof: let ⟨U, hU, hU', hx, hy⟩ := exists_isClopen_upper_of_not_le h
  ⟨Uᶜ, hU.compl, hU'.compl, Classical.not_not.2 hx, hy⟩

中文:
定理 exists_isClopen_lower_of_not_le
  条件: (h : ¬x <= y)
  证明: let ⟨U, hU, hU', hx, hy⟩ := exists_isClopen_upper_of_not_le h
  ⟨Uᶜ, hU.compl, hU'.compl, Classical.not_not.2 hx, hy⟩

Depends on / 依赖: Classical, Classical.not_not, exists_isClopen_upper_of_not_le, hU.compl, not_not
-/
theorem exists_isClopen_lower_of_not_le (h : ¬x <= y) :
    exists U : Set α, IsClopen U ∧ IsLowerSet U ∧ x ∉ U ∧ y in U :=
  let ⟨U, hU, hU', hx, hy⟩ := exists_isClopen_upper_of_not_le h
  ⟨Uᶜ, hU.compl, hU'.compl, Classical.not_not.2 hx, hy⟩

end Preorder

section PartialOrder

variable [PartialOrder α] [PriestleySpace α] {x y : α}

/--
theorem `exists_isClopen_upper_or_lower_of_ne` / 定理 `exists_isClopen_upper_or_lower_of_ne`

English:
theorem exists_isClopen_upper_or_lower_of_ne
  given: (h : x != y)
  proof: by
  obtain h | h := h.not_le_or_not_ge
· exact (exists_isClopen_upper_of_not_le h).imp fun _ => And.imp_right And.imp_left Or.inl
  · obtain ⟨U, hU, hU', hy, hx⟩ := exists_isClopen_lower_of_not_le h
    exact ⟨U, hU, Or.inr hU', hx, hy⟩

中文:
定理 exists_isClopen_upper_or_lower_of_ne
  条件: (h : x != y)
  证明: by
  obtain h | h := h.not_le_or_not_ge
· exact (exists_isClopen_upper_of_not_le h).imp fun _ => And.imp_right And.imp_left Or.inl
  · obtain ⟨U, hU, hU', hy, hx⟩ := exists_isClopen_lower_of_not_le h
    exact ⟨U, hU, Or.inr hU', hx, hy⟩

Depends on / 依赖: And.imp_left, And.imp_right, Or.inl, Or.inr, exists_isClopen_lower_of_not_le, exists_isClopen_upper_of_not_le, h.not_le_or_not_ge, imp_left, imp_right, not_le_or_not_ge
-/
theorem exists_isClopen_upper_or_lower_of_ne (h : x != y) :
    exists U : Set α, IsClopen U ∧ (IsUpperSet U ∨ IsLowerSet U) ∧ x in U ∧ y ∉ U := by
  obtain h | h := h.not_le_or_not_ge
· exact (exists_isClopen_upper_of_not_le h).imp fun _ => And.imp_right And.imp_left Or.inl
  · obtain ⟨U, hU, hU', hy, hx⟩ := exists_isClopen_lower_of_not_le h
    exact ⟨U, hU, Or.inr hU', hx, hy⟩

-- See note [lower instance priority]
instance (priority := 100) PriestleySpace.toTotallySeparatedSpace : TotallySeparatedSpace α where
  isTotallySeparated_univ _ _ _ _ h :=
    (exists_isClopen_upper_or_lower_of_ne h).elim fun U ⟨hU, _, hx, hy⟩ =>
      ⟨U, Uᶜ, hU.isOpen, hU.compl.isOpen, hx, hy,
        union_compl_self U ▸ subset_rfl, disjoint_compl_right⟩

end PartialOrder
