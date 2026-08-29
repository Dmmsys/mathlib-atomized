/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Tactic.Common

/-!
# Co-Heyting boundary

The boundary of an element of a co-Heyting algebra is the intersection of its Heyting negation with
itself. The boundary in the co-Heyting algebra of closed sets coincides with the topological
boundary.

## Main declarations

* `Coheyting.boundary`: Co-Heyting boundary. `Coheyting.boundary a = a ⊓ ￢a`

## Notation

`∂ a` is notation for `Coheyting.boundary a` in scope `Heyting`.
-/

@[expose] public section

assert_not_exists RelIso

variable {α : Type*}

namespace Coheyting

variable [CoheytingAlgebra α] {a b : α}

/--
Definition of `boundary` / `boundary` 的定义

English:
definition boundary
  signature: (a : α)
  body: a ⊓ ￢a

中文:
定义 boundary
  签名: (a : α)
  定义体: a ⊓ ￢a
-/
def boundary (a : α) : α :=
  a ⊓ ￢a

/-- The boundary of an element of a co-Heyting algebra. -/
scoped[Heyting] prefix:120 "∂ " => Coheyting.boundary

open Heyting

-- TODO: Should hnot be named hNot?
/--
theorem `inf_hnot_self` / 定理 `inf_hnot_self`

English:
theorem inf_hnot_self
  given: (a : α)
  statement: a ⊓ ￢a = ∂ a
  proof: rfl

中文:
定理 inf_hnot_self
  条件: (a : α)
  结论: a ⊓ ￢a = ∂ a
  证明: rfl
-/
theorem inf_hnot_self (a : α) : a ⊓ ￢a = ∂ a :=
  rfl

/--
theorem `boundary_le` / 定理 `boundary_le`

English:
theorem boundary_le
  statement: ∂ a <= a
  proof: inf_le_left

中文:
定理 boundary_le
  结论: ∂ a <= a
  证明: inf_le_left

Depends on / 依赖: inf_le_left
-/
theorem boundary_le : ∂ a <= a :=
  inf_le_left

/--
theorem `boundary_le_hnot` / 定理 `boundary_le_hnot`

English:
theorem boundary_le_hnot
  statement: ∂ a <= ￢a
  proof: inf_le_right

@[simp]

中文:
定理 boundary_le_hnot
  结论: ∂ a <= ￢a
  证明: inf_le_right

@[simp]

Depends on / 依赖: inf_le_right
-/
theorem boundary_le_hnot : ∂ a <= ￢a :=
  inf_le_right

@[simp]
/--
theorem `boundary_bot` / 定理 `boundary_bot`

English:
theorem boundary_bot
  statement: ∂ (⊥ : α) = ⊥
  proof: bot_inf_eq _

@[simp]

中文:
定理 boundary_bot
  结论: ∂ (⊥ : α) = ⊥
  证明: bot_inf_eq _

@[simp]

Depends on / 依赖: bot_inf_eq
-/
theorem boundary_bot : ∂ (⊥ : α) = ⊥ := bot_inf_eq _

@[simp]
/--
theorem `boundary_top` / 定理 `boundary_top`

English:
theorem boundary_top
  statement: ∂ (⊤ : α) = ⊥
  proof: by rw [boundary, hnot_top, inf_bot_eq]

中文:
定理 boundary_top
  结论: ∂ (⊤ : α) = ⊥
  证明: by rw [boundary, hnot_top, inf_bot_eq]

Depends on / 依赖: boundary, hnot_top, inf_bot_eq
-/
theorem boundary_top : ∂ (⊤ : α) = ⊥ := by rw [boundary, hnot_top, inf_bot_eq]

/--
theorem `boundary_hnot_le` / 定理 `boundary_hnot_le`

English:
theorem boundary_hnot_le
  given: (a : α)
  statement: ∂ (￢a) <= ∂ a
  proof: (inf_comm _ _).trans_le inf_le_inf_right _ hnot_hnot_le

@[simp]

中文:
定理 boundary_hnot_le
  条件: (a : α)
  结论: ∂ (￢a) <= ∂ a
  证明: (inf_comm _ _).trans_le inf_le_inf_right _ hnot_hnot_le

@[simp]

Depends on / 依赖: hnot_hnot_le, inf_comm, inf_le_inf_right, trans_le
-/
theorem boundary_hnot_le (a : α) : ∂ (￢a) <= ∂ a :=
(inf_comm _ _).trans_le inf_le_inf_right _ hnot_hnot_le

@[simp]
/--
theorem `boundary_hnot_hnot` / 定理 `boundary_hnot_hnot`

English:
theorem boundary_hnot_hnot
  given: (a : α)
  statement: ∂ (￢￢a) = ∂ (￢a)
  proof: by
  simp_rw [boundary, hnot_hnot_hnot, inf_comm]

@[simp]

中文:
定理 boundary_hnot_hnot
  条件: (a : α)
  结论: ∂ (￢￢a) = ∂ (￢a)
  证明: by
  simp_rw [boundary, hnot_hnot_hnot, inf_comm]

@[simp]

Depends on / 依赖: boundary, hnot_hnot_hnot, inf_comm, simp_rw
-/
theorem boundary_hnot_hnot (a : α) : ∂ (￢￢a) = ∂ (￢a) := by
  simp_rw [boundary, hnot_hnot_hnot, inf_comm]

@[simp]
/--
theorem `hnot_boundary` / 定理 `hnot_boundary`

English:
theorem hnot_boundary
  given: (a : α)
  statement: ￢∂ a = ⊤
  proof: by rw [boundary, hnot_inf_distrib, sup_hnot_self]

中文:
定理 hnot_boundary
  条件: (a : α)
  结论: ￢∂ a = ⊤
  证明: by rw [boundary, hnot_inf_distrib, sup_hnot_self]

Depends on / 依赖: boundary, hnot_inf_distrib, sup_hnot_self
-/
theorem hnot_boundary (a : α) : ￢∂ a = ⊤ := by rw [boundary, hnot_inf_distrib, sup_hnot_self]

/--
theorem `boundary_inf` / 定理 `boundary_inf`

English:
theorem boundary_inf
  given: (a b : α)
  statement: ∂ (a ⊓ b) = ∂ a ⊓ b ⊔ a ⊓ ∂ b
  proof: by
  unfold boundary
  rw [hnot_inf_distrib]; rw [inf_sup_left]; rw [inf_right_comm]; rw [← inf_assoc]

中文:
定理 boundary_inf
  条件: (a b : α)
  结论: ∂ (a ⊓ b) = ∂ a ⊓ b ⊔ a ⊓ ∂ b
  证明: by
  unfold boundary
  rw [hnot_inf_distrib]; rw [inf_sup_left]; rw [inf_right_comm]; rw [← inf_assoc]

Depends on / 依赖: boundary, hnot_inf_distrib, inf_assoc, inf_right_comm, inf_sup_left
-/
theorem boundary_inf (a b : α) : ∂ (a ⊓ b) = ∂ a ⊓ b ⊔ a ⊓ ∂ b := by
  unfold boundary
  rw [hnot_inf_distrib]; rw [inf_sup_left]; rw [inf_right_comm]; rw [← inf_assoc]

/--
theorem `boundary_inf_le` / 定理 `boundary_inf_le`

English:
theorem boundary_inf_le
  statement: ∂ (a ⊓ b) <= ∂ a ⊔ ∂ b
  proof: (boundary_inf _ _).trans_le sup_le_sup inf_le_left inf_le_right

中文:
定理 boundary_inf_le
  结论: ∂ (a ⊓ b) <= ∂ a ⊔ ∂ b
  证明: (boundary_inf _ _).trans_le sup_le_sup inf_le_left inf_le_right

Depends on / 依赖: boundary_inf, inf_le_left, inf_le_right, sup_le_sup, trans_le
-/
theorem boundary_inf_le : ∂ (a ⊓ b) <= ∂ a ⊔ ∂ b :=
(boundary_inf _ _).trans_le sup_le_sup inf_le_left inf_le_right

/--
theorem `boundary_sup_le` / 定理 `boundary_sup_le`

English:
theorem boundary_sup_le
  statement: ∂ (a ⊔ b) <= ∂ a ⊔ ∂ b
  proof: by
  rw [boundary]; rw [inf_sup_right]
  exact
    sup_le_sup (inf_le_inf_left _ <| hnot_anti le_sup_left)
      (inf_le_inf_left _ <| hnot_anti le_sup_right)

中文:
定理 boundary_sup_le
  结论: ∂ (a ⊔ b) <= ∂ a ⊔ ∂ b
  证明: by
  rw [boundary]; rw [inf_sup_right]
  exact
    sup_le_sup (inf_le_inf_left _ <| hnot_anti le_sup_left)
      (inf_le_inf_left _ <| hnot_anti le_sup_right)

Depends on / 依赖: boundary, hnot_anti, inf_le_inf_left, inf_sup_right, le_sup_left, le_sup_right, sup_le_sup
-/
theorem boundary_sup_le : ∂ (a ⊔ b) <= ∂ a ⊔ ∂ b := by
  rw [boundary]; rw [inf_sup_right]
  exact
    sup_le_sup (inf_le_inf_left _ <| hnot_anti le_sup_left)
      (inf_le_inf_left _ <| hnot_anti le_sup_right)

/-- The intuitionistic version of `Coheyting.boundary_le_boundary_sup_sup_boundary_inf_left`. Either
proof can be obtained from the other using the equivalence of Heyting algebras and intuitionistic
logic and duality between Heyting and co-Heyting algebras. It is crucial that the following proof be
intuitionistic. -/
example (a b : Prop) : (a ∧ b ∨ ¬(a ∧ b)) ∧ ((a ∨ b) ∨ ¬(a ∨ b)) -> a ∨ ¬a := by
  rintro ⟨⟨ha, _⟩ | hnab, (ha | hb) | hnab⟩ <;> try exact Or.inl ha
  · exact Or.inr fun ha => hnab ⟨ha, hb⟩
· exact Or.inr fun ha => hnab Or.inl ha

/--
theorem `boundary_le_boundary_sup_sup_boundary_inf_left` / 定理 `boundary_le_boundary_sup_sup_boundary_inf_left`

English:
theorem boundary_le_boundary_sup_sup_boundary_inf_left
  statement: ∂ a <= ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b)
  proof: by
  simp only [boundary, sup_inf_left, sup_inf_right, sup_right_idem, le_inf_iff, sup_assoc,
    sup_comm _ a]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_, ?_⟩ <;> try { exact le_sup_of_le_left inf_le_left } <;>
    refine inf_le_of_right_le ?_
  · rw [hnot_le_iff_codisjoint_right, codisjoint_left_comm]
    exact codisjoint_hnot_left
  · refine le_sup_of_le_right ?_
    rw [hnot_le_iff_codisjoint_right]
    exact codisjoint_hnot_right.mono_right (hnot_anti inf_le_left)

中文:
定理 boundary_le_boundary_sup_sup_boundary_inf_left
  结论: ∂ a <= ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b)
  证明: by
  simp only [boundary, sup_inf_left, sup_inf_right, sup_right_idem, le_inf_iff, sup_assoc,
    sup_comm _ a]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_, ?_⟩ <;> try { exact le_sup_of_le_left inf_le_left } <;>
    refine inf_le_of_right_le ?_
  · rw [hnot_le_iff_codisjoint_right, codisjoint_left_comm]
    exact codisjoint_hnot_left
  · refine le_sup_of_le_right ?_
    rw [hnot_le_iff_codisjoint_right]
    exact codisjoint_hnot_right.mono_right (hnot_anti inf_le_left)

Depends on / 依赖: boundary, codisjoint_hnot_left, codisjoint_hnot_right, codisjoint_hnot_right.mono_right, codisjoint_left_comm, hnot_anti, hnot_le_iff_codisjoint_right, inf_le_left, inf_le_of_right_le, le_inf_iff, le_sup_of_le_left, le_sup_of_le_right, mono_right, sup_assoc, sup_comm, sup_inf_left, sup_inf_right, sup_right_idem
-/
theorem boundary_le_boundary_sup_sup_boundary_inf_left : ∂ a <= ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b) := by
  simp only [boundary, sup_inf_left, sup_inf_right, sup_right_idem, le_inf_iff, sup_assoc,
    sup_comm _ a]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_, ?_⟩ <;> try { exact le_sup_of_le_left inf_le_left } <;>
    refine inf_le_of_right_le ?_
  · rw [hnot_le_iff_codisjoint_right, codisjoint_left_comm]
    exact codisjoint_hnot_left
  · refine le_sup_of_le_right ?_
    rw [hnot_le_iff_codisjoint_right]
    exact codisjoint_hnot_right.mono_right (hnot_anti inf_le_left)

/--
theorem `boundary_le_boundary_sup_sup_boundary_inf_right` / 定理 `boundary_le_boundary_sup_sup_boundary_inf_right`

English:
theorem boundary_le_boundary_sup_sup_boundary_inf_right
  statement: ∂ b <= ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b)
  proof: by
  rw [sup_comm a]; rw [inf_comm]
  exact boundary_le_boundary_sup_sup_boundary_inf_left

中文:
定理 boundary_le_boundary_sup_sup_boundary_inf_right
  结论: ∂ b <= ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b)
  证明: by
  rw [sup_comm a]; rw [inf_comm]
  exact boundary_le_boundary_sup_sup_boundary_inf_left

Depends on / 依赖: boundary_le_boundary_sup_sup_boundary_inf_left, inf_comm, sup_comm
-/
theorem boundary_le_boundary_sup_sup_boundary_inf_right : ∂ b <= ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b) := by
  rw [sup_comm a]; rw [inf_comm]
  exact boundary_le_boundary_sup_sup_boundary_inf_left

/--
theorem `boundary_sup_sup_boundary_inf` / 定理 `boundary_sup_sup_boundary_inf`

English:
theorem boundary_sup_sup_boundary_inf
  given: (a b : α)
  statement: ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b) = ∂ a ⊔ ∂ b
  proof: le_antisymm (sup_le boundary_sup_le boundary_inf_le)
    sup_le boundary_le_boundary_sup_sup_boundary_inf_left
      boundary_le_boundary_sup_sup_boundary_inf_right

@[simp]

中文:
定理 boundary_sup_sup_boundary_inf
  条件: (a b : α)
  结论: ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b) = ∂ a ⊔ ∂ b
  证明: le_antisymm (sup_le boundary_sup_le boundary_inf_le)
    sup_le boundary_le_boundary_sup_sup_boundary_inf_left
      boundary_le_boundary_sup_sup_boundary_inf_right

@[simp]

Depends on / 依赖: boundary_inf_le, boundary_le_boundary_sup_sup_boundary_inf_left, boundary_le_boundary_sup_sup_boundary_inf_right, boundary_sup_le, le_antisymm, sup_le
-/
theorem boundary_sup_sup_boundary_inf (a b : α) : ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b) = ∂ a ⊔ ∂ b :=
le_antisymm (sup_le boundary_sup_le boundary_inf_le)
    sup_le boundary_le_boundary_sup_sup_boundary_inf_left
      boundary_le_boundary_sup_sup_boundary_inf_right

@[simp]
/--
theorem `boundary_boundary` / 定理 `boundary_boundary`

English:
theorem boundary_boundary
  given: (a : α)
  statement: ∂ ∂ a = ∂ a
  proof: by rw [boundary, hnot_boundary, inf_top_eq]

alias boundary_idem := boundary_boundary

中文:
定理 boundary_boundary
  条件: (a : α)
  结论: ∂ ∂ a = ∂ a
  证明: by rw [boundary, hnot_boundary, inf_top_eq]

alias boundary_idem := boundary_boundary

Depends on / 依赖: boundary, hnot_boundary, inf_top_eq
-/
theorem boundary_boundary (a : α) : ∂ ∂ a = ∂ a := by rw [boundary, hnot_boundary, inf_top_eq]

alias boundary_idem := boundary_boundary

/--
theorem `hnot_hnot_sup_boundary` / 定理 `hnot_hnot_sup_boundary`

English:
theorem hnot_hnot_sup_boundary
  given: (a : α)
  statement: ￢￢a ⊔ ∂ a = a
  proof: by
  rw [boundary]; rw [sup_inf_left]; rw [hnot_sup_self]; rw [inf_top_eq]; rw [sup_eq_right]
  exact hnot_hnot_le

中文:
定理 hnot_hnot_sup_boundary
  条件: (a : α)
  结论: ￢￢a ⊔ ∂ a = a
  证明: by
  rw [boundary]; rw [sup_inf_left]; rw [hnot_sup_self]; rw [inf_top_eq]; rw [sup_eq_right]
  exact hnot_hnot_le

Depends on / 依赖: boundary, hnot_hnot_le, hnot_sup_self, inf_top_eq, sup_eq_right, sup_inf_left
-/
theorem hnot_hnot_sup_boundary (a : α) : ￢￢a ⊔ ∂ a = a := by
  rw [boundary]; rw [sup_inf_left]; rw [hnot_sup_self]; rw [inf_top_eq]; rw [sup_eq_right]
  exact hnot_hnot_le

/--
theorem `sdiff_boundary_self` / 定理 `sdiff_boundary_self`

English:
theorem sdiff_boundary_self
  statement: a \ ∂ a = ￢￢a
  proof: by
  rw (occs := [1]) [← hnot_hnot_sup_boundary a]
  rw [sup_sdiff_distrib]; rw [sdiff_self]; rw [sup_bot_eq]; rw [hnot_sdiff_comm]; rw [hnot_boundary]; rw [top_sdiff']

中文:
定理 sdiff_boundary_self
  结论: a \ ∂ a = ￢￢a
  证明: by
  rw (occs := [1]) [← hnot_hnot_sup_boundary a]
  rw [sup_sdiff_distrib]; rw [sdiff_self]; rw [sup_bot_eq]; rw [hnot_sdiff_comm]; rw [hnot_boundary]; rw [top_sdiff']

Depends on / 依赖: hnot_boundary, hnot_hnot_sup_boundary, hnot_sdiff_comm, sdiff_self, sup_bot_eq, sup_sdiff_distrib, top_sdiff
-/
theorem sdiff_boundary_self : a \ ∂ a = ￢￢a := by
  rw (occs := [1]) [← hnot_hnot_sup_boundary a]
  rw [sup_sdiff_distrib]; rw [sdiff_self]; rw [sup_bot_eq]; rw [hnot_sdiff_comm]; rw [hnot_boundary]; rw [top_sdiff']

/--
theorem `hnot_eq_top_iff_exists_boundary` / 定理 `hnot_eq_top_iff_exists_boundary`

English:
theorem hnot_eq_top_iff_exists_boundary
  statement: ￢a = ⊤ ↔ exists b, ∂ b = a
  proof: ⟨fun h => ⟨a, by rw [boundary, h, inf_top_eq]⟩, by
    rintro ⟨b, rfl⟩
    exact hnot_boundary _⟩

中文:
定理 hnot_eq_top_iff_存在_boundary
  结论: ￢a = ⊤ ↔ 存在 b, ∂ b = a
  证明: ⟨fun h => ⟨a, by rw [boundary, h, inf_top_eq]⟩, by
    rintro ⟨b, rfl⟩
    exact hnot_boundary _⟩

Depends on / 依赖: boundary, hnot_boundary, inf_top_eq
-/
theorem hnot_eq_top_iff_exists_boundary : ￢a = ⊤ ↔ exists b, ∂ b = a :=
  ⟨fun h => ⟨a, by rw [boundary, h, inf_top_eq]⟩, by
    rintro ⟨b, rfl⟩
    exact hnot_boundary _⟩

end Coheyting

open Heyting

section BooleanAlgebra

variable [BooleanAlgebra α]

@[simp]
/--
theorem `Coheyting.boundary_eq_bot` / 定理 `Coheyting.boundary_eq_bot`

English:
theorem Coheyting.boundary_eq_bot
  given: (a : α)
  statement: ∂ a = ⊥
  proof: inf_compl_eq_bot

中文:
定理 Coheyting.boundary_eq_bot
  条件: (a : α)
  结论: ∂ a = ⊥
  证明: inf_compl_eq_bot

Depends on / 依赖: inf_compl_eq_bot
-/
theorem Coheyting.boundary_eq_bot (a : α) : ∂ a = ⊥ :=
  inf_compl_eq_bot

end BooleanAlgebra
