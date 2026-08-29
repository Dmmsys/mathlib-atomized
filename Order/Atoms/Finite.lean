/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Atoms
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Preorder.Finite

/-!
# Atoms, Coatoms, Simple Lattices, and Finiteness

This module contains some results on atoms and simple lattices in the finite context.

## Main results
* `Finite.to_isAtomic`, `Finite.to_isCoatomic`: Finite partial orders with bottom resp. top
  are atomic resp. coatomic.

-/

public section


variable {α β : Type*}

namespace IsSimpleOrder

variable [LE α] [BoundedOrder α] [IsSimpleOrder α]

section DecidableEq

/-- It is important that `IsSimpleOrder` is the last type-class argument of this instance,
so that type-class inference fails quickly if it doesn't apply.

Note that as of 2025-08-13, this is false. Could someone investigate? -/
scoped instance (priority := 200) [DecidableEq α] : Fintype α :=
  Fintype.ofEquiv Bool equivBool.symm

end DecidableEq

scoped instance (priority := 200) : Finite α := by classical infer_instance

end IsSimpleOrder

namespace Fintype

namespace IsSimpleOrder

open scoped _root_.IsSimpleOrder

variable [LE α] [BoundedOrder α] [IsSimpleOrder α] [DecidableEq α]

/--
theorem `univ` / 定理 `univ`

English:
theorem univ
  statement: (Finset.univ : Finset α) = {⊤, ⊥}
  proof: by
  ext
  simpa using (eq_bot_or_eq_top _).symm

中文:
定理 univ
  结论: (Finset.univ : Finset α) = {⊤, ⊥}
  证明: by
  ext
  simpa using (eq_bot_or_eq_top _).symm

Depends on / 依赖: eq_bot_or_eq_top
-/
theorem univ : (Finset.univ : Finset α) = {⊤, ⊥} := by
  ext
  simpa using (eq_bot_or_eq_top _).symm

/--
theorem `card` / 定理 `card`

English:
theorem card
  statement: Fintype.card α = 2
  proof: (Fintype.ofEquiv_card _).trans Fintype.card_bool

中文:
定理 card
  结论: Fintype.card α = 2
  证明: (Fintype.ofEquiv_card _).trans Fintype.card_bool

Depends on / 依赖: Fintype, Fintype.card_bool, Fintype.ofEquiv_card, card_bool, ofEquiv_card
-/
theorem card : Fintype.card α = 2 :=
  (Fintype.ofEquiv_card _).trans Fintype.card_bool

end IsSimpleOrder

end Fintype

namespace Bool

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSimpleOrder Bool
  body: ⟨fun a => by
    rw [← Finset.mem_singleton]; rw [Or.comm]; rw [← Finset.mem_insert]; rw [top_eq_true]; rw [bot_eq_false]; rw [←
      Fintype.univ_bool]
    apply Finset.mem_univ⟩

中文:
实例 :
  签名: IsSimpleOrder 布尔
  定义体: ⟨fun a => by
    rw [← Finset.mem_singleton]; rw [Or.comm]; rw [← Finset.mem_insert]; rw [top_eq_true]; rw [bot_eq_false]; rw [←
      Fintype.univ_bool]
    apply Finset.mem_univ⟩

Depends on / 依赖: Finset, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, Fintype, Fintype.univ_bool, Or.comm, bot_eq_false, mem_insert, mem_singleton, mem_univ, top_eq_true, univ_bool
-/
instance : IsSimpleOrder Bool :=
  ⟨fun a => by
    rw [← Finset.mem_singleton]; rw [Or.comm]; rw [← Finset.mem_insert]; rw [top_eq_true]; rw [bot_eq_false]; rw [←
      Fintype.univ_bool]
    apply Finset.mem_univ⟩

end Bool

section Fintype

open Finset

-- see Note [lower instance priority]
instance (priority := 100) Finite.to_isCoatomic [PartialOrder α] [OrderTop α] [Finite α] :
    IsCoatomic α :=
  IsStronglyCoatomic.toIsCoatomic α

-- see Note [lower instance priority]
instance (priority := 100) Finite.to_isAtomic [PartialOrder α] [OrderBot α] [Finite α] :
    IsAtomic α :=
  isCoatomic_dual_iff_isAtomic.mp Finite.to_isCoatomic

end Fintype

section LocallyFinite

variable [Preorder α] [LocallyFiniteOrder α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStronglyAtomic α
  body: by
    obtain ⟨x, hx, hxmin⟩ := (LocallyFiniteOrder.finsetIoc a b).exists_minimal
      ⟨b, by simpa [LocallyFiniteOrder.finset_mem_Ioc]⟩
    simp only [LocallyFiniteOrder.finset_mem_Ioc] at hx hxmin
exact ⟨x, ⟨hx.1, fun c hac hcx => hcx.not_ge hxmin ⟨hac, hcx.le.trans hx.2⟩ hcx.le⟩, hx.2⟩

中文:
实例 :
  签名: IsStronglyAtomic α
  定义体: by
    obtain ⟨x, hx, hxmin⟩ := (LocallyFiniteOrder.finsetIoc a b).exists_minimal
      ⟨b, by simpa [LocallyFiniteOrder.finset_mem_Ioc]⟩
    simp only [LocallyFiniteOrder.finset_mem_Ioc] at hx hxmin
exact ⟨x, ⟨hx.1, fun c hac hcx => hcx.not_ge hxmin ⟨hac, hcx.le.trans hx.2⟩ hcx.le⟩, hx.2⟩

Depends on / 依赖: LocallyFiniteOrder, LocallyFiniteOrder.finsetIoc, LocallyFiniteOrder.finset_mem_Ioc, exists_minimal, finsetIoc, finset_mem_Ioc, hcx.le, hcx.le.trans, hcx.not_ge, not_ge
-/
instance : IsStronglyAtomic α where
  exists_covBy_le_of_lt a b hab := by
    obtain ⟨x, hx, hxmin⟩ := (LocallyFiniteOrder.finsetIoc a b).exists_minimal
      ⟨b, by simpa [LocallyFiniteOrder.finset_mem_Ioc]⟩
    simp only [LocallyFiniteOrder.finset_mem_Ioc] at hx hxmin
exact ⟨x, ⟨hx.1, fun c hac hcx => hcx.not_ge hxmin ⟨hac, hcx.le.trans hx.2⟩ hcx.le⟩, hx.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStronglyCoatomic α
  body: by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]; infer_instance

中文:
实例 :
  签名: IsStronglyCoatomic α
  定义体: by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]; infer_instance

Depends on / 依赖: infer_instance, isStronglyAtomic_dual_iff_is_stronglyCoatomic
-/
instance : IsStronglyCoatomic α := by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]; infer_instance

end LocallyFinite

section IsStronglyAtomic

variable [PartialOrder α] {a : α}

/--
theorem `exists_covby_infinite_Ici_of_infinite_Ici` / 定理 `exists_covby_infinite_Ici_of_infinite_Ici`

English:
theorem exists_covby_infinite_Ici_of_infinite_Ici
  statement: [IsStronglyAtomic α]
  proof: by
  by_contra! h
  refine ((hfin.biUnion (t := Set.Ici) (by simpa using h)).subset (fun b hb => ?_)).not_infinite
    (ha.sdiff (Set.finite_singleton a))
  obtain ⟨x, hax, hxb⟩ := ((show a <= b from hb.1).lt_of_ne (Ne.symm hb.2)).exists_covby_le
  exact Set.mem_biUnion hax hxb

中文:
定理 exists_covby_infinite_Ici_of_infinite_Ici
  结论: [IsStronglyAtomic α]
  证明: by
  by_contra! h
  refine ((hfin.biUnion (t := Set.Ici) (by simpa using h)).subset (fun b hb => ?_)).not_infinite
    (ha.sdiff (Set.finite_singleton a))
  obtain ⟨x, hax, hxb⟩ := ((show a <= b from hb.1).lt_of_ne (Ne.symm hb.2)).exists_covby_le
  exact Set.mem_biUnion hax hxb

Depends on / 依赖: Ne.symm, Set.Ici, Set.finite_singleton, Set.mem_biUnion, biUnion, exists_covby_le, finite_singleton, ha.sdiff, hfin.biUnion, lt_of_ne, mem_biUnion, not_infinite, subset
-/
theorem exists_covby_infinite_Ici_of_infinite_Ici [IsStronglyAtomic α]
    (ha : (Set.Ici a).Infinite) (hfin : {x | a ⋖ x}.Finite) :
    exists b, a ⋖ b ∧ (Set.Ici b).Infinite := by
  by_contra! h
  refine ((hfin.biUnion (t := Set.Ici) (by simpa using h)).subset (fun b hb => ?_)).not_infinite
    (ha.sdiff (Set.finite_singleton a))
  obtain ⟨x, hax, hxb⟩ := ((show a <= b from hb.1).lt_of_ne (Ne.symm hb.2)).exists_covby_le
  exact Set.mem_biUnion hax hxb

/--
theorem `exists_covby_infinite_Iic_of_infinite_Iic` / 定理 `exists_covby_infinite_Iic_of_infinite_Iic`

English:
theorem exists_covby_infinite_Iic_of_infinite_Iic
  statement: [IsStronglyCoatomic α]
  proof: by
  simp_rw [← toDual_covBy_toDual_iff (α := α)] at hfin ⊢
  exact exists_covby_infinite_Ici_of_infinite_Ici (α := αᵒᵈ) ha hfin

中文:
定理 exists_covby_infinite_Iic_of_infinite_Iic
  结论: [IsStronglyCoatomic α]
  证明: by
  simp_rw [← toDual_covBy_toDual_iff (α := α)] at hfin ⊢
  exact exists_covby_infinite_Ici_of_infinite_Ici (α := αᵒᵈ) ha hfin

Depends on / 依赖: exists_covby_infinite_Ici_of_infinite_Ici, simp_rw, toDual_covBy_toDual_iff
-/
theorem exists_covby_infinite_Iic_of_infinite_Iic [IsStronglyCoatomic α]
    (ha : (Set.Iic a).Infinite) (hfin : {x | x ⋖ a}.Finite) :
    exists b, b ⋖ a ∧ (Set.Iic b).Infinite := by
  simp_rw [← toDual_covBy_toDual_iff (α := α)] at hfin ⊢
  exact exists_covby_infinite_Ici_of_infinite_Ici (α := αᵒᵈ) ha hfin

end IsStronglyAtomic
