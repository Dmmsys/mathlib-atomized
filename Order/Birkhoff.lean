/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Filippo A. E. Nuccio, Sam van Gool
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Irreducible
public import Mathlib.Order.UpperLower.Closure

/-!
# Birkhoff representation

This file proves two facts which together are commonly referred to as "Birkhoff representation":
1. Any nonempty finite partial order is isomorphic to the partial order of sup-irreducible elements
  in its lattice of lower sets.
2. Any nonempty finite distributive lattice is isomorphic to the lattice of lower sets of its
  partial order of sup-irreducible elements.

## Main declarations

For a finite nonempty partial order `α`:
* `OrderEmbedding.supIrredLowerSet`: `α` is isomorphic to the order of its irreducible lower sets.

If `α` is moreover a distributive lattice:
* `OrderIso.lowerSetSupIrred`: `α` is isomorphic to the lattice of lower sets of its irreducible
  elements.
* `OrderEmbedding.birkhoffSet`, `OrderEmbedding.birkhoffFinset`: Order embedding of `α` into the
  powerset lattice of its irreducible elements.
* `LatticeHom.birkhoffSet`, `LatticeHom.birkhoffFinset`: Same as the previous two, but bundled as
  an injective lattice homomorphism.
* `exists_birkhoff_representation`: `α` embeds into some powerset algebra. You should prefer using
  this over the explicit Birkhoff embedding because the Birkhoff embedding is littered with
  decidability footguns that this existential-packaged version can afford to avoid.

## See also

These results form the object part of finite Stone duality: the functorial contravariant
equivalence between the category of finite distributive lattices and the category of finite
partial orders. TODO: extend to morphisms.

## References

* [G. Birkhoff, *Rings of sets*][birkhoff1937]

## Tags

birkhoff, representation, stone duality, lattice embedding
-/

@[expose] public section

open Finset Function OrderDual UpperSet LowerSet

variable {α : Type*}

section PartialOrder
variable [PartialOrder α]

namespace UpperSet
variable {s : UpperSet α}

/--
lemma `infIrred_Ici` / 引理 `infIrred_Ici`

English:
lemma infIrred_Ici
  given: (a : α)
  statement: InfIrred (Ici a)
  proof: by
  refine ⟨fun h => Ici_ne_top h.eq_top, fun s t hst => ?_⟩
  have := mem_Ici_iff.2 (le_refl a)
  rw [← hst] at this
  exact this.imp (fun ha => le_antisymm (le_Ici.2 ha) <| hst.ge.trans inf_le_left) fun ha =>
le_antisymm (le_Ici.2 ha) hst.ge.trans inf_le_right

中文:
引理 infIrred_Ici
  条件: (a : α)
  结论: InfIrred (左闭右无界区间 a)
  证明: by
  refine ⟨fun h => Ici_ne_top h.eq_top, fun s t hst => ?_⟩
  have := mem_Ici_iff.2 (le_refl a)
  rw [← hst] at this
  exact this.imp (fun ha => le_antisymm (le_Ici.2 ha) <| hst.ge.trans inf_le_left) fun ha =>
le_antisymm (le_Ici.2 ha) hst.ge.trans inf_le_right
-/
@[simp] lemma infIrred_Ici (a : α) : InfIrred (Ici a) := by
  refine ⟨fun h => Ici_ne_top h.eq_top, fun s t hst => ?_⟩
  have := mem_Ici_iff.2 (le_refl a)
  rw [← hst] at this
  exact this.imp (fun ha => le_antisymm (le_Ici.2 ha) <| hst.ge.trans inf_le_left) fun ha =>
le_antisymm (le_Ici.2 ha) hst.ge.trans inf_le_right

variable [Finite α]

/--
lemma `infIrred_iff_of_finite` / 引理 `infIrred_iff_of_finite`

English:
lemma infIrred_iff_of_finite
  statement: InfIrred s ↔ exists a, Ici a = s
  proof: by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨a, ha, has⟩ := (s : Set α).toFinite.exists_minimal (coe_nonempty.2 hs.ne_top)
    exact ⟨a, (hs.2 <| erase_inf_Ici ha fun b hb => le_imp_eq_iff_le_imp_ge.2 <| has hb).resolve_left
      (lt_erase.2 ha).ne'⟩
  · rintro ⟨a, rfl⟩
    exact infIrred_Ici _

中文:
引理 infIrred_iff_of_finite
  结论: InfIrred s ↔ 存在 a, 左闭右无界区间 a = s
  证明: by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨a, ha, has⟩ := (s : Set α).toFinite.exists_minimal (coe_nonempty.2 hs.ne_top)
    exact ⟨a, (hs.2 <| erase_inf_Ici ha fun b hb => le_imp_eq_iff_le_imp_ge.2 <| has hb).resolve_left
      (lt_erase.2 ha).ne'⟩
  · rintro ⟨a, rfl⟩
    exact infIrred_Ici _
-/
@[simp] lemma infIrred_iff_of_finite : InfIrred s ↔ exists a, Ici a = s := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨a, ha, has⟩ := (s : Set α).toFinite.exists_minimal (coe_nonempty.2 hs.ne_top)
    exact ⟨a, (hs.2 <| erase_inf_Ici ha fun b hb => le_imp_eq_iff_le_imp_ge.2 <| has hb).resolve_left
      (lt_erase.2 ha).ne'⟩
  · rintro ⟨a, rfl⟩
    exact infIrred_Ici _

end UpperSet

namespace LowerSet
variable {s : LowerSet α}

/--
lemma `supIrred_Iic` / 引理 `supIrred_Iic`

English:
lemma supIrred_Iic
  given: (a : α)
  statement: SupIrred (Iic a)
  proof: by
  refine ⟨fun h => Iic_ne_bot h.eq_bot, fun s t hst => ?_⟩
  have := mem_Iic_iff.2 (le_refl a)
  rw [← hst] at this
  exact this.imp (fun ha => (le_sup_left.trans_eq hst).antisymm <| Iic_le.2 ha) fun ha =>
(le_sup_right.trans_eq hst).antisymm Iic_le.2 ha

中文:
引理 supIrred_Iic
  条件: (a : α)
  结论: SupIrred (左无界右闭区间 a)
  证明: by
  refine ⟨fun h => Iic_ne_bot h.eq_bot, fun s t hst => ?_⟩
  have := mem_Iic_iff.2 (le_refl a)
  rw [← hst] at this
  exact this.imp (fun ha => (le_sup_left.trans_eq hst).antisymm <| Iic_le.2 ha) fun ha =>
(le_sup_right.trans_eq hst).antisymm Iic_le.2 ha
-/
@[simp] lemma supIrred_Iic (a : α) : SupIrred (Iic a) := by
  refine ⟨fun h => Iic_ne_bot h.eq_bot, fun s t hst => ?_⟩
  have := mem_Iic_iff.2 (le_refl a)
  rw [← hst] at this
  exact this.imp (fun ha => (le_sup_left.trans_eq hst).antisymm <| Iic_le.2 ha) fun ha =>
(le_sup_right.trans_eq hst).antisymm Iic_le.2 ha

variable [Finite α]

/--
lemma `supIrred_iff_of_finite` / 引理 `supIrred_iff_of_finite`

English:
lemma supIrred_iff_of_finite
  statement: SupIrred s ↔ exists a, Iic a = s
  proof: by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨a, ha, has⟩ := (s : Set α).toFinite.exists_maximal (coe_nonempty.2 hs.ne_bot)
    exact ⟨a, (hs.2 <| erase_sup_Iic ha fun b hb =>
le_imp_eq_iff_le_imp_ge'.2 has hb).resolve_left (erase_lt.2 ha).ne⟩
  · rintro ⟨a, rfl⟩
    exact supIrred_Iic _

中文:
引理 supIrred_iff_of_finite
  结论: SupIrred s ↔ 存在 a, 左无界右闭区间 a = s
  证明: by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨a, ha, has⟩ := (s : Set α).toFinite.exists_maximal (coe_nonempty.2 hs.ne_bot)
    exact ⟨a, (hs.2 <| erase_sup_Iic ha fun b hb =>
le_imp_eq_iff_le_imp_ge'.2 has hb).resolve_left (erase_lt.2 ha).ne⟩
  · rintro ⟨a, rfl⟩
    exact supIrred_Iic _
-/
@[simp] lemma supIrred_iff_of_finite : SupIrred s ↔ exists a, Iic a = s := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨a, ha, has⟩ := (s : Set α).toFinite.exists_maximal (coe_nonempty.2 hs.ne_bot)
    exact ⟨a, (hs.2 <| erase_sup_Iic ha fun b hb =>
le_imp_eq_iff_le_imp_ge'.2 has hb).resolve_left (erase_lt.2 ha).ne⟩
  · rintro ⟨a, rfl⟩
    exact supIrred_Iic _

end LowerSet

namespace OrderEmbedding

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `supIrredLowerSet` / `supIrredLowerSet` 的定义

English:
definition supIrredLowerSet
  signature: : α ↪o {s : LowerSet α // SupIrred s} where
  body: ⟨Iic a, supIrred_Iic _⟩
  inj' _ := by simp
  map_rel_iff' := by simp

中文:
定义 supIrredLowerSet
  签名: : α ↪o {s : 下集 α // SupIrred s} where
  定义体: ⟨Iic a, supIrred_Iic _⟩
  inj' _ := by simp
  map_rel_iff' := by simp

Depends on / 依赖: supIrred_Iic
-/
def supIrredLowerSet : α ↪o {s : LowerSet α // SupIrred s} where
  toFun a := ⟨Iic a, supIrred_Iic _⟩
  inj' _ := by simp
  map_rel_iff' := by simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `infIrredUpperSet` / `infIrredUpperSet` 的定义

English:
definition infIrredUpperSet
  signature: : α ↪o {s : UpperSet α // InfIrred s} where
  body: ⟨Ici a, infIrred_Ici _⟩
  inj' _ := by simp
  map_rel_iff' := by simp

中文:
定义 infIrredUpperSet
  签名: : α ↪o {s : 上集 α // InfIrred s} where
  定义体: ⟨Ici a, infIrred_Ici _⟩
  inj' _ := by simp
  map_rel_iff' := by simp

Depends on / 依赖: infIrred_Ici
-/
def infIrredUpperSet : α ↪o {s : UpperSet α // InfIrred s} where
  toFun a := ⟨Ici a, infIrred_Ici _⟩
  inj' _ := by simp
  map_rel_iff' := by simp

/--
lemma `supIrredLowerSet_apply` / 引理 `supIrredLowerSet_apply`

English:
lemma supIrredLowerSet_apply
  given: (a : α)
  statement: supIrredLowerSet a = ⟨Iic a, supIrred_Iic _⟩
  proof: rfl

中文:
引理 supIrredLowerSet_apply
  条件: (a : α)
  结论: supIrredLowerSet a = ⟨左无界右闭区间 a, supIrred_Iic _⟩
  证明: rfl
-/
@[simp] lemma supIrredLowerSet_apply (a : α) : supIrredLowerSet a = ⟨Iic a, supIrred_Iic _⟩ := rfl
/--
lemma `infIrredUpperSet_apply` / 引理 `infIrredUpperSet_apply`

English:
lemma infIrredUpperSet_apply
  given: (a : α)
  statement: infIrredUpperSet a = ⟨Ici a, infIrred_Ici _⟩
  proof: rfl

中文:
引理 infIrredUpperSet_apply
  条件: (a : α)
  结论: infIrredUpperSet a = ⟨左闭右无界区间 a, infIrred_Ici _⟩
  证明: rfl
-/
@[simp] lemma infIrredUpperSet_apply (a : α) : infIrredUpperSet a = ⟨Ici a, infIrred_Ici _⟩ := rfl

variable [Finite α]

/--
lemma `supIrredLowerSet_surjective` / 引理 `supIrredLowerSet_surjective`

English:
lemma supIrredLowerSet_surjective
  statement: Surjective (supIrredLowerSet (α := α))
  proof: by
  aesop (add simp Surjective)

中文:
引理 supIrredLowerSet_surjective
  结论: 满射 (supIrredLowerSet (α := α))
  证明: by
  aesop (add simp Surjective)

Depends on / 依赖: Surjective
-/
lemma supIrredLowerSet_surjective : Surjective (supIrredLowerSet (α := α)) := by
  aesop (add simp Surjective)

/--
lemma `infIrredUpperSet_surjective` / 引理 `infIrredUpperSet_surjective`

English:
lemma infIrredUpperSet_surjective
  statement: Surjective (infIrredUpperSet (α := α))
  proof: by
  aesop (add simp Surjective)

中文:
引理 infIrredUpperSet_surjective
  结论: 满射 (infIrredUpperSet (α := α))
  证明: by
  aesop (add simp Surjective)

Depends on / 依赖: Surjective
-/
lemma infIrredUpperSet_surjective : Surjective (infIrredUpperSet (α := α)) := by
  aesop (add simp Surjective)

end OrderEmbedding

namespace OrderIso
variable [Finite α]

/--
Definition of `supIrredLowerSet` / `supIrredLowerSet` 的定义

English:
definition supIrredLowerSet
  signature: : α ≃o {s : LowerSet α // SupIrred s}
  body: RelIso.ofSurjective _ OrderEmbedding.supIrredLowerSet_surjective

中文:
定义 supIrredLowerSet
  签名: : α ≃o {s : 下集 α // SupIrred s}
  定义体: RelIso.ofSurjective _ OrderEmbedding.supIrredLowerSet_surjective

Depends on / 依赖: OrderEmbedding, OrderEmbedding.supIrredLowerSet_surjective, RelIso, RelIso.ofSurjective, ofSurjective, supIrredLowerSet_surjective
-/
noncomputable def supIrredLowerSet : α ≃o {s : LowerSet α // SupIrred s} :=
  RelIso.ofSurjective _ OrderEmbedding.supIrredLowerSet_surjective

/--
Definition of `infIrredUpperSet` / `infIrredUpperSet` 的定义

English:
definition infIrredUpperSet
  signature: : α ≃o {s : UpperSet α // InfIrred s}
  body: RelIso.ofSurjective _ OrderEmbedding.infIrredUpperSet_surjective

中文:
定义 infIrredUpperSet
  签名: : α ≃o {s : 上集 α // InfIrred s}
  定义体: RelIso.ofSurjective _ OrderEmbedding.infIrredUpperSet_surjective

Depends on / 依赖: OrderEmbedding, OrderEmbedding.infIrredUpperSet_surjective, RelIso, RelIso.ofSurjective, infIrredUpperSet_surjective, ofSurjective
-/
noncomputable def infIrredUpperSet : α ≃o {s : UpperSet α // InfIrred s} :=
  RelIso.ofSurjective _ OrderEmbedding.infIrredUpperSet_surjective

/--
lemma `supIrredLowerSet_apply` / 引理 `supIrredLowerSet_apply`

English:
lemma supIrredLowerSet_apply
  given: (a : α)
  statement: supIrredLowerSet a = ⟨Iic a, supIrred_Iic _⟩
  proof: rfl

中文:
引理 supIrredLowerSet_apply
  条件: (a : α)
  结论: supIrredLowerSet a = ⟨左无界右闭区间 a, supIrred_Iic _⟩
  证明: rfl
-/
@[simp] lemma supIrredLowerSet_apply (a : α) : supIrredLowerSet a = ⟨Iic a, supIrred_Iic _⟩ := rfl
/--
lemma `infIrredUpperSet_apply` / 引理 `infIrredUpperSet_apply`

English:
lemma infIrredUpperSet_apply
  given: (a : α)
  statement: infIrredUpperSet a = ⟨Ici a, infIrred_Ici _⟩
  proof: rfl

中文:
引理 infIrredUpperSet_apply
  条件: (a : α)
  结论: infIrredUpperSet a = ⟨左闭右无界区间 a, infIrred_Ici _⟩
  证明: rfl
-/
@[simp] lemma infIrredUpperSet_apply (a : α) : infIrredUpperSet a = ⟨Ici a, infIrred_Ici _⟩ := rfl

end OrderIso
end PartialOrder

namespace OrderIso
section SemilatticeSup
variable [SemilatticeSup α] [OrderBot α] [Finite α]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `supIrredLowerSet_symm_apply` / 引理 `supIrredLowerSet_symm_apply`

English:
lemma supIrredLowerSet_symm_apply
  given: (s : {s : LowerSet α // SupIrred s}) [Fintype s]
  proof: by
  classical
  obtain ⟨s, hs⟩ := s
  obtain ⟨a, rfl⟩ := supIrred_iff_of_finite.1 hs
  cases nonempty_fintype α
  have : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  simp [symm_apply_eq]

中文:
引理 supIrredLowerSet_symm_apply
  条件: (s : {s : 下集 α // SupIrred s}) [有限类型 s]
  证明: by
  classical
  obtain ⟨s, hs⟩ := s
  obtain ⟨a, rfl⟩ := supIrred_iff_of_finite.1 hs
  cases nonempty_fintype α
  have : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  simp [symm_apply_eq]
-/
@[simp] lemma supIrredLowerSet_symm_apply (s : {s : LowerSet α // SupIrred s}) [Fintype s] :
    supIrredLowerSet.symm s = (s.1 : Set α).toFinset.sup id := by
  classical
  obtain ⟨s, hs⟩ := s
  obtain ⟨a, rfl⟩ := supIrred_iff_of_finite.1 hs
  cases nonempty_fintype α
  have : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  simp [symm_apply_eq]

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [OrderTop α] [Finite α]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `infIrredUpperSet_symm_apply` / 引理 `infIrredUpperSet_symm_apply`

English:
lemma infIrredUpperSet_symm_apply
  given: (s : {s : UpperSet α // InfIrred s}) [Fintype s]
  proof: by
  classical
  obtain ⟨s, hs⟩ := s
  obtain ⟨a, rfl⟩ := infIrred_iff_of_finite.1 hs
  cases nonempty_fintype α
  have : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  simp [symm_apply_eq]

中文:
引理 infIrredUpperSet_symm_apply
  条件: (s : {s : 上集 α // InfIrred s}) [有限类型 s]
  证明: by
  classical
  obtain ⟨s, hs⟩ := s
  obtain ⟨a, rfl⟩ := infIrred_iff_of_finite.1 hs
  cases nonempty_fintype α
  have : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  simp [symm_apply_eq]
-/
@[simp] lemma infIrredUpperSet_symm_apply (s : {s : UpperSet α // InfIrred s}) [Fintype s] :
    infIrredUpperSet.symm s = (s.1 : Set α).toFinset.inf id := by
  classical
  obtain ⟨s, hs⟩ := s
  obtain ⟨a, rfl⟩ := infIrred_iff_of_finite.1 hs
  cases nonempty_fintype α
  have : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  simp [symm_apply_eq]

end SemilatticeInf
end OrderIso

section DistribLattice
variable [DistribLattice α] [Fintype α] [@DecidablePred α SupIrred]

open scoped Classical in
/--
Definition of `OrderIso.lowerSetSupIrred` / `OrderIso.lowerSetSupIrred` 的定义

English:
definition OrderIso.lowerSetSupIrred
  signature: [OrderBot α]
  body: Equiv.toOrderIso
    { toFun := fun a => ⟨{b | ↑b <= a}, fun _ _ hcb hba => hba.trans' hcb⟩
      invFun := fun s => (s : Set {a : α // SupIrred a}).toFinset.sup (↑)
      left_inv := fun a => by
        refine le_antisymm (Finset.sup_le fun b => Set.mem_toFinset.1) ?_
        obtain ⟨s, rfl, hs⟩ := exists_supIrred_decomposition a
        exact Finset.sup_le fun i hi =>
          le_sup_of_le (b := ⟨i, hs hi⟩) (Set.mem_toFinset.2 <| le_sup (f := id) hi) le_rfl
      right_inv := fun s => by
        ext a
        dsimp
        refine ⟨fun ha => ?_, fun ha => ?_⟩
        · obtain ⟨i, hi, ha⟩ := a.2.supPrime.le_finset_sup.1 ha
          exact s.lower ha (Set.mem_toFinset.1 hi)
        · exact le_sup (Set.mem_toFinset.2 ha) }
(fun _ _ hbc _ => le_trans' hbc) fun _ _ hst => Finset.sup_mono Set.toFinset_mono hst

中文:
定义 OrderIso.lowerSetSupIrred
  签名: [有底序 α]
  定义体: Equiv.toOrderIso
    { toFun := fun a => ⟨{b | ↑b <= a}, fun _ _ hcb hba => hba.trans' hcb⟩
      invFun := fun s => (s : Set {a : α // SupIrred a}).toFinset.sup (↑)
      left_inv := fun a => by
        refine le_antisymm (Finset.sup_le fun b => Set.mem_toFinset.1) ?_
        obtain ⟨s, rfl, hs⟩ := exists_supIrred_decomposition a
        exact Finset.sup_le fun i hi =>
          le_sup_of_le (b := ⟨i, hs hi⟩) (Set.mem_toFinset.2 <| le_sup (f := id) hi) le_rfl
      right_inv := fun s => by
        ext a
        dsimp
        refine ⟨fun ha => ?_, fun ha => ?_⟩
        · obtain ⟨i, hi, ha⟩ := a.2.supPrime.le_finset_sup.1 ha
          exact s.lower ha (Set.mem_toFinset.1 hi)
        · exact le_sup (Set.mem_toFinset.2 ha) }
(fun _ _ hbc _ => le_trans' hbc) fun _ _ hst => Finset.sup_mono Set.toFinset_mono hst

Depends on / 依赖: Equiv.toOrderIso, Finset, Finset.sup_le, Set.mem_toFinset, SupIrred, exists_supIrred_decomposition, hba.trans, invFun, le_antisymm, le_rfl, le_sup, le_sup_of_le, left_inv, mem_toFinset, right_inv, sup_le, toFinset, toFinset.sup, toOrderIso
-/
noncomputable def OrderIso.lowerSetSupIrred [OrderBot α] : α ≃o LowerSet {a : α // SupIrred a} :=
  Equiv.toOrderIso
    { toFun := fun a => ⟨{b | ↑b <= a}, fun _ _ hcb hba => hba.trans' hcb⟩
      invFun := fun s => (s : Set {a : α // SupIrred a}).toFinset.sup (↑)
      left_inv := fun a => by
        refine le_antisymm (Finset.sup_le fun b => Set.mem_toFinset.1) ?_
        obtain ⟨s, rfl, hs⟩ := exists_supIrred_decomposition a
        exact Finset.sup_le fun i hi =>
          le_sup_of_le (b := ⟨i, hs hi⟩) (Set.mem_toFinset.2 <| le_sup (f := id) hi) le_rfl
      right_inv := fun s => by
        ext a
        dsimp
        refine ⟨fun ha => ?_, fun ha => ?_⟩
        · obtain ⟨i, hi, ha⟩ := a.2.supPrime.le_finset_sup.1 ha
          exact s.lower ha (Set.mem_toFinset.1 hi)
        · exact le_sup (Set.mem_toFinset.2 ha) }
(fun _ _ hbc _ => le_trans' hbc) fun _ _ hst => Finset.sup_mono Set.toFinset_mono hst

namespace OrderEmbedding

/--
Definition of `birkhoffSet` / `birkhoffSet` 的定义

English:
definition birkhoffSet
  signature: : α ↪o Set {a : α // SupIrred a}
  body: by
  by_cases! h : IsEmpty α
  · exact OrderEmbedding.ofIsEmpty
  have := Fintype.toOrderBot α
  exact OrderIso.lowerSetSupIrred.toOrderEmbedding.trans ⟨⟨_, SetLike.coe_injective⟩, Iff.rfl⟩

中文:
定义 birkhoffSet
  签名: : α ↪o 集合 {a : α // SupIrred a}
  定义体: by
  by_cases! h : IsEmpty α
  · exact OrderEmbedding.ofIsEmpty
  have := Fintype.toOrderBot α
  exact OrderIso.lowerSetSupIrred.toOrderEmbedding.trans ⟨⟨_, SetLike.coe_injective⟩, Iff.rfl⟩

Depends on / 依赖: Fintype, Fintype.toOrderBot, Iff.rfl, IsEmpty, OrderEmbedding, OrderEmbedding.ofIsEmpty, OrderIso, OrderIso.lowerSetSupIrred.toOrderEmbedding.trans, SetLike, SetLike.coe_injective, coe_injective, lowerSetSupIrred, ofIsEmpty, toOrderBot, toOrderEmbedding
-/
noncomputable def birkhoffSet : α ↪o Set {a : α // SupIrred a} := by
  by_cases! h : IsEmpty α
  · exact OrderEmbedding.ofIsEmpty
  have := Fintype.toOrderBot α
  exact OrderIso.lowerSetSupIrred.toOrderEmbedding.trans ⟨⟨_, SetLike.coe_injective⟩, Iff.rfl⟩

/--
Definition of `birkhoffFinset` / `birkhoffFinset` 的定义

English:
definition birkhoffFinset
  signature: : α ↪o Finset {a : α // SupIrred a}
  body: by
  exact birkhoffSet.trans Fintype.finsetOrderIsoSet.symm.toOrderEmbedding

中文:
定义 birkhoffFinset
  签名: : α ↪o 有限集 {a : α // SupIrred a}
  定义体: by
  exact birkhoffSet.trans Fintype.finsetOrderIsoSet.symm.toOrderEmbedding

Depends on / 依赖: Fintype, Fintype.finsetOrderIsoSet.symm.toOrderEmbedding, birkhoffSet, birkhoffSet.trans, finsetOrderIsoSet, toOrderEmbedding
-/
noncomputable def birkhoffFinset : α ↪o Finset {a : α // SupIrred a} := by
  exact birkhoffSet.trans Fintype.finsetOrderIsoSet.symm.toOrderEmbedding

/--
lemma `coe_birkhoffFinset` / 引理 `coe_birkhoffFinset`

English:
lemma coe_birkhoffFinset
  given: (a : α)
  statement: birkhoffFinset a = birkhoffSet a
  proof: by
  classical
  -- TODO: This should be a single `simp` call but `simp` refuses to use
  -- `OrderIso.coe_toOrderEmbedding` and `Fintype.coe_finsetOrderIsoSet_symm`
  simp [birkhoffFinset, (OrderIso.coe_toOrderEmbedding)]

中文:
引理 coe_birkhoffFinset
  条件: (a : α)
  结论: birkhoffFinset a = birkhoffSet a
  证明: by
  classical
  -- TODO: This should be a single `simp` call but `simp` refuses to use
  -- `OrderIso.coe_toOrderEmbedding` and `Fintype.coe_finsetOrderIsoSet_symm`
  simp [birkhoffFinset, (OrderIso.coe_toOrderEmbedding)]
-/
@[simp] lemma coe_birkhoffFinset (a : α) : birkhoffFinset a = birkhoffSet a := by
  classical
  -- TODO: This should be a single `simp` call but `simp` refuses to use
  -- `OrderIso.coe_toOrderEmbedding` and `Fintype.coe_finsetOrderIsoSet_symm`
  simp [birkhoffFinset, (OrderIso.coe_toOrderEmbedding)]

/--
lemma `birkhoffSet_sup` / 引理 `birkhoffSet_sup`

English:
lemma birkhoffSet_sup
  given: (a b : α)
  statement: birkhoffSet (a ⊔ b) = birkhoffSet a union birkhoffSet b
  proof: by
  unfold OrderEmbedding.birkhoffSet; split <;> simp [eq_iff_true_of_subsingleton]

中文:
引理 birkhoffSet_sup
  条件: (a b : α)
  结论: birkhoffSet (a ⊔ b) = birkhoffSet a union birkhoffSet b
  证明: by
  unfold OrderEmbedding.birkhoffSet; split <;> simp [eq_iff_true_of_subsingleton]
-/
@[simp] lemma birkhoffSet_sup (a b : α) : birkhoffSet (a ⊔ b) = birkhoffSet a union birkhoffSet b := by
  unfold OrderEmbedding.birkhoffSet; split <;> simp [eq_iff_true_of_subsingleton]

/--
lemma `birkhoffSet_inf` / 引理 `birkhoffSet_inf`

English:
lemma birkhoffSet_inf
  given: (a b : α)
  statement: birkhoffSet (a ⊓ b) = birkhoffSet a inter birkhoffSet b
  proof: by
  unfold OrderEmbedding.birkhoffSet; split <;> simp [eq_iff_true_of_subsingleton]

中文:
引理 birkhoffSet_inf
  条件: (a b : α)
  结论: birkhoffSet (a ⊓ b) = birkhoffSet a inter birkhoffSet b
  证明: by
  unfold OrderEmbedding.birkhoffSet; split <;> simp [eq_iff_true_of_subsingleton]
-/
@[simp] lemma birkhoffSet_inf (a b : α) : birkhoffSet (a ⊓ b) = birkhoffSet a inter birkhoffSet b := by
  unfold OrderEmbedding.birkhoffSet; split <;> simp [eq_iff_true_of_subsingleton]

/--
lemma `birkhoffSet_apply` / 引理 `birkhoffSet_apply`

English:
lemma birkhoffSet_apply
  given: [OrderBot α] (a : α)
  proof: by
  have : Subsingleton (OrderBot α) := inferInstance
  simp +instances [birkhoffSet, this.allEq]

中文:
引理 birkhoffSet_apply
  条件: [有底序 α] (a : α)
  证明: by
  have : Subsingleton (OrderBot α) := inferInstance
  simp +instances [birkhoffSet, this.allEq]
-/
@[simp] lemma birkhoffSet_apply [OrderBot α] (a : α) :
    birkhoffSet a = OrderIso.lowerSetSupIrred a := by
  have : Subsingleton (OrderBot α) := inferInstance
  simp +instances [birkhoffSet, this.allEq]

variable [DecidableEq α]

/--
lemma `birkhoffFinset_sup` / 引理 `birkhoffFinset_sup`

English:
lemma birkhoffFinset_sup
  given: (a b : α)
  proof: by
  classical
  dsimp [OrderEmbedding.birkhoffFinset]
  simp [birkhoffSet_sup]

中文:
引理 birkhoffFinset_sup
  条件: (a b : α)
  证明: by
  classical
  dsimp [OrderEmbedding.birkhoffFinset]
  simp [birkhoffSet_sup]
-/
@[simp] lemma birkhoffFinset_sup (a b : α) :
    birkhoffFinset (a ⊔ b) = birkhoffFinset a union birkhoffFinset b := by
  classical
  dsimp [OrderEmbedding.birkhoffFinset]
  simp [birkhoffSet_sup]

/--
lemma `birkhoffFinset_inf` / 引理 `birkhoffFinset_inf`

English:
lemma birkhoffFinset_inf
  given: (a b : α)
  proof: by
  classical
  dsimp [OrderEmbedding.birkhoffFinset]
  simp [birkhoffSet_inf]

中文:
引理 birkhoffFinset_inf
  条件: (a b : α)
  证明: by
  classical
  dsimp [OrderEmbedding.birkhoffFinset]
  simp [birkhoffSet_inf]
-/
@[simp] lemma birkhoffFinset_inf (a b : α) :
    birkhoffFinset (a ⊓ b) = birkhoffFinset a inter birkhoffFinset b := by
  classical
  dsimp [OrderEmbedding.birkhoffFinset]
  simp [birkhoffSet_inf]

end OrderEmbedding

namespace LatticeHom

/--
Definition of `birkhoffSet` / `birkhoffSet` 的定义

English:
definition birkhoffSet
  signature: : LatticeHom α (Set {a : α // SupIrred a}) where
  body: OrderEmbedding.birkhoffSet
  map_sup' := OrderEmbedding.birkhoffSet_sup
  map_inf' := OrderEmbedding.birkhoffSet_inf

中文:
定义 birkhoffSet
  签名: : 格态射 α (集合 {a : α // SupIrred a}) where
  定义体: OrderEmbedding.birkhoffSet
  map_sup' := OrderEmbedding.birkhoffSet_sup
  map_inf' := OrderEmbedding.birkhoffSet_inf

Depends on / 依赖: OrderEmbedding, OrderEmbedding.birkhoffSet, birkhoffSet
-/
noncomputable def birkhoffSet : LatticeHom α (Set {a : α // SupIrred a}) where
  toFun := OrderEmbedding.birkhoffSet
  map_sup' := OrderEmbedding.birkhoffSet_sup
  map_inf' := OrderEmbedding.birkhoffSet_inf

open scoped Classical in
/--
Definition of `birkhoffFinset` / `birkhoffFinset` 的定义

English:
definition birkhoffFinset
  signature: : LatticeHom α (Finset {a : α // SupIrred a}) where
  body: OrderEmbedding.birkhoffFinset
  map_sup' := OrderEmbedding.birkhoffFinset_sup
  map_inf' := OrderEmbedding.birkhoffFinset_inf

中文:
定义 birkhoffFinset
  签名: : 格态射 α (有限集 {a : α // SupIrred a}) where
  定义体: OrderEmbedding.birkhoffFinset
  map_sup' := OrderEmbedding.birkhoffFinset_sup
  map_inf' := OrderEmbedding.birkhoffFinset_inf

Depends on / 依赖: OrderEmbedding, OrderEmbedding.birkhoffFinset, birkhoffFinset
-/
noncomputable def birkhoffFinset : LatticeHom α (Finset {a : α // SupIrred a}) where
  toFun := OrderEmbedding.birkhoffFinset
  map_sup' := OrderEmbedding.birkhoffFinset_sup
  map_inf' := OrderEmbedding.birkhoffFinset_inf

/--
lemma `birkhoffFinset_injective` / 引理 `birkhoffFinset_injective`

English:
lemma birkhoffFinset_injective
  statement: Injective (birkhoffFinset (α := α))
  proof: OrderEmbedding.birkhoffFinset.injective

中文:
引理 birkhoffFinset_injective
  结论: 单射 (birkhoffFinset (α := α))
  证明: OrderEmbedding.birkhoffFinset.injective
-/
lemma birkhoffFinset_injective : Injective (birkhoffFinset (α := α)) :=
  OrderEmbedding.birkhoffFinset.injective

end LatticeHom

/--
lemma `exists_birkhoff_representation.` / 引理 `exists_birkhoff_representation.`

English:
lemma exists_birkhoff_representation.{u}
  given: (α : Type u) [Finite α] [DistribLattice α]
  proof: by
  classical
  cases nonempty_fintype α
  exact ⟨{a : α // SupIrred a}, _, inferInstance, _, LatticeHom.birkhoffFinset_injective⟩

中文:
引理 存在_birkhoff_representation.{u}
  条件: (α : 类型u) [有限 α] [Distrib格 α]
  证明: by
  classical
  cases nonempty_fintype α
  exact ⟨{a : α // SupIrred a}, _, inferInstance, _, LatticeHom.birkhoffFinset_injective⟩

Depends on / 依赖: LatticeHom, LatticeHom.birkhoffFinset_injective, SupIrred, birkhoffFinset_injective, classical, nonempty_fintype
-/
lemma exists_birkhoff_representation.{u} (α : Type u) [Finite α] [DistribLattice α] :
    exists (β : Type u) (_ : DecidableEq β) (_ : Fintype β) (f : LatticeHom α (Finset β)),
      Injective f := by
  classical
  cases nonempty_fintype α
  exact ⟨{a : α // SupIrred a}, _, inferInstance, _, LatticeHom.birkhoffFinset_injective⟩

end DistribLattice
