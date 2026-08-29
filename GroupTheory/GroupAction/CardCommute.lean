/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Properties of group actions involving quotient groups

This file proves cardinality properties of group actions which use the quotient group construction,
notably
* the class formula `MulAction.card_eq_sum_card_group_div_card_stabilizer'`
* `card_comm_eq_card_conjClasses_mul_card`

as well as their analogues for additive groups.

See `Mathlib/GroupTheory/GroupAction/Quotient.lean` for the construction of isomorphisms used to
prove these cardinality properties.
These lemmas are separate because they require the development of cardinals.
-/

public section

variable {α β : Type*}

open Function

namespace MulAction

variable (α β)
variable [Group α] [MulAction α β]

local notation "Ω" => Quotient orbitRel α β

/-- **Class formula** for a finite group acting on a finite type. See
`MulAction.card_eq_sum_card_group_div_card_stabilizer` for a specialized version using
`Quotient.out`. -/
@[to_additive
      /-- **Class formula** for a finite group acting on a finite type. See
      `AddAction.card_eq_sum_card_addGroup_div_card_stabilizer` for a specialized version using
      `Quotient.out`. -/]
/--
theorem `card_eq_sum_card_group_div_card_stabilizer'` / 定理 `card_eq_sum_card_group_div_card_stabilizer'`

English:
theorem card_eq_sum_card_group_div_card_stabilizer'
  statement: [Fintype α] [Fintype β] [Fintype Ω]
  proof: by
  classical
    have : forall ω : Ω, Fintype.card α / Fintype.card (stabilizer α (φ ω)) =
        Fintype.card (α ⧸ stabilizer α (φ ω)) := by
      intro ω
      rw [Fintype.card_congr (@Subgroup.groupEquivQuotientProdSubgroup α _ (stabilizer α <| φ ω))]; rw [Fintype.card_prod]; rw [Nat.mul_div_cancel]
      exact Fintype.card_pos_iff.mpr (by infer_instance)
    simp_rw [this, ← Fintype.card_sigma,
      Fintype.card_congr (selfEquivSigmaOrbitsQuotientStabilizer' α β hφ)]

中文:
定理 card_eq_sum_card_group_div_card_stabilizer'
  结论: [有限类型 α] [有限类型 β] [有限类型 Ω]
  证明: by
  classical
    have : forall ω : Ω, Fintype.card α / Fintype.card (stabilizer α (φ ω)) =
        Fintype.card (α ⧸ stabilizer α (φ ω)) := by
      intro ω
      rw [Fintype.card_congr (@Subgroup.groupEquivQuotientProdSubgroup α _ (stabilizer α <| φ ω))]; rw [Fintype.card_prod]; rw [Nat.mul_div_cancel]
      exact Fintype.card_pos_iff.mpr (by infer_instance)
    simp_rw [this, ← Fintype.card_sigma,
      Fintype.card_congr (selfEquivSigmaOrbitsQuotientStabilizer' α β hφ)]

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_congr, Fintype.card_pos_iff.mpr, Fintype.card_prod, Fintype.card_sigma, Nat.mul_div_cancel, Subgroup, Subgroup.groupEquivQuotientProdSubgroup, card_congr, card_pos_iff, card_prod, card_sigma, classical, groupEquivQuotientProdSubgroup, infer_instance, mul_div_cancel, selfEquivSigmaOrbitsQuotientStabilizer, simp_rw, stabilizer
-/
theorem card_eq_sum_card_group_div_card_stabilizer' [Fintype α] [Fintype β] [Fintype Ω]
    [forall b : β, Fintype <| stabilizer α b] {φ : Ω -> β} (hφ : LeftInverse Quotient.mk'' φ) :
    Fintype.card β = ∑ ω : Ω, Fintype.card α / Fintype.card (stabilizer α (φ ω)) := by
  classical
    have : forall ω : Ω, Fintype.card α / Fintype.card (stabilizer α (φ ω)) =
        Fintype.card (α ⧸ stabilizer α (φ ω)) := by
      intro ω
      rw [Fintype.card_congr (@Subgroup.groupEquivQuotientProdSubgroup α _ (stabilizer α <| φ ω))]; rw [Fintype.card_prod]; rw [Nat.mul_div_cancel]
      exact Fintype.card_pos_iff.mpr (by infer_instance)
    simp_rw [this, ← Fintype.card_sigma,
      Fintype.card_congr (selfEquivSigmaOrbitsQuotientStabilizer' α β hφ)]

/-- **Class formula** for a finite group acting on a finite type. -/
@[to_additive /-- **Class formula** for a finite group acting on a finite type. -/]
/--
theorem `card_eq_sum_card_group_div_card_stabilizer` / 定理 `card_eq_sum_card_group_div_card_stabilizer`

English:
theorem card_eq_sum_card_group_div_card_stabilizer
  statement: [Fintype α] [Fintype β] [Fintype Ω]
  proof: card_eq_sum_card_group_div_card_stabilizer' α β Quotient.out_eq'

中文:
定理 card_eq_sum_card_group_div_card_stabilizer
  结论: [有限类型 α] [有限类型 β] [有限类型 Ω]
  证明: card_eq_sum_card_group_div_card_stabilizer' α β Quotient.out_eq'

Depends on / 依赖: Quotient, Quotient.out_eq, card_eq_sum_card_group_div_card_stabilizer, out_eq
-/
theorem card_eq_sum_card_group_div_card_stabilizer [Fintype α] [Fintype β] [Fintype Ω]
    [forall b : β, Fintype <| stabilizer α b] :
    Fintype.card β = ∑ ω : Ω, Fintype.card α / Fintype.card (stabilizer α ω.out) :=
  card_eq_sum_card_group_div_card_stabilizer' α β Quotient.out_eq'

end MulAction

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instInfiniteProdSubtypeCommute` / 实例 `instInfiniteProdSubtypeCommute`

English:
instance instInfiniteProdSubtypeCommute
  signature: [Mul α] [Infinite α]
  body: Infinite.of_injective (fun a => ⟨⟨a, a⟩, rfl⟩) (by intro; simp)

中文:
实例 instInfiniteProdSubtypeCommute
  签名: [乘法 α] [无限 α]
  定义体: Infinite.of_injective (fun a => ⟨⟨a, a⟩, rfl⟩) (by intro; simp)

Depends on / 依赖: Infinite, Infinite.of_injective, of_injective
-/
instance instInfiniteProdSubtypeCommute [Mul α] [Infinite α] :
    Infinite { p : α × α // Commute p.1 p.2 } :=
  Infinite.of_injective (fun a => ⟨⟨a, a⟩, rfl⟩) (by intro; simp)

open Fintype

/--
theorem `card_comm_eq_card_conjClasses_mul_card` / 定理 `card_comm_eq_card_conjClasses_mul_card`

English:
theorem card_comm_eq_card_conjClasses_mul_card
  given: (G : Type*) [Group G]
  proof: by
  classical
  rcases fintypeOrInfinite G; swap
  · rw [mul_comm, Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite, zero_mul]
  simp only [Nat.card_eq_fintype_card]
  calc card { p : G × G // Commute p.1 p.2 }
      _ = card ((a : G) × { b // Commute a b }) :=
            card_congr (Equiv.subtypeProdEquivSigmaSubtype Commute)
      _ = ∑ i, card { b // Commute i b } := card_sigma
      _ = ∑ x, card (MulAction.fixedBy G x) :=
            sum_equiv ConjAct.toConjAct.toEquiv (fun a => card { b // Commute a b })
              (fun g => card (MulAction.fixedBy G g))
fun g => card_congr' congr_arg _ funext fun h => mul_inv_eq_iff_eq_mul.symm.eq
      _ = card (Quotient (MulAction.orbitRel (ConjAct G) G)) * card (ConjAct G) :=
             MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group _ _
      _ = card (ConjClasses G) * card G := by
             congr 1; apply card_congr'; congr; ext
             exact (Setoid.comm' _).trans isConj_iff.symm

中文:
定理 card_comm_eq_card_conjClasses_mul_card
  条件: (G : 类型) [群 G]
  证明: by
  classical
  rcases fintypeOrInfinite G; swap
  · rw [mul_comm, Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite, zero_mul]
  simp only [Nat.card_eq_fintype_card]
  calc card { p : G × G // Commute p.1 p.2 }
      _ = card ((a : G) × { b // Commute a b }) :=
            card_congr (Equiv.subtypeProdEquivSigmaSubtype Commute)
      _ = ∑ i, card { b // Commute i b } := card_sigma
      _ = ∑ x, card (MulAction.fixedBy G x) :=
            sum_equiv ConjAct.toConjAct.toEquiv (fun a => card { b // Commute a b })
              (fun g => card (MulAction.fixedBy G g))
fun g => card_congr' congr_arg _ funext fun h => mul_inv_eq_iff_eq_mul.symm.eq
      _ = card (Quotient (MulAction.orbitRel (ConjAct G) G)) * card (ConjAct G) :=
             MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group _ _
      _ = card (ConjClasses G) * card G := by
             congr 1; apply card_congr'; congr; ext
             exact (Setoid.comm' _).trans isConj_iff.symm

Depends on / 依赖: Commute, ConjAct, ConjAct.toConjAct.toEquiv, Equiv.subtypeProdEquivSigmaSubtype, MulActio, MulAction, MulAction.fixedBy, Nat.card_eq_fintype_card, Nat.card_eq_zero_of_infinite, card_congr, card_eq_fintype_card, card_eq_zero_of_infinite, card_sigma, classical, fintypeOrInfinite, fixedBy, mul_comm, subtypeProdEquivSigmaSubtype, sum_equiv, toConjAct
-/
theorem card_comm_eq_card_conjClasses_mul_card (G : Type*) [Group G] :
    Nat.card { p : G × G // Commute p.1 p.2 } = Nat.card (ConjClasses G) * Nat.card G := by
  classical
  rcases fintypeOrInfinite G; swap
  · rw [mul_comm, Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite, zero_mul]
  simp only [Nat.card_eq_fintype_card]
  calc card { p : G × G // Commute p.1 p.2 }
      _ = card ((a : G) × { b // Commute a b }) :=
            card_congr (Equiv.subtypeProdEquivSigmaSubtype Commute)
      _ = ∑ i, card { b // Commute i b } := card_sigma
      _ = ∑ x, card (MulAction.fixedBy G x) :=
            sum_equiv ConjAct.toConjAct.toEquiv (fun a => card { b // Commute a b })
              (fun g => card (MulAction.fixedBy G g))
fun g => card_congr' congr_arg _ funext fun h => mul_inv_eq_iff_eq_mul.symm.eq
      _ = card (Quotient (MulAction.orbitRel (ConjAct G) G)) * card (ConjAct G) :=
             MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group _ _
      _ = card (ConjClasses G) * card G := by
             congr 1; apply card_congr'; congr; ext
             exact (Setoid.comm' _).trans isConj_iff.symm
