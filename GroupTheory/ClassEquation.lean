/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Rodriguez
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Class Equation

This file establishes the class equation for finite groups.

## Main statements

* `Group.card_center_add_sum_card_noncenter_eq_card`: The **class equation** for finite groups.
  The cardinality of a group is equal to the size of its center plus the sum of the size of all its
  nontrivial conjugacy classes. Also `Group.nat_card_center_add_sum_card_noncenter_eq_card`.

-/

public section

open MulAction ConjClasses

variable (G : Type*) [Group G]

/--
theorem `sum_conjClasses_card_eq_card` / 定理 `sum_conjClasses_card_eq_card`

English:
theorem sum_conjClasses_card_eq_card
  statement: [Fintype <| ConjClasses G] [Fintype G]
  proof: by
  suffices (Σ x : ConjClasses G, x.carrier) ≃ G by simpa using! (Fintype.card_congr this)
  simpa [carrier_eq_preimage_mk] using! Equiv.sigmaFiberEquiv ConjClasses.mk

中文:
定理 sum_conjClasses_card_eq_card
  结论: [有限类型 <| ConjClasses G] [有限类型 G]
  证明: by
  suffices (Σ x : ConjClasses G, x.carrier) ≃ G by simpa using! (Fintype.card_congr this)
  simpa [carrier_eq_preimage_mk] using! Equiv.sigmaFiberEquiv ConjClasses.mk

Depends on / 依赖: ConjClasses, ConjClasses.mk, Equiv.sigmaFiberEquiv, Fintype, Fintype.card_congr, card_congr, carrier, carrier_eq_preimage_mk, sigmaFiberEquiv, x.carrier
-/
theorem sum_conjClasses_card_eq_card [Fintype <| ConjClasses G] [Fintype G]
    [forall x : ConjClasses G, Fintype x.carrier] :
    ∑ x : ConjClasses G, x.carrier.toFinset.card = Fintype.card G := by
  suffices (Σ x : ConjClasses G, x.carrier) ≃ G by simpa using! (Fintype.card_congr this)
  simpa [carrier_eq_preimage_mk] using! Equiv.sigmaFiberEquiv ConjClasses.mk

/--
theorem `Group.sum_card_conj_classes_eq_card` / 定理 `Group.sum_card_conj_classes_eq_card`

English:
theorem Group.sum_card_conj_classes_eq_card
  given: [Finite G]
  proof: by
  classical
  cases nonempty_fintype G
  simp [← sum_conjClasses_card_eq_card, finsum_eq_sum_of_fintype]

中文:
定理 群.sum_card_conj_classes_eq_card
  条件: [有限 G]
  证明: by
  classical
  cases nonempty_fintype G
  simp [← sum_conjClasses_card_eq_card, finsum_eq_sum_of_fintype]

Depends on / 依赖: classical, finsum_eq_sum_of_fintype, nonempty_fintype, sum_conjClasses_card_eq_card
-/
theorem Group.sum_card_conj_classes_eq_card [Finite G] :
    ∑ᶠ x : ConjClasses G, x.carrier.ncard = Nat.card G := by
  classical
  cases nonempty_fintype G
  simp [← sum_conjClasses_card_eq_card, finsum_eq_sum_of_fintype]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Group.nat_card_center_add_sum_card_noncenter_eq_card` / 定理 `Group.nat_card_center_add_sum_card_noncenter_eq_card`

English:
theorem Group.nat_card_center_add_sum_card_noncenter_eq_card
  given: [Finite G]
  proof: by
  classical
  cases nonempty_fintype G
  rw [@Nat.card_eq_fintype_card G]; rw [← sum_conjClasses_card_eq_card]; rw [←
    Finset.sum_sdiff (ConjClasses.noncenter G).toFinset.subset_univ]
  simp only [Nat.card_eq_fintype_card, Set.toFinset_card]
  congr 1
  swap
  · convert! finsum_cond_eq_sum_of_cond_iff _ _
    simp [Set.mem_toFinset]
  calc
    Fintype.card (Subgroup.center G) = Fintype.card ((noncenter G)ᶜ : Set _) :=
      Fintype.card_congr ((mk_bijOn G).equiv _)
    _ = Finset.card (Finset.univ \ (noncenter G).toFinset) := by
      rw [← Set.toFinset_card]; rw [Set.toFinset_compl]; rw [Finset.compl_eq_univ_sdiff]
    _ = _ := ?_
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl ?_
  rintro ⟨g⟩ hg
  simp only [noncenter, Set.toFinset_ofPred, Finset.mem_univ, true_and,
             Finset.mem_sdiff, Finset.mem_filter, Set.not_nontrivial_iff] at hg
  rw [eq_comm]; rw [← Set.toFinset_card]; rw [Finset.card_eq_one]
exact ⟨g, Finset.coe_injective by simpa using hg.eq_singleton_of_mem mem_carrier_mk⟩

中文:
定理 群.nat_card_center_add_sum_card_noncenter_eq_card
  条件: [有限 G]
  证明: by
  classical
  cases nonempty_fintype G
  rw [@Nat.card_eq_fintype_card G]; rw [← sum_conjClasses_card_eq_card]; rw [←
    Finset.sum_sdiff (ConjClasses.noncenter G).toFinset.subset_univ]
  simp only [Nat.card_eq_fintype_card, Set.toFinset_card]
  congr 1
  swap
  · convert! finsum_cond_eq_sum_of_cond_iff _ _
    simp [Set.mem_toFinset]
  calc
    Fintype.card (Subgroup.center G) = Fintype.card ((noncenter G)ᶜ : Set _) :=
      Fintype.card_congr ((mk_bijOn G).equiv _)
    _ = Finset.card (Finset.univ \ (noncenter G).toFinset) := by
      rw [← Set.toFinset_card]; rw [Set.toFinset_compl]; rw [Finset.compl_eq_univ_sdiff]
    _ = _ := ?_
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl ?_
  rintro ⟨g⟩ hg
  simp only [noncenter, Set.toFinset_ofPred, Finset.mem_univ, true_and,
             Finset.mem_sdiff, Finset.mem_filter, Set.not_nontrivial_iff] at hg
  rw [eq_comm]; rw [← Set.toFinset_card]; rw [Finset.card_eq_one]
exact ⟨g, Finset.coe_injective by simpa using hg.eq_singleton_of_mem mem_carrier_mk⟩

Depends on / 依赖: ConjClasses, ConjClasses.noncenter, Finset, Finset.card, Finset.sum_sdiff, Finset.univ, Fintype, Fintype.card, Fintype.card_congr, Nat.card_eq_fintype_card, Set.mem_toFinset, Set.toFinset_card, Subgroup, Subgroup.center, card_congr, card_eq_fintype_card, center, classical, convert, finsum_cond_eq_sum_of_cond_iff
-/
theorem Group.nat_card_center_add_sum_card_noncenter_eq_card [Finite G] :
    Nat.card (Subgroup.center G) + ∑ᶠ x in noncenter G, Nat.card x.carrier = Nat.card G := by
  classical
  cases nonempty_fintype G
  rw [@Nat.card_eq_fintype_card G]; rw [← sum_conjClasses_card_eq_card]; rw [←
    Finset.sum_sdiff (ConjClasses.noncenter G).toFinset.subset_univ]
  simp only [Nat.card_eq_fintype_card, Set.toFinset_card]
  congr 1
  swap
  · convert! finsum_cond_eq_sum_of_cond_iff _ _
    simp [Set.mem_toFinset]
  calc
    Fintype.card (Subgroup.center G) = Fintype.card ((noncenter G)ᶜ : Set _) :=
      Fintype.card_congr ((mk_bijOn G).equiv _)
    _ = Finset.card (Finset.univ \ (noncenter G).toFinset) := by
      rw [← Set.toFinset_card]; rw [Set.toFinset_compl]; rw [Finset.compl_eq_univ_sdiff]
    _ = _ := ?_
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl ?_
  rintro ⟨g⟩ hg
  simp only [noncenter, Set.toFinset_ofPred, Finset.mem_univ, true_and,
             Finset.mem_sdiff, Finset.mem_filter, Set.not_nontrivial_iff] at hg
  rw [eq_comm]; rw [← Set.toFinset_card]; rw [Finset.card_eq_one]
exact ⟨g, Finset.coe_injective by simpa using hg.eq_singleton_of_mem mem_carrier_mk⟩

/--
theorem `Group.card_center_add_sum_card_noncenter_eq_card` / 定理 `Group.card_center_add_sum_card_noncenter_eq_card`

English:
theorem Group.card_center_add_sum_card_noncenter_eq_card
  statement: (G) [Group G]
  proof: by
  convert! Group.nat_card_center_add_sum_card_noncenter_eq_card G using 2
  · simp
  · rw [← finsum_set_coe_eq_finsum_mem (noncenter G), finsum_eq_sum_of_fintype,
      ← Finset.sum_set_coe]
    simp
  · simp

中文:
定理 群.card_center_add_sum_card_noncenter_eq_card
  结论: (G) [群 G]
  证明: by
  convert! Group.nat_card_center_add_sum_card_noncenter_eq_card G using 2
  · simp
  · rw [← finsum_set_coe_eq_finsum_mem (noncenter G), finsum_eq_sum_of_fintype,
      ← Finset.sum_set_coe]
    simp
  · simp

Depends on / 依赖: Finset, Finset.sum_set_coe, Group.nat_card_center_add_sum_card_noncenter_eq_card, convert, finsum_eq_sum_of_fintype, finsum_set_coe_eq_finsum_mem, nat_card_center_add_sum_card_noncenter_eq_card, noncenter, sum_set_coe
-/
theorem Group.card_center_add_sum_card_noncenter_eq_card (G) [Group G]
    [forall x : ConjClasses G, Fintype x.carrier] [Fintype G] [Fintype <| Subgroup.center G]
    [Fintype <| noncenter G] : Fintype.card (Subgroup.center G) +
    ∑ x in (noncenter G).toFinset, x.carrier.toFinset.card = Fintype.card G := by
  convert! Group.nat_card_center_add_sum_card_noncenter_eq_card G using 2
  · simp
  · rw [← finsum_set_coe_eq_finsum_mem (noncenter G), finsum_eq_sum_of_fintype,
      ← Finset.sum_set_coe]
    simp
  · simp
