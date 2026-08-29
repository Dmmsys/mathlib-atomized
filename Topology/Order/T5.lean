/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.OrdConnectedComponent
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Separation.Regular

/-!
# Linear order is a completely normal Hausdorff topological space

In this file we prove that a linear order with order topology is a completely normal Hausdorff
topological space.
-/

public section


open Filter Set Function OrderDual Topology Interval

variable {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderTopology X] {a : X} {s t : Set X}

namespace Set

@[simp]
/--
theorem `ordConnectedComponent_mem_nhds` / 定理 `ordConnectedComponent_mem_nhds`

English:
theorem ordConnectedComponent_mem_nhds
  statement: ordConnectedComponent s a in 𝓝 a ↔ s in 𝓝 a
  proof: by
  refine ⟨fun h => mem_of_superset h ordConnectedComponent_subset, fun h => ?_⟩
  rcases exists_Icc_mem_subset_of_mem_nhds h with ⟨b, c, ha, ha', hs⟩
  exact mem_of_superset ha' (subset_ordConnectedComponent ha hs)

中文:
定理 ordConnectedComponent_mem_nhds
  结论: ordConnectedComponent s a in 𝓝 a ↔ s in 𝓝 a
  证明: by
  refine ⟨fun h => mem_of_superset h ordConnectedComponent_subset, fun h => ?_⟩
  rcases exists_Icc_mem_subset_of_mem_nhds h with ⟨b, c, ha, ha', hs⟩
  exact mem_of_superset ha' (subset_ordConnectedComponent ha hs)

Depends on / 依赖: exists_Icc_mem_subset_of_mem_nhds, mem_of_superset, ordConnectedComponent_subset, subset_ordConnectedComponent
-/
theorem ordConnectedComponent_mem_nhds : ordConnectedComponent s a in 𝓝 a ↔ s in 𝓝 a := by
  refine ⟨fun h => mem_of_superset h ordConnectedComponent_subset, fun h => ?_⟩
  rcases exists_Icc_mem_subset_of_mem_nhds h with ⟨b, c, ha, ha', hs⟩
  exact mem_of_superset ha' (subset_ordConnectedComponent ha hs)

/--
theorem `compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE` / 定理 `compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE`

English:
theorem compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE
  statement: (hd : Disjoint s (closure t))
  proof: by
  have hmem : tᶜ in 𝓝[>=] a := by
    refine mem_nhdsWithin_of_mem_nhds ?_
    rw [← mem_interior_iff_mem_nhds]; rw [interior_compl]
    exact disjoint_left.1 hd ha
  rcases exists_Icc_mem_subset_of_mem_nhdsGE hmem with ⟨b, hab, hmem', hsub⟩
  by_cases H : Disjoint (Icc a b) (ordConnectedSection <| ordSeparatingSet s t)
  · exact mem_of_superset hmem' (disjoint_left.1 H)
  · simp only [Set.disjoint_left, not_forall, Classical.not_not] at H
    rcases H with ⟨c, ⟨hac, hcb⟩, hc⟩
    have hsub' : Icc a b subseteq ordConnectedComponent tᶜ a :=
      subset_ordConnectedComponent (left_mem_Icc.2 hab) hsub
    have hd : Disjoint s (ordConnectedSection (ordSeparatingSet s t)) :=
      disjoint_left_ordSeparatingSet.mono_right ordConnectedSection_subset
replace hac : a < c := hac.lt_of_ne Ne.symm ne_of_mem_of_not_mem hc
      disjoint_left.1 hd ha
    filter_upwards [Ico_mem_nhdsGE hac] with x hx hx'
    refine hx.2.ne (eq_of_mem_ordConnectedSection_of_uIcc_subset hx' hc ?_)
    refine subset_inter (subset_iUnion₂_of_subset a ha ?_) ?_
    · exact OrdConnected.uIcc_subset inferInstance (hsub' ⟨hx.1, hx.2.le.trans hcb⟩)
        (hsub' ⟨hac.le, hcb⟩)
    · rcases mem_iUnion₂.1 (ordConnectedSection_subset hx').2 with ⟨y, hyt, hxy⟩
      refine subset_iUnion₂_of_subset y hyt (OrdConnected.uIcc_subset inferInstance hxy ?_)
      refine subset_ordConnectedComponent left_mem_uIcc hxy ?_
      suffices c < y by
        rw [uIcc_of_ge (hx.2.trans this).le]
        exact ⟨hx.2.le, this.le⟩
      refine lt_of_not_ge fun hyc => ?_
      have hya : y < a := not_le.1 fun hay => hsub ⟨hay, hyc.trans hcb⟩ hyt
      exact hxy (Icc_subset_uIcc ⟨hya.le, hx.1⟩) ha

中文:
定理 compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE
  结论: (hd : Disjoint s (closure t))
  证明: by
  have hmem : tᶜ in 𝓝[>=] a := by
    refine mem_nhdsWithin_of_mem_nhds ?_
    rw [← mem_interior_iff_mem_nhds]; rw [interior_compl]
    exact disjoint_left.1 hd ha
  rcases exists_Icc_mem_subset_of_mem_nhdsGE hmem with ⟨b, hab, hmem', hsub⟩
  by_cases H : Disjoint (Icc a b) (ordConnectedSection <| ordSeparatingSet s t)
  · exact mem_of_superset hmem' (disjoint_left.1 H)
  · simp only [Set.disjoint_left, not_forall, Classical.not_not] at H
    rcases H with ⟨c, ⟨hac, hcb⟩, hc⟩
    have hsub' : Icc a b subseteq ordConnectedComponent tᶜ a :=
      subset_ordConnectedComponent (left_mem_Icc.2 hab) hsub
    have hd : Disjoint s (ordConnectedSection (ordSeparatingSet s t)) :=
      disjoint_left_ordSeparatingSet.mono_right ordConnectedSection_subset
replace hac : a < c := hac.lt_of_ne Ne.symm ne_of_mem_of_not_mem hc
      disjoint_left.1 hd ha
    filter_upwards [Ico_mem_nhdsGE hac] with x hx hx'
    refine hx.2.ne (eq_of_mem_ordConnectedSection_of_uIcc_subset hx' hc ?_)
    refine subset_inter (subset_iUnion₂_of_subset a ha ?_) ?_
    · exact OrdConnected.uIcc_subset inferInstance (hsub' ⟨hx.1, hx.2.le.trans hcb⟩)
        (hsub' ⟨hac.le, hcb⟩)
    · rcases mem_iUnion₂.1 (ordConnectedSection_subset hx').2 with ⟨y, hyt, hxy⟩
      refine subset_iUnion₂_of_subset y hyt (OrdConnected.uIcc_subset inferInstance hxy ?_)
      refine subset_ordConnectedComponent left_mem_uIcc hxy ?_
      suffices c < y by
        rw [uIcc_of_ge (hx.2.trans this).le]
        exact ⟨hx.2.le, this.le⟩
      refine lt_of_not_ge fun hyc => ?_
      have hya : y < a := not_le.1 fun hay => hsub ⟨hay, hyc.trans hcb⟩ hyt
      exact hxy (Icc_subset_uIcc ⟨hya.le, hx.1⟩) ha

Depends on / 依赖: Classical, Classical.not_not, Disjoint, Set.disjoint_left, disjoint_left, exists_Icc_mem_subset_of_mem_nhdsGE, interior_compl, mem_interior_iff_mem_nhds, mem_nhdsWithin_of_mem_nhds, mem_of_superset, not_forall, not_not, ordConnecte, ordConnectedSection, ordSeparatingSet, subseteq
-/
theorem compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE (hd : Disjoint s (closure t))
    (ha : a in s) : (ordConnectedSection (ordSeparatingSet s t))ᶜ in 𝓝[>=] a := by
  have hmem : tᶜ in 𝓝[>=] a := by
    refine mem_nhdsWithin_of_mem_nhds ?_
    rw [← mem_interior_iff_mem_nhds]; rw [interior_compl]
    exact disjoint_left.1 hd ha
  rcases exists_Icc_mem_subset_of_mem_nhdsGE hmem with ⟨b, hab, hmem', hsub⟩
  by_cases H : Disjoint (Icc a b) (ordConnectedSection <| ordSeparatingSet s t)
  · exact mem_of_superset hmem' (disjoint_left.1 H)
  · simp only [Set.disjoint_left, not_forall, Classical.not_not] at H
    rcases H with ⟨c, ⟨hac, hcb⟩, hc⟩
    have hsub' : Icc a b subseteq ordConnectedComponent tᶜ a :=
      subset_ordConnectedComponent (left_mem_Icc.2 hab) hsub
    have hd : Disjoint s (ordConnectedSection (ordSeparatingSet s t)) :=
      disjoint_left_ordSeparatingSet.mono_right ordConnectedSection_subset
replace hac : a < c := hac.lt_of_ne Ne.symm ne_of_mem_of_not_mem hc
      disjoint_left.1 hd ha
    filter_upwards [Ico_mem_nhdsGE hac] with x hx hx'
    refine hx.2.ne (eq_of_mem_ordConnectedSection_of_uIcc_subset hx' hc ?_)
    refine subset_inter (subset_iUnion₂_of_subset a ha ?_) ?_
    · exact OrdConnected.uIcc_subset inferInstance (hsub' ⟨hx.1, hx.2.le.trans hcb⟩)
        (hsub' ⟨hac.le, hcb⟩)
    · rcases mem_iUnion₂.1 (ordConnectedSection_subset hx').2 with ⟨y, hyt, hxy⟩
      refine subset_iUnion₂_of_subset y hyt (OrdConnected.uIcc_subset inferInstance hxy ?_)
      refine subset_ordConnectedComponent left_mem_uIcc hxy ?_
      suffices c < y by
        rw [uIcc_of_ge (hx.2.trans this).le]
        exact ⟨hx.2.le, this.le⟩
      refine lt_of_not_ge fun hyc => ?_
      have hya : y < a := not_le.1 fun hay => hsub ⟨hay, hyc.trans hcb⟩ hyt
      exact hxy (Icc_subset_uIcc ⟨hya.le, hx.1⟩) ha

/--
theorem `compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE` / 定理 `compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE`

English:
theorem compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE
  statement: (hd : Disjoint s (closure t))
  proof: by
  have hd' : Disjoint (ofDual ⁻¹' s) (closure <| ofDual ⁻¹' t) := hd
  have ha' : toDual a in ofDual ⁻¹' s := ha
  simpa only [dual_ordSeparatingSet, dual_ordConnectedSection] using!
    compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE hd' ha'

中文:
定理 compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE
  结论: (hd : Disjoint s (closure t))
  证明: by
  have hd' : Disjoint (ofDual ⁻¹' s) (closure <| ofDual ⁻¹' t) := hd
  have ha' : toDual a in ofDual ⁻¹' s := ha
  simpa only [dual_ordSeparatingSet, dual_ordConnectedSection] using!
    compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE hd' ha'

Depends on / 依赖: Disjoint, closure, compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE, dual_ordConnectedSection, dual_ordSeparatingSet, ofDual, toDual
-/
theorem compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE (hd : Disjoint s (closure t))
    (ha : a in s) : (ordConnectedSection <| ordSeparatingSet s t)ᶜ in 𝓝[<=] a := by
  have hd' : Disjoint (ofDual ⁻¹' s) (closure <| ofDual ⁻¹' t) := hd
  have ha' : toDual a in ofDual ⁻¹' s := ha
  simpa only [dual_ordSeparatingSet, dual_ordConnectedSection] using!
    compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE hd' ha'

/--
theorem `compl_ordConnectedSection_ordSeparatingSet_mem_nhds` / 定理 `compl_ordConnectedSection_ordSeparatingSet_mem_nhds`

English:
theorem compl_ordConnectedSection_ordSeparatingSet_mem_nhds
  statement: (hd : Disjoint s (closure t))
  proof: by
  rw [← nhdsLE_sup_nhdsGE]; rw [mem_sup]
  exact ⟨compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE hd ha,
    compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE hd ha⟩

中文:
定理 compl_ordConnectedSection_ordSeparatingSet_mem_nhds
  结论: (hd : Disjoint s (closure t))
  证明: by
  rw [← nhdsLE_sup_nhdsGE]; rw [mem_sup]
  exact ⟨compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE hd ha,
    compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE hd ha⟩

Depends on / 依赖: compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE, compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE, mem_sup, nhdsLE_sup_nhdsGE
-/
theorem compl_ordConnectedSection_ordSeparatingSet_mem_nhds (hd : Disjoint s (closure t))
    (ha : a in s) : (ordConnectedSection <| ordSeparatingSet s t)ᶜ in 𝓝 a := by
  rw [← nhdsLE_sup_nhdsGE]; rw [mem_sup]
  exact ⟨compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE hd ha,
    compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE hd ha⟩

/--
theorem `ordT5Nhd_mem_nhdsSet` / 定理 `ordT5Nhd_mem_nhdsSet`

English:
theorem ordT5Nhd_mem_nhdsSet
  given: (hd : Disjoint s (closure t))
  statement: ordT5Nhd s t in 𝓝ˢ s
  proof: bUnion_mem_nhdsSet fun x hx => ordConnectedComponent_mem_nhds.2 inter_mem
    (by
      rw [← mem_interior_iff_mem_nhds]; rw [interior_compl]
      exact disjoint_left.1 hd hx)
    (compl_ordConnectedSection_ordSeparatingSet_mem_nhds hd hx)

中文:
定理 ordT5Nhd_mem_nhdsSet
  条件: (hd : Disjoint s (closure t))
  结论: ordT5Nhd s t in 𝓝ˢ s
  证明: bUnion_mem_nhdsSet fun x hx => ordConnectedComponent_mem_nhds.2 inter_mem
    (by
      rw [← mem_interior_iff_mem_nhds]; rw [interior_compl]
      exact disjoint_left.1 hd hx)
    (compl_ordConnectedSection_ordSeparatingSet_mem_nhds hd hx)

Depends on / 依赖: bUnion_mem_nhdsSet, compl_ordConnectedSection_ordSeparatingSet_mem_nhds, disjoint_left, inter_mem, interior_compl, mem_interior_iff_mem_nhds, ordConnectedComponent_mem_nhds
-/
theorem ordT5Nhd_mem_nhdsSet (hd : Disjoint s (closure t)) : ordT5Nhd s t in 𝓝ˢ s :=
bUnion_mem_nhdsSet fun x hx => ordConnectedComponent_mem_nhds.2 inter_mem
    (by
      rw [← mem_interior_iff_mem_nhds]; rw [interior_compl]
      exact disjoint_left.1 hd hx)
    (compl_ordConnectedSection_ordSeparatingSet_mem_nhds hd hx)

end Set

open Set

/-- A linear order with order topology is a completely normal Hausdorff topological space. -/
instance (priority := 100) OrderTopology.completelyNormalSpace : CompletelyNormalSpace X :=
  ⟨fun s t h₁ h₂ => Filter.disjoint_iff.2
    ⟨ordT5Nhd s t, ordT5Nhd_mem_nhdsSet h₂, ordT5Nhd t s, ordT5Nhd_mem_nhdsSet h₁.symm,
      disjoint_ordT5Nhd⟩⟩

instance (priority := 100) OrderTopology.t5Space : T5Space X := T5Space.mk
