/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Violeta Hernández Palacios
-/
module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.SuccPred.Limit

/-!
# Order topologies of successor or predecessor orders

This file proves miscellaneous results under the assumption of `OrderTopology` plus either of
`SuccOrder` or `PredOrder`.
-/

public section

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  {a : α} {s : Set α}

open Filter Order Set Topology

namespace SuccOrder
variable [SuccOrder α]

@[to_dual]
/--
theorem `isOpen_singleton_of_not_isSuccPrelimit` / 定理 `isOpen_singleton_of_not_isSuccPrelimit`

English:
theorem isOpen_singleton_of_not_isSuccPrelimit
  given: (ha : ¬ IsSuccPrelimit a)
  statement: IsOpen {a}
  proof: by
  obtain ⟨b, hb⟩ := not_isSuccPrelimit_iff.1 ha
  by_cases ha' : IsMax a
  · convert! isOpen_Ioi (a := b) using 1
    rw [hb.Ioi_eq]
    grind [IsMax]
  · convert! isOpen_Ioo (a := b) (b := Order.succ a) using 1
    simp [(covBy_succ_of_not_isMax ha').Ioo_eq_Ioc, hb.Ioc_eq]

中文:
定理 isOpen_singleton_of_not_isSuccPrelimit
  条件: (ha : ¬ IsSuccPrelimit a)
  结论: 是开集 {a}
  证明: by
  obtain ⟨b, hb⟩ := not_isSuccPrelimit_iff.1 ha
  by_cases ha' : IsMax a
  · convert! isOpen_Ioi (a := b) using 1
    rw [hb.Ioi_eq]
    grind [IsMax]
  · convert! isOpen_Ioo (a := b) (b := Order.succ a) using 1
    simp [(covBy_succ_of_not_isMax ha').Ioo_eq_Ioc, hb.Ioc_eq]

Depends on / 依赖: Ioc_eq, Ioi_eq, Ioo_eq_Ioc, Order.succ, convert, covBy_succ_of_not_isMax, hb.Ioc_eq, hb.Ioi_eq, isOpen_Ioi, isOpen_Ioo, not_isSuccPrelimit_iff
-/
theorem isOpen_singleton_of_not_isSuccPrelimit (ha : ¬ IsSuccPrelimit a) : IsOpen {a} := by
  obtain ⟨b, hb⟩ := not_isSuccPrelimit_iff.1 ha
  by_cases ha' : IsMax a
  · convert! isOpen_Ioi (a := b) using 1
    rw [hb.Ioi_eq]
    grind [IsMax]
  · convert! isOpen_Ioo (a := b) (b := Order.succ a) using 1
    simp [(covBy_succ_of_not_isMax ha').Ioo_eq_Ioc, hb.Ioc_eq]

variable [NoMaxOrder α]

@[to_dual]
/--
theorem `isOpen_singleton_iff` / 定理 `isOpen_singleton_iff`

English:
theorem isOpen_singleton_iff
  statement: IsOpen {a} ↔ ¬ IsSuccLimit a
  proof: by
  nontriviality α
  refine ⟨fun h ha => ?_, fun ha => ?_⟩
  · obtain ⟨l, u, h₁, h₂⟩ := mem_nhds_iff_exists_Ioo_subset' (by simpa using ha.not_isMin)
.mp (h.mem_nhds (mem_singleton a)) (by simpa only [not_isMax_iff] using not_isMax a)
    refine ha.isSuccPrelimit l ?_
    rw [← succ_eq_iff_covBy]
    simp only [mem_Ioo, subset_singleton_iff] at h₁ h₂
    exact h₂ _ ⟨lt_succ l, h₁.1.succ_le.trans_lt h₁.2⟩
  · obtain (ha | ha) := not_isSuccLimit_iff.mp ha
    · convert! isOpen_Iio (a := Order.succ a) using 1
      simp [ha.Iic_eq]
    · exact isOpen_singleton_of_not_isSuccPrelimit ha

@[to_dual]

中文:
定理 isOpen_singleton_iff
  结论: 是开集 {a} ↔ ¬ 是SuccLimit a
  证明: by
  nontriviality α
  refine ⟨fun h ha => ?_, fun ha => ?_⟩
  · obtain ⟨l, u, h₁, h₂⟩ := mem_nhds_iff_exists_Ioo_subset' (by simpa using ha.not_isMin)
.mp (h.mem_nhds (mem_singleton a)) (by simpa only [not_isMax_iff] using not_isMax a)
    refine ha.isSuccPrelimit l ?_
    rw [← succ_eq_iff_covBy]
    simp only [mem_Ioo, subset_singleton_iff] at h₁ h₂
    exact h₂ _ ⟨lt_succ l, h₁.1.succ_le.trans_lt h₁.2⟩
  · obtain (ha | ha) := not_isSuccLimit_iff.mp ha
    · convert! isOpen_Iio (a := Order.succ a) using 1
      simp [ha.Iic_eq]
    · exact isOpen_singleton_of_not_isSuccPrelimit ha

@[to_dual]

Depends on / 依赖: Iic_e, Order.succ, convert, h.mem_nhds, ha.Iic_e, ha.isSuccPrelimit, ha.not_isMin, isOpen_Iio, isSuccPrelimit, lt_succ, mem_Ioo, mem_nhds, mem_nhds_iff_exists_Ioo_subset, mem_singleton, nontriviality, not_isMax, not_isMax_iff, not_isMin, not_isSuccLimit_iff, not_isSuccLimit_iff.mp
-/
theorem isOpen_singleton_iff : IsOpen {a} ↔ ¬ IsSuccLimit a := by
  nontriviality α
  refine ⟨fun h ha => ?_, fun ha => ?_⟩
  · obtain ⟨l, u, h₁, h₂⟩ := mem_nhds_iff_exists_Ioo_subset' (by simpa using ha.not_isMin)
.mp (h.mem_nhds (mem_singleton a)) (by simpa only [not_isMax_iff] using not_isMax a)
    refine ha.isSuccPrelimit l ?_
    rw [← succ_eq_iff_covBy]
    simp only [mem_Ioo, subset_singleton_iff] at h₁ h₂
    exact h₂ _ ⟨lt_succ l, h₁.1.succ_le.trans_lt h₁.2⟩
  · obtain (ha | ha) := not_isSuccLimit_iff.mp ha
    · convert! isOpen_Iio (a := Order.succ a) using 1
      simp [ha.Iic_eq]
    · exact isOpen_singleton_of_not_isSuccPrelimit ha

@[to_dual]
/--
theorem `nhds_eq_pure` / 定理 `nhds_eq_pure`

English:
theorem nhds_eq_pure
  given: {a : α}
  statement: 𝓝 a = pure a ↔ ¬ IsSuccLimit a
  proof: (isOpen_singleton_iff_nhds_eq_pure _).symm.trans isOpen_singleton_iff

@[to_dual]

中文:
定理 nhds_eq_pure
  条件: {a : α}
  结论: 𝓝 a = pure a ↔ ¬ 是SuccLimit a
  证明: (isOpen_singleton_iff_nhds_eq_pure _).symm.trans isOpen_singleton_iff

@[to_dual]

Depends on / 依赖: isOpen_singleton_iff, isOpen_singleton_iff_nhds_eq_pure, symm.trans
-/
theorem nhds_eq_pure {a : α} : 𝓝 a = pure a ↔ ¬ IsSuccLimit a :=
  (isOpen_singleton_iff_nhds_eq_pure _).symm.trans isOpen_singleton_iff

@[to_dual]
/--
theorem `nhds_of_isMin` / 定理 `nhds_of_isMin`

English:
theorem nhds_of_isMin
  given: {a : α} (h : IsMin a)
  statement: 𝓝 a = pure a
  proof: by
  rw [nhds_eq_pure]; rw [isSuccLimit_iff]
  tauto

@[to_dual (attr := simp)]

中文:
定理 nhds_of_isMin
  条件: {a : α} (h : IsMin a)
  结论: 𝓝 a = pure a
  证明: by
  rw [nhds_eq_pure]; rw [isSuccLimit_iff]
  tauto

@[to_dual (attr := simp)]

Depends on / 依赖: isSuccLimit_iff, nhds_eq_pure
-/
theorem nhds_of_isMin {a : α} (h : IsMin a) : 𝓝 a = pure a := by
  rw [nhds_eq_pure]; rw [isSuccLimit_iff]
  tauto

@[to_dual (attr := simp)]
/--
theorem `nhds_bot` / 定理 `nhds_bot`

English:
theorem nhds_bot
  given: [OrderBot α]
  statement: 𝓝 (⊥ : α) = pure ⊥
  proof: nhds_of_isMin isMin_bot

@[to_dual]

中文:
定理 nhds_bot
  条件: [有底序 α]
  结论: 𝓝 (⊥ : α) = pure ⊥
  证明: nhds_of_isMin isMin_bot

@[to_dual]

Depends on / 依赖: isMin_bot, nhds_of_isMin
-/
theorem nhds_bot [OrderBot α] : 𝓝 (⊥ : α) = pure ⊥ :=
  nhds_of_isMin isMin_bot

@[to_dual]
/--
theorem `isOpen_iff` / 定理 `isOpen_iff`

English:
theorem isOpen_iff
  given: {s : Set α}
  statement: IsOpen s ↔
  proof: by
refine isOpen_iff_mem_nhds.trans forall₂_congr fun o ho => ?_
  by_cases ho' : IsSuccLimit o
  · rw [(hasBasis_nhds_Ioc_of_exists_lt (not_isMin_iff.1 ho'.not_isMin)).mem_iff]
    grind
  · simp [nhds_eq_pure.2 ho', ho, ho']

@[to_dual]

中文:
定理 isOpen_iff
  条件: {s : 集合 α}
  结论: 是开集 s ↔
  证明: by
refine isOpen_iff_mem_nhds.trans forall₂_congr fun o ho => ?_
  by_cases ho' : IsSuccLimit o
  · rw [(hasBasis_nhds_Ioc_of_exists_lt (not_isMin_iff.1 ho'.not_isMin)).mem_iff]
    grind
  · simp [nhds_eq_pure.2 ho', ho, ho']

@[to_dual]

Depends on / 依赖: IsSuccLimit, hasBasis_nhds_Ioc_of_exists_lt, isOpen_iff_mem_nhds, isOpen_iff_mem_nhds.trans, mem_iff, nhds_eq_pure, not_isMin, not_isMin_iff
-/
theorem isOpen_iff {s : Set α} : IsOpen s ↔
    forall o in s, IsSuccLimit o -> exists a < o, Ioo a o subseteq s := by
refine isOpen_iff_mem_nhds.trans forall₂_congr fun o ho => ?_
  by_cases ho' : IsSuccLimit o
  · rw [(hasBasis_nhds_Ioc_of_exists_lt (not_isMin_iff.1 ho'.not_isMin)).mem_iff]
    grind
  · simp [nhds_eq_pure.2 ho', ho, ho']

@[to_dual]
/--
theorem `accPt_principal` / 定理 `accPt_principal`

English:
theorem accPt_principal
  given: {a : α} {s : Set α}
  proof: by
  rw [accPt_iff_frequently]
  by_cases ha : IsMin a
  · simp [nhds_of_isMin, ha]
  · rw [not_isMin_iff] at ha ⊢
    simp_rw [(hasBasis_nhds_Ioc_of_exists_lt ha).frequently_iff, Set.Nonempty, mem_inter_iff]
    grind

@[to_dual]

中文:
定理 accPt_principal
  条件: {a : α} {s : 集合 α}
  证明: by
  rw [accPt_iff_frequently]
  by_cases ha : IsMin a
  · simp [nhds_of_isMin, ha]
  · rw [not_isMin_iff] at ha ⊢
    simp_rw [(hasBasis_nhds_Ioc_of_exists_lt ha).frequently_iff, Set.Nonempty, mem_inter_iff]
    grind

@[to_dual]

Depends on / 依赖: Nonempty, Set.Nonempty, accPt_iff_frequently, frequently_iff, hasBasis_nhds_Ioc_of_exists_lt, mem_inter_iff, nhds_of_isMin, not_isMin_iff, simp_rw
-/
theorem accPt_principal {a : α} {s : Set α} :
    AccPt a (𝓟 s) ↔ ¬ IsMin a ∧ forall b < a, (s inter Ioo b a).Nonempty := by
  rw [accPt_iff_frequently]
  by_cases ha : IsMin a
  · simp [nhds_of_isMin, ha]
  · rw [not_isMin_iff] at ha ⊢
    simp_rw [(hasBasis_nhds_Ioc_of_exists_lt ha).frequently_iff, Set.Nonempty, mem_inter_iff]
    grind

@[to_dual]
/--
theorem `_root_.AccPt.not_isMin` / 定理 `_root_.AccPt.not_isMin`

English:
theorem _root_.AccPt.not_isMin
  given: {a : α} {s : Set α} (h : AccPt a (𝓟 s))
  statement: ¬ IsMin a
  proof: (accPt_principal.1 h).1

@[to_dual]

中文:
定理 _root_.聚点.not_isMin
  条件: {a : α} {s : 集合 α} (h : 聚点 a (𝓟 s))
  结论: ¬ IsMin a
  证明: (accPt_principal.1 h).1

@[to_dual]

Depends on / 依赖: accPt_principal
-/
theorem _root_.AccPt.not_isMin {a : α} {s : Set α} (h : AccPt a (𝓟 s)) : ¬ IsMin a :=
  (accPt_principal.1 h).1

@[to_dual]
/--
theorem `_root_.AccPt.isSuccLimit` / 定理 `_root_.AccPt.isSuccLimit`

English:
theorem _root_.AccPt.isSuccLimit
  given: {a : α} {s : Set α} (h : AccPt a (𝓟 s))
  statement: IsSuccLimit a
  proof: by
  rw [isSuccLimit_iff]; rw [IsSuccPrelimit]
  simp_rw [accPt_principal, Set.Nonempty] at h
  grind [covBy_iff_Ioo_eq]

@[to_dual]

中文:
定理 _root_.聚点.isSuccLimit
  条件: {a : α} {s : 集合 α} (h : 聚点 a (𝓟 s))
  结论: 是SuccLimit a
  证明: by
  rw [isSuccLimit_iff]; rw [IsSuccPrelimit]
  simp_rw [accPt_principal, Set.Nonempty] at h
  grind [covBy_iff_Ioo_eq]

@[to_dual]

Depends on / 依赖: IsSuccPrelimit, Nonempty, Set.Nonempty, accPt_principal, covBy_iff_Ioo_eq, isSuccLimit_iff, simp_rw
-/
theorem _root_.AccPt.isSuccLimit {a : α} {s : Set α} (h : AccPt a (𝓟 s)) : IsSuccLimit a := by
  rw [isSuccLimit_iff]; rw [IsSuccPrelimit]
  simp_rw [accPt_principal, Set.Nonempty] at h
  grind [covBy_iff_Ioo_eq]

@[to_dual]
/--
theorem `isSuccLimit_of_mem_frontier` / 定理 `isSuccLimit_of_mem_frontier`

English:
theorem isSuccLimit_of_mem_frontier
  given: {a : α} {s : Set α} (ha : a in frontier s)
  statement: IsSuccLimit a
  proof: by
  rw [← isOpen_singleton_iff.not_left]
  rw [frontier_eq_closure_inter_closure] at ha
  grind [mem_closure_iff, Set.Nonempty]

中文:
定理 isSuccLimit_of_mem_frontier
  条件: {a : α} {s : 集合 α} (ha : a in frontier s)
  结论: 是SuccLimit a
  证明: by
  rw [← isOpen_singleton_iff.not_left]
  rw [frontier_eq_closure_inter_closure] at ha
  grind [mem_closure_iff, Set.Nonempty]

Depends on / 依赖: Nonempty, Set.Nonempty, frontier_eq_closure_inter_closure, isOpen_singleton_iff, isOpen_singleton_iff.not_left, mem_closure_iff, not_left
-/
theorem isSuccLimit_of_mem_frontier {a : α} {s : Set α} (ha : a in frontier s) : IsSuccLimit a := by
  rw [← isOpen_singleton_iff.not_left]
  rw [frontier_eq_closure_inter_closure] at ha
  grind [mem_closure_iff, Set.Nonempty]

end SuccOrder
