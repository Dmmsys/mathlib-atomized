/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Thickenings in pseudo-metric spaces

## Main definitions
* `Metric.thickening δ s`, the open thickening by radius `δ` of a set `s` in a pseudo emetric space.
* `Metric.cthickening δ s`, the closed thickening by radius `δ` of a set `s` in a pseudo emetric
  space.

## Main results
* `Disjoint.exists_thickenings`: two disjoint sets admit disjoint thickenings
* `Disjoint.exists_cthickenings`: two disjoint sets admit disjoint closed thickenings
* `IsCompact.exists_cthickening_subset_open`: if `s` is compact, `t` is open and `s ⊆ t`,
  some `cthickening` of `s` is contained in `t`.

* `Metric.hasBasis_nhdsSet_cthickening`: the `cthickening`s of a compact set `K` form a basis
  of the neighbourhoods of `K`
* `Metric.closure_eq_iInter_cthickening'`: the closure of a set equals the intersection
  of its closed thickenings of positive radii accumulating at zero.
  The same holds for open thickenings.
* `IsCompact.cthickening_eq_biUnion_closedBall`: if `s` is compact, `cthickening δ s` is the union
  of `closedBall`s of radius `δ` around `x : E`.

-/

@[expose] public section

noncomputable section
open NNReal ENNReal Topology Set Filter Bornology

universe u v w

variable {ι : Sort*} {α : Type u}

namespace Metric

section Thickening

variable [PseudoEMetricSpace α] {δ : Real} {s : Set α} {x : α}

/--
Definition of `thickening` / `thickening` 的定义

English:
definition thickening
  signature: (δ : Real) (E : Set α)
  body: { x : α | infEDist x E < ENNReal.ofReal δ }

中文:
定义 thickening
  签名: (δ : 实数) (E : Set α)
  定义体: { x : α | infEDist x E < ENNReal.ofReal δ }

Depends on / 依赖: ENNReal, ENNReal.ofReal, infEDist, ofReal
-/
def thickening (δ : Real) (E : Set α) : Set α :=
  { x : α | infEDist x E < ENNReal.ofReal δ }

/--
theorem `mem_thickening_iff_infEDist_lt` / 定理 `mem_thickening_iff_infEDist_lt`

English:
theorem mem_thickening_iff_infEDist_lt
  statement: x in thickening δ s ↔ infEDist x s < ENNReal.ofReal δ
  proof: Iff.rfl

@[deprecated (since := "2026-01-08")]
alias mem_thickening_iff_infEdist_lt := mem_thickening_iff_infEDist_lt

中文:
定理 mem_thickening_iff_infEDist_lt
  结论: x in thickening δ s ↔ infEDist x s < ENN实数.of实数 δ
  证明: Iff.rfl

@[deprecated (since := "2026-01-08")]
alias mem_thickening_iff_infEdist_lt := mem_thickening_iff_infEDist_lt

Depends on / 依赖: Iff.rfl
-/
theorem mem_thickening_iff_infEDist_lt : x in thickening δ s ↔ infEDist x s < ENNReal.ofReal δ :=
  Iff.rfl

@[deprecated (since := "2026-01-08")]
alias mem_thickening_iff_infEdist_lt := mem_thickening_iff_infEDist_lt

/--
lemma `eventually_notMem_thickening_of_infEDist_pos` / 引理 `eventually_notMem_thickening_of_infEDist_pos`

English:
lemma eventually_notMem_thickening_of_infEDist_pos
  given: {E : Set α} {x : α} (h : x ∉ closure E)
  proof: by
  obtain ⟨ε, ⟨ε_pos, ε_lt⟩⟩ := exists_real_pos_lt_infEDist_of_notMem_closure h
  filter_upwards [eventually_lt_nhds ε_pos] with δ hδ
  simp only [thickening, mem_ofPred_eq, not_lt]
  exact (ENNReal.ofReal_le_ofReal hδ.le).trans ε_lt.le

@[deprecated (since := "2026-01-08")]
alias eventually_notMe

中文:
引理 eventually_notMem_thickening_of_infEDist_pos
  条件: {E : Set α} {x : α} (h : x ∉ closure E)
  证明: by
  obtain ⟨ε, ⟨ε_pos, ε_lt⟩⟩ := exists_real_pos_lt_infEDist_of_notMem_closure h
  filter_upwards [eventually_lt_nhds ε_pos] with δ hδ
  simp only [thickening, mem_ofPred_eq, not_lt]
  exact (ENNReal.ofReal_le_ofReal hδ.le).trans ε_lt.le

@[deprecated (since := "2026-01-08")]
alias eventually_notMe

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal, _lt.le, eventually_lt_nhds, exists_real_pos_lt_infEDist_of_notMem_closure, filter_upwards, mem_ofPred_eq, not_lt, ofReal_le_ofReal, thickening
-/
lemma eventually_notMem_thickening_of_infEDist_pos {E : Set α} {x : α} (h : x ∉ closure E) :
    forallᶠ δ in 𝓝 (0 : Real), x ∉ Metric.thickening δ E := by
  obtain ⟨ε, ⟨ε_pos, ε_lt⟩⟩ := exists_real_pos_lt_infEDist_of_notMem_closure h
  filter_upwards [eventually_lt_nhds ε_pos] with δ hδ
  simp only [thickening, mem_ofPred_eq, not_lt]
  exact (ENNReal.ofReal_le_ofReal hδ.le).trans ε_lt.le

@[deprecated (since := "2026-01-08")]
alias eventually_notMem_thickening_of_infEdist_pos :=
  eventually_notMem_thickening_of_infEDist_pos

/--
theorem `thickening_eq_preimage_infEDist` / 定理 `thickening_eq_preimage_infEDist`

English:
theorem thickening_eq_preimage_infEDist
  given: (δ : Real) (E : Set α)
  proof: rfl

@[deprecated (since := "2026-01-08")]
alias thickening_eq_preimage_infEdist := thickening_eq_preimage_infEDist

中文:
定理 thickening_eq_preimage_infEDist
  条件: (δ : 实数) (E : Set α)
  证明: rfl

@[deprecated (since := "2026-01-08")]
alias thickening_eq_preimage_infEdist := thickening_eq_preimage_infEDist
-/
theorem thickening_eq_preimage_infEDist (δ : Real) (E : Set α) :
    thickening δ E = (infEDist · E) ⁻¹' Iio (ENNReal.ofReal δ) :=
  rfl

@[deprecated (since := "2026-01-08")]
alias thickening_eq_preimage_infEdist := thickening_eq_preimage_infEDist

/--
theorem `isOpen_thickening` / 定理 `isOpen_thickening`

English:
theorem isOpen_thickening
  given: {δ : Real} {E : Set α}
  statement: IsOpen (thickening δ E)
  proof: Continuous.isOpen_preimage continuous_infEDist _ isOpen_Iio

中文:
定理 isOpen_thickening
  条件: {δ : 实数} {E : Set α}
  结论: IsOpen (thickening δ E)
  证明: Continuous.isOpen_preimage continuous_infEDist _ isOpen_Iio

Depends on / 依赖: Continuous, Continuous.isOpen_preimage, continuous_infEDist, isOpen_Iio, isOpen_preimage
-/
theorem isOpen_thickening {δ : Real} {E : Set α} : IsOpen (thickening δ E) :=
  Continuous.isOpen_preimage continuous_infEDist _ isOpen_Iio

/-- The (open) thickening of the empty set is empty. -/
@[simp]
/--
theorem `thickening_empty` / 定理 `thickening_empty`

English:
theorem thickening_empty
  given: (δ : Real)
  statement: thickening δ (∅ : Set α) = ∅
  proof: by
  simp only [thickening, ofPred_false, infEDist_empty, not_top_lt]

中文:
定理 thickening_empty
  条件: (δ : 实数)
  结论: thickening δ (∅ : Set α) = ∅
  证明: by
  simp only [thickening, ofPred_false, infEDist_empty, not_top_lt]

Depends on / 依赖: infEDist_empty, not_top_lt, ofPred_false, thickening
-/
theorem thickening_empty (δ : Real) : thickening δ (∅ : Set α) = ∅ := by
  simp only [thickening, ofPred_false, infEDist_empty, not_top_lt]

/--
theorem `thickening_of_nonpos` / 定理 `thickening_of_nonpos`

English:
theorem thickening_of_nonpos
  given: (hδ : δ <= 0) (s : Set α)
  statement: thickening δ s = ∅
  proof: eq_empty_of_forall_notMem fun _ => ((ENNReal.ofReal_of_nonpos hδ).trans_le bot_le).not_gt

中文:
定理 thickening_of_nonpos
  条件: (hδ : δ <= 0) (s : Set α)
  结论: thickening δ s = ∅
  证明: eq_empty_of_forall_notMem fun _ => ((ENNReal.ofReal_of_nonpos hδ).trans_le bot_le).not_gt

Depends on / 依赖: ENNReal, ENNReal.ofReal_of_nonpos, bot_le, eq_empty_of_forall_notMem, not_gt, ofReal_of_nonpos, trans_le
-/
theorem thickening_of_nonpos (hδ : δ <= 0) (s : Set α) : thickening δ s = ∅ :=
  eq_empty_of_forall_notMem fun _ => ((ENNReal.ofReal_of_nonpos hδ).trans_le bot_le).not_gt

/-- The (open) thickening `Metric.thickening δ E` of a fixed subset `E` is an increasing function of
the thickening radius `δ`. -/
@[gcongr]
/--
theorem `thickening_mono` / 定理 `thickening_mono`

English:
theorem thickening_mono
  given: {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) (E : Set α)
  proof: preimage_mono (Iio_subset_Iio (ENNReal.ofReal_le_ofReal hle))

中文:
定理 thickening_mono
  条件: {δ₁ δ₂ : 实数} (hle : δ₁ <= δ₂) (E : Set α)
  证明: preimage_mono (Iio_subset_Iio (ENNReal.ofReal_le_ofReal hle))

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal, Iio_subset_Iio, ofReal_le_ofReal, preimage_mono
-/
theorem thickening_mono {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) (E : Set α) :
    thickening δ₁ E subseteq thickening δ₂ E :=
  preimage_mono (Iio_subset_Iio (ENNReal.ofReal_le_ofReal hle))

/--
theorem `thickening_subset_of_subset` / 定理 `thickening_subset_of_subset`

English:
theorem thickening_subset_of_subset
  given: (δ : Real) {E₁ E₂ : Set α} (h : E₁ subseteq E₂)
  proof: fun _ hx => lt_of_le_of_lt (infEDist_anti h) hx

中文:
定理 thickening_subset_of_subset
  条件: (δ : 实数) {E₁ E₂ : Set α} (h : E₁ subseteq E₂)
  证明: fun _ hx => lt_of_le_of_lt (infEDist_anti h) hx

Depends on / 依赖: infEDist_anti, lt_of_le_of_lt
-/
theorem thickening_subset_of_subset (δ : Real) {E₁ E₂ : Set α} (h : E₁ subseteq E₂) :
    thickening δ E₁ subseteq thickening δ E₂ := fun _ hx => lt_of_le_of_lt (infEDist_anti h) hx

/--
theorem `mem_thickening_iff_exists_edist_lt` / 定理 `mem_thickening_iff_exists_edist_lt`

English:
theorem mem_thickening_iff_exists_edist_lt
  given: {δ : Real} (E : Set α) (x : α)
  proof: infEDist_lt_iff

中文:
定理 mem_thickening_iff_exists_edist_lt
  条件: {δ : 实数} (E : Set α) (x : α)
  证明: infEDist_lt_iff

Depends on / 依赖: infEDist_lt_iff
-/
theorem mem_thickening_iff_exists_edist_lt {δ : Real} (E : Set α) (x : α) :
    x in thickening δ E ↔ exists z in E, edist x z < ENNReal.ofReal δ :=
  infEDist_lt_iff

/--
theorem `frontier_thickening_subset` / 定理 `frontier_thickening_subset`

English:
theorem frontier_thickening_subset
  given: (E : Set α) {δ : Real}
  proof: frontier_lt_subset_eq continuous_infEDist continuous_const

中文:
定理 frontier_thickening_subset
  条件: (E : Set α) {δ : 实数}
  证明: frontier_lt_subset_eq continuous_infEDist continuous_const

Depends on / 依赖: continuous_const, continuous_infEDist, frontier_lt_subset_eq
-/
theorem frontier_thickening_subset (E : Set α) {δ : Real} :
    frontier (thickening δ E) subseteq { x : α | infEDist x E = ENNReal.ofReal δ } :=
  frontier_lt_subset_eq continuous_infEDist continuous_const

open scoped Function in -- required for scoped `on` notation
/--
theorem `frontier_thickening_disjoint` / 定理 `frontier_thickening_disjoint`

English:
theorem frontier_thickening_disjoint
  given: (A : Set α)
  proof: by
  refine (pairwise_disjoint_on _).2 fun r₁ r₂ hr => ?_
  rcases le_total r₁ 0 with h₁ | h₁
  · simp [thickening_of_nonpos h₁]
  refine ((disjoint_singleton.2 fun h => hr.ne ?_).preimage _).mono (frontier_thickening_subset _)
    (frontier_thickening_subset _)
  apply_fun ENNReal.toReal at h
  rwa

中文:
定理 frontier_thickening_disjoint
  条件: (A : Set α)
  证明: by
  refine (pairwise_disjoint_on _).2 fun r₁ r₂ hr => ?_
  rcases le_total r₁ 0 with h₁ | h₁
  · simp [thickening_of_nonpos h₁]
  refine ((disjoint_singleton.2 fun h => hr.ne ?_).preimage _).mono (frontier_thickening_subset _)
    (frontier_thickening_subset _)
  apply_fun ENNReal.toReal at h
  rwa

Depends on / 依赖: ENNReal, ENNReal.toReal, ENNReal.toReal_ofReal, apply_fun, disjoint_singleton, frontier_thickening_subset, hr.le, hr.ne, le_total, pairwise_disjoint_on, preimage, thickening_of_nonpos, toReal, toReal_ofReal
-/
theorem frontier_thickening_disjoint (A : Set α) :
    Pairwise (Disjoint on fun r : Real => frontier (thickening r A)) := by
  refine (pairwise_disjoint_on _).2 fun r₁ r₂ hr => ?_
  rcases le_total r₁ 0 with h₁ | h₁
  · simp [thickening_of_nonpos h₁]
  refine ((disjoint_singleton.2 fun h => hr.ne ?_).preimage _).mono (frontier_thickening_subset _)
    (frontier_thickening_subset _)
  apply_fun ENNReal.toReal at h
  rwa [ENNReal.toReal_ofReal h₁, ENNReal.toReal_ofReal (h₁.trans hr.le)] at h

/--
lemma `subset_compl_thickening_compl_thickening_self` / 引理 `subset_compl_thickening_compl_thickening_self`

English:
lemma subset_compl_thickening_compl_thickening_self
  given: (δ : Real) (E : Set α)
  proof: by
  intro x x_in_E
  simp only [thickening, mem_compl_iff, mem_ofPred_eq, not_lt]
  apply le_infEDist.mpr fun y hy => ?_
  simp only [mem_compl_iff, mem_ofPred_eq, not_lt] at hy
simpa only [edist_comm] using le_trans hy Metric.infEDist_le_edist_of_mem x_in_E

中文:
引理 subset_compl_thickening_compl_thickening_self
  条件: (δ : 实数) (E : Set α)
  证明: by
  intro x x_in_E
  simp only [thickening, mem_compl_iff, mem_ofPred_eq, not_lt]
  apply le_infEDist.mpr fun y hy => ?_
  simp only [mem_compl_iff, mem_ofPred_eq, not_lt] at hy
simpa only [edist_comm] using le_trans hy Metric.infEDist_le_edist_of_mem x_in_E

Depends on / 依赖: Metric, Metric.infEDist_le_edist_of_mem, edist_comm, infEDist_le_edist_of_mem, le_infEDist, le_infEDist.mpr, le_trans, mem_compl_iff, mem_ofPred_eq, not_lt, thickening, x_in_E
-/
lemma subset_compl_thickening_compl_thickening_self (δ : Real) (E : Set α) :
    E subseteq (thickening δ (thickening δ E)ᶜ)ᶜ := by
  intro x x_in_E
  simp only [thickening, mem_compl_iff, mem_ofPred_eq, not_lt]
  apply le_infEDist.mpr fun y hy => ?_
  simp only [mem_compl_iff, mem_ofPred_eq, not_lt] at hy
simpa only [edist_comm] using le_trans hy Metric.infEDist_le_edist_of_mem x_in_E

/--
lemma `thickening_compl_thickening_self_subset_compl` / 引理 `thickening_compl_thickening_self_subset_compl`

English:
lemma thickening_compl_thickening_self_subset_compl
  given: (δ : Real) (E : Set α)
  proof: by
  apply compl_subset_compl.mp
  simpa only [compl_compl] using subset_compl_thickening_compl_thickening_self δ E

中文:
引理 thickening_compl_thickening_self_subset_compl
  条件: (δ : 实数) (E : Set α)
  证明: by
  apply compl_subset_compl.mp
  simpa only [compl_compl] using subset_compl_thickening_compl_thickening_self δ E

Depends on / 依赖: compl_compl, compl_subset_compl, compl_subset_compl.mp, subset_compl_thickening_compl_thickening_self
-/
lemma thickening_compl_thickening_self_subset_compl (δ : Real) (E : Set α) :
    thickening δ (thickening δ E)ᶜ subseteq Eᶜ := by
  apply compl_subset_compl.mp
  simpa only [compl_compl] using subset_compl_thickening_compl_thickening_self δ E

variable {X : Type u} [PseudoMetricSpace X]

/--
theorem `mem_thickening_iff_infDist_lt` / 定理 `mem_thickening_iff_infDist_lt`

English:
theorem mem_thickening_iff_infDist_lt
  given: {E : Set X} {x : X} (h : E.Nonempty)
  proof: lt_ofReal_iff_toReal_lt (infEDist_ne_top h)

中文:
定理 mem_thickening_iff_infDist_lt
  条件: {E : Set X} {x : X} (h : E.Nonempty)
  证明: lt_ofReal_iff_toReal_lt (infEDist_ne_top h)

Depends on / 依赖: infEDist_ne_top, lt_ofReal_iff_toReal_lt
-/
theorem mem_thickening_iff_infDist_lt {E : Set X} {x : X} (h : E.Nonempty) :
    x in thickening δ E ↔ infDist x E < δ :=
  lt_ofReal_iff_toReal_lt (infEDist_ne_top h)

/--
theorem `mem_thickening_iff` / 定理 `mem_thickening_iff`

English:
theorem mem_thickening_iff
  given: {E : Set X} {x : X}
  statement: x in thickening δ E ↔ exists z in E, dist x z < δ
  proof: by
  have key_iff : forall z : X, edist x z < ENNReal.ofReal δ ↔ dist x z < δ := fun z => by
    rw [dist_edist]; rw [lt_ofReal_iff_toReal_lt (edist_ne_top _ _)]
  simp_rw [mem_thickening_iff_exists_edist_lt, key_iff]

@[simp]

中文:
定理 mem_thickening_iff
  条件: {E : Set X} {x : X}
  结论: x in thickening δ E ↔ 存在 z in E, dist x z < δ
  证明: by
  have key_iff : forall z : X, edist x z < ENNReal.ofReal δ ↔ dist x z < δ := fun z => by
    rw [dist_edist]; rw [lt_ofReal_iff_toReal_lt (edist_ne_top _ _)]
  simp_rw [mem_thickening_iff_exists_edist_lt, key_iff]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal, dist_edist, edist_ne_top, key_iff, lt_ofReal_iff_toReal_lt, mem_thickening_iff_exists_edist_lt, ofReal, simp_rw
-/
theorem mem_thickening_iff {E : Set X} {x : X} : x in thickening δ E ↔ exists z in E, dist x z < δ := by
  have key_iff : forall z : X, edist x z < ENNReal.ofReal δ ↔ dist x z < δ := fun z => by
    rw [dist_edist]; rw [lt_ofReal_iff_toReal_lt (edist_ne_top _ _)]
  simp_rw [mem_thickening_iff_exists_edist_lt, key_iff]

@[simp]
/--
theorem `thickening_singleton` / 定理 `thickening_singleton`

English:
theorem thickening_singleton
  given: (δ : Real) (x : X)
  statement: thickening δ ({x} : Set X) = ball x δ
  proof: by
  ext
  simp [mem_thickening_iff]

中文:
定理 thickening_singleton
  条件: (δ : 实数) (x : X)
  结论: thickening δ ({x} : Set X) = ball x δ
  证明: by
  ext
  simp [mem_thickening_iff]

Depends on / 依赖: mem_thickening_iff
-/
theorem thickening_singleton (δ : Real) (x : X) : thickening δ ({x} : Set X) = ball x δ := by
  ext
  simp [mem_thickening_iff]

/--
theorem `ball_subset_thickening` / 定理 `ball_subset_thickening`

English:
theorem ball_subset_thickening
  given: {x : X} {E : Set X} (hx : x in E) (δ : Real)
  proof: Subset.trans (by simp) (thickening_subset_of_subset δ <| singleton_subset_iff.mpr hx)

中文:
定理 ball_subset_thickening
  条件: {x : X} {E : Set X} (hx : x in E) (δ : 实数)
  证明: Subset.trans (by simp) (thickening_subset_of_subset δ <| singleton_subset_iff.mpr hx)

Depends on / 依赖: Subset, Subset.trans, singleton_subset_iff, singleton_subset_iff.mpr, thickening_subset_of_subset
-/
theorem ball_subset_thickening {x : X} {E : Set X} (hx : x in E) (δ : Real) :
    ball x δ subseteq thickening δ E :=
  Subset.trans (by simp) (thickening_subset_of_subset δ <| singleton_subset_iff.mpr hx)

/--
theorem `thickening_eq_biUnion_ball` / 定理 `thickening_eq_biUnion_ball`

English:
theorem thickening_eq_biUnion_ball
  given: {δ : Real} {E : Set X}
  statement: thickening δ E = ⋃ x in E, ball x δ
  proof: by
  ext x
  simp only [mem_iUnion₂, exists_prop]
  exact mem_thickening_iff

中文:
定理 thickening_eq_biUnion_ball
  条件: {δ : 实数} {E : Set X}
  结论: thickening δ E = ⋃ x in E, ball x δ
  证明: by
  ext x
  simp only [mem_iUnion₂, exists_prop]
  exact mem_thickening_iff

Depends on / 依赖: exists_prop, mem_thickening_iff
-/
theorem thickening_eq_biUnion_ball {δ : Real} {E : Set X} : thickening δ E = ⋃ x in E, ball x δ := by
  ext x
  simp only [mem_iUnion₂, exists_prop]
  exact mem_thickening_iff

/--
theorem `_root_.Bornology.IsBounded.thickening` / 定理 `_root_.Bornology.IsBounded.thickening`

English:
theorem _root_.Bornology.IsBounded.thickening
  given: {δ : Real} {E : Set X} (h : IsBounded E)
  proof: by
  rcases E.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · refine (isBounded_iff_subset_closedBall x).2 ⟨δ + diam E, fun y hy => ?_⟩
    calc
      dist y x <= infDist y E + diam E := dist_le_infDist_add_diam (x := y) h hx
      _ <= δ + diam E := by grw [(mem_thickening_iff_infDist_lt ⟨x, h

中文:
定理 _root_.Bornology.IsBounded.thickening
  条件: {δ : 实数} {E : Set X} (h : IsBounded E)
  证明: by
  rcases E.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · refine (isBounded_iff_subset_closedBall x).2 ⟨δ + diam E, fun y hy => ?_⟩
    calc
      dist y x <= infDist y E + diam E := dist_le_infDist_add_diam (x := y) h hx
      _ <= δ + diam E := by grw [(mem_thickening_iff_infDist_lt ⟨x, h
-/
protected theorem _root_.Bornology.IsBounded.thickening {δ : Real} {E : Set X} (h : IsBounded E) :
    IsBounded (thickening δ E) := by
  rcases E.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · refine (isBounded_iff_subset_closedBall x).2 ⟨δ + diam E, fun y hy => ?_⟩
    calc
      dist y x <= infDist y E + diam E := dist_le_infDist_add_diam (x := y) h hx
      _ <= δ + diam E := by grw [(mem_thickening_iff_infDist_lt ⟨x, hx⟩).1 hy]

end Thickening

section Cthickening

variable [PseudoEMetricSpace α] {δ ε : Real} {s t : Set α} {x : α}

open EMetric

/--
Definition of `cthickening` / `cthickening` 的定义

English:
definition cthickening
  signature: (δ : Real) (E : Set α)
  body: { x : α | infEDist x E <= ENNReal.ofReal δ }

@[simp]

中文:
定义 cthickening
  签名: (δ : 实数) (E : Set α)
  定义体: { x : α | infEDist x E <= ENNReal.ofReal δ }

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal, infEDist, ofReal
-/
def cthickening (δ : Real) (E : Set α) : Set α :=
  { x : α | infEDist x E <= ENNReal.ofReal δ }

@[simp]
/--
theorem `mem_cthickening_iff` / 定理 `mem_cthickening_iff`

English:
theorem mem_cthickening_iff
  statement: x in cthickening δ s ↔ infEDist x s <= ENNReal.ofReal δ
  proof: Iff.rfl

中文:
定理 mem_cthickening_iff
  结论: x in cthickening δ s ↔ infEDist x s <= ENN实数.of实数 δ
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_cthickening_iff : x in cthickening δ s ↔ infEDist x s <= ENNReal.ofReal δ :=
  Iff.rfl

/--
lemma `eventually_notMem_cthickening_of_infEDist_pos` / 引理 `eventually_notMem_cthickening_of_infEDist_pos`

English:
lemma eventually_notMem_cthickening_of_infEDist_pos
  given: {E : Set α} {x : α} (h : x ∉ closure E)
  proof: by
  obtain ⟨ε, ⟨ε_pos, ε_lt⟩⟩ := exists_real_pos_lt_infEDist_of_notMem_closure h
  filter_upwards [eventually_lt_nhds ε_pos] with δ hδ
  simp only [cthickening, mem_ofPred_eq, not_le]
  exact ((ofReal_lt_ofReal_iff ε_pos).mpr hδ).trans ε_lt

@[deprecated (since := "2026-01-08")]
alias eventually_no

中文:
引理 eventually_notMem_cthickening_of_infEDist_pos
  条件: {E : Set α} {x : α} (h : x ∉ closure E)
  证明: by
  obtain ⟨ε, ⟨ε_pos, ε_lt⟩⟩ := exists_real_pos_lt_infEDist_of_notMem_closure h
  filter_upwards [eventually_lt_nhds ε_pos] with δ hδ
  simp only [cthickening, mem_ofPred_eq, not_le]
  exact ((ofReal_lt_ofReal_iff ε_pos).mpr hδ).trans ε_lt

@[deprecated (since := "2026-01-08")]
alias eventually_no

Depends on / 依赖: cthickening, eventually_lt_nhds, exists_real_pos_lt_infEDist_of_notMem_closure, filter_upwards, mem_ofPred_eq, not_le, ofReal_lt_ofReal_iff
-/
lemma eventually_notMem_cthickening_of_infEDist_pos {E : Set α} {x : α} (h : x ∉ closure E) :
    forallᶠ δ in 𝓝 (0 : Real), x ∉ Metric.cthickening δ E := by
  obtain ⟨ε, ⟨ε_pos, ε_lt⟩⟩ := exists_real_pos_lt_infEDist_of_notMem_closure h
  filter_upwards [eventually_lt_nhds ε_pos] with δ hδ
  simp only [cthickening, mem_ofPred_eq, not_le]
  exact ((ofReal_lt_ofReal_iff ε_pos).mpr hδ).trans ε_lt

@[deprecated (since := "2026-01-08")]
alias eventually_notMem_cthickening_of_infEdist_pos :=
  eventually_notMem_cthickening_of_infEDist_pos

/--
theorem `mem_cthickening_of_edist_le` / 定理 `mem_cthickening_of_edist_le`

English:
theorem mem_cthickening_of_edist_le
  statement: (x y : α) (δ : Real) (E : Set α) (h : y in E)
  proof: (infEDist_le_edist_of_mem h).trans h'

中文:
定理 mem_cthickening_of_edist_le
  结论: (x y : α) (δ : 实数) (E : Set α) (h : y in E)
  证明: (infEDist_le_edist_of_mem h).trans h'

Depends on / 依赖: infEDist_le_edist_of_mem
-/
theorem mem_cthickening_of_edist_le (x y : α) (δ : Real) (E : Set α) (h : y in E)
    (h' : edist x y <= ENNReal.ofReal δ) : x in cthickening δ E :=
  (infEDist_le_edist_of_mem h).trans h'

/--
theorem `mem_cthickening_of_dist_le` / 定理 `mem_cthickening_of_dist_le`

English:
theorem mem_cthickening_of_dist_le
  statement: {α : Type*} [PseudoMetricSpace α] (x y : α) (δ : Real) (E : Set α)
  proof: by
  apply mem_cthickening_of_edist_le x y δ E h
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal h'

中文:
定理 mem_cthickening_of_dist_le
  结论: {α : 类型} [PseudoMetricSpace α] (x y : α) (δ : 实数) (E : Set α)
  证明: by
  apply mem_cthickening_of_edist_le x y δ E h
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal h'

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal, edist_dist, mem_cthickening_of_edist_le, ofReal_le_ofReal
-/
theorem mem_cthickening_of_dist_le {α : Type*} [PseudoMetricSpace α] (x y : α) (δ : Real) (E : Set α)
    (h : y in E) (h' : dist x y <= δ) : x in cthickening δ E := by
  apply mem_cthickening_of_edist_le x y δ E h
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal h'

/--
theorem `cthickening_eq_preimage_infEDist` / 定理 `cthickening_eq_preimage_infEDist`

English:
theorem cthickening_eq_preimage_infEDist
  given: (δ : Real) (E : Set α)
  proof: rfl

@[deprecated (since := "2026-01-08")]
alias cthickening_eq_preimage_infEdist := cthickening_eq_preimage_infEDist

中文:
定理 cthickening_eq_preimage_infEDist
  条件: (δ : 实数) (E : Set α)
  证明: rfl

@[deprecated (since := "2026-01-08")]
alias cthickening_eq_preimage_infEdist := cthickening_eq_preimage_infEDist
-/
theorem cthickening_eq_preimage_infEDist (δ : Real) (E : Set α) :
    cthickening δ E = (fun x => infEDist x E) ⁻¹' Iic (ENNReal.ofReal δ) :=
  rfl

@[deprecated (since := "2026-01-08")]
alias cthickening_eq_preimage_infEdist := cthickening_eq_preimage_infEDist

/--
theorem `isClosed_cthickening` / 定理 `isClosed_cthickening`

English:
theorem isClosed_cthickening
  given: {δ : Real} {E : Set α}
  statement: IsClosed (cthickening δ E)
  proof: IsClosed.preimage continuous_infEDist isClosed_Iic

中文:
定理 isClosed_cthickening
  条件: {δ : 实数} {E : Set α}
  结论: IsClosed (cthickening δ E)
  证明: IsClosed.preimage continuous_infEDist isClosed_Iic

Depends on / 依赖: IsClosed, IsClosed.preimage, continuous_infEDist, isClosed_Iic, preimage
-/
theorem isClosed_cthickening {δ : Real} {E : Set α} : IsClosed (cthickening δ E) :=
  IsClosed.preimage continuous_infEDist isClosed_Iic

/-- The closed thickening of the empty set is empty. -/
@[simp]
/--
theorem `cthickening_empty` / 定理 `cthickening_empty`

English:
theorem cthickening_empty
  given: (δ : Real)
  statement: cthickening δ (∅ : Set α) = ∅
  proof: by
  simp only [cthickening, ENNReal.ofReal_ne_top, ofPred_false, infEDist_empty, top_le_iff]

中文:
定理 cthickening_empty
  条件: (δ : 实数)
  结论: cthickening δ (∅ : Set α) = ∅
  证明: by
  simp only [cthickening, ENNReal.ofReal_ne_top, ofPred_false, infEDist_empty, top_le_iff]

Depends on / 依赖: ENNReal, ENNReal.ofReal_ne_top, cthickening, infEDist_empty, ofPred_false, ofReal_ne_top, top_le_iff
-/
theorem cthickening_empty (δ : Real) : cthickening δ (∅ : Set α) = ∅ := by
  simp only [cthickening, ENNReal.ofReal_ne_top, ofPred_false, infEDist_empty, top_le_iff]

/--
theorem `cthickening_of_nonpos` / 定理 `cthickening_of_nonpos`

English:
theorem cthickening_of_nonpos
  given: {δ : Real} (hδ : δ <= 0) (E : Set α)
  statement: cthickening δ E = closure E
  proof: by
  ext x
  simp [mem_closure_iff_infEDist_zero, cthickening, ENNReal.ofReal_eq_zero.2 hδ]

中文:
定理 cthickening_of_nonpos
  条件: {δ : 实数} (hδ : δ <= 0) (E : Set α)
  结论: cthickening δ E = closure E
  证明: by
  ext x
  simp [mem_closure_iff_infEDist_zero, cthickening, ENNReal.ofReal_eq_zero.2 hδ]

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_zero, cthickening, mem_closure_iff_infEDist_zero, ofReal_eq_zero
-/
theorem cthickening_of_nonpos {δ : Real} (hδ : δ <= 0) (E : Set α) : cthickening δ E = closure E := by
  ext x
  simp [mem_closure_iff_infEDist_zero, cthickening, ENNReal.ofReal_eq_zero.2 hδ]

/-- The closed thickening with radius zero is the closure of the set. -/
@[simp]
/--
theorem `cthickening_zero` / 定理 `cthickening_zero`

English:
theorem cthickening_zero
  given: (E : Set α)
  statement: cthickening 0 E = closure E
  proof: cthickening_of_nonpos le_rfl E

中文:
定理 cthickening_zero
  条件: (E : Set α)
  结论: cthickening 0 E = closure E
  证明: cthickening_of_nonpos le_rfl E

Depends on / 依赖: cthickening_of_nonpos, le_rfl
-/
theorem cthickening_zero (E : Set α) : cthickening 0 E = closure E :=
  cthickening_of_nonpos le_rfl E

/--
theorem `cthickening_max_zero` / 定理 `cthickening_max_zero`

English:
theorem cthickening_max_zero
  given: (δ : Real) (E : Set α)
  statement: cthickening (max 0 δ) E = cthickening δ E
  proof: by
  cases le_total δ 0 <;> simp [cthickening_of_nonpos, *]

中文:
定理 cthickening_max_zero
  条件: (δ : 实数) (E : Set α)
  结论: cthickening (max 0 δ) E = cthickening δ E
  证明: by
  cases le_total δ 0 <;> simp [cthickening_of_nonpos, *]

Depends on / 依赖: cthickening_of_nonpos, le_total
-/
theorem cthickening_max_zero (δ : Real) (E : Set α) : cthickening (max 0 δ) E = cthickening δ E := by
  cases le_total δ 0 <;> simp [cthickening_of_nonpos, *]

/--
theorem `cthickening_mono` / 定理 `cthickening_mono`

English:
theorem cthickening_mono
  given: {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) (E : Set α)
  proof: preimage_mono (Iic_subset_Iic.mpr (ENNReal.ofReal_le_ofReal hle))

@[simp]

中文:
定理 cthickening_mono
  条件: {δ₁ δ₂ : 实数} (hle : δ₁ <= δ₂) (E : Set α)
  证明: preimage_mono (Iic_subset_Iic.mpr (ENNReal.ofReal_le_ofReal hle))

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal, Iic_subset_Iic, Iic_subset_Iic.mpr, ofReal_le_ofReal, preimage_mono
-/
theorem cthickening_mono {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) (E : Set α) :
    cthickening δ₁ E subseteq cthickening δ₂ E :=
  preimage_mono (Iic_subset_Iic.mpr (ENNReal.ofReal_le_ofReal hle))

@[simp]
/--
theorem `cthickening_singleton` / 定理 `cthickening_singleton`

English:
theorem cthickening_singleton
  given: {α : Type*} [PseudoMetricSpace α] (x : α) {δ : Real} (hδ : 0 <= δ)
  proof: by
  ext y
  simp [cthickening, edist_dist, ENNReal.ofReal_le_ofReal_iff hδ]

中文:
定理 cthickening_singleton
  条件: {α : 类型} [PseudoMetricSpace α] (x : α) {δ : 实数} (hδ : 0 <= δ)
  证明: by
  ext y
  simp [cthickening, edist_dist, ENNReal.ofReal_le_ofReal_iff hδ]

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal_iff, cthickening, edist_dist, ofReal_le_ofReal_iff
-/
theorem cthickening_singleton {α : Type*} [PseudoMetricSpace α] (x : α) {δ : Real} (hδ : 0 <= δ) :
    cthickening δ ({x} : Set α) = closedBall x δ := by
  ext y
  simp [cthickening, edist_dist, ENNReal.ofReal_le_ofReal_iff hδ]

/--
theorem `closedBall_subset_cthickening_singleton` / 定理 `closedBall_subset_cthickening_singleton`

English:
theorem closedBall_subset_cthickening_singleton
  given: {α : Type*} [PseudoMetricSpace α] (x : α) (δ : Real)
  proof: by
  rcases lt_or_ge δ 0 with (hδ | hδ)
  · simp only [closedBall_eq_empty.mpr hδ, empty_subset]
  · simp only [cthickening_singleton x hδ, Subset.rfl]

中文:
定理 closedBall_subset_cthickening_singleton
  条件: {α : 类型} [PseudoMetricSpace α] (x : α) (δ : 实数)
  证明: by
  rcases lt_or_ge δ 0 with (hδ | hδ)
  · simp only [closedBall_eq_empty.mpr hδ, empty_subset]
  · simp only [cthickening_singleton x hδ, Subset.rfl]

Depends on / 依赖: Subset, Subset.rfl, closedBall_eq_empty, closedBall_eq_empty.mpr, cthickening_singleton, empty_subset, lt_or_ge
-/
theorem closedBall_subset_cthickening_singleton {α : Type*} [PseudoMetricSpace α] (x : α) (δ : Real) :
    closedBall x δ subseteq cthickening δ ({x} : Set α) := by
  rcases lt_or_ge δ 0 with (hδ | hδ)
  · simp only [closedBall_eq_empty.mpr hδ, empty_subset]
  · simp only [cthickening_singleton x hδ, Subset.rfl]

/--
theorem `cthickening_subset_of_subset` / 定理 `cthickening_subset_of_subset`

English:
theorem cthickening_subset_of_subset
  given: (δ : Real) {E₁ E₂ : Set α} (h : E₁ subseteq E₂)
  proof: fun _ hx => le_trans (infEDist_anti h) hx

中文:
定理 cthickening_subset_of_subset
  条件: (δ : 实数) {E₁ E₂ : Set α} (h : E₁ subseteq E₂)
  证明: fun _ hx => le_trans (infEDist_anti h) hx

Depends on / 依赖: infEDist_anti, le_trans
-/
theorem cthickening_subset_of_subset (δ : Real) {E₁ E₂ : Set α} (h : E₁ subseteq E₂) :
    cthickening δ E₁ subseteq cthickening δ E₂ := fun _ hx => le_trans (infEDist_anti h) hx

/--
theorem `cthickening_subset_thickening` / 定理 `cthickening_subset_thickening`

English:
theorem cthickening_subset_thickening
  given: {δ₁ : Real>=0} {δ₂ : Real} (hlt : (δ₁ : Real) < δ₂) (E : Set α)
  proof: fun _ hx =>
  hx.out.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt δ₁.prop hlt)).mpr hlt)

中文:
定理 cthickening_subset_thickening
  条件: {δ₁ : 实数>=0} {δ₂ : 实数} (hlt : (δ₁ : 实数) < δ₂) (E : Set α)
  证明: fun _ hx =>
  hx.out.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt δ₁.prop hlt)).mpr hlt)
-/
theorem cthickening_subset_thickening {δ₁ : Real>=0} {δ₂ : Real} (hlt : (δ₁ : Real) < δ₂) (E : Set α) :
    cthickening δ₁ E subseteq thickening δ₂ E := fun _ hx =>
  hx.out.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt δ₁.prop hlt)).mpr hlt)

/--
theorem `cthickening_subset_thickening'` / 定理 `cthickening_subset_thickening'`

English:
theorem cthickening_subset_thickening'
  given: {δ₁ δ₂ : Real} (δ₂_pos : 0 < δ₂) (hlt : δ₁ < δ₂) (E : Set α)
  proof: fun _ hx =>
  lt_of_le_of_lt hx.out ((ENNReal.ofReal_lt_ofReal_iff δ₂_pos).mpr hlt)

中文:
定理 cthickening_subset_thickening'
  条件: {δ₁ δ₂ : 实数} (δ₂_pos : 0 < δ₂) (hlt : δ₁ < δ₂) (E : Set α)
  证明: fun _ hx =>
  lt_of_le_of_lt hx.out ((ENNReal.ofReal_lt_ofReal_iff δ₂_pos).mpr hlt)
-/
theorem cthickening_subset_thickening' {δ₁ δ₂ : Real} (δ₂_pos : 0 < δ₂) (hlt : δ₁ < δ₂) (E : Set α) :
    cthickening δ₁ E subseteq thickening δ₂ E := fun _ hx =>
  lt_of_le_of_lt hx.out ((ENNReal.ofReal_lt_ofReal_iff δ₂_pos).mpr hlt)

/--
theorem `thickening_subset_cthickening` / 定理 `thickening_subset_cthickening`

English:
theorem thickening_subset_cthickening
  given: (δ : Real) (E : Set α)
  statement: thickening δ E subseteq cthickening δ E
  proof: by
  intro x hx
  rw [thickening]; rw [mem_ofPred_eq] at hx
  exact hx.le

中文:
定理 thickening_subset_cthickening
  条件: (δ : 实数) (E : Set α)
  结论: thickening δ E subseteq cthickening δ E
  证明: by
  intro x hx
  rw [thickening]; rw [mem_ofPred_eq] at hx
  exact hx.le

Depends on / 依赖: hx.le, mem_ofPred_eq, thickening
-/
theorem thickening_subset_cthickening (δ : Real) (E : Set α) : thickening δ E subseteq cthickening δ E := by
  intro x hx
  rw [thickening]; rw [mem_ofPred_eq] at hx
  exact hx.le

/--
theorem `thickening_subset_cthickening_of_le` / 定理 `thickening_subset_cthickening_of_le`

English:
theorem thickening_subset_cthickening_of_le
  given: {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) (E : Set α)
  proof: (thickening_subset_cthickening δ₁ E).trans (cthickening_mono hle E)

中文:
定理 thickening_subset_cthickening_of_le
  条件: {δ₁ δ₂ : 实数} (hle : δ₁ <= δ₂) (E : Set α)
  证明: (thickening_subset_cthickening δ₁ E).trans (cthickening_mono hle E)

Depends on / 依赖: cthickening_mono, thickening_subset_cthickening
-/
theorem thickening_subset_cthickening_of_le {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) (E : Set α) :
    thickening δ₁ E subseteq cthickening δ₂ E :=
  (thickening_subset_cthickening δ₁ E).trans (cthickening_mono hle E)

/--
theorem `_root_.Bornology.IsBounded.cthickening` / 定理 `_root_.Bornology.IsBounded.cthickening`

English:
theorem _root_.Bornology.IsBounded.cthickening
  statement: {α : Type*} [PseudoMetricSpace α] {δ : Real} {E : Set α}
  proof: by
  have : IsBounded (thickening (max (δ + 1) 1) E) := h.thickening
  apply this.subset
  exact cthickening_subset_thickening' (zero_lt_one.trans_le (le_max_right _ _))
    ((lt_add_one _).trans_le (le_max_left _ _)) _

中文:
定理 _root_.Bornology.IsBounded.cthickening
  结论: {α : 类型} [PseudoMetricSpace α] {δ : 实数} {E : Set α}
  证明: by
  have : IsBounded (thickening (max (δ + 1) 1) E) := h.thickening
  apply this.subset
  exact cthickening_subset_thickening' (zero_lt_one.trans_le (le_max_right _ _))
    ((lt_add_one _).trans_le (le_max_left _ _)) _

Depends on / 依赖: IsBounded, cthickening_subset_thickening, h.thickening, le_max_left, le_max_right, lt_add_one, subset, thickening, this.subset, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem _root_.Bornology.IsBounded.cthickening {α : Type*} [PseudoMetricSpace α] {δ : Real} {E : Set α}
    (h : IsBounded E) : IsBounded (cthickening δ E) := by
  have : IsBounded (thickening (max (δ + 1) 1) E) := h.thickening
  apply this.subset
  exact cthickening_subset_thickening' (zero_lt_one.trans_le (le_max_right _ _))
    ((lt_add_one _).trans_le (le_max_left _ _)) _

/--
theorem `_root_.IsCompact.cthickening` / 定理 `_root_.IsCompact.cthickening`

English:
theorem _root_.IsCompact.cthickening
  proof: isCompact_of_isClosed_isBounded isClosed_cthickening hs.isBounded.cthickening

中文:
定理 _root_.IsCompact.cthickening
  证明: isCompact_of_isClosed_isBounded isClosed_cthickening hs.isBounded.cthickening
-/
protected theorem _root_.IsCompact.cthickening
    {α : Type*} [PseudoMetricSpace α] [ProperSpace α] {s : Set α}
    (hs : IsCompact s) {r : Real} : IsCompact (cthickening r s) :=
  isCompact_of_isClosed_isBounded isClosed_cthickening hs.isBounded.cthickening

/--
theorem `thickening_subset_interior_cthickening` / 定理 `thickening_subset_interior_cthickening`

English:
theorem thickening_subset_interior_cthickening
  given: (δ : Real) (E : Set α)
  proof: (subset_interior_iff_isOpen.mpr isOpen_thickening).trans
    (interior_mono (thickening_subset_cthickening δ E))

中文:
定理 thickening_subset_interior_cthickening
  条件: (δ : 实数) (E : Set α)
  证明: (subset_interior_iff_isOpen.mpr isOpen_thickening).trans
    (interior_mono (thickening_subset_cthickening δ E))

Depends on / 依赖: interior_mono, isOpen_thickening, subset_interior_iff_isOpen, subset_interior_iff_isOpen.mpr, thickening_subset_cthickening
-/
theorem thickening_subset_interior_cthickening (δ : Real) (E : Set α) :
    thickening δ E subseteq interior (cthickening δ E) :=
  (subset_interior_iff_isOpen.mpr isOpen_thickening).trans
    (interior_mono (thickening_subset_cthickening δ E))

/--
theorem `closure_thickening_subset_cthickening` / 定理 `closure_thickening_subset_cthickening`

English:
theorem closure_thickening_subset_cthickening
  given: (δ : Real) (E : Set α)
  proof: (closure_mono (thickening_subset_cthickening δ E)).trans isClosed_cthickening.closure_subset

中文:
定理 closure_thickening_subset_cthickening
  条件: (δ : 实数) (E : Set α)
  证明: (closure_mono (thickening_subset_cthickening δ E)).trans isClosed_cthickening.closure_subset

Depends on / 依赖: closure_mono, closure_subset, isClosed_cthickening, isClosed_cthickening.closure_subset, thickening_subset_cthickening
-/
theorem closure_thickening_subset_cthickening (δ : Real) (E : Set α) :
    closure (thickening δ E) subseteq cthickening δ E :=
  (closure_mono (thickening_subset_cthickening δ E)).trans isClosed_cthickening.closure_subset

/--
theorem `closure_subset_cthickening` / 定理 `closure_subset_cthickening`

English:
theorem closure_subset_cthickening
  given: (δ : Real) (E : Set α)
  statement: closure E subseteq cthickening δ E
  proof: by
  rw [← cthickening_of_nonpos (min_le_right δ 0)]
  exact cthickening_mono (min_le_left δ 0) E

中文:
定理 closure_subset_cthickening
  条件: (δ : 实数) (E : Set α)
  结论: closure E subseteq cthickening δ E
  证明: by
  rw [← cthickening_of_nonpos (min_le_right δ 0)]
  exact cthickening_mono (min_le_left δ 0) E

Depends on / 依赖: cthickening_mono, cthickening_of_nonpos, min_le_left, min_le_right
-/
theorem closure_subset_cthickening (δ : Real) (E : Set α) : closure E subseteq cthickening δ E := by
  rw [← cthickening_of_nonpos (min_le_right δ 0)]
  exact cthickening_mono (min_le_left δ 0) E

/--
theorem `closure_subset_thickening` / 定理 `closure_subset_thickening`

English:
theorem closure_subset_thickening
  given: {δ : Real} (δ_pos : 0 < δ) (E : Set α)
  proof: by
  rw [← cthickening_zero]
  exact cthickening_subset_thickening' δ_pos δ_pos E

中文:
定理 closure_subset_thickening
  条件: {δ : 实数} (δ_pos : 0 < δ) (E : Set α)
  证明: by
  rw [← cthickening_zero]
  exact cthickening_subset_thickening' δ_pos δ_pos E

Depends on / 依赖: cthickening_subset_thickening, cthickening_zero
-/
theorem closure_subset_thickening {δ : Real} (δ_pos : 0 < δ) (E : Set α) :
    closure E subseteq thickening δ E := by
  rw [← cthickening_zero]
  exact cthickening_subset_thickening' δ_pos δ_pos E

/--
theorem `self_subset_thickening` / 定理 `self_subset_thickening`

English:
theorem self_subset_thickening
  given: {δ : Real} (δ_pos : 0 < δ) (E : Set α)
  statement: E subseteq thickening δ E
  proof: (@subset_closure _ _ E).trans (closure_subset_thickening δ_pos E)

中文:
定理 self_subset_thickening
  条件: {δ : 实数} (δ_pos : 0 < δ) (E : Set α)
  结论: E subseteq thickening δ E
  证明: (@subset_closure _ _ E).trans (closure_subset_thickening δ_pos E)

Depends on / 依赖: closure_subset_thickening, subset_closure
-/
theorem self_subset_thickening {δ : Real} (δ_pos : 0 < δ) (E : Set α) : E subseteq thickening δ E :=
  (@subset_closure _ _ E).trans (closure_subset_thickening δ_pos E)

/--
theorem `self_subset_cthickening` / 定理 `self_subset_cthickening`

English:
theorem self_subset_cthickening
  given: {δ : Real} (E : Set α)
  statement: E subseteq cthickening δ E
  proof: subset_closure.trans (closure_subset_cthickening δ E)

中文:
定理 self_subset_cthickening
  条件: {δ : 实数} (E : Set α)
  结论: E subseteq cthickening δ E
  证明: subset_closure.trans (closure_subset_cthickening δ E)

Depends on / 依赖: closure_subset_cthickening, subset_closure, subset_closure.trans
-/
theorem self_subset_cthickening {δ : Real} (E : Set α) : E subseteq cthickening δ E :=
  subset_closure.trans (closure_subset_cthickening δ E)

/--
theorem `thickening_mem_nhdsSet` / 定理 `thickening_mem_nhdsSet`

English:
theorem thickening_mem_nhdsSet
  given: (E : Set α) {δ : Real} (hδ : 0 < δ)
  statement: thickening δ E in 𝓝ˢ E
  proof: isOpen_thickening.mem_nhdsSet.2 self_subset_thickening hδ E

中文:
定理 thickening_mem_nhdsSet
  条件: (E : Set α) {δ : 实数} (hδ : 0 < δ)
  结论: thickening δ E in 𝓝ˢ E
  证明: isOpen_thickening.mem_nhdsSet.2 self_subset_thickening hδ E

Depends on / 依赖: isOpen_thickening, isOpen_thickening.mem_nhdsSet, mem_nhdsSet, self_subset_thickening
-/
theorem thickening_mem_nhdsSet (E : Set α) {δ : Real} (hδ : 0 < δ) : thickening δ E in 𝓝ˢ E :=
isOpen_thickening.mem_nhdsSet.2 self_subset_thickening hδ E

/--
theorem `cthickening_mem_nhdsSet` / 定理 `cthickening_mem_nhdsSet`

English:
theorem cthickening_mem_nhdsSet
  given: (E : Set α) {δ : Real} (hδ : 0 < δ)
  statement: cthickening δ E in 𝓝ˢ E
  proof: mem_of_superset (thickening_mem_nhdsSet E hδ) (thickening_subset_cthickening _ _)

@[simp]

中文:
定理 cthickening_mem_nhdsSet
  条件: (E : Set α) {δ : 实数} (hδ : 0 < δ)
  结论: cthickening δ E in 𝓝ˢ E
  证明: mem_of_superset (thickening_mem_nhdsSet E hδ) (thickening_subset_cthickening _ _)

@[simp]

Depends on / 依赖: mem_of_superset, thickening_mem_nhdsSet, thickening_subset_cthickening
-/
theorem cthickening_mem_nhdsSet (E : Set α) {δ : Real} (hδ : 0 < δ) : cthickening δ E in 𝓝ˢ E :=
  mem_of_superset (thickening_mem_nhdsSet E hδ) (thickening_subset_cthickening _ _)

@[simp]
/--
theorem `thickening_union` / 定理 `thickening_union`

English:
theorem thickening_union
  given: (δ : Real) (s t : Set α)
  proof: by
  simp_rw [thickening, infEDist_union, min_lt_iff, ofPred_or]

@[simp]

中文:
定理 thickening_union
  条件: (δ : 实数) (s t : Set α)
  证明: by
  simp_rw [thickening, infEDist_union, min_lt_iff, ofPred_or]

@[simp]

Depends on / 依赖: infEDist_union, min_lt_iff, ofPred_or, simp_rw, thickening
-/
theorem thickening_union (δ : Real) (s t : Set α) :
    thickening δ (s union t) = thickening δ s union thickening δ t := by
  simp_rw [thickening, infEDist_union, min_lt_iff, ofPred_or]

@[simp]
/--
theorem `cthickening_union` / 定理 `cthickening_union`

English:
theorem cthickening_union
  given: (δ : Real) (s t : Set α)
  proof: by
  simp_rw [cthickening, infEDist_union, min_le_iff, ofPred_or]

@[simp]

中文:
定理 cthickening_union
  条件: (δ : 实数) (s t : Set α)
  证明: by
  simp_rw [cthickening, infEDist_union, min_le_iff, ofPred_or]

@[simp]

Depends on / 依赖: cthickening, infEDist_union, min_le_iff, ofPred_or, simp_rw
-/
theorem cthickening_union (δ : Real) (s t : Set α) :
    cthickening δ (s union t) = cthickening δ s union cthickening δ t := by
  simp_rw [cthickening, infEDist_union, min_le_iff, ofPred_or]

@[simp]
/--
theorem `thickening_iUnion` / 定理 `thickening_iUnion`

English:
theorem thickening_iUnion
  given: (δ : Real) (f : ι -> Set α)
  proof: by
  simp_rw [thickening, infEDist_iUnion, iInf_lt_iff, ofPred_exists]

中文:
定理 thickening_iUnion
  条件: (δ : 实数) (f : ι -> Set α)
  证明: by
  simp_rw [thickening, infEDist_iUnion, iInf_lt_iff, ofPred_exists]

Depends on / 依赖: iInf_lt_iff, infEDist_iUnion, ofPred_exists, simp_rw, thickening
-/
theorem thickening_iUnion (δ : Real) (f : ι -> Set α) :
    thickening δ (⋃ i, f i) = ⋃ i, thickening δ (f i) := by
  simp_rw [thickening, infEDist_iUnion, iInf_lt_iff, ofPred_exists]

/--
lemma `thickening_biUnion` / 引理 `thickening_biUnion`

English:
lemma thickening_biUnion
  given: {ι : Type*} (δ : Real) (f : ι -> Set α) (I : Set ι)
  proof: by simp only [thickening_iUnion]

中文:
引理 thickening_biUnion
  条件: {ι : 类型} (δ : 实数) (f : ι -> Set α) (I : Set ι)
  证明: by simp only [thickening_iUnion]

Depends on / 依赖: thickening_iUnion
-/
lemma thickening_biUnion {ι : Type*} (δ : Real) (f : ι -> Set α) (I : Set ι) :
    thickening δ (⋃ i in I, f i) = ⋃ i in I, thickening δ (f i) := by simp only [thickening_iUnion]

/--
theorem `ediam_cthickening_le` / 定理 `ediam_cthickening_le`

English:
theorem ediam_cthickening_le
  given: (ε : Real>=0)
  proof: by
  refine ediam_le fun x hx y hy => ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  rw [mem_cthickening_iff]; rw [ENNReal.ofReal_coe_nnreal] at hx hy
  have hε : (ε : Real>=0∞) < ε + δ := ENNReal.coe_lt_coe.2 (lt_add_of_pos_right _ hδ)
  replace hx := hx.trans_lt hε
  obtain ⟨x', hx', hxx'⟩ := 

中文:
定理 ediam_cthickening_le
  条件: (ε : 实数>=0)
  证明: by
  refine ediam_le fun x hx y hy => ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  rw [mem_cthickening_iff]; rw [ENNReal.ofReal_coe_nnreal] at hx hy
  have hε : (ε : Real>=0∞) < ε + δ := ENNReal.coe_lt_coe.2 (lt_add_of_pos_right _ hδ)
  replace hx := hx.trans_lt hε
  obtain ⟨x', hx', hxx'⟩ := 

Depends on / 依赖: ENNReal, ENNReal.coe_lt_coe, ENNReal.le_of_forall_pos_le_add, ENNReal.ofReal_coe_nnreal, add_le_add, coe_lt_coe, ediam_le, edist_le_infEDist_add_ediam, edist_triangle_right, hx.trans_lt, infEDist, infEDist_lt_iff, infEDist_lt_iff.mp, le_of_forall_pos_le_add, lt_add_of_pos_right, mem_cthickening_iff, ofReal_coe_nnreal, replace, trans_lt
-/
theorem ediam_cthickening_le (ε : Real>=0) :
    ediam (cthickening ε s) <= ediam s + 2 * ε := by
  refine ediam_le fun x hx y hy => ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  rw [mem_cthickening_iff]; rw [ENNReal.ofReal_coe_nnreal] at hx hy
  have hε : (ε : Real>=0∞) < ε + δ := ENNReal.coe_lt_coe.2 (lt_add_of_pos_right _ hδ)
  replace hx := hx.trans_lt hε
  obtain ⟨x', hx', hxx'⟩ := infEDist_lt_iff.mp hx
  calc
    edist x y <= edist x x' + edist y x' := edist_triangle_right _ _ _
    _ <= ε + δ + (infEDist y s + ediam s) :=
      add_le_add hxx'.le (edist_le_infEDist_add_ediam hx')
    _ <= ε + δ + (ε + ediam s) := by grw [hy]
    _ = _ := by rw [two_mul]; ac_rfl

/--
theorem `ediam_thickening_le` / 定理 `ediam_thickening_le`

English:
theorem ediam_thickening_le
  given: (ε : Real>=0)
  statement: ediam (thickening ε s) <= ediam s + 2 * ε
  proof: (ediam_mono <| thickening_subset_cthickening _ _).trans ediam_cthickening_le _

中文:
定理 ediam_thickening_le
  条件: (ε : 实数>=0)
  结论: ediam (thickening ε s) <= ediam s + 2 * ε
  证明: (ediam_mono <| thickening_subset_cthickening _ _).trans ediam_cthickening_le _

Depends on / 依赖: ediam_cthickening_le, ediam_mono, thickening_subset_cthickening
-/
theorem ediam_thickening_le (ε : Real>=0) : ediam (thickening ε s) <= ediam s + 2 * ε :=
(ediam_mono <| thickening_subset_cthickening _ _).trans ediam_cthickening_le _

/--
theorem `diam_cthickening_le` / 定理 `diam_cthickening_le`

English:
theorem diam_cthickening_le
  given: {α : Type*} [PseudoMetricSpace α] (s : Set α) (hε : 0 <= ε)
  proof: by
  lift ε to Real>=0 using hε
  refine (toReal_le_add' (ediam_cthickening_le _) ?_ ?_).trans_eq ?_
· exact fun h => top_unique h ▸ ediam_mono (self_subset_cthickening _)
  · simp [mul_eq_top]
  · simp [diam]

中文:
定理 diam_cthickening_le
  条件: {α : 类型} [PseudoMetricSpace α] (s : Set α) (hε : 0 <= ε)
  证明: by
  lift ε to Real>=0 using hε
  refine (toReal_le_add' (ediam_cthickening_le _) ?_ ?_).trans_eq ?_
· exact fun h => top_unique h ▸ ediam_mono (self_subset_cthickening _)
  · simp [mul_eq_top]
  · simp [diam]

Depends on / 依赖: ediam_cthickening_le, ediam_mono, mul_eq_top, self_subset_cthickening, toReal_le_add, top_unique, trans_eq
-/
theorem diam_cthickening_le {α : Type*} [PseudoMetricSpace α] (s : Set α) (hε : 0 <= ε) :
    diam (cthickening ε s) <= diam s + 2 * ε := by
  lift ε to Real>=0 using hε
  refine (toReal_le_add' (ediam_cthickening_le _) ?_ ?_).trans_eq ?_
· exact fun h => top_unique h ▸ ediam_mono (self_subset_cthickening _)
  · simp [mul_eq_top]
  · simp [diam]

/--
theorem `diam_thickening_le` / 定理 `diam_thickening_le`

English:
theorem diam_thickening_le
  given: {α : Type*} [PseudoMetricSpace α] (s : Set α) (hε : 0 <= ε)
  proof: by
  by_cases hs : IsBounded s
  · exact (diam_mono (thickening_subset_cthickening _ _) hs.cthickening).trans
      (diam_cthickening_le _ hε)
  obtain rfl | hε := hε.eq_or_lt
  · simp [thickening_of_nonpos, diam_nonneg]
  · rw [diam_eq_zero_of_unbounded (mt (IsBounded.subset · <| self_subset_thicke

中文:
定理 diam_thickening_le
  条件: {α : 类型} [PseudoMetricSpace α] (s : Set α) (hε : 0 <= ε)
  证明: by
  by_cases hs : IsBounded s
  · exact (diam_mono (thickening_subset_cthickening _ _) hs.cthickening).trans
      (diam_cthickening_le _ hε)
  obtain rfl | hε := hε.eq_or_lt
  · simp [thickening_of_nonpos, diam_nonneg]
  · rw [diam_eq_zero_of_unbounded (mt (IsBounded.subset · <| self_subset_thicke

Depends on / 依赖: IsBounded, IsBounded.subset, cthickening, diam_cthickening_le, diam_eq_zero_of_unbounded, diam_mono, diam_nonneg, eq_or_lt, hs.cthickening, self_subset_thickening, subset, thickening_of_nonpos, thickening_subset_cthickening
-/
theorem diam_thickening_le {α : Type*} [PseudoMetricSpace α] (s : Set α) (hε : 0 <= ε) :
    diam (thickening ε s) <= diam s + 2 * ε := by
  by_cases hs : IsBounded s
  · exact (diam_mono (thickening_subset_cthickening _ _) hs.cthickening).trans
      (diam_cthickening_le _ hε)
  obtain rfl | hε := hε.eq_or_lt
  · simp [thickening_of_nonpos, diam_nonneg]
  · rw [diam_eq_zero_of_unbounded (mt (IsBounded.subset · <| self_subset_thickening hε _) hs)]
    positivity

@[simp]
/--
theorem `thickening_closure` / 定理 `thickening_closure`

English:
theorem thickening_closure
  statement: thickening δ (closure s) = thickening δ s
  proof: by
  simp_rw [thickening, infEDist_closure]

@[simp]

中文:
定理 thickening_closure
  结论: thickening δ (closure s) = thickening δ s
  证明: by
  simp_rw [thickening, infEDist_closure]

@[simp]

Depends on / 依赖: infEDist_closure, simp_rw, thickening
-/
theorem thickening_closure : thickening δ (closure s) = thickening δ s := by
  simp_rw [thickening, infEDist_closure]

@[simp]
/--
theorem `cthickening_closure` / 定理 `cthickening_closure`

English:
theorem cthickening_closure
  statement: cthickening δ (closure s) = cthickening δ s
  proof: by
  simp_rw [cthickening, infEDist_closure]

中文:
定理 cthickening_closure
  结论: cthickening δ (closure s) = cthickening δ s
  证明: by
  simp_rw [cthickening, infEDist_closure]

Depends on / 依赖: cthickening, infEDist_closure, simp_rw
-/
theorem cthickening_closure : cthickening δ (closure s) = cthickening δ s := by
  simp_rw [cthickening, infEDist_closure]

/--
lemma `thickening_eq_empty_iff_of_pos` / 引理 `thickening_eq_empty_iff_of_pos`

English:
lemma thickening_eq_empty_iff_of_pos
  given: (hε : 0 < ε)
  proof: ⟨fun h => subset_eq_empty (self_subset_thickening hε _) h, by simp +contextual⟩

中文:
引理 thickening_eq_empty_iff_of_pos
  条件: (hε : 0 < ε)
  证明: ⟨fun h => subset_eq_empty (self_subset_thickening hε _) h, by simp +contextual⟩

Depends on / 依赖: contextual, self_subset_thickening, subset_eq_empty
-/
lemma thickening_eq_empty_iff_of_pos (hε : 0 < ε) :
    thickening ε s = ∅ ↔ s = ∅ :=
  ⟨fun h => subset_eq_empty (self_subset_thickening hε _) h, by simp +contextual⟩

/--
lemma `thickening_nonempty_iff_of_pos` / 引理 `thickening_nonempty_iff_of_pos`

English:
lemma thickening_nonempty_iff_of_pos
  given: (hε : 0 < ε)
  proof: by
  simp [nonempty_iff_ne_empty, thickening_eq_empty_iff_of_pos hε]

中文:
引理 thickening_nonempty_iff_of_pos
  条件: (hε : 0 < ε)
  证明: by
  simp [nonempty_iff_ne_empty, thickening_eq_empty_iff_of_pos hε]

Depends on / 依赖: nonempty_iff_ne_empty, thickening_eq_empty_iff_of_pos
-/
lemma thickening_nonempty_iff_of_pos (hε : 0 < ε) :
    (thickening ε s).Nonempty ↔ s.Nonempty := by
  simp [nonempty_iff_ne_empty, thickening_eq_empty_iff_of_pos hε]

/--
lemma `thickening_eq_empty_iff` / 引理 `thickening_eq_empty_iff`

English:
lemma thickening_eq_empty_iff
  statement: thickening ε s = ∅ ↔ ε <= 0 ∨ s = ∅
  proof: by
  obtain hε | hε := lt_or_ge 0 ε
  · simp [thickening_eq_empty_iff_of_pos, hε]
  · simp [hε, thickening_of_nonpos hε]

中文:
引理 thickening_eq_empty_iff
  结论: thickening ε s = ∅ ↔ ε <= 0 ∨ s = ∅
  证明: by
  obtain hε | hε := lt_or_ge 0 ε
  · simp [thickening_eq_empty_iff_of_pos, hε]
  · simp [hε, thickening_of_nonpos hε]
-/
@[simp] lemma thickening_eq_empty_iff : thickening ε s = ∅ ↔ ε <= 0 ∨ s = ∅ := by
  obtain hε | hε := lt_or_ge 0 ε
  · simp [thickening_eq_empty_iff_of_pos, hε]
  · simp [hε, thickening_of_nonpos hε]

/--
lemma `thickening_nonempty_iff` / 引理 `thickening_nonempty_iff`

English:
lemma thickening_nonempty_iff
  statement: (thickening ε s).Nonempty ↔ 0 < ε ∧ s.Nonempty
  proof: by
  simp [nonempty_iff_ne_empty]

中文:
引理 thickening_nonempty_iff
  结论: (thickening ε s).Nonempty ↔ 0 < ε ∧ s.Nonempty
  证明: by
  simp [nonempty_iff_ne_empty]
-/
@[simp] lemma thickening_nonempty_iff : (thickening ε s).Nonempty ↔ 0 < ε ∧ s.Nonempty := by
  simp [nonempty_iff_ne_empty]

open ENNReal

/--
theorem `_root_.Disjoint.exists_thickenings` / 定理 `_root_.Disjoint.exists_thickenings`

English:
theorem _root_.Disjoint.exists_thickenings
  statement: (hst : Disjoint s t) (hs : IsCompact s)
  proof: by
  obtain ⟨r, hr, h⟩ := exists_pos_forall_lt_edist hs ht hst
  refine ⟨r / 2, half_pos (NNReal.coe_pos.2 hr), ?_⟩
  rw [disjoint_iff_inf_le]
  rintro z ⟨hzs, hzt⟩
  rw [mem_thickening_iff_exists_edist_lt] at hzs hzt
  rw [← NNReal.coe_two]; rw [← NNReal.coe_div]; rw [ENNReal.ofReal_coe_nnreal] at 

中文:
定理 _root_.Disjoint.exists_thickenings
  结论: (hst : Disjoint s t) (hs : IsCompact s)
  证明: by
  obtain ⟨r, hr, h⟩ := exists_pos_forall_lt_edist hs ht hst
  refine ⟨r / 2, half_pos (NNReal.coe_pos.2 hr), ?_⟩
  rw [disjoint_iff_inf_le]
  rintro z ⟨hzs, hzt⟩
  rw [mem_thickening_iff_exists_edist_lt] at hzs hzt
  rw [← NNReal.coe_two]; rw [← NNReal.coe_div]; rw [ENNReal.ofReal_coe_nnreal] at 

Depends on / 依赖: ENNReal, ENNReal.ofReal_coe_nnreal, NNReal, NNReal.coe_div, NNReal.coe_pos, NNReal.coe_two, add_le_add, coe_div, coe_pos, coe_two, disjoint_iff_inf_le, edist_triangle_left, exists_pos_forall_lt_edist, half_pos, hzx.le, mem_thickening_iff_exists_edist_lt, not_ge, ofReal_coe_nnreal
-/
theorem _root_.Disjoint.exists_thickenings (hst : Disjoint s t) (hs : IsCompact s)
    (ht : IsClosed t) :
    exists δ, 0 < δ ∧ Disjoint (thickening δ s) (thickening δ t) := by
  obtain ⟨r, hr, h⟩ := exists_pos_forall_lt_edist hs ht hst
  refine ⟨r / 2, half_pos (NNReal.coe_pos.2 hr), ?_⟩
  rw [disjoint_iff_inf_le]
  rintro z ⟨hzs, hzt⟩
  rw [mem_thickening_iff_exists_edist_lt] at hzs hzt
  rw [← NNReal.coe_two]; rw [← NNReal.coe_div]; rw [ENNReal.ofReal_coe_nnreal] at hzs hzt
  obtain ⟨x, hx, hzx⟩ := hzs
  obtain ⟨y, hy, hzy⟩ := hzt
  refine (h x hx y hy).not_ge ?_
  calc
    edist x y <= edist z x + edist z y := edist_triangle_left _ _ _
    _ <= ↑(r / 2) + ↑(r / 2) := add_le_add hzx.le hzy.le
    _ = r := by rw [← ENNReal.coe_add, add_halves]

/--
theorem `_root_.Disjoint.exists_cthickenings` / 定理 `_root_.Disjoint.exists_cthickenings`

English:
theorem _root_.Disjoint.exists_cthickenings
  statement: (hst : Disjoint s t) (hs : IsCompact s)
  proof: by
  obtain ⟨δ, hδ, h⟩ := hst.exists_thickenings hs ht
  refine ⟨δ / 2, half_pos hδ, h.mono ?_ ?_⟩ <;>
    exact cthickening_subset_thickening' hδ (half_lt_self hδ) _

中文:
定理 _root_.Disjoint.exists_cthickenings
  结论: (hst : Disjoint s t) (hs : IsCompact s)
  证明: by
  obtain ⟨δ, hδ, h⟩ := hst.exists_thickenings hs ht
  refine ⟨δ / 2, half_pos hδ, h.mono ?_ ?_⟩ <;>
    exact cthickening_subset_thickening' hδ (half_lt_self hδ) _

Depends on / 依赖: cthickening_subset_thickening, exists_thickenings, h.mono, half_lt_self, half_pos, hst.exists_thickenings
-/
theorem _root_.Disjoint.exists_cthickenings (hst : Disjoint s t) (hs : IsCompact s)
    (ht : IsClosed t) :
    exists δ, 0 < δ ∧ Disjoint (cthickening δ s) (cthickening δ t) := by
  obtain ⟨δ, hδ, h⟩ := hst.exists_thickenings hs ht
  refine ⟨δ / 2, half_pos hδ, h.mono ?_ ?_⟩ <;>
    exact cthickening_subset_thickening' hδ (half_lt_self hδ) _

/--
theorem `_root_.IsCompact.exists_cthickening_subset_open` / 定理 `_root_.IsCompact.exists_cthickening_subset_open`

English:
theorem _root_.IsCompact.exists_cthickening_subset_open
  statement: (hs : IsCompact s) (ht : IsOpen t)
  proof: (hst.disjoint_compl_right.exists_cthickenings hs ht.isClosed_compl).imp fun _ h =>
⟨h.1, disjoint_compl_right_iff_subset.1 h.2.mono_right self_subset_cthickening _⟩

中文:
定理 _root_.IsCompact.exists_cthickening_subset_open
  结论: (hs : IsCompact s) (ht : IsOpen t)
  证明: (hst.disjoint_compl_right.exists_cthickenings hs ht.isClosed_compl).imp fun _ h =>
⟨h.1, disjoint_compl_right_iff_subset.1 h.2.mono_right self_subset_cthickening _⟩

Depends on / 依赖: disjoint_compl_right, disjoint_compl_right_iff_subset, exists_cthickenings, hst.disjoint_compl_right.exists_cthickenings, ht.isClosed_compl, isClosed_compl, mono_right, self_subset_cthickening
-/
theorem _root_.IsCompact.exists_cthickening_subset_open (hs : IsCompact s) (ht : IsOpen t)
    (hst : s subseteq t) :
    exists δ, 0 < δ ∧ cthickening δ s subseteq t :=
  (hst.disjoint_compl_right.exists_cthickenings hs ht.isClosed_compl).imp fun _ h =>
⟨h.1, disjoint_compl_right_iff_subset.1 h.2.mono_right self_subset_cthickening _⟩

/--
theorem `_root_.IsCompact.exists_isCompact_cthickening` / 定理 `_root_.IsCompact.exists_isCompact_cthickening`

English:
theorem _root_.IsCompact.exists_isCompact_cthickening
  given: [LocallyCompactSpace α] (hs : IsCompact s)
  proof: by
  rcases exists_compact_superset hs with ⟨K, K_compact, hK⟩
  rcases hs.exists_cthickening_subset_open isOpen_interior hK with ⟨δ, δpos, hδ⟩
  refine ⟨δ, δpos, ?_⟩
  exact K_compact.of_isClosed_subset isClosed_cthickening (hδ.trans interior_subset)

中文:
定理 _root_.IsCompact.exists_isCompact_cthickening
  条件: [LocallyCompactSpace α] (hs : IsCompact s)
  证明: by
  rcases exists_compact_superset hs with ⟨K, K_compact, hK⟩
  rcases hs.exists_cthickening_subset_open isOpen_interior hK with ⟨δ, δpos, hδ⟩
  refine ⟨δ, δpos, ?_⟩
  exact K_compact.of_isClosed_subset isClosed_cthickening (hδ.trans interior_subset)

Depends on / 依赖: K_compact, K_compact.of_isClosed_subset, exists_compact_superset, exists_cthickening_subset_open, hs.exists_cthickening_subset_open, interior_subset, isClosed_cthickening, isOpen_interior, of_isClosed_subset
-/
theorem _root_.IsCompact.exists_isCompact_cthickening [LocallyCompactSpace α] (hs : IsCompact s) :
    exists δ, 0 < δ ∧ IsCompact (cthickening δ s) := by
  rcases exists_compact_superset hs with ⟨K, K_compact, hK⟩
  rcases hs.exists_cthickening_subset_open isOpen_interior hK with ⟨δ, δpos, hδ⟩
  refine ⟨δ, δpos, ?_⟩
  exact K_compact.of_isClosed_subset isClosed_cthickening (hδ.trans interior_subset)

/--
theorem `_root_.IsCompact.exists_thickening_subset_open` / 定理 `_root_.IsCompact.exists_thickening_subset_open`

English:
theorem _root_.IsCompact.exists_thickening_subset_open
  statement: (hs : IsCompact s) (ht : IsOpen t)
  proof: let ⟨δ, h₀, hδ⟩ := hs.exists_cthickening_subset_open ht hst
  ⟨δ, h₀, (thickening_subset_cthickening _ _).trans hδ⟩

中文:
定理 _root_.IsCompact.exists_thickening_subset_open
  结论: (hs : IsCompact s) (ht : IsOpen t)
  证明: let ⟨δ, h₀, hδ⟩ := hs.exists_cthickening_subset_open ht hst
  ⟨δ, h₀, (thickening_subset_cthickening _ _).trans hδ⟩

Depends on / 依赖: exists_cthickening_subset_open, hs.exists_cthickening_subset_open, thickening_subset_cthickening
-/
theorem _root_.IsCompact.exists_thickening_subset_open (hs : IsCompact s) (ht : IsOpen t)
    (hst : s subseteq t) : exists δ, 0 < δ ∧ thickening δ s subseteq t :=
  let ⟨δ, h₀, hδ⟩ := hs.exists_cthickening_subset_open ht hst
  ⟨δ, h₀, (thickening_subset_cthickening _ _).trans hδ⟩

/--
theorem `hasBasis_nhdsSet_thickening` / 定理 `hasBasis_nhdsSet_thickening`

English:
theorem hasBasis_nhdsSet_thickening
  given: {K : Set α} (hK : IsCompact K)
  proof: (hasBasis_nhdsSet K).to_hasBasis' (fun _U hU => hK.exists_thickening_subset_open hU.1 hU.2)
    fun _ => thickening_mem_nhdsSet K

中文:
定理 hasBasis_nhdsSet_thickening
  条件: {K : Set α} (hK : IsCompact K)
  证明: (hasBasis_nhdsSet K).to_hasBasis' (fun _U hU => hK.exists_thickening_subset_open hU.1 hU.2)
    fun _ => thickening_mem_nhdsSet K

Depends on / 依赖: exists_thickening_subset_open, hK.exists_thickening_subset_open, hasBasis_nhdsSet, thickening_mem_nhdsSet, to_hasBasis
-/
theorem hasBasis_nhdsSet_thickening {K : Set α} (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis (fun δ : Real => 0 < δ) fun δ => thickening δ K :=
  (hasBasis_nhdsSet K).to_hasBasis' (fun _U hU => hK.exists_thickening_subset_open hU.1 hU.2)
    fun _ => thickening_mem_nhdsSet K

/--
theorem `hasBasis_nhdsSet_cthickening` / 定理 `hasBasis_nhdsSet_cthickening`

English:
theorem hasBasis_nhdsSet_cthickening
  given: {K : Set α} (hK : IsCompact K)
  proof: (hasBasis_nhdsSet K).to_hasBasis' (fun _U hU => hK.exists_cthickening_subset_open hU.1 hU.2)
    fun _ => cthickening_mem_nhdsSet K

中文:
定理 hasBasis_nhdsSet_cthickening
  条件: {K : Set α} (hK : IsCompact K)
  证明: (hasBasis_nhdsSet K).to_hasBasis' (fun _U hU => hK.exists_cthickening_subset_open hU.1 hU.2)
    fun _ => cthickening_mem_nhdsSet K

Depends on / 依赖: cthickening_mem_nhdsSet, exists_cthickening_subset_open, hK.exists_cthickening_subset_open, hasBasis_nhdsSet, to_hasBasis
-/
theorem hasBasis_nhdsSet_cthickening {K : Set α} (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis (fun δ : Real => 0 < δ) fun δ => cthickening δ K :=
  (hasBasis_nhdsSet K).to_hasBasis' (fun _U hU => hK.exists_cthickening_subset_open hU.1 hU.2)
    fun _ => cthickening_mem_nhdsSet K

/--
theorem `cthickening_eq_iInter_cthickening'` / 定理 `cthickening_eq_iInter_cthickening'`

English:
theorem cthickening_eq_iInter_cthickening'
  statement: {δ : Real} (s : Set Real) (hsδ : s subseteq Ioi δ)
  proof: by
  apply Subset.antisymm
  · exact subset_iInter₂ fun _ hε => cthickening_mono (le_of_lt (hsδ hε)) E
  · unfold cthickening
    intro x hx
    simp only [mem_iInter, mem_ofPred_eq] at *
    apply ENNReal.le_of_forall_pos_le_add
    intro η η_pos _
    rcases hs (δ + η) (lt_add_of_pos_right _ (NNRe

中文:
定理 cthickening_eq_iInter_cthickening'
  结论: {δ : 实数} (s : Set 实数) (hsδ : s subseteq Ioi δ)
  证明: by
  apply Subset.antisymm
  · exact subset_iInter₂ fun _ hε => cthickening_mono (le_of_lt (hsδ hε)) E
  · unfold cthickening
    intro x hx
    simp only [mem_iInter, mem_ofPred_eq] at *
    apply ENNReal.le_of_forall_pos_le_add
    intro η η_pos _
    rcases hs (δ + η) (lt_add_of_pos_right _ (NNRe

Depends on / 依赖: ENNReal, ENNReal.coe_nnreal_eq, ENNReal.le_of_forall_pos_le_add, ENNReal.ofReal_add_le, ENNReal.ofReal_le_ofReal, NNReal, NNReal.coe_pos.mpr, Subset, Subset.antisymm, antisymm, coe_nnreal_eq, coe_pos, cthickening, cthickening_mono, le_of_forall_pos_le_add, le_of_lt, lt_add_of_pos_right, mem_iInter, mem_ofPred_eq, ofReal_add_le
-/
theorem cthickening_eq_iInter_cthickening' {δ : Real} (s : Set Real) (hsδ : s subseteq Ioi δ)
    (hs : forall ε, δ < ε -> (s inter Ioc δ ε).Nonempty) (E : Set α) :
    cthickening δ E = ⋂ ε in s, cthickening ε E := by
  apply Subset.antisymm
  · exact subset_iInter₂ fun _ hε => cthickening_mono (le_of_lt (hsδ hε)) E
  · unfold cthickening
    intro x hx
    simp only [mem_iInter, mem_ofPred_eq] at *
    apply ENNReal.le_of_forall_pos_le_add
    intro η η_pos _
    rcases hs (δ + η) (lt_add_of_pos_right _ (NNReal.coe_pos.mpr η_pos)) with ⟨ε, ⟨hsε, hε⟩⟩
    apply ((hx ε hsε).trans (ENNReal.ofReal_le_ofReal hε.2)).trans
    rw [ENNReal.coe_nnreal_eq η]
    exact ENNReal.ofReal_add_le

/--
theorem `cthickening_eq_iInter_cthickening` / 定理 `cthickening_eq_iInter_cthickening`

English:
theorem cthickening_eq_iInter_cthickening
  given: {δ : Real} (E : Set α)
  proof: by
  apply cthickening_eq_iInter_cthickening' (Ioi δ) rfl.subset
  simp_rw [inter_eq_right.mpr Ioc_subset_Ioi_self]
  exact fun _ hε => nonempty_Ioc.mpr hε

中文:
定理 cthickening_eq_iInter_cthickening
  条件: {δ : 实数} (E : Set α)
  证明: by
  apply cthickening_eq_iInter_cthickening' (Ioi δ) rfl.subset
  simp_rw [inter_eq_right.mpr Ioc_subset_Ioi_self]
  exact fun _ hε => nonempty_Ioc.mpr hε

Depends on / 依赖: Ioc_subset_Ioi_self, cthickening_eq_iInter_cthickening, inter_eq_right, inter_eq_right.mpr, nonempty_Ioc, nonempty_Ioc.mpr, rfl.subset, simp_rw, subset
-/
theorem cthickening_eq_iInter_cthickening {δ : Real} (E : Set α) :
    cthickening δ E = ⋂ (ε : Real) (_ : δ < ε), cthickening ε E := by
  apply cthickening_eq_iInter_cthickening' (Ioi δ) rfl.subset
  simp_rw [inter_eq_right.mpr Ioc_subset_Ioi_self]
  exact fun _ hε => nonempty_Ioc.mpr hε

/--
theorem `cthickening_eq_iInter_thickening'` / 定理 `cthickening_eq_iInter_thickening'`

English:
theorem cthickening_eq_iInter_thickening'
  statement: {δ : Real} (δ_nn : 0 <= δ) (s : Set Real) (hsδ : s subseteq Ioi δ)
  proof: by
  refine (subset_iInter₂ fun ε hε => ?_).antisymm ?_
  · obtain ⟨ε', -, hε'⟩ := hs ε (hsδ hε)
    have ss := cthickening_subset_thickening' (lt_of_le_of_lt δ_nn hε'.1) hε'.1 E
    exact ss.trans (thickening_mono hε'.2 E)
  · rw [cthickening_eq_iInter_cthickening' s hsδ hs E]
    exact iInter₂_mon

中文:
定理 cthickening_eq_iInter_thickening'
  结论: {δ : 实数} (δ_nn : 0 <= δ) (s : Set 实数) (hsδ : s subseteq Ioi δ)
  证明: by
  refine (subset_iInter₂ fun ε hε => ?_).antisymm ?_
  · obtain ⟨ε', -, hε'⟩ := hs ε (hsδ hε)
    have ss := cthickening_subset_thickening' (lt_of_le_of_lt δ_nn hε'.1) hε'.1 E
    exact ss.trans (thickening_mono hε'.2 E)
  · rw [cthickening_eq_iInter_cthickening' s hsδ hs E]
    exact iInter₂_mon

Depends on / 依赖: antisymm, cthickening_eq_iInter_cthickening, cthickening_subset_thickening, lt_of_le_of_lt, ss.trans, thickening_mono, thickening_subset_cthickening
-/
theorem cthickening_eq_iInter_thickening' {δ : Real} (δ_nn : 0 <= δ) (s : Set Real) (hsδ : s subseteq Ioi δ)
    (hs : forall ε, δ < ε -> (s inter Ioc δ ε).Nonempty) (E : Set α) :
    cthickening δ E = ⋂ ε in s, thickening ε E := by
  refine (subset_iInter₂ fun ε hε => ?_).antisymm ?_
  · obtain ⟨ε', -, hε'⟩ := hs ε (hsδ hε)
    have ss := cthickening_subset_thickening' (lt_of_le_of_lt δ_nn hε'.1) hε'.1 E
    exact ss.trans (thickening_mono hε'.2 E)
  · rw [cthickening_eq_iInter_cthickening' s hsδ hs E]
    exact iInter₂_mono fun ε _ => thickening_subset_cthickening ε E

/--
theorem `cthickening_eq_iInter_thickening` / 定理 `cthickening_eq_iInter_thickening`

English:
theorem cthickening_eq_iInter_thickening
  given: {δ : Real} (δ_nn : 0 <= δ) (E : Set α)
  proof: by
  apply cthickening_eq_iInter_thickening' δ_nn (Ioi δ) rfl.subset
  simp_rw [inter_eq_right.mpr Ioc_subset_Ioi_self]
  exact fun _ hε => nonempty_Ioc.mpr hε

中文:
定理 cthickening_eq_iInter_thickening
  条件: {δ : 实数} (δ_nn : 0 <= δ) (E : Set α)
  证明: by
  apply cthickening_eq_iInter_thickening' δ_nn (Ioi δ) rfl.subset
  simp_rw [inter_eq_right.mpr Ioc_subset_Ioi_self]
  exact fun _ hε => nonempty_Ioc.mpr hε

Depends on / 依赖: Ioc_subset_Ioi_self, cthickening_eq_iInter_thickening, inter_eq_right, inter_eq_right.mpr, nonempty_Ioc, nonempty_Ioc.mpr, rfl.subset, simp_rw, subset
-/
theorem cthickening_eq_iInter_thickening {δ : Real} (δ_nn : 0 <= δ) (E : Set α) :
    cthickening δ E = ⋂ (ε : Real) (_ : δ < ε), thickening ε E := by
  apply cthickening_eq_iInter_thickening' δ_nn (Ioi δ) rfl.subset
  simp_rw [inter_eq_right.mpr Ioc_subset_Ioi_self]
  exact fun _ hε => nonempty_Ioc.mpr hε

/--
theorem `cthickening_eq_iInter_thickening''` / 定理 `cthickening_eq_iInter_thickening''`

English:
theorem cthickening_eq_iInter_thickening''
  given: (δ : Real) (E : Set α)
  proof: by
  rw [← cthickening_max_zero]; rw [cthickening_eq_iInter_thickening]
  exact le_max_left _ _

中文:
定理 cthickening_eq_iInter_thickening''
  条件: (δ : 实数) (E : Set α)
  证明: by
  rw [← cthickening_max_zero]; rw [cthickening_eq_iInter_thickening]
  exact le_max_left _ _

Depends on / 依赖: cthickening_eq_iInter_thickening, cthickening_max_zero, le_max_left
-/
theorem cthickening_eq_iInter_thickening'' (δ : Real) (E : Set α) :
    cthickening δ E = ⋂ (ε : Real) (_ : max 0 δ < ε), thickening ε E := by
  rw [← cthickening_max_zero]; rw [cthickening_eq_iInter_thickening]
  exact le_max_left _ _

/--
theorem `closure_eq_iInter_cthickening'` / 定理 `closure_eq_iInter_cthickening'`

English:
theorem closure_eq_iInter_cthickening'
  statement: (E : Set α) (s : Set Real)
  proof: by
  by_cases hs₀ : s subseteq Ioi 0
  · rw [← cthickening_zero]
    apply cthickening_eq_iInter_cthickening' _ hs₀ hs
  obtain ⟨δ, hδs, δ_nonpos⟩ := not_subset.mp hs₀
  rw [Set.mem_Ioi]; rw [not_lt] at δ_nonpos
  apply Subset.antisymm
  · exact subset_iInter₂ fun ε _ => closure_subset_cthickening ε

中文:
定理 closure_eq_iInter_cthickening'
  结论: (E : Set α) (s : Set 实数)
  证明: by
  by_cases hs₀ : s subseteq Ioi 0
  · rw [← cthickening_zero]
    apply cthickening_eq_iInter_cthickening' _ hs₀ hs
  obtain ⟨δ, hδs, δ_nonpos⟩ := not_subset.mp hs₀
  rw [Set.mem_Ioi]; rw [not_lt] at δ_nonpos
  apply Subset.antisymm
  · exact subset_iInter₂ fun ε _ => closure_subset_cthickening ε

Depends on / 依赖: Set.mem_Ioi, Subset, Subset.antisymm, antisymm, biInter_subset_of_mem, closure_subset_cthickening, cthickening_eq_iInter_cthickening, cthickening_of_nonpos, cthickening_zero, mem_Ioi, not_lt, not_subset, not_subset.mp, subseteq
-/
theorem closure_eq_iInter_cthickening' (E : Set α) (s : Set Real)
    (hs : forall ε, 0 < ε -> (s inter Ioc 0 ε).Nonempty) : closure E = ⋂ δ in s, cthickening δ E := by
  by_cases hs₀ : s subseteq Ioi 0
  · rw [← cthickening_zero]
    apply cthickening_eq_iInter_cthickening' _ hs₀ hs
  obtain ⟨δ, hδs, δ_nonpos⟩ := not_subset.mp hs₀
  rw [Set.mem_Ioi]; rw [not_lt] at δ_nonpos
  apply Subset.antisymm
  · exact subset_iInter₂ fun ε _ => closure_subset_cthickening ε E
  · rw [← cthickening_of_nonpos δ_nonpos E]
    exact biInter_subset_of_mem hδs

/--
theorem `closure_eq_iInter_cthickening` / 定理 `closure_eq_iInter_cthickening`

English:
theorem closure_eq_iInter_cthickening
  given: (E : Set α)
  proof: by
  rw [← cthickening_zero]
  exact cthickening_eq_iInter_cthickening E

中文:
定理 closure_eq_iInter_cthickening
  条件: (E : Set α)
  证明: by
  rw [← cthickening_zero]
  exact cthickening_eq_iInter_cthickening E

Depends on / 依赖: cthickening_eq_iInter_cthickening, cthickening_zero
-/
theorem closure_eq_iInter_cthickening (E : Set α) :
    closure E = ⋂ (δ : Real) (_ : 0 < δ), cthickening δ E := by
  rw [← cthickening_zero]
  exact cthickening_eq_iInter_cthickening E

/--
theorem `closure_eq_iInter_thickening'` / 定理 `closure_eq_iInter_thickening'`

English:
theorem closure_eq_iInter_thickening'
  statement: (E : Set α) (s : Set Real) (hs₀ : s subseteq Ioi 0)
  proof: by
  rw [← cthickening_zero]
  apply cthickening_eq_iInter_thickening' le_rfl _ hs₀ hs

中文:
定理 closure_eq_iInter_thickening'
  结论: (E : Set α) (s : Set 实数) (hs₀ : s subseteq Ioi 0)
  证明: by
  rw [← cthickening_zero]
  apply cthickening_eq_iInter_thickening' le_rfl _ hs₀ hs

Depends on / 依赖: cthickening_eq_iInter_thickening, cthickening_zero, le_rfl
-/
theorem closure_eq_iInter_thickening' (E : Set α) (s : Set Real) (hs₀ : s subseteq Ioi 0)
    (hs : forall ε, 0 < ε -> (s inter Ioc 0 ε).Nonempty) : closure E = ⋂ δ in s, thickening δ E := by
  rw [← cthickening_zero]
  apply cthickening_eq_iInter_thickening' le_rfl _ hs₀ hs

/--
theorem `closure_eq_iInter_thickening` / 定理 `closure_eq_iInter_thickening`

English:
theorem closure_eq_iInter_thickening
  given: (E : Set α)
  proof: by
  rw [← cthickening_zero]
  exact cthickening_eq_iInter_thickening rfl.ge E

中文:
定理 closure_eq_iInter_thickening
  条件: (E : Set α)
  证明: by
  rw [← cthickening_zero]
  exact cthickening_eq_iInter_thickening rfl.ge E

Depends on / 依赖: cthickening_eq_iInter_thickening, cthickening_zero, rfl.ge
-/
theorem closure_eq_iInter_thickening (E : Set α) :
    closure E = ⋂ (δ : Real) (_ : 0 < δ), thickening δ E := by
  rw [← cthickening_zero]
  exact cthickening_eq_iInter_thickening rfl.ge E

/--
theorem `frontier_cthickening_subset` / 定理 `frontier_cthickening_subset`

English:
theorem frontier_cthickening_subset
  given: (E : Set α) {δ : Real}
  proof: frontier_le_subset_eq continuous_infEDist continuous_const

中文:
定理 frontier_cthickening_subset
  条件: (E : Set α) {δ : 实数}
  证明: frontier_le_subset_eq continuous_infEDist continuous_const

Depends on / 依赖: continuous_const, continuous_infEDist, frontier_le_subset_eq
-/
theorem frontier_cthickening_subset (E : Set α) {δ : Real} :
    frontier (cthickening δ E) subseteq { x : α | infEDist x E = ENNReal.ofReal δ } :=
  frontier_le_subset_eq continuous_infEDist continuous_const

/--
theorem `closedBall_subset_cthickening` / 定理 `closedBall_subset_cthickening`

English:
theorem closedBall_subset_cthickening
  statement: {α : Type*} [PseudoMetricSpace α] {x : α} {E : Set α}
  proof: by
  refine (closedBall_subset_cthickening_singleton _ _).trans (cthickening_subset_of_subset _ ?_)
  simpa using hx

中文:
定理 closedBall_subset_cthickening
  结论: {α : 类型} [PseudoMetricSpace α] {x : α} {E : Set α}
  证明: by
  refine (closedBall_subset_cthickening_singleton _ _).trans (cthickening_subset_of_subset _ ?_)
  simpa using hx

Depends on / 依赖: closedBall_subset_cthickening_singleton, cthickening_subset_of_subset
-/
theorem closedBall_subset_cthickening {α : Type*} [PseudoMetricSpace α] {x : α} {E : Set α}
    (hx : x in E) (δ : Real) : closedBall x δ subseteq cthickening δ E := by
  refine (closedBall_subset_cthickening_singleton _ _).trans (cthickening_subset_of_subset _ ?_)
  simpa using hx

/--
theorem `cthickening_subset_iUnion_closedBall_of_lt` / 定理 `cthickening_subset_iUnion_closedBall_of_lt`

English:
theorem cthickening_subset_iUnion_closedBall_of_lt
  statement: {α : Type*} [PseudoMetricSpace α] (E : Set α)
  proof: by
  refine (cthickening_subset_thickening' hδ₀ hδδ' E).trans fun x hx => ?_
  obtain ⟨y, hy₁, hy₂⟩ := mem_thickening_iff.mp hx
  exact mem_iUnion₂.mpr ⟨y, hy₁, hy₂.le⟩

中文:
定理 cthickening_subset_iUnion_closedBall_of_lt
  结论: {α : 类型} [PseudoMetricSpace α] (E : Set α)
  证明: by
  refine (cthickening_subset_thickening' hδ₀ hδδ' E).trans fun x hx => ?_
  obtain ⟨y, hy₁, hy₂⟩ := mem_thickening_iff.mp hx
  exact mem_iUnion₂.mpr ⟨y, hy₁, hy₂.le⟩

Depends on / 依赖: cthickening_subset_thickening, mem_thickening_iff, mem_thickening_iff.mp
-/
theorem cthickening_subset_iUnion_closedBall_of_lt {α : Type*} [PseudoMetricSpace α] (E : Set α)
    {δ δ' : Real} (hδ₀ : 0 < δ') (hδδ' : δ < δ') : cthickening δ E subseteq ⋃ x in E, closedBall x δ' := by
  refine (cthickening_subset_thickening' hδ₀ hδδ' E).trans fun x hx => ?_
  obtain ⟨y, hy₁, hy₂⟩ := mem_thickening_iff.mp hx
  exact mem_iUnion₂.mpr ⟨y, hy₁, hy₂.le⟩

/--
theorem `_root_.IsCompact.cthickening_eq_biUnion_closedBall` / 定理 `_root_.IsCompact.cthickening_eq_biUnion_closedBall`

English:
theorem _root_.IsCompact.cthickening_eq_biUnion_closedBall
  statement: {α : Type*} [PseudoMetricSpace α]
  proof: by
  rcases eq_empty_or_nonempty E with (rfl | hne)
  · simp only [cthickening_empty, biUnion_empty]
  refine Subset.antisymm (fun x hx => ?_)
    (iUnion₂_subset fun x hx => closedBall_subset_cthickening hx _)
  obtain ⟨y, yE, hy⟩ : exists y in E, infEDist x E = edist x y := hE.exists_infEDist_eq_e

中文:
定理 _root_.IsCompact.cthickening_eq_biUnion_closedBall
  结论: {α : 类型} [PseudoMetricSpace α]
  证明: by
  rcases eq_empty_or_nonempty E with (rfl | hne)
  · simp only [cthickening_empty, biUnion_empty]
  refine Subset.antisymm (fun x hx => ?_)
    (iUnion₂_subset fun x hx => closedBall_subset_cthickening hx _)
  obtain ⟨y, yE, hy⟩ : exists y in E, infEDist x E = edist x y := hE.exists_infEDist_eq_e

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.ofReal_le_ofReal_iff, Subset, Subset.antisymm, antisymm, biUnion_empty, closedBall_subset_cthickening, cthickening_empty, edist_dist, eq_empty_or_nonempty, exists_infEDist_eq_edist, hE.exists_infEDist_eq_edist, hy.symm, infEDist, le_of_eq, mem_biUnion, ofReal, ofReal_le_ofReal_iff
-/
theorem _root_.IsCompact.cthickening_eq_biUnion_closedBall {α : Type*} [PseudoMetricSpace α]
    {δ : Real} {E : Set α} (hE : IsCompact E) (hδ : 0 <= δ) :
    cthickening δ E = ⋃ x in E, closedBall x δ := by
  rcases eq_empty_or_nonempty E with (rfl | hne)
  · simp only [cthickening_empty, biUnion_empty]
  refine Subset.antisymm (fun x hx => ?_)
    (iUnion₂_subset fun x hx => closedBall_subset_cthickening hx _)
  obtain ⟨y, yE, hy⟩ : exists y in E, infEDist x E = edist x y := hE.exists_infEDist_eq_edist hne _
  have D1 : edist x y <= ENNReal.ofReal δ := (le_of_eq hy.symm).trans hx
  have D2 : dist x y <= δ := by
    rw [edist_dist] at D1
    exact (ENNReal.ofReal_le_ofReal_iff hδ).1 D1
  exact mem_biUnion yE D2

/--
theorem `cthickening_eq_biUnion_closedBall` / 定理 `cthickening_eq_biUnion_closedBall`

English:
theorem cthickening_eq_biUnion_closedBall
  statement: {α : Type*} [PseudoMetricSpace α] [ProperSpace α]
  proof: by
  rcases eq_empty_or_nonempty E with (rfl | hne)
  · simp only [cthickening_empty, biUnion_empty, closure_empty]
  rw [← cthickening_closure]
  refine Subset.antisymm (fun x hx => ?_)
    (iUnion₂_subset fun x hx => closedBall_subset_cthickening hx _)
  obtain ⟨y, yE, hy⟩ : exists y in closure E,

中文:
定理 cthickening_eq_biUnion_closedBall
  结论: {α : 类型} [PseudoMetricSpace α] [命题erSpace α]
  证明: by
  rcases eq_empty_or_nonempty E with (rfl | hne)
  · simp only [cthickening_empty, biUnion_empty, closure_empty]
  rw [← cthickening_closure]
  refine Subset.antisymm (fun x hx => ?_)
    (iUnion₂_subset fun x hx => closedBall_subset_cthickening hx _)
  obtain ⟨y, yE, hy⟩ : exists y in closure E,

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.ofReal_le_ofReal_iff, Subset, Subset.antisymm, antisymm, biUnion_empty, closedBall_subset_cthickening, closure, closure_empty, closure_nonempty_iff, closure_nonempty_iff.mpr, congr_arg, cthickening_closure, cthickening_empty, eq_empty_or_nonempty, exists_infDist_eq_dist, hy.symm, infDist, isClosed_closure
-/
theorem cthickening_eq_biUnion_closedBall {α : Type*} [PseudoMetricSpace α] [ProperSpace α]
    (E : Set α) (hδ : 0 <= δ) : cthickening δ E = ⋃ x in closure E, closedBall x δ := by
  rcases eq_empty_or_nonempty E with (rfl | hne)
  · simp only [cthickening_empty, biUnion_empty, closure_empty]
  rw [← cthickening_closure]
  refine Subset.antisymm (fun x hx => ?_)
    (iUnion₂_subset fun x hx => closedBall_subset_cthickening hx _)
  obtain ⟨y, yE, hy⟩ : exists y in closure E, infDist x (closure E) = dist x y :=
    isClosed_closure.exists_infDist_eq_dist (closure_nonempty_iff.mpr hne) x
  replace hy : dist x y <= δ :=
    (ENNReal.ofReal_le_ofReal_iff hδ).mp
      (((congr_arg ENNReal.ofReal hy.symm).le.trans ENNReal.ofReal_toReal_le).trans hx)
  exact mem_biUnion yE hy

nonrec theorem _root_.IsClosed.cthickening_eq_biUnion_closedBall {α : Type*} [PseudoMetricSpace α]
    [ProperSpace α] {E : Set α} (hE : IsClosed E) (hδ : 0 <= δ) :
    cthickening δ E = ⋃ x in E, closedBall x δ := by
  rw [cthickening_eq_biUnion_closedBall E hδ]; rw [hE.closure_eq]

/--
theorem `infEDist_le_infEDist_cthickening_add` / 定理 `infEDist_le_infEDist_cthickening_add`

English:
theorem infEDist_le_infEDist_cthickening_add
  proof: by
  refine le_of_forall_gt fun r h => ?_
  simp_rw [← lt_tsub_iff_right, infEDist_lt_iff, mem_cthickening_iff] at h
  obtain ⟨y, hy, hxy⟩ := h
  exact infEDist_le_edist_add_infEDist.trans_lt
    ((ENNReal.add_lt_add_of_lt_of_le (hy.trans_lt ENNReal.ofReal_lt_top).ne hxy hy).trans_eq
      (tsub_add

中文:
定理 infEDist_le_infEDist_cthickening_add
  证明: by
  refine le_of_forall_gt fun r h => ?_
  simp_rw [← lt_tsub_iff_right, infEDist_lt_iff, mem_cthickening_iff] at h
  obtain ⟨y, hy, hxy⟩ := h
  exact infEDist_le_edist_add_infEDist.trans_lt
    ((ENNReal.add_lt_add_of_lt_of_le (hy.trans_lt ENNReal.ofReal_lt_top).ne hxy hy).trans_eq
      (tsub_add

Depends on / 依赖: ENNReal, ENNReal.add_lt_add_of_lt_of_le, ENNReal.ofReal_lt_top, add_lt_add_of_lt_of_le, hy.trans_lt, infEDist_le_edist_add_infEDist, infEDist_le_edist_add_infEDist.trans_lt, infEDist_lt_iff, le_of_forall_gt, le_self_add, le_self_add.trans, lt_tsub_iff_left, lt_tsub_iff_right, mem_cthickening_iff, ofReal_lt_top, simp_rw, trans_eq, trans_lt, tsub_add_cancel_of_le
-/
theorem infEDist_le_infEDist_cthickening_add :
    infEDist x s <= infEDist x (cthickening δ s) + ENNReal.ofReal δ := by
  refine le_of_forall_gt fun r h => ?_
  simp_rw [← lt_tsub_iff_right, infEDist_lt_iff, mem_cthickening_iff] at h
  obtain ⟨y, hy, hxy⟩ := h
  exact infEDist_le_edist_add_infEDist.trans_lt
    ((ENNReal.add_lt_add_of_lt_of_le (hy.trans_lt ENNReal.ofReal_lt_top).ne hxy hy).trans_eq
      (tsub_add_cancel_of_le <| le_self_add.trans (lt_tsub_iff_left.1 hxy).le))

@[deprecated (since := "2026-01-08")]
alias infEdist_le_infEdist_cthickening_add := infEDist_le_infEDist_cthickening_add

/--
theorem `infEDist_le_infEDist_thickening_add` / 定理 `infEDist_le_infEDist_thickening_add`

English:
theorem infEDist_le_infEDist_thickening_add
  proof: infEDist_le_infEDist_cthickening_add.trans by gcongr; exact thickening_subset_cthickening ..

@[deprecated (since := "2026-01-08")]
alias infEdist_le_infEdist_thickening_add := infEDist_le_infEDist_thickening_add

中文:
定理 infEDist_le_infEDist_thickening_add
  证明: infEDist_le_infEDist_cthickening_add.trans by gcongr; exact thickening_subset_cthickening ..

@[deprecated (since := "2026-01-08")]
alias infEdist_le_infEdist_thickening_add := infEDist_le_infEDist_thickening_add

Depends on / 依赖: infEDist_le_infEDist_cthickening_add, infEDist_le_infEDist_cthickening_add.trans, thickening_subset_cthickening
-/
theorem infEDist_le_infEDist_thickening_add :
    infEDist x s <= infEDist x (thickening δ s) + ENNReal.ofReal δ :=
infEDist_le_infEDist_cthickening_add.trans by gcongr; exact thickening_subset_cthickening ..

@[deprecated (since := "2026-01-08")]
alias infEdist_le_infEdist_thickening_add := infEDist_le_infEDist_thickening_add

/-- For the equality, see `thickening_thickening`. -/
@[simp]
/--
theorem `thickening_thickening_subset` / 定理 `thickening_thickening_subset`

English:
theorem thickening_thickening_subset
  given: (ε δ : Real) (s : Set α)
  proof: by
  obtain hε | hε := le_total ε 0
  · simp only [thickening_of_nonpos hε, empty_subset]
  obtain hδ | hδ := le_total δ 0
  · simp only [thickening_of_nonpos hδ, thickening_empty, empty_subset]
  intro x
  simp_rw [mem_thickening_iff_exists_edist_lt, ENNReal.ofReal_add hε hδ]
  exact fun ⟨y, ⟨z, hz

中文:
定理 thickening_thickening_subset
  条件: (ε δ : 实数) (s : Set α)
  证明: by
  obtain hε | hε := le_total ε 0
  · simp only [thickening_of_nonpos hε, empty_subset]
  obtain hδ | hδ := le_total δ 0
  · simp only [thickening_of_nonpos hδ, thickening_empty, empty_subset]
  intro x
  simp_rw [mem_thickening_iff_exists_edist_lt, ENNReal.ofReal_add hε hδ]
  exact fun ⟨y, ⟨z, hz

Depends on / 依赖: ENNReal, ENNReal.add_lt_add, ENNReal.ofReal_add, add_lt_add, edist_triangle, empty_subset, le_total, mem_thickening_iff_exists_edist_lt, ofReal_add, simp_rw, thickening_empty, thickening_of_nonpos, trans_lt
-/
theorem thickening_thickening_subset (ε δ : Real) (s : Set α) :
    thickening ε (thickening δ s) subseteq thickening (ε + δ) s := by
  obtain hε | hε := le_total ε 0
  · simp only [thickening_of_nonpos hε, empty_subset]
  obtain hδ | hδ := le_total δ 0
  · simp only [thickening_of_nonpos hδ, thickening_empty, empty_subset]
  intro x
  simp_rw [mem_thickening_iff_exists_edist_lt, ENNReal.ofReal_add hε hδ]
  exact fun ⟨y, ⟨z, hz, hy⟩, hx⟩ =>
⟨z, hz, (edist_triangle _ _ _).trans_lt ENNReal.add_lt_add hx hy⟩

/-- For the equality, see `thickening_cthickening`. -/
@[simp]
/--
theorem `thickening_cthickening_subset` / 定理 `thickening_cthickening_subset`

English:
theorem thickening_cthickening_subset
  given: (ε : Real) (hδ : 0 <= δ) (s : Set α)
  proof: by
  obtain hε | hε := le_total ε 0
  · simp only [thickening_of_nonpos hε, empty_subset]
  intro x
  simp_rw [mem_thickening_iff_exists_edist_lt, mem_cthickening_iff, ← infEDist_lt_iff,
    ENNReal.ofReal_add hε hδ]
  rintro ⟨y, hy, hxy⟩
  exact infEDist_le_edist_add_infEDist.trans_lt
    (ENNReal.

中文:
定理 thickening_cthickening_subset
  条件: (ε : 实数) (hδ : 0 <= δ) (s : Set α)
  证明: by
  obtain hε | hε := le_total ε 0
  · simp only [thickening_of_nonpos hε, empty_subset]
  intro x
  simp_rw [mem_thickening_iff_exists_edist_lt, mem_cthickening_iff, ← infEDist_lt_iff,
    ENNReal.ofReal_add hε hδ]
  rintro ⟨y, hy, hxy⟩
  exact infEDist_le_edist_add_infEDist.trans_lt
    (ENNReal.

Depends on / 依赖: ENNReal, ENNReal.add_lt_add_of_lt_of_le, ENNReal.ofReal_add, ENNReal.ofReal_lt_top, add_lt_add_of_lt_of_le, empty_subset, hy.trans_lt, infEDist_le_edist_add_infEDist, infEDist_le_edist_add_infEDist.trans_lt, infEDist_lt_iff, le_total, mem_cthickening_iff, mem_thickening_iff_exists_edist_lt, ofReal_add, ofReal_lt_top, simp_rw, thickening_of_nonpos, trans_lt
-/
theorem thickening_cthickening_subset (ε : Real) (hδ : 0 <= δ) (s : Set α) :
    thickening ε (cthickening δ s) subseteq thickening (ε + δ) s := by
  obtain hε | hε := le_total ε 0
  · simp only [thickening_of_nonpos hε, empty_subset]
  intro x
  simp_rw [mem_thickening_iff_exists_edist_lt, mem_cthickening_iff, ← infEDist_lt_iff,
    ENNReal.ofReal_add hε hδ]
  rintro ⟨y, hy, hxy⟩
  exact infEDist_le_edist_add_infEDist.trans_lt
    (ENNReal.add_lt_add_of_lt_of_le (hy.trans_lt ENNReal.ofReal_lt_top).ne hxy hy)

/-- For the equality, see `cthickening_thickening`. -/
@[simp]
/--
theorem `cthickening_thickening_subset` / 定理 `cthickening_thickening_subset`

English:
theorem cthickening_thickening_subset
  given: (hε : 0 <= ε) (δ : Real) (s : Set α)
  proof: by
  obtain hδ | hδ := le_total δ 0
  · simp only [thickening_of_nonpos hδ, cthickening_empty, empty_subset]
  intro x
  simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ]
  exact fun hx => infEDist_le_infEDist_thickening_add.trans (by grw [hx])

中文:
定理 cthickening_thickening_subset
  条件: (hε : 0 <= ε) (δ : 实数) (s : Set α)
  证明: by
  obtain hδ | hδ := le_total δ 0
  · simp only [thickening_of_nonpos hδ, cthickening_empty, empty_subset]
  intro x
  simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ]
  exact fun hx => infEDist_le_infEDist_thickening_add.trans (by grw [hx])

Depends on / 依赖: ENNReal, ENNReal.ofReal_add, cthickening_empty, empty_subset, infEDist_le_infEDist_thickening_add, infEDist_le_infEDist_thickening_add.trans, le_total, mem_cthickening_iff, ofReal_add, simp_rw, thickening_of_nonpos
-/
theorem cthickening_thickening_subset (hε : 0 <= ε) (δ : Real) (s : Set α) :
    cthickening ε (thickening δ s) subseteq cthickening (ε + δ) s := by
  obtain hδ | hδ := le_total δ 0
  · simp only [thickening_of_nonpos hδ, cthickening_empty, empty_subset]
  intro x
  simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ]
  exact fun hx => infEDist_le_infEDist_thickening_add.trans (by grw [hx])

/-- For the equality, see `cthickening_cthickening`. -/
@[simp]
/--
theorem `cthickening_cthickening_subset` / 定理 `cthickening_cthickening_subset`

English:
theorem cthickening_cthickening_subset
  given: (hε : 0 <= ε) (hδ : 0 <= δ) (s : Set α)
  proof: by
  intro x
  simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ]
  exact fun hx => infEDist_le_infEDist_cthickening_add.trans (by grw [hx])

中文:
定理 cthickening_cthickening_subset
  条件: (hε : 0 <= ε) (hδ : 0 <= δ) (s : Set α)
  证明: by
  intro x
  simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ]
  exact fun hx => infEDist_le_infEDist_cthickening_add.trans (by grw [hx])

Depends on / 依赖: ENNReal, ENNReal.ofReal_add, infEDist_le_infEDist_cthickening_add, infEDist_le_infEDist_cthickening_add.trans, mem_cthickening_iff, ofReal_add, simp_rw
-/
theorem cthickening_cthickening_subset (hε : 0 <= ε) (hδ : 0 <= δ) (s : Set α) :
    cthickening ε (cthickening δ s) subseteq cthickening (ε + δ) s := by
  intro x
  simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ]
  exact fun hx => infEDist_le_infEDist_cthickening_add.trans (by grw [hx])

open scoped Function in -- required for scoped `on` notation
/--
theorem `frontier_cthickening_disjoint` / 定理 `frontier_cthickening_disjoint`

English:
theorem frontier_cthickening_disjoint
  given: (A : Set α)
  proof: fun r₁ r₂ hr =>
  ((disjoint_singleton.2 <| by simpa).preimage _).mono (frontier_cthickening_subset _)
    (frontier_cthickening_subset _)

中文:
定理 frontier_cthickening_disjoint
  条件: (A : Set α)
  证明: fun r₁ r₂ hr =>
  ((disjoint_singleton.2 <| by simpa).preimage _).mono (frontier_cthickening_subset _)
    (frontier_cthickening_subset _)
-/
theorem frontier_cthickening_disjoint (A : Set α) :
    Pairwise (Disjoint on fun r : Real>=0 => frontier (cthickening r A)) := fun r₁ r₂ hr =>
  ((disjoint_singleton.2 <| by simpa).preimage _).mono (frontier_cthickening_subset _)
    (frontier_cthickening_subset _)

end Cthickening

section PseudoMetricSpace

variable {α β E : Type*} [PseudoMetricSpace α] {l : Filter β} {s : Set α}

/--
theorem `thickening_ball` / 定理 `thickening_ball`

English:
theorem thickening_ball
  given: (x : α) (ε δ : Real)
  proof: by
  rw [← thickening_singleton]; rw [← thickening_singleton]
  apply thickening_thickening_subset

中文:
定理 thickening_ball
  条件: (x : α) (ε δ : 实数)
  证明: by
  rw [← thickening_singleton]; rw [← thickening_singleton]
  apply thickening_thickening_subset

Depends on / 依赖: thickening_singleton, thickening_thickening_subset
-/
theorem thickening_ball (x : α) (ε δ : Real) :
    thickening ε (ball x δ) subseteq ball x (ε + δ) := by
  rw [← thickening_singleton]; rw [← thickening_singleton]
  apply thickening_thickening_subset

/--
theorem `tendsto_nhdsSet` / 定理 `tendsto_nhdsSet`

English:
theorem tendsto_nhdsSet
  given: {f : β -> α} (hs₁ : IsCompact s) (hs₂ : Set.Nonempty s)
  proof: by
  rw [(hasBasis_nhdsSet_thickening hs₁).tendsto_right_iff]
  congrm (forall ε hε, ?_)
  simp [mem_thickening_iff_infDist_lt hs₂]

中文:
定理 tendsto_nhdsSet
  条件: {f : β -> α} (hs₁ : IsCompact s) (hs₂ : Set.Nonempty s)
  证明: by
  rw [(hasBasis_nhdsSet_thickening hs₁).tendsto_right_iff]
  congrm (forall ε hε, ?_)
  simp [mem_thickening_iff_infDist_lt hs₂]

Depends on / 依赖: congrm, hasBasis_nhdsSet_thickening, mem_thickening_iff_infDist_lt, tendsto_right_iff
-/
theorem tendsto_nhdsSet {f : β -> α} (hs₁ : IsCompact s) (hs₂ : Set.Nonempty s) :
    Tendsto f l (𝓝ˢ s) ↔ forall ε > 0, forallᶠ x in l, infDist (f x) s < ε := by
  rw [(hasBasis_nhdsSet_thickening hs₁).tendsto_right_iff]
  congrm (forall ε hε, ?_)
  simp [mem_thickening_iff_infDist_lt hs₂]

/--
theorem `mem_nhdsSet_iff` / 定理 `mem_nhdsSet_iff`

English:
theorem mem_nhdsSet_iff
  given: {t : Set α} (hs : IsCompact s)
  proof: by
  rw [(hasBasis_nhdsSet_thickening hs).mem_iff]

中文:
定理 mem_nhdsSet_iff
  条件: {t : Set α} (hs : IsCompact s)
  证明: by
  rw [(hasBasis_nhdsSet_thickening hs).mem_iff]

Depends on / 依赖: hasBasis_nhdsSet_thickening, mem_iff
-/
theorem mem_nhdsSet_iff {t : Set α} (hs : IsCompact s) :
    t in 𝓝ˢ s ↔ exists ε > 0, Metric.thickening ε s subseteq t := by
  rw [(hasBasis_nhdsSet_thickening hs).mem_iff]

end PseudoMetricSpace

end Metric

section Clopen

open Metric

variable [PseudoEMetricSpace α] {s : Set α}

/--
lemma `IsClopen.of_thickening_subset_self` / 引理 `IsClopen.of_thickening_subset_self`

English:
lemma IsClopen.of_thickening_subset_self
  given: {δ : Real} (hδ : 0 < δ) (hs : thickening δ s subseteq s)
  proof: by
  replace hs : thickening δ s = s := le_antisymm hs (self_subset_thickening hδ s)
  refine ⟨?_, hs ▸ isOpen_thickening⟩
  rw [← closure_subset_iff_isClosed]; rw [closure_eq_iInter_thickening]
.trans_eq hs exact Set.iInter₂_subset δ hδ

中文:
引理 IsClopen.of_thickening_subset_self
  条件: {δ : 实数} (hδ : 0 < δ) (hs : thickening δ s subseteq s)
  证明: by
  replace hs : thickening δ s = s := le_antisymm hs (self_subset_thickening hδ s)
  refine ⟨?_, hs ▸ isOpen_thickening⟩
  rw [← closure_subset_iff_isClosed]; rw [closure_eq_iInter_thickening]
.trans_eq hs exact Set.iInter₂_subset δ hδ

Depends on / 依赖: Set.iInter, closure_eq_iInter_thickening, closure_subset_iff_isClosed, isOpen_thickening, le_antisymm, replace, self_subset_thickening, thickening, trans_eq
-/
lemma IsClopen.of_thickening_subset_self {δ : Real} (hδ : 0 < δ) (hs : thickening δ s subseteq s) :
    IsClopen s := by
  replace hs : thickening δ s = s := le_antisymm hs (self_subset_thickening hδ s)
  refine ⟨?_, hs ▸ isOpen_thickening⟩
  rw [← closure_subset_iff_isClosed]; rw [closure_eq_iInter_thickening]
.trans_eq hs exact Set.iInter₂_subset δ hδ

/--
lemma `IsClopen.of_cthickening_subset_self` / 引理 `IsClopen.of_cthickening_subset_self`

English:
lemma IsClopen.of_cthickening_subset_self
  given: {δ : Real} (hδ : 0 < δ) (hs : cthickening δ s subseteq s)
  proof: .of_thickening_subset_self hδ (thickening_subset_cthickening δ s).trans hs

中文:
引理 IsClopen.of_cthickening_subset_self
  条件: {δ : 实数} (hδ : 0 < δ) (hs : cthickening δ s subseteq s)
  证明: .of_thickening_subset_self hδ (thickening_subset_cthickening δ s).trans hs

Depends on / 依赖: of_thickening_subset_self, thickening_subset_cthickening
-/
lemma IsClopen.of_cthickening_subset_self {δ : Real} (hδ : 0 < δ) (hs : cthickening δ s subseteq s) :
    IsClopen s :=
.of_thickening_subset_self hδ (thickening_subset_cthickening δ s).trans hs

end Clopen

open Metric in
/--
theorem `IsCompact.exists_thickening_image_subset` / 定理 `IsCompact.exists_thickening_image_subset`

English:
theorem IsCompact.exists_thickening_image_subset
  proof: by
  apply hK.induction_on (p := fun K => exists ε > 0, exists V in 𝓝ˢ K, thickening ε (f '' V) subseteq U)
  · use 1, by positivity, ∅, by simp, by simp
  · exact fun s t hst ⟨ε, hε, V, hV, hthickening⟩ => ⟨ε, hε, V, nhdsSet_mono hst hV, hthickening⟩
  · rintro s t ⟨ε₁, hε₁, V₁, hV₁, hV₁thickening⟩

中文:
定理 IsCompact.exists_thickening_image_subset
  证明: by
  apply hK.induction_on (p := fun K => exists ε > 0, exists V in 𝓝ˢ K, thickening ε (f '' V) subseteq U)
  · use 1, by positivity, ∅, by simp, by simp
  · exact fun s t hst ⟨ε, hε, V, hV, hthickening⟩ => ⟨ε, hε, V, nhdsSet_mono hst hV, hthickening⟩
  · rintro s t ⟨ε₁, hε₁, V₁, hV₁, hV₁thickening⟩

Depends on / 依赖: hK.induction_on, hthickening, image_union, induction_on, nhdsSet_mono, subseteq, thickening, thickening_union, union_mem_nhdsSet
-/
theorem IsCompact.exists_thickening_image_subset
    [PseudoEMetricSpace α] {β : Type*} [PseudoEMetricSpace β]
    {f : α -> β} {K : Set α} {U : Set β} (hK : IsCompact K) (ho : IsOpen U)
    (hf : forall x in K, ContinuousAt f x) (hKU : MapsTo f K U) :
    exists ε > 0, exists V in 𝓝ˢ K, thickening ε (f '' V) subseteq U := by
  apply hK.induction_on (p := fun K => exists ε > 0, exists V in 𝓝ˢ K, thickening ε (f '' V) subseteq U)
  · use 1, by positivity, ∅, by simp, by simp
  · exact fun s t hst ⟨ε, hε, V, hV, hthickening⟩ => ⟨ε, hε, V, nhdsSet_mono hst hV, hthickening⟩
  · rintro s t ⟨ε₁, hε₁, V₁, hV₁, hV₁thickening⟩ ⟨ε₂, hε₂, V₂, hV₂, hV₂thickening⟩
    refine ⟨min ε₁ ε₂, by positivity, V₁ union V₂, union_mem_nhdsSet hV₁ hV₂, ?_⟩
    rw [image_union]; rw [thickening_union]
    calc thickening (ε₁ ⊓ ε₂) (f '' V₁) union thickening (ε₁ ⊓ ε₂) (f '' V₂)
      _ subseteq thickening ε₁ (f '' V₁) union thickening ε₂ (f '' V₂) := by gcongr <;> norm_num
      _ subseteq U union U := by gcongr
      _ = U := union_self _
  · intro x hx
    have : {f x} subseteq U := by rw [singleton_subset_iff]; exact hKU hx
    obtain ⟨δ, hδ, hthick⟩ := (isCompact_singleton (x := f x)).exists_thickening_subset_open ho this
    let V := f ⁻¹' (thickening (δ / 2) {f x})
    have : V in 𝓝 x := by
      apply hf x hx
      apply isOpen_thickening.mem_nhds
      exact (self_subset_thickening (by positivity) _) rfl
    refine ⟨K inter (interior V), inter_mem_nhdsWithin K (interior_mem_nhds.mpr this),
      δ / 2, by positivity, V, by rw [← subset_interior_iff_mem_nhdsSet]; simp, ?_⟩
    calc thickening (δ / 2) (f '' V)
      _ subseteq thickening (δ / 2) (thickening (δ / 2) {f x}) :=
        thickening_subset_of_subset _ (image_preimage_subset f _)
      _ subseteq thickening ((δ / 2) + (δ / 2)) ({f x}) :=
        thickening_thickening_subset (δ / 2) (δ / 2) {f x}
      _ subseteq U := by simp [hthick]
