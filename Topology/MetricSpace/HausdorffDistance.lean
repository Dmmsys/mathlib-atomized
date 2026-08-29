/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Tactic.Finiteness

/-!
# Hausdorff distance

The Hausdorff distance on subsets of a metric (or emetric) space.

Given two subsets `s` and `t` of a metric space, their Hausdorff distance is the smallest `d`
such that any point of `s` is within `d` of a point in `t`, and conversely. This quantity
is often infinite (think of `s` bounded and `t` unbounded), and therefore better
expressed in the setting of emetric spaces.

## Main definitions

This file introduces:
* `Metric.infEDist x s`, the infimum edistance of a point `x` to a set `s` in an emetric space
* `Metric.hausdorffEDist s t`, the Hausdorff edistance of two sets in an emetric space
* Versions of these notions on metric spaces, called respectively `Metric.infDist`
  and `Metric.hausdorffDist`

## Main results
* `infEDist_closure`: the edistance to a set and its closure coincide
* `Metric.mem_closure_iff_infEDist_zero`: a point `x` belongs to the closure of `s` iff
  `infEDist x s = 0`
* `IsCompact.exists_infEDist_eq_edist`: if `s` is compact and non-empty, there exists a point `y`
  which attains this edistance
* `IsOpen.exists_iUnion_isClosed`: every open set `U` can be written as the increasing union
  of countably many closed subsets of `U`

* `hausdorffEDist_closure`: replacing a set by its closure does not change the Hausdorff edistance
* `hausdorffEDist_zero_iff_closure_eq_closure`: two sets have Hausdorff edistance zero
  iff their closures coincide
* the Hausdorff edistance is symmetric and satisfies the triangle inequality
* in particular, closed sets in an emetric space are an emetric space
  (this is shown in `EMetricSpace.Closeds.emetricSpace`)

* versions of these notions on metric spaces
* `hausdorffEDist_ne_top_of_nonempty_of_bounded`: if two sets in a metric space
  are nonempty and bounded in a metric space, they are at finite Hausdorff edistance.

## Tags
metric space, Hausdorff distance
-/

@[expose] public section


noncomputable section

open NNReal ENNReal Topology Set Filter Pointwise Bornology

universe u v w

variable {ι : Sort*} {α : Type u} {β : Type v}

namespace Metric

section InfEDist

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {x y : α} {s t : Set α} {Φ : α -> β}

/-! ### Distance of a point to a set as a function into `ℝ≥0∞`. -/

/--
Definition of `infEDist` / `infEDist` 的定义

English:
definition infEDist
  signature: (x : α) (s : Set α)
  body: ⨅ y in s, edist x y

@[simp]

中文:
定义 infEDist
  签名: (x : α) (s : Set α)
  定义体: ⨅ y in s, edist x y

@[simp]
-/
def infEDist (x : α) (s : Set α) : Real>=0∞ :=
  ⨅ y in s, edist x y

@[simp]
/--
theorem `infEDist_empty` / 定理 `infEDist_empty`

English:
theorem infEDist_empty
  statement: infEDist x ∅ = ∞
  proof: iInf_emptyset

中文:
定理 infEDist_empty
  结论: infEDist x ∅ = ∞
  证明: iInf_emptyset

Depends on / 依赖: iInf_emptyset
-/
theorem infEDist_empty : infEDist x ∅ = ∞ :=
  iInf_emptyset

/--
theorem `le_infEDist` / 定理 `le_infEDist`

English:
theorem le_infEDist
  given: {d}
  statement: d <= infEDist x s ↔ forall y in s, d <= edist x y
  proof: by
  simp only [infEDist, le_iInf_iff]

中文:
定理 le_infEDist
  条件: {d}
  结论: d <= infEDist x s ↔ 对任意 y in s, d <= edist x y
  证明: by
  simp only [infEDist, le_iInf_iff]

Depends on / 依赖: infEDist, le_iInf_iff
-/
theorem le_infEDist {d} : d <= infEDist x s ↔ forall y in s, d <= edist x y := by
  simp only [infEDist, le_iInf_iff]

/-- The edist to a union is the minimum of the edists -/
@[simp]
/--
theorem `infEDist_union` / 定理 `infEDist_union`

English:
theorem infEDist_union
  statement: infEDist x (s union t) = infEDist x s ⊓ infEDist x t
  proof: iInf_union

@[simp]

中文:
定理 infEDist_union
  结论: infEDist x (s union t) = infEDist x s ⊓ infEDist x t
  证明: iInf_union

@[simp]

Depends on / 依赖: iInf_union
-/
theorem infEDist_union : infEDist x (s union t) = infEDist x s ⊓ infEDist x t :=
  iInf_union

@[simp]
/--
theorem `infEDist_iUnion` / 定理 `infEDist_iUnion`

English:
theorem infEDist_iUnion
  given: (f : ι -> Set α) (x : α)
  statement: infEDist x (⋃ i, f i) = ⨅ i, infEDist x (f i)
  proof: iInf_iUnion f _

中文:
定理 infEDist_iUnion
  条件: (f : ι -> Set α) (x : α)
  结论: infEDist x (⋃ i, f i) = ⨅ i, infEDist x (f i)
  证明: iInf_iUnion f _

Depends on / 依赖: iInf_iUnion
-/
theorem infEDist_iUnion (f : ι -> Set α) (x : α) : infEDist x (⋃ i, f i) = ⨅ i, infEDist x (f i) :=
  iInf_iUnion f _

/--
lemma `infEDist_biUnion` / 引理 `infEDist_biUnion`

English:
lemma infEDist_biUnion
  given: {ι : Type*} (f : ι -> Set α) (I : Set ι) (x : α)
  proof: by simp only [infEDist_iUnion]

中文:
引理 infEDist_biUnion
  条件: {ι : 类型} (f : ι -> Set α) (I : Set ι) (x : α)
  证明: by simp only [infEDist_iUnion]

Depends on / 依赖: infEDist_iUnion
-/
lemma infEDist_biUnion {ι : Type*} (f : ι -> Set α) (I : Set ι) (x : α) :
    infEDist x (⋃ i in I, f i) = ⨅ i in I, infEDist x (f i) := by simp only [infEDist_iUnion]

/-- The edist to a singleton is the edistance to the single point of this singleton -/
@[simp]
/--
theorem `infEDist_singleton` / 定理 `infEDist_singleton`

English:
theorem infEDist_singleton
  statement: infEDist x {y} = edist x y
  proof: iInf_singleton

中文:
定理 infEDist_singleton
  结论: infEDist x {y} = edist x y
  证明: iInf_singleton

Depends on / 依赖: iInf_singleton
-/
theorem infEDist_singleton : infEDist x {y} = edist x y :=
  iInf_singleton

/--
theorem `infEDist_le_edist_of_mem` / 定理 `infEDist_le_edist_of_mem`

English:
theorem infEDist_le_edist_of_mem
  given: (h : y in s)
  statement: infEDist x s <= edist x y
  proof: iInf₂_le y h

中文:
定理 infEDist_le_edist_of_mem
  条件: (h : y in s)
  结论: infEDist x s <= edist x y
  证明: iInf₂_le y h
-/
theorem infEDist_le_edist_of_mem (h : y in s) : infEDist x s <= edist x y :=
  iInf₂_le y h

/--
theorem `infEDist_zero_of_mem` / 定理 `infEDist_zero_of_mem`

English:
theorem infEDist_zero_of_mem
  given: (h : x in s)
  statement: infEDist x s = 0
  proof: nonpos_iff_eq_zero.1 @edist_self _ _ x ▸ infEDist_le_edist_of_mem h

中文:
定理 infEDist_zero_of_mem
  条件: (h : x in s)
  结论: infEDist x s = 0
  证明: nonpos_iff_eq_zero.1 @edist_self _ _ x ▸ infEDist_le_edist_of_mem h

Depends on / 依赖: edist_self, infEDist_le_edist_of_mem, nonpos_iff_eq_zero
-/
theorem infEDist_zero_of_mem (h : x in s) : infEDist x s = 0 :=
nonpos_iff_eq_zero.1 @edist_self _ _ x ▸ infEDist_le_edist_of_mem h

/-- The edist is antitone with respect to inclusion. -/
@[gcongr]
/--
theorem `infEDist_anti` / 定理 `infEDist_anti`

English:
theorem infEDist_anti
  given: (h : s subseteq t)
  statement: infEDist x t <= infEDist x s
  proof: iInf_le_iInf_of_subset h

中文:
定理 infEDist_anti
  条件: (h : s subseteq t)
  结论: infEDist x t <= infEDist x s
  证明: iInf_le_iInf_of_subset h

Depends on / 依赖: iInf_le_iInf_of_subset
-/
theorem infEDist_anti (h : s subseteq t) : infEDist x t <= infEDist x s :=
  iInf_le_iInf_of_subset h

/--
theorem `infEDist_lt_iff` / 定理 `infEDist_lt_iff`

English:
theorem infEDist_lt_iff
  given: {r : Real>=0∞}
  statement: infEDist x s < r ↔ exists y in s, edist x y < r
  proof: by
  simp_rw [infEDist, iInf_lt_iff, exists_prop]

中文:
定理 infEDist_lt_iff
  条件: {r : 实数>=0∞}
  结论: infEDist x s < r ↔ 存在 y in s, edist x y < r
  证明: by
  simp_rw [infEDist, iInf_lt_iff, exists_prop]

Depends on / 依赖: exists_prop, iInf_lt_iff, infEDist, simp_rw
-/
theorem infEDist_lt_iff {r : Real>=0∞} : infEDist x s < r ↔ exists y in s, edist x y < r := by
  simp_rw [infEDist, iInf_lt_iff, exists_prop]

/--
theorem `infEDist_le_infEDist_add_edist` / 定理 `infEDist_le_infEDist_add_edist`

English:
theorem infEDist_le_infEDist_add_edist
  statement: infEDist x s <= infEDist y s + edist x y
  proof: calc
    ⨅ z in s, edist x z <= ⨅ z in s, edist y z + edist x y :=
      iInf₂_mono fun _ _ => (edist_triangle _ _ _).trans_eq (add_comm _ _)
    _ = (⨅ z in s, edist y z) + edist x y := by simp only [ENNReal.iInf_add]

中文:
定理 infEDist_le_infEDist_add_edist
  结论: infEDist x s <= infEDist y s + edist x y
  证明: calc
    ⨅ z in s, edist x z <= ⨅ z in s, edist y z + edist x y :=
      iInf₂_mono fun _ _ => (edist_triangle _ _ _).trans_eq (add_comm _ _)
    _ = (⨅ z in s, edist y z) + edist x y := by simp only [ENNReal.iInf_add]

Depends on / 依赖: ENNReal, ENNReal.iInf_add, add_comm, edist_triangle, iInf_add, trans_eq
-/
theorem infEDist_le_infEDist_add_edist : infEDist x s <= infEDist y s + edist x y :=
  calc
    ⨅ z in s, edist x z <= ⨅ z in s, edist y z + edist x y :=
      iInf₂_mono fun _ _ => (edist_triangle _ _ _).trans_eq (add_comm _ _)
    _ = (⨅ z in s, edist y z) + edist x y := by simp only [ENNReal.iInf_add]

/--
theorem `infEDist_le_edist_add_infEDist` / 定理 `infEDist_le_edist_add_infEDist`

English:
theorem infEDist_le_edist_add_infEDist
  statement: infEDist x s <= edist x y + infEDist y s
  proof: by
  rw [add_comm]
  exact infEDist_le_infEDist_add_edist

中文:
定理 infEDist_le_edist_add_infEDist
  结论: infEDist x s <= edist x y + infEDist y s
  证明: by
  rw [add_comm]
  exact infEDist_le_infEDist_add_edist

Depends on / 依赖: add_comm, infEDist_le_infEDist_add_edist
-/
theorem infEDist_le_edist_add_infEDist : infEDist x s <= edist x y + infEDist y s := by
  rw [add_comm]
  exact infEDist_le_infEDist_add_edist

/--
theorem `edist_le_infEDist_add_ediam` / 定理 `edist_le_infEDist_add_ediam`

English:
theorem edist_le_infEDist_add_ediam
  given: (hy : y in s)
  statement: edist x y <= infEDist x s + Metric.ediam s
  proof: by
  simp_rw [infEDist, ENNReal.iInf_add]
  refine le_iInf₂ fun i hi => ?_
  calc
    edist x y <= edist x i + edist i y := edist_triangle _ _ _
    _ <= edist x i + Metric.ediam s := add_le_add le_rfl (Metric.edist_le_ediam_of_mem hi hy)

中文:
定理 edist_le_infEDist_add_ediam
  条件: (hy : y in s)
  结论: edist x y <= infEDist x s + Metric.ediam s
  证明: by
  simp_rw [infEDist, ENNReal.iInf_add]
  refine le_iInf₂ fun i hi => ?_
  calc
    edist x y <= edist x i + edist i y := edist_triangle _ _ _
    _ <= edist x i + Metric.ediam s := add_le_add le_rfl (Metric.edist_le_ediam_of_mem hi hy)

Depends on / 依赖: ENNReal, ENNReal.iInf_add, Metric, Metric.ediam, Metric.edist_le_ediam_of_mem, add_le_add, edist_le_ediam_of_mem, edist_triangle, iInf_add, infEDist, le_rfl, simp_rw
-/
theorem edist_le_infEDist_add_ediam (hy : y in s) : edist x y <= infEDist x s + Metric.ediam s := by
  simp_rw [infEDist, ENNReal.iInf_add]
  refine le_iInf₂ fun i hi => ?_
  calc
    edist x y <= edist x i + edist i y := edist_triangle _ _ _
    _ <= edist x i + Metric.ediam s := add_le_add le_rfl (Metric.edist_le_ediam_of_mem hi hy)

/-- The edist to a set depends continuously on the point -/
@[continuity, fun_prop]
/--
theorem `continuous_infEDist` / 定理 `continuous_infEDist`

English:
theorem continuous_infEDist
  statement: Continuous fun x => infEDist x s
  proof: continuous_of_le_add_edist 1 (by simp) by
    simp only [one_mul, infEDist_le_infEDist_add_edist, forall₂_true_iff]

中文:
定理 continuous_infEDist
  结论: Continuous fun x => infEDist x s
  证明: continuous_of_le_add_edist 1 (by simp) by
    simp only [one_mul, infEDist_le_infEDist_add_edist, forall₂_true_iff]

Depends on / 依赖: continuous_of_le_add_edist, infEDist_le_infEDist_add_edist, one_mul
-/
theorem continuous_infEDist : Continuous fun x => infEDist x s :=
continuous_of_le_add_edist 1 (by simp) by
    simp only [one_mul, infEDist_le_infEDist_add_edist, forall₂_true_iff]

/--
theorem `infEDist_closure` / 定理 `infEDist_closure`

English:
theorem infEDist_closure
  statement: infEDist x (closure s) = infEDist x s
  proof: by
  refine le_antisymm (infEDist_anti subset_closure) ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε εpos h => ?_
  have ε0 : 0 < (ε / 2 : Real>=0∞) := by simpa [pos_iff_ne_zero] using εpos
  have : infEDist x (closure s) < infEDist x (closure s) + ε / 2 :=
    ENNReal.lt_add_right h.ne ε0.ne'
 

中文:
定理 infEDist_closure
  结论: infEDist x (closure s) = infEDist x s
  证明: by
  refine le_antisymm (infEDist_anti subset_closure) ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε εpos h => ?_
  have ε0 : 0 < (ε / 2 : Real>=0∞) := by simpa [pos_iff_ne_zero] using εpos
  have : infEDist x (closure s) < infEDist x (closure s) + ε / 2 :=
    ENNReal.lt_add_right h.ne ε0.ne'
 

Depends on / 依赖: EMetric, EMetric.mem_closure_iff, ENNReal, ENNReal.le_of_forall_pos_le_add, ENNReal.lt_add_right, closure, h.ne, infEDist, infEDist_anti, infEDist_lt_iff, infEDist_lt_iff.mp, le_antisymm, le_of_forall_pos_le_add, lt_add_right, mem_closure_iff, pos_iff_ne_zero, subset_closure
-/
theorem infEDist_closure : infEDist x (closure s) = infEDist x s := by
  refine le_antisymm (infEDist_anti subset_closure) ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε εpos h => ?_
  have ε0 : 0 < (ε / 2 : Real>=0∞) := by simpa [pos_iff_ne_zero] using εpos
  have : infEDist x (closure s) < infEDist x (closure s) + ε / 2 :=
    ENNReal.lt_add_right h.ne ε0.ne'
  obtain ⟨y : α, ycs : y in closure s, hy : edist x y < infEDist x (closure s) + ↑ε / 2⟩ :=
    infEDist_lt_iff.mp this
  obtain ⟨z : α, zs : z in s, dyz : edist y z < ↑ε / 2⟩ := EMetric.mem_closure_iff.1 ycs (ε / 2) ε0
  calc
    infEDist x s <= edist x z := infEDist_le_edist_of_mem zs
    _ <= edist x y + edist y z := edist_triangle _ _ _
    _ <= infEDist x (closure s) + ε / 2 + ε / 2 := add_le_add (le_of_lt hy) (le_of_lt dyz)
    _ = infEDist x (closure s) + ↑ε := by rw [add_assoc, ENNReal.add_halves]

/--
theorem `mem_closure_iff_infEDist_zero` / 定理 `mem_closure_iff_infEDist_zero`

English:
theorem mem_closure_iff_infEDist_zero
  statement: x in closure s ↔ infEDist x s = 0
  proof: ⟨fun h => by
    rw [← infEDist_closure]
    exact infEDist_zero_of_mem h,
   fun h =>
EMetric.mem_closure_iff.2 fun ε εpos => infEDist_lt_iff.mp by rwa [h]⟩

中文:
定理 mem_closure_iff_infEDist_zero
  结论: x in closure s ↔ infEDist x s = 0
  证明: ⟨fun h => by
    rw [← infEDist_closure]
    exact infEDist_zero_of_mem h,
   fun h =>
EMetric.mem_closure_iff.2 fun ε εpos => infEDist_lt_iff.mp by rwa [h]⟩

Depends on / 依赖: EMetric, EMetric.mem_closure_iff, infEDist_closure, infEDist_lt_iff, infEDist_lt_iff.mp, infEDist_zero_of_mem, mem_closure_iff
-/
theorem mem_closure_iff_infEDist_zero : x in closure s ↔ infEDist x s = 0 :=
  ⟨fun h => by
    rw [← infEDist_closure]
    exact infEDist_zero_of_mem h,
   fun h =>
EMetric.mem_closure_iff.2 fun ε εpos => infEDist_lt_iff.mp by rwa [h]⟩

/--
theorem `mem_iff_infEDist_zero_of_closed` / 定理 `mem_iff_infEDist_zero_of_closed`

English:
theorem mem_iff_infEDist_zero_of_closed
  given: (h : IsClosed s)
  statement: x in s ↔ infEDist x s = 0
  proof: by
  rw [← mem_closure_iff_infEDist_zero]; rw [h.closure_eq]

中文:
定理 mem_iff_infEDist_zero_of_closed
  条件: (h : IsClosed s)
  结论: x in s ↔ infEDist x s = 0
  证明: by
  rw [← mem_closure_iff_infEDist_zero]; rw [h.closure_eq]

Depends on / 依赖: closure_eq, h.closure_eq, mem_closure_iff_infEDist_zero
-/
theorem mem_iff_infEDist_zero_of_closed (h : IsClosed s) : x in s ↔ infEDist x s = 0 := by
  rw [← mem_closure_iff_infEDist_zero]; rw [h.closure_eq]

/--
theorem `infEDist_pos_iff_notMem_closure` / 定理 `infEDist_pos_iff_notMem_closure`

English:
theorem infEDist_pos_iff_notMem_closure
  given: {x : α} {E : Set α}
  proof: by
  rw [mem_closure_iff_infEDist_zero]; rw [pos_iff_ne_zero]

中文:
定理 infEDist_pos_iff_notMem_closure
  条件: {x : α} {E : Set α}
  证明: by
  rw [mem_closure_iff_infEDist_zero]; rw [pos_iff_ne_zero]

Depends on / 依赖: mem_closure_iff_infEDist_zero, pos_iff_ne_zero
-/
theorem infEDist_pos_iff_notMem_closure {x : α} {E : Set α} :
    0 < infEDist x E ↔ x ∉ closure E := by
  rw [mem_closure_iff_infEDist_zero]; rw [pos_iff_ne_zero]

/--
theorem `infEDist_closure_pos_iff_notMem_closure` / 定理 `infEDist_closure_pos_iff_notMem_closure`

English:
theorem infEDist_closure_pos_iff_notMem_closure
  given: {x : α} {E : Set α}
  proof: by
  rw [infEDist_closure]; rw [infEDist_pos_iff_notMem_closure]

中文:
定理 infEDist_closure_pos_iff_notMem_closure
  条件: {x : α} {E : Set α}
  证明: by
  rw [infEDist_closure]; rw [infEDist_pos_iff_notMem_closure]

Depends on / 依赖: infEDist_closure, infEDist_pos_iff_notMem_closure
-/
theorem infEDist_closure_pos_iff_notMem_closure {x : α} {E : Set α} :
    0 < infEDist x (closure E) ↔ x ∉ closure E := by
  rw [infEDist_closure]; rw [infEDist_pos_iff_notMem_closure]

/--
theorem `exists_real_pos_lt_infEDist_of_notMem_closure` / 定理 `exists_real_pos_lt_infEDist_of_notMem_closure`

English:
theorem exists_real_pos_lt_infEDist_of_notMem_closure
  given: {x : α} {E : Set α} (h : x ∉ closure E)
  proof: by
  rw [← infEDist_pos_iff_notMem_closure]; rw [ENNReal.lt_iff_exists_real_btwn] at h
  rcases h with ⟨ε, ⟨_, ⟨ε_pos, ε_lt⟩⟩⟩
  exact ⟨ε, ⟨ENNReal.ofReal_pos.mp ε_pos, ε_lt⟩⟩

中文:
定理 exists_real_pos_lt_infEDist_of_notMem_closure
  条件: {x : α} {E : Set α} (h : x ∉ closure E)
  证明: by
  rw [← infEDist_pos_iff_notMem_closure]; rw [ENNReal.lt_iff_exists_real_btwn] at h
  rcases h with ⟨ε, ⟨_, ⟨ε_pos, ε_lt⟩⟩⟩
  exact ⟨ε, ⟨ENNReal.ofReal_pos.mp ε_pos, ε_lt⟩⟩

Depends on / 依赖: ENNReal, ENNReal.lt_iff_exists_real_btwn, ENNReal.ofReal_pos.mp, infEDist_pos_iff_notMem_closure, lt_iff_exists_real_btwn, ofReal_pos
-/
theorem exists_real_pos_lt_infEDist_of_notMem_closure {x : α} {E : Set α} (h : x ∉ closure E) :
    exists ε : Real, 0 < ε ∧ ENNReal.ofReal ε < infEDist x E := by
  rw [← infEDist_pos_iff_notMem_closure]; rw [ENNReal.lt_iff_exists_real_btwn] at h
  rcases h with ⟨ε, ⟨_, ⟨ε_pos, ε_lt⟩⟩⟩
  exact ⟨ε, ⟨ENNReal.ofReal_pos.mp ε_pos, ε_lt⟩⟩

/--
theorem `disjoint_closedEBall_of_lt_infEDist` / 定理 `disjoint_closedEBall_of_lt_infEDist`

English:
theorem disjoint_closedEBall_of_lt_infEDist
  given: {r : Real>=0∞} (h : r < infEDist x s)
  proof: by
  rw [disjoint_left]
  intro y hy h'y
  apply lt_irrefl (infEDist x s)
  calc
    infEDist x s <= edist x y := infEDist_le_edist_of_mem h'y
    _ <= r := by rwa [Metric.mem_closedEBall, edist_comm] at hy
    _ < infEDist x s := h

中文:
定理 disjoint_closedEBall_of_lt_infEDist
  条件: {r : 实数>=0∞} (h : r < infEDist x s)
  证明: by
  rw [disjoint_left]
  intro y hy h'y
  apply lt_irrefl (infEDist x s)
  calc
    infEDist x s <= edist x y := infEDist_le_edist_of_mem h'y
    _ <= r := by rwa [Metric.mem_closedEBall, edist_comm] at hy
    _ < infEDist x s := h

Depends on / 依赖: Metric, Metric.mem_closedEBall, disjoint_left, edist_comm, infEDist, infEDist_le_edist_of_mem, lt_irrefl, mem_closedEBall
-/
theorem disjoint_closedEBall_of_lt_infEDist {r : Real>=0∞} (h : r < infEDist x s) :
    Disjoint (Metric.closedEBall x r) s := by
  rw [disjoint_left]
  intro y hy h'y
  apply lt_irrefl (infEDist x s)
  calc
    infEDist x s <= edist x y := infEDist_le_edist_of_mem h'y
    _ <= r := by rwa [Metric.mem_closedEBall, edist_comm] at hy
    _ < infEDist x s := h

/--
theorem `infEDist_image` / 定理 `infEDist_image`

English:
theorem infEDist_image
  given: (hΦ : Isometry Φ)
  statement: infEDist (Φ x) (Φ '' t) = infEDist x t
  proof: by
  simp only [infEDist, iInf_image, hΦ.edist_eq]

@[to_additive (attr := simp)]

中文:
定理 infEDist_image
  条件: (hΦ : Isometry Φ)
  结论: infEDist (Φ x) (Φ '' t) = infEDist x t
  证明: by
  simp only [infEDist, iInf_image, hΦ.edist_eq]

@[to_additive (attr := simp)]

Depends on / 依赖: edist_eq, iInf_image, infEDist
-/
theorem infEDist_image (hΦ : Isometry Φ) : infEDist (Φ x) (Φ '' t) = infEDist x t := by
  simp only [infEDist, iInf_image, hΦ.edist_eq]

@[to_additive (attr := simp)]
/--
theorem `infEDist_smul` / 定理 `infEDist_smul`

English:
theorem infEDist_smul
  given: {M} [SMul M α] [IsIsometricSMul M α] (c : M) (x : α) (s : Set α)
  proof: infEDist_image (isometry_smul _ _)

中文:
定理 infEDist_smul
  条件: {M} [SMul M α] [IsIsometricSMul M α] (c : M) (x : α) (s : Set α)
  证明: infEDist_image (isometry_smul _ _)

Depends on / 依赖: infEDist_image, isometry_smul
-/
theorem infEDist_smul {M} [SMul M α] [IsIsometricSMul M α] (c : M) (x : α) (s : Set α) :
    infEDist (c • x) (c • s) = infEDist x s :=
  infEDist_image (isometry_smul _ _)

/--
theorem `_root_.IsOpen.exists_iUnion_isClosed` / 定理 `_root_.IsOpen.exists_iUnion_isClosed`

English:
theorem _root_.IsOpen.exists_iUnion_isClosed
  given: {U : Set α} (hU : IsOpen U)
  proof: by
  obtain ⟨a, a_pos, a_lt_one⟩ : exists a : Real>=0∞, 0 < a ∧ a < 1 := exists_between zero_lt_one
  let F := fun n : Nat => (fun x => infEDist x Uᶜ) ⁻¹' Ici (a ^ n)
  have F_subset : forall n, F n subseteq U := fun n x hx => by
    by_contra h
    have : infEDist x Uᶜ != 0 := ((ENNReal.pow_pos a_p

中文:
定理 _root_.IsOpen.exists_iUnion_isClosed
  条件: {U : Set α} (hU : IsOpen U)
  证明: by
  obtain ⟨a, a_pos, a_lt_one⟩ : exists a : Real>=0∞, 0 < a ∧ a < 1 := exists_between zero_lt_one
  let F := fun n : Nat => (fun x => infEDist x Uᶜ) ⁻¹' Ici (a ^ n)
  have F_subset : forall n, F n subseteq U := fun n x hx => by
    by_contra h
    have : infEDist x Uᶜ != 0 := ((ENNReal.pow_pos a_p

Depends on / 依赖: ENNReal, ENNReal.pow_pos, F_subset, IsClosed, IsClosed.preimage, Subset, Subset.antisymm, a_lt_one, a_pos, antisymm, continuous_infEDist, exists_between, iUnion_, infEDist, infEDist_zero_of_mem, isClosed_Ici, pow_pos, preimage, subseteq, trans_le
-/
theorem _root_.IsOpen.exists_iUnion_isClosed {U : Set α} (hU : IsOpen U) :
    exists F : Nat -> Set α, (forall n, IsClosed (F n)) ∧ (forall n, F n subseteq U) ∧ ⋃ n, F n = U ∧ Monotone F := by
  obtain ⟨a, a_pos, a_lt_one⟩ : exists a : Real>=0∞, 0 < a ∧ a < 1 := exists_between zero_lt_one
  let F := fun n : Nat => (fun x => infEDist x Uᶜ) ⁻¹' Ici (a ^ n)
  have F_subset : forall n, F n subseteq U := fun n x hx => by
    by_contra h
    have : infEDist x Uᶜ != 0 := ((ENNReal.pow_pos a_pos _).trans_le hx).ne'
    exact this (infEDist_zero_of_mem h)
  refine ⟨F, fun n => IsClosed.preimage continuous_infEDist isClosed_Ici, F_subset, ?_, ?_⟩
  · show ⋃ n, F n = U
    refine Subset.antisymm (by simp only [iUnion_subset_iff, F_subset, forall_const]) fun x hx => ?_
    have : x ∉ Uᶜ := by simpa using hx
    rw [mem_iff_infEDist_zero_of_closed hU.isClosed_compl] at this
    have B : 0 < infEDist x Uᶜ := by simpa [pos_iff_ne_zero] using this
    have : Filter.Tendsto (fun n => a ^ n) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one a_lt_one
    rcases ((tendsto_order.1 this).2 _ B).exists with ⟨n, hn⟩
    simp only [mem_iUnion]
    exact ⟨n, hn.le⟩
  show Monotone F
  intro m n hmn x hx
  simp only [F, mem_Ici, mem_preimage] at hx ⊢
  apply le_trans (pow_le_pow_right_of_le_one' a_lt_one.le hmn) hx

/--
theorem `_root_.IsCompact.exists_infEDist_eq_edist` / 定理 `_root_.IsCompact.exists_infEDist_eq_edist`

English:
theorem _root_.IsCompact.exists_infEDist_eq_edist
  given: (hs : IsCompact s) (hne : s.Nonempty) (x : α)
  proof: by
  have A : Continuous fun y => edist x y := by fun_prop
  obtain ⟨y, ys, hy⟩ := hs.exists_isMinOn hne A.continuousOn
  exact ⟨y, ys, le_antisymm (infEDist_le_edist_of_mem ys) (by rwa [le_infEDist])⟩

中文:
定理 _root_.IsCompact.exists_infEDist_eq_edist
  条件: (hs : IsCompact s) (hne : s.Nonempty) (x : α)
  证明: by
  have A : Continuous fun y => edist x y := by fun_prop
  obtain ⟨y, ys, hy⟩ := hs.exists_isMinOn hne A.continuousOn
  exact ⟨y, ys, le_antisymm (infEDist_le_edist_of_mem ys) (by rwa [le_infEDist])⟩

Depends on / 依赖: A.continuousOn, Continuous, continuousOn, exists_isMinOn, fun_prop, hs.exists_isMinOn, infEDist_le_edist_of_mem, le_antisymm, le_infEDist
-/
theorem _root_.IsCompact.exists_infEDist_eq_edist (hs : IsCompact s) (hne : s.Nonempty) (x : α) :
    exists y in s, infEDist x s = edist x y := by
  have A : Continuous fun y => edist x y := by fun_prop
  obtain ⟨y, ys, hy⟩ := hs.exists_isMinOn hne A.continuousOn
  exact ⟨y, ys, le_antisymm (infEDist_le_edist_of_mem ys) (by rwa [le_infEDist])⟩

/--
theorem `exists_pos_forall_lt_edist` / 定理 `exists_pos_forall_lt_edist`

English:
theorem exists_pos_forall_lt_edist
  given: (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t)
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · use 1
    simp
  obtain ⟨x, hx, h⟩ := hs.exists_isMinOn hne continuous_infEDist.continuousOn
  have : 0 < infEDist x t :=
    pos_iff_ne_zero.2 fun H => hst.le_bot ⟨hx, (mem_iff_infEDist_zero_of_closed ht).mpr H⟩
  rcases ENNReal.lt_iff_exists_

中文:
定理 exists_pos_forall_lt_edist
  条件: (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t)
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · use 1
    simp
  obtain ⟨x, hx, h⟩ := hs.exists_isMinOn hne continuous_infEDist.continuousOn
  have : 0 < infEDist x t :=
    pos_iff_ne_zero.2 fun H => hst.le_bot ⟨hx, (mem_iff_infEDist_zero_of_closed ht).mpr H⟩
  rcases ENNReal.lt_iff_exists_

Depends on / 依赖: ENNReal, ENNReal.coe_pos.mp, ENNReal.lt_iff_exists_nnreal_btwn, coe_pos, continuousOn, continuous_infEDist, continuous_infEDist.continuousOn, eq_empty_or_nonempty, exists_isMinOn, hr.trans_le, hs.exists_isMinOn, hst.le_bot, infEDist, le_bot, le_infEDist, lt_iff_exists_nnreal_btwn, mem_iff_infEDist_zero_of_closed, pos_iff_ne_zero, s.eq_empty_or_nonempty, trans_le
-/
theorem exists_pos_forall_lt_edist (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) :
    exists r : Real>=0, 0 < r ∧ forall x in s, forall y in t, (r : Real>=0∞) < edist x y := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · use 1
    simp
  obtain ⟨x, hx, h⟩ := hs.exists_isMinOn hne continuous_infEDist.continuousOn
  have : 0 < infEDist x t :=
    pos_iff_ne_zero.2 fun H => hst.le_bot ⟨hx, (mem_iff_infEDist_zero_of_closed ht).mpr H⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 this with ⟨r, h₀, hr⟩
exact ⟨r, ENNReal.coe_pos.mp h₀, fun y hy z hz => hr.trans_le le_infEDist.1 (h hy) z hz⟩

/--
theorem `infEDist_prod` / 定理 `infEDist_prod`

English:
theorem infEDist_prod
  given: (x : α × β) (s : Set α) (t : Set β)
  proof: by
  simp_rw +singlePass [infEDist, Prod.edist_eq, iInf_prod, Set.mem_prod, iInf_and, iInf_sup_eq,
    sup_iInf_eq, iInf_sup_eq, sup_iInf_eq]

中文:
定理 infEDist_prod
  条件: (x : α × β) (s : Set α) (t : Set β)
  证明: by
  simp_rw +singlePass [infEDist, Prod.edist_eq, iInf_prod, Set.mem_prod, iInf_and, iInf_sup_eq,
    sup_iInf_eq, iInf_sup_eq, sup_iInf_eq]

Depends on / 依赖: Prod.edist_eq, Set.mem_prod, edist_eq, iInf_and, iInf_prod, iInf_sup_eq, infEDist, mem_prod, simp_rw, singlePass, sup_iInf_eq
-/
theorem infEDist_prod (x : α × β) (s : Set α) (t : Set β) :
    infEDist x (s ×ˢ t) = max (infEDist x.1 s) (infEDist x.2 t) := by
  simp_rw +singlePass [infEDist, Prod.edist_eq, iInf_prod, Set.mem_prod, iInf_and, iInf_sup_eq,
    sup_iInf_eq, iInf_sup_eq, sup_iInf_eq]

end InfEDist

/-! ### The Hausdorff distance as a function into `ℝ≥0∞`. -/

/-- The Hausdorff edistance between two sets is the smallest `r` such that each set
is contained in the `r`-neighborhood of the other one -/
irreducible_def hausdorffEDist {α : Type u} [PseudoEMetricSpace α] (s t : Set α) : Real>=0∞ :=
  (⨆ x in s, infEDist x t) ⊔ ⨆ y in t, infEDist y s

section HausdorffEDist

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {x y : α} {s t u : Set α} {Φ : α -> β}

/-- The Hausdorff edistance of a set to itself vanishes. -/
@[simp]
/--
theorem `hausdorffEDist_self` / 定理 `hausdorffEDist_self`

English:
theorem hausdorffEDist_self
  statement: hausdorffEDist s s = 0
  proof: by
  simp only [hausdorffEDist_def, sup_idem, ENNReal.iSup_eq_zero]
  exact fun x hx => infEDist_zero_of_mem hx

中文:
定理 hausdorffEDist_self
  结论: hausdorffEDist s s = 0
  证明: by
  simp only [hausdorffEDist_def, sup_idem, ENNReal.iSup_eq_zero]
  exact fun x hx => infEDist_zero_of_mem hx

Depends on / 依赖: ENNReal, ENNReal.iSup_eq_zero, hausdorffEDist_def, iSup_eq_zero, infEDist_zero_of_mem, sup_idem
-/
theorem hausdorffEDist_self : hausdorffEDist s s = 0 := by
  simp only [hausdorffEDist_def, sup_idem, ENNReal.iSup_eq_zero]
  exact fun x hx => infEDist_zero_of_mem hx

/--
theorem `hausdorffEDist_comm` / 定理 `hausdorffEDist_comm`

English:
theorem hausdorffEDist_comm
  statement: hausdorffEDist s t = hausdorffEDist t s
  proof: by
  simp only [hausdorffEDist_def]; apply sup_comm

中文:
定理 hausdorffEDist_comm
  结论: hausdorffEDist s t = hausdorffEDist t s
  证明: by
  simp only [hausdorffEDist_def]; apply sup_comm

Depends on / 依赖: hausdorffEDist_def, sup_comm
-/
theorem hausdorffEDist_comm : hausdorffEDist s t = hausdorffEDist t s := by
  simp only [hausdorffEDist_def]; apply sup_comm

/--
theorem `hausdorffEDist_le_of_infEDist` / 定理 `hausdorffEDist_le_of_infEDist`

English:
theorem hausdorffEDist_le_of_infEDist
  statement: {r : Real>=0∞} (H1 : forall x in s, infEDist x t <= r)
  proof: by
  simp only [hausdorffEDist_def, sup_le_iff, iSup_le_iff]
  exact ⟨H1, H2⟩

中文:
定理 hausdorffEDist_le_of_infEDist
  结论: {r : 实数>=0∞} (H1 : 对任意 x in s, infEDist x t <= r)
  证明: by
  simp only [hausdorffEDist_def, sup_le_iff, iSup_le_iff]
  exact ⟨H1, H2⟩

Depends on / 依赖: hausdorffEDist_def, iSup_le_iff, sup_le_iff
-/
theorem hausdorffEDist_le_of_infEDist {r : Real>=0∞} (H1 : forall x in s, infEDist x t <= r)
    (H2 : forall x in t, infEDist x s <= r) : hausdorffEDist s t <= r := by
  simp only [hausdorffEDist_def, sup_le_iff, iSup_le_iff]
  exact ⟨H1, H2⟩

/--
theorem `hausdorffEDist_le_of_mem_edist` / 定理 `hausdorffEDist_le_of_mem_edist`

English:
theorem hausdorffEDist_le_of_mem_edist
  statement: {r : Real>=0∞} (H1 : forall x in s, exists y in t, edist x y <= r)
  proof: by
  refine hausdorffEDist_le_of_infEDist (fun x xs => ?_) (fun x xt => ?_)
  · rcases H1 x xs with ⟨y, yt, hy⟩
    exact le_trans (infEDist_le_edist_of_mem yt) hy
  · rcases H2 x xt with ⟨y, ys, hy⟩
    exact le_trans (infEDist_le_edist_of_mem ys) hy

中文:
定理 hausdorffEDist_le_of_mem_edist
  结论: {r : 实数>=0∞} (H1 : 对任意 x in s, 存在 y in t, edist x y <= r)
  证明: by
  refine hausdorffEDist_le_of_infEDist (fun x xs => ?_) (fun x xt => ?_)
  · rcases H1 x xs with ⟨y, yt, hy⟩
    exact le_trans (infEDist_le_edist_of_mem yt) hy
  · rcases H2 x xt with ⟨y, ys, hy⟩
    exact le_trans (infEDist_le_edist_of_mem ys) hy

Depends on / 依赖: hausdorffEDist_le_of_infEDist, infEDist_le_edist_of_mem, le_trans
-/
theorem hausdorffEDist_le_of_mem_edist {r : Real>=0∞} (H1 : forall x in s, exists y in t, edist x y <= r)
    (H2 : forall x in t, exists y in s, edist x y <= r) : hausdorffEDist s t <= r := by
  refine hausdorffEDist_le_of_infEDist (fun x xs => ?_) (fun x xt => ?_)
  · rcases H1 x xs with ⟨y, yt, hy⟩
    exact le_trans (infEDist_le_edist_of_mem yt) hy
  · rcases H2 x xt with ⟨y, ys, hy⟩
    exact le_trans (infEDist_le_edist_of_mem ys) hy

/--
theorem `infEDist_le_hausdorffEDist_of_mem` / 定理 `infEDist_le_hausdorffEDist_of_mem`

English:
theorem infEDist_le_hausdorffEDist_of_mem
  given: (h : x in s)
  statement: infEDist x t <= hausdorffEDist s t
  proof: by
  rw [hausdorffEDist_def]
  refine le_trans ?_ le_sup_left
  exact le_iSup₂ (α := Real>=0∞) x h

中文:
定理 infEDist_le_hausdorffEDist_of_mem
  条件: (h : x in s)
  结论: infEDist x t <= hausdorffEDist s t
  证明: by
  rw [hausdorffEDist_def]
  refine le_trans ?_ le_sup_left
  exact le_iSup₂ (α := Real>=0∞) x h

Depends on / 依赖: hausdorffEDist_def, le_sup_left, le_trans
-/
theorem infEDist_le_hausdorffEDist_of_mem (h : x in s) : infEDist x t <= hausdorffEDist s t := by
  rw [hausdorffEDist_def]
  refine le_trans ?_ le_sup_left
  exact le_iSup₂ (α := Real>=0∞) x h

/--
theorem `exists_edist_lt_of_hausdorffEDist_lt` / 定理 `exists_edist_lt_of_hausdorffEDist_lt`

English:
theorem exists_edist_lt_of_hausdorffEDist_lt
  given: {r : Real>=0∞} (h : x in s) (H : hausdorffEDist s t < r)
  proof: infEDist_lt_iff.mp
    calc
      infEDist x t <= hausdorffEDist s t := infEDist_le_hausdorffEDist_of_mem h
      _ < r := H

中文:
定理 exists_edist_lt_of_hausdorffEDist_lt
  条件: {r : 实数>=0∞} (h : x in s) (H : hausdorffEDist s t < r)
  证明: infEDist_lt_iff.mp
    calc
      infEDist x t <= hausdorffEDist s t := infEDist_le_hausdorffEDist_of_mem h
      _ < r := H

Depends on / 依赖: hausdorffEDist, infEDist, infEDist_le_hausdorffEDist_of_mem, infEDist_lt_iff, infEDist_lt_iff.mp
-/
theorem exists_edist_lt_of_hausdorffEDist_lt {r : Real>=0∞} (h : x in s) (H : hausdorffEDist s t < r) :
    exists y in t, edist x y < r :=
infEDist_lt_iff.mp
    calc
      infEDist x t <= hausdorffEDist s t := infEDist_le_hausdorffEDist_of_mem h
      _ < r := H

/--
theorem `infEDist_le_infEDist_add_hausdorffEDist` / 定理 `infEDist_le_infEDist_add_hausdorffEDist`

English:
theorem infEDist_le_infEDist_add_hausdorffEDist
  proof: ENNReal.le_of_forall_pos_le_add fun ε εpos h => by
    have ε0 : (ε / 2 : Real>=0∞) != 0 := by simpa [pos_iff_ne_zero] using εpos
    have : infEDist x s < infEDist x s + ε / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 h).1.ne ε0
    obtain ⟨y : α, ys : y in s, dxy : edist x y < infEDist x

中文:
定理 infEDist_le_infEDist_add_hausdorffEDist
  证明: ENNReal.le_of_forall_pos_le_add fun ε εpos h => by
    have ε0 : (ε / 2 : Real>=0∞) != 0 := by simpa [pos_iff_ne_zero] using εpos
    have : infEDist x s < infEDist x s + ε / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 h).1.ne ε0
    obtain ⟨y : α, ys : y in s, dxy : edist x y < infEDist x

Depends on / 依赖: ENNReal, ENNReal.add_lt_top, ENNReal.le_of_forall_pos_le_add, ENNReal.lt_add_right, add_lt_top, hausdorffEDist, infEDist, infEDist_lt_iff, infEDist_lt_iff.mp, le_of_forall_pos_le_add, lt_add_right, pos_iff_ne_zero
-/
theorem infEDist_le_infEDist_add_hausdorffEDist :
    infEDist x t <= infEDist x s + hausdorffEDist s t :=
  ENNReal.le_of_forall_pos_le_add fun ε εpos h => by
    have ε0 : (ε / 2 : Real>=0∞) != 0 := by simpa [pos_iff_ne_zero] using εpos
    have : infEDist x s < infEDist x s + ε / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 h).1.ne ε0
    obtain ⟨y : α, ys : y in s, dxy : edist x y < infEDist x s + ↑ε / 2⟩ := infEDist_lt_iff.mp this
    have : hausdorffEDist s t < hausdorffEDist s t + ε / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 h).2.ne ε0
    obtain ⟨z : α, zt : z in t, dyz : edist y z < hausdorffEDist s t + ↑ε / 2⟩ :=
      exists_edist_lt_of_hausdorffEDist_lt ys this
    calc
      infEDist x t <= edist x z := infEDist_le_edist_of_mem zt
      _ <= edist x y + edist y z := edist_triangle _ _ _
      _ <= infEDist x s + ε / 2 + (hausdorffEDist s t + ε / 2) := add_le_add dxy.le dyz.le
      _ = infEDist x s + hausdorffEDist s t + ε := by
        rw [add_add_add_comm]; rw [ENNReal.add_halves]

/--
theorem `hausdorffEDist_image` / 定理 `hausdorffEDist_image`

English:
theorem hausdorffEDist_image
  given: (h : Isometry Φ)
  proof: by
  simp only [hausdorffEDist_def, iSup_image, infEDist_image h]

中文:
定理 hausdorffEDist_image
  条件: (h : Isometry Φ)
  证明: by
  simp only [hausdorffEDist_def, iSup_image, infEDist_image h]

Depends on / 依赖: hausdorffEDist_def, iSup_image, infEDist_image
-/
theorem hausdorffEDist_image (h : Isometry Φ) :
    hausdorffEDist (Φ '' s) (Φ '' t) = hausdorffEDist s t := by
  simp only [hausdorffEDist_def, iSup_image, infEDist_image h]

/--
theorem `hausdorffEDist_le_ediam` / 定理 `hausdorffEDist_le_ediam`

English:
theorem hausdorffEDist_le_ediam
  given: (hs : s.Nonempty) (ht : t.Nonempty)
  proof: by
  rcases hs with ⟨x, xs⟩
  rcases ht with ⟨y, yt⟩
  refine hausdorffEDist_le_of_mem_edist ?_ ?_
  · intro z hz
    exact ⟨y, yt, Metric.edist_le_ediam_of_mem (subset_union_left hz) (subset_union_right yt)⟩
  · intro z hz
    exact ⟨x, xs, Metric.edist_le_ediam_of_mem (subset_union_right hz) (subs

中文:
定理 hausdorffEDist_le_ediam
  条件: (hs : s.Nonempty) (ht : t.Nonempty)
  证明: by
  rcases hs with ⟨x, xs⟩
  rcases ht with ⟨y, yt⟩
  refine hausdorffEDist_le_of_mem_edist ?_ ?_
  · intro z hz
    exact ⟨y, yt, Metric.edist_le_ediam_of_mem (subset_union_left hz) (subset_union_right yt)⟩
  · intro z hz
    exact ⟨x, xs, Metric.edist_le_ediam_of_mem (subset_union_right hz) (subs

Depends on / 依赖: Metric, Metric.edist_le_ediam_of_mem, edist_le_ediam_of_mem, hausdorffEDist_le_of_mem_edist, subset_union_left, subset_union_right
-/
theorem hausdorffEDist_le_ediam (hs : s.Nonempty) (ht : t.Nonempty) :
    hausdorffEDist s t <= Metric.ediam (s union t) := by
  rcases hs with ⟨x, xs⟩
  rcases ht with ⟨y, yt⟩
  refine hausdorffEDist_le_of_mem_edist ?_ ?_
  · intro z hz
    exact ⟨y, yt, Metric.edist_le_ediam_of_mem (subset_union_left hz) (subset_union_right yt)⟩
  · intro z hz
    exact ⟨x, xs, Metric.edist_le_ediam_of_mem (subset_union_right hz) (subset_union_left xs)⟩

/--
theorem `hausdorffEDist_triangle` / 定理 `hausdorffEDist_triangle`

English:
theorem hausdorffEDist_triangle
  statement: hausdorffEDist s u <= hausdorffEDist s t + hausdorffEDist t u
  proof: by
  rw [hausdorffEDist_def]
  simp only [sup_le_iff, iSup_le_iff]
  constructor
  · change forall x in s, infEDist x u <= hausdorffEDist s t + hausdorffEDist t u
    exact fun x xs =>
      calc
        infEDist x u <= infEDist x t + hausdorffEDist t u :=
          infEDist_le_infEDist_add_hausdorf

中文:
定理 hausdorffEDist_triangle
  结论: hausdorffEDist s u <= hausdorffEDist s t + hausdorffEDist t u
  证明: by
  rw [hausdorffEDist_def]
  simp only [sup_le_iff, iSup_le_iff]
  constructor
  · change forall x in s, infEDist x u <= hausdorffEDist s t + hausdorffEDist t u
    exact fun x xs =>
      calc
        infEDist x u <= infEDist x t + hausdorffEDist t u :=
          infEDist_le_infEDist_add_hausdorf

Depends on / 依赖: hausdorffEDist, hausdorffEDist_def, iSup_le_iff, infEDist, infEDist_le_hausdorffEDist_of_mem, infEDist_le_infEDist_add_hausdorffEDist, sup_le_iff
-/
theorem hausdorffEDist_triangle : hausdorffEDist s u <= hausdorffEDist s t + hausdorffEDist t u := by
  rw [hausdorffEDist_def]
  simp only [sup_le_iff, iSup_le_iff]
  constructor
  · change forall x in s, infEDist x u <= hausdorffEDist s t + hausdorffEDist t u
    exact fun x xs =>
      calc
        infEDist x u <= infEDist x t + hausdorffEDist t u :=
          infEDist_le_infEDist_add_hausdorffEDist
        _ <= hausdorffEDist s t + hausdorffEDist t u := by grw [infEDist_le_hausdorffEDist_of_mem xs]
  · change forall x in u, infEDist x s <= hausdorffEDist s t + hausdorffEDist t u
    exact fun x xu =>
      calc
        infEDist x s <= infEDist x t + hausdorffEDist t s :=
          infEDist_le_infEDist_add_hausdorffEDist
        _ <= hausdorffEDist u t + hausdorffEDist t s := by grw [infEDist_le_hausdorffEDist_of_mem xu]
        _ = hausdorffEDist s t + hausdorffEDist t u := by simp [hausdorffEDist_comm, add_comm]

/--
theorem `hausdorffEDist_zero_iff_closure_eq_closure` / 定理 `hausdorffEDist_zero_iff_closure_eq_closure`

English:
theorem hausdorffEDist_zero_iff_closure_eq_closure
  proof: by
  simp [hausdorffEDist_def, ← subset_def, ← mem_closure_iff_infEDist_zero,
    subset_antisymm_iff, isClosed_closure.closure_subset_iff]

中文:
定理 hausdorffEDist_zero_iff_closure_eq_closure
  证明: by
  simp [hausdorffEDist_def, ← subset_def, ← mem_closure_iff_infEDist_zero,
    subset_antisymm_iff, isClosed_closure.closure_subset_iff]

Depends on / 依赖: closure_subset_iff, hausdorffEDist_def, isClosed_closure, isClosed_closure.closure_subset_iff, mem_closure_iff_infEDist_zero, subset_antisymm_iff, subset_def
-/
theorem hausdorffEDist_zero_iff_closure_eq_closure :
    hausdorffEDist s t = 0 ↔ closure s = closure t := by
  simp [hausdorffEDist_def, ← subset_def, ← mem_closure_iff_infEDist_zero,
    subset_antisymm_iff, isClosed_closure.closure_subset_iff]

/-- The Hausdorff edistance between a set and its closure vanishes. -/
@[simp]
/--
theorem `hausdorffEDist_self_closure` / 定理 `hausdorffEDist_self_closure`

English:
theorem hausdorffEDist_self_closure
  statement: hausdorffEDist s (closure s) = 0
  proof: by
  rw [hausdorffEDist_zero_iff_closure_eq_closure]; rw [closure_closure]

中文:
定理 hausdorffEDist_self_closure
  结论: hausdorffEDist s (closure s) = 0
  证明: by
  rw [hausdorffEDist_zero_iff_closure_eq_closure]; rw [closure_closure]

Depends on / 依赖: closure_closure, hausdorffEDist_zero_iff_closure_eq_closure
-/
theorem hausdorffEDist_self_closure : hausdorffEDist s (closure s) = 0 := by
  rw [hausdorffEDist_zero_iff_closure_eq_closure]; rw [closure_closure]

/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp]
/--
theorem `hausdorffEDist_closure_left` / 定理 `hausdorffEDist_closure_left`

English:
theorem hausdorffEDist_closure_left
  statement: hausdorffEDist (closure s) t = hausdorffEDist s t
  proof: by
  refine le_antisymm ?_ ?_
  · calc
      _ <= hausdorffEDist (closure s) s + hausdorffEDist s t := hausdorffEDist_triangle
      _ = hausdorffEDist s t := by simp [hausdorffEDist_comm]
  · calc
      _ <= hausdorffEDist s (closure s) + hausdorffEDist (closure s) t := hausdorffEDist_triangle
    

中文:
定理 hausdorffEDist_closure_left
  结论: hausdorffEDist (closure s) t = hausdorffEDist s t
  证明: by
  refine le_antisymm ?_ ?_
  · calc
      _ <= hausdorffEDist (closure s) s + hausdorffEDist s t := hausdorffEDist_triangle
      _ = hausdorffEDist s t := by simp [hausdorffEDist_comm]
  · calc
      _ <= hausdorffEDist s (closure s) + hausdorffEDist (closure s) t := hausdorffEDist_triangle
    

Depends on / 依赖: closure, hausdorffEDist, hausdorffEDist_comm, hausdorffEDist_triangle, le_antisymm
-/
theorem hausdorffEDist_closure_left : hausdorffEDist (closure s) t = hausdorffEDist s t := by
  refine le_antisymm ?_ ?_
  · calc
      _ <= hausdorffEDist (closure s) s + hausdorffEDist s t := hausdorffEDist_triangle
      _ = hausdorffEDist s t := by simp [hausdorffEDist_comm]
  · calc
      _ <= hausdorffEDist s (closure s) + hausdorffEDist (closure s) t := hausdorffEDist_triangle
      _ = hausdorffEDist (closure s) t := by simp

/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp]
/--
theorem `hausdorffEDist_closure_right` / 定理 `hausdorffEDist_closure_right`

English:
theorem hausdorffEDist_closure_right
  statement: hausdorffEDist s (closure t) = hausdorffEDist s t
  proof: by
  simp [@hausdorffEDist_comm _ _ s _]

中文:
定理 hausdorffEDist_closure_right
  结论: hausdorffEDist s (closure t) = hausdorffEDist s t
  证明: by
  simp [@hausdorffEDist_comm _ _ s _]

Depends on / 依赖: hausdorffEDist_comm
-/
theorem hausdorffEDist_closure_right : hausdorffEDist s (closure t) = hausdorffEDist s t := by
  simp [@hausdorffEDist_comm _ _ s _]

/--
theorem `hausdorffEDist_closure` / 定理 `hausdorffEDist_closure`

English:
theorem hausdorffEDist_closure
  statement: hausdorffEDist (closure s) (closure t) = hausdorffEDist s t
  proof: by
  simp

中文:
定理 hausdorffEDist_closure
  结论: hausdorffEDist (closure s) (closure t) = hausdorffEDist s t
  证明: by
  simp
-/
theorem hausdorffEDist_closure : hausdorffEDist (closure s) (closure t) = hausdorffEDist s t := by
  simp

/--
theorem `_root_.IsClosed.hausdorffEDist_zero_iff` / 定理 `_root_.IsClosed.hausdorffEDist_zero_iff`

English:
theorem _root_.IsClosed.hausdorffEDist_zero_iff
  given: (hs : IsClosed s) (ht : IsClosed t)
  proof: by
  rw [hausdorffEDist_zero_iff_closure_eq_closure]; rw [hs.closure_eq]; rw [ht.closure_eq]

中文:
定理 _root_.IsClosed.hausdorffEDist_zero_iff
  条件: (hs : IsClosed s) (ht : IsClosed t)
  证明: by
  rw [hausdorffEDist_zero_iff_closure_eq_closure]; rw [hs.closure_eq]; rw [ht.closure_eq]

Depends on / 依赖: closure_eq, hausdorffEDist_zero_iff_closure_eq_closure, hs.closure_eq, ht.closure_eq
-/
theorem _root_.IsClosed.hausdorffEDist_zero_iff (hs : IsClosed s) (ht : IsClosed t) :
    hausdorffEDist s t = 0 ↔ s = t := by
  rw [hausdorffEDist_zero_iff_closure_eq_closure]; rw [hs.closure_eq]; rw [ht.closure_eq]

/--
theorem `hausdorffEDist_empty` / 定理 `hausdorffEDist_empty`

English:
theorem hausdorffEDist_empty
  given: (ne : s.Nonempty)
  statement: hausdorffEDist s ∅ = ∞
  proof: by
  rcases ne with ⟨x, xs⟩
  have : infEDist x ∅ <= hausdorffEDist s ∅ := infEDist_le_hausdorffEDist_of_mem xs
  simpa using this

中文:
定理 hausdorffEDist_empty
  条件: (ne : s.Nonempty)
  结论: hausdorffEDist s ∅ = ∞
  证明: by
  rcases ne with ⟨x, xs⟩
  have : infEDist x ∅ <= hausdorffEDist s ∅ := infEDist_le_hausdorffEDist_of_mem xs
  simpa using this

Depends on / 依赖: hausdorffEDist, infEDist, infEDist_le_hausdorffEDist_of_mem
-/
theorem hausdorffEDist_empty (ne : s.Nonempty) : hausdorffEDist s ∅ = ∞ := by
  rcases ne with ⟨x, xs⟩
  have : infEDist x ∅ <= hausdorffEDist s ∅ := infEDist_le_hausdorffEDist_of_mem xs
  simpa using this

/--
theorem `nonempty_of_hausdorffEDist_ne_top` / 定理 `nonempty_of_hausdorffEDist_ne_top`

English:
theorem nonempty_of_hausdorffEDist_ne_top
  given: (hs : s.Nonempty) (fin : hausdorffEDist s t != ⊤)
  proof: t.eq_empty_or_nonempty.resolve_left fun ht => fin (ht.symm ▸ hausdorffEDist_empty hs)

中文:
定理 nonempty_of_hausdorffEDist_ne_top
  条件: (hs : s.Nonempty) (fin : hausdorffEDist s t != ⊤)
  证明: t.eq_empty_or_nonempty.resolve_left fun ht => fin (ht.symm ▸ hausdorffEDist_empty hs)

Depends on / 依赖: eq_empty_or_nonempty, hausdorffEDist_empty, ht.symm, resolve_left, t.eq_empty_or_nonempty.resolve_left
-/
theorem nonempty_of_hausdorffEDist_ne_top (hs : s.Nonempty) (fin : hausdorffEDist s t != ⊤) :
    t.Nonempty :=
  t.eq_empty_or_nonempty.resolve_left fun ht => fin (ht.symm ▸ hausdorffEDist_empty hs)

/--
theorem `empty_or_nonempty_of_hausdorffEDist_ne_top` / 定理 `empty_or_nonempty_of_hausdorffEDist_ne_top`

English:
theorem empty_or_nonempty_of_hausdorffEDist_ne_top
  given: (fin : hausdorffEDist s t != ⊤)
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rcases t.eq_empty_or_nonempty with rfl | ht
    · exact Or.inl ⟨rfl, rfl⟩
    · rw [hausdorffEDist_comm] at fin
      exact Or.inr ⟨nonempty_of_hausdorffEDist_ne_top ht fin, ht⟩
  · exact Or.inr ⟨hs, nonempty_of_hausdorffEDist_ne_top hs fin⟩

@[si

中文:
定理 empty_or_nonempty_of_hausdorffEDist_ne_top
  条件: (fin : hausdorffEDist s t != ⊤)
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rcases t.eq_empty_or_nonempty with rfl | ht
    · exact Or.inl ⟨rfl, rfl⟩
    · rw [hausdorffEDist_comm] at fin
      exact Or.inr ⟨nonempty_of_hausdorffEDist_ne_top ht fin, ht⟩
  · exact Or.inr ⟨hs, nonempty_of_hausdorffEDist_ne_top hs fin⟩

@[si

Depends on / 依赖: Or.inl, Or.inr, eq_empty_or_nonempty, hausdorffEDist_comm, nonempty_of_hausdorffEDist_ne_top, s.eq_empty_or_nonempty, t.eq_empty_or_nonempty
-/
theorem empty_or_nonempty_of_hausdorffEDist_ne_top (fin : hausdorffEDist s t != ⊤) :
    (s = ∅ ∧ t = ∅) ∨ (s.Nonempty ∧ t.Nonempty) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rcases t.eq_empty_or_nonempty with rfl | ht
    · exact Or.inl ⟨rfl, rfl⟩
    · rw [hausdorffEDist_comm] at fin
      exact Or.inr ⟨nonempty_of_hausdorffEDist_ne_top ht fin, ht⟩
  · exact Or.inr ⟨hs, nonempty_of_hausdorffEDist_ne_top hs fin⟩

@[simp]
/--
theorem `hausdorffEDist_singleton` / 定理 `hausdorffEDist_singleton`

English:
theorem hausdorffEDist_singleton
  statement: hausdorffEDist {x} {y} = edist x y
  proof: by
  simp_rw [hausdorffEDist, iSup_singleton, infEDist_singleton]
  nth_rw 2 [edist_comm]
  exact max_self _

中文:
定理 hausdorffEDist_singleton
  结论: hausdorffEDist {x} {y} = edist x y
  证明: by
  simp_rw [hausdorffEDist, iSup_singleton, infEDist_singleton]
  nth_rw 2 [edist_comm]
  exact max_self _

Depends on / 依赖: edist_comm, hausdorffEDist, iSup_singleton, infEDist_singleton, max_self, nth_rw, simp_rw
-/
theorem hausdorffEDist_singleton : hausdorffEDist {x} {y} = edist x y := by
  simp_rw [hausdorffEDist, iSup_singleton, infEDist_singleton]
  nth_rw 2 [edist_comm]
  exact max_self _

/--
theorem `hausdorffEDist_iUnion_le` / 定理 `hausdorffEDist_iUnion_le`

English:
theorem hausdorffEDist_iUnion_le
  given: {ι : Sort*} {s t : ι -> Set α}
  proof: by
  simp_rw [hausdorffEDist, max_le_iff, iSup_iUnion, iSup_le_iff, infEDist_iUnion]
constructor <;> refine fun i x hx => (iInf_le _ i).trans le_iSup_of_le i ?_
· exact le_max_of_le_left le_iSup₂_of_le x hx le_rfl
· exact le_max_of_le_right le_iSup₂_of_le x hx le_rfl

中文:
定理 hausdorffEDist_iUnion_le
  条件: {ι : Sort*} {s t : ι -> Set α}
  证明: by
  simp_rw [hausdorffEDist, max_le_iff, iSup_iUnion, iSup_le_iff, infEDist_iUnion]
constructor <;> refine fun i x hx => (iInf_le _ i).trans le_iSup_of_le i ?_
· exact le_max_of_le_left le_iSup₂_of_le x hx le_rfl
· exact le_max_of_le_right le_iSup₂_of_le x hx le_rfl

Depends on / 依赖: hausdorffEDist, iInf_le, iSup_iUnion, iSup_le_iff, infEDist_iUnion, le_iSup_of_le, le_max_of_le_left, le_max_of_le_right, le_rfl, max_le_iff, simp_rw
-/
theorem hausdorffEDist_iUnion_le {ι : Sort*} {s t : ι -> Set α} :
    hausdorffEDist (⋃ i, s i) (⋃ i, t i) <= ⨆ i, hausdorffEDist (s i) (t i) := by
  simp_rw [hausdorffEDist, max_le_iff, iSup_iUnion, iSup_le_iff, infEDist_iUnion]
constructor <;> refine fun i x hx => (iInf_le _ i).trans le_iSup_of_le i ?_
· exact le_max_of_le_left le_iSup₂_of_le x hx le_rfl
· exact le_max_of_le_right le_iSup₂_of_le x hx le_rfl

/--
theorem `hausdorffEDist_union_le` / 定理 `hausdorffEDist_union_le`

English:
theorem hausdorffEDist_union_le
  given: {s₁ s₂ t₁ t₂ : Set α}
  proof: by
  simp_rw [union_eq_iUnion, sup_eq_iSup]
  convert! hausdorffEDist_iUnion_le with (_ | _)

中文:
定理 hausdorffEDist_union_le
  条件: {s₁ s₂ t₁ t₂ : Set α}
  证明: by
  simp_rw [union_eq_iUnion, sup_eq_iSup]
  convert! hausdorffEDist_iUnion_le with (_ | _)

Depends on / 依赖: convert, hausdorffEDist_iUnion_le, simp_rw, sup_eq_iSup, union_eq_iUnion
-/
theorem hausdorffEDist_union_le {s₁ s₂ t₁ t₂ : Set α} :
    hausdorffEDist (s₁ union s₂) (t₁ union t₂) <= max (hausdorffEDist s₁ t₁) (hausdorffEDist s₂ t₂) := by
  simp_rw [union_eq_iUnion, sup_eq_iSup]
  convert! hausdorffEDist_iUnion_le with (_ | _)

/--
theorem `hausdorffEDist_prod_le` / 定理 `hausdorffEDist_prod_le`

English:
theorem hausdorffEDist_prod_le
  given: {s₁ t₁ : Set α} {s₂ t₂ : Set β}
  proof: by
  refine le_of_forall_ge fun _ _ => ?_
  simp_all only [hausdorffEDist, infEDist_prod, max_le_iff, iSup_le_iff, mem_prod, true_and,
    implies_true]

中文:
定理 hausdorffEDist_prod_le
  条件: {s₁ t₁ : Set α} {s₂ t₂ : Set β}
  证明: by
  refine le_of_forall_ge fun _ _ => ?_
  simp_all only [hausdorffEDist, infEDist_prod, max_le_iff, iSup_le_iff, mem_prod, true_and,
    implies_true]

Depends on / 依赖: hausdorffEDist, iSup_le_iff, implies_true, infEDist_prod, le_of_forall_ge, max_le_iff, mem_prod, true_and
-/
theorem hausdorffEDist_prod_le {s₁ t₁ : Set α} {s₂ t₂ : Set β} :
    hausdorffEDist (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) <= max (hausdorffEDist s₁ t₁) (hausdorffEDist s₂ t₂) := by
  refine le_of_forall_ge fun _ _ => ?_
  simp_all only [hausdorffEDist, infEDist_prod, max_le_iff, iSup_le_iff, mem_prod, true_and,
    implies_true]

end HausdorffEDist -- section

end Metric -- namespace

namespace EMetric

open Metric

@[deprecated (since := "2026-01-08")]
noncomputable alias infEdist := infEDist

@[deprecated (since := "2026-01-08")]
alias infEdist_empty := infEDist_empty

@[deprecated (since := "2026-01-08")] alias le_infEdist := le_infEDist
@[deprecated (since := "2026-01-08")] alias infEdist_union := infEDist_union
@[deprecated (since := "2026-01-08")] alias infEdist_iUnion := infEDist_iUnion
@[deprecated (since := "2026-01-08")] alias infEdist_biUnion := infEDist_biUnion
@[deprecated (since := "2026-01-08")] alias infEdist_singleton := infEDist_singleton
@[deprecated (since := "2026-01-08")] alias infEdist_le_edist_of_mem := infEDist_le_edist_of_mem
@[deprecated (since := "2026-01-08")] alias infEdist_zero_of_mem := infEDist_zero_of_mem
@[deprecated (since := "2026-01-08")] alias infEdist_anti := infEDist_anti
@[deprecated (since := "2026-01-08")] alias infEdist_lt_iff := infEDist_lt_iff

@[deprecated (since := "2026-01-08")]
alias infEdist_le_infEdist_add_edist := infEDist_le_infEDist_add_edist

@[deprecated (since := "2026-01-08")]
alias infEdist_le_edist_add_infEdist := infEDist_le_edist_add_infEDist

@[deprecated (since := "2026-01-08")]
alias edist_le_infEdist_add_ediam := edist_le_infEDist_add_ediam

@[deprecated (since := "2026-01-08")] alias continuous_infEdist := continuous_infEDist
@[deprecated (since := "2026-01-08")] alias infEdist_closure := infEDist_closure

@[deprecated (since := "2026-01-08")]
alias mem_closure_iff_infEdist_zero := mem_closure_iff_infEDist_zero

@[deprecated (since := "2026-01-08")]
alias mem_iff_infEdist_zero_of_closed := mem_iff_infEDist_zero_of_closed

@[deprecated (since := "2026-01-08")]
alias infEdist_pos_iff_notMem_closure := infEDist_pos_iff_notMem_closure

@[deprecated (since := "2026-01-08")]
alias infEdist_closure_pos_iff_notMem_closure := infEDist_closure_pos_iff_notMem_closure

@[deprecated (since := "2026-01-08")]
alias exists_real_pos_lt_infEdist_of_notMem_closure := exists_real_pos_lt_infEDist_of_notMem_closure

@[deprecated (since := "2026-01-08")]
alias disjoint_closedBall_of_lt_infEdist := disjoint_closedEBall_of_lt_infEDist

@[deprecated (since := "2026-01-08")] alias infEdist_image := infEDist_image
@[deprecated (since := "2026-01-08")] alias infEdist_vadd := infEDist_vadd
@[to_additive existing, deprecated (since := "2026-01-08")] alias infEdist_smul := infEDist_smul

@[deprecated (since := "2026-01-08")]
alias _root_.IsCompact.exists_infEdist_eq_edist := _root_.IsCompact.exists_infEDist_eq_edist

@[deprecated (since := "2026-01-08")] alias exists_pos_forall_lt_edist := exists_pos_forall_lt_edist
@[deprecated (since := "2026-01-08")] alias infEdist_prod := infEDist_prod

@[deprecated (since := "2026-01-08")] noncomputable alias hausdorffEdist := hausdorffEDist
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_def := hausdorffEDist_def
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_self := hausdorffEDist_self
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_comm := hausdorffEDist_comm

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_le_of_infEdist := hausdorffEDist_le_of_infEDist

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_le_of_mem_edist := hausdorffEDist_le_of_mem_edist

@[deprecated (since := "2026-01-08")]
alias infEdist_le_hausdorffEdist_of_mem := infEDist_le_hausdorffEDist_of_mem

@[deprecated (since := "2026-01-08")]
alias exists_edist_lt_of_hausdorffEdist_lt := exists_edist_lt_of_hausdorffEDist_lt

@[deprecated (since := "2026-01-08")]
alias infEdist_le_infEdist_add_hausdorffEdist := infEDist_le_infEDist_add_hausdorffEDist

@[deprecated (since := "2026-01-08")] alias hausdorffEdist_image := hausdorffEDist_image
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_le_ediam := hausdorffEDist_le_ediam
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_triangle := hausdorffEDist_triangle

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_zero_iff_closure_eq_closure := hausdorffEDist_zero_iff_closure_eq_closure

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_self_closure := hausdorffEDist_self_closure

@[deprecated (since := "2026-01-08")] alias hausdorffEdist_closure₁ := hausdorffEDist_closure_left
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_closure₂ := hausdorffEDist_closure_right
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_closure := hausdorffEDist_closure

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_zero_iff_eq_of_closed := IsClosed.hausdorffEDist_zero_iff

@[deprecated (since := "2026-01-08")] alias hausdorffEdist_empty := hausdorffEDist_empty

@[deprecated (since := "2026-01-08")]
alias nonempty_of_hausdorffEdist_ne_top := nonempty_of_hausdorffEDist_ne_top

@[deprecated (since := "2026-01-08")]
alias empty_or_nonempty_of_hausdorffEdist_ne_top := empty_or_nonempty_of_hausdorffEDist_ne_top

@[deprecated (since := "2026-01-08")] alias hausdorffEdist_singleton := hausdorffEDist_singleton
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_iUnion_le := hausdorffEDist_iUnion_le
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_union_le := hausdorffEDist_union_le
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_prod_le := hausdorffEDist_prod_le

end EMetric

/-! Now, we turn to the same notions in metric spaces. To avoid the difficulties related to
`sInf` and `sSup` on `ℝ` (which is only conditionally complete), we use the notions in `ℝ≥0∞`
formulated in terms of the edistance, and coerce them to `ℝ`.
Then their properties follow readily from the corresponding properties in `ℝ≥0∞`,
modulo some tedious rewriting of inequalities from one to the other. -/

namespace Metric

section

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {s t u : Set α} {x y : α} {Φ : α -> β}

/-! ### Distance of a point to a set as a function into `ℝ`. -/

/--
Definition of `infDist` / `infDist` 的定义

English:
definition infDist
  signature: (x : α) (s : Set α)
  body: ENNReal.toReal (infEDist x s)

中文:
定义 infDist
  签名: (x : α) (s : Set α)
  定义体: ENNReal.toReal (infEDist x s)

Depends on / 依赖: ENNReal, ENNReal.toReal, infEDist, toReal
-/
def infDist (x : α) (s : Set α) : Real :=
  ENNReal.toReal (infEDist x s)

/--
theorem `infDist_eq_iInf` / 定理 `infDist_eq_iInf`

English:
theorem infDist_eq_iInf
  statement: infDist x s = ⨅ y : s, dist x y
  proof: by
  rw [infDist]; rw [infEDist]; rw [iInf_subtype']; rw [ENNReal.toReal_iInf]
  · simp only [dist_edist]
  · finiteness

中文:
定理 infDist_eq_iInf
  结论: infDist x s = ⨅ y : s, dist x y
  证明: by
  rw [infDist]; rw [infEDist]; rw [iInf_subtype']; rw [ENNReal.toReal_iInf]
  · simp only [dist_edist]
  · finiteness

Depends on / 依赖: ENNReal, ENNReal.toReal_iInf, dist_edist, finiteness, iInf_subtype, infDist, infEDist, toReal_iInf
-/
theorem infDist_eq_iInf : infDist x s = ⨅ y : s, dist x y := by
  rw [infDist]; rw [infEDist]; rw [iInf_subtype']; rw [ENNReal.toReal_iInf]
  · simp only [dist_edist]
  · finiteness

/--
theorem `infDist_nonneg` / 定理 `infDist_nonneg`

English:
theorem infDist_nonneg
  statement: 0 <= infDist x s
  proof: toReal_nonneg

中文:
定理 infDist_nonneg
  结论: 0 <= infDist x s
  证明: toReal_nonneg

Depends on / 依赖: toReal_nonneg
-/
theorem infDist_nonneg : 0 <= infDist x s := toReal_nonneg

/-- The minimal distance to the empty set is 0 (if you want to have the more reasonable
value `∞` instead, use `Metric.infEDist`, which takes values in `ℝ≥0∞`) -/
@[simp]
/--
theorem `infDist_empty` / 定理 `infDist_empty`

English:
theorem infDist_empty
  statement: infDist x ∅ = 0
  proof: by simp [infDist]

中文:
定理 infDist_empty
  结论: infDist x ∅ = 0
  证明: by simp [infDist]

Depends on / 依赖: infDist
-/
theorem infDist_empty : infDist x ∅ = 0 := by simp [infDist]

/--
lemma `isGLB_infDist` / 引理 `isGLB_infDist`

English:
lemma isGLB_infDist
  given: (hs : s.Nonempty)
  statement: IsGLB ((dist x ·) '' s) (infDist x s)
  proof: by
  simpa [infDist_eq_iInf, sInf_image']
    using isGLB_csInf (hs.image _) ⟨0, by simp [lowerBounds]⟩

中文:
引理 isGLB_infDist
  条件: (hs : s.Nonempty)
  结论: IsGLB ((dist x ·) '' s) (infDist x s)
  证明: by
  simpa [infDist_eq_iInf, sInf_image']
    using isGLB_csInf (hs.image _) ⟨0, by simp [lowerBounds]⟩

Depends on / 依赖: hs.image, infDist_eq_iInf, isGLB_csInf, lowerBounds, sInf_image
-/
lemma isGLB_infDist (hs : s.Nonempty) : IsGLB ((dist x ·) '' s) (infDist x s) := by
  simpa [infDist_eq_iInf, sInf_image']
    using isGLB_csInf (hs.image _) ⟨0, by simp [lowerBounds]⟩

/--
theorem `infEDist_ne_top` / 定理 `infEDist_ne_top`

English:
theorem infEDist_ne_top
  given: (h : s.Nonempty)
  statement: infEDist x s != ∞
  proof: by
  rcases h with ⟨y, hy⟩
  exact ne_top_of_le_ne_top (edist_ne_top _ _) (infEDist_le_edist_of_mem hy)

@[deprecated (since := "2026-01-08")]
alias infEdist_ne_top := infEDist_ne_top

@[simp]

中文:
定理 infEDist_ne_top
  条件: (h : s.Nonempty)
  结论: infEDist x s != ∞
  证明: by
  rcases h with ⟨y, hy⟩
  exact ne_top_of_le_ne_top (edist_ne_top _ _) (infEDist_le_edist_of_mem hy)

@[deprecated (since := "2026-01-08")]
alias infEdist_ne_top := infEDist_ne_top

@[simp]

Depends on / 依赖: edist_ne_top, infEDist_le_edist_of_mem, ne_top_of_le_ne_top
-/
theorem infEDist_ne_top (h : s.Nonempty) : infEDist x s != ∞ := by
  rcases h with ⟨y, hy⟩
  exact ne_top_of_le_ne_top (edist_ne_top _ _) (infEDist_le_edist_of_mem hy)

@[deprecated (since := "2026-01-08")]
alias infEdist_ne_top := infEDist_ne_top

@[simp]
/--
theorem `infEDist_eq_top_iff` / 定理 `infEDist_eq_top_iff`

English:
theorem infEDist_eq_top_iff
  statement: infEDist x s = ∞ ↔ s = ∅
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hs <;> simp [*, Nonempty.ne_empty, infEDist_ne_top]

@[deprecated (since := "2026-01-08")]
alias infEdist_eq_top_iff := infEDist_eq_top_iff

中文:
定理 infEDist_eq_top_iff
  结论: infEDist x s = ∞ ↔ s = ∅
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hs <;> simp [*, Nonempty.ne_empty, infEDist_ne_top]

@[deprecated (since := "2026-01-08")]
alias infEdist_eq_top_iff := infEDist_eq_top_iff

Depends on / 依赖: Nonempty, Nonempty.ne_empty, eq_empty_or_nonempty, infEDist_ne_top, ne_empty, s.eq_empty_or_nonempty
-/
theorem infEDist_eq_top_iff : infEDist x s = ∞ ↔ s = ∅ := by
  rcases s.eq_empty_or_nonempty with rfl | hs <;> simp [*, Nonempty.ne_empty, infEDist_ne_top]

@[deprecated (since := "2026-01-08")]
alias infEdist_eq_top_iff := infEDist_eq_top_iff

/--
theorem `infDist_zero_of_mem` / 定理 `infDist_zero_of_mem`

English:
theorem infDist_zero_of_mem
  given: (h : x in s)
  statement: infDist x s = 0
  proof: by
  simp [infEDist_zero_of_mem h, infDist]

中文:
定理 infDist_zero_of_mem
  条件: (h : x in s)
  结论: infDist x s = 0
  证明: by
  simp [infEDist_zero_of_mem h, infDist]

Depends on / 依赖: infDist, infEDist_zero_of_mem
-/
theorem infDist_zero_of_mem (h : x in s) : infDist x s = 0 := by
  simp [infEDist_zero_of_mem h, infDist]

/-- The minimal distance to a singleton is the distance to the unique point in this singleton. -/
@[simp]
/--
theorem `infDist_singleton` / 定理 `infDist_singleton`

English:
theorem infDist_singleton
  statement: infDist x {y} = dist x y
  proof: by simp [infDist, dist_edist]

中文:
定理 infDist_singleton
  结论: infDist x {y} = dist x y
  证明: by simp [infDist, dist_edist]

Depends on / 依赖: dist_edist, infDist
-/
theorem infDist_singleton : infDist x {y} = dist x y := by simp [infDist, dist_edist]

/--
theorem `infDist_le_dist_of_mem` / 定理 `infDist_le_dist_of_mem`

English:
theorem infDist_le_dist_of_mem
  given: (h : y in s)
  statement: infDist x s <= dist x y
  proof: by
  rw [dist_edist]; rw [infDist]
  exact ENNReal.toReal_mono (edist_ne_top _ _) (infEDist_le_edist_of_mem h)

中文:
定理 infDist_le_dist_of_mem
  条件: (h : y in s)
  结论: infDist x s <= dist x y
  证明: by
  rw [dist_edist]; rw [infDist]
  exact ENNReal.toReal_mono (edist_ne_top _ _) (infEDist_le_edist_of_mem h)

Depends on / 依赖: ENNReal, ENNReal.toReal_mono, dist_edist, edist_ne_top, infDist, infEDist_le_edist_of_mem, toReal_mono
-/
theorem infDist_le_dist_of_mem (h : y in s) : infDist x s <= dist x y := by
  rw [dist_edist]; rw [infDist]
  exact ENNReal.toReal_mono (edist_ne_top _ _) (infEDist_le_edist_of_mem h)

/--
theorem `infDist_le_infDist_of_subset` / 定理 `infDist_le_infDist_of_subset`

English:
theorem infDist_le_infDist_of_subset
  given: (h : s subseteq t) (hs : s.Nonempty)
  statement: infDist x t <= infDist x s
  proof: ENNReal.toReal_mono (infEDist_ne_top hs) (infEDist_anti h)

中文:
定理 infDist_le_infDist_of_subset
  条件: (h : s subseteq t) (hs : s.Nonempty)
  结论: infDist x t <= infDist x s
  证明: ENNReal.toReal_mono (infEDist_ne_top hs) (infEDist_anti h)

Depends on / 依赖: ENNReal, ENNReal.toReal_mono, infEDist_anti, infEDist_ne_top, toReal_mono
-/
theorem infDist_le_infDist_of_subset (h : s subseteq t) (hs : s.Nonempty) : infDist x t <= infDist x s :=
  ENNReal.toReal_mono (infEDist_ne_top hs) (infEDist_anti h)

/--
lemma `le_infDist` / 引理 `le_infDist`

English:
lemma le_infDist
  given: {r : Real} (hs : s.Nonempty)
  statement: r <= infDist x s ↔ forall ⦃y⦄, y in s -> r <= dist x y
  proof: by
  simp_rw [infDist, ← ENNReal.ofReal_le_iff_le_toReal (infEDist_ne_top hs), le_infEDist,
    ENNReal.ofReal_le_iff_le_toReal (edist_ne_top _ _), ← dist_edist]

中文:
引理 le_infDist
  条件: {r : 实数} (hs : s.Nonempty)
  结论: r <= infDist x s ↔ 对任意 ⦃y⦄, y in s -> r <= dist x y
  证明: by
  simp_rw [infDist, ← ENNReal.ofReal_le_iff_le_toReal (infEDist_ne_top hs), le_infEDist,
    ENNReal.ofReal_le_iff_le_toReal (edist_ne_top _ _), ← dist_edist]

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_iff_le_toReal, dist_edist, edist_ne_top, infDist, infEDist_ne_top, le_infEDist, ofReal_le_iff_le_toReal, simp_rw
-/
lemma le_infDist {r : Real} (hs : s.Nonempty) : r <= infDist x s ↔ forall ⦃y⦄, y in s -> r <= dist x y := by
  simp_rw [infDist, ← ENNReal.ofReal_le_iff_le_toReal (infEDist_ne_top hs), le_infEDist,
    ENNReal.ofReal_le_iff_le_toReal (edist_ne_top _ _), ← dist_edist]

/--
theorem `infDist_lt_iff` / 定理 `infDist_lt_iff`

English:
theorem infDist_lt_iff
  given: {r : Real} (hs : s.Nonempty)
  statement: infDist x s < r ↔ exists y in s, dist x y < r
  proof: by
  simp [← not_le, le_infDist hs]

中文:
定理 infDist_lt_iff
  条件: {r : 实数} (hs : s.Nonempty)
  结论: infDist x s < r ↔ 存在 y in s, dist x y < r
  证明: by
  simp [← not_le, le_infDist hs]

Depends on / 依赖: le_infDist, not_le
-/
theorem infDist_lt_iff {r : Real} (hs : s.Nonempty) : infDist x s < r ↔ exists y in s, dist x y < r := by
  simp [← not_le, le_infDist hs]

/--
theorem `infDist_le_infDist_add_dist` / 定理 `infDist_le_infDist_add_dist`

English:
theorem infDist_le_infDist_add_dist
  statement: infDist x s <= infDist y s + dist x y
  proof: by
  rw [infDist]; rw [infDist]; rw [dist_edist]
  refine ENNReal.toReal_le_add' infEDist_le_infEDist_add_edist ?_ (flip absurd (edist_ne_top _ _))
  simp only [infEDist_eq_top_iff, imp_self]

中文:
定理 infDist_le_infDist_add_dist
  结论: infDist x s <= infDist y s + dist x y
  证明: by
  rw [infDist]; rw [infDist]; rw [dist_edist]
  refine ENNReal.toReal_le_add' infEDist_le_infEDist_add_edist ?_ (flip absurd (edist_ne_top _ _))
  simp only [infEDist_eq_top_iff, imp_self]

Depends on / 依赖: ENNReal, ENNReal.toReal_le_add, absurd, dist_edist, edist_ne_top, imp_self, infDist, infEDist_eq_top_iff, infEDist_le_infEDist_add_edist, toReal_le_add
-/
theorem infDist_le_infDist_add_dist : infDist x s <= infDist y s + dist x y := by
  rw [infDist]; rw [infDist]; rw [dist_edist]
  refine ENNReal.toReal_le_add' infEDist_le_infEDist_add_edist ?_ (flip absurd (edist_ne_top _ _))
  simp only [infEDist_eq_top_iff, imp_self]

/--
theorem `notMem_of_dist_lt_infDist` / 定理 `notMem_of_dist_lt_infDist`

English:
theorem notMem_of_dist_lt_infDist
  given: (h : dist x y < infDist x s)
  statement: y ∉ s
  proof: fun hy =>
h.not_ge infDist_le_dist_of_mem hy

中文:
定理 notMem_of_dist_lt_infDist
  条件: (h : dist x y < infDist x s)
  结论: y ∉ s
  证明: fun hy =>
h.not_ge infDist_le_dist_of_mem hy
-/
theorem notMem_of_dist_lt_infDist (h : dist x y < infDist x s) : y ∉ s := fun hy =>
h.not_ge infDist_le_dist_of_mem hy

/--
theorem `disjoint_ball_infDist` / 定理 `disjoint_ball_infDist`

English:
theorem disjoint_ball_infDist
  statement: Disjoint (ball x (infDist x s)) s
  proof: disjoint_left.2 fun _y hy => notMem_of_dist_lt_infDist mem_ball'.1 hy

中文:
定理 disjoint_ball_infDist
  结论: Disjoint (ball x (infDist x s)) s
  证明: disjoint_left.2 fun _y hy => notMem_of_dist_lt_infDist mem_ball'.1 hy

Depends on / 依赖: disjoint_left, mem_ball, notMem_of_dist_lt_infDist
-/
theorem disjoint_ball_infDist : Disjoint (ball x (infDist x s)) s :=
disjoint_left.2 fun _y hy => notMem_of_dist_lt_infDist mem_ball'.1 hy

/--
theorem `ball_infDist_subset_compl` / 定理 `ball_infDist_subset_compl`

English:
theorem ball_infDist_subset_compl
  statement: ball x (infDist x s) subseteq sᶜ
  proof: (disjoint_ball_infDist (s := s)).subset_compl_right

中文:
定理 ball_infDist_subset_compl
  结论: ball x (infDist x s) subseteq sᶜ
  证明: (disjoint_ball_infDist (s := s)).subset_compl_right

Depends on / 依赖: disjoint_ball_infDist, subset_compl_right
-/
theorem ball_infDist_subset_compl : ball x (infDist x s) subseteq sᶜ :=
  (disjoint_ball_infDist (s := s)).subset_compl_right

/--
theorem `ball_infDist_compl_subset` / 定理 `ball_infDist_compl_subset`

English:
theorem ball_infDist_compl_subset
  statement: ball x (infDist x sᶜ) subseteq s
  proof: ball_infDist_subset_compl.trans_eq (compl_compl s)

中文:
定理 ball_infDist_compl_subset
  结论: ball x (infDist x sᶜ) subseteq s
  证明: ball_infDist_subset_compl.trans_eq (compl_compl s)

Depends on / 依赖: ball_infDist_subset_compl, ball_infDist_subset_compl.trans_eq, compl_compl, trans_eq
-/
theorem ball_infDist_compl_subset : ball x (infDist x sᶜ) subseteq s :=
  ball_infDist_subset_compl.trans_eq (compl_compl s)

/--
theorem `disjoint_closedBall_of_lt_infDist` / 定理 `disjoint_closedBall_of_lt_infDist`

English:
theorem disjoint_closedBall_of_lt_infDist
  given: {r : Real} (h : r < infDist x s)
  proof: disjoint_ball_infDist.mono_left closedBall_subset_ball h

中文:
定理 disjoint_closedBall_of_lt_infDist
  条件: {r : 实数} (h : r < infDist x s)
  证明: disjoint_ball_infDist.mono_left closedBall_subset_ball h

Depends on / 依赖: closedBall_subset_ball, disjoint_ball_infDist, disjoint_ball_infDist.mono_left, mono_left
-/
theorem disjoint_closedBall_of_lt_infDist {r : Real} (h : r < infDist x s) :
    Disjoint (closedBall x r) s :=
disjoint_ball_infDist.mono_left closedBall_subset_ball h

/--
theorem `dist_le_infDist_add_diam` / 定理 `dist_le_infDist_add_diam`

English:
theorem dist_le_infDist_add_diam
  given: (hs : IsBounded s) (hy : y in s)
  proof: by
  rw [infDist]; rw [diam]; rw [dist_edist]
  exact toReal_le_add (edist_le_infEDist_add_ediam hy) (infEDist_ne_top ⟨y, hy⟩) hs.ediam_ne_top

中文:
定理 dist_le_infDist_add_diam
  条件: (hs : IsBounded s) (hy : y in s)
  证明: by
  rw [infDist]; rw [diam]; rw [dist_edist]
  exact toReal_le_add (edist_le_infEDist_add_ediam hy) (infEDist_ne_top ⟨y, hy⟩) hs.ediam_ne_top

Depends on / 依赖: dist_edist, ediam_ne_top, edist_le_infEDist_add_ediam, hs.ediam_ne_top, infDist, infEDist_ne_top, toReal_le_add
-/
theorem dist_le_infDist_add_diam (hs : IsBounded s) (hy : y in s) :
    dist x y <= infDist x s + diam s := by
  rw [infDist]; rw [diam]; rw [dist_edist]
  exact toReal_le_add (edist_le_infEDist_add_ediam hy) (infEDist_ne_top ⟨y, hy⟩) hs.ediam_ne_top

variable (s)

/--
theorem `lipschitz_infDist_pt` / 定理 `lipschitz_infDist_pt`

English:
theorem lipschitz_infDist_pt
  statement: LipschitzWith 1 (infDist · s)
  proof: LipschitzWith.of_le_add fun _ _ => infDist_le_infDist_add_dist

中文:
定理 lipschitz_infDist_pt
  结论: LipschitzWith 1 (infDist · s)
  证明: LipschitzWith.of_le_add fun _ _ => infDist_le_infDist_add_dist

Depends on / 依赖: LipschitzWith, LipschitzWith.of_le_add, infDist_le_infDist_add_dist, of_le_add
-/
theorem lipschitz_infDist_pt : LipschitzWith 1 (infDist · s) :=
  LipschitzWith.of_le_add fun _ _ => infDist_le_infDist_add_dist

/--
theorem `uniformContinuous_infDist_pt` / 定理 `uniformContinuous_infDist_pt`

English:
theorem uniformContinuous_infDist_pt
  statement: UniformContinuous (infDist · s)
  proof: (lipschitz_infDist_pt s).uniformContinuous

中文:
定理 uniformContinuous_infDist_pt
  结论: UniformContinuous (infDist · s)
  证明: (lipschitz_infDist_pt s).uniformContinuous

Depends on / 依赖: lipschitz_infDist_pt, uniformContinuous
-/
theorem uniformContinuous_infDist_pt : UniformContinuous (infDist · s) :=
  (lipschitz_infDist_pt s).uniformContinuous

/-- The minimal distance to a set is continuous in point -/
@[continuity, fun_prop]
/--
theorem `continuous_infDist_pt` / 定理 `continuous_infDist_pt`

English:
theorem continuous_infDist_pt
  statement: Continuous (infDist · s)
  proof: (uniformContinuous_infDist_pt s).continuous

中文:
定理 continuous_infDist_pt
  结论: Continuous (infDist · s)
  证明: (uniformContinuous_infDist_pt s).continuous

Depends on / 依赖: continuous, uniformContinuous_infDist_pt
-/
theorem continuous_infDist_pt : Continuous (infDist · s) :=
  (uniformContinuous_infDist_pt s).continuous

variable {s}

/--
theorem `infDist_closure` / 定理 `infDist_closure`

English:
theorem infDist_closure
  statement: infDist x (closure s) = infDist x s
  proof: by
  simp [infDist, infEDist_closure]

中文:
定理 infDist_closure
  结论: infDist x (closure s) = infDist x s
  证明: by
  simp [infDist, infEDist_closure]

Depends on / 依赖: infDist, infEDist_closure
-/
theorem infDist_closure : infDist x (closure s) = infDist x s := by
  simp [infDist, infEDist_closure]

/--
theorem `infDist_zero_of_mem_closure` / 定理 `infDist_zero_of_mem_closure`

English:
theorem infDist_zero_of_mem_closure
  given: (hx : x in closure s)
  statement: infDist x s = 0
  proof: by
  rw [← infDist_closure]
  exact infDist_zero_of_mem hx

中文:
定理 infDist_zero_of_mem_closure
  条件: (hx : x in closure s)
  结论: infDist x s = 0
  证明: by
  rw [← infDist_closure]
  exact infDist_zero_of_mem hx

Depends on / 依赖: infDist_closure, infDist_zero_of_mem
-/
theorem infDist_zero_of_mem_closure (hx : x in closure s) : infDist x s = 0 := by
  rw [← infDist_closure]
  exact infDist_zero_of_mem hx

/--
theorem `mem_closure_iff_infDist_zero` / 定理 `mem_closure_iff_infDist_zero`

English:
theorem mem_closure_iff_infDist_zero
  given: (h : s.Nonempty)
  statement: x in closure s ↔ infDist x s = 0
  proof: by
  simp [mem_closure_iff_infEDist_zero, infDist, ENNReal.toReal_eq_zero_iff, infEDist_ne_top h]

中文:
定理 mem_closure_iff_infDist_zero
  条件: (h : s.Nonempty)
  结论: x in closure s ↔ infDist x s = 0
  证明: by
  simp [mem_closure_iff_infEDist_zero, infDist, ENNReal.toReal_eq_zero_iff, infEDist_ne_top h]

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_zero_iff, infDist, infEDist_ne_top, mem_closure_iff_infEDist_zero, toReal_eq_zero_iff
-/
theorem mem_closure_iff_infDist_zero (h : s.Nonempty) : x in closure s ↔ infDist x s = 0 := by
  simp [mem_closure_iff_infEDist_zero, infDist, ENNReal.toReal_eq_zero_iff, infEDist_ne_top h]

/--
theorem `infDist_pos_iff_notMem_closure` / 定理 `infDist_pos_iff_notMem_closure`

English:
theorem infDist_pos_iff_notMem_closure
  given: (hs : s.Nonempty)
  proof: (mem_closure_iff_infDist_zero hs).not.trans infDist_nonneg.lt_iff_ne'.symm

中文:
定理 infDist_pos_iff_notMem_closure
  条件: (hs : s.Nonempty)
  证明: (mem_closure_iff_infDist_zero hs).not.trans infDist_nonneg.lt_iff_ne'.symm

Depends on / 依赖: infDist_nonneg, infDist_nonneg.lt_iff_ne, lt_iff_ne, mem_closure_iff_infDist_zero, not.trans
-/
theorem infDist_pos_iff_notMem_closure (hs : s.Nonempty) :
    x ∉ closure s ↔ 0 < infDist x s :=
  (mem_closure_iff_infDist_zero hs).not.trans infDist_nonneg.lt_iff_ne'.symm

/--
theorem `_root_.IsClosed.mem_iff_infDist_zero` / 定理 `_root_.IsClosed.mem_iff_infDist_zero`

English:
theorem _root_.IsClosed.mem_iff_infDist_zero
  given: (h : IsClosed s) (hs : s.Nonempty)
  proof: by rw [← mem_closure_iff_infDist_zero hs, h.closure_eq]

中文:
定理 _root_.IsClosed.mem_iff_infDist_zero
  条件: (h : IsClosed s) (hs : s.Nonempty)
  证明: by rw [← mem_closure_iff_infDist_zero hs, h.closure_eq]

Depends on / 依赖: closure_eq, h.closure_eq, mem_closure_iff_infDist_zero
-/
theorem _root_.IsClosed.mem_iff_infDist_zero (h : IsClosed s) (hs : s.Nonempty) :
    x in s ↔ infDist x s = 0 := by rw [← mem_closure_iff_infDist_zero hs, h.closure_eq]

/--
theorem `_root_.IsClosed.notMem_iff_infDist_pos` / 定理 `_root_.IsClosed.notMem_iff_infDist_pos`

English:
theorem _root_.IsClosed.notMem_iff_infDist_pos
  given: (h : IsClosed s) (hs : s.Nonempty)
  proof: by
  simp [h.mem_iff_infDist_zero hs, infDist_nonneg.lt_iff_ne']

中文:
定理 _root_.IsClosed.notMem_iff_infDist_pos
  条件: (h : IsClosed s) (hs : s.Nonempty)
  证明: by
  simp [h.mem_iff_infDist_zero hs, infDist_nonneg.lt_iff_ne']

Depends on / 依赖: h.mem_iff_infDist_zero, infDist_nonneg, infDist_nonneg.lt_iff_ne, lt_iff_ne, mem_iff_infDist_zero
-/
theorem _root_.IsClosed.notMem_iff_infDist_pos (h : IsClosed s) (hs : s.Nonempty) :
    x ∉ s ↔ 0 < infDist x s := by
  simp [h.mem_iff_infDist_zero hs, infDist_nonneg.lt_iff_ne']

/--
theorem `continuousAt_inv_infDist_pt` / 定理 `continuousAt_inv_infDist_pt`

English:
theorem continuousAt_inv_infDist_pt
  given: (h : x ∉ closure s)
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp only [infDist_empty, continuousAt_const]
  · refine (continuous_infDist_pt s).continuousAt.inv₀ ?_
    rwa [Ne, ← mem_closure_iff_infDist_zero hs]

中文:
定理 continuousAt_inv_infDist_pt
  条件: (h : x ∉ closure s)
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp only [infDist_empty, continuousAt_const]
  · refine (continuous_infDist_pt s).continuousAt.inv₀ ?_
    rwa [Ne, ← mem_closure_iff_infDist_zero hs]

Depends on / 依赖: continuousAt, continuousAt.inv, continuousAt_const, continuous_infDist_pt, eq_empty_or_nonempty, infDist_empty, mem_closure_iff_infDist_zero, s.eq_empty_or_nonempty
-/
theorem continuousAt_inv_infDist_pt (h : x ∉ closure s) :
    ContinuousAt (fun x => (infDist x s)⁻¹) x := by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp only [infDist_empty, continuousAt_const]
  · refine (continuous_infDist_pt s).continuousAt.inv₀ ?_
    rwa [Ne, ← mem_closure_iff_infDist_zero hs]

/--
theorem `infDist_image` / 定理 `infDist_image`

English:
theorem infDist_image
  given: (hΦ : Isometry Φ)
  statement: infDist (Φ x) (Φ '' t) = infDist x t
  proof: by
  simp [infDist, infEDist_image hΦ]

中文:
定理 infDist_image
  条件: (hΦ : Isometry Φ)
  结论: infDist (Φ x) (Φ '' t) = infDist x t
  证明: by
  simp [infDist, infEDist_image hΦ]

Depends on / 依赖: infDist, infEDist_image
-/
theorem infDist_image (hΦ : Isometry Φ) : infDist (Φ x) (Φ '' t) = infDist x t := by
  simp [infDist, infEDist_image hΦ]

/--
theorem `infDist_inter_closedBall_of_mem` / 定理 `infDist_inter_closedBall_of_mem`

English:
theorem infDist_inter_closedBall_of_mem
  given: (h : y in s)
  proof: by
  replace h : y in s inter closedBall x (dist y x) := ⟨h, mem_closedBall.2 le_rfl⟩
  refine le_antisymm ?_ (infDist_le_infDist_of_subset inter_subset_left ⟨y, h⟩)
  refine not_lt.1 fun hlt => ?_
  rcases (infDist_lt_iff ⟨y, h.1⟩).mp hlt with ⟨z, hzs, hz⟩
  rcases le_or_gt (dist z x) (dist y x) wi

中文:
定理 infDist_inter_closedBall_of_mem
  条件: (h : y in s)
  证明: by
  replace h : y in s inter closedBall x (dist y x) := ⟨h, mem_closedBall.2 le_rfl⟩
  refine le_antisymm ?_ (infDist_le_infDist_of_subset inter_subset_left ⟨y, h⟩)
  refine not_lt.1 fun hlt => ?_
  rcases (infDist_lt_iff ⟨y, h.1⟩).mp hlt with ⟨z, hzs, hz⟩
  rcases le_or_gt (dist z x) (dist y x) wi

Depends on / 依赖: closedBall, dist_comm, hlt.trans, hz.not_ge, infDist_le_dist_of_mem, infDist_le_infDist_of_subset, infDist_lt_iff, inter_subset_left, le_antisymm, le_or_gt, le_rfl, mem_closedBall, not_ge, not_lt, replace
-/
theorem infDist_inter_closedBall_of_mem (h : y in s) :
    infDist x (s inter closedBall x (dist y x)) = infDist x s := by
  replace h : y in s inter closedBall x (dist y x) := ⟨h, mem_closedBall.2 le_rfl⟩
  refine le_antisymm ?_ (infDist_le_infDist_of_subset inter_subset_left ⟨y, h⟩)
  refine not_lt.1 fun hlt => ?_
  rcases (infDist_lt_iff ⟨y, h.1⟩).mp hlt with ⟨z, hzs, hz⟩
  rcases le_or_gt (dist z x) (dist y x) with hle | hlt
  · exact hz.not_ge (infDist_le_dist_of_mem ⟨hzs, hle⟩)
  · rw [dist_comm z, dist_comm y] at hlt
    exact (hlt.trans hz).not_ge (infDist_le_dist_of_mem h)

/--
theorem `_root_.IsCompact.exists_infDist_eq_dist` / 定理 `_root_.IsCompact.exists_infDist_eq_dist`

English:
theorem _root_.IsCompact.exists_infDist_eq_dist
  given: (h : IsCompact s) (hne : s.Nonempty) (x : α)
  proof: let ⟨y, hys, hy⟩ := h.exists_infEDist_eq_edist hne x
  ⟨y, hys, by rw [infDist, dist_edist, hy]⟩

中文:
定理 _root_.IsCompact.exists_infDist_eq_dist
  条件: (h : IsCompact s) (hne : s.Nonempty) (x : α)
  证明: let ⟨y, hys, hy⟩ := h.exists_infEDist_eq_edist hne x
  ⟨y, hys, by rw [infDist, dist_edist, hy]⟩

Depends on / 依赖: dist_edist, exists_infEDist_eq_edist, h.exists_infEDist_eq_edist, infDist
-/
theorem _root_.IsCompact.exists_infDist_eq_dist (h : IsCompact s) (hne : s.Nonempty) (x : α) :
    exists y in s, infDist x s = dist x y :=
  let ⟨y, hys, hy⟩ := h.exists_infEDist_eq_edist hne x
  ⟨y, hys, by rw [infDist, dist_edist, hy]⟩

/--
theorem `_root_.IsClosed.exists_infDist_eq_dist` / 定理 `_root_.IsClosed.exists_infDist_eq_dist`

English:
theorem _root_.IsClosed.exists_infDist_eq_dist
  statement: [ProperSpace α] (h : IsClosed s) (hne : s.Nonempty)
  proof: by
  rcases hne with ⟨z, hz⟩
  rw [← infDist_inter_closedBall_of_mem hz]
  set t := s inter closedBall x (dist z x)
  have htc : IsCompact t := (isCompact_closedBall x (dist z x)).inter_left h
  have htne : t.Nonempty := ⟨z, hz, mem_closedBall.2 le_rfl⟩
  obtain ⟨y, ⟨hys, -⟩, hyd⟩ : exists y in t, i

中文:
定理 _root_.IsClosed.exists_infDist_eq_dist
  结论: [命题erSpace α] (h : IsClosed s) (hne : s.Nonempty)
  证明: by
  rcases hne with ⟨z, hz⟩
  rw [← infDist_inter_closedBall_of_mem hz]
  set t := s inter closedBall x (dist z x)
  have htc : IsCompact t := (isCompact_closedBall x (dist z x)).inter_left h
  have htne : t.Nonempty := ⟨z, hz, mem_closedBall.2 le_rfl⟩
  obtain ⟨y, ⟨hys, -⟩, hyd⟩ : exists y in t, i

Depends on / 依赖: IsCompact, Nonempty, closedBall, exists_infDist_eq_dist, htc.exists_infDist_eq_dist, infDist, infDist_inter_closedBall_of_mem, inter_left, isCompact_closedBall, le_rfl, mem_closedBall, t.Nonempty
-/
theorem _root_.IsClosed.exists_infDist_eq_dist [ProperSpace α] (h : IsClosed s) (hne : s.Nonempty)
    (x : α) : exists y in s, infDist x s = dist x y := by
  rcases hne with ⟨z, hz⟩
  rw [← infDist_inter_closedBall_of_mem hz]
  set t := s inter closedBall x (dist z x)
  have htc : IsCompact t := (isCompact_closedBall x (dist z x)).inter_left h
  have htne : t.Nonempty := ⟨z, hz, mem_closedBall.2 le_rfl⟩
  obtain ⟨y, ⟨hys, -⟩, hyd⟩ : exists y in t, infDist x t = dist x y := htc.exists_infDist_eq_dist htne x
  exact ⟨y, hys, hyd⟩

/--
theorem `exists_mem_closure_infDist_eq_dist` / 定理 `exists_mem_closure_infDist_eq_dist`

English:
theorem exists_mem_closure_infDist_eq_dist
  given: [ProperSpace α] (hne : s.Nonempty) (x : α)
  proof: by
  simpa only [infDist_closure] using isClosed_closure.exists_infDist_eq_dist hne.closure x

中文:
定理 exists_mem_closure_infDist_eq_dist
  条件: [命题erSpace α] (hne : s.Nonempty) (x : α)
  证明: by
  simpa only [infDist_closure] using isClosed_closure.exists_infDist_eq_dist hne.closure x

Depends on / 依赖: closure, exists_infDist_eq_dist, hne.closure, infDist_closure, isClosed_closure, isClosed_closure.exists_infDist_eq_dist
-/
theorem exists_mem_closure_infDist_eq_dist [ProperSpace α] (hne : s.Nonempty) (x : α) :
    exists y in closure s, infDist x s = dist x y := by
  simpa only [infDist_closure] using isClosed_closure.exists_infDist_eq_dist hne.closure x

/-! ### Distance of a point to a set as a function into `ℝ≥0`. -/

/--
Definition of `infNndist` / `infNndist` 的定义

English:
definition infNndist
  signature: (x : α) (s : Set α)
  body: ENNReal.toNNReal (infEDist x s)

@[simp]

中文:
定义 infNndist
  签名: (x : α) (s : Set α)
  定义体: ENNReal.toNNReal (infEDist x s)

@[simp]

Depends on / 依赖: ENNReal, ENNReal.toNNReal, infEDist, toNNReal
-/
def infNndist (x : α) (s : Set α) : Real>=0 :=
  ENNReal.toNNReal (infEDist x s)

@[simp]
/--
theorem `coe_infNndist` / 定理 `coe_infNndist`

English:
theorem coe_infNndist
  statement: (infNndist x s : Real) = infDist x s
  proof: rfl

中文:
定理 coe_infNndist
  结论: (infNndist x s : 实数) = infDist x s
  证明: rfl
-/
theorem coe_infNndist : (infNndist x s : Real) = infDist x s :=
  rfl

/--
theorem `lipschitz_infNndist_pt` / 定理 `lipschitz_infNndist_pt`

English:
theorem lipschitz_infNndist_pt
  given: (s : Set α)
  statement: LipschitzWith 1 fun x => infNndist x s
  proof: LipschitzWith.of_le_add fun _ _ => infDist_le_infDist_add_dist

中文:
定理 lipschitz_infNndist_pt
  条件: (s : Set α)
  结论: LipschitzWith 1 fun x => infNndist x s
  证明: LipschitzWith.of_le_add fun _ _ => infDist_le_infDist_add_dist

Depends on / 依赖: LipschitzWith, LipschitzWith.of_le_add, infDist_le_infDist_add_dist, of_le_add
-/
theorem lipschitz_infNndist_pt (s : Set α) : LipschitzWith 1 fun x => infNndist x s :=
  LipschitzWith.of_le_add fun _ _ => infDist_le_infDist_add_dist

/--
theorem `uniformContinuous_infNndist_pt` / 定理 `uniformContinuous_infNndist_pt`

English:
theorem uniformContinuous_infNndist_pt
  given: (s : Set α)
  statement: UniformContinuous fun x => infNndist x s
  proof: (lipschitz_infNndist_pt s).uniformContinuous

中文:
定理 uniformContinuous_infNndist_pt
  条件: (s : Set α)
  结论: UniformContinuous fun x => infNndist x s
  证明: (lipschitz_infNndist_pt s).uniformContinuous

Depends on / 依赖: lipschitz_infNndist_pt, uniformContinuous
-/
theorem uniformContinuous_infNndist_pt (s : Set α) : UniformContinuous fun x => infNndist x s :=
  (lipschitz_infNndist_pt s).uniformContinuous

/-- The minimal distance to a set (as `ℝ≥0`) is continuous in point -/
@[continuity, fun_prop]
/--
theorem `continuous_infNndist_pt` / 定理 `continuous_infNndist_pt`

English:
theorem continuous_infNndist_pt
  given: (s : Set α)
  statement: Continuous fun x => infNndist x s
  proof: (uniformContinuous_infNndist_pt s).continuous

中文:
定理 continuous_infNndist_pt
  条件: (s : Set α)
  结论: Continuous fun x => infNndist x s
  证明: (uniformContinuous_infNndist_pt s).continuous

Depends on / 依赖: continuous, uniformContinuous_infNndist_pt
-/
theorem continuous_infNndist_pt (s : Set α) : Continuous fun x => infNndist x s :=
  (uniformContinuous_infNndist_pt s).continuous

/-! ### The Hausdorff distance as a function into `ℝ`. -/

/--
Definition of `hausdorffDist` / `hausdorffDist` 的定义

English:
definition hausdorffDist
  signature: (s t : Set α)
  body: ENNReal.toReal (hausdorffEDist s t)

中文:
定义 hausdorffDist
  签名: (s t : Set α)
  定义体: ENNReal.toReal (hausdorffEDist s t)

Depends on / 依赖: ENNReal, ENNReal.toReal, hausdorffEDist, toReal
-/
def hausdorffDist (s t : Set α) : Real :=
  ENNReal.toReal (hausdorffEDist s t)

/--
theorem `hausdorffDist_nonneg` / 定理 `hausdorffDist_nonneg`

English:
theorem hausdorffDist_nonneg
  statement: 0 <= hausdorffDist s t
  proof: by simp [hausdorffDist]

中文:
定理 hausdorffDist_nonneg
  结论: 0 <= hausdorffDist s t
  证明: by simp [hausdorffDist]

Depends on / 依赖: hausdorffDist
-/
theorem hausdorffDist_nonneg : 0 <= hausdorffDist s t := by simp [hausdorffDist]

/--
theorem `hausdorffEDist_ne_top_of_nonempty_of_bounded` / 定理 `hausdorffEDist_ne_top_of_nonempty_of_bounded`

English:
theorem hausdorffEDist_ne_top_of_nonempty_of_bounded
  statement: (hs : s.Nonempty) (ht : t.Nonempty)
  proof: by
  rcases hs with ⟨cs, hcs⟩
  rcases ht with ⟨ct, hct⟩
  rcases bs.subset_closedBall ct with ⟨rs, hrs⟩
  rcases bt.subset_closedBall cs with ⟨rt, hrt⟩
  have : hausdorffEDist s t <= ENNReal.ofReal (max rs rt) := by
    apply hausdorffEDist_le_of_mem_edist
    · intro x xs
      exists ct, hct
    

中文:
定理 hausdorffEDist_ne_top_of_nonempty_of_bounded
  结论: (hs : s.Nonempty) (ht : t.Nonempty)
  证明: by
  rcases hs with ⟨cs, hcs⟩
  rcases ht with ⟨ct, hct⟩
  rcases bs.subset_closedBall ct with ⟨rs, hrs⟩
  rcases bt.subset_closedBall cs with ⟨rt, hrt⟩
  have : hausdorffEDist s t <= ENNReal.ofReal (max rs rt) := by
    apply hausdorffEDist_le_of_mem_edist
    · intro x xs
      exists ct, hct
    

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.ofReal_le_ofReal_iff, bs.subset_closedBall, bt.subset_closedBall, dist_nonneg, edist_dist, hausdorffEDist, hausdorffEDist_le_of_mem_edist, le_max_left, le_trans, ofReal, ofReal_le_ofReal_iff, subset_closedBall
-/
theorem hausdorffEDist_ne_top_of_nonempty_of_bounded (hs : s.Nonempty) (ht : t.Nonempty)
    (bs : IsBounded s) (bt : IsBounded t) : hausdorffEDist s t != ⊤ := by
  rcases hs with ⟨cs, hcs⟩
  rcases ht with ⟨ct, hct⟩
  rcases bs.subset_closedBall ct with ⟨rs, hrs⟩
  rcases bt.subset_closedBall cs with ⟨rt, hrt⟩
  have : hausdorffEDist s t <= ENNReal.ofReal (max rs rt) := by
    apply hausdorffEDist_le_of_mem_edist
    · intro x xs
      exists ct, hct
      have : dist x ct <= max rs rt := le_trans (hrs xs) (le_max_left _ _)
      rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff]
      exact le_trans dist_nonneg this
    · intro x xt
      exists cs, hcs
      have : dist x cs <= max rs rt := le_trans (hrt xt) (le_max_right _ _)
      rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff]
      exact le_trans dist_nonneg this
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_ne_top_of_nonempty_of_bounded := hausdorffEDist_ne_top_of_nonempty_of_bounded

/-- The Hausdorff distance between a set and itself is zero. -/
@[simp]
/--
theorem `hausdorffDist_self_zero` / 定理 `hausdorffDist_self_zero`

English:
theorem hausdorffDist_self_zero
  statement: hausdorffDist s s = 0
  proof: by simp [hausdorffDist]

中文:
定理 hausdorffDist_self_zero
  结论: hausdorffDist s s = 0
  证明: by simp [hausdorffDist]

Depends on / 依赖: hausdorffDist
-/
theorem hausdorffDist_self_zero : hausdorffDist s s = 0 := by simp [hausdorffDist]

/--
theorem `hausdorffDist_comm` / 定理 `hausdorffDist_comm`

English:
theorem hausdorffDist_comm
  statement: hausdorffDist s t = hausdorffDist t s
  proof: by
  simp [hausdorffDist, hausdorffEDist_comm]

中文:
定理 hausdorffDist_comm
  结论: hausdorffDist s t = hausdorffDist t s
  证明: by
  simp [hausdorffDist, hausdorffEDist_comm]

Depends on / 依赖: hausdorffDist, hausdorffEDist_comm
-/
theorem hausdorffDist_comm : hausdorffDist s t = hausdorffDist t s := by
  simp [hausdorffDist, hausdorffEDist_comm]

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value `∞` instead, use `Metric.hausdorffEDist`, which takes values in `ℝ≥0∞`). -/
@[simp]
/--
theorem `hausdorffDist_empty` / 定理 `hausdorffDist_empty`

English:
theorem hausdorffDist_empty
  statement: hausdorffDist s ∅ = 0
  proof: by
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h]
  · simp [hausdorffDist, hausdorffEDist_empty h]

中文:
定理 hausdorffDist_empty
  结论: hausdorffDist s ∅ = 0
  证明: by
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h]
  · simp [hausdorffDist, hausdorffEDist_empty h]

Depends on / 依赖: eq_empty_or_nonempty, hausdorffDist, hausdorffEDist_empty, s.eq_empty_or_nonempty
-/
theorem hausdorffDist_empty : hausdorffDist s ∅ = 0 := by
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h]
  · simp [hausdorffDist, hausdorffEDist_empty h]

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value `∞` instead, use `Metric.hausdorffEDist`, which takes values in `ℝ≥0∞`). -/
@[simp]
/--
theorem `hausdorffDist_empty'` / 定理 `hausdorffDist_empty'`

English:
theorem hausdorffDist_empty'
  statement: hausdorffDist ∅ s = 0
  proof: by simp [hausdorffDist_comm]

中文:
定理 hausdorffDist_empty'
  结论: hausdorffDist ∅ s = 0
  证明: by simp [hausdorffDist_comm]

Depends on / 依赖: hausdorffDist_comm
-/
theorem hausdorffDist_empty' : hausdorffDist ∅ s = 0 := by simp [hausdorffDist_comm]

/--
theorem `hausdorffDist_le_of_infDist` / 定理 `hausdorffDist_le_of_infDist`

English:
theorem hausdorffDist_le_of_infDist
  statement: {r : Real} (hr : 0 <= r) (H1 : forall x in s, infDist x t <= r)
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rwa [hausdorffDist_empty']
  rcases t.eq_empty_or_nonempty with rfl | ht
  · rwa [hausdorffDist_empty]
  have : hausdorffEDist s t <= ENNReal.ofReal r := by
    apply hausdorffEDist_le_of_infEDist _ _
    · simpa only [infDist, ← ENNReal.le_ofReal

中文:
定理 hausdorffDist_le_of_infDist
  结论: {r : 实数} (hr : 0 <= r) (H1 : 对任意 x in s, infDist x t <= r)
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rwa [hausdorffDist_empty']
  rcases t.eq_empty_or_nonempty with rfl | ht
  · rwa [hausdorffDist_empty]
  have : hausdorffEDist s t <= ENNReal.ofReal r := by
    apply hausdorffEDist_le_of_infEDist _ _
    · simpa only [infDist, ← ENNReal.le_ofReal

Depends on / 依赖: ENNReal, ENNReal.le_ofReal_iff_toReal_le, ENNReal.ofReal, ENNReal.toReal_le_of_le_ofReal, eq_empty_or_nonempty, hausdorffDist_empty, hausdorffEDist, hausdorffEDist_le_of_infEDist, infDist, infEDist_ne_top, le_ofReal_iff_toReal_le, ofReal, s.eq_empty_or_nonempty, t.eq_empty_or_nonempty, toReal_le_of_le_ofReal
-/
theorem hausdorffDist_le_of_infDist {r : Real} (hr : 0 <= r) (H1 : forall x in s, infDist x t <= r)
    (H2 : forall x in t, infDist x s <= r) : hausdorffDist s t <= r := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rwa [hausdorffDist_empty']
  rcases t.eq_empty_or_nonempty with rfl | ht
  · rwa [hausdorffDist_empty]
  have : hausdorffEDist s t <= ENNReal.ofReal r := by
    apply hausdorffEDist_le_of_infEDist _ _
    · simpa only [infDist, ← ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top ht) hr] using H1
    · simpa only [infDist, ← ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hs) hr] using H2
  exact ENNReal.toReal_le_of_le_ofReal hr this

/--
theorem `hausdorffDist_le_of_mem_dist` / 定理 `hausdorffDist_le_of_mem_dist`

English:
theorem hausdorffDist_le_of_mem_dist
  statement: {r : Real} (hr : 0 <= r) (H1 : forall x in s, exists y in t, dist x y <= r)
  proof: by
  apply hausdorffDist_le_of_infDist hr
  · intro x xs
    rcases H1 x xs with ⟨y, yt, hy⟩
    exact le_trans (infDist_le_dist_of_mem yt) hy
  · intro x xt
    rcases H2 x xt with ⟨y, ys, hy⟩
    exact le_trans (infDist_le_dist_of_mem ys) hy

中文:
定理 hausdorffDist_le_of_mem_dist
  结论: {r : 实数} (hr : 0 <= r) (H1 : 对任意 x in s, 存在 y in t, dist x y <= r)
  证明: by
  apply hausdorffDist_le_of_infDist hr
  · intro x xs
    rcases H1 x xs with ⟨y, yt, hy⟩
    exact le_trans (infDist_le_dist_of_mem yt) hy
  · intro x xt
    rcases H2 x xt with ⟨y, ys, hy⟩
    exact le_trans (infDist_le_dist_of_mem ys) hy

Depends on / 依赖: hausdorffDist_le_of_infDist, infDist_le_dist_of_mem, le_trans
-/
theorem hausdorffDist_le_of_mem_dist {r : Real} (hr : 0 <= r) (H1 : forall x in s, exists y in t, dist x y <= r)
    (H2 : forall x in t, exists y in s, dist x y <= r) : hausdorffDist s t <= r := by
  apply hausdorffDist_le_of_infDist hr
  · intro x xs
    rcases H1 x xs with ⟨y, yt, hy⟩
    exact le_trans (infDist_le_dist_of_mem yt) hy
  · intro x xt
    rcases H2 x xt with ⟨y, ys, hy⟩
    exact le_trans (infDist_le_dist_of_mem ys) hy

/--
theorem `hausdorffDist_le_diam` / 定理 `hausdorffDist_le_diam`

English:
theorem hausdorffDist_le_diam
  statement: (hs : s.Nonempty) (bs : IsBounded s) (ht : t.Nonempty)
  proof: by
  rcases hs with ⟨x, xs⟩
  rcases ht with ⟨y, yt⟩
  refine hausdorffDist_le_of_mem_dist diam_nonneg ?_ ?_
  · exact fun z hz => ⟨y, yt, dist_le_diam_of_mem (bs.union bt) (subset_union_left hz)
      (subset_union_right yt)⟩
  · exact fun z hz => ⟨x, xs, dist_le_diam_of_mem (bs.union bt) (subset_u

中文:
定理 hausdorffDist_le_diam
  结论: (hs : s.Nonempty) (bs : IsBounded s) (ht : t.Nonempty)
  证明: by
  rcases hs with ⟨x, xs⟩
  rcases ht with ⟨y, yt⟩
  refine hausdorffDist_le_of_mem_dist diam_nonneg ?_ ?_
  · exact fun z hz => ⟨y, yt, dist_le_diam_of_mem (bs.union bt) (subset_union_left hz)
      (subset_union_right yt)⟩
  · exact fun z hz => ⟨x, xs, dist_le_diam_of_mem (bs.union bt) (subset_u

Depends on / 依赖: bs.union, diam_nonneg, dist_le_diam_of_mem, hausdorffDist_le_of_mem_dist, subset_union_left, subset_union_right
-/
theorem hausdorffDist_le_diam (hs : s.Nonempty) (bs : IsBounded s) (ht : t.Nonempty)
    (bt : IsBounded t) : hausdorffDist s t <= diam (s union t) := by
  rcases hs with ⟨x, xs⟩
  rcases ht with ⟨y, yt⟩
  refine hausdorffDist_le_of_mem_dist diam_nonneg ?_ ?_
  · exact fun z hz => ⟨y, yt, dist_le_diam_of_mem (bs.union bt) (subset_union_left hz)
      (subset_union_right yt)⟩
  · exact fun z hz => ⟨x, xs, dist_le_diam_of_mem (bs.union bt) (subset_union_right hz)
      (subset_union_left xs)⟩

/--
theorem `infDist_le_hausdorffDist_of_mem` / 定理 `infDist_le_hausdorffDist_of_mem`

English:
theorem infDist_le_hausdorffDist_of_mem
  given: (hx : x in s) (fin : hausdorffEDist s t != ⊤)
  proof: toReal_mono fin (infEDist_le_hausdorffEDist_of_mem hx)

中文:
定理 infDist_le_hausdorffDist_of_mem
  条件: (hx : x in s) (fin : hausdorffEDist s t != ⊤)
  证明: toReal_mono fin (infEDist_le_hausdorffEDist_of_mem hx)

Depends on / 依赖: infEDist_le_hausdorffEDist_of_mem, toReal_mono
-/
theorem infDist_le_hausdorffDist_of_mem (hx : x in s) (fin : hausdorffEDist s t != ⊤) :
    infDist x t <= hausdorffDist s t :=
  toReal_mono fin (infEDist_le_hausdorffEDist_of_mem hx)

/--
theorem `exists_dist_lt_of_hausdorffDist_lt` / 定理 `exists_dist_lt_of_hausdorffDist_lt`

English:
theorem exists_dist_lt_of_hausdorffDist_lt
  statement: {r : Real} (h : x in s) (H : hausdorffDist s t < r)
  proof: by
  have r0 : 0 < r := lt_of_le_of_lt hausdorffDist_nonneg H
  have : hausdorffEDist s t < ENNReal.ofReal r := by
    rwa [hausdorffDist, ← ENNReal.toReal_ofReal (le_of_lt r0),
      ENNReal.toReal_lt_toReal fin ENNReal.ofReal_ne_top] at H
  rcases exists_edist_lt_of_hausdorffEDist_lt h this with ⟨

中文:
定理 exists_dist_lt_of_hausdorffDist_lt
  结论: {r : 实数} (h : x in s) (H : hausdorffDist s t < r)
  证明: by
  have r0 : 0 < r := lt_of_le_of_lt hausdorffDist_nonneg H
  have : hausdorffEDist s t < ENNReal.ofReal r := by
    rwa [hausdorffDist, ← ENNReal.toReal_ofReal (le_of_lt r0),
      ENNReal.toReal_lt_toReal fin ENNReal.ofReal_ne_top] at H
  rcases exists_edist_lt_of_hausdorffEDist_lt h this with ⟨

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.ofReal_lt_ofReal_iff, ENNReal.ofReal_ne_top, ENNReal.toReal_lt_toReal, ENNReal.toReal_ofReal, edist_dist, exists_edist_lt_of_hausdorffEDist_lt, hausdorffDist, hausdorffDist_nonneg, hausdorffEDist, le_of_lt, lt_of_le_of_lt, ofReal, ofReal_lt_ofReal_iff, ofReal_ne_top, toReal_lt_toReal, toReal_ofReal
-/
theorem exists_dist_lt_of_hausdorffDist_lt {r : Real} (h : x in s) (H : hausdorffDist s t < r)
    (fin : hausdorffEDist s t != ⊤) : exists y in t, dist x y < r := by
  have r0 : 0 < r := lt_of_le_of_lt hausdorffDist_nonneg H
  have : hausdorffEDist s t < ENNReal.ofReal r := by
    rwa [hausdorffDist, ← ENNReal.toReal_ofReal (le_of_lt r0),
      ENNReal.toReal_lt_toReal fin ENNReal.ofReal_ne_top] at H
  rcases exists_edist_lt_of_hausdorffEDist_lt h this with ⟨y, hy, yr⟩
  rw [edist_dist]; rw [ENNReal.ofReal_lt_ofReal_iff r0] at yr
  exact ⟨y, hy, yr⟩

/--
theorem `exists_dist_lt_of_hausdorffDist_lt'` / 定理 `exists_dist_lt_of_hausdorffDist_lt'`

English:
theorem exists_dist_lt_of_hausdorffDist_lt'
  statement: {r : Real} (h : y in t) (H : hausdorffDist s t < r)
  proof: by
  rw [hausdorffDist_comm] at H
  rw [hausdorffEDist_comm] at fin
  simpa [dist_comm] using exists_dist_lt_of_hausdorffDist_lt h H fin

中文:
定理 exists_dist_lt_of_hausdorffDist_lt'
  结论: {r : 实数} (h : y in t) (H : hausdorffDist s t < r)
  证明: by
  rw [hausdorffDist_comm] at H
  rw [hausdorffEDist_comm] at fin
  simpa [dist_comm] using exists_dist_lt_of_hausdorffDist_lt h H fin

Depends on / 依赖: dist_comm, exists_dist_lt_of_hausdorffDist_lt, hausdorffDist_comm, hausdorffEDist_comm
-/
theorem exists_dist_lt_of_hausdorffDist_lt' {r : Real} (h : y in t) (H : hausdorffDist s t < r)
    (fin : hausdorffEDist s t != ⊤) : exists x in s, dist x y < r := by
  rw [hausdorffDist_comm] at H
  rw [hausdorffEDist_comm] at fin
  simpa [dist_comm] using exists_dist_lt_of_hausdorffDist_lt h H fin

/--
theorem `infDist_le_infDist_add_hausdorffDist` / 定理 `infDist_le_infDist_add_hausdorffDist`

English:
theorem infDist_le_infDist_add_hausdorffDist
  given: (fin : hausdorffEDist s t != ⊤)
  proof: by
  refine toReal_le_add' infEDist_le_infEDist_add_hausdorffEDist (fun h => ?_) (flip absurd fin)
  rw [infEDist_eq_top_iff]; rw [← not_nonempty_iff_eq_empty] at h ⊢
  rw [hausdorffEDist_comm] at fin
  exact mt (nonempty_of_hausdorffEDist_ne_top · fin) h

中文:
定理 infDist_le_infDist_add_hausdorffDist
  条件: (fin : hausdorffEDist s t != ⊤)
  证明: by
  refine toReal_le_add' infEDist_le_infEDist_add_hausdorffEDist (fun h => ?_) (flip absurd fin)
  rw [infEDist_eq_top_iff]; rw [← not_nonempty_iff_eq_empty] at h ⊢
  rw [hausdorffEDist_comm] at fin
  exact mt (nonempty_of_hausdorffEDist_ne_top · fin) h

Depends on / 依赖: absurd, hausdorffEDist_comm, infEDist_eq_top_iff, infEDist_le_infEDist_add_hausdorffEDist, nonempty_of_hausdorffEDist_ne_top, not_nonempty_iff_eq_empty, toReal_le_add
-/
theorem infDist_le_infDist_add_hausdorffDist (fin : hausdorffEDist s t != ⊤) :
    infDist x t <= infDist x s + hausdorffDist s t := by
  refine toReal_le_add' infEDist_le_infEDist_add_hausdorffEDist (fun h => ?_) (flip absurd fin)
  rw [infEDist_eq_top_iff]; rw [← not_nonempty_iff_eq_empty] at h ⊢
  rw [hausdorffEDist_comm] at fin
  exact mt (nonempty_of_hausdorffEDist_ne_top · fin) h

/--
theorem `hausdorffDist_image` / 定理 `hausdorffDist_image`

English:
theorem hausdorffDist_image
  given: (h : Isometry Φ)
  proof: by
  simp [hausdorffDist, hausdorffEDist_image h]

中文:
定理 hausdorffDist_image
  条件: (h : Isometry Φ)
  证明: by
  simp [hausdorffDist, hausdorffEDist_image h]

Depends on / 依赖: hausdorffDist, hausdorffEDist_image
-/
theorem hausdorffDist_image (h : Isometry Φ) :
    hausdorffDist (Φ '' s) (Φ '' t) = hausdorffDist s t := by
  simp [hausdorffDist, hausdorffEDist_image h]

/--
theorem `hausdorffDist_triangle` / 定理 `hausdorffDist_triangle`

English:
theorem hausdorffDist_triangle
  given: (fin : hausdorffEDist s t != ⊤)
  proof: by
  refine toReal_le_add' hausdorffEDist_triangle (flip absurd fin) (not_imp_not.1 fun h => ?_)
  rw [hausdorffEDist_comm] at fin
  exact ne_top_of_le_ne_top (add_ne_top.2 ⟨fin, h⟩) hausdorffEDist_triangle

中文:
定理 hausdorffDist_triangle
  条件: (fin : hausdorffEDist s t != ⊤)
  证明: by
  refine toReal_le_add' hausdorffEDist_triangle (flip absurd fin) (not_imp_not.1 fun h => ?_)
  rw [hausdorffEDist_comm] at fin
  exact ne_top_of_le_ne_top (add_ne_top.2 ⟨fin, h⟩) hausdorffEDist_triangle

Depends on / 依赖: absurd, add_ne_top, hausdorffEDist_comm, hausdorffEDist_triangle, ne_top_of_le_ne_top, not_imp_not, toReal_le_add
-/
theorem hausdorffDist_triangle (fin : hausdorffEDist s t != ⊤) :
    hausdorffDist s u <= hausdorffDist s t + hausdorffDist t u := by
  refine toReal_le_add' hausdorffEDist_triangle (flip absurd fin) (not_imp_not.1 fun h => ?_)
  rw [hausdorffEDist_comm] at fin
  exact ne_top_of_le_ne_top (add_ne_top.2 ⟨fin, h⟩) hausdorffEDist_triangle

/--
theorem `hausdorffDist_triangle'` / 定理 `hausdorffDist_triangle'`

English:
theorem hausdorffDist_triangle'
  given: (fin : hausdorffEDist t u != ⊤)
  proof: by
  rw [hausdorffEDist_comm] at fin
  have I : hausdorffDist u s <= hausdorffDist u t + hausdorffDist t s :=
    hausdorffDist_triangle fin
  simpa [add_comm, hausdorffDist_comm] using I

中文:
定理 hausdorffDist_triangle'
  条件: (fin : hausdorffEDist t u != ⊤)
  证明: by
  rw [hausdorffEDist_comm] at fin
  have I : hausdorffDist u s <= hausdorffDist u t + hausdorffDist t s :=
    hausdorffDist_triangle fin
  simpa [add_comm, hausdorffDist_comm] using I

Depends on / 依赖: add_comm, hausdorffDist, hausdorffDist_comm, hausdorffDist_triangle, hausdorffEDist_comm
-/
theorem hausdorffDist_triangle' (fin : hausdorffEDist t u != ⊤) :
    hausdorffDist s u <= hausdorffDist s t + hausdorffDist t u := by
  rw [hausdorffEDist_comm] at fin
  have I : hausdorffDist u s <= hausdorffDist u t + hausdorffDist t s :=
    hausdorffDist_triangle fin
  simpa [add_comm, hausdorffDist_comm] using I

/-- The Hausdorff distance between a set and its closure vanishes. -/
@[simp]
/--
theorem `hausdorffDist_self_closure` / 定理 `hausdorffDist_self_closure`

English:
theorem hausdorffDist_self_closure
  statement: hausdorffDist s (closure s) = 0
  proof: by simp [hausdorffDist]

中文:
定理 hausdorffDist_self_closure
  结论: hausdorffDist s (closure s) = 0
  证明: by simp [hausdorffDist]

Depends on / 依赖: hausdorffDist
-/
theorem hausdorffDist_self_closure : hausdorffDist s (closure s) = 0 := by simp [hausdorffDist]

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp]
/--
theorem `hausdorffDist_closure₁` / 定理 `hausdorffDist_closure₁`

English:
theorem hausdorffDist_closure₁
  statement: hausdorffDist (closure s) t = hausdorffDist s t
  proof: by
  simp [hausdorffDist]

中文:
定理 hausdorffDist_closure₁
  结论: hausdorffDist (closure s) t = hausdorffDist s t
  证明: by
  simp [hausdorffDist]

Depends on / 依赖: hausdorffDist
-/
theorem hausdorffDist_closure₁ : hausdorffDist (closure s) t = hausdorffDist s t := by
  simp [hausdorffDist]

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp]
/--
theorem `hausdorffDist_closure₂` / 定理 `hausdorffDist_closure₂`

English:
theorem hausdorffDist_closure₂
  statement: hausdorffDist s (closure t) = hausdorffDist s t
  proof: by
  simp [hausdorffDist]

中文:
定理 hausdorffDist_closure₂
  结论: hausdorffDist s (closure t) = hausdorffDist s t
  证明: by
  simp [hausdorffDist]

Depends on / 依赖: hausdorffDist
-/
theorem hausdorffDist_closure₂ : hausdorffDist s (closure t) = hausdorffDist s t := by
  simp [hausdorffDist]

/--
theorem `hausdorffDist_closure` / 定理 `hausdorffDist_closure`

English:
theorem hausdorffDist_closure
  statement: hausdorffDist (closure s) (closure t) = hausdorffDist s t
  proof: by
  simp [hausdorffDist]

中文:
定理 hausdorffDist_closure
  结论: hausdorffDist (closure s) (closure t) = hausdorffDist s t
  证明: by
  simp [hausdorffDist]

Depends on / 依赖: hausdorffDist
-/
theorem hausdorffDist_closure : hausdorffDist (closure s) (closure t) = hausdorffDist s t := by
  simp [hausdorffDist]

/--
theorem `hausdorffDist_zero_iff_closure_eq_closure` / 定理 `hausdorffDist_zero_iff_closure_eq_closure`

English:
theorem hausdorffDist_zero_iff_closure_eq_closure
  given: (fin : hausdorffEDist s t != ⊤)
  proof: by
  simp [← hausdorffEDist_zero_iff_closure_eq_closure, hausdorffDist,
    ENNReal.toReal_eq_zero_iff, fin]

中文:
定理 hausdorffDist_zero_iff_closure_eq_closure
  条件: (fin : hausdorffEDist s t != ⊤)
  证明: by
  simp [← hausdorffEDist_zero_iff_closure_eq_closure, hausdorffDist,
    ENNReal.toReal_eq_zero_iff, fin]

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_zero_iff, hausdorffDist, hausdorffEDist_zero_iff_closure_eq_closure, toReal_eq_zero_iff
-/
theorem hausdorffDist_zero_iff_closure_eq_closure (fin : hausdorffEDist s t != ⊤) :
    hausdorffDist s t = 0 ↔ closure s = closure t := by
  simp [← hausdorffEDist_zero_iff_closure_eq_closure, hausdorffDist,
    ENNReal.toReal_eq_zero_iff, fin]

/--
theorem `_root_.IsClosed.hausdorffDist_zero_iff_eq` / 定理 `_root_.IsClosed.hausdorffDist_zero_iff_eq`

English:
theorem _root_.IsClosed.hausdorffDist_zero_iff_eq
  statement: (hs : IsClosed s) (ht : IsClosed t)
  proof: by
  simp [← _root_.IsClosed.hausdorffEDist_zero_iff hs ht, hausdorffDist, ENNReal.toReal_eq_zero_iff,
    fin]

@[simp]

中文:
定理 _root_.IsClosed.hausdorffDist_zero_iff_eq
  结论: (hs : IsClosed s) (ht : IsClosed t)
  证明: by
  simp [← _root_.IsClosed.hausdorffEDist_zero_iff hs ht, hausdorffDist, ENNReal.toReal_eq_zero_iff,
    fin]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_zero_iff, IsClosed, _root_, _root_.IsClosed.hausdorffEDist_zero_iff, hausdorffDist, hausdorffEDist_zero_iff, toReal_eq_zero_iff
-/
theorem _root_.IsClosed.hausdorffDist_zero_iff_eq (hs : IsClosed s) (ht : IsClosed t)
    (fin : hausdorffEDist s t != ⊤) : hausdorffDist s t = 0 ↔ s = t := by
  simp [← _root_.IsClosed.hausdorffEDist_zero_iff hs ht, hausdorffDist, ENNReal.toReal_eq_zero_iff,
    fin]

@[simp]
/--
theorem `hausdorffDist_singleton` / 定理 `hausdorffDist_singleton`

English:
theorem hausdorffDist_singleton
  statement: hausdorffDist {x} {y} = dist x y
  proof: by
  rw [hausdorffDist]; rw [hausdorffEDist_singleton]; rw [dist_edist]

中文:
定理 hausdorffDist_singleton
  结论: hausdorffDist {x} {y} = dist x y
  证明: by
  rw [hausdorffDist]; rw [hausdorffEDist_singleton]; rw [dist_edist]

Depends on / 依赖: dist_edist, hausdorffDist, hausdorffEDist_singleton
-/
theorem hausdorffDist_singleton : hausdorffDist {x} {y} = dist x y := by
  rw [hausdorffDist]; rw [hausdorffEDist_singleton]; rw [dist_edist]

end

end Metric
