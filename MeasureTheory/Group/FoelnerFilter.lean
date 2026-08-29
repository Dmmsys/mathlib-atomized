/-
Copyright (c) 2025 Stefano Rocca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Stefano Rocca
-/
module

public import Mathlib.MeasureTheory.Group.Action

/-!
# Følner sequences and filters - definitions and properties

This file defines Følner sequences and filters for measurable spaces acted on by a group.

## Definitions

* `IsFoelner G μ l F` : Consider a group `G` acting on a measure space `X`.
  A sequence of sets `F : ι → Set X` is **Følner** with respect to the `G`-action, the measure `μ`,
  and a filter `l` on the indexing type `ι`, if:
  1. Eventually, as `i` tends to `l`, the set `F i` is measurable with finite non-zero measure,
  2. For all `g : G`, `μ ((g • F i) ∆ F i) / μ (F i)` tends to `0`.

* `IsFoelner.mean μ u F s` : The limit along an ultrafilter `u` of the density of a set `s`
  with respect to a Følner sequence `F` in the measure space `X`.

* `maxFoelner G μ` : The maximal Følner filter with respect to some group `G` acting on a
  measure space `X` is the pullback of `𝓝 0` along the map `s ↦ μ (g • s) / μ s` over measurable
  sets of finite non-zero measure.

* `IsAddFoelner G μ l F`: the analog of `IsFoelner G μ l F` for an additive group action

## Main results

* `IsFoelner.amenable` : If there exists a non-trivial Følner filter with respect to some
  group `G` acting on a measure space `X`, then there exists a `G`-invariant finitely additive
  probability measure on `X`.

* `isFoelner_iff_tendsto` : A sequence of sets is Følner if and only if it tends to the
  maximal Følner filter.
  The attribute "maximal" of the latter comes from the direct implication of this theorem :
  if `IsFoelner G μ l F` then the push-forward filter `map F l ≤ maxFoelner G μ`.

* `amenable_of_maxFoelner_neBot` : If the maximal Følner filter is non-trivial,
  then there exists a `G`-invariant finitely additive probability measure on `X`.

## Temporary design adaptations

* In the current version, we refer to the amenability of the action of a group on a measure space
  (e.g. in `IsFoelner.amenable` and `amenable_of_maxFoelner_neBot`), even though a definition of
  amenability has not yet been given in Mathlib.
  This is because there are different notions of amenability for groups and for group actions,
  and a Mathlib definition should be provided at the greatest level of generality, on which there
  has not yet been a general consensus.
  At the present moment, `amenable` corresponds to the existence of a `G`-invariant finitely
  additive probability measure.

## Tags

Foelner, Følner filter, amenability, amenable group
-/

@[expose] public section

open MeasureTheory Filter Set Tendsto
open scoped ENNReal Pointwise symmDiff Topology Filter

variable {G X : Type*} [MeasurableSpace X] {μ : Measure X} [Group G] [MulAction G X]
variable {ι : Type*} {l : Filter ι} {u : Ultrafilter ι} {F : ι -> Set X}

variable (G : Type*) {X : Type*} [MeasurableSpace X] (μ : Measure X) [AddGroup G] [AddAction G X]
         {ι : Type*} (l : Filter ι) (F : ι -> Set X) in
/-- Consider an additive group `G` acting on a measure space `X`.
  A sequence of sets `F : ι → Set X` is **Følner** with respect to the `G`-action,
  the measure `μ`, and a filter `l` on the indexing type `ι`, if:
  1. Each `s` in `l` is eventually measurable with finite non-zero measure,
  2. For all `g : G`, `μ ((g +ᵥ F i) ∆ F i) / μ (F i)` tends to `0`. -/
@[mk_iff]
/--
Definition of `IsAddFoelner` / `IsAddFoelner` 的定义

English:
structure IsAddFoelner
  parameters: : Prop where
  axioms and operations (4):
    - eventually_measurableSet : forallᶠ i in l, MeasurableSet (F i)
    - eventually_meas_ne_zero : forallᶠ i in l, μ (F i) != 0
    - eventually_meas_ne_top : forallᶠ i in l, μ (F i) != ∞
    - tendsto_meas_vadd_symmDiff((g : G)) : Tendsto (fun i => μ ((g +ᵥ F i) ∆ F i) / μ (F i)) l (𝓝 0)

中文:
结构 是加法Foelner
  参数: : 命题 where
  公理与运算 (4 个):
    - eventually_measurableSet : 对任意ᶠ i in l, 可测集 (F i)
    - eventually_meas_ne_zero : 对任意ᶠ i in l, μ (F i) != 0
    - eventually_meas_ne_top : 对任意ᶠ i in l, μ (F i) != ∞
    - tendsto_meas_vadd_symmDiff((g : G)) : 收敛 (fun i => μ ((g +ᵥ F i) ∆ F i) / μ (F i)) l (𝓝 0)
-/
structure IsAddFoelner : Prop where
  eventually_measurableSet : forallᶠ i in l, MeasurableSet (F i)
  eventually_meas_ne_zero : forallᶠ i in l, μ (F i) != 0
  eventually_meas_ne_top : forallᶠ i in l, μ (F i) != ∞
  tendsto_meas_vadd_symmDiff (g : G) : Tendsto (fun i => μ ((g +ᵥ F i) ∆ F i) / μ (F i)) l (𝓝 0)

variable (G μ l F) in
/-- Consider a group `G` acting on a measure space `X`.
  A sequence of sets `F : ι → Set X` is **Følner** with respect to the `G`-action,
  the measure `μ`, and a filter `l` on the indexing type `ι`, if:
  1. Each `s` in `l` is eventually measurable with finite non-zero measure,
  2. For all `g : G`, `μ ((g • F i) ∆ F i) / μ (F i)` tends to `0`. -/
@[mk_iff]
/--
Definition of `IsFoelner` / `IsFoelner` 的定义

English:
structure IsFoelner
  parameters: : Prop where
  axioms and operations (4):
    - eventually_measurableSet : forallᶠ i in l, MeasurableSet (F i)
    - eventually_meas_ne_zero : forallᶠ i in l, μ (F i) != 0
    - eventually_meas_ne_top : forallᶠ i in l, μ (F i) != ∞
    - tendsto_meas_smul_symmDiff((g : G)) : Tendsto (fun i => μ ((g • F i) ∆ F i) / μ (F i)) l (𝓝 0)

中文:
结构 是Foelner
  参数: : 命题 where
  公理与运算 (4 个):
    - eventually_measurableSet : 对任意ᶠ i in l, 可测集 (F i)
    - eventually_meas_ne_zero : 对任意ᶠ i in l, μ (F i) != 0
    - eventually_meas_ne_top : 对任意ᶠ i in l, μ (F i) != ∞
    - tendsto_meas_smul_symmDiff((g : G)) : 收敛 (fun i => μ ((g • F i) ∆ F i) / μ (F i)) l (𝓝 0)
-/
structure IsFoelner : Prop where
  eventually_measurableSet : forallᶠ i in l, MeasurableSet (F i)
  eventually_meas_ne_zero : forallᶠ i in l, μ (F i) != 0
  eventually_meas_ne_top : forallᶠ i in l, μ (F i) != ∞
  tendsto_meas_smul_symmDiff (g : G) : Tendsto (fun i => μ ((g • F i) ∆ F i) / μ (F i)) l (𝓝 0)

attribute [to_additive IsAddFoelner] IsFoelner
attribute [to_additive existing isAddFoelner_iff] isFoelner_iff

namespace IsFoelner

/-- The constant sequence `X` is Følner if `X` has finite measure. -/
@[to_additive /--The constant sequence `X` is Følner if `X` has finite measure. -/]
/--
theorem `univ_of_isFiniteMeasure` / 定理 `univ_of_isFiniteMeasure`

English:
theorem univ_of_isFiniteMeasure
  given: [NeZero μ] [IsFiniteMeasure μ]
  proof: by simp
  eventually_meas_ne_zero := by simp [NeZero.ne]
  eventually_meas_ne_top := by simp
  tendsto_meas_smul_symmDiff := by simp [tendsto_const_nhds]

@[to_additive]

中文:
定理 univ_of_isFiniteMeasure
  条件: [NeZero μ] [是有限测度 μ]
  证明: by simp
  eventually_meas_ne_zero := by simp [NeZero.ne]
  eventually_meas_ne_top := by simp
  tendsto_meas_smul_symmDiff := by simp [tendsto_const_nhds]

@[to_additive]

Depends on / 依赖: ContinuousMap, ContinuousMap.smul_apply, NeZero, NeZero.ne, _apply, contractSnd_apply, eventually_meas_ne_top, eventually_meas_ne_zero, map_smul, mul_comm, prodMk, simp_rw, smul_apply, smul_eq_mul, tendsto_const_nhds, tendsto_meas_smul_symmDiff
-/
theorem univ_of_isFiniteMeasure [NeZero μ] [IsFiniteMeasure μ] :
    IsFoelner G μ l (fun _ => .univ) where
  eventually_measurableSet := by simp
  eventually_meas_ne_zero := by simp [NeZero.ne]
  eventually_meas_ne_top := by simp
  tendsto_meas_smul_symmDiff := by simp [tendsto_const_nhds]

@[to_additive]
/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {l' : Filter ι} (hfoel : IsFoelner G μ l F) (hle : l' <= l)
  proof: hfoel.eventually_measurableSet.filter_mono hle
  eventually_meas_ne_zero := hfoel.eventually_meas_ne_zero.filter_mono hle
  eventually_meas_ne_top := hfoel.eventually_meas_ne_top.filter_mono hle
  tendsto_meas_smul_symmDiff (g : G) := Tendsto.mono_left (hfoel.tendsto_meas_smul_symmDiff g) hle

@[to_additive]

中文:
定理 mono
  条件: {l' : 滤子 ι} (hfoel : 是Foelner G μ l F) (hle : l' <= l)
  证明: hfoel.eventually_measurableSet.filter_mono hle
  eventually_meas_ne_zero := hfoel.eventually_meas_ne_zero.filter_mono hle
  eventually_meas_ne_top := hfoel.eventually_meas_ne_top.filter_mono hle
  tendsto_meas_smul_symmDiff (g : G) := Tendsto.mono_left (hfoel.tendsto_meas_smul_symmDiff g) hle

@[to_additive]

Depends on / 依赖: eventually_measurableSet, filter_mono, hfoel.eventually_measurableSet.filter_mono
-/
theorem mono {l' : Filter ι} (hfoel : IsFoelner G μ l F) (hle : l' <= l) :
    IsFoelner G μ l' F where
  eventually_measurableSet := hfoel.eventually_measurableSet.filter_mono hle
  eventually_meas_ne_zero := hfoel.eventually_meas_ne_zero.filter_mono hle
  eventually_meas_ne_top := hfoel.eventually_meas_ne_top.filter_mono hle
  tendsto_meas_smul_symmDiff (g : G) := Tendsto.mono_left (hfoel.tendsto_meas_smul_symmDiff g) hle

@[to_additive]
/--
theorem `comp_tendsto` / 定理 `comp_tendsto`

English:
theorem comp_tendsto
  statement: {ι' : Type*} {l' : Filter ι'} {φ : ι' -> ι} (hfoel : IsFoelner G μ l F)
  proof: htendsto.eventually hfoel.eventually_measurableSet
  eventually_meas_ne_zero := htendsto.eventually hfoel.eventually_meas_ne_zero
  eventually_meas_ne_top := htendsto.eventually hfoel.eventually_meas_ne_top
  tendsto_meas_smul_symmDiff (g : G) := (hfoel.tendsto_meas_smul_symmDiff g).comp htendsto

中文:
定理 comp_tendsto
  结论: {ι' : 类型} {l' : 滤子 ι'} {φ : ι' -> ι} (hfoel : 是Foelner G μ l F)
  证明: htendsto.eventually hfoel.eventually_measurableSet
  eventually_meas_ne_zero := htendsto.eventually hfoel.eventually_meas_ne_zero
  eventually_meas_ne_top := htendsto.eventually hfoel.eventually_meas_ne_top
  tendsto_meas_smul_symmDiff (g : G) := (hfoel.tendsto_meas_smul_symmDiff g).comp htendsto

Depends on / 依赖: eventually, eventually_measurableSet, hfoel.eventually_measurableSet, htendsto, htendsto.eventually
-/
theorem comp_tendsto {ι' : Type*} {l' : Filter ι'} {φ : ι' -> ι} (hfoel : IsFoelner G μ l F)
    (htendsto : Tendsto φ l' l) :
    IsFoelner G μ l' (F ∘ φ) where
  eventually_measurableSet := htendsto.eventually hfoel.eventually_measurableSet
  eventually_meas_ne_zero := htendsto.eventually hfoel.eventually_meas_ne_zero
  eventually_meas_ne_top := htendsto.eventually hfoel.eventually_meas_ne_top
  tendsto_meas_smul_symmDiff (g : G) := (hfoel.tendsto_meas_smul_symmDiff g).comp htendsto

variable (μ u F) in
/-- The limit along an ultrafilter of the density of a set with respect to a sequence in `X`. -/
@[to_additive
/-- The limit along an ultrafilter of the density of a set with respect to a sequence in `X`. -/]
/--
Definition of `mean` / `mean` 的定义

English:
definition mean
  signature: (s : Set X)
  body: limUnder u (fun i => μ (s inter F i) / μ (F i))

@[to_additive]

中文:
定义 mean
  签名: (s : 集合 X)
  定义体: limUnder u (fun i => μ (s inter F i) / μ (F i))

@[to_additive]

Depends on / 依赖: limUnder
-/
noncomputable def mean (s : Set X) :=
  limUnder u (fun i => μ (s inter F i) / μ (F i))

@[to_additive]
/--
theorem `tendsto_nhds_mean` / 定理 `tendsto_nhds_mean`

English:
theorem tendsto_nhds_mean
  given: (hfoel : IsFoelner G μ u F) (s : Set X)
  proof: by
  have mem_Icc : forallᶠ i in u, μ (s inter F i) / μ (F i) in Icc 0 1 := by
    filter_upwards [hfoel.eventually_meas_ne_zero, hfoel.eventually_meas_ne_top] with i hi hi'
    simpa [ENNReal.div_le_iff hi hi'] using μ.mono inter_subset_right
  obtain ⟨x, hx⟩ := isCompact_Icc.ultrafilter_le_nhds'
    (u.map (fun i => μ (s inter F i) / μ (F i))) (mem_map.1 mem_Icc)
  exact tendsto_nhds_limUnder (by use x; exact hx.2)

@[to_additive]

中文:
定理 tendsto_nhds_mean
  条件: (hfoel : 是Foelner G μ u F) (s : 集合 X)
  证明: by
  have mem_Icc : forallᶠ i in u, μ (s inter F i) / μ (F i) in Icc 0 1 := by
    filter_upwards [hfoel.eventually_meas_ne_zero, hfoel.eventually_meas_ne_top] with i hi hi'
    simpa [ENNReal.div_le_iff hi hi'] using μ.mono inter_subset_right
  obtain ⟨x, hx⟩ := isCompact_Icc.ultrafilter_le_nhds'
    (u.map (fun i => μ (s inter F i) / μ (F i))) (mem_map.1 mem_Icc)
  exact tendsto_nhds_limUnder (by use x; exact hx.2)

@[to_additive]

Depends on / 依赖: ENNReal, ENNReal.div_le_iff, div_le_iff, eventually_meas_ne_top, eventually_meas_ne_zero, filter_upwards, hfoel.eventually_meas_ne_top, hfoel.eventually_meas_ne_zero, inter_subset_right, isCompact_Icc, isCompact_Icc.ultrafilter_le_nhds, mem_Icc, mem_map, tendsto_nhds_limUnder, u.map, ultrafilter_le_nhds
-/
theorem tendsto_nhds_mean (hfoel : IsFoelner G μ u F) (s : Set X) :
    Tendsto (fun i => μ (s inter F i) / μ (F i)) u (𝓝 (mean μ u F s)) := by
  have mem_Icc : forallᶠ i in u, μ (s inter F i) / μ (F i) in Icc 0 1 := by
    filter_upwards [hfoel.eventually_meas_ne_zero, hfoel.eventually_meas_ne_top] with i hi hi'
    simpa [ENNReal.div_le_iff hi hi'] using μ.mono inter_subset_right
  obtain ⟨x, hx⟩ := isCompact_Icc.ultrafilter_le_nhds'
    (u.map (fun i => μ (s inter F i) / μ (F i))) (mem_map.1 mem_Icc)
  exact tendsto_nhds_limUnder (by use x; exact hx.2)

@[to_additive]
/--
theorem `mean_univ_eq_one` / 定理 `mean_univ_eq_one`

English:
theorem mean_univ_eq_one
  given: (hfoel : IsFoelner G μ u F)
  proof: by
  refine tendsto_nhds_unique_of_eventuallyEq (hfoel.tendsto_nhds_mean _) tendsto_const_nhds ?_
  filter_upwards [hfoel.eventually_meas_ne_zero, hfoel.eventually_meas_ne_top] with i hi hi'
  simp [ENNReal.div_self hi hi']

@[to_additive]

中文:
定理 mean_univ_eq_one
  条件: (hfoel : 是Foelner G μ u F)
  证明: by
  refine tendsto_nhds_unique_of_eventuallyEq (hfoel.tendsto_nhds_mean _) tendsto_const_nhds ?_
  filter_upwards [hfoel.eventually_meas_ne_zero, hfoel.eventually_meas_ne_top] with i hi hi'
  simp [ENNReal.div_self hi hi']

@[to_additive]

Depends on / 依赖: ENNReal, ENNReal.div_self, div_self, eventually_meas_ne_top, eventually_meas_ne_zero, filter_upwards, hfoel.eventually_meas_ne_top, hfoel.eventually_meas_ne_zero, hfoel.tendsto_nhds_mean, tendsto_const_nhds, tendsto_nhds_mean, tendsto_nhds_unique_of_eventuallyEq
-/
theorem mean_univ_eq_one (hfoel : IsFoelner G μ u F) :
    mean μ u F .univ = 1 := by
  refine tendsto_nhds_unique_of_eventuallyEq (hfoel.tendsto_nhds_mean _) tendsto_const_nhds ?_
  filter_upwards [hfoel.eventually_meas_ne_zero, hfoel.eventually_meas_ne_top] with i hi hi'
  simp [ENNReal.div_self hi hi']

@[to_additive]
/--
theorem `mean_union_eq_add_of_disjoint` / 定理 `mean_union_eq_add_of_disjoint`

English:
theorem mean_union_eq_add_of_disjoint
  statement: (hfoel : IsFoelner G μ u F)
  proof: by
  refine tendsto_nhds_unique_of_eventuallyEq
    (hfoel.tendsto_nhds_mean _) (hfoel.tendsto_nhds_mean _ |>.add <| hfoel.tendsto_nhds_mean _) ?_
  filter_upwards [hfoel.eventually_measurableSet] with i hi
  rw [union_inter_distrib_right]; rw [measure_union (hdisj.inter_left _ |>.inter_right _) (ht.inter hi)]; rw [ENNReal.add_div]

@[to_additive]

中文:
定理 mean_union_eq_add_of_disjoint
  结论: (hfoel : 是Foelner G μ u F)
  证明: by
  refine tendsto_nhds_unique_of_eventuallyEq
    (hfoel.tendsto_nhds_mean _) (hfoel.tendsto_nhds_mean _ |>.add <| hfoel.tendsto_nhds_mean _) ?_
  filter_upwards [hfoel.eventually_measurableSet] with i hi
  rw [union_inter_distrib_right]; rw [measure_union (hdisj.inter_left _ |>.inter_right _) (ht.inter hi)]; rw [ENNReal.add_div]

@[to_additive]

Depends on / 依赖: ENNReal, ENNReal.add_div, add_div, eventually_measurableSet, filter_upwards, hdisj.inter_left, hfoel.eventually_measurableSet, hfoel.tendsto_nhds_mean, ht.inter, inter_left, inter_right, measure_union, tendsto_nhds_mean, tendsto_nhds_unique_of_eventuallyEq, union_inter_distrib_right
-/
theorem mean_union_eq_add_of_disjoint (hfoel : IsFoelner G μ u F)
    (s t : Set X) (ht : MeasurableSet t) (hdisj : Disjoint s t) :
    mean μ u F (s union t) = mean μ u F s + mean μ u F t := by
  refine tendsto_nhds_unique_of_eventuallyEq
    (hfoel.tendsto_nhds_mean _) (hfoel.tendsto_nhds_mean _ |>.add <| hfoel.tendsto_nhds_mean _) ?_
  filter_upwards [hfoel.eventually_measurableSet] with i hi
  rw [union_inter_distrib_right]; rw [measure_union (hdisj.inter_left _ |>.inter_right _) (ht.inter hi)]; rw [ENNReal.add_div]

@[to_additive]
/--
theorem `tendsto_meas_smul_symmDiff_smul` / 定理 `tendsto_meas_smul_symmDiff_smul`

English:
theorem tendsto_meas_smul_symmDiff_smul
  statement: [SMulInvariantMeasure G X μ]
  proof: by
  simpa [← smul_smul] using hfoel.tendsto_meas_smul_symmDiff (h⁻¹ * g)

@[to_additive]

中文:
定理 tendsto_meas_smul_symmDiff_smul
  结论: [标量乘不变测度 G X μ]
  证明: by
  simpa [← smul_smul] using hfoel.tendsto_meas_smul_symmDiff (h⁻¹ * g)

@[to_additive]

Depends on / 依赖: hfoel.tendsto_meas_smul_symmDiff, smul_smul, tendsto_meas_smul_symmDiff
-/
theorem tendsto_meas_smul_symmDiff_smul [SMulInvariantMeasure G X μ]
    (hfoel : IsFoelner G μ u F) (g h : G) :
    Tendsto (fun i => μ ((g • F i) ∆ (h • F i)) / μ (F i)) u (𝓝 0) := by
  simpa [← smul_smul] using hfoel.tendsto_meas_smul_symmDiff (h⁻¹ * g)

@[to_additive]
/--
theorem `mean_smul_eq_mean_smul` / 定理 `mean_smul_eq_mean_smul`

English:
theorem mean_smul_eq_mean_smul
  statement: [SMulInvariantMeasure G X μ]
  proof: by
  suffices hle : forall g h, mean μ u F (g • s) <= mean μ u F (h • s) by
    exact le_antisymm (hle g h) (hle h g)
  intro g h
  rw [← add_zero <| mean μ u F (h • s)]
  refine le_of_tendsto_of_tendsto
    (hfoel.tendsto_nhds_mean (g • s))
    (hfoel.tendsto_nhds_mean (h • s) |>.add <| hfoel.tendsto_meas_smul_symmDiff_smul g⁻¹ h⁻¹) ?_
  filter_upwards [hfoel.eventually_meas_ne_zero] with i hi
  rw [← tsub_le_iff_left]; rw [← ENNReal.sub_div <| fun _ _ => hi]
  refine ENNReal.div_le_div_right (le_trans ?_ (measure_mono <| @inter_subset_right _ s _)) _
  simpa [inter_symmDiff_distrib_left, ← measure_inter_inv_smul] using le_measure_symmDiff

@[to_additive]

中文:
定理 mean_smul_eq_mean_smul
  结论: [标量乘不变测度 G X μ]
  证明: by
  suffices hle : forall g h, mean μ u F (g • s) <= mean μ u F (h • s) by
    exact le_antisymm (hle g h) (hle h g)
  intro g h
  rw [← add_zero <| mean μ u F (h • s)]
  refine le_of_tendsto_of_tendsto
    (hfoel.tendsto_nhds_mean (g • s))
    (hfoel.tendsto_nhds_mean (h • s) |>.add <| hfoel.tendsto_meas_smul_symmDiff_smul g⁻¹ h⁻¹) ?_
  filter_upwards [hfoel.eventually_meas_ne_zero] with i hi
  rw [← tsub_le_iff_left]; rw [← ENNReal.sub_div <| fun _ _ => hi]
  refine ENNReal.div_le_div_right (le_trans ?_ (measure_mono <| @inter_subset_right _ s _)) _
  simpa [inter_symmDiff_distrib_left, ← measure_inter_inv_smul] using le_measure_symmDiff

@[to_additive]

Depends on / 依赖: ENNReal, ENNReal.div_le_div_right, ENNReal.sub_div, add_zero, div_le_div_right, eventually_meas_ne_zero, filter_upwards, hfoel.eventually_meas_ne_zero, hfoel.tendsto_meas_smul_symmDiff_smul, hfoel.tendsto_nhds_mean, le_antisymm, le_of_tendsto_of_tendsto, le_trans, measure_mono, sub_div, tendsto_meas_smul_symmDiff_smul, tendsto_nhds_mean, tsub_le_iff_left
-/
theorem mean_smul_eq_mean_smul [SMulInvariantMeasure G X μ]
    (hfoel : IsFoelner G μ u F) (g h : G) (s : Set X) :
    mean μ u F (g • s) = mean μ u F (h • s) := by
  suffices hle : forall g h, mean μ u F (g • s) <= mean μ u F (h • s) by
    exact le_antisymm (hle g h) (hle h g)
  intro g h
  rw [← add_zero <| mean μ u F (h • s)]
  refine le_of_tendsto_of_tendsto
    (hfoel.tendsto_nhds_mean (g • s))
    (hfoel.tendsto_nhds_mean (h • s) |>.add <| hfoel.tendsto_meas_smul_symmDiff_smul g⁻¹ h⁻¹) ?_
  filter_upwards [hfoel.eventually_meas_ne_zero] with i hi
  rw [← tsub_le_iff_left]; rw [← ENNReal.sub_div <| fun _ _ => hi]
  refine ENNReal.div_le_div_right (le_trans ?_ (measure_mono <| @inter_subset_right _ s _)) _
  simpa [inter_symmDiff_distrib_left, ← measure_inter_inv_smul] using le_measure_symmDiff

@[to_additive]
/--
theorem `mean_smul_eq_mean` / 定理 `mean_smul_eq_mean`

English:
theorem mean_smul_eq_mean
  statement: [SMulInvariantMeasure G X μ]
  proof: by
  simpa using hfoel.mean_smul_eq_mean_smul g 1 s

中文:
定理 mean_smul_eq_mean
  结论: [标量乘不变测度 G X μ]
  证明: by
  simpa using hfoel.mean_smul_eq_mean_smul g 1 s

Depends on / 依赖: hfoel.mean_smul_eq_mean_smul, mean_smul_eq_mean_smul
-/
theorem mean_smul_eq_mean [SMulInvariantMeasure G X μ]
    (hfoel : IsFoelner G μ u F) (g : G) (s : Set X) :
    mean μ u F (g • s) = mean μ u F s := by
  simpa using hfoel.mean_smul_eq_mean_smul g 1 s

/-- If there exists a non-trivial Følner filter with respect to some group `G` acting on a measure
    space `X`, then there exists a `G`-invariant finitely additive probability measure on `X`. -/
@[to_additive
/-- If there exists a non-trivial Følner filter with respect to some additive group
    `G` acting on a measure space `X`, then there exists a `G`-invariant finitely additive
    probability measure on `X`. -/]
/--
theorem `amenable` / 定理 `amenable`

English:
theorem amenable
  given: [SMulInvariantMeasure G X μ] [NeBot l] (hfoel : IsFoelner G μ l F)
  proof: by
  use mean μ (Ultrafilter.of l) F
  refine ⟨?_, ?_, ?_⟩
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_univ_eq_one
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_union_eq_add_of_disjoint
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_smul_eq_mean

中文:
定理 amenable
  条件: [标量乘不变测度 G X μ] [NeBot l] (hfoel : 是Foelner G μ l F)
  证明: by
  use mean μ (Ultrafilter.of l) F
  refine ⟨?_, ?_, ?_⟩
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_univ_eq_one
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_union_eq_add_of_disjoint
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_smul_eq_mean

Depends on / 依赖: Ultrafilter, Ultrafilter.of, Ultrafilter.of_le, hfoel.mono, mean_smul_eq_mean, mean_union_eq_add_of_disjoint, mean_univ_eq_one, of_le
-/
theorem amenable [SMulInvariantMeasure G X μ] [NeBot l] (hfoel : IsFoelner G μ l F) :
    exists m : Set X -> Real>=0∞, m .univ = 1 ∧
      (forall s t, MeasurableSet t -> Disjoint s t -> m (s union t) = m s + m t) ∧
        forall (g : G) (s : Set X), m (g • s) = m s := by
  use mean μ (Ultrafilter.of l) F
  refine ⟨?_, ?_, ?_⟩
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_univ_eq_one
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_union_eq_add_of_disjoint
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_smul_eq_mean

end IsFoelner

variable (G μ) in
/-- The maximal Følner filter with respect to some group `G` acting on a
    measure space `X` is the pullback of `𝓝 0` along the map `s ↦ μ (g • s) / μ s`
    on measurable sets of finite non-zero measure. -/
@[to_additive maxAddFoelner
/-- The maximal Følner filter with respect to some additive group `G` acting
    on a measure space `X` is the pullback of `𝓝 0` along the map `s ↦ μ (g +ᵥ s) / μ s`
    on measurable sets of finite non-zero measure. -/]
/--
Definition of `maxFoelner` / `maxFoelner` 的定义

English:
definition maxFoelner
  signature: : Filter (Set X)
  body: 𝓟 {s : Set X | MeasurableSet s ∧ μ s != 0 ∧ μ s != ∞} ⊓
  ⨅ (g : G), comap (fun s => μ ((g • s) ∆ s) / μ s) (𝓝 0)

中文:
定义 maxFoelner
  签名: : 滤子 (集合 X)
  定义体: 𝓟 {s : Set X | MeasurableSet s ∧ μ s != 0 ∧ μ s != ∞} ⊓
  ⨅ (g : G), comap (fun s => μ ((g • s) ∆ s) / μ s) (𝓝 0)

Depends on / 依赖: MeasurableSet
-/
noncomputable def maxFoelner : Filter (Set X) :=
  𝓟 {s : Set X | MeasurableSet s ∧ μ s != 0 ∧ μ s != ∞} ⊓
  ⨅ (g : G), comap (fun s => μ ((g • s) ∆ s) / μ s) (𝓝 0)

variable (l F) in
@[to_additive isAddFoelner_iff_tendsto]
/--
theorem `isFoelner_iff_tendsto` / 定理 `isFoelner_iff_tendsto`

English:
theorem isFoelner_iff_tendsto
  statement: IsFoelner G μ l F ↔ Tendsto F l (maxFoelner G μ)
  proof: by
  simp [maxFoelner, tendsto_inf, tendsto_iInf, isFoelner_iff, Function.comp_def, and_assoc]

中文:
定理 isFoelner_iff_tendsto
  结论: 是Foelner G μ l F ↔ 收敛 F l (maxFoelner G μ)
  证明: by
  simp [maxFoelner, tendsto_inf, tendsto_iInf, isFoelner_iff, Function.comp_def, and_assoc]

Depends on / 依赖: Function, Function.comp_def, and_assoc, comp_def, isFoelner_iff, maxFoelner, tendsto_iInf, tendsto_inf
-/
theorem isFoelner_iff_tendsto : IsFoelner G μ l F ↔ Tendsto F l (maxFoelner G μ) := by
  simp [maxFoelner, tendsto_inf, tendsto_iInf, isFoelner_iff, Function.comp_def, and_assoc]

variable (G μ) in
@[to_additive isAddFoelner_maxAddFoelner]
/--
theorem `isFoelner_maxFoelner` / 定理 `isFoelner_maxFoelner`

English:
theorem isFoelner_maxFoelner
  statement: IsFoelner G μ (maxFoelner G μ) id
  proof: .2 @tendsto_id _ (maxFoelner G μ) isFoelner_iff_tendsto _ _

@[to_additive amenable_of_maxAddFoelner_neBot]

中文:
定理 isFoelner_maxFoelner
  结论: 是Foelner G μ (maxFoelner G μ) id
  证明: .2 @tendsto_id _ (maxFoelner G μ) isFoelner_iff_tendsto _ _

@[to_additive amenable_of_maxAddFoelner_neBot]

Depends on / 依赖: isFoelner_iff_tendsto, maxFoelner, tendsto_id
-/
theorem isFoelner_maxFoelner : IsFoelner G μ (maxFoelner G μ) id :=
.2 @tendsto_id _ (maxFoelner G μ) isFoelner_iff_tendsto _ _

@[to_additive amenable_of_maxAddFoelner_neBot]
/--
theorem `amenable_of_maxFoelner_neBot` / 定理 `amenable_of_maxFoelner_neBot`

English:
theorem amenable_of_maxFoelner_neBot
  given: [SMulInvariantMeasure G X μ] [NeBot (maxFoelner G μ)]
  proof: IsFoelner.amenable isFoelner_maxFoelner G μ

中文:
定理 amenable_of_maxFoelner_neBot
  条件: [标量乘不变测度 G X μ] [NeBot (maxFoelner G μ)]
  证明: IsFoelner.amenable isFoelner_maxFoelner G μ

Depends on / 依赖: IsFoelner, IsFoelner.amenable, amenable, isFoelner_maxFoelner
-/
theorem amenable_of_maxFoelner_neBot [SMulInvariantMeasure G X μ] [NeBot (maxFoelner G μ)] :
    exists m : Set X -> Real>=0∞, m .univ = 1 ∧
      (forall s t, MeasurableSet t -> Disjoint s t -> m (s union t) = m s + m t) ∧
        forall (g : G) (s : Set X), m (g • s) = m s :=
IsFoelner.amenable isFoelner_maxFoelner G μ
