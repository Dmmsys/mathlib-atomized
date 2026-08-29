/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Jensen's inequality for integrals

In this file we prove several forms of Jensen's inequality for integrals.

- for convex sets: `Convex.average_mem`, `Convex.set_average_mem`, `Convex.integral_mem`;

- for convex functions: `ConvexOn.average_mem_epigraph`, `ConvexOn.map_average_le`,
  `ConvexOn.set_average_mem_epigraph`, `ConvexOn.map_set_average_le`, `ConvexOn.map_integral_le`;

- for strictly convex sets: `StrictConvex.ae_eq_const_or_average_mem_interior`;

- for a closed ball in a strictly convex normed space:
  `ae_eq_const_or_norm_integral_lt_of_norm_le_const`;

- for strictly convex functions: `StrictConvexOn.ae_eq_const_or_map_average_lt`.

## TODO

- Use a typeclass for strict convexity of a closed ball.

## Tags

convex, integral, center mass, average value, Jensen's inequality
-/

public section


open MeasureTheory MeasureTheory.Measure Metric Set Filter TopologicalSpace Function

open scoped Topology ENNReal Convex

variable {α E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace Real E]
  [CompleteSpace E] {μ : Measure α} {s : Set E} {t : Set α} {f : α -> E} {g : E -> Real} {C : Real}

/-!
### Non-strict Jensen's inequality
-/


/--
theorem `Convex.integral_mem` / 定理 `Convex.integral_mem`

English:
theorem Convex.integral_mem
  statement: [IsProbabilityMeasure μ] (hs : Convex Real s) (hsc : IsClosed s)
  proof: by
  borelize E
  rcases hfi.aestronglyMeasurable with ⟨g, hgm, hfg⟩
  have : SeparableSpace (range g inter s : Set E) :=
    (hgm.isSeparable_range.mono inter_subset_left).separableSpace
  obtain ⟨y₀, h₀⟩ : (range g inter s).Nonempty := by
    rcases (hf.and hfg).exists with ⟨x₀, h₀⟩
    exact ⟨f x

中文:
定理 Convex.integral_mem
  结论: [IsProbabilityMeasure μ] (hs : Convex 实数 s) (hsc : IsClosed s)
  证明: by
  borelize E
  rcases hfi.aestronglyMeasurable with ⟨g, hgm, hfg⟩
  have : SeparableSpace (range g inter s : Set E) :=
    (hgm.isSeparable_range.mono inter_subset_left).separableSpace
  obtain ⟨y₀, h₀⟩ : (range g inter s).Nonempty := by
    rcases (hf.and hfg).exists with ⟨x₀, h₀⟩
    exact ⟨f x

Depends on / 依赖: Nonempty, SeparableSpace, aestronglyMeasurable, borelize, closure, filter_upwards, hf.and, hfg.rw, hfi.aestronglyMeasurable, hgm.isSeparable_range.mono, integrable_congr, integral_congr_ae, inter_subset_left, isSeparable_range, mem_range_self, separableSpace
-/
theorem Convex.integral_mem [IsProbabilityMeasure μ] (hs : Convex Real s) (hsc : IsClosed s)
    (hf : forallᵐ x ∂μ, f x in s) (hfi : Integrable f μ) : (∫ x, f x ∂μ) in s := by
  borelize E
  rcases hfi.aestronglyMeasurable with ⟨g, hgm, hfg⟩
  have : SeparableSpace (range g inter s : Set E) :=
    (hgm.isSeparable_range.mono inter_subset_left).separableSpace
  obtain ⟨y₀, h₀⟩ : (range g inter s).Nonempty := by
    rcases (hf.and hfg).exists with ⟨x₀, h₀⟩
    exact ⟨f x₀, by simp only [h₀.2, mem_range_self], h₀.1⟩
  rw [integral_congr_ae hfg]; rw [integrable_congr hfg] at hfi
  have hg : forallᵐ x ∂μ, g x in closure (range g inter s) := by
    filter_upwards [hfg.rw (fun _ y => y in s) hf] with x hx
    apply subset_closure
    exact ⟨mem_range_self _, hx⟩
  set G : Nat -> SimpleFunc α E := SimpleFunc.approxOn _ hgm.measurable (range g inter s) y₀ h₀
  have : Tendsto (fun n => (G n).integral μ) atTop (𝓝 <| ∫ x, g x ∂μ) :=
    tendsto_integral_approxOn_of_measurable hfi _ hg _ (integrable_const _)
  refine hsc.mem_of_tendsto this (Eventually.of_forall fun n => hs.sum_mem ?_ ?_ ?_)
  · exact fun _ _ => ENNReal.toReal_nonneg
  · simp_rw [measureReal_def]
    rw [← ENNReal.toReal_sum]; rw [(G n).sum_range_measure_preimage_singleton]; rw [measure_univ]; rw [ENNReal.toReal_one]
    finiteness
  · simp only [SimpleFunc.mem_range, forall_mem_range]
    intro x
    apply (range g).inter_subset_right
    exact SimpleFunc.approxOn_mem hgm.measurable h₀ _ _

/--
theorem `Convex.average_mem` / 定理 `Convex.average_mem`

English:
theorem Convex.average_mem
  statement: [IsFiniteMeasure μ] [NeZero μ] (hs : Convex Real s) (hsc : IsClosed s)
  proof: hs.integral_mem hsc (ae_mono' smul_absolutelyContinuous hfs) hfi.to_average

中文:
定理 Convex.average_mem
  结论: [IsFiniteMeasure μ] [NeZero μ] (hs : Convex 实数 s) (hsc : IsClosed s)
  证明: hs.integral_mem hsc (ae_mono' smul_absolutelyContinuous hfs) hfi.to_average

Depends on / 依赖: ae_mono, hfi.to_average, hs.integral_mem, integral_mem, smul_absolutelyContinuous, to_average
-/
theorem Convex.average_mem [IsFiniteMeasure μ] [NeZero μ] (hs : Convex Real s) (hsc : IsClosed s)
    (hfs : forallᵐ x ∂μ, f x in s) (hfi : Integrable f μ) : (⨍ x, f x ∂μ) in s :=
  hs.integral_mem hsc (ae_mono' smul_absolutelyContinuous hfs) hfi.to_average

/--
theorem `Convex.set_average_mem` / 定理 `Convex.set_average_mem`

English:
theorem Convex.set_average_mem
  statement: (hs : Convex Real s) (hsc : IsClosed s) (h0 : μ t != 0) (ht : μ t != ∞)
  proof: have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hs.average_mem hsc hfs hfi

中文:
定理 Convex.set_average_mem
  结论: (hs : Convex 实数 s) (hsc : IsClosed s) (h0 : μ t != 0) (ht : μ t != ∞)
  证明: have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hs.average_mem hsc hfs hfi

Depends on / 依赖: Fact.mk, NeZero, NeZero.mk, average_mem, hs.average_mem, ht.lt_top, lt_top
-/
theorem Convex.set_average_mem (hs : Convex Real s) (hsc : IsClosed s) (h0 : μ t != 0) (ht : μ t != ∞)
    (hfs : forallᵐ x ∂μ.restrict t, f x in s) (hfi : IntegrableOn f t μ) : (⨍ x in t, f x ∂μ) in s :=
  have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hs.average_mem hsc hfs hfi

/--
theorem `Convex.set_average_mem_closure` / 定理 `Convex.set_average_mem_closure`

English:
theorem Convex.set_average_mem_closure
  statement: (hs : Convex Real s) (h0 : μ t != 0) (ht : μ t != ∞)
  proof: hs.closure.set_average_mem isClosed_closure h0 ht (hfs.mono fun _ hx => subset_closure hx) hfi

中文:
定理 Convex.set_average_mem_closure
  结论: (hs : Convex 实数 s) (h0 : μ t != 0) (ht : μ t != ∞)
  证明: hs.closure.set_average_mem isClosed_closure h0 ht (hfs.mono fun _ hx => subset_closure hx) hfi

Depends on / 依赖: closure, hfs.mono, hs.closure.set_average_mem, isClosed_closure, set_average_mem, subset_closure
-/
theorem Convex.set_average_mem_closure (hs : Convex Real s) (h0 : μ t != 0) (ht : μ t != ∞)
    (hfs : forallᵐ x ∂μ.restrict t, f x in s) (hfi : IntegrableOn f t μ) :
    (⨍ x in t, f x ∂μ) in closure s :=
  hs.closure.set_average_mem isClosed_closure h0 ht (hfs.mono fun _ hx => subset_closure hx) hfi

/--
theorem `ConvexOn.average_mem_epigraph` / 定理 `ConvexOn.average_mem_epigraph`

English:
theorem ConvexOn.average_mem_epigraph
  statement: [IsFiniteMeasure μ] [NeZero μ] (hg : ConvexOn Real s g)
  proof: by
  have ht_mem : forallᵐ x ∂μ, (f x, g (f x)) in {p : E × Real | p.1 in s ∧ g p.1 <= p.2} :=
    hfs.mono fun x hx => ⟨hx, le_rfl⟩
  exact average_pair hfi hgi ▸
    hg.convex_epigraph.average_mem (hsc.epigraph hgc) ht_mem (hfi.prodMk hgi)

中文:
定理 ConvexOn.average_mem_epigraph
  结论: [IsFiniteMeasure μ] [NeZero μ] (hg : ConvexOn 实数 s g)
  证明: by
  have ht_mem : forallᵐ x ∂μ, (f x, g (f x)) in {p : E × Real | p.1 in s ∧ g p.1 <= p.2} :=
    hfs.mono fun x hx => ⟨hx, le_rfl⟩
  exact average_pair hfi hgi ▸
    hg.convex_epigraph.average_mem (hsc.epigraph hgc) ht_mem (hfi.prodMk hgi)

Depends on / 依赖: average_mem, average_pair, convex_epigraph, epigraph, hfi.prodMk, hfs.mono, hg.convex_epigraph.average_mem, hsc.epigraph, ht_mem, le_rfl, prodMk
-/
theorem ConvexOn.average_mem_epigraph [IsFiniteMeasure μ] [NeZero μ] (hg : ConvexOn Real s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : forallᵐ x ∂μ, f x in s)
    (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ) in {p : E × Real | p.1 in s ∧ g p.1 <= p.2} := by
  have ht_mem : forallᵐ x ∂μ, (f x, g (f x)) in {p : E × Real | p.1 in s ∧ g p.1 <= p.2} :=
    hfs.mono fun x hx => ⟨hx, le_rfl⟩
  exact average_pair hfi hgi ▸
    hg.convex_epigraph.average_mem (hsc.epigraph hgc) ht_mem (hfi.prodMk hgi)

/--
theorem `ConcaveOn.average_mem_hypograph` / 定理 `ConcaveOn.average_mem_hypograph`

English:
theorem ConcaveOn.average_mem_hypograph
  statement: [IsFiniteMeasure μ] [NeZero μ] (hg : ConcaveOn Real s g)
  proof: by
  simpa only [mem_ofPred_eq, Pi.neg_apply, average_neg, neg_le_neg_iff] using
    hg.neg.average_mem_epigraph hgc.neg hsc hfs hfi hgi.neg

中文:
定理 ConcaveOn.average_mem_hypograph
  结论: [IsFiniteMeasure μ] [NeZero μ] (hg : ConcaveOn 实数 s g)
  证明: by
  simpa only [mem_ofPred_eq, Pi.neg_apply, average_neg, neg_le_neg_iff] using
    hg.neg.average_mem_epigraph hgc.neg hsc hfs hfi hgi.neg

Depends on / 依赖: Pi.neg_apply, average_mem_epigraph, average_neg, hg.neg.average_mem_epigraph, hgc.neg, hgi.neg, mem_ofPred_eq, neg_apply, neg_le_neg_iff
-/
theorem ConcaveOn.average_mem_hypograph [IsFiniteMeasure μ] [NeZero μ] (hg : ConcaveOn Real s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : forallᵐ x ∂μ, f x in s)
    (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ) in {p : E × Real | p.1 in s ∧ p.2 <= g p.1} := by
  simpa only [mem_ofPred_eq, Pi.neg_apply, average_neg, neg_le_neg_iff] using
    hg.neg.average_mem_epigraph hgc.neg hsc hfs hfi hgi.neg

/--
theorem `ConvexOn.map_average_le` / 定理 `ConvexOn.map_average_le`

English:
theorem ConvexOn.map_average_le
  statement: [IsFiniteMeasure μ] [NeZero μ]
  proof: (hg.average_mem_epigraph hgc hsc hfs hfi hgi).2

中文:
定理 ConvexOn.map_average_le
  结论: [IsFiniteMeasure μ] [NeZero μ]
  证明: (hg.average_mem_epigraph hgc hsc hfs hfi hgi).2

Depends on / 依赖: average_mem_epigraph, hg.average_mem_epigraph
-/
theorem ConvexOn.map_average_le [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConvexOn Real s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : forallᵐ x ∂μ, f x in s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    g (⨍ x, f x ∂μ) <= ⨍ x, g (f x) ∂μ :=
  (hg.average_mem_epigraph hgc hsc hfs hfi hgi).2

/--
theorem `ConcaveOn.le_map_average` / 定理 `ConcaveOn.le_map_average`

English:
theorem ConcaveOn.le_map_average
  statement: [IsFiniteMeasure μ] [NeZero μ]
  proof: (hg.average_mem_hypograph hgc hsc hfs hfi hgi).2

中文:
定理 ConcaveOn.le_map_average
  结论: [IsFiniteMeasure μ] [NeZero μ]
  证明: (hg.average_mem_hypograph hgc hsc hfs hfi hgi).2

Depends on / 依赖: average_mem_hypograph, hg.average_mem_hypograph
-/
theorem ConcaveOn.le_map_average [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConcaveOn Real s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : forallᵐ x ∂μ, f x in s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, g (f x) ∂μ) <= g (⨍ x, f x ∂μ) :=
  (hg.average_mem_hypograph hgc hsc hfs hfi hgi).2

/--
theorem `ConvexOn.set_average_mem_epigraph` / 定理 `ConvexOn.set_average_mem_epigraph`

English:
theorem ConvexOn.set_average_mem_epigraph
  statement: (hg : ConvexOn Real s g) (hgc : ContinuousOn g s)
  proof: have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hg.average_mem_epigraph hgc hsc hfs hfi hgi

中文:
定理 ConvexOn.set_average_mem_epigraph
  结论: (hg : ConvexOn 实数 s g) (hgc : ContinuousOn g s)
  证明: have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hg.average_mem_epigraph hgc hsc hfs hfi hgi

Depends on / 依赖: Fact.mk, NeZero, NeZero.mk, average_mem_epigraph, hg.average_mem_epigraph, ht.lt_top, lt_top
-/
theorem ConvexOn.set_average_mem_epigraph (hg : ConvexOn Real s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t != 0) (ht : μ t != ∞) (hfs : forallᵐ x ∂μ.restrict t, f x in s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, f x ∂μ, ⨍ x in t, g (f x) ∂μ) in {p : E × Real | p.1 in s ∧ g p.1 <= p.2} :=
  have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hg.average_mem_epigraph hgc hsc hfs hfi hgi

/--
theorem `ConcaveOn.set_average_mem_hypograph` / 定理 `ConcaveOn.set_average_mem_hypograph`

English:
theorem ConcaveOn.set_average_mem_hypograph
  statement: (hg : ConcaveOn Real s g) (hgc : ContinuousOn g s)
  proof: by
  simpa only [mem_ofPred_eq, Pi.neg_apply, average_neg, neg_le_neg_iff] using
    hg.neg.set_average_mem_epigraph hgc.neg hsc h0 ht hfs hfi hgi.neg

中文:
定理 ConcaveOn.set_average_mem_hypograph
  结论: (hg : ConcaveOn 实数 s g) (hgc : ContinuousOn g s)
  证明: by
  simpa only [mem_ofPred_eq, Pi.neg_apply, average_neg, neg_le_neg_iff] using
    hg.neg.set_average_mem_epigraph hgc.neg hsc h0 ht hfs hfi hgi.neg

Depends on / 依赖: Pi.neg_apply, average_neg, hg.neg.set_average_mem_epigraph, hgc.neg, hgi.neg, mem_ofPred_eq, neg_apply, neg_le_neg_iff, set_average_mem_epigraph
-/
theorem ConcaveOn.set_average_mem_hypograph (hg : ConcaveOn Real s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t != 0) (ht : μ t != ∞) (hfs : forallᵐ x ∂μ.restrict t, f x in s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, f x ∂μ, ⨍ x in t, g (f x) ∂μ) in {p : E × Real | p.1 in s ∧ p.2 <= g p.1} := by
  simpa only [mem_ofPred_eq, Pi.neg_apply, average_neg, neg_le_neg_iff] using
    hg.neg.set_average_mem_epigraph hgc.neg hsc h0 ht hfs hfi hgi.neg

/--
theorem `ConvexOn.map_set_average_le` / 定理 `ConvexOn.map_set_average_le`

English:
theorem ConvexOn.map_set_average_le
  statement: (hg : ConvexOn Real s g) (hgc : ContinuousOn g s)
  proof: (hg.set_average_mem_epigraph hgc hsc h0 ht hfs hfi hgi).2

中文:
定理 ConvexOn.map_set_average_le
  结论: (hg : ConvexOn 实数 s g) (hgc : ContinuousOn g s)
  证明: (hg.set_average_mem_epigraph hgc hsc h0 ht hfs hfi hgi).2

Depends on / 依赖: hg.set_average_mem_epigraph, set_average_mem_epigraph
-/
theorem ConvexOn.map_set_average_le (hg : ConvexOn Real s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t != 0) (ht : μ t != ∞) (hfs : forallᵐ x ∂μ.restrict t, f x in s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    g (⨍ x in t, f x ∂μ) <= ⨍ x in t, g (f x) ∂μ :=
  (hg.set_average_mem_epigraph hgc hsc h0 ht hfs hfi hgi).2

/--
theorem `ConcaveOn.le_map_set_average` / 定理 `ConcaveOn.le_map_set_average`

English:
theorem ConcaveOn.le_map_set_average
  statement: (hg : ConcaveOn Real s g) (hgc : ContinuousOn g s)
  proof: (hg.set_average_mem_hypograph hgc hsc h0 ht hfs hfi hgi).2

中文:
定理 ConcaveOn.le_map_set_average
  结论: (hg : ConcaveOn 实数 s g) (hgc : ContinuousOn g s)
  证明: (hg.set_average_mem_hypograph hgc hsc h0 ht hfs hfi hgi).2

Depends on / 依赖: hg.set_average_mem_hypograph, set_average_mem_hypograph
-/
theorem ConcaveOn.le_map_set_average (hg : ConcaveOn Real s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t != 0) (ht : μ t != ∞) (hfs : forallᵐ x ∂μ.restrict t, f x in s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, g (f x) ∂μ) <= g (⨍ x in t, f x ∂μ) :=
  (hg.set_average_mem_hypograph hgc hsc h0 ht hfs hfi hgi).2

/--
theorem `ConvexOn.map_integral_le` / 定理 `ConvexOn.map_integral_le`

English:
theorem ConvexOn.map_integral_le
  statement: [IsProbabilityMeasure μ] (hg : ConvexOn Real s g)
  proof: by
  simpa only [average_eq_integral] using hg.map_average_le hgc hsc hfs hfi hgi

中文:
定理 ConvexOn.map_integral_le
  结论: [IsProbabilityMeasure μ] (hg : ConvexOn 实数 s g)
  证明: by
  simpa only [average_eq_integral] using hg.map_average_le hgc hsc hfs hfi hgi

Depends on / 依赖: average_eq_integral, hg.map_average_le, map_average_le
-/
theorem ConvexOn.map_integral_le [IsProbabilityMeasure μ] (hg : ConvexOn Real s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : forallᵐ x ∂μ, f x in s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) : g (∫ x, f x ∂μ) <= ∫ x, g (f x) ∂μ := by
  simpa only [average_eq_integral] using hg.map_average_le hgc hsc hfs hfi hgi

/--
theorem `ConcaveOn.le_map_integral` / 定理 `ConcaveOn.le_map_integral`

English:
theorem ConcaveOn.le_map_integral
  statement: [IsProbabilityMeasure μ] (hg : ConcaveOn Real s g)
  proof: by
  simpa only [average_eq_integral] using hg.le_map_average hgc hsc hfs hfi hgi

中文:
定理 ConcaveOn.le_map_integral
  结论: [IsProbabilityMeasure μ] (hg : ConcaveOn 实数 s g)
  证明: by
  simpa only [average_eq_integral] using hg.le_map_average hgc hsc hfs hfi hgi

Depends on / 依赖: average_eq_integral, hg.le_map_average, le_map_average
-/
theorem ConcaveOn.le_map_integral [IsProbabilityMeasure μ] (hg : ConcaveOn Real s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : forallᵐ x ∂μ, f x in s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) : (∫ x, g (f x) ∂μ) <= g (∫ x, f x ∂μ) := by
  simpa only [average_eq_integral] using hg.le_map_average hgc hsc hfs hfi hgi

/-!
### Strict Jensen's inequality
-/


/--
theorem `ae_eq_const_or_exists_average_ne_compl` / 定理 `ae_eq_const_or_exists_average_ne_compl`

English:
theorem ae_eq_const_or_exists_average_ne_compl
  given: [IsFiniteMeasure μ] (hfi : Integrable f μ)
  proof: by
  refine or_iff_not_imp_right.mpr fun H => ?_; push Not at H
  refine hfi.ae_eq_of_forall_setIntegral_eq _ _ (integrable_const _) fun t ht ht' => ?_; clear ht'
  simp only [const_apply, setIntegral_const]
  by_cases h₀ : μ t = 0
  · rw [restrict_eq_zero.2 h₀, integral_zero_measure, measureReal_de

中文:
定理 ae_eq_const_or_exists_average_ne_compl
  条件: [IsFiniteMeasure μ] (hfi : 整数egrable f μ)
  证明: by
  refine or_iff_not_imp_right.mpr fun H => ?_; push Not at H
  refine hfi.ae_eq_of_forall_setIntegral_eq _ _ (integrable_const _) fun t ht ht' => ?_; clear ht'
  simp only [const_apply, setIntegral_const]
  by_cases h₀ : μ t = 0
  · rw [restrict_eq_zero.2 h₀, integral_zero_measure, measureReal_de

Depends on / 依赖: ENNReal, ENNReal.toReal_zero, ae_eq_of_forall_setIntegral_eq, ae_eq_univ, average_m, const_apply, hfi.ae_eq_of_forall_setIntegral_eq, integrable_const, integral_zero_measure, measureReal_congr, measureReal_def, measure_smul_average, or_iff_not_imp_right, or_iff_not_imp_right.mpr, restrict_congr_set, restrict_eq_zero, restrict_univ, setIntegral_const, toReal_zero, zero_smul
-/
theorem ae_eq_const_or_exists_average_ne_compl [IsFiniteMeasure μ] (hfi : Integrable f μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨
      exists t, MeasurableSet t ∧ μ t != 0 ∧ μ tᶜ != 0 ∧ (⨍ x in t, f x ∂μ) != ⨍ x in tᶜ, f x ∂μ := by
  refine or_iff_not_imp_right.mpr fun H => ?_; push Not at H
  refine hfi.ae_eq_of_forall_setIntegral_eq _ _ (integrable_const _) fun t ht ht' => ?_; clear ht'
  simp only [const_apply, setIntegral_const]
  by_cases h₀ : μ t = 0
  · rw [restrict_eq_zero.2 h₀, integral_zero_measure, measureReal_def, h₀,
      ENNReal.toReal_zero, zero_smul]
  by_cases h₀' : μ tᶜ = 0
  · rw [← ae_eq_univ] at h₀'
    rw [restrict_congr_set h₀']; rw [restrict_univ]; rw [measureReal_congr h₀']; rw [measure_smul_average]
  have := average_mem_openSegment_compl_self ht.nullMeasurableSet h₀ h₀' hfi
  rw [← H t ht h₀ h₀']; rw [openSegment_same]; rw [mem_singleton_iff] at this
  rw [this]; rw [measure_smul_setAverage _ (by finiteness)]

/--
theorem `Convex.average_mem_interior_of_set` / 定理 `Convex.average_mem_interior_of_set`

English:
theorem Convex.average_mem_interior_of_set
  statement: [IsFiniteMeasure μ] (hs : Convex Real s) (h0 : μ t != 0)
  proof: by
  rw [← measure_toMeasurable] at h0; rw [← restrict_toMeasurable (by finiteness)] at ht
  by_cases h0' : μ (toMeasurable μ t)ᶜ = 0
  · rw [← ae_eq_univ] at h0'
    rwa [restrict_congr_set h0', restrict_univ] at ht
  exact hs.openSegment_interior_closure_subset_interior ht
      (hs.set_average_me

中文:
定理 Convex.average_mem_interior_of_set
  结论: [IsFiniteMeasure μ] (hs : Convex 实数 s) (h0 : μ t != 0)
  证明: by
  rw [← measure_toMeasurable] at h0; rw [← restrict_toMeasurable (by finiteness)] at ht
  by_cases h0' : μ (toMeasurable μ t)ᶜ = 0
  · rw [← ae_eq_univ] at h0'
    rwa [restrict_congr_set h0', restrict_univ] at ht
  exact hs.openSegment_interior_closure_subset_interior ht
      (hs.set_average_me

Depends on / 依赖: ae_eq_univ, ae_restrict_of_ae, average_mem_openSegment_compl_self, finiteness, hfi.integrableOn, hs.openSegment_interior_closure_subset_interior, hs.set_average_mem_closure, integrableOn, measurableSet_toMeasurable, measure_toMeasurable, nullMeasurableSet, openSegment_interior_closure_subset_interior, restrict_congr_set, restrict_toMeasurable, restrict_univ, set_average_mem_closure, toMeasurable
-/
theorem Convex.average_mem_interior_of_set [IsFiniteMeasure μ] (hs : Convex Real s) (h0 : μ t != 0)
    (hfs : forallᵐ x ∂μ, f x in s) (hfi : Integrable f μ) (ht : (⨍ x in t, f x ∂μ) in interior s) :
    (⨍ x, f x ∂μ) in interior s := by
  rw [← measure_toMeasurable] at h0; rw [← restrict_toMeasurable (by finiteness)] at ht
  by_cases h0' : μ (toMeasurable μ t)ᶜ = 0
  · rw [← ae_eq_univ] at h0'
    rwa [restrict_congr_set h0', restrict_univ] at ht
  exact hs.openSegment_interior_closure_subset_interior ht
      (hs.set_average_mem_closure h0' (by finiteness) (ae_restrict_of_ae hfs) hfi.integrableOn)
      (average_mem_openSegment_compl_self (measurableSet_toMeasurable μ t).nullMeasurableSet h0
        h0' hfi)

/--
theorem `StrictConvex.ae_eq_const_or_average_mem_interior` / 定理 `StrictConvex.ae_eq_const_or_average_mem_interior`

English:
theorem StrictConvex.ae_eq_const_or_average_mem_interior
  statement: [IsFiniteMeasure μ] (hs : StrictConvex Real s)
  proof: by
  have : forall {t}, μ t != 0 -> (⨍ x in t, f x ∂μ) in s := fun ht =>
    hs.convex.set_average_mem hsc ht (by finiteness) (ae_restrict_of_ae hfs) hfi.integrableOn
  refine (ae_eq_const_or_exists_average_ne_compl hfi).imp_right ?_
  rintro ⟨t, hm, h₀, h₀', hne⟩
  exact
    hs.openSegment_subset (

中文:
定理 StrictConvex.ae_eq_const_or_average_mem_interior
  结论: [IsFiniteMeasure μ] (hs : StrictConvex 实数 s)
  证明: by
  have : forall {t}, μ t != 0 -> (⨍ x in t, f x ∂μ) in s := fun ht =>
    hs.convex.set_average_mem hsc ht (by finiteness) (ae_restrict_of_ae hfs) hfi.integrableOn
  refine (ae_eq_const_or_exists_average_ne_compl hfi).imp_right ?_
  rintro ⟨t, hm, h₀, h₀', hne⟩
  exact
    hs.openSegment_subset (

Depends on / 依赖: ae_eq_const_or_exists_average_ne_compl, ae_restrict_of_ae, average_mem_openSegment_compl_self, convex, finiteness, hfi.integrableOn, hm.nullMeasurableSet, hs.convex.set_average_mem, hs.openSegment_subset, imp_right, integrableOn, nullMeasurableSet, openSegment_subset, set_average_mem
-/
theorem StrictConvex.ae_eq_const_or_average_mem_interior [IsFiniteMeasure μ] (hs : StrictConvex Real s)
    (hsc : IsClosed s) (hfs : forallᵐ x ∂μ, f x in s) (hfi : Integrable f μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ (⨍ x, f x ∂μ) in interior s := by
  have : forall {t}, μ t != 0 -> (⨍ x in t, f x ∂μ) in s := fun ht =>
    hs.convex.set_average_mem hsc ht (by finiteness) (ae_restrict_of_ae hfs) hfi.integrableOn
  refine (ae_eq_const_or_exists_average_ne_compl hfi).imp_right ?_
  rintro ⟨t, hm, h₀, h₀', hne⟩
  exact
    hs.openSegment_subset (this h₀) (this h₀') hne
      (average_mem_openSegment_compl_self hm.nullMeasurableSet h₀ h₀' hfi)

/--
theorem `StrictConvexOn.ae_eq_const_or_map_average_lt` / 定理 `StrictConvexOn.ae_eq_const_or_map_average_lt`

English:
theorem StrictConvexOn.ae_eq_const_or_map_average_lt
  statement: [IsFiniteMeasure μ] (hg : StrictConvexOn Real s g)
  proof: by
  have : forall {t}, μ t != 0 -> (⨍ x in t, f x ∂μ) in s ∧ g (⨍ x in t, f x ∂μ) <= ⨍ x in t, g (f x) ∂μ :=
    fun ht =>
    hg.convexOn.set_average_mem_epigraph hgc hsc ht (by finiteness) (ae_restrict_of_ae hfs)
      hfi.integrableOn hgi.integrableOn
  refine (ae_eq_const_or_exists_average_ne_c

中文:
定理 StrictConvexOn.ae_eq_const_or_map_average_lt
  结论: [IsFiniteMeasure μ] (hg : StrictConvexOn 实数 s g)
  证明: by
  have : forall {t}, μ t != 0 -> (⨍ x in t, f x ∂μ) in s ∧ g (⨍ x in t, f x ∂μ) <= ⨍ x in t, g (f x) ∂μ :=
    fun ht =>
    hg.convexOn.set_average_mem_epigraph hgc hsc ht (by finiteness) (ae_restrict_of_ae hfs)
      hfi.integrableOn hgi.integrableOn
  refine (ae_eq_const_or_exists_average_ne_c

Depends on / 依赖: ae_eq_const_or_exists_average_ne_compl, ae_restrict_of_ae, average_mem_openSegment_compl_self, average_pair, convexOn, finiteness, h_avg, hfi.integrableOn, hfi.prodMk, hg.convexOn.set_average_mem_epigraph, hgi.integrableOn, hm.nullMeasurableSet, imp_right, integrableOn, nullMeasurableSet, prodMk, set_average_mem_epigraph
-/
theorem StrictConvexOn.ae_eq_const_or_map_average_lt [IsFiniteMeasure μ] (hg : StrictConvexOn Real s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : forallᵐ x ∂μ, f x in s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ g (⨍ x, f x ∂μ) < ⨍ x, g (f x) ∂μ := by
  have : forall {t}, μ t != 0 -> (⨍ x in t, f x ∂μ) in s ∧ g (⨍ x in t, f x ∂μ) <= ⨍ x in t, g (f x) ∂μ :=
    fun ht =>
    hg.convexOn.set_average_mem_epigraph hgc hsc ht (by finiteness) (ae_restrict_of_ae hfs)
      hfi.integrableOn hgi.integrableOn
  refine (ae_eq_const_or_exists_average_ne_compl hfi).imp_right ?_
  rintro ⟨t, hm, h₀, h₀', hne⟩
  rcases average_mem_openSegment_compl_self hm.nullMeasurableSet h₀ h₀' (hfi.prodMk hgi) with
    ⟨a, b, ha, hb, hab, h_avg⟩
  rw [average_pair hfi hgi]; rw [average_pair hfi.integrableOn hgi.integrableOn]; rw [average_pair hfi.integrableOn hgi.integrableOn]; rw [Prod.smul_mk]; rw [Prod.smul_mk]; rw [Prod.mk_add_mk]; rw [Prod.mk_inj] at h_avg
  simp only [Function.comp] at h_avg
  rw [← h_avg.1]; rw [← h_avg.2]
  calc
    g ((a • ⨍ x in t, f x ∂μ) + b • ⨍ x in tᶜ, f x ∂μ) <
        a * g (⨍ x in t, f x ∂μ) + b * g (⨍ x in tᶜ, f x ∂μ) :=
      hg.2 (this h₀).1 (this h₀').1 hne ha hb hab
    _ <= (a * ⨍ x in t, g (f x) ∂μ) + b * ⨍ x in tᶜ, g (f x) ∂μ := by
      gcongr
      exacts [(this h₀).2, (this h₀').2]

/--
theorem `StrictConcaveOn.ae_eq_const_or_lt_map_average` / 定理 `StrictConcaveOn.ae_eq_const_or_lt_map_average`

English:
theorem StrictConcaveOn.ae_eq_const_or_lt_map_average
  statement: [IsFiniteMeasure μ]
  proof: by
  simpa only [Pi.neg_apply, average_neg, neg_lt_neg_iff] using
    hg.neg.ae_eq_const_or_map_average_lt hgc.neg hsc hfs hfi hgi.neg

中文:
定理 StrictConcaveOn.ae_eq_const_or_lt_map_average
  结论: [IsFiniteMeasure μ]
  证明: by
  simpa only [Pi.neg_apply, average_neg, neg_lt_neg_iff] using
    hg.neg.ae_eq_const_or_map_average_lt hgc.neg hsc hfs hfi hgi.neg

Depends on / 依赖: Pi.neg_apply, ae_eq_const_or_map_average_lt, average_neg, hg.neg.ae_eq_const_or_map_average_lt, hgc.neg, hgi.neg, neg_apply, neg_lt_neg_iff
-/
theorem StrictConcaveOn.ae_eq_const_or_lt_map_average [IsFiniteMeasure μ]
    (hg : StrictConcaveOn Real s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : forallᵐ x ∂μ, f x in s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ (⨍ x, g (f x) ∂μ) < g (⨍ x, f x ∂μ) := by
  simpa only [Pi.neg_apply, average_neg, neg_lt_neg_iff] using
    hg.neg.ae_eq_const_or_map_average_lt hgc.neg hsc hfs hfi hgi.neg

/--
theorem `ae_eq_const_or_norm_average_lt_of_norm_le_const` / 定理 `ae_eq_const_or_norm_average_lt_of_norm_le_const`

English:
theorem ae_eq_const_or_norm_average_lt_of_norm_le_const
  statement: [StrictConvexSpace Real E]
  proof: by
  rcases le_or_gt C 0 with hC0 | hC0
  · have : f =ᵐ[μ] 0 := h_le.mono fun x hx => norm_le_zero_iff.1 (hx.trans hC0)
    simp only [average_congr this, Pi.zero_apply, average_zero]
    exact Or.inl this
  by_cases hfi : Integrable f μ; swap
  · simp [average_eq, integral_undef hfi, hC0]
  rcases 

中文:
定理 ae_eq_const_or_norm_average_lt_of_norm_le_const
  结论: [StrictConvexSpace 实数 E]
  证明: by
  rcases le_or_gt C 0 with hC0 | hC0
  · have : f =ᵐ[μ] 0 := h_le.mono fun x hx => norm_le_zero_iff.1 (hx.trans hC0)
    simp only [average_congr this, Pi.zero_apply, average_zero]
    exact Or.inl this
  by_cases hfi : Integrable f μ; swap
  · simp [average_eq, integral_undef hfi, hC0]
  rcases 

Depends on / 依赖: Integrable, IsFiniteMeasure, Or.inl, Pi.zero_apply, average_congr, average_eq, average_zero, closedBall, eq_or_lt, h_le, h_le.mono, hx.trans, integral_undef, le_or_gt, le_top, measureReal_def, mem_closedBall_, norm_le_zero_iff, replace, zero_apply
-/
theorem ae_eq_const_or_norm_average_lt_of_norm_le_const [StrictConvexSpace Real E]
    (h_le : forallᵐ x ∂μ, ‖f x‖ <= C) : f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ ‖⨍ x, f x ∂μ‖ < C := by
  rcases le_or_gt C 0 with hC0 | hC0
  · have : f =ᵐ[μ] 0 := h_le.mono fun x hx => norm_le_zero_iff.1 (hx.trans hC0)
    simp only [average_congr this, Pi.zero_apply, average_zero]
    exact Or.inl this
  by_cases hfi : Integrable f μ; swap
  · simp [average_eq, integral_undef hfi, hC0]
  rcases (le_top : μ univ <= ∞).eq_or_lt with hμt | hμt
  · simp [average_eq, measureReal_def, hμt, hC0]
  have : IsFiniteMeasure μ := ⟨hμt⟩
  replace h_le : forallᵐ x ∂μ, f x in closedBall (0 : E) C := by simpa only [mem_closedBall_zero_iff]
  simpa only [interior_closedBall _ hC0.ne', mem_ball_zero_iff] using
    (strictConvex_closedBall Real (0 : E) C).ae_eq_const_or_average_mem_interior isClosed_closedBall
      h_le hfi

/--
theorem `ae_eq_const_or_norm_integral_lt_of_norm_le_const` / 定理 `ae_eq_const_or_norm_integral_lt_of_norm_le_const`

English:
theorem ae_eq_const_or_norm_integral_lt_of_norm_le_const
  statement: [StrictConvexSpace Real E] [IsFiniteMeasure μ]
  proof: by
  rcases eq_or_ne μ 0 with h₀ | h₀; · simp [h₀, EventuallyEq]
  have hμ : 0 < μ.real univ := by
    simp [measureReal_def, ENNReal.toReal_pos_iff, pos_iff_ne_zero, h₀, measure_lt_top]
  refine (ae_eq_const_or_norm_average_lt_of_norm_le_const h_le).imp_right fun H => ?_
  rwa [average_eq, norm_smu

中文:
定理 ae_eq_const_or_norm_integral_lt_of_norm_le_const
  结论: [StrictConvexSpace 实数 E] [IsFiniteMeasure μ]
  证明: by
  rcases eq_or_ne μ 0 with h₀ | h₀; · simp [h₀, EventuallyEq]
  have hμ : 0 < μ.real univ := by
    simp [measureReal_def, ENNReal.toReal_pos_iff, pos_iff_ne_zero, h₀, measure_lt_top]
  refine (ae_eq_const_or_norm_average_lt_of_norm_le_const h_le).imp_right fun H => ?_
  rwa [average_eq, norm_smu

Depends on / 依赖: ENNReal, ENNReal.toReal_pos_iff, EventuallyEq, Real.norm_eq_abs, abs_of_pos, ae_eq_const_or_norm_average_lt_of_norm_le_const, average_eq, div_eq_inv_mul, eq_or_ne, h_le, imp_right, measureReal_def, measure_lt_top, norm_eq_abs, norm_inv, norm_smul, pos_iff_ne_zero, toReal_pos_iff
-/
theorem ae_eq_const_or_norm_integral_lt_of_norm_le_const [StrictConvexSpace Real E] [IsFiniteMeasure μ]
    (h_le : forallᵐ x ∂μ, ‖f x‖ <= C) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ ‖∫ x, f x ∂μ‖ < μ.real univ * C := by
  rcases eq_or_ne μ 0 with h₀ | h₀; · simp [h₀, EventuallyEq]
  have hμ : 0 < μ.real univ := by
    simp [measureReal_def, ENNReal.toReal_pos_iff, pos_iff_ne_zero, h₀, measure_lt_top]
  refine (ae_eq_const_or_norm_average_lt_of_norm_le_const h_le).imp_right fun H => ?_
  rwa [average_eq, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hμ, ← div_eq_inv_mul,
    div_lt_iff₀' hμ] at H

/--
theorem `ae_eq_const_or_norm_setIntegral_lt_of_norm_le_const` / 定理 `ae_eq_const_or_norm_setIntegral_lt_of_norm_le_const`

English:
theorem ae_eq_const_or_norm_setIntegral_lt_of_norm_le_const
  statement: [StrictConvexSpace Real E] (ht : μ t != ∞)
  proof: by
  have := Fact.mk ht.lt_top
  rw [← measureReal_restrict_apply_univ]
  exact ae_eq_const_or_norm_integral_lt_of_norm_le_const h_le

中文:
定理 ae_eq_const_or_norm_setIntegral_lt_of_norm_le_const
  结论: [StrictConvexSpace 实数 E] (ht : μ t != ∞)
  证明: by
  have := Fact.mk ht.lt_top
  rw [← measureReal_restrict_apply_univ]
  exact ae_eq_const_or_norm_integral_lt_of_norm_le_const h_le

Depends on / 依赖: Fact.mk, ae_eq_const_or_norm_integral_lt_of_norm_le_const, h_le, ht.lt_top, lt_top, measureReal_restrict_apply_univ
-/
theorem ae_eq_const_or_norm_setIntegral_lt_of_norm_le_const [StrictConvexSpace Real E] (ht : μ t != ∞)
    (h_le : forallᵐ x ∂μ.restrict t, ‖f x‖ <= C) :
    f =ᵐ[μ.restrict t] const α (⨍ x in t, f x ∂μ) ∨ ‖∫ x in t, f x ∂μ‖ < μ.real t * C := by
  have := Fact.mk ht.lt_top
  rw [← measureReal_restrict_apply_univ]
  exact ae_eq_const_or_norm_integral_lt_of_norm_le_const h_le
