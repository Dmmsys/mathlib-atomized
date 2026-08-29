/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Properties of analyticity restricted to a set

From `Mathlib/Analysis/Analytic/Basic.lean`, we have the definitions

1. `AnalyticWithinAt 𝕜 f s x` means a power series at `x` converges to `f` on `𝓝[insert x s] x`.
2. `AnalyticOn 𝕜 f s t` means `∀ x ∈ t, AnalyticWithinAt 𝕜 f s x`.

This means there exists an extension of `f` which is analytic and agrees with `f` on `s ∪ {x}`, but
`f` is allowed to be arbitrary elsewhere.

Here we prove basic properties of these definitions. Where convenient we assume completeness of the
ambient space, which allows us to relate `AnalyticWithinAt` to analyticity of a local extension.
-/

public section

noncomputable section

open scoped Topology Filter ENNReal
open Set Filter Metric

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-!
### Basic properties
-/

/--
lemma `analyticWithinAt_of_singleton_mem` / 引理 `analyticWithinAt_of_singleton_mem`

English:
lemma analyticWithinAt_of_singleton_mem
  given: {f : E -> F} {s : Set E} {x : E} (h : {x} in 𝓝[s] x)
  proof: by
  rcases mem_nhdsWithin.mp h with ⟨t, ot, xt, st⟩
  rcases Metric.mem_nhds_iff.mp (ot.mem_nhds xt) with ⟨r, r0, rt⟩
  exact ⟨constFormalMultilinearSeries 𝕜 E (f x), .ofReal r,
  { r_le := by simp only [FormalMultilinearSeries.constFormalMultilinearSeries_radius, le_top]
    r_pos := by positivity

中文:
引理 analyticWithinAt_of_singleton_mem
  条件: {f : E -> F} {s : Set E} {x : E} (h : {x} in 𝓝[s] x)
  证明: by
  rcases mem_nhdsWithin.mp h with ⟨t, ot, xt, st⟩
  rcases Metric.mem_nhds_iff.mp (ot.mem_nhds xt) with ⟨r, r0, rt⟩
  exact ⟨constFormalMultilinearSeries 𝕜 E (f x), .ofReal r,
  { r_le := by simp only [FormalMultilinearSeries.constFormalMultilinearSeries_radius, le_top]
    r_pos := by positivity

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.constFormalMultilinearSeries_radius, Metric, Metric.mem_nhds_iff.mp, add_eq_left, and_imp, constFormalMultilinearSeries, constFormalMultilinearSeries_radius, hasSum, le_top, mem_insert_iff, mem_inter_iff, mem_nhds, mem_nhdsWithin, mem_nhdsWithin.mp, mem_nhds_iff, ofReal, ot.mem_nhds, r_le, r_pos
-/
lemma analyticWithinAt_of_singleton_mem {f : E -> F} {s : Set E} {x : E} (h : {x} in 𝓝[s] x) :
    AnalyticWithinAt 𝕜 f s x := by
  rcases mem_nhdsWithin.mp h with ⟨t, ot, xt, st⟩
  rcases Metric.mem_nhds_iff.mp (ot.mem_nhds xt) with ⟨r, r0, rt⟩
  exact ⟨constFormalMultilinearSeries 𝕜 E (f x), .ofReal r,
  { r_le := by simp only [FormalMultilinearSeries.constFormalMultilinearSeries_radius, le_top]
    r_pos := by positivity
    hasSum := by
      intro y ys yr
      simp only [subset_singleton_iff, mem_inter_iff, and_imp] at st
      simp only [mem_insert_iff, add_eq_left] at ys
      have : x + y = x := by
        rcases ys with rfl | ys
        · simp
        · exact st (x + y) (rt (by simpa using yr)) ys
      simp only [this]
      apply (hasFPowerSeriesOnBall_const (e := 0)).hasSum
      simp only [eball_top, mem_univ] }⟩

/--
lemma `analyticOn_of_locally_analyticOn` / 引理 `analyticOn_of_locally_analyticOn`

English:
lemma analyticOn_of_locally_analyticOn
  statement: {f : E -> F} {s : Set E}
  proof: by
  intro x m
  rcases h x m with ⟨u, ou, xu, fu⟩
  rcases Metric.mem_nhds_iff.mp (ou.mem_nhds xu) with ⟨r, r0, ru⟩
  rcases fu x ⟨m, xu⟩ with ⟨p, t, fp⟩
  exact ⟨p, min (.ofReal r) t,
    { r_pos := lt_min (by positivity) fp.r_pos
      r_le := min_le_of_right_le fp.r_le
      hasSum := by
       

中文:
引理 analyticOn_of_locally_analyticOn
  结论: {f : E -> F} {s : Set E}
  证明: by
  intro x m
  rcases h x m with ⟨u, ou, xu, fu⟩
  rcases Metric.mem_nhds_iff.mp (ou.mem_nhds xu) with ⟨r, r0, ru⟩
  rcases fu x ⟨m, xu⟩ with ⟨p, t, fp⟩
  exact ⟨p, min (.ofReal r) t,
    { r_pos := lt_min (by positivity) fp.r_pos
      r_le := min_le_of_right_le fp.r_le
      hasSum := by
       

Depends on / 依赖: Metric, Metric.mem_nhds_iff.mp, add_eq_left, dist_zero_right, edist_lt_ofReal, fp.hasSum, fp.r_le, fp.r_pos, hasSum, lt_min, lt_min_iff, mem_eball, mem_insert_iff, mem_inte, mem_nhds, mem_nhds_iff, min_le_of_right_le, ofReal, ou.mem_nhds, r_le
-/
lemma analyticOn_of_locally_analyticOn {f : E -> F} {s : Set E}
    (h : forall x in s, exists u, IsOpen u ∧ x in u ∧ AnalyticOn 𝕜 f (s inter u)) :
    AnalyticOn 𝕜 f s := by
  intro x m
  rcases h x m with ⟨u, ou, xu, fu⟩
  rcases Metric.mem_nhds_iff.mp (ou.mem_nhds xu) with ⟨r, r0, ru⟩
  rcases fu x ⟨m, xu⟩ with ⟨p, t, fp⟩
  exact ⟨p, min (.ofReal r) t,
    { r_pos := lt_min (by positivity) fp.r_pos
      r_le := min_le_of_right_le fp.r_le
      hasSum := by
        intro y ys yr
        simp only [mem_eball, lt_min_iff, edist_lt_ofReal, dist_zero_right] at yr
        apply fp.hasSum
        · simp only [mem_insert_iff, add_eq_left] at ys
          rcases ys with rfl | ys
          · simp
          · simp only [mem_insert_iff, add_eq_left, mem_inter_iff, ys, true_and]
            apply Or.inr (ru ?_)
            simp only [mem_ball, dist_self_add_left, yr]
        · simp only [mem_eball, yr] }⟩

/--
lemma `IsOpen.analyticOn_iff_analyticOnNhd` / 引理 `IsOpen.analyticOn_iff_analyticOnNhd`

English:
lemma IsOpen.analyticOn_iff_analyticOnNhd
  given: {f : E -> F} {s : Set E} (hs : IsOpen s)
  proof: by
  refine ⟨?_, AnalyticOnNhd.analyticOn⟩
  intro hf x m
  rcases Metric.mem_nhds_iff.mp (hs.mem_nhds m) with ⟨r, r0, rs⟩
  rcases hf x m with ⟨p, t, fp⟩
  exact ⟨p, min (.ofReal r) t,
  { r_pos := lt_min (by positivity) fp.r_pos
    r_le := min_le_of_right_le fp.r_le
    hasSum := by
      intro y

中文:
引理 IsOpen.analyticOn_iff_analyticOnNhd
  条件: {f : E -> F} {s : Set E} (hs : IsOpen s)
  证明: by
  refine ⟨?_, AnalyticOnNhd.analyticOn⟩
  intro hf x m
  rcases Metric.mem_nhds_iff.mp (hs.mem_nhds m) with ⟨r, r0, rs⟩
  rcases hf x m with ⟨p, t, fp⟩
  exact ⟨p, min (.ofReal r) t,
  { r_pos := lt_min (by positivity) fp.r_pos
    r_le := min_le_of_right_le fp.r_le
    hasSum := by
      intro y

Depends on / 依赖: AnalyticOnNhd, AnalyticOnNhd.analyticOn, Metric, Metric.mem_nhds_iff.mp, analyticOn, dist_self_add_left, dist_zero_right, edist_lt_ofReal, fp.hasSum, fp.r_le, fp.r_pos, hasSum, hs.mem_nhds, lt_min, lt_min_iff, mem_ball, mem_eball, mem_insert_of_mem, mem_nhds, mem_nhds_iff
-/
lemma IsOpen.analyticOn_iff_analyticOnNhd {f : E -> F} {s : Set E} (hs : IsOpen s) :
    AnalyticOn 𝕜 f s ↔ AnalyticOnNhd 𝕜 f s := by
  refine ⟨?_, AnalyticOnNhd.analyticOn⟩
  intro hf x m
  rcases Metric.mem_nhds_iff.mp (hs.mem_nhds m) with ⟨r, r0, rs⟩
  rcases hf x m with ⟨p, t, fp⟩
  exact ⟨p, min (.ofReal r) t,
  { r_pos := lt_min (by positivity) fp.r_pos
    r_le := min_le_of_right_le fp.r_le
    hasSum := by
      intro y ym
      simp only [mem_eball, lt_min_iff, edist_lt_ofReal, dist_zero_right] at ym
      refine fp.hasSum ?_ ym.2
      apply mem_insert_of_mem
      apply rs
      simp only [mem_ball, dist_self_add_left, ym.1] }⟩

/-!
### Equivalence to analyticity of a local extension

We show that `HasFPowerSeriesWithinOnBall`, `HasFPowerSeriesWithinAt`, and `AnalyticWithinAt` are
equivalent to the existence of a local extension with full analyticity. We do not yet show a
result for `AnalyticOn`, as this requires a bit more work to show that local extensions can
be stitched together.
-/

/--
lemma `hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall` / 引理 `hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall`

English:
lemma hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall
  statement: [CompleteSpace F] {f : E -> F}
  proof: by
  constructor
  · intro h
    refine ⟨fun y => p.sum (y - x), ?_, ?_⟩
    · intro y ⟨ys,yb⟩
      simp only [mem_eball, edist_eq_enorm_sub] at yb
      have e0 := p.hasSum (x := y - x) ?_
      · have e1 := (h.hasSum (y := y - x) ?_ ?_)
        · simp only [add_sub_cancel] at e1
          exact e

中文:
引理 hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall
  结论: [CompleteSpace F] {f : E -> F}
  证明: by
  constructor
  · intro h
    refine ⟨fun y => p.sum (y - x), ?_, ?_⟩
    · intro y ⟨ys,yb⟩
      simp only [mem_eball, edist_eq_enorm_sub] at yb
      have e0 := p.hasSum (x := y - x) ?_
      · have e1 := (h.hasSum (y := y - x) ?_ ?_)
        · simp only [add_sub_cancel] at e1
          exact e

Depends on / 依赖: add_sub_cancel, add_sub_cancel_left, e1.unique, edist_eq_enorm_sub, edist_zero_right, h.hasSum, h.r_le, h.r_pos, hasSum, lt_of_lt_of_le, mem_eball, p.hasSum, p.sum, r_le, r_pos, unique
-/
lemma hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall [CompleteSpace F] {f : E -> F}
    {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : Real>=0∞} :
    HasFPowerSeriesWithinOnBall f p s x r ↔
      exists g, EqOn f g (insert x s inter eball x r) ∧
        HasFPowerSeriesOnBall g p x r := by
  constructor
  · intro h
    refine ⟨fun y => p.sum (y - x), ?_, ?_⟩
    · intro y ⟨ys,yb⟩
      simp only [mem_eball, edist_eq_enorm_sub] at yb
      have e0 := p.hasSum (x := y - x) ?_
      · have e1 := (h.hasSum (y := y - x) ?_ ?_)
        · simp only [add_sub_cancel] at e1
          exact e1.unique e0
        · simpa only [add_sub_cancel]
        · simpa only [mem_eball, edist_zero_right]
      · simp only [mem_eball, edist_zero_right]
        exact lt_of_lt_of_le yb h.r_le
    · refine ⟨h.r_le, h.r_pos, ?_⟩
      intro y lt
      simp only [add_sub_cancel_left]
      apply p.hasSum
      simp only [mem_eball] at lt ⊢
      exact lt_of_lt_of_le lt h.r_le
  · intro ⟨g, hfg, hg⟩
    refine ⟨hg.r_le, hg.r_pos, ?_⟩
    intro y ys lt
    rw [hfg]
    · exact hg.hasSum lt
    · refine ⟨ys, ?_⟩
      simpa only [mem_eball, edist_eq_enorm_sub, add_sub_cancel_left, sub_zero] using lt

/--
lemma `hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt` / 引理 `hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt`

English:
lemma hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt
  statement: [CompleteSpace F] {f : E -> F}
  proof: by
  constructor
  · intro ⟨r, h⟩
    rcases hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall.mp h with ⟨g, e, h⟩
    refine ⟨g, ?_, ⟨r, h⟩⟩
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, ?_, e⟩
    exact inter_mem_nhdsWithin _ (eball_mem_nhds _ h.r_pos)
  · intro ⟨g, hfg, ⟨r, hg⟩

中文:
引理 hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt
  结论: [CompleteSpace F] {f : E -> F}
  证明: by
  constructor
  · intro ⟨r, h⟩
    rcases hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall.mp h with ⟨g, e, h⟩
    refine ⟨g, ?_, ⟨r, h⟩⟩
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, ?_, e⟩
    exact inter_mem_nhdsWithin _ (eball_mem_nhds _ h.r_pos)
  · intro ⟨g, hfg, ⟨r, hg⟩

Depends on / 依赖: Filter, Filter.eventuallyEq_iff_exists_mem.mpr, Metric, Metric.eventually_nhds_iff, eball_mem_nhds, eventuallyEq_iff_exists_mem, eventuallyEq_nhdsWithin_iff, eventually_nhds_iff, h.r_pos, hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall, hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall.mp, hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall.mpr, inter_mem_nhdsWithin, ofReal, r_pos
-/
lemma hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt [CompleteSpace F] {f : E -> F}
    {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} :
    HasFPowerSeriesWithinAt f p s x ↔
      exists g, f =ᶠ[𝓝[insert x s] x] g ∧ HasFPowerSeriesAt g p x := by
  constructor
  · intro ⟨r, h⟩
    rcases hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall.mp h with ⟨g, e, h⟩
    refine ⟨g, ?_, ⟨r, h⟩⟩
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, ?_, e⟩
    exact inter_mem_nhdsWithin _ (eball_mem_nhds _ h.r_pos)
  · intro ⟨g, hfg, ⟨r, hg⟩⟩
    simp only [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff] at hfg
    rcases hfg with ⟨e, e0, hfg⟩
    refine ⟨min r (.ofReal e), ?_⟩
    refine hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall.mpr ⟨g, ?_, ?_⟩
    · intro y ⟨ys, xy⟩
      refine hfg ?_ ys
      simp only [mem_eball, lt_min_iff, edist_lt_ofReal] at xy
      exact xy.2
    · exact hg.mono (lt_min hg.r_pos (by positivity)) (min_le_left _ _)

/--
lemma `analyticWithinAt_iff_exists_analyticAt` / 引理 `analyticWithinAt_iff_exists_analyticAt`

English:
lemma analyticWithinAt_iff_exists_analyticAt
  given: [CompleteSpace F] {f : E -> F} {s : Set E} {x : E}
  proof: by
  simp only [AnalyticWithinAt, AnalyticAt, hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt]
  tauto

中文:
引理 analyticWithinAt_iff_exists_analyticAt
  条件: [CompleteSpace F] {f : E -> F} {s : Set E} {x : E}
  证明: by
  simp only [AnalyticWithinAt, AnalyticAt, hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt]
  tauto

Depends on / 依赖: AnalyticAt, AnalyticWithinAt, hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt
-/
lemma analyticWithinAt_iff_exists_analyticAt [CompleteSpace F] {f : E -> F} {s : Set E} {x : E} :
    AnalyticWithinAt 𝕜 f s x ↔
      exists g, f =ᶠ[𝓝[insert x s] x] g ∧ AnalyticAt 𝕜 g x := by
  simp only [AnalyticWithinAt, AnalyticAt, hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt]
  tauto

/--
lemma `analyticWithinAt_iff_exists_analyticAt'` / 引理 `analyticWithinAt_iff_exists_analyticAt'`

English:
lemma analyticWithinAt_iff_exists_analyticAt'
  given: [CompleteSpace F] {f : E -> F} {s : Set E} {x : E}
  proof: by
  classical
  simp only [analyticWithinAt_iff_exists_analyticAt]
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hf, hg⟩
    rcases mem_nhdsWithin.1 hf with ⟨u, u_open, xu, hu⟩
    let g' := Set.piecewise u g f
    refine ⟨g', ?_, ?_, ?_⟩
    · have : x in u inter insert x s := ⟨xu, by simp⟩
      simpa [g', xu

中文:
引理 analyticWithinAt_iff_exists_analyticAt'
  条件: [CompleteSpace F] {f : E -> F} {s : Set E} {x : E}
  证明: by
  classical
  simp only [analyticWithinAt_iff_exists_analyticAt]
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hf, hg⟩
    rcases mem_nhdsWithin.1 hf with ⟨u, u_open, xu, hu⟩
    let g' := Set.piecewise u g f
    refine ⟨g', ?_, ?_, ?_⟩
    · have : x in u inter insert x s := ⟨xu, by simp⟩
      simpa [g', xu

Depends on / 依赖: Set.piecewise, analyticWithinAt_iff_exists_analyticAt, classical, filter_upwards, hg.congr, insert, mem_nhds, mem_nhdsWithin, piecewise, u_open, u_open.mem_nhds
-/
lemma analyticWithinAt_iff_exists_analyticAt' [CompleteSpace F] {f : E -> F} {s : Set E} {x : E} :
    AnalyticWithinAt 𝕜 f s x ↔
      exists g, f x = g x ∧ EqOn f g (insert x s) ∧ AnalyticAt 𝕜 g x := by
  classical
  simp only [analyticWithinAt_iff_exists_analyticAt]
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hf, hg⟩
    rcases mem_nhdsWithin.1 hf with ⟨u, u_open, xu, hu⟩
    let g' := Set.piecewise u g f
    refine ⟨g', ?_, ?_, ?_⟩
    · have : x in u inter insert x s := ⟨xu, by simp⟩
      simpa [g', xu, this] using hu this
    · intro y hy
      by_cases h'y : y in u
      · have : y in u inter insert x s := ⟨h'y, hy⟩
        simpa [g', h'y, this] using hu this
      · simp [g', h'y]
    · apply hg.congr
      filter_upwards [u_open.mem_nhds xu] with y hy using by simp [g', hy]
  · rintro ⟨g, -, hf, hg⟩
    exact ⟨g, by filter_upwards [self_mem_nhdsWithin] using hf, hg⟩

alias ⟨AnalyticWithinAt.exists_analyticAt, _⟩ := analyticWithinAt_iff_exists_analyticAt'

/--
lemma `AnalyticWithinAt.exists_mem_nhdsWithin_analyticOn` / 引理 `AnalyticWithinAt.exists_mem_nhdsWithin_analyticOn`

English:
lemma AnalyticWithinAt.exists_mem_nhdsWithin_analyticOn
  proof: by
  obtain ⟨g, -, h'g, hg⟩ : exists g, f x = g x ∧ EqOn f g (insert x s) ∧ AnalyticAt 𝕜 g x :=
    h.exists_analyticAt
  let u := insert x s inter {y | AnalyticAt 𝕜 g y}
  refine ⟨u, ?_, ?_⟩
  · exact inter_mem_nhdsWithin _ ((isOpen_analyticAt 𝕜 g).mem_nhds hg)
  · intro y hy
    have : AnalyticWit

中文:
引理 AnalyticWithinAt.exists_mem_nhdsWithin_analyticOn
  证明: by
  obtain ⟨g, -, h'g, hg⟩ : exists g, f x = g x ∧ EqOn f g (insert x s) ∧ AnalyticAt 𝕜 g x :=
    h.exists_analyticAt
  let u := insert x s inter {y | AnalyticAt 𝕜 g y}
  refine ⟨u, ?_, ?_⟩
  · exact inter_mem_nhdsWithin _ ((isOpen_analyticAt 𝕜 g).mem_nhds hg)
  · intro y hy
    have : AnalyticWit

Depends on / 依赖: AnalyticAt, AnalyticWithinAt, analyticWithinAt, exists_analyticAt, g.mono, h.exists_analyticAt, insert, inter_mem_nhdsWithin, inter_subset_left, isOpen_analyticAt, mem_nhds, this.congr
-/
lemma AnalyticWithinAt.exists_mem_nhdsWithin_analyticOn
    [CompleteSpace F] {f : E -> F} {s : Set E} {x : E} (h : AnalyticWithinAt 𝕜 f s x) :
    exists u in 𝓝[insert x s] x, AnalyticOn 𝕜 f u := by
  obtain ⟨g, -, h'g, hg⟩ : exists g, f x = g x ∧ EqOn f g (insert x s) ∧ AnalyticAt 𝕜 g x :=
    h.exists_analyticAt
  let u := insert x s inter {y | AnalyticAt 𝕜 g y}
  refine ⟨u, ?_, ?_⟩
  · exact inter_mem_nhdsWithin _ ((isOpen_analyticAt 𝕜 g).mem_nhds hg)
  · intro y hy
    have : AnalyticWithinAt 𝕜 g u y := hy.2.analyticWithinAt
    exact this.congr (h'g.mono (inter_subset_left)) (h'g (inter_subset_left hy))

/--
theorem `AnalyticWithinAt.eventually_analyticWithinAt` / 定理 `AnalyticWithinAt.eventually_analyticWithinAt`

English:
theorem AnalyticWithinAt.eventually_analyticWithinAt
  proof: by
  obtain ⟨g, hfg, hga⟩ := analyticWithinAt_iff_exists_analyticAt.mp hf
  simp only [Filter.EventuallyEq, eventually_nhdsWithin_iff] at hfg ⊢
  filter_upwards [hfg.eventually_nhds, hga.eventually_analyticAt] with z hfgz hgaz hz
  refine analyticWithinAt_iff_exists_analyticAt.mpr ⟨g, ?_, hgaz⟩
exac

中文:
定理 AnalyticWithinAt.eventually_analyticWithinAt
  证明: by
  obtain ⟨g, hfg, hga⟩ := analyticWithinAt_iff_exists_analyticAt.mp hf
  simp only [Filter.EventuallyEq, eventually_nhdsWithin_iff] at hfg ⊢
  filter_upwards [hfg.eventually_nhds, hga.eventually_analyticAt] with z hfgz hgaz hz
  refine analyticWithinAt_iff_exists_analyticAt.mpr ⟨g, ?_, hgaz⟩
exac

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, analyticWithinAt_iff_exists_analyticAt, analyticWithinAt_iff_exists_analyticAt.mp, analyticWithinAt_iff_exists_analyticAt.mpr, eventually_analyticAt, eventually_nhds, eventually_nhdsWithin_iff, eventually_nhdsWithin_iff.mpr, filter_mono, filter_upwards, hfg.eventually_nhds, hga.eventually_analyticAt, nhdsWithin_mono
-/
theorem AnalyticWithinAt.eventually_analyticWithinAt
    [CompleteSpace F] {f : E -> F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) : forallᶠ y in 𝓝[s] x, AnalyticWithinAt 𝕜 f s y := by
  obtain ⟨g, hfg, hga⟩ := analyticWithinAt_iff_exists_analyticAt.mp hf
  simp only [Filter.EventuallyEq, eventually_nhdsWithin_iff] at hfg ⊢
  filter_upwards [hfg.eventually_nhds, hga.eventually_analyticAt] with z hfgz hgaz hz
  refine analyticWithinAt_iff_exists_analyticAt.mpr ⟨g, ?_, hgaz⟩
exact (eventually_nhdsWithin_iff.mpr hfgz).filter_mono nhdsWithin_mono _ (by simp [hz])
