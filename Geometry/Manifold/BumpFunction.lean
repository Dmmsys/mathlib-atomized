/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Smooth bump functions on a smooth manifold

In this file we define `SmoothBumpFunction I c` to be a bundled smooth "bump" function centered at
`c`. It is a structure that consists of two real numbers `0 < rIn < rOut` with small enough `rOut`.
We define a coercion to function for this type, and for `f : SmoothBumpFunction I c`, the function
`⇑f` written in the extended chart at `c` has the following properties:

* `f x = 1` in the closed ball of radius `f.rIn` centered at `c`;
* `f x = 0` outside of the ball of radius `f.rOut` centered at `c`;
* `0 ≤ f x ≤ 1` for all `x`.

The actual statements involve (pre)images under `extChartAt I f` and are given as lemmas in the
`SmoothBumpFunction` namespace.

## Tags

manifold, smooth bump function
-/

@[expose] public section

universe uE uF uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M]

open Function Filter Module Set Metric

open scoped Topology Manifold ContDiff

noncomputable section

/-!
### Smooth bump function

In this section we define a structure for a bundled smooth bump function and prove its properties.
-/

variable (I) in
/--
Definition of `SmoothBumpFunction` / `SmoothBumpFunction` 的定义

English:
structure SmoothBumpFunction
  parameters: (c : M)
  extends: ContDiffBump (extChartAt I c c)
  axioms and operations (1):
    - closedBall_subset : closedBall (extChartAt I c c) rOut inter range I subseteq (extChartAt I c).target

中文:
结构 光滑凸函数
  参数: (c : M)
  继承: 余ntDiffBump (extChartAt I c c)
  公理与运算 (1 个):
    - closedBall_subset : closedBall (extChartAt I c c) rOut inter range I subseteq (extChartAt I c).target
-/
structure SmoothBumpFunction (c : M) extends ContDiffBump (extChartAt I c c) where
  closedBall_subset : closedBall (extChartAt I c c) rOut inter range I subseteq (extChartAt I c).target

namespace SmoothBumpFunction

section FiniteDimensional

variable [FiniteDimensional Real E]

variable {c : M} (f : SmoothBumpFunction I c) {x : M}

/--
Definition of `toFun` / `toFun` 的定义

English:
definition toFun
  signature: : M -> Real
  body: indicator (chartAt H c).source (f.toContDiffBump ∘ extChartAt I c)

中文:
定义 toFun
  签名: : M -> 实数
  定义体: indicator (chartAt H c).source (f.toContDiffBump ∘ extChartAt I c)
-/
@[coe] def toFun : M -> Real :=
  indicator (chartAt H c).source (f.toContDiffBump ∘ extChartAt I c)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (SmoothBumpFunction I c) fun _ => M -> Real
  body: ⟨toFun⟩

中文:
实例 :
  签名: CoeFun (光滑凸函数 I c) fun _ => M -> 实数
  定义体: ⟨toFun⟩
-/
instance : CoeFun (SmoothBumpFunction I c) fun _ => M -> Real :=
  ⟨toFun⟩

/--
theorem `coe_def` / 定理 `coe_def`

English:
theorem coe_def
  statement: ⇑f = indicator (chartAt H c).source (f.toContDiffBump ∘ extChartAt I c)
  proof: rfl

中文:
定理 coe_def
  结论: ⇑f = indicator (chartAt H c).source (f.toContDiffBump ∘ extChartAt I c)
  证明: rfl
-/
theorem coe_def : ⇑f = indicator (chartAt H c).source (f.toContDiffBump ∘ extChartAt I c) :=
  rfl

end FiniteDimensional

variable {c : M} (f : SmoothBumpFunction I c) {x : M}

/--
theorem `rOut_pos` / 定理 `rOut_pos`

English:
theorem rOut_pos
  statement: 0 < f.rOut
  proof: f.toContDiffBump.rOut_pos

中文:
定理 rOut_pos
  结论: 0 < f.rOut
  证明: f.toContDiffBump.rOut_pos

Depends on / 依赖: f.toContDiffBump.rOut_pos, rOut_pos, toContDiffBump
-/
theorem rOut_pos : 0 < f.rOut :=
  f.toContDiffBump.rOut_pos

/--
theorem `ball_subset` / 定理 `ball_subset`

English:
theorem ball_subset
  statement: ball (extChartAt I c c) f.rOut inter range I subseteq (extChartAt I c).target
  proof: Subset.trans (inter_subset_inter_left _ ball_subset_closedBall) f.closedBall_subset

中文:
定理 ball_subset
  结论: ball (extChartAt I c c) f.rOut inter range I subseteq (extChartAt I c).target
  证明: Subset.trans (inter_subset_inter_left _ ball_subset_closedBall) f.closedBall_subset

Depends on / 依赖: Subset, Subset.trans, ball_subset_closedBall, closedBall_subset, f.closedBall_subset, inter_subset_inter_left
-/
theorem ball_subset : ball (extChartAt I c c) f.rOut inter range I subseteq (extChartAt I c).target :=
  Subset.trans (inter_subset_inter_left _ ball_subset_closedBall) f.closedBall_subset

/--
theorem `ball_inter_range_eq_ball_inter_target` / 定理 `ball_inter_range_eq_ball_inter_target`

English:
theorem ball_inter_range_eq_ball_inter_target
  proof: (subset_inter inter_subset_left f.ball_subset).antisymm inter_subset_inter_right _
    extChartAt_target_subset_range _

中文:
定理 ball_inter_range_eq_ball_inter_target
  证明: (subset_inter inter_subset_left f.ball_subset).antisymm inter_subset_inter_right _
    extChartAt_target_subset_range _

Depends on / 依赖: antisymm, ball_subset, extChartAt_target_subset_range, f.ball_subset, inter_subset_inter_right, inter_subset_left, subset_inter
-/
theorem ball_inter_range_eq_ball_inter_target :
    ball (extChartAt I c c) f.rOut inter range I =
      ball (extChartAt I c c) f.rOut inter (extChartAt I c).target :=
(subset_inter inter_subset_left f.ball_subset).antisymm inter_subset_inter_right _
    extChartAt_target_subset_range _

section FiniteDimensional

variable [FiniteDimensional Real E]

/--
theorem `eqOn_source` / 定理 `eqOn_source`

English:
theorem eqOn_source
  statement: EqOn f (f.toContDiffBump ∘ extChartAt I c) (chartAt H c).source
  proof: eqOn_indicator

中文:
定理 eqOn_source
  结论: EqOn f (f.toContDiffBump ∘ extChartAt I c) (chartAt H c).source
  证明: eqOn_indicator

Depends on / 依赖: eqOn_indicator
-/
theorem eqOn_source : EqOn f (f.toContDiffBump ∘ extChartAt I c) (chartAt H c).source :=
  eqOn_indicator

/--
theorem `eventuallyEq_of_mem_source` / 定理 `eventuallyEq_of_mem_source`

English:
theorem eventuallyEq_of_mem_source
  given: (hx : x in (chartAt H c).source)
  proof: f.eqOn_source.eventuallyEq_of_mem (chartAt H c).open_source.mem_nhds hx

中文:
定理 eventuallyEq_of_mem_source
  条件: (hx : x in (chartAt H c).source)
  证明: f.eqOn_source.eventuallyEq_of_mem (chartAt H c).open_source.mem_nhds hx

Depends on / 依赖: chartAt, eqOn_source, eventuallyEq_of_mem, f.eqOn_source.eventuallyEq_of_mem, mem_nhds, open_source, open_source.mem_nhds
-/
theorem eventuallyEq_of_mem_source (hx : x in (chartAt H c).source) :
    f =ᶠ[𝓝 x] f.toContDiffBump ∘ extChartAt I c :=
f.eqOn_source.eventuallyEq_of_mem (chartAt H c).open_source.mem_nhds hx

/--
theorem `one_of_dist_le` / 定理 `one_of_dist_le`

English:
theorem one_of_dist_le
  statement: (hs : x in (chartAt H c).source)
  proof: by
  simp only [f.eqOn_source hs, (· ∘ ·), f.one_of_mem_closedBall hd]

中文:
定理 one_of_dist_le
  结论: (hs : x in (chartAt H c).source)
  证明: by
  simp only [f.eqOn_source hs, (· ∘ ·), f.one_of_mem_closedBall hd]

Depends on / 依赖: eqOn_source, f.eqOn_source, f.one_of_mem_closedBall, one_of_mem_closedBall
-/
theorem one_of_dist_le (hs : x in (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) <= f.rIn) : f x = 1 := by
  simp only [f.eqOn_source hs, (· ∘ ·), f.one_of_mem_closedBall hd]

/--
theorem `support_eq_inter_preimage` / 定理 `support_eq_inter_preimage`

English:
theorem support_eq_inter_preimage
  proof: by
  rw [coe_def]; rw [support_indicator]; rw [support_comp_eq_preimage]; rw [← extChartAt_source I]; rw [← (extChartAt I c).symm_image_target_inter_eq']; rw [← (extChartAt I c).symm_image_target_inter_eq']; rw [f.support_eq]

中文:
定理 support_eq_inter_preimage
  证明: by
  rw [coe_def]; rw [support_indicator]; rw [support_comp_eq_preimage]; rw [← extChartAt_source I]; rw [← (extChartAt I c).symm_image_target_inter_eq']; rw [← (extChartAt I c).symm_image_target_inter_eq']; rw [f.support_eq]

Depends on / 依赖: coe_def, extChartAt, extChartAt_source, f.support_eq, support_comp_eq_preimage, support_eq, support_indicator, symm_image_target_inter_eq
-/
theorem support_eq_inter_preimage :
    support f = (chartAt H c).source inter extChartAt I c ⁻¹' ball (extChartAt I c c) f.rOut := by
  rw [coe_def]; rw [support_indicator]; rw [support_comp_eq_preimage]; rw [← extChartAt_source I]; rw [← (extChartAt I c).symm_image_target_inter_eq']; rw [← (extChartAt I c).symm_image_target_inter_eq']; rw [f.support_eq]

/--
theorem `isOpen_support` / 定理 `isOpen_support`

English:
theorem isOpen_support
  statement: IsOpen (support f)
  proof: by
  rw [support_eq_inter_preimage]
  exact isOpen_extChartAt_preimage c isOpen_ball

中文:
定理 isOpen_support
  结论: 是开集 (support f)
  证明: by
  rw [support_eq_inter_preimage]
  exact isOpen_extChartAt_preimage c isOpen_ball

Depends on / 依赖: isOpen_ball, isOpen_extChartAt_preimage, support_eq_inter_preimage
-/
theorem isOpen_support : IsOpen (support f) := by
  rw [support_eq_inter_preimage]
  exact isOpen_extChartAt_preimage c isOpen_ball

/--
theorem `support_eq_symm_image` / 定理 `support_eq_symm_image`

English:
theorem support_eq_symm_image
  proof: by
  rw [f.support_eq_inter_preimage]; rw [← extChartAt_source I]; rw [← (extChartAt I c).symm_image_target_inter_eq']; rw [inter_comm]; rw [ball_inter_range_eq_ball_inter_target]

中文:
定理 support_eq_symm_image
  证明: by
  rw [f.support_eq_inter_preimage]; rw [← extChartAt_source I]; rw [← (extChartAt I c).symm_image_target_inter_eq']; rw [inter_comm]; rw [ball_inter_range_eq_ball_inter_target]

Depends on / 依赖: ball_inter_range_eq_ball_inter_target, extChartAt, extChartAt_source, f.support_eq_inter_preimage, inter_comm, support_eq_inter_preimage, symm_image_target_inter_eq
-/
theorem support_eq_symm_image :
    support f = (extChartAt I c).symm '' (ball (extChartAt I c c) f.rOut inter range I) := by
  rw [f.support_eq_inter_preimage]; rw [← extChartAt_source I]; rw [← (extChartAt I c).symm_image_target_inter_eq']; rw [inter_comm]; rw [ball_inter_range_eq_ball_inter_target]

/--
theorem `support_subset_source` / 定理 `support_subset_source`

English:
theorem support_subset_source
  statement: support f subseteq (chartAt H c).source
  proof: by
  rw [f.support_eq_inter_preimage]; rw [← extChartAt_source I]; exact inter_subset_left

中文:
定理 support_subset_source
  结论: support f subseteq (chartAt H c).source
  证明: by
  rw [f.support_eq_inter_preimage]; rw [← extChartAt_source I]; exact inter_subset_left

Depends on / 依赖: extChartAt_source, f.support_eq_inter_preimage, inter_subset_left, support_eq_inter_preimage
-/
theorem support_subset_source : support f subseteq (chartAt H c).source := by
  rw [f.support_eq_inter_preimage]; rw [← extChartAt_source I]; exact inter_subset_left

/--
theorem `image_eq_inter_preimage_of_subset_support` / 定理 `image_eq_inter_preimage_of_subset_support`

English:
theorem image_eq_inter_preimage_of_subset_support
  given: {s : Set M} (hs : s subseteq support f)
  proof: by
  rw [support_eq_inter_preimage]; rw [subset_inter_iff]; rw [← extChartAt_source I]; rw [← image_subset_iff] at hs
  obtain ⟨hse, hsf⟩ := hs
  apply Subset.antisymm
  · refine subset_inter (subset_inter (hsf.trans ball_subset_closedBall) ?_) ?_
    · rintro _ ⟨x, -, rfl⟩; exact mem_range_self _
 

中文:
定理 image_eq_inter_preimage_of_subset_support
  条件: {s : 集合 M} (hs : s subseteq support f)
  证明: by
  rw [support_eq_inter_preimage]; rw [subset_inter_iff]; rw [← extChartAt_source I]; rw [← image_subset_iff] at hs
  obtain ⟨hse, hsf⟩ := hs
  apply Subset.antisymm
  · refine subset_inter (subset_inter (hsf.trans ball_subset_closedBall) ?_) ?_
    · rintro _ ⟨x, -, rfl⟩; exact mem_range_self _
 

Depends on / 依赖: Subset, Subset.antisymm, Subset.trans, antisymm, ball_subset_closedBall, closedBall_subset, extChartAt, extChartAt_source, f.closedBall_subset, hsf.trans, image_eq_target_inter_inv_preim, image_eq_target_inter_inv_preimage, image_subset_iff, inter_subset_inter_left, inter_subset_right, mem_range_self, subset_inter, subset_inter_iff, support_eq_inter_preimage
-/
theorem image_eq_inter_preimage_of_subset_support {s : Set M} (hs : s subseteq support f) :
    extChartAt I c '' s =
      closedBall (extChartAt I c c) f.rOut inter range I inter (extChartAt I c).symm ⁻¹' s := by
  rw [support_eq_inter_preimage]; rw [subset_inter_iff]; rw [← extChartAt_source I]; rw [← image_subset_iff] at hs
  obtain ⟨hse, hsf⟩ := hs
  apply Subset.antisymm
  · refine subset_inter (subset_inter (hsf.trans ball_subset_closedBall) ?_) ?_
    · rintro _ ⟨x, -, rfl⟩; exact mem_range_self _
    · rw [(extChartAt I c).image_eq_target_inter_inv_preimage hse]
      exact inter_subset_right
  · refine Subset.trans (inter_subset_inter_left _ f.closedBall_subset) ?_
    rw [(extChartAt I c).image_eq_target_inter_inv_preimage hse]

/--
theorem `mem_Icc` / 定理 `mem_Icc`

English:
theorem mem_Icc
  statement: f x in Icc (0 : Real) 1
  proof: by
  have : f x = 0 ∨ f x = _ := indicator_eq_zero_or_self _ _ _
  rcases this with h | h <;> rw [h]
  exacts [left_mem_Icc.2 zero_le_one, ⟨f.nonneg, f.le_one⟩]

中文:
定理 mem_Icc
  结论: f x in 闭区间 (0 : 实数) 1
  证明: by
  have : f x = 0 ∨ f x = _ := indicator_eq_zero_or_self _ _ _
  rcases this with h | h <;> rw [h]
  exacts [left_mem_Icc.2 zero_le_one, ⟨f.nonneg, f.le_one⟩]

Depends on / 依赖: exacts, f.le_one, f.nonneg, indicator_eq_zero_or_self, le_one, left_mem_Icc, nonneg, zero_le_one
-/
theorem mem_Icc : f x in Icc (0 : Real) 1 := by
  have : f x = 0 ∨ f x = _ := indicator_eq_zero_or_self _ _ _
  rcases this with h | h <;> rw [h]
  exacts [left_mem_Icc.2 zero_le_one, ⟨f.nonneg, f.le_one⟩]

/--
theorem `nonneg` / 定理 `nonneg`

English:
theorem nonneg
  statement: 0 <= f x
  proof: f.mem_Icc.1

中文:
定理 nonneg
  结论: 0 <= f x
  证明: f.mem_Icc.1

Depends on / 依赖: f.mem_Icc, mem_Icc
-/
theorem nonneg : 0 <= f x :=
  f.mem_Icc.1

/--
theorem `le_one` / 定理 `le_one`

English:
theorem le_one
  statement: f x <= 1
  proof: f.mem_Icc.2

中文:
定理 le_one
  结论: f x <= 1
  证明: f.mem_Icc.2

Depends on / 依赖: f.mem_Icc, mem_Icc
-/
theorem le_one : f x <= 1 :=
  f.mem_Icc.2

/--
theorem `eventuallyEq_one_of_dist_lt` / 定理 `eventuallyEq_one_of_dist_lt`

English:
theorem eventuallyEq_one_of_dist_lt
  statement: (hs : x in (chartAt H c).source)
  proof: by
  filter_upwards [IsOpen.mem_nhds (isOpen_extChartAt_preimage c isOpen_ball) ⟨hs, hd⟩]
  rintro z ⟨hzs, hzd⟩
exact f.one_of_dist_le hzs le_of_lt hzd

中文:
定理 eventuallyEq_one_of_dist_lt
  结论: (hs : x in (chartAt H c).source)
  证明: by
  filter_upwards [IsOpen.mem_nhds (isOpen_extChartAt_preimage c isOpen_ball) ⟨hs, hd⟩]
  rintro z ⟨hzs, hzd⟩
exact f.one_of_dist_le hzs le_of_lt hzd

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, f.one_of_dist_le, filter_upwards, isOpen_ball, isOpen_extChartAt_preimage, le_of_lt, mem_nhds, one_of_dist_le
-/
theorem eventuallyEq_one_of_dist_lt (hs : x in (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) < f.rIn) : f =ᶠ[𝓝 x] 1 := by
  filter_upwards [IsOpen.mem_nhds (isOpen_extChartAt_preimage c isOpen_ball) ⟨hs, hd⟩]
  rintro z ⟨hzs, hzd⟩
exact f.one_of_dist_le hzs le_of_lt hzd

/--
theorem `eventuallyEq_one` / 定理 `eventuallyEq_one`

English:
theorem eventuallyEq_one
  statement: f =ᶠ[𝓝 c] 1
  proof: f.eventuallyEq_one_of_dist_lt (mem_chart_source _ _) by rw [dist_self]; exact f.rIn_pos

@[simp]

中文:
定理 eventuallyEq_one
  结论: f =ᶠ[𝓝 c] 1
  证明: f.eventuallyEq_one_of_dist_lt (mem_chart_source _ _) by rw [dist_self]; exact f.rIn_pos

@[simp]

Depends on / 依赖: dist_self, eventuallyEq_one_of_dist_lt, f.eventuallyEq_one_of_dist_lt, f.rIn_pos, mem_chart_source, rIn_pos
-/
theorem eventuallyEq_one : f =ᶠ[𝓝 c] 1 :=
f.eventuallyEq_one_of_dist_lt (mem_chart_source _ _) by rw [dist_self]; exact f.rIn_pos

@[simp]
/--
theorem `eq_one` / 定理 `eq_one`

English:
theorem eq_one
  statement: f c = 1
  proof: f.eventuallyEq_one.eq_of_nhds

中文:
定理 eq_one
  结论: f c = 1
  证明: f.eventuallyEq_one.eq_of_nhds

Depends on / 依赖: eq_of_nhds, eventuallyEq_one, f.eventuallyEq_one.eq_of_nhds
-/
theorem eq_one : f c = 1 :=
  f.eventuallyEq_one.eq_of_nhds

/--
theorem `support_mem_nhds` / 定理 `support_mem_nhds`

English:
theorem support_mem_nhds
  statement: support f in 𝓝 c
  proof: f.eventuallyEq_one.mono fun x hx => by rw [hx]; exact one_ne_zero

中文:
定理 support_mem_nhds
  结论: support f in 𝓝 c
  证明: f.eventuallyEq_one.mono fun x hx => by rw [hx]; exact one_ne_zero

Depends on / 依赖: eventuallyEq_one, f.eventuallyEq_one.mono, one_ne_zero
-/
theorem support_mem_nhds : support f in 𝓝 c :=
  f.eventuallyEq_one.mono fun x hx => by rw [hx]; exact one_ne_zero

/--
theorem `tsupport_mem_nhds` / 定理 `tsupport_mem_nhds`

English:
theorem tsupport_mem_nhds
  statement: tsupport f in 𝓝 c
  proof: mem_of_superset f.support_mem_nhds subset_closure

中文:
定理 tsupport_mem_nhds
  结论: tsupport f in 𝓝 c
  证明: mem_of_superset f.support_mem_nhds subset_closure

Depends on / 依赖: f.support_mem_nhds, mem_of_superset, subset_closure, support_mem_nhds
-/
theorem tsupport_mem_nhds : tsupport f in 𝓝 c :=
  mem_of_superset f.support_mem_nhds subset_closure

/--
theorem `c_mem_support` / 定理 `c_mem_support`

English:
theorem c_mem_support
  statement: c in support f
  proof: mem_of_mem_nhds f.support_mem_nhds

中文:
定理 c_mem_support
  结论: c in support f
  证明: mem_of_mem_nhds f.support_mem_nhds

Depends on / 依赖: f.support_mem_nhds, mem_of_mem_nhds, support_mem_nhds
-/
theorem c_mem_support : c in support f :=
  mem_of_mem_nhds f.support_mem_nhds

/--
theorem `nonempty_support` / 定理 `nonempty_support`

English:
theorem nonempty_support
  statement: (support f).Nonempty
  proof: ⟨c, f.c_mem_support⟩

中文:
定理 nonempty_support
  结论: (support f).非空
  证明: ⟨c, f.c_mem_support⟩

Depends on / 依赖: c_mem_support, f.c_mem_support
-/
theorem nonempty_support : (support f).Nonempty :=
  ⟨c, f.c_mem_support⟩

/--
theorem `isCompact_symm_image_closedBall` / 定理 `isCompact_symm_image_closedBall`

English:
theorem isCompact_symm_image_closedBall
  proof: ((isCompact_closedBall _ _).inter_right I.isClosed_range).image_of_continuousOn
    (continuousOn_extChartAt_symm _).mono f.closedBall_subset

中文:
定理 isCompact_symm_image_closedBall
  证明: ((isCompact_closedBall _ _).inter_right I.isClosed_range).image_of_continuousOn
    (continuousOn_extChartAt_symm _).mono f.closedBall_subset

Depends on / 依赖: I.isClosed_range, closedBall_subset, continuousOn_extChartAt_symm, f.closedBall_subset, image_of_continuousOn, inter_right, isClosed_range, isCompact_closedBall
-/
theorem isCompact_symm_image_closedBall :
    IsCompact ((extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut inter range I)) :=
((isCompact_closedBall _ _).inter_right I.isClosed_range).image_of_continuousOn
    (continuousOn_extChartAt_symm _).mono f.closedBall_subset

end FiniteDimensional

/--
theorem `nhdsWithin_range_basis` / 定理 `nhdsWithin_range_basis`

English:
theorem nhdsWithin_range_basis
  proof: by
  refine ((nhdsWithin_hasBasis nhds_basis_closedBall _).restrict_subset
    (extChartAt_target_mem_nhdsWithin _)).to_hasBasis' ?_ ?_
  · rintro R ⟨hR0, hsub⟩
    exact ⟨⟨⟨R / 2, R, half_pos hR0, half_lt_self hR0⟩, hsub⟩, trivial, Subset.rfl⟩
  · exact fun f _ => inter_mem (mem_nhdsWithin_of_mem_n

中文:
定理 nhdsWithin_range_basis
  证明: by
  refine ((nhdsWithin_hasBasis nhds_basis_closedBall _).restrict_subset
    (extChartAt_target_mem_nhdsWithin _)).to_hasBasis' ?_ ?_
  · rintro R ⟨hR0, hsub⟩
    exact ⟨⟨⟨R / 2, R, half_pos hR0, half_lt_self hR0⟩, hsub⟩, trivial, Subset.rfl⟩
  · exact fun f _ => inter_mem (mem_nhdsWithin_of_mem_n

Depends on / 依赖: Subset, Subset.rfl, closedBall_mem_nhds, extChartAt_target_mem_nhdsWithin, f.rOut_pos, half_lt_self, half_pos, inter_mem, mem_nhdsWithin_of_mem_nhds, nhdsWithin_hasBasis, nhds_basis_closedBall, rOut_pos, restrict_subset, self_mem_nhdsWithin, to_hasBasis
-/
theorem nhdsWithin_range_basis :
    (𝓝[range I] extChartAt I c c).HasBasis (fun _ : SmoothBumpFunction I c => True) fun f =>
      closedBall (extChartAt I c c) f.rOut inter range I := by
  refine ((nhdsWithin_hasBasis nhds_basis_closedBall _).restrict_subset
    (extChartAt_target_mem_nhdsWithin _)).to_hasBasis' ?_ ?_
  · rintro R ⟨hR0, hsub⟩
    exact ⟨⟨⟨R / 2, R, half_pos hR0, half_lt_self hR0⟩, hsub⟩, trivial, Subset.rfl⟩
  · exact fun f _ => inter_mem (mem_nhdsWithin_of_mem_nhds <| closedBall_mem_nhds _ f.rOut_pos)
      self_mem_nhdsWithin

variable [FiniteDimensional Real E]

/--
theorem `isClosed_image_of_isClosed` / 定理 `isClosed_image_of_isClosed`

English:
theorem isClosed_image_of_isClosed
  given: {s : Set M} (hsc : IsClosed s) (hs : s subseteq support f)
  proof: by
  rw [f.image_eq_inter_preimage_of_subset_support hs]
  refine ContinuousOn.preimage_isClosed_of_isClosed
    ((continuousOn_extChartAt_symm _).mono f.closedBall_subset) ?_ hsc
  exact IsClosed.inter isClosed_closedBall I.isClosed_range

中文:
定理 isClosed_image_of_isClosed
  条件: {s : 集合 M} (hsc : 是闭集 s) (hs : s subseteq support f)
  证明: by
  rw [f.image_eq_inter_preimage_of_subset_support hs]
  refine ContinuousOn.preimage_isClosed_of_isClosed
    ((continuousOn_extChartAt_symm _).mono f.closedBall_subset) ?_ hsc
  exact IsClosed.inter isClosed_closedBall I.isClosed_range

Depends on / 依赖: ContinuousOn, ContinuousOn.preimage_isClosed_of_isClosed, I.isClosed_range, IsClosed, IsClosed.inter, closedBall_subset, continuousOn_extChartAt_symm, f.closedBall_subset, f.image_eq_inter_preimage_of_subset_support, image_eq_inter_preimage_of_subset_support, isClosed_closedBall, isClosed_range, preimage_isClosed_of_isClosed
-/
theorem isClosed_image_of_isClosed {s : Set M} (hsc : IsClosed s) (hs : s subseteq support f) :
    IsClosed (extChartAt I c '' s) := by
  rw [f.image_eq_inter_preimage_of_subset_support hs]
  refine ContinuousOn.preimage_isClosed_of_isClosed
    ((continuousOn_extChartAt_symm _).mono f.closedBall_subset) ?_ hsc
  exact IsClosed.inter isClosed_closedBall I.isClosed_range

/--
theorem `exists_r_pos_lt_subset_ball` / 定理 `exists_r_pos_lt_subset_ball`

English:
theorem exists_r_pos_lt_subset_ball
  given: {s : Set M} (hsc : IsClosed s) (hs : s subseteq support f)
  proof: by
  set e := extChartAt I c
  have : IsClosed (e '' s) := f.isClosed_image_of_isClosed hsc hs
  rw [support_eq_inter_preimage]; rw [subset_inter_iff]; rw [← image_subset_iff] at hs
  rcases exists_pos_lt_subset_ball f.rOut_pos this hs.2 with ⟨r, hrR, hr⟩
  exact ⟨r, hrR, subset_inter hs.1 (image_su

中文:
定理 存在_r_pos_lt_subset_ball
  条件: {s : 集合 M} (hsc : 是闭集 s) (hs : s subseteq support f)
  证明: by
  set e := extChartAt I c
  have : IsClosed (e '' s) := f.isClosed_image_of_isClosed hsc hs
  rw [support_eq_inter_preimage]; rw [subset_inter_iff]; rw [← image_subset_iff] at hs
  rcases exists_pos_lt_subset_ball f.rOut_pos this hs.2 with ⟨r, hrR, hr⟩
  exact ⟨r, hrR, subset_inter hs.1 (image_su

Depends on / 依赖: IsClosed, exists_pos_lt_subset_ball, extChartAt, f.isClosed_image_of_isClosed, f.rOut_pos, image_subset_iff, isClosed_image_of_isClosed, rOut_pos, subset_inter, subset_inter_iff, support_eq_inter_preimage
-/
theorem exists_r_pos_lt_subset_ball {s : Set M} (hsc : IsClosed s) (hs : s subseteq support f) :
    exists r in Ioo 0 f.rOut,
      s subseteq (chartAt H c).source inter extChartAt I c ⁻¹' ball (extChartAt I c c) r := by
  set e := extChartAt I c
  have : IsClosed (e '' s) := f.isClosed_image_of_isClosed hsc hs
  rw [support_eq_inter_preimage]; rw [subset_inter_iff]; rw [← image_subset_iff] at hs
  rcases exists_pos_lt_subset_ball f.rOut_pos this hs.2 with ⟨r, hrR, hr⟩
  exact ⟨r, hrR, subset_inter hs.1 (image_subset_iff.1 hr)⟩

/-- Replace `rIn` with another value in the interval `(0, f.rOut)`. -/
@[simps rOut rIn]
/--
Definition of `updateRIn` / `updateRIn` 的定义

English:
definition updateRIn
  signature: (r : Real) (hr : r in Ioo 0 f.rOut)
  body: ⟨⟨r, f.rOut, hr.1, hr.2⟩, f.closedBall_subset⟩

@[simp]

中文:
定义 updateRIn
  签名: (r : 实数) (hr : r in 开区间 0 f.rOut)
  定义体: ⟨⟨r, f.rOut, hr.1, hr.2⟩, f.closedBall_subset⟩

@[simp]

Depends on / 依赖: closedBall_subset, f.closedBall_subset, f.rOut
-/
def updateRIn (r : Real) (hr : r in Ioo 0 f.rOut) : SmoothBumpFunction I c :=
  ⟨⟨r, f.rOut, hr.1, hr.2⟩, f.closedBall_subset⟩

@[simp]
/--
theorem `support_updateRIn` / 定理 `support_updateRIn`

English:
theorem support_updateRIn
  given: {r : Real} (hr : r in Ioo 0 f.rOut)
  proof: by
  simp only [support_eq_inter_preimage, updateRIn_rOut]

中文:
定理 support_updateRIn
  条件: {r : 实数} (hr : r in 开区间 0 f.rOut)
  证明: by
  simp only [support_eq_inter_preimage, updateRIn_rOut]

Depends on / 依赖: support_eq_inter_preimage, updateRIn_rOut
-/
theorem support_updateRIn {r : Real} (hr : r in Ioo 0 f.rOut) :
    support (f.updateRIn r hr) = support f := by
  simp only [support_eq_inter_preimage, updateRIn_rOut]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (SmoothBumpFunction I c)
  body: nhdsWithin_range_basis.nonempty

中文:
实例 :
  签名: 非空 (光滑凸函数 I c)
  定义体: nhdsWithin_range_basis.nonempty

Depends on / 依赖: nhdsWithin_range_basis, nhdsWithin_range_basis.nonempty, nonempty
-/
instance : Nonempty (SmoothBumpFunction I c) := nhdsWithin_range_basis.nonempty

variable [T2Space M]

/--
theorem `isClosed_symm_image_closedBall` / 定理 `isClosed_symm_image_closedBall`

English:
theorem isClosed_symm_image_closedBall
  proof: f.isCompact_symm_image_closedBall.isClosed

中文:
定理 isClosed_symm_image_closedBall
  证明: f.isCompact_symm_image_closedBall.isClosed

Depends on / 依赖: f.isCompact_symm_image_closedBall.isClosed, isClosed, isCompact_symm_image_closedBall
-/
theorem isClosed_symm_image_closedBall :
    IsClosed ((extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut inter range I)) :=
  f.isCompact_symm_image_closedBall.isClosed

/--
theorem `tsupport_subset_symm_image_closedBall` / 定理 `tsupport_subset_symm_image_closedBall`

English:
theorem tsupport_subset_symm_image_closedBall
  proof: by
  rw [tsupport]; rw [support_eq_symm_image]
  exact closure_minimal (image_mono <| inter_subset_inter_left _ ball_subset_closedBall)
    f.isClosed_symm_image_closedBall

中文:
定理 tsupport_subset_symm_image_closedBall
  证明: by
  rw [tsupport]; rw [support_eq_symm_image]
  exact closure_minimal (image_mono <| inter_subset_inter_left _ ball_subset_closedBall)
    f.isClosed_symm_image_closedBall

Depends on / 依赖: ball_subset_closedBall, closure_minimal, f.isClosed_symm_image_closedBall, image_mono, inter_subset_inter_left, isClosed_symm_image_closedBall, support_eq_symm_image, tsupport
-/
theorem tsupport_subset_symm_image_closedBall :
    tsupport f subseteq (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut inter range I) := by
  rw [tsupport]; rw [support_eq_symm_image]
  exact closure_minimal (image_mono <| inter_subset_inter_left _ ball_subset_closedBall)
    f.isClosed_symm_image_closedBall

/--
theorem `tsupport_subset_extChartAt_source` / 定理 `tsupport_subset_extChartAt_source`

English:
theorem tsupport_subset_extChartAt_source
  statement: tsupport f subseteq (extChartAt I c).source
  proof: calc
    tsupport f subseteq (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut inter range I) :=
      f.tsupport_subset_symm_image_closedBall
    _ subseteq (extChartAt I c).symm '' (extChartAt I c).target := image_mono f.closedBall_subset
    _ = (extChartAt I c).source := (extChartAt

中文:
定理 tsupport_subset_extChartAt_source
  结论: tsupport f subseteq (extChartAt I c).source
  证明: calc
    tsupport f subseteq (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut inter range I) :=
      f.tsupport_subset_symm_image_closedBall
    _ subseteq (extChartAt I c).symm '' (extChartAt I c).target := image_mono f.closedBall_subset
    _ = (extChartAt I c).source := (extChartAt

Depends on / 依赖: closedBall, closedBall_subset, extChartAt, f.closedBall_subset, f.rOut, f.tsupport_subset_symm_image_closedBall, image_mono, source, subseteq, symm_image_target_eq_source, target, tsupport, tsupport_subset_symm_image_closedBall
-/
theorem tsupport_subset_extChartAt_source : tsupport f subseteq (extChartAt I c).source :=
  calc
    tsupport f subseteq (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut inter range I) :=
      f.tsupport_subset_symm_image_closedBall
    _ subseteq (extChartAt I c).symm '' (extChartAt I c).target := image_mono f.closedBall_subset
    _ = (extChartAt I c).source := (extChartAt I c).symm_image_target_eq_source

/--
theorem `tsupport_subset_chartAt_source` / 定理 `tsupport_subset_chartAt_source`

English:
theorem tsupport_subset_chartAt_source
  statement: tsupport f subseteq (chartAt H c).source
  proof: by
  simpa only [extChartAt_source] using f.tsupport_subset_extChartAt_source

中文:
定理 tsupport_subset_chartAt_source
  结论: tsupport f subseteq (chartAt H c).source
  证明: by
  simpa only [extChartAt_source] using f.tsupport_subset_extChartAt_source

Depends on / 依赖: extChartAt_source, f.tsupport_subset_extChartAt_source, tsupport_subset_extChartAt_source
-/
theorem tsupport_subset_chartAt_source : tsupport f subseteq (chartAt H c).source := by
  simpa only [extChartAt_source] using f.tsupport_subset_extChartAt_source

/--
theorem `hasCompactSupport` / 定理 `hasCompactSupport`

English:
theorem hasCompactSupport
  statement: HasCompactSupport f
  proof: f.isCompact_symm_image_closedBall.of_isClosed_subset isClosed_closure
    f.tsupport_subset_symm_image_closedBall

中文:
定理 hasCompactSupport
  结论: HasCompactSupport f
  证明: f.isCompact_symm_image_closedBall.of_isClosed_subset isClosed_closure
    f.tsupport_subset_symm_image_closedBall
-/
protected theorem hasCompactSupport : HasCompactSupport f :=
  f.isCompact_symm_image_closedBall.of_isClosed_subset isClosed_closure
    f.tsupport_subset_symm_image_closedBall

variable (c) in
/--
theorem `nhds_basis_tsupport` / 定理 `nhds_basis_tsupport`

English:
theorem nhds_basis_tsupport
  proof: by
  have :
    (𝓝 c).HasBasis (fun _ : SmoothBumpFunction I c => True) fun f =>
      (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut inter range I) := by
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) c]
    exact nhdsWithin_range_basis.map _
  exact this.to_hasBasis' (fun 

中文:
定理 nhds_basis_tsupport
  证明: by
  have :
    (𝓝 c).HasBasis (fun _ : SmoothBumpFunction I c => True) fun f =>
      (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut inter range I) := by
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) c]
    exact nhdsWithin_range_basis.map _
  exact this.to_hasBasis' (fun 

Depends on / 依赖: HasBasis, SmoothBumpFunction, closedBall, extChartAt, f.rOut, f.tsupport_mem_nhds, f.tsupport_subset_symm_image_closedBall, map_extChartAt_symm_nhdsWithin_range, nhdsWithin_range_basis, nhdsWithin_range_basis.map, this.to_hasBasis, to_hasBasis, tsupport_mem_nhds, tsupport_subset_symm_image_closedBall
-/
theorem nhds_basis_tsupport :
    (𝓝 c).HasBasis (fun _ : SmoothBumpFunction I c => True) fun f => tsupport f := by
  have :
    (𝓝 c).HasBasis (fun _ : SmoothBumpFunction I c => True) fun f =>
      (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut inter range I) := by
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) c]
    exact nhdsWithin_range_basis.map _
  exact this.to_hasBasis' (fun f _ => ⟨f, trivial, f.tsupport_subset_symm_image_closedBall⟩)
    fun f _ => f.tsupport_mem_nhds

/--
theorem `nhds_basis_support` / 定理 `nhds_basis_support`

English:
theorem nhds_basis_support
  given: {s : Set M} (hs : s in 𝓝 c)
  proof: ((nhds_basis_tsupport c).restrict_subset hs).to_hasBasis'
    (fun f hf => ⟨f, hf.2, subset_closure⟩) fun f _ => f.support_mem_nhds

中文:
定理 nhds_basis_support
  条件: {s : 集合 M} (hs : s in 𝓝 c)
  证明: ((nhds_basis_tsupport c).restrict_subset hs).to_hasBasis'
    (fun f hf => ⟨f, hf.2, subset_closure⟩) fun f _ => f.support_mem_nhds

Depends on / 依赖: f.support_mem_nhds, nhds_basis_tsupport, restrict_subset, subset_closure, support_mem_nhds, to_hasBasis
-/
theorem nhds_basis_support {s : Set M} (hs : s in 𝓝 c) :
    (𝓝 c).HasBasis (fun f : SmoothBumpFunction I c => tsupport f subseteq s) fun f => support f :=
  ((nhds_basis_tsupport c).restrict_subset hs).to_hasBasis'
    (fun f hf => ⟨f, hf.2, subset_closure⟩) fun f _ => f.support_mem_nhds

variable [IsManifold I ∞ M]

/--
theorem `contMDiff` / 定理 `contMDiff`

English:
theorem contMDiff
  statement: CMDiff ∞ f
  proof: by
  refine contMDiff_of_tsupport fun x hx => ?_
  have : x in (chartAt H c).source := f.tsupport_subset_chartAt_source hx
refine ContMDiffAt.congr_of_eventuallyEq ?_ f.eqOn_source.eventuallyEq_of_mem
    (chartAt H c).open_source.mem_nhds this
  exact f.contDiffAt.contMDiffAt.comp _ (contMDiffAt_ex

中文:
定理 contMDiff
  结论: CMDiff ∞ f
  证明: by
  refine contMDiff_of_tsupport fun x hx => ?_
  have : x in (chartAt H c).source := f.tsupport_subset_chartAt_source hx
refine ContMDiffAt.congr_of_eventuallyEq ?_ f.eqOn_source.eventuallyEq_of_mem
    (chartAt H c).open_source.mem_nhds this
  exact f.contDiffAt.contMDiffAt.comp _ (contMDiffAt_ex
-/
protected theorem contMDiff : CMDiff ∞ f := by
  refine contMDiff_of_tsupport fun x hx => ?_
  have : x in (chartAt H c).source := f.tsupport_subset_chartAt_source hx
refine ContMDiffAt.congr_of_eventuallyEq ?_ f.eqOn_source.eventuallyEq_of_mem
    (chartAt H c).open_source.mem_nhds this
  exact f.contDiffAt.contMDiffAt.comp _ (contMDiffAt_extChartAt' this)

/--
theorem `contMDiffAt` / 定理 `contMDiffAt`

English:
theorem contMDiffAt
  given: {x}
  statement: CMDiffAt ∞ f x
  proof: f.contMDiff.contMDiffAt

中文:
定理 contMDiffAt
  条件: {x}
  结论: CMDiffAt ∞ f x
  证明: f.contMDiff.contMDiffAt
-/
protected theorem contMDiffAt {x} : CMDiffAt ∞ f x :=
  f.contMDiff.contMDiffAt

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  statement: Continuous f
  proof: f.contMDiff.continuous

中文:
定理 continuous
  结论: 连续 f
  证明: f.contMDiff.continuous
-/
protected theorem continuous : Continuous f :=
  f.contMDiff.continuous

/--
theorem `contMDiff_smul` / 定理 `contMDiff_smul`

English:
theorem contMDiff_smul
  statement: {G} [NormedAddCommGroup G] [NormedSpace Real G] {g : M -> G}
  proof: by
  refine contMDiff_of_tsupport fun x hx => ?_
  -- Porting note: was a more readable `calc`
  -- calc
  -- x ∈ tsupport fun x => f x • g x := hx
  -- _ ⊆ tsupport f := tsupport_smul_subset_left _ _
  -- _ ⊆ (chart_at _ c).source := f.tsupport_subset_chartAt_source
  have : x in (chartAt H c).sour

中文:
定理 contMDiff_smul
  结论: {G} [赋范交换加群 G] [赋范空间 实数 G] {g : M -> G}
  证明: by
  refine contMDiff_of_tsupport fun x hx => ?_
  -- Porting note: was a more readable `calc`
  -- calc
  -- x ∈ tsupport fun x => f x • g x := hx
  -- _ ⊆ tsupport f := tsupport_smul_subset_left _ _
  -- _ ⊆ (chart_at _ c).source := f.tsupport_subset_chartAt_source
  have : x in (chartAt H c).sour

Depends on / 依赖: contMDiff_of_tsupport
-/
theorem contMDiff_smul {G} [NormedAddCommGroup G] [NormedSpace Real G] {g : M -> G}
    (hg : CMDiff[(chartAt H c).source] ∞ g) : CMDiff ∞ fun x => f x • g x := by
  refine contMDiff_of_tsupport fun x hx => ?_
  -- Porting note: was a more readable `calc`
  -- calc
  -- x ∈ tsupport fun x => f x • g x := hx
  -- _ ⊆ tsupport f := tsupport_smul_subset_left _ _
  -- _ ⊆ (chart_at _ c).source := f.tsupport_subset_chartAt_source
  have : x in (chartAt H c).source :=
f.tsupport_subset_chartAt_source tsupport_smul_subset_left _ _ hx
  exact f.contMDiffAt.smul ((hg _ this).contMDiffAt <| (chartAt _ _).open_source.mem_nhds this)

end SmoothBumpFunction
