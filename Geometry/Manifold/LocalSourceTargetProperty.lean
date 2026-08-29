/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! # Local properties of smooth functions which depend on both the source and target

In this file, we consider local properties of functions between manifolds, which depend on both the
source and the target: more precisely, properties `P` of functions `f : M → N` such that
`f` has property `P` if and only if there is a suitable pair of charts on `M` and `N`, respectively,
such that `f` read in these charts has a particular form.
The motivating examples of this general description are immersions and submersions:
`f : M → N` is an immersion at `x` iff there are charts `φ` and `ψ` of `M` and `N` around `x` and
`f x`, respectively, such that in these charts, `f` looks like `u ↦ (u, 0)`. Similarly, `f` is a
submersion at `x` iff it looks like a projection `(u, v) ↦ u` in suitable charts near `x` and `f x`.

Studying such local properties allows proving several lemmas about immersions and submersions
only once. In `IsImmersionEmbedding.lean`, we prove that being an immersion at `x` is indeed a
local property of this form.

## Main definitions and results

* `Manifold.LocalSourceTargetPropertyAt` captures a local property of the above form:
  for each `f : M → N`, and pair of charts `φ` of `M` and `ψ` of `N`, the local property is either
  satisfied or not.
  We ask that the property be stable under congruence and under restriction of `φ`.
* `Manifold.LiftSourceTargetPropertyAt f x P`, where `P` is a `LocalSourceTargetPropertyAt`,
  defines a local property of functions of the above shape:
  `f` has this property at `x` if there exist charts `φ` and `ψ` such that `P f φ ψ` holds.
* `Manifold.LiftSourceTargetPropertyAt.congr_of_eventuallyEq`: if `f` has property `P` at `x`
  and `g` equals `f` near `x`, then `g` also has property `P` at `x`.
* `IsOpen.liftSourceTargetPropertyAt`: the set of points at which `LiftSourceTargetPropertyAt`
  holds is open

-/

public section

open scoped Manifold Topology ContDiff

open Function Set

variable {𝕜 E E' F F' H H' G G' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F' G'}
  {M M' N N' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : Nat∞ω}

namespace Manifold

/--
Definition of `IsLocalSourceTargetProperty` / `IsLocalSourceTargetProperty` 的定义

English:
structure IsLocalSourceTargetProperty
  axioms and operations (2):
    - mono_source : forall {f : M -> N}, forall {φ : OpenPartialHomeomorph M H}, forall {ψ : OpenPartialHomeomorph N G}, forall {s : Set M}, IsOpen s -> P f φ ψ -> P f (φ.restr s) ψ
    - congr : forall {f g : M -> N}, forall {φ : OpenPartialHomeomorph M H}, forall {ψ : OpenPartialHomeomorph N G}, EqOn f g φ.source -> P f φ ψ -> P g φ ψ

中文:
结构 是LocalSourceTargetProperty
  公理与运算 (2 个):
    - mono_source : 对任意 {f : M -> N}, 对任意 {φ : OpenPartialHomeomorph M H}, 对任意 {ψ : OpenPartialHomeomorph N G}, 对任意 {s : 集合 M}, 是开集 s -> P f φ ψ -> P f (φ.restr s) ψ
    - congr : 对任意 {f g : M -> N}, 对任意 {φ : OpenPartialHomeomorph M H}, 对任意 {ψ : OpenPartialHomeomorph N G}, EqOn f g φ.source -> P f φ ψ -> P g φ ψ
-/
structure IsLocalSourceTargetProperty
    (P : (M -> N) -> OpenPartialHomeomorph M H -> OpenPartialHomeomorph N G -> Prop) : Prop where
  mono_source : forall {f : M -> N}, forall {φ : OpenPartialHomeomorph M H}, forall {ψ : OpenPartialHomeomorph N G},
    forall {s : Set M}, IsOpen s -> P f φ ψ -> P f (φ.restr s) ψ
  -- Note: the analogous `mono_target` statement is true for both immersions and submersions.
  -- If and when a future lemma requires it, add this here.
  congr : forall {f g : M -> N}, forall {φ : OpenPartialHomeomorph M H}, forall {ψ : OpenPartialHomeomorph N G},
    EqOn f g φ.source -> P f φ ψ -> P g φ ψ

variable (I J n) in
/--
Definition of `LocalPresentationAt` / `LocalPresentationAt` 的定义

English:
structure LocalPresentationAt
  parameters: (f : M -> N) (x : M)
  axioms and operations (8):
    - domChart : OpenPartialHomeomorph M H
    - codChart : OpenPartialHomeomorph N G
    - mem_domChart_source : x in domChart.source
    - mem_codChart_source : f x in codChart.source
    - domChart_mem_maximalAtlas : domChart in IsManifold.maximalAtlas I n M
    - codChart_mem_maximalAtlas : codChart in IsManifold.maximalAtlas J n N
    - source_subset_preimage_source : domChart.source subseteq f ⁻¹' codChart.source
    - property : P f domChart codChart

中文:
结构 LocalPresentationAt
  参数: (f : M -> N) (x : M)
  公理与运算 (8 个):
    - domChart : OpenPartialHomeomorph M H
    - codChart : OpenPartialHomeomorph N G
    - mem_domChart_source : x in domChart.source
    - mem_codChart_source : f x in codChart.source
    - domChart_mem_maximalAtlas : domChart in 是流形.maximalAtlas I n M
    - codChart_mem_maximalAtlas : codChart in 是流形.maximalAtlas J n N
    - source_subset_preimage_source : domChart.source subseteq f ⁻¹' codChart.source
    - property : P f domChart codChart
-/
structure LocalPresentationAt (f : M -> N) (x : M)
    (P : (M -> N) -> OpenPartialHomeomorph M H -> OpenPartialHomeomorph N G -> Prop) where
  /-- A choice of chart on the domain `M` of the local property `P` of `f` at `x`:
  w.r.t. this chart and `codChart`, `f` has the local property `P` at `x`. -/
  domChart : OpenPartialHomeomorph M H
  /-- A choice of chart on the target `N` of the local property `P` of `f` at `x`:
  w.r.t. this chart and `domChart`, `f` has the local property `P` at `x`. -/
  codChart : OpenPartialHomeomorph N G
  mem_domChart_source : x in domChart.source
  mem_codChart_source : f x in codChart.source
  domChart_mem_maximalAtlas : domChart in IsManifold.maximalAtlas I n M
  codChart_mem_maximalAtlas : codChart in IsManifold.maximalAtlas J n N
  source_subset_preimage_source : domChart.source subseteq f ⁻¹' codChart.source
  property : P f domChart codChart

variable (I J n) in
/-- The induced property by a local property `P`: it is satisfied for `f` at `x` iff there exist
charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively, such that `f` satisfies `P`
w.r.t. `φ` and `ψ`.

The motivating examples are smooth immersions and submersions: the corresponding condition is that
`f` look like the inclusion `u ↦ (u, 0)` (resp. a projection `(u, v) ↦ u`)
in the charts `φ` and `ψ`.
-/
@[expose]
/--
Definition of `LiftSourceTargetPropertyAt` / `LiftSourceTargetPropertyAt` 的定义

English:
definition LiftSourceTargetPropertyAt
  signature: (f : M -> N) (x : M)
  body: Nonempty (LocalPresentationAt I J n f x P)

中文:
定义 LiftSourceTargetPropertyAt
  签名: (f : M -> N) (x : M)
  定义体: Nonempty (LocalPresentationAt I J n f x P)

Depends on / 依赖: LocalPresentationAt, Nonempty
-/
def LiftSourceTargetPropertyAt (f : M -> N) (x : M)
    (P : (M -> N) -> OpenPartialHomeomorph M H -> OpenPartialHomeomorph N G -> Prop) : Prop :=
  Nonempty (LocalPresentationAt I J n f x P)

namespace LocalPresentationAt

variable {f g : M -> N} {x : M}
  {P : (M -> N) -> OpenPartialHomeomorph M H -> OpenPartialHomeomorph N G -> Prop}

/--
lemma `mapsto_domChart_source_codChart_source` / 引理 `mapsto_domChart_source_codChart_source`

English:
lemma mapsto_domChart_source_codChart_source
  given: (h : LocalPresentationAt I J n f x P)
  proof: h.source_subset_preimage_source

中文:
引理 mapsto_domChart_source_codChart_source
  条件: (h : LocalPresentationAt I J n f x P)
  证明: h.source_subset_preimage_source

Depends on / 依赖: h.source_subset_preimage_source, source_subset_preimage_source
-/
lemma mapsto_domChart_source_codChart_source (h : LocalPresentationAt I J n f x P) :
    MapsTo f h.domChart.source h.codChart.source :=
  h.source_subset_preimage_source

end LocalPresentationAt

namespace LiftSourceTargetPropertyAt

variable {f g : M -> N} {x : M}
  {P : (M -> N) -> OpenPartialHomeomorph M H -> OpenPartialHomeomorph N G -> Prop}

/--
Definition of `localPresentationAt` / `localPresentationAt` 的定义

English:
definition localPresentationAt
  signature: (h : LiftSourceTargetPropertyAt I J n f x P)
  body: Classical.choice h

中文:
定义 localPresentationAt
  签名: (h : LiftSourceTargetPropertyAt I J n f x P)
  定义体: Classical.choice h

Depends on / 依赖: Classical, Classical.choice, choice
-/
noncomputable def localPresentationAt (h : LiftSourceTargetPropertyAt I J n f x P) :
    LocalPresentationAt I J n f x P :=
  Classical.choice h

/--
Definition of `domChart` / `domChart` 的定义

English:
definition domChart
  signature: (h : LiftSourceTargetPropertyAt I J n f x P)
  body: h.localPresentationAt.domChart

中文:
定义 domChart
  签名: (h : LiftSourceTargetPropertyAt I J n f x P)
  定义体: h.localPresentationAt.domChart

Depends on / 依赖: domChart, h.localPresentationAt.domChart, localPresentationAt
-/
noncomputable def domChart (h : LiftSourceTargetPropertyAt I J n f x P) :
    OpenPartialHomeomorph M H :=
  h.localPresentationAt.domChart

/--
Definition of `codChart` / `codChart` 的定义

English:
definition codChart
  signature: (h : LiftSourceTargetPropertyAt I J n f x P)
  body: h.localPresentationAt.codChart

中文:
定义 codChart
  签名: (h : LiftSourceTargetPropertyAt I J n f x P)
  定义体: h.localPresentationAt.codChart

Depends on / 依赖: codChart, h.localPresentationAt.codChart, localPresentationAt
-/
noncomputable def codChart (h : LiftSourceTargetPropertyAt I J n f x P) :
    OpenPartialHomeomorph N G :=
  h.localPresentationAt.codChart

/--
lemma `mem_domChart_source` / 引理 `mem_domChart_source`

English:
lemma mem_domChart_source
  given: (h : LiftSourceTargetPropertyAt I J n f x P)
  proof: h.localPresentationAt.mem_domChart_source

中文:
引理 mem_domChart_source
  条件: (h : LiftSourceTargetPropertyAt I J n f x P)
  证明: h.localPresentationAt.mem_domChart_source

Depends on / 依赖: h.localPresentationAt.mem_domChart_source, localPresentationAt, mem_domChart_source
-/
lemma mem_domChart_source (h : LiftSourceTargetPropertyAt I J n f x P) :
    x in h.domChart.source :=
  h.localPresentationAt.mem_domChart_source

/--
lemma `mem_codChart_source` / 引理 `mem_codChart_source`

English:
lemma mem_codChart_source
  given: (h : LiftSourceTargetPropertyAt I J n f x P)
  proof: h.localPresentationAt.mem_codChart_source

中文:
引理 mem_codChart_source
  条件: (h : LiftSourceTargetPropertyAt I J n f x P)
  证明: h.localPresentationAt.mem_codChart_source

Depends on / 依赖: h.localPresentationAt.mem_codChart_source, localPresentationAt, mem_codChart_source
-/
lemma mem_codChart_source (h : LiftSourceTargetPropertyAt I J n f x P) :
    f x in h.codChart.source :=
  h.localPresentationAt.mem_codChart_source

/--
lemma `domChart_mem_maximalAtlas` / 引理 `domChart_mem_maximalAtlas`

English:
lemma domChart_mem_maximalAtlas
  given: (h : LiftSourceTargetPropertyAt I J n f x P)
  proof: h.localPresentationAt.domChart_mem_maximalAtlas

中文:
引理 domChart_mem_maximalAtlas
  条件: (h : LiftSourceTargetPropertyAt I J n f x P)
  证明: h.localPresentationAt.domChart_mem_maximalAtlas

Depends on / 依赖: domChart_mem_maximalAtlas, h.localPresentationAt.domChart_mem_maximalAtlas, localPresentationAt
-/
lemma domChart_mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) :
    h.domChart in IsManifold.maximalAtlas I n M :=
  h.localPresentationAt.domChart_mem_maximalAtlas

/--
lemma `codChart_mem_maximalAtlas` / 引理 `codChart_mem_maximalAtlas`

English:
lemma codChart_mem_maximalAtlas
  given: (h : LiftSourceTargetPropertyAt I J n f x P)
  proof: h.localPresentationAt.codChart_mem_maximalAtlas

中文:
引理 codChart_mem_maximalAtlas
  条件: (h : LiftSourceTargetPropertyAt I J n f x P)
  证明: h.localPresentationAt.codChart_mem_maximalAtlas

Depends on / 依赖: codChart_mem_maximalAtlas, h.localPresentationAt.codChart_mem_maximalAtlas, localPresentationAt
-/
lemma codChart_mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) :
    h.codChart in IsManifold.maximalAtlas J n N :=
  h.localPresentationAt.codChart_mem_maximalAtlas

/--
lemma `source_subset_preimage_source` / 引理 `source_subset_preimage_source`

English:
lemma source_subset_preimage_source
  given: (h : LiftSourceTargetPropertyAt I J n f x P)
  proof: h.localPresentationAt.source_subset_preimage_source

中文:
引理 source_subset_preimage_source
  条件: (h : LiftSourceTargetPropertyAt I J n f x P)
  证明: h.localPresentationAt.source_subset_preimage_source

Depends on / 依赖: h.localPresentationAt.source_subset_preimage_source, localPresentationAt, source_subset_preimage_source
-/
lemma source_subset_preimage_source (h : LiftSourceTargetPropertyAt I J n f x P) :
    h.domChart.source subseteq f ⁻¹' h.codChart.source :=
  h.localPresentationAt.source_subset_preimage_source

/--
lemma `property` / 引理 `property`

English:
lemma property
  given: (h : LiftSourceTargetPropertyAt I J n f x P)
  statement: P f h.domChart h.codChart
  proof: h.localPresentationAt.property

omit [ChartedSpace H M] [ChartedSpace G N] in

中文:
引理 property
  条件: (h : LiftSourceTargetPropertyAt I J n f x P)
  结论: P f h.domChart h.codChart
  证明: h.localPresentationAt.property

omit [ChartedSpace H M] [ChartedSpace G N] in

Depends on / 依赖: h.localPresentationAt.property, localPresentationAt, property
-/
lemma property (h : LiftSourceTargetPropertyAt I J n f x P) : P f h.domChart h.codChart :=
  h.localPresentationAt.property

omit [ChartedSpace H M] [ChartedSpace G N] in
/--
lemma `congr_iff` / 引理 `congr_iff`

English:
lemma congr_iff
  statement: (hP : IsLocalSourceTargetProperty P) {f g : M -> N}
  proof: ⟨hP.congr hfg, hP.congr hfg.symm⟩

中文:
引理 congr_iff
  结论: (hP : 是LocalSourceTargetProperty P) {f g : M -> N}
  证明: ⟨hP.congr hfg, hP.congr hfg.symm⟩

Depends on / 依赖: hP.congr, hfg.symm
-/
lemma congr_iff (hP : IsLocalSourceTargetProperty P) {f g : M -> N}
    {φ : OpenPartialHomeomorph M H} {ψ : OpenPartialHomeomorph N G} (hfg : EqOn f g φ.source) :
    P f φ ψ ↔ P g φ ψ :=
  ⟨hP.congr hfg, hP.congr hfg.symm⟩

/--
lemma `mk_of_continuousAt` / 引理 `mk_of_continuousAt`

English:
lemma mk_of_continuousAt
  statement: (hf : ContinuousAt f x)
  proof: by
obtain ⟨s, hs, hsopen, hxs⟩ := mem_nhds_iff.mp
    hf.preimage_mem_nhds (codChart.open_source.mem_nhds hfx)
  exact ⟨domChart.restr s, codChart, by grind, hfx,
    restr_mem_maximalAtlas (contDiffGroupoid n I) hdomChart hsopen, hcodChart, by grind,
    hP.mono_source hsopen hfP⟩

中文:
引理 mk_of_continuousAt
  结论: (hf : ContinuousAt f x)
  证明: by
obtain ⟨s, hs, hsopen, hxs⟩ := mem_nhds_iff.mp
    hf.preimage_mem_nhds (codChart.open_source.mem_nhds hfx)
  exact ⟨domChart.restr s, codChart, by grind, hfx,
    restr_mem_maximalAtlas (contDiffGroupoid n I) hdomChart hsopen, hcodChart, by grind,
    hP.mono_source hsopen hfP⟩

Depends on / 依赖: codChart, codChart.open_source.mem_nhds, contDiffGroupoid, domChart, domChart.restr, hP.mono_source, hcodChart, hdomChart, hf.preimage_mem_nhds, hsopen, mem_nhds, mem_nhds_iff, mem_nhds_iff.mp, mono_source, open_source, preimage_mem_nhds, restr_mem_maximalAtlas
-/
lemma mk_of_continuousAt (hf : ContinuousAt f x)
    (hP : IsLocalSourceTargetProperty P)
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x in domChart.source) (hfx : f x in codChart.source)
    (hdomChart : domChart in IsManifold.maximalAtlas I n M)
    (hcodChart : codChart in IsManifold.maximalAtlas J n N)
    (hfP : P f domChart codChart) : LiftSourceTargetPropertyAt I J n f x P := by
obtain ⟨s, hs, hsopen, hxs⟩ := mem_nhds_iff.mp
    hf.preimage_mem_nhds (codChart.open_source.mem_nhds hfx)
  exact ⟨domChart.restr s, codChart, by grind, hfx,
    restr_mem_maximalAtlas (contDiffGroupoid n I) hdomChart hsopen, hcodChart, by grind,
    hP.mono_source hsopen hfP⟩

/--
lemma `congr_of_eventuallyEq` / 引理 `congr_of_eventuallyEq`

English:
lemma congr_of_eventuallyEq
  statement: (hP : IsLocalSourceTargetProperty P)
  proof: by
  obtain ⟨s', hxs', hfg⟩ := h'.exists_mem
  obtain ⟨s, hss', hs, hxs⟩ := mem_nhds_iff.mp hxs'
  refine ⟨hf.domChart.restr s, hf.codChart, ?_, ?_, ?_, hf.codChart_mem_maximalAtlas, ?_, ?_⟩
  · simpa using ⟨mem_domChart_source hf, by rwa [interior_eq_iff_isOpen.mpr hs]⟩
  · exact hfg (mem_of_mem_nh

中文:
引理 congr_of_eventuallyEq
  结论: (hP : 是LocalSourceTargetProperty P)
  证明: by
  obtain ⟨s', hxs', hfg⟩ := h'.exists_mem
  obtain ⟨s, hss', hs, hxs⟩ := mem_nhds_iff.mp hxs'
  refine ⟨hf.domChart.restr s, hf.codChart, ?_, ?_, ?_, hf.codChart_mem_maximalAtlas, ?_, ?_⟩
  · simpa using ⟨mem_domChart_source hf, by rwa [interior_eq_iff_isOpen.mpr hs]⟩
  · exact hfg (mem_of_mem_nh

Depends on / 依赖: Subset, Subset.trans, codChart, codChart_mem_maximalAtlas, domChart, domChart_mem_maximalAtlas, exists_mem, hf.codChart, hf.codChart.source, hf.codChart_mem_maximalAtlas, hf.domChart.restr, hf.domChart_mem_maximalAtlas, interior_eq_iff_i, interior_eq_iff_isOpen, interior_eq_iff_isOpen.mpr, mem_codChart_source, mem_domChart_source, mem_nhds_iff, mem_nhds_iff.mp, mem_of_mem_nhds
-/
lemma congr_of_eventuallyEq (hP : IsLocalSourceTargetProperty P)
    (hf : LiftSourceTargetPropertyAt I J n f x P)
    (h' : f =ᶠ[nhds x] g) : LiftSourceTargetPropertyAt I J n g x P := by
  obtain ⟨s', hxs', hfg⟩ := h'.exists_mem
  obtain ⟨s, hss', hs, hxs⟩ := mem_nhds_iff.mp hxs'
  refine ⟨hf.domChart.restr s, hf.codChart, ?_, ?_, ?_, hf.codChart_mem_maximalAtlas, ?_, ?_⟩
  · simpa using ⟨mem_domChart_source hf, by rwa [interior_eq_iff_isOpen.mpr hs]⟩
  · exact hfg (mem_of_mem_nhds hxs') ▸ mem_codChart_source hf
  · exact restr_mem_maximalAtlas _ hf.domChart_mem_maximalAtlas hs
  · trans s' inter f ⁻¹' hf.codChart.source
    · apply subset_inter
      · exact Subset.trans (by simp [interior_eq_iff_isOpen.mpr hs]) hss'
      · exact Subset.trans (by simp) hf.source_subset_preimage_source
    · rw [hfg.inter_preimage_eq]; exact inter_subset_right
· exact hP.congr (hfg.mono hss' |>.mono (by grind)) hP.mono_source hs hf.property

/--
lemma `congr_iff_of_eventuallyEq` / 引理 `congr_iff_of_eventuallyEq`

English:
lemma congr_iff_of_eventuallyEq
  given: (hP : IsLocalSourceTargetProperty P) (h' : f =ᶠ[nhds x] g)
  proof: ⟨fun hf => hf.congr_of_eventuallyEq hP h', fun hg => hg.congr_of_eventuallyEq hP h'.symm⟩

中文:
引理 congr_iff_of_eventuallyEq
  条件: (hP : 是LocalSourceTargetProperty P) (h' : f =ᶠ[邻域滤子 x] g)
  证明: ⟨fun hf => hf.congr_of_eventuallyEq hP h', fun hg => hg.congr_of_eventuallyEq hP h'.symm⟩

Depends on / 依赖: congr_of_eventuallyEq, hf.congr_of_eventuallyEq, hg.congr_of_eventuallyEq
-/
lemma congr_iff_of_eventuallyEq (hP : IsLocalSourceTargetProperty P) (h' : f =ᶠ[nhds x] g) :
    LiftSourceTargetPropertyAt I J n f x P ↔ LiftSourceTargetPropertyAt I J n g x P :=
  ⟨fun hf => hf.congr_of_eventuallyEq hP h', fun hg => hg.congr_of_eventuallyEq hP h'.symm⟩

/--
lemma `_root_.IsOpen.liftSourceTargetPropertyAt` / 引理 `_root_.IsOpen.liftSourceTargetPropertyAt`

English:
lemma _root_.IsOpen.liftSourceTargetPropertyAt
  proof: by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  -- Suppose the lifted property `P` holds at `x`:
  -- choose slice charts `φ` near `x` and `ψ` near `f x` s.t. `P f φ ψ` holds.
  -- Then the same charts witness that `P f φ ψ` holds at any `y ∈ φ.source`.
  refine ⟨hx.domChart.source, fun y hy => 

中文:
引理 _root_.是开集.liftSourceTargetPropertyAt
  证明: by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  -- Suppose the lifted property `P` holds at `x`:
  -- choose slice charts `φ` near `x` and `ψ` near `f x` s.t. `P f φ ψ` holds.
  -- Then the same charts witness that `P f φ ψ` holds at any `y ∈ φ.source`.
  refine ⟨hx.domChart.source, fun y hy => 

Depends on / 依赖: isOpen_iff_forall_mem_open
-/
lemma _root_.IsOpen.liftSourceTargetPropertyAt :
    IsOpen {x | LiftSourceTargetPropertyAt I J n g x P} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  -- Suppose the lifted property `P` holds at `x`:
  -- choose slice charts `φ` near `x` and `ψ` near `f x` s.t. `P f φ ψ` holds.
  -- Then the same charts witness that `P f φ ψ` holds at any `y ∈ φ.source`.
  refine ⟨hx.domChart.source, fun y hy => ?_, hx.domChart.open_source, hx.mem_domChart_source⟩
  exact ⟨hx.domChart, hx.codChart, hy, hx.source_subset_preimage_source hy,
    hx.domChart_mem_maximalAtlas, hx.codChart_mem_maximalAtlas, hx.source_subset_preimage_source,
    hx.property⟩

/--
lemma `prodMap` / 引理 `prodMap`

English:
lemma prodMap
  statement: [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
  proof: by
  use hf.domChart.prod hg.domChart, hf.codChart.prod hg.codChart
  · simp [hf.mem_domChart_source, hg.mem_domChart_source]
  · simp [mem_codChart_source hf, mem_codChart_source hg]
  · exact IsManifold.mem_maximalAtlas_prod
      (domChart_mem_maximalAtlas hf) (domChart_mem_maximalAtlas hg)
  · a

中文:
引理 prodMap
  结论: [是流形 I n M] [是流形 I' n M'] [是流形 J n N] [是流形 J' n N']
  证明: by
  use hf.domChart.prod hg.domChart, hf.codChart.prod hg.codChart
  · simp [hf.mem_domChart_source, hg.mem_domChart_source]
  · simp [mem_codChart_source hf, mem_codChart_source hg]
  · exact IsManifold.mem_maximalAtlas_prod
      (domChart_mem_maximalAtlas hf) (domChart_mem_maximalAtlas hg)
  · a

Depends on / 依赖: IsManifold, IsManifold.mem_maximalAtlas_prod, OpenPartialHomeomorph, OpenPartialHomeomorph.prod_toPartialHomeomorph, PartialEquiv, PartialEquiv.prod_source, codChart, codChart_mem_maximalAtlas, domChart, domChart_mem_maximalAtlas, hf.codChart.prod, hf.domChart.prod, hf.mem_domChart_source, hg.codChart, hg.domChart, hg.mem_domChart_source, mem_codChart_source, mem_domChart_source, mem_maximalAtlas_prod, preimage_prod_map_prod
-/
lemma prodMap [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    {Q : (M' -> N') -> OpenPartialHomeomorph M' H' -> OpenPartialHomeomorph N' G' -> Prop}
    {R : ((M × M') -> (N × N')) -> OpenPartialHomeomorph (M × M') (H × H') ->
      OpenPartialHomeomorph (N × N') (G × G') -> Prop}
    (hf : LiftSourceTargetPropertyAt I J n f x P) {g : M' -> N'} {x' : M'}
    (hg : LiftSourceTargetPropertyAt I' J' n g x' Q)
    (h : forall {f : M -> N}, forall {φ₁ : OpenPartialHomeomorph M H}, forall {ψ₁ : OpenPartialHomeomorph N G},
      forall {g : M' -> N'}, forall {φ₂ : OpenPartialHomeomorph M' H'}, forall {ψ₂ : OpenPartialHomeomorph N' G'},
      P f φ₁ ψ₁ -> Q g φ₂ ψ₂ -> R (Prod.map f g) (φ₁.prod φ₂) (ψ₁.prod ψ₂)) :
    LiftSourceTargetPropertyAt (I.prod I') (J.prod J') n (Prod.map f g) (x, x') R := by
  use hf.domChart.prod hg.domChart, hf.codChart.prod hg.codChart
  · simp [hf.mem_domChart_source, hg.mem_domChart_source]
  · simp [mem_codChart_source hf, mem_codChart_source hg]
  · exact IsManifold.mem_maximalAtlas_prod
      (domChart_mem_maximalAtlas hf) (domChart_mem_maximalAtlas hg)
  · apply IsManifold.mem_maximalAtlas_prod
      (codChart_mem_maximalAtlas hf) (codChart_mem_maximalAtlas hg)
  · simp only [OpenPartialHomeomorph.prod_toPartialHomeomorph, PartialEquiv.prod_source,
      preimage_prod_map_prod]
    exact prod_mono hf.source_subset_preimage_source hg.source_subset_preimage_source
  · exact h hf.property hg.property

end LiftSourceTargetPropertyAt

end Manifold
