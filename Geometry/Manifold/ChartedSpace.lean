/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Charted spaces

A smooth manifold is a topological space `M` locally modelled on a Euclidean space (or a Euclidean
half-space for manifolds with boundaries, or an infinite-dimensional vector space for more general
notions of manifolds), i.e., the manifold is covered by open subsets on which there are local
homeomorphisms (the charts) going to a model space `H`, and the changes of charts should be smooth
maps.

In this file, we introduce a general framework describing these notions, where the model space is an
arbitrary topological space. We avoid the word *manifold*, which should be reserved for the
situation where the model space is a (subset of a) vector space, and use the terminology
*charted space* instead.

If the changes of charts satisfy some additional property (for instance if they are smooth), then
`M` inherits additional structure (it makes sense to talk about smooth manifolds). There are
therefore two different ingredients in a charted space:
* the set of charts, which is data
* the fact that changes of charts belong to some group (in fact groupoid), which is additional Prop.

We separate these two parts in the definition: the charted space structure is just the set of
charts, and then the different smoothness requirements (smooth manifold, orientable manifold,
contact manifold, and so on) are additional properties of these charts. These properties are
formalized through the notion of structure groupoid, i.e., a set of open partial homeomorphisms
stable under composition and inverse, to which the change of coordinates should belong.

## Main definitions

* `StructureGroupoid H` : a subset of open partial homeomorphisms of `H` stable under composition,
  inverse and restriction (ex: partial diffeomorphisms).
* `continuousGroupoid H` : the groupoid of all open partial homeomorphisms of `H`.
* `ChartedSpace H M` : charted space structure on `M` modelled on `H`, given by an atlas of
  open partial homeomorphisms from `M` to `H` whose sources cover `M`. This is a type class.
* `HasGroupoid M G` : when `G` is a structure groupoid on `H` and `M` is a charted space
  modelled on `H`, require that all coordinate changes belong to `G`. This is a type class.
* `atlas H M` : when `M` is a charted space modelled on `H`, the atlas of this charted
  space structure, i.e., the set of charts.
* `G.maximalAtlas M` : when `M` is a charted space modelled on `H` and admitting `G` as a
  structure groupoid, one can consider all the open partial homeomorphisms from `M` to `H` such that
  changing coordinate from any chart to them belongs to `G`. This is a larger atlas, called the
  maximal atlas (for the groupoid `G`).
* `Structomorph G M M'` : the type of diffeomorphisms between the charted spaces `M` and `M'` for
  the groupoid `G`. We avoid the word diffeomorphism, keeping it for the smooth category.

As a basic example, we give the instance
`instance chartedSpaceSelf (H : Type*) [TopologicalSpace H] : ChartedSpace H H`
saying that a topological space is a charted space over itself, with the identity as unique chart.
This charted space structure is compatible with any groupoid.

Additional useful definitions:

* `Pregroupoid H` : a subset of partial maps of `H` stable under composition and
  restriction, but not inverse (ex: smooth maps)
* `Pregroupoid.groupoid` : construct a groupoid from a pregroupoid, by requiring that a map and
  its inverse both belong to the pregroupoid (ex: construct diffeos from smooth maps)
* `chartAt H x` is a preferred chart at `x : M` when `M` has a charted space structure modelled on
  `H`.
* `G.compatible he he'` states that, for any two charts `e` and `e'` in the atlas, the composition
  of `e.symm` and `e'` belongs to the groupoid `G` when `M` admits `G` as a structure groupoid.
* `G.compatible_of_mem_maximalAtlas he he'` states that, for any two charts `e` and `e'` in the
  maximal atlas associated to the groupoid `G`, the composition of `e.symm` and `e'` belongs to the
  `G` if `M` admits `G` as a structure groupoid.
* `ChartedSpaceCore.toChartedSpace`: consider a space without a topology, but endowed with a set
  of charts (which are partial equivs) for which the changes of coordinates are partial homeos.
  Then one can construct a topology on the space for which the charts become partial homeos,
  defining a genuine charted space structure.

## Implementation notes

The atlas in a charted space is *not* a maximal atlas in general: the notion of maximality depends
on the groupoid one considers, and changing groupoids changes the maximal atlas. With the current
formalization, it makes sense first to choose the atlas, and then to ask whether this precise atlas
defines a smooth manifold, an orientable manifold, and so on. A consequence is that structomorphisms
between `M` and `M'` do *not* induce a bijection between the atlases of `M` and `M'`: the
definition is only that, read in charts, the structomorphism locally belongs to the groupoid under
consideration. (This is equivalent to inducing a bijection between elements of the maximal atlas).
A consequence is that the invariance under structomorphisms of properties defined in terms of the
atlas is not obvious in general, and could require some work in theory (amounting to the fact
that these properties only depend on the maximal atlas, for instance). In practice, this does not
create any real difficulty.

We use the letter `H` for the model space thinking of the case of manifolds with boundary, where the
model space is a half-space.

Manifolds are sometimes defined as topological spaces with an atlas of local diffeomorphisms, and
sometimes as spaces with an atlas from which a topology is deduced. We use the former approach:
otherwise, there would be an instance from manifolds to topological spaces, which means that any
instance search for topological spaces would try to find manifold structures involving a yet
unknown model space, leading to problems. However, we also introduce the latter approach,
through a structure `ChartedSpaceCore` making it possible to construct a topology out of a set of
partial equivs with compatibility conditions (but we do not register it as an instance).

In the definition of a charted space, the model space is written as an explicit parameter as there
can be several model spaces for a given topological space. For instance, a complex manifold
(modelled over `ℂ^n`) will also be seen sometimes as a real manifold modelled over `ℝ^(2n)`.

## Notation

In the scope `Manifold`, we denote the composition of open partial homeomorphisms with `≫ₕ`, and the
composition of partial equivs with `≫`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Topology

universe u

variable {H : Type u} {H' : Type*} {M : Type*} {M' : Type*} {M'' : Type*}

open Set OpenPartialHomeomorph Manifold

/-! ### Charted spaces -/

/-- A charted space is a topological space endowed with an atlas, i.e., a set of local
homeomorphisms taking values in a model space `H`, called charts, such that the domains of the
charts cover the whole space. We express the covering property by choosing for each `x` a member
`chartAt x` of the atlas containing `x` in its source: in the smooth case, this is convenient to
construct the tangent bundle in an efficient way.
The model space is written as an explicit parameter as there can be several model spaces for a
given topological space. For instance, a complex manifold (modelled over `ℂ^n`) will also be seen
sometimes as a real manifold over `ℝ^(2n)`.
-/
@[ext]
/--
Definition of `ChartedSpace` / `ChartedSpace` 的定义

English:
class ChartedSpace
  parameters: (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
  axioms and operations (4):
    - atlas : Set (OpenPartialHomeomorph M H)
    - chartAt : M -> OpenPartialHomeomorph M H
    - mem_chart_source : forall x, x in (chartAt x).source
    - chart_mem_atlas : forall x, chartAt x in atlas

中文:
类 ChartedSpace
  参数: (H : 类型) [TopologicalSpace H] (M : 类型) [TopologicalSpace M]
  公理与运算 (4 个):
    - atlas : Set (OpenPartialHomeomorph M H)
    - chartAt : M -> OpenPartialHomeomorph M H
    - mem_chart_source : 对任意 x, x in (chartAt x).source
    - chart_mem_atlas : 对任意 x, chartAt x in atlas
-/
class ChartedSpace (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M] where
  /-- The atlas of charts in the `ChartedSpace`. -/
  protected atlas : Set (OpenPartialHomeomorph M H)
  /-- The preferred chart at each point in the charted space. -/
  protected chartAt : M -> OpenPartialHomeomorph M H
  protected mem_chart_source : forall x, x in (chartAt x).source
  protected chart_mem_atlas : forall x, chartAt x in atlas

/--
Definition of `atlas` / `atlas` 的定义

English:
abbreviation atlas
  signature: (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
  body: ChartedSpace.atlas

中文:
缩写 atlas
  签名: (H : 类型) [TopologicalSpace H] (M : 类型) [TopologicalSpace M]
  定义体: ChartedSpace.atlas

Depends on / 依赖: ChartedSpace, ChartedSpace.atlas
-/
abbrev atlas (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Set (OpenPartialHomeomorph M H) :=
  ChartedSpace.atlas

/--
Definition of `chartAt` / `chartAt` 的定义

English:
abbreviation chartAt
  signature: (H : Type*) [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  body: ChartedSpace.chartAt x

@[simp, mfld_simps]

中文:
缩写 chartAt
  签名: (H : 类型) [TopologicalSpace H] {M : 类型} [TopologicalSpace M]
  定义体: ChartedSpace.chartAt x

@[simp, mfld_simps]

Depends on / 依赖: ChartedSpace, ChartedSpace.chartAt, chartAt
-/
abbrev chartAt (H : Type*) [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : OpenPartialHomeomorph M H :=
  ChartedSpace.chartAt x

@[simp, mfld_simps]
/--
lemma `mem_chart_source` / 引理 `mem_chart_source`

English:
lemma mem_chart_source
  statement: (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  proof: ChartedSpace.mem_chart_source x

@[simp, mfld_simps]

中文:
引理 mem_chart_source
  结论: (H : 类型) {M : 类型} [TopologicalSpace H] [TopologicalSpace M]
  证明: ChartedSpace.mem_chart_source x

@[simp, mfld_simps]

Depends on / 依赖: ChartedSpace, ChartedSpace.mem_chart_source, mem_chart_source
-/
lemma mem_chart_source (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : x in (chartAt H x).source :=
  ChartedSpace.mem_chart_source x

@[simp, mfld_simps]
/--
lemma `chart_mem_atlas` / 引理 `chart_mem_atlas`

English:
lemma chart_mem_atlas
  statement: (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  proof: ChartedSpace.chart_mem_atlas x

中文:
引理 chart_mem_atlas
  结论: (H : 类型) {M : 类型} [TopologicalSpace H] [TopologicalSpace M]
  证明: ChartedSpace.chart_mem_atlas x

Depends on / 依赖: ChartedSpace, ChartedSpace.chart_mem_atlas, chart_mem_atlas
-/
lemma chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : chartAt H x in atlas H M :=
  ChartedSpace.chart_mem_atlas x

/--
lemma `nonempty_of_chartedSpace` / 引理 `nonempty_of_chartedSpace`

English:
lemma nonempty_of_chartedSpace
  statement: {H : Type*} {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  proof: ⟨chartAt H x x⟩

中文:
引理 nonempty_of_chartedSpace
  结论: {H : 类型} {M : 类型} [TopologicalSpace H] [TopologicalSpace M]
  证明: ⟨chartAt H x x⟩

Depends on / 依赖: chartAt
-/
lemma nonempty_of_chartedSpace {H : Type*} {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : Nonempty H :=
  ⟨chartAt H x x⟩

/--
lemma `isEmpty_of_chartedSpace` / 引理 `isEmpty_of_chartedSpace`

English:
lemma isEmpty_of_chartedSpace
  statement: (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  proof: by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x⟩⟩
  · exact hM
  · exact (IsEmpty.false (chartAt H x x)).elim

中文:
引理 isEmpty_of_chartedSpace
  结论: (H : 类型) {M : 类型} [TopologicalSpace H] [TopologicalSpace M]
  证明: by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x⟩⟩
  · exact hM
  · exact (IsEmpty.false (chartAt H x x)).elim

Depends on / 依赖: IsEmpty, IsEmpty.false, chartAt, isEmpty_or_nonempty
-/
lemma isEmpty_of_chartedSpace (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] [IsEmpty H] : IsEmpty M := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x⟩⟩
  · exact hM
  · exact (IsEmpty.false (chartAt H x x)).elim

section ChartedSpace

section

variable (H) [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

/--
theorem `mem_chart_target` / 定理 `mem_chart_target`

English:
theorem mem_chart_target
  given: (x : M)
  statement: chartAt H x x in (chartAt H x).target
  proof: (chartAt H x).map_source (mem_chart_source _ _)

中文:
定理 mem_chart_target
  条件: (x : M)
  结论: chartAt H x x in (chartAt H x).target
  证明: (chartAt H x).map_source (mem_chart_source _ _)

Depends on / 依赖: chartAt, map_source, mem_chart_source
-/
theorem mem_chart_target (x : M) : chartAt H x x in (chartAt H x).target :=
  (chartAt H x).map_source (mem_chart_source _ _)

/--
theorem `chart_source_mem_nhds` / 定理 `chart_source_mem_nhds`

English:
theorem chart_source_mem_nhds
  given: (x : M)
  statement: (chartAt H x).source in 𝓝 x
  proof: (chartAt H x).open_source.mem_nhds mem_chart_source H x

中文:
定理 chart_source_mem_nhds
  条件: (x : M)
  结论: (chartAt H x).source in 𝓝 x
  证明: (chartAt H x).open_source.mem_nhds mem_chart_source H x

Depends on / 依赖: chartAt, mem_chart_source, mem_nhds, open_source, open_source.mem_nhds
-/
theorem chart_source_mem_nhds (x : M) : (chartAt H x).source in 𝓝 x :=
(chartAt H x).open_source.mem_nhds mem_chart_source H x

/--
theorem `chart_target_mem_nhds` / 定理 `chart_target_mem_nhds`

English:
theorem chart_target_mem_nhds
  given: (x : M)
  statement: (chartAt H x).target in 𝓝 (chartAt H x x)
  proof: (chartAt H x).open_target.mem_nhds mem_chart_target H x

中文:
定理 chart_target_mem_nhds
  条件: (x : M)
  结论: (chartAt H x).target in 𝓝 (chartAt H x x)
  证明: (chartAt H x).open_target.mem_nhds mem_chart_target H x

Depends on / 依赖: chartAt, mem_chart_target, mem_nhds, open_target, open_target.mem_nhds
-/
theorem chart_target_mem_nhds (x : M) : (chartAt H x).target in 𝓝 (chartAt H x x) :=
(chartAt H x).open_target.mem_nhds mem_chart_target H x

variable (M) in
@[simp]
/--
theorem `iUnion_source_chartAt` / 定理 `iUnion_source_chartAt`

English:
theorem iUnion_source_chartAt
  statement: (⋃ x : M, (chartAt H x).source) = (univ : Set M)
  proof: eq_univ_iff_forall.mpr fun x => mem_iUnion.mpr ⟨x, mem_chart_source H x⟩

中文:
定理 iUnion_source_chartAt
  结论: (⋃ x : M, (chartAt H x).source) = (univ : Set M)
  证明: eq_univ_iff_forall.mpr fun x => mem_iUnion.mpr ⟨x, mem_chart_source H x⟩

Depends on / 依赖: eq_univ_iff_forall, eq_univ_iff_forall.mpr, mem_chart_source, mem_iUnion, mem_iUnion.mpr
-/
theorem iUnion_source_chartAt : (⋃ x : M, (chartAt H x).source) = (univ : Set M) :=
  eq_univ_iff_forall.mpr fun x => mem_iUnion.mpr ⟨x, mem_chart_source H x⟩

/--
theorem `ChartedSpace.isOpen_iff` / 定理 `ChartedSpace.isOpen_iff`

English:
theorem ChartedSpace.isOpen_iff
  given: (s : Set M)
  proof: by
  rw [isOpen_iff_of_cover (fun i => (chartAt H i).open_source) (iUnion_source_chartAt H M)]
  simp only [(chartAt H _).isOpen_image_iff_of_subset_source inter_subset_left]

中文:
定理 ChartedSpace.isOpen_iff
  条件: (s : Set M)
  证明: by
  rw [isOpen_iff_of_cover (fun i => (chartAt H i).open_source) (iUnion_source_chartAt H M)]
  simp only [(chartAt H _).isOpen_image_iff_of_subset_source inter_subset_left]

Depends on / 依赖: chartAt, iUnion_source_chartAt, inter_subset_left, isOpen_iff_of_cover, isOpen_image_iff_of_subset_source, open_source
-/
theorem ChartedSpace.isOpen_iff (s : Set M) :
IsOpen s ↔ forall x : M, IsOpen chartAt H x '' ((chartAt H x).source inter s) := by
  rw [isOpen_iff_of_cover (fun i => (chartAt H i).open_source) (iUnion_source_chartAt H M)]
  simp only [(chartAt H _).isOpen_image_iff_of_subset_source inter_subset_left]

/--
Definition of `achart` / `achart` 的定义

English:
definition achart
  signature: (x : M)
  body: ⟨chartAt H x, chart_mem_atlas H x⟩

中文:
定义 achart
  签名: (x : M)
  定义体: ⟨chartAt H x, chart_mem_atlas H x⟩

Depends on / 依赖: chartAt, chart_mem_atlas
-/
def achart (x : M) : atlas H M :=
  ⟨chartAt H x, chart_mem_atlas H x⟩

/--
theorem `achart_def` / 定理 `achart_def`

English:
theorem achart_def
  given: (x : M)
  statement: achart H x = ⟨chartAt H x, chart_mem_atlas H x⟩
  proof: rfl

@[simp, mfld_simps]

中文:
定理 achart_def
  条件: (x : M)
  结论: achart H x = ⟨chartAt H x, chart_mem_atlas H x⟩
  证明: rfl

@[simp, mfld_simps]
-/
theorem achart_def (x : M) : achart H x = ⟨chartAt H x, chart_mem_atlas H x⟩ :=
  rfl

@[simp, mfld_simps]
/--
theorem `coe_achart` / 定理 `coe_achart`

English:
theorem coe_achart
  given: (x : M)
  statement: (achart H x : OpenPartialHomeomorph M H) = chartAt H x
  proof: rfl

@[simp, mfld_simps]

中文:
定理 coe_achart
  条件: (x : M)
  结论: (achart H x : OpenPartialHomeomorph M H) = chartAt H x
  证明: rfl

@[simp, mfld_simps]
-/
theorem coe_achart (x : M) : (achart H x : OpenPartialHomeomorph M H) = chartAt H x :=
  rfl

@[simp, mfld_simps]
/--
theorem `achart_val` / 定理 `achart_val`

English:
theorem achart_val
  given: (x : M)
  statement: (achart H x).1 = chartAt H x
  proof: rfl

中文:
定理 achart_val
  条件: (x : M)
  结论: (achart H x).1 = chartAt H x
  证明: rfl
-/
theorem achart_val (x : M) : (achart H x).1 = chartAt H x :=
  rfl

/--
theorem `mem_achart_source` / 定理 `mem_achart_source`

English:
theorem mem_achart_source
  given: (x : M)
  statement: x in (achart H x).1.source
  proof: mem_chart_source H x

中文:
定理 mem_achart_source
  条件: (x : M)
  结论: x in (achart H x).1.source
  证明: mem_chart_source H x

Depends on / 依赖: mem_chart_source
-/
theorem mem_achart_source (x : M) : x in (achart H x).1.source :=
  mem_chart_source H x

open TopologicalSpace

/--
theorem `ChartedSpace.secondCountable_of_countable_cover` / 定理 `ChartedSpace.secondCountable_of_countable_cover`

English:
theorem ChartedSpace.secondCountable_of_countable_cover
  statement: [SecondCountableTopology H] {s : Set M}
  proof: by
  have : forall x : M, SecondCountableTopology (chartAt H x).source :=
    fun x => (chartAt (H := H) x).secondCountableTopology_source
  have := hsc.toEncodable
  rw [biUnion_eq_iUnion] at hs
  exact secondCountableTopology_of_countable_cover (fun x : s => (chartAt H (x : M)).open_source) hs

中文:
定理 ChartedSpace.secondCountable_of_countable_cover
  结论: [SecondCountableTopology H] {s : Set M}
  证明: by
  have : forall x : M, SecondCountableTopology (chartAt H x).source :=
    fun x => (chartAt (H := H) x).secondCountableTopology_source
  have := hsc.toEncodable
  rw [biUnion_eq_iUnion] at hs
  exact secondCountableTopology_of_countable_cover (fun x : s => (chartAt H (x : M)).open_source) hs

Depends on / 依赖: SecondCountableTopology, biUnion_eq_iUnion, chartAt, hsc.toEncodable, open_source, secondCountableTopology_of_countable_cover, secondCountableTopology_source, source, toEncodable
-/
theorem ChartedSpace.secondCountable_of_countable_cover [SecondCountableTopology H] {s : Set M}
    (hs : ⋃ (x) (_ : x in s), (chartAt H x).source = univ) (hsc : s.Countable) :
    SecondCountableTopology M := by
  have : forall x : M, SecondCountableTopology (chartAt H x).source :=
    fun x => (chartAt (H := H) x).secondCountableTopology_source
  have := hsc.toEncodable
  rw [biUnion_eq_iUnion] at hs
  exact secondCountableTopology_of_countable_cover (fun x : s => (chartAt H (x : M)).open_source) hs

variable (M)

/--
theorem `ChartedSpace.secondCountable_of_sigmaCompact` / 定理 `ChartedSpace.secondCountable_of_sigmaCompact`

English:
theorem ChartedSpace.secondCountable_of_sigmaCompact
  statement: [SecondCountableTopology H]
  proof: by
  obtain ⟨s, hsc, hsU⟩ : exists s, Set.Countable s ∧ ⋃ (x) (_ : x in s), (chartAt H x).source = univ :=
    countable_cover_nhds_of_sigmaCompact fun x : M => chart_source_mem_nhds H x
  exact ChartedSpace.secondCountable_of_countable_cover H hsU hsc

中文:
定理 ChartedSpace.secondCountable_of_sigmaCompact
  结论: [SecondCountableTopology H]
  证明: by
  obtain ⟨s, hsc, hsU⟩ : exists s, Set.Countable s ∧ ⋃ (x) (_ : x in s), (chartAt H x).source = univ :=
    countable_cover_nhds_of_sigmaCompact fun x : M => chart_source_mem_nhds H x
  exact ChartedSpace.secondCountable_of_countable_cover H hsU hsc

Depends on / 依赖: ChartedSpace, ChartedSpace.secondCountable_of_countable_cover, Countable, Set.Countable, chartAt, chart_source_mem_nhds, countable_cover_nhds_of_sigmaCompact, secondCountable_of_countable_cover, source
-/
theorem ChartedSpace.secondCountable_of_sigmaCompact [SecondCountableTopology H]
    [SigmaCompactSpace M] : SecondCountableTopology M := by
  obtain ⟨s, hsc, hsU⟩ : exists s, Set.Countable s ∧ ⋃ (x) (_ : x in s), (chartAt H x).source = univ :=
    countable_cover_nhds_of_sigmaCompact fun x : M => chart_source_mem_nhds H x
  exact ChartedSpace.secondCountable_of_countable_cover H hsU hsc

/--
theorem `ChartedSpace.locallyCompactSpace` / 定理 `ChartedSpace.locallyCompactSpace`

English:
theorem ChartedSpace.locallyCompactSpace
  given: [LocallyCompactSpace H]
  statement: LocallyCompactSpace M
  proof: by
  have : forall x : M, (𝓝 x).HasBasis
      (fun s => s in 𝓝 (chartAt H x x) ∧ IsCompact s ∧ s subseteq (chartAt H x).target)
      fun s => (chartAt H x).symm '' s := fun x => by
    rw [← (chartAt H x).symm_map_nhds_eq (mem_chart_source H x)]
    exact ((compact_basis_nhds (chartAt H x x)).hasB

中文:
定理 ChartedSpace.locallyCompactSpace
  条件: [LocallyCompactSpace H]
  结论: LocallyCompactSpace M
  证明: by
  have : forall x : M, (𝓝 x).HasBasis
      (fun s => s in 𝓝 (chartAt H x x) ∧ IsCompact s ∧ s subseteq (chartAt H x).target)
      fun s => (chartAt H x).symm '' s := fun x => by
    rw [← (chartAt H x).symm_map_nhds_eq (mem_chart_source H x)]
    exact ((compact_basis_nhds (chartAt H x x)).hasB

Depends on / 依赖: HasBasis, IsCompact, chartAt, chart_target_mem_nhds, compact_basis_nhds, continuousOn_symm, continuousOn_symm.mono, hasBasis_self_subset, image_of_continuousOn, mem_chart_source, of_hasBasis, subseteq, symm_map_nhds_eq, target
-/
theorem ChartedSpace.locallyCompactSpace [LocallyCompactSpace H] : LocallyCompactSpace M := by
  have : forall x : M, (𝓝 x).HasBasis
      (fun s => s in 𝓝 (chartAt H x x) ∧ IsCompact s ∧ s subseteq (chartAt H x).target)
      fun s => (chartAt H x).symm '' s := fun x => by
    rw [← (chartAt H x).symm_map_nhds_eq (mem_chart_source H x)]
    exact ((compact_basis_nhds (chartAt H x x)).hasBasis_self_subset
      (chart_target_mem_nhds H x)).map _
  refine .of_hasBasis this ?_
  rintro x s ⟨_, h₂, h₃⟩
  exact h₂.image_of_continuousOn ((chartAt H x).continuousOn_symm.mono h₃)

/--
theorem `ChartedSpace.locallyConnectedSpace` / 定理 `ChartedSpace.locallyConnectedSpace`

English:
theorem ChartedSpace.locallyConnectedSpace
  given: [LocallyConnectedSpace H]
  statement: LocallyConnectedSpace M
  proof: by
  let e : M -> OpenPartialHomeomorph M H := chartAt H
  refine locallyConnectedSpace_of_connected_bases (fun x s => (e x).symm '' s)
      (fun x s => (IsOpen s ∧ e x x in s ∧ IsConnected s) ∧ s subseteq (e x).target) ?_ ?_
  · intro x
    simpa only [e, OpenPartialHomeomorph.symm_map_nhds_eq, me

中文:
定理 ChartedSpace.locallyConnectedSpace
  条件: [LocallyConnectedSpace H]
  结论: LocallyConnectedSpace M
  证明: by
  let e : M -> OpenPartialHomeomorph M H := chartAt H
  refine locallyConnectedSpace_of_connected_bases (fun x s => (e x).symm '' s)
      (fun x s => (IsOpen s ∧ e x x in s ∧ IsConnected s) ∧ s subseteq (e x).target) ?_ ?_
  · intro x
    simpa only [e, OpenPartialHomeomorph.symm_map_nhds_eq, me

Depends on / 依赖: IsConnected, IsOpen, LocallyConnectedSpace, LocallyConnectedSpace.open_connected_basis, OpenPartialHomeomorph, OpenPartialHomeomorph.symm_map_nhds_eq, chartAt, hsconn, hsconn.is, hssubset, locallyConnectedSpace_of_connected_bases, mem_chart_source, mem_chart_target, mem_nhds, open_connected_basis, open_target, open_target.mem_nhds, restrict_subset, subseteq, symm_map_nhds_eq
-/
theorem ChartedSpace.locallyConnectedSpace [LocallyConnectedSpace H] : LocallyConnectedSpace M := by
  let e : M -> OpenPartialHomeomorph M H := chartAt H
  refine locallyConnectedSpace_of_connected_bases (fun x s => (e x).symm '' s)
      (fun x s => (IsOpen s ∧ e x x in s ∧ IsConnected s) ∧ s subseteq (e x).target) ?_ ?_
  · intro x
    simpa only [e, OpenPartialHomeomorph.symm_map_nhds_eq, mem_chart_source] using!
      ((LocallyConnectedSpace.open_connected_basis (e x x)).restrict_subset
        ((e x).open_target.mem_nhds (mem_chart_target H x))).map (e x).symm
  · rintro x s ⟨⟨-, -, hsconn⟩, hssubset⟩
    exact hsconn.isPreconnected.image _ ((e x).continuousOn_symm.mono hssubset)

/--
theorem `ChartedSpace.locallyPathConnectedSpace` / 定理 `ChartedSpace.locallyPathConnectedSpace`

English:
theorem ChartedSpace.locallyPathConnectedSpace
  given: [LocallyPathConnectedSpace H]
  proof: by
  refine ⟨fun x => ⟨fun s => ⟨fun hs => ?_, fun ⟨u, hu⟩ => Filter.mem_of_superset hu.1.1 hu.2⟩⟩⟩
  let e := chartAt H x
  let t := s inter e.source
  have ht : t in 𝓝 x := Filter.inter_mem hs (chart_source_mem_nhds _ _)
  refine ⟨e.symm '' pathComponentIn (e '' t) (e x), ⟨?_, ?_⟩, (?_ : _ subsete

中文:
定理 ChartedSpace.locallyPathConnectedSpace
  条件: [LocallyPathConnectedSpace H]
  证明: by
  refine ⟨fun x => ⟨fun s => ⟨fun hs => ?_, fun ⟨u, hu⟩ => Filter.mem_of_superset hu.1.1 hu.2⟩⟩⟩
  let e := chartAt H x
  let t := s inter e.source
  have ht : t in 𝓝 x := Filter.inter_mem hs (chart_source_mem_nhds _ _)
  refine ⟨e.symm '' pathComponentIn (e '' t) (e x), ⟨?_, ?_⟩, (?_ : _ subsete

Depends on / 依赖: Filter, Filter.inter_mem, Filter.mem_of_superset, chartAt, chart_source_mem_nhds, e.image_mem_nhds, e.left_inv, e.source, e.symm, e.symm.image_mem_nhds, image_mem_nhds, inter_mem, inter_subset_left, left_inv, mem_chart_source, mem_of_superset, nth_rewrite, pathComponentIn, pathComponentIn_mem_nhds, source
-/
theorem ChartedSpace.locallyPathConnectedSpace [LocallyPathConnectedSpace H] :
    LocallyPathConnectedSpace M := by
  refine ⟨fun x => ⟨fun s => ⟨fun hs => ?_, fun ⟨u, hu⟩ => Filter.mem_of_superset hu.1.1 hu.2⟩⟩⟩
  let e := chartAt H x
  let t := s inter e.source
  have ht : t in 𝓝 x := Filter.inter_mem hs (chart_source_mem_nhds _ _)
  refine ⟨e.symm '' pathComponentIn (e '' t) (e x), ⟨?_, ?_⟩, (?_ : _ subseteq t).trans inter_subset_left⟩
  · nth_rewrite 1 [← e.left_inv (mem_chart_source _ _)]
    apply e.symm.image_mem_nhds (by simp [e])
exact pathComponentIn_mem_nhds e.image_mem_nhds (mem_chart_source _ _) ht
  · refine (isPathConnected_pathComponentIn <| mem_image_of_mem e (mem_of_mem_nhds ht)).image' ?_
    refine e.continuousOn_symm.mono ?_
    unfold t
    grw [pathComponentIn_subset, inter_subset_right, e.image_source_subset]
  · exact (image_mono pathComponentIn_subset).trans
      (PartialEquiv.symm_image_image_of_subset_source _ inter_subset_right).subset

@[deprecated (since := "2026-06-21")]
alias ChartedSpace.locPathConnectedSpace := ChartedSpace.locallyPathConnectedSpace

/-- If `M` is modelled on `H'` and `H'` is itself modelled on `H`, then we can consider `M` as being
modelled on `H`. -/
@[instance_reducible]
/--
Definition of `ChartedSpace.comp` / `ChartedSpace.comp` 的定义

English:
definition ChartedSpace.comp
  signature: (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H']
  body: image2 OpenPartialHomeomorph.trans (atlas H' M) (atlas H H')
  chartAt p := (chartAt H' p).trans (chartAt H (chartAt H' p p))
  mem_chart_source p := by simp only [mfld_simps]
  chart_mem_atlas p := ⟨chartAt _ p, chart_mem_atlas _ p, chartAt _ _, chart_mem_atlas _ _, rfl⟩

中文:
定义 ChartedSpace.comp
  签名: (H : 类型) [TopologicalSpace H] (H' : 类型) [TopologicalSpace H']
  定义体: image2 OpenPartialHomeomorph.trans (atlas H' M) (atlas H H')
  chartAt p := (chartAt H' p).trans (chartAt H (chartAt H' p p))
  mem_chart_source p := by simp only [mfld_simps]
  chart_mem_atlas p := ⟨chartAt _ p, chart_mem_atlas _ p, chartAt _ _, chart_mem_atlas _ _, rfl⟩

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.trans, image2
-/
def ChartedSpace.comp (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H']
    (M : Type*) [TopologicalSpace M] [ChartedSpace H H'] [ChartedSpace H' M] :
    ChartedSpace H M where
  atlas := image2 OpenPartialHomeomorph.trans (atlas H' M) (atlas H H')
  chartAt p := (chartAt H' p).trans (chartAt H (chartAt H' p p))
  mem_chart_source p := by simp only [mfld_simps]
  chart_mem_atlas p := ⟨chartAt _ p, chart_mem_atlas _ p, chartAt _ _, chart_mem_atlas _ _, rfl⟩

/--
theorem `chartAt_comp` / 定理 `chartAt_comp`

English:
theorem chartAt_comp
  statement: (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H']
  proof: rfl

中文:
定理 chartAt_comp
  结论: (H : 类型) [TopologicalSpace H] (H' : 类型) [TopologicalSpace H']
  证明: rfl

Depends on / 依赖: ChartedSpace, ChartedSpace.comp, chartAt
-/
theorem chartAt_comp (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H']
    {M : Type*} [TopologicalSpace M] [ChartedSpace H H'] [ChartedSpace H' M] (x : M) :
    (letI := ChartedSpace.comp H H' M; chartAt H x) = chartAt H' x ≫ₕ chartAt H (chartAt H' x x) :=
  rfl

/--
theorem `ChartedSpace.t1Space` / 定理 `ChartedSpace.t1Space`

English:
theorem ChartedSpace.t1Space
  given: [T1Space H]
  statement: T1Space M
  proof: by
  apply t1Space_iff_exists_open.2 (fun x y hxy => ?_)
  by_cases hy : y in (chartAt H x).source
  · refine ⟨(chartAt H x).source inter (chartAt H x)⁻¹' ({chartAt H x y}ᶜ), ?_, ?_, by simp⟩
    · exact OpenPartialHomeomorph.isOpen_inter_preimage _ isOpen_compl_singleton
    · simp only [preimage_c

中文:
定理 ChartedSpace.t1Space
  条件: [T1Space H]
  结论: T1Space M
  证明: by
  apply t1Space_iff_exists_open.2 (fun x y hxy => ?_)
  by_cases hy : y in (chartAt H x).source
  · refine ⟨(chartAt H x).source inter (chartAt H x)⁻¹' ({chartAt H x y}ᶜ), ?_, ?_, by simp⟩
    · exact OpenPartialHomeomorph.isOpen_inter_preimage _ isOpen_compl_singleton
    · simp only [preimage_c

Depends on / 依赖: ChartedSpace, ChartedSpace.mem_chart_source, OpenPartialHomeomorph, OpenPartialHomeomorph.isOpen_inter_preimage, chartAt, injOn.ne, isOpen_compl_singleton, isOpen_inter_preimage, mem_chart_source, mem_compl_iff, mem_inter_iff, mem_preimage, mem_singleton_iff, preimage_compl, source, t1Space_iff_exists_open, true_and
-/
theorem ChartedSpace.t1Space [T1Space H] : T1Space M := by
  apply t1Space_iff_exists_open.2 (fun x y hxy => ?_)
  by_cases hy : y in (chartAt H x).source
  · refine ⟨(chartAt H x).source inter (chartAt H x)⁻¹' ({chartAt H x y}ᶜ), ?_, ?_, by simp⟩
    · exact OpenPartialHomeomorph.isOpen_inter_preimage _ isOpen_compl_singleton
    · simp only [preimage_compl, mem_inter_iff, mem_chart_source, mem_compl_iff, mem_preimage,
        mem_singleton_iff, true_and]
      exact (chartAt H x).injOn.ne (ChartedSpace.mem_chart_source x) hy hxy
  · exact ⟨(chartAt H x).source, (chartAt H x).open_source, ChartedSpace.mem_chart_source x, hy⟩

/--
theorem `ChartedSpace.discreteTopology` / 定理 `ChartedSpace.discreteTopology`

English:
theorem ChartedSpace.discreteTopology
  given: [DiscreteTopology H]
  statement: DiscreteTopology M
  proof: by
  apply discreteTopology_iff_isOpen_singleton.2 (fun x => ?_)
  have : IsOpen ((chartAt H x).source inter (chartAt H x) ⁻¹' {chartAt H x x}) :=
    isOpen_inter_preimage _ (isOpen_discrete _)
  convert! this
  refine Subset.antisymm (by simp) ?_
  simp only [subset_singleton_iff, mem_inter_iff, m

中文:
定理 ChartedSpace.discreteTopology
  条件: [DiscreteTopology H]
  结论: DiscreteTopology M
  证明: by
  apply discreteTopology_iff_isOpen_singleton.2 (fun x => ?_)
  have : IsOpen ((chartAt H x).source inter (chartAt H x) ⁻¹' {chartAt H x x}) :=
    isOpen_inter_preimage _ (isOpen_discrete _)
  convert! this
  refine Subset.antisymm (by simp) ?_
  simp only [subset_singleton_iff, mem_inter_iff, m

Depends on / 依赖: IsOpen, Subset, Subset.antisymm, and_imp, antisymm, chartAt, convert, discreteTopology_iff_isOpen_singleton, isOpen_discrete, isOpen_inter_preimage, mem_chart_source, mem_inter_iff, mem_preimage, mem_singleton_iff, source, subset_singleton_iff
-/
theorem ChartedSpace.discreteTopology [DiscreteTopology H] : DiscreteTopology M := by
  apply discreteTopology_iff_isOpen_singleton.2 (fun x => ?_)
  have : IsOpen ((chartAt H x).source inter (chartAt H x) ⁻¹' {chartAt H x x}) :=
    isOpen_inter_preimage _ (isOpen_discrete _)
  convert! this
  refine Subset.antisymm (by simp) ?_
  simp only [subset_singleton_iff, mem_inter_iff, mem_preimage, mem_singleton_iff, and_imp]
  intro y hy h'y
  exact (chartAt H x).injOn hy (mem_chart_source _ x) h'y

end

section Constructions

/-- An empty type is a charted space over any topological space. -/
@[instance_reducible]
/--
Definition of `ChartedSpace.empty` / `ChartedSpace.empty` 的定义

English:
definition ChartedSpace.empty
  signature: (H : Type*) [TopologicalSpace H]
  body: ∅
  chartAt x := (IsEmpty.false x).elim
  mem_chart_source x := (IsEmpty.false x).elim
  chart_mem_atlas x := (IsEmpty.false x).elim

中文:
定义 ChartedSpace.empty
  签名: (H : 类型) [TopologicalSpace H]
  定义体: ∅
  chartAt x := (IsEmpty.false x).elim
  mem_chart_source x := (IsEmpty.false x).elim
  chart_mem_atlas x := (IsEmpty.false x).elim
-/
def ChartedSpace.empty (H : Type*) [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [IsEmpty M] : ChartedSpace H M where
  atlas := ∅
  chartAt x := (IsEmpty.false x).elim
  mem_chart_source x := (IsEmpty.false x).elim
  chart_mem_atlas x := (IsEmpty.false x).elim

/--
Instance `chartedSpaceSelf` / 实例 `chartedSpaceSelf`

English:
instance chartedSpaceSelf
  signature: (H : Type*) [TopologicalSpace H]
  body: {OpenPartialHomeomorph.refl H}
  chartAt _ := OpenPartialHomeomorph.refl H
  mem_chart_source x := mem_univ x
  chart_mem_atlas _ := mem_singleton _

中文:
实例 chartedSpaceSelf
  签名: (H : 类型) [TopologicalSpace H]
  定义体: {OpenPartialHomeomorph.refl H}
  chartAt _ := OpenPartialHomeomorph.refl H
  mem_chart_source x := mem_univ x
  chart_mem_atlas _ := mem_singleton _

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.refl
-/
instance chartedSpaceSelf (H : Type*) [TopologicalSpace H] : ChartedSpace H H where
  atlas := {OpenPartialHomeomorph.refl H}
  chartAt _ := OpenPartialHomeomorph.refl H
  mem_chart_source x := mem_univ x
  chart_mem_atlas _ := mem_singleton _

/-- In the trivial `ChartedSpace` structure of a space modelled over itself through the identity,
the atlas members are just the identity. -/
@[simp, mfld_simps]
/--
theorem `chartedSpaceSelf_atlas` / 定理 `chartedSpaceSelf_atlas`

English:
theorem chartedSpaceSelf_atlas
  given: {H : Type*} [TopologicalSpace H] {e : OpenPartialHomeomorph H H}
  proof: Iff.rfl

中文:
定理 chartedSpaceSelf_atlas
  条件: {H : 类型} [TopologicalSpace H] {e : OpenPartialHomeomorph H H}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem chartedSpaceSelf_atlas {H : Type*} [TopologicalSpace H] {e : OpenPartialHomeomorph H H} :
    e in atlas H H ↔ e = OpenPartialHomeomorph.refl H :=
  Iff.rfl

/--
theorem `chartAt_self_eq` / 定理 `chartAt_self_eq`

English:
theorem chartAt_self_eq
  given: {H : Type*} [TopologicalSpace H] {x : H}
  proof: rfl

中文:
定理 chartAt_self_eq
  条件: {H : 类型} [TopologicalSpace H] {x : H}
  证明: rfl
-/
theorem chartAt_self_eq {H : Type*} [TopologicalSpace H] {x : H} :
    chartAt H x = OpenPartialHomeomorph.refl H := rfl

/-- Any discrete space is a charted space over a singleton set.
We keep this as a definition (not an instance) to avoid instance search trying to search for
`DiscreteTopology` or `Unique` instances.
-/
@[instance_reducible]
/--
Definition of `ChartedSpace.ofDiscreteTopology` / `ChartedSpace.ofDiscreteTopology` 的定义

English:
definition ChartedSpace.ofDiscreteTopology
  signature: [TopologicalSpace M] [TopologicalSpace H]
  body: letI f := fun x : M => OpenPartialHomeomorph.const
      (isOpen_discrete {x}) (isOpen_discrete {h.default})
    Set.image f univ
  chartAt x := OpenPartialHomeomorph.const (isOpen_discrete {x}) (isOpen_discrete {h.default})
  mem_chart_source x := by simp
  chart_mem_atlas x := by simp

@[deprecate

中文:
定义 ChartedSpace.ofDiscreteTopology
  签名: [TopologicalSpace M] [TopologicalSpace H]
  定义体: letI f := fun x : M => OpenPartialHomeomorph.const
      (isOpen_discrete {x}) (isOpen_discrete {h.default})
    Set.image f univ
  chartAt x := OpenPartialHomeomorph.const (isOpen_discrete {x}) (isOpen_discrete {h.default})
  mem_chart_source x := by simp
  chart_mem_atlas x := by simp

@[deprecate

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.const, Set.image, chartAt, chart_mem_atlas, h.default, isOpen_discrete, mem_chart_source
-/
def ChartedSpace.ofDiscreteTopology [TopologicalSpace M] [TopologicalSpace H]
    [DiscreteTopology M] [h : Unique H] : ChartedSpace H M where
  atlas :=
    letI f := fun x : M => OpenPartialHomeomorph.const
      (isOpen_discrete {x}) (isOpen_discrete {h.default})
    Set.image f univ
  chartAt x := OpenPartialHomeomorph.const (isOpen_discrete {x}) (isOpen_discrete {h.default})
  mem_chart_source x := by simp
  chart_mem_atlas x := by simp

@[deprecated (since := "2026-07-26")]
alias ChartedSpace.of_discreteTopology := ChartedSpace.ofDiscreteTopology

/-- A chart on the discrete space is the constant chart. -/
@[simp, mfld_simps]
/--
lemma `chartedSpace_of_discreteTopology_chartAt` / 引理 `chartedSpace_of_discreteTopology_chartAt`

English:
lemma chartedSpace_of_discreteTopology_chartAt
  statement: [TopologicalSpace M] [TopologicalSpace H]
  proof: ChartedSpace.ofDiscreteTopology (M := M) (H := H)
    chartAt H x = OpenPartialHomeomorph.const (isOpen_discrete {x}) (isOpen_discrete {h.default}) :=
  rfl

中文:
引理 chartedSpace_of_discreteTopology_chartAt
  结论: [TopologicalSpace M] [TopologicalSpace H]
  证明: ChartedSpace.ofDiscreteTopology (M := M) (H := H)
    chartAt H x = OpenPartialHomeomorph.const (isOpen_discrete {x}) (isOpen_discrete {h.default}) :=
  rfl

Depends on / 依赖: ChartedSpace, ChartedSpace.ofDiscreteTopology, ofDiscreteTopology
-/
lemma chartedSpace_of_discreteTopology_chartAt [TopologicalSpace M] [TopologicalSpace H]
    [DiscreteTopology M] [h : Unique H] {x : M} :
    haveI := ChartedSpace.ofDiscreteTopology (M := M) (H := H)
    chartAt H x = OpenPartialHomeomorph.const (isOpen_discrete {x}) (isOpen_discrete {h.default}) :=
  rfl

section Products

library_note «Manifold type tags» /-- For technical reasons we introduce two type tags:

* `ModelProd H H'` is the same as `H × H'`;
* `ModelPi H` is the same as `∀ i, H i`, where `H : ι → Type*` and `ι` is a finite type.

In both cases the reason is the same, so we explain it only in the case of the product. A charted
space `M` with model `H` is a set of charts from `M` to `H` covering the space. Every space is
registered as a charted space over itself, using the only chart `id`, in `chartedSpaceSelf`. You
can also define a product of charted space `M` and `M'` (with model space `H × H'`) by taking the
products of the charts. Now, on `H × H'`, there are two charted space structures with model space
`H × H'` itself, the one coming from `chartedSpaceSelf`, and the one coming from the product of
the two `chartedSpaceSelf` on each component. They are equal, but not defeq (because the product
of `id` and `id` is not defeq to `id`), which is bad as we know. This expedient of renaming `H × H'`
solves this problem. -/


/-- Same thing as `H × H'`. We introduce it for technical reasons,
see note [Manifold type tags]. -/
@[implicit_reducible]
/--
Definition of `ModelProd` / `ModelProd` 的定义

English:
definition ModelProd
  signature: (H : Type*) (H' : Type*)
  body: H × H'

中文:
定义 ModelProd
  签名: (H : 类型) (H' : 类型)
  定义体: H × H'
-/
def ModelProd (H : Type*) (H' : Type*) :=
  H × H'

/-- Same thing as `∀ i, H i`. We introduce it for technical reasons,
see note [Manifold type tags]. -/
@[implicit_reducible]
/--
Definition of `ModelPi` / `ModelPi` 的定义

English:
definition ModelPi
  signature: {ι : Type*} (H : ι -> Type*)
  body: forall i, H i

中文:
定义 ModelPi
  签名: {ι : 类型} (H : ι -> 类型)
  定义体: forall i, H i

Depends on / 依赖: sub_eq_add_neg
-/
def ModelPi {ι : Type*} (H : ι -> Type*) :=
  forall i, H i

section

/--
Instance `modelProdInhabited` / 实例 `modelProdInhabited`

English:
instance modelProdInhabited
  signature: [Inhabited H] [Inhabited H']
  body: inferInstanceAs Inhabited (H × H')

中文:
实例 modelProdInhabited
  签名: [Inhabited H] [Inhabited H']
  定义体: inferInstanceAs Inhabited (H × H')

Depends on / 依赖: Inhabited
-/
instance modelProdInhabited [Inhabited H] [Inhabited H'] : Inhabited (ModelProd H H') :=
inferInstanceAs Inhabited (H × H')

instance (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H'] :
    TopologicalSpace (ModelProd H H') :=
inferInstanceAs TopologicalSpace (H × H')

-- Next lemma shows up often when dealing with derivatives, so we register it as simp lemma.
@[simp, mfld_simps]
/--
theorem `modelProd_range_prod_id` / 定理 `modelProd_range_prod_id`

English:
theorem modelProd_range_prod_id
  given: {H : Type*} {H' : Type*} {α : Type*} (f : H -> α)
  proof: by
  rw [prod_range_univ_eq]
  rfl

中文:
定理 modelProd_range_prod_id
  条件: {H : 类型} {H' : 类型} {α : 类型} (f : H -> α)
  证明: by
  rw [prod_range_univ_eq]
  rfl

Depends on / 依赖: prod_range_univ_eq
-/
theorem modelProd_range_prod_id {H : Type*} {H' : Type*} {α : Type*} (f : H -> α) :
    (range fun p : ModelProd H H' => (f p.1, p.2)) = range f ×ˢ (univ : Set H') := by
  rw [prod_range_univ_eq]
  rfl

end

section

variable {ι : Type*} {Hi : ι -> Type*}

/--
Instance `modelPiInhabited` / 实例 `modelPiInhabited`

English:
instance modelPiInhabited
  signature: [forall i, Inhabited (Hi i)]
  body: inferInstanceAs Inhabited (forall i, Hi i)

中文:
实例 modelPiInhabited
  签名: [对任意 i, Inhabited (Hi i)]
  定义体: inferInstanceAs Inhabited (forall i, Hi i)

Depends on / 依赖: Inhabited
-/
instance modelPiInhabited [forall i, Inhabited (Hi i)] : Inhabited (ModelPi Hi) :=
inferInstanceAs Inhabited (forall i, Hi i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, TopologicalSpace (Hi i)] : TopologicalSpace (ModelPi Hi)
  body: inferInstanceAs TopologicalSpace (forall i, Hi i)

中文:
实例 [forall
  签名: i, TopologicalSpace (Hi i)] : TopologicalSpace (ModelPi Hi)
  定义体: inferInstanceAs TopologicalSpace (forall i, Hi i)

Depends on / 依赖: TopologicalSpace
-/
instance [forall i, TopologicalSpace (Hi i)] : TopologicalSpace (ModelPi Hi) :=
inferInstanceAs TopologicalSpace (forall i, Hi i)

end

/--
Instance `prodChartedSpace` / 实例 `prodChartedSpace`

English:
instance prodChartedSpace
  signature: (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
  body: image2 OpenPartialHomeomorph.prod (atlas H M) (atlas H' M')
  chartAt x := (chartAt H x.1).prod (chartAt H' x.2)
  mem_chart_source x := ⟨mem_chart_source H x.1, mem_chart_source H' x.2⟩
  chart_mem_atlas x := mem_image2_of_mem (chart_mem_atlas H x.1) (chart_mem_atlas H' x.2)

中文:
实例 prodChartedSpace
  签名: (H : 类型) [TopologicalSpace H] (M : 类型) [TopologicalSpace M]
  定义体: image2 OpenPartialHomeomorph.prod (atlas H M) (atlas H' M')
  chartAt x := (chartAt H x.1).prod (chartAt H' x.2)
  mem_chart_source x := ⟨mem_chart_source H x.1, mem_chart_source H' x.2⟩
  chart_mem_atlas x := mem_image2_of_mem (chart_mem_atlas H x.1) (chart_mem_atlas H' x.2)

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.prod, image2
-/
instance prodChartedSpace (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (H' : Type*) [TopologicalSpace H'] (M' : Type*) [TopologicalSpace M']
    [ChartedSpace H' M'] : ChartedSpace (ModelProd H H') (M × M') where
  atlas := image2 OpenPartialHomeomorph.prod (atlas H M) (atlas H' M')
  chartAt x := (chartAt H x.1).prod (chartAt H' x.2)
  mem_chart_source x := ⟨mem_chart_source H x.1, mem_chart_source H' x.2⟩
  chart_mem_atlas x := mem_image2_of_mem (chart_mem_atlas H x.1) (chart_mem_atlas H' x.2)

section prodChartedSpace

@[ext]
/--
theorem `ModelProd.ext` / 定理 `ModelProd.ext`

English:
theorem ModelProd.ext
  given: {x y : ModelProd H H'} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2)
  statement: x = y
  proof: Prod.ext h₁ h₂

中文:
定理 ModelProd.ext
  条件: {x y : ModelProd H H'} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2)
  结论: x = y
  证明: Prod.ext h₁ h₂

Depends on / 依赖: Prod.ext
-/
theorem ModelProd.ext {x y : ModelProd H H'} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y :=
  Prod.ext h₁ h₂

variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {x : M × M'}

@[simp, mfld_simps]
/--
theorem `prodChartedSpace_chartAt` / 定理 `prodChartedSpace_chartAt`

English:
theorem prodChartedSpace_chartAt
  proof: rfl

中文:
定理 prodChartedSpace_chartAt
  证明: rfl
-/
theorem prodChartedSpace_chartAt :
    chartAt (ModelProd H H') x = (chartAt H x.fst).prod (chartAt H' x.snd) :=
  rfl

/--
theorem `chartedSpaceSelf_prod` / 定理 `chartedSpaceSelf_prod`

English:
theorem chartedSpaceSelf_prod
  statement: prodChartedSpace H H H' H' = chartedSpaceSelf (H × H')
  proof: by
  ext1
  · simp [atlas, ChartedSpace.atlas]
  · ext1
    simp only [prodChartedSpace_chartAt, chartAt_self_eq, refl_prod_refl]
    rfl

中文:
定理 chartedSpaceSelf_prod
  结论: prodChartedSpace H H H' H' = chartedSpaceSelf (H × H')
  证明: by
  ext1
  · simp [atlas, ChartedSpace.atlas]
  · ext1
    simp only [prodChartedSpace_chartAt, chartAt_self_eq, refl_prod_refl]
    rfl

Depends on / 依赖: ChartedSpace, ChartedSpace.atlas, chartAt_self_eq, prodChartedSpace_chartAt, refl_prod_refl
-/
theorem chartedSpaceSelf_prod : prodChartedSpace H H H' H' = chartedSpaceSelf (H × H') := by
  ext1
  · simp [atlas, ChartedSpace.atlas]
  · ext1
    simp only [prodChartedSpace_chartAt, chartAt_self_eq, refl_prod_refl]
    rfl

end prodChartedSpace

/--
Instance `piChartedSpace` / 实例 `piChartedSpace`

English:
instance piChartedSpace
  signature: {ι : Type*} [Finite ι] (H : ι -> Type*) [forall i, TopologicalSpace (H i)]
  body: OpenPartialHomeomorph.pi '' Set.pi univ fun _ => atlas (H _) (M _)
  chartAt f := OpenPartialHomeomorph.pi fun i => chartAt (H i) (f i)
  mem_chart_source f i _ := mem_chart_source (H i) (f i)
  chart_mem_atlas f := mem_image_of_mem _ fun i _ => chart_mem_atlas (H i) (f i)

@[simp, mfld_simps]

中文:
实例 piChartedSpace
  签名: {ι : 类型} [Finite ι] (H : ι -> 类型) [对任意 i, TopologicalSpace (H i)]
  定义体: OpenPartialHomeomorph.pi '' Set.pi univ fun _ => atlas (H _) (M _)
  chartAt f := OpenPartialHomeomorph.pi fun i => chartAt (H i) (f i)
  mem_chart_source f i _ := mem_chart_source (H i) (f i)
  chart_mem_atlas f := mem_image_of_mem _ fun i _ => chart_mem_atlas (H i) (f i)

@[simp, mfld_simps]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.pi, Set.pi
-/
instance piChartedSpace {ι : Type*} [Finite ι] (H : ι -> Type*) [forall i, TopologicalSpace (H i)]
    (M : ι -> Type*) [forall i, TopologicalSpace (M i)] [forall i, ChartedSpace (H i) (M i)] :
    ChartedSpace (ModelPi H) (forall i, M i) where
  atlas := OpenPartialHomeomorph.pi '' Set.pi univ fun _ => atlas (H _) (M _)
  chartAt f := OpenPartialHomeomorph.pi fun i => chartAt (H i) (f i)
  mem_chart_source f i _ := mem_chart_source (H i) (f i)
  chart_mem_atlas f := mem_image_of_mem _ fun i _ => chart_mem_atlas (H i) (f i)

@[simp, mfld_simps]
/--
theorem `piChartedSpace_chartAt` / 定理 `piChartedSpace_chartAt`

English:
theorem piChartedSpace_chartAt
  statement: {ι : Type*} [Finite ι] (H : ι -> Type*)
  proof: rfl

中文:
定理 piChartedSpace_chartAt
  结论: {ι : 类型} [Finite ι] (H : ι -> 类型)
  证明: rfl

Depends on / 依赖: ModelPi, OpenPartialHomeomorph, OpenPartialHomeomorph.pi, chartAt
-/
theorem piChartedSpace_chartAt {ι : Type*} [Finite ι] (H : ι -> Type*)
    [forall i, TopologicalSpace (H i)] (M : ι -> Type*) [forall i, TopologicalSpace (M i)]
    [forall i, ChartedSpace (H i) (M i)] (f : forall i, M i) :
    chartAt (H := ModelPi H) f = OpenPartialHomeomorph.pi fun i => chartAt (H i) (f i) :=
  rfl

end Products

section sum

variable [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace M']
    [cm : ChartedSpace H M] [cm' : ChartedSpace H M']

/-- The disjoint union of two charted spaces modelled on a non-empty space `H`
is a charted space over `H`. -/
@[instance_reducible]
/--
Definition of `ChartedSpace.sumOfNonempty` / `ChartedSpace.sumOfNonempty` 的定义

English:
definition ChartedSpace.sumOfNonempty
  signature: [Nonempty H]
  body: ((fun e => e.lift_openEmbedding IsOpenEmbedding.inl) '' cm.atlas) union
    ((fun e => e.lift_openEmbedding IsOpenEmbedding.inr) '' cm'.atlas)
  -- At `x : M`, the chart is the chart in `M`; at `x' ∈ M'`, it is the chart in `M'`.
  chartAt := Sum.elim (fun x => (cm.chartAt x).lift_openEmbedding IsOp

中文:
定义 ChartedSpace.sumOfNonempty
  签名: [Nonempty H]
  定义体: ((fun e => e.lift_openEmbedding IsOpenEmbedding.inl) '' cm.atlas) union
    ((fun e => e.lift_openEmbedding IsOpenEmbedding.inr) '' cm'.atlas)
  -- At `x : M`, the chart is the chart in `M`; at `x' ∈ M'`, it is the chart in `M'`.
  chartAt := Sum.elim (fun x => (cm.chartAt x).lift_openEmbedding IsOp

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.inl, cm.atlas, e.lift_openEmbedding, lift_openEmbedding
-/
def ChartedSpace.sumOfNonempty [Nonempty H] : ChartedSpace H (M oplus M') where
  atlas := ((fun e => e.lift_openEmbedding IsOpenEmbedding.inl) '' cm.atlas) union
    ((fun e => e.lift_openEmbedding IsOpenEmbedding.inr) '' cm'.atlas)
  -- At `x : M`, the chart is the chart in `M`; at `x' ∈ M'`, it is the chart in `M'`.
  chartAt := Sum.elim (fun x => (cm.chartAt x).lift_openEmbedding IsOpenEmbedding.inl)
    (fun x => (cm'.chartAt x).lift_openEmbedding IsOpenEmbedding.inr)
  mem_chart_source p := by
    cases p with
    | inl x =>
      rw [Sum.elim_inl]; rw [lift_openEmbedding_source]; rw [← OpenPartialHomeomorph.lift_openEmbedding_source _ IsOpenEmbedding.inl]
      use x, cm.mem_chart_source x
    | inr x =>
      rw [Sum.elim_inr]; rw [lift_openEmbedding_source]; rw [← OpenPartialHomeomorph.lift_openEmbedding_source _ IsOpenEmbedding.inr]
      use x, cm'.mem_chart_source x
  chart_mem_atlas p := by
    cases p with
    | inl x =>
      rw [Sum.elim_inl]
      left
      use ChartedSpace.chartAt x, cm.chart_mem_atlas x
    | inr x =>
      rw [Sum.elim_inr]
      right
      use ChartedSpace.chartAt x, cm'.chart_mem_atlas x

@[deprecated (since := "2026-07-26")]
alias ChartedSpace.sum_of_nonempty := ChartedSpace.sumOfNonempty

/--
Instance `ChartedSpace.sum` / 实例 `ChartedSpace.sum`

English:
instance ChartedSpace.sum
  signature: : ChartedSpace H (M oplus M')
  body: by
  by_cases! h : Nonempty H
  · exact ChartedSpace.sumOfNonempty
  have : IsEmpty M := isEmpty_of_chartedSpace H
  have : IsEmpty M' := isEmpty_of_chartedSpace H
  exact empty H (M oplus M')

中文:
实例 ChartedSpace.sum
  签名: : ChartedSpace H (M oplus M')
  定义体: by
  by_cases! h : Nonempty H
  · exact ChartedSpace.sumOfNonempty
  have : IsEmpty M := isEmpty_of_chartedSpace H
  have : IsEmpty M' := isEmpty_of_chartedSpace H
  exact empty H (M oplus M')

Depends on / 依赖: ChartedSpace, ChartedSpace.sumOfNonempty, IsEmpty, Nonempty, isEmpty_of_chartedSpace, sumOfNonempty
-/
instance ChartedSpace.sum : ChartedSpace H (M oplus M') := by
  by_cases! h : Nonempty H
  · exact ChartedSpace.sumOfNonempty
  have : IsEmpty M := isEmpty_of_chartedSpace H
  have : IsEmpty M' := isEmpty_of_chartedSpace H
  exact empty H (M oplus M')

/--
lemma `ChartedSpace.sum_chartAt_inl` / 引理 `ChartedSpace.sum_chartAt_inl`

English:
lemma ChartedSpace.sum_chartAt_inl
  given: (x : M)
  proof: nonempty_of_chartedSpace x
    chartAt H (Sum.inl x)
      = (chartAt H x).lift_openEmbedding (X' := M oplus M') IsOpenEmbedding.inl := by
  simp +instances only [chartAt, sum, nonempty_of_chartedSpace x, ↓reduceDIte]
  rfl

中文:
引理 ChartedSpace.sum_chartAt_inl
  条件: (x : M)
  证明: nonempty_of_chartedSpace x
    chartAt H (Sum.inl x)
      = (chartAt H x).lift_openEmbedding (X' := M oplus M') IsOpenEmbedding.inl := by
  simp +instances only [chartAt, sum, nonempty_of_chartedSpace x, ↓reduceDIte]
  rfl

Depends on / 依赖: nonempty_of_chartedSpace
-/
lemma ChartedSpace.sum_chartAt_inl (x : M) :
    haveI : Nonempty H := nonempty_of_chartedSpace x
    chartAt H (Sum.inl x)
      = (chartAt H x).lift_openEmbedding (X' := M oplus M') IsOpenEmbedding.inl := by
  simp +instances only [chartAt, sum, nonempty_of_chartedSpace x, ↓reduceDIte]
  rfl

/--
lemma `ChartedSpace.sum_chartAt_inr` / 引理 `ChartedSpace.sum_chartAt_inr`

English:
lemma ChartedSpace.sum_chartAt_inr
  given: (x' : M')
  proof: nonempty_of_chartedSpace x'
    chartAt H (Sum.inr x')
      = (chartAt H x').lift_openEmbedding (X' := M oplus M') IsOpenEmbedding.inr := by
  simp +instances only [chartAt, sum, nonempty_of_chartedSpace x', ↓reduceDIte]
  rfl

中文:
引理 ChartedSpace.sum_chartAt_inr
  条件: (x' : M')
  证明: nonempty_of_chartedSpace x'
    chartAt H (Sum.inr x')
      = (chartAt H x').lift_openEmbedding (X' := M oplus M') IsOpenEmbedding.inr := by
  simp +instances only [chartAt, sum, nonempty_of_chartedSpace x', ↓reduceDIte]
  rfl

Depends on / 依赖: nonempty_of_chartedSpace
-/
lemma ChartedSpace.sum_chartAt_inr (x' : M') :
    haveI : Nonempty H := nonempty_of_chartedSpace x'
    chartAt H (Sum.inr x')
      = (chartAt H x').lift_openEmbedding (X' := M oplus M') IsOpenEmbedding.inr := by
  simp +instances only [chartAt, sum, nonempty_of_chartedSpace x', ↓reduceDIte]
  rfl

/--
lemma `sum_chartAt_inl_apply` / 引理 `sum_chartAt_inl_apply`

English:
lemma sum_chartAt_inl_apply
  given: {x y : M}
  proof: by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [ChartedSpace.sum_chartAt_inl]
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _

中文:
引理 sum_chartAt_inl_apply
  条件: {x y : M}
  证明: by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [ChartedSpace.sum_chartAt_inl]
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _
-/
@[simp, mfld_simps] lemma sum_chartAt_inl_apply {x y : M} :
    (chartAt H (.inl x : M oplus M')) (Sum.inl y) = (chartAt H x) y := by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [ChartedSpace.sum_chartAt_inl]
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _

/--
lemma `sum_chartAt_inr_apply` / 引理 `sum_chartAt_inr_apply`

English:
lemma sum_chartAt_inr_apply
  given: {x y : M'}
  proof: by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [ChartedSpace.sum_chartAt_inr]
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _

中文:
引理 sum_chartAt_inr_apply
  条件: {x y : M'}
  证明: by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [ChartedSpace.sum_chartAt_inr]
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _
-/
@[simp, mfld_simps] lemma sum_chartAt_inr_apply {x y : M'} :
    (chartAt H (.inr x : M oplus M')) (Sum.inr y) = (chartAt H x) y := by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [ChartedSpace.sum_chartAt_inr]
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _

/--
lemma `ChartedSpace.mem_atlas_sum` / 引理 `ChartedSpace.mem_atlas_sum`

English:
lemma ChartedSpace.mem_atlas_sum
  statement: [h : Nonempty H]
  proof: by
  simp +instances only [atlas, sum, h, ↓reduceDIte] at he
  obtain (⟨x, hx, hxe⟩ | ⟨x, hx, hxe⟩) := he
  · rw [← hxe]; left; use x
  · rw [← hxe]; right; use x

中文:
引理 ChartedSpace.mem_atlas_sum
  结论: [h : Nonempty H]
  证明: by
  simp +instances only [atlas, sum, h, ↓reduceDIte] at he
  obtain (⟨x, hx, hxe⟩ | ⟨x, hx, hxe⟩) := he
  · rw [← hxe]; left; use x
  · rw [← hxe]; right; use x

Depends on / 依赖: instances, reduceDIte
-/
lemma ChartedSpace.mem_atlas_sum [h : Nonempty H]
    {e : OpenPartialHomeomorph (M oplus M') H} (he : e in atlas H (M oplus M')) :
    (exists f : OpenPartialHomeomorph M H, f in (atlas H M)
      ∧ e = (f.lift_openEmbedding IsOpenEmbedding.inl))
    ∨ (exists f' : OpenPartialHomeomorph M' H, f' in (atlas H M') ∧
      e = (f'.lift_openEmbedding IsOpenEmbedding.inr)) := by
  simp +instances only [atlas, sum, h, ↓reduceDIte] at he
  obtain (⟨x, hx, hxe⟩ | ⟨x, hx, hxe⟩) := he
  · rw [← hxe]; left; use x
  · rw [← hxe]; right; use x

end sum

section IsLocalHomeomorph

variable [TopologicalSpace M] [TopologicalSpace M'] [TopologicalSpace H] [ChartedSpace H M]

/-- Given a right inverse for a local homeomorphism `f : M → M'`, endow `M'` with a `ChartedSpace`
structure by pushing forward the `ChartedSpace` structure from `M`. -/
@[instance_reducible]
/--
Definition of `IsLocalHomeomorph.chartedSpaceOfRightInverse` / `IsLocalHomeomorph.chartedSpaceOfRightInverse` 的定义

English:
definition IsLocalHomeomorph.chartedSpaceOfRightInverse
  body: {(hf.localInverseAt (g q)).trans (chartAt H (g q)) | q : M'}
  chartAt q := (hf.localInverseAt (g q)).trans (chartAt H (g q))
  mem_chart_source q := by
    nth_rw 3 [← hg.eq q]
    simp
  chart_mem_atlas := by simp

中文:
定义 IsLocalHomeomorph.chartedSpaceOfRightInverse
  定义体: {(hf.localInverseAt (g q)).trans (chartAt H (g q)) | q : M'}
  chartAt q := (hf.localInverseAt (g q)).trans (chartAt H (g q))
  mem_chart_source q := by
    nth_rw 3 [← hg.eq q]
    simp
  chart_mem_atlas := by simp

Depends on / 依赖: chartAt, hf.localInverseAt, localInverseAt
-/
def IsLocalHomeomorph.chartedSpaceOfRightInverse
    {f : M -> M'} (hf : IsLocalHomeomorph f) {g : M' -> M} (hg : Function.RightInverse g f) :
    ChartedSpace H M' where
  atlas := {(hf.localInverseAt (g q)).trans (chartAt H (g q)) | q : M'}
  chartAt q := (hf.localInverseAt (g q)).trans (chartAt H (g q))
  mem_chart_source q := by
    nth_rw 3 [← hg.eq q]
    simp
  chart_mem_atlas := by simp

/-- Given a surjective local homeomorphism `f : M → M'`, endow `M'` with a `ChartedSpace` structure
by pushing forward the `ChartedSpace` structure from `M`. -/
@[instance_reducible]
/--
Definition of `IsLocalHomeomorph.chartedSpace` / `IsLocalHomeomorph.chartedSpace` 的定义

English:
definition IsLocalHomeomorph.chartedSpace
  body: hf.chartedSpaceOfRightInverse hf'.hasRightInverse.choose_spec

中文:
定义 IsLocalHomeomorph.chartedSpace
  定义体: hf.chartedSpaceOfRightInverse hf'.hasRightInverse.choose_spec

Depends on / 依赖: chartedSpaceOfRightInverse, choose_spec, hasRightInverse, hasRightInverse.choose_spec, hf.chartedSpaceOfRightInverse
-/
def IsLocalHomeomorph.chartedSpace
    {f : M -> M'} (hf : IsLocalHomeomorph f) (hf' : Function.Surjective f) :
    ChartedSpace H M' :=
  hf.chartedSpaceOfRightInverse hf'.hasRightInverse.choose_spec

/-- Given a homeomorphism `f : M ≃ₜ M'`, endow `M'` with a `ChartedSpace` structure by pushing
forward the `ChartedSpace` structure from `M`. -/
@[implicit_reducible]
/--
Definition of `Homeomorph.chartedSpace` / `Homeomorph.chartedSpace` 的定义

English:
definition Homeomorph.chartedSpace
  signature: (f : M ≃ₜ M')
  body: f.isLocalHomeomorph.chartedSpace f.surjective

中文:
定义 Homeomorph.chartedSpace
  签名: (f : M ≃ₜ M')
  定义体: f.isLocalHomeomorph.chartedSpace f.surjective

Depends on / 依赖: chartedSpace, f.isLocalHomeomorph.chartedSpace, f.surjective, isLocalHomeomorph, surjective
-/
def Homeomorph.chartedSpace (f : M ≃ₜ M') : ChartedSpace H M' :=
  f.isLocalHomeomorph.chartedSpace f.surjective

end IsLocalHomeomorph

end Constructions

end ChartedSpace

/-! ### Constructing a topology from an atlas -/

/--
Definition of `ChartedSpaceCore` / `ChartedSpaceCore` 的定义

English:
structure ChartedSpaceCore
  parameters: (H : Type*) [TopologicalSpace H] (M : Type*)
  axioms and operations (6):
    - atlas : Set (PartialEquiv M H)
    - chartAt : M -> PartialEquiv M H
    - mem_chart_source : forall x, x in (chartAt x).source
    - chart_mem_atlas : forall x, chartAt x in atlas
    - open_source : forall e e' : PartialEquiv M H, e in atlas -> e' in atlas -> IsOpen (e.symm.trans e').source
    - continuousOn_toFun : forall e e' : PartialEquiv M H, e in atlas -> e' in atlas -> ContinuousOn (e.symm.trans e') (e.symm.trans e').source

中文:
结构 ChartedSpaceCore
  参数: (H : 类型) [TopologicalSpace H] (M : 类型)
  公理与运算 (6 个):
    - atlas : Set (PartialEquiv M H)
    - chartAt : M -> PartialEquiv M H
    - mem_chart_source : 对任意 x, x in (chartAt x).source
    - chart_mem_atlas : 对任意 x, chartAt x in atlas
    - open_source : 对任意 e e' : PartialEquiv M H, e in atlas -> e' in atlas -> IsOpen (e.symm.trans e').source
    - continuousOn_toFun : 对任意 e e' : PartialEquiv M H, e in atlas -> e' in atlas -> ContinuousOn (e.symm.trans e') (e.symm.trans e').source
-/
structure ChartedSpaceCore (H : Type*) [TopologicalSpace H] (M : Type*) where
  /-- An atlas of charts, which are only `PartialEquiv`s -/
  atlas : Set (PartialEquiv M H)
  /-- The preferred chart at each point -/
  chartAt : M -> PartialEquiv M H
  mem_chart_source : forall x, x in (chartAt x).source
  chart_mem_atlas : forall x, chartAt x in atlas
  open_source : forall e e' : PartialEquiv M H, e in atlas -> e' in atlas -> IsOpen (e.symm.trans e').source
  continuousOn_toFun : forall e e' : PartialEquiv M H, e in atlas -> e' in atlas ->
    ContinuousOn (e.symm.trans e') (e.symm.trans e').source

namespace ChartedSpaceCore

variable [TopologicalSpace H] (c : ChartedSpaceCore H M) {e : PartialEquiv M H}

/-- Topology generated by a set of charts on a Type. -/
@[instance_reducible]
/--
Definition of `toTopologicalSpace` / `toTopologicalSpace` 的定义

English:
definition toTopologicalSpace
  signature: : TopologicalSpace M
  body: TopologicalSpace.generateFrom
    ⋃ (e : PartialEquiv M H) (_ : e in c.atlas) (s : Set H) (_ : IsOpen s),
      {e ⁻¹' s inter e.source}

中文:
定义 toTopologicalSpace
  签名: : TopologicalSpace M
  定义体: TopologicalSpace.generateFrom
    ⋃ (e : PartialEquiv M H) (_ : e in c.atlas) (s : Set H) (_ : IsOpen s),
      {e ⁻¹' s inter e.source}
-/
protected def toTopologicalSpace : TopologicalSpace M :=
TopologicalSpace.generateFrom
    ⋃ (e : PartialEquiv M H) (_ : e in c.atlas) (s : Set H) (_ : IsOpen s),
      {e ⁻¹' s inter e.source}

/--
theorem `open_source'` / 定理 `open_source'`

English:
theorem open_source'
  given: (he : e in c.atlas)
  statement: IsOpen[c.toTopologicalSpace] e.source
  proof: by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [exists_prop, mem_iUnion, mem_singleton_iff]
  refine ⟨e, he, univ, isOpen_univ, ?_⟩
  simp only [Set.univ_inter, Set.preimage_univ]

中文:
定理 open_source'
  条件: (he : e in c.atlas)
  结论: IsOpen[c.toTopologicalSpace] e.source
  证明: by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [exists_prop, mem_iUnion, mem_singleton_iff]
  refine ⟨e, he, univ, isOpen_univ, ?_⟩
  simp only [Set.univ_inter, Set.preimage_univ]

Depends on / 依赖: GenerateOpen, Set.preimage_univ, Set.univ_inter, TopologicalSpace, TopologicalSpace.GenerateOpen.basic, exists_prop, isOpen_univ, mem_iUnion, mem_singleton_iff, preimage_univ, univ_inter
-/
theorem open_source' (he : e in c.atlas) : IsOpen[c.toTopologicalSpace] e.source := by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [exists_prop, mem_iUnion, mem_singleton_iff]
  refine ⟨e, he, univ, isOpen_univ, ?_⟩
  simp only [Set.univ_inter, Set.preimage_univ]

/--
theorem `open_target` / 定理 `open_target`

English:
theorem open_target
  given: (he : e in c.atlas)
  statement: IsOpen e.target
  proof: by
  have E : e.target inter e.symm ⁻¹' e.source = e.target :=
    Subset.antisymm inter_subset_left fun x hx =>
      ⟨hx, PartialEquiv.target_subset_preimage_source _ hx⟩
  simpa [PartialEquiv.trans_source, E] using c.open_source e e he he

中文:
定理 open_target
  条件: (he : e in c.atlas)
  结论: IsOpen e.target
  证明: by
  have E : e.target inter e.symm ⁻¹' e.source = e.target :=
    Subset.antisymm inter_subset_left fun x hx =>
      ⟨hx, PartialEquiv.target_subset_preimage_source _ hx⟩
  simpa [PartialEquiv.trans_source, E] using c.open_source e e he he

Depends on / 依赖: PartialEquiv, PartialEquiv.target_subset_preimage_source, PartialEquiv.trans_source, Subset, Subset.antisymm, antisymm, c.open_source, e.source, e.symm, e.target, inter_subset_left, open_source, source, target, target_subset_preimage_source, trans_source
-/
theorem open_target (he : e in c.atlas) : IsOpen e.target := by
  have E : e.target inter e.symm ⁻¹' e.source = e.target :=
    Subset.antisymm inter_subset_left fun x hx =>
      ⟨hx, PartialEquiv.target_subset_preimage_source _ hx⟩
  simpa [PartialEquiv.trans_source, E] using c.open_source e e he he

/--
Definition of `openPartialHomeomorph` / `openPartialHomeomorph` 的定义

English:
definition openPartialHomeomorph
  signature: (e : PartialEquiv M H) (he : e in c.atlas)
  body: { __ := c.toTopologicalSpace
    __ := e
    open_source := by convert! c.open_source' he
    open_target := by convert! c.open_target he
    continuousOn_toFun := by
      let : TopologicalSpace M := c.toTopologicalSpace
      rw [continuousOn_open_iff (c.open_source' he)]
      intro s s_open
    

中文:
定义 openPartialHomeomorph
  签名: (e : PartialEquiv M H) (he : e in c.atlas)
  定义体: { __ := c.toTopologicalSpace
    __ := e
    open_source := by convert! c.open_source' he
    open_target := by convert! c.open_target he
    continuousOn_toFun := by
      let : TopologicalSpace M := c.toTopologicalSpace
      rw [continuousOn_open_iff (c.open_source' he)]
      intro s s_open
    
-/
protected def openPartialHomeomorph (e : PartialEquiv M H) (he : e in c.atlas) :
    @OpenPartialHomeomorph M H c.toTopologicalSpace _ :=
  { __ := c.toTopologicalSpace
    __ := e
    open_source := by convert! c.open_source' he
    open_target := by convert! c.open_target he
    continuousOn_toFun := by
      let : TopologicalSpace M := c.toTopologicalSpace
      rw [continuousOn_open_iff (c.open_source' he)]
      intro s s_open
      rw [inter_comm]
      apply TopologicalSpace.GenerateOpen.basic
      simp only [exists_prop, mem_iUnion, mem_singleton_iff]
      exact ⟨e, he, ⟨s, s_open, rfl⟩⟩
    continuousOn_invFun := by
      let : TopologicalSpace M := c.toTopologicalSpace
      apply continuousOn_isOpen_of_generateFrom
      intro t ht
      simp only [exists_prop, mem_iUnion, mem_singleton_iff] at ht
      rcases ht with ⟨e', e'_atlas, s, s_open, ts⟩
      rw [ts]
      let f := e.symm.trans e'
      have : IsOpen (f ⁻¹' s inter f.source) := by
        simpa [f, inter_comm] using (continuousOn_open_iff (c.open_source e e' he e'_atlas)).1
          (c.continuousOn_toFun e e' he e'_atlas) s s_open
      have A : e' ∘ e.symm ⁻¹' s inter (e.target inter e.symm ⁻¹' e'.source) =
          e.target inter (e' ∘ e.symm ⁻¹' s inter e.symm ⁻¹' e'.source) := by
        rw [← inter_assoc]; rw [← inter_assoc]
        congr 1
        exact inter_comm _ _
      simpa [f, PartialEquiv.trans_source, preimage_inter, preimage_comp.symm, A] using this }

/-- Given a charted space without topology, endow it with a genuine charted space structure with
respect to the topology constructed from the atlas. -/
@[instance_reducible]
/--
Definition of `toChartedSpace` / `toChartedSpace` 的定义

English:
definition toChartedSpace
  signature: : @ChartedSpace H _ M c.toTopologicalSpace
  body: { __ := c.toTopologicalSpace
    atlas := ⋃ (e : PartialEquiv M H) (he : e in c.atlas), {c.openPartialHomeomorph e he}
    chartAt := fun x => c.openPartialHomeomorph (c.chartAt x) (c.chart_mem_atlas x)
    mem_chart_source := fun x => c.mem_chart_source x
    chart_mem_atlas := fun x => by
      si

中文:
定义 toChartedSpace
  签名: : @ChartedSpace H _ M c.toTopologicalSpace
  定义体: { __ := c.toTopologicalSpace
    atlas := ⋃ (e : PartialEquiv M H) (he : e in c.atlas), {c.openPartialHomeomorph e he}
    chartAt := fun x => c.openPartialHomeomorph (c.chartAt x) (c.chart_mem_atlas x)
    mem_chart_source := fun x => c.mem_chart_source x
    chart_mem_atlas := fun x => by
      si

Depends on / 依赖: PartialEquiv, c.atlas, c.chartAt, c.chart_mem_atlas, c.mem_chart_source, c.openPartialHomeomorph, c.toTopologicalSpace, chartAt, chart_mem_atlas, mem_chart_source, mem_iUnion, mem_singleton_iff, openPartialHomeomorph, toTopologicalSpace
-/
def toChartedSpace : @ChartedSpace H _ M c.toTopologicalSpace :=
  { __ := c.toTopologicalSpace
    atlas := ⋃ (e : PartialEquiv M H) (he : e in c.atlas), {c.openPartialHomeomorph e he}
    chartAt := fun x => c.openPartialHomeomorph (c.chartAt x) (c.chart_mem_atlas x)
    mem_chart_source := fun x => c.mem_chart_source x
    chart_mem_atlas := fun x => by
      simp only [mem_iUnion, mem_singleton_iff]
      exact ⟨c.chartAt x, c.chart_mem_atlas x, rfl⟩}

end ChartedSpaceCore
