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
/-
**ChartedSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(H : Type u_5) → [TopologicalSpace H] → (M : Type u_6) → [TopologicalSpace
 M] → Type (max u_5 u_6)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A charted space is a topological space endowed with an atlas, i.e., a set of loc
al
homeomorphisms taking values in a model space `H`, called charts, such that the 
domains of the
charts cover the whole space. We express the covering property by choosing for e
ach `x` a member
`chartAt x` of the atlas containing `x` in its source: in the smooth case, this 
is convenient to
construct the tangent bundle in an efficient way.
The model space is written as an explicit parameter as there can be several mode
l spaces for a
given topological space. For instance, a complex manifold (modelled over `ℂ^n`) 
will also be seen
sometimes as a real manifold over `ℝ^(2n)`.
-/
class ChartedSpace (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M] where
  /-- The atlas of charts in the `ChartedSpace`. -/
  protected atlas : Set (OpenPartialHomeomorph M H)
  /-- The preferred chart at each point in the charted space. -/
  protected chartAt : M → OpenPartialHomeomorph M H
  protected mem_chart_source : ∀ x, x ∈ (chartAt x).source
  protected chart_mem_atlas : ∀ x, chartAt x ∈ atlas

/-- The atlas of charts in a `ChartedSpace`. -/
/-
**atlas** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：atlas (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M] [C
hartedSpace H M] : Set (OpenPartialHomeomorph M H)
参数：H : Type*；M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The atlas of charts in a `ChartedSpace`.
-/
abbrev atlas (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Set (OpenPartialHomeomorph M H) :=
  ChartedSpace.atlas

/-- The preferred chart at a point `x` in a charted space `M`. -/
/-
**chartAt** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：chartAt (H : Type*) [TopologicalSpace H] {M : Type*} [TopologicalSpace M] 
[ChartedSpace H M] (x : M) : OpenPartialHomeomorph M H
参数：H : Type*；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preferred chart at a point `x` in a charted space `M`.
-/
abbrev chartAt (H : Type*) [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : OpenPartialHomeomorph M H :=
  ChartedSpace.chartAt x

@[simp, mfld_simps]
/-
**mem_chart_source** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_chart_source (H : Type*) {M : Type*} [TopologicalSpace H] [Topological
Space M] [ChartedSpace H M] (x : M) : x in (chartAt H x).source
参数：H : Type*；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ChartedSpace.mem_chart_source`：∀ {H : Type u_5} {inst : TopologicalSpace
 H} {M : Type u_6} {inst_1 : TopologicalSpace M} [self : ChartedSpace H M]   (x 
: M), x ∈ (ChartedS…
-/
lemma mem_chart_source (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : x ∈ (chartAt H x).source :=
  ChartedSpace.mem_chart_source x

@[simp, mfld_simps]
/-
**chart_mem_atlas** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalS
pace M] [ChartedSpace H M] (x : M) : chartAt H x in atlas H M
参数：H : Type*；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ChartedSpace.chart_mem_atlas`：∀ {H : Type u_5} {inst : TopologicalSpace 
H} {M : Type u_6} {inst_1 : TopologicalSpace M} [self : ChartedSpace H M]   (x :
 M), ChartedSpace.…
-/
lemma chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : chartAt H x ∈ atlas H M :=
  ChartedSpace.chart_mem_atlas x
/-
**nonempty_of_chartedSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonempty_of_chartedSpace {H : Type*} {M : Type*} [TopologicalSpace H] [Top
ologicalSpace M] [ChartedSpace H M] (x : M) : Nonempty H
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nonempty_of_chartedSpace {H : Type*} {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : Nonempty H :=
  ⟨chartAt H x x⟩
/-
**isEmpty_of_chartedSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isEmpty_of_chartedSpace (H : Type*) {M : Type*} [TopologicalSpace H] [Topo
logicalSpace M] [ChartedSpace H M] [IsEmpty H] : IsEmpty M
参数：H : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
-/
lemma isEmpty_of_chartedSpace (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] [IsEmpty H] : IsEmpty M := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x⟩⟩
  · exact hM
  · exact (IsEmpty.false (chartAt H x x)).elim

section ChartedSpace

section

variable (H) [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

/-
**mem_chart_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_chart_target (x : M) : chartAt H x x in (chartAt H x).target
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
-/
theorem mem_chart_target (x : M) : chartAt H x x ∈ (chartAt H x).target :=
  (chartAt H x).map_source (mem_chart_source _ _)
/-
**chart_source_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：chart_source_mem_nhds (x : M) : (chartAt H x).source in 𝓝 x
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
-/
theorem chart_source_mem_nhds (x : M) : (chartAt H x).source ∈ 𝓝 x :=
  (chartAt H x).open_source.mem_nhds <| mem_chart_source H x
/-
**chart_target_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：chart_target_mem_nhds (x : M) : (chartAt H x).target in 𝓝 (chartAt H x x)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `mem_chart_target`：mem_chart_target (x : M) : chartAt H x x in (chartAt H
 x).target
-/
theorem chart_target_mem_nhds (x : M) : (chartAt H x).target ∈ 𝓝 (chartAt H x x) :=
  (chartAt H x).open_target.mem_nhds <| mem_chart_target H x

variable (M) in
@[simp]
/-
**iUnion_source_chartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_source_chartAt : (⋃ x : M, (chartAt H x).source) = (univ : Set M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
-/
theorem iUnion_source_chartAt : (⋃ x : M, (chartAt H x).source) = (univ : Set M) :=
  eq_univ_iff_forall.mpr fun x ↦ mem_iUnion.mpr ⟨x, mem_chart_source H x⟩
/-
**ChartedSpace.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ChartedSpace.isOpen_iff (s : Set M) : IsOpen s ↔ forall x : M, IsOpen char
tAt H x '' ((chartAt H x).source inter s)
参数：s : Set M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isOpen_iff_of_cover`：isOpen_iff_of_cover {f : α -> Set X} (ho : forall i
, IsOpen (f i)) (hU : (⋃ i, f i) = univ) : IsOpen s ↔ forall i, IsOpen (f i inte
r s)
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `iUnion_source_chartAt`：iUnion_source_chartAt : (⋃ x : M, (chartAt H x).s
ource) = (univ : Set M)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `OpenPartialHomeomorph.isOpen_image_iff_of_subset_source`：isOpen_image_if
f_of_subset_source {s : Set X} (hs : s subseteq e.source) : IsOpen (e '' s) ↔ Is
Open s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ChartedSpace.isOpen_iff (s : Set M) :
    IsOpen s ↔ ∀ x : M, IsOpen <| chartAt H x '' ((chartAt H x).source ∩ s) := by
  rw [isOpen_iff_of_cover (fun i ↦ (chartAt H i).open_source) (iUnion_source_chartAt H M)]
  simp only [(chartAt H _).isOpen_image_iff_of_subset_source inter_subset_left]

/-- `achart H x` is the chart at `x`, considered as an element of the atlas.
Especially useful for working with `BasicContMDiffVectorBundleCore`. -/
/-
**achart** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：achart (x : M) : atlas H M
参数：x : M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `chart_mem_atlas`：chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpa
ce H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : chartAt H x in atlas H M

--- 原说明 ---
`achart H x` is the chart at `x`, considered as an element of the atlas.
Especially useful for working with `BasicContMDiffVectorBundleCore`.
-/
def achart (x : M) : atlas H M :=
  ⟨chartAt H x, chart_mem_atlas H x⟩
/-
**achart_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：achart_def (x : M) : achart H x = ⟨chartAt H x, chart_mem_atlas H x⟩
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem achart_def (x : M) : achart H x = ⟨chartAt H x, chart_mem_atlas H x⟩ :=
  rfl

@[simp, mfld_simps]
/-
**coe_achart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_achart (x : M) : (achart H x : OpenPartialHomeomorph M H) = chartAt H 
x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_achart (x : M) : (achart H x : OpenPartialHomeomorph M H) = chartAt H x :=
  rfl

@[simp, mfld_simps]
/-
**achart_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：achart_val (x : M) : (achart H x).1 = chartAt H x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem achart_val (x : M) : (achart H x).1 = chartAt H x :=
  rfl
/-
**mem_achart_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_achart_source (x : M) : x in (achart H x).1.source
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
-/
theorem mem_achart_source (x : M) : x ∈ (achart H x).1.source :=
  mem_chart_source H x

open TopologicalSpace
/-
**ChartedSpace.secondCountable_of_countable_cover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ChartedSpace.secondCountable_of_countable_cover [SecondCountableTopology H
] {s : Set M} (hs : ⋃ (x) (_ : x in s), (chartAt H x).source = univ) (hsc : s.Co
untable) : SecondCountableTopology M
参数：hs : ⋃ (x) (_ : x in s), (chartAt H x).source = univ；hsc : s.Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.secondCountableTopology_source`：secondCountableTop
ology_source [SecondCountableTopology Y] : SecondCountableTopology e.source
· 使用定理 `TopologicalSpace.secondCountableTopology_of_countable_cover`：secondCount
ableTopology_of_countable_cover {ι} [Countable ι] {U : ι -> Set α} [forall i, Se
condCountableTopology (U i)] (Uo : forall i, IsOp…
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
-/
theorem ChartedSpace.secondCountable_of_countable_cover [SecondCountableTopology H] {s : Set M}
    (hs : ⋃ (x) (_ : x ∈ s), (chartAt H x).source = univ) (hsc : s.Countable) :
    SecondCountableTopology M := by
  have : ∀ x : M, SecondCountableTopology (chartAt H x).source :=
    fun x ↦ (chartAt (H := H) x).secondCountableTopology_source
  have := hsc.toEncodable
  rw [biUnion_eq_iUnion] at hs
  exact secondCountableTopology_of_countable_cover (fun x : s ↦ (chartAt H (x : M)).open_source) hs

variable (M)
/-
**ChartedSpace.secondCountable_of_sigmaCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ChartedSpace.secondCountable_of_sigmaCompact [SecondCountableTopology H] [
SigmaCompactSpace M] : SecondCountableTopology M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `countable_cover_nhds_of_sigmaCompact`：countable_cover_nhds_of_sigmaCompa
ct {f : X -> Set X} (hf : forall x, f x in 𝓝 x) : exists s : Set X, s.Countable 
∧ ⋃ x in s, f x = univ
· 使用定理 `chart_source_mem_nhds`：chart_source_mem_nhds (x : M) : (chartAt H x).sou
rce in 𝓝 x
· 使用定理 `ChartedSpace.secondCountable_of_countable_cover`：ChartedSpace.secondCoun
table_of_countable_cover [SecondCountableTopology H] {s : Set M} (hs : ⋃ (x) (_ 
: x in s), (chartAt H x).source = uni…
-/
theorem ChartedSpace.secondCountable_of_sigmaCompact [SecondCountableTopology H]
    [SigmaCompactSpace M] : SecondCountableTopology M := by
  obtain ⟨s, hsc, hsU⟩ : ∃ s, Set.Countable s ∧ ⋃ (x) (_ : x ∈ s), (chartAt H x).source = univ :=
    countable_cover_nhds_of_sigmaCompact fun x : M ↦ chart_source_mem_nhds H x
  exact ChartedSpace.secondCountable_of_countable_cover H hsU hsc

/-- If a topological space admits an atlas with locally compact charts, then the space itself
is locally compact. -/
/-
**ChartedSpace.locallyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ChartedSpace.locallyCompactSpace [LocallyCompactSpace H] : LocallyCompactS
pace M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.symm_map_nhds_eq`：symm_map_nhds_eq {x} (hx : x in 
e.source) : map e.symm (𝓝 (e x)) = 𝓝 x
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.HasBasis.hasBasis_self_subset`：∀ {α : Type u_1} {l : Filter α} {p
 : Set α → Prop},   l.HasBasis (fun s => s ∈ l ∧ p s) id → ∀ {V : Set α}, V ∈ l 
→ l.HasBasis (fun s => s ∈…
· 使用定理 `compact_basis_nhds`：compact_basis_nhds [LocallyCompactSpace X] (x : X) :
 (𝓝 x).HasBasis (fun s => s in 𝓝 x ∧ IsCompact s) fun s => s
· 使用定理 `chart_target_mem_nhds`：chart_target_mem_nhds (x : M) : (chartAt H x).tar
get in 𝓝 (chartAt H x x)
· 使用定理 `LocallyCompactSpace.of_hasBasis`：LocallyCompactSpace.of_hasBasis {ι : X 
-> Type*} {p : forall x, ι x -> Prop} {s : forall x, ι x -> Set X} (h : forall x
, (𝓝 x).HasBasis (p x…
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `OpenPartialHomeomorph.continuousOn_symm`：continuousOn_symm : ContinuousO
n e.symm e.target

--- 原说明 ---
If a topological space admits an atlas with locally compact charts, then the spa
ce itself
is locally compact.
-/
theorem ChartedSpace.locallyCompactSpace [LocallyCompactSpace H] : LocallyCompactSpace M := by
  have : ∀ x : M, (𝓝 x).HasBasis
      (fun s ↦ s ∈ 𝓝 (chartAt H x x) ∧ IsCompact s ∧ s ⊆ (chartAt H x).target)
      fun s ↦ (chartAt H x).symm '' s := fun x ↦ by
    rw [← (chartAt H x).symm_map_nhds_eq (mem_chart_source H x)]
    exact ((compact_basis_nhds (chartAt H x x)).hasBasis_self_subset
      (chart_target_mem_nhds H x)).map _
  refine .of_hasBasis this ?_
  rintro x s ⟨_, h₂, h₃⟩
  exact h₂.image_of_continuousOn ((chartAt H x).continuousOn_symm.mono h₃)

/-- If a topological space admits an atlas with locally connected charts, then the space itself is
locally connected. -/
/-
**ChartedSpace.locallyConnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ChartedSpace.locallyConnectedSpace [LocallyConnectedSpace H] : LocallyConn
ectedSpace M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `locallyConnectedSpace_of_connected_bases`：locallyConnectedSpace_of_conne
cted_bases {ι : Type*} (b : α -> ι -> Set α) (p : α -> ι -> Prop) (hbasis : fora
ll x, (𝓝 x).HasBasis (p x) (b …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OpenPartialHomeomorph.symm_map_nhds_eq`：symm_map_nhds_eq {x} (hx : x in 
e.source) : map e.symm (𝓝 (e x)) = 𝓝 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.HasBasis.restrict_subset`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fi
lter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {V : Set α}, V ∈ l 
→ l.HasBasis (fun i =…
· 使用定理 `LocallyConnectedSpace.open_connected_basis`：∀ {α : Type u_3} {inst : Top
ologicalSpace α} [self : LocallyConnectedSpace α] (x : α),   (nhds x).HasBasis (
fun s => IsOpen s ∧ x ∈ s ∧ IsCo…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `mem_chart_target`：mem_chart_target (x : M) : chartAt H x x in (chartAt H
 x).target
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `OpenPartialHomeomorph.continuousOn_symm`：continuousOn_symm : ContinuousO
n e.symm e.target

--- 原说明 ---
If a topological space admits an atlas with locally connected charts, then the s
pace itself is
locally connected.
-/
theorem ChartedSpace.locallyConnectedSpace [LocallyConnectedSpace H] : LocallyConnectedSpace M := by
  let e : M → OpenPartialHomeomorph M H := chartAt H
  refine locallyConnectedSpace_of_connected_bases (fun x s ↦ (e x).symm '' s)
      (fun x s ↦ (IsOpen s ∧ e x x ∈ s ∧ IsConnected s) ∧ s ⊆ (e x).target) ?_ ?_
  · intro x
    simpa only [e, OpenPartialHomeomorph.symm_map_nhds_eq, mem_chart_source] using!
      ((LocallyConnectedSpace.open_connected_basis (e x x)).restrict_subset
        ((e x).open_target.mem_nhds (mem_chart_target H x))).map (e x).symm
  · rintro x s ⟨⟨-, -, hsconn⟩, hssubset⟩
    exact hsconn.isPreconnected.image _ ((e x).continuousOn_symm.mono hssubset)

/-- If a topological space `M` admits an atlas with locally path-connected charts,
then `M` itself is locally path-connected. -/
/-
**ChartedSpace.locallyPathConnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ChartedSpace.locallyPathConnectedSpace [LocallyPathConnectedSpace H] : Loc
allyPathConnectedSpace M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `chart_source_mem_nhds`：chart_source_mem_nhds (x : M) : (chartAt H x).sou
rce in 𝓝 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `OpenPartialHomeomorph.image_mem_nhds`：image_mem_nhds {x} (hx : x in e.so
urce) {s : Set X} (hs : s in 𝓝 x) : e '' s in 𝓝 (e x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `pathComponentIn_mem_nhds`：pathComponentIn_mem_nhds (hF : F in 𝓝 x) : pat
hComponentIn F x in 𝓝 x
· 使用定理 `IsPathConnected.image'`：IsPathConnected.image' (hF : IsPathConnected F) 
{f : X -> Y} (hf : ContinuousOn f F) : IsPathConnected (f '' F)
· 使用定理 `isPathConnected_pathComponentIn`：isPathConnected_pathComponentIn (h : x 
in F) : IsPathConnected (pathComponentIn F x)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `OpenPartialHomeomorph.continuousOn_symm`：continuousOn_symm : ContinuousO
n e.symm e.target
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `pathComponentIn_subset`：pathComponentIn_subset : pathComponentIn F x sub
seteq F
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用引理 `OpenPartialHomeomorph.image_source_subset`：image_source_subset : e '' e.
source subseteq e.target
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `PartialEquiv.symm_image_image_of_subset_source`：symm_image_image_of_subs
et_source {s : Set α} (h : s subseteq e.source) : e.symm '' e '' s = s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If a topological space `M` admits an atlas with locally path-connected charts,
then `M` itself is locally path-connected.
-/
theorem ChartedSpace.locallyPathConnectedSpace [LocallyPathConnectedSpace H] :
    LocallyPathConnectedSpace M := by
  refine ⟨fun x ↦ ⟨fun s ↦ ⟨fun hs ↦ ?_, fun ⟨u, hu⟩ ↦ Filter.mem_of_superset hu.1.1 hu.2⟩⟩⟩
  let e := chartAt H x
  let t := s ∩ e.source
  have ht : t ∈ 𝓝 x := Filter.inter_mem hs (chart_source_mem_nhds _ _)
  refine ⟨e.symm '' pathComponentIn (e '' t) (e x), ⟨?_, ?_⟩, (?_ : _ ⊆ t).trans inter_subset_left⟩
  · nth_rewrite 1 [← e.left_inv (mem_chart_source _ _)]
    apply e.symm.image_mem_nhds (by simp [e])
    exact pathComponentIn_mem_nhds <| e.image_mem_nhds (mem_chart_source _ _) ht
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
/-
**ChartedSpace.comp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ChartedSpace.comp (H : Type*) [TopologicalSpace H] (H' : Type*) [Topologic
alSpace H'] (M : Type*) [TopologicalSpace M] [ChartedSpace H H'] [ChartedSpace H
' M] : ChartedSpace H M where atlas
参数：H : Type*；H' : Type*；M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is modelled on `H'` and `H'` is itself modelled on `H`, then we can consi
der `M` as being
modelled on `H`.
-/
def ChartedSpace.comp (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H']
    (M : Type*) [TopologicalSpace M] [ChartedSpace H H'] [ChartedSpace H' M] :
    ChartedSpace H M where
  atlas := image2 OpenPartialHomeomorph.trans (atlas H' M) (atlas H H')
  chartAt p := (chartAt H' p).trans (chartAt H (chartAt H' p p))
  mem_chart_source p := by simp only [mfld_simps]
  chart_mem_atlas p := ⟨chartAt _ p, chart_mem_atlas _ p, chartAt _ _, chart_mem_atlas _ _, rfl⟩
/-
**chartAt_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：chartAt_comp (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpa
ce H'] {M : Type*} [TopologicalSpace M] [ChartedSpace H H'] [ChartedSpace H' M] 
(x : M) : (letI
参数：H : Type*；H' : Type*；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem chartAt_comp (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H']
    {M : Type*} [TopologicalSpace M] [ChartedSpace H H'] [ChartedSpace H' M] (x : M) :
    (letI := ChartedSpace.comp H H' M; chartAt H x) = chartAt H' x ≫ₕ chartAt H (chartAt H' x x) :=
  rfl

/-- A charted space over a T1 space is T1. Note that this is *not* true for T2 (for instance for
the real line with a double origin). -/
/-
**ChartedSpace.t1Space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ChartedSpace.t1Space [T1Space H] : T1Space M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `t1Space_iff_exists_open`：t1Space_iff_exists_open : T1Space X ↔ Pairwise 
fun x y => exists U : Set X, IsOpen U ∧ x in U ∧ y ∉ U
· 使用定理 `OpenPartialHomeomorph.isOpen_inter_preimage`：isOpen_inter_preimage {s : 
Set Y} (hs : IsOpen s) : IsOpen (e.source inter e ⁻¹' s)
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.InjOn.ne`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {x
 y : α}, Set.InjOn f s → x ∈ s → y ∈ s → x ≠ y → f x ≠ f y
· 使用定理 `OpenPartialHomeomorph.injOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.InjOn (↑e) …
· 使用定理 `ChartedSpace.mem_chart_source`：∀ {H : Type u_5} {inst : TopologicalSpace
 H} {M : Type u_6} {inst_1 : TopologicalSpace M} [self : ChartedSpace H M]   (x 
: M), x ∈ (ChartedS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…

--- 原说明 ---
A charted space over a T1 space is T1. Note that this is *not* true for T2 (for 
instance for
the real line with a double origin).
-/
theorem ChartedSpace.t1Space [T1Space H] : T1Space M := by
  apply t1Space_iff_exists_open.2 (fun x y hxy ↦ ?_)
  by_cases hy : y ∈ (chartAt H x).source
  · refine ⟨(chartAt H x).source ∩ (chartAt H x)⁻¹' ({chartAt H x y}ᶜ), ?_, ?_, by simp⟩
    · exact OpenPartialHomeomorph.isOpen_inter_preimage _ isOpen_compl_singleton
    · simp only [preimage_compl, mem_inter_iff, mem_chart_source, mem_compl_iff, mem_preimage,
        mem_singleton_iff, true_and]
      exact (chartAt H x).injOn.ne (ChartedSpace.mem_chart_source x) hy hxy
  · exact ⟨(chartAt H x).source, (chartAt H x).open_source, ChartedSpace.mem_chart_source x, hy⟩

/-- A charted space over a discrete space is discrete. -/
/-
**ChartedSpace.discreteTopology** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ChartedSpace.discreteTopology [DiscreteTopology H] : DiscreteTopology M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `discreteTopology_iff_isOpen_singleton`：discreteTopology_iff_isOpen_singl
eton [TopologicalSpace α] : DiscreteTopology α ↔ (forall a : α, IsOpen ({a} : Se
t α))
· 使用定理 `OpenPartialHomeomorph.isOpen_inter_preimage`：isOpen_inter_preimage {s : 
Set Y} (hs : IsOpen s) : IsOpen (e.source inter e ⁻¹' s)
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `OpenPartialHomeomorph.injOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.InjOn (↑e) …
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce

--- 原说明 ---
A charted space over a discrete space is discrete.
-/
theorem ChartedSpace.discreteTopology [DiscreteTopology H] : DiscreteTopology M := by
  apply discreteTopology_iff_isOpen_singleton.2 (fun x ↦ ?_)
  have : IsOpen ((chartAt H x).source ∩ (chartAt H x) ⁻¹' {chartAt H x x}) :=
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
/-
**ChartedSpace.empty** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ChartedSpace.empty (H : Type*) [TopologicalSpace H] (M : Type*) [Topologic
alSpace M] [IsEmpty M] : ChartedSpace H M where atlas
参数：H : Type*；M : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False

--- 原说明 ---
An empty type is a charted space over any topological space.
-/
def ChartedSpace.empty (H : Type*) [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [IsEmpty M] : ChartedSpace H M where
  atlas := ∅
  chartAt x := (IsEmpty.false x).elim
  mem_chart_source x := (IsEmpty.false x).elim
  chart_mem_atlas x := (IsEmpty.false x).elim

/-- Any space is a `ChartedSpace` modelled over itself, by just using the identity chart. -/
/-
**chartedSpaceSelf** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：chartedSpaceSelf (H : Type*) [TopologicalSpace H] : ChartedSpace H H where
 atlas
参数：H : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
Any space is a `ChartedSpace` modelled over itself, by just using the identity c
hart.
-/
instance chartedSpaceSelf (H : Type*) [TopologicalSpace H] : ChartedSpace H H where
  atlas := {OpenPartialHomeomorph.refl H}
  chartAt _ := OpenPartialHomeomorph.refl H
  mem_chart_source x := mem_univ x
  chart_mem_atlas _ := mem_singleton _

/-- In the trivial `ChartedSpace` structure of a space modelled over itself through the identity,
the atlas members are just the identity. -/
@[simp, mfld_simps]
/-
**chartedSpaceSelf_atlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：chartedSpaceSelf_atlas {H : Type*} [TopologicalSpace H] {e : OpenPartialHo
meomorph H H} : e in atlas H H ↔ e = OpenPartialHomeomorph.refl H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
In the trivial `ChartedSpace` structure of a space modelled over itself through 
the identity,
the atlas members are just the identity.
-/
theorem chartedSpaceSelf_atlas {H : Type*} [TopologicalSpace H] {e : OpenPartialHomeomorph H H} :
    e ∈ atlas H H ↔ e = OpenPartialHomeomorph.refl H :=
  Iff.rfl

/-- In the model space, `chartAt` is always the identity. -/
/-
**chartAt_self_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：chartAt_self_eq {H : Type*} [TopologicalSpace H] {x : H} : chartAt H x = O
penPartialHomeomorph.refl H
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the model space, `chartAt` is always the identity.
-/
theorem chartAt_self_eq {H : Type*} [TopologicalSpace H] {x : H} :
    chartAt H x = OpenPartialHomeomorph.refl H := rfl

/-- Any discrete space is a charted space over a singleton set.
We keep this as a definition (not an instance) to avoid instance search trying to search for
`DiscreteTopology` or `Unique` instances.
-/
@[instance_reducible]
/-
**ChartedSpace.ofDiscreteTopology** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ChartedSpace.ofDiscreteTopology [TopologicalSpace M] [TopologicalSpace H] 
[DiscreteTopology M] [h : Unique H] : ChartedSpace H M where atlas
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any discrete space is a charted space over a singleton set.
We keep this as a definition (not an instance) to avoid instance search trying t
o search for
`DiscreteTopology` or `Unique` instances.
-/
def ChartedSpace.ofDiscreteTopology [TopologicalSpace M] [TopologicalSpace H]
    [DiscreteTopology M] [h : Unique H] : ChartedSpace H M where
  atlas :=
    letI f := fun x : M ↦ OpenPartialHomeomorph.const
      (isOpen_discrete {x}) (isOpen_discrete {h.default})
    Set.image f univ
  chartAt x := OpenPartialHomeomorph.const (isOpen_discrete {x}) (isOpen_discrete {h.default})
  mem_chart_source x := by simp
  chart_mem_atlas x := by simp

@[deprecated (since := "2026-07-26")]
alias ChartedSpace.of_discreteTopology := ChartedSpace.ofDiscreteTopology

/-- A chart on the discrete space is the constant chart. -/
@[simp, mfld_simps]
/-
**chartedSpace_of_discreteTopology_chartAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：chartedSpace_of_discreteTopology_chartAt [TopologicalSpace M] [Topological
Space H] [DiscreteTopology M] [h : Unique H] {x : M} : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A chart on the discrete space is the constant chart.
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
/-
**ModelProd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ModelProd (H : Type*) (H' : Type*)
参数：H : Type*；H' : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Same thing as `H × H'`. We introduce it for technical reasons,
see note [Manifold type tags].
-/
def ModelProd (H : Type*) (H' : Type*) :=
  H × H'

/-- Same thing as `∀ i, H i`. We introduce it for technical reasons,
see note [Manifold type tags]. -/
@[implicit_reducible]
/-
**ModelPi** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ModelPi {ι : Type*} (H : ι -> Type*)
参数：H : ι -> Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Same thing as `∀ i, H i`. We introduce it for technical reasons,
see note [Manifold type tags].
-/
def ModelPi {ι : Type*} (H : ι → Type*) :=
  ∀ i, H i

section

/-
**modelProdInhabited** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：modelProdInhabited [Inhabited H] [Inhabited H'] : Inhabited (ModelProd H H
')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance modelProdInhabited [Inhabited H] [Inhabited H'] : Inhabited (ModelProd H H') :=
  inferInstanceAs <| Inhabited (H × H')
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H'] :
    TopologicalSpace (ModelProd H H') :=
  inferInstanceAs <| TopologicalSpace (H × H')

-- Next lemma shows up often when dealing with derivatives, so we register it as simp lemma.
@[simp, mfld_simps]
/-
**modelProd_range_prod_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：modelProd_range_prod_id {H : Type*} {H' : Type*} {α : Type*} (f : H -> α) 
: (range fun p : ModelProd H H' => (f p.1, p.2)) = range f ×ˢ (univ : Set H')
参数：f : H -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prod_range_univ_eq`：prod_range_univ_eq {m₁ : α -> γ} : range m₁ ×ˢ (
univ : Set β) = range fun p : α × β => (m₁ p.1, p.2)
-/
theorem modelProd_range_prod_id {H : Type*} {H' : Type*} {α : Type*} (f : H → α) :
    (range fun p : ModelProd H H' ↦ (f p.1, p.2)) = range f ×ˢ (univ : Set H') := by
  rw [prod_range_univ_eq]
  rfl

end

section

variable {ι : Type*} {Hi : ι → Type*}

/-
**modelPiInhabited** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：modelPiInhabited [forall i, Inhabited (Hi i)] : Inhabited (ModelPi Hi)
参数：Hi i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance modelPiInhabited [∀ i, Inhabited (Hi i)] : Inhabited (ModelPi Hi) :=
  inferInstanceAs <| Inhabited (∀ i, Hi i)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, TopologicalSpace (Hi i)] : TopologicalSpace (ModelPi Hi) :=
  inferInstanceAs <| TopologicalSpace (∀ i, Hi i)

end

/-- The product of two charted spaces is naturally a charted space, with the canonical
construction of the atlas of product maps. -/
/-
**prodChartedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：prodChartedSpace (H : Type*) [TopologicalSpace H] (M : Type*) [Topological
Space M] [ChartedSpace H M] (H' : Type*) [TopologicalSpace H'] (M' : Type*) [Top
ologicalSpace M'] [ChartedSpace H' M'] : ChartedSpace (ModelProd H H') (M × M') 
where atlas
参数：H : Type*；M : Type*；H' : Type*；M' : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two charted spaces is naturally a charted space, with the canonic
al
construction of the atlas of product maps.
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
/-
**ModelProd.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ModelProd.ext {x y : ModelProd H H'} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x
 = y
参数：h₁ : x.1 = y.1；h₂ : x.2 = y.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
theorem ModelProd.ext {x y : ModelProd H H'} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y :=
  Prod.ext h₁ h₂

variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {x : M × M'}

@[simp, mfld_simps]
/-
**prodChartedSpace_chartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prodChartedSpace_chartAt : chartAt (ModelProd H H') x = (chartAt H x.fst).
prod (chartAt H' x.snd)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodChartedSpace_chartAt :
    chartAt (ModelProd H H') x = (chartAt H x.fst).prod (chartAt H' x.snd) :=
  rfl
/-
**chartedSpaceSelf_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：chartedSpaceSelf_prod : prodChartedSpace H H H' H' = chartedSpaceSelf (H ×
 H')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ChartedSpace.ext`：∀ {H : Type u_5} {inst : TopologicalSpace H} {M : Type
 u_6} {inst_1 : TopologicalSpace M} {x y : ChartedSpace H M},   ChartedSpace.atl
as = C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_singleton_right`：image2_singleton_right : image2 f s {b} = (f
un a => f a b) '' s
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `OpenPartialHomeomorph.refl_prod_refl`：refl_prod_refl : (OpenPartialHomeo
morph.refl X).prod (OpenPartialHomeomorph.refl Y) = OpenPartialHomeomorph.refl (
X × Y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem chartedSpaceSelf_prod : prodChartedSpace H H H' H' = chartedSpaceSelf (H × H') := by
  ext1
  · simp [atlas, ChartedSpace.atlas]
  · ext1
    simp only [prodChartedSpace_chartAt, chartAt_self_eq, refl_prod_refl]
    rfl

end prodChartedSpace

/-- The product of a finite family of charted spaces is naturally a charted space, with the
canonical construction of the atlas of finite product maps. -/
/-
**piChartedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：piChartedSpace {ι : Type*} [Finite ι] (H : ι -> Type*) [forall i, Topologi
calSpace (H i)] (M : ι -> Type*) [forall i, TopologicalSpace (M i)] [forall i, C
hartedSpace (H i) (M i)] : ChartedSpace (ModelPi H) (forall i, M i) where atlas
参数：H : ι -> Type*；H i；M : ι -> Type*；M i；H i；M i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of a finite family of charted spaces is naturally a charted space, w
ith the
canonical construction of the atlas of finite product maps.
-/
instance piChartedSpace {ι : Type*} [Finite ι] (H : ι → Type*) [∀ i, TopologicalSpace (H i)]
    (M : ι → Type*) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)] :
    ChartedSpace (ModelPi H) (∀ i, M i) where
  atlas := OpenPartialHomeomorph.pi '' Set.pi univ fun _ ↦ atlas (H _) (M _)
  chartAt f := OpenPartialHomeomorph.pi fun i ↦ chartAt (H i) (f i)
  mem_chart_source f i _ := mem_chart_source (H i) (f i)
  chart_mem_atlas f := mem_image_of_mem _ fun i _ ↦ chart_mem_atlas (H i) (f i)

@[simp, mfld_simps]
/-
**piChartedSpace_chartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：piChartedSpace_chartAt {ι : Type*} [Finite ι] (H : ι -> Type*) [forall i, 
TopologicalSpace (H i)] (M : ι -> Type*) [forall i, TopologicalSpace (M i)] [for
all i, ChartedSpace (H i) (M i)] (f : forall i, M i) : chartAt (H
参数：H : ι -> Type*；H i；M : ι -> Type*；M i；H i；M i；f : forall i, M i。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piChartedSpace_chartAt {ι : Type*} [Finite ι] (H : ι → Type*)
    [∀ i, TopologicalSpace (H i)] (M : ι → Type*) [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace (H i) (M i)] (f : ∀ i, M i) :
    chartAt (H := ModelPi H) f = OpenPartialHomeomorph.pi fun i ↦ chartAt (H i) (f i) :=
  rfl

end Products

section sum

variable [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace M']
    [cm : ChartedSpace H M] [cm' : ChartedSpace H M']

/-- The disjoint union of two charted spaces modelled on a non-empty space `H`
is a charted space over `H`. -/
@[instance_reducible]
/-
**ChartedSpace.sumOfNonempty** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ChartedSpace.sumOfNonempty [Nonempty H] : ChartedSpace H (M oplus M') wher
e atlas
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inl
· 使用定理 `Topology.IsOpenEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inr

--- 原说明 ---
The disjoint union of two charted spaces modelled on a non-empty space `H`
is a charted space over `H`.
-/
def ChartedSpace.sumOfNonempty [Nonempty H] : ChartedSpace H (M ⊕ M') where
  atlas := ((fun e ↦ e.lift_openEmbedding IsOpenEmbedding.inl) '' cm.atlas) ∪
    ((fun e ↦ e.lift_openEmbedding IsOpenEmbedding.inr) '' cm'.atlas)
  -- At `x : M`, the chart is the chart in `M`; at `x' ∈ M'`, it is the chart in `M'`.
  chartAt := Sum.elim (fun x ↦ (cm.chartAt x).lift_openEmbedding IsOpenEmbedding.inl)
    (fun x ↦ (cm'.chartAt x).lift_openEmbedding IsOpenEmbedding.inr)
  mem_chart_source p := by
    cases p with
    | inl x =>
      rw [Sum.elim_inl, lift_openEmbedding_source,
        ← OpenPartialHomeomorph.lift_openEmbedding_source _ IsOpenEmbedding.inl]
      use x, cm.mem_chart_source x
    | inr x =>
      rw [Sum.elim_inr, lift_openEmbedding_source,
        ← OpenPartialHomeomorph.lift_openEmbedding_source _ IsOpenEmbedding.inr]
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
/-
**ChartedSpace.sum** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ChartedSpace.sum : ChartedSpace H (M oplus M')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ChartedSpace.sum : ChartedSpace H (M ⊕ M') := by
  by_cases! h : Nonempty H
  · exact ChartedSpace.sumOfNonempty
  have : IsEmpty M := isEmpty_of_chartedSpace H
  have : IsEmpty M' := isEmpty_of_chartedSpace H
  exact empty H (M ⊕ M')
/-
**ChartedSpace.sum_chartAt_inl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ChartedSpace.sum_chartAt_inl (x : M) : haveI : Nonempty H
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nonempty_of_chartedSpace`：nonempty_of_chartedSpace {H : Type*} {M : Type
*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : Nonemp
ty H
· 使用定理 `Topology.IsOpenEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inl
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
lemma ChartedSpace.sum_chartAt_inl (x : M) :
    haveI : Nonempty H := nonempty_of_chartedSpace x
    chartAt H (Sum.inl x)
      = (chartAt H x).lift_openEmbedding (X' := M ⊕ M') IsOpenEmbedding.inl := by
  simp +instances only [chartAt, sum, nonempty_of_chartedSpace x, ↓reduceDIte]
  rfl
/-
**ChartedSpace.sum_chartAt_inr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ChartedSpace.sum_chartAt_inr (x' : M') : haveI : Nonempty H
参数：x' : M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nonempty_of_chartedSpace`：nonempty_of_chartedSpace {H : Type*} {M : Type
*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : Nonemp
ty H
· 使用定理 `Topology.IsOpenEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inr
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
lemma ChartedSpace.sum_chartAt_inr (x' : M') :
    haveI : Nonempty H := nonempty_of_chartedSpace x'
    chartAt H (Sum.inr x')
      = (chartAt H x').lift_openEmbedding (X' := M ⊕ M') IsOpenEmbedding.inr := by
  simp +instances only [chartAt, sum, nonempty_of_chartedSpace x', ↓reduceDIte]
  rfl
/-
**sum_chartAt_inl_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {H : Type u} {M : Type u_2} {M' : Type u_3} [inst : TopologicalSpace H] 
[inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSpace M'] [cm : ChartedSpac
e H M] [cm' : ChartedSpace H M'] {x y : M},   ↑(chartAt H (Sum.inl x)) (Sum.inl 
y) = ↑(chartAt H x) y
参数：chartAt H (Sum.inl x)；Sum.inl y；chartAt H x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nonempty_of_chartedSpace`：nonempty_of_chartedSpace {H : Type*} {M : Type
*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : Nonemp
ty H
· 使用定理 `Topology.IsOpenEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inl
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ChartedSpace.sum_chartAt_inl`：ChartedSpace.sum_chartAt_inl (x : M) : hav
eI : Nonempty H
· 使用引理 `OpenPartialHomeomorph.lift_openEmbedding_apply`：lift_openEmbedding_apply
 (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) {x : X} : (lift_openEm
bedding e hf) (f x) = e x
-/
@[simp, mfld_simps] lemma sum_chartAt_inl_apply {x y : M} :
    (chartAt H (.inl x : M ⊕ M')) (Sum.inl y) = (chartAt H x) y := by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [ChartedSpace.sum_chartAt_inl]
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _
/-
**sum_chartAt_inr_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {H : Type u} {M : Type u_2} {M' : Type u_3} [inst : TopologicalSpace H] 
[inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSpace M'] [cm : ChartedSpac
e H M] [cm' : ChartedSpace H M'] {x y : M'},   ↑(chartAt H (Sum.inr x)) (Sum.inr
 y) = ↑(chartAt H x) y
参数：chartAt H (Sum.inr x)；Sum.inr y；chartAt H x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nonempty_of_chartedSpace`：nonempty_of_chartedSpace {H : Type*} {M : Type
*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : Nonemp
ty H
· 使用定理 `Topology.IsOpenEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inr
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ChartedSpace.sum_chartAt_inr`：ChartedSpace.sum_chartAt_inr (x' : M') : h
aveI : Nonempty H
· 使用引理 `OpenPartialHomeomorph.lift_openEmbedding_apply`：lift_openEmbedding_apply
 (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) {x : X} : (lift_openEm
bedding e hf) (f x) = e x
-/
@[simp, mfld_simps] lemma sum_chartAt_inr_apply {x y : M'} :
    (chartAt H (.inr x : M ⊕ M')) (Sum.inr y) = (chartAt H x) y := by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [ChartedSpace.sum_chartAt_inr]
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _
/-
**ChartedSpace.mem_atlas_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ChartedSpace.mem_atlas_sum [h : Nonempty H] {e : OpenPartialHomeomorph (M 
oplus M') H} (he : e in atlas H (M oplus M')) : (exists f : OpenPartialHomeomorp
h M H, f in (atlas H M) ∧ e = (f.lift_openEmbedding IsOpenEmbedding.inl)) ∨ (exi
sts f' : OpenPartialHomeomorph M' H, f' in (atlas H M') ∧ e = (f'.lift_openEmbed
ding IsOpenEmbedding.inr))
参数：M oplus M'；he : e in atlas H (M oplus M')。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Topology.IsOpenEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inl
· 使用定理 `Topology.IsOpenEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inr
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ChartedSpace.mem_atlas_sum [h : Nonempty H]
    {e : OpenPartialHomeomorph (M ⊕ M') H} (he : e ∈ atlas H (M ⊕ M')) :
    (∃ f : OpenPartialHomeomorph M H, f ∈ (atlas H M)
      ∧ e = (f.lift_openEmbedding IsOpenEmbedding.inl))
    ∨ (∃ f' : OpenPartialHomeomorph M' H, f' ∈ (atlas H M') ∧
      e = (f'.lift_openEmbedding IsOpenEmbedding.inr)) := by
  simp +instances only [atlas, sum, h, ↓reduceDIte] at he
  obtain (⟨x, hx, hxe⟩ | ⟨x, hx, hxe⟩) := he
  · rw [← hxe]; left; use x
  · rw [← hxe]; right; use x

end sum

section IsLocalHomeomorph

variable [TopologicalSpace M] [TopologicalSpace M'] [TopologicalSpace H] [ChartedSpace H M]

/-- Given a right inverse for a local homeomorphism `f : M → M'`, endow `M'` with a `ChartedSpace`
/-
**by** 是 Mathlib 中的一个结构，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure by pushing forward the `ChartedSpace` structure from `M`. -/
@[instance_reducible]
/-
**IsLocalHomeomorph.chartedSpaceOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocalHomeomorph.chartedSpaceOfRightInverse {f : M -> M'} (hf : IsLocalHo
meomorph f) {g : M' -> M} (hg : Function.RightInverse g f) : ChartedSpace H M' w
here atlas
参数：hf : IsLocalHomeomorph f；hg : Function.RightInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a right inverse for a local homeomorphism `f : M → M'`, endow `M'` with a 
`ChartedSpace`
structure by pushing forward the `ChartedSpace` structure from `M`.
-/
def IsLocalHomeomorph.chartedSpaceOfRightInverse
    {f : M → M'} (hf : IsLocalHomeomorph f) {g : M' → M} (hg : Function.RightInverse g f) :
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
/-
**IsLocalHomeomorph.chartedSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocalHomeomorph.chartedSpace {f : M -> M'} (hf : IsLocalHomeomorph f) (h
f' : Function.Surjective f) : ChartedSpace H M'
参数：hf : IsLocalHomeomorph f；hf' : Function.Surjective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.hasRightInverse`：∀ {α : Sort u} {β : Sort v} {f : α 
→ β}, Function.Surjective f → Function.HasRightInverse f

--- 原说明 ---
Given a surjective local homeomorphism `f : M → M'`, endow `M'` with a `ChartedS
pace` structure
by pushing forward the `ChartedSpace` structure from `M`.
-/
def IsLocalHomeomorph.chartedSpace
    {f : M → M'} (hf : IsLocalHomeomorph f) (hf' : Function.Surjective f) :
    ChartedSpace H M' :=
  hf.chartedSpaceOfRightInverse hf'.hasRightInverse.choose_spec

/-- Given a homeomorphism `f : M ≃ₜ M'`, endow `M'` with a `ChartedSpace` structure by pushing
forward the `ChartedSpace` structure from `M`. -/
@[implicit_reducible]
/-
**Homeomorph.chartedSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Homeomorph.chartedSpace (f : M ≃ₜ M') : ChartedSpace H M'
参数：f : M ≃ₜ M'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isLocalHomeomorph`：Homeomorph.isLocalHomeomorph (f : X ≃ₜ Y) 
: IsLocalHomeomorph f
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h

--- 原说明 ---
Given a homeomorphism `f : M ≃ₜ M'`, endow `M'` with a `ChartedSpace` structure 
by pushing
forward the `ChartedSpace` structure from `M`.
-/
def Homeomorph.chartedSpace (f : M ≃ₜ M') : ChartedSpace H M' :=
  f.isLocalHomeomorph.chartedSpace f.surjective

end IsLocalHomeomorph

end Constructions

end ChartedSpace

/-! ### Constructing a topology from an atlas -/

/-- Sometimes, one may want to construct a charted space structure on a space which does not yet
have a topological structure, where the topology would come from the charts. For this, one needs
charts that are only partial equivalences, and continuity properties for their composition.
This is formalised in `ChartedSpaceCore`. -/
/-
**ChartedSpaceCore** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(H : Type u_5) → [TopologicalSpace H] → Type u_6 → Type (max u_5 u_6)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sometimes, one may want to construct a charted space structure on a space which 
does not yet
have a topological structure, where the topology would come from the charts. For
 this, one needs
charts that are only partial equivalences, and continuity properties for their c
omposition.
This is formalised in `ChartedSpaceCore`.
-/
structure ChartedSpaceCore (H : Type*) [TopologicalSpace H] (M : Type*) where
  /-- An atlas of charts, which are only `PartialEquiv`s -/
  atlas : Set (PartialEquiv M H)
  /-- The preferred chart at each point -/
  chartAt : M → PartialEquiv M H
  mem_chart_source : ∀ x, x ∈ (chartAt x).source
  chart_mem_atlas : ∀ x, chartAt x ∈ atlas
  open_source : ∀ e e' : PartialEquiv M H, e ∈ atlas → e' ∈ atlas → IsOpen (e.symm.trans e').source
  continuousOn_toFun : ∀ e e' : PartialEquiv M H, e ∈ atlas → e' ∈ atlas →
    ContinuousOn (e.symm.trans e') (e.symm.trans e').source

namespace ChartedSpaceCore

variable [TopologicalSpace H] (c : ChartedSpaceCore H M) {e : PartialEquiv M H}

/-- Topology generated by a set of charts on a Type. -/
@[instance_reducible]
/-
**ChartedSpaceCore.toTopologicalSpace** 是 Mathlib 中的一个定义，位于命名空间 `ChartedSpaceCor
e`。
形式化陈述：{H : Type u} → {M : Type u_2} → [inst : TopologicalSpace H] → ChartedSpace
Core H M → TopologicalSpace M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Topology generated by a set of charts on a Type.
-/
protected def toTopologicalSpace : TopologicalSpace M :=
  TopologicalSpace.generateFrom <|
    ⋃ (e : PartialEquiv M H) (_ : e ∈ c.atlas) (s : Set H) (_ : IsOpen s),
      {e ⁻¹' s ∩ e.source}
/-
**ChartedSpaceCore.open_source'** 是 Mathlib 中的一个定理，位于命名空间 `ChartedSpaceCore`。
形式化陈述：open_source' (he : e in c.atlas) : IsOpen[c.toTopologicalSpace] e.source
参数：he : e in c.atlas。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem open_source' (he : e ∈ c.atlas) : IsOpen[c.toTopologicalSpace] e.source := by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [exists_prop, mem_iUnion, mem_singleton_iff]
  refine ⟨e, he, univ, isOpen_univ, ?_⟩
  simp only [Set.univ_inter, Set.preimage_univ]
/-
**ChartedSpaceCore.open_target** 是 Mathlib 中的一个定理，位于命名空间 `ChartedSpaceCore`。
形式化陈述：open_target (he : e in c.atlas) : IsOpen e.target
参数：he : e in c.atlas。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `PartialEquiv.target_subset_preimage_source`：target_subset_preimage_sourc
e : e.target subseteq e.symm ⁻¹' e.source
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ChartedSpaceCore.open_source`：∀ {H : Type u_5} [inst : TopologicalSpace 
H] {M : Type u_6} (self : ChartedSpaceCore H M) (e e' : PartialEquiv M H),   e ∈
 self.atlas → e' ∈…
-/
theorem open_target (he : e ∈ c.atlas) : IsOpen e.target := by
  have E : e.target ∩ e.symm ⁻¹' e.source = e.target :=
    Subset.antisymm inter_subset_left fun x hx ↦
      ⟨hx, PartialEquiv.target_subset_preimage_source _ hx⟩
  simpa [PartialEquiv.trans_source, E] using c.open_source e e he he

/-- An element of the atlas in a charted space without topology becomes an open partial
homeomorphism for the topology constructed from this atlas. The `OpenPartialHomeomorph` version is
given in this definition. -/
/-
**ChartedSpaceCore.openPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `ChartedSpace
Core`。
形式化陈述：{H : Type u} →   {M : Type u_2} →     [inst : TopologicalSpace H] →       
(c : ChartedSpaceCore H M) → (e : PartialEquiv M H) → e ∈ c.atlas → OpenPartialH
omeomorph M H
参数：c : ChartedSpaceCore H M；e : PartialEquiv M H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of the atlas in a charted space without topology becomes an open part
ial
homeomorphism for the topology constructed from this atlas. The `OpenPartialHome
omorph` version is
given in this definition.
-/
protected def openPartialHomeomorph (e : PartialEquiv M H) (he : e ∈ c.atlas) :
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
      have : IsOpen (f ⁻¹' s ∩ f.source) := by
        simpa [f, inter_comm] using (continuousOn_open_iff (c.open_source e e' he e'_atlas)).1
          (c.continuousOn_toFun e e' he e'_atlas) s s_open
      have A : e' ∘ e.symm ⁻¹' s ∩ (e.target ∩ e.symm ⁻¹' e'.source) =
          e.target ∩ (e' ∘ e.symm ⁻¹' s ∩ e.symm ⁻¹' e'.source) := by
        rw [← inter_assoc, ← inter_assoc]
        congr 1
        exact inter_comm _ _
      simpa [f, PartialEquiv.trans_source, preimage_inter, preimage_comp.symm, A] using this }

/-- Given a charted space without topology, endow it with a genuine charted space structure with
respect to the topology constructed from the atlas. -/
@[instance_reducible]
/-
**ChartedSpaceCore.toChartedSpace** 是 Mathlib 中的一个定义，位于命名空间 `ChartedSpaceCore`。
形式化陈述：toChartedSpace : @ChartedSpace H _ M c.toTopologicalSpace
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ChartedSpaceCore.chart_mem_atlas`：∀ {H : Type u_5} [inst : TopologicalSp
ace H] {M : Type u_6} (self : ChartedSpaceCore H M) (x : M),   self.chartAt x ∈ 
self.atlas
· 使用定理 `ChartedSpaceCore.mem_chart_source`：∀ {H : Type u_5} [inst : TopologicalS
pace H] {M : Type u_6} (self : ChartedSpaceCore H M) (x : M),   x ∈ (self.chartA
t x).source

--- 原说明 ---
Given a charted space without topology, endow it with a genuine charted space st
ructure with
respect to the topology constructed from the atlas.
-/
def toChartedSpace : @ChartedSpace H _ M c.toTopologicalSpace :=
  { __ := c.toTopologicalSpace
    atlas := ⋃ (e : PartialEquiv M H) (he : e ∈ c.atlas), {c.openPartialHomeomorph e he}
    chartAt := fun x ↦ c.openPartialHomeomorph (c.chartAt x) (c.chart_mem_atlas x)
    mem_chart_source := fun x ↦ c.mem_chart_source x
    chart_mem_atlas := fun x ↦ by
      simp only [mem_iUnion, mem_singleton_iff]
      exact ⟨c.chartAt x, c.chart_mem_atlas x, rfl⟩}

end ChartedSpaceCore

