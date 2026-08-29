/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.LocalSourceTargetProperty
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Analysis.Normed.Module.Shrink -- shake: keep (NormedAddCommGroup (Shrink ...)), cf. lean#13417
public import Mathlib.Topology.Algebra.Module.TransferInstance

/-! # Smooth immersions

In this file, we define `C^n` immersions between `C^n` manifolds.
The correct definition in the infinite-dimensional setting differs from the standard
finite-dimensional definition (concerning the `mfderiv` being injective): future pull requests will
prove that our definition implies the latter, and that both are equivalent for finite-dimensional
manifolds.

This definition can be conveniently formulated in terms of local properties: `f` is an immersion at
`x` iff there exist suitable charts near `x` and `f x` such that `f` has a nice form w.r.t. these
charts. Most results below can be deduced from more abstract results about such local properties.
This shortens the overall argument, as the definition of submersions has the same general form.

## Main definitions

* `IsImmersionAtOfComplement F I J n f x` means a map `f : M → N` between `C^n` manifolds `M` and
  `N` is an immersion at `x : M`: there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`,
  respectively, such that in these charts, `f` looks like `u ↦ (u, 0)`, w.r.t. some equivalence
  `E' ≃L[𝕜] E × F`. We do not demand that `f` be differentiable (this follows from this definition).
* `IsImmersionAt I J n f x` means that `f` is a `C^n` immersion at `x : M` for some choice of a
  complement `F` of the model normed space `E` of `M` in the model normed space `E'` of `N`.
  In most cases, prefer this definition over `IsImmersionAtOfComplement`.
* `IsImmersionOfComplement F I J n f` means `f : M → N` is an immersion at every point `x : M`,
  w.r.t. the chosen complement `F`.
* `IsImmersion I J n f` means `f : M → N` is an immersion at every point `x : M`,
  w.r.t. some global choice of complement.

## Main results

* `IsImmersionAt.congr_of_eventuallyEq`: being an immersion is a local property.
  If `f` and `g` agree near `x` and `f` is an immersion at `x`, so is `g`
* `IsImmersionAtOfComplement.congr_F`, `IsImmersionOfComplement.congr_F`:
  being an immersion (at `x`) w.r.t. `F` is stable under
  replacing the complement `F` by an isomorphic copy.
* `IsOpen.isImmersionAtOfComplement` and `IsOpen.isImmersionAt`:
  the set of points where `IsImmersionAt(OfComplement)` holds is open.
* `IsImmersionAt.prodMap` and `IsImmersion.prodMap`: the product of two immersions (at a point)
  is an immersion (at the product point).
* `IsImmersion.id`: the identity map is an immersion
* `IsImmersion.of_opens`: the inclusion of an open subset `s → M` of a smooth manifold
  is a smooth immersion
* `ModelWithCorners.isImmersion`: every model with corners is itself an immersion
* `IsImmersionOfComplement.sumInl` and `IsImmersionOfComplement.sumInr`: given `C^n` manifolds
  `M` and `N`, `Sum.inl : M → M ⊕ N` and `Sum.inr : N → M ⊕ N` are `C^n` immersions
* `IsImmersionAt.contMDiffAt`: if f is an immersion at `x`, it is `C^n` at `x`.
* `IsImmersion.contMDiff`: if f is a `C^n` immersion, it is automatically `C^n`
  in the sense of `ContMDiff`.
* `ContMDiffAt.iff_comp_isImmersionAt` and `ContMDiff.iff_comp_isImmersion`: a function `f : M → N`
  is `C^n` (at `x`) if and only if it is continuous (at `x`) and its composition `φ ∘ f` with a
  `C^n` immersion `φ : N → P` (at `f x`) is `C^n`.

## Implementation notes

* In most applications, there is no need to control the choice of complement in the definition of an
  immersion, so `IsImmersion(At)` is perfectly adequate. Such control will be helpful, however,
  when considering the local characterisation of submanifolds: locally, a submanifold is described
  either as the image of an immersion, or the preimage of a submersion --- w.r.t. the same
  complement. Providing a version of the definition that includes complements enables stating this
  equivalence cleanly.
* To avoid a free universe variable in `IsImmersion(At)`, we ask for a complement in the same
  universe as the model normed space for `N`. We provide convenience constructors which do not
  have this restriction to preserve usability.
  This relies on the observation that the equivalence in the definition of immersions allows
  shrinking the universe of the complement: this is implemented in
  `IsImmersion(At)OfComplement.small` and `IsImmersion(At)OfComplement.smallEquiv`.

## TODO
* The converse to `IsImmersionAtOfComplement.congr_F` also holds: any two complements are
  isomorphic, as they are isomorphic to the cokernel of the differential `mfderiv I J f x`.
* If `f` is an immersion at `x`, its differential splits, hence is injective.
* If `f : M → N` is a map between Banach manifolds, `mfderiv I J f x` splitting implies `f` is an
  immersion at `x`. (This requires the inverse function theorem.)
* `IsImmersionAt.comp`: if `f : M → N` and `g: N → N'` are maps between Banach manifolds such that
  `f` is an immersion at `x : M` and `g` is an immersion at `f x`, then `g ∘ f` is an immersion
  at `x`.
* `IsImmersion.comp`: the composition of immersions (between Banach manifolds) is an immersion
* If `f : M → N` is a map between finite-dimensional manifolds, `mfderiv I J f x` being injective
  implies `f` is an immersion at `x`.
* `IsLocalDiffeomorphAt.isImmersionAt` and `IsLocalDiffeomorph.isImmersion`:
  a local diffeomorphism (at `x`) is an immersion (at `x`)
* `Diffeomorph.isImmersion`: in particular, a diffeomorphism is an immersion

## References

* [Juan Margalef-Roig and Enrique Outerelo Dominguez, *Differential topology*][roigdomingues1992]

-/

open scoped Topology ContDiff
open Function Set

public noncomputable section

namespace Manifold

-- We manually name the universe of `E''` as `IsImmersionAt` will use it.
universe u
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E''' : Type*} {E'' : Type u} {F F' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : Nat∞ω}

variable (F I J M N) in
/--
Definition of `ImmersionAtProp` / `ImmersionAtProp` 的定义

English:
definition ImmersionAtProp
  signature: : (M -> N) -> OpenPartialHomeomorph M H -> OpenPartialHomeomorph N G -> Prop
  body: fun f domChart codChart => exists equiv : (E × F) ≃L[𝕜] E'',
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in

中文:
定义 ImmersionAtProp
  签名: : (M -> N) -> OpenPartialHomeomorph M H -> OpenPartialHomeomorph N G -> 命题
  定义体: fun f domChart codChart => exists equiv : (E × F) ≃L[𝕜] E'',
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in

Depends on / 依赖: codChart, codChart.extend, domChart, domChart.extend, extend, target
-/
def ImmersionAtProp : (M -> N) -> OpenPartialHomeomorph M H -> OpenPartialHomeomorph N G -> Prop :=
  fun f domChart codChart => exists equiv : (E × F) ≃L[𝕜] E'',
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in
/--
lemma `isLocalSourceTargetProperty_immersionAtProp` / 引理 `isLocalSourceTargetProperty_immersionAtProp`

English:
lemma isLocalSourceTargetProperty_immersionAtProp
  proof: fun ⟨equiv, hf⟩ => ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg := by
    intro ⟨equiv, hf⟩
    refine ⟨equiv, EqOn.trans (fun x hx => ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x in φ.source := by simp_all
    grind

中文:
引理 isLocalSourceTargetProperty_immersionAtProp
  证明: fun ⟨equiv, hf⟩ => ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg := by
    intro ⟨equiv, hf⟩
    refine ⟨equiv, EqOn.trans (fun x hx => ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x in φ.source := by simp_all
    grind

Depends on / 依赖: hf.mono
-/
lemma isLocalSourceTargetProperty_immersionAtProp :
    IsLocalSourceTargetProperty (ImmersionAtProp F I J M N) where
  mono_source {f φ ψ s} hs := fun ⟨equiv, hf⟩ => ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg := by
    intro ⟨equiv, hf⟩
    refine ⟨equiv, EqOn.trans (fun x hx => ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x in φ.source := by simp_all
    grind

variable (F I J n) in
/--
Definition of `IsImmersionAtOfComplement` / `IsImmersionAtOfComplement` 的定义

English:
definition IsImmersionAtOfComplement
  signature: (f : M -> N) (x : M)
  body: LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp F I J M N)

中文:
定义 IsImmersionAtOfComplement
  签名: (f : M -> N) (x : M)
  定义体: LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp F I J M N)

Depends on / 依赖: ImmersionAtProp, LiftSourceTargetPropertyAt
-/
def IsImmersionAtOfComplement (f : M -> N) (x : M) : Prop :=
  LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp F I J M N)

-- Lift the universe from `E''`, to avoid a free universe parameter.
variable (I J n) in
/--
Definition of `IsImmersionAt` / `IsImmersionAt` 的定义

English:
definition IsImmersionAt
  signature: (f : M -> N) (x : M)
  body: exists (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsImmersionAtOfComplement F I J n f x

中文:
定义 IsImmersionAt
  签名: (f : M -> N) (x : M)
  定义体: exists (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsImmersionAtOfComplement F I J n f x

Depends on / 依赖: IsImmersionAtOfComplement, NormedAddCommGroup, NormedSpace
-/
def IsImmersionAt (f : M -> N) (x : M) : Prop :=
  exists (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsImmersionAtOfComplement F I J n f x

variable {f g : M -> N} {x : M}

namespace IsImmersionAtOfComplement

/--
lemma `mk_of_charts` / 引理 `mk_of_charts`

English:
lemma mk_of_charts
  statement: (equiv : (E × F) ≃L[𝕜] E'') (domChart : OpenPartialHomeomorph M H)
  proof: by
  use domChart, codChart
  use equiv

中文:
引理 mk_of_charts
  结论: (equiv : (E × F) ≃L[𝕜] E'') (domChart : OpenPartialHomeomorph M H)
  证明: by
  use domChart, codChart
  use equiv

Depends on / 依赖: codChart, domChart
-/
lemma mk_of_charts (equiv : (E × F) ≃L[𝕜] E'') (domChart : OpenPartialHomeomorph M H)
    (codChart : OpenPartialHomeomorph N G)
    (hx : x in domChart.source) (hfx : f x in codChart.source)
    (hdomChart : domChart in IsManifold.maximalAtlas I n M)
    (hcodChart : codChart in IsManifold.maximalAtlas J n N)
    (hsource : domChart.source subseteq f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAtOfComplement F I J n f x := by
  use domChart, codChart
  use equiv

/--
lemma `mk_of_continuousAt` / 引理 `mk_of_continuousAt`

English:
lemma mk_of_continuousAt
  statement: {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
  proof: LiftSourceTargetPropertyAt.mk_of_continuousAt hf isLocalSourceTargetProperty_immersionAtProp
    _ _ hx hfx hdomChart hcodChart ⟨equiv, hwrittenInExtend⟩

中文:
引理 mk_of_continuousAt
  结论: {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
  证明: LiftSourceTargetPropertyAt.mk_of_continuousAt hf isLocalSourceTargetProperty_immersionAtProp
    _ _ hx hfx hdomChart hcodChart ⟨equiv, hwrittenInExtend⟩

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.mk_of_continuousAt, hcodChart, hdomChart, hwrittenInExtend, isLocalSourceTargetProperty_immersionAtProp, mk_of_continuousAt
-/
lemma mk_of_continuousAt {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x in domChart.source) (hfx : f x in codChart.source)
    (hdomChart : domChart in IsManifold.maximalAtlas I n M)
    (hcodChart : codChart in IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAtOfComplement F I J n f x :=
  LiftSourceTargetPropertyAt.mk_of_continuousAt hf isLocalSourceTargetProperty_immersionAtProp
    _ _ hx hfx hdomChart hcodChart ⟨equiv, hwrittenInExtend⟩

/--
Definition of `domChart` / `domChart` 的定义

English:
definition domChart
  signature: (h : IsImmersionAtOfComplement F I J n f x)
  body: LiftSourceTargetPropertyAt.domChart h

中文:
定义 domChart
  签名: (h : IsImmersionAtOfComplement F I J n f x)
  定义体: LiftSourceTargetPropertyAt.domChart h

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.domChart, domChart
-/
def domChart (h : IsImmersionAtOfComplement F I J n f x) : OpenPartialHomeomorph M H :=
  LiftSourceTargetPropertyAt.domChart h

/--
Definition of `codChart` / `codChart` 的定义

English:
definition codChart
  signature: (h : IsImmersionAtOfComplement F I J n f x)
  body: LiftSourceTargetPropertyAt.codChart h

中文:
定义 codChart
  签名: (h : IsImmersionAtOfComplement F I J n f x)
  定义体: LiftSourceTargetPropertyAt.codChart h

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.codChart, codChart
-/
def codChart (h : IsImmersionAtOfComplement F I J n f x) : OpenPartialHomeomorph N G :=
  LiftSourceTargetPropertyAt.codChart h

/--
lemma `mem_domChart_source` / 引理 `mem_domChart_source`

English:
lemma mem_domChart_source
  given: (h : IsImmersionAtOfComplement F I J n f x)
  statement: x in h.domChart.source
  proof: LiftSourceTargetPropertyAt.mem_domChart_source h

中文:
引理 mem_domChart_source
  条件: (h : IsImmersionAtOfComplement F I J n f x)
  结论: x in h.domChart.source
  证明: LiftSourceTargetPropertyAt.mem_domChart_source h

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.mem_domChart_source, mem_domChart_source
-/
lemma mem_domChart_source (h : IsImmersionAtOfComplement F I J n f x) : x in h.domChart.source :=
  LiftSourceTargetPropertyAt.mem_domChart_source h

/--
lemma `mem_codChart_source` / 引理 `mem_codChart_source`

English:
lemma mem_codChart_source
  given: (h : IsImmersionAtOfComplement F I J n f x)
  statement: f x in h.codChart.source
  proof: LiftSourceTargetPropertyAt.mem_codChart_source h

中文:
引理 mem_codChart_source
  条件: (h : IsImmersionAtOfComplement F I J n f x)
  结论: f x in h.codChart.source
  证明: LiftSourceTargetPropertyAt.mem_codChart_source h

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.mem_codChart_source, mem_codChart_source
-/
lemma mem_codChart_source (h : IsImmersionAtOfComplement F I J n f x) : f x in h.codChart.source :=
  LiftSourceTargetPropertyAt.mem_codChart_source h

/--
lemma `domChart_mem_maximalAtlas` / 引理 `domChart_mem_maximalAtlas`

English:
lemma domChart_mem_maximalAtlas
  given: (h : IsImmersionAtOfComplement F I J n f x)
  proof: LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas h

中文:
引理 domChart_mem_maximalAtlas
  条件: (h : IsImmersionAtOfComplement F I J n f x)
  证明: LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas h

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas, domChart_mem_maximalAtlas
-/
lemma domChart_mem_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) :
    h.domChart in IsManifold.maximalAtlas I n M :=
  LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas h

/--
lemma `codChart_mem_maximalAtlas` / 引理 `codChart_mem_maximalAtlas`

English:
lemma codChart_mem_maximalAtlas
  given: (h : IsImmersionAtOfComplement F I J n f x)
  proof: LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas h

中文:
引理 codChart_mem_maximalAtlas
  条件: (h : IsImmersionAtOfComplement F I J n f x)
  证明: LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas h

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas, codChart_mem_maximalAtlas
-/
lemma codChart_mem_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) :
    h.codChart in IsManifold.maximalAtlas J n N :=
  LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas h

/--
lemma `source_subset_preimage_source` / 引理 `source_subset_preimage_source`

English:
lemma source_subset_preimage_source
  given: (h : IsImmersionAtOfComplement F I J n f x)
  proof: LiftSourceTargetPropertyAt.source_subset_preimage_source h

中文:
引理 source_subset_preimage_source
  条件: (h : IsImmersionAtOfComplement F I J n f x)
  证明: LiftSourceTargetPropertyAt.source_subset_preimage_source h

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.source_subset_preimage_source, source_subset_preimage_source
-/
lemma source_subset_preimage_source (h : IsImmersionAtOfComplement F I J n f x) :
    h.domChart.source subseteq f ⁻¹' h.codChart.source :=
  LiftSourceTargetPropertyAt.source_subset_preimage_source h

/--
lemma `mapsto_domChart_source_codChart_source` / 引理 `mapsto_domChart_source_codChart_source`

English:
lemma mapsto_domChart_source_codChart_source
  given: (h : IsImmersionAtOfComplement F I J n f x)
  proof: h.source_subset_preimage_source

中文:
引理 mapsto_domChart_source_codChart_source
  条件: (h : IsImmersionAtOfComplement F I J n f x)
  证明: h.source_subset_preimage_source

Depends on / 依赖: h.source_subset_preimage_source, source_subset_preimage_source
-/
lemma mapsto_domChart_source_codChart_source (h : IsImmersionAtOfComplement F I J n f x) :
    MapsTo f h.domChart.source h.codChart.source :=
  h.source_subset_preimage_source

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: (h : IsImmersionAtOfComplement F I J n f x)
  body: Classical.choose LiftSourceTargetPropertyAt.property h

中文:
定义 equiv
  签名: (h : IsImmersionAtOfComplement F I J n f x)
  定义体: Classical.choose LiftSourceTargetPropertyAt.property h

Depends on / 依赖: Classical, Classical.choose, LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.property, property
-/
def equiv (h : IsImmersionAtOfComplement F I J n f x) : (E × F) ≃L[𝕜] E'' :=
Classical.choose LiftSourceTargetPropertyAt.property h

/--
lemma `writtenInCharts` / 引理 `writtenInCharts`

English:
lemma writtenInCharts
  given: (h : IsImmersionAtOfComplement F I J n f x)
  proof: Classical.choose_spec LiftSourceTargetPropertyAt.property h

中文:
引理 writtenInCharts
  条件: (h : IsImmersionAtOfComplement F I J n f x)
  证明: Classical.choose_spec LiftSourceTargetPropertyAt.property h

Depends on / 依赖: Classical, Classical.choose_spec, LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.property, choose_spec, property
-/
lemma writtenInCharts (h : IsImmersionAtOfComplement F I J n f x) :
    EqOn ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (h.equiv ∘ (·, 0))
      (h.domChart.extend I).target :=
Classical.choose_spec LiftSourceTargetPropertyAt.property h

/--
lemma `property` / 引理 `property`

English:
lemma property
  given: (h : IsImmersionAtOfComplement F I J n f x)
  proof: h

中文:
引理 property
  条件: (h : IsImmersionAtOfComplement F I J n f x)
  证明: h
-/
lemma property (h : IsImmersionAtOfComplement F I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp F I J M N) := h

/--
lemma `map_target_subset_target` / 引理 `map_target_subset_target`

English:
lemma map_target_subset_target
  given: (h : IsImmersionAtOfComplement F I J n f x)
  proof: by
  rw [← h.writtenInCharts.image_eq]; rw [Set.image_comp]; rw [Set.image_comp]; rw [PartialEquiv.symm_image_target_eq_source]; rw [OpenPartialHomeomorph.extend_source]; rw [← PartialEquiv.image_source_eq_target]
  have : f '' h.domChart.source subseteq h.codChart.source := by
    simp [h.source_subset_preimage_source]
  grw [this, OpenPartialHomeomorph.extend_source]

中文:
引理 map_target_subset_target
  条件: (h : IsImmersionAtOfComplement F I J n f x)
  证明: by
  rw [← h.writtenInCharts.image_eq]; rw [Set.image_comp]; rw [Set.image_comp]; rw [PartialEquiv.symm_image_target_eq_source]; rw [OpenPartialHomeomorph.extend_source]; rw [← PartialEquiv.image_source_eq_target]
  have : f '' h.domChart.source subseteq h.codChart.source := by
    simp [h.source_subset_preimage_source]
  grw [this, OpenPartialHomeomorph.extend_source]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.extend_source, PartialEquiv, PartialEquiv.image_source_eq_target, PartialEquiv.symm_image_target_eq_source, Set.image_comp, codChart, domChart, extend_source, h.codChart.source, h.domChart.source, h.source_subset_preimage_source, h.writtenInCharts.image_eq, image_comp, image_eq, image_source_eq_target, source, source_subset_preimage_source, subseteq, symm_image_target_eq_source
-/
lemma map_target_subset_target (h : IsImmersionAtOfComplement F I J n f x) :
    (h.equiv ∘ (·, 0)) '' (h.domChart.extend I).target subseteq (h.codChart.extend J).target := by
  rw [← h.writtenInCharts.image_eq]; rw [Set.image_comp]; rw [Set.image_comp]; rw [PartialEquiv.symm_image_target_eq_source]; rw [OpenPartialHomeomorph.extend_source]; rw [← PartialEquiv.image_source_eq_target]
  have : f '' h.domChart.source subseteq h.codChart.source := by
    simp [h.source_subset_preimage_source]
  grw [this, OpenPartialHomeomorph.extend_source]

/--
lemma `target_subset_preimage_target` / 引理 `target_subset_preimage_target`

English:
lemma target_subset_preimage_target
  given: (h : IsImmersionAtOfComplement F I J n f x)
  proof: fun _x hx => h.map_target_subset_target (mem_image_of_mem _ hx)

中文:
引理 target_subset_preimage_target
  条件: (h : IsImmersionAtOfComplement F I J n f x)
  证明: fun _x hx => h.map_target_subset_target (mem_image_of_mem _ hx)

Depends on / 依赖: h.map_target_subset_target, map_target_subset_target, mem_image_of_mem
-/
lemma target_subset_preimage_target (h : IsImmersionAtOfComplement F I J n f x) :
    (h.domChart.extend I).target subseteq (h.equiv ∘ (·, 0)) ⁻¹' (h.codChart.extend J).target :=
  fun _x hx => h.map_target_subset_target (mem_image_of_mem _ hx)

/--
lemma `congr_of_eventuallyEq` / 引理 `congr_of_eventuallyEq`

English:
lemma congr_of_eventuallyEq
  given: (hf : IsImmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g)
  proof: LiftSourceTargetPropertyAt.congr_of_eventuallyEq
    isLocalSourceTargetProperty_immersionAtProp hf.property hfg

中文:
引理 congr_of_eventuallyEq
  条件: (hf : IsImmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g)
  证明: LiftSourceTargetPropertyAt.congr_of_eventuallyEq
    isLocalSourceTargetProperty_immersionAtProp hf.property hfg

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.congr_of_eventuallyEq, congr_of_eventuallyEq, hf.property, isLocalSourceTargetProperty_immersionAtProp, property
-/
lemma congr_of_eventuallyEq (hf : IsImmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAtOfComplement F I J n g x :=
  LiftSourceTargetPropertyAt.congr_of_eventuallyEq
    isLocalSourceTargetProperty_immersionAtProp hf.property hfg

/--
lemma `congr_iff_of_eventuallyEq` / 引理 `congr_iff_of_eventuallyEq`

English:
lemma congr_iff_of_eventuallyEq
  given: (hfg : f =ᶠ[𝓝 x] g)
  proof: LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq
      isLocalSourceTargetProperty_immersionAtProp hfg

中文:
引理 congr_iff_of_eventuallyEq
  条件: (hfg : f =ᶠ[𝓝 x] g)
  证明: LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq
      isLocalSourceTargetProperty_immersionAtProp hfg

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq, congr_iff_of_eventuallyEq, isLocalSourceTargetProperty_immersionAtProp
-/
lemma congr_iff_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAtOfComplement F I J n f x ↔ IsImmersionAtOfComplement F I J n g x :=
  LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq
      isLocalSourceTargetProperty_immersionAtProp hfg

/--
lemma `small` / 引理 `small`

English:
lemma small
  given: (hf : IsImmersionAtOfComplement F I J n f x)
  statement: Small.{u} F
  proof: small_of_injective hf.equiv.injective.comp (Prod.mk_right_injective 0)

中文:
引理 small
  条件: (hf : IsImmersionAtOfComplement F I J n f x)
  结论: Small.{u} F
  证明: small_of_injective hf.equiv.injective.comp (Prod.mk_right_injective 0)

Depends on / 依赖: Prod.mk_right_injective, hf.equiv.injective.comp, injective, mk_right_injective, small_of_injective
-/
lemma small (hf : IsImmersionAtOfComplement F I J n f x) : Small.{u} F :=
small_of_injective hf.equiv.injective.comp (Prod.mk_right_injective 0)

/--
Definition of `smallComplement` / `smallComplement` 的定义

English:
definition smallComplement
  signature: (hf : IsImmersionAtOfComplement F I J n f x)
  body: haveI := hf.small
  Shrink.{u} F

中文:
定义 smallComplement
  签名: (hf : IsImmersionAtOfComplement F I J n f x)
  定义体: haveI := hf.small
  Shrink.{u} F

Depends on / 依赖: Shrink, hf.small
-/
def smallComplement (hf : IsImmersionAtOfComplement F I J n f x) : Type u :=
  haveI := hf.small
  Shrink.{u} F

instance (hf : IsImmersionAtOfComplement F I J n f x) : NormedAddCommGroup hf.smallComplement :=
  haveI := hf.small
inferInstanceAs NormedAddCommGroup (Shrink F)

instance (hf : IsImmersionAtOfComplement F I J n f x) : NormedSpace 𝕜 hf.smallComplement :=
  haveI := hf.small
inferInstanceAs NormedSpace 𝕜 (Shrink F)

/--
Definition of `smallEquiv` / `smallEquiv` 的定义

English:
definition smallEquiv
  signature: (hf : IsImmersionAtOfComplement F I J n f x)
  body: haveI := hf.small
  ((equivShrink F).symm.continuousLinearEquiv 𝕜).symm

中文:
定义 smallEquiv
  签名: (hf : IsImmersionAtOfComplement F I J n f x)
  定义体: haveI := hf.small
  ((equivShrink F).symm.continuousLinearEquiv 𝕜).symm

Depends on / 依赖: continuousLinearEquiv, equivShrink, hf.small, symm.continuousLinearEquiv
-/
def smallEquiv (hf : IsImmersionAtOfComplement F I J n f x) : F ≃L[𝕜] hf.smallComplement :=
  haveI := hf.small
  ((equivShrink F).symm.continuousLinearEquiv 𝕜).symm

/--
lemma `trans_F` / 引理 `trans_F`

English:
lemma trans_F
  given: (h : IsImmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F')
  proof: by
  refine ⟨h.domChart, h.codChart, h.mem_domChart_source, h.mem_codChart_source,
    h.domChart_mem_maximalAtlas, h.codChart_mem_maximalAtlas, h.source_subset_preimage_source, ?_⟩
  use ((ContinuousLinearEquiv.refl 𝕜 E).prodCongr e.symm).trans h.equiv
  apply Set.EqOn.trans h.writtenInCharts
  intro x hx
  simp

中文:
引理 trans_F
  条件: (h : IsImmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F')
  证明: by
  refine ⟨h.domChart, h.codChart, h.mem_domChart_source, h.mem_codChart_source,
    h.domChart_mem_maximalAtlas, h.codChart_mem_maximalAtlas, h.source_subset_preimage_source, ?_⟩
  use ((ContinuousLinearEquiv.refl 𝕜 E).prodCongr e.symm).trans h.equiv
  apply Set.EqOn.trans h.writtenInCharts
  intro x hx
  simp

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.refl, Set.EqOn.trans, codChart, codChart_mem_maximalAtlas, domChart, domChart_mem_maximalAtlas, e.symm, h.codChart, h.codChart_mem_maximalAtlas, h.domChart, h.domChart_mem_maximalAtlas, h.equiv, h.mem_codChart_source, h.mem_domChart_source, h.source_subset_preimage_source, h.writtenInCharts, mem_codChart_source, mem_domChart_source, prodCongr
-/
lemma trans_F (h : IsImmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F') :
    IsImmersionAtOfComplement F' I J n f x := by
  refine ⟨h.domChart, h.codChart, h.mem_domChart_source, h.mem_codChart_source,
    h.domChart_mem_maximalAtlas, h.codChart_mem_maximalAtlas, h.source_subset_preimage_source, ?_⟩
  use ((ContinuousLinearEquiv.refl 𝕜 E).prodCongr e.symm).trans h.equiv
  apply Set.EqOn.trans h.writtenInCharts
  intro x hx
  simp

/--
lemma `congr_F` / 引理 `congr_F`

English:
lemma congr_F
  given: (e : F ≃L[𝕜] F')
  proof: ⟨fun h => trans_F (e := e) h, fun h => trans_F (e := e.symm) h⟩

中文:
引理 congr_F
  条件: (e : F ≃L[𝕜] F')
  证明: ⟨fun h => trans_F (e := e) h, fun h => trans_F (e := e.symm) h⟩

Depends on / 依赖: e.symm, trans_F
-/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsImmersionAtOfComplement F I J n f x ↔ IsImmersionAtOfComplement F' I J n f x :=
  ⟨fun h => trans_F (e := e) h, fun h => trans_F (e := e.symm) h⟩

/--
lemma `_root_.IsOpen.isImmersionAtOfComplement` / 引理 `_root_.IsOpen.isImmersionAtOfComplement`

English:
lemma _root_.IsOpen.isImmersionAtOfComplement
  proof: IsOpen.liftSourceTargetPropertyAt

中文:
引理 _root_.是开集.isImmersionAtOfComplement
  证明: IsOpen.liftSourceTargetPropertyAt

Depends on / 依赖: IsOpen, IsOpen.liftSourceTargetPropertyAt, liftSourceTargetPropertyAt
-/
lemma _root_.IsOpen.isImmersionAtOfComplement :
    IsOpen {x | IsImmersionAtOfComplement F I J n f x} :=
  IsOpen.liftSourceTargetPropertyAt

/--
theorem `prodMap` / 定理 `prodMap`

English:
theorem prodMap
  statement: {f : M -> N} {g : M' -> N'} {x' : M'}
  proof: by
  apply LiftSourceTargetPropertyAt.prodMap hf.property hg.property
  rintro f φ₁ ψ₁ g φ₂ ψ₂ ⟨equiv₁, hfprop⟩ ⟨equiv₂, hgprop⟩
  use (ContinuousLinearEquiv.prodProdProdComm 𝕜 E E' F F').trans (equiv₁.prodCongr equiv₂)
  rw [φ₁.extend_prod φ₂]; rw [ψ₁.extend_prod]; rw [PartialEquiv.prod_target]; rw [eqOn_prod_iff]
  exact ⟨fun x ⟨hx, hx'⟩ => by simpa using hfprop hx, fun x ⟨hx, hx'⟩ => by simpa using hgprop hx'⟩

中文:
定理 prodMap
  结论: {f : M -> N} {g : M' -> N'} {x' : M'}
  证明: by
  apply LiftSourceTargetPropertyAt.prodMap hf.property hg.property
  rintro f φ₁ ψ₁ g φ₂ ψ₂ ⟨equiv₁, hfprop⟩ ⟨equiv₂, hgprop⟩
  use (ContinuousLinearEquiv.prodProdProdComm 𝕜 E E' F F').trans (equiv₁.prodCongr equiv₂)
  rw [φ₁.extend_prod φ₂]; rw [ψ₁.extend_prod]; rw [PartialEquiv.prod_target]; rw [eqOn_prod_iff]
  exact ⟨fun x ⟨hx, hx'⟩ => by simpa using hfprop hx, fun x ⟨hx, hx'⟩ => by simpa using hgprop hx'⟩

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.prodProdProdComm, LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.prodMap, PartialEquiv, PartialEquiv.prod_target, eqOn_prod_iff, extend_prod, hf.property, hfprop, hg.property, hgprop, prodCongr, prodMap, prodProdProdComm, prod_target, property
-/
theorem prodMap {f : M -> N} {g : M' -> N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsImmersionAtOfComplement F I J n f x) (hg : IsImmersionAtOfComplement F' I' J' n g x') :
    IsImmersionAtOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) (x, x') := by
  apply LiftSourceTargetPropertyAt.prodMap hf.property hg.property
  rintro f φ₁ ψ₁ g φ₂ ψ₂ ⟨equiv₁, hfprop⟩ ⟨equiv₂, hgprop⟩
  use (ContinuousLinearEquiv.prodProdProdComm 𝕜 E E' F F').trans (equiv₁.prodCongr equiv₂)
  rw [φ₁.extend_prod φ₂]; rw [ψ₁.extend_prod]; rw [PartialEquiv.prod_target]; rw [eqOn_prod_iff]
  exact ⟨fun x ⟨hx, hx'⟩ => by simpa using hfprop hx, fun x ⟨hx, hx'⟩ => by simpa using hgprop hx'⟩

/--
lemma `isImmersionAt` / 引理 `isImmersionAt`

English:
lemma isImmersionAt
  given: (h : IsImmersionAtOfComplement F I J n f x)
  proof: by
  use h.smallComplement, by infer_instance, by infer_instance
  exact (IsImmersionAtOfComplement.congr_F h.smallEquiv).mp h

中文:
引理 isImmersionAt
  条件: (h : IsImmersionAtOfComplement F I J n f x)
  证明: by
  use h.smallComplement, by infer_instance, by infer_instance
  exact (IsImmersionAtOfComplement.congr_F h.smallEquiv).mp h

Depends on / 依赖: IsImmersionAtOfComplement, IsImmersionAtOfComplement.congr_F, congr_F, h.smallComplement, h.smallEquiv, infer_instance, smallComplement, smallEquiv
-/
lemma isImmersionAt (h : IsImmersionAtOfComplement F I J n f x) :
    IsImmersionAt I J n f x := by
  use h.smallComplement, by infer_instance, by infer_instance
  exact (IsImmersionAtOfComplement.congr_F h.smallEquiv).mp h

open IsManifold in
/--
lemma `of_opens` / 引理 `of_opens`

English:
lemma of_opens
  given: [IsManifold I n M] (s : TopologicalSpace.Opens M) (y : s)
  proof: by
  apply IsImmersionAtOfComplement.mk_of_continuousAt (by fun_prop) (.prodUnique 𝕜 E _)
    (chartAt H y) (chartAt H y.val) (mem_chart_source H y) (mem_chart_source H y.val)
    (chart_mem_maximalAtlas y) (chart_mem_maximalAtlas y.val)
  intro x hx
  suffices I ((chartAt H ↑y) ((chartAt H y).symm (I.symm x))) = x by simpa +contextual
  simp_all

中文:
引理 of_opens
  条件: [是流形 I n M] (s : 拓扑空间.Opens M) (y : s)
  证明: by
  apply IsImmersionAtOfComplement.mk_of_continuousAt (by fun_prop) (.prodUnique 𝕜 E _)
    (chartAt H y) (chartAt H y.val) (mem_chart_source H y) (mem_chart_source H y.val)
    (chart_mem_maximalAtlas y) (chart_mem_maximalAtlas y.val)
  intro x hx
  suffices I ((chartAt H ↑y) ((chartAt H y).symm (I.symm x))) = x by simpa +contextual
  simp_all

Depends on / 依赖: I.symm, IsImmersionAtOfComplement, IsImmersionAtOfComplement.mk_of_continuousAt, chartAt, chart_mem_maximalAtlas, contextual, fun_prop, mem_chart_source, mk_of_continuousAt, prodUnique, y.val
-/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) (y : s) :
    IsImmersionAtOfComplement PUnit I I n (Subtype.val : s -> M) y := by
  apply IsImmersionAtOfComplement.mk_of_continuousAt (by fun_prop) (.prodUnique 𝕜 E _)
    (chartAt H y) (chartAt H y.val) (mem_chart_source H y) (mem_chart_source H y.val)
    (chart_mem_maximalAtlas y) (chart_mem_maximalAtlas y.val)
  intro x hx
  suffices I ((chartAt H ↑y) ((chartAt H y).symm (I.symm x))) = x by simpa +contextual
  simp_all

/--
lemma `_root_.ModelWithCorners.isImmersionAtOfComplement` / 引理 `_root_.ModelWithCorners.isImmersionAtOfComplement`

English:
lemma _root_.ModelWithCorners.isImmersionAtOfComplement
  given: {n : Nat} {x : H}
  proof: Manifold.IsImmersionAtOfComplement.mk_of_continuousAt I.continuousAt
    (.prodUnique _ _ _) (.refl _) (.refl _) (by simp) (by simp)
    (IsManifold.subset_maximalAtlas (by simp)) (IsManifold.subset_maximalAtlas (by simp))
    (by simp [Function.comp_def])

中文:
引理 _root_.带角模型.isImmersionAtOfComplement
  条件: {n : 自然数} {x : H}
  证明: Manifold.IsImmersionAtOfComplement.mk_of_continuousAt I.continuousAt
    (.prodUnique _ _ _) (.refl _) (.refl _) (by simp) (by simp)
    (IsManifold.subset_maximalAtlas (by simp)) (IsManifold.subset_maximalAtlas (by simp))
    (by simp [Function.comp_def])
-/
protected lemma _root_.ModelWithCorners.isImmersionAtOfComplement {n : Nat} {x : H} :
    IsImmersionAtOfComplement PUnit I 𝓘(𝕜, E) n I x :=
  Manifold.IsImmersionAtOfComplement.mk_of_continuousAt I.continuousAt
    (.prodUnique _ _ _) (.refl _) (.refl _) (by simp) (by simp)
    (IsManifold.subset_maximalAtlas (by simp)) (IsManifold.subset_maximalAtlas (by simp))
    (by simp [Function.comp_def])

/--
theorem `continuousOn` / 定理 `continuousOn`

English:
theorem continuousOn
  given: (h : IsImmersionAtOfComplement F I J n f x)
  proof: by
  rw [← h.domChart.continuousOn_writtenInExtend_iff le_rfl
      h.mapsto_domChart_source_codChart_source (I' := J) (I := I)]; rw [← h.domChart.extend_target_eq_image_source]
  have : ContinuousOn (h.equiv ∘ fun x => (x, 0)) (h.domChart.extend I).target := by fun_prop
  exact this.congr h.writtenInCharts

中文:
定理 continuousOn
  条件: (h : IsImmersionAtOfComplement F I J n f x)
  证明: by
  rw [← h.domChart.continuousOn_writtenInExtend_iff le_rfl
      h.mapsto_domChart_source_codChart_source (I' := J) (I := I)]; rw [← h.domChart.extend_target_eq_image_source]
  have : ContinuousOn (h.equiv ∘ fun x => (x, 0)) (h.domChart.extend I).target := by fun_prop
  exact this.congr h.writtenInCharts

Depends on / 依赖: ContinuousOn, continuousOn_writtenInExtend_iff, domChart, extend, extend_target_eq_image_source, fun_prop, h.domChart.continuousOn_writtenInExtend_iff, h.domChart.extend, h.domChart.extend_target_eq_image_source, h.equiv, h.mapsto_domChart_source_codChart_source, h.writtenInCharts, le_rfl, mapsto_domChart_source_codChart_source, target, this.congr, writtenInCharts
-/
theorem continuousOn (h : IsImmersionAtOfComplement F I J n f x) :
    ContinuousOn f h.domChart.source := by
  rw [← h.domChart.continuousOn_writtenInExtend_iff le_rfl
      h.mapsto_domChart_source_codChart_source (I' := J) (I := I)]; rw [← h.domChart.extend_target_eq_image_source]
  have : ContinuousOn (h.equiv ∘ fun x => (x, 0)) (h.domChart.extend I).target := by fun_prop
  exact this.congr h.writtenInCharts

/--
theorem `continuousAt` / 定理 `continuousAt`

English:
theorem continuousAt
  given: (h : IsImmersionAtOfComplement F I J n f x)
  statement: ContinuousAt f x
  proof: h.continuousOn.continuousAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

中文:
定理 continuousAt
  条件: (h : IsImmersionAtOfComplement F I J n f x)
  结论: ContinuousAt f x
  证明: h.continuousOn.continuousAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

Depends on / 依赖: continuousAt, continuousOn, domChart, h.continuousOn.continuousAt, h.domChart.open_source.mem_nhds, mem_domChart_source, mem_nhds, open_source
-/
theorem continuousAt (h : IsImmersionAtOfComplement F I J n f x) : ContinuousAt f x :=
  h.continuousOn.continuousAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

/--
theorem `contMDiffOn` / 定理 `contMDiffOn`

English:
theorem contMDiffOn
  given: (h : IsImmersionAtOfComplement F I J n f x)
  proof: by
  rw [← h.domChart.contMDiffOn_writtenInExtend_iff h.domChart_mem_maximalAtlas
    h.codChart_mem_maximalAtlas le_rfl h.mapsto_domChart_source_codChart_source]; rw [← h.domChart.extend_target_eq_image_source]
  have : CMDiff n (h.equiv ∘ fun x => (x, 0)) := by
    rw [contMDiff_iff_contDiff]; fun_prop
  exact this.contMDiffOn.congr h.writtenInCharts

中文:
定理 contMDiffOn
  条件: (h : IsImmersionAtOfComplement F I J n f x)
  证明: by
  rw [← h.domChart.contMDiffOn_writtenInExtend_iff h.domChart_mem_maximalAtlas
    h.codChart_mem_maximalAtlas le_rfl h.mapsto_domChart_source_codChart_source]; rw [← h.domChart.extend_target_eq_image_source]
  have : CMDiff n (h.equiv ∘ fun x => (x, 0)) := by
    rw [contMDiff_iff_contDiff]; fun_prop
  exact this.contMDiffOn.congr h.writtenInCharts

Depends on / 依赖: CMDiff, codChart_mem_maximalAtlas, contMDiffOn, contMDiffOn_writtenInExtend_iff, contMDiff_iff_contDiff, domChart, domChart_mem_maximalAtlas, extend_target_eq_image_source, fun_prop, h.codChart_mem_maximalAtlas, h.domChart.contMDiffOn_writtenInExtend_iff, h.domChart.extend_target_eq_image_source, h.domChart_mem_maximalAtlas, h.equiv, h.mapsto_domChart_source_codChart_source, h.writtenInCharts, le_rfl, mapsto_domChart_source_codChart_source, this.contMDiffOn.congr, writtenInCharts
-/
theorem contMDiffOn (h : IsImmersionAtOfComplement F I J n f x) :
    CMDiff[h.domChart.source] n f := by
  rw [← h.domChart.contMDiffOn_writtenInExtend_iff h.domChart_mem_maximalAtlas
    h.codChart_mem_maximalAtlas le_rfl h.mapsto_domChart_source_codChart_source]; rw [← h.domChart.extend_target_eq_image_source]
  have : CMDiff n (h.equiv ∘ fun x => (x, 0)) := by
    rw [contMDiff_iff_contDiff]; fun_prop
  exact this.contMDiffOn.congr h.writtenInCharts

/--
theorem `contMDiffAt` / 定理 `contMDiffAt`

English:
theorem contMDiffAt
  given: (h : IsImmersionAtOfComplement F I J n f x)
  statement: CMDiffAt n f x
  proof: h.contMDiffOn.contMDiffAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

中文:
定理 contMDiffAt
  条件: (h : IsImmersionAtOfComplement F I J n f x)
  结论: CMDiffAt n f x
  证明: h.contMDiffOn.contMDiffAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

Depends on / 依赖: contMDiffAt, contMDiffOn, domChart, h.contMDiffOn.contMDiffAt, h.domChart.open_source.mem_nhds, mem_domChart_source, mem_nhds, open_source
-/
theorem contMDiffAt (h : IsImmersionAtOfComplement F I J n f x) : CMDiffAt n f x :=
  h.contMDiffOn.contMDiffAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

/--
lemma `aux` / 引理 `aux`

English:
lemma aux
  statement: {f : M -> N} {φ : N -> N'}
  proof: by
  -- Consider the local expressions of `f`, `φ`, `x` and `s'` in the charts we're considering.
  set f' := (h.domChart.extend J) ∘ f ∘ (extChartAt I x).symm
  set φ' := (h.codChart.extend J') ∘ φ ∘ (h.domChart.extend J).symm
  set x' := (extChartAt I x) x
  set s := (extChartAt I x).symm ⁻¹' t inter range I
  have hx' : extChartAt I x x in s := ⟨by simp [mem_chart_source H x, hxt], mem_range_self _⟩
  have h'loc : ContDiffWithinAt 𝕜 n ((h.codChart.extend J') ∘ (φ ∘ f) ∘ (extChartAt I x).symm)
      ((extChartAt I x).symm ⁻¹' t inter range I) (extChartAt I x x) := by
    replace h' : CMDiffAt[t] n (φ ∘ f) x := h'.contMDiffWithinAt
    rw [contMDiffWithinAt_iff_of_mem_maximalAtlas' h.codChart_mem_maximalAtlas] at h'
    exacts [h'.2, h.mem_codChart_source]
  -- By hypothesis, `φ ∘ f` (read in our charts) is `C^n` at `x'` within `s`.
  have h'' : ContDiffWithinAt 𝕜 n (φ' ∘ f') s x' := by
    apply h'loc.congr_of_mem (fun y hy => ?_) hx'
    simp only [mfld_simps, φ', f']
    rw [h.domChart.left_inv]
    apply ht hy.1
  -- On the other hand, composing `f'` with the inclusion `u ↦ (u, 0)` is also `C^n`
  -- (as a composition of `C^n` functions); this locally equals `φ ∘ f` in coordinates
  -- (since `f` is an immersion).
  set f'' := (h.equiv ∘ fun x => (x, 0)) ∘ f'
  have h''' : ContDiffWithinAt 𝕜 n f'' s x' := by
    refine h''.congr_of_mem (fun y hy => ?_) hx'
    simp only [f'', φ', f']
    nth_rw 2 [comp_apply]
    rw [Function.comp_apply]; rw [h.writtenInCharts]
    rw [h.domChart.extend_target_eq_image_source]
    exact ⟨(f ∘ (extChartAt I x).symm) y, ht hy.1, by simp⟩
  -- Composing with a suitable projection to cancel the inclusion, we deduce that `f` is `C^n`.
  have h'''' : ContDiffWithinAt 𝕜 n ((Prod.fst ∘ h.equiv.symm) ∘ f'') s x' :=
    ContDiffWithinAt.comp x' (by fun_prop) h''' (mapsTo_univ _ _)
  exact h''''.congr_of_mem (fun y hy => by simp [f'']) hx'

中文:
引理 aux
  结论: {f : M -> N} {φ : N -> N'}
  证明: by
  -- Consider the local expressions of `f`, `φ`, `x` and `s'` in the charts we're considering.
  set f' := (h.domChart.extend J) ∘ f ∘ (extChartAt I x).symm
  set φ' := (h.codChart.extend J') ∘ φ ∘ (h.domChart.extend J).symm
  set x' := (extChartAt I x) x
  set s := (extChartAt I x).symm ⁻¹' t inter range I
  have hx' : extChartAt I x x in s := ⟨by simp [mem_chart_source H x, hxt], mem_range_self _⟩
  have h'loc : ContDiffWithinAt 𝕜 n ((h.codChart.extend J') ∘ (φ ∘ f) ∘ (extChartAt I x).symm)
      ((extChartAt I x).symm ⁻¹' t inter range I) (extChartAt I x x) := by
    replace h' : CMDiffAt[t] n (φ ∘ f) x := h'.contMDiffWithinAt
    rw [contMDiffWithinAt_iff_of_mem_maximalAtlas' h.codChart_mem_maximalAtlas] at h'
    exacts [h'.2, h.mem_codChart_source]
  -- By hypothesis, `φ ∘ f` (read in our charts) is `C^n` at `x'` within `s`.
  have h'' : ContDiffWithinAt 𝕜 n (φ' ∘ f') s x' := by
    apply h'loc.congr_of_mem (fun y hy => ?_) hx'
    simp only [mfld_simps, φ', f']
    rw [h.domChart.left_inv]
    apply ht hy.1
  -- On the other hand, composing `f'` with the inclusion `u ↦ (u, 0)` is also `C^n`
  -- (as a composition of `C^n` functions); this locally equals `φ ∘ f` in coordinates
  -- (since `f` is an immersion).
  set f'' := (h.equiv ∘ fun x => (x, 0)) ∘ f'
  have h''' : ContDiffWithinAt 𝕜 n f'' s x' := by
    refine h''.congr_of_mem (fun y hy => ?_) hx'
    simp only [f'', φ', f']
    nth_rw 2 [comp_apply]
    rw [Function.comp_apply]; rw [h.writtenInCharts]
    rw [h.domChart.extend_target_eq_image_source]
    exact ⟨(f ∘ (extChartAt I x).symm) y, ht hy.1, by simp⟩
  -- Composing with a suitable projection to cancel the inclusion, we deduce that `f` is `C^n`.
  have h'''' : ContDiffWithinAt 𝕜 n ((Prod.fst ∘ h.equiv.symm) ∘ f'') s x' :=
    ContDiffWithinAt.comp x' (by fun_prop) h''' (mapsTo_univ _ _)
  exact h''''.congr_of_mem (fun y hy => by simp [f'']) hx'
-/
private lemma aux {f : M -> N} {φ : N -> N'}
    (h : IsImmersionAtOfComplement F J J' n φ (f x)) (h' : CMDiffAt n (φ ∘ f) x)
    {t : Set M} (ht : t subseteq f ⁻¹' h.domChart.source) (hxt : x in t) :
    ContDiffWithinAt 𝕜 n ((h.domChart.extend J) ∘ f ∘ (extChartAt I x).symm)
      ((extChartAt I x).symm ⁻¹' t inter range I) ((extChartAt I x) x) := by
  -- Consider the local expressions of `f`, `φ`, `x` and `s'` in the charts we're considering.
  set f' := (h.domChart.extend J) ∘ f ∘ (extChartAt I x).symm
  set φ' := (h.codChart.extend J') ∘ φ ∘ (h.domChart.extend J).symm
  set x' := (extChartAt I x) x
  set s := (extChartAt I x).symm ⁻¹' t inter range I
  have hx' : extChartAt I x x in s := ⟨by simp [mem_chart_source H x, hxt], mem_range_self _⟩
  have h'loc : ContDiffWithinAt 𝕜 n ((h.codChart.extend J') ∘ (φ ∘ f) ∘ (extChartAt I x).symm)
      ((extChartAt I x).symm ⁻¹' t inter range I) (extChartAt I x x) := by
    replace h' : CMDiffAt[t] n (φ ∘ f) x := h'.contMDiffWithinAt
    rw [contMDiffWithinAt_iff_of_mem_maximalAtlas' h.codChart_mem_maximalAtlas] at h'
    exacts [h'.2, h.mem_codChart_source]
  -- By hypothesis, `φ ∘ f` (read in our charts) is `C^n` at `x'` within `s`.
  have h'' : ContDiffWithinAt 𝕜 n (φ' ∘ f') s x' := by
    apply h'loc.congr_of_mem (fun y hy => ?_) hx'
    simp only [mfld_simps, φ', f']
    rw [h.domChart.left_inv]
    apply ht hy.1
  -- On the other hand, composing `f'` with the inclusion `u ↦ (u, 0)` is also `C^n`
  -- (as a composition of `C^n` functions); this locally equals `φ ∘ f` in coordinates
  -- (since `f` is an immersion).
  set f'' := (h.equiv ∘ fun x => (x, 0)) ∘ f'
  have h''' : ContDiffWithinAt 𝕜 n f'' s x' := by
    refine h''.congr_of_mem (fun y hy => ?_) hx'
    simp only [f'', φ', f']
    nth_rw 2 [comp_apply]
    rw [Function.comp_apply]; rw [h.writtenInCharts]
    rw [h.domChart.extend_target_eq_image_source]
    exact ⟨(f ∘ (extChartAt I x).symm) y, ht hy.1, by simp⟩
  -- Composing with a suitable projection to cancel the inclusion, we deduce that `f` is `C^n`.
  have h'''' : ContDiffWithinAt 𝕜 n ((Prod.fst ∘ h.equiv.symm) ∘ f'') s x' :=
    ContDiffWithinAt.comp x' (by fun_prop) h''' (mapsTo_univ _ _)
  exact h''''.congr_of_mem (fun y hy => by simp [f'']) hx'

/--
lemma `_root_.ContMDiffAt.iff_comp_isImmersionAtOfComplement` / 引理 `_root_.ContMDiffAt.iff_comp_isImmersionAtOfComplement`

English:
lemma _root_.ContMDiffAt.iff_comp_isImmersionAtOfComplement
  proof: by
  refine ⟨fun hf => ⟨hf.continuousAt, hφ.contMDiffAt.comp x hf⟩, fun ⟨hf, h'⟩ => ?_⟩
  -- Since `f` is continuous at `x`, some neighbourhood `t` of `x` is mapped
  -- into `hφ.domChart.source` under `f`. By restriction, we may assume `t` is open,
  -- so it suffices to test smoothness on `t`.
  have : hφ.domChart.source in 𝓝 (f x) := hφ.domChart.open_source.mem_nhds hφ.mem_domChart_source
  obtain ⟨t, ht, htopen, hxt⟩ := mem_nhds_iff.mp (hf this)
suffices CMDiffAt[t] n f x from this.contMDiffAt htopen.mem_nhds hxt
  -- We test smoothness of `f` on `t` in the preferred chart at `x` and `hφ.codChart`.
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas'
    hφ.domChart_mem_maximalAtlas hφ.mem_domChart_source]
  refine ⟨hf.continuousWithinAt, ?_⟩
  exact aux hφ h' ht hxt

中文:
引理 _root_.ContMDiffAt.iff_comp_isImmersionAtOfComplement
  证明: by
  refine ⟨fun hf => ⟨hf.continuousAt, hφ.contMDiffAt.comp x hf⟩, fun ⟨hf, h'⟩ => ?_⟩
  -- Since `f` is continuous at `x`, some neighbourhood `t` of `x` is mapped
  -- into `hφ.domChart.source` under `f`. By restriction, we may assume `t` is open,
  -- so it suffices to test smoothness on `t`.
  have : hφ.domChart.source in 𝓝 (f x) := hφ.domChart.open_source.mem_nhds hφ.mem_domChart_source
  obtain ⟨t, ht, htopen, hxt⟩ := mem_nhds_iff.mp (hf this)
suffices CMDiffAt[t] n f x from this.contMDiffAt htopen.mem_nhds hxt
  -- We test smoothness of `f` on `t` in the preferred chart at `x` and `hφ.codChart`.
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas'
    hφ.domChart_mem_maximalAtlas hφ.mem_domChart_source]
  refine ⟨hf.continuousWithinAt, ?_⟩
  exact aux hφ h' ht hxt

Depends on / 依赖: contMDiffAt, contMDiffAt.comp, continuousAt, hf.continuousAt
-/
lemma _root_.ContMDiffAt.iff_comp_isImmersionAtOfComplement
    {f : M -> N} {φ : N -> N'} (hφ : IsImmersionAtOfComplement F J J' n φ (f x)) :
    -- Note: `φ` need not be inducing, so continuity of `φ ∘ f` at `x`
    -- generally does not imply continuity of `f`
    CMDiffAt n f x ↔ ContinuousAt f x ∧ CMDiffAt n (φ ∘ f) x := by
  refine ⟨fun hf => ⟨hf.continuousAt, hφ.contMDiffAt.comp x hf⟩, fun ⟨hf, h'⟩ => ?_⟩
  -- Since `f` is continuous at `x`, some neighbourhood `t` of `x` is mapped
  -- into `hφ.domChart.source` under `f`. By restriction, we may assume `t` is open,
  -- so it suffices to test smoothness on `t`.
  have : hφ.domChart.source in 𝓝 (f x) := hφ.domChart.open_source.mem_nhds hφ.mem_domChart_source
  obtain ⟨t, ht, htopen, hxt⟩ := mem_nhds_iff.mp (hf this)
suffices CMDiffAt[t] n f x from this.contMDiffAt htopen.mem_nhds hxt
  -- We test smoothness of `f` on `t` in the preferred chart at `x` and `hφ.codChart`.
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas'
    hφ.domChart_mem_maximalAtlas hφ.mem_domChart_source]
  refine ⟨hf.continuousWithinAt, ?_⟩
  exact aux hφ h' ht hxt

end IsImmersionAtOfComplement

namespace IsImmersionAt

/--
lemma `mk_of_charts` / 引理 `mk_of_charts`

English:
lemma mk_of_charts
  statement: (equiv : (E × F) ≃L[𝕜] E'')
  proof: by
  have aux : IsImmersionAtOfComplement F I J n f x := by
    apply IsImmersionAtOfComplement.mk_of_charts <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsImmersionAtOfComplement.congr_F aux.smallEquiv]

中文:
引理 mk_of_charts
  结论: (equiv : (E × F) ≃L[𝕜] E'')
  证明: by
  have aux : IsImmersionAtOfComplement F I J n f x := by
    apply IsImmersionAtOfComplement.mk_of_charts <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsImmersionAtOfComplement.congr_F aux.smallEquiv]

Depends on / 依赖: IsImmersionAtOfComplement, IsImmersionAtOfComplement.congr_F, IsImmersionAtOfComplement.mk_of_charts, aux.smallComplement, aux.smallEquiv, congr_F, infer_instance, mk_of_charts, smallComplement, smallEquiv
-/
lemma mk_of_charts (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x in domChart.source) (hfx : f x in codChart.source)
    (hdomChart : domChart in IsManifold.maximalAtlas I n M)
    (hcodChart : codChart in IsManifold.maximalAtlas J n N)
    (hsource : domChart.source subseteq f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAt I J n f x := by
  have aux : IsImmersionAtOfComplement F I J n f x := by
    apply IsImmersionAtOfComplement.mk_of_charts <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsImmersionAtOfComplement.congr_F aux.smallEquiv]

/--
lemma `mk_of_continuousAt` / 引理 `mk_of_continuousAt`

English:
lemma mk_of_continuousAt
  statement: {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
  proof: by
  have aux : IsImmersionAtOfComplement F I J n f x := by
    apply IsImmersionAtOfComplement.mk_of_continuousAt <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsImmersionAtOfComplement.congr_F aux.smallEquiv]

中文:
引理 mk_of_continuousAt
  结论: {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
  证明: by
  have aux : IsImmersionAtOfComplement F I J n f x := by
    apply IsImmersionAtOfComplement.mk_of_continuousAt <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsImmersionAtOfComplement.congr_F aux.smallEquiv]

Depends on / 依赖: IsImmersionAtOfComplement, IsImmersionAtOfComplement.congr_F, IsImmersionAtOfComplement.mk_of_continuousAt, aux.smallComplement, aux.smallEquiv, congr_F, infer_instance, mk_of_continuousAt, smallComplement, smallEquiv
-/
lemma mk_of_continuousAt {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x in domChart.source) (hfx : f x in codChart.source)
    (hdomChart : domChart in IsManifold.maximalAtlas I n M)
    (hcodChart : codChart in IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAt I J n f x := by
  have aux : IsImmersionAtOfComplement F I J n f x := by
    apply IsImmersionAtOfComplement.mk_of_continuousAt <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsImmersionAtOfComplement.congr_F aux.smallEquiv]

/--
Definition of `complement` / `complement` 的定义

English:
definition complement
  signature: (h : IsImmersionAt I J n f x)
  body: Classical.choose h

中文:
定义 complement
  签名: (h : IsImmersionAt I J n f x)
  定义体: Classical.choose h

Depends on / 依赖: Classical, Classical.choose
-/
def complement (h : IsImmersionAt I J n f x) : Type u := Classical.choose h

@[no_expose] instance (h : IsImmersionAt I J n f x) : NormedAddCommGroup h.complement :=
Classical.choose Classical.choose_spec h

@[no_expose] instance (h : IsImmersionAt I J n f x) : NormedSpace 𝕜 h.complement :=
Classical.choose Classical.choose_spec Classical.choose_spec h

/--
lemma `isImmersionAtOfComplement_complement` / 引理 `isImmersionAtOfComplement_complement`

English:
lemma isImmersionAtOfComplement_complement
  given: (h : IsImmersionAt I J n f x)
  proof: Classical.choose_spec Classical.choose_spec Classical.choose_spec h

中文:
引理 isImmersionAtOfComplement_complement
  条件: (h : IsImmersionAt I J n f x)
  证明: Classical.choose_spec Classical.choose_spec Classical.choose_spec h

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
lemma isImmersionAtOfComplement_complement (h : IsImmersionAt I J n f x) :
    IsImmersionAtOfComplement h.complement I J n f x :=
Classical.choose_spec Classical.choose_spec Classical.choose_spec h

/--
Definition of `domChart` / `domChart` 的定义

English:
definition domChart
  signature: (h : IsImmersionAt I J n f x)
  body: h.isImmersionAtOfComplement_complement.domChart

中文:
定义 domChart
  签名: (h : IsImmersionAt I J n f x)
  定义体: h.isImmersionAtOfComplement_complement.domChart

Depends on / 依赖: domChart, h.isImmersionAtOfComplement_complement.domChart, isImmersionAtOfComplement_complement
-/
def domChart (h : IsImmersionAt I J n f x) : OpenPartialHomeomorph M H :=
  h.isImmersionAtOfComplement_complement.domChart

/--
Definition of `codChart` / `codChart` 的定义

English:
definition codChart
  signature: (h : IsImmersionAt I J n f x)
  body: h.isImmersionAtOfComplement_complement.codChart

中文:
定义 codChart
  签名: (h : IsImmersionAt I J n f x)
  定义体: h.isImmersionAtOfComplement_complement.codChart

Depends on / 依赖: codChart, h.isImmersionAtOfComplement_complement.codChart, isImmersionAtOfComplement_complement
-/
def codChart (h : IsImmersionAt I J n f x) : OpenPartialHomeomorph N G :=
  h.isImmersionAtOfComplement_complement.codChart

/--
lemma `mem_domChart_source` / 引理 `mem_domChart_source`

English:
lemma mem_domChart_source
  given: (h : IsImmersionAt I J n f x)
  statement: x in h.domChart.source
  proof: h.isImmersionAtOfComplement_complement.mem_domChart_source

中文:
引理 mem_domChart_source
  条件: (h : IsImmersionAt I J n f x)
  结论: x in h.domChart.source
  证明: h.isImmersionAtOfComplement_complement.mem_domChart_source

Depends on / 依赖: h.isImmersionAtOfComplement_complement.mem_domChart_source, isImmersionAtOfComplement_complement, mem_domChart_source
-/
lemma mem_domChart_source (h : IsImmersionAt I J n f x) : x in h.domChart.source :=
  h.isImmersionAtOfComplement_complement.mem_domChart_source

/--
lemma `mem_codChart_source` / 引理 `mem_codChart_source`

English:
lemma mem_codChart_source
  given: (h : IsImmersionAt I J n f x)
  statement: f x in h.codChart.source
  proof: h.isImmersionAtOfComplement_complement.mem_codChart_source

中文:
引理 mem_codChart_source
  条件: (h : IsImmersionAt I J n f x)
  结论: f x in h.codChart.source
  证明: h.isImmersionAtOfComplement_complement.mem_codChart_source

Depends on / 依赖: h.isImmersionAtOfComplement_complement.mem_codChart_source, isImmersionAtOfComplement_complement, mem_codChart_source
-/
lemma mem_codChart_source (h : IsImmersionAt I J n f x) : f x in h.codChart.source :=
  h.isImmersionAtOfComplement_complement.mem_codChart_source

/--
lemma `domChart_mem_maximalAtlas` / 引理 `domChart_mem_maximalAtlas`

English:
lemma domChart_mem_maximalAtlas
  given: (h : IsImmersionAt I J n f x)
  proof: h.isImmersionAtOfComplement_complement.domChart_mem_maximalAtlas

中文:
引理 domChart_mem_maximalAtlas
  条件: (h : IsImmersionAt I J n f x)
  证明: h.isImmersionAtOfComplement_complement.domChart_mem_maximalAtlas

Depends on / 依赖: domChart_mem_maximalAtlas, h.isImmersionAtOfComplement_complement.domChart_mem_maximalAtlas, isImmersionAtOfComplement_complement
-/
lemma domChart_mem_maximalAtlas (h : IsImmersionAt I J n f x) :
    h.domChart in IsManifold.maximalAtlas I n M :=
  h.isImmersionAtOfComplement_complement.domChart_mem_maximalAtlas

/--
lemma `codChart_mem_maximalAtlas` / 引理 `codChart_mem_maximalAtlas`

English:
lemma codChart_mem_maximalAtlas
  given: (h : IsImmersionAt I J n f x)
  proof: h.isImmersionAtOfComplement_complement.codChart_mem_maximalAtlas

中文:
引理 codChart_mem_maximalAtlas
  条件: (h : IsImmersionAt I J n f x)
  证明: h.isImmersionAtOfComplement_complement.codChart_mem_maximalAtlas

Depends on / 依赖: codChart_mem_maximalAtlas, h.isImmersionAtOfComplement_complement.codChart_mem_maximalAtlas, isImmersionAtOfComplement_complement
-/
lemma codChart_mem_maximalAtlas (h : IsImmersionAt I J n f x) :
    h.codChart in IsManifold.maximalAtlas J n N :=
  h.isImmersionAtOfComplement_complement.codChart_mem_maximalAtlas

/--
lemma `source_subset_preimage_source` / 引理 `source_subset_preimage_source`

English:
lemma source_subset_preimage_source
  given: (h : IsImmersionAt I J n f x)
  proof: h.isImmersionAtOfComplement_complement.source_subset_preimage_source

中文:
引理 source_subset_preimage_source
  条件: (h : IsImmersionAt I J n f x)
  证明: h.isImmersionAtOfComplement_complement.source_subset_preimage_source

Depends on / 依赖: h.isImmersionAtOfComplement_complement.source_subset_preimage_source, isImmersionAtOfComplement_complement, source_subset_preimage_source
-/
lemma source_subset_preimage_source (h : IsImmersionAt I J n f x) :
    h.domChart.source subseteq f ⁻¹' h.codChart.source :=
  h.isImmersionAtOfComplement_complement.source_subset_preimage_source

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: (h : IsImmersionAt I J n f x)
  body: h.isImmersionAtOfComplement_complement.equiv

中文:
定义 equiv
  签名: (h : IsImmersionAt I J n f x)
  定义体: h.isImmersionAtOfComplement_complement.equiv

Depends on / 依赖: h.isImmersionAtOfComplement_complement.equiv, isImmersionAtOfComplement_complement
-/
def equiv (h : IsImmersionAt I J n f x) : (E × h.complement) ≃L[𝕜] E'' :=
  h.isImmersionAtOfComplement_complement.equiv

/--
lemma `writtenInCharts` / 引理 `writtenInCharts`

English:
lemma writtenInCharts
  given: (h : IsImmersionAt I J n f x)
  proof: h.isImmersionAtOfComplement_complement.writtenInCharts

中文:
引理 writtenInCharts
  条件: (h : IsImmersionAt I J n f x)
  证明: h.isImmersionAtOfComplement_complement.writtenInCharts

Depends on / 依赖: h.isImmersionAtOfComplement_complement.writtenInCharts, isImmersionAtOfComplement_complement, writtenInCharts
-/
lemma writtenInCharts (h : IsImmersionAt I J n f x) :
    EqOn ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (h.equiv ∘ (·, 0))
      (h.domChart.extend I).target :=
  h.isImmersionAtOfComplement_complement.writtenInCharts

/--
lemma `property` / 引理 `property`

English:
lemma property
  given: (h : IsImmersionAt I J n f x)
  proof: h.isImmersionAtOfComplement_complement.property

中文:
引理 property
  条件: (h : IsImmersionAt I J n f x)
  证明: h.isImmersionAtOfComplement_complement.property

Depends on / 依赖: h.isImmersionAtOfComplement_complement.property, isImmersionAtOfComplement_complement, property
-/
lemma property (h : IsImmersionAt I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp h.complement I J M N) :=
  h.isImmersionAtOfComplement_complement.property

/--
lemma `map_target_subset_target` / 引理 `map_target_subset_target`

English:
lemma map_target_subset_target
  given: (h : IsImmersionAt I J n f x)
  proof: h.isImmersionAtOfComplement_complement.map_target_subset_target

中文:
引理 map_target_subset_target
  条件: (h : IsImmersionAt I J n f x)
  证明: h.isImmersionAtOfComplement_complement.map_target_subset_target

Depends on / 依赖: h.isImmersionAtOfComplement_complement.map_target_subset_target, isImmersionAtOfComplement_complement, map_target_subset_target
-/
lemma map_target_subset_target (h : IsImmersionAt I J n f x) :
    (h.equiv ∘ (·, 0)) '' (h.domChart.extend I).target subseteq (h.codChart.extend J).target :=
  h.isImmersionAtOfComplement_complement.map_target_subset_target

/--
lemma `target_subset_preimage_target` / 引理 `target_subset_preimage_target`

English:
lemma target_subset_preimage_target
  given: (h : IsImmersionAt I J n f x)
  proof: fun _x hx => h.map_target_subset_target (mem_image_of_mem _ hx)

中文:
引理 target_subset_preimage_target
  条件: (h : IsImmersionAt I J n f x)
  证明: fun _x hx => h.map_target_subset_target (mem_image_of_mem _ hx)

Depends on / 依赖: h.map_target_subset_target, map_target_subset_target, mem_image_of_mem
-/
lemma target_subset_preimage_target (h : IsImmersionAt I J n f x) :
    (h.domChart.extend I).target subseteq (h.equiv ∘ (·, 0)) ⁻¹' (h.codChart.extend J).target :=
  fun _x hx => h.map_target_subset_target (mem_image_of_mem _ hx)

/--
lemma `congr_of_eventuallyEq` / 引理 `congr_of_eventuallyEq`

English:
lemma congr_of_eventuallyEq
  given: (hf : IsImmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g)
  proof: by
  use hf.complement, by infer_instance, by infer_instance
  exact hf.isImmersionAtOfComplement_complement.congr_of_eventuallyEq hfg

中文:
引理 congr_of_eventuallyEq
  条件: (hf : IsImmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g)
  证明: by
  use hf.complement, by infer_instance, by infer_instance
  exact hf.isImmersionAtOfComplement_complement.congr_of_eventuallyEq hfg

Depends on / 依赖: complement, congr_of_eventuallyEq, hf.complement, hf.isImmersionAtOfComplement_complement.congr_of_eventuallyEq, infer_instance, isImmersionAtOfComplement_complement
-/
lemma congr_of_eventuallyEq (hf : IsImmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAt I J n g x := by
  use hf.complement, by infer_instance, by infer_instance
  exact hf.isImmersionAtOfComplement_complement.congr_of_eventuallyEq hfg

/--
lemma `congr_iff` / 引理 `congr_iff`

English:
lemma congr_iff
  given: (hfg : f =ᶠ[𝓝 x] g)
  proof: ⟨fun h => h.congr_of_eventuallyEq hfg, fun h => h.congr_of_eventuallyEq hfg.symm⟩

中文:
引理 congr_iff
  条件: (hfg : f =ᶠ[𝓝 x] g)
  证明: ⟨fun h => h.congr_of_eventuallyEq hfg, fun h => h.congr_of_eventuallyEq hfg.symm⟩

Depends on / 依赖: congr_of_eventuallyEq, h.congr_of_eventuallyEq, hfg.symm
-/
lemma congr_iff (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAt I J n f x ↔ IsImmersionAt I J n g x :=
  ⟨fun h => h.congr_of_eventuallyEq hfg, fun h => h.congr_of_eventuallyEq hfg.symm⟩

/--
lemma `_root_.IsOpen.isImmersionAt` / 引理 `_root_.IsOpen.isImmersionAt`

English:
lemma _root_.IsOpen.isImmersionAt
  proof: by
  rw [isOpen_iff_forall_mem_open]
  exact fun x hx => ⟨{x | IsImmersionAtOfComplement hx.complement I J n f x },
    fun y hy => hy.isImmersionAt, .isImmersionAtOfComplement,
    by simp [hx.isImmersionAtOfComplement_complement]⟩

中文:
引理 _root_.是开集.isImmersionAt
  证明: by
  rw [isOpen_iff_forall_mem_open]
  exact fun x hx => ⟨{x | IsImmersionAtOfComplement hx.complement I J n f x },
    fun y hy => hy.isImmersionAt, .isImmersionAtOfComplement,
    by simp [hx.isImmersionAtOfComplement_complement]⟩

Depends on / 依赖: IsImmersionAtOfComplement, complement, hx.complement, hx.isImmersionAtOfComplement_complement, hy.isImmersionAt, isImmersionAt, isImmersionAtOfComplement, isImmersionAtOfComplement_complement, isOpen_iff_forall_mem_open
-/
lemma _root_.IsOpen.isImmersionAt :
    IsOpen {x | IsImmersionAt I J n f x} := by
  rw [isOpen_iff_forall_mem_open]
  exact fun x hx => ⟨{x | IsImmersionAtOfComplement hx.complement I J n f x },
    fun y hy => hy.isImmersionAt, .isImmersionAtOfComplement,
    by simp [hx.isImmersionAtOfComplement_complement]⟩

/--
theorem `prodMap` / 定理 `prodMap`

English:
theorem prodMap
  statement: {f : M -> N} {g : M' -> N'} {x' : M'}
  proof: hf.isImmersionAtOfComplement_complement.prodMap hg.isImmersionAtOfComplement_complement
.isImmersionAt

中文:
定理 prodMap
  结论: {f : M -> N} {g : M' -> N'} {x' : M'}
  证明: hf.isImmersionAtOfComplement_complement.prodMap hg.isImmersionAtOfComplement_complement
.isImmersionAt

Depends on / 依赖: hf.isImmersionAtOfComplement_complement.prodMap, hg.isImmersionAtOfComplement_complement, isImmersionAt, isImmersionAtOfComplement_complement, prodMap
-/
theorem prodMap {f : M -> N} {g : M' -> N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsImmersionAt I J n f x) (hg : IsImmersionAt I' J' n g x') :
    IsImmersionAt (I.prod I') (J.prod J') n (Prod.map f g) (x, x') :=
  hf.isImmersionAtOfComplement_complement.prodMap hg.isImmersionAtOfComplement_complement
.isImmersionAt

/--
lemma `of_opens` / 引理 `of_opens`

English:
lemma of_opens
  given: [IsManifold I n M] (s : TopologicalSpace.Opens M) (hx : x in s)
  proof: by
  use PUnit, by infer_instance, by infer_instance
  apply Manifold.IsImmersionAtOfComplement.of_opens

中文:
引理 of_opens
  条件: [是流形 I n M] (s : 拓扑空间.Opens M) (hx : x in s)
  证明: by
  use PUnit, by infer_instance, by infer_instance
  apply Manifold.IsImmersionAtOfComplement.of_opens

Depends on / 依赖: IsImmersionAtOfComplement, Manifold, Manifold.IsImmersionAtOfComplement.of_opens, infer_instance, of_opens
-/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) (hx : x in s) :
    IsImmersionAt I I n (Subtype.val : s -> M) ⟨x, hx⟩ := by
  use PUnit, by infer_instance, by infer_instance
  apply Manifold.IsImmersionAtOfComplement.of_opens

/--
lemma `_root_.ModelWithCorners.isImmersionAt` / 引理 `_root_.ModelWithCorners.isImmersionAt`

English:
lemma _root_.ModelWithCorners.isImmersionAt
  given: {n : Nat} {x : H}
  proof: by
  use PUnit, by infer_instance, by infer_instance
  exact I.isImmersionAtOfComplement

中文:
引理 _root_.带角模型.isImmersionAt
  条件: {n : 自然数} {x : H}
  证明: by
  use PUnit, by infer_instance, by infer_instance
  exact I.isImmersionAtOfComplement
-/
protected lemma _root_.ModelWithCorners.isImmersionAt {n : Nat} {x : H} :
    IsImmersionAt I (modelWithCornersSelf 𝕜 E) n I x := by
  use PUnit, by infer_instance, by infer_instance
  exact I.isImmersionAtOfComplement

/--
theorem `continuousOn` / 定理 `continuousOn`

English:
theorem continuousOn
  given: (h : IsImmersionAt I J n f x)
  statement: ContinuousOn f h.domChart.source
  proof: h.isImmersionAtOfComplement_complement.continuousOn

中文:
定理 continuousOn
  条件: (h : IsImmersionAt I J n f x)
  结论: ContinuousOn f h.domChart.source
  证明: h.isImmersionAtOfComplement_complement.continuousOn

Depends on / 依赖: continuousOn, h.isImmersionAtOfComplement_complement.continuousOn, isImmersionAtOfComplement_complement
-/
theorem continuousOn (h : IsImmersionAt I J n f x) : ContinuousOn f h.domChart.source :=
  h.isImmersionAtOfComplement_complement.continuousOn

/--
theorem `continuousAt` / 定理 `continuousAt`

English:
theorem continuousAt
  given: (h : IsImmersionAt I J n f x)
  statement: ContinuousAt f x
  proof: h.isImmersionAtOfComplement_complement.continuousAt

中文:
定理 continuousAt
  条件: (h : IsImmersionAt I J n f x)
  结论: ContinuousAt f x
  证明: h.isImmersionAtOfComplement_complement.continuousAt

Depends on / 依赖: continuousAt, h.isImmersionAtOfComplement_complement.continuousAt, isImmersionAtOfComplement_complement
-/
theorem continuousAt (h : IsImmersionAt I J n f x) : ContinuousAt f x :=
  h.isImmersionAtOfComplement_complement.continuousAt

/--
theorem `contMDiffOn` / 定理 `contMDiffOn`

English:
theorem contMDiffOn
  given: (h : IsImmersionAt I J n f x)
  statement: CMDiff[h.domChart.source] n f
  proof: h.isImmersionAtOfComplement_complement.contMDiffOn

中文:
定理 contMDiffOn
  条件: (h : IsImmersionAt I J n f x)
  结论: CMDiff[h.domChart.source] n f
  证明: h.isImmersionAtOfComplement_complement.contMDiffOn

Depends on / 依赖: contMDiffOn, h.isImmersionAtOfComplement_complement.contMDiffOn, isImmersionAtOfComplement_complement
-/
theorem contMDiffOn (h : IsImmersionAt I J n f x) : CMDiff[h.domChart.source] n f :=
  h.isImmersionAtOfComplement_complement.contMDiffOn

/--
theorem `contMDiffAt` / 定理 `contMDiffAt`

English:
theorem contMDiffAt
  given: (h : IsImmersionAt I J n f x)
  statement: CMDiffAt n f x
  proof: h.isImmersionAtOfComplement_complement.contMDiffAt

中文:
定理 contMDiffAt
  条件: (h : IsImmersionAt I J n f x)
  结论: CMDiffAt n f x
  证明: h.isImmersionAtOfComplement_complement.contMDiffAt

Depends on / 依赖: contMDiffAt, h.isImmersionAtOfComplement_complement.contMDiffAt, isImmersionAtOfComplement_complement
-/
theorem contMDiffAt (h : IsImmersionAt I J n f x) : CMDiffAt n f x :=
  h.isImmersionAtOfComplement_complement.contMDiffAt

/--
lemma `_root_.ContMDiffAt.iff_comp_isImmersionAt` / 引理 `_root_.ContMDiffAt.iff_comp_isImmersionAt`

English:
lemma _root_.ContMDiffAt.iff_comp_isImmersionAt
  statement: {f : M -> N} {φ : N -> N'}
  proof: by
  rw [← ContMDiffAt.iff_comp_isImmersionAtOfComplement hφ.isImmersionAtOfComplement_complement]

中文:
引理 _root_.ContMDiffAt.iff_comp_isImmersionAt
  结论: {f : M -> N} {φ : N -> N'}
  证明: by
  rw [← ContMDiffAt.iff_comp_isImmersionAtOfComplement hφ.isImmersionAtOfComplement_complement]

Depends on / 依赖: ContMDiffAt, ContMDiffAt.iff_comp_isImmersionAtOfComplement, iff_comp_isImmersionAtOfComplement, isImmersionAtOfComplement_complement
-/
lemma _root_.ContMDiffAt.iff_comp_isImmersionAt {f : M -> N} {φ : N -> N'}
    (hφ : IsImmersionAt J J' n φ (f x)) :
    -- Note: `φ` need not be inducing, so continuity of `φ ∘ f` at `x`
    -- generally does not imply continuity of `f`
    CMDiffAt n f x ↔ ContinuousAt f x ∧ CMDiffAt n (φ ∘ f) x := by
  rw [← ContMDiffAt.iff_comp_isImmersionAtOfComplement hφ.isImmersionAtOfComplement_complement]

end IsImmersionAt

variable (F I J n) in
/-- `f : M → N` is a `C^n` immersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `u ↦ (u, 0)`.

In other words, `f` is an immersion at each `x ∈ M`.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in `E'`:
being an immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`.
-/
@[expose]
/--
Definition of `IsImmersionOfComplement` / `IsImmersionOfComplement` 的定义

English:
definition IsImmersionOfComplement
  signature: (f : M -> N)
  body: forall x, IsImmersionAtOfComplement F I J n f x

中文:
定义 IsImmersionOfComplement
  签名: (f : M -> N)
  定义体: forall x, IsImmersionAtOfComplement F I J n f x

Depends on / 依赖: IsImmersionAtOfComplement
-/
def IsImmersionOfComplement (f : M -> N) : Prop := forall x, IsImmersionAtOfComplement F I J n f x

variable (I J n) in
/--
Definition of `IsImmersion` / `IsImmersion` 的定义

English:
definition IsImmersion
  signature: (f : M -> N)
  body: exists (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F), IsImmersionOfComplement F I J n f

中文:
定义 是Immersion
  签名: (f : M -> N)
  定义体: exists (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F), IsImmersionOfComplement F I J n f

Depends on / 依赖: IsImmersionOfComplement, NormedAddCommGroup, NormedSpace
-/
def IsImmersion (f : M -> N) : Prop :=
  exists (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F), IsImmersionOfComplement F I J n f

namespace IsImmersionOfComplement

variable {f g : M -> N}

/--
lemma `isImmersionAt` / 引理 `isImmersionAt`

English:
lemma isImmersionAt
  given: (h : IsImmersionOfComplement F I J n f) (x : M)
  proof: h x

中文:
引理 isImmersionAt
  条件: (h : IsImmersionOfComplement F I J n f) (x : M)
  证明: h x
-/
lemma isImmersionAt (h : IsImmersionOfComplement F I J n f) (x : M) :
    IsImmersionAtOfComplement F I J n f x := h x

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  given: (h : IsImmersionOfComplement F I J n f) (heq : f = g)
  proof: heq ▸ h

中文:
定理 congr
  条件: (h : IsImmersionOfComplement F I J n f) (heq : f = g)
  证明: heq ▸ h
-/
theorem congr (h : IsImmersionOfComplement F I J n f) (heq : f = g) :
    IsImmersionOfComplement F I J n g :=
  heq ▸ h

/--
lemma `trans_F` / 引理 `trans_F`

English:
lemma trans_F
  given: (h : IsImmersionOfComplement F I J n f) (e : F ≃L[𝕜] F')
  proof: fun x => (h x).trans_F e

中文:
引理 trans_F
  条件: (h : IsImmersionOfComplement F I J n f) (e : F ≃L[𝕜] F')
  证明: fun x => (h x).trans_F e

Depends on / 依赖: trans_F
-/
lemma trans_F (h : IsImmersionOfComplement F I J n f) (e : F ≃L[𝕜] F') :
    IsImmersionOfComplement F' I J n f :=
  fun x => (h x).trans_F e

/--
lemma `congr_F` / 引理 `congr_F`

English:
lemma congr_F
  given: (e : F ≃L[𝕜] F')
  proof: ⟨fun h => trans_F (e := e) h, fun h => trans_F (e := e.symm) h⟩

中文:
引理 congr_F
  条件: (e : F ≃L[𝕜] F')
  证明: ⟨fun h => trans_F (e := e) h, fun h => trans_F (e := e.symm) h⟩

Depends on / 依赖: e.symm, trans_F
-/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsImmersionOfComplement F I J n f ↔ IsImmersionOfComplement F' I J n f :=
  ⟨fun h => trans_F (e := e) h, fun h => trans_F (e := e.symm) h⟩

/--
theorem `prodMap` / 定理 `prodMap`

English:
theorem prodMap
  statement: {f : M -> N} {g : M' -> N'}
  proof: fun ⟨x, x'⟩ => (h x).prodMap (h' x')

中文:
定理 prodMap
  结论: {f : M -> N} {g : M' -> N'}
  证明: fun ⟨x, x'⟩ => (h x).prodMap (h' x')

Depends on / 依赖: prodMap
-/
theorem prodMap {f : M -> N} {g : M' -> N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (h : IsImmersionOfComplement F I J n f) (h' : IsImmersionOfComplement F' I' J' n g) :
    IsImmersionOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) :=
  fun ⟨x, x'⟩ => (h x).prodMap (h' x')

/--
lemma `isImmersion` / 引理 `isImmersion`

English:
lemma isImmersion
  given: (h : IsImmersionOfComplement F I J n f)
  statement: IsImmersion I J n f
  proof: by
  by_cases! hM : IsEmpty M
  · rw [IsImmersion]
    use PUnit, by infer_instance, by infer_instance
    exact fun x => (IsEmpty.false x).elim
  inhabit M
  let x : M := Inhabited.default
  use (h x).smallComplement, by infer_instance, by infer_instance
  exact (IsImmersionOfComplement.congr_F (h x).smallEquiv).mp h

中文:
引理 isImmersion
  条件: (h : IsImmersionOfComplement F I J n f)
  结论: 是Immersion I J n f
  证明: by
  by_cases! hM : IsEmpty M
  · rw [IsImmersion]
    use PUnit, by infer_instance, by infer_instance
    exact fun x => (IsEmpty.false x).elim
  inhabit M
  let x : M := Inhabited.default
  use (h x).smallComplement, by infer_instance, by infer_instance
  exact (IsImmersionOfComplement.congr_F (h x).smallEquiv).mp h

Depends on / 依赖: Inhabited, Inhabited.default, IsEmpty, IsEmpty.false, IsImmersion, IsImmersionOfComplement, IsImmersionOfComplement.congr_F, congr_F, infer_instance, inhabit, smallComplement, smallEquiv
-/
lemma isImmersion (h : IsImmersionOfComplement F I J n f) : IsImmersion I J n f := by
  by_cases! hM : IsEmpty M
  · rw [IsImmersion]
    use PUnit, by infer_instance, by infer_instance
    exact fun x => (IsEmpty.false x).elim
  inhabit M
  let x : M := Inhabited.default
  use (h x).smallComplement, by infer_instance, by infer_instance
  exact (IsImmersionOfComplement.congr_F (h x).smallEquiv).mp h

open IsManifold in
/--
lemma `id` / 引理 `id`

English:
lemma id
  given: [IsManifold I n M]
  statement: IsImmersionOfComplement PUnit I I n (@id M)
  proof: by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt (continuousAt_id) (.prodUnique 𝕜 E _)
    (chartAt H x) (chartAt H x) (mem_chart_source H x) (mem_chart_source H x)
    (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas x)
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all)]; rw [I.right_inv (by simp_all)]
  simpa

中文:
引理 id
  条件: [是流形 I n M]
  结论: IsImmersionOfComplement 命题单元 I I n (@id M)
  证明: by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt (continuousAt_id) (.prodUnique 𝕜 E _)
    (chartAt H x) (chartAt H x) (mem_chart_source H x) (mem_chart_source H x)
    (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas x)
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all)]; rw [I.right_inv (by simp_all)]
  simpa
-/
protected lemma id [IsManifold I n M] : IsImmersionOfComplement PUnit I I n (@id M) := by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt (continuousAt_id) (.prodUnique 𝕜 E _)
    (chartAt H x) (chartAt H x) (mem_chart_source H x) (mem_chart_source H x)
    (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas x)
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all)]; rw [I.right_inv (by simp_all)]
  simpa

/--
lemma `of_opens` / 引理 `of_opens`

English:
lemma of_opens
  given: [IsManifold I n M] (s : TopologicalSpace.Opens M)
  proof: fun y => IsImmersionAtOfComplement.of_opens s y

中文:
引理 of_opens
  条件: [是流形 I n M] (s : 拓扑空间.Opens M)
  证明: fun y => IsImmersionAtOfComplement.of_opens s y

Depends on / 依赖: IsImmersionAtOfComplement, IsImmersionAtOfComplement.of_opens, of_opens
-/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) :
    IsImmersionOfComplement PUnit I I n (Subtype.val : s -> M) :=
  fun y => IsImmersionAtOfComplement.of_opens s y

/--
lemma `_root_.ModelWithCorners.isImmersionOfComplement` / 引理 `_root_.ModelWithCorners.isImmersionOfComplement`

English:
lemma _root_.ModelWithCorners.isImmersionOfComplement
  given: {n : Nat}
  proof: fun _ => I.isImmersionAtOfComplement

中文:
引理 _root_.带角模型.isImmersionOfComplement
  条件: {n : 自然数}
  证明: fun _ => I.isImmersionAtOfComplement
-/
protected lemma _root_.ModelWithCorners.isImmersionOfComplement {n : Nat} :
    IsImmersionOfComplement PUnit I (modelWithCornersSelf 𝕜 E) n I :=
  fun _ => I.isImmersionAtOfComplement

/--
lemma `sumInl` / 引理 `sumInl`

English:
lemma sumInl
  statement: {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I n M]
  proof: by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt (equiv := (.prodUnique 𝕜 E _))
    (by fun_prop) _ _ (mem_chart_source H x) (mem_chart_source H (Sum.inl x))
    (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas (Sum.inl x))
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all)]; rw [I.right_inv (by simp_all)]
  simpa

中文:
引理 sumInl
  结论: {M' : 类型} [拓扑空间 M'] [Charted空间 H M'] [是流形 I n M]
  证明: by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt (equiv := (.prodUnique 𝕜 E _))
    (by fun_prop) _ _ (mem_chart_source H x) (mem_chart_source H (Sum.inl x))
    (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas (Sum.inl x))
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all)]; rw [I.right_inv (by simp_all)]
  simpa

Depends on / 依赖: I.right_inv, I.symm, IsImmersionAtOfComplement, IsImmersionAtOfComplement.mk_of_continuousAt, IsManifold, IsManifold.chart_mem_maximalAtlas, Sum.inl, chartAt, chart_mem_maximalAtlas, fun_prop, mem_chart_source, mk_of_continuousAt, prodUnique, right_inv
-/
lemma sumInl {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I n M]
    [IsManifold I n M'] : IsImmersionOfComplement Unit I I n (@Sum.inl M M') := by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt (equiv := (.prodUnique 𝕜 E _))
    (by fun_prop) _ _ (mem_chart_source H x) (mem_chart_source H (Sum.inl x))
    (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas (Sum.inl x))
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all)]; rw [I.right_inv (by simp_all)]
  simpa

/--
lemma `sumInr` / 引理 `sumInr`

English:
lemma sumInr
  statement: {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I n M]
  proof: by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt (equiv := (.prodUnique 𝕜 E _))
    (by fun_prop) _ _ (mem_chart_source H x) (mem_chart_source H (Sum.inr x))
    (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas (Sum.inr x))
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all)]; rw [I.right_inv (by simp_all)]
  simpa

中文:
引理 sumInr
  结论: {M' : 类型} [拓扑空间 M'] [Charted空间 H M'] [是流形 I n M]
  证明: by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt (equiv := (.prodUnique 𝕜 E _))
    (by fun_prop) _ _ (mem_chart_source H x) (mem_chart_source H (Sum.inr x))
    (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas (Sum.inr x))
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all)]; rw [I.right_inv (by simp_all)]
  simpa

Depends on / 依赖: I.right_inv, I.symm, IsImmersionAtOfComplement, IsImmersionAtOfComplement.mk_of_continuousAt, IsManifold, IsManifold.chart_mem_maximalAtlas, Sum.inr, chartAt, chart_mem_maximalAtlas, fun_prop, mem_chart_source, mk_of_continuousAt, prodUnique, right_inv
-/
lemma sumInr {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I n M]
    [IsManifold I n M'] : IsImmersionOfComplement Unit I I n (@Sum.inr M M') := by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt (equiv := (.prodUnique 𝕜 E _))
    (by fun_prop) _ _ (mem_chart_source H x) (mem_chart_source H (Sum.inr x))
    (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas (Sum.inr x))
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all)]; rw [I.right_inv (by simp_all)]
  simpa

/--
theorem `contMDiff` / 定理 `contMDiff`

English:
theorem contMDiff
  given: (h : IsImmersionOfComplement F I J n f)
  statement: CMDiff n f
  proof: fun x => (h x).contMDiffAt

中文:
定理 contMDiff
  条件: (h : IsImmersionOfComplement F I J n f)
  结论: CMDiff n f
  证明: fun x => (h x).contMDiffAt

Depends on / 依赖: contMDiffAt
-/
theorem contMDiff (h : IsImmersionOfComplement F I J n f) : CMDiff n f :=
  fun x => (h x).contMDiffAt

/--
lemma `_root_.ContMDiff.iff_comp_isImmersionOfComplement` / 引理 `_root_.ContMDiff.iff_comp_isImmersionOfComplement`

English:
lemma _root_.ContMDiff.iff_comp_isImmersionOfComplement
  statement: {f : M -> N} {φ : N -> N'}
  proof: by
  refine ⟨fun h => ⟨h.continuous, hφ.contMDiff.comp h⟩, fun ⟨h, h'⟩ x => ?_⟩
  rw [ContMDiffAt.iff_comp_isImmersionAtOfComplement (hφ (f x))]
  exact ⟨h.continuousAt, h' x⟩

中文:
引理 _root_.ContMDiff.iff_comp_isImmersionOfComplement
  结论: {f : M -> N} {φ : N -> N'}
  证明: by
  refine ⟨fun h => ⟨h.continuous, hφ.contMDiff.comp h⟩, fun ⟨h, h'⟩ x => ?_⟩
  rw [ContMDiffAt.iff_comp_isImmersionAtOfComplement (hφ (f x))]
  exact ⟨h.continuousAt, h' x⟩

Depends on / 依赖: ContMDiffAt, ContMDiffAt.iff_comp_isImmersionAtOfComplement, contMDiff, contMDiff.comp, continuous, continuousAt, h.continuous, h.continuousAt, iff_comp_isImmersionAtOfComplement
-/
lemma _root_.ContMDiff.iff_comp_isImmersionOfComplement {f : M -> N} {φ : N -> N'}
    (hφ : IsImmersionOfComplement F J J' n φ) :
    CMDiff n f ↔ Continuous f ∧ CMDiff n (φ ∘ f) := by
  refine ⟨fun h => ⟨h.continuous, hφ.contMDiff.comp h⟩, fun ⟨h, h'⟩ x => ?_⟩
  rw [ContMDiffAt.iff_comp_isImmersionAtOfComplement (hφ (f x))]
  exact ⟨h.continuousAt, h' x⟩

end IsImmersionOfComplement

namespace IsImmersion

variable {f g : M -> N}

/--
Definition of `complement` / `complement` 的定义

English:
definition complement
  signature: (h : IsImmersion I J n f)
  body: Classical.choose h

中文:
定义 complement
  签名: (h : 是Immersion I J n f)
  定义体: Classical.choose h

Depends on / 依赖: Classical, Classical.choose
-/
def complement (h : IsImmersion I J n f) : Type u := Classical.choose h

@[no_expose] instance (h : IsImmersion I J n f) : NormedAddCommGroup h.complement :=
Classical.choose Classical.choose_spec h

@[no_expose] instance (h : IsImmersion I J n f) : NormedSpace 𝕜 h.complement :=
Classical.choose Classical.choose_spec Classical.choose_spec h

/--
lemma `isImmersionOfComplement_complement` / 引理 `isImmersionOfComplement_complement`

English:
lemma isImmersionOfComplement_complement
  given: (h : IsImmersion I J n f)
  proof: Classical.choose_spec Classical.choose_spec Classical.choose_spec h

中文:
引理 isImmersionOfComplement_complement
  条件: (h : 是Immersion I J n f)
  证明: Classical.choose_spec Classical.choose_spec Classical.choose_spec h

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
lemma isImmersionOfComplement_complement (h : IsImmersion I J n f) :
    IsImmersionOfComplement h.complement I J n f :=
Classical.choose_spec Classical.choose_spec Classical.choose_spec h

/--
lemma `isImmersionAt` / 引理 `isImmersionAt`

English:
lemma isImmersionAt
  given: (h : IsImmersion I J n f) (x : M)
  statement: IsImmersionAt I J n f x
  proof: by
  rw [IsImmersionAt]
  use h.complement, by infer_instance, by infer_instance
  exact h.isImmersionOfComplement_complement x

中文:
引理 isImmersionAt
  条件: (h : 是Immersion I J n f) (x : M)
  结论: IsImmersionAt I J n f x
  证明: by
  rw [IsImmersionAt]
  use h.complement, by infer_instance, by infer_instance
  exact h.isImmersionOfComplement_complement x

Depends on / 依赖: IsImmersionAt, complement, h.complement, h.isImmersionOfComplement_complement, infer_instance, isImmersionOfComplement_complement
-/
lemma isImmersionAt (h : IsImmersion I J n f) (x : M) : IsImmersionAt I J n f x := by
  rw [IsImmersionAt]
  use h.complement, by infer_instance, by infer_instance
  exact h.isImmersionOfComplement_complement x

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  given: (h : IsImmersion I J n f) (heq : f = g)
  statement: IsImmersion I J n g
  proof: heq ▸ h

中文:
定理 congr
  条件: (h : 是Immersion I J n f) (heq : f = g)
  结论: 是Immersion I J n g
  证明: heq ▸ h
-/
theorem congr (h : IsImmersion I J n f) (heq : f = g) : IsImmersion I J n g :=
  heq ▸ h

/--
theorem `prodMap` / 定理 `prodMap`

English:
theorem prodMap
  statement: {f : M -> N} {g : M' -> N'}
  proof: (hf.isImmersionOfComplement_complement.prodMap hg.isImmersionOfComplement_complement).isImmersion

中文:
定理 prodMap
  结论: {f : M -> N} {g : M' -> N'}
  证明: (hf.isImmersionOfComplement_complement.prodMap hg.isImmersionOfComplement_complement).isImmersion

Depends on / 依赖: hf.isImmersionOfComplement_complement.prodMap, hg.isImmersionOfComplement_complement, isImmersion, isImmersionOfComplement_complement, prodMap
-/
theorem prodMap {f : M -> N} {g : M' -> N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsImmersion I J n f) (hg : IsImmersion I' J' n g) :
    IsImmersion (I.prod I') (J.prod J') n (Prod.map f g) :=
  (hf.isImmersionOfComplement_complement.prodMap hg.isImmersionOfComplement_complement).isImmersion

open IsManifold in
/--
lemma `id` / 引理 `id`

English:
lemma id
  given: [IsManifold I n M]
  statement: IsImmersion I I n (@id M)
  proof: by
  use PUnit, by infer_instance, by infer_instance
  exact IsImmersionOfComplement.id

中文:
引理 id
  条件: [是流形 I n M]
  结论: 是Immersion I I n (@id M)
  证明: by
  use PUnit, by infer_instance, by infer_instance
  exact IsImmersionOfComplement.id
-/
protected lemma id [IsManifold I n M] : IsImmersion I I n (@id M) := by
  use PUnit, by infer_instance, by infer_instance
  exact IsImmersionOfComplement.id

/--
lemma `of_opens` / 引理 `of_opens`

English:
lemma of_opens
  given: [IsManifold I n M] (s : TopologicalSpace.Opens M)
  proof: by
  use PUnit, by infer_instance, by infer_instance
  exact IsImmersionOfComplement.of_opens s

中文:
引理 of_opens
  条件: [是流形 I n M] (s : 拓扑空间.Opens M)
  证明: by
  use PUnit, by infer_instance, by infer_instance
  exact IsImmersionOfComplement.of_opens s

Depends on / 依赖: IsImmersionOfComplement, IsImmersionOfComplement.of_opens, infer_instance, of_opens
-/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) :
    IsImmersion I I n (Subtype.val : s -> M) := by
  use PUnit, by infer_instance, by infer_instance
  exact IsImmersionOfComplement.of_opens s

/--
lemma `_root_.ModelWithCorners.isImmersion` / 引理 `_root_.ModelWithCorners.isImmersion`

English:
lemma _root_.ModelWithCorners.isImmersion
  given: {n : Nat}
  proof: by
  use PUnit, by infer_instance, by infer_instance
  exact I.isImmersionOfComplement

中文:
引理 _root_.带角模型.isImmersion
  条件: {n : 自然数}
  证明: by
  use PUnit, by infer_instance, by infer_instance
  exact I.isImmersionOfComplement
-/
protected lemma _root_.ModelWithCorners.isImmersion {n : Nat} :
    IsImmersion I (modelWithCornersSelf 𝕜 E) n I := by
  use PUnit, by infer_instance, by infer_instance
  exact I.isImmersionOfComplement

/--
theorem `contMDiff` / 定理 `contMDiff`

English:
theorem contMDiff
  proof: h.isImmersionOfComplement_complement.contMDiff

中文:
定理 contMDiff
  证明: h.isImmersionOfComplement_complement.contMDiff

Depends on / 依赖: contMDiff, h.isImmersionOfComplement_complement.contMDiff, isImmersionOfComplement_complement
-/
theorem contMDiff
    (h : IsImmersion I J n f) : CMDiff n f :=
  h.isImmersionOfComplement_complement.contMDiff

/--
lemma `_root_.ContMDiff.iff_comp_isImmersion` / 引理 `_root_.ContMDiff.iff_comp_isImmersion`

English:
lemma _root_.ContMDiff.iff_comp_isImmersion
  given: {f : M -> N} {φ : N -> N'} (hφ : IsImmersion J J' n φ)
  proof: by
  rw [ContMDiff.iff_comp_isImmersionOfComplement hφ.isImmersionOfComplement_complement]

中文:
引理 _root_.ContMDiff.iff_comp_isImmersion
  条件: {f : M -> N} {φ : N -> N'} (hφ : 是Immersion J J' n φ)
  证明: by
  rw [ContMDiff.iff_comp_isImmersionOfComplement hφ.isImmersionOfComplement_complement]

Depends on / 依赖: ContMDiff, ContMDiff.iff_comp_isImmersionOfComplement, iff_comp_isImmersionOfComplement, isImmersionOfComplement_complement
-/
lemma _root_.ContMDiff.iff_comp_isImmersion {f : M -> N} {φ : N -> N'} (hφ : IsImmersion J J' n φ) :
    CMDiff n f ↔ Continuous f ∧ CMDiff n (φ ∘ f) := by
  rw [ContMDiff.iff_comp_isImmersionOfComplement hφ.isImmersionOfComplement_complement]

end IsImmersion

end Manifold
