/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Samantha Naranjo Guevara
-/
module

public import Mathlib.Geometry.Manifold.LocalSourceTargetProperty
public import Mathlib.Analysis.Normed.Module.Shrink
public import Mathlib.Topology.Algebra.Module.TransferInstance
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Notation

/-! # Smooth submersions

In this file, we define `C^n` submersions between `C^n` manifolds.
As in the case of immersions, the correct definition in the infinite-dimensional setting differs
from the classical finite-dimensional one (which is usually phrased in terms of surjectivity of the
`mfderiv`). Future work will prove that our definition implies the latter, and that both are
equivalent for finite-dimensional manifolds.

Our definition is formulated in terms of local normal forms; i.e., a map `f` is a submersion at `x`
if there exist charts near `x` and `f x` in which `f` looks like the standard projection
`(u, v) ↦ u`. The results in this file follow from abstract results about such local properties.

## Main definitions

* `IsSubmersionAtOfComplement F I J n f x` means a map `f : M → N` between `C^n` manifolds `M` and
  `N` is a submersion at `x : M`: there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`,
  respectively, such that in these charts, `f` looks like `(u, v) ↦ u`, w.r.t. some equivalence
  `E ≃L[𝕜] (E'' × F)`. Differentiability of `f` is not assumed as it follows from this definition.
* `IsSubmersionAt I J n f x` means that `f` is a `C^n` submersion at `x : M` for some choice of a
  complement `F` of the model normed space `E` of `M` in the model normed space `E''` of `N`.
* `IsSubmersionOfComplement F I J n f` means `f : M → N` is a submersion at every point `x : M`,
  w.r.t. the chosen complement `F`.
* `IsSubmersion I J n f` means `f : M → N` is a submersion at every point `x : M`,
  w.r.t. some global choice of complement.

## Main results

* `IsSubmersionAt.congr_of_eventuallyEq`: being a submersion is a local property.
  If `f` and `g` agree near `x` and `f` is a submersion at `x`, then so is `g`.
* `IsSubmersionAtOfComplement.congr_F`, `IsSubmersionOfComplement.congr_F`:
  being a submersion at `x` w.r.t. `F` is stable under
  replacing the complement `F` by an isomorphic copy.
* `isOpen_isSubmersionAtOfComplement` and `isOpen_isSubmersionAt`:
  the set of points where `IsSubmersionAt(OfComplement)` holds is open.
* `IsSubmersionAt.prodMap` and `IsSubmersion.prodMap`: the product of two submersions (at a point)
  is a submersion (at the product point).
* `IsSubmersionAt.contMDiffAt`: if `f` is a submersion at `x`, it is `C^n` at `x`.
* `IsSubmersion.contMDiff`: if `f` is a submersion, it is automatically `C^n`
  in the sense of `ContMDiff`.

## Implementation notes

The implementation strategy is identical to the one for immersions. See the implementation notes in
`Mathlib/Geometry/Manifold/Immersion` for details on:
* `IsSubmersionAt(OfComplement)`,
* universe level issues for complements,
* `small` and `smallEquiv` constructions.

## TODO
* The converse to `IsSubmersionAtOfComplement.congr_F` also holds: any two complements are
  isomorphic, as they are isomorphic to the kernel of the differential `mfderiv I J f x`.
* If `f` is a submersion at `x`, its differential `mfderiv I J f x` admits a continuous right
  inverse, in particular is surjective.
* If `f : M → N` is a map between Banach manifolds, `mfderiv I J f x` having a continuous right
  inverse implies `f` is a submersion at `x`. (This requires the inverse function theorem.)
* `IsSubmersionAt.comp`: if `f : M → N` and `g: N → N'` are maps between Banach manifolds such that
  `f` is a submersion at `x : M` and `g` is a submersion at `f x`, then `g ∘ f` is a submersion
  at `x`.
* `IsSubmersion.comp`: the composition of submersions is a submersion
* If `f : M → N` is a map between finite-dimensional manifolds, `mfderiv I J f x` being surjective
  implies `f` is a submersion at `x`.
* `IsLocalDiffeomorphAt.isSubmersionAt` and `IsLocalDiffeomorph.isSubmersion`:
  a local diffeomorphism (at `x`) is a submersion (at `x`)
* `Diffeomorph.isSubmersion`: in particular, a diffeomorphism is a submersion

## References

* [Alexander Schmeding, *An introduction to infinite-dimensional differential geometry*]
  [schmeding2023]
* Note that Margelef-Roig and Dominguez have a slightly different definition of submersions.

**Please talk** to Michael Rothgang before working on this file, to avoid duplicate work.
The above TODOs are the topic of Samantha Naranjo's master's thesis; it's nicer to coordinate.

-/

public noncomputable section

open scoped Topology ContDiff Manifold
open OpenPartialHomeomorph Function Set

namespace Manifold

universe u
-- We manually name the universe of `E` as `IsSubmersionAt` will use it.

variable {𝕜 E' E'' E''' F F' H H' G G' : Type*} {E : Type u} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}

variable {M M' N N' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop Nat∞}

variable (F I J M N) in
/--
Definition of `SubmersionAtProp` / `SubmersionAtProp` 的定义

English:
definition SubmersionAtProp
  signature: :
  body: fun f domChart codChart => exists equiv : E ≃L[𝕜] (E'' × F),
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in

中文:
定义 SubmersionAtProp
  签名: :
  定义体: fun f domChart codChart => exists equiv : E ≃L[𝕜] (E'' × F),
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in

Depends on / 依赖: Prod.fst, codChart, codChart.extend, domChart, domChart.extend, extend, target
-/
def SubmersionAtProp :
    (M -> N) -> OpenPartialHomeomorph M H -> OpenPartialHomeomorph N G -> Prop :=
  fun f domChart codChart => exists equiv : E ≃L[𝕜] (E'' × F),
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in
/--
lemma `isLocalSourceTargetProperty_submmersionAtProp` / 引理 `isLocalSourceTargetProperty_submmersionAtProp`

English:
lemma isLocalSourceTargetProperty_submmersionAtProp
  proof: fun ⟨equiv, hf⟩ => ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg := by
    intro ⟨equiv, hf⟩
    refine ⟨equiv, EqOn.trans (fun x hx => ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x in φ.source := by simp_all
    grind

中文:
引理 isLocalSourceTargetProperty_submmersionAtProp
  证明: fun ⟨equiv, hf⟩ => ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg := by
    intro ⟨equiv, hf⟩
    refine ⟨equiv, EqOn.trans (fun x hx => ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x in φ.source := by simp_all
    grind

Depends on / 依赖: hf.mono
-/
lemma isLocalSourceTargetProperty_submmersionAtProp :
    IsLocalSourceTargetProperty (SubmersionAtProp F I J M N) where
  mono_source {f φ ψ s} hs := fun ⟨equiv, hf⟩ => ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg := by
    intro ⟨equiv, hf⟩
    refine ⟨equiv, EqOn.trans (fun x hx => ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x in φ.source := by simp_all
    grind

variable (F I J n) in
/--
Definition of `IsSubmersionAtOfComplement` / `IsSubmersionAtOfComplement` 的定义

English:
definition IsSubmersionAtOfComplement
  signature: (f : M -> N) (x : M)
  body: LiftSourceTargetPropertyAt I J n f x (SubmersionAtProp F I J M N)

中文:
定义 IsSubmersionAtOfComplement
  签名: (f : M -> N) (x : M)
  定义体: LiftSourceTargetPropertyAt I J n f x (SubmersionAtProp F I J M N)

Depends on / 依赖: LiftSourceTargetPropertyAt, SubmersionAtProp
-/
def IsSubmersionAtOfComplement (f : M -> N) (x : M) : Prop :=
  LiftSourceTargetPropertyAt I J n f x (SubmersionAtProp F I J M N)

-- Lift the universe from `E`, to avoid a free universe parameter.

variable (I J n) in
/--
Definition of `IsSubmersionAt` / `IsSubmersionAt` 的定义

English:
definition IsSubmersionAt
  signature: (f : M -> N) (x : M)
  body: exists (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsSubmersionAtOfComplement F I J n f x

中文:
定义 IsSubmersionAt
  签名: (f : M -> N) (x : M)
  定义体: exists (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsSubmersionAtOfComplement F I J n f x

Depends on / 依赖: IsSubmersionAtOfComplement, NormedAddCommGroup, NormedSpace
-/
def IsSubmersionAt (f : M -> N) (x : M) : Prop :=
  exists (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsSubmersionAtOfComplement F I J n f x

variable {f g : M -> N} {x : M}

namespace IsSubmersionAtOfComplement

/--
lemma `mk_of_charts` / 引理 `mk_of_charts`

English:
lemma mk_of_charts
  statement: (equiv : E ≃L[𝕜] (E'' × F)) (domChart : OpenPartialHomeomorph M H)
  proof: by
  use domChart, codChart
  use equiv

中文:
引理 mk_of_charts
  结论: (equiv : E ≃L[𝕜] (E'' × F)) (domChart : OpenPartialHomeomorph M H)
  证明: by
  use domChart, codChart
  use equiv

Depends on / 依赖: codChart, domChart
-/
lemma mk_of_charts (equiv : E ≃L[𝕜] (E'' × F)) (domChart : OpenPartialHomeomorph M H)
    (codChart : OpenPartialHomeomorph N G)
    (hx : x in domChart.source) (hfx : f x in codChart.source)
    (hdomChart : domChart in IsManifold.maximalAtlas I n M)
    (hcodChart : codChart in IsManifold.maximalAtlas J n N)
    (hsource : domChart.source subseteq f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAtOfComplement F I J n f x := by
  use domChart, codChart
  use equiv

/--
lemma `mk_of_continuousAt` / 引理 `mk_of_continuousAt`

English:
lemma mk_of_continuousAt
  statement: {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : E ≃L[𝕜] (E'' × F))
  proof: LiftSourceTargetPropertyAt.mk_of_continuousAt hf
    isLocalSourceTargetProperty_submmersionAtProp
    _ _ hx hfx hdomChart hcodChart ⟨equiv, hwrittenInExtend⟩

中文:
引理 mk_of_continuousAt
  结论: {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : E ≃L[𝕜] (E'' × F))
  证明: LiftSourceTargetPropertyAt.mk_of_continuousAt hf
    isLocalSourceTargetProperty_submmersionAtProp
    _ _ hx hfx hdomChart hcodChart ⟨equiv, hwrittenInExtend⟩

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.mk_of_continuousAt, hcodChart, hdomChart, hwrittenInExtend, isLocalSourceTargetProperty_submmersionAtProp, mk_of_continuousAt
-/
lemma mk_of_continuousAt {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : E ≃L[𝕜] (E'' × F))
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x in domChart.source) (hfx : f x in codChart.source)
    (hdomChart : domChart in IsManifold.maximalAtlas I n M)
    (hcodChart : codChart in IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAtOfComplement F I J n f x :=
      LiftSourceTargetPropertyAt.mk_of_continuousAt hf
    isLocalSourceTargetProperty_submmersionAtProp
    _ _ hx hfx hdomChart hcodChart ⟨equiv, hwrittenInExtend⟩

/--
Definition of `domChart` / `domChart` 的定义

English:
definition domChart
  signature: (h : IsSubmersionAtOfComplement F I J n f x)
  body: LiftSourceTargetPropertyAt.domChart h

中文:
定义 domChart
  签名: (h : IsSubmersionAtOfComplement F I J n f x)
  定义体: LiftSourceTargetPropertyAt.domChart h

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.domChart, domChart
-/
def domChart (h : IsSubmersionAtOfComplement F I J n f x) :
    OpenPartialHomeomorph M H :=
  LiftSourceTargetPropertyAt.domChart h

/--
Definition of `codChart` / `codChart` 的定义

English:
definition codChart
  signature: (h : IsSubmersionAtOfComplement F I J n f x)
  body: LiftSourceTargetPropertyAt.codChart h

中文:
定义 codChart
  签名: (h : IsSubmersionAtOfComplement F I J n f x)
  定义体: LiftSourceTargetPropertyAt.codChart h

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.codChart, codChart
-/
def codChart (h : IsSubmersionAtOfComplement F I J n f x) :
    OpenPartialHomeomorph N G :=
  LiftSourceTargetPropertyAt.codChart h

/--
lemma `mem_domChart_source` / 引理 `mem_domChart_source`

English:
lemma mem_domChart_source
  given: (h : IsSubmersionAtOfComplement F I J n f x)
  statement: x in h.domChart.source
  proof: LiftSourceTargetPropertyAt.mem_domChart_source h

中文:
引理 mem_domChart_source
  条件: (h : IsSubmersionAtOfComplement F I J n f x)
  结论: x in h.domChart.source
  证明: LiftSourceTargetPropertyAt.mem_domChart_source h

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.mem_domChart_source, mem_domChart_source
-/
lemma mem_domChart_source (h : IsSubmersionAtOfComplement F I J n f x) : x in h.domChart.source :=
  LiftSourceTargetPropertyAt.mem_domChart_source h

/--
lemma `mem_codChart_source` / 引理 `mem_codChart_source`

English:
lemma mem_codChart_source
  given: (h : IsSubmersionAtOfComplement F I J n f x)
  statement: f x in h.codChart.source
  proof: LiftSourceTargetPropertyAt.mem_codChart_source h

中文:
引理 mem_codChart_source
  条件: (h : IsSubmersionAtOfComplement F I J n f x)
  结论: f x in h.codChart.source
  证明: LiftSourceTargetPropertyAt.mem_codChart_source h

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.mem_codChart_source, mem_codChart_source
-/
lemma mem_codChart_source (h : IsSubmersionAtOfComplement F I J n f x) : f x in h.codChart.source :=
  LiftSourceTargetPropertyAt.mem_codChart_source h

/--
lemma `domChart_mem_maximalAtlas` / 引理 `domChart_mem_maximalAtlas`

English:
lemma domChart_mem_maximalAtlas
  given: (h : IsSubmersionAtOfComplement F I J n f x)
  proof: LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas h

中文:
引理 domChart_mem_maximalAtlas
  条件: (h : IsSubmersionAtOfComplement F I J n f x)
  证明: LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas h

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas, domChart_mem_maximalAtlas
-/
lemma domChart_mem_maximalAtlas (h : IsSubmersionAtOfComplement F I J n f x) :
    h.domChart in IsManifold.maximalAtlas I n M :=
  LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas h

/--
lemma `codChart_mem_maximalAtlas` / 引理 `codChart_mem_maximalAtlas`

English:
lemma codChart_mem_maximalAtlas
  given: (h : IsSubmersionAtOfComplement F I J n f x)
  proof: LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas h

中文:
引理 codChart_mem_maximalAtlas
  条件: (h : IsSubmersionAtOfComplement F I J n f x)
  证明: LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas h

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas, codChart_mem_maximalAtlas
-/
lemma codChart_mem_maximalAtlas (h : IsSubmersionAtOfComplement F I J n f x) :
    h.codChart in IsManifold.maximalAtlas J n N :=
  LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas h

/--
lemma `source_subset_preimage_source` / 引理 `source_subset_preimage_source`

English:
lemma source_subset_preimage_source
  given: (h : IsSubmersionAtOfComplement F I J n f x)
  proof: LiftSourceTargetPropertyAt.source_subset_preimage_source h

中文:
引理 source_subset_preimage_source
  条件: (h : IsSubmersionAtOfComplement F I J n f x)
  证明: LiftSourceTargetPropertyAt.source_subset_preimage_source h

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.source_subset_preimage_source, source_subset_preimage_source
-/
lemma source_subset_preimage_source (h : IsSubmersionAtOfComplement F I J n f x) :
    h.domChart.source subseteq f ⁻¹' h.codChart.source :=
  LiftSourceTargetPropertyAt.source_subset_preimage_source h

/--
lemma `mapsto_domChart_source_codChart_source` / 引理 `mapsto_domChart_source_codChart_source`

English:
lemma mapsto_domChart_source_codChart_source
  given: (h : IsSubmersionAtOfComplement F I J n f x)
  proof: h.source_subset_preimage_source

中文:
引理 mapsto_domChart_source_codChart_source
  条件: (h : IsSubmersionAtOfComplement F I J n f x)
  证明: h.source_subset_preimage_source

Depends on / 依赖: h.source_subset_preimage_source, source_subset_preimage_source
-/
lemma mapsto_domChart_source_codChart_source (h : IsSubmersionAtOfComplement F I J n f x) :
    MapsTo f h.domChart.source h.codChart.source :=
  h.source_subset_preimage_source

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: (h : IsSubmersionAtOfComplement F I J n f x)
  body: Classical.choose LiftSourceTargetPropertyAt.property h

中文:
定义 equiv
  签名: (h : IsSubmersionAtOfComplement F I J n f x)
  定义体: Classical.choose LiftSourceTargetPropertyAt.property h

Depends on / 依赖: Classical, Classical.choose, LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.property, property
-/
def equiv (h : IsSubmersionAtOfComplement F I J n f x) : E ≃L[𝕜] (E'' × F) :=
Classical.choose LiftSourceTargetPropertyAt.property h

/--
lemma `writtenInCharts` / 引理 `writtenInCharts`

English:
lemma writtenInCharts
  given: (h : IsSubmersionAtOfComplement F I J n f x)
  proof: Classical.choose_spec LiftSourceTargetPropertyAt.property h

中文:
引理 writtenInCharts
  条件: (h : IsSubmersionAtOfComplement F I J n f x)
  证明: Classical.choose_spec LiftSourceTargetPropertyAt.property h

Depends on / 依赖: Classical, Classical.choose_spec, LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.property, choose_spec, property
-/
lemma writtenInCharts (h : IsSubmersionAtOfComplement F I J n f x) :
    EqOn ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (Prod.fst ∘ h.equiv)
      (h.domChart.extend I).target :=
Classical.choose_spec LiftSourceTargetPropertyAt.property h

/--
lemma `property` / 引理 `property`

English:
lemma property
  given: (h : IsSubmersionAtOfComplement F I J n f x)
  proof: h

中文:
引理 property
  条件: (h : IsSubmersionAtOfComplement F I J n f x)
  证明: h
-/
lemma property (h : IsSubmersionAtOfComplement F I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (SubmersionAtProp F I J M N) := h

/--
lemma `image_target_subset_target` / 引理 `image_target_subset_target`

English:
lemma image_target_subset_target
  given: (h : IsSubmersionAtOfComplement F I J n f x)
  proof: by
  rw [← h.writtenInCharts.image_eq]; rw [Set.image_comp]; rw [Set.image_comp]; rw [PartialEquiv.symm_image_target_eq_source]; rw [OpenPartialHomeomorph.extend_source]; rw [← PartialEquiv.image_source_eq_target]
  have : f '' h.domChart.source subseteq h.codChart.source := by
    simp [h.source_su

中文:
引理 image_target_subset_target
  条件: (h : IsSubmersionAtOfComplement F I J n f x)
  证明: by
  rw [← h.writtenInCharts.image_eq]; rw [Set.image_comp]; rw [Set.image_comp]; rw [PartialEquiv.symm_image_target_eq_source]; rw [OpenPartialHomeomorph.extend_source]; rw [← PartialEquiv.image_source_eq_target]
  have : f '' h.domChart.source subseteq h.codChart.source := by
    simp [h.source_su

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.extend_source, PartialEquiv, PartialEquiv.image_source_eq_target, PartialEquiv.symm_image_target_eq_source, Set.image_comp, codChart, domChart, extend_source, h.codChart.source, h.domChart.source, h.source_subset_preimage_source, h.writtenInCharts.image_eq, image_comp, image_eq, image_source_eq_target, source, source_subset_preimage_source, subseteq, symm_image_target_eq_source
-/
lemma image_target_subset_target (h : IsSubmersionAtOfComplement F I J n f x) :
    (Prod.fst ∘ h.equiv) '' (h.domChart.extend I).target subseteq (h.codChart.extend J).target := by
  rw [← h.writtenInCharts.image_eq]; rw [Set.image_comp]; rw [Set.image_comp]; rw [PartialEquiv.symm_image_target_eq_source]; rw [OpenPartialHomeomorph.extend_source]; rw [← PartialEquiv.image_source_eq_target]
  have : f '' h.domChart.source subseteq h.codChart.source := by
    simp [h.source_subset_preimage_source]
  grw [this, OpenPartialHomeomorph.extend_source]

/--
lemma `target_subset_preimage_target` / 引理 `target_subset_preimage_target`

English:
lemma target_subset_preimage_target
  given: (h : IsSubmersionAtOfComplement F I J n f x)
  proof: fun _x hx => h.image_target_subset_target (mem_image_of_mem _ hx)

中文:
引理 target_subset_preimage_target
  条件: (h : IsSubmersionAtOfComplement F I J n f x)
  证明: fun _x hx => h.image_target_subset_target (mem_image_of_mem _ hx)

Depends on / 依赖: h.image_target_subset_target, image_target_subset_target, mem_image_of_mem
-/
lemma target_subset_preimage_target (h : IsSubmersionAtOfComplement F I J n f x) :
    (h.domChart.extend I).target subseteq (Prod.fst ∘ h.equiv) ⁻¹' (h.codChart.extend J).target :=
  fun _x hx => h.image_target_subset_target (mem_image_of_mem _ hx)

/--
lemma `congr_of_eventuallyEq` / 引理 `congr_of_eventuallyEq`

English:
lemma congr_of_eventuallyEq
  given: (hf : IsSubmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g)
  proof: by
  exact LiftSourceTargetPropertyAt.congr_of_eventuallyEq
    isLocalSourceTargetProperty_submmersionAtProp hf.property hfg

中文:
引理 congr_of_eventuallyEq
  条件: (hf : IsSubmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g)
  证明: by
  exact LiftSourceTargetPropertyAt.congr_of_eventuallyEq
    isLocalSourceTargetProperty_submmersionAtProp hf.property hfg

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.congr_of_eventuallyEq, congr_of_eventuallyEq, hf.property, isLocalSourceTargetProperty_submmersionAtProp, property
-/
lemma congr_of_eventuallyEq (hf : IsSubmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsSubmersionAtOfComplement F I J n g x := by
  exact LiftSourceTargetPropertyAt.congr_of_eventuallyEq
    isLocalSourceTargetProperty_submmersionAtProp hf.property hfg

/--
lemma `congr_iff_of_eventuallyEq` / 引理 `congr_iff_of_eventuallyEq`

English:
lemma congr_iff_of_eventuallyEq
  given: (hfg : f =ᶠ[𝓝 x] g)
  proof: LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq
    isLocalSourceTargetProperty_submmersionAtProp hfg

中文:
引理 congr_iff_of_eventuallyEq
  条件: (hfg : f =ᶠ[𝓝 x] g)
  证明: LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq
    isLocalSourceTargetProperty_submmersionAtProp hfg

Depends on / 依赖: LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq, congr_iff_of_eventuallyEq, isLocalSourceTargetProperty_submmersionAtProp
-/
lemma congr_iff_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) :
    IsSubmersionAtOfComplement F I J n f x ↔ IsSubmersionAtOfComplement F I J n g x :=
  LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq
    isLocalSourceTargetProperty_submmersionAtProp hfg

/--
lemma `small` / 引理 `small`

English:
lemma small
  given: (hf : IsSubmersionAtOfComplement F I J n f x)
  statement: Small.{u} F
  proof: small_of_injective hf.equiv.symm.injective.comp (Prod.mk_right_injective 0)

中文:
引理 small
  条件: (hf : IsSubmersionAtOfComplement F I J n f x)
  结论: Small.{u} F
  证明: small_of_injective hf.equiv.symm.injective.comp (Prod.mk_right_injective 0)

Depends on / 依赖: Prod.mk_right_injective, hf.equiv.symm.injective.comp, injective, mk_right_injective, small_of_injective
-/
lemma small (hf : IsSubmersionAtOfComplement F I J n f x) : Small.{u} F :=
small_of_injective hf.equiv.symm.injective.comp (Prod.mk_right_injective 0)

/--
Definition of `smallComplement` / `smallComplement` 的定义

English:
definition smallComplement
  signature: (hf : IsSubmersionAtOfComplement F I J n f x)
  body: haveI := hf.small
  Shrink.{u} F

中文:
定义 smallComplement
  签名: (hf : IsSubmersionAtOfComplement F I J n f x)
  定义体: haveI := hf.small
  Shrink.{u} F

Depends on / 依赖: Shrink, hf.small
-/
def smallComplement (hf : IsSubmersionAtOfComplement F I J n f x) : Type u :=
  haveI := hf.small
  Shrink.{u} F

instance (hf : IsSubmersionAtOfComplement F I J n f x) : NormedAddCommGroup hf.smallComplement :=
  haveI := hf.small
inferInstanceAs NormedAddCommGroup (Shrink F)

instance (hf : IsSubmersionAtOfComplement F I J n f x) : NormedSpace 𝕜 hf.smallComplement :=
  haveI := hf.small
inferInstanceAs NormedSpace 𝕜 (Shrink F)

/--
Definition of `smallEquiv` / `smallEquiv` 的定义

English:
definition smallEquiv
  signature: (hf : IsSubmersionAtOfComplement F I J n f x)
  body: haveI := hf.small
  ((equivShrink F).symm.continuousLinearEquiv 𝕜).symm

中文:
定义 smallEquiv
  签名: (hf : IsSubmersionAtOfComplement F I J n f x)
  定义体: haveI := hf.small
  ((equivShrink F).symm.continuousLinearEquiv 𝕜).symm

Depends on / 依赖: continuousLinearEquiv, equivShrink, hf.small, symm.continuousLinearEquiv
-/
def smallEquiv (hf : IsSubmersionAtOfComplement F I J n f x) : F ≃L[𝕜] hf.smallComplement :=
  haveI := hf.small
  ((equivShrink F).symm.continuousLinearEquiv 𝕜).symm

/--
lemma `trans_F` / 引理 `trans_F`

English:
lemma trans_F
  given: (h : IsSubmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F')
  proof: by
  refine ⟨h.domChart, h.codChart, h.mem_domChart_source, h.mem_codChart_source,
    h.domChart_mem_maximalAtlas, h.codChart_mem_maximalAtlas, h.source_subset_preimage_source, ?_⟩
  use h.equiv.trans ((ContinuousLinearEquiv.refl 𝕜 E'').prodCongr e)
  apply Set.EqOn.trans h.writtenInCharts
  intro 

中文:
引理 trans_F
  条件: (h : IsSubmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F')
  证明: by
  refine ⟨h.domChart, h.codChart, h.mem_domChart_source, h.mem_codChart_source,
    h.domChart_mem_maximalAtlas, h.codChart_mem_maximalAtlas, h.source_subset_preimage_source, ?_⟩
  use h.equiv.trans ((ContinuousLinearEquiv.refl 𝕜 E'').prodCongr e)
  apply Set.EqOn.trans h.writtenInCharts
  intro 

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.refl, Set.EqOn.trans, codChart, codChart_mem_maximalAtlas, domChart, domChart_mem_maximalAtlas, h.codChart, h.codChart_mem_maximalAtlas, h.domChart, h.domChart_mem_maximalAtlas, h.equiv.trans, h.mem_codChart_source, h.mem_domChart_source, h.source_subset_preimage_source, h.writtenInCharts, mem_codChart_source, mem_domChart_source, prodCongr, source_subset_preimage_source
-/
lemma trans_F (h : IsSubmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F') :
    IsSubmersionAtOfComplement F' I J n f x := by
  refine ⟨h.domChart, h.codChart, h.mem_domChart_source, h.mem_codChart_source,
    h.domChart_mem_maximalAtlas, h.codChart_mem_maximalAtlas, h.source_subset_preimage_source, ?_⟩
  use h.equiv.trans ((ContinuousLinearEquiv.refl 𝕜 E'').prodCongr e)
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
    IsSubmersionAtOfComplement F I J n f x ↔ IsSubmersionAtOfComplement F' I J n f x :=
  ⟨fun h => trans_F (e := e) h, fun h => trans_F (e := e.symm) h⟩

/--
lemma `_root_.isOpen_isSubmersionAtOfComplement` / 引理 `_root_.isOpen_isSubmersionAtOfComplement`

English:
lemma _root_.isOpen_isSubmersionAtOfComplement
  proof: by
  exact IsOpen.liftSourceTargetPropertyAt

中文:
引理 _root_.isOpen_isSubmersionAtOfComplement
  证明: by
  exact IsOpen.liftSourceTargetPropertyAt

Depends on / 依赖: IsOpen, IsOpen.liftSourceTargetPropertyAt, liftSourceTargetPropertyAt
-/
lemma _root_.isOpen_isSubmersionAtOfComplement :
    IsOpen {x | IsSubmersionAtOfComplement F I J n f x} := by
  exact IsOpen.liftSourceTargetPropertyAt

/--
theorem `prodMap` / 定理 `prodMap`

English:
theorem prodMap
  statement: {f : M -> N} {g : M' -> N'} {x' : M'}
  proof: by
  apply LiftSourceTargetPropertyAt.prodMap hf.property hg.property
  rintro f φ₁ ψ₁ g φ₂ ψ₂ ⟨equiv₁, hfprop⟩ ⟨equiv₂, hgprop⟩
  use (equiv₁.prodCongr equiv₂).trans (ContinuousLinearEquiv.prodProdProdComm 𝕜 E'' F E''' F')
  rw [φ₁.extend_prod φ₂]; rw [ψ₁.extend_prod]; rw [PartialEquiv.prod_target]

中文:
定理 prodMap
  结论: {f : M -> N} {g : M' -> N'} {x' : M'}
  证明: by
  apply LiftSourceTargetPropertyAt.prodMap hf.property hg.property
  rintro f φ₁ ψ₁ g φ₂ ψ₂ ⟨equiv₁, hfprop⟩ ⟨equiv₂, hgprop⟩
  use (equiv₁.prodCongr equiv₂).trans (ContinuousLinearEquiv.prodProdProdComm 𝕜 E'' F E''' F')
  rw [φ₁.extend_prod φ₂]; rw [ψ₁.extend_prod]; rw [PartialEquiv.prod_target]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.prodProdProdComm, LiftSourceTargetPropertyAt, LiftSourceTargetPropertyAt.prodMap, PartialEquiv, PartialEquiv.prod_target, eqOn_prod_iff, extend_prod, hf.property, hfprop, hg.property, hgprop, prodCongr, prodMap, prodProdProdComm, prod_target, property
-/
theorem prodMap {f : M -> N} {g : M' -> N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersionAtOfComplement F I J n f x)
    (hg : IsSubmersionAtOfComplement F' I' J' n g x') :
    IsSubmersionAtOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) (x, x') := by
  apply LiftSourceTargetPropertyAt.prodMap hf.property hg.property
  rintro f φ₁ ψ₁ g φ₂ ψ₂ ⟨equiv₁, hfprop⟩ ⟨equiv₂, hgprop⟩
  use (equiv₁.prodCongr equiv₂).trans (ContinuousLinearEquiv.prodProdProdComm 𝕜 E'' F E''' F')
  rw [φ₁.extend_prod φ₂]; rw [ψ₁.extend_prod]; rw [PartialEquiv.prod_target]; rw [eqOn_prod_iff]
  exact ⟨fun x ⟨hx, hx'⟩ => by simpa using hfprop hx, fun x ⟨hx, hx'⟩ => by simpa using hgprop hx'⟩

/--
lemma `isSubmersionAt` / 引理 `isSubmersionAt`

English:
lemma isSubmersionAt
  given: (h : IsSubmersionAtOfComplement F I J n f x)
  proof: by
  use h.smallComplement, by infer_instance, by infer_instance
  exact (IsSubmersionAtOfComplement.congr_F h.smallEquiv).mp h

中文:
引理 isSubmersionAt
  条件: (h : IsSubmersionAtOfComplement F I J n f x)
  证明: by
  use h.smallComplement, by infer_instance, by infer_instance
  exact (IsSubmersionAtOfComplement.congr_F h.smallEquiv).mp h

Depends on / 依赖: IsSubmersionAtOfComplement, IsSubmersionAtOfComplement.congr_F, congr_F, h.smallComplement, h.smallEquiv, infer_instance, smallComplement, smallEquiv
-/
lemma isSubmersionAt (h : IsSubmersionAtOfComplement F I J n f x) :
    IsSubmersionAt I J n f x := by
  use h.smallComplement, by infer_instance, by infer_instance
  exact (IsSubmersionAtOfComplement.congr_F h.smallEquiv).mp h

/--
theorem `contMDiffOn` / 定理 `contMDiffOn`

English:
theorem contMDiffOn
  given: (h : IsSubmersionAtOfComplement F I J n f x)
  proof: by
  rw [← contMDiffOn_writtenInExtend_iff h.domChart_mem_maximalAtlas
    h.codChart_mem_maximalAtlas le_rfl h.mapsto_domChart_source_codChart_source]; rw [← h.domChart.extend_target_eq_image_source]
  have : CMDiff n (Prod.fst ∘ h.equiv) := by rw [contMDiff_iff_contDiff]; fun_prop
  exact this.con

中文:
定理 contMDiffOn
  条件: (h : IsSubmersionAtOfComplement F I J n f x)
  证明: by
  rw [← contMDiffOn_writtenInExtend_iff h.domChart_mem_maximalAtlas
    h.codChart_mem_maximalAtlas le_rfl h.mapsto_domChart_source_codChart_source]; rw [← h.domChart.extend_target_eq_image_source]
  have : CMDiff n (Prod.fst ∘ h.equiv) := by rw [contMDiff_iff_contDiff]; fun_prop
  exact this.con

Depends on / 依赖: CMDiff, Prod.fst, codChart_mem_maximalAtlas, contMDiffOn, contMDiffOn_writtenInExtend_iff, contMDiff_iff_contDiff, domChart, domChart_mem_maximalAtlas, extend_target_eq_image_source, fun_prop, h.codChart_mem_maximalAtlas, h.domChart.extend_target_eq_image_source, h.domChart_mem_maximalAtlas, h.equiv, h.mapsto_domChart_source_codChart_source, h.writtenInCharts, le_rfl, mapsto_domChart_source_codChart_source, this.contMDiffOn.congr, writtenInCharts
-/
theorem contMDiffOn (h : IsSubmersionAtOfComplement F I J n f x) :
    ContMDiffOn I J n f h.domChart.source := by
  rw [← contMDiffOn_writtenInExtend_iff h.domChart_mem_maximalAtlas
    h.codChart_mem_maximalAtlas le_rfl h.mapsto_domChart_source_codChart_source]; rw [← h.domChart.extend_target_eq_image_source]
  have : CMDiff n (Prod.fst ∘ h.equiv) := by rw [contMDiff_iff_contDiff]; fun_prop
  exact this.contMDiffOn.congr h.writtenInCharts

/--
theorem `contMDiffAt` / 定理 `contMDiffAt`

English:
theorem contMDiffAt
  given: (h : IsSubmersionAtOfComplement F I J n f x)
  statement: CMDiffAt n f x
  proof: h.contMDiffOn.contMDiffAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

中文:
定理 contMDiffAt
  条件: (h : IsSubmersionAtOfComplement F I J n f x)
  结论: CMDiffAt n f x
  证明: h.contMDiffOn.contMDiffAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

Depends on / 依赖: contMDiffAt, contMDiffOn, domChart, h.contMDiffOn.contMDiffAt, h.domChart.open_source.mem_nhds, mem_domChart_source, mem_nhds, open_source
-/
theorem contMDiffAt (h : IsSubmersionAtOfComplement F I J n f x) : CMDiffAt n f x :=
  h.contMDiffOn.contMDiffAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

end IsSubmersionAtOfComplement

namespace IsSubmersionAt

/--
lemma `mk_of_charts` / 引理 `mk_of_charts`

English:
lemma mk_of_charts
  statement: (equiv : E ≃L[𝕜] (E'' × F))
  proof: by
  have aux : IsSubmersionAtOfComplement F I J n f x := by
    apply IsSubmersionAtOfComplement.mk_of_charts <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsSubmersionAtOfComplement.congr_F aux.smallEquiv]

中文:
引理 mk_of_charts
  结论: (equiv : E ≃L[𝕜] (E'' × F))
  证明: by
  have aux : IsSubmersionAtOfComplement F I J n f x := by
    apply IsSubmersionAtOfComplement.mk_of_charts <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsSubmersionAtOfComplement.congr_F aux.smallEquiv]

Depends on / 依赖: IsSubmersionAtOfComplement, IsSubmersionAtOfComplement.congr_F, IsSubmersionAtOfComplement.mk_of_charts, aux.smallComplement, aux.smallEquiv, congr_F, infer_instance, mk_of_charts, smallComplement, smallEquiv
-/
lemma mk_of_charts (equiv : E ≃L[𝕜] (E'' × F))
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x in domChart.source) (hfx : f x in codChart.source)
    (hdomChart : domChart in IsManifold.maximalAtlas I n M)
    (hcodChart : codChart in IsManifold.maximalAtlas J n N)
    (hsource : domChart.source subseteq f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAt I J n f x := by
  have aux : IsSubmersionAtOfComplement F I J n f x := by
    apply IsSubmersionAtOfComplement.mk_of_charts <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsSubmersionAtOfComplement.congr_F aux.smallEquiv]

/--
lemma `mk_of_continuousAt` / 引理 `mk_of_continuousAt`

English:
lemma mk_of_continuousAt
  statement: {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : E ≃L[𝕜] (E'' × F))
  proof: by
  have aux : IsSubmersionAtOfComplement F I J n f x := by
    apply IsSubmersionAtOfComplement.mk_of_continuousAt <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsSubmersionAtOfComplement.congr_F aux.smallEquiv]

中文:
引理 mk_of_continuousAt
  结论: {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : E ≃L[𝕜] (E'' × F))
  证明: by
  have aux : IsSubmersionAtOfComplement F I J n f x := by
    apply IsSubmersionAtOfComplement.mk_of_continuousAt <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsSubmersionAtOfComplement.congr_F aux.smallEquiv]

Depends on / 依赖: IsSubmersionAtOfComplement, IsSubmersionAtOfComplement.congr_F, IsSubmersionAtOfComplement.mk_of_continuousAt, aux.smallComplement, aux.smallEquiv, congr_F, infer_instance, mk_of_continuousAt, smallComplement, smallEquiv
-/
lemma mk_of_continuousAt {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : E ≃L[𝕜] (E'' × F))
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x in domChart.source) (hfx : f x in codChart.source)
    (hdomChart : domChart in IsManifold.maximalAtlas I n M)
    (hcodChart : codChart in IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAt I J n f x := by
  have aux : IsSubmersionAtOfComplement F I J n f x := by
    apply IsSubmersionAtOfComplement.mk_of_continuousAt <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsSubmersionAtOfComplement.congr_F aux.smallEquiv]

/--
Definition of `complement` / `complement` 的定义

English:
definition complement
  signature: (h : IsSubmersionAt I J n f x)
  body: Classical.choose h

中文:
定义 complement
  签名: (h : IsSubmersionAt I J n f x)
  定义体: Classical.choose h

Depends on / 依赖: Classical, Classical.choose
-/
def complement (h : IsSubmersionAt I J n f x) : Type u := Classical.choose h

@[no_expose] instance (h : IsSubmersionAt I J n f x) : NormedAddCommGroup h.complement :=
  Classical.choose (Classical.choose_spec h)

@[no_expose] instance (h : IsSubmersionAt I J n f x) : NormedSpace 𝕜 h.complement :=
Classical.choose Classical.choose_spec Classical.choose_spec h

/--
lemma `isSubmersionAtOfComplement_complement` / 引理 `isSubmersionAtOfComplement_complement`

English:
lemma isSubmersionAtOfComplement_complement
  given: (h : IsSubmersionAt I J n f x)
  proof: Classical.choose_spec Classical.choose_spec Classical.choose_spec h

中文:
引理 isSubmersionAtOfComplement_complement
  条件: (h : IsSubmersionAt I J n f x)
  证明: Classical.choose_spec Classical.choose_spec Classical.choose_spec h

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
lemma isSubmersionAtOfComplement_complement (h : IsSubmersionAt I J n f x) :
    IsSubmersionAtOfComplement h.complement I J n f x :=
Classical.choose_spec Classical.choose_spec Classical.choose_spec h

/--
Definition of `domChart` / `domChart` 的定义

English:
definition domChart
  signature: (h : IsSubmersionAt I J n f x)
  body: h.isSubmersionAtOfComplement_complement.domChart

中文:
定义 domChart
  签名: (h : IsSubmersionAt I J n f x)
  定义体: h.isSubmersionAtOfComplement_complement.domChart

Depends on / 依赖: domChart, h.isSubmersionAtOfComplement_complement.domChart, isSubmersionAtOfComplement_complement
-/
def domChart (h : IsSubmersionAt I J n f x) : OpenPartialHomeomorph M H :=
  h.isSubmersionAtOfComplement_complement.domChart

/--
Definition of `codChart` / `codChart` 的定义

English:
definition codChart
  signature: (h : IsSubmersionAt I J n f x)
  body: h.isSubmersionAtOfComplement_complement.codChart

中文:
定义 codChart
  签名: (h : IsSubmersionAt I J n f x)
  定义体: h.isSubmersionAtOfComplement_complement.codChart

Depends on / 依赖: codChart, h.isSubmersionAtOfComplement_complement.codChart, isSubmersionAtOfComplement_complement
-/
def codChart (h : IsSubmersionAt I J n f x) : OpenPartialHomeomorph N G :=
  h.isSubmersionAtOfComplement_complement.codChart

/--
lemma `mem_domChart_source` / 引理 `mem_domChart_source`

English:
lemma mem_domChart_source
  given: (h : IsSubmersionAt I J n f x)
  statement: x in h.domChart.source
  proof: h.isSubmersionAtOfComplement_complement.mem_domChart_source

中文:
引理 mem_domChart_source
  条件: (h : IsSubmersionAt I J n f x)
  结论: x in h.domChart.source
  证明: h.isSubmersionAtOfComplement_complement.mem_domChart_source

Depends on / 依赖: h.isSubmersionAtOfComplement_complement.mem_domChart_source, isSubmersionAtOfComplement_complement, mem_domChart_source
-/
lemma mem_domChart_source (h : IsSubmersionAt I J n f x) : x in h.domChart.source :=
  h.isSubmersionAtOfComplement_complement.mem_domChart_source

/--
lemma `mem_codChart_source` / 引理 `mem_codChart_source`

English:
lemma mem_codChart_source
  given: (h : IsSubmersionAt I J n f x)
  statement: f x in h.codChart.source
  proof: h.isSubmersionAtOfComplement_complement.mem_codChart_source

中文:
引理 mem_codChart_source
  条件: (h : IsSubmersionAt I J n f x)
  结论: f x in h.codChart.source
  证明: h.isSubmersionAtOfComplement_complement.mem_codChart_source

Depends on / 依赖: h.isSubmersionAtOfComplement_complement.mem_codChart_source, isSubmersionAtOfComplement_complement, mem_codChart_source
-/
lemma mem_codChart_source (h : IsSubmersionAt I J n f x) : f x in h.codChart.source :=
  h.isSubmersionAtOfComplement_complement.mem_codChart_source

/--
lemma `domChart_mem_maximalAtlas` / 引理 `domChart_mem_maximalAtlas`

English:
lemma domChart_mem_maximalAtlas
  given: (h : IsSubmersionAt I J n f x)
  proof: h.isSubmersionAtOfComplement_complement.domChart_mem_maximalAtlas

中文:
引理 domChart_mem_maximalAtlas
  条件: (h : IsSubmersionAt I J n f x)
  证明: h.isSubmersionAtOfComplement_complement.domChart_mem_maximalAtlas

Depends on / 依赖: domChart_mem_maximalAtlas, h.isSubmersionAtOfComplement_complement.domChart_mem_maximalAtlas, isSubmersionAtOfComplement_complement
-/
lemma domChart_mem_maximalAtlas (h : IsSubmersionAt I J n f x) :
    h.domChart in IsManifold.maximalAtlas I n M :=
  h.isSubmersionAtOfComplement_complement.domChart_mem_maximalAtlas

/--
lemma `codChart_mem_maximalAtlas` / 引理 `codChart_mem_maximalAtlas`

English:
lemma codChart_mem_maximalAtlas
  given: (h : IsSubmersionAt I J n f x)
  proof: h.isSubmersionAtOfComplement_complement.codChart_mem_maximalAtlas

中文:
引理 codChart_mem_maximalAtlas
  条件: (h : IsSubmersionAt I J n f x)
  证明: h.isSubmersionAtOfComplement_complement.codChart_mem_maximalAtlas

Depends on / 依赖: codChart_mem_maximalAtlas, h.isSubmersionAtOfComplement_complement.codChart_mem_maximalAtlas, isSubmersionAtOfComplement_complement
-/
lemma codChart_mem_maximalAtlas (h : IsSubmersionAt I J n f x) :
    h.codChart in IsManifold.maximalAtlas J n N :=
  h.isSubmersionAtOfComplement_complement.codChart_mem_maximalAtlas

/--
lemma `source_subset_preimage_source` / 引理 `source_subset_preimage_source`

English:
lemma source_subset_preimage_source
  given: (h : IsSubmersionAt I J n f x)
  proof: h.isSubmersionAtOfComplement_complement.source_subset_preimage_source

中文:
引理 source_subset_preimage_source
  条件: (h : IsSubmersionAt I J n f x)
  证明: h.isSubmersionAtOfComplement_complement.source_subset_preimage_source

Depends on / 依赖: h.isSubmersionAtOfComplement_complement.source_subset_preimage_source, isSubmersionAtOfComplement_complement, source_subset_preimage_source
-/
lemma source_subset_preimage_source (h : IsSubmersionAt I J n f x) :
    h.domChart.source subseteq f ⁻¹' h.codChart.source :=
  h.isSubmersionAtOfComplement_complement.source_subset_preimage_source

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: (h : IsSubmersionAt I J n f x)
  body: h.isSubmersionAtOfComplement_complement.equiv

中文:
定义 equiv
  签名: (h : IsSubmersionAt I J n f x)
  定义体: h.isSubmersionAtOfComplement_complement.equiv

Depends on / 依赖: h.isSubmersionAtOfComplement_complement.equiv, isSubmersionAtOfComplement_complement
-/
def equiv (h : IsSubmersionAt I J n f x) : E ≃L[𝕜] (E'' × h.complement) :=
  h.isSubmersionAtOfComplement_complement.equiv

/--
lemma `writtenInCharts` / 引理 `writtenInCharts`

English:
lemma writtenInCharts
  given: (h : IsSubmersionAt I J n f x)
  proof: h.isSubmersionAtOfComplement_complement.writtenInCharts

中文:
引理 writtenInCharts
  条件: (h : IsSubmersionAt I J n f x)
  证明: h.isSubmersionAtOfComplement_complement.writtenInCharts

Depends on / 依赖: h.isSubmersionAtOfComplement_complement.writtenInCharts, isSubmersionAtOfComplement_complement, writtenInCharts
-/
lemma writtenInCharts (h : IsSubmersionAt I J n f x) :
    EqOn ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (Prod.fst ∘ h.equiv)
      (h.domChart.extend I).target :=
  h.isSubmersionAtOfComplement_complement.writtenInCharts

/--
lemma `property` / 引理 `property`

English:
lemma property
  given: (h : IsSubmersionAt I J n f x)
  proof: h.isSubmersionAtOfComplement_complement.property

中文:
引理 property
  条件: (h : IsSubmersionAt I J n f x)
  证明: h.isSubmersionAtOfComplement_complement.property

Depends on / 依赖: h.isSubmersionAtOfComplement_complement.property, isSubmersionAtOfComplement_complement, property
-/
lemma property (h : IsSubmersionAt I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (SubmersionAtProp h.complement I J M N) :=
  h.isSubmersionAtOfComplement_complement.property

/--
lemma `image_target_subset_target` / 引理 `image_target_subset_target`

English:
lemma image_target_subset_target
  given: (h : IsSubmersionAt I J n f x)
  proof: h.isSubmersionAtOfComplement_complement.image_target_subset_target

中文:
引理 image_target_subset_target
  条件: (h : IsSubmersionAt I J n f x)
  证明: h.isSubmersionAtOfComplement_complement.image_target_subset_target

Depends on / 依赖: h.isSubmersionAtOfComplement_complement.image_target_subset_target, image_target_subset_target, isSubmersionAtOfComplement_complement
-/
lemma image_target_subset_target (h : IsSubmersionAt I J n f x) :
    (Prod.fst ∘ h.equiv) '' (h.domChart.extend I).target subseteq (h.codChart.extend J).target :=
  h.isSubmersionAtOfComplement_complement.image_target_subset_target

/--
lemma `target_subset_preimage_target` / 引理 `target_subset_preimage_target`

English:
lemma target_subset_preimage_target
  given: (h : IsSubmersionAt I J n f x)
  proof: fun _x hx => h.image_target_subset_target (mem_image_of_mem _ hx)

中文:
引理 target_subset_preimage_target
  条件: (h : IsSubmersionAt I J n f x)
  证明: fun _x hx => h.image_target_subset_target (mem_image_of_mem _ hx)

Depends on / 依赖: h.image_target_subset_target, image_target_subset_target, mem_image_of_mem
-/
lemma target_subset_preimage_target (h : IsSubmersionAt I J n f x) :
    (h.domChart.extend I).target subseteq (Prod.fst ∘ h.equiv) ⁻¹' (h.codChart.extend J).target :=
  fun _x hx => h.image_target_subset_target (mem_image_of_mem _ hx)

/--
lemma `congr_of_eventuallyEq` / 引理 `congr_of_eventuallyEq`

English:
lemma congr_of_eventuallyEq
  given: (hf : IsSubmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g)
  proof: by
  use hf.complement, by infer_instance, by infer_instance
  exact hf.isSubmersionAtOfComplement_complement.congr_of_eventuallyEq hfg

中文:
引理 congr_of_eventuallyEq
  条件: (hf : IsSubmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g)
  证明: by
  use hf.complement, by infer_instance, by infer_instance
  exact hf.isSubmersionAtOfComplement_complement.congr_of_eventuallyEq hfg

Depends on / 依赖: complement, congr_of_eventuallyEq, hf.complement, hf.isSubmersionAtOfComplement_complement.congr_of_eventuallyEq, infer_instance, isSubmersionAtOfComplement_complement
-/
lemma congr_of_eventuallyEq (hf : IsSubmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsSubmersionAt I J n g x := by
  use hf.complement, by infer_instance, by infer_instance
  exact hf.isSubmersionAtOfComplement_complement.congr_of_eventuallyEq hfg

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
    IsSubmersionAt I J n f x ↔ IsSubmersionAt I J n g x :=
  ⟨fun h => h.congr_of_eventuallyEq hfg, fun h => h.congr_of_eventuallyEq hfg.symm⟩

/--
lemma `_root_.isOpen_isSubmersionAt` / 引理 `_root_.isOpen_isSubmersionAt`

English:
lemma _root_.isOpen_isSubmersionAt
  proof: by
  rw [isOpen_iff_forall_mem_open]
  exact fun x hx => ⟨{x | IsSubmersionAtOfComplement hx.complement I J n f x },
    fun y hy => hy.isSubmersionAt,
    isOpen_isSubmersionAtOfComplement, by simp [hx.isSubmersionAtOfComplement_complement]⟩

中文:
引理 _root_.isOpen_isSubmersionAt
  证明: by
  rw [isOpen_iff_forall_mem_open]
  exact fun x hx => ⟨{x | IsSubmersionAtOfComplement hx.complement I J n f x },
    fun y hy => hy.isSubmersionAt,
    isOpen_isSubmersionAtOfComplement, by simp [hx.isSubmersionAtOfComplement_complement]⟩

Depends on / 依赖: IsSubmersionAtOfComplement, complement, hx.complement, hx.isSubmersionAtOfComplement_complement, hy.isSubmersionAt, isOpen_iff_forall_mem_open, isOpen_isSubmersionAtOfComplement, isSubmersionAt, isSubmersionAtOfComplement_complement
-/
lemma _root_.isOpen_isSubmersionAt :
    IsOpen {x | IsSubmersionAt I J n f x} := by
  rw [isOpen_iff_forall_mem_open]
  exact fun x hx => ⟨{x | IsSubmersionAtOfComplement hx.complement I J n f x },
    fun y hy => hy.isSubmersionAt,
    isOpen_isSubmersionAtOfComplement, by simp [hx.isSubmersionAtOfComplement_complement]⟩

/--
theorem `prodMap` / 定理 `prodMap`

English:
theorem prodMap
  statement: {f : M -> N} {g : M' -> N'} {x' : M'}
  proof: hf.isSubmersionAtOfComplement_complement.prodMap hg.isSubmersionAtOfComplement_complement
.isSubmersionAt

中文:
定理 prodMap
  结论: {f : M -> N} {g : M' -> N'} {x' : M'}
  证明: hf.isSubmersionAtOfComplement_complement.prodMap hg.isSubmersionAtOfComplement_complement
.isSubmersionAt

Depends on / 依赖: hf.isSubmersionAtOfComplement_complement.prodMap, hg.isSubmersionAtOfComplement_complement, isSubmersionAt, isSubmersionAtOfComplement_complement, prodMap
-/
theorem prodMap {f : M -> N} {g : M' -> N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersionAt I J n f x) (hg : IsSubmersionAt I' J' n g x') :
    IsSubmersionAt (I.prod I') (J.prod J') n (Prod.map f g) (x, x') :=
  hf.isSubmersionAtOfComplement_complement.prodMap hg.isSubmersionAtOfComplement_complement
.isSubmersionAt

/--
theorem `contMDiffOn` / 定理 `contMDiffOn`

English:
theorem contMDiffOn
  given: (h : IsSubmersionAt I J n f x)
  statement: CMDiff[h.domChart.source] n f
  proof: h.isSubmersionAtOfComplement_complement.contMDiffOn

中文:
定理 contMDiffOn
  条件: (h : IsSubmersionAt I J n f x)
  结论: CMDiff[h.domChart.source] n f
  证明: h.isSubmersionAtOfComplement_complement.contMDiffOn

Depends on / 依赖: contMDiffOn, h.isSubmersionAtOfComplement_complement.contMDiffOn, isSubmersionAtOfComplement_complement
-/
theorem contMDiffOn (h : IsSubmersionAt I J n f x) : CMDiff[h.domChart.source] n f :=
  h.isSubmersionAtOfComplement_complement.contMDiffOn

/--
theorem `contMDiffAt` / 定理 `contMDiffAt`

English:
theorem contMDiffAt
  given: (h : IsSubmersionAt I J n f x)
  statement: CMDiffAt n f x
  proof: h.isSubmersionAtOfComplement_complement.contMDiffAt

中文:
定理 contMDiffAt
  条件: (h : IsSubmersionAt I J n f x)
  结论: CMDiffAt n f x
  证明: h.isSubmersionAtOfComplement_complement.contMDiffAt

Depends on / 依赖: contMDiffAt, h.isSubmersionAtOfComplement_complement.contMDiffAt, isSubmersionAtOfComplement_complement
-/
theorem contMDiffAt (h : IsSubmersionAt I J n f x) : CMDiffAt n f x :=
  h.isSubmersionAtOfComplement_complement.contMDiffAt

end IsSubmersionAt

variable (F I J n) in
/--
Definition of `IsSubmersionOfComplement` / `IsSubmersionOfComplement` 的定义

English:
definition IsSubmersionOfComplement
  signature: (f : M -> N)
  body: forall x, IsSubmersionAtOfComplement F I J n f x

中文:
定义 IsSubmersionOfComplement
  签名: (f : M -> N)
  定义体: forall x, IsSubmersionAtOfComplement F I J n f x

Depends on / 依赖: IsSubmersionAtOfComplement
-/
def IsSubmersionOfComplement (f : M -> N) : Prop := forall x, IsSubmersionAtOfComplement F I J n f x

variable (I J n) in
/--
Definition of `IsSubmersion` / `IsSubmersion` 的定义

English:
definition IsSubmersion
  signature: (f : M -> N)
  body: exists (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsSubmersionOfComplement F I J n f

中文:
定义 IsSubmersion
  签名: (f : M -> N)
  定义体: exists (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsSubmersionOfComplement F I J n f

Depends on / 依赖: IsSubmersionOfComplement, NormedAddCommGroup, NormedSpace
-/
def IsSubmersion (f : M -> N) : Prop :=
  exists (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsSubmersionOfComplement F I J n f

namespace IsSubmersionOfComplement

variable {f g : M -> N}

/--
lemma `isSubmersionAt` / 引理 `isSubmersionAt`

English:
lemma isSubmersionAt
  given: (h : IsSubmersionOfComplement F I J n f) (x : M)
  proof: h x

中文:
引理 isSubmersionAt
  条件: (h : IsSubmersionOfComplement F I J n f) (x : M)
  证明: h x
-/
lemma isSubmersionAt (h : IsSubmersionOfComplement F I J n f) (x : M) :
    IsSubmersionAtOfComplement F I J n f x := h x

/--
lemma `trans_F` / 引理 `trans_F`

English:
lemma trans_F
  given: (h : IsSubmersionOfComplement F I J n f) (e : F ≃L[𝕜] F')
  proof: fun x => (h x).trans_F e

中文:
引理 trans_F
  条件: (h : IsSubmersionOfComplement F I J n f) (e : F ≃L[𝕜] F')
  证明: fun x => (h x).trans_F e

Depends on / 依赖: trans_F
-/
lemma trans_F (h : IsSubmersionOfComplement F I J n f) (e : F ≃L[𝕜] F') :
    IsSubmersionOfComplement F' I J n f :=
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
    IsSubmersionOfComplement F I J n f ↔ IsSubmersionOfComplement F' I J n f :=
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
    (h : IsSubmersionOfComplement F I J n f) (h' : IsSubmersionOfComplement F' I' J' n g) :
    IsSubmersionOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) :=
  fun ⟨x, x'⟩ => (h x).prodMap (h' x')

/--
lemma `isSubmersion` / 引理 `isSubmersion`

English:
lemma isSubmersion
  given: (h : IsSubmersionOfComplement F I J n f)
  statement: IsSubmersion I J n f
  proof: by
  by_cases! hM : IsEmpty M
  · rw [IsSubmersion]
    use PUnit, by infer_instance, by infer_instance
    exact fun x => (IsEmpty.false x).elim
  inhabit M
  let x : M := Inhabited.default
  use (h x).smallComplement, by infer_instance, by infer_instance
  exact (IsSubmersionOfComplement.congr_F (

中文:
引理 isSubmersion
  条件: (h : IsSubmersionOfComplement F I J n f)
  结论: IsSubmersion I J n f
  证明: by
  by_cases! hM : IsEmpty M
  · rw [IsSubmersion]
    use PUnit, by infer_instance, by infer_instance
    exact fun x => (IsEmpty.false x).elim
  inhabit M
  let x : M := Inhabited.default
  use (h x).smallComplement, by infer_instance, by infer_instance
  exact (IsSubmersionOfComplement.congr_F (

Depends on / 依赖: Inhabited, Inhabited.default, IsEmpty, IsEmpty.false, IsSubmersion, IsSubmersionOfComplement, IsSubmersionOfComplement.congr_F, congr_F, infer_instance, inhabit, smallComplement, smallEquiv
-/
lemma isSubmersion (h : IsSubmersionOfComplement F I J n f) : IsSubmersion I J n f := by
  by_cases! hM : IsEmpty M
  · rw [IsSubmersion]
    use PUnit, by infer_instance, by infer_instance
    exact fun x => (IsEmpty.false x).elim
  inhabit M
  let x : M := Inhabited.default
  use (h x).smallComplement, by infer_instance, by infer_instance
  exact (IsSubmersionOfComplement.congr_F (h x).smallEquiv).mp h

open IsManifold in
/--
lemma `id` / 引理 `id`

English:
lemma id
  given: [IsManifold I n M]
  statement: IsSubmersionOfComplement PUnit I I n (@id M)
  proof: by
  intro x
  apply IsSubmersionAtOfComplement.mk_of_continuousAt (continuousAt_id)
    (ContinuousLinearEquiv.prodUnique 𝕜 E PUnit).symm
    (chartAt H x) (chartAt H x) (mem_chart_source H x) (mem_chart_source H x)
    (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas x)
  intro y hy
  have : I (

中文:
引理 id
  条件: [是流形 I n M]
  结论: IsSubmersionOfComplement 命题单元 I I n (@id M)
  证明: by
  intro x
  apply IsSubmersionAtOfComplement.mk_of_continuousAt (continuousAt_id)
    (ContinuousLinearEquiv.prodUnique 𝕜 E PUnit).symm
    (chartAt H x) (chartAt H x) (mem_chart_source H x) (mem_chart_source H x)
    (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas x)
  intro y hy
  have : I (
-/
protected lemma id [IsManifold I n M] : IsSubmersionOfComplement PUnit I I n (@id M) := by
  intro x
  apply IsSubmersionAtOfComplement.mk_of_continuousAt (continuousAt_id)
    (ContinuousLinearEquiv.prodUnique 𝕜 E PUnit).symm
    (chartAt H x) (chartAt H x) (mem_chart_source H x) (mem_chart_source H x)
    (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas x)
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all)]; rw [I.right_inv (by simp_all)]
  simpa

/--
theorem `contMDiff` / 定理 `contMDiff`

English:
theorem contMDiff
  given: (h : IsSubmersionOfComplement F I J n f)
  statement: CMDiff n f
  proof: fun x => (h x).contMDiffAt

中文:
定理 contMDiff
  条件: (h : IsSubmersionOfComplement F I J n f)
  结论: CMDiff n f
  证明: fun x => (h x).contMDiffAt

Depends on / 依赖: contMDiffAt
-/
theorem contMDiff (h : IsSubmersionOfComplement F I J n f) : CMDiff n f :=
  fun x => (h x).contMDiffAt

end IsSubmersionOfComplement

namespace IsSubmersion

variable {f g : M -> N}

/--
Definition of `complement` / `complement` 的定义

English:
definition complement
  signature: (h : IsSubmersion I J n f)
  body: Classical.choose h

中文:
定义 complement
  签名: (h : IsSubmersion I J n f)
  定义体: Classical.choose h

Depends on / 依赖: Classical, Classical.choose
-/
def complement (h : IsSubmersion I J n f) : Type u := Classical.choose h

@[no_expose] instance (h : IsSubmersion I J n f) : NormedAddCommGroup h.complement :=
Classical.choose Classical.choose_spec h

@[no_expose] instance (h : IsSubmersion I J n f) : NormedSpace 𝕜 h.complement :=
Classical.choose Classical.choose_spec Classical.choose_spec h

/--
lemma `isSubmersionOfComplement_complement` / 引理 `isSubmersionOfComplement_complement`

English:
lemma isSubmersionOfComplement_complement
  given: (h : IsSubmersion I J n f)
  proof: Classical.choose_spec Classical.choose_spec Classical.choose_spec h

中文:
引理 isSubmersionOfComplement_complement
  条件: (h : IsSubmersion I J n f)
  证明: Classical.choose_spec Classical.choose_spec Classical.choose_spec h

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
lemma isSubmersionOfComplement_complement (h : IsSubmersion I J n f) :
    IsSubmersionOfComplement h.complement I J n f :=
Classical.choose_spec Classical.choose_spec Classical.choose_spec h

/--
lemma `isSubmersionAt` / 引理 `isSubmersionAt`

English:
lemma isSubmersionAt
  given: (h : IsSubmersion I J n f) (x : M)
  statement: IsSubmersionAt I J n f x
  proof: by
  rw [IsSubmersionAt]
  use h.complement, by infer_instance, by infer_instance
  exact h.isSubmersionOfComplement_complement x

中文:
引理 isSubmersionAt
  条件: (h : IsSubmersion I J n f) (x : M)
  结论: IsSubmersionAt I J n f x
  证明: by
  rw [IsSubmersionAt]
  use h.complement, by infer_instance, by infer_instance
  exact h.isSubmersionOfComplement_complement x

Depends on / 依赖: IsSubmersionAt, complement, h.complement, h.isSubmersionOfComplement_complement, infer_instance, isSubmersionOfComplement_complement
-/
lemma isSubmersionAt (h : IsSubmersion I J n f) (x : M) : IsSubmersionAt I J n f x := by
  rw [IsSubmersionAt]
  use h.complement, by infer_instance, by infer_instance
  exact h.isSubmersionOfComplement_complement x

/--
theorem `prodMap` / 定理 `prodMap`

English:
theorem prodMap
  statement: {f : M -> N} {g : M' -> N'}
  proof: (hf.isSubmersionOfComplement_complement.prodMap
    hg.isSubmersionOfComplement_complement ).isSubmersion

中文:
定理 prodMap
  结论: {f : M -> N} {g : M' -> N'}
  证明: (hf.isSubmersionOfComplement_complement.prodMap
    hg.isSubmersionOfComplement_complement ).isSubmersion

Depends on / 依赖: hf.isSubmersionOfComplement_complement.prodMap, hg.isSubmersionOfComplement_complement, isSubmersion, isSubmersionOfComplement_complement, prodMap
-/
theorem prodMap {f : M -> N} {g : M' -> N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersion I J n f) (hg : IsSubmersion I' J' n g) :
    IsSubmersion (I.prod I') (J.prod J') n (Prod.map f g) :=
  (hf.isSubmersionOfComplement_complement.prodMap
    hg.isSubmersionOfComplement_complement ).isSubmersion

/--
lemma `id` / 引理 `id`

English:
lemma id
  given: [IsManifold I n M]
  statement: IsSubmersion I I n (@id M)
  proof: by
  use PUnit, by infer_instance, by infer_instance
  exact IsSubmersionOfComplement.id

中文:
引理 id
  条件: [是流形 I n M]
  结论: IsSubmersion I I n (@id M)
  证明: by
  use PUnit, by infer_instance, by infer_instance
  exact IsSubmersionOfComplement.id
-/
protected lemma id [IsManifold I n M] : IsSubmersion I I n (@id M) := by
  use PUnit, by infer_instance, by infer_instance
  exact IsSubmersionOfComplement.id

/--
theorem `contMDiff` / 定理 `contMDiff`

English:
theorem contMDiff
  given: (h : IsSubmersion I J n f)
  statement: CMDiff n f
  proof: h.isSubmersionOfComplement_complement.contMDiff

中文:
定理 contMDiff
  条件: (h : IsSubmersion I J n f)
  结论: CMDiff n f
  证明: h.isSubmersionOfComplement_complement.contMDiff

Depends on / 依赖: contMDiff, h.isSubmersionOfComplement_complement.contMDiff, isSubmersionOfComplement_complement
-/
theorem contMDiff (h : IsSubmersion I J n f) : CMDiff n f :=
  h.isSubmersionOfComplement_complement.contMDiff

end IsSubmersion

end Manifold
