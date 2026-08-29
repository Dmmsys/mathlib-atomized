/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Extended charts in smooth manifolds

In a `C^n` manifold with corners with the model `I` on `(E, H)`, the charts take values in the
model space `H`. However, we also need to use extended charts taking values in the model vector
space `E`. These extended charts are not `OpenPartialHomeomorph` as the target is not open in `E`
in general, but we can still register them as `PartialEquiv`s.

## Main definitions

* `OpenPartialHomeomorph.extend`: compose an open partial homeomorphism into `H` with the model `I`,
  to obtain a `PartialEquiv` into `E`. Extended charts are an example of this.
* `extChartAt I x`: the extended chart at `x`, obtained by composing the `chartAt H x` with `I`.
  Since the target is in general not open, this is not an open partial homeomorphism in general, but
  we register them as `PartialEquiv`s.
* `I.extendCoordChange e e'`: the change of extended charts `(e.extend I).symm ≫ e'.extend I`.

## Main results

* `ModelWithCorners.contDiffOn_extendCoordChange`: if `f` and `f'` lie in the maximal atlas on `M`,
  `I.extendCoordChange f f'` is Cⁿ on its source

* `contDiffOn_ext_coord_change`: for `x x' : M`, the coordinate change
  `(extChartAt I x').symm ≫ extChartAt I x` is continuous on its source

* `Manifold.locallyCompact_of_finiteDimensional`: a finite-dimensional manifold
  modelled on a locally compact field (such as ℝ, ℂ or the `p`-adic numbers) is locally compact
* `LocallyCompactSpace.of_locallyCompact_manifold`: a locally compact manifold must be modelled
  on a locally compact space.
* `FiniteDimensional.of_locallyCompact_manifold`: a locally compact manifold must be modelled
  on a finite-dimensional space

## Implementation notes

This file uses the name `writtenInExtend` (in analogy to `writtenInExtChart`) to refer to a
composition `ψ.extend J ∘ f ∘ φ.extend I` of `f : M → N` with charts `ψ` and `φ` extended by the
appropriate models with corners. This is not a definition, so technically deviating from the naming
convention.

TODO: this file uses more made-up names; document these as well

-/

@[expose] public section

noncomputable section

open Set Filter Function
open scoped Manifold Topology

variable {𝕜 E M H E' M' H' : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M] {n : WithTop Nat∞}
  (f f' : OpenPartialHomeomorph M H)
  {I : ModelWithCorners 𝕜 E H} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  [TopologicalSpace M'] {I' : ModelWithCorners 𝕜 E' H'} {s t : Set M}

section ExtendedCharts

namespace OpenPartialHomeomorph

variable (I) in
/-- Given a chart `f` on a manifold with corners, `f.extend I` is the extended chart to the model
vector space. -/
@[simp, mfld_simps]
/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: : PartialEquiv M E
  body: f.toPartialEquiv ≫ I.toPartialEquiv

中文:
定义 extend
  签名: : 部分等价 M E
  定义体: f.toPartialEquiv ≫ I.toPartialEquiv

Depends on / 依赖: I.toPartialEquiv, f.toPartialEquiv, toPartialEquiv
-/
def extend : PartialEquiv M E :=
  f.toPartialEquiv ≫ I.toPartialEquiv

/--
theorem `extend_coe` / 定理 `extend_coe`

English:
theorem extend_coe
  statement: ⇑(f.extend I) = I ∘ f
  proof: rfl

中文:
定理 extend_coe
  结论: ⇑(f.extend I) = I ∘ f
  证明: rfl
-/
theorem extend_coe : ⇑(f.extend I) = I ∘ f :=
  rfl

/--
theorem `extend_coe_symm` / 定理 `extend_coe_symm`

English:
theorem extend_coe_symm
  statement: ⇑(f.extend I).symm = f.symm ∘ I.symm
  proof: rfl

中文:
定理 extend_coe_symm
  结论: ⇑(f.extend I).symm = f.symm ∘ I.symm
  证明: rfl

Depends on / 依赖: Finite, IsReflexive, IsReflexive.of_finite_of_free, Module, Module.Finite, of_finite_of_free
-/
theorem extend_coe_symm : ⇑(f.extend I).symm = f.symm ∘ I.symm :=
  rfl

/--
theorem `extend_source` / 定理 `extend_source`

English:
theorem extend_source
  statement: (f.extend I).source = f.source
  proof: by
  rw [extend]; rw [PartialEquiv.trans_source]; rw [I.source_eq]; rw [preimage_univ]; rw [inter_univ]

中文:
定理 extend_source
  结论: (f.extend I).source = f.source
  证明: by
  rw [extend]; rw [PartialEquiv.trans_source]; rw [I.source_eq]; rw [preimage_univ]; rw [inter_univ]

Depends on / 依赖: Finite, I.source_eq, IsReflexive, Module, Module.Finite, PartialEquiv, PartialEquiv.trans_source, Projective, extend, inter_univ, preimage_univ, source_eq, trans_source
-/
theorem extend_source : (f.extend I).source = f.source := by
  rw [extend]; rw [PartialEquiv.trans_source]; rw [I.source_eq]; rw [preimage_univ]; rw [inter_univ]

/--
theorem `isOpen_extend_source` / 定理 `isOpen_extend_source`

English:
theorem isOpen_extend_source
  statement: IsOpen (f.extend I).source
  proof: by
  rw [extend_source]
  exact f.open_source

中文:
定理 isOpen_extend_source
  结论: 是开集 (f.extend I).source
  证明: by
  rw [extend_source]
  exact f.open_source

Depends on / 依赖: extend_source, f.open_source, open_source
-/
theorem isOpen_extend_source : IsOpen (f.extend I).source := by
  rw [extend_source]
  exact f.open_source

/--
theorem `extend_target` / 定理 `extend_target`

English:
theorem extend_target
  statement: (f.extend I).target = I.symm ⁻¹' f.target inter range I
  proof: by
  simp_rw [extend, PartialEquiv.trans_target, I.target_eq, I.toPartialEquiv_coe_symm, inter_comm]

中文:
定理 extend_target
  结论: (f.extend I).target = I.symm ⁻¹' f.target inter range I
  证明: by
  simp_rw [extend, PartialEquiv.trans_target, I.target_eq, I.toPartialEquiv_coe_symm, inter_comm]

Depends on / 依赖: I.target_eq, I.toPartialEquiv_coe_symm, PartialEquiv, PartialEquiv.trans_target, extend, inter_comm, simp_rw, target_eq, toPartialEquiv_coe_symm, trans_target
-/
theorem extend_target : (f.extend I).target = I.symm ⁻¹' f.target inter range I := by
  simp_rw [extend, PartialEquiv.trans_target, I.target_eq, I.toPartialEquiv_coe_symm, inter_comm]

/--
theorem `extend_target'` / 定理 `extend_target'`

English:
theorem extend_target'
  statement: (f.extend I).target = I '' f.target
  proof: by
  rw [extend]; rw [PartialEquiv.trans_target'']; rw [I.source_eq]; rw [univ_inter]; rw [I.toPartialEquiv_coe]

中文:
定理 extend_target'
  结论: (f.extend I).target = I '' f.target
  证明: by
  rw [extend]; rw [PartialEquiv.trans_target'']; rw [I.source_eq]; rw [univ_inter]; rw [I.toPartialEquiv_coe]

Depends on / 依赖: I.source_eq, I.toPartialEquiv_coe, PartialEquiv, PartialEquiv.trans_target, extend, instFiniteDimensionalOfIsReflexive, source_eq, toPartialEquiv_coe, trans_target, univ_inter
-/
theorem extend_target' : (f.extend I).target = I '' f.target := by
  rw [extend]; rw [PartialEquiv.trans_target'']; rw [I.source_eq]; rw [univ_inter]; rw [I.toPartialEquiv_coe]

/--
theorem `extend_target_eq_image_source` / 定理 `extend_target_eq_image_source`

English:
theorem extend_target_eq_image_source
  statement: (f.extend I).target = (f.extend I) '' f.source
  proof: by
  rw [f.extend_target']; rw [← f.image_source_eq_target]; rw [← image_comp]; rw [f.extend_coe]

中文:
定理 extend_target_eq_image_source
  结论: (f.extend I).target = (f.extend I) '' f.source
  证明: by
  rw [f.extend_target']; rw [← f.image_source_eq_target]; rw [← image_comp]; rw [f.extend_coe]

Depends on / 依赖: extend_coe, extend_target, f.extend_coe, f.extend_target, f.image_source_eq_target, image_comp, image_source_eq_target
-/
theorem extend_target_eq_image_source : (f.extend I).target = (f.extend I) '' f.source := by
  rw [f.extend_target']; rw [← f.image_source_eq_target]; rw [← image_comp]; rw [f.extend_coe]

/--
lemma `isOpen_extend_target` / 引理 `isOpen_extend_target`

English:
lemma isOpen_extend_target
  given: [I.Boundaryless]
  statement: IsOpen (f.extend I).target
  proof: by
  rw [extend_target]; rw [I.range_eq_univ]; rw [inter_univ]
  exact I.continuous_symm.isOpen_preimage _ f.open_target

中文:
引理 isOpen_extend_target
  条件: [I.无边界]
  结论: 是开集 (f.extend I).target
  证明: by
  rw [extend_target]; rw [I.range_eq_univ]; rw [inter_univ]
  exact I.continuous_symm.isOpen_preimage _ f.open_target

Depends on / 依赖: I.continuous_symm.isOpen_preimage, I.range_eq_univ, continuous_symm, extend_target, f.open_target, inter_univ, isOpen_preimage, open_target, range_eq_univ
-/
lemma isOpen_extend_target [I.Boundaryless] : IsOpen (f.extend I).target := by
  rw [extend_target]; rw [I.range_eq_univ]; rw [inter_univ]
  exact I.continuous_symm.isOpen_preimage _ f.open_target

/--
theorem `mapsTo_extend` / 定理 `mapsTo_extend`

English:
theorem mapsTo_extend
  given: (hs : s subseteq f.source)
  proof: by
  rw [mapsTo_iff_image_subset]; rw [extend_coe]; rw [extend_coe_symm]; rw [preimage_comp]; rw [← I.image_eq]; rw [image_comp]; rw [f.image_eq_target_inter_inv_preimage hs]
  exact image_mono inter_subset_right

中文:
定理 mapsTo_extend
  条件: (hs : s subseteq f.source)
  证明: by
  rw [mapsTo_iff_image_subset]; rw [extend_coe]; rw [extend_coe_symm]; rw [preimage_comp]; rw [← I.image_eq]; rw [image_comp]; rw [f.image_eq_target_inter_inv_preimage hs]
  exact image_mono inter_subset_right

Depends on / 依赖: I.image_eq, extend_coe, extend_coe_symm, f.image_eq_target_inter_inv_preimage, image_comp, image_eq, image_eq_target_inter_inv_preimage, image_mono, inter_subset_right, mapsTo_iff_image_subset, preimage_comp
-/
theorem mapsTo_extend (hs : s subseteq f.source) :
    MapsTo (f.extend I) s ((f.extend I).symm ⁻¹' s inter range I) := by
  rw [mapsTo_iff_image_subset]; rw [extend_coe]; rw [extend_coe_symm]; rw [preimage_comp]; rw [← I.image_eq]; rw [image_comp]; rw [f.image_eq_target_inter_inv_preimage hs]
  exact image_mono inter_subset_right

/--
theorem `extend_left_inv` / 定理 `extend_left_inv`

English:
theorem extend_left_inv
  given: {x : M} (hxf : x in f.source)
  statement: (f.extend I).symm (f.extend I x) = x
  proof: (f.extend I).left_inv by rwa [f.extend_source]

中文:
定理 extend_left_inv
  条件: {x : M} (hxf : x in f.source)
  结论: (f.extend I).symm (f.extend I x) = x
  证明: (f.extend I).left_inv by rwa [f.extend_source]

Depends on / 依赖: extend, extend_source, f.extend, f.extend_source, left_inv
-/
theorem extend_left_inv {x : M} (hxf : x in f.source) : (f.extend I).symm (f.extend I x) = x :=
(f.extend I).left_inv by rwa [f.extend_source]

/--
lemma `extend_left_inv'` / 引理 `extend_left_inv'`

English:
lemma extend_left_inv'
  given: (ht : t subseteq f.source)
  statement: ((f.extend I).symm ∘ (f.extend I)) '' t = t
  proof: EqOn.image_eq_self (fun _ hx => f.extend_left_inv (ht hx))

中文:
引理 extend_left_inv'
  条件: (ht : t subseteq f.source)
  结论: ((f.extend I).symm ∘ (f.extend I)) '' t = t
  证明: EqOn.image_eq_self (fun _ hx => f.extend_left_inv (ht hx))

Depends on / 依赖: EqOn.image_eq_self, extend_left_inv, f.extend_left_inv, image_eq_self
-/
lemma extend_left_inv' (ht : t subseteq f.source) : ((f.extend I).symm ∘ (f.extend I)) '' t = t :=
  EqOn.image_eq_self (fun _ hx => f.extend_left_inv (ht hx))

/--
theorem `extend_source_mem_nhds` / 定理 `extend_source_mem_nhds`

English:
theorem extend_source_mem_nhds
  given: {x : M} (h : x in f.source)
  statement: (f.extend I).source in 𝓝 x
  proof: (isOpen_extend_source f).mem_nhds by rwa [f.extend_source]

中文:
定理 extend_source_mem_nhds
  条件: {x : M} (h : x in f.source)
  结论: (f.extend I).source in 𝓝 x
  证明: (isOpen_extend_source f).mem_nhds by rwa [f.extend_source]

Depends on / 依赖: extend_source, f.extend_source, isOpen_extend_source, mem_nhds
-/
theorem extend_source_mem_nhds {x : M} (h : x in f.source) : (f.extend I).source in 𝓝 x :=
(isOpen_extend_source f).mem_nhds by rwa [f.extend_source]

/--
theorem `extend_source_mem_nhdsWithin` / 定理 `extend_source_mem_nhdsWithin`

English:
theorem extend_source_mem_nhdsWithin
  given: {x : M} (h : x in f.source)
  statement: (f.extend I).source in 𝓝[s] x
  proof: mem_nhdsWithin_of_mem_nhds extend_source_mem_nhds f h

中文:
定理 extend_source_mem_nhdsWithin
  条件: {x : M} (h : x in f.source)
  结论: (f.extend I).source in 𝓝[s] x
  证明: mem_nhdsWithin_of_mem_nhds extend_source_mem_nhds f h

Depends on / 依赖: extend_source_mem_nhds, mem_nhdsWithin_of_mem_nhds
-/
theorem extend_source_mem_nhdsWithin {x : M} (h : x in f.source) : (f.extend I).source in 𝓝[s] x :=
mem_nhdsWithin_of_mem_nhds extend_source_mem_nhds f h

/--
theorem `continuousOn_extend` / 定理 `continuousOn_extend`

English:
theorem continuousOn_extend
  statement: ContinuousOn (f.extend I) (f.extend I).source
  proof: by
  refine I.continuous.comp_continuousOn ?_
  rw [extend_source]
  exact f.continuousOn

中文:
定理 continuousOn_extend
  结论: ContinuousOn (f.extend I) (f.extend I).source
  证明: by
  refine I.continuous.comp_continuousOn ?_
  rw [extend_source]
  exact f.continuousOn

Depends on / 依赖: I.continuous.comp_continuousOn, comp_continuousOn, continuous, continuousOn, extend_source, f.continuousOn
-/
theorem continuousOn_extend : ContinuousOn (f.extend I) (f.extend I).source := by
  refine I.continuous.comp_continuousOn ?_
  rw [extend_source]
  exact f.continuousOn

/--
theorem `continuousAt_extend` / 定理 `continuousAt_extend`

English:
theorem continuousAt_extend
  given: {x : M} (h : x in f.source)
  statement: ContinuousAt (f.extend I) x
  proof: (continuousOn_extend f).continuousAt extend_source_mem_nhds f h

中文:
定理 continuousAt_extend
  条件: {x : M} (h : x in f.source)
  结论: ContinuousAt (f.extend I) x
  证明: (continuousOn_extend f).continuousAt extend_source_mem_nhds f h

Depends on / 依赖: continuousAt, continuousOn_extend, extend_source_mem_nhds
-/
theorem continuousAt_extend {x : M} (h : x in f.source) : ContinuousAt (f.extend I) x :=
(continuousOn_extend f).continuousAt extend_source_mem_nhds f h

/--
theorem `map_extend_nhds` / 定理 `map_extend_nhds`

English:
theorem map_extend_nhds
  given: {x : M} (hy : x in f.source)
  proof: by
  rwa [extend_coe, comp_apply, ← I.map_nhds_eq, ← f.map_nhds_eq, map_map]

中文:
定理 map_extend_nhds
  条件: {x : M} (hy : x in f.source)
  证明: by
  rwa [extend_coe, comp_apply, ← I.map_nhds_eq, ← f.map_nhds_eq, map_map]

Depends on / 依赖: I.map_nhds_eq, comp_apply, extend_coe, f.map_nhds_eq, map_map, map_nhds_eq
-/
theorem map_extend_nhds {x : M} (hy : x in f.source) :
    map (f.extend I) (𝓝 x) = 𝓝[range I] f.extend I x := by
  rwa [extend_coe, comp_apply, ← I.map_nhds_eq, ← f.map_nhds_eq, map_map]

/--
theorem `map_extend_nhds_of_mem_interior_range` / 定理 `map_extend_nhds_of_mem_interior_range`

English:
theorem map_extend_nhds_of_mem_interior_range
  statement: {x : M} (hx : x in f.source)
  proof: by
  rw [f.map_extend_nhds hx]; rw [nhdsWithin_eq_nhds]
  exact mem_of_superset (isOpen_interior.mem_nhds h'x) interior_subset

中文:
定理 map_extend_nhds_of_mem_interior_range
  结论: {x : M} (hx : x in f.source)
  证明: by
  rw [f.map_extend_nhds hx]; rw [nhdsWithin_eq_nhds]
  exact mem_of_superset (isOpen_interior.mem_nhds h'x) interior_subset

Depends on / 依赖: f.map_extend_nhds, interior_subset, isOpen_interior, isOpen_interior.mem_nhds, map_extend_nhds, mem_nhds, mem_of_superset, nhdsWithin_eq_nhds
-/
theorem map_extend_nhds_of_mem_interior_range {x : M} (hx : x in f.source)
    (h'x : f.extend I x in interior (range I)) :
    map (f.extend I) (𝓝 x) = 𝓝 (f.extend I x) := by
  rw [f.map_extend_nhds hx]; rw [nhdsWithin_eq_nhds]
  exact mem_of_superset (isOpen_interior.mem_nhds h'x) interior_subset

/--
theorem `map_extend_nhds_of_boundaryless` / 定理 `map_extend_nhds_of_boundaryless`

English:
theorem map_extend_nhds_of_boundaryless
  given: [I.Boundaryless] {x : M} (hx : x in f.source)
  proof: by
  rw [f.map_extend_nhds hx]; rw [I.range_eq_univ]; rw [nhdsWithin_univ]

中文:
定理 map_extend_nhds_of_boundaryless
  条件: [I.无边界] {x : M} (hx : x in f.source)
  证明: by
  rw [f.map_extend_nhds hx]; rw [I.range_eq_univ]; rw [nhdsWithin_univ]

Depends on / 依赖: I.range_eq_univ, f.map_extend_nhds, map_extend_nhds, nhdsWithin_univ, range_eq_univ
-/
theorem map_extend_nhds_of_boundaryless [I.Boundaryless] {x : M} (hx : x in f.source) :
    map (f.extend I) (𝓝 x) = 𝓝 (f.extend I x) := by
  rw [f.map_extend_nhds hx]; rw [I.range_eq_univ]; rw [nhdsWithin_univ]

/--
theorem `extend_target_mem_nhdsWithin` / 定理 `extend_target_mem_nhdsWithin`

English:
theorem extend_target_mem_nhdsWithin
  given: {y : M} (hy : y in f.source)
  proof: by
  rw [← PartialEquiv.image_source_eq_target]; rw [← map_extend_nhds f hy]
  exact image_mem_map (extend_source_mem_nhds _ hy)

中文:
定理 extend_target_mem_nhdsWithin
  条件: {y : M} (hy : y in f.source)
  证明: by
  rw [← PartialEquiv.image_source_eq_target]; rw [← map_extend_nhds f hy]
  exact image_mem_map (extend_source_mem_nhds _ hy)

Depends on / 依赖: PartialEquiv, PartialEquiv.image_source_eq_target, extend_source_mem_nhds, image_mem_map, image_source_eq_target, map_extend_nhds
-/
theorem extend_target_mem_nhdsWithin {y : M} (hy : y in f.source) :
    (f.extend I).target in 𝓝[range I] f.extend I y := by
  rw [← PartialEquiv.image_source_eq_target]; rw [← map_extend_nhds f hy]
  exact image_mem_map (extend_source_mem_nhds _ hy)

/--
lemma `extend_image_target_mem_nhds` / 引理 `extend_image_target_mem_nhds`

English:
lemma extend_image_target_mem_nhds
  given: {x : M} (hx : x in f.source)
  proof: by
  rw [← f.map_extend_nhds hx]; rw [Filter.mem_map]; rw [f.extend_coe]; rw [Set.preimage_comp]; rw [I.preimage_image f.target]
  exact (f.continuousAt hx).preimage_mem_nhds (f.open_target.mem_nhds (f.map_source hx))

中文:
引理 extend_image_target_mem_nhds
  条件: {x : M} (hx : x in f.source)
  证明: by
  rw [← f.map_extend_nhds hx]; rw [Filter.mem_map]; rw [f.extend_coe]; rw [Set.preimage_comp]; rw [I.preimage_image f.target]
  exact (f.continuousAt hx).preimage_mem_nhds (f.open_target.mem_nhds (f.map_source hx))

Depends on / 依赖: Filter, Filter.mem_map, I.preimage_image, Set.preimage_comp, continuousAt, extend_coe, f.continuousAt, f.extend_coe, f.map_extend_nhds, f.map_source, f.open_target.mem_nhds, f.target, map_extend_nhds, map_source, mem_map, mem_nhds, open_target, preimage_comp, preimage_image, preimage_mem_nhds
-/
lemma extend_image_target_mem_nhds {x : M} (hx : x in f.source) :
    I '' f.target in 𝓝[range I] (f.extend I) x := by
  rw [← f.map_extend_nhds hx]; rw [Filter.mem_map]; rw [f.extend_coe]; rw [Set.preimage_comp]; rw [I.preimage_image f.target]
  exact (f.continuousAt hx).preimage_mem_nhds (f.open_target.mem_nhds (f.map_source hx))

/--
theorem `extend_image_nhds_mem_nhds_of_boundaryless` / 定理 `extend_image_nhds_mem_nhds_of_boundaryless`

English:
theorem extend_image_nhds_mem_nhds_of_boundaryless
  statement: [I.Boundaryless] {x} (hx : x in f.source)
  proof: by
  rw [← f.map_extend_nhds_of_boundaryless hx]; rw [Filter.mem_map]
  filter_upwards [h] using subset_preimage_image (f.extend I) s

中文:
定理 extend_image_nhds_mem_nhds_of_boundaryless
  结论: [I.无边界] {x} (hx : x in f.source)
  证明: by
  rw [← f.map_extend_nhds_of_boundaryless hx]; rw [Filter.mem_map]
  filter_upwards [h] using subset_preimage_image (f.extend I) s

Depends on / 依赖: Filter, Filter.mem_map, extend, f.extend, f.map_extend_nhds_of_boundaryless, filter_upwards, map_extend_nhds_of_boundaryless, mem_map, subset_preimage_image
-/
theorem extend_image_nhds_mem_nhds_of_boundaryless [I.Boundaryless] {x} (hx : x in f.source)
    {s : Set M} (h : s in 𝓝 x) : (f.extend I) '' s in 𝓝 ((f.extend I) x) := by
  rw [← f.map_extend_nhds_of_boundaryless hx]; rw [Filter.mem_map]
  filter_upwards [h] using subset_preimage_image (f.extend I) s

/--
theorem `extend_image_nhds_mem_nhds_of_mem_interior_range` / 定理 `extend_image_nhds_mem_nhds_of_mem_interior_range`

English:
theorem extend_image_nhds_mem_nhds_of_mem_interior_range
  statement: {x} (hx : x in f.source)
  proof: by
  rw [← f.map_extend_nhds_of_mem_interior_range hx h'x]; rw [Filter.mem_map]
  filter_upwards [h] using subset_preimage_image (f.extend I) s

中文:
定理 extend_image_nhds_mem_nhds_of_mem_interior_range
  结论: {x} (hx : x in f.source)
  证明: by
  rw [← f.map_extend_nhds_of_mem_interior_range hx h'x]; rw [Filter.mem_map]
  filter_upwards [h] using subset_preimage_image (f.extend I) s

Depends on / 依赖: Filter, Filter.mem_map, extend, f.extend, f.map_extend_nhds_of_mem_interior_range, filter_upwards, map_extend_nhds_of_mem_interior_range, mem_map, subset_preimage_image
-/
theorem extend_image_nhds_mem_nhds_of_mem_interior_range {x} (hx : x in f.source)
    (h'x : f.extend I x in interior (range I)) {s : Set M} (h : s in 𝓝 x) :
    (f.extend I) '' s in 𝓝 ((f.extend I) x) := by
  rw [← f.map_extend_nhds_of_mem_interior_range hx h'x]; rw [Filter.mem_map]
  filter_upwards [h] using subset_preimage_image (f.extend I) s

/--
theorem `extend_target_subset_range` / 定理 `extend_target_subset_range`

English:
theorem extend_target_subset_range
  statement: (f.extend I).target subseteq range I
  proof: by simp only [mfld_simps]

中文:
定理 extend_target_subset_range
  结论: (f.extend I).target subseteq range I
  证明: by simp only [mfld_simps]

Depends on / 依赖: mfld_simps
-/
theorem extend_target_subset_range : (f.extend I).target subseteq range I := by simp only [mfld_simps]

/--
lemma `interior_extend_target_subset_interior_range` / 引理 `interior_extend_target_subset_interior_range`

English:
lemma interior_extend_target_subset_interior_range
  proof: by
  rw [f.extend_target]; rw [interior_inter]; rw [(f.open_target.preimage I.continuous_symm).interior_eq]
  exact inter_subset_right

中文:
引理 interior_extend_target_subset_interior_range
  证明: by
  rw [f.extend_target]; rw [interior_inter]; rw [(f.open_target.preimage I.continuous_symm).interior_eq]
  exact inter_subset_right

Depends on / 依赖: I.continuous_symm, continuous_symm, extend_target, f.extend_target, f.open_target.preimage, inter_subset_right, interior_eq, interior_inter, open_target, preimage
-/
lemma interior_extend_target_subset_interior_range :
    interior (f.extend I).target subseteq interior (range I) := by
  rw [f.extend_target]; rw [interior_inter]; rw [(f.open_target.preimage I.continuous_symm).interior_eq]
  exact inter_subset_right

/--
lemma `mem_interior_extend_target` / 引理 `mem_interior_extend_target`

English:
lemma mem_interior_extend_target
  statement: {y : H} (hy : y in f.target)
  proof: by
  rw [f.extend_target]; rw [interior_inter]; rw [(f.open_target.preimage I.continuous_symm).interior_eq]; rw [mem_inter_iff]; rw [mem_preimage]
  exact ⟨mem_of_eq_of_mem (I.left_inv (y)) hy, hy'⟩

中文:
引理 mem_interior_extend_target
  结论: {y : H} (hy : y in f.target)
  证明: by
  rw [f.extend_target]; rw [interior_inter]; rw [(f.open_target.preimage I.continuous_symm).interior_eq]; rw [mem_inter_iff]; rw [mem_preimage]
  exact ⟨mem_of_eq_of_mem (I.left_inv (y)) hy, hy'⟩

Depends on / 依赖: I.continuous_symm, I.left_inv, continuous_symm, extend_target, f.extend_target, f.open_target.preimage, interior_eq, interior_inter, left_inv, mem_inter_iff, mem_of_eq_of_mem, mem_preimage, open_target, preimage
-/
lemma mem_interior_extend_target {y : H} (hy : y in f.target)
    (hy' : I y in interior (range I)) : I y in interior (f.extend I).target := by
  rw [f.extend_target]; rw [interior_inter]; rw [(f.open_target.preimage I.continuous_symm).interior_eq]; rw [mem_inter_iff]; rw [mem_preimage]
  exact ⟨mem_of_eq_of_mem (I.left_inv (y)) hy, hy'⟩

/--
theorem `nhdsWithin_extend_target_eq` / 定理 `nhdsWithin_extend_target_eq`

English:
theorem nhdsWithin_extend_target_eq
  given: {y : M} (hy : y in f.source)
  proof: (nhdsWithin_mono _ (extend_target_subset_range _)).antisymm
    nhdsWithin_le_of_mem (extend_target_mem_nhdsWithin _ hy)

中文:
定理 nhdsWithin_extend_target_eq
  条件: {y : M} (hy : y in f.source)
  证明: (nhdsWithin_mono _ (extend_target_subset_range _)).antisymm
    nhdsWithin_le_of_mem (extend_target_mem_nhdsWithin _ hy)

Depends on / 依赖: antisymm, extend_target_mem_nhdsWithin, extend_target_subset_range, nhdsWithin_le_of_mem, nhdsWithin_mono
-/
theorem nhdsWithin_extend_target_eq {y : M} (hy : y in f.source) :
    𝓝[(f.extend I).target] f.extend I y = 𝓝[range I] f.extend I y :=
(nhdsWithin_mono _ (extend_target_subset_range _)).antisymm
    nhdsWithin_le_of_mem (extend_target_mem_nhdsWithin _ hy)

/--
theorem `extend_target_eventuallyEq` / 定理 `extend_target_eventuallyEq`

English:
theorem extend_target_eventuallyEq
  given: {y : M} (hy : y in f.source)
  proof: nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extend_target_eq _ hy)

中文:
定理 extend_target_eventuallyEq
  条件: {y : M} (hy : y in f.source)
  证明: nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extend_target_eq _ hy)

Depends on / 依赖: nhdsWithin_eq_iff_eventuallyEq, nhdsWithin_extend_target_eq
-/
theorem extend_target_eventuallyEq {y : M} (hy : y in f.source) :
    (f.extend I).target =ᶠ[𝓝 (f.extend I y)] range I :=
  nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extend_target_eq _ hy)

/--
theorem `continuousAt_extend_symm'` / 定理 `continuousAt_extend_symm'`

English:
theorem continuousAt_extend_symm'
  given: {x : E} (h : x in (f.extend I).target)
  proof: (f.continuousAt_symm h.2).comp I.continuous_symm.continuousAt

中文:
定理 continuousAt_extend_symm'
  条件: {x : E} (h : x in (f.extend I).target)
  证明: (f.continuousAt_symm h.2).comp I.continuous_symm.continuousAt

Depends on / 依赖: I.continuous_symm.continuousAt, continuousAt, continuousAt_symm, continuous_symm, f.continuousAt_symm
-/
theorem continuousAt_extend_symm' {x : E} (h : x in (f.extend I).target) :
    ContinuousAt (f.extend I).symm x :=
  (f.continuousAt_symm h.2).comp I.continuous_symm.continuousAt

/--
theorem `continuousAt_extend_symm` / 定理 `continuousAt_extend_symm`

English:
theorem continuousAt_extend_symm
  given: {x : M} (h : x in f.source)
  proof: continuousAt_extend_symm' f (f.extend I).map_source by rwa [f.extend_source]

中文:
定理 continuousAt_extend_symm
  条件: {x : M} (h : x in f.source)
  证明: continuousAt_extend_symm' f (f.extend I).map_source by rwa [f.extend_source]

Depends on / 依赖: continuousAt_extend_symm, extend, extend_source, f.extend, f.extend_source, map_source
-/
theorem continuousAt_extend_symm {x : M} (h : x in f.source) :
    ContinuousAt (f.extend I).symm (f.extend I x) :=
continuousAt_extend_symm' f (f.extend I).map_source by rwa [f.extend_source]

/--
theorem `continuousOn_extend_symm` / 定理 `continuousOn_extend_symm`

English:
theorem continuousOn_extend_symm
  statement: ContinuousOn (f.extend I).symm (f.extend I).target
  proof: fun _ h =>
  (continuousAt_extend_symm' _ h).continuousWithinAt

中文:
定理 continuousOn_extend_symm
  结论: ContinuousOn (f.extend I).symm (f.extend I).target
  证明: fun _ h =>
  (continuousAt_extend_symm' _ h).continuousWithinAt
-/
theorem continuousOn_extend_symm : ContinuousOn (f.extend I).symm (f.extend I).target := fun _ h =>
  (continuousAt_extend_symm' _ h).continuousWithinAt

/--
theorem `extend_symm_continuousWithinAt_comp_right_iff` / 定理 `extend_symm_continuousWithinAt_comp_right_iff`

English:
theorem extend_symm_continuousWithinAt_comp_right_iff
  statement: {X} [TopologicalSpace X] {g : M -> X}
  proof: by
  rw [← I.symm_continuousWithinAt_comp_right_iff]; rfl

中文:
定理 extend_symm_continuousWithinAt_comp_right_iff
  结论: {X} [拓扑空间 X] {g : M -> X}
  证明: by
  rw [← I.symm_continuousWithinAt_comp_right_iff]; rfl

Depends on / 依赖: I.symm_continuousWithinAt_comp_right_iff, symm_continuousWithinAt_comp_right_iff
-/
theorem extend_symm_continuousWithinAt_comp_right_iff {X} [TopologicalSpace X] {g : M -> X}
    {s : Set M} {x : M} :
    ContinuousWithinAt (g ∘ (f.extend I).symm) ((f.extend I).symm ⁻¹' s inter range I) (f.extend I x) ↔
      ContinuousWithinAt (g ∘ f.symm) (f.symm ⁻¹' s) (f x) := by
  rw [← I.symm_continuousWithinAt_comp_right_iff]; rfl

/--
theorem `isOpen_extend_preimage'` / 定理 `isOpen_extend_preimage'`

English:
theorem isOpen_extend_preimage'
  given: {s : Set E} (hs : IsOpen s)
  proof: (continuousOn_extend f).isOpen_inter_preimage (isOpen_extend_source _) hs

中文:
定理 isOpen_extend_preimage'
  条件: {s : 集合 E} (hs : 是开集 s)
  证明: (continuousOn_extend f).isOpen_inter_preimage (isOpen_extend_source _) hs

Depends on / 依赖: continuousOn_extend, isOpen_extend_source, isOpen_inter_preimage
-/
theorem isOpen_extend_preimage' {s : Set E} (hs : IsOpen s) :
    IsOpen ((f.extend I).source inter f.extend I ⁻¹' s) :=
  (continuousOn_extend f).isOpen_inter_preimage (isOpen_extend_source _) hs

/--
theorem `isOpen_extend_preimage` / 定理 `isOpen_extend_preimage`

English:
theorem isOpen_extend_preimage
  given: {s : Set E} (hs : IsOpen s)
  proof: by
  rw [← extend_source f (I := I)]; exact isOpen_extend_preimage' f hs

中文:
定理 isOpen_extend_preimage
  条件: {s : 集合 E} (hs : 是开集 s)
  证明: by
  rw [← extend_source f (I := I)]; exact isOpen_extend_preimage' f hs

Depends on / 依赖: extend_source, isOpen_extend_preimage
-/
theorem isOpen_extend_preimage {s : Set E} (hs : IsOpen s) :
    IsOpen (f.source inter f.extend I ⁻¹' s) := by
  rw [← extend_source f (I := I)]; exact isOpen_extend_preimage' f hs

/--
theorem `map_extend_nhdsWithin_eq_image` / 定理 `map_extend_nhdsWithin_eq_image`

English:
theorem map_extend_nhdsWithin_eq_image
  given: {y : M} (hy : y in f.source)
  proof: by
  set e := f.extend I
  calc
    map e (𝓝[s] y) = map e (𝓝[e.source inter s] y) :=
      congr_arg (map e) (nhdsWithin_inter_of_mem (extend_source_mem_nhdsWithin f hy)).symm
    _ = 𝓝[e '' (e.source inter s)] e y :=
      ((f.extend I).leftInvOn.mono inter_subset_left).map_nhdsWithin_eq
        (

中文:
定理 map_extend_nhdsWithin_eq_image
  条件: {y : M} (hy : y in f.source)
  证明: by
  set e := f.extend I
  calc
    map e (𝓝[s] y) = map e (𝓝[e.source inter s] y) :=
      congr_arg (map e) (nhdsWithin_inter_of_mem (extend_source_mem_nhdsWithin f hy)).symm
    _ = 𝓝[e '' (e.source inter s)] e y :=
      ((f.extend I).leftInvOn.mono inter_subset_left).map_nhdsWithin_eq
        (

Depends on / 依赖: congr_arg, continuousAt_extend, continuousAt_extend_symm, continuousWithinAt, e.source, extend, extend_source, extend_source_mem_nhdsWithin, f.extend, f.extend_source, inter_subset_left, leftInvOn, leftInvOn.mono, left_inv, map_nhdsWithin_eq, nhdsWithin_inter_of_mem, source
-/
theorem map_extend_nhdsWithin_eq_image {y : M} (hy : y in f.source) :
    map (f.extend I) (𝓝[s] y) = 𝓝[f.extend I '' ((f.extend I).source inter s)] f.extend I y := by
  set e := f.extend I
  calc
    map e (𝓝[s] y) = map e (𝓝[e.source inter s] y) :=
      congr_arg (map e) (nhdsWithin_inter_of_mem (extend_source_mem_nhdsWithin f hy)).symm
    _ = 𝓝[e '' (e.source inter s)] e y :=
      ((f.extend I).leftInvOn.mono inter_subset_left).map_nhdsWithin_eq
        ((f.extend I).left_inv <| by rwa [f.extend_source])
        (continuousAt_extend_symm f hy).continuousWithinAt
        (continuousAt_extend f hy).continuousWithinAt

/--
theorem `map_extend_nhdsWithin_eq_image_of_subset` / 定理 `map_extend_nhdsWithin_eq_image_of_subset`

English:
theorem map_extend_nhdsWithin_eq_image_of_subset
  given: {y : M} (hy : y in f.source) (hs : s subseteq f.source)
  proof: by
  rw [map_extend_nhdsWithin_eq_image _ hy]; rw [inter_eq_self_of_subset_right]
  rwa [extend_source]

中文:
定理 map_extend_nhdsWithin_eq_image_of_subset
  条件: {y : M} (hy : y in f.source) (hs : s subseteq f.source)
  证明: by
  rw [map_extend_nhdsWithin_eq_image _ hy]; rw [inter_eq_self_of_subset_right]
  rwa [extend_source]

Depends on / 依赖: extend_source, inter_eq_self_of_subset_right, map_extend_nhdsWithin_eq_image
-/
theorem map_extend_nhdsWithin_eq_image_of_subset {y : M} (hy : y in f.source) (hs : s subseteq f.source) :
    map (f.extend I) (𝓝[s] y) = 𝓝[f.extend I '' s] f.extend I y := by
  rw [map_extend_nhdsWithin_eq_image _ hy]; rw [inter_eq_self_of_subset_right]
  rwa [extend_source]

/--
theorem `map_extend_nhdsWithin` / 定理 `map_extend_nhdsWithin`

English:
theorem map_extend_nhdsWithin
  given: {y : M} (hy : y in f.source)
  proof: by
  rw [map_extend_nhdsWithin_eq_image f hy]; rw [nhdsWithin_inter]; rw [←
    nhdsWithin_extend_target_eq _ hy]; rw [← nhdsWithin_inter]; rw [(f.extend I).image_source_inter_eq']; rw [inter_comm]

中文:
定理 map_extend_nhdsWithin
  条件: {y : M} (hy : y in f.source)
  证明: by
  rw [map_extend_nhdsWithin_eq_image f hy]; rw [nhdsWithin_inter]; rw [←
    nhdsWithin_extend_target_eq _ hy]; rw [← nhdsWithin_inter]; rw [(f.extend I).image_source_inter_eq']; rw [inter_comm]

Depends on / 依赖: extend, f.extend, image_source_inter_eq, inter_comm, map_extend_nhdsWithin_eq_image, nhdsWithin_extend_target_eq, nhdsWithin_inter
-/
theorem map_extend_nhdsWithin {y : M} (hy : y in f.source) :
    map (f.extend I) (𝓝[s] y) = 𝓝[(f.extend I).symm ⁻¹' s inter range I] f.extend I y := by
  rw [map_extend_nhdsWithin_eq_image f hy]; rw [nhdsWithin_inter]; rw [←
    nhdsWithin_extend_target_eq _ hy]; rw [← nhdsWithin_inter]; rw [(f.extend I).image_source_inter_eq']; rw [inter_comm]

/--
theorem `map_extend_symm_nhdsWithin` / 定理 `map_extend_symm_nhdsWithin`

English:
theorem map_extend_symm_nhdsWithin
  given: {y : M} (hy : y in f.source)
  proof: by
  rw [← map_extend_nhdsWithin f hy]; rw [map_map]; rw [Filter.map_congr]; rw [map_id]
  exact (f.extend I).leftInvOn.eqOn.eventuallyEq_of_mem (extend_source_mem_nhdsWithin _ hy)

中文:
定理 map_extend_symm_nhdsWithin
  条件: {y : M} (hy : y in f.source)
  证明: by
  rw [← map_extend_nhdsWithin f hy]; rw [map_map]; rw [Filter.map_congr]; rw [map_id]
  exact (f.extend I).leftInvOn.eqOn.eventuallyEq_of_mem (extend_source_mem_nhdsWithin _ hy)

Depends on / 依赖: Filter, Filter.map_congr, eventuallyEq_of_mem, extend, extend_source_mem_nhdsWithin, f.extend, leftInvOn, leftInvOn.eqOn.eventuallyEq_of_mem, map_congr, map_extend_nhdsWithin, map_id, map_map
-/
theorem map_extend_symm_nhdsWithin {y : M} (hy : y in f.source) :
    map (f.extend I).symm (𝓝[(f.extend I).symm ⁻¹' s inter range I] f.extend I y) = 𝓝[s] y := by
  rw [← map_extend_nhdsWithin f hy]; rw [map_map]; rw [Filter.map_congr]; rw [map_id]
  exact (f.extend I).leftInvOn.eqOn.eventuallyEq_of_mem (extend_source_mem_nhdsWithin _ hy)

/--
theorem `map_extend_symm_nhdsWithin_range` / 定理 `map_extend_symm_nhdsWithin_range`

English:
theorem map_extend_symm_nhdsWithin_range
  given: {y : M} (hy : y in f.source)
  proof: by
  rw [← nhdsWithin_univ]; rw [← map_extend_symm_nhdsWithin f (I := I) hy]; rw [preimage_univ]; rw [univ_inter]

中文:
定理 map_extend_symm_nhdsWithin_range
  条件: {y : M} (hy : y in f.source)
  证明: by
  rw [← nhdsWithin_univ]; rw [← map_extend_symm_nhdsWithin f (I := I) hy]; rw [preimage_univ]; rw [univ_inter]

Depends on / 依赖: map_extend_symm_nhdsWithin, nhdsWithin_univ, preimage_univ, univ_inter
-/
theorem map_extend_symm_nhdsWithin_range {y : M} (hy : y in f.source) :
    map (f.extend I).symm (𝓝[range I] f.extend I y) = 𝓝 y := by
  rw [← nhdsWithin_univ]; rw [← map_extend_symm_nhdsWithin f (I := I) hy]; rw [preimage_univ]; rw [univ_inter]

/--
theorem `tendsto_extend_comp_iff` / 定理 `tendsto_extend_comp_iff`

English:
theorem tendsto_extend_comp_iff
  statement: {α : Type*} {l : Filter α} {g : α -> M}
  proof: by
  refine ⟨fun h u hu => mem_map.2 ?_, (continuousAt_extend _ hy).tendsto.comp⟩
  have := (f.continuousAt_extend_symm hy).tendsto.comp h
  rw [extend_left_inv _ hy] at this
  filter_upwards [hg, mem_map.1 (this hu)] with z hz hzu
  simpa only [(· ∘ ·), extend_left_inv _ hz, mem_preimage] using hzu

中文:
定理 tendsto_extend_comp_iff
  结论: {α : 类型} {l : 滤子 α} {g : α -> M}
  证明: by
  refine ⟨fun h u hu => mem_map.2 ?_, (continuousAt_extend _ hy).tendsto.comp⟩
  have := (f.continuousAt_extend_symm hy).tendsto.comp h
  rw [extend_left_inv _ hy] at this
  filter_upwards [hg, mem_map.1 (this hu)] with z hz hzu
  simpa only [(· ∘ ·), extend_left_inv _ hz, mem_preimage] using hzu

Depends on / 依赖: continuousAt_extend, continuousAt_extend_symm, extend_left_inv, f.continuousAt_extend_symm, filter_upwards, mem_map, mem_preimage, tendsto, tendsto.comp
-/
theorem tendsto_extend_comp_iff {α : Type*} {l : Filter α} {g : α -> M}
    (hg : forallᶠ z in l, g z in f.source) {y : M} (hy : y in f.source) :
    Tendsto (f.extend I ∘ g) l (𝓝 (f.extend I y)) ↔ Tendsto g l (𝓝 y) := by
  refine ⟨fun h u hu => mem_map.2 ?_, (continuousAt_extend _ hy).tendsto.comp⟩
  have := (f.continuousAt_extend_symm hy).tendsto.comp h
  rw [extend_left_inv _ hy] at this
  filter_upwards [hg, mem_map.1 (this hu)] with z hz hzu
  simpa only [(· ∘ ·), extend_left_inv _ hz, mem_preimage] using hzu

/--
theorem `continuousWithinAt_writtenInExtend_iff` / 定理 `continuousWithinAt_writtenInExtend_iff`

English:
theorem continuousWithinAt_writtenInExtend_iff
  statement: {f' : OpenPartialHomeomorph M' H'} {g : M -> M'}
  proof: by
  unfold ContinuousWithinAt
  simp only [comp_apply]
  rw [extend_left_inv _ hy]; rw [f'.tendsto_extend_comp_iff _ hgy]; rw [← f.map_extend_symm_nhdsWithin (I := I) hy]; rw [tendsto_map'_iff]
  rw [← f.map_extend_nhdsWithin (I := I) hy]; rw [eventually_map]
  filter_upwards [inter_mem_nhdsWithin 

中文:
定理 continuousWithinAt_writtenInExtend_iff
  结论: {f' : OpenPartialHomeomorph M' H'} {g : M -> M'}
  证明: by
  unfold ContinuousWithinAt
  simp only [comp_apply]
  rw [extend_left_inv _ hy]; rw [f'.tendsto_extend_comp_iff _ hgy]; rw [← f.map_extend_symm_nhdsWithin (I := I) hy]; rw [tendsto_map'_iff]
  rw [← f.map_extend_nhdsWithin (I := I) hy]; rw [eventually_map]
  filter_upwards [inter_mem_nhdsWithin 

Depends on / 依赖: ContinuousWithinAt, _iff, comp_apply, eventually_map, extend_left_inv, f.map_extend_nhdsWithin, f.map_extend_symm_nhdsWithin, f.open_source.mem_nhds, filter_upwards, inter_mem_nhdsWithin, map_extend_nhdsWithin, map_extend_symm_nhdsWithin, mem_nhds, open_source, tendsto_extend_comp_iff, tendsto_map
-/
theorem continuousWithinAt_writtenInExtend_iff {f' : OpenPartialHomeomorph M' H'} {g : M -> M'}
    {y : M} (hy : y in f.source) (hgy : g y in f'.source) (hmaps : MapsTo g s f'.source) :
    ContinuousWithinAt (f'.extend I' ∘ g ∘ (f.extend I).symm)
      ((f.extend I).symm ⁻¹' s inter range I) (f.extend I y) ↔ ContinuousWithinAt g s y := by
  unfold ContinuousWithinAt
  simp only [comp_apply]
  rw [extend_left_inv _ hy]; rw [f'.tendsto_extend_comp_iff _ hgy]; rw [← f.map_extend_symm_nhdsWithin (I := I) hy]; rw [tendsto_map'_iff]
  rw [← f.map_extend_nhdsWithin (I := I) hy]; rw [eventually_map]
  filter_upwards [inter_mem_nhdsWithin _ (f.open_source.mem_nhds hy)] with z hz
  rw [comp_apply]; rw [extend_left_inv _ hz.2]
  exact hmaps hz.1

/--
theorem `continuousOn_writtenInExtend_iff` / 定理 `continuousOn_writtenInExtend_iff`

English:
theorem continuousOn_writtenInExtend_iff
  statement: {f' : OpenPartialHomeomorph M' H'} {g : M -> M'}
  proof: by
refine forall_mem_image.trans forall₂_congr fun x hx => ?_
  refine (continuousWithinAt_congr_set ?_).trans
    (continuousWithinAt_writtenInExtend_iff _ (hs hx) (hmaps hx) hmaps)
  rw [← nhdsWithin_eq_iff_eventuallyEq]; rw [← map_extend_nhdsWithin_eq_image_of_subset]; rw [← map_extend_nhdsWithin

中文:
定理 continuousOn_writtenInExtend_iff
  结论: {f' : OpenPartialHomeomorph M' H'} {g : M -> M'}
  证明: by
refine forall_mem_image.trans forall₂_congr fun x hx => ?_
  refine (continuousWithinAt_congr_set ?_).trans
    (continuousWithinAt_writtenInExtend_iff _ (hs hx) (hmaps hx) hmaps)
  rw [← nhdsWithin_eq_iff_eventuallyEq]; rw [← map_extend_nhdsWithin_eq_image_of_subset]; rw [← map_extend_nhdsWithin

Depends on / 依赖: continuousWithinAt_congr_set, continuousWithinAt_writtenInExtend_iff, exacts, forall_mem_image, forall_mem_image.trans, map_extend_nhdsWithin, map_extend_nhdsWithin_eq_image_of_subset, nhdsWithin_eq_iff_eventuallyEq
-/
theorem continuousOn_writtenInExtend_iff {f' : OpenPartialHomeomorph M' H'} {g : M -> M'}
    (hs : s subseteq f.source) (hmaps : MapsTo g s f'.source) :
    ContinuousOn (f'.extend I' ∘ g ∘ (f.extend I).symm) (f.extend I '' s) ↔ ContinuousOn g s := by
refine forall_mem_image.trans forall₂_congr fun x hx => ?_
  refine (continuousWithinAt_congr_set ?_).trans
    (continuousWithinAt_writtenInExtend_iff _ (hs hx) (hmaps hx) hmaps)
  rw [← nhdsWithin_eq_iff_eventuallyEq]; rw [← map_extend_nhdsWithin_eq_image_of_subset]; rw [← map_extend_nhdsWithin]
  exacts [hs hx, hs hx, hs]

/--
theorem `extend_preimage_mem_nhds_of_mem_nhdsWithin` / 定理 `extend_preimage_mem_nhds_of_mem_nhdsWithin`

English:
theorem extend_preimage_mem_nhds_of_mem_nhdsWithin
  statement: {s : Set E} {x : M} (hx : x in f.source)
  proof: by
  rwa [← map_extend_nhds (I := I) f hx] at hs

中文:
定理 extend_preimage_mem_nhds_of_mem_nhdsWithin
  结论: {s : 集合 E} {x : M} (hx : x in f.source)
  证明: by
  rwa [← map_extend_nhds (I := I) f hx] at hs

Depends on / 依赖: map_extend_nhds
-/
theorem extend_preimage_mem_nhds_of_mem_nhdsWithin {s : Set E} {x : M} (hx : x in f.source)
    (hs : s in 𝓝[range I] (f.extend I x)) :
    (f.extend I) ⁻¹' s in 𝓝 x := by
  rwa [← map_extend_nhds (I := I) f hx] at hs

/--
theorem `extend_preimage_mem_nhdsWithin` / 定理 `extend_preimage_mem_nhdsWithin`

English:
theorem extend_preimage_mem_nhdsWithin
  given: {x : M} (h : x in f.source) (ht : t in 𝓝[s] x)
  proof: by
  rwa [← map_extend_symm_nhdsWithin f (I := I) h, mem_map] at ht

中文:
定理 extend_preimage_mem_nhdsWithin
  条件: {x : M} (h : x in f.source) (ht : t in 𝓝[s] x)
  证明: by
  rwa [← map_extend_symm_nhdsWithin f (I := I) h, mem_map] at ht

Depends on / 依赖: map_extend_symm_nhdsWithin, mem_map
-/
theorem extend_preimage_mem_nhdsWithin {x : M} (h : x in f.source) (ht : t in 𝓝[s] x) :
    (f.extend I).symm ⁻¹' t in 𝓝[(f.extend I).symm ⁻¹' s inter range I] f.extend I x := by
  rwa [← map_extend_symm_nhdsWithin f (I := I) h, mem_map] at ht

/--
theorem `extend_preimage_mem_nhds` / 定理 `extend_preimage_mem_nhds`

English:
theorem extend_preimage_mem_nhds
  given: {x : M} (h : x in f.source) (ht : t in 𝓝 x)
  proof: by
  apply (continuousAt_extend_symm f h).preimage_mem_nhds
  rwa [(f.extend I).left_inv]
  rwa [f.extend_source]

中文:
定理 extend_preimage_mem_nhds
  条件: {x : M} (h : x in f.source) (ht : t in 𝓝 x)
  证明: by
  apply (continuousAt_extend_symm f h).preimage_mem_nhds
  rwa [(f.extend I).left_inv]
  rwa [f.extend_source]

Depends on / 依赖: continuousAt_extend_symm, extend, extend_source, f.extend, f.extend_source, left_inv, preimage_mem_nhds
-/
theorem extend_preimage_mem_nhds {x : M} (h : x in f.source) (ht : t in 𝓝 x) :
    (f.extend I).symm ⁻¹' t in 𝓝 (f.extend I x) := by
  apply (continuousAt_extend_symm f h).preimage_mem_nhds
  rwa [(f.extend I).left_inv]
  rwa [f.extend_source]

/--
theorem `extend_preimage_inter_eq` / 定理 `extend_preimage_inter_eq`

English:
theorem extend_preimage_inter_eq
  proof: by
  mfld_set_tac

中文:
定理 extend_preimage_inter_eq
  证明: by
  mfld_set_tac

Depends on / 依赖: mfld_set_tac
-/
theorem extend_preimage_inter_eq :
    (f.extend I).symm ⁻¹' (s inter t) inter range I =
      (f.extend I).symm ⁻¹' s inter range I inter (f.extend I).symm ⁻¹' t := by
  mfld_set_tac

/--
theorem `extend_symm_preimage_inter_range_eventuallyEq` / 定理 `extend_symm_preimage_inter_range_eventuallyEq`

English:
theorem extend_symm_preimage_inter_range_eventuallyEq
  statement: {s : Set M} {x : M} (hs : s subseteq f.source)
  proof: by
  rw [← nhdsWithin_eq_iff_eventuallyEq]; rw [← map_extend_nhdsWithin _ hx]; rw [map_extend_nhdsWithin_eq_image_of_subset _ hx hs]

中文:
定理 extend_symm_preimage_inter_range_eventuallyEq
  结论: {s : 集合 M} {x : M} (hs : s subseteq f.source)
  证明: by
  rw [← nhdsWithin_eq_iff_eventuallyEq]; rw [← map_extend_nhdsWithin _ hx]; rw [map_extend_nhdsWithin_eq_image_of_subset _ hx hs]

Depends on / 依赖: map_extend_nhdsWithin, map_extend_nhdsWithin_eq_image_of_subset, nhdsWithin_eq_iff_eventuallyEq
-/
theorem extend_symm_preimage_inter_range_eventuallyEq {s : Set M} {x : M} (hs : s subseteq f.source)
    (hx : x in f.source) :
    ((f.extend I).symm ⁻¹' s inter range I : Set _) =ᶠ[𝓝 (f.extend I x)] f.extend I '' s := by
  rw [← nhdsWithin_eq_iff_eventuallyEq]; rw [← map_extend_nhdsWithin _ hx]; rw [map_extend_nhdsWithin_eq_image_of_subset _ hx hs]

/--
lemma `extend_prod` / 引理 `extend_prod`

English:
lemma extend_prod
  given: (f' : OpenPartialHomeomorph M' H')
  proof: by simp

中文:
引理 extend_prod
  条件: (f' : OpenPartialHomeomorph M' H')
  证明: by simp
-/
lemma extend_prod (f' : OpenPartialHomeomorph M' H') :
    (f.prod f').extend (I.prod I') = (f.extend I).prod (f'.extend I') := by simp

end OpenPartialHomeomorph

namespace ModelWithCorners

/--
Definition of `extendCoordChange` / `extendCoordChange` 的定义

English:
abbreviation extendCoordChange
  signature: (e e' : OpenPartialHomeomorph M H)
  body: (e.extend I).symm ≫ e'.extend I

中文:
缩写 extendCoordChange
  签名: (e e' : OpenPartialHomeomorph M H)
  定义体: (e.extend I).symm ≫ e'.extend I

Depends on / 依赖: e.extend, extend
-/
abbrev extendCoordChange (e e' : OpenPartialHomeomorph M H) : PartialEquiv E E :=
  (e.extend I).symm ≫ e'.extend I

variable {e e' : OpenPartialHomeomorph M H}

/--
lemma `extendCoordChange_symm` / 引理 `extendCoordChange_symm`

English:
lemma extendCoordChange_symm
  statement: (I.extendCoordChange e e').symm = I.extendCoordChange e' e
  proof: by
  rfl

中文:
引理 extendCoordChange_symm
  结论: (I.extendCoordChange e e').symm = I.extendCoordChange e' e
  证明: by
  rfl
-/
lemma extendCoordChange_symm : (I.extendCoordChange e e').symm = I.extendCoordChange e' e := by
  rfl

/--
lemma `extendCoordChange_source` / 引理 `extendCoordChange_source`

English:
lemma extendCoordChange_source
  proof: by
  simp_rw [extendCoordChange, PartialEquiv.trans_source, I.image_eq, e'.extend_source,
    PartialEquiv.symm_source, e.extend_target, inter_right_comm _ (range I)]
  simp [Set.preimage_comp]

中文:
引理 extendCoordChange_source
  证明: by
  simp_rw [extendCoordChange, PartialEquiv.trans_source, I.image_eq, e'.extend_source,
    PartialEquiv.symm_source, e.extend_target, inter_right_comm _ (range I)]
  simp [Set.preimage_comp]

Depends on / 依赖: I.image_eq, PartialEquiv, PartialEquiv.symm_source, PartialEquiv.trans_source, Set.preimage_comp, e.extend_target, extendCoordChange, extend_source, extend_target, image_eq, inter_right_comm, preimage_comp, simp_rw, symm_source, trans_source
-/
lemma extendCoordChange_source :
    (I.extendCoordChange e e').source = I '' (e.symm ≫ₕ e').source := by
  simp_rw [extendCoordChange, PartialEquiv.trans_source, I.image_eq, e'.extend_source,
    PartialEquiv.symm_source, e.extend_target, inter_right_comm _ (range I)]
  simp [Set.preimage_comp]

/--
lemma `extendCoordChange_target` / 引理 `extendCoordChange_target`

English:
lemma extendCoordChange_target
  proof: by
  rw [← PartialEquiv.symm_source]; rw [← OpenPartialHomeomorph.symm_source]
  exact I.extendCoordChange_source

中文:
引理 extendCoordChange_target
  证明: by
  rw [← PartialEquiv.symm_source]; rw [← OpenPartialHomeomorph.symm_source]
  exact I.extendCoordChange_source

Depends on / 依赖: I.extendCoordChange_source, OpenPartialHomeomorph, OpenPartialHomeomorph.symm_source, PartialEquiv, PartialEquiv.symm_source, extendCoordChange_source, symm_source
-/
lemma extendCoordChange_target :
    (I.extendCoordChange e e').target = I '' (e.symm ≫ₕ e').target := by
  rw [← PartialEquiv.symm_source]; rw [← OpenPartialHomeomorph.symm_source]
  exact I.extendCoordChange_source

/--
lemma `_root_.OpenPartialHomeomorph.extend_image_source_inter` / 引理 `_root_.OpenPartialHomeomorph.extend_image_source_inter`

English:
lemma _root_.OpenPartialHomeomorph.extend_image_source_inter
  proof: by
  simp_rw [I.extendCoordChange_source, f.extend_coe, image_comp I f,
    OpenPartialHomeomorph.trans_source'', OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.symm_target]

中文:
引理 _root_.OpenPartialHomeomorph.extend_image_source_inter
  证明: by
  simp_rw [I.extendCoordChange_source, f.extend_coe, image_comp I f,
    OpenPartialHomeomorph.trans_source'', OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.symm_target]

Depends on / 依赖: I.extendCoordChange_source, OpenPartialHomeomorph, OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target, OpenPartialHomeomorph.trans_source, extendCoordChange_source, extend_coe, f.extend_coe, image_comp, simp_rw, symm_symm, symm_target, trans_source
-/
lemma _root_.OpenPartialHomeomorph.extend_image_source_inter :
    f.extend I '' (f.source inter f'.source) = (I.extendCoordChange f f').source := by
  simp_rw [I.extendCoordChange_source, f.extend_coe, image_comp I f,
    OpenPartialHomeomorph.trans_source'', OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.symm_target]

/--
lemma `extendCoordChange_source_mem_nhdsWithin` / 引理 `extendCoordChange_source_mem_nhdsWithin`

English:
lemma extendCoordChange_source_mem_nhdsWithin
  statement: {x : E}
  proof: by
  rw [I.extendCoordChange_source] at hx ⊢
  obtain ⟨x, hx, rfl⟩ := hx
  refine I.image_mem_nhdsWithin ?_
  exact (OpenPartialHomeomorph.open_source _).mem_nhds hx

中文:
引理 extendCoordChange_source_mem_nhdsWithin
  结论: {x : E}
  证明: by
  rw [I.extendCoordChange_source] at hx ⊢
  obtain ⟨x, hx, rfl⟩ := hx
  refine I.image_mem_nhdsWithin ?_
  exact (OpenPartialHomeomorph.open_source _).mem_nhds hx

Depends on / 依赖: I.extendCoordChange_source, I.image_mem_nhdsWithin, OpenPartialHomeomorph, OpenPartialHomeomorph.open_source, extendCoordChange_source, image_mem_nhdsWithin, mem_nhds, open_source
-/
lemma extendCoordChange_source_mem_nhdsWithin {x : E}
    (hx : x in (I.extendCoordChange e e').source) :
    (I.extendCoordChange e e').source in 𝓝[range I] x := by
  rw [I.extendCoordChange_source] at hx ⊢
  obtain ⟨x, hx, rfl⟩ := hx
  refine I.image_mem_nhdsWithin ?_
  exact (OpenPartialHomeomorph.open_source _).mem_nhds hx

/--
lemma `extendCoordChange_source_mem_nhdsWithin'` / 引理 `extendCoordChange_source_mem_nhdsWithin'`

English:
lemma extendCoordChange_source_mem_nhdsWithin'
  statement: {x : M} (hxe : x in e.source)
  proof: by
  apply extendCoordChange_source_mem_nhdsWithin
  rw [← OpenPartialHomeomorph.extend_image_source_inter]
  exact mem_image_of_mem _ ⟨hxe, hxe'⟩

中文:
引理 extendCoordChange_source_mem_nhdsWithin'
  结论: {x : M} (hxe : x in e.source)
  证明: by
  apply extendCoordChange_source_mem_nhdsWithin
  rw [← OpenPartialHomeomorph.extend_image_source_inter]
  exact mem_image_of_mem _ ⟨hxe, hxe'⟩

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.extend_image_source_inter, extendCoordChange_source_mem_nhdsWithin, extend_image_source_inter, mem_image_of_mem
-/
lemma extendCoordChange_source_mem_nhdsWithin' {x : M} (hxe : x in e.source)
    (hxe' : x in e'.source) :
    (I.extendCoordChange e e').source in 𝓝[range I] e.extend I x := by
  apply extendCoordChange_source_mem_nhdsWithin
  rw [← OpenPartialHomeomorph.extend_image_source_inter]
  exact mem_image_of_mem _ ⟨hxe, hxe'⟩

/--
lemma `uniqueDiffOn_extendCoordChange_source` / 引理 `uniqueDiffOn_extendCoordChange_source`

English:
lemma uniqueDiffOn_extendCoordChange_source
  statement: UniqueDiffOn 𝕜 (I.extendCoordChange e e').source
  proof: by
  rw [extendCoordChange_source]; rw [I.image_eq]
exact I.uniqueDiffOn_preimage e.isOpen_inter_preimage_symm e'.open_source

中文:
引理 uniqueDiffOn_extendCoordChange_source
  结论: UniqueDiffOn 𝕜 (I.extendCoordChange e e').source
  证明: by
  rw [extendCoordChange_source]; rw [I.image_eq]
exact I.uniqueDiffOn_preimage e.isOpen_inter_preimage_symm e'.open_source

Depends on / 依赖: I.image_eq, I.uniqueDiffOn_preimage, e.isOpen_inter_preimage_symm, extendCoordChange_source, image_eq, isOpen_inter_preimage_symm, open_source, uniqueDiffOn_preimage
-/
lemma uniqueDiffOn_extendCoordChange_source : UniqueDiffOn 𝕜 (I.extendCoordChange e e').source := by
  rw [extendCoordChange_source]; rw [I.image_eq]
exact I.uniqueDiffOn_preimage e.isOpen_inter_preimage_symm e'.open_source

/--
lemma `uniqueDiffOn_extendCoordChange_target` / 引理 `uniqueDiffOn_extendCoordChange_target`

English:
lemma uniqueDiffOn_extendCoordChange_target
  statement: UniqueDiffOn 𝕜 (I.extendCoordChange e e').target
  proof: by
  rw [← extendCoordChange_symm]; rw [PartialEquiv.symm_target]
  exact uniqueDiffOn_extendCoordChange_source

中文:
引理 uniqueDiffOn_extendCoordChange_target
  结论: UniqueDiffOn 𝕜 (I.extendCoordChange e e').target
  证明: by
  rw [← extendCoordChange_symm]; rw [PartialEquiv.symm_target]
  exact uniqueDiffOn_extendCoordChange_source

Depends on / 依赖: PartialEquiv, PartialEquiv.symm_target, extendCoordChange_symm, symm_target, uniqueDiffOn_extendCoordChange_source
-/
lemma uniqueDiffOn_extendCoordChange_target : UniqueDiffOn 𝕜 (I.extendCoordChange e e').target := by
  rw [← extendCoordChange_symm]; rw [PartialEquiv.symm_target]
  exact uniqueDiffOn_extendCoordChange_source

open IsManifold

variable [ChartedSpace H M]

/--
lemma `contDiffOn_extendCoordChange` / 引理 `contDiffOn_extendCoordChange`

English:
lemma contDiffOn_extendCoordChange
  given: (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I n M)
  proof: by
  rw [I.extendCoordChange_source]; rw [I.image_eq]
  exact (StructureGroupoid.compatible_of_mem_maximalAtlas he he').1

中文:
引理 contDiffOn_extendCoordChange
  条件: (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I n M)
  证明: by
  rw [I.extendCoordChange_source]; rw [I.image_eq]
  exact (StructureGroupoid.compatible_of_mem_maximalAtlas he he').1

Depends on / 依赖: I.extendCoordChange_source, I.image_eq, StructureGroupoid, StructureGroupoid.compatible_of_mem_maximalAtlas, compatible_of_mem_maximalAtlas, extendCoordChange_source, image_eq
-/
lemma contDiffOn_extendCoordChange (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I n M) :
    ContDiffOn 𝕜 n (I.extendCoordChange e e') (I.extendCoordChange e e').source := by
  rw [I.extendCoordChange_source]; rw [I.image_eq]
  exact (StructureGroupoid.compatible_of_mem_maximalAtlas he he').1

/--
lemma `contDiffWithinAt_extendCoordChange` / 引理 `contDiffWithinAt_extendCoordChange`

English:
lemma contDiffWithinAt_extendCoordChange
  statement: (he : e in maximalAtlas I n M)
  proof: by
  apply (I.contDiffOn_extendCoordChange he he' x hx).mono_of_mem_nhdsWithin
  rw [I.extendCoordChange_source] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hx
  exact I.image_mem_nhdsWithin ((OpenPartialHomeomorph.open_source _).mem_nhds hz)

中文:
引理 contDiffWithinAt_extendCoordChange
  结论: (he : e in maximalAtlas I n M)
  证明: by
  apply (I.contDiffOn_extendCoordChange he he' x hx).mono_of_mem_nhdsWithin
  rw [I.extendCoordChange_source] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hx
  exact I.image_mem_nhdsWithin ((OpenPartialHomeomorph.open_source _).mem_nhds hz)

Depends on / 依赖: I.contDiffOn_extendCoordChange, I.extendCoordChange_source, I.image_mem_nhdsWithin, OpenPartialHomeomorph, OpenPartialHomeomorph.open_source, contDiffOn_extendCoordChange, extendCoordChange_source, image_mem_nhdsWithin, mem_nhds, mono_of_mem_nhdsWithin, open_source
-/
lemma contDiffWithinAt_extendCoordChange (he : e in maximalAtlas I n M)
    (he' : e' in maximalAtlas I n M) {x : E} (hx : x in (I.extendCoordChange e e').source) :
    ContDiffWithinAt 𝕜 n (I.extendCoordChange e e') (range I) x := by
  apply (I.contDiffOn_extendCoordChange he he' x hx).mono_of_mem_nhdsWithin
  rw [I.extendCoordChange_source] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hx
  exact I.image_mem_nhdsWithin ((OpenPartialHomeomorph.open_source _).mem_nhds hz)

/--
lemma `contDiffWithinAt_extendCoordChange'` / 引理 `contDiffWithinAt_extendCoordChange'`

English:
lemma contDiffWithinAt_extendCoordChange'
  statement: (he : e in maximalAtlas I n M)
  proof: by
  refine I.contDiffWithinAt_extendCoordChange he he' ?_
  rw [← OpenPartialHomeomorph.extend_image_source_inter]
  exact mem_image_of_mem _ ⟨hxe, hxe'⟩

中文:
引理 contDiffWithinAt_extendCoordChange'
  结论: (he : e in maximalAtlas I n M)
  证明: by
  refine I.contDiffWithinAt_extendCoordChange he he' ?_
  rw [← OpenPartialHomeomorph.extend_image_source_inter]
  exact mem_image_of_mem _ ⟨hxe, hxe'⟩

Depends on / 依赖: I.contDiffWithinAt_extendCoordChange, OpenPartialHomeomorph, OpenPartialHomeomorph.extend_image_source_inter, contDiffWithinAt_extendCoordChange, extend_image_source_inter, mem_image_of_mem
-/
lemma contDiffWithinAt_extendCoordChange' (he : e in maximalAtlas I n M)
    (he' : e' in maximalAtlas I n M) {x : M} (hxe : x in e.source) (hxe' : x in e'.source) :
    ContDiffWithinAt 𝕜 n (I.extendCoordChange e e') (range I) (e.extend I x) := by
  refine I.contDiffWithinAt_extendCoordChange he he' ?_
  rw [← OpenPartialHomeomorph.extend_image_source_inter]
  exact mem_image_of_mem _ ⟨hxe, hxe'⟩

/--
lemma `contDiffOn_extendCoordChange_symm` / 引理 `contDiffOn_extendCoordChange_symm`

English:
lemma contDiffOn_extendCoordChange_symm
  statement: (he : e in maximalAtlas I n M)
  proof: I.contDiffOn_extendCoordChange he' he

中文:
引理 contDiffOn_extendCoordChange_symm
  结论: (he : e in maximalAtlas I n M)
  证明: I.contDiffOn_extendCoordChange he' he

Depends on / 依赖: I.contDiffOn_extendCoordChange, contDiffOn_extendCoordChange
-/
lemma contDiffOn_extendCoordChange_symm (he : e in maximalAtlas I n M)
    (he' : e' in maximalAtlas I n M) :
    ContDiffOn 𝕜 n (I.extendCoordChange e e').symm (I.extendCoordChange e e').target :=
  I.contDiffOn_extendCoordChange he' he

/--
lemma `isInvertible_fderivWithin_extendCoordChange` / 引理 `isInvertible_fderivWithin_extendCoordChange`

English:
lemma isInvertible_fderivWithin_extendCoordChange
  statement: (hn : n != 0)
  proof: by
  set φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 n φ φ.source := I.contDiffOn_extendCoordChange he he'
  have hφ' : ContDiffOn 𝕜 n φ.symm φ.target := I.contDiffOn_extendCoordChange_symm he he'
  refine .of_inverse (g := (fderivWithin 𝕜 φ.symm φ.target (φ x))) ?_ ?_
  · rw [← φ.left_in

中文:
引理 isInvertible_fderivWithin_extendCoordChange
  结论: (hn : n != 0)
  证明: by
  set φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 n φ φ.source := I.contDiffOn_extendCoordChange he he'
  have hφ' : ContDiffOn 𝕜 n φ.symm φ.target := I.contDiffOn_extendCoordChange_symm he he'
  refine .of_inverse (g := (fderivWithin 𝕜 φ.symm φ.target (φ x))) ?_ ?_
  · rw [← φ.left_in

Depends on / 依赖: ContDiffOn, I.contDiffOn_extendCoordChange, I.contDiffOn_extendCoordChange_symm, I.extendCoordChange, I.uniqueDiffOn_extendCoordChange_source, contDiffOn_extendCoordChange, contDiffOn_extendCoordChange_symm, extendCoordChange, fderivWithin, fderivWithin_comp, fderivWithin_congr, fderivWithin_id, left_inv, map_source, of_inverse, rightInvOn, rightInvOn.eqOn, right_inv, source, target
-/
lemma isInvertible_fderivWithin_extendCoordChange (hn : n != 0)
    (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I n M)
    {x : E} (hx : x in (I.extendCoordChange e e').source) :
ContinuousLinearMap.IsInvertible
      fderivWithin 𝕜 (I.extendCoordChange e e') (I.extendCoordChange e e').source x := by
  set φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 n φ φ.source := I.contDiffOn_extendCoordChange he he'
  have hφ' : ContDiffOn 𝕜 n φ.symm φ.target := I.contDiffOn_extendCoordChange_symm he he'
  refine .of_inverse (g := (fderivWithin 𝕜 φ.symm φ.target (φ x))) ?_ ?_
  · rw [← φ.left_inv hx, φ.right_inv (φ.map_source hx), ← fderivWithin_comp,
      fderivWithin_congr' φ.rightInvOn.eqOn (φ.map_source hx), fderivWithin_id]
    · exact I.uniqueDiffOn_extendCoordChange_source _ (φ.map_source hx)
    · exact (φ.left_inv hx ▸ ((hφ _ hx).differentiableWithinAt hn) :)
    · exact (hφ' _ (φ.map_source hx)).differentiableWithinAt hn
    · exact φ.mapsTo_symm
    · exact I.uniqueDiffOn_extendCoordChange_source _ (φ.map_source hx)
  · rw [← fderivWithin_comp, fderivWithin_congr' φ.leftInvOn.eqOn hx, fderivWithin_id]
    · exact I.uniqueDiffOn_extendCoordChange_source _ hx
    · exact (hφ' _ (φ.map_source hx)).differentiableWithinAt hn
    · exact (hφ _ hx).differentiableWithinAt hn
    · exact φ.mapsTo
    · exact I.uniqueDiffOn_extendCoordChange_source _ hx

end ModelWithCorners

namespace OpenPartialHomeomorph

@[deprecated (since := "2026-02-16")]
alias extend_coord_change_source := ModelWithCorners.extendCoordChange_source

@[deprecated (since := "2026-02-16")]
alias extend_coord_change_source_mem_nhdsWithin :=
  ModelWithCorners.extendCoordChange_source_mem_nhdsWithin

@[deprecated (since := "2026-02-16")]
alias extend_coord_change_source_mem_nhdsWithin' :=
  ModelWithCorners.extendCoordChange_source_mem_nhdsWithin'

@[deprecated (since := "2026-02-16")]
alias contDiffOn_extend_coord_change := ModelWithCorners.contDiffOn_extendCoordChange

@[deprecated (since := "2026-02-16")]
alias contDiffWithinAt_extend_coord_change := ModelWithCorners.contDiffWithinAt_extendCoordChange

@[deprecated (since := "2026-02-16")]
alias contDiffWithinAt_extend_coord_change' := ModelWithCorners.contDiffWithinAt_extendCoordChange'

end OpenPartialHomeomorph

open OpenPartialHomeomorph

variable [ChartedSpace H M] [ChartedSpace H' M']

variable (I) in
/-- The preferred extended chart on a manifold with corners around a point `x`, from a neighborhood
of `x` to the model vector space. -/
@[simp, mfld_simps]
/--
Definition of `extChartAt` / `extChartAt` 的定义

English:
definition extChartAt
  signature: (x : M)
  body: (chartAt H x).extend I

中文:
定义 extChartAt
  签名: (x : M)
  定义体: (chartAt H x).extend I

Depends on / 依赖: chartAt, extend
-/
def extChartAt (x : M) : PartialEquiv M E :=
  (chartAt H x).extend I

/--
theorem `extChartAt_coe` / 定理 `extChartAt_coe`

English:
theorem extChartAt_coe
  given: (x : M)
  statement: ⇑(extChartAt I x) = I ∘ chartAt H x
  proof: rfl

中文:
定理 extChartAt_coe
  条件: (x : M)
  结论: ⇑(extChartAt I x) = I ∘ chartAt H x
  证明: rfl
-/
theorem extChartAt_coe (x : M) : ⇑(extChartAt I x) = I ∘ chartAt H x :=
  rfl

/--
theorem `extChartAt_coe_symm` / 定理 `extChartAt_coe_symm`

English:
theorem extChartAt_coe_symm
  given: (x : M)
  statement: ⇑(extChartAt I x).symm = (chartAt H x).symm ∘ I.symm
  proof: rfl

中文:
定理 extChartAt_coe_symm
  条件: (x : M)
  结论: ⇑(extChartAt I x).symm = (chartAt H x).symm ∘ I.symm
  证明: rfl
-/
theorem extChartAt_coe_symm (x : M) : ⇑(extChartAt I x).symm = (chartAt H x).symm ∘ I.symm :=
  rfl

variable (I) in
/--
theorem `extChartAt_source` / 定理 `extChartAt_source`

English:
theorem extChartAt_source
  given: (x : M)
  statement: (extChartAt I x).source = (chartAt H x).source
  proof: extend_source _

中文:
定理 extChartAt_source
  条件: (x : M)
  结论: (extChartAt I x).source = (chartAt H x).source
  证明: extend_source _

Depends on / 依赖: extend_source
-/
theorem extChartAt_source (x : M) : (extChartAt I x).source = (chartAt H x).source :=
  extend_source _

/--
theorem `isOpen_extChartAt_source` / 定理 `isOpen_extChartAt_source`

English:
theorem isOpen_extChartAt_source
  given: (x : M)
  statement: IsOpen (extChartAt I x).source
  proof: isOpen_extend_source _

中文:
定理 isOpen_extChartAt_source
  条件: (x : M)
  结论: 是开集 (extChartAt I x).source
  证明: isOpen_extend_source _

Depends on / 依赖: isOpen_extend_source
-/
theorem isOpen_extChartAt_source (x : M) : IsOpen (extChartAt I x).source :=
  isOpen_extend_source _

/--
theorem `mem_extChartAt_source` / 定理 `mem_extChartAt_source`

English:
theorem mem_extChartAt_source
  given: (x : M)
  statement: x in (extChartAt I x).source
  proof: by
  simp only [extChartAt_source, mem_chart_source]

中文:
定理 mem_extChartAt_source
  条件: (x : M)
  结论: x in (extChartAt I x).source
  证明: by
  simp only [extChartAt_source, mem_chart_source]

Depends on / 依赖: extChartAt_source, mem_chart_source
-/
theorem mem_extChartAt_source (x : M) : x in (extChartAt I x).source := by
  simp only [extChartAt_source, mem_chart_source]

/--
theorem `mem_extChartAt_target` / 定理 `mem_extChartAt_target`

English:
theorem mem_extChartAt_target
  given: (x : M)
  statement: extChartAt I x x in (extChartAt I x).target
  proof: (extChartAt I x).map_source mem_extChartAt_source _

中文:
定理 mem_extChartAt_target
  条件: (x : M)
  结论: extChartAt I x x in (extChartAt I x).target
  证明: (extChartAt I x).map_source mem_extChartAt_source _

Depends on / 依赖: extChartAt, map_source, mem_extChartAt_source
-/
theorem mem_extChartAt_target (x : M) : extChartAt I x x in (extChartAt I x).target :=
(extChartAt I x).map_source mem_extChartAt_source _

variable (I) in
/--
theorem `extChartAt_target` / 定理 `extChartAt_target`

English:
theorem extChartAt_target
  given: (x : M)
  proof: extend_target _

中文:
定理 extChartAt_target
  条件: (x : M)
  证明: extend_target _

Depends on / 依赖: extend_target
-/
theorem extChartAt_target (x : M) :
    (extChartAt I x).target = I.symm ⁻¹' (chartAt H x).target inter range I :=
  extend_target _

/--
theorem `uniqueDiffOn_extChartAt_target` / 定理 `uniqueDiffOn_extChartAt_target`

English:
theorem uniqueDiffOn_extChartAt_target
  given: (x : M)
  statement: UniqueDiffOn 𝕜 (extChartAt I x).target
  proof: by
  rw [extChartAt_target]
  exact I.uniqueDiffOn_preimage (chartAt H x).open_target

中文:
定理 uniqueDiffOn_extChartAt_target
  条件: (x : M)
  结论: UniqueDiffOn 𝕜 (extChartAt I x).target
  证明: by
  rw [extChartAt_target]
  exact I.uniqueDiffOn_preimage (chartAt H x).open_target

Depends on / 依赖: I.uniqueDiffOn_preimage, chartAt, extChartAt_target, open_target, uniqueDiffOn_preimage
-/
theorem uniqueDiffOn_extChartAt_target (x : M) : UniqueDiffOn 𝕜 (extChartAt I x).target := by
  rw [extChartAt_target]
  exact I.uniqueDiffOn_preimage (chartAt H x).open_target

/--
theorem `uniqueDiffWithinAt_extChartAt_target` / 定理 `uniqueDiffWithinAt_extChartAt_target`

English:
theorem uniqueDiffWithinAt_extChartAt_target
  given: (x : M)
  proof: uniqueDiffOn_extChartAt_target x _ mem_extChartAt_target x

中文:
定理 uniqueDiffWithinAt_extChartAt_target
  条件: (x : M)
  证明: uniqueDiffOn_extChartAt_target x _ mem_extChartAt_target x

Depends on / 依赖: mem_extChartAt_target, uniqueDiffOn_extChartAt_target
-/
theorem uniqueDiffWithinAt_extChartAt_target (x : M) :
    UniqueDiffWithinAt 𝕜 (extChartAt I x).target (extChartAt I x x) :=
uniqueDiffOn_extChartAt_target x _ mem_extChartAt_target x

/--
theorem `extChartAt_to_inv` / 定理 `extChartAt_to_inv`

English:
theorem extChartAt_to_inv
  given: (x : M)
  statement: (extChartAt I x).symm ((extChartAt I x) x) = x
  proof: (extChartAt I x).left_inv (mem_extChartAt_source x)

中文:
定理 extChartAt_to_inv
  条件: (x : M)
  结论: (extChartAt I x).symm ((extChartAt I x) x) = x
  证明: (extChartAt I x).left_inv (mem_extChartAt_source x)

Depends on / 依赖: extChartAt, left_inv, mem_extChartAt_source
-/
theorem extChartAt_to_inv (x : M) : (extChartAt I x).symm ((extChartAt I x) x) = x :=
  (extChartAt I x).left_inv (mem_extChartAt_source x)

/--
theorem `mapsTo_extChartAt` / 定理 `mapsTo_extChartAt`

English:
theorem mapsTo_extChartAt
  given: {x : M} (hs : s subseteq (chartAt H x).source)
  proof: mapsTo_extend _ hs

中文:
定理 mapsTo_extChartAt
  条件: {x : M} (hs : s subseteq (chartAt H x).source)
  证明: mapsTo_extend _ hs

Depends on / 依赖: mapsTo_extend
-/
theorem mapsTo_extChartAt {x : M} (hs : s subseteq (chartAt H x).source) :
    MapsTo (extChartAt I x) s ((extChartAt I x).symm ⁻¹' s inter range I) :=
  mapsTo_extend _ hs

/--
theorem `extChartAt_source_mem_nhds'` / 定理 `extChartAt_source_mem_nhds'`

English:
theorem extChartAt_source_mem_nhds'
  given: {x x' : M} (h : x' in (extChartAt I x).source)
  proof: extend_source_mem_nhds _ by rwa [← extChartAt_source I]

中文:
定理 extChartAt_source_mem_nhds'
  条件: {x x' : M} (h : x' in (extChartAt I x).source)
  证明: extend_source_mem_nhds _ by rwa [← extChartAt_source I]

Depends on / 依赖: extChartAt_source, extend_source_mem_nhds
-/
theorem extChartAt_source_mem_nhds' {x x' : M} (h : x' in (extChartAt I x).source) :
    (extChartAt I x).source in 𝓝 x' :=
extend_source_mem_nhds _ by rwa [← extChartAt_source I]

/--
theorem `extChartAt_source_mem_nhds` / 定理 `extChartAt_source_mem_nhds`

English:
theorem extChartAt_source_mem_nhds
  given: (x : M)
  statement: (extChartAt I x).source in 𝓝 x
  proof: extChartAt_source_mem_nhds' (mem_extChartAt_source x)

中文:
定理 extChartAt_source_mem_nhds
  条件: (x : M)
  结论: (extChartAt I x).source in 𝓝 x
  证明: extChartAt_source_mem_nhds' (mem_extChartAt_source x)

Depends on / 依赖: extChartAt_source_mem_nhds, mem_extChartAt_source
-/
theorem extChartAt_source_mem_nhds (x : M) : (extChartAt I x).source in 𝓝 x :=
  extChartAt_source_mem_nhds' (mem_extChartAt_source x)

/--
theorem `extChartAt_source_mem_nhdsWithin'` / 定理 `extChartAt_source_mem_nhdsWithin'`

English:
theorem extChartAt_source_mem_nhdsWithin'
  given: {x x' : M} (h : x' in (extChartAt I x).source)
  proof: mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds' h)

中文:
定理 extChartAt_source_mem_nhdsWithin'
  条件: {x x' : M} (h : x' in (extChartAt I x).source)
  证明: mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds' h)

Depends on / 依赖: extChartAt_source_mem_nhds, mem_nhdsWithin_of_mem_nhds
-/
theorem extChartAt_source_mem_nhdsWithin' {x x' : M} (h : x' in (extChartAt I x).source) :
    (extChartAt I x).source in 𝓝[s] x' :=
  mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds' h)

/--
theorem `extChartAt_source_mem_nhdsWithin` / 定理 `extChartAt_source_mem_nhdsWithin`

English:
theorem extChartAt_source_mem_nhdsWithin
  given: (x : M)
  statement: (extChartAt I x).source in 𝓝[s] x
  proof: mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds x)

中文:
定理 extChartAt_source_mem_nhdsWithin
  条件: (x : M)
  结论: (extChartAt I x).source in 𝓝[s] x
  证明: mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds x)

Depends on / 依赖: extChartAt_source_mem_nhds, mem_nhdsWithin_of_mem_nhds
-/
theorem extChartAt_source_mem_nhdsWithin (x : M) : (extChartAt I x).source in 𝓝[s] x :=
  mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds x)

/--
theorem `continuousOn_extChartAt` / 定理 `continuousOn_extChartAt`

English:
theorem continuousOn_extChartAt
  given: (x : M)
  statement: ContinuousOn (extChartAt I x) (extChartAt I x).source
  proof: continuousOn_extend _

中文:
定理 continuousOn_extChartAt
  条件: (x : M)
  结论: ContinuousOn (extChartAt I x) (extChartAt I x).source
  证明: continuousOn_extend _

Depends on / 依赖: continuousOn_extend
-/
theorem continuousOn_extChartAt (x : M) : ContinuousOn (extChartAt I x) (extChartAt I x).source :=
  continuousOn_extend _

/--
theorem `continuousAt_extChartAt'` / 定理 `continuousAt_extChartAt'`

English:
theorem continuousAt_extChartAt'
  given: {x x' : M} (h : x' in (extChartAt I x).source)
  proof: continuousAt_extend _ by rwa [← extChartAt_source I]

中文:
定理 continuousAt_extChartAt'
  条件: {x x' : M} (h : x' in (extChartAt I x).source)
  证明: continuousAt_extend _ by rwa [← extChartAt_source I]

Depends on / 依赖: continuousAt_extend, extChartAt_source
-/
theorem continuousAt_extChartAt' {x x' : M} (h : x' in (extChartAt I x).source) :
    ContinuousAt (extChartAt I x) x' :=
continuousAt_extend _ by rwa [← extChartAt_source I]

/--
theorem `continuousAt_extChartAt` / 定理 `continuousAt_extChartAt`

English:
theorem continuousAt_extChartAt
  given: (x : M)
  statement: ContinuousAt (extChartAt I x) x
  proof: continuousAt_extChartAt' (mem_extChartAt_source x)

中文:
定理 continuousAt_extChartAt
  条件: (x : M)
  结论: ContinuousAt (extChartAt I x) x
  证明: continuousAt_extChartAt' (mem_extChartAt_source x)

Depends on / 依赖: continuousAt_extChartAt, mem_extChartAt_source
-/
theorem continuousAt_extChartAt (x : M) : ContinuousAt (extChartAt I x) x :=
  continuousAt_extChartAt' (mem_extChartAt_source x)

/--
theorem `map_extChartAt_nhds'` / 定理 `map_extChartAt_nhds'`

English:
theorem map_extChartAt_nhds'
  given: {x y : M} (hy : y in (extChartAt I x).source)
  proof: map_extend_nhds _ by rwa [← extChartAt_source I]

中文:
定理 map_extChartAt_nhds'
  条件: {x y : M} (hy : y in (extChartAt I x).source)
  证明: map_extend_nhds _ by rwa [← extChartAt_source I]

Depends on / 依赖: extChartAt_source, map_extend_nhds
-/
theorem map_extChartAt_nhds' {x y : M} (hy : y in (extChartAt I x).source) :
    map (extChartAt I x) (𝓝 y) = 𝓝[range I] extChartAt I x y :=
map_extend_nhds _ by rwa [← extChartAt_source I]

/--
theorem `map_extChartAt_nhds` / 定理 `map_extChartAt_nhds`

English:
theorem map_extChartAt_nhds
  given: (x : M)
  statement: map (extChartAt I x) (𝓝 x) = 𝓝[range I] extChartAt I x x
  proof: map_extChartAt_nhds' mem_extChartAt_source x

中文:
定理 map_extChartAt_nhds
  条件: (x : M)
  结论: map (extChartAt I x) (𝓝 x) = 𝓝[range I] extChartAt I x x
  证明: map_extChartAt_nhds' mem_extChartAt_source x

Depends on / 依赖: map_extChartAt_nhds, mem_extChartAt_source
-/
theorem map_extChartAt_nhds (x : M) : map (extChartAt I x) (𝓝 x) = 𝓝[range I] extChartAt I x x :=
map_extChartAt_nhds' mem_extChartAt_source x

/--
theorem `map_extChartAt_nhds_of_boundaryless` / 定理 `map_extChartAt_nhds_of_boundaryless`

English:
theorem map_extChartAt_nhds_of_boundaryless
  given: [I.Boundaryless] (x : M)
  proof: by
  rw [extChartAt]
  exact map_extend_nhds_of_boundaryless (chartAt H x) (mem_chart_source H x)

中文:
定理 map_extChartAt_nhds_of_boundaryless
  条件: [I.无边界] (x : M)
  证明: by
  rw [extChartAt]
  exact map_extend_nhds_of_boundaryless (chartAt H x) (mem_chart_source H x)

Depends on / 依赖: chartAt, extChartAt, map_extend_nhds_of_boundaryless, mem_chart_source
-/
theorem map_extChartAt_nhds_of_boundaryless [I.Boundaryless] (x : M) :
    map (extChartAt I x) (𝓝 x) = 𝓝 (extChartAt I x x) := by
  rw [extChartAt]
  exact map_extend_nhds_of_boundaryless (chartAt H x) (mem_chart_source H x)

/--
theorem `extChartAt_image_nhds_mem_nhds_of_mem_interior_range` / 定理 `extChartAt_image_nhds_mem_nhds_of_mem_interior_range`

English:
theorem extChartAt_image_nhds_mem_nhds_of_mem_interior_range
  statement: {x y}
  proof: by
  rw [extChartAt]
  exact extend_image_nhds_mem_nhds_of_mem_interior_range _ (by simpa using hx) h'x h

中文:
定理 extChartAt_image_nhds_mem_nhds_of_mem_interior_range
  结论: {x y}
  证明: by
  rw [extChartAt]
  exact extend_image_nhds_mem_nhds_of_mem_interior_range _ (by simpa using hx) h'x h

Depends on / 依赖: extChartAt, extend_image_nhds_mem_nhds_of_mem_interior_range
-/
theorem extChartAt_image_nhds_mem_nhds_of_mem_interior_range {x y}
    (hx : y in (extChartAt I x).source)
    (h'x : extChartAt I x y in interior (range I)) {s : Set M} (h : s in 𝓝 y) :
    (extChartAt I x) '' s in 𝓝 (extChartAt I x y) := by
  rw [extChartAt]
  exact extend_image_nhds_mem_nhds_of_mem_interior_range _ (by simpa using hx) h'x h

variable {x} in
/--
theorem `extChartAt_image_nhds_mem_nhds_of_boundaryless` / 定理 `extChartAt_image_nhds_mem_nhds_of_boundaryless`

English:
theorem extChartAt_image_nhds_mem_nhds_of_boundaryless
  statement: [I.Boundaryless]
  proof: by
  rw [extChartAt]
  exact extend_image_nhds_mem_nhds_of_boundaryless _ (mem_chart_source H x) hx

中文:
定理 extChartAt_image_nhds_mem_nhds_of_boundaryless
  结论: [I.无边界]
  证明: by
  rw [extChartAt]
  exact extend_image_nhds_mem_nhds_of_boundaryless _ (mem_chart_source H x) hx

Depends on / 依赖: extChartAt, extend_image_nhds_mem_nhds_of_boundaryless, mem_chart_source
-/
theorem extChartAt_image_nhds_mem_nhds_of_boundaryless [I.Boundaryless]
    {x : M} (hx : s in 𝓝 x) : extChartAt I x '' s in 𝓝 (extChartAt I x x) := by
  rw [extChartAt]
  exact extend_image_nhds_mem_nhds_of_boundaryless _ (mem_chart_source H x) hx

/--
theorem `extChartAt_target_mem_nhdsWithin'` / 定理 `extChartAt_target_mem_nhdsWithin'`

English:
theorem extChartAt_target_mem_nhdsWithin'
  given: {x y : M} (hy : y in (extChartAt I x).source)
  proof: extend_target_mem_nhdsWithin _ by rwa [← extChartAt_source I]

中文:
定理 extChartAt_target_mem_nhdsWithin'
  条件: {x y : M} (hy : y in (extChartAt I x).source)
  证明: extend_target_mem_nhdsWithin _ by rwa [← extChartAt_source I]

Depends on / 依赖: extChartAt_source, extend_target_mem_nhdsWithin
-/
theorem extChartAt_target_mem_nhdsWithin' {x y : M} (hy : y in (extChartAt I x).source) :
    (extChartAt I x).target in 𝓝[range I] extChartAt I x y :=
extend_target_mem_nhdsWithin _ by rwa [← extChartAt_source I]

/--
theorem `extChartAt_target_mem_nhdsWithin` / 定理 `extChartAt_target_mem_nhdsWithin`

English:
theorem extChartAt_target_mem_nhdsWithin
  given: (x : M)
  proof: extChartAt_target_mem_nhdsWithin' (mem_extChartAt_source x)

中文:
定理 extChartAt_target_mem_nhdsWithin
  条件: (x : M)
  证明: extChartAt_target_mem_nhdsWithin' (mem_extChartAt_source x)

Depends on / 依赖: extChartAt_target_mem_nhdsWithin, mem_extChartAt_source
-/
theorem extChartAt_target_mem_nhdsWithin (x : M) :
    (extChartAt I x).target in 𝓝[range I] extChartAt I x x :=
  extChartAt_target_mem_nhdsWithin' (mem_extChartAt_source x)

/--
theorem `extChartAt_target_mem_nhdsWithin_of_mem` / 定理 `extChartAt_target_mem_nhdsWithin_of_mem`

English:
theorem extChartAt_target_mem_nhdsWithin_of_mem
  given: {x : M} {y : E} (hy : y in (extChartAt I x).target)
  proof: by
  rw [← (extChartAt I x).right_inv hy]
  apply extChartAt_target_mem_nhdsWithin'
  exact (extChartAt I x).map_target hy

中文:
定理 extChartAt_target_mem_nhdsWithin_of_mem
  条件: {x : M} {y : E} (hy : y in (extChartAt I x).target)
  证明: by
  rw [← (extChartAt I x).right_inv hy]
  apply extChartAt_target_mem_nhdsWithin'
  exact (extChartAt I x).map_target hy

Depends on / 依赖: extChartAt, extChartAt_target_mem_nhdsWithin, map_target, right_inv
-/
theorem extChartAt_target_mem_nhdsWithin_of_mem {x : M} {y : E} (hy : y in (extChartAt I x).target) :
    (extChartAt I x).target in 𝓝[range I] y := by
  rw [← (extChartAt I x).right_inv hy]
  apply extChartAt_target_mem_nhdsWithin'
  exact (extChartAt I x).map_target hy

/--
theorem `extChartAt_target_union_compl_range_mem_nhds_of_mem` / 定理 `extChartAt_target_union_compl_range_mem_nhds_of_mem`

English:
theorem extChartAt_target_union_compl_range_mem_nhds_of_mem
  statement: {y : E} {x : M}
  proof: by
  rw [← nhdsWithin_univ]; rw [← union_compl_self (range I)]; rw [nhdsWithin_union]
  exact Filter.union_mem_sup (extChartAt_target_mem_nhdsWithin_of_mem hy) self_mem_nhdsWithin

中文:
定理 extChartAt_target_union_compl_range_mem_nhds_of_mem
  结论: {y : E} {x : M}
  证明: by
  rw [← nhdsWithin_univ]; rw [← union_compl_self (range I)]; rw [nhdsWithin_union]
  exact Filter.union_mem_sup (extChartAt_target_mem_nhdsWithin_of_mem hy) self_mem_nhdsWithin

Depends on / 依赖: Filter, Filter.union_mem_sup, extChartAt_target_mem_nhdsWithin_of_mem, nhdsWithin_union, nhdsWithin_univ, self_mem_nhdsWithin, union_compl_self, union_mem_sup
-/
theorem extChartAt_target_union_compl_range_mem_nhds_of_mem {y : E} {x : M}
    (hy : y in (extChartAt I x).target) : (extChartAt I x).target union (range I)ᶜ in 𝓝 y := by
  rw [← nhdsWithin_univ]; rw [← union_compl_self (range I)]; rw [nhdsWithin_union]
  exact Filter.union_mem_sup (extChartAt_target_mem_nhdsWithin_of_mem hy) self_mem_nhdsWithin

/--
theorem `isOpen_extChartAt_target` / 定理 `isOpen_extChartAt_target`

English:
theorem isOpen_extChartAt_target
  given: [I.Boundaryless] (x : M)
  statement: IsOpen (extChartAt I x).target
  proof: by
  simp_rw [extChartAt_target, I.range_eq_univ, inter_univ]
  exact (OpenPartialHomeomorph.open_target _).preimage I.continuous_symm

中文:
定理 isOpen_extChartAt_target
  条件: [I.无边界] (x : M)
  结论: 是开集 (extChartAt I x).target
  证明: by
  simp_rw [extChartAt_target, I.range_eq_univ, inter_univ]
  exact (OpenPartialHomeomorph.open_target _).preimage I.continuous_symm

Depends on / 依赖: I.continuous_symm, I.range_eq_univ, OpenPartialHomeomorph, OpenPartialHomeomorph.open_target, continuous_symm, extChartAt_target, inter_univ, open_target, preimage, range_eq_univ, simp_rw
-/
theorem isOpen_extChartAt_target [I.Boundaryless] (x : M) : IsOpen (extChartAt I x).target := by
  simp_rw [extChartAt_target, I.range_eq_univ, inter_univ]
  exact (OpenPartialHomeomorph.open_target _).preimage I.continuous_symm

/--
theorem `extChartAt_target_mem_nhds` / 定理 `extChartAt_target_mem_nhds`

English:
theorem extChartAt_target_mem_nhds
  given: [I.Boundaryless] (x : M)
  proof: by
  convert! extChartAt_target_mem_nhdsWithin x
  simp only [I.range_eq_univ, nhdsWithin_univ]

中文:
定理 extChartAt_target_mem_nhds
  条件: [I.无边界] (x : M)
  证明: by
  convert! extChartAt_target_mem_nhdsWithin x
  simp only [I.range_eq_univ, nhdsWithin_univ]

Depends on / 依赖: I.range_eq_univ, convert, extChartAt_target_mem_nhdsWithin, nhdsWithin_univ, range_eq_univ
-/
theorem extChartAt_target_mem_nhds [I.Boundaryless] (x : M) :
    (extChartAt I x).target in 𝓝 (extChartAt I x x) := by
  convert! extChartAt_target_mem_nhdsWithin x
  simp only [I.range_eq_univ, nhdsWithin_univ]

/--
theorem `extChartAt_target_mem_nhds'` / 定理 `extChartAt_target_mem_nhds'`

English:
theorem extChartAt_target_mem_nhds'
  statement: [I.Boundaryless] {x : M} {y : E}
  proof: (isOpen_extChartAt_target x).mem_nhds m

中文:
定理 extChartAt_target_mem_nhds'
  结论: [I.无边界] {x : M} {y : E}
  证明: (isOpen_extChartAt_target x).mem_nhds m

Depends on / 依赖: isOpen_extChartAt_target, mem_nhds
-/
theorem extChartAt_target_mem_nhds' [I.Boundaryless] {x : M} {y : E}
    (m : y in (extChartAt I x).target) : (extChartAt I x).target in 𝓝 y :=
  (isOpen_extChartAt_target x).mem_nhds m

/--
theorem `extChartAt_target_subset_range` / 定理 `extChartAt_target_subset_range`

English:
theorem extChartAt_target_subset_range
  given: (x : M)
  statement: (extChartAt I x).target subseteq range I
  proof: by
  simp only [mfld_simps]

中文:
定理 extChartAt_target_subset_range
  条件: (x : M)
  结论: (extChartAt I x).target subseteq range I
  证明: by
  simp only [mfld_simps]

Depends on / 依赖: mfld_simps
-/
theorem extChartAt_target_subset_range (x : M) : (extChartAt I x).target subseteq range I := by
  simp only [mfld_simps]

/--
theorem `nhdsWithin_extChartAt_target_eq'` / 定理 `nhdsWithin_extChartAt_target_eq'`

English:
theorem nhdsWithin_extChartAt_target_eq'
  given: {x y : M} (hy : y in (extChartAt I x).source)
  proof: nhdsWithin_extend_target_eq _ by rwa [← extChartAt_source I]

中文:
定理 nhdsWithin_extChartAt_target_eq'
  条件: {x y : M} (hy : y in (extChartAt I x).source)
  证明: nhdsWithin_extend_target_eq _ by rwa [← extChartAt_source I]

Depends on / 依赖: extChartAt_source, nhdsWithin_extend_target_eq
-/
theorem nhdsWithin_extChartAt_target_eq' {x y : M} (hy : y in (extChartAt I x).source) :
    𝓝[(extChartAt I x).target] extChartAt I x y = 𝓝[range I] extChartAt I x y :=
nhdsWithin_extend_target_eq _ by rwa [← extChartAt_source I]

/--
theorem `nhdsWithin_extChartAt_target_eq_of_mem` / 定理 `nhdsWithin_extChartAt_target_eq_of_mem`

English:
theorem nhdsWithin_extChartAt_target_eq_of_mem
  given: {x : M} {z : E} (hz : z in (extChartAt I x).target)
  proof: by
  rw [← PartialEquiv.right_inv (extChartAt I x) hz]
  exact nhdsWithin_extChartAt_target_eq' ((extChartAt I x).map_target hz)

中文:
定理 nhdsWithin_extChartAt_target_eq_of_mem
  条件: {x : M} {z : E} (hz : z in (extChartAt I x).target)
  证明: by
  rw [← PartialEquiv.right_inv (extChartAt I x) hz]
  exact nhdsWithin_extChartAt_target_eq' ((extChartAt I x).map_target hz)

Depends on / 依赖: PartialEquiv, PartialEquiv.right_inv, extChartAt, map_target, nhdsWithin_extChartAt_target_eq, right_inv
-/
theorem nhdsWithin_extChartAt_target_eq_of_mem {x : M} {z : E} (hz : z in (extChartAt I x).target) :
    𝓝[(extChartAt I x).target] z = 𝓝[range I] z := by
  rw [← PartialEquiv.right_inv (extChartAt I x) hz]
  exact nhdsWithin_extChartAt_target_eq' ((extChartAt I x).map_target hz)

/--
theorem `nhdsWithin_extChartAt_target_eq` / 定理 `nhdsWithin_extChartAt_target_eq`

English:
theorem nhdsWithin_extChartAt_target_eq
  given: (x : M)
  proof: nhdsWithin_extChartAt_target_eq' (mem_extChartAt_source x)

中文:
定理 nhdsWithin_extChartAt_target_eq
  条件: (x : M)
  证明: nhdsWithin_extChartAt_target_eq' (mem_extChartAt_source x)

Depends on / 依赖: mem_extChartAt_source, nhdsWithin_extChartAt_target_eq
-/
theorem nhdsWithin_extChartAt_target_eq (x : M) :
    𝓝[(extChartAt I x).target] (extChartAt I x) x = 𝓝[range I] (extChartAt I x) x :=
  nhdsWithin_extChartAt_target_eq' (mem_extChartAt_source x)

/--
theorem `extChartAt_target_eventuallyEq'` / 定理 `extChartAt_target_eventuallyEq'`

English:
theorem extChartAt_target_eventuallyEq'
  given: {x y : M} (hy : y in (extChartAt I x).source)
  proof: nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extChartAt_target_eq' hy)

中文:
定理 extChartAt_target_eventuallyEq'
  条件: {x y : M} (hy : y in (extChartAt I x).source)
  证明: nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extChartAt_target_eq' hy)

Depends on / 依赖: nhdsWithin_eq_iff_eventuallyEq, nhdsWithin_extChartAt_target_eq
-/
theorem extChartAt_target_eventuallyEq' {x y : M} (hy : y in (extChartAt I x).source) :
    (extChartAt I x).target =ᶠ[𝓝 (extChartAt I x y)] range I :=
  nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extChartAt_target_eq' hy)

/--
theorem `extChartAt_target_eventuallyEq_of_mem` / 定理 `extChartAt_target_eventuallyEq_of_mem`

English:
theorem extChartAt_target_eventuallyEq_of_mem
  given: {x : M} {z : E} (hz : z in (extChartAt I x).target)
  proof: nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extChartAt_target_eq_of_mem hz)

中文:
定理 extChartAt_target_eventuallyEq_of_mem
  条件: {x : M} {z : E} (hz : z in (extChartAt I x).target)
  证明: nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extChartAt_target_eq_of_mem hz)

Depends on / 依赖: nhdsWithin_eq_iff_eventuallyEq, nhdsWithin_extChartAt_target_eq_of_mem
-/
theorem extChartAt_target_eventuallyEq_of_mem {x : M} {z : E} (hz : z in (extChartAt I x).target) :
    (extChartAt I x).target =ᶠ[𝓝 z] range I :=
  nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extChartAt_target_eq_of_mem hz)

/--
theorem `extChartAt_target_eventuallyEq` / 定理 `extChartAt_target_eventuallyEq`

English:
theorem extChartAt_target_eventuallyEq
  given: {x : M}
  proof: nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extChartAt_target_eq x)

中文:
定理 extChartAt_target_eventuallyEq
  条件: {x : M}
  证明: nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extChartAt_target_eq x)

Depends on / 依赖: nhdsWithin_eq_iff_eventuallyEq, nhdsWithin_extChartAt_target_eq
-/
theorem extChartAt_target_eventuallyEq {x : M} :
    (extChartAt I x).target =ᶠ[𝓝 (extChartAt I x x)] range I :=
  nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extChartAt_target_eq x)

/--
theorem `continuousAt_extChartAt_symm''` / 定理 `continuousAt_extChartAt_symm''`

English:
theorem continuousAt_extChartAt_symm''
  given: {x : M} {y : E} (h : y in (extChartAt I x).target)
  proof: continuousAt_extend_symm' _ h

中文:
定理 continuousAt_extChartAt_symm''
  条件: {x : M} {y : E} (h : y in (extChartAt I x).target)
  证明: continuousAt_extend_symm' _ h

Depends on / 依赖: continuousAt_extend_symm
-/
theorem continuousAt_extChartAt_symm'' {x : M} {y : E} (h : y in (extChartAt I x).target) :
    ContinuousAt (extChartAt I x).symm y :=
  continuousAt_extend_symm' _ h

/--
theorem `continuousAt_extChartAt_symm'` / 定理 `continuousAt_extChartAt_symm'`

English:
theorem continuousAt_extChartAt_symm'
  given: {x x' : M} (h : x' in (extChartAt I x).source)
  proof: continuousAt_extChartAt_symm'' (extChartAt I x).map_source h

中文:
定理 continuousAt_extChartAt_symm'
  条件: {x x' : M} (h : x' in (extChartAt I x).source)
  证明: continuousAt_extChartAt_symm'' (extChartAt I x).map_source h

Depends on / 依赖: continuousAt_extChartAt_symm, extChartAt, map_source
-/
theorem continuousAt_extChartAt_symm' {x x' : M} (h : x' in (extChartAt I x).source) :
    ContinuousAt (extChartAt I x).symm (extChartAt I x x') :=
continuousAt_extChartAt_symm'' (extChartAt I x).map_source h

/--
theorem `continuousAt_extChartAt_symm` / 定理 `continuousAt_extChartAt_symm`

English:
theorem continuousAt_extChartAt_symm
  given: (x : M)
  proof: continuousAt_extChartAt_symm' (mem_extChartAt_source x)

中文:
定理 continuousAt_extChartAt_symm
  条件: (x : M)
  证明: continuousAt_extChartAt_symm' (mem_extChartAt_source x)

Depends on / 依赖: continuousAt_extChartAt_symm, mem_extChartAt_source
-/
theorem continuousAt_extChartAt_symm (x : M) :
    ContinuousAt (extChartAt I x).symm ((extChartAt I x) x) :=
  continuousAt_extChartAt_symm' (mem_extChartAt_source x)

/--
theorem `continuousOn_extChartAt_symm` / 定理 `continuousOn_extChartAt_symm`

English:
theorem continuousOn_extChartAt_symm
  given: (x : M)
  proof: fun _y hy => (continuousAt_extChartAt_symm'' hy).continuousWithinAt

中文:
定理 continuousOn_extChartAt_symm
  条件: (x : M)
  证明: fun _y hy => (continuousAt_extChartAt_symm'' hy).continuousWithinAt

Depends on / 依赖: continuousAt_extChartAt_symm, continuousWithinAt
-/
theorem continuousOn_extChartAt_symm (x : M) :
    ContinuousOn (extChartAt I x).symm (extChartAt I x).target :=
  fun _y hy => (continuousAt_extChartAt_symm'' hy).continuousWithinAt

/--
lemma `extChartAt_target_subset_closure_interior` / 引理 `extChartAt_target_subset_closure_interior`

English:
lemma extChartAt_target_subset_closure_interior
  given: {x : M}
  proof: by
  intro y hy
  rw [mem_closure_iff_nhds]
  intro t ht
  have A : t inter ((extChartAt I x).target union (range I)ᶜ) in 𝓝 y :=
    inter_mem ht (extChartAt_target_union_compl_range_mem_nhds_of_mem hy)
  have B : y in closure (interior (range I)) := by
    apply I.range_subset_closure_interior (ext

中文:
引理 extChartAt_target_subset_closure_interior
  条件: {x : M}
  证明: by
  intro y hy
  rw [mem_closure_iff_nhds]
  intro t ht
  have A : t inter ((extChartAt I x).target union (range I)ᶜ) in 𝓝 y :=
    inter_mem ht (extChartAt_target_union_compl_range_mem_nhds_of_mem hy)
  have B : y in closure (interior (range I)) := by
    apply I.range_subset_closure_interior (ext

Depends on / 依赖: I.range_subset_closure_interior, Nonempty, closure, extChartAt, extChartAt_target_subset_range, extChartAt_target_union_compl_range_mem_nhds_of_mem, inter_mem, interior, mem_closure_iff_nhds, range_subset_closure_interior, target
-/
lemma extChartAt_target_subset_closure_interior {x : M} :
    (extChartAt I x).target subseteq closure (interior (extChartAt I x).target) := by
  intro y hy
  rw [mem_closure_iff_nhds]
  intro t ht
  have A : t inter ((extChartAt I x).target union (range I)ᶜ) in 𝓝 y :=
    inter_mem ht (extChartAt_target_union_compl_range_mem_nhds_of_mem hy)
  have B : y in closure (interior (range I)) := by
    apply I.range_subset_closure_interior (extChartAt_target_subset_range x hy)
  obtain ⟨z, ⟨tz, h'z⟩, hz⟩ :
      (t inter ((extChartAt I x).target union (range ↑I)ᶜ) inter interior (range I)).Nonempty :=
    mem_closure_iff_nhds.1 B _ A
  refine ⟨z, ⟨tz, ?_⟩⟩
  have h''z : z in (extChartAt I x).target := by simpa [interior_subset hz] using h'z
  exact (extChartAt_target_eventuallyEq_of_mem h''z).symm.mem_interior hz

variable (I) in
/--
theorem `interior_extChartAt_target_nonempty` / 定理 `interior_extChartAt_target_nonempty`

English:
theorem interior_extChartAt_target_nonempty
  given: (x : M)
  proof: by
  by_contra! H
  have := extChartAt_target_subset_closure_interior (mem_extChartAt_target (I := I) x)
  simp only [H, closure_empty, mem_empty_iff_false] at this

中文:
定理 interior_extChartAt_target_nonempty
  条件: (x : M)
  证明: by
  by_contra! H
  have := extChartAt_target_subset_closure_interior (mem_extChartAt_target (I := I) x)
  simp only [H, closure_empty, mem_empty_iff_false] at this

Depends on / 依赖: closure_empty, extChartAt_target_subset_closure_interior, mem_empty_iff_false, mem_extChartAt_target
-/
theorem interior_extChartAt_target_nonempty (x : M) :
    (interior (extChartAt I x).target).Nonempty := by
  by_contra! H
  have := extChartAt_target_subset_closure_interior (mem_extChartAt_target (I := I) x)
  simp only [H, closure_empty, mem_empty_iff_false] at this

/--
lemma `extChartAt_mem_closure_interior` / 引理 `extChartAt_mem_closure_interior`

English:
lemma extChartAt_mem_closure_interior
  statement: {x₀ x : M}
  proof: by
  simp_rw [mem_closure_iff, interior_inter, ← inter_assoc]
  intro o o_open ho
  obtain ⟨y, ⟨yo, hy⟩, ys⟩ :
      ((extChartAt I x₀) ⁻¹' o inter (extChartAt I x₀).source inter interior s).Nonempty := by
    have : (extChartAt I x₀) ⁻¹' o in 𝓝 x := by
      apply (continuousAt_extChartAt' h'x).pre

中文:
引理 extChartAt_mem_closure_interior
  结论: {x₀ x : M}
  证明: by
  simp_rw [mem_closure_iff, interior_inter, ← inter_assoc]
  intro o o_open ho
  obtain ⟨y, ⟨yo, hy⟩, ys⟩ :
      ((extChartAt I x₀) ⁻¹' o inter (extChartAt I x₀).source inter interior s).Nonempty := by
    have : (extChartAt I x₀) ⁻¹' o in 𝓝 x := by
      apply (continuousAt_extChartAt' h'x).pre

Depends on / 依赖: Nonempty, continuousAt_extChartAt, extChartAt, inter_assoc, inter_mem, interior, interior_inter, isOpen_extChartAt_source, mem_closure_iff, mem_closure_iff_nhds, mem_nhds, o_open, o_open.mem_nhds, preimage_mem_nhds, simp_rw, source
-/
lemma extChartAt_mem_closure_interior {x₀ x : M}
    (hx : x in closure (interior s)) (h'x : x in (extChartAt I x₀).source) :
    extChartAt I x₀ x in
      closure (interior ((extChartAt I x₀).symm ⁻¹' s inter (extChartAt I x₀).target)) := by
  simp_rw [mem_closure_iff, interior_inter, ← inter_assoc]
  intro o o_open ho
  obtain ⟨y, ⟨yo, hy⟩, ys⟩ :
      ((extChartAt I x₀) ⁻¹' o inter (extChartAt I x₀).source inter interior s).Nonempty := by
    have : (extChartAt I x₀) ⁻¹' o in 𝓝 x := by
      apply (continuousAt_extChartAt' h'x).preimage_mem_nhds (o_open.mem_nhds ho)
    refine (mem_closure_iff_nhds.1 hx) _ (inter_mem this ?_)
    apply (isOpen_extChartAt_source x₀).mem_nhds h'x
  have A : interior (↑(extChartAt I x₀).symm ⁻¹' s) in 𝓝 (extChartAt I x₀ y) := by
    simp only [interior_mem_nhds]
    apply (continuousAt_extChartAt_symm' hy).preimage_mem_nhds
    simp only [hy, PartialEquiv.left_inv]
    exact mem_interior_iff_mem_nhds.mp ys
  have B : (extChartAt I x₀) y in closure (interior (extChartAt I x₀).target) := by
    apply extChartAt_target_subset_closure_interior (x := x₀)
    exact (extChartAt I x₀).map_source hy
  exact mem_closure_iff_nhds.1 B _ (inter_mem (o_open.mem_nhds yo) A)

/--
theorem `isOpen_extChartAt_preimage'` / 定理 `isOpen_extChartAt_preimage'`

English:
theorem isOpen_extChartAt_preimage'
  given: (x : M) {s : Set E} (hs : IsOpen s)
  proof: isOpen_extend_preimage' _ hs

中文:
定理 isOpen_extChartAt_preimage'
  条件: (x : M) {s : 集合 E} (hs : 是开集 s)
  证明: isOpen_extend_preimage' _ hs

Depends on / 依赖: isOpen_extend_preimage
-/
theorem isOpen_extChartAt_preimage' (x : M) {s : Set E} (hs : IsOpen s) :
    IsOpen ((extChartAt I x).source inter extChartAt I x ⁻¹' s) :=
  isOpen_extend_preimage' _ hs

/--
theorem `isOpen_extChartAt_preimage` / 定理 `isOpen_extChartAt_preimage`

English:
theorem isOpen_extChartAt_preimage
  given: (x : M) {s : Set E} (hs : IsOpen s)
  proof: by
  rw [← extChartAt_source I]
  exact isOpen_extChartAt_preimage' x hs

中文:
定理 isOpen_extChartAt_preimage
  条件: (x : M) {s : 集合 E} (hs : 是开集 s)
  证明: by
  rw [← extChartAt_source I]
  exact isOpen_extChartAt_preimage' x hs

Depends on / 依赖: extChartAt_source, isOpen_extChartAt_preimage
-/
theorem isOpen_extChartAt_preimage (x : M) {s : Set E} (hs : IsOpen s) :
    IsOpen ((chartAt H x).source inter extChartAt I x ⁻¹' s) := by
  rw [← extChartAt_source I]
  exact isOpen_extChartAt_preimage' x hs

/--
theorem `map_extChartAt_nhdsWithin_eq_image'` / 定理 `map_extChartAt_nhdsWithin_eq_image'`

English:
theorem map_extChartAt_nhdsWithin_eq_image'
  given: {x y : M} (hy : y in (extChartAt I x).source)
  proof: map_extend_nhdsWithin_eq_image _ by rwa [← extChartAt_source I]

中文:
定理 map_extChartAt_nhdsWithin_eq_image'
  条件: {x y : M} (hy : y in (extChartAt I x).source)
  证明: map_extend_nhdsWithin_eq_image _ by rwa [← extChartAt_source I]

Depends on / 依赖: extChartAt_source, map_extend_nhdsWithin_eq_image
-/
theorem map_extChartAt_nhdsWithin_eq_image' {x y : M} (hy : y in (extChartAt I x).source) :
    map (extChartAt I x) (𝓝[s] y) =
      𝓝[extChartAt I x '' ((extChartAt I x).source inter s)] extChartAt I x y :=
map_extend_nhdsWithin_eq_image _ by rwa [← extChartAt_source I]

/--
theorem `map_extChartAt_nhdsWithin_eq_image` / 定理 `map_extChartAt_nhdsWithin_eq_image`

English:
theorem map_extChartAt_nhdsWithin_eq_image
  given: (x : M)
  proof: map_extChartAt_nhdsWithin_eq_image' (mem_extChartAt_source x)

中文:
定理 map_extChartAt_nhdsWithin_eq_image
  条件: (x : M)
  证明: map_extChartAt_nhdsWithin_eq_image' (mem_extChartAt_source x)

Depends on / 依赖: map_extChartAt_nhdsWithin_eq_image, mem_extChartAt_source
-/
theorem map_extChartAt_nhdsWithin_eq_image (x : M) :
    map (extChartAt I x) (𝓝[s] x) =
      𝓝[extChartAt I x '' ((extChartAt I x).source inter s)] extChartAt I x x :=
  map_extChartAt_nhdsWithin_eq_image' (mem_extChartAt_source x)

/--
theorem `map_extChartAt_nhdsWithin'` / 定理 `map_extChartAt_nhdsWithin'`

English:
theorem map_extChartAt_nhdsWithin'
  given: {x y : M} (hy : y in (extChartAt I x).source)
  proof: map_extend_nhdsWithin _ by rwa [← extChartAt_source I]

中文:
定理 map_extChartAt_nhdsWithin'
  条件: {x y : M} (hy : y in (extChartAt I x).source)
  证明: map_extend_nhdsWithin _ by rwa [← extChartAt_source I]

Depends on / 依赖: extChartAt_source, map_extend_nhdsWithin
-/
theorem map_extChartAt_nhdsWithin' {x y : M} (hy : y in (extChartAt I x).source) :
    map (extChartAt I x) (𝓝[s] y) = 𝓝[(extChartAt I x).symm ⁻¹' s inter range I] extChartAt I x y :=
map_extend_nhdsWithin _ by rwa [← extChartAt_source I]

/--
theorem `map_extChartAt_nhdsWithin` / 定理 `map_extChartAt_nhdsWithin`

English:
theorem map_extChartAt_nhdsWithin
  given: (x : M)
  proof: map_extChartAt_nhdsWithin' (mem_extChartAt_source x)

中文:
定理 map_extChartAt_nhdsWithin
  条件: (x : M)
  证明: map_extChartAt_nhdsWithin' (mem_extChartAt_source x)

Depends on / 依赖: map_extChartAt_nhdsWithin, mem_extChartAt_source
-/
theorem map_extChartAt_nhdsWithin (x : M) :
    map (extChartAt I x) (𝓝[s] x) = 𝓝[(extChartAt I x).symm ⁻¹' s inter range I] extChartAt I x x :=
  map_extChartAt_nhdsWithin' (mem_extChartAt_source x)

/--
theorem `map_extChartAt_symm_nhdsWithin'` / 定理 `map_extChartAt_symm_nhdsWithin'`

English:
theorem map_extChartAt_symm_nhdsWithin'
  given: {x y : M} (hy : y in (extChartAt I x).source)
  proof: map_extend_symm_nhdsWithin _ by rwa [← extChartAt_source I]

中文:
定理 map_extChartAt_symm_nhdsWithin'
  条件: {x y : M} (hy : y in (extChartAt I x).source)
  证明: map_extend_symm_nhdsWithin _ by rwa [← extChartAt_source I]

Depends on / 依赖: extChartAt_source, map_extend_symm_nhdsWithin
-/
theorem map_extChartAt_symm_nhdsWithin' {x y : M} (hy : y in (extChartAt I x).source) :
    map (extChartAt I x).symm (𝓝[(extChartAt I x).symm ⁻¹' s inter range I] extChartAt I x y) =
      𝓝[s] y :=
map_extend_symm_nhdsWithin _ by rwa [← extChartAt_source I]

/--
theorem `map_extChartAt_symm_nhdsWithin_range'` / 定理 `map_extChartAt_symm_nhdsWithin_range'`

English:
theorem map_extChartAt_symm_nhdsWithin_range'
  given: {x y : M} (hy : y in (extChartAt I x).source)
  proof: map_extend_symm_nhdsWithin_range _ by rwa [← extChartAt_source I]

中文:
定理 map_extChartAt_symm_nhdsWithin_range'
  条件: {x y : M} (hy : y in (extChartAt I x).source)
  证明: map_extend_symm_nhdsWithin_range _ by rwa [← extChartAt_source I]

Depends on / 依赖: extChartAt_source, map_extend_symm_nhdsWithin_range
-/
theorem map_extChartAt_symm_nhdsWithin_range' {x y : M} (hy : y in (extChartAt I x).source) :
    map (extChartAt I x).symm (𝓝[range I] extChartAt I x y) = 𝓝 y :=
map_extend_symm_nhdsWithin_range _ by rwa [← extChartAt_source I]

/--
theorem `map_extChartAt_symm_nhdsWithin` / 定理 `map_extChartAt_symm_nhdsWithin`

English:
theorem map_extChartAt_symm_nhdsWithin
  given: (x : M)
  proof: map_extChartAt_symm_nhdsWithin' (mem_extChartAt_source x)

中文:
定理 map_extChartAt_symm_nhdsWithin
  条件: (x : M)
  证明: map_extChartAt_symm_nhdsWithin' (mem_extChartAt_source x)

Depends on / 依赖: map_extChartAt_symm_nhdsWithin, mem_extChartAt_source
-/
theorem map_extChartAt_symm_nhdsWithin (x : M) :
    map (extChartAt I x).symm (𝓝[(extChartAt I x).symm ⁻¹' s inter range I] extChartAt I x x) =
      𝓝[s] x :=
  map_extChartAt_symm_nhdsWithin' (mem_extChartAt_source x)

/--
theorem `map_extChartAt_symm_nhdsWithin_range` / 定理 `map_extChartAt_symm_nhdsWithin_range`

English:
theorem map_extChartAt_symm_nhdsWithin_range
  given: (x : M)
  proof: map_extChartAt_symm_nhdsWithin_range' (mem_extChartAt_source x)

中文:
定理 map_extChartAt_symm_nhdsWithin_range
  条件: (x : M)
  证明: map_extChartAt_symm_nhdsWithin_range' (mem_extChartAt_source x)

Depends on / 依赖: map_extChartAt_symm_nhdsWithin_range, mem_extChartAt_source
-/
theorem map_extChartAt_symm_nhdsWithin_range (x : M) :
    map (extChartAt I x).symm (𝓝[range I] extChartAt I x x) = 𝓝 x :=
  map_extChartAt_symm_nhdsWithin_range' (mem_extChartAt_source x)

/--
theorem `extChartAt_preimage_mem_nhds_of_mem_nhdsWithin` / 定理 `extChartAt_preimage_mem_nhds_of_mem_nhdsWithin`

English:
theorem extChartAt_preimage_mem_nhds_of_mem_nhdsWithin
  statement: {s : Set E} {x x' : M}
  proof: extend_preimage_mem_nhds_of_mem_nhdsWithin _ (by simpa using hx) hs

中文:
定理 extChartAt_preimage_mem_nhds_of_mem_nhdsWithin
  结论: {s : 集合 E} {x x' : M}
  证明: extend_preimage_mem_nhds_of_mem_nhdsWithin _ (by simpa using hx) hs

Depends on / 依赖: extend_preimage_mem_nhds_of_mem_nhdsWithin
-/
theorem extChartAt_preimage_mem_nhds_of_mem_nhdsWithin {s : Set E} {x x' : M}
    (hx : x' in (extChartAt I x).source)
    (hs : s in 𝓝[range I] (extChartAt I x x')) :
    (extChartAt I x) ⁻¹' s in 𝓝 x' :=
  extend_preimage_mem_nhds_of_mem_nhdsWithin _ (by simpa using hx) hs

/--
theorem `extChartAt_preimage_mem_nhdsWithin'` / 定理 `extChartAt_preimage_mem_nhdsWithin'`

English:
theorem extChartAt_preimage_mem_nhdsWithin'
  statement: {x x' : M} (h : x' in (extChartAt I x).source)
  proof: by
  rwa [← map_extChartAt_symm_nhdsWithin' h, mem_map] at ht

中文:
定理 extChartAt_preimage_mem_nhdsWithin'
  结论: {x x' : M} (h : x' in (extChartAt I x).source)
  证明: by
  rwa [← map_extChartAt_symm_nhdsWithin' h, mem_map] at ht

Depends on / 依赖: map_extChartAt_symm_nhdsWithin, mem_map
-/
theorem extChartAt_preimage_mem_nhdsWithin' {x x' : M} (h : x' in (extChartAt I x).source)
    (ht : t in 𝓝[s] x') :
    (extChartAt I x).symm ⁻¹' t in 𝓝[(extChartAt I x).symm ⁻¹' s inter range I] (extChartAt I x) x' := by
  rwa [← map_extChartAt_symm_nhdsWithin' h, mem_map] at ht

/--
theorem `extChartAt_preimage_mem_nhdsWithin` / 定理 `extChartAt_preimage_mem_nhdsWithin`

English:
theorem extChartAt_preimage_mem_nhdsWithin
  given: {x : M} (ht : t in 𝓝[s] x)
  proof: extChartAt_preimage_mem_nhdsWithin' (mem_extChartAt_source x) ht

中文:
定理 extChartAt_preimage_mem_nhdsWithin
  条件: {x : M} (ht : t in 𝓝[s] x)
  证明: extChartAt_preimage_mem_nhdsWithin' (mem_extChartAt_source x) ht

Depends on / 依赖: extChartAt_preimage_mem_nhdsWithin, mem_extChartAt_source
-/
theorem extChartAt_preimage_mem_nhdsWithin {x : M} (ht : t in 𝓝[s] x) :
    (extChartAt I x).symm ⁻¹' t in 𝓝[(extChartAt I x).symm ⁻¹' s inter range I] (extChartAt I x) x :=
  extChartAt_preimage_mem_nhdsWithin' (mem_extChartAt_source x) ht

/--
theorem `extChartAt_preimage_mem_nhds'` / 定理 `extChartAt_preimage_mem_nhds'`

English:
theorem extChartAt_preimage_mem_nhds'
  statement: {x x' : M} (h : x' in (extChartAt I x).source)
  proof: extend_preimage_mem_nhds _ (by rwa [← extChartAt_source I]) ht

中文:
定理 extChartAt_preimage_mem_nhds'
  结论: {x x' : M} (h : x' in (extChartAt I x).source)
  证明: extend_preimage_mem_nhds _ (by rwa [← extChartAt_source I]) ht

Depends on / 依赖: extChartAt_source, extend_preimage_mem_nhds
-/
theorem extChartAt_preimage_mem_nhds' {x x' : M} (h : x' in (extChartAt I x).source)
    (ht : t in 𝓝 x') : (extChartAt I x).symm ⁻¹' t in 𝓝 (extChartAt I x x') :=
  extend_preimage_mem_nhds _ (by rwa [← extChartAt_source I]) ht

/--
theorem `extChartAt_preimage_mem_nhds` / 定理 `extChartAt_preimage_mem_nhds`

English:
theorem extChartAt_preimage_mem_nhds
  given: {x : M} (ht : t in 𝓝 x)
  proof: by
  apply (continuousAt_extChartAt_symm x).preimage_mem_nhds
  rwa [(extChartAt I x).left_inv (mem_extChartAt_source _)]

中文:
定理 extChartAt_preimage_mem_nhds
  条件: {x : M} (ht : t in 𝓝 x)
  证明: by
  apply (continuousAt_extChartAt_symm x).preimage_mem_nhds
  rwa [(extChartAt I x).left_inv (mem_extChartAt_source _)]

Depends on / 依赖: continuousAt_extChartAt_symm, extChartAt, left_inv, mem_extChartAt_source, preimage_mem_nhds
-/
theorem extChartAt_preimage_mem_nhds {x : M} (ht : t in 𝓝 x) :
    (extChartAt I x).symm ⁻¹' t in 𝓝 ((extChartAt I x) x) := by
  apply (continuousAt_extChartAt_symm x).preimage_mem_nhds
  rwa [(extChartAt I x).left_inv (mem_extChartAt_source _)]

/--
theorem `extChartAt_preimage_inter_eq` / 定理 `extChartAt_preimage_inter_eq`

English:
theorem extChartAt_preimage_inter_eq
  given: (x : M)
  proof: by
  mfld_set_tac

中文:
定理 extChartAt_preimage_inter_eq
  条件: (x : M)
  证明: by
  mfld_set_tac

Depends on / 依赖: mfld_set_tac
-/
theorem extChartAt_preimage_inter_eq (x : M) :
    (extChartAt I x).symm ⁻¹' (s inter t) inter range I =
      (extChartAt I x).symm ⁻¹' s inter range I inter (extChartAt I x).symm ⁻¹' t := by
  mfld_set_tac

/--
theorem `ContinuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range` / 定理 `ContinuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range`

English:
theorem ContinuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range
  proof: by
  rw [← (extChartAt I x).image_source_inter_eq']; rw [← map_extChartAt_nhdsWithin_eq_image]; rw [← map_extChartAt_nhdsWithin]; rw [nhdsWithin_inter_of_mem']
  exact hc (extChartAt_source_mem_nhds _)

中文:
定理 ContinuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range
  证明: by
  rw [← (extChartAt I x).image_source_inter_eq']; rw [← map_extChartAt_nhdsWithin_eq_image]; rw [← map_extChartAt_nhdsWithin]; rw [nhdsWithin_inter_of_mem']
  exact hc (extChartAt_source_mem_nhds _)

Depends on / 依赖: extChartAt, extChartAt_source_mem_nhds, image_source_inter_eq, map_extChartAt_nhdsWithin, map_extChartAt_nhdsWithin_eq_image, nhdsWithin_inter_of_mem
-/
theorem ContinuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range
    {f : M -> M'} {x : M} (hc : ContinuousWithinAt f s x) :
    𝓝[(extChartAt I x).symm ⁻¹' s inter range I] (extChartAt I x x) =
      𝓝[(extChartAt I x).target inter
        (extChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' (f x)).source)] (extChartAt I x x) := by
  rw [← (extChartAt I x).image_source_inter_eq']; rw [← map_extChartAt_nhdsWithin_eq_image]; rw [← map_extChartAt_nhdsWithin]; rw [nhdsWithin_inter_of_mem']
  exact hc (extChartAt_source_mem_nhds _)

/--
theorem `ContinuousWithinAt.extChartAt_symm_preimage_inter_range_eventuallyEq` / 定理 `ContinuousWithinAt.extChartAt_symm_preimage_inter_range_eventuallyEq`

English:
theorem ContinuousWithinAt.extChartAt_symm_preimage_inter_range_eventuallyEq
  proof: by
  rw [← nhdsWithin_eq_iff_eventuallyEq]
  exact hc.nhdsWithin_extChartAt_symm_preimage_inter_range

中文:
定理 ContinuousWithinAt.extChartAt_symm_preimage_inter_range_eventuallyEq
  证明: by
  rw [← nhdsWithin_eq_iff_eventuallyEq]
  exact hc.nhdsWithin_extChartAt_symm_preimage_inter_range

Depends on / 依赖: hc.nhdsWithin_extChartAt_symm_preimage_inter_range, nhdsWithin_eq_iff_eventuallyEq, nhdsWithin_extChartAt_symm_preimage_inter_range
-/
theorem ContinuousWithinAt.extChartAt_symm_preimage_inter_range_eventuallyEq
    {f : M -> M'} {x : M} (hc : ContinuousWithinAt f s x) :
    ((extChartAt I x).symm ⁻¹' s inter range I : Set E) =ᶠ[𝓝 (extChartAt I x x)]
      ((extChartAt I x).target inter
        (extChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' (f x)).source) : Set E) := by
  rw [← nhdsWithin_eq_iff_eventuallyEq]
  exact hc.nhdsWithin_extChartAt_symm_preimage_inter_range


/--
theorem `ext_coord_change_source` / 定理 `ext_coord_change_source`

English:
theorem ext_coord_change_source
  given: (x x' : M)
  proof: I.extendCoordChange_source

中文:
定理 ext_coord_change_source
  条件: (x x' : M)
  证明: I.extendCoordChange_source

Depends on / 依赖: I.extendCoordChange_source, extendCoordChange_source
-/
theorem ext_coord_change_source (x x' : M) :
    ((extChartAt I x').symm ≫ extChartAt I x).source =
      I '' ((chartAt H x').symm ≫ₕ chartAt H x).source :=
  I.extendCoordChange_source

open IsManifold

/--
theorem `contDiffOn_ext_coord_change` / 定理 `contDiffOn_ext_coord_change`

English:
theorem contDiffOn_ext_coord_change
  given: [IsManifold I n M] (x x' : M)
  proof: I.contDiffOn_extendCoordChange (chart_mem_maximalAtlas x') (chart_mem_maximalAtlas x)

中文:
定理 contDiffOn_ext_coord_change
  条件: [是流形 I n M] (x x' : M)
  证明: I.contDiffOn_extendCoordChange (chart_mem_maximalAtlas x') (chart_mem_maximalAtlas x)

Depends on / 依赖: I.contDiffOn_extendCoordChange, chart_mem_maximalAtlas, contDiffOn_extendCoordChange
-/
theorem contDiffOn_ext_coord_change [IsManifold I n M] (x x' : M) :
    ContDiffOn 𝕜 n (extChartAt I x ∘ (extChartAt I x').symm)
      ((extChartAt I x').symm ≫ extChartAt I x).source :=
  I.contDiffOn_extendCoordChange (chart_mem_maximalAtlas x') (chart_mem_maximalAtlas x)

/--
theorem `contDiffWithinAt_ext_coord_change` / 定理 `contDiffWithinAt_ext_coord_change`

English:
theorem contDiffWithinAt_ext_coord_change
  statement: [IsManifold I n M] (x x' : M) {y : E}
  proof: I.contDiffWithinAt_extendCoordChange (chart_mem_maximalAtlas x') (chart_mem_maximalAtlas x) hy

中文:
定理 contDiffWithinAt_ext_coord_change
  结论: [是流形 I n M] (x x' : M) {y : E}
  证明: I.contDiffWithinAt_extendCoordChange (chart_mem_maximalAtlas x') (chart_mem_maximalAtlas x) hy

Depends on / 依赖: I.contDiffWithinAt_extendCoordChange, chart_mem_maximalAtlas, contDiffWithinAt_extendCoordChange
-/
theorem contDiffWithinAt_ext_coord_change [IsManifold I n M] (x x' : M) {y : E}
    (hy : y in ((extChartAt I x').symm ≫ extChartAt I x).source) :
    ContDiffWithinAt 𝕜 n (extChartAt I x ∘ (extChartAt I x').symm) (range I) y :=
  I.contDiffWithinAt_extendCoordChange (chart_mem_maximalAtlas x') (chart_mem_maximalAtlas x) hy

variable (I I') in
/-- Conjugating a function to write it in the preferred charts around `x`.
The manifold derivative of `f` will just be the derivative of this conjugated function. -/
@[simp, mfld_simps]
/--
Definition of `writtenInExtChartAt` / `writtenInExtChartAt` 的定义

English:
definition writtenInExtChartAt
  signature: (x : M) (f : M -> M')
  body: extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm

中文:
定义 writtenInExtChartAt
  签名: (x : M) (f : M -> M')
  定义体: extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm

Depends on / 依赖: extChartAt
-/
def writtenInExtChartAt (x : M) (f : M -> M') : E -> E' :=
  extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `writtenInExtChartAt_chartAt` / 定理 `writtenInExtChartAt_chartAt`

English:
theorem writtenInExtChartAt_chartAt
  given: {x : M} {y : E} (h : y in (extChartAt I x).target)
  proof: by simp_all only [mfld_simps]

中文:
定理 writtenInExtChartAt_chartAt
  条件: {x : M} {y : E} (h : y in (extChartAt I x).target)
  证明: by simp_all only [mfld_simps]

Depends on / 依赖: mfld_simps
-/
theorem writtenInExtChartAt_chartAt {x : M} {y : E} (h : y in (extChartAt I x).target) :
    writtenInExtChartAt I I x (chartAt H x) y = y := by simp_all only [mfld_simps]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `writtenInExtChartAt_chartAt_symm` / 定理 `writtenInExtChartAt_chartAt_symm`

English:
theorem writtenInExtChartAt_chartAt_symm
  given: {x : M} {y : E} (h : y in (extChartAt I x).target)
  proof: by
  simp_all only [mfld_simps]

中文:
定理 writtenInExtChartAt_chartAt_symm
  条件: {x : M} {y : E} (h : y in (extChartAt I x).target)
  证明: by
  simp_all only [mfld_simps]

Depends on / 依赖: mfld_simps
-/
theorem writtenInExtChartAt_chartAt_symm {x : M} {y : E} (h : y in (extChartAt I x).target) :
    writtenInExtChartAt I I (chartAt H x x) (chartAt H x).symm y = y := by
  simp_all only [mfld_simps]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `writtenInExtChartAt_extChartAt` / 定理 `writtenInExtChartAt_extChartAt`

English:
theorem writtenInExtChartAt_extChartAt
  given: {x : M} {y : E} (h : y in (extChartAt I x).target)
  proof: by
  simp_all only [mfld_simps]

中文:
定理 writtenInExtChartAt_extChartAt
  条件: {x : M} {y : E} (h : y in (extChartAt I x).target)
  证明: by
  simp_all only [mfld_simps]

Depends on / 依赖: mfld_simps
-/
theorem writtenInExtChartAt_extChartAt {x : M} {y : E} (h : y in (extChartAt I x).target) :
    writtenInExtChartAt I 𝓘(𝕜, E) x (extChartAt I x) y = y := by
  simp_all only [mfld_simps]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `writtenInExtChartAt_extChartAt_symm` / 定理 `writtenInExtChartAt_extChartAt_symm`

English:
theorem writtenInExtChartAt_extChartAt_symm
  given: {x : M} {y : E} (h : y in (extChartAt I x).target)
  proof: by
  simp_all only [mfld_simps]

中文:
定理 writtenInExtChartAt_extChartAt_symm
  条件: {x : M} {y : E} (h : y in (extChartAt I x).target)
  证明: by
  simp_all only [mfld_simps]

Depends on / 依赖: mfld_simps
-/
theorem writtenInExtChartAt_extChartAt_symm {x : M} {y : E} (h : y in (extChartAt I x).target) :
    writtenInExtChartAt 𝓘(𝕜, E) I (extChartAt I x x) (extChartAt I x).symm y = y := by
  simp_all only [mfld_simps]

/--
theorem `writtenInExtChartAt_mapsTo` / 定理 `writtenInExtChartAt_mapsTo`

English:
theorem writtenInExtChartAt_mapsTo
  given: {x : M} {f : M -> M'}
  proof: by
  intro x' hx'
  simpa using (chartAt H' (f x)).mapsTo (by simpa using hx'.2)

中文:
定理 writtenInExtChartAt_mapsTo
  条件: {x : M} {f : M -> M'}
  证明: by
  intro x' hx'
  simpa using (chartAt H' (f x)).mapsTo (by simpa using hx'.2)

Depends on / 依赖: chartAt, mapsTo
-/
theorem writtenInExtChartAt_mapsTo {x : M} {f : M -> M'} :
    MapsTo (writtenInExtChartAt I I' x f)
      ((extChartAt I x).target inter f ∘ (extChartAt I x).symm ⁻¹' (extChartAt I' (f x)).source)
      (extChartAt I' (f x)).target := by
  intro x' hx'
  simpa using (chartAt H' (f x)).mapsTo (by simpa using hx'.2)

section

variable {G G' F F' N N' : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace G] [TopologicalSpace N] [TopologicalSpace G'] [TopologicalSpace N']
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F' G'}
  [ChartedSpace G N] [ChartedSpace G' N']

/--
lemma `writtenInExtChartAt_prod` / 引理 `writtenInExtChartAt_prod`

English:
lemma writtenInExtChartAt_prod
  given: {f : M -> N} {g : M' -> N'} {x : M} {x' : M'}
  proof: by
  ext p <;>
  simp [writtenInExtChartAt, I.toPartialEquiv.prod_symm, (chartAt H x).toPartialEquiv.prod_symm]

@[deprecated (since := "2026-02-18")] alias writtenInExtChart_prod := writtenInExtChartAt_prod

中文:
引理 writtenInExtChartAt_prod
  条件: {f : M -> N} {g : M' -> N'} {x : M} {x' : M'}
  证明: by
  ext p <;>
  simp [writtenInExtChartAt, I.toPartialEquiv.prod_symm, (chartAt H x).toPartialEquiv.prod_symm]

@[deprecated (since := "2026-02-18")] alias writtenInExtChart_prod := writtenInExtChartAt_prod

Depends on / 依赖: I.toPartialEquiv.prod_symm, chartAt, prod_symm, toPartialEquiv, toPartialEquiv.prod_symm, writtenInExtChartAt
-/
lemma writtenInExtChartAt_prod {f : M -> N} {g : M' -> N'} {x : M} {x' : M'} :
    (writtenInExtChartAt (I.prod I') (J.prod J') (x, x') (Prod.map f g)) =
      Prod.map (writtenInExtChartAt I J x f) (writtenInExtChartAt I' J' x' g) := by
  ext p <;>
  simp [writtenInExtChartAt, I.toPartialEquiv.prod_symm, (chartAt H x).toPartialEquiv.prod_symm]

@[deprecated (since := "2026-02-18")] alias writtenInExtChart_prod := writtenInExtChartAt_prod

end

variable (𝕜)

/--
theorem `extChartAt_self_eq` / 定理 `extChartAt_self_eq`

English:
theorem extChartAt_self_eq
  given: {x : H}
  statement: ⇑(extChartAt I x) = I
  proof: rfl

中文:
定理 extChartAt_self_eq
  条件: {x : H}
  结论: ⇑(extChartAt I x) = I
  证明: rfl
-/
theorem extChartAt_self_eq {x : H} : ⇑(extChartAt I x) = I :=
  rfl

/--
theorem `extChartAt_self_apply` / 定理 `extChartAt_self_apply`

English:
theorem extChartAt_self_apply
  given: {x y : H}
  statement: extChartAt I x y = I y
  proof: rfl

中文:
定理 extChartAt_self_apply
  条件: {x y : H}
  结论: extChartAt I x y = I y
  证明: rfl
-/
theorem extChartAt_self_apply {x y : H} : extChartAt I x y = I y :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `extChartAt_model_space_eq_id` / 定理 `extChartAt_model_space_eq_id`

English:
theorem extChartAt_model_space_eq_id
  given: (x : E)
  statement: extChartAt 𝓘(𝕜, E) x = PartialEquiv.refl E
  proof: by
  simp only [mfld_simps]

中文:
定理 extChartAt_model_space_eq_id
  条件: (x : E)
  结论: extChartAt 𝓘(𝕜, E) x = 部分等价.refl E
  证明: by
  simp only [mfld_simps]

Depends on / 依赖: mfld_simps
-/
theorem extChartAt_model_space_eq_id (x : E) : extChartAt 𝓘(𝕜, E) x = PartialEquiv.refl E := by
  simp only [mfld_simps]

/--
theorem `ext_chart_model_space_apply` / 定理 `ext_chart_model_space_apply`

English:
theorem ext_chart_model_space_apply
  given: {x y : E}
  statement: extChartAt 𝓘(𝕜, E) x y = y
  proof: rfl

中文:
定理 ext_chart_model_space_apply
  条件: {x y : E}
  结论: extChartAt 𝓘(𝕜, E) x y = y
  证明: rfl
-/
theorem ext_chart_model_space_apply {x y : E} : extChartAt 𝓘(𝕜, E) x y = y :=
  rfl

variable {𝕜}

/--
theorem `extChartAt_prod` / 定理 `extChartAt_prod`

English:
theorem extChartAt_prod
  given: (x : M × M')
  proof: by
  simp only [mfld_simps]
  rw [PartialEquiv.prod_trans]

中文:
定理 extChartAt_prod
  条件: (x : M × M')
  证明: by
  simp only [mfld_simps]
  rw [PartialEquiv.prod_trans]

Depends on / 依赖: PartialEquiv, PartialEquiv.prod_trans, mfld_simps, prod_trans
-/
theorem extChartAt_prod (x : M × M') :
    extChartAt (I.prod I') x = (extChartAt I x.1).prod (extChartAt I' x.2) := by
  simp only [mfld_simps]
  rw [PartialEquiv.prod_trans]

/--
theorem `extChartAt_comp` / 定理 `extChartAt_comp`

English:
theorem extChartAt_comp
  given: [ChartedSpace H H'] (x : M')
  proof: PartialEquiv.trans_assoc ..

中文:
定理 extChartAt_comp
  条件: [Charted空间 H H'] (x : M')
  证明: PartialEquiv.trans_assoc ..

Depends on / 依赖: ChartedSpace, ChartedSpace.comp, extChartAt
-/
theorem extChartAt_comp [ChartedSpace H H'] (x : M') :
    (letI := ChartedSpace.comp H H' M'; extChartAt I x) =
      (chartAt H' x).toPartialEquiv ≫ extChartAt I (chartAt H' x x) :=
  PartialEquiv.trans_assoc ..

/--
theorem `writtenInExtChartAt_chartAt_comp` / 定理 `writtenInExtChartAt_chartAt_comp`

English:
theorem writtenInExtChartAt_chartAt_comp
  statement: [ChartedSpace H H'] (x : M') {y}
  proof: by
  let := ChartedSpace.comp H H' M'
  simp_all only [mfld_simps, chartAt_comp]

中文:
定理 writtenInExtChartAt_chartAt_comp
  结论: [Charted空间 H H'] (x : M') {y}
  证明: by
  let := ChartedSpace.comp H H' M'
  simp_all only [mfld_simps, chartAt_comp]

Depends on / 依赖: ChartedSpace, ChartedSpace.comp, extChartAt, target
-/
theorem writtenInExtChartAt_chartAt_comp [ChartedSpace H H'] (x : M') {y}
    (hy : y in letI := ChartedSpace.comp H H' M'; (extChartAt I x).target) :
    (letI := ChartedSpace.comp H H' M'; writtenInExtChartAt I I x (chartAt H' x) y) = y := by
  let := ChartedSpace.comp H H' M'
  simp_all only [mfld_simps, chartAt_comp]

/--
theorem `writtenInExtChartAt_chartAt_symm_comp` / 定理 `writtenInExtChartAt_chartAt_symm_comp`

English:
theorem writtenInExtChartAt_chartAt_symm_comp
  statement: [ChartedSpace H H'] (x : M') {y}
  proof: by
  let := ChartedSpace.comp H H' M'
  simp_all only [mfld_simps, chartAt_comp]

中文:
定理 writtenInExtChartAt_chartAt_symm_comp
  结论: [Charted空间 H H'] (x : M') {y}
  证明: by
  let := ChartedSpace.comp H H' M'
  simp_all only [mfld_simps, chartAt_comp]

Depends on / 依赖: ChartedSpace, ChartedSpace.comp, extChartAt, target
-/
theorem writtenInExtChartAt_chartAt_symm_comp [ChartedSpace H H'] (x : M') {y}
    (hy : y in letI := ChartedSpace.comp H H' M'; (extChartAt I x).target) :
    (letI := ChartedSpace.comp H H' M'
     writtenInExtChartAt I I (chartAt H' x x) (chartAt H' x).symm y) = y := by
  let := ChartedSpace.comp H H' M'
  simp_all only [mfld_simps, chartAt_comp]

end ExtendedCharts

section Topology

-- Let `M` be a topological manifold over the field 𝕜.
variable
  {E : Type*} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/--
lemma `Manifold.locallyCompact_of_finiteDimensional` / 引理 `Manifold.locallyCompact_of_finiteDimensional`

English:
lemma Manifold.locallyCompact_of_finiteDimensional
  proof: by
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  have : LocallyCompactSpace H := I.locallyCompactSpace
  exact ChartedSpace.locallyCompactSpace H M

中文:
引理 流形.locallyCompact_of_finiteDimensional
  证明: by
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  have : LocallyCompactSpace H := I.locallyCompactSpace
  exact ChartedSpace.locallyCompactSpace H M

Depends on / 依赖: ChartedSpace, ChartedSpace.locallyCompactSpace, FiniteDimensional, FiniteDimensional.proper, I.locallyCompactSpace, LocallyCompactSpace, ProperSpace, locallyCompactSpace, proper
-/
lemma Manifold.locallyCompact_of_finiteDimensional
    (I : ModelWithCorners 𝕜 E H) [LocallyCompactSpace 𝕜] [FiniteDimensional 𝕜 E] :
    LocallyCompactSpace M := by
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  have : LocallyCompactSpace H := I.locallyCompactSpace
  exact ChartedSpace.locallyCompactSpace H M

variable (M)

/--
lemma `LocallyCompactSpace.of_locallyCompact_manifold` / 引理 `LocallyCompactSpace.of_locallyCompact_manifold`

English:
lemma LocallyCompactSpace.of_locallyCompact_manifold
  statement: (I : ModelWithCorners 𝕜 E H)
  proof: by
  rcases h with ⟨x⟩
  obtain ⟨y, hy⟩ := interior_extChartAt_target_nonempty I x
  have h'y : y in (extChartAt I x).target := interior_subset hy
  obtain ⟨s, hmem, hss, hcom⟩ :=
    LocallyCompactSpace.local_compact_nhds ((extChartAt I x).symm y) (extChartAt I x).source
      ((isOpen_extChartAt_s

中文:
引理 局部紧空间.of_locallyCompact_manifold
  结论: (I : 带角模型 𝕜 E H)
  证明: by
  rcases h with ⟨x⟩
  obtain ⟨y, hy⟩ := interior_extChartAt_target_nonempty I x
  have h'y : y in (extChartAt I x).target := interior_subset hy
  obtain ⟨s, hmem, hss, hcom⟩ :=
    LocallyCompactSpace.local_compact_nhds ((extChartAt I x).symm y) (extChartAt I x).source
      ((isOpen_extChartAt_s

Depends on / 依赖: IsCompact, LocallyCompactSpace, LocallyCompactSpace.local_compact_nhds, continuousOn_extChartAt, extChartAt, hcom.image_of_continuousOn, image_of_continuousOn, interior_extChartAt_target_nonempty, interior_subset, isOpen_extChartAt_source, local_compact_nhds, locallyCompactSpace_of_mem_nhds_of_addGroup, map_target, mem_nhds, source, target, this.locallyCompactSpace_of_mem_nhds_of_addGroup
-/
lemma LocallyCompactSpace.of_locallyCompact_manifold (I : ModelWithCorners 𝕜 E H)
    [h : Nonempty M] [LocallyCompactSpace M] :
    LocallyCompactSpace E := by
  rcases h with ⟨x⟩
  obtain ⟨y, hy⟩ := interior_extChartAt_target_nonempty I x
  have h'y : y in (extChartAt I x).target := interior_subset hy
  obtain ⟨s, hmem, hss, hcom⟩ :=
    LocallyCompactSpace.local_compact_nhds ((extChartAt I x).symm y) (extChartAt I x).source
      ((isOpen_extChartAt_source x).mem_nhds ((extChartAt I x).map_target h'y))
have : IsCompact (extChartAt I x) '' s :=
hcom.image_of_continuousOn (continuousOn_extChartAt x).mono hss
  apply this.locallyCompactSpace_of_mem_nhds_of_addGroup (x := y)
  rw [← (extChartAt I x).right_inv h'y]
  apply extChartAt_image_nhds_mem_nhds_of_mem_interior_range
    (PartialEquiv.map_target (extChartAt I x) h'y) _ hmem
  simp only [(extChartAt I x).right_inv h'y]
  exact interior_mono (extChartAt_target_subset_range x) hy

/--
theorem `FiniteDimensional.of_locallyCompact_manifold` / 定理 `FiniteDimensional.of_locallyCompact_manifold`

English:
theorem FiniteDimensional.of_locallyCompact_manifold
  proof: by
  have := LocallyCompactSpace.of_locallyCompact_manifold M I
  exact FiniteDimensional.of_locallyCompactSpace 𝕜

中文:
定理 有限维.of_locallyCompact_manifold
  证明: by
  have := LocallyCompactSpace.of_locallyCompact_manifold M I
  exact FiniteDimensional.of_locallyCompactSpace 𝕜

Depends on / 依赖: FiniteDimensional, FiniteDimensional.of_locallyCompactSpace, LocallyCompactSpace, LocallyCompactSpace.of_locallyCompact_manifold, of_locallyCompactSpace, of_locallyCompact_manifold
-/
theorem FiniteDimensional.of_locallyCompact_manifold
    [CompleteSpace 𝕜] (I : ModelWithCorners 𝕜 E H) [Nonempty M] [LocallyCompactSpace M] :
    FiniteDimensional 𝕜 E := by
  have := LocallyCompactSpace.of_locallyCompact_manifold M I
  exact FiniteDimensional.of_locallyCompactSpace 𝕜

end Topology
