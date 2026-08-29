/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Notation

/-! # Tangent bundles

This file defines the tangent bundle as a `C^n` vector bundle.

Let `M` be a manifold with model `I` on `(E, H)`. The tangent space `TangentSpace I (x : M)` has
already been defined as a type synonym for `E`, and the tangent bundle `TangentBundle I M` as an
abbrev of `Bundle.TotalSpace E (TangentSpace I : M → Type _)`.

In this file, when `M` is `C^1`, we construct a vector bundle structure
on `TangentBundle I M` using the `VectorBundleCore` construction indexed by the charts of `M`
with fibers `E`. Given two charts `i, j : OpenPartialHomeomorph M H`, the coordinate change
between `i` and `j` at a point `x : M` is the derivative of the composite
```
  I.symm i.symm j I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`.
This defines a vector bundle `TangentBundle` with fibers `TangentSpace`.

## Main definitions and results

* `tangentBundleCore I M` is the vector bundle core for the tangent bundle over `M`.

* When `M` is a `C^{n+1}` manifold, `TangentBundle I M` has a `C^n` vector bundle
  structure over `M`. In particular, it is a topological space, a vector bundle, a fiber bundle,
  and a `C^n` manifold.
-/

@[expose] public section


open Bundle Set IsManifold OpenPartialHomeomorph ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff

noncomputable section

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Nat∞ω} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/--
theorem `contDiffOn_fderiv_coord_change` / 定理 `contDiffOn_fderiv_coord_change`

English:
theorem contDiffOn_fderiv_coord_change
  statement: [IsManifold I (n + 1) M]
  proof: by
  have h : ((i.1.extend I).symm ≫ j.1.extend I).source subseteq range I := by
    refine I.extendCoordChange_source.trans_subset ?_; apply image_subset_range
  intro x hx
  refine (ContDiffWithinAt.fderivWithin_right ?_ I.uniqueDiffOn le_rfl
 h hx).mono h
  refine (I.contDiffOn_extendCoordChange 

中文:
定理 contDiffOn_fderiv_coord_change
  结论: [IsManifold I (n + 1) M]
  证明: by
  have h : ((i.1.extend I).symm ≫ j.1.extend I).source subseteq range I := by
    refine I.extendCoordChange_source.trans_subset ?_; apply image_subset_range
  intro x hx
  refine (ContDiffWithinAt.fderivWithin_right ?_ I.uniqueDiffOn le_rfl
 h hx).mono h
  refine (I.contDiffOn_extendCoordChange 

Depends on / 依赖: ContDiffWithinAt, ContDiffWithinAt.fderivWithin_right, I.contDiffOn_extendCoordChange, I.extendCoordChange_source.trans_subset, I.extendCoordChange_source_mem_nhdsWithin, I.uniqueDiffOn, contDiffOn_extendCoordChange, extend, extendCoordChange_source, extendCoordChange_source_mem_nhdsWithin, fderivWithin_right, image_subset_range, le_rfl, mono_of_mem_nhdsWithin, source, subset_maximalAtlas, subseteq, trans_subset, uniqueDiffOn
-/
theorem contDiffOn_fderiv_coord_change [IsManifold I (n + 1) M]
    (i j : atlas H M) :
    ContDiffOn 𝕜 n (fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I))
      ((i.1.extend I).symm ≫ j.1.extend I).source := by
  have h : ((i.1.extend I).symm ≫ j.1.extend I).source subseteq range I := by
    refine I.extendCoordChange_source.trans_subset ?_; apply image_subset_range
  intro x hx
  refine (ContDiffWithinAt.fderivWithin_right ?_ I.uniqueDiffOn le_rfl
 h hx).mono h
  refine (I.contDiffOn_extendCoordChange (subset_maximalAtlas i.2)
    (subset_maximalAtlas j.2) x hx).mono_of_mem_nhdsWithin ?_
  exact I.extendCoordChange_source_mem_nhdsWithin hx

open IsManifold

variable [IsManifold I 1 M] [IsManifold I' 1 M']

variable (I M) in
/-- Let `M` be a `C^1` manifold with model `I` on `(E, H)`.
Then `tangentBundleCore I M` is the vector bundle core for the tangent bundle over `M`.
It is indexed by the atlas of `M`, with fiber `E` and its change of coordinates from the chart `i`
to the chart `j` at point `x : M` is the derivative of the composite
```
  I.symm i.symm j I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`. -/
@[simps indexAt coordChange]
/--
Definition of `tangentBundleCore` / `tangentBundleCore` 的定义

English:
definition tangentBundleCore
  signature: : VectorBundleCore 𝕜 M E (atlas H M) where
  body: i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart H
  mem_baseSet_at := mem_chart_source H
  coordChange i j x :=
    fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I) (i.1.extend I x)
  coordChange_self i x hx v := by
    rw [Filter.EventuallyEq.fderivWithin_eq]; rw [

中文:
定义 tangentBundleCore
  签名: : VectorBundleCore 𝕜 M E (atlas H M) where
  定义体: i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart H
  mem_baseSet_at := mem_chart_source H
  coordChange i j x :=
    fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I) (i.1.extend I x)
  coordChange_self i x hx v := by
    rw [Filter.EventuallyEq.fderivWithin_eq]; rw [

Depends on / 依赖: source
-/
def tangentBundleCore : VectorBundleCore 𝕜 M E (atlas H M) where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart H
  mem_baseSet_at := mem_chart_source H
  coordChange i j x :=
    fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I) (i.1.extend I x)
  coordChange_self i x hx v := by
    rw [Filter.EventuallyEq.fderivWithin_eq]; rw [fderivWithin_fun_id]; rw [ContinuousLinearMap.id_apply]
    · exact I.uniqueDiffWithinAt_image
    · filter_upwards [i.1.extend_target_mem_nhdsWithin hx] with y hy
      exact (i.1.extend I).right_inv hy
    · simp_rw [Function.comp_apply, i.1.extend_left_inv hx]
  continuousOn_coordChange i j := by
    have : IsManifold I (0 + 1) M := by simpa
    refine (contDiffOn_fderiv_coord_change (n := 0) i j).continuousOn.comp
      (i.1.continuousOn_extend.mono ?_) ?_
    · rw [i.1.extend_source]; exact inter_subset_left
    exact mapsTo_iff_image_subset.2 (i.1.extend_image_source_inter j.1).subset
  coordChange_comp := by
    have : IsManifold I (0 + 1) M := by simpa
    rintro i j k x ⟨⟨hxi, hxj⟩, hxk⟩ v
    rw [fderivWithin_fderivWithin]; rw [Filter.EventuallyEq.fderivWithin_eq]
    · have := i.1.extend_preimage_mem_nhds (I := I) hxi (j.1.extend_source_mem_nhds (I := I) hxj)
      filter_upwards [nhdsWithin_le_nhds this] with y hy
      simp_rw [Function.comp_apply, (j.1.extend I).left_inv hy]
    · simp_rw [Function.comp_apply, i.1.extend_left_inv hxi, j.1.extend_left_inv hxj]
    · exact (I.contDiffWithinAt_extendCoordChange' (subset_maximalAtlas j.2)
        (subset_maximalAtlas k.2) hxj hxk).differentiableWithinAt one_ne_zero
    · exact (I.contDiffWithinAt_extendCoordChange' (subset_maximalAtlas i.2)
        (subset_maximalAtlas j.2) hxi hxj).differentiableWithinAt one_ne_zero
    · intro x _; exact mem_range_self _
    · exact I.uniqueDiffWithinAt_image
    · rw [Function.comp_apply, i.1.extend_left_inv hxi]

/--
theorem `tangentBundleCore_baseSet` / 定理 `tangentBundleCore_baseSet`

English:
theorem tangentBundleCore_baseSet
  given: (i)
  statement: (tangentBundleCore I M).baseSet i = i.1.source
  proof: rfl

@[simp]

中文:
定理 tangentBundleCore_baseSet
  条件: (i)
  结论: (tangentBundleCore I M).baseSet i = i.1.source
  证明: rfl

@[simp]
-/
theorem tangentBundleCore_baseSet (i) : (tangentBundleCore I M).baseSet i = i.1.source := rfl

@[simp]
/--
theorem `tangentBundleCore_localTriv_baseSet` / 定理 `tangentBundleCore_localTriv_baseSet`

English:
theorem tangentBundleCore_localTriv_baseSet
  given: (i)
  proof: rfl

中文:
定理 tangentBundleCore_localTriv_baseSet
  条件: (i)
  证明: rfl
-/
theorem tangentBundleCore_localTriv_baseSet (i) :
    ((tangentBundleCore I M).localTriv i).baseSet = i.1.source := rfl

/--
theorem `tangentBundleCore_coordChange_achart` / 定理 `tangentBundleCore_coordChange_achart`

English:
theorem tangentBundleCore_coordChange_achart
  given: (x x' z : M)
  proof: rfl

中文:
定理 tangentBundleCore_coordChange_achart
  条件: (x x' z : M)
  证明: rfl
-/
theorem tangentBundleCore_coordChange_achart (x x' z : M) :
    (tangentBundleCore I M).coordChange (achart H x) (achart H x') z =
      fderivWithin 𝕜 (extChartAt I x' ∘ (extChartAt I x).symm) (range I) (extChartAt I x z) :=
  rfl

section tangentCoordChange

variable (I) in
/--
Definition of `tangentCoordChange` / `tangentCoordChange` 的定义

English:
abbreviation tangentCoordChange
  signature: (x y : M)
  body: (tangentBundleCore I M).coordChange (achart H x) (achart H y)

中文:
缩写 tangentCoordChange
  签名: (x y : M)
  定义体: (tangentBundleCore I M).coordChange (achart H x) (achart H y)

Depends on / 依赖: achart, coordChange, tangentBundleCore
-/
abbrev tangentCoordChange (x y : M) : M -> E ->L[𝕜] E :=
  (tangentBundleCore I M).coordChange (achart H x) (achart H y)

/--
lemma `tangentCoordChange_def` / 引理 `tangentCoordChange_def`

English:
lemma tangentCoordChange_def
  given: {x y z : M}
  statement: tangentCoordChange I x y z =
  proof: rfl

中文:
引理 tangentCoordChange_def
  条件: {x y z : M}
  结论: tangentCoordChange I x y z =
  证明: rfl
-/
lemma tangentCoordChange_def {x y z : M} : tangentCoordChange I x y z =
    fderivWithin 𝕜 (extChartAt I y ∘ (extChartAt I x).symm) (range I) (extChartAt I x z) := rfl

/--
lemma `tangentCoordChange_self` / 引理 `tangentCoordChange_self`

English:
lemma tangentCoordChange_self
  given: {x z : M} {v : E} (h : z in (extChartAt I x).source)
  proof: by
  apply (tangentBundleCore I M).coordChange_self
  rw [tangentBundleCore_baseSet]; rw [coe_achart]; rw [← extChartAt_source I]
  exact h

中文:
引理 tangentCoordChange_self
  条件: {x z : M} {v : E} (h : z in (extChartAt I x).source)
  证明: by
  apply (tangentBundleCore I M).coordChange_self
  rw [tangentBundleCore_baseSet]; rw [coe_achart]; rw [← extChartAt_source I]
  exact h

Depends on / 依赖: coe_achart, coordChange_self, extChartAt_source, tangentBundleCore, tangentBundleCore_baseSet
-/
lemma tangentCoordChange_self {x z : M} {v : E} (h : z in (extChartAt I x).source) :
    tangentCoordChange I x x z v = v := by
  apply (tangentBundleCore I M).coordChange_self
  rw [tangentBundleCore_baseSet]; rw [coe_achart]; rw [← extChartAt_source I]
  exact h

/--
lemma `tangentCoordChange_comp` / 引理 `tangentCoordChange_comp`

English:
lemma tangentCoordChange_comp
  statement: {w x y z : M} {v : E}
  proof: by
  apply (tangentBundleCore I M).coordChange_comp
  simp only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]
  exact h

中文:
引理 tangentCoordChange_comp
  结论: {w x y z : M} {v : E}
  证明: by
  apply (tangentBundleCore I M).coordChange_comp
  simp only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]
  exact h

Depends on / 依赖: coe_achart, coordChange_comp, extChartAt_source, tangentBundleCore, tangentBundleCore_baseSet
-/
lemma tangentCoordChange_comp {w x y z : M} {v : E}
    (h : z in (extChartAt I w).source inter (extChartAt I x).source inter (extChartAt I y).source) :
    tangentCoordChange I x y z (tangentCoordChange I w x z v) = tangentCoordChange I w y z v := by
  apply (tangentBundleCore I M).coordChange_comp
  simp only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]
  exact h

/--
lemma `hasFDerivWithinAt_tangentCoordChange` / 引理 `hasFDerivWithinAt_tangentCoordChange`

English:
lemma hasFDerivWithinAt_tangentCoordChange
  statement: {x y z : M}
  proof: have h' : extChartAt I x z in ((extChartAt I x).symm ≫ (extChartAt I y)).source := by
    rw [PartialEquiv.trans_source'']; rw [PartialEquiv.symm_symm]; rw [PartialEquiv.symm_target]
    exact mem_image_of_mem _ h
  ((contDiffWithinAt_ext_coord_change y x h').differentiableWithinAt one_ne_zero).hasF

中文:
引理 hasFDerivWithinAt_tangentCoordChange
  结论: {x y z : M}
  证明: have h' : extChartAt I x z in ((extChartAt I x).symm ≫ (extChartAt I y)).source := by
    rw [PartialEquiv.trans_source'']; rw [PartialEquiv.symm_symm]; rw [PartialEquiv.symm_target]
    exact mem_image_of_mem _ h
  ((contDiffWithinAt_ext_coord_change y x h').differentiableWithinAt one_ne_zero).hasF

Depends on / 依赖: PartialEquiv, PartialEquiv.symm_symm, PartialEquiv.symm_target, PartialEquiv.trans_source, contDiffWithinAt_ext_coord_change, differentiableWithinAt, extChartAt, hasFDerivWithinAt, mem_image_of_mem, one_ne_zero, source, symm_symm, symm_target, trans_source
-/
lemma hasFDerivWithinAt_tangentCoordChange {x y z : M}
    (h : z in (extChartAt I x).source inter (extChartAt I y).source) :
    HasFDerivWithinAt ((extChartAt I y) ∘ (extChartAt I x).symm) (tangentCoordChange I x y z)
      (range I) (extChartAt I x z) :=
  have h' : extChartAt I x z in ((extChartAt I x).symm ≫ (extChartAt I y)).source := by
    rw [PartialEquiv.trans_source'']; rw [PartialEquiv.symm_symm]; rw [PartialEquiv.symm_target]
    exact mem_image_of_mem _ h
  ((contDiffWithinAt_ext_coord_change y x h').differentiableWithinAt one_ne_zero).hasFDerivWithinAt

/--
lemma `continuousOn_tangentCoordChange` / 引理 `continuousOn_tangentCoordChange`

English:
lemma continuousOn_tangentCoordChange
  given: (x y : M)
  statement: ContinuousOn (tangentCoordChange I x y)
  proof: by
  convert! (tangentBundleCore I M).continuousOn_coordChange (achart H x) (achart H y) <;>
  simp only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]

中文:
引理 continuousOn_tangentCoordChange
  条件: (x y : M)
  结论: ContinuousOn (tangentCoordChange I x y)
  证明: by
  convert! (tangentBundleCore I M).continuousOn_coordChange (achart H x) (achart H y) <;>
  simp only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]

Depends on / 依赖: achart, coe_achart, continuousOn_coordChange, convert, extChartAt_source, tangentBundleCore, tangentBundleCore_baseSet
-/
lemma continuousOn_tangentCoordChange (x y : M) : ContinuousOn (tangentCoordChange I x y)
    ((extChartAt I x).source inter (extChartAt I y).source) := by
  convert! (tangentBundleCore I M).continuousOn_coordChange (achart H x) (achart H y) <;>
  simp only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]

end tangentCoordChange

local notation "TM" => TangentBundle I M

section TangentBundleInstances

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace TM
  body: inferInstanceAs TopologicalSpace (tangentBundleCore I M).TotalSpace

中文:
实例 :
  签名: TopologicalSpace TM
  定义体: inferInstanceAs TopologicalSpace (tangentBundleCore I M).TotalSpace

Depends on / 依赖: TopologicalSpace, TotalSpace, tangentBundleCore
-/
instance : TopologicalSpace TM :=
inferInstanceAs TopologicalSpace (tangentBundleCore I M).TotalSpace

/--
Instance `TangentSpace.fiberBundle` / 实例 `TangentSpace.fiberBundle`

English:
instance TangentSpace.fiberBundle
  signature: : FiberBundle E (TangentSpace I : M -> Type _)
  body: inferInstanceAs FiberBundle E (tangentBundleCore I M).Fiber

中文:
实例 TangentSpace.fiberBundle
  签名: : FiberBundle E (TangentSpace I : M -> Type _)
  定义体: inferInstanceAs FiberBundle E (tangentBundleCore I M).Fiber

Depends on / 依赖: FiberBundle, tangentBundleCore
-/
instance TangentSpace.fiberBundle : FiberBundle E (TangentSpace I : M -> Type _) :=
inferInstanceAs FiberBundle E (tangentBundleCore I M).Fiber

/--
Instance `TangentSpace.vectorBundle` / 实例 `TangentSpace.vectorBundle`

English:
instance TangentSpace.vectorBundle
  signature: : VectorBundle 𝕜 E (TangentSpace I : M -> Type _)
  body: inferInstanceAs VectorBundle 𝕜 E (tangentBundleCore I M).Fiber

中文:
实例 TangentSpace.vectorBundle
  签名: : VectorBundle 𝕜 E (TangentSpace I : M -> Type _)
  定义体: inferInstanceAs VectorBundle 𝕜 E (tangentBundleCore I M).Fiber

Depends on / 依赖: VectorBundle, tangentBundleCore
-/
instance TangentSpace.vectorBundle : VectorBundle 𝕜 E (TangentSpace I : M -> Type _) :=
inferInstanceAs VectorBundle 𝕜 E (tangentBundleCore I M).Fiber

namespace TangentBundle

/--
theorem `chartAt` / 定理 `chartAt`

English:
theorem chartAt
  given: (p : TM)
  proof: rfl

中文:
定理 chartAt
  条件: (p : TM)
  证明: rfl
-/
protected theorem chartAt (p : TM) :
    chartAt (ModelProd H E) p =
      ((tangentBundleCore I M).toFiberBundleCore.localTriv
        (achart H p.1)).toOpenPartialHomeomorph ≫ₕ
        (chartAt H p.1).prod (OpenPartialHomeomorph.refl E) :=
  rfl

/--
theorem `chartAt_toPartialEquiv` / 定理 `chartAt_toPartialEquiv`

English:
theorem chartAt_toPartialEquiv
  given: (p : TM)
  proof: rfl

中文:
定理 chartAt_toPartialEquiv
  条件: (p : TM)
  证明: rfl
-/
theorem chartAt_toPartialEquiv (p : TM) :
    (chartAt (ModelProd H E) p).toPartialEquiv =
      (tangentBundleCore I M).toFiberBundleCore.localTrivAsPartialEquiv (achart H p.1) ≫
        (chartAt H p.1).toPartialEquiv.prod (PartialEquiv.refl E) :=
  rfl

/--
theorem `trivializationAt_eq_localTriv` / 定理 `trivializationAt_eq_localTriv`

English:
theorem trivializationAt_eq_localTriv
  given: (x : M)
  proof: rfl

@[simp, mfld_simps]

中文:
定理 trivializationAt_eq_localTriv
  条件: (x : M)
  证明: rfl

@[simp, mfld_simps]
-/
theorem trivializationAt_eq_localTriv (x : M) :
    trivializationAt E (TangentSpace I) x =
      (tangentBundleCore I M).toFiberBundleCore.localTriv (achart H x) :=
  rfl

@[simp, mfld_simps]
/--
theorem `trivializationAt_source` / 定理 `trivializationAt_source`

English:
theorem trivializationAt_source
  given: (x : M)
  proof: rfl

@[simp, mfld_simps]

中文:
定理 trivializationAt_source
  条件: (x : M)
  证明: rfl

@[simp, mfld_simps]
-/
theorem trivializationAt_source (x : M) :
    (trivializationAt E (TangentSpace I) x).source =
      π E (TangentSpace I) ⁻¹' (chartAt H x).source :=
  rfl

@[simp, mfld_simps]
/--
theorem `trivializationAt_target` / 定理 `trivializationAt_target`

English:
theorem trivializationAt_target
  given: (x : M)
  proof: rfl

@[simp, mfld_simps]

中文:
定理 trivializationAt_target
  条件: (x : M)
  证明: rfl

@[simp, mfld_simps]
-/
theorem trivializationAt_target (x : M) :
    (trivializationAt E (TangentSpace I) x).target = (chartAt H x).source ×ˢ univ :=
  rfl

@[simp, mfld_simps]
/--
theorem `trivializationAt_baseSet` / 定理 `trivializationAt_baseSet`

English:
theorem trivializationAt_baseSet
  given: (x : M)
  proof: rfl

中文:
定理 trivializationAt_baseSet
  条件: (x : M)
  证明: rfl
-/
theorem trivializationAt_baseSet (x : M) :
    (trivializationAt E (TangentSpace I) x).baseSet = (chartAt H x).source :=
  rfl

/--
theorem `trivializationAt_apply` / 定理 `trivializationAt_apply`

English:
theorem trivializationAt_apply
  given: (x : M) (z : TM)
  proof: rfl

@[simp, mfld_simps]

中文:
定理 trivializationAt_apply
  条件: (x : M) (z : TM)
  证明: rfl

@[simp, mfld_simps]
-/
theorem trivializationAt_apply (x : M) (z : TM) :
    trivializationAt E (TangentSpace I) x z =
      (z.1, fderivWithin 𝕜 ((chartAt H x).extend I ∘ ((chartAt H z.1).extend I).symm) (range I)
        ((chartAt H z.1).extend I z.1) z.2) :=
  rfl

@[simp, mfld_simps]
/--
theorem `trivializationAt_fst` / 定理 `trivializationAt_fst`

English:
theorem trivializationAt_fst
  given: (x : M) (z : TM)
  statement: (trivializationAt E (TangentSpace I) x z).1 = z.1
  proof: rfl

@[simp, mfld_simps]

中文:
定理 trivializationAt_fst
  条件: (x : M) (z : TM)
  结论: (trivializationAt E (TangentSpace I) x z).1 = z.1
  证明: rfl

@[simp, mfld_simps]
-/
theorem trivializationAt_fst (x : M) (z : TM) : (trivializationAt E (TangentSpace I) x z).1 = z.1 :=
  rfl

@[simp, mfld_simps]
/--
theorem `mem_chart_source_iff` / 定理 `mem_chart_source_iff`

English:
theorem mem_chart_source_iff
  given: (p q : TM)
  proof: by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]

中文:
定理 mem_chart_source_iff
  条件: (p q : TM)
  证明: by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]

Depends on / 依赖: FiberBundle, FiberBundle.chartedSpace_chartAt, chartedSpace_chartAt, mfld_simps
-/
theorem mem_chart_source_iff (p q : TM) :
    p in (chartAt (ModelProd H E) q).source ↔ p.1 in (chartAt H q.1).source := by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]

set_option backward.isDefEq.respectTransparency false in
@[simp, mfld_simps]
/--
theorem `mem_chart_target_iff` / 定理 `mem_chart_target_iff`

English:
theorem mem_chart_target_iff
  given: (p : H × E) (q : TM)
  proof: by
  /- porting note: was
  simp +contextual only [FiberBundle.chartedSpace_chartAt,
    and_iff_left_iff_imp, mfld_simps]
  -/
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]
  rw [PartialEquiv.prod_symm]
  simp +contextual only [and_iff_left_iff_imp, mfld_simps]

@[simp, mfld_simps]

中文:
定理 mem_chart_target_iff
  条件: (p : H × E) (q : TM)
  证明: by
  /- porting note: was
  simp +contextual only [FiberBundle.chartedSpace_chartAt,
    and_iff_left_iff_imp, mfld_simps]
  -/
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]
  rw [PartialEquiv.prod_symm]
  simp +contextual only [and_iff_left_iff_imp, mfld_simps]

@[simp, mfld_simps]
-/
theorem mem_chart_target_iff (p : H × E) (q : TM) :
    p in (chartAt (ModelProd H E) q).target ↔ p.1 in (chartAt H q.1).target := by
  /- porting note: was
  simp +contextual only [FiberBundle.chartedSpace_chartAt,
    and_iff_left_iff_imp, mfld_simps]
  -/
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]
  rw [PartialEquiv.prod_symm]
  simp +contextual only [and_iff_left_iff_imp, mfld_simps]

@[simp, mfld_simps]
/--
theorem `coe_chartAt_fst` / 定理 `coe_chartAt_fst`

English:
theorem coe_chartAt_fst
  given: (p q : TM)
  statement: ((chartAt (ModelProd H E) q) p).1 = chartAt H q.1 p.1
  proof: rfl

@[simp, mfld_simps]

中文:
定理 coe_chartAt_fst
  条件: (p q : TM)
  结论: ((chartAt (ModelProd H E) q) p).1 = chartAt H q.1 p.1
  证明: rfl

@[simp, mfld_simps]
-/
theorem coe_chartAt_fst (p q : TM) : ((chartAt (ModelProd H E) q) p).1 = chartAt H q.1 p.1 :=
  rfl

@[simp, mfld_simps]
/--
theorem `coe_chartAt_symm_fst` / 定理 `coe_chartAt_symm_fst`

English:
theorem coe_chartAt_symm_fst
  given: (p : H × E) (q : TM)
  proof: rfl

中文:
定理 coe_chartAt_symm_fst
  条件: (p : H × E) (q : TM)
  证明: rfl
-/
theorem coe_chartAt_symm_fst (p : H × E) (q : TM) :
    ((chartAt (ModelProd H E) q).symm p).1 = ((chartAt H q.1).symm : H -> M) p.1 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `continuousLinearMapAt_trivializationAt_eq_core` / 定理 `continuousLinearMapAt_trivializationAt_eq_core`

English:
theorem continuousLinearMapAt_trivializationAt_eq_core
  given: {b₀ b : M} (hb : b in (chartAt H b₀).source)
  proof: by
  simp [hb]

中文:
定理 continuousLinearMapAt_trivializationAt_eq_core
  条件: {b₀ b : M} (hb : b in (chartAt H b₀).source)
  证明: by
  simp [hb]
-/
theorem continuousLinearMapAt_trivializationAt_eq_core {b₀ b : M} (hb : b in (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt 𝕜 b =
      (tangentBundleCore I M).coordChange (achart H b) (achart H b₀) b := by
  simp [hb]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `symmL_trivializationAt_eq_core` / 定理 `symmL_trivializationAt_eq_core`

English:
theorem symmL_trivializationAt_eq_core
  given: {b₀ b : M} (hb : b in (chartAt H b₀).source)
  proof: by
  simp [hb]

中文:
定理 symmL_trivializationAt_eq_core
  条件: {b₀ b : M} (hb : b in (chartAt H b₀).source)
  证明: by
  simp [hb]
-/
theorem symmL_trivializationAt_eq_core {b₀ b : M} (hb : b in (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).symmL 𝕜 b =
      (tangentBundleCore I M).coordChange (achart H b₀) (achart H b) b := by
  simp [hb]

/-! The lemmas below have high priority because `simp` simplifies the LHS to `.id _ _`;
we prefer `1` as the simp-normal form. -/
@[simp high, mfld_simps]
/--
theorem `coordChange_model_space` / 定理 `coordChange_model_space`

English:
theorem coordChange_model_space
  given: (b b' x : F)
  proof: by
  simpa only [tangentBundleCore_coordChange, mfld_simps] using!
    fderivWithin_id uniqueDiffWithinAt_univ

@[simp high, mfld_simps]

中文:
定理 coordChange_model_space
  条件: (b b' x : F)
  证明: by
  simpa only [tangentBundleCore_coordChange, mfld_simps] using!
    fderivWithin_id uniqueDiffWithinAt_univ

@[simp high, mfld_simps]

Depends on / 依赖: fderivWithin_id, mfld_simps, tangentBundleCore_coordChange, uniqueDiffWithinAt_univ
-/
theorem coordChange_model_space (b b' x : F) :
    (tangentBundleCore 𝓘(𝕜, F) F).coordChange (achart F b) (achart F b') x = 1 := by
  simpa only [tangentBundleCore_coordChange, mfld_simps] using!
    fderivWithin_id uniqueDiffWithinAt_univ

@[simp high, mfld_simps]
/--
theorem `symmL_model_space` / 定理 `symmL_model_space`

English:
theorem symmL_model_space
  given: (b b' : F)
  proof: by
  rw [TangentBundle.symmL_trivializationAt_eq_core]; rw [coordChange_model_space]
  apply mem_univ

@[simp high, mfld_simps]

中文:
定理 symmL_model_space
  条件: (b b' : F)
  证明: by
  rw [TangentBundle.symmL_trivializationAt_eq_core]; rw [coordChange_model_space]
  apply mem_univ

@[simp high, mfld_simps]

Depends on / 依赖: TangentBundle, TangentBundle.symmL_trivializationAt_eq_core, coordChange_model_space, mem_univ, symmL_trivializationAt_eq_core
-/
theorem symmL_model_space (b b' : F) :
    (trivializationAt F (TangentSpace 𝓘(𝕜, F)) b).symmL 𝕜 b' = (1 : F ->L[𝕜] F) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core]; rw [coordChange_model_space]
  apply mem_univ

@[simp high, mfld_simps]
/--
theorem `continuousLinearMapAt_model_space` / 定理 `continuousLinearMapAt_model_space`

English:
theorem continuousLinearMapAt_model_space
  given: (b b' : F)
  proof: by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core]; rw [coordChange_model_space]
  apply mem_univ

中文:
定理 continuousLinearMapAt_model_space
  条件: (b b' : F)
  证明: by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core]; rw [coordChange_model_space]
  apply mem_univ

Depends on / 依赖: TangentBundle, TangentBundle.continuousLinearMapAt_trivializationAt_eq_core, continuousLinearMapAt_trivializationAt_eq_core, coordChange_model_space, mem_univ
-/
theorem continuousLinearMapAt_model_space (b b' : F) :
    (trivializationAt F (TangentSpace 𝓘(𝕜, F)) b).continuousLinearMapAt 𝕜 b' = (1 : F ->L[𝕜] F) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core]; rw [coordChange_model_space]
  apply mem_univ

end TangentBundle

omit [IsManifold I 1 M] in
/--
lemma `tangentBundleCore.isContMDiff` / 引理 `tangentBundleCore.isContMDiff`

English:
lemma tangentBundleCore.isContMDiff
  given: [h : IsManifold I (n + 1) M]
  proof: .of_le (n := n + 1) le_add_self
    (tangentBundleCore I M).IsContMDiff I n := by
  have : IsManifold I n M := .of_le (n := n + 1) (le_self_add)
  refine ⟨fun i j => ?_⟩
  rw [contMDiffOn_iff_source_of_mem_maximalAtlas (subset_maximalAtlas i.2)]; rw [contMDiffOn_iff_contDiffOn]
  · refine ((contDiff

中文:
引理 tangentBundleCore.isContMDiff
  条件: [h : IsManifold I (n + 1) M]
  证明: .of_le (n := n + 1) le_add_self
    (tangentBundleCore I M).IsContMDiff I n := by
  have : IsManifold I n M := .of_le (n := n + 1) (le_self_add)
  refine ⟨fun i j => ?_⟩
  rw [contMDiffOn_iff_source_of_mem_maximalAtlas (subset_maximalAtlas i.2)]; rw [contMDiffOn_iff_contDiffOn]
  · refine ((contDiff

Depends on / 依赖: le_add_self, of_le
-/
lemma tangentBundleCore.isContMDiff [h : IsManifold I (n + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    (tangentBundleCore I M).IsContMDiff I n := by
  have : IsManifold I n M := .of_le (n := n + 1) (le_self_add)
  refine ⟨fun i j => ?_⟩
  rw [contMDiffOn_iff_source_of_mem_maximalAtlas (subset_maximalAtlas i.2)]; rw [contMDiffOn_iff_contDiffOn]
  · refine ((contDiffOn_fderiv_coord_change (I := I) i j).congr fun x hx => ?_).mono ?_
    · rw [PartialEquiv.trans_source'] at hx
      simp_rw [Function.comp_apply, tangentBundleCore_coordChange, (i.1.extend I).right_inv hx.1]
    · exact (i.1.extend_image_source_inter j.1).subset
  · apply inter_subset_left

omit [IsManifold I 1 M] in
/--
lemma `TangentBundle.contMDiffVectorBundle` / 引理 `TangentBundle.contMDiffVectorBundle`

English:
lemma TangentBundle.contMDiffVectorBundle
  given: [h : IsManifold I (n + 1) M]
  proof: .of_le (n := n + 1) le_add_self
    ContMDiffVectorBundle n E (TangentSpace I : M -> Type _) I := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : (tangentBundleCore I M).IsContMDiff I n := tangentBundleCore.isContMDiff
  exact (tangentBundleCore I M).instContMDiffVectorBundl

中文:
引理 TangentBundle.contMDiffVectorBundle
  条件: [h : IsManifold I (n + 1) M]
  证明: .of_le (n := n + 1) le_add_self
    ContMDiffVectorBundle n E (TangentSpace I : M -> Type _) I := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : (tangentBundleCore I M).IsContMDiff I n := tangentBundleCore.isContMDiff
  exact (tangentBundleCore I M).instContMDiffVectorBundl

Depends on / 依赖: le_add_self, of_le
-/
lemma TangentBundle.contMDiffVectorBundle [h : IsManifold I (n + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    ContMDiffVectorBundle n E (TangentSpace I : M -> Type _) I := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : (tangentBundleCore I M).IsContMDiff I n := tangentBundleCore.isContMDiff
  exact (tangentBundleCore I M).instContMDiffVectorBundle

omit [IsManifold I 1 M] in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : IsManifold I ∞ M] :
  body: by
  have : IsManifold I (∞ + 1) M := h
  exact TangentBundle.contMDiffVectorBundle

omit [IsManifold I 1 M] in

中文:
实例 [h
  签名: : IsManifold I ∞ M] :
  定义体: by
  have : IsManifold I (∞ + 1) M := h
  exact TangentBundle.contMDiffVectorBundle

omit [IsManifold I 1 M] in

Depends on / 依赖: IsManifold, TangentBundle, TangentBundle.contMDiffVectorBundle, contMDiffVectorBundle
-/
instance [h : IsManifold I ∞ M] :
    ContMDiffVectorBundle ∞ E (TangentSpace I : M -> Type _) I := by
  have : IsManifold I (∞ + 1) M := h
  exact TangentBundle.contMDiffVectorBundle

omit [IsManifold I 1 M] in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsManifold
  signature: I ω M] :
  body: TangentBundle.contMDiffVectorBundle

omit [IsManifold I 1 M] in

中文:
实例 [IsManifold
  签名: I ω M] :
  定义体: TangentBundle.contMDiffVectorBundle

omit [IsManifold I 1 M] in

Depends on / 依赖: TangentBundle, TangentBundle.contMDiffVectorBundle, contMDiffVectorBundle
-/
instance [IsManifold I ω M] :
    ContMDiffVectorBundle ω E (TangentSpace I : M -> Type _) I :=
  TangentBundle.contMDiffVectorBundle

omit [IsManifold I 1 M] in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : IsManifold I 2 M] :
  body: by
  have : IsManifold I (1 + 1) M := h
  exact TangentBundle.contMDiffVectorBundle

中文:
实例 [h
  签名: : IsManifold I 2 M] :
  定义体: by
  have : IsManifold I (1 + 1) M := h
  exact TangentBundle.contMDiffVectorBundle

Depends on / 依赖: IsManifold, TangentBundle, TangentBundle.contMDiffVectorBundle, contMDiffVectorBundle
-/
instance [h : IsManifold I 2 M] :
    ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I := by
  have : IsManifold I (1 + 1) M := h
  exact TangentBundle.contMDiffVectorBundle

end TangentBundleInstances

/-! ## The tangent bundle to the model space -/

set_option backward.isDefEq.respectTransparency false in
@[simp, mfld_simps]
/--
theorem `trivializationAt_model_space_apply` / 定理 `trivializationAt_model_space_apply`

English:
theorem trivializationAt_model_space_apply
  given: (p : TangentBundle I H) (x : H)
  proof: by
  simp only [TangentBundle.trivializationAt_apply]
  have : fderivWithin 𝕜 (↑I ∘ ↑I.symm) (range I) (I p.proj) =
      fderivWithin 𝕜 id (range I) (I p.proj) :=
    fderivWithin_congr' (fun y hy => by simp [hy]) (mem_range_self p.proj)
  simp [this, fderivWithin_id (ModelWithCorners.uniqueDiffWit

中文:
定理 trivializationAt_model_space_apply
  条件: (p : TangentBundle I H) (x : H)
  证明: by
  simp only [TangentBundle.trivializationAt_apply]
  have : fderivWithin 𝕜 (↑I ∘ ↑I.symm) (range I) (I p.proj) =
      fderivWithin 𝕜 id (range I) (I p.proj) :=
    fderivWithin_congr' (fun y hy => by simp [hy]) (mem_range_self p.proj)
  simp [this, fderivWithin_id (ModelWithCorners.uniqueDiffWit

Depends on / 依赖: I.symm, ModelWithCorners, ModelWithCorners.uniqueDiffWithinAt_image, TangentBundle, TangentBundle.trivializationAt_apply, fderivWithin, fderivWithin_congr, fderivWithin_id, mem_range_self, p.proj, trivializationAt_apply, uniqueDiffWithinAt_image
-/
theorem trivializationAt_model_space_apply (p : TangentBundle I H) (x : H) :
    trivializationAt E (TangentSpace I) x p = (p.1, p.2) := by
  simp only [TangentBundle.trivializationAt_apply]
  have : fderivWithin 𝕜 (↑I ∘ ↑I.symm) (range I) (I p.proj) =
      fderivWithin 𝕜 id (range I) (I p.proj) :=
    fderivWithin_congr' (fun y hy => by simp [hy]) (mem_range_self p.proj)
  simp [this, fderivWithin_id (ModelWithCorners.uniqueDiffWithinAt_image I)]

set_option backward.isDefEq.respectTransparency false in
/-- In the tangent bundle to the model space, the charts are just the canonical identification
between a product type and a sigma type, a.k.a. `TotalSpace.toProd`. -/
@[simp, mfld_simps]
/--
theorem `tangentBundle_model_space_chartAt` / 定理 `tangentBundle_model_space_chartAt`

English:
theorem tangentBundle_model_space_chartAt
  given: (p : TangentBundle I H)
  proof: by
  ext x : 1
  · ext; · rfl
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  · ext; · rfl
    apply heq_of_eq
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  simp_rw [TangentBundle.chartAt, F

中文:
定理 tangentBundle_model_space_chartAt
  条件: (p : TangentBundle I H)
  证明: by
  ext x : 1
  · ext; · rfl
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  · ext; · rfl
    apply heq_of_eq
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  simp_rw [TangentBundle.chartAt, F

Depends on / 依赖: FiberBundleCore, FiberBundleCore.localTriv, FiberBundleCore.localTrivAsPartialEquiv, TangentBundle, TangentBundle.chartAt, VectorBundleCore, VectorBundleCore.toFiberBundleCore_baseSet, achart, chartAt, coordChange_self, heq_of_eq, localTriv, localTrivAsPartialEquiv, mem_achart_source, mfld_simps, simp_rw, tangentBundleCore, tangentBundleCore_baseSet, toFiberBundleCore_baseSet
-/
theorem tangentBundle_model_space_chartAt (p : TangentBundle I H) :
    (chartAt (ModelProd H E) p).toPartialEquiv = (TotalSpace.toProd H E).toPartialEquiv := by
  ext x : 1
  · ext; · rfl
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  · ext; · rfl
    apply heq_of_eq
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  simp_rw [TangentBundle.chartAt, FiberBundleCore.localTriv,
    FiberBundleCore.localTrivAsPartialEquiv, VectorBundleCore.toFiberBundleCore_baseSet,
    tangentBundleCore_baseSet]
  simp only [mfld_simps]

@[simp, mfld_simps]
/--
theorem `tangentBundle_model_space_coe_chartAt` / 定理 `tangentBundle_model_space_coe_chartAt`

English:
theorem tangentBundle_model_space_coe_chartAt
  given: (p : TangentBundle I H)
  proof: by
  rw [← OpenPartialHomeomorph.coe_toPartialEquiv]; rw [tangentBundle_model_space_chartAt]; rfl

@[simp, mfld_simps]

中文:
定理 tangentBundle_model_space_coe_chartAt
  条件: (p : TangentBundle I H)
  证明: by
  rw [← OpenPartialHomeomorph.coe_toPartialEquiv]; rw [tangentBundle_model_space_chartAt]; rfl

@[simp, mfld_simps]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.coe_toPartialEquiv, coe_toPartialEquiv, tangentBundle_model_space_chartAt
-/
theorem tangentBundle_model_space_coe_chartAt (p : TangentBundle I H) :
    ⇑(chartAt (ModelProd H E) p) = TotalSpace.toProd H E := by
  rw [← OpenPartialHomeomorph.coe_toPartialEquiv]; rw [tangentBundle_model_space_chartAt]; rfl

@[simp, mfld_simps]
/--
theorem `tangentBundle_model_space_coe_chartAt_symm` / 定理 `tangentBundle_model_space_coe_chartAt_symm`

English:
theorem tangentBundle_model_space_coe_chartAt_symm
  given: (p : TangentBundle I H)
  proof: by
  rw [← OpenPartialHomeomorph.coe_toPartialEquiv]; rw [OpenPartialHomeomorph.symm_toPartialEquiv]; rw [tangentBundle_model_space_chartAt]; rfl

中文:
定理 tangentBundle_model_space_coe_chartAt_symm
  条件: (p : TangentBundle I H)
  证明: by
  rw [← OpenPartialHomeomorph.coe_toPartialEquiv]; rw [OpenPartialHomeomorph.symm_toPartialEquiv]; rw [tangentBundle_model_space_chartAt]; rfl

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.coe_toPartialEquiv, OpenPartialHomeomorph.symm_toPartialEquiv, coe_toPartialEquiv, symm_toPartialEquiv, tangentBundle_model_space_chartAt
-/
theorem tangentBundle_model_space_coe_chartAt_symm (p : TangentBundle I H) :
    ((chartAt (ModelProd H E) p).symm : ModelProd H E -> TangentBundle I H) =
      (TotalSpace.toProd H E).symm := by
  rw [← OpenPartialHomeomorph.coe_toPartialEquiv]; rw [OpenPartialHomeomorph.symm_toPartialEquiv]; rw [tangentBundle_model_space_chartAt]; rfl

/--
theorem `tangentBundleCore_coordChange_model_space` / 定理 `tangentBundleCore_coordChange_model_space`

English:
theorem tangentBundleCore_coordChange_model_space
  given: (x x' z : H)
  proof: by
  ext v; exact (tangentBundleCore I H).coordChange_self (achart _ z) z (mem_univ _) v

中文:
定理 tangentBundleCore_coordChange_model_space
  条件: (x x' z : H)
  证明: by
  ext v; exact (tangentBundleCore I H).coordChange_self (achart _ z) z (mem_univ _) v

Depends on / 依赖: achart, coordChange_self, mem_univ, tangentBundleCore
-/
theorem tangentBundleCore_coordChange_model_space (x x' z : H) :
    (tangentBundleCore I H).coordChange (achart H x) (achart H x') z =
    ContinuousLinearMap.id 𝕜 E := by
  ext v; exact (tangentBundleCore I H).coordChange_self (achart _ z) z (mem_univ _) v

set_option backward.isDefEq.respectTransparency false in
variable (I) in
/--
Definition of `tangentBundleModelSpaceHomeomorph` / `tangentBundleModelSpaceHomeomorph` 的定义

English:
definition tangentBundleModelSpaceHomeomorph
  signature: : TangentBundle I H ≃ₜ ModelProd H E
  body: { TotalSpace.toProd H E with
    continuous_toFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chartAt (ModelProd H E) p) := by
        rw [← continuousOn_univ]
        convert! (chartAt (ModelProd H E) p).continuousOn
        simp only [mfld_simps]
   

中文:
定义 tangentBundleModelSpaceHomeomorph
  签名: : TangentBundle I H ≃ₜ ModelProd H E
  定义体: { TotalSpace.toProd H E with
    continuous_toFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chartAt (ModelProd H E) p) := by
        rw [← continuousOn_univ]
        convert! (chartAt (ModelProd H E) p).continuousOn
        simp only [mfld_simps]
   

Depends on / 依赖: Continuous, I.symm, ModelProd, TangentBundle, TotalSpace, TotalSpace.toProd, chartAt, continuousOn, continuousOn_univ, continuous_invFun, continuous_toFun, convert, mfld_simps, symm.conti, toProd
-/
def tangentBundleModelSpaceHomeomorph : TangentBundle I H ≃ₜ ModelProd H E :=
  { TotalSpace.toProd H E with
    continuous_toFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chartAt (ModelProd H E) p) := by
        rw [← continuousOn_univ]
        convert! (chartAt (ModelProd H E) p).continuousOn
        simp only [mfld_simps]
      simpa only [mfld_simps] using this
    continuous_invFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chartAt (ModelProd H E) p).symm := by
        rw [← continuousOn_univ]
        convert! (chartAt (ModelProd H E) p).symm.continuousOn
        simp only [mfld_simps]
      simpa only [mfld_simps] using this }

@[simp, mfld_simps]
/--
theorem `tangentBundleModelSpaceHomeomorph_coe` / 定理 `tangentBundleModelSpaceHomeomorph_coe`

English:
theorem tangentBundleModelSpaceHomeomorph_coe
  proof: rfl

@[simp, mfld_simps]

中文:
定理 tangentBundleModelSpaceHomeomorph_coe
  证明: rfl

@[simp, mfld_simps]
-/
theorem tangentBundleModelSpaceHomeomorph_coe :
    (tangentBundleModelSpaceHomeomorph I : TangentBundle I H -> ModelProd H E) =
      TotalSpace.toProd H E :=
  rfl

@[simp, mfld_simps]
/--
theorem `tangentBundleModelSpaceHomeomorph_coe_symm` / 定理 `tangentBundleModelSpaceHomeomorph_coe_symm`

English:
theorem tangentBundleModelSpaceHomeomorph_coe_symm
  proof: rfl

中文:
定理 tangentBundleModelSpaceHomeomorph_coe_symm
  证明: rfl
-/
theorem tangentBundleModelSpaceHomeomorph_coe_symm :
    ((tangentBundleModelSpaceHomeomorph I).symm : ModelProd H E -> TangentBundle I H) =
      (TotalSpace.toProd H E).symm :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `contMDiff_tangentBundleModelSpaceHomeomorph` / 定理 `contMDiff_tangentBundleModelSpaceHomeomorph`

English:
theorem contMDiff_tangentBundleModelSpaceHomeomorph
  proof: by
  apply contMDiff_iff.2 ⟨Homeomorph.continuous _, fun x y => ?_⟩
  apply contDiffOn_id.congr
  simp only [mfld_simps, mem_range, TotalSpace.toProd, Equiv.coe_fn_symm_mk, forall_exists_index,
    Prod.forall, Prod.mk.injEq]
  rintro a b x rfl
  simp [PartialEquiv.prod]

中文:
定理 contMDiff_tangentBundleModelSpaceHomeomorph
  证明: by
  apply contMDiff_iff.2 ⟨Homeomorph.continuous _, fun x y => ?_⟩
  apply contDiffOn_id.congr
  simp only [mfld_simps, mem_range, TotalSpace.toProd, Equiv.coe_fn_symm_mk, forall_exists_index,
    Prod.forall, Prod.mk.injEq]
  rintro a b x rfl
  simp [PartialEquiv.prod]

Depends on / 依赖: Equiv.coe_fn_symm_mk, Homeomorph, Homeomorph.continuous, PartialEquiv, PartialEquiv.prod, Prod.forall, Prod.mk.injEq, TotalSpace, TotalSpace.toProd, coe_fn_symm_mk, contDiffOn_id, contDiffOn_id.congr, contMDiff_iff, continuous, forall_exists_index, mem_range, mfld_simps, toProd
-/
theorem contMDiff_tangentBundleModelSpaceHomeomorph :
    ContMDiff I.tangent (I.prod 𝓘(𝕜, E)) n
    (tangentBundleModelSpaceHomeomorph I : TangentBundle I H -> ModelProd H E) := by
  apply contMDiff_iff.2 ⟨Homeomorph.continuous _, fun x y => ?_⟩
  apply contDiffOn_id.congr
  simp only [mfld_simps, mem_range, TotalSpace.toProd, Equiv.coe_fn_symm_mk, forall_exists_index,
    Prod.forall, Prod.mk.injEq]
  rintro a b x rfl
  simp [PartialEquiv.prod]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `contMDiff_tangentBundleModelSpaceHomeomorph_symm` / 定理 `contMDiff_tangentBundleModelSpaceHomeomorph_symm`

English:
theorem contMDiff_tangentBundleModelSpaceHomeomorph_symm
  proof: by
  apply contMDiff_iff.2 ⟨Homeomorph.continuous _, fun x y => ?_⟩
  apply contDiffOn_id.congr
  simp only [mfld_simps, mem_range, TotalSpace.toProd, Equiv.coe_fn_symm_mk, forall_exists_index,
    Prod.forall, Prod.mk.injEq]
  rintro a b x rfl
  simpa [PartialEquiv.prod] using ⟨rfl, rfl⟩

中文:
定理 contMDiff_tangentBundleModelSpaceHomeomorph_symm
  证明: by
  apply contMDiff_iff.2 ⟨Homeomorph.continuous _, fun x y => ?_⟩
  apply contDiffOn_id.congr
  simp only [mfld_simps, mem_range, TotalSpace.toProd, Equiv.coe_fn_symm_mk, forall_exists_index,
    Prod.forall, Prod.mk.injEq]
  rintro a b x rfl
  simpa [PartialEquiv.prod] using ⟨rfl, rfl⟩

Depends on / 依赖: Equiv.coe_fn_symm_mk, Homeomorph, Homeomorph.continuous, PartialEquiv, PartialEquiv.prod, Prod.forall, Prod.mk.injEq, TotalSpace, TotalSpace.toProd, coe_fn_symm_mk, contDiffOn_id, contDiffOn_id.congr, contMDiff_iff, continuous, forall_exists_index, mem_range, mfld_simps, toProd
-/
theorem contMDiff_tangentBundleModelSpaceHomeomorph_symm :
    ContMDiff I.tangent I.tangent n
    ((tangentBundleModelSpaceHomeomorph I).symm : ModelProd H E -> TangentBundle I H) := by
  apply contMDiff_iff.2 ⟨Homeomorph.continuous _, fun x y => ?_⟩
  apply contDiffOn_id.congr
  simp only [mfld_simps, mem_range, TotalSpace.toProd, Equiv.coe_fn_symm_mk, forall_exists_index,
    Prod.forall, Prod.mk.injEq]
  rintro a b x rfl
  simpa [PartialEquiv.prod] using ⟨rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable (H I) in
/--
lemma `contMDiff_snd_tangentBundle_modelSpace` / 引理 `contMDiff_snd_tangentBundle_modelSpace`

English:
lemma contMDiff_snd_tangentBundle_modelSpace
  proof: by
  change CMDiff n ((id Prod.snd : ModelProd H E -> E) ∘ (tangentBundleModelSpaceHomeomorph I))
  apply ContMDiff.comp (I' := I.prod 𝓘(𝕜, E))
  · convert! contMDiff_snd
    rw [chartedSpaceSelf_prod]
    rfl
  · exact contMDiff_tangentBundleModelSpaceHomeomorph

中文:
引理 contMDiff_snd_tangentBundle_modelSpace
  证明: by
  change CMDiff n ((id Prod.snd : ModelProd H E -> E) ∘ (tangentBundleModelSpaceHomeomorph I))
  apply ContMDiff.comp (I' := I.prod 𝓘(𝕜, E))
  · convert! contMDiff_snd
    rw [chartedSpaceSelf_prod]
    rfl
  · exact contMDiff_tangentBundleModelSpaceHomeomorph

Depends on / 依赖: CMDiff, ContMDiff, ContMDiff.comp, I.prod, ModelProd, Prod.snd, chartedSpaceSelf_prod, contMDiff_snd, contMDiff_tangentBundleModelSpaceHomeomorph, convert, tangentBundleModelSpaceHomeomorph
-/
lemma contMDiff_snd_tangentBundle_modelSpace :
    ContMDiff I.tangent 𝓘(𝕜, E) n (fun (p : TangentBundle I H) => p.2) := by
  change CMDiff n ((id Prod.snd : ModelProd H E -> E) ∘ (tangentBundleModelSpaceHomeomorph I))
  apply ContMDiff.comp (I' := I.prod 𝓘(𝕜, E))
  · convert! contMDiff_snd
    rw [chartedSpaceSelf_prod]
    rfl
  · exact contMDiff_tangentBundleModelSpaceHomeomorph

/--
lemma `contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt` / 引理 `contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt`

English:
lemma contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
· exact ContMDiffWithinAt.contDiffWithinAt
      (contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).contMDiffAt.comp_contMDiffWithinAt _ h
  · apply Bundle.contMDiffWithinAt_totalSpace.2
    refine ⟨contMDiffWithinAt_id, ?_⟩
    convert! h.contMDiffWithinAt wit

中文:
引理 contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
· exact ContMDiffWithinAt.contDiffWithinAt
      (contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).contMDiffAt.comp_contMDiffWithinAt _ h
  · apply Bundle.contMDiffWithinAt_totalSpace.2
    refine ⟨contMDiffWithinAt_id, ?_⟩
    convert! h.contMDiffWithinAt wit

Depends on / 依赖: Bundle, Bundle.contMDiffWithinAt_totalSpace, ContMDiffWithinAt, ContMDiffWithinAt.contDiffWithinAt, comp_contMDiffWithinAt, contDiffWithinAt, contMDiffAt, contMDiffAt.comp_contMDiffWithinAt, contMDiffWithinAt, contMDiffWithinAt_id, contMDiffWithinAt_totalSpace, contMDiff_snd_tangentBundle_modelSpace, convert, h.contMDiffWithinAt
-/
lemma contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {s : Set E} {x : E} :
    CMDiffAt[s] n (T% V) x ↔ ContDiffWithinAt 𝕜 n V s x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
· exact ContMDiffWithinAt.contDiffWithinAt
      (contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).contMDiffAt.comp_contMDiffWithinAt _ h
  · apply Bundle.contMDiffWithinAt_totalSpace.2
    refine ⟨contMDiffWithinAt_id, ?_⟩
    convert! h.contMDiffWithinAt with y
    simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `contMDiffAt_vectorSpace_iff_contDiffAt` / 引理 `contMDiffAt_vectorSpace_iff_contDiffAt`

English:
lemma contMDiffAt_vectorSpace_iff_contDiffAt
  proof: by
  simp only [← contMDiffWithinAt_univ, ← contDiffWithinAt_univ,
    contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt]

中文:
引理 contMDiffAt_vectorSpace_iff_contDiffAt
  证明: by
  simp only [← contMDiffWithinAt_univ, ← contDiffWithinAt_univ,
    contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt]

Depends on / 依赖: contDiffWithinAt_univ, contMDiffWithinAt_univ, contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt
-/
lemma contMDiffAt_vectorSpace_iff_contDiffAt
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {x : E} :
    CMDiffAt n (T% V) x ↔ ContDiffAt 𝕜 n V x := by
  simp only [← contMDiffWithinAt_univ, ← contDiffWithinAt_univ,
    contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt]

/--
lemma `contMDiffOn_vectorSpace_iff_contDiffOn` / 引理 `contMDiffOn_vectorSpace_iff_contDiffOn`

English:
lemma contMDiffOn_vectorSpace_iff_contDiffOn
  proof: by
  simp only [ContMDiffOn, ContDiffOn, contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt]

中文:
引理 contMDiffOn_vectorSpace_iff_contDiffOn
  证明: by
  simp only [ContMDiffOn, ContDiffOn, contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt]

Depends on / 依赖: ContDiffOn, ContMDiffOn, contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt
-/
lemma contMDiffOn_vectorSpace_iff_contDiffOn
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {s : Set E} :
    CMDiff[s] n (T% V) ↔ ContDiffOn 𝕜 n V s := by
  simp only [ContMDiffOn, ContDiffOn, contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `contMDiff_vectorSpace_iff_contDiff` / 引理 `contMDiff_vectorSpace_iff_contDiff`

English:
lemma contMDiff_vectorSpace_iff_contDiff
  given: {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x}
  proof: by
  simp only [← contMDiffOn_univ, ← contDiffOn_univ, contMDiffOn_vectorSpace_iff_contDiffOn]

中文:
引理 contMDiff_vectorSpace_iff_contDiff
  条件: {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x}
  证明: by
  simp only [← contMDiffOn_univ, ← contDiffOn_univ, contMDiffOn_vectorSpace_iff_contDiffOn]

Depends on / 依赖: contDiffOn_univ, contMDiffOn_univ, contMDiffOn_vectorSpace_iff_contDiffOn
-/
lemma contMDiff_vectorSpace_iff_contDiff {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} :
    CMDiff n (T% V) ↔ ContDiff 𝕜 n V := by
  simp only [← contMDiffOn_univ, ← contDiffOn_univ, contMDiffOn_vectorSpace_iff_contDiffOn]

section inTangentCoordinates

variable {N : Type*}

/--
theorem `inCoordinates_tangent_bundle_core_model_space` / 定理 `inCoordinates_tangent_bundle_core_model_space`

English:
theorem inCoordinates_tangent_bundle_core_model_space
  given: (x₀ x : H) (y₀ y : H') (ϕ : E ->L[𝕜] E')
  proof: by
  erw [VectorBundleCore.inCoordinates_eq] <;> try trivial
  simp_rw [tangentBundleCore_indexAt, tangentBundleCore_coordChange_model_space,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

中文:
定理 inCoordinates_tangent_bundle_core_model_space
  条件: (x₀ x : H) (y₀ y : H') (ϕ : E ->L[𝕜] E')
  证明: by
  erw [VectorBundleCore.inCoordinates_eq] <;> try trivial
  simp_rw [tangentBundleCore_indexAt, tangentBundleCore_coordChange_model_space,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp, VectorBundleCore, VectorBundleCore.inCoordinates_eq, comp_id, id_comp, inCoordinates_eq, simp_rw, tangentBundleCore_coordChange_model_space, tangentBundleCore_indexAt
-/
theorem inCoordinates_tangent_bundle_core_model_space (x₀ x : H) (y₀ y : H') (ϕ : E ->L[𝕜] E') :
    inCoordinates E (TangentSpace I) E' (TangentSpace I') x₀ x y₀ y ϕ = ϕ := by
  erw [VectorBundleCore.inCoordinates_eq] <;> try trivial
  simp_rw [tangentBundleCore_indexAt, tangentBundleCore_coordChange_model_space,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

variable (I I') in
/--
Definition of `inTangentCoordinates` / `inTangentCoordinates` 的定义

English:
definition inTangentCoordinates
  signature: (f : N -> M) (g : N -> M') (ϕ : N -> E ->L[𝕜] E')
  body: fun x₀ x => inCoordinates E (TangentSpace I) E' (TangentSpace I') (f x₀) (f x) (g x₀) (g x) (ϕ x)

中文:
定义 inTangentCoordinates
  签名: (f : N -> M) (g : N -> M') (ϕ : N -> E ->L[𝕜] E')
  定义体: fun x₀ x => inCoordinates E (TangentSpace I) E' (TangentSpace I') (f x₀) (f x) (g x₀) (g x) (ϕ x)

Depends on / 依赖: TangentSpace, inCoordinates
-/
def inTangentCoordinates (f : N -> M) (g : N -> M') (ϕ : N -> E ->L[𝕜] E') : N -> N -> E ->L[𝕜] E' :=
  fun x₀ x => inCoordinates E (TangentSpace I) E' (TangentSpace I') (f x₀) (f x) (g x₀) (g x) (ϕ x)

/--
theorem `inTangentCoordinates_model_space` / 定理 `inTangentCoordinates_model_space`

English:
theorem inTangentCoordinates_model_space
  given: (f : N -> H) (g : N -> H') (ϕ : N -> E ->L[𝕜] E') (x₀ : N)
  proof: by
  simp +unfoldPartialApp only [inTangentCoordinates,
    inCoordinates_tangent_bundle_core_model_space]

中文:
定理 inTangentCoordinates_model_space
  条件: (f : N -> H) (g : N -> H') (ϕ : N -> E ->L[𝕜] E') (x₀ : N)
  证明: by
  simp +unfoldPartialApp only [inTangentCoordinates,
    inCoordinates_tangent_bundle_core_model_space]

Depends on / 依赖: inCoordinates_tangent_bundle_core_model_space, inTangentCoordinates, unfoldPartialApp
-/
theorem inTangentCoordinates_model_space (f : N -> H) (g : N -> H') (ϕ : N -> E ->L[𝕜] E') (x₀ : N) :
    inTangentCoordinates I I' f g ϕ x₀ = ϕ := by
  simp +unfoldPartialApp only [inTangentCoordinates,
    inCoordinates_tangent_bundle_core_model_space]

/--
theorem `inTangentCoordinates_eq` / 定理 `inTangentCoordinates_eq`

English:
theorem inTangentCoordinates_eq
  statement: (f : N -> M) (g : N -> M') (ϕ : N -> E ->L[𝕜] E') {x₀ x : N}
  proof: (tangentBundleCore I M).inCoordinates_eq (tangentBundleCore I' M') (ϕ x) hx hy

中文:
定理 inTangentCoordinates_eq
  结论: (f : N -> M) (g : N -> M') (ϕ : N -> E ->L[𝕜] E') {x₀ x : N}
  证明: (tangentBundleCore I M).inCoordinates_eq (tangentBundleCore I' M') (ϕ x) hx hy

Depends on / 依赖: inCoordinates_eq, tangentBundleCore
-/
theorem inTangentCoordinates_eq (f : N -> M) (g : N -> M') (ϕ : N -> E ->L[𝕜] E') {x₀ x : N}
    (hx : f x in (chartAt H (f x₀)).source) (hy : g x in (chartAt H' (g x₀)).source) :
    inTangentCoordinates I I' f g ϕ x₀ x =
      (tangentBundleCore I' M').coordChange (achart H' (g x)) (achart H' (g x₀)) (g x) ∘L
        ϕ x ∘L (tangentBundleCore I M).coordChange (achart H (f x₀)) (achart H (f x)) (f x) :=
  (tangentBundleCore I M).inCoordinates_eq (tangentBundleCore I' M') (ϕ x) hx hy

end inTangentCoordinates

end General
