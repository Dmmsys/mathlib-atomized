/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smoothness of charts and local structomorphisms

We show that the model with corners, charts, extended charts and their inverses are `C^n`,
and that local structomorphisms are `C^n` with `C^n` inverses.

## Implementation notes

This file uses the name `writtenInExtend` (in analogy to `writtenInExtChart`) to refer to a
composition `ψ.extend J ∘ f ∘ φ.extend I` of `f : M → N` with charts `ψ` and `φ` extended by the
appropriate models with corners. This is not a definition, so technically deviating from the naming
convention.

`isLocalStructomorphOn` is another made-up name.
-/

assert_not_exists mfderiv

public section

open Set ChartedSpace IsManifold
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a `C^n` manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : Nat∞ω}
  -- declare a topological space `M'`.
  {M' : Type*} [TopologicalSpace M']
  -- declare functions, sets, points and smoothness indices
  {e : OpenPartialHomeomorph M H} {x : M}

/-! ### Atlas members are `C^n` -/

section Atlas

set_option backward.isDefEq.respectTransparency false in
variable (I) in
/--
theorem `ModelWithCorners.contMDiff` / 定理 `ModelWithCorners.contMDiff`

English:
theorem ModelWithCorners.contMDiff
  statement: ContMDiff I 𝓘(𝕜, E) n I
  proof: by
  intro x
  refine contMDiffAt_iff.mpr ⟨I.continuousAt, ?_⟩
  simpa using contDiffWithinAt_id.congr (fun y hy => by simp [hy]) (by simp)
@[deprecated (since := "2026-06-16")] alias contMDiff_model := ModelWithCorners.contMDiff

中文:
定理 ModelWithCorners.contMDiff
  结论: ContMDiff I 𝓘(𝕜, E) n I
  证明: by
  intro x
  refine contMDiffAt_iff.mpr ⟨I.continuousAt, ?_⟩
  simpa using contDiffWithinAt_id.congr (fun y hy => by simp [hy]) (by simp)
@[deprecated (since := "2026-06-16")] alias contMDiff_model := ModelWithCorners.contMDiff

Depends on / 依赖: I.continuousAt, ModelWithCorners, ModelWithCorners.contMDiff, contDiffWithinAt_id, contDiffWithinAt_id.congr, contMDiff, contMDiffAt_iff, contMDiffAt_iff.mpr, contMDiff_model, continuousAt, deprecated
-/
theorem ModelWithCorners.contMDiff : ContMDiff I 𝓘(𝕜, E) n I := by
  intro x
  refine contMDiffAt_iff.mpr ⟨I.continuousAt, ?_⟩
  simpa using contDiffWithinAt_id.congr (fun y hy => by simp [hy]) (by simp)
@[deprecated (since := "2026-06-16")] alias contMDiff_model := ModelWithCorners.contMDiff

set_option backward.isDefEq.respectTransparency false in
variable (I) in
/--
theorem `ModelWithCorners.contMDiffOn_symm` / 定理 `ModelWithCorners.contMDiffOn_symm`

English:
theorem ModelWithCorners.contMDiffOn_symm
  statement: ContMDiffOn 𝓘(𝕜, E) I n I.symm (range I)
  proof: by
  intro x hx
  apply contMDiffWithinAt_iff.mpr ⟨by fun_prop, ?_⟩
  simpa using contDiffWithinAt_id.congr (fun y hy => by simp [hy]) (by simp [hx])
@[deprecated (since := "2026-06-16")]
alias contMDiffOn_model_symm := ModelWithCorners.contMDiffOn_symm

中文:
定理 ModelWithCorners.contMDiffOn_symm
  结论: ContMDiffOn 𝓘(𝕜, E) I n I.symm (range I)
  证明: by
  intro x hx
  apply contMDiffWithinAt_iff.mpr ⟨by fun_prop, ?_⟩
  simpa using contDiffWithinAt_id.congr (fun y hy => by simp [hy]) (by simp [hx])
@[deprecated (since := "2026-06-16")]
alias contMDiffOn_model_symm := ModelWithCorners.contMDiffOn_symm

Depends on / 依赖: ModelWithCorners, ModelWithCorners.contMDiffOn_symm, contDiffWithinAt_id, contDiffWithinAt_id.congr, contMDiffOn_model_symm, contMDiffOn_symm, contMDiffWithinAt_iff, contMDiffWithinAt_iff.mpr, deprecated, fun_prop
-/
theorem ModelWithCorners.contMDiffOn_symm : ContMDiffOn 𝓘(𝕜, E) I n I.symm (range I) := by
  intro x hx
  apply contMDiffWithinAt_iff.mpr ⟨by fun_prop, ?_⟩
  simpa using contDiffWithinAt_id.congr (fun y hy => by simp [hy]) (by simp [hx])
@[deprecated (since := "2026-06-16")]
alias contMDiffOn_model_symm := ModelWithCorners.contMDiffOn_symm

/--
theorem `contMDiffOn_of_mem_maximalAtlas` / 定理 `contMDiffOn_of_mem_maximalAtlas`

English:
theorem contMDiffOn_of_mem_maximalAtlas
  given: (h : e in maximalAtlas I n M)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropOn_of_mem_maximalAtlas
    contDiffWithinAtProp_id h

中文:
定理 contMDiffOn_of_mem_maximalAtlas
  条件: (h : e in maximalAtlas I n M)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropOn_of_mem_maximalAtlas
    contDiffWithinAtProp_id h

Depends on / 依赖: contDiffWithinAtProp_id, contDiffWithinAt_localInvariantProp, liftPropOn_of_mem_maximalAtlas
-/
theorem contMDiffOn_of_mem_maximalAtlas (h : e in maximalAtlas I n M) :
    ContMDiffOn I I n e e.source :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_of_mem_maximalAtlas
    contDiffWithinAtProp_id h

/--
theorem `contMDiffOn_symm_of_mem_maximalAtlas` / 定理 `contMDiffOn_symm_of_mem_maximalAtlas`

English:
theorem contMDiffOn_symm_of_mem_maximalAtlas
  given: (h : e in maximalAtlas I n M)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropOn_symm_of_mem_maximalAtlas
      contDiffWithinAtProp_id h

中文:
定理 contMDiffOn_symm_of_mem_maximalAtlas
  条件: (h : e in maximalAtlas I n M)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropOn_symm_of_mem_maximalAtlas
      contDiffWithinAtProp_id h

Depends on / 依赖: contDiffWithinAtProp_id, contDiffWithinAt_localInvariantProp, liftPropOn_symm_of_mem_maximalAtlas
-/
theorem contMDiffOn_symm_of_mem_maximalAtlas (h : e in maximalAtlas I n M) :
    ContMDiffOn I I n e.symm e.target :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_symm_of_mem_maximalAtlas
      contDiffWithinAtProp_id h

/--
theorem `contMDiffAt_of_mem_maximalAtlas` / 定理 `contMDiffAt_of_mem_maximalAtlas`

English:
theorem contMDiffAt_of_mem_maximalAtlas
  given: (h : e in maximalAtlas I n M) (hx : x in e.source)
  proof: (contMDiffOn_of_mem_maximalAtlas h).contMDiffAt e.open_source.mem_nhds hx

中文:
定理 contMDiffAt_of_mem_maximalAtlas
  条件: (h : e in maximalAtlas I n M) (hx : x in e.source)
  证明: (contMDiffOn_of_mem_maximalAtlas h).contMDiffAt e.open_source.mem_nhds hx

Depends on / 依赖: contMDiffAt, contMDiffOn_of_mem_maximalAtlas, e.open_source.mem_nhds, mem_nhds, open_source
-/
theorem contMDiffAt_of_mem_maximalAtlas (h : e in maximalAtlas I n M) (hx : x in e.source) :
    ContMDiffAt I I n e x :=
(contMDiffOn_of_mem_maximalAtlas h).contMDiffAt e.open_source.mem_nhds hx

/--
theorem `contMDiffAt_symm_of_mem_maximalAtlas` / 定理 `contMDiffAt_symm_of_mem_maximalAtlas`

English:
theorem contMDiffAt_symm_of_mem_maximalAtlas
  statement: {x : H} (h : e in maximalAtlas I n M)
  proof: (contMDiffOn_symm_of_mem_maximalAtlas h).contMDiffAt e.open_target.mem_nhds hx

中文:
定理 contMDiffAt_symm_of_mem_maximalAtlas
  结论: {x : H} (h : e in maximalAtlas I n M)
  证明: (contMDiffOn_symm_of_mem_maximalAtlas h).contMDiffAt e.open_target.mem_nhds hx

Depends on / 依赖: contMDiffAt, contMDiffOn_symm_of_mem_maximalAtlas, e.open_target.mem_nhds, mem_nhds, open_target
-/
theorem contMDiffAt_symm_of_mem_maximalAtlas {x : H} (h : e in maximalAtlas I n M)
    (hx : x in e.target) : ContMDiffAt I I n e.symm x :=
(contMDiffOn_symm_of_mem_maximalAtlas h).contMDiffAt e.open_target.mem_nhds hx

/--
theorem `contMDiffOn_chart` / 定理 `contMDiffOn_chart`

English:
theorem contMDiffOn_chart
  given: [IsManifold I n M]
  proof: contMDiffOn_of_mem_maximalAtlas chart_mem_maximalAtlas x

中文:
定理 contMDiffOn_chart
  条件: [IsManifold I n M]
  证明: contMDiffOn_of_mem_maximalAtlas chart_mem_maximalAtlas x

Depends on / 依赖: chart_mem_maximalAtlas, contMDiffOn_of_mem_maximalAtlas
-/
theorem contMDiffOn_chart [IsManifold I n M] :
    ContMDiffOn I I n (chartAt H x) (chartAt H x).source :=
contMDiffOn_of_mem_maximalAtlas chart_mem_maximalAtlas x

/--
theorem `contMDiffOn_chart_symm` / 定理 `contMDiffOn_chart_symm`

English:
theorem contMDiffOn_chart_symm
  given: [IsManifold I n M]
  proof: contMDiffOn_symm_of_mem_maximalAtlas chart_mem_maximalAtlas x

中文:
定理 contMDiffOn_chart_symm
  条件: [IsManifold I n M]
  证明: contMDiffOn_symm_of_mem_maximalAtlas chart_mem_maximalAtlas x

Depends on / 依赖: Algebra, Algebra.smul_def, Aux_apply_apply, Prod.smul_mk, chart_mem_maximalAtlas, contMDiffOn_symm_of_mem_maximalAtlas, mul_assoc, smul_def, smul_mk
-/
theorem contMDiffOn_chart_symm [IsManifold I n M] :
    ContMDiffOn I I n (chartAt H x).symm (chartAt H x).target :=
contMDiffOn_symm_of_mem_maximalAtlas chart_mem_maximalAtlas x

/--
theorem `OpenPartialHomeomorph.contMDiffAt_extend` / 定理 `OpenPartialHomeomorph.contMDiffAt_extend`

English:
theorem OpenPartialHomeomorph.contMDiffAt_extend
  statement: {x : M}
  proof: (I.contMDiff _).comp x contMDiffAt_of_mem_maximalAtlas he hx

中文:
定理 OpenPartialHomeomorph.contMDiffAt_extend
  结论: {x : M}
  证明: (I.contMDiff _).comp x contMDiffAt_of_mem_maximalAtlas he hx

Depends on / 依赖: Aux_foldr, I.contMDiff, LinearMap, LinearMap.snd, contMDiff, contMDiffAt_of_mem_maximalAtlas
-/
theorem OpenPartialHomeomorph.contMDiffAt_extend {x : M}
    (he : e in maximalAtlas I n M) (hx : x in e.source) :
    ContMDiffAt I 𝓘(𝕜, E) n (e.extend I) x :=
(I.contMDiff _).comp x contMDiffAt_of_mem_maximalAtlas he hx

/--
theorem `OpenPartialHomeomorph.contMDiffOn_extend` / 定理 `OpenPartialHomeomorph.contMDiffOn_extend`

English:
theorem OpenPartialHomeomorph.contMDiffOn_extend
  given: (he : e in maximalAtlas I n M)
  proof: fun _x' hx' => (e.contMDiffAt_extend he hx').contMDiffWithinAt

中文:
定理 OpenPartialHomeomorph.contMDiffOn_extend
  条件: (he : e in maximalAtlas I n M)
  证明: fun _x' hx' => (e.contMDiffAt_extend he hx').contMDiffWithinAt

Depends on / 依赖: Prod.snd, congr_arg, contMDiffAt_extend, contMDiffWithinAt, e.contMDiffAt_extend, foldr_algebraMap
-/
theorem OpenPartialHomeomorph.contMDiffOn_extend (he : e in maximalAtlas I n M) :
    ContMDiffOn I 𝓘(𝕜, E) n (e.extend I) e.source :=
  fun _x' hx' => (e.contMDiffAt_extend he hx').contMDiffWithinAt

/--
theorem `contMDiffAt_extChartAt'` / 定理 `contMDiffAt_extChartAt'`

English:
theorem contMDiffAt_extChartAt'
  given: [IsManifold I n M] {x' : M} (h : x' in (chartAt H x).source)
  proof: (chartAt H x).contMDiffAt_extend (chart_mem_maximalAtlas x) h

中文:
定理 contMDiffAt_extChartAt'
  条件: [IsManifold I n M] {x' : M} (h : x' in (chartAt H x).source)
  证明: (chartAt H x).contMDiffAt_extend (chart_mem_maximalAtlas x) h

Depends on / 依赖: Prod.snd, chartAt, chart_mem_maximalAtlas, congr_arg, contMDiffAt_extend
-/
theorem contMDiffAt_extChartAt' [IsManifold I n M] {x' : M} (h : x' in (chartAt H x).source) :
    ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x) x' :=
  (chartAt H x).contMDiffAt_extend (chart_mem_maximalAtlas x) h

/--
theorem `contMDiffAt_extChartAt` / 定理 `contMDiffAt_extChartAt`

English:
theorem contMDiffAt_extChartAt
  statement: ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x) x
  proof: by
  rw [contMDiffAt_iff_source]
  apply contMDiffWithinAt_id.congr_of_eventuallyEq_of_mem _ (by simp)
  filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
  exact PartialEquiv.right_inv (extChartAt I x) hy

中文:
定理 contMDiffAt_extChartAt
  结论: ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x) x
  证明: by
  rw [contMDiffAt_iff_source]
  apply contMDiffWithinAt_id.congr_of_eventuallyEq_of_mem _ (by simp)
  filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
  exact PartialEquiv.right_inv (extChartAt I x) hy

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Aux_apply_apply, CliffordAlgebra, CliffordAlgebra.left_induction, PartialEquiv, PartialEquiv.right_inv, Prod.fst_add, Prod.mk.eta.symm.trans, Prod.smul_mk, algebraMap, algebraMap_eq_smul_one, congr_arg, congr_of_eventuallyEq_of_mem, contMDiffAt_iff_source, contMDiffWithinAt_id, contMDiffWithinAt_id.congr_of_eventuallyEq_of_mem, extChartAt, extChartAt_target_mem_nhdsWithin, filter_upwards
-/
theorem contMDiffAt_extChartAt : ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x) x := by
  rw [contMDiffAt_iff_source]
  apply contMDiffWithinAt_id.congr_of_eventuallyEq_of_mem _ (by simp)
  filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
  exact PartialEquiv.right_inv (extChartAt I x) hy

/--
theorem `contMDiffOn_extChartAt` / 定理 `contMDiffOn_extChartAt`

English:
theorem contMDiffOn_extChartAt
  given: [IsManifold I n M]
  proof: (chartAt H x).contMDiffOn_extend (chart_mem_maximalAtlas x)

中文:
定理 contMDiffOn_extChartAt
  条件: [IsManifold I n M]
  证明: (chartAt H x).contMDiffOn_extend (chart_mem_maximalAtlas x)

Depends on / 依赖: chartAt, chart_mem_maximalAtlas, contMDiffOn_extend
-/
theorem contMDiffOn_extChartAt [IsManifold I n M] :
    ContMDiffOn I 𝓘(𝕜, E) n (extChartAt I x) (chartAt H x).source :=
  (chartAt H x).contMDiffOn_extend (chart_mem_maximalAtlas x)

/--
theorem `contMDiffOn_extend_symm` / 定理 `contMDiffOn_extend_symm`

English:
theorem contMDiffOn_extend_symm
  given: (he : e in maximalAtlas I n M)
  proof: by
  refine (contMDiffOn_symm_of_mem_maximalAtlas he).comp
    (I.contMDiffOn_symm.mono <| image_subset_range _ _) ?_
  simp_rw [image_subset_iff, PartialEquiv.restr_coe_symm, I.toPartialEquiv_coe_symm,
    preimage_preimage, I.left_inv, preimage_id']; rfl

中文:
定理 contMDiffOn_extend_symm
  条件: (he : e in maximalAtlas I n M)
  证明: by
  refine (contMDiffOn_symm_of_mem_maximalAtlas he).comp
    (I.contMDiffOn_symm.mono <| image_subset_range _ _) ?_
  simp_rw [image_subset_iff, PartialEquiv.restr_coe_symm, I.toPartialEquiv_coe_symm,
    preimage_preimage, I.left_inv, preimage_id']; rfl

Depends on / 依赖: I.contMDiffOn_symm.mono, I.left_inv, I.toPartialEquiv_coe_symm, PartialEquiv, PartialEquiv.restr_coe_symm, contMDiffOn_symm, contMDiffOn_symm_of_mem_maximalAtlas, image_subset_iff, image_subset_range, left_inv, preimage_id, preimage_preimage, restr_coe_symm, simp_rw, toPartialEquiv_coe_symm
-/
theorem contMDiffOn_extend_symm (he : e in maximalAtlas I n M) :
    ContMDiffOn 𝓘(𝕜, E) I n (e.extend I).symm (I '' e.target) := by
  refine (contMDiffOn_symm_of_mem_maximalAtlas he).comp
    (I.contMDiffOn_symm.mono <| image_subset_range _ _) ?_
  simp_rw [image_subset_iff, PartialEquiv.restr_coe_symm, I.toPartialEquiv_coe_symm,
    preimage_preimage, I.left_inv, preimage_id']; rfl

/--
theorem `contMDiffOn_extChartAt_symm` / 定理 `contMDiffOn_extChartAt_symm`

English:
theorem contMDiffOn_extChartAt_symm
  given: [IsManifold I n M] (x : M)
  proof: by
  convert! contMDiffOn_extend_symm (chart_mem_maximalAtlas (I := I) x)
  · rw [extChartAt_target, I.image_eq]
  · infer_instance

中文:
定理 contMDiffOn_extChartAt_symm
  条件: [IsManifold I n M] (x : M)
  证明: by
  convert! contMDiffOn_extend_symm (chart_mem_maximalAtlas (I := I) x)
  · rw [extChartAt_target, I.image_eq]
  · infer_instance

Depends on / 依赖: I.image_eq, chart_mem_maximalAtlas, contMDiffOn_extend_symm, convert, extChartAt_target, image_eq, infer_instance
-/
theorem contMDiffOn_extChartAt_symm [IsManifold I n M] (x : M) :
    ContMDiffOn 𝓘(𝕜, E) I n (extChartAt I x).symm (extChartAt I x).target := by
  convert! contMDiffOn_extend_symm (chart_mem_maximalAtlas (I := I) x)
  · rw [extChartAt_target, I.image_eq]
  · infer_instance

/--
theorem `contMDiffWithinAt_extChartAt_symm_target` / 定理 `contMDiffWithinAt_extChartAt_symm_target`

English:
theorem contMDiffWithinAt_extChartAt_symm_target
  statement: [IsManifold I n M]
  proof: contMDiffOn_extChartAt_symm x y hy

中文:
定理 contMDiffWithinAt_extChartAt_symm_target
  结论: [IsManifold I n M]
  证明: contMDiffOn_extChartAt_symm x y hy

Depends on / 依赖: contMDiffOn_extChartAt_symm
-/
theorem contMDiffWithinAt_extChartAt_symm_target [IsManifold I n M]
    (x : M) {y : E} (hy : y in (extChartAt I x).target) :
    ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x).symm (extChartAt I x).target y :=
  contMDiffOn_extChartAt_symm x y hy

/--
theorem `contMDiffWithinAt_extChartAt_symm_range` / 定理 `contMDiffWithinAt_extChartAt_symm_range`

English:
theorem contMDiffWithinAt_extChartAt_symm_range
  statement: [IsManifold I n M]
  proof: (contMDiffWithinAt_extChartAt_symm_target x hy).mono_of_mem_nhdsWithin
    (extChartAt_target_mem_nhdsWithin_of_mem hy)

中文:
定理 contMDiffWithinAt_extChartAt_symm_range
  结论: [IsManifold I n M]
  证明: (contMDiffWithinAt_extChartAt_symm_target x hy).mono_of_mem_nhdsWithin
    (extChartAt_target_mem_nhdsWithin_of_mem hy)

Depends on / 依赖: contMDiffWithinAt_extChartAt_symm_target, extChartAt_target_mem_nhdsWithin_of_mem, mono_of_mem_nhdsWithin
-/
theorem contMDiffWithinAt_extChartAt_symm_range [IsManifold I n M]
    (x : M) {y : E} (hy : y in (extChartAt I x).target) :
    ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x).symm (range I) y :=
  (contMDiffWithinAt_extChartAt_symm_target x hy).mono_of_mem_nhdsWithin
    (extChartAt_target_mem_nhdsWithin_of_mem hy)

/--
theorem `contMDiffWithinAt_extChartAt_symm_target_self` / 定理 `contMDiffWithinAt_extChartAt_symm_target_self`

English:
theorem contMDiffWithinAt_extChartAt_symm_target_self
  given: (x : M)
  proof: by
  rw [contMDiffWithinAt_iff_target]
  constructor
  · apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.comp _ I.continuousAt_symm
    exact (chartAt H x).symm.continuousAt (by simp)
  · apply contMDiffWithinAt_id.congr_of_mem (fun y hy => ?_) (by simp)
    convert! PartialEquiv.right_

中文:
定理 contMDiffWithinAt_extChartAt_symm_target_self
  条件: (x : M)
  证明: by
  rw [contMDiffWithinAt_iff_target]
  constructor
  · apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.comp _ I.continuousAt_symm
    exact (chartAt H x).symm.continuousAt (by simp)
  · apply contMDiffWithinAt_id.congr_of_mem (fun y hy => ?_) (by simp)
    convert! PartialEquiv.right_

Depends on / 依赖: ContinuousAt, ContinuousAt.comp, ContinuousAt.continuousWithinAt, I.continuousAt_symm, PartialEquiv, PartialEquiv.right_inv, chartAt, congr_of_mem, contMDiffWithinAt_id, contMDiffWithinAt_id.congr_of_mem, contMDiffWithinAt_iff_target, continuousAt, continuousAt_symm, continuousWithinAt, convert, extChartAt, right_inv, symm.continuousAt
-/
theorem contMDiffWithinAt_extChartAt_symm_target_self (x : M) :
    ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x).symm (extChartAt I x).target
      (extChartAt I x x) := by
  rw [contMDiffWithinAt_iff_target]
  constructor
  · apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.comp _ I.continuousAt_symm
    exact (chartAt H x).symm.continuousAt (by simp)
  · apply contMDiffWithinAt_id.congr_of_mem (fun y hy => ?_) (by simp)
    convert! PartialEquiv.right_inv (extChartAt I x) hy
    simp

/--
theorem `contMDiffWithinAt_extChartAt_symm_range_self` / 定理 `contMDiffWithinAt_extChartAt_symm_range_self`

English:
theorem contMDiffWithinAt_extChartAt_symm_range_self
  given: (x : M)
  proof: (contMDiffWithinAt_extChartAt_symm_target_self x).mono_of_mem_nhdsWithin
    (extChartAt_target_mem_nhdsWithin x)

中文:
定理 contMDiffWithinAt_extChartAt_symm_range_self
  条件: (x : M)
  证明: (contMDiffWithinAt_extChartAt_symm_target_self x).mono_of_mem_nhdsWithin
    (extChartAt_target_mem_nhdsWithin x)

Depends on / 依赖: contMDiffWithinAt_extChartAt_symm_target_self, extChartAt_target_mem_nhdsWithin, mono_of_mem_nhdsWithin
-/
theorem contMDiffWithinAt_extChartAt_symm_range_self (x : M) :
    ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x).symm (range I) (extChartAt I x x) :=
  (contMDiffWithinAt_extChartAt_symm_target_self x).mono_of_mem_nhdsWithin
    (extChartAt_target_mem_nhdsWithin x)

/--
theorem `contMDiffOn_of_mem_contDiffGroupoid` / 定理 `contMDiffOn_of_mem_contDiffGroupoid`

English:
theorem contMDiffOn_of_mem_contDiffGroupoid
  statement: {e' : OpenPartialHomeomorph H H}
  proof: (contDiffWithinAt_localInvariantProp n).liftPropOn_of_mem_groupoid contDiffWithinAtProp_id h

中文:
定理 contMDiffOn_of_mem_contDiffGroupoid
  结论: {e' : OpenPartialHomeomorph H H}
  证明: (contDiffWithinAt_localInvariantProp n).liftPropOn_of_mem_groupoid contDiffWithinAtProp_id h

Depends on / 依赖: contDiffWithinAtProp_id, contDiffWithinAt_localInvariantProp, liftPropOn_of_mem_groupoid
-/
theorem contMDiffOn_of_mem_contDiffGroupoid {e' : OpenPartialHomeomorph H H}
    (h : e' in contDiffGroupoid n I) : ContMDiffOn I I n e' e'.source :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_of_mem_groupoid contDiffWithinAtProp_id h

/--
lemma `OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn` / 引理 `OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn`

English:
lemma OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  statement: [IsManifold I n M]
  proof: by
  simp only [mfld_simps, IsManifold.mem_maximalAtlas_iff, StructureGroupoid.maximalAtlas,
    contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid,
    ← contMDiffOn_iff_contDiffOn]
  intro e he
  have he' := contMDiffOn_of_mem_maximalAtlas (I := I) (n := n)
    (StructureGroupoid.s

中文:
引理 OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  结论: [IsManifold I n M]
  证明: by
  simp only [mfld_simps, IsManifold.mem_maximalAtlas_iff, StructureGroupoid.maximalAtlas,
    contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid,
    ← contMDiffOn_iff_contDiffOn]
  intro e he
  have he' := contMDiffOn_of_mem_maximalAtlas (I := I) (n := n)
    (StructureGroupoid.s

Depends on / 依赖: I.contMDiff.comp_contMDiffOn, IsManifold, IsManifold.mem_maximalAtlas_iff, StructureGroupoid, StructureGroupoid.maximalAtlas, StructureGroupoid.subset_maximalAtlas, all_goals, comp_contMDiffOn, contDiffGroupoid, contDiffPregroupoid, contMDiff, contMDiffOn_iff_contDiffOn, contMDiffOn_of_mem_maximalAtlas, contMDiffOn_symm_of_mem_maximalAtlas, maximalAtlas, mem_groupoid_of_pregroupoid, mem_maximalAtlas_iff, mfld_simps, subset_maximalAtlas
-/
lemma OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn [IsManifold I n M]
    (φ : OpenPartialHomeomorph M H) (hφ : ContMDiffOn I I n φ φ.source)
    (hφ' : ContMDiffOn I I n φ.symm φ.target) :
    φ in maximalAtlas I n M := by
  simp only [mfld_simps, IsManifold.mem_maximalAtlas_iff, StructureGroupoid.maximalAtlas,
    contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid,
    ← contMDiffOn_iff_contDiffOn]
  intro e he
  have he' := contMDiffOn_of_mem_maximalAtlas (I := I) (n := n)
    (StructureGroupoid.subset_maximalAtlas _ he)
  have he'' := contMDiffOn_symm_of_mem_maximalAtlas (I := I) (n := n)
    (StructureGroupoid.subset_maximalAtlas _ he)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  all_goals apply I.contMDiff.comp_contMDiffOn
  · apply he'.comp (hφ'.comp (I.contMDiffOn_symm.mono (by simp)) (by grind)) (by grind)
  · apply hφ.comp (he''.comp (I.contMDiffOn_symm.mono (by simp)) (by grind)) (by grind)
  · exact hφ.comp (he''.comp (I.contMDiffOn_symm.mono (by simp)) (by grind)) (by grind)
  · exact he'.comp (hφ'.comp (I.contMDiffOn_symm.mono (by simp)) (by grind)) (by grind)

/--
lemma `IsManifold.mem_maximalAtlas_iff_contMDiffOn` / 引理 `IsManifold.mem_maximalAtlas_iff_contMDiffOn`

English:
lemma IsManifold.mem_maximalAtlas_iff_contMDiffOn
  statement: [IsManifold I n M]
  proof: ⟨fun h => ⟨contMDiffOn_of_mem_maximalAtlas h, contMDiffOn_symm_of_mem_maximalAtlas h⟩,
   fun ⟨hφ, hφ'⟩ => φ.mem_maximalAtlas_of_contMDiffOn hφ hφ'⟩

中文:
引理 IsManifold.mem_maximalAtlas_iff_contMDiffOn
  结论: [IsManifold I n M]
  证明: ⟨fun h => ⟨contMDiffOn_of_mem_maximalAtlas h, contMDiffOn_symm_of_mem_maximalAtlas h⟩,
   fun ⟨hφ, hφ'⟩ => φ.mem_maximalAtlas_of_contMDiffOn hφ hφ'⟩

Depends on / 依赖: contMDiffOn_of_mem_maximalAtlas, contMDiffOn_symm_of_mem_maximalAtlas, mem_maximalAtlas_of_contMDiffOn
-/
lemma IsManifold.mem_maximalAtlas_iff_contMDiffOn [IsManifold I n M]
    (φ : OpenPartialHomeomorph M H) :
    φ in maximalAtlas I n M ↔ ContMDiffOn I I n φ φ.source ∧ ContMDiffOn I I n φ.symm φ.target :=
  ⟨fun h => ⟨contMDiffOn_of_mem_maximalAtlas h, contMDiffOn_symm_of_mem_maximalAtlas h⟩,
   fun ⟨hφ, hφ'⟩ => φ.mem_maximalAtlas_of_contMDiffOn hφ hφ'⟩

end Atlas

/-! ### (local) structomorphisms are `C^n` -/

section IsLocalStructomorph

variable [IsManifold I n M] [ChartedSpace H M'] [IsM' : IsManifold I n M']

/--
theorem `isLocalStructomorphOn_contDiffGroupoid_iff_aux` / 定理 `isLocalStructomorphOn_contDiffGroupoid_iff_aux`

English:
theorem isLocalStructomorphOn_contDiffGroupoid_iff_aux
  statement: {f : OpenPartialHomeomorph M M'}
  proof: by
  -- It suffices to show regularity near each `x`
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  let c := chartAt H x
  let c' := chartAt H (f x)
  obtain ⟨-, hxf⟩ := hf x hx
  -- Since `f` is a local structomorph, it is locally equal to some transferred element `e` of
  -- the `contDi

中文:
定理 isLocalStructomorphOn_contDiffGroupoid_iff_aux
  结论: {f : OpenPartialHomeomorph M M'}
  证明: by
  -- It suffices to show regularity near each `x`
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  let c := chartAt H x
  let c' := chartAt H (f x)
  obtain ⟨-, hxf⟩ := hf x hx
  -- Since `f` is a local structomorph, it is locally equal to some transferred element `e` of
  -- the `contDi
-/
theorem isLocalStructomorphOn_contDiffGroupoid_iff_aux {f : OpenPartialHomeomorph M M'}
    (hf : LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt f f.source) :
    ContMDiffOn I I n f f.source := by
  -- It suffices to show regularity near each `x`
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  let c := chartAt H x
  let c' := chartAt H (f x)
  obtain ⟨-, hxf⟩ := hf x hx
  -- Since `f` is a local structomorph, it is locally equal to some transferred element `e` of
  -- the `contDiffGroupoid`.
  obtain
    ⟨e, he, he' : EqOn (c' ∘ f ∘ c.symm) e (c.symm ⁻¹' f.source inter e.source), hex :
      c x in e.source⟩ :=
    hxf (by simp only [hx, mfld_simps])
  -- We choose a convenient set `s` in `M`.
  let s : Set M := (f.trans c').source inter ((c.trans e).trans c'.symm).source
  refine ⟨s, (f.trans c').open_source.inter ((c.trans e).trans c'.symm).open_source, ?_, ?_⟩
  · simp only [s, mfld_simps]
    rw [← he'] <;> simp only [c, c', hx, hex, mfld_simps]
  -- We need to show `f` is `ContMDiffOn` the domain `s ∩ f.source`. We show this in two
  -- steps: `f` is equal to `c'.symm ∘ e ∘ c` on that domain and that function is
  -- `ContMDiffOn` it.
  have H₁ : ContMDiffOn I I n (c'.symm ∘ e ∘ c) s := by
    have hc' : ContMDiffOn I I n c'.symm _ := contMDiffOn_chart_symm
    have he'' : ContMDiffOn I I n e _ := contMDiffOn_of_mem_contDiffGroupoid he
    have hc : ContMDiffOn I I n c _ := contMDiffOn_chart
    refine (hc'.comp' (he''.comp' hc)).mono ?_
    dsimp [s, c, c']
    mfld_set_tac
  have H₂ : EqOn f (c'.symm ∘ e ∘ c) s := by
    intro y hy
    simp only [s, mfld_simps] at hy
    have hy₁ : f y in c'.source := by simp only [hy, mfld_simps]
    have hy₂ : y in c.source := by simp only [hy, mfld_simps]
    have hy₃ : c y in c.symm ⁻¹' f.source inter e.source := by simp only [hy, mfld_simps]
    calc
      f y = c'.symm (c' (f y)) := by rw [c'.left_inv hy₁]
      _ = c'.symm (c' (f (c.symm (c y)))) := by rw [c.left_inv hy₂]
      _ = c'.symm (e (c y)) := by rw [← he' hy₃]; rfl
  refine (H₁.congr H₂).mono ?_
  mfld_set_tac

/--
theorem `isLocalStructomorphOn_contDiffGroupoid_iff` / 定理 `isLocalStructomorphOn_contDiffGroupoid_iff`

English:
theorem isLocalStructomorphOn_contDiffGroupoid_iff
  given: (f : OpenPartialHomeomorph M M')
  proof: by
  constructor
  · intro h
    refine ⟨isLocalStructomorphOn_contDiffGroupoid_iff_aux h,
      isLocalStructomorphOn_contDiffGroupoid_iff_aux ?_⟩
    -- todo: we can generalize this part of the proof to a lemma
    intro X hX
    let x := f.symm X
    have hx : x in f.source := f.symm.mapsTo hX
  

中文:
定理 isLocalStructomorphOn_contDiffGroupoid_iff
  条件: (f : OpenPartialHomeomorph M M')
  证明: by
  constructor
  · intro h
    refine ⟨isLocalStructomorphOn_contDiffGroupoid_iff_aux h,
      isLocalStructomorphOn_contDiffGroupoid_iff_aux ?_⟩
    -- todo: we can generalize this part of the proof to a lemma
    intro X hX
    let x := f.symm X
    have hx : x in f.source := f.symm.mapsTo hX
  

Depends on / 依赖: isLocalStructomorphOn_contDiffGroupoid_iff_aux
-/
theorem isLocalStructomorphOn_contDiffGroupoid_iff (f : OpenPartialHomeomorph M M') :
    LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt f f.source ↔
      ContMDiffOn I I n f f.source ∧ ContMDiffOn I I n f.symm f.target := by
  constructor
  · intro h
    refine ⟨isLocalStructomorphOn_contDiffGroupoid_iff_aux h,
      isLocalStructomorphOn_contDiffGroupoid_iff_aux ?_⟩
    -- todo: we can generalize this part of the proof to a lemma
    intro X hX
    let x := f.symm X
    have hx : x in f.source := f.symm.mapsTo hX
    let c := chartAt H x
    let c' := chartAt H X
    obtain ⟨-, hxf⟩ := h x hx
    refine ⟨(f.symm.continuousAt hX).continuousWithinAt, fun h2x => ?_⟩
    obtain ⟨e, he, h2e, hef, hex⟩ :
      exists e : OpenPartialHomeomorph H H,
        e in contDiffGroupoid n I ∧
          e.source subseteq (c.symm ≫ₕ f ≫ₕ c').source ∧
            EqOn (c' ∘ f ∘ c.symm) e e.source ∧ c x in e.source := by
      have h1 : c' = chartAt H (f x) := by simp only [x, c', f.right_inv hX]
      have h2 : c' ∘ f ∘ c.symm = ⇑(c.symm ≫ₕ f ≫ₕ c') := rfl
      have hcx : c x in c.symm ⁻¹' f.source := by simp only [c, hx, mfld_simps]
      rw [h2]
      rw [← h1]; rw [h2]; rw [OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff'] at hxf
      · exact hxf hcx
      · dsimp [x, c]; mfld_set_tac
      · apply Or.inl
        simp only [c, hx, h1, mfld_simps]
    have h2X : c' X = e (c (f.symm X)) := by
      rw [← hef hex]
      dsimp only [Function.comp_def]
      have hfX : f.symm X in c.source := by simp only [c, x, mfld_simps]
      rw [c.left_inv hfX]; rw [f.right_inv hX]
    have h3e : EqOn (c ∘ f.symm ∘ c'.symm) e.symm (c'.symm ⁻¹' f.target inter e.target) := by
      have h1 : EqOn (c.symm ≫ₕ f ≫ₕ c').symm e.symm (e.target inter e.target) := by
        apply EqOn.symm
        refine e.isImage_source_target.symm_eqOn_of_inter_eq_of_eqOn ?_ ?_
        · rw [inter_self, inter_eq_right.mpr h2e]
        · rw [inter_self]; exact hef.symm
      have h2 : e.target subseteq (c.symm ≫ₕ f ≫ₕ c').target := by
        intro x hx; rw [← e.right_inv hx, ← hef (e.symm.mapsTo hx)]
        exact OpenPartialHomeomorph.mapsTo _ (h2e <| e.symm.mapsTo hx)
      rw [inter_self] at h1
      rwa [inter_eq_right.mpr]
      refine h2.trans ?_
      mfld_set_tac
    refine ⟨e.symm, StructureGroupoid.symm _ he, h3e, ?_⟩
    rw [h2X]; exact e.mapsTo hex
  · -- We now show the converse: an open partial homeomorphism `f : M → M'` which is `C^n` in both
    -- directions is a local structomorphism. We do this by proposing
    -- `((chart_at H x).symm.trans f).trans (chart_at H (f x))` as a candidate for a structomorphism
    -- of `H`.
    rintro ⟨h₁, h₂⟩ x hx
    refine ⟨(h₁ x hx).continuousWithinAt, ?_⟩
    let c := chartAt H x
    let c' := chartAt H (f x)
    rintro (hx' : c x in c.symm ⁻¹' f.source)
    -- propose `(c.symm.trans f).trans c'` as a candidate for a local structomorphism of `H`
    refine ⟨(c.symm.trans f).trans c', ⟨?_, ?_⟩, (?_ : EqOn (c' ∘ f ∘ c.symm) _ _), ?_⟩
    · -- regularity of the candidate local structomorphism in the forward direction
      intro y hy
      simp only [mfld_simps] at hy
      have H : ContMDiffWithinAt I I n f (f ≫ₕ c').source ((extChartAt I x).symm y) := by
        refine (h₁ ((extChartAt I x).symm y) ?_).mono ?_
        · simp only [c, hy, mfld_simps]
        · mfld_set_tac
      have hy' : (extChartAt I x).symm y in c.source := by simp only [c, hy, mfld_simps]
      have hy'' : f ((extChartAt I x).symm y) in c'.source := by
        simp only [c, hy, mfld_simps]
      rw [contMDiffWithinAt_iff_of_mem_source hy' hy''] at H
      convert! H.2.mono _
      · simp only [c, hy, mfld_simps]
      · dsimp [c, c']; mfld_set_tac
    · -- regularity of the candidate local structomorphism in the reverse direction
      intro y hy
      simp only [mfld_simps] at hy
      have H : ContMDiffWithinAt I I n f.symm (f.symm ≫ₕ c).source
          ((extChartAt I (f x)).symm y) := by
        refine (h₂ ((extChartAt I (f x)).symm y) ?_).mono ?_
        · simp only [c', hy, mfld_simps]
        · mfld_set_tac
      have hy' : (extChartAt I (f x)).symm y in c'.source := by simp only [c', hy, mfld_simps]
      have hy'' : f.symm ((extChartAt I (f x)).symm y) in c.source := by
        simp only [c', hy, mfld_simps]
      rw [contMDiffWithinAt_iff_of_mem_source hy' hy''] at H
      convert! H.2.mono _
      · simp only [c', hy, mfld_simps]
      · dsimp [c, c']; mfld_set_tac
    -- now check the candidate local structomorphism agrees with `f` where it is supposed to
    · simp only [mfld_simps]; apply eqOn_refl
    · simp only [c, c', hx', mfld_simps]

end IsLocalStructomorph

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : Nat∞ω} {f : M -> N} {s : Set M}
  {φ : OpenPartialHomeomorph M H} {ψ : OpenPartialHomeomorph N G}

/--
theorem `OpenPartialHomeomorph.contMDiffWithinAt_writtenInExtend_iff` / 定理 `OpenPartialHomeomorph.contMDiffWithinAt_writtenInExtend_iff`

English:
theorem OpenPartialHomeomorph.contMDiffWithinAt_writtenInExtend_iff
  statement: {y : M}
  proof: by
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas hφ hψ hy hgy]
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · rw [← φ.continuousWithinAt_writtenInExtend_iff (I := I) (I' := J) hy hgy hmaps]
    exact h.continuousWithinAt
  · rwa [← contMDiffWithinAt_iff_contDiffWithinAt]
  · rw [contMDiffWithinAt_i

中文:
定理 OpenPartialHomeomorph.contMDiffWithinAt_writtenInExtend_iff
  结论: {y : M}
  证明: by
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas hφ hψ hy hgy]
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · rw [← φ.continuousWithinAt_writtenInExtend_iff (I := I) (I' := J) hy hgy hmaps]
    exact h.continuousWithinAt
  · rwa [← contMDiffWithinAt_iff_contDiffWithinAt]
  · rw [contMDiffWithinAt_i

Depends on / 依赖: contMDiffWithinAt_iff_contDiffWithinAt, contMDiffWithinAt_iff_of_mem_maximalAtlas, continuousWithinAt, continuousWithinAt_writtenInExtend_iff, h.continuousWithinAt
-/
theorem OpenPartialHomeomorph.contMDiffWithinAt_writtenInExtend_iff {y : M}
    (hφ : φ in maximalAtlas I n M) (hψ : ψ in maximalAtlas J n N)
    (hy : y in φ.source) (hgy : f y in ψ.source) (hmaps : MapsTo f s ψ.source) :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, F) n (ψ.extend J ∘ f ∘ (φ.extend I).symm)
      ((φ.extend I).symm ⁻¹' s inter range I) (φ.extend I y) ↔ ContMDiffWithinAt I J n f s y := by
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas hφ hψ hy hgy]
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · rw [← φ.continuousWithinAt_writtenInExtend_iff (I := I) (I' := J) hy hgy hmaps]
    exact h.continuousWithinAt
  · rwa [← contMDiffWithinAt_iff_contDiffWithinAt]
  · rw [contMDiffWithinAt_iff_contDiffWithinAt]
    exact h.2

/--
theorem `OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff` / 定理 `OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff`

English:
theorem OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff
  proof: by
refine forall_mem_image.trans forall₂_congr fun x hx => ?_
  refine (contMDiffWithinAt_congr_set ?_).trans
    (contMDiffWithinAt_writtenInExtend_iff hφ hψ (hs hx) (hmaps hx) hmaps)
  rw [← nhdsWithin_eq_iff_eventuallyEq]; rw [← φ.map_extend_nhdsWithin_eq_image_of_subset]; rw [← φ.map_extend_nhds

中文:
定理 OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff
  证明: by
refine forall_mem_image.trans forall₂_congr fun x hx => ?_
  refine (contMDiffWithinAt_congr_set ?_).trans
    (contMDiffWithinAt_writtenInExtend_iff hφ hψ (hs hx) (hmaps hx) hmaps)
  rw [← nhdsWithin_eq_iff_eventuallyEq]; rw [← φ.map_extend_nhdsWithin_eq_image_of_subset]; rw [← φ.map_extend_nhds

Depends on / 依赖: contMDiffWithinAt_congr_set, contMDiffWithinAt_writtenInExtend_iff, exacts, forall_mem_image, forall_mem_image.trans, map_extend_nhdsWithin, map_extend_nhdsWithin_eq_image_of_subset, nhdsWithin_eq_iff_eventuallyEq
-/
theorem OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff
    (hφ : φ in maximalAtlas I n M) (hψ : ψ in maximalAtlas J n N)
    (hs : s subseteq φ.source) (hmaps : MapsTo f s ψ.source) :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, F) n (ψ.extend J ∘ f ∘ (φ.extend I).symm) (φ.extend I '' s) ↔
      ContMDiffOn I J n f s := by
refine forall_mem_image.trans forall₂_congr fun x hx => ?_
  refine (contMDiffWithinAt_congr_set ?_).trans
    (contMDiffWithinAt_writtenInExtend_iff hφ hψ (hs hx) (hmaps hx) hmaps)
  rw [← nhdsWithin_eq_iff_eventuallyEq]; rw [← φ.map_extend_nhdsWithin_eq_image_of_subset]; rw [← φ.map_extend_nhdsWithin]
  exacts [hs hx, hs hx, hs]
