/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.Notation

/-!
# Differentiability of models with corners and (extended) charts

In this file, we analyse the differentiability of charts, models with corners and extended charts.
We show that
* models with corners are differentiable
* charts are differentiable on their source
* `mdifferentiableOn_extChartAt`: `extChartAt` is differentiable on its source

Suppose an open partial homeomorphism `e` is differentiable. This file shows
* `OpenPartialHomeomorph.MDifferentiable.mfderiv`: its derivative is a continuous linear equivalence
* `OpenPartialHomeomorph.MDifferentiable.mfderiv_bijective`: its derivative is bijective;
  there are also spellings with trivial kernel and full range

In particular, (extended) charts have bijective differential.

## Tags
charts, differentiable, bijective
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff
open Bundle Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']

section ModelWithCorners
namespace ModelWithCorners

/- In general, the model with corner `I` is implicit in most theorems in differential geometry, but
this section is about `I` as a map, not as a parameter. Therefore, we make it explicit. -/
variable (I)


/--
theorem `hasMFDerivAt` / 定理 `hasMFDerivAt`

English:
theorem hasMFDerivAt
  given: {x}
  statement: HasMFDerivAt I 𝓘(𝕜, E) I x (ContinuousLinearMap.id _ _)
  proof: ⟨I.continuousAt, (hasFDerivWithinAt_id _ _).congr' I.rightInvOn (mem_range_self _)⟩

中文:
定理 hasMFDerivAt
  条件: {x}
  结论: HasMFDerivAt I 𝓘(𝕜, E) I x (连续线性映射.id _ _)
  证明: ⟨I.continuousAt, (hasFDerivWithinAt_id _ _).congr' I.rightInvOn (mem_range_self _)⟩
-/
protected theorem hasMFDerivAt {x} : HasMFDerivAt I 𝓘(𝕜, E) I x (ContinuousLinearMap.id _ _) :=
  ⟨I.continuousAt, (hasFDerivWithinAt_id _ _).congr' I.rightInvOn (mem_range_self _)⟩

/--
theorem `hasMFDerivWithinAt` / 定理 `hasMFDerivWithinAt`

English:
theorem hasMFDerivWithinAt
  given: {s x}
  proof: I.hasMFDerivAt.hasMFDerivWithinAt

中文:
定理 hasMFDerivWithinAt
  条件: {s x}
  证明: I.hasMFDerivAt.hasMFDerivWithinAt
-/
protected theorem hasMFDerivWithinAt {s x} :
    HasMFDerivWithinAt I 𝓘(𝕜, E) I s x (ContinuousLinearMap.id _ _) :=
  I.hasMFDerivAt.hasMFDerivWithinAt

/--
theorem `mdifferentiableWithinAt` / 定理 `mdifferentiableWithinAt`

English:
theorem mdifferentiableWithinAt
  given: {s x}
  statement: MDiffAt[s] I x
  proof: I.hasMFDerivWithinAt.mdifferentiableWithinAt

中文:
定理 mdifferentiableWithinAt
  条件: {s x}
  结论: MDiffAt[s] I x
  证明: I.hasMFDerivWithinAt.mdifferentiableWithinAt
-/
protected theorem mdifferentiableWithinAt {s x} : MDiffAt[s] I x :=
  I.hasMFDerivWithinAt.mdifferentiableWithinAt

/--
theorem `mdifferentiableAt` / 定理 `mdifferentiableAt`

English:
theorem mdifferentiableAt
  given: {x}
  statement: MDiffAt I x
  proof: I.hasMFDerivAt.mdifferentiableAt

中文:
定理 mdifferentiableAt
  条件: {x}
  结论: MDiffAt I x
  证明: I.hasMFDerivAt.mdifferentiableAt
-/
protected theorem mdifferentiableAt {x} : MDiffAt I x :=
  I.hasMFDerivAt.mdifferentiableAt

/--
theorem `mdifferentiableOn` / 定理 `mdifferentiableOn`

English:
theorem mdifferentiableOn
  given: {s}
  statement: MDiff[s] I
  proof: fun _ _ =>
  I.mdifferentiableWithinAt

中文:
定理 mdifferentiableOn
  条件: {s}
  结论: MDiff[s] I
  证明: fun _ _ =>
  I.mdifferentiableWithinAt
-/
protected theorem mdifferentiableOn {s} : MDiff[s] I := fun _ _ =>
  I.mdifferentiableWithinAt

/--
theorem `mdifferentiable` / 定理 `mdifferentiable`

English:
theorem mdifferentiable
  statement: MDiff I
  proof: fun _ => I.mdifferentiableAt

中文:
定理 mdifferentiable
  结论: MDiff I
  证明: fun _ => I.mdifferentiableAt
-/
protected theorem mdifferentiable : MDiff I := fun _ => I.mdifferentiableAt

/--
theorem `hasMFDerivWithinAt_symm` / 定理 `hasMFDerivWithinAt_symm`

English:
theorem hasMFDerivWithinAt_symm
  given: {x} (hx : x in range I)
  proof: ⟨I.continuousWithinAt_symm,
    (hasFDerivWithinAt_id _ _).congr' (fun _y hy => I.rightInvOn hy.1) ⟨hx, mem_range_self _⟩⟩

中文:
定理 hasMFDerivWithinAt_symm
  条件: {x} (hx : x in range I)
  证明: ⟨I.continuousWithinAt_symm,
    (hasFDerivWithinAt_id _ _).congr' (fun _y hy => I.rightInvOn hy.1) ⟨hx, mem_range_self _⟩⟩

Depends on / 依赖: I.continuousWithinAt_symm, I.rightInvOn, continuousWithinAt_symm, hasFDerivWithinAt_id, mem_range_self, rightInvOn
-/
theorem hasMFDerivWithinAt_symm {x} (hx : x in range I) :
    HasMFDerivWithinAt 𝓘(𝕜, E) I I.symm (range I) x (ContinuousLinearMap.id _ _) :=
  ⟨I.continuousWithinAt_symm,
    (hasFDerivWithinAt_id _ _).congr' (fun _y hy => I.rightInvOn hy.1) ⟨hx, mem_range_self _⟩⟩

/--
theorem `mdifferentiableOn_symm` / 定理 `mdifferentiableOn_symm`

English:
theorem mdifferentiableOn_symm
  statement: MDiff[range I] I.symm
  proof: fun _x hx =>
  (I.hasMFDerivWithinAt_symm hx).mdifferentiableWithinAt

中文:
定理 mdifferentiableOn_symm
  结论: MDiff[range I] I.symm
  证明: fun _x hx =>
  (I.hasMFDerivWithinAt_symm hx).mdifferentiableWithinAt
-/
theorem mdifferentiableOn_symm : MDiff[range I] I.symm := fun _x hx =>
  (I.hasMFDerivWithinAt_symm hx).mdifferentiableWithinAt

/--
theorem `mdifferentiableWithinAt_symm` / 定理 `mdifferentiableWithinAt_symm`

English:
theorem mdifferentiableWithinAt_symm
  given: {z : E} (hz : z in range I)
  proof: I.mdifferentiableOn_symm z hz

中文:
定理 mdifferentiableWithinAt_symm
  条件: {z : E} (hz : z in range I)
  证明: I.mdifferentiableOn_symm z hz

Depends on / 依赖: I.mdifferentiableOn_symm, mdifferentiableOn_symm
-/
theorem mdifferentiableWithinAt_symm {z : E} (hz : z in range I) :
    MDiffAt[range I] I.symm z :=
  I.mdifferentiableOn_symm z hz

end ModelWithCorners

end ModelWithCorners

section Charts

variable {e : OpenPartialHomeomorph M H}

/--
theorem `mdifferentiableAt_of_mem_maximalAtlas` / 定理 `mdifferentiableAt_of_mem_maximalAtlas`

English:
theorem mdifferentiableAt_of_mem_maximalAtlas
  proof: (contMDiffAt_of_mem_maximalAtlas h hx).mdifferentiableAt one_ne_zero

中文:
定理 mdifferentiableAt_of_mem_maximalAtlas
  证明: (contMDiffAt_of_mem_maximalAtlas h hx).mdifferentiableAt one_ne_zero

Depends on / 依赖: contMDiffAt_of_mem_maximalAtlas, mdifferentiableAt, one_ne_zero
-/
theorem mdifferentiableAt_of_mem_maximalAtlas
    (h : e in IsManifold.maximalAtlas I 1 M) {x : M} (hx : x in e.source) : MDiffAt e x :=
  (contMDiffAt_of_mem_maximalAtlas h hx).mdifferentiableAt one_ne_zero

/--
lemma `mdifferentiableAt_symm_of_mem_maximalAtlas` / 引理 `mdifferentiableAt_symm_of_mem_maximalAtlas`

English:
lemma mdifferentiableAt_symm_of_mem_maximalAtlas
  proof: .mdifferentiableAt one_ne_zero contMDiffAt_symm_of_mem_maximalAtlas h hx

中文:
引理 mdifferentiableAt_symm_of_mem_maximalAtlas
  证明: .mdifferentiableAt one_ne_zero contMDiffAt_symm_of_mem_maximalAtlas h hx

Depends on / 依赖: contMDiffAt_symm_of_mem_maximalAtlas, mdifferentiableAt, one_ne_zero
-/
lemma mdifferentiableAt_symm_of_mem_maximalAtlas
    (h : e in IsManifold.maximalAtlas I 1 M) {x : H} (hx : x in e.target) :
    MDiffAt e.symm x :=
.mdifferentiableAt one_ne_zero contMDiffAt_symm_of_mem_maximalAtlas h hx

variable [IsManifold I 1 M] [IsManifold I' 1 M'] [IsManifold I'' 1 M'']

/--
theorem `mdifferentiableAt_atlas` / 定理 `mdifferentiableAt_atlas`

English:
theorem mdifferentiableAt_atlas
  given: (h : e in atlas H M) {x : M} (hx : x in e.source)
  statement: MDiffAt e x
  proof: contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas h) hx
.mdifferentiableAt one_ne_zero

中文:
定理 mdifferentiableAt_atlas
  条件: (h : e in atlas H M) {x : M} (hx : x in e.source)
  结论: MDiffAt e x
  证明: contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas h) hx
.mdifferentiableAt one_ne_zero

Depends on / 依赖: IsManifold, IsManifold.subset_maximalAtlas, contMDiffAt_of_mem_maximalAtlas, mdifferentiableAt, one_ne_zero, subset_maximalAtlas
-/
theorem mdifferentiableAt_atlas (h : e in atlas H M) {x : M} (hx : x in e.source) : MDiffAt e x :=
  contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas h) hx
.mdifferentiableAt one_ne_zero

/--
theorem `mdifferentiableOn_atlas` / 定理 `mdifferentiableOn_atlas`

English:
theorem mdifferentiableOn_atlas
  given: (h : e in atlas H M)
  statement: MDiff[e.source] e
  proof: fun _x hx => (mdifferentiableAt_atlas h hx).mdifferentiableWithinAt

中文:
定理 mdifferentiableOn_atlas
  条件: (h : e in atlas H M)
  结论: MDiff[e.source] e
  证明: fun _x hx => (mdifferentiableAt_atlas h hx).mdifferentiableWithinAt

Depends on / 依赖: mdifferentiableAt_atlas, mdifferentiableWithinAt
-/
theorem mdifferentiableOn_atlas (h : e in atlas H M) : MDiff[e.source] e :=
  fun _x hx => (mdifferentiableAt_atlas h hx).mdifferentiableWithinAt

/--
theorem `mdifferentiableAt_atlas_symm` / 定理 `mdifferentiableAt_atlas_symm`

English:
theorem mdifferentiableAt_atlas_symm
  given: (h : e in atlas H M) {x : H} (hx : x in e.target)
  proof: mdifferentiableAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas h) hx

中文:
定理 mdifferentiableAt_atlas_symm
  条件: (h : e in atlas H M) {x : H} (hx : x in e.target)
  证明: mdifferentiableAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas h) hx

Depends on / 依赖: IsManifold, IsManifold.subset_maximalAtlas, mdifferentiableAt_symm_of_mem_maximalAtlas, subset_maximalAtlas
-/
theorem mdifferentiableAt_atlas_symm (h : e in atlas H M) {x : H} (hx : x in e.target) :
    MDiffAt e.symm x :=
  mdifferentiableAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas h) hx

/--
theorem `mdifferentiableOn_atlas_symm` / 定理 `mdifferentiableOn_atlas_symm`

English:
theorem mdifferentiableOn_atlas_symm
  given: (h : e in atlas H M)
  statement: MDiff[e.target] e.symm
  proof: fun _x hx => (mdifferentiableAt_atlas_symm h hx).mdifferentiableWithinAt

中文:
定理 mdifferentiableOn_atlas_symm
  条件: (h : e in atlas H M)
  结论: MDiff[e.target] e.symm
  证明: fun _x hx => (mdifferentiableAt_atlas_symm h hx).mdifferentiableWithinAt

Depends on / 依赖: mdifferentiableAt_atlas_symm, mdifferentiableWithinAt
-/
theorem mdifferentiableOn_atlas_symm (h : e in atlas H M) : MDiff[e.target] e.symm :=
  fun _x hx => (mdifferentiableAt_atlas_symm h hx).mdifferentiableWithinAt

/--
theorem `mdifferentiable_of_mem_atlas` / 定理 `mdifferentiable_of_mem_atlas`

English:
theorem mdifferentiable_of_mem_atlas
  given: (h : e in atlas H M)
  statement: e.MDifferentiable I I
  proof: ⟨mdifferentiableOn_atlas h, mdifferentiableOn_atlas_symm h⟩

中文:
定理 mdifferentiable_of_mem_atlas
  条件: (h : e in atlas H M)
  结论: e.MDifferentiable I I
  证明: ⟨mdifferentiableOn_atlas h, mdifferentiableOn_atlas_symm h⟩

Depends on / 依赖: mdifferentiableOn_atlas, mdifferentiableOn_atlas_symm
-/
theorem mdifferentiable_of_mem_atlas (h : e in atlas H M) : e.MDifferentiable I I :=
  ⟨mdifferentiableOn_atlas h, mdifferentiableOn_atlas_symm h⟩

/--
theorem `mdifferentiable_chart` / 定理 `mdifferentiable_chart`

English:
theorem mdifferentiable_chart
  given: (x : M)
  statement: (chartAt H x).MDifferentiable I I
  proof: mdifferentiable_of_mem_atlas (chart_mem_atlas _ _)

中文:
定理 mdifferentiable_chart
  条件: (x : M)
  结论: (chartAt H x).MDifferentiable I I
  证明: mdifferentiable_of_mem_atlas (chart_mem_atlas _ _)

Depends on / 依赖: chart_mem_atlas, mdifferentiable_of_mem_atlas
-/
theorem mdifferentiable_chart (x : M) : (chartAt H x).MDifferentiable I I :=
  mdifferentiable_of_mem_atlas (chart_mem_atlas _ _)

end Charts

/-! ### Differentiable open partial homeomorphisms -/

namespace OpenPartialHomeomorph.MDifferentiable
variable {e : OpenPartialHomeomorph M M'} (he : e.MDifferentiable I I')
  {e' : OpenPartialHomeomorph M' M''}
include he

nonrec theorem symm : e.symm.MDifferentiable I' I := he.symm

/--
theorem `mdifferentiableAt` / 定理 `mdifferentiableAt`

English:
theorem mdifferentiableAt
  given: {x : M} (hx : x in e.source)
  statement: MDiffAt e x
  proof: (he.1 x hx).mdifferentiableAt (e.open_source.mem_nhds hx)

中文:
定理 mdifferentiableAt
  条件: {x : M} (hx : x in e.source)
  结论: MDiffAt e x
  证明: (he.1 x hx).mdifferentiableAt (e.open_source.mem_nhds hx)
-/
protected theorem mdifferentiableAt {x : M} (hx : x in e.source) : MDiffAt e x :=
  (he.1 x hx).mdifferentiableAt (e.open_source.mem_nhds hx)

/--
theorem `mdifferentiableAt_symm` / 定理 `mdifferentiableAt_symm`

English:
theorem mdifferentiableAt_symm
  given: {x : M'} (hx : x in e.target)
  statement: MDiffAt e.symm x
  proof: (he.2 x hx).mdifferentiableAt (e.open_target.mem_nhds hx)

中文:
定理 mdifferentiableAt_symm
  条件: {x : M'} (hx : x in e.target)
  结论: MDiffAt e.symm x
  证明: (he.2 x hx).mdifferentiableAt (e.open_target.mem_nhds hx)

Depends on / 依赖: e.open_target.mem_nhds, mdifferentiableAt, mem_nhds, open_target
-/
theorem mdifferentiableAt_symm {x : M'} (hx : x in e.target) : MDiffAt e.symm x :=
  (he.2 x hx).mdifferentiableAt (e.open_target.mem_nhds hx)

/--
theorem `symm_comp_deriv` / 定理 `symm_comp_deriv`

English:
theorem symm_comp_deriv
  given: {x : M} (hx : x in e.source)
  proof: by
  have : mfderiv% (e.symm ∘ e) x = (mfderiv% e.symm (e x)).comp (mfderiv% e x) :=
    mfderiv_comp x (he.mdifferentiableAt_symm (e.map_source hx)) (he.mdifferentiableAt hx)
  rw [← this]
  have : mfderiv% (_root_.id : M -> M) x = ContinuousLinearMap.id _ _ := mfderiv_id
  rw [← this]
  apply Filt

中文:
定理 symm_comp_deriv
  条件: {x : M} (hx : x in e.source)
  证明: by
  have : mfderiv% (e.symm ∘ e) x = (mfderiv% e.symm (e x)).comp (mfderiv% e x) :=
    mfderiv_comp x (he.mdifferentiableAt_symm (e.map_source hx)) (he.mdifferentiableAt hx)
  rw [← this]
  have : mfderiv% (_root_.id : M -> M) x = ContinuousLinearMap.id _ _ := mfderiv_id
  rw [← this]
  apply Filt

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, EventuallyEq, Filter, Filter.EventuallyEq.mfderiv_eq, Filter.mem_of_superset, _root_, _root_.id, e.map_source, e.open_source.mem_nhds, e.source, e.symm, he.mdifferentiableAt, he.mdifferentiableAt_symm, map_source, mdifferentiableAt, mdifferentiableAt_symm, mem_nhds, mem_of_superset, mfderiv
-/
theorem symm_comp_deriv {x : M} (hx : x in e.source) :
    (mfderiv% e.symm (e x)).comp (mfderiv% e x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  have : mfderiv% (e.symm ∘ e) x = (mfderiv% e.symm (e x)).comp (mfderiv% e x) :=
    mfderiv_comp x (he.mdifferentiableAt_symm (e.map_source hx)) (he.mdifferentiableAt hx)
  rw [← this]
  have : mfderiv% (_root_.id : M -> M) x = ContinuousLinearMap.id _ _ := mfderiv_id
  rw [← this]
  apply Filter.EventuallyEq.mfderiv_eq
  have : e.source in 𝓝 x := e.open_source.mem_nhds hx
  exact Filter.mem_of_superset this (by mfld_set_tac)

/--
theorem `comp_symm_deriv` / 定理 `comp_symm_deriv`

English:
theorem comp_symm_deriv
  given: {x : M'} (hx : x in e.target)
  proof: he.symm.symm_comp_deriv hx

中文:
定理 comp_symm_deriv
  条件: {x : M'} (hx : x in e.target)
  证明: he.symm.symm_comp_deriv hx

Depends on / 依赖: he.symm.symm_comp_deriv, symm_comp_deriv
-/
theorem comp_symm_deriv {x : M'} (hx : x in e.target) :
    (mfderiv% e (e.symm x)).comp (mfderiv% e.symm x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I' x) :=
  he.symm.symm_comp_deriv hx

/--
Definition of `mfderiv` / `mfderiv` 的定义

English:
definition mfderiv
  signature: (he : e.MDifferentiable I I') {x : M} (hx : x in e.source)
  body: { mfderiv% e x with
    invFun := mfderiv% e.symm (e x)
    continuous_toFun := (mfderiv% e x).cont
    continuous_invFun := (mfderiv% e.symm (e x)).cont
    left_inv := fun y => by
      have : (ContinuousLinearMap.id _ _ : TangentSpace I x ->L[𝕜] TangentSpace I x) y = y := rfl
      conv_rhs => rw

中文:
定义 mfderiv
  签名: (he : e.MDifferentiable I I') {x : M} (hx : x in e.source)
  定义体: { mfderiv% e x with
    invFun := mfderiv% e.symm (e x)
    continuous_toFun := (mfderiv% e x).cont
    continuous_invFun := (mfderiv% e.symm (e x)).cont
    left_inv := fun y => by
      have : (ContinuousLinearMap.id _ _ : TangentSpace I x ->L[𝕜] TangentSpace I x) y = y := rfl
      conv_rhs => rw
-/
protected def mfderiv (he : e.MDifferentiable I I') {x : M} (hx : x in e.source) :
    TangentSpace I x ≃L[𝕜] TangentSpace I' (e x) :=
  { mfderiv% e x with
    invFun := mfderiv% e.symm (e x)
    continuous_toFun := (mfderiv% e x).cont
    continuous_invFun := (mfderiv% e.symm (e x)).cont
    left_inv := fun y => by
      have : (ContinuousLinearMap.id _ _ : TangentSpace I x ->L[𝕜] TangentSpace I x) y = y := rfl
      conv_rhs => rw [← this, ← he.symm_comp_deriv hx]
      rfl
    right_inv := fun y => by
      have :
        (ContinuousLinearMap.id 𝕜 _ : TangentSpace I' (e x) ->L[𝕜] TangentSpace I' (e x)) y = y :=
        rfl
      conv_rhs => rw [← this, ← he.comp_symm_deriv (e.map_source hx)]
      rw [e.left_inv hx]
      rfl }

/--
theorem `mfderiv_bijective` / 定理 `mfderiv_bijective`

English:
theorem mfderiv_bijective
  given: {x : M} (hx : x in e.source)
  statement: Function.Bijective (mfderiv% e x)
  proof: (he.mfderiv hx).bijective

中文:
定理 mfderiv_bijective
  条件: {x : M} (hx : x in e.source)
  结论: 函数.双射 (mfderiv% e x)
  证明: (he.mfderiv hx).bijective

Depends on / 依赖: bijective, he.mfderiv, mfderiv
-/
theorem mfderiv_bijective {x : M} (hx : x in e.source) : Function.Bijective (mfderiv% e x) :=
  (he.mfderiv hx).bijective

/--
theorem `mfderiv_injective` / 定理 `mfderiv_injective`

English:
theorem mfderiv_injective
  given: {x : M} (hx : x in e.source)
  statement: Function.Injective (mfderiv% e x)
  proof: (he.mfderiv hx).injective

中文:
定理 mfderiv_injective
  条件: {x : M} (hx : x in e.source)
  结论: 函数.单射 (mfderiv% e x)
  证明: (he.mfderiv hx).injective

Depends on / 依赖: he.mfderiv, injective, mfderiv
-/
theorem mfderiv_injective {x : M} (hx : x in e.source) : Function.Injective (mfderiv% e x) :=
  (he.mfderiv hx).injective

/--
theorem `mfderiv_surjective` / 定理 `mfderiv_surjective`

English:
theorem mfderiv_surjective
  given: {x : M} (hx : x in e.source)
  statement: Function.Surjective (mfderiv% e x)
  proof: (he.mfderiv hx).surjective

中文:
定理 mfderiv_surjective
  条件: {x : M} (hx : x in e.source)
  结论: 函数.满射 (mfderiv% e x)
  证明: (he.mfderiv hx).surjective

Depends on / 依赖: he.mfderiv, mfderiv, surjective
-/
theorem mfderiv_surjective {x : M} (hx : x in e.source) : Function.Surjective (mfderiv% e x) :=
  (he.mfderiv hx).surjective

/--
theorem `ker_mfderiv_eq_bot` / 定理 `ker_mfderiv_eq_bot`

English:
theorem ker_mfderiv_eq_bot
  given: {x : M} (hx : x in e.source)
  statement: (mfderiv% e x).ker = ⊥
  proof: (he.mfderiv hx).toLinearEquiv.ker

中文:
定理 ker_mfderiv_eq_bot
  条件: {x : M} (hx : x in e.source)
  结论: (mfderiv% e x).ker = ⊥
  证明: (he.mfderiv hx).toLinearEquiv.ker

Depends on / 依赖: he.mfderiv, mfderiv, toLinearEquiv, toLinearEquiv.ker
-/
theorem ker_mfderiv_eq_bot {x : M} (hx : x in e.source) : (mfderiv% e x).ker = ⊥ :=
  (he.mfderiv hx).toLinearEquiv.ker

/--
theorem `range_mfderiv_eq_top` / 定理 `range_mfderiv_eq_top`

English:
theorem range_mfderiv_eq_top
  given: {x : M} (hx : x in e.source)
  statement: (mfderiv% e x).range = ⊤
  proof: (he.mfderiv hx).toLinearEquiv.range

中文:
定理 range_mfderiv_eq_top
  条件: {x : M} (hx : x in e.source)
  结论: (mfderiv% e x).range = ⊤
  证明: (he.mfderiv hx).toLinearEquiv.range

Depends on / 依赖: he.mfderiv, mfderiv, toLinearEquiv, toLinearEquiv.range
-/
theorem range_mfderiv_eq_top {x : M} (hx : x in e.source) : (mfderiv% e x).range = ⊤ :=
  (he.mfderiv hx).toLinearEquiv.range

/--
theorem `range_mfderiv_eq_univ` / 定理 `range_mfderiv_eq_univ`

English:
theorem range_mfderiv_eq_univ
  given: {x : M} (hx : x in e.source)
  statement: range (mfderiv% e x) = univ
  proof: (he.mfderiv_surjective hx).range_eq

中文:
定理 range_mfderiv_eq_univ
  条件: {x : M} (hx : x in e.source)
  结论: range (mfderiv% e x) = univ
  证明: (he.mfderiv_surjective hx).range_eq

Depends on / 依赖: he.mfderiv_surjective, mfderiv_surjective, range_eq
-/
theorem range_mfderiv_eq_univ {x : M} (hx : x in e.source) : range (mfderiv% e x) = univ :=
  (he.mfderiv_surjective hx).range_eq

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: (he' : e'.MDifferentiable I' I'')
  statement: (e.trans e').MDifferentiable I I''
  proof: by
  constructor
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he'.mdifferentiableAt hx.2).comp _ (he.mdifferentiableAt hx.1)).mdifferentiableWithinAt
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he.symm.mdifferentiableAt hx.2).comp _
          (he'.symm.mdif

中文:
定理 trans
  条件: (he' : e'.MDifferentiable I' I'')
  结论: (e.trans e').MDifferentiable I I''
  证明: by
  constructor
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he'.mdifferentiableAt hx.2).comp _ (he.mdifferentiableAt hx.1)).mdifferentiableWithinAt
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he.symm.mdifferentiableAt hx.2).comp _
          (he'.symm.mdif

Depends on / 依赖: he.mdifferentiableAt, he.symm.mdifferentiableAt, mdifferentiableAt, mdifferentiableWithinAt, mfld_simps, symm.mdifferentiableAt
-/
theorem trans (he' : e'.MDifferentiable I' I'') : (e.trans e').MDifferentiable I I'' := by
  constructor
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he'.mdifferentiableAt hx.2).comp _ (he.mdifferentiableAt hx.1)).mdifferentiableWithinAt
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he.symm.mdifferentiableAt hx.2).comp _
          (he'.symm.mdifferentiableAt hx.1)).mdifferentiableWithinAt

end OpenPartialHomeomorph.MDifferentiable

/-! ### Differentiability of `extChartAt` -/

section extChartAt

variable [IsManifold I 1 M] {s : Set M} {x y : M} {z : E}

/--
theorem `hasMFDerivAt_extChartAt` / 定理 `hasMFDerivAt_extChartAt`

English:
theorem hasMFDerivAt_extChartAt
  given: (h : y in (chartAt H x).source)
  proof: I.hasMFDerivAt.comp y ((mdifferentiable_chart x).mdifferentiableAt h).hasMFDerivAt

中文:
定理 hasMFDerivAt_extChartAt
  条件: (h : y in (chartAt H x).source)
  证明: I.hasMFDerivAt.comp y ((mdifferentiable_chart x).mdifferentiableAt h).hasMFDerivAt

Depends on / 依赖: I.hasMFDerivAt.comp, hasMFDerivAt, mdifferentiableAt, mdifferentiable_chart
-/
theorem hasMFDerivAt_extChartAt (h : y in (chartAt H x).source) :
    HasMFDerivAt% (extChartAt I x) y (mfderiv% (chartAt H x) y :) :=
  I.hasMFDerivAt.comp y ((mdifferentiable_chart x).mdifferentiableAt h).hasMFDerivAt

/--
theorem `hasMFDerivWithinAt_extChartAt` / 定理 `hasMFDerivWithinAt_extChartAt`

English:
theorem hasMFDerivWithinAt_extChartAt
  given: (h : y in (chartAt H x).source)
  proof: (hasMFDerivAt_extChartAt h).hasMFDerivWithinAt

中文:
定理 hasMFDerivWithinAt_extChartAt
  条件: (h : y in (chartAt H x).source)
  证明: (hasMFDerivAt_extChartAt h).hasMFDerivWithinAt

Depends on / 依赖: hasMFDerivAt_extChartAt, hasMFDerivWithinAt
-/
theorem hasMFDerivWithinAt_extChartAt (h : y in (chartAt H x).source) :
    HasMFDerivAt[s] (extChartAt I x) y (mfderiv% (chartAt H x) y :) :=
  (hasMFDerivAt_extChartAt h).hasMFDerivWithinAt

/--
theorem `mdifferentiableAt_extChartAt` / 定理 `mdifferentiableAt_extChartAt`

English:
theorem mdifferentiableAt_extChartAt
  given: (h : y in (chartAt H x).source)
  proof: (hasMFDerivAt_extChartAt h).mdifferentiableAt

中文:
定理 mdifferentiableAt_extChartAt
  条件: (h : y in (chartAt H x).source)
  证明: (hasMFDerivAt_extChartAt h).mdifferentiableAt

Depends on / 依赖: hasMFDerivAt_extChartAt, mdifferentiableAt
-/
theorem mdifferentiableAt_extChartAt (h : y in (chartAt H x).source) :
    MDiffAt (extChartAt I x) y :=
  (hasMFDerivAt_extChartAt h).mdifferentiableAt

/--
theorem `mdifferentiableOn_extChartAt` / 定理 `mdifferentiableOn_extChartAt`

English:
theorem mdifferentiableOn_extChartAt
  statement: MDiff[(chartAt H x).source] (extChartAt I x)
  proof: fun _y hy => (hasMFDerivWithinAt_extChartAt hy).mdifferentiableWithinAt

中文:
定理 mdifferentiableOn_extChartAt
  结论: MDiff[(chartAt H x).source] (extChartAt I x)
  证明: fun _y hy => (hasMFDerivWithinAt_extChartAt hy).mdifferentiableWithinAt

Depends on / 依赖: hasMFDerivWithinAt_extChartAt, mdifferentiableWithinAt
-/
theorem mdifferentiableOn_extChartAt : MDiff[(chartAt H x).source] (extChartAt I x) :=
  fun _y hy => (hasMFDerivWithinAt_extChartAt hy).mdifferentiableWithinAt

/--
theorem `mdifferentiableWithinAt_extChartAt_symm` / 定理 `mdifferentiableWithinAt_extChartAt_symm`

English:
theorem mdifferentiableWithinAt_extChartAt_symm
  given: (h : z in (extChartAt I x).target)
  proof: by
  have Z := I.mdifferentiableWithinAt_symm (extChartAt_target_subset_range x h)
  apply MDifferentiableAt.comp_mdifferentiableWithinAt (I' := I) _ _ Z
  apply mdifferentiableAt_atlas_symm (ChartedSpace.chart_mem_atlas x)
  simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.trans_ta

中文:
定理 mdifferentiableWithinAt_extChartAt_symm
  条件: (h : z in (extChartAt I x).target)
  证明: by
  have Z := I.mdifferentiableWithinAt_symm (extChartAt_target_subset_range x h)
  apply MDifferentiableAt.comp_mdifferentiableWithinAt (I' := I) _ _ Z
  apply mdifferentiableAt_atlas_symm (ChartedSpace.chart_mem_atlas x)
  simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.trans_ta

Depends on / 依赖: ChartedSpace, ChartedSpace.chart_mem_atlas, I.mdifferentiableWithinAt_symm, MDifferentiableAt, MDifferentiableAt.comp_mdifferentiableWithinAt, ModelWithCorners, ModelWithCorners.target_eq, ModelWithCorners.toPartialEquiv_coe_symm, OpenPartialHomeomorph, OpenPartialHomeomorph.extend, PartialEquiv, PartialEquiv.trans_target, chart_mem_atlas, comp_mdifferentiableWithinAt, extChartAt, extChartAt_target_subset_range, extend, mdifferentiableAt_atlas_symm, mdifferentiableWithinAt_symm, mem_inter_iff
-/
theorem mdifferentiableWithinAt_extChartAt_symm (h : z in (extChartAt I x).target) :
    MDiffAt[range I] (extChartAt I x).symm z := by
  have Z := I.mdifferentiableWithinAt_symm (extChartAt_target_subset_range x h)
  apply MDifferentiableAt.comp_mdifferentiableWithinAt (I' := I) _ _ Z
  apply mdifferentiableAt_atlas_symm (ChartedSpace.chart_mem_atlas x)
  simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.trans_target,
    ModelWithCorners.target_eq, ModelWithCorners.toPartialEquiv_coe_symm, mem_inter_iff, mem_range,
    mem_preimage] at h
  exact h.2

/--
theorem `mdifferentiableOn_extChartAt_symm` / 定理 `mdifferentiableOn_extChartAt_symm`

English:
theorem mdifferentiableOn_extChartAt_symm
  proof: by
  intro y hy
  exact (mdifferentiableWithinAt_extChartAt_symm hy).mono (extChartAt_target_subset_range x)

中文:
定理 mdifferentiableOn_extChartAt_symm
  证明: by
  intro y hy
  exact (mdifferentiableWithinAt_extChartAt_symm hy).mono (extChartAt_target_subset_range x)

Depends on / 依赖: extChartAt_target_subset_range, mdifferentiableWithinAt_extChartAt_symm
-/
theorem mdifferentiableOn_extChartAt_symm :
    MDiff[(extChartAt I x).target] (extChartAt I x).symm := by
  intro y hy
  exact (mdifferentiableWithinAt_extChartAt_symm hy).mono (extChartAt_target_subset_range x)

/--
lemma `mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm` / 引理 `mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm`

English:
lemma mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
  statement: {x : M}
  proof: by
  have U : UniqueMDiffAt[range I] y := by
    apply I.uniqueMDiffOn
    exact extChartAt_target_subset_range x hy
  have h'y : (extChartAt I x).symm y in (extChartAt I x).source := (extChartAt I x).map_target hy
  have h''y : (extChartAt I x).symm y in (chartAt H x).source := by
    rwa [← extCha

中文:
引理 mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
  结论: {x : M}
  证明: by
  have U : UniqueMDiffAt[range I] y := by
    apply I.uniqueMDiffOn
    exact extChartAt_target_subset_range x hy
  have h'y : (extChartAt I x).symm y in (extChartAt I x).source := (extChartAt I x).map_target hy
  have h''y : (extChartAt I x).symm y in (chartAt H x).source := by
    rwa [← extCha

Depends on / 依赖: Eventua, Filter, Filter.Eventua, I.uniqueMDiffOn, UniqueMDiffAt, chartAt, extChartAt, extChartAt_source, extChartAt_target_subset_range, map_target, mdifferentiableAt_extChartAt, mdifferentiableWithinAt_extChartAt_symm, mfderivWithin_id, mfderiv_comp_mfderivWithin, rotate_left, source, uniqueMDiffOn
-/
lemma mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm {x : M}
    {y : E} (hy : y in (extChartAt I x).target) :
    (mfderiv% (extChartAt I x) ((extChartAt I x).symm y)) ∘L
      (mfderiv[range I] (extChartAt I x).symm y) = ContinuousLinearMap.id _ _ := by
  have U : UniqueMDiffAt[range I] y := by
    apply I.uniqueMDiffOn
    exact extChartAt_target_subset_range x hy
  have h'y : (extChartAt I x).symm y in (extChartAt I x).source := (extChartAt I x).map_target hy
  have h''y : (extChartAt I x).symm y in (chartAt H x).source := by
    rwa [← extChartAt_source (I := I)]
  rw [← mfderiv_comp_mfderivWithin]; rotate_left
  · apply mdifferentiableAt_extChartAt h''y
  · exact mdifferentiableWithinAt_extChartAt_symm hy
  · exact U
  rw [← mfderivWithin_id U]
  apply Filter.EventuallyEq.mfderivWithin_eq
  · filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hy] with z hz
    simp only [Function.comp_def, PartialEquiv.right_inv (extChartAt I x) hz, id_eq]
  · simp only [Function.comp_def, PartialEquiv.right_inv (extChartAt I x) hy, id_eq]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'` / 引理 `mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'`

English:
lemma mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
  statement: {x : M}
  proof: by
  have : y = (extChartAt I x).symm (extChartAt I x y) := ((extChartAt I x).left_inv hy).symm
  convert! mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm ((extChartAt I x).map_source hy)

中文:
引理 mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
  结论: {x : M}
  证明: by
  have : y = (extChartAt I x).symm (extChartAt I x y) := ((extChartAt I x).left_inv hy).symm
  convert! mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm ((extChartAt I x).map_source hy)

Depends on / 依赖: convert, extChartAt, left_inv, map_source, mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
-/
lemma mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' {x : M}
    {y : M} (hy : y in (extChartAt I x).source) :
    (mfderiv% (extChartAt I x) y) ∘L (mfderiv[range I] (extChartAt I x).symm (extChartAt I x y))
    = ContinuousLinearMap.id _ _ := by
  have : y = (extChartAt I x).symm (extChartAt I x y) := ((extChartAt I x).left_inv hy).symm
  convert! mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm ((extChartAt I x).map_source hy)

/--
lemma `mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt` / 引理 `mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt`

English:
lemma mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
  proof: by
  have h'y : (extChartAt I x).symm y in (extChartAt I x).source := (extChartAt I x).map_target hy
  have h''y : (extChartAt I x).symm y in (chartAt H x).source := by
    rwa [← extChartAt_source (I := I)]
  have U' : UniqueMDiffAt[(extChartAt I x).source] ((extChartAt I x).symm y) :=
    (isOpen_

中文:
引理 mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
  证明: by
  have h'y : (extChartAt I x).symm y in (extChartAt I x).source := (extChartAt I x).map_target hy
  have h''y : (extChartAt I x).symm y in (chartAt H x).source := by
    rwa [← extChartAt_source (I := I)]
  have U' : UniqueMDiffAt[(extChartAt I x).source] ((extChartAt I x).symm y) :=
    (isOpen_

Depends on / 依赖: UniqueMDiffAt, chartAt, extChartAt, extChartAt_source, isOpen_extChartAt_source, map_target, mfderiv, mfderivWithin_eq_mfder, source, uniqueMDiffWithinAt
-/
lemma mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
    {y : E} (hy : y in (extChartAt I x).target) :
    (mfderiv[range I] (extChartAt I x).symm y) ∘L
      (mfderiv% (extChartAt I x) ((extChartAt I x).symm y))
      = ContinuousLinearMap.id _ _ := by
  have h'y : (extChartAt I x).symm y in (extChartAt I x).source := (extChartAt I x).map_target hy
  have h''y : (extChartAt I x).symm y in (chartAt H x).source := by
    rwa [← extChartAt_source (I := I)]
  have U' : UniqueMDiffAt[(extChartAt I x).source] ((extChartAt I x).symm y) :=
    (isOpen_extChartAt_source x).uniqueMDiffWithinAt h'y
  have : mfderiv% (extChartAt I x) ((extChartAt I x).symm y)
      = mfderiv[(extChartAt I x).source] (extChartAt I x) ((extChartAt I x).symm y) := by
    rw [mfderivWithin_eq_mfderiv U']
    exact mdifferentiableAt_extChartAt h''y
  rw [this]; rw [← mfderivWithin_comp_of_eq]; rotate_left
  · exact mdifferentiableWithinAt_extChartAt_symm hy
  · exact (mdifferentiableAt_extChartAt h''y).mdifferentiableWithinAt
  · intro z hz
    apply extChartAt_target_subset_range x
    exact PartialEquiv.map_source (extChartAt I x) hz
  · exact U'
  · exact PartialEquiv.right_inv (extChartAt I x) hy
  rw [← mfderivWithin_id U']
  apply Filter.EventuallyEq.mfderivWithin_eq
  · filter_upwards [extChartAt_source_mem_nhdsWithin' h'y] with z hz
    simp only [Function.comp_def, PartialEquiv.left_inv (extChartAt I x) hz, id_eq]
  · simp only [Function.comp_def, PartialEquiv.right_inv (extChartAt I x) hy, id_eq]

/--
lemma `mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'` / 引理 `mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'`

English:
lemma mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
  proof: by
  have : y = (extChartAt I x).symm (extChartAt I x y) := ((extChartAt I x).left_inv hy).symm
  convert! mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt ((extChartAt I x).map_source hy)
  rw [(extChartAt I x).left_inv (by simpa using hy)]

中文:
引理 mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
  证明: by
  have : y = (extChartAt I x).symm (extChartAt I x y) := ((extChartAt I x).left_inv hy).symm
  convert! mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt ((extChartAt I x).map_source hy)
  rw [(extChartAt I x).left_inv (by simpa using hy)]

Depends on / 依赖: convert, extChartAt, left_inv, map_source, mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
-/
lemma mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    {y : M} (hy : y in (extChartAt I x).source) :
    (mfderiv[range I] (extChartAt I x).symm (extChartAt I x y)) ∘L (mfderiv% (extChartAt I x) y)
      = ContinuousLinearMap.id _ _ := by
  have : y = (extChartAt I x).symm (extChartAt I x y) := ((extChartAt I x).left_inv hy).symm
  convert! mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt ((extChartAt I x).map_source hy)
  rw [(extChartAt I x).left_inv (by simpa using hy)]

/--
lemma `isInvertible_mfderivWithin_extChartAt_symm` / 引理 `isInvertible_mfderivWithin_extChartAt_symm`

English:
lemma isInvertible_mfderivWithin_extChartAt_symm
  given: {y : E} (hy : y in (extChartAt I x).target)
  proof: ContinuousLinearMap.IsInvertible.of_inverse
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hy)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hy)

中文:
引理 isInvertible_mfderivWithin_extChartAt_symm
  条件: {y : E} (hy : y in (extChartAt I x).target)
  证明: ContinuousLinearMap.IsInvertible.of_inverse
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hy)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hy)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.IsInvertible.of_inverse, IsInvertible, mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt, mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm, of_inverse
-/
lemma isInvertible_mfderivWithin_extChartAt_symm {y : E} (hy : y in (extChartAt I x).target) :
    (mfderiv[range I] (extChartAt I x).symm y).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hy)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hy)

/--
lemma `isInvertible_mfderiv_extChartAt` / 引理 `isInvertible_mfderiv_extChartAt`

English:
lemma isInvertible_mfderiv_extChartAt
  given: {y : M} (hy : y in (extChartAt I x).source)
  proof: by
  have h'y : extChartAt I x y in (extChartAt I x).target := (extChartAt I x).map_source hy
  have Z := ContinuousLinearMap.IsInvertible.of_inverse
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm h'y)
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt h'y)
  have : (extChartAt I

中文:
引理 isInvertible_mfderiv_extChartAt
  条件: {y : M} (hy : y in (extChartAt I x).source)
  证明: by
  have h'y : extChartAt I x y in (extChartAt I x).target := (extChartAt I x).map_source hy
  have Z := ContinuousLinearMap.IsInvertible.of_inverse
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm h'y)
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt h'y)
  have : (extChartAt I

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.IsInvertible.of_inverse, IsInvertible, extChartAt, left_inv, map_source, mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt, mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm, of_inverse, target
-/
lemma isInvertible_mfderiv_extChartAt {y : M} (hy : y in (extChartAt I x).source) :
    (mfderiv% (extChartAt I x) y).IsInvertible := by
  have h'y : extChartAt I x y in (extChartAt I x).target := (extChartAt I x).map_source hy
  have Z := ContinuousLinearMap.IsInvertible.of_inverse
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm h'y)
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt h'y)
  have : (extChartAt I x).symm ((extChartAt I x) y) = y := (extChartAt I x).left_inv hy
  rwa [this] at Z

set_option backward.isDefEq.respectTransparency false in
/--
theorem `TangentBundle.continuousLinearMapAt_trivializationAt` / 定理 `TangentBundle.continuousLinearMapAt_trivializationAt`

English:
theorem TangentBundle.continuousLinearMapAt_trivializationAt
  proof: by
  have : MDiffAt (extChartAt I x₀) x := mdifferentiableAt_extChartAt hx
  simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe] at this
  simp [hx, mfderiv, this]

中文:
定理 切丛.continuousLinearMapAt_trivializationAt
  证明: by
  have : MDiffAt (extChartAt I x₀) x := mdifferentiableAt_extChartAt hx
  simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe] at this
  simp [hx, mfderiv, this]

Depends on / 依赖: MDiffAt, ModelWithCorners, ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph, OpenPartialHomeomorph.extend, OpenPartialHomeomorph.toFun_eq_coe, PartialEquiv, PartialEquiv.coe_trans, coe_trans, extChartAt, extend, mdifferentiableAt_extChartAt, mfderiv, toFun_eq_coe, toPartialEquiv_coe
-/
theorem TangentBundle.continuousLinearMapAt_trivializationAt
    {x₀ x : M} (hx : x in (chartAt H x₀).source) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x =
      mfderiv% (extChartAt I x₀) x := by
  have : MDiffAt (extChartAt I x₀) x := mdifferentiableAt_extChartAt hx
  simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe] at this
  simp [hx, mfderiv, this]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `TangentBundle.symmL_trivializationAt` / 定理 `TangentBundle.symmL_trivializationAt`

English:
theorem TangentBundle.symmL_trivializationAt
  proof: by
  have : MDiffAt[range I] ((chartAt H x₀).symm ∘ I.symm) (I (chartAt H x₀ x)) := by
    simpa using mdifferentiableWithinAt_extChartAt_symm (by simp [hx])
  simp [hx, mfderivWithin, this]

omit [IsManifold I 1 M] in

中文:
定理 切丛.symmL_trivializationAt
  证明: by
  have : MDiffAt[range I] ((chartAt H x₀).symm ∘ I.symm) (I (chartAt H x₀ x)) := by
    simpa using mdifferentiableWithinAt_extChartAt_symm (by simp [hx])
  simp [hx, mfderivWithin, this]

omit [IsManifold I 1 M] in

Depends on / 依赖: I.symm, MDiffAt, chartAt, mdifferentiableWithinAt_extChartAt_symm, mfderivWithin
-/
theorem TangentBundle.symmL_trivializationAt
    {x₀ x : M} (hx : x in (chartAt H x₀).source) :
    (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x =
      mfderiv[range I] (extChartAt I x₀).symm (extChartAt I x₀ x) := by
  have : MDiffAt[range I] ((chartAt H x₀).symm ∘ I.symm) (I (chartAt H x₀ x)) := by
    simpa using mdifferentiableWithinAt_extChartAt_symm (by simp [hx])
  simp [hx, mfderivWithin, this]

omit [IsManifold I 1 M] in
/--
lemma `fderivWithin_extChartAt_comp_extChartAt_symm_range` / 引理 `fderivWithin_extChartAt_comp_extChartAt_symm_range`

English:
lemma fderivWithin_extChartAt_comp_extChartAt_symm_range
  proof: by
  set φ := extChartAt I x
  have eq_nhd : ((extChartAt I x) ∘ (extChartAt I x).symm) =ᶠ[𝓝[range I] (extChartAt I x x)] id :=
    Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin x)
      (fun _ => (extChartAt I x).right_inv)
  rw [eq_nhd.fderivWithin_eq (by simp)]
exact fderivWithin_i

中文:
引理 fderivWithin_extChartAt_comp_extChartAt_symm_range
  证明: by
  set φ := extChartAt I x
  have eq_nhd : ((extChartAt I x) ∘ (extChartAt I x).symm) =ᶠ[𝓝[range I] (extChartAt I x x)] id :=
    Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin x)
      (fun _ => (extChartAt I x).right_inv)
  rw [eq_nhd.fderivWithin_eq (by simp)]
exact fderivWithin_i

Depends on / 依赖: Filter, Filter.eventuallyEq_of_mem, I.uniqueDiffOn.uniqueDiffWithinAt, eq_nhd, eq_nhd.fderivWithin_eq, eventuallyEq_of_mem, extChartAt, extChartAt_target_mem_nhdsWithin, fderivWithin_eq, fderivWithin_id, mem_range_self, right_inv, uniqueDiffOn, uniqueDiffWithinAt
-/
lemma fderivWithin_extChartAt_comp_extChartAt_symm_range :
    fderivWithin 𝕜 ((extChartAt I x) ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) =
      ContinuousLinearMap.id 𝕜 _ := by
  set φ := extChartAt I x
  have eq_nhd : ((extChartAt I x) ∘ (extChartAt I x).symm) =ᶠ[𝓝[range I] (extChartAt I x x)] id :=
    Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin x)
      (fun _ => (extChartAt I x).right_inv)
  rw [eq_nhd.fderivWithin_eq (by simp)]
exact fderivWithin_id I.uniqueDiffOn.uniqueDiffWithinAt (mem_range_self _)

/--
lemma `mfderiv_extChartAt_self` / 引理 `mfderiv_extChartAt_self`

English:
lemma mfderiv_extChartAt_self
  proof: by
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt (by simp)]; rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (by simp)]
  ext v
  simpa using! (tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x) v

中文:
引理 mfderiv_extChartAt_self
  证明: by
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt (by simp)]; rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (by simp)]
  ext v
  simpa using! (tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x) v

Depends on / 依赖: TangentBundle, TangentBundle.continuousLinearMapAt_trivializationAt, TangentBundle.continuousLinearMapAt_trivializationAt_eq_core, achart, continuousLinearMapAt_trivializationAt, continuousLinearMapAt_trivializationAt_eq_core, coordChange_self, mem_chart_source, tangentBundleCore
-/
lemma mfderiv_extChartAt_self :
    mfderiv% (extChartAt I x) x = ContinuousLinearMap.id 𝕜 _ := by
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt (by simp)]; rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (by simp)]
  ext v
  simpa using! (tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x) v

set_option backward.isDefEq.respectTransparency false in
-- TODO: should there be a version for `extChartAt`?
/--
lemma `mfderivWithin_range_extChartAt_symm` / 引理 `mfderivWithin_range_extChartAt_symm`

English:
lemma mfderivWithin_range_extChartAt_symm
  proof: by
  have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I)
    (mem_extChartAt_source x)
  rw [mfderiv_extChartAt_self]; rw [ContinuousLinearMap.comp_id] at hcomp
  simpa using! hcomp

中文:
引理 mfderivWithin_range_extChartAt_symm
  证明: by
  have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I)
    (mem_extChartAt_source x)
  rw [mfderiv_extChartAt_self]; rw [ContinuousLinearMap.comp_id] at hcomp
  simpa using! hcomp

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_id, comp_id, mem_extChartAt_source, mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt, mfderiv_extChartAt_self
-/
lemma mfderivWithin_range_extChartAt_symm :
    mfderiv[range I] (extChartAt I x).symm (extChartAt I x x) = ContinuousLinearMap.id 𝕜 _ := by
  have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I)
    (mem_extChartAt_source x)
  rw [mfderiv_extChartAt_self]; rw [ContinuousLinearMap.comp_id] at hcomp
  simpa using! hcomp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mfderivWithin_extChartAt_symm_inverse_apply` / 引理 `mfderivWithin_extChartAt_symm_inverse_apply`

English:
lemma mfderivWithin_extChartAt_symm_inverse_apply
  given: (v : TangentSpace I x)
  proof: by
  rw [mfderivWithin_range_extChartAt_symm]; rw [ContinuousLinearMap.inverse_id]
  exact ContinuousLinearMap.id_apply ..

中文:
引理 mfderivWithin_extChartAt_symm_inverse_apply
  条件: (v : TangentSpace I x)
  证明: by
  rw [mfderivWithin_range_extChartAt_symm]; rw [ContinuousLinearMap.inverse_id]
  exact ContinuousLinearMap.id_apply ..

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id_apply, ContinuousLinearMap.inverse_id, id_apply, inverse_id, mfderivWithin_range_extChartAt_symm
-/
lemma mfderivWithin_extChartAt_symm_inverse_apply (v : TangentSpace I x) :
    (mfderiv[range I] (extChartAt I x).symm (extChartAt I x x)).inverse v = v := by
  rw [mfderivWithin_range_extChartAt_symm]; rw [ContinuousLinearMap.inverse_id]
  exact ContinuousLinearMap.id_apply ..

end extChartAt
