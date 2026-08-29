/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-! # Riemannian manifolds

A Riemannian manifold `M` is a real manifold such that its tangent spaces are endowed with an
inner product, depending smoothly on the point, and such that `M` has an emetric space
structure for which the distance is the infimum of lengths of paths.

We register a Prop-valued typeclass `IsRiemannianManifold I M` recording this fact, building on top
of `[EMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]`.

We show that an inner product vector space, with the associated canonical Riemannian metric,
satisfies the predicate `IsRiemannianManifold 𝓘(ℝ, E) E`.

In a general manifold with a Riemannian metric, we define the associated extended distance in the
manifold, and show that it defines the same topology as the pre-existing one. Therefore, one
may endow the manifold with an emetric space structure, see `EMetricSpace.ofRiemannianMetric`.
By definition, it then satisfies the predicate `IsRiemannianManifold I M`.

The following code block is the standard way to say "Let `M` be a `C^∞` Riemannian manifold".
```
open scoped Bundle
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
```
To register a `C^n` manifold for a general `n`, one should replace `[IsManifold I ∞ M]` with
`[IsManifold I n M] [IsManifold I 1 M]`, where the second one is needed to ensure that the
tangent bundle is well behaved (not necessary when `n` is concrete like 2 or 3 as there are
automatic instances for these cases). One can require whatever regularity one wants in the
`IsContMDiffRiemannianBundle` instance above, for example
`[IsContMDiffRiemannianBundle I n E (fun (x : M) ↦ TangentSpace I x)]`, and one should also add
`[IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]` (as above, Lean cannot infer
the latter from the former as it cannot guess `n`).
-/

@[expose] public section

open Bundle Bornology Set MeasureTheory Manifold Filter
open scoped ENNReal ContDiff Topology

local notation "⟪" x ", " y "⟫" => inner Real x y

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H} {n : Nat∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section

variable [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) => TangentSpace% x)]

variable (I M) in
/--
Definition of `IsRiemannianManifold` / `IsRiemannianManifold` 的定义

English:
class IsRiemannianManifold
  parameters: : Prop where
  axioms and operations (1):
    - out((x y : M)) : edist x y = riemannianEDist I x y

中文:
类 是RiemannianManifold
  参数: : 命题 where
  公理与运算 (1 个):
    - out((x y : M)) : edist x y = riemannianEDist I x y
-/
class IsRiemannianManifold : Prop where
  out (x y : M) : edist x y = riemannianEDist I x y

end

section

/-!
### Riemannian structure on an inner product vector space

We endow an inner product vector space with the canonical Riemannian metric, given by the
inner product of the vector space in each of the tangent spaces, and we show that this construction
satisfies the `IsRiemannianManifold 𝓘(ℝ, E) E` predicate, i.e., the extended distance between
two points is the infimum of the length of paths between these points.
-/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/--
Definition of `riemannianMetricVectorSpace` / `riemannianMetricVectorSpace` 的定义

English:
definition riemannianMetricVectorSpace
  signature: :
  body: (innerSL Real (E := F) : F ->L[Real] F ->L[Real] Real)
  symm x v w := real_inner_comm _ _
  pos x v hv := real_inner_self_pos.2 hv
  isVonNBounded x := by
    change IsVonNBounded Real {v : F | ⟪v, v⟫ < 1}
    have : Metric.ball (0 : F) 1 = {v : F | ⟪v, v⟫ < 1} := by
      ext v
      simp only [Me

中文:
定义 riemannianMetricVectorSpace
  签名: :
  定义体: (innerSL Real (E := F) : F ->L[Real] F ->L[Real] Real)
  symm x v w := real_inner_comm _ _
  pos x v hv := real_inner_self_pos.2 hv
  isVonNBounded x := by
    change IsVonNBounded Real {v : F | ⟪v, v⟫ < 1}
    have : Metric.ball (0 : F) 1 = {v : F | ⟪v, v⟫ < 1} := by
      ext v
      simp only [Me

Depends on / 依赖: innerSL
-/
noncomputable def riemannianMetricVectorSpace :
    ContMDiffRiemannianMetric 𝓘(Real, F) ω F (fun (x : F) => TangentSpace% x) where
  inner x := (innerSL Real (E := F) : F ->L[Real] F ->L[Real] Real)
  symm x v w := real_inner_comm _ _
  pos x v hv := real_inner_self_pos.2 hv
  isVonNBounded x := by
    change IsVonNBounded Real {v : F | ⟪v, v⟫ < 1}
    have : Metric.ball (0 : F) 1 = {v : F | ⟪v, v⟫ < 1} := by
      ext v
      simp only [Metric.mem_ball, dist_zero_right, norm_eq_sqrt_re_inner (𝕜 := Real),
        RCLike.re_to_real, Set.mem_ofPred_eq]
      conv_lhs => rw [show (1 : Real) = √1 by simp]
      rw [Real.sqrt_lt_sqrt_iff]
      exact real_inner_self_nonneg
    rw [← this]
    exact NormedSpace.isVonNBounded_ball Real F 1
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert! contMDiffAt_const (c := innerSL Real)
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RiemannianBundle (fun (x : F) => TangentSpace% x)
  body: ⟨(riemannianMetricVectorSpace F).toRiemannianMetric⟩

中文:
实例 :
  签名: Riemann丛 (fun (x : F) => TangentSpace% x)
  定义体: ⟨(riemannianMetricVectorSpace F).toRiemannianMetric⟩

Depends on / 依赖: riemannianMetricVectorSpace, toRiemannianMetric
-/
noncomputable instance : RiemannianBundle (fun (x : F) => TangentSpace% x) :=
  ⟨(riemannianMetricVectorSpace F).toRiemannianMetric⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `norm_tangentSpace_vectorSpace` / 引理 `norm_tangentSpace_vectorSpace`

English:
lemma norm_tangentSpace_vectorSpace
  given: {x : F} {v : TangentSpace% x}
  proof: v; V‖ := by
  rw [norm_eq_sqrt_real_inner]; rw [norm_eq_sqrt_real_inner]

中文:
引理 norm_tangentSpace_vectorSpace
  条件: {x : F} {v : TangentSpace% x}
  证明: v; V‖ := by
  rw [norm_eq_sqrt_real_inner]; rw [norm_eq_sqrt_real_inner]

Depends on / 依赖: norm_eq_sqrt_real_inner
-/
lemma norm_tangentSpace_vectorSpace {x : F} {v : TangentSpace% x} :
    ‖v‖ = ‖letI V : F := v; V‖ := by
  rw [norm_eq_sqrt_real_inner]; rw [norm_eq_sqrt_real_inner]

/--
lemma `nnnorm_tangentSpace_vectorSpace` / 引理 `nnnorm_tangentSpace_vectorSpace`

English:
lemma nnnorm_tangentSpace_vectorSpace
  given: {x : F} {v : TangentSpace% x}
  proof: v; V‖₊ := by
  simp [nnnorm, norm_tangentSpace_vectorSpace]

中文:
引理 nnnorm_tangentSpace_vectorSpace
  条件: {x : F} {v : TangentSpace% x}
  证明: v; V‖₊ := by
  simp [nnnorm, norm_tangentSpace_vectorSpace]

Depends on / 依赖: nnnorm, norm_tangentSpace_vectorSpace
-/
lemma nnnorm_tangentSpace_vectorSpace {x : F} {v : TangentSpace% x} :
    ‖v‖₊ = ‖letI V : F := v; V‖₊ := by
  simp [nnnorm, norm_tangentSpace_vectorSpace]

/--
lemma `enorm_tangentSpace_vectorSpace` / 引理 `enorm_tangentSpace_vectorSpace`

English:
lemma enorm_tangentSpace_vectorSpace
  given: {x : F} {v : TangentSpace% x}
  proof: v; V‖ₑ := by
  simp [enorm, nnnorm_tangentSpace_vectorSpace]

中文:
引理 enorm_tangentSpace_vectorSpace
  条件: {x : F} {v : TangentSpace% x}
  证明: v; V‖ₑ := by
  simp [enorm, nnnorm_tangentSpace_vectorSpace]

Depends on / 依赖: nnnorm_tangentSpace_vectorSpace
-/
lemma enorm_tangentSpace_vectorSpace {x : F} {v : TangentSpace% x} :
    ‖v‖ₑ = ‖letI V : F := v; V‖ₑ := by
  simp [enorm, nnnorm_tangentSpace_vectorSpace]

open MeasureTheory Measure

/--
lemma `lintegral_fderiv_lineMap_eq_edist` / 引理 `lintegral_fderiv_lineMap_eq_edist`

English:
lemma lintegral_fderiv_lineMap_eq_edist
  given: {x y : E}
  proof: by
  have : edist x y = ∫⁻ t in Icc (0 : Real) 1, ‖y - x‖ₑ := by
    simp [edist_comm x y, edist_eq_enorm_sub]
  rw [this]
  apply setLIntegral_congr_fun measurableSet_Icc (fun z hz => ?_)
  rw [show y - x = fderiv Real (ContinuousAffineMap.lineMap (R := Real) x y) z 1 by simp]
  congr
  exact fderi

中文:
引理 lintegral_fderiv_lineMap_eq_edist
  条件: {x y : E}
  证明: by
  have : edist x y = ∫⁻ t in Icc (0 : Real) 1, ‖y - x‖ₑ := by
    simp [edist_comm x y, edist_eq_enorm_sub]
  rw [this]
  apply setLIntegral_congr_fun measurableSet_Icc (fun z hz => ?_)
  rw [show y - x = fderiv Real (ContinuousAffineMap.lineMap (R := Real) x y) z 1 by simp]
  congr
  exact fderi
-/
lemma lintegral_fderiv_lineMap_eq_edist {x y : E} :
    ∫⁻ t in Icc 0 1, ‖fderivWithin Real (ContinuousAffineMap.lineMap (R := Real) x y) (Icc 0 1) t 1‖ₑ
      = edist x y := by
  have : edist x y = ∫⁻ t in Icc (0 : Real) 1, ‖y - x‖ₑ := by
    simp [edist_comm x y, edist_eq_enorm_sub]
  rw [this]
  apply setLIntegral_congr_fun measurableSet_Icc (fun z hz => ?_)
  rw [show y - x = fderiv Real (ContinuousAffineMap.lineMap (R := Real) x y) z 1 by simp]
  congr
  exact fderivWithin_eq_fderiv (uniqueDiffOn_Icc zero_lt_one _ hz)
    (ContinuousAffineMap.differentiableAt _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsRiemannianManifold 𝓘(Real, F) F
  body: by
  refine ⟨fun x y => le_antisymm ?_ ?_⟩
  · simp only [riemannianEDist, le_iInf_iff]
    intro γ hγ
    let e : Real -> F := γ ∘ (projIcc 0 1 zero_le_one)
    have D : ContDiffOn Real 1 e (Icc 0 1) :=
      contMDiffOn_iff_contDiffOn.mp (hγ.comp_contMDiffOn contMDiffOn_projIcc)
    rw [lintegral_

中文:
实例 :
  签名: 是RiemannianManifold 𝓘(实数, F) F
  定义体: by
  refine ⟨fun x y => le_antisymm ?_ ?_⟩
  · simp only [riemannianEDist, le_iInf_iff]
    intro γ hγ
    let e : Real -> F := γ ∘ (projIcc 0 1 zero_le_one)
    have D : ContDiffOn Real 1 e (Icc 0 1) :=
      contMDiffOn_iff_contDiffOn.mp (hγ.comp_contMDiffOn contMDiffOn_projIcc)
    rw [lintegral_

Depends on / 依赖: ContDiffOn, comp_contMDiffOn, contMDiffOn_iff_contDiffOn, contMDiffOn_iff_contDiffOn.mp, contMDiffOn_projIcc, conv_lhs, edist_comm, edist_eq_enorm_sub, enorm_tangentSpace_vectorSpace, le_antisymm, le_iInf_iff, lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc, mfderivWithin_eq_fderivWithin, pathELength_eq_lintegral_mfderivWithin_Icc, projIcc, riemannianEDist, zero_le_one
-/
instance : IsRiemannianManifold 𝓘(Real, F) F := by
  refine ⟨fun x y => le_antisymm ?_ ?_⟩
  · simp only [riemannianEDist, le_iInf_iff]
    intro γ hγ
    let e : Real -> F := γ ∘ (projIcc 0 1 zero_le_one)
    have D : ContDiffOn Real 1 e (Icc 0 1) :=
      contMDiffOn_iff_contDiffOn.mp (hγ.comp_contMDiffOn contMDiffOn_projIcc)
    rw [lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]; rw [pathELength_eq_lintegral_mfderivWithin_Icc]
    simp only [mfderivWithin_eq_fderivWithin, enorm_tangentSpace_vectorSpace]
    conv_lhs =>
      rw [edist_comm]; rw [edist_eq_enorm_sub]; rw [show x = e 0 by simp [e], show y = e 1 by simp [e]]
    exact (enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc D zero_le_one).trans_eq rfl
  · let γ := ContinuousAffineMap.lineMap (R := Real) x y
    have : riemannianEDist 𝓘(Real, F) x y <= pathELength 𝓘(Real, F) γ 0 1 := by
      apply riemannianEDist_le_pathELength ?_ (by simp [γ, ContinuousAffineMap.coe_lineMap_eq])
        (by simp [γ, ContinuousAffineMap.coe_lineMap_eq]) zero_le_one
      rw [contMDiffOn_iff_contDiffOn]
      exact γ.contDiff.contDiffOn
    apply this.trans_eq
    rw [pathELength_eq_lintegral_mfderivWithin_Icc]
    simp only [mfderivWithin_eq_fderivWithin, enorm_tangentSpace_vectorSpace]
    exact lintegral_fderiv_lineMap_eq_edist

end

section

/-!
### Constructing a distance from a Riemannian structure

Let `M` be a real manifold with a Riemannian structure. We construct the associated distance and
show that the associated topology coincides with the pre-existing topology. Therefore, one may
endow `M` with an emetric space structure, called `EMetricSpace.ofRiemannianMetric`.
Moreover, we show that in this case the resulting emetric space satisfies the predicate
`IsRiemannianManifold I M`.

Showing that the distance topology coincides with the pre-existing topology is not trivial. The
two inclusions are proved respectively in `eventually_riemannianEDist_lt` and
`setOfPred_riemannianEDist_lt_subset_nhds`.

For the first one, we have to show that points which are close for the topology are at small
distance. For this, we use the path between the two points which is the pullback of the segment
in the extended chart, and argue that it is short because the images are close in the extended
chart.

For the second one, we have to show that any neighborhood of `x` contains all the points `y`
with `riemannianEDist x y < c` for some `c > 0`. For this, we argue that a short path from `x`
to `y` remains short in the extended chart, and therefore it doesn't have the time to exit
the image of the neighborhood in the extended chart.
-/

open Manifold Metric
open scoped NNReal

variable [RiemannianBundle (fun (x : M) => TangentSpace% x)]
  [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun (x : M) => TangentSpace% x)]

/-- Register on the tangent space to a normed vector space the same `NormedAddCommGroup` structure
as in the vector space.

Should not be a global instance, as it does not coincide definitionally with the Riemannian
structure for inner product spaces, but can be activated locally. -/
@[instance_reducible]
/--
Definition of `normedAddCommGroupTangentSpaceVectorSpace` / `normedAddCommGroupTangentSpaceVectorSpace` 的定义

English:
definition normedAddCommGroupTangentSpaceVectorSpace
  signature: (x : E)
  body: inferInstanceAs (NormedAddCommGroup E)

中文:
定义 normedAddCommGroupTangentSpaceVectorSpace
  签名: (x : E)
  定义体: inferInstanceAs (NormedAddCommGroup E)

Depends on / 依赖: NormedAddCommGroup
-/
def normedAddCommGroupTangentSpaceVectorSpace (x : E) :
    NormedAddCommGroup (TangentSpace% x) :=
  inferInstanceAs (NormedAddCommGroup E)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace

/-- Register on the tangent space to a normed vector space the same `NormedSpace` structure
as in the vector space.

Should not be a global instance, as it does not coincide definitionally with the Riemannian
structure for inner product spaces, but can be activated locally. -/
@[instance_reducible]
/--
Definition of `normedSpaceTangentSpaceVectorSpace` / `normedSpaceTangentSpaceVectorSpace` 的定义

English:
definition normedSpaceTangentSpaceVectorSpace
  signature: (x : E)
  body: inferInstanceAs (NormedSpace Real E)

中文:
定义 normedSpaceTangentSpaceVectorSpace
  签名: (x : E)
  定义体: inferInstanceAs (NormedSpace Real E)

Depends on / 依赖: NormedSpace
-/
def normedSpaceTangentSpaceVectorSpace (x : E) : NormedSpace Real (TangentSpace% x) :=
  inferInstanceAs (NormedSpace Real E)

attribute [local instance] normedSpaceTangentSpaceVectorSpace

variable (I)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `eventually_norm_mfderiv_extChartAt_lt` / 引理 `eventually_norm_mfderiv_extChartAt_lt`

English:
lemma eventually_norm_mfderiv_extChartAt_lt
  given: (x : M)
  proof: by
  rcases eventually_norm_trivializationAt_lt E (fun (x : M) => TangentSpace% x) x
    with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  have hx : (chartAt H x).source in 𝓝 x := chart_source_mem_nhds H x
  filter_upwards [hC, hx] with y hy h'y
  rwa [← TangentBundle.continuousLinearMapAt_trivializatio

中文:
引理 eventually_norm_mfderiv_extChartAt_lt
  条件: (x : M)
  证明: by
  rcases eventually_norm_trivializationAt_lt E (fun (x : M) => TangentSpace% x) x
    with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  have hx : (chartAt H x).source in 𝓝 x := chart_source_mem_nhds H x
  filter_upwards [hC, hx] with y hy h'y
  rwa [← TangentBundle.continuousLinearMapAt_trivializatio

Depends on / 依赖: C_pos, TangentBundle, TangentBundle.continuousLinearMapAt_trivializationAt, TangentSpace, chartAt, chart_source_mem_nhds, continuousLinearMapAt_trivializationAt, eventually_norm_trivializationAt_lt, filter_upwards, source
-/
lemma eventually_norm_mfderiv_extChartAt_lt (x : M) :
    exists C > 0, forallᶠ y in 𝓝 x, ‖mfderiv% (extChartAt I x) y‖ < C := by
  rcases eventually_norm_trivializationAt_lt E (fun (x : M) => TangentSpace% x) x
    with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  have hx : (chartAt H x).source in 𝓝 x := chart_source_mem_nhds H x
  filter_upwards [hC, hx] with y hy h'y
  rwa [← TangentBundle.continuousLinearMapAt_trivializationAt h'y]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `eventually_enorm_mfderiv_extChartAt_lt` / 引理 `eventually_enorm_mfderiv_extChartAt_lt`

English:
lemma eventually_enorm_mfderiv_extChartAt_lt
  given: (x : M)
  proof: by
  rcases eventually_norm_mfderiv_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  lift C to Real>=0 using C_pos.le
  simp only [gt_iff_lt, NNReal.coe_pos] at C_pos
  refine ⟨C, C_pos, ?_⟩
  filter_upwards [hC] with y hy
  simp only [enorm, nnnorm]
  exact_mod_cast hy

中文:
引理 eventually_enorm_mfderiv_extChartAt_lt
  条件: (x : M)
  证明: by
  rcases eventually_norm_mfderiv_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  lift C to Real>=0 using C_pos.le
  simp only [gt_iff_lt, NNReal.coe_pos] at C_pos
  refine ⟨C, C_pos, ?_⟩
  filter_upwards [hC] with y hy
  simp only [enorm, nnnorm]
  exact_mod_cast hy

Depends on / 依赖: C_pos, C_pos.le, NNReal, NNReal.coe_pos, coe_pos, eventually_norm_mfderiv_extChartAt_lt, filter_upwards, gt_iff_lt, nnnorm
-/
lemma eventually_enorm_mfderiv_extChartAt_lt (x : M) :
    exists C > (0 : Real>=0), forallᶠ y in 𝓝 x, ‖mfderiv% (extChartAt I x) y‖ₑ < C := by
  rcases eventually_norm_mfderiv_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  lift C to Real>=0 using C_pos.le
  simp only [gt_iff_lt, NNReal.coe_pos] at C_pos
  refine ⟨C, C_pos, ?_⟩
  filter_upwards [hC] with y hy
  simp only [enorm, nnnorm]
  exact_mod_cast hy

set_option backward.isDefEq.respectTransparency false in
/--
lemma `eventually_norm_mfderivWithin_symm_extChartAt_comp_lt` / 引理 `eventually_norm_mfderivWithin_symm_extChartAt_comp_lt`

English:
lemma eventually_norm_mfderivWithin_symm_extChartAt_comp_lt
  given: (x : M)
  proof: by
  rcases eventually_norm_symmL_trivializationAt_lt E (fun (x : M) => TangentSpace% x) x
    with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  have hx : (chartAt H x).source in 𝓝 x := chart_source_mem_nhds H x
  filter_upwards [hC, hx] with y hy h'y
  rw [TangentBundle.symmL_trivializationAt h'y] at h

中文:
引理 eventually_norm_mfderivWithin_symm_extChartAt_comp_lt
  条件: (x : M)
  证明: by
  rcases eventually_norm_symmL_trivializationAt_lt E (fun (x : M) => TangentSpace% x) x
    with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  have hx : (chartAt H x).source in 𝓝 x := chart_source_mem_nhds H x
  filter_upwards [hC, hx] with y hy h'y
  rw [TangentBundle.symmL_trivializationAt h'y] at h

Depends on / 依赖: C_pos, TangentBundle, TangentBundle.symmL_trivializationAt, TangentSpace, chartAt, chart_source_mem_nhds, convert, eventually_norm_symmL_trivializationAt_lt, extChartAt, filter_upwards, left_inv, source, symmL_trivializationAt
-/
lemma eventually_norm_mfderivWithin_symm_extChartAt_comp_lt (x : M) :
    exists C > 0, forallᶠ y in 𝓝 x, ‖mfderiv[range I] (extChartAt I x).symm (extChartAt I x y)‖ < C := by
  rcases eventually_norm_symmL_trivializationAt_lt E (fun (x : M) => TangentSpace% x) x
    with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  have hx : (chartAt H x).source in 𝓝 x := chart_source_mem_nhds H x
  filter_upwards [hC, hx] with y hy h'y
  rw [TangentBundle.symmL_trivializationAt h'y] at hy
  have A : (extChartAt I x).symm (extChartAt I x y) = y :=
    (extChartAt I x).left_inv (by simpa using h'y)
  convert! hy using 3 <;> congr

set_option backward.isDefEq.respectTransparency false in
/--
lemma `eventually_norm_mfderivWithin_symm_extChartAt_lt` / 引理 `eventually_norm_mfderivWithin_symm_extChartAt_lt`

English:
lemma eventually_norm_mfderivWithin_symm_extChartAt_lt
  given: (x : M)
  proof: by
  rcases eventually_norm_mfderivWithin_symm_extChartAt_comp_lt I x with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  have : 𝓝 x = 𝓝 ((extChartAt I x).symm (extChartAt I x x)) := by simp
  rw [this] at hC
  have : ContinuousAt (extChartAt I x).symm (extChartAt I x x) := continuousAt_extChartAt_symm _


中文:
引理 eventually_norm_mfderivWithin_symm_extChartAt_lt
  条件: (x : M)
  证明: by
  rcases eventually_norm_mfderivWithin_symm_extChartAt_comp_lt I x with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  have : 𝓝 x = 𝓝 ((extChartAt I x).symm (extChartAt I x x)) := by simp
  rw [this] at hC
  have : ContinuousAt (extChartAt I x).symm (extChartAt I x x) := continuousAt_extChartAt_symm _


Depends on / 依赖: C_pos, ContinuousAt, continuousAt_extChartAt_symm, eventually_norm_mfderivWithin_symm_extChartAt_comp_lt, extChartAt, extChartAt_target_mem_nhdsWithin, filter_upwards, nhdsWithin_le_nhds, preimage_mem_nhds, this.preimage_mem_nhds
-/
lemma eventually_norm_mfderivWithin_symm_extChartAt_lt (x : M) :
    exists C > 0, forallᶠ y in 𝓝[range I] (extChartAt I x x),
    ‖mfderiv[range I] (extChartAt I x).symm y‖ < C := by
  rcases eventually_norm_mfderivWithin_symm_extChartAt_comp_lt I x with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  have : 𝓝 x = 𝓝 ((extChartAt I x).symm (extChartAt I x x)) := by simp
  rw [this] at hC
  have : ContinuousAt (extChartAt I x).symm (extChartAt I x x) := continuousAt_extChartAt_symm _
  filter_upwards [nhdsWithin_le_nhds (this.preimage_mem_nhds hC),
    extChartAt_target_mem_nhdsWithin x] with y hy h'y
  have : y = (extChartAt I x) ((extChartAt I x).symm y) := by simp [-extChartAt, h'y]
  simp only [preimage_ofPred_eq, mem_ofPred_eq] at hy
  convert! hy

set_option backward.isDefEq.respectTransparency false in
/--
lemma `eventually_enorm_mfderivWithin_symm_extChartAt_lt` / 引理 `eventually_enorm_mfderivWithin_symm_extChartAt_lt`

English:
lemma eventually_enorm_mfderivWithin_symm_extChartAt_lt
  given: (x : M)
  proof: by
  rcases eventually_norm_mfderivWithin_symm_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  lift C to Real>=0 using C_pos.le
  simp only [gt_iff_lt, NNReal.coe_pos] at C_pos
  refine ⟨C, C_pos, ?_⟩
  filter_upwards [hC] with y hy
  simp only [enorm, nnnorm]
  exact_mod_cast hy

中文:
引理 eventually_enorm_mfderivWithin_symm_extChartAt_lt
  条件: (x : M)
  证明: by
  rcases eventually_norm_mfderivWithin_symm_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  lift C to Real>=0 using C_pos.le
  simp only [gt_iff_lt, NNReal.coe_pos] at C_pos
  refine ⟨C, C_pos, ?_⟩
  filter_upwards [hC] with y hy
  simp only [enorm, nnnorm]
  exact_mod_cast hy

Depends on / 依赖: C_pos, C_pos.le, NNReal, NNReal.coe_pos, coe_pos, eventually_norm_mfderivWithin_symm_extChartAt_lt, filter_upwards, gt_iff_lt, nnnorm
-/
lemma eventually_enorm_mfderivWithin_symm_extChartAt_lt (x : M) :
    exists C > (0 : Real>=0), forallᶠ y in 𝓝[range I] (extChartAt I x x),
    ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ < C := by
  rcases eventually_norm_mfderivWithin_symm_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  lift C to Real>=0 using C_pos.le
  simp only [gt_iff_lt, NNReal.coe_pos] at C_pos
  refine ⟨C, C_pos, ?_⟩
  filter_upwards [hC] with y hy
  simp only [enorm, nnnorm]
  exact_mod_cast hy

set_option backward.isDefEq.respectTransparency false in
/--
lemma `eventually_riemannianEDist_le_edist_extChartAt` / 引理 `eventually_riemannianEDist_le_edist_extChartAt`

English:
lemma eventually_riemannianEDist_le_edist_extChartAt
  given: (x : M)
  proof: by
  /- To construct a path with controlled distance from `x` to `y`, we consider the segment from
  `extChartAt x x` to `extChartAt x y` in the chart, and we push it by `(extChartAt x).symm`. As
  the derivative of the latter is locally bounded, this only multiplies the length by a bounded
  amount

中文:
引理 eventually_riemannianEDist_le_edist_extChartAt
  条件: (x : M)
  证明: by
  /- To construct a path with controlled distance from `x` to `y`, we consider the segment from
  `extChartAt x x` to `extChartAt x y` in the chart, and we push it by `(extChartAt x).symm`. As
  the derivative of the latter is locally bounded, this only multiplies the length by a bounded
  amount
-/
lemma eventually_riemannianEDist_le_edist_extChartAt (x : M) :
    exists C > (0 : Real>=0), forallᶠ y in 𝓝 x,
    riemannianEDist I x y <= C * edist (extChartAt I x x) (extChartAt I x y) := by
  /- To construct a path with controlled distance from `x` to `y`, we consider the segment from
  `extChartAt x x` to `extChartAt x y` in the chart, and we push it by `(extChartAt x).symm`. As
  the derivative of the latter is locally bounded, this only multiplies the length by a bounded
  amount. -/
  -- first start from a bound on the derivative
  rcases eventually_enorm_mfderivWithin_symm_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  -- consider a small convex set around `extChartAt x x` where everything is controlled.
  obtain ⟨r, r_pos, hr⟩ : exists r > 0,
      ball (extChartAt I x x) r inter range I subseteq (extChartAt I x).target inter
        {y | ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ < C} :=
    mem_nhdsWithin_iff.1 (inter_mem (extChartAt_target_mem_nhdsWithin x) hC)
  -- pull this set inside `M`: this is the set where we will get the estimate.
  have A : (extChartAt I x) ⁻¹' (ball (extChartAt I x x) r inter range I) in 𝓝 x := by
    apply extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (by simp)
    rw [inter_comm]
    exact inter_mem_nhdsWithin _ (ball_mem_nhds _ r_pos)
  -- consider `y` in this good set. Let `η` be the segment in the extended chart, and
  -- `γ` its composition with `(extChartAt x).symm`.
  filter_upwards [A, chart_source_mem_nhds H x] with y hy h'y
  let η := ContinuousAffineMap.lineMap (R := Real) (extChartAt I x x) (extChartAt I x y)
  set γ := (extChartAt I x).symm ∘ η
  -- by convexity, the whole segment between `extChartAt x x` and `extChartAt x y` is in the
  -- controlled set.
  have hη : Icc 0 1 subseteq ⇑η ⁻¹' ((extChartAt I x).target inter
        {y | ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ < C}) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
     ← segment_eq_image_lineMap, η]
    apply Subset.trans _ hr
    exact ((convex_ball _ _).inter I.convex_range).segment_subset (by simp [r_pos]) hy
  simp only [preimage_inter, subset_inter_iff] at hη
  have η_smooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  -- we can bound the Riemannian distance using the specific path `γ`.
  have : riemannianEDist I x y <= pathELength I γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp η_smooth hη.1
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq, h'y]
  apply this.trans
  -- Finally, we control the length of `γ` thanks to the boundedness of the derivative of
  -- `(extChartAt x).symm` on the whole controlled set.
  rw [← lintegral_fderiv_lineMap_eq_edist]; rw [pathELength_eq_lintegral_mfderivWithin_Icc]; rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
  have : mfderiv[Icc 0 1] γ t =
      (mfderiv[range I] (extChartAt I x).symm (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[range I] (extChartAt I x).symm (η t)) (mfderiv[Icc 0 1] η t 1) := congr($this 1)
  rw [this]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

/--
lemma `eventually_riemannianEDist_lt` / 引理 `eventually_riemannianEDist_lt`

English:
lemma eventually_riemannianEDist_lt
  given: (x : M) {c : Real>=0∞} (hc : 0 < c)
  proof: by
  rcases eventually_riemannianEDist_le_edist_extChartAt I x with ⟨C, C_pos, hC⟩
  have : (extChartAt I x) ⁻¹' (Metric.eball (extChartAt I x x) (c / C)) in 𝓝 x := by
    apply (continuousAt_extChartAt x).preimage_mem_nhds
    exact Metric.eball_mem_nhds _ (ENNReal.div_pos hc.ne' (by simp))
  filte

中文:
引理 eventually_riemannianEDist_lt
  条件: (x : M) {c : 实数>=0∞} (hc : 0 < c)
  证明: by
  rcases eventually_riemannianEDist_le_edist_extChartAt I x with ⟨C, C_pos, hC⟩
  have : (extChartAt I x) ⁻¹' (Metric.eball (extChartAt I x x) (c / C)) in 𝓝 x := by
    apply (continuousAt_extChartAt x).preimage_mem_nhds
    exact Metric.eball_mem_nhds _ (ENNReal.div_pos hc.ne' (by simp))
  filte

Depends on / 依赖: C_pos, ENNReal, ENNReal.div_pos, ENNReal.lt_div_iff_mul_lt, Metric, Metric.eball, Metric.eball_mem_nhds, Metric.mem_eball, continuousAt_extChartAt, div_pos, eball_mem_nhds, eventually_riemannianEDist_le_edist_extChartAt, extChartAt, filter_upwards, hc.ne, lt_div_iff_mul_lt, mem_eball, mem_preimage, mul_comm, preimage_mem_nhds
-/
lemma eventually_riemannianEDist_lt (x : M) {c : Real>=0∞} (hc : 0 < c) :
    forallᶠ y in 𝓝 x, riemannianEDist I x y < c := by
  rcases eventually_riemannianEDist_le_edist_extChartAt I x with ⟨C, C_pos, hC⟩
  have : (extChartAt I x) ⁻¹' (Metric.eball (extChartAt I x x) (c / C)) in 𝓝 x := by
    apply (continuousAt_extChartAt x).preimage_mem_nhds
    exact Metric.eball_mem_nhds _ (ENNReal.div_pos hc.ne' (by simp))
  filter_upwards [this, hC] with y hy h'y
  apply h'y.trans_lt
  have : edist (extChartAt I x x) (extChartAt I x y) < c / C := by
    simpa only [mem_preimage, Metric.mem_eball'] using hy
  rwa [ENNReal.lt_div_iff_mul_lt, mul_comm] at this
  · exact Or.inl (mod_cast C_pos.ne')
  · simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `setOfPred_riemannianEDist_lt_subset_nhds` / 引理 `setOfPred_riemannianEDist_lt_subset_nhds`

English:
lemma setOfPred_riemannianEDist_lt_subset_nhds
  given: [RegularSpace M] {x : M} {s : Set M} (hs : s in 𝓝 x)
  proof: by
  /- Consider a closed neighborhood `u` of `x` on which the derivative of the extended chart is
  bounded by some `C`, contained in `s`, then an open neighborhood `v` of `x` inside `u`,
  and finally `r` small enough that the ball of radius `r` in the extended chart is contained in
  the image of

中文:
引理 setOfPred_riemannianEDist_lt_subset_nhds
  条件: [正则空间 M] {x : M} {s : 集合 M} (hs : s in 𝓝 x)
  证明: by
  /- Consider a closed neighborhood `u` of `x` on which the derivative of the extended chart is
  bounded by some `C`, contained in `s`, then an open neighborhood `v` of `x` inside `u`,
  and finally `r` small enough that the ball of radius `r` in the extended chart is contained in
  the image of
-/
lemma setOfPred_riemannianEDist_lt_subset_nhds [RegularSpace M] {x : M} {s : Set M} (hs : s in 𝓝 x) :
    exists c > (0 : Real>=0), {y | riemannianEDist I x y < c} subseteq s := by
  /- Consider a closed neighborhood `u` of `x` on which the derivative of the extended chart is
  bounded by some `C`, contained in `s`, then an open neighborhood `v` of `x` inside `u`,
  and finally `r` small enough that the ball of radius `r` in the extended chart is contained in
  the image of `v`.

  We claim that points at Riemannian distance at most `r / C` of `x` are inside `u` (and therefore
  inside `s`). To prove this, consider a path of length at most `r / C` starting from `x`. While
  it stays inside `u`, then by the derivative control its image in the extended chart has length
  at most `r`, so it cannot exit the ball of radius `r`, which means that in the manifold it is
  inside `v` (which is strictly inside `u`). This means that the path will stay inside `u` for
  a little bit longer, by openness of `v`. Iterating this argument, it follows that the path will
  remain inside `u` for the whole time interval `[0, 1]`. In particular, its right endpoint is
  inside `u`, as desired.

  The formalization of this argument goes through the lemma
  `IsClosed.Icc_subset_of_forall_mem_nhdsGT_of_mem` which gives an induction-like principle over
  real intervals.
  -/
  -- first introduce a neighborhood where the derivative of the extended chart is bounded by `C`
  rcases eventually_enorm_mfderiv_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  -- let `u` be a closed neighborhood, inside `s`, with the derivative control
  obtain ⟨u, u_mem, u_closed, us, hu, uc⟩ : exists u in 𝓝 x, IsClosed u ∧ u subseteq s
      ∧ u subseteq {y | ‖mfderiv% (extChartAt I x) y‖ₑ < C} ∧ u subseteq (extChartAt I x).source := by
    have := Filter.inter_mem (Filter.inter_mem hs hC) (extChartAt_source_mem_nhds (I := I) x)
    rcases exists_mem_nhds_isClosed_subset this with ⟨u, u_mem, u_closed, hu⟩
    simp only [subset_inter_iff] at hu
    exact ⟨u, u_mem, u_closed, hu.1.1, hu.1.2, hu.2⟩
  have uc' : u subseteq (chartAt H x).source := by simpa [extChartAt_source I x] using uc
  -- let `v` be a smaller open neighborhood, inside `u`.
  obtain ⟨v, ⟨v_mem, v_open⟩, hv⟩ : exists v, (v in 𝓝 x ∧ IsOpen v) ∧ v subseteq u :=
    (nhds_basis_opens' x).mem_iff.1 u_mem
  -- let `r > 0` be small enough that, in the extended chart, the ball of radius `r` is contained
  -- in the image of `v`.
  obtain ⟨r, r_pos, hr⟩ : exists r > 0, ball (extChartAt I x x) r subseteq (extChartAt I x).symm ⁻¹' v :=
    Metric.mem_nhds_iff.1 (extChartAt_preimage_mem_nhds v_mem)
  lift r to Real>=0 using r_pos.le
  simp only [gt_iff_lt, NNReal.coe_pos] at r_pos
  -- the desired constant will be `c := r / C`
  refine ⟨r / C, by positivity, ?_⟩
  intro y hy
  -- consider a path `γ` of length `< r / C` from `x` to a point `y`. We will show that `y` belongs
  -- to `u`.
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hy zero_lt_one
    with ⟨γ, hγx, hγy, γ_smooth, hγ, -⟩
  let A := γ ⁻¹' u
  have zero_mem : 0 in A := by simpa [hγx, A] using mem_of_mem_nhds u_mem
  have A_closed : IsClosed (A inter Icc 0 1) :=
    (u_closed.preimage γ_smooth.continuous).inter isClosed_Icc
  suffices Icc 0 1 subseteq A by
    apply us
    have : 1 in A := this ⟨zero_le_one, le_rfl⟩
    simpa [A, hγy, us]
  apply A_closed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset zero_mem
  rintro t₁ ⟨ht₁0, ht₁1⟩ t₁_mem
  suffices γ t₁ in v from
γ_smooth.continuous.continuousWithinAt mem_of_superset (v_open.mem_nhds this) hv
  let γ' := extChartAt I x ∘ γ
  have hC : CMDiff[Icc 0 t₁] 1 γ' :=
    contMDiffOn_extChartAt.comp (I' := I) (t := (chartAt H x).source)
      γ_smooth.contMDiffOn (fun t' ht' => uc' <| t₁_mem ht')
  have : ‖γ' t₁ - γ' 0‖ₑ < r := by
    rcases ht₁0.eq_or_lt with rfl | h't'
    · simp [r_pos]
    calc
      ‖γ' t₁ - γ' 0‖ₑ
    _ <= ∫⁻ t' in Icc 0 t₁, ‖derivWithin γ' (Icc 0 t₁) t'‖ₑ := by
      apply enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc _ ht₁0
      rwa [← contMDiffOn_iff_contDiffOn]
    _ = ∫⁻ t' in Icc 0 t₁, ‖mfderiv[Icc 0 t₁] γ' t' 1‖ₑ := by
      simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
      rfl
    _ <= ∫⁻ t' in Icc 0 t₁, C * ‖mfderiv[Icc 0 t₁] γ t' 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc (fun t' ht' => ?_)
      have : mfderiv[Icc 0 t₁] γ' t' =
          (mfderiv% (extChartAt I x) (γ t')) ∘L (mfderiv[Icc 0 t₁] γ t') := by
        apply mfderiv_comp_mfderivWithin
        · refine mdifferentiableAt_extChartAt (uc' ?_)
          apply t₁_mem ht'
        · exact (γ_smooth.mdifferentiable one_ne_zero).mdifferentiableOn _ ht'
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc h't' _ ht'
      have : mfderiv[Icc 0 t₁] γ' t' 1 =
          (mfderiv% (extChartAt I x) (γ t')) (mfderiv[Icc 0 t₁] γ t' 1) :=
        congr($this 1)
      rw [this]
      apply (ContinuousLinearMap.le_opENorm _ _).trans
      gcongr
      refine (hu ?_).le
      apply t₁_mem ht'
    _ = C * pathELength I γ 0 t₁ := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]; rw [pathELength_eq_lintegral_mfderivWithin_Icc]
    _ <= C * pathELength I γ 0 1 := by
      gcongr
    _ < C * (r / C) := by
      gcongr
      · exact ENNReal.coe_ne_top
      · exact hγ.trans_eq (ENNReal.coe_div C_pos.ne')
    _ = r := (ENNReal.eq_div_iff (by simpa using C_pos.ne') ENNReal.coe_ne_top).mp rfl
  have : γ' t₁ in (extChartAt I x).symm ⁻¹' v := by
    apply hr
    rw [← Metric.eball_coe]; rw [Metric.mem_eball]; rw [edist_eq_enorm_sub]
    convert! this
    simp [γ', hγx]
  convert! mem_preimage.1 this
  simp only [Function.comp_apply, γ', (extChartAt I x).left_inv <| uc <| t₁_mem
    (right_mem_Icc.mpr ht₁0)]

@[deprecated (since := "2026-07-09")]
alias setOf_riemannianEDist_lt_subset_nhds := setOfPred_riemannianEDist_lt_subset_nhds

/--
lemma `setOfPred_riemannianEDist_lt_subset_nhds'` / 引理 `setOfPred_riemannianEDist_lt_subset_nhds'`

English:
lemma setOfPred_riemannianEDist_lt_subset_nhds'
  statement: [RegularSpace M] {x : M} {s : Set M}
  proof: by
  rcases setOfPred_riemannianEDist_lt_subset_nhds I hs with ⟨c, c_pos, hc⟩
  exact ⟨c, mod_cast c_pos, hc⟩

@[deprecated (since := "2026-07-09")]
alias setOf_riemannianEDist_lt_subset_nhds' := setOfPred_riemannianEDist_lt_subset_nhds'

中文:
引理 setOfPred_riemannianEDist_lt_subset_nhds'
  结论: [正则空间 M] {x : M} {s : 集合 M}
  证明: by
  rcases setOfPred_riemannianEDist_lt_subset_nhds I hs with ⟨c, c_pos, hc⟩
  exact ⟨c, mod_cast c_pos, hc⟩

@[deprecated (since := "2026-07-09")]
alias setOf_riemannianEDist_lt_subset_nhds' := setOfPred_riemannianEDist_lt_subset_nhds'

Depends on / 依赖: c_pos, mod_cast, setOfPred_riemannianEDist_lt_subset_nhds
-/
lemma setOfPred_riemannianEDist_lt_subset_nhds' [RegularSpace M] {x : M} {s : Set M}
    (hs : s in 𝓝 x) :
    exists c > 0, {y | riemannianEDist I x y < c} subseteq s := by
  rcases setOfPred_riemannianEDist_lt_subset_nhds I hs with ⟨c, c_pos, hc⟩
  exact ⟨c, mod_cast c_pos, hc⟩

@[deprecated (since := "2026-07-09")]
alias setOf_riemannianEDist_lt_subset_nhds' := setOfPred_riemannianEDist_lt_subset_nhds'

variable (M) in
/--
Definition of `PseudoEMetricSpace.ofRiemannianMetric` / `PseudoEMetricSpace.ofRiemannianMetric` 的定义

English:
definition PseudoEMetricSpace.ofRiemannianMetric
  signature: [RegularSpace M]
  body: PseudoEMetricSpace.ofEDistOfTopology (riemannianEDist I (M := M))
    (fun _ => riemannianEDist_self)
    (fun _ _ => riemannianEDist_comm)
    (fun _ _ _ => riemannianEDist_triangle)
    (fun x => (basis_sets (𝓝 x)).to_hasBasis'
      (fun _ hs => setOfPred_riemannianEDist_lt_subset_nhds' I hs)
   

中文:
定义 PseudoEMetric空间.ofRiemannianMetric
  签名: [正则空间 M]
  定义体: PseudoEMetricSpace.ofEDistOfTopology (riemannianEDist I (M := M))
    (fun _ => riemannianEDist_self)
    (fun _ _ => riemannianEDist_comm)
    (fun _ _ _ => riemannianEDist_triangle)
    (fun x => (basis_sets (𝓝 x)).to_hasBasis'
      (fun _ hs => setOfPred_riemannianEDist_lt_subset_nhds' I hs)
   
-/
@[reducible] def PseudoEMetricSpace.ofRiemannianMetric [RegularSpace M] : PseudoEMetricSpace M :=
  PseudoEMetricSpace.ofEDistOfTopology (riemannianEDist I (M := M))
    (fun _ => riemannianEDist_self)
    (fun _ _ => riemannianEDist_comm)
    (fun _ _ _ => riemannianEDist_triangle)
    (fun x => (basis_sets (𝓝 x)).to_hasBasis'
      (fun _ hs => setOfPred_riemannianEDist_lt_subset_nhds' I hs)
      (fun _ hc => eventually_riemannianEDist_lt I x hc))

@[deprecated (since := "2026-01-08")]
noncomputable alias PseudoEmetricSpace.ofRiemannianMetric := PseudoEMetricSpace.ofRiemannianMetric

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RegularSpace
  signature: M] :
  body: .ofRiemannianMetric I M
    IsRiemannianManifold I M := by
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  exact ⟨fun x y => rfl⟩

中文:
实例 [正则空间
  签名: M] :
  定义体: .ofRiemannianMetric I M
    IsRiemannianManifold I M := by
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  exact ⟨fun x y => rfl⟩

Depends on / 依赖: ofRiemannianMetric
-/
instance [RegularSpace M] :
    letI : PseudoEMetricSpace M := .ofRiemannianMetric I M
    IsRiemannianManifold I M := by
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  exact ⟨fun x y => rfl⟩

variable (M) in
/--
Definition of `EMetricSpace.ofRiemannianMetric` / `EMetricSpace.ofRiemannianMetric` 的定义

English:
definition EMetricSpace.ofRiemannianMetric
  signature: [T3Space M]
  body: letI : PseudoEMetricSpace M := .ofRiemannianMetric I M
  EMetricSpace.ofT0PseudoEMetricSpace M

@[deprecated (since := "2026-01-08")]
noncomputable alias EmetricSpace.ofRiemannianMetric := EMetricSpace.ofRiemannianMetric

中文:
定义 广义度量空间.ofRiemannianMetric
  签名: [T3空间 M]
  定义体: letI : PseudoEMetricSpace M := .ofRiemannianMetric I M
  EMetricSpace.ofT0PseudoEMetricSpace M

@[deprecated (since := "2026-01-08")]
noncomputable alias EmetricSpace.ofRiemannianMetric := EMetricSpace.ofRiemannianMetric
-/
@[reducible] def EMetricSpace.ofRiemannianMetric [T3Space M] : EMetricSpace M :=
  letI : PseudoEMetricSpace M := .ofRiemannianMetric I M
  EMetricSpace.ofT0PseudoEMetricSpace M

@[deprecated (since := "2026-01-08")]
noncomputable alias EmetricSpace.ofRiemannianMetric := EMetricSpace.ofRiemannianMetric

end
