/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Polar coordinate change of variables for the mixed space of a number field

We define two polar coordinate changes of variables for the mixed space `ℝ^r₁ × ℂ^r₂` associated
to a number field `K` of signature `(r₁, r₂)`. The first one is `mixedEmbedding.polarCoord` and has
value in `realMixedSpace K` defined as `ℝ^r₁ × (ℝ ⨯ ℝ)^r₂`, the second is
`mixedEmbedding.polarSpaceCoord` and has value in `polarSpace K` defined as `ℝ^(r₁+r₂) × ℝ^r₂`.

The change of variables with the `polarSpace` is useful to compute the volume of subsets of the
mixed space with enough symmetries, see `volume_eq_two_pi_pow_mul_integral` and
`volume_eq_two_pow_mul_two_pi_pow_mul_integral`

## Main definitions and results

* `mixedEmbedding.polarCoord`: the polar coordinate change of variables between the mixed
  space `ℝ^r₁ × ℂ^r₂` and `ℝ^r₁ × (ℝ × ℝ)^r₂` defined as the identity on the first component and
  mapping `(zᵢ)ᵢ` to `(‖zᵢ‖, Arg zᵢ)ᵢ` on the second component.

* `mixedEmbedding.integral_comp_polarCoord_symm`: the change of variables formula for
  `mixedEmbedding.polarCoord`

* `mixedEmbedding.polarSpaceCoord`: the polar coordinate change of variables between the mixed
  space `ℝ^r₁ × ℂ^r₂` and the polar space `ℝ^(r₁ + r₂) × ℝ^r₂` defined by sending `x` to
  `x w` or `‖x w‖` depending on whether `w` is real or complex for the first component, and
  to `Arg (x w)`, `w` complex, for the second component.

* `mixedEmbedding.integral_comp_polarSpaceCoord_symm`: the change of variables formula for
  `mixedEmbedding.polarSpaceCoord`

* `mixedEmbedding.volume_eq_two_pi_pow_mul_integral`: if the measurable set `A` of the mixed space
  is norm-stable at complex places in the sense that
  `normAtComplexPlaces⁻¹ (normAtComplexPlaces '' A) = A`, then its volume can be computed via an
  integral over `normAtComplexPlaces '' A`.

* `mixedEmbedding.volume_eq_two_pow_mul_two_pi_pow_mul_integral`: if the measurable set `A` of the
  mixed space is norm-stable in the sense that `normAtAllPlaces⁻¹ (normAtAllPlaces '' A) = A`,
  then its volume can be computed via an integral over `normAtAllPlaces '' A`.

-/

@[expose] public section

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding ENNReal MeasureTheory
  MeasureTheory.Measure Real

noncomputable section realMixedSpace

/--
Definition of `realMixedSpace` / `realMixedSpace` 的定义

English:
abbreviation realMixedSpace
  body: ({w : InfinitePlace K // IsReal w} -> Real) × ({w : InfinitePlace K // IsComplex w} -> Real × Real)

中文:
缩写 realMixedSpace
  定义体: ({w : InfinitePlace K // IsReal w} -> Real) × ({w : InfinitePlace K // IsComplex w} -> Real × Real)

Depends on / 依赖: InfinitePlace, IsComplex, IsReal
-/
abbrev realMixedSpace :=
  ({w : InfinitePlace K // IsReal w} -> Real) × ({w : InfinitePlace K // IsComplex w} -> Real × Real)

/--
Definition of `mixedSpaceToRealMixedSpace` / `mixedSpaceToRealMixedSpace` 的定义

English:
definition mixedSpaceToRealMixedSpace
  signature: : mixedSpace K ≃ₜ realMixedSpace K
  body: (Homeomorph.refl _).prodCongr .piCongrRight fun _ => Complex.equivRealProdCLM.toHomeomorph

@[simp]

中文:
定义 mixedSpaceTo实数MixedSpace
  签名: : mixedSpace K ≃ₜ realMixedSpace K
  定义体: (Homeomorph.refl _).prodCongr .piCongrRight fun _ => Complex.equivRealProdCLM.toHomeomorph

@[simp]

Depends on / 依赖: Complex.equivRealProdCLM.toHomeomorph, Homeomorph, Homeomorph.refl, equivRealProdCLM, piCongrRight, prodCongr, toHomeomorph
-/
noncomputable def mixedSpaceToRealMixedSpace : mixedSpace K ≃ₜ realMixedSpace K :=
(Homeomorph.refl _).prodCongr .piCongrRight fun _ => Complex.equivRealProdCLM.toHomeomorph

@[simp]
/--
theorem `mixedSpaceToRealMixedSpace_apply` / 定理 `mixedSpaceToRealMixedSpace_apply`

English:
theorem mixedSpaceToRealMixedSpace_apply
  given: (x : mixedSpace K)
  proof: rfl

中文:
定理 mixedSpaceTo实数MixedSpace_apply
  条件: (x : mixedSpace K)
  证明: rfl
-/
theorem mixedSpaceToRealMixedSpace_apply (x : mixedSpace K) :
    mixedSpaceToRealMixedSpace K x = (x.1, fun w => Complex.equivRealProd (x.2 w)) := rfl

variable [NumberField K]

open scoped Classical in
/--
theorem `volume_preserving_mixedSpaceToRealMixedSpace_symm` / 定理 `volume_preserving_mixedSpaceToRealMixedSpace_symm`

English:
theorem volume_preserving_mixedSpaceToRealMixedSpace_symm
  proof: (MeasurePreserving.id _).prod
    volume_preserving_pi fun _ => Complex.volume_preserving_equiv_real_prod.symm

中文:
定理 volume_preserving_mixedSpaceTo实数MixedSpace_symm
  证明: (MeasurePreserving.id _).prod
    volume_preserving_pi fun _ => Complex.volume_preserving_equiv_real_prod.symm

Depends on / 依赖: Complex.volume_preserving_equiv_real_prod.symm, MeasurePreserving, MeasurePreserving.id, volume_preserving_equiv_real_prod, volume_preserving_pi
-/
theorem volume_preserving_mixedSpaceToRealMixedSpace_symm :
    MeasurePreserving (mixedSpaceToRealMixedSpace K).symm :=
(MeasurePreserving.id _).prod
    volume_preserving_pi fun _ => Complex.volume_preserving_equiv_real_prod.symm

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddHaarMeasure (volume : Measure (realMixedSpace K))
  body: prod.instIsAddHaarMeasure _ _

中文:
实例 :
  签名: 是加法Haar测度 (volume : 测度 (realMixedSpace K))
  定义体: prod.instIsAddHaarMeasure _ _

Depends on / 依赖: instIsAddHaarMeasure, prod.instIsAddHaarMeasure
-/
instance : IsAddHaarMeasure (volume : Measure (realMixedSpace K)) := prod.instIsAddHaarMeasure _ _

/--
The polar coordinate open partial homeomorphism of `ℝ^r₁ × (ℝ × ℝ)^r₂` defined as the identity on
the first component and mapping `(rᵢ cos θᵢ, rᵢ sin θᵢ)ᵢ` to `(rᵢ, θᵢ)ᵢ` on the second component.
-/
@[simps! apply target]
/--
Definition of `polarCoordReal` / `polarCoordReal` 的定义

English:
definition polarCoordReal
  signature: : OpenPartialHomeomorph (realMixedSpace K) (realMixedSpace K)
  body: (OpenPartialHomeomorph.refl _).prod (OpenPartialHomeomorph.pi fun _ => polarCoord)

中文:
定义 polarCoord实数
  签名: : OpenPartialHomeomorph (realMixedSpace K) (realMixedSpace K)
  定义体: (OpenPartialHomeomorph.refl _).prod (OpenPartialHomeomorph.pi fun _ => polarCoord)

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.pi, OpenPartialHomeomorph.refl, polarCoord
-/
def polarCoordReal : OpenPartialHomeomorph (realMixedSpace K) (realMixedSpace K) :=
  (OpenPartialHomeomorph.refl _).prod (OpenPartialHomeomorph.pi fun _ => polarCoord)

/--
theorem `measurable_polarCoordReal_symm` / 定理 `measurable_polarCoordReal_symm`

English:
theorem measurable_polarCoordReal_symm
  proof: by
refine measurable_fst.prodMk Measurable.comp ?_ measurable_snd
  exact measurable_pi_lambda _
    fun _ => continuous_polarCoord_symm.measurable.comp (measurable_pi_apply _)

中文:
定理 measurable_polarCoord实数_symm
  证明: by
refine measurable_fst.prodMk Measurable.comp ?_ measurable_snd
  exact measurable_pi_lambda _
    fun _ => continuous_polarCoord_symm.measurable.comp (measurable_pi_apply _)

Depends on / 依赖: Measurable, Measurable.comp, continuous_polarCoord_symm, continuous_polarCoord_symm.measurable.comp, measurable, measurable_fst, measurable_fst.prodMk, measurable_pi_apply, measurable_pi_lambda, measurable_snd, prodMk
-/
theorem measurable_polarCoordReal_symm :
    Measurable (polarCoordReal K).symm := by
refine measurable_fst.prodMk Measurable.comp ?_ measurable_snd
  exact measurable_pi_lambda _
    fun _ => continuous_polarCoord_symm.measurable.comp (measurable_pi_apply _)

/--
theorem `polarCoordReal_source` / 定理 `polarCoordReal_source`

English:
theorem polarCoordReal_source
  proof: rfl

中文:
定理 polarCoord实数_source
  证明: rfl
-/
theorem polarCoordReal_source :
    (polarCoordReal K).source = Set.univ ×ˢ (Set.univ.pi fun _ => polarCoord.source) := rfl

/--
theorem `abs_of_mem_polarCoordReal_target` / 定理 `abs_of_mem_polarCoordReal_target`

English:
theorem abs_of_mem_polarCoordReal_target
  statement: {x : realMixedSpace K}
  proof: abs_of_pos (hx.2 w (Set.mem_univ _)).1

中文:
定理 abs_of_mem_polarCoord实数_target
  结论: {x : realMixedSpace K}
  证明: abs_of_pos (hx.2 w (Set.mem_univ _)).1
-/
private theorem abs_of_mem_polarCoordReal_target {x : realMixedSpace K}
    (hx : x in (polarCoordReal K).target) (w : {w // IsComplex w}) :
    |(x.2 w).1| = (x.2 w).1 :=
  abs_of_pos (hx.2 w (Set.mem_univ _)).1

open ContinuousLinearMap in
/--
Definition of `FDerivPolarCoordRealSymm` / `FDerivPolarCoordRealSymm` 的定义

English:
definition FDerivPolarCoordRealSymm
  signature: : realMixedSpace K -> realMixedSpace K ->L[Real] realMixedSpace K
  body: fun x => (fst Real _ _).prod (fderivPiPolarCoordSymm x.2).comp (snd Real _ _)

中文:
定义 FDerivPolarCoord实数Symm
  签名: : realMixedSpace K -> realMixedSpace K ->L[实数] realMixedSpace K
  定义体: fun x => (fst Real _ _).prod (fderivPiPolarCoordSymm x.2).comp (snd Real _ _)

Depends on / 依赖: fderivPiPolarCoordSymm
-/
def FDerivPolarCoordRealSymm : realMixedSpace K -> realMixedSpace K ->L[Real] realMixedSpace K :=
fun x => (fst Real _ _).prod (fderivPiPolarCoordSymm x.2).comp (snd Real _ _)

/--
theorem `hasFDerivAt_polarCoordReal_symm` / 定理 `hasFDerivAt_polarCoordReal_symm`

English:
theorem hasFDerivAt_polarCoordReal_symm
  given: (x : realMixedSpace K)
  proof: by
  classical
  exact (hasFDerivAt_id x.1).prodMap x (hasFDerivAt_pi_polarCoord_symm x.2)

中文:
定理 hasFDerivAt_polarCoord实数_symm
  条件: (x : realMixedSpace K)
  证明: by
  classical
  exact (hasFDerivAt_id x.1).prodMap x (hasFDerivAt_pi_polarCoord_symm x.2)

Depends on / 依赖: classical, hasFDerivAt_id, hasFDerivAt_pi_polarCoord_symm, prodMap
-/
theorem hasFDerivAt_polarCoordReal_symm (x : realMixedSpace K) :
    HasFDerivAt (polarCoordReal K).symm (FDerivPolarCoordRealSymm K x) x := by
  classical
  exact (hasFDerivAt_id x.1).prodMap x (hasFDerivAt_pi_polarCoord_symm x.2)

open scoped Classical in
/--
theorem `det_fderivPolarCoordRealSymm` / 定理 `det_fderivPolarCoordRealSymm`

English:
theorem det_fderivPolarCoordRealSymm
  given: (x : realMixedSpace K)
  proof: by
  have : (FDerivPolarCoordRealSymm K x).toLinearMap =
      LinearMap.prodMap (LinearMap.id) (fderivPiPolarCoordSymm x.2).toLinearMap := rfl
  rw [ContinuousLinearMap.det]; rw [this]; rw [LinearMap.det_prodMap]; rw [LinearMap.det_id]; rw [one_mul]; rw [← ContinuousLinearMap.det]; rw [det_fderivPiPolarCoordSymm]

中文:
定理 det_fderivPolarCoord实数Symm
  条件: (x : realMixedSpace K)
  证明: by
  have : (FDerivPolarCoordRealSymm K x).toLinearMap =
      LinearMap.prodMap (LinearMap.id) (fderivPiPolarCoordSymm x.2).toLinearMap := rfl
  rw [ContinuousLinearMap.det]; rw [this]; rw [LinearMap.det_prodMap]; rw [LinearMap.det_id]; rw [one_mul]; rw [← ContinuousLinearMap.det]; rw [det_fderivPiPolarCoordSymm]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.det, FDerivPolarCoordRealSymm, LinearMap, LinearMap.det_id, LinearMap.det_prodMap, LinearMap.id, LinearMap.prodMap, det_fderivPiPolarCoordSymm, det_id, det_prodMap, fderivPiPolarCoordSymm, one_mul, prodMap, toLinearMap
-/
theorem det_fderivPolarCoordRealSymm (x : realMixedSpace K) :
    (FDerivPolarCoordRealSymm K x).det = ∏ w : {w // IsComplex w}, (x.2 w).1 := by
  have : (FDerivPolarCoordRealSymm K x).toLinearMap =
      LinearMap.prodMap (LinearMap.id) (fderivPiPolarCoordSymm x.2).toLinearMap := rfl
  rw [ContinuousLinearMap.det]; rw [this]; rw [LinearMap.det_prodMap]; rw [LinearMap.det_id]; rw [one_mul]; rw [← ContinuousLinearMap.det]; rw [det_fderivPiPolarCoordSymm]

open scoped Classical in
/--
theorem `polarCoordReal_symm_target_ae_eq_univ` / 定理 `polarCoordReal_symm_target_ae_eq_univ`

English:
theorem polarCoordReal_symm_target_ae_eq_univ
  proof: by
  rw [← Set.univ_prod_univ]; rw [volume_eq_prod]; rw [(polarCoordReal K).symm_image_target_eq_source]; rw [polarCoordReal_source]; rw [← polarCoord.symm_image_target_eq_source]; rw [← Set.piMap_image_univ_pi]
  exact set_prod_ae_eq .rfl pi_polarCoord_symm_target_ae_eq_univ

中文:
定理 polarCoord实数_symm_target_ae_eq_univ
  证明: by
  rw [← Set.univ_prod_univ]; rw [volume_eq_prod]; rw [(polarCoordReal K).symm_image_target_eq_source]; rw [polarCoordReal_source]; rw [← polarCoord.symm_image_target_eq_source]; rw [← Set.piMap_image_univ_pi]
  exact set_prod_ae_eq .rfl pi_polarCoord_symm_target_ae_eq_univ

Depends on / 依赖: Set.piMap_image_univ_pi, Set.univ_prod_univ, piMap_image_univ_pi, pi_polarCoord_symm_target_ae_eq_univ, polarCoord, polarCoord.symm_image_target_eq_source, polarCoordReal, polarCoordReal_source, set_prod_ae_eq, symm_image_target_eq_source, univ_prod_univ, volume_eq_prod
-/
theorem polarCoordReal_symm_target_ae_eq_univ :
    (polarCoordReal K).symm '' (polarCoordReal K).target =ᵐ[volume] Set.univ := by
  rw [← Set.univ_prod_univ]; rw [volume_eq_prod]; rw [(polarCoordReal K).symm_image_target_eq_source]; rw [polarCoordReal_source]; rw [← polarCoord.symm_image_target_eq_source]; rw [← Set.piMap_image_univ_pi]
  exact set_prod_ae_eq .rfl pi_polarCoord_symm_target_ae_eq_univ

open scoped Classical in
/--
theorem `integral_comp_polarCoordReal_symm` / 定理 `integral_comp_polarCoordReal_symm`

English:
theorem integral_comp_polarCoordReal_symm
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  rw [← setIntegral_univ (f := f)]; rw [← setIntegral_congr_set (polarCoordReal_symm_target_ae_eq_univ K)]; rw [integral_image_eq_integral_abs_det_fderiv_smul volume
      (polarCoordReal K).open_target.measurableSet
      (fun x _ => (hasFDerivAt_polarCoordReal_symm K x).hasFDerivWithinAt)
      (polarCoordReal K).symm.injOn f]
  refine setIntegral_congr_fun (polarCoordReal K).open_target.measurableSet fun x hx => ?_
  simp_rw [det_fderivPolarCoordRealSymm, Finset.abs_prod, abs_of_mem_polarCoordReal_target K hx]

中文:
定理 integral_comp_polarCoord实数_symm
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  rw [← setIntegral_univ (f := f)]; rw [← setIntegral_congr_set (polarCoordReal_symm_target_ae_eq_univ K)]; rw [integral_image_eq_integral_abs_det_fderiv_smul volume
      (polarCoordReal K).open_target.measurableSet
      (fun x _ => (hasFDerivAt_polarCoordReal_symm K x).hasFDerivWithinAt)
      (polarCoordReal K).symm.injOn f]
  refine setIntegral_congr_fun (polarCoordReal K).open_target.measurableSet fun x hx => ?_
  simp_rw [det_fderivPolarCoordRealSymm, Finset.abs_prod, abs_of_mem_polarCoordReal_target K hx]

Depends on / 依赖: Finset, Finset.abs_prod, abs_of_mem_polarCoordReal_target, abs_prod, det_fderivPolarCoordRealSymm, hasFDerivAt_polarCoordReal_symm, hasFDerivWithinAt, integral_image_eq_integral_abs_det_fderiv_smul, measurableSet, open_target, open_target.measurableSet, polarCoordReal, polarCoordReal_symm_target_ae_eq_univ, setIntegral_congr_fun, setIntegral_congr_set, setIntegral_univ, simp_rw, symm.injOn, volume
-/
theorem integral_comp_polarCoordReal_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (f : realMixedSpace K -> E) :
    ∫ x in (polarCoordReal K).target, (∏ w : {w // IsComplex w}, (x.2 w).1) •
      f ((polarCoordReal K).symm x) = ∫ x, f x := by
  rw [← setIntegral_univ (f := f)]; rw [← setIntegral_congr_set (polarCoordReal_symm_target_ae_eq_univ K)]; rw [integral_image_eq_integral_abs_det_fderiv_smul volume
      (polarCoordReal K).open_target.measurableSet
      (fun x _ => (hasFDerivAt_polarCoordReal_symm K x).hasFDerivWithinAt)
      (polarCoordReal K).symm.injOn f]
  refine setIntegral_congr_fun (polarCoordReal K).open_target.measurableSet fun x hx => ?_
  simp_rw [det_fderivPolarCoordRealSymm, Finset.abs_prod, abs_of_mem_polarCoordReal_target K hx]

open scoped Classical in
/--
theorem `lintegral_comp_polarCoordReal_symm` / 定理 `lintegral_comp_polarCoordReal_symm`

English:
theorem lintegral_comp_polarCoordReal_symm
  given: (f : realMixedSpace K -> Real>=0∞)
  proof: by
  rw [← setLIntegral_univ f]; rw [← setLIntegral_congr (polarCoordReal_symm_target_ae_eq_univ K)]; rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      (polarCoordReal K).open_target.measurableSet
      (fun x _ => (hasFDerivAt_polarCoordReal_symm K x).hasFDerivWithinAt)
      (polarCoordReal K).symm.injOn f]
  refine setLIntegral_congr_fun (polarCoordReal K).open_target.measurableSet (fun x hx => ?_)
  simp_rw [det_fderivPolarCoordRealSymm, Finset.abs_prod,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => abs_nonneg _), abs_of_mem_polarCoordReal_target K hx]

中文:
定理 lintegral_comp_polarCoord实数_symm
  条件: (f : realMixedSpace K -> 实数>=0∞)
  证明: by
  rw [← setLIntegral_univ f]; rw [← setLIntegral_congr (polarCoordReal_symm_target_ae_eq_univ K)]; rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      (polarCoordReal K).open_target.measurableSet
      (fun x _ => (hasFDerivAt_polarCoordReal_symm K x).hasFDerivWithinAt)
      (polarCoordReal K).symm.injOn f]
  refine setLIntegral_congr_fun (polarCoordReal K).open_target.measurableSet (fun x hx => ?_)
  simp_rw [det_fderivPolarCoordRealSymm, Finset.abs_prod,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => abs_nonneg _), abs_of_mem_polarCoordReal_target K hx]

Depends on / 依赖: ENNReal, ENNReal.ofReal_prod_of_nonneg, Finset, Finset.abs_prod, abs_, abs_prod, det_fderivPolarCoordRealSymm, hasFDerivAt_polarCoordReal_symm, hasFDerivWithinAt, lintegral_image_eq_lintegral_abs_det_fderiv_mul, measurableSet, ofReal_prod_of_nonneg, open_target, open_target.measurableSet, polarCoordReal, polarCoordReal_symm_target_ae_eq_univ, setLIntegral_congr, setLIntegral_congr_fun, setLIntegral_univ, simp_rw
-/
theorem lintegral_comp_polarCoordReal_symm (f : realMixedSpace K -> Real>=0∞) :
    ∫⁻ x in (polarCoordReal K).target, (∏ w : {w // IsComplex w}, .ofReal (x.2 w).1) *
      f ((polarCoordReal K).symm x) = ∫⁻ x, f x := by
  rw [← setLIntegral_univ f]; rw [← setLIntegral_congr (polarCoordReal_symm_target_ae_eq_univ K)]; rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      (polarCoordReal K).open_target.measurableSet
      (fun x _ => (hasFDerivAt_polarCoordReal_symm K x).hasFDerivWithinAt)
      (polarCoordReal K).symm.injOn f]
  refine setLIntegral_congr_fun (polarCoordReal K).open_target.measurableSet (fun x hx => ?_)
  simp_rw [det_fderivPolarCoordRealSymm, Finset.abs_prod,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => abs_nonneg _), abs_of_mem_polarCoordReal_target K hx]

end realMixedSpace

section mixedSpace

variable [NumberField K]

/--
The polar coordinate open partial homeomorphism between the mixed space `ℝ^r₁ × ℂ^r₂` and
`ℝ^r₁ × (ℝ × ℝ)^r₂` defined as the identity on the first component and mapping `(zᵢ)ᵢ` to
`(‖zᵢ‖, Arg zᵢ)ᵢ` on the second component.
-/
@[simps!]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def polarCoord
  body: (OpenPartialHomeomorph.refl _).prod (OpenPartialHomeomorph.pi fun _ => Complex.polarCoord)

中文:
定义 noncomputable
  签名: def polarCoord
  定义体: (OpenPartialHomeomorph.refl _).prod (OpenPartialHomeomorph.pi fun _ => Complex.polarCoord)
-/
protected noncomputable def polarCoord : OpenPartialHomeomorph (mixedSpace K) (realMixedSpace K) :=
  (OpenPartialHomeomorph.refl _).prod (OpenPartialHomeomorph.pi fun _ => Complex.polarCoord)

/--
theorem `polarCoord_target_eq_polarCoordReal_target` / 定理 `polarCoord_target_eq_polarCoordReal_target`

English:
theorem polarCoord_target_eq_polarCoordReal_target
  proof: rfl

中文:
定理 polarCoord_target_eq_polarCoord实数_target
  证明: rfl
-/
theorem polarCoord_target_eq_polarCoordReal_target :
    (mixedEmbedding.polarCoord K).target = (polarCoordReal K).target := rfl

/--
theorem `polarCoord_symm_eq` / 定理 `polarCoord_symm_eq`

English:
theorem polarCoord_symm_eq
  proof: rfl

中文:
定理 polarCoord_symm_eq
  证明: rfl
-/
theorem polarCoord_symm_eq :
    (mixedEmbedding.polarCoord K).symm =
      (mixedSpaceToRealMixedSpace K).symm ∘ (polarCoordReal K).symm := rfl

/--
theorem `measurable_polarCoord_symm` / 定理 `measurable_polarCoord_symm`

English:
theorem measurable_polarCoord_symm
  proof: by
  rw [polarCoord_symm_eq]
  exact (Homeomorph.measurable _).comp (measurable_polarCoordReal_symm K)

中文:
定理 measurable_polarCoord_symm
  证明: by
  rw [polarCoord_symm_eq]
  exact (Homeomorph.measurable _).comp (measurable_polarCoordReal_symm K)

Depends on / 依赖: Homeomorph, Homeomorph.measurable, measurable, measurable_polarCoordReal_symm, polarCoord_symm_eq
-/
theorem measurable_polarCoord_symm :
    Measurable (mixedEmbedding.polarCoord K).symm := by
  rw [polarCoord_symm_eq]
  exact (Homeomorph.measurable _).comp (measurable_polarCoordReal_symm K)

/--
theorem `normAtPlace_polarCoord_symm_of_isReal` / 定理 `normAtPlace_polarCoord_symm_of_isReal`

English:
theorem normAtPlace_polarCoord_symm_of_isReal
  statement: (x : realMixedSpace K) {w : InfinitePlace K}
  proof: by
  simp [normAtPlace_apply_of_isReal hw]

中文:
定理 normAtPlace_polarCoord_symm_of_is实数
  结论: (x : realMixedSpace K) {w : InfinitePlace K}
  证明: by
  simp [normAtPlace_apply_of_isReal hw]

Depends on / 依赖: normAtPlace_apply_of_isReal
-/
theorem normAtPlace_polarCoord_symm_of_isReal (x : realMixedSpace K) {w : InfinitePlace K}
    (hw : IsReal w) :
    normAtPlace w ((mixedEmbedding.polarCoord K).symm x) = ‖x.1 ⟨w, hw⟩‖ := by
  simp [normAtPlace_apply_of_isReal hw]

/--
theorem `normAtPlace_polarCoord_symm_of_isComplex` / 定理 `normAtPlace_polarCoord_symm_of_isComplex`

English:
theorem normAtPlace_polarCoord_symm_of_isComplex
  statement: (x : realMixedSpace K)
  proof: by
  simp [normAtPlace_apply_of_isComplex hw]

中文:
定理 normAtPlace_polarCoord_symm_of_isComplex
  结论: (x : realMixedSpace K)
  证明: by
  simp [normAtPlace_apply_of_isComplex hw]

Depends on / 依赖: normAtPlace_apply_of_isComplex
-/
theorem normAtPlace_polarCoord_symm_of_isComplex (x : realMixedSpace K)
    {w : InfinitePlace K} (hw : IsComplex w) :
    normAtPlace w ((mixedEmbedding.polarCoord K).symm x) = ‖(x.2 ⟨w, hw⟩).1‖ := by
  simp [normAtPlace_apply_of_isComplex hw]

open scoped Classical in
/--
theorem `integral_comp_polarCoord_symm` / 定理 `integral_comp_polarCoord_symm`

English:
theorem integral_comp_polarCoord_symm
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  rw [← (volume_preserving_mixedSpaceToRealMixedSpace_symm K).integral_comp
    (mixedSpaceToRealMixedSpace K).symm.measurableEmbedding]; rw [← integral_comp_polarCoordReal_symm]; rw [polarCoord_target_eq_polarCoordReal_target]; rw [polarCoord_symm_eq]; rw [Function.comp_def]

中文:
定理 integral_comp_polarCoord_symm
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  rw [← (volume_preserving_mixedSpaceToRealMixedSpace_symm K).integral_comp
    (mixedSpaceToRealMixedSpace K).symm.measurableEmbedding]; rw [← integral_comp_polarCoordReal_symm]; rw [polarCoord_target_eq_polarCoordReal_target]; rw [polarCoord_symm_eq]; rw [Function.comp_def]
-/
protected theorem integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (f : mixedSpace K -> E) :
    ∫ x in (mixedEmbedding.polarCoord K).target,
      (∏ w : {w // IsComplex w}, (x.2 w).1) • f ((mixedEmbedding.polarCoord K).symm x) =
        ∫ x, f x := by
  rw [← (volume_preserving_mixedSpaceToRealMixedSpace_symm K).integral_comp
    (mixedSpaceToRealMixedSpace K).symm.measurableEmbedding]; rw [← integral_comp_polarCoordReal_symm]; rw [polarCoord_target_eq_polarCoordReal_target]; rw [polarCoord_symm_eq]; rw [Function.comp_def]

open scoped Classical in
/--
theorem `lintegral_comp_polarCoord_symm` / 定理 `lintegral_comp_polarCoord_symm`

English:
theorem lintegral_comp_polarCoord_symm
  given: (f : mixedSpace K -> Real>=0∞)
  proof: by
  rw [← (volume_preserving_mixedSpaceToRealMixedSpace_symm K).lintegral_comp_emb
    (mixedSpaceToRealMixedSpace K).symm.measurableEmbedding]; rw [← lintegral_comp_polarCoordReal_symm]; rw [polarCoord_target_eq_polarCoordReal_target]; rw [polarCoord_symm_eq]; rw [Function.comp_def]

中文:
定理 lintegral_comp_polarCoord_symm
  条件: (f : mixedSpace K -> 实数>=0∞)
  证明: by
  rw [← (volume_preserving_mixedSpaceToRealMixedSpace_symm K).lintegral_comp_emb
    (mixedSpaceToRealMixedSpace K).symm.measurableEmbedding]; rw [← lintegral_comp_polarCoordReal_symm]; rw [polarCoord_target_eq_polarCoordReal_target]; rw [polarCoord_symm_eq]; rw [Function.comp_def]
-/
protected theorem lintegral_comp_polarCoord_symm (f : mixedSpace K -> Real>=0∞) :
    ∫⁻ x in (mixedEmbedding.polarCoord K).target, (∏ w : {w // IsComplex w}, .ofReal (x.2 w).1) *
      f ((mixedEmbedding.polarCoord K).symm x) = ∫⁻ x, f x := by
  rw [← (volume_preserving_mixedSpaceToRealMixedSpace_symm K).lintegral_comp_emb
    (mixedSpaceToRealMixedSpace K).symm.measurableEmbedding]; rw [← lintegral_comp_polarCoordReal_symm]; rw [polarCoord_target_eq_polarCoordReal_target]; rw [polarCoord_symm_eq]; rw [Function.comp_def]

end mixedSpace

noncomputable section polarSpace

open MeasurableEquiv

/--
Definition of `polarSpace` / `polarSpace` 的定义

English:
abbreviation polarSpace
  body: ((InfinitePlace K) -> Real) × ({w : InfinitePlace K // w.IsComplex} -> Real)

中文:
缩写 polarSpace
  定义体: ((InfinitePlace K) -> Real) × ({w : InfinitePlace K // w.IsComplex} -> Real)

Depends on / 依赖: InfinitePlace, IsComplex, w.IsComplex
-/
abbrev polarSpace := ((InfinitePlace K) -> Real) × ({w : InfinitePlace K // w.IsComplex} -> Real)

open scoped Classical in
/--
Definition of `measurableEquivRealMixedSpacePolarSpace` / `measurableEquivRealMixedSpacePolarSpace` 的定义

English:
definition measurableEquivRealMixedSpacePolarSpace
  signature: : realMixedSpace K ≃ᵐ polarSpace K
  body: MeasurableEquiv.trans (prodCongr (refl _)
    (arrowProdEquivProdArrow Real Real _)) <|
MeasurableEquiv.trans prodAssoc.symm
      MeasurableEquiv.trans
        (prodCongr (prodCongr (refl _)
          (arrowCongr' (Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex.symm)) (refl _)))
            (refl _))
          (prodCongr (piEquivPiSubtypeProd (fun _ => Real) _).symm (refl _))

中文:
定义 measurableEquiv实数MixedSpacePolarSpace
  签名: : realMixedSpace K ≃ᵐ polarSpace K
  定义体: MeasurableEquiv.trans (prodCongr (refl _)
    (arrowProdEquivProdArrow Real Real _)) <|
MeasurableEquiv.trans prodAssoc.symm
      MeasurableEquiv.trans
        (prodCongr (prodCongr (refl _)
          (arrowCongr' (Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex.symm)) (refl _)))
            (refl _))
          (prodCongr (piEquivPiSubtypeProd (fun _ => Real) _).symm (refl _))

Depends on / 依赖: Equiv.subtypeEquivRight, MeasurableEquiv, MeasurableEquiv.trans, arrowCongr, arrowProdEquivProdArrow, not_isReal_iff_isComplex, not_isReal_iff_isComplex.symm, piEquivPiSubtypeProd, prodAssoc, prodAssoc.symm, prodCongr, subtypeEquivRight
-/
def measurableEquivRealMixedSpacePolarSpace : realMixedSpace K ≃ᵐ polarSpace K :=
  MeasurableEquiv.trans (prodCongr (refl _)
    (arrowProdEquivProdArrow Real Real _)) <|
MeasurableEquiv.trans prodAssoc.symm
      MeasurableEquiv.trans
        (prodCongr (prodCongr (refl _)
          (arrowCongr' (Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex.symm)) (refl _)))
            (refl _))
          (prodCongr (piEquivPiSubtypeProd (fun _ => Real) _).symm (refl _))

open scoped Classical in
/--
Definition of `homeoRealMixedSpacePolarSpace` / `homeoRealMixedSpacePolarSpace` 的定义

English:
definition homeoRealMixedSpacePolarSpace
  signature: : realMixedSpace K ≃ₜ polarSpace K
  body: { measurableEquivRealMixedSpacePolarSpace K with
  continuous_toFun := by
    change Continuous fun x : realMixedSpace K => (fun w => if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w => (x.2 w).2)
    refine .prodMk (continuous_pi fun w => ?_) (by fun_prop)
    split_ifs <;> fun_prop
  continuous_invFun := by
    change Continuous fun x : polarSpace K =>
      (⟨fun w => x.1 w.val, fun w => ⟨x.1 w.val, x.2 w⟩⟩ : realMixedSpace K)
    fun_prop }

中文:
定义 homeo实数MixedSpacePolarSpace
  签名: : realMixedSpace K ≃ₜ polarSpace K
  定义体: { measurableEquivRealMixedSpacePolarSpace K with
  continuous_toFun := by
    change Continuous fun x : realMixedSpace K => (fun w => if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w => (x.2 w).2)
    refine .prodMk (continuous_pi fun w => ?_) (by fun_prop)
    split_ifs <;> fun_prop
  continuous_invFun := by
    change Continuous fun x : polarSpace K =>
      (⟨fun w => x.1 w.val, fun w => ⟨x.1 w.val, x.2 w⟩⟩ : realMixedSpace K)
    fun_prop }

Depends on / 依赖: Continuous, IsReal, continuous_invFun, continuous_pi, continuous_toFun, fun_prop, measurableEquivRealMixedSpacePolarSpace, not_isReal_iff_isComplex, not_isReal_iff_isComplex.mp, polarSpace, prodMk, realMixedSpace, split_ifs, w.IsReal, w.val
-/
def homeoRealMixedSpacePolarSpace : realMixedSpace K ≃ₜ polarSpace K :=
{ measurableEquivRealMixedSpacePolarSpace K with
  continuous_toFun := by
    change Continuous fun x : realMixedSpace K => (fun w => if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w => (x.2 w).2)
    refine .prodMk (continuous_pi fun w => ?_) (by fun_prop)
    split_ifs <;> fun_prop
  continuous_invFun := by
    change Continuous fun x : polarSpace K =>
      (⟨fun w => x.1 w.val, fun w => ⟨x.1 w.val, x.2 w⟩⟩ : realMixedSpace K)
    fun_prop }

open scoped Classical in
/--
theorem `homeoRealMixedSpacePolarSpace_apply` / 定理 `homeoRealMixedSpacePolarSpace_apply`

English:
theorem homeoRealMixedSpacePolarSpace_apply
  given: (x : realMixedSpace K)
  proof: rfl

中文:
定理 homeo实数MixedSpacePolarSpace_apply
  条件: (x : realMixedSpace K)
  证明: rfl
-/
theorem homeoRealMixedSpacePolarSpace_apply (x : realMixedSpace K) :
    homeoRealMixedSpacePolarSpace K x =
      ⟨fun w => if hw : w.IsReal then x.1 ⟨w, hw⟩ else
        (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w => (x.2 w).2⟩ := rfl

/--
theorem `homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal` / 定理 `homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal`

English:
theorem homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal
  statement: (x : realMixedSpace K)
  proof: by
  simp_rw [homeoRealMixedSpacePolarSpace_apply, dif_pos w.prop]

中文:
定理 homeo实数MixedSpacePolarSpace_apply_fst_ofIs实数
  结论: (x : realMixedSpace K)
  证明: by
  simp_rw [homeoRealMixedSpacePolarSpace_apply, dif_pos w.prop]

Depends on / 依赖: dif_pos, homeoRealMixedSpacePolarSpace_apply, simp_rw, w.prop
-/
theorem homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal (x : realMixedSpace K)
    (w : {w // IsReal w}) :
    (homeoRealMixedSpacePolarSpace K x).1 w.1 = x.1 w := by
  simp_rw [homeoRealMixedSpacePolarSpace_apply, dif_pos w.prop]

/--
theorem `homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex` / 定理 `homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex`

English:
theorem homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex
  statement: (x : realMixedSpace K)
  proof: by
  simp_rw [homeoRealMixedSpacePolarSpace_apply, dif_neg (not_isReal_iff_isComplex.mpr w.prop)]

中文:
定理 homeo实数MixedSpacePolarSpace_apply_fst_ofIsComplex
  结论: (x : realMixedSpace K)
  证明: by
  simp_rw [homeoRealMixedSpacePolarSpace_apply, dif_neg (not_isReal_iff_isComplex.mpr w.prop)]

Depends on / 依赖: dif_neg, homeoRealMixedSpacePolarSpace_apply, not_isReal_iff_isComplex, not_isReal_iff_isComplex.mpr, simp_rw, w.prop
-/
theorem homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex (x : realMixedSpace K)
    (w : {w // IsComplex w}) :
    (homeoRealMixedSpacePolarSpace K x).1 w.1 = (x.2 w).1 := by
  simp_rw [homeoRealMixedSpacePolarSpace_apply, dif_neg (not_isReal_iff_isComplex.mpr w.prop)]

/--
theorem `homeoRealMixedSpacePolarSpace_apply_snd` / 定理 `homeoRealMixedSpacePolarSpace_apply_snd`

English:
theorem homeoRealMixedSpacePolarSpace_apply_snd
  given: (x : realMixedSpace K) (w : {w // IsComplex w})
  proof: rfl

@[simp]

中文:
定理 homeo实数MixedSpacePolarSpace_apply_snd
  条件: (x : realMixedSpace K) (w : {w // 是复形 w})
  证明: rfl

@[simp]
-/
theorem homeoRealMixedSpacePolarSpace_apply_snd (x : realMixedSpace K) (w : {w // IsComplex w}) :
    (homeoRealMixedSpacePolarSpace K x).2 w = (x.2 w).2 := rfl

@[simp]
/--
theorem `homeoRealMixedSpacePolarSpace_symm_apply` / 定理 `homeoRealMixedSpacePolarSpace_symm_apply`

English:
theorem homeoRealMixedSpacePolarSpace_symm_apply
  given: (x : polarSpace K)
  proof: rfl

中文:
定理 homeo实数MixedSpacePolarSpace_symm_apply
  条件: (x : polarSpace K)
  证明: rfl
-/
theorem homeoRealMixedSpacePolarSpace_symm_apply (x : polarSpace K) :
    (homeoRealMixedSpacePolarSpace K).symm x = ⟨fun w => x.1 w, fun w => (x.1 w, x.2 w)⟩ := rfl

open scoped Classical in
/--
theorem `volume_preserving_homeoRealMixedSpacePolarSpace` / 定理 `volume_preserving_homeoRealMixedSpacePolarSpace`

English:
theorem volume_preserving_homeoRealMixedSpacePolarSpace
  given: [NumberField K]
  proof: ((MeasurePreserving.id volume).prod
    (volume_measurePreserving_arrowProdEquivProdArrow Real Real _)).trans <|
(volume_preserving_prodAssoc.symm).trans
        (((MeasurePreserving.id volume).prod (volume_preserving_arrowCongr' _
          (MeasurableEquiv.refl Real) (.id volume))).prod (.id volume)).trans <|
            ((volume_preserving_piEquivPiSubtypeProd
              (fun _ : InfinitePlace K => Real) (fun w => IsReal w)).symm).prod (.id volume)

中文:
定理 volume_preserving_homeo实数MixedSpacePolarSpace
  条件: [数域 K]
  证明: ((MeasurePreserving.id volume).prod
    (volume_measurePreserving_arrowProdEquivProdArrow Real Real _)).trans <|
(volume_preserving_prodAssoc.symm).trans
        (((MeasurePreserving.id volume).prod (volume_preserving_arrowCongr' _
          (MeasurableEquiv.refl Real) (.id volume))).prod (.id volume)).trans <|
            ((volume_preserving_piEquivPiSubtypeProd
              (fun _ : InfinitePlace K => Real) (fun w => IsReal w)).symm).prod (.id volume)

Depends on / 依赖: InfinitePlace, IsReal, MeasurableEquiv, MeasurableEquiv.refl, MeasurePreserving, MeasurePreserving.id, volume, volume_measurePreserving_arrowProdEquivProdArrow, volume_preserving_arrowCongr, volume_preserving_piEquivPiSubtypeProd, volume_preserving_prodAssoc, volume_preserving_prodAssoc.symm
-/
theorem volume_preserving_homeoRealMixedSpacePolarSpace [NumberField K] :
    MeasurePreserving (homeoRealMixedSpacePolarSpace K) :=
  ((MeasurePreserving.id volume).prod
    (volume_measurePreserving_arrowProdEquivProdArrow Real Real _)).trans <|
(volume_preserving_prodAssoc.symm).trans
        (((MeasurePreserving.id volume).prod (volume_preserving_arrowCongr' _
          (MeasurableEquiv.refl Real) (.id volume))).prod (.id volume)).trans <|
            ((volume_preserving_piEquivPiSubtypeProd
              (fun _ : InfinitePlace K => Real) (fun w => IsReal w)).symm).prod (.id volume)

/--
The polar coordinate open partial homeomorphism between the mixed space `ℝ^r₁ × ℂ^r₂` and the polar
space `ℝ^(r₁ + r₂) × ℝ^r₂` defined by sending `x` to `x w` or `‖x w‖` depending on whether `w` is
real or complex for the first component, and to `Arg (x w)`, `w` complex, for the second component.
-/
@[simps!]
/--
Definition of `polarSpaceCoord` / `polarSpaceCoord` 的定义

English:
definition polarSpaceCoord
  signature: [NumberField K]
  body: (mixedEmbedding.polarCoord K).transHomeomorph (homeoRealMixedSpacePolarSpace K)

中文:
定义 polarSpaceCoord
  签名: [数域 K]
  定义体: (mixedEmbedding.polarCoord K).transHomeomorph (homeoRealMixedSpacePolarSpace K)

Depends on / 依赖: homeoRealMixedSpacePolarSpace, mixedEmbedding, mixedEmbedding.polarCoord, polarCoord, transHomeomorph
-/
def polarSpaceCoord [NumberField K] : OpenPartialHomeomorph (mixedSpace K) (polarSpace K) :=
    (mixedEmbedding.polarCoord K).transHomeomorph (homeoRealMixedSpacePolarSpace K)

/--
theorem `measurable_polarSpaceCoord_symm` / 定理 `measurable_polarSpaceCoord_symm`

English:
theorem measurable_polarSpaceCoord_symm
  given: [NumberField K]
  proof: by
  rw [polarSpaceCoord]; rw [OpenPartialHomeomorph.transHomeomorph_symm_apply]
  exact (measurable_polarCoord_symm K).comp (Homeomorph.measurable _)

中文:
定理 measurable_polarSpaceCoord_symm
  条件: [数域 K]
  证明: by
  rw [polarSpaceCoord]; rw [OpenPartialHomeomorph.transHomeomorph_symm_apply]
  exact (measurable_polarCoord_symm K).comp (Homeomorph.measurable _)

Depends on / 依赖: Homeomorph, Homeomorph.measurable, OpenPartialHomeomorph, OpenPartialHomeomorph.transHomeomorph_symm_apply, measurable, measurable_polarCoord_symm, polarSpaceCoord, transHomeomorph_symm_apply
-/
theorem measurable_polarSpaceCoord_symm [NumberField K] :
    Measurable (polarSpaceCoord K).symm := by
  rw [polarSpaceCoord]; rw [OpenPartialHomeomorph.transHomeomorph_symm_apply]
  exact (measurable_polarCoord_symm K).comp (Homeomorph.measurable _)

open scoped Classical in
/--
theorem `polarSpaceCoord_target'` / 定理 `polarSpaceCoord_target'`

English:
theorem polarSpaceCoord_target'
  given: [NumberField K]
  proof: by
  ext
  simp_rw [polarSpaceCoord_target, Set.mem_preimage, homeoRealMixedSpacePolarSpace_symm_apply,
    Set.mem_prod, Set.mem_univ, true_and, Set.mem_univ_pi, Set.mem_ite_univ_left,
    not_isReal_iff_isComplex, Subtype.forall, Complex.polarCoord_target, Set.mem_prod, forall_and]

中文:
定理 polarSpaceCoord_target'
  条件: [数域 K]
  证明: by
  ext
  simp_rw [polarSpaceCoord_target, Set.mem_preimage, homeoRealMixedSpacePolarSpace_symm_apply,
    Set.mem_prod, Set.mem_univ, true_and, Set.mem_univ_pi, Set.mem_ite_univ_left,
    not_isReal_iff_isComplex, Subtype.forall, Complex.polarCoord_target, Set.mem_prod, forall_and]

Depends on / 依赖: Complex.polarCoord_target, Set.mem_ite_univ_left, Set.mem_preimage, Set.mem_prod, Set.mem_univ, Set.mem_univ_pi, Subtype, Subtype.forall, forall_and, homeoRealMixedSpacePolarSpace_symm_apply, mem_ite_univ_left, mem_preimage, mem_prod, mem_univ, mem_univ_pi, not_isReal_iff_isComplex, polarCoord_target, polarSpaceCoord_target, simp_rw, true_and
-/
theorem polarSpaceCoord_target' [NumberField K] :
    (polarSpaceCoord K).target =
      (Set.univ.pi fun w => if w.IsReal then Set.univ else Set.Ioi 0) ×ˢ
        (Set.univ.pi fun _ => Set.Ioo (-π) π) := by
  ext
  simp_rw [polarSpaceCoord_target, Set.mem_preimage, homeoRealMixedSpacePolarSpace_symm_apply,
    Set.mem_prod, Set.mem_univ, true_and, Set.mem_univ_pi, Set.mem_ite_univ_left,
    not_isReal_iff_isComplex, Subtype.forall, Complex.polarCoord_target, Set.mem_prod, forall_and]

open scoped Classical in
/--
theorem `integral_comp_polarSpaceCoord_symm` / 定理 `integral_comp_polarSpaceCoord_symm`

English:
theorem integral_comp_polarSpaceCoord_symm
  statement: [NumberField K] {E : Type*} [NormedAddCommGroup E]
  proof: by
  rw [← (volume_preserving_homeoRealMixedSpacePolarSpace K).setIntegral_preimage_emb
    (homeoRealMixedSpacePolarSpace K).measurableEmbedding]; rw [← mixedEmbedding.integral_comp_polarCoord_symm]; rw [polarSpaceCoord_target]; rw [← Homeomorph.image_eq_preimage_symm]; rw [Homeomorph.preimage_image]; rw [mixedEmbedding.polarCoord_target]
  simp_rw [polarSpaceCoord_symm_apply, mixedEmbedding.polarCoord_symm_apply,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex, homeoRealMixedSpacePolarSpace_apply_snd]

中文:
定理 integral_comp_polarSpaceCoord_symm
  结论: [数域 K] {E : 类型} [赋范交换加群 E]
  证明: by
  rw [← (volume_preserving_homeoRealMixedSpacePolarSpace K).setIntegral_preimage_emb
    (homeoRealMixedSpacePolarSpace K).measurableEmbedding]; rw [← mixedEmbedding.integral_comp_polarCoord_symm]; rw [polarSpaceCoord_target]; rw [← Homeomorph.image_eq_preimage_symm]; rw [Homeomorph.preimage_image]; rw [mixedEmbedding.polarCoord_target]
  simp_rw [polarSpaceCoord_symm_apply, mixedEmbedding.polarCoord_symm_apply,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex, homeoRealMixedSpacePolarSpace_apply_snd]

Depends on / 依赖: Homeomorph, Homeomorph.image_eq_preimage_symm, Homeomorph.preimage_image, homeoRealMixedSpacePolarSpace, homeoRealMixedSpacePolarSpace_apply_fst, homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal, image_eq_preimage_symm, integral_comp_polarCoord_symm, measurableEmbedding, mixedEmbedding, mixedEmbedding.integral_comp_polarCoord_symm, mixedEmbedding.polarCoord_symm_apply, mixedEmbedding.polarCoord_target, polarCoord_symm_apply, polarCoord_target, polarSpaceCoord_symm_apply, polarSpaceCoord_target, preimage_image, setIntegral_preimage_emb, simp_rw
-/
theorem integral_comp_polarSpaceCoord_symm [NumberField K] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] (f : mixedSpace K -> E) :
    ∫ x in (polarSpaceCoord K).target,
      (∏ w : {w // IsComplex w}, x.1 w.1) • f ((polarSpaceCoord K).symm x) = ∫ x, f x := by
  rw [← (volume_preserving_homeoRealMixedSpacePolarSpace K).setIntegral_preimage_emb
    (homeoRealMixedSpacePolarSpace K).measurableEmbedding]; rw [← mixedEmbedding.integral_comp_polarCoord_symm]; rw [polarSpaceCoord_target]; rw [← Homeomorph.image_eq_preimage_symm]; rw [Homeomorph.preimage_image]; rw [mixedEmbedding.polarCoord_target]
  simp_rw [polarSpaceCoord_symm_apply, mixedEmbedding.polarCoord_symm_apply,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex, homeoRealMixedSpacePolarSpace_apply_snd]

open scoped Classical in
/--
theorem `lintegral_comp_polarSpaceCoord_symm` / 定理 `lintegral_comp_polarSpaceCoord_symm`

English:
theorem lintegral_comp_polarSpaceCoord_symm
  given: [NumberField K] (f : mixedSpace K -> Real>=0∞)
  proof: by
  rw [← (volume_preserving_homeoRealMixedSpacePolarSpace K).setLIntegral_comp_preimage_emb
    (homeoRealMixedSpacePolarSpace K).measurableEmbedding]; rw [← mixedEmbedding.lintegral_comp_polarCoord_symm]; rw [polarSpaceCoord_target]; rw [← Homeomorph.image_eq_preimage_symm]; rw [Homeomorph.preimage_image]; rw [mixedEmbedding.polarCoord_target]
  simp_rw [polarSpaceCoord_symm_apply, mixedEmbedding.polarCoord_symm_apply,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex, homeoRealMixedSpacePolarSpace_apply_snd]

中文:
定理 lintegral_comp_polarSpaceCoord_symm
  条件: [数域 K] (f : mixedSpace K -> 实数>=0∞)
  证明: by
  rw [← (volume_preserving_homeoRealMixedSpacePolarSpace K).setLIntegral_comp_preimage_emb
    (homeoRealMixedSpacePolarSpace K).measurableEmbedding]; rw [← mixedEmbedding.lintegral_comp_polarCoord_symm]; rw [polarSpaceCoord_target]; rw [← Homeomorph.image_eq_preimage_symm]; rw [Homeomorph.preimage_image]; rw [mixedEmbedding.polarCoord_target]
  simp_rw [polarSpaceCoord_symm_apply, mixedEmbedding.polarCoord_symm_apply,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex, homeoRealMixedSpacePolarSpace_apply_snd]

Depends on / 依赖: Homeomorph, Homeomorph.image_eq_preimage_symm, Homeomorph.preimage_image, homeoRealMixedSpacePolarSpace, homeoRealMixedSpacePolarSpace_ap, homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal, image_eq_preimage_symm, lintegral_comp_polarCoord_symm, measurableEmbedding, mixedEmbedding, mixedEmbedding.lintegral_comp_polarCoord_symm, mixedEmbedding.polarCoord_symm_apply, mixedEmbedding.polarCoord_target, polarCoord_symm_apply, polarCoord_target, polarSpaceCoord_symm_apply, polarSpaceCoord_target, preimage_image, setLIntegral_comp_preimage_emb, simp_rw
-/
theorem lintegral_comp_polarSpaceCoord_symm [NumberField K] (f : mixedSpace K -> Real>=0∞) :
    ∫⁻ x in (polarSpaceCoord K).target,
      (∏ w : {w // IsComplex w}, .ofReal (x.1 w.1)) * f ((polarSpaceCoord K).symm x) =
        ∫⁻ x, f x := by
  rw [← (volume_preserving_homeoRealMixedSpacePolarSpace K).setLIntegral_comp_preimage_emb
    (homeoRealMixedSpacePolarSpace K).measurableEmbedding]; rw [← mixedEmbedding.lintegral_comp_polarCoord_symm]; rw [polarSpaceCoord_target]; rw [← Homeomorph.image_eq_preimage_symm]; rw [Homeomorph.preimage_image]; rw [mixedEmbedding.polarCoord_target]
  simp_rw [polarSpaceCoord_symm_apply, mixedEmbedding.polarCoord_symm_apply,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex, homeoRealMixedSpacePolarSpace_apply_snd]

variable {K}

variable {A : Set (mixedSpace K)}

/--
theorem `normAtComplexPlaces_polarSpaceCoord_symm` / 定理 `normAtComplexPlaces_polarSpaceCoord_symm`

English:
theorem normAtComplexPlaces_polarSpaceCoord_symm
  given: [NumberField K] (x : polarSpace K)
  proof: by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simp [normAtComplexPlaces_apply_isReal ⟨w, hw⟩, mixedSpaceOfRealSpace_apply]
  · simp [normAtComplexPlaces_apply_isComplex ⟨w, hw⟩, mixedSpaceOfRealSpace_apply]

中文:
定理 normAtComplexPlaces_polarSpaceCoord_symm
  条件: [数域 K] (x : polarSpace K)
  证明: by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simp [normAtComplexPlaces_apply_isReal ⟨w, hw⟩, mixedSpaceOfRealSpace_apply]
  · simp [normAtComplexPlaces_apply_isComplex ⟨w, hw⟩, mixedSpaceOfRealSpace_apply]

Depends on / 依赖: isReal_or_isComplex, mixedSpaceOfRealSpace_apply, normAtComplexPlaces_apply_isComplex, normAtComplexPlaces_apply_isReal
-/
theorem normAtComplexPlaces_polarSpaceCoord_symm [NumberField K] (x : polarSpace K) :
    normAtComplexPlaces ((polarSpaceCoord K).symm x) =
      normAtComplexPlaces (mixedSpaceOfRealSpace x.1) := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simp [normAtComplexPlaces_apply_isReal ⟨w, hw⟩, mixedSpaceOfRealSpace_apply]
  · simp [normAtComplexPlaces_apply_isComplex ⟨w, hw⟩, mixedSpaceOfRealSpace_apply]

open scoped ComplexOrder Classical in
/--
theorem `volume_eq_two_pi_pow_mul_integral_aux` / 定理 `volume_eq_two_pi_pow_mul_integral_aux`

English:
theorem volume_eq_two_pi_pow_mul_integral_aux
  proof: by
  have h : forall (x : mixedSpace K), forall w, IsComplex w -> 0 <= normAtComplexPlaces x w := by
    intro x w hw
    rw [normAtComplexPlaces_apply_isComplex ⟨w]; rw [hw⟩]
    exact norm_nonneg _
  ext x
  refine ⟨?_, fun ⟨hx₁, hx₂⟩ => ?_⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨?_, by simpa using h a⟩
    rw [Set.mem_preimage]; rw [← hA]; rw [Set.mem_preimage]; rw [normAtComplexPlaces_mixedSpaceOfRealSpace (h a)]
    exact Set.mem_image_of_mem _ ha
  · rwa [Set.mem_preimage, ← hA, Set.mem_preimage, normAtComplexPlaces_mixedSpaceOfRealSpace] at hx₁
    intro w hw
    simpa [if_neg (not_isReal_iff_isComplex.mpr hw)] using hx₂ w (Set.mem_univ w)

中文:
定理 volume_eq_two_pi_pow_mul_integral_aux
  证明: by
  have h : forall (x : mixedSpace K), forall w, IsComplex w -> 0 <= normAtComplexPlaces x w := by
    intro x w hw
    rw [normAtComplexPlaces_apply_isComplex ⟨w]; rw [hw⟩]
    exact norm_nonneg _
  ext x
  refine ⟨?_, fun ⟨hx₁, hx₂⟩ => ?_⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨?_, by simpa using h a⟩
    rw [Set.mem_preimage]; rw [← hA]; rw [Set.mem_preimage]; rw [normAtComplexPlaces_mixedSpaceOfRealSpace (h a)]
    exact Set.mem_image_of_mem _ ha
  · rwa [Set.mem_preimage, ← hA, Set.mem_preimage, normAtComplexPlaces_mixedSpaceOfRealSpace] at hx₁
    intro w hw
    simpa [if_neg (not_isReal_iff_isComplex.mpr hw)] using hx₂ w (Set.mem_univ w)
-/
private theorem volume_eq_two_pi_pow_mul_integral_aux
    (hA : normAtComplexPlaces ⁻¹' normAtComplexPlaces '' A = A) :
    normAtComplexPlaces '' A =
      (mixedSpaceOfRealSpace ⁻¹' A) inter
        Set.univ.pi fun w => if w.IsReal then Set.univ else Set.Ici 0 := by
  have h : forall (x : mixedSpace K), forall w, IsComplex w -> 0 <= normAtComplexPlaces x w := by
    intro x w hw
    rw [normAtComplexPlaces_apply_isComplex ⟨w]; rw [hw⟩]
    exact norm_nonneg _
  ext x
  refine ⟨?_, fun ⟨hx₁, hx₂⟩ => ?_⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨?_, by simpa using h a⟩
    rw [Set.mem_preimage]; rw [← hA]; rw [Set.mem_preimage]; rw [normAtComplexPlaces_mixedSpaceOfRealSpace (h a)]
    exact Set.mem_image_of_mem _ ha
  · rwa [Set.mem_preimage, ← hA, Set.mem_preimage, normAtComplexPlaces_mixedSpaceOfRealSpace] at hx₁
    intro w hw
    simpa [if_neg (not_isReal_iff_isComplex.mpr hw)] using hx₂ w (Set.mem_univ w)

open scoped Classical in
/--
theorem `volume_eq_two_pi_pow_mul_integral` / 定理 `volume_eq_two_pi_pow_mul_integral`

English:
theorem volume_eq_two_pi_pow_mul_integral
  statement: [NumberField K]
  proof: by
  have hA' {x} : (A.indicator 1 x : Real>=0∞) =
      (normAtComplexPlaces '' A).indicator 1 (normAtComplexPlaces x) := by
    simp_rw [← Set.indicator_comp_right, Function.comp_def, Pi.one_def, hA]
  rw [← lintegral_indicator_one hm]; rw [← lintegral_comp_polarSpaceCoord_symm]; rw [polarSpaceCoord_target']; rw [Measure.volume_eq_prod]; rw [setLIntegral_prod]
  · simp_rw [hA', normAtComplexPlaces_polarSpaceCoord_symm, lintegral_const, restrict_apply
      MeasurableSet.univ, Set.univ_inter, volume_pi, Measure.pi_pi, volume_Ioo, sub_neg_eq_add,
      ← two_mul, Finset.prod_const, Finset.card_univ, ← Set.indicator_const_mul,
      ← Set.indicator_comp_right, Function.comp_def, Pi.one_apply, mul_one]
    rw [lintegral_mul_const' _ _ (ne_of_beq_false rfl).symm]; rw [mul_comm]
    erw [setLIntegral_indicator (by convert! hm.preimage mixedSpaceOfRealSpace.measurable)]
    rw [hA]; rw [volume_eq_two_pi_pow_mul_integral_aux hA]
    congr 1
    refine setLIntegral_congr (ae_eq_set_inter (by rfl) (Measure.ae_eq_set_pi fun w _ => ?_))
    split_ifs
    exacts [ae_eq_rfl, Ioi_ae_eq_Ici]
  · exact (Measurable.mul (by fun_prop)
 measurable_const.indicator hm.preimage (measurable_polarSpaceCoord_symm K)).aemeasurable

中文:
定理 volume_eq_two_pi_pow_mul_integral
  结论: [数域 K]
  证明: by
  have hA' {x} : (A.indicator 1 x : Real>=0∞) =
      (normAtComplexPlaces '' A).indicator 1 (normAtComplexPlaces x) := by
    simp_rw [← Set.indicator_comp_right, Function.comp_def, Pi.one_def, hA]
  rw [← lintegral_indicator_one hm]; rw [← lintegral_comp_polarSpaceCoord_symm]; rw [polarSpaceCoord_target']; rw [Measure.volume_eq_prod]; rw [setLIntegral_prod]
  · simp_rw [hA', normAtComplexPlaces_polarSpaceCoord_symm, lintegral_const, restrict_apply
      MeasurableSet.univ, Set.univ_inter, volume_pi, Measure.pi_pi, volume_Ioo, sub_neg_eq_add,
      ← two_mul, Finset.prod_const, Finset.card_univ, ← Set.indicator_const_mul,
      ← Set.indicator_comp_right, Function.comp_def, Pi.one_apply, mul_one]
    rw [lintegral_mul_const' _ _ (ne_of_beq_false rfl).symm]; rw [mul_comm]
    erw [setLIntegral_indicator (by convert! hm.preimage mixedSpaceOfRealSpace.measurable)]
    rw [hA]; rw [volume_eq_two_pi_pow_mul_integral_aux hA]
    congr 1
    refine setLIntegral_congr (ae_eq_set_inter (by rfl) (Measure.ae_eq_set_pi fun w _ => ?_))
    split_ifs
    exacts [ae_eq_rfl, Ioi_ae_eq_Ici]
  · exact (Measurable.mul (by fun_prop)
 measurable_const.indicator hm.preimage (measurable_polarSpaceCoord_symm K)).aemeasurable

Depends on / 依赖: A.indicator, Function, Function.comp_def, MeasurableSet, MeasurableSet.univ, Measure, Measure.pi_p, Measure.volume_eq_prod, Pi.one_def, Set.indicator_comp_right, Set.univ_inter, comp_def, indicator, indicator_comp_right, lintegral_comp_polarSpaceCoord_symm, lintegral_const, lintegral_indicator_one, normAtComplexPlaces, normAtComplexPlaces_polarSpaceCoord_symm, one_def
-/
theorem volume_eq_two_pi_pow_mul_integral [NumberField K]
    (hA : normAtComplexPlaces ⁻¹' normAtComplexPlaces '' A = A) (hm : MeasurableSet A) :
    volume A = .ofReal (2 * π) ^ nrComplexPlaces K *
      ∫⁻ x in normAtComplexPlaces '' A, ∏ w : {w // IsComplex w}, ENNReal.ofReal (x w.1) := by
  have hA' {x} : (A.indicator 1 x : Real>=0∞) =
      (normAtComplexPlaces '' A).indicator 1 (normAtComplexPlaces x) := by
    simp_rw [← Set.indicator_comp_right, Function.comp_def, Pi.one_def, hA]
  rw [← lintegral_indicator_one hm]; rw [← lintegral_comp_polarSpaceCoord_symm]; rw [polarSpaceCoord_target']; rw [Measure.volume_eq_prod]; rw [setLIntegral_prod]
  · simp_rw [hA', normAtComplexPlaces_polarSpaceCoord_symm, lintegral_const, restrict_apply
      MeasurableSet.univ, Set.univ_inter, volume_pi, Measure.pi_pi, volume_Ioo, sub_neg_eq_add,
      ← two_mul, Finset.prod_const, Finset.card_univ, ← Set.indicator_const_mul,
      ← Set.indicator_comp_right, Function.comp_def, Pi.one_apply, mul_one]
    rw [lintegral_mul_const' _ _ (ne_of_beq_false rfl).symm]; rw [mul_comm]
    erw [setLIntegral_indicator (by convert! hm.preimage mixedSpaceOfRealSpace.measurable)]
    rw [hA]; rw [volume_eq_two_pi_pow_mul_integral_aux hA]
    congr 1
    refine setLIntegral_congr (ae_eq_set_inter (by rfl) (Measure.ae_eq_set_pi fun w _ => ?_))
    split_ifs
    exacts [ae_eq_rfl, Ioi_ae_eq_Ici]
  · exact (Measurable.mul (by fun_prop)
 measurable_const.indicator hm.preimage (measurable_polarSpaceCoord_symm K)).aemeasurable

/--
theorem `volume_eq_two_pow_mul_two_pi_pow_mul_integral_aux` / 定理 `volume_eq_two_pow_mul_two_pi_pow_mul_integral_aux`

English:
theorem volume_eq_two_pow_mul_two_pi_pow_mul_integral_aux
  proof: by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha, rfl⟩, ha₂⟩
    refine ⟨mixedSpaceOfRealSpace (normAtAllPlaces a), ⟨?_, ?_⟩, ?_⟩
    · rw [← hA, Set.mem_preimage, normAtAllPlaces_normAtAllPlaces]
      exact Set.mem_image_of_mem normAtAllPlaces ha
    · intro w
      refine lt_of_le_of_ne' (normAtPlace_nonneg _ _) (Set.mem_iInter.mp ha₂ w)
    · rw [normAtComplexPlaces_normAtAllPlaces]
  · rintro ⟨a, ⟨ha₁, ha₂⟩, rfl⟩
    refine ⟨⟨a, ha₁, funext fun w => ?_⟩, Set.mem_iInter.mpr fun w => ?_⟩
    · obtain hw | hw := isReal_or_isComplex w
      · simpa [normAtComplexPlaces_apply_isReal ⟨w, hw⟩, normAtPlace_apply_of_isReal hw]
          using (ha₂ ⟨w, hw⟩).le
      · rw [normAtAllPlaces_apply, normAtPlace_apply_of_isComplex hw,
          normAtComplexPlaces_apply_isComplex ⟨w, hw⟩]
    · simpa [Set.mem_ofPred_eq, normAtComplexPlaces_apply_isReal] using (ha₂ w).ne'

中文:
定理 volume_eq_two_pow_mul_two_pi_pow_mul_integral_aux
  证明: by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha, rfl⟩, ha₂⟩
    refine ⟨mixedSpaceOfRealSpace (normAtAllPlaces a), ⟨?_, ?_⟩, ?_⟩
    · rw [← hA, Set.mem_preimage, normAtAllPlaces_normAtAllPlaces]
      exact Set.mem_image_of_mem normAtAllPlaces ha
    · intro w
      refine lt_of_le_of_ne' (normAtPlace_nonneg _ _) (Set.mem_iInter.mp ha₂ w)
    · rw [normAtComplexPlaces_normAtAllPlaces]
  · rintro ⟨a, ⟨ha₁, ha₂⟩, rfl⟩
    refine ⟨⟨a, ha₁, funext fun w => ?_⟩, Set.mem_iInter.mpr fun w => ?_⟩
    · obtain hw | hw := isReal_or_isComplex w
      · simpa [normAtComplexPlaces_apply_isReal ⟨w, hw⟩, normAtPlace_apply_of_isReal hw]
          using (ha₂ ⟨w, hw⟩).le
      · rw [normAtAllPlaces_apply, normAtPlace_apply_of_isComplex hw,
          normAtComplexPlaces_apply_isComplex ⟨w, hw⟩]
    · simpa [Set.mem_ofPred_eq, normAtComplexPlaces_apply_isReal] using (ha₂ w).ne'
-/
private theorem volume_eq_two_pow_mul_two_pi_pow_mul_integral_aux
    (hA : normAtAllPlaces ⁻¹' normAtAllPlaces '' A = A) :
    normAtAllPlaces '' A inter (⋂ w : {w // IsReal w}, {x | x w.1 != 0}) =
      normAtComplexPlaces '' plusPart A := by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha, rfl⟩, ha₂⟩
    refine ⟨mixedSpaceOfRealSpace (normAtAllPlaces a), ⟨?_, ?_⟩, ?_⟩
    · rw [← hA, Set.mem_preimage, normAtAllPlaces_normAtAllPlaces]
      exact Set.mem_image_of_mem normAtAllPlaces ha
    · intro w
      refine lt_of_le_of_ne' (normAtPlace_nonneg _ _) (Set.mem_iInter.mp ha₂ w)
    · rw [normAtComplexPlaces_normAtAllPlaces]
  · rintro ⟨a, ⟨ha₁, ha₂⟩, rfl⟩
    refine ⟨⟨a, ha₁, funext fun w => ?_⟩, Set.mem_iInter.mpr fun w => ?_⟩
    · obtain hw | hw := isReal_or_isComplex w
      · simpa [normAtComplexPlaces_apply_isReal ⟨w, hw⟩, normAtPlace_apply_of_isReal hw]
          using (ha₂ ⟨w, hw⟩).le
      · rw [normAtAllPlaces_apply, normAtPlace_apply_of_isComplex hw,
          normAtComplexPlaces_apply_isComplex ⟨w, hw⟩]
    · simpa [Set.mem_ofPred_eq, normAtComplexPlaces_apply_isReal] using (ha₂ w).ne'

open scoped Classical in
/--
theorem `volume_eq_two_pow_mul_two_pi_pow_mul_integral` / 定理 `volume_eq_two_pow_mul_two_pi_pow_mul_integral`

English:
theorem volume_eq_two_pow_mul_two_pi_pow_mul_integral
  statement: [NumberField K]
  proof: by
  have hA₁ (x : mixedSpace K) : x in A ↔ (fun w => ‖x.1 w‖, x.2) in A := by
    rw [← hA]
    simp_rw [Set.mem_preimage, Set.mem_image, normAtAllPlaces_norm_at_real_places]
  have hA₃ : normAtComplexPlaces ⁻¹' normAtComplexPlaces '' plusPart A = plusPart A := by
    refine subset_antisymm (fun x ⟨a, ha₁, ha₂⟩ => ⟨?_, fun w => ?_⟩) (Set.subset_preimage_image _ _)
    · rw [← hA, Set.mem_preimage, ← normAtAllPlaces_eq_of_normAtComplexPlaces_eq ha₂]
      exact Set.mem_image_of_mem normAtAllPlaces (Set.inter_subset_left ha₁)
    · have := funext_iff.mp ha₂ w
      rw [normAtComplexPlaces_apply_isReal]; rw [normAtComplexPlaces_apply_isReal] at this
      rw [← this]
      exact ha₁.2 w
  rw [volume_eq_two_pow_mul_volume_plusPart hA₁ hm]; rw [volume_eq_two_pi_pow_mul_integral hA₃
    (measurableSet_plusPart hm)]; rw [← mul_assoc]
refine congr_arg (_ * _ * ·) setLIntegral_congr ?_
  rw [← volume_eq_two_pow_mul_two_pi_pow_mul_integral_aux hA]
refine inter_ae_eq_left_of_ae_eq_univ ae_eq_univ.mpr
 Set.compl_iInter _ ▸ measure_iUnion_null_iff.mpr fun w => ?_
  rw [show {x : realSpace K | x w.1 != 0}ᶜ = {x | x w.1 = 0} by ext; simp]
  exact realSpace.volume_eq_zero w.1

中文:
定理 volume_eq_two_pow_mul_two_pi_pow_mul_integral
  结论: [数域 K]
  证明: by
  have hA₁ (x : mixedSpace K) : x in A ↔ (fun w => ‖x.1 w‖, x.2) in A := by
    rw [← hA]
    simp_rw [Set.mem_preimage, Set.mem_image, normAtAllPlaces_norm_at_real_places]
  have hA₃ : normAtComplexPlaces ⁻¹' normAtComplexPlaces '' plusPart A = plusPart A := by
    refine subset_antisymm (fun x ⟨a, ha₁, ha₂⟩ => ⟨?_, fun w => ?_⟩) (Set.subset_preimage_image _ _)
    · rw [← hA, Set.mem_preimage, ← normAtAllPlaces_eq_of_normAtComplexPlaces_eq ha₂]
      exact Set.mem_image_of_mem normAtAllPlaces (Set.inter_subset_left ha₁)
    · have := funext_iff.mp ha₂ w
      rw [normAtComplexPlaces_apply_isReal]; rw [normAtComplexPlaces_apply_isReal] at this
      rw [← this]
      exact ha₁.2 w
  rw [volume_eq_two_pow_mul_volume_plusPart hA₁ hm]; rw [volume_eq_two_pi_pow_mul_integral hA₃
    (measurableSet_plusPart hm)]; rw [← mul_assoc]
refine congr_arg (_ * _ * ·) setLIntegral_congr ?_
  rw [← volume_eq_two_pow_mul_two_pi_pow_mul_integral_aux hA]
refine inter_ae_eq_left_of_ae_eq_univ ae_eq_univ.mpr
 Set.compl_iInter _ ▸ measure_iUnion_null_iff.mpr fun w => ?_
  rw [show {x : realSpace K | x w.1 != 0}ᶜ = {x | x w.1 = 0} by ext; simp]
  exact realSpace.volume_eq_zero w.1

Depends on / 依赖: Set.inter_subset_left, Set.mem_image, Set.mem_image_of_mem, Set.mem_preimage, Set.subset_preimage_image, inter_subset_left, mem_image, mem_image_of_mem, mem_preimage, mixedSpace, normAtAllPlaces, normAtAllPlaces_eq_of_normAtComplexPlaces_eq, normAtAllPlaces_norm_at_real_places, normAtComplexPlaces, plusPart, simp_rw, subset_antisymm, subset_preimage_image
-/
theorem volume_eq_two_pow_mul_two_pi_pow_mul_integral [NumberField K]
    (hA : normAtAllPlaces ⁻¹' normAtAllPlaces '' A = A) (hm : MeasurableSet A) :
    volume A = 2 ^ nrRealPlaces K * .ofReal (2 * π) ^ nrComplexPlaces K *
      ∫⁻ x in normAtAllPlaces '' A, ∏ w : {w // IsComplex w}, ENNReal.ofReal (x w.1) := by
  have hA₁ (x : mixedSpace K) : x in A ↔ (fun w => ‖x.1 w‖, x.2) in A := by
    rw [← hA]
    simp_rw [Set.mem_preimage, Set.mem_image, normAtAllPlaces_norm_at_real_places]
  have hA₃ : normAtComplexPlaces ⁻¹' normAtComplexPlaces '' plusPart A = plusPart A := by
    refine subset_antisymm (fun x ⟨a, ha₁, ha₂⟩ => ⟨?_, fun w => ?_⟩) (Set.subset_preimage_image _ _)
    · rw [← hA, Set.mem_preimage, ← normAtAllPlaces_eq_of_normAtComplexPlaces_eq ha₂]
      exact Set.mem_image_of_mem normAtAllPlaces (Set.inter_subset_left ha₁)
    · have := funext_iff.mp ha₂ w
      rw [normAtComplexPlaces_apply_isReal]; rw [normAtComplexPlaces_apply_isReal] at this
      rw [← this]
      exact ha₁.2 w
  rw [volume_eq_two_pow_mul_volume_plusPart hA₁ hm]; rw [volume_eq_two_pi_pow_mul_integral hA₃
    (measurableSet_plusPart hm)]; rw [← mul_assoc]
refine congr_arg (_ * _ * ·) setLIntegral_congr ?_
  rw [← volume_eq_two_pow_mul_two_pi_pow_mul_integral_aux hA]
refine inter_ae_eq_left_of_ae_eq_univ ae_eq_univ.mpr
 Set.compl_iInter _ ▸ measure_iUnion_null_iff.mpr fun w => ?_
  rw [show {x : realSpace K | x w.1 != 0}ᶜ = {x | x w.1 = 0} by ext; simp]
  exact realSpace.volume_eq_zero w.1

end polarSpace

end NumberField.mixedEmbedding
