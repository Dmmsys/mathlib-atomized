/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Invariant measure on the upper half-plane

We equip the upper half-plane with a measure, defined as the restriction of the usual measure
on `ℂ` weighted by the function `1 / (im z) ^ 2`. We show that this measure is invariant under
the action of `GL(2, ℝ)`.
-/

open MeasureTheory
open scoped NNReal

public noncomputable section

namespace UpperHalfPlane

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MeasurableSpace ℍ
  body: .comap UpperHalfPlane.coe inferInstance

中文:
实例 :
  签名: 可测空间 ℍ
  定义体: .comap UpperHalfPlane.coe inferInstance

Depends on / 依赖: UpperHalfPlane, UpperHalfPlane.coe
-/
instance : MeasurableSpace ℍ := .comap UpperHalfPlane.coe inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BorelSpace ℍ
  body: ⟨borel_comap.symm⟩

中文:
实例 :
  签名: Borel空间 ℍ
  定义体: ⟨borel_comap.symm⟩

Depends on / 依赖: borel_comap, borel_comap.symm
-/
instance : BorelSpace ℍ := ⟨borel_comap.symm⟩

/--
lemma `measurableEmbedding_coe` / 引理 `measurableEmbedding_coe`

English:
lemma measurableEmbedding_coe
  statement: MeasurableEmbedding UpperHalfPlane.coe
  proof: isOpenEmbedding_coe.measurableEmbedding

@[fun_prop]

中文:
引理 measurableEmbedding_coe
  结论: 可测嵌入 UpperHalfPlane.coe
  证明: isOpenEmbedding_coe.measurableEmbedding

@[fun_prop]

Depends on / 依赖: isOpenEmbedding_coe, isOpenEmbedding_coe.measurableEmbedding, measurableEmbedding
-/
lemma measurableEmbedding_coe : MeasurableEmbedding UpperHalfPlane.coe :=
  isOpenEmbedding_coe.measurableEmbedding

@[fun_prop]
/--
lemma `measurable_coe` / 引理 `measurable_coe`

English:
lemma measurable_coe
  statement: Measurable UpperHalfPlane.coe
  proof: measurableEmbedding_coe.measurable

中文:
引理 measurable_coe
  结论: 可测 UpperHalfPlane.coe
  证明: measurableEmbedding_coe.measurable

Depends on / 依赖: measurable, measurableEmbedding_coe, measurableEmbedding_coe.measurable
-/
lemma measurable_coe : Measurable UpperHalfPlane.coe :=
  measurableEmbedding_coe.measurable

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MeasureSpace ℍ
  body: ⟨(volume.comap UpperHalfPlane.coe).withDensity
    fun z => ↑((1 / NNReal.mk z.im z.im_pos.le : Real>=0) ^ 2)⟩

中文:
实例 :
  签名: 测度空间 ℍ
  定义体: ⟨(volume.comap UpperHalfPlane.coe).withDensity
    fun z => ↑((1 / NNReal.mk z.im z.im_pos.le : Real>=0) ^ 2)⟩

Depends on / 依赖: NNReal, NNReal.mk, UpperHalfPlane, UpperHalfPlane.coe, im_pos, volume, volume.comap, withDensity, z.im, z.im_pos.le
-/
instance : MeasureSpace ℍ :=
  ⟨(volume.comap UpperHalfPlane.coe).withDensity
    fun z => ↑((1 / NNReal.mk z.im z.im_pos.le : Real>=0) ^ 2)⟩

/--
theorem `volume_def` / 定理 `volume_def`

English:
theorem volume_def
  proof: rfl

中文:
定理 volume_def
  证明: rfl
-/
theorem volume_def :
    (volume : Measure ℍ) = (volume.comap UpperHalfPlane.coe).withDensity fun z =>
      ↑((1 / NNReal.mk z.im z.im_pos.le : Real>=0) ^ 2) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFiniteMeasureOnCompacts (volume.comap UpperHalfPlane.coe)
  body: .comap' _ continuous_coe measurableEmbedding_coe

中文:
实例 :
  签名: 紧集上有限测度 (volume.comap UpperHalfPlane.coe)
  定义体: .comap' _ continuous_coe measurableEmbedding_coe

Depends on / 依赖: continuous_coe, measurableEmbedding_coe
-/
instance : IsFiniteMeasureOnCompacts (volume.comap UpperHalfPlane.coe) :=
  .comap' _ continuous_coe measurableEmbedding_coe

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocallyFiniteMeasure (volume.comap UpperHalfPlane.coe)
  body: inferInstance

中文:
实例 :
  签名: 是局部有限测度 (volume.comap UpperHalfPlane.coe)
  定义体: inferInstance
-/
instance : IsLocallyFiniteMeasure (volume.comap UpperHalfPlane.coe) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SigmaFinite (volume.comap UpperHalfPlane.coe)
  body: inferInstance

中文:
实例 :
  签名: σ有限 (volume.comap UpperHalfPlane.coe)
  定义体: inferInstance
-/
instance : SigmaFinite (volume.comap UpperHalfPlane.coe) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SFinite (volume.comap UpperHalfPlane.coe)
  body: inferInstance

中文:
实例 :
  签名: SFinite (volume.comap UpperHalfPlane.coe)
  定义体: inferInstance
-/
instance : SFinite (volume.comap UpperHalfPlane.coe) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocallyFiniteMeasure (volume : Measure ℍ)
  body: by
  refine .withDensity_coe ?_
  refine .pow (.div₀ continuous_const ?_ ?_) _
  · exact continuous_im.subtype_mk _
  · exact fun x => NNReal.ne_iff.mp x.im_ne_zero

中文:
实例 :
  签名: 是局部有限测度 (volume : 测度 ℍ)
  定义体: by
  refine .withDensity_coe ?_
  refine .pow (.div₀ continuous_const ?_ ?_) _
  · exact continuous_im.subtype_mk _
  · exact fun x => NNReal.ne_iff.mp x.im_ne_zero

Depends on / 依赖: NNReal, NNReal.ne_iff.mp, continuous_const, continuous_im, continuous_im.subtype_mk, im_ne_zero, ne_iff, subtype_mk, withDensity_coe, x.im_ne_zero
-/
instance : IsLocallyFiniteMeasure (volume : Measure ℍ) := by
  refine .withDensity_coe ?_
  refine .pow (.div₀ continuous_const ?_ ?_) _
  · exact continuous_im.subtype_mk _
  · exact fun x => NNReal.ne_iff.mp x.im_ne_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFiniteMeasureOnCompacts (volume : Measure ℍ)
  body: inferInstance

中文:
实例 :
  签名: 紧集上有限测度 (volume : 测度 ℍ)
  定义体: inferInstance
-/
instance : IsFiniteMeasureOnCompacts (volume : Measure ℍ) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SigmaFinite (volume : Measure ℍ)
  body: inferInstance

中文:
实例 :
  签名: σ有限 (volume : 测度 ℍ)
  定义体: inferInstance
-/
instance : SigmaFinite (volume : Measure ℍ) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SFinite (volume : Measure ℍ)
  body: inferInstance

中文:
实例 :
  签名: SFinite (volume : 测度 ℍ)
  定义体: inferInstance
-/
instance : SFinite (volume : Measure ℍ) := inferInstance

/--
lemma `volume_eq_lintegral` / 引理 `volume_eq_lintegral`

English:
lemma volume_eq_lintegral
  given: (s : Set ℍ)
  proof: by
  have : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (.range UpperHalfPlane.coe)) :=
    ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  rw [volume_def]; rw [withDensity_apply']; rw [← Set.inter_eq_self_of_subset_left (Set.image_subs

中文:
引理 volume_eq_lintegral
  条件: (s : 集合 ℍ)
  证明: by
  have : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (.range UpperHalfPlane.coe)) :=
    ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  rw [volume_def]; rw [withDensity_apply']; rw [← Set.inter_eq_self_of_subset_left (Set.image_subs

Depends on / 依赖: Measure, Measure.restrict_restrict, MeasurePreserving, Real.nnnorm_of_nonneg, Set.image_subset_range, Set.inter_eq_self_of_subset_left, UpperHalfPlane, UpperHalfPlane.coe, im_pos, image_subset_range, inter_eq_self_of_subset_left, map_comap, measurableEmbedding_coe, measurableEmbedding_coe.map_comap, measurableEmbedding_coe.measurableSet_range, measurableSet_range, measurable_coe, nnnorm_of_nonneg, restrict, restrict_restrict
-/
lemma volume_eq_lintegral (s : Set ℍ) :
    volume s = ∫⁻ z : Complex in (↑) '' s, ↑((1 / ‖z.im‖₊) ^ 2 : NNReal) := by
  have : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (.range UpperHalfPlane.coe)) :=
    ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  rw [volume_def]; rw [withDensity_apply']; rw [← Set.inter_eq_self_of_subset_left (Set.image_subset_range _ _)]; rw [← Measure.restrict_restrict']; rw [← this.setLIntegral_comp_emb measurableEmbedding_coe]
  · simp [Real.nnnorm_of_nonneg (im_pos _).le]
  · exact measurableEmbedding_coe.measurableSet_range

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulInvariantMeasure (GL (Fin 2) Real) ℍ volume
  body: by
  -- It suffices to show `volume (g • s) = volume s` for measurable sets `s`. First
  -- we write this as a lintegral over subsets of `ℂ`.
  refine ((smulInvariantMeasure_tfae _ _).out 2 0).mp fun g s hs => ?_
  rw [volume_eq_lintegral]; rw [volume_eq_lintegral]; rw [← Set.image_smul]; rw [Set.im

中文:
实例 :
  签名: 标量乘不变测度 (GL (有限集 2) 实数) ℍ volume
  定义体: by
  -- It suffices to show `volume (g • s) = volume s` for measurable sets `s`. First
  -- we write this as a lintegral over subsets of `ℂ`.
  refine ((smulInvariantMeasure_tfae _ _).out 2 0).mp fun g s hs => ?_
  rw [volume_eq_lintegral]; rw [volume_eq_lintegral]; rw [← Set.image_smul]; rw [Set.im
-/
instance : SMulInvariantMeasure (GL (Fin 2) Real) ℍ volume := by
  -- It suffices to show `volume (g • s) = volume s` for measurable sets `s`. First
  -- we write this as a lintegral over subsets of `ℂ`.
  refine ((smulInvariantMeasure_tfae _ _).out 2 0).mp fun g s hs => ?_
  rw [volume_eq_lintegral]; rw [volume_eq_lintegral]; rw [← Set.image_smul]; rw [Set.image_image]
  -- We want to apply the Jacobian change-of-variable formula.
  have hinj : Set.InjOn (fun z => ↑(g • ofComplex z) : Complex -> Complex) (UpperHalfPlane.coe '' s) :=
.image_of_comp by simp
  have main := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      volume (measurableEmbedding_coe.measurableSet_image.mpr hs)
      (Set.forall_mem_image.mpr fun z hz =>
        (hasStrictFDerivAt_smul g _).hasFDerivAt.hasFDerivWithinAt)
      hinj
      (fun z => ↑((1 / ‖z.im‖₊) ^ 2 : NNReal))
  convert! main using 1
  · simp [Set.image_image]
  · apply setLIntegral_congr_fun (measurableEmbedding_coe.measurableSet_image.mpr hs)
    rintro _ ⟨τ, -, rfl⟩
    simp only [← Real.enorm_eq_ofReal_abs, enorm_eq_nnnorm]
    have : ‖(SignType.sign g.val.det : Real)‖₊ = 1 := by
      rcases g.det_ne_zero.lt_or_gt with h | h <;> simp [h]
    have := g.det_ne_zero
    have := denom_ne_zero g τ
    norm_cast
    ext
    simp [det_smulFDeriv, *, im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, field]

end UpperHalfPlane

end
