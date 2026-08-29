/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Volume measure for Euclidean geometry

In this file we introduce a `d`-dimensional measure for `n`-dimensional Euclidean affine space,
namely `MeasureTheory.Measure.euclideanHausdorffMeasure d` with notation `μHE[d]`.
This is the suitable measure to describe area and volume in an environment of arbitrary dimension.
It is characterized by the following properties:

* Coincides with Lebesgue measure when `d = n`.
* Preserved through isometry, and specifically through affine subspace inclusion.

Internally, this is defined as the `MeasureTheory.Measure.hausdorffMeasure` scaled by a factor.
The factor is defined nonconstructively as the `MeasureTheory.Measure.addHaarScalarFactor` between
the Hausdorff measure and the Lebesgue measure on a model Euclidean space.

TODO: show the scaling factor equals to the ratio between the volume of `d`-dimensional
`Metric.ball` with Euclidean metric and with sup metric.

## Main definitions

* `MeasureTheory.Measure.euclideanHausdorffMeasure`: the Euclidean Hausdorff measure.

## Main statements

* `EuclideanGeometry.measurePreserving_vaddConst`: `μHE[d]` on an affine space matches volume on the
  associated inner product space.
* `AffineSubspace.euclideanHausdorffMeasure_coe_image`: `μHE[d]` is preserved through subspace
  inclusion.

## Tags

Hausdorff measure, measure, metric measure, volume, area
-/

open MeasureTheory Measure Module

public section

instance (d : Nat) : (μH[d] : Measure (EuclideanSpace Real (Fin d))).IsAddHaarMeasure := by
  simpa using MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := EuclideanSpace Real (Fin d))

variable {X Y : Type*}
variable [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/--
Euclidean Hausdorff measure `μHE[d]`, defined as `μH[d]` scaled to agree with Lebesgue measure
on a `d`-dimensional Euclidean space. While this is defined on any (e)metric space, it is intended
to be used for affine space associated with an inner product space, where it agrees with the volume
measure on the inner product space.
-/
noncomputable
/--
Definition of `MeasureTheory.Measure.euclideanHausdorffMeasure` / `MeasureTheory.Measure.euclideanHausdorffMeasure` 的定义

English:
definition MeasureTheory.Measure.euclideanHausdorffMeasure
  signature: (d : Nat)
  body: addHaarScalarFactor (volume : Measure (EuclideanSpace Real (Fin d))) μH[d] • μH[d]

@[inherit_doc]
scoped[MeasureTheory] notation "μHE[" d "]" => MeasureTheory.Measure.euclideanHausdorffMeasure d

中文:
定义 MeasureTheory.Measure.euclideanHausdorffMeasure
  签名: (d : 自然数)
  定义体: addHaarScalarFactor (volume : Measure (EuclideanSpace Real (Fin d))) μH[d] • μH[d]

@[inherit_doc]
scoped[MeasureTheory] notation "μHE[" d "]" => MeasureTheory.Measure.euclideanHausdorffMeasure d

Depends on / 依赖: EuclideanSpace, Measure, addHaarScalarFactor, volume
-/
def MeasureTheory.Measure.euclideanHausdorffMeasure (d : Nat) : Measure X :=
  addHaarScalarFactor (volume : Measure (EuclideanSpace Real (Fin d))) μH[d] • μH[d]

@[inherit_doc]
scoped[MeasureTheory] notation "μHE[" d "]" => MeasureTheory.Measure.euclideanHausdorffMeasure d

/-- show the scaling factor equals to the ratio between the volume of `d`-dimensional
`Metric.ball` with Euclidean metric and with sup metric (i.e. a cube), or explicitly,
$\pi^{d/2} / (2^d \Gamma (d/2+1))$. -/
proof_wanted MeasureTheory.Measure.addHaarScalarFactor_hausdorffMeasure_eq (d : Nat) :
    addHaarScalarFactor (volume : Measure (EuclideanSpace Real (Fin d))) μH[d] =
    volume (Metric.ball (0 : EuclideanSpace Real (Fin d)) 1) / volume (Metric.ball (0 : Fin d -> Real) 1)

/--
theorem `MeasureTheory.Measure.euclideanHausdorffMeasure_def` / 定理 `MeasureTheory.Measure.euclideanHausdorffMeasure_def`

English:
theorem MeasureTheory.Measure.euclideanHausdorffMeasure_def
  given: (d : Nat)
  proof: by
  rfl

中文:
定理 MeasureTheory.Measure.euclideanHausdorffMeasure_def
  条件: (d : 自然数)
  证明: by
  rfl
-/
theorem MeasureTheory.Measure.euclideanHausdorffMeasure_def (d : Nat) :
    (μHE[d] : Measure X) =
    addHaarScalarFactor (volume : Measure (EuclideanSpace Real (Fin d))) μH[d] • μH[d] := by
  rfl

set_option backward.isDefEq.respectTransparency false in -- needed by simplifying `1 • _`
/-- `μHE[0]` and `μH[0]` are equal. -/
@[simp]
/--
theorem `MeasureTheory.Measure.euclideanHausdorffMeasure_zero` / 定理 `MeasureTheory.Measure.euclideanHausdorffMeasure_zero`

English:
theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero
  proof: by
  let basis : OrthonormalBasis (Fin 0) Real (EuclideanSpace Real (Fin 0)) :=
    EuclideanSpace.basisFun (Fin 0) Real
  have heq : ({0} : Set (EuclideanSpace Real (Fin 0))) = parallelepiped basis := by
    simp [parallelepiped]
  obtain h := isAddLeftInvariant_eq_smul (volume : Measure (Euclidean

中文:
定理 MeasureTheory.Measure.euclideanHausdorffMeasure_zero
  证明: by
  let basis : OrthonormalBasis (Fin 0) Real (EuclideanSpace Real (Fin 0)) :=
    EuclideanSpace.basisFun (Fin 0) Real
  have heq : ({0} : Set (EuclideanSpace Real (Fin 0))) = parallelepiped basis := by
    simp [parallelepiped]
  obtain h := isAddLeftInvariant_eq_smul (volume : Measure (Euclidean

Depends on / 依赖: CharP.cast_eq_zero, ENNReal, EuclideanSpace, EuclideanSpace.basisFun, Measure, OrthonormalBasis, OrthonormalBasis.volume_parallelepiped, basisFun, cast_eq_zero, conv_rhs, h.symm, hausdorffMeasure_zero_singleton, isAddLeftInvariant_eq_smul, parallelepiped, simp_rw, smul_apply, volume, volume_parallelepiped
-/
theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero :
    (μHE[0] : Measure X) = (μH[0] : Measure X) := by
  let basis : OrthonormalBasis (Fin 0) Real (EuclideanSpace Real (Fin 0)) :=
    EuclideanSpace.basisFun (Fin 0) Real
  have heq : ({0} : Set (EuclideanSpace Real (Fin 0))) = parallelepiped basis := by
    simp [parallelepiped]
  obtain h := isAddLeftInvariant_eq_smul (volume : Measure (EuclideanSpace Real (Fin 0))) μH[(0 : Nat)]
  obtain h := congr($h.symm {0})
  conv_rhs at h => rw [heq, OrthonormalBasis.volume_parallelepiped]
  simp_rw [CharP.cast_eq_zero, smul_apply, hausdorffMeasure_zero_singleton, ENNReal.smul_def,
    smul_eq_mul, mul_one, ENNReal.coe_eq_one] at h
  simp [euclideanHausdorffMeasure_def, h]

/--
theorem `MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero` / 定理 `MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero`

English:
theorem MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero
  given: (d : Nat)
  proof: by
  intro h0
  obtain h := isAddLeftInvariant_eq_smul (volume : Measure (EuclideanSpace Real (Fin d))) μH[d]
  obtain h := congr($h (parallelepiped (stdOrthonormalBasis Real (EuclideanSpace Real (Fin d)))))
  simp [OrthonormalBasis.volume_parallelepiped, h0] at h

中文:
定理 MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero
  条件: (d : 自然数)
  证明: by
  intro h0
  obtain h := isAddLeftInvariant_eq_smul (volume : Measure (EuclideanSpace Real (Fin d))) μH[d]
  obtain h := congr($h (parallelepiped (stdOrthonormalBasis Real (EuclideanSpace Real (Fin d)))))
  simp [OrthonormalBasis.volume_parallelepiped, h0] at h

Depends on / 依赖: EuclideanSpace, Measure, OrthonormalBasis, OrthonormalBasis.volume_parallelepiped, isAddLeftInvariant_eq_smul, parallelepiped, stdOrthonormalBasis, volume, volume_parallelepiped
-/
theorem MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (d : Nat) :
    addHaarScalarFactor (volume : Measure (EuclideanSpace Real (Fin d))) μH[d] != 0 := by
  intro h0
  obtain h := isAddLeftInvariant_eq_smul (volume : Measure (EuclideanSpace Real (Fin d))) μH[d]
  obtain h := congr($h (parallelepiped (stdOrthonormalBasis Real (EuclideanSpace Real (Fin d)))))
  simp [OrthonormalBasis.volume_parallelepiped, h0] at h

set_option backward.isDefEq.respectTransparency false in -- needed by `ENNReal.smul_def`
/--
Instance `MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure` / 实例 `MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure`

English:
instance MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure
  signature: {E : Type*}
  body: by
  rw [euclideanHausdorffMeasure_def]; rw [ENNReal.smul_def]
  exact IsAddHaarMeasure.smul _
    (by simpa using addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (Module.finrank Real E))
    (by simp)

中文:
实例 MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure
  签名: {E : 类型}
  定义体: by
  rw [euclideanHausdorffMeasure_def]; rw [ENNReal.smul_def]
  exact IsAddHaarMeasure.smul _
    (by simpa using addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (Module.finrank Real E))
    (by simp)

Depends on / 依赖: ENNReal, ENNReal.smul_def, IsAddHaarMeasure, IsAddHaarMeasure.smul, Module, Module.finrank, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, euclideanHausdorffMeasure_def, finrank, smul_def
-/
instance MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E] [MeasurableSpace E]
    [BorelSpace E] : (μHE[Module.finrank Real E] : Measure E).IsAddHaarMeasure := by
  rw [euclideanHausdorffMeasure_def]; rw [ENNReal.smul_def]
  exact IsAddHaarMeasure.smul _
    (by simpa using addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (Module.finrank Real E))
    (by simp)

set_option backward.isDefEq.respectTransparency false in -- needed by `ENNReal.smul_top`
/--
theorem `MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top` / 定理 `MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top`

English:
theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top
  statement: {d₁ d₂ : Nat} (h : d₁ < d₂)
  proof: by
  simp_rw [euclideanHausdorffMeasure_def]
  obtain h | h := hausdorffMeasure_zero_or_top (show (d₁ : Real) < d₂ by simpa using h) s
  · simp [h]
  · right
    rw [smul_apply]; rw [h]; rw [ENNReal.smul_top]
    simp [addHaarScalarFactor_volume_hausdorffMeasure_ne_zero]

中文:
定理 MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top
  结论: {d₁ d₂ : 自然数} (h : d₁ < d₂)
  证明: by
  simp_rw [euclideanHausdorffMeasure_def]
  obtain h | h := hausdorffMeasure_zero_or_top (show (d₁ : Real) < d₂ by simpa using h) s
  · simp [h]
  · right
    rw [smul_apply]; rw [h]; rw [ENNReal.smul_top]
    simp [addHaarScalarFactor_volume_hausdorffMeasure_ne_zero]

Depends on / 依赖: ENNReal, ENNReal.smul_top, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, euclideanHausdorffMeasure_def, hausdorffMeasure_zero_or_top, simp_rw, smul_apply, smul_top
-/
theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top {d₁ d₂ : Nat} (h : d₁ < d₂)
    (s : Set X) : μHE[d₂] s = 0 ∨ μHE[d₁] s = ⊤ := by
  simp_rw [euclideanHausdorffMeasure_def]
  obtain h | h := hausdorffMeasure_zero_or_top (show (d₁ : Real) < d₂ by simpa using h) s
  · simp [h]
  · right
    rw [smul_apply]; rw [h]; rw [ENNReal.smul_top]
    simp [addHaarScalarFactor_volume_hausdorffMeasure_ne_zero]


/--
theorem `IsometryEquiv.measurePreserving_euclideanHausdorffMeasure` / 定理 `IsometryEquiv.measurePreserving_euclideanHausdorffMeasure`

English:
theorem IsometryEquiv.measurePreserving_euclideanHausdorffMeasure
  given: (e : X ≃ᵢ Y) (d : Nat)
  proof: (IsometryEquiv.measurePreserving_hausdorffMeasure e d).smul_measure _

中文:
定理 IsometryEquiv.measurePreserving_euclideanHausdorffMeasure
  条件: (e : X ≃ᵢ Y) (d : 自然数)
  证明: (IsometryEquiv.measurePreserving_hausdorffMeasure e d).smul_measure _

Depends on / 依赖: IsometryEquiv, IsometryEquiv.measurePreserving_hausdorffMeasure, measurePreserving_hausdorffMeasure, smul_measure
-/
theorem IsometryEquiv.measurePreserving_euclideanHausdorffMeasure (e : X ≃ᵢ Y) (d : Nat) :
    MeasurePreserving e μHE[d] μHE[d] :=
  (IsometryEquiv.measurePreserving_hausdorffMeasure e d).smul_measure _

/--
theorem `Isometry.euclideanHausdorffMeasure_image` / 定理 `Isometry.euclideanHausdorffMeasure_image`

English:
theorem Isometry.euclideanHausdorffMeasure_image
  given: {f : X -> Y} {d : Nat} (hf : Isometry f) (s : Set X)
  proof: by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [Isometry.hausdorffMeasure_image hf (by simp)]

中文:
定理 Isometry.euclideanHausdorffMeasure_image
  条件: {f : X -> Y} {d : 自然数} (hf : Isometry f) (s : Set X)
  证明: by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [Isometry.hausdorffMeasure_image hf (by simp)]

Depends on / 依赖: Isometry, Isometry.hausdorffMeasure_image, Measure, Measure.smul_apply, euclideanHausdorffMeasure_def, hausdorffMeasure_image, simp_rw, smul_apply
-/
theorem Isometry.euclideanHausdorffMeasure_image {f : X -> Y} {d : Nat} (hf : Isometry f) (s : Set X) :
    μHE[d] (f '' s) = μHE[d] s := by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [Isometry.hausdorffMeasure_image hf (by simp)]

/--
theorem `Isometry.euclideanHausdorffMeasure_preimage` / 定理 `Isometry.euclideanHausdorffMeasure_preimage`

English:
theorem Isometry.euclideanHausdorffMeasure_preimage
  statement: {f : X -> Y} {d : Nat} (hf : Isometry f)
  proof: by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [Isometry.hausdorffMeasure_preimage hf (by simp)]

中文:
定理 Isometry.euclideanHausdorffMeasure_preimage
  结论: {f : X -> Y} {d : 自然数} (hf : Isometry f)
  证明: by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [Isometry.hausdorffMeasure_preimage hf (by simp)]

Depends on / 依赖: Isometry, Isometry.hausdorffMeasure_preimage, Measure, Measure.smul_apply, euclideanHausdorffMeasure_def, hausdorffMeasure_preimage, simp_rw, smul_apply
-/
theorem Isometry.euclideanHausdorffMeasure_preimage {f : X -> Y} {d : Nat} (hf : Isometry f)
    (s : Set Y) : μHE[d] (f ⁻¹' s) = μHE[d] (s inter Set.range f) := by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [Isometry.hausdorffMeasure_preimage hf (by simp)]

/--
theorem `Isometry.map_euclideanHausdorffMeasure` / 定理 `Isometry.map_euclideanHausdorffMeasure`

English:
theorem Isometry.map_euclideanHausdorffMeasure
  given: {f : X -> Y} {d : Nat} (hf : Isometry f)
  proof: by
  simp_rw [euclideanHausdorffMeasure_def]
  rw [Measure.map_smul]; rw [map_hausdorffMeasure hf (by simp)]; rw [Measure.restrict_smul]

中文:
定理 Isometry.map_euclideanHausdorffMeasure
  条件: {f : X -> Y} {d : 自然数} (hf : Isometry f)
  证明: by
  simp_rw [euclideanHausdorffMeasure_def]
  rw [Measure.map_smul]; rw [map_hausdorffMeasure hf (by simp)]; rw [Measure.restrict_smul]

Depends on / 依赖: Measure, Measure.map_smul, Measure.restrict_smul, euclideanHausdorffMeasure_def, map_hausdorffMeasure, map_smul, restrict_smul, simp_rw
-/
theorem Isometry.map_euclideanHausdorffMeasure {f : X -> Y} {d : Nat} (hf : Isometry f) :
    μHE[d].map f = μHE[d].restrict (Set.range f) := by
  simp_rw [euclideanHausdorffMeasure_def]
  rw [Measure.map_smul]; rw [map_hausdorffMeasure hf (by simp)]; rw [Measure.restrict_smul]

/-!
### Applying scalers to `μHE[d]`
-/

open scoped Pointwise in
/--
theorem `MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀` / 定理 `MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀`

English:
theorem MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀
  statement: {𝕜 : Type*} {E : Type*}
  proof: by
  rw [euclideanHausdorffMeasure_def]; rw [Measure.smul_apply]; rw [hausdorffMeasure_smul₀ (by simp) hr]; rw [Measure.smul_apply]; rw [smul_comm]
  simp

中文:
定理 MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀
  结论: {𝕜 : 类型} {E : 类型}
  证明: by
  rw [euclideanHausdorffMeasure_def]; rw [Measure.smul_apply]; rw [hausdorffMeasure_smul₀ (by simp) hr]; rw [Measure.smul_apply]; rw [smul_comm]
  simp

Depends on / 依赖: Measure, Measure.smul_apply, euclideanHausdorffMeasure_def, smul_apply, smul_comm
-/
theorem MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀ {𝕜 : Type*} {E : Type*}
    [NormedAddCommGroup E] [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    [MeasurableSpace E] [BorelSpace E] (d : Nat) {r : 𝕜} (hr : r != 0) (s : Set E) :
    μHE[d] (r • s) = ‖r‖₊ ^ d • μHE[d] s := by
  rw [euclideanHausdorffMeasure_def]; rw [Measure.smul_apply]; rw [hausdorffMeasure_smul₀ (by simp) hr]; rw [Measure.smul_apply]; rw [smul_comm]
  simp

section Homothety
variable {𝕜 V P : Type*} [NormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [MeasurableSpace P] [MetricSpace P] [NormedAddTorsor V P] [BorelSpace P]

/--
theorem `MeasureTheory.euclideanHausdorffMeasure_homothety_image` / 定理 `MeasureTheory.euclideanHausdorffMeasure_homothety_image`

English:
theorem MeasureTheory.euclideanHausdorffMeasure_homothety_image
  statement: (d : Nat) (x : P) {c : 𝕜}
  proof: by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [hausdorffMeasure_homothety_image (by simp) x hc]; rw [smul_comm]; rw [NNReal.rpow_natCast]

中文:
定理 MeasureTheory.euclideanHausdorffMeasure_homothety_image
  结论: (d : 自然数) (x : P) {c : 𝕜}
  证明: by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [hausdorffMeasure_homothety_image (by simp) x hc]; rw [smul_comm]; rw [NNReal.rpow_natCast]

Depends on / 依赖: Measure, Measure.smul_apply, NNReal, NNReal.rpow_natCast, euclideanHausdorffMeasure_def, hausdorffMeasure_homothety_image, rpow_natCast, simp_rw, smul_apply, smul_comm
-/
theorem MeasureTheory.euclideanHausdorffMeasure_homothety_image (d : Nat) (x : P) {c : 𝕜}
    (hc : c != 0) (s : Set P) :
    μHE[d] (AffineMap.homothety x c '' s) = ‖c‖₊ ^ d • μHE[d] s := by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [hausdorffMeasure_homothety_image (by simp) x hc]; rw [smul_comm]; rw [NNReal.rpow_natCast]

/--
theorem `MeasureTheory.euclideanHausdorffMeasure_homothety_preimage` / 定理 `MeasureTheory.euclideanHausdorffMeasure_homothety_preimage`

English:
theorem MeasureTheory.euclideanHausdorffMeasure_homothety_preimage
  statement: (d : Nat) (x : P) {c : 𝕜}
  proof: by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [hausdorffMeasure_homothety_preimage (by simp) x hc]; rw [smul_comm]; rw [NNReal.rpow_natCast]

中文:
定理 MeasureTheory.euclideanHausdorffMeasure_homothety_preimage
  结论: (d : 自然数) (x : P) {c : 𝕜}
  证明: by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [hausdorffMeasure_homothety_preimage (by simp) x hc]; rw [smul_comm]; rw [NNReal.rpow_natCast]

Depends on / 依赖: Measure, Measure.smul_apply, NNReal, NNReal.rpow_natCast, euclideanHausdorffMeasure_def, hausdorffMeasure_homothety_preimage, rpow_natCast, simp_rw, smul_apply, smul_comm
-/
theorem MeasureTheory.euclideanHausdorffMeasure_homothety_preimage (d : Nat) (x : P) {c : 𝕜}
    (hc : c != 0) (s : Set P) :
    μHE[d] (AffineMap.homothety x c ⁻¹' s) = ‖c‖₊⁻¹ ^ d • μHE[d] s := by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [hausdorffMeasure_homothety_preimage (by simp) x hc]; rw [smul_comm]; rw [NNReal.rpow_natCast]

end Homothety

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace Real V] [MeasurableSpace V] [BorelSpace V]
variable [FiniteDimensional Real V]
variable [MetricSpace P] [MeasurableSpace P] [BorelSpace P] [NormedAddTorsor V P]


/--
theorem `EuclideanSpace.euclideanHausdorffMeasure_eq_volume` / 定理 `EuclideanSpace.euclideanHausdorffMeasure_eq_volume`

English:
theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume
  given: (d : Nat)
  proof: by
  rw [euclideanHausdorffMeasure_def]; rw [← isAddLeftInvariant_eq_smul]

中文:
定理 EuclideanSpace.euclideanHausdorffMeasure_eq_volume
  条件: (d : 自然数)
  证明: by
  rw [euclideanHausdorffMeasure_def]; rw [← isAddLeftInvariant_eq_smul]

Depends on / 依赖: euclideanHausdorffMeasure_def, isAddLeftInvariant_eq_smul
-/
theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume (d : Nat) :
    (μHE[d] : Measure (EuclideanSpace Real (Fin d))) = volume := by
  rw [euclideanHausdorffMeasure_def]; rw [← isAddLeftInvariant_eq_smul]

/--
theorem `InnerProductSpace.euclideanHausdorffMeasure_eq_volume` / 定理 `InnerProductSpace.euclideanHausdorffMeasure_eq_volume`

English:
theorem InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  proof: by
  rw [← (stdOrthonormalBasis Real V).measurePreserving_repr_symm.map_eq]; rw [← (stdOrthonormalBasis Real V).repr.toIsometryEquiv
.map_eq]; rw [.symm.measurePreserving_euclideanHausdorffMeasure _
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  simp

中文:
定理 InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  证明: by
  rw [← (stdOrthonormalBasis Real V).measurePreserving_repr_symm.map_eq]; rw [← (stdOrthonormalBasis Real V).repr.toIsometryEquiv
.map_eq]; rw [.symm.measurePreserving_euclideanHausdorffMeasure _
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  simp

Depends on / 依赖: EuclideanSpace, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, euclideanHausdorffMeasure_eq_volume, map_eq, measurePreserving_euclideanHausdorffMeasure, measurePreserving_repr_symm, measurePreserving_repr_symm.map_eq, repr.toIsometryEquiv, stdOrthonormalBasis, symm.measurePreserving_euclideanHausdorffMeasure, toIsometryEquiv
-/
theorem InnerProductSpace.euclideanHausdorffMeasure_eq_volume :
    (μHE[finrank Real V] : Measure V) = volume := by
  rw [← (stdOrthonormalBasis Real V).measurePreserving_repr_symm.map_eq]; rw [← (stdOrthonormalBasis Real V).repr.toIsometryEquiv
.map_eq]; rw [.symm.measurePreserving_euclideanHausdorffMeasure _
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  simp

/-!
### `μHE[d]` on an affine space matches the volume measure on the associated inner product space.
-/
/--
theorem `EuclideanGeometry.euclideanHausdorffMeasure_eq` / 定理 `EuclideanGeometry.euclideanHausdorffMeasure_eq`

English:
theorem EuclideanGeometry.euclideanHausdorffMeasure_eq
  given: (p : P)
  proof: by
  have h := (IsometryEquiv.vaddConst p)
.map_eq .measurePreserving_euclideanHausdorffMeasure (finrank Real V)
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
  exact h.symm

中文:
定理 EuclideanGeometry.euclideanHausdorffMeasure_eq
  条件: (p : P)
  证明: by
  have h := (IsometryEquiv.vaddConst p)
.map_eq .measurePreserving_euclideanHausdorffMeasure (finrank Real V)
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
  exact h.symm

Depends on / 依赖: InnerProductSpace, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, IsometryEquiv, IsometryEquiv.vaddConst, euclideanHausdorffMeasure_eq_volume, finrank, h.symm, map_eq, measurePreserving_euclideanHausdorffMeasure, vaddConst
-/
theorem EuclideanGeometry.euclideanHausdorffMeasure_eq (p : P) :
    μHE[finrank Real V] = volume.map (IsometryEquiv.vaddConst p) := by
  have h := (IsometryEquiv.vaddConst p)
.map_eq .measurePreserving_euclideanHausdorffMeasure (finrank Real V)
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
  exact h.symm

/--
theorem `EuclideanGeometry.measurePreserving_vaddConst` / 定理 `EuclideanGeometry.measurePreserving_vaddConst`

English:
theorem EuclideanGeometry.measurePreserving_vaddConst
  given: (p : P)
  proof: (IsometryEquiv.vaddConst p).toHomeomorph.measurable
  map_eq := (euclideanHausdorffMeasure_eq p).symm

中文:
定理 EuclideanGeometry.measurePreserving_vaddConst
  条件: (p : P)
  证明: (IsometryEquiv.vaddConst p).toHomeomorph.measurable
  map_eq := (euclideanHausdorffMeasure_eq p).symm

Depends on / 依赖: IsometryEquiv, IsometryEquiv.vaddConst, measurable, toHomeomorph, toHomeomorph.measurable, vaddConst
-/
theorem EuclideanGeometry.measurePreserving_vaddConst (p : P) :
    MeasurePreserving (IsometryEquiv.vaddConst p) volume μHE[finrank Real V] where
  measurable := (IsometryEquiv.vaddConst p).toHomeomorph.measurable
  map_eq := (euclideanHausdorffMeasure_eq p).symm

open EuclideanGeometry

/-!
### `μHE[d]` is preserved through subspace inclusion
-/

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional Real V] in
/--
theorem `AffineSubspace.euclideanHausdorffMeasure_coe_image` / 定理 `AffineSubspace.euclideanHausdorffMeasure_coe_image`

English:
theorem AffineSubspace.euclideanHausdorffMeasure_coe_image
  statement: (d : Nat) (s : AffineSubspace Real P)
  proof: isometry_subtype_coe.euclideanHausdorffMeasure_image _

中文:
定理 AffineSubspace.euclideanHausdorffMeasure_coe_image
  结论: (d : 自然数) (s : AffineSubspace 实数 P)
  证明: isometry_subtype_coe.euclideanHausdorffMeasure_image _

Depends on / 依赖: euclideanHausdorffMeasure_image, isometry_subtype_coe, isometry_subtype_coe.euclideanHausdorffMeasure_image
-/
theorem AffineSubspace.euclideanHausdorffMeasure_coe_image (d : Nat) (s : AffineSubspace Real P)
    (t : Set s) : μHE[d] (Subtype.val '' t) = μHE[d] t :=
  isometry_subtype_coe.euclideanHausdorffMeasure_image _

/-!
### `μHE[d]` is translation invariant
-/

instance {α : Type*} [AddGroup α] [AddAction α X] [IsIsometricVAdd α X] (d : Nat) :
    VAddInvariantMeasure α X μHE[d] := by
  rw [euclideanHausdorffMeasure_def]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroup
  signature: X] [IsIsometricVAdd X X] (d
  body: by
  rw [euclideanHausdorffMeasure_def]
  infer_instance

中文:
实例 [AddGroup
  签名: X] [IsIsometricVAdd X X] (d
  定义体: by
  rw [euclideanHausdorffMeasure_def]
  infer_instance

Depends on / 依赖: euclideanHausdorffMeasure_def, infer_instance
-/
instance [AddGroup X] [IsIsometricVAdd X X] (d : Nat) :
    (μHE[d] : Measure X).IsAddLeftInvariant := by
  rw [euclideanHausdorffMeasure_def]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroup
  signature: X] [IsIsometricVAdd Xᵃᵒᵖ X] (d
  body: by
  rw [euclideanHausdorffMeasure_def]
  infer_instance

中文:
实例 [AddGroup
  签名: X] [IsIsometricVAdd Xᵃᵒᵖ X] (d
  定义体: by
  rw [euclideanHausdorffMeasure_def]
  infer_instance

Depends on / 依赖: euclideanHausdorffMeasure_def, infer_instance
-/
instance [AddGroup X] [IsIsometricVAdd Xᵃᵒᵖ X] (d : Nat) :
    (μHE[d] : Measure X).IsAddRightInvariant := by
  rw [euclideanHausdorffMeasure_def]
  infer_instance

/-!
### Integration formula for `μHE[d]`
-/

/--
Definition of `Submodule.measurableEquivProd` / `Submodule.measurableEquivProd` 的定义

English:
definition Submodule.measurableEquivProd
  signature: (s : Submodule Real V) (p : P)
  body: (IsometryEquiv.vaddConst p).toHomeomorph.toMeasurableEquiv.symm.trans
s.orthogonalDecomposition.toHomeomorph.toMeasurableEquiv.trans
  (MeasurableEquiv.toLp 2 _).symm

@[simp]

中文:
定义 Submodule.measurableEquivProd
  签名: (s : Submodule 实数 V) (p : P)
  定义体: (IsometryEquiv.vaddConst p).toHomeomorph.toMeasurableEquiv.symm.trans
s.orthogonalDecomposition.toHomeomorph.toMeasurableEquiv.trans
  (MeasurableEquiv.toLp 2 _).symm

@[simp]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.vaddConst, MeasurableEquiv, MeasurableEquiv.toLp, orthogonalDecomposition, s.orthogonalDecomposition.toHomeomorph.toMeasurableEquiv.trans, toHomeomorph, toHomeomorph.toMeasurableEquiv.symm.trans, toMeasurableEquiv, vaddConst
-/
noncomputable def Submodule.measurableEquivProd (s : Submodule Real V) (p : P) : P ≃ᵐ s × sᗮ :=
(IsometryEquiv.vaddConst p).toHomeomorph.toMeasurableEquiv.symm.trans
s.orthogonalDecomposition.toHomeomorph.toMeasurableEquiv.trans
  (MeasurableEquiv.toLp 2 _).symm

@[simp]
/--
theorem `Submodule.measurableEquivProd_apply` / 定理 `Submodule.measurableEquivProd_apply`

English:
theorem Submodule.measurableEquivProd_apply
  given: (s : Submodule Real V) (p q : P)
  proof: by
  simp [measurableEquivProd]

@[simp]

中文:
定理 Submodule.measurableEquivProd_apply
  条件: (s : Submodule 实数 V) (p q : P)
  证明: by
  simp [measurableEquivProd]

@[simp]

Depends on / 依赖: measurableEquivProd
-/
theorem Submodule.measurableEquivProd_apply (s : Submodule Real V) (p q : P) :
    s.measurableEquivProd p q =
    (s.orthogonalProjectionOnto (q -ᵥ p), sᗮ.orthogonalProjectionOnto (q -ᵥ p)) := by
  simp [measurableEquivProd]

@[simp]
/--
theorem `Submodule.measurableEquivProd_symm_apply` / 定理 `Submodule.measurableEquivProd_symm_apply`

English:
theorem Submodule.measurableEquivProd_symm_apply
  given: (s : Submodule Real V) (p : P) (q : s × sᗮ)
  proof: by
  simp [measurableEquivProd]

中文:
定理 Submodule.measurableEquivProd_symm_apply
  条件: (s : Submodule 实数 V) (p : P) (q : s × sᗮ)
  证明: by
  simp [measurableEquivProd]

Depends on / 依赖: measurableEquivProd
-/
theorem Submodule.measurableEquivProd_symm_apply (s : Submodule Real V) (p : P) (q : s × sᗮ) :
    (s.measurableEquivProd p).symm q = (q.1.val + q.2.val) +ᵥ p := by
  simp [measurableEquivProd]

/--
theorem `Submodule.measurePreserving_measurableEquivProd` / 定理 `Submodule.measurePreserving_measurableEquivProd`

English:
theorem Submodule.measurePreserving_measurableEquivProd
  given: (s : Submodule Real V) (p : P)
  proof: by
  refine (measurePreserving_vaddConst _).symm.trans ?_
  refine s.orthogonalDecomposition.measurePreserving.trans ?_
  exact WithLp.volume_preserving_ofLp _ _

中文:
定理 Submodule.measurePreserving_measurableEquivProd
  条件: (s : Submodule 实数 V) (p : P)
  证明: by
  refine (measurePreserving_vaddConst _).symm.trans ?_
  refine s.orthogonalDecomposition.measurePreserving.trans ?_
  exact WithLp.volume_preserving_ofLp _ _

Depends on / 依赖: WithLp, WithLp.volume_preserving_ofLp, measurePreserving, measurePreserving_vaddConst, orthogonalDecomposition, s.orthogonalDecomposition.measurePreserving.trans, symm.trans, volume_preserving_ofLp
-/
theorem Submodule.measurePreserving_measurableEquivProd (s : Submodule Real V) (p : P) :
    MeasurePreserving (s.measurableEquivProd p) μHE[finrank Real V] := by
  refine (measurePreserving_vaddConst _).symm.trans ?_
  refine s.orthogonalDecomposition.measurePreserving.trans ?_
  exact WithLp.volume_preserving_ofLp _ _

/--
theorem `AffineSubspace.euclideanHausdorffMeasure_eq_lintegral` / 定理 `AffineSubspace.euclideanHausdorffMeasure_eq_lintegral`

English:
theorem AffineSubspace.euclideanHausdorffMeasure_eq_lintegral
  statement: (s : AffineSubspace Real P)
  proof: by
  obtain p := hs.some
  rw [← (s.direction.measurePreserving_measurableEquivProd p.val).symm.measure_preimage_equiv]; rw [volume_eq_prod]; rw [prod_apply (by measurability)]; rw [euclideanHausdorffMeasure_eq]; rw [MeasurableEmbedding.lintegral_map
        (by simpa using (IsometryEquiv.vaddConst 

中文:
定理 AffineSubspace.euclideanHausdorffMeasure_eq_lintegral
  结论: (s : AffineSubspace 实数 P)
  证明: by
  obtain p := hs.some
  rw [← (s.direction.measurePreserving_measurableEquivProd p.val).symm.measure_preimage_equiv]; rw [volume_eq_prod]; rw [prod_apply (by measurability)]; rw [euclideanHausdorffMeasure_eq]; rw [MeasurableEmbedding.lintegral_map
        (by simpa using (IsometryEquiv.vaddConst 

Depends on / 依赖: IsometryEquiv, IsometryEquiv.vaddConst, MeasurableEmbedding, MeasurableEmbedding.lintegral_map, MeasurableSet, Subtype, Subtype.val, closed_of_finiteDi, direction, euclideanHausdorffMeasure_eq, hs.some, ht.inter, lintegral_map, measurability, measurableEmbedding, measurePreserving_measurableEquivProd, measure_preimage_equiv, p.val, prod_apply, s.direction
-/
theorem AffineSubspace.euclideanHausdorffMeasure_eq_lintegral (s : AffineSubspace Real P)
    [hs : Nonempty s] {t : Set P} (ht : MeasurableSet t) :
    μHE[finrank Real V] t = ∫⁻ (x : s), μHE[finrank Real s.directionᗮ] (t inter mk' x.val s.directionᗮ)
      ∂μHE[finrank Real s.direction] := by
  obtain p := hs.some
  rw [← (s.direction.measurePreserving_measurableEquivProd p.val).symm.measure_preimage_equiv]; rw [volume_eq_prod]; rw [prod_apply (by measurability)]; rw [euclideanHausdorffMeasure_eq]; rw [MeasurableEmbedding.lintegral_map
        (by simpa using (IsometryEquiv.vaddConst p).toHomeomorph.measurableEmbedding)]
  congr with x
  let u : Set (mk' (x +ᵥ p).val s.directionᗮ) := Subtype.val ⁻¹' (t inter mk' (x +ᵥ p).val s.directionᗮ)
  have hu : MeasurableSet u :=
    (ht.inter (closed_of_finiteDimensional _).measurableSet).preimage measurable_subtype_coe
  have hinter : t inter (mk' (x +ᵥ p).val s.directionᗮ) = Subtype.val '' u := by
    ext x
    simp [u]
  have hxp : (x +ᵥ p).val in mk' (x +ᵥ p).val s.directionᗮ := by simp
  have hrank : finrank Real s.directionᗮ = finrank Real (mk' (x +ᵥ p).val s.directionᗮ).direction := by
    rw [direction_mk']
  rw [IsometryEquiv.vaddConst_apply]; rw [hinter]; rw [euclideanHausdorffMeasure_coe_image]; rw [hrank]; rw [euclideanHausdorffMeasure_eq ⟨x +ᵥ p]; rw [hxp⟩]; rw [map_apply (by fun_prop) hu]
  /- we have ⊢ volume (a : Set A) = volume (b : Set B). We'd like show a = b, but A and B are
    non-defeq subspaces!
    Lucky we have just developed euclideanHausdorffMeasure, which allows us to move the measure to
    the global vector space. -/
  simp_rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  conv_lhs => rw [← isometry_subtype_coe.euclideanHausdorffMeasure_image]
  conv_rhs => rw [← isometry_subtype_coe.euclideanHausdorffMeasure_image]
  congrm μHE[$hrank] ?_
  ext y
  simp [u, vadd_vadd, add_comm]

/--
theorem `EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral` / 定理 `EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral`

English:
theorem EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral
  statement: (p : P) {v : V} (hv : v != 0)
  proof: by
  have hrank : finrank Real (AffineSubspace.mk' p (Real ∙ v)).direction = 1 := by
    rw [AffineSubspace.direction_mk']
    apply finrank_span_singleton hv
  have hrank' : finrank Real (AffineSubspace.mk' p (Real ∙ v)).directionᗮ = finrank Real V - 1 := by
    rw [← (AffineSubspace.mk' p (Real ∙ 

中文:
定理 EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral
  结论: (p : P) {v : V} (hv : v != 0)
  证明: by
  have hrank : finrank Real (AffineSubspace.mk' p (Real ∙ v)).direction = 1 := by
    rw [AffineSubspace.direction_mk']
    apply finrank_span_singleton hv
  have hrank' : finrank Real (AffineSubspace.mk' p (Real ∙ v)).directionᗮ = finrank Real V - 1 := by
    rw [← (AffineSubspace.mk' p (Real ∙ 

Depends on / 依赖: AffineSubspace, AffineSubspace.direction_mk, AffineSubspace.mk, ContinuousLinearEquiv, ContinuousLinearEquiv.toSpanNonzeroSingleton, Nat.add_sub_cancel_left, add_sub_cancel_left, direction, direction.finrank_add_finrank_orthogonal, direction_mk, finrank, finrank_add_finrank_orthogonal, finrank_span_singleton, toSpanNonzeroSingleton
-/
theorem EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral (p : P) {v : V} (hv : v != 0)
    {t : Set P} (ht : MeasurableSet t) :
    μHE[finrank Real V] t =
      ‖v‖ₑ * ∫⁻ (x : Real), μHE[finrank Real V - 1] (t inter AffineSubspace.mk' (x • v +ᵥ p) (Real ∙ v)ᗮ) := by
  have hrank : finrank Real (AffineSubspace.mk' p (Real ∙ v)).direction = 1 := by
    rw [AffineSubspace.direction_mk']
    apply finrank_span_singleton hv
  have hrank' : finrank Real (AffineSubspace.mk' p (Real ∙ v)).directionᗮ = finrank Real V - 1 := by
    rw [← (AffineSubspace.mk' p (Real ∙ v)).direction.finrank_add_finrank_orthogonal]; rw [hrank]; rw [Nat.add_sub_cancel_left]
  let f : Real ≃L[Real] (AffineSubspace.mk' p (Real ∙ v)).direction :=
    (ContinuousLinearEquiv.toSpanNonzeroSingleton Real v hv).trans
    (ContinuousLinearEquiv.ofEq (Real ∙ v) ((AffineSubspace.mk' p (Real ∙ v)).direction) (by simp))
  have hf : MeasurableEmbedding f := f.toHomeomorph.measurableEmbedding
  let p' : AffineSubspace.mk' p (Real ∙ v) := ⟨p, by simp⟩
  let g : Real -> AffineSubspace.mk' p (Real ∙ v) := IsometryEquiv.vaddConst p' ∘ f
  have hadd : MeasurableEmbedding (IsometryEquiv.vaddConst p') :=
    (IsometryEquiv.vaddConst p').toHomeomorph.measurableEmbedding
  have hg : MeasurableEmbedding g := hadd.comp hf
  have hm : μHE[finrank Real (AffineSubspace.mk' p (Real ∙ v)).direction] =
      ‖v‖ₑ • (volume : Measure Real).map g := by
    unfold g
    rw [euclideanHausdorffMeasure_eq p']; rw [← map_map hadd.measurable hf.measurable]; rw [← Measure.map_smul]
    congr
    let v' : (AffineSubspace.mk' p (Real ∙ v)).direction := ⟨v, by simp⟩
    suffices volume = ‖v'‖ₑ • volume.map f by simpa [v']
    exact volume_eq_of_finrank_eq_one hrank (by simpa [v'] using hv)
  have hx (x : Real) : x • v +ᵥ p = g x := by rfl
  simp_rw [(AffineSubspace.mk' p (Real ∙ v)).euclideanHausdorffMeasure_eq_lintegral ht, hx,
    hm, lintegral_smul_measure, hg.lintegral_map, smul_eq_mul, hrank', AffineSubspace.direction_mk']
