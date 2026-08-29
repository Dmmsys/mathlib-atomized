/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Analytic.RadiusLiminf

/-!
# Gelfand's formula and other results on the spectrum in complex Banach algebras

This file contains results on the spectrum of elements in a complex Banach algebra, including
**Gelfand's formula** and the **Gelfand-Mazur theorem** and the fact that every element in a
complex Banach algebra has nonempty spectrum.

## Main results

* `spectrum.hasDerivAt_resolvent_const_left`: the resolvent function is differentiable on the
  resolvent set.
* `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`: Gelfand's formula for the
  spectral radius in Banach algebras over `ℂ`.
* `spectrum.nonempty`: the spectrum of any element in a complex Banach algebra is nonempty.
* `NormedRing.algEquivComplexOfComplete`: **Gelfand-Mazur theorem** For a complex
  Banach division algebra, the natural `algebraMap ℂ A` is an algebra isomorphism whose inverse
  is given by selecting the (unique) element of `spectrum ℂ a`

## Implementation notes

Note that it is important here that the complex analysis files are privately imported, since the
material proven here gets used in contexts that have nothing to do with complex analysis
(i.e. C⋆-algebras, etc).

-/

@[expose] public section

variable {𝕜 A : Type*}

open scoped NNReal Topology Ring
open Filter ENNReal

namespace spectrum

section NonTriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

/--
theorem `hasDerivAt_resolvent_const_left` / 定理 `hasDerivAt_resolvent_const_left`

English:
theorem hasDerivAt_resolvent_const_left
  given: {a : A} {k : 𝕜} (hk : k in resolventSet 𝕜 a)
  proof: by
  have H₁ : HasFDerivAt Ring.inverse _ (algebraMap 𝕜 A k - a) :=
    hasFDerivAt_ringInverse (𝕜 := 𝕜) hk.unit
  have H₂ : HasDerivAt (fun k => algebraMap 𝕜 A k - a) 1 k := by
    simpa using! (Algebra.linearMap 𝕜 A).hasDerivAt.sub_const a
  simpa [resolvent, sq, hk.unit_spec, ← Ring.inverse_unit 

中文:
定理 hasDerivAt_resolvent_const_left
  条件: {a : A} {k : 𝕜} (hk : k in resolventSet 𝕜 a)
  证明: by
  have H₁ : HasFDerivAt Ring.inverse _ (algebraMap 𝕜 A k - a) :=
    hasFDerivAt_ringInverse (𝕜 := 𝕜) hk.unit
  have H₂ : HasDerivAt (fun k => algebraMap 𝕜 A k - a) 1 k := by
    simpa using! (Algebra.linearMap 𝕜 A).hasDerivAt.sub_const a
  simpa [resolvent, sq, hk.unit_spec, ← Ring.inverse_unit 

Depends on / 依赖: Algebra, Algebra.linearMap, HasDerivAt, HasFDerivAt, Ring.inverse, Ring.inverse_unit, algebraMap, comp_hasDerivAt, hasDerivAt, hasDerivAt.sub_const, hasFDerivAt_ringInverse, hk.unit, hk.unit_spec, inverse, inverse_unit, linearMap, resolvent, sub_const, unit_spec
-/
theorem hasDerivAt_resolvent_const_left {a : A} {k : 𝕜} (hk : k in resolventSet 𝕜 a) :
    HasDerivAt (resolvent a) (-resolvent a k ^ 2) k := by
  have H₁ : HasFDerivAt Ring.inverse _ (algebraMap 𝕜 A k - a) :=
    hasFDerivAt_ringInverse (𝕜 := 𝕜) hk.unit
  have H₂ : HasDerivAt (fun k => algebraMap 𝕜 A k - a) 1 k := by
    simpa using! (Algebra.linearMap 𝕜 A).hasDerivAt.sub_const a
  simpa [resolvent, sq, hk.unit_spec, ← Ring.inverse_unit hk.unit] using! H₁.comp_hasDerivAt k H₂

@[deprecated (since := "2026-03-26")]
alias hasDerivAt_resolvent := hasDerivAt_resolvent_const_left

/--
theorem `hasFDerivAt_resolvent` / 定理 `hasFDerivAt_resolvent`

English:
theorem hasFDerivAt_resolvent
  given: {a : A} {k : 𝕜} (hk : k in resolventSet 𝕜 a)
  proof: by
  have H₁ : HasFDerivAt Ring.inverse _ (algebraMap 𝕜 A k - a) :=
    hasFDerivAt_ringInverse (𝕜 := 𝕜) hk.unit
  have H₂ : HasFDerivAt (fun a => algebraMap 𝕜 A k - a) (- .id 𝕜 A) a := by
    simpa using! (hasFDerivAt_const _ a).sub (hasFDerivAt_id a)
  simpa [resolvent_eq hk] using! H₁.comp a H₂

中文:
定理 hasFDerivAt_resolvent
  条件: {a : A} {k : 𝕜} (hk : k in resolventSet 𝕜 a)
  证明: by
  have H₁ : HasFDerivAt Ring.inverse _ (algebraMap 𝕜 A k - a) :=
    hasFDerivAt_ringInverse (𝕜 := 𝕜) hk.unit
  have H₂ : HasFDerivAt (fun a => algebraMap 𝕜 A k - a) (- .id 𝕜 A) a := by
    simpa using! (hasFDerivAt_const _ a).sub (hasFDerivAt_id a)
  simpa [resolvent_eq hk] using! H₁.comp a H₂

Depends on / 依赖: HasFDerivAt, Ring.inverse, algebraMap, hasFDerivAt_const, hasFDerivAt_id, hasFDerivAt_ringInverse, hk.unit, inverse, resolvent_eq
-/
theorem hasFDerivAt_resolvent {a : A} {k : 𝕜} (hk : k in resolventSet 𝕜 a) :
    HasFDerivAt (resolvent · k)
      (((ContinuousLinearMap.mulLeftRight 𝕜 A) (resolvent a k)) (resolvent a k)) a := by
  have H₁ : HasFDerivAt Ring.inverse _ (algebraMap 𝕜 A k - a) :=
    hasFDerivAt_ringInverse (𝕜 := 𝕜) hk.unit
  have H₂ : HasFDerivAt (fun a => algebraMap 𝕜 A k - a) (- .id 𝕜 A) a := by
    simpa using! (hasFDerivAt_const _ a).sub (hasFDerivAt_id a)
  simpa [resolvent_eq hk] using! H₁.comp a H₂

end NonTriviallyNormedField

/--
theorem `hasDerivAt_resolvent_const_right` / 定理 `hasDerivAt_resolvent_const_right`

English:
theorem hasDerivAt_resolvent_const_right
  statement: [NontriviallyNormedField 𝕜] [NontriviallyNormedField A]
  proof: by
.hasDerivAt convert! hasFDerivAt_resolvent (𝕜 := A) hk
  simp [resolvent, pow_two]

中文:
定理 hasDerivAt_resolvent_const_right
  结论: [NontriviallyNormedField 𝕜] [NontriviallyNormedField A]
  证明: by
.hasDerivAt convert! hasFDerivAt_resolvent (𝕜 := A) hk
  simp [resolvent, pow_two]

Depends on / 依赖: convert, hasDerivAt, hasFDerivAt_resolvent, pow_two, resolvent
-/
theorem hasDerivAt_resolvent_const_right [NontriviallyNormedField 𝕜] [NontriviallyNormedField A]
    [NormedAlgebra 𝕜 A] [CompleteSpace A] {a : A} {k : 𝕜} (hk : k in resolventSet 𝕜 a) :
    HasDerivAt (resolvent · k) (resolvent a k ^ 2) a := by
.hasDerivAt convert! hasFDerivAt_resolvent (𝕜 := A) hk
  simp [resolvent, pow_two]

open ENNReal in
/--
theorem `differentiableOn_inverse_one_sub_smul` / 定理 `differentiableOn_inverse_one_sub_smul`

English:
theorem differentiableOn_inverse_one_sub_smul
  statement: [NontriviallyNormedField 𝕜] [NormedRing A]
  proof: by
  intro z z_mem
  apply DifferentiableAt.differentiableWithinAt
  have hu : IsUnit (1 - z • a) := by
    refine isUnit_one_sub_smul_of_lt_inv_radius (lt_of_le_of_lt (coe_mono ?_) hr)
    simpa only [norm_toNNReal, Real.toNNReal_coe] using
      Real.toNNReal_mono (mem_closedBall_zero_iff.mp z_mem

中文:
定理 differentiableOn_inverse_one_sub_smul
  结论: [NontriviallyNormedField 𝕜] [赋范环 A]
  证明: by
  intro z z_mem
  apply DifferentiableAt.differentiableWithinAt
  have hu : IsUnit (1 - z • a) := by
    refine isUnit_one_sub_smul_of_lt_inv_radius (lt_of_le_of_lt (coe_mono ?_) hr)
    simpa only [norm_toNNReal, Real.toNNReal_coe] using
      Real.toNNReal_mono (mem_closedBall_zero_iff.mp z_mem

Depends on / 依赖: Differentiable, DifferentiableAt, DifferentiableAt.comp, DifferentiableAt.differentiableWithinAt, IsUnit, Real.toNNReal_coe, Real.toNNReal_mono, coe_mono, const_sub, differentiableAt, differentiableAt_inverse, differentiableWithinAt, differentiable_id, differentiable_id.smul_const, isUnit_one_sub_smul_of_lt_inv_radius, lt_of_le_of_lt, mem_closedBall_zero_iff, mem_closedBall_zero_iff.mp, norm_toNNReal, smul_const
-/
theorem differentiableOn_inverse_one_sub_smul [NontriviallyNormedField 𝕜] [NormedRing A]
    [NormedAlgebra 𝕜 A] [CompleteSpace A] {a : A} {r : Real>=0}
    (hr : (r : Real>=0∞) < (spectralRadius 𝕜 a)⁻¹) :
    DifferentiableOn 𝕜 (fun z : 𝕜 => (1 - z • a)⁻¹ʳ) (Metric.closedBall 0 r) := by
  intro z z_mem
  apply DifferentiableAt.differentiableWithinAt
  have hu : IsUnit (1 - z • a) := by
    refine isUnit_one_sub_smul_of_lt_inv_radius (lt_of_le_of_lt (coe_mono ?_) hr)
    simpa only [norm_toNNReal, Real.toNNReal_coe] using
      Real.toNNReal_mono (mem_closedBall_zero_iff.mp z_mem)
  have H₁ : Differentiable 𝕜 fun w : 𝕜 => 1 - w • a := (differentiable_id.smul_const a).const_sub 1
  exact DifferentiableAt.comp z (differentiableAt_inverse hu) H₁.differentiableAt

section Complex

variable [NormedRing A] [NormedAlgebra Complex A] [CompleteSpace A]

open ContinuousMultilinearMap in
/--
theorem `limsup_pow_nnnorm_pow_one_div_le_spectralRadius` / 定理 `limsup_pow_nnnorm_pow_one_div_le_spectralRadius`

English:
theorem limsup_pow_nnnorm_pow_one_div_le_spectralRadius
  given: (a : A)
  proof: by
  refine ENNReal.inv_le_inv.mp (le_of_forall_pos_nnreal_lt fun r r_pos r_lt => ?_)
  simp_rw [inv_limsup, ← one_div]
  let p : FormalMultilinearSeries Complex Complex A := fun n =>
    ContinuousMultilinearMap.mkPiRing Complex (Fin n) (a ^ n)
  suffices h : (r : Real>=0∞) <= p.radius by
    conve

中文:
定理 limsup_pow_nnnorm_pow_one_div_le_spectralRadius
  条件: (a : A)
  证明: by
  refine ENNReal.inv_le_inv.mp (le_of_forall_pos_nnreal_lt fun r r_pos r_lt => ?_)
  simp_rw [inv_limsup, ← one_div]
  let p : FormalMultilinearSeries Complex Complex A := fun n =>
    ContinuousMultilinearMap.mkPiRing Complex (Fin n) (a ^ n)
  suffices h : (r : Real>=0∞) <= p.radius by
    conve

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiRing, ENNReal, ENNReal.coe_rpow_def, ENNReal.inv_le_inv.mp, FormalMultilinearSeries, coe_rpow_def, convert, if_neg, inv_le_inv, inv_limsup, le_of_forall_pos_nnreal_lt, lt_self_iff_false, mkPiRing, norm_mkPiRing, norm_toNNReal, one_div, p.radius, p.radius_eq_liminf, r_lt
-/
theorem limsup_pow_nnnorm_pow_one_div_le_spectralRadius (a : A) :
    limsup (fun n : Nat => (‖a ^ n‖₊ : Real>=0∞) ^ (1 / n : Real)) atTop <= spectralRadius Complex a := by
  refine ENNReal.inv_le_inv.mp (le_of_forall_pos_nnreal_lt fun r r_pos r_lt => ?_)
  simp_rw [inv_limsup, ← one_div]
  let p : FormalMultilinearSeries Complex Complex A := fun n =>
    ContinuousMultilinearMap.mkPiRing Complex (Fin n) (a ^ n)
  suffices h : (r : Real>=0∞) <= p.radius by
    convert! h
    simp only [p, p.radius_eq_liminf, ← norm_toNNReal, norm_mkPiRing]
    congr
    ext n
    rw [norm_toNNReal]; rw [ENNReal.coe_rpow_def ‖a ^ n‖₊ (1 / n : Real)]; rw [if_neg]
    exact fun ha => (lt_self_iff_false _).mp
      (ha.2.trans_le (one_div_nonneg.mpr n.cast_nonneg : 0 <= (1 / n : Real)))
  have H₁ := (differentiableOn_inverse_one_sub_smul r_lt).hasFPowerSeriesOnBall r_pos
  exact ((hasFPowerSeriesOnBall_inverse_one_sub_smul Complex a).exchange_radius H₁).r_le

/--
theorem `pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` / 定理 `pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`

English:
theorem pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius
  given: (a : A)
  proof: tendsto_of_le_liminf_of_limsup_le (spectralRadius_le_liminf_pow_nnnorm_pow_one_div Complex a)
    (limsup_pow_nnnorm_pow_one_div_le_spectralRadius a)

alias gelfand_formula := pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius

中文:
定理 pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius
  条件: (a : A)
  证明: tendsto_of_le_liminf_of_limsup_le (spectralRadius_le_liminf_pow_nnnorm_pow_one_div Complex a)
    (limsup_pow_nnnorm_pow_one_div_le_spectralRadius a)

alias gelfand_formula := pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius

Depends on / 依赖: limsup_pow_nnnorm_pow_one_div_le_spectralRadius, spectralRadius_le_liminf_pow_nnnorm_pow_one_div, tendsto_of_le_liminf_of_limsup_le
-/
theorem pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a : A) :
    Tendsto (fun n : Nat => (‖a ^ n‖₊ : Real>=0∞) ^ (1 / n : Real)) atTop (𝓝 (spectralRadius Complex a)) :=
  tendsto_of_le_liminf_of_limsup_le (spectralRadius_le_liminf_pow_nnnorm_pow_one_div Complex a)
    (limsup_pow_nnnorm_pow_one_div_le_spectralRadius a)

alias gelfand_formula := pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius

/- This is the same as `pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` but for `norm`
instead of `nnnorm`. -/
/--
theorem `pow_norm_pow_one_div_tendsto_nhds_spectralRadius` / 定理 `pow_norm_pow_one_div_tendsto_nhds_spectralRadius`

English:
theorem pow_norm_pow_one_div_tendsto_nhds_spectralRadius
  given: (a : A)
  proof: by
  convert! pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a using 1
  ext1
  rw [← ofReal_rpow_of_nonneg (norm_nonneg _) _]; rw [← coe_nnnorm]; rw [coe_nnreal_eq]
  simp

中文:
定理 pow_norm_pow_one_div_tendsto_nhds_spectralRadius
  条件: (a : A)
  证明: by
  convert! pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a using 1
  ext1
  rw [← ofReal_rpow_of_nonneg (norm_nonneg _) _]; rw [← coe_nnnorm]; rw [coe_nnreal_eq]
  simp

Depends on / 依赖: coe_nnnorm, coe_nnreal_eq, convert, norm_nonneg, ofReal_rpow_of_nonneg, pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius
-/
theorem pow_norm_pow_one_div_tendsto_nhds_spectralRadius (a : A) :
    Tendsto (fun n : Nat => ENNReal.ofReal (‖a ^ n‖ ^ (1 / n : Real))) atTop
      (𝓝 (spectralRadius Complex a)) := by
  convert! pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a using 1
  ext1
  rw [← ofReal_rpow_of_nonneg (norm_nonneg _) _]; rw [← coe_nnnorm]; rw [coe_nnreal_eq]
  simp

section Nontrivial

variable [Nontrivial A]

/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  given: (a : A)
  statement: (spectrum Complex a).Nonempty
  proof: by
  /- Suppose `σ a = ∅`, then resolvent set is `ℂ`, any `(z • 1 - a)` is a unit, and `resolvent a`
    is differentiable on `ℂ`. -/
  by_contra! h
  have H₀ : resolventSet Complex a = Set.univ := by rwa [spectrum, Set.compl_empty_iff] at h
  have H₁ : Differentiable Complex fun z : Complex => reso

中文:
定理 nonempty
  条件: (a : A)
  结论: (spectrum 复形 a).非空
  证明: by
  /- Suppose `σ a = ∅`, then resolvent set is `ℂ`, any `(z • 1 - a)` is a unit, and `resolvent a`
    is differentiable on `ℂ`. -/
  by_contra! h
  have H₀ : resolventSet Complex a = Set.univ := by rwa [spectrum, Set.compl_empty_iff] at h
  have H₁ : Differentiable Complex fun z : Complex => reso
-/
protected theorem nonempty (a : A) : (spectrum Complex a).Nonempty := by
  /- Suppose `σ a = ∅`, then resolvent set is `ℂ`, any `(z • 1 - a)` is a unit, and `resolvent a`
    is differentiable on `ℂ`. -/
  by_contra! h
  have H₀ : resolventSet Complex a = Set.univ := by rwa [spectrum, Set.compl_empty_iff] at h
  have H₁ : Differentiable Complex fun z : Complex => resolvent a z := fun z =>
    hasDerivAt_resolvent_const_left (H₀.symm ▸ Set.mem_univ z : z in resolventSet Complex a)
.differentiableAt
  /- Since `resolvent a` tends to zero at infinity, by Liouville's theorem `resolvent a = 0`,
  which contradicts that `resolvent a z` is invertible. -/
have H₃ := H₁.apply_eq_of_tendsto_cocompact 0 by
    simpa [Metric.cobounded_eq_cocompact] using resolvent_tendsto_cobounded a (𝕜 := Complex)
exact not_isUnit_zero H₃ ▸ (isUnit_resolvent.mp <| H₀.symm ▸ Set.mem_univ 0)

/--
theorem `exists_nnnorm_eq_spectralRadius` / 定理 `exists_nnnorm_eq_spectralRadius`

English:
theorem exists_nnnorm_eq_spectralRadius
  given: (a : A)
  proof: exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty a)

中文:
定理 存在_nnnorm_eq_spectralRadius
  条件: (a : A)
  证明: exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty a)

Depends on / 依赖: exists_nnnorm_eq_spectralRadius_of_nonempty, nonempty, spectrum, spectrum.nonempty
-/
theorem exists_nnnorm_eq_spectralRadius (a : A) :
    exists z in spectrum Complex a, (‖z‖₊ : Real>=0∞) = spectralRadius Complex a :=
  exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty a)

/--
theorem `spectralRadius_lt_of_forall_lt` / 定理 `spectralRadius_lt_of_forall_lt`

English:
theorem spectralRadius_lt_of_forall_lt
  statement: (a : A) {r : Real>=0}
  proof: spectralRadius_lt_of_forall_lt_of_nonempty (spectrum.nonempty a) hr

中文:
定理 spectralRadius_lt_of_对任意_lt
  结论: (a : A) {r : 实数>=0}
  证明: spectralRadius_lt_of_forall_lt_of_nonempty (spectrum.nonempty a) hr

Depends on / 依赖: nonempty, spectralRadius_lt_of_forall_lt_of_nonempty, spectrum, spectrum.nonempty
-/
theorem spectralRadius_lt_of_forall_lt (a : A) {r : Real>=0}
    (hr : forall z in spectrum Complex a, ‖z‖₊ < r) : spectralRadius Complex a < r :=
  spectralRadius_lt_of_forall_lt_of_nonempty (spectrum.nonempty a) hr


open Polynomial in
/--
theorem `map_polynomial_aeval` / 定理 `map_polynomial_aeval`

English:
theorem map_polynomial_aeval
  given: (a : A) (p : Complex[X])
  proof: map_polynomial_aeval_of_nonempty a p (spectrum.nonempty a)

中文:
定理 map_polynomial_aeval
  条件: (a : A) (p : 复形[X])
  证明: map_polynomial_aeval_of_nonempty a p (spectrum.nonempty a)

Depends on / 依赖: map_polynomial_aeval_of_nonempty, nonempty, spectrum, spectrum.nonempty
-/
theorem map_polynomial_aeval (a : A) (p : Complex[X]) :
    spectrum Complex (aeval a p) = (fun k => eval k p) '' spectrum Complex a :=
  map_polynomial_aeval_of_nonempty a p (spectrum.nonempty a)

open Polynomial in
/--
theorem `map_pow` / 定理 `map_pow`

English:
theorem map_pow
  given: (a : A) (n : Nat)
  proof: by
  simpa only [aeval_X_pow, eval_X_pow] using map_polynomial_aeval a (X ^ n)

中文:
定理 map_pow
  条件: (a : A) (n : 自然数)
  证明: by
  simpa only [aeval_X_pow, eval_X_pow] using map_polynomial_aeval a (X ^ n)
-/
protected theorem map_pow (a : A) (n : Nat) :
    spectrum Complex (a ^ n) = (· ^ n) '' spectrum Complex a := by
  simpa only [aeval_X_pow, eval_X_pow] using map_polynomial_aeval a (X ^ n)

end Nontrivial

omit [CompleteSpace A] in
/--
theorem `algebraMap_eq_of_mem` / 定理 `algebraMap_eq_of_mem`

English:
theorem algebraMap_eq_of_mem
  statement: (hA : forall {a : A}, IsUnit a ↔ a != 0) {a : A} {z : Complex}
  proof: by
  rwa [mem_iff, hA, Classical.not_not, sub_eq_zero] at h

中文:
定理 algebraMap_eq_of_mem
  结论: (hA : 对任意 {a : A}, 是单位 a ↔ a != 0) {a : A} {z : 复形}
  证明: by
  rwa [mem_iff, hA, Classical.not_not, sub_eq_zero] at h

Depends on / 依赖: Classical, Classical.not_not, mem_iff, not_not, sub_eq_zero
-/
theorem algebraMap_eq_of_mem (hA : forall {a : A}, IsUnit a ↔ a != 0) {a : A} {z : Complex}
    (h : z in spectrum Complex a) : algebraMap Complex A z = a := by
  rwa [mem_iff, hA, Classical.not_not, sub_eq_zero] at h

/-- **Gelfand-Mazur theorem**: For a complex Banach division algebra, the natural `algebraMap ℂ A`
is an algebra isomorphism whose inverse is given by selecting the (unique) element of
`spectrum ℂ a`. In addition, `algebraMap_isometry` guarantees this map is an isometry.

Note: because `NormedDivisionRing` requires the field `norm_mul : ∀ a b, ‖a * b‖ = ‖a‖ * ‖b‖`, we
don't use this type class and instead opt for a `NormedRing` in which the nonzero elements are
precisely the units. This allows for the application of this isomorphism in broader contexts, e.g.,
to the quotient of a complex Banach algebra by a maximal ideal. In the case when `A` is actually a
`NormedDivisionRing`, one may fill in the argument `hA` with the lemma `isUnit_iff_ne_zero`. -/
@[simps]
/--
Definition of `_root_.NormedRing.algEquivComplexOfComplete` / `_root_.NormedRing.algEquivComplexOfComplete` 的定义

English:
definition _root_.NormedRing.algEquivComplexOfComplete
  signature: (hA : forall {a : A}, IsUnit a ↔ a != 0)
  body: let nt : Nontrivial A := ⟨⟨1, 0, hA.mp ⟨⟨1, 1, mul_one _, mul_one _⟩, rfl⟩⟩⟩
  { Algebra.ofId Complex A with
    toFun := algebraMap Complex A
    invFun := fun a => (@spectrum.nonempty _ _ _ _ nt a).some
    left_inv := fun z => by
      simpa only [@scalar_eq _ _ _ _ _ nt _] using!
        (@spect

中文:
定义 _root_.赋范环.algEquivComplexOfComplete
  签名: (hA : 对任意 {a : A}, 是单位 a ↔ a != 0)
  定义体: let nt : Nontrivial A := ⟨⟨1, 0, hA.mp ⟨⟨1, 1, mul_one _, mul_one _⟩, rfl⟩⟩⟩
  { Algebra.ofId Complex A with
    toFun := algebraMap Complex A
    invFun := fun a => (@spectrum.nonempty _ _ _ _ nt a).some
    left_inv := fun z => by
      simpa only [@scalar_eq _ _ _ _ _ nt _] using!
        (@spect

Depends on / 依赖: Algebra, Algebra.ofId, Nontrivial, algebraMap, algebraMap_eq_of_mem, hA.mp, invFun, left_inv, mul_one, nonempty, right_inv, scalar_eq, some_mem, spectrum, spectrum.nonempty
-/
noncomputable def _root_.NormedRing.algEquivComplexOfComplete (hA : forall {a : A}, IsUnit a ↔ a != 0) :
    Complex ≃ₐ[Complex] A :=
  let nt : Nontrivial A := ⟨⟨1, 0, hA.mp ⟨⟨1, 1, mul_one _, mul_one _⟩, rfl⟩⟩⟩
  { Algebra.ofId Complex A with
    toFun := algebraMap Complex A
    invFun := fun a => (@spectrum.nonempty _ _ _ _ nt a).some
    left_inv := fun z => by
      simpa only [@scalar_eq _ _ _ _ _ nt _] using!
        (@spectrum.nonempty _ _ _ _ nt <| algebraMap Complex A z).some_mem
    right_inv := fun a => algebraMap_eq_of_mem (@hA) (@spectrum.nonempty _ _ _ _ nt a).some_mem }

end Complex

end spectrum
