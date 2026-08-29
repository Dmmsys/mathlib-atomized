/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Algebra.Star.StarAlgHom

/-! # Spectral properties in C⋆-algebras

In this file, we establish various properties related to the spectrum of elements in C⋆-algebras.
In particular, we show that the spectrum of a unitary element is contained in the unit circle in
`ℂ`, the spectrum of a selfadjoint element is real, the spectral radius of a selfadjoint element
or normal element is its norm, among others.

An essential feature of C⋆-algebras is **spectral permanence**. This is the property that the
spectrum of an element in a closed subalgebra is the same as the spectrum of the element in the
whole algebra. For Banach algebras more generally, and even for Banach ⋆-algebras, this fails.

A consequence of spectral permanence is that one may always enlarge the C⋆-algebra (via a unital
embedding) while preserving the spectrum of any element. In addition, it allows us to make sense of
the spectrum of elements in non-unital C⋆-algebras by considering them as elements in the
`Unitization` of the C⋆-algebra, or indeed *any* unital C⋆-algebra. Of course, one may do this
(that is, consider the spectrum of an element in a non-unital by embedding it in a unital algebra)
for any Banach algebra, but the downside in that setting is that embedding in different unital
algebras results in varying spectra.

In Mathlib, we don't *define* the spectrum of an element in a non-unital C⋆-algebra, and instead
simply consider the `quasispectrum` so as to avoid depending on a choice of unital algebra. However,
we can still establish a form of spectral permanence.

## Main statements

+ `Unitary.spectrum_subset_circle`: The spectrum of a unitary element is contained in the unit
  sphere in `ℂ`.
+ `IsSelfAdjoint.spectralRadius_eq_nnnorm`: The spectral radius of a selfadjoint element is equal
  to its norm.
+ `IsStarNormal.spectralRadius_eq_nnnorm`: The spectral radius of a normal element is equal to
  its norm.
+ `spectralRadius_toReal_star_self_mul_self_eq_normSq`: The spectral radius of `a⋆ * a` is equal to
  the square of the norm of `a`.
+ `IsSelfAdjoint.mem_spectrum_eq_re`: Any element of the spectrum of a selfadjoint element is real.
* `StarSubalgebra.coe_isUnit`: for `x : S` in a C⋆-Subalgebra `S` of `A`, then `↑x : A` is a Unit
  if and only if `x` is a unit.
* `StarSubalgebra.spectrum_eq`: **spectral permanence** for `x : S`, where `S` is a C⋆-Subalgebra
  of `A`, `spectrum ℂ x = spectrum ℂ (x : A)`.

## TODO

+ prove a variation of spectral permanence using `StarAlgHom` instead of `StarSubalgebra`.
+ prove a variation of spectral permanence for `quasispectrum`.

-/

public section


local notation "σ" => spectrum
local postfix:max "⋆" => star

section

open scoped Topology ENNReal

open Filter ENNReal spectrum CStarRing NormedSpace

section UnitarySpectrum

variable {𝕜 : Type*} [NormedField 𝕜] {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]
  [NormedAlgebra 𝕜 E] [CompleteSpace E]

/--
theorem `Unitary.spectrum_subset_circle` / 定理 `Unitary.spectrum_subset_circle`

English:
theorem Unitary.spectrum_subset_circle
  given: (u : unitary E)
  proof: by
  nontriviality E
  refine fun k hk => mem_sphere_zero_iff_norm.mpr (le_antisymm ?_ ?_)
  · simpa only [CStarRing.norm_coe_unitary u] using norm_le_norm_of_mem hk
  · rw [← Unitary.val_toUnits_apply u] at hk
    have hnk := ne_zero_of_mem_of_unit hk
    rw [← inv_inv (Unitary.toUnits u)]; rw [← s

中文:
定理 Unitary.spectrum_subset_circle
  条件: (u : unitary E)
  证明: by
  nontriviality E
  refine fun k hk => mem_sphere_zero_iff_norm.mpr (le_antisymm ?_ ?_)
  · simpa only [CStarRing.norm_coe_unitary u] using norm_le_norm_of_mem hk
  · rw [← Unitary.val_toUnits_apply u] at hk
    have hnk := ne_zero_of_mem_of_unit hk
    rw [← inv_inv (Unitary.toUnits u)]; rw [← s

Depends on / 依赖: CStarRing, CStarRing.norm_coe_unitary, Set.mem_inv, Unitary, Unitary.toUnits, Unitary.val_toUnits_apply, inv_inv, le_antisymm, map_inv, mem_inv, mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm.mpr, ne_zero_of_mem_of_unit, nontriviality, norm_coe_unitary, norm_inv, norm_le_norm_of_mem, norm_pos_iff, norm_pos_iff.mpr, spectrum
-/
theorem Unitary.spectrum_subset_circle (u : unitary E) :
    spectrum 𝕜 (u : E) subseteq Metric.sphere 0 1 := by
  nontriviality E
  refine fun k hk => mem_sphere_zero_iff_norm.mpr (le_antisymm ?_ ?_)
  · simpa only [CStarRing.norm_coe_unitary u] using norm_le_norm_of_mem hk
  · rw [← Unitary.val_toUnits_apply u] at hk
    have hnk := ne_zero_of_mem_of_unit hk
    rw [← inv_inv (Unitary.toUnits u)]; rw [← spectrum.map_inv]; rw [Set.mem_inv] at hk
    have : ‖k‖⁻¹ <= ‖(↑(Unitary.toUnits u)⁻¹ : E)‖ := by
      simpa only [norm_inv] using norm_le_norm_of_mem hk
    simpa using inv_le_of_inv_le₀ (norm_pos_iff.mpr hnk) this

/--
theorem `spectrum.subset_circle_of_unitary` / 定理 `spectrum.subset_circle_of_unitary`

English:
theorem spectrum.subset_circle_of_unitary
  given: {u : E} (h : u in unitary E)
  proof: Unitary.spectrum_subset_circle ⟨u, h⟩

中文:
定理 spectrum.subset_circle_of_unitary
  条件: {u : E} (h : u in unitary E)
  证明: Unitary.spectrum_subset_circle ⟨u, h⟩

Depends on / 依赖: Unitary, Unitary.spectrum_subset_circle, spectrum_subset_circle
-/
theorem spectrum.subset_circle_of_unitary {u : E} (h : u in unitary E) :
    spectrum 𝕜 u subseteq Metric.sphere 0 1 :=
  Unitary.spectrum_subset_circle ⟨u, h⟩

/--
theorem `spectrum.norm_eq_one_of_unitary` / 定理 `spectrum.norm_eq_one_of_unitary`

English:
theorem spectrum.norm_eq_one_of_unitary
  statement: {u : E} (hu : u in unitary E)
  proof: by
  simpa using spectrum.subset_circle_of_unitary hu hz

中文:
定理 spectrum.norm_eq_one_of_unitary
  结论: {u : E} (hu : u in unitary E)
  证明: by
  simpa using spectrum.subset_circle_of_unitary hu hz

Depends on / 依赖: spectrum, spectrum.subset_circle_of_unitary, subset_circle_of_unitary
-/
theorem spectrum.norm_eq_one_of_unitary {u : E} (hu : u in unitary E)
    ⦃z : 𝕜⦄ (hz : z in spectrum 𝕜 u) : ‖z‖ = 1 := by
  simpa using spectrum.subset_circle_of_unitary hu hz

end UnitarySpectrum

section Quasispectrum

open scoped NNReal in
/--
lemma `CStarAlgebra.le_nnnorm_of_mem_quasispectrum` / 引理 `CStarAlgebra.le_nnnorm_of_mem_quasispectrum`

English:
lemma CStarAlgebra.le_nnnorm_of_mem_quasispectrum
  statement: {A : Type*} [NonUnitalCStarAlgebra A]
  proof: by
  rw [Unitization.quasispectrum_eq_spectrum_inr' Real>=0 Complex] at hx
  simpa [Unitization.nnnorm_inr] using spectrum.le_nnnorm_of_mem hx

中文:
引理 CStarAlgebra.le_nnnorm_of_mem_quasispectrum
  结论: {A : 类型} [NonUnitalCStarAlgebra A]
  证明: by
  rw [Unitization.quasispectrum_eq_spectrum_inr' Real>=0 Complex] at hx
  simpa [Unitization.nnnorm_inr] using spectrum.le_nnnorm_of_mem hx

Depends on / 依赖: Unitization, Unitization.nnnorm_inr, Unitization.quasispectrum_eq_spectrum_inr, le_nnnorm_of_mem, nnnorm_inr, quasispectrum_eq_spectrum_inr, spectrum, spectrum.le_nnnorm_of_mem
-/
lemma CStarAlgebra.le_nnnorm_of_mem_quasispectrum {A : Type*} [NonUnitalCStarAlgebra A]
    {a : A} {x : Real>=0} (hx : x in quasispectrum Real>=0 a) : x <= ‖a‖₊ := by
  rw [Unitization.quasispectrum_eq_spectrum_inr' Real>=0 Complex] at hx
  simpa [Unitization.nnnorm_inr] using spectrum.le_nnnorm_of_mem hx

end Quasispectrum

section ComplexScalars

open Complex

variable {A : Type*} [CStarAlgebra A]

local notation "↑ₐ" => algebraMap Complex A

/--
theorem `IsSelfAdjoint.spectralRadius_eq_nnnorm` / 定理 `IsSelfAdjoint.spectralRadius_eq_nnnorm`

English:
theorem IsSelfAdjoint.spectralRadius_eq_nnnorm
  given: {a : A} (ha : IsSelfAdjoint a)
  proof: by
  have hconst : Tendsto (fun _n : Nat => (‖a‖₊ : Real>=0∞)) atTop _ := tendsto_const_nhds
  refine tendsto_nhds_unique ?_ hconst
  convert!
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a : A)).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) using 1
  refine funext f

中文:
定理 IsSelfAdjoint.spectralRadius_eq_nnnorm
  条件: {a : A} (ha : IsSelfAdjoint a)
  证明: by
  have hconst : Tendsto (fun _n : Nat => (‖a‖₊ : Real>=0∞)) atTop _ := tendsto_const_nhds
  refine tendsto_nhds_unique ?_ hconst
  convert!
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a : A)).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) using 1
  refine funext f

Depends on / 依赖: ENNReal, ENNReal.coe_pow, ENNReal.ofReal_le_ofReal_iff, Function, Function.comp_apply, Tendsto, coe_pow, comp_apply, convert, ha.nnnorm_pow_two_pow, hconst, nnnorm_pow_two_pow, norm_nonneg, ofReal_le_ofReal_iff, ofReal_norm, one_lt_two, pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius, rpow_mul, rpow_natCast, spectrum
-/
theorem IsSelfAdjoint.spectralRadius_eq_nnnorm {a : A} (ha : IsSelfAdjoint a) :
    spectralRadius Complex a = ‖a‖₊ := by
  have hconst : Tendsto (fun _n : Nat => (‖a‖₊ : Real>=0∞)) atTop _ := tendsto_const_nhds
  refine tendsto_nhds_unique ?_ hconst
  convert!
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a : A)).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) using 1
  refine funext fun n => ?_
  rw [Function.comp_apply]; rw [ha.nnnorm_pow_two_pow]; rw [ENNReal.coe_pow]; rw [← rpow_natCast]; rw [← rpow_mul]
  simp

/--
lemma `IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm` / 引理 `IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm`

English:
lemma IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm
  given: {a : A} (ha : IsSelfAdjoint a)
  proof: by
  simp [ha.spectralRadius_eq_nnnorm]

中文:
引理 IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm
  条件: {a : A} (ha : IsSelfAdjoint a)
  证明: by
  simp [ha.spectralRadius_eq_nnnorm]

Depends on / 依赖: ha.spectralRadius_eq_nnnorm, spectralRadius_eq_nnnorm
-/
lemma IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm {a : A} (ha : IsSelfAdjoint a) :
    (spectralRadius Complex a).toReal = ‖a‖ := by
  simp [ha.spectralRadius_eq_nnnorm]

/--
theorem `IsStarNormal.spectralRadius_eq_nnnorm` / 定理 `IsStarNormal.spectralRadius_eq_nnnorm`

English:
theorem IsStarNormal.spectralRadius_eq_nnnorm
  given: (a : A) [IsStarNormal a]
  proof: by
  refine (ENNReal.pow_right_strictMono two_ne_zero).injective ?_
  have heq :
    (fun n : Nat => (‖(a⋆ * a) ^ n‖₊ : Real>=0∞) ^ (1 / n : Real)) =
      (fun x => x ^ 2) ∘ fun n : Nat => (‖a ^ n‖₊ : Real>=0∞) ^ (1 / n : Real) := by
    funext n
    rw [Function.comp_apply]; rw [← rpow_natCast]; r

中文:
定理 IsStarNormal.spectralRadius_eq_nnnorm
  条件: (a : A) [IsStarNormal a]
  证明: by
  refine (ENNReal.pow_right_strictMono two_ne_zero).injective ?_
  have heq :
    (fun n : Nat => (‖(a⋆ * a) ^ n‖₊ : Real>=0∞) ^ (1 / n : Real)) =
      (fun x => x ^ 2) ∘ fun n : Nat => (‖a ^ n‖₊ : Real>=0∞) ^ (1 / n : Real) := by
    funext n
    rw [Function.comp_apply]; rw [← rpow_natCast]; r

Depends on / 依赖: Commute, Commute.mul_pow, ENNReal, ENNReal.continuous_pow, ENNReal.pow_right_strictMono, Function, Function.comp_apply, coe_pow, comp_apply, continuous_pow, injective, mul_comm, mul_pow, nnnorm_star_mul_self, pow_right_strictMono, rpow_mul, rpow_natCast, star_comm_self, star_pow, tendsto
-/
theorem IsStarNormal.spectralRadius_eq_nnnorm (a : A) [IsStarNormal a] :
    spectralRadius Complex a = ‖a‖₊ := by
  refine (ENNReal.pow_right_strictMono two_ne_zero).injective ?_
  have heq :
    (fun n : Nat => (‖(a⋆ * a) ^ n‖₊ : Real>=0∞) ^ (1 / n : Real)) =
      (fun x => x ^ 2) ∘ fun n : Nat => (‖a ^ n‖₊ : Real>=0∞) ^ (1 / n : Real) := by
    funext n
    rw [Function.comp_apply]; rw [← rpow_natCast]; rw [← rpow_mul]; rw [mul_comm]; rw [rpow_mul]; rw [rpow_natCast]; rw [←
      coe_pow]; rw [sq]; rw [← nnnorm_star_mul_self]; rw [Commute.mul_pow (star_comm_self' a)]; rw [star_pow]
  have h₂ :=
    ((ENNReal.continuous_pow 2).tendsto (spectralRadius Complex a)).comp
      (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a)
  rw [← heq] at h₂
  convert! tendsto_nhds_unique h₂ (pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a⋆ * a))
  rw [(IsSelfAdjoint.star_mul_self a).spectralRadius_eq_nnnorm]; rw [sq]; rw [nnnorm_star_mul_self]; rw [coe_mul]

namespace CStarAlgebra

/--
theorem `toReal_spectralRadius_star_mul_self_eq_norm_sq` / 定理 `toReal_spectralRadius_star_mul_self_eq_norm_sq`

English:
theorem toReal_spectralRadius_star_mul_self_eq_norm_sq
  given: (a : A)
  proof: by
  rw [(IsSelfAdjoint.star_mul_self a).toReal_spectralRadius_complex_eq_norm]; rw [CStarRing.norm_star_mul_self]; rw [← pow_two]

中文:
定理 toReal_spectralRadius_star_mul_self_eq_norm_sq
  条件: (a : A)
  证明: by
  rw [(IsSelfAdjoint.star_mul_self a).toReal_spectralRadius_complex_eq_norm]; rw [CStarRing.norm_star_mul_self]; rw [← pow_two]

Depends on / 依赖: CStarRing, CStarRing.norm_star_mul_self, IsSelfAdjoint, IsSelfAdjoint.star_mul_self, norm_star_mul_self, pow_two, star_mul_self, toReal_spectralRadius_complex_eq_norm
-/
theorem toReal_spectralRadius_star_mul_self_eq_norm_sq (a : A) :
    (spectralRadius Complex (a⋆ * a)).toReal = ‖a‖ ^ 2 := by
  rw [(IsSelfAdjoint.star_mul_self a).toReal_spectralRadius_complex_eq_norm]; rw [CStarRing.norm_star_mul_self]; rw [← pow_two]

/--
theorem `toReal_spectralRadius_self_mul_star_eq_norm_sq` / 定理 `toReal_spectralRadius_self_mul_star_eq_norm_sq`

English:
theorem toReal_spectralRadius_self_mul_star_eq_norm_sq
  given: (a : A)
  proof: by
  rw [← norm_star a]; rw [← toReal_spectralRadius_star_mul_self_eq_norm_sq]; rw [star_star]

中文:
定理 toReal_spectralRadius_self_mul_star_eq_norm_sq
  条件: (a : A)
  证明: by
  rw [← norm_star a]; rw [← toReal_spectralRadius_star_mul_self_eq_norm_sq]; rw [star_star]

Depends on / 依赖: norm_star, star_star, toReal_spectralRadius_star_mul_self_eq_norm_sq
-/
theorem toReal_spectralRadius_self_mul_star_eq_norm_sq (a : A) :
    (spectralRadius Complex (a * a⋆)).toReal = ‖a‖ ^ 2 := by
  rw [← norm_star a]; rw [← toReal_spectralRadius_star_mul_self_eq_norm_sq]; rw [star_star]

/--
theorem `sqrt_toReal_spectralRadius_star_mul_self_eq_norm` / 定理 `sqrt_toReal_spectralRadius_star_mul_self_eq_norm`

English:
theorem sqrt_toReal_spectralRadius_star_mul_self_eq_norm
  given: (a : A)
  proof: by
  simp [toReal_spectralRadius_star_mul_self_eq_norm_sq]

中文:
定理 sqrt_toReal_spectralRadius_star_mul_self_eq_norm
  条件: (a : A)
  证明: by
  simp [toReal_spectralRadius_star_mul_self_eq_norm_sq]

Depends on / 依赖: toReal_spectralRadius_star_mul_self_eq_norm_sq
-/
theorem sqrt_toReal_spectralRadius_star_mul_self_eq_norm (a : A) :
    (spectralRadius Complex (a⋆ * a)).toReal.sqrt = ‖a‖ := by
  simp [toReal_spectralRadius_star_mul_self_eq_norm_sq]

/--
theorem `sqrt_toReal_spectralRadius_self_mul_star_eq_norm` / 定理 `sqrt_toReal_spectralRadius_self_mul_star_eq_norm`

English:
theorem sqrt_toReal_spectralRadius_self_mul_star_eq_norm
  given: (a : A)
  proof: by
  simp [toReal_spectralRadius_self_mul_star_eq_norm_sq]

中文:
定理 sqrt_toReal_spectralRadius_self_mul_star_eq_norm
  条件: (a : A)
  证明: by
  simp [toReal_spectralRadius_self_mul_star_eq_norm_sq]

Depends on / 依赖: toReal_spectralRadius_self_mul_star_eq_norm_sq
-/
theorem sqrt_toReal_spectralRadius_self_mul_star_eq_norm (a : A) :
    (spectralRadius Complex (a * a⋆)).toReal.sqrt = ‖a‖ := by
  simp [toReal_spectralRadius_self_mul_star_eq_norm_sq]

end CStarAlgebra

/--
theorem `IsSelfAdjoint.mem_spectrum_eq_re` / 定理 `IsSelfAdjoint.mem_spectrum_eq_re`

English:
theorem IsSelfAdjoint.mem_spectrum_eq_re
  statement: {a : A} (ha : IsSelfAdjoint a) {z : Complex}
  proof: by
  let +nondep : NormedAlgebra Rat A := .restrictScalars Rat Complex A
  have hu := exp_mem_unitary_of_mem_skewAdjoint (ha.smul_mem_skewAdjoint conj_I)
  let Iu := Units.mk0 I I_ne_zero
  have : NormedSpace.exp (I • z) in spectrum Complex (NormedSpace.exp (I • a)) := by
    simpa only [Units.smul_

中文:
定理 IsSelfAdjoint.mem_spectrum_eq_re
  结论: {a : A} (ha : IsSelfAdjoint a) {z : Complex}
  证明: by
  let +nondep : NormedAlgebra Rat A := .restrictScalars Rat Complex A
  have hu := exp_mem_unitary_of_mem_skewAdjoint (ha.smul_mem_skewAdjoint conj_I)
  let Iu := Units.mk0 I I_ne_zero
  have : NormedSpace.exp (I • z) in spectrum Complex (NormedSpace.exp (I • a)) := by
    simpa only [Units.smul_

Depends on / 依赖: Complex.exp_eq_exp_Complex, Complex.ext, I_ne_zero, NormedAlgebra, NormedSpace, NormedSpace.exp, Real.exp_eq_one, Units.mk0, Units.smul_def, Units.val_mk0, conj_I, exp_eq_exp_Complex, exp_eq_one, exp_mem_exp, exp_mem_unitary_of_mem_skewAdjoint, ha.smul_mem_skewAdjoint, mem_sphere_zero_iff_norm, nondep, norm_exp, ofReal_re
-/
theorem IsSelfAdjoint.mem_spectrum_eq_re {a : A} (ha : IsSelfAdjoint a) {z : Complex}
    (hz : z in spectrum Complex a) : z = z.re := by
  let +nondep : NormedAlgebra Rat A := .restrictScalars Rat Complex A
  have hu := exp_mem_unitary_of_mem_skewAdjoint (ha.smul_mem_skewAdjoint conj_I)
  let Iu := Units.mk0 I I_ne_zero
  have : NormedSpace.exp (I • z) in spectrum Complex (NormedSpace.exp (I • a)) := by
    simpa only [Units.smul_def, Units.val_mk0] using!
      spectrum.exp_mem_exp (Iu • a) (smul_mem_smul_iff.mpr hz)
exact Complex.ext (ofReal_re _) by
    simpa only [← Complex.exp_eq_exp_Complex, mem_sphere_zero_iff_norm, norm_exp, Real.exp_eq_one_iff,
      smul_eq_mul, I_mul, neg_eq_zero] using!
      spectrum.subset_circle_of_unitary hu this

/--
theorem `selfAdjoint.mem_spectrum_eq_re` / 定理 `selfAdjoint.mem_spectrum_eq_re`

English:
theorem selfAdjoint.mem_spectrum_eq_re
  statement: (a : selfAdjoint A) {z : Complex}
  proof: a.prop.mem_spectrum_eq_re hz

中文:
定理 selfAdjoint.mem_spectrum_eq_re
  结论: (a : selfAdjoint A) {z : Complex}
  证明: a.prop.mem_spectrum_eq_re hz

Depends on / 依赖: a.prop.mem_spectrum_eq_re, mem_spectrum_eq_re
-/
theorem selfAdjoint.mem_spectrum_eq_re (a : selfAdjoint A) {z : Complex}
    (hz : z in spectrum Complex (a : A)) : z = z.re :=
  a.prop.mem_spectrum_eq_re hz

/--
theorem `IsSelfAdjoint.im_eq_zero_of_mem_spectrum` / 定理 `IsSelfAdjoint.im_eq_zero_of_mem_spectrum`

English:
theorem IsSelfAdjoint.im_eq_zero_of_mem_spectrum
  statement: {a : A} (ha : IsSelfAdjoint a)
  proof: by
  rw [ha.mem_spectrum_eq_re hz]; rw [ofReal_im]

中文:
定理 IsSelfAdjoint.im_eq_zero_of_mem_spectrum
  结论: {a : A} (ha : IsSelfAdjoint a)
  证明: by
  rw [ha.mem_spectrum_eq_re hz]; rw [ofReal_im]

Depends on / 依赖: ha.mem_spectrum_eq_re, mem_spectrum_eq_re, ofReal_im
-/
theorem IsSelfAdjoint.im_eq_zero_of_mem_spectrum {a : A} (ha : IsSelfAdjoint a)
    {z : Complex} (hz : z in spectrum Complex a) : z.im = 0 := by
  rw [ha.mem_spectrum_eq_re hz]; rw [ofReal_im]

/--
theorem `IsSelfAdjoint.val_re_map_spectrum` / 定理 `IsSelfAdjoint.val_re_map_spectrum`

English:
theorem IsSelfAdjoint.val_re_map_spectrum
  given: {a : A} (ha : IsSelfAdjoint a)
  proof: le_antisymm (fun z hz => ⟨z, hz, (ha.mem_spectrum_eq_re hz).symm⟩) fun z => by
    rintro ⟨z, hz, rfl⟩
    simpa only [(ha.mem_spectrum_eq_re hz).symm, Function.comp_apply] using hz

中文:
定理 IsSelfAdjoint.val_re_map_spectrum
  条件: {a : A} (ha : IsSelfAdjoint a)
  证明: le_antisymm (fun z hz => ⟨z, hz, (ha.mem_spectrum_eq_re hz).symm⟩) fun z => by
    rintro ⟨z, hz, rfl⟩
    simpa only [(ha.mem_spectrum_eq_re hz).symm, Function.comp_apply] using hz

Depends on / 依赖: Function, Function.comp_apply, comp_apply, ha.mem_spectrum_eq_re, le_antisymm, mem_spectrum_eq_re
-/
theorem IsSelfAdjoint.val_re_map_spectrum {a : A} (ha : IsSelfAdjoint a) :
    spectrum Complex a = ((↑) ∘ re '' spectrum Complex a : Set Complex) :=
  le_antisymm (fun z hz => ⟨z, hz, (ha.mem_spectrum_eq_re hz).symm⟩) fun z => by
    rintro ⟨z, hz, rfl⟩
    simpa only [(ha.mem_spectrum_eq_re hz).symm, Function.comp_apply] using hz

/--
theorem `selfAdjoint.val_re_map_spectrum` / 定理 `selfAdjoint.val_re_map_spectrum`

English:
theorem selfAdjoint.val_re_map_spectrum
  given: (a : selfAdjoint A)
  proof: a.property.val_re_map_spectrum

中文:
定理 selfAdjoint.val_re_map_spectrum
  条件: (a : selfAdjoint A)
  证明: a.property.val_re_map_spectrum

Depends on / 依赖: a.property.val_re_map_spectrum, property, val_re_map_spectrum
-/
theorem selfAdjoint.val_re_map_spectrum (a : selfAdjoint A) :
    spectrum Complex (a : A) = ((↑) ∘ re '' spectrum Complex (a : A) : Set Complex) :=
  a.property.val_re_map_spectrum

/--
lemma `IsSelfAdjoint.isConnected_spectrum_compl` / 引理 `IsSelfAdjoint.isConnected_spectrum_compl`

English:
lemma IsSelfAdjoint.isConnected_spectrum_compl
  given: {a : A} (ha : IsSelfAdjoint a)
  proof: by
  suffices IsConnected (((σ Complex a)ᶜ inter {z | 0 <= z.im}) union (σ Complex a)ᶜ inter {z | z.im <= 0}) by
    rw [← Set.inter_union_distrib_left]; rw [← Set.ofPred_or] at this
    rw [← Set.inter_univ (σ Complex a)ᶜ]
    convert this
exact Eq.symm Set.eq_univ_of_forall (fun z => le_total 0 z.

中文:
引理 IsSelfAdjoint.isConnected_spectrum_compl
  条件: {a : A} (ha : IsSelfAdjoint a)
  证明: by
  suffices IsConnected (((σ Complex a)ᶜ inter {z | 0 <= z.im}) union (σ Complex a)ᶜ inter {z | z.im <= 0}) by
    rw [← Set.inter_union_distrib_left]; rw [← Set.ofPred_or] at this
    rw [← Set.inter_univ (σ Complex a)ᶜ]
    convert this
exact Eq.symm Set.eq_univ_of_forall (fun z => le_total 0 z.

Depends on / 依赖: Complex.isometry_ofReal.antilipschitz.tendsto_cobounded, Eq.symm, Filter, Filter.NeBot.nonempty_of_mem, Filter.mem_map.mp, IsConnected, IsConnected.union, Set.eq_univ_of_forall, Set.inter_union_distrib_left, Set.inter_univ, Set.ofPred_or, antilipschitz, convert, eq_univ_of_forall, inter_union_distrib_left, inter_univ, isBounded, isometry_ofReal, le_total, mem_map
-/
lemma IsSelfAdjoint.isConnected_spectrum_compl {a : A} (ha : IsSelfAdjoint a) :
    IsConnected (σ Complex a)ᶜ := by
  suffices IsConnected (((σ Complex a)ᶜ inter {z | 0 <= z.im}) union (σ Complex a)ᶜ inter {z | z.im <= 0}) by
    rw [← Set.inter_union_distrib_left]; rw [← Set.ofPred_or] at this
    rw [← Set.inter_univ (σ Complex a)ᶜ]
    convert this
exact Eq.symm Set.eq_univ_of_forall (fun z => le_total 0 z.im)
  refine IsConnected.union ?nonempty ?upper ?lower
  case nonempty =>
have := Filter.NeBot.nonempty_of_mem inferInstance Filter.mem_map.mp
      Complex.isometry_ofReal.antilipschitz.tendsto_cobounded (spectrum.isBounded a |>.compl)
.mono by simp exact this.image Complex.ofReal
case' upper => apply Complex.isConnected_of_upperHalfPlane ?_ Set.inter_subset_right
case' lower => apply Complex.isConnected_of_lowerHalfPlane ?_ Set.inter_subset_right
  all_goals
    refine Set.subset_inter (fun z hz hz' => ?_) (fun _ => by simpa using le_of_lt)
    rw [Set.mem_ofPred_eq]; rw [ha.im_eq_zero_of_mem_spectrum hz'] at hz
    simp_all

namespace StarSubalgebra

variable (S : StarSubalgebra Complex A) [hS : IsClosed (S : Set A)]

/--
lemma `coe_isUnit` / 引理 `coe_isUnit`

English:
lemma coe_isUnit
  given: {a : S}
  statement: IsUnit (a : A) ↔ IsUnit a
  proof: by
  refine ⟨fun ha => ?_, IsUnit.map S.subtype⟩
  have ha₁ := ha.star.mul ha
  have ha₂ := ha.mul ha.star
  have spec_eq {x : S} (hx : IsSelfAdjoint x) : spectrum Complex x = spectrum Complex (x : A) :=
Subalgebra.spectrum_eq_of_isPreconnected_compl S _
      (hx.map S.subtype).isConnected_spectrum

中文:
引理 coe_isUnit
  条件: {a : S}
  结论: IsUnit (a : A) ↔ IsUnit a
  证明: by
  refine ⟨fun ha => ?_, IsUnit.map S.subtype⟩
  have ha₁ := ha.star.mul ha
  have ha₂ := ha.mul ha.star
  have spec_eq {x : S} (hx : IsSelfAdjoint x) : spectrum Complex x = spectrum Complex (x : A) :=
Subalgebra.spectrum_eq_of_isPreconnected_compl S _
      (hx.map S.subtype).isConnected_spectrum

Depends on / 依赖: IsSelfAdjoint, IsUnit, IsUnit.map, MulMemClass, MulMemClass.coe_mul, S.subtype, StarMemClass, StarMemClass.coe_star, Subalgebra, Subalgebra.spectrum_eq_of_isPreconnected_compl, coe_mul, coe_star, ha.mul, ha.star, ha.star.mul, hx.map, isConnected_spectrum_compl, isConnected_spectrum_compl.isPreconnected, isPreconnected, spec_eq
-/
lemma coe_isUnit {a : S} : IsUnit (a : A) ↔ IsUnit a := by
  refine ⟨fun ha => ?_, IsUnit.map S.subtype⟩
  have ha₁ := ha.star.mul ha
  have ha₂ := ha.mul ha.star
  have spec_eq {x : S} (hx : IsSelfAdjoint x) : spectrum Complex x = spectrum Complex (x : A) :=
Subalgebra.spectrum_eq_of_isPreconnected_compl S _
      (hx.map S.subtype).isConnected_spectrum_compl.isPreconnected
  rw [← StarMemClass.coe_star]; rw [← MulMemClass.coe_mul]; rw [← spectrum.zero_notMem_iff Complex]; rw [← spec_eq]; rw [spectrum.zero_notMem_iff] at ha₁ ha₂
  · have h₁ : ha₁.unit⁻¹ * star a * a = 1 := mul_assoc _ _ a ▸ ha₁.val_inv_mul
    have h₂ : a * (star a * ha₂.unit⁻¹) = 1 := (mul_assoc a _ _).symm ▸ ha₂.mul_val_inv
    exact ⟨⟨a, ha₁.unit⁻¹ * star a, left_inv_eq_right_inv h₁ h₂ ▸ h₂, h₁⟩, rfl⟩
  · exact IsSelfAdjoint.mul_star_self a
  · exact IsSelfAdjoint.star_mul_self a

/--
lemma `mem_spectrum_iff` / 引理 `mem_spectrum_iff`

English:
lemma mem_spectrum_iff
  given: {a : S} {z : Complex}
  statement: z in spectrum Complex a ↔ z in spectrum Complex (a : A)
  proof: not_iff_not.mpr S.coe_isUnit.symm

中文:
引理 mem_spectrum_iff
  条件: {a : S} {z : Complex}
  结论: z in spectrum Complex a ↔ z in spectrum Complex (a : A)
  证明: not_iff_not.mpr S.coe_isUnit.symm

Depends on / 依赖: S.coe_isUnit.symm, coe_isUnit, not_iff_not, not_iff_not.mpr
-/
lemma mem_spectrum_iff {a : S} {z : Complex} : z in spectrum Complex a ↔ z in spectrum Complex (a : A) :=
  not_iff_not.mpr S.coe_isUnit.symm

/--
lemma `spectrum_eq` / 引理 `spectrum_eq`

English:
lemma spectrum_eq
  given: {a : S}
  statement: spectrum Complex a = spectrum Complex (a : A)
  proof: Set.ext fun _ => S.mem_spectrum_iff

中文:
引理 spectrum_eq
  条件: {a : S}
  结论: spectrum Complex a = spectrum Complex (a : A)
  证明: Set.ext fun _ => S.mem_spectrum_iff

Depends on / 依赖: S.mem_spectrum_iff, Set.ext, mem_spectrum_iff
-/
lemma spectrum_eq {a : S} : spectrum Complex a = spectrum Complex (a : A) :=
  Set.ext fun _ => S.mem_spectrum_iff

end StarSubalgebra

end ComplexScalars

namespace NonUnitalStarAlgHom

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [FunLike F A B] [NonUnitalAlgHomClass F Complex A B] [StarHomClass F A B]

open Unitization

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `nnnorm_apply_le` / 引理 `nnnorm_apply_le`

English:
lemma nnnorm_apply_le
  given: (φ : F) (a : A)
  statement: ‖φ a‖₊ <= ‖a‖₊
  proof: by
  have h (ψ : Unitization Complex A ->⋆ₐ[Complex] Unitization Complex B) (x : Unitization Complex A) :
      ‖ψ x‖₊ <= ‖x‖₊ := by
    suffices forall {s}, IsSelfAdjoint s -> ‖ψ s‖₊ <= ‖s‖₊ by
      refine nonneg_le_nonneg_of_sq_le_sq zero_le ?_
      simp_rw [← nnnorm_star_mul_self, ← map_star, ←

中文:
引理 nnnorm_apply_le
  条件: (φ : F) (a : A)
  结论: ‖φ a‖₊ <= ‖a‖₊
  证明: by
  have h (ψ : Unitization Complex A ->⋆ₐ[Complex] Unitization Complex B) (x : Unitization Complex A) :
      ‖ψ x‖₊ <= ‖x‖₊ := by
    suffices forall {s}, IsSelfAdjoint s -> ‖ψ s‖₊ <= ‖s‖₊ by
      refine nonneg_le_nonneg_of_sq_le_sq zero_le ?_
      simp_rw [← nnnorm_star_mul_self, ← map_star, ←

Depends on / 依赖: IsSelfAdjoint, Unitization, coe_le_coe, hs.map, hs.spectralRadius_eq_nnnorm, map_mul, map_star, nnnorm_star_mul_self, nonneg_le_nonneg_of_sq_le_sq, simp_rw, spectralRadius, spectralRadius_eq_nnnorm, star_mul_self, zero_le
-/
lemma nnnorm_apply_le (φ : F) (a : A) : ‖φ a‖₊ <= ‖a‖₊ := by
  have h (ψ : Unitization Complex A ->⋆ₐ[Complex] Unitization Complex B) (x : Unitization Complex A) :
      ‖ψ x‖₊ <= ‖x‖₊ := by
    suffices forall {s}, IsSelfAdjoint s -> ‖ψ s‖₊ <= ‖s‖₊ by
      refine nonneg_le_nonneg_of_sq_le_sq zero_le ?_
      simp_rw [← nnnorm_star_mul_self, ← map_star, ← map_mul]
exact this .star_mul_self x
    intro s hs
    suffices this : spectralRadius Complex (ψ s) <= spectralRadius Complex s by
      rwa [(hs.map ψ).spectralRadius_eq_nnnorm, hs.spectralRadius_eq_nnnorm, coe_le_coe]
        at this
    exact iSup_le_iSup_of_subset (AlgHom.spectrum_apply_subset ψ s)
  simpa [nnnorm_inr] using h (starLift (inrNonUnitalStarAlgHom Complex B |>.comp (φ : A ->⋆ₙₐ[Complex] B))) a

/--
lemma `norm_apply_le` / 引理 `norm_apply_le`

English:
lemma norm_apply_le
  given: (φ : F) (a : A)
  statement: ‖φ a‖ <= ‖a‖
  proof: by
  exact_mod_cast nnnorm_apply_le φ a

中文:
引理 norm_apply_le
  条件: (φ : F) (a : A)
  结论: ‖φ a‖ <= ‖a‖
  证明: by
  exact_mod_cast nnnorm_apply_le φ a

Depends on / 依赖: nnnorm_apply_le
-/
lemma norm_apply_le (φ : F) (a : A) : ‖φ a‖ <= ‖a‖ := by
  exact_mod_cast nnnorm_apply_le φ a

/--
lemma `instContinuousLinearMapClassComplex` / 引理 `instContinuousLinearMapClassComplex`

English:
lemma instContinuousLinearMapClassComplex
  statement: ContinuousLinearMapClass F Complex A B
  proof: { NonUnitalAlgHomClass.instLinearMapClass with
    map_continuous := fun φ =>
      AddMonoidHomClass.continuous_of_bound φ 1 (by simpa only [one_mul] using! nnnorm_apply_le φ) }

scoped[CStarAlgebra] attribute [instance] NonUnitalStarAlgHom.instContinuousLinearMapClassComplex

中文:
引理 instContinuousLinearMapClassComplex
  结论: ContinuousLinearMapClass F Complex A B
  证明: { NonUnitalAlgHomClass.instLinearMapClass with
    map_continuous := fun φ =>
      AddMonoidHomClass.continuous_of_bound φ 1 (by simpa only [one_mul] using! nnnorm_apply_le φ) }

scoped[CStarAlgebra] attribute [instance] NonUnitalStarAlgHom.instContinuousLinearMapClassComplex

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.continuous_of_bound, NonUnitalAlgHomClass, NonUnitalAlgHomClass.instLinearMapClass, continuous_of_bound, instLinearMapClass, map_continuous, nnnorm_apply_le, one_mul
-/
lemma instContinuousLinearMapClassComplex : ContinuousLinearMapClass F Complex A B :=
  { NonUnitalAlgHomClass.instLinearMapClass with
    map_continuous := fun φ =>
      AddMonoidHomClass.continuous_of_bound φ 1 (by simpa only [one_mul] using! nnnorm_apply_le φ) }

scoped[CStarAlgebra] attribute [instance] NonUnitalStarAlgHom.instContinuousLinearMapClassComplex

end NonUnitalStarAlgHom

namespace StarAlgEquiv

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [EquivLike F A B]
variable [NonUnitalAlgEquivClass F Complex A B] [StarHomClass F A B]

/--
lemma `nnnorm_map` / 引理 `nnnorm_map`

English:
lemma nnnorm_map
  given: (φ : F) (a : A)
  statement: ‖φ a‖₊ = ‖a‖₊
  proof: le_antisymm (NonUnitalStarAlgHom.nnnorm_apply_le φ a) by
    simpa using! NonUnitalStarAlgHom.nnnorm_apply_le (symm (φ : A ≃⋆ₐ[Complex] B)) ((φ : A ≃⋆ₐ[Complex] B) a)

中文:
引理 nnnorm_map
  条件: (φ : F) (a : A)
  结论: ‖φ a‖₊ = ‖a‖₊
  证明: le_antisymm (NonUnitalStarAlgHom.nnnorm_apply_le φ a) by
    simpa using! NonUnitalStarAlgHom.nnnorm_apply_le (symm (φ : A ≃⋆ₐ[Complex] B)) ((φ : A ≃⋆ₐ[Complex] B) a)

Depends on / 依赖: NonUnitalStarAlgHom, NonUnitalStarAlgHom.nnnorm_apply_le, le_antisymm, nnnorm_apply_le
-/
lemma nnnorm_map (φ : F) (a : A) : ‖φ a‖₊ = ‖a‖₊ :=
le_antisymm (NonUnitalStarAlgHom.nnnorm_apply_le φ a) by
    simpa using! NonUnitalStarAlgHom.nnnorm_apply_le (symm (φ : A ≃⋆ₐ[Complex] B)) ((φ : A ≃⋆ₐ[Complex] B) a)

/--
lemma `norm_map` / 引理 `norm_map`

English:
lemma norm_map
  given: (φ : F) (a : A)
  statement: ‖φ a‖ = ‖a‖
  proof: congr_arg NNReal.toReal (nnnorm_map φ a)

中文:
引理 norm_map
  条件: (φ : F) (a : A)
  结论: ‖φ a‖ = ‖a‖
  证明: congr_arg NNReal.toReal (nnnorm_map φ a)

Depends on / 依赖: NNReal, NNReal.toReal, congr_arg, nnnorm_map, toReal
-/
lemma norm_map (φ : F) (a : A) : ‖φ a‖ = ‖a‖ :=
  congr_arg NNReal.toReal (nnnorm_map φ a)

/--
lemma `isometry` / 引理 `isometry`

English:
lemma isometry
  given: (φ : F)
  statement: Isometry φ
  proof: AddMonoidHomClass.isometry_of_norm φ (norm_map φ)

中文:
引理 isometry
  条件: (φ : F)
  结论: Isometry φ
  证明: AddMonoidHomClass.isometry_of_norm φ (norm_map φ)

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, isometry_of_norm, norm_map
-/
lemma isometry (φ : F) : Isometry φ :=
  AddMonoidHomClass.isometry_of_norm φ (norm_map φ)

end StarAlgEquiv

end

namespace WeakDual

open ContinuousMap Complex

open scoped ComplexStarModule

variable {F A : Type*} [CStarAlgebra A] [FunLike F A Complex] [hF : AlgHomClass F Complex A Complex]

/-- This instance is provided instead of `StarHomClass` to avoid type class inference loops.
See note [lower instance priority] -/
noncomputable instance (priority := 100) Complex.instStarHomClass : StarHomClass F A Complex where
  map_star φ a := by
    suffices hsa : forall s : selfAdjoint A, (φ s)⋆ = φ s by
      rw [← realPart_add_I_smul_imaginaryPart a]
      simp only [map_add, map_smul, star_add, star_smul, hsa, selfAdjoint.star_val_eq]
    intro s
    rw [selfAdjoint.mem_spectrum_eq_re s (AlgHom.apply_mem_spectrum φ (s : A))]
    simp

/--
lemma `_root_.AlgHomClass.instStarHomClass` / 引理 `_root_.AlgHomClass.instStarHomClass`

English:
lemma _root_.AlgHomClass.instStarHomClass
  statement: StarHomClass F A Complex
  proof: { WeakDual.Complex.instStarHomClass, hF with }

中文:
引理 _root_.AlgHomClass.instStarHomClass
  结论: StarHomClass F A Complex
  证明: { WeakDual.Complex.instStarHomClass, hF with }

Depends on / 依赖: WeakDual, WeakDual.Complex.instStarHomClass, instStarHomClass
-/
lemma _root_.AlgHomClass.instStarHomClass : StarHomClass F A Complex :=
  { WeakDual.Complex.instStarHomClass, hF with }

namespace CharacterSpace

/--
Instance `instStarHomClass` / 实例 `instStarHomClass`

English:
instance instStarHomClass
  signature: : StarHomClass (characterSpace Complex A) A Complex
  body: { AlgHomClass.instStarHomClass with }

中文:
实例 instStarHomClass
  签名: : StarHomClass (characterSpace Complex A) A Complex
  定义体: { AlgHomClass.instStarHomClass with }

Depends on / 依赖: AlgHomClass, AlgHomClass.instStarHomClass, instStarHomClass
-/
noncomputable instance instStarHomClass : StarHomClass (characterSpace Complex A) A Complex :=
  { AlgHomClass.instStarHomClass with }

end CharacterSpace

end WeakDual
