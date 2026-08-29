/-
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# The Product Formula for number fields

In this file we prove the Product Formula for number fields: for any non-zero element `x` of a
number field `K`, we have `∏ |x|ᵥ=1` where the product runs over the equivalence classes of absolute
values of `K`. The `|⬝|ᵥ` are normalized as follows:
- for the infinite places, `|⬝|ᵥ` is the absolute value on `K` induced by the corresponding field
  embedding in `ℂ` and the usual absolute value on `ℂ`;
- for the finite places and a non-zero `x`, `|x|ᵥ` is equal to the norm of the corresponding maximal
  ideal of `𝓞 K` raised to the power of the `v`-adic valuation of `x`.

## Main Results

* `NumberField.FinitePlace.prod_eq_inv_abs_norm`: for any non-zero element `x` of a number field
  `K`, the product `∏ |x|ᵥ` of the absolute values of `x` associated to the finite places of `K` is
  equal to the inverse of the norm of `x`.
* `NumberField.prod_abs_eq_one`: for any non-zero element `x` of a number field `K`, we have
  `∏ |x|ᵥ=1`, where the product runs over the equivalence classes of absolute values of `K`.

## Tags
number field, embeddings, places, infinite places, finite places, product formula
-/

public section

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

open Algebra

open Function Ideal IsDedekindDomain HeightOneSpectrum in
/--
theorem `FinitePlace.prod_eq_inv_abs_norm_int` / 定理 `FinitePlace.prod_eq_inv_abs_norm_int`

English:
theorem FinitePlace.prod_eq_inv_abs_norm_int
  given: {x : 𝓞 K} (h_x_nezero : x != 0)
  proof: by
  simp only [← finprod_comp_equiv equivHeightOneSpectrum.symm, equivHeightOneSpectrum_symm_apply]
  refine (inv_eq_of_mul_eq_one_left ?_).symm
  norm_cast
  have h_span_nezero : span {x} != 0 := by simp [h_x_nezero]
  rw [Int.abs_eq_natAbs]; rw [← absNorm_span_singleton]; rw [← finprod_heightOneS

中文:
定理 FinitePlace.prod_eq_inv_abs_norm_int
  条件: {x : 𝓞 K} (h_x_nezero : x != 0)
  证明: by
  simp only [← finprod_comp_equiv equivHeightOneSpectrum.symm, equivHeightOneSpectrum_symm_apply]
  refine (inv_eq_of_mul_eq_one_left ?_).symm
  norm_cast
  have h_span_nezero : span {x} != 0 := by simp [h_x_nezero]
  rw [Int.abs_eq_natAbs]; rw [← absNorm_span_singleton]; rw [← finprod_heightOneS

Depends on / 依赖: Finite, HeightOneSpectrum, Int.abs_eq_natAbs, Int.cast_natCast, absNorm_span_singleton, abs_eq_natAbs, asIdeal, cast_natCast, dvd_span_singleton, equivHeightOneSpectrum, equivHeightOneSpectrum.symm, equivHeightOneSpectrum_symm_apply, finite_factors, finprod_comp_equiv, finprod_heightOneSpectrum_factorization, h_span_nezero, h_x_nezero, inv_eq_of_mul_eq_one_left, v.asIdeal
-/
theorem FinitePlace.prod_eq_inv_abs_norm_int {x : 𝓞 K} (h_x_nezero : x != 0) :
    ∏ᶠ w : FinitePlace K, w x = (|norm Int x| : Real)⁻¹ := by
  simp only [← finprod_comp_equiv equivHeightOneSpectrum.symm, equivHeightOneSpectrum_symm_apply]
  refine (inv_eq_of_mul_eq_one_left ?_).symm
  norm_cast
  have h_span_nezero : span {x} != 0 := by simp [h_x_nezero]
  rw [Int.abs_eq_natAbs]; rw [← absNorm_span_singleton]; rw [← finprod_heightOneSpectrum_factorization h_span_nezero]; rw [Int.cast_natCast]
  let t₀ := {v : HeightOneSpectrum (𝓞 K) | x in v.asIdeal}
  have h_fin₀ : t₀.Finite := by simp only [← dvd_span_singleton, finite_factors h_span_nezero, t₀]
  let t₁ := (fun v : HeightOneSpectrum (𝓞 K) => ‖embedding v (x : K)‖).mulSupport
  let t₂ :=
    (fun v : HeightOneSpectrum (𝓞 K) => (absNorm (v.maxPowDividing (span {x})) : Real)).mulSupport
have h_fin₁ : t₁.Finite := h_fin₀.subset by simp [norm_eq_one_iff_notMem, t₁, t₀]
  have h_fin₂ : t₂.Finite := by
    refine h_fin₀.subset ?_
    simp only [mulSupport_subset_iff, Set.mem_ofPred_eq, t₂, t₀,
      maxPowDividing, ← dvd_span_singleton]
    intro v hv
    simp only [map_pow, Nat.cast_pow, ← pow_zero (absNorm v.asIdeal : Real)] at hv
refine (Associates.count_ne_zero_iff_dvd h_span_nezero (irreducible v)).1 fun h => hv ?_
    congr
  have h_prod : (absNorm (∏ᶠ (v : HeightOneSpectrum (𝓞 K)), v.maxPowDividing (span {x})) : Real) =
      ∏ᶠ (v : HeightOneSpectrum (𝓞 K)), (absNorm (v.maxPowDividing (span {x})) : Real) :=
    ((Nat.castRingHom Real).toMonoidHom.comp absNorm.toMonoidHom).map_finprod_of_preimage_one
      (by simp) _
  rw [h_prod]; rw [← finprod_mul_distrib h_fin₁ h_fin₂]
  exact finprod_eq_one_of_forall_eq_one fun v => embedding_mul_absNorm _ v h_x_nezero

/--
theorem `FinitePlace.prod_eq_inv_abs_norm` / 定理 `FinitePlace.prod_eq_inv_abs_norm`

English:
theorem FinitePlace.prod_eq_inv_abs_norm
  given: {x : K} (h_x_nezero : x != 0)
  proof: by
  --reduce to 𝓞 K
  rcases IsFractionRing.div_surjective (𝓞 K) x with ⟨a, b, hb, rfl⟩
  apply nonZeroDivisors.ne_zero at hb
  have ha : a != 0 := by
    rintro rfl
    simp at h_x_nezero
  simp_rw [map_div₀, Rat.cast_inv, Rat.cast_abs,
    finprod_div_distrib (hasFiniteMulSupport_int ha) (hasFini

中文:
定理 FinitePlace.prod_eq_inv_abs_norm
  条件: {x : K} (h_x_nezero : x != 0)
  证明: by
  --reduce to 𝓞 K
  rcases IsFractionRing.div_surjective (𝓞 K) x with ⟨a, b, hb, rfl⟩
  apply nonZeroDivisors.ne_zero at hb
  have ha : a != 0 := by
    rintro rfl
    simp at h_x_nezero
  simp_rw [map_div₀, Rat.cast_inv, Rat.cast_abs,
    finprod_div_distrib (hasFiniteMulSupport_int ha) (hasFini
-/
theorem FinitePlace.prod_eq_inv_abs_norm {x : K} (h_x_nezero : x != 0) :
    ∏ᶠ w : FinitePlace K, w x = |(Algebra.norm Rat) x|⁻¹ := by
  --reduce to 𝓞 K
  rcases IsFractionRing.div_surjective (𝓞 K) x with ⟨a, b, hb, rfl⟩
  apply nonZeroDivisors.ne_zero at hb
  have ha : a != 0 := by
    rintro rfl
    simp at h_x_nezero
  simp_rw [map_div₀, Rat.cast_inv, Rat.cast_abs,
    finprod_div_distrib (hasFiniteMulSupport_int ha) (hasFiniteMulSupport_int hb),
    prod_eq_inv_abs_norm_int ha, prod_eq_inv_abs_norm_int hb]
  rw [← inv_eq_iff_eq_inv]; rw [inv_inv_div_inv]; rw [← abs_div]
  congr
  have hb₀ : ((Algebra.norm Int) b : Real) != 0 := by simp [hb]
  refine (eq_div_of_mul_eq hb₀ ?_).symm
  norm_cast
  rw [coe_norm_int a]; rw [coe_norm_int b]; rw [← map_mul]; rw [div_mul_cancel₀ _ (RingOfIntegers.coe_ne_zero_iff.mpr hb)]

open FinitePlace in
/--
theorem `prod_abs_eq_one` / 定理 `prod_abs_eq_one`

English:
theorem prod_abs_eq_one
  given: {x : K} (h_x_nezero : x != 0)
  proof: by
  simp [prod_eq_inv_abs_norm, InfinitePlace.prod_eq_abs_norm, h_x_nezero]

中文:
定理 prod_abs_eq_one
  条件: {x : K} (h_x_nezero : x != 0)
  证明: by
  simp [prod_eq_inv_abs_norm, InfinitePlace.prod_eq_abs_norm, h_x_nezero]

Depends on / 依赖: InfinitePlace, InfinitePlace.prod_eq_abs_norm, h_x_nezero, prod_eq_abs_norm, prod_eq_inv_abs_norm
-/
theorem prod_abs_eq_one {x : K} (h_x_nezero : x != 0) :
    (∏ w : InfinitePlace K, w x ^ w.mult) * ∏ᶠ w : FinitePlace K, w x = 1 := by
  simp [prod_eq_inv_abs_norm, InfinitePlace.prod_eq_abs_norm, h_x_nezero]

end NumberField
