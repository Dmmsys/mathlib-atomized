/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Fabrizio Barroero, Christopher Hoskin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Order.Interval.Set.Defs

/-!
# circleMap

This file defines the circle map $θ ↦ c + R e^{θi}$, a parametrization of a circle.

## Main definitions

* `circleMap c R`: the exponential map $θ ↦ c + R e^{θi}$.

## Tags

-/

@[expose] public section
noncomputable section circleMap

open Complex ComplexConjugate Function Metric Real

/--
Definition of `circleMap` / `circleMap` 的定义

English:
definition circleMap
  signature: (c : Complex) (R : Real)
  body: fun θ => c + R * exp (θ * I)

@[simp]

中文:
定义 circleMap
  签名: (c : 复形) (R : 实数)
  定义体: fun θ => c + R * exp (θ * I)

@[simp]
-/
def circleMap (c : Complex) (R : Real) : Real -> Complex := fun θ => c + R * exp (θ * I)

@[simp]
/--
theorem `circleMap_sub_center` / 定理 `circleMap_sub_center`

English:
theorem circleMap_sub_center
  given: (c : Complex) (R : Real) (θ : Real)
  statement: circleMap c R θ - c = circleMap 0 R θ
  proof: by
  simp [circleMap]

中文:
定理 circleMap_sub_center
  条件: (c : 复形) (R : 实数) (θ : 实数)
  结论: circleMap c R θ - c = circleMap 0 R θ
  证明: by
  simp [circleMap]

Depends on / 依赖: circleMap
-/
theorem circleMap_sub_center (c : Complex) (R : Real) (θ : Real) : circleMap c R θ - c = circleMap 0 R θ := by
  simp [circleMap]

/--
theorem `circleMap_zero` / 定理 `circleMap_zero`

English:
theorem circleMap_zero
  given: (R θ : Real)
  statement: circleMap 0 R θ = R * exp (θ * I)
  proof: zero_add _

@[simp]

中文:
定理 circleMap_zero
  条件: (R θ : 实数)
  结论: circleMap 0 R θ = R * exp (θ * I)
  证明: zero_add _

@[simp]

Depends on / 依赖: zero_add
-/
theorem circleMap_zero (R θ : Real) : circleMap 0 R θ = R * exp (θ * I) := zero_add _

@[simp]
/--
theorem `norm_circleMap_zero` / 定理 `norm_circleMap_zero`

English:
theorem norm_circleMap_zero
  given: (R : Real) (θ : Real)
  statement: ‖circleMap 0 R θ‖ = |R|
  proof: by simp [circleMap]

中文:
定理 norm_circleMap_zero
  条件: (R : 实数) (θ : 实数)
  结论: ‖circleMap 0 R θ‖ = |R|
  证明: by simp [circleMap]

Depends on / 依赖: circleMap
-/
theorem norm_circleMap_zero (R : Real) (θ : Real) : ‖circleMap 0 R θ‖ = |R| := by simp [circleMap]

/--
theorem `circleMap_notMem_ball` / 定理 `circleMap_notMem_ball`

English:
theorem circleMap_notMem_ball
  given: (c : Complex) (R : Real) (θ : Real)
  statement: circleMap c R θ ∉ ball c R
  proof: by
  simp [Complex.dist_eq, le_abs_self]

中文:
定理 circleMap_notMem_ball
  条件: (c : 复形) (R : 实数) (θ : 实数)
  结论: circleMap c R θ ∉ ball c R
  证明: by
  simp [Complex.dist_eq, le_abs_self]

Depends on / 依赖: Complex.dist_eq, dist_eq, le_abs_self
-/
theorem circleMap_notMem_ball (c : Complex) (R : Real) (θ : Real) : circleMap c R θ ∉ ball c R := by
  simp [Complex.dist_eq, le_abs_self]

/--
theorem `circleMap_ne_mem_ball` / 定理 `circleMap_ne_mem_ball`

English:
theorem circleMap_ne_mem_ball
  given: {c : Complex} {R : Real} {w : Complex} (hw : w in ball c R) (θ : Real)
  proof: (ne_of_mem_of_not_mem hw (circleMap_notMem_ball _ _ _)).symm

中文:
定理 circleMap_ne_mem_ball
  条件: {c : 复形} {R : 实数} {w : 复形} (hw : w in ball c R) (θ : 实数)
  证明: (ne_of_mem_of_not_mem hw (circleMap_notMem_ball _ _ _)).symm

Depends on / 依赖: circleMap_notMem_ball, ne_of_mem_of_not_mem
-/
theorem circleMap_ne_mem_ball {c : Complex} {R : Real} {w : Complex} (hw : w in ball c R) (θ : Real) :
    circleMap c R θ != w :=
  (ne_of_mem_of_not_mem hw (circleMap_notMem_ball _ _ _)).symm

/--
theorem `circleMap_mem_sphere'` / 定理 `circleMap_mem_sphere'`

English:
theorem circleMap_mem_sphere'
  given: (c : Complex) (R : Real) (θ : Real)
  statement: circleMap c R θ in sphere c |R|
  proof: by simp

中文:
定理 circleMap_mem_sphere'
  条件: (c : 复形) (R : 实数) (θ : 实数)
  结论: circleMap c R θ in sphere c |R|
  证明: by simp
-/
theorem circleMap_mem_sphere' (c : Complex) (R : Real) (θ : Real) : circleMap c R θ in sphere c |R| := by simp

/--
theorem `circleMap_mem_sphere` / 定理 `circleMap_mem_sphere`

English:
theorem circleMap_mem_sphere
  given: (c : Complex) {R : Real} (hR : 0 <= R) (θ : Real)
  proof: by
  simpa only [abs_of_nonneg hR] using circleMap_mem_sphere' c R θ

中文:
定理 circleMap_mem_sphere
  条件: (c : 复形) {R : 实数} (hR : 0 <= R) (θ : 实数)
  证明: by
  simpa only [abs_of_nonneg hR] using circleMap_mem_sphere' c R θ

Depends on / 依赖: abs_of_nonneg, circleMap_mem_sphere
-/
theorem circleMap_mem_sphere (c : Complex) {R : Real} (hR : 0 <= R) (θ : Real) :
    circleMap c R θ in sphere c R := by
  simpa only [abs_of_nonneg hR] using circleMap_mem_sphere' c R θ

/--
theorem `circleMap_mem_closedBall` / 定理 `circleMap_mem_closedBall`

English:
theorem circleMap_mem_closedBall
  given: (c : Complex) {R : Real} (hR : 0 <= R) (θ : Real)
  proof: sphere_subset_closedBall (circleMap_mem_sphere c hR θ)

@[simp]

中文:
定理 circleMap_mem_closedBall
  条件: (c : 复形) {R : 实数} (hR : 0 <= R) (θ : 实数)
  证明: sphere_subset_closedBall (circleMap_mem_sphere c hR θ)

@[simp]

Depends on / 依赖: circleMap_mem_sphere, sphere_subset_closedBall
-/
theorem circleMap_mem_closedBall (c : Complex) {R : Real} (hR : 0 <= R) (θ : Real) :
    circleMap c R θ in closedBall c R :=
  sphere_subset_closedBall (circleMap_mem_sphere c hR θ)

@[simp]
/--
theorem `circleMap_eq_center_iff` / 定理 `circleMap_eq_center_iff`

English:
theorem circleMap_eq_center_iff
  given: {c : Complex} {R : Real} {θ : Real}
  statement: circleMap c R θ = c ↔ R = 0
  proof: by
  simp [circleMap, Complex.exp_ne_zero]

@[simp]

中文:
定理 circleMap_eq_center_iff
  条件: {c : 复形} {R : 实数} {θ : 实数}
  结论: circleMap c R θ = c ↔ R = 0
  证明: by
  simp [circleMap, Complex.exp_ne_zero]

@[simp]

Depends on / 依赖: Complex.exp_ne_zero, circleMap, exp_ne_zero
-/
theorem circleMap_eq_center_iff {c : Complex} {R : Real} {θ : Real} : circleMap c R θ = c ↔ R = 0 := by
  simp [circleMap, Complex.exp_ne_zero]

@[simp]
/--
theorem `circleMap_zero_radius` / 定理 `circleMap_zero_radius`

English:
theorem circleMap_zero_radius
  given: (c : Complex)
  statement: circleMap c 0 = const Real c
  proof: funext fun _ => circleMap_eq_center_iff.2 rfl

中文:
定理 circleMap_zero_radius
  条件: (c : 复形)
  结论: circleMap c 0 = const 实数 c
  证明: funext fun _ => circleMap_eq_center_iff.2 rfl

Depends on / 依赖: circleMap_eq_center_iff
-/
theorem circleMap_zero_radius (c : Complex) : circleMap c 0 = const Real c :=
  funext fun _ => circleMap_eq_center_iff.2 rfl

/--
theorem `circleMap_ne_center` / 定理 `circleMap_ne_center`

English:
theorem circleMap_ne_center
  given: {c : Complex} {R : Real} (hR : R != 0) {θ : Real}
  statement: circleMap c R θ != c
  proof: mt circleMap_eq_center_iff.1 hR

中文:
定理 circleMap_ne_center
  条件: {c : 复形} {R : 实数} (hR : R != 0) {θ : 实数}
  结论: circleMap c R θ != c
  证明: mt circleMap_eq_center_iff.1 hR

Depends on / 依赖: circleMap_eq_center_iff
-/
theorem circleMap_ne_center {c : Complex} {R : Real} (hR : R != 0) {θ : Real} : circleMap c R θ != c :=
  mt circleMap_eq_center_iff.1 hR

/--
lemma `circleMap_zero_mul` / 引理 `circleMap_zero_mul`

English:
lemma circleMap_zero_mul
  given: (R₁ R₂ θ₁ θ₂ : Real)
  proof: by
  simp only [circleMap_zero, ofReal_mul, ofReal_add, add_mul, Complex.exp_add]
  ring

中文:
引理 circleMap_zero_mul
  条件: (R₁ R₂ θ₁ θ₂ : 实数)
  证明: by
  simp only [circleMap_zero, ofReal_mul, ofReal_add, add_mul, Complex.exp_add]
  ring

Depends on / 依赖: Complex.exp_add, add_mul, circleMap_zero, exp_add, ofReal_add, ofReal_mul
-/
lemma circleMap_zero_mul (R₁ R₂ θ₁ θ₂ : Real) :
    (circleMap 0 R₁ θ₁) * (circleMap 0 R₂ θ₂) = circleMap 0 (R₁ * R₂) (θ₁ + θ₂) := by
  simp only [circleMap_zero, ofReal_mul, ofReal_add, add_mul, Complex.exp_add]
  ring

/--
lemma `circleMap_zero_div` / 引理 `circleMap_zero_div`

English:
lemma circleMap_zero_div
  given: (R₁ R₂ θ₁ θ₂ : Real)
  proof: by
  simp only [circleMap_zero, ofReal_div, ofReal_sub, sub_mul, Complex.exp_sub]
  ring

中文:
引理 circleMap_zero_div
  条件: (R₁ R₂ θ₁ θ₂ : 实数)
  证明: by
  simp only [circleMap_zero, ofReal_div, ofReal_sub, sub_mul, Complex.exp_sub]
  ring

Depends on / 依赖: Complex.exp_sub, circleMap_zero, exp_sub, ofReal_div, ofReal_sub, sub_mul
-/
lemma circleMap_zero_div (R₁ R₂ θ₁ θ₂ : Real) :
    (circleMap 0 R₁ θ₁) / (circleMap 0 R₂ θ₂) = circleMap 0 (R₁ / R₂) (θ₁ - θ₂) := by
  simp only [circleMap_zero, ofReal_div, ofReal_sub, sub_mul, Complex.exp_sub]
  ring

/--
lemma `circleMap_zero_inv` / 引理 `circleMap_zero_inv`

English:
lemma circleMap_zero_inv
  given: (R θ : Real)
  statement: (circleMap 0 R θ)⁻¹ = circleMap 0 R⁻¹ (-θ)
  proof: by
  simp [circleMap_zero, Complex.exp_neg, mul_comm]

中文:
引理 circleMap_zero_inv
  条件: (R θ : 实数)
  结论: (circleMap 0 R θ)⁻¹ = circleMap 0 R⁻¹ (-θ)
  证明: by
  simp [circleMap_zero, Complex.exp_neg, mul_comm]

Depends on / 依赖: Complex.exp_neg, circleMap_zero, exp_neg, mul_comm
-/
lemma circleMap_zero_inv (R θ : Real) : (circleMap 0 R θ)⁻¹ = circleMap 0 R⁻¹ (-θ) := by
  simp [circleMap_zero, Complex.exp_neg, mul_comm]

/--
lemma `circleMap_zero_pow` / 引理 `circleMap_zero_pow`

English:
lemma circleMap_zero_pow
  given: (n : Nat) (R θ : Real)
  proof: by
  simp [circleMap_zero, mul_pow, ← Complex.exp_nat_mul, ← mul_assoc]

中文:
引理 circleMap_zero_pow
  条件: (n : 自然数) (R θ : 实数)
  证明: by
  simp [circleMap_zero, mul_pow, ← Complex.exp_nat_mul, ← mul_assoc]

Depends on / 依赖: Complex.exp_nat_mul, circleMap_zero, exp_nat_mul, mul_assoc, mul_pow
-/
lemma circleMap_zero_pow (n : Nat) (R θ : Real) :
    (circleMap 0 R θ) ^ n = circleMap 0 (R ^ n) (n * θ) := by
  simp [circleMap_zero, mul_pow, ← Complex.exp_nat_mul, ← mul_assoc]

/--
lemma `circleMap_zero_zpow` / 引理 `circleMap_zero_zpow`

English:
lemma circleMap_zero_zpow
  given: (n : Int) (R θ : Real)
  proof: by
  simp [circleMap_zero, mul_zpow, ← exp_int_mul, ← mul_assoc]

中文:
引理 circleMap_zero_zpow
  条件: (n : 整数) (R θ : 实数)
  证明: by
  simp [circleMap_zero, mul_zpow, ← exp_int_mul, ← mul_assoc]

Depends on / 依赖: circleMap_zero, exp_int_mul, mul_assoc, mul_zpow
-/
lemma circleMap_zero_zpow (n : Int) (R θ : Real) :
    (circleMap 0 R θ) ^ n = circleMap 0 (R ^ n) (n * θ) := by
  simp [circleMap_zero, mul_zpow, ← exp_int_mul, ← mul_assoc]

/--
lemma `conj_circleMap_zero` / 引理 `conj_circleMap_zero`

English:
lemma conj_circleMap_zero
  given: (r θ : Real)
  proof: by
  simp [circleMap_zero, ← exp_conj]

中文:
引理 conj_circleMap_zero
  条件: (r θ : 实数)
  证明: by
  simp [circleMap_zero, ← exp_conj]

Depends on / 依赖: circleMap_zero, exp_conj
-/
lemma conj_circleMap_zero (r θ : Real) :
    conj (circleMap 0 r θ) = circleMap 0 r (-θ) := by
  simp [circleMap_zero, ← exp_conj]

/--
lemma `conj_circleMap` / 引理 `conj_circleMap`

English:
lemma conj_circleMap
  given: (c : Complex) (r θ : Real)
  proof: sub_left_injective (b := conj c) by simp [← map_sub, conj_circleMap_zero]

中文:
引理 conj_circleMap
  条件: (c : 复形) (r θ : 实数)
  证明: sub_left_injective (b := conj c) by simp [← map_sub, conj_circleMap_zero]

Depends on / 依赖: conj_circleMap_zero, map_sub, sub_left_injective
-/
lemma conj_circleMap (c : Complex) (r θ : Real) :
    conj (circleMap c r θ) = circleMap (conj c) r (-θ) :=
sub_left_injective (b := conj c) by simp [← map_sub, conj_circleMap_zero]

/--
lemma `circleMap_zero_re` / 引理 `circleMap_zero_re`

English:
lemma circleMap_zero_re
  given: (r θ : Real)
  statement: (circleMap 0 r θ).re = r * Real.cos θ
  proof: by
  simp [circleMap_zero]

中文:
引理 circleMap_zero_re
  条件: (r θ : 实数)
  结论: (circleMap 0 r θ).re = r * 实数.cos θ
  证明: by
  simp [circleMap_zero]

Depends on / 依赖: circleMap_zero
-/
lemma circleMap_zero_re (r θ : Real) : (circleMap 0 r θ).re = r * Real.cos θ := by
  simp [circleMap_zero]

/--
lemma `circleMap_zero_im` / 引理 `circleMap_zero_im`

English:
lemma circleMap_zero_im
  given: (r θ : Real)
  statement: (circleMap 0 r θ).im = r * Real.sin θ
  proof: by
  simp [circleMap_zero]

中文:
引理 circleMap_zero_im
  条件: (r θ : 实数)
  结论: (circleMap 0 r θ).im = r * 实数.sin θ
  证明: by
  simp [circleMap_zero]

Depends on / 依赖: circleMap_zero
-/
lemma circleMap_zero_im (r θ : Real) : (circleMap 0 r θ).im = r * Real.sin θ := by
  simp [circleMap_zero]

/--
lemma `circleMap_pi_div_two` / 引理 `circleMap_pi_div_two`

English:
lemma circleMap_pi_div_two
  given: (c : Complex) (R : Real)
  statement: circleMap c R (π / 2) = c + R * I
  proof: by
  simp only [circleMap, ofReal_div, ofReal_ofNat, exp_pi_div_two_mul_I]

中文:
引理 circleMap_pi_div_two
  条件: (c : 复形) (R : 实数)
  结论: circleMap c R (π / 2) = c + R * I
  证明: by
  simp only [circleMap, ofReal_div, ofReal_ofNat, exp_pi_div_two_mul_I]

Depends on / 依赖: circleMap, exp_pi_div_two_mul_I, ofReal_div, ofReal_ofNat
-/
lemma circleMap_pi_div_two (c : Complex) (R : Real) : circleMap c R (π / 2) = c + R * I := by
  simp only [circleMap, ofReal_div, ofReal_ofNat, exp_pi_div_two_mul_I]

/--
lemma `circleMap_neg_pi_div_two` / 引理 `circleMap_neg_pi_div_two`

English:
lemma circleMap_neg_pi_div_two
  given: (c : Complex) (R : Real)
  statement: circleMap c R (-π / 2) = c - R * I
  proof: by
  simp only [circleMap, ofReal_div, ofReal_neg, ofReal_ofNat, exp_neg_pi_div_two_mul_I, mul_neg,
    sub_eq_add_neg]

中文:
引理 circleMap_neg_pi_div_two
  条件: (c : 复形) (R : 实数)
  结论: circleMap c R (-π / 2) = c - R * I
  证明: by
  simp only [circleMap, ofReal_div, ofReal_neg, ofReal_ofNat, exp_neg_pi_div_two_mul_I, mul_neg,
    sub_eq_add_neg]

Depends on / 依赖: circleMap, exp_neg_pi_div_two_mul_I, mul_neg, ofReal_div, ofReal_neg, ofReal_ofNat, sub_eq_add_neg
-/
lemma circleMap_neg_pi_div_two (c : Complex) (R : Real) : circleMap c R (-π / 2) = c - R * I := by
  simp only [circleMap, ofReal_div, ofReal_neg, ofReal_ofNat, exp_neg_pi_div_two_mul_I, mul_neg,
    sub_eq_add_neg]

/--
theorem `periodic_circleMap` / 定理 `periodic_circleMap`

English:
theorem periodic_circleMap
  given: (c : Complex) (R : Real)
  statement: Periodic (circleMap c R) (2 * π)
  proof: fun θ => by
  simp [circleMap, add_mul, exp_periodic _]

中文:
定理 periodic_circleMap
  条件: (c : 复形) (R : 实数)
  结论: 周期 (circleMap c R) (2 * π)
  证明: fun θ => by
  simp [circleMap, add_mul, exp_periodic _]

Depends on / 依赖: add_mul, circleMap, exp_periodic
-/
theorem periodic_circleMap (c : Complex) (R : Real) : Periodic (circleMap c R) (2 * π) := fun θ => by
  simp [circleMap, add_mul, exp_periodic _]

/--
theorem `Set.Countable.preimage_circleMap` / 定理 `Set.Countable.preimage_circleMap`

English:
theorem Set.Countable.preimage_circleMap
  statement: {s : Set Complex} (hs : s.Countable) (c : Complex) {R : Real}
  proof: show (((↑) : Real -> Complex) ⁻¹' ((· * I) ⁻¹'
      (exp ⁻¹' ((R * ·) ⁻¹' ((c + ·) ⁻¹' s))))).Countable from
    (((hs.preimage (add_right_injective _)).preimage <|
mul_right_injective₀ ofReal_ne_zero.2 hR).preimage_cexp.preimage <|
        mul_left_injective₀ I_ne_zero).preimage ofReal_injective

中文:
定理 集合.可数.preimage_circleMap
  结论: {s : 集合 复形} (hs : s.可数) (c : 复形) {R : 实数}
  证明: show (((↑) : Real -> Complex) ⁻¹' ((· * I) ⁻¹'
      (exp ⁻¹' ((R * ·) ⁻¹' ((c + ·) ⁻¹' s))))).Countable from
    (((hs.preimage (add_right_injective _)).preimage <|
mul_right_injective₀ ofReal_ne_zero.2 hR).preimage_cexp.preimage <|
        mul_left_injective₀ I_ne_zero).preimage ofReal_injective

Depends on / 依赖: Countable, I_ne_zero, add_right_injective, hs.preimage, ofReal_injective, ofReal_ne_zero, preimage, preimage_cexp, preimage_cexp.preimage
-/
theorem Set.Countable.preimage_circleMap {s : Set Complex} (hs : s.Countable) (c : Complex) {R : Real}
    (hR : R != 0) : (circleMap c R ⁻¹' s).Countable :=
  show (((↑) : Real -> Complex) ⁻¹' ((· * I) ⁻¹'
      (exp ⁻¹' ((R * ·) ⁻¹' ((c + ·) ⁻¹' s))))).Countable from
    (((hs.preimage (add_right_injective _)).preimage <|
mul_right_injective₀ ofReal_ne_zero.2 hR).preimage_cexp.preimage <|
        mul_left_injective₀ I_ne_zero).preimage ofReal_injective

/--
lemma `circleMap_eq_circleMap_iff` / 引理 `circleMap_eq_circleMap_iff`

English:
lemma circleMap_eq_circleMap_iff
  given: {a b R : Real} (c : Complex) (h_R : R != 0)
  proof: by
  have : circleMap c R a = circleMap c R b ↔ (exp (a * I)).arg = (exp (b * I)).arg := by
    simp [circleMap, ext_norm_arg_iff, h_R]
  simp [this, arg_eq_arg_iff, exp_eq_exp_iff_exists_int]

中文:
引理 circleMap_eq_circleMap_iff
  条件: {a b R : 实数} (c : 复形) (h_R : R != 0)
  证明: by
  have : circleMap c R a = circleMap c R b ↔ (exp (a * I)).arg = (exp (b * I)).arg := by
    simp [circleMap, ext_norm_arg_iff, h_R]
  simp [this, arg_eq_arg_iff, exp_eq_exp_iff_exists_int]

Depends on / 依赖: arg_eq_arg_iff, circleMap, exp_eq_exp_iff_exists_int, ext_norm_arg_iff
-/
lemma circleMap_eq_circleMap_iff {a b R : Real} (c : Complex) (h_R : R != 0) :
    circleMap c R a = circleMap c R b ↔ exists (n : Int), a * I = b * I + n * (2 * π * I) := by
  have : circleMap c R a = circleMap c R b ↔ (exp (a * I)).arg = (exp (b * I)).arg := by
    simp [circleMap, ext_norm_arg_iff, h_R]
  simp [this, arg_eq_arg_iff, exp_eq_exp_iff_exists_int]

/--
lemma `eq_of_circleMap_eq` / 引理 `eq_of_circleMap_eq`

English:
lemma eq_of_circleMap_eq
  statement: {a b R : Real} {c : Complex} (h_R : R != 0) (h_dist : |a - b| < 2 * π)
  proof: by
  rw [circleMap_eq_circleMap_iff c h_R] at h
  obtain ⟨n, hn⟩ := h
  simp only [show n * (2 * π * I) = (n * 2 * π) * I by ring, ← add_mul, mul_eq_mul_right_iff,
    I_ne_zero, or_false] at hn
  norm_cast at hn
  simp only [hn, Int.cast_mul, Int.cast_ofNat, mul_assoc, add_sub_cancel_left, abs_mul,
    Nat.abs_ofNat, abs_of_pos Real.pi_pos] at h_dist
  simp (disch := positivity) at h_dist
  norm_cast at h_dist
  simp [hn, Int.abs_lt_one_iff.mp h_dist]

中文:
引理 eq_of_circleMap_eq
  结论: {a b R : 实数} {c : 复形} (h_R : R != 0) (h_dist : |a - b| < 2 * π)
  证明: by
  rw [circleMap_eq_circleMap_iff c h_R] at h
  obtain ⟨n, hn⟩ := h
  simp only [show n * (2 * π * I) = (n * 2 * π) * I by ring, ← add_mul, mul_eq_mul_right_iff,
    I_ne_zero, or_false] at hn
  norm_cast at hn
  simp only [hn, Int.cast_mul, Int.cast_ofNat, mul_assoc, add_sub_cancel_left, abs_mul,
    Nat.abs_ofNat, abs_of_pos Real.pi_pos] at h_dist
  simp (disch := positivity) at h_dist
  norm_cast at h_dist
  simp [hn, Int.abs_lt_one_iff.mp h_dist]

Depends on / 依赖: I_ne_zero, Int.abs_lt_one_iff.mp, Int.cast_mul, Int.cast_ofNat, Nat.abs_ofNat, Real.pi_pos, abs_lt_one_iff, abs_mul, abs_ofNat, abs_of_pos, add_mul, add_sub_cancel_left, cast_mul, cast_ofNat, circleMap_eq_circleMap_iff, h_dist, mul_assoc, mul_eq_mul_right_iff, or_false, pi_pos
-/
lemma eq_of_circleMap_eq {a b R : Real} {c : Complex} (h_R : R != 0) (h_dist : |a - b| < 2 * π)
    (h : circleMap c R a = circleMap c R b) : a = b := by
  rw [circleMap_eq_circleMap_iff c h_R] at h
  obtain ⟨n, hn⟩ := h
  simp only [show n * (2 * π * I) = (n * 2 * π) * I by ring, ← add_mul, mul_eq_mul_right_iff,
    I_ne_zero, or_false] at hn
  norm_cast at hn
  simp only [hn, Int.cast_mul, Int.cast_ofNat, mul_assoc, add_sub_cancel_left, abs_mul,
    Nat.abs_ofNat, abs_of_pos Real.pi_pos] at h_dist
  simp (disch := positivity) at h_dist
  norm_cast at h_dist
  simp [hn, Int.abs_lt_one_iff.mp h_dist]

open scoped Interval in
/--
theorem `injOn_circleMap_of_abs_sub_le` / 定理 `injOn_circleMap_of_abs_sub_le`

English:
theorem injOn_circleMap_of_abs_sub_le
  given: {a b R : Real} {c : Complex} (h_R : R != 0) (_ : |a - b| <= 2 * π)
  proof: by
  rintro _ ⟨_, _⟩ _ ⟨_, _⟩ h
  apply eq_of_circleMap_eq h_R _ h
  rw [abs_lt]
  constructor <;> linarith [max_sub_min_eq_abs' a b]

中文:
定理 injOn_circleMap_of_abs_sub_le
  条件: {a b R : 实数} {c : 复形} (h_R : R != 0) (_ : |a - b| <= 2 * π)
  证明: by
  rintro _ ⟨_, _⟩ _ ⟨_, _⟩ h
  apply eq_of_circleMap_eq h_R _ h
  rw [abs_lt]
  constructor <;> linarith [max_sub_min_eq_abs' a b]

Depends on / 依赖: abs_lt, eq_of_circleMap_eq, max_sub_min_eq_abs
-/
theorem injOn_circleMap_of_abs_sub_le {a b R : Real} {c : Complex} (h_R : R != 0) (_ : |a - b| <= 2 * π) :
    (Ι a b).InjOn (circleMap c R) := by
  rintro _ ⟨_, _⟩ _ ⟨_, _⟩ h
  apply eq_of_circleMap_eq h_R _ h
  rw [abs_lt]
  constructor <;> linarith [max_sub_min_eq_abs' a b]

/--
theorem `injOn_circleMap_of_abs_sub_le'` / 定理 `injOn_circleMap_of_abs_sub_le'`

English:
theorem injOn_circleMap_of_abs_sub_le'
  given: {a b R : Real} {c : Complex} (h_R : R != 0) (_ : b - a <= 2 * π)
  proof: by
  rintro _ ⟨_, _⟩ _ ⟨_, _⟩ h
  apply eq_of_circleMap_eq h_R _ h
  rw [abs_lt]
  constructor <;> linarith

中文:
定理 injOn_circleMap_of_abs_sub_le'
  条件: {a b R : 实数} {c : 复形} (h_R : R != 0) (_ : b - a <= 2 * π)
  证明: by
  rintro _ ⟨_, _⟩ _ ⟨_, _⟩ h
  apply eq_of_circleMap_eq h_R _ h
  rw [abs_lt]
  constructor <;> linarith

Depends on / 依赖: abs_lt, eq_of_circleMap_eq
-/
theorem injOn_circleMap_of_abs_sub_le' {a b R : Real} {c : Complex} (h_R : R != 0) (_ : b - a <= 2 * π) :
    (Set.Ico a b).InjOn (circleMap c R) := by
  rintro _ ⟨_, _⟩ _ ⟨_, _⟩ h
  apply eq_of_circleMap_eq h_R _ h
  rw [abs_lt]
  constructor <;> linarith

end circleMap
