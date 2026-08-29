/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The argument of a complex number.

We define `arg : ℂ → ℝ`, returning a real number in the range $(-π, π]$,
such that for `x ≠ 0`, `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
while `arg 0` defaults to `0`
-/

@[expose] public section

open Filter Metric Set
open scoped ComplexConjugate Real Topology

namespace Complex
variable {a x z : Complex}

/--
Definition of `arg` / `arg` 的定义

English:
definition arg
  signature: (x : Complex)
  body: if 0 <= x.re then Real.arcsin (x.im / ‖x‖)
  else if 0 <= x.im then Real.arcsin ((-x).im / ‖x‖) + π else Real.arcsin ((-x).im / ‖x‖) - π

中文:
定义 arg
  签名: (x : 复形)
  定义体: if 0 <= x.re then Real.arcsin (x.im / ‖x‖)
  else if 0 <= x.im then Real.arcsin ((-x).im / ‖x‖) + π else Real.arcsin ((-x).im / ‖x‖) - π

Depends on / 依赖: Real.arcsin, arcsin, x.im, x.re
-/
noncomputable def arg (x : Complex) : Real :=
  if 0 <= x.re then Real.arcsin (x.im / ‖x‖)
  else if 0 <= x.im then Real.arcsin ((-x).im / ‖x‖) + π else Real.arcsin ((-x).im / ‖x‖) - π

/--
theorem `sin_arg` / 定理 `sin_arg`

English:
theorem sin_arg
  given: (x : Complex)
  statement: Real.sin (arg x) = x.im / ‖x‖
  proof: by
  unfold arg; split_ifs <;>
    simp [sub_eq_add_neg, Real.sin_arcsin (abs_le.1 (abs_im_div_norm_le_one x)).1
      (abs_le.1 (abs_im_div_norm_le_one x)).2, Real.sin_add, neg_div, Real.arcsin_neg, Real.sin_neg]

中文:
定理 sin_arg
  条件: (x : 复形)
  结论: 实数.sin (arg x) = x.im / ‖x‖
  证明: by
  unfold arg; split_ifs <;>
    simp [sub_eq_add_neg, Real.sin_arcsin (abs_le.1 (abs_im_div_norm_le_one x)).1
      (abs_le.1 (abs_im_div_norm_le_one x)).2, Real.sin_add, neg_div, Real.arcsin_neg, Real.sin_neg]

Depends on / 依赖: Real.arcsin_neg, Real.sin_add, Real.sin_arcsin, Real.sin_neg, abs_im_div_norm_le_one, abs_le, arcsin_neg, neg_div, sin_add, sin_arcsin, sin_neg, split_ifs, sub_eq_add_neg
-/
theorem sin_arg (x : Complex) : Real.sin (arg x) = x.im / ‖x‖ := by
  unfold arg; split_ifs <;>
    simp [sub_eq_add_neg, Real.sin_arcsin (abs_le.1 (abs_im_div_norm_le_one x)).1
      (abs_le.1 (abs_im_div_norm_le_one x)).2, Real.sin_add, neg_div, Real.arcsin_neg, Real.sin_neg]

/--
theorem `cos_arg` / 定理 `cos_arg`

English:
theorem cos_arg
  given: {x : Complex} (hx : x != 0)
  statement: Real.cos (arg x) = x.re / ‖x‖
  proof: by
  rw [arg]
  split_ifs with h₁ h₂
  · rw [Real.cos_arcsin]
    field_simp
    simp [Real.sqrt_sq, (norm_pos_iff.mpr hx).le, *]
    field
  · rw [Real.cos_add_pi, Real.cos_arcsin]
    field_simp
    simp [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, _root_.abs_of_neg (not_le.1 h₁), *]
    fie

中文:
定理 cos_arg
  条件: {x : 复形} (hx : x != 0)
  结论: 实数.cos (arg x) = x.re / ‖x‖
  证明: by
  rw [arg]
  split_ifs with h₁ h₂
  · rw [Real.cos_arcsin]
    field_simp
    simp [Real.sqrt_sq, (norm_pos_iff.mpr hx).le, *]
    field
  · rw [Real.cos_add_pi, Real.cos_arcsin]
    field_simp
    simp [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, _root_.abs_of_neg (not_le.1 h₁), *]
    fie

Depends on / 依赖: Real.cos_add_pi, Real.cos_arcsin, Real.cos_sub_pi, Real.sqrt_div, Real.sqrt_sq, Real.sqrt_sq_eq_abs, _root_, _root_.abs_of_neg, abs_of_neg, cos_add_pi, cos_arcsin, cos_sub_pi, norm_pos_iff, norm_pos_iff.mpr, not_le, split_ifs, sq_nonneg, sqrt_div, sqrt_sq, sqrt_sq_eq_abs
-/
theorem cos_arg {x : Complex} (hx : x != 0) : Real.cos (arg x) = x.re / ‖x‖ := by
  rw [arg]
  split_ifs with h₁ h₂
  · rw [Real.cos_arcsin]
    field_simp
    simp [Real.sqrt_sq, (norm_pos_iff.mpr hx).le, *]
    field
  · rw [Real.cos_add_pi, Real.cos_arcsin]
    field_simp
    simp [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, _root_.abs_of_neg (not_le.1 h₁), *]
    field
  · rw [Real.cos_sub_pi, Real.cos_arcsin]
    field_simp
    simp [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, _root_.abs_of_neg (not_le.1 h₁), *]
    field

@[simp]
/--
theorem `norm_mul_exp_arg_mul_I` / 定理 `norm_mul_exp_arg_mul_I`

English:
theorem norm_mul_exp_arg_mul_I
  given: (x : Complex)
  statement: ‖x‖ * exp (arg x * I) = x
  proof: by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  · have : ‖x‖ != 0 := norm_ne_zero_iff.mpr hx
    apply Complex.ext <;> simp [sin_arg, cos_arg hx, this, mul_comm ‖x‖]

@[simp]

中文:
定理 norm_mul_exp_arg_mul_I
  条件: (x : 复形)
  结论: ‖x‖ * exp (arg x * I) = x
  证明: by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  · have : ‖x‖ != 0 := norm_ne_zero_iff.mpr hx
    apply Complex.ext <;> simp [sin_arg, cos_arg hx, this, mul_comm ‖x‖]

@[simp]

Depends on / 依赖: Complex.ext, cos_arg, eq_or_ne, mul_comm, norm_ne_zero_iff, norm_ne_zero_iff.mpr, sin_arg
-/
theorem norm_mul_exp_arg_mul_I (x : Complex) : ‖x‖ * exp (arg x * I) = x := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  · have : ‖x‖ != 0 := norm_ne_zero_iff.mpr hx
    apply Complex.ext <;> simp [sin_arg, cos_arg hx, this, mul_comm ‖x‖]

@[simp]
/--
theorem `norm_mul_cos_add_sin_mul_I` / 定理 `norm_mul_cos_add_sin_mul_I`

English:
theorem norm_mul_cos_add_sin_mul_I
  given: (x : Complex)
  statement: (‖x‖ * (cos (arg x) + sin (arg x) * I) : Complex) = x
  proof: by
  rw [← exp_mul_I]; rw [norm_mul_exp_arg_mul_I]

@[simp]

中文:
定理 norm_mul_cos_add_sin_mul_I
  条件: (x : 复形)
  结论: (‖x‖ * (cos (arg x) + sin (arg x) * I) : 复形) = x
  证明: by
  rw [← exp_mul_I]; rw [norm_mul_exp_arg_mul_I]

@[simp]

Depends on / 依赖: exp_mul_I, norm_mul_exp_arg_mul_I
-/
theorem norm_mul_cos_add_sin_mul_I (x : Complex) : (‖x‖ * (cos (arg x) + sin (arg x) * I) : Complex) = x := by
  rw [← exp_mul_I]; rw [norm_mul_exp_arg_mul_I]

@[simp]
/--
lemma `norm_mul_cos_arg` / 引理 `norm_mul_cos_arg`

English:
lemma norm_mul_cos_arg
  given: (x : Complex)
  statement: ‖x‖ * Real.cos (arg x) = x.re
  proof: by
  simpa [-norm_mul_cos_add_sin_mul_I] using! congr_arg re (norm_mul_cos_add_sin_mul_I x)

@[simp]

中文:
引理 norm_mul_cos_arg
  条件: (x : 复形)
  结论: ‖x‖ * 实数.cos (arg x) = x.re
  证明: by
  simpa [-norm_mul_cos_add_sin_mul_I] using! congr_arg re (norm_mul_cos_add_sin_mul_I x)

@[simp]

Depends on / 依赖: congr_arg, norm_mul_cos_add_sin_mul_I
-/
lemma norm_mul_cos_arg (x : Complex) : ‖x‖ * Real.cos (arg x) = x.re := by
  simpa [-norm_mul_cos_add_sin_mul_I] using! congr_arg re (norm_mul_cos_add_sin_mul_I x)

@[simp]
/--
lemma `norm_mul_sin_arg` / 引理 `norm_mul_sin_arg`

English:
lemma norm_mul_sin_arg
  given: (x : Complex)
  statement: ‖x‖ * Real.sin (arg x) = x.im
  proof: by
  simpa [-norm_mul_cos_add_sin_mul_I] using! congr_arg im (norm_mul_cos_add_sin_mul_I x)

中文:
引理 norm_mul_sin_arg
  条件: (x : 复形)
  结论: ‖x‖ * 实数.sin (arg x) = x.im
  证明: by
  simpa [-norm_mul_cos_add_sin_mul_I] using! congr_arg im (norm_mul_cos_add_sin_mul_I x)

Depends on / 依赖: congr_arg, norm_mul_cos_add_sin_mul_I
-/
lemma norm_mul_sin_arg (x : Complex) : ‖x‖ * Real.sin (arg x) = x.im := by
  simpa [-norm_mul_cos_add_sin_mul_I] using! congr_arg im (norm_mul_cos_add_sin_mul_I x)

/--
theorem `norm_eq_one_iff` / 定理 `norm_eq_one_iff`

English:
theorem norm_eq_one_iff
  given: (z : Complex)
  statement: ‖z‖ = 1 ↔ exists θ : Real, exp (θ * I) = z
  proof: by
  refine ⟨fun hz => ⟨arg z, ?_⟩, ?_⟩
  · calc
      exp (arg z * I) = ‖z‖ * exp (arg z * I) := by rw [hz, ofReal_one, one_mul]
      _ = z := norm_mul_exp_arg_mul_I z
  · rintro ⟨θ, rfl⟩
    exact Complex.norm_exp_ofReal_mul_I θ

@[simp]

中文:
定理 norm_eq_one_iff
  条件: (z : 复形)
  结论: ‖z‖ = 1 ↔ 存在 θ : 实数, exp (θ * I) = z
  证明: by
  refine ⟨fun hz => ⟨arg z, ?_⟩, ?_⟩
  · calc
      exp (arg z * I) = ‖z‖ * exp (arg z * I) := by rw [hz, ofReal_one, one_mul]
      _ = z := norm_mul_exp_arg_mul_I z
  · rintro ⟨θ, rfl⟩
    exact Complex.norm_exp_ofReal_mul_I θ

@[simp]

Depends on / 依赖: Complex.norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I, norm_mul_exp_arg_mul_I, ofReal_one, one_mul
-/
theorem norm_eq_one_iff (z : Complex) : ‖z‖ = 1 ↔ exists θ : Real, exp (θ * I) = z := by
  refine ⟨fun hz => ⟨arg z, ?_⟩, ?_⟩
  · calc
      exp (arg z * I) = ‖z‖ * exp (arg z * I) := by rw [hz, ofReal_one, one_mul]
      _ = z := norm_mul_exp_arg_mul_I z
  · rintro ⟨θ, rfl⟩
    exact Complex.norm_exp_ofReal_mul_I θ

@[simp]
/--
theorem `range_exp_mul_I` / 定理 `range_exp_mul_I`

English:
theorem range_exp_mul_I
  statement: (Set.range fun x : Real => exp (x * I)) = Metric.sphere 0 1
  proof: by
  ext x
  simp only [mem_sphere_zero_iff_norm, norm_eq_one_iff, Set.mem_range]

中文:
定理 range_exp_mul_I
  结论: (集合.range fun x : 实数 => exp (x * I)) = Metric.sphere 0 1
  证明: by
  ext x
  simp only [mem_sphere_zero_iff_norm, norm_eq_one_iff, Set.mem_range]

Depends on / 依赖: Set.mem_range, mem_range, mem_sphere_zero_iff_norm, norm_eq_one_iff
-/
theorem range_exp_mul_I : (Set.range fun x : Real => exp (x * I)) = Metric.sphere 0 1 := by
  ext x
  simp only [mem_sphere_zero_iff_norm, norm_eq_one_iff, Set.mem_range]

/--
theorem `arg_mul_cos_add_sin_mul_I` / 定理 `arg_mul_cos_add_sin_mul_I`

English:
theorem arg_mul_cos_add_sin_mul_I
  given: {r : Real} (hr : 0 < r) {θ : Real} (hθ : θ in Set.Ioc (-π) π)
  proof: by
  simp only [arg, norm_mul, norm_cos_add_sin_mul_I, Complex.norm_of_nonneg hr.le, mul_one]
  simp only [re_ofReal_mul, im_ofReal_mul, neg_im, ← ofReal_cos, ← ofReal_sin, ←
    mk_eq_add_mul_I, neg_div, mul_div_cancel_left₀ _ hr.ne', mul_nonneg_iff_right_nonneg_of_pos hr]
  by_cases h₁ : θ in Set.

中文:
定理 arg_mul_cos_add_sin_mul_I
  条件: {r : 实数} (hr : 0 < r) {θ : 实数} (hθ : θ in 集合.左开右闭区间 (-π) π)
  证明: by
  simp only [arg, norm_mul, norm_cos_add_sin_mul_I, Complex.norm_of_nonneg hr.le, mul_one]
  simp only [re_ofReal_mul, im_ofReal_mul, neg_im, ← ofReal_cos, ← ofReal_sin, ←
    mk_eq_add_mul_I, neg_div, mul_div_cancel_left₀ _ hr.ne', mul_nonneg_iff_right_nonneg_of_pos hr]
  by_cases h₁ : θ in Set.

Depends on / 依赖: Arrow.isIso_iff_isIso_of_isIso, Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right, Complex.norm_of_nonneg, Ind.exists_nonempty_arrow_mk_iso_ind_lim, Ind.lim, Iso.isIso_hom, PreservesCoimageImageComparison, PreservesCoimageImageComparison.iso, Real.arcsin_sin, Real.cos_nonneg_of_mem_Icc, Set.Icc, Set.mem_Icc, arcsin_sin, coimageImageComparisonFunctor, coimageImageComparisonFunctor.mapIso, coimageImageComparisonFunctor_obj, cos_nonneg_of_mem_Icc, exacts
-/
theorem arg_mul_cos_add_sin_mul_I {r : Real} (hr : 0 < r) {θ : Real} (hθ : θ in Set.Ioc (-π) π) :
    arg (r * (cos θ + sin θ * I)) = θ := by
  simp only [arg, norm_mul, norm_cos_add_sin_mul_I, Complex.norm_of_nonneg hr.le, mul_one]
  simp only [re_ofReal_mul, im_ofReal_mul, neg_im, ← ofReal_cos, ← ofReal_sin, ←
    mk_eq_add_mul_I, neg_div, mul_div_cancel_left₀ _ hr.ne', mul_nonneg_iff_right_nonneg_of_pos hr]
  by_cases h₁ : θ in Set.Icc (-(π / 2)) (π / 2)
  · rw [if_pos]
    exacts [Real.arcsin_sin' h₁, Real.cos_nonneg_of_mem_Icc h₁]
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at h₁
    rcases h₁ with h₁ | h₁
    · replace hθ := hθ.1
      have hcos : Real.cos θ < 0 := by
        rw [← neg_pos]; rw [← Real.cos_add_pi]
        refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;> linarith
      have hsin : Real.sin θ < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) hθ
      rw [if_neg]; rw [if_neg]; rw [← Real.sin_add_pi]; rw [Real.arcsin_sin]; rw [add_sub_cancel_right] <;> [linarith;
        linarith; exact hsin.not_ge; exact hcos.not_ge]
    · replace hθ := hθ.2
      have hcos : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt h₁ (by linarith)
      have hsin : 0 <= Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨by linarith, hθ⟩
      rw [if_neg]; rw [if_pos]; rw [← Real.sin_sub_pi]; rw [Real.arcsin_sin]; rw [sub_add_cancel] <;> [linarith;
        linarith; exact hsin; exact hcos.not_ge]

/--
theorem `arg_cos_add_sin_mul_I` / 定理 `arg_cos_add_sin_mul_I`

English:
theorem arg_cos_add_sin_mul_I
  given: {θ : Real} (hθ : θ in Set.Ioc (-π) π)
  statement: arg (cos θ + sin θ * I) = θ
  proof: by
  rw [← one_mul (_ + _)]; rw [← ofReal_one]; rw [arg_mul_cos_add_sin_mul_I zero_lt_one hθ]

中文:
定理 arg_cos_add_sin_mul_I
  条件: {θ : 实数} (hθ : θ in 集合.左开右闭区间 (-π) π)
  结论: arg (cos θ + sin θ * I) = θ
  证明: by
  rw [← one_mul (_ + _)]; rw [← ofReal_one]; rw [arg_mul_cos_add_sin_mul_I zero_lt_one hθ]

Depends on / 依赖: arg_mul_cos_add_sin_mul_I, ofReal_one, one_mul, zero_lt_one
-/
theorem arg_cos_add_sin_mul_I {θ : Real} (hθ : θ in Set.Ioc (-π) π) : arg (cos θ + sin θ * I) = θ := by
  rw [← one_mul (_ + _)]; rw [← ofReal_one]; rw [arg_mul_cos_add_sin_mul_I zero_lt_one hθ]

/--
theorem `arg_exp` / 定理 `arg_exp`

English:
theorem arg_exp
  given: (z : Complex)
  statement: arg (exp z) = toIocMod Real.two_pi_pos (-π) z.im
  proof: by
  convert!
    arg_mul_cos_add_sin_mul_I (Real.exp_pos z.re) (θ := toIocMod Real.two_pi_pos (-π) z.im) _
    using 1
  · rw [← exp_mul_I, ofReal_exp, toIocMod]
    push_cast
    rw [exp_mul_I_periodic.sub_zsmul_eq]; rw [← exp_add]; rw [re_add_im]
  · convert! toIocMod_mem_Ioc ..
    ring

中文:
定理 arg_exp
  条件: (z : 复形)
  结论: arg (exp z) = toIocMod 实数.two_pi_pos (-π) z.im
  证明: by
  convert!
    arg_mul_cos_add_sin_mul_I (Real.exp_pos z.re) (θ := toIocMod Real.two_pi_pos (-π) z.im) _
    using 1
  · rw [← exp_mul_I, ofReal_exp, toIocMod]
    push_cast
    rw [exp_mul_I_periodic.sub_zsmul_eq]; rw [← exp_add]; rw [re_add_im]
  · convert! toIocMod_mem_Ioc ..
    ring

Depends on / 依赖: Real.exp_pos, Real.two_pi_pos, arg_mul_cos_add_sin_mul_I, convert, exp_add, exp_mul_I, exp_mul_I_periodic, exp_mul_I_periodic.sub_zsmul_eq, exp_pos, ofReal_exp, re_add_im, sub_zsmul_eq, toIocMod, toIocMod_mem_Ioc, two_pi_pos, z.im, z.re
-/
theorem arg_exp (z : Complex) : arg (exp z) = toIocMod Real.two_pi_pos (-π) z.im := by
  convert!
    arg_mul_cos_add_sin_mul_I (Real.exp_pos z.re) (θ := toIocMod Real.two_pi_pos (-π) z.im) _
    using 1
  · rw [← exp_mul_I, ofReal_exp, toIocMod]
    push_cast
    rw [exp_mul_I_periodic.sub_zsmul_eq]; rw [← exp_add]; rw [re_add_im]
  · convert! toIocMod_mem_Ioc ..
    ring

/--
lemma `arg_exp_mul_I` / 引理 `arg_exp_mul_I`

English:
lemma arg_exp_mul_I
  given: (θ : Real)
  proof: by
  simp [arg_exp]

@[simp]

中文:
引理 arg_exp_mul_I
  条件: (θ : 实数)
  证明: by
  simp [arg_exp]

@[simp]

Depends on / 依赖: arg_exp
-/
lemma arg_exp_mul_I (θ : Real) :
    arg (exp (θ * I)) = toIocMod Real.two_pi_pos (-π) θ := by
  simp [arg_exp]

@[simp]
/--
theorem `arg_zero` / 定理 `arg_zero`

English:
theorem arg_zero
  statement: arg 0 = 0
  proof: by simp [arg]

中文:
定理 arg_zero
  结论: arg 0 = 0
  证明: by simp [arg]
-/
theorem arg_zero : arg 0 = 0 := by simp [arg]

/--
theorem `ext_norm_arg` / 定理 `ext_norm_arg`

English:
theorem ext_norm_arg
  given: {x y : Complex} (h₁ : ‖x‖ = ‖y‖) (h₂ : x.arg = y.arg)
  statement: x = y
  proof: by
  rw [← norm_mul_exp_arg_mul_I x]; rw [← norm_mul_exp_arg_mul_I y]; rw [h₁]; rw [h₂]

中文:
定理 ext_norm_arg
  条件: {x y : 复形} (h₁ : ‖x‖ = ‖y‖) (h₂ : x.arg = y.arg)
  结论: x = y
  证明: by
  rw [← norm_mul_exp_arg_mul_I x]; rw [← norm_mul_exp_arg_mul_I y]; rw [h₁]; rw [h₂]

Depends on / 依赖: norm_mul_exp_arg_mul_I
-/
theorem ext_norm_arg {x y : Complex} (h₁ : ‖x‖ = ‖y‖) (h₂ : x.arg = y.arg) : x = y := by
  rw [← norm_mul_exp_arg_mul_I x]; rw [← norm_mul_exp_arg_mul_I y]; rw [h₁]; rw [h₂]

/--
theorem `ext_norm_arg_iff` / 定理 `ext_norm_arg_iff`

English:
theorem ext_norm_arg_iff
  given: {x y : Complex}
  statement: x = y ↔ ‖x‖ = ‖y‖ ∧ arg x = arg y
  proof: ⟨fun h => h ▸ ⟨rfl, rfl⟩, and_imp.2 ext_norm_arg⟩

中文:
定理 ext_norm_arg_iff
  条件: {x y : 复形}
  结论: x = y ↔ ‖x‖ = ‖y‖ ∧ arg x = arg y
  证明: ⟨fun h => h ▸ ⟨rfl, rfl⟩, and_imp.2 ext_norm_arg⟩

Depends on / 依赖: and_imp, ext_norm_arg
-/
theorem ext_norm_arg_iff {x y : Complex} : x = y ↔ ‖x‖ = ‖y‖ ∧ arg x = arg y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, and_imp.2 ext_norm_arg⟩

/--
theorem `arg_mem_Ioc` / 定理 `arg_mem_Ioc`

English:
theorem arg_mem_Ioc
  given: (z : Complex)
  statement: arg z in Set.Ioc (-π) π
  proof: by
  have hπ : 0 < π := Real.pi_pos
  rcases eq_or_ne z 0 with (rfl | hz)
  · simp [hπ, hπ.le]
  rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos (arg z) (-π) with ⟨N, hN, -⟩
  rw [two_mul]; rw [neg_add_cancel_left]; rw [← two_mul]; rw [zsmul_eq_mul] at hN
  rw [← norm_mul_cos_add_sin_mul_I z];

中文:
定理 arg_mem_Ioc
  条件: (z : 复形)
  结论: arg z in 集合.左开右闭区间 (-π) π
  证明: by
  have hπ : 0 < π := Real.pi_pos
  rcases eq_or_ne z 0 with (rfl | hz)
  · simp [hπ, hπ.le]
  rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos (arg z) (-π) with ⟨N, hN, -⟩
  rw [two_mul]; rw [neg_add_cancel_left]; rw [← two_mul]; rw [zsmul_eq_mul] at hN
  rw [← norm_mul_cos_add_sin_mul_I z];

Depends on / 依赖: Real.pi_pos, Real.two_pi_pos, arg_mul_cos_add_sin_mul_I, cos_add_int_mul_two_pi, eq_or_ne, existsUnique_add_zsmul_mem_Ioc, neg_add_cancel_left, norm_mul_cos_add_sin_mul_I, norm_pos_iff, norm_pos_iff.mpr, pi_pos, sin_add_int_mul_two_pi, two_mul, two_pi_pos, zsmul_eq_mul
-/
theorem arg_mem_Ioc (z : Complex) : arg z in Set.Ioc (-π) π := by
  have hπ : 0 < π := Real.pi_pos
  rcases eq_or_ne z 0 with (rfl | hz)
  · simp [hπ, hπ.le]
  rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos (arg z) (-π) with ⟨N, hN, -⟩
  rw [two_mul]; rw [neg_add_cancel_left]; rw [← two_mul]; rw [zsmul_eq_mul] at hN
  rw [← norm_mul_cos_add_sin_mul_I z]; rw [← cos_add_int_mul_two_pi _ N]; rw [← sin_add_int_mul_two_pi _ N]
  have := arg_mul_cos_add_sin_mul_I (norm_pos_iff.mpr hz) hN
  push_cast at this
  rwa [this]

@[simp]
/--
theorem `toIocMod_arg` / 定理 `toIocMod_arg`

English:
theorem toIocMod_arg
  given: (z : Complex)
  statement: toIocMod Real.two_pi_pos (-π) z.arg = z.arg
  proof: by
  simpa [toIocMod_eq_self, two_mul] using z.arg_mem_Ioc

@[simp]

中文:
定理 toIocMod_arg
  条件: (z : 复形)
  结论: toIocMod 实数.two_pi_pos (-π) z.arg = z.arg
  证明: by
  simpa [toIocMod_eq_self, two_mul] using z.arg_mem_Ioc

@[simp]

Depends on / 依赖: arg_mem_Ioc, toIocMod_eq_self, two_mul, z.arg_mem_Ioc
-/
theorem toIocMod_arg (z : Complex) : toIocMod Real.two_pi_pos (-π) z.arg = z.arg := by
  simpa [toIocMod_eq_self, two_mul] using z.arg_mem_Ioc

@[simp]
/--
theorem `range_arg` / 定理 `range_arg`

English:
theorem range_arg
  statement: Set.range arg = Set.Ioc (-π) π
  proof: (Set.range_subset_iff.2 arg_mem_Ioc).antisymm fun _ hx => ⟨_, arg_cos_add_sin_mul_I hx⟩

中文:
定理 range_arg
  结论: 集合.range arg = 集合.左开右闭区间 (-π) π
  证明: (Set.range_subset_iff.2 arg_mem_Ioc).antisymm fun _ hx => ⟨_, arg_cos_add_sin_mul_I hx⟩

Depends on / 依赖: Set.range_subset_iff, antisymm, arg_cos_add_sin_mul_I, arg_mem_Ioc, range_subset_iff
-/
theorem range_arg : Set.range arg = Set.Ioc (-π) π :=
  (Set.range_subset_iff.2 arg_mem_Ioc).antisymm fun _ hx => ⟨_, arg_cos_add_sin_mul_I hx⟩

/--
theorem `arg_le_pi` / 定理 `arg_le_pi`

English:
theorem arg_le_pi
  given: (x : Complex)
  statement: arg x <= π
  proof: (arg_mem_Ioc x).2

中文:
定理 arg_le_pi
  条件: (x : 复形)
  结论: arg x <= π
  证明: (arg_mem_Ioc x).2

Depends on / 依赖: arg_mem_Ioc
-/
theorem arg_le_pi (x : Complex) : arg x <= π :=
  (arg_mem_Ioc x).2

/--
theorem `neg_pi_lt_arg` / 定理 `neg_pi_lt_arg`

English:
theorem neg_pi_lt_arg
  given: (x : Complex)
  statement: -π < arg x
  proof: (arg_mem_Ioc x).1

中文:
定理 neg_pi_lt_arg
  条件: (x : 复形)
  结论: -π < arg x
  证明: (arg_mem_Ioc x).1

Depends on / 依赖: arg_mem_Ioc
-/
theorem neg_pi_lt_arg (x : Complex) : -π < arg x :=
  (arg_mem_Ioc x).1

/--
theorem `arg_lt_arg_add_two_pi` / 定理 `arg_lt_arg_add_two_pi`

English:
theorem arg_lt_arg_add_two_pi
  given: (x y : Complex)
  statement: x.arg < y.arg + 2 * π
  proof: by
  grind [arg_le_pi x, neg_pi_lt_arg y]

中文:
定理 arg_lt_arg_add_two_pi
  条件: (x y : 复形)
  结论: x.arg < y.arg + 2 * π
  证明: by
  grind [arg_le_pi x, neg_pi_lt_arg y]

Depends on / 依赖: arg_le_pi, neg_pi_lt_arg
-/
theorem arg_lt_arg_add_two_pi (x y : Complex) : x.arg < y.arg + 2 * π := by
  grind [arg_le_pi x, neg_pi_lt_arg y]

/--
theorem `abs_arg_sub_arg_lt` / 定理 `abs_arg_sub_arg_lt`

English:
theorem abs_arg_sub_arg_lt
  given: (x y : Complex)
  statement: |x.arg - y.arg| < 2 * π
  proof: by
  grind [arg_lt_arg_add_two_pi x y, arg_lt_arg_add_two_pi y x]

中文:
定理 abs_arg_sub_arg_lt
  条件: (x y : 复形)
  结论: |x.arg - y.arg| < 2 * π
  证明: by
  grind [arg_lt_arg_add_two_pi x y, arg_lt_arg_add_two_pi y x]

Depends on / 依赖: arg_lt_arg_add_two_pi
-/
theorem abs_arg_sub_arg_lt (x y : Complex) : |x.arg - y.arg| < 2 * π := by
  grind [arg_lt_arg_add_two_pi x y, arg_lt_arg_add_two_pi y x]

/--
theorem `abs_arg_le_pi` / 定理 `abs_arg_le_pi`

English:
theorem abs_arg_le_pi
  given: (z : Complex)
  statement: |arg z| <= π
  proof: abs_le.2 ⟨(neg_pi_lt_arg z).le, arg_le_pi z⟩

@[simp]

中文:
定理 abs_arg_le_pi
  条件: (z : 复形)
  结论: |arg z| <= π
  证明: abs_le.2 ⟨(neg_pi_lt_arg z).le, arg_le_pi z⟩

@[simp]

Depends on / 依赖: abs_le, arg_le_pi, neg_pi_lt_arg
-/
theorem abs_arg_le_pi (z : Complex) : |arg z| <= π :=
  abs_le.2 ⟨(neg_pi_lt_arg z).le, arg_le_pi z⟩

@[simp]
/--
theorem `arg_nonneg_iff` / 定理 `arg_nonneg_iff`

English:
theorem arg_nonneg_iff
  given: {z : Complex}
  statement: 0 <= arg z ↔ 0 <= z.im
  proof: by
  rcases eq_or_ne z 0 with (rfl | h₀); · simp
  calc
    0 <= arg z ↔ 0 <= Real.sin (arg z) :=
      ⟨fun h => Real.sin_nonneg_of_mem_Icc ⟨h, arg_le_pi z⟩, by
        contrapose!
        intro h
        exact Real.sin_neg_of_neg_of_neg_pi_lt h (neg_pi_lt_arg _)⟩
    _ ↔ _ := by rw [sin_arg, le_di

中文:
定理 arg_nonneg_iff
  条件: {z : 复形}
  结论: 0 <= arg z ↔ 0 <= z.im
  证明: by
  rcases eq_or_ne z 0 with (rfl | h₀); · simp
  calc
    0 <= arg z ↔ 0 <= Real.sin (arg z) :=
      ⟨fun h => Real.sin_nonneg_of_mem_Icc ⟨h, arg_le_pi z⟩, by
        contrapose!
        intro h
        exact Real.sin_neg_of_neg_of_neg_pi_lt h (neg_pi_lt_arg _)⟩
    _ ↔ _ := by rw [sin_arg, le_di

Depends on / 依赖: Real.sin, Real.sin_neg_of_neg_of_neg_pi_lt, Real.sin_nonneg_of_mem_Icc, arg_le_pi, contrapose, eq_or_ne, neg_pi_lt_arg, norm_pos_iff, norm_pos_iff.mpr, sin_arg, sin_neg_of_neg_of_neg_pi_lt, sin_nonneg_of_mem_Icc, zero_mul
-/
theorem arg_nonneg_iff {z : Complex} : 0 <= arg z ↔ 0 <= z.im := by
  rcases eq_or_ne z 0 with (rfl | h₀); · simp
  calc
    0 <= arg z ↔ 0 <= Real.sin (arg z) :=
      ⟨fun h => Real.sin_nonneg_of_mem_Icc ⟨h, arg_le_pi z⟩, by
        contrapose!
        intro h
        exact Real.sin_neg_of_neg_of_neg_pi_lt h (neg_pi_lt_arg _)⟩
    _ ↔ _ := by rw [sin_arg, le_div_iff₀ (norm_pos_iff.mpr h₀), zero_mul]

@[simp]
/--
theorem `arg_neg_iff` / 定理 `arg_neg_iff`

English:
theorem arg_neg_iff
  given: {z : Complex}
  statement: arg z < 0 ↔ z.im < 0
  proof: lt_iff_lt_of_le_iff_le arg_nonneg_iff

中文:
定理 arg_neg_iff
  条件: {z : 复形}
  结论: arg z < 0 ↔ z.im < 0
  证明: lt_iff_lt_of_le_iff_le arg_nonneg_iff

Depends on / 依赖: arg_nonneg_iff, lt_iff_lt_of_le_iff_le
-/
theorem arg_neg_iff {z : Complex} : arg z < 0 ↔ z.im < 0 :=
  lt_iff_lt_of_le_iff_le arg_nonneg_iff

/--
theorem `arg_real_mul` / 定理 `arg_real_mul`

English:
theorem arg_real_mul
  given: (x : Complex) {r : Real} (hr : 0 < r)
  statement: arg (r * x) = arg x
  proof: by
  rcases eq_or_ne x 0 with (rfl | hx); · rw [mul_zero]
  conv_lhs =>
    rw [← norm_mul_cos_add_sin_mul_I x]; rw [← mul_assoc]; rw [← ofReal_mul]; rw [arg_mul_cos_add_sin_mul_I (mul_pos hr (norm_pos_iff.mpr hx)) x.arg_mem_Ioc]

中文:
定理 arg_real_mul
  条件: (x : 复形) {r : 实数} (hr : 0 < r)
  结论: arg (r * x) = arg x
  证明: by
  rcases eq_or_ne x 0 with (rfl | hx); · rw [mul_zero]
  conv_lhs =>
    rw [← norm_mul_cos_add_sin_mul_I x]; rw [← mul_assoc]; rw [← ofReal_mul]; rw [arg_mul_cos_add_sin_mul_I (mul_pos hr (norm_pos_iff.mpr hx)) x.arg_mem_Ioc]

Depends on / 依赖: arg_mem_Ioc, arg_mul_cos_add_sin_mul_I, conv_lhs, eq_or_ne, mul_assoc, mul_pos, mul_zero, norm_mul_cos_add_sin_mul_I, norm_pos_iff, norm_pos_iff.mpr, ofReal_mul, x.arg_mem_Ioc
-/
theorem arg_real_mul (x : Complex) {r : Real} (hr : 0 < r) : arg (r * x) = arg x := by
  rcases eq_or_ne x 0 with (rfl | hx); · rw [mul_zero]
  conv_lhs =>
    rw [← norm_mul_cos_add_sin_mul_I x]; rw [← mul_assoc]; rw [← ofReal_mul]; rw [arg_mul_cos_add_sin_mul_I (mul_pos hr (norm_pos_iff.mpr hx)) x.arg_mem_Ioc]

/--
theorem `arg_mul_real` / 定理 `arg_mul_real`

English:
theorem arg_mul_real
  given: {r : Real} (hr : 0 < r) (x : Complex)
  statement: arg (x * r) = arg x
  proof: mul_comm x r ▸ arg_real_mul x hr

中文:
定理 arg_mul_real
  条件: {r : 实数} (hr : 0 < r) (x : 复形)
  结论: arg (x * r) = arg x
  证明: mul_comm x r ▸ arg_real_mul x hr

Depends on / 依赖: arg_real_mul, mul_comm
-/
theorem arg_mul_real {r : Real} (hr : 0 < r) (x : Complex) : arg (x * r) = arg x :=
  mul_comm x r ▸ arg_real_mul x hr

/--
theorem `arg_eq_arg_iff` / 定理 `arg_eq_arg_iff`

English:
theorem arg_eq_arg_iff
  given: {x y : Complex} (hx : x != 0) (hy : y != 0)
  proof: by
  simp only [ext_norm_arg_iff, norm_mul, norm_div, norm_real, norm_norm,
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx), true_and]
  rw [← ofReal_div]; rw [arg_real_mul]
  exact div_pos (norm_pos_iff.mpr hy) (norm_pos_iff.mpr hx)

中文:
定理 arg_eq_arg_iff
  条件: {x y : 复形} (hx : x != 0) (hy : y != 0)
  证明: by
  simp only [ext_norm_arg_iff, norm_mul, norm_div, norm_real, norm_norm,
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx), true_and]
  rw [← ofReal_div]; rw [arg_real_mul]
  exact div_pos (norm_pos_iff.mpr hy) (norm_pos_iff.mpr hx)

Depends on / 依赖: arg_real_mul, div_pos, ext_norm_arg_iff, norm_div, norm_mul, norm_ne_zero_iff, norm_ne_zero_iff.mpr, norm_norm, norm_pos_iff, norm_pos_iff.mpr, norm_real, ofReal_div, true_and
-/
theorem arg_eq_arg_iff {x y : Complex} (hx : x != 0) (hy : y != 0) :
    arg x = arg y ↔ (‖y‖ / ‖x‖ : Complex) * x = y := by
  simp only [ext_norm_arg_iff, norm_mul, norm_div, norm_real, norm_norm,
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx), true_and]
  rw [← ofReal_div]; rw [arg_real_mul]
  exact div_pos (norm_pos_iff.mpr hy) (norm_pos_iff.mpr hx)

/--
lemma `arg_one` / 引理 `arg_one`

English:
lemma arg_one
  statement: arg 1 = 0
  proof: by simp [arg, zero_le_one]

中文:
引理 arg_one
  结论: arg 1 = 0
  证明: by simp [arg, zero_le_one]
-/
@[simp] lemma arg_one : arg 1 = 0 := by simp [arg, zero_le_one]

/--
lemma `arg_div_self` / 引理 `arg_div_self`

English:
lemma arg_div_self
  given: (x : Complex)
  statement: arg (x / x) = 0
  proof: by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [*]

@[simp]

中文:
引理 arg_div_self
  条件: (x : 复形)
  结论: arg (x / x) = 0
  证明: by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [*]

@[simp]
-/
@[simp] lemma arg_div_self (x : Complex) : arg (x / x) = 0 := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [*]

@[simp]
/--
theorem `arg_neg_one` / 定理 `arg_neg_one`

English:
theorem arg_neg_one
  statement: arg (-1) = π
  proof: by simp [arg]

@[simp]

中文:
定理 arg_neg_one
  结论: arg (-1) = π
  证明: by simp [arg]

@[simp]

Depends on / 依赖: F.map_comp, Functor, Functor.mapHomologicalComplex_map_f, HomologicalComplex, HomologicalComplex.pOpcycles, HomologicalComplex.p_opcyclesMap_assoc, _assoc, cancel_epi, mapHomologicalComplex_map_f, map_comp, pOpcycles, pOpcycles_comp_fromLeftDerivedZero, p_opcyclesMap_assoc
-/
theorem arg_neg_one : arg (-1) = π := by simp [arg]

@[simp]
/--
theorem `arg_I` / 定理 `arg_I`

English:
theorem arg_I
  statement: arg I = π / 2
  proof: by simp [arg]

@[simp]

中文:
定理 arg_I
  结论: arg I = π / 2
  证明: by simp [arg]

@[simp]

Depends on / 依赖: ChainComplex, ChainComplex.isIso_descOpcycles_iff, F.map_isZero, ProjectiveResolution, ProjectiveResolution.fromLeftDerivedZero, ShortComplex, ShortComplex.Splitting.exact, Splitting, eq_of_src, fromLeftDerivedZero, isIso_descOpcycles_iff, isZero_zero, map_isZero
-/
theorem arg_I : arg I = π / 2 := by simp [arg]

@[simp]
/--
theorem `arg_neg_I` / 定理 `arg_neg_I`

English:
theorem arg_neg_I
  statement: arg (-I) = -(π / 2)
  proof: by simp [arg]

@[simp]

中文:
定理 arg_neg_I
  结论: arg (-I) = -(π / 2)
  证明: by simp [arg]

@[simp]
-/
theorem arg_neg_I : arg (-I) = -(π / 2) := by simp [arg]

@[simp]
/--
theorem `tan_arg` / 定理 `tan_arg`

English:
theorem tan_arg
  given: (x : Complex)
  statement: Real.tan (arg x) = x.im / x.re
  proof: by
  by_cases h : x = 0
  · simp only [h, zero_div, Complex.zero_im, Complex.arg_zero, Real.tan_zero, Complex.zero_re]
  rw [Real.tan_eq_sin_div_cos]; rw [sin_arg]; rw [cos_arg h]; rw [div_div_div_cancel_right₀ (norm_ne_zero_iff.mpr h)]

中文:
定理 tan_arg
  条件: (x : 复形)
  结论: 实数.tan (arg x) = x.im / x.re
  证明: by
  by_cases h : x = 0
  · simp only [h, zero_div, Complex.zero_im, Complex.arg_zero, Real.tan_zero, Complex.zero_re]
  rw [Real.tan_eq_sin_div_cos]; rw [sin_arg]; rw [cos_arg h]; rw [div_div_div_cancel_right₀ (norm_ne_zero_iff.mpr h)]

Depends on / 依赖: Complex.arg_zero, Complex.zero_im, Complex.zero_re, Real.tan_eq_sin_div_cos, Real.tan_zero, arg_zero, cos_arg, norm_ne_zero_iff, norm_ne_zero_iff.mpr, sin_arg, tan_eq_sin_div_cos, tan_zero, zero_div, zero_im, zero_re
-/
theorem tan_arg (x : Complex) : Real.tan (arg x) = x.im / x.re := by
  by_cases h : x = 0
  · simp only [h, zero_div, Complex.zero_im, Complex.arg_zero, Real.tan_zero, Complex.zero_re]
  rw [Real.tan_eq_sin_div_cos]; rw [sin_arg]; rw [cos_arg h]; rw [div_div_div_cancel_right₀ (norm_ne_zero_iff.mpr h)]

/--
theorem `arg_ofReal_of_nonneg` / 定理 `arg_ofReal_of_nonneg`

English:
theorem arg_ofReal_of_nonneg
  given: {x : Real} (hx : 0 <= x)
  statement: arg x = 0
  proof: by simp [arg, hx]

@[simp, norm_cast]

中文:
定理 arg_of实数_of_nonneg
  条件: {x : 实数} (hx : 0 <= x)
  结论: arg x = 0
  证明: by simp [arg, hx]

@[simp, norm_cast]

Depends on / 依赖: ProjectiveResolution, ProjectiveResolution.self, fromLeftDerivedZero_eq, infer_instance
-/
theorem arg_ofReal_of_nonneg {x : Real} (hx : 0 <= x) : arg x = 0 := by simp [arg, hx]

@[simp, norm_cast]
/--
lemma `natCast_arg` / 引理 `natCast_arg`

English:
lemma natCast_arg
  given: {n : Nat}
  statement: arg n = 0
  proof: ofReal_natCast n ▸ arg_ofReal_of_nonneg n.cast_nonneg

@[simp]

中文:
引理 natCast_arg
  条件: {n : 自然数}
  结论: arg n = 0
  证明: ofReal_natCast n ▸ arg_ofReal_of_nonneg n.cast_nonneg

@[simp]

Depends on / 依赖: ChainComplex, ChainComplex.isIso_descOpcycles_iff, CokernelCofork, CokernelCofork.mapIsColimit, P.isColimitCokernelCofork, ProjectiveResolution, ProjectiveResolution.fromLeftDerivedZero, ShortComplex, ShortComplex.exact_and_epi_g_iff_g_is_cokernel, arg_ofReal_of_nonneg, cast_nonneg, exact_and_epi_g_iff_g_is_cokernel, fromLeftDerivedZero, isColimitCokernelCofork, isIso_descOpcycles_iff, mapIsColimit, n.cast_nonneg, ofReal_natCast
-/
lemma natCast_arg {n : Nat} : arg n = 0 :=
  ofReal_natCast n ▸ arg_ofReal_of_nonneg n.cast_nonneg

@[simp]
/--
lemma `ofNat_arg` / 引理 `ofNat_arg`

English:
lemma ofNat_arg
  given: {n : Nat} [n.AtLeastTwo]
  statement: arg ofNat(n) = 0
  proof: natCast_arg

中文:
引理 of自然数_arg
  条件: {n : 自然数} [n.AtLeastTwo]
  结论: arg of自然数(n) = 0
  证明: natCast_arg

Depends on / 依赖: Functor, Functor.fromLeftDerivedZero, fromLeftDerivedZero, infer_instance, natCast_arg
-/
lemma ofNat_arg {n : Nat} [n.AtLeastTwo] : arg ofNat(n) = 0 :=
  natCast_arg

/--
theorem `arg_eq_zero_iff` / 定理 `arg_eq_zero_iff`

English:
theorem arg_eq_zero_iff
  given: {z : Complex}
  statement: arg z = 0 ↔ 0 <= z.re ∧ z.im = 0
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← norm_mul_cos_add_sin_mul_I z, h]
    simp [norm_nonneg]
  · obtain ⟨x, y⟩ := z
    rintro ⟨h, rfl : y = 0⟩
    exact arg_ofReal_of_nonneg h

中文:
定理 arg_eq_zero_iff
  条件: {z : 复形}
  结论: arg z = 0 ↔ 0 <= z.re ∧ z.im = 0
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← norm_mul_cos_add_sin_mul_I z, h]
    simp [norm_nonneg]
  · obtain ⟨x, y⟩ := z
    rintro ⟨h, rfl : y = 0⟩
    exact arg_ofReal_of_nonneg h

Depends on / 依赖: arg_ofReal_of_nonneg, norm_mul_cos_add_sin_mul_I, norm_nonneg
-/
theorem arg_eq_zero_iff {z : Complex} : arg z = 0 ↔ 0 <= z.re ∧ z.im = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← norm_mul_cos_add_sin_mul_I z, h]
    simp [norm_nonneg]
  · obtain ⟨x, y⟩ := z
    rintro ⟨h, rfl : y = 0⟩
    exact arg_ofReal_of_nonneg h

open ComplexOrder in
/--
lemma `arg_eq_zero_iff_zero_le` / 引理 `arg_eq_zero_iff_zero_le`

English:
lemma arg_eq_zero_iff_zero_le
  given: {z : Complex}
  statement: arg z = 0 ↔ 0 <= z
  proof: by
  rw [arg_eq_zero_iff]; rw [eq_comm]; rw [nonneg_iff]

中文:
引理 arg_eq_zero_iff_zero_le
  条件: {z : 复形}
  结论: arg z = 0 ↔ 0 <= z
  证明: by
  rw [arg_eq_zero_iff]; rw [eq_comm]; rw [nonneg_iff]

Depends on / 依赖: arg_eq_zero_iff, eq_comm, nonneg_iff
-/
lemma arg_eq_zero_iff_zero_le {z : Complex} : arg z = 0 ↔ 0 <= z := by
  rw [arg_eq_zero_iff]; rw [eq_comm]; rw [nonneg_iff]

/--
theorem `arg_eq_pi_iff` / 定理 `arg_eq_pi_iff`

English:
theorem arg_eq_pi_iff
  given: {z : Complex}
  statement: arg z = π ↔ z.re < 0 ∧ z.im = 0
  proof: by
  by_cases h₀ : z = 0
  · simp [h₀, Real.pi_ne_zero.symm]
  constructor
  · intro h
    rw [← norm_mul_cos_add_sin_mul_I z]; rw [h]
    simp [h₀]
  · obtain ⟨x, y⟩ := z
    rintro ⟨h : x < 0, rfl : y = 0⟩
    rw [← arg_neg_one]; rw [← arg_real_mul (-1) (neg_pos.2 h)]
    simp [← ofReal_def]

中文:
定理 arg_eq_pi_iff
  条件: {z : 复形}
  结论: arg z = π ↔ z.re < 0 ∧ z.im = 0
  证明: by
  by_cases h₀ : z = 0
  · simp [h₀, Real.pi_ne_zero.symm]
  constructor
  · intro h
    rw [← norm_mul_cos_add_sin_mul_I z]; rw [h]
    simp [h₀]
  · obtain ⟨x, y⟩ := z
    rintro ⟨h : x < 0, rfl : y = 0⟩
    rw [← arg_neg_one]; rw [← arg_real_mul (-1) (neg_pos.2 h)]
    simp [← ofReal_def]

Depends on / 依赖: Real.pi_ne_zero.symm, arg_neg_one, arg_real_mul, neg_pos, norm_mul_cos_add_sin_mul_I, ofReal_def, pi_ne_zero
-/
theorem arg_eq_pi_iff {z : Complex} : arg z = π ↔ z.re < 0 ∧ z.im = 0 := by
  by_cases h₀ : z = 0
  · simp [h₀, Real.pi_ne_zero.symm]
  constructor
  · intro h
    rw [← norm_mul_cos_add_sin_mul_I z]; rw [h]
    simp [h₀]
  · obtain ⟨x, y⟩ := z
    rintro ⟨h : x < 0, rfl : y = 0⟩
    rw [← arg_neg_one]; rw [← arg_real_mul (-1) (neg_pos.2 h)]
    simp [← ofReal_def]

open ComplexOrder in
/--
lemma `arg_eq_pi_iff_lt_zero` / 引理 `arg_eq_pi_iff_lt_zero`

English:
lemma arg_eq_pi_iff_lt_zero
  given: {z : Complex}
  statement: arg z = π ↔ z < 0
  proof: arg_eq_pi_iff

中文:
引理 arg_eq_pi_iff_lt_zero
  条件: {z : 复形}
  结论: arg z = π ↔ z < 0
  证明: arg_eq_pi_iff

Depends on / 依赖: arg_eq_pi_iff
-/
lemma arg_eq_pi_iff_lt_zero {z : Complex} : arg z = π ↔ z < 0 := arg_eq_pi_iff

/--
theorem `arg_lt_pi_iff` / 定理 `arg_lt_pi_iff`

English:
theorem arg_lt_pi_iff
  given: {z : Complex}
  statement: arg z < π ↔ 0 <= z.re ∨ z.im != 0
  proof: by
  rw [(arg_le_pi z).lt_iff_ne]; rw [not_iff_comm]; rw [not_or]; rw [not_le]; rw [Classical.not_not]; rw [arg_eq_pi_iff]

中文:
定理 arg_lt_pi_iff
  条件: {z : 复形}
  结论: arg z < π ↔ 0 <= z.re ∨ z.im != 0
  证明: by
  rw [(arg_le_pi z).lt_iff_ne]; rw [not_iff_comm]; rw [not_or]; rw [not_le]; rw [Classical.not_not]; rw [arg_eq_pi_iff]

Depends on / 依赖: Classical, Classical.not_not, arg_eq_pi_iff, arg_le_pi, lt_iff_ne, not_iff_comm, not_le, not_not, not_or
-/
theorem arg_lt_pi_iff {z : Complex} : arg z < π ↔ 0 <= z.re ∨ z.im != 0 := by
  rw [(arg_le_pi z).lt_iff_ne]; rw [not_iff_comm]; rw [not_or]; rw [not_le]; rw [Classical.not_not]; rw [arg_eq_pi_iff]

/--
theorem `arg_ofReal_of_neg` / 定理 `arg_ofReal_of_neg`

English:
theorem arg_ofReal_of_neg
  given: {x : Real} (hx : x < 0)
  statement: arg x = π
  proof: arg_eq_pi_iff.2 ⟨hx, rfl⟩

中文:
定理 arg_of实数_of_neg
  条件: {x : 实数} (hx : x < 0)
  结论: arg x = π
  证明: arg_eq_pi_iff.2 ⟨hx, rfl⟩

Depends on / 依赖: arg_eq_pi_iff
-/
theorem arg_ofReal_of_neg {x : Real} (hx : x < 0) : arg x = π :=
  arg_eq_pi_iff.2 ⟨hx, rfl⟩

/--
theorem `arg_eq_pi_div_two_iff` / 定理 `arg_eq_pi_div_two_iff`

English:
theorem arg_eq_pi_div_two_iff
  given: {z : Complex}
  statement: arg z = π / 2 ↔ z.re = 0 ∧ 0 < z.im
  proof: by
  by_cases h₀ : z = 0; · simp [h₀, Real.pi_div_two_pos.ne]
  constructor
  · intro h
    rw [← norm_mul_cos_add_sin_mul_I z]; rw [h]
    simp [h₀]
  · obtain ⟨x, y⟩ := z
    rintro ⟨rfl : x = 0, hy : 0 < y⟩
    rw [← arg_I]; rw [← arg_real_mul I hy]; rw [ofReal_mul']; rw [I_re]; rw [I_im]; rw [mu

中文:
定理 arg_eq_pi_div_two_iff
  条件: {z : 复形}
  结论: arg z = π / 2 ↔ z.re = 0 ∧ 0 < z.im
  证明: by
  by_cases h₀ : z = 0; · simp [h₀, Real.pi_div_two_pos.ne]
  constructor
  · intro h
    rw [← norm_mul_cos_add_sin_mul_I z]; rw [h]
    simp [h₀]
  · obtain ⟨x, y⟩ := z
    rintro ⟨rfl : x = 0, hy : 0 < y⟩
    rw [← arg_I]; rw [← arg_real_mul I hy]; rw [ofReal_mul']; rw [I_re]; rw [I_im]; rw [mu

Depends on / 依赖: I_im, I_re, Real.pi_div_two_pos.ne, arg_I, arg_real_mul, mul_one, mul_zero, norm_mul_cos_add_sin_mul_I, ofReal_mul, pi_div_two_pos
-/
theorem arg_eq_pi_div_two_iff {z : Complex} : arg z = π / 2 ↔ z.re = 0 ∧ 0 < z.im := by
  by_cases h₀ : z = 0; · simp [h₀, Real.pi_div_two_pos.ne]
  constructor
  · intro h
    rw [← norm_mul_cos_add_sin_mul_I z]; rw [h]
    simp [h₀]
  · obtain ⟨x, y⟩ := z
    rintro ⟨rfl : x = 0, hy : 0 < y⟩
    rw [← arg_I]; rw [← arg_real_mul I hy]; rw [ofReal_mul']; rw [I_re]; rw [I_im]; rw [mul_zero]; rw [mul_one]

/--
theorem `arg_eq_neg_pi_div_two_iff` / 定理 `arg_eq_neg_pi_div_two_iff`

English:
theorem arg_eq_neg_pi_div_two_iff
  given: {z : Complex}
  statement: arg z = -(π / 2) ↔ z.re = 0 ∧ z.im < 0
  proof: by
  by_cases h₀ : z = 0; · simp [h₀, Real.pi_ne_zero]
  constructor
  · intro h
    rw [← norm_mul_cos_add_sin_mul_I z]; rw [h]
    simp [h₀]
  · obtain ⟨x, y⟩ := z
    rintro ⟨rfl : x = 0, hy : y < 0⟩
    rw [← arg_neg_I]; rw [← arg_real_mul (-I) (neg_pos.2 hy)]; rw [mk_eq_add_mul_I]
    simp

中文:
定理 arg_eq_neg_pi_div_two_iff
  条件: {z : 复形}
  结论: arg z = -(π / 2) ↔ z.re = 0 ∧ z.im < 0
  证明: by
  by_cases h₀ : z = 0; · simp [h₀, Real.pi_ne_zero]
  constructor
  · intro h
    rw [← norm_mul_cos_add_sin_mul_I z]; rw [h]
    simp [h₀]
  · obtain ⟨x, y⟩ := z
    rintro ⟨rfl : x = 0, hy : y < 0⟩
    rw [← arg_neg_I]; rw [← arg_real_mul (-I) (neg_pos.2 hy)]; rw [mk_eq_add_mul_I]
    simp

Depends on / 依赖: Real.pi_ne_zero, arg_neg_I, arg_real_mul, mk_eq_add_mul_I, neg_pos, norm_mul_cos_add_sin_mul_I, pi_ne_zero
-/
theorem arg_eq_neg_pi_div_two_iff {z : Complex} : arg z = -(π / 2) ↔ z.re = 0 ∧ z.im < 0 := by
  by_cases h₀ : z = 0; · simp [h₀, Real.pi_ne_zero]
  constructor
  · intro h
    rw [← norm_mul_cos_add_sin_mul_I z]; rw [h]
    simp [h₀]
  · obtain ⟨x, y⟩ := z
    rintro ⟨rfl : x = 0, hy : y < 0⟩
    rw [← arg_neg_I]; rw [← arg_real_mul (-I) (neg_pos.2 hy)]; rw [mk_eq_add_mul_I]
    simp

/--
theorem `arg_of_re_nonneg` / 定理 `arg_of_re_nonneg`

English:
theorem arg_of_re_nonneg
  given: {x : Complex} (hx : 0 <= x.re)
  statement: arg x = Real.arcsin (x.im / ‖x‖)
  proof: if_pos hx

中文:
定理 arg_of_re_nonneg
  条件: {x : 复形} (hx : 0 <= x.re)
  结论: arg x = 实数.arcsin (x.im / ‖x‖)
  证明: if_pos hx

Depends on / 依赖: if_pos
-/
theorem arg_of_re_nonneg {x : Complex} (hx : 0 <= x.re) : arg x = Real.arcsin (x.im / ‖x‖) :=
  if_pos hx

/--
theorem `arg_of_re_neg_of_im_nonneg` / 定理 `arg_of_re_neg_of_im_nonneg`

English:
theorem arg_of_re_neg_of_im_nonneg
  given: {x : Complex} (hx_re : x.re < 0) (hx_im : 0 <= x.im)
  proof: by
  simp only [arg, hx_re.not_ge, hx_im, if_true, if_false]

中文:
定理 arg_of_re_neg_of_im_nonneg
  条件: {x : 复形} (hx_re : x.re < 0) (hx_im : 0 <= x.im)
  证明: by
  simp only [arg, hx_re.not_ge, hx_im, if_true, if_false]

Depends on / 依赖: hx_im, hx_re, hx_re.not_ge, if_false, if_true, not_ge
-/
theorem arg_of_re_neg_of_im_nonneg {x : Complex} (hx_re : x.re < 0) (hx_im : 0 <= x.im) :
    arg x = Real.arcsin ((-x).im / ‖x‖) + π := by
  simp only [arg, hx_re.not_ge, hx_im, if_true, if_false]

/--
theorem `arg_of_re_neg_of_im_neg` / 定理 `arg_of_re_neg_of_im_neg`

English:
theorem arg_of_re_neg_of_im_neg
  given: {x : Complex} (hx_re : x.re < 0) (hx_im : x.im < 0)
  proof: by
  simp only [arg, hx_re.not_ge, hx_im.not_ge, if_false]

中文:
定理 arg_of_re_neg_of_im_neg
  条件: {x : 复形} (hx_re : x.re < 0) (hx_im : x.im < 0)
  证明: by
  simp only [arg, hx_re.not_ge, hx_im.not_ge, if_false]

Depends on / 依赖: hx_im, hx_im.not_ge, hx_re, hx_re.not_ge, if_false, not_ge
-/
theorem arg_of_re_neg_of_im_neg {x : Complex} (hx_re : x.re < 0) (hx_im : x.im < 0) :
    arg x = Real.arcsin ((-x).im / ‖x‖) - π := by
  simp only [arg, hx_re.not_ge, hx_im.not_ge, if_false]

/--
theorem `arg_of_im_nonneg_of_ne_zero` / 定理 `arg_of_im_nonneg_of_ne_zero`

English:
theorem arg_of_im_nonneg_of_ne_zero
  given: {z : Complex} (h₁ : 0 <= z.im) (h₂ : z != 0)
  proof: by
  rw [← cos_arg h₂]; rw [Real.arccos_cos (arg_nonneg_iff.2 h₁) (arg_le_pi _)]

中文:
定理 arg_of_im_nonneg_of_ne_zero
  条件: {z : 复形} (h₁ : 0 <= z.im) (h₂ : z != 0)
  证明: by
  rw [← cos_arg h₂]; rw [Real.arccos_cos (arg_nonneg_iff.2 h₁) (arg_le_pi _)]

Depends on / 依赖: Real.arccos_cos, arccos_cos, arg_le_pi, arg_nonneg_iff, cos_arg
-/
theorem arg_of_im_nonneg_of_ne_zero {z : Complex} (h₁ : 0 <= z.im) (h₂ : z != 0) :
    arg z = Real.arccos (z.re / ‖z‖) := by
  rw [← cos_arg h₂]; rw [Real.arccos_cos (arg_nonneg_iff.2 h₁) (arg_le_pi _)]

/--
theorem `arg_of_im_pos` / 定理 `arg_of_im_pos`

English:
theorem arg_of_im_pos
  given: {z : Complex} (hz : 0 < z.im)
  statement: arg z = Real.arccos (z.re / ‖z‖)
  proof: arg_of_im_nonneg_of_ne_zero hz.le fun h => hz.ne' h.symm ▸ rfl

中文:
定理 arg_of_im_pos
  条件: {z : 复形} (hz : 0 < z.im)
  结论: arg z = 实数.arccos (z.re / ‖z‖)
  证明: arg_of_im_nonneg_of_ne_zero hz.le fun h => hz.ne' h.symm ▸ rfl

Depends on / 依赖: arg_of_im_nonneg_of_ne_zero, h.symm, hz.le, hz.ne
-/
theorem arg_of_im_pos {z : Complex} (hz : 0 < z.im) : arg z = Real.arccos (z.re / ‖z‖) :=
arg_of_im_nonneg_of_ne_zero hz.le fun h => hz.ne' h.symm ▸ rfl

/--
theorem `arg_of_im_neg` / 定理 `arg_of_im_neg`

English:
theorem arg_of_im_neg
  given: {z : Complex} (hz : z.im < 0)
  statement: arg z = -Real.arccos (z.re / ‖z‖)
  proof: by
  have h₀ : z != 0 := mt (congr_arg im) hz.ne
  rw [← cos_arg h₀]; rw [← Real.cos_neg]; rw [Real.arccos_cos]; rw [neg_neg]
  exacts [neg_nonneg.2 (arg_neg_iff.2 hz).le, neg_le.2 (neg_pi_lt_arg z).le]

中文:
定理 arg_of_im_neg
  条件: {z : 复形} (hz : z.im < 0)
  结论: arg z = -实数.arccos (z.re / ‖z‖)
  证明: by
  have h₀ : z != 0 := mt (congr_arg im) hz.ne
  rw [← cos_arg h₀]; rw [← Real.cos_neg]; rw [Real.arccos_cos]; rw [neg_neg]
  exacts [neg_nonneg.2 (arg_neg_iff.2 hz).le, neg_le.2 (neg_pi_lt_arg z).le]

Depends on / 依赖: Real.arccos_cos, Real.cos_neg, arccos_cos, arg_neg_iff, congr_arg, cos_arg, cos_neg, exacts, hz.ne, neg_le, neg_neg, neg_nonneg, neg_pi_lt_arg
-/
theorem arg_of_im_neg {z : Complex} (hz : z.im < 0) : arg z = -Real.arccos (z.re / ‖z‖) := by
  have h₀ : z != 0 := mt (congr_arg im) hz.ne
  rw [← cos_arg h₀]; rw [← Real.cos_neg]; rw [Real.arccos_cos]; rw [neg_neg]
  exacts [neg_nonneg.2 (arg_neg_iff.2 hz).le, neg_le.2 (neg_pi_lt_arg z).le]

/--
theorem `arg_conj` / 定理 `arg_conj`

English:
theorem arg_conj
  given: (x : Complex)
  statement: arg (conj x) = if arg x = π then π else -arg x
  proof: by
  simp_rw [arg_eq_pi_iff, arg, neg_im, conj_im, conj_re, norm_conj, neg_div, neg_neg,
    Real.arcsin_neg]
  rcases lt_trichotomy x.re 0 with (hr | hr | hr) <;>
    rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hr, hr.not_ge, hi.le, hi.ne, not_le.2 hi, add_comm]
  · simp [hr, hr.not_g

中文:
定理 arg_conj
  条件: (x : 复形)
  结论: arg (conj x) = if arg x = π then π else -arg x
  证明: by
  simp_rw [arg_eq_pi_iff, arg, neg_im, conj_im, conj_re, norm_conj, neg_div, neg_neg,
    Real.arcsin_neg]
  rcases lt_trichotomy x.re 0 with (hr | hr | hr) <;>
    rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hr, hr.not_ge, hi.le, hi.ne, not_le.2 hi, add_comm]
  · simp [hr, hr.not_g

Depends on / 依赖: Real.arcsin_neg, add_comm, arcsin_neg, arg_eq_pi_iff, conj_im, conj_re, hi.le, hi.ne, hi.ne.symm, hr.le, hr.le.not_gt, hr.not_ge, lt_trichotomy, neg_div, neg_im, neg_neg, norm_conj, not_ge, not_gt, not_le
-/
theorem arg_conj (x : Complex) : arg (conj x) = if arg x = π then π else -arg x := by
  simp_rw [arg_eq_pi_iff, arg, neg_im, conj_im, conj_re, norm_conj, neg_div, neg_neg,
    Real.arcsin_neg]
  rcases lt_trichotomy x.re 0 with (hr | hr | hr) <;>
    rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hr, hr.not_ge, hi.le, hi.ne, not_le.2 hi, add_comm]
  · simp [hr, hr.not_ge, hi]
  · simp [hr, hr.not_ge, hi.ne.symm, hi.le, not_le.2 hi, sub_eq_neg_add]
  · simp [hr]
  · simp [hr]
  · simp [hr]
  · simp [hr.le, hi.ne]
  · simp [hr.le, hr.le.not_gt]
  · simp [hr.le, hr.le.not_gt]

/--
theorem `arg_inv` / 定理 `arg_inv`

English:
theorem arg_inv
  given: (x : Complex)
  statement: arg x⁻¹ = if arg x = π then π else -arg x
  proof: by
  rw [← arg_conj]; rw [inv_def]; rw [mul_comm]
  by_cases hx : x = 0
  · simp [hx]
  · exact arg_real_mul (conj x) (by simp [hx])

中文:
定理 arg_inv
  条件: (x : 复形)
  结论: arg x⁻¹ = if arg x = π then π else -arg x
  证明: by
  rw [← arg_conj]; rw [inv_def]; rw [mul_comm]
  by_cases hx : x = 0
  · simp [hx]
  · exact arg_real_mul (conj x) (by simp [hx])

Depends on / 依赖: arg_conj, arg_real_mul, inv_def, mul_comm
-/
theorem arg_inv (x : Complex) : arg x⁻¹ = if arg x = π then π else -arg x := by
  rw [← arg_conj]; rw [inv_def]; rw [mul_comm]
  by_cases hx : x = 0
  · simp [hx]
  · exact arg_real_mul (conj x) (by simp [hx])

/--
lemma `abs_arg_inv` / 引理 `abs_arg_inv`

English:
lemma abs_arg_inv
  given: (x : Complex)
  statement: |x⁻¹.arg| = |x.arg|
  proof: by rw [arg_inv]; split_ifs <;> simp [*]

中文:
引理 abs_arg_inv
  条件: (x : 复形)
  结论: |x⁻¹.arg| = |x.arg|
  证明: by rw [arg_inv]; split_ifs <;> simp [*]
-/
@[simp] lemma abs_arg_inv (x : Complex) : |x⁻¹.arg| = |x.arg| := by rw [arg_inv]; split_ifs <;> simp [*]

-- TODO: Replace the next two lemmas by general facts about periodic functions
/--
lemma `norm_eq_one_iff'` / 引理 `norm_eq_one_iff'`

English:
lemma norm_eq_one_iff'
  statement: ‖x‖ = 1 ↔ exists θ in Set.Ioc (-π) π, exp (θ * I) = x
  proof: by
  rw [norm_eq_one_iff]
  constructor
  · rintro ⟨θ, rfl⟩
    refine ⟨toIocMod (mul_pos two_pos Real.pi_pos) (-π) θ, ?_, ?_⟩
    · convert! toIocMod_mem_Ioc _ _ _
      ring
    · rw [eq_sub_of_add_eq <| toIocMod_add_toIocDiv_zsmul _ _ θ, ofReal_sub,
      ofReal_zsmul, ofReal_mul, ofReal_ofNat, e

中文:
引理 norm_eq_one_iff'
  结论: ‖x‖ = 1 ↔ 存在 θ in 集合.左开右闭区间 (-π) π, exp (θ * I) = x
  证明: by
  rw [norm_eq_one_iff]
  constructor
  · rintro ⟨θ, rfl⟩
    refine ⟨toIocMod (mul_pos two_pos Real.pi_pos) (-π) θ, ?_, ?_⟩
    · convert! toIocMod_mem_Ioc _ _ _
      ring
    · rw [eq_sub_of_add_eq <| toIocMod_add_toIocDiv_zsmul _ _ θ, ofReal_sub,
      ofReal_zsmul, ofReal_mul, ofReal_ofNat, e

Depends on / 依赖: Real.pi_pos, convert, eq_sub_of_add_eq, exp_mul_I_periodic, exp_mul_I_periodic.sub_zsmul_eq, mul_pos, norm_eq_one_iff, ofReal_mul, ofReal_ofNat, ofReal_sub, ofReal_zsmul, pi_pos, sub_zsmul_eq, toIocMod, toIocMod_add_toIocDiv_zsmul, toIocMod_mem_Ioc, two_pos
-/
lemma norm_eq_one_iff' : ‖x‖ = 1 ↔ exists θ in Set.Ioc (-π) π, exp (θ * I) = x := by
  rw [norm_eq_one_iff]
  constructor
  · rintro ⟨θ, rfl⟩
    refine ⟨toIocMod (mul_pos two_pos Real.pi_pos) (-π) θ, ?_, ?_⟩
    · convert! toIocMod_mem_Ioc _ _ _
      ring
    · rw [eq_sub_of_add_eq <| toIocMod_add_toIocDiv_zsmul _ _ θ, ofReal_sub,
      ofReal_zsmul, ofReal_mul, ofReal_ofNat, exp_mul_I_periodic.sub_zsmul_eq]
  · rintro ⟨θ, _, rfl⟩
    exact ⟨θ, rfl⟩

/--
lemma `image_exp_Ioc_eq_sphere` / 引理 `image_exp_Ioc_eq_sphere`

English:
lemma image_exp_Ioc_eq_sphere
  statement: (fun θ : Real => exp (θ * I)) '' Set.Ioc (-π) π = sphere 0 1
  proof: by
  ext; simpa using norm_eq_one_iff'.symm

中文:
引理 image_exp_Ioc_eq_sphere
  结论: (fun θ : 实数 => exp (θ * I)) '' 集合.左开右闭区间 (-π) π = sphere 0 1
  证明: by
  ext; simpa using norm_eq_one_iff'.symm

Depends on / 依赖: norm_eq_one_iff
-/
lemma image_exp_Ioc_eq_sphere : (fun θ : Real => exp (θ * I)) '' Set.Ioc (-π) π = sphere 0 1 := by
  ext; simpa using norm_eq_one_iff'.symm

/--
theorem `arg_le_pi_div_two_iff` / 定理 `arg_le_pi_div_two_iff`

English:
theorem arg_le_pi_div_two_iff
  given: {z : Complex}
  statement: arg z <= π / 2 ↔ 0 <= re z ∨ im z < 0
  proof: by
  rcases le_or_gt 0 (re z) with hre | hre
  · simp only [hre, arg_of_re_nonneg hre, Real.arcsin_le_pi_div_two, true_or]
  simp only [hre.not_ge, false_or]
  rcases le_or_gt 0 (im z) with him | him
  · simp only [him.not_gt]
    rw [iff_false]; rw [not_le]; rw [arg_of_re_neg_of_im_nonneg hre him];

中文:
定理 arg_le_pi_div_two_iff
  条件: {z : 复形}
  结论: arg z <= π / 2 ↔ 0 <= re z ∨ im z < 0
  证明: by
  rcases le_or_gt 0 (re z) with hre | hre
  · simp only [hre, arg_of_re_nonneg hre, Real.arcsin_le_pi_div_two, true_or]
  simp only [hre.not_ge, false_or]
  rcases le_or_gt 0 (im z) with him | him
  · simp only [him.not_gt]
    rw [iff_false]; rw [not_le]; rw [arg_of_re_neg_of_im_nonneg hre him];

Depends on / 依赖: Real.arcsin_le_pi_div_two, Real.neg_pi_div_two_lt_arcsin, abs_im_lt_norm, abs_of_nonneg, arcsin_le_pi_div_two, arg_of_re_neg_of_im_nonneg, arg_of_re_nonneg, div_lt_one, exacts, false_or, half_sub, him.not_gt, hre.ne, hre.not_ge, iff_false, le_or_gt, neg_div, neg_im, neg_lt_neg_iff, neg_pi_div_two_lt_arcsin
-/
theorem arg_le_pi_div_two_iff {z : Complex} : arg z <= π / 2 ↔ 0 <= re z ∨ im z < 0 := by
  rcases le_or_gt 0 (re z) with hre | hre
  · simp only [hre, arg_of_re_nonneg hre, Real.arcsin_le_pi_div_two, true_or]
  simp only [hre.not_ge, false_or]
  rcases le_or_gt 0 (im z) with him | him
  · simp only [him.not_gt]
    rw [iff_false]; rw [not_le]; rw [arg_of_re_neg_of_im_nonneg hre him]; rw [← sub_lt_iff_lt_add]; rw [half_sub]; rw [Real.neg_pi_div_two_lt_arcsin]; rw [neg_im]; rw [neg_div]; rw [neg_lt_neg_iff]; rw [div_lt_one]; rw [←
      abs_of_nonneg him]; rw [abs_im_lt_norm]
    exacts [hre.ne, norm_pos_iff.mpr <| ne_of_apply_ne re hre.ne]
  · simp only [him]
    rw [iff_true]; rw [arg_of_re_neg_of_im_neg hre him]
    exact (sub_le_self _ Real.pi_pos.le).trans (Real.arcsin_le_pi_div_two _)

/--
theorem `neg_pi_div_two_le_arg_iff` / 定理 `neg_pi_div_two_le_arg_iff`

English:
theorem neg_pi_div_two_le_arg_iff
  given: {z : Complex}
  statement: -(π / 2) <= arg z ↔ 0 <= re z ∨ 0 <= im z
  proof: by
  rcases le_or_gt 0 (re z) with hre | hre
  · simp only [hre, arg_of_re_nonneg hre, Real.neg_pi_div_two_le_arcsin, true_or]
  simp only [hre.not_ge, false_or]
  rcases le_or_gt 0 (im z) with him | him
  · simp only [him]
    rw [iff_true]; rw [arg_of_re_neg_of_im_nonneg hre him]
    exact (Real.n

中文:
定理 neg_pi_div_two_le_arg_iff
  条件: {z : 复形}
  结论: -(π / 2) <= arg z ↔ 0 <= re z ∨ 0 <= im z
  证明: by
  rcases le_or_gt 0 (re z) with hre | hre
  · simp only [hre, arg_of_re_nonneg hre, Real.neg_pi_div_two_le_arcsin, true_or]
  simp only [hre.not_ge, false_or]
  rcases le_or_gt 0 (im z) with him | him
  · simp only [him]
    rw [iff_true]; rw [arg_of_re_neg_of_im_nonneg hre him]
    exact (Real.n

Depends on / 依赖: Real.neg_pi_div_two_le_arcsin, Real.pi_pos.le, arg_of_re_neg_of_im_neg, arg_of_re_neg_of_im_nonneg, arg_of_re_nonneg, false_or, him.not_ge, hre.not_ge, iff_false, iff_true, le_add_of_nonneg_right, le_or_gt, neg_pi_div_two_le_arcsin, not_ge, not_le, pi_pos, sub_eq_add_neg, sub_lt_iff_lt_add, true_or
-/
theorem neg_pi_div_two_le_arg_iff {z : Complex} : -(π / 2) <= arg z ↔ 0 <= re z ∨ 0 <= im z := by
  rcases le_or_gt 0 (re z) with hre | hre
  · simp only [hre, arg_of_re_nonneg hre, Real.neg_pi_div_two_le_arcsin, true_or]
  simp only [hre.not_ge, false_or]
  rcases le_or_gt 0 (im z) with him | him
  · simp only [him]
    rw [iff_true]; rw [arg_of_re_neg_of_im_nonneg hre him]
    exact (Real.neg_pi_div_two_le_arcsin _).trans (le_add_of_nonneg_right Real.pi_pos.le)
  · simp only [him.not_ge]
    rw [iff_false]; rw [not_le]; rw [arg_of_re_neg_of_im_neg hre him]; rw [sub_lt_iff_lt_add']; rw [←
      sub_eq_add_neg]; rw [sub_half]; rw [Real.arcsin_lt_pi_div_two]; rw [div_lt_one]; rw [neg_im]; rw [← abs_of_neg him]; rw [abs_im_lt_norm]
    exacts [hre.ne, norm_pos_iff.mpr <| ne_of_apply_ne re hre.ne]

/--
lemma `neg_pi_div_two_lt_arg_iff` / 引理 `neg_pi_div_two_lt_arg_iff`

English:
lemma neg_pi_div_two_lt_arg_iff
  given: {z : Complex}
  statement: -(π / 2) < arg z ↔ 0 < re z ∨ 0 <= im z
  proof: by
  rw [lt_iff_le_and_ne]; rw [neg_pi_div_two_le_arg_iff]; rw [ne_comm]; rw [Ne]; rw [arg_eq_neg_pi_div_two_iff]
  rcases lt_trichotomy z.re 0 with hre | hre | hre
  · simp [hre.ne, hre.not_ge, hre.not_gt]
  · simp [hre]
  · simp [hre, hre.le, hre.ne']

中文:
引理 neg_pi_div_two_lt_arg_iff
  条件: {z : 复形}
  结论: -(π / 2) < arg z ↔ 0 < re z ∨ 0 <= im z
  证明: by
  rw [lt_iff_le_and_ne]; rw [neg_pi_div_two_le_arg_iff]; rw [ne_comm]; rw [Ne]; rw [arg_eq_neg_pi_div_two_iff]
  rcases lt_trichotomy z.re 0 with hre | hre | hre
  · simp [hre.ne, hre.not_ge, hre.not_gt]
  · simp [hre]
  · simp [hre, hre.le, hre.ne']

Depends on / 依赖: arg_eq_neg_pi_div_two_iff, hre.le, hre.ne, hre.not_ge, hre.not_gt, lt_iff_le_and_ne, lt_trichotomy, ne_comm, neg_pi_div_two_le_arg_iff, not_ge, not_gt, z.re
-/
lemma neg_pi_div_two_lt_arg_iff {z : Complex} : -(π / 2) < arg z ↔ 0 < re z ∨ 0 <= im z := by
  rw [lt_iff_le_and_ne]; rw [neg_pi_div_two_le_arg_iff]; rw [ne_comm]; rw [Ne]; rw [arg_eq_neg_pi_div_two_iff]
  rcases lt_trichotomy z.re 0 with hre | hre | hre
  · simp [hre.ne, hre.not_ge, hre.not_gt]
  · simp [hre]
  · simp [hre, hre.le, hre.ne']

/--
lemma `arg_lt_pi_div_two_iff` / 引理 `arg_lt_pi_div_two_iff`

English:
lemma arg_lt_pi_div_two_iff
  given: {z : Complex}
  statement: arg z < π / 2 ↔ 0 < re z ∨ im z < 0 ∨ z = 0
  proof: by
  rw [lt_iff_le_and_ne]; rw [arg_le_pi_div_two_iff]; rw [Ne]; rw [arg_eq_pi_div_two_iff]
  rcases lt_trichotomy z.re 0 with hre | hre | hre
  · have : z != 0 := by simp [Complex.ext_iff, hre.ne]
    simp [hre.ne, hre.not_ge, hre.not_gt, this]
  · have : z = 0 ↔ z.im = 0 := by simp [Complex.ext_if

中文:
引理 arg_lt_pi_div_two_iff
  条件: {z : 复形}
  结论: arg z < π / 2 ↔ 0 < re z ∨ im z < 0 ∨ z = 0
  证明: by
  rw [lt_iff_le_and_ne]; rw [arg_le_pi_div_two_iff]; rw [Ne]; rw [arg_eq_pi_div_two_iff]
  rcases lt_trichotomy z.re 0 with hre | hre | hre
  · have : z != 0 := by simp [Complex.ext_iff, hre.ne]
    simp [hre.ne, hre.not_ge, hre.not_gt, this]
  · have : z = 0 ↔ z.im = 0 := by simp [Complex.ext_if

Depends on / 依赖: Complex.ext_iff, arg_eq_pi_div_two_iff, arg_le_pi_div_two_iff, ext_iff, hre.le, hre.ne, hre.not_ge, hre.not_gt, le_iff_eq_or_lt, lt_iff_le_and_ne, lt_trichotomy, not_ge, not_gt, or_comm, z.im, z.re
-/
lemma arg_lt_pi_div_two_iff {z : Complex} : arg z < π / 2 ↔ 0 < re z ∨ im z < 0 ∨ z = 0 := by
  rw [lt_iff_le_and_ne]; rw [arg_le_pi_div_two_iff]; rw [Ne]; rw [arg_eq_pi_div_two_iff]
  rcases lt_trichotomy z.re 0 with hre | hre | hre
  · have : z != 0 := by simp [Complex.ext_iff, hre.ne]
    simp [hre.ne, hre.not_ge, hre.not_gt, this]
  · have : z = 0 ↔ z.im = 0 := by simp [Complex.ext_iff, hre]
    simp [hre, this, or_comm, le_iff_eq_or_lt]
  · simp [hre, hre.le, hre.ne']

@[simp]
/--
theorem `abs_arg_le_pi_div_two_iff` / 定理 `abs_arg_le_pi_div_two_iff`

English:
theorem abs_arg_le_pi_div_two_iff
  given: {z : Complex}
  statement: |arg z| <= π / 2 ↔ 0 <= re z
  proof: by
  rw [abs_le]; rw [arg_le_pi_div_two_iff]; rw [neg_pi_div_two_le_arg_iff]; rw [← or_and_left]; rw [← not_le]; rw [and_not_self_iff]; rw [or_false]

@[simp]

中文:
定理 abs_arg_le_pi_div_two_iff
  条件: {z : 复形}
  结论: |arg z| <= π / 2 ↔ 0 <= re z
  证明: by
  rw [abs_le]; rw [arg_le_pi_div_two_iff]; rw [neg_pi_div_two_le_arg_iff]; rw [← or_and_left]; rw [← not_le]; rw [and_not_self_iff]; rw [or_false]

@[simp]

Depends on / 依赖: abs_le, and_not_self_iff, arg_le_pi_div_two_iff, neg_pi_div_two_le_arg_iff, not_le, or_and_left, or_false
-/
theorem abs_arg_le_pi_div_two_iff {z : Complex} : |arg z| <= π / 2 ↔ 0 <= re z := by
  rw [abs_le]; rw [arg_le_pi_div_two_iff]; rw [neg_pi_div_two_le_arg_iff]; rw [← or_and_left]; rw [← not_le]; rw [and_not_self_iff]; rw [or_false]

@[simp]
/--
theorem `abs_arg_lt_pi_div_two_iff` / 定理 `abs_arg_lt_pi_div_two_iff`

English:
theorem abs_arg_lt_pi_div_two_iff
  given: {z : Complex}
  statement: |arg z| < π / 2 ↔ 0 < re z ∨ z = 0
  proof: by
  rw [abs_lt]; rw [arg_lt_pi_div_two_iff]; rw [neg_pi_div_two_lt_arg_iff]; rw [← or_and_left]
  rcases eq_or_ne z 0 with hz | hz
  · simp [hz]
  · simp_rw [hz, or_false, ← not_lt, not_and_self_iff, or_false]

@[simp]

中文:
定理 abs_arg_lt_pi_div_two_iff
  条件: {z : 复形}
  结论: |arg z| < π / 2 ↔ 0 < re z ∨ z = 0
  证明: by
  rw [abs_lt]; rw [arg_lt_pi_div_two_iff]; rw [neg_pi_div_two_lt_arg_iff]; rw [← or_and_left]
  rcases eq_or_ne z 0 with hz | hz
  · simp [hz]
  · simp_rw [hz, or_false, ← not_lt, not_and_self_iff, or_false]

@[simp]

Depends on / 依赖: abs_lt, arg_lt_pi_div_two_iff, eq_or_ne, neg_pi_div_two_lt_arg_iff, not_and_self_iff, not_lt, or_and_left, or_false, simp_rw
-/
theorem abs_arg_lt_pi_div_two_iff {z : Complex} : |arg z| < π / 2 ↔ 0 < re z ∨ z = 0 := by
  rw [abs_lt]; rw [arg_lt_pi_div_two_iff]; rw [neg_pi_div_two_lt_arg_iff]; rw [← or_and_left]
  rcases eq_or_ne z 0 with hz | hz
  · simp [hz]
  · simp_rw [hz, or_false, ← not_lt, not_and_self_iff, or_false]

@[simp]
/--
theorem `arg_conj_coe_angle` / 定理 `arg_conj_coe_angle`

English:
theorem arg_conj_coe_angle
  given: (x : Complex)
  statement: (arg (conj x) : Real.Angle) = -arg x
  proof: by
  by_cases h : arg x = π <;> simp [arg_conj, h]

@[simp]

中文:
定理 arg_conj_coe_angle
  条件: (x : 复形)
  结论: (arg (conj x) : 实数.Angle) = -arg x
  证明: by
  by_cases h : arg x = π <;> simp [arg_conj, h]

@[simp]

Depends on / 依赖: arg_conj
-/
theorem arg_conj_coe_angle (x : Complex) : (arg (conj x) : Real.Angle) = -arg x := by
  by_cases h : arg x = π <;> simp [arg_conj, h]

@[simp]
/--
theorem `arg_inv_coe_angle` / 定理 `arg_inv_coe_angle`

English:
theorem arg_inv_coe_angle
  given: (x : Complex)
  statement: (arg x⁻¹ : Real.Angle) = -arg x
  proof: by
  by_cases h : arg x = π <;> simp [arg_inv, h]

中文:
定理 arg_inv_coe_angle
  条件: (x : 复形)
  结论: (arg x⁻¹ : 实数.Angle) = -arg x
  证明: by
  by_cases h : arg x = π <;> simp [arg_inv, h]

Depends on / 依赖: arg_inv
-/
theorem arg_inv_coe_angle (x : Complex) : (arg x⁻¹ : Real.Angle) = -arg x := by
  by_cases h : arg x = π <;> simp [arg_inv, h]

/--
theorem `arg_neg_eq_arg_sub_pi_of_im_pos` / 定理 `arg_neg_eq_arg_sub_pi_of_im_pos`

English:
theorem arg_neg_eq_arg_sub_pi_of_im_pos
  given: {x : Complex} (hi : 0 < x.im)
  statement: arg (-x) = arg x - π
  proof: by
  rw [arg_of_im_pos hi]; rw [arg_of_im_neg (show (-x).im < 0 from Left.neg_neg_iff.2 hi)]
  simp [neg_div, Real.arccos_neg]

中文:
定理 arg_neg_eq_arg_sub_pi_of_im_pos
  条件: {x : 复形} (hi : 0 < x.im)
  结论: arg (-x) = arg x - π
  证明: by
  rw [arg_of_im_pos hi]; rw [arg_of_im_neg (show (-x).im < 0 from Left.neg_neg_iff.2 hi)]
  simp [neg_div, Real.arccos_neg]

Depends on / 依赖: Left.neg_neg_iff, Real.arccos_neg, arccos_neg, arg_of_im_neg, arg_of_im_pos, neg_div, neg_neg_iff
-/
theorem arg_neg_eq_arg_sub_pi_of_im_pos {x : Complex} (hi : 0 < x.im) : arg (-x) = arg x - π := by
  rw [arg_of_im_pos hi]; rw [arg_of_im_neg (show (-x).im < 0 from Left.neg_neg_iff.2 hi)]
  simp [neg_div, Real.arccos_neg]

/--
theorem `arg_neg_eq_arg_add_pi_of_im_neg` / 定理 `arg_neg_eq_arg_add_pi_of_im_neg`

English:
theorem arg_neg_eq_arg_add_pi_of_im_neg
  given: {x : Complex} (hi : x.im < 0)
  statement: arg (-x) = arg x + π
  proof: by
  rw [arg_of_im_neg hi]; rw [arg_of_im_pos (show 0 < (-x).im from Left.neg_pos_iff.2 hi)]
  simp [neg_div, Real.arccos_neg, add_comm, ← sub_eq_add_neg]

中文:
定理 arg_neg_eq_arg_add_pi_of_im_neg
  条件: {x : 复形} (hi : x.im < 0)
  结论: arg (-x) = arg x + π
  证明: by
  rw [arg_of_im_neg hi]; rw [arg_of_im_pos (show 0 < (-x).im from Left.neg_pos_iff.2 hi)]
  simp [neg_div, Real.arccos_neg, add_comm, ← sub_eq_add_neg]

Depends on / 依赖: Left.neg_pos_iff, Real.arccos_neg, add_comm, arccos_neg, arg_of_im_neg, arg_of_im_pos, neg_div, neg_pos_iff, sub_eq_add_neg
-/
theorem arg_neg_eq_arg_add_pi_of_im_neg {x : Complex} (hi : x.im < 0) : arg (-x) = arg x + π := by
  rw [arg_of_im_neg hi]; rw [arg_of_im_pos (show 0 < (-x).im from Left.neg_pos_iff.2 hi)]
  simp [neg_div, Real.arccos_neg, add_comm, ← sub_eq_add_neg]

/--
theorem `arg_neg_eq_arg_sub_pi_iff` / 定理 `arg_neg_eq_arg_sub_pi_iff`

English:
theorem arg_neg_eq_arg_sub_pi_iff
  given: {x : Complex}
  proof: by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hi, hi.ne, hi.not_gt, arg_neg_eq_arg_add_pi_of_im_neg, sub_eq_add_neg, ←
      add_eq_zero_iff_eq_neg, Real.pi_ne_zero]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, 

中文:
定理 arg_neg_eq_arg_sub_pi_iff
  条件: {x : 复形}
  证明: by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hi, hi.ne, hi.not_gt, arg_neg_eq_arg_add_pi_of_im_neg, sub_eq_add_neg, ←
      add_eq_zero_iff_eq_neg, Real.pi_ne_zero]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, 

Depends on / 依赖: Left.neg_neg_iff, Left.neg_pos_iff, Real.pi_ne_zero, add_eq_z, add_eq_zero_iff_eq_neg, arg_neg_eq_arg_add_pi_of_im_neg, arg_ofReal_of_neg, arg_ofReal_of_nonneg, hi.ne, hi.not_gt, hr.le, hr.not_gt, lt_trichotomy, neg_neg_iff, neg_pos_iff, not_gt, ofReal_neg, pi_ne_zero, sub_eq_add_neg, x.im
-/
theorem arg_neg_eq_arg_sub_pi_iff {x : Complex} :
    arg (-x) = arg x - π ↔ 0 < x.im ∨ x.im = 0 ∧ x.re < 0 := by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hi, hi.ne, hi.not_gt, arg_neg_eq_arg_add_pi_of_im_neg, sub_eq_add_neg, ←
      add_eq_zero_iff_eq_neg, Real.pi_ne_zero]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le]
      simp [hr]
    · simp [hr, Real.pi_ne_zero]
    · rw [arg_ofReal_of_nonneg hr.le, ← ofReal_neg, arg_ofReal_of_neg (Left.neg_neg_iff.2 hr)]
      simp [hr.not_gt, ← add_eq_zero_iff_eq_neg, Real.pi_ne_zero]
  · simp [hi, arg_neg_eq_arg_sub_pi_of_im_pos]

/--
theorem `arg_neg_eq_arg_add_pi_iff` / 定理 `arg_neg_eq_arg_add_pi_iff`

English:
theorem arg_neg_eq_arg_add_pi_iff
  given: {x : Complex}
  proof: by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hi, arg_neg_eq_arg_add_pi_of_im_neg]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le]
      simp [hr.not_g

中文:
定理 arg_neg_eq_arg_add_pi_iff
  条件: {x : 复形}
  证明: by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hi, arg_neg_eq_arg_add_pi_of_im_neg]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le]
      simp [hr.not_g

Depends on / 依赖: Left.neg_neg_iff, Left.neg_pos_iff, Real.pi_ne_zero, Real.pi_ne_zero.symm, arg_neg_eq_arg_add_pi_of_im_neg, arg_neg_eq_arg_sub_, arg_ofReal_of_neg, arg_ofReal_of_nonneg, hi.ne.symm, hi.not_gt, hr.le, hr.not_gt, lt_trichotomy, neg_neg_iff, neg_pos_iff, not_gt, ofReal_neg, pi_ne_zero, two_mul, x.im
-/
theorem arg_neg_eq_arg_add_pi_iff {x : Complex} :
    arg (-x) = arg x + π ↔ x.im < 0 ∨ x.im = 0 ∧ 0 < x.re := by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hi, arg_neg_eq_arg_add_pi_of_im_neg]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le]
      simp [hr.not_gt, ← two_mul, Real.pi_ne_zero]
    · simp [hr, Real.pi_ne_zero.symm]
    · rw [arg_ofReal_of_nonneg hr.le, ← ofReal_neg, arg_ofReal_of_neg (Left.neg_neg_iff.2 hr)]
      simp [hr]
  · simp [hi, hi.ne.symm, hi.not_gt, arg_neg_eq_arg_sub_pi_of_im_pos, sub_eq_add_neg, ←
      add_eq_zero_iff_neg_eq, Real.pi_ne_zero]

/--
theorem `arg_neg_coe_angle` / 定理 `arg_neg_coe_angle`

English:
theorem arg_neg_coe_angle
  given: {x : Complex} (hx : x != 0)
  statement: (arg (-x) : Real.Angle) = arg x + π
  proof: by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · rw [arg_neg_eq_arg_add_pi_of_im_neg hi, Real.Angle.coe_add]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le, ←
 

中文:
定理 arg_neg_coe_angle
  条件: {x : 复形} (hx : x != 0)
  结论: (arg (-x) : 实数.Angle) = arg x + π
  证明: by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · rw [arg_neg_eq_arg_add_pi_of_im_neg hi, Real.Angle.coe_add]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le, ←
 

Depends on / 依赖: False.elim, Left.neg_neg_iff, Left.neg_pos_iff, Real.Angle.co, Real.Angle.coe_add, Real.Angle.coe_two_pi, Real.Angle.coe_zero, arg_neg_eq_arg_add_pi_of_im_neg, arg_ofReal_of_neg, arg_ofReal_of_nonneg, coe_add, coe_two_pi, coe_zero, hr.le, lt_trichotomy, neg_neg_iff, neg_pos_iff, ofReal_neg, two_mul, x.im
-/
theorem arg_neg_coe_angle {x : Complex} (hx : x != 0) : (arg (-x) : Real.Angle) = arg x + π := by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · rw [arg_neg_eq_arg_add_pi_of_im_neg hi, Real.Angle.coe_add]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le, ←
        Real.Angle.coe_add, ← two_mul, Real.Angle.coe_two_pi, Real.Angle.coe_zero]
    · exact False.elim (hx (ext hr hi))
    · rw [arg_ofReal_of_nonneg hr.le, ← ofReal_neg, arg_ofReal_of_neg (Left.neg_neg_iff.2 hr),
        Real.Angle.coe_zero, zero_add]
  · rw [arg_neg_eq_arg_sub_pi_of_im_pos hi, Real.Angle.coe_sub, Real.Angle.sub_coe_pi_eq_add_coe_pi]

/--
theorem `arg_mul_cos_add_sin_mul_I_eq_toIocMod` / 定理 `arg_mul_cos_add_sin_mul_I_eq_toIocMod`

English:
theorem arg_mul_cos_add_sin_mul_I_eq_toIocMod
  given: {r : Real} (hr : 0 < r) (θ : Real)
  proof: by
  rw [arg_real_mul _ hr]; rw [← exp_mul_I]; rw [arg_exp_mul_I]

中文:
定理 arg_mul_cos_add_sin_mul_I_eq_toIocMod
  条件: {r : 实数} (hr : 0 < r) (θ : 实数)
  证明: by
  rw [arg_real_mul _ hr]; rw [← exp_mul_I]; rw [arg_exp_mul_I]

Depends on / 依赖: arg_exp_mul_I, arg_real_mul, exp_mul_I
-/
theorem arg_mul_cos_add_sin_mul_I_eq_toIocMod {r : Real} (hr : 0 < r) (θ : Real) :
    arg (r * (cos θ + sin θ * I)) = toIocMod Real.two_pi_pos (-π) θ := by
  rw [arg_real_mul _ hr]; rw [← exp_mul_I]; rw [arg_exp_mul_I]

/--
theorem `arg_cos_add_sin_mul_I_eq_toIocMod` / 定理 `arg_cos_add_sin_mul_I_eq_toIocMod`

English:
theorem arg_cos_add_sin_mul_I_eq_toIocMod
  given: (θ : Real)
  proof: by
  rw [← one_mul (_ + _)]; rw [← ofReal_one]; rw [arg_mul_cos_add_sin_mul_I_eq_toIocMod zero_lt_one]

中文:
定理 arg_cos_add_sin_mul_I_eq_toIocMod
  条件: (θ : 实数)
  证明: by
  rw [← one_mul (_ + _)]; rw [← ofReal_one]; rw [arg_mul_cos_add_sin_mul_I_eq_toIocMod zero_lt_one]

Depends on / 依赖: arg_mul_cos_add_sin_mul_I_eq_toIocMod, ofReal_one, one_mul, zero_lt_one
-/
theorem arg_cos_add_sin_mul_I_eq_toIocMod (θ : Real) :
    arg (cos θ + sin θ * I) = toIocMod Real.two_pi_pos (-π) θ := by
  rw [← one_mul (_ + _)]; rw [← ofReal_one]; rw [arg_mul_cos_add_sin_mul_I_eq_toIocMod zero_lt_one]

/--
theorem `arg_mul_cos_add_sin_mul_I_sub` / 定理 `arg_mul_cos_add_sin_mul_I_sub`

English:
theorem arg_mul_cos_add_sin_mul_I_sub
  given: {r : Real} (hr : 0 < r) (θ : Real)
  proof: by
  rw [arg_mul_cos_add_sin_mul_I_eq_toIocMod hr]; rw [toIocMod_sub_self]; rw [toIocDiv_eq_neg_floor]; rw [zsmul_eq_mul]
  ring_nf

中文:
定理 arg_mul_cos_add_sin_mul_I_sub
  条件: {r : 实数} (hr : 0 < r) (θ : 实数)
  证明: by
  rw [arg_mul_cos_add_sin_mul_I_eq_toIocMod hr]; rw [toIocMod_sub_self]; rw [toIocDiv_eq_neg_floor]; rw [zsmul_eq_mul]
  ring_nf

Depends on / 依赖: arg_mul_cos_add_sin_mul_I_eq_toIocMod, ring_nf, toIocDiv_eq_neg_floor, toIocMod_sub_self, zsmul_eq_mul
-/
theorem arg_mul_cos_add_sin_mul_I_sub {r : Real} (hr : 0 < r) (θ : Real) :
    arg (r * (cos θ + sin θ * I)) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋ := by
  rw [arg_mul_cos_add_sin_mul_I_eq_toIocMod hr]; rw [toIocMod_sub_self]; rw [toIocDiv_eq_neg_floor]; rw [zsmul_eq_mul]
  ring_nf

/--
theorem `arg_cos_add_sin_mul_I_sub` / 定理 `arg_cos_add_sin_mul_I_sub`

English:
theorem arg_cos_add_sin_mul_I_sub
  given: (θ : Real)
  proof: by
  rw [← one_mul (_ + _)]; rw [← ofReal_one]; rw [arg_mul_cos_add_sin_mul_I_sub zero_lt_one]

中文:
定理 arg_cos_add_sin_mul_I_sub
  条件: (θ : 实数)
  证明: by
  rw [← one_mul (_ + _)]; rw [← ofReal_one]; rw [arg_mul_cos_add_sin_mul_I_sub zero_lt_one]

Depends on / 依赖: arg_mul_cos_add_sin_mul_I_sub, ofReal_one, one_mul, zero_lt_one
-/
theorem arg_cos_add_sin_mul_I_sub (θ : Real) :
    arg (cos θ + sin θ * I) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋ := by
  rw [← one_mul (_ + _)]; rw [← ofReal_one]; rw [arg_mul_cos_add_sin_mul_I_sub zero_lt_one]

/--
theorem `arg_mul_cos_add_sin_mul_I_coe_angle` / 定理 `arg_mul_cos_add_sin_mul_I_coe_angle`

English:
theorem arg_mul_cos_add_sin_mul_I_coe_angle
  given: {r : Real} (hr : 0 < r) (θ : Real.Angle)
  proof: by
  induction θ using Real.Angle.induction_on with | _ θ
  simp [arg_mul_cos_add_sin_mul_I_eq_toIocMod hr]

中文:
定理 arg_mul_cos_add_sin_mul_I_coe_angle
  条件: {r : 实数} (hr : 0 < r) (θ : 实数.Angle)
  证明: by
  induction θ using Real.Angle.induction_on with | _ θ
  simp [arg_mul_cos_add_sin_mul_I_eq_toIocMod hr]

Depends on / 依赖: Real.Angle.induction_on, arg_mul_cos_add_sin_mul_I_eq_toIocMod, induction_on
-/
theorem arg_mul_cos_add_sin_mul_I_coe_angle {r : Real} (hr : 0 < r) (θ : Real.Angle) :
    (arg (r * (Real.Angle.cos θ + Real.Angle.sin θ * I)) : Real.Angle) = θ := by
  induction θ using Real.Angle.induction_on with | _ θ
  simp [arg_mul_cos_add_sin_mul_I_eq_toIocMod hr]

/--
theorem `arg_cos_add_sin_mul_I_coe_angle` / 定理 `arg_cos_add_sin_mul_I_coe_angle`

English:
theorem arg_cos_add_sin_mul_I_coe_angle
  given: (θ : Real.Angle)
  proof: by
  rw [← one_mul (_ + _)]; rw [← ofReal_one]; rw [arg_mul_cos_add_sin_mul_I_coe_angle zero_lt_one]

中文:
定理 arg_cos_add_sin_mul_I_coe_angle
  条件: (θ : 实数.Angle)
  证明: by
  rw [← one_mul (_ + _)]; rw [← ofReal_one]; rw [arg_mul_cos_add_sin_mul_I_coe_angle zero_lt_one]

Depends on / 依赖: arg_mul_cos_add_sin_mul_I_coe_angle, ofReal_one, one_mul, zero_lt_one
-/
theorem arg_cos_add_sin_mul_I_coe_angle (θ : Real.Angle) :
    (arg (Real.Angle.cos θ + Real.Angle.sin θ * I) : Real.Angle) = θ := by
  rw [← one_mul (_ + _)]; rw [← ofReal_one]; rw [arg_mul_cos_add_sin_mul_I_coe_angle zero_lt_one]

/--
theorem `arg_mul_coe_angle` / 定理 `arg_mul_coe_angle`

English:
theorem arg_mul_coe_angle
  given: {x y : Complex} (hx : x != 0) (hy : y != 0)
  proof: by
  convert!
    arg_mul_cos_add_sin_mul_I_coe_angle (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy))
      (arg x + arg y : Real.Angle) using 3
  simp_rw [← Real.Angle.coe_add, Real.Angle.sin_coe, Real.Angle.cos_coe, ofReal_cos, ofReal_sin,
    cos_add_sin_I, ofReal_add, add_mul, exp_add, ofR

中文:
定理 arg_mul_coe_angle
  条件: {x y : 复形} (hx : x != 0) (hy : y != 0)
  证明: by
  convert!
    arg_mul_cos_add_sin_mul_I_coe_angle (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy))
      (arg x + arg y : Real.Angle) using 3
  simp_rw [← Real.Angle.coe_add, Real.Angle.sin_coe, Real.Angle.cos_coe, ofReal_cos, ofReal_sin,
    cos_add_sin_I, ofReal_add, add_mul, exp_add, ofR

Depends on / 依赖: Real.Angle, Real.Angle.coe_add, Real.Angle.cos_coe, Real.Angle.sin_coe, add_mul, arg_mul_cos_add_sin_mul_I_coe_angle, coe_add, convert, cos_add_sin_I, cos_coe, exp_add, mul_assoc, mul_comm, mul_pos, norm_mul_exp_arg_mul_I, norm_pos_iff, norm_pos_iff.mpr, ofReal_add, ofReal_cos, ofReal_mul
-/
theorem arg_mul_coe_angle {x y : Complex} (hx : x != 0) (hy : y != 0) :
    (arg (x * y) : Real.Angle) = arg x + arg y := by
  convert!
    arg_mul_cos_add_sin_mul_I_coe_angle (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy))
      (arg x + arg y : Real.Angle) using 3
  simp_rw [← Real.Angle.coe_add, Real.Angle.sin_coe, Real.Angle.cos_coe, ofReal_cos, ofReal_sin,
    cos_add_sin_I, ofReal_add, add_mul, exp_add, ofReal_mul]
  rw [mul_assoc]; rw [mul_comm (exp _)]; rw [← mul_assoc (‖y‖ : Complex)]; rw [norm_mul_exp_arg_mul_I]; rw [mul_comm y]; rw [←
    mul_assoc]; rw [norm_mul_exp_arg_mul_I]

/--
theorem `arg_div_coe_angle` / 定理 `arg_div_coe_angle`

English:
theorem arg_div_coe_angle
  given: {x y : Complex} (hx : x != 0) (hy : y != 0)
  proof: by
  rw [div_eq_mul_inv]; rw [arg_mul_coe_angle hx (inv_ne_zero hy)]; rw [arg_inv_coe_angle]; rw [sub_eq_add_neg]

中文:
定理 arg_div_coe_angle
  条件: {x y : 复形} (hx : x != 0) (hy : y != 0)
  证明: by
  rw [div_eq_mul_inv]; rw [arg_mul_coe_angle hx (inv_ne_zero hy)]; rw [arg_inv_coe_angle]; rw [sub_eq_add_neg]

Depends on / 依赖: arg_inv_coe_angle, arg_mul_coe_angle, div_eq_mul_inv, inv_ne_zero, sub_eq_add_neg
-/
theorem arg_div_coe_angle {x y : Complex} (hx : x != 0) (hy : y != 0) :
    (arg (x / y) : Real.Angle) = arg x - arg y := by
  rw [div_eq_mul_inv]; rw [arg_mul_coe_angle hx (inv_ne_zero hy)]; rw [arg_inv_coe_angle]; rw [sub_eq_add_neg]

/--
theorem `arg_pow_coe_angle` / 定理 `arg_pow_coe_angle`

English:
theorem arg_pow_coe_angle
  given: (x : Complex) (n : Nat)
  proof: by
  obtain rfl | x0 := eq_or_ne x 0
  · by_cases n0 : n = 0 <;> simp [n0]
  · induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, arg_mul_coe_angle (pow_ne_zero n x0) x0, ih, succ_nsmul]

中文:
定理 arg_pow_coe_angle
  条件: (x : 复形) (n : 自然数)
  证明: by
  obtain rfl | x0 := eq_or_ne x 0
  · by_cases n0 : n = 0 <;> simp [n0]
  · induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, arg_mul_coe_angle (pow_ne_zero n x0) x0, ih, succ_nsmul]

Depends on / 依赖: arg_mul_coe_angle, eq_or_ne, pow_ne_zero, pow_succ, succ_nsmul
-/
theorem arg_pow_coe_angle (x : Complex) (n : Nat) :
    (arg (x ^ n) : Real.Angle) = n • (arg x : Real.Angle) := by
  obtain rfl | x0 := eq_or_ne x 0
  · by_cases n0 : n = 0 <;> simp [n0]
  · induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, arg_mul_coe_angle (pow_ne_zero n x0) x0, ih, succ_nsmul]

/--
theorem `arg_zpow_coe_angle` / 定理 `arg_zpow_coe_angle`

English:
theorem arg_zpow_coe_angle
  given: (x : Complex) (n : Int)
  proof: by
  match n with
  | Int.ofNat m => simp [arg_pow_coe_angle]
  | Int.negSucc m => simp [arg_pow_coe_angle]

@[simp]

中文:
定理 arg_zpow_coe_angle
  条件: (x : 复形) (n : 整数)
  证明: by
  match n with
  | Int.ofNat m => simp [arg_pow_coe_angle]
  | Int.negSucc m => simp [arg_pow_coe_angle]

@[simp]

Depends on / 依赖: Int.negSucc, Int.ofNat, arg_pow_coe_angle, negSucc
-/
theorem arg_zpow_coe_angle (x : Complex) (n : Int) :
    (arg (x ^ n) : Real.Angle) = n • (arg x : Real.Angle) := by
  match n with
  | Int.ofNat m => simp [arg_pow_coe_angle]
  | Int.negSucc m => simp [arg_pow_coe_angle]

@[simp]
/--
theorem `arg_coe_angle_toReal_eq_arg` / 定理 `arg_coe_angle_toReal_eq_arg`

English:
theorem arg_coe_angle_toReal_eq_arg
  given: (z : Complex)
  statement: (arg z : Real.Angle).toReal = arg z
  proof: by
  rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc]
  exact arg_mem_Ioc _

中文:
定理 arg_coe_angle_to实数_eq_arg
  条件: (z : 复形)
  结论: (arg z : 实数.Angle).to实数 = arg z
  证明: by
  rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc]
  exact arg_mem_Ioc _

Depends on / 依赖: Real.Angle.toReal_coe_eq_self_iff_mem_Ioc, arg_mem_Ioc, toReal_coe_eq_self_iff_mem_Ioc
-/
theorem arg_coe_angle_toReal_eq_arg (z : Complex) : (arg z : Real.Angle).toReal = arg z := by
  rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc]
  exact arg_mem_Ioc _

/--
theorem `arg_coe_angle_eq_iff_eq_toReal` / 定理 `arg_coe_angle_eq_iff_eq_toReal`

English:
theorem arg_coe_angle_eq_iff_eq_toReal
  given: {z : Complex} {θ : Real.Angle}
  proof: by
  rw [← Real.Angle.toReal_inj]; rw [arg_coe_angle_toReal_eq_arg]

@[simp]

中文:
定理 arg_coe_angle_eq_iff_eq_to实数
  条件: {z : 复形} {θ : 实数.Angle}
  证明: by
  rw [← Real.Angle.toReal_inj]; rw [arg_coe_angle_toReal_eq_arg]

@[simp]

Depends on / 依赖: Real.Angle.toReal_inj, arg_coe_angle_toReal_eq_arg, toReal_inj
-/
theorem arg_coe_angle_eq_iff_eq_toReal {z : Complex} {θ : Real.Angle} :
    (arg z : Real.Angle) = θ ↔ arg z = θ.toReal := by
  rw [← Real.Angle.toReal_inj]; rw [arg_coe_angle_toReal_eq_arg]

@[simp]
/--
theorem `arg_coe_angle_eq_iff` / 定理 `arg_coe_angle_eq_iff`

English:
theorem arg_coe_angle_eq_iff
  given: {x y : Complex}
  statement: (arg x : Real.Angle) = arg y ↔ arg x = arg y
  proof: by
  simp_rw [← Real.Angle.toReal_inj, arg_coe_angle_toReal_eq_arg]

中文:
定理 arg_coe_angle_eq_iff
  条件: {x y : 复形}
  结论: (arg x : 实数.Angle) = arg y ↔ arg x = arg y
  证明: by
  simp_rw [← Real.Angle.toReal_inj, arg_coe_angle_toReal_eq_arg]

Depends on / 依赖: Real.Angle.toReal_inj, arg_coe_angle_toReal_eq_arg, simp_rw, toReal_inj
-/
theorem arg_coe_angle_eq_iff {x y : Complex} : (arg x : Real.Angle) = arg y ↔ arg x = arg y := by
  simp_rw [← Real.Angle.toReal_inj, arg_coe_angle_toReal_eq_arg]

/--
lemma `arg_mul_eq_add_arg_iff` / 引理 `arg_mul_eq_add_arg_iff`

English:
lemma arg_mul_eq_add_arg_iff
  given: {x y : Complex} (hx₀ : x != 0) (hy₀ : y != 0)
  proof: by
  rw [← arg_coe_angle_toReal_eq_arg]; rw [arg_mul_coe_angle hx₀ hy₀]; rw [← Real.Angle.coe_add]; rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc]

alias ⟨_, arg_mul⟩ := arg_mul_eq_add_arg_iff

中文:
引理 arg_mul_eq_add_arg_iff
  条件: {x y : 复形} (hx₀ : x != 0) (hy₀ : y != 0)
  证明: by
  rw [← arg_coe_angle_toReal_eq_arg]; rw [arg_mul_coe_angle hx₀ hy₀]; rw [← Real.Angle.coe_add]; rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc]

alias ⟨_, arg_mul⟩ := arg_mul_eq_add_arg_iff

Depends on / 依赖: Real.Angle.coe_add, Real.Angle.toReal_coe_eq_self_iff_mem_Ioc, arg_coe_angle_toReal_eq_arg, arg_mul_coe_angle, coe_add, toReal_coe_eq_self_iff_mem_Ioc
-/
lemma arg_mul_eq_add_arg_iff {x y : Complex} (hx₀ : x != 0) (hy₀ : y != 0) :
    (x * y).arg = x.arg + y.arg ↔ arg x + arg y in Set.Ioc (-π) π := by
  rw [← arg_coe_angle_toReal_eq_arg]; rw [arg_mul_coe_angle hx₀ hy₀]; rw [← Real.Angle.coe_add]; rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc]

alias ⟨_, arg_mul⟩ := arg_mul_eq_add_arg_iff

section slitPlane

open ComplexOrder in
/--
lemma `mem_slitPlane_iff_arg` / 引理 `mem_slitPlane_iff_arg`

English:
lemma mem_slitPlane_iff_arg
  given: {z : Complex}
  statement: z in slitPlane ↔ z.arg != π ∧ z != 0
  proof: by
  simp only [mem_slitPlane_iff_not_le_zero, le_iff_lt_or_eq, ne_eq, arg_eq_pi_iff_lt_zero, not_or]

中文:
引理 mem_slitPlane_iff_arg
  条件: {z : 复形}
  结论: z in slitPlane ↔ z.arg != π ∧ z != 0
  证明: by
  simp only [mem_slitPlane_iff_not_le_zero, le_iff_lt_or_eq, ne_eq, arg_eq_pi_iff_lt_zero, not_or]

Depends on / 依赖: arg_eq_pi_iff_lt_zero, le_iff_lt_or_eq, mem_slitPlane_iff_not_le_zero, ne_eq, not_or
-/
lemma mem_slitPlane_iff_arg {z : Complex} : z in slitPlane ↔ z.arg != π ∧ z != 0 := by
  simp only [mem_slitPlane_iff_not_le_zero, le_iff_lt_or_eq, ne_eq, arg_eq_pi_iff_lt_zero, not_or]

/--
lemma `slitPlane_arg_ne_pi` / 引理 `slitPlane_arg_ne_pi`

English:
lemma slitPlane_arg_ne_pi
  given: {z : Complex} (hz : z in slitPlane)
  statement: z.arg != Real.pi
  proof: (mem_slitPlane_iff_arg.mp hz).1

中文:
引理 slitPlane_arg_ne_pi
  条件: {z : 复形} (hz : z in slitPlane)
  结论: z.arg != 实数.pi
  证明: (mem_slitPlane_iff_arg.mp hz).1

Depends on / 依赖: mem_slitPlane_iff_arg, mem_slitPlane_iff_arg.mp
-/
lemma slitPlane_arg_ne_pi {z : Complex} (hz : z in slitPlane) : z.arg != Real.pi :=
  (mem_slitPlane_iff_arg.mp hz).1

/--
theorem `exp_mem_slitPlane` / 定理 `exp_mem_slitPlane`

English:
theorem exp_mem_slitPlane
  given: {z : Complex}
  statement: exp z in slitPlane ↔ toIocMod Real.two_pi_pos (-π) z.im != π
  proof: by
  simp [mem_slitPlane_iff_arg, arg_exp]

中文:
定理 exp_mem_slitPlane
  条件: {z : 复形}
  结论: exp z in slitPlane ↔ toIocMod 实数.two_pi_pos (-π) z.im != π
  证明: by
  simp [mem_slitPlane_iff_arg, arg_exp]

Depends on / 依赖: arg_exp, mem_slitPlane_iff_arg
-/
theorem exp_mem_slitPlane {z : Complex} : exp z in slitPlane ↔ toIocMod Real.two_pi_pos (-π) z.im != π := by
  simp [mem_slitPlane_iff_arg, arg_exp]

end slitPlane

section Continuity

/--
theorem `arg_eq_nhds_of_re_pos` / 定理 `arg_eq_nhds_of_re_pos`

English:
theorem arg_eq_nhds_of_re_pos
  given: (hx : 0 < x.re)
  statement: arg =ᶠ[𝓝 x] fun x => Real.arcsin (x.im / ‖x‖)
  proof: ((continuous_re.tendsto _).eventually (lt_mem_nhds hx)).mono fun _ hy => arg_of_re_nonneg hy.le

中文:
定理 arg_eq_nhds_of_re_pos
  条件: (hx : 0 < x.re)
  结论: arg =ᶠ[𝓝 x] fun x => 实数.arcsin (x.im / ‖x‖)
  证明: ((continuous_re.tendsto _).eventually (lt_mem_nhds hx)).mono fun _ hy => arg_of_re_nonneg hy.le

Depends on / 依赖: arg_of_re_nonneg, continuous_re, continuous_re.tendsto, eventually, hy.le, lt_mem_nhds, tendsto
-/
theorem arg_eq_nhds_of_re_pos (hx : 0 < x.re) : arg =ᶠ[𝓝 x] fun x => Real.arcsin (x.im / ‖x‖) :=
  ((continuous_re.tendsto _).eventually (lt_mem_nhds hx)).mono fun _ hy => arg_of_re_nonneg hy.le

/--
theorem `arg_eq_nhds_of_re_neg_of_im_pos` / 定理 `arg_eq_nhds_of_re_neg_of_im_pos`

English:
theorem arg_eq_nhds_of_re_neg_of_im_pos
  given: (hx_re : x.re < 0) (hx_im : 0 < x.im)
  proof: by
  suffices h_forall_nhds : forallᶠ y : Complex in 𝓝 x, y.re < 0 ∧ 0 < y.im from
    h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_nonneg hy.1 hy.2.le
  refine IsOpen.eventually_mem ?_ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ 0 < x.im)
  exact
    IsOpen.and (isOpen_lt continuous_re continuous_zero) (isO

中文:
定理 arg_eq_nhds_of_re_neg_of_im_pos
  条件: (hx_re : x.re < 0) (hx_im : 0 < x.im)
  证明: by
  suffices h_forall_nhds : forallᶠ y : Complex in 𝓝 x, y.re < 0 ∧ 0 < y.im from
    h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_nonneg hy.1 hy.2.le
  refine IsOpen.eventually_mem ?_ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ 0 < x.im)
  exact
    IsOpen.and (isOpen_lt continuous_re continuous_zero) (isO

Depends on / 依赖: IsOpen, IsOpen.and, IsOpen.eventually_mem, arg_of_re_neg_of_im_nonneg, continuous_im, continuous_re, continuous_zero, eventually_mem, h_forall_nhds, h_forall_nhds.mono, hx_im, hx_re, isOpen_lt, x.im, x.re, y.im, y.re
-/
theorem arg_eq_nhds_of_re_neg_of_im_pos (hx_re : x.re < 0) (hx_im : 0 < x.im) :
    arg =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / ‖x‖) + π := by
  suffices h_forall_nhds : forallᶠ y : Complex in 𝓝 x, y.re < 0 ∧ 0 < y.im from
    h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_nonneg hy.1 hy.2.le
  refine IsOpen.eventually_mem ?_ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ 0 < x.im)
  exact
    IsOpen.and (isOpen_lt continuous_re continuous_zero) (isOpen_lt continuous_zero continuous_im)

/--
theorem `arg_eq_nhds_of_re_neg_of_im_neg` / 定理 `arg_eq_nhds_of_re_neg_of_im_neg`

English:
theorem arg_eq_nhds_of_re_neg_of_im_neg
  given: (hx_re : x.re < 0) (hx_im : x.im < 0)
  proof: by
  suffices h_forall_nhds : forallᶠ y : Complex in 𝓝 x, y.re < 0 ∧ y.im < 0 from
    h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_neg hy.1 hy.2
  refine IsOpen.eventually_mem ?_ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ x.im < 0)
  exact
    IsOpen.and (isOpen_lt continuous_re continuous_zero) (isOpen_lt

中文:
定理 arg_eq_nhds_of_re_neg_of_im_neg
  条件: (hx_re : x.re < 0) (hx_im : x.im < 0)
  证明: by
  suffices h_forall_nhds : forallᶠ y : Complex in 𝓝 x, y.re < 0 ∧ y.im < 0 from
    h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_neg hy.1 hy.2
  refine IsOpen.eventually_mem ?_ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ x.im < 0)
  exact
    IsOpen.and (isOpen_lt continuous_re continuous_zero) (isOpen_lt

Depends on / 依赖: IsOpen, IsOpen.and, IsOpen.eventually_mem, arg_of_re_neg_of_im_neg, continuous_im, continuous_re, continuous_zero, eventually_mem, h_forall_nhds, h_forall_nhds.mono, hx_im, hx_re, isOpen_lt, x.im, x.re, y.im, y.re
-/
theorem arg_eq_nhds_of_re_neg_of_im_neg (hx_re : x.re < 0) (hx_im : x.im < 0) :
    arg =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / ‖x‖) - π := by
  suffices h_forall_nhds : forallᶠ y : Complex in 𝓝 x, y.re < 0 ∧ y.im < 0 from
    h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_neg hy.1 hy.2
  refine IsOpen.eventually_mem ?_ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ x.im < 0)
  exact
    IsOpen.and (isOpen_lt continuous_re continuous_zero) (isOpen_lt continuous_im continuous_zero)

/--
theorem `arg_eq_nhds_of_im_pos` / 定理 `arg_eq_nhds_of_im_pos`

English:
theorem arg_eq_nhds_of_im_pos
  given: (hz : 0 < im z)
  statement: arg =ᶠ[𝓝 z] fun x => Real.arccos (x.re / ‖x‖)
  proof: ((continuous_im.tendsto _).eventually (lt_mem_nhds hz)).mono fun _ => arg_of_im_pos

中文:
定理 arg_eq_nhds_of_im_pos
  条件: (hz : 0 < im z)
  结论: arg =ᶠ[𝓝 z] fun x => 实数.arccos (x.re / ‖x‖)
  证明: ((continuous_im.tendsto _).eventually (lt_mem_nhds hz)).mono fun _ => arg_of_im_pos

Depends on / 依赖: arg_of_im_pos, continuous_im, continuous_im.tendsto, eventually, lt_mem_nhds, tendsto
-/
theorem arg_eq_nhds_of_im_pos (hz : 0 < im z) : arg =ᶠ[𝓝 z] fun x => Real.arccos (x.re / ‖x‖) :=
  ((continuous_im.tendsto _).eventually (lt_mem_nhds hz)).mono fun _ => arg_of_im_pos

/--
theorem `arg_eq_nhds_of_im_neg` / 定理 `arg_eq_nhds_of_im_neg`

English:
theorem arg_eq_nhds_of_im_neg
  given: (hz : im z < 0)
  statement: arg =ᶠ[𝓝 z] fun x => -Real.arccos (x.re / ‖x‖)
  proof: ((continuous_im.tendsto _).eventually (gt_mem_nhds hz)).mono fun _ => arg_of_im_neg

中文:
定理 arg_eq_nhds_of_im_neg
  条件: (hz : im z < 0)
  结论: arg =ᶠ[𝓝 z] fun x => -实数.arccos (x.re / ‖x‖)
  证明: ((continuous_im.tendsto _).eventually (gt_mem_nhds hz)).mono fun _ => arg_of_im_neg

Depends on / 依赖: arg_of_im_neg, continuous_im, continuous_im.tendsto, eventually, gt_mem_nhds, tendsto
-/
theorem arg_eq_nhds_of_im_neg (hz : im z < 0) : arg =ᶠ[𝓝 z] fun x => -Real.arccos (x.re / ‖x‖) :=
  ((continuous_im.tendsto _).eventually (gt_mem_nhds hz)).mono fun _ => arg_of_im_neg

/--
theorem `continuousAt_arg` / 定理 `continuousAt_arg`

English:
theorem continuousAt_arg
  given: (h : x in slitPlane)
  statement: ContinuousAt arg x
  proof: by
  have h₀ : ‖x‖ != 0 := by
    rw [norm_ne_zero_iff]
    exact slitPlane_ne_zero h
  rw [mem_slitPlane_iff]; rw [← lt_or_lt_iff_ne] at h
  rcases h with (hx_re | hx_im | hx_im)
  exacts [(Real.continuousAt_arcsin.comp
          (continuous_im.continuousAt.div continuous_norm.continuousAt h₀)).con

中文:
定理 continuousAt_arg
  条件: (h : x in slitPlane)
  结论: ContinuousAt arg x
  证明: by
  have h₀ : ‖x‖ != 0 := by
    rw [norm_ne_zero_iff]
    exact slitPlane_ne_zero h
  rw [mem_slitPlane_iff]; rw [← lt_or_lt_iff_ne] at h
  rcases h with (hx_re | hx_im | hx_im)
  exacts [(Real.continuousAt_arcsin.comp
          (continuous_im.continuousAt.div continuous_norm.continuousAt h₀)).con

Depends on / 依赖: Real.continuousAt_arcsin.comp, Real.continuous_arccos.continuou, Real.continuous_arccos.continuousAt.comp, arg_eq_nhds_of_im_neg, arg_eq_nhds_of_re_pos, continuou, continuousAt, continuousAt_arcsin, continuous_arccos, continuous_im, continuous_im.continuousAt.div, continuous_norm, continuous_norm.continuousAt, continuous_re, continuous_re.continuousAt.div, exacts, hx_im, hx_re, lt_or_lt_iff_ne, mem_slitPlane_iff
-/
theorem continuousAt_arg (h : x in slitPlane) : ContinuousAt arg x := by
  have h₀ : ‖x‖ != 0 := by
    rw [norm_ne_zero_iff]
    exact slitPlane_ne_zero h
  rw [mem_slitPlane_iff]; rw [← lt_or_lt_iff_ne] at h
  rcases h with (hx_re | hx_im | hx_im)
  exacts [(Real.continuousAt_arcsin.comp
          (continuous_im.continuousAt.div continuous_norm.continuousAt h₀)).congr
      (arg_eq_nhds_of_re_pos hx_re).symm,
    (Real.continuous_arccos.continuousAt.comp
            (continuous_re.continuousAt.div continuous_norm.continuousAt h₀)).neg.congr
      (arg_eq_nhds_of_im_neg hx_im).symm,
    (Real.continuous_arccos.continuousAt.comp
          (continuous_re.continuousAt.div continuous_norm.continuousAt h₀)).congr
      (arg_eq_nhds_of_im_pos hx_im).symm]

@[fun_prop]
/--
theorem `continuousOn_arg` / 定理 `continuousOn_arg`

English:
theorem continuousOn_arg
  statement: ContinuousOn arg slitPlane
  proof: .continuousWithinAt fun _ h => continuousAt_arg h

中文:
定理 continuousOn_arg
  结论: ContinuousOn arg slitPlane
  证明: .continuousWithinAt fun _ h => continuousAt_arg h

Depends on / 依赖: continuousAt_arg, continuousWithinAt
-/
theorem continuousOn_arg : ContinuousOn arg slitPlane :=
.continuousWithinAt fun _ h => continuousAt_arg h

/--
theorem `tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero` / 定理 `tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero`

English:
theorem tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero
  statement: {z : Complex} (hre : z.re < 0)
  proof: by
  suffices H : Tendsto (fun x : Complex => Real.arcsin ((-x).im / ‖x‖) - π)
      (𝓝[{ z : Complex | z.im < 0 }] z) (𝓝 (-π)) by
    refine H.congr' ?_
    have : forallᶠ x : Complex in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWith

中文:
定理 tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero
  结论: {z : 复形} (hre : z.re < 0)
  证明: by
  suffices H : Tendsto (fun x : Complex => Real.arcsin ((-x).im / ‖x‖) - π)
      (𝓝[{ z : Complex | z.im < 0 }] z) (𝓝 (-π)) by
    refine H.congr' ?_
    have : forallᶠ x : Complex in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWith

Depends on / 依赖: H.congr, Real.arcsin, Real.continuousAt_arcsin.comp_continuousWithinAt, Tendsto, arcsin, comp_continuousWithinAt, continuousAt, continuousAt_arcsin, continuousWithi, continuous_im, continuous_im.continuousAt.comp_continuousWithinAt, continuous_re, continuous_re.tendsto, convert, filter_upwards, gt_mem_nhds, him.not_ge, hre.not_ge, if_neg, mem_nhdsWithin_of_mem_nhds
-/
theorem tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero {z : Complex} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto arg (𝓝[{ z : Complex | z.im < 0 }] z) (𝓝 (-π)) := by
  suffices H : Tendsto (fun x : Complex => Real.arcsin ((-x).im / ‖x‖) - π)
      (𝓝[{ z : Complex | z.im < 0 }] z) (𝓝 (-π)) by
    refine H.congr' ?_
    have : forallᶠ x : Complex in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds this] with _ him hre
    rw [arg]; rw [if_neg hre.not_ge]; rw [if_neg him.not_ge]
  convert!
    (Real.continuousAt_arcsin.comp_continuousWithinAt
          ((continuous_im.continuousAt.comp_continuousWithinAt continuousWithinAt_neg).div
            continuous_norm.continuousWithinAt _)).sub_const
      π using 1
  · simp [him]
  · lift z to Real using him
    simpa using hre.ne

/--
theorem `continuousWithinAt_arg_of_re_neg_of_im_zero` / 定理 `continuousWithinAt_arg_of_re_neg_of_im_zero`

English:
theorem continuousWithinAt_arg_of_re_neg_of_im_zero
  given: {z : Complex} (hre : z.re < 0) (him : z.im = 0)
  proof: by
  have : arg =ᶠ[𝓝[{ z : Complex | 0 <= z.im }] z] fun x => Real.arcsin ((-x).im / ‖x‖) + π := by
    have : forallᶠ x : Complex in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    filter_upwards [self_mem_nhdsWithin (s := { z : Complex | 0 <= z.im }),
      mem_nhdsWithin_of_mem_nhd

中文:
定理 continuousWithinAt_arg_of_re_neg_of_im_zero
  条件: {z : 复形} (hre : z.re < 0) (him : z.im = 0)
  证明: by
  have : arg =ᶠ[𝓝[{ z : Complex | 0 <= z.im }] z] fun x => Real.arcsin ((-x).im / ‖x‖) + π := by
    have : forallᶠ x : Complex in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    filter_upwards [self_mem_nhdsWithin (s := { z : Complex | 0 <= z.im }),
      mem_nhdsWithin_of_mem_nhd

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.congr_of_eventuallyEq, Real.arcsin, Real.continuousAt_arcsin.comp_continuousWithinAt, arcsin, comp_continuousWithinAt, congr_of_eventuallyEq, continuou, continuousAt_arcsin, continuous_im, continuous_im.continuou, continuous_re, continuous_re.tendsto, filter_upwards, gt_mem_nhds, hre.not_ge, if_neg, if_pos, mem_nhdsWithin_of_mem_nhds, not_ge
-/
theorem continuousWithinAt_arg_of_re_neg_of_im_zero {z : Complex} (hre : z.re < 0) (him : z.im = 0) :
    ContinuousWithinAt arg { z : Complex | 0 <= z.im } z := by
  have : arg =ᶠ[𝓝[{ z : Complex | 0 <= z.im }] z] fun x => Real.arcsin ((-x).im / ‖x‖) + π := by
    have : forallᶠ x : Complex in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    filter_upwards [self_mem_nhdsWithin (s := { z : Complex | 0 <= z.im }),
      mem_nhdsWithin_of_mem_nhds this] with _ him hre
    rw [arg]; rw [if_neg hre.not_ge]; rw [if_pos him]
  refine ContinuousWithinAt.congr_of_eventuallyEq ?_ this ?_
  · refine
      (Real.continuousAt_arcsin.comp_continuousWithinAt
            ((continuous_im.continuousAt.comp_continuousWithinAt continuousWithinAt_neg).div
              continuous_norm.continuousWithinAt ?_)).add
        tendsto_const_nhds
    lift z to Real using him
    simpa using hre.ne
  · rw [arg, if_neg hre.not_ge, if_pos him.ge]

/--
theorem `tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero` / 定理 `tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero`

English:
theorem tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
  statement: {z : Complex} (hre : z.re < 0)
  proof: by
  simpa only [arg_eq_pi_iff.2 ⟨hre, him⟩] using
    (continuousWithinAt_arg_of_re_neg_of_im_zero hre him).tendsto

中文:
定理 tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
  结论: {z : 复形} (hre : z.re < 0)
  证明: by
  simpa only [arg_eq_pi_iff.2 ⟨hre, him⟩] using
    (continuousWithinAt_arg_of_re_neg_of_im_zero hre him).tendsto

Depends on / 依赖: arg_eq_pi_iff, continuousWithinAt_arg_of_re_neg_of_im_zero, tendsto
-/
theorem tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero {z : Complex} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto arg (𝓝[{ z : Complex | 0 <= z.im }] z) (𝓝 π) := by
  simpa only [arg_eq_pi_iff.2 ⟨hre, him⟩] using
    (continuousWithinAt_arg_of_re_neg_of_im_zero hre him).tendsto

/--
theorem `continuousAt_arg_coe_angle` / 定理 `continuousAt_arg_coe_angle`

English:
theorem continuousAt_arg_coe_angle
  given: (h : x != 0)
  statement: ContinuousAt ((↑) ∘ arg : Complex -> Real.Angle) x
  proof: by
  by_cases hs : x in slitPlane
  · exact Real.Angle.continuous_coe.continuousAt.comp (continuousAt_arg hs)
  · rw [← Function.comp_id (((↑) : Real -> Real.Angle) ∘ arg),
      (funext_iff.2 fun _ => (neg_neg _).symm : (id : Complex -> Complex) = Neg.neg ∘ Neg.neg), ←
      Function.comp_assoc]
  

中文:
定理 continuousAt_arg_coe_angle
  条件: (h : x != 0)
  结论: ContinuousAt ((↑) ∘ arg : 复形 -> 实数.Angle) x
  证明: by
  by_cases hs : x in slitPlane
  · exact Real.Angle.continuous_coe.continuousAt.comp (continuousAt_arg hs)
  · rw [← Function.comp_id (((↑) : Real -> Real.Angle) ∘ arg),
      (funext_iff.2 fun _ => (neg_neg _).symm : (id : Complex -> Complex) = Neg.neg ∘ Neg.neg), ←
      Function.comp_assoc]
  

Depends on / 依赖: ContinuousAt, ContinuousAt.comp, Function, Function.comp_assoc, Function.comp_id, Function.update, Neg.neg, Real.Angle, Real.Angle.continuous_coe.continuousAt.comp, comp_assoc, comp_id, continuousAt, continuousAt_arg, continuousAt_update_of_ne, continuous_coe, continuous_neg, continuous_neg.continuousAt, funext_iff, neg_ne_zero, neg_neg
-/
theorem continuousAt_arg_coe_angle (h : x != 0) : ContinuousAt ((↑) ∘ arg : Complex -> Real.Angle) x := by
  by_cases hs : x in slitPlane
  · exact Real.Angle.continuous_coe.continuousAt.comp (continuousAt_arg hs)
  · rw [← Function.comp_id (((↑) : Real -> Real.Angle) ∘ arg),
      (funext_iff.2 fun _ => (neg_neg _).symm : (id : Complex -> Complex) = Neg.neg ∘ Neg.neg), ←
      Function.comp_assoc]
    refine ContinuousAt.comp ?_ continuous_neg.continuousAt
    suffices ContinuousAt (Function.update (((↑) ∘ arg) ∘ Neg.neg : Complex -> Real.Angle) 0 π) (-x) by
      rwa [continuousAt_update_of_ne (neg_ne_zero.2 h)] at this
    have ha :
      Function.update (((↑) ∘ arg) ∘ Neg.neg : Complex -> Real.Angle) 0 π = fun z =>
        (arg z : Real.Angle) + π := by
      rw [Function.update_eq_iff]
      exact ⟨by simp, fun z hz => arg_neg_coe_angle hz⟩
    rw [ha]
    replace hs := mem_slitPlane_iff.mpr.mt hs
    push Not at hs
    refine
      (Real.Angle.continuous_coe.continuousAt.comp (continuousAt_arg (Or.inl ?_))).add
        continuousAt_const
    rw [neg_re]; rw [neg_pos]
    exact hs.1.lt_of_ne fun h0 => h (Complex.ext_iff.2 ⟨h0, hs.2⟩)

end Continuity

end Complex
