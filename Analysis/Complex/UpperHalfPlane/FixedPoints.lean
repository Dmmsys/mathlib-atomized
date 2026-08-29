/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Fixed points of isometries of the upper half-plane

In this file we show that the scalar multiplication by an element `g : GL (Fin 2) ℝ`
has the following set of fixed points, depending on `g`.

- if `g` preserves orientation (i.e., has positive determinant) and is an elliptic matrix,
  then `z ↦ g • z` has a unique fixed point;
- if `g` is a scalar matrix, then it acts by the identity map (proved upstream of this file);
- if `g` preserves orientation, and is a parabolic or a hyperbolic matrix,
  then it has no fixed points;
- if `g` reverses orientation and has zero trace, then it has a geodesic line of fixed points;
  - if `g 1 0 = 0`, then this is the vertical line `re z = g 0 1 / (2 * g 1 1)`;
  - otherwise, it's a half-circle with its center on the real axis;
- if `g` reverses orientation and has nonzero trace, then it has no fixed points.

As a corollary of this classification, we conclude that `PSL(2, ℝ)` acts faithfully
on the upper half-plane.
-/

open Matrix
open scoped MatrixGroups ComplexConjugate

public noncomputable section

namespace UpperHalfPlane

section GLAction

variable {g : GL (Fin 2) Real} {z w : ℍ}

/--
theorem `gl_smul_eq_iff_num_eq` / 定理 `gl_smul_eq_iff_num_eq`

English:
theorem gl_smul_eq_iff_num_eq
  proof: by
  rw [← (σ g).injective.eq_iff]
  simp [UpperHalfPlane.ext_iff, coe_smul, div_eq_iff]

中文:
定理 gl_smul_eq_iff_num_eq
  证明: by
  rw [← (σ g).injective.eq_iff]
  simp [UpperHalfPlane.ext_iff, coe_smul, div_eq_iff]

Depends on / 依赖: UpperHalfPlane, UpperHalfPlane.ext_iff, coe_smul, div_eq_iff, eq_iff, ext_iff, injective, injective.eq_iff
-/
theorem gl_smul_eq_iff_num_eq :
    g • z = w ↔ num g z = σ g w * denom g z := by
  rw [← (σ g).injective.eq_iff]
  simp [UpperHalfPlane.ext_iff, coe_smul, div_eq_iff]

/--
theorem `gl_smul_eq_self_iff_re_eq` / 定理 `gl_smul_eq_self_iff_re_eq`

English:
theorem gl_smul_eq_self_iff_re_eq
  given: (htrace : g.val.trace = 0) (hc : g 1 0 = 0)
  proof: by
  rw [Matrix.trace_fin_two]; rw [add_eq_zero_iff_eq_neg] at htrace
  have h₀ : g 1 1 != 0 := by
    intro h₀
    simpa [Matrix.det_fin_two, hc, h₀] using g.det_ne_zero
  have h : g.val.det < 0 := by simp [Matrix.det_fin_two, *]
  simp [gl_smul_eq_iff_num_eq, Complex.ext_iff, htrace, hc, num, denom, σ, h.not_gt, mul_comm,
    eq_div_iff, h₀]
  grind

中文:
定理 gl_smul_eq_self_iff_re_eq
  条件: (htrace : g.val.trace = 0) (hc : g 1 0 = 0)
  证明: by
  rw [Matrix.trace_fin_two]; rw [add_eq_zero_iff_eq_neg] at htrace
  have h₀ : g 1 1 != 0 := by
    intro h₀
    simpa [Matrix.det_fin_two, hc, h₀] using g.det_ne_zero
  have h : g.val.det < 0 := by simp [Matrix.det_fin_two, *]
  simp [gl_smul_eq_iff_num_eq, Complex.ext_iff, htrace, hc, num, denom, σ, h.not_gt, mul_comm,
    eq_div_iff, h₀]
  grind

Depends on / 依赖: Complex.ext_iff, Matrix, Matrix.det_fin_two, Matrix.trace_fin_two, add_eq_zero_iff_eq_neg, det_fin_two, det_ne_zero, eq_div_iff, ext_iff, g.det_ne_zero, g.val.det, gl_smul_eq_iff_num_eq, h.not_gt, htrace, mul_comm, not_gt, trace_fin_two
-/
theorem gl_smul_eq_self_iff_re_eq (htrace : g.val.trace = 0) (hc : g 1 0 = 0) :
    g • z = z ↔ z.re = g 0 1 / (2 * g 1 1) := by
  rw [Matrix.trace_fin_two]; rw [add_eq_zero_iff_eq_neg] at htrace
  have h₀ : g 1 1 != 0 := by
    intro h₀
    simpa [Matrix.det_fin_two, hc, h₀] using g.det_ne_zero
  have h : g.val.det < 0 := by simp [Matrix.det_fin_two, *]
  simp [gl_smul_eq_iff_num_eq, Complex.ext_iff, htrace, hc, num, denom, σ, h.not_gt, mul_comm,
    eq_div_iff, h₀]
  grind

/--
theorem `gl_smul_eq_self_iff_dist_sq_eq` / 定理 `gl_smul_eq_self_iff_dist_sq_eq`

English:
theorem gl_smul_eq_self_iff_dist_sq_eq
  statement: (h : g.val.det < 0) (htrace : g.val.trace = 0)
  proof: by
  rw [Matrix.trace_fin_two]; rw [← eq_neg_iff_add_eq_zero] at htrace
  rw [eq_div_iff (by positivity)]; rw [dist_eq_norm]; rw [← Complex.normSq_eq_norm_sq]; rw [Complex.normSq_apply]; rw [gl_smul_eq_iff_num_eq]; rw [σ]; rw [g.val_det_apply]; rw [if_neg h.not_gt]
  simp [num, denom, Complex.ext_iff, htrace, Matrix.det_fin_two, field]
  grind

中文:
定理 gl_smul_eq_self_iff_dist_sq_eq
  结论: (h : g.val.det < 0) (htrace : g.val.trace = 0)
  证明: by
  rw [Matrix.trace_fin_two]; rw [← eq_neg_iff_add_eq_zero] at htrace
  rw [eq_div_iff (by positivity)]; rw [dist_eq_norm]; rw [← Complex.normSq_eq_norm_sq]; rw [Complex.normSq_apply]; rw [gl_smul_eq_iff_num_eq]; rw [σ]; rw [g.val_det_apply]; rw [if_neg h.not_gt]
  simp [num, denom, Complex.ext_iff, htrace, Matrix.det_fin_two, field]
  grind

Depends on / 依赖: Complex.ext_iff, Complex.normSq_apply, Complex.normSq_eq_norm_sq, Matrix, Matrix.det_fin_two, Matrix.trace_fin_two, det_fin_two, dist_eq_norm, eq_div_iff, eq_neg_iff_add_eq_zero, ext_iff, g.val_det_apply, gl_smul_eq_iff_num_eq, h.not_gt, htrace, if_neg, normSq_apply, normSq_eq_norm_sq, not_gt, trace_fin_two
-/
theorem gl_smul_eq_self_iff_dist_sq_eq (h : g.val.det < 0) (htrace : g.val.trace = 0)
    (hc : g 1 0 != 0) :
    g • z = z ↔ dist (z : Complex) (-g 1 1 / g 1 0) ^ 2 = (-g.val.det) / g 1 0 ^ 2 := by
  rw [Matrix.trace_fin_two]; rw [← eq_neg_iff_add_eq_zero] at htrace
  rw [eq_div_iff (by positivity)]; rw [dist_eq_norm]; rw [← Complex.normSq_eq_norm_sq]; rw [Complex.normSq_apply]; rw [gl_smul_eq_iff_num_eq]; rw [σ]; rw [g.val_det_apply]; rw [if_neg h.not_gt]
  simp [num, denom, Complex.ext_iff, htrace, Matrix.det_fin_two, field]
  grind

/--
theorem `gl_smul_eq_self_iff_dist_eq` / 定理 `gl_smul_eq_self_iff_dist_eq`

English:
theorem gl_smul_eq_self_iff_dist_eq
  statement: (h : g.val.det < 0) (htrace : g.val.trace = 0)
  proof: by
  rw [gl_smul_eq_self_iff_dist_sq_eq h htrace hc]; rw [eq_comm]; rw [← Real.sqrt_eq_iff_eq_sq]; rw [eq_comm]; rw [Real.sqrt_div']; rw [Real.sqrt_sq_eq_abs] <;> positivity [neg_pos.mpr h]

中文:
定理 gl_smul_eq_self_iff_dist_eq
  结论: (h : g.val.det < 0) (htrace : g.val.trace = 0)
  证明: by
  rw [gl_smul_eq_self_iff_dist_sq_eq h htrace hc]; rw [eq_comm]; rw [← Real.sqrt_eq_iff_eq_sq]; rw [eq_comm]; rw [Real.sqrt_div']; rw [Real.sqrt_sq_eq_abs] <;> positivity [neg_pos.mpr h]

Depends on / 依赖: Real.sqrt_div, Real.sqrt_eq_iff_eq_sq, Real.sqrt_sq_eq_abs, eq_comm, gl_smul_eq_self_iff_dist_sq_eq, htrace, neg_pos, neg_pos.mpr, sqrt_div, sqrt_eq_iff_eq_sq, sqrt_sq_eq_abs
-/
theorem gl_smul_eq_self_iff_dist_eq (h : g.val.det < 0) (htrace : g.val.trace = 0)
    (hc : g 1 0 != 0) :
    g • z = z ↔ dist (z : Complex) (-g 1 1 / g 1 0) = √(-g.val.det) / |g 1 0| := by
  rw [gl_smul_eq_self_iff_dist_sq_eq h htrace hc]; rw [eq_comm]; rw [← Real.sqrt_eq_iff_eq_sq]; rw [eq_comm]; rw [Real.sqrt_div']; rw [Real.sqrt_sq_eq_abs] <;> positivity [neg_pos.mpr h]

/--
theorem `exists_gl_smul_eq_self_iff_trace_eq_zero` / 定理 `exists_gl_smul_eq_self_iff_trace_eq_zero`

English:
theorem exists_gl_smul_eq_self_iff_trace_eq_zero
  given: (h : g.val.det < 0)
  proof: by
  constructor
  · rintro ⟨z, hz⟩
    linear_combination
      (norm := { simp [σ, h.not_gt, num, denom, z.im_ne_zero, Matrix.trace_fin_two, field] })
      congr($(gl_smul_eq_iff_num_eq.mp hz).im / z.im)
  · intro hadd
    by_cases hc : g 1 0 = 0
    · use ⟨⟨g 0 1 / (2 * g 1 1), 1⟩, one_pos⟩
      simp [gl_smul_eq_self_iff_re_eq, *]
    · use ⟨⟨-g 1 1 / g 1 0, √(-g.val.det) / |g 1 0|⟩, by simp [*]⟩
      simp [gl_smul_eq_self_iff_dist_sq_eq, *, dist_eq_norm, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply, ← pow_two, div_pow, h.le]

中文:
定理 存在_gl_smul_eq_self_iff_trace_eq_zero
  条件: (h : g.val.det < 0)
  证明: by
  constructor
  · rintro ⟨z, hz⟩
    linear_combination
      (norm := { simp [σ, h.not_gt, num, denom, z.im_ne_zero, Matrix.trace_fin_two, field] })
      congr($(gl_smul_eq_iff_num_eq.mp hz).im / z.im)
  · intro hadd
    by_cases hc : g 1 0 = 0
    · use ⟨⟨g 0 1 / (2 * g 1 1), 1⟩, one_pos⟩
      simp [gl_smul_eq_self_iff_re_eq, *]
    · use ⟨⟨-g 1 1 / g 1 0, √(-g.val.det) / |g 1 0|⟩, by simp [*]⟩
      simp [gl_smul_eq_self_iff_dist_sq_eq, *, dist_eq_norm, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply, ← pow_two, div_pow, h.le]

Depends on / 依赖: Complex.normSq_apply, Complex.normSq_eq_norm_sq, Matrix, Matrix.trace_fin_two, dist_eq_norm, div_pow, g.val.det, gl_smul_eq_iff_num_eq, gl_smul_eq_iff_num_eq.mp, gl_smul_eq_self_iff_dist_sq_eq, gl_smul_eq_self_iff_re_eq, h.le, h.not_gt, im_ne_zero, linear_combination, normSq_apply, normSq_eq_norm_sq, not_gt, one_pos, pow_two
-/
theorem exists_gl_smul_eq_self_iff_trace_eq_zero (h : g.val.det < 0) :
    (exists z : ℍ, g • z = z) ↔ g.val.trace = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    linear_combination
      (norm := { simp [σ, h.not_gt, num, denom, z.im_ne_zero, Matrix.trace_fin_two, field] })
      congr($(gl_smul_eq_iff_num_eq.mp hz).im / z.im)
  · intro hadd
    by_cases hc : g 1 0 = 0
    · use ⟨⟨g 0 1 / (2 * g 1 1), 1⟩, one_pos⟩
      simp [gl_smul_eq_self_iff_re_eq, *]
    · use ⟨⟨-g 1 1 / g 1 0, √(-g.val.det) / |g 1 0|⟩, by simp [*]⟩
      simp [gl_smul_eq_self_iff_dist_sq_eq, *, dist_eq_norm, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply, ← pow_two, div_pow, h.le]

/--
theorem `gl_smul_eq_self_iff_quadratic` / 定理 `gl_smul_eq_self_iff_quadratic`

English:
theorem gl_smul_eq_self_iff_quadratic
  given: (h : 0 < g.val.det)
  proof: by
  simp [gl_smul_eq_iff_num_eq, σ, h, num, denom]
  grind

中文:
定理 gl_smul_eq_self_iff_quadratic
  条件: (h : 0 < g.val.det)
  证明: by
  simp [gl_smul_eq_iff_num_eq, σ, h, num, denom]
  grind

Depends on / 依赖: gl_smul_eq_iff_num_eq
-/
theorem gl_smul_eq_self_iff_quadratic (h : 0 < g.val.det) :
    g • z = z ↔ (g 1 0 * (z * z) + (g 1 1 - g 0 0) * z + -g 0 1 : Complex) = 0 := by
  simp [gl_smul_eq_iff_num_eq, σ, h, num, denom]
  grind

/--
theorem `isElliptic_of_exists_smul_eq_self` / 定理 `isElliptic_of_exists_smul_eq_self`

English:
theorem isElliptic_of_exists_smul_eq_self
  statement: (h : 0 < g.val.det) (hgc : g ∉ Subgroup.center _)
  proof: by
  rcases hfix with ⟨z, hz⟩
  have hc : g 1 0 != 0 := by
    intro hc
    simp [GeneralLinearGroup.mem_center_iff_val_mem_range_scalar, ← Matrix.ext_iff, hc] at hgc
    simp [gl_smul_eq_iff_num_eq, Complex.ext_iff, σ, h, num, denom, hc, mul_comm, z.im_ne_zero]
      at hz
    grind
  refine lt_of_not_ge fun hge => ?_
  have hd : discrim (g 1 0 : Complex) (g 1 1 - g 0 0) (-g 0 1) = √g.val.discr * √g.val.discr := by
    rw [← Complex.ofReal_mul]; rw [Real.mul_self_sqrt hge]
    simp [discrim, Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
    ring
  rw [gl_smul_eq_self_iff_quadratic h]; rw [quadratic_eq_zero_iff (mod_cast hc) hd] at hz
  norm_cast at hz
  simp only [z.ne_ofReal, false_or] at hz

中文:
定理 isElliptic_of_存在_smul_eq_self
  结论: (h : 0 < g.val.det) (hgc : g ∉ 子群.center _)
  证明: by
  rcases hfix with ⟨z, hz⟩
  have hc : g 1 0 != 0 := by
    intro hc
    simp [GeneralLinearGroup.mem_center_iff_val_mem_range_scalar, ← Matrix.ext_iff, hc] at hgc
    simp [gl_smul_eq_iff_num_eq, Complex.ext_iff, σ, h, num, denom, hc, mul_comm, z.im_ne_zero]
      at hz
    grind
  refine lt_of_not_ge fun hge => ?_
  have hd : discrim (g 1 0 : Complex) (g 1 1 - g 0 0) (-g 0 1) = √g.val.discr * √g.val.discr := by
    rw [← Complex.ofReal_mul]; rw [Real.mul_self_sqrt hge]
    simp [discrim, Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
    ring
  rw [gl_smul_eq_self_iff_quadratic h]; rw [quadratic_eq_zero_iff (mod_cast hc) hd] at hz
  norm_cast at hz
  simp only [z.ne_ofReal, false_or] at hz

Depends on / 依赖: Complex.ext_iff, Complex.ofReal_mul, GeneralLinearGroup, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar, Matrix, Matrix.discr_fin_two, Matrix.ext_iff, Matrix.trace_fin_t, Real.mul_self_sqrt, discr_fin_two, discrim, ext_iff, g.val.discr, gl_smul_eq_iff_num_eq, im_ne_zero, lt_of_not_ge, mem_center_iff_val_mem_range_scalar, mul_comm, mul_self_sqrt, ofReal_mul
-/
theorem isElliptic_of_exists_smul_eq_self (h : 0 < g.val.det) (hgc : g ∉ Subgroup.center _)
    (hfix : exists z : ℍ, g • z = z) : g.IsElliptic := by
  rcases hfix with ⟨z, hz⟩
  have hc : g 1 0 != 0 := by
    intro hc
    simp [GeneralLinearGroup.mem_center_iff_val_mem_range_scalar, ← Matrix.ext_iff, hc] at hgc
    simp [gl_smul_eq_iff_num_eq, Complex.ext_iff, σ, h, num, denom, hc, mul_comm, z.im_ne_zero]
      at hz
    grind
  refine lt_of_not_ge fun hge => ?_
  have hd : discrim (g 1 0 : Complex) (g 1 1 - g 0 0) (-g 0 1) = √g.val.discr * √g.val.discr := by
    rw [← Complex.ofReal_mul]; rw [Real.mul_self_sqrt hge]
    simp [discrim, Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
    ring
  rw [gl_smul_eq_self_iff_quadratic h]; rw [quadratic_eq_zero_iff (mod_cast hc) hd] at hz
  norm_cast at hz
  simp only [z.ne_ofReal, false_or] at hz

/--
Definition of `fixedPt` / `fixedPt` 的定义

English:
definition fixedPt
  signature: (g : GL (Fin 2) Real) (hell : g.IsElliptic)
  body: ⟨(g 0 0 - g 1 1) / (2 * g 1 0) + .I * (√(-g.val.discr) / (2 * |g 1 0|)), by
    simpa [div_pos, Complex.div_re, Complex.div_im, hell.c_ne_zero]⟩

@[simp]

中文:
定义 fixedPt
  签名: (g : GL (有限集 2) 实数) (hell : g.是Elliptic)
  定义体: ⟨(g 0 0 - g 1 1) / (2 * g 1 0) + .I * (√(-g.val.discr) / (2 * |g 1 0|)), by
    simpa [div_pos, Complex.div_re, Complex.div_im, hell.c_ne_zero]⟩

@[simp]

Depends on / 依赖: Complex.div_im, Complex.div_re, c_ne_zero, div_im, div_pos, div_re, g.val.discr, hell.c_ne_zero
-/
def fixedPt (g : GL (Fin 2) Real) (hell : g.IsElliptic) : ℍ :=
  ⟨(g 0 0 - g 1 1) / (2 * g 1 0) + .I * (√(-g.val.discr) / (2 * |g 1 0|)), by
    simpa [div_pos, Complex.div_re, Complex.div_im, hell.c_ne_zero]⟩

@[simp]
/--
theorem `fixedPt_neg` / 定理 `fixedPt_neg`

English:
theorem fixedPt_neg
  given: (hg : (-g).IsElliptic)
  proof: by
  ext
  simp [fixedPt, Matrix.discr_fin_two, Matrix.det_neg]
  ring

中文:
定理 fixedPt_neg
  条件: (hg : (-g).是Elliptic)
  证明: by
  ext
  simp [fixedPt, Matrix.discr_fin_two, Matrix.det_neg]
  ring

Depends on / 依赖: Matrix, Matrix.det_neg, Matrix.discr_fin_two, det_neg, discr_fin_two, fixedPt
-/
theorem fixedPt_neg (hg : (-g).IsElliptic) :
    fixedPt (-g) hg = fixedPt g (isElliptic_neg_iff.mp hg) := by
  ext
  simp [fixedPt, Matrix.discr_fin_two, Matrix.det_neg]
  ring

/--
theorem `gl_smul_eq_self_iff_eq_fixedPt` / 定理 `gl_smul_eq_self_iff_eq_fixedPt`

English:
theorem gl_smul_eq_self_iff_eq_fixedPt
  given: (hpos : 0 < g.val.det) (hell : g.IsElliptic)
  proof: by
  wlog hc : 0 < g 1 0 generalizing g
  · replace hc := hell.c_ne_zero.lt_or_gt.resolve_right hc
    simpa using @this (-g) (by simpa [Matrix.det_neg]) hell.neg (by simpa)
  have hd : discrim (g 1 0 : Complex) (g 1 1 - g 0 0) (-g 0 1) = (.I * √(-g.val.discr)) ^ 2 := by
    rw [mul_pow]; rw [← Complex.ofReal_pow]; rw [Real.sq_sqrt]
    · simp [discrim, Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
      grind
    · simpa using hell.le
  rw [gl_smul_eq_self_iff_quadratic hpos]; rw [quadratic_eq_zero_iff (mod_cast hell.c_ne_zero)
    (hd.trans (pow_two _))]
  rw [or_iff_left]
  · simp [fixedPt, UpperHalfPlane.ext_iff, abs_of_pos hc, field]
  · intro h
    refine z.im_pos.not_ge ?_
    rw [← coe_im]; rw [h]
    simp [Complex.div_im, div_nonpos_iff, hc.le, mul_nonneg]

中文:
定理 gl_smul_eq_self_iff_eq_fixedPt
  条件: (hpos : 0 < g.val.det) (hell : g.是Elliptic)
  证明: by
  wlog hc : 0 < g 1 0 generalizing g
  · replace hc := hell.c_ne_zero.lt_or_gt.resolve_right hc
    simpa using @this (-g) (by simpa [Matrix.det_neg]) hell.neg (by simpa)
  have hd : discrim (g 1 0 : Complex) (g 1 1 - g 0 0) (-g 0 1) = (.I * √(-g.val.discr)) ^ 2 := by
    rw [mul_pow]; rw [← Complex.ofReal_pow]; rw [Real.sq_sqrt]
    · simp [discrim, Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
      grind
    · simpa using hell.le
  rw [gl_smul_eq_self_iff_quadratic hpos]; rw [quadratic_eq_zero_iff (mod_cast hell.c_ne_zero)
    (hd.trans (pow_two _))]
  rw [or_iff_left]
  · simp [fixedPt, UpperHalfPlane.ext_iff, abs_of_pos hc, field]
  · intro h
    refine z.im_pos.not_ge ?_
    rw [← coe_im]; rw [h]
    simp [Complex.div_im, div_nonpos_iff, hc.le, mul_nonneg]

Depends on / 依赖: Complex.ofReal_pow, Matrix, Matrix.det_fin_two, Matrix.det_neg, Matrix.discr_fin_two, Matrix.trace_fin_two, Real.sq_sqrt, c_ne_zero, det_fin_two, det_neg, discr_fin_two, discrim, g.val.discr, generalizing, gl_smul_eq_self_iff_quadratic, hell.c_ne_zero.lt_or_gt.resolve_right, hell.le, hell.neg, lt_or_gt, mul_pow
-/
theorem gl_smul_eq_self_iff_eq_fixedPt (hpos : 0 < g.val.det) (hell : g.IsElliptic) :
    g • z = z ↔ z = fixedPt g hell := by
  wlog hc : 0 < g 1 0 generalizing g
  · replace hc := hell.c_ne_zero.lt_or_gt.resolve_right hc
    simpa using @this (-g) (by simpa [Matrix.det_neg]) hell.neg (by simpa)
  have hd : discrim (g 1 0 : Complex) (g 1 1 - g 0 0) (-g 0 1) = (.I * √(-g.val.discr)) ^ 2 := by
    rw [mul_pow]; rw [← Complex.ofReal_pow]; rw [Real.sq_sqrt]
    · simp [discrim, Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
      grind
    · simpa using hell.le
  rw [gl_smul_eq_self_iff_quadratic hpos]; rw [quadratic_eq_zero_iff (mod_cast hell.c_ne_zero)
    (hd.trans (pow_two _))]
  rw [or_iff_left]
  · simp [fixedPt, UpperHalfPlane.ext_iff, abs_of_pos hc, field]
  · intro h
    refine z.im_pos.not_ge ?_
    rw [← coe_im]; rw [h]
    simp [Complex.div_im, div_nonpos_iff, hc.le, mul_nonneg]

/--
theorem `gl_smul_I_eq_I_iff_of_pos` / 定理 `gl_smul_I_eq_I_iff_of_pos`

English:
theorem gl_smul_I_eq_I_iff_of_pos
  given: {g : GL (Fin 2) Real} (hg : 0 < g.det.val)
  proof: by
  rw [gl_smul_eq_iff_num_eq]; rw [σ]; rw [if_pos hg]
  simp [Complex.ext_iff, num, denom, and_comm]

中文:
定理 gl_smul_I_eq_I_iff_of_pos
  条件: {g : GL (有限集 2) 实数} (hg : 0 < g.det.val)
  证明: by
  rw [gl_smul_eq_iff_num_eq]; rw [σ]; rw [if_pos hg]
  simp [Complex.ext_iff, num, denom, and_comm]

Depends on / 依赖: Complex.ext_iff, and_comm, ext_iff, gl_smul_eq_iff_num_eq, if_pos
-/
theorem gl_smul_I_eq_I_iff_of_pos {g : GL (Fin 2) Real} (hg : 0 < g.det.val) :
    g • I = I ↔ g 0 0 = g 1 1 ∧ g 0 1 = -g 1 0 := by
  rw [gl_smul_eq_iff_num_eq]; rw [σ]; rw [if_pos hg]
  simp [Complex.ext_iff, num, denom, and_comm]

/--
theorem `gl_smul_I_eq_I_iff_of_neg` / 定理 `gl_smul_I_eq_I_iff_of_neg`

English:
theorem gl_smul_I_eq_I_iff_of_neg
  given: {g : GL (Fin 2) Real} (hg : g.det.val < 0)
  proof: by
  rw [gl_smul_eq_iff_num_eq]; rw [σ]; rw [if_neg (not_lt_of_gt hg)]
  simp [num, denom, Complex.ext_iff, and_comm]

中文:
定理 gl_smul_I_eq_I_iff_of_neg
  条件: {g : GL (有限集 2) 实数} (hg : g.det.val < 0)
  证明: by
  rw [gl_smul_eq_iff_num_eq]; rw [σ]; rw [if_neg (not_lt_of_gt hg)]
  simp [num, denom, Complex.ext_iff, and_comm]

Depends on / 依赖: Complex.ext_iff, and_comm, ext_iff, gl_smul_eq_iff_num_eq, if_neg, not_lt_of_gt
-/
theorem gl_smul_I_eq_I_iff_of_neg {g : GL (Fin 2) Real} (hg : g.det.val < 0) :
    g • I = I ↔ g 0 0 = -g 1 1 ∧ g 0 1 = g 1 0 := by
  rw [gl_smul_eq_iff_num_eq]; rw [σ]; rw [if_neg (not_lt_of_gt hg)]
  simp [num, denom, Complex.ext_iff, and_comm]

/--
theorem `forall_smul_eq_self_iff_mem_center` / 定理 `forall_smul_eq_self_iff_mem_center`

English:
theorem forall_smul_eq_self_iff_mem_center
  given: {g : GL (Fin 2) Real}
  proof: by
  constructor
  · intro hg
    by_contra! hgc
    rcases g.det_ne_zero.lt_or_gt with hlt | hgt
    · obtain ⟨ha, hb⟩ := (gl_smul_I_eq_I_iff_of_neg hlt).mp (hg _)
      rw [eq_neg_iff_add_eq_zero]; rw [← Matrix.trace_fin_two] at ha
      rcases eq_or_ne (g 1 0) 0 with hc | hc
      · specialize hg ⟨1 + .I, by simp⟩
        rw [gl_smul_eq_self_iff_re_eq ha hc] at hg
        simp_all
      · have : 0 < 1 + √(-g.val.det) / |g 1 0| := by simp [add_pos, *]
        specialize hg ⟨⟨-g 1 1 / g 1 0, 1 + √(-g.val.det) / |g 1 0|⟩, this⟩
        simp [gl_smul_eq_self_iff_dist_eq hlt ha hc, Complex.dist_eq_re_im, Real.sqrt_sq this.le]
          at hg
    · have := isElliptic_of_exists_smul_eq_self hgt hgc ⟨.I, hg _⟩
      contrapose! hg
      simp [gl_smul_eq_self_iff_eq_fixedPt hgt this, exists_ne]
  · aesop (add simp GeneralLinearGroup.center_eq_range_scalar)

中文:
定理 对任意_smul_eq_self_iff_mem_center
  条件: {g : GL (有限集 2) 实数}
  证明: by
  constructor
  · intro hg
    by_contra! hgc
    rcases g.det_ne_zero.lt_or_gt with hlt | hgt
    · obtain ⟨ha, hb⟩ := (gl_smul_I_eq_I_iff_of_neg hlt).mp (hg _)
      rw [eq_neg_iff_add_eq_zero]; rw [← Matrix.trace_fin_two] at ha
      rcases eq_or_ne (g 1 0) 0 with hc | hc
      · specialize hg ⟨1 + .I, by simp⟩
        rw [gl_smul_eq_self_iff_re_eq ha hc] at hg
        simp_all
      · have : 0 < 1 + √(-g.val.det) / |g 1 0| := by simp [add_pos, *]
        specialize hg ⟨⟨-g 1 1 / g 1 0, 1 + √(-g.val.det) / |g 1 0|⟩, this⟩
        simp [gl_smul_eq_self_iff_dist_eq hlt ha hc, Complex.dist_eq_re_im, Real.sqrt_sq this.le]
          at hg
    · have := isElliptic_of_exists_smul_eq_self hgt hgc ⟨.I, hg _⟩
      contrapose! hg
      simp [gl_smul_eq_self_iff_eq_fixedPt hgt this, exists_ne]
  · aesop (add simp GeneralLinearGroup.center_eq_range_scalar)

Depends on / 依赖: Matrix, Matrix.trace_fin_two, add_pos, det_ne_zero, eq_neg_iff_add_eq_zero, eq_or_ne, g.det_ne_zero.lt_or_gt, g.val.det, gl_smul_I_eq_I_iff_of_neg, gl_smul_eq_self_iff_dist, gl_smul_eq_self_iff_re_eq, lt_or_gt, specialize, trace_fin_two
-/
theorem forall_smul_eq_self_iff_mem_center {g : GL (Fin 2) Real} :
    (forall z : ℍ, g • z = z) ↔ g in Subgroup.center _ := by
  constructor
  · intro hg
    by_contra! hgc
    rcases g.det_ne_zero.lt_or_gt with hlt | hgt
    · obtain ⟨ha, hb⟩ := (gl_smul_I_eq_I_iff_of_neg hlt).mp (hg _)
      rw [eq_neg_iff_add_eq_zero]; rw [← Matrix.trace_fin_two] at ha
      rcases eq_or_ne (g 1 0) 0 with hc | hc
      · specialize hg ⟨1 + .I, by simp⟩
        rw [gl_smul_eq_self_iff_re_eq ha hc] at hg
        simp_all
      · have : 0 < 1 + √(-g.val.det) / |g 1 0| := by simp [add_pos, *]
        specialize hg ⟨⟨-g 1 1 / g 1 0, 1 + √(-g.val.det) / |g 1 0|⟩, this⟩
        simp [gl_smul_eq_self_iff_dist_eq hlt ha hc, Complex.dist_eq_re_im, Real.sqrt_sq this.le]
          at hg
    · have := isElliptic_of_exists_smul_eq_self hgt hgc ⟨.I, hg _⟩
      contrapose! hg
      simp [gl_smul_eq_self_iff_eq_fixedPt hgt this, exists_ne]
  · aesop (add simp GeneralLinearGroup.center_eq_range_scalar)

end GLAction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FaithfulSMul PGL(2, Real) ℍ
  body: by
  rw [faithfulSMul_iff]
  intro g
  cases g
  simp [forall_smul_eq_self_iff_mem_center]

中文:
实例 :
  签名: 忠实标量乘法 PGL(2, 实数) ℍ
  定义体: by
  rw [faithfulSMul_iff]
  intro g
  cases g
  simp [forall_smul_eq_self_iff_mem_center]

Depends on / 依赖: faithfulSMul_iff, forall_smul_eq_self_iff_mem_center
-/
instance : FaithfulSMul PGL(2, Real) ℍ := by
  rw [faithfulSMul_iff]
  intro g
  cases g
  simp [forall_smul_eq_self_iff_mem_center]

end UpperHalfPlane
