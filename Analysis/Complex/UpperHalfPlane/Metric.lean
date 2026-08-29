/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Geometry.Euclidean.Inversion.Basic

/-!
# Metric on the upper half-plane

In this file we define a `MetricSpace` structure on the `UpperHalfPlane`. We use hyperbolic
(Poincaré) distance given by
`dist z w = 2 * arsinh (dist (z : ℂ) w / (2 * √(z.im * w.im)))` instead of the induced
Euclidean distance because the hyperbolic distance is invariant under holomorphic automorphisms of
the upper half-plane. However, we ensure that the projection to `TopologicalSpace` is
definitionally equal to the induced topological space structure.

We also prove that a metric ball/closed ball/sphere in Poincaré metric is a Euclidean ball/closed
ball/sphere with another center and radius.

-/

@[expose] public section


noncomputable section

open Filter Metric Real Set Topology
open scoped UpperHalfPlane ComplexConjugate NNReal Topology MatrixGroups

variable {z w : ℍ} {r : Real}

namespace UpperHalfPlane

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Dist ℍ
  body: ⟨fun z w => 2 * arsinh (dist (z : Complex) w / (2 * √(z.im * w.im)))⟩

中文:
实例 :
  签名: Dist ℍ
  定义体: ⟨fun z w => 2 * arsinh (dist (z : Complex) w / (2 * √(z.im * w.im)))⟩

Depends on / 依赖: arsinh, w.im, z.im
-/
instance : Dist ℍ :=
  ⟨fun z w => 2 * arsinh (dist (z : Complex) w / (2 * √(z.im * w.im)))⟩

/--
theorem `dist_eq` / 定理 `dist_eq`

English:
theorem dist_eq
  given: (z w : ℍ)
  statement: dist z w = 2 * arsinh (dist (z : Complex) w / (2 * √(z.im * w.im)))
  proof: rfl

中文:
定理 dist_eq
  条件: (z w : ℍ)
  结论: dist z w = 2 * arsinh (dist (z : Complex) w / (2 * √(z.im * w.im)))
  证明: rfl
-/
theorem dist_eq (z w : ℍ) : dist z w = 2 * arsinh (dist (z : Complex) w / (2 * √(z.im * w.im))) :=
  rfl

/--
theorem `sinh_half_dist` / 定理 `sinh_half_dist`

English:
theorem sinh_half_dist
  given: (z w : ℍ)
  proof: by
  rw [dist_eq]; rw [mul_div_cancel_left₀ (arsinh _) two_ne_zero]; rw [sinh_arsinh]

中文:
定理 sinh_half_dist
  条件: (z w : ℍ)
  证明: by
  rw [dist_eq]; rw [mul_div_cancel_left₀ (arsinh _) two_ne_zero]; rw [sinh_arsinh]

Depends on / 依赖: arsinh, dist_eq, sinh_arsinh, two_ne_zero
-/
theorem sinh_half_dist (z w : ℍ) :
    sinh (dist z w / 2) = dist (z : Complex) w / (2 * √(z.im * w.im)) := by
  rw [dist_eq]; rw [mul_div_cancel_left₀ (arsinh _) two_ne_zero]; rw [sinh_arsinh]

/--
theorem `cosh_half_dist` / 定理 `cosh_half_dist`

English:
theorem cosh_half_dist
  given: (z w : ℍ)
  proof: by
  rw [← sq_eq_sq₀]; rw [cosh_sq']; rw [sinh_half_dist]; rw [div_pow]; rw [div_pow]; rw [one_add_div]; rw [mul_pow]; rw [sq_sqrt]
  · congr 1
    simp only [Complex.dist_eq, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_conj,
      Complex.conj_conj, Complex.mul_re, Complex.conj_re, Complex.

中文:
定理 cosh_half_dist
  条件: (z w : ℍ)
  证明: by
  rw [← sq_eq_sq₀]; rw [cosh_sq']; rw [sinh_half_dist]; rw [div_pow]; rw [div_pow]; rw [one_add_div]; rw [mul_pow]; rw [sq_sqrt]
  · congr 1
    simp only [Complex.dist_eq, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_conj,
      Complex.conj_conj, Complex.mul_re, Complex.conj_re, Complex.

Depends on / 依赖: Complex.conj_conj, Complex.conj_im, Complex.conj_re, Complex.dist_eq, Complex.mul_re, Complex.normSq_conj, Complex.normSq_sub, Complex.sq_norm, all_goals, coe_im, conj_conj, conj_im, conj_re, cosh_sq, dist_eq, div_pow, mul_pow, mul_re, normSq_conj, normSq_sub
-/
theorem cosh_half_dist (z w : ℍ) :
    cosh (dist z w / 2) = dist (z : Complex) (conj (w : Complex)) / (2 * √(z.im * w.im)) := by
  rw [← sq_eq_sq₀]; rw [cosh_sq']; rw [sinh_half_dist]; rw [div_pow]; rw [div_pow]; rw [one_add_div]; rw [mul_pow]; rw [sq_sqrt]
  · congr 1
    simp only [Complex.dist_eq, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_conj,
      Complex.conj_conj, Complex.mul_re, Complex.conj_re, Complex.conj_im, coe_im]
    ring
  all_goals positivity

/--
theorem `tanh_half_dist` / 定理 `tanh_half_dist`

English:
theorem tanh_half_dist
  given: (z w : ℍ)
  proof: by
  rw [tanh_eq_sinh_div_cosh]; rw [sinh_half_dist]; rw [cosh_half_dist]; rw [div_div_div_comm]; rw [div_self]; rw [div_one]
  positivity

中文:
定理 tanh_half_dist
  条件: (z w : ℍ)
  证明: by
  rw [tanh_eq_sinh_div_cosh]; rw [sinh_half_dist]; rw [cosh_half_dist]; rw [div_div_div_comm]; rw [div_self]; rw [div_one]
  positivity

Depends on / 依赖: cosh_half_dist, div_div_div_comm, div_one, div_self, sinh_half_dist, tanh_eq_sinh_div_cosh
-/
theorem tanh_half_dist (z w : ℍ) :
    tanh (dist z w / 2) = dist (z : Complex) w / dist (z : Complex) (conj ↑w) := by
  rw [tanh_eq_sinh_div_cosh]; rw [sinh_half_dist]; rw [cosh_half_dist]; rw [div_div_div_comm]; rw [div_self]; rw [div_one]
  positivity

/--
theorem `exp_half_dist` / 定理 `exp_half_dist`

English:
theorem exp_half_dist
  given: (z w : ℍ)
  proof: by
  rw [← sinh_add_cosh]; rw [sinh_half_dist]; rw [cosh_half_dist]; rw [add_div]

中文:
定理 exp_half_dist
  条件: (z w : ℍ)
  证明: by
  rw [← sinh_add_cosh]; rw [sinh_half_dist]; rw [cosh_half_dist]; rw [add_div]

Depends on / 依赖: add_div, cosh_half_dist, sinh_add_cosh, sinh_half_dist
-/
theorem exp_half_dist (z w : ℍ) :
    exp (dist z w / 2) = (dist (z : Complex) w + dist (z : Complex) (conj ↑w)) / (2 * √(z.im * w.im)) := by
  rw [← sinh_add_cosh]; rw [sinh_half_dist]; rw [cosh_half_dist]; rw [add_div]

/--
theorem `cosh_dist` / 定理 `cosh_dist`

English:
theorem cosh_dist
  given: (z w : ℍ)
  statement: cosh (dist z w) = 1 + dist (z : Complex) w ^ 2 / (2 * z.im * w.im)
  proof: by
  rw [dist_eq]; rw [cosh_two_mul]; rw [cosh_sq']; rw [add_assoc]; rw [← two_mul]; rw [sinh_arsinh]; rw [div_pow]; rw [mul_pow]; rw [sq_sqrt]; rw [sq (2 : Real)]; rw [mul_assoc]; rw [← mul_div_assoc]; rw [mul_assoc]; rw [mul_div_mul_left] <;> positivity

中文:
定理 cosh_dist
  条件: (z w : ℍ)
  结论: cosh (dist z w) = 1 + dist (z : Complex) w ^ 2 / (2 * z.im * w.im)
  证明: by
  rw [dist_eq]; rw [cosh_two_mul]; rw [cosh_sq']; rw [add_assoc]; rw [← two_mul]; rw [sinh_arsinh]; rw [div_pow]; rw [mul_pow]; rw [sq_sqrt]; rw [sq (2 : Real)]; rw [mul_assoc]; rw [← mul_div_assoc]; rw [mul_assoc]; rw [mul_div_mul_left] <;> positivity

Depends on / 依赖: add_assoc, cosh_sq, cosh_two_mul, dist_eq, div_pow, mul_assoc, mul_div_assoc, mul_div_mul_left, mul_pow, sinh_arsinh, sq_sqrt, two_mul
-/
theorem cosh_dist (z w : ℍ) : cosh (dist z w) = 1 + dist (z : Complex) w ^ 2 / (2 * z.im * w.im) := by
  rw [dist_eq]; rw [cosh_two_mul]; rw [cosh_sq']; rw [add_assoc]; rw [← two_mul]; rw [sinh_arsinh]; rw [div_pow]; rw [mul_pow]; rw [sq_sqrt]; rw [sq (2 : Real)]; rw [mul_assoc]; rw [← mul_div_assoc]; rw [mul_assoc]; rw [mul_div_mul_left] <;> positivity

/--
theorem `sinh_half_dist_add_dist` / 定理 `sinh_half_dist_add_dist`

English:
theorem sinh_half_dist_add_dist
  given: (a b c : ℍ)
  statement: sinh ((dist a b + dist b c) / 2) =
  proof: by
  simp only [add_div _ _ (2 : Real), sinh_add, sinh_half_dist, cosh_half_dist, div_mul_div_comm]
  rw [← add_div]; rw [Complex.dist_self_conj]; rw [coe_im]; rw [abs_of_pos b.im_pos]; rw [mul_comm (dist (b : Complex) _)]; rw [dist_comm (b : Complex)]; rw [Complex.dist_conj_comm]; rw [mul_mul_mul_c

中文:
定理 sinh_half_dist_add_dist
  条件: (a b c : ℍ)
  结论: sinh ((dist a b + dist b c) / 2) =
  证明: by
  simp only [add_div _ _ (2 : Real), sinh_add, sinh_half_dist, cosh_half_dist, div_mul_div_comm]
  rw [← add_div]; rw [Complex.dist_self_conj]; rw [coe_im]; rw [abs_of_pos b.im_pos]; rw [mul_comm (dist (b : Complex) _)]; rw [dist_comm (b : Complex)]; rw [Complex.dist_conj_comm]; rw [mul_mul_mul_c

Depends on / 依赖: Complex.dist_conj_comm, Complex.dist_self_conj, a.im, abs_of_pos, add_div, b.im, b.im_pos, coe_im, cosh_half_dist, dist_comm, dist_conj_comm, dist_self_conj, div_mul_div_comm, im_pos, mul_comm, mul_mul_mul_comm, mul_self_sqrt, sinh_add, sinh_half_dist, sqrt_mul
-/
theorem sinh_half_dist_add_dist (a b c : ℍ) : sinh ((dist a b + dist b c) / 2) =
    (dist (a : Complex) b * dist (c : Complex) (conj ↑b) + dist (b : Complex) c * dist (a : Complex) (conj ↑b)) /
      (2 * √(a.im * c.im) * dist (b : Complex) (conj ↑b)) := by
  simp only [add_div _ _ (2 : Real), sinh_add, sinh_half_dist, cosh_half_dist, div_mul_div_comm]
  rw [← add_div]; rw [Complex.dist_self_conj]; rw [coe_im]; rw [abs_of_pos b.im_pos]; rw [mul_comm (dist (b : Complex) _)]; rw [dist_comm (b : Complex)]; rw [Complex.dist_conj_comm]; rw [mul_mul_mul_comm]; rw [mul_mul_mul_comm _ _ _ b.im]
  congr 2
  rw [sqrt_mul]; rw [sqrt_mul]; rw [sqrt_mul]; rw [mul_comm (√a.im)]; rw [mul_mul_mul_comm]; rw [mul_self_sqrt]; rw [mul_comm] <;> exact (im_pos _).le

/--
theorem `dist_comm` / 定理 `dist_comm`

English:
theorem dist_comm
  given: (z w : ℍ)
  statement: dist z w = dist w z
  proof: by
  simp only [dist_eq, dist_comm (z : Complex), mul_comm]

中文:
定理 dist_comm
  条件: (z w : ℍ)
  结论: dist z w = dist w z
  证明: by
  simp only [dist_eq, dist_comm (z : Complex), mul_comm]
-/
protected theorem dist_comm (z w : ℍ) : dist z w = dist w z := by
  simp only [dist_eq, dist_comm (z : Complex), mul_comm]

/--
theorem `dist_le_iff_le_sinh` / 定理 `dist_le_iff_le_sinh`

English:
theorem dist_le_iff_le_sinh
  proof: by
  rw [← div_le_div_iff_of_pos_right (zero_lt_two' Real)]; rw [← sinh_le_sinh]; rw [sinh_half_dist]

中文:
定理 dist_le_iff_le_sinh
  证明: by
  rw [← div_le_div_iff_of_pos_right (zero_lt_two' Real)]; rw [← sinh_le_sinh]; rw [sinh_half_dist]

Depends on / 依赖: div_le_div_iff_of_pos_right, sinh_half_dist, sinh_le_sinh, zero_lt_two
-/
theorem dist_le_iff_le_sinh :
    dist z w <= r ↔ dist (z : Complex) w / (2 * √(z.im * w.im)) <= sinh (r / 2) := by
  rw [← div_le_div_iff_of_pos_right (zero_lt_two' Real)]; rw [← sinh_le_sinh]; rw [sinh_half_dist]

/--
theorem `dist_eq_iff_eq_sinh` / 定理 `dist_eq_iff_eq_sinh`

English:
theorem dist_eq_iff_eq_sinh
  proof: by
  rw [← div_left_inj' (two_ne_zero' Real)]; rw [← sinh_inj]; rw [sinh_half_dist]

中文:
定理 dist_eq_iff_eq_sinh
  证明: by
  rw [← div_left_inj' (two_ne_zero' Real)]; rw [← sinh_inj]; rw [sinh_half_dist]

Depends on / 依赖: div_left_inj, sinh_half_dist, sinh_inj, two_ne_zero
-/
theorem dist_eq_iff_eq_sinh :
    dist z w = r ↔ dist (z : Complex) w / (2 * √(z.im * w.im)) = sinh (r / 2) := by
  rw [← div_left_inj' (two_ne_zero' Real)]; rw [← sinh_inj]; rw [sinh_half_dist]

/--
theorem `dist_eq_iff_eq_sq_sinh` / 定理 `dist_eq_iff_eq_sq_sinh`

English:
theorem dist_eq_iff_eq_sq_sinh
  given: (hr : 0 <= r)
  proof: by
  rw [dist_eq_iff_eq_sinh]; rw [← sq_eq_sq₀]; rw [div_pow]; rw [mul_pow]; rw [sq_sqrt]; rw [mul_assoc]
  · norm_num
  all_goals positivity

中文:
定理 dist_eq_iff_eq_sq_sinh
  条件: (hr : 0 <= r)
  证明: by
  rw [dist_eq_iff_eq_sinh]; rw [← sq_eq_sq₀]; rw [div_pow]; rw [mul_pow]; rw [sq_sqrt]; rw [mul_assoc]
  · norm_num
  all_goals positivity

Depends on / 依赖: all_goals, dist_eq_iff_eq_sinh, div_pow, mul_assoc, mul_pow, sq_sqrt
-/
theorem dist_eq_iff_eq_sq_sinh (hr : 0 <= r) :
    dist z w = r ↔ dist (z : Complex) w ^ 2 / (4 * z.im * w.im) = sinh (r / 2) ^ 2 := by
  rw [dist_eq_iff_eq_sinh]; rw [← sq_eq_sq₀]; rw [div_pow]; rw [mul_pow]; rw [sq_sqrt]; rw [mul_assoc]
  · norm_num
  all_goals positivity

/--
theorem `dist_triangle` / 定理 `dist_triangle`

English:
theorem dist_triangle
  given: (a b c : ℍ)
  statement: dist a c <= dist a b + dist b c
  proof: by
  rw [dist_le_iff_le_sinh]; rw [sinh_half_dist_add_dist]; rw [div_mul_eq_div_div _ _ (dist _ _)]; rw [le_div_iff₀]; rw [div_mul_eq_mul_div]
  · gcongr
    exact EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist (a : Complex) b c (conj (b : Complex))
  · rw [dist_comm, dist_pos, Ne, Complex.conj

中文:
定理 dist_triangle
  条件: (a b c : ℍ)
  结论: dist a c <= dist a b + dist b c
  证明: by
  rw [dist_le_iff_le_sinh]; rw [sinh_half_dist_add_dist]; rw [div_mul_eq_div_div _ _ (dist _ _)]; rw [le_div_iff₀]; rw [div_mul_eq_mul_div]
  · gcongr
    exact EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist (a : Complex) b c (conj (b : Complex))
  · rw [dist_comm, dist_pos, Ne, Complex.conj
-/
protected theorem dist_triangle (a b c : ℍ) : dist a c <= dist a b + dist b c := by
  rw [dist_le_iff_le_sinh]; rw [sinh_half_dist_add_dist]; rw [div_mul_eq_div_div _ _ (dist _ _)]; rw [le_div_iff₀]; rw [div_mul_eq_mul_div]
  · gcongr
    exact EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist (a : Complex) b c (conj (b : Complex))
  · rw [dist_comm, dist_pos, Ne, Complex.conj_eq_iff_im]
    exact b.im_ne_zero

/--
theorem `dist_le_dist_coe_div_sqrt` / 定理 `dist_le_dist_coe_div_sqrt`

English:
theorem dist_le_dist_coe_div_sqrt
  given: (z w : ℍ)
  statement: dist z w <= dist (z : Complex) w / √(z.im * w.im)
  proof: by
  rw [dist_le_iff_le_sinh]; rw [← div_mul_eq_div_div_swap]; rw [self_le_sinh_iff]
  positivity

中文:
定理 dist_le_dist_coe_div_sqrt
  条件: (z w : ℍ)
  结论: dist z w <= dist (z : Complex) w / √(z.im * w.im)
  证明: by
  rw [dist_le_iff_le_sinh]; rw [← div_mul_eq_div_div_swap]; rw [self_le_sinh_iff]
  positivity

Depends on / 依赖: dist_le_iff_le_sinh, div_mul_eq_div_div_swap, self_le_sinh_iff
-/
theorem dist_le_dist_coe_div_sqrt (z w : ℍ) : dist z w <= dist (z : Complex) w / √(z.im * w.im) := by
  rw [dist_le_iff_le_sinh]; rw [← div_mul_eq_div_div_swap]; rw [self_le_sinh_iff]
  positivity

/-- An auxiliary `MetricSpace` instance on the upper half-plane. This instance has bad projection
to `TopologicalSpace`. We replace it later. -/
@[instance_reducible]
/--
Definition of `metricSpaceAux` / `metricSpaceAux` 的定义

English:
definition metricSpaceAux
  signature: : MetricSpace ℍ where
  body: dist
  dist_self z := by rw [dist_eq, dist_self, zero_div, arsinh_zero, mul_zero]
  dist_comm := UpperHalfPlane.dist_comm
  dist_triangle := UpperHalfPlane.dist_triangle
  eq_of_dist_eq_zero {z w} h := by
    simpa [dist_eq, Real.sqrt_eq_zero', (mul_pos z.im_pos w.im_pos).not_ge, Set.ext_iff] using 

中文:
定义 metricSpaceAux
  签名: : MetricSpace ℍ where
  定义体: dist
  dist_self z := by rw [dist_eq, dist_self, zero_div, arsinh_zero, mul_zero]
  dist_comm := UpperHalfPlane.dist_comm
  dist_triangle := UpperHalfPlane.dist_triangle
  eq_of_dist_eq_zero {z w} h := by
    simpa [dist_eq, Real.sqrt_eq_zero', (mul_pos z.im_pos w.im_pos).not_ge, Set.ext_iff] using 
-/
def metricSpaceAux : MetricSpace ℍ where
  dist := dist
  dist_self z := by rw [dist_eq, dist_self, zero_div, arsinh_zero, mul_zero]
  dist_comm := UpperHalfPlane.dist_comm
  dist_triangle := UpperHalfPlane.dist_triangle
  eq_of_dist_eq_zero {z w} h := by
    simpa [dist_eq, Real.sqrt_eq_zero', (mul_pos z.im_pos w.im_pos).not_ge, Set.ext_iff] using h

open Complex

/--
theorem `cosh_dist'` / 定理 `cosh_dist'`

English:
theorem cosh_dist'
  given: (z w : ℍ)
  proof: by
  simp [field, cosh_dist, Complex.dist_eq, Complex.sq_norm, normSq_apply]
  ring

中文:
定理 cosh_dist'
  条件: (z w : ℍ)
  证明: by
  simp [field, cosh_dist, Complex.dist_eq, Complex.sq_norm, normSq_apply]
  ring

Depends on / 依赖: Complex.dist_eq, Complex.sq_norm, cosh_dist, dist_eq, normSq_apply, sq_norm
-/
theorem cosh_dist' (z w : ℍ) :
    Real.cosh (dist z w) = ((z.re - w.re) ^ 2 + z.im ^ 2 + w.im ^ 2) / (2 * z.im * w.im) := by
  simp [field, cosh_dist, Complex.dist_eq, Complex.sq_norm, normSq_apply]
  ring

/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: (z : ℍ) (r : Real)
  body: ⟨⟨z.re, z.im * Real.cosh r⟩, by positivity⟩

@[simp]

中文:
定义 center
  签名: (z : ℍ) (r : 实数)
  定义体: ⟨⟨z.re, z.im * Real.cosh r⟩, by positivity⟩

@[simp]

Depends on / 依赖: Real.cosh, z.im, z.re
-/
def center (z : ℍ) (r : Real) : ℍ :=
  ⟨⟨z.re, z.im * Real.cosh r⟩, by positivity⟩

@[simp]
/--
theorem `center_re` / 定理 `center_re`

English:
theorem center_re
  given: (z r)
  statement: (center z r).re = z.re
  proof: rfl

@[simp]

中文:
定理 center_re
  条件: (z r)
  结论: (center z r).re = z.re
  证明: rfl

@[simp]
-/
theorem center_re (z r) : (center z r).re = z.re :=
  rfl

@[simp]
/--
theorem `center_im` / 定理 `center_im`

English:
theorem center_im
  given: (z r)
  statement: (center z r).im = z.im * Real.cosh r
  proof: rfl

@[simp]

中文:
定理 center_im
  条件: (z r)
  结论: (center z r).im = z.im * 实数.cosh r
  证明: rfl

@[simp]
-/
theorem center_im (z r) : (center z r).im = z.im * Real.cosh r :=
  rfl

@[simp]
/--
theorem `center_zero` / 定理 `center_zero`

English:
theorem center_zero
  given: (z : ℍ)
  statement: center z 0 = z
  proof: by
  apply ext_re_im <;> simp

中文:
定理 center_zero
  条件: (z : ℍ)
  结论: center z 0 = z
  证明: by
  apply ext_re_im <;> simp

Depends on / 依赖: ext_re_im
-/
theorem center_zero (z : ℍ) : center z 0 = z := by
  apply ext_re_im <;> simp

/--
theorem `dist_coe_center_sq` / 定理 `dist_coe_center_sq`

English:
theorem dist_coe_center_sq
  given: (z w : ℍ) (r : Real)
  statement: dist (z : Complex) (w.center r) ^ 2 =
  proof: by
  have H : 2 * z.im * w.im != 0 := by positivity
  simp only [Complex.dist_eq, Complex.sq_norm, normSq_apply, coe_re, coe_im, center_re, center_im,
    cosh_dist', mul_div_cancel₀ _ H, sub_sq z.im, mul_pow, Real.cosh_sq, sub_re, sub_im, mul_sub, ←
    sq]
  ring

中文:
定理 dist_coe_center_sq
  条件: (z w : ℍ) (r : 实数)
  结论: dist (z : Complex) (w.center r) ^ 2 =
  证明: by
  have H : 2 * z.im * w.im != 0 := by positivity
  simp only [Complex.dist_eq, Complex.sq_norm, normSq_apply, coe_re, coe_im, center_re, center_im,
    cosh_dist', mul_div_cancel₀ _ H, sub_sq z.im, mul_pow, Real.cosh_sq, sub_re, sub_im, mul_sub, ←
    sq]
  ring

Depends on / 依赖: Complex.dist_eq, Complex.sq_norm, Real.cosh_sq, center_im, center_re, coe_im, coe_re, cosh_dist, cosh_sq, dist_eq, mul_pow, mul_sub, normSq_apply, sq_norm, sub_im, sub_re, sub_sq, w.im, z.im
-/
theorem dist_coe_center_sq (z w : ℍ) (r : Real) : dist (z : Complex) (w.center r) ^ 2 =
    2 * z.im * w.im * (Real.cosh (dist z w) - Real.cosh r) + (w.im * Real.sinh r) ^ 2 := by
  have H : 2 * z.im * w.im != 0 := by positivity
  simp only [Complex.dist_eq, Complex.sq_norm, normSq_apply, coe_re, coe_im, center_re, center_im,
    cosh_dist', mul_div_cancel₀ _ H, sub_sq z.im, mul_pow, Real.cosh_sq, sub_re, sub_im, mul_sub, ←
    sq]
  ring

/--
theorem `dist_coe_center` / 定理 `dist_coe_center`

English:
theorem dist_coe_center
  given: (z w : ℍ) (r : Real)
  statement: dist (z : Complex) (w.center r) =
  proof: by
  rw [← sqrt_sq dist_nonneg]; rw [dist_coe_center_sq]

中文:
定理 dist_coe_center
  条件: (z w : ℍ) (r : 实数)
  结论: dist (z : Complex) (w.center r) =
  证明: by
  rw [← sqrt_sq dist_nonneg]; rw [dist_coe_center_sq]

Depends on / 依赖: dist_coe_center_sq, dist_nonneg, sqrt_sq
-/
theorem dist_coe_center (z w : ℍ) (r : Real) : dist (z : Complex) (w.center r) =
    √(2 * z.im * w.im * (Real.cosh (dist z w) - Real.cosh r) + (w.im * Real.sinh r) ^ 2) := by
  rw [← sqrt_sq dist_nonneg]; rw [dist_coe_center_sq]

/--
theorem `cmp_dist_eq_cmp_dist_coe_center` / 定理 `cmp_dist_eq_cmp_dist_coe_center`

English:
theorem cmp_dist_eq_cmp_dist_coe_center
  given: (z w : ℍ) (r : Real)
  proof: by
  let := metricSpaceAux
  rcases lt_or_ge r 0 with hr₀ | hr₀
  · trans Ordering.gt
    exacts [(hr₀.trans_le dist_nonneg).cmp_eq_gt,
      ((mul_neg_of_pos_of_neg w.im_pos (sinh_neg_iff.2 hr₀)).trans_le dist_nonneg).cmp_eq_gt.symm]
  have hr₀' : 0 <= w.im * Real.sinh r := by positivity
  have hzw

中文:
定理 cmp_dist_eq_cmp_dist_coe_center
  条件: (z w : ℍ) (r : 实数)
  证明: by
  let := metricSpaceAux
  rcases lt_or_ge r 0 with hr₀ | hr₀
  · trans Ordering.gt
    exacts [(hr₀.trans_le dist_nonneg).cmp_eq_gt,
      ((mul_neg_of_pos_of_neg w.im_pos (sinh_neg_iff.2 hr₀)).trans_le dist_nonneg).cmp_eq_gt.symm]
  have hr₀' : 0 <= w.im * Real.sinh r := by positivity
  have hzw

Depends on / 依赖: Ordering, Ordering.gt, Real.sinh, cmp_eq_gt, cmp_eq_gt.symm, cmp_map_eq, cmp_mul_pos_l, cosh_strictMonoOn, cosh_strictMonoOn.cmp_map_eq, dist_coe_center_sq, dist_nonneg, exacts, im_pos, lt_or_ge, metricSpaceAux, mul_neg_of_pos_of_neg, sinh_neg_iff, trans_le, two_ne_zero, w.im
-/
theorem cmp_dist_eq_cmp_dist_coe_center (z w : ℍ) (r : Real) :
    cmp (dist z w) r = cmp (dist (z : Complex) (w.center r)) (w.im * Real.sinh r) := by
  let := metricSpaceAux
  rcases lt_or_ge r 0 with hr₀ | hr₀
  · trans Ordering.gt
    exacts [(hr₀.trans_le dist_nonneg).cmp_eq_gt,
      ((mul_neg_of_pos_of_neg w.im_pos (sinh_neg_iff.2 hr₀)).trans_le dist_nonneg).cmp_eq_gt.symm]
  have hr₀' : 0 <= w.im * Real.sinh r := by positivity
  have hzw₀ : 0 < 2 * z.im * w.im := by positivity
  simp only [← cosh_strictMonoOn.cmp_map_eq dist_nonneg hr₀,
    ← (pow_left_strictMonoOn₀ (M₀ := Real) two_ne_zero).cmp_map_eq dist_nonneg hr₀',
    dist_coe_center_sq]
  rw [← cmp_mul_pos_left hzw₀]; rw [← cmp_sub_zero]; rw [← mul_sub]; rw [← cmp_add_right]; rw [zero_add]

/--
theorem `dist_eq_iff_dist_coe_center_eq` / 定理 `dist_eq_iff_dist_coe_center_eq`

English:
theorem dist_eq_iff_dist_coe_center_eq
  proof: eq_iff_eq_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)

@[simp]

中文:
定理 dist_eq_iff_dist_coe_center_eq
  证明: eq_iff_eq_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)

@[simp]

Depends on / 依赖: cmp_dist_eq_cmp_dist_coe_center, eq_iff_eq_of_cmp_eq_cmp
-/
theorem dist_eq_iff_dist_coe_center_eq :
    dist z w = r ↔ dist (z : Complex) (w.center r) = w.im * Real.sinh r :=
  eq_iff_eq_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)

@[simp]
/--
theorem `dist_self_center` / 定理 `dist_self_center`

English:
theorem dist_self_center
  given: (z : ℍ) (r : Real)
  proof: by
  rw [dist_of_re_eq (z.center_re r).symm]; rw [dist_comm]; rw [Real.dist_eq]; rw [mul_sub]; rw [mul_one]
  exact abs_of_nonneg (sub_nonneg.2 <| le_mul_of_one_le_right z.im_pos.le (one_le_cosh _))

@[simp]

中文:
定理 dist_self_center
  条件: (z : ℍ) (r : 实数)
  证明: by
  rw [dist_of_re_eq (z.center_re r).symm]; rw [dist_comm]; rw [Real.dist_eq]; rw [mul_sub]; rw [mul_one]
  exact abs_of_nonneg (sub_nonneg.2 <| le_mul_of_one_le_right z.im_pos.le (one_le_cosh _))

@[simp]

Depends on / 依赖: Real.dist_eq, abs_of_nonneg, center_re, dist_comm, dist_eq, dist_of_re_eq, im_pos, le_mul_of_one_le_right, mul_one, mul_sub, one_le_cosh, sub_nonneg, z.center_re, z.im_pos.le
-/
theorem dist_self_center (z : ℍ) (r : Real) :
    dist (z : Complex) (z.center r) = z.im * (Real.cosh r - 1) := by
  rw [dist_of_re_eq (z.center_re r).symm]; rw [dist_comm]; rw [Real.dist_eq]; rw [mul_sub]; rw [mul_one]
  exact abs_of_nonneg (sub_nonneg.2 <| le_mul_of_one_le_right z.im_pos.le (one_le_cosh _))

@[simp]
/--
theorem `dist_center_dist` / 定理 `dist_center_dist`

English:
theorem dist_center_dist
  given: (z w : ℍ)
  proof: dist_eq_iff_dist_coe_center_eq.1 rfl

中文:
定理 dist_center_dist
  条件: (z w : ℍ)
  证明: dist_eq_iff_dist_coe_center_eq.1 rfl

Depends on / 依赖: dist_eq_iff_dist_coe_center_eq
-/
theorem dist_center_dist (z w : ℍ) :
    dist (z : Complex) (w.center (dist z w)) = w.im * Real.sinh (dist z w) :=
  dist_eq_iff_dist_coe_center_eq.1 rfl

/--
theorem `dist_lt_iff_dist_coe_center_lt` / 定理 `dist_lt_iff_dist_coe_center_lt`

English:
theorem dist_lt_iff_dist_coe_center_lt
  proof: lt_iff_lt_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)

中文:
定理 dist_lt_iff_dist_coe_center_lt
  证明: lt_iff_lt_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)

Depends on / 依赖: cmp_dist_eq_cmp_dist_coe_center, lt_iff_lt_of_cmp_eq_cmp
-/
theorem dist_lt_iff_dist_coe_center_lt :
    dist z w < r ↔ dist (z : Complex) (w.center r) < w.im * Real.sinh r :=
  lt_iff_lt_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)

/--
theorem `lt_dist_iff_lt_dist_coe_center` / 定理 `lt_dist_iff_lt_dist_coe_center`

English:
theorem lt_dist_iff_lt_dist_coe_center
  proof: lt_iff_lt_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 <| cmp_dist_eq_cmp_dist_coe_center z w r)

中文:
定理 lt_dist_iff_lt_dist_coe_center
  证明: lt_iff_lt_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 <| cmp_dist_eq_cmp_dist_coe_center z w r)

Depends on / 依赖: cmp_dist_eq_cmp_dist_coe_center, cmp_eq_cmp_symm, lt_iff_lt_of_cmp_eq_cmp
-/
theorem lt_dist_iff_lt_dist_coe_center :
    r < dist z w ↔ w.im * Real.sinh r < dist (z : Complex) (w.center r) :=
  lt_iff_lt_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 <| cmp_dist_eq_cmp_dist_coe_center z w r)

/--
theorem `dist_le_iff_dist_coe_center_le` / 定理 `dist_le_iff_dist_coe_center_le`

English:
theorem dist_le_iff_dist_coe_center_le
  proof: le_iff_le_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)

中文:
定理 dist_le_iff_dist_coe_center_le
  证明: le_iff_le_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)

Depends on / 依赖: cmp_dist_eq_cmp_dist_coe_center, le_iff_le_of_cmp_eq_cmp
-/
theorem dist_le_iff_dist_coe_center_le :
    dist z w <= r ↔ dist (z : Complex) (w.center r) <= w.im * Real.sinh r :=
  le_iff_le_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)

/--
theorem `le_dist_iff_le_dist_coe_center` / 定理 `le_dist_iff_le_dist_coe_center`

English:
theorem le_dist_iff_le_dist_coe_center
  proof: lt_iff_lt_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 <| cmp_dist_eq_cmp_dist_coe_center z w r)

中文:
定理 le_dist_iff_le_dist_coe_center
  证明: lt_iff_lt_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 <| cmp_dist_eq_cmp_dist_coe_center z w r)

Depends on / 依赖: cmp_dist_eq_cmp_dist_coe_center, cmp_eq_cmp_symm, lt_iff_lt_of_cmp_eq_cmp
-/
theorem le_dist_iff_le_dist_coe_center :
    r < dist z w ↔ w.im * Real.sinh r < dist (z : Complex) (w.center r) :=
  lt_iff_lt_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 <| cmp_dist_eq_cmp_dist_coe_center z w r)

/-- For two points on the same vertical line, the distance is equal to the distance between the
logarithms of their imaginary parts. -/
nonrec theorem dist_of_re_eq (h : z.re = w.re) : dist z w = dist (log z.im) (log w.im) := by
  have h₀ : 0 < z.im / w.im := by positivity
  rw [dist_eq_iff_dist_coe_center_eq]; rw [Real.dist_eq]; rw [← abs_sinh]; rw [← log_div z.im_ne_zero w.im_ne_zero]; rw [sinh_log h₀]; rw [dist_of_re_eq]; rw [coe_im]; rw [coe_im]; rw [center_im]; rw [cosh_abs]; rw [cosh_log h₀]; rw [inv_div] <;>
  [skip; exact h]
  nth_rw 4 [← abs_of_pos w.im_pos]
  simp only [← _root_.abs_mul, Real.dist_eq]
  congr 1
  field

/--
theorem `dist_log_im_le` / 定理 `dist_log_im_le`

English:
theorem dist_log_im_le
  given: (z w : ℍ)
  statement: dist (log z.im) (log w.im) <= dist z w
  proof: calc
    dist (log z.im) (log w.im) = dist (mk ⟨0, z.im⟩ z.im_pos) (mk ⟨0, w.im⟩ w.im_pos) :=
Eq.symm dist_of_re_eq rfl
    _ <= dist z w := by
      simp_rw [dist_eq]
      dsimp only [coe_mk, mk_im]
      gcongr
      simpa [sqrt_sq_eq_abs, ← dist_eq_norm] using Complex.abs_im_le_norm (z - w)

中文:
定理 dist_log_im_le
  条件: (z w : ℍ)
  结论: dist (log z.im) (log w.im) <= dist z w
  证明: calc
    dist (log z.im) (log w.im) = dist (mk ⟨0, z.im⟩ z.im_pos) (mk ⟨0, w.im⟩ w.im_pos) :=
Eq.symm dist_of_re_eq rfl
    _ <= dist z w := by
      simp_rw [dist_eq]
      dsimp only [coe_mk, mk_im]
      gcongr
      simpa [sqrt_sq_eq_abs, ← dist_eq_norm] using Complex.abs_im_le_norm (z - w)

Depends on / 依赖: Complex.abs_im_le_norm, Eq.symm, abs_im_le_norm, coe_mk, dist_eq, dist_eq_norm, dist_of_re_eq, im_pos, mk_im, simp_rw, sqrt_sq_eq_abs, w.im, w.im_pos, z.im, z.im_pos
-/
theorem dist_log_im_le (z w : ℍ) : dist (log z.im) (log w.im) <= dist z w :=
  calc
    dist (log z.im) (log w.im) = dist (mk ⟨0, z.im⟩ z.im_pos) (mk ⟨0, w.im⟩ w.im_pos) :=
Eq.symm dist_of_re_eq rfl
    _ <= dist z w := by
      simp_rw [dist_eq]
      dsimp only [coe_mk, mk_im]
      gcongr
      simpa [sqrt_sq_eq_abs, ← dist_eq_norm] using Complex.abs_im_le_norm (z - w)

/--
theorem `im_le_im_mul_exp_dist` / 定理 `im_le_im_mul_exp_dist`

English:
theorem im_le_im_mul_exp_dist
  given: (z w : ℍ)
  statement: z.im <= w.im * Real.exp (dist z w)
  proof: by
  rw [← div_le_iff₀' w.im_pos]; rw [← exp_log z.im_pos]; rw [← exp_log w.im_pos]; rw [← Real.exp_sub]; rw [exp_le_exp]
  exact (le_abs_self _).trans (dist_log_im_le z w)

中文:
定理 im_le_im_mul_exp_dist
  条件: (z w : ℍ)
  结论: z.im <= w.im * 实数.exp (dist z w)
  证明: by
  rw [← div_le_iff₀' w.im_pos]; rw [← exp_log z.im_pos]; rw [← exp_log w.im_pos]; rw [← Real.exp_sub]; rw [exp_le_exp]
  exact (le_abs_self _).trans (dist_log_im_le z w)

Depends on / 依赖: Real.exp_sub, dist_log_im_le, exp_le_exp, exp_log, exp_sub, im_pos, le_abs_self, w.im_pos, z.im_pos
-/
theorem im_le_im_mul_exp_dist (z w : ℍ) : z.im <= w.im * Real.exp (dist z w) := by
  rw [← div_le_iff₀' w.im_pos]; rw [← exp_log z.im_pos]; rw [← exp_log w.im_pos]; rw [← Real.exp_sub]; rw [exp_le_exp]
  exact (le_abs_self _).trans (dist_log_im_le z w)

/--
theorem `im_div_exp_dist_le` / 定理 `im_div_exp_dist_le`

English:
theorem im_div_exp_dist_le
  given: (z w : ℍ)
  statement: z.im / Real.exp (dist z w) <= w.im
  proof: (div_le_iff₀ (exp_pos _)).2 (im_le_im_mul_exp_dist z w)

中文:
定理 im_div_exp_dist_le
  条件: (z w : ℍ)
  结论: z.im / 实数.exp (dist z w) <= w.im
  证明: (div_le_iff₀ (exp_pos _)).2 (im_le_im_mul_exp_dist z w)

Depends on / 依赖: exp_pos, im_le_im_mul_exp_dist
-/
theorem im_div_exp_dist_le (z w : ℍ) : z.im / Real.exp (dist z w) <= w.im :=
  (div_le_iff₀ (exp_pos _)).2 (im_le_im_mul_exp_dist z w)

/--
theorem `dist_coe_le` / 定理 `dist_coe_le`

English:
theorem dist_coe_le
  given: (z w : ℍ)
  statement: dist (z : Complex) w <= w.im * (Real.exp (dist z w) - 1)
  proof: calc
    dist (z : Complex) w <= dist (z : Complex) (w.center (dist z w)) + dist (w : Complex) (w.center (dist z w)) :=
      dist_triangle_right _ _ _
    _ = w.im * (Real.exp (dist z w) - 1) := by
      rw [dist_center_dist]; rw [dist_self_center]; rw [← mul_add]; rw [← add_sub_assoc]; rw [Real.si

中文:
定理 dist_coe_le
  条件: (z w : ℍ)
  结论: dist (z : Complex) w <= w.im * (实数.exp (dist z w) - 1)
  证明: calc
    dist (z : Complex) w <= dist (z : Complex) (w.center (dist z w)) + dist (w : Complex) (w.center (dist z w)) :=
      dist_triangle_right _ _ _
    _ = w.im * (Real.exp (dist z w) - 1) := by
      rw [dist_center_dist]; rw [dist_self_center]; rw [← mul_add]; rw [← add_sub_assoc]; rw [Real.si

Depends on / 依赖: Real.exp, Real.sinh_add_cosh, add_sub_assoc, center, dist_center_dist, dist_self_center, dist_triangle_right, mul_add, sinh_add_cosh, w.center, w.im
-/
theorem dist_coe_le (z w : ℍ) : dist (z : Complex) w <= w.im * (Real.exp (dist z w) - 1) :=
  calc
    dist (z : Complex) w <= dist (z : Complex) (w.center (dist z w)) + dist (w : Complex) (w.center (dist z w)) :=
      dist_triangle_right _ _ _
    _ = w.im * (Real.exp (dist z w) - 1) := by
      rw [dist_center_dist]; rw [dist_self_center]; rw [← mul_add]; rw [← add_sub_assoc]; rw [Real.sinh_add_cosh]

/--
theorem `le_dist_coe` / 定理 `le_dist_coe`

English:
theorem le_dist_coe
  given: (z w : ℍ)
  statement: w.im * (1 - Real.exp (-dist z w)) <= dist (z : Complex) w
  proof: calc
    w.im * (1 - Real.exp (-dist z w)) =
        dist (z : Complex) (w.center (dist z w)) - dist (w : Complex) (w.center (dist z w)) := by
      rw [dist_center_dist]; rw [dist_self_center]; rw [← Real.cosh_sub_sinh]; ring
_ <= dist (z : Complex) w := sub_le_iff_le_add.2 dist_triangle _ _ _

中文:
定理 le_dist_coe
  条件: (z w : ℍ)
  结论: w.im * (1 - 实数.exp (-dist z w)) <= dist (z : Complex) w
  证明: calc
    w.im * (1 - Real.exp (-dist z w)) =
        dist (z : Complex) (w.center (dist z w)) - dist (w : Complex) (w.center (dist z w)) := by
      rw [dist_center_dist]; rw [dist_self_center]; rw [← Real.cosh_sub_sinh]; ring
_ <= dist (z : Complex) w := sub_le_iff_le_add.2 dist_triangle _ _ _

Depends on / 依赖: Real.cosh_sub_sinh, Real.exp, center, cosh_sub_sinh, dist_center_dist, dist_self_center, dist_triangle, sub_le_iff_le_add, w.center, w.im
-/
theorem le_dist_coe (z w : ℍ) : w.im * (1 - Real.exp (-dist z w)) <= dist (z : Complex) w :=
  calc
    w.im * (1 - Real.exp (-dist z w)) =
        dist (z : Complex) (w.center (dist z w)) - dist (w : Complex) (w.center (dist z w)) := by
      rw [dist_center_dist]; rw [dist_self_center]; rw [← Real.cosh_sub_sinh]; ring
_ <= dist (z : Complex) w := sub_le_iff_le_add.2 dist_triangle _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetricSpace ℍ
  body: metricSpaceAux.replaceTopology by
    refine le_antisymm (continuous_id_iff_le.1 ?_) ?_
    · refine (@continuous_iff_continuous_dist ℍ ℍ metricSpaceAux.toPseudoMetricSpace _ _).2 ?_
      have : forall x : ℍ × ℍ, 2 * √(x.1.im * x.2.im) != 0 := fun x => by positivity
      -- `continuity` fails to a

中文:
实例 :
  签名: MetricSpace ℍ
  定义体: metricSpaceAux.replaceTopology by
    refine le_antisymm (continuous_id_iff_le.1 ?_) ?_
    · refine (@continuous_iff_continuous_dist ℍ ℍ metricSpaceAux.toPseudoMetricSpace _ _).2 ?_
      have : forall x : ℍ × ℍ, 2 * √(x.1.im * x.2.im) != 0 := fun x => by positivity
      -- `continuity` fails to a

Depends on / 依赖: continuous_id_iff_le, continuous_iff_continuous_dist, le_antisymm, metricSpaceAux, metricSpaceAux.replaceTopology, metricSpaceAux.toPseudoMetricSpace, replaceTopology, toPseudoMetricSpace
-/
instance : MetricSpace ℍ :=
metricSpaceAux.replaceTopology by
    refine le_antisymm (continuous_id_iff_le.1 ?_) ?_
    · refine (@continuous_iff_continuous_dist ℍ ℍ metricSpaceAux.toPseudoMetricSpace _ _).2 ?_
      have : forall x : ℍ × ℍ, 2 * √(x.1.im * x.2.im) != 0 := fun x => by positivity
      -- `continuity` fails to apply `Continuous.div`
      apply_rules [Continuous.div, Continuous.mul, continuous_const, Continuous.arsinh,
        Continuous.dist, continuous_coe.comp, continuous_fst, continuous_snd,
        Real.continuous_sqrt.comp, continuous_im.comp]
    · let : MetricSpace ℍ := metricSpaceAux
      refine le_of_nhds_le_nhds fun z => ?_
      rw [nhds_induced]
      refine (nhds_basis_ball.le_basis_iff (nhds_basis_ball.comap _)).2 fun R hR => ?_
      have h₁ : 1 < R / im z + 1 := lt_add_of_pos_left _ (div_pos hR z.im_pos)
      have h₀ : 0 < R / im z + 1 := one_pos.trans h₁
      refine ⟨log (R / im z + 1), Real.log_pos h₁, ?_⟩
      refine fun w hw => (dist_coe_le w z).trans_lt ?_
      rwa [← lt_div_iff₀' z.im_pos, sub_lt_iff_lt_add, ← Real.lt_log_iff_exp_lt h₀]

/--
theorem `im_pos_of_dist_center_le` / 定理 `im_pos_of_dist_center_le`

English:
theorem im_pos_of_dist_center_le
  statement: {z : ℍ} {r : Real} {w : Complex}
  proof: calc
    0 < z.im * (Real.cosh r - Real.sinh r) := mul_pos z.im_pos (sub_pos.2 <| sinh_lt_cosh _)
    _ = (z.center r).im - z.im * Real.sinh r := mul_sub _ _ _
    _ <= (z.center r).im - dist (z.center r : Complex) w := sub_le_sub_left (by rwa [dist_comm]) _
_ <= w.im := sub_le_comm.1
      (le_abs_

中文:
定理 im_pos_of_dist_center_le
  结论: {z : ℍ} {r : 实数} {w : Complex}
  证明: calc
    0 < z.im * (Real.cosh r - Real.sinh r) := mul_pos z.im_pos (sub_pos.2 <| sinh_lt_cosh _)
    _ = (z.center r).im - z.im * Real.sinh r := mul_sub _ _ _
    _ <= (z.center r).im - dist (z.center r : Complex) w := sub_le_sub_left (by rwa [dist_comm]) _
_ <= w.im := sub_le_comm.1
      (le_abs_

Depends on / 依赖: Real.cosh, Real.sinh, abs_im_le_norm, center, dist_comm, dist_eq_norm, im_pos, le_abs_self, mul_pos, mul_sub, sinh_lt_cosh, sub_le_comm, sub_le_sub_left, sub_pos, trans_eq, w.im, z.center, z.im, z.im_pos
-/
theorem im_pos_of_dist_center_le {z : ℍ} {r : Real} {w : Complex}
    (h : dist w (center z r) <= z.im * Real.sinh r) : 0 < w.im :=
  calc
    0 < z.im * (Real.cosh r - Real.sinh r) := mul_pos z.im_pos (sub_pos.2 <| sinh_lt_cosh _)
    _ = (z.center r).im - z.im * Real.sinh r := mul_sub _ _ _
    _ <= (z.center r).im - dist (z.center r : Complex) w := sub_le_sub_left (by rwa [dist_comm]) _
_ <= w.im := sub_le_comm.1
      (le_abs_self _).trans ((abs_im_le_norm <| z.center r - w).trans_eq (dist_eq_norm _ _).symm)

/--
theorem `image_coe_closedBall` / 定理 `image_coe_closedBall`

English:
theorem image_coe_closedBall
  given: (z : ℍ) (r : Real)
  proof: by
  ext w; constructor
  · rintro ⟨w, hw, rfl⟩
    exact dist_le_iff_dist_coe_center_le.1 hw
  · intro hw
    lift w to ℍ using im_pos_of_dist_center_le hw
    exact mem_image_of_mem _ (dist_le_iff_dist_coe_center_le.2 hw)

中文:
定理 image_coe_closedBall
  条件: (z : ℍ) (r : 实数)
  证明: by
  ext w; constructor
  · rintro ⟨w, hw, rfl⟩
    exact dist_le_iff_dist_coe_center_le.1 hw
  · intro hw
    lift w to ℍ using im_pos_of_dist_center_le hw
    exact mem_image_of_mem _ (dist_le_iff_dist_coe_center_le.2 hw)

Depends on / 依赖: Real.sinh, center, closedBall, dist_le_iff_dist_coe_center_le, im_pos_of_dist_center_le, mem_image_of_mem, z.center, z.im
-/
theorem image_coe_closedBall (z : ℍ) (r : Real) :
    ((↑) : ℍ -> Complex) '' closedBall (α := ℍ) z r = closedBall ↑(z.center r) (z.im * Real.sinh r) := by
  ext w; constructor
  · rintro ⟨w, hw, rfl⟩
    exact dist_le_iff_dist_coe_center_le.1 hw
  · intro hw
    lift w to ℍ using im_pos_of_dist_center_le hw
    exact mem_image_of_mem _ (dist_le_iff_dist_coe_center_le.2 hw)

/--
theorem `image_coe_ball` / 定理 `image_coe_ball`

English:
theorem image_coe_ball
  given: (z : ℍ) (r : Real)
  proof: by
  ext w; constructor
  · rintro ⟨w, hw, rfl⟩
    exact dist_lt_iff_dist_coe_center_lt.1 hw
  · intro hw
    lift w to ℍ using im_pos_of_dist_center_le (ball_subset_closedBall hw)
    exact mem_image_of_mem _ (dist_lt_iff_dist_coe_center_lt.2 hw)

中文:
定理 image_coe_ball
  条件: (z : ℍ) (r : 实数)
  证明: by
  ext w; constructor
  · rintro ⟨w, hw, rfl⟩
    exact dist_lt_iff_dist_coe_center_lt.1 hw
  · intro hw
    lift w to ℍ using im_pos_of_dist_center_le (ball_subset_closedBall hw)
    exact mem_image_of_mem _ (dist_lt_iff_dist_coe_center_lt.2 hw)

Depends on / 依赖: Real.sinh, ball_subset_closedBall, center, dist_lt_iff_dist_coe_center_lt, im_pos_of_dist_center_le, mem_image_of_mem, z.center, z.im
-/
theorem image_coe_ball (z : ℍ) (r : Real) :
    ((↑) : ℍ -> Complex) '' ball (α := ℍ) z r = ball ↑(z.center r) (z.im * Real.sinh r) := by
  ext w; constructor
  · rintro ⟨w, hw, rfl⟩
    exact dist_lt_iff_dist_coe_center_lt.1 hw
  · intro hw
    lift w to ℍ using im_pos_of_dist_center_le (ball_subset_closedBall hw)
    exact mem_image_of_mem _ (dist_lt_iff_dist_coe_center_lt.2 hw)

/--
theorem `image_coe_sphere` / 定理 `image_coe_sphere`

English:
theorem image_coe_sphere
  given: (z : ℍ) (r : Real)
  proof: by
  ext w; constructor
  · rintro ⟨w, hw, rfl⟩
    exact dist_eq_iff_dist_coe_center_eq.1 hw
  · intro hw
    lift w to ℍ using im_pos_of_dist_center_le (sphere_subset_closedBall hw)
    exact mem_image_of_mem _ (dist_eq_iff_dist_coe_center_eq.2 hw)

中文:
定理 image_coe_sphere
  条件: (z : ℍ) (r : 实数)
  证明: by
  ext w; constructor
  · rintro ⟨w, hw, rfl⟩
    exact dist_eq_iff_dist_coe_center_eq.1 hw
  · intro hw
    lift w to ℍ using im_pos_of_dist_center_le (sphere_subset_closedBall hw)
    exact mem_image_of_mem _ (dist_eq_iff_dist_coe_center_eq.2 hw)

Depends on / 依赖: Real.sinh, center, dist_eq_iff_dist_coe_center_eq, im_pos_of_dist_center_le, mem_image_of_mem, sphere, sphere_subset_closedBall, z.center, z.im
-/
theorem image_coe_sphere (z : ℍ) (r : Real) :
    ((↑) : ℍ -> Complex) '' sphere (α := ℍ) z r = sphere ↑(z.center r) (z.im * Real.sinh r) := by
  ext w; constructor
  · rintro ⟨w, hw, rfl⟩
    exact dist_eq_iff_dist_coe_center_eq.1 hw
  · intro hw
    lift w to ℍ using im_pos_of_dist_center_le (sphere_subset_closedBall hw)
    exact mem_image_of_mem _ (dist_eq_iff_dist_coe_center_eq.2 hw)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ProperSpace ℍ
  body: by
  refine ⟨fun z r => ?_⟩
  rw [isEmbedding_coe.isCompact_iff (f := ((↑) : ℍ -> Complex))]; rw [image_coe_closedBall]
  apply isCompact_closedBall

中文:
实例 :
  签名: 命题erSpace ℍ
  定义体: by
  refine ⟨fun z r => ?_⟩
  rw [isEmbedding_coe.isCompact_iff (f := ((↑) : ℍ -> Complex))]; rw [image_coe_closedBall]
  apply isCompact_closedBall

Depends on / 依赖: image_coe_closedBall, isCompact_closedBall, isCompact_iff, isEmbedding_coe, isEmbedding_coe.isCompact_iff
-/
instance : ProperSpace ℍ := by
  refine ⟨fun z r => ?_⟩
  rw [isEmbedding_coe.isCompact_iff (f := ((↑) : ℍ -> Complex))]; rw [image_coe_closedBall]
  apply isCompact_closedBall

/--
theorem `isometry_vertical_line` / 定理 `isometry_vertical_line`

English:
theorem isometry_vertical_line
  given: (a : Real)
  statement: Isometry fun y => mk ⟨a, exp y⟩ (exp_pos y)
  proof: by
  refine Isometry.of_dist_eq fun y₁ y₂ => ?_
  rw [dist_of_re_eq]
  exacts [congr_arg₂ _ (log_exp _) (log_exp _), rfl]

中文:
定理 isometry_vertical_line
  条件: (a : 实数)
  结论: Isometry fun y => mk ⟨a, exp y⟩ (exp_pos y)
  证明: by
  refine Isometry.of_dist_eq fun y₁ y₂ => ?_
  rw [dist_of_re_eq]
  exacts [congr_arg₂ _ (log_exp _) (log_exp _), rfl]

Depends on / 依赖: Isometry, Isometry.of_dist_eq, dist_of_re_eq, exacts, log_exp, of_dist_eq
-/
theorem isometry_vertical_line (a : Real) : Isometry fun y => mk ⟨a, exp y⟩ (exp_pos y) := by
  refine Isometry.of_dist_eq fun y₁ y₂ => ?_
  rw [dist_of_re_eq]
  exacts [congr_arg₂ _ (log_exp _) (log_exp _), rfl]

/--
theorem `isometry_real_vadd` / 定理 `isometry_real_vadd`

English:
theorem isometry_real_vadd
  given: (a : Real)
  statement: Isometry (a +ᵥ · : ℍ -> ℍ)
  proof: Isometry.of_dist_eq fun y₁ y₂ => by simp only [dist_eq, coe_vadd, vadd_im, dist_add_left]

中文:
定理 isometry_real_vadd
  条件: (a : 实数)
  结论: Isometry (a +ᵥ · : ℍ -> ℍ)
  证明: Isometry.of_dist_eq fun y₁ y₂ => by simp only [dist_eq, coe_vadd, vadd_im, dist_add_left]

Depends on / 依赖: Isometry, Isometry.of_dist_eq, coe_vadd, dist_add_left, dist_eq, of_dist_eq, vadd_im
-/
theorem isometry_real_vadd (a : Real) : Isometry (a +ᵥ · : ℍ -> ℍ) :=
  Isometry.of_dist_eq fun y₁ y₂ => by simp only [dist_eq, coe_vadd, vadd_im, dist_add_left]

/--
theorem `isometry_pos_mul` / 定理 `isometry_pos_mul`

English:
theorem isometry_pos_mul
  given: (a : { x : Real // 0 < x })
  statement: Isometry (a • · : ℍ -> ℍ)
  proof: by
  refine Isometry.of_dist_eq fun y₁ y₂ => ?_
  simp only [dist_eq, coe_pos_real_smul, pos_real_im]; congr 2
  rw [dist_smul₀]; rw [mul_mul_mul_comm]; rw [Real.sqrt_mul (mul_self_nonneg _)]; rw [Real.sqrt_mul_self_eq_abs]; rw [Real.norm_eq_abs]; rw [mul_left_comm]
  exact mul_div_mul_left _ _ (mt 

中文:
定理 isometry_pos_mul
  条件: (a : { x : 实数 // 0 < x })
  结论: Isometry (a • · : ℍ -> ℍ)
  证明: by
  refine Isometry.of_dist_eq fun y₁ y₂ => ?_
  simp only [dist_eq, coe_pos_real_smul, pos_real_im]; congr 2
  rw [dist_smul₀]; rw [mul_mul_mul_comm]; rw [Real.sqrt_mul (mul_self_nonneg _)]; rw [Real.sqrt_mul_self_eq_abs]; rw [Real.norm_eq_abs]; rw [mul_left_comm]
  exact mul_div_mul_left _ _ (mt 

Depends on / 依赖: Isometry, Isometry.of_dist_eq, Real.norm_eq_abs, Real.sqrt_mul, Real.sqrt_mul_self_eq_abs, _root_, _root_.abs_eq_zero, abs_eq_zero, coe_pos_real_smul, dist_eq, mul_div_mul_left, mul_left_comm, mul_mul_mul_comm, mul_self_nonneg, norm_eq_abs, of_dist_eq, pos_real_im, sqrt_mul, sqrt_mul_self_eq_abs
-/
theorem isometry_pos_mul (a : { x : Real // 0 < x }) : Isometry (a • · : ℍ -> ℍ) := by
  refine Isometry.of_dist_eq fun y₁ y₂ => ?_
  simp only [dist_eq, coe_pos_real_smul, pos_real_im]; congr 2
  rw [dist_smul₀]; rw [mul_mul_mul_comm]; rw [Real.sqrt_mul (mul_self_nonneg _)]; rw [Real.sqrt_mul_self_eq_abs]; rw [Real.norm_eq_abs]; rw [mul_left_comm]
  exact mul_div_mul_left _ _ (mt _root_.abs_eq_zero.1 a.2.ne')

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIsometricSMul SL(2, Real) ℍ
  body: ⟨fun g => by
    have h₀ : Isometry (fun z => ModularGroup.S • z : ℍ -> ℍ) :=
      Isometry.of_dist_eq fun y₁ y₂ => by
        have h₁ : 0 <= im y₁ * im y₂ := by positivity
        have h₂ : ‖(y₁ * y₂ : Complex)‖ != 0 := by simp [y₁.ne_zero, y₂.ne_zero]
        simp_rw [modular_S_smul, inv_neg, dis

中文:
实例 :
  签名: IsIsometricSMul SL(2, 实数) ℍ
  定义体: ⟨fun g => by
    have h₀ : Isometry (fun z => ModularGroup.S • z : ℍ -> ℍ) :=
      Isometry.of_dist_eq fun y₁ y₂ => by
        have h₁ : 0 <= im y₁ * im y₂ := by positivity
        have h₂ : ‖(y₁ * y₂ : Complex)‖ != 0 := by simp [y₁.ne_zero, y₂.ne_zero]
        simp_rw [modular_S_smul, inv_neg, dis

Depends on / 依赖: Isometry, Isometry.of_dist_eq, ModularGroup, ModularGroup.S, Real.sqrt_div, coe_im, dist_eq, dist_neg_neg, div_div_div_comm, div_mul_div_comm, inv_im, inv_neg, mk_im, modular_S_smul, mul_div, ne_zero, neg_div, neg_im, neg_neg, normSq_mul
-/
instance : IsIsometricSMul SL(2, Real) ℍ :=
  ⟨fun g => by
    have h₀ : Isometry (fun z => ModularGroup.S • z : ℍ -> ℍ) :=
      Isometry.of_dist_eq fun y₁ y₂ => by
        have h₁ : 0 <= im y₁ * im y₂ := by positivity
        have h₂ : ‖(y₁ * y₂ : Complex)‖ != 0 := by simp [y₁.ne_zero, y₂.ne_zero]
        simp_rw [modular_S_smul, inv_neg, dist_eq, dist_neg_neg,
          dist_inv_inv₀ y₁.ne_zero y₂.ne_zero, mk_im, neg_im, inv_im, coe_im, neg_div, neg_neg,
          div_mul_div_comm, ← normSq_mul, Real.sqrt_div h₁, ← norm_def, mul_div (2 : Real)]
        rw [div_div_div_comm]; rw [← norm_mul]; rw [div_self h₂]; rw [div_one]
    by_cases hc : g 1 0 = 0
    · obtain ⟨u, v, h⟩ := exists_SL2_smul_eq_of_apply_zero_one_eq_zero g hc
      rw [h]
      exact (isometry_real_vadd v).comp (isometry_pos_mul u)
    · obtain ⟨u, v, w, h⟩ := exists_SL2_smul_eq_of_apply_zero_one_ne_zero g hc
      rw [h]
      exact
        (isometry_real_vadd w).comp (h₀.comp <| (isometry_real_vadd v).comp <| isometry_pos_mul u)⟩

end UpperHalfPlane
