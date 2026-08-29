/-
Copyright (c) 2025 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis, Alex Meiburg, Jovan Gerbscheid
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

import Mathlib.Geometry.Euclidean.Triangle

/-!
# The Triangle Inequality for Angles

This file contains the proof that angles obey the triangle inequality.
-/

open InnerProductGeometry
open NormedSpace

open scoped Real NNReal RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]

namespace InnerProductGeometry

section UnitVectorAngles

/--
Definition of `ortho` / `ortho` 的定义

English:
definition ortho
  signature: (x y : V)
  body: y - (Real ∙ x).starProjection y

中文:
定义 ortho
  签名: (x y : V)
  定义体: y - (Real ∙ x).starProjection y

Depends on / 依赖: starProjection
-/
noncomputable def ortho (x y : V) : V := y - (Real ∙ x).starProjection y

/--
lemma `ortho_eq_sub_inner` / 引理 `ortho_eq_sub_inner`

English:
lemma ortho_eq_sub_inner
  given: (x : V) {y : V} (hy : ‖y‖ = 1)
  statement: ortho y x = x - inner Real y x • y
  proof: by
  rw [ortho]; rw [Submodule.starProjection_unit_singleton _ hy]

中文:
引理 ortho_eq_sub_inner
  条件: (x : V) {y : V} (hy : ‖y‖ = 1)
  结论: ortho y x = x - inner 实数 y x • y
  证明: by
  rw [ortho]; rw [Submodule.starProjection_unit_singleton _ hy]

Depends on / 依赖: Submodule, Submodule.starProjection_unit_singleton, starProjection_unit_singleton
-/
lemma ortho_eq_sub_inner (x : V) {y : V} (hy : ‖y‖ = 1) : ortho y x = x - inner Real y x • y := by
  rw [ortho]; rw [Submodule.starProjection_unit_singleton _ hy]

/--
lemma `inner_ortho_nonneg` / 引理 `inner_ortho_nonneg`

English:
lemma inner_ortho_nonneg
  given: {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  statement: 0 <= ⟪x, ortho y x⟫
  proof: by
  rw [ortho_eq_sub_inner x hy]; rw [inner_sub_right]; rw [inner_self_eq_one_of_norm_eq_one hx]; rw [real_inner_smul_right]; rw [real_inner_comm]; rw [sub_nonneg]
  grw [← sq, sq_le_one_iff_abs_le_one, abs_real_inner_le_norm, hx, hy, one_mul]

中文:
引理 inner_ortho_nonneg
  条件: {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  结论: 0 <= ⟪x, ortho y x⟫
  证明: by
  rw [ortho_eq_sub_inner x hy]; rw [inner_sub_right]; rw [inner_self_eq_one_of_norm_eq_one hx]; rw [real_inner_smul_right]; rw [real_inner_comm]; rw [sub_nonneg]
  grw [← sq, sq_le_one_iff_abs_le_one, abs_real_inner_le_norm, hx, hy, one_mul]

Depends on / 依赖: abs_real_inner_le_norm, inner_self_eq_one_of_norm_eq_one, inner_sub_right, one_mul, ortho_eq_sub_inner, real_inner_comm, real_inner_smul_right, sq_le_one_iff_abs_le_one, sub_nonneg
-/
lemma inner_ortho_nonneg {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : 0 <= ⟪x, ortho y x⟫ := by
  rw [ortho_eq_sub_inner x hy]; rw [inner_sub_right]; rw [inner_self_eq_one_of_norm_eq_one hx]; rw [real_inner_smul_right]; rw [real_inner_comm]; rw [sub_nonneg]
  grw [← sq, sq_le_one_iff_abs_le_one, abs_real_inner_le_norm, hx, hy, one_mul]

/--
lemma `inner_normalize_ortho` / 引理 `inner_normalize_ortho`

English:
lemma inner_normalize_ortho
  given: (x y : V)
  statement: ⟪y, normalize (ortho y x)⟫ = 0
  proof: by
  simp only [NormedSpace.normalize, real_inner_smul_right, mul_eq_zero, inv_eq_zero, norm_eq_zero]
  right; rw [ortho, real_inner_comm, Submodule.starProjection_inner_eq_zero]
  exact Submodule.mem_span_singleton_self y

中文:
引理 inner_normalize_ortho
  条件: (x y : V)
  结论: ⟪y, normalize (ortho y x)⟫ = 0
  证明: by
  simp only [NormedSpace.normalize, real_inner_smul_right, mul_eq_zero, inv_eq_zero, norm_eq_zero]
  right; rw [ortho, real_inner_comm, Submodule.starProjection_inner_eq_zero]
  exact Submodule.mem_span_singleton_self y

Depends on / 依赖: NormedSpace, NormedSpace.normalize, Submodule, Submodule.mem_span_singleton_self, Submodule.starProjection_inner_eq_zero, inv_eq_zero, mem_span_singleton_self, mul_eq_zero, norm_eq_zero, normalize, real_inner_comm, real_inner_smul_right, starProjection_inner_eq_zero
-/
lemma inner_normalize_ortho (x y : V) : ⟪y, normalize (ortho y x)⟫ = 0 := by
  simp only [NormedSpace.normalize, real_inner_smul_right, mul_eq_zero, inv_eq_zero, norm_eq_zero]
  right; rw [ortho, real_inner_comm, Submodule.starProjection_inner_eq_zero]
  exact Submodule.mem_span_singleton_self y

variable {x y z : V}
variable (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)

include hx hy
/--
lemma `inner_normalized_ortho_sq_add_inner_sq_eq_one` / 引理 `inner_normalized_ortho_sq_add_inner_sq_eq_one`

English:
lemma inner_normalized_ortho_sq_add_inner_sq_eq_one
  proof: by
  rw [NormedSpace.normalize]; rw [real_inner_smul_right]; rw [ortho_eq_sub_inner _ hy]; rw [inner_sub_right]; rw [real_inner_smul_right]
  by_cases h₁ : x = y
  · simp [*]
  by_cases h₂ : x = -y
  · simp [*]
  rw [real_inner_self_eq_norm_sq]; rw [hx]
  have H1 : ‖x - ⟪y, x⟫ • y‖ != 0 := by
    si

中文:
引理 inner_normalized_ortho_sq_add_inner_sq_eq_one
  证明: by
  rw [NormedSpace.normalize]; rw [real_inner_smul_right]; rw [ortho_eq_sub_inner _ hy]; rw [inner_sub_right]; rw [real_inner_smul_right]
  by_cases h₁ : x = y
  · simp [*]
  by_cases h₂ : x = -y
  · simp [*]
  rw [real_inner_self_eq_norm_sq]; rw [hx]
  have H1 : ‖x - ⟪y, x⟫ • y‖ != 0 := by
    si

Depends on / 依赖: NormedSpace, NormedSpace.normalize, Real.norm_eq_abs, eq_or_eq_neg_of_abs_eq, inner_sub_right, mul_one, ne_eq, norm_eq_abs, norm_eq_zero, norm_smul, normalize, ortho_eq_sub_inner, real_inner_self_eq_norm_sq, real_inner_smul_right, sub_eq_zero
-/
lemma inner_normalized_ortho_sq_add_inner_sq_eq_one :
    ⟪x, normalize (ortho y x)⟫ ^ 2 + ⟪x, y⟫ ^ 2 = 1 := by
  rw [NormedSpace.normalize]; rw [real_inner_smul_right]; rw [ortho_eq_sub_inner _ hy]; rw [inner_sub_right]; rw [real_inner_smul_right]
  by_cases h₁ : x = y
  · simp [*]
  by_cases h₂ : x = -y
  · simp [*]
  rw [real_inner_self_eq_norm_sq]; rw [hx]
  have H1 : ‖x - ⟪y, x⟫ • y‖ != 0 := by
    simp only [ne_eq, norm_eq_zero, sub_eq_zero]
    intro H2
    rw [H2]; rw [norm_smul]; rw [hy]; rw [Real.norm_eq_abs]; rw [mul_one] at hx
    apply eq_or_eq_neg_of_abs_eq at hx
    rcases hx with hx | hx <;> simp [*] at H2
  have H2 : (1 - ⟪y, x⟫ * ⟪x, y⟫) ^ 2 + ‖x - ⟪y, x⟫ • y‖ ^ 2 * ⟪x, y⟫ ^ 2 =
      ‖x - ⟪y, x⟫ • y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]; rw [inner_sub_left]; rw [inner_sub_right]; rw [inner_sub_right]; rw [real_inner_smul_right]; rw [real_inner_smul_left]; rw [real_inner_smul_right]; rw [real_inner_smul_left]; rw [real_inner_comm x y]; rw [real_inner_self_eq_norm_sq]; rw [hx]; rw [real_inner_self_eq_norm_sq]; rw [hy]
    ring
  field_simp; exact H2

/--
lemma `inner_ortho_right_eq_sin_angle` / 引理 `inner_ortho_right_eq_sin_angle`

English:
lemma inner_ortho_right_eq_sin_angle
  statement: ⟪x, normalize (ortho y x)⟫ = Real.sin (angle x y)
  proof: by
  have H : ⟪x, normalize (ortho y x)⟫ ^ 2 = Real.sin (angle x y) ^ 2 := by
    simp [Real.sin_sq, ← inner_eq_cos_angle_of_norm_eq_one hx hy,
      ← inner_normalized_ortho_sq_add_inner_sq_eq_one hx hy]
  rw [sq_eq_sq_iff_abs_eq_abs]; rw [abs_of_nonneg (sin_angle_nonneg x y)] at H
  have H0 : 0 <=

中文:
引理 inner_ortho_right_eq_sin_angle
  结论: ⟪x, normalize (ortho y x)⟫ = 实数.sin (angle x y)
  证明: by
  have H : ⟪x, normalize (ortho y x)⟫ ^ 2 = Real.sin (angle x y) ^ 2 := by
    simp [Real.sin_sq, ← inner_eq_cos_angle_of_norm_eq_one hx hy,
      ← inner_normalized_ortho_sq_add_inner_sq_eq_one hx hy]
  rw [sq_eq_sq_iff_abs_eq_abs]; rw [abs_of_nonneg (sin_angle_nonneg x y)] at H
  have H0 : 0 <=

Depends on / 依赖: Left.mul_nonneg, NormedSpace, NormedSpace.normalize, Real.sin, Real.sin_sq, abs_of_nonneg, inner_eq_cos_angle_of_norm_eq_one, inner_normalized_ortho_sq_add_inner_sq_eq_one, inner_ortho_nonneg, inv_nonneg_of_nonneg, mul_nonneg, norm_nonneg, normalize, real_inner_smul_right, sin_angle_nonneg, sin_sq, sq_eq_sq_iff_abs_eq_abs
-/
lemma inner_ortho_right_eq_sin_angle : ⟪x, normalize (ortho y x)⟫ = Real.sin (angle x y) := by
  have H : ⟪x, normalize (ortho y x)⟫ ^ 2 = Real.sin (angle x y) ^ 2 := by
    simp [Real.sin_sq, ← inner_eq_cos_angle_of_norm_eq_one hx hy,
      ← inner_normalized_ortho_sq_add_inner_sq_eq_one hx hy]
  rw [sq_eq_sq_iff_abs_eq_abs]; rw [abs_of_nonneg (sin_angle_nonneg x y)] at H
  have H0 : 0 <= ⟪x, normalize (ortho y x)⟫ := by
    rw [NormedSpace.normalize]; rw [real_inner_smul_right]
    exact Left.mul_nonneg (inv_nonneg_of_nonneg (norm_nonneg (ortho y x)))
      (inner_ortho_nonneg hx hy)
  simp_all [abs_of_nonneg H0]

/--
lemma `angle_le_angle_add_angle_aux` / 引理 `angle_le_angle_add_angle_aux`

English:
lemma angle_le_angle_add_angle_aux
  proof: by
  rw [← inner_ortho_right_eq_sin_angle hx hy]; rw [← inner_eq_cos_angle_of_norm_eq_one hx hy]; rw [ortho_eq_sub_inner _ hy]
  by_cases hxy : x - ⟪x, y⟫ • y = 0
  · simp [hxy, real_inner_comm, ← sub_eq_zero]
  rw [NormedSpace.normalize]; rw [real_inner_smul_right]; rw [inner_sub_right]; rw [real_i

中文:
引理 angle_le_angle_add_angle_aux
  证明: by
  rw [← inner_ortho_right_eq_sin_angle hx hy]; rw [← inner_eq_cos_angle_of_norm_eq_one hx hy]; rw [ortho_eq_sub_inner _ hy]
  by_cases hxy : x - ⟪x, y⟫ • y = 0
  · simp [hxy, real_inner_comm, ← sub_eq_zero]
  rw [NormedSpace.normalize]; rw [real_inner_smul_right]; rw [inner_sub_right]; rw [real_i

Depends on / 依赖: NormedSpace, NormedSpace.normalize, inner_eq_cos_angle_of_norm_eq_one, inner_ortho_right_eq_sin_angle, inner_sub_right, mul_smul, normalize, one_pow, ortho_eq_sub_inner, real_inner_comm, real_inner_self_eq_norm_sq, real_inner_smul_right, smul_assoc, smul_eq_mul, sub_eq_zero, sub_ne_z
-/
lemma angle_le_angle_add_angle_aux :
    x = Real.cos (angle x y) • y + Real.sin (angle x y) • normalize (ortho y x) := by
  rw [← inner_ortho_right_eq_sin_angle hx hy]; rw [← inner_eq_cos_angle_of_norm_eq_one hx hy]; rw [ortho_eq_sub_inner _ hy]
  by_cases hxy : x - ⟪x, y⟫ • y = 0
  · simp [hxy, real_inner_comm, ← sub_eq_zero]
  rw [NormedSpace.normalize]; rw [real_inner_smul_right]; rw [inner_sub_right]; rw [real_inner_smul_right]; rw [real_inner_self_eq_norm_sq]; rw [hx]; rw [real_inner_comm y]; rw [← sq]; rw [mul_smul]; rw [← smul_assoc]
  simp only [one_pow, smul_eq_mul]
  have H : 1 - ⟪x, y⟫ ^ 2 != 0 := by
    rw [sub_ne_zero]; rw [ne_comm]; rw [sq_ne_one_iff]
    constructor <;> contrapose hxy
    · rw [inner_eq_one_iff_of_norm_eq_one hx hy] at hxy
      simp [hy, hxy]
    · rw [inner_eq_neg_one_iff_of_norm_eq_one hx hy] at hxy
      simp [hy, hxy]
  rw [← smul_assoc]; rw [smul_eq_mul]
  field_simp
  rw [← real_inner_self_eq_norm_sq]
  have H0 : ⟪x - ⟪x, y⟫ • y, x - ⟪x, y⟫ • y⟫ = 1 - ⟪x, y⟫ ^ 2 := by
    rw [inner_sub_left]; rw [inner_sub_right]; rw [inner_sub_right]; rw [inner_self_eq_one_of_norm_eq_one hx]; rw [real_inner_smul_right]; rw [← sq]; rw [real_inner_smul_left]; rw [real_inner_smul_left]; rw [real_inner_smul_right]; rw [inner_self_eq_one_of_norm_eq_one hy]; rw [real_inner_comm y x]
    ring
  rw [real_inner_comm x]; rw [H0]
  simp [H]

include hz in
/--
lemma `angle_le_angle_add_angle_of_norm_eq_one` / 引理 `angle_le_angle_add_angle_of_norm_eq_one`

English:
lemma angle_le_angle_add_angle_of_norm_eq_one
  statement: angle x z <= angle x y + angle y z
  proof: by
  rcases lt_or_ge π (angle x y + angle y z) with H | H
  · linarith [angle_le_pi x z]
  suffices Real.cos (angle x y + angle y z) <= Real.cos (angle x z) by
    have H0 : 0 <= angle x y + angle y z :=
      add_nonneg (angle_nonneg x y) (angle_nonneg y z)
    rwa [Real.strictAntiOn_cos.le_iff_ge 

中文:
引理 angle_le_angle_add_angle_of_norm_eq_one
  结论: angle x z <= angle x y + angle y z
  证明: by
  rcases lt_or_ge π (angle x y + angle y z) with H | H
  · linarith [angle_le_pi x z]
  suffices Real.cos (angle x y + angle y z) <= Real.cos (angle x z) by
    have H0 : 0 <= angle x y + angle y z :=
      add_nonneg (angle_nonneg x y) (angle_nonneg y z)
    rwa [Real.strictAntiOn_cos.le_iff_ge 

Depends on / 依赖: Real.cos, Real.strictAntiOn_cos.le_iff_ge, add_nonneg, angle_le_angle_add_angle_aux, angle_le_pi, angle_nonneg, inner_add_left, inner_add_right, le_iff_ge, lt_or_ge, nth_rw, strictAntiOn_cos
-/
lemma angle_le_angle_add_angle_of_norm_eq_one : angle x z <= angle x y + angle y z := by
  rcases lt_or_ge π (angle x y + angle y z) with H | H
  · linarith [angle_le_pi x z]
  suffices Real.cos (angle x y + angle y z) <= Real.cos (angle x z) by
    have H0 : 0 <= angle x y + angle y z :=
      add_nonneg (angle_nonneg x y) (angle_nonneg y z)
    rwa [Real.strictAntiOn_cos.le_iff_ge ⟨H0, H⟩ ⟨angle_nonneg x z, angle_le_pi x z⟩] at this
  have H1 : ⟪x, z⟫ = ⟪x, z⟫ := rfl
  nth_rw 2 [angle_le_angle_add_angle_aux hx hy, angle_le_angle_add_angle_aux hz hy] at H1
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm y (normalize _), real_inner_self_eq_norm_sq, hy, angle_comm z y,
    inner_normalize_ortho] at H1
  simp only [one_pow, mul_one, mul_zero, add_zero, zero_add] at H1
  rw [mul_comm (Real.cos (angle y z))] at H1
  rw [Real.cos_add]; rw [← inner_eq_cos_angle_of_norm_eq_one hx hz]; rw [H1]
  have H2 : -1 <= ⟪normalize (ortho y x), normalize (ortho y z)⟫ := by
    by_cases H3 : ortho y x = 0
    · simp [*]
    by_cases H4 : ortho y z = 0
    · simp [*]
    exact neg_one_le_real_inner_of_norm_eq_one
      (norm_normalize_eq_one_iff.mpr H3) (norm_normalize_eq_one_iff.mpr H4)
  have := sin_angle_nonneg x y; have := sin_angle_nonneg y z
  grw [← H2]
  apply le_of_eq
  ring

/--
lemma `ortho_ne_zero_of_not_collinear` / 引理 `ortho_ne_zero_of_not_collinear`

English:
lemma ortho_ne_zero_of_not_collinear
  given: (hxy1 : angle x y != 0) (hxy2 : angle x y != π)
  proof: by
  intro h; rw [ortho_eq_sub_inner _ hx, sub_eq_zero] at h
  grind [abs, norm_smul, Real.norm_eq_abs, norm_zero, inner_eq_mul_norm_iff_angle_eq_zero,
    inner_eq_neg_mul_norm_iff_angle_eq_pi]

中文:
引理 ortho_ne_zero_of_not_collinear
  条件: (hxy1 : angle x y != 0) (hxy2 : angle x y != π)
  证明: by
  intro h; rw [ortho_eq_sub_inner _ hx, sub_eq_zero] at h
  grind [abs, norm_smul, Real.norm_eq_abs, norm_zero, inner_eq_mul_norm_iff_angle_eq_zero,
    inner_eq_neg_mul_norm_iff_angle_eq_pi]

Depends on / 依赖: Real.norm_eq_abs, inner_eq_mul_norm_iff_angle_eq_zero, inner_eq_neg_mul_norm_iff_angle_eq_pi, norm_eq_abs, norm_smul, norm_zero, ortho_eq_sub_inner, sub_eq_zero
-/
lemma ortho_ne_zero_of_not_collinear (hxy1 : angle x y != 0) (hxy2 : angle x y != π) :
    ortho x y != 0 := by
  intro h; rw [ortho_eq_sub_inner _ hx, sub_eq_zero] at h
  grind [abs, norm_smul, Real.norm_eq_abs, norm_zero, inner_eq_mul_norm_iff_angle_eq_zero,
    inner_eq_neg_mul_norm_iff_angle_eq_pi]

/--
lemma `eq_of_angle_eq_zero` / 引理 `eq_of_angle_eq_zero`

English:
lemma eq_of_angle_eq_zero
  given: (hxy : angle x y = 0)
  statement: x = y
  proof: by
  grind [eq_of_angle_eq_zero_of_norm_eq]

include hz in

中文:
引理 eq_of_angle_eq_zero
  条件: (hxy : angle x y = 0)
  结论: x = y
  证明: by
  grind [eq_of_angle_eq_zero_of_norm_eq]

include hz in

Depends on / 依赖: eq_of_angle_eq_zero_of_norm_eq
-/
lemma eq_of_angle_eq_zero (hxy : angle x y = 0) : x = y := by
  grind [eq_of_angle_eq_zero_of_norm_eq]

include hz in
/--
lemma `angle_expression_of_angle_eq_angle_sum` / 引理 `angle_expression_of_angle_eq_angle_sum`

English:
lemma angle_expression_of_angle_eq_angle_sum
  proof: by
  intros H H0
  by_cases H1 : angle x z = 0
  · grind [angle_nonneg, Real.sin_zero, zero_smul]
  have Hxz : Real.sin (angle x z) != 0 := by
    grind [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi]
  by_cases H2 : angle x y = 0
  · grind [Real.sin_zero, zero_smul, eq_of_angle_eq_zero]
  by_cases H

中文:
引理 angle_expression_of_angle_eq_angle_sum
  证明: by
  intros H H0
  by_cases H1 : angle x z = 0
  · grind [angle_nonneg, Real.sin_zero, zero_smul]
  have Hxz : Real.sin (angle x z) != 0 := by
    grind [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi]
  by_cases H2 : angle x y = 0
  · grind [Real.sin_zero, zero_smul, eq_of_angle_eq_zero]
  by_cases H

Depends on / 依赖: Real.sin, Real.sin_zero, angle_le_pi, angle_nonneg, eq_of_angle_eq_zero, intros, sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi, sin_zero, smul_right_inj, zero_smul
-/
lemma angle_expression_of_angle_eq_angle_sum :
    angle x z != π -> angle x z = angle x y + angle y z ->
    Real.sin (angle x z) • y = Real.sin (angle y z) • x + Real.sin (angle x y) • z := by
  intros H H0
  by_cases H1 : angle x z = 0
  · grind [angle_nonneg, Real.sin_zero, zero_smul]
  have Hxz : Real.sin (angle x z) != 0 := by
    grind [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi]
  by_cases H2 : angle x y = 0
  · grind [Real.sin_zero, zero_smul, eq_of_angle_eq_zero]
  by_cases H3 : angle y z = 0
  · grind [Real.sin_zero, zero_smul, smul_right_inj, eq_of_angle_eq_zero]
  by_cases H4 : angle x y = π
  · grind [angle_le_pi, angle_nonneg]
  by_cases H5 : angle y z = π
  · grind [angle_le_pi, angle_nonneg]
  have H6 : ⟪x, z⟫ = ⟪x, z⟫ := rfl
  nth_rw 2 [angle_le_angle_add_angle_aux hx hy, angle_le_angle_add_angle_aux hz hy] at H6
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
             real_inner_comm y (normalize _), real_inner_self_eq_norm_sq, hy, angle_comm z y,
             inner_normalize_ortho] at H6
  simp only [one_pow, mul_one, mul_zero, add_zero, zero_add] at H6
  rw [inner_eq_cos_angle_of_norm_eq_one hx hz]; rw [H0]; rw [Real.cos_add] at H6
  ring_nf at H6
  have Hw : Real.sin (angle x y) * Real.sin (angle y z) != 0 := by
    grind [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi]
  have H8 : ⟪normalize (ortho y x), normalize (ortho y z)⟫ = -1 := by
    grind
  have H9 : ortho y x != 0 := by
    grind [ortho_ne_zero_of_not_collinear, angle_comm]
  have H10 : ortho y z != 0 := by
    grind [ortho_ne_zero_of_not_collinear]
  have H11 : ‖normalize (ortho y x)‖ = 1 := norm_normalize_eq_one_iff.mpr H9
  have H12 : ‖normalize (ortho y z)‖ = 1 := norm_normalize_eq_one_iff.mpr H10
  rw [inner_eq_neg_one_iff_of_norm_eq_one H11 H12] at H8
  nth_rw 2 [angle_le_angle_add_angle_aux hx hy]
  nth_rw 3 [angle_le_angle_add_angle_aux hz hy]
  rw [H8]; match_scalars <;> grind [Real.sin_add, angle_comm]

end UnitVectorAngles


/-- **Triangle inequality** for angles between vectors. -/
public theorem angle_le_angle_add_angle (x y z : V) :
    angle x z <= angle x y + angle y z := by
  by_cases hx : x = 0
  · simpa [hx] using angle_nonneg y z
  by_cases hy : y = 0
  · simpa [hy] using angle_le_pi x z
  by_cases hz : z = 0
  · simpa [hz] using angle_nonneg x y
  simpa using angle_le_angle_add_angle_of_norm_eq_one (norm_normalize_eq_one_iff.mpr hx)
    (norm_normalize_eq_one_iff.mpr hy) (norm_normalize_eq_one_iff.mpr hz)

/-- The triangle inequality is an equality if the middle vector is a nonnegative linear combination
of the other two vectors. See `angle_add_angle_eq_pi_of_angle_eq_pi` for the other equality case. -/
public theorem angle_eq_angle_add_add_angle_add_of_mem_span {x y z : V} (hy : y != 0)
    (h_mem : y in Submodule.span Real>=0 {x, z}) : angle x z = angle x y + angle y z := by
  rw [Submodule.mem_span_pair] at h_mem
  obtain ⟨kx, kz, rfl⟩ := h_mem
  rcases eq_zero_or_pos kx with rfl | hkx <;> rcases eq_zero_or_pos kz with rfl | hkz
  · simp at hy
  · simp_all [NNReal.smul_def]
  · simp_all [NNReal.smul_def]
  · rw [angle_comm (_ + _) z]
    by_cases! hz : z != 0
    · simpa [hkx, hkz, NNReal.smul_def] using
        angle_eq_angle_add_add_angle_add (kx • x) (smul_ne_zero hkz.ne' hz)
    · have hx : x != 0 := by simp_all
      rw [angle_comm]; rw [add_comm]; rw [add_comm (kx • x)]
      simpa [hkx, hkz, NNReal.smul_def] using
        angle_eq_angle_add_add_angle_add (kz • z) (smul_ne_zero hkx.ne' hx)

/--
lemma `mem_span_of_linear_combination` / 引理 `mem_span_of_linear_combination`

English:
lemma mem_span_of_linear_combination
  statement: {x y z : V} {kx ky kz : Real>=0} (hy : ky != 0)
  proof: by
  have h₁ : ky • y in Submodule.span Real>=0 {x, z} := by
    rw [Submodule.mem_span_pair]; grind
  rwa [Submodule.smul_mem_iff _ hy] at h₁

中文:
引理 mem_span_of_linear_combination
  结论: {x y z : V} {kx ky kz : 实数>=0} (hy : ky != 0)
  证明: by
  have h₁ : ky • y in Submodule.span Real>=0 {x, z} := by
    rw [Submodule.mem_span_pair]; grind
  rwa [Submodule.smul_mem_iff _ hy] at h₁

Depends on / 依赖: Submodule, Submodule.mem_span_pair, Submodule.smul_mem_iff, Submodule.span, mem_span_pair, smul_mem_iff
-/
lemma mem_span_of_linear_combination {x y z : V} {kx ky kz : Real>=0} (hy : ky != 0)
    (hlincomb : ky • y = kx • x + kz • z) : y in Submodule.span Real>=0 {x, z} := by
  have h₁ : ky • y in Submodule.span Real>=0 {x, z} := by
    rw [Submodule.mem_span_pair]; grind
  rwa [Submodule.smul_mem_iff _ hy] at h₁

/-- The triangle inequality on vectors `x`, `y`, `z` is an equality if and only if
`angle x z = π`, or `y` is a nonnegative linear combination of `x` and `z`. -/
public theorem angle_eq_angle_add_angle_iff {x y z : V} (hy : y != 0) :
    angle x z = angle x y + angle y z ↔ angle x z = π ∨ y in Submodule.span Real>=0 {x, z} := by
  constructor <;> rintro h
  · by_cases hxz₁ : angle x z = π
    · tauto
    right
    by_cases hxz₂ : angle x z = 0
    · have hxy : angle x y = 0 := by grind [angle_nonneg]
      rw [angle_eq_zero_iff] at hxy hxz₂
      obtain ⟨_, ⟨r2, ⟨hr2, rfl⟩⟩⟩ := hxy
      lift r2 to Real>=0 using hr2.le
      exact Submodule.smul_mem _ _ (Submodule.mem_span_of_mem (by simp))
    have h_sin_xz : Real.sin (angle x z) != 0 := by
      grind [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi]
    by_cases hx : x = 0
    · subst x; simp only [angle_zero_left, left_eq_add] at h
      rw [angle_eq_zero_iff] at h
      obtain ⟨_, ⟨r, ⟨hr, rfl⟩⟩⟩ := h
      lift r to Real>=0 using hr.le
      rw [← NNReal.smul_def]; rw [Submodule.span_insert_zero]; rw [Submodule.span_singleton_smul_eq]
      · simp
      norm_cast at hr
      grind [isUnit_iff_ne_zero]
    by_cases hz : z = 0
    · subst z; simp only [angle_zero_right, right_eq_add] at h
      rw [angle_eq_zero_iff] at h
      obtain ⟨_, ⟨r, ⟨hr, rfl⟩⟩⟩ := h
      lift r to Real>=0 using hr.le
      exact Submodule.smul_mem _ _ (Submodule.mem_span_of_mem (by simp))
    have hnneg₁ : 0 <= Real.sin (angle y z) / ‖x‖ := by
      grind [sin_angle_nonneg, norm_nonneg, div_nonneg_iff, mul_nonneg_iff]
    have hnneg₂ : 0 <= Real.sin (angle x y) / ‖z‖ := by
      grind [sin_angle_nonneg, norm_nonneg, div_nonneg_iff, mul_nonneg_iff]
    have hnneg₃ : 0 <= Real.sin (angle x z) / ‖y‖ := by
      grind [sin_angle_nonneg, norm_nonneg, div_nonneg_iff, mul_nonneg_iff]
    have hnonzero : (⟨Real.sin (angle x z) / ‖y‖, hnneg₃⟩ : Real>=0) != 0 := by
      simp; grind
    have h₁ := angle_expression_of_angle_eq_angle_sum (norm_normalize_eq_one_iff.mpr hx)
        (norm_normalize_eq_one_iff.mpr hy) (norm_normalize_eq_one_iff.mpr hz)
    simp only [angle_normalize_right, angle_normalize_left] at h₁
    have h₂ := h₁ hxz₁ h
    have h₃ : (⟨_, hnneg₃⟩ : Real>=0) • y = (⟨_, hnneg₁⟩ : Real>=0) • x + (⟨_, hnneg₂⟩ : Real>=0) • z := by
      simp only [NormedSpace.normalize, ← smul_assoc, smul_eq_mul, Nonneg.mk_smul] at h₂ ⊢
      exact h₂
    exact mem_span_of_linear_combination hnonzero h₃
  · obtain h | h := h
    · grind [angle_add_angle_eq_pi_of_angle_eq_pi, angle_comm]
    · exact angle_eq_angle_add_add_angle_add_of_mem_span hy h

end InnerProductGeometry

namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Triangle inequality** for angles in Euclidean geometry. -/
public theorem angle_le_angle_add_angle (p p₁ p₂ p₃ : P) : ∠ p₁ p p₃ <= ∠ p₁ p p₂ + ∠ p₂ p p₃ :=
  InnerProductGeometry.angle_le_angle_add_angle _ _ _

end EuclideanGeometry
