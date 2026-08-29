/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Chu Zheng
-/
module

public import Mathlib.Analysis.Normed.Affine.Simplex
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid

/-!
# Simplices in Euclidean spaces.

This file defines properties of simplices in a Euclidean space.

## Main definitions

* `Affine.Simplex.AcuteAngled`

-/

@[expose] public section


namespace Affine

open EuclideanGeometry
open scoped Real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
variable [NormedAddTorsor V P]

namespace Simplex

variable {m n : Nat}

/--
lemma `Equilateral.angle_eq_pi_div_three` / 引理 `Equilateral.angle_eq_pi_div_three`

English:
lemma Equilateral.angle_eq_pi_div_three
  statement: {s : Simplex Real P n} (he : s.Equilateral)
  proof: by
  rcases he with ⟨r, hr⟩
  rw [angle]; rw [InnerProductGeometry.angle]; rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  refine Real.arccos_eq_of_eq_cos (by linarith [Real.pi_nonneg]) (by linarith [Real.pi_nonneg]) ?_
  simp only [vsub_sub_vsub_cancel_right, ← di

中文:
引理 Equilateral.angle_eq_pi_div_three
  结论: {s : Simplex 实数 P n} (he : s.Equilateral)
  证明: by
  rcases he with ⟨r, hr⟩
  rw [angle]; rw [InnerProductGeometry.angle]; rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  refine Real.arccos_eq_of_eq_cos (by linarith [Real.pi_nonneg]) (by linarith [Real.pi_nonneg]) ?_
  simp only [vsub_sub_vsub_cancel_right, ← di

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle, Real.arccos_eq_of_eq_cos, Real.cos_pi_div_three, Real.pi_nonneg, arccos_eq_of_eq_cos, b.constr_basis, constr_basis, cos_pi_div_three, dist_eq_norm_vsub, dist_eq_zero, independent, injective, pi_nonneg, real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, replace, s.independent.injective, vsub_sub_vsub_cancel_right
-/
lemma Equilateral.angle_eq_pi_div_three {s : Simplex Real P n} (he : s.Equilateral)
    {i₁ i₂ i₃ : Fin (n + 1)} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) :
    ∠ (s.points i₁) (s.points i₂) (s.points i₃) = π / 3 := by
  rcases he with ⟨r, hr⟩
  rw [angle]; rw [InnerProductGeometry.angle]; rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  refine Real.arccos_eq_of_eq_cos (by linarith [Real.pi_nonneg]) (by linarith [Real.pi_nonneg]) ?_
  simp only [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub, hr _ _ h₁₂, hr _ _ h₁₃,
    hr _ _ h₂₃.symm, Real.cos_pi_div_three]
  have hr0 : r != 0 := by
    rintro rfl
    replace hr := hr _ _ h₁₂
    rw [dist_eq_zero] at hr
    exact h₁₂ (s.independent.injective hr)
  field

/--
Definition of `AcuteAngled` / `AcuteAngled` 的定义

English:
definition AcuteAngled
  signature: (s : Simplex Real P n)
  body: forall i₁ i₂ i₃ : Fin (n + 1), i₁ != i₂ -> i₁ != i₃ -> i₂ != i₃ ->
    ∠ (s.points i₁) (s.points i₂) (s.points i₃) < π / 2

中文:
定义 AcuteAngled
  签名: (s : Simplex 实数 P n)
  定义体: forall i₁ i₂ i₃ : Fin (n + 1), i₁ != i₂ -> i₁ != i₃ -> i₂ != i₃ ->
    ∠ (s.points i₁) (s.points i₂) (s.points i₃) < π / 2

Depends on / 依赖: constr_basis, points, s.points
-/
def AcuteAngled (s : Simplex Real P n) : Prop :=
  forall i₁ i₂ i₃ : Fin (n + 1), i₁ != i₂ -> i₁ != i₃ -> i₂ != i₃ ->
    ∠ (s.points i₁) (s.points i₂) (s.points i₃) < π / 2

/--
lemma `acuteAngled_reindex_iff` / 引理 `acuteAngled_reindex_iff`

English:
lemma acuteAngled_reindex_iff
  given: {s : Simplex Real P m} (e : Fin (m + 1) ≃ Fin (n + 1))
  proof: by
  refine ⟨fun h {i₁ i₂ i₃} h₁₂ h₁₃ h₂₃ => ?_, fun h {i₁ i₂ i₃} h₁₂ h₁₃ h₂₃ => ?_⟩
  · convert! h (i₁ := e i₁) (i₂ := e i₂) (i₃ := e i₃) ?_ ?_ ?_ using 1 <;> simp [*]
  · convert! h (i₁ := e.symm i₁) (i₂ := e.symm i₂) (i₃ := e.symm i₃) ?_ ?_ ?_ using 1 <;> simp [*]

中文:
引理 acuteAngled_reindex_iff
  条件: {s : Simplex 实数 P m} (e : Fin (m + 1) ≃ Fin (n + 1))
  证明: by
  refine ⟨fun h {i₁ i₂ i₃} h₁₂ h₁₃ h₂₃ => ?_, fun h {i₁ i₂ i₃} h₁₂ h₁₃ h₂₃ => ?_⟩
  · convert! h (i₁ := e i₁) (i₂ := e i₂) (i₃ := e i₃) ?_ ?_ ?_ using 1 <;> simp [*]
  · convert! h (i₁ := e.symm i₁) (i₂ := e.symm i₂) (i₃ := e.symm i₃) ?_ ?_ ?_ using 1 <;> simp [*]
-/
@[simp] lemma acuteAngled_reindex_iff {s : Simplex Real P m} (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).AcuteAngled ↔ s.AcuteAngled := by
  refine ⟨fun h {i₁ i₂ i₃} h₁₂ h₁₃ h₂₃ => ?_, fun h {i₁ i₂ i₃} h₁₂ h₁₃ h₂₃ => ?_⟩
  · convert! h (i₁ := e i₁) (i₂ := e i₂) (i₃ := e i₃) ?_ ?_ ?_ using 1 <;> simp [*]
  · convert! h (i₁ := e.symm i₁) (i₂ := e.symm i₂) (i₃ := e.symm i₃) ?_ ?_ ?_ using 1 <;> simp [*]

/--
lemma `Equilateral.acuteAngled` / 引理 `Equilateral.acuteAngled`

English:
lemma Equilateral.acuteAngled
  given: {s : Simplex Real P n} (he : s.Equilateral)
  statement: s.AcuteAngled
  proof: by
  intro i₁ i₂ i₃ h₁₂ h₁₃ h₂₃
  rw [he.angle_eq_pi_div_three h₁₂ h₁₃ h₂₃]
  linarith [Real.pi_pos]

中文:
引理 Equilateral.acuteAngled
  条件: {s : Simplex 实数 P n} (he : s.Equilateral)
  结论: s.AcuteAngled
  证明: by
  intro i₁ i₂ i₃ h₁₂ h₁₃ h₂₃
  rw [he.angle_eq_pi_div_three h₁₂ h₁₃ h₂₃]
  linarith [Real.pi_pos]

Depends on / 依赖: Real.pi_pos, angle_eq_pi_div_three, he.angle_eq_pi_div_three, pi_pos
-/
lemma Equilateral.acuteAngled {s : Simplex Real P n} (he : s.Equilateral) : s.AcuteAngled := by
  intro i₁ i₂ i₃ h₁₂ h₁₃ h₂₃
  rw [he.angle_eq_pi_div_three h₁₂ h₁₃ h₂₃]
  linarith [Real.pi_pos]

/--
theorem `dist_point_centroid` / 定理 `dist_point_centroid`

English:
theorem dist_point_centroid
  given: [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1))
  proof: by
  simp_rw [dist_eq_norm_vsub, s.point_vsub_centroid_eq_smul_vsub i, norm_smul, Real.norm_natCast]

中文:
定理 dist_point_centroid
  条件: [NeZero n] (s : Simplex 实数 P n) (i : Fin (n + 1))
  证明: by
  simp_rw [dist_eq_norm_vsub, s.point_vsub_centroid_eq_smul_vsub i, norm_smul, Real.norm_natCast]

Depends on / 依赖: Real.norm_natCast, dist_eq_norm_vsub, norm_natCast, norm_smul, point_vsub_centroid_eq_smul_vsub, s.point_vsub_centroid_eq_smul_vsub, simp_rw
-/
theorem dist_point_centroid [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) :
    dist (s.points i) s.centroid = n * dist s.centroid (s.faceOppositeCentroid i) := by
  simp_rw [dist_eq_norm_vsub, s.point_vsub_centroid_eq_smul_vsub i, norm_smul, Real.norm_natCast]

/--
theorem `dist_point_faceOppositeCentroid` / 定理 `dist_point_faceOppositeCentroid`

English:
theorem dist_point_faceOppositeCentroid
  given: [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1))
  proof: by
  simp_rw [dist_eq_norm_vsub, s.point_vsub_faceOppositeCentroid_eq_smul_vsub i,
    norm_smul]
  norm_cast

中文:
定理 dist_point_faceOppositeCentroid
  条件: [NeZero n] (s : Simplex 实数 P n) (i : Fin (n + 1))
  证明: by
  simp_rw [dist_eq_norm_vsub, s.point_vsub_faceOppositeCentroid_eq_smul_vsub i,
    norm_smul]
  norm_cast

Depends on / 依赖: dist_eq_norm_vsub, norm_smul, point_vsub_faceOppositeCentroid_eq_smul_vsub, s.point_vsub_faceOppositeCentroid_eq_smul_vsub, simp_rw
-/
theorem dist_point_faceOppositeCentroid [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) :
    dist (s.points i) (s.faceOppositeCentroid i) =
    (n + 1) * dist s.centroid (s.faceOppositeCentroid i) := by
  simp_rw [dist_eq_norm_vsub, s.point_vsub_faceOppositeCentroid_eq_smul_vsub i,
    norm_smul]
  norm_cast

end Simplex

namespace Triangle

/--
lemma `acuteAngled_iff_angle_lt` / 引理 `acuteAngled_iff_angle_lt`

English:
lemma acuteAngled_iff_angle_lt
  given: {t : Triangle Real P}
  statement: t.AcuteAngled ↔
  proof: by
  refine ⟨fun h => ⟨h _ _ _ (by decide) (by decide) (by decide),
                   h _ _ _ (by decide) (by decide) (by decide),
                   h _ _ _ (by decide) (by decide) (by decide)⟩,
          fun ⟨h012, h120, h201⟩ => ?_⟩
  have h210 := angle_comm (t.points 0) _ _ ▸ h012
  have h021 :

中文:
引理 acuteAngled_iff_angle_lt
  条件: {t : Triangle 实数 P}
  结论: t.AcuteAngled ↔
  证明: by
  refine ⟨fun h => ⟨h _ _ _ (by decide) (by decide) (by decide),
                   h _ _ _ (by decide) (by decide) (by decide),
                   h _ _ _ (by decide) (by decide) (by decide)⟩,
          fun ⟨h012, h120, h201⟩ => ?_⟩
  have h210 := angle_comm (t.points 0) _ _ ▸ h012
  have h021 :

Depends on / 依赖: angle_comm, fin_cases, points, t.points
-/
lemma acuteAngled_iff_angle_lt {t : Triangle Real P} : t.AcuteAngled ↔
    ∠ (t.points 0) (t.points 1) (t.points 2) < π / 2 ∧
    ∠ (t.points 1) (t.points 2) (t.points 0) < π / 2 ∧
    ∠ (t.points 2) (t.points 0) (t.points 1) < π / 2 := by
  refine ⟨fun h => ⟨h _ _ _ (by decide) (by decide) (by decide),
                   h _ _ _ (by decide) (by decide) (by decide),
                   h _ _ _ (by decide) (by decide) (by decide)⟩,
          fun ⟨h012, h120, h201⟩ => ?_⟩
  have h210 := angle_comm (t.points 0) _ _ ▸ h012
  have h021 := angle_comm (t.points 1) _ _ ▸ h120
  have h102 := angle_comm (t.points 2) _ _ ▸ h201
  intro i₁ i₂ i₃ h₁₂ h₁₃ h₂₃
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases i₃ <;> simp [*] at *

/--
theorem `dist_point_centroid` / 定理 `dist_point_centroid`

English:
theorem dist_point_centroid
  given: (t : Affine.Triangle Real P) (i : Fin 3)
  proof: by
  rw [Affine.Simplex.dist_point_centroid]
  norm_cast

中文:
定理 dist_point_centroid
  条件: (t : Affine.Triangle 实数 P) (i : Fin 3)
  证明: by
  rw [Affine.Simplex.dist_point_centroid]
  norm_cast

Depends on / 依赖: Affine, Affine.Simplex.dist_point_centroid, Simplex, dist_point_centroid
-/
theorem dist_point_centroid (t : Affine.Triangle Real P) (i : Fin 3) :
    dist (t.points i) t.centroid = 2 * dist t.centroid (t.faceOppositeCentroid i) := by
  rw [Affine.Simplex.dist_point_centroid]
  norm_cast

/--
theorem `dist_point_faceOppositeCentroid` / 定理 `dist_point_faceOppositeCentroid`

English:
theorem dist_point_faceOppositeCentroid
  given: (t : Affine.Triangle Real P) (i : Fin 3)
  proof: by
  rw [Affine.Simplex.dist_point_faceOppositeCentroid]
  norm_cast

中文:
定理 dist_point_faceOppositeCentroid
  条件: (t : Affine.Triangle 实数 P) (i : Fin 3)
  证明: by
  rw [Affine.Simplex.dist_point_faceOppositeCentroid]
  norm_cast

Depends on / 依赖: Affine, Affine.Simplex.dist_point_faceOppositeCentroid, Simplex, dist_point_faceOppositeCentroid
-/
theorem dist_point_faceOppositeCentroid (t : Affine.Triangle Real P) (i : Fin 3) :
    dist (t.points i) (t.faceOppositeCentroid i) =
      3 * dist t.centroid (t.faceOppositeCentroid i) := by
  rw [Affine.Simplex.dist_point_faceOppositeCentroid]
  norm_cast

end Triangle

end Affine
