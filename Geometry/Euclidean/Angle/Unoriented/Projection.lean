/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Projection

/-!
# Angles and orthogonal projection.

This file proves lemmas relating to angles involving orthogonal projections.

-/

public section


namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
variable [NormedAddTorsor V P]

open scoped Real

/--
lemma `angle_self_orthogonalProjection` / 引理 `angle_self_orthogonalProjection`

English:
lemma angle_self_orthogonalProjection
  statement: (p : P) {p' : P} {s : AffineSubspace Real P}
  proof: ⟨p', h⟩
    ∠ p (orthogonalProjection s p) p' = π / 2 := by
  have : Nonempty s := ⟨p', h⟩
  rw [angle]; rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  exact Submodule.inner_left_of_mem_orthogonal (K := s.direction)
    (AffineSubspace.vsub_mem_direction h (orthogonalProjection_

中文:
引理 angle_self_orthogonalProjection
  结论: (p : P) {p' : P} {s : 仿射子空间 实数 P}
  证明: ⟨p', h⟩
    ∠ p (orthogonalProjection s p) p' = π / 2 := by
  have : Nonempty s := ⟨p', h⟩
  rw [angle]; rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  exact Submodule.inner_left_of_mem_orthogonal (K := s.direction)
    (AffineSubspace.vsub_mem_direction h (orthogonalProjection_
-/
@[simp] lemma angle_self_orthogonalProjection (p : P) {p' : P} {s : AffineSubspace Real P}
    [s.direction.HasOrthogonalProjection] (h : p' in s) :
    haveI : Nonempty s := ⟨p', h⟩
    ∠ p (orthogonalProjection s p) p' = π / 2 := by
  have : Nonempty s := ⟨p', h⟩
  rw [angle]; rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  exact Submodule.inner_left_of_mem_orthogonal (K := s.direction)
    (AffineSubspace.vsub_mem_direction h (orthogonalProjection_mem _))
    (vsub_orthogonalProjection_mem_direction_orthogonal _ _)

/--
lemma `angle_orthogonalProjection_self` / 引理 `angle_orthogonalProjection_self`

English:
lemma angle_orthogonalProjection_self
  statement: (p : P) {p' : P} {s : AffineSubspace Real P}
  proof: ⟨p', h⟩
    ∠ p' (orthogonalProjection s p) p = π / 2 := by
  rw [angle_comm]; rw [angle_self_orthogonalProjection p h]

中文:
引理 angle_orthogonalProjection_self
  结论: (p : P) {p' : P} {s : 仿射子空间 实数 P}
  证明: ⟨p', h⟩
    ∠ p' (orthogonalProjection s p) p = π / 2 := by
  rw [angle_comm]; rw [angle_self_orthogonalProjection p h]
-/
@[simp] lemma angle_orthogonalProjection_self (p : P) {p' : P} {s : AffineSubspace Real P}
    [s.direction.HasOrthogonalProjection] (h : p' in s) :
    haveI : Nonempty s := ⟨p', h⟩
    ∠ p' (orthogonalProjection s p) p = π / 2 := by
  rw [angle_comm]; rw [angle_self_orthogonalProjection p h]

end EuclideanGeometry
