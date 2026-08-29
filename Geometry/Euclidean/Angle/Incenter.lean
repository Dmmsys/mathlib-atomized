/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Bisector
public import Mathlib.Geometry.Euclidean.Incenter

/-!
# Angles and incenters and excenters.

This file proves lemmas relating incenters and excenters of a simplex to angle bisection.

-/

public section


open EuclideanGeometry Module
open scoped Real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
variable [NormedAddTorsor V P]

namespace Affine

namespace Simplex

variable {n : Nat} [NeZero n] (s : Simplex Real P n)

variable {s} in
/--
lemma `ExcenterExists.angle_excenter_touchpoint_eq` / 引理 `ExcenterExists.angle_excenter_touchpoint_eq`

English:
lemma ExcenterExists.angle_excenter_touchpoint_eq
  statement: {signs : Finset (Fin (n + 1))}
  proof: (dist_orthogonalProjection_eq_iff_angle_eq hp₁ hp₂).1 (h.dist_excenter_eq_dist_excenter i₁ i₂)

中文:
引理 ExcenterExists.angle_excenter_touchpoint_eq
  结论: {signs : Finset (Fin (n + 1))}
  证明: (dist_orthogonalProjection_eq_iff_angle_eq hp₁ hp₂).1 (h.dist_excenter_eq_dist_excenter i₁ i₂)

Depends on / 依赖: dist_excenter_eq_dist_excenter, dist_orthogonalProjection_eq_iff_angle_eq, h.dist_excenter_eq_dist_excenter
-/
lemma ExcenterExists.angle_excenter_touchpoint_eq {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {p : P} {i₁ i₂ : Fin (n + 1)}
    (hp₁ : p in affineSpan Real (Set.range (s.faceOpposite i₁).points))
    (hp₂ : p in affineSpan Real (Set.range (s.faceOpposite i₂).points)) :
    ∠ (s.excenter signs) p (s.touchpoint signs i₁) =
      ∠ (s.excenter signs) p (s.touchpoint signs i₂) :=
  (dist_orthogonalProjection_eq_iff_angle_eq hp₁ hp₂).1 (h.dist_excenter_eq_dist_excenter i₁ i₂)

variable {s} in
/--
lemma `angle_incenter_touchpoint_eq` / 引理 `angle_incenter_touchpoint_eq`

English:
lemma angle_incenter_touchpoint_eq
  statement: {p : P} {i₁ i₂ : Fin (n + 1)}
  proof: s.excenterExists_empty.angle_excenter_touchpoint_eq hp₁ hp₂

中文:
引理 angle_incenter_touchpoint_eq
  结论: {p : P} {i₁ i₂ : Fin (n + 1)}
  证明: s.excenterExists_empty.angle_excenter_touchpoint_eq hp₁ hp₂

Depends on / 依赖: angle_excenter_touchpoint_eq, excenterExists_empty, s.excenterExists_empty.angle_excenter_touchpoint_eq
-/
lemma angle_incenter_touchpoint_eq {p : P} {i₁ i₂ : Fin (n + 1)}
    (hp₁ : p in affineSpan Real (Set.range (s.faceOpposite i₁).points))
    (hp₂ : p in affineSpan Real (Set.range (s.faceOpposite i₂).points)) :
    ∠ s.incenter p (s.touchpoint ∅ i₁) =
      ∠ s.incenter p (s.touchpoint ∅ i₂) :=
  s.excenterExists_empty.angle_excenter_touchpoint_eq hp₁ hp₂

variable {s} in
/--
lemma `exists_excenterExists_and_eq_excenter_of_forall_angle_orthogonalProjectionSpan_eq` / 引理 `exists_excenterExists_and_eq_excenter_of_forall_angle_orthogonalProjectionSpan_eq`

English:
lemma exists_excenterExists_and_eq_excenter_of_forall_angle_orthogonalProjectionSpan_eq
  statement: {p : P}
  proof: by
  rw [← s.exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter hp]
  refine ⟨dist p ((s.faceOpposite i₁).orthogonalProjectionSpan p), ?_⟩
  intro i
  by_cases hi : i = i₁
  · rw [hi]
  obtain ⟨p', hp'₁, hp'₂, ha⟩ := h i hi
  exact ((dist_orthogonalProjection_eq_iff_angle_eq hp'₁ hp'₂).

中文:
引理 exists_excenterExists_and_eq_excenter_of_forall_angle_orthogonalProjectionSpan_eq
  结论: {p : P}
  证明: by
  rw [← s.exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter hp]
  refine ⟨dist p ((s.faceOpposite i₁).orthogonalProjectionSpan p), ?_⟩
  intro i
  by_cases hi : i = i₁
  · rw [hi]
  obtain ⟨p', hp'₁, hp'₂, ha⟩ := h i hi
  exact ((dist_orthogonalProjection_eq_iff_angle_eq hp'₁ hp'₂).

Depends on / 依赖: dist_orthogonalProjection_eq_iff_angle_eq, exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter, faceOpposite, orthogonalProjectionSpan, s.exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter, s.faceOpposite
-/
lemma exists_excenterExists_and_eq_excenter_of_forall_angle_orthogonalProjectionSpan_eq {p : P}
    (hp : p in affineSpan Real (Set.range s.points)) {i₁ : Fin (n + 1)}
    (h : forall i₂, i₂ != i₁ -> exists p' : P, p' in affineSpan Real (Set.range (s.faceOpposite i₁).points) ∧
      p' in affineSpan Real (Set.range (s.faceOpposite i₂).points) ∧
      ∠ p p' ((s.faceOpposite i₁).orthogonalProjectionSpan p) =
        ∠ p p' ((s.faceOpposite i₂).orthogonalProjectionSpan p)) :
    exists signs, s.ExcenterExists signs ∧ p = s.excenter signs := by
  rw [← s.exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter hp]
  refine ⟨dist p ((s.faceOpposite i₁).orthogonalProjectionSpan p), ?_⟩
  intro i
  by_cases hi : i = i₁
  · rw [hi]
  obtain ⟨p', hp'₁, hp'₂, ha⟩ := h i hi
  exact ((dist_orthogonalProjection_eq_iff_angle_eq hp'₁ hp'₂).2 ha).symm

end Simplex

namespace Triangle

open Simplex

variable [hd2 : Fact (finrank Real V = 2)] [Module.Oriented Real V (Fin 2)]
variable (t : Triangle Real P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃)
include h₁₂ h₁₃ h₂₃

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {t} in
/--
lemma `dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq` / 引理 `dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq`

English:
lemma dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq
  given: {p : P}
  proof: by
  have ha : AffineIndependent Real ![t.points i₁, t.points i₂, t.points i₃] := by
    convert!
      t.independent.comp_embedding
        ⟨![i₁, i₂, i₃], by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all⟩
    ext i
    fin_cases i <;> rfl
  rw [orthogonalProjectionSpan

中文:
引理 dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq
  条件: {p : P}
  证明: by
  have ha : AffineIndependent Real ![t.points i₁, t.points i₂, t.points i₃] := by
    convert!
      t.independent.comp_embedding
        ⟨![i₁, i₂, i₃], by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all⟩
    ext i
    fin_cases i <;> rfl
  rw [orthogonalProjectionSpan

Depends on / 依赖: AffineIndependent, Set.ima, comp_embedding, convert, dist_orthogonalProjection_line_eq_iff_two_zsmul_oangle_eq, fin_cases, independent, orthogonalProjectionSpan, points, range_faceOpposite_points, simp_rw, t.independent.comp_embedding, t.points
-/
lemma dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq {p : P} :
    dist p ((t.faceOpposite i₃).orthogonalProjectionSpan p) =
      dist p ((t.faceOpposite i₂).orthogonalProjectionSpan p) ↔
        (2 : Int) • ∡ (t.points i₂) (t.points i₁) p = (2 : Int) • ∡ p (t.points i₁) (t.points i₃) := by
  have ha : AffineIndependent Real ![t.points i₁, t.points i₂, t.points i₃] := by
    convert!
      t.independent.comp_embedding
        ⟨![i₁, i₂, i₃], by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all⟩
    ext i
    fin_cases i <;> rfl
  rw [orthogonalProjectionSpan]; rw [orthogonalProjectionSpan]; rw [← dist_orthogonalProjection_line_eq_iff_two_zsmul_oangle_eq ha]
  simp only [range_faceOpposite_points]
  simp_rw [(by grind : ({i₃}ᶜ : Set (Fin 3)) = {i₁, i₂}),
    (by grind : ({i₂}ᶜ : Set (Fin 3)) = {i₁, i₃}), Set.image_insert_eq, Set.image_singleton]

/--
lemma `two_zsmul_oangle_excenter_eq` / 引理 `two_zsmul_oangle_excenter_eq`

English:
lemma two_zsmul_oangle_excenter_eq
  given: (signs : Finset (Fin 3))
  proof: by
  rw [← dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃]; rw [← touchpoint]; rw [← touchpoint]; rw [(t.excenterExists signs).dist_excenter_eq_dist_excenter]

中文:
引理 two_zsmul_oangle_excenter_eq
  条件: (signs : Finset (Fin 3))
  证明: by
  rw [← dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃]; rw [← touchpoint]; rw [← touchpoint]; rw [(t.excenterExists signs).dist_excenter_eq_dist_excenter]

Depends on / 依赖: dist_excenter_eq_dist_excenter, dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq, excenterExists, t.excenterExists, touchpoint
-/
lemma two_zsmul_oangle_excenter_eq (signs : Finset (Fin 3)) :
    (2 : Int) • ∡ (t.points i₂) (t.points i₁) (t.excenter signs) =
      (2 : Int) • ∡ (t.excenter signs) (t.points i₁) (t.points i₃) := by
  rw [← dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃]; rw [← touchpoint]; rw [← touchpoint]; rw [(t.excenterExists signs).dist_excenter_eq_dist_excenter]

/--
lemma `oangle_incenter_eq` / 引理 `oangle_incenter_eq`

English:
lemma oangle_incenter_eq
  proof: by
  rw [← (t.sbtw_touchpoint_empty h₁₃ h₁₂ h₂₃.symm).oangle_eq_left]; rw [← (t.sbtw_touchpoint_empty h₁₂ h₁₃ h₂₃).oangle_eq_right]
  have hd := t.dist_incenter_eq_dist_incenter i₃ i₂
  simp_rw [touchpoint, orthogonalProjectionSpan] at hd ⊢
  refine oangle_eq_of_dist_orthogonalProjection_eq (mem_aff

中文:
引理 oangle_incenter_eq
  证明: by
  rw [← (t.sbtw_touchpoint_empty h₁₃ h₁₂ h₂₃.symm).oangle_eq_left]; rw [← (t.sbtw_touchpoint_empty h₁₂ h₁₃ h₂₃).oangle_eq_right]
  have hd := t.dist_incenter_eq_dist_incenter i₃ i₂
  simp_rw [touchpoint, orthogonalProjectionSpan] at hd ⊢
  refine oangle_eq_of_dist_orthogonalProjection_eq (mem_aff

Depends on / 依赖: dist_incenter_eq_dist_incenter, mem_affineSpan, oangle_eq_left, oangle_eq_of_dist_orthogonalProjection_eq, oangle_eq_right, orthogonalProjectionSpan, sbtw_touchpoint_empty, simp_rw, t.dist_incenter_eq_dist_incenter, t.sbtw_touchpoint_empty, t.touchpoint_empty_injective.ne, touchpoint, touchpoint_empty_injective
-/
lemma oangle_incenter_eq :
    ∡ (t.points i₂) (t.points i₁) t.incenter = ∡ t.incenter (t.points i₁) (t.points i₃) := by
  rw [← (t.sbtw_touchpoint_empty h₁₃ h₁₂ h₂₃.symm).oangle_eq_left]; rw [← (t.sbtw_touchpoint_empty h₁₂ h₁₃ h₂₃).oangle_eq_right]
  have hd := t.dist_incenter_eq_dist_incenter i₃ i₂
  simp_rw [touchpoint, orthogonalProjectionSpan] at hd ⊢
  refine oangle_eq_of_dist_orthogonalProjection_eq (mem_affineSpan _ ?_) (mem_affineSpan _ ?_)
    (t.touchpoint_empty_injective.ne h₂₃.symm) hd
  · simp
    grind
  · simp
    grind

/--
lemma `oangle_excenter_singleton_eq` / 引理 `oangle_excenter_singleton_eq`

English:
lemma oangle_excenter_singleton_eq
  proof: by
  rw [(t.touchpoint_singleton_sbtw h₁₃ h₁₂ h₂₃.symm).symm.oangle_eq_left]; rw [(t.touchpoint_singleton_sbtw h₁₂ h₁₃ h₂₃).symm.oangle_eq_right]
  have hd := (t.excenterExists_singleton i₁).dist_excenter_eq_dist_excenter i₃ i₂
  simp_rw [touchpoint, orthogonalProjectionSpan] at hd ⊢
  refine oangle

中文:
引理 oangle_excenter_singleton_eq
  证明: by
  rw [(t.touchpoint_singleton_sbtw h₁₃ h₁₂ h₂₃.symm).symm.oangle_eq_left]; rw [(t.touchpoint_singleton_sbtw h₁₂ h₁₃ h₂₃).symm.oangle_eq_right]
  have hd := (t.excenterExists_singleton i₁).dist_excenter_eq_dist_excenter i₃ i₂
  simp_rw [touchpoint, orthogonalProjectionSpan] at hd ⊢
  refine oangle

Depends on / 依赖: dist_excenter_eq_dist_excenter, excenterExists_singleton, mem_affineSpan, oangle_eq_left, oangle_eq_of_dist_orthogonalProjection_eq, oangle_eq_right, orthogonalProjectionSpan, simp_rw, symm.oangle_eq_left, symm.oangle_eq_right, t.excenterExists_singleton, t.touchpoint_singleton_sbtw, touchpoint, touchpoint_injective, touchpoint_injective.ne, touchpoint_singleton_sbtw
-/
lemma oangle_excenter_singleton_eq :
    ∡ (t.points i₂) (t.points i₁) (t.excenter {i₁}) =
      ∡ (t.excenter {i₁}) (t.points i₁) (t.points i₃) := by
  rw [(t.touchpoint_singleton_sbtw h₁₃ h₁₂ h₂₃.symm).symm.oangle_eq_left]; rw [(t.touchpoint_singleton_sbtw h₁₂ h₁₃ h₂₃).symm.oangle_eq_right]
  have hd := (t.excenterExists_singleton i₁).dist_excenter_eq_dist_excenter i₃ i₂
  simp_rw [touchpoint, orthogonalProjectionSpan] at hd ⊢
  refine oangle_eq_of_dist_orthogonalProjection_eq (mem_affineSpan _ ?_) (mem_affineSpan _ ?_)
    ((t.excenterExists_singleton i₁).touchpoint_injective.ne h₂₃.symm) hd
  · simp
    grind
  · simp
    grind

/--
lemma `oangle_excenter_singleton_eq_add_pi` / 引理 `oangle_excenter_singleton_eq_add_pi`

English:
lemma oangle_excenter_singleton_eq_add_pi
  proof: by
  rw [(t.touchpoint_singleton_sbtw h₁₃ h₁₂ h₂₃.symm).symm.oangle_eq_add_pi_left
        ((t.excenterExists_singleton _).excenter_ne_point _)]; rw [← (t.sbtw_touchpoint_singleton h₁₂.symm h₂₃ h₁₃).oangle_eq_right]; rw [add_left_inj]
  have hd := (t.excenterExists_singleton i₁).dist_excenter_eq_dis

中文:
引理 oangle_excenter_singleton_eq_add_pi
  证明: by
  rw [(t.touchpoint_singleton_sbtw h₁₃ h₁₂ h₂₃.symm).symm.oangle_eq_add_pi_left
        ((t.excenterExists_singleton _).excenter_ne_point _)]; rw [← (t.sbtw_touchpoint_singleton h₁₂.symm h₂₃ h₁₃).oangle_eq_right]; rw [add_left_inj]
  have hd := (t.excenterExists_singleton i₁).dist_excenter_eq_dis

Depends on / 依赖: add_left_inj, dist_excenter_eq_dist_excenter, excenterExists_singleton, excenter_ne_point, mem_affineSpan, oangle_eq_add_pi_left, oangle_eq_of_dist_orthogonalProjection_eq, oangle_eq_right, orthogonalProjectionSpan, sbtw_touchpoint_singleton, simp_rw, symm.oangle_eq_add_pi_left, t.excenterExists_singleton, t.sbtw_touchpoint_singleton, t.touchpoint_singleton_sbtw, touchpoint, touchpoint_inj, touchpoint_singleton_sbtw
-/
lemma oangle_excenter_singleton_eq_add_pi :
    ∡ (t.points i₁) (t.points i₂) (t.excenter {i₁}) =
      ∡ (t.excenter {i₁}) (t.points i₂) (t.points i₃) + π := by
  rw [(t.touchpoint_singleton_sbtw h₁₃ h₁₂ h₂₃.symm).symm.oangle_eq_add_pi_left
        ((t.excenterExists_singleton _).excenter_ne_point _)]; rw [← (t.sbtw_touchpoint_singleton h₁₂.symm h₂₃ h₁₃).oangle_eq_right]; rw [add_left_inj]
  have hd := (t.excenterExists_singleton i₁).dist_excenter_eq_dist_excenter i₃ i₁
  simp_rw [touchpoint, orthogonalProjectionSpan] at hd ⊢
  refine oangle_eq_of_dist_orthogonalProjection_eq (mem_affineSpan _ ?_) (mem_affineSpan _ ?_)
    ((t.excenterExists_singleton i₁).touchpoint_injective.ne h₁₃.symm) hd
  · simp
    grind
  · simp
    grind

variable {t} in
/--
lemma `eq_excenter_of_two_zsmul_oangle_eq` / 引理 `eq_excenter_of_two_zsmul_oangle_eq`

English:
lemma eq_excenter_of_two_zsmul_oangle_eq
  statement: {p : P}
  proof: by
  rw [← dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃] at h₁
  rw [← dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq h₂₃ h₁₂.symm h₁₃.symm]
    at h₂
  have hp : p in affineSpan Real (Set.range t.points) := by
    convert! AffineSubspace.m

中文:
引理 eq_excenter_of_two_zsmul_oangle_eq
  结论: {p : P}
  证明: by
  rw [← dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃] at h₁
  rw [← dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq h₂₃ h₁₂.symm h₁₃.symm]
    at h₂
  have hp : p in affineSpan Real (Set.range t.points) := by
    convert! AffineSubspace.m

Depends on / 依赖: AffineSubspace, AffineSubspace.mem_top, Set.range, affineSpan, affineSpan_eq_top_iff_card_eq_finrank_add_one, convert, dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq, faceOpposite, hd2.out, independent, mem_top, orthogonalProjectionSpan, points, t.faceOpposite, t.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one, t.points
-/
lemma eq_excenter_of_two_zsmul_oangle_eq {p : P}
    (h₁ : (2 : Int) • ∡ (t.points i₂) (t.points i₁) p = (2 : Int) • ∡ p (t.points i₁) (t.points i₃))
    (h₂ : (2 : Int) • ∡ (t.points i₃) (t.points i₂) p = (2 : Int) • ∡ p (t.points i₂) (t.points i₁)) :
    exists signs : Finset (Fin 3), p = t.excenter signs := by
  rw [← dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃] at h₁
  rw [← dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq h₂₃ h₁₂.symm h₁₃.symm]
    at h₂
  have hp : p in affineSpan Real (Set.range t.points) := by
    convert! AffineSubspace.mem_top Real V p
    rw [t.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    simp [hd2.out]
  have hr : exists r : Real, forall i, dist p ((t.faceOpposite i).orthogonalProjectionSpan p) = r := by
    refine ⟨dist p ((faceOpposite t i₃).orthogonalProjectionSpan p), ?_⟩
    intro i
    have h : i = i₁ ∨ i = i₂ ∨ i = i₃ := by clear! p t; decide +revert
    rcases h with rfl | rfl | rfl <;> grind
  obtain ⟨signs, -, hp⟩ :=
    (t.exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter hp).1 hr
  exact ⟨signs, hp⟩

variable {t} in
/--
lemma `eq_incenter_or_eq_excenter_singleton_of_oangle_eq` / 引理 `eq_incenter_or_eq_excenter_singleton_of_oangle_eq`

English:
lemma eq_incenter_or_eq_excenter_singleton_of_oangle_eq
  statement: {signs : Finset (Fin 3)}
  proof: by
  have hs := t.excenter_eq_incenter_or_excenter_singleton_of_ne signs h₁₂ h₁₃ h₂₃
  rcases hs with hs | hs | hs | hs
  · exact .inl hs
  · exact .inr hs
  · rw [hs, t.oangle_excenter_singleton_eq_add_pi h₁₂.symm h₂₃ h₁₃] at h
    simp [Real.Angle.pi_ne_zero] at h
  · rw [hs, oangle_rev (t.points 

中文:
引理 eq_incenter_or_eq_excenter_singleton_of_oangle_eq
  结论: {signs : Finset (Fin 3)}
  证明: by
  have hs := t.excenter_eq_incenter_or_excenter_singleton_of_ne signs h₁₂ h₁₃ h₂₃
  rcases hs with hs | hs | hs | hs
  · exact .inl hs
  · exact .inr hs
  · rw [hs, t.oangle_excenter_singleton_eq_add_pi h₁₂.symm h₂₃ h₁₃] at h
    simp [Real.Angle.pi_ne_zero] at h
  · rw [hs, oangle_rev (t.points 

Depends on / 依赖: Real.Angle.pi_ne_zero, excenter_eq_incenter_or_excenter_singleton_of_ne, oangle_excenter_singleton_eq_add_pi, oangle_rev, pi_ne_zero, points, t.excenter_eq_incenter_or_excenter_singleton_of_ne, t.oangle_excenter_singleton_eq_add_pi, t.points
-/
lemma eq_incenter_or_eq_excenter_singleton_of_oangle_eq {signs : Finset (Fin 3)}
    (h : ∡ (t.points i₂) (t.points i₁) (t.excenter signs) =
      ∡ (t.excenter signs) (t.points i₁) (t.points i₃)) :
    t.excenter signs = t.incenter ∨ t.excenter signs = t.excenter {i₁} := by
  have hs := t.excenter_eq_incenter_or_excenter_singleton_of_ne signs h₁₂ h₁₃ h₂₃
  rcases hs with hs | hs | hs | hs
  · exact .inl hs
  · exact .inr hs
  · rw [hs, t.oangle_excenter_singleton_eq_add_pi h₁₂.symm h₂₃ h₁₃] at h
    simp [Real.Angle.pi_ne_zero] at h
  · rw [hs, oangle_rev (t.points i₃), t.oangle_excenter_singleton_eq_add_pi h₁₃.symm h₂₃.symm h₁₂,
      oangle_rev] at h
    simp [Real.Angle.pi_ne_zero] at h

variable {t} in
/--
lemma `eq_excenter_singleton_of_oangle_eq_add_pi` / 引理 `eq_excenter_singleton_of_oangle_eq_add_pi`

English:
lemma eq_excenter_singleton_of_oangle_eq_add_pi
  statement: {signs : Finset (Fin 3)}
  proof: by
  have hs := t.excenter_eq_incenter_or_excenter_singleton_of_ne signs h₁₂ h₁₃ h₂₃
  rcases hs with hs | hs | hs | hs
  · rw [hs, t.oangle_incenter_eq h₁₂ h₁₃ h₂₃] at h
    simp [Real.Angle.pi_ne_zero] at h
  · rw [hs, t.oangle_excenter_singleton_eq h₁₂ h₁₃ h₂₃] at h
    simp [Real.Angle.pi_ne_zer

中文:
引理 eq_excenter_singleton_of_oangle_eq_add_pi
  结论: {signs : Finset (Fin 3)}
  证明: by
  have hs := t.excenter_eq_incenter_or_excenter_singleton_of_ne signs h₁₂ h₁₃ h₂₃
  rcases hs with hs | hs | hs | hs
  · rw [hs, t.oangle_incenter_eq h₁₂ h₁₃ h₂₃] at h
    simp [Real.Angle.pi_ne_zero] at h
  · rw [hs, t.oangle_excenter_singleton_eq h₁₂ h₁₃ h₂₃] at h
    simp [Real.Angle.pi_ne_zer

Depends on / 依赖: Real.Angle.pi_ne_zero, excenter_eq_incenter_or_excenter_singleton_of_ne, oangle_excenter_singleton_eq, oangle_incenter_eq, pi_ne_zero, t.excenter_eq_incenter_or_excenter_singleton_of_ne, t.oangle_excenter_singleton_eq, t.oangle_incenter_eq
-/
lemma eq_excenter_singleton_of_oangle_eq_add_pi {signs : Finset (Fin 3)}
    (h : ∡ (t.points i₂) (t.points i₁) (t.excenter signs) =
      ∡ (t.excenter signs) (t.points i₁) (t.points i₃) + π) :
    t.excenter signs = t.excenter {i₂} ∨ t.excenter signs = t.excenter {i₃} := by
  have hs := t.excenter_eq_incenter_or_excenter_singleton_of_ne signs h₁₂ h₁₃ h₂₃
  rcases hs with hs | hs | hs | hs
  · rw [hs, t.oangle_incenter_eq h₁₂ h₁₃ h₂₃] at h
    simp [Real.Angle.pi_ne_zero] at h
  · rw [hs, t.oangle_excenter_singleton_eq h₁₂ h₁₃ h₂₃] at h
    simp [Real.Angle.pi_ne_zero] at h
  · exact .inl hs
  · exact .inr hs

variable {t} in
/--
lemma `eq_incenter_of_oangle_eq` / 引理 `eq_incenter_of_oangle_eq`

English:
lemma eq_incenter_of_oangle_eq
  statement: {p : P}
  proof: by
  obtain ⟨signs, rfl⟩ := t.eq_excenter_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ (by rw [h₁]) (by rw [h₂])
  have h₁' := t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq h₁₂ h₁₃ h₂₃ h₁
  have h₂' := t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq h₂₃ h₁₂.symm h₁₃.symm h₂
  rcases h₁' with h₁' | h

中文:
引理 eq_incenter_of_oangle_eq
  结论: {p : P}
  证明: by
  obtain ⟨signs, rfl⟩ := t.eq_excenter_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ (by rw [h₁]) (by rw [h₂])
  have h₁' := t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq h₁₂ h₁₃ h₂₃ h₁
  have h₂' := t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq h₂₃ h₁₂.symm h₁₃.symm h₂
  rcases h₁' with h₁' | h

Depends on / 依赖: eq_excenter_of_two_zsmul_oangle_eq, eq_incenter_or_eq_excenter_singleton_of_oangle_eq, excenter_singleton_injective, t.eq_excenter_of_two_zsmul_oangle_eq, t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq, t.excenter_singleton_injective.ne
-/
lemma eq_incenter_of_oangle_eq {p : P}
    (h₁ : ∡ (t.points i₂) (t.points i₁) p = ∡ p (t.points i₁) (t.points i₃))
    (h₂ : ∡ (t.points i₃) (t.points i₂) p = ∡ p (t.points i₂) (t.points i₁)) :
    p = t.incenter := by
  obtain ⟨signs, rfl⟩ := t.eq_excenter_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ (by rw [h₁]) (by rw [h₂])
  have h₁' := t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq h₁₂ h₁₃ h₂₃ h₁
  have h₂' := t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq h₂₃ h₁₂.symm h₁₃.symm h₂
  rcases h₁' with h₁' | h₁'
  · exact h₁'
  rcases h₂' with h₂' | h₂'
  · exact h₂'
  rw [h₁'] at h₂'
  exfalso
  exact t.excenter_singleton_injective.ne h₁₂ h₂'

variable {t} in
/--
lemma `eq_excenter_singleton_of_oangle_eq_of_oangle_eq_add_pi` / 引理 `eq_excenter_singleton_of_oangle_eq_of_oangle_eq_add_pi`

English:
lemma eq_excenter_singleton_of_oangle_eq_of_oangle_eq_add_pi
  statement: {p : P}
  proof: by
  obtain ⟨signs, rfl⟩ := t.eq_excenter_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ (by rw [h₁])
    (by rw [h₂]; simp)
  have h₁' := t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq h₁₂ h₁₃ h₂₃ h₁
  have h₂' := t.eq_excenter_singleton_of_oangle_eq_add_pi h₂₃ h₁₂.symm h₁₃.symm h₂
  rcases h₁' with h₁' |

中文:
引理 eq_excenter_singleton_of_oangle_eq_of_oangle_eq_add_pi
  结论: {p : P}
  证明: by
  obtain ⟨signs, rfl⟩ := t.eq_excenter_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ (by rw [h₁])
    (by rw [h₂]; simp)
  have h₁' := t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq h₁₂ h₁₃ h₂₃ h₁
  have h₂' := t.eq_excenter_singleton_of_oangle_eq_add_pi h₂₃ h₁₂.symm h₁₃.symm h₂
  rcases h₁' with h₁' |

Depends on / 依赖: eq_excenter_of_two_zsmul_oangle_eq, eq_excenter_singleton_of_oangle_eq_add_pi, eq_incenter_or_eq_excenter_singleton_of_oangle_eq, excenter_singleton_ne_incenter, t.eq_excenter_of_two_zsmul_oangle_eq, t.eq_excenter_singleton_of_oangle_eq_add_pi, t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq, t.excenter_singleton_ne_incenter
-/
lemma eq_excenter_singleton_of_oangle_eq_of_oangle_eq_add_pi {p : P}
    (h₁ : ∡ (t.points i₂) (t.points i₁) p = ∡ p (t.points i₁) (t.points i₃))
    (h₂ : ∡ (t.points i₃) (t.points i₂) p = ∡ p (t.points i₂) (t.points i₁) + π) :
    p = t.excenter {i₁} := by
  obtain ⟨signs, rfl⟩ := t.eq_excenter_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ (by rw [h₁])
    (by rw [h₂]; simp)
  have h₁' := t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq h₁₂ h₁₃ h₂₃ h₁
  have h₂' := t.eq_excenter_singleton_of_oangle_eq_add_pi h₂₃ h₁₂.symm h₁₃.symm h₂
  rcases h₁' with h₁' | h₁'
  · rcases h₂' with h₂' | h₂'
    · rw [h₁'] at h₂'
      exfalso
      exact (t.excenter_singleton_ne_incenter _).symm h₂'
    · exact h₂'
  · exact h₁'

variable {t} in
/--
lemma `eq_excenter_singleton_of_oangle_eq_add_pi_of_oangle_eq_add_pi` / 引理 `eq_excenter_singleton_of_oangle_eq_add_pi_of_oangle_eq_add_pi`

English:
lemma eq_excenter_singleton_of_oangle_eq_add_pi_of_oangle_eq_add_pi
  statement: {p : P}
  proof: by
  obtain ⟨signs, rfl⟩ := t.eq_excenter_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ (by rw [h₁]; simp)
    (by rw [h₂]; simp)
  have h₁' := t.eq_excenter_singleton_of_oangle_eq_add_pi h₁₂ h₁₃ h₂₃ h₁
  have h₂' := t.eq_excenter_singleton_of_oangle_eq_add_pi h₂₃ h₁₂.symm h₁₃.symm h₂
  rcases h₁' with h₁' | h

中文:
引理 eq_excenter_singleton_of_oangle_eq_add_pi_of_oangle_eq_add_pi
  结论: {p : P}
  证明: by
  obtain ⟨signs, rfl⟩ := t.eq_excenter_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ (by rw [h₁]; simp)
    (by rw [h₂]; simp)
  have h₁' := t.eq_excenter_singleton_of_oangle_eq_add_pi h₁₂ h₁₃ h₂₃ h₁
  have h₂' := t.eq_excenter_singleton_of_oangle_eq_add_pi h₂₃ h₁₂.symm h₁₃.symm h₂
  rcases h₁' with h₁' | h

Depends on / 依赖: eq_excenter_of_two_zsmul_oangle_eq, eq_excenter_singleton_of_oangle_eq_add_pi, excenter_singleton_injective, t.eq_excenter_of_two_zsmul_oangle_eq, t.eq_excenter_singleton_of_oangle_eq_add_pi, t.excenter_singleton_injective.ne
-/
lemma eq_excenter_singleton_of_oangle_eq_add_pi_of_oangle_eq_add_pi {p : P}
    (h₁ : ∡ (t.points i₂) (t.points i₁) p = ∡ p (t.points i₁) (t.points i₃) + π)
    (h₂ : ∡ (t.points i₃) (t.points i₂) p = ∡ p (t.points i₂) (t.points i₁) + π) :
    p = t.excenter {i₃} := by
  obtain ⟨signs, rfl⟩ := t.eq_excenter_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ (by rw [h₁]; simp)
    (by rw [h₂]; simp)
  have h₁' := t.eq_excenter_singleton_of_oangle_eq_add_pi h₁₂ h₁₃ h₂₃ h₁
  have h₂' := t.eq_excenter_singleton_of_oangle_eq_add_pi h₂₃ h₁₂.symm h₁₃.symm h₂
  rcases h₁' with h₁' | h₁'
  · rcases h₂' with h₂' | h₂'
    · exact h₂'
    rw [h₂'] at h₁'
    exfalso
    exact t.excenter_singleton_injective.ne h₁₂ h₁'
  · exact h₁'

end Triangle

end Affine
