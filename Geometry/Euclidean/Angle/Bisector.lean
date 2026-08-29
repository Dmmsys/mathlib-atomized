/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Projection

/-!
# Angle bisectors.

This file proves lemmas relating to bisecting angles.

-/

public section


namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
variable [NormedAddTorsor V P]

/--
lemma `dist_orthogonalProjection_eq_iff_angle_eq_aux₁` / 引理 `dist_orthogonalProjection_eq_iff_angle_eq_aux₁`

English:
lemma dist_orthogonalProjection_eq_iff_angle_eq_aux₁
  statement: {p p' : P}
  proof: ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∠ p p' (orthogonalProjection s₁ p) = ∠ p p' (orthogonalProjection s₂ p) := by
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  refine ⟨fun h => 

中文:
引理 dist_orthogonalProjection_eq_iff_angle_eq_aux₁
  结论: {p p' : P}
  证明: ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∠ p p' (orthogonalProjection s₁ p) = ∠ p p' (orthogonalProjection s₂ p) := by
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  refine ⟨fun h => 
-/
private lemma dist_orthogonalProjection_eq_iff_angle_eq_aux₁ {p p' : P}
    {s₁ s₂ : AffineSubspace Real P}
    [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (hp'₁ : p' in s₁) (hp'₂ : p' in s₂) (h' : p in s₁) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∠ p p' (orthogonalProjection s₁ p) = ∠ p p' (orthogonalProjection s₂ p) := by
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [orthogonalProjection_eq_self_iff.2 h'] at h ⊢
    rw [dist_self]; rw [zero_eq_dist]; rw [eq_comm]; rw [orthogonalProjection_eq_self_iff] at h
    rw [orthogonalProjection_eq_self_iff.2 h]
  · rw [orthogonalProjection_eq_self_iff.2 h'] at h ⊢
    rw [dist_self]; rw [zero_eq_dist]; rw [eq_comm]; rw [orthogonalProjection_eq_self_iff]
    obtain rfl | hpp' := eq_or_ne p p'
    · exact hp'₂
    · by_contra hn
      rw [angle_self_of_ne hpp']; rw [angle_comm]; rw [angle_eq_arcsin_of_angle_eq_pi_div_two (angle_self_orthogonalProjection p hp'₂)]; rw [Real.zero_eq_arcsin_iff]; rw [div_eq_zero_iff] at h
      · simp only [dist_eq_zero, hpp', or_false] at h
        rw [eq_comm] at h
        simp [orthogonalProjection_eq_self_iff, hn] at h
      · exact .inl (Ne.symm (orthogonalProjection_eq_self_iff.symm.not.1 hn))

/--
lemma `dist_orthogonalProjection_eq_iff_angle_eq_aux` / 引理 `dist_orthogonalProjection_eq_iff_angle_eq_aux`

English:
lemma dist_orthogonalProjection_eq_iff_angle_eq_aux
  statement: {p p' : P}
  proof: ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∠ p p' (orthogonalProjection s₁ p) = ∠ p p' (orthogonalProjection s₂ p) := by
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  rcases h' with h'

中文:
引理 dist_orthogonalProjection_eq_iff_angle_eq_aux
  结论: {p p' : P}
  证明: ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∠ p p' (orthogonalProjection s₁ p) = ∠ p p' (orthogonalProjection s₂ p) := by
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  rcases h' with h'
-/
private lemma dist_orthogonalProjection_eq_iff_angle_eq_aux {p p' : P}
    {s₁ s₂ : AffineSubspace Real P}
    [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (hp'₁ : p' in s₁) (hp'₂ : p' in s₂) (h' : p in s₁ ∨ p in s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∠ p p' (orthogonalProjection s₁ p) = ∠ p p' (orthogonalProjection s₂ p) := by
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  rcases h' with h' | h'
  · exact dist_orthogonalProjection_eq_iff_angle_eq_aux₁ hp'₁ hp'₂ h'
  · nth_rw 1 [eq_comm]
    nth_rw 2 [eq_comm]
    exact dist_orthogonalProjection_eq_iff_angle_eq_aux₁ hp'₂ hp'₁ h'

/--
lemma `dist_orthogonalProjection_eq_iff_angle_eq` / 引理 `dist_orthogonalProjection_eq_iff_angle_eq`

English:
lemma dist_orthogonalProjection_eq_iff_angle_eq
  statement: {p p' : P} {s₁ s₂ : AffineSubspace Real P}
  proof: ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∠ p p' (orthogonalProjection s₁ p) = ∠ p p' (orthogonalProjection s₂ p) := by
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  by_cases h' : p i

中文:
引理 dist_orthogonalProjection_eq_iff_angle_eq
  结论: {p p' : P} {s₁ s₂ : 仿射子空间 实数 P}
  证明: ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∠ p p' (orthogonalProjection s₁ p) = ∠ p p' (orthogonalProjection s₂ p) := by
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  by_cases h' : p i
-/
lemma dist_orthogonalProjection_eq_iff_angle_eq {p p' : P} {s₁ s₂ : AffineSubspace Real P}
    [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (hp'₁ : p' in s₁) (hp'₂ : p' in s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∠ p p' (orthogonalProjection s₁ p) = ∠ p p' (orthogonalProjection s₂ p) := by
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  by_cases h' : p in s₁ ∨ p in s₂
  · exact dist_orthogonalProjection_eq_iff_angle_eq_aux hp'₁ hp'₂ h'
  rw [not_or] at h'
  rw [angle_comm]; rw [angle_eq_arcsin_of_angle_eq_pi_div_two (angle_self_orthogonalProjection p hp'₁)
      (.inl (Ne.symm (orthogonalProjection_eq_self_iff.symm.not.1 h'.1)))]; rw [angle_comm]; rw [angle_eq_arcsin_of_angle_eq_pi_div_two (angle_self_orthogonalProjection p hp'₂)
      (.inl (Ne.symm (orthogonalProjection_eq_self_iff.symm.not.1 h'.2)))]
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h]
    · have hp : p != p' := by
        rintro rfl
        exact h'.1 hp'₁
      have hpd : 0 < dist p p' := dist_pos.2 hp
      rw [Real.arcsin_inj (le_trans (by norm_num : (-1 : Real) <= 0) (by positivity))
        ((div_le_one hpd).2 ?_)
        (le_trans (by norm_num : (-1 : Real) <= 0) (by positivity)) ((div_le_one hpd).2 ?_)] at h
      · rwa [div_left_inj' hpd.ne'] at h
      · rw [dist_orthogonalProjection_eq_infDist]
        exact Metric.infDist_le_dist_of_mem (SetLike.mem_coe.1 hp'₁)
      · rw [dist_orthogonalProjection_eq_infDist]
        exact Metric.infDist_le_dist_of_mem (SetLike.mem_coe.1 hp'₂)

section Oriented

open Module

variable [Fact (finrank Real V = 2)] [Module.Oriented Real V (Fin 2)]

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

-- See https://github.com/leanprover/lean4/issues/11182 for why hypotheses are after the colon.
/--
lemma `dist_orthogonalProjection_eq_of_oangle_eq` / 引理 `dist_orthogonalProjection_eq_of_oangle_eq`

English:
lemma dist_orthogonalProjection_eq_of_oangle_eq
  statement: {p p' : P} {s₁ s₂ : AffineSubspace Real P}
  proof: ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    orthogonalProjection s₁ p != p' ->
    orthogonalProjection s₂ p != p' ->
    ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p) ->
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) := by
  intro 

中文:
引理 dist_orthogonalProjection_eq_of_oangle_eq
  结论: {p p' : P} {s₁ s₂ : 仿射子空间 实数 P}
  证明: ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    orthogonalProjection s₁ p != p' ->
    orthogonalProjection s₂ p != p' ->
    ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p) ->
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) := by
  intro 
-/
lemma dist_orthogonalProjection_eq_of_oangle_eq {p p' : P} {s₁ s₂ : AffineSubspace Real P}
    (hp'₁ : p' in s₁) (hp'₂ : p' in s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    orthogonalProjection s₁ p != p' ->
    orthogonalProjection s₂ p != p' ->
    ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p) ->
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) := by
  intro hp₁ hp₂ h
  rw [dist_orthogonalProjection_eq_iff_angle_eq hp'₁ hp'₂]; rw [angle_comm]; rw [angle_eq_iff_oangle_eq_or_wbtw hp₁ hp₂]
  exact .inl h

-- See https://github.com/leanprover/lean4/issues/11182 for why hypotheses are after the colon.
/--
lemma `oangle_eq_of_dist_orthogonalProjection_eq` / 引理 `oangle_eq_of_dist_orthogonalProjection_eq`

English:
lemma oangle_eq_of_dist_orthogonalProjection_eq
  statement: {p p' : P} {s₁ s₂ : AffineSubspace Real P}
  proof: ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    (orthogonalProjection s₁ p : P) != orthogonalProjection s₂ p ->
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ->
    ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p) := by
  intro hne h
  ha

中文:
引理 oangle_eq_of_dist_orthogonalProjection_eq
  结论: {p p' : P} {s₁ s₂ : 仿射子空间 实数 P}
  证明: ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    (orthogonalProjection s₁ p : P) != orthogonalProjection s₂ p ->
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ->
    ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p) := by
  intro hne h
  ha
-/
lemma oangle_eq_of_dist_orthogonalProjection_eq {p p' : P} {s₁ s₂ : AffineSubspace Real P}
    (hp'₁ : p' in s₁) (hp'₂ : p' in s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    (orthogonalProjection s₁ p : P) != orthogonalProjection s₂ p ->
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ->
    ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p) := by
  intro hne h
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  have : Nonempty (s₁ ⊓ s₂ : AffineSubspace Real P) := ⟨p', hp'₁, hp'₂⟩
  have hp₁ : orthogonalProjection s₁ p != p' := by
    intro hp
    rw [hp]; rw [eq_comm]; rw [dist_orthogonalProjection_eq_dist_iff_eq_of_mem hp'₂] at h
    grind
  have hp₂ : orthogonalProjection s₂ p != p' := by
    intro hp
    rw [hp]; rw [dist_orthogonalProjection_eq_dist_iff_eq_of_mem hp'₁] at h
    grind
  have hc : ¬ Collinear Real {p', (orthogonalProjection s₁ p : P),
      (orthogonalProjection s₂ p : P)} := by
    intro hc
    have h₁ : (orthogonalProjection s₁ p : P) in line[Real, p', (orthogonalProjection s₂ p : P)] :=
      hc.mem_affineSpan_of_mem_of_ne (by grind) (by grind) (by grind) (by grind)
    have h₁' : (orthogonalProjection s₁ p : P) in s₁ ⊓ s₂ :=
      ⟨orthogonalProjection_mem _,
        SetLike.le_def.1 (affineSpan_pair_le_of_mem_of_mem hp'₂ (orthogonalProjection_mem _)) h₁⟩
    have h₁'' : (orthogonalProjection s₁ p : P) = (orthogonalProjection (s₁ ⊓ s₂) p : P) := by
      rw [← orthogonalProjection_orthogonalProjection_of_le inf_le_left]; rw [eq_comm]; rw [orthogonalProjection_eq_self_iff]
      grind
    have h₂ : (orthogonalProjection s₂ p : P) in line[Real, p', (orthogonalProjection s₁ p : P)] :=
      hc.mem_affineSpan_of_mem_of_ne (by grind) (by grind) (by grind) (by grind)
    have h₂' : (orthogonalProjection s₂ p : P) in s₁ ⊓ s₂ :=
      ⟨SetLike.le_def.1 (affineSpan_pair_le_of_mem_of_mem hp'₁ (orthogonalProjection_mem _)) h₂,
        orthogonalProjection_mem _⟩
    have h₂'' : (orthogonalProjection s₂ p : P) = (orthogonalProjection (s₁ ⊓ s₂) p : P) := by
      rw [← orthogonalProjection_orthogonalProjection_of_le inf_le_right]; rw [eq_comm]; rw [orthogonalProjection_eq_self_iff]
      grind
    apply hne
    rw [h₁'']; rw [h₂'']
  rw [dist_orthogonalProjection_eq_iff_angle_eq hp'₁ hp'₂]; rw [angle_comm]; rw [angle_eq_iff_oangle_eq_or_wbtw hp₁ hp₂] at h
  rcases h with h | h | h
  · exact h
  · exfalso
    exact hc h.collinear
  · exfalso
    have h' := h.collinear
    rw [Set.pair_comm] at h'
    exact hc h'

-- See https://github.com/leanprover/lean4/issues/11182 for why hypotheses are after the colon.
/--
lemma `dist_orthogonalProjection_eq_iff_oangle_eq` / 引理 `dist_orthogonalProjection_eq_iff_oangle_eq`

English:
lemma dist_orthogonalProjection_eq_iff_oangle_eq
  statement: {p p' : P} {s₁ s₂ : AffineSubspace Real P}
  proof: ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    (orthogonalProjection s₁ p : P) != orthogonalProjection s₂ p ->
    orthogonalProjection s₁ p != p' ->
    orthogonalProjection s₂ p != p' ->
    (dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∡ (orthogonalProject

中文:
引理 dist_orthogonalProjection_eq_iff_oangle_eq
  结论: {p p' : P} {s₁ s₂ : 仿射子空间 实数 P}
  证明: ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    (orthogonalProjection s₁ p : P) != orthogonalProjection s₂ p ->
    orthogonalProjection s₁ p != p' ->
    orthogonalProjection s₂ p != p' ->
    (dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∡ (orthogonalProject
-/
lemma dist_orthogonalProjection_eq_iff_oangle_eq {p p' : P} {s₁ s₂ : AffineSubspace Real P}
    (hp'₁ : p' in s₁) (hp'₂ : p' in s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    (orthogonalProjection s₁ p : P) != orthogonalProjection s₂ p ->
    orthogonalProjection s₁ p != p' ->
    orthogonalProjection s₂ p != p' ->
    (dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p)) :=
  fun hne hp₁ hp₂ => ⟨oangle_eq_of_dist_orthogonalProjection_eq hp'₁ hp'₂ hne,
   dist_orthogonalProjection_eq_of_oangle_eq hp'₁ hp'₂ hp₁ hp₂⟩

/--
lemma `dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq` / 引理 `dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq`

English:
lemma dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq
  statement: {p p' : P}
  proof: ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    -- after the colon as these need the `haveI`s above
    orthogonalProjection s₁ p != p' ->
    orthogonalProjection s₂ p != p' ->
    (2 : Int) • ∡ (orthogonalProjection s₁ p : P) p' p =
      (2 : Int) • ∡ p p' (orthogonalProjection s₂ p) ->
    

中文:
引理 dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq
  结论: {p p' : P}
  证明: ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    -- after the colon as these need the `haveI`s above
    orthogonalProjection s₁ p != p' ->
    orthogonalProjection s₂ p != p' ->
    (2 : Int) • ∡ (orthogonalProjection s₁ p : P) p' p =
      (2 : Int) • ∡ p p' (orthogonalProjection s₂ p) ->
    
-/
lemma dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq {p p' : P}
    {s₁ s₂ : AffineSubspace Real P} (hp'₁ : p' in s₁) (hp'₂ : p' in s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    -- after the colon as these need the `haveI`s above
    orthogonalProjection s₁ p != p' ->
    orthogonalProjection s₂ p != p' ->
    (2 : Int) • ∡ (orthogonalProjection s₁ p : P) p' p =
      (2 : Int) • ∡ p p' (orthogonalProjection s₂ p) ->
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) := by
  intro hp₁ hp₂ h
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  have h' : ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p) :=
    oangle_eq_oangle_rev_of_two_zsmul_eq_of_angle_eq_pi_div_two h
      (angle_self_orthogonalProjection _ hp'₁) (angle_self_orthogonalProjection _ hp'₂)
  exact dist_orthogonalProjection_eq_of_oangle_eq hp'₁ hp'₂ hp₁ hp₂ h'

/--
lemma `dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁` / 引理 `dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁`

English:
lemma dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁
  statement: {p p₁ p₂ p₃ : P}
  proof: by
  obtain rfl | hp := eq_or_ne p p₁
  · rw [h', dist_self, zero_eq_dist, eq_comm, orthogonalProjection_eq_self_iff]
    exact left_mem_affineSpan_pair _ _ _
  · rw [← h'] at h hp
    have hpm : p ∉ line[Real, p₁, p₂] := orthogonalProjection_eq_self_iff.not.1 (Ne.symm hp)
    rw [two_zsmul_oangle_o

中文:
引理 dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁
  结论: {p p₁ p₂ p₃ : P}
  证明: by
  obtain rfl | hp := eq_or_ne p p₁
  · rw [h', dist_self, zero_eq_dist, eq_comm, orthogonalProjection_eq_self_iff]
    exact left_mem_affineSpan_pair _ _ _
  · rw [← h'] at h hp
    have hpm : p ∉ line[Real, p₁, p₂] := orthogonalProjection_eq_self_iff.not.1 (Ne.symm hp)
    rw [two_zsmul_oangle_o
-/
private lemma dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁ {p p₁ p₂ p₃ : P}
    (h₂ : p₁ != p₂) (h : (2 : Int) • ∡ p₂ p₁ p = (2 : Int) • ∡ p p₁ p₃)
    (h' : orthogonalProjection line[Real, p₁, p₂] p = p₁) :
    dist p (orthogonalProjection line[Real, p₁, p₂] p) =
      dist p (orthogonalProjection line[Real, p₁, p₃] p) := by
  obtain rfl | hp := eq_or_ne p p₁
  · rw [h', dist_self, zero_eq_dist, eq_comm, orthogonalProjection_eq_self_iff]
    exact left_mem_affineSpan_pair _ _ _
  · rw [← h'] at h hp
    have hpm : p ∉ line[Real, p₁, p₂] := orthogonalProjection_eq_self_iff.not.1 (Ne.symm hp)
    rw [two_zsmul_oangle_orthogonalProjection_self _ hpm (right_mem_affineSpan_pair _ _ _)
          (h'.symm ▸ h₂.symm)]; rw [eq_comm]; rw [oangle]; rw [Real.Angle.two_zsmul_eq_pi_iff]; rw [h'] at h
    replace h := (Orientation.eq_zero_or_oangle_eq_iff_inner_eq_zero _).1 (.inr (.inr h))
    congr 1
    rw [h']; rw [eq_comm]; rw [coe_orthogonalProjection_eq_iff_mem]
    refine ⟨left_mem_affineSpan_pair _ _ _, ?_⟩
    rw [Submodule.mem_orthogonal']
    intro u hu
    rw [direction_affineSpan]; rw [mem_vectorSpan_pair] at hu
    rcases hu with ⟨r, rfl⟩
    rw [inner_smul_right]; rw [← inner_neg_neg]; rw [inner_neg_left]
    simp [h]

/--
lemma `dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₂` / 引理 `dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₂`

English:
lemma dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₂
  statement: {p p₁ p₂ p₃ : P}
  proof: by
  rcases h' with h' | h'
  · exact dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁ h₂ h h'
  · refine (dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁ h₃ ?_ h').symm
    rw [oangle_rev]; rw [smul_neg]; rw [← h]; rw [oangle_rev]; rw [smul_neg]; rw [neg_neg]

中文:
引理 dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₂
  结论: {p p₁ p₂ p₃ : P}
  证明: by
  rcases h' with h' | h'
  · exact dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁ h₂ h h'
  · refine (dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁ h₃ ?_ h').symm
    rw [oangle_rev]; rw [smul_neg]; rw [← h]; rw [oangle_rev]; rw [smul_neg]; rw [neg_neg]
-/
private lemma dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₂ {p p₁ p₂ p₃ : P}
    (h₂ : p₁ != p₂) (h₃ : p₁ != p₃) (h : (2 : Int) • ∡ p₂ p₁ p = (2 : Int) • ∡ p p₁ p₃)
    (h' : orthogonalProjection line[Real, p₁, p₂] p = p₁ ∨
      orthogonalProjection line[Real, p₁, p₃] p = p₁) :
    dist p (orthogonalProjection line[Real, p₁, p₂] p) =
      dist p (orthogonalProjection line[Real, p₁, p₃] p) := by
  rcases h' with h' | h'
  · exact dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁ h₂ h h'
  · refine (dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁ h₃ ?_ h').symm
    rw [oangle_rev]; rw [smul_neg]; rw [← h]; rw [oangle_rev]; rw [smul_neg]; rw [neg_neg]

/--
lemma `dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq` / 引理 `dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq`

English:
lemma dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq
  statement: {p p₁ p₂ p₃ : P} (h₂ : p₁ != p₂)
  proof: by
  by_cases h' : orthogonalProjection line[Real, p₁, p₂] p = p₁ ∨
      orthogonalProjection line[Real, p₁, p₃] p = p₁
  · exact dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₂ h₂ h₃ h h'
  · rw [not_or] at h'
    refine dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq
      (left

中文:
引理 dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq
  结论: {p p₁ p₂ p₃ : P} (h₂ : p₁ != p₂)
  证明: by
  by_cases h' : orthogonalProjection line[Real, p₁, p₂] p = p₁ ∨
      orthogonalProjection line[Real, p₁, p₃] p = p₁
  · exact dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₂ h₂ h₃ h h'
  · rw [not_or] at h'
    refine dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq
      (left

Depends on / 依赖: collinear_insert_of_mem_affi, collinear_insert_of_mem_affineSpan_pair, dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq, left_mem_affineSpan_pair, not_or, orthogonalProjection, orthogonalProjection_mem, two_zsmul_oangle_eq_left
-/
lemma dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq {p p₁ p₂ p₃ : P} (h₂ : p₁ != p₂)
    (h₃ : p₁ != p₃) (h : (2 : Int) • ∡ p₂ p₁ p = (2 : Int) • ∡ p p₁ p₃) :
    dist p (orthogonalProjection line[Real, p₁, p₂] p) =
      dist p (orthogonalProjection line[Real, p₁, p₃] p) := by
  by_cases h' : orthogonalProjection line[Real, p₁, p₂] p = p₁ ∨
      orthogonalProjection line[Real, p₁, p₃] p = p₁
  · exact dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₂ h₂ h₃ h h'
  · rw [not_or] at h'
    refine dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq
      (left_mem_affineSpan_pair _ _ _) (left_mem_affineSpan_pair _ _ _) h'.1 h'.2 ?_
    rw [(collinear_insert_of_mem_affineSpan_pair
          (orthogonalProjection_mem p)).two_zsmul_oangle_eq_left h'.1 h₂.symm]; rw [(collinear_insert_of_mem_affineSpan_pair
        (orthogonalProjection_mem p)).two_zsmul_oangle_eq_right h'.2 h₃.symm]; rw [h]

/--
lemma `two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq` / 引理 `two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq`

English:
lemma two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq
  statement: {p p₁ p₂ p₃ : P}
  proof: by
  by_cases ho : (orthogonalProjection line[Real, p₁, p₂] p : P) =
      orthogonalProjection line[Real, p₁, p₃] p
  · suffices p = p₁ by simp [this]
    have hs := orthogonalProjection_sup_of_orthogonalProjection_eq ho
    have hinf : line[Real, p₁, p₂] ⊓ line[Real, p₁, p₃] = affineSpan Real {p₁}

中文:
引理 two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq
  结论: {p p₁ p₂ p₃ : P}
  证明: by
  by_cases ho : (orthogonalProjection line[Real, p₁, p₂] p : P) =
      orthogonalProjection line[Real, p₁, p₃] p
  · suffices p = p₁ by simp [this]
    have hs := orthogonalProjection_sup_of_orthogonalProjection_eq ho
    have hinf : line[Real, p₁, p₂] ⊓ line[Real, p₁, p₃] = affineSpan Real {p₁}

Depends on / 依赖: Set.image_insert_eq, affineSpan, convert, ha.inf_affineSpan_eq_affineSpan_inter, image_insert_eq, inf_affineSpan_eq_affineSpan_inter, orthogonalProjection, orthogonalProjection_sup_of_orthogonalProjection_eq
-/
lemma two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq {p p₁ p₂ p₃ : P}
    (ha : AffineIndependent Real ![p₁, p₂, p₃])
    (h : dist p (orthogonalProjection line[Real, p₁, p₂] p) =
      dist p (orthogonalProjection line[Real, p₁, p₃] p)) :
    (2 : Int) • ∡ p₂ p₁ p = (2 : Int) • ∡ p p₁ p₃ := by
  by_cases ho : (orthogonalProjection line[Real, p₁, p₂] p : P) =
      orthogonalProjection line[Real, p₁, p₃] p
  · suffices p = p₁ by simp [this]
    have hs := orthogonalProjection_sup_of_orthogonalProjection_eq ho
    have hinf : line[Real, p₁, p₂] ⊓ line[Real, p₁, p₃] = affineSpan Real {p₁} := by
      convert! (ha.inf_affineSpan_eq_affineSpan_inter {0, 1} {0, 2})
      · simp [Set.image_insert_eq]
      · simp [Set.image_insert_eq]
      · suffices {p₁} = ![p₁, p₂, p₃] '' {0} by grind
        simp
    have hsup : line[Real, p₁, p₂] ⊔ line[Real, p₁, p₃] = ⊤ := by
      rw [← AffineSubspace.span_union]
      convert! ha.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 ?_
      · simp
        grind
      · simpa using Fact.out
    have hp : orthogonalProjection (line[Real, p₁, p₂]) p = p₁ := by
      suffices (orthogonalProjection (line[Real, p₁, p₂]) p : P) in affineSpan Real {p₁} by
        simpa using this
      have hi : (orthogonalProjection (line[Real, p₁, p₂]) p : P) in
          line[Real, p₁, p₂] ⊓ line[Real, p₁, p₃] :=
        ⟨orthogonalProjection_mem _, ho ▸ orthogonalProjection_mem _⟩
      rwa [hinf] at hi
    rw [← orthogonalProjection_sup_of_orthogonalProjection_eq ho] at hp
    rw [← hp]; rw [eq_comm]; rw [orthogonalProjection_eq_self_iff]; rw [hsup]
    exact AffineSubspace.mem_top Real V p
  · have hp := oangle_eq_of_dist_orthogonalProjection_eq
      (left_mem_affineSpan_pair _ _ _) (left_mem_affineSpan_pair _ _ _) ho h
    have h₂₁ : p₂ != p₁ := ha.injective.ne (by decide : (1 : Fin 3) != 0)
    have h₃₁ : p₃ != p₁ := ha.injective.ne (by decide : (2 : Fin 3) != 0)
    have hp₁ : orthogonalProjection line[Real, p₁, p₂] p != p₁ := by
      intro hp
      rw [hp]; rw [eq_comm]; rw [dist_orthogonalProjection_eq_dist_iff_eq_of_mem
        (left_mem_affineSpan_pair Real _ p₃)] at h
      grind
    have hp₂ : orthogonalProjection line[Real, p₁, p₃] p != p₁ := by
      intro hp
      rw [hp]; rw [dist_orthogonalProjection_eq_dist_iff_eq_of_mem
          (left_mem_affineSpan_pair Real _ p₂)] at h
      grind
    rw [← (collinear_insert_of_mem_affineSpan_pair
             (orthogonalProjection_mem p)).two_zsmul_oangle_eq_left hp₁ h₂₁]; rw [← (collinear_insert_of_mem_affineSpan_pair
             (orthogonalProjection_mem p)).two_zsmul_oangle_eq_right hp₂ h₃₁]; rw [hp]

/--
lemma `dist_orthogonalProjection_line_eq_iff_two_zsmul_oangle_eq` / 引理 `dist_orthogonalProjection_line_eq_iff_two_zsmul_oangle_eq`

English:
lemma dist_orthogonalProjection_line_eq_iff_two_zsmul_oangle_eq
  statement: {p p₁ p₂ p₃ : P}
  proof: ⟨two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq ha,
    dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq
      (ha.injective.ne (by decide : (0 : Fin 3) != 1))
      (ha.injective.ne (by decide : (0 : Fin 3) != 2))⟩

中文:
引理 dist_orthogonalProjection_line_eq_iff_two_zsmul_oangle_eq
  结论: {p p₁ p₂ p₃ : P}
  证明: ⟨two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq ha,
    dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq
      (ha.injective.ne (by decide : (0 : Fin 3) != 1))
      (ha.injective.ne (by decide : (0 : Fin 3) != 2))⟩

Depends on / 依赖: dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq, ha.injective.ne, injective, two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq
-/
lemma dist_orthogonalProjection_line_eq_iff_two_zsmul_oangle_eq {p p₁ p₂ p₃ : P}
    (ha : AffineIndependent Real ![p₁, p₂, p₃]) :
    dist p (orthogonalProjection line[Real, p₁, p₂] p) =
      dist p (orthogonalProjection line[Real, p₁, p₃] p) ↔
        (2 : Int) • ∡ p₂ p₁ p = (2 : Int) • ∡ p p₁ p₃ :=
  ⟨two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq ha,
    dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq
      (ha.injective.ne (by decide : (0 : Fin 3) != 1))
      (ha.injective.ne (by decide : (0 : Fin 3) != 2))⟩

end Oriented

end EuclideanGeometry
