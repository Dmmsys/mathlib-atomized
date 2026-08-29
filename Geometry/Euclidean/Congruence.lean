/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Chu Zheng
-/
module

public import Mathlib.Topology.MetricSpace.Congruence
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Triangle

/-!
# Triangle congruence

This file proves the classical triangle congruence criteria for (possibly degenerate) triangles
in real inner product spaces and Euclidean affine spaces.
We prove SSS, SAS, ASA, and AAS congruence.

## Implementation notes

Side–Side–Side (SSS) congruence is proved using the definition of `Congruent`.
Side–Angle–Side (SAS) congruence is proved via the law of cosines.
Angle–Side–Angle (ASA) congruence is reduced to SAS using the law of sines.
Angle–Angle–Side (AAS) congruence uses the fact that the sum of the angles in a triangle equals π,
then reduces to ASA.

## References

* https://en.wikipedia.org/wiki/Congruence_(geometry)

-/

public section

open scoped Congruent

namespace EuclideanGeometry

variable {ι V₁ V₂ P₁ P₂ : Type*}
  [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
  [InnerProductSpace Real V₁] [InnerProductSpace Real V₂]
  [MetricSpace P₁] [MetricSpace P₂]
  [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
  {v₁ : ι -> P₁} {v₂ : ι -> P₂}
  {a b c : P₁} {a' b' c' : P₂}

/--
lemma `triangle_congruent_iff_dist_eq` / 引理 `triangle_congruent_iff_dist_eq`

English:
lemma triangle_congruent_iff_dist_eq
  given: {t₁ : Fin 3 -> P₁} {t₂ : Fin 3 -> P₂}
  proof: congruent_iff_dist_eq

中文:
引理 triangle_congruent_iff_dist_eq
  条件: {t₁ : Fin 3 -> P₁} {t₂ : Fin 3 -> P₂}
  证明: congruent_iff_dist_eq

Depends on / 依赖: congruent_iff_dist_eq
-/
lemma triangle_congruent_iff_dist_eq {t₁ : Fin 3 -> P₁} {t₂ : Fin 3 -> P₂} :
    t₁ ≅ t₂ ↔ forall (i j : Fin 3), dist (t₁ i) (t₁ j) = dist (t₂ i) (t₂ j) := congruent_iff_dist_eq

/--
theorem `side_side_side` / 定理 `side_side_side`

English:
theorem side_side_side
  statement: (hd₁ : dist a b = dist a' b') (hd₂ : dist b c = dist b' c')
  proof: by
  rw [triangle_congruent_iff_dist_eq]
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [dist_comm]

中文:
定理 side_side_side
  结论: (hd₁ : dist a b = dist a' b') (hd₂ : dist b c = dist b' c')
  证明: by
  rw [triangle_congruent_iff_dist_eq]
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [dist_comm]

Depends on / 依赖: dist_comm, fin_cases, triangle_congruent_iff_dist_eq
-/
theorem side_side_side (hd₁ : dist a b = dist a' b') (hd₂ : dist b c = dist b' c')
    (hd₃ : dist c a = dist c' a') :
    ![a, b, c] ≅ ![a', b', c'] := by
  rw [triangle_congruent_iff_dist_eq]
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [dist_comm]

/--
theorem `side_angle_side` / 定理 `side_angle_side`

English:
theorem side_angle_side
  statement: (h : ∠ a b c = ∠ a' b' c') (hd₁ : dist a b = dist a' b')
  proof: by
  apply side_side_side hd₁ hd₂
  rw [dist_comm]; rw [dist_comm c' a']; rw [← sq_eq_sq₀ (by positivity) (by positivity)]; rw [pow_two]; rw [pow_two]; rw [EuclideanGeometry.law_cos a b c]; rw [EuclideanGeometry.law_cos a' b' c']
  simp [h, hd₁, hd₂, dist_comm]

中文:
定理 side_angle_side
  结论: (h : ∠ a b c = ∠ a' b' c') (hd₁ : dist a b = dist a' b')
  证明: by
  apply side_side_side hd₁ hd₂
  rw [dist_comm]; rw [dist_comm c' a']; rw [← sq_eq_sq₀ (by positivity) (by positivity)]; rw [pow_two]; rw [pow_two]; rw [EuclideanGeometry.law_cos a b c]; rw [EuclideanGeometry.law_cos a' b' c']
  simp [h, hd₁, hd₂, dist_comm]

Depends on / 依赖: EuclideanGeometry, EuclideanGeometry.law_cos, dist_comm, law_cos, pow_two, side_side_side
-/
theorem side_angle_side (h : ∠ a b c = ∠ a' b' c') (hd₁ : dist a b = dist a' b')
    (hd₂ : dist b c = dist b' c') : ![a, b, c] ≅ ![a', b', c'] := by
  apply side_side_side hd₁ hd₂
  rw [dist_comm]; rw [dist_comm c' a']; rw [← sq_eq_sq₀ (by positivity) (by positivity)]; rw [pow_two]; rw [pow_two]; rw [EuclideanGeometry.law_cos a b c]; rw [EuclideanGeometry.law_cos a' b' c']
  simp [h, hd₁, hd₂, dist_comm]

/--
theorem `angle_side_angle` / 定理 `angle_side_angle`

English:
theorem angle_side_angle
  statement: (h : ¬Collinear Real {a, b, c}) (ha₁ : ∠ a b c = ∠ a' b' c')
  proof: by
  have h' : ¬Collinear Real {a', b', c'} := by
    grind only [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, angle_self_right,
      angle_self_left, dist_eq_zero, Set.insert_comm, Set.pair_comm]
  have ha₃ := angle_add_angle_add_angle_eq_pi b (ne₁₃_of_not_collinear h)
  have ha₃' := an

中文:
定理 angle_side_angle
  结论: (h : ¬Collinear 实数 {a, b, c}) (ha₁ : ∠ a b c = ∠ a' b' c')
  证明: by
  have h' : ¬Collinear Real {a', b', c'} := by
    grind only [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, angle_self_right,
      angle_self_left, dist_eq_zero, Set.insert_comm, Set.pair_comm]
  have ha₃ := angle_add_angle_add_angle_eq_pi b (ne₁₃_of_not_collinear h)
  have ha₃' := an

Depends on / 依赖: Collinear, Set.insert_comm, Set.pair_comm, add_right_cancel_iff, angle_add_angle_add_angle_eq_pi, angle_comm, angle_self_left, angle_self_right, collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, dist_eq_zero, h_bac, insert_comm, pair_comm
-/
theorem angle_side_angle (h : ¬Collinear Real {a, b, c}) (ha₁ : ∠ a b c = ∠ a' b' c')
    (hd : dist b c = dist b' c') (ha₂ : ∠ b c a = ∠ b' c' a') : ![a, b, c] ≅ ![a', b', c'] := by
  have h' : ¬Collinear Real {a', b', c'} := by
    grind only [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, angle_self_right,
      angle_self_left, dist_eq_zero, Set.insert_comm, Set.pair_comm]
  have ha₃ := angle_add_angle_add_angle_eq_pi b (ne₁₃_of_not_collinear h)
  have ha₃' := angle_add_angle_add_angle_eq_pi b' (ne₁₃_of_not_collinear h')
  simp only [← ha₃', ha₁, ha₂, angle_comm b' c' a', add_right_cancel_iff] at ha₃
  have h_bac : ¬Collinear Real {b, a, c} := by simpa [Set.insert_comm] using h
  have h_bac' : ¬Collinear Real {b', a', c'} := by simpa [Set.insert_comm] using h'
  have dist_ab_eq : dist a b = dist a' b' := by
    rw [dist_comm a b]; rw [dist_comm a' b']; rw [dist_eq_dist_mul_sin_angle_div_sin_angle h_bac]; rw [dist_eq_dist_mul_sin_angle_div_sin_angle h_bac']; rw [dist_comm c b]; rw [dist_comm c' b']; rw [hd]; rw [angle_comm]; rw [ha₂]; rw [angle_comm b' c' a']; rw [angle_comm b a c]; rw [ha₃]; rw [angle_comm b' a' c']
  exact side_angle_side ha₁ dist_ab_eq hd

/--
theorem `angle_angle_side` / 定理 `angle_angle_side`

English:
theorem angle_angle_side
  statement: (h : ¬Collinear Real {a, b, c}) (ha₁ : ∠ a b c = ∠ a' b' c')
  proof: by
  have ha₃ := angle_add_angle_add_angle_eq_pi b (ne₁₃_of_not_collinear h)
  have h' : ¬Collinear Real {a', b', c'} := by
    grind only [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, angle_self_right,
      angle_self_left, dist_eq_zero, Set.insert_comm, Set.pair_comm]
  have ha₃' := an

中文:
定理 angle_angle_side
  结论: (h : ¬Collinear 实数 {a, b, c}) (ha₁ : ∠ a b c = ∠ a' b' c')
  证明: by
  have ha₃ := angle_add_angle_add_angle_eq_pi b (ne₁₃_of_not_collinear h)
  have h' : ¬Collinear Real {a', b', c'} := by
    grind only [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, angle_self_right,
      angle_self_left, dist_eq_zero, Set.insert_comm, Set.pair_comm]
  have ha₃' := an

Depends on / 依赖: Collinear, Set.insert_comm, Set.pair_c, Set.pair_comm, add_right_cancel_iff, angle_add_angle_add_angle_eq_pi, angle_comm, angle_self_left, angle_self_right, collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, dist_eq_zero, h_bca, insert_comm, pair_c, pair_comm
-/
theorem angle_angle_side (h : ¬Collinear Real {a, b, c}) (ha₁ : ∠ a b c = ∠ a' b' c')
    (ha₂ : ∠ b c a = ∠ b' c' a') (hd : dist c a = dist c' a') : ![a, b, c] ≅ ![a', b', c'] := by
  have ha₃ := angle_add_angle_add_angle_eq_pi b (ne₁₃_of_not_collinear h)
  have h' : ¬Collinear Real {a', b', c'} := by
    grind only [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, angle_self_right,
      angle_self_left, dist_eq_zero, Set.insert_comm, Set.pair_comm]
  have ha₃' := angle_add_angle_add_angle_eq_pi b' (ne₁₃_of_not_collinear h')
  simp only [← ha₃', ha₁, ha₂, angle_comm b' c' a', add_right_cancel_iff] at ha₃
  have h_bca : ¬Collinear Real {b, c, a} := by rwa [Set.insert_comm, Set.pair_comm] at h
  have h1 := angle_side_angle h_bca ha₂ hd ha₃
  exact angle_side_angle h ha₁ (h1.dist_eq 0 1) ha₂

include V₁ V₂

/--
theorem `angle_eq_of_congruent` / 定理 `angle_eq_of_congruent`

English:
theorem angle_eq_of_congruent
  given: (h : v₁ ≅ v₂) (i j k : ι)
  proof: by
  unfold EuclideanGeometry.angle
  unfold InnerProductGeometry.angle
  simp_rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub, h.dist_eq]

中文:
定理 angle_eq_of_congruent
  条件: (h : v₁ ≅ v₂) (i j k : ι)
  证明: by
  unfold EuclideanGeometry.angle
  unfold InnerProductGeometry.angle
  simp_rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub, h.dist_eq]

Depends on / 依赖: EuclideanGeometry, EuclideanGeometry.angle, InnerProductGeometry, InnerProductGeometry.angle, dist_eq, dist_eq_norm_vsub, h.dist_eq, real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, simp_rw, vsub_sub_vsub_cancel_right
-/
theorem angle_eq_of_congruent (h : v₁ ≅ v₂) (i j k : ι) :
    ∠ (v₁ i) (v₁ j) (v₁ k) = ∠ (v₂ i) (v₂ j) (v₂ k) := by
  unfold EuclideanGeometry.angle
  unfold InnerProductGeometry.angle
  simp_rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub, h.dist_eq]

end EuclideanGeometry
