/-
Copyright (c) 2025 Chu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chu Zheng
-/
module

public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Topology.MetricSpace.Similarity
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

/-!
# Triangle Similarity

This file contains theorems about similarity of triangles, including conditions
for similarity based on sides and angles.

-/

public section

open scoped Congruent EuclideanGeometry

open Similar NNReal Affine

namespace EuclideanGeometry

variable {ι V₁ V₂ P₁ P₂ : Type*}
  [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
  [InnerProductSpace Real V₁] [InnerProductSpace Real V₂]
  [MetricSpace P₁] [MetricSpace P₂]
  [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
  {v₁ : ι -> P₁} {v₂ : ι -> P₂}
  {a b c : P₁} {a' b' c' : P₂}

/--
theorem `similar_of_angle_angle` / 定理 `similar_of_angle_angle`

English:
theorem similar_of_angle_angle
  statement: (h_not_col : ¬ Collinear Real {a, b, c}) (h₁ : ∠ a b c = ∠ a' b' c')
  proof: by
  have hne_pi_div_two : ∠ a b c != Real.pi / 2 ∨ ∠ b c a != Real.pi / 2 := by
    by_contra! hq
    have := angle_lt_pi_div_two_of_angle_eq_pi_div_two hq.1 (ne₂₃_of_not_collinear h_not_col).symm
    grind
  have not_all_eq : a' != b' ∨ b' != c' ∨ a' != c' := by grind [angle_self_left]
  have h_no

中文:
定理 similar_of_angle_angle
  结论: (h_not_col : ¬ Collinear 实数 {a, b, c}) (h₁ : ∠ a b c = ∠ a' b' c')
  证明: by
  have hne_pi_div_two : ∠ a b c != Real.pi / 2 ∨ ∠ b c a != Real.pi / 2 := by
    by_contra! hq
    have := angle_lt_pi_div_two_of_angle_eq_pi_div_two hq.1 (ne₂₃_of_not_collinear h_not_col).symm
    grind
  have not_all_eq : a' != b' ∨ b' != c' ∨ a' != c' := by grind [angle_self_left]
  have h_no

Depends on / 依赖: Collinear, Real.pi, Set.insert_comm, Set.pair_comm, angle_lt_pi_div_two_of_angle_eq_pi_div_two, angle_self_left, angle_self_right, collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, h_not_col, h_pos1, hne_pi_div_two, insert_comm, not_all_eq, pair_comm
-/
theorem similar_of_angle_angle (h_not_col : ¬ Collinear Real {a, b, c}) (h₁ : ∠ a b c = ∠ a' b' c')
    (h₂ : ∠ b c a = ∠ b' c' a') :
    ![a, b, c] ∼ ![a', b', c'] := by
  have hne_pi_div_two : ∠ a b c != Real.pi / 2 ∨ ∠ b c a != Real.pi / 2 := by
    by_contra! hq
    have := angle_lt_pi_div_two_of_angle_eq_pi_div_two hq.1 (ne₂₃_of_not_collinear h_not_col).symm
    grind
  have not_all_eq : a' != b' ∨ b' != c' ∨ a' != c' := by grind [angle_self_left]
  have h_not_col' : ¬ Collinear Real {a', b', c'} := by
    grind only [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, angle_self_right,
      angle_self_left, Set.insert_comm, Set.pair_comm]
  have h_pos1 : 0 < dist a b := by simp [dist_pos, ne₁₂_of_not_collinear h_not_col]
  have h_pos1' : 0 < dist a' b' := by simp [dist_pos, ne₁₂_of_not_collinear h_not_col']
  have h_pos2 : 0 < dist b c := by simp [dist_pos, ne₂₃_of_not_collinear h_not_col]
  have h_pos2' : 0 < dist b' c' := by simp [dist_pos, ne₂₃_of_not_collinear h_not_col']
  have h₃ : ∠ c a b = ∠ c' a' b' := by
    have hsum := angle_add_angle_add_angle_eq_pi c (ne₁₂_of_not_collinear h_not_col)
    have hsum' := angle_add_angle_add_angle_eq_pi c' (ne₁₂_of_not_collinear h_not_col')
    grind [angle_comm]
  have h_sin_ne1 : Real.sin (∠ b c a) != 0 := by
    grind only [sin_ne_zero_of_not_collinear, Set.pair_comm, Set.insert_comm]
  have h_sin_ne2 : Real.sin (∠ c a b) != 0 := by
    grind only [sin_ne_zero_of_not_collinear, Set.pair_comm, Set.insert_comm]
  have h_sin1 := law_sin c a b
  have h_sin1' := law_sin c' a' b'
  rw [← eq_div_iff_mul_eq (by positivity)] at h_sin1 h_sin1'
  rw [← h₃]; rw [← h₂] at h_sin1'
  rw [h_sin1']; rw [mul_div_assoc]; rw [mul_div_assoc]; rw [mul_right_inj' h_sin_ne1]; rw [div_eq_div_iff (by positivity) (by positivity)]; rw [mul_comm] at h_sin1
  have h_sin2 := law_sin a b c
  have h_sin2' := law_sin a' b' c'
  rw [← eq_div_iff_mul_eq (by positivity)] at h_sin2 h_sin2'
  rw [← h₁]; rw [← h₃] at h_sin2'
  rw [h_sin2']; rw [mul_div_assoc]; rw [mul_div_assoc]; rw [mul_right_inj' h_sin_ne2]; rw [div_eq_div_iff (by positivity) (by positivity)]; rw [mul_comm] at h_sin2
  apply Similar.reverse_of_three
  apply Similar.comm_left
  exact similar_of_side_side (by positivity) (by positivity) h_sin2 h_sin1.symm

/--
theorem `similar_of_side_angle_side` / 定理 `similar_of_side_angle_side`

English:
theorem similar_of_side_angle_side
  statement: (h_not_col : ¬ Collinear Real {a, b, c})
  proof: by
  have dist_a'b' : dist a' b' != 0 := by simp [ne₁₂_of_not_collinear h_not_col']
  have dist_b'c' : dist b' c' != 0 := by simp [ne₂₃_of_not_collinear h_not_col']
  rw [← div_eq_div_iff dist_a'b' dist_b'c'] at hd
  set k := (dist a b / dist a' b') with hk
  have k_pos : 0 < k := by
    rw [hk]
   

中文:
定理 similar_of_side_angle_side
  结论: (h_not_col : ¬ Collinear 实数 {a, b, c})
  证明: by
  have dist_a'b' : dist a' b' != 0 := by simp [ne₁₂_of_not_collinear h_not_col']
  have dist_b'c' : dist b' c' != 0 := by simp [ne₂₃_of_not_collinear h_not_col']
  rw [← div_eq_div_iff dist_a'b' dist_b'c'] at hd
  set k := (dist a b / dist a' b') with hk
  have k_pos : 0 < k := by
    rw [hk]
   

Depends on / 依赖: dist_a, dist_b, dist_pos, div_eq_div_iff, div_pos, h_ab, h_bc, h_not_col, k_pos
-/
theorem similar_of_side_angle_side (h_not_col : ¬ Collinear Real {a, b, c})
    (h_not_col' : ¬ Collinear Real {a', b', c'}) (h : ∠ a b c = ∠ a' b' c')
    (hd : dist a b * dist b' c' = dist b c * dist a' b') :
    ![a, b, c] ∼ ![a', b', c'] := by
  have dist_a'b' : dist a' b' != 0 := by simp [ne₁₂_of_not_collinear h_not_col']
  have dist_b'c' : dist b' c' != 0 := by simp [ne₂₃_of_not_collinear h_not_col']
  rw [← div_eq_div_iff dist_a'b' dist_b'c'] at hd
  set k := (dist a b / dist a' b') with hk
  have k_pos : 0 < k := by
    rw [hk]
    apply div_pos
    · simp [dist_pos, ne₁₂_of_not_collinear h_not_col]
    · simp [dist_pos, ne₁₂_of_not_collinear h_not_col']
  have h_ab : dist a b = k * dist a' b' := by grind
  have h_bc : dist b c = k * dist b' c' := by grind
  have hcos := law_cos a b c
  rw [dist_comm b _]; rw [dist_comm b' _] at h_bc
  rw [h_ab]; rw [h_bc] at hcos
  field_simp at hcos
  rw [h] at hcos
  have hcos' := law_cos a' b' c'
  field_simp at hcos'
  rw [← hcos']; rw [← mul_pow] at hcos
  have dist_ac_pos : 0 < dist a c := by grind [dist_pos, ne₁₃_of_not_collinear]
  have k_dist_a'c' : 0 <= k * dist a' c' := by positivity
  rw [pow_left_inj₀ (le_of_lt dist_ac_pos) k_dist_a'c' (by norm_num)]; rw [dist_comm a _]; rw [dist_comm a' _] at hcos
  rw [dist_comm c _]; rw [dist_comm c' _] at h_bc
  rw [similar_iff_exists_pos_pairwise_dist_eq]
  use k
  refine ⟨k_pos, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> try {rw [dist_self, dist_self, mul_zero]}
  all_goals simp; grind [dist_comm]

/--
theorem `_root_.Similar.angle_eq` / 定理 `_root_.Similar.angle_eq`

English:
theorem _root_.Similar.angle_eq
  given: (h : ![a, b, c] ∼ ![a', b', c'])
  proof: by
  rw [similar_iff_exists_pos_dist_eq] at h
  rcases h with ⟨r, hr_pos, hdist⟩
  have h_ab : dist a b = r * dist a' b' := hdist 0 1
  have h_cb : dist c b = r * dist c' b' := hdist 2 1
  have h_ac : dist a c = r * dist a' c' := hdist 0 2
  have h_cos := law_cos a b c
  rw [h_ab]; rw [h_cb]; rw [h_

中文:
定理 _root_.Similar.angle_eq
  条件: (h : ![a, b, c] ∼ ![a', b', c'])
  证明: by
  rw [similar_iff_exists_pos_dist_eq] at h
  rcases h with ⟨r, hr_pos, hdist⟩
  have h_ab : dist a b = r * dist a' b' := hdist 0 1
  have h_cb : dist c b = r * dist c' b' := hdist 2 1
  have h_ac : dist a c = r * dist a' c' := hdist 0 2
  have h_cos := law_cos a b c
  rw [h_ab]; rw [h_cb]; rw [h_

Depends on / 依赖: h_ab, h_ac, h_cb, h_cos, hr_pos, law_cos, mul_eq_zero_iff_right, similar_iff_exists_pos_dist_eq, sub_right_inj
-/
theorem _root_.Similar.angle_eq (h : ![a, b, c] ∼ ![a', b', c']) :
    ∠ a b c = ∠ a' b' c' := by
  rw [similar_iff_exists_pos_dist_eq] at h
  rcases h with ⟨r, hr_pos, hdist⟩
  have h_ab : dist a b = r * dist a' b' := hdist 0 1
  have h_cb : dist c b = r * dist c' b' := hdist 2 1
  have h_ac : dist a c = r * dist a' c' := hdist 0 2
  have h_cos := law_cos a b c
  rw [h_ab]; rw [h_cb]; rw [h_ac] at h_cos
  field_simp at h_cos
  have h_cos' := law_cos a' b' c'
  field_simp at h_cos'
  rw [h_cos']; rw [sub_right_inj] at h_cos
  by_cases heq : dist a' b' * dist c' b' * 2 = 0
  · rw [mul_eq_zero_iff_right (by norm_num), mul_eq_zero] at heq
    rcases heq with h1 | h2
    · have h_dist_ab : dist a b = 0 := by grind
      rw [dist_eq_zero] at h_dist_ab h1
      simp_rw [h_dist_ab, h1, angle_self_left]
    · have h_dist_cb : dist c b = 0 := by grind
      rw [dist_eq_zero] at h_dist_cb h2
      simp_rw [h_dist_cb, h2, angle_self_right]
  rw [mul_right_inj' heq] at h_cos
  apply Real.injOn_cos at h_cos
  repeat grind [angle_nonneg, angle_le_pi]

/--
theorem `_root_.Similar.angle_eq_all` / 定理 `_root_.Similar.angle_eq_all`

English:
theorem _root_.Similar.angle_eq_all
  given: (h : ![a, b, c] ∼ ![a', b', c'])
  proof: ⟨h.angle_eq, h.comm_left.comm_right.angle_eq, h.comm_right.comm_left.angle_eq⟩

中文:
定理 _root_.Similar.angle_eq_all
  条件: (h : ![a, b, c] ∼ ![a', b', c'])
  证明: ⟨h.angle_eq, h.comm_left.comm_right.angle_eq, h.comm_right.comm_left.angle_eq⟩

Depends on / 依赖: angle_eq, comm_left, comm_right, h.angle_eq, h.comm_left.comm_right.angle_eq, h.comm_right.comm_left.angle_eq
-/
theorem _root_.Similar.angle_eq_all (h : ![a, b, c] ∼ ![a', b', c']) :
    ∠ a b c = ∠ a' b' c' ∧ ∠ b c a = ∠ b' c' a' ∧ ∠ c a b = ∠ c' a' b' :=
  ⟨h.angle_eq, h.comm_left.comm_right.angle_eq, h.comm_right.comm_left.angle_eq⟩

end EuclideanGeometry
