/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.StrictConvexSpace

/-!
# Uniformly convex spaces

This file defines uniformly convex spaces, which are real normed vector spaces in which for all
strictly positive `ε`, there exists some strictly positive `δ` such that `ε ≤ ‖x - y‖` implies
`‖x + y‖ ≤ 2 - δ` for all `x` and `y` of norm at most than `1`. This means that the triangle
inequality is strict with a uniform bound, as opposed to strictly convex spaces where the triangle
inequality is strict but not necessarily uniformly (`‖x + y‖ < ‖x‖ + ‖y‖` for all `x` and `y` not in
the same ray).

## Main declarations

`UniformConvexSpace E` means that `E` is a uniformly convex space.

## TODO

* Milman-Pettis
* Hanner's inequalities

## Tags

convex, uniformly convex
-/

public section


open Set Metric

open Convex Pointwise

/--
Definition of `UniformConvexSpace` / `UniformConvexSpace` 的定义

English:
class UniformConvexSpace
  parameters: (E : Type*) [SeminormedAddCommGroup E]
  axioms and operations (1):
    - uniform_convex : forall ⦃ε : Real⦄, 0 < ε -> exists δ, 0 < δ ∧ forall ⦃x : E⦄, ‖x‖ = 1 -> forall ⦃y⦄, ‖y‖ = 1 -> ε <= ‖x - y‖ -> ‖x + y‖ <= 2 - δ

中文:
类 UniformConvex空间
  参数: (E : 类型) [SeminormedAddComm群 E]
  公理与运算 (1 个):
    - uniform_convex : 对任意 ⦃ε : 实数⦄, 0 < ε -> 存在 δ, 0 < δ ∧ 对任意 ⦃x : E⦄, ‖x‖ = 1 -> 对任意 ⦃y⦄, ‖y‖ = 1 -> ε <= ‖x - y‖ -> ‖x + y‖ <= 2 - δ

Depends on / 依赖: LinearMap, LinearMap.proj, induced
-/
class UniformConvexSpace (E : Type*) [SeminormedAddCommGroup E] : Prop where
  uniform_convex : forall ⦃ε : Real⦄,
    0 < ε -> exists δ, 0 < δ ∧ forall ⦃x : E⦄, ‖x‖ = 1 -> forall ⦃y⦄, ‖y‖ = 1 -> ε <= ‖x - y‖ -> ‖x + y‖ <= 2 - δ

variable {E : Type*}

section SeminormedAddCommGroup

variable (E) [SeminormedAddCommGroup E] [UniformConvexSpace E] {ε : Real}

/--
theorem `exists_forall_sphere_dist_add_le_two_sub` / 定理 `exists_forall_sphere_dist_add_le_two_sub`

English:
theorem exists_forall_sphere_dist_add_le_two_sub
  given: (hε : 0 < ε)
  proof: UniformConvexSpace.uniform_convex hε

中文:
定理 存在_对任意_sphere_dist_add_le_two_sub
  条件: (hε : 0 < ε)
  证明: UniformConvexSpace.uniform_convex hε

Depends on / 依赖: LinearMap, LinearMap.fst, LinearMap.snd, UniformConvexSpace, UniformConvexSpace.uniform_convex, induced, uniform_convex
-/
theorem exists_forall_sphere_dist_add_le_two_sub (hε : 0 < ε) :
    exists δ, 0 < δ ∧ forall ⦃x : E⦄, ‖x‖ = 1 -> forall ⦃y⦄, ‖y‖ = 1 -> ε <= ‖x - y‖ -> ‖x + y‖ <= 2 - δ :=
  UniformConvexSpace.uniform_convex hε

variable [NormedSpace Real E]

/--
theorem `exists_forall_closed_ball_dist_add_le_two_sub` / 定理 `exists_forall_closed_ball_dist_add_le_two_sub`

English:
theorem exists_forall_closed_ball_dist_add_le_two_sub
  given: (hε : 0 < ε)
  proof: by
  have hε' : 0 < ε / 3 := div_pos hε zero_lt_three
  obtain ⟨δ, hδ, h⟩ := exists_forall_sphere_dist_add_le_two_sub E hε'
  set δ' := min (1 / 2) (min (ε / 3) <| δ / 3)
refine ⟨δ', lt_min one_half_pos lt_min hε' (div_pos hδ zero_lt_three), fun x hx y hy hxy => ?_⟩
  obtain hx' | hx' := le_or_gt ‖x‖ (1 - δ')
  · rw [← one_add_one_eq_two]
    exact (norm_add_le_of_le hx' hy).trans (sub_add_eq_add_sub _ _ _).le
  obtain hy' | hy' := le_or_gt ‖y‖ (1 - δ')
  · rw [← one_add_one_eq_two]
    exact (norm_add_le_of_le hx hy').trans (add_sub_assoc _ _ _).ge
  have hδ' : 0 < 1 - δ' := sub_pos_of_lt (min_lt_of_left_lt one_half_lt_one)
  have h₁ : forall z : E, 1 - δ' < ‖z‖ -> ‖‖z‖⁻¹ • z‖ = 1 := by
    rintro z hz
    rw [norm_smul_of_nonneg (inv_nonneg.2 <| norm_nonneg _)]; rw [inv_mul_cancel₀ (hδ'.trans hz).ne']
  have h₂ : forall z : E, ‖z‖ <= 1 -> 1 - δ' <= ‖z‖ -> ‖‖z‖⁻¹ • z - z‖ <= δ' := by
    rintro z hz hδz
    nth_rw 3 [← one_smul Real z]
    rwa [← sub_smul,
      norm_smul_of_nonneg (sub_nonneg_of_le <| (one_le_inv₀ (hδ'.trans_le hδz)).2 hz),
      sub_mul, inv_mul_cancel₀ (hδ'.trans_le hδz).ne', one_mul, sub_le_comm]
  set x' := ‖x‖⁻¹ • x
  set y' := ‖y‖⁻¹ • y
  have hxy' : ε / 3 <= ‖x' - y'‖ :=
    calc
      ε / 3 = ε - (ε / 3 + ε / 3) := by ring
      _ <= ‖x - y‖ - (‖x' - x‖ + ‖y' - y‖) := by
        gcongr
· exact (h₂ _ hx hx'.le).trans min_le_of_right_le min_le_left _ _
· exact (h₂ _ hy hy'.le).trans min_le_of_right_le min_le_left _ _
      _ <= _ := by
        have : forall x' y', x - y = x' - y' + (x - x') + (y' - y) := fun _ _ => by abel
        rw [sub_le_iff_le_add]; rw [norm_sub_rev _ x]; rw [← add_assoc]; rw [this]
        exact norm_add₃_le
  calc
    ‖x + y‖ <= ‖x' + y'‖ + ‖x' - x‖ + ‖y' - y‖ := by
      have : forall x' y', x + y = x' + y' + (x - x') + (y - y') := fun _ _ => by abel
      rw [norm_sub_rev]; rw [norm_sub_rev y']; rw [this]
      exact norm_add₃_le
    _ <= 2 - δ + δ' + δ' := by
      gcongr
      exacts [h (h₁ _ hx') (h₁ _ hy') hxy', h₂ _ hx hx'.le, h₂ _ hy hy'.le]
    _ <= 2 - δ' := by
      suffices δ' <= δ / 3 by linarith
exact min_le_of_right_le min_le_right _ _

中文:
定理 存在_对任意_closed_ball_dist_add_le_two_sub
  条件: (hε : 0 < ε)
  证明: by
  have hε' : 0 < ε / 3 := div_pos hε zero_lt_three
  obtain ⟨δ, hδ, h⟩ := exists_forall_sphere_dist_add_le_two_sub E hε'
  set δ' := min (1 / 2) (min (ε / 3) <| δ / 3)
refine ⟨δ', lt_min one_half_pos lt_min hε' (div_pos hδ zero_lt_three), fun x hx y hy hxy => ?_⟩
  obtain hx' | hx' := le_or_gt ‖x‖ (1 - δ')
  · rw [← one_add_one_eq_two]
    exact (norm_add_le_of_le hx' hy).trans (sub_add_eq_add_sub _ _ _).le
  obtain hy' | hy' := le_or_gt ‖y‖ (1 - δ')
  · rw [← one_add_one_eq_two]
    exact (norm_add_le_of_le hx hy').trans (add_sub_assoc _ _ _).ge
  have hδ' : 0 < 1 - δ' := sub_pos_of_lt (min_lt_of_left_lt one_half_lt_one)
  have h₁ : forall z : E, 1 - δ' < ‖z‖ -> ‖‖z‖⁻¹ • z‖ = 1 := by
    rintro z hz
    rw [norm_smul_of_nonneg (inv_nonneg.2 <| norm_nonneg _)]; rw [inv_mul_cancel₀ (hδ'.trans hz).ne']
  have h₂ : forall z : E, ‖z‖ <= 1 -> 1 - δ' <= ‖z‖ -> ‖‖z‖⁻¹ • z - z‖ <= δ' := by
    rintro z hz hδz
    nth_rw 3 [← one_smul Real z]
    rwa [← sub_smul,
      norm_smul_of_nonneg (sub_nonneg_of_le <| (one_le_inv₀ (hδ'.trans_le hδz)).2 hz),
      sub_mul, inv_mul_cancel₀ (hδ'.trans_le hδz).ne', one_mul, sub_le_comm]
  set x' := ‖x‖⁻¹ • x
  set y' := ‖y‖⁻¹ • y
  have hxy' : ε / 3 <= ‖x' - y'‖ :=
    calc
      ε / 3 = ε - (ε / 3 + ε / 3) := by ring
      _ <= ‖x - y‖ - (‖x' - x‖ + ‖y' - y‖) := by
        gcongr
· exact (h₂ _ hx hx'.le).trans min_le_of_right_le min_le_left _ _
· exact (h₂ _ hy hy'.le).trans min_le_of_right_le min_le_left _ _
      _ <= _ := by
        have : forall x' y', x - y = x' - y' + (x - x') + (y' - y) := fun _ _ => by abel
        rw [sub_le_iff_le_add]; rw [norm_sub_rev _ x]; rw [← add_assoc]; rw [this]
        exact norm_add₃_le
  calc
    ‖x + y‖ <= ‖x' + y'‖ + ‖x' - x‖ + ‖y' - y‖ := by
      have : forall x' y', x + y = x' + y' + (x - x') + (y - y') := fun _ _ => by abel
      rw [norm_sub_rev]; rw [norm_sub_rev y']; rw [this]
      exact norm_add₃_le
    _ <= 2 - δ + δ' + δ' := by
      gcongr
      exacts [h (h₁ _ hx') (h₁ _ hy') hxy', h₂ _ hx hx'.le, h₂ _ hy hy'.le]
    _ <= 2 - δ' := by
      suffices δ' <= δ / 3 by linarith
exact min_le_of_right_le min_le_right _ _

Depends on / 依赖: div_pos, exists_forall_sphere_dist_add_le_two_sub, le_or_gt, lt_min, norm_add_le_of_le, one_add_one_eq_two, one_half_pos, sub_add_eq_add_sub, zero_lt_three
-/
theorem exists_forall_closed_ball_dist_add_le_two_sub (hε : 0 < ε) :
    exists δ, 0 < δ ∧ forall ⦃x : E⦄, ‖x‖ <= 1 -> forall ⦃y⦄, ‖y‖ <= 1 -> ε <= ‖x - y‖ -> ‖x + y‖ <= 2 - δ := by
  have hε' : 0 < ε / 3 := div_pos hε zero_lt_three
  obtain ⟨δ, hδ, h⟩ := exists_forall_sphere_dist_add_le_two_sub E hε'
  set δ' := min (1 / 2) (min (ε / 3) <| δ / 3)
refine ⟨δ', lt_min one_half_pos lt_min hε' (div_pos hδ zero_lt_three), fun x hx y hy hxy => ?_⟩
  obtain hx' | hx' := le_or_gt ‖x‖ (1 - δ')
  · rw [← one_add_one_eq_two]
    exact (norm_add_le_of_le hx' hy).trans (sub_add_eq_add_sub _ _ _).le
  obtain hy' | hy' := le_or_gt ‖y‖ (1 - δ')
  · rw [← one_add_one_eq_two]
    exact (norm_add_le_of_le hx hy').trans (add_sub_assoc _ _ _).ge
  have hδ' : 0 < 1 - δ' := sub_pos_of_lt (min_lt_of_left_lt one_half_lt_one)
  have h₁ : forall z : E, 1 - δ' < ‖z‖ -> ‖‖z‖⁻¹ • z‖ = 1 := by
    rintro z hz
    rw [norm_smul_of_nonneg (inv_nonneg.2 <| norm_nonneg _)]; rw [inv_mul_cancel₀ (hδ'.trans hz).ne']
  have h₂ : forall z : E, ‖z‖ <= 1 -> 1 - δ' <= ‖z‖ -> ‖‖z‖⁻¹ • z - z‖ <= δ' := by
    rintro z hz hδz
    nth_rw 3 [← one_smul Real z]
    rwa [← sub_smul,
      norm_smul_of_nonneg (sub_nonneg_of_le <| (one_le_inv₀ (hδ'.trans_le hδz)).2 hz),
      sub_mul, inv_mul_cancel₀ (hδ'.trans_le hδz).ne', one_mul, sub_le_comm]
  set x' := ‖x‖⁻¹ • x
  set y' := ‖y‖⁻¹ • y
  have hxy' : ε / 3 <= ‖x' - y'‖ :=
    calc
      ε / 3 = ε - (ε / 3 + ε / 3) := by ring
      _ <= ‖x - y‖ - (‖x' - x‖ + ‖y' - y‖) := by
        gcongr
· exact (h₂ _ hx hx'.le).trans min_le_of_right_le min_le_left _ _
· exact (h₂ _ hy hy'.le).trans min_le_of_right_le min_le_left _ _
      _ <= _ := by
        have : forall x' y', x - y = x' - y' + (x - x') + (y' - y) := fun _ _ => by abel
        rw [sub_le_iff_le_add]; rw [norm_sub_rev _ x]; rw [← add_assoc]; rw [this]
        exact norm_add₃_le
  calc
    ‖x + y‖ <= ‖x' + y'‖ + ‖x' - x‖ + ‖y' - y‖ := by
      have : forall x' y', x + y = x' + y' + (x - x') + (y - y') := fun _ _ => by abel
      rw [norm_sub_rev]; rw [norm_sub_rev y']; rw [this]
      exact norm_add₃_le
    _ <= 2 - δ + δ' + δ' := by
      gcongr
      exacts [h (h₁ _ hx') (h₁ _ hy') hxy', h₂ _ hx hx'.le, h₂ _ hy hy'.le]
    _ <= 2 - δ' := by
      suffices δ' <= δ / 3 by linarith
exact min_le_of_right_le min_le_right _ _

/--
theorem `exists_forall_closed_ball_dist_add_le_two_mul_sub` / 定理 `exists_forall_closed_ball_dist_add_le_two_mul_sub`

English:
theorem exists_forall_closed_ball_dist_add_le_two_mul_sub
  given: (hε : 0 < ε) (r : Real)
  proof: by
  obtain hr | hr := le_or_gt r 0
  · exact ⟨1, one_pos, fun x hx y hy h => (hε.not_ge <|
h.trans (norm_sub_le _ _).trans add_nonpos (hx.trans hr) (hy.trans hr)).elim⟩
  obtain ⟨δ, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (div_pos hε hr)
  refine ⟨δ * r, mul_pos hδ hr, fun x hx y hy hxy => ?_⟩
  rw [← div_le_one hr]; rw [div_eq_inv_mul]; rw [← norm_smul_of_nonneg (inv_nonneg.2 hr.le)] at hx hy
  have := h hx hy
  simp_rw [← smul_add, ← smul_sub, norm_smul_of_nonneg (inv_nonneg.2 hr.le), ← div_eq_inv_mul,
    div_le_div_iff_of_pos_right hr, div_le_iff₀ hr, sub_mul] at this
  exact this hxy

中文:
定理 存在_对任意_closed_ball_dist_add_le_two_mul_sub
  条件: (hε : 0 < ε) (r : 实数)
  证明: by
  obtain hr | hr := le_or_gt r 0
  · exact ⟨1, one_pos, fun x hx y hy h => (hε.not_ge <|
h.trans (norm_sub_le _ _).trans add_nonpos (hx.trans hr) (hy.trans hr)).elim⟩
  obtain ⟨δ, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (div_pos hε hr)
  refine ⟨δ * r, mul_pos hδ hr, fun x hx y hy hxy => ?_⟩
  rw [← div_le_one hr]; rw [div_eq_inv_mul]; rw [← norm_smul_of_nonneg (inv_nonneg.2 hr.le)] at hx hy
  have := h hx hy
  simp_rw [← smul_add, ← smul_sub, norm_smul_of_nonneg (inv_nonneg.2 hr.le), ← div_eq_inv_mul,
    div_le_div_iff_of_pos_right hr, div_le_iff₀ hr, sub_mul] at this
  exact this hxy

Depends on / 依赖: add_nonpos, div_eq_inv_mul, div_le_one, div_pos, exists_forall_closed_ball_dist_add_le_two_sub, h.trans, hr.le, hx.trans, hy.trans, inv_nonneg, le_or_gt, mul_pos, norm_smul_of_nonneg, norm_sub_le, not_ge, one_pos, simp_rw, smul_add, smul_sub
-/
theorem exists_forall_closed_ball_dist_add_le_two_mul_sub (hε : 0 < ε) (r : Real) :
    exists δ, 0 < δ ∧ forall ⦃x : E⦄, ‖x‖ <= r -> forall ⦃y⦄, ‖y‖ <= r -> ε <= ‖x - y‖ -> ‖x + y‖ <= 2 * r - δ := by
  obtain hr | hr := le_or_gt r 0
  · exact ⟨1, one_pos, fun x hx y hy h => (hε.not_ge <|
h.trans (norm_sub_le _ _).trans add_nonpos (hx.trans hr) (hy.trans hr)).elim⟩
  obtain ⟨δ, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (div_pos hε hr)
  refine ⟨δ * r, mul_pos hδ hr, fun x hx y hy hxy => ?_⟩
  rw [← div_le_one hr]; rw [div_eq_inv_mul]; rw [← norm_smul_of_nonneg (inv_nonneg.2 hr.le)] at hx hy
  have := h hx hy
  simp_rw [← smul_add, ← smul_sub, norm_smul_of_nonneg (inv_nonneg.2 hr.le), ← div_eq_inv_mul,
    div_le_div_iff_of_pos_right hr, div_le_iff₀ hr, sub_mul] at this
  exact this hxy

end SeminormedAddCommGroup

variable [NormedAddCommGroup E] [NormedSpace Real E] [UniformConvexSpace E]

-- See note [lower instance priority]
instance (priority := 100) UniformConvexSpace.toStrictConvexSpace : StrictConvexSpace Real E :=
  StrictConvexSpace.of_norm_add_ne_two fun _ _ hx hy hxy =>
    let ⟨_, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (norm_sub_pos_iff.2 hxy)
    ((h hx.le hy.le le_rfl).trans_lt <| sub_lt_self _ hδ).ne
