/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Normed spaces over R or C

This file is about results on normed spaces over the fields `ℝ` and `ℂ`.

## Main definitions

None.

## Main theorems

* `ContinuousLinearMap.opNorm_bound_of_ball_bound`: A bound on the norms of values of a linear
  map in a ball yields a bound on the operator norm.

## Notes

This file exists mainly to avoid importing `RCLike` in the main normed space theory files.
-/

public section


open Metric

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]

/--
theorem `RCLike.norm_coe_norm` / 定理 `RCLike.norm_coe_norm`

English:
theorem RCLike.norm_coe_norm
  given: {z : E}
  statement: ‖(‖z‖ : 𝕜)‖ = ‖z‖
  proof: by simp

中文:
定理 RCLike.norm_coe_norm
  条件: {z : E}
  结论: ‖(‖z‖ : 𝕜)‖ = ‖z‖
  证明: by simp
-/
theorem RCLike.norm_coe_norm {z : E} : ‖(‖z‖ : 𝕜)‖ = ‖z‖ := by simp

variable [NormedSpace 𝕜 E]

/-- Lemma to normalize a vector in a normed space `E` over either `ℂ` or `ℝ` to unit length. -/
@[simp]
/--
theorem `norm_smul_inv_norm` / 定理 `norm_smul_inv_norm`

English:
theorem norm_smul_inv_norm
  given: {x : E} (hx : x != 0)
  statement: ‖(‖x‖⁻¹ : 𝕜) • x‖ = 1
  proof: by
  have : ‖x‖ != 0 := by simp [hx]
  simp [field, norm_smul]

中文:
定理 norm_smul_inv_norm
  条件: {x : E} (hx : x != 0)
  结论: ‖(‖x‖⁻¹ : 𝕜) • x‖ = 1
  证明: by
  have : ‖x‖ != 0 := by simp [hx]
  simp [field, norm_smul]

Depends on / 依赖: norm_smul
-/
theorem norm_smul_inv_norm {x : E} (hx : x != 0) : ‖(‖x‖⁻¹ : 𝕜) • x‖ = 1 := by
  have : ‖x‖ != 0 := by simp [hx]
  simp [field, norm_smul]

/--
theorem `norm_smul_inv_norm'` / 定理 `norm_smul_inv_norm'`

English:
theorem norm_smul_inv_norm'
  given: {r : Real} (r_nonneg : 0 <= r) {x : E} (hx : x != 0)
  proof: by
  have : ‖x‖ != 0 := by simp [hx]
  simp [field, norm_smul, r_nonneg, rclike_simps]

中文:
定理 norm_smul_inv_norm'
  条件: {r : 实数} (r_nonneg : 0 <= r) {x : E} (hx : x != 0)
  证明: by
  have : ‖x‖ != 0 := by simp [hx]
  simp [field, norm_smul, r_nonneg, rclike_simps]

Depends on / 依赖: norm_smul, r_nonneg, rclike_simps
-/
theorem norm_smul_inv_norm' {r : Real} (r_nonneg : 0 <= r) {x : E} (hx : x != 0) :
    ‖((r : 𝕜) * (‖x‖ : 𝕜)⁻¹) • x‖ = r := by
  have : ‖x‖ != 0 := by simp [hx]
  simp [field, norm_smul, r_nonneg, rclike_simps]

/--
theorem `ContinuousLinearEquiv.coord_norm'` / 定理 `ContinuousLinearEquiv.coord_norm'`

English:
theorem ContinuousLinearEquiv.coord_norm'
  given: {x : E} (h : x != 0)
  proof: by
  simp only [norm_smul, RCLike.norm_coe_norm, coord_norm, mul_inv_cancel₀ (mt norm_eq_zero.mp h)]

@[deprecated (since := "2026-02-01")] alias coord_norm' := ContinuousLinearEquiv.coord_norm'

中文:
定理 ContinuousLinearEquiv.coord_norm'
  条件: {x : E} (h : x != 0)
  证明: by
  simp only [norm_smul, RCLike.norm_coe_norm, coord_norm, mul_inv_cancel₀ (mt norm_eq_zero.mp h)]

@[deprecated (since := "2026-02-01")] alias coord_norm' := ContinuousLinearEquiv.coord_norm'

Depends on / 依赖: RCLike, RCLike.norm_coe_norm, coord_norm, norm_coe_norm, norm_eq_zero, norm_eq_zero.mp, norm_smul
-/
theorem ContinuousLinearEquiv.coord_norm' {x : E} (h : x != 0) :
    ‖(‖x‖ : 𝕜) • ContinuousLinearEquiv.coord 𝕜 x h‖ = 1 := by
  simp only [norm_smul, RCLike.norm_coe_norm, coord_norm, mul_inv_cancel₀ (mt norm_eq_zero.mp h)]

@[deprecated (since := "2026-02-01")] alias coord_norm' := ContinuousLinearEquiv.coord_norm'

/--
theorem `LinearMap.bound_of_sphere_bound` / 定理 `LinearMap.bound_of_sphere_bound`

English:
theorem LinearMap.bound_of_sphere_bound
  statement: {r : Real} (r_pos : 0 < r) (c : Real) (f : E ->ₗ[𝕜] 𝕜)
  proof: by
  by_cases z_zero : z = 0
  · rw [z_zero]
    simp only [map_zero, norm_zero, mul_zero]
    exact le_rfl
  set z₁ := ((r : 𝕜) * (‖z‖ : 𝕜)⁻¹) • z with hz₁
  have norm_f_z₁ : ‖f z₁‖ <= c := by
    apply h
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm' r_pos.le z_zero
  have r_ne_ze

中文:
定理 LinearMap.bound_of_sphere_bound
  结论: {r : 实数} (r_pos : 0 < r) (c : 实数) (f : E ->ₗ[𝕜] 𝕜)
  证明: by
  by_cases z_zero : z = 0
  · rw [z_zero]
    simp only [map_zero, norm_zero, mul_zero]
    exact le_rfl
  set z₁ := ((r : 𝕜) * (‖z‖ : 𝕜)⁻¹) • z with hz₁
  have norm_f_z₁ : ‖f z₁‖ <= c := by
    apply h
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm' r_pos.le z_zero
  have r_ne_ze

Depends on / 依赖: RCLike, RCLike.ofReal_ne_zero.mpr, le_rfl, map_smul, map_zero, mem_sphere_zero_iff_norm, mul_assoc, mul_zero, norm_smul_inv_norm, norm_zero, ofReal_ne_zero, r_ne_zero, r_pos, r_pos.le, r_pos.ne, smul_eq_mul, z_zero
-/
theorem LinearMap.bound_of_sphere_bound {r : Real} (r_pos : 0 < r) (c : Real) (f : E ->ₗ[𝕜] 𝕜)
    (h : forall z in sphere (0 : E) r, ‖f z‖ <= c) (z : E) : ‖f z‖ <= c / r * ‖z‖ := by
  by_cases z_zero : z = 0
  · rw [z_zero]
    simp only [map_zero, norm_zero, mul_zero]
    exact le_rfl
  set z₁ := ((r : 𝕜) * (‖z‖ : 𝕜)⁻¹) • z with hz₁
  have norm_f_z₁ : ‖f z₁‖ <= c := by
    apply h
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm' r_pos.le z_zero
  have r_ne_zero : (r : 𝕜) != 0 := RCLike.ofReal_ne_zero.mpr r_pos.ne'
  have eq : f z = ‖z‖ / r * f z₁ := by
    rw [hz₁]; rw [map_smul]; rw [smul_eq_mul]
    rw [← mul_assoc]; rw [← mul_assoc]; rw [div_mul_cancel₀ _ r_ne_zero]; rw [mul_inv_cancel₀]; rw [one_mul]
    simp only [z_zero, RCLike.ofReal_eq_zero, norm_eq_zero, Ne, not_false_iff]
  rw [eq]; rw [norm_mul]; rw [norm_div]; rw [RCLike.norm_coe_norm]; rw [RCLike.norm_of_nonneg r_pos.le]; rw [div_mul_eq_mul_div]; rw [div_mul_eq_mul_div]; rw [mul_comm]
  apply div_le_div₀ _ _ r_pos rfl.ge
  · exact mul_nonneg ((norm_nonneg _).trans norm_f_z₁) (norm_nonneg z)
  apply mul_le_mul norm_f_z₁ rfl.le (norm_nonneg z) ((norm_nonneg _).trans norm_f_z₁)

/--
theorem `LinearMap.bound_of_ball_bound'` / 定理 `LinearMap.bound_of_ball_bound'`

English:
theorem LinearMap.bound_of_ball_bound'
  statement: {r : Real} (r_pos : 0 < r) (c : Real) (f : E ->ₗ[𝕜] 𝕜)
  proof: f.bound_of_sphere_bound r_pos c (fun z hz => h z hz.le) z

中文:
定理 LinearMap.bound_of_ball_bound'
  结论: {r : 实数} (r_pos : 0 < r) (c : 实数) (f : E ->ₗ[𝕜] 𝕜)
  证明: f.bound_of_sphere_bound r_pos c (fun z hz => h z hz.le) z

Depends on / 依赖: bound_of_sphere_bound, f.bound_of_sphere_bound, hz.le, r_pos
-/
theorem LinearMap.bound_of_ball_bound' {r : Real} (r_pos : 0 < r) (c : Real) (f : E ->ₗ[𝕜] 𝕜)
    (h : forall z in closedBall (0 : E) r, ‖f z‖ <= c) (z : E) : ‖f z‖ <= c / r * ‖z‖ :=
  f.bound_of_sphere_bound r_pos c (fun z hz => h z hz.le) z

/--
theorem `ContinuousLinearMap.opNorm_bound_of_ball_bound` / 定理 `ContinuousLinearMap.opNorm_bound_of_ball_bound`

English:
theorem ContinuousLinearMap.opNorm_bound_of_ball_bound
  statement: {r : Real} (r_pos : 0 < r) (c : Real)
  proof: by
  apply ContinuousLinearMap.opNorm_le_bound
  · apply div_nonneg _ r_pos.le
    exact
      (norm_nonneg _).trans
        (h 0 (by simp only [norm_zero, mem_closedBall, dist_zero_left, r_pos.le]))
  apply LinearMap.bound_of_ball_bound' r_pos
  exact fun z hz => h z hz

中文:
定理 ContinuousLinearMap.opNorm_bound_of_ball_bound
  结论: {r : 实数} (r_pos : 0 < r) (c : 实数)
  证明: by
  apply ContinuousLinearMap.opNorm_le_bound
  · apply div_nonneg _ r_pos.le
    exact
      (norm_nonneg _).trans
        (h 0 (by simp only [norm_zero, mem_closedBall, dist_zero_left, r_pos.le]))
  apply LinearMap.bound_of_ball_bound' r_pos
  exact fun z hz => h z hz

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_le_bound, LinearMap, LinearMap.bound_of_ball_bound, bound_of_ball_bound, dist_zero_left, div_nonneg, mem_closedBall, norm_nonneg, norm_zero, opNorm_le_bound, r_pos, r_pos.le
-/
theorem ContinuousLinearMap.opNorm_bound_of_ball_bound {r : Real} (r_pos : 0 < r) (c : Real)
    (f : StrongDual 𝕜 E) (h : forall z in closedBall (0 : E) r, ‖f z‖ <= c) : ‖f‖ <= c / r := by
  apply ContinuousLinearMap.opNorm_le_bound
  · apply div_nonneg _ r_pos.le
    exact
      (norm_nonneg _).trans
        (h 0 (by simp only [norm_zero, mem_closedBall, dist_zero_left, r_pos.le]))
  apply LinearMap.bound_of_ball_bound' r_pos
  exact fun z hz => h z hz

/--
lemma `antilipschitz_of_bound_of_norm_one` / 引理 `antilipschitz_of_bound_of_norm_one`

English:
lemma antilipschitz_of_bound_of_norm_one
  statement: {𝓕 E F : Type*}
  proof: AddMonoidHomClass.antilipschitz_of_bound f fun x => by
    obtain rfl | hx := eq_or_ne x 0
    · simp
    simpa [norm_smul, field] using h ((‖x‖⁻¹ : 𝕜) • x) (norm_smul_inv_norm hx)

中文:
引理 antilipschitz_of_bound_of_norm_one
  结论: {𝓕 E F : 类型}
  证明: AddMonoidHomClass.antilipschitz_of_bound f fun x => by
    obtain rfl | hx := eq_or_ne x 0
    · simp
    simpa [norm_smul, field] using h ((‖x‖⁻¹ : 𝕜) • x) (norm_smul_inv_norm hx)

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.antilipschitz_of_bound, antilipschitz_of_bound, eq_or_ne, norm_smul, norm_smul_inv_norm
-/
lemma antilipschitz_of_bound_of_norm_one {𝓕 E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [FunLike 𝓕 E F] [AddMonoidHomClass 𝓕 E F] [MulActionHomClass 𝓕 𝕜 E F]
    (f : 𝓕) {K : NNReal} (h : forall x, ‖x‖ = 1 -> 1 <= K * ‖f x‖) :
    AntilipschitzWith K f :=
  AddMonoidHomClass.antilipschitz_of_bound f fun x => by
    obtain rfl | hx := eq_or_ne x 0
    · simp
    simpa [norm_smul, field] using h ((‖x‖⁻¹ : 𝕜) • x) (norm_smul_inv_norm hx)

variable (𝕜)
include 𝕜 in
/--
theorem `NormedSpace.sphere_nonempty_rclike` / 定理 `NormedSpace.sphere_nonempty_rclike`

English:
theorem NormedSpace.sphere_nonempty_rclike
  given: [Nontrivial E] {r : Real} (hr : 0 <= r)
  proof: letI : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  (NormedSpace.sphere_nonempty.mpr hr).coe_sort

中文:
定理 NormedSpace.sphere_nonempty_rclike
  条件: [Nontrivial E] {r : 实数} (hr : 0 <= r)
  证明: letI : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  (NormedSpace.sphere_nonempty.mpr hr).coe_sort

Depends on / 依赖: NormedSpace, NormedSpace.restrictScalars, NormedSpace.sphere_nonempty.mpr, coe_sort, restrictScalars, sphere_nonempty
-/
theorem NormedSpace.sphere_nonempty_rclike [Nontrivial E] {r : Real} (hr : 0 <= r) :
    Nonempty (sphere (0 : E) r) :=
  letI : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  (NormedSpace.sphere_nonempty.mpr hr).coe_sort
