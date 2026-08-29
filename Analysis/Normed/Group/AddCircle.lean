/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Topology.Instances.AddCircle.Real -- shake: keep (used in type annotation)

/-!
# The additive circle as a normed group

We define the normed group structure on `AddCircle p`, for `p : ℝ`. For example if `p = 1` then:
`‖(x : AddCircle 1)‖ = |x - round x|` for any `x : ℝ` (see `UnitAddCircle.norm_eq`).

## Main definitions:

* `AddCircle.norm_eq`: a characterisation of the norm on `AddCircle p`

## TODO

* The fact `InnerProductGeometry.angle (Real.cos θ) (Real.sin θ) = ‖(θ : Real.Angle)‖`

-/

public section


noncomputable section

open Metric QuotientAddGroup Set

open Int hiding mem_zmultiples_iff

open AddSubgroup

namespace AddCircle

variable (p : Real)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedAddCommGroup (AddCircle p)
  body: QuotientAddGroup.instNormedAddCommGroup _

@[simp]

中文:
实例 :
  签名: 赋范交换加群 (AddCircle p)
  定义体: QuotientAddGroup.instNormedAddCommGroup _

@[simp]

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.instNormedAddCommGroup, instNormedAddCommGroup
-/
instance : NormedAddCommGroup (AddCircle p) := QuotientAddGroup.instNormedAddCommGroup _

@[simp]
/--
theorem `norm_coe_mul` / 定理 `norm_coe_mul`

English:
theorem norm_coe_mul
  given: (x : Real) (t : Real)
  proof: by
  obtain rfl | ht := eq_or_ne t 0
  · simp
  simp only [norm_eq_infDist, ← Real.norm_eq_abs, ← infDist_smul₀ ht, smul_zero]
  congr 1 with m
  simp_rw [zmultiples, eq_iff_sub_mem, zsmul_eq_mul, mul_left_comm, ← smul_eq_mul, Set.range_smul]
  simp [mem_smul_set_iff_inv_smul_mem₀ ht, mul_sub, ht]

中文:
定理 norm_coe_mul
  条件: (x : 实数) (t : 实数)
  证明: by
  obtain rfl | ht := eq_or_ne t 0
  · simp
  simp only [norm_eq_infDist, ← Real.norm_eq_abs, ← infDist_smul₀ ht, smul_zero]
  congr 1 with m
  simp_rw [zmultiples, eq_iff_sub_mem, zsmul_eq_mul, mul_left_comm, ← smul_eq_mul, Set.range_smul]
  simp [mem_smul_set_iff_inv_smul_mem₀ ht, mul_sub, ht]

Depends on / 依赖: Real.norm_eq_abs, Set.range_smul, eq_iff_sub_mem, eq_or_ne, mul_left_comm, mul_sub, norm_eq_abs, norm_eq_infDist, range_smul, simp_rw, smul_eq_mul, smul_zero, zmultiples, zsmul_eq_mul
-/
theorem norm_coe_mul (x : Real) (t : Real) :
    ‖(↑(t * x) : AddCircle (t * p))‖ = |t| * ‖(x : AddCircle p)‖ := by
  obtain rfl | ht := eq_or_ne t 0
  · simp
  simp only [norm_eq_infDist, ← Real.norm_eq_abs, ← infDist_smul₀ ht, smul_zero]
  congr 1 with m
  simp_rw [zmultiples, eq_iff_sub_mem, zsmul_eq_mul, mul_left_comm, ← smul_eq_mul, Set.range_smul]
  simp [mem_smul_set_iff_inv_smul_mem₀ ht, mul_sub, ht]

/--
theorem `norm_neg_period` / 定理 `norm_neg_period`

English:
theorem norm_neg_period
  given: (x : Real)
  statement: ‖(x : AddCircle (-p))‖ = ‖(x : AddCircle p)‖
  proof: by
  suffices ‖(↑(-1 * x) : AddCircle (-1 * p))‖ = ‖(x : AddCircle p)‖ by
    rw [← this]; rw [neg_one_mul]
    simp
  simp only [norm_coe_mul, abs_neg, abs_one, one_mul]

@[simp]

中文:
定理 norm_neg_period
  条件: (x : 实数)
  结论: ‖(x : AddCircle (-p))‖ = ‖(x : AddCircle p)‖
  证明: by
  suffices ‖(↑(-1 * x) : AddCircle (-1 * p))‖ = ‖(x : AddCircle p)‖ by
    rw [← this]; rw [neg_one_mul]
    simp
  simp only [norm_coe_mul, abs_neg, abs_one, one_mul]

@[simp]

Depends on / 依赖: AddCircle, abs_neg, abs_one, neg_one_mul, norm_coe_mul, one_mul
-/
theorem norm_neg_period (x : Real) : ‖(x : AddCircle (-p))‖ = ‖(x : AddCircle p)‖ := by
  suffices ‖(↑(-1 * x) : AddCircle (-1 * p))‖ = ‖(x : AddCircle p)‖ by
    rw [← this]; rw [neg_one_mul]
    simp
  simp only [norm_coe_mul, abs_neg, abs_one, one_mul]

@[simp]
/--
theorem `norm_eq_of_zero` / 定理 `norm_eq_of_zero`

English:
theorem norm_eq_of_zero
  given: {x : Real}
  statement: ‖(x : AddCircle (0 : Real))‖ = |x|
  proof: by
  suffices { y : Real | (y : AddCircle (0 : Real)) = (x : AddCircle (0 : Real)) } = {x} by
    simp [norm_eq_infDist, this]
  ext y
  simp [eq_iff_sub_mem, sub_eq_zero]

中文:
定理 norm_eq_of_zero
  条件: {x : 实数}
  结论: ‖(x : AddCircle (0 : 实数))‖ = |x|
  证明: by
  suffices { y : Real | (y : AddCircle (0 : Real)) = (x : AddCircle (0 : Real)) } = {x} by
    simp [norm_eq_infDist, this]
  ext y
  simp [eq_iff_sub_mem, sub_eq_zero]

Depends on / 依赖: AddCircle, eq_iff_sub_mem, norm_eq_infDist, sub_eq_zero
-/
theorem norm_eq_of_zero {x : Real} : ‖(x : AddCircle (0 : Real))‖ = |x| := by
  suffices { y : Real | (y : AddCircle (0 : Real)) = (x : AddCircle (0 : Real)) } = {x} by
    simp [norm_eq_infDist, this]
  ext y
  simp [eq_iff_sub_mem, sub_eq_zero]

/--
theorem `norm_eq` / 定理 `norm_eq`

English:
theorem norm_eq
  given: {x : Real}
  statement: ‖(x : AddCircle p)‖ = |x - round (p⁻¹ * x) * p|
  proof: by
  suffices forall x : Real, ‖(x : AddCircle (1 : Real))‖ = |x - round x| by
    rcases eq_or_ne p 0 with (rfl | hp)
    · simp
    have hx := norm_coe_mul p x p⁻¹
    rw [abs_inv]; rw [eq_inv_mul_iff_mul_eq₀ ((not_congr abs_eq_zero).mpr hp)] at hx
    rw [← hx]; rw [inv_mul_cancel₀ hp]; rw [this]; rw [← abs_mul]; rw [mul_sub]; rw [mul_inv_cancel_left₀ hp]; rw [mul_comm p]
  clear! x p
  intro x
  simp only [le_antisymm_iff, le_norm_iff, Real.norm_eq_abs]
  refine ⟨le_of_forall_le fun r hr => ?_, ?_⟩
  · rw [abs_sub_round_eq_min, le_inf_iff]
    rw [le_norm_iff] at hr
    constructor
    · simpa [abs_of_nonneg] using hr (fract x)
    · simpa [abs_sub_comm (fract x)] using hr (fract x - 1) (by simp)
  · simpa [zmultiples, QuotientAddGroup.eq, zsmul_eq_mul, mul_one, mem_mk, mem_range, and_imp,
      forall_exists_index, eq_neg_add_iff_add_eq, ← eq_sub_iff_add_eq, forall_comm (α := Nat)]
      using round_le _

中文:
定理 norm_eq
  条件: {x : 实数}
  结论: ‖(x : AddCircle p)‖ = |x - round (p⁻¹ * x) * p|
  证明: by
  suffices forall x : Real, ‖(x : AddCircle (1 : Real))‖ = |x - round x| by
    rcases eq_or_ne p 0 with (rfl | hp)
    · simp
    have hx := norm_coe_mul p x p⁻¹
    rw [abs_inv]; rw [eq_inv_mul_iff_mul_eq₀ ((not_congr abs_eq_zero).mpr hp)] at hx
    rw [← hx]; rw [inv_mul_cancel₀ hp]; rw [this]; rw [← abs_mul]; rw [mul_sub]; rw [mul_inv_cancel_left₀ hp]; rw [mul_comm p]
  clear! x p
  intro x
  simp only [le_antisymm_iff, le_norm_iff, Real.norm_eq_abs]
  refine ⟨le_of_forall_le fun r hr => ?_, ?_⟩
  · rw [abs_sub_round_eq_min, le_inf_iff]
    rw [le_norm_iff] at hr
    constructor
    · simpa [abs_of_nonneg] using hr (fract x)
    · simpa [abs_sub_comm (fract x)] using hr (fract x - 1) (by simp)
  · simpa [zmultiples, QuotientAddGroup.eq, zsmul_eq_mul, mul_one, mem_mk, mem_range, and_imp,
      forall_exists_index, eq_neg_add_iff_add_eq, ← eq_sub_iff_add_eq, forall_comm (α := Nat)]
      using round_le _

Depends on / 依赖: AddCircle, Real.norm_eq_abs, abs_eq_zero, abs_inv, abs_mul, abs_sub_round_eq, eq_or_ne, le_antisymm_iff, le_norm_iff, le_of_forall_le, mul_comm, mul_sub, norm_coe_mul, norm_eq_abs, not_congr
-/
theorem norm_eq {x : Real} : ‖(x : AddCircle p)‖ = |x - round (p⁻¹ * x) * p| := by
  suffices forall x : Real, ‖(x : AddCircle (1 : Real))‖ = |x - round x| by
    rcases eq_or_ne p 0 with (rfl | hp)
    · simp
    have hx := norm_coe_mul p x p⁻¹
    rw [abs_inv]; rw [eq_inv_mul_iff_mul_eq₀ ((not_congr abs_eq_zero).mpr hp)] at hx
    rw [← hx]; rw [inv_mul_cancel₀ hp]; rw [this]; rw [← abs_mul]; rw [mul_sub]; rw [mul_inv_cancel_left₀ hp]; rw [mul_comm p]
  clear! x p
  intro x
  simp only [le_antisymm_iff, le_norm_iff, Real.norm_eq_abs]
  refine ⟨le_of_forall_le fun r hr => ?_, ?_⟩
  · rw [abs_sub_round_eq_min, le_inf_iff]
    rw [le_norm_iff] at hr
    constructor
    · simpa [abs_of_nonneg] using hr (fract x)
    · simpa [abs_sub_comm (fract x)] using hr (fract x - 1) (by simp)
  · simpa [zmultiples, QuotientAddGroup.eq, zsmul_eq_mul, mul_one, mem_mk, mem_range, and_imp,
      forall_exists_index, eq_neg_add_iff_add_eq, ← eq_sub_iff_add_eq, forall_comm (α := Nat)]
      using round_le _

/--
theorem `norm_eq'` / 定理 `norm_eq'`

English:
theorem norm_eq'
  given: (hp : 0 < p) {x : Real}
  statement: ‖(x : AddCircle p)‖ = p * |p⁻¹ * x - round (p⁻¹ * x)|
  proof: by
  conv_rhs =>
    congr
    rw [← abs_eq_self.mpr hp.le]
  rw [← abs_mul]; rw [mul_sub]; rw [mul_inv_cancel_left₀ hp.ne.symm]; rw [norm_eq]; rw [mul_comm p]

中文:
定理 norm_eq'
  条件: (hp : 0 < p) {x : 实数}
  结论: ‖(x : AddCircle p)‖ = p * |p⁻¹ * x - round (p⁻¹ * x)|
  证明: by
  conv_rhs =>
    congr
    rw [← abs_eq_self.mpr hp.le]
  rw [← abs_mul]; rw [mul_sub]; rw [mul_inv_cancel_left₀ hp.ne.symm]; rw [norm_eq]; rw [mul_comm p]

Depends on / 依赖: abs_eq_self, abs_eq_self.mpr, abs_mul, conv_rhs, hp.le, hp.ne.symm, mul_comm, mul_sub, norm_eq
-/
theorem norm_eq' (hp : 0 < p) {x : Real} : ‖(x : AddCircle p)‖ = p * |p⁻¹ * x - round (p⁻¹ * x)| := by
  conv_rhs =>
    congr
    rw [← abs_eq_self.mpr hp.le]
  rw [← abs_mul]; rw [mul_sub]; rw [mul_inv_cancel_left₀ hp.ne.symm]; rw [norm_eq]; rw [mul_comm p]

/--
theorem `norm_le_half_period` / 定理 `norm_le_half_period`

English:
theorem norm_le_half_period
  given: {x : AddCircle p} (hp : p != 0)
  statement: ‖x‖ <= |p| / 2
  proof: by
  obtain ⟨x⟩ := x
  change ‖(x : AddCircle p)‖ <= |p| / 2
  rw [norm_eq]; rw [← mul_le_mul_iff_right₀ (abs_pos.mpr (inv_ne_zero hp))]; rw [← abs_mul]; rw [mul_sub]; rw [mul_left_comm]; rw [← mul_div_assoc]; rw [← abs_mul]; rw [inv_mul_cancel₀ hp]; rw [mul_one]; rw [abs_one]
  exact abs_sub_round (p⁻¹ * x)

@[simp]

中文:
定理 norm_le_half_period
  条件: {x : AddCircle p} (hp : p != 0)
  结论: ‖x‖ <= |p| / 2
  证明: by
  obtain ⟨x⟩ := x
  change ‖(x : AddCircle p)‖ <= |p| / 2
  rw [norm_eq]; rw [← mul_le_mul_iff_right₀ (abs_pos.mpr (inv_ne_zero hp))]; rw [← abs_mul]; rw [mul_sub]; rw [mul_left_comm]; rw [← mul_div_assoc]; rw [← abs_mul]; rw [inv_mul_cancel₀ hp]; rw [mul_one]; rw [abs_one]
  exact abs_sub_round (p⁻¹ * x)

@[simp]

Depends on / 依赖: AddCircle, abs_mul, abs_one, abs_pos, abs_pos.mpr, abs_sub_round, inv_ne_zero, mul_div_assoc, mul_left_comm, mul_one, mul_sub, norm_eq
-/
theorem norm_le_half_period {x : AddCircle p} (hp : p != 0) : ‖x‖ <= |p| / 2 := by
  obtain ⟨x⟩ := x
  change ‖(x : AddCircle p)‖ <= |p| / 2
  rw [norm_eq]; rw [← mul_le_mul_iff_right₀ (abs_pos.mpr (inv_ne_zero hp))]; rw [← abs_mul]; rw [mul_sub]; rw [mul_left_comm]; rw [← mul_div_assoc]; rw [← abs_mul]; rw [inv_mul_cancel₀ hp]; rw [mul_one]; rw [abs_one]
  exact abs_sub_round (p⁻¹ * x)

@[simp]
/--
theorem `norm_half_period_eq` / 定理 `norm_half_period_eq`

English:
theorem norm_half_period_eq
  statement: ‖(↑(p / 2) : AddCircle p)‖ = |p| / 2
  proof: by
  rcases eq_or_ne p 0 with (rfl | hp); · simp
  rw [norm_eq]; rw [← mul_div_assoc]; rw [inv_mul_cancel₀ hp]; rw [one_div]; rw [round_two_inv]; rw [Int.cast_one]; rw [one_mul]; rw [(by linarith : p / 2 - p = -(p / 2))]; rw [abs_neg]; rw [abs_div]; rw [abs_two]

中文:
定理 norm_half_period_eq
  结论: ‖(↑(p / 2) : AddCircle p)‖ = |p| / 2
  证明: by
  rcases eq_or_ne p 0 with (rfl | hp); · simp
  rw [norm_eq]; rw [← mul_div_assoc]; rw [inv_mul_cancel₀ hp]; rw [one_div]; rw [round_two_inv]; rw [Int.cast_one]; rw [one_mul]; rw [(by linarith : p / 2 - p = -(p / 2))]; rw [abs_neg]; rw [abs_div]; rw [abs_two]

Depends on / 依赖: Int.cast_one, abs_div, abs_neg, abs_two, cast_one, eq_or_ne, mul_div_assoc, norm_eq, one_div, one_mul, round_two_inv
-/
theorem norm_half_period_eq : ‖(↑(p / 2) : AddCircle p)‖ = |p| / 2 := by
  rcases eq_or_ne p 0 with (rfl | hp); · simp
  rw [norm_eq]; rw [← mul_div_assoc]; rw [inv_mul_cancel₀ hp]; rw [one_div]; rw [round_two_inv]; rw [Int.cast_one]; rw [one_mul]; rw [(by linarith : p / 2 - p = -(p / 2))]; rw [abs_neg]; rw [abs_div]; rw [abs_two]

/--
theorem `norm_coe_eq_abs_iff` / 定理 `norm_coe_eq_abs_iff`

English:
theorem norm_coe_eq_abs_iff
  given: {x : Real} (hp : p != 0)
  statement: ‖(x : AddCircle p)‖ = |x| ↔ |x| <= |p| / 2
  proof: by
  refine ⟨fun hx => hx ▸ norm_le_half_period p hp, fun hx => ?_⟩
  suffices forall p : Real, 0 < p -> |x| <= p / 2 -> ‖(x : AddCircle p)‖ = |x| by
    rcases hp.symm.lt_or_gt with (hp | hp)
    · rw [abs_eq_self.mpr hp.le] at hx
      exact this p hp hx
    · rw [← norm_neg_period]
      rw [abs_eq_neg_self.mpr hp.le] at hx
      exact this (-p) (neg_pos.mpr hp) hx
  clear hx
  intro p hp hx
  rcases eq_or_ne x (p / (2 : Real)) with (rfl | hx')
  · simp [abs_div]
  suffices round (p⁻¹ * x) = 0 by simp [norm_eq, this]
  rw [round_eq_zero_iff]
  obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx
  replace hx₂ := Ne.lt_of_le hx' hx₂
  constructor
  · rwa [le_inv_mul_iff₀ hp, mul_neg, ← mul_div_assoc, mul_one]
  · rwa [inv_mul_lt_iff₀ hp, ← mul_div_assoc, mul_one]

中文:
定理 norm_coe_eq_abs_iff
  条件: {x : 实数} (hp : p != 0)
  结论: ‖(x : AddCircle p)‖ = |x| ↔ |x| <= |p| / 2
  证明: by
  refine ⟨fun hx => hx ▸ norm_le_half_period p hp, fun hx => ?_⟩
  suffices forall p : Real, 0 < p -> |x| <= p / 2 -> ‖(x : AddCircle p)‖ = |x| by
    rcases hp.symm.lt_or_gt with (hp | hp)
    · rw [abs_eq_self.mpr hp.le] at hx
      exact this p hp hx
    · rw [← norm_neg_period]
      rw [abs_eq_neg_self.mpr hp.le] at hx
      exact this (-p) (neg_pos.mpr hp) hx
  clear hx
  intro p hp hx
  rcases eq_or_ne x (p / (2 : Real)) with (rfl | hx')
  · simp [abs_div]
  suffices round (p⁻¹ * x) = 0 by simp [norm_eq, this]
  rw [round_eq_zero_iff]
  obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx
  replace hx₂ := Ne.lt_of_le hx' hx₂
  constructor
  · rwa [le_inv_mul_iff₀ hp, mul_neg, ← mul_div_assoc, mul_one]
  · rwa [inv_mul_lt_iff₀ hp, ← mul_div_assoc, mul_one]

Depends on / 依赖: AddCircle, abs_div, abs_eq_neg_self, abs_eq_neg_self.mpr, abs_eq_self, abs_eq_self.mpr, eq_or_ne, hp.le, hp.symm.lt_or_gt, lt_or_gt, neg_pos, neg_pos.mpr, norm_eq, norm_le_half_period, norm_neg_period, round_eq_zero_
-/
theorem norm_coe_eq_abs_iff {x : Real} (hp : p != 0) : ‖(x : AddCircle p)‖ = |x| ↔ |x| <= |p| / 2 := by
  refine ⟨fun hx => hx ▸ norm_le_half_period p hp, fun hx => ?_⟩
  suffices forall p : Real, 0 < p -> |x| <= p / 2 -> ‖(x : AddCircle p)‖ = |x| by
    rcases hp.symm.lt_or_gt with (hp | hp)
    · rw [abs_eq_self.mpr hp.le] at hx
      exact this p hp hx
    · rw [← norm_neg_period]
      rw [abs_eq_neg_self.mpr hp.le] at hx
      exact this (-p) (neg_pos.mpr hp) hx
  clear hx
  intro p hp hx
  rcases eq_or_ne x (p / (2 : Real)) with (rfl | hx')
  · simp [abs_div]
  suffices round (p⁻¹ * x) = 0 by simp [norm_eq, this]
  rw [round_eq_zero_iff]
  obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx
  replace hx₂ := Ne.lt_of_le hx' hx₂
  constructor
  · rwa [le_inv_mul_iff₀ hp, mul_neg, ← mul_div_assoc, mul_one]
  · rwa [inv_mul_lt_iff₀ hp, ← mul_div_assoc, mul_one]

open Metric

/--
theorem `closedBall_eq_univ_of_half_period_le` / 定理 `closedBall_eq_univ_of_half_period_le`

English:
theorem closedBall_eq_univ_of_half_period_le
  statement: (hp : p != 0) (x : AddCircle p) {ε : Real}
  proof: eq_univ_iff_forall.mpr fun x => by
    simpa only [mem_closedBall, dist_eq_norm] using (norm_le_half_period p hp).trans hε

@[simp]

中文:
定理 closedBall_eq_univ_of_half_period_le
  结论: (hp : p != 0) (x : AddCircle p) {ε : 实数}
  证明: eq_univ_iff_forall.mpr fun x => by
    simpa only [mem_closedBall, dist_eq_norm] using (norm_le_half_period p hp).trans hε

@[simp]

Depends on / 依赖: dist_eq_norm, eq_univ_iff_forall, eq_univ_iff_forall.mpr, mem_closedBall, norm_le_half_period
-/
theorem closedBall_eq_univ_of_half_period_le (hp : p != 0) (x : AddCircle p) {ε : Real}
    (hε : |p| / 2 <= ε) : closedBall x ε = univ :=
  eq_univ_iff_forall.mpr fun x => by
    simpa only [mem_closedBall, dist_eq_norm] using (norm_le_half_period p hp).trans hε

@[simp]
/--
theorem `coe_real_preimage_closedBall_period_zero` / 定理 `coe_real_preimage_closedBall_period_zero`

English:
theorem coe_real_preimage_closedBall_period_zero
  given: (x ε : Real)
  proof: by
  ext y
  simp [dist_eq_norm, ← QuotientAddGroup.mk_sub]

中文:
定理 coe_real_preimage_closedBall_period_zero
  条件: (x ε : 实数)
  证明: by
  ext y
  simp [dist_eq_norm, ← QuotientAddGroup.mk_sub]

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.mk_sub, dist_eq_norm, mk_sub
-/
theorem coe_real_preimage_closedBall_period_zero (x ε : Real) :
    (↑) ⁻¹' closedBall (x : AddCircle (0 : Real)) ε = closedBall x ε := by
  ext y
  simp [dist_eq_norm, ← QuotientAddGroup.mk_sub]

/--
theorem `coe_real_preimage_closedBall_eq_iUnion` / 定理 `coe_real_preimage_closedBall_eq_iUnion`

English:
theorem coe_real_preimage_closedBall_eq_iUnion
  given: (x ε : Real)
  proof: by
  rcases eq_or_ne p 0 with (rfl | hp)
  · simp [iUnion_const]
  ext y
  simp only [dist_eq_norm, mem_preimage, mem_closedBall, zsmul_eq_mul, mem_iUnion, Real.norm_eq_abs,
    ← QuotientAddGroup.mk_sub, norm_eq, ← sub_sub]
  refine ⟨fun h => ⟨round (p⁻¹ * (y - x)), h⟩, ?_⟩
  rintro ⟨n, hn⟩
  rw [← mul_le_mul_iff_right₀ (abs_pos.mpr <| inv_ne_zero hp)]; rw [← abs_mul]; rw [mul_sub]; rw [mul_comm _ p]; rw [inv_mul_cancel_left₀ hp] at hn ⊢
  exact (round_le (p⁻¹ * (y - x)) n).trans hn

中文:
定理 coe_real_preimage_closedBall_eq_iUnion
  条件: (x ε : 实数)
  证明: by
  rcases eq_or_ne p 0 with (rfl | hp)
  · simp [iUnion_const]
  ext y
  simp only [dist_eq_norm, mem_preimage, mem_closedBall, zsmul_eq_mul, mem_iUnion, Real.norm_eq_abs,
    ← QuotientAddGroup.mk_sub, norm_eq, ← sub_sub]
  refine ⟨fun h => ⟨round (p⁻¹ * (y - x)), h⟩, ?_⟩
  rintro ⟨n, hn⟩
  rw [← mul_le_mul_iff_right₀ (abs_pos.mpr <| inv_ne_zero hp)]; rw [← abs_mul]; rw [mul_sub]; rw [mul_comm _ p]; rw [inv_mul_cancel_left₀ hp] at hn ⊢
  exact (round_le (p⁻¹ * (y - x)) n).trans hn

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.mk_sub, Real.norm_eq_abs, abs_mul, abs_pos, abs_pos.mpr, dist_eq_norm, eq_or_ne, iUnion_const, inv_ne_zero, mem_closedBall, mem_iUnion, mem_preimage, mk_sub, mul_comm, mul_sub, norm_eq, norm_eq_abs, round_le, sub_sub
-/
theorem coe_real_preimage_closedBall_eq_iUnion (x ε : Real) :
    (↑) ⁻¹' closedBall (x : AddCircle p) ε = ⋃ z : Int, closedBall (x + z • p) ε := by
  rcases eq_or_ne p 0 with (rfl | hp)
  · simp [iUnion_const]
  ext y
  simp only [dist_eq_norm, mem_preimage, mem_closedBall, zsmul_eq_mul, mem_iUnion, Real.norm_eq_abs,
    ← QuotientAddGroup.mk_sub, norm_eq, ← sub_sub]
  refine ⟨fun h => ⟨round (p⁻¹ * (y - x)), h⟩, ?_⟩
  rintro ⟨n, hn⟩
  rw [← mul_le_mul_iff_right₀ (abs_pos.mpr <| inv_ne_zero hp)]; rw [← abs_mul]; rw [mul_sub]; rw [mul_comm _ p]; rw [inv_mul_cancel_left₀ hp] at hn ⊢
  exact (round_le (p⁻¹ * (y - x)) n).trans hn

/--
theorem `coe_real_preimage_closedBall_inter_eq` / 定理 `coe_real_preimage_closedBall_inter_eq`

English:
theorem coe_real_preimage_closedBall_inter_eq
  statement: {x ε : Real} (s : Set Real)
  proof: by
  rcases le_or_gt (|p| / 2) ε with hε | hε
  · rcases eq_or_ne p 0 with (rfl | hp)
    · simp only [abs_zero, zero_div] at hε
      simp only [not_lt.mpr hε, coe_real_preimage_closedBall_period_zero, abs_zero, zero_div,
        if_false, inter_eq_right]
      exact hs.trans (closedBall_subset_closedBall <| by simp [hε])
    simp [closedBall_eq_univ_of_half_period_le p hp (↑x) hε, not_lt.mpr hε]
  · suffices forall z : Int, closedBall (x + z • p) ε inter s = if z = 0 then closedBall x ε inter s else ∅ by
      simp [-zsmul_eq_mul, coe_real_preimage_closedBall_eq_iUnion,
        iUnion_inter, iUnion_ite, this, hε]
    intro z
    simp only [Real.closedBall_eq_Icc] at hs ⊢
    rcases eq_or_ne z 0 with (rfl | hz)
    · simp
    simp only [hz, zsmul_eq_mul, if_false, eq_empty_iff_forall_notMem]
    rintro y ⟨⟨hy₁, hy₂⟩, hy₀⟩
    obtain ⟨hy₃, hy₄⟩ := hs hy₀
    rcases lt_trichotomy 0 p with (hp | (rfl : 0 = p) | hp)
    · rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero Real hz with hz' | hz'
      · have : ↑z * p <= -p := by nlinarith
        linarith [abs_eq_self.mpr hp.le]
      · have : p <= ↑z * p := by nlinarith
        linarith [abs_eq_self.mpr hp.le]
    · simp only [mul_zero, add_zero, abs_zero, zero_div] at hy₁ hy₂ hε
      linarith
    · rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero Real hz with hz' | hz'
      · have : -p <= ↑z * p := by nlinarith
        linarith [abs_eq_neg_self.mpr hp.le]
      · have : ↑z * p <= p := by nlinarith
        linarith [abs_eq_neg_self.mpr hp.le]

中文:
定理 coe_real_preimage_closedBall_inter_eq
  结论: {x ε : 实数} (s : 集合 实数)
  证明: by
  rcases le_or_gt (|p| / 2) ε with hε | hε
  · rcases eq_or_ne p 0 with (rfl | hp)
    · simp only [abs_zero, zero_div] at hε
      simp only [not_lt.mpr hε, coe_real_preimage_closedBall_period_zero, abs_zero, zero_div,
        if_false, inter_eq_right]
      exact hs.trans (closedBall_subset_closedBall <| by simp [hε])
    simp [closedBall_eq_univ_of_half_period_le p hp (↑x) hε, not_lt.mpr hε]
  · suffices forall z : Int, closedBall (x + z • p) ε inter s = if z = 0 then closedBall x ε inter s else ∅ by
      simp [-zsmul_eq_mul, coe_real_preimage_closedBall_eq_iUnion,
        iUnion_inter, iUnion_ite, this, hε]
    intro z
    simp only [Real.closedBall_eq_Icc] at hs ⊢
    rcases eq_or_ne z 0 with (rfl | hz)
    · simp
    simp only [hz, zsmul_eq_mul, if_false, eq_empty_iff_forall_notMem]
    rintro y ⟨⟨hy₁, hy₂⟩, hy₀⟩
    obtain ⟨hy₃, hy₄⟩ := hs hy₀
    rcases lt_trichotomy 0 p with (hp | (rfl : 0 = p) | hp)
    · rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero Real hz with hz' | hz'
      · have : ↑z * p <= -p := by nlinarith
        linarith [abs_eq_self.mpr hp.le]
      · have : p <= ↑z * p := by nlinarith
        linarith [abs_eq_self.mpr hp.le]
    · simp only [mul_zero, add_zero, abs_zero, zero_div] at hy₁ hy₂ hε
      linarith
    · rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero Real hz with hz' | hz'
      · have : -p <= ↑z * p := by nlinarith
        linarith [abs_eq_neg_self.mpr hp.le]
      · have : ↑z * p <= p := by nlinarith
        linarith [abs_eq_neg_self.mpr hp.le]

Depends on / 依赖: abs_zero, closedBall, closedBall_eq_univ_of_half_period_le, closedBall_subset_closedBall, coe_real_preimage_closedBall_period_zero, eq_or_ne, hs.trans, if_false, inter_eq_right, le_or_gt, not_lt, not_lt.mpr, zero_div, zsmul_eq_mul
-/
theorem coe_real_preimage_closedBall_inter_eq {x ε : Real} (s : Set Real)
    (hs : s subseteq closedBall x (|p| / 2)) :
    (↑) ⁻¹' closedBall (x : AddCircle p) ε inter s = if ε < |p| / 2 then closedBall x ε inter s else s := by
  rcases le_or_gt (|p| / 2) ε with hε | hε
  · rcases eq_or_ne p 0 with (rfl | hp)
    · simp only [abs_zero, zero_div] at hε
      simp only [not_lt.mpr hε, coe_real_preimage_closedBall_period_zero, abs_zero, zero_div,
        if_false, inter_eq_right]
      exact hs.trans (closedBall_subset_closedBall <| by simp [hε])
    simp [closedBall_eq_univ_of_half_period_le p hp (↑x) hε, not_lt.mpr hε]
  · suffices forall z : Int, closedBall (x + z • p) ε inter s = if z = 0 then closedBall x ε inter s else ∅ by
      simp [-zsmul_eq_mul, coe_real_preimage_closedBall_eq_iUnion,
        iUnion_inter, iUnion_ite, this, hε]
    intro z
    simp only [Real.closedBall_eq_Icc] at hs ⊢
    rcases eq_or_ne z 0 with (rfl | hz)
    · simp
    simp only [hz, zsmul_eq_mul, if_false, eq_empty_iff_forall_notMem]
    rintro y ⟨⟨hy₁, hy₂⟩, hy₀⟩
    obtain ⟨hy₃, hy₄⟩ := hs hy₀
    rcases lt_trichotomy 0 p with (hp | (rfl : 0 = p) | hp)
    · rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero Real hz with hz' | hz'
      · have : ↑z * p <= -p := by nlinarith
        linarith [abs_eq_self.mpr hp.le]
      · have : p <= ↑z * p := by nlinarith
        linarith [abs_eq_self.mpr hp.le]
    · simp only [mul_zero, add_zero, abs_zero, zero_div] at hy₁ hy₂ hε
      linarith
    · rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero Real hz with hz' | hz'
      · have : -p <= ↑z * p := by nlinarith
        linarith [abs_eq_neg_self.mpr hp.le]
      · have : ↑z * p <= p := by nlinarith
        linarith [abs_eq_neg_self.mpr hp.le]

section FiniteOrderPoints

variable {p} [hp : Fact (0 < p)]

/--
theorem `norm_div_natCast` / 定理 `norm_div_natCast`

English:
theorem norm_div_natCast
  given: {m n : Nat}
  proof: by
  have : p⁻¹ * (↑m / ↑n * p) = ↑m / ↑n := by rw [mul_comm _ p, inv_mul_cancel_left₀ hp.out.ne.symm]
  rw [norm_eq' p hp.out]; rw [this]; rw [abs_sub_round_div_natCast_eq]

中文:
定理 norm_div_natCast
  条件: {m n : 自然数}
  证明: by
  have : p⁻¹ * (↑m / ↑n * p) = ↑m / ↑n := by rw [mul_comm _ p, inv_mul_cancel_left₀ hp.out.ne.symm]
  rw [norm_eq' p hp.out]; rw [this]; rw [abs_sub_round_div_natCast_eq]

Depends on / 依赖: abs_sub_round_div_natCast_eq, hp.out, hp.out.ne.symm, mul_comm, norm_eq
-/
theorem norm_div_natCast {m n : Nat} :
    ‖(↑(↑m / ↑n * p) : AddCircle p)‖ = p * (↑(min (m % n) (n - m % n)) / n) := by
  have : p⁻¹ * (↑m / ↑n * p) = ↑m / ↑n := by rw [mul_comm _ p, inv_mul_cancel_left₀ hp.out.ne.symm]
  rw [norm_eq' p hp.out]; rw [this]; rw [abs_sub_round_div_natCast_eq]

/--
theorem `exists_norm_eq_of_isOfFinAddOrder` / 定理 `exists_norm_eq_of_isOfFinAddOrder`

English:
theorem exists_norm_eq_of_isOfFinAddOrder
  given: {u : AddCircle p} (hu : IsOfFinAddOrder u)
  proof: by
  let n := addOrderOf u
  change exists k : Nat, ‖u‖ = p * (k / n)
  obtain ⟨m, -, -, hm⟩ := exists_gcd_eq_one_of_isOfFinAddOrder hu
  refine ⟨min (m % n) (n - m % n), ?_⟩
  rw [← hm]; rw [norm_div_natCast]

中文:
定理 存在_norm_eq_of_isOfFinAddOrder
  条件: {u : AddCircle p} (hu : IsOfFinAddOrder u)
  证明: by
  let n := addOrderOf u
  change exists k : Nat, ‖u‖ = p * (k / n)
  obtain ⟨m, -, -, hm⟩ := exists_gcd_eq_one_of_isOfFinAddOrder hu
  refine ⟨min (m % n) (n - m % n), ?_⟩
  rw [← hm]; rw [norm_div_natCast]

Depends on / 依赖: addOrderOf, exists_gcd_eq_one_of_isOfFinAddOrder, norm_div_natCast
-/
theorem exists_norm_eq_of_isOfFinAddOrder {u : AddCircle p} (hu : IsOfFinAddOrder u) :
    exists k : Nat, ‖u‖ = p * (k / addOrderOf u) := by
  let n := addOrderOf u
  change exists k : Nat, ‖u‖ = p * (k / n)
  obtain ⟨m, -, -, hm⟩ := exists_gcd_eq_one_of_isOfFinAddOrder hu
  refine ⟨min (m % n) (n - m % n), ?_⟩
  rw [← hm]; rw [norm_div_natCast]

/--
theorem `le_add_order_smul_norm_of_isOfFinAddOrder` / 定理 `le_add_order_smul_norm_of_isOfFinAddOrder`

English:
theorem le_add_order_smul_norm_of_isOfFinAddOrder
  statement: {u : AddCircle p} (hu : IsOfFinAddOrder u)
  proof: by
  obtain ⟨n, hn⟩ := exists_norm_eq_of_isOfFinAddOrder hu
  replace hu : (addOrderOf u : Real) != 0 := by
    norm_cast
    exact (addOrderOf_pos_iff.mpr hu).ne'
  conv_lhs => rw [← mul_one p]
  rw [hn]; rw [nsmul_eq_mul]; rw [← mul_assoc]; rw [mul_comm _ p]; rw [mul_assoc]; rw [mul_div_cancel₀ _ hu]; rw [mul_le_mul_iff_right₀ hp.out]; rw [Nat.one_le_cast]; rw [Nat.one_le_iff_ne_zero]
  contrapose hu'
  simpa only [hu', Nat.cast_zero, zero_div, mul_zero, norm_eq_zero] using hn

中文:
定理 le_add_order_smul_norm_of_isOfFinAddOrder
  结论: {u : AddCircle p} (hu : IsOfFinAddOrder u)
  证明: by
  obtain ⟨n, hn⟩ := exists_norm_eq_of_isOfFinAddOrder hu
  replace hu : (addOrderOf u : Real) != 0 := by
    norm_cast
    exact (addOrderOf_pos_iff.mpr hu).ne'
  conv_lhs => rw [← mul_one p]
  rw [hn]; rw [nsmul_eq_mul]; rw [← mul_assoc]; rw [mul_comm _ p]; rw [mul_assoc]; rw [mul_div_cancel₀ _ hu]; rw [mul_le_mul_iff_right₀ hp.out]; rw [Nat.one_le_cast]; rw [Nat.one_le_iff_ne_zero]
  contrapose hu'
  simpa only [hu', Nat.cast_zero, zero_div, mul_zero, norm_eq_zero] using hn

Depends on / 依赖: Nat.cast_zero, Nat.one_le_cast, Nat.one_le_iff_ne_zero, addOrderOf, addOrderOf_pos_iff, addOrderOf_pos_iff.mpr, cast_zero, contrapose, conv_lhs, exists_norm_eq_of_isOfFinAddOrder, hp.out, mul_assoc, mul_comm, mul_one, mul_zero, norm_eq_zero, nsmul_eq_mul, one_le_cast, one_le_iff_ne_zero, replace
-/
theorem le_add_order_smul_norm_of_isOfFinAddOrder {u : AddCircle p} (hu : IsOfFinAddOrder u)
    (hu' : u != 0) : p <= addOrderOf u • ‖u‖ := by
  obtain ⟨n, hn⟩ := exists_norm_eq_of_isOfFinAddOrder hu
  replace hu : (addOrderOf u : Real) != 0 := by
    norm_cast
    exact (addOrderOf_pos_iff.mpr hu).ne'
  conv_lhs => rw [← mul_one p]
  rw [hn]; rw [nsmul_eq_mul]; rw [← mul_assoc]; rw [mul_comm _ p]; rw [mul_assoc]; rw [mul_div_cancel₀ _ hu]; rw [mul_le_mul_iff_right₀ hp.out]; rw [Nat.one_le_cast]; rw [Nat.one_le_iff_ne_zero]
  contrapose hu'
  simpa only [hu', Nat.cast_zero, zero_div, mul_zero, norm_eq_zero] using hn

end FiniteOrderPoints

end AddCircle

namespace UnitAddCircle

/--
theorem `norm_eq` / 定理 `norm_eq`

English:
theorem norm_eq
  given: {x : Real}
  statement: ‖(x : UnitAddCircle)‖ = |x - round x|
  proof: by simp [AddCircle.norm_eq]

中文:
定理 norm_eq
  条件: {x : 实数}
  结论: ‖(x : UnitAddCircle)‖ = |x - round x|
  证明: by simp [AddCircle.norm_eq]

Depends on / 依赖: AddCircle, AddCircle.norm_eq, norm_eq
-/
theorem norm_eq {x : Real} : ‖(x : UnitAddCircle)‖ = |x - round x| := by simp [AddCircle.norm_eq]

end UnitAddCircle
