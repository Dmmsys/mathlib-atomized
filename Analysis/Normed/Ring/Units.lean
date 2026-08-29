/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.RingTheory.Ideal.Nonunits

/-!
# The group of units of a complete normed ring

This file contains the basic theory for the group of units (invertible elements) of a complete
normed ring (Banach algebras being a notable special case).

## Main results

The constructions `Units.add` and `Units.ofNearby` (based on `Units.oneSub` defined elsewhere)
state, in varying forms, that perturbations of a unit are units. They are not stated
in their optimal form; more precise versions would use the spectral radius.

The first main result is `Units.isOpen`: the group of units of a normed ring with summable
geometric series is an open subset of the ring.

The function `Ring.inverse` (defined elsewhere), for a ring `R`, sends `a : R` to `a⁻¹` if `a` is a
unit and `0` if not. The other major results of this file (notably `NormedRing.inverse_add`,
`NormedRing.inverse_add_norm` and `NormedRing.inverse_add_norm_diff_nth_order`) cover the asymptotic
properties of `Ring.inverse (x + t)` as `t → 0`.
-/

@[expose] public section

noncomputable section

open Topology
open scoped Ring

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

namespace Units

/-- In a normed ring with summable geometric series, a perturbation of a unit `x` by an
element `t` of distance less than `‖x⁻¹‖⁻¹` from `x` is a unit.
Here we construct its `Units` structure. -/
@[simps! val]
/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹)
  body: Units.copy -- to make `add_val` true definitionally, for convenience
    (x * Units.oneSub (-((x⁻¹).1 * t)) (by
      nontriviality R using zero_lt_one
      have hpos : 0 < ‖(↑x⁻¹ : R)‖ := Units.norm_pos x⁻¹
      calc
        ‖-(↑x⁻¹ * t)‖ = ‖↑x⁻¹ * t‖ := by rw [norm_neg]
        _ <= ‖(↑x⁻¹ : R)‖

中文:
定义 add
  签名: (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹)
  定义体: Units.copy -- to make `add_val` true definitionally, for convenience
    (x * Units.oneSub (-((x⁻¹).1 * t)) (by
      nontriviality R using zero_lt_one
      have hpos : 0 < ‖(↑x⁻¹ : R)‖ := Units.norm_pos x⁻¹
      calc
        ‖-(↑x⁻¹ * t)‖ = ‖↑x⁻¹ * t‖ := by rw [norm_neg]
        _ <= ‖(↑x⁻¹ : R)‖

Depends on / 依赖: Units.copy, Units.norm_pos, Units.oneSub, add_val, convenience, definitionally, mul_add, ne_of_gt, nontriviality, norm_mul_le, norm_neg, norm_pos, oneSub, zero_lt_one
-/
def add (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) : Rˣ :=
  Units.copy -- to make `add_val` true definitionally, for convenience
    (x * Units.oneSub (-((x⁻¹).1 * t)) (by
      nontriviality R using zero_lt_one
      have hpos : 0 < ‖(↑x⁻¹ : R)‖ := Units.norm_pos x⁻¹
      calc
        ‖-(↑x⁻¹ * t)‖ = ‖↑x⁻¹ * t‖ := by rw [norm_neg]
        _ <= ‖(↑x⁻¹ : R)‖ * ‖t‖ := norm_mul_le (x⁻¹).1 _
        _ < ‖(↑x⁻¹ : R)‖ * ‖(↑x⁻¹ : R)‖⁻¹ := by nlinarith only [h, hpos]
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)))
    (x + t) (by simp [mul_add]) _ rfl

/-- In a normed ring with summable geometric series, an element `y` of distance less
than `‖x⁻¹‖⁻¹` from `x` is a unit. Here we construct its `Units` structure. -/
@[simps! val]
/--
Definition of `ofNearby` / `ofNearby` 的定义

English:
definition ofNearby
  signature: (x : Rˣ) (y : R) (h : ‖y - x‖ < ‖(↑x⁻¹ : R)‖⁻¹)
  body: (x.add (y - x : R) h).copy y (by simp) _ rfl

中文:
定义 ofNearby
  签名: (x : Rˣ) (y : R) (h : ‖y - x‖ < ‖(↑x⁻¹ : R)‖⁻¹)
  定义体: (x.add (y - x : R) h).copy y (by simp) _ rfl

Depends on / 依赖: x.add
-/
def ofNearby (x : Rˣ) (y : R) (h : ‖y - x‖ < ‖(↑x⁻¹ : R)‖⁻¹) : Rˣ :=
  (x.add (y - x : R) h).copy y (by simp) _ rfl

/--
theorem `isOpen` / 定理 `isOpen`

English:
theorem isOpen
  statement: IsOpen { x : R | IsUnit x }
  proof: by
  nontriviality R
  rw [Metric.isOpen_iff]
  rintro _ ⟨x, rfl⟩
  refine ⟨‖(↑x⁻¹ : R)‖⁻¹, _root_.inv_pos.mpr (Units.norm_pos x⁻¹), fun y hy => ?_⟩
  rw [mem_ball_iff_norm] at hy
  exact (x.ofNearby y hy).isUnit

中文:
定理 isOpen
  结论: IsOpen { x : R | IsUnit x }
  证明: by
  nontriviality R
  rw [Metric.isOpen_iff]
  rintro _ ⟨x, rfl⟩
  refine ⟨‖(↑x⁻¹ : R)‖⁻¹, _root_.inv_pos.mpr (Units.norm_pos x⁻¹), fun y hy => ?_⟩
  rw [mem_ball_iff_norm] at hy
  exact (x.ofNearby y hy).isUnit
-/
protected theorem isOpen : IsOpen { x : R | IsUnit x } := by
  nontriviality R
  rw [Metric.isOpen_iff]
  rintro _ ⟨x, rfl⟩
  refine ⟨‖(↑x⁻¹ : R)‖⁻¹, _root_.inv_pos.mpr (Units.norm_pos x⁻¹), fun y hy => ?_⟩
  rw [mem_ball_iff_norm] at hy
  exact (x.ofNearby y hy).isUnit

/--
theorem `nhds` / 定理 `nhds`

English:
theorem nhds
  given: (x : Rˣ)
  statement: { x : R | IsUnit x } in 𝓝 (x : R)
  proof: IsOpen.mem_nhds Units.isOpen x.isUnit

中文:
定理 nhds
  条件: (x : Rˣ)
  结论: { x : R | IsUnit x } in 𝓝 (x : R)
  证明: IsOpen.mem_nhds Units.isOpen x.isUnit
-/
protected theorem nhds (x : Rˣ) : { x : R | IsUnit x } in 𝓝 (x : R) :=
  IsOpen.mem_nhds Units.isOpen x.isUnit

end Units

namespace nonunits

/--
theorem `subset_compl_ball` / 定理 `subset_compl_ball`

English:
theorem subset_compl_ball
  statement: nonunits R subseteq (Metric.ball (1 : R) 1)ᶜ
  proof: fun x hx h₁ => hx
  sub_sub_self 1 x ▸ (Units.oneSub (1 - x) (by rwa [mem_ball_iff_norm'] at h₁)).isUnit

中文:
定理 subset_compl_ball
  结论: nonunits R subseteq (Metric.ball (1 : R) 1)ᶜ
  证明: fun x hx h₁ => hx
  sub_sub_self 1 x ▸ (Units.oneSub (1 - x) (by rwa [mem_ball_iff_norm'] at h₁)).isUnit
-/
theorem subset_compl_ball : nonunits R subseteq (Metric.ball (1 : R) 1)ᶜ := fun x hx h₁ => hx
  sub_sub_self 1 x ▸ (Units.oneSub (1 - x) (by rwa [mem_ball_iff_norm'] at h₁)).isUnit

-- The `nonunits` in a normed ring with summable geometric series are a closed set
/--
theorem `isClosed` / 定理 `isClosed`

English:
theorem isClosed
  statement: IsClosed (nonunits R)
  proof: Units.isOpen.isClosed_compl

中文:
定理 isClosed
  结论: IsClosed (nonunits R)
  证明: Units.isOpen.isClosed_compl
-/
protected theorem isClosed : IsClosed (nonunits R) :=
  Units.isOpen.isClosed_compl

end nonunits

namespace NormedRing

open Asymptotics Filter Metric Finset Ring

/--
theorem `inverse_one_sub` / 定理 `inverse_one_sub`

English:
theorem inverse_one_sub
  given: (t : R) (h : ‖t‖ < 1)
  statement: inverse (1 - t) = ↑(Units.oneSub t h)⁻¹
  proof: by
  rw [← inverse_unit (Units.oneSub t h)]; rw [Units.val_oneSub]

中文:
定理 inverse_one_sub
  条件: (t : R) (h : ‖t‖ < 1)
  结论: inverse (1 - t) = ↑(Units.oneSub t h)⁻¹
  证明: by
  rw [← inverse_unit (Units.oneSub t h)]; rw [Units.val_oneSub]

Depends on / 依赖: Units.oneSub, Units.val_oneSub, inverse_unit, oneSub, val_oneSub
-/
theorem inverse_one_sub (t : R) (h : ‖t‖ < 1) : inverse (1 - t) = ↑(Units.oneSub t h)⁻¹ := by
  rw [← inverse_unit (Units.oneSub t h)]; rw [Units.val_oneSub]

/--
theorem `inverse_add` / 定理 `inverse_add`

English:
theorem inverse_add
  given: (x : Rˣ)
  proof: by
  nontriviality R
  rw [Metric.eventually_nhds_iff]
  refine ⟨‖(↑x⁻¹ : R)‖⁻¹, by cancel_denoms, fun t ht => ?_⟩
  rw [dist_zero_right] at ht
  rw [← x.val_add t ht]; rw [inverse_unit]; rw [Units.add]; rw [Units.copy_eq]; rw [mul_inv_rev]; rw [Units.val_mul]; rw [← inverse_unit]; rw [Units.val_one

中文:
定理 inverse_add
  条件: (x : Rˣ)
  证明: by
  nontriviality R
  rw [Metric.eventually_nhds_iff]
  refine ⟨‖(↑x⁻¹ : R)‖⁻¹, by cancel_denoms, fun t ht => ?_⟩
  rw [dist_zero_right] at ht
  rw [← x.val_add t ht]; rw [inverse_unit]; rw [Units.add]; rw [Units.copy_eq]; rw [mul_inv_rev]; rw [Units.val_mul]; rw [← inverse_unit]; rw [Units.val_one

Depends on / 依赖: Metric, Metric.eventually_nhds_iff, Units.add, Units.copy_eq, Units.val_mul, Units.val_oneSub, cancel_denoms, copy_eq, dist_zero_right, eventually_nhds_iff, inverse_unit, mul_inv_rev, nontriviality, sub_neg_eq_add, val_add, val_mul, val_oneSub, x.val_add
-/
theorem inverse_add (x : Rˣ) :
    forallᶠ t in 𝓝 0, ((x : R) + t)⁻¹ʳ = (1 + ↑x⁻¹ * t)⁻¹ʳ * ↑x⁻¹ := by
  nontriviality R
  rw [Metric.eventually_nhds_iff]
  refine ⟨‖(↑x⁻¹ : R)‖⁻¹, by cancel_denoms, fun t ht => ?_⟩
  rw [dist_zero_right] at ht
  rw [← x.val_add t ht]; rw [inverse_unit]; rw [Units.add]; rw [Units.copy_eq]; rw [mul_inv_rev]; rw [Units.val_mul]; rw [← inverse_unit]; rw [Units.val_oneSub]; rw [sub_neg_eq_add]

/--
theorem `inverse_one_sub_nth_order'` / 定理 `inverse_one_sub_nth_order'`

English:
theorem inverse_one_sub_nth_order'
  given: (n : Nat) {t : R} (ht : ‖t‖ < 1)
  proof: have := _root_.summable_geometric_of_norm_lt_one ht
  calc inverse (1 - t) = ∑' i : Nat, t ^ i := inverse_one_sub t ht
    _ = ∑ i in range n, t ^ i + ∑' i : Nat, t ^ (i + n) := (this.sum_add_tsum_nat_add _).symm
    _ = (∑ i in range n, t ^ i) + t ^ n * inverse (1 - t) := by
      simp only [invers

中文:
定理 inverse_one_sub_nth_order'
  条件: (n : 自然数) {t : R} (ht : ‖t‖ < 1)
  证明: have := _root_.summable_geometric_of_norm_lt_one ht
  calc inverse (1 - t) = ∑' i : Nat, t ^ i := inverse_one_sub t ht
    _ = ∑ i in range n, t ^ i + ∑' i : Nat, t ^ (i + n) := (this.sum_add_tsum_nat_add _).symm
    _ = (∑ i in range n, t ^ i) + t ^ n * inverse (1 - t) := by
      simp only [invers

Depends on / 依赖: _root_, _root_.summable_geometric_of_norm_lt_one, add_comm, inverse, inverse_one_sub, pow_add, sum_add_tsum_nat_add, summable_geometric_of_norm_lt_one, this.sum_add_tsum_nat_add, this.tsum_mul_left, tsum_mul_left
-/
theorem inverse_one_sub_nth_order' (n : Nat) {t : R} (ht : ‖t‖ < 1) :
    inverse ((1 : R) - t) = (∑ i in range n, t ^ i) + t ^ n * inverse (1 - t) :=
  have := _root_.summable_geometric_of_norm_lt_one ht
  calc inverse (1 - t) = ∑' i : Nat, t ^ i := inverse_one_sub t ht
    _ = ∑ i in range n, t ^ i + ∑' i : Nat, t ^ (i + n) := (this.sum_add_tsum_nat_add _).symm
    _ = (∑ i in range n, t ^ i) + t ^ n * inverse (1 - t) := by
      simp only [inverse_one_sub t ht, add_comm _ n, pow_add, this.tsum_mul_left]; rfl

/--
theorem `inverse_one_sub_nth_order` / 定理 `inverse_one_sub_nth_order`

English:
theorem inverse_one_sub_nth_order
  given: (n : Nat)
  proof: Metric.eventually_nhds_iff.2 ⟨1, one_pos, fun t ht => inverse_one_sub_nth_order' n by
    rwa [← dist_zero_right]⟩

中文:
定理 inverse_one_sub_nth_order
  条件: (n : 自然数)
  证明: Metric.eventually_nhds_iff.2 ⟨1, one_pos, fun t ht => inverse_one_sub_nth_order' n by
    rwa [← dist_zero_right]⟩

Depends on / 依赖: Metric, Metric.eventually_nhds_iff, dist_zero_right, eventually_nhds_iff, inverse_one_sub_nth_order, one_pos
-/
theorem inverse_one_sub_nth_order (n : Nat) :
    forallᶠ t in 𝓝 0, inverse ((1 : R) - t) = (∑ i in range n, t ^ i) + t ^ n * inverse (1 - t) :=
Metric.eventually_nhds_iff.2 ⟨1, one_pos, fun t ht => inverse_one_sub_nth_order' n by
    rwa [← dist_zero_right]⟩


/--
theorem `inverse_add_nth_order` / 定理 `inverse_add_nth_order`

English:
theorem inverse_add_nth_order
  given: (x : Rˣ) (n : Nat)
  proof: by
  have hzero : Tendsto (-(↑x⁻¹ : R) * ·) (𝓝 0) (𝓝 0) :=
(mulLeft_continuous _).tendsto' _ _ mul_zero _
  filter_upwards [inverse_add x, hzero.eventually (inverse_one_sub_nth_order n)] with t ht ht'
  rw [neg_mul]; rw [sub_neg_eq_add] at ht'
  conv_lhs => rw [ht, ht', add_mul, ← neg_mul, mul_assoc

中文:
定理 inverse_add_nth_order
  条件: (x : Rˣ) (n : 自然数)
  证明: by
  have hzero : Tendsto (-(↑x⁻¹ : R) * ·) (𝓝 0) (𝓝 0) :=
(mulLeft_continuous _).tendsto' _ _ mul_zero _
  filter_upwards [inverse_add x, hzero.eventually (inverse_one_sub_nth_order n)] with t ht ht'
  rw [neg_mul]; rw [sub_neg_eq_add] at ht'
  conv_lhs => rw [ht, ht', add_mul, ← neg_mul, mul_assoc

Depends on / 依赖: Tendsto, add_mul, conv_lhs, eventually, filter_upwards, hzero.eventually, inverse_add, inverse_one_sub_nth_order, mulLeft_continuous, mul_assoc, mul_zero, neg_mul, sub_neg_eq_add, tendsto
-/
theorem inverse_add_nth_order (x : Rˣ) (n : Nat) :
    forallᶠ t in 𝓝 0, ((x : R) + t)⁻¹ʳ =
      (∑ i in range n, (-↑x⁻¹ * t) ^ i) * ↑x⁻¹ + (-↑x⁻¹ * t) ^ n * (x + t)⁻¹ʳ := by
  have hzero : Tendsto (-(↑x⁻¹ : R) * ·) (𝓝 0) (𝓝 0) :=
(mulLeft_continuous _).tendsto' _ _ mul_zero _
  filter_upwards [inverse_add x, hzero.eventually (inverse_one_sub_nth_order n)] with t ht ht'
  rw [neg_mul]; rw [sub_neg_eq_add] at ht'
  conv_lhs => rw [ht, ht', add_mul, ← neg_mul, mul_assoc]
  rw [ht]

/--
theorem `inverse_one_sub_norm` / 定理 `inverse_one_sub_norm`

English:
theorem inverse_one_sub_norm
  statement: (fun t : R => inverse (1 - t)) =O[𝓝 0] (fun _t => 1 : R -> Real)
  proof: by
  simp only [IsBigO, IsBigOWith, Metric.eventually_nhds_iff]
  refine ⟨‖(1 : R)‖ + 1, (2 : Real)⁻¹, by simp, fun t ht => ?_⟩
  rw [dist_zero_right] at ht
  have ht' : ‖t‖ < 1 := by linarith
  simp only [inverse_one_sub t ht', norm_one, mul_one]
  change ‖∑' n : Nat, t ^ n‖ <= _
  have := tsum_geo

中文:
定理 inverse_one_sub_norm
  结论: (fun t : R => inverse (1 - t)) =O[𝓝 0] (fun _t => 1 : R -> 实数)
  证明: by
  simp only [IsBigO, IsBigOWith, Metric.eventually_nhds_iff]
  refine ⟨‖(1 : R)‖ + 1, (2 : Real)⁻¹, by simp, fun t ht => ?_⟩
  rw [dist_zero_right] at ht
  have ht' : ‖t‖ < 1 := by linarith
  simp only [inverse_one_sub t ht', norm_one, mul_one]
  change ‖∑' n : Nat, t ^ n‖ <= _
  have := tsum_geo

Depends on / 依赖: IsBigO, IsBigOWith, Metric, Metric.eventually_nhds_iff, dist_zero_right, eventually_nhds_iff, inverse_one_sub, mul_one, norm_one, tsum_geometric_le_of_norm_lt_one
-/
theorem inverse_one_sub_norm : (fun t : R => inverse (1 - t)) =O[𝓝 0] (fun _t => 1 : R -> Real) := by
  simp only [IsBigO, IsBigOWith, Metric.eventually_nhds_iff]
  refine ⟨‖(1 : R)‖ + 1, (2 : Real)⁻¹, by simp, fun t ht => ?_⟩
  rw [dist_zero_right] at ht
  have ht' : ‖t‖ < 1 := by linarith
  simp only [inverse_one_sub t ht', norm_one, mul_one]
  change ‖∑' n : Nat, t ^ n‖ <= _
  have := tsum_geometric_le_of_norm_lt_one t ht'
  have : (1 - ‖t‖)⁻¹ <= 2 := inv_le_of_inv_le₀ (by simp) (by linarith)
  linarith

/--
theorem `inverse_add_norm` / 定理 `inverse_add_norm`

English:
theorem inverse_add_norm
  given: (x : Rˣ)
  statement: (fun t : R => inverse (↑x + t)) =O[𝓝 0] fun _t => (1 : Real)
  proof: by
  refine EventuallyEq.trans_isBigO (inverse_add x) (one_mul (1 : Real) ▸ ?_)
  simp only [← sub_neg_eq_add, ← neg_mul]
  have hzero : Tendsto (-(↑x⁻¹ : R) * ·) (𝓝 0) (𝓝 0) :=
(mulLeft_continuous _).tendsto' _ _ mul_zero _
  exact (inverse_one_sub_norm.comp_tendsto hzero).mul (isBigO_const_const _

中文:
定理 inverse_add_norm
  条件: (x : Rˣ)
  结论: (fun t : R => inverse (↑x + t)) =O[𝓝 0] fun _t => (1 : 实数)
  证明: by
  refine EventuallyEq.trans_isBigO (inverse_add x) (one_mul (1 : Real) ▸ ?_)
  simp only [← sub_neg_eq_add, ← neg_mul]
  have hzero : Tendsto (-(↑x⁻¹ : R) * ·) (𝓝 0) (𝓝 0) :=
(mulLeft_continuous _).tendsto' _ _ mul_zero _
  exact (inverse_one_sub_norm.comp_tendsto hzero).mul (isBigO_const_const _

Depends on / 依赖: EventuallyEq, EventuallyEq.trans_isBigO, Tendsto, comp_tendsto, inverse_add, inverse_one_sub_norm, inverse_one_sub_norm.comp_tendsto, isBigO_const_const, mulLeft_continuous, mul_zero, neg_mul, one_mul, one_ne_zero, sub_neg_eq_add, tendsto, trans_isBigO
-/
theorem inverse_add_norm (x : Rˣ) : (fun t : R => inverse (↑x + t)) =O[𝓝 0] fun _t => (1 : Real) := by
  refine EventuallyEq.trans_isBigO (inverse_add x) (one_mul (1 : Real) ▸ ?_)
  simp only [← sub_neg_eq_add, ← neg_mul]
  have hzero : Tendsto (-(↑x⁻¹ : R) * ·) (𝓝 0) (𝓝 0) :=
(mulLeft_continuous _).tendsto' _ _ mul_zero _
  exact (inverse_one_sub_norm.comp_tendsto hzero).mul (isBigO_const_const _ one_ne_zero _)

/--
theorem `inverse_add_norm_diff_nth_order` / 定理 `inverse_add_norm_diff_nth_order`

English:
theorem inverse_add_norm_diff_nth_order
  given: (x : Rˣ) (n : Nat)
  proof: by
  refine EventuallyEq.trans_isBigO (.fun_sub (inverse_add_nth_order x n) (.refl _ _)) ?_
  simp only [add_sub_cancel_left]
  refine ((isBigO_refl _ _).norm_right.mul (inverse_add_norm x)).trans ?_
  simp only [mul_one, isBigO_norm_left]
  exact ((isBigO_refl _ _).norm_right.const_mul_left _).pow 

中文:
定理 inverse_add_norm_diff_nth_order
  条件: (x : Rˣ) (n : 自然数)
  证明: by
  refine EventuallyEq.trans_isBigO (.fun_sub (inverse_add_nth_order x n) (.refl _ _)) ?_
  simp only [add_sub_cancel_left]
  refine ((isBigO_refl _ _).norm_right.mul (inverse_add_norm x)).trans ?_
  simp only [mul_one, isBigO_norm_left]
  exact ((isBigO_refl _ _).norm_right.const_mul_left _).pow 

Depends on / 依赖: EventuallyEq, EventuallyEq.trans_isBigO, add_sub_cancel_left, const_mul_left, fun_sub, inverse_add_norm, inverse_add_nth_order, isBigO_norm_left, isBigO_refl, mul_one, norm_right, norm_right.const_mul_left, norm_right.mul, trans_isBigO
-/
theorem inverse_add_norm_diff_nth_order (x : Rˣ) (n : Nat) :
    (fun t : R => (↑x + t)⁻¹ʳ - (∑ i in range n, (-↑x⁻¹ * t) ^ i) * ↑x⁻¹) =O[𝓝 (0 : R)]
      fun t => ‖t‖ ^ n := by
  refine EventuallyEq.trans_isBigO (.fun_sub (inverse_add_nth_order x n) (.refl _ _)) ?_
  simp only [add_sub_cancel_left]
  refine ((isBigO_refl _ _).norm_right.mul (inverse_add_norm x)).trans ?_
  simp only [mul_one, isBigO_norm_left]
  exact ((isBigO_refl _ _).norm_right.const_mul_left _).pow _

/--
theorem `inverse_add_norm_diff_first_order` / 定理 `inverse_add_norm_diff_first_order`

English:
theorem inverse_add_norm_diff_first_order
  given: (x : Rˣ)
  proof: by
  simpa using inverse_add_norm_diff_nth_order x 1

中文:
定理 inverse_add_norm_diff_first_order
  条件: (x : Rˣ)
  证明: by
  simpa using inverse_add_norm_diff_nth_order x 1

Depends on / 依赖: inverse_add_norm_diff_nth_order
-/
theorem inverse_add_norm_diff_first_order (x : Rˣ) :
    (fun t : R => (↑x + t)⁻¹ʳ - ↑x⁻¹) =O[𝓝 0] fun t => ‖t‖ := by
  simpa using inverse_add_norm_diff_nth_order x 1

/--
theorem `inverse_add_norm_diff_second_order` / 定理 `inverse_add_norm_diff_second_order`

English:
theorem inverse_add_norm_diff_second_order
  given: (x : Rˣ)
  proof: by
  convert! inverse_add_norm_diff_nth_order x 2 using 2
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one, add_mul, one_mul,
    ← sub_sub, neg_mul, sub_neg_eq_add]

中文:
定理 inverse_add_norm_diff_second_order
  条件: (x : Rˣ)
  证明: by
  convert! inverse_add_norm_diff_nth_order x 2 using 2
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one, add_mul, one_mul,
    ← sub_sub, neg_mul, sub_neg_eq_add]

Depends on / 依赖: add_mul, convert, inverse_add_norm_diff_nth_order, neg_mul, one_mul, pow_one, pow_zero, sub_neg_eq_add, sub_sub, sum_range_succ, sum_range_zero, zero_add
-/
theorem inverse_add_norm_diff_second_order (x : Rˣ) :
    (fun t : R => (↑x + t)⁻¹ʳ - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =O[𝓝 0] fun t => ‖t‖ ^ 2 := by
  convert! inverse_add_norm_diff_nth_order x 2 using 2
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one, add_mul, one_mul,
    ← sub_sub, neg_mul, sub_neg_eq_add]

/--
theorem `inverse_continuousAt` / 定理 `inverse_continuousAt`

English:
theorem inverse_continuousAt
  given: (x : Rˣ)
  statement: ContinuousAt inverse (x : R)
  proof: by
  have h_is_o : (fun t : R => (↑x + t)⁻¹ʳ - ↑x⁻¹) =o[𝓝 0] (fun _ => 1 : R -> Real) :=
    (inverse_add_norm_diff_first_order x).trans_isLittleO (isLittleO_id_const one_ne_zero).norm_left
  have h_lim : Tendsto (fun y : R => y - x) (𝓝 x) (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mp

中文:
定理 inverse_continuousAt
  条件: (x : Rˣ)
  结论: ContinuousAt inverse (x : R)
  证明: by
  have h_is_o : (fun t : R => (↑x + t)⁻¹ʳ - ↑x⁻¹) =o[𝓝 0] (fun _ => 1 : R -> Real) :=
    (inverse_add_norm_diff_first_order x).trans_isLittleO (isLittleO_id_const one_ne_zero).norm_left
  have h_lim : Tendsto (fun y : R => y - x) (𝓝 x) (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mp

Depends on / 依赖: ContinuousAt, Function, Function.comp_def, Tendsto, comp_def, h_is_o, h_is_o.norm_left.tendsto_div_nhds_zero.comp, h_lim, inverse_add_norm_diff_first_order, inverse_unit, isLittleO_id_const, norm_left, one_ne_zero, tendsto_div_nhds_zero, tendsto_id, tendsto_iff_norm_sub_tendsto_zero, tendsto_iff_norm_sub_tendsto_zero.mp, tendsto_zero_iff_norm_tendsto_zero, tendsto_zero_iff_norm_tendsto_zero.mpr, trans_isLittleO
-/
theorem inverse_continuousAt (x : Rˣ) : ContinuousAt inverse (x : R) := by
  have h_is_o : (fun t : R => (↑x + t)⁻¹ʳ - ↑x⁻¹) =o[𝓝 0] (fun _ => 1 : R -> Real) :=
    (inverse_add_norm_diff_first_order x).trans_isLittleO (isLittleO_id_const one_ne_zero).norm_left
  have h_lim : Tendsto (fun y : R => y - x) (𝓝 x) (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    exact tendsto_iff_norm_sub_tendsto_zero.mp tendsto_id
  rw [ContinuousAt]; rw [tendsto_iff_norm_sub_tendsto_zero]; rw [inverse_unit]
  simpa [Function.comp_def] using h_is_o.norm_left.tendsto_div_nhds_zero.comp h_lim

end NormedRing

namespace Units

open MulOpposite Filter NormedRing

/--
theorem `isOpenEmbedding_val` / 定理 `isOpenEmbedding_val`

English:
theorem isOpenEmbedding_val
  statement: IsOpenEmbedding (val : Rˣ -> R) where
  proof: isEmbedding_val_mk'
    (fun _ ⟨u, hu⟩ => hu ▸ (inverse_continuousAt u).continuousWithinAt) Ring.inverse_unit
  isOpen_range := Units.isOpen

中文:
定理 isOpenEmbedding_val
  结论: IsOpenEmbedding (val : Rˣ -> R) where
  证明: isEmbedding_val_mk'
    (fun _ ⟨u, hu⟩ => hu ▸ (inverse_continuousAt u).continuousWithinAt) Ring.inverse_unit
  isOpen_range := Units.isOpen

Depends on / 依赖: isEmbedding_val_mk
-/
theorem isOpenEmbedding_val : IsOpenEmbedding (val : Rˣ -> R) where
  toIsEmbedding := isEmbedding_val_mk'
    (fun _ ⟨u, hu⟩ => hu ▸ (inverse_continuousAt u).continuousWithinAt) Ring.inverse_unit
  isOpen_range := Units.isOpen

/--
theorem `isOpenMap_val` / 定理 `isOpenMap_val`

English:
theorem isOpenMap_val
  statement: IsOpenMap (val : Rˣ -> R)
  proof: isOpenEmbedding_val.isOpenMap

中文:
定理 isOpenMap_val
  结论: IsOpenMap (val : Rˣ -> R)
  证明: isOpenEmbedding_val.isOpenMap

Depends on / 依赖: isOpenEmbedding_val, isOpenEmbedding_val.isOpenMap, isOpenMap
-/
theorem isOpenMap_val : IsOpenMap (val : Rˣ -> R) :=
  isOpenEmbedding_val.isOpenMap

end Units

namespace Ideal

/--
theorem `eq_top_of_norm_lt_one` / 定理 `eq_top_of_norm_lt_one`

English:
theorem eq_top_of_norm_lt_one
  given: (I : Ideal R) {x : R} (hxI : x in I) (hx : ‖1 - x‖ < 1)
  statement: I = ⊤
  proof: let u := Units.oneSub (1 - x) hx
I.eq_top_iff_one.mpr by
    simpa only [show u.inv * x = 1 by simp [u]] using I.mul_mem_left u.inv hxI

中文:
定理 eq_top_of_norm_lt_one
  条件: (I : Ideal R) {x : R} (hxI : x in I) (hx : ‖1 - x‖ < 1)
  结论: I = ⊤
  证明: let u := Units.oneSub (1 - x) hx
I.eq_top_iff_one.mpr by
    simpa only [show u.inv * x = 1 by simp [u]] using I.mul_mem_left u.inv hxI

Depends on / 依赖: I.eq_top_iff_one.mpr, I.mul_mem_left, Units.oneSub, eq_top_iff_one, mul_mem_left, oneSub, u.inv
-/
theorem eq_top_of_norm_lt_one (I : Ideal R) {x : R} (hxI : x in I) (hx : ‖1 - x‖ < 1) : I = ⊤ :=
  let u := Units.oneSub (1 - x) hx
I.eq_top_iff_one.mpr by
    simpa only [show u.inv * x = 1 by simp [u]] using I.mul_mem_left u.inv hxI

/--
theorem `closure_ne_top` / 定理 `closure_ne_top`

English:
theorem closure_ne_top
  given: (I : Ideal R) (hI : I != ⊤)
  statement: I.closure != ⊤
  proof: by
  have h := closure_minimal (coe_subset_nonunits hI) nonunits.isClosed
  simpa only [I.closure.eq_top_iff_one, Ne] using! mt (@h 1) one_notMem_nonunits

中文:
定理 closure_ne_top
  条件: (I : Ideal R) (hI : I != ⊤)
  结论: I.closure != ⊤
  证明: by
  have h := closure_minimal (coe_subset_nonunits hI) nonunits.isClosed
  simpa only [I.closure.eq_top_iff_one, Ne] using! mt (@h 1) one_notMem_nonunits

Depends on / 依赖: I.closure.eq_top_iff_one, closure, closure_minimal, coe_subset_nonunits, eq_top_iff_one, isClosed, nonunits, nonunits.isClosed, one_notMem_nonunits
-/
theorem closure_ne_top (I : Ideal R) (hI : I != ⊤) : I.closure != ⊤ := by
  have h := closure_minimal (coe_subset_nonunits hI) nonunits.isClosed
  simpa only [I.closure.eq_top_iff_one, Ne] using! mt (@h 1) one_notMem_nonunits

/--
theorem `IsMaximal.closure_eq` / 定理 `IsMaximal.closure_eq`

English:
theorem IsMaximal.closure_eq
  given: {I : Ideal R} (hI : I.IsMaximal)
  statement: I.closure = I
  proof: (hI.eq_of_le (I.closure_ne_top hI.ne_top) subset_closure).symm

中文:
定理 IsMaximal.closure_eq
  条件: {I : Ideal R} (hI : I.IsMaximal)
  结论: I.closure = I
  证明: (hI.eq_of_le (I.closure_ne_top hI.ne_top) subset_closure).symm

Depends on / 依赖: I.closure_ne_top, closure_ne_top, eq_of_le, hI.eq_of_le, hI.ne_top, ne_top, subset_closure
-/
theorem IsMaximal.closure_eq {I : Ideal R} (hI : I.IsMaximal) : I.closure = I :=
  (hI.eq_of_le (I.closure_ne_top hI.ne_top) subset_closure).symm

/--
Instance `IsMaximal.isClosed` / 实例 `IsMaximal.isClosed`

English:
instance IsMaximal.isClosed
  signature: {I : Ideal R} [hI : I.IsMaximal]
  body: isClosed_of_closure_subset Eq.subset congr_arg ((↑) : Ideal R -> Set R) hI.closure_eq

中文:
实例 IsMaximal.isClosed
  签名: {I : Ideal R} [hI : I.IsMaximal]
  定义体: isClosed_of_closure_subset Eq.subset congr_arg ((↑) : Ideal R -> Set R) hI.closure_eq

Depends on / 依赖: Eq.subset, closure_eq, congr_arg, hI.closure_eq, isClosed_of_closure_subset, subset
-/
instance IsMaximal.isClosed {I : Ideal R} [hI : I.IsMaximal] : IsClosed (I : Set R) :=
isClosed_of_closure_subset Eq.subset congr_arg ((↑) : Ideal R -> Set R) hI.closure_eq

end Ideal
