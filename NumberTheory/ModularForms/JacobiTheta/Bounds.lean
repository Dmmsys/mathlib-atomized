/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Asymptotic bounds for Jacobi theta functions

The goal of this file is to establish some technical lemmas about the asymptotics of the sums

`F_nat k a t = ∑' (n : ℕ), (n + a) ^ k * exp (-π * (n + a) ^ 2 * t)`

and

`F_int k a t = ∑' (n : ℤ), |n + a| ^ k * exp (-π * (n + a) ^ 2 * t).`

Here `k : ℕ` and `a : ℝ` (resp `a : UnitAddCircle`) are fixed, and we are interested in
asymptotics as `t → ∞`. These results are needed for the theory of Hurwitz zeta functions (and
hence Dirichlet L-functions, etc).

## Main results

* `HurwitzKernelBounds.isBigO_atTop_F_nat_zero_sub` : for `0 ≤ a`, the function
  `F_nat 0 a - (if a = 0 then 1 else 0)` decays exponentially at `∞` (i.e. it satisfies
  `=O[atTop] fun t ↦ exp (-p * t)` for some real `0 < p`).
* `HurwitzKernelBounds.isBigO_atTop_F_nat_one` : for `0 ≤ a`, the function `F_nat 1 a` decays
  exponentially at `∞`.
* `HurwitzKernelBounds.isBigO_atTop_F_int_zero_sub` : for any `a : UnitAddCircle`, the function
  `F_int 0 a - (if a = 0 then 1 else 0)` decays exponentially at `∞`.
* `HurwitzKernelBounds.isBigO_atTop_F_int_one`: the function `F_int 1 a` decays exponentially at
  `∞`.
-/

@[expose] public section

open Set Filter Topology Asymptotics Real

noncomputable section

namespace HurwitzKernelBounds

section lemmas

/--
lemma `isBigO_exp_neg_mul_of_le` / 引理 `isBigO_exp_neg_mul_of_le`

English:
lemma isBigO_exp_neg_mul_of_le
  given: {c d : Real} (hcd : c <= d)
  proof: by
  apply Eventually.isBigO
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_of_nonneg (exp_pos _).le]
  gcongr

中文:
引理 isBigO_exp_neg_mul_of_le
  条件: {c d : 实数} (hcd : c <= d)
  证明: by
  apply Eventually.isBigO
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_of_nonneg (exp_pos _).le]
  gcongr

Depends on / 依赖: Eventually, Eventually.isBigO, eventually_gt_atTop, exp_pos, filter_upwards, isBigO, norm_of_nonneg
-/
lemma isBigO_exp_neg_mul_of_le {c d : Real} (hcd : c <= d) :
    (fun t => exp (-d * t)) =O[atTop] fun t => exp (-c * t) := by
  apply Eventually.isBigO
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_of_nonneg (exp_pos _).le]
  gcongr

/--
lemma `exp_lt_aux` / 引理 `exp_lt_aux`

English:
lemma exp_lt_aux
  given: {t : Real} (ht : 0 < t)
  statement: rexp (-π * t) < 1
  proof: by
  simpa only [exp_lt_one_iff, neg_mul, neg_lt_zero] using mul_pos pi_pos ht

中文:
引理 exp_lt_aux
  条件: {t : 实数} (ht : 0 < t)
  结论: rexp (-π * t) < 1
  证明: by
  simpa only [exp_lt_one_iff, neg_mul, neg_lt_zero] using mul_pos pi_pos ht
-/
private lemma exp_lt_aux {t : Real} (ht : 0 < t) : rexp (-π * t) < 1 := by
  simpa only [exp_lt_one_iff, neg_mul, neg_lt_zero] using mul_pos pi_pos ht

/--
lemma `isBigO_one_aux` / 引理 `isBigO_one_aux`

English:
lemma isBigO_one_aux
  proof: by
  refine ((Tendsto.const_sub _ ?_).inv₀ (by simp)).isBigO_one Real (c := ((1 - 0)⁻¹ : Real))
  simpa only [neg_mul, tendsto_exp_comp_nhds_zero, tendsto_neg_atBot_iff]
    using! tendsto_id.const_mul_atTop pi_pos

中文:
引理 isBigO_one_aux
  证明: by
  refine ((Tendsto.const_sub _ ?_).inv₀ (by simp)).isBigO_one Real (c := ((1 - 0)⁻¹ : Real))
  simpa only [neg_mul, tendsto_exp_comp_nhds_zero, tendsto_neg_atBot_iff]
    using! tendsto_id.const_mul_atTop pi_pos
-/
private lemma isBigO_one_aux :
    IsBigO atTop (fun t : Real => (1 - rexp (-π * t))⁻¹) (fun _ => (1 : Real)) := by
  refine ((Tendsto.const_sub _ ?_).inv₀ (by simp)).isBigO_one Real (c := ((1 - 0)⁻¹ : Real))
  simpa only [neg_mul, tendsto_exp_comp_nhds_zero, tendsto_neg_atBot_iff]
    using! tendsto_id.const_mul_atTop pi_pos

end lemmas


section nat

/--
Definition of `f_nat` / `f_nat` 的定义

English:
definition f_nat
  signature: (k : Nat) (a t : Real) (n : Nat)
  body: (n + a) ^ k * exp (-π * (n + a) ^ 2 * t)

中文:
定义 f_nat
  签名: (k : 自然数) (a t : 实数) (n : 自然数)
  定义体: (n + a) ^ k * exp (-π * (n + a) ^ 2 * t)
-/
def f_nat (k : Nat) (a t : Real) (n : Nat) : Real := (n + a) ^ k * exp (-π * (n + a) ^ 2 * t)

/--
Definition of `g_nat` / `g_nat` 的定义

English:
definition g_nat
  signature: (k : Nat) (a t : Real) (n : Nat)
  body: (n + a) ^ k * exp (-π * (n + a ^ 2) * t)

中文:
定义 g_nat
  签名: (k : 自然数) (a t : 实数) (n : 自然数)
  定义体: (n + a) ^ k * exp (-π * (n + a ^ 2) * t)
-/
def g_nat (k : Nat) (a t : Real) (n : Nat) : Real := (n + a) ^ k * exp (-π * (n + a ^ 2) * t)

/--
lemma `f_le_g_nat` / 引理 `f_le_g_nat`

English:
lemma f_le_g_nat
  given: (k : Nat) {a t : Real} (ha : 0 <= a) (ht : 0 < t) (n : Nat)
  proof: by
  rw [f_nat]; rw [norm_of_nonneg (by positivity)]; rw [g_nat]
  simp only [neg_mul, add_sq]
  gcongr
  have H₁ : (n : Real) <= n ^ 2 := mod_cast Nat.le_self_pow two_ne_zero n
  have H₂ : 0 <= 2 * n * a := by positivity
  linear_combination H₁ + H₂

中文:
引理 f_le_g_nat
  条件: (k : 自然数) {a t : 实数} (ha : 0 <= a) (ht : 0 < t) (n : 自然数)
  证明: by
  rw [f_nat]; rw [norm_of_nonneg (by positivity)]; rw [g_nat]
  simp only [neg_mul, add_sq]
  gcongr
  have H₁ : (n : Real) <= n ^ 2 := mod_cast Nat.le_self_pow two_ne_zero n
  have H₂ : 0 <= 2 * n * a := by positivity
  linear_combination H₁ + H₂

Depends on / 依赖: Nat.le_self_pow, add_sq, f_nat, g_nat, le_self_pow, linear_combination, mod_cast, neg_mul, norm_of_nonneg, two_ne_zero
-/
lemma f_le_g_nat (k : Nat) {a t : Real} (ha : 0 <= a) (ht : 0 < t) (n : Nat) :
    ‖f_nat k a t n‖ <= g_nat k a t n := by
  rw [f_nat]; rw [norm_of_nonneg (by positivity)]; rw [g_nat]
  simp only [neg_mul, add_sq]
  gcongr
  have H₁ : (n : Real) <= n ^ 2 := mod_cast Nat.le_self_pow two_ne_zero n
  have H₂ : 0 <= 2 * n * a := by positivity
  linear_combination H₁ + H₂

/--
Definition of `F_nat` / `F_nat` 的定义

English:
definition F_nat
  signature: (k : Nat) (a t : Real)
  body: ∑' n, f_nat k a t n

中文:
定义 F_nat
  签名: (k : 自然数) (a t : 实数)
  定义体: ∑' n, f_nat k a t n

Depends on / 依赖: f_nat
-/
def F_nat (k : Nat) (a t : Real) : Real := ∑' n, f_nat k a t n

/--
lemma `summable_f_nat` / 引理 `summable_f_nat`

English:
lemma summable_f_nat
  given: (k : Nat) (a : Real) {t : Real} (ht : 0 < t)
  statement: Summable (f_nat k a t)
  proof: by
  have : Summable fun n : Nat => n ^ k * exp (-π * (n + a) ^ 2 * t) := by
    refine (((summable_pow_mul_jacobiTheta₂_term_bound (|a| * t) ht k).mul_right
      (rexp (-π * a ^ 2 * t))).comp_injective Nat.cast_injective).of_norm_bounded (fun n => ?_)
    simp_rw [mul_assoc, Function.comp_apply, ←

中文:
引理 summable_f_nat
  条件: (k : 自然数) (a : 实数) {t : 实数} (ht : 0 < t)
  结论: Summable (f_nat k a t)
  证明: by
  have : Summable fun n : Nat => n ^ k * exp (-π * (n + a) ^ 2 * t) := by
    refine (((summable_pow_mul_jacobiTheta₂_term_bound (|a| * t) ht k).mul_right
      (rexp (-π * a ^ 2 * t))).comp_injective Nat.cast_injective).of_norm_bounded (fun n => ?_)
    simp_rw [mul_assoc, Function.comp_apply, ←

Depends on / 依赖: Function, Function.comp_apply, Int.cast_abs, Int.cast_natCast, Nat.abs_cast, Nat.cast_injective, Real.exp_add, Summable, abs_cast, abs_exp, cast_abs, cast_injective, cast_natCast, comp_apply, comp_injective, exp_add, mul_assoc, mul_right, norm_eq_abs, norm_mul
-/
lemma summable_f_nat (k : Nat) (a : Real) {t : Real} (ht : 0 < t) : Summable (f_nat k a t) := by
  have : Summable fun n : Nat => n ^ k * exp (-π * (n + a) ^ 2 * t) := by
    refine (((summable_pow_mul_jacobiTheta₂_term_bound (|a| * t) ht k).mul_right
      (rexp (-π * a ^ 2 * t))).comp_injective Nat.cast_injective).of_norm_bounded (fun n => ?_)
    simp_rw [mul_assoc, Function.comp_apply, ← Real.exp_add, norm_mul, norm_pow, Int.cast_abs,
      Int.cast_natCast, norm_eq_abs, Nat.abs_cast, abs_exp]
    gcongr
    rw [← sub_nonneg]
    rw [show -π * (t * n ^ 2 - 2 * (|a| * (t * n))) + -π * (a ^ 2 * t) - -π * ((n + a) ^ 2 * t)
         = π * t * n * (|a| + a) * 2 by ring]
    refine mul_nonneg (mul_nonneg (by positivity) ?_) two_pos.le
    rw [← neg_le_iff_add_nonneg]
    apply neg_le_abs
  apply (this.mul_left (2 ^ k)).of_norm_bounded_eventually_nat
  simp_rw [← mul_assoc, f_nat, norm_mul, norm_eq_abs, abs_exp,
    mul_le_mul_iff_of_pos_right (exp_pos _), ← mul_pow, abs_pow, two_mul]
  filter_upwards [eventually_ge_atTop (Nat.ceil |a|)] with n hn
  gcongr
  exact (abs_add_le ..).trans (add_le_add (Nat.abs_cast _).le (Nat.ceil_le.mp hn))

section k_eq_zero


/--
lemma `F_nat_zero_le` / 引理 `F_nat_zero_le`

English:
lemma F_nat_zero_le
  given: {a : Real} (ha : 0 <= a) {t : Real} (ht : 0 < t)
  proof: by
  refine tsum_of_norm_bounded ?_ (f_le_g_nat 0 ha ht)
  convert! (hasSum_geometric_of_lt_one (exp_pos _).le <| exp_lt_aux ht).mul_left _ using 1
  ext1 n
  simp only [g_nat]
  rw [← Real.exp_nat_mul]; rw [← Real.exp_add]
  ring_nf

中文:
引理 F_nat_zero_le
  条件: {a : 实数} (ha : 0 <= a) {t : 实数} (ht : 0 < t)
  证明: by
  refine tsum_of_norm_bounded ?_ (f_le_g_nat 0 ha ht)
  convert! (hasSum_geometric_of_lt_one (exp_pos _).le <| exp_lt_aux ht).mul_left _ using 1
  ext1 n
  simp only [g_nat]
  rw [← Real.exp_nat_mul]; rw [← Real.exp_add]
  ring_nf

Depends on / 依赖: Real.exp_add, Real.exp_nat_mul, convert, exp_add, exp_lt_aux, exp_nat_mul, exp_pos, f_le_g_nat, g_nat, hasSum_geometric_of_lt_one, mul_left, ring_nf, tsum_of_norm_bounded
-/
lemma F_nat_zero_le {a : Real} (ha : 0 <= a) {t : Real} (ht : 0 < t) :
    ‖F_nat 0 a t‖ <= rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t)) := by
  refine tsum_of_norm_bounded ?_ (f_le_g_nat 0 ha ht)
  convert! (hasSum_geometric_of_lt_one (exp_pos _).le <| exp_lt_aux ht).mul_left _ using 1
  ext1 n
  simp only [g_nat]
  rw [← Real.exp_nat_mul]; rw [← Real.exp_add]
  ring_nf

/--
lemma `F_nat_zero_zero_sub_le` / 引理 `F_nat_zero_zero_sub_le`

English:
lemma F_nat_zero_zero_sub_le
  given: {t : Real} (ht : 0 < t)
  proof: by
  convert! F_nat_zero_le zero_le_one ht using 2
  · rw [F_nat, (summable_f_nat 0 0 ht).tsum_eq_zero_add, f_nat, Nat.cast_zero, add_zero, pow_zero,
      one_mul, pow_two, mul_zero, mul_zero, zero_mul, exp_zero, add_comm, add_sub_cancel_right]
    simp_rw [F_nat, f_nat, Nat.cast_add, Nat.cast_one,

中文:
引理 F_nat_zero_zero_sub_le
  条件: {t : 实数} (ht : 0 < t)
  证明: by
  convert! F_nat_zero_le zero_le_one ht using 2
  · rw [F_nat, (summable_f_nat 0 0 ht).tsum_eq_zero_add, f_nat, Nat.cast_zero, add_zero, pow_zero,
      one_mul, pow_two, mul_zero, mul_zero, zero_mul, exp_zero, add_comm, add_sub_cancel_right]
    simp_rw [F_nat, f_nat, Nat.cast_add, Nat.cast_one,

Depends on / 依赖: F_nat, F_nat_zero_le, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_comm, add_sub_cancel_right, add_zero, cast_add, cast_one, cast_zero, convert, exp_zero, f_nat, mul_one, mul_zero, one_mul, one_pow, pow_two, pow_zero
-/
lemma F_nat_zero_zero_sub_le {t : Real} (ht : 0 < t) :
    ‖F_nat 0 0 t - 1‖ <= rexp (-π * t) / (1 - rexp (-π * t)) := by
  convert! F_nat_zero_le zero_le_one ht using 2
  · rw [F_nat, (summable_f_nat 0 0 ht).tsum_eq_zero_add, f_nat, Nat.cast_zero, add_zero, pow_zero,
      one_mul, pow_two, mul_zero, mul_zero, zero_mul, exp_zero, add_comm, add_sub_cancel_right]
    simp_rw [F_nat, f_nat, Nat.cast_add, Nat.cast_one, add_zero]
  · rw [one_pow, mul_one]

/--
lemma `isBigO_atTop_F_nat_zero_sub` / 引理 `isBigO_atTop_F_nat_zero_sub`

English:
lemma isBigO_atTop_F_nat_zero_sub
  given: {a : Real} (ha : 0 <= a)
  statement: exists p, 0 < p ∧
  proof: by
  split_ifs with h
  · rw [h]
    have : (fun t => F_nat 0 0 t - 1) =O[atTop] fun t => rexp (-π * t) / (1 - rexp (-π * t)) := by
      apply Eventually.isBigO
      filter_upwards [eventually_gt_atTop 0] with t ht
      exact F_nat_zero_zero_sub_le ht
    refine ⟨_, pi_pos, this.trans ?_⟩
    sim

中文:
引理 isBigO_atTop_F_nat_zero_sub
  条件: {a : 实数} (ha : 0 <= a)
  结论: 存在 p, 0 < p ∧
  证明: by
  split_ifs with h
  · rw [h]
    have : (fun t => F_nat 0 0 t - 1) =O[atTop] fun t => rexp (-π * t) / (1 - rexp (-π * t)) := by
      apply Eventually.isBigO
      filter_upwards [eventually_gt_atTop 0] with t ht
      exact F_nat_zero_zero_sub_le ht
    refine ⟨_, pi_pos, this.trans ?_⟩
    sim

Depends on / 依赖: Eventually, Eventually.isBigO, F_nat, F_nat_zero_zero_sub_le, eventually_gt_atTop, filter_upwards, isBigO, isBigO_one_aux, isBigO_refl, pi_pos, simp_rw, split_ifs, sub_zero, this.trans
-/
lemma isBigO_atTop_F_nat_zero_sub {a : Real} (ha : 0 <= a) : exists p, 0 < p ∧
    (fun t => F_nat 0 a t - (if a = 0 then 1 else 0)) =O[atTop] fun t => exp (-p * t) := by
  split_ifs with h
  · rw [h]
    have : (fun t => F_nat 0 0 t - 1) =O[atTop] fun t => rexp (-π * t) / (1 - rexp (-π * t)) := by
      apply Eventually.isBigO
      filter_upwards [eventually_gt_atTop 0] with t ht
      exact F_nat_zero_zero_sub_le ht
    refine ⟨_, pi_pos, this.trans ?_⟩
    simpa using! (isBigO_refl (fun t => rexp (-π * t)) _).mul isBigO_one_aux
  · simp_rw [sub_zero]
    have : (fun t => F_nat 0 a t) =O[atTop] fun t => rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t)) := by
      apply Eventually.isBigO
      filter_upwards [eventually_gt_atTop 0] with t ht
      exact F_nat_zero_le ha ht
    refine ⟨π * a ^ 2, mul_pos pi_pos (sq_pos_of_ne_zero h), this.trans ?_⟩
    simpa only [neg_mul π (a ^ 2), mul_one] using! (isBigO_refl _ _).mul isBigO_one_aux

end k_eq_zero

section k_eq_one


/--
lemma `F_nat_one_le` / 引理 `F_nat_one_le`

English:
lemma F_nat_one_le
  given: {a : Real} (ha : 0 <= a) {t : Real} (ht : 0 < t)
  proof: by
  refine tsum_of_norm_bounded ?_ (f_le_g_nat 1 ha ht)
  unfold g_nat
  simp_rw [pow_one, add_mul]
  apply HasSum.add
  · have h0' : ‖rexp (-π * t)‖ < 1 := by
      simpa only [norm_eq_abs, abs_exp] using exp_lt_aux ht
    convert! (hasSum_coe_mul_geometric_of_norm_lt_one h0').mul_left (exp (-π * 

中文:
引理 F_nat_one_le
  条件: {a : 实数} (ha : 0 <= a) {t : 实数} (ht : 0 < t)
  证明: by
  refine tsum_of_norm_bounded ?_ (f_le_g_nat 1 ha ht)
  unfold g_nat
  simp_rw [pow_one, add_mul]
  apply HasSum.add
  · have h0' : ‖rexp (-π * t)‖ < 1 := by
      simpa only [norm_eq_abs, abs_exp] using exp_lt_aux ht
    convert! (hasSum_coe_mul_geometric_of_norm_lt_one h0').mul_left (exp (-π * 

Depends on / 依赖: HasSum, HasSum.add, Real.exp_add, Real.exp_nat_mul, abs_exp, add_mul, convert, exp_add, exp_lt_aux, exp_nat_mul, f_le_g_nat, g_nat, hasSum_coe_mul_geometric_of_norm_lt_one, hasSum_geometric_of, mul_add, mul_assoc, mul_comm, mul_div_assoc, mul_left, mul_one
-/
lemma F_nat_one_le {a : Real} (ha : 0 <= a) {t : Real} (ht : 0 < t) :
    ‖F_nat 1 a t‖ <= rexp (-π * (a ^ 2 + 1) * t) / (1 - rexp (-π * t)) ^ 2
      + a * rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t)) := by
  refine tsum_of_norm_bounded ?_ (f_le_g_nat 1 ha ht)
  unfold g_nat
  simp_rw [pow_one, add_mul]
  apply HasSum.add
  · have h0' : ‖rexp (-π * t)‖ < 1 := by
      simpa only [norm_eq_abs, abs_exp] using exp_lt_aux ht
    convert! (hasSum_coe_mul_geometric_of_norm_lt_one h0').mul_left (exp (-π * a ^ 2 * t)) using 1
    · ext1 n
      rw [mul_comm (exp _)]; rw [← Real.exp_nat_mul]; rw [mul_assoc (n : Real)]; rw [← Real.exp_add]
      ring_nf
    · rw [mul_add, add_mul, mul_one, exp_add, mul_div_assoc]
  · convert! (hasSum_geometric_of_lt_one (exp_pos _).le <| exp_lt_aux ht).mul_left _ using 1
    ext1 n
    rw [← Real.exp_nat_mul]; rw [mul_assoc _ (exp _)]; rw [← Real.exp_add]
    ring_nf

/--
lemma `isBigO_atTop_F_nat_one` / 引理 `isBigO_atTop_F_nat_one`

English:
lemma isBigO_atTop_F_nat_one
  given: {a : Real} (ha : 0 <= a)
  statement: exists p, 0 < p ∧
  proof: by
  suffices exists p, 0 < p ∧ (fun t => rexp (-π * (a ^ 2 + 1) * t) / (1 - rexp (-π * t)) ^ 2
      + a * rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t))) =O[atTop] fun t => exp (-p * t) by
    let ⟨p, hp, hp'⟩ := this
    refine ⟨p, hp, (Eventually.isBigO ?_).trans hp'⟩
    filter_upwards [eventually

中文:
引理 isBigO_atTop_F_nat_one
  条件: {a : 实数} (ha : 0 <= a)
  结论: 存在 p, 0 < p ∧
  证明: by
  suffices exists p, 0 < p ∧ (fun t => rexp (-π * (a ^ 2 + 1) * t) / (1 - rexp (-π * t)) ^ 2
      + a * rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t))) =O[atTop] fun t => exp (-p * t) by
    let ⟨p, hp, hp'⟩ := this
    refine ⟨p, hp, (Eventually.isBigO ?_).trans hp'⟩
    filter_upwards [eventually

Depends on / 依赖: Eventually, Eventually.isBigO, F_nat_one_le, IsBigO, eq_or_lt, eventually_gt_atTop, filter_upwards, inv_pow, isBigO, isBigO_one_aux, isBigO_one_aux.pow, one_pow
-/
lemma isBigO_atTop_F_nat_one {a : Real} (ha : 0 <= a) : exists p, 0 < p ∧
    F_nat 1 a =O[atTop] fun t => exp (-p * t) := by
  suffices exists p, 0 < p ∧ (fun t => rexp (-π * (a ^ 2 + 1) * t) / (1 - rexp (-π * t)) ^ 2
      + a * rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t))) =O[atTop] fun t => exp (-p * t) by
    let ⟨p, hp, hp'⟩ := this
    refine ⟨p, hp, (Eventually.isBigO ?_).trans hp'⟩
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact F_nat_one_le ha ht
  have aux' : IsBigO atTop (fun t : Real => ((1 - rexp (-π * t)) ^ 2)⁻¹) (fun _ => (1 : Real)) := by
    simpa only [inv_pow, one_pow] using! isBigO_one_aux.pow 2
  rcases eq_or_lt_of_le ha with rfl | ha'
  · exact ⟨_, pi_pos, by simpa only [zero_pow two_ne_zero, zero_add, mul_one, zero_mul, zero_div,
      add_zero] using! (isBigO_refl _ _).mul aux'⟩
· refine ⟨π * a ^ 2, mul_pos pi_pos pow_pos ha' _, IsBigO.add ?_ ?_⟩
    · conv_rhs => enter [t]; rw [← mul_one (rexp _)]
      refine (Eventually.isBigO ?_).mul aux'
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [norm_of_nonneg (exp_pos _).le]; rw [exp_le_exp]
      nlinarith [pi_pos]
    · simp_rw [mul_div_assoc, ← neg_mul]
      apply IsBigO.const_mul_left
      simpa only [mul_one] using! (isBigO_refl _ _).mul isBigO_one_aux

end k_eq_one

end nat

section int

/--
Definition of `f_int` / `f_int` 的定义

English:
definition f_int
  signature: (k : Nat) (a t : Real) (n : Int)
  body: |n + a| ^ k * exp (-π * (n + a) ^ 2 * t)

中文:
定义 f_int
  签名: (k : 自然数) (a t : 实数) (n : 整数)
  定义体: |n + a| ^ k * exp (-π * (n + a) ^ 2 * t)
-/
def f_int (k : Nat) (a t : Real) (n : Int) : Real := |n + a| ^ k * exp (-π * (n + a) ^ 2 * t)

/--
lemma `f_int_ofNat` / 引理 `f_int_ofNat`

English:
lemma f_int_ofNat
  given: (k : Nat) {a : Real} (ha : 0 <= a) (t : Real) (n : Nat)
  proof: by
  rw [f_int]; rw [f_nat]; rw [Int.ofNat_eq_natCast]; rw [Int.cast_natCast]; rw [abs_of_nonneg (by positivity)]

中文:
引理 f_int_of自然数
  条件: (k : 自然数) {a : 实数} (ha : 0 <= a) (t : 实数) (n : 自然数)
  证明: by
  rw [f_int]; rw [f_nat]; rw [Int.ofNat_eq_natCast]; rw [Int.cast_natCast]; rw [abs_of_nonneg (by positivity)]

Depends on / 依赖: Int.cast_natCast, Int.ofNat_eq_natCast, abs_of_nonneg, cast_natCast, f_int, f_nat, ofNat_eq_natCast
-/
lemma f_int_ofNat (k : Nat) {a : Real} (ha : 0 <= a) (t : Real) (n : Nat) :
    f_int k a t (Int.ofNat n) = f_nat k a t n := by
  rw [f_int]; rw [f_nat]; rw [Int.ofNat_eq_natCast]; rw [Int.cast_natCast]; rw [abs_of_nonneg (by positivity)]

/--
lemma `f_int_negSucc` / 引理 `f_int_negSucc`

English:
lemma f_int_negSucc
  given: (k : Nat) {a : Real} (ha : a <= 1) (t : Real) (n : Nat)
  proof: by
  have : (Int.negSucc n) + a = -(n + (1 - a)) := by { push_cast; ring }
  rw [f_int]; rw [f_nat]; rw [this]; rw [abs_neg]; rw [neg_sq]; rw [abs_of_nonneg (by linarith)]

中文:
引理 f_int_negSucc
  条件: (k : 自然数) {a : 实数} (ha : a <= 1) (t : 实数) (n : 自然数)
  证明: by
  have : (Int.negSucc n) + a = -(n + (1 - a)) := by { push_cast; ring }
  rw [f_int]; rw [f_nat]; rw [this]; rw [abs_neg]; rw [neg_sq]; rw [abs_of_nonneg (by linarith)]

Depends on / 依赖: Int.negSucc, abs_neg, abs_of_nonneg, f_int, f_nat, negSucc, neg_sq
-/
lemma f_int_negSucc (k : Nat) {a : Real} (ha : a <= 1) (t : Real) (n : Nat) :
    f_int k a t (Int.negSucc n) = f_nat k (1 - a) t n := by
  have : (Int.negSucc n) + a = -(n + (1 - a)) := by { push_cast; ring }
  rw [f_int]; rw [f_nat]; rw [this]; rw [abs_neg]; rw [neg_sq]; rw [abs_of_nonneg (by linarith)]

/--
lemma `summable_f_int` / 引理 `summable_f_int`

English:
lemma summable_f_int
  given: (k : Nat) (a : Real) {t : Real} (ht : 0 < t)
  statement: Summable (f_int k a t)
  proof: by
  apply Summable.of_norm
  suffices forall n, ‖f_int k a t n‖ = ‖(Int.rec (f_nat k a t) (f_nat k (1 - a) t) : Int -> Real) n‖ from
    funext this ▸ (HasSum.int_rec (summable_f_nat k a ht).hasSum
      (summable_f_nat k (1 - a) ht).hasSum).summable.norm
  intro n
  rcases n with - | m
  · simp on

中文:
引理 summable_f_int
  条件: (k : 自然数) (a : 实数) {t : 实数} (ht : 0 < t)
  结论: Summable (f_int k a t)
  证明: by
  apply Summable.of_norm
  suffices forall n, ‖f_int k a t n‖ = ‖(Int.rec (f_nat k a t) (f_nat k (1 - a) t) : Int -> Real) n‖ from
    funext this ▸ (HasSum.int_rec (summable_f_nat k a ht).hasSum
      (summable_f_nat k (1 - a) ht).hasSum).summable.norm
  intro n
  rcases n with - | m
  · simp on

Depends on / 依赖: HasSum, HasSum.int_rec, Int.cast_natCast, Int.cast_negSucc, Int.ofNat_eq_natCast, Int.rec, Summable, Summable.of_norm, abs_abs, abs_pow, cast_natCast, cast_negSucc, f_int, f_nat, hasSum, int_rec, norm_eq_abs, norm_mul, ofNat_eq_natCast, of_norm
-/
lemma summable_f_int (k : Nat) (a : Real) {t : Real} (ht : 0 < t) : Summable (f_int k a t) := by
  apply Summable.of_norm
  suffices forall n, ‖f_int k a t n‖ = ‖(Int.rec (f_nat k a t) (f_nat k (1 - a) t) : Int -> Real) n‖ from
    funext this ▸ (HasSum.int_rec (summable_f_nat k a ht).hasSum
      (summable_f_nat k (1 - a) ht).hasSum).summable.norm
  intro n
  rcases n with - | m
  · simp only [f_int, f_nat, Int.ofNat_eq_natCast, Int.cast_natCast, norm_mul, norm_eq_abs, abs_pow,
      abs_abs]
  · simp only [f_int, f_nat, Int.cast_negSucc, norm_mul, norm_eq_abs, abs_pow, abs_abs,
      (by { push_cast; ring } : -↑(m + 1) + a = -(m + (1 - a))), abs_neg, neg_sq]

/--
Definition of `F_int` / `F_int` 的定义

English:
definition F_int
  signature: (k : Nat) (a : UnitAddCircle) (t : Real)
  body: (show Function.Periodic (fun b => ∑' (n : Int), f_int k b t n) 1 by
    intro b
    simp_rw [← (Equiv.addRight (1 : Int)).tsum_eq (f := fun n => f_int k b t n)]
    simp only [f_int, ← add_assoc, add_comm, Equiv.coe_addRight, Int.cast_add, Int.cast_one]).lift a

中文:
定义 F_int
  签名: (k : 自然数) (a : UnitAddCircle) (t : 实数)
  定义体: (show Function.Periodic (fun b => ∑' (n : Int), f_int k b t n) 1 by
    intro b
    simp_rw [← (Equiv.addRight (1 : Int)).tsum_eq (f := fun n => f_int k b t n)]
    simp only [f_int, ← add_assoc, add_comm, Equiv.coe_addRight, Int.cast_add, Int.cast_one]).lift a

Depends on / 依赖: Equiv.addRight, Equiv.coe_addRight, Function, Function.Periodic, Int.cast_add, Int.cast_one, Periodic, addRight, add_assoc, add_comm, cast_add, cast_one, coe_addRight, f_int, simp_rw, tsum_eq
-/
def F_int (k : Nat) (a : UnitAddCircle) (t : Real) : Real :=
  (show Function.Periodic (fun b => ∑' (n : Int), f_int k b t n) 1 by
    intro b
    simp_rw [← (Equiv.addRight (1 : Int)).tsum_eq (f := fun n => f_int k b t n)]
    simp only [f_int, ← add_assoc, add_comm, Equiv.coe_addRight, Int.cast_add, Int.cast_one]).lift a

/--
lemma `F_int_eq_of_mem_Icc` / 引理 `F_int_eq_of_mem_Icc`

English:
lemma F_int_eq_of_mem_Icc
  given: (k : Nat) {a : Real} (ha : a in Icc 0 1) {t : Real} (ht : 0 < t)
  proof: by
  simp only [F_int, F_nat, Function.Periodic.lift_coe]
  convert!
    ((summable_f_nat k a ht).hasSum.int_rec (summable_f_nat k (1 - a) ht).hasSum).tsum_eq using
    3 with n
  cases n
  · rw [f_int_ofNat _ ha.1]
  · rw [f_int_negSucc _ ha.2]

中文:
引理 F_int_eq_of_mem_Icc
  条件: (k : 自然数) {a : 实数} (ha : a in 闭区间 0 1) {t : 实数} (ht : 0 < t)
  证明: by
  simp only [F_int, F_nat, Function.Periodic.lift_coe]
  convert!
    ((summable_f_nat k a ht).hasSum.int_rec (summable_f_nat k (1 - a) ht).hasSum).tsum_eq using
    3 with n
  cases n
  · rw [f_int_ofNat _ ha.1]
  · rw [f_int_negSucc _ ha.2]

Depends on / 依赖: F_int, F_nat, Function, Function.Periodic.lift_coe, Periodic, convert, f_int_negSucc, f_int_ofNat, hasSum, hasSum.int_rec, int_rec, lift_coe, summable_f_nat, tsum_eq
-/
lemma F_int_eq_of_mem_Icc (k : Nat) {a : Real} (ha : a in Icc 0 1) {t : Real} (ht : 0 < t) :
    F_int k a t = (F_nat k a t) + (F_nat k (1 - a) t) := by
  simp only [F_int, F_nat, Function.Periodic.lift_coe]
  convert!
    ((summable_f_nat k a ht).hasSum.int_rec (summable_f_nat k (1 - a) ht).hasSum).tsum_eq using
    3 with n
  cases n
  · rw [f_int_ofNat _ ha.1]
  · rw [f_int_negSucc _ ha.2]

/--
lemma `isBigO_atTop_F_int_zero_sub` / 引理 `isBigO_atTop_F_int_zero_sub`

English:
lemma isBigO_atTop_F_int_zero_sub
  given: (a : UnitAddCircle)
  statement: exists p, 0 < p ∧
  proof: by
  obtain ⟨a, ha, rfl⟩ := a.eq_coe_Ico
  obtain ⟨p, hp, hp'⟩ := isBigO_atTop_F_nat_zero_sub ha.1
  obtain ⟨q, hq, hq'⟩ := isBigO_atTop_F_nat_zero_sub (sub_nonneg.mpr ha.2.le)
  simp_rw [AddCircle.coe_eq_zero_iff_of_mem_Ico ha]
  simp_rw [eq_false_intro (by linarith [ha.2] : 1 - a != 0), if_false, 

中文:
引理 isBigO_atTop_F_int_zero_sub
  条件: (a : UnitAddCircle)
  结论: 存在 p, 0 < p ∧
  证明: by
  obtain ⟨a, ha, rfl⟩ := a.eq_coe_Ico
  obtain ⟨p, hp, hp'⟩ := isBigO_atTop_F_nat_zero_sub ha.1
  obtain ⟨q, hq, hq'⟩ := isBigO_atTop_F_nat_zero_sub (sub_nonneg.mpr ha.2.le)
  simp_rw [AddCircle.coe_eq_zero_iff_of_mem_Ico ha]
  simp_rw [eq_false_intro (by linarith [ha.2] : 1 - a != 0), if_false, 

Depends on / 依赖: AddCircle, AddCircle.coe_eq_zero_iff_of_mem_Ico, F_int, F_nat, a.eq_coe_Ico, coe_eq_zero_iff_of_mem_Ico, eq_coe_Ico, eq_false_intro, filter_upwards, if_false, isBigO_atTop_F_nat_zero_sub, lt_min, simp_rw, sub_nonneg, sub_nonneg.mpr, sub_zero
-/
lemma isBigO_atTop_F_int_zero_sub (a : UnitAddCircle) : exists p, 0 < p ∧
    (fun t => F_int 0 a t - (if a = 0 then 1 else 0)) =O[atTop] fun t => exp (-p * t) := by
  obtain ⟨a, ha, rfl⟩ := a.eq_coe_Ico
  obtain ⟨p, hp, hp'⟩ := isBigO_atTop_F_nat_zero_sub ha.1
  obtain ⟨q, hq, hq'⟩ := isBigO_atTop_F_nat_zero_sub (sub_nonneg.mpr ha.2.le)
  simp_rw [AddCircle.coe_eq_zero_iff_of_mem_Ico ha]
  simp_rw [eq_false_intro (by linarith [ha.2] : 1 - a != 0), if_false, sub_zero] at hq'
  refine ⟨_, lt_min hp hq, ?_⟩
  have : (fun t => F_int 0 a t - (if a = 0 then 1 else 0)) =ᶠ[atTop]
      fun t => (F_nat 0 a t - (if a = 0 then 1 else 0)) + F_nat 0 (1 - a) t := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [F_int_eq_of_mem_Icc 0 (Ico_subset_Icc_self ha) ht]
    ring
  refine this.isBigO.trans ((hp'.trans ?_).add (hq'.trans ?_)) <;>
  apply isBigO_exp_neg_mul_of_le
  exacts [min_le_left .., min_le_right ..]

/--
lemma `isBigO_atTop_F_int_one` / 引理 `isBigO_atTop_F_int_one`

English:
lemma isBigO_atTop_F_int_one
  given: (a : UnitAddCircle)
  statement: exists p, 0 < p ∧
  proof: by
  obtain ⟨a, ha, rfl⟩ := a.eq_coe_Ico
  obtain ⟨p, hp, hp'⟩ := isBigO_atTop_F_nat_one ha.1
  obtain ⟨q, hq, hq'⟩ := isBigO_atTop_F_nat_one (sub_nonneg.mpr ha.2.le)
  refine ⟨_, lt_min hp hq, ?_⟩
  have : F_int 1 a =ᶠ[atTop] fun t => F_nat 1 a t + F_nat 1 (1 - a) t := by
    filter_upwards [eventu

中文:
引理 isBigO_atTop_F_int_one
  条件: (a : UnitAddCircle)
  结论: 存在 p, 0 < p ∧
  证明: by
  obtain ⟨a, ha, rfl⟩ := a.eq_coe_Ico
  obtain ⟨p, hp, hp'⟩ := isBigO_atTop_F_nat_one ha.1
  obtain ⟨q, hq, hq'⟩ := isBigO_atTop_F_nat_one (sub_nonneg.mpr ha.2.le)
  refine ⟨_, lt_min hp hq, ?_⟩
  have : F_int 1 a =ᶠ[atTop] fun t => F_nat 1 a t + F_nat 1 (1 - a) t := by
    filter_upwards [eventu

Depends on / 依赖: F_int, F_int_eq_of_mem_Icc, F_nat, Ico_subset_Icc_self, a.eq_coe_Ico, eq_coe_Ico, eventually_gt_atTop, exacts, filter_upwards, isBigO, isBigO_atTop_F_nat_one, isBigO_exp_neg_mul_of_le, lt_min, min_le_left, min_le_righ, sub_nonneg, sub_nonneg.mpr, this.isBigO.trans
-/
lemma isBigO_atTop_F_int_one (a : UnitAddCircle) : exists p, 0 < p ∧
    F_int 1 a =O[atTop] fun t => exp (-p * t) := by
  obtain ⟨a, ha, rfl⟩ := a.eq_coe_Ico
  obtain ⟨p, hp, hp'⟩ := isBigO_atTop_F_nat_one ha.1
  obtain ⟨q, hq, hq'⟩ := isBigO_atTop_F_nat_one (sub_nonneg.mpr ha.2.le)
  refine ⟨_, lt_min hp hq, ?_⟩
  have : F_int 1 a =ᶠ[atTop] fun t => F_nat 1 a t + F_nat 1 (1 - a) t := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact F_int_eq_of_mem_Icc 1 (Ico_subset_Icc_self ha) ht
  refine this.isBigO.trans ((hp'.trans ?_).add (hq'.trans ?_)) <;>
  apply isBigO_exp_neg_mul_of_le
  exacts [min_le_left .., min_le_right ..]

end int

end HurwitzKernelBounds
