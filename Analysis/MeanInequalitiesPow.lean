/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Mean value inequalities

In this file we prove several mean inequalities for finite sums. Versions for integrals of some of
these inequalities are available in `MeasureTheory.MeanInequalities`.

## Main theorems: generalized mean inequality

The inequality says that for two non-negative vectors $w$ and $z$ with $\sum_{i\in s} w_i=1$
and $p ≤ q$ we have
$$
\sqrt[p]{\sum_{i\in s} w_i z_i^p} ≤ \sqrt[q]{\sum_{i\in s} w_i z_i^q}.
$$

Currently we only prove this inequality for $p=1$. As in the rest of `Mathlib`, we provide
different theorems for natural exponents (`pow_arith_mean_le_arith_mean_pow`), integer exponents
(`zpow_arith_mean_le_arith_mean_zpow`), and real exponents (`rpow_arith_mean_le_arith_mean_rpow` and
`arith_mean_le_rpow_mean`). In the first two cases we prove
$$
\left(\sum_{i\in s} w_i z_i\right)^n ≤ \sum_{i\in s} w_i z_i^n
$$
in order to avoid using real exponents. For real exponents we prove both this and standard versions.

## TODO

- each inequality `A ≤ B` should come with a theorem `A = B ↔ _`; one of the ways to prove them
  is to define `StrictConvexOn` functions.
- generalized mean inequality with any `p ≤ q`, including negative numbers;
- prove that the power mean tends to the geometric mean as the exponent tends to zero.

-/

public section


universe u v

open Finset NNReal ENNReal

noncomputable section

variable {ι : Type u} (s : Finset ι)

namespace Real

/--
theorem `pow_arith_mean_le_arith_mean_pow` / 定理 `pow_arith_mean_le_arith_mean_pow`

English:
theorem pow_arith_mean_le_arith_mean_pow
  statement: (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
  proof: (convexOn_pow n).map_sum_le hw hw' hz

中文:
定理 pow_arith_mean_le_arith_mean_pow
  结论: (w z : ι -> 实数) (hw : 对任意 i in s, 0 <= w i)
  证明: (convexOn_pow n).map_sum_le hw hw' hz

Depends on / 依赖: convexOn_pow, map_sum_le
-/
theorem pow_arith_mean_le_arith_mean_pow (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
    (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) (n : Nat) :
    (∑ i in s, w i * z i) ^ n <= ∑ i in s, w i * z i ^ n :=
  (convexOn_pow n).map_sum_le hw hw' hz

/--
theorem `pow_arith_mean_le_arith_mean_pow_of_even` / 定理 `pow_arith_mean_le_arith_mean_pow_of_even`

English:
theorem pow_arith_mean_le_arith_mean_pow_of_even
  statement: (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
  proof: hn.convexOn_pow.map_sum_le hw hw' fun _ _ => Set.mem_univ _

中文:
定理 pow_arith_mean_le_arith_mean_pow_of_even
  结论: (w z : ι -> 实数) (hw : 对任意 i in s, 0 <= w i)
  证明: hn.convexOn_pow.map_sum_le hw hw' fun _ _ => Set.mem_univ _

Depends on / 依赖: Set.mem_univ, convexOn_pow, hn.convexOn_pow.map_sum_le, map_sum_le, mem_univ
-/
theorem pow_arith_mean_le_arith_mean_pow_of_even (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
    (hw' : ∑ i in s, w i = 1) {n : Nat} (hn : Even n) :
    (∑ i in s, w i * z i) ^ n <= ∑ i in s, w i * z i ^ n :=
  hn.convexOn_pow.map_sum_le hw hw' fun _ _ => Set.mem_univ _

/--
theorem `zpow_arith_mean_le_arith_mean_zpow` / 定理 `zpow_arith_mean_le_arith_mean_zpow`

English:
theorem zpow_arith_mean_le_arith_mean_zpow
  statement: (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
  proof: (convexOn_zpow m).map_sum_le hw hw' hz

中文:
定理 zpow_arith_mean_le_arith_mean_zpow
  结论: (w z : ι -> 实数) (hw : 对任意 i in s, 0 <= w i)
  证明: (convexOn_zpow m).map_sum_le hw hw' hz

Depends on / 依赖: convexOn_zpow, map_sum_le
-/
theorem zpow_arith_mean_le_arith_mean_zpow (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
    (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 < z i) (m : Int) :
    (∑ i in s, w i * z i) ^ m <= ∑ i in s, w i * z i ^ m :=
  (convexOn_zpow m).map_sum_le hw hw' hz

/--
theorem `rpow_arith_mean_le_arith_mean_rpow` / 定理 `rpow_arith_mean_le_arith_mean_rpow`

English:
theorem rpow_arith_mean_le_arith_mean_rpow
  statement: (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
  proof: (convexOn_rpow hp).map_sum_le hw hw' hz

中文:
定理 rpow_arith_mean_le_arith_mean_rpow
  结论: (w z : ι -> 实数) (hw : 对任意 i in s, 0 <= w i)
  证明: (convexOn_rpow hp).map_sum_le hw hw' hz

Depends on / 依赖: convexOn_rpow, map_sum_le
-/
theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
    (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) {p : Real} (hp : 1 <= p) :
    (∑ i in s, w i * z i) ^ p <= ∑ i in s, w i * z i ^ p :=
  (convexOn_rpow hp).map_sum_le hw hw' hz

/--
theorem `arith_mean_le_rpow_mean` / 定理 `arith_mean_le_rpow_mean`

English:
theorem arith_mean_le_rpow_mean
  statement: (w z : ι -> Real) (hw : forall i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1)
  proof: by
  have : 0 < p := by positivity
  rw [← rpow_le_rpow_iff _ _ this]; rw [← rpow_mul]; rw [one_div_mul_cancel (ne_of_gt this)]; rw [rpow_one]
  · exact rpow_arith_mean_le_arith_mean_rpow s w z hw hw' hz hp
  all_goals
    apply_rules [sum_nonneg, rpow_nonneg]
    intro i hi
    positivity [hw i hi, hz i hi]

中文:
定理 arith_mean_le_rpow_mean
  结论: (w z : ι -> 实数) (hw : 对任意 i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1)
  证明: by
  have : 0 < p := by positivity
  rw [← rpow_le_rpow_iff _ _ this]; rw [← rpow_mul]; rw [one_div_mul_cancel (ne_of_gt this)]; rw [rpow_one]
  · exact rpow_arith_mean_le_arith_mean_rpow s w z hw hw' hz hp
  all_goals
    apply_rules [sum_nonneg, rpow_nonneg]
    intro i hi
    positivity [hw i hi, hz i hi]

Depends on / 依赖: all_goals, apply_rules, ne_of_gt, one_div_mul_cancel, rpow_arith_mean_le_arith_mean_rpow, rpow_le_rpow_iff, rpow_mul, rpow_nonneg, rpow_one, sum_nonneg
-/
theorem arith_mean_le_rpow_mean (w z : ι -> Real) (hw : forall i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1)
    (hz : forall i in s, 0 <= z i) {p : Real} (hp : 1 <= p) :
    ∑ i in s, w i * z i <= (∑ i in s, w i * z i ^ p) ^ (1 / p) := by
  have : 0 < p := by positivity
  rw [← rpow_le_rpow_iff _ _ this]; rw [← rpow_mul]; rw [one_div_mul_cancel (ne_of_gt this)]; rw [rpow_one]
  · exact rpow_arith_mean_le_arith_mean_rpow s w z hw hw' hz hp
  all_goals
    apply_rules [sum_nonneg, rpow_nonneg]
    intro i hi
    positivity [hw i hi, hz i hi]

end Real

namespace NNReal

/--
theorem `pow_arith_mean_le_arith_mean_pow` / 定理 `pow_arith_mean_le_arith_mean_pow`

English:
theorem pow_arith_mean_le_arith_mean_pow
  given: (w z : ι -> Real>=0) (hw' : ∑ i in s, w i = 1) (n : Nat)
  proof: mod_cast
    Real.pow_arith_mean_le_arith_mean_pow s _ _ (fun i _ => (w i).coe_nonneg)
      (mod_cast hw') (fun i _ => (z i).coe_nonneg) n

中文:
定理 pow_arith_mean_le_arith_mean_pow
  条件: (w z : ι -> 实数>=0) (hw' : ∑ i in s, w i = 1) (n : 自然数)
  证明: mod_cast
    Real.pow_arith_mean_le_arith_mean_pow s _ _ (fun i _ => (w i).coe_nonneg)
      (mod_cast hw') (fun i _ => (z i).coe_nonneg) n

Depends on / 依赖: Real.pow_arith_mean_le_arith_mean_pow, coe_nonneg, mod_cast, pow_arith_mean_le_arith_mean_pow
-/
theorem pow_arith_mean_le_arith_mean_pow (w z : ι -> Real>=0) (hw' : ∑ i in s, w i = 1) (n : Nat) :
    (∑ i in s, w i * z i) ^ n <= ∑ i in s, w i * z i ^ n :=
  mod_cast
    Real.pow_arith_mean_le_arith_mean_pow s _ _ (fun i _ => (w i).coe_nonneg)
      (mod_cast hw') (fun i _ => (z i).coe_nonneg) n

/--
theorem `rpow_arith_mean_le_arith_mean_rpow` / 定理 `rpow_arith_mean_le_arith_mean_rpow`

English:
theorem rpow_arith_mean_le_arith_mean_rpow
  statement: (w z : ι -> Real>=0) (hw' : ∑ i in s, w i = 1) {p : Real}
  proof: mod_cast
    Real.rpow_arith_mean_le_arith_mean_rpow s _ _ (fun i _ => (w i).coe_nonneg)
      (mod_cast hw') (fun i _ => (z i).coe_nonneg) hp

中文:
定理 rpow_arith_mean_le_arith_mean_rpow
  结论: (w z : ι -> 实数>=0) (hw' : ∑ i in s, w i = 1) {p : 实数}
  证明: mod_cast
    Real.rpow_arith_mean_le_arith_mean_rpow s _ _ (fun i _ => (w i).coe_nonneg)
      (mod_cast hw') (fun i _ => (z i).coe_nonneg) hp

Depends on / 依赖: Real.rpow_arith_mean_le_arith_mean_rpow, coe_nonneg, mod_cast, rpow_arith_mean_le_arith_mean_rpow
-/
theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι -> Real>=0) (hw' : ∑ i in s, w i = 1) {p : Real}
    (hp : 1 <= p) : (∑ i in s, w i * z i) ^ p <= ∑ i in s, w i * z i ^ p :=
  mod_cast
    Real.rpow_arith_mean_le_arith_mean_rpow s _ _ (fun i _ => (w i).coe_nonneg)
      (mod_cast hw') (fun i _ => (z i).coe_nonneg) hp

/--
theorem `rpow_arith_mean_le_arith_mean2_rpow` / 定理 `rpow_arith_mean_le_arith_mean2_rpow`

English:
theorem rpow_arith_mean_le_arith_mean2_rpow
  statement: (w₁ w₂ z₁ z₂ : Real>=0) (hw' : w₁ + w₂ = 1) {p : Real}
  proof: by
  have h := rpow_arith_mean_le_arith_mean_rpow univ ![w₁, w₂] ![z₁, z₂] ?_ hp
  · simpa [Fin.sum_univ_succ] using h
  · simp [hw', Fin.sum_univ_succ]

中文:
定理 rpow_arith_mean_le_arith_mean2_rpow
  结论: (w₁ w₂ z₁ z₂ : 实数>=0) (hw' : w₁ + w₂ = 1) {p : 实数}
  证明: by
  have h := rpow_arith_mean_le_arith_mean_rpow univ ![w₁, w₂] ![z₁, z₂] ?_ hp
  · simpa [Fin.sum_univ_succ] using h
  · simp [hw', Fin.sum_univ_succ]

Depends on / 依赖: Fin.sum_univ_succ, rpow_arith_mean_le_arith_mean_rpow, sum_univ_succ
-/
theorem rpow_arith_mean_le_arith_mean2_rpow (w₁ w₂ z₁ z₂ : Real>=0) (hw' : w₁ + w₂ = 1) {p : Real}
    (hp : 1 <= p) : (w₁ * z₁ + w₂ * z₂) ^ p <= w₁ * z₁ ^ p + w₂ * z₂ ^ p := by
  have h := rpow_arith_mean_le_arith_mean_rpow univ ![w₁, w₂] ![z₁, z₂] ?_ hp
  · simpa [Fin.sum_univ_succ] using h
  · simp [hw', Fin.sum_univ_succ]

/--
theorem `rpow_add_le_mul_rpow_add_rpow` / 定理 `rpow_add_le_mul_rpow_add_rpow`

English:
theorem rpow_add_le_mul_rpow_add_rpow
  given: (z₁ z₂ : Real>=0) {p : Real} (hp : 1 <= p)
  proof: by
  rcases eq_or_lt_of_le hp with (rfl | h'p)
  · simp only [rpow_one, sub_self, rpow_zero, one_mul]; rfl
  convert!
    rpow_arith_mean_le_arith_mean2_rpow (1 / 2) (1 / 2) (2 * z₁) (2 * z₂) (add_halves 1) hp using 1
  · simp only [one_div, inv_mul_cancel_left₀, Ne, two_ne_zero,
      not_false_iff]
  · have A : p - 1 != 0 := ne_of_gt (sub_pos.2 h'p)
    simp only [mul_rpow, rpow_sub' A, rpow_one]
    ring

中文:
定理 rpow_add_le_mul_rpow_add_rpow
  条件: (z₁ z₂ : 实数>=0) {p : 实数} (hp : 1 <= p)
  证明: by
  rcases eq_or_lt_of_le hp with (rfl | h'p)
  · simp only [rpow_one, sub_self, rpow_zero, one_mul]; rfl
  convert!
    rpow_arith_mean_le_arith_mean2_rpow (1 / 2) (1 / 2) (2 * z₁) (2 * z₂) (add_halves 1) hp using 1
  · simp only [one_div, inv_mul_cancel_left₀, Ne, two_ne_zero,
      not_false_iff]
  · have A : p - 1 != 0 := ne_of_gt (sub_pos.2 h'p)
    simp only [mul_rpow, rpow_sub' A, rpow_one]
    ring

Depends on / 依赖: add_halves, convert, eq_or_lt_of_le, mul_rpow, ne_of_gt, not_false_iff, one_div, one_mul, rpow_arith_mean_le_arith_mean2_rpow, rpow_one, rpow_sub, rpow_zero, sub_pos, sub_self, two_ne_zero
-/
theorem rpow_add_le_mul_rpow_add_rpow (z₁ z₂ : Real>=0) {p : Real} (hp : 1 <= p) :
    (z₁ + z₂) ^ p <= (2 : Real>=0) ^ (p - 1) * (z₁ ^ p + z₂ ^ p) := by
  rcases eq_or_lt_of_le hp with (rfl | h'p)
  · simp only [rpow_one, sub_self, rpow_zero, one_mul]; rfl
  convert!
    rpow_arith_mean_le_arith_mean2_rpow (1 / 2) (1 / 2) (2 * z₁) (2 * z₂) (add_halves 1) hp using 1
  · simp only [one_div, inv_mul_cancel_left₀, Ne, two_ne_zero,
      not_false_iff]
  · have A : p - 1 != 0 := ne_of_gt (sub_pos.2 h'p)
    simp only [mul_rpow, rpow_sub' A, rpow_one]
    ring

/--
theorem `arith_mean_le_rpow_mean` / 定理 `arith_mean_le_rpow_mean`

English:
theorem arith_mean_le_rpow_mean
  given: (w z : ι -> Real>=0) (hw' : ∑ i in s, w i = 1) {p : Real} (hp : 1 <= p)
  proof: mod_cast
    Real.arith_mean_le_rpow_mean s _ _ (fun i _ => (w i).coe_nonneg) (mod_cast hw')
      (fun i _ => (z i).coe_nonneg) hp

中文:
定理 arith_mean_le_rpow_mean
  条件: (w z : ι -> 实数>=0) (hw' : ∑ i in s, w i = 1) {p : 实数} (hp : 1 <= p)
  证明: mod_cast
    Real.arith_mean_le_rpow_mean s _ _ (fun i _ => (w i).coe_nonneg) (mod_cast hw')
      (fun i _ => (z i).coe_nonneg) hp

Depends on / 依赖: Real.arith_mean_le_rpow_mean, arith_mean_le_rpow_mean, coe_nonneg, mod_cast
-/
theorem arith_mean_le_rpow_mean (w z : ι -> Real>=0) (hw' : ∑ i in s, w i = 1) {p : Real} (hp : 1 <= p) :
    ∑ i in s, w i * z i <= (∑ i in s, w i * z i ^ p) ^ (1 / p) :=
  mod_cast
    Real.arith_mean_le_rpow_mean s _ _ (fun i _ => (w i).coe_nonneg) (mod_cast hw')
      (fun i _ => (z i).coe_nonneg) hp

/--
theorem `add_rpow_le_one_of_add_le_one` / 定理 `add_rpow_le_one_of_add_le_one`

English:
theorem add_rpow_le_one_of_add_le_one
  given: {p : Real} (a b : Real>=0) (hab : a + b <= 1) (hp1 : 1 <= p)
  proof: by
  have h_le_one : forall x : Real>=0, x <= 1 -> x ^ p <= x := fun x hx => rpow_le_self_of_le_one hx hp1
  have ha : a <= 1 := (self_le_add_right a b).trans hab
  have hb : b <= 1 := (self_le_add_left b a).trans hab
  exact (add_le_add (h_le_one a ha) (h_le_one b hb)).trans hab

中文:
定理 add_rpow_le_one_of_add_le_one
  条件: {p : 实数} (a b : 实数>=0) (hab : a + b <= 1) (hp1 : 1 <= p)
  证明: by
  have h_le_one : forall x : Real>=0, x <= 1 -> x ^ p <= x := fun x hx => rpow_le_self_of_le_one hx hp1
  have ha : a <= 1 := (self_le_add_right a b).trans hab
  have hb : b <= 1 := (self_le_add_left b a).trans hab
  exact (add_le_add (h_le_one a ha) (h_le_one b hb)).trans hab
-/
private theorem add_rpow_le_one_of_add_le_one {p : Real} (a b : Real>=0) (hab : a + b <= 1) (hp1 : 1 <= p) :
    a ^ p + b ^ p <= 1 := by
  have h_le_one : forall x : Real>=0, x <= 1 -> x ^ p <= x := fun x hx => rpow_le_self_of_le_one hx hp1
  have ha : a <= 1 := (self_le_add_right a b).trans hab
  have hb : b <= 1 := (self_le_add_left b a).trans hab
  exact (add_le_add (h_le_one a ha) (h_le_one b hb)).trans hab

/--
theorem `add_rpow_le_rpow_add` / 定理 `add_rpow_le_rpow_add`

English:
theorem add_rpow_le_rpow_add
  given: {p : Real} (a b : Real>=0) (hp1 : 1 <= p)
  statement: a ^ p + b ^ p <= (a + b) ^ p
  proof: by
  have hp_pos : 0 < p := by positivity
  by_cases h_zero : a + b = 0
  · simp [add_eq_zero.mp h_zero, hp_pos.ne']
  have h_nonzero : ¬(a = 0 ∧ b = 0) := by rwa [add_eq_zero] at h_zero
  have h_add : a / (a + b) + b / (a + b) = 1 := by rw [← add_div, div_self h_zero]
  have h := add_rpow_le_one_of_add_le_one (a / (a + b)) (b / (a + b)) h_add.le hp1
  rw [div_rpow a (a + b)]; rw [div_rpow b (a + b)] at h
  have hab_0 : (a + b) ^ p != 0 := by simp [h_nonzero]
  have h_mul : (a + b) ^ p * (a ^ p / (a + b) ^ p + b ^ p / (a + b) ^ p) <= (a + b) ^ p := by
    nth_rw 4 [← mul_one ((a + b) ^ p)]; gcongr
  rwa [div_eq_mul_inv, div_eq_mul_inv, mul_add, mul_comm (a ^ p), mul_comm (b ^ p), ← mul_assoc, ←
    mul_assoc, mul_inv_cancel₀ hab_0, one_mul, one_mul] at h_mul

中文:
定理 add_rpow_le_rpow_add
  条件: {p : 实数} (a b : 实数>=0) (hp1 : 1 <= p)
  结论: a ^ p + b ^ p <= (a + b) ^ p
  证明: by
  have hp_pos : 0 < p := by positivity
  by_cases h_zero : a + b = 0
  · simp [add_eq_zero.mp h_zero, hp_pos.ne']
  have h_nonzero : ¬(a = 0 ∧ b = 0) := by rwa [add_eq_zero] at h_zero
  have h_add : a / (a + b) + b / (a + b) = 1 := by rw [← add_div, div_self h_zero]
  have h := add_rpow_le_one_of_add_le_one (a / (a + b)) (b / (a + b)) h_add.le hp1
  rw [div_rpow a (a + b)]; rw [div_rpow b (a + b)] at h
  have hab_0 : (a + b) ^ p != 0 := by simp [h_nonzero]
  have h_mul : (a + b) ^ p * (a ^ p / (a + b) ^ p + b ^ p / (a + b) ^ p) <= (a + b) ^ p := by
    nth_rw 4 [← mul_one ((a + b) ^ p)]; gcongr
  rwa [div_eq_mul_inv, div_eq_mul_inv, mul_add, mul_comm (a ^ p), mul_comm (b ^ p), ← mul_assoc, ←
    mul_assoc, mul_inv_cancel₀ hab_0, one_mul, one_mul] at h_mul

Depends on / 依赖: add_div, add_eq_zero, add_eq_zero.mp, add_rpow_le_one_of_add_le_one, div_rpow, div_self, h_add, h_add.le, h_mul, h_nonzero, h_zero, hab_0, hp_pos, hp_pos.ne
-/
theorem add_rpow_le_rpow_add {p : Real} (a b : Real>=0) (hp1 : 1 <= p) : a ^ p + b ^ p <= (a + b) ^ p := by
  have hp_pos : 0 < p := by positivity
  by_cases h_zero : a + b = 0
  · simp [add_eq_zero.mp h_zero, hp_pos.ne']
  have h_nonzero : ¬(a = 0 ∧ b = 0) := by rwa [add_eq_zero] at h_zero
  have h_add : a / (a + b) + b / (a + b) = 1 := by rw [← add_div, div_self h_zero]
  have h := add_rpow_le_one_of_add_le_one (a / (a + b)) (b / (a + b)) h_add.le hp1
  rw [div_rpow a (a + b)]; rw [div_rpow b (a + b)] at h
  have hab_0 : (a + b) ^ p != 0 := by simp [h_nonzero]
  have h_mul : (a + b) ^ p * (a ^ p / (a + b) ^ p + b ^ p / (a + b) ^ p) <= (a + b) ^ p := by
    nth_rw 4 [← mul_one ((a + b) ^ p)]; gcongr
  rwa [div_eq_mul_inv, div_eq_mul_inv, mul_add, mul_comm (a ^ p), mul_comm (b ^ p), ← mul_assoc, ←
    mul_assoc, mul_inv_cancel₀ hab_0, one_mul, one_mul] at h_mul

/--
theorem `rpow_add_rpow_le_add` / 定理 `rpow_add_rpow_le_add`

English:
theorem rpow_add_rpow_le_add
  given: {p : Real} (a b : Real>=0) (hp1 : 1 <= p)
  proof: by
  rw [one_div]; rw [← @NNReal.le_rpow_inv_iff _ _ p⁻¹ (by simp [lt_of_lt_of_le zero_lt_one hp1]), inv_inv]
  exact add_rpow_le_rpow_add _ _ hp1

中文:
定理 rpow_add_rpow_le_add
  条件: {p : 实数} (a b : 实数>=0) (hp1 : 1 <= p)
  证明: by
  rw [one_div]; rw [← @NNReal.le_rpow_inv_iff _ _ p⁻¹ (by simp [lt_of_lt_of_le zero_lt_one hp1]), inv_inv]
  exact add_rpow_le_rpow_add _ _ hp1

Depends on / 依赖: NNReal, NNReal.le_rpow_inv_iff, add_rpow_le_rpow_add, inv_inv, le_rpow_inv_iff, lt_of_lt_of_le, one_div, zero_lt_one
-/
theorem rpow_add_rpow_le_add {p : Real} (a b : Real>=0) (hp1 : 1 <= p) :
    (a ^ p + b ^ p) ^ (1 / p) <= a + b := by
  rw [one_div]; rw [← @NNReal.le_rpow_inv_iff _ _ p⁻¹ (by simp [lt_of_lt_of_le zero_lt_one hp1]), inv_inv]
  exact add_rpow_le_rpow_add _ _ hp1

/--
theorem `rpow_add_rpow_le` / 定理 `rpow_add_rpow_le`

English:
theorem rpow_add_rpow_le
  given: {p q : Real} (a b : Real>=0) (hp_pos : 0 < p) (hpq : p <= q)
  proof: by
  have h_rpow : forall a : Real>=0, a ^ q = (a ^ p) ^ (q / p) := fun a => by
    rw [← NNReal.rpow_mul]; rw [div_eq_inv_mul]; rw [← mul_assoc]; rw [mul_inv_cancel₀ hp_pos.ne.symm]; rw [one_mul]
  have h_rpow_add_rpow_le_add :
    ((a ^ p) ^ (q / p) + (b ^ p) ^ (q / p)) ^ (1 / (q / p)) <= a ^ p + b ^ p := by
    refine rpow_add_rpow_le_add (a ^ p) (b ^ p) ?_
    rwa [one_le_div hp_pos]
  rw [h_rpow a]; rw [h_rpow b]; rw [one_div p]; rw [NNReal.le_rpow_inv_iff hp_pos]; rw [← NNReal.rpow_mul]; rw [mul_comm]; rw [mul_one_div]
  rwa [one_div_div] at h_rpow_add_rpow_le_add

中文:
定理 rpow_add_rpow_le
  条件: {p q : 实数} (a b : 实数>=0) (hp_pos : 0 < p) (hpq : p <= q)
  证明: by
  have h_rpow : forall a : Real>=0, a ^ q = (a ^ p) ^ (q / p) := fun a => by
    rw [← NNReal.rpow_mul]; rw [div_eq_inv_mul]; rw [← mul_assoc]; rw [mul_inv_cancel₀ hp_pos.ne.symm]; rw [one_mul]
  have h_rpow_add_rpow_le_add :
    ((a ^ p) ^ (q / p) + (b ^ p) ^ (q / p)) ^ (1 / (q / p)) <= a ^ p + b ^ p := by
    refine rpow_add_rpow_le_add (a ^ p) (b ^ p) ?_
    rwa [one_le_div hp_pos]
  rw [h_rpow a]; rw [h_rpow b]; rw [one_div p]; rw [NNReal.le_rpow_inv_iff hp_pos]; rw [← NNReal.rpow_mul]; rw [mul_comm]; rw [mul_one_div]
  rwa [one_div_div] at h_rpow_add_rpow_le_add

Depends on / 依赖: NNReal, NNReal.le_rpow_inv_iff, NNReal.rpow_mul, div_eq_inv_mul, h_rpow, h_rpow_add_rpow_le_add, hp_pos, hp_pos.ne.symm, le_rpow_inv_iff, mul_, mul_assoc, mul_comm, one_div, one_le_div, one_mul, rpow_add_rpow_le_add, rpow_mul
-/
theorem rpow_add_rpow_le {p q : Real} (a b : Real>=0) (hp_pos : 0 < p) (hpq : p <= q) :
    (a ^ q + b ^ q) ^ (1 / q) <= (a ^ p + b ^ p) ^ (1 / p) := by
  have h_rpow : forall a : Real>=0, a ^ q = (a ^ p) ^ (q / p) := fun a => by
    rw [← NNReal.rpow_mul]; rw [div_eq_inv_mul]; rw [← mul_assoc]; rw [mul_inv_cancel₀ hp_pos.ne.symm]; rw [one_mul]
  have h_rpow_add_rpow_le_add :
    ((a ^ p) ^ (q / p) + (b ^ p) ^ (q / p)) ^ (1 / (q / p)) <= a ^ p + b ^ p := by
    refine rpow_add_rpow_le_add (a ^ p) (b ^ p) ?_
    rwa [one_le_div hp_pos]
  rw [h_rpow a]; rw [h_rpow b]; rw [one_div p]; rw [NNReal.le_rpow_inv_iff hp_pos]; rw [← NNReal.rpow_mul]; rw [mul_comm]; rw [mul_one_div]
  rwa [one_div_div] at h_rpow_add_rpow_le_add

/--
theorem `rpow_add_le_add_rpow` / 定理 `rpow_add_le_add_rpow`

English:
theorem rpow_add_le_add_rpow
  given: {p : Real} (a b : Real>=0) (hp : 0 <= p) (hp1 : p <= 1)
  proof: by
  rcases hp.eq_or_lt with (rfl | hp_pos)
  · simp
  have h := rpow_add_rpow_le a b hp_pos hp1
  rw [one_div_one]; rw [one_div] at h
  repeat' rw [NNReal.rpow_one] at h
  exact (NNReal.le_rpow_inv_iff hp_pos).mp h

中文:
定理 rpow_add_le_add_rpow
  条件: {p : 实数} (a b : 实数>=0) (hp : 0 <= p) (hp1 : p <= 1)
  证明: by
  rcases hp.eq_or_lt with (rfl | hp_pos)
  · simp
  have h := rpow_add_rpow_le a b hp_pos hp1
  rw [one_div_one]; rw [one_div] at h
  repeat' rw [NNReal.rpow_one] at h
  exact (NNReal.le_rpow_inv_iff hp_pos).mp h

Depends on / 依赖: NNReal, NNReal.le_rpow_inv_iff, NNReal.rpow_one, eq_or_lt, hp.eq_or_lt, hp_pos, le_rpow_inv_iff, one_div, one_div_one, repeat, rpow_add_rpow_le, rpow_one
-/
theorem rpow_add_le_add_rpow {p : Real} (a b : Real>=0) (hp : 0 <= p) (hp1 : p <= 1) :
    (a + b) ^ p <= a ^ p + b ^ p := by
  rcases hp.eq_or_lt with (rfl | hp_pos)
  · simp
  have h := rpow_add_rpow_le a b hp_pos hp1
  rw [one_div_one]; rw [one_div] at h
  repeat' rw [NNReal.rpow_one] at h
  exact (NNReal.le_rpow_inv_iff hp_pos).mp h

end NNReal

namespace Real

/--
lemma `add_rpow_le_rpow_add` / 引理 `add_rpow_le_rpow_add`

English:
lemma add_rpow_le_rpow_add
  given: {p : Real} {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (hp1 : 1 <= p)
  proof: by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.add_rpow_le_rpow_add a b hp1

中文:
引理 add_rpow_le_rpow_add
  条件: {p : 实数} {a b : 实数} (ha : 0 <= a) (hb : 0 <= b) (hp1 : 1 <= p)
  证明: by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.add_rpow_le_rpow_add a b hp1

Depends on / 依赖: NNReal, NNReal.add_rpow_le_rpow_add, add_rpow_le_rpow_add
-/
lemma add_rpow_le_rpow_add {p : Real} {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (hp1 : 1 <= p) :
     a ^ p + b ^ p <= (a + b) ^ p := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.add_rpow_le_rpow_add a b hp1

/--
lemma `rpow_add_rpow_le_add` / 引理 `rpow_add_rpow_le_add`

English:
lemma rpow_add_rpow_le_add
  given: {p : Real} {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (hp1 : 1 <= p)
  proof: by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_rpow_le_add a b hp1

中文:
引理 rpow_add_rpow_le_add
  条件: {p : 实数} {a b : 实数} (ha : 0 <= a) (hb : 0 <= b) (hp1 : 1 <= p)
  证明: by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_rpow_le_add a b hp1

Depends on / 依赖: NNReal, NNReal.rpow_add_rpow_le_add, rpow_add_rpow_le_add
-/
lemma rpow_add_rpow_le_add {p : Real} {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (hp1 : 1 <= p) :
    (a ^ p + b ^ p) ^ (1 / p) <= a + b := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_rpow_le_add a b hp1

/--
lemma `rpow_add_rpow_le` / 引理 `rpow_add_rpow_le`

English:
lemma rpow_add_rpow_le
  statement: {p q : Real} {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (hp_pos : 0 < p)
  proof: by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_rpow_le a b hp_pos hpq

中文:
引理 rpow_add_rpow_le
  结论: {p q : 实数} {a b : 实数} (ha : 0 <= a) (hb : 0 <= b) (hp_pos : 0 < p)
  证明: by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_rpow_le a b hp_pos hpq

Depends on / 依赖: NNReal, NNReal.rpow_add_rpow_le, hp_pos, rpow_add_rpow_le
-/
lemma rpow_add_rpow_le {p q : Real} {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (hp_pos : 0 < p)
    (hpq : p <= q) :
    (a ^ q + b ^ q) ^ (1 / q) <= (a ^ p + b ^ p) ^ (1 / p) := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_rpow_le a b hp_pos hpq

/--
lemma `rpow_add_le_add_rpow` / 引理 `rpow_add_le_add_rpow`

English:
lemma rpow_add_le_add_rpow
  statement: {p : Real} {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (hp : 0 <= p)
  proof: by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_le_add_rpow a b hp hp1

中文:
引理 rpow_add_le_add_rpow
  结论: {p : 实数} {a b : 实数} (ha : 0 <= a) (hb : 0 <= b) (hp : 0 <= p)
  证明: by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_le_add_rpow a b hp hp1

Depends on / 依赖: NNReal, NNReal.rpow_add_le_add_rpow, rpow_add_le_add_rpow
-/
lemma rpow_add_le_add_rpow {p : Real} {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (hp : 0 <= p)
    (hp1 : p <= 1) :
    (a + b) ^ p <= a ^ p + b ^ p := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_le_add_rpow a b hp hp1

end Real

namespace ENNReal

/--
theorem `rpow_arith_mean_le_arith_mean_rpow` / 定理 `rpow_arith_mean_le_arith_mean_rpow`

English:
theorem rpow_arith_mean_le_arith_mean_rpow
  statement: (w z : ι -> Real>=0∞) (hw' : ∑ i in s, w i = 1) {p : Real}
  proof: by
  have hp_pos : 0 < p := by positivity
  have hp_nonneg : 0 <= p := by positivity
  have hp_not_neg : ¬p < 0 := by simp [hp_nonneg]
  have h_top_iff_rpow_top : forall (i : ι), i in s -> (w i * z i = ⊤ ↔ w i * z i ^ p = ⊤) := by
    simp [ENNReal.mul_eq_top, hp_pos, hp_not_neg]
  refine le_of_top_imp_top_of_toNNReal_le ?_ ?_
  · -- first, prove `(∑ i ∈ s, w i * z i) ^ p = ⊤ → ∑ i ∈ s, (w i * z i ^ p) = ⊤`
    rw [rpow_eq_top_iff]; rw [sum_eq_top]; rw [sum_eq_top]
    grind
  · -- second, suppose both `(∑ i ∈ s, w i * z i) ^ p ≠ ⊤` and `∑ i ∈ s, (w i * z i ^ p) ≠ ⊤`,
    -- and prove `((∑ i ∈ s, w i * z i) ^ p).toNNReal ≤ (∑ i ∈ s, (w i * z i ^ p)).toNNReal`,
    -- by using `NNReal.rpow_arith_mean_le_arith_mean_rpow`.
    intro h_top_rpow_sum _
    -- show hypotheses needed to put the `.toNNReal` inside the sums.
    have h_top : forall a : ι, a in s -> w a * z a != ⊤ :=
      haveI h_top_sum : ∑ i in s, w i * z i != ⊤ := by
        intro h
        rw [h]; rw [top_rpow_of_pos hp_pos] at h_top_rpow_sum
        exact h_top_rpow_sum rfl
      fun a ha => (lt_top_of_sum_ne_top h_top_sum ha).ne
    have h_top_rpow : forall a : ι, a in s -> w a * z a ^ p != ⊤ := by
      intro i hi
      specialize h_top i hi
      rwa [Ne, ← h_top_iff_rpow_top i hi]
    -- put the `.toNNReal` inside the sums.
    simp_rw [toNNReal_sum h_top_rpow, toNNReal_rpow, toNNReal_sum h_top, toNNReal_mul,
      toNNReal_rpow]
    -- use corresponding nnreal result
    refine
      NNReal.rpow_arith_mean_le_arith_mean_rpow s (fun i => (w i).toNNReal)
        (fun i => (z i).toNNReal) ?_ hp
    -- verify the hypothesis `∑ i ∈ s, (w i).toNNReal = 1`, using `∑ i ∈ s, w i = 1` .
    have h_sum_nnreal : ∑ i in s, w i = ↑(∑ i in s, (w i).toNNReal) := by
      push_cast
      congr! with i hi
      refine (coe_toNNReal (lt_top_of_sum_ne_top ?_ hi).ne).symm
      exact hw'.symm ▸ ENNReal.one_ne_top
    rwa [← coe_inj, ← h_sum_nnreal]

中文:
定理 rpow_arith_mean_le_arith_mean_rpow
  结论: (w z : ι -> 实数>=0∞) (hw' : ∑ i in s, w i = 1) {p : 实数}
  证明: by
  have hp_pos : 0 < p := by positivity
  have hp_nonneg : 0 <= p := by positivity
  have hp_not_neg : ¬p < 0 := by simp [hp_nonneg]
  have h_top_iff_rpow_top : forall (i : ι), i in s -> (w i * z i = ⊤ ↔ w i * z i ^ p = ⊤) := by
    simp [ENNReal.mul_eq_top, hp_pos, hp_not_neg]
  refine le_of_top_imp_top_of_toNNReal_le ?_ ?_
  · -- first, prove `(∑ i ∈ s, w i * z i) ^ p = ⊤ → ∑ i ∈ s, (w i * z i ^ p) = ⊤`
    rw [rpow_eq_top_iff]; rw [sum_eq_top]; rw [sum_eq_top]
    grind
  · -- second, suppose both `(∑ i ∈ s, w i * z i) ^ p ≠ ⊤` and `∑ i ∈ s, (w i * z i ^ p) ≠ ⊤`,
    -- and prove `((∑ i ∈ s, w i * z i) ^ p).toNNReal ≤ (∑ i ∈ s, (w i * z i ^ p)).toNNReal`,
    -- by using `NNReal.rpow_arith_mean_le_arith_mean_rpow`.
    intro h_top_rpow_sum _
    -- show hypotheses needed to put the `.toNNReal` inside the sums.
    have h_top : forall a : ι, a in s -> w a * z a != ⊤ :=
      haveI h_top_sum : ∑ i in s, w i * z i != ⊤ := by
        intro h
        rw [h]; rw [top_rpow_of_pos hp_pos] at h_top_rpow_sum
        exact h_top_rpow_sum rfl
      fun a ha => (lt_top_of_sum_ne_top h_top_sum ha).ne
    have h_top_rpow : forall a : ι, a in s -> w a * z a ^ p != ⊤ := by
      intro i hi
      specialize h_top i hi
      rwa [Ne, ← h_top_iff_rpow_top i hi]
    -- put the `.toNNReal` inside the sums.
    simp_rw [toNNReal_sum h_top_rpow, toNNReal_rpow, toNNReal_sum h_top, toNNReal_mul,
      toNNReal_rpow]
    -- use corresponding nnreal result
    refine
      NNReal.rpow_arith_mean_le_arith_mean_rpow s (fun i => (w i).toNNReal)
        (fun i => (z i).toNNReal) ?_ hp
    -- verify the hypothesis `∑ i ∈ s, (w i).toNNReal = 1`, using `∑ i ∈ s, w i = 1` .
    have h_sum_nnreal : ∑ i in s, w i = ↑(∑ i in s, (w i).toNNReal) := by
      push_cast
      congr! with i hi
      refine (coe_toNNReal (lt_top_of_sum_ne_top ?_ hi).ne).symm
      exact hw'.symm ▸ ENNReal.one_ne_top
    rwa [← coe_inj, ← h_sum_nnreal]

Depends on / 依赖: ENNReal, ENNReal.mul_eq_top, h_top_iff_rpow_top, hp_nonneg, hp_not_neg, hp_pos, le_of_top_imp_top_of_toNNReal_le, mul_eq_top, rpow_eq_top_iff, second, sum_eq_top, suppose
-/
theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι -> Real>=0∞) (hw' : ∑ i in s, w i = 1) {p : Real}
    (hp : 1 <= p) : (∑ i in s, w i * z i) ^ p <= ∑ i in s, w i * z i ^ p := by
  have hp_pos : 0 < p := by positivity
  have hp_nonneg : 0 <= p := by positivity
  have hp_not_neg : ¬p < 0 := by simp [hp_nonneg]
  have h_top_iff_rpow_top : forall (i : ι), i in s -> (w i * z i = ⊤ ↔ w i * z i ^ p = ⊤) := by
    simp [ENNReal.mul_eq_top, hp_pos, hp_not_neg]
  refine le_of_top_imp_top_of_toNNReal_le ?_ ?_
  · -- first, prove `(∑ i ∈ s, w i * z i) ^ p = ⊤ → ∑ i ∈ s, (w i * z i ^ p) = ⊤`
    rw [rpow_eq_top_iff]; rw [sum_eq_top]; rw [sum_eq_top]
    grind
  · -- second, suppose both `(∑ i ∈ s, w i * z i) ^ p ≠ ⊤` and `∑ i ∈ s, (w i * z i ^ p) ≠ ⊤`,
    -- and prove `((∑ i ∈ s, w i * z i) ^ p).toNNReal ≤ (∑ i ∈ s, (w i * z i ^ p)).toNNReal`,
    -- by using `NNReal.rpow_arith_mean_le_arith_mean_rpow`.
    intro h_top_rpow_sum _
    -- show hypotheses needed to put the `.toNNReal` inside the sums.
    have h_top : forall a : ι, a in s -> w a * z a != ⊤ :=
      haveI h_top_sum : ∑ i in s, w i * z i != ⊤ := by
        intro h
        rw [h]; rw [top_rpow_of_pos hp_pos] at h_top_rpow_sum
        exact h_top_rpow_sum rfl
      fun a ha => (lt_top_of_sum_ne_top h_top_sum ha).ne
    have h_top_rpow : forall a : ι, a in s -> w a * z a ^ p != ⊤ := by
      intro i hi
      specialize h_top i hi
      rwa [Ne, ← h_top_iff_rpow_top i hi]
    -- put the `.toNNReal` inside the sums.
    simp_rw [toNNReal_sum h_top_rpow, toNNReal_rpow, toNNReal_sum h_top, toNNReal_mul,
      toNNReal_rpow]
    -- use corresponding nnreal result
    refine
      NNReal.rpow_arith_mean_le_arith_mean_rpow s (fun i => (w i).toNNReal)
        (fun i => (z i).toNNReal) ?_ hp
    -- verify the hypothesis `∑ i ∈ s, (w i).toNNReal = 1`, using `∑ i ∈ s, w i = 1` .
    have h_sum_nnreal : ∑ i in s, w i = ↑(∑ i in s, (w i).toNNReal) := by
      push_cast
      congr! with i hi
      refine (coe_toNNReal (lt_top_of_sum_ne_top ?_ hi).ne).symm
      exact hw'.symm ▸ ENNReal.one_ne_top
    rwa [← coe_inj, ← h_sum_nnreal]

/--
theorem `rpow_arith_mean_le_arith_mean2_rpow` / 定理 `rpow_arith_mean_le_arith_mean2_rpow`

English:
theorem rpow_arith_mean_le_arith_mean2_rpow
  statement: (w₁ w₂ z₁ z₂ : Real>=0∞) (hw' : w₁ + w₂ = 1) {p : Real}
  proof: by
  have h := rpow_arith_mean_le_arith_mean_rpow univ ![w₁, w₂] ![z₁, z₂] ?_ hp
  · simpa [Fin.sum_univ_succ] using h
  · simp [hw', Fin.sum_univ_succ]

中文:
定理 rpow_arith_mean_le_arith_mean2_rpow
  结论: (w₁ w₂ z₁ z₂ : 实数>=0∞) (hw' : w₁ + w₂ = 1) {p : 实数}
  证明: by
  have h := rpow_arith_mean_le_arith_mean_rpow univ ![w₁, w₂] ![z₁, z₂] ?_ hp
  · simpa [Fin.sum_univ_succ] using h
  · simp [hw', Fin.sum_univ_succ]

Depends on / 依赖: Fin.sum_univ_succ, rpow_arith_mean_le_arith_mean_rpow, sum_univ_succ
-/
theorem rpow_arith_mean_le_arith_mean2_rpow (w₁ w₂ z₁ z₂ : Real>=0∞) (hw' : w₁ + w₂ = 1) {p : Real}
    (hp : 1 <= p) : (w₁ * z₁ + w₂ * z₂) ^ p <= w₁ * z₁ ^ p + w₂ * z₂ ^ p := by
  have h := rpow_arith_mean_le_arith_mean_rpow univ ![w₁, w₂] ![z₁, z₂] ?_ hp
  · simpa [Fin.sum_univ_succ] using h
  · simp [hw', Fin.sum_univ_succ]

/--
theorem `rpow_add_le_mul_rpow_add_rpow` / 定理 `rpow_add_le_mul_rpow_add_rpow`

English:
theorem rpow_add_le_mul_rpow_add_rpow
  given: (z₁ z₂ : Real>=0∞) {p : Real} (hp : 1 <= p)
  proof: by
  convert!
    rpow_arith_mean_le_arith_mean2_rpow (1 / 2) (1 / 2) (2 * z₁) (2 * z₂) (ENNReal.add_halves 1) hp
      using 1
  · simp [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ofNat_ne_top]
  · simp only [mul_rpow_of_nonneg _ _ (zero_le_one.trans hp), rpow_sub _ _ two_ne_zero ofNat_ne_top,
      ENNReal.div_eq_inv_mul, rpow_one, mul_one]
    ring

中文:
定理 rpow_add_le_mul_rpow_add_rpow
  条件: (z₁ z₂ : 实数>=0∞) {p : 实数} (hp : 1 <= p)
  证明: by
  convert!
    rpow_arith_mean_le_arith_mean2_rpow (1 / 2) (1 / 2) (2 * z₁) (2 * z₂) (ENNReal.add_halves 1) hp
      using 1
  · simp [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ofNat_ne_top]
  · simp only [mul_rpow_of_nonneg _ _ (zero_le_one.trans hp), rpow_sub _ _ two_ne_zero ofNat_ne_top,
      ENNReal.div_eq_inv_mul, rpow_one, mul_one]
    ring

Depends on / 依赖: ENNReal, ENNReal.add_halves, ENNReal.div_eq_inv_mul, ENNReal.inv_mul_cancel, add_halves, convert, div_eq_inv_mul, inv_mul_cancel, mul_assoc, mul_one, mul_rpow_of_nonneg, ofNat_ne_top, rpow_arith_mean_le_arith_mean2_rpow, rpow_one, rpow_sub, two_ne_zero, zero_le_one, zero_le_one.trans
-/
theorem rpow_add_le_mul_rpow_add_rpow (z₁ z₂ : Real>=0∞) {p : Real} (hp : 1 <= p) :
    (z₁ + z₂) ^ p <= (2 : Real>=0∞) ^ (p - 1) * (z₁ ^ p + z₂ ^ p) := by
  convert!
    rpow_arith_mean_le_arith_mean2_rpow (1 / 2) (1 / 2) (2 * z₁) (2 * z₂) (ENNReal.add_halves 1) hp
      using 1
  · simp [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ofNat_ne_top]
  · simp only [mul_rpow_of_nonneg _ _ (zero_le_one.trans hp), rpow_sub _ _ two_ne_zero ofNat_ne_top,
      ENNReal.div_eq_inv_mul, rpow_one, mul_one]
    ring

/--
theorem `add_rpow_le_rpow_add` / 定理 `add_rpow_le_rpow_add`

English:
theorem add_rpow_le_rpow_add
  given: {p : Real} (a b : Real>=0∞) (hp1 : 1 <= p)
  statement: a ^ p + b ^ p <= (a + b) ^ p
  proof: by
  have hp_pos : 0 < p := by positivity
  by_cases h_top : a + b = ⊤
  · rw [← @ENNReal.rpow_eq_top_iff_of_pos (a + b) p hp_pos] at h_top
    rw [h_top]
    exact le_top
  obtain ⟨ha_top, hb_top⟩ := add_ne_top.mp h_top
  lift a to Real>=0 using ha_top
  lift b to Real>=0 using hb_top
  simpa [ENNReal.coe_rpow_of_nonneg _ hp_pos.le] using
    ENNReal.coe_le_coe.2 (NNReal.add_rpow_le_rpow_add a b hp1)

中文:
定理 add_rpow_le_rpow_add
  条件: {p : 实数} (a b : 实数>=0∞) (hp1 : 1 <= p)
  结论: a ^ p + b ^ p <= (a + b) ^ p
  证明: by
  have hp_pos : 0 < p := by positivity
  by_cases h_top : a + b = ⊤
  · rw [← @ENNReal.rpow_eq_top_iff_of_pos (a + b) p hp_pos] at h_top
    rw [h_top]
    exact le_top
  obtain ⟨ha_top, hb_top⟩ := add_ne_top.mp h_top
  lift a to Real>=0 using ha_top
  lift b to Real>=0 using hb_top
  simpa [ENNReal.coe_rpow_of_nonneg _ hp_pos.le] using
    ENNReal.coe_le_coe.2 (NNReal.add_rpow_le_rpow_add a b hp1)

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_rpow_of_nonneg, ENNReal.rpow_eq_top_iff_of_pos, NNReal, NNReal.add_rpow_le_rpow_add, add_ne_top, add_ne_top.mp, add_rpow_le_rpow_add, coe_le_coe, coe_rpow_of_nonneg, h_top, ha_top, hb_top, hp_pos, hp_pos.le, le_top, rpow_eq_top_iff_of_pos
-/
theorem add_rpow_le_rpow_add {p : Real} (a b : Real>=0∞) (hp1 : 1 <= p) : a ^ p + b ^ p <= (a + b) ^ p := by
  have hp_pos : 0 < p := by positivity
  by_cases h_top : a + b = ⊤
  · rw [← @ENNReal.rpow_eq_top_iff_of_pos (a + b) p hp_pos] at h_top
    rw [h_top]
    exact le_top
  obtain ⟨ha_top, hb_top⟩ := add_ne_top.mp h_top
  lift a to Real>=0 using ha_top
  lift b to Real>=0 using hb_top
  simpa [ENNReal.coe_rpow_of_nonneg _ hp_pos.le] using
    ENNReal.coe_le_coe.2 (NNReal.add_rpow_le_rpow_add a b hp1)

/--
theorem `rpow_add_rpow_le_add` / 定理 `rpow_add_rpow_le_add`

English:
theorem rpow_add_rpow_le_add
  given: {p : Real} (a b : Real>=0∞) (hp1 : 1 <= p)
  proof: by
  rw [one_div]; rw [← @ENNReal.le_rpow_inv_iff _ _ p⁻¹ (by simp [lt_of_lt_of_le zero_lt_one hp1])]
  rw [inv_inv]
  exact add_rpow_le_rpow_add _ _ hp1

中文:
定理 rpow_add_rpow_le_add
  条件: {p : 实数} (a b : 实数>=0∞) (hp1 : 1 <= p)
  证明: by
  rw [one_div]; rw [← @ENNReal.le_rpow_inv_iff _ _ p⁻¹ (by simp [lt_of_lt_of_le zero_lt_one hp1])]
  rw [inv_inv]
  exact add_rpow_le_rpow_add _ _ hp1

Depends on / 依赖: ENNReal, ENNReal.le_rpow_inv_iff, add_rpow_le_rpow_add, inv_inv, le_rpow_inv_iff, lt_of_lt_of_le, one_div, zero_lt_one
-/
theorem rpow_add_rpow_le_add {p : Real} (a b : Real>=0∞) (hp1 : 1 <= p) :
    (a ^ p + b ^ p) ^ (1 / p) <= a + b := by
  rw [one_div]; rw [← @ENNReal.le_rpow_inv_iff _ _ p⁻¹ (by simp [lt_of_lt_of_le zero_lt_one hp1])]
  rw [inv_inv]
  exact add_rpow_le_rpow_add _ _ hp1

/--
theorem `rpow_add_rpow_le` / 定理 `rpow_add_rpow_le`

English:
theorem rpow_add_rpow_le
  given: {p q : Real} (a b : Real>=0∞) (hp_pos : 0 < p) (hpq : p <= q)
  proof: by
  have h_rpow : forall a : Real>=0∞, a ^ q = (a ^ p) ^ (q / p) := fun a => by
    rw [← ENNReal.rpow_mul]; rw [mul_div_cancel₀ _ hp_pos.ne']
  have h_rpow_add_rpow_le_add :
    ((a ^ p) ^ (q / p) + (b ^ p) ^ (q / p)) ^ (1 / (q / p)) <= a ^ p + b ^ p := by
    refine rpow_add_rpow_le_add (a ^ p) (b ^ p) ?_
    rwa [one_le_div hp_pos]
  rw [h_rpow a]; rw [h_rpow b]; rw [one_div p]; rw [ENNReal.le_rpow_inv_iff hp_pos]; rw [← ENNReal.rpow_mul]; rw [mul_comm]; rw [mul_one_div]
  rwa [one_div_div] at h_rpow_add_rpow_le_add

中文:
定理 rpow_add_rpow_le
  条件: {p q : 实数} (a b : 实数>=0∞) (hp_pos : 0 < p) (hpq : p <= q)
  证明: by
  have h_rpow : forall a : Real>=0∞, a ^ q = (a ^ p) ^ (q / p) := fun a => by
    rw [← ENNReal.rpow_mul]; rw [mul_div_cancel₀ _ hp_pos.ne']
  have h_rpow_add_rpow_le_add :
    ((a ^ p) ^ (q / p) + (b ^ p) ^ (q / p)) ^ (1 / (q / p)) <= a ^ p + b ^ p := by
    refine rpow_add_rpow_le_add (a ^ p) (b ^ p) ?_
    rwa [one_le_div hp_pos]
  rw [h_rpow a]; rw [h_rpow b]; rw [one_div p]; rw [ENNReal.le_rpow_inv_iff hp_pos]; rw [← ENNReal.rpow_mul]; rw [mul_comm]; rw [mul_one_div]
  rwa [one_div_div] at h_rpow_add_rpow_le_add

Depends on / 依赖: ENNReal, ENNReal.le_rpow_inv_iff, ENNReal.rpow_mul, h_rpow, h_rpow_add_rpow_le_ad, h_rpow_add_rpow_le_add, hp_pos, hp_pos.ne, le_rpow_inv_iff, mul_comm, mul_one_div, one_div, one_div_div, one_le_div, rpow_add_rpow_le_add, rpow_mul
-/
theorem rpow_add_rpow_le {p q : Real} (a b : Real>=0∞) (hp_pos : 0 < p) (hpq : p <= q) :
    (a ^ q + b ^ q) ^ (1 / q) <= (a ^ p + b ^ p) ^ (1 / p) := by
  have h_rpow : forall a : Real>=0∞, a ^ q = (a ^ p) ^ (q / p) := fun a => by
    rw [← ENNReal.rpow_mul]; rw [mul_div_cancel₀ _ hp_pos.ne']
  have h_rpow_add_rpow_le_add :
    ((a ^ p) ^ (q / p) + (b ^ p) ^ (q / p)) ^ (1 / (q / p)) <= a ^ p + b ^ p := by
    refine rpow_add_rpow_le_add (a ^ p) (b ^ p) ?_
    rwa [one_le_div hp_pos]
  rw [h_rpow a]; rw [h_rpow b]; rw [one_div p]; rw [ENNReal.le_rpow_inv_iff hp_pos]; rw [← ENNReal.rpow_mul]; rw [mul_comm]; rw [mul_one_div]
  rwa [one_div_div] at h_rpow_add_rpow_le_add

/--
theorem `rpow_add_le_add_rpow` / 定理 `rpow_add_le_add_rpow`

English:
theorem rpow_add_le_add_rpow
  given: {p : Real} (a b : Real>=0∞) (hp : 0 <= p) (hp1 : p <= 1)
  proof: by
  rcases hp.eq_or_lt with (rfl | hp_pos)
  · simp
  have h := rpow_add_rpow_le a b hp_pos hp1
  rw [one_div_one]; rw [one_div] at h
  repeat' rw [ENNReal.rpow_one] at h
  exact (ENNReal.le_rpow_inv_iff hp_pos).mp h

中文:
定理 rpow_add_le_add_rpow
  条件: {p : 实数} (a b : 实数>=0∞) (hp : 0 <= p) (hp1 : p <= 1)
  证明: by
  rcases hp.eq_or_lt with (rfl | hp_pos)
  · simp
  have h := rpow_add_rpow_le a b hp_pos hp1
  rw [one_div_one]; rw [one_div] at h
  repeat' rw [ENNReal.rpow_one] at h
  exact (ENNReal.le_rpow_inv_iff hp_pos).mp h

Depends on / 依赖: ENNReal, ENNReal.le_rpow_inv_iff, ENNReal.rpow_one, eq_or_lt, hp.eq_or_lt, hp_pos, le_rpow_inv_iff, one_div, one_div_one, repeat, rpow_add_rpow_le, rpow_one
-/
theorem rpow_add_le_add_rpow {p : Real} (a b : Real>=0∞) (hp : 0 <= p) (hp1 : p <= 1) :
    (a + b) ^ p <= a ^ p + b ^ p := by
  rcases hp.eq_or_lt with (rfl | hp_pos)
  · simp
  have h := rpow_add_rpow_le a b hp_pos hp1
  rw [one_div_one]; rw [one_div] at h
  repeat' rw [ENNReal.rpow_one] at h
  exact (ENNReal.le_rpow_inv_iff hp_pos).mp h

/--
Definition of `LpAddConst` / `LpAddConst` 的定义

English:
definition LpAddConst
  signature: (p : Real>=0∞)
  body: if p in Set.Ioo (0 : Real>=0∞) 1 then (2 : Real>=0∞) ^ (1 / p.toReal - 1) else 1

中文:
定义 LpAddConst
  签名: (p : 实数>=0∞)
  定义体: if p in Set.Ioo (0 : Real>=0∞) 1 then (2 : Real>=0∞) ^ (1 / p.toReal - 1) else 1
-/
@[expose] noncomputable def LpAddConst (p : Real>=0∞) : Real>=0∞ :=
  if p in Set.Ioo (0 : Real>=0∞) 1 then (2 : Real>=0∞) ^ (1 / p.toReal - 1) else 1

/--
theorem `LpAddConst_of_one_le` / 定理 `LpAddConst_of_one_le`

English:
theorem LpAddConst_of_one_le
  given: {p : Real>=0∞} (hp : 1 <= p)
  statement: LpAddConst p = 1
  proof: by
  rw [LpAddConst]; rw [if_neg]
  intro h
  exact lt_irrefl _ (h.2.trans_le hp)

中文:
定理 LpAddConst_of_one_le
  条件: {p : 实数>=0∞} (hp : 1 <= p)
  结论: LpAddConst p = 1
  证明: by
  rw [LpAddConst]; rw [if_neg]
  intro h
  exact lt_irrefl _ (h.2.trans_le hp)

Depends on / 依赖: LpAddConst, if_neg, lt_irrefl, trans_le
-/
theorem LpAddConst_of_one_le {p : Real>=0∞} (hp : 1 <= p) : LpAddConst p = 1 := by
  rw [LpAddConst]; rw [if_neg]
  intro h
  exact lt_irrefl _ (h.2.trans_le hp)

/--
theorem `LpAddConst_zero` / 定理 `LpAddConst_zero`

English:
theorem LpAddConst_zero
  statement: LpAddConst 0 = 1
  proof: by
  rw [LpAddConst]; rw [if_neg]
  intro h
  exact lt_irrefl _ h.1

中文:
定理 LpAddConst_zero
  结论: LpAddConst 0 = 1
  证明: by
  rw [LpAddConst]; rw [if_neg]
  intro h
  exact lt_irrefl _ h.1

Depends on / 依赖: LpAddConst, if_neg, lt_irrefl
-/
theorem LpAddConst_zero : LpAddConst 0 = 1 := by
  rw [LpAddConst]; rw [if_neg]
  intro h
  exact lt_irrefl _ h.1

/--
theorem `LpAddConst_lt_top` / 定理 `LpAddConst_lt_top`

English:
theorem LpAddConst_lt_top
  given: (p : Real>=0∞)
  statement: LpAddConst p < ∞
  proof: by
  rw [LpAddConst]
  split_ifs with h
  · apply ENNReal.rpow_lt_top_of_nonneg _ ENNReal.ofNat_ne_top
    rw [one_div]; rw [sub_nonneg]; rw [← ENNReal.toReal_inv]; rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (by simpa using h.1.ne') (ENNReal.one_le_inv.2 h.2.le)
  · exact ENNReal.one_lt_top

中文:
定理 LpAddConst_lt_top
  条件: (p : 实数>=0∞)
  结论: LpAddConst p < ∞
  证明: by
  rw [LpAddConst]
  split_ifs with h
  · apply ENNReal.rpow_lt_top_of_nonneg _ ENNReal.ofNat_ne_top
    rw [one_div]; rw [sub_nonneg]; rw [← ENNReal.toReal_inv]; rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (by simpa using h.1.ne') (ENNReal.one_le_inv.2 h.2.le)
  · exact ENNReal.one_lt_top

Depends on / 依赖: ENNReal, ENNReal.ofNat_ne_top, ENNReal.one_le_inv, ENNReal.one_lt_top, ENNReal.rpow_lt_top_of_nonneg, ENNReal.toReal_inv, ENNReal.toReal_mono, ENNReal.toReal_one, LpAddConst, ofNat_ne_top, one_div, one_le_inv, one_lt_top, rpow_lt_top_of_nonneg, split_ifs, sub_nonneg, toReal_inv, toReal_mono, toReal_one
-/
theorem LpAddConst_lt_top (p : Real>=0∞) : LpAddConst p < ∞ := by
  rw [LpAddConst]
  split_ifs with h
  · apply ENNReal.rpow_lt_top_of_nonneg _ ENNReal.ofNat_ne_top
    rw [one_div]; rw [sub_nonneg]; rw [← ENNReal.toReal_inv]; rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (by simpa using h.1.ne') (ENNReal.one_le_inv.2 h.2.le)
  · exact ENNReal.one_lt_top

/--
theorem `rpow_add_le_mul_rpow_add_rpow'` / 定理 `rpow_add_le_mul_rpow_add_rpow'`

English:
theorem rpow_add_le_mul_rpow_add_rpow'
  given: (z₁ z₂ : Real>=0∞) {p : Real} (hp : 0 <= p)
  proof: by
  by_cases h : 1 < p
  · have hmem : (ENNReal.ofReal p)⁻¹ in Set.Ioo (0 : Real>=0∞) 1 := by
      constructor
      · simp
      · rwa [ENNReal.inv_lt_one, one_lt_ofReal]
    rw [show LpAddConst (ENNReal.ofReal p)⁻¹ =
        (2 : Real>=0∞) ^ (1 / ((ENNReal.ofReal p)⁻¹).toReal - 1) by
      rw [LpAddConst]; rw [if_pos hmem]]
    simp only [ENNReal.toReal_inv, div_inv_eq_mul, one_mul]
    rw [ENNReal.toReal_ofReal hp]
    exact rpow_add_le_mul_rpow_add_rpow _ _ h.le
  · have hp1 : p <= 1 := not_lt.mp h
    rw [LpAddConst_of_one_le (ENNReal.one_le_inv.mpr (ENNReal.ofReal_le_one.mpr hp1))]; rw [one_mul]
    exact rpow_add_le_add_rpow _ _ hp hp1

中文:
定理 rpow_add_le_mul_rpow_add_rpow'
  条件: (z₁ z₂ : 实数>=0∞) {p : 实数} (hp : 0 <= p)
  证明: by
  by_cases h : 1 < p
  · have hmem : (ENNReal.ofReal p)⁻¹ in Set.Ioo (0 : Real>=0∞) 1 := by
      constructor
      · simp
      · rwa [ENNReal.inv_lt_one, one_lt_ofReal]
    rw [show LpAddConst (ENNReal.ofReal p)⁻¹ =
        (2 : Real>=0∞) ^ (1 / ((ENNReal.ofReal p)⁻¹).toReal - 1) by
      rw [LpAddConst]; rw [if_pos hmem]]
    simp only [ENNReal.toReal_inv, div_inv_eq_mul, one_mul]
    rw [ENNReal.toReal_ofReal hp]
    exact rpow_add_le_mul_rpow_add_rpow _ _ h.le
  · have hp1 : p <= 1 := not_lt.mp h
    rw [LpAddConst_of_one_le (ENNReal.one_le_inv.mpr (ENNReal.ofReal_le_one.mpr hp1))]; rw [one_mul]
    exact rpow_add_le_add_rpow _ _ hp hp1

Depends on / 依赖: ENNReal, ENNReal.inv_lt_one, ENNReal.ofReal, ENNReal.one_le_inv, ENNReal.toReal_inv, ENNReal.toReal_ofReal, LpAddConst, LpAddConst_of_one_le, Set.Ioo, div_inv_eq_mul, h.le, if_pos, inv_lt_one, not_lt, not_lt.mp, ofReal, one_le_inv, one_lt_ofReal, one_mul, rpow_add_le_mul_rpow_add_rpow
-/
theorem rpow_add_le_mul_rpow_add_rpow' (z₁ z₂ : Real>=0∞) {p : Real} (hp : 0 <= p) :
    (z₁ + z₂) ^ p <= LpAddConst (ENNReal.ofReal p)⁻¹ * (z₁ ^ p + z₂ ^ p) := by
  by_cases h : 1 < p
  · have hmem : (ENNReal.ofReal p)⁻¹ in Set.Ioo (0 : Real>=0∞) 1 := by
      constructor
      · simp
      · rwa [ENNReal.inv_lt_one, one_lt_ofReal]
    rw [show LpAddConst (ENNReal.ofReal p)⁻¹ =
        (2 : Real>=0∞) ^ (1 / ((ENNReal.ofReal p)⁻¹).toReal - 1) by
      rw [LpAddConst]; rw [if_pos hmem]]
    simp only [ENNReal.toReal_inv, div_inv_eq_mul, one_mul]
    rw [ENNReal.toReal_ofReal hp]
    exact rpow_add_le_mul_rpow_add_rpow _ _ h.le
  · have hp1 : p <= 1 := not_lt.mp h
    rw [LpAddConst_of_one_le (ENNReal.one_le_inv.mpr (ENNReal.ofReal_le_one.mpr hp1))]; rw [one_mul]
    exact rpow_add_le_add_rpow _ _ hp hp1

/--
theorem `rpow_add_le_mul_rpow_add_rpow''` / 定理 `rpow_add_le_mul_rpow_add_rpow''`

English:
theorem rpow_add_le_mul_rpow_add_rpow''
  given: (z₁ z₂ : Real>=0∞) {p : Real>=0∞}
  proof: by
  by_cases p_zero : p = 0
  · simp [p_zero, LpAddConst_zero]
  convert rpow_add_le_mul_rpow_add_rpow' z₁ z₂ (p := p.toReal⁻¹) (by positivity)
  rw [← ENNReal.toReal_inv]; rw [ENNReal.ofReal_toReal (by simpa)]; rw [inv_inv]

中文:
定理 rpow_add_le_mul_rpow_add_rpow''
  条件: (z₁ z₂ : 实数>=0∞) {p : 实数>=0∞}
  证明: by
  by_cases p_zero : p = 0
  · simp [p_zero, LpAddConst_zero]
  convert rpow_add_le_mul_rpow_add_rpow' z₁ z₂ (p := p.toReal⁻¹) (by positivity)
  rw [← ENNReal.toReal_inv]; rw [ENNReal.ofReal_toReal (by simpa)]; rw [inv_inv]

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal, ENNReal.toReal_inv, LpAddConst_zero, convert, inv_inv, ofReal_toReal, p.toReal, p_zero, rpow_add_le_mul_rpow_add_rpow, toReal, toReal_inv
-/
theorem rpow_add_le_mul_rpow_add_rpow'' (z₁ z₂ : Real>=0∞) {p : Real>=0∞} :
    (z₁ + z₂) ^ p.toReal⁻¹ <=
      LpAddConst p * (z₁ ^ p.toReal⁻¹ + z₂ ^ p.toReal⁻¹) := by
  by_cases p_zero : p = 0
  · simp [p_zero, LpAddConst_zero]
  convert rpow_add_le_mul_rpow_add_rpow' z₁ z₂ (p := p.toReal⁻¹) (by positivity)
  rw [← ENNReal.toReal_inv]; rw [ENNReal.ofReal_toReal (by simpa)]; rw [inv_inv]

end ENNReal
