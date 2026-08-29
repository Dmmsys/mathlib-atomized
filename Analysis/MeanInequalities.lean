/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne, Jireh Loreaux
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Real.ConjExponents

/-!
# Mean value inequalities

In this file we prove several inequalities for finite sums, including AM-GM inequality,
HM-GM inequality, Young's inequality, Hölder inequality, and Minkowski inequality. Versions for
integrals of some of these inequalities are available in
`Mathlib/MeasureTheory/Integral/MeanInequalities.lean`.

## Main theorems

### AM-GM inequality:

The inequality says that the geometric mean of a tuple of non-negative numbers is less than or equal
to their arithmetic mean. We prove the weighted version of this inequality: if $w$ and $z$
are two non-negative vectors and $\sum_{i\in s} w_i=1$, then
$$
\prod_{i\in s} z_i^{w_i} ≤ \sum_{i\in s} w_iz_i.
$$
The classical version is a special case of this inequality for $w_i=\frac{1}{n}$.

We prove a few versions of this inequality. Each of the following lemmas comes in two versions:
a version for real-valued non-negative functions is in the `Real` namespace, and a version for
`NNReal`-valued functions is in the `NNReal` namespace.

- `geom_mean_le_arith_mean_weighted` : weighted version for functions on `Finset`s;
- `geom_mean_le_arith_mean2_weighted` : weighted version for two numbers;
- `geom_mean_le_arith_mean3_weighted` : weighted version for three numbers;
- `geom_mean_le_arith_mean4_weighted` : weighted version for four numbers.


### HM-GM inequality:

The inequality says that the harmonic mean of a tuple of positive numbers is less than or equal
to their geometric mean. We prove the weighted version of this inequality: if $w$ and $z$
are two positive vectors and $\sum_{i\in s} w_i=1$, then
$$
1/(\sum_{i\in s} w_i/z_i) ≤ \prod_{i\in s} z_i^{w_i}
$$
The classical version is proven as a special case of this inequality for $w_i=\frac{1}{n}$.

The inequalities are proven only for real-valued positive functions on `Finset`s, and namespaced in
`Real`. The weighted version follows as a corollary of the weighted AM-GM inequality.

### Young's inequality

Young's inequality says that for non-negative numbers `a`, `b`, `p`, `q` such that
$\frac{1}{p}+\frac{1}{q}=1$ we have
$$
ab ≤ \frac{a^p}{p} + \frac{b^q}{q}.
$$

This inequality is a special case of the AM-GM inequality. It is then used to prove Hölder's
inequality (see below).

### Hölder's inequality

The inequality says that for two conjugate exponents `p` and `q` (i.e., for two positive numbers
such that $\frac{1}{p}+\frac{1}{q}=1$) and any two non-negative vectors their inner product is
less than or equal to the product of the $L_p$ norm of the first vector and the $L_q$ norm of the
second vector:
$$
\sum_{i\in s} a_ib_i ≤ \sqrt[p]{\sum_{i\in s} a_i^p}\sqrt[q]{\sum_{i\in s} b_i^q}.
$$

We give versions of this result in `ℝ`, `ℝ≥0` and `ℝ≥0∞`.

There are at least two short proofs of this inequality. In our proof we prenormalize both vectors,
then apply Young's inequality to each $a_ib_i$. Another possible proof would be to deduce this
inequality from the generalized mean inequality for well-chosen vectors and weights.

### Minkowski's inequality

The inequality says that for `p ≥ 1` the function
$$
\|a\|_p=\sqrt[p]{\sum_{i\in s} a_i^p}
$$
satisfies the triangle inequality $\|a+b\|_p\le \|a\|_p+\|b\|_p$.

We give versions of this result in `Real`, `ℝ≥0` and `ℝ≥0∞`.

We deduce this inequality from Hölder's inequality. Namely, Hölder inequality implies that $\|a\|_p$
is the maximum of the inner product $\sum_{i\in s}a_ib_i$ over `b` such that $\|b\|_q\le 1$. Now
Minkowski's inequality follows from the fact that the maximum value of the sum of two functions is
less than or equal to the sum of the maximum values of the summands.

## TODO

- each inequality `A ≤ B` should come with a theorem `A = B ↔ _`; one of the ways to prove them
  is to define `StrictConvexOn` functions.
- generalized mean inequality with any `p ≤ q`, including negative numbers;
- prove that the power mean tends to the geometric mean as the exponent tends to zero.

-/

public section


universe u v

open Finset NNReal ENNReal
open scoped BigOperators

noncomputable section

variable {ι : Type u} (s : Finset ι)

section GeomMeanLEArithMean

/-! ### AM-GM inequality -/


namespace Real

/--
theorem `geom_mean_le_arith_mean_weighted` / 定理 `geom_mean_le_arith_mean_weighted`

English:
theorem geom_mean_le_arith_mean_weighted
  statement: (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
  proof: by
  -- If some number `z i` equals zero and has non-zero weight, then LHS is 0 and RHS is nonnegative.
  by_cases! A : exists i in s, z i = 0 ∧ w i != 0
  · rcases A with ⟨i, his, hzi, hwi⟩
    rw [prod_eq_zero his]
    · exact sum_nonneg fun j hj => mul_nonneg (hw j hj) (hz j hj)
    · rw [hzi]
  

中文:
定理 geom_mean_le_arith_mean_weighted
  结论: (w z : ι -> 实数) (hw : 对任意 i in s, 0 <= w i)
  证明: by
  -- If some number `z i` equals zero and has non-zero weight, then LHS is 0 and RHS is nonnegative.
  by_cases! A : exists i in s, z i = 0 ∧ w i != 0
  · rcases A with ⟨i, his, hzi, hwi⟩
    rw [prod_eq_zero his]
    · exact sum_nonneg fun j hj => mul_nonneg (hw j hj) (hz j hj)
    · rw [hzi]
  
-/
theorem geom_mean_le_arith_mean_weighted (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
    (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) :
    ∏ i in s, z i ^ w i <= ∑ i in s, w i * z i := by
  -- If some number `z i` equals zero and has non-zero weight, then LHS is 0 and RHS is nonnegative.
  by_cases! A : exists i in s, z i = 0 ∧ w i != 0
  · rcases A with ⟨i, his, hzi, hwi⟩
    rw [prod_eq_zero his]
    · exact sum_nonneg fun j hj => mul_nonneg (hw j hj) (hz j hj)
    · rw [hzi]
      exact zero_rpow hwi
  -- If all numbers `z i` with non-zero weight are positive, then we apply Jensen's inequality
  -- for `exp` and numbers `log (z i)` with weights `w i`.
· have := convexOn_exp.map_sum_le hw hw' fun i _ => Set.mem_univ log (z i)
    simp only [exp_sum, smul_eq_mul, mul_comm (w _) (log _)] at this
    convert! this using 1 <;> [apply prod_congr rfl; apply sum_congr rfl] <;> intro i hi
    · rcases eq_or_lt_of_le (hz i hi) with hz | hz
      · simp [A i hi hz.symm]
      · exact rpow_def_of_pos hz _
    · rcases eq_or_lt_of_le (hz i hi) with hz | hz
      · simp [A i hi hz.symm]
      · rw [exp_log hz]

/--
theorem `geom_mean_le_arith_mean` / 定理 `geom_mean_le_arith_mean`

English:
theorem geom_mean_le_arith_mean
  statement: {ι : Type*} (s : Finset ι) (w : ι -> Real) (z : ι -> Real)
  proof: by
  convert geom_mean_le_arith_mean_weighted s (fun i => (w i) / ∑ i in s, w i) z ?_ ?_ hz
  · rw [← finsetProd_rpow _ _ (fun i hi => rpow_nonneg (hz _ hi) _) _]
    refine Finset.prod_congr rfl (fun _ ih => ?_)
    rw [div_eq_mul_inv]; rw [rpow_mul (hz _ ih)]
  · simp_rw [div_eq_mul_inv, mul_assoc

中文:
定理 geom_mean_le_arith_mean
  结论: {ι : 类型} (s : Finset ι) (w : ι -> 实数) (z : ι -> 实数)
  证明: by
  convert geom_mean_le_arith_mean_weighted s (fun i => (w i) / ∑ i in s, w i) z ?_ ?_ hz
  · rw [← finsetProd_rpow _ _ (fun i hi => rpow_nonneg (hz _ hi) _) _]
    refine Finset.prod_congr rfl (fun _ ih => ?_)
    rw [div_eq_mul_inv]; rw [rpow_mul (hz _ ih)]
  · simp_rw [div_eq_mul_inv, mul_assoc

Depends on / 依赖: Finset, Finset.prod_congr, Finset.sum_mul, convert, div_eq_mul_inv, div_nonneg, finsetProd_rpow, geom_mean_le_arith_mean_weighted, le_of_lt, mul_assoc, mul_comm, prod_congr, rpow_mul, rpow_nonneg, simp_rw, sum_mul
-/
theorem geom_mean_le_arith_mean {ι : Type*} (s : Finset ι) (w : ι -> Real) (z : ι -> Real)
    (hw : forall i in s, 0 <= w i) (hw' : 0 < ∑ i in s, w i) (hz : forall i in s, 0 <= z i) :
    (∏ i in s, z i ^ w i) ^ (∑ i in s, w i)⁻¹ <= (∑ i in s, w i * z i) / (∑ i in s, w i) := by
  convert geom_mean_le_arith_mean_weighted s (fun i => (w i) / ∑ i in s, w i) z ?_ ?_ hz
  · rw [← finsetProd_rpow _ _ (fun i hi => rpow_nonneg (hz _ hi) _) _]
    refine Finset.prod_congr rfl (fun _ ih => ?_)
    rw [div_eq_mul_inv]; rw [rpow_mul (hz _ ih)]
  · simp_rw [div_eq_mul_inv, mul_assoc, mul_comm, ← mul_assoc, ← Finset.sum_mul, mul_comm]
  · exact fun _ hi => div_nonneg (hw _ hi) (le_of_lt hw')
  · simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ (by linarith)

/--
theorem `geom_mean_weighted_of_constant` / 定理 `geom_mean_weighted_of_constant`

English:
theorem geom_mean_weighted_of_constant
  statement: (w z : ι -> Real) (x : Real) (hw : forall i in s, 0 <= w i)
  proof: calc
    ∏ i in s, z i ^ w i = ∏ i in s, x ^ w i := by
      refine prod_congr rfl fun i hi => ?_
      rcases eq_or_ne (w i) 0 with h₀ | h₀
      · rw [h₀, rpow_zero, rpow_zero]
      · rw [hx i hi h₀]
    _ = x := by
      rw [← rpow_sum_of_nonneg _ hw]; rw [hw']; rw [rpow_one]
      have : (∑ i i

中文:
定理 geom_mean_weighted_of_constant
  结论: (w z : ι -> 实数) (x : 实数) (hw : 对任意 i in s, 0 <= w i)
  证明: calc
    ∏ i in s, z i ^ w i = ∏ i in s, x ^ w i := by
      refine prod_congr rfl fun i hi => ?_
      rcases eq_or_ne (w i) 0 with h₀ | h₀
      · rw [h₀, rpow_zero, rpow_zero]
      · rw [hx i hi h₀]
    _ = x := by
      rw [← rpow_sum_of_nonneg _ hw]; rw [hw']; rw [rpow_one]
      have : (∑ i i

Depends on / 依赖: eq_or_ne, exists_ne_zero_of_sum_ne_zero, one_ne_zero, prod_congr, rpow_one, rpow_sum_of_nonneg, rpow_zero
-/
theorem geom_mean_weighted_of_constant (w z : ι -> Real) (x : Real) (hw : forall i in s, 0 <= w i)
    (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) (hx : forall i in s, w i != 0 -> z i = x) :
    ∏ i in s, z i ^ w i = x :=
  calc
    ∏ i in s, z i ^ w i = ∏ i in s, x ^ w i := by
      refine prod_congr rfl fun i hi => ?_
      rcases eq_or_ne (w i) 0 with h₀ | h₀
      · rw [h₀, rpow_zero, rpow_zero]
      · rw [hx i hi h₀]
    _ = x := by
      rw [← rpow_sum_of_nonneg _ hw]; rw [hw']; rw [rpow_one]
      have : (∑ i in s, w i) != 0 := by
        rw [hw']
        exact one_ne_zero
      obtain ⟨i, his, hi⟩ := exists_ne_zero_of_sum_ne_zero this
      rw [← hx i his hi]
      exact hz i his

/--
theorem `arith_mean_weighted_of_constant` / 定理 `arith_mean_weighted_of_constant`

English:
theorem arith_mean_weighted_of_constant
  statement: (w z : ι -> Real) (x : Real) (hw' : ∑ i in s, w i = 1)
  proof: calc
    ∑ i in s, w i * z i = ∑ i in s, w i * x := by
      refine sum_congr rfl fun i hi => ?_
      rcases eq_or_ne (w i) 0 with hwi | hwi
      · rw [hwi, zero_mul, zero_mul]
      · rw [hx i hi hwi]
    _ = x := by rw [← sum_mul, hw', one_mul]

中文:
定理 arith_mean_weighted_of_constant
  结论: (w z : ι -> 实数) (x : 实数) (hw' : ∑ i in s, w i = 1)
  证明: calc
    ∑ i in s, w i * z i = ∑ i in s, w i * x := by
      refine sum_congr rfl fun i hi => ?_
      rcases eq_or_ne (w i) 0 with hwi | hwi
      · rw [hwi, zero_mul, zero_mul]
      · rw [hx i hi hwi]
    _ = x := by rw [← sum_mul, hw', one_mul]

Depends on / 依赖: eq_or_ne, one_mul, sum_congr, sum_mul, zero_mul
-/
theorem arith_mean_weighted_of_constant (w z : ι -> Real) (x : Real) (hw' : ∑ i in s, w i = 1)
    (hx : forall i in s, w i != 0 -> z i = x) : ∑ i in s, w i * z i = x :=
  calc
    ∑ i in s, w i * z i = ∑ i in s, w i * x := by
      refine sum_congr rfl fun i hi => ?_
      rcases eq_or_ne (w i) 0 with hwi | hwi
      · rw [hwi, zero_mul, zero_mul]
      · rw [hx i hi hwi]
    _ = x := by rw [← sum_mul, hw', one_mul]

/--
theorem `geom_mean_eq_arith_mean_weighted_of_constant` / 定理 `geom_mean_eq_arith_mean_weighted_of_constant`

English:
theorem geom_mean_eq_arith_mean_weighted_of_constant
  statement: (w z : ι -> Real) (x : Real) (hw : forall i in s, 0 <= w i)
  proof: by
  rw [geom_mean_weighted_of_constant]; rw [arith_mean_weighted_of_constant] <;> assumption

中文:
定理 geom_mean_eq_arith_mean_weighted_of_constant
  结论: (w z : ι -> 实数) (x : 实数) (hw : 对任意 i in s, 0 <= w i)
  证明: by
  rw [geom_mean_weighted_of_constant]; rw [arith_mean_weighted_of_constant] <;> assumption

Depends on / 依赖: arith_mean_weighted_of_constant, geom_mean_weighted_of_constant
-/
theorem geom_mean_eq_arith_mean_weighted_of_constant (w z : ι -> Real) (x : Real) (hw : forall i in s, 0 <= w i)
    (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) (hx : forall i in s, w i != 0 -> z i = x) :
    ∏ i in s, z i ^ w i = ∑ i in s, w i * z i := by
  rw [geom_mean_weighted_of_constant]; rw [arith_mean_weighted_of_constant] <;> assumption

/--
theorem `geom_mean_eq_arith_mean_weighted_iff_of_pos'` / 定理 `geom_mean_eq_arith_mean_weighted_iff_of_pos'`

English:
theorem geom_mean_eq_arith_mean_weighted_iff_of_pos'
  statement: (w z : ι -> Real) (hw : forall i in s, 0 < w i)
  proof: by
  by_cases! A : exists i in s, z i = 0 ∧ w i != 0
  · rcases A with ⟨i, his, hzi, hwi⟩
    rw [prod_eq_zero his]
    · constructor
      · intro h
        rw [← h]
        intro j hj
        apply eq_zero_of_ne_zero_of_mul_left_eq_zero (ne_of_lt (hw j hj)).symm
        apply (sum_eq_zero_iff_of_n

中文:
定理 geom_mean_eq_arith_mean_weighted_iff_of_pos'
  结论: (w z : ι -> 实数) (hw : 对任意 i in s, 0 < w i)
  证明: by
  by_cases! A : exists i in s, z i = 0 ∧ w i != 0
  · rcases A with ⟨i, his, hzi, hwi⟩
    rw [prod_eq_zero his]
    · constructor
      · intro h
        rw [← h]
        intro j hj
        apply eq_zero_of_ne_zero_of_mul_left_eq_zero (ne_of_lt (hw j hj)).symm
        apply (sum_eq_zero_iff_of_n

Depends on / 依赖: convert, eq_zero_of_ne_zero_of_mul_left_eq_zero, h.symm, hzi.symm, lt_of_le_of_ne, mul_nonneg_iff_of_pos_left, ne_of_gt, ne_of_lt, prod_eq_zero, sum_eq_zero_iff_of_nonneg, zero_rpow
-/
theorem geom_mean_eq_arith_mean_weighted_iff_of_pos' (w z : ι -> Real) (hw : forall i in s, 0 < w i)
    (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) :
    ∏ i in s, z i ^ w i = ∑ i in s, w i * z i ↔ forall j in s, z j = ∑ i in s, w i * z i := by
  by_cases! A : exists i in s, z i = 0 ∧ w i != 0
  · rcases A with ⟨i, his, hzi, hwi⟩
    rw [prod_eq_zero his]
    · constructor
      · intro h
        rw [← h]
        intro j hj
        apply eq_zero_of_ne_zero_of_mul_left_eq_zero (ne_of_lt (hw j hj)).symm
        apply (sum_eq_zero_iff_of_nonneg ?_).mp h.symm j hj
        exact fun i hi => (mul_nonneg_iff_of_pos_left (hw i hi)).mpr (hz i hi)
      · intro h
        convert! h i his
        exact hzi.symm
    · rw [hzi]
      exact zero_rpow hwi
  · have hz' := fun i h => lt_of_le_of_ne (hz i h) (fun a => (ne_of_gt (hw i h)) (A i h a.symm))
have := strictConvexOn_exp.map_sum_eq_iff hw hw' fun i _ => Set.mem_univ log (z i)
    simp only [exp_sum, smul_eq_mul, mul_comm (w _) (log _)] at this
    convert! this using 1
    · apply Eq.congr <;>
      [apply prod_congr rfl; apply sum_congr rfl] <;>
      intro i hi <;>
      simp only [exp_mul, exp_log (hz' i hi)]
    · constructor <;> intro h j hj
      · rw [← arith_mean_weighted_of_constant s w _ (log (z j)) hw' fun i _ => congrFun rfl]
        apply sum_congr rfl
        intro x hx
        simp only [mul_comm, h j hj, h x hx]
      · rw [← arith_mean_weighted_of_constant s w _ (z j) hw' fun i _ => congrFun rfl]
        apply sum_congr rfl
        intro x hx
        simp only [log_injOn_pos (hz' j hj) (hz' x hx), h j hj, h x hx]

@[deprecated (since := "2026-06-07")]
alias geom_mean_eq_arith_mean_weighted_iff' := geom_mean_eq_arith_mean_weighted_iff_of_pos'

/--
theorem `geom_mean_eq_arith_mean_weighted_iff_of_nonneg'` / 定理 `geom_mean_eq_arith_mean_weighted_iff_of_nonneg'`

English:
theorem geom_mean_eq_arith_mean_weighted_iff_of_nonneg'
  statement: (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
  proof: by
  have :
      ∏ i in s with w i != 0, z i ^ w i = ∑ i in s with w i != 0, w i * z i ↔
        forall j in {x in s | w x != 0}, z j = ∑ i in s with w i != 0, w i * z i :=
    geom_mean_eq_arith_mean_weighted_iff_of_pos' _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of_me

中文:
定理 geom_mean_eq_arith_mean_weighted_iff_of_nonneg'
  结论: (w z : ι -> 实数) (hw : 对任意 i in s, 0 <= w i)
  证明: by
  have :
      ∏ i in s with w i != 0, z i ^ w i = ∑ i in s with w i != 0, w i * z i ↔
        forall j in {x in s | w x != 0}, z j = ∑ i in s with w i != 0, w i * z i :=
    geom_mean_eq_arith_mean_weighted_iff_of_pos' _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of_me

Depends on / 依赖: geom_mean_eq_arith_mean_weighted_iff_of_pos, mem_of_mem_filter, prod_filter_of_ne, rpow_zero, sum_filter_ne_zero, sum_filter_of_ne
-/
theorem geom_mean_eq_arith_mean_weighted_iff_of_nonneg' (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
    (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) :
    ∏ i in s, z i ^ w i = ∑ i in s, w i * z i ↔ forall j in s, w j != 0 -> z j = ∑ i in s, w i * z i := by
  have :
      ∏ i in s with w i != 0, z i ^ w i = ∑ i in s with w i != 0, w i * z i ↔
        forall j in {x in s | w x != 0}, z j = ∑ i in s with w i != 0, w i * z i :=
    geom_mean_eq_arith_mean_weighted_iff_of_pos' _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of_mem_filter · ·)
  grind [prod_filter_of_ne, sum_filter_of_ne, rpow_zero]

@[deprecated (since := "2026-06-07")]
alias geom_mean_eq_arith_mean_weighted_iff := geom_mean_eq_arith_mean_weighted_iff_of_nonneg'

/--
theorem `geom_mean_eq_arith_mean_weighted_iff_of_pos` / 定理 `geom_mean_eq_arith_mean_weighted_iff_of_pos`

English:
theorem geom_mean_eq_arith_mean_weighted_iff_of_pos
  statement: (w z : ι -> Real) (hw : forall i in s, 0 < w i)
  proof: by
  refine ⟨by grind [geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw hw' hz], fun h => ?_⟩
  have ⟨k, hk⟩ : s.Nonempty := by grind [s.eq_empty_or_nonempty]
  suffices ∏ i in s, z k ^ w i = ∑ i in s, w i * z k by convert this using 3 <;> grind
  rw [← rpow_sum_of_nonneg (hz k hk) (hw · · |>.l

中文:
定理 geom_mean_eq_arith_mean_weighted_iff_of_pos
  结论: (w z : ι -> 实数) (hw : 对任意 i in s, 0 < w i)
  证明: by
  refine ⟨by grind [geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw hw' hz], fun h => ?_⟩
  have ⟨k, hk⟩ : s.Nonempty := by grind [s.eq_empty_or_nonempty]
  suffices ∏ i in s, z k ^ w i = ∑ i in s, w i * z k by convert this using 3 <;> grind
  rw [← rpow_sum_of_nonneg (hz k hk) (hw · · |>.l

Depends on / 依赖: Nonempty, convert, eq_empty_or_nonempty, geom_mean_eq_arith_mean_weighted_iff_of_pos, one_mul, rpow_one, rpow_sum_of_nonneg, s.Nonempty, s.eq_empty_or_nonempty, sum_mul
-/
theorem geom_mean_eq_arith_mean_weighted_iff_of_pos (w z : ι -> Real) (hw : forall i in s, 0 < w i)
    (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) :
    ∏ i in s, z i ^ w i = ∑ i in s, w i * z i ↔ forall j in s, forall k in s, z j = z k := by
  refine ⟨by grind [geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw hw' hz], fun h => ?_⟩
  have ⟨k, hk⟩ : s.Nonempty := by grind [s.eq_empty_or_nonempty]
  suffices ∏ i in s, z k ^ w i = ∑ i in s, w i * z k by convert this using 3 <;> grind
  rw [← rpow_sum_of_nonneg (hz k hk) (hw · · |>.le)]; rw [← sum_mul]; rw [hw']; rw [rpow_one]; rw [one_mul]

/--
theorem `geom_mean_eq_arith_mean_weighted_iff_of_nonneg` / 定理 `geom_mean_eq_arith_mean_weighted_iff_of_nonneg`

English:
theorem geom_mean_eq_arith_mean_weighted_iff_of_nonneg
  statement: (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
  proof: by
  have :
      ∏ i in s with w i != 0, z i ^ w i = ∑ i in s with w i != 0, w i * z i ↔
        forall j in {x in s | w x != 0}, forall k in {x in s | w x != 0}, z j = z k :=
    geom_mean_eq_arith_mean_weighted_iff_of_pos _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of_

中文:
定理 geom_mean_eq_arith_mean_weighted_iff_of_nonneg
  结论: (w z : ι -> 实数) (hw : 对任意 i in s, 0 <= w i)
  证明: by
  have :
      ∏ i in s with w i != 0, z i ^ w i = ∑ i in s with w i != 0, w i * z i ↔
        forall j in {x in s | w x != 0}, forall k in {x in s | w x != 0}, z j = z k :=
    geom_mean_eq_arith_mean_weighted_iff_of_pos _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of_

Depends on / 依赖: geom_mean_eq_arith_mean_weighted_iff_of_pos, mem_of_mem_filter, prod_filter_of_ne, rpow_zero, sum_filter_ne_zero, sum_filter_of_ne
-/
theorem geom_mean_eq_arith_mean_weighted_iff_of_nonneg (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
    (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) :
    ∏ i in s, z i ^ w i = ∑ i in s, w i * z i ↔ forall j in s, w j != 0 -> forall k in s, w k != 0 -> z j = z k := by
  have :
      ∏ i in s with w i != 0, z i ^ w i = ∑ i in s with w i != 0, w i * z i ↔
        forall j in {x in s | w x != 0}, forall k in {x in s | w x != 0}, z j = z k :=
    geom_mean_eq_arith_mean_weighted_iff_of_pos _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of_mem_filter · ·)
  grind [prod_filter_of_ne, sum_filter_of_ne, rpow_zero]

/--
theorem `geom_mean_lt_arith_mean_weighted_iff_of_pos'` / 定理 `geom_mean_lt_arith_mean_weighted_iff_of_pos'`

English:
theorem geom_mean_lt_arith_mean_weighted_iff_of_pos'
  statement: (w z : ι -> Real) (hw : forall i in s, 0 < w i)
  proof: by
  contrapose!
  rw [← geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw hw' hz]
.ge_iff_eq exact geom_mean_le_arith_mean_weighted s w z (hw · · |>.le) hw' hz

中文:
定理 geom_mean_lt_arith_mean_weighted_iff_of_pos'
  结论: (w z : ι -> 实数) (hw : 对任意 i in s, 0 < w i)
  证明: by
  contrapose!
  rw [← geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw hw' hz]
.ge_iff_eq exact geom_mean_le_arith_mean_weighted s w z (hw · · |>.le) hw' hz

Depends on / 依赖: contrapose, ge_iff_eq, geom_mean_eq_arith_mean_weighted_iff_of_pos, geom_mean_le_arith_mean_weighted
-/
theorem geom_mean_lt_arith_mean_weighted_iff_of_pos' (w z : ι -> Real) (hw : forall i in s, 0 < w i)
    (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) :
    ∏ i in s, z i ^ w i < ∑ i in s, w i * z i ↔ exists j in s, z j != ∑ i in s, w i * z i := by
  contrapose!
  rw [← geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw hw' hz]
.ge_iff_eq exact geom_mean_le_arith_mean_weighted s w z (hw · · |>.le) hw' hz

/--
theorem `geom_mean_lt_arith_mean_weighted_iff_of_nonneg'` / 定理 `geom_mean_lt_arith_mean_weighted_iff_of_nonneg'`

English:
theorem geom_mean_lt_arith_mean_weighted_iff_of_nonneg'
  statement: (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
  proof: by
  have :
      ∏ i in s with w i != 0, z i ^ w i < ∑ i in s with w i != 0, w i * z i ↔
        exists j in {x in s | w x != 0}, z j != ∑ i in s with w i != 0, w i * z i :=
    geom_mean_lt_arith_mean_weighted_iff_of_pos' _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of_m

中文:
定理 geom_mean_lt_arith_mean_weighted_iff_of_nonneg'
  结论: (w z : ι -> 实数) (hw : 对任意 i in s, 0 <= w i)
  证明: by
  have :
      ∏ i in s with w i != 0, z i ^ w i < ∑ i in s with w i != 0, w i * z i ↔
        exists j in {x in s | w x != 0}, z j != ∑ i in s with w i != 0, w i * z i :=
    geom_mean_lt_arith_mean_weighted_iff_of_pos' _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of_m

Depends on / 依赖: geom_mean_lt_arith_mean_weighted_iff_of_pos, mem_of_mem_filter, prod_filter_of_ne, rpow_zero, sum_filter_ne_zero, sum_filter_of_ne
-/
theorem geom_mean_lt_arith_mean_weighted_iff_of_nonneg' (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
    (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) :
    ∏ i in s, z i ^ w i < ∑ i in s, w i * z i ↔ exists j in s, w j != 0 ∧ z j != ∑ i in s, w i * z i := by
  have :
      ∏ i in s with w i != 0, z i ^ w i < ∑ i in s with w i != 0, w i * z i ↔
        exists j in {x in s | w x != 0}, z j != ∑ i in s with w i != 0, w i * z i :=
    geom_mean_lt_arith_mean_weighted_iff_of_pos' _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of_mem_filter · ·)
  grind [prod_filter_of_ne, sum_filter_of_ne, rpow_zero]

/--
theorem `geom_mean_lt_arith_mean_weighted_iff_of_pos` / 定理 `geom_mean_lt_arith_mean_weighted_iff_of_pos`

English:
theorem geom_mean_lt_arith_mean_weighted_iff_of_pos
  statement: (w z : ι -> Real) (hw : forall i in s, 0 < w i)
  proof: by
  constructor
  · intro h
    by_contra! h_contra
    rw [(geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw hw' hz).mpr ?_] at h
    · exact (lt_self_iff_false _).mp h
    · intro j hjs
      rw [← arith_mean_weighted_of_constant s w (fun _ => z j) (z j) hw' fun _ _ => congrFun rfl]
      ap

中文:
定理 geom_mean_lt_arith_mean_weighted_iff_of_pos
  结论: (w z : ι -> 实数) (hw : 对任意 i in s, 0 < w i)
  证明: by
  constructor
  · intro h
    by_contra! h_contra
    rw [(geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw hw' hz).mpr ?_] at h
    · exact (lt_self_iff_false _).mp h
    · intro j hjs
      rw [← arith_mean_weighted_of_constant s w (fun _ => z j) (z j) hw' fun _ _ => congrFun rfl]
      ap

Depends on / 依赖: HMul.hMul, arith_mean_weighted_of_constant, geom_mean_eq_arith_mean_weighted_iff_of_pos, geom_mean_le_arith_mean_weighted, h_contra, le_antisymm, le_of_lt, lt_self_iff_false, sum_congr
-/
theorem geom_mean_lt_arith_mean_weighted_iff_of_pos (w z : ι -> Real) (hw : forall i in s, 0 < w i)
    (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) :
    ∏ i in s, z i ^ w i < ∑ i in s, w i * z i ↔ exists j in s, exists k in s, z j != z k := by
  constructor
  · intro h
    by_contra! h_contra
    rw [(geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw hw' hz).mpr ?_] at h
    · exact (lt_self_iff_false _).mp h
    · intro j hjs
      rw [← arith_mean_weighted_of_constant s w (fun _ => z j) (z j) hw' fun _ _ => congrFun rfl]
      apply sum_congr rfl (fun x a => congrArg (HMul.hMul (w x)) (h_contra j hjs x a))
  · rintro ⟨j, hjs, k, hks, hzjk⟩
    have := geom_mean_le_arith_mean_weighted s w z (fun i a => le_of_lt (hw i a)) hw' hz
    by_contra! h
    apply le_antisymm this at h
    apply (geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw hw' hz).mp at h
    simp only [h j hjs, h k hks, ne_eq, not_true_eq_false] at hzjk

/--
theorem `geom_mean_lt_arith_mean_weighted_iff_of_nonneg` / 定理 `geom_mean_lt_arith_mean_weighted_iff_of_nonneg`

English:
theorem geom_mean_lt_arith_mean_weighted_iff_of_nonneg
  statement: (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
  proof: by
  have :
      ∏ i in s with w i != 0, z i ^ w i < ∑ i in s with w i != 0, w i * z i ↔
        exists j in {x in s | w x != 0}, exists k in {x in s | w x != 0}, z j != z k :=
    geom_mean_lt_arith_mean_weighted_iff_of_pos _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of

中文:
定理 geom_mean_lt_arith_mean_weighted_iff_of_nonneg
  结论: (w z : ι -> 实数) (hw : 对任意 i in s, 0 <= w i)
  证明: by
  have :
      ∏ i in s with w i != 0, z i ^ w i < ∑ i in s with w i != 0, w i * z i ↔
        exists j in {x in s | w x != 0}, exists k in {x in s | w x != 0}, z j != z k :=
    geom_mean_lt_arith_mean_weighted_iff_of_pos _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of

Depends on / 依赖: geom_mean_lt_arith_mean_weighted_iff_of_pos, mem_of_mem_filter, prod_filter_of_ne, rpow_zero, sum_filter_ne_zero, sum_filter_of_ne
-/
theorem geom_mean_lt_arith_mean_weighted_iff_of_nonneg (w z : ι -> Real) (hw : forall i in s, 0 <= w i)
    (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) :
    ∏ i in s, z i ^ w i < ∑ i in s, w i * z i ↔ exists j in s, exists k in s, w j != 0 ∧ w k != 0 ∧ z j != z k := by
  have :
      ∏ i in s with w i != 0, z i ^ w i < ∑ i in s with w i != 0, w i * z i ↔
        exists j in {x in s | w x != 0}, exists k in {x in s | w x != 0}, z j != z k :=
    geom_mean_lt_arith_mean_weighted_iff_of_pos _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of_mem_filter · ·)
  grind [prod_filter_of_ne, sum_filter_of_ne, rpow_zero]

end Real

namespace NNReal

/--
theorem `geom_mean_le_arith_mean_weighted` / 定理 `geom_mean_le_arith_mean_weighted`

English:
theorem geom_mean_le_arith_mean_weighted
  given: (w z : ι -> Real>=0) (hw' : ∑ i in s, w i = 1)
  proof: mod_cast
    Real.geom_mean_le_arith_mean_weighted _ _ _ (fun i _ => (w i).coe_nonneg)
      (by assumption_mod_cast) fun i _ => (z i).coe_nonneg

中文:
定理 geom_mean_le_arith_mean_weighted
  条件: (w z : ι -> 实数>=0) (hw' : ∑ i in s, w i = 1)
  证明: mod_cast
    Real.geom_mean_le_arith_mean_weighted _ _ _ (fun i _ => (w i).coe_nonneg)
      (by assumption_mod_cast) fun i _ => (z i).coe_nonneg

Depends on / 依赖: Real.geom_mean_le_arith_mean_weighted, assumption_mod_cast, coe_nonneg, geom_mean_le_arith_mean_weighted, mod_cast
-/
theorem geom_mean_le_arith_mean_weighted (w z : ι -> Real>=0) (hw' : ∑ i in s, w i = 1) :
    (∏ i in s, z i ^ (w i : Real)) <= ∑ i in s, w i * z i :=
  mod_cast
    Real.geom_mean_le_arith_mean_weighted _ _ _ (fun i _ => (w i).coe_nonneg)
      (by assumption_mod_cast) fun i _ => (z i).coe_nonneg

/--
theorem `geom_mean_le_arith_mean2_weighted` / 定理 `geom_mean_le_arith_mean2_weighted`

English:
theorem geom_mean_le_arith_mean2_weighted
  given: (w₁ w₂ p₁ p₂ : Real>=0)
  proof: by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one] using!
    geom_mean_le_arith_mean_weighted univ ![w₁, w₂] ![p₁, p₂]

中文:
定理 geom_mean_le_arith_mean2_weighted
  条件: (w₁ w₂ p₁ p₂ : 实数>=0)
  证明: by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one] using!
    geom_mean_le_arith_mean_weighted univ ![w₁, w₂] ![p₁, p₂]

Depends on / 依赖: Fin.cons_succ, Fin.cons_zero, Fin.prod_univ_succ, Fin.sum_univ_succ, Finset, Finset.prod_empty, Finset.sum_empty, Finset.univ_eq_empty, add_zero, cons_succ, cons_zero, geom_mean_le_arith_mean_weighted, mul_one, prod_empty, prod_univ_succ, sum_empty, sum_univ_succ, univ_eq_empty
-/
theorem geom_mean_le_arith_mean2_weighted (w₁ w₂ p₁ p₂ : Real>=0) :
    w₁ + w₂ = 1 -> p₁ ^ (w₁ : Real) * p₂ ^ (w₂ : Real) <= w₁ * p₁ + w₂ * p₂ := by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one] using!
    geom_mean_le_arith_mean_weighted univ ![w₁, w₂] ![p₁, p₂]

/--
theorem `geom_mean_le_arith_mean3_weighted` / 定理 `geom_mean_le_arith_mean3_weighted`

English:
theorem geom_mean_le_arith_mean3_weighted
  given: (w₁ w₂ w₃ p₁ p₂ p₃ : Real>=0)
  proof: by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one, ← add_assoc,
    mul_assoc] using! geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃] ![p₁, p₂, p₃]

中文:
定理 geom_mean_le_arith_mean3_weighted
  条件: (w₁ w₂ w₃ p₁ p₂ p₃ : 实数>=0)
  证明: by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one, ← add_assoc,
    mul_assoc] using! geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃] ![p₁, p₂, p₃]

Depends on / 依赖: Fin.cons_succ, Fin.cons_zero, Fin.prod_univ_succ, Fin.sum_univ_succ, Finset, Finset.prod_empty, Finset.sum_empty, Finset.univ_eq_empty, add_assoc, add_zero, cons_succ, cons_zero, geom_mean_le_arith_mean_weighted, mul_assoc, mul_one, prod_empty, prod_univ_succ, sum_empty, sum_univ_succ, univ_eq_empty
-/
theorem geom_mean_le_arith_mean3_weighted (w₁ w₂ w₃ p₁ p₂ p₃ : Real>=0) :
    w₁ + w₂ + w₃ = 1 ->
      p₁ ^ (w₁ : Real) * p₂ ^ (w₂ : Real) * p₃ ^ (w₃ : Real) <= w₁ * p₁ + w₂ * p₂ + w₃ * p₃ := by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one, ← add_assoc,
    mul_assoc] using! geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃] ![p₁, p₂, p₃]

/--
theorem `geom_mean_le_arith_mean4_weighted` / 定理 `geom_mean_le_arith_mean4_weighted`

English:
theorem geom_mean_le_arith_mean4_weighted
  given: (w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : Real>=0)
  proof: by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one, ← add_assoc,
    mul_assoc] using! geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃, w₄] ![p₁, p₂, p₃, p₄]

中文:
定理 geom_mean_le_arith_mean4_weighted
  条件: (w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : 实数>=0)
  证明: by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one, ← add_assoc,
    mul_assoc] using! geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃, w₄] ![p₁, p₂, p₃, p₄]

Depends on / 依赖: Fin.cons_succ, Fin.cons_zero, Fin.prod_univ_succ, Fin.sum_univ_succ, Finset, Finset.prod_empty, Finset.sum_empty, Finset.univ_eq_empty, add_assoc, add_zero, cons_succ, cons_zero, geom_mean_le_arith_mean_weighted, mul_assoc, mul_one, prod_empty, prod_univ_succ, sum_empty, sum_univ_succ, univ_eq_empty
-/
theorem geom_mean_le_arith_mean4_weighted (w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : Real>=0) :
    w₁ + w₂ + w₃ + w₄ = 1 ->
      p₁ ^ (w₁ : Real) * p₂ ^ (w₂ : Real) * p₃ ^ (w₃ : Real) * p₄ ^ (w₄ : Real) <=
        w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ := by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one, ← add_assoc,
    mul_assoc] using! geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃, w₄] ![p₁, p₂, p₃, p₄]

end NNReal

namespace Real

/--
theorem `geom_mean_le_arith_mean2_weighted` / 定理 `geom_mean_le_arith_mean2_weighted`

English:
theorem geom_mean_le_arith_mean2_weighted
  statement: {w₁ w₂ p₁ p₂ : Real} (hw₁ : 0 <= w₁) (hw₂ : 0 <= w₂)
  proof: NNReal.geom_mean_le_arith_mean2_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
NNReal.coe_inj.1 by assumption

中文:
定理 geom_mean_le_arith_mean2_weighted
  结论: {w₁ w₂ p₁ p₂ : 实数} (hw₁ : 0 <= w₁) (hw₂ : 0 <= w₂)
  证明: NNReal.geom_mean_le_arith_mean2_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
NNReal.coe_inj.1 by assumption

Depends on / 依赖: NNReal, NNReal.coe_inj, NNReal.geom_mean_le_arith_mean2_weighted, coe_inj, geom_mean_le_arith_mean2_weighted
-/
theorem geom_mean_le_arith_mean2_weighted {w₁ w₂ p₁ p₂ : Real} (hw₁ : 0 <= w₁) (hw₂ : 0 <= w₂)
    (hp₁ : 0 <= p₁) (hp₂ : 0 <= p₂) (hw : w₁ + w₂ = 1) : p₁ ^ w₁ * p₂ ^ w₂ <= w₁ * p₁ + w₂ * p₂ :=
NNReal.geom_mean_le_arith_mean2_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
NNReal.coe_inj.1 by assumption

/--
theorem `geom_mean_le_arith_mean3_weighted` / 定理 `geom_mean_le_arith_mean3_weighted`

English:
theorem geom_mean_le_arith_mean3_weighted
  statement: {w₁ w₂ w₃ p₁ p₂ p₃ : Real} (hw₁ : 0 <= w₁) (hw₂ : 0 <= w₂)
  proof: NNReal.geom_mean_le_arith_mean3_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
⟨p₃, hp₃⟩
    NNReal.coe_inj.1 hw

中文:
定理 geom_mean_le_arith_mean3_weighted
  结论: {w₁ w₂ w₃ p₁ p₂ p₃ : 实数} (hw₁ : 0 <= w₁) (hw₂ : 0 <= w₂)
  证明: NNReal.geom_mean_le_arith_mean3_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
⟨p₃, hp₃⟩
    NNReal.coe_inj.1 hw

Depends on / 依赖: NNReal, NNReal.coe_inj, NNReal.geom_mean_le_arith_mean3_weighted, coe_inj, geom_mean_le_arith_mean3_weighted
-/
theorem geom_mean_le_arith_mean3_weighted {w₁ w₂ w₃ p₁ p₂ p₃ : Real} (hw₁ : 0 <= w₁) (hw₂ : 0 <= w₂)
    (hw₃ : 0 <= w₃) (hp₁ : 0 <= p₁) (hp₂ : 0 <= p₂) (hp₃ : 0 <= p₃) (hw : w₁ + w₂ + w₃ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ <= w₁ * p₁ + w₂ * p₂ + w₃ * p₃ :=
  NNReal.geom_mean_le_arith_mean3_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
⟨p₃, hp₃⟩
    NNReal.coe_inj.1 hw

/--
theorem `geom_mean_le_arith_mean4_weighted` / 定理 `geom_mean_le_arith_mean4_weighted`

English:
theorem geom_mean_le_arith_mean4_weighted
  statement: {w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : Real} (hw₁ : 0 <= w₁)
  proof: NNReal.geom_mean_le_arith_mean4_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨w₄, hw₄⟩ ⟨p₁, hp₁⟩
⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩ ⟨p₄, hp₄⟩
NNReal.coe_inj.1 by assumption

中文:
定理 geom_mean_le_arith_mean4_weighted
  结论: {w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : 实数} (hw₁ : 0 <= w₁)
  证明: NNReal.geom_mean_le_arith_mean4_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨w₄, hw₄⟩ ⟨p₁, hp₁⟩
⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩ ⟨p₄, hp₄⟩
NNReal.coe_inj.1 by assumption

Depends on / 依赖: NNReal, NNReal.coe_inj, NNReal.geom_mean_le_arith_mean4_weighted, coe_inj, geom_mean_le_arith_mean4_weighted
-/
theorem geom_mean_le_arith_mean4_weighted {w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : Real} (hw₁ : 0 <= w₁)
    (hw₂ : 0 <= w₂) (hw₃ : 0 <= w₃) (hw₄ : 0 <= w₄) (hp₁ : 0 <= p₁) (hp₂ : 0 <= p₂) (hp₃ : 0 <= p₃)
    (hp₄ : 0 <= p₄) (hw : w₁ + w₂ + w₃ + w₄ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ * p₄ ^ w₄ <= w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ :=
  NNReal.geom_mean_le_arith_mean4_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨w₄, hw₄⟩ ⟨p₁, hp₁⟩
⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩ ⟨p₄, hp₄⟩
NNReal.coe_inj.1 by assumption

/--
theorem `geom_mean_eq_arith_mean2_weighted_iff_of_pos` / 定理 `geom_mean_eq_arith_mean2_weighted_iff_of_pos`

English:
theorem geom_mean_eq_arith_mean2_weighted_iff_of_pos
  statement: {w₁ w₂ p₁ p₂ : Real} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
  proof: by
  have := geom_mean_eq_arith_mean_weighted_iff_of_pos univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind

中文:
定理 geom_mean_eq_arith_mean2_weighted_iff_of_pos
  结论: {w₁ w₂ p₁ p₂ : 实数} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
  证明: by
  have := geom_mean_eq_arith_mean_weighted_iff_of_pos univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind

Depends on / 依赖: geom_mean_eq_arith_mean_weighted_iff_of_pos
-/
theorem geom_mean_eq_arith_mean2_weighted_iff_of_pos {w₁ w₂ p₁ p₂ : Real} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hp₁ : 0 <= p₁) (hp₂ : 0 <= p₂) (hw : w₁ + w₂ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ = w₁ * p₁ + w₂ * p₂ ↔ p₁ = p₂ := by
  have := geom_mean_eq_arith_mean_weighted_iff_of_pos univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind

/--
theorem `geom_mean_eq_arith_mean2_weighted_iff_of_nonneg` / 定理 `geom_mean_eq_arith_mean2_weighted_iff_of_nonneg`

English:
theorem geom_mean_eq_arith_mean2_weighted_iff_of_nonneg
  statement: {w₁ w₂ p₁ p₂ : Real} (hw₁ : 0 <= w₁)
  proof: by
  have := geom_mean_eq_arith_mean_weighted_iff_of_nonneg univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind

中文:
定理 geom_mean_eq_arith_mean2_weighted_iff_of_nonneg
  结论: {w₁ w₂ p₁ p₂ : 实数} (hw₁ : 0 <= w₁)
  证明: by
  have := geom_mean_eq_arith_mean_weighted_iff_of_nonneg univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind

Depends on / 依赖: geom_mean_eq_arith_mean_weighted_iff_of_nonneg
-/
theorem geom_mean_eq_arith_mean2_weighted_iff_of_nonneg {w₁ w₂ p₁ p₂ : Real} (hw₁ : 0 <= w₁)
    (hw₂ : 0 <= w₂) (hp₁ : 0 <= p₁) (hp₂ : 0 <= p₂) (hw : w₁ + w₂ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ = w₁ * p₁ + w₂ * p₂ ↔ w₁ = 0 ∨ w₂ = 0 ∨ p₁ = p₂ := by
  have := geom_mean_eq_arith_mean_weighted_iff_of_nonneg univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind

/--
theorem `geom_mean_lt_arith_mean2_weighted_iff_of_pos` / 定理 `geom_mean_lt_arith_mean2_weighted_iff_of_pos`

English:
theorem geom_mean_lt_arith_mean2_weighted_iff_of_pos
  statement: {w₁ w₂ p₁ p₂ : Real} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
  proof: by
  have := geom_mean_lt_arith_mean_weighted_iff_of_pos univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind

中文:
定理 geom_mean_lt_arith_mean2_weighted_iff_of_pos
  结论: {w₁ w₂ p₁ p₂ : 实数} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
  证明: by
  have := geom_mean_lt_arith_mean_weighted_iff_of_pos univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind

Depends on / 依赖: geom_mean_lt_arith_mean_weighted_iff_of_pos
-/
theorem geom_mean_lt_arith_mean2_weighted_iff_of_pos {w₁ w₂ p₁ p₂ : Real} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hp₁ : 0 <= p₁) (hp₂ : 0 <= p₂) (hw : w₁ + w₂ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ < w₁ * p₁ + w₂ * p₂ ↔ p₁ != p₂ := by
  have := geom_mean_lt_arith_mean_weighted_iff_of_pos univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind

/--
theorem `geom_mean_lt_arith_mean2_weighted_iff_of_nonneg` / 定理 `geom_mean_lt_arith_mean2_weighted_iff_of_nonneg`

English:
theorem geom_mean_lt_arith_mean2_weighted_iff_of_nonneg
  statement: {w₁ w₂ p₁ p₂ : Real} (hw₁ : 0 <= w₁)
  proof: by
  have := geom_mean_lt_arith_mean_weighted_iff_of_nonneg univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind

中文:
定理 geom_mean_lt_arith_mean2_weighted_iff_of_nonneg
  结论: {w₁ w₂ p₁ p₂ : 实数} (hw₁ : 0 <= w₁)
  证明: by
  have := geom_mean_lt_arith_mean_weighted_iff_of_nonneg univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind

Depends on / 依赖: geom_mean_lt_arith_mean_weighted_iff_of_nonneg
-/
theorem geom_mean_lt_arith_mean2_weighted_iff_of_nonneg {w₁ w₂ p₁ p₂ : Real} (hw₁ : 0 <= w₁)
    (hw₂ : 0 <= w₂) (hp₁ : 0 <= p₁) (hp₂ : 0 <= p₂) (hw : w₁ + w₂ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ < w₁ * p₁ + w₂ * p₂ ↔ w₁ != 0 ∧ w₂ != 0 ∧ p₁ != p₂ := by
  have := geom_mean_lt_arith_mean_weighted_iff_of_nonneg univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind

end Real

end GeomMeanLEArithMean

section HarmMeanLEGeomMean

/-! ### HM-GM inequality -/

namespace Real

/--
theorem `harm_mean_le_geom_mean_weighted` / 定理 `harm_mean_le_geom_mean_weighted`

English:
theorem harm_mean_le_geom_mean_weighted
  statement: (w z : ι -> Real) (hs : s.Nonempty) (hw : forall i in s, 0 < w i)
  proof: by
  have : ∏ i in s, (1 / z) i ^ w i <= ∑ i in s, w i * (1 / z) i :=
    geom_mean_le_arith_mean_weighted s w (1 / z) (fun i hi => le_of_lt (hw i hi)) hw'
    (fun i hi => one_div_nonneg.2 (le_of_lt (hz i hi)))
  have p_pos : 0 < ∏ i in s, (z i)⁻¹ ^ w i :=
    prod_pos fun i hi => rpow_pos_of_pos (

中文:
定理 harm_mean_le_geom_mean_weighted
  结论: (w z : ι -> 实数) (hs : s.Nonempty) (hw : 对任意 i in s, 0 < w i)
  证明: by
  have : ∏ i in s, (1 / z) i ^ w i <= ∑ i in s, w i * (1 / z) i :=
    geom_mean_le_arith_mean_weighted s w (1 / z) (fun i hi => le_of_lt (hw i hi)) hw'
    (fun i hi => one_div_nonneg.2 (le_of_lt (hz i hi)))
  have p_pos : 0 < ∏ i in s, (z i)⁻¹ ^ w i :=
    prod_pos fun i hi => rpow_pos_of_pos (

Depends on / 依赖: Pi.div_apply, Pi.one_apply, div_apply, geom_mean_le_arith_mean_weighted, inv_pos, le_of_lt, mul_pos, one_apply, one_div, one_div_nonneg, p_pos, prod_pos, rpow_pos_of_pos, s_pos, sum_pos
-/
theorem harm_mean_le_geom_mean_weighted (w z : ι -> Real) (hs : s.Nonempty) (hw : forall i in s, 0 < w i)
    (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 < z i) :
    (∑ i in s, w i / z i)⁻¹ <= ∏ i in s, z i ^ w i := by
  have : ∏ i in s, (1 / z) i ^ w i <= ∑ i in s, w i * (1 / z) i :=
    geom_mean_le_arith_mean_weighted s w (1 / z) (fun i hi => le_of_lt (hw i hi)) hw'
    (fun i hi => one_div_nonneg.2 (le_of_lt (hz i hi)))
  have p_pos : 0 < ∏ i in s, (z i)⁻¹ ^ w i :=
    prod_pos fun i hi => rpow_pos_of_pos (inv_pos.2 (hz i hi)) _
  have s_pos : 0 < ∑ i in s, w i * (z i)⁻¹ :=
    sum_pos (fun i hi => mul_pos (hw i hi) (inv_pos.2 (hz i hi))) hs
  simp only [Pi.div_apply, Pi.one_apply, one_div, ← inv_le_inv₀ s_pos p_pos] at this
  apply le_trans this
  have p_pos₂ : 0 < (∏ i in s, (z i) ^ w i)⁻¹ :=
    inv_pos.2 (prod_pos fun i hi => rpow_pos_of_pos ((hz i hi)) _)
  rw [← inv_inv (∏ i in s]; rw [z i ^ w i)]; rw [inv_le_inv₀ p_pos p_pos₂]; rw [← Finset.prod_inv_distrib]
  gcongr
  · exact fun i hi => by positivity [hz i hi]
  · rw [Real.inv_rpow]; apply fun i hi => le_of_lt (hz i hi); assumption


/--
theorem `harm_mean_le_geom_mean` / 定理 `harm_mean_le_geom_mean`

English:
theorem harm_mean_le_geom_mean
  statement: {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (w : ι -> Real)
  proof: by
  have := harm_mean_le_geom_mean_weighted s (fun i => (w i) / ∑ i in s, w i) z hs ?_ ?_ hz
  · set n := ∑ i in s, w i
    nth_rw 1 [div_eq_mul_inv, (show n = (n⁻¹)⁻¹ by simp), ← mul_inv, Finset.mul_sum _ _ n⁻¹]
    simp_rw [inv_mul_eq_div n ((w _) / (z _)), div_right_comm _ _ n]
    convert! this

中文:
定理 harm_mean_le_geom_mean
  结论: {ι : 类型} (s : Finset ι) (hs : s.Nonempty) (w : ι -> 实数)
  证明: by
  have := harm_mean_le_geom_mean_weighted s (fun i => (w i) / ∑ i in s, w i) z hs ?_ ?_ hz
  · set n := ∑ i in s, w i
    nth_rw 1 [div_eq_mul_inv, (show n = (n⁻¹)⁻¹ by simp), ← mul_inv, Finset.mul_sum _ _ n⁻¹]
    simp_rw [inv_mul_eq_div n ((w _) / (z _)), div_right_comm _ _ n]
    convert! this

Depends on / 依赖: Finset, Finset.mul_sum, Finset.prod_congr, Real.finsetProd_rpow, Real.rpow_mul, convert, div_eq_mul_inv, div_right_comm, finsetProd_rpow, harm_mean_le_geom_mean_weighted, inv_mul_eq_div, le_of_lt, mul_inv, mul_sum, nth_rw, prod_congr, rpow_mul, simp_rw
-/
theorem harm_mean_le_geom_mean {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (w : ι -> Real)
    (z : ι -> Real) (hw : forall i in s, 0 < w i) (hw' : 0 < ∑ i in s, w i) (hz : forall i in s, 0 < z i) :
    (∑ i in s, w i) / (∑ i in s, w i / z i) <= (∏ i in s, z i ^ w i) ^ (∑ i in s, w i)⁻¹ := by
  have := harm_mean_le_geom_mean_weighted s (fun i => (w i) / ∑ i in s, w i) z hs ?_ ?_ hz
  · set n := ∑ i in s, w i
    nth_rw 1 [div_eq_mul_inv, (show n = (n⁻¹)⁻¹ by simp), ← mul_inv, Finset.mul_sum _ _ n⁻¹]
    simp_rw [inv_mul_eq_div n ((w _) / (z _)), div_right_comm _ _ n]
    convert! this
    rw [← Real.finsetProd_rpow s _ (fun i hi => by positivity [hz i hi])]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [← Real.rpow_mul (le_of_lt <| hz i hi) (w _) n⁻¹]; rw [div_eq_mul_inv (w _) n]
  · exact fun i hi => div_pos (hw i hi) hw'
  · simp_rw [div_eq_mul_inv (w _) (∑ i in s, w i), ← Finset.sum_mul _ _ (∑ i in s, w i)⁻¹]
    exact mul_inv_cancel₀ hw'.ne'

end Real

end HarmMeanLEGeomMean


section Young

/-! ### Young's inequality -/


namespace Real

/--
theorem `young_inequality_of_nonneg` / 定理 `young_inequality_of_nonneg`

English:
theorem young_inequality_of_nonneg
  statement: {a b p q : Real} (ha : 0 <= a) (hb : 0 <= b)
  proof: by
  simpa [← rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, div_eq_inv_mul] using
    geom_mean_le_arith_mean2_weighted hpq.inv_nonneg hpq.symm.inv_nonneg
      (rpow_nonneg ha p) (rpow_nonneg hb q) hpq.inv_add_inv_eq_one

中文:
定理 young_inequality_of_nonneg
  结论: {a b p q : 实数} (ha : 0 <= a) (hb : 0 <= b)
  证明: by
  simpa [← rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, div_eq_inv_mul] using
    geom_mean_le_arith_mean2_weighted hpq.inv_nonneg hpq.symm.inv_nonneg
      (rpow_nonneg ha p) (rpow_nonneg hb q) hpq.inv_add_inv_eq_one

Depends on / 依赖: div_eq_inv_mul, geom_mean_le_arith_mean2_weighted, hpq.inv_add_inv_eq_one, hpq.inv_nonneg, hpq.ne_zero, hpq.symm.inv_nonneg, hpq.symm.ne_zero, inv_add_inv_eq_one, inv_nonneg, ne_zero, rpow_mul, rpow_nonneg
-/
theorem young_inequality_of_nonneg {a b p q : Real} (ha : 0 <= a) (hb : 0 <= b)
    (hpq : p.HolderConjugate q) : a * b <= a ^ p / p + b ^ q / q := by
  simpa [← rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, div_eq_inv_mul] using
    geom_mean_le_arith_mean2_weighted hpq.inv_nonneg hpq.symm.inv_nonneg
      (rpow_nonneg ha p) (rpow_nonneg hb q) hpq.inv_add_inv_eq_one

/--
theorem `young_inequality` / 定理 `young_inequality`

English:
theorem young_inequality
  given: (a b : Real) {p q : Real} (hpq : p.HolderConjugate q)
  proof: calc
    a * b <= |a * b| := le_abs_self (a * b)
    _ = |a| * |b| := abs_mul a b
    _ <= |a| ^ p / p + |b| ^ q / q :=
      Real.young_inequality_of_nonneg (abs_nonneg a) (abs_nonneg b) hpq

中文:
定理 young_inequality
  条件: (a b : 实数) {p q : 实数} (hpq : p.HolderConjugate q)
  证明: calc
    a * b <= |a * b| := le_abs_self (a * b)
    _ = |a| * |b| := abs_mul a b
    _ <= |a| ^ p / p + |b| ^ q / q :=
      Real.young_inequality_of_nonneg (abs_nonneg a) (abs_nonneg b) hpq

Depends on / 依赖: Real.young_inequality_of_nonneg, abs_mul, abs_nonneg, le_abs_self, young_inequality_of_nonneg
-/
theorem young_inequality (a b : Real) {p q : Real} (hpq : p.HolderConjugate q) :
    a * b <= |a| ^ p / p + |b| ^ q / q :=
  calc
    a * b <= |a * b| := le_abs_self (a * b)
    _ = |a| * |b| := abs_mul a b
    _ <= |a| ^ p / p + |b| ^ q / q :=
      Real.young_inequality_of_nonneg (abs_nonneg a) (abs_nonneg b) hpq

/--
theorem `young_inequality_eq_iff_of_nonneg` / 定理 `young_inequality_eq_iff_of_nonneg`

English:
theorem young_inequality_eq_iff_of_nonneg
  statement: {a b p q : Real} (ha : 0 <= a) (hb : 0 <= b)
  proof: by
  simpa [← rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, div_eq_inv_mul] using
    geom_mean_eq_arith_mean2_weighted_iff_of_nonneg hpq.inv_nonneg hpq.symm.inv_nonneg
      (rpow_nonneg ha p) (rpow_nonneg hb q) hpq.inv_add_inv_eq_one

中文:
定理 young_inequality_eq_iff_of_nonneg
  结论: {a b p q : 实数} (ha : 0 <= a) (hb : 0 <= b)
  证明: by
  simpa [← rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, div_eq_inv_mul] using
    geom_mean_eq_arith_mean2_weighted_iff_of_nonneg hpq.inv_nonneg hpq.symm.inv_nonneg
      (rpow_nonneg ha p) (rpow_nonneg hb q) hpq.inv_add_inv_eq_one

Depends on / 依赖: div_eq_inv_mul, geom_mean_eq_arith_mean2_weighted_iff_of_nonneg, hpq.inv_add_inv_eq_one, hpq.inv_nonneg, hpq.ne_zero, hpq.symm.inv_nonneg, hpq.symm.ne_zero, inv_add_inv_eq_one, inv_nonneg, ne_zero, rpow_mul, rpow_nonneg
-/
theorem young_inequality_eq_iff_of_nonneg {a b p q : Real} (ha : 0 <= a) (hb : 0 <= b)
    (hpq : p.HolderConjugate q) : a * b = a ^ p / p + b ^ q / q ↔ a ^ p = b ^ q := by
  simpa [← rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, div_eq_inv_mul] using
    geom_mean_eq_arith_mean2_weighted_iff_of_nonneg hpq.inv_nonneg hpq.symm.inv_nonneg
      (rpow_nonneg ha p) (rpow_nonneg hb q) hpq.inv_add_inv_eq_one

end Real

namespace NNReal

/--
theorem `young_inequality` / 定理 `young_inequality`

English:
theorem young_inequality
  given: (a b : Real>=0) {p q : Real>=0} (hpq : p.HolderConjugate q)
  proof: Real.young_inequality_of_nonneg a.coe_nonneg b.coe_nonneg hpq.coe

中文:
定理 young_inequality
  条件: (a b : 实数>=0) {p q : 实数>=0} (hpq : p.HolderConjugate q)
  证明: Real.young_inequality_of_nonneg a.coe_nonneg b.coe_nonneg hpq.coe

Depends on / 依赖: Real.young_inequality_of_nonneg, a.coe_nonneg, b.coe_nonneg, coe_nonneg, hpq.coe, young_inequality_of_nonneg
-/
theorem young_inequality (a b : Real>=0) {p q : Real>=0} (hpq : p.HolderConjugate q) :
    a * b <= a ^ (p : Real) / p + b ^ (q : Real) / q :=
  Real.young_inequality_of_nonneg a.coe_nonneg b.coe_nonneg hpq.coe

/--
theorem `young_inequality_real` / 定理 `young_inequality_real`

English:
theorem young_inequality_real
  given: (a b : Real>=0) {p q : Real} (hpq : p.HolderConjugate q)
  proof: by
  simpa [hpq.nonneg, hpq.symm.nonneg] using young_inequality a b hpq.toNNReal

中文:
定理 young_inequality_real
  条件: (a b : 实数>=0) {p q : 实数} (hpq : p.HolderConjugate q)
  证明: by
  simpa [hpq.nonneg, hpq.symm.nonneg] using young_inequality a b hpq.toNNReal

Depends on / 依赖: hpq.nonneg, hpq.symm.nonneg, hpq.toNNReal, nonneg, toNNReal, young_inequality
-/
theorem young_inequality_real (a b : Real>=0) {p q : Real} (hpq : p.HolderConjugate q) :
    a * b <= a ^ p / p.toNNReal + b ^ q / q.toNNReal := by
  simpa [hpq.nonneg, hpq.symm.nonneg] using young_inequality a b hpq.toNNReal

/--
theorem `young_inequality_eq_iff` / 定理 `young_inequality_eq_iff`

English:
theorem young_inequality_eq_iff
  given: (a b : Real>=0) {p q : Real>=0} (hpq : p.HolderConjugate q)
  proof: mod_cast Real.young_inequality_eq_iff_of_nonneg a.coe_nonneg b.coe_nonneg hpq.coe

中文:
定理 young_inequality_eq_iff
  条件: (a b : 实数>=0) {p q : 实数>=0} (hpq : p.HolderConjugate q)
  证明: mod_cast Real.young_inequality_eq_iff_of_nonneg a.coe_nonneg b.coe_nonneg hpq.coe

Depends on / 依赖: Real.young_inequality_eq_iff_of_nonneg, a.coe_nonneg, b.coe_nonneg, coe_nonneg, hpq.coe, mod_cast, young_inequality_eq_iff_of_nonneg
-/
theorem young_inequality_eq_iff (a b : Real>=0) {p q : Real>=0} (hpq : p.HolderConjugate q) :
    a * b = a ^ (p : Real) / p + b ^ (q : Real) / q ↔ a ^ (p : Real) = b ^ (q : Real) :=
  mod_cast Real.young_inequality_eq_iff_of_nonneg a.coe_nonneg b.coe_nonneg hpq.coe

/--
theorem `young_inequality_real_eq_iff` / 定理 `young_inequality_real_eq_iff`

English:
theorem young_inequality_real_eq_iff
  given: (a b : Real>=0) {p q : Real} (hpq : p.HolderConjugate q)
  proof: by
  simpa [hpq.nonneg, hpq.symm.nonneg] using young_inequality_eq_iff a b hpq.toNNReal

中文:
定理 young_inequality_real_eq_iff
  条件: (a b : 实数>=0) {p q : 实数} (hpq : p.HolderConjugate q)
  证明: by
  simpa [hpq.nonneg, hpq.symm.nonneg] using young_inequality_eq_iff a b hpq.toNNReal

Depends on / 依赖: hpq.nonneg, hpq.symm.nonneg, hpq.toNNReal, nonneg, toNNReal, young_inequality_eq_iff
-/
theorem young_inequality_real_eq_iff (a b : Real>=0) {p q : Real} (hpq : p.HolderConjugate q) :
    a * b = a ^ p / p.toNNReal + b ^ q / q.toNNReal ↔ a ^ p = b ^ q := by
  simpa [hpq.nonneg, hpq.symm.nonneg] using young_inequality_eq_iff a b hpq.toNNReal

end NNReal

namespace ENNReal

/--
theorem `young_inequality` / 定理 `young_inequality`

English:
theorem young_inequality
  given: (a b : Real>=0∞) {p q : Real} (hpq : p.HolderConjugate q)
  proof: by
  by_cases! h : a = ⊤ ∨ b = ⊤
  · refine le_trans le_top (le_of_eq ?_)
    repeat rw [div_eq_mul_inv]
    rcases h with h | h <;> rw [h] <;> simp [hpq.pos, hpq.symm.pos]
  -- if `a ≠ ⊤` and `b ≠ ⊤`, use the `NNReal` version: `NNReal.young_inequality_real`
  rw [← coe_toNNReal h.left]; rw [← coe_t

中文:
定理 young_inequality
  条件: (a b : 实数>=0∞) {p q : 实数} (hpq : p.HolderConjugate q)
  证明: by
  by_cases! h : a = ⊤ ∨ b = ⊤
  · refine le_trans le_top (le_of_eq ?_)
    repeat rw [div_eq_mul_inv]
    rcases h with h | h <;> rw [h] <;> simp [hpq.pos, hpq.symm.pos]
  -- if `a ≠ ⊤` and `b ≠ ⊤`, use the `NNReal` version: `NNReal.young_inequality_real`
  rw [← coe_toNNReal h.left]; rw [← coe_t

Depends on / 依赖: div_eq_mul_inv, hpq.pos, hpq.symm.pos, le_of_eq, le_top, le_trans, repeat
-/
theorem young_inequality (a b : Real>=0∞) {p q : Real} (hpq : p.HolderConjugate q) :
    a * b <= a ^ p / ENNReal.ofReal p + b ^ q / ENNReal.ofReal q := by
  by_cases! h : a = ⊤ ∨ b = ⊤
  · refine le_trans le_top (le_of_eq ?_)
    repeat rw [div_eq_mul_inv]
    rcases h with h | h <;> rw [h] <;> simp [hpq.pos, hpq.symm.pos]
  -- if `a ≠ ⊤` and `b ≠ ⊤`, use the `NNReal` version: `NNReal.young_inequality_real`
  rw [← coe_toNNReal h.left]; rw [← coe_toNNReal h.right]; rw [← coe_mul]; rw [← coe_rpow_of_nonneg _ hpq.nonneg]; rw [← coe_rpow_of_nonneg _ hpq.symm.nonneg]; rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [←
    @coe_div (Real.toNNReal p) _ (by simp [hpq.pos]), ←
    @coe_div (Real.toNNReal q) _ (by simp [hpq.symm.pos]), ← coe_add, coe_le_coe]
  exact NNReal.young_inequality_real a.toNNReal b.toNNReal hpq

/--
theorem `young_inequality_eq_iff` / 定理 `young_inequality_eq_iff`

English:
theorem young_inequality_eq_iff
  given: (a b : Real>=0∞) {p q : Real} (hpq : p.HolderConjugate q)
  proof: by
  by_cases! h0 : a = 0 ∨ b = 0
  · rcases h0 with rfl | rfl <;> simp [hpq.pos, hpq.symm.pos, eq_comm]
  by_cases! h : a = ⊤ ∨ b = ⊤
  · rcases h with rfl | rfl <;> simp [hpq.pos, hpq.symm.pos, h0, div_eq_mul_inv]
  rw [← coe_toNNReal h.left]; rw [← coe_toNNReal h.right]; rw [← coe_mul]; rw [← coe

中文:
定理 young_inequality_eq_iff
  条件: (a b : 实数>=0∞) {p q : 实数} (hpq : p.HolderConjugate q)
  证明: by
  by_cases! h0 : a = 0 ∨ b = 0
  · rcases h0 with rfl | rfl <;> simp [hpq.pos, hpq.symm.pos, eq_comm]
  by_cases! h : a = ⊤ ∨ b = ⊤
  · rcases h with rfl | rfl <;> simp [hpq.pos, hpq.symm.pos, h0, div_eq_mul_inv]
  rw [← coe_toNNReal h.left]; rw [← coe_toNNReal h.right]; rw [← coe_mul]; rw [← coe

Depends on / 依赖: coe_add, coe_div, coe_mul, coe_rpow_of_nonneg, coe_toNNReal, div_eq_mul_inv, eq_comm, h.left, h.right, hpq.nonneg, hpq.pos, hpq.symm.nonneg, hpq.symm.pos, nonneg, ofNNReal_toNNReal
-/
theorem young_inequality_eq_iff (a b : Real>=0∞) {p q : Real} (hpq : p.HolderConjugate q) :
    a * b = a ^ p / .ofReal p + b ^ q / .ofReal q ↔
      (a = ⊤ ∧ b != 0) ∨ (a != 0 ∧ b = ⊤) ∨ a ^ p = b ^ q := by
  by_cases! h0 : a = 0 ∨ b = 0
  · rcases h0 with rfl | rfl <;> simp [hpq.pos, hpq.symm.pos, eq_comm]
  by_cases! h : a = ⊤ ∨ b = ⊤
  · rcases h with rfl | rfl <;> simp [hpq.pos, hpq.symm.pos, h0, div_eq_mul_inv]
  rw [← coe_toNNReal h.left]; rw [← coe_toNNReal h.right]; rw [← coe_mul]; rw [← coe_rpow_of_nonneg _ hpq.nonneg]; rw [← coe_rpow_of_nonneg _ hpq.symm.nonneg]; rw [← ofNNReal_toNNReal]; rw [← ofNNReal_toNNReal]; rw [← coe_div (by simp [hpq.pos]), ← coe_div (by simp [hpq.symm.pos]), ← coe_add, coe_inj, coe_inj]
  simp [young_inequality_real_eq_iff a.toNNReal b.toNNReal hpq]

end ENNReal

end Young

section HoelderMinkowski

/-! ### Hölder's and Minkowski's inequalities -/


namespace NNReal

/--
theorem `inner_le_Lp_mul_Lp_of_norm_le_one` / 定理 `inner_le_Lp_mul_Lp_of_norm_le_one`

English:
theorem inner_le_Lp_mul_Lp_of_norm_le_one
  statement: (f g : ι -> Real>=0) {p q : Real}
  proof: by
  have hp : 0 < p.toNNReal := zero_lt_one.trans hpq.toNNReal.lt
  have hq : 0 < q.toNNReal := zero_lt_one.trans hpq.toNNReal.symm.lt
  calc
    ∑ i in s, f i * g i <= ∑ i in s, (f i ^ p / Real.toNNReal p + g i ^ q / Real.toNNReal q) :=
      Finset.sum_le_sum fun i _ => young_inequality_real (f i

中文:
定理 inner_le_Lp_mul_Lp_of_norm_le_one
  结论: (f g : ι -> 实数>=0) {p q : 实数}
  证明: by
  have hp : 0 < p.toNNReal := zero_lt_one.trans hpq.toNNReal.lt
  have hq : 0 < q.toNNReal := zero_lt_one.trans hpq.toNNReal.symm.lt
  calc
    ∑ i in s, f i * g i <= ∑ i in s, (f i ^ p / Real.toNNReal p + g i ^ q / Real.toNNReal q) :=
      Finset.sum_le_sum fun i _ => young_inequality_real (f i
-/
private theorem inner_le_Lp_mul_Lp_of_norm_le_one (f g : ι -> Real>=0) {p q : Real}
    (hpq : p.HolderConjugate q) (hf : ∑ i in s, f i ^ p <= 1) (hg : ∑ i in s, g i ^ q <= 1) :
    ∑ i in s, f i * g i <= 1 := by
  have hp : 0 < p.toNNReal := zero_lt_one.trans hpq.toNNReal.lt
  have hq : 0 < q.toNNReal := zero_lt_one.trans hpq.toNNReal.symm.lt
  calc
    ∑ i in s, f i * g i <= ∑ i in s, (f i ^ p / Real.toNNReal p + g i ^ q / Real.toNNReal q) :=
      Finset.sum_le_sum fun i _ => young_inequality_real (f i) (g i) hpq
    _ = (∑ i in s, f i ^ p) / Real.toNNReal p + (∑ i in s, g i ^ q) / Real.toNNReal q := by
      rw [sum_add_distrib]; rw [sum_div]; rw [sum_div]
    _ <= 1 / Real.toNNReal p + 1 / Real.toNNReal q := by gcongr
    _ = 1 := by simp_rw [one_div, hpq.toNNReal.inv_add_inv_eq_one]

/--
theorem `inner_le_Lp_mul_Lp_of_norm_eq_zero` / 定理 `inner_le_Lp_mul_Lp_of_norm_eq_zero`

English:
theorem inner_le_Lp_mul_Lp_of_norm_eq_zero
  statement: (f g : ι -> Real>=0) {p q : Real}
  proof: by
  simp only [hf, hpq.ne_zero, one_div, sum_eq_zero_iff, zero_rpow, zero_mul,
    inv_eq_zero, Ne, not_false_iff, le_zero_iff, mul_eq_zero]
  intro i his
  left
  rw [sum_eq_zero_iff] at hf
  exact (rpow_eq_zero_iff.mp (hf i his)).left

中文:
定理 inner_le_Lp_mul_Lp_of_norm_eq_zero
  结论: (f g : ι -> 实数>=0) {p q : 实数}
  证明: by
  simp only [hf, hpq.ne_zero, one_div, sum_eq_zero_iff, zero_rpow, zero_mul,
    inv_eq_zero, Ne, not_false_iff, le_zero_iff, mul_eq_zero]
  intro i his
  left
  rw [sum_eq_zero_iff] at hf
  exact (rpow_eq_zero_iff.mp (hf i his)).left
-/
private theorem inner_le_Lp_mul_Lp_of_norm_eq_zero (f g : ι -> Real>=0) {p q : Real}
    (hpq : p.HolderConjugate q) (hf : ∑ i in s, f i ^ p = 0) :
    ∑ i in s, f i * g i <= (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) := by
  simp only [hf, hpq.ne_zero, one_div, sum_eq_zero_iff, zero_rpow, zero_mul,
    inv_eq_zero, Ne, not_false_iff, le_zero_iff, mul_eq_zero]
  intro i his
  left
  rw [sum_eq_zero_iff] at hf
  exact (rpow_eq_zero_iff.mp (hf i his)).left

/--
theorem `inner_le_Lp_mul_Lq` / 定理 `inner_le_Lp_mul_Lq`

English:
theorem inner_le_Lp_mul_Lq
  given: (f g : ι -> Real>=0) {p q : Real} (hpq : p.HolderConjugate q)
  proof: by
  obtain hf | hf := eq_zero_or_pos (∑ i in s, f i ^ p)
  · exact inner_le_Lp_mul_Lp_of_norm_eq_zero s f g hpq hf
  obtain hg | hg := eq_zero_or_pos (∑ i in s, g i ^ q)
  · calc
      ∑ i in s, f i * g i = ∑ i in s, g i * f i := by
        congr with i
        rw [mul_comm]
      _ <= (∑ i in s, g

中文:
定理 inner_le_Lp_mul_Lq
  条件: (f g : ι -> 实数>=0) {p q : 实数} (hpq : p.HolderConjugate q)
  证明: by
  obtain hf | hf := eq_zero_or_pos (∑ i in s, f i ^ p)
  · exact inner_le_Lp_mul_Lp_of_norm_eq_zero s f g hpq hf
  obtain hg | hg := eq_zero_or_pos (∑ i in s, g i ^ q)
  · calc
      ∑ i in s, f i * g i = ∑ i in s, g i * f i := by
        congr with i
        rw [mul_comm]
      _ <= (∑ i in s, g

Depends on / 依赖: eq_zero_or_pos, hpq.symm, inner_le_Lp_mul_Lp_of_norm_eq_zero, mul_comm
-/
theorem inner_le_Lp_mul_Lq (f g : ι -> Real>=0) {p q : Real} (hpq : p.HolderConjugate q) :
    ∑ i in s, f i * g i <= (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) := by
  obtain hf | hf := eq_zero_or_pos (∑ i in s, f i ^ p)
  · exact inner_le_Lp_mul_Lp_of_norm_eq_zero s f g hpq hf
  obtain hg | hg := eq_zero_or_pos (∑ i in s, g i ^ q)
  · calc
      ∑ i in s, f i * g i = ∑ i in s, g i * f i := by
        congr with i
        rw [mul_comm]
      _ <= (∑ i in s, g i ^ q) ^ (1 / q) * (∑ i in s, f i ^ p) ^ (1 / p) :=
        (inner_le_Lp_mul_Lp_of_norm_eq_zero s g f hpq.symm hg)
      _ = (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) := mul_comm _ _
  let f' i := f i / (∑ i in s, f i ^ p) ^ (1 / p)
  let g' i := g i / (∑ i in s, g i ^ q) ^ (1 / q)
  suffices (∑ i in s, f' i * g' i) <= 1 by
    simp_rw [f', g', div_mul_div_comm, ← sum_div] at this
    rwa [div_le_iff₀, one_mul] at this
    positivity
  refine inner_le_Lp_mul_Lp_of_norm_le_one s f' g' hpq (le_of_eq ?_) (le_of_eq ?_)
  · simp_rw [f', div_rpow, ← sum_div, ← rpow_mul, one_div, inv_mul_cancel₀ hpq.ne_zero, rpow_one,
      div_self hf.ne']
  · simp_rw [g', div_rpow, ← sum_div, ← rpow_mul, one_div, inv_mul_cancel₀ hpq.symm.ne_zero,
      rpow_one, div_self hg.ne']

/--
theorem `Lr_rpow_le_Lp_mul_Lq` / 定理 `Lr_rpow_le_Lp_mul_Lq`

English:
theorem Lr_rpow_le_Lp_mul_Lq
  given: (f g : ι -> Real>=0) {p q r : Real} (hpqr : p.HolderTriple q r)
  proof: by
  simpa [mul_rpow, ← NNReal.rpow_mul, ← mul_div_assoc, hpqr.pos'.ne', fieldEq] using
    inner_le_Lp_mul_Lq s (fun i => f i ^ r) (fun i => g i ^ r) hpqr.holderConjugate_div_div

中文:
定理 Lr_rpow_le_Lp_mul_Lq
  条件: (f g : ι -> 实数>=0) {p q r : 实数} (hpqr : p.HolderTriple q r)
  证明: by
  simpa [mul_rpow, ← NNReal.rpow_mul, ← mul_div_assoc, hpqr.pos'.ne', fieldEq] using
    inner_le_Lp_mul_Lq s (fun i => f i ^ r) (fun i => g i ^ r) hpqr.holderConjugate_div_div

Depends on / 依赖: NNReal, NNReal.rpow_mul, fieldEq, holderConjugate_div_div, hpqr.holderConjugate_div_div, hpqr.pos, inner_le_Lp_mul_Lq, mul_div_assoc, mul_rpow, rpow_mul
-/
theorem Lr_rpow_le_Lp_mul_Lq (f g : ι -> Real>=0) {p q r : Real} (hpqr : p.HolderTriple q r) :
    ∑ i in s, (f i * g i) ^ r <= (∑ i in s, f i ^ p) ^ (r / p) * (∑ i in s, g i ^ q) ^ (r / q) := by
  simpa [mul_rpow, ← NNReal.rpow_mul, ← mul_div_assoc, hpqr.pos'.ne', fieldEq] using
    inner_le_Lp_mul_Lq s (fun i => f i ^ r) (fun i => g i ^ r) hpqr.holderConjugate_div_div

/--
theorem `Lr_le_Lp_mul_Lq` / 定理 `Lr_le_Lp_mul_Lq`

English:
theorem Lr_le_Lp_mul_Lq
  given: (f g : ι -> Real>=0) {p q r : Real} (hpqr : p.HolderTriple q r)
  proof: by
  convert
.mpr rpow_le_rpow_iff (inv_eq_one_div r ▸ inv_pos.mpr hpqr.pos' : 0 < 1 / r)
      Lr_rpow_le_Lp_mul_Lq s f g hpqr
  have hr := hpqr.pos'.ne'
  simp only [← rpow_mul, mul_rpow]
  field_simp

中文:
定理 Lr_le_Lp_mul_Lq
  条件: (f g : ι -> 实数>=0) {p q r : 实数} (hpqr : p.HolderTriple q r)
  证明: by
  convert
.mpr rpow_le_rpow_iff (inv_eq_one_div r ▸ inv_pos.mpr hpqr.pos' : 0 < 1 / r)
      Lr_rpow_le_Lp_mul_Lq s f g hpqr
  have hr := hpqr.pos'.ne'
  simp only [← rpow_mul, mul_rpow]
  field_simp

Depends on / 依赖: Lr_rpow_le_Lp_mul_Lq, convert, hpqr.pos, inv_eq_one_div, inv_pos, inv_pos.mpr, mul_rpow, rpow_le_rpow_iff, rpow_mul
-/
theorem Lr_le_Lp_mul_Lq (f g : ι -> Real>=0) {p q r : Real} (hpqr : p.HolderTriple q r) :
    (∑ i in s, (f i * g i) ^ r) ^ (1 / r) <=
      (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) := by
  convert
.mpr rpow_le_rpow_iff (inv_eq_one_div r ▸ inv_pos.mpr hpqr.pos' : 0 < 1 / r)
      Lr_rpow_le_Lp_mul_Lq s f g hpqr
  have hr := hpqr.pos'.ne'
  simp only [← rpow_mul, mul_rpow]
  field_simp

/--
lemma `inner_le_weight_mul_Lp` / 引理 `inner_le_weight_mul_Lp`

English:
lemma inner_le_weight_mul_Lp
  given: (s : Finset ι) {p : Real} (hp : 1 <= p) (w f : ι -> Real>=0)
  proof: by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  calc
    _ = ∑ i in s, w i ^ (1 - p⁻¹) * (w i ^ p⁻¹ * f i) := ?_
    _ <= (∑ i in s, (w i ^ (1 - p⁻¹)) ^ (1 - p⁻¹)⁻¹) ^ (1 / (1 - p⁻¹)⁻¹) *
          (∑ i in s, (w i ^ p⁻¹ * f i) ^ p) ^ (1 / p) :=
        inner_le_Lp_mul_Lq _ _ _ (.symm <| Real.holderCo

中文:
引理 inner_le_weight_mul_Lp
  条件: (s : Finset ι) {p : 实数} (hp : 1 <= p) (w f : ι -> 实数>=0)
  证明: by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  calc
    _ = ∑ i in s, w i ^ (1 - p⁻¹) * (w i ^ p⁻¹ * f i) := ?_
    _ <= (∑ i in s, (w i ^ (1 - p⁻¹)) ^ (1 - p⁻¹)⁻¹) ^ (1 / (1 - p⁻¹)⁻¹) *
          (∑ i in s, (w i ^ p⁻¹ * f i) ^ p) ^ (1 / p) :=
        inner_le_Lp_mul_Lq _ _ _ (.symm <| Real.holderCo

Depends on / 依赖: Real.holderConjugate_iff.mpr, eq_or_lt, holderConjugate_iff, hp.eq_or_lt, hp.ne, inner_le_Lp_mul_Lq, mul_assoc, one_ne_zero, rpow_of_add_eq, rpow_one, sub_eq_zero
-/
lemma inner_le_weight_mul_Lp (s : Finset ι) {p : Real} (hp : 1 <= p) (w f : ι -> Real>=0) :
    ∑ i in s, w i * f i <= (∑ i in s, w i) ^ (1 - p⁻¹) * (∑ i in s, w i * f i ^ p) ^ p⁻¹ := by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  calc
    _ = ∑ i in s, w i ^ (1 - p⁻¹) * (w i ^ p⁻¹ * f i) := ?_
    _ <= (∑ i in s, (w i ^ (1 - p⁻¹)) ^ (1 - p⁻¹)⁻¹) ^ (1 / (1 - p⁻¹)⁻¹) *
          (∑ i in s, (w i ^ p⁻¹ * f i) ^ p) ^ (1 / p) :=
        inner_le_Lp_mul_Lq _ _ _ (.symm <| Real.holderConjugate_iff.mpr ⟨hp, by simp⟩)
    _ = _ := ?_
  · congr with i
    rw [← mul_assoc]; rw [← rpow_of_add_eq _ one_ne_zero]; rw [rpow_one]
    simp
  · have hp₀ : p != 0 := by positivity
    have hp₁ : 1 - p⁻¹ != 0 := by simp [sub_eq_zero, hp.ne']
    simp [mul_rpow, div_inv_eq_mul, one_mul, one_div, hp₀, hp₁]

/--
theorem `summable_and_Lr_rpow_le_Lp_mul_Lq_tsum` / 定理 `summable_and_Lr_rpow_le_Lp_mul_Lq_tsum`

English:
theorem summable_and_Lr_rpow_le_Lp_mul_Lq_tsum
  statement: {f g : ι -> Real>=0} {p q r : Real}
  proof: by
  have H₁ : forall s : Finset ι,
      ∑ i in s, (f i * g i) ^ r <= (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) := by
    intro s
    obtain ⟨hp, hq, hr⟩ := hpqr.all_pos
    refine le_trans (Lr_rpow_le_Lp_mul_Lq s f g hpqr) (mul_le_mul ?_ ?_ bot_le bot_le)
    · gcongr
      exact hf.su

中文:
定理 summable_and_Lr_rpow_le_Lp_mul_Lq_tsum
  结论: {f g : ι -> 实数>=0} {p q r : 实数}
  证明: by
  have H₁ : forall s : Finset ι,
      ∑ i in s, (f i * g i) ^ r <= (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) := by
    intro s
    obtain ⟨hp, hq, hr⟩ := hpqr.all_pos
    refine le_trans (Lr_rpow_le_Lp_mul_Lq s f g hpqr) (mul_le_mul ?_ ?_ bot_le bot_le)
    · gcongr
      exact hf.su

Depends on / 依赖: BddAbove, Finset, Lr_rpow_le_Lp_mul_Lq, Set.range, all_pos, bot_le, hf.sum_le_tsum, hg.sum_le_tsum, hpqr.all_pos, le_trans, mul_le_mul, sum_le_tsum, zero_le
-/
theorem summable_and_Lr_rpow_le_Lp_mul_Lq_tsum {f g : ι -> Real>=0} {p q r : Real}
    (hpqr : p.HolderTriple q r) (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (Summable fun i => (f i * g i) ^ r) ∧
      ∑' i, (f i * g i) ^ r <= (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) := by
  have H₁ : forall s : Finset ι,
      ∑ i in s, (f i * g i) ^ r <= (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) := by
    intro s
    obtain ⟨hp, hq, hr⟩ := hpqr.all_pos
    refine le_trans (Lr_rpow_le_Lp_mul_Lq s f g hpqr) (mul_le_mul ?_ ?_ bot_le bot_le)
    · gcongr
      exact hf.sum_le_tsum _ (fun _ _ => zero_le)
    · gcongr
      exact hg.sum_le_tsum _ (fun _ _ => zero_le)
  have bdd : BddAbove (Set.range fun s => ∑ i in s, (f i * g i) ^ r) := by
    refine ⟨(∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q), ?_⟩
    rintro a ⟨s, rfl⟩
    exact H₁ s
  have H₂ : Summable _ := (hasSum_of_isLUB _ (isLUB_ciSup bdd)).summable
  exact ⟨H₂, H₂.tsum_le_of_sum_le H₁⟩

/--
theorem `summable_and_inner_le_Lp_mul_Lq_tsum` / 定理 `summable_and_inner_le_Lp_mul_Lq_tsum`

English:
theorem summable_and_inner_le_Lp_mul_Lq_tsum
  statement: {f g : ι -> Real>=0} {p q : Real} (hpq : p.HolderConjugate q)
  proof: by
  simpa using summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpq hf hg

中文:
定理 summable_and_inner_le_Lp_mul_Lq_tsum
  结论: {f g : ι -> 实数>=0} {p q : 实数} (hpq : p.HolderConjugate q)
  证明: by
  simpa using summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpq hf hg

Depends on / 依赖: summable_and_Lr_rpow_le_Lp_mul_Lq_tsum
-/
theorem summable_and_inner_le_Lp_mul_Lq_tsum {f g : ι -> Real>=0} {p q : Real} (hpq : p.HolderConjugate q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (Summable fun i => f i * g i) ∧
      ∑' i, f i * g i <= (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  simpa using summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpq hf hg

/--
theorem `summable_mul_rpow_of_Lp_Lq` / 定理 `summable_mul_rpow_of_Lp_Lq`

English:
theorem summable_mul_rpow_of_Lp_Lq
  statement: {f g : ι -> Real>=0} {p q r : Real} (hpqr : p.HolderTriple q r)
  proof: (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg).1

中文:
定理 summable_mul_rpow_of_Lp_Lq
  结论: {f g : ι -> 实数>=0} {p q r : 实数} (hpqr : p.HolderTriple q r)
  证明: (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg).1

Depends on / 依赖: summable_and_Lr_rpow_le_Lp_mul_Lq_tsum
-/
theorem summable_mul_rpow_of_Lp_Lq {f g : ι -> Real>=0} {p q r : Real} (hpqr : p.HolderTriple q r)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    Summable fun i => (f i * g i) ^ r :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg).1

/--
theorem `summable_mul_of_Lp_Lq` / 定理 `summable_mul_of_Lp_Lq`

English:
theorem summable_mul_of_Lp_Lq
  statement: {f g : ι -> Real>=0} {p q : Real} (hpq : p.HolderConjugate q)
  proof: (summable_and_inner_le_Lp_mul_Lq_tsum hpq hf hg).1

中文:
定理 summable_mul_of_Lp_Lq
  结论: {f g : ι -> 实数>=0} {p q : 实数} (hpq : p.HolderConjugate q)
  证明: (summable_and_inner_le_Lp_mul_Lq_tsum hpq hf hg).1

Depends on / 依赖: summable_and_inner_le_Lp_mul_Lq_tsum
-/
theorem summable_mul_of_Lp_Lq {f g : ι -> Real>=0} {p q : Real} (hpq : p.HolderConjugate q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    Summable fun i => f i * g i :=
  (summable_and_inner_le_Lp_mul_Lq_tsum hpq hf hg).1

/--
theorem `Lr_rpow_le_Lp_mul_Lq_tsum` / 定理 `Lr_rpow_le_Lp_mul_Lq_tsum`

English:
theorem Lr_rpow_le_Lp_mul_Lq_tsum
  statement: {f g : ι -> Real>=0} {p q r : Real} (hpqr : p.HolderTriple q r)
  proof: (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg).2

中文:
定理 Lr_rpow_le_Lp_mul_Lq_tsum
  结论: {f g : ι -> 实数>=0} {p q r : 实数} (hpqr : p.HolderTriple q r)
  证明: (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg).2

Depends on / 依赖: summable_and_Lr_rpow_le_Lp_mul_Lq_tsum
-/
theorem Lr_rpow_le_Lp_mul_Lq_tsum {f g : ι -> Real>=0} {p q r : Real} (hpqr : p.HolderTriple q r)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    ∑' i, (f i * g i) ^ r <= (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg).2

/--
theorem `Lr_le_Lp_mul_Lq_tsum` / 定理 `Lr_le_Lp_mul_Lq_tsum`

English:
theorem Lr_le_Lp_mul_Lq_tsum
  statement: {f g : ι -> Real>=0} {p q r : Real} (hpqr : p.HolderTriple q r)
  proof: by
  convert!
.mpr rpow_le_rpow_iff (inv_eq_one_div r ▸ inv_pos.mpr hpqr.pos')
      Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg
  have hr := hpqr.pos'.ne'
  simp only [← rpow_mul, mul_rpow]
  field_simp

中文:
定理 Lr_le_Lp_mul_Lq_tsum
  结论: {f g : ι -> 实数>=0} {p q r : 实数} (hpqr : p.HolderTriple q r)
  证明: by
  convert!
.mpr rpow_le_rpow_iff (inv_eq_one_div r ▸ inv_pos.mpr hpqr.pos')
      Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg
  have hr := hpqr.pos'.ne'
  simp only [← rpow_mul, mul_rpow]
  field_simp

Depends on / 依赖: Lr_rpow_le_Lp_mul_Lq_tsum, convert, hpqr.pos, inv_eq_one_div, inv_pos, inv_pos.mpr, mul_rpow, rpow_le_rpow_iff, rpow_mul
-/
theorem Lr_le_Lp_mul_Lq_tsum {f g : ι -> Real>=0} {p q r : Real} (hpqr : p.HolderTriple q r)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (∑' i, (f i * g i) ^ r) ^ (1 / r) <= (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  convert!
.mpr rpow_le_rpow_iff (inv_eq_one_div r ▸ inv_pos.mpr hpqr.pos')
      Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg
  have hr := hpqr.pos'.ne'
  simp only [← rpow_mul, mul_rpow]
  field_simp

/--
theorem `inner_le_Lp_mul_Lq_tsum` / 定理 `inner_le_Lp_mul_Lq_tsum`

English:
theorem inner_le_Lp_mul_Lq_tsum
  statement: {f g : ι -> Real>=0} {p q : Real} (hpq : p.HolderConjugate q)
  proof: (summable_and_inner_le_Lp_mul_Lq_tsum hpq hf hg).2

@[deprecated (since := "2026-02-12")] alias inner_le_Lp_mul_Lq_tsum' := inner_le_Lp_mul_Lq_tsum

中文:
定理 inner_le_Lp_mul_Lq_tsum
  结论: {f g : ι -> 实数>=0} {p q : 实数} (hpq : p.HolderConjugate q)
  证明: (summable_and_inner_le_Lp_mul_Lq_tsum hpq hf hg).2

@[deprecated (since := "2026-02-12")] alias inner_le_Lp_mul_Lq_tsum' := inner_le_Lp_mul_Lq_tsum

Depends on / 依赖: summable_and_inner_le_Lp_mul_Lq_tsum
-/
theorem inner_le_Lp_mul_Lq_tsum {f g : ι -> Real>=0} {p q : Real} (hpq : p.HolderConjugate q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    ∑' i, f i * g i <= (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) :=
  (summable_and_inner_le_Lp_mul_Lq_tsum hpq hf hg).2

@[deprecated (since := "2026-02-12")] alias inner_le_Lp_mul_Lq_tsum' := inner_le_Lp_mul_Lq_tsum

/--
theorem `inner_le_Lp_mul_Lq_hasSum` / 定理 `inner_le_Lp_mul_Lq_hasSum`

English:
theorem inner_le_Lp_mul_Lq_hasSum
  statement: {f g : ι -> Real>=0} {A B : Real>=0} {p q : Real}
  proof: by
  obtain ⟨H₁, H₂⟩ := summable_and_inner_le_Lp_mul_Lq_tsum hpq hf.summable hg.summable
  have hA : A = (∑' i : ι, f i ^ p) ^ (1 / p) := by rw [hf.tsum_eq, rpow_inv_rpow_self hpq.ne_zero]
  have hB : B = (∑' i : ι, g i ^ q) ^ (1 / q) := by
    rw [hg.tsum_eq]; rw [rpow_inv_rpow_self hpq.symm.ne_zer

中文:
定理 inner_le_Lp_mul_Lq_hasSum
  结论: {f g : ι -> 实数>=0} {A B : 实数>=0} {p q : 实数}
  证明: by
  obtain ⟨H₁, H₂⟩ := summable_and_inner_le_Lp_mul_Lq_tsum hpq hf.summable hg.summable
  have hA : A = (∑' i : ι, f i ^ p) ^ (1 / p) := by rw [hf.tsum_eq, rpow_inv_rpow_self hpq.ne_zero]
  have hB : B = (∑' i : ι, g i ^ q) ^ (1 / q) := by
    rw [hg.tsum_eq]; rw [rpow_inv_rpow_self hpq.symm.ne_zer

Depends on / 依赖: hasSum, hf.summable, hf.tsum_eq, hg.summable, hg.tsum_eq, hpq.ne_zero, hpq.symm.ne_zero, ne_zero, rpow_inv_rpow_self, rpow_self_rpow_inv, summable, summable_and_inner_le_Lp_mul_Lq_tsum, tsum_eq
-/
theorem inner_le_Lp_mul_Lq_hasSum {f g : ι -> Real>=0} {A B : Real>=0} {p q : Real}
    (hpq : p.HolderConjugate q) (hf : HasSum (fun i => f i ^ p) (A ^ p))
    (hg : HasSum (fun i => g i ^ q) (B ^ q)) : exists C, C <= A * B ∧ HasSum (fun i => f i * g i) C := by
  obtain ⟨H₁, H₂⟩ := summable_and_inner_le_Lp_mul_Lq_tsum hpq hf.summable hg.summable
  have hA : A = (∑' i : ι, f i ^ p) ^ (1 / p) := by rw [hf.tsum_eq, rpow_inv_rpow_self hpq.ne_zero]
  have hB : B = (∑' i : ι, g i ^ q) ^ (1 / q) := by
    rw [hg.tsum_eq]; rw [rpow_inv_rpow_self hpq.symm.ne_zero]
  refine ⟨∑' i, f i * g i, ?_, ?_⟩
  · simpa [hA, hB] using H₂
  · simpa only [rpow_self_rpow_inv hpq.ne_zero] using H₁.hasSum

/--
theorem `rpow_sum_le_const_mul_sum_rpow` / 定理 `rpow_sum_le_const_mul_sum_rpow`

English:
theorem rpow_sum_le_const_mul_sum_rpow
  given: (f : ι -> Real>=0) {p : Real} (hp : 1 <= p)
  proof: by
  rcases eq_or_lt_of_le hp with hp | hp
  · simp [← hp]
  let q : Real := p / (p - 1)
  have hpq : p.HolderConjugate q := .conjExponent hp
  have hp₁ : 1 / p * p = 1 := one_div_mul_cancel hpq.ne_zero
  have hq : 1 / q * p = p - 1 := by
    rw [← hpq.div_conj_eq_sub_one]
    ring
  simpa only [NNR

中文:
定理 rpow_sum_le_const_mul_sum_rpow
  条件: (f : ι -> 实数>=0) {p : 实数} (hp : 1 <= p)
  证明: by
  rcases eq_or_lt_of_le hp with hp | hp
  · simp [← hp]
  let q : Real := p / (p - 1)
  have hpq : p.HolderConjugate q := .conjExponent hp
  have hp₁ : 1 / p * p = 1 := one_div_mul_cancel hpq.ne_zero
  have hq : 1 / q * p = p - 1 := by
    rw [← hpq.div_conj_eq_sub_one]
    ring
  simpa only [NNR

Depends on / 依赖: HolderConjugate, NNReal, NNReal.mul_rpow, NNReal.rpow_le_rpow, NNReal.rpow_mul, Nat.smul_one_eq_cast, Pi.one_apply, conjExponent, div_conj_eq_sub_one, eq_or_lt_of_le, hpq.div_conj_eq_sub_one, hpq.ne_zero, hpq.nonneg, hpq.symm, inner_le_Lp_mul_Lq, mul_rpow, ne_zero, nonneg, one_apply, one_div_mul_cancel
-/
theorem rpow_sum_le_const_mul_sum_rpow (f : ι -> Real>=0) {p : Real} (hp : 1 <= p) :
    (∑ i in s, f i) ^ p <= (#s : Real>=0) ^ (p - 1) * ∑ i in s, f i ^ p := by
  rcases eq_or_lt_of_le hp with hp | hp
  · simp [← hp]
  let q : Real := p / (p - 1)
  have hpq : p.HolderConjugate q := .conjExponent hp
  have hp₁ : 1 / p * p = 1 := one_div_mul_cancel hpq.ne_zero
  have hq : 1 / q * p = p - 1 := by
    rw [← hpq.div_conj_eq_sub_one]
    ring
  simpa only [NNReal.mul_rpow, ← NNReal.rpow_mul, hp₁, hq, one_mul, one_rpow, rpow_one,
    Pi.one_apply, sum_const, Nat.smul_one_eq_cast] using
    NNReal.rpow_le_rpow (inner_le_Lp_mul_Lq s 1 f hpq.symm) hpq.nonneg

/--
theorem `isGreatest_Lp` / 定理 `isGreatest_Lp`

English:
theorem isGreatest_Lp
  given: (f : ι -> Real>=0) {p q : Real} (hpq : p.HolderConjugate q)
  proof: by
  constructor
  · use fun i => f i ^ p / f i / (∑ i in s, f i ^ p) ^ (1 / q)
    obtain hf | hf := eq_zero_or_pos (∑ i in s, f i ^ p)
    · simp [hf, hpq.ne_zero, hpq.symm.ne_zero]
    · have A : p + q - q != 0 := by simp [hpq.ne_zero]
      have B : forall y : Real>=0, y * y ^ p / y = y ^ p := b

中文:
定理 isGreatest_Lp
  条件: (f : ι -> 实数>=0) {p q : 实数} (hpq : p.HolderConjugate q)
  证明: by
  constructor
  · use fun i => f i ^ p / f i / (∑ i in s, f i ^ p) ^ (1 / q)
    obtain hf | hf := eq_zero_or_pos (∑ i in s, f i ^ p)
    · simp [hf, hpq.ne_zero, hpq.symm.ne_zero]
    · have A : p + q - q != 0 := by simp [hpq.ne_zero]
      have B : forall y : Real>=0, y * y ^ p / y = y ^ p := b

Depends on / 依赖: Set.mem_ofPred_eq, div_rpow, eq_zero_or_pos, hpq.mul_e, hpq.ne_zero, hpq.symm.ne_zero, mem_ofPred_eq, mul_div_cancel_left_of_imp, mul_e, ne_zero, one_mul, rpow_mul, rpow_one, sum_div
-/
theorem isGreatest_Lp (f : ι -> Real>=0) {p q : Real} (hpq : p.HolderConjugate q) :
    IsGreatest ((fun g : ι -> Real>=0 => ∑ i in s, f i * g i) '' { g | ∑ i in s, g i ^ q <= 1 })
      ((∑ i in s, f i ^ p) ^ (1 / p)) := by
  constructor
  · use fun i => f i ^ p / f i / (∑ i in s, f i ^ p) ^ (1 / q)
    obtain hf | hf := eq_zero_or_pos (∑ i in s, f i ^ p)
    · simp [hf, hpq.ne_zero, hpq.symm.ne_zero]
    · have A : p + q - q != 0 := by simp [hpq.ne_zero]
      have B : forall y : Real>=0, y * y ^ p / y = y ^ p := by
        refine fun y => mul_div_cancel_left_of_imp fun h => ?_
        simp [h, hpq.ne_zero]
      simp only [Set.mem_ofPred_eq, div_rpow, ← sum_div, ← rpow_mul,
        div_mul_cancel₀ _ hpq.symm.ne_zero, rpow_one, div_le_iff₀ hf, one_mul, hpq.mul_eq_add, ←
        rpow_sub' A, add_sub_cancel_right, le_refl, true_and, ← mul_div_assoc, B]
      rw [div_eq_iff]; rw [← rpow_add hf.ne']; rw [one_div]; rw [one_div]; rw [hpq.inv_add_inv_eq_one]; rw [rpow_one]
      simpa [hpq.symm.ne_zero] using hf.ne'
  · rintro _ ⟨g, hg, rfl⟩
    apply le_trans (inner_le_Lp_mul_Lq s f g hpq)
    simpa only [mul_one] using
      mul_le_mul_right (NNReal.rpow_le_one hg (le_of_lt hpq.symm.one_div_pos)) _

/--
theorem `Lp_add_le` / 定理 `Lp_add_le`

English:
theorem Lp_add_le
  given: (f g : ι -> Real>=0) {p : Real} (hp : 1 <= p)
  proof: by
  -- The result is trivial when `p = 1`, so we can assume `1 < p`.
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simp [Finset.sum_add_distrib]
  have hpq := Real.HolderConjugate.conjExponent hp
  have := isGreatest_Lp s (f + g) hpq
  simp only [Pi.add_apply, add_mul, sum_add_distrib] at this
  r

中文:
定理 Lp_add_le
  条件: (f g : ι -> 实数>=0) {p : 实数} (hp : 1 <= p)
  证明: by
  -- The result is trivial when `p = 1`, so we can assume `1 < p`.
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simp [Finset.sum_add_distrib]
  have hpq := Real.HolderConjugate.conjExponent hp
  have := isGreatest_Lp s (f + g) hpq
  simp only [Pi.add_apply, add_mul, sum_add_distrib] at this
  r
-/
theorem Lp_add_le (f g : ι -> Real>=0) {p : Real} (hp : 1 <= p) :
    (∑ i in s, (f i + g i) ^ p) ^ (1 / p) <=
      (∑ i in s, f i ^ p) ^ (1 / p) + (∑ i in s, g i ^ p) ^ (1 / p) := by
  -- The result is trivial when `p = 1`, so we can assume `1 < p`.
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simp [Finset.sum_add_distrib]
  have hpq := Real.HolderConjugate.conjExponent hp
  have := isGreatest_Lp s (f + g) hpq
  simp only [Pi.add_apply, add_mul, sum_add_distrib] at this
  rcases this.1 with ⟨φ, hφ, H⟩
  rw [← H]
  exact add_le_add ((isGreatest_Lp s f hpq).2 ⟨φ, hφ, rfl⟩) ((isGreatest_Lp s g hpq).2 ⟨φ, hφ, rfl⟩)

/--
theorem `Lp_add_le_tsum` / 定理 `Lp_add_le_tsum`

English:
theorem Lp_add_le_tsum
  statement: {f g : ι -> Real>=0} {p : Real} (hp : 1 <= p) (hf : Summable fun i => f i ^ p)
  proof: by
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have H₁ : forall s : Finset ι,
      (∑ i in s, (f i + g i) ^ p) <=
        ((∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)) ^ p := by
    intro s
    rw [one_div]; rw [← NNReal.rpow_inv_le_iff pos]; rw [← one_div]
    refine le_trans (

中文:
定理 Lp_add_le_tsum
  结论: {f g : ι -> 实数>=0} {p : 实数} (hp : 1 <= p) (hf : Summable fun i => f i ^ p)
  证明: by
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have H₁ : forall s : Finset ι,
      (∑ i in s, (f i + g i) ^ p) <=
        ((∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)) ^ p := by
    intro s
    rw [one_div]; rw [← NNReal.rpow_inv_le_iff pos]; rw [← one_div]
    refine le_trans (

Depends on / 依赖: BddAbove, Finset, Lp_add_le, NNReal, NNReal.rpow_inv_le_iff, Set.range, Summable, Summable.sum_le_tsum, exacts, le_trans, lt_of_lt_of_le, one_div, rpow_inv_le_iff, sum_le_tsum, zero_le, zero_lt_one
-/
theorem Lp_add_le_tsum {f g : ι -> Real>=0} {p : Real} (hp : 1 <= p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) :
    (Summable fun i => (f i + g i) ^ p) ∧
      (∑' i, (f i + g i) ^ p) ^ (1 / p) <=
        (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) := by
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have H₁ : forall s : Finset ι,
      (∑ i in s, (f i + g i) ^ p) <=
        ((∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)) ^ p := by
    intro s
    rw [one_div]; rw [← NNReal.rpow_inv_le_iff pos]; rw [← one_div]
    refine le_trans (Lp_add_le s f g hp) ?_
    gcongr <;>
      refine Summable.sum_le_tsum _ (fun _ _ => zero_le) ?_
    exacts [hf, hg]
  have bdd : BddAbove (Set.range fun s => ∑ i in s, (f i + g i) ^ p) := by
    refine ⟨((∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)) ^ p, ?_⟩
    rintro a ⟨s, rfl⟩
    exact H₁ s
  have H₂ : Summable _ := (hasSum_of_isLUB _ (isLUB_ciSup bdd)).summable
  refine ⟨H₂, ?_⟩
  rw [one_div]; rw [NNReal.rpow_inv_le_iff pos]; rw [← one_div]
  exact H₂.tsum_le_of_sum_le H₁

/--
theorem `summable_Lp_add` / 定理 `summable_Lp_add`

English:
theorem summable_Lp_add
  statement: {f g : ι -> Real>=0} {p : Real} (hp : 1 <= p) (hf : Summable fun i => f i ^ p)
  proof: (Lp_add_le_tsum hp hf hg).1

中文:
定理 summable_Lp_add
  结论: {f g : ι -> 实数>=0} {p : 实数} (hp : 1 <= p) (hf : Summable fun i => f i ^ p)
  证明: (Lp_add_le_tsum hp hf hg).1

Depends on / 依赖: Lp_add_le_tsum
-/
theorem summable_Lp_add {f g : ι -> Real>=0} {p : Real} (hp : 1 <= p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) : Summable fun i => (f i + g i) ^ p :=
  (Lp_add_le_tsum hp hf hg).1

/--
theorem `Lp_add_le_tsum'` / 定理 `Lp_add_le_tsum'`

English:
theorem Lp_add_le_tsum'
  statement: {f g : ι -> Real>=0} {p : Real} (hp : 1 <= p) (hf : Summable fun i => f i ^ p)
  proof: (Lp_add_le_tsum hp hf hg).2

中文:
定理 Lp_add_le_tsum'
  结论: {f g : ι -> 实数>=0} {p : 实数} (hp : 1 <= p) (hf : Summable fun i => f i ^ p)
  证明: (Lp_add_le_tsum hp hf hg).2

Depends on / 依赖: Lp_add_le_tsum
-/
theorem Lp_add_le_tsum' {f g : ι -> Real>=0} {p : Real} (hp : 1 <= p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) <= (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) :=
  (Lp_add_le_tsum hp hf hg).2

/--
theorem `Lp_add_le_hasSum` / 定理 `Lp_add_le_hasSum`

English:
theorem Lp_add_le_hasSum
  statement: {f g : ι -> Real>=0} {A B : Real>=0} {p : Real} (hp : 1 <= p)
  proof: by
  have hp' : p != 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  obtain ⟨H₁, H₂⟩ := Lp_add_le_tsum hp hf.summable hg.summable
  have hA : A = (∑' i : ι, f i ^ p) ^ (1 / p) := by rw [hf.tsum_eq, rpow_inv_rpow_self hp']
  have hB : B = (∑' i : ι, g i ^ p) ^ (1 / p) := by rw [hg.tsum_eq, rpow_inv_rpow_s

中文:
定理 Lp_add_le_hasSum
  结论: {f g : ι -> 实数>=0} {A B : 实数>=0} {p : 实数} (hp : 1 <= p)
  证明: by
  have hp' : p != 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  obtain ⟨H₁, H₂⟩ := Lp_add_le_tsum hp hf.summable hg.summable
  have hA : A = (∑' i : ι, f i ^ p) ^ (1 / p) := by rw [hf.tsum_eq, rpow_inv_rpow_self hp']
  have hB : B = (∑' i : ι, g i ^ p) ^ (1 / p) := by rw [hg.tsum_eq, rpow_inv_rpow_s

Depends on / 依赖: Lp_add_le_tsum, hasSum, hf.summable, hf.tsum_eq, hg.summable, hg.tsum_eq, lt_of_lt_of_le, rpow_inv_rpow_self, rpow_self_rpow_inv, summable, tsum_eq, zero_lt_one
-/
theorem Lp_add_le_hasSum {f g : ι -> Real>=0} {A B : Real>=0} {p : Real} (hp : 1 <= p)
    (hf : HasSum (fun i => f i ^ p) (A ^ p)) (hg : HasSum (fun i => g i ^ p) (B ^ p)) :
    exists C, C <= A + B ∧ HasSum (fun i => (f i + g i) ^ p) (C ^ p) := by
  have hp' : p != 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  obtain ⟨H₁, H₂⟩ := Lp_add_le_tsum hp hf.summable hg.summable
  have hA : A = (∑' i : ι, f i ^ p) ^ (1 / p) := by rw [hf.tsum_eq, rpow_inv_rpow_self hp']
  have hB : B = (∑' i : ι, g i ^ p) ^ (1 / p) := by rw [hg.tsum_eq, rpow_inv_rpow_self hp']
  refine ⟨(∑' i, (f i + g i) ^ p) ^ (1 / p), ?_, ?_⟩
  · simpa [hA, hB] using H₂
  · simpa only [rpow_self_rpow_inv hp'] using H₁.hasSum

end NNReal

namespace Real

variable (f g : ι -> Real) {p q r : Real}

/--
theorem `Lr_rpow_le_Lp_mul_Lq` / 定理 `Lr_rpow_le_Lp_mul_Lq`

English:
theorem Lr_rpow_le_Lp_mul_Lq
  given: (hpqr : HolderTriple p q r)
  proof: by
simpa using! NNReal.coe_le_coe.2 NNReal.Lr_rpow_le_Lp_mul_Lq s (fun i => ⟨_, abs_nonneg (f i)⟩)
    (fun i => ⟨_, abs_nonneg (g i)⟩) hpqr

中文:
定理 Lr_rpow_le_Lp_mul_Lq
  条件: (hpqr : HolderTriple p q r)
  证明: by
simpa using! NNReal.coe_le_coe.2 NNReal.Lr_rpow_le_Lp_mul_Lq s (fun i => ⟨_, abs_nonneg (f i)⟩)
    (fun i => ⟨_, abs_nonneg (g i)⟩) hpqr

Depends on / 依赖: Lr_rpow_le_Lp_mul_Lq, NNReal, NNReal.Lr_rpow_le_Lp_mul_Lq, NNReal.coe_le_coe, abs_nonneg, coe_le_coe
-/
theorem Lr_rpow_le_Lp_mul_Lq (hpqr : HolderTriple p q r) :
    ∑ i in s, |f i * g i| ^ r <= (∑ i in s, |f i| ^ p) ^ (r / p) * (∑ i in s, |g i| ^ q) ^ (r / q) := by
simpa using! NNReal.coe_le_coe.2 NNReal.Lr_rpow_le_Lp_mul_Lq s (fun i => ⟨_, abs_nonneg (f i)⟩)
    (fun i => ⟨_, abs_nonneg (g i)⟩) hpqr

/--
theorem `inner_le_Lp_mul_Lq` / 定理 `inner_le_Lp_mul_Lq`

English:
theorem inner_le_Lp_mul_Lq
  given: (hpq : HolderConjugate p q)
  proof: by
  refine le_trans (sum_le_sum fun i _ => ?_) (by simpa using Lr_rpow_le_Lp_mul_Lq s f g hpq)
  simp only [← abs_mul, le_abs_self]

中文:
定理 inner_le_Lp_mul_Lq
  条件: (hpq : HolderConjugate p q)
  证明: by
  refine le_trans (sum_le_sum fun i _ => ?_) (by simpa using Lr_rpow_le_Lp_mul_Lq s f g hpq)
  simp only [← abs_mul, le_abs_self]

Depends on / 依赖: Lr_rpow_le_Lp_mul_Lq, abs_mul, le_abs_self, le_trans, sum_le_sum
-/
theorem inner_le_Lp_mul_Lq (hpq : HolderConjugate p q) :
    ∑ i in s, f i * g i <= (∑ i in s, |f i| ^ p) ^ (1 / p) * (∑ i in s, |g i| ^ q) ^ (1 / q) := by
  refine le_trans (sum_le_sum fun i _ => ?_) (by simpa using Lr_rpow_le_Lp_mul_Lq s f g hpq)
  simp only [← abs_mul, le_abs_self]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `rpow_sum_le_const_mul_sum_rpow` / 定理 `rpow_sum_le_const_mul_sum_rpow`

English:
theorem rpow_sum_le_const_mul_sum_rpow
  given: (hp : 1 <= p)
  proof: by
  have :=
    NNReal.coe_le_coe.2
      (NNReal.rpow_sum_le_const_mul_sum_rpow s (fun i => ⟨_, abs_nonneg (f i)⟩) hp)
  push_cast at this
  exact this

中文:
定理 rpow_sum_le_const_mul_sum_rpow
  条件: (hp : 1 <= p)
  证明: by
  have :=
    NNReal.coe_le_coe.2
      (NNReal.rpow_sum_le_const_mul_sum_rpow s (fun i => ⟨_, abs_nonneg (f i)⟩) hp)
  push_cast at this
  exact this

Depends on / 依赖: NNReal, NNReal.coe_le_coe, NNReal.rpow_sum_le_const_mul_sum_rpow, abs_nonneg, coe_le_coe, rpow_sum_le_const_mul_sum_rpow
-/
theorem rpow_sum_le_const_mul_sum_rpow (hp : 1 <= p) :
    (∑ i in s, |f i|) ^ p <= (#s : Real) ^ (p - 1) * ∑ i in s, |f i| ^ p := by
  have :=
    NNReal.coe_le_coe.2
      (NNReal.rpow_sum_le_const_mul_sum_rpow s (fun i => ⟨_, abs_nonneg (f i)⟩) hp)
  push_cast at this
  exact this

-- for some reason `exact_mod_cast` can't replace this argument
/--
theorem `Lp_add_le` / 定理 `Lp_add_le`

English:
theorem Lp_add_le
  given: (hp : 1 <= p)
  proof: by
  have := NNReal.coe_le_coe.2
    (NNReal.Lp_add_le s (fun i => .mk _ (abs_nonneg (f i))) (fun i => .mk _ (abs_nonneg (g i))) hp)
  push_cast at this
  refine le_trans (rpow_le_rpow ?_ (sum_le_sum fun i _ => ?_) ?_) this <;>
    simp [sum_nonneg, rpow_nonneg, abs_nonneg, le_trans zero_le_one hp, 

中文:
定理 Lp_add_le
  条件: (hp : 1 <= p)
  证明: by
  have := NNReal.coe_le_coe.2
    (NNReal.Lp_add_le s (fun i => .mk _ (abs_nonneg (f i))) (fun i => .mk _ (abs_nonneg (g i))) hp)
  push_cast at this
  refine le_trans (rpow_le_rpow ?_ (sum_le_sum fun i _ => ?_) ?_) this <;>
    simp [sum_nonneg, rpow_nonneg, abs_nonneg, le_trans zero_le_one hp, 

Depends on / 依赖: Lp_add_le, NNReal, NNReal.Lp_add_le, NNReal.coe_le_coe, abs_add_le, abs_nonneg, coe_le_coe, le_trans, rpow_le_rpow, rpow_nonneg, sum_le_sum, sum_nonneg, zero_le_one
-/
theorem Lp_add_le (hp : 1 <= p) :
    (∑ i in s, |f i + g i| ^ p) ^ (1 / p) <=
      (∑ i in s, |f i| ^ p) ^ (1 / p) + (∑ i in s, |g i| ^ p) ^ (1 / p) := by
  have := NNReal.coe_le_coe.2
    (NNReal.Lp_add_le s (fun i => .mk _ (abs_nonneg (f i))) (fun i => .mk _ (abs_nonneg (g i))) hp)
  push_cast at this
  refine le_trans (rpow_le_rpow ?_ (sum_le_sum fun i _ => ?_) ?_) this <;>
    simp [sum_nonneg, rpow_nonneg, abs_nonneg, le_trans zero_le_one hp, abs_add_le,
      rpow_le_rpow]

variable {f g}

/--
theorem `inner_le_Lp_mul_Lq_of_nonneg` / 定理 `inner_le_Lp_mul_Lq_of_nonneg`

English:
theorem inner_le_Lp_mul_Lq_of_nonneg
  statement: (hpq : HolderConjugate p q) (hf : forall i in s, 0 <= f i)
  proof: by
  convert! inner_le_Lp_mul_Lq s f g hpq using 3 <;> apply sum_congr rfl <;> intro i hi <;>
    simp only [abs_of_nonneg, hf i hi, hg i hi]

中文:
定理 inner_le_Lp_mul_Lq_of_nonneg
  结论: (hpq : HolderConjugate p q) (hf : 对任意 i in s, 0 <= f i)
  证明: by
  convert! inner_le_Lp_mul_Lq s f g hpq using 3 <;> apply sum_congr rfl <;> intro i hi <;>
    simp only [abs_of_nonneg, hf i hi, hg i hi]

Depends on / 依赖: abs_of_nonneg, convert, inner_le_Lp_mul_Lq, sum_congr
-/
theorem inner_le_Lp_mul_Lq_of_nonneg (hpq : HolderConjugate p q) (hf : forall i in s, 0 <= f i)
    (hg : forall i in s, 0 <= g i) :
    ∑ i in s, f i * g i <= (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) := by
  convert! inner_le_Lp_mul_Lq s f g hpq using 3 <;> apply sum_congr rfl <;> intro i hi <;>
    simp only [abs_of_nonneg, hf i hi, hg i hi]

/--
theorem `Lr_rpow_le_Lp_mul_Lq_of_nonneg` / 定理 `Lr_rpow_le_Lp_mul_Lq_of_nonneg`

English:
theorem Lr_rpow_le_Lp_mul_Lq_of_nonneg
  statement: {ι : Type*} (s : Finset ι) {f g : ι -> Real} {p q r : Real}
  proof: by
  convert Lr_rpow_le_Lp_mul_Lq s f g hpqr with i hi
  · rw [abs_of_nonneg (mul_nonneg (hf i hi) (hg i hi))]
  all_goals
    exact Eq.symm (abs_of_nonneg (by grind))

中文:
定理 Lr_rpow_le_Lp_mul_Lq_of_nonneg
  结论: {ι : 类型} (s : Finset ι) {f g : ι -> 实数} {p q r : 实数}
  证明: by
  convert Lr_rpow_le_Lp_mul_Lq s f g hpqr with i hi
  · rw [abs_of_nonneg (mul_nonneg (hf i hi) (hg i hi))]
  all_goals
    exact Eq.symm (abs_of_nonneg (by grind))

Depends on / 依赖: Eq.symm, Lr_rpow_le_Lp_mul_Lq, abs_of_nonneg, all_goals, convert, mul_nonneg
-/
theorem Lr_rpow_le_Lp_mul_Lq_of_nonneg {ι : Type*} (s : Finset ι) {f g : ι -> Real} {p q r : Real}
    (hpqr : p.HolderTriple q r) (hf : forall i in s, 0 <= f i) (hg : forall i in s, 0 <= g i) :
    ∑ i in s, (f i * g i) ^ r <= (∑ i in s, f i ^ p) ^ (r / p) * (∑ i in s, g i ^ q) ^ (r / q) := by
  convert Lr_rpow_le_Lp_mul_Lq s f g hpqr with i hi
  · rw [abs_of_nonneg (mul_nonneg (hf i hi) (hg i hi))]
  all_goals
    exact Eq.symm (abs_of_nonneg (by grind))

/--
lemma `inner_le_weight_mul_Lp_of_nonneg` / 引理 `inner_le_weight_mul_Lp_of_nonneg`

English:
lemma inner_le_weight_mul_Lp_of_nonneg
  statement: (s : Finset ι) {p : Real} (hp : 1 <= p) (w f : ι -> Real)
  proof: by
  lift w to ι -> Real>=0 using hw
  lift f to ι -> Real>=0 using hf
  beta_reduce at *
  norm_cast at *
  exact NNReal.inner_le_weight_mul_Lp _ hp _ _

中文:
引理 inner_le_weight_mul_Lp_of_nonneg
  结论: (s : Finset ι) {p : 实数} (hp : 1 <= p) (w f : ι -> 实数)
  证明: by
  lift w to ι -> Real>=0 using hw
  lift f to ι -> Real>=0 using hf
  beta_reduce at *
  norm_cast at *
  exact NNReal.inner_le_weight_mul_Lp _ hp _ _

Depends on / 依赖: NNReal, NNReal.inner_le_weight_mul_Lp, beta_reduce, inner_le_weight_mul_Lp
-/
lemma inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : Real} (hp : 1 <= p) (w f : ι -> Real)
    (hw : forall i, 0 <= w i) (hf : forall i, 0 <= f i) :
    ∑ i in s, w i * f i <= (∑ i in s, w i) ^ (1 - p⁻¹) * (∑ i in s, w i * f i ^ p) ^ p⁻¹ := by
  lift w to ι -> Real>=0 using hw
  lift f to ι -> Real>=0 using hf
  beta_reduce at *
  norm_cast at *
  exact NNReal.inner_le_weight_mul_Lp _ hp _ _

/--
lemma `compact_inner_le_weight_mul_Lp_of_nonneg` / 引理 `compact_inner_le_weight_mul_Lp_of_nonneg`

English:
lemma compact_inner_le_weight_mul_Lp_of_nonneg
  statement: (s : Finset ι) {p : Real} (hp : 1 <= p) {w f : ι -> Real}
  proof: by
  simp_rw [expect_eq_sum_div_card]
  rw [div_rpow]; rw [div_rpow]; rw [div_mul_div_comm]; rw [← rpow_add']; rw [sub_add_cancel]; rw [rpow_one]
  · gcongr
    exact inner_le_weight_mul_Lp_of_nonneg s hp _ _ hw hf
  any_goals simp
  · exact sum_nonneg fun i _ => by have := hw i; have := hf i; posit

中文:
引理 compact_inner_le_weight_mul_Lp_of_nonneg
  结论: (s : Finset ι) {p : 实数} (hp : 1 <= p) {w f : ι -> 实数}
  证明: by
  simp_rw [expect_eq_sum_div_card]
  rw [div_rpow]; rw [div_rpow]; rw [div_mul_div_comm]; rw [← rpow_add']; rw [sub_add_cancel]; rw [rpow_one]
  · gcongr
    exact inner_le_weight_mul_Lp_of_nonneg s hp _ _ hw hf
  any_goals simp
  · exact sum_nonneg fun i _ => by have := hw i; have := hf i; posit

Depends on / 依赖: any_goals, div_mul_div_comm, div_rpow, expect_eq_sum_div_card, inner_le_weight_mul_Lp_of_nonneg, rpow_add, rpow_one, simp_rw, sub_add_cancel, sum_nonneg
-/
lemma compact_inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : Real} (hp : 1 <= p) {w f : ι -> Real}
    (hw : forall i, 0 <= w i) (hf : forall i, 0 <= f i) :
    𝔼 i in s, w i * f i <= (𝔼 i in s, w i) ^ (1 - p⁻¹) * (𝔼 i in s, w i * f i ^ p) ^ p⁻¹ := by
  simp_rw [expect_eq_sum_div_card]
  rw [div_rpow]; rw [div_rpow]; rw [div_mul_div_comm]; rw [← rpow_add']; rw [sub_add_cancel]; rw [rpow_one]
  · gcongr
    exact inner_le_weight_mul_Lp_of_nonneg s hp _ _ hw hf
  any_goals simp
  · exact sum_nonneg fun i _ => by have := hw i; have := hf i; positivity
  · exact sum_nonneg fun i _ => by have := hw i; positivity

/--
theorem `summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg` / 定理 `summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg`

English:
theorem summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg
  statement: (hpqr : p.HolderTriple q r)
  proof: by
  lift f to ι -> Real>=0 using hf
  lift g to ι -> Real>=0 using hg
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast at *
  exact NNReal.summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf_sum hg_sum

中文:
定理 summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg
  结论: (hpqr : p.HolderTriple q r)
  证明: by
  lift f to ι -> Real>=0 using hf
  lift g to ι -> Real>=0 using hg
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast at *
  exact NNReal.summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf_sum hg_sum
-/
theorem summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r)
    (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i) (hf_sum : Summable fun i => f i ^ p)
    (hg_sum : Summable fun i => g i ^ q) :
    (Summable fun i => (f i * g i) ^ r) ∧
      ∑' i, (f i * g i) ^ r <= (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) := by
  lift f to ι -> Real>=0 using hf
  lift g to ι -> Real>=0 using hg
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast at *
  exact NNReal.summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf_sum hg_sum

/--
theorem `summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg` / 定理 `summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg`

English:
theorem summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
  statement: (hpq : p.HolderConjugate q)
  proof: by
  simpa using summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum

中文:
定理 summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
  结论: (hpq : p.HolderConjugate q)
  证明: by
  simpa using summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum

Depends on / 依赖: hf_sum, hg_sum, summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg
-/
theorem summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg (hpq : p.HolderConjugate q)
    (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i) (hf_sum : Summable fun i => f i ^ p)
    (hg_sum : Summable fun i => g i ^ q) :
    (Summable fun i => f i * g i) ∧
      ∑' i, f i * g i <= (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  simpa using summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum

/--
theorem `summable_Lr_of_Lp_Lq_of_nonneg` / 定理 `summable_Lr_of_Lp_Lq_of_nonneg`

English:
theorem summable_Lr_of_Lp_Lq_of_nonneg
  statement: (hpqr : p.HolderTriple q r) (hf : forall i, 0 <= f i)
  proof: (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpqr hf hg hf_sum hg_sum).1

中文:
定理 summable_Lr_of_Lp_Lq_of_nonneg
  结论: (hpqr : p.HolderTriple q r) (hf : 对任意 i, 0 <= f i)
  证明: (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpqr hf hg hf_sum hg_sum).1

Depends on / 依赖: hf_sum, hg_sum, summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg
-/
theorem summable_Lr_of_Lp_Lq_of_nonneg (hpqr : p.HolderTriple q r) (hf : forall i, 0 <= f i)
    (hg : forall i, 0 <= g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    Summable fun i => (f i * g i) ^ r :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpqr hf hg hf_sum hg_sum).1

/--
theorem `summable_mul_of_Lp_Lq_of_nonneg` / 定理 `summable_mul_of_Lp_Lq_of_nonneg`

English:
theorem summable_mul_of_Lp_Lq_of_nonneg
  statement: (hpq : p.HolderConjugate q) (hf : forall i, 0 <= f i)
  proof: (summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).1

中文:
定理 summable_mul_of_Lp_Lq_of_nonneg
  结论: (hpq : p.HolderConjugate q) (hf : 对任意 i, 0 <= f i)
  证明: (summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).1

Depends on / 依赖: hf_sum, hg_sum, summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
-/
theorem summable_mul_of_Lp_Lq_of_nonneg (hpq : p.HolderConjugate q) (hf : forall i, 0 <= f i)
    (hg : forall i, 0 <= g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    Summable fun i => f i * g i :=
  (summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).1

/--
theorem `Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg` / 定理 `Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg`

English:
theorem Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg
  statement: (hpqr : p.HolderTriple q r) (hf : forall i, 0 <= f i)
  proof: (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpqr hf hg hf_sum hg_sum).2

中文:
定理 Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg
  结论: (hpqr : p.HolderTriple q r) (hf : 对任意 i, 0 <= f i)
  证明: (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpqr hf hg hf_sum hg_sum).2

Depends on / 依赖: hf_sum, hg_sum, summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg
-/
theorem Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r) (hf : forall i, 0 <= f i)
    (hg : forall i, 0 <= g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    ∑' i, (f i * g i) ^ r <= (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpqr hf hg hf_sum hg_sum).2

/--
theorem `Lr_le_Lp_mul_Lq_tsum_of_nonneg` / 定理 `Lr_le_Lp_mul_Lq_tsum_of_nonneg`

English:
theorem Lr_le_Lp_mul_Lq_tsum_of_nonneg
  statement: (hpqr : p.HolderTriple q r) (hf : forall i, 0 <= f i)
  proof: by
  -- It's really inconvenient that `positivity` can't use `∀` hypotheses.
  have hf' : 0 <= ∑' i, f i ^ p := tsum_nonneg fun i => rpow_nonneg (hf i) p
  have hg' : 0 <= ∑' i, g i ^ q := tsum_nonneg fun i => rpow_nonneg (hg i) q
  have hr := hpqr.pos'
  convert
    rpow_le_rpow_iff (tsum_nonneg fu

中文:
定理 Lr_le_Lp_mul_Lq_tsum_of_nonneg
  结论: (hpqr : p.HolderTriple q r) (hf : 对任意 i, 0 <= f i)
  证明: by
  -- It's really inconvenient that `positivity` can't use `∀` hypotheses.
  have hf' : 0 <= ∑' i, f i ^ p := tsum_nonneg fun i => rpow_nonneg (hf i) p
  have hg' : 0 <= ∑' i, g i ^ q := tsum_nonneg fun i => rpow_nonneg (hg i) q
  have hr := hpqr.pos'
  convert
    rpow_le_rpow_iff (tsum_nonneg fu
-/
theorem Lr_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r) (hf : forall i, 0 <= f i)
    (hg : forall i, 0 <= g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    (∑' i, (f i * g i) ^ r) ^ (1 / r) <= (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  -- It's really inconvenient that `positivity` can't use `∀` hypotheses.
  have hf' : 0 <= ∑' i, f i ^ p := tsum_nonneg fun i => rpow_nonneg (hf i) p
  have hg' : 0 <= ∑' i, g i ^ q := tsum_nonneg fun i => rpow_nonneg (hg i) q
  have hr := hpqr.pos'
  convert
    rpow_le_rpow_iff (tsum_nonneg fun i => by positivity [hf i, hg i]) (by positivity)
.mpr (inv_eq_one_div r ▸ inv_pos.mpr hr)
      Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpqr hf hg hf_sum hg_sum
  rw [mul_rpow (rpow_nonneg hf' _) (rpow_nonneg hg' _)]; rw [← Real.rpow_mul hg']; rw [← Real.rpow_mul hf']
  field_simp

/--
theorem `inner_le_Lp_mul_Lq_tsum_of_nonneg` / 定理 `inner_le_Lp_mul_Lq_tsum_of_nonneg`

English:
theorem inner_le_Lp_mul_Lq_tsum_of_nonneg
  statement: (hpq : p.HolderConjugate q) (hf : forall i, 0 <= f i)
  proof: (summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).2

@[deprecated (since := "2026-02-12")]
alias inner_le_Lp_mul_Lq_of_nonneg' := inner_le_Lp_mul_Lq_of_nonneg

中文:
定理 inner_le_Lp_mul_Lq_tsum_of_nonneg
  结论: (hpq : p.HolderConjugate q) (hf : 对任意 i, 0 <= f i)
  证明: (summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).2

@[deprecated (since := "2026-02-12")]
alias inner_le_Lp_mul_Lq_of_nonneg' := inner_le_Lp_mul_Lq_of_nonneg

Depends on / 依赖: hf_sum, hg_sum, summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
-/
theorem inner_le_Lp_mul_Lq_tsum_of_nonneg (hpq : p.HolderConjugate q) (hf : forall i, 0 <= f i)
    (hg : forall i, 0 <= g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    ∑' i, f i * g i <= (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) :=
  (summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).2

@[deprecated (since := "2026-02-12")]
alias inner_le_Lp_mul_Lq_of_nonneg' := inner_le_Lp_mul_Lq_of_nonneg

/--
theorem `inner_le_Lp_mul_Lq_hasSum_of_nonneg` / 定理 `inner_le_Lp_mul_Lq_hasSum_of_nonneg`

English:
theorem inner_le_Lp_mul_Lq_hasSum_of_nonneg
  statement: (hpq : p.HolderConjugate q) {A B : Real} (hA : 0 <= A)
  proof: by
  lift f to ι -> Real>=0 using hf
  lift g to ι -> Real>=0 using hg
  lift A to Real>=0 using hA
  lift B to Real>=0 using hB
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast at hf_sum hg_sum
  obtain ⟨C, hC, H⟩ :

中文:
定理 inner_le_Lp_mul_Lq_hasSum_of_nonneg
  结论: (hpq : p.HolderConjugate q) {A B : 实数} (hA : 0 <= A)
  证明: by
  lift f to ι -> Real>=0 using hf
  lift g to ι -> Real>=0 using hg
  lift A to Real>=0 using hA
  lift B to Real>=0 using hB
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast at hf_sum hg_sum
  obtain ⟨C, hC, H⟩ :
-/
theorem inner_le_Lp_mul_Lq_hasSum_of_nonneg (hpq : p.HolderConjugate q) {A B : Real} (hA : 0 <= A)
    (hB : 0 <= B) (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i)
    (hf_sum : HasSum (fun i => f i ^ p) (A ^ p)) (hg_sum : HasSum (fun i => g i ^ q) (B ^ q)) :
    exists C : Real, 0 <= C ∧ C <= A * B ∧ HasSum (fun i => f i * g i) C := by
  lift f to ι -> Real>=0 using hf
  lift g to ι -> Real>=0 using hg
  lift A to Real>=0 using hA
  lift B to Real>=0 using hB
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast at hf_sum hg_sum
  obtain ⟨C, hC, H⟩ := NNReal.inner_le_Lp_mul_Lq_hasSum hpq hf_sum hg_sum
  refine ⟨C, C.prop, hC, ?_⟩
  norm_cast

/--
theorem `rpow_sum_le_const_mul_sum_rpow_of_nonneg` / 定理 `rpow_sum_le_const_mul_sum_rpow_of_nonneg`

English:
theorem rpow_sum_le_const_mul_sum_rpow_of_nonneg
  given: (hp : 1 <= p) (hf : forall i in s, 0 <= f i)
  proof: by
  convert! rpow_sum_le_const_mul_sum_rpow s f hp using 2 <;> apply sum_congr rfl <;> intro i hi <;>
    simp only [abs_of_nonneg, hf i hi]

中文:
定理 rpow_sum_le_const_mul_sum_rpow_of_nonneg
  条件: (hp : 1 <= p) (hf : 对任意 i in s, 0 <= f i)
  证明: by
  convert! rpow_sum_le_const_mul_sum_rpow s f hp using 2 <;> apply sum_congr rfl <;> intro i hi <;>
    simp only [abs_of_nonneg, hf i hi]

Depends on / 依赖: abs_of_nonneg, convert, rpow_sum_le_const_mul_sum_rpow, sum_congr
-/
theorem rpow_sum_le_const_mul_sum_rpow_of_nonneg (hp : 1 <= p) (hf : forall i in s, 0 <= f i) :
    (∑ i in s, f i) ^ p <= (#s : Real) ^ (p - 1) * ∑ i in s, f i ^ p := by
  convert! rpow_sum_le_const_mul_sum_rpow s f hp using 2 <;> apply sum_congr rfl <;> intro i hi <;>
    simp only [abs_of_nonneg, hf i hi]

/--
theorem `Lp_add_le_of_nonneg` / 定理 `Lp_add_le_of_nonneg`

English:
theorem Lp_add_le_of_nonneg
  given: (hp : 1 <= p) (hf : forall i in s, 0 <= f i) (hg : forall i in s, 0 <= g i)
  proof: by
  convert! Lp_add_le s f g hp using 2 <;> [skip; congr 1; congr 1] <;> apply sum_congr rfl <;>
      intro i hi <;>
    simp only [abs_of_nonneg, hf i hi, hg i hi, add_nonneg]

中文:
定理 Lp_add_le_of_nonneg
  条件: (hp : 1 <= p) (hf : 对任意 i in s, 0 <= f i) (hg : 对任意 i in s, 0 <= g i)
  证明: by
  convert! Lp_add_le s f g hp using 2 <;> [skip; congr 1; congr 1] <;> apply sum_congr rfl <;>
      intro i hi <;>
    simp only [abs_of_nonneg, hf i hi, hg i hi, add_nonneg]

Depends on / 依赖: Lp_add_le, abs_of_nonneg, add_nonneg, convert, sum_congr
-/
theorem Lp_add_le_of_nonneg (hp : 1 <= p) (hf : forall i in s, 0 <= f i) (hg : forall i in s, 0 <= g i) :
    (∑ i in s, (f i + g i) ^ p) ^ (1 / p) <=
      (∑ i in s, f i ^ p) ^ (1 / p) + (∑ i in s, g i ^ p) ^ (1 / p) := by
  convert! Lp_add_le s f g hp using 2 <;> [skip; congr 1; congr 1] <;> apply sum_congr rfl <;>
      intro i hi <;>
    simp only [abs_of_nonneg, hf i hi, hg i hi, add_nonneg]

/--
theorem `Lp_add_le_tsum_of_nonneg` / 定理 `Lp_add_le_tsum_of_nonneg`

English:
theorem Lp_add_le_tsum_of_nonneg
  statement: (hp : 1 <= p) (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i)
  proof: by
  lift f to ι -> Real>=0 using hf
  lift g to ι -> Real>=0 using hg
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast0 at *
  exact NNReal.Lp_add_le_tsum hp hf_sum hg_sum

中文:
定理 Lp_add_le_tsum_of_nonneg
  结论: (hp : 1 <= p) (hf : 对任意 i, 0 <= f i) (hg : 对任意 i, 0 <= g i)
  证明: by
  lift f to ι -> Real>=0 using hf
  lift g to ι -> Real>=0 using hg
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast0 at *
  exact NNReal.Lp_add_le_tsum hp hf_sum hg_sum
-/
theorem Lp_add_le_tsum_of_nonneg (hp : 1 <= p) (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    (Summable fun i => (f i + g i) ^ p) ∧
      (∑' i, (f i + g i) ^ p) ^ (1 / p) <=
        (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) := by
  lift f to ι -> Real>=0 using hf
  lift g to ι -> Real>=0 using hg
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast0 at *
  exact NNReal.Lp_add_le_tsum hp hf_sum hg_sum

/--
theorem `summable_Lp_add_of_nonneg` / 定理 `summable_Lp_add_of_nonneg`

English:
theorem summable_Lp_add_of_nonneg
  statement: (hp : 1 <= p) (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i)
  proof: (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).1

中文:
定理 summable_Lp_add_of_nonneg
  结论: (hp : 1 <= p) (hf : 对任意 i, 0 <= f i) (hg : 对任意 i, 0 <= g i)
  证明: (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).1

Depends on / 依赖: Lp_add_le_tsum_of_nonneg, hf_sum, hg_sum
-/
theorem summable_Lp_add_of_nonneg (hp : 1 <= p) (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    Summable fun i => (f i + g i) ^ p :=
  (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).1

/--
theorem `Lp_add_le_tsum_of_nonneg'` / 定理 `Lp_add_le_tsum_of_nonneg'`

English:
theorem Lp_add_le_tsum_of_nonneg'
  statement: (hp : 1 <= p) (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i)
  proof: (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).2

中文:
定理 Lp_add_le_tsum_of_nonneg'
  结论: (hp : 1 <= p) (hf : 对任意 i, 0 <= f i) (hg : 对任意 i, 0 <= g i)
  证明: (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).2

Depends on / 依赖: Lp_add_le_tsum_of_nonneg, hf_sum, hg_sum
-/
theorem Lp_add_le_tsum_of_nonneg' (hp : 1 <= p) (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) <= (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) :=
  (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).2

/--
theorem `Lp_add_le_hasSum_of_nonneg` / 定理 `Lp_add_le_hasSum_of_nonneg`

English:
theorem Lp_add_le_hasSum_of_nonneg
  statement: (hp : 1 <= p) (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i) {A B : Real}
  proof: by
  lift f to ι -> Real>=0 using hf
  lift g to ι -> Real>=0 using hg
  lift A to Real>=0 using hA
  lift B to Real>=0 using hB
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at hfA hgB
  norm_cast at hfA hgB
  obtain ⟨C, hC₁, hC₂

中文:
定理 Lp_add_le_hasSum_of_nonneg
  结论: (hp : 1 <= p) (hf : 对任意 i, 0 <= f i) (hg : 对任意 i, 0 <= g i) {A B : 实数}
  证明: by
  lift f to ι -> Real>=0 using hf
  lift g to ι -> Real>=0 using hg
  lift A to Real>=0 using hA
  lift B to Real>=0 using hB
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at hfA hgB
  norm_cast at hfA hgB
  obtain ⟨C, hC₁, hC₂
-/
theorem Lp_add_le_hasSum_of_nonneg (hp : 1 <= p) (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i) {A B : Real}
    (hA : 0 <= A) (hB : 0 <= B) (hfA : HasSum (fun i => f i ^ p) (A ^ p))
    (hgB : HasSum (fun i => g i ^ p) (B ^ p)) :
    exists C, 0 <= C ∧ C <= A + B ∧ HasSum (fun i => (f i + g i) ^ p) (C ^ p) := by
  lift f to ι -> Real>=0 using hf
  lift g to ι -> Real>=0 using hg
  lift A to Real>=0 using hA
  lift B to Real>=0 using hB
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at hfA hgB
  norm_cast at hfA hgB
  obtain ⟨C, hC₁, hC₂⟩ := NNReal.Lp_add_le_hasSum hp hfA hgB
  use C
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce
  norm_cast
  exact ⟨zero_le, hC₁, hC₂⟩

end Real

namespace ENNReal

variable (f g : ι -> Real>=0∞) {p q : Real}

-- TODO: fix the non-terminal simp on the last line
set_option linter.flexible false in
/--
theorem `inner_le_Lp_mul_Lq` / 定理 `inner_le_Lp_mul_Lq`

English:
theorem inner_le_Lp_mul_Lq
  given: (hpq : p.HolderConjugate q)
  proof: by
  by_cases! H : (∑ i in s, f i ^ p) ^ (1 / p) = 0 ∨ (∑ i in s, g i ^ q) ^ (1 / q) = 0
  · replace H : (forall i in s, f i = 0) ∨ forall i in s, g i = 0 := by
      simpa [ENNReal.rpow_eq_zero_iff, hpq.pos, hpq.symm.pos, asymm hpq.pos, asymm hpq.symm.pos,
        sum_eq_zero_iff_of_nonneg] using H

中文:
定理 inner_le_Lp_mul_Lq
  条件: (hpq : p.HolderConjugate q)
  证明: by
  by_cases! H : (∑ i in s, f i ^ p) ^ (1 / p) = 0 ∨ (∑ i in s, g i ^ q) ^ (1 / q) = 0
  · replace H : (forall i in s, f i = 0) ∨ forall i in s, g i = 0 := by
      simpa [ENNReal.rpow_eq_zero_iff, hpq.pos, hpq.symm.pos, asymm hpq.pos, asymm hpq.symm.pos,
        sum_eq_zero_iff_of_nonneg] using H

Depends on / 依赖: ENNReal, ENNReal.rpow_eq_zero_iff, hpq.pos, hpq.symm.pos, replace, rpow_eq_zero_iff, sum_eq_zero, sum_eq_zero_iff_of_nonneg
-/
theorem inner_le_Lp_mul_Lq (hpq : p.HolderConjugate q) :
    ∑ i in s, f i * g i <= (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) := by
  by_cases! H : (∑ i in s, f i ^ p) ^ (1 / p) = 0 ∨ (∑ i in s, g i ^ q) ^ (1 / q) = 0
  · replace H : (forall i in s, f i = 0) ∨ forall i in s, g i = 0 := by
      simpa [ENNReal.rpow_eq_zero_iff, hpq.pos, hpq.symm.pos, asymm hpq.pos, asymm hpq.symm.pos,
        sum_eq_zero_iff_of_nonneg] using H
    have : forall i in s, f i * g i = 0 := fun i hi => by rcases H with H | H <;> simp [H i hi]
    simp [sum_eq_zero this]
  by_cases H' : (∑ i in s, f i ^ p) ^ (1 / p) = ⊤ ∨ (∑ i in s, g i ^ q) ^ (1 / q) = ⊤
  · rcases H' with H' | H' <;> simp [H', -one_div, -sum_eq_zero_iff, -rpow_eq_zero_iff, H]
  replace H' : (forall i in s, f i != ⊤) ∧ forall i in s, g i != ⊤ := by
    simpa [ENNReal.rpow_eq_top_iff, asymm hpq.pos, asymm hpq.symm.pos, hpq.pos, hpq.symm.pos,
      ENNReal.sum_eq_top, not_or] using H'
  have := ENNReal.coe_le_coe.2 (@NNReal.inner_le_Lp_mul_Lq _ s (fun i => ENNReal.toNNReal (f i))
    (fun i => ENNReal.toNNReal (g i)) _ _ hpq)
  simp [ENNReal.coe_rpow_of_nonneg, hpq.pos.le, hpq.symm.pos.le] at this
  convert! this using 1 <;> [skip; congr 2] <;> [skip; skip; simp; skip; simp] <;>
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp [H'.1 i hi, H'.2 i hi, -WithZero.coe_mul]

/--
lemma `inner_le_weight_mul_Lp_of_nonneg` / 引理 `inner_le_weight_mul_Lp_of_nonneg`

English:
lemma inner_le_weight_mul_Lp_of_nonneg
  given: (s : Finset ι) {p : Real} (hp : 1 <= p) (w f : ι -> Real>=0∞)
  proof: by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  have hp₀ : 0 < p := by positivity
  have hp₁ : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  by_cases! H : (∑ i in s, w i) ^ (1 - p⁻¹) = 0 ∨ (∑ i in s, w i * f i ^ p) ^ p⁻¹ = 0
  · replace H : (forall i in s, w i = 0) ∨ forall i in s, w i = 0 ∨ f i = 0 := by
  

中文:
引理 inner_le_weight_mul_Lp_of_nonneg
  条件: (s : Finset ι) {p : 实数} (hp : 1 <= p) (w f : ι -> 实数>=0∞)
  证明: by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  have hp₀ : 0 < p := by positivity
  have hp₁ : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  by_cases! H : (∑ i in s, w i) ^ (1 - p⁻¹) = 0 ∨ (∑ i in s, w i * f i ^ p) ^ p⁻¹ = 0
  · replace H : (forall i in s, w i = 0) ∨ forall i in s, w i = 0 ∨ f i = 0 := by
  

Depends on / 依赖: eq_or_lt, hp.eq_or_lt, not_gt, replace, sum_eq_zero, sum_eq_zero_iff_of_nonneg
-/
lemma inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : Real} (hp : 1 <= p) (w f : ι -> Real>=0∞) :
    ∑ i in s, w i * f i <= (∑ i in s, w i) ^ (1 - p⁻¹) * (∑ i in s, w i * f i ^ p) ^ p⁻¹ := by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  have hp₀ : 0 < p := by positivity
  have hp₁ : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  by_cases! H : (∑ i in s, w i) ^ (1 - p⁻¹) = 0 ∨ (∑ i in s, w i * f i ^ p) ^ p⁻¹ = 0
  · replace H : (forall i in s, w i = 0) ∨ forall i in s, w i = 0 ∨ f i = 0 := by
      simpa [hp₀, hp₁, hp₀.not_gt, hp₁.not_gt, sum_eq_zero_iff_of_nonneg] using H
    have (i) (hi : i in s) : w i * f i = 0 := by rcases H with H | H <;> simp [H i hi]
    simp [sum_eq_zero this]
  by_cases H' : (∑ i in s, w i) ^ (1 - p⁻¹) = ⊤ ∨ (∑ i in s, w i * f i ^ p) ^ p⁻¹ = ⊤
  · rcases H' with H' | H' <;> simp [H', -one_div, -sum_eq_zero_iff, -rpow_eq_zero_iff, H]
  replace H' : (forall i in s, w i != ⊤) ∧ forall i in s, w i * f i ^ p != ⊤ := by
    simpa [rpow_eq_top_iff, hp₀, hp₁, hp₀.not_gt, hp₁.not_gt, sum_eq_top, not_or] using H'
have := coe_le_coe.2 NNReal.inner_le_weight_mul_Lp s hp.le (fun i => ENNReal.toNNReal (w i))
    fun i => ENNReal.toNNReal (f i)
  rw [coe_mul] at this
  simp_rw [coe_rpow_of_nonneg _ <| inv_nonneg.2 hp₀.le, ofNNReal_finsetSum, ← ENNReal.toNNReal_rpow,
    ← ENNReal.toNNReal_mul, sum_congr rfl fun i hi => coe_toNNReal (H'.2 i hi)] at this
  simp only [toNNReal_mul, coe_mul, sub_nonneg, hp₁.le, coe_rpow_of_nonneg, ofNNReal_finsetSum]
    at this
  convert! this using 2 with i hi
  · obtain hw | hw := eq_or_ne (w i) 0
    · simp [hw]
    rw [coe_toNNReal (H'.1 _ hi)]; rw [coe_toNNReal]
    simpa [mul_eq_top, hw, hp₀, hp₀.not_gt, H'.1 _ hi] using H'.2 _ hi
  · convert! rfl with i hi
    exact coe_toNNReal (H'.1 _ hi)

/--
theorem `rpow_sum_le_const_mul_sum_rpow` / 定理 `rpow_sum_le_const_mul_sum_rpow`

English:
theorem rpow_sum_le_const_mul_sum_rpow
  given: (hp : 1 <= p)
  proof: by
  rcases eq_or_lt_of_le hp with hp | hp
  · simp [← hp]
  let q : Real := p / (p - 1)
  have hpq : p.HolderConjugate q := .conjExponent hp
  have hp₁ : 1 / p * p = 1 := one_div_mul_cancel hpq.ne_zero
  have hq : 1 / q * p = p - 1 := by
    rw [← hpq.div_conj_eq_sub_one]
    ring
  simpa only [ENN

中文:
定理 rpow_sum_le_const_mul_sum_rpow
  条件: (hp : 1 <= p)
  证明: by
  rcases eq_or_lt_of_le hp with hp | hp
  · simp [← hp]
  let q : Real := p / (p - 1)
  have hpq : p.HolderConjugate q := .conjExponent hp
  have hp₁ : 1 / p * p = 1 := one_div_mul_cancel hpq.ne_zero
  have hq : 1 / q * p = p - 1 := by
    rw [← hpq.div_conj_eq_sub_one]
    ring
  simpa only [ENN

Depends on / 依赖: ENNReal, ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_le_rpow, ENNReal.rpow_mul, HolderConjugate, Nat.smul_one_eq_cast, Pi.one_apply, coe_one, conjExponent, div_conj_eq_sub_one, eq_or_lt_of_le, hpq.div_conj_eq_sub_one, hpq.n, hpq.ne_zero, hpq.nonneg, hpq.symm, inner_le_Lp_mul_Lq, mul_rpow_of_nonneg, ne_zero, nonneg
-/
theorem rpow_sum_le_const_mul_sum_rpow (hp : 1 <= p) :
    (∑ i in s, f i) ^ p <= (card s : Real>=0∞) ^ (p - 1) * ∑ i in s, f i ^ p := by
  rcases eq_or_lt_of_le hp with hp | hp
  · simp [← hp]
  let q : Real := p / (p - 1)
  have hpq : p.HolderConjugate q := .conjExponent hp
  have hp₁ : 1 / p * p = 1 := one_div_mul_cancel hpq.ne_zero
  have hq : 1 / q * p = p - 1 := by
    rw [← hpq.div_conj_eq_sub_one]
    ring
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg, ← ENNReal.rpow_mul, hp₁, hq, coe_one,
    one_mul, one_rpow, rpow_one, Pi.one_apply, sum_const, Nat.smul_one_eq_cast] using
    ENNReal.rpow_le_rpow (inner_le_Lp_mul_Lq s 1 f hpq.symm) hpq.nonneg

/--
theorem `Lp_add_le` / 定理 `Lp_add_le`

English:
theorem Lp_add_le
  given: (hp : 1 <= p)
  proof: by
  by_cases H' : (∑ i in s, f i ^ p) ^ (1 / p) = ⊤ ∨ (∑ i in s, g i ^ p) ^ (1 / p) = ⊤
  · rcases H' with H' | H' <;> simp [H', -one_div]
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  replace H' : (forall i in s, f i != ⊤) ∧ forall i in s, g i != ⊤ := by
    simpa [ENNReal.rpow_eq_top_iff,

中文:
定理 Lp_add_le
  条件: (hp : 1 <= p)
  证明: by
  by_cases H' : (∑ i in s, f i ^ p) ^ (1 / p) = ⊤ ∨ (∑ i in s, g i ^ p) ^ (1 / p) = ⊤
  · rcases H' with H' | H' <;> simp [H', -one_div]
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  replace H' : (forall i in s, f i != ⊤) ∧ forall i in s, g i != ⊤ := by
    simpa [ENNReal.rpow_eq_top_iff,

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_rpow_of_n, ENNReal.rpow_eq_top_iff, ENNReal.sum_eq_top, ENNReal.toNNReal, Lp_add_le, NNReal, NNReal.Lp_add_le, coe_le_coe, coe_rpow_of_n, lt_of_lt_of_le, not_or, one_div, replace, rpow_eq_top_iff, sum_eq_top, toNNReal, zero_lt_one
-/
theorem Lp_add_le (hp : 1 <= p) :
    (∑ i in s, (f i + g i) ^ p) ^ (1 / p) <=
      (∑ i in s, f i ^ p) ^ (1 / p) + (∑ i in s, g i ^ p) ^ (1 / p) := by
  by_cases H' : (∑ i in s, f i ^ p) ^ (1 / p) = ⊤ ∨ (∑ i in s, g i ^ p) ^ (1 / p) = ⊤
  · rcases H' with H' | H' <;> simp [H', -one_div]
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  replace H' : (forall i in s, f i != ⊤) ∧ forall i in s, g i != ⊤ := by
    simpa [ENNReal.rpow_eq_top_iff, asymm pos, pos, ENNReal.sum_eq_top, not_or] using H'
  have :=
    ENNReal.coe_le_coe.2
      (@NNReal.Lp_add_le _ s (fun i => ENNReal.toNNReal (f i)) (fun i => ENNReal.toNNReal (g i)) _
        hp)
  push_cast [ENNReal.coe_rpow_of_nonneg, le_of_lt pos, le_of_lt (one_div_pos.2 pos)] at this
  simp_all

end ENNReal

end HoelderMinkowski
