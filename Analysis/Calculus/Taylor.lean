/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Taylor's theorem

This file defines the Taylor polynomial of a real function `f : ℝ → E`,
where `E` is a normed vector space over `ℝ` and proves Taylor's theorem,
which states that if `f` is sufficiently smooth, then
`f` can be approximated by the Taylor polynomial up to an explicit error term.

## Main definitions

* `taylorCoeffWithin`: the Taylor coefficient using `iteratedDerivWithin`
* `taylorWithin`: the Taylor polynomial using `iteratedDerivWithin`

## Main statements

* `taylor_tendsto`: Taylor's theorem as a limit
* `taylor_isLittleO`: Taylor's theorem using little-o notation
* `taylor_mean_remainder`: Taylor's theorem with the general form of the remainder term
* `taylor_mean_remainder_lagrange`: Taylor's theorem with the Lagrange remainder
* `taylor_mean_remainder_cauchy`: Taylor's theorem with the Cauchy remainder
* `exists_taylor_mean_remainder_bound`: Taylor's theorem for vector-valued functions with a
  polynomial bound on the remainder
* `taylor_integral_remainder_of_absolutelyContinuous`,
  `taylor_integral_remainder`: Taylor's theorem with the integral form of the
  remainder

## TODO

* Generalization to higher dimensions

## Tags

Taylor polynomial, Taylor's theorem
-/

@[expose] public section


open scoped Interval Topology Nat

open Set

variable {𝕜 E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace Real E]

/--
Definition of `taylorCoeffWithin` / `taylorCoeffWithin` 的定义

English:
definition taylorCoeffWithin
  signature: (f : Real -> E) (k : Nat) (s : Set Real) (x₀ : Real)
  body: (k ! : Real)⁻¹ • iteratedDerivWithin k f s x₀

中文:
定义 taylorCoeffWithin
  签名: (f : 实数 -> E) (k : 自然数) (s : 集合 实数) (x₀ : 实数)
  定义体: (k ! : Real)⁻¹ • iteratedDerivWithin k f s x₀

Depends on / 依赖: iteratedDerivWithin
-/
noncomputable def taylorCoeffWithin (f : Real -> E) (k : Nat) (s : Set Real) (x₀ : Real) : E :=
  (k ! : Real)⁻¹ • iteratedDerivWithin k f s x₀

/--
Definition of `taylorWithin` / `taylorWithin` 的定义

English:
definition taylorWithin
  signature: (f : Real -> E) (n : Nat) (s : Set Real) (x₀ : Real)
  body: (Finset.range (n + 1)).sum fun k =>
    PolynomialModule.comp (Polynomial.X - Polynomial.C x₀)
      (PolynomialModule.single Real k (taylorCoeffWithin f k s x₀))

中文:
定义 taylorWithin
  签名: (f : 实数 -> E) (n : 自然数) (s : 集合 实数) (x₀ : 实数)
  定义体: (Finset.range (n + 1)).sum fun k =>
    PolynomialModule.comp (Polynomial.X - Polynomial.C x₀)
      (PolynomialModule.single Real k (taylorCoeffWithin f k s x₀))

Depends on / 依赖: Finset, Finset.range, Polynomial, Polynomial.C, Polynomial.X, PolynomialModule, PolynomialModule.comp, PolynomialModule.single, single, taylorCoeffWithin
-/
noncomputable def taylorWithin (f : Real -> E) (n : Nat) (s : Set Real) (x₀ : Real) : PolynomialModule Real E :=
  (Finset.range (n + 1)).sum fun k =>
    PolynomialModule.comp (Polynomial.X - Polynomial.C x₀)
      (PolynomialModule.single Real k (taylorCoeffWithin f k s x₀))

/--
Definition of `taylorWithinEval` / `taylorWithinEval` 的定义

English:
definition taylorWithinEval
  signature: (f : Real -> E) (n : Nat) (s : Set Real) (x₀ x : Real)
  body: PolynomialModule.eval x (taylorWithin f n s x₀)

中文:
定义 taylorWithinEval
  签名: (f : 实数 -> E) (n : 自然数) (s : 集合 实数) (x₀ x : 实数)
  定义体: PolynomialModule.eval x (taylorWithin f n s x₀)

Depends on / 依赖: PolynomialModule, PolynomialModule.eval, taylorWithin
-/
noncomputable def taylorWithinEval (f : Real -> E) (n : Nat) (s : Set Real) (x₀ x : Real) : E :=
  PolynomialModule.eval x (taylorWithin f n s x₀)

/--
theorem `taylorWithin_succ` / 定理 `taylorWithin_succ`

English:
theorem taylorWithin_succ
  given: (f : Real -> E) (n : Nat) (s : Set Real) (x₀ : Real)
  proof: by
  dsimp only [taylorWithin]
  rw [Finset.sum_range_succ]

@[simp]

中文:
定理 taylorWithin_succ
  条件: (f : 实数 -> E) (n : 自然数) (s : 集合 实数) (x₀ : 实数)
  证明: by
  dsimp only [taylorWithin]
  rw [Finset.sum_range_succ]

@[simp]

Depends on / 依赖: Finset, Finset.sum_range_succ, sum_range_succ, taylorWithin
-/
theorem taylorWithin_succ (f : Real -> E) (n : Nat) (s : Set Real) (x₀ : Real) :
    taylorWithin f (n + 1) s x₀ = taylorWithin f n s x₀ +
      PolynomialModule.comp (Polynomial.X - Polynomial.C x₀)
      (PolynomialModule.single Real (n + 1) (taylorCoeffWithin f (n + 1) s x₀)) := by
  dsimp only [taylorWithin]
  rw [Finset.sum_range_succ]

@[simp]
/--
theorem `taylorWithinEval_succ` / 定理 `taylorWithinEval_succ`

English:
theorem taylorWithinEval_succ
  given: (f : Real -> E) (n : Nat) (s : Set Real) (x₀ x : Real)
  proof: by
  simp_rw [taylorWithinEval, taylorWithin_succ, map_add, PolynomialModule.comp_eval]
  congr
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    PolynomialModule.eval_single, mul_inv_rev]
  dsimp only [taylorCoeffWithin]
  rw [← mul_smul]; rw [mul_comm]; rw [Nat.factorial_

中文:
定理 taylorWithinEval_succ
  条件: (f : 实数 -> E) (n : 自然数) (s : 集合 实数) (x₀ x : 实数)
  证明: by
  simp_rw [taylorWithinEval, taylorWithin_succ, map_add, PolynomialModule.comp_eval]
  congr
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    PolynomialModule.eval_single, mul_inv_rev]
  dsimp only [taylorCoeffWithin]
  rw [← mul_smul]; rw [mul_comm]; rw [Nat.factorial_

Depends on / 依赖: Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.factorial_succ, Polynomial, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub, PolynomialModule, PolynomialModule.comp_eval, PolynomialModule.eval_single, cast_add, cast_mul, cast_one, comp_eval, eval_C, eval_X, eval_single, eval_sub, factorial_succ
-/
theorem taylorWithinEval_succ (f : Real -> E) (n : Nat) (s : Set Real) (x₀ x : Real) :
    taylorWithinEval f (n + 1) s x₀ x = taylorWithinEval f n s x₀ x +
      (((n + 1 : Real) * n !)⁻¹ * (x - x₀) ^ (n + 1)) • iteratedDerivWithin (n + 1) f s x₀ := by
  simp_rw [taylorWithinEval, taylorWithin_succ, map_add, PolynomialModule.comp_eval]
  congr
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    PolynomialModule.eval_single, mul_inv_rev]
  dsimp only [taylorCoeffWithin]
  rw [← mul_smul]; rw [mul_comm]; rw [Nat.factorial_succ]; rw [Nat.cast_mul]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [mul_inv_rev]

/-- The Taylor polynomial of order zero evaluates to `f x`. -/
@[simp]
/--
theorem `taylor_within_zero_eval` / 定理 `taylor_within_zero_eval`

English:
theorem taylor_within_zero_eval
  given: (f : Real -> E) (s : Set Real) (x₀ x : Real)
  proof: by
  dsimp only [taylorWithinEval]
  dsimp only [taylorWithin]
  dsimp only [taylorCoeffWithin]
  simp

中文:
定理 taylor_within_zero_eval
  条件: (f : 实数 -> E) (s : 集合 实数) (x₀ x : 实数)
  证明: by
  dsimp only [taylorWithinEval]
  dsimp only [taylorWithin]
  dsimp only [taylorCoeffWithin]
  simp

Depends on / 依赖: taylorCoeffWithin, taylorWithin, taylorWithinEval
-/
theorem taylor_within_zero_eval (f : Real -> E) (s : Set Real) (x₀ x : Real) :
    taylorWithinEval f 0 s x₀ x = f x₀ := by
  dsimp only [taylorWithinEval]
  dsimp only [taylorWithin]
  dsimp only [taylorCoeffWithin]
  simp

/-- Evaluating the Taylor polynomial at `x = x₀` yields `f x`. -/
@[simp]
/--
theorem `taylorWithinEval_self` / 定理 `taylorWithinEval_self`

English:
theorem taylorWithinEval_self
  given: (f : Real -> E) (n : Nat) (s : Set Real) (x₀ : Real)
  proof: by
  induction n with
  | zero => exact taylor_within_zero_eval _ _ _ _
  | succ k hk => simp [hk]

中文:
定理 taylorWithinEval_self
  条件: (f : 实数 -> E) (n : 自然数) (s : 集合 实数) (x₀ : 实数)
  证明: by
  induction n with
  | zero => exact taylor_within_zero_eval _ _ _ _
  | succ k hk => simp [hk]

Depends on / 依赖: taylor_within_zero_eval
-/
theorem taylorWithinEval_self (f : Real -> E) (n : Nat) (s : Set Real) (x₀ : Real) :
    taylorWithinEval f n s x₀ x₀ = f x₀ := by
  induction n with
  | zero => exact taylor_within_zero_eval _ _ _ _
  | succ k hk => simp [hk]

/--
theorem `taylor_within_apply` / 定理 `taylor_within_apply`

English:
theorem taylor_within_apply
  given: (f : Real -> E) (n : Nat) (s : Set Real) (x₀ x : Real)
  proof: by
  induction n with
  | zero => simp
  | succ k hk =>
    rw [taylorWithinEval_succ]; rw [Finset.sum_range_succ]; rw [hk]
    simp [Nat.factorial]

中文:
定理 taylor_within_apply
  条件: (f : 实数 -> E) (n : 自然数) (s : 集合 实数) (x₀ x : 实数)
  证明: by
  induction n with
  | zero => simp
  | succ k hk =>
    rw [taylorWithinEval_succ]; rw [Finset.sum_range_succ]; rw [hk]
    simp [Nat.factorial]

Depends on / 依赖: Finset, Finset.sum_range_succ, Nat.factorial, factorial, sum_range_succ, taylorWithinEval_succ
-/
theorem taylor_within_apply (f : Real -> E) (n : Nat) (s : Set Real) (x₀ x : Real) :
    taylorWithinEval f n s x₀ x =
      ∑ k in Finset.range (n + 1), ((k ! : Real)⁻¹ * (x - x₀) ^ k) • iteratedDerivWithin k f s x₀ := by
  induction n with
  | zero => simp
  | succ k hk =>
    rw [taylorWithinEval_succ]; rw [Finset.sum_range_succ]; rw [hk]
    simp [Nat.factorial]

/--
theorem `continuousOn_taylorWithinEval` / 定理 `continuousOn_taylorWithinEval`

English:
theorem continuousOn_taylorWithinEval
  statement: {f : Real -> E} {x : Real} {n : Nat} {s : Set Real}
  proof: by
  simp_rw [taylor_within_apply]
  refine continuousOn_finsetSum (Finset.range (n + 1)) fun i hi => ?_
  refine (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow _)).smul ?_
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hs] at hf
  simp only [Finset.mem_range] at

中文:
定理 continuousOn_taylorWithinEval
  结论: {f : 实数 -> E} {x : 实数} {n : 自然数} {s : 集合 实数}
  证明: by
  simp_rw [taylor_within_apply]
  refine continuousOn_finsetSum (Finset.range (n + 1)) fun i hi => ?_
  refine (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow _)).smul ?_
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hs] at hf
  simp only [Finset.mem_range] at

Depends on / 依赖: Finset, Finset.mem_range, Finset.range, Nat.lt_succ_iff.mp, contDiffOn_nat_iff_continuousOn_differentiableOn_deriv, continuousOn_const, continuousOn_const.mul, continuousOn_const.sub, continuousOn_finsetSum, continuousOn_id, lt_succ_iff, mem_range, simp_rw, taylor_within_apply
-/
theorem continuousOn_taylorWithinEval {f : Real -> E} {x : Real} {n : Nat} {s : Set Real}
    (hs : UniqueDiffOn Real s) (hf : ContDiffOn Real n f s) :
    ContinuousOn (fun t => taylorWithinEval f n s t x) s := by
  simp_rw [taylor_within_apply]
  refine continuousOn_finsetSum (Finset.range (n + 1)) fun i hi => ?_
  refine (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow _)).smul ?_
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hs] at hf
  simp only [Finset.mem_range] at hi
  refine hf.1 i ?_
  simp only [Nat.lt_succ_iff.mp hi]

/--
theorem `monomial_has_deriv_aux` / 定理 `monomial_has_deriv_aux`

English:
theorem monomial_has_deriv_aux
  given: (t x : Real) (n : Nat)
  proof: by
  simp_rw [sub_eq_neg_add]
  rw [← neg_one_mul]; rw [mul_comm (-1 : Real)]; rw [mul_assoc]; rw [mul_comm (-1 : Real)]; rw [← mul_assoc]
  convert! ((hasDerivAt_id t).neg.add_const x).pow (n + 1)
  simp only [Nat.cast_add, Nat.cast_one]

中文:
定理 monomial_has_deriv_aux
  条件: (t x : 实数) (n : 自然数)
  证明: by
  simp_rw [sub_eq_neg_add]
  rw [← neg_one_mul]; rw [mul_comm (-1 : Real)]; rw [mul_assoc]; rw [mul_comm (-1 : Real)]; rw [← mul_assoc]
  convert! ((hasDerivAt_id t).neg.add_const x).pow (n + 1)
  simp only [Nat.cast_add, Nat.cast_one]

Depends on / 依赖: Nat.cast_add, Nat.cast_one, add_const, cast_add, cast_one, convert, hasDerivAt_id, mul_assoc, mul_comm, neg.add_const, neg_one_mul, simp_rw, sub_eq_neg_add
-/
theorem monomial_has_deriv_aux (t x : Real) (n : Nat) :
    HasDerivAt (fun y => (x - y) ^ (n + 1)) (-(n + 1) * (x - t) ^ n) t := by
  simp_rw [sub_eq_neg_add]
  rw [← neg_one_mul]; rw [mul_comm (-1 : Real)]; rw [mul_assoc]; rw [mul_comm (-1 : Real)]; rw [← mul_assoc]
  convert! ((hasDerivAt_id t).neg.add_const x).pow (n + 1)
  simp only [Nat.cast_add, Nat.cast_one]

/--
theorem `hasDerivWithinAt_taylor_coeff_within` / 定理 `hasDerivWithinAt_taylor_coeff_within`

English:
theorem hasDerivWithinAt_taylor_coeff_within
  statement: {f : Real -> E} {x y : Real} {k : Nat} {s t : Set Real}
  proof: by
  replace hf :
    HasDerivWithinAt (iteratedDerivWithin (k + 1) f s) (iteratedDerivWithin (k + 2) f s y) t y := by
    convert (hf.mono_of_mem_nhdsWithin hs).hasDerivWithinAt
    rw [iteratedDerivWithin_succ]
    exact (derivWithin_of_mem_nhdsWithin hs ht hf).symm
  have : HasDerivWithinAt (fun 

中文:
定理 hasDerivWithinAt_taylor_coeff_within
  结论: {f : 实数 -> E} {x y : 实数} {k : 自然数} {s t : 集合 实数}
  证明: by
  replace hf :
    HasDerivWithinAt (iteratedDerivWithin (k + 1) f s) (iteratedDerivWithin (k + 2) f s y) t y := by
    convert (hf.mono_of_mem_nhdsWithin hs).hasDerivWithinAt
    rw [iteratedDerivWithin_succ]
    exact (derivWithin_of_mem_nhdsWithin hs ht hf).symm
  have : HasDerivWithinAt (fun 

Depends on / 依赖: HasDerivWithinAt, convert, derivWithin_of_mem_nhdsWithin, hasDerivWithinAt, hf.mono_of_mem_nhdsWithin, iteratedDerivWithin, iteratedDerivWithin_succ, mono_of_mem_nhdsWithin, replace
-/
theorem hasDerivWithinAt_taylor_coeff_within {f : Real -> E} {x y : Real} {k : Nat} {s t : Set Real}
    (ht : UniqueDiffWithinAt Real t y) (hs : s in 𝓝[t] y)
    (hf : DifferentiableWithinAt Real (iteratedDerivWithin (k + 1) f s) s y) :
    HasDerivWithinAt
      (fun z => (((k + 1 : Real) * k !)⁻¹ * (x - z) ^ (k + 1)) • iteratedDerivWithin (k + 1) f s z)
      ((((k + 1 : Real) * k !)⁻¹ * (x - y) ^ (k + 1)) • iteratedDerivWithin (k + 2) f s y -
        ((k ! : Real)⁻¹ * (x - y) ^ k) • iteratedDerivWithin (k + 1) f s y) t y := by
  replace hf :
    HasDerivWithinAt (iteratedDerivWithin (k + 1) f s) (iteratedDerivWithin (k + 2) f s y) t y := by
    convert (hf.mono_of_mem_nhdsWithin hs).hasDerivWithinAt
    rw [iteratedDerivWithin_succ]
    exact (derivWithin_of_mem_nhdsWithin hs ht hf).symm
  have : HasDerivWithinAt (fun t => ((k + 1 : Real) * k !)⁻¹ * (x - t) ^ (k + 1))
      (-((k ! : Real)⁻¹ * (x - y) ^ k)) t y := by
    -- Commuting the factors:
    have : -((k ! : Real)⁻¹ * (x - y) ^ k) = ((k + 1 : Real) * k !)⁻¹ * (-(k + 1) * (x - y) ^ k) := by
      field
    rw [this]
    exact (monomial_has_deriv_aux y x _).hasDerivWithinAt.const_mul _
  convert! this.smul hf using 1
  field_simp
  module

/--
theorem `hasDerivWithinAt_taylorWithinEval` / 定理 `hasDerivWithinAt_taylorWithinEval`

English:
theorem hasDerivWithinAt_taylorWithinEval
  statement: {f : Real -> E} {x y : Real} {n : Nat} {s s' : Set Real}
  proof: by
  have hs'_unique : UniqueDiffWithinAt Real s' y :=
    UniqueDiffWithinAt.mono_nhds (hs_unique _ (h hy)) (nhdsWithin_le_iff.mpr hs')
  induction n with
  | zero =>
    simp only [taylor_within_zero_eval, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
      mul_one, zero_add, one_smul]
    

中文:
定理 hasDerivWithinAt_taylorWithinEval
  结论: {f : 实数 -> E} {x y : 实数} {n : 自然数} {s s' : 集合 实数}
  证明: by
  have hs'_unique : UniqueDiffWithinAt Real s' y :=
    UniqueDiffWithinAt.mono_nhds (hs_unique _ (h hy)) (nhdsWithin_le_iff.mpr hs')
  induction n with
  | zero =>
    simp only [taylor_within_zero_eval, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
      mul_one, zero_add, one_smul]
    

Depends on / 依赖: Nat.add_succ, Nat.cast_mul, Nat.cast_one, Nat.factorial_succ, Nat.factorial_zero, UniqueDiffWithinAt, UniqueDiffWithinAt.mono_nhds, _unique, add_succ, add_zero, cast_mul, cast_one, factorial_succ, factorial_zero, hasDerivWithinAt, hasDerivWithinAt.mono, hs_unique, inv_one, iteratedDerivWithin_one, iteratedDerivWithin_zero
-/
theorem hasDerivWithinAt_taylorWithinEval {f : Real -> E} {x y : Real} {n : Nat} {s s' : Set Real}
    (hs_unique : UniqueDiffOn Real s) (hs' : s' in 𝓝[s] y)
    (hy : y in s') (h : s' subseteq s) (hf : ContDiffOn Real n f s)
    (hf' : DifferentiableWithinAt Real (iteratedDerivWithin n f s) s y) :
    HasDerivWithinAt (fun t => taylorWithinEval f n s t x)
      (((n ! : Real)⁻¹ * (x - y) ^ n) • iteratedDerivWithin (n + 1) f s y) s' y := by
  have hs'_unique : UniqueDiffWithinAt Real s' y :=
    UniqueDiffWithinAt.mono_nhds (hs_unique _ (h hy)) (nhdsWithin_le_iff.mpr hs')
  induction n with
  | zero =>
    simp only [taylor_within_zero_eval, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
      mul_one, zero_add, one_smul]
    simp only [iteratedDerivWithin_zero] at hf'
    rw [iteratedDerivWithin_one]
    exact hf'.hasDerivWithinAt.mono h
  | succ k hk =>
    simp_rw [Nat.add_succ, taylorWithinEval_succ]
    simp only [add_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have coe_lt_succ : (k : WithTop Nat) < k.succ := Nat.cast_lt.2 k.lt_succ_self
    have hdiff : DifferentiableOn Real (iteratedDerivWithin k f s) s' :=
      (hf.differentiableOn_iteratedDerivWithin (mod_cast coe_lt_succ) hs_unique).mono h
    specialize hk hf.of_succ ((hdiff y hy).mono_of_mem_nhdsWithin hs')
    convert!
      hk.add
        (hasDerivWithinAt_taylor_coeff_within hs'_unique (nhdsWithin_mono _ h self_mem_nhdsWithin)
          hf') using 1
    exact (add_sub_cancel _ _).symm

/--
theorem `taylorWithinEval_hasDerivAt_Ioo` / 定理 `taylorWithinEval_hasDerivAt_Ioo`

English:
theorem taylorWithinEval_hasDerivAt_Ioo
  statement: {f : Real -> E} {a b t : Real} (x : Real) {n : Nat} (hx : a < b)
  proof: have h_nhds : Ioo a b in 𝓝 t := isOpen_Ioo.mem_nhds ht
  have h_nhds' : Ioo a b in 𝓝[Icc a b] t := nhdsWithin_le_nhds h_nhds
  (hasDerivWithinAt_taylorWithinEval (uniqueDiffOn_Icc hx) h_nhds' ht
Ioo_subset_Icc_self hf (hf' t ht).mono_of_mem_nhdsWithin h_nhds').hasDerivAt h_nhds

中文:
定理 taylorWithinEval_hasDerivAt_Ioo
  结论: {f : 实数 -> E} {a b t : 实数} (x : 实数) {n : 自然数} (hx : a < b)
  证明: have h_nhds : Ioo a b in 𝓝 t := isOpen_Ioo.mem_nhds ht
  have h_nhds' : Ioo a b in 𝓝[Icc a b] t := nhdsWithin_le_nhds h_nhds
  (hasDerivWithinAt_taylorWithinEval (uniqueDiffOn_Icc hx) h_nhds' ht
Ioo_subset_Icc_self hf (hf' t ht).mono_of_mem_nhdsWithin h_nhds').hasDerivAt h_nhds

Depends on / 依赖: Ioo_subset_Icc_self, h_nhds, hasDerivAt, hasDerivWithinAt_taylorWithinEval, isOpen_Ioo, isOpen_Ioo.mem_nhds, mem_nhds, mono_of_mem_nhdsWithin, nhdsWithin_le_nhds, uniqueDiffOn_Icc
-/
theorem taylorWithinEval_hasDerivAt_Ioo {f : Real -> E} {a b t : Real} (x : Real) {n : Nat} (hx : a < b)
    (ht : t in Ioo a b) (hf : ContDiffOn Real n f (Icc a b))
    (hf' : DifferentiableOn Real (iteratedDerivWithin n f (Icc a b)) (Ioo a b)) :
    HasDerivAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((n ! : Real)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) t :=
  have h_nhds : Ioo a b in 𝓝 t := isOpen_Ioo.mem_nhds ht
  have h_nhds' : Ioo a b in 𝓝[Icc a b] t := nhdsWithin_le_nhds h_nhds
  (hasDerivWithinAt_taylorWithinEval (uniqueDiffOn_Icc hx) h_nhds' ht
Ioo_subset_Icc_self hf (hf' t ht).mono_of_mem_nhdsWithin h_nhds').hasDerivAt h_nhds

/--
theorem `hasDerivWithinAt_taylorWithinEval_at_Icc` / 定理 `hasDerivWithinAt_taylorWithinEval_at_Icc`

English:
theorem hasDerivWithinAt_taylorWithinEval_at_Icc
  statement: {f : Real -> E} {a b t : Real} (x : Real) {n : Nat}
  proof: hasDerivWithinAt_taylorWithinEval (uniqueDiffOn_Icc hx)
    self_mem_nhdsWithin ht rfl.subset hf (hf' t ht)

中文:
定理 hasDerivWithinAt_taylorWithinEval_at_Icc
  结论: {f : 实数 -> E} {a b t : 实数} (x : 实数) {n : 自然数}
  证明: hasDerivWithinAt_taylorWithinEval (uniqueDiffOn_Icc hx)
    self_mem_nhdsWithin ht rfl.subset hf (hf' t ht)

Depends on / 依赖: hasDerivWithinAt_taylorWithinEval, rfl.subset, self_mem_nhdsWithin, subset, uniqueDiffOn_Icc
-/
theorem hasDerivWithinAt_taylorWithinEval_at_Icc {f : Real -> E} {a b t : Real} (x : Real) {n : Nat}
    (hx : a < b) (ht : t in Icc a b) (hf : ContDiffOn Real n f (Icc a b))
    (hf' : DifferentiableOn Real (iteratedDerivWithin n f (Icc a b)) (Icc a b)) :
    HasDerivWithinAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((n ! : Real)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) (Icc a b) t :=
  hasDerivWithinAt_taylorWithinEval (uniqueDiffOn_Icc hx)
    self_mem_nhdsWithin ht rfl.subset hf (hf' t ht)

/--
theorem `hasDerivAt_taylorWithinEval_succ` / 定理 `hasDerivAt_taylorWithinEval_succ`

English:
theorem hasDerivAt_taylorWithinEval_succ
  given: {x₀ x : Real} {s : Set Real} (f : Real -> E) (n : Nat)
  proof: by
  change HasDerivAt (fun x => taylorWithinEval f _ s x₀ x) _ _
  simp_rw [taylor_within_apply]
  have : forall (i : Nat) {c : Real} {c' : E},
      HasDerivAt (fun x => (c * (x - x₀) ^ i) • c') ((c * (i * (x - x₀) ^ (i - 1) * 1)) • c') x :=
.smul_const _ .const_mul _ .pow _ .sub_const _ fun _ _ =

中文:
定理 hasDerivAt_taylorWithinEval_succ
  条件: {x₀ x : 实数} {s : 集合 实数} (f : 实数 -> E) (n : 自然数)
  证明: by
  change HasDerivAt (fun x => taylorWithinEval f _ s x₀ x) _ _
  simp_rw [taylor_within_apply]
  have : forall (i : Nat) {c : Real} {c' : E},
      HasDerivAt (fun x => (c * (x - x₀) ^ i) • c') ((c * (i * (x - x₀) ^ (i - 1) * 1)) • c') x :=
.smul_const _ .const_mul _ .pow _ .sub_const _ fun _ _ =

Depends on / 依赖: Finset, Finset.sum_range_succ, HasDerivAt, HasDerivAt.fun_sum, Nat.cast_zero, add_zero, cast_zero, congr_deriv, const_mul, fun_sum, hasDerivAt_id, mul_zero, simp_rw, smul_const, sub_const, sum_range_succ, taylorWithinEval, taylor_within_apply, zero_mul, zero_smul
-/
theorem hasDerivAt_taylorWithinEval_succ {x₀ x : Real} {s : Set Real} (f : Real -> E) (n : Nat) :
    HasDerivAt (taylorWithinEval f (n + 1) s x₀)
      (taylorWithinEval (derivWithin f s) n s x₀ x) x := by
  change HasDerivAt (fun x => taylorWithinEval f _ s x₀ x) _ _
  simp_rw [taylor_within_apply]
  have : forall (i : Nat) {c : Real} {c' : E},
      HasDerivAt (fun x => (c * (x - x₀) ^ i) • c') ((c * (i * (x - x₀) ^ (i - 1) * 1)) • c') x :=
.smul_const _ .const_mul _ .pow _ .sub_const _ fun _ _ => hasDerivAt_id _
.congr_deriv apply HasDerivAt.fun_sum (fun i _ => this i)
  rw [Finset.sum_range_succ']; rw [Nat.cast_zero]; rw [zero_mul]; rw [zero_mul]; rw [mul_zero]; rw [zero_smul]; rw [add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [← iteratedDerivWithin_succ']
  congr 1
  simp [field, Nat.factorial_succ]

/--
theorem `taylor_isLittleO` / 定理 `taylor_isLittleO`

English:
theorem taylor_isLittleO
  statement: {f : Real -> E} {x₀ : Real} {n : Nat} {s : Set Real}
  proof: by
  induction n generalizing f with
  | zero =>
    simp only [taylor_within_zero_eval, pow_zero, Asymptotics.isLittleO_one_iff]
    rw [tendsto_sub_nhds_zero_iff]
    exact hf.continuousOn.continuousWithinAt hx₀s
  | succ n h =>
    rcases s.eq_singleton_or_nontrivial hx₀s with rfl | hs'
    · sim

中文:
定理 taylor_isLittleO
  结论: {f : 实数 -> E} {x₀ : 实数} {n : 自然数} {s : 集合 实数}
  证明: by
  induction n generalizing f with
  | zero =>
    simp only [taylor_within_zero_eval, pow_zero, Asymptotics.isLittleO_one_iff]
    rw [tendsto_sub_nhds_zero_iff]
    exact hf.continuousOn.continuousWithinAt hx₀s
  | succ n h =>
    rcases s.eq_singleton_or_nontrivial hx₀s with rfl | hs'
    · sim

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_one_iff, Convex, Convex.isLittleO_pow_succ_real, Nat.cast_add, Nat.cast_one, cast_add, cast_one, continuousOn, continuousWithinAt, convert, derivWithin, eq_singleton_or_nontrivial, generalizing, hf.continuousOn.continuousWithinAt, hf.derivWithin, hs.nontrivial_iff_nonempty_interior, isLittleO_one_iff, isLittleO_pow_succ_real, le_rfl
-/
theorem taylor_isLittleO {f : Real -> E} {x₀ : Real} {n : Nat} {s : Set Real}
    (hs : Convex Real s) (hx₀s : x₀ in s) (hf : ContDiffOn Real n f s) :
    (fun x => f x - taylorWithinEval f n s x₀ x) =o[𝓝[s] x₀] fun x => (x - x₀) ^ n := by
  induction n generalizing f with
  | zero =>
    simp only [taylor_within_zero_eval, pow_zero, Asymptotics.isLittleO_one_iff]
    rw [tendsto_sub_nhds_zero_iff]
    exact hf.continuousOn.continuousWithinAt hx₀s
  | succ n h =>
    rcases s.eq_singleton_or_nontrivial hx₀s with rfl | hs'
    · simp
    replace hs' := uniqueDiffOn_convex hs (hs.nontrivial_iff_nonempty_interior.1 hs')
    simp only [Nat.cast_add, Nat.cast_one] at hf
    convert!
      Convex.isLittleO_pow_succ_real hs hx₀s ?_ (h (hf.derivWithin hs' le_rfl)) (f := fun x =>
        f x - taylorWithinEval f (n + 1) s x₀ x) using 1
    · simp
    · intro x hx
      refine HasDerivWithinAt.sub ?_ (hasDerivAt_taylorWithinEval_succ f n).hasDerivWithinAt
      exact (hf.differentiableOn (by simp) _ hx).hasDerivWithinAt

/--
theorem `taylor_isLittleO_univ` / 定理 `taylor_isLittleO_univ`

English:
theorem taylor_isLittleO_univ
  given: {f : Real -> E} {x₀ : Real} {n : Nat} (hf : ContDiff Real n f)
  proof: by
  simpa using taylor_isLittleO convex_univ (mem_univ x₀) hf.contDiffOn

中文:
定理 taylor_isLittleO_univ
  条件: {f : 实数 -> E} {x₀ : 实数} {n : 自然数} (hf : 连续可微 实数 n f)
  证明: by
  simpa using taylor_isLittleO convex_univ (mem_univ x₀) hf.contDiffOn

Depends on / 依赖: contDiffOn, convex_univ, hf.contDiffOn, mem_univ, taylor_isLittleO
-/
theorem taylor_isLittleO_univ {f : Real -> E} {x₀ : Real} {n : Nat} (hf : ContDiff Real n f) :
    (fun x => f x - taylorWithinEval f n univ x₀ x) =o[𝓝 x₀] fun x => (x - x₀) ^ n := by
  simpa using taylor_isLittleO convex_univ (mem_univ x₀) hf.contDiffOn

/--
theorem `taylor_tendsto` / 定理 `taylor_tendsto`

English:
theorem taylor_tendsto
  statement: {f : Real -> E} {x₀ : Real} {n : Nat} {s : Set Real}
  proof: by
  have h_isLittleO := (taylor_isLittleO hs hx₀s hf).norm_norm
  rw [Asymptotics.isLittleO_iff_tendsto] at h_isLittleO
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_smul, div_eq_inv_mul] using h_isLittleO
  · simp only [norm_pow, Real.norm_eq_abs, pow_eq_zero_iff', abs_eq_zero, ne_eq

中文:
定理 taylor_tendsto
  结论: {f : 实数 -> E} {x₀ : 实数} {n : 自然数} {s : 集合 实数}
  证明: by
  have h_isLittleO := (taylor_isLittleO hs hx₀s hf).norm_norm
  rw [Asymptotics.isLittleO_iff_tendsto] at h_isLittleO
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_smul, div_eq_inv_mul] using h_isLittleO
  · simp only [norm_pow, Real.norm_eq_abs, pow_eq_zero_iff', abs_eq_zero, ne_eq

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_iff_tendsto, Real.norm_eq_abs, abs_eq_zero, and_imp, div_eq_inv_mul, h_isLittleO, isLittleO_iff_tendsto, ne_eq, norm_eq_abs, norm_eq_zero, norm_norm, norm_pow, norm_smul, pow_eq_zero_iff, sub_eq_zero, taylor_isLittleO, tendsto_zero_iff_norm_tendsto_zero
-/
theorem taylor_tendsto {f : Real -> E} {x₀ : Real} {n : Nat} {s : Set Real}
    (hs : Convex Real s) (hx₀s : x₀ in s) (hf : ContDiffOn Real n f s) :
    Filter.Tendsto (fun x => ((x - x₀) ^ n)⁻¹ • (f x - taylorWithinEval f n s x₀ x))
      (𝓝[s] x₀) (𝓝 0) := by
  have h_isLittleO := (taylor_isLittleO hs hx₀s hf).norm_norm
  rw [Asymptotics.isLittleO_iff_tendsto] at h_isLittleO
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_smul, div_eq_inv_mul] using h_isLittleO
  · simp only [norm_pow, Real.norm_eq_abs, pow_eq_zero_iff', abs_eq_zero, ne_eq, norm_eq_zero,
      and_imp]
    intro x hx
    rw [sub_eq_zero] at hx
    simp [hx]

/--
theorem `Real.taylor_tendsto` / 定理 `Real.taylor_tendsto`

English:
theorem Real.taylor_tendsto
  statement: {f : Real -> Real} {x₀ : Real} {n : Nat} {s : Set Real}
  proof: by
  convert _root_.taylor_tendsto hs hx₀s hf with x
  simp [div_eq_inv_mul]

中文:
定理 实数.taylor_tendsto
  结论: {f : 实数 -> 实数} {x₀ : 实数} {n : 自然数} {s : 集合 实数}
  证明: by
  convert _root_.taylor_tendsto hs hx₀s hf with x
  simp [div_eq_inv_mul]

Depends on / 依赖: _root_, _root_.taylor_tendsto, convert, div_eq_inv_mul, taylor_tendsto
-/
theorem Real.taylor_tendsto {f : Real -> Real} {x₀ : Real} {n : Nat} {s : Set Real}
    (hs : Convex Real s) (hx₀s : x₀ in s) (hf : ContDiffOn Real n f s) :
    Filter.Tendsto (fun x => (f x - taylorWithinEval f n s x₀ x) / (x - x₀) ^ n)
      (𝓝[s] x₀) (𝓝 0) := by
  convert _root_.taylor_tendsto hs hx₀s hf with x
  simp [div_eq_inv_mul]


/-! ### Taylor's theorem with mean value type remainder estimate -/


/--
theorem `taylor_mean_remainder` / 定理 `taylor_mean_remainder`

English:
theorem taylor_mean_remainder
  statement: {f : Real -> Real} {g g' : Real -> Real} {x x₀ : Real} {n : Nat} (hx : x₀ != x)
  proof: by
  have hx₁ : min x₀ x < max x₀ x := by grind
  -- We apply the mean value theorem
  rcases exists_ratio_hasDerivAt_eq_ratio_slope (fun t => taylorWithinEval f n (uIcc x₀ x) t x)
      (fun t => ((n ! : Real)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (uIcc x₀ x) t) hx₁
      (continuousOn_t

中文:
定理 taylor_mean_remainder
  结论: {f : 实数 -> 实数} {g g' : 实数 -> 实数} {x x₀ : 实数} {n : 自然数} (hx : x₀ != x)
  证明: by
  have hx₁ : min x₀ x < max x₀ x := by grind
  -- We apply the mean value theorem
  rcases exists_ratio_hasDerivAt_eq_ratio_slope (fun t => taylorWithinEval f n (uIcc x₀ x) t x)
      (fun t => ((n ! : Real)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (uIcc x₀ x) t) hx₁
      (continuousOn_t
-/
theorem taylor_mean_remainder {f : Real -> Real} {g g' : Real -> Real} {x x₀ : Real} {n : Nat} (hx : x₀ != x)
    (hf : ContDiffOn Real n f (uIcc x₀ x))
    (hf' : DifferentiableOn Real (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x))
    (gcont : ContinuousOn g (uIcc x₀ x))
    (gdiff : forall x_1 : Real, x_1 in uIoo x₀ x -> HasDerivAt g (g' x_1) x_1)
    (g'_ne : forall x_1 : Real, x_1 in uIoo x₀ x -> g' x_1 != 0) :
    exists x' in uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x = ((x - x') ^ n / n ! *
      (g x - g x₀) / g' x') • iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' := by
  have hx₁ : min x₀ x < max x₀ x := by grind
  -- We apply the mean value theorem
  rcases exists_ratio_hasDerivAt_eq_ratio_slope (fun t => taylorWithinEval f n (uIcc x₀ x) t x)
      (fun t => ((n ! : Real)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (uIcc x₀ x) t) hx₁
      (continuousOn_taylorWithinEval (uniqueDiffOn_Icc hx₁) hf)
      (fun _ hy => taylorWithinEval_hasDerivAt_Ioo x hx₁ hy hf hf')
    g g' gcont gdiff with ⟨y, hy, h⟩
  use y, hy
  -- The rest is simplifications and trivial calculations
  grind [uIoo, smul_eq_mul, taylorWithinEval_self]

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/--
theorem `taylor_mean_remainder_lagrange` / 定理 `taylor_mean_remainder_lagrange`

English:
theorem taylor_mean_remainder_lagrange
  statement: {f : Real -> Real} {x x₀ : Real} {n : Nat} (hx : x₀ != x)
  proof: by
  have gcont : ContinuousOn (fun t : Real => (x - t) ^ (n + 1)) (uIcc x₀ x) := by fun_prop
  have xy_ne : forall y : Real, y in uIoo x₀ x -> (x - y) ^ n != 0 := by grind [uIoo, pow_ne_zero]
  have hg' : forall y : Real, y in uIoo x₀ x -> -(↑n + 1) * (x - y) ^ n != 0 := fun y hy =>
    mul_ne_zero

中文:
定理 taylor_mean_remainder_lagrange
  结论: {f : 实数 -> 实数} {x x₀ : 实数} {n : 自然数} (hx : x₀ != x)
  证明: by
  have gcont : ContinuousOn (fun t : Real => (x - t) ^ (n + 1)) (uIcc x₀ x) := by fun_prop
  have xy_ne : forall y : Real, y in uIoo x₀ x -> (x - y) ^ n != 0 := by grind [uIoo, pow_ne_zero]
  have hg' : forall y : Real, y in uIoo x₀ x -> -(↑n + 1) * (x - y) ^ n != 0 := fun y hy =>
    mul_ne_zero

Depends on / 依赖: ContinuousOn, Nat.cast_add_one_ne_zero, cast_add_one_ne_zero, fun_prop, mul_ne_zero, neg_ne_zero, neg_ne_zero.mpr, pow_ne_zero, xy_ne
-/
theorem taylor_mean_remainder_lagrange {f : Real -> Real} {x x₀ : Real} {n : Nat} (hx : x₀ != x)
    (hf : ContDiffOn Real n f (uIcc x₀ x))
    (hf' : DifferentiableOn Real (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)) :
    exists x' in uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1)! := by
  have gcont : ContinuousOn (fun t : Real => (x - t) ^ (n + 1)) (uIcc x₀ x) := by fun_prop
  have xy_ne : forall y : Real, y in uIoo x₀ x -> (x - y) ^ n != 0 := by grind [uIoo, pow_ne_zero]
  have hg' : forall y : Real, y in uIoo x₀ x -> -(↑n + 1) * (x - y) ^ n != 0 := fun y hy =>
    mul_ne_zero (neg_ne_zero.mpr (Nat.cast_add_one_ne_zero n)) (xy_ne y hy)
  -- We apply the general theorem with g(t) = (x - t)^(n+1)
  rcases taylor_mean_remainder hx hf hf' gcont (fun y _ => monomial_has_deriv_aux y x _) hg' with
    ⟨y, hy, h⟩
  use y, hy
  simp only [sub_self, zero_pow, Ne, Nat.succ_ne_zero, not_false_iff, zero_sub, mul_neg] at h
  rw [h]; rw [neg_div]; rw [← div_neg]; rw [neg_mul]; rw [neg_neg]
  simp [field, xy_ne y hy, Nat.factorial]

/--
lemma `taylor_mean_remainder_lagrange_iteratedDeriv` / 引理 `taylor_mean_remainder_lagrange_iteratedDeriv`

English:
lemma taylor_mean_remainder_lagrange_iteratedDeriv
  statement: {f : Real -> Real} {x x₀ : Real} {n : Nat} (hx : x₀ != x)
  proof: by
  have hu : UniqueDiffOn Real (uIcc x₀ x) := uniqueDiffOn_uIcc hx
  have hd : DifferentiableOn Real (iteratedDerivWithin n f (uIcc x₀ x)) (uIcc x₀ x) := by
    refine hf.differentiableOn_iteratedDerivWithin ?_ hu
    norm_cast
    simp
  obtain ⟨x', h1, h2⟩ := taylor_mean_remainder_lagrange hx hf

中文:
引理 taylor_mean_remainder_lagrange_iteratedDeriv
  结论: {f : 实数 -> 实数} {x x₀ : 实数} {n : 自然数} (hx : x₀ != x)
  证明: by
  have hu : UniqueDiffOn Real (uIcc x₀ x) := uniqueDiffOn_uIcc hx
  have hd : DifferentiableOn Real (iteratedDerivWithin n f (uIcc x₀ x)) (uIcc x₀ x) := by
    refine hf.differentiableOn_iteratedDerivWithin ?_ hu
    norm_cast
    simp
  obtain ⟨x', h1, h2⟩ := taylor_mean_remainder_lagrange hx hf

Depends on / 依赖: DifferentiableOn, Ioo_subset_Icc_self, UniqueDiffOn, differentiableOn_iteratedDerivWithin, hd.mono, hf.differentiableOn_iteratedDerivWithin, hf.of_succ, iteratedDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDeriv_eq_iteratedFDeriv, iteratedFDerivWithin_eq_iteratedFDeriv, le_of_lt, of_succ, taylor_mean_remainder_lagrange, uniqueDiffOn_uIcc
-/
lemma taylor_mean_remainder_lagrange_iteratedDeriv {f : Real -> Real} {x x₀ : Real} {n : Nat} (hx : x₀ != x)
    (hf : ContDiffOn Real (n + 1) f (uIcc x₀ x)) :
    exists x' in uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      iteratedDeriv (n + 1) f x' * (x - x₀) ^ (n + 1) / (n + 1)! := by
  have hu : UniqueDiffOn Real (uIcc x₀ x) := uniqueDiffOn_uIcc hx
  have hd : DifferentiableOn Real (iteratedDerivWithin n f (uIcc x₀ x)) (uIcc x₀ x) := by
    refine hf.differentiableOn_iteratedDerivWithin ?_ hu
    norm_cast
    simp
  obtain ⟨x', h1, h2⟩ := taylor_mean_remainder_lagrange hx hf.of_succ (hd.mono Ioo_subset_Icc_self)
  use x', h1
  rw [h2]; rw [iteratedDeriv_eq_iteratedFDeriv]; rw [iteratedDerivWithin_eq_iteratedFDerivWithin]; rw [iteratedFDerivWithin_eq_iteratedFDeriv hu _ ⟨le_of_lt h1.1]; rw [le_of_lt h1.2⟩]
  exact hf.contDiffAt (Icc_mem_nhds_iff.2 h1)

/--
theorem `taylor_mean_remainder_cauchy` / 定理 `taylor_mean_remainder_cauchy`

English:
theorem taylor_mean_remainder_cauchy
  statement: {f : Real -> Real} {x x₀ : Real} {n : Nat} (hx : x₀ != x)
  proof: by
  have gcont : ContinuousOn id (uIcc x₀ x) := by fun_prop
  have gdiff : forall x_1 : Real, x_1 in uIoo x₀ x -> HasDerivAt id ((fun _ : Real => (1 : Real)) x_1) x_1 :=
    fun _ _ => hasDerivAt_id _
  -- We apply the general theorem with g = id
  rcases taylor_mean_remainder hx hf hf' gcont gdiff

中文:
定理 taylor_mean_remainder_cauchy
  结论: {f : 实数 -> 实数} {x x₀ : 实数} {n : 自然数} (hx : x₀ != x)
  证明: by
  have gcont : ContinuousOn id (uIcc x₀ x) := by fun_prop
  have gdiff : forall x_1 : Real, x_1 in uIoo x₀ x -> HasDerivAt id ((fun _ : Real => (1 : Real)) x_1) x_1 :=
    fun _ _ => hasDerivAt_id _
  -- We apply the general theorem with g = id
  rcases taylor_mean_remainder hx hf hf' gcont gdiff

Depends on / 依赖: ContinuousOn, HasDerivAt, fun_prop, hasDerivAt_id
-/
theorem taylor_mean_remainder_cauchy {f : Real -> Real} {x x₀ : Real} {n : Nat} (hx : x₀ != x)
    (hf : ContDiffOn Real n f (uIcc x₀ x))
    (hf' : DifferentiableOn Real (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)) :
    exists x' in uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' * (x - x') ^ n / n ! * (x - x₀) := by
  have gcont : ContinuousOn id (uIcc x₀ x) := by fun_prop
  have gdiff : forall x_1 : Real, x_1 in uIoo x₀ x -> HasDerivAt id ((fun _ : Real => (1 : Real)) x_1) x_1 :=
    fun _ _ => hasDerivAt_id _
  -- We apply the general theorem with g = id
  rcases taylor_mean_remainder hx hf hf' gcont gdiff fun _ _ => by simp with ⟨y, hy, h⟩
  use y, hy
  rw [h]
  simp [field]

/--
theorem `taylor_mean_remainder_bound` / 定理 `taylor_mean_remainder_bound`

English:
theorem taylor_mean_remainder_bound
  statement: {f : Real -> E} {a b C x : Real} {n : Nat} (hab : a <= b)
  proof: by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · rw [Icc_self, mem_singleton_iff] at hx
    simp [hx]
  -- The nth iterated derivative is differentiable
  have hf' : DifferentiableOn Real (iteratedDerivWithin n f (Icc a b)) (Icc a b) :=
    hf.differentiableOn_iteratedDerivWithin (mod_cast n.lt_suc

中文:
定理 taylor_mean_remainder_bound
  结论: {f : 实数 -> E} {a b C x : 实数} {n : 自然数} (hab : a <= b)
  证明: by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · rw [Icc_self, mem_singleton_iff] at hx
    simp [hx]
  -- The nth iterated derivative is differentiable
  have hf' : DifferentiableOn Real (iteratedDerivWithin n f (Icc a b)) (Icc a b) :=
    hf.differentiableOn_iteratedDerivWithin (mod_cast n.lt_suc

Depends on / 依赖: Icc_self, eq_or_lt_of_le, mem_singleton_iff
-/
theorem taylor_mean_remainder_bound {f : Real -> E} {a b C x : Real} {n : Nat} (hab : a <= b)
    (hf : ContDiffOn Real (n + 1) f (Icc a b)) (hx : x in Icc a b)
    (hC : forall y in Icc a b, ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖ <= C) :
    ‖f x - taylorWithinEval f n (Icc a b) a x‖ <= C * (x - a) ^ (n + 1) / n ! := by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · rw [Icc_self, mem_singleton_iff] at hx
    simp [hx]
  -- The nth iterated derivative is differentiable
  have hf' : DifferentiableOn Real (iteratedDerivWithin n f (Icc a b)) (Icc a b) :=
    hf.differentiableOn_iteratedDerivWithin (mod_cast n.lt_succ_self)
      (uniqueDiffOn_Icc h)
  -- We can uniformly bound the derivative of the Taylor polynomial
  have h' : forall y in Ico a x,
      ‖((n ! : Real)⁻¹ * (x - y) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) y‖ <=
        (n ! : Real)⁻¹ * |x - a| ^ n * C := by
    rintro y ⟨hay, hyx⟩
    rw [norm_smul]; rw [Real.norm_eq_abs]
    gcongr
    · rw [abs_mul, abs_pow, abs_inv, Nat.abs_cast]
      gcongr
    -- Estimate the iterated derivative by `C`
    · exact hC y ⟨hay, hyx.le.trans hx.2⟩
  -- Apply the mean value theorem for vector-valued functions:
  have A : forall t in Icc a x, HasDerivWithinAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((↑n !)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) (Icc a x) t := by
    intro t ht
    have I : Icc a x subseteq Icc a b := Icc_subset_Icc_right hx.2
    exact (hasDerivWithinAt_taylorWithinEval_at_Icc x h (I ht) hf.of_succ hf').mono I
  have := norm_image_sub_le_of_norm_deriv_le_segment' A h' x (right_mem_Icc.2 hx.1)
  simp only [taylorWithinEval_self] at this
  refine this.trans_eq ?_
  -- The rest is a trivial calculation
  rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
  ring

/--
theorem `exists_taylor_mean_remainder_bound` / 定理 `exists_taylor_mean_remainder_bound`

English:
theorem exists_taylor_mean_remainder_bound
  statement: {f : Real -> E} {a b : Real} {n : Nat} (hab : a <= b)
  proof: by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · refine ⟨0, fun x hx => ?_⟩
    have : x = a := by simpa [← le_antisymm_iff] using hx
    simp [← this]
  -- We estimate by the supremum of the norm of the iterated derivative
  let g : Real -> Real := fun y => ‖iteratedDerivWithin (n + 1) f (Icc a b)

中文:
定理 存在_taylor_mean_remainder_bound
  结论: {f : 实数 -> E} {a b : 实数} {n : 自然数} (hab : a <= b)
  证明: by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · refine ⟨0, fun x hx => ?_⟩
    have : x = a := by simpa [← le_antisymm_iff] using hx
    simp [← this]
  -- We estimate by the supremum of the norm of the iterated derivative
  let g : Real -> Real := fun y => ‖iteratedDerivWithin (n + 1) f (Icc a b)

Depends on / 依赖: eq_or_lt_of_le, le_antisymm_iff
-/
theorem exists_taylor_mean_remainder_bound {f : Real -> E} {a b : Real} {n : Nat} (hab : a <= b)
    (hf : ContDiffOn Real (n + 1) f (Icc a b)) :
    exists C, forall x in Icc a b, ‖f x - taylorWithinEval f n (Icc a b) a x‖ <= C * (x - a) ^ (n + 1) := by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · refine ⟨0, fun x hx => ?_⟩
    have : x = a := by simpa [← le_antisymm_iff] using hx
    simp [← this]
  -- We estimate by the supremum of the norm of the iterated derivative
  let g : Real -> Real := fun y => ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖
  use SupSet.sSup (g '' Icc a b) / (n !)
  intro x hx
  rw [div_mul_eq_mul_div₀]
  refine taylor_mean_remainder_bound hab hf hx fun y => ?_
  exact (hf.continuousOn_iteratedDerivWithin rfl.le <| uniqueDiffOn_Icc h).norm.le_sSup_image_Icc

/--
theorem `taylor_integral_remainder_aux` / 定理 `taylor_integral_remainder_aux`

English:
theorem taylor_integral_remainder_aux
  statement: [NormedAddCommGroup F] [NormedSpace Real F]
  proof: by
  rcases eq_or_ne x₀ x with rfl | this
  · simp
  induction n with
  | zero =>
    simp only [taylor_within_zero_eval, pow_zero, Nat.factorial_zero, Nat.cast_one, ne_eq,
      one_ne_zero, not_false_eq_true, div_self, zero_add, iteratedDerivWithin_one, one_smul]
    simp only [nonpos_iff_eq_zero,

中文:
定理 taylor_integral_remainder_aux
  结论: [赋范交换加群 F] [赋范空间 实数 F]
  证明: by
  rcases eq_or_ne x₀ x with rfl | this
  · simp
  induction n with
  | zero =>
    simp only [taylor_within_zero_eval, pow_zero, Nat.factorial_zero, Nat.cast_one, ne_eq,
      one_ne_zero, not_false_eq_true, div_self, zero_add, iteratedDerivWithin_one, one_smul]
    simp only [nonpos_iff_eq_zero,
-/
theorem taylor_integral_remainder_aux [NormedAddCommGroup F] [NormedSpace Real F]
    {f : Real -> F} {x x₀ : Real} {n : Nat}
    (hf : forall k <= n, let u := fun t => (x - t) ^ k / k !;
      let v := fun t => iteratedDerivWithin k f [[x₀, x]] t;
      ∫ (t : Real) in x₀..x, u t • deriv v t = u x • v x - u x₀ • v x₀ -
      ∫ (t : Real) in x₀..x, deriv u t • v t) :
    f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      ∫ t in x₀..x, ((x - t) ^ n / n !) • iteratedDerivWithin (n + 1) f (uIcc x₀ x) t := by
  rcases eq_or_ne x₀ x with rfl | this
  · simp
  induction n with
  | zero =>
    simp only [taylor_within_zero_eval, pow_zero, Nat.factorial_zero, Nat.cast_one, ne_eq,
      one_ne_zero, not_false_eq_true, div_self, zero_add, iteratedDerivWithin_one, one_smul]
    simp only [nonpos_iff_eq_zero, sub_self, deriv_div_const, forall_eq, pow_zero,
      Nat.factorial_zero, Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self,
      iteratedDerivWithin_zero, one_smul, deriv_const', div_one, zero_smul,
      intervalIntegral.integral_zero, sub_zero] at hf
    rw [← hf]
    refine intervalIntegral.integral_congr_uIoo fun _ ⟨h1, h2⟩ => ?_
    rw [← derivWithin_of_mem_nhds <| Icc_mem_nhds h1 h2]
    rfl
  | succ n ih =>
    specialize ih (by grind)
    simp only [taylorWithinEval_succ, mul_inv_rev]
    rw [sub_add_eq_sub_sub]; rw [ih]
    simp only [Nat.factorial, Nat.succ_eq_add_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have := hf (n + 1) (by rfl)
    convert! this.symm using 1
    · simp only [sub_self, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow, zero_div, zero_smul, zero_sub, deriv_div_const, Nat.factorial]
      apply fun (a b c d : F) (_ : b = c) (_ : a = -d) => show a - b = -c - d by grind
      · grind
      · rw [← intervalIntegral.integral_neg]
        congr
        ext t
        rw [deriv_fun_pow (by fun_prop)]; rw [deriv_const_sub]; rw [deriv_id'']; rw [← neg_smul]
        congr
        field_simp
        grind
    · refine intervalIntegral.integral_congr_uIoo fun _ ⟨h1, h2⟩ => ?_
      rw [iteratedDerivWithin_succ]
      congr
      · rw [Nat.factorial, Nat.cast_mul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
      · rw [← derivWithin_of_mem_nhds <| Icc_mem_nhds h1 h2]
        rfl

/--
theorem `taylor_integral_remainder_of_absolutelyContinuous` / 定理 `taylor_integral_remainder_of_absolutelyContinuous`

English:
theorem taylor_integral_remainder_of_absolutelyContinuous
  statement: {f : Real -> Real} {x x₀ : Real} {n : Nat}
  proof: by
  rcases eq_or_ne x₀ x with rfl | this
  · simp
  apply taylor_integral_remainder_aux
  intro k hk
  apply AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
  · apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  · rcases hk.eq_or_lt with rfl | hk
    · exact hf₂
    repla

中文:
定理 taylor_integral_remainder_of_absolutelyContinuous
  结论: {f : 实数 -> 实数} {x x₀ : 实数} {n : 自然数}
  证明: by
  rcases eq_or_ne x₀ x with rfl | this
  · simp
  apply taylor_integral_remainder_aux
  intro k hk
  apply AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
  · apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  · rcases hk.eq_or_lt with rfl | hk
    · exact hf₂
    repla

Depends on / 依赖: AbsolutelyContinuousOnInterval, AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul, ContDiffOn, ContDiffOn.absolutelyContinuousOnInterval, absolutelyContinuousOnInterval, contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin, eq_or_lt, eq_or_ne, fun_prop, hk.eq_or_lt, integral_mul_deriv_eq_deriv_mul, k.succ, of_le, replace, taylor_integral_remainder_aux, uniqueDiffOn_uIcc
-/
theorem taylor_integral_remainder_of_absolutelyContinuous {f : Real -> Real} {x x₀ : Real} {n : Nat}
    (hf₁ : ContDiffOn Real n f (uIcc x₀ x))
    (hf₂ : AbsolutelyContinuousOnInterval (iteratedDerivWithin n f (uIcc x₀ x)) x₀ x) :
    f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      ∫ t in x₀..x, ((x - t) ^ n / n !) * iteratedDerivWithin (n + 1) f (uIcc x₀ x) t := by
  rcases eq_or_ne x₀ x with rfl | this
  · simp
  apply taylor_integral_remainder_aux
  intro k hk
  apply AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
  · apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  · rcases hk.eq_or_lt with rfl | hk
    · exact hf₂
    replace hf₁ := hf₁.of_le (m := k.succ) (by norm_cast)
    grind [ContDiffOn.absolutelyContinuousOnInterval, uniqueDiffOn_uIcc,
      contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin]

/--
theorem `taylor_integral_remainder` / 定理 `taylor_integral_remainder`

English:
theorem taylor_integral_remainder
  statement: [NormedAddCommGroup F] [NormedSpace Real F]
  proof: by
  rcases eq_or_ne x₀ x with rfl | this
  · simp
  have : UniqueDiffOn Real [[x₀, x]] := uniqueDiffOn_uIcc this
  apply taylor_integral_remainder_aux
  intro k hk
  apply intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (u := fun t => (x - t) ^ k / k !) (v := fun t => iteratedD

中文:
定理 taylor_integral_remainder
  结论: [赋范交换加群 F] [赋范空间 实数 F]
  证明: by
  rcases eq_or_ne x₀ x with rfl | this
  · simp
  have : UniqueDiffOn Real [[x₀, x]] := uniqueDiffOn_uIcc this
  apply taylor_integral_remainder_aux
  intro k hk
  apply intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (u := fun t => (x - t) ^ k / k !) (v := fun t => iteratedD

Depends on / 依赖: DifferentiableAt, DifferentiableAt.hasDerivAt, DifferentiableOn, DifferentiableOn.hasDerivAt, UniqueDiffOn, continuousOn_iteratedDerivWithin, eq_or_ne, fun_prop, hasDerivAt, hf.continuousOn_iteratedDerivWithin, integral_smul_deriv_eq_deriv_smul_of_hasDerivAt, intervalIntegral, intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt, iteratedDerivWithin, taylor_integral_remainder_aux, uniqueDiffOn_uIcc
-/
theorem taylor_integral_remainder [NormedAddCommGroup F] [NormedSpace Real F]
    [CompleteSpace F] {f : Real -> F} {x x₀ : Real} {n : Nat}
    (hf : ContDiffOn Real (n + 1 : Nat) f (uIcc x₀ x)) :
    f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      ∫ t in x₀..x, ((x - t) ^ n / n !) • iteratedDerivWithin (n + 1) f (uIcc x₀ x) t := by
  rcases eq_or_ne x₀ x with rfl | this
  · simp
  have : UniqueDiffOn Real [[x₀, x]] := uniqueDiffOn_uIcc this
  apply taylor_integral_remainder_aux
  intro k hk
  apply intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (u := fun t => (x - t) ^ k / k !) (v := fun t => iteratedDerivWithin k f (uIcc x₀ x) t)
  · fun_prop
  · exact hf.continuousOn_iteratedDerivWithin (by norm_cast; omega) this
  · intro t ht
    apply DifferentiableAt.hasDerivAt
    fun_prop
  · intro t ht
    refine DifferentiableOn.hasDerivAt (s := uIoo x₀ x) ?_ (by grind [Ioo_mem_nhds, uIoo])
    exact hf.differentiableOn_iteratedDerivWithin (by norm_cast; omega) this
.mono (by grind [uIoo, uIcc])
  · apply ContinuousOn.intervalIntegrable
    fun_prop
  · apply IntervalIntegrable.congr_ae (f := iteratedDerivWithin (k + 1) f [[x₀, x]])
.intervalIntegrable · exact hf.continuousOn_iteratedDerivWithin (by norm_cast; omega) this
    · rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (by measurability)]
      filter_upwards [MeasureTheory.volume.ae_ne x₀, MeasureTheory.volume.ae_ne x] with _ _ _ _
      rw [iteratedDerivWithin_succ]
      grind [derivWithin_of_mem_nhds, Icc_mem_nhds, uIcc]
