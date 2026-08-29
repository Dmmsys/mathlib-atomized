/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.Positivity

/-!
# Hasse derivative of polynomials

The `k`th Hasse derivative of a polynomial `∑ a_i X^i` is `∑ (i.choose k) a_i X^(i-k)`.
It is a variant of the usual derivative, and satisfies `k! * (hasseDeriv k f) = derivative^[k] f`.
The main benefit is that is gives an atomic way of talking about expressions such as
`(derivative^[k] f).eval r / k!`, that occur in Taylor expansions, for example.

## Main declarations

In the following, we write `D k` for the `k`-th Hasse derivative `hasse_deriv k`.

* `Polynomial.hasseDeriv`: the `k`-th Hasse derivative of a polynomial
* `Polynomial.hasseDeriv_zero`: the `0`th Hasse derivative is the identity
* `Polynomial.hasseDeriv_one`: the `1`st Hasse derivative is the usual derivative
* `Polynomial.factorial_smul_hasseDeriv`: the identity `k! • (D k f) = derivative^[k] f`
* `Polynomial.hasseDeriv_comp`: the identity `(D k).comp (D l) = (k+l).choose k • D (k+l)`
* `Polynomial.hasseDeriv_mul`:
  the "Leibniz rule" `D k (f * g) = ∑ ij ∈ antidiagonal k, D ij.1 f * D ij.2 g`

For the identity principle, see `Polynomial.eq_zero_of_hasseDeriv_eq_zero`
in `Mathlib/Algebra/Polynomial/Taylor.lean`.

## Reference

https://math.fontein.de/2009/08/12/the-hasse-derivative/

-/

@[expose] public section


noncomputable section

namespace Polynomial

open Nat Polynomial

open Function

variable {R : Type*} [Semiring R] (k : Nat) (f : R[X])

/--
Definition of `hasseDeriv` / `hasseDeriv` 的定义

English:
definition hasseDeriv
  signature: (k : Nat)
  body: lsum fun i => monomial (i - k) ∘ₗ DistribSMul.toLinearMap R R (i.choose k)

中文:
定义 hasseDeriv
  签名: (k : 自然数)
  定义体: lsum fun i => monomial (i - k) ∘ₗ DistribSMul.toLinearMap R R (i.choose k)

Depends on / 依赖: DistribSMul, DistribSMul.toLinearMap, i.choose, monomial, toLinearMap
-/
def hasseDeriv (k : Nat) : R[X] ->ₗ[R] R[X] :=
  lsum fun i => monomial (i - k) ∘ₗ DistribSMul.toLinearMap R R (i.choose k)

/--
theorem `hasseDeriv_apply` / 定理 `hasseDeriv_apply`

English:
theorem hasseDeriv_apply
  proof: by
  dsimp [hasseDeriv]
  simp

中文:
定理 hasseDeriv_apply
  证明: by
  dsimp [hasseDeriv]
  simp

Depends on / 依赖: hasseDeriv
-/
theorem hasseDeriv_apply :
    hasseDeriv k f = f.sum fun i r => monomial (i - k) (↑(i.choose k) * r) := by
  dsimp [hasseDeriv]
  simp

/--
theorem `hasseDeriv_coeff` / 定理 `hasseDeriv_coeff`

English:
theorem hasseDeriv_coeff
  given: (n : Nat)
  proof: by
  rw [hasseDeriv_apply]; rw [coeff_sum]; rw [sum_def]; rw [Finset.sum_eq_single (n + k)]; rw [coeff_monomial]
  · simp
  · #adaptation_note
    /-- Prior to nightly-2025-08-14, this was working as
    `grind [coeff_monomial, Nat.choose_eq_zero_of_lt, Nat.cast_zero, zero_mul]` -/
    intro i _hi h

中文:
定理 hasseDeriv_coeff
  条件: (n : 自然数)
  证明: by
  rw [hasseDeriv_apply]; rw [coeff_sum]; rw [sum_def]; rw [Finset.sum_eq_single (n + k)]; rw [coeff_monomial]
  · simp
  · #adaptation_note
    /-- Prior to nightly-2025-08-14, this was working as
    `grind [coeff_monomial, Nat.choose_eq_zero_of_lt, Nat.cast_zero, zero_mul]` -/
    intro i _hi h

Depends on / 依赖: Finset, Finset.sum_eq_single, adaptation_note, coeff_monomial, coeff_sum, hasseDeriv_apply, sum_def, sum_eq_single
-/
theorem hasseDeriv_coeff (n : Nat) :
    (hasseDeriv k f).coeff n = (n + k).choose k * f.coeff (n + k) := by
  rw [hasseDeriv_apply]; rw [coeff_sum]; rw [sum_def]; rw [Finset.sum_eq_single (n + k)]; rw [coeff_monomial]
  · simp
  · #adaptation_note
    /-- Prior to nightly-2025-08-14, this was working as
    `grind [coeff_monomial, Nat.choose_eq_zero_of_lt, Nat.cast_zero, zero_mul]` -/
    intro i _hi hink
    rw [coeff_monomial]
    by_cases hik : i < k
    · simp only [Nat.choose_eq_zero_of_lt hik, ite_self, Nat.cast_zero, zero_mul]
    · grind
  · intro h
    simp only [notMem_support_iff.mp h, monomial_zero_right, mul_zero, coeff_zero]

/--
theorem `hasseDeriv_zero'` / 定理 `hasseDeriv_zero'`

English:
theorem hasseDeriv_zero'
  statement: hasseDeriv 0 f = f
  proof: by
  simp only [hasseDeriv_apply, Nat.sub_zero, choose_zero_right, cast_one, one_mul, sum_monomial_eq]

@[simp]

中文:
定理 hasseDeriv_zero'
  结论: hasseDeriv 0 f = f
  证明: by
  simp only [hasseDeriv_apply, Nat.sub_zero, choose_zero_right, cast_one, one_mul, sum_monomial_eq]

@[simp]

Depends on / 依赖: Nat.sub_zero, cast_one, choose_zero_right, hasseDeriv_apply, one_mul, sub_zero, sum_monomial_eq
-/
theorem hasseDeriv_zero' : hasseDeriv 0 f = f := by
  simp only [hasseDeriv_apply, Nat.sub_zero, choose_zero_right, cast_one, one_mul, sum_monomial_eq]

@[simp]
/--
theorem `hasseDeriv_zero` / 定理 `hasseDeriv_zero`

English:
theorem hasseDeriv_zero
  statement: @hasseDeriv R _ 0 = LinearMap.id
  proof: LinearMap.ext hasseDeriv_zero'

中文:
定理 hasseDeriv_zero
  结论: @hasseDeriv R _ 0 = LinearMap.id
  证明: LinearMap.ext hasseDeriv_zero'

Depends on / 依赖: LinearMap, LinearMap.ext, hasseDeriv_zero
-/
theorem hasseDeriv_zero : @hasseDeriv R _ 0 = LinearMap.id :=
LinearMap.ext hasseDeriv_zero'

/--
theorem `hasseDeriv_eq_zero_of_lt_natDegree` / 定理 `hasseDeriv_eq_zero_of_lt_natDegree`

English:
theorem hasseDeriv_eq_zero_of_lt_natDegree
  given: (p : R[X]) (n : Nat) (h : p.natDegree < n)
  proof: by
  rw [hasseDeriv_apply]; rw [sum_def]
  refine Finset.sum_eq_zero fun x hx => ?_
  simp [Nat.choose_eq_zero_of_lt ((le_natDegree_of_mem_supp _ hx).trans_lt h)]

中文:
定理 hasseDeriv_eq_zero_of_lt_natDegree
  条件: (p : R[X]) (n : 自然数) (h : p.natDegree < n)
  证明: by
  rw [hasseDeriv_apply]; rw [sum_def]
  refine Finset.sum_eq_zero fun x hx => ?_
  simp [Nat.choose_eq_zero_of_lt ((le_natDegree_of_mem_supp _ hx).trans_lt h)]

Depends on / 依赖: Finset, Finset.sum_eq_zero, Nat.choose_eq_zero_of_lt, choose_eq_zero_of_lt, hasseDeriv_apply, le_natDegree_of_mem_supp, sum_def, sum_eq_zero, trans_lt
-/
theorem hasseDeriv_eq_zero_of_lt_natDegree (p : R[X]) (n : Nat) (h : p.natDegree < n) :
    hasseDeriv n p = 0 := by
  rw [hasseDeriv_apply]; rw [sum_def]
  refine Finset.sum_eq_zero fun x hx => ?_
  simp [Nat.choose_eq_zero_of_lt ((le_natDegree_of_mem_supp _ hx).trans_lt h)]

/--
theorem `hasseDeriv_one'` / 定理 `hasseDeriv_one'`

English:
theorem hasseDeriv_one'
  statement: hasseDeriv 1 f = derivative f
  proof: by
  simp only [hasseDeriv_apply, derivative_apply, ← C_mul_X_pow_eq_monomial, Nat.choose_one_right,
    (Nat.cast_commute _ _).eq]

@[simp]

中文:
定理 hasseDeriv_one'
  结论: hasseDeriv 1 f = derivative f
  证明: by
  simp only [hasseDeriv_apply, derivative_apply, ← C_mul_X_pow_eq_monomial, Nat.choose_one_right,
    (Nat.cast_commute _ _).eq]

@[simp]

Depends on / 依赖: C_mul_X_pow_eq_monomial, Nat.cast_commute, Nat.choose_one_right, cast_commute, choose_one_right, derivative_apply, hasseDeriv_apply
-/
theorem hasseDeriv_one' : hasseDeriv 1 f = derivative f := by
  simp only [hasseDeriv_apply, derivative_apply, ← C_mul_X_pow_eq_monomial, Nat.choose_one_right,
    (Nat.cast_commute _ _).eq]

@[simp]
/--
theorem `hasseDeriv_one` / 定理 `hasseDeriv_one`

English:
theorem hasseDeriv_one
  statement: @hasseDeriv R _ 1 = derivative
  proof: LinearMap.ext hasseDeriv_one'

@[simp]

中文:
定理 hasseDeriv_one
  结论: @hasseDeriv R _ 1 = derivative
  证明: LinearMap.ext hasseDeriv_one'

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, hasseDeriv_one
-/
theorem hasseDeriv_one : @hasseDeriv R _ 1 = derivative :=
LinearMap.ext hasseDeriv_one'

@[simp]
/--
theorem `hasseDeriv_monomial` / 定理 `hasseDeriv_monomial`

English:
theorem hasseDeriv_monomial
  given: (n : Nat) (r : R)
  proof: by
  ext i
  simp only [hasseDeriv_coeff, coeff_monomial]
  by_cases hnik : n = i + k
  · grind
  · rw [if_neg hnik, mul_zero]
    by_cases! hkn : k <= n
    · rw [← tsub_eq_iff_eq_add_of_le hkn] at hnik
      rw [if_neg hnik]
    · rw [Nat.choose_eq_zero_of_lt hkn, Nat.cast_zero, zero_mul, ite_self

中文:
定理 hasseDeriv_monomial
  条件: (n : 自然数) (r : R)
  证明: by
  ext i
  simp only [hasseDeriv_coeff, coeff_monomial]
  by_cases hnik : n = i + k
  · grind
  · rw [if_neg hnik, mul_zero]
    by_cases! hkn : k <= n
    · rw [← tsub_eq_iff_eq_add_of_le hkn] at hnik
      rw [if_neg hnik]
    · rw [Nat.choose_eq_zero_of_lt hkn, Nat.cast_zero, zero_mul, ite_self

Depends on / 依赖: Nat.cast_zero, Nat.choose_eq_zero_of_lt, cast_zero, choose_eq_zero_of_lt, coeff_monomial, hasseDeriv_coeff, if_neg, ite_self, mul_zero, tsub_eq_iff_eq_add_of_le, zero_mul
-/
theorem hasseDeriv_monomial (n : Nat) (r : R) :
    hasseDeriv k (monomial n r) = monomial (n - k) (↑(n.choose k) * r) := by
  ext i
  simp only [hasseDeriv_coeff, coeff_monomial]
  by_cases hnik : n = i + k
  · grind
  · rw [if_neg hnik, mul_zero]
    by_cases! hkn : k <= n
    · rw [← tsub_eq_iff_eq_add_of_le hkn] at hnik
      rw [if_neg hnik]
    · rw [Nat.choose_eq_zero_of_lt hkn, Nat.cast_zero, zero_mul, ite_self]

/--
theorem `hasseDeriv_C` / 定理 `hasseDeriv_C`

English:
theorem hasseDeriv_C
  given: (r : R) (hk : 0 < k)
  statement: hasseDeriv k (C r) = 0
  proof: by
  rw [← monomial_zero_left]; rw [hasseDeriv_monomial]; rw [Nat.choose_eq_zero_of_lt hk]; rw [Nat.cast_zero]; rw [zero_mul]; rw [monomial_zero_right]

中文:
定理 hasseDeriv_C
  条件: (r : R) (hk : 0 < k)
  结论: hasseDeriv k (C r) = 0
  证明: by
  rw [← monomial_zero_left]; rw [hasseDeriv_monomial]; rw [Nat.choose_eq_zero_of_lt hk]; rw [Nat.cast_zero]; rw [zero_mul]; rw [monomial_zero_right]

Depends on / 依赖: Nat.cast_zero, Nat.choose_eq_zero_of_lt, cast_zero, choose_eq_zero_of_lt, hasseDeriv_monomial, monomial_zero_left, monomial_zero_right, zero_mul
-/
theorem hasseDeriv_C (r : R) (hk : 0 < k) : hasseDeriv k (C r) = 0 := by
  rw [← monomial_zero_left]; rw [hasseDeriv_monomial]; rw [Nat.choose_eq_zero_of_lt hk]; rw [Nat.cast_zero]; rw [zero_mul]; rw [monomial_zero_right]

/--
theorem `hasseDeriv_apply_one` / 定理 `hasseDeriv_apply_one`

English:
theorem hasseDeriv_apply_one
  given: (hk : 0 < k)
  statement: hasseDeriv k (1 : R[X]) = 0
  proof: by
  rw [← C_1]; rw [hasseDeriv_C k _ hk]

中文:
定理 hasseDeriv_apply_one
  条件: (hk : 0 < k)
  结论: hasseDeriv k (1 : R[X]) = 0
  证明: by
  rw [← C_1]; rw [hasseDeriv_C k _ hk]

Depends on / 依赖: hasseDeriv_C
-/
theorem hasseDeriv_apply_one (hk : 0 < k) : hasseDeriv k (1 : R[X]) = 0 := by
  rw [← C_1]; rw [hasseDeriv_C k _ hk]

/--
theorem `hasseDeriv_X` / 定理 `hasseDeriv_X`

English:
theorem hasseDeriv_X
  given: (hk : 1 < k)
  statement: hasseDeriv k (X : R[X]) = 0
  proof: by
  rw [← monomial_one_one_eq_X]; rw [hasseDeriv_monomial]; rw [Nat.choose_eq_zero_of_lt hk]; rw [Nat.cast_zero]; rw [zero_mul]; rw [monomial_zero_right]

中文:
定理 hasseDeriv_X
  条件: (hk : 1 < k)
  结论: hasseDeriv k (X : R[X]) = 0
  证明: by
  rw [← monomial_one_one_eq_X]; rw [hasseDeriv_monomial]; rw [Nat.choose_eq_zero_of_lt hk]; rw [Nat.cast_zero]; rw [zero_mul]; rw [monomial_zero_right]

Depends on / 依赖: Nat.cast_zero, Nat.choose_eq_zero_of_lt, cast_zero, choose_eq_zero_of_lt, hasseDeriv_monomial, monomial_one_one_eq_X, monomial_zero_right, zero_mul
-/
theorem hasseDeriv_X (hk : 1 < k) : hasseDeriv k (X : R[X]) = 0 := by
  rw [← monomial_one_one_eq_X]; rw [hasseDeriv_monomial]; rw [Nat.choose_eq_zero_of_lt hk]; rw [Nat.cast_zero]; rw [zero_mul]; rw [monomial_zero_right]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `factorial_smul_hasseDeriv` / 定理 `factorial_smul_hasseDeriv`

English:
theorem factorial_smul_hasseDeriv
  statement: ⇑(k ! • @hasseDeriv R _ k) = (@derivative R _)^[k]
  proof: by
  induction k with
  | zero => rw [hasseDeriv_zero, factorial_zero, iterate_zero, one_smul, LinearMap.id_coe]
  | succ k ih => ?_
  ext f n : 2
  rw [iterate_succ_apply']; rw [← ih]
  simp only [LinearMap.smul_apply, coeff_smul, LinearMap.map_smul_of_tower, coeff_derivative,
    hasseDeriv_coeff,

中文:
定理 factorial_smul_hasseDeriv
  结论: ⇑(k ! • @hasseDeriv R _ k) = (@derivative R _)^[k]
  证明: by
  induction k with
  | zero => rw [hasseDeriv_zero, factorial_zero, iterate_zero, one_smul, LinearMap.id_coe]
  | succ k ih => ?_
  ext f n : 2
  rw [iterate_succ_apply']; rw [← ih]
  simp only [LinearMap.smul_apply, coeff_smul, LinearMap.map_smul_of_tower, coeff_derivative,
    hasseDeriv_coeff,

Depends on / 依赖: LinearMap, LinearMap.id_coe, LinearMap.map_smul_of_tower, LinearMap.smul_apply, add_assoc, add_right_comm, cast_commute, cast_succ, choose_symm_add, coeff_derivative, coeff_smul, f.coeff, factorial_succ, factorial_zero, hasseDeriv_coeff, hasseDeriv_zero, id_coe, iterate_succ_apply, iterate_zero, map_smul_of_tower
-/
theorem factorial_smul_hasseDeriv : ⇑(k ! • @hasseDeriv R _ k) = (@derivative R _)^[k] := by
  induction k with
  | zero => rw [hasseDeriv_zero, factorial_zero, iterate_zero, one_smul, LinearMap.id_coe]
  | succ k ih => ?_
  ext f n : 2
  rw [iterate_succ_apply']; rw [← ih]
  simp only [LinearMap.smul_apply, coeff_smul, LinearMap.map_smul_of_tower, coeff_derivative,
    hasseDeriv_coeff, ← @choose_symm_add _ k]
  simp only [nsmul_eq_mul, factorial_succ, mul_assoc, succ_eq_add_one, ← add_assoc,
    add_right_comm n 1 k, ← cast_succ]
  rw [← (cast_commute (n + 1) (f.coeff (n + k + 1))).eq]
  simp only [← mul_assoc]
  norm_cast
  congr 2
  rw [mul_comm (k + 1) _]; rw [mul_assoc]; rw [mul_assoc]
  congr 1
  have : n + k + 1 = n + (k + 1) := by apply add_assoc
  rw [← choose_symm_of_eq_add this]; rw [choose_succ_right_eq]; rw [mul_comm]
  congr
  rw [add_assoc]; rw [add_tsub_cancel_left]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasseDeriv_comp` / 定理 `hasseDeriv_comp`

English:
theorem hasseDeriv_comp
  given: (k l : Nat)
  proof: by
  ext i : 2
  simp only [LinearMap.smul_apply, comp_apply, LinearMap.coe_comp, smul_monomial, hasseDeriv_apply,
    mul_one, monomial_eq_zero_iff, sum_monomial_index, mul_zero, ←
    tsub_add_eq_tsub_tsub, add_comm l k]
  rw_mod_cast [nsmul_eq_mul]
  rw [← Nat.cast_mul]
  congr 2
  by_cases! hikl

中文:
定理 hasseDeriv_comp
  条件: (k l : 自然数)
  证明: by
  ext i : 2
  simp only [LinearMap.smul_apply, comp_apply, LinearMap.coe_comp, smul_monomial, hasseDeriv_apply,
    mul_one, monomial_eq_zero_iff, sum_monomial_index, mul_zero, ←
    tsub_add_eq_tsub_tsub, add_comm l k]
  rw_mod_cast [nsmul_eq_mul]
  rw [← Nat.cast_mul]
  congr 2
  by_cases! hikl

Depends on / 依赖: LinearMap, LinearMap.coe_comp, LinearMap.smul_apply, Nat.cast_mul, add_comm, cast_inj, cast_mul, choose_eq_zero_of_lt, coe_comp, comp_apply, hasseDeriv_apply, monomial_eq_zero_iff, mul_one, mul_zero, nsmul_eq_mul, rw_mod_cast, smul_apply, smul_monomial, sum_monomial_index, tsub_add_eq_tsub_tsub
-/
theorem hasseDeriv_comp (k l : Nat) :
    (@hasseDeriv R _ k).comp (hasseDeriv l) = (k + l).choose k • hasseDeriv (k + l) := by
  ext i : 2
  simp only [LinearMap.smul_apply, comp_apply, LinearMap.coe_comp, smul_monomial, hasseDeriv_apply,
    mul_one, monomial_eq_zero_iff, sum_monomial_index, mul_zero, ←
    tsub_add_eq_tsub_tsub, add_comm l k]
  rw_mod_cast [nsmul_eq_mul]
  rw [← Nat.cast_mul]
  congr 2
  by_cases! hikl : i < k + l
  · rw [choose_eq_zero_of_lt hikl, mul_zero]
    by_cases! hil : i < l
    · rw [choose_eq_zero_of_lt hil, mul_zero]
    · rw [← tsub_lt_iff_right hil] at hikl
      rw [choose_eq_zero_of_lt hikl]; rw [zero_mul]
  apply @cast_injective Rat
  have h1 : l <= i := le_of_add_le_right hikl
  have h2 : k <= i - l := le_tsub_of_add_le_right hikl
  have h3 : k <= k + l := le_self_add
  push_cast
  rw [cast_choose Rat h1]; rw [cast_choose Rat h2]; rw [cast_choose Rat h3]; rw [cast_choose Rat hikl]
  rw [show i - (k + l) = i - l - k by rw [add_comm]; apply tsub_add_eq_tsub_tsub]
  simp only [add_tsub_cancel_left]
  field

/--
theorem `natDegree_hasseDeriv_le` / 定理 `natDegree_hasseDeriv_le`

English:
theorem natDegree_hasseDeriv_le
  given: (p : R[X]) (n : Nat)
  proof: by
  classical
    rw [hasseDeriv_apply]; rw [sum_def]
    refine (natDegree_sum_le _ _).trans ?_
    simp_rw [Function.comp, natDegree_monomial]
    rw [Finset.fold_ite]; rw [Finset.fold_const]
    · simp only [ite_self, max_eq_right, zero_le, Finset.fold_max_le, true_and, and_imp,
        tsub_le_

中文:
定理 natDegree_hasseDeriv_le
  条件: (p : R[X]) (n : 自然数)
  证明: by
  classical
    rw [hasseDeriv_apply]; rw [sum_def]
    refine (natDegree_sum_le _ _).trans ?_
    simp_rw [Function.comp, natDegree_monomial]
    rw [Finset.fold_ite]; rw [Finset.fold_const]
    · simp only [ite_self, max_eq_right, zero_le, Finset.fold_max_le, true_and, and_imp,
        tsub_le_

Depends on / 依赖: Finset, Finset.fold_const, Finset.fold_ite, Finset.fold_max_le, Finset.mem_filter, Function, Function.comp, and_imp, classical, fold_const, fold_ite, fold_max_le, hasseDeriv_apply, ite_self, le_natDegree_of_ne_zero, max_eq_right, mem_filter, mem_support_iff, natDegree, natDegree_monomial
-/
theorem natDegree_hasseDeriv_le (p : R[X]) (n : Nat) :
    natDegree (hasseDeriv n p) <= natDegree p - n := by
  classical
    rw [hasseDeriv_apply]; rw [sum_def]
    refine (natDegree_sum_le _ _).trans ?_
    simp_rw [Function.comp, natDegree_monomial]
    rw [Finset.fold_ite]; rw [Finset.fold_const]
    · simp only [ite_self, max_eq_right, zero_le, Finset.fold_max_le, true_and, and_imp,
        tsub_le_iff_right, mem_support_iff, Ne, Finset.mem_filter]
      intro x hx hx'
      have hxp : x <= p.natDegree := le_natDegree_of_ne_zero hx
      grind
    · simp

/--
theorem `hasseDeriv_natDegree_eq_C` / 定理 `hasseDeriv_natDegree_eq_C`

English:
theorem hasseDeriv_natDegree_eq_C
  statement: f.hasseDeriv f.natDegree = C f.leadingCoeff
  proof: by
  have : _ <= 0 := Nat.sub_self f.natDegree ▸ natDegree_hasseDeriv_le ..
  rw [eq_C_of_natDegree_le_zero this]; rw [hasseDeriv_coeff]; rw [zero_add]; rw [Nat.choose_self]; rw [Nat.cast_one]; rw [one_mul]; rw [leadingCoeff]

中文:
定理 hasseDeriv_natDegree_eq_C
  结论: f.hasseDeriv f.natDegree = C f.leadingCoeff
  证明: by
  have : _ <= 0 := Nat.sub_self f.natDegree ▸ natDegree_hasseDeriv_le ..
  rw [eq_C_of_natDegree_le_zero this]; rw [hasseDeriv_coeff]; rw [zero_add]; rw [Nat.choose_self]; rw [Nat.cast_one]; rw [one_mul]; rw [leadingCoeff]

Depends on / 依赖: Nat.cast_one, Nat.choose_self, Nat.sub_self, cast_one, choose_self, eq_C_of_natDegree_le_zero, f.natDegree, hasseDeriv_coeff, leadingCoeff, natDegree, natDegree_hasseDeriv_le, one_mul, sub_self, zero_add
-/
theorem hasseDeriv_natDegree_eq_C : f.hasseDeriv f.natDegree = C f.leadingCoeff := by
  have : _ <= 0 := Nat.sub_self f.natDegree ▸ natDegree_hasseDeriv_le ..
  rw [eq_C_of_natDegree_le_zero this]; rw [hasseDeriv_coeff]; rw [zero_add]; rw [Nat.choose_self]; rw [Nat.cast_one]; rw [one_mul]; rw [leadingCoeff]

/--
theorem `natDegree_hasseDeriv` / 定理 `natDegree_hasseDeriv`

English:
theorem natDegree_hasseDeriv
  given: [IsAddTorsionFree R] (p : R[X]) (n : Nat)
  proof: by
  classical
  refine map_natDegree_eq_sub (fun h => hasseDeriv_eq_zero_of_lt_natDegree _ _) ?_
  simp only [Ne, hasseDeriv_monomial, natDegree_monomial, ite_eq_right_iff]
  simp +contextual [← nsmul_eq_mul, Nat.choose_eq_zero_iff, le_of_lt]

中文:
定理 natDegree_hasseDeriv
  条件: [IsAddTorsionFree R] (p : R[X]) (n : 自然数)
  证明: by
  classical
  refine map_natDegree_eq_sub (fun h => hasseDeriv_eq_zero_of_lt_natDegree _ _) ?_
  simp only [Ne, hasseDeriv_monomial, natDegree_monomial, ite_eq_right_iff]
  simp +contextual [← nsmul_eq_mul, Nat.choose_eq_zero_iff, le_of_lt]

Depends on / 依赖: Nat.choose_eq_zero_iff, choose_eq_zero_iff, classical, contextual, hasseDeriv_eq_zero_of_lt_natDegree, hasseDeriv_monomial, ite_eq_right_iff, le_of_lt, map_natDegree_eq_sub, natDegree_monomial, nsmul_eq_mul
-/
theorem natDegree_hasseDeriv [IsAddTorsionFree R] (p : R[X]) (n : Nat) :
    natDegree (hasseDeriv n p) = natDegree p - n := by
  classical
  refine map_natDegree_eq_sub (fun h => hasseDeriv_eq_zero_of_lt_natDegree _ _) ?_
  simp only [Ne, hasseDeriv_monomial, natDegree_monomial, ite_eq_right_iff]
  simp +contextual [← nsmul_eq_mul, Nat.choose_eq_zero_iff, le_of_lt]

section

open AddMonoidHom Finset.Nat

open Finset (antidiagonal mem_antidiagonal)

/--
theorem `hasseDeriv_mul` / 定理 `hasseDeriv_mul`

English:
theorem hasseDeriv_mul
  given: (f g : R[X])
  proof: by
  let D k := (@hasseDeriv R _ k).toAddMonoidHom
  let Φ := @AddMonoidHom.mul R[X] _
  change
    (compHom (D k)).comp Φ f g =
      ∑ ij in antidiagonal k, ((compHom.comp ((compHom Φ) (D ij.1))).flip (D ij.2) f) g
  simp only [← finsetSum_apply]
  congr 2
  clear f g
  ext m r n s : 4
  simp only

中文:
定理 hasseDeriv_mul
  条件: (f g : R[X])
  证明: by
  let D k := (@hasseDeriv R _ k).toAddMonoidHom
  let Φ := @AddMonoidHom.mul R[X] _
  change
    (compHom (D k)).comp Φ f g =
      ∑ ij in antidiagonal k, ((compHom.comp ((compHom Φ) (D ij.1))).flip (D ij.2) f) g
  simp only [← finsetSum_apply]
  congr 2
  clear f g
  ext m r n s : 4
  simp only

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mul, Function, Function.comp_apply, LinearMap, LinearMap.toAddMonoidHom_coe, antidiagonal, coe_comp, coe_mul, coe_mulLeft, compHom, compHom.comp, compHom_apply_apply, comp_apply, finsetSum_apply, flip_apply, hasseDeriv, hasseDeriv_monomial, monomial_mul_monomial, toAddMonoidHom
-/
theorem hasseDeriv_mul (f g : R[X]) :
    hasseDeriv k (f * g) = ∑ ij in antidiagonal k, hasseDeriv ij.1 f * hasseDeriv ij.2 g := by
  let D k := (@hasseDeriv R _ k).toAddMonoidHom
  let Φ := @AddMonoidHom.mul R[X] _
  change
    (compHom (D k)).comp Φ f g =
      ∑ ij in antidiagonal k, ((compHom.comp ((compHom Φ) (D ij.1))).flip (D ij.2) f) g
  simp only [← finsetSum_apply]
  congr 2
  clear f g
  ext m r n s : 4
  simp only [Φ, D, finsetSum_apply, coe_mulLeft, coe_comp, flip_apply, Function.comp_apply,
             hasseDeriv_monomial, LinearMap.toAddMonoidHom_coe, compHom_apply_apply,
             coe_mul, monomial_mul_monomial]
  have aux :
    forall x : Nat × Nat,
      x in antidiagonal k ->
        monomial (m - x.1 + (n - x.2)) (↑(m.choose x.1) * r * (↑(n.choose x.2) * s)) =
          monomial (m + n - k) (↑(m.choose x.1) * ↑(n.choose x.2) * (r * s)) := by
    intro x hx
    rw [mem_antidiagonal] at hx
    subst hx
    by_cases! hm : m < x.1
    · simp only [Nat.choose_eq_zero_of_lt hm, Nat.cast_zero, zero_mul,
                 monomial_zero_right]
    by_cases! hn : n < x.2
    · simp only [Nat.choose_eq_zero_of_lt hn, Nat.cast_zero, zero_mul,
                 mul_zero, monomial_zero_right]
    rw [tsub_add_eq_add_tsub hm]; rw [← add_tsub_assoc_of_le hn]; rw [← tsub_add_eq_tsub_tsub]; rw [add_comm x.2 x.1]; rw [mul_assoc]; rw [← mul_assoc r]; rw [← (Nat.cast_commute _ r).eq]; rw [mul_assoc]; rw [mul_assoc]
  rw [Finset.sum_congr rfl aux]
  rw [← map_sum]; rw [← Finset.sum_mul]
  congr
  rw_mod_cast [← Nat.add_choose_eq]

end

end Polynomial
