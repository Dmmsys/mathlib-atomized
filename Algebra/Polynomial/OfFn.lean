/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.List.ToFinsupp
public import Mathlib.LinearAlgebra.Pi
/-!
# `Polynomial.ofFn` and `Polynomial.toFn`

In this file we introduce `ofFn` and `toFn`, two functions that associate a polynomial to the vector
of its coefficients and vice versa. We prove some basic APIs for these functions.

## Main definitions

- `Polynomial.toFn n` associates to a polynomial the vector of its first `n` coefficients.
- `Polynomial.ofFn n` associates to a vector of length `n` the polynomial that has the entries of
  the vector as coefficients.
-/

@[expose] public section

namespace Polynomial

section toFn

variable {R : Type*} [Semiring R]

/--
Definition of `toFn` / `toFn` 的定义

English:
definition toFn
  signature: (n : Nat)
  body: LinearMap.pi (fun i => lcoeff R i)

中文:
定义 toFn
  签名: (n : 自然数)
  定义体: LinearMap.pi (fun i => lcoeff R i)

Depends on / 依赖: LinearMap, LinearMap.pi, lcoeff
-/
noncomputable def toFn (n : Nat) : R[X] ->ₗ[R] Fin n -> R := LinearMap.pi (fun i => lcoeff R i)

/--
theorem `toFn_zero` / 定理 `toFn_zero`

English:
theorem toFn_zero
  given: (n : Nat)
  statement: toFn n (0 : R[X]) = 0
  proof: by simp

中文:
定理 toFn_zero
  条件: (n : 自然数)
  结论: toFn n (0 : R[X]) = 0
  证明: by simp
-/
theorem toFn_zero (n : Nat) : toFn n (0 : R[X]) = 0 := by simp

end toFn
section ofFn

variable {R : Type*} [Semiring R] [DecidableEq R]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofFn` / `ofFn` 的定义

English:
definition ofFn
  signature: (n : Nat)
  body: ⟨.ofCoeff (List.ofFn v).toFinsupp⟩
  map_add' x y := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [h]
  map_smul' x p := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [h]

中文:
定义 ofFn
  签名: (n : 自然数)
  定义体: ⟨.ofCoeff (List.ofFn v).toFinsupp⟩
  map_add' x y := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [h]
  map_smul' x p := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [h]

Depends on / 依赖: List.ofFn, ofCoeff, toFinsupp
-/
def ofFn (n : Nat) : (Fin n -> R) ->ₗ[R] R[X] where
  toFun v := ⟨.ofCoeff (List.ofFn v).toFinsupp⟩
  map_add' x y := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [h]
  map_smul' x p := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [h]

/--
theorem `ofFn_zero` / 定理 `ofFn_zero`

English:
theorem ofFn_zero
  given: (n : Nat)
  statement: ofFn n (0 : Fin n -> R) = 0
  proof: by simp

@[simp]

中文:
定理 ofFn_zero
  条件: (n : 自然数)
  结论: ofFn n (0 : 有限集 n -> R) = 0
  证明: by simp

@[simp]
-/
theorem ofFn_zero (n : Nat) : ofFn n (0 : Fin n -> R) = 0 := by simp

@[simp]
/--
theorem `ofFn_zero'` / 定理 `ofFn_zero'`

English:
theorem ofFn_zero'
  given: (v : Fin 0 -> R)
  statement: ofFn 0 v = 0
  proof: rfl

中文:
定理 ofFn_zero'
  条件: (v : 有限集 0 -> R)
  结论: ofFn 0 v = 0
  证明: rfl
-/
theorem ofFn_zero' (v : Fin 0 -> R) : ofFn 0 v = 0 := rfl

/--
lemma `ne_zero_of_ofFn_ne_zero` / 引理 `ne_zero_of_ofFn_ne_zero`

English:
lemma ne_zero_of_ofFn_ne_zero
  given: {n : Nat} {v : Fin n -> R} (h : ofFn n v != 0)
  statement: n != 0
  proof: by
  contrapose h
  subst h
  simp

中文:
引理 ne_zero_of_ofFn_ne_zero
  条件: {n : 自然数} {v : 有限集 n -> R} (h : ofFn n v != 0)
  结论: n != 0
  证明: by
  contrapose h
  subst h
  simp

Depends on / 依赖: contrapose
-/
lemma ne_zero_of_ofFn_ne_zero {n : Nat} {v : Fin n -> R} (h : ofFn n v != 0) : n != 0 := by
  contrapose h
  subst h
  simp

set_option backward.isDefEq.respectTransparency false in
/-- If `i < n` the `i`-th coefficient of `ofFn n v` is `v i`. -/
@[simp]
/--
theorem `ofFn_coeff_eq_val_of_lt` / 定理 `ofFn_coeff_eq_val_of_lt`

English:
theorem ofFn_coeff_eq_val_of_lt
  given: {n i : Nat} (v : Fin n -> R) (hi : i < n)
  proof: by
  simp [ofFn, hi]

中文:
定理 ofFn_coeff_eq_val_of_lt
  条件: {n i : 自然数} (v : 有限集 n -> R) (hi : i < n)
  证明: by
  simp [ofFn, hi]
-/
theorem ofFn_coeff_eq_val_of_lt {n i : Nat} (v : Fin n -> R) (hi : i < n) :
    (ofFn n v).coeff i = v ⟨i, hi⟩ := by
  simp [ofFn, hi]

set_option backward.isDefEq.respectTransparency false in
/-- If `n ≤ i` the `i`-th coefficient of `ofFn n v` is `0`. -/
@[simp]
/--
theorem `ofFn_coeff_eq_zero_of_ge` / 定理 `ofFn_coeff_eq_zero_of_ge`

English:
theorem ofFn_coeff_eq_zero_of_ge
  given: {n i : Nat} (v : Fin n -> R) (hi : n <= i)
  proof: by
  simp [ofFn, Nat.not_lt_of_ge hi]

中文:
定理 ofFn_coeff_eq_zero_of_ge
  条件: {n i : 自然数} (v : 有限集 n -> R) (hi : n <= i)
  证明: by
  simp [ofFn, Nat.not_lt_of_ge hi]

Depends on / 依赖: Nat.not_lt_of_ge, not_lt_of_ge
-/
theorem ofFn_coeff_eq_zero_of_ge {n i : Nat} (v : Fin n -> R) (hi : n <= i) :
    (ofFn n v).coeff i = 0 := by
  simp [ofFn, Nat.not_lt_of_ge hi]

/--
theorem `ofFn_natDegree_lt` / 定理 `ofFn_natDegree_lt`

English:
theorem ofFn_natDegree_lt
  given: {n : Nat} (h : 1 <= n) (v : Fin n -> R)
  statement: (ofFn n v).natDegree < n
  proof: by
  rw [Nat.lt_iff_le_pred h]; rw [natDegree_le_iff_coeff_eq_zero]
exact fun _ h => ofFn_coeff_eq_zero_of_ge _ Nat.le_of_pred_lt h

中文:
定理 ofFn_natDegree_lt
  条件: {n : 自然数} (h : 1 <= n) (v : 有限集 n -> R)
  结论: (ofFn n v).natDegree < n
  证明: by
  rw [Nat.lt_iff_le_pred h]; rw [natDegree_le_iff_coeff_eq_zero]
exact fun _ h => ofFn_coeff_eq_zero_of_ge _ Nat.le_of_pred_lt h

Depends on / 依赖: Nat.le_of_pred_lt, Nat.lt_iff_le_pred, le_of_pred_lt, lt_iff_le_pred, natDegree_le_iff_coeff_eq_zero, ofFn_coeff_eq_zero_of_ge
-/
theorem ofFn_natDegree_lt {n : Nat} (h : 1 <= n) (v : Fin n -> R) : (ofFn n v).natDegree < n := by
  rw [Nat.lt_iff_le_pred h]; rw [natDegree_le_iff_coeff_eq_zero]
exact fun _ h => ofFn_coeff_eq_zero_of_ge _ Nat.le_of_pred_lt h

/--
theorem `ofFn_degree_lt` / 定理 `ofFn_degree_lt`

English:
theorem ofFn_degree_lt
  given: {n : Nat} (v : Fin n -> R)
  statement: (ofFn n v).degree < n
  proof: by
  by_cases h : ofFn n v = 0
  · simp only [h, degree_zero]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
  · exact (natDegree_lt_iff_degree_lt h).mp
 ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr <| ne_zero_of_ofFn_ne_zero h) _

中文:
定理 ofFn_degree_lt
  条件: {n : 自然数} (v : 有限集 n -> R)
  结论: (ofFn n v).degree < n
  证明: by
  by_cases h : ofFn n v = 0
  · simp only [h, degree_zero]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
  · exact (natDegree_lt_iff_degree_lt h).mp
 ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr <| ne_zero_of_ofFn_ne_zero h) _

Depends on / 依赖: Batteries, Batteries.compareOfLessAndEq_eq_lt.mp, Nat.one_le_iff_ne_zero.mpr, compareOfLessAndEq_eq_lt, degree_zero, natDegree_lt_iff_degree_lt, ne_zero_of_ofFn_ne_zero, ofFn_natDegree_lt, one_le_iff_ne_zero
-/
theorem ofFn_degree_lt {n : Nat} (v : Fin n -> R) : (ofFn n v).degree < n := by
  by_cases h : ofFn n v = 0
  · simp only [h, degree_zero]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
  · exact (natDegree_lt_iff_degree_lt h).mp
 ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr <| ne_zero_of_ofFn_ne_zero h) _

/--
theorem `ofFn_eq_sum_monomial` / 定理 `ofFn_eq_sum_monomial`

English:
theorem ofFn_eq_sum_monomial
  given: {n : Nat} (v : Fin n -> R)
  statement: ofFn n v =
  proof: by
  by_cases h : n = 0
  · subst h
    simp [ofFn]
  · rw [as_sum_range' (ofFn n v) n <| ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr h) v]
    simp [Finset.sum_range]

中文:
定理 ofFn_eq_sum_monomial
  条件: {n : 自然数} (v : 有限集 n -> R)
  结论: ofFn n v =
  证明: by
  by_cases h : n = 0
  · subst h
    simp [ofFn]
  · rw [as_sum_range' (ofFn n v) n <| ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr h) v]
    simp [Finset.sum_range]

Depends on / 依赖: Finset, Finset.sum_range, Nat.one_le_iff_ne_zero.mpr, as_sum_range, ofFn_natDegree_lt, one_le_iff_ne_zero, sum_range
-/
theorem ofFn_eq_sum_monomial {n : Nat} (v : Fin n -> R) : ofFn n v =
    ∑ i : Fin n, monomial i (v i) := by
  by_cases h : n = 0
  · subst h
    simp [ofFn]
  · rw [as_sum_range' (ofFn n v) n <| ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr h) v]
    simp [Finset.sum_range]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toFn_comp_ofFn_eq_id` / 定理 `toFn_comp_ofFn_eq_id`

English:
theorem toFn_comp_ofFn_eq_id
  given: (n : Nat) (v : Fin n -> R)
  statement: toFn n (ofFn n v) = v
  proof: by
  simp [toFn, ofFn, LinearMap.pi]

中文:
定理 toFn_comp_ofFn_eq_id
  条件: (n : 自然数) (v : 有限集 n -> R)
  结论: toFn n (ofFn n v) = v
  证明: by
  simp [toFn, ofFn, LinearMap.pi]

Depends on / 依赖: LinearMap, LinearMap.pi
-/
theorem toFn_comp_ofFn_eq_id (n : Nat) (v : Fin n -> R) : toFn n (ofFn n v) = v := by
  simp [toFn, ofFn, LinearMap.pi]

/--
theorem `injective_ofFn` / 定理 `injective_ofFn`

English:
theorem injective_ofFn
  given: (n : Nat)
  statement: Function.Injective (ofFn (R := R) n)
  proof: Function.LeftInverse.injective toFn_comp_ofFn_eq_id n

omit [DecidableEq R] in

中文:
定理 injective_ofFn
  条件: (n : 自然数)
  结论: 函数.单射 (ofFn (R := R) n)
  证明: Function.LeftInverse.injective toFn_comp_ofFn_eq_id n

omit [DecidableEq R] in
-/
theorem injective_ofFn (n : Nat) : Function.Injective (ofFn (R := R) n) :=
Function.LeftInverse.injective toFn_comp_ofFn_eq_id n

omit [DecidableEq R] in
/--
theorem `surjective_toFn` / 定理 `surjective_toFn`

English:
theorem surjective_toFn
  given: (n : Nat)
  statement: Function.Surjective (toFn (R := R) n)
  proof: open scoped Classical in
Function.RightInverse.surjective toFn_comp_ofFn_eq_id n

中文:
定理 surjective_toFn
  条件: (n : 自然数)
  结论: 函数.满射 (toFn (R := R) n)
  证明: open scoped Classical in
Function.RightInverse.surjective toFn_comp_ofFn_eq_id n
-/
theorem surjective_toFn (n : Nat) : Function.Surjective (toFn (R := R) n) :=
  open scoped Classical in
Function.RightInverse.surjective toFn_comp_ofFn_eq_id n

/--
theorem `ofFn_comp_toFn_eq_id_of_natDegree_lt` / 定理 `ofFn_comp_toFn_eq_id_of_natDegree_lt`

English:
theorem ofFn_comp_toFn_eq_id_of_natDegree_lt
  given: {n : Nat} {p : R[X]} (h_deg : p.natDegree < n)
  proof: by
  ext i
  by_cases! h : i < n
  · simp [h, toFn]
· have : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt by lia
    simp [*]

中文:
定理 ofFn_comp_toFn_eq_id_of_natDegree_lt
  条件: {n : 自然数} {p : R[X]} (h_deg : p.natDegree < n)
  证明: by
  ext i
  by_cases! h : i < n
  · simp [h, toFn]
· have : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt by lia
    simp [*]

Depends on / 依赖: coeff_eq_zero_of_natDegree_lt, p.coeff
-/
theorem ofFn_comp_toFn_eq_id_of_natDegree_lt {n : Nat} {p : R[X]} (h_deg : p.natDegree < n) :
    ofFn n (toFn n p) = p := by
  ext i
  by_cases! h : i < n
  · simp [h, toFn]
· have : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt by lia
    simp [*]

end ofFn

end Polynomial
