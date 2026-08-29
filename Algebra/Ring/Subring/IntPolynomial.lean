/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomials over subrings.

Given a field `K` with a subring `R`, in this file we construct a map from polynomials in `K[X]`
with coefficients in `R` to `R[X]`. We provide several lemmas to deal with
coefficients, degree, and evaluation of `Polynomial.int`.
This is useful when dealing with integral elements in an extension of fields.

## Main Definitions
* `Polynomial.int` : given a polynomial `P` in `K[X]` whose coefficients all belong to a subring `R`
  of the field `K`, `P.int R` is the corresponding polynomial in `R[X]`.
-/

@[expose] public section

variable {K : Type*} [Field K] (R : Subring K)

open scoped Polynomial

/--
Definition of `Polynomial.int` / `Polynomial.int` 的定义

English:
definition Polynomial.int
  signature: (P : K[X]) (hP : forall n : Nat, P.coeff n in R)
  body: ⟨P.coeff n, hP n⟩
  toFinsupp.coeff.support := P.support
  toFinsupp.coeff.mem_support_toFun n := by rw [ne_eq, ← Subring.coe_eq_zero_iff, mem_support_iff]

中文:
定义 Polynomial.int
  签名: (P : K[X]) (hP : 对任意 n : 自然数, P.coeff n in R)
  定义体: ⟨P.coeff n, hP n⟩
  toFinsupp.coeff.support := P.support
  toFinsupp.coeff.mem_support_toFun n := by rw [ne_eq, ← Subring.coe_eq_zero_iff, mem_support_iff]

Depends on / 依赖: P.coeff
-/
def Polynomial.int (P : K[X]) (hP : forall n : Nat, P.coeff n in R) : R[X] where
  toFinsupp.coeff.toFun n := ⟨P.coeff n, hP n⟩
  toFinsupp.coeff.support := P.support
  toFinsupp.coeff.mem_support_toFun n := by rw [ne_eq, ← Subring.coe_eq_zero_iff, mem_support_iff]

namespace Polynomial

variable (P : K[X]) (hP : forall n : Nat, P.coeff n in R)

@[simp]
/--
theorem `int_coeff_eq` / 定理 `int_coeff_eq`

English:
theorem int_coeff_eq
  given: (n : Nat)
  statement: ↑((P.int R hP).coeff n) = P.coeff n
  proof: rfl

@[simp]

中文:
定理 int_coeff_eq
  条件: (n : 自然数)
  结论: ↑((P.int R hP).coeff n) = P.coeff n
  证明: rfl

@[simp]
-/
theorem int_coeff_eq (n : Nat) : ↑((P.int R hP).coeff n) = P.coeff n := rfl

@[simp]
/--
theorem `int_leadingCoeff_eq` / 定理 `int_leadingCoeff_eq`

English:
theorem int_leadingCoeff_eq
  statement: ↑(P.int R hP).leadingCoeff = P.leadingCoeff
  proof: rfl

@[simp]

中文:
定理 int_leadingCoeff_eq
  结论: ↑(P.int R hP).leadingCoeff = P.leadingCoeff
  证明: rfl

@[simp]
-/
theorem int_leadingCoeff_eq : ↑(P.int R hP).leadingCoeff = P.leadingCoeff := rfl

@[simp]
/--
theorem `int_monic_iff` / 定理 `int_monic_iff`

English:
theorem int_monic_iff
  statement: (P.int R hP).Monic ↔ P.Monic
  proof: by
  rw [Monic]; rw [Monic]; rw [← int_leadingCoeff_eq]; rw [OneMemClass.coe_eq_one]

@[simp]

中文:
定理 int_monic_iff
  结论: (P.int R hP).Monic ↔ P.Monic
  证明: by
  rw [Monic]; rw [Monic]; rw [← int_leadingCoeff_eq]; rw [OneMemClass.coe_eq_one]

@[simp]

Depends on / 依赖: OneMemClass, OneMemClass.coe_eq_one, X.fromSpecStalk, coe_eq_one, fromSpecStalk, int_leadingCoeff_eq
-/
theorem int_monic_iff : (P.int R hP).Monic ↔ P.Monic := by
  rw [Monic]; rw [Monic]; rw [← int_leadingCoeff_eq]; rw [OneMemClass.coe_eq_one]

@[simp]
/--
theorem `int_natDegree` / 定理 `int_natDegree`

English:
theorem int_natDegree
  statement: (P.int R hP).natDegree = P.natDegree
  proof: rfl

中文:
定理 int_natDegree
  结论: (P.int R hP).natDegree = P.natDegree
  证明: rfl
-/
theorem int_natDegree : (P.int R hP).natDegree = P.natDegree := rfl

variable {L : Type*} [Field L] [Algebra K L]

@[simp]
/--
theorem `int_eval₂_eq` / 定理 `int_eval₂_eq`

English:
theorem int_eval₂_eq
  given: (x : L)
  proof: by
  rw [aeval_eq_sum_range]; rw [eval₂_eq_sum_range]
  exact Finset.sum_congr rfl (fun n _ => by rw [Algebra.smul_def]; rfl)

中文:
定理 int_eval₂_eq
  条件: (x : L)
  证明: by
  rw [aeval_eq_sum_range]; rw [eval₂_eq_sum_range]
  exact Finset.sum_congr rfl (fun n _ => by rw [Algebra.smul_def]; rfl)

Depends on / 依赖: Algebra, Algebra.smul_def, Finset, Finset.sum_congr, aeval_eq_sum_range, smul_def, sum_congr
-/
theorem int_eval₂_eq (x : L) :
    eval₂ (algebraMap R L) x (P.int R hP) = aeval x P := by
  rw [aeval_eq_sum_range]; rw [eval₂_eq_sum_range]
  exact Finset.sum_congr rfl (fun n _ => by rw [Algebra.smul_def]; rfl)

end Polynomial
