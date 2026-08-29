/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Polynomial identities from evaluation at invertible matrices

We prove `MvPolynomial.eq_of_eval_eq_on_gl`: two polynomials in `MvPolynomial (m × m) k` over an
infinite field `k` are equal if their evaluations agree at every invertible matrix. The proof
uses that the set of invertible matrices is Zariski-dense in `Matrix m m k`.
-/

@[expose] public section

namespace MvPolynomial

/--
theorem `eq_of_eval_eq_on_gl` / 定理 `eq_of_eval_eq_on_gl`

English:
theorem eq_of_eval_eq_on_gl
  statement: {m k : Type*} [Fintype m] [DecidableEq m] [Field k] [Infinite k]
  proof: by
  have hprod : (p - q) * Matrix.det (Matrix.mvPolynomialX m m k) = 0 := by
    apply MvPolynomial.funext
    intro s
    rw [map_mul]; rw [map_sub]; rw [map_zero]; rw [Matrix.eval_det_mvPolynomialX]
    by_cases hs_det : Matrix.det (Matrix.of fun i j : m => s (i, j)) = 0
    · rw [hs_det, mul_zer

中文:
定理 eq_of_eval_eq_on_gl
  结论: {m k : 类型} [Fintype m] [DecidableEq m] [Field k] [Infinite k]
  证明: by
  have hprod : (p - q) * Matrix.det (Matrix.mvPolynomialX m m k) = 0 := by
    apply MvPolynomial.funext
    intro s
    rw [map_mul]; rw [map_sub]; rw [map_zero]; rw [Matrix.eval_det_mvPolynomialX]
    by_cases hs_det : Matrix.det (Matrix.of fun i j : m => s (i, j)) = 0
    · rw [hs_det, mul_zer

Depends on / 依赖: GeneralLinearGroup, Matrix, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det, Matrix.eval_det_mvPolynomialX, Matrix.mvPolynomialX, Matrix.of, MvPolynomial, MvPolynomial.funext, eval_det_mvPolynomialX, hs_det, map_mul, map_sub, map_zero, mkOfDetNeZero, mul_eq_zero, mul_eq_zero.mp, mul_zero, mvPolynomialX, resolve_ri
-/
theorem eq_of_eval_eq_on_gl {m k : Type*} [Fintype m] [DecidableEq m] [Field k] [Infinite k]
    {p q : MvPolynomial (m × m) k}
    (h : forall g : Matrix.GeneralLinearGroup m k,
           MvPolynomial.eval (fun ij : m × m => (g : Matrix m m k) ij.1 ij.2) p =
           MvPolynomial.eval (fun ij : m × m => (g : Matrix m m k) ij.1 ij.2) q) :
    p = q := by
  have hprod : (p - q) * Matrix.det (Matrix.mvPolynomialX m m k) = 0 := by
    apply MvPolynomial.funext
    intro s
    rw [map_mul]; rw [map_sub]; rw [map_zero]; rw [Matrix.eval_det_mvPolynomialX]
    by_cases hs_det : Matrix.det (Matrix.of fun i j : m => s (i, j)) = 0
    · rw [hs_det, mul_zero]
    · have hh : (eval s) p = (eval s) q :=
        h (Matrix.GeneralLinearGroup.mkOfDetNeZero
          (Matrix.of fun i j : m => s (i, j)) hs_det)
      rw [hh]; rw [sub_self]; rw [zero_mul]
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hprod).resolve_right (Matrix.det_mvPolynomialX_ne_zero m k))

end MvPolynomial
