/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs

/-! # Lemmas about `Algebra.trace` and `Algebra.norm` on `ℂ` -/

public section


open Complex

/--
theorem `Algebra.leftMulMatrix_complex` / 定理 `Algebra.leftMulMatrix_complex`

English:
theorem Algebra.leftMulMatrix_complex
  given: (z : Complex)
  proof: by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]; rw [Complex.coe_basisOneI_repr]; rw [Complex.coe_basisOneI]; rw [mul_re]; rw [mul_im]; rw [Matrix.of_apply]
  fin_cases j <;> dsimp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val]
  · simp only [one_re, mul_one, one_im, mul_zero,
      sub_zero, zero_add]
    fin_cases i <;> rfl
  · simp only [I_re, mul_zero, I_im,
      mul_one, zero_sub, add_zero]
    fin_cases i <;> rfl

中文:
定理 代数.leftMulMatrix_complex
  条件: (z : 复形)
  证明: by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]; rw [Complex.coe_basisOneI_repr]; rw [Complex.coe_basisOneI]; rw [mul_re]; rw [mul_im]; rw [Matrix.of_apply]
  fin_cases j <;> dsimp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val]
  · simp only [one_re, mul_one, one_im, mul_zero,
      sub_zero, zero_add]
    fin_cases i <;> rfl
  · simp only [I_re, mul_zero, I_im,
      mul_one, zero_sub, add_zero]
    fin_cases i <;> rfl

Depends on / 依赖: Algebra, Algebra.leftMulMatrix_eq_repr_mul, Complex.coe_basisOneI, Complex.coe_basisOneI_repr, Fin.mk_one, Fin.zero_eta, I_im, I_re, Matrix, Matrix.cons_val, Matrix.of_apply, add_zero, coe_basisOneI, coe_basisOneI_repr, cons_val, fin_cases, leftMulMatrix_eq_repr_mul, mk_one, mul_im, mul_one
-/
theorem Algebra.leftMulMatrix_complex (z : Complex) :
    Algebra.leftMulMatrix Complex.basisOneI z = !![z.re, -z.im; z.im, z.re] := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]; rw [Complex.coe_basisOneI_repr]; rw [Complex.coe_basisOneI]; rw [mul_re]; rw [mul_im]; rw [Matrix.of_apply]
  fin_cases j <;> dsimp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val]
  · simp only [one_re, mul_one, one_im, mul_zero,
      sub_zero, zero_add]
    fin_cases i <;> rfl
  · simp only [I_re, mul_zero, I_im,
      mul_one, zero_sub, add_zero]
    fin_cases i <;> rfl

/--
theorem `Algebra.trace_complex_apply` / 定理 `Algebra.trace_complex_apply`

English:
theorem Algebra.trace_complex_apply
  given: (z : Complex)
  statement: Algebra.trace Real Complex z = 2 * z.re
  proof: by
  rw [Algebra.trace_eq_matrix_trace Complex.basisOneI]; rw [Algebra.leftMulMatrix_complex]; rw [Matrix.trace_fin_two]
  exact (two_mul _).symm

中文:
定理 代数.trace_complex_apply
  条件: (z : 复形)
  结论: 代数.trace 实数 复形 z = 2 * z.re
  证明: by
  rw [Algebra.trace_eq_matrix_trace Complex.basisOneI]; rw [Algebra.leftMulMatrix_complex]; rw [Matrix.trace_fin_two]
  exact (two_mul _).symm

Depends on / 依赖: Algebra, Algebra.leftMulMatrix_complex, Algebra.trace_eq_matrix_trace, Complex.basisOneI, Matrix, Matrix.trace_fin_two, basisOneI, leftMulMatrix_complex, trace_eq_matrix_trace, trace_fin_two, two_mul
-/
theorem Algebra.trace_complex_apply (z : Complex) : Algebra.trace Real Complex z = 2 * z.re := by
  rw [Algebra.trace_eq_matrix_trace Complex.basisOneI]; rw [Algebra.leftMulMatrix_complex]; rw [Matrix.trace_fin_two]
  exact (two_mul _).symm

/--
theorem `Algebra.norm_complex_apply` / 定理 `Algebra.norm_complex_apply`

English:
theorem Algebra.norm_complex_apply
  given: (z : Complex)
  statement: Algebra.norm Real z = Complex.normSq z
  proof: by
  rw [Algebra.norm_eq_matrix_det Complex.basisOneI]; rw [Algebra.leftMulMatrix_complex]; rw [Matrix.det_fin_two]; rw [normSq_apply]
  simp

中文:
定理 代数.norm_complex_apply
  条件: (z : 复形)
  结论: 代数.norm 实数 z = 复形.normSq z
  证明: by
  rw [Algebra.norm_eq_matrix_det Complex.basisOneI]; rw [Algebra.leftMulMatrix_complex]; rw [Matrix.det_fin_two]; rw [normSq_apply]
  simp

Depends on / 依赖: Algebra, Algebra.leftMulMatrix_complex, Algebra.norm_eq_matrix_det, Complex.basisOneI, Matrix, Matrix.det_fin_two, basisOneI, det_fin_two, leftMulMatrix_complex, normSq_apply, norm_eq_matrix_det
-/
theorem Algebra.norm_complex_apply (z : Complex) : Algebra.norm Real z = Complex.normSq z := by
  rw [Algebra.norm_eq_matrix_det Complex.basisOneI]; rw [Algebra.leftMulMatrix_complex]; rw [Matrix.det_fin_two]; rw [normSq_apply]
  simp

/--
theorem `Algebra.norm_complex_eq` / 定理 `Algebra.norm_complex_eq`

English:
theorem Algebra.norm_complex_eq
  statement: Algebra.norm Real = normSq.toMonoidHom
  proof: MonoidHom.ext Algebra.norm_complex_apply

中文:
定理 代数.norm_complex_eq
  结论: 代数.norm 实数 = normSq.toMonoidHom
  证明: MonoidHom.ext Algebra.norm_complex_apply

Depends on / 依赖: Algebra, Algebra.norm_complex_apply, MonoidHom, MonoidHom.ext, norm_complex_apply
-/
theorem Algebra.norm_complex_eq : Algebra.norm Real = normSq.toMonoidHom :=
  MonoidHom.ext Algebra.norm_complex_apply
