/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
public import Mathlib.Algebra.CharP.Invertible
import Mathlib.Analysis.Complex.Polynomial.Basic

deprecated_module (since := "2026-01-19")

public section

open QuadraticMap

namespace QuadraticForm

@[deprecated "Use QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed"
  (since := "2026-01-19")]
/--
theorem `equivalent_sum_squares` / 定理 `equivalent_sum_squares`

English:
theorem equivalent_sum_squares
  statement: {M : Type*} [AddCommGroup M] [Module Complex M] [FiniteDimensional Complex M]
  proof: equivalent_weightedSumSquares_of_isAlgClosed Q hQ

@[deprecated "Use QuadraticForm.equivalent_of_isAlgClosed" (since := "2026-01-19")]

中文:
定理 equivalent_sum_squares
  结论: {M : 类型} [加法交换群 M] [模 复形 M] [有限维 复形 M]
  证明: equivalent_weightedSumSquares_of_isAlgClosed Q hQ

@[deprecated "Use QuadraticForm.equivalent_of_isAlgClosed" (since := "2026-01-19")]

Depends on / 依赖: SeparatingLeft
-/
theorem equivalent_sum_squares {M : Type*} [AddCommGroup M] [Module Complex M] [FiniteDimensional Complex M]
    (Q : QuadraticForm Complex M) (hQ : (associated (R := Complex) Q).SeparatingLeft) :
    Equivalent Q (weightedSumSquares Complex (1 : Fin (Module.finrank Complex M) -> Complex)) :=
  equivalent_weightedSumSquares_of_isAlgClosed Q hQ

@[deprecated "Use QuadraticForm.equivalent_of_isAlgClosed" (since := "2026-01-19")]
/--
theorem `complex_equivalent` / 定理 `complex_equivalent`

English:
theorem complex_equivalent
  statement: {M : Type*} [AddCommGroup M] [Module Complex M]
  proof: equivalent_of_isAlgClosed Q₁ Q₂ hQ₁ hQ₂

中文:
定理 complex_equivalent
  结论: {M : 类型} [加法交换群 M] [模 复形 M]
  证明: equivalent_of_isAlgClosed Q₁ Q₂ hQ₁ hQ₂

Depends on / 依赖: equivalent_of_isAlgClosed
-/
theorem complex_equivalent {M : Type*} [AddCommGroup M] [Module Complex M]
    [FiniteDimensional Complex M] (Q₁ Q₂ : QuadraticForm Complex M)
    (hQ₁ : (associated Q₁).SeparatingLeft)
    (hQ₂ : (associated Q₂).SeparatingLeft) : Equivalent Q₁ Q₂ :=
  equivalent_of_isAlgClosed Q₁ Q₂ hQ₁ hQ₂

end QuadraticForm
