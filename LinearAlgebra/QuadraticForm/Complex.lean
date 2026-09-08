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
/-
**QuadraticForm.equivalent_sum_squares** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`
。
形式化陈述：equivalent_sum_squares {M : Type*} [AddCommGroup M] [Module Complex M] [Fi
niteDimensional Complex M] (Q : QuadraticForm Complex M) (hQ : (associated (R
参数：Q : QuadraticForm Complex M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed`：equivalent_w
eightedSumSquares_of_isAlgClosed [Invertible (2 : K)] {M : Type*} [AddCommGroup 
M] [Module K M] [FiniteDimensional K M] (Q : Qua…
-/
theorem equivalent_sum_squares {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (Q : QuadraticForm ℂ M) (hQ : (associated (R := ℂ) Q).SeparatingLeft) :
    Equivalent Q (weightedSumSquares ℂ (1 : Fin (Module.finrank ℂ M) → ℂ)) :=
  equivalent_weightedSumSquares_of_isAlgClosed Q hQ

@[deprecated "Use QuadraticForm.equivalent_of_isAlgClosed" (since := "2026-01-19")]
/-
**QuadraticForm.complex_equivalent** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：complex_equivalent {M : Type*} [AddCommGroup M] [Module Complex M] [Finite
Dimensional Complex M] (Q₁ Q₂ : QuadraticForm Complex M) (hQ₁ : (associated Q₁).
SeparatingLeft) (hQ₂ : (associated Q₂).SeparatingLeft) : Equivalent Q₁ Q₂
参数：Q₁ Q₂ : QuadraticForm Complex M；hQ₁ : (associated Q₁).SeparatingLeft；hQ₂ : (a
ssociated Q₂).SeparatingLeft。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `QuadraticForm.equivalent_of_isAlgClosed`：equivalent_of_isAlgClosed [Inve
rtible (2 : K)] {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M
] (Q₁ Q₂ : QuadraticForm K M)…
-/
theorem complex_equivalent {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (Q₁ Q₂ : QuadraticForm ℂ M)
    (hQ₁ : (associated Q₁).SeparatingLeft)
    (hQ₂ : (associated Q₂).SeparatingLeft) : Equivalent Q₁ Q₂ :=
  equivalent_of_isAlgClosed Q₁ Q₂ hQ₁ hQ₂

end QuadraticForm

