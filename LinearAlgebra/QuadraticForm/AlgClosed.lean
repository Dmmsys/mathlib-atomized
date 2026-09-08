/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Quadratic forms over an algebraically closed field

`equivalent_sum_squares`: A nondegenerate quadratic form over an algebraically closed field of
characteristic not equal to 2 is equivalent to a sum of squares.

TODO: generalize `QuadraticForm.isometryEquivSumSquares` to quadratically closed field.
-/

public section


open QuadraticMap
namespace QuadraticForm

open Finset

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K] [IsAlgClosed K]

/-- The isometry between a weighted sum of squares on an algebraically closed field and the
sum of squares, i.e. `weightedSumSquares` with weights 1 or 0. -/
/-
**QuadraticForm.isometryEquivSumSquares** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm
`。
形式化陈述：isometryEquivSumSquares [DecidableEq K] (w : ι -> K) : IsometryEquiv (weig
htedSumSquares K w) (weightedSumSquares K (fun i => if w i = 0 then 0 else 1 : ι
 -> K))
参数：w : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isometry between a weighted sum of squares on an algebraically closed field 
and the
sum of squares, i.e. `weightedSumSquares` with weights 1 or 0.
-/
noncomputable def isometryEquivSumSquares [DecidableEq K] (w : ι → K) :
    IsometryEquiv (weightedSumSquares K w)
      (weightedSumSquares K (fun i => if w i = 0 then 0 else 1 : ι → K)) := by
  refine isometryEquivWeightedSumSquaresWeightedSumSquares (fun i => if h : w i = 0 then 1 else
    Units.mk0 (IsAlgClosed.exists_eq_mul_self (w i)).choose (by
      rw [← mul_self_eq_zero.ne, ← (IsAlgClosed.exists_eq_mul_self (w i)).choose_spec]
      simpa using h)) ?_
  intro i
  split_ifs with h <;>
    simp [h, pow_two, ← (IsAlgClosed.exists_eq_mul_self (w i : K)).choose_spec]

/-- The isometry between a weighted sum of squares on an algebraically closed field and the
sum of squares, i.e. `weightedSumSquares` with weight `fun (i : ι) => 1`. -/
/-
**QuadraticForm.isometryEquivSumSquaresUnits** 是 Mathlib 中的一个定义，位于命名空间 `Quadrati
cForm`。
形式化陈述：isometryEquivSumSquaresUnits [DecidableEq K] (w : ι -> Kˣ) : IsometryEquiv
 (weightedSumSquares K w) (weightedSumSquares K (1 : ι -> K))
参数：w : ι -> Kˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isometry between a weighted sum of squares on an algebraically closed field 
and the
sum of squares, i.e. `weightedSumSquares` with weight `fun (i : ι) => 1`.
-/
noncomputable def isometryEquivSumSquaresUnits [DecidableEq K] (w : ι → Kˣ) :
    IsometryEquiv (weightedSumSquares K w) (weightedSumSquares K (1 : ι → K)) :=
  (isometryEquivSumSquares (fun i ↦ (w i).val)).trans (weightedSumSquaresCongr (by ext; simp))

/-- A nondegenerate quadratic form on an algebraically closed field of characteristic not equal to 2
is equivalent to the sum of squares, i.e. `weightedSumSquares` with weight `fun (i : ι) => 1`. -/
/-
**QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed** 是 Mathlib 中的一个定理，
位于命名空间 `QuadraticForm`。
形式化陈述：equivalent_weightedSumSquares_of_isAlgClosed [Invertible (2 : K)] {M : Typ
e*} [AddCommGroup M] [Module K M] [FiniteDimensional K M] (Q : QuadraticForm K M
) (hQ : (associated Q).SeparatingLeft) : Equivalent Q (weightedSumSquares K (1 :
 Fin (Module.finrank K M) -> K))
参数：2 : K；Q : QuadraticForm K M；hQ : (associated Q).SeparatingLeft。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'`：equ
ivalent_weightedSumSquares_units_of_nondegenerate' (Q : QuadraticForm K V) (hQ :
 (associated (R

--- 原说明 ---
A nondegenerate quadratic form on an algebraically closed field of characteristi
c not equal to 2
is equivalent to the sum of squares, i.e. `weightedSumSquares` with weight `fun 
(i : ι) => 1`.
-/
theorem equivalent_weightedSumSquares_of_isAlgClosed [Invertible (2 : K)] {M : Type*}
    [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (Q : QuadraticForm K M) (hQ : (associated Q).SeparatingLeft) :
    Equivalent Q (weightedSumSquares K (1 : Fin (Module.finrank K M) → K)) :=
  open scoped Classical in
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  ⟨hw₁.trans (isometryEquivSumSquaresUnits w)⟩

/-- All nondegenerate quadratic forms on an algebraically closed field of characteristic not equal
to 2 are equivalent. -/
/-
**QuadraticForm.equivalent_of_isAlgClosed** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticFo
rm`。
形式化陈述：equivalent_of_isAlgClosed [Invertible (2 : K)] {M : Type*} [AddCommGroup M
] [Module K M] [FiniteDimensional K M] (Q₁ Q₂ : QuadraticForm K M) (hQ₁ : (assoc
iated Q₁).SeparatingLeft) (hQ₂ : (associated Q₂).SeparatingLeft) : Equivalent Q₁
 Q₂
参数：2 : K；Q₁ Q₂ : QuadraticForm K M；hQ₁ : (associated Q₁).SeparatingLeft；hQ₂ : (a
ssociated Q₂).SeparatingLeft。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `QuadraticMap.Equivalent.trans`：trans (h : Q₁.Equivalent Q₂) (h' : Q₂.Equ
ivalent Q₃) : Q₁.Equivalent Q₃
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed`：equivalent_w
eightedSumSquares_of_isAlgClosed [Invertible (2 : K)] {M : Type*} [AddCommGroup 
M] [Module K M] [FiniteDimensional K M] (Q : Qua…
· 使用定理 `QuadraticMap.Equivalent.symm`：symm (h : Q₁.Equivalent Q₂) : Q₂.Equivalen
t Q₁

--- 原说明 ---
All nondegenerate quadratic forms on an algebraically closed field of characteri
stic not equal
to 2 are equivalent.
-/
theorem equivalent_of_isAlgClosed [Invertible (2 : K)] {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (Q₁ Q₂ : QuadraticForm K M)
    (hQ₁ : (associated Q₁).SeparatingLeft)
    (hQ₂ : (associated Q₂).SeparatingLeft) : Equivalent Q₁ Q₂ :=
  (Q₁.equivalent_weightedSumSquares_of_isAlgClosed hQ₁).trans
  (Q₂.equivalent_weightedSumSquares_of_isAlgClosed hQ₂).symm

end QuadraticForm

