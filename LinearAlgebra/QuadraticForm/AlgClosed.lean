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

/--
Definition of `isometryEquivSumSquares` / `isometryEquivSumSquares` 的定义

English:
definition isometryEquivSumSquares
  signature: [DecidableEq K] (w : ι -> K)
  body: by
  refine isometryEquivWeightedSumSquaresWeightedSumSquares (fun i => if h : w i = 0 then 1 else
    Units.mk0 (IsAlgClosed.exists_eq_mul_self (w i)).choose (by
      rw [← mul_self_eq_zero.ne]; rw [← (IsAlgClosed.exists_eq_mul_self (w i)).choose_spec]
      simpa using h)) ?_
  intro i
  split_if

中文:
定义 isometryEquivSumSquares
  签名: [DecidableEq K] (w : ι -> K)
  定义体: by
  refine isometryEquivWeightedSumSquaresWeightedSumSquares (fun i => if h : w i = 0 then 1 else
    Units.mk0 (IsAlgClosed.exists_eq_mul_self (w i)).choose (by
      rw [← mul_self_eq_zero.ne]; rw [← (IsAlgClosed.exists_eq_mul_self (w i)).choose_spec]
      simpa using h)) ?_
  intro i
  split_if

Depends on / 依赖: IsAlgClosed, IsAlgClosed.exists_eq_mul_self, Units.mk0, choose_spec, exists_eq_mul_self, isometryEquivWeightedSumSquaresWeightedSumSquares, mul_self_eq_zero, mul_self_eq_zero.ne, pow_two, split_ifs
-/
noncomputable def isometryEquivSumSquares [DecidableEq K] (w : ι -> K) :
    IsometryEquiv (weightedSumSquares K w)
      (weightedSumSquares K (fun i => if w i = 0 then 0 else 1 : ι -> K)) := by
  refine isometryEquivWeightedSumSquaresWeightedSumSquares (fun i => if h : w i = 0 then 1 else
    Units.mk0 (IsAlgClosed.exists_eq_mul_self (w i)).choose (by
      rw [← mul_self_eq_zero.ne]; rw [← (IsAlgClosed.exists_eq_mul_self (w i)).choose_spec]
      simpa using h)) ?_
  intro i
  split_ifs with h <;>
    simp [h, pow_two, ← (IsAlgClosed.exists_eq_mul_self (w i : K)).choose_spec]

/--
Definition of `isometryEquivSumSquaresUnits` / `isometryEquivSumSquaresUnits` 的定义

English:
definition isometryEquivSumSquaresUnits
  signature: [DecidableEq K] (w : ι -> Kˣ)
  body: (isometryEquivSumSquares (fun i => (w i).val)).trans (weightedSumSquaresCongr (by ext; simp))

中文:
定义 isometryEquivSumSquaresUnits
  签名: [DecidableEq K] (w : ι -> Kˣ)
  定义体: (isometryEquivSumSquares (fun i => (w i).val)).trans (weightedSumSquaresCongr (by ext; simp))

Depends on / 依赖: isometryEquivSumSquares, weightedSumSquaresCongr
-/
noncomputable def isometryEquivSumSquaresUnits [DecidableEq K] (w : ι -> Kˣ) :
    IsometryEquiv (weightedSumSquares K w) (weightedSumSquares K (1 : ι -> K)) :=
  (isometryEquivSumSquares (fun i => (w i).val)).trans (weightedSumSquaresCongr (by ext; simp))

/--
theorem `equivalent_weightedSumSquares_of_isAlgClosed` / 定理 `equivalent_weightedSumSquares_of_isAlgClosed`

English:
theorem equivalent_weightedSumSquares_of_isAlgClosed
  statement: [Invertible (2 : K)] {M : Type*}
  proof: open scoped Classical in
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  ⟨hw₁.trans (isometryEquivSumSquaresUnits w)⟩

中文:
定理 equivalent_weightedSumSquares_of_isAlgClosed
  结论: [可逆 (2 : K)] {M : 类型}
  证明: open scoped Classical in
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  ⟨hw₁.trans (isometryEquivSumSquaresUnits w)⟩

Depends on / 依赖: Classical, Q.equivalent_weightedSumSquares_units_of_nondegenerate, equivalent_weightedSumSquares_units_of_nondegenerate, isometryEquivSumSquaresUnits, scoped
-/
theorem equivalent_weightedSumSquares_of_isAlgClosed [Invertible (2 : K)] {M : Type*}
    [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (Q : QuadraticForm K M) (hQ : (associated Q).SeparatingLeft) :
    Equivalent Q (weightedSumSquares K (1 : Fin (Module.finrank K M) -> K)) :=
  open scoped Classical in
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  ⟨hw₁.trans (isometryEquivSumSquaresUnits w)⟩

/--
theorem `equivalent_of_isAlgClosed` / 定理 `equivalent_of_isAlgClosed`

English:
theorem equivalent_of_isAlgClosed
  statement: [Invertible (2 : K)] {M : Type*} [AddCommGroup M] [Module K M]
  proof: (Q₁.equivalent_weightedSumSquares_of_isAlgClosed hQ₁).trans
  (Q₂.equivalent_weightedSumSquares_of_isAlgClosed hQ₂).symm

中文:
定理 equivalent_of_isAlgClosed
  结论: [可逆 (2 : K)] {M : 类型} [加法交换群 M] [模 K M]
  证明: (Q₁.equivalent_weightedSumSquares_of_isAlgClosed hQ₁).trans
  (Q₂.equivalent_weightedSumSquares_of_isAlgClosed hQ₂).symm

Depends on / 依赖: equivalent_weightedSumSquares_of_isAlgClosed
-/
theorem equivalent_of_isAlgClosed [Invertible (2 : K)] {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (Q₁ Q₂ : QuadraticForm K M)
    (hQ₁ : (associated Q₁).SeparatingLeft)
    (hQ₂ : (associated Q₂).SeparatingLeft) : Equivalent Q₁ Q₂ :=
  (Q₁.equivalent_weightedSumSquares_of_isAlgClosed hQ₁).trans
  (Q₂.equivalent_weightedSumSquares_of_isAlgClosed hQ₂).symm

end QuadraticForm
