/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Data.Sign.Basic
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.RCLike.Basic

/-!
# Real quadratic forms

Sylvester's law of inertia `equivalent_one_neg_one_weighted_sum_squared`:
A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0.

When the real quadratic form is nondegenerate we can take the weights to be ±1,
as in `QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared`.

-/

@[expose] public section

open Finset Module QuadraticMap SignType

namespace QuadraticForm
variable {ι : Type*} [Fintype ι]

/--
Definition of `isometryEquivSignWeightedSumSquares` / `isometryEquivSignWeightedSumSquares` 的定义

English:
definition isometryEquivSignWeightedSumSquares
  signature: (w : ι -> Real)
  body: by
  let u i := if h : w i = 0 then (1 : Realˣ) else Units.mk0 (w i) h
  have hu : forall i : ι, 1 / √|(u i : Real)| != 0 := fun i =>
    have : (u i : Real) != 0 := (u i).ne_zero
    by positivity
  have hwu : forall i, w i / |(u i : Real)| = sign (w i) := fun i => by
    by_cases hi : w i = 0
    

中文:
定义 isometryEquivSignWeightedSumSquares
  签名: (w : ι -> 实数)
  定义体: by
  let u i := if h : w i = 0 then (1 : Realˣ) else Units.mk0 (w i) h
  have hu : forall i : ι, 1 / √|(u i : Real)| != 0 := fun i =>
    have : (u i : Real) != 0 := (u i).ne_zero
    by positivity
  have hwu : forall i, w i / |(u i : Real)| = sign (w i) := fun i => by
    by_cases hi : w i = 0
    

Depends on / 依赖: Pi.basisFun, QuadraticMap, QuadraticMap.isometryEquivBasisRepr, Units.mk0, Units.val_mk0, basisFun, classica, convert, isometryEquivBasisRepr, ne_zero, reduceDIte, unitsSMul, val_mk0, weightedSumSquares
-/
noncomputable def isometryEquivSignWeightedSumSquares (w : ι -> Real) :
    IsometryEquiv (weightedSumSquares Real w)
      (weightedSumSquares Real (fun i => (sign (w i) : Real))) := by
  let u i := if h : w i = 0 then (1 : Realˣ) else Units.mk0 (w i) h
  have hu : forall i : ι, 1 / √|(u i : Real)| != 0 := fun i =>
    have : (u i : Real) != 0 := (u i).ne_zero
    by positivity
  have hwu : forall i, w i / |(u i : Real)| = sign (w i) := fun i => by
    by_cases hi : w i = 0
    · simp [hi]
    · simp only [hi, ↓reduceDIte, Units.val_mk0, u]; field_simp; simp
  convert!
    QuadraticMap.isometryEquivBasisRepr (weightedSumSquares Real w)
      ((Pi.basisFun Real ι).unitsSMul fun i => .mk0 _ (hu i))
  ext1 v
  classical
  suffices ∑ i, (w i / |(u i : Real)|) * v i ^ 2 = ∑ i, w i * (v i ^ 2 * |(u i : Real)|⁻¹) by
    simpa [basisRepr_apply, Basis.unitsSMul_apply, ← _root_.sq, mul_pow, ← hwu, Pi.single_apply]
  exact sum_congr rfl fun j _ => by ring

/--
theorem `equivalent_sign_ne_zero_weighted_sum_squared` / 定理 `equivalent_sign_ne_zero_weighted_sum_squared`

English:
theorem equivalent_sign_ne_zero_weighted_sum_squared
  statement: {M : Type*} [AddCommGroup M] [Module Real M]
  proof: let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  ⟨sign ∘ ((↑) : Realˣ -> Real) ∘ w, fun i => sign_ne_zero.2 (w i).ne_zero,
    ⟨hw₁.trans (isometryEquivSignWeightedSumSquares (((↑) : Realˣ -> Real) ∘ w))⟩⟩

中文:
定理 equivalent_sign_ne_zero_weighted_sum_squared
  结论: {M : 类型} [加法交换群 M] [模 实数 M]
  证明: let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  ⟨sign ∘ ((↑) : Realˣ -> Real) ∘ w, fun i => sign_ne_zero.2 (w i).ne_zero,
    ⟨hw₁.trans (isometryEquivSignWeightedSumSquares (((↑) : Realˣ -> Real) ∘ w))⟩⟩

Depends on / 依赖: SeparatingLeft
-/
theorem equivalent_sign_ne_zero_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module Real M]
    [FiniteDimensional Real M] (Q : QuadraticForm Real M) (hQ : (associated (R := Real) Q).SeparatingLeft) :
    exists w : Fin (Module.finrank Real M) -> SignType,
      (forall i, w i != 0) ∧ Equivalent Q (weightedSumSquares Real fun i => (w i : Real)) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  ⟨sign ∘ ((↑) : Realˣ -> Real) ∘ w, fun i => sign_ne_zero.2 (w i).ne_zero,
    ⟨hw₁.trans (isometryEquivSignWeightedSumSquares (((↑) : Realˣ -> Real) ∘ w))⟩⟩

/--
theorem `equivalent_one_neg_one_weighted_sum_squared` / 定理 `equivalent_one_neg_one_weighted_sum_squared`

English:
theorem equivalent_one_neg_one_weighted_sum_squared
  statement: {M : Type*} [AddCommGroup M] [Module Real M]
  proof: let ⟨w, hw₀, hw⟩ := Q.equivalent_sign_ne_zero_weighted_sum_squared hQ
  ⟨(w ·), fun i => by cases hi : w i <;> simp_all, hw⟩

中文:
定理 equivalent_one_neg_one_weighted_sum_squared
  结论: {M : 类型} [加法交换群 M] [模 实数 M]
  证明: let ⟨w, hw₀, hw⟩ := Q.equivalent_sign_ne_zero_weighted_sum_squared hQ
  ⟨(w ·), fun i => by cases hi : w i <;> simp_all, hw⟩

Depends on / 依赖: SeparatingLeft
-/
theorem equivalent_one_neg_one_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module Real M]
    [FiniteDimensional Real M] (Q : QuadraticForm Real M) (hQ : (associated (R := Real) Q).SeparatingLeft) :
    exists w : Fin (Module.finrank Real M) -> Real,
      (forall i, w i = -1 ∨ w i = 1) ∧ Equivalent Q (weightedSumSquares Real w) :=
  let ⟨w, hw₀, hw⟩ := Q.equivalent_sign_ne_zero_weighted_sum_squared hQ
  ⟨(w ·), fun i => by cases hi : w i <;> simp_all, hw⟩

/--
theorem `equivalent_signType_weighted_sum_squared` / 定理 `equivalent_signType_weighted_sum_squared`

English:
theorem equivalent_signType_weighted_sum_squared
  statement: {M : Type*} [AddCommGroup M] [Module Real M]
  proof: let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares
  ⟨sign ∘ w, ⟨hw₁.trans (isometryEquivSignWeightedSumSquares w)⟩⟩

中文:
定理 equivalent_signType_weighted_sum_squared
  结论: {M : 类型} [加法交换群 M] [模 实数 M]
  证明: let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares
  ⟨sign ∘ w, ⟨hw₁.trans (isometryEquivSignWeightedSumSquares w)⟩⟩

Depends on / 依赖: Q.equivalent_weightedSumSquares, equivalent_weightedSumSquares, isometryEquivSignWeightedSumSquares
-/
theorem equivalent_signType_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module Real M]
    [FiniteDimensional Real M] (Q : QuadraticForm Real M) :
    exists w : Fin (Module.finrank Real M) -> SignType,
      Equivalent Q (weightedSumSquares Real fun i => (w i : Real)) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares
  ⟨sign ∘ w, ⟨hw₁.trans (isometryEquivSignWeightedSumSquares w)⟩⟩

/--
theorem `equivalent_one_zero_neg_one_weighted_sum_squared` / 定理 `equivalent_one_zero_neg_one_weighted_sum_squared`

English:
theorem equivalent_one_zero_neg_one_weighted_sum_squared
  statement: {M : Type*} [AddCommGroup M] [Module Real M]
  proof: let ⟨w, hw⟩ := Q.equivalent_signType_weighted_sum_squared
  ⟨(w ·), fun i => by cases h : w i <;> simp [h], hw⟩

中文:
定理 equivalent_one_zero_neg_one_weighted_sum_squared
  结论: {M : 类型} [加法交换群 M] [模 实数 M]
  证明: let ⟨w, hw⟩ := Q.equivalent_signType_weighted_sum_squared
  ⟨(w ·), fun i => by cases h : w i <;> simp [h], hw⟩

Depends on / 依赖: Q.equivalent_signType_weighted_sum_squared, equivalent_signType_weighted_sum_squared
-/
theorem equivalent_one_zero_neg_one_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module Real M]
    [FiniteDimensional Real M] (Q : QuadraticForm Real M) :
    exists w : Fin (Module.finrank Real M) -> Real,
      (forall i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧ Equivalent Q (weightedSumSquares Real w) :=
  let ⟨w, hw⟩ := Q.equivalent_signType_weighted_sum_squared
  ⟨(w ·), fun i => by cases h : w i <;> simp [h], hw⟩

end QuadraticForm
