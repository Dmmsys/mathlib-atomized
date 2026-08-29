/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change of polynomial algebras

Given `[CommSemiring R] [Semiring A] [Algebra R A]` we show `A[X] ≃ₐ[R] (A ⊗[R] R[X])`.
-/

@[expose] public section

-- This file should not become entangled with `RingTheory/MatrixAlgebra`.
assert_not_exists Matrix

universe u v w

open Polynomial TensorProduct

open Algebra.TensorProduct (algHomOfLinearMapTensorProduct includeLeft)

noncomputable section

variable (R S A : Type*)
variable [CommSemiring R] [CommSemiring S]
variable [Semiring A] [Algebra R A] [Algebra R S] [Algebra S A] [IsScalarTower R S A]

namespace PolyEquivTensor

/--
Definition of `toFunBilinear` / `toFunBilinear` 的定义

English:
definition toFunBilinear
  signature: : A ->ₗ[A] R[X] ->ₗ[R] A[X]
  body: LinearMap.toSpanSingleton A _ (aeval (Polynomial.X : A[X])).toLinearMap

中文:
定义 toFunBilinear
  签名: : A ->ₗ[A] R[X] ->ₗ[R] A[X]
  定义体: LinearMap.toSpanSingleton A _ (aeval (Polynomial.X : A[X])).toLinearMap

Depends on / 依赖: LinearMap, LinearMap.toSpanSingleton, Polynomial, Polynomial.X, toLinearMap, toSpanSingleton
-/
def toFunBilinear : A ->ₗ[A] R[X] ->ₗ[R] A[X] :=
  LinearMap.toSpanSingleton A _ (aeval (Polynomial.X : A[X])).toLinearMap

/--
theorem `toFunBilinear_apply_apply` / 定理 `toFunBilinear_apply_apply`

English:
theorem toFunBilinear_apply_apply
  given: (a : A) (p : R[X])
  proof: rfl

中文:
定理 toFunBilinear_apply_apply
  条件: (a : A) (p : R[X])
  证明: rfl
-/
theorem toFunBilinear_apply_apply (a : A) (p : R[X]) :
    toFunBilinear R A a p = a • (aeval X) p := rfl

/--
theorem `toFunBilinear_apply_eq_smul` / 定理 `toFunBilinear_apply_eq_smul`

English:
theorem toFunBilinear_apply_eq_smul
  given: (a : A) (p : R[X])
  proof: rfl

中文:
定理 toFunBilinear_apply_eq_smul
  条件: (a : A) (p : R[X])
  证明: rfl
-/
@[simp] theorem toFunBilinear_apply_eq_smul (a : A) (p : R[X]) :
    toFunBilinear R A a p = a • p.map (algebraMap R A) := rfl

/--
theorem `toFunBilinear_apply_eq_sum` / 定理 `toFunBilinear_apply_eq_sum`

English:
theorem toFunBilinear_apply_eq_sum
  given: (a : A) (p : R[X])
  proof: by
  conv_lhs => rw [toFunBilinear_apply_eq_smul, ← p.sum_monomial_eq, sum, Polynomial.map_sum]
  simp [Finset.smul_sum, sum, ← smul_eq_mul]

中文:
定理 toFunBilinear_apply_eq_sum
  条件: (a : A) (p : R[X])
  证明: by
  conv_lhs => rw [toFunBilinear_apply_eq_smul, ← p.sum_monomial_eq, sum, Polynomial.map_sum]
  simp [Finset.smul_sum, sum, ← smul_eq_mul]

Depends on / 依赖: Finset, Finset.smul_sum, Polynomial, Polynomial.map_sum, conv_lhs, map_sum, p.sum_monomial_eq, smul_eq_mul, smul_sum, sum_monomial_eq, toFunBilinear_apply_eq_smul
-/
theorem toFunBilinear_apply_eq_sum (a : A) (p : R[X]) :
    toFunBilinear R A a p = p.sum fun n r => monomial n (a * algebraMap R A r) := by
  conv_lhs => rw [toFunBilinear_apply_eq_smul, ← p.sum_monomial_eq, sum, Polynomial.map_sum]
  simp [Finset.smul_sum, sum, ← smul_eq_mul]

/--
Definition of `toFunLinear` / `toFunLinear` 的定义

English:
definition toFunLinear
  signature: : A otimes[R] R[X] ->ₗ[R] A[X]
  body: TensorProduct.lift (toFunBilinear R A)

@[simp]

中文:
定义 toFunLinear
  签名: : A otimes[R] R[X] ->ₗ[R] A[X]
  定义体: TensorProduct.lift (toFunBilinear R A)

@[simp]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, TensorProduct, TensorProduct.lift, algebraMap_injective, faithfulSMul_iff_algebraMap_injective, toFunBilinear
-/
def toFunLinear : A otimes[R] R[X] ->ₗ[R] A[X] :=
  TensorProduct.lift (toFunBilinear R A)

@[simp]
/--
theorem `toFunLinear_tmul_apply` / 定理 `toFunLinear_tmul_apply`

English:
theorem toFunLinear_tmul_apply
  given: (a : A) (p : R[X])
  proof: rfl

中文:
定理 toFunLinear_tmul_apply
  条件: (a : A) (p : R[X])
  证明: rfl
-/
theorem toFunLinear_tmul_apply (a : A) (p : R[X]) :
    toFunLinear R A (a otimesₜ[R] p) = toFunBilinear R A a p :=
  rfl

-- We apparently need to provide the decidable instance here
-- in order to successfully rewrite by this lemma.
/--
theorem `toFunLinear_mul_tmul_mul_aux_1` / 定理 `toFunLinear_mul_tmul_mul_aux_1`

English:
theorem toFunLinear_mul_tmul_mul_aux_1
  given: (p : R[X]) (k : Nat) (h : Decidable ¬p.coeff k = 0) (a : A)
  proof: by split_ifs <;> simp [*]

中文:
定理 toFunLinear_mul_tmul_mul_aux_1
  条件: (p : R[X]) (k : 自然数) (h : 可判定 ¬p.coeff k = 0) (a : A)
  证明: by split_ifs <;> simp [*]

Depends on / 依赖: split_ifs
-/
theorem toFunLinear_mul_tmul_mul_aux_1 (p : R[X]) (k : Nat) (h : Decidable ¬p.coeff k = 0) (a : A) :
    ite (¬coeff p k = 0) (a * (algebraMap R A) (coeff p k)) 0 =
    a * (algebraMap R A) (coeff p k) := by split_ifs <;> simp [*]

/--
theorem `toFunLinear_mul_tmul_mul_aux_2` / 定理 `toFunLinear_mul_tmul_mul_aux_2`

English:
theorem toFunLinear_mul_tmul_mul_aux_2
  given: (k : Nat) (a₁ a₂ : A) (p₁ p₂ : R[X])
  proof: by
  simp_rw [mul_assoc, Algebra.commutes, ← Finset.mul_sum, mul_assoc, ← Finset.mul_sum]
  congr
  simp_rw [Algebra.commutes (coeff p₂ _), coeff_mul, map_sum, map_mul]

中文:
定理 toFunLinear_mul_tmul_mul_aux_2
  条件: (k : 自然数) (a₁ a₂ : A) (p₁ p₂ : R[X])
  证明: by
  simp_rw [mul_assoc, Algebra.commutes, ← Finset.mul_sum, mul_assoc, ← Finset.mul_sum]
  congr
  simp_rw [Algebra.commutes (coeff p₂ _), coeff_mul, map_sum, map_mul]

Depends on / 依赖: Algebra, Algebra.commutes, Finset, Finset.mul_sum, coeff_mul, commutes, map_mul, map_sum, mul_assoc, mul_sum, simp_rw
-/
theorem toFunLinear_mul_tmul_mul_aux_2 (k : Nat) (a₁ a₂ : A) (p₁ p₂ : R[X]) :
    a₁ * a₂ * (algebraMap R A) ((p₁ * p₂).coeff k) =
      (Finset.antidiagonal k).sum fun x =>
        a₁ * (algebraMap R A) (coeff p₁ x.1) * (a₂ * (algebraMap R A) (coeff p₂ x.2)) := by
  simp_rw [mul_assoc, Algebra.commutes, ← Finset.mul_sum, mul_assoc, ← Finset.mul_sum]
  congr
  simp_rw [Algebra.commutes (coeff p₂ _), coeff_mul, map_sum, map_mul]

/--
theorem `toFunLinear_mul_tmul_mul` / 定理 `toFunLinear_mul_tmul_mul`

English:
theorem toFunLinear_mul_tmul_mul
  given: (a₁ a₂ : A) (p₁ p₂ : R[X])
  proof: by
  classical
    simp only [toFunLinear_tmul_apply, toFunBilinear_apply_eq_sum]
    ext k
    simp_rw [coeff_sum, coeff_monomial, sum_def, Finset.sum_ite_eq', mem_support_iff, Ne]
    conv_rhs => rw [coeff_mul]
    simp_rw [finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq', mem_support_iff, Ne, 

中文:
定理 toFunLinear_mul_tmul_mul
  条件: (a₁ a₂ : A) (p₁ p₂ : R[X])
  证明: by
  classical
    simp only [toFunLinear_tmul_apply, toFunBilinear_apply_eq_sum]
    ext k
    simp_rw [coeff_sum, coeff_monomial, sum_def, Finset.sum_ite_eq', mem_support_iff, Ne]
    conv_rhs => rw [coeff_mul]
    simp_rw [finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq', mem_support_iff, Ne, 

Depends on / 依赖: Finset, Finset.sum_ite_eq, algebraMap, classical, coeff_monomial, coeff_mul, coeff_sum, conv_rhs, finsetSum_coeff, ite_mul, ite_zero_mul, mem_support_iff, mul_ite, mul_ite_zero, mul_zero, simp_rw, sum_def, sum_ite_eq, toFunBilinear_apply_eq_sum, toFunLinea
-/
theorem toFunLinear_mul_tmul_mul (a₁ a₂ : A) (p₁ p₂ : R[X]) :
    (toFunLinear R A) ((a₁ * a₂) otimesₜ[R] (p₁ * p₂)) =
      (toFunLinear R A) (a₁ otimesₜ[R] p₁) * (toFunLinear R A) (a₂ otimesₜ[R] p₂) := by
  classical
    simp only [toFunLinear_tmul_apply, toFunBilinear_apply_eq_sum]
    ext k
    simp_rw [coeff_sum, coeff_monomial, sum_def, Finset.sum_ite_eq', mem_support_iff, Ne]
    conv_rhs => rw [coeff_mul]
    simp_rw [finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq', mem_support_iff, Ne, mul_ite,
      mul_zero, ite_mul, zero_mul]
    simp_rw [← ite_zero_mul (¬coeff p₁ _ = 0) (a₁ * (algebraMap R A) (coeff p₁ _))]
    simp_rw [← mul_ite_zero (¬coeff p₂ _ = 0) _ (_ * _)]
    simp_rw [toFunLinear_mul_tmul_mul_aux_1, toFunLinear_mul_tmul_mul_aux_2]

/--
theorem `toFunLinear_one_tmul_one` / 定理 `toFunLinear_one_tmul_one`

English:
theorem toFunLinear_one_tmul_one
  proof: by
  rw [toFunLinear_tmul_apply]; rw [toFunBilinear_apply_apply]; rw [Polynomial.aeval_one]; rw [one_smul]

中文:
定理 toFunLinear_one_tmul_one
  证明: by
  rw [toFunLinear_tmul_apply]; rw [toFunBilinear_apply_apply]; rw [Polynomial.aeval_one]; rw [one_smul]

Depends on / 依赖: Polynomial, Polynomial.aeval_one, aeval_one, one_smul, toFunBilinear_apply_apply, toFunLinear_tmul_apply
-/
theorem toFunLinear_one_tmul_one :
    toFunLinear R A (1 otimesₜ[R] 1) = 1 := by
  rw [toFunLinear_tmul_apply]; rw [toFunBilinear_apply_apply]; rw [Polynomial.aeval_one]; rw [one_smul]

/--
Definition of `toFunAlgHom` / `toFunAlgHom` 的定义

English:
definition toFunAlgHom
  signature: : A otimes[R] R[X] ->ₐ[R] A[X]
  body: algHomOfLinearMapTensorProduct (toFunLinear R A) (toFunLinear_mul_tmul_mul R A)
    (toFunLinear_one_tmul_one R A)

中文:
定义 toFunAlgHom
  签名: : A otimes[R] R[X] ->ₐ[R] A[X]
  定义体: algHomOfLinearMapTensorProduct (toFunLinear R A) (toFunLinear_mul_tmul_mul R A)
    (toFunLinear_one_tmul_one R A)

Depends on / 依赖: algHomOfLinearMapTensorProduct, toFunLinear, toFunLinear_mul_tmul_mul, toFunLinear_one_tmul_one
-/
def toFunAlgHom : A otimes[R] R[X] ->ₐ[R] A[X] :=
  algHomOfLinearMapTensorProduct (toFunLinear R A) (toFunLinear_mul_tmul_mul R A)
    (toFunLinear_one_tmul_one R A)

/--
theorem `toFunAlgHom_apply_tmul_eq_smul` / 定理 `toFunAlgHom_apply_tmul_eq_smul`

English:
theorem toFunAlgHom_apply_tmul_eq_smul
  given: (a : A) (p : R[X])
  proof: rfl

中文:
定理 toFunAlgHom_apply_tmul_eq_smul
  条件: (a : A) (p : R[X])
  证明: rfl
-/
@[simp] theorem toFunAlgHom_apply_tmul_eq_smul (a : A) (p : R[X]) :
    toFunAlgHom R A (a otimesₜ[R] p) = a • p.map (algebraMap R A) := rfl

/--
theorem `toFunAlgHom_apply_tmul` / 定理 `toFunAlgHom_apply_tmul`

English:
theorem toFunAlgHom_apply_tmul
  given: (a : A) (p : R[X])
  proof: toFunBilinear_apply_eq_sum R A _ _

中文:
定理 toFunAlgHom_apply_tmul
  条件: (a : A) (p : R[X])
  证明: toFunBilinear_apply_eq_sum R A _ _

Depends on / 依赖: toFunBilinear_apply_eq_sum
-/
theorem toFunAlgHom_apply_tmul (a : A) (p : R[X]) :
    toFunAlgHom R A (a otimesₜ[R] p) = p.sum fun n r => monomial n (a * (algebraMap R A) r) :=
  toFunBilinear_apply_eq_sum R A _ _

/--
Definition of `invFun` / `invFun` 的定义

English:
definition invFun
  signature: (p : A[X])
  body: p.eval₂ (includeLeft : A ->ₐ[R] A otimes[R] R[X]) ((1 : A) otimesₜ[R] (X : R[X]))

@[simp]

中文:
定义 invFun
  签名: (p : A[X])
  定义体: p.eval₂ (includeLeft : A ->ₐ[R] A otimes[R] R[X]) ((1 : A) otimesₜ[R] (X : R[X]))

@[simp]

Depends on / 依赖: includeLeft, otimes, p.eval
-/
def invFun (p : A[X]) : A otimes[R] R[X] :=
  p.eval₂ (includeLeft : A ->ₐ[R] A otimes[R] R[X]) ((1 : A) otimesₜ[R] (X : R[X]))

@[simp]
/--
theorem `invFun_add` / 定理 `invFun_add`

English:
theorem invFun_add
  given: {p q}
  statement: invFun R A (p + q) = invFun R A p + invFun R A q
  proof: by
  simp only [invFun, eval₂_add]

中文:
定理 invFun_add
  条件: {p q}
  结论: invFun R A (p + q) = invFun R A p + invFun R A q
  证明: by
  simp only [invFun, eval₂_add]

Depends on / 依赖: invFun
-/
theorem invFun_add {p q} : invFun R A (p + q) = invFun R A p + invFun R A q := by
  simp only [invFun, eval₂_add]

/--
theorem `invFun_monomial` / 定理 `invFun_monomial`

English:
theorem invFun_monomial
  given: (n : Nat) (a : A)
  proof: eval₂_monomial _ _

中文:
定理 invFun_monomial
  条件: (n : 自然数) (a : A)
  证明: eval₂_monomial _ _
-/
theorem invFun_monomial (n : Nat) (a : A) :
    invFun R A (monomial n a) = (a otimesₜ[R] 1) * 1 otimesₜ[R] X ^ n :=
  eval₂_monomial _ _

/--
theorem `left_inv` / 定理 `left_inv`

English:
theorem left_inv
  given: (x : A otimes R[X])
  statement: invFun R A ((toFunAlgHom R A) x) = x
  proof: by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [invFun]
  · intro a p
    dsimp only [invFun]
    rw [toFunAlgHom_apply_tmul]; rw [eval₂_sum]
    simp_rw [eval₂_monomial, AlgHom.coe_toRingHom, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.includeLeft_apply, Algebra

中文:
定理 left_inv
  条件: (x : A otimes R[X])
  结论: invFun R A ((toFunAlgHom R A) x) = x
  证明: by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [invFun]
  · intro a p
    dsimp only [invFun]
    rw [toFunAlgHom_apply_tmul]; rw [eval₂_sum]
    simp_rw [eval₂_monomial, AlgHom.coe_toRingHom, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.includeLeft_apply, Algebra

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, Algebra, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_pow, Algebra.commutes, Algebra.smul_def, TensorProduct, TensorProduct.induction_on, coe_toRingHom, commutes, conv_rhs, includeLeft_apply, induction_on, invFun, mul_one, one_mul, one_pow, simp_rw
-/
theorem left_inv (x : A otimes R[X]) : invFun R A ((toFunAlgHom R A) x) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [invFun]
  · intro a p
    dsimp only [invFun]
    rw [toFunAlgHom_apply_tmul]; rw [eval₂_sum]
    simp_rw [eval₂_monomial, AlgHom.coe_toRingHom, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, ← Algebra.commutes, ← Algebra.smul_def, smul_tmul, sum_def, ← tmul_sum]
    conv_rhs => rw [← sum_C_mul_X_pow_eq p]
    simp only [Algebra.smul_def]
    rfl
  · intro p q hp hq
    simp only [map_add, invFun_add, hp, hq]

/--
theorem `right_inv` / 定理 `right_inv`

English:
theorem right_inv
  given: (x : A[X])
  statement: (toFunAlgHom R A) (invFun R A x) = x
  proof: by
  refine Polynomial.induction_on' x ?_ ?_
  · intro p q hp hq
    simp only [invFun_add, map_add, hp, hq]
  · intro n a
    rw [invFun_monomial]; rw [Algebra.TensorProduct.tmul_pow]; rw [one_pow]; rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [mul_one]; rw [one_mul]; rw [toFunAlgHom_apply_tmul]; r

中文:
定理 right_inv
  条件: (x : A[X])
  结论: (toFunAlgHom R A) (invFun R A x) = x
  证明: by
  refine Polynomial.induction_on' x ?_ ?_
  · intro p q hp hq
    simp only [invFun_add, map_add, hp, hq]
  · intro n a
    rw [invFun_monomial]; rw [Algebra.TensorProduct.tmul_pow]; rw [one_pow]; rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [mul_one]; rw [one_mul]; rw [toFunAlgHom_apply_tmul]; r

Depends on / 依赖: Algebra, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_pow, Polynomial, Polynomial.induction_on, TensorProduct, X_pow_eq_monomial, induction_on, invFun_add, invFun_monomial, map_add, mul_one, one_mul, one_pow, sum_monomial_index, tmul_mul_tmul, tmul_pow, toFunAlgHom_apply_tmul
-/
theorem right_inv (x : A[X]) : (toFunAlgHom R A) (invFun R A x) = x := by
  refine Polynomial.induction_on' x ?_ ?_
  · intro p q hp hq
    simp only [invFun_add, map_add, hp, hq]
  · intro n a
    rw [invFun_monomial]; rw [Algebra.TensorProduct.tmul_pow]; rw [one_pow]; rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [mul_one]; rw [one_mul]; rw [toFunAlgHom_apply_tmul]; rw [X_pow_eq_monomial]; rw [sum_monomial_index] <;>
      simp

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : A otimes[R] R[X] ≃ A[X] where
  body: toFunAlgHom R A
  invFun := invFun R A
  left_inv := left_inv R A
  right_inv := right_inv R A

中文:
定义 equiv
  签名: : A otimes[R] R[X] ≃ A[X] where
  定义体: toFunAlgHom R A
  invFun := invFun R A
  left_inv := left_inv R A
  right_inv := right_inv R A

Depends on / 依赖: toFunAlgHom
-/
def equiv : A otimes[R] R[X] ≃ A[X] where
  toFun := toFunAlgHom R A
  invFun := invFun R A
  left_inv := left_inv R A
  right_inv := right_inv R A

end PolyEquivTensor

open PolyEquivTensor

/--
Definition of `polyEquivTensor` / `polyEquivTensor` 的定义

English:
definition polyEquivTensor
  signature: : A[X] ≃ₐ[R] A otimes[R] R[X]
  body: AlgEquiv.symm { PolyEquivTensor.toFunAlgHom R A, PolyEquivTensor.equiv R A with }

@[simp]

中文:
定义 polyEquivTensor
  签名: : A[X] ≃ₐ[R] A otimes[R] R[X]
  定义体: AlgEquiv.symm { PolyEquivTensor.toFunAlgHom R A, PolyEquivTensor.equiv R A with }

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.symm, PolyEquivTensor, PolyEquivTensor.equiv, PolyEquivTensor.toFunAlgHom, toFunAlgHom
-/
def polyEquivTensor : A[X] ≃ₐ[R] A otimes[R] R[X] :=
  AlgEquiv.symm { PolyEquivTensor.toFunAlgHom R A, PolyEquivTensor.equiv R A with }

@[simp]
/--
theorem `polyEquivTensor_apply` / 定理 `polyEquivTensor_apply`

English:
theorem polyEquivTensor_apply
  given: (p : A[X])
  proof: rfl

@[simp]

中文:
定理 polyEquivTensor_apply
  条件: (p : A[X])
  证明: rfl

@[simp]
-/
theorem polyEquivTensor_apply (p : A[X]) :
    polyEquivTensor R A p =
      p.eval₂ (includeLeft : A ->ₐ[R] A otimes[R] R[X]) ((1 : A) otimesₜ[R] (X : R[X])) :=
  rfl

@[simp]
/--
theorem `polyEquivTensor_symm_apply_tmul_eq_smul` / 定理 `polyEquivTensor_symm_apply_tmul_eq_smul`

English:
theorem polyEquivTensor_symm_apply_tmul_eq_smul
  given: (a : A) (p : R[X])
  proof: rfl

中文:
定理 polyEquivTensor_symm_apply_tmul_eq_smul
  条件: (a : A) (p : R[X])
  证明: rfl

Depends on / 依赖: x.ofVal
-/
theorem polyEquivTensor_symm_apply_tmul_eq_smul (a : A) (p : R[X]) :
    (polyEquivTensor R A).symm (a otimesₜ p) = a • p.map (algebraMap R A) := rfl

/--
theorem `polyEquivTensor_symm_apply_tmul` / 定理 `polyEquivTensor_symm_apply_tmul`

English:
theorem polyEquivTensor_symm_apply_tmul
  given: (a : A) (p : R[X])
  proof: toFunAlgHom_apply_tmul _ _ _ _

中文:
定理 polyEquivTensor_symm_apply_tmul
  条件: (a : A) (p : R[X])
  证明: toFunAlgHom_apply_tmul _ _ _ _

Depends on / 依赖: toFunAlgHom_apply_tmul
-/
theorem polyEquivTensor_symm_apply_tmul (a : A) (p : R[X]) :
    (polyEquivTensor R A).symm (a otimesₜ p) = p.sum fun n r => monomial n (a * algebraMap R A r) :=
  toFunAlgHom_apply_tmul _ _ _ _

section

variable (A : Type*) [CommSemiring A] [Algebra R A]

/--
Definition of `polyEquivTensor'` / `polyEquivTensor'` 的定义

English:
definition polyEquivTensor'
  signature: : A[X] ≃ₐ[A] A otimes[R] R[X] where
  body: polyEquivTensor R A
  commutes' a := by simp

中文:
定义 polyEquivTensor'
  签名: : A[X] ≃ₐ[A] A otimes[R] R[X] where
  定义体: polyEquivTensor R A
  commutes' a := by simp

Depends on / 依赖: polyEquivTensor
-/
def polyEquivTensor' : A[X] ≃ₐ[A] A otimes[R] R[X] where
  __ := polyEquivTensor R A
  commutes' a := by simp

/--
theorem `coe_polyEquivTensor'` / 定理 `coe_polyEquivTensor'`

English:
theorem coe_polyEquivTensor'
  statement: ⇑(polyEquivTensor' R A) = polyEquivTensor R A
  proof: rfl

中文:
定理 coe_polyEquivTensor'
  结论: ⇑(polyEquivTensor' R A) = polyEquivTensor R A
  证明: rfl
-/
@[simp] theorem coe_polyEquivTensor' : ⇑(polyEquivTensor' R A) = polyEquivTensor R A := rfl

/--
theorem `coe_polyEquivTensor'_symm` / 定理 `coe_polyEquivTensor'_symm`

English:
theorem coe_polyEquivTensor'_symm
  proof: rfl

中文:
定理 coe_polyEquivTensor'_symm
  证明: rfl
-/
@[simp] theorem coe_polyEquivTensor'_symm :
    ⇑(polyEquivTensor' R A).symm = (polyEquivTensor R A).symm := rfl

end

/--
Definition of `Polynomial.algebra` / `Polynomial.algebra` 的定义

English:
definition Polynomial.algebra
  signature: : Algebra R[X] A[X]
  body: (mapRingHom (algebraMap R A)).toAlgebra' fun _ _ => by
    ext; rw [coeff_mul, ← Finset.Nat.sum_antidiagonal_swap, coeff_mul]; simp [Algebra.commutes]

中文:
定义 多项式.algebra
  签名: : 代数 R[X] A[X]
  定义体: (mapRingHom (algebraMap R A)).toAlgebra' fun _ _ => by
    ext; rw [coeff_mul, ← Finset.Nat.sum_antidiagonal_swap, coeff_mul]; simp [Algebra.commutes]
-/
@[reducible] def Polynomial.algebra : Algebra R[X] A[X] :=
  (mapRingHom (algebraMap R A)).toAlgebra' fun _ _ => by
    ext; rw [coeff_mul, ← Finset.Nat.sum_antidiagonal_swap, coeff_mul]; simp [Algebra.commutes]

attribute [local instance] Polynomial.algebra

@[simp]
/--
theorem `Polynomial.algebraMap_def` / 定理 `Polynomial.algebraMap_def`

English:
theorem Polynomial.algebraMap_def
  statement: algebraMap R[X] A[X] = mapRingHom (algebraMap R A)
  proof: rfl

中文:
定理 多项式.algebraMap_def
  结论: algebraMap R[X] A[X] = mapRingHom (algebraMap R A)
  证明: rfl
-/
theorem Polynomial.algebraMap_def : algebraMap R[X] A[X] = mapRingHom (algebraMap R A) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R S[X] A[X]
  body: have : IsScalarTower S S[X] A[X] := .of_algebraMap_eq' (mapRingHom_comp_C _).symm
  .to₁₃₄ _ S _ _

中文:
实例 :
  签名: 标量塔 R S[X] A[X]
  定义体: have : IsScalarTower S S[X] A[X] := .of_algebraMap_eq' (mapRingHom_comp_C _).symm
  .to₁₃₄ _ S _ _

Depends on / 依赖: IsScalarTower, mapRingHom_comp_C, of_algebraMap_eq
-/
instance : IsScalarTower R S[X] A[X] :=
  have : IsScalarTower S S[X] A[X] := .of_algebraMap_eq' (mapRingHom_comp_C _).symm
  .to₁₃₄ _ S _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R[X] S[X] A[X]
  body: .of_algebraMap_eq'
  congr(mapRingHom $(IsScalarTower.algebraMap_eq R S A)).trans (mapRingHom_comp ..).symm

中文:
实例 :
  签名: 标量塔 R[X] S[X] A[X]
  定义体: .of_algebraMap_eq'
  congr(mapRingHom $(IsScalarTower.algebraMap_eq R S A)).trans (mapRingHom_comp ..).symm

Depends on / 依赖: of_algebraMap_eq
-/
instance : IsScalarTower R[X] S[X] A[X] := .of_algebraMap_eq'
  congr(mapRingHom $(IsScalarTower.algebraMap_eq R S A)).trans (mapRingHom_comp ..).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FaithfulSMul
  signature: R A] : FaithfulSMul R[X] A[X]
  body: (faithfulSMul_iff_algebraMap_injective ..).mpr
    (map_injective _ <| FaithfulSMul.algebraMap_injective ..)

中文:
实例 [忠实标量乘法
  签名: R A] : 忠实标量乘法 R[X] A[X]
  定义体: (faithfulSMul_iff_algebraMap_injective ..).mpr
    (map_injective _ <| FaithfulSMul.algebraMap_injective ..)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, faithfulSMul_iff_algebraMap_injective, map_injective
-/
instance [FaithfulSMul R A] : FaithfulSMul R[X] A[X] :=
  (faithfulSMul_iff_algebraMap_injective ..).mpr
    (map_injective _ <| FaithfulSMul.algebraMap_injective ..)

variable {S : Type*} [CommSemiring S] [Algebra R S]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.IsPushout R S R[X] S[X]
  body: .of_equiv (polyEquivTensor' R S).symm fun _ =>
(polyEquivTensor_symm_apply_tmul_eq_smul ..).trans one_smul ..

中文:
实例 :
  签名: 代数.是推出 R S R[X] S[X]
  定义体: .of_equiv (polyEquivTensor' R S).symm fun _ =>
(polyEquivTensor_symm_apply_tmul_eq_smul ..).trans one_smul ..

Depends on / 依赖: of_equiv, polyEquivTensor
-/
instance : Algebra.IsPushout R S R[X] S[X] where
  out := .of_equiv (polyEquivTensor' R S).symm fun _ =>
(polyEquivTensor_symm_apply_tmul_eq_smul ..).trans one_smul ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.IsPushout R R[X] S S[X]
  body: .symm inferInstance

中文:
实例 :
  签名: 代数.是推出 R R[X] S S[X]
  定义体: .symm inferInstance
-/
instance : Algebra.IsPushout R R[X] S S[X] := .symm inferInstance
