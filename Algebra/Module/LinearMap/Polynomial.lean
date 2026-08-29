/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Characteristic polynomials of linear families of endomorphisms

The coefficients of the characteristic polynomials of a linear family of endomorphisms
are homogeneous polynomials in the parameters.
This result is used in Lie theory
to establish the existence of regular elements and Cartan subalgebras,
and ultimately a well-defined notion of rank for Lie algebras.

In this file we prove this result about characteristic polynomials.
Let `L` and `M` be modules over a nontrivial commutative ring `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear map.
Let `b` be a basis of `L`, indexed by `ι`.
Then we define a multivariate polynomial with variables indexed by `ι`
that evaluates on elements `x` of `L` to the characteristic polynomial of `φ x`.

## Main declarations

* `Matrix.toMvPolynomial M i`: the family of multivariate polynomials that evaluates on `c : n → R`
  to the dot product of the `i`-th row of `M` with `c`.
  `Matrix.toMvPolynomial M i` is the sum of the monomials `C (M i j) * X j`.
* `LinearMap.toMvPolynomial b₁ b₂ f`: a version of `Matrix.toMvPolynomial` for linear maps `f`
  with respect to bases `b₁` and `b₂` of the domain and codomain.
* `LinearMap.polyCharpoly`: the multivariate polynomial that evaluates on elements `x` of `L`
  to the characteristic polynomial of `φ x`.
* `LinearMap.polyCharpoly_map_eq_charpoly`: the evaluation of `polyCharpoly` on elements `x` of `L`
  is the characteristic polynomial of `φ x`.
* `LinearMap.polyCharpoly_coeff_isHomogeneous`: the coefficients of `polyCharpoly`
  are homogeneous polynomials in the parameters.
* `LinearMap.nilRank`: the smallest index at which `polyCharpoly` has a non-zero coefficient,
  which is independent of the choice of basis for `L`.
* `LinearMap.IsNilRegular`: an element `x` of `L` is *nil-regular* with respect to `φ`
  if the `n`-th coefficient of the characteristic polynomial of `φ x` is non-zero,
  where `n` denotes the nil-rank of `φ`.

## Implementation details

We show that `LinearMap.polyCharpoly` does not depend on the choice of basis of the target module.
This is done via `LinearMap.polyCharpoly_eq_polyCharpolyAux`
and `LinearMap.polyCharpolyAux_basisIndep`.
The latter is proven by considering
the base change of the `R`-linear map `φ : L →ₗ[R] End R M`
to the multivariate polynomial ring `MvPolynomial ι R`,
and showing that `polyCharpolyAux φ` is equal to the characteristic polynomial of this base change.
The proof concludes because characteristic polynomials are independent of the chosen basis.

## References

* [barnes1967]: "On Cartan subalgebras of Lie algebras" by D.W. Barnes.

-/

@[expose] public section

open Module MvPolynomial
open scoped Matrix

namespace Matrix

variable {m n o R S : Type*}
variable [Fintype n] [Fintype o] [CommSemiring R] [CommSemiring S]

/-- Let `M` be an `(m × n)`-matrix over `R`.
Then `Matrix.toMvPolynomial M` is the family (indexed by `i : m`)
of multivariate polynomials in `n` variables over `R` that evaluates on `c : n → R`
to the dot product of the `i`-th row of `M` with `c`:
`Matrix.toMvPolynomial M i` is the sum of the monomials `C (M i j) * X j`. -/
noncomputable
/--
Definition of `toMvPolynomial` / `toMvPolynomial` 的定义

English:
definition toMvPolynomial
  signature: (M : Matrix m n R) (i : m)
  body: ∑ j, monomial (.single j 1) (M i j)

中文:
定义 toMvPolynomial
  签名: (M : Matrix m n R) (i : m)
  定义体: ∑ j, monomial (.single j 1) (M i j)

Depends on / 依赖: monomial, single
-/
def toMvPolynomial (M : Matrix m n R) (i : m) : MvPolynomial n R :=
  ∑ j, monomial (.single j 1) (M i j)

/--
lemma `toMvPolynomial_eval_eq_apply` / 引理 `toMvPolynomial_eval_eq_apply`

English:
lemma toMvPolynomial_eval_eq_apply
  given: (M : Matrix m n R) (i : m) (c : n -> R)
  proof: by
  simp only [toMvPolynomial, map_sum, eval_monomial, pow_zero, Finsupp.prod_single_index, pow_one,
    mulVec, dotProduct]

中文:
引理 toMvPolynomial_eval_eq_apply
  条件: (M : Matrix m n R) (i : m) (c : n -> R)
  证明: by
  simp only [toMvPolynomial, map_sum, eval_monomial, pow_zero, Finsupp.prod_single_index, pow_one,
    mulVec, dotProduct]

Depends on / 依赖: Finsupp, Finsupp.prod_single_index, dotProduct, eval_monomial, map_sum, mulVec, pow_one, pow_zero, prod_single_index, toMvPolynomial
-/
lemma toMvPolynomial_eval_eq_apply (M : Matrix m n R) (i : m) (c : n -> R) :
    eval c (M.toMvPolynomial i) = (M *ᵥ c) i := by
  simp only [toMvPolynomial, map_sum, eval_monomial, pow_zero, Finsupp.prod_single_index, pow_one,
    mulVec, dotProduct]

/--
lemma `toMvPolynomial_map` / 引理 `toMvPolynomial_map`

English:
lemma toMvPolynomial_map
  given: (f : R ->+* S) (M : Matrix m n R) (i : m)
  proof: by
  simp only [toMvPolynomial, map_apply, map_sum, map_monomial]

中文:
引理 toMvPolynomial_map
  条件: (f : R ->+* S) (M : Matrix m n R) (i : m)
  证明: by
  simp only [toMvPolynomial, map_apply, map_sum, map_monomial]

Depends on / 依赖: map_apply, map_monomial, map_sum, toMvPolynomial
-/
lemma toMvPolynomial_map (f : R ->+* S) (M : Matrix m n R) (i : m) :
    (M.map f).toMvPolynomial i = MvPolynomial.map f (M.toMvPolynomial i) := by
  simp only [toMvPolynomial, map_apply, map_sum, map_monomial]

/--
lemma `toMvPolynomial_isHomogeneous` / 引理 `toMvPolynomial_isHomogeneous`

English:
lemma toMvPolynomial_isHomogeneous
  given: (M : Matrix m n R) (i : m)
  proof: by
  apply MvPolynomial.IsHomogeneous.sum
  rintro j -
  apply MvPolynomial.isHomogeneous_monomial _ _
  simp

中文:
引理 toMvPolynomial_isHomogeneous
  条件: (M : Matrix m n R) (i : m)
  证明: by
  apply MvPolynomial.IsHomogeneous.sum
  rintro j -
  apply MvPolynomial.isHomogeneous_monomial _ _
  simp

Depends on / 依赖: IsHomogeneous, MvPolynomial, MvPolynomial.IsHomogeneous.sum, MvPolynomial.isHomogeneous_monomial, isHomogeneous_monomial
-/
lemma toMvPolynomial_isHomogeneous (M : Matrix m n R) (i : m) :
    (M.toMvPolynomial i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  rintro j -
  apply MvPolynomial.isHomogeneous_monomial _ _
  simp

/--
lemma `toMvPolynomial_totalDegree_le` / 引理 `toMvPolynomial_totalDegree_le`

English:
lemma toMvPolynomial_totalDegree_le
  given: (M : Matrix m n R) (i : m)
  proof: by
  apply (toMvPolynomial_isHomogeneous _ _).totalDegree_le

@[simp]

中文:
引理 toMvPolynomial_totalDegree_le
  条件: (M : Matrix m n R) (i : m)
  证明: by
  apply (toMvPolynomial_isHomogeneous _ _).totalDegree_le

@[simp]

Depends on / 依赖: toMvPolynomial_isHomogeneous, totalDegree_le
-/
lemma toMvPolynomial_totalDegree_le (M : Matrix m n R) (i : m) :
    (M.toMvPolynomial i).totalDegree <= 1 := by
  apply (toMvPolynomial_isHomogeneous _ _).totalDegree_le

@[simp]
/--
lemma `toMvPolynomial_constantCoeff` / 引理 `toMvPolynomial_constantCoeff`

English:
lemma toMvPolynomial_constantCoeff
  given: (M : Matrix m n R) (i : m)
  proof: by
  simp only [toMvPolynomial, ← C_mul_X_eq_monomial, map_sum, map_mul, constantCoeff_X,
    mul_zero, Finset.sum_const_zero]

@[simp]

中文:
引理 toMvPolynomial_constantCoeff
  条件: (M : Matrix m n R) (i : m)
  证明: by
  simp only [toMvPolynomial, ← C_mul_X_eq_monomial, map_sum, map_mul, constantCoeff_X,
    mul_zero, Finset.sum_const_zero]

@[simp]

Depends on / 依赖: C_mul_X_eq_monomial, Finset, Finset.sum_const_zero, constantCoeff_X, map_mul, map_sum, mul_zero, sum_const_zero, toMvPolynomial
-/
lemma toMvPolynomial_constantCoeff (M : Matrix m n R) (i : m) :
    constantCoeff (M.toMvPolynomial i) = 0 := by
  simp only [toMvPolynomial, ← C_mul_X_eq_monomial, map_sum, map_mul, constantCoeff_X,
    mul_zero, Finset.sum_const_zero]

@[simp]
/--
lemma `toMvPolynomial_zero` / 引理 `toMvPolynomial_zero`

English:
lemma toMvPolynomial_zero
  statement: (0 : Matrix m n R).toMvPolynomial = 0
  proof: by
  ext; simp only [toMvPolynomial, zero_apply, map_zero, Finset.sum_const_zero, Pi.zero_apply]

@[simp]

中文:
引理 toMvPolynomial_zero
  结论: (0 : Matrix m n R).toMvPolynomial = 0
  证明: by
  ext; simp only [toMvPolynomial, zero_apply, map_zero, Finset.sum_const_zero, Pi.zero_apply]

@[simp]

Depends on / 依赖: Finset, Finset.sum_const_zero, Pi.zero_apply, map_zero, sum_const_zero, toMvPolynomial, zero_apply
-/
lemma toMvPolynomial_zero : (0 : Matrix m n R).toMvPolynomial = 0 := by
  ext; simp only [toMvPolynomial, zero_apply, map_zero, Finset.sum_const_zero, Pi.zero_apply]

@[simp]
/--
lemma `toMvPolynomial_one` / 引理 `toMvPolynomial_one`

English:
lemma toMvPolynomial_one
  given: [DecidableEq n]
  statement: (1 : Matrix n n R).toMvPolynomial = X
  proof: by
  ext i : 1
  rw [toMvPolynomial]; rw [Finset.sum_eq_single i]
  · simp only [one_apply_eq, ← C_mul_X_eq_monomial, C_1, one_mul]
  · rintro j - hj
    simp only [one_apply_ne hj.symm, map_zero]
  · grind

中文:
引理 toMvPolynomial_one
  条件: [DecidableEq n]
  结论: (1 : Matrix n n R).toMvPolynomial = X
  证明: by
  ext i : 1
  rw [toMvPolynomial]; rw [Finset.sum_eq_single i]
  · simp only [one_apply_eq, ← C_mul_X_eq_monomial, C_1, one_mul]
  · rintro j - hj
    simp only [one_apply_ne hj.symm, map_zero]
  · grind

Depends on / 依赖: C_mul_X_eq_monomial, Finset, Finset.sum_eq_single, hj.symm, map_zero, one_apply_eq, one_apply_ne, one_mul, sum_eq_single, toMvPolynomial
-/
lemma toMvPolynomial_one [DecidableEq n] : (1 : Matrix n n R).toMvPolynomial = X := by
  ext i : 1
  rw [toMvPolynomial]; rw [Finset.sum_eq_single i]
  · simp only [one_apply_eq, ← C_mul_X_eq_monomial, C_1, one_mul]
  · rintro j - hj
    simp only [one_apply_ne hj.symm, map_zero]
  · grind

/--
lemma `toMvPolynomial_add` / 引理 `toMvPolynomial_add`

English:
lemma toMvPolynomial_add
  given: (M N : Matrix m n R)
  proof: by
  ext i : 1
  simp only [toMvPolynomial, add_apply, map_add, Finset.sum_add_distrib, Pi.add_apply]

中文:
引理 toMvPolynomial_add
  条件: (M N : Matrix m n R)
  证明: by
  ext i : 1
  simp only [toMvPolynomial, add_apply, map_add, Finset.sum_add_distrib, Pi.add_apply]

Depends on / 依赖: Finset, Finset.sum_add_distrib, Pi.add_apply, add_apply, map_add, sum_add_distrib, toMvPolynomial
-/
lemma toMvPolynomial_add (M N : Matrix m n R) :
    (M + N).toMvPolynomial = M.toMvPolynomial + N.toMvPolynomial := by
  ext i : 1
  simp only [toMvPolynomial, add_apply, map_add, Finset.sum_add_distrib, Pi.add_apply]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `toMvPolynomial_mul` / 引理 `toMvPolynomial_mul`

English:
lemma toMvPolynomial_mul
  given: (M : Matrix m n R) (N : Matrix n o R) (i : m)
  proof: by
  simp only [toMvPolynomial, mul_apply, map_sum, Finset.sum_comm (γ := o), bind₁, aeval,
    AlgHom.coe_mk, coe_eval₂Hom, eval₂_monomial, algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, C_apply, pow_zero, Finsupp.prod_single_index, pow_one, Finset.mul_sum,
    monomial_mul, zero_

中文:
引理 toMvPolynomial_mul
  条件: (M : Matrix m n R) (N : Matrix n o R) (i : m)
  证明: by
  simp only [toMvPolynomial, mul_apply, map_sum, Finset.sum_comm (γ := o), bind₁, aeval,
    AlgHom.coe_mk, coe_eval₂Hom, eval₂_monomial, algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, C_apply, pow_zero, Finsupp.prod_single_index, pow_one, Finset.mul_sum,
    monomial_mul, zero_

Depends on / 依赖: AlgHom, AlgHom.coe_mk, Algebra, Algebra.algebraMap_self, C_apply, Finset, Finset.mul_sum, Finset.sum_comm, Finsupp, Finsupp.prod_single_index, RingHom, RingHom.id_apply, algebraMap_apply, algebraMap_self, coe_mk, id_apply, map_sum, monomial_mul, mul_apply, mul_sum
-/
lemma toMvPolynomial_mul (M : Matrix m n R) (N : Matrix n o R) (i : m) :
    (M * N).toMvPolynomial i = bind₁ N.toMvPolynomial (M.toMvPolynomial i) := by
  simp only [toMvPolynomial, mul_apply, map_sum, Finset.sum_comm (γ := o), bind₁, aeval,
    AlgHom.coe_mk, coe_eval₂Hom, eval₂_monomial, algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, C_apply, pow_zero, Finsupp.prod_single_index, pow_one, Finset.mul_sum,
    monomial_mul, zero_add]

end Matrix

namespace LinearMap

open MvPolynomial

section

variable {R M₁ M₂ ι₁ ι₂ : Type*}
variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂]
variable [Module R M₁] [Module R M₂]
variable [Fintype ι₁] [Finite ι₂]
variable [DecidableEq ι₁]
variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

/-- Let `f : M₁ →ₗ[R] M₂` be an `R`-linear map
between modules `M₁` and `M₂` with bases `b₁` and `b₂` respectively.
Then `LinearMap.toMvPolynomial b₁ b₂ f` is the family of multivariate polynomials over `R`
that evaluates on an element `x` of `M₁` (represented on the basis `b₁`)
to the element `f x` of `M₂` (represented on the basis `b₂`). -/
noncomputable
/--
Definition of `toMvPolynomial` / `toMvPolynomial` 的定义

English:
definition toMvPolynomial
  signature: (f : M₁ ->ₗ[R] M₂) (i : ι₂)
  body: (toMatrix b₁ b₂ f).toMvPolynomial i

中文:
定义 toMvPolynomial
  签名: (f : M₁ ->ₗ[R] M₂) (i : ι₂)
  定义体: (toMatrix b₁ b₂ f).toMvPolynomial i

Depends on / 依赖: toMatrix, toMvPolynomial
-/
def toMvPolynomial (f : M₁ ->ₗ[R] M₂) (i : ι₂) :
    MvPolynomial ι₁ R :=
  (toMatrix b₁ b₂ f).toMvPolynomial i

/--
lemma `toMvPolynomial_eval_eq_apply` / 引理 `toMvPolynomial_eval_eq_apply`

English:
lemma toMvPolynomial_eval_eq_apply
  given: (f : M₁ ->ₗ[R] M₂) (i : ι₂) (c : ι₁ ->₀ R)
  proof: by
  rw [toMvPolynomial]; rw [Matrix.toMvPolynomial_eval_eq_apply]; rw [← LinearMap.toMatrix_mulVec_repr b₁ b₂]; rw [LinearEquiv.apply_symm_apply]

中文:
引理 toMvPolynomial_eval_eq_apply
  条件: (f : M₁ ->ₗ[R] M₂) (i : ι₂) (c : ι₁ ->₀ R)
  证明: by
  rw [toMvPolynomial]; rw [Matrix.toMvPolynomial_eval_eq_apply]; rw [← LinearMap.toMatrix_mulVec_repr b₁ b₂]; rw [LinearEquiv.apply_symm_apply]

Depends on / 依赖: LinearEquiv, LinearEquiv.apply_symm_apply, LinearMap, LinearMap.toMatrix_mulVec_repr, Matrix, Matrix.toMvPolynomial_eval_eq_apply, apply_symm_apply, toMatrix_mulVec_repr, toMvPolynomial, toMvPolynomial_eval_eq_apply
-/
lemma toMvPolynomial_eval_eq_apply (f : M₁ ->ₗ[R] M₂) (i : ι₂) (c : ι₁ ->₀ R) :
    eval c (f.toMvPolynomial b₁ b₂ i) = b₂.repr (f (b₁.repr.symm c)) i := by
  rw [toMvPolynomial]; rw [Matrix.toMvPolynomial_eval_eq_apply]; rw [← LinearMap.toMatrix_mulVec_repr b₁ b₂]; rw [LinearEquiv.apply_symm_apply]

open Algebra.TensorProduct in
/--
lemma `toMvPolynomial_baseChange` / 引理 `toMvPolynomial_baseChange`

English:
lemma toMvPolynomial_baseChange
  given: (f : M₁ ->ₗ[R] M₂) (i : ι₂) (A : Type*) [CommRing A] [Algebra R A]
  proof: by
  simp only [toMvPolynomial, toMatrix_baseChange, Matrix.toMvPolynomial_map]

中文:
引理 toMvPolynomial_baseChange
  条件: (f : M₁ ->ₗ[R] M₂) (i : ι₂) (A : 类型) [CommRing A] [Algebra R A]
  证明: by
  simp only [toMvPolynomial, toMatrix_baseChange, Matrix.toMvPolynomial_map]

Depends on / 依赖: Matrix, Matrix.toMvPolynomial_map, toMatrix_baseChange, toMvPolynomial, toMvPolynomial_map
-/
lemma toMvPolynomial_baseChange (f : M₁ ->ₗ[R] M₂) (i : ι₂) (A : Type*) [CommRing A] [Algebra R A] :
    (f.baseChange A).toMvPolynomial (basis A b₁) (basis A b₂) i =
      MvPolynomial.map (algebraMap R A) (f.toMvPolynomial b₁ b₂ i) := by
  simp only [toMvPolynomial, toMatrix_baseChange, Matrix.toMvPolynomial_map]

/--
lemma `toMvPolynomial_isHomogeneous` / 引理 `toMvPolynomial_isHomogeneous`

English:
lemma toMvPolynomial_isHomogeneous
  given: (f : M₁ ->ₗ[R] M₂) (i : ι₂)
  proof: Matrix.toMvPolynomial_isHomogeneous _ _

中文:
引理 toMvPolynomial_isHomogeneous
  条件: (f : M₁ ->ₗ[R] M₂) (i : ι₂)
  证明: Matrix.toMvPolynomial_isHomogeneous _ _

Depends on / 依赖: Matrix, Matrix.toMvPolynomial_isHomogeneous, toMvPolynomial_isHomogeneous
-/
lemma toMvPolynomial_isHomogeneous (f : M₁ ->ₗ[R] M₂) (i : ι₂) :
    (f.toMvPolynomial b₁ b₂ i).IsHomogeneous 1 :=
  Matrix.toMvPolynomial_isHomogeneous _ _

/--
lemma `toMvPolynomial_totalDegree_le` / 引理 `toMvPolynomial_totalDegree_le`

English:
lemma toMvPolynomial_totalDegree_le
  given: (f : M₁ ->ₗ[R] M₂) (i : ι₂)
  proof: Matrix.toMvPolynomial_totalDegree_le _ _

@[simp]

中文:
引理 toMvPolynomial_totalDegree_le
  条件: (f : M₁ ->ₗ[R] M₂) (i : ι₂)
  证明: Matrix.toMvPolynomial_totalDegree_le _ _

@[simp]

Depends on / 依赖: Matrix, Matrix.toMvPolynomial_totalDegree_le, toMvPolynomial_totalDegree_le
-/
lemma toMvPolynomial_totalDegree_le (f : M₁ ->ₗ[R] M₂) (i : ι₂) :
    (f.toMvPolynomial b₁ b₂ i).totalDegree <= 1 :=
  Matrix.toMvPolynomial_totalDegree_le _ _

@[simp]
/--
lemma `toMvPolynomial_constantCoeff` / 引理 `toMvPolynomial_constantCoeff`

English:
lemma toMvPolynomial_constantCoeff
  given: (f : M₁ ->ₗ[R] M₂) (i : ι₂)
  proof: Matrix.toMvPolynomial_constantCoeff _ _

@[simp]

中文:
引理 toMvPolynomial_constantCoeff
  条件: (f : M₁ ->ₗ[R] M₂) (i : ι₂)
  证明: Matrix.toMvPolynomial_constantCoeff _ _

@[simp]

Depends on / 依赖: Matrix, Matrix.toMvPolynomial_constantCoeff, toMvPolynomial_constantCoeff
-/
lemma toMvPolynomial_constantCoeff (f : M₁ ->ₗ[R] M₂) (i : ι₂) :
    constantCoeff (f.toMvPolynomial b₁ b₂ i) = 0 :=
  Matrix.toMvPolynomial_constantCoeff _ _

@[simp]
/--
lemma `toMvPolynomial_zero` / 引理 `toMvPolynomial_zero`

English:
lemma toMvPolynomial_zero
  statement: (0 : M₁ ->ₗ[R] M₂).toMvPolynomial b₁ b₂ = 0
  proof: by
  unfold toMvPolynomial; simp only [map_zero, Matrix.toMvPolynomial_zero]

@[simp]

中文:
引理 toMvPolynomial_zero
  结论: (0 : M₁ ->ₗ[R] M₂).toMvPolynomial b₁ b₂ = 0
  证明: by
  unfold toMvPolynomial; simp only [map_zero, Matrix.toMvPolynomial_zero]

@[simp]

Depends on / 依赖: Matrix, Matrix.toMvPolynomial_zero, map_zero, toMvPolynomial, toMvPolynomial_zero
-/
lemma toMvPolynomial_zero : (0 : M₁ ->ₗ[R] M₂).toMvPolynomial b₁ b₂ = 0 := by
  unfold toMvPolynomial; simp only [map_zero, Matrix.toMvPolynomial_zero]

@[simp]
/--
lemma `toMvPolynomial_id` / 引理 `toMvPolynomial_id`

English:
lemma toMvPolynomial_id
  statement: (id : M₁ ->ₗ[R] M₁).toMvPolynomial b₁ b₁ = X
  proof: by
  unfold toMvPolynomial; simp only [toMatrix_id, Matrix.toMvPolynomial_one]

中文:
引理 toMvPolynomial_id
  结论: (id : M₁ ->ₗ[R] M₁).toMvPolynomial b₁ b₁ = X
  证明: by
  unfold toMvPolynomial; simp only [toMatrix_id, Matrix.toMvPolynomial_one]

Depends on / 依赖: Matrix, Matrix.toMvPolynomial_one, toMatrix_id, toMvPolynomial, toMvPolynomial_one
-/
lemma toMvPolynomial_id : (id : M₁ ->ₗ[R] M₁).toMvPolynomial b₁ b₁ = X := by
  unfold toMvPolynomial; simp only [toMatrix_id, Matrix.toMvPolynomial_one]

/--
lemma `toMvPolynomial_add` / 引理 `toMvPolynomial_add`

English:
lemma toMvPolynomial_add
  given: (f g : M₁ ->ₗ[R] M₂)
  proof: by
  unfold toMvPolynomial; simp only [map_add, Matrix.toMvPolynomial_add]

中文:
引理 toMvPolynomial_add
  条件: (f g : M₁ ->ₗ[R] M₂)
  证明: by
  unfold toMvPolynomial; simp only [map_add, Matrix.toMvPolynomial_add]

Depends on / 依赖: Matrix, Matrix.toMvPolynomial_add, map_add, toMvPolynomial, toMvPolynomial_add
-/
lemma toMvPolynomial_add (f g : M₁ ->ₗ[R] M₂) :
    (f + g).toMvPolynomial b₁ b₂ = f.toMvPolynomial b₁ b₂ + g.toMvPolynomial b₁ b₂ := by
  unfold toMvPolynomial; simp only [map_add, Matrix.toMvPolynomial_add]

end

variable {R M₁ M₂ M₃ ι₁ ι₂ ι₃ : Type*}
variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M₁] [Module R M₂] [Module R M₃]
variable [Fintype ι₁] [Fintype ι₂] [Finite ι₃]
variable [DecidableEq ι₁] [DecidableEq ι₂]
variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂) (b₃ : Basis ι₃ R M₃)

/--
lemma `toMvPolynomial_comp` / 引理 `toMvPolynomial_comp`

English:
lemma toMvPolynomial_comp
  given: (g : M₂ ->ₗ[R] M₃) (f : M₁ ->ₗ[R] M₂) (i : ι₃)
  proof: by
  simp only [toMvPolynomial, toMatrix_comp b₁ b₂ b₃, Matrix.toMvPolynomial_mul]
  rfl

中文:
引理 toMvPolynomial_comp
  条件: (g : M₂ ->ₗ[R] M₃) (f : M₁ ->ₗ[R] M₂) (i : ι₃)
  证明: by
  simp only [toMvPolynomial, toMatrix_comp b₁ b₂ b₃, Matrix.toMvPolynomial_mul]
  rfl

Depends on / 依赖: Matrix, Matrix.toMvPolynomial_mul, toMatrix_comp, toMvPolynomial, toMvPolynomial_mul
-/
lemma toMvPolynomial_comp (g : M₂ ->ₗ[R] M₃) (f : M₁ ->ₗ[R] M₂) (i : ι₃) :
    (g ∘ₗ f).toMvPolynomial b₁ b₃ i =
      bind₁ (f.toMvPolynomial b₁ b₂) (g.toMvPolynomial b₂ b₃ i) := by
  simp only [toMvPolynomial, toMatrix_comp b₁ b₂ b₃, Matrix.toMvPolynomial_mul]
  rfl

end LinearMap

variable {R L M n ι ι' ιM : Type*}
variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
variable (φ : L ->ₗ[R] Module.End R M)
variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

namespace LinearMap

section aux

variable [DecidableEq ιM] (b : Basis ι R L) (bₘ : Basis ιM R M)

open Matrix

/-- (Implementation detail, see `LinearMap.polyCharpoly`.)

Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear map.
Let `b` be a basis of `L` and `bₘ` a basis of `M`.
Then `LinearMap.polyCharpolyAux φ b bₘ` is the polynomial that evaluates on elements `x` of `L`
to the characteristic polynomial of `φ x` acting on `M`.

This definition does not depend on the choice of `bₘ`
(see `LinearMap.polyCharpolyAux_basisIndep`). -/
noncomputable
/--
Definition of `polyCharpolyAux` / `polyCharpolyAux` 的定义

English:
definition polyCharpolyAux
  signature: : Polynomial (MvPolynomial ι R)
  body: (charpoly.univ R ιM).map MvPolynomial.bind₁ (φ.toMvPolynomial b bₘ.end)

中文:
定义 polyCharpolyAux
  签名: : Polynomial (MvPolynomial ι R)
  定义体: (charpoly.univ R ιM).map MvPolynomial.bind₁ (φ.toMvPolynomial b bₘ.end)

Depends on / 依赖: MvPolynomial, MvPolynomial.bind, charpoly, charpoly.univ, toMvPolynomial
-/
def polyCharpolyAux : Polynomial (MvPolynomial ι R) :=
(charpoly.univ R ιM).map MvPolynomial.bind₁ (φ.toMvPolynomial b bₘ.end)

set_option backward.defeqAttrib.useBackward true in
open Algebra.TensorProduct MvPolynomial in
/--
lemma `polyCharpolyAux_baseChange` / 引理 `polyCharpolyAux_baseChange`

English:
lemma polyCharpolyAux_baseChange
  given: (A : Type*) [CommRing A] [Algebra R A]
  proof: by
  simp only [polyCharpolyAux]
  rw [← charpoly.univ_map_map _ (algebraMap R A)]
  simp only [Polynomial.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_C, bind₁_C_right]
  · rintro ij
    simp only [RingHom

中文:
引理 polyCharpolyAux_baseChange
  条件: (A : 类型) [CommRing A] [Algebra R A]
  证明: by
  simp only [polyCharpolyAux]
  rw [← charpoly.univ_map_map _ (algebraMap R A)]
  simp only [Polynomial.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_C, bind₁_C_right]
  · rintro ij
    simp only [RingHom

Depends on / 依赖: Basis.end, Function, Function.comp_apply, Module, Module.End, MvPolynomial, MvPolynomial.ringHom_ext, Polynomial, Polynomial.map_map, RingHom, RingHom.coe_coe, RingHom.coe_comp, TensorProduct, algebraMap, charpoly, charpoly.univ_map_map, coe_coe, coe_comp, comp_apply, map_C
-/
lemma polyCharpolyAux_baseChange (A : Type*) [CommRing A] [Algebra R A] :
    polyCharpolyAux (tensorProduct _ _ _ _ ∘ₗ φ.baseChange A) (basis A b) (basis A bₘ) =
      (polyCharpolyAux φ b bₘ).map (MvPolynomial.map (algebraMap R A)) := by
  simp only [polyCharpolyAux]
  rw [← charpoly.univ_map_map _ (algebraMap R A)]
  simp only [Polynomial.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_C, bind₁_C_right]
  · rintro ij
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_X, bind₁_X_right]
    rw [toMvPolynomial_comp _ (basis A (Basis.end bₘ))]; rw [← toMvPolynomial_baseChange]
    suffices toMvPolynomial (M₂ := (Module.End A (TensorProduct R A M)))
        (basis A bₘ.end) (basis A bₘ).end (tensorProduct R A M M) ij = X ij by
      rw [this]; rw [bind₁_X_right]
    simp only [toMvPolynomial, Matrix.toMvPolynomial]
    suffices forall kl,
        (toMatrix (basis A bₘ.end) (basis A bₘ).end) (tensorProduct R A M M) ij kl =
        if kl = ij then 1 else 0 by
      rw [Finset.sum_eq_single ij]
      · rw [this, if_pos rfl, X]
      · rintro kl - H
        rw [this]; rw [if_neg H]; rw [map_zero]
      · grind
    intro kl
    rw [toMatrix_apply]; rw [tensorProduct]; rw [TensorProduct.AlgebraTensorModule.lift_apply]; rw [basis_apply]; rw [TensorProduct.lift.tmul]; rw [coe_restrictScalars]
    dsimp only [coe_mk, AddHom.coe_mk, smul_apply, baseChangeHom_apply]
    rw [one_smul]; rw [Basis.baseChange_end]; rw [Basis.repr_self_apply]

open LinearMap in
/--
lemma `polyCharpolyAux_map_eq_toMatrix_charpoly` / 引理 `polyCharpolyAux_map_eq_toMatrix_charpoly`

English:
lemma polyCharpolyAux_map_eq_toMatrix_charpoly
  given: (x : L)
  proof: by
  rw [polyCharpolyAux]; rw [Polynomial.map_map]; rw [← MvPolynomial.eval₂Hom_C_eq_bind₁]; rw [MvPolynomial.comp_eval₂Hom]; rw [charpoly.univ_map_eval₂Hom]
  congr
  ext
  rw [of_apply]; rw [Function.curry_apply]; rw [toMvPolynomial_eval_eq_apply]; rw [LinearEquiv.symm_apply_apply]
  rfl

中文:
引理 polyCharpolyAux_map_eq_toMatrix_charpoly
  条件: (x : L)
  证明: by
  rw [polyCharpolyAux]; rw [Polynomial.map_map]; rw [← MvPolynomial.eval₂Hom_C_eq_bind₁]; rw [MvPolynomial.comp_eval₂Hom]; rw [charpoly.univ_map_eval₂Hom]
  congr
  ext
  rw [of_apply]; rw [Function.curry_apply]; rw [toMvPolynomial_eval_eq_apply]; rw [LinearEquiv.symm_apply_apply]
  rfl

Depends on / 依赖: Function, Function.curry_apply, LinearEquiv, LinearEquiv.symm_apply_apply, MvPolynomial, MvPolynomial.comp_eval, MvPolynomial.eval, Polynomial, Polynomial.map_map, charpoly, charpoly.univ_map_eval, curry_apply, map_map, of_apply, polyCharpolyAux, symm_apply_apply, toMvPolynomial_eval_eq_apply
-/
lemma polyCharpolyAux_map_eq_toMatrix_charpoly (x : L) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval (b.repr x)) =
      (toMatrix bₘ bₘ (φ x)).charpoly := by
  rw [polyCharpolyAux]; rw [Polynomial.map_map]; rw [← MvPolynomial.eval₂Hom_C_eq_bind₁]; rw [MvPolynomial.comp_eval₂Hom]; rw [charpoly.univ_map_eval₂Hom]
  congr
  ext
  rw [of_apply]; rw [Function.curry_apply]; rw [toMvPolynomial_eval_eq_apply]; rw [LinearEquiv.symm_apply_apply]
  rfl

open LinearMap in
/--
lemma `polyCharpolyAux_eval_eq_toMatrix_charpoly_coeff` / 引理 `polyCharpolyAux_eval_eq_toMatrix_charpoly_coeff`

English:
lemma polyCharpolyAux_eval_eq_toMatrix_charpoly_coeff
  given: (x : L) (i : Nat)
  proof: by
  simp [← polyCharpolyAux_map_eq_toMatrix_charpoly φ b bₘ x]

@[simp]

中文:
引理 polyCharpolyAux_eval_eq_toMatrix_charpoly_coeff
  条件: (x : L) (i : 自然数)
  证明: by
  simp [← polyCharpolyAux_map_eq_toMatrix_charpoly φ b bₘ x]

@[simp]

Depends on / 依赖: polyCharpolyAux_map_eq_toMatrix_charpoly
-/
lemma polyCharpolyAux_eval_eq_toMatrix_charpoly_coeff (x : L) (i : Nat) :
    MvPolynomial.eval (b.repr x) ((polyCharpolyAux φ b bₘ).coeff i) =
      (toMatrix bₘ bₘ (φ x)).charpoly.coeff i := by
  simp [← polyCharpolyAux_map_eq_toMatrix_charpoly φ b bₘ x]

@[simp]
/--
lemma `polyCharpolyAux_map_eq_charpoly` / 引理 `polyCharpolyAux_map_eq_charpoly`

English:
lemma polyCharpolyAux_map_eq_charpoly
  statement: [Module.Finite R M] [Module.Free R M]
  proof: by
  nontriviality R
  rw [polyCharpolyAux_map_eq_toMatrix_charpoly]; rw [LinearMap.charpoly_toMatrix]

@[simp]

中文:
引理 polyCharpolyAux_map_eq_charpoly
  结论: [Module.Finite R M] [Module.Free R M]
  证明: by
  nontriviality R
  rw [polyCharpolyAux_map_eq_toMatrix_charpoly]; rw [LinearMap.charpoly_toMatrix]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.charpoly_toMatrix, charpoly_toMatrix, nontriviality, polyCharpolyAux_map_eq_toMatrix_charpoly
-/
lemma polyCharpolyAux_map_eq_charpoly [Module.Finite R M] [Module.Free R M]
    (x : L) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly := by
  nontriviality R
  rw [polyCharpolyAux_map_eq_toMatrix_charpoly]; rw [LinearMap.charpoly_toMatrix]

@[simp]
/--
lemma `polyCharpolyAux_coeff_eval` / 引理 `polyCharpolyAux_coeff_eval`

English:
lemma polyCharpolyAux_coeff_eval
  given: [Module.Finite R M] [Module.Free R M] (x : L) (i : Nat)
  proof: by
  nontriviality R
  rw [← polyCharpolyAux_map_eq_charpoly φ b bₘ x]; rw [Polynomial.coeff_map]

中文:
引理 polyCharpolyAux_coeff_eval
  条件: [Module.Finite R M] [Module.Free R M] (x : L) (i : 自然数)
  证明: by
  nontriviality R
  rw [← polyCharpolyAux_map_eq_charpoly φ b bₘ x]; rw [Polynomial.coeff_map]

Depends on / 依赖: Polynomial, Polynomial.coeff_map, coeff_map, nontriviality, polyCharpolyAux_map_eq_charpoly
-/
lemma polyCharpolyAux_coeff_eval [Module.Finite R M] [Module.Free R M] (x : L) (i : Nat) :
    MvPolynomial.eval (b.repr x) ((polyCharpolyAux φ b bₘ).coeff i) = (φ x).charpoly.coeff i := by
  nontriviality R
  rw [← polyCharpolyAux_map_eq_charpoly φ b bₘ x]; rw [Polynomial.coeff_map]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `polyCharpolyAux_map_eval` / 引理 `polyCharpolyAux_map_eval`

English:
lemma polyCharpolyAux_map_eval
  statement: [Module.Finite R M] [Module.Free R M]
  proof: by
  simp only [← polyCharpolyAux_map_eq_charpoly φ b bₘ, LinearEquiv.apply_symm_apply,
    Finsupp.equivFunOnFinite, Equiv.coe_fn_symm_mk, Finsupp.coe_mk]

中文:
引理 polyCharpolyAux_map_eval
  结论: [Module.Finite R M] [Module.Free R M]
  证明: by
  simp only [← polyCharpolyAux_map_eq_charpoly φ b bₘ, LinearEquiv.apply_symm_apply,
    Finsupp.equivFunOnFinite, Equiv.coe_fn_symm_mk, Finsupp.coe_mk]

Depends on / 依赖: Equiv.coe_fn_symm_mk, Finsupp, Finsupp.coe_mk, Finsupp.equivFunOnFinite, LinearEquiv, LinearEquiv.apply_symm_apply, apply_symm_apply, coe_fn_symm_mk, coe_mk, equivFunOnFinite, polyCharpolyAux_map_eq_charpoly
-/
lemma polyCharpolyAux_map_eval [Module.Finite R M] [Module.Free R M]
    (x : ι -> R) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval x) =
      (φ (b.repr.symm (Finsupp.equivFunOnFinite.symm x))).charpoly := by
  simp only [← polyCharpolyAux_map_eq_charpoly φ b bₘ, LinearEquiv.apply_symm_apply,
    Finsupp.equivFunOnFinite, Equiv.coe_fn_symm_mk, Finsupp.coe_mk]

open Algebra.TensorProduct TensorProduct in
/--
lemma `polyCharpolyAux_map_aeval` / 引理 `polyCharpolyAux_map_aeval`

English:
lemma polyCharpolyAux_map_aeval
  proof: by
  rw [← polyCharpolyAux_map_eval (tensorProduct R A M M ∘ₗ baseChange A φ) _ (basis A bₘ)]; rw [polyCharpolyAux_baseChange]; rw [Polynomial.map_map]
  congr
  exact DFunLike.ext _ _ fun f => (MvPolynomial.eval_map (algebraMap R A) x f).symm

中文:
引理 polyCharpolyAux_map_aeval
  证明: by
  rw [← polyCharpolyAux_map_eval (tensorProduct R A M M ∘ₗ baseChange A φ) _ (basis A bₘ)]; rw [polyCharpolyAux_baseChange]; rw [Polynomial.map_map]
  congr
  exact DFunLike.ext _ _ fun f => (MvPolynomial.eval_map (algebraMap R A) x f).symm

Depends on / 依赖: DFunLike, DFunLike.ext, MvPolynomial, MvPolynomial.eval_map, Polynomial, Polynomial.map_map, algebraMap, baseChange, eval_map, map_map, polyCharpolyAux_baseChange, polyCharpolyAux_map_eval, tensorProduct
-/
lemma polyCharpolyAux_map_aeval
    (A : Type*) [CommRing A] [Algebra R A] [Module.Finite A (A otimes[R] M)] [Module.Free A (A otimes[R] M)]
    (x : ι -> A) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.aeval x).toRingHom =
      LinearMap.charpoly ((tensorProduct R A M M).comp (baseChange A φ)
        ((basis A b).repr.symm (Finsupp.equivFunOnFinite.symm x))) := by
  rw [← polyCharpolyAux_map_eval (tensorProduct R A M M ∘ₗ baseChange A φ) _ (basis A bₘ)]; rw [polyCharpolyAux_baseChange]; rw [Polynomial.map_map]
  congr
  exact DFunLike.ext _ _ fun f => (MvPolynomial.eval_map (algebraMap R A) x f).symm

open Algebra.TensorProduct MvPolynomial in
/--
lemma `polyCharpolyAux_basisIndep` / 引理 `polyCharpolyAux_basisIndep`

English:
lemma polyCharpolyAux_basisIndep
  statement: {ιM' : Type*} [Fintype ιM'] [DecidableEq ιM']
  proof: by
  let f : Polynomial (MvPolynomial ι R) -> Polynomial (MvPolynomial ι R) :=
    Polynomial.map (MvPolynomial.aeval X).toRingHom
  have hf : Function.Injective f := by
    simp only [f, aeval_X_left, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom]
    exact Polynomial.map_injective (RingHom.id _) Fu

中文:
引理 polyCharpolyAux_basisIndep
  结论: {ιM' : 类型} [Fintype ιM'] [DecidableEq ιM']
  证明: by
  let f : Polynomial (MvPolynomial ι R) -> Polynomial (MvPolynomial ι R) :=
    Polynomial.map (MvPolynomial.aeval X).toRingHom
  have hf : Function.Injective f := by
    simp only [f, aeval_X_left, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom]
    exact Polynomial.map_injective (RingHom.id _) Fu

Depends on / 依赖: AlgHom, AlgHom.id_toRingHom, AlgHom.toRingHom_eq_coe, Finite, Function, Function.Injective, Function.injective_id, Injective, Module, Module.Finite, Module.Finite.of_basis, Module.Free, MvPolynomial, MvPolynomial.aeval, Polynomial, Polynomial.map, Polynomial.map_injective, RingHom, RingHom.id, TensorP
-/
lemma polyCharpolyAux_basisIndep {ιM' : Type*} [Fintype ιM'] [DecidableEq ιM']
    (bₘ' : Basis ιM' R M) :
    polyCharpolyAux φ b bₘ = polyCharpolyAux φ b bₘ' := by
  let f : Polynomial (MvPolynomial ι R) -> Polynomial (MvPolynomial ι R) :=
    Polynomial.map (MvPolynomial.aeval X).toRingHom
  have hf : Function.Injective f := by
    simp only [f, aeval_X_left, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom]
    exact Polynomial.map_injective (RingHom.id _) Function.injective_id
  apply hf
  let _h1 : Module.Finite (MvPolynomial ι R) (TensorProduct R (MvPolynomial ι R) M) :=
    Module.Finite.of_basis (basis (MvPolynomial ι R) bₘ)
  let _h2 : Module.Free (MvPolynomial ι R) (TensorProduct R (MvPolynomial ι R) M) :=
    Module.Free.of_basis (basis (MvPolynomial ι R) bₘ)
  simp only [f, polyCharpolyAux_map_aeval, polyCharpolyAux_map_aeval]

end aux

open Module Matrix

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

/-- Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms.
Let `b` be a basis of `L` and `bₘ` a basis of `M`.
Then `LinearMap.polyCharpoly φ b` is the polynomial that evaluates on elements `x` of `L`
to the characteristic polynomial of `φ x` acting on `M`. -/
noncomputable
/--
Definition of `polyCharpoly` / `polyCharpoly` 的定义

English:
definition polyCharpoly
  signature: : Polynomial (MvPolynomial ι R)
  body: φ.polyCharpolyAux b (Module.Free.chooseBasis R M)

中文:
定义 polyCharpoly
  签名: : Polynomial (MvPolynomial ι R)
  定义体: φ.polyCharpolyAux b (Module.Free.chooseBasis R M)

Depends on / 依赖: Module, Module.Free.chooseBasis, chooseBasis, polyCharpolyAux
-/
def polyCharpoly : Polynomial (MvPolynomial ι R) :=
  φ.polyCharpolyAux b (Module.Free.chooseBasis R M)

/--
lemma `polyCharpoly_eq_of_basis` / 引理 `polyCharpoly_eq_of_basis`

English:
lemma polyCharpoly_eq_of_basis
  given: [DecidableEq ιM] (bₘ : Basis ιM R M)
  proof: by
  rw [polyCharpoly]; rw [φ.polyCharpolyAux_basisIndep b (Module.Free.chooseBasis R M) bₘ]; rw [polyCharpolyAux]

中文:
引理 polyCharpoly_eq_of_basis
  条件: [DecidableEq ιM] (bₘ : Basis ιM R M)
  证明: by
  rw [polyCharpoly]; rw [φ.polyCharpolyAux_basisIndep b (Module.Free.chooseBasis R M) bₘ]; rw [polyCharpolyAux]

Depends on / 依赖: Module, Module.Free.chooseBasis, chooseBasis, polyCharpoly, polyCharpolyAux, polyCharpolyAux_basisIndep
-/
lemma polyCharpoly_eq_of_basis [DecidableEq ιM] (bₘ : Basis ιM R M) :
    polyCharpoly φ b =
    (charpoly.univ R ιM).map (MvPolynomial.bind₁ (φ.toMvPolynomial b bₘ.end)) := by
  rw [polyCharpoly]; rw [φ.polyCharpolyAux_basisIndep b (Module.Free.chooseBasis R M) bₘ]; rw [polyCharpolyAux]

/--
lemma `polyCharpoly_monic` / 引理 `polyCharpoly_monic`

English:
lemma polyCharpoly_monic
  statement: (polyCharpoly φ b).Monic
  proof: (charpoly.univ_monic R _).map _

中文:
引理 polyCharpoly_monic
  结论: (polyCharpoly φ b).Monic
  证明: (charpoly.univ_monic R _).map _

Depends on / 依赖: charpoly, charpoly.univ_monic, univ_monic
-/
lemma polyCharpoly_monic : (polyCharpoly φ b).Monic :=
  (charpoly.univ_monic R _).map _

/--
lemma `polyCharpoly_ne_zero` / 引理 `polyCharpoly_ne_zero`

English:
lemma polyCharpoly_ne_zero
  given: [Nontrivial R]
  statement: (polyCharpoly φ b) != 0
  proof: (polyCharpoly_monic _ _).ne_zero

@[simp]

中文:
引理 polyCharpoly_ne_zero
  条件: [Nontrivial R]
  结论: (polyCharpoly φ b) != 0
  证明: (polyCharpoly_monic _ _).ne_zero

@[simp]

Depends on / 依赖: ne_zero, polyCharpoly_monic
-/
lemma polyCharpoly_ne_zero [Nontrivial R] : (polyCharpoly φ b) != 0 :=
  (polyCharpoly_monic _ _).ne_zero

@[simp]
/--
lemma `polyCharpoly_natDegree` / 引理 `polyCharpoly_natDegree`

English:
lemma polyCharpoly_natDegree
  given: [Nontrivial R]
  proof: by
  rw [polyCharpoly]; rw [polyCharpolyAux]; rw [(charpoly.univ_monic _ _).natDegree_map]; rw [charpoly.univ_natDegree]; rw [finrank_eq_card_chooseBasisIndex]

中文:
引理 polyCharpoly_natDegree
  条件: [Nontrivial R]
  证明: by
  rw [polyCharpoly]; rw [polyCharpolyAux]; rw [(charpoly.univ_monic _ _).natDegree_map]; rw [charpoly.univ_natDegree]; rw [finrank_eq_card_chooseBasisIndex]

Depends on / 依赖: charpoly, charpoly.univ_monic, charpoly.univ_natDegree, finrank_eq_card_chooseBasisIndex, natDegree_map, polyCharpoly, polyCharpolyAux, univ_monic, univ_natDegree
-/
lemma polyCharpoly_natDegree [Nontrivial R] :
    (polyCharpoly φ b).natDegree = finrank R M := by
  rw [polyCharpoly]; rw [polyCharpolyAux]; rw [(charpoly.univ_monic _ _).natDegree_map]; rw [charpoly.univ_natDegree]; rw [finrank_eq_card_chooseBasisIndex]

/--
lemma `polyCharpoly_coeff_isHomogeneous` / 引理 `polyCharpoly_coeff_isHomogeneous`

English:
lemma polyCharpoly_coeff_isHomogeneous
  given: (i j : Nat) (hij : i + j = finrank R M) [Nontrivial R]
  proof: by
  rw [finrank_eq_card_chooseBasisIndex] at hij
  rw [polyCharpoly]; rw [polyCharpolyAux]; rw [Polynomial.coeff_map]; rw [← one_mul j]
  apply (charpoly.univ_coeff_isHomogeneous _ _ _ _ hij).eval₂
  · exact fun r => MvPolynomial.isHomogeneous_C _ _
  · exact LinearMap.toMvPolynomial_isHomogeneous 

中文:
引理 polyCharpoly_coeff_isHomogeneous
  条件: (i j : 自然数) (hij : i + j = finrank R M) [Nontrivial R]
  证明: by
  rw [finrank_eq_card_chooseBasisIndex] at hij
  rw [polyCharpoly]; rw [polyCharpolyAux]; rw [Polynomial.coeff_map]; rw [← one_mul j]
  apply (charpoly.univ_coeff_isHomogeneous _ _ _ _ hij).eval₂
  · exact fun r => MvPolynomial.isHomogeneous_C _ _
  · exact LinearMap.toMvPolynomial_isHomogeneous 

Depends on / 依赖: LinearMap, LinearMap.toMvPolynomial_isHomogeneous, MvPolynomial, MvPolynomial.isHomogeneous_C, Polynomial, Polynomial.coeff_map, charpoly, charpoly.univ_coeff_isHomogeneous, coeff_map, finrank_eq_card_chooseBasisIndex, isHomogeneous_C, one_mul, polyCharpoly, polyCharpolyAux, toMvPolynomial_isHomogeneous, univ_coeff_isHomogeneous
-/
lemma polyCharpoly_coeff_isHomogeneous (i j : Nat) (hij : i + j = finrank R M) [Nontrivial R] :
    ((polyCharpoly φ b).coeff i).IsHomogeneous j := by
  rw [finrank_eq_card_chooseBasisIndex] at hij
  rw [polyCharpoly]; rw [polyCharpolyAux]; rw [Polynomial.coeff_map]; rw [← one_mul j]
  apply (charpoly.univ_coeff_isHomogeneous _ _ _ _ hij).eval₂
  · exact fun r => MvPolynomial.isHomogeneous_C _ _
  · exact LinearMap.toMvPolynomial_isHomogeneous _ _ _

open Algebra.TensorProduct MvPolynomial in
/--
lemma `polyCharpoly_baseChange` / 引理 `polyCharpoly_baseChange`

English:
lemma polyCharpoly_baseChange
  given: (A : Type*) [CommRing A] [Algebra R A]
  proof: by
  unfold polyCharpoly
  rw [← φ.polyCharpolyAux_baseChange]
  apply polyCharpolyAux_basisIndep

@[simp]

中文:
引理 polyCharpoly_baseChange
  条件: (A : 类型) [CommRing A] [Algebra R A]
  证明: by
  unfold polyCharpoly
  rw [← φ.polyCharpolyAux_baseChange]
  apply polyCharpolyAux_basisIndep

@[simp]

Depends on / 依赖: polyCharpoly, polyCharpolyAux_baseChange, polyCharpolyAux_basisIndep
-/
lemma polyCharpoly_baseChange (A : Type*) [CommRing A] [Algebra R A] :
    polyCharpoly (tensorProduct _ _ _ _ ∘ₗ φ.baseChange A) (basis A b) =
      (polyCharpoly φ b).map (MvPolynomial.map (algebraMap R A)) := by
  unfold polyCharpoly
  rw [← φ.polyCharpolyAux_baseChange]
  apply polyCharpolyAux_basisIndep

@[simp]
/--
lemma `polyCharpoly_map_eq_charpoly` / 引理 `polyCharpoly_map_eq_charpoly`

English:
lemma polyCharpoly_map_eq_charpoly
  given: (x : L)
  proof: by
  rw [polyCharpoly]; rw [polyCharpolyAux_map_eq_charpoly]

@[simp]

中文:
引理 polyCharpoly_map_eq_charpoly
  条件: (x : L)
  证明: by
  rw [polyCharpoly]; rw [polyCharpolyAux_map_eq_charpoly]

@[simp]

Depends on / 依赖: polyCharpoly, polyCharpolyAux_map_eq_charpoly
-/
lemma polyCharpoly_map_eq_charpoly (x : L) :
    (polyCharpoly φ b).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly := by
  rw [polyCharpoly]; rw [polyCharpolyAux_map_eq_charpoly]

@[simp]
/--
lemma `polyCharpoly_coeff_eval` / 引理 `polyCharpoly_coeff_eval`

English:
lemma polyCharpoly_coeff_eval
  given: (x : L) (i : Nat)
  proof: by
  rw [polyCharpoly]; rw [polyCharpolyAux_coeff_eval]

中文:
引理 polyCharpoly_coeff_eval
  条件: (x : L) (i : 自然数)
  证明: by
  rw [polyCharpoly]; rw [polyCharpolyAux_coeff_eval]

Depends on / 依赖: polyCharpoly, polyCharpolyAux_coeff_eval
-/
lemma polyCharpoly_coeff_eval (x : L) (i : Nat) :
    MvPolynomial.eval (b.repr x) ((polyCharpoly φ b).coeff i) = (φ x).charpoly.coeff i := by
  rw [polyCharpoly]; rw [polyCharpolyAux_coeff_eval]

/--
lemma `polyCharpoly_coeff_eq_zero_of_basis` / 引理 `polyCharpoly_coeff_eq_zero_of_basis`

English:
lemma polyCharpoly_coeff_eq_zero_of_basis
  statement: (b : Basis ι R L) (b' : Basis ι' R L) (k : Nat)
  proof: by
  rw [polyCharpoly]; rw [polyCharpolyAux]; rw [Polynomial.coeff_map] at H ⊢
  set B := (Module.Free.chooseBasis R M).end
  set g := toMvPolynomial b' b LinearMap.id
  apply_fun (MvPolynomial.bind₁ g) at H
  have : toMvPolynomial b' B φ = fun i => (MvPolynomial.bind₁ g) (toMvPolynomial b B φ i) :=

中文:
引理 polyCharpoly_coeff_eq_zero_of_basis
  结论: (b : Basis ι R L) (b' : Basis ι' R L) (k : 自然数)
  证明: by
  rw [polyCharpoly]; rw [polyCharpolyAux]; rw [Polynomial.coeff_map] at H ⊢
  set B := (Module.Free.chooseBasis R M).end
  set g := toMvPolynomial b' b LinearMap.id
  apply_fun (MvPolynomial.bind₁ g) at H
  have : toMvPolynomial b' B φ = fun i => (MvPolynomial.bind₁ g) (toMvPolynomial b B φ i) :=

Depends on / 依赖: LinearMap, LinearMap.id, Module, Module.Free.chooseBasis, MvPolynomial, MvPolynomial.bind, Polynomial, Polynomial.coeff_map, RingHom, RingHom.coe_coe, apply_fun, chooseBasis, coe_coe, coeff_map, map_zero, polyCharpoly, polyCharpolyAux, toMvPolynomial, toMvPolynomial_comp
-/
lemma polyCharpoly_coeff_eq_zero_of_basis (b : Basis ι R L) (b' : Basis ι' R L) (k : Nat)
    (H : (polyCharpoly φ b).coeff k = 0) :
    (polyCharpoly φ b').coeff k = 0 := by
  rw [polyCharpoly]; rw [polyCharpolyAux]; rw [Polynomial.coeff_map] at H ⊢
  set B := (Module.Free.chooseBasis R M).end
  set g := toMvPolynomial b' b LinearMap.id
  apply_fun (MvPolynomial.bind₁ g) at H
  have : toMvPolynomial b' B φ = fun i => (MvPolynomial.bind₁ g) (toMvPolynomial b B φ i) :=
funext toMvPolynomial_comp b' b B φ LinearMap.id
  rwa [map_zero, RingHom.coe_coe, MvPolynomial.bind₁_bind₁, ← this] at H

/--
lemma `polyCharpoly_coeff_eq_zero_iff_of_basis` / 引理 `polyCharpoly_coeff_eq_zero_iff_of_basis`

English:
lemma polyCharpoly_coeff_eq_zero_iff_of_basis
  given: (b : Basis ι R L) (b' : Basis ι' R L) (k : Nat)
  proof: by
  constructor <;> apply polyCharpoly_coeff_eq_zero_of_basis

中文:
引理 polyCharpoly_coeff_eq_zero_iff_of_basis
  条件: (b : Basis ι R L) (b' : Basis ι' R L) (k : 自然数)
  证明: by
  constructor <;> apply polyCharpoly_coeff_eq_zero_of_basis

Depends on / 依赖: polyCharpoly_coeff_eq_zero_of_basis
-/
lemma polyCharpoly_coeff_eq_zero_iff_of_basis (b : Basis ι R L) (b' : Basis ι' R L) (k : Nat) :
    (polyCharpoly φ b).coeff k = 0 ↔ (polyCharpoly φ b').coeff k = 0 := by
  constructor <;> apply polyCharpoly_coeff_eq_zero_of_basis

section aux

/-- (Implementation detail, see `LinearMap.nilRank`.)

Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms.
Then `LinearMap.nilRankAux φ b` is the smallest index
at which `LinearMap.polyCharpoly φ b` has a non-zero coefficient.

This number does not depend on the choice of `b`, see `nilRankAux_basis_indep`. -/
noncomputable
/--
Definition of `nilRankAux` / `nilRankAux` 的定义

English:
definition nilRankAux
  signature: (φ : L ->ₗ[R] Module.End R M) (b : Basis ι R L)
  body: (polyCharpoly φ b).natTrailingDegree

中文:
定义 nilRankAux
  签名: (φ : L ->ₗ[R] Module.End R M) (b : Basis ι R L)
  定义体: (polyCharpoly φ b).natTrailingDegree

Depends on / 依赖: natTrailingDegree, polyCharpoly
-/
def nilRankAux (φ : L ->ₗ[R] Module.End R M) (b : Basis ι R L) : Nat :=
  (polyCharpoly φ b).natTrailingDegree

/--
lemma `polyCharpoly_coeff_nilRankAux_ne_zero` / 引理 `polyCharpoly_coeff_nilRankAux_ne_zero`

English:
lemma polyCharpoly_coeff_nilRankAux_ne_zero
  given: [Nontrivial R]
  proof: by
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
  apply polyCharpoly_ne_zero

中文:
引理 polyCharpoly_coeff_nilRankAux_ne_zero
  条件: [Nontrivial R]
  证明: by
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
  apply polyCharpoly_ne_zero

Depends on / 依赖: Polynomial, Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr, polyCharpoly_ne_zero, trailingCoeff_nonzero_iff_nonzero
-/
lemma polyCharpoly_coeff_nilRankAux_ne_zero [Nontrivial R] :
    (polyCharpoly φ b).coeff (nilRankAux φ b) != 0 := by
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
  apply polyCharpoly_ne_zero

/--
lemma `nilRankAux_le` / 引理 `nilRankAux_le`

English:
lemma nilRankAux_le
  given: [Nontrivial R] (b : Basis ι R L) (b' : Basis ι' R L)
  proof: by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [Ne]; rw [(polyCharpoly_coeff_eq_zero_iff_of_basis φ b b' _).not]
  apply polyCharpoly_coeff_nilRankAux_ne_zero

中文:
引理 nilRankAux_le
  条件: [Nontrivial R] (b : Basis ι R L) (b' : Basis ι' R L)
  证明: by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [Ne]; rw [(polyCharpoly_coeff_eq_zero_iff_of_basis φ b b' _).not]
  apply polyCharpoly_coeff_nilRankAux_ne_zero

Depends on / 依赖: Polynomial, Polynomial.natTrailingDegree_le_of_ne_zero, natTrailingDegree_le_of_ne_zero, polyCharpoly_coeff_eq_zero_iff_of_basis, polyCharpoly_coeff_nilRankAux_ne_zero
-/
lemma nilRankAux_le [Nontrivial R] (b : Basis ι R L) (b' : Basis ι' R L) :
    nilRankAux φ b <= nilRankAux φ b' := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [Ne]; rw [(polyCharpoly_coeff_eq_zero_iff_of_basis φ b b' _).not]
  apply polyCharpoly_coeff_nilRankAux_ne_zero

/--
lemma `nilRankAux_basis_indep` / 引理 `nilRankAux_basis_indep`

English:
lemma nilRankAux_basis_indep
  given: [Nontrivial R] (b : Basis ι R L) (b' : Basis ι' R L)
  proof: by
  apply le_antisymm <;> apply nilRankAux_le

中文:
引理 nilRankAux_basis_indep
  条件: [Nontrivial R] (b : Basis ι R L) (b' : Basis ι' R L)
  证明: by
  apply le_antisymm <;> apply nilRankAux_le

Depends on / 依赖: le_antisymm, nilRankAux_le
-/
lemma nilRankAux_basis_indep [Nontrivial R] (b : Basis ι R L) (b' : Basis ι' R L) :
    nilRankAux φ b = (polyCharpoly φ b').natTrailingDegree := by
  apply le_antisymm <;> apply nilRankAux_le

end aux

variable [Module.Finite R L] [Module.Free R L]

/-- Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms.
Then `LinearMap.nilRank φ b` is the smallest index
at which `LinearMap.polyCharpoly φ b` has a non-zero coefficient.

This number does not depend on the choice of `b`,
see `LinearMap.nilRank_eq_polyCharpoly_natTrailingDegree`. -/
noncomputable
/--
Definition of `nilRank` / `nilRank` 的定义

English:
definition nilRank
  signature: (φ : L ->ₗ[R] Module.End R M)
  body: nilRankAux φ (Module.Free.chooseBasis R L)

中文:
定义 nilRank
  签名: (φ : L ->ₗ[R] Module.End R M)
  定义体: nilRankAux φ (Module.Free.chooseBasis R L)

Depends on / 依赖: Module, Module.Free.chooseBasis, chooseBasis, nilRankAux
-/
def nilRank (φ : L ->ₗ[R] Module.End R M) : Nat :=
  nilRankAux φ (Module.Free.chooseBasis R L)

section
variable [Nontrivial R]

/--
lemma `nilRank_eq_polyCharpoly_natTrailingDegree` / 引理 `nilRank_eq_polyCharpoly_natTrailingDegree`

English:
lemma nilRank_eq_polyCharpoly_natTrailingDegree
  given: (b : Basis ι R L)
  proof: by
  apply nilRankAux_basis_indep

中文:
引理 nilRank_eq_polyCharpoly_natTrailingDegree
  条件: (b : Basis ι R L)
  证明: by
  apply nilRankAux_basis_indep

Depends on / 依赖: nilRankAux_basis_indep
-/
lemma nilRank_eq_polyCharpoly_natTrailingDegree (b : Basis ι R L) :
    nilRank φ = (polyCharpoly φ b).natTrailingDegree := by
  apply nilRankAux_basis_indep

/--
lemma `polyCharpoly_coeff_nilRank_ne_zero` / 引理 `polyCharpoly_coeff_nilRank_ne_zero`

English:
lemma polyCharpoly_coeff_nilRank_ne_zero
  proof: by
  rw [nilRank_eq_polyCharpoly_natTrailingDegree _ b]
  apply polyCharpoly_coeff_nilRankAux_ne_zero

中文:
引理 polyCharpoly_coeff_nilRank_ne_zero
  证明: by
  rw [nilRank_eq_polyCharpoly_natTrailingDegree _ b]
  apply polyCharpoly_coeff_nilRankAux_ne_zero

Depends on / 依赖: nilRank_eq_polyCharpoly_natTrailingDegree, polyCharpoly_coeff_nilRankAux_ne_zero
-/
lemma polyCharpoly_coeff_nilRank_ne_zero :
    (polyCharpoly φ b).coeff (nilRank φ) != 0 := by
  rw [nilRank_eq_polyCharpoly_natTrailingDegree _ b]
  apply polyCharpoly_coeff_nilRankAux_ne_zero

open Module Module.Free

/--
lemma `nilRank_le_card` / 引理 `nilRank_le_card`

English:
lemma nilRank_le_card
  given: {ι : Type*} [Fintype ι] (b : Basis ι R M)
  statement: nilRank φ <= Fintype.card ι
  proof: by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [← Module.finrank_eq_card_basis b]; rw [← polyCharpoly_natDegree φ (chooseBasis R L)]; rw [Polynomial.coeff_natDegree]; rw [(polyCharpoly_monic _ _).leadingCoeff]
  apply one_ne_zero

中文:
引理 nilRank_le_card
  条件: {ι : 类型} [Fintype ι] (b : Basis ι R M)
  结论: nilRank φ <= Fintype.card ι
  证明: by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [← Module.finrank_eq_card_basis b]; rw [← polyCharpoly_natDegree φ (chooseBasis R L)]; rw [Polynomial.coeff_natDegree]; rw [(polyCharpoly_monic _ _).leadingCoeff]
  apply one_ne_zero

Depends on / 依赖: Module, Module.finrank_eq_card_basis, Polynomial, Polynomial.coeff_natDegree, Polynomial.natTrailingDegree_le_of_ne_zero, chooseBasis, coeff_natDegree, finrank_eq_card_basis, leadingCoeff, natTrailingDegree_le_of_ne_zero, one_ne_zero, polyCharpoly_monic, polyCharpoly_natDegree
-/
lemma nilRank_le_card {ι : Type*} [Fintype ι] (b : Basis ι R M) : nilRank φ <= Fintype.card ι := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [← Module.finrank_eq_card_basis b]; rw [← polyCharpoly_natDegree φ (chooseBasis R L)]; rw [Polynomial.coeff_natDegree]; rw [(polyCharpoly_monic _ _).leadingCoeff]
  apply one_ne_zero

/--
lemma `nilRank_le_finrank` / 引理 `nilRank_le_finrank`

English:
lemma nilRank_le_finrank
  statement: nilRank φ <= finrank R M
  proof: by
  simpa only [finrank_eq_card_chooseBasisIndex R M] using nilRank_le_card φ (chooseBasis R M)

中文:
引理 nilRank_le_finrank
  结论: nilRank φ <= finrank R M
  证明: by
  simpa only [finrank_eq_card_chooseBasisIndex R M] using nilRank_le_card φ (chooseBasis R M)

Depends on / 依赖: chooseBasis, finrank_eq_card_chooseBasisIndex, nilRank_le_card
-/
lemma nilRank_le_finrank : nilRank φ <= finrank R M := by
  simpa only [finrank_eq_card_chooseBasisIndex R M] using nilRank_le_card φ (chooseBasis R M)

/--
lemma `nilRank_le_natTrailingDegree_charpoly` / 引理 `nilRank_le_natTrailingDegree_charpoly`

English:
lemma nilRank_le_natTrailingDegree_charpoly
  given: (x : L)
  proof: by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  intro h
  apply_fun (MvPolynomial.eval ((chooseBasis R L).repr x)) at h
  rw [polyCharpoly_coeff_eval]; rw [map_zero] at h
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr _ h
  apply (LinearMap.charpoly_monic _).ne_zero

中文:
引理 nilRank_le_natTrailingDegree_charpoly
  条件: (x : L)
  证明: by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  intro h
  apply_fun (MvPolynomial.eval ((chooseBasis R L).repr x)) at h
  rw [polyCharpoly_coeff_eval]; rw [map_zero] at h
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr _ h
  apply (LinearMap.charpoly_monic _).ne_zero

Depends on / 依赖: LinearMap, LinearMap.charpoly_monic, MvPolynomial, MvPolynomial.eval, Polynomial, Polynomial.natTrailingDegree_le_of_ne_zero, Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr, apply_fun, charpoly_monic, chooseBasis, map_zero, natTrailingDegree_le_of_ne_zero, ne_zero, polyCharpoly_coeff_eval, trailingCoeff_nonzero_iff_nonzero
-/
lemma nilRank_le_natTrailingDegree_charpoly (x : L) :
    nilRank φ <= (φ x).charpoly.natTrailingDegree := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  intro h
  apply_fun (MvPolynomial.eval ((chooseBasis R L).repr x)) at h
  rw [polyCharpoly_coeff_eval]; rw [map_zero] at h
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr _ h
  apply (LinearMap.charpoly_monic _).ne_zero

end

/--
Definition of `IsNilRegular` / `IsNilRegular` 的定义

English:
definition IsNilRegular
  signature: (x : L)
  body: Polynomial.coeff (φ x).charpoly (nilRank φ) != 0

中文:
定义 IsNilRegular
  签名: (x : L)
  定义体: Polynomial.coeff (φ x).charpoly (nilRank φ) != 0

Depends on / 依赖: Polynomial, Polynomial.coeff, charpoly, nilRank
-/
def IsNilRegular (x : L) : Prop :=
  Polynomial.coeff (φ x).charpoly (nilRank φ) != 0

variable (x : L)

/--
lemma `isNilRegular_def` / 引理 `isNilRegular_def`

English:
lemma isNilRegular_def
  proof: Iff.rfl

中文:
引理 isNilRegular_def
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl, one_left, single_commute
-/
lemma isNilRegular_def :
    IsNilRegular φ x ↔ (Polynomial.coeff (φ x).charpoly (nilRank φ) != 0) := Iff.rfl

/--
lemma `isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero` / 引理 `isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero`

English:
lemma isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero
  proof: by
  rw [IsNilRegular]; rw [polyCharpoly_coeff_eval]

中文:
引理 isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero
  证明: by
  rw [IsNilRegular]; rw [polyCharpoly_coeff_eval]

Depends on / 依赖: IsNilRegular, polyCharpoly_coeff_eval
-/
lemma isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero :
    IsNilRegular φ x ↔
    MvPolynomial.eval (b.repr x)
      ((polyCharpoly φ b).coeff (nilRank φ)) != 0 := by
  rw [IsNilRegular]; rw [polyCharpoly_coeff_eval]

/--
lemma `isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank` / 引理 `isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank`

English:
lemma isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank
  given: [Nontrivial R]
  proof: by
  rw [isNilRegular_def]
  constructor
  · intro h
    exact le_antisymm
      (Polynomial.natTrailingDegree_le_of_ne_zero h)
      (nilRank_le_natTrailingDegree_charpoly φ x)
  · intro h
    rw [← h]
    apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
    apply (LinearMap.charpoly_monic _)

中文:
引理 isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank
  条件: [Nontrivial R]
  证明: by
  rw [isNilRegular_def]
  constructor
  · intro h
    exact le_antisymm
      (Polynomial.natTrailingDegree_le_of_ne_zero h)
      (nilRank_le_natTrailingDegree_charpoly φ x)
  · intro h
    rw [← h]
    apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
    apply (LinearMap.charpoly_monic _)

Depends on / 依赖: LinearMap, LinearMap.charpoly_monic, Polynomial, Polynomial.natTrailingDegree_le_of_ne_zero, Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr, charpoly_monic, isNilRegular_def, le_antisymm, natTrailingDegree_le_of_ne_zero, ne_zero, nilRank_le_natTrailingDegree_charpoly, trailingCoeff_nonzero_iff_nonzero
-/
lemma isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank [Nontrivial R] :
    IsNilRegular φ x ↔ (φ x).charpoly.natTrailingDegree = nilRank φ := by
  rw [isNilRegular_def]
  constructor
  · intro h
    exact le_antisymm
      (Polynomial.natTrailingDegree_le_of_ne_zero h)
      (nilRank_le_natTrailingDegree_charpoly φ x)
  · intro h
    rw [← h]
    apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
    apply (LinearMap.charpoly_monic _).ne_zero

section IsDomain

variable [IsDomain R]

open Cardinal Module MvPolynomial Module.Free in
/--
lemma `exists_isNilRegular_of_finrank_le_card` / 引理 `exists_isNilRegular_of_finrank_le_card`

English:
lemma exists_isNilRegular_of_finrank_le_card
  given: (h : finrank R M <= #R)
  proof: by
  let b := chooseBasis R L
  let bₘ := chooseBasis R M
  let n := Fintype.card (ChooseBasisIndex R M)
  have aux :
    ((polyCharpoly φ b).coeff (nilRank φ)).IsHomogeneous (n - nilRank φ) :=
    polyCharpoly_coeff_isHomogeneous _ b (nilRank φ) (n - nilRank φ)
      (by simp [n, nilRank_le_card φ 

中文:
引理 exists_isNilRegular_of_finrank_le_card
  条件: (h : finrank R M <= #R)
  证明: by
  let b := chooseBasis R L
  let bₘ := chooseBasis R M
  let n := Fintype.card (ChooseBasisIndex R M)
  have aux :
    ((polyCharpoly φ b).coeff (nilRank φ)).IsHomogeneous (n - nilRank φ) :=
    polyCharpoly_coeff_isHomogeneous _ b (nilRank φ) (n - nilRank φ)
      (by simp [n, nilRank_le_card φ 

Depends on / 依赖: ChooseBasisIndex, Fintype, Fintype.card, IsHomogeneous, aux.eq_zero_of_forall_eval_eq_zero, chooseBasis, eq_zero_of_forall_eval_eq_zero, finrank_eq_card_chooseBasisIndex, nilRank, nilRank_le_card, polyCharpoly, polyCharpoly_coeff_isHomogeneous, polyCharpoly_coeff_nilRank_ne_zero
-/
lemma exists_isNilRegular_of_finrank_le_card (h : finrank R M <= #R) :
    exists x : L, IsNilRegular φ x := by
  let b := chooseBasis R L
  let bₘ := chooseBasis R M
  let n := Fintype.card (ChooseBasisIndex R M)
  have aux :
    ((polyCharpoly φ b).coeff (nilRank φ)).IsHomogeneous (n - nilRank φ) :=
    polyCharpoly_coeff_isHomogeneous _ b (nilRank φ) (n - nilRank φ)
      (by simp [n, nilRank_le_card φ bₘ, finrank_eq_card_chooseBasisIndex])
  obtain ⟨x, hx⟩ : exists r, eval r ((polyCharpoly _ b).coeff (nilRank φ)) != 0 := by
    by_contra! h₀
    apply polyCharpoly_coeff_nilRank_ne_zero φ b
    apply aux.eq_zero_of_forall_eval_eq_zero_of_le_card h₀ (le_trans _ h)
    simp only [n, finrank_eq_card_chooseBasisIndex, Nat.cast_le, Nat.sub_le]
  let c := Finsupp.equivFunOnFinite.symm x
  use b.repr.symm c
  rwa [isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ b, LinearEquiv.apply_symm_apply]

/--
lemma `exists_isNilRegular` / 引理 `exists_isNilRegular`

English:
lemma exists_isNilRegular
  given: [Infinite R]
  statement: exists x : L, IsNilRegular φ x
  proof: by
  apply exists_isNilRegular_of_finrank_le_card
exact Cardinal.natCast_le_aleph0.trans Cardinal.infinite_iff.mp ‹Infinite R›

中文:
引理 exists_isNilRegular
  条件: [Infinite R]
  结论: 存在 x : L, IsNilRegular φ x
  证明: by
  apply exists_isNilRegular_of_finrank_le_card
exact Cardinal.natCast_le_aleph0.trans Cardinal.infinite_iff.mp ‹Infinite R›

Depends on / 依赖: Cardinal, Cardinal.infinite_iff.mp, Cardinal.natCast_le_aleph0.trans, Infinite, exists_isNilRegular_of_finrank_le_card, infinite_iff, natCast_le_aleph0
-/
lemma exists_isNilRegular [Infinite R] : exists x : L, IsNilRegular φ x := by
  apply exists_isNilRegular_of_finrank_le_card
exact Cardinal.natCast_le_aleph0.trans Cardinal.infinite_iff.mp ‹Infinite R›

end IsDomain

end LinearMap
