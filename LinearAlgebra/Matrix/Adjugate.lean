/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Regular.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Cramer's rule and adjugate matrices

The adjugate matrix is the transpose of the cofactor matrix.
It is calculated with Cramer's rule, which we introduce first.
The vectors returned by Cramer's rule are given by the linear map `cramer`,
which sends a matrix `A` and vector `b` to the vector consisting of the
determinant of replacing the `i`th column of `A` with `b` at index `i`
(written as `(A.updateCol i b).det`).
Using Cramer's rule, we can compute for each matrix `A` the matrix `adjugate A`.
The entries of the adjugate are the minors of `A`.
Instead of defining a minor by deleting row `i` and column `j` of `A`, we
replace the `i`th row of `A` with the `j`th basis vector; the resulting matrix
has the same determinant but more importantly equals Cramer's rule applied
to `A` and the `j`th basis vector, simplifying the subsequent proofs.
We prove the adjugate behaves like `det A • A⁻¹`.

## Main definitions

* `Matrix.cramer A b`: the vector output by Cramer's rule on `A` and `b`.
* `Matrix.adjugate A`: the adjugate (or classical adjoint) of the matrix `A`.

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

cramer, cramer's rule, adjugate
-/

@[expose] public section


namespace Matrix

universe u v w

variable {m : Type u} {n : Type v} {α : Type w}
variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

open Matrix Polynomial Equiv Equiv.Perm Finset

section Cramer

/-!
  ### `cramer` section

  Introduce the linear map `cramer` with values defined by `cramerMap`.
  After defining `cramerMap` and showing it is linear,
  we will restrict our proofs to using `cramer`.
-/


variable (A : Matrix n n α) (b : n -> α)

/--
Definition of `cramerMap` / `cramerMap` 的定义

English:
definition cramerMap
  signature: (i : n)
  body: (A.updateCol i b).det

中文:
定义 cramerMap
  签名: (i : n)
  定义体: (A.updateCol i b).det

Depends on / 依赖: A.updateCol, updateCol
-/
def cramerMap (i : n) : α :=
  (A.updateCol i b).det

/--
theorem `cramerMap_is_linear` / 定理 `cramerMap_is_linear`

English:
theorem cramerMap_is_linear
  given: (i : n)
  statement: IsLinearMap α fun b => cramerMap A b i
  proof: { map_add := det_updateCol_add _ _
    map_smul := det_updateCol_smul _ _ }

中文:
定理 cramerMap_is_linear
  条件: (i : n)
  结论: 是线性映射 α fun b => cramerMap A b i
  证明: { map_add := det_updateCol_add _ _
    map_smul := det_updateCol_smul _ _ }

Depends on / 依赖: det_updateCol_add, det_updateCol_smul, map_add, map_smul
-/
theorem cramerMap_is_linear (i : n) : IsLinearMap α fun b => cramerMap A b i :=
  { map_add := det_updateCol_add _ _
    map_smul := det_updateCol_smul _ _ }

/--
theorem `cramer_is_linear` / 定理 `cramer_is_linear`

English:
theorem cramer_is_linear
  statement: IsLinearMap α (cramerMap A)
  proof: by
  constructor <;> intros <;> ext i
  · apply (cramerMap_is_linear A i).1
  · apply (cramerMap_is_linear A i).2

中文:
定理 cramer_is_linear
  结论: 是线性映射 α (cramerMap A)
  证明: by
  constructor <;> intros <;> ext i
  · apply (cramerMap_is_linear A i).1
  · apply (cramerMap_is_linear A i).2

Depends on / 依赖: cramerMap_is_linear, intros
-/
theorem cramer_is_linear : IsLinearMap α (cramerMap A) := by
  constructor <;> intros <;> ext i
  · apply (cramerMap_is_linear A i).1
  · apply (cramerMap_is_linear A i).2

/--
Definition of `cramer` / `cramer` 的定义

English:
definition cramer
  signature: (A : Matrix n n α)
  body: IsLinearMap.mk' (cramerMap A) (cramer_is_linear A)

中文:
定义 cramer
  签名: (A : 矩阵 n n α)
  定义体: IsLinearMap.mk' (cramerMap A) (cramer_is_linear A)

Depends on / 依赖: IsLinearMap, IsLinearMap.mk, cramerMap, cramer_is_linear
-/
def cramer (A : Matrix n n α) : (n -> α) ->ₗ[α] (n -> α) :=
  IsLinearMap.mk' (cramerMap A) (cramer_is_linear A)

/--
theorem `cramer_apply` / 定理 `cramer_apply`

English:
theorem cramer_apply
  given: (i : n)
  statement: cramer A b i = (A.updateCol i b).det
  proof: rfl

中文:
定理 cramer_apply
  条件: (i : n)
  结论: cramer A b i = (A.updateCol i b).det
  证明: rfl
-/
theorem cramer_apply (i : n) : cramer A b i = (A.updateCol i b).det :=
  rfl

/--
theorem `cramer_transpose_apply` / 定理 `cramer_transpose_apply`

English:
theorem cramer_transpose_apply
  given: (i : n)
  statement: cramer Aᵀ b i = (A.updateRow i b).det
  proof: by
  rw [cramer_apply]; rw [updateCol_transpose]; rw [det_transpose]

中文:
定理 cramer_transpose_apply
  条件: (i : n)
  结论: cramer Aᵀ b i = (A.updateRow i b).det
  证明: by
  rw [cramer_apply]; rw [updateCol_transpose]; rw [det_transpose]

Depends on / 依赖: cramer_apply, det_transpose, updateCol_transpose
-/
theorem cramer_transpose_apply (i : n) : cramer Aᵀ b i = (A.updateRow i b).det := by
  rw [cramer_apply]; rw [updateCol_transpose]; rw [det_transpose]

/--
theorem `cramer_transpose_row_self` / 定理 `cramer_transpose_row_self`

English:
theorem cramer_transpose_row_self
  given: (i : n)
  statement: Aᵀ.cramer (A i) = Pi.single i A.det
  proof: by
  ext j
  rw [cramer_apply]; rw [Pi.single_apply]
  split_ifs with h
  · -- i = j: this entry should be `A.det`
    subst h
    simp only [updateCol_transpose, det_transpose, updateRow_eq_self]
  · -- i ≠ j: this entry should be 0
    rw [updateCol_transpose]; rw [det_transpose]
    apply det_zero_of_row_eq h
    rw [updateRow_self]; rw [updateRow_ne (Ne.symm h)]

中文:
定理 cramer_transpose_row_self
  条件: (i : n)
  结论: Aᵀ.cramer (A i) = 依赖函数类型.single i A.det
  证明: by
  ext j
  rw [cramer_apply]; rw [Pi.single_apply]
  split_ifs with h
  · -- i = j: this entry should be `A.det`
    subst h
    simp only [updateCol_transpose, det_transpose, updateRow_eq_self]
  · -- i ≠ j: this entry should be 0
    rw [updateCol_transpose]; rw [det_transpose]
    apply det_zero_of_row_eq h
    rw [updateRow_self]; rw [updateRow_ne (Ne.symm h)]

Depends on / 依赖: A.det, Ne.symm, Pi.single_apply, cramer_apply, det_transpose, det_zero_of_row_eq, should, single_apply, split_ifs, updateCol_transpose, updateRow_eq_self, updateRow_ne, updateRow_self
-/
theorem cramer_transpose_row_self (i : n) : Aᵀ.cramer (A i) = Pi.single i A.det := by
  ext j
  rw [cramer_apply]; rw [Pi.single_apply]
  split_ifs with h
  · -- i = j: this entry should be `A.det`
    subst h
    simp only [updateCol_transpose, det_transpose, updateRow_eq_self]
  · -- i ≠ j: this entry should be 0
    rw [updateCol_transpose]; rw [det_transpose]
    apply det_zero_of_row_eq h
    rw [updateRow_self]; rw [updateRow_ne (Ne.symm h)]

/--
theorem `cramer_row_self` / 定理 `cramer_row_self`

English:
theorem cramer_row_self
  given: (i : n) (h : forall j, b j = A j i)
  statement: A.cramer b = Pi.single i A.det
  proof: by
  rw [← transpose_transpose A]; rw [det_transpose]
  convert! cramer_transpose_row_self Aᵀ i
  exact funext h

@[simp]

中文:
定理 cramer_row_self
  条件: (i : n) (h : 对任意 j, b j = A j i)
  结论: A.cramer b = 依赖函数类型.single i A.det
  证明: by
  rw [← transpose_transpose A]; rw [det_transpose]
  convert! cramer_transpose_row_self Aᵀ i
  exact funext h

@[simp]

Depends on / 依赖: convert, cramer_transpose_row_self, det_transpose, transpose_transpose
-/
theorem cramer_row_self (i : n) (h : forall j, b j = A j i) : A.cramer b = Pi.single i A.det := by
  rw [← transpose_transpose A]; rw [det_transpose]
  convert! cramer_transpose_row_self Aᵀ i
  exact funext h

@[simp]
/--
theorem `cramer_one` / 定理 `cramer_one`

English:
theorem cramer_one
  statement: cramer (1 : Matrix n n α) = 1
  proof: by
  ext i j
  convert! congr_fun (cramer_row_self (1 : Matrix n n α) (Pi.single i 1) i _) j
  · simp
  · intro j
    rw [Matrix.one_eq_pi_single]; rw [Pi.single_comm]

中文:
定理 cramer_one
  结论: cramer (1 : 矩阵 n n α) = 1
  证明: by
  ext i j
  convert! congr_fun (cramer_row_self (1 : Matrix n n α) (Pi.single i 1) i _) j
  · simp
  · intro j
    rw [Matrix.one_eq_pi_single]; rw [Pi.single_comm]

Depends on / 依赖: Matrix, Matrix.one_eq_pi_single, Pi.single, Pi.single_comm, congr_fun, convert, cramer_row_self, one_eq_pi_single, single, single_comm
-/
theorem cramer_one : cramer (1 : Matrix n n α) = 1 := by
  ext i j
  convert! congr_fun (cramer_row_self (1 : Matrix n n α) (Pi.single i 1) i _) j
  · simp
  · intro j
    rw [Matrix.one_eq_pi_single]; rw [Pi.single_comm]

/--
theorem `cramer_smul` / 定理 `cramer_smul`

English:
theorem cramer_smul
  given: (r : α) (A : Matrix n n α)
  proof: LinearMap.ext fun _ => funext fun _ => det_updateCol_smul_left _ _ _ _

@[simp]

中文:
定理 cramer_smul
  条件: (r : α) (A : 矩阵 n n α)
  证明: LinearMap.ext fun _ => funext fun _ => det_updateCol_smul_left _ _ _ _

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, det_updateCol_smul_left
-/
theorem cramer_smul (r : α) (A : Matrix n n α) :
    cramer (r • A) = r ^ (Fintype.card n - 1) • cramer A :=
  LinearMap.ext fun _ => funext fun _ => det_updateCol_smul_left _ _ _ _

@[simp]
/--
theorem `cramer_subsingleton_apply` / 定理 `cramer_subsingleton_apply`

English:
theorem cramer_subsingleton_apply
  given: [Subsingleton n] (A : Matrix n n α) (b : n -> α) (i : n)
  proof: by rw [cramer_apply, det_eq_elem_of_subsingleton _ i, updateCol_self]

中文:
定理 cramer_subsingleton_apply
  条件: [子单例 n] (A : 矩阵 n n α) (b : n -> α) (i : n)
  证明: by rw [cramer_apply, det_eq_elem_of_subsingleton _ i, updateCol_self]

Depends on / 依赖: cramer_apply, det_eq_elem_of_subsingleton, updateCol_self
-/
theorem cramer_subsingleton_apply [Subsingleton n] (A : Matrix n n α) (b : n -> α) (i : n) :
    cramer A b i = b i := by rw [cramer_apply, det_eq_elem_of_subsingleton _ i, updateCol_self]

/--
theorem `cramer_zero` / 定理 `cramer_zero`

English:
theorem cramer_zero
  given: [Nontrivial n]
  statement: cramer (0 : Matrix n n α) = 0
  proof: by
  ext i j
  obtain ⟨j', hj'⟩ : exists j', j' != j := exists_ne j
  apply det_eq_zero_of_column_eq_zero j'
  simp [updateCol_ne hj']

中文:
定理 cramer_zero
  条件: [非平凡 n]
  结论: cramer (0 : 矩阵 n n α) = 0
  证明: by
  ext i j
  obtain ⟨j', hj'⟩ : exists j', j' != j := exists_ne j
  apply det_eq_zero_of_column_eq_zero j'
  simp [updateCol_ne hj']

Depends on / 依赖: det_eq_zero_of_column_eq_zero, exists_ne, updateCol_ne
-/
theorem cramer_zero [Nontrivial n] : cramer (0 : Matrix n n α) = 0 := by
  ext i j
  obtain ⟨j', hj'⟩ : exists j', j' != j := exists_ne j
  apply det_eq_zero_of_column_eq_zero j'
  simp [updateCol_ne hj']

/--
theorem `sum_cramer` / 定理 `sum_cramer`

English:
theorem sum_cramer
  given: {β} (s : Finset β) (f : β -> n -> α)
  proof: (map_sum (cramer A) ..).symm

中文:
定理 sum_cramer
  条件: {β} (s : 有限集 β) (f : β -> n -> α)
  证明: (map_sum (cramer A) ..).symm

Depends on / 依赖: cramer, map_sum
-/
theorem sum_cramer {β} (s : Finset β) (f : β -> n -> α) :
    (∑ x in s, cramer A (f x)) = cramer A (∑ x in s, f x) :=
  (map_sum (cramer A) ..).symm

/--
theorem `sum_cramer_apply` / 定理 `sum_cramer_apply`

English:
theorem sum_cramer_apply
  given: {β} (s : Finset β) (f : n -> β -> α) (i : n)
  proof: calc
    (∑ x in s, cramer A (fun j => f j x) i) = (∑ x in s, cramer A fun j => f j x) i :=
      (Finset.sum_apply i s _).symm
    _ = cramer A (fun j : n => ∑ x in s, f j x) i := by
      rw [sum_cramer]; rw [cramer_apply]
      congr with j
      apply Finset.sum_apply

中文:
定理 sum_cramer_apply
  条件: {β} (s : 有限集 β) (f : n -> β -> α) (i : n)
  证明: calc
    (∑ x in s, cramer A (fun j => f j x) i) = (∑ x in s, cramer A fun j => f j x) i :=
      (Finset.sum_apply i s _).symm
    _ = cramer A (fun j : n => ∑ x in s, f j x) i := by
      rw [sum_cramer]; rw [cramer_apply]
      congr with j
      apply Finset.sum_apply

Depends on / 依赖: Finset, Finset.sum_apply, cramer, cramer_apply, sum_apply, sum_cramer
-/
theorem sum_cramer_apply {β} (s : Finset β) (f : n -> β -> α) (i : n) :
    (∑ x in s, cramer A (fun j => f j x) i) = cramer A (fun j : n => ∑ x in s, f j x) i :=
  calc
    (∑ x in s, cramer A (fun j => f j x) i) = (∑ x in s, cramer A fun j => f j x) i :=
      (Finset.sum_apply i s _).symm
    _ = cramer A (fun j : n => ∑ x in s, f j x) i := by
      rw [sum_cramer]; rw [cramer_apply]
      congr with j
      apply Finset.sum_apply

/--
theorem `cramer_submatrix_equiv` / 定理 `cramer_submatrix_equiv`

English:
theorem cramer_submatrix_equiv
  given: (A : Matrix m m α) (e : n ≃ m) (b : n -> α)
  proof: by
  ext i
  simp_rw [Function.comp_apply, cramer_apply, updateCol_submatrix_equiv,
    det_submatrix_equiv_self e, Function.comp_def]

中文:
定理 cramer_submatrix_equiv
  条件: (A : 矩阵 m m α) (e : n ≃ m) (b : n -> α)
  证明: by
  ext i
  simp_rw [Function.comp_apply, cramer_apply, updateCol_submatrix_equiv,
    det_submatrix_equiv_self e, Function.comp_def]

Depends on / 依赖: Function, Function.comp_apply, Function.comp_def, comp_apply, comp_def, cramer_apply, det_submatrix_equiv_self, simp_rw, updateCol_submatrix_equiv
-/
theorem cramer_submatrix_equiv (A : Matrix m m α) (e : n ≃ m) (b : n -> α) :
    cramer (A.submatrix e e) b = cramer A (b ∘ e.symm) ∘ e := by
  ext i
  simp_rw [Function.comp_apply, cramer_apply, updateCol_submatrix_equiv,
    det_submatrix_equiv_self e, Function.comp_def]

/--
theorem `cramer_reindex` / 定理 `cramer_reindex`

English:
theorem cramer_reindex
  given: (e : m ≃ n) (A : Matrix m m α) (b : n -> α)
  proof: cramer_submatrix_equiv _ _ _

中文:
定理 cramer_reindex
  条件: (e : m ≃ n) (A : 矩阵 m m α) (b : n -> α)
  证明: cramer_submatrix_equiv _ _ _

Depends on / 依赖: cramer_submatrix_equiv
-/
theorem cramer_reindex (e : m ≃ n) (A : Matrix m m α) (b : n -> α) :
    cramer (reindex e e A) b = cramer A (b ∘ e) ∘ e.symm :=
  cramer_submatrix_equiv _ _ _

end Cramer

section Adjugate

/-!
### `adjugate` section

Define the `adjugate` matrix and a few equations.
These will hold for any matrix over a commutative ring.
-/


/--
Definition of `adjugate` / `adjugate` 的定义

English:
definition adjugate
  signature: (A : Matrix n n α)
  body: of fun i => cramer Aᵀ (Pi.single i 1)

中文:
定义 adjugate
  签名: (A : 矩阵 n n α)
  定义体: of fun i => cramer Aᵀ (Pi.single i 1)

Depends on / 依赖: Pi.single, cramer, single
-/
def adjugate (A : Matrix n n α) : Matrix n n α :=
  of fun i => cramer Aᵀ (Pi.single i 1)

/--
theorem `adjugate_def` / 定理 `adjugate_def`

English:
theorem adjugate_def
  given: (A : Matrix n n α)
  statement: adjugate A = of fun i => cramer Aᵀ (Pi.single i 1)
  proof: rfl

中文:
定理 adjugate_def
  条件: (A : 矩阵 n n α)
  结论: adjugate A = of fun i => cramer Aᵀ (依赖函数类型.single i 1)
  证明: rfl
-/
theorem adjugate_def (A : Matrix n n α) : adjugate A = of fun i => cramer Aᵀ (Pi.single i 1) :=
  rfl

/--
theorem `adjugate_apply` / 定理 `adjugate_apply`

English:
theorem adjugate_apply
  given: (A : Matrix n n α) (i j : n)
  proof: by
  rw [adjugate_def]; rw [of_apply]; rw [cramer_apply]; rw [updateCol_transpose]; rw [det_transpose]

中文:
定理 adjugate_apply
  条件: (A : 矩阵 n n α) (i j : n)
  证明: by
  rw [adjugate_def]; rw [of_apply]; rw [cramer_apply]; rw [updateCol_transpose]; rw [det_transpose]

Depends on / 依赖: adjugate_def, cramer_apply, det_transpose, of_apply, updateCol_transpose
-/
theorem adjugate_apply (A : Matrix n n α) (i j : n) :
    adjugate A i j = (A.updateRow j (Pi.single i 1)).det := by
  rw [adjugate_def]; rw [of_apply]; rw [cramer_apply]; rw [updateCol_transpose]; rw [det_transpose]

/--
theorem `adjugate_transpose` / 定理 `adjugate_transpose`

English:
theorem adjugate_transpose
  given: (A : Matrix n n α)
  statement: (adjugate A)ᵀ = adjugate Aᵀ
  proof: by
  ext i j
  rw [transpose_apply]; rw [adjugate_apply]; rw [adjugate_apply]; rw [updateRow_transpose]; rw [det_transpose]
  rw [det_apply']; rw [det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  by_cases h : i = σ j
  · -- Everything except `(i, j)` (= `(σ j, j)`) is given by A, and the rest is a single `1`.
    congr
    ext j'
    subst h
    have : σ j' = σ j ↔ j' = j := σ.injective.eq_iff
    rw [updateRow_apply]; rw [updateCol_apply]
    simp_rw [this]
    rw [← dite_eq_ite]; rw [← dite_eq_ite]
    congr 1 with rfl
    rw [Pi.single_eq_same]; rw [Pi.single_eq_same]
  · -- Otherwise, we need to show that there is a `0` somewhere in the product.
    have : (∏ j' : n, updateCol A j (Pi.single i 1) (σ j') j') = 0 := by
      apply prod_eq_zero (mem_univ j)
      rw [updateCol_self]; rw [Pi.single_eq_of_ne' h]
    rw [this]
    apply prod_eq_zero (mem_univ (σ⁻¹ i))
    simp only [Perm.coe_inv, apply_symm_apply, updateRow_self]
    apply Pi.single_eq_of_ne
    intro h'
    exact h ((symm_apply_eq σ).mp h')

中文:
定理 adjugate_transpose
  条件: (A : 矩阵 n n α)
  结论: (adjugate A)ᵀ = adjugate Aᵀ
  证明: by
  ext i j
  rw [transpose_apply]; rw [adjugate_apply]; rw [adjugate_apply]; rw [updateRow_transpose]; rw [det_transpose]
  rw [det_apply']; rw [det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  by_cases h : i = σ j
  · -- Everything except `(i, j)` (= `(σ j, j)`) is given by A, and the rest is a single `1`.
    congr
    ext j'
    subst h
    have : σ j' = σ j ↔ j' = j := σ.injective.eq_iff
    rw [updateRow_apply]; rw [updateCol_apply]
    simp_rw [this]
    rw [← dite_eq_ite]; rw [← dite_eq_ite]
    congr 1 with rfl
    rw [Pi.single_eq_same]; rw [Pi.single_eq_same]
  · -- Otherwise, we need to show that there is a `0` somewhere in the product.
    have : (∏ j' : n, updateCol A j (Pi.single i 1) (σ j') j') = 0 := by
      apply prod_eq_zero (mem_univ j)
      rw [updateCol_self]; rw [Pi.single_eq_of_ne' h]
    rw [this]
    apply prod_eq_zero (mem_univ (σ⁻¹ i))
    simp only [Perm.coe_inv, apply_symm_apply, updateRow_self]
    apply Pi.single_eq_of_ne
    intro h'
    exact h ((symm_apply_eq σ).mp h')

Depends on / 依赖: Everything, Finset, Finset.sum_congr, adjugate_apply, det_apply, det_transpose, dite_eq_ite, eq_iff, except, injective, injective.eq_iff, simp_rw, single, sum_congr, transpose_apply, updateCol_apply, updateRow_apply, updateRow_transpose
-/
theorem adjugate_transpose (A : Matrix n n α) : (adjugate A)ᵀ = adjugate Aᵀ := by
  ext i j
  rw [transpose_apply]; rw [adjugate_apply]; rw [adjugate_apply]; rw [updateRow_transpose]; rw [det_transpose]
  rw [det_apply']; rw [det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  by_cases h : i = σ j
  · -- Everything except `(i, j)` (= `(σ j, j)`) is given by A, and the rest is a single `1`.
    congr
    ext j'
    subst h
    have : σ j' = σ j ↔ j' = j := σ.injective.eq_iff
    rw [updateRow_apply]; rw [updateCol_apply]
    simp_rw [this]
    rw [← dite_eq_ite]; rw [← dite_eq_ite]
    congr 1 with rfl
    rw [Pi.single_eq_same]; rw [Pi.single_eq_same]
  · -- Otherwise, we need to show that there is a `0` somewhere in the product.
    have : (∏ j' : n, updateCol A j (Pi.single i 1) (σ j') j') = 0 := by
      apply prod_eq_zero (mem_univ j)
      rw [updateCol_self]; rw [Pi.single_eq_of_ne' h]
    rw [this]
    apply prod_eq_zero (mem_univ (σ⁻¹ i))
    simp only [Perm.coe_inv, apply_symm_apply, updateRow_self]
    apply Pi.single_eq_of_ne
    intro h'
    exact h ((symm_apply_eq σ).mp h')

/--
theorem `IsSymm.adjugate` / 定理 `IsSymm.adjugate`

English:
theorem IsSymm.adjugate
  given: {A : Matrix n n α} (hA : A.IsSymm)
  statement: A.adjugate.IsSymm
  proof: by
  rw [IsSymm]; rw [Matrix.adjugate_transpose]; rw [hA.eq]

@[simp]

中文:
定理 是Symm.adjugate
  条件: {A : 矩阵 n n α} (hA : A.是Symm)
  结论: A.adjugate.是Symm
  证明: by
  rw [IsSymm]; rw [Matrix.adjugate_transpose]; rw [hA.eq]

@[simp]

Depends on / 依赖: IsSymm, Matrix, Matrix.adjugate_transpose, adjugate_transpose, hA.eq
-/
theorem IsSymm.adjugate {A : Matrix n n α} (hA : A.IsSymm) : A.adjugate.IsSymm := by
  rw [IsSymm]; rw [Matrix.adjugate_transpose]; rw [hA.eq]

@[simp]
/--
theorem `adjugate_submatrix_equiv_self` / 定理 `adjugate_submatrix_equiv_self`

English:
theorem adjugate_submatrix_equiv_self
  given: (e : n ≃ m) (A : Matrix m m α)
  proof: by
  ext i j
  have : (fun j => Pi.single i 1 <| e.symm j) = Pi.single (e i) 1 :=
    Function.update_comp_equiv (0 : n -> α) e.symm i 1
  rw [adjugate_apply]; rw [submatrix_apply]; rw [adjugate_apply]; rw [← det_submatrix_equiv_self e]; rw [updateRow_submatrix_equiv]; rw [this]

中文:
定理 adjugate_submatrix_equiv_self
  条件: (e : n ≃ m) (A : 矩阵 m m α)
  证明: by
  ext i j
  have : (fun j => Pi.single i 1 <| e.symm j) = Pi.single (e i) 1 :=
    Function.update_comp_equiv (0 : n -> α) e.symm i 1
  rw [adjugate_apply]; rw [submatrix_apply]; rw [adjugate_apply]; rw [← det_submatrix_equiv_self e]; rw [updateRow_submatrix_equiv]; rw [this]

Depends on / 依赖: Function, Function.update_comp_equiv, Pi.single, adjugate_apply, det_submatrix_equiv_self, e.symm, single, submatrix_apply, updateRow_submatrix_equiv, update_comp_equiv
-/
theorem adjugate_submatrix_equiv_self (e : n ≃ m) (A : Matrix m m α) :
    adjugate (A.submatrix e e) = (adjugate A).submatrix e e := by
  ext i j
  have : (fun j => Pi.single i 1 <| e.symm j) = Pi.single (e i) 1 :=
    Function.update_comp_equiv (0 : n -> α) e.symm i 1
  rw [adjugate_apply]; rw [submatrix_apply]; rw [adjugate_apply]; rw [← det_submatrix_equiv_self e]; rw [updateRow_submatrix_equiv]; rw [this]

/--
theorem `adjugate_reindex` / 定理 `adjugate_reindex`

English:
theorem adjugate_reindex
  given: (e : m ≃ n) (A : Matrix m m α)
  proof: adjugate_submatrix_equiv_self _ _

中文:
定理 adjugate_reindex
  条件: (e : m ≃ n) (A : 矩阵 m m α)
  证明: adjugate_submatrix_equiv_self _ _

Depends on / 依赖: adjugate_submatrix_equiv_self
-/
theorem adjugate_reindex (e : m ≃ n) (A : Matrix m m α) :
    adjugate (reindex e e A) = reindex e e (adjugate A) :=
  adjugate_submatrix_equiv_self _ _

/--
theorem `cramer_eq_adjugate_mulVec` / 定理 `cramer_eq_adjugate_mulVec`

English:
theorem cramer_eq_adjugate_mulVec
  given: (A : Matrix n n α) (b : n -> α)
  proof: by
  nth_rw 2 [← A.transpose_transpose]
  rw [← adjugate_transpose]; rw [adjugate_def]
  have : b = ∑ i, b i • (Pi.single i 1 : n -> α) := by
    refine (pi_eq_sum_univ b).trans ?_
    congr with j
    simp [Pi.single_apply, eq_comm]
  conv_lhs =>
    rw [this]
  ext k
  simp [mulVec, dotProduct, mul_comm]

中文:
定理 cramer_eq_adjugate_mulVec
  条件: (A : 矩阵 n n α) (b : n -> α)
  证明: by
  nth_rw 2 [← A.transpose_transpose]
  rw [← adjugate_transpose]; rw [adjugate_def]
  have : b = ∑ i, b i • (Pi.single i 1 : n -> α) := by
    refine (pi_eq_sum_univ b).trans ?_
    congr with j
    simp [Pi.single_apply, eq_comm]
  conv_lhs =>
    rw [this]
  ext k
  simp [mulVec, dotProduct, mul_comm]

Depends on / 依赖: A.transpose_transpose, Pi.single, Pi.single_apply, adjugate_def, adjugate_transpose, conv_lhs, dotProduct, eq_comm, mulVec, mul_comm, nth_rw, pi_eq_sum_univ, single, single_apply, transpose_transpose
-/
theorem cramer_eq_adjugate_mulVec (A : Matrix n n α) (b : n -> α) :
    cramer A b = A.adjugate *ᵥ b := by
  nth_rw 2 [← A.transpose_transpose]
  rw [← adjugate_transpose]; rw [adjugate_def]
  have : b = ∑ i, b i • (Pi.single i 1 : n -> α) := by
    refine (pi_eq_sum_univ b).trans ?_
    congr with j
    simp [Pi.single_apply, eq_comm]
  conv_lhs =>
    rw [this]
  ext k
  simp [mulVec, dotProduct, mul_comm]

/--
theorem `mul_adjugate_apply` / 定理 `mul_adjugate_apply`

English:
theorem mul_adjugate_apply
  given: (A : Matrix n n α) (i j k)
  proof: by
  rw [← smul_eq_mul]; rw [adjugate]; rw [of_apply]; rw [← Pi.smul_apply]; rw [← map_smul]; rw [← Pi.single_smul']; rw [smul_eq_mul]; rw [mul_one]

中文:
定理 mul_adjugate_apply
  条件: (A : 矩阵 n n α) (i j k)
  证明: by
  rw [← smul_eq_mul]; rw [adjugate]; rw [of_apply]; rw [← Pi.smul_apply]; rw [← map_smul]; rw [← Pi.single_smul']; rw [smul_eq_mul]; rw [mul_one]

Depends on / 依赖: Pi.single_smul, Pi.smul_apply, adjugate, map_smul, mul_one, of_apply, single_smul, smul_apply, smul_eq_mul
-/
theorem mul_adjugate_apply (A : Matrix n n α) (i j k) :
    A i k * adjugate A k j = cramer Aᵀ (Pi.single k (A i k)) j := by
  rw [← smul_eq_mul]; rw [adjugate]; rw [of_apply]; rw [← Pi.smul_apply]; rw [← map_smul]; rw [← Pi.single_smul']; rw [smul_eq_mul]; rw [mul_one]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mul_adjugate` / 定理 `mul_adjugate`

English:
theorem mul_adjugate
  given: (A : Matrix n n α)
  statement: A * adjugate A = A.det • (1 : Matrix n n α)
  proof: by
  ext i j
  rw [mul_apply]; rw [Pi.smul_apply]; rw [Pi.smul_apply]; rw [one_apply]; rw [smul_eq_mul]; rw [mul_boole]
  simp [mul_adjugate_apply, sum_cramer_apply, cramer_transpose_row_self, Pi.single_apply, eq_comm]

中文:
定理 mul_adjugate
  条件: (A : 矩阵 n n α)
  结论: A * adjugate A = A.det • (1 : 矩阵 n n α)
  证明: by
  ext i j
  rw [mul_apply]; rw [Pi.smul_apply]; rw [Pi.smul_apply]; rw [one_apply]; rw [smul_eq_mul]; rw [mul_boole]
  simp [mul_adjugate_apply, sum_cramer_apply, cramer_transpose_row_self, Pi.single_apply, eq_comm]

Depends on / 依赖: Pi.single_apply, Pi.smul_apply, cramer_transpose_row_self, eq_comm, mul_adjugate_apply, mul_apply, mul_boole, one_apply, single_apply, smul_apply, smul_eq_mul, sum_cramer_apply
-/
theorem mul_adjugate (A : Matrix n n α) : A * adjugate A = A.det • (1 : Matrix n n α) := by
  ext i j
  rw [mul_apply]; rw [Pi.smul_apply]; rw [Pi.smul_apply]; rw [one_apply]; rw [smul_eq_mul]; rw [mul_boole]
  simp [mul_adjugate_apply, sum_cramer_apply, cramer_transpose_row_self, Pi.single_apply, eq_comm]

/--
theorem `adjugate_mul` / 定理 `adjugate_mul`

English:
theorem adjugate_mul
  given: (A : Matrix n n α)
  statement: adjugate A * A = A.det • (1 : Matrix n n α)
  proof: calc
    adjugate A * A = (Aᵀ * adjugate Aᵀ)ᵀ := by
      rw [← adjugate_transpose]; rw [← transpose_mul]; rw [transpose_transpose]
    _ = _ := by rw [mul_adjugate Aᵀ, det_transpose, transpose_smul, transpose_one]

中文:
定理 adjugate_mul
  条件: (A : 矩阵 n n α)
  结论: adjugate A * A = A.det • (1 : 矩阵 n n α)
  证明: calc
    adjugate A * A = (Aᵀ * adjugate Aᵀ)ᵀ := by
      rw [← adjugate_transpose]; rw [← transpose_mul]; rw [transpose_transpose]
    _ = _ := by rw [mul_adjugate Aᵀ, det_transpose, transpose_smul, transpose_one]

Depends on / 依赖: adjugate, adjugate_transpose, det_transpose, mul_adjugate, transpose_mul, transpose_one, transpose_smul, transpose_transpose
-/
theorem adjugate_mul (A : Matrix n n α) : adjugate A * A = A.det • (1 : Matrix n n α) :=
  calc
    adjugate A * A = (Aᵀ * adjugate Aᵀ)ᵀ := by
      rw [← adjugate_transpose]; rw [← transpose_mul]; rw [transpose_transpose]
    _ = _ := by rw [mul_adjugate Aᵀ, det_transpose, transpose_smul, transpose_one]

/--
theorem `adjugate_smul` / 定理 `adjugate_smul`

English:
theorem adjugate_smul
  given: (r : α) (A : Matrix n n α)
  proof: by
  rw [adjugate]; rw [adjugate]; rw [transpose_smul]; rw [cramer_smul]
  rfl

中文:
定理 adjugate_smul
  条件: (r : α) (A : 矩阵 n n α)
  证明: by
  rw [adjugate]; rw [adjugate]; rw [transpose_smul]; rw [cramer_smul]
  rfl

Depends on / 依赖: adjugate, cramer_smul, transpose_smul
-/
theorem adjugate_smul (r : α) (A : Matrix n n α) :
    adjugate (r • A) = r ^ (Fintype.card n - 1) • adjugate A := by
  rw [adjugate]; rw [adjugate]; rw [transpose_smul]; rw [cramer_smul]
  rfl

/-- A stronger form of **Cramer's rule** that allows us to solve some instances of `A * x = b` even
if the determinant is not a unit. A sufficient (but still not necessary) condition is that `A.det`
divides `b`. -/
@[simp]
/--
theorem `mulVec_cramer` / 定理 `mulVec_cramer`

English:
theorem mulVec_cramer
  given: (A : Matrix n n α) (b : n -> α)
  statement: A *ᵥ cramer A b = A.det • b
  proof: by
  rw [cramer_eq_adjugate_mulVec]; rw [mulVec_mulVec]; rw [mul_adjugate]; rw [smul_mulVec]; rw [one_mulVec]

中文:
定理 mulVec_cramer
  条件: (A : 矩阵 n n α) (b : n -> α)
  结论: A *ᵥ cramer A b = A.det • b
  证明: by
  rw [cramer_eq_adjugate_mulVec]; rw [mulVec_mulVec]; rw [mul_adjugate]; rw [smul_mulVec]; rw [one_mulVec]

Depends on / 依赖: cramer_eq_adjugate_mulVec, mulVec_mulVec, mul_adjugate, one_mulVec, smul_mulVec
-/
theorem mulVec_cramer (A : Matrix n n α) (b : n -> α) : A *ᵥ cramer A b = A.det • b := by
  rw [cramer_eq_adjugate_mulVec]; rw [mulVec_mulVec]; rw [mul_adjugate]; rw [smul_mulVec]; rw [one_mulVec]

/--
theorem `det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors` / 定理 `det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors`

English:
theorem det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
  statement: {M : Matrix n n α} {v : n -> α}
  proof: by
.mp apply mul_right_mem_nonZeroDivisors_eq_zero_iff hi
  simpa [adjugate_mul, smul_mulVec] using congr((M.adjugate *ᵥ $h) i)

中文:
定理 det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
  结论: {M : 矩阵 n n α} {v : n -> α}
  证明: by
.mp apply mul_right_mem_nonZeroDivisors_eq_zero_iff hi
  simpa [adjugate_mul, smul_mulVec] using congr((M.adjugate *ᵥ $h) i)

Depends on / 依赖: M.adjugate, adjugate, adjugate_mul, mul_right_mem_nonZeroDivisors_eq_zero_iff, smul_mulVec
-/
theorem det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors {M : Matrix n n α} {v : n -> α}
    (h : M *ᵥ v = 0) {i : n} (hi : v i in nonZeroDivisors α) : M.det = 0 := by
.mp apply mul_right_mem_nonZeroDivisors_eq_zero_iff hi
  simpa [adjugate_mul, smul_mulVec] using congr((M.adjugate *ᵥ $h) i)

/--
theorem `adjugate_subsingleton` / 定理 `adjugate_subsingleton`

English:
theorem adjugate_subsingleton
  given: [Subsingleton n] (A : Matrix n n α)
  statement: adjugate A = 1
  proof: by
  ext i j
  simp [Subsingleton.elim i j, adjugate_apply, det_eq_elem_of_subsingleton _ i, one_apply]

中文:
定理 adjugate_subsingleton
  条件: [子单例 n] (A : 矩阵 n n α)
  结论: adjugate A = 1
  证明: by
  ext i j
  simp [Subsingleton.elim i j, adjugate_apply, det_eq_elem_of_subsingleton _ i, one_apply]

Depends on / 依赖: Subsingleton, Subsingleton.elim, adjugate_apply, det_eq_elem_of_subsingleton, one_apply
-/
theorem adjugate_subsingleton [Subsingleton n] (A : Matrix n n α) : adjugate A = 1 := by
  ext i j
  simp [Subsingleton.elim i j, adjugate_apply, det_eq_elem_of_subsingleton _ i, one_apply]

/--
theorem `adjugate_eq_one_of_card_eq_one` / 定理 `adjugate_eq_one_of_card_eq_one`

English:
theorem adjugate_eq_one_of_card_eq_one
  given: {A : Matrix n n α} (h : Fintype.card n = 1)
  proof: haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  adjugate_subsingleton _

@[simp]

中文:
定理 adjugate_eq_one_of_card_eq_one
  条件: {A : 矩阵 n n α} (h : 有限类型.card n = 1)
  证明: haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  adjugate_subsingleton _

@[simp]

Depends on / 依赖: Fintype, Fintype.card_le_one_iff_subsingleton.mp, Subsingleton, adjugate_subsingleton, card_le_one_iff_subsingleton, h.le
-/
theorem adjugate_eq_one_of_card_eq_one {A : Matrix n n α} (h : Fintype.card n = 1) :
    adjugate A = 1 :=
  haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  adjugate_subsingleton _

@[simp]
/--
theorem `adjugate_zero` / 定理 `adjugate_zero`

English:
theorem adjugate_zero
  given: [Nontrivial n]
  statement: adjugate (0 : Matrix n n α) = 0
  proof: by
  ext i j
  obtain ⟨j', hj'⟩ : exists j', j' != j := exists_ne j
  apply det_eq_zero_of_column_eq_zero j'
  simp [updateCol_ne hj']

@[simp]

中文:
定理 adjugate_zero
  条件: [非平凡 n]
  结论: adjugate (0 : 矩阵 n n α) = 0
  证明: by
  ext i j
  obtain ⟨j', hj'⟩ : exists j', j' != j := exists_ne j
  apply det_eq_zero_of_column_eq_zero j'
  simp [updateCol_ne hj']

@[simp]

Depends on / 依赖: det_eq_zero_of_column_eq_zero, exists_ne, updateCol_ne
-/
theorem adjugate_zero [Nontrivial n] : adjugate (0 : Matrix n n α) = 0 := by
  ext i j
  obtain ⟨j', hj'⟩ : exists j', j' != j := exists_ne j
  apply det_eq_zero_of_column_eq_zero j'
  simp [updateCol_ne hj']

@[simp]
/--
theorem `adjugate_one` / 定理 `adjugate_one`

English:
theorem adjugate_one
  statement: adjugate (1 : Matrix n n α) = 1
  proof: by
  ext
  simp [adjugate_def, Matrix.one_apply, Pi.single_apply, eq_comm]

@[simp]

中文:
定理 adjugate_one
  结论: adjugate (1 : 矩阵 n n α) = 1
  证明: by
  ext
  simp [adjugate_def, Matrix.one_apply, Pi.single_apply, eq_comm]

@[simp]

Depends on / 依赖: Matrix, Matrix.one_apply, Pi.single_apply, adjugate_def, eq_comm, one_apply, single_apply
-/
theorem adjugate_one : adjugate (1 : Matrix n n α) = 1 := by
  ext
  simp [adjugate_def, Matrix.one_apply, Pi.single_apply, eq_comm]

@[simp]
/--
theorem `adjugate_diagonal` / 定理 `adjugate_diagonal`

English:
theorem adjugate_diagonal
  given: (v : n -> α)
  proof: by
  ext i j
  simp only [adjugate_def, cramer_apply, diagonal_transpose, of_apply]
  obtain rfl | hij := eq_or_ne i j
  · rw [diagonal_apply_eq, diagonal_updateCol_single, det_diagonal,
      prod_update_of_mem (Finset.mem_univ _), sdiff_singleton_eq_erase, one_mul]
  · rw [diagonal_apply_ne _ hij]
    refine det_eq_zero_of_row_eq_zero j fun k => ?_
    obtain rfl | hjk := eq_or_ne k j
    · rw [updateCol_self, Pi.single_eq_of_ne' hij]
    · rw [updateCol_ne hjk, diagonal_apply_ne' _ hjk]

中文:
定理 adjugate_diagonal
  条件: (v : n -> α)
  证明: by
  ext i j
  simp only [adjugate_def, cramer_apply, diagonal_transpose, of_apply]
  obtain rfl | hij := eq_or_ne i j
  · rw [diagonal_apply_eq, diagonal_updateCol_single, det_diagonal,
      prod_update_of_mem (Finset.mem_univ _), sdiff_singleton_eq_erase, one_mul]
  · rw [diagonal_apply_ne _ hij]
    refine det_eq_zero_of_row_eq_zero j fun k => ?_
    obtain rfl | hjk := eq_or_ne k j
    · rw [updateCol_self, Pi.single_eq_of_ne' hij]
    · rw [updateCol_ne hjk, diagonal_apply_ne' _ hjk]

Depends on / 依赖: Finset, Finset.mem_univ, Pi.single_eq_of_ne, adjugate_def, cramer_apply, det_diagonal, det_eq_zero_of_row_eq_zero, diagonal_apply_eq, diagonal_apply_ne, diagonal_transpose, diagonal_updateCol_single, eq_or_ne, mem_univ, of_apply, one_mul, prod_update_of_mem, sdiff_singleton_eq_erase, single_eq_of_ne, updateCol_ne, updateCol_self
-/
theorem adjugate_diagonal (v : n -> α) :
    adjugate (diagonal v) = diagonal fun i => ∏ j in Finset.univ.erase i, v j := by
  ext i j
  simp only [adjugate_def, cramer_apply, diagonal_transpose, of_apply]
  obtain rfl | hij := eq_or_ne i j
  · rw [diagonal_apply_eq, diagonal_updateCol_single, det_diagonal,
      prod_update_of_mem (Finset.mem_univ _), sdiff_singleton_eq_erase, one_mul]
  · rw [diagonal_apply_ne _ hij]
    refine det_eq_zero_of_row_eq_zero j fun k => ?_
    obtain rfl | hjk := eq_or_ne k j
    · rw [updateCol_self, Pi.single_eq_of_ne' hij]
    · rw [updateCol_ne hjk, diagonal_apply_ne' _ hjk]

/--
theorem `_root_.RingHom.map_adjugate` / 定理 `_root_.RingHom.map_adjugate`

English:
theorem _root_.RingHom.map_adjugate
  statement: {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S)
  proof: by
  ext i k
  have : Pi.single i (1 : S) = f ∘ Pi.single i 1 := by
    rw [← f.map_one]
    exact Pi.single_op (fun _ => f) (fun _ => f.map_zero) i (1 : R)
  rw [adjugate_apply]; rw [RingHom.mapMatrix_apply]; rw [map_apply]; rw [RingHom.mapMatrix_apply]; rw [this]; rw [←
    map_updateRow]; rw [← RingHom.mapMatrix_apply]; rw [← RingHom.map_det]; rw [← adjugate_apply]

中文:
定理 _root_.环态射.map_adjugate
  结论: {R S : 类型} [交换环 R] [交换环 S] (f : R ->+* S)
  证明: by
  ext i k
  have : Pi.single i (1 : S) = f ∘ Pi.single i 1 := by
    rw [← f.map_one]
    exact Pi.single_op (fun _ => f) (fun _ => f.map_zero) i (1 : R)
  rw [adjugate_apply]; rw [RingHom.mapMatrix_apply]; rw [map_apply]; rw [RingHom.mapMatrix_apply]; rw [this]; rw [←
    map_updateRow]; rw [← RingHom.mapMatrix_apply]; rw [← RingHom.map_det]; rw [← adjugate_apply]

Depends on / 依赖: Pi.single, Pi.single_op, RingHom, RingHom.mapMatrix_apply, RingHom.map_det, adjugate_apply, f.map_one, f.map_zero, mapMatrix_apply, map_apply, map_det, map_one, map_updateRow, map_zero, single, single_op
-/
theorem _root_.RingHom.map_adjugate {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S)
    (M : Matrix n n R) : f.mapMatrix M.adjugate = Matrix.adjugate (f.mapMatrix M) := by
  ext i k
  have : Pi.single i (1 : S) = f ∘ Pi.single i 1 := by
    rw [← f.map_one]
    exact Pi.single_op (fun _ => f) (fun _ => f.map_zero) i (1 : R)
  rw [adjugate_apply]; rw [RingHom.mapMatrix_apply]; rw [map_apply]; rw [RingHom.mapMatrix_apply]; rw [this]; rw [←
    map_updateRow]; rw [← RingHom.mapMatrix_apply]; rw [← RingHom.map_det]; rw [← adjugate_apply]

/--
theorem `_root_.AlgHom.map_adjugate` / 定理 `_root_.AlgHom.map_adjugate`

English:
theorem _root_.AlgHom.map_adjugate
  statement: {R A B : Type*} [CommSemiring R] [CommRing A] [CommRing B]
  proof: f.toRingHom.map_adjugate _

中文:
定理 _root_.代数态射.map_adjugate
  结论: {R A B : 类型} [交换半环 R] [交换环 A] [交换环 B]
  证明: f.toRingHom.map_adjugate _

Depends on / 依赖: f.toRingHom.map_adjugate, map_adjugate, toRingHom
-/
theorem _root_.AlgHom.map_adjugate {R A B : Type*} [CommSemiring R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A ->ₐ[R] B) (M : Matrix n n A) :
    f.mapMatrix M.adjugate = Matrix.adjugate (f.mapMatrix M) :=
  f.toRingHom.map_adjugate _

/--
theorem `det_adjugate` / 定理 `det_adjugate`

English:
theorem det_adjugate
  given: (A : Matrix n n α)
  statement: (adjugate A).det = A.det ^ (Fintype.card n - 1)
  proof: by
  -- get rid of the `- 1`
  rcases (Fintype.card n).eq_zero_or_pos with h_card | h_card
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp h_card
    rw [h_card]; rw [Nat.zero_sub]; rw [pow_zero]; rw [adjugate_subsingleton]; rw [det_one]
  replace h_card := tsub_add_cancel_of_le h_card.nat_succ_le
  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mvPolynomialX n n Int
  suffices A'.adjugate.det = A'.det ^ (Fintype.card n - 1) by
    rw [← mvPolynomialX_mapMatrix_aeval Int A]; rw [← AlgHom.map_adjugate]; rw [← AlgHom.map_det]; rw [←
      AlgHom.map_det]; rw [← map_pow]; rw [this]
  apply mul_left_cancel₀ (show A'.det != 0 from det_mvPolynomialX_ne_zero n Int)
  calc
    A'.det * A'.adjugate.det = (A' * adjugate A').det := (det_mul _ _).symm
    _ = A'.det ^ Fintype.card n := by rw [mul_adjugate A', det_smul, det_one, mul_one]
    _ = A'.det * A'.det ^ (Fintype.card n - 1) := by rw [← pow_succ', h_card]

@[simp]

中文:
定理 det_adjugate
  条件: (A : 矩阵 n n α)
  结论: (adjugate A).det = A.det ^ (有限类型.card n - 1)
  证明: by
  -- get rid of the `- 1`
  rcases (Fintype.card n).eq_zero_or_pos with h_card | h_card
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp h_card
    rw [h_card]; rw [Nat.zero_sub]; rw [pow_zero]; rw [adjugate_subsingleton]; rw [det_one]
  replace h_card := tsub_add_cancel_of_le h_card.nat_succ_le
  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mvPolynomialX n n Int
  suffices A'.adjugate.det = A'.det ^ (Fintype.card n - 1) by
    rw [← mvPolynomialX_mapMatrix_aeval Int A]; rw [← AlgHom.map_adjugate]; rw [← AlgHom.map_det]; rw [←
      AlgHom.map_det]; rw [← map_pow]; rw [this]
  apply mul_left_cancel₀ (show A'.det != 0 from det_mvPolynomialX_ne_zero n Int)
  calc
    A'.det * A'.adjugate.det = (A' * adjugate A').det := (det_mul _ _).symm
    _ = A'.det ^ Fintype.card n := by rw [mul_adjugate A', det_smul, det_one, mul_one]
    _ = A'.det * A'.det ^ (Fintype.card n - 1) := by rw [← pow_succ', h_card]

@[simp]
-/
theorem det_adjugate (A : Matrix n n α) : (adjugate A).det = A.det ^ (Fintype.card n - 1) := by
  -- get rid of the `- 1`
  rcases (Fintype.card n).eq_zero_or_pos with h_card | h_card
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp h_card
    rw [h_card]; rw [Nat.zero_sub]; rw [pow_zero]; rw [adjugate_subsingleton]; rw [det_one]
  replace h_card := tsub_add_cancel_of_le h_card.nat_succ_le
  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mvPolynomialX n n Int
  suffices A'.adjugate.det = A'.det ^ (Fintype.card n - 1) by
    rw [← mvPolynomialX_mapMatrix_aeval Int A]; rw [← AlgHom.map_adjugate]; rw [← AlgHom.map_det]; rw [←
      AlgHom.map_det]; rw [← map_pow]; rw [this]
  apply mul_left_cancel₀ (show A'.det != 0 from det_mvPolynomialX_ne_zero n Int)
  calc
    A'.det * A'.adjugate.det = (A' * adjugate A').det := (det_mul _ _).symm
    _ = A'.det ^ Fintype.card n := by rw [mul_adjugate A', det_smul, det_one, mul_one]
    _ = A'.det * A'.det ^ (Fintype.card n - 1) := by rw [← pow_succ', h_card]

@[simp]
/--
theorem `adjugate_fin_zero` / 定理 `adjugate_fin_zero`

English:
theorem adjugate_fin_zero
  given: (A : Matrix (Fin 0) (Fin 0) α)
  statement: adjugate A = 0
  proof: Subsingleton.elim _ _

@[simp]

中文:
定理 adjugate_fin_zero
  条件: (A : 矩阵 (有限集 0) (有限集 0) α)
  结论: adjugate A = 0
  证明: Subsingleton.elim _ _

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem adjugate_fin_zero (A : Matrix (Fin 0) (Fin 0) α) : adjugate A = 0 :=
  Subsingleton.elim _ _

@[simp]
/--
theorem `adjugate_fin_one` / 定理 `adjugate_fin_one`

English:
theorem adjugate_fin_one
  given: (A : Matrix (Fin 1) (Fin 1) α)
  statement: adjugate A = 1
  proof: adjugate_subsingleton A

中文:
定理 adjugate_fin_one
  条件: (A : 矩阵 (有限集 1) (有限集 1) α)
  结论: adjugate A = 1
  证明: adjugate_subsingleton A

Depends on / 依赖: adjugate_subsingleton
-/
theorem adjugate_fin_one (A : Matrix (Fin 1) (Fin 1) α) : adjugate A = 1 :=
  adjugate_subsingleton A

/--
theorem `adjugate_fin_succ_eq_det_submatrix` / 定理 `adjugate_fin_succ_eq_det_submatrix`

English:
theorem adjugate_fin_succ_eq_det_submatrix
  given: {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) α) (i j)
  proof: by
  simp_rw [adjugate_apply, det_succ_row _ j, updateRow_self, submatrix_updateRow_succAbove]
  rw [Fintype.sum_eq_single i fun h hjk => ?_]; rw [Pi.single_eq_same]; rw [mul_one]
  rw [Pi.single_eq_of_ne hjk]; rw [mul_zero]; rw [zero_mul]

中文:
定理 adjugate_fin_succ_eq_det_submatrix
  条件: {n : 自然数} (A : 矩阵 (有限集 n.succ) (有限集 n.succ) α) (i j)
  证明: by
  simp_rw [adjugate_apply, det_succ_row _ j, updateRow_self, submatrix_updateRow_succAbove]
  rw [Fintype.sum_eq_single i fun h hjk => ?_]; rw [Pi.single_eq_same]; rw [mul_one]
  rw [Pi.single_eq_of_ne hjk]; rw [mul_zero]; rw [zero_mul]

Depends on / 依赖: Fintype, Fintype.sum_eq_single, Pi.single_eq_of_ne, Pi.single_eq_same, adjugate_apply, det_succ_row, mul_one, mul_zero, simp_rw, single_eq_of_ne, single_eq_same, submatrix_updateRow_succAbove, sum_eq_single, updateRow_self, zero_mul
-/
theorem adjugate_fin_succ_eq_det_submatrix {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) α) (i j) :
    adjugate A i j = (-1) ^ (j + i : Nat) * det (A.submatrix j.succAbove i.succAbove) := by
  simp_rw [adjugate_apply, det_succ_row _ j, updateRow_self, submatrix_updateRow_succAbove]
  rw [Fintype.sum_eq_single i fun h hjk => ?_]; rw [Pi.single_eq_same]; rw [mul_one]
  rw [Pi.single_eq_of_ne hjk]; rw [mul_zero]; rw [zero_mul]

/--
theorem `adjugate_fin_two` / 定理 `adjugate_fin_two`

English:
theorem adjugate_fin_two
  given: (A : Matrix (Fin 2) (Fin 2) α)
  proof: by
  ext i j
  rw [adjugate_fin_succ_eq_det_submatrix]
  fin_cases i <;> fin_cases j <;> simp

@[simp]

中文:
定理 adjugate_fin_two
  条件: (A : 矩阵 (有限集 2) (有限集 2) α)
  证明: by
  ext i j
  rw [adjugate_fin_succ_eq_det_submatrix]
  fin_cases i <;> fin_cases j <;> simp

@[simp]

Depends on / 依赖: adjugate_fin_succ_eq_det_submatrix, fin_cases
-/
theorem adjugate_fin_two (A : Matrix (Fin 2) (Fin 2) α) :
    adjugate A = !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
  ext i j
  rw [adjugate_fin_succ_eq_det_submatrix]
  fin_cases i <;> fin_cases j <;> simp

@[simp]
/--
theorem `adjugate_fin_two_of` / 定理 `adjugate_fin_two_of`

English:
theorem adjugate_fin_two_of
  given: (a b c d : α)
  statement: adjugate !![a, b; c, d] = !![d, -b; -c, a]
  proof: adjugate_fin_two _

中文:
定理 adjugate_fin_two_of
  条件: (a b c d : α)
  结论: adjugate !![a, b; c, d] = !![d, -b; -c, a]
  证明: adjugate_fin_two _

Depends on / 依赖: adjugate_fin_two
-/
theorem adjugate_fin_two_of (a b c d : α) : adjugate !![a, b; c, d] = !![d, -b; -c, a] :=
  adjugate_fin_two _

/--
theorem `adjugate_fin_three` / 定理 `adjugate_fin_three`

English:
theorem adjugate_fin_three
  given: (A : Matrix (Fin 3) (Fin 3) α)
  proof: by
  ext i j
  rw [adjugate_fin_succ_eq_det_submatrix]; rw [det_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Fin.succAbove, Fin.lt_def] <;> ring

中文:
定理 adjugate_fin_three
  条件: (A : 矩阵 (有限集 3) (有限集 3) α)
  证明: by
  ext i j
  rw [adjugate_fin_succ_eq_det_submatrix]; rw [det_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Fin.succAbove, Fin.lt_def] <;> ring

Depends on / 依赖: Fin.lt_def, Fin.succAbove, adjugate_fin_succ_eq_det_submatrix, det_fin_two, fin_cases, lt_def, succAbove
-/
theorem adjugate_fin_three (A : Matrix (Fin 3) (Fin 3) α) :
    adjugate A =
    !![A 1 1 * A 2 2 - A 1 2 * A 2 1,
      -(A 0 1 * A 2 2) + A 0 2 * A 2 1,
      A 0 1 * A 1 2 - A 0 2 * A 1 1;
      -(A 1 0 * A 2 2) + A 1 2 * A 2 0,
      A 0 0 * A 2 2 - A 0 2 * A 2 0,
      -(A 0 0 * A 1 2) + A 0 2 * A 1 0;
      A 1 0 * A 2 1 - A 1 1 * A 2 0,
      -(A 0 0 * A 2 1) + A 0 1 * A 2 0,
      A 0 0 * A 1 1 - A 0 1 * A 1 0] := by
  ext i j
  rw [adjugate_fin_succ_eq_det_submatrix]; rw [det_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Fin.succAbove, Fin.lt_def] <;> ring

set_option linter.style.whitespace false in -- Use spaces to format a matrix.
@[simp]
/--
theorem `adjugate_fin_three_of` / 定理 `adjugate_fin_three_of`

English:
theorem adjugate_fin_three_of
  given: (a b c d e f g h i : α)
  proof: adjugate_fin_three _

中文:
定理 adjugate_fin_three_of
  条件: (a b c d e f g h i : α)
  证明: adjugate_fin_three _

Depends on / 依赖: adjugate_fin_three
-/
theorem adjugate_fin_three_of (a b c d e f g h i : α) :
    adjugate !![a, b, c; d, e, f; g, h, i] =
      !![ e * i - f * h, -(b * i) + c * h, b * f - c * e;
         -(d * i) + f * g, a * i - c * g, -(a * f) + c * d;
           d * h - e * g, -(a * h) + b * g, a * e - b * d] :=
  adjugate_fin_three _

/--
theorem `det_eq_sum_mul_adjugate_row` / 定理 `det_eq_sum_mul_adjugate_row`

English:
theorem det_eq_sum_mul_adjugate_row
  given: (A : Matrix n n α) (i : n)
  proof: by
  have : Nonempty n := ⟨i⟩
  obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero : Fintype.card n != 0)
  obtain ⟨e⟩ := Fintype.truncEquivFinOfCardEq hn'
  let A' := reindex e e A
  suffices det A' = ∑ j : Fin n'.succ, A' (e i) j * adjugate A' j (e i) by
    simp_rw [A', det_reindex_self, adjugate_reindex, reindex_apply, submatrix_apply, ← e.sum_comp,
      Equiv.symm_apply_apply] at this
    exact this
  rw [det_succ_row A' (e i)]
  simp_rw [mul_assoc, mul_left_comm _ (A' _ _), ← adjugate_fin_succ_eq_det_submatrix]

中文:
定理 det_eq_sum_mul_adjugate_row
  条件: (A : 矩阵 n n α) (i : n)
  证明: by
  have : Nonempty n := ⟨i⟩
  obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero : Fintype.card n != 0)
  obtain ⟨e⟩ := Fintype.truncEquivFinOfCardEq hn'
  let A' := reindex e e A
  suffices det A' = ∑ j : Fin n'.succ, A' (e i) j * adjugate A' j (e i) by
    simp_rw [A', det_reindex_self, adjugate_reindex, reindex_apply, submatrix_apply, ← e.sum_comp,
      Equiv.symm_apply_apply] at this
    exact this
  rw [det_succ_row A' (e i)]
  simp_rw [mul_assoc, mul_left_comm _ (A' _ _), ← adjugate_fin_succ_eq_det_submatrix]

Depends on / 依赖: Equiv.symm_apply_apply, Fintype, Fintype.card, Fintype.card_ne_zero, Fintype.truncEquivFinOfCardEq, Nat.exists_eq_succ_of_ne_zero, Nonempty, adjugate, adjugate_fin_succ_e, adjugate_reindex, card_ne_zero, det_reindex_self, det_succ_row, e.sum_comp, exists_eq_succ_of_ne_zero, mul_assoc, mul_left_comm, reindex, reindex_apply, simp_rw
-/
theorem det_eq_sum_mul_adjugate_row (A : Matrix n n α) (i : n) :
    det A = ∑ j : n, A i j * adjugate A j i := by
  have : Nonempty n := ⟨i⟩
  obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero : Fintype.card n != 0)
  obtain ⟨e⟩ := Fintype.truncEquivFinOfCardEq hn'
  let A' := reindex e e A
  suffices det A' = ∑ j : Fin n'.succ, A' (e i) j * adjugate A' j (e i) by
    simp_rw [A', det_reindex_self, adjugate_reindex, reindex_apply, submatrix_apply, ← e.sum_comp,
      Equiv.symm_apply_apply] at this
    exact this
  rw [det_succ_row A' (e i)]
  simp_rw [mul_assoc, mul_left_comm _ (A' _ _), ← adjugate_fin_succ_eq_det_submatrix]

/--
theorem `det_eq_sum_mul_adjugate_col` / 定理 `det_eq_sum_mul_adjugate_col`

English:
theorem det_eq_sum_mul_adjugate_col
  given: (A : Matrix n n α) (j : n)
  proof: by
  simpa only [det_transpose, ← adjugate_transpose] using! det_eq_sum_mul_adjugate_row Aᵀ j

中文:
定理 det_eq_sum_mul_adjugate_col
  条件: (A : 矩阵 n n α) (j : n)
  证明: by
  simpa only [det_transpose, ← adjugate_transpose] using! det_eq_sum_mul_adjugate_row Aᵀ j

Depends on / 依赖: adjugate_transpose, det_eq_sum_mul_adjugate_row, det_transpose
-/
theorem det_eq_sum_mul_adjugate_col (A : Matrix n n α) (j : n) :
    det A = ∑ i : n, A i j * adjugate A j i := by
  simpa only [det_transpose, ← adjugate_transpose] using! det_eq_sum_mul_adjugate_row Aᵀ j

/--
theorem `adjugate_conjTranspose` / 定理 `adjugate_conjTranspose`

English:
theorem adjugate_conjTranspose
  given: [StarRing α] (A : Matrix n n α)
  statement: A.adjugateᴴ = adjugate Aᴴ
  proof: by
  dsimp only [conjTranspose]
  have : Aᵀ.adjugate.map star = adjugate (Aᵀ.map star) := (starRingEnd α).map_adjugate Aᵀ
  rw [A.adjugate_transpose]; rw [this]

中文:
定理 adjugate_conjTranspose
  条件: [对合环 α] (A : 矩阵 n n α)
  结论: A.adjugateᴴ = adjugate Aᴴ
  证明: by
  dsimp only [conjTranspose]
  have : Aᵀ.adjugate.map star = adjugate (Aᵀ.map star) := (starRingEnd α).map_adjugate Aᵀ
  rw [A.adjugate_transpose]; rw [this]

Depends on / 依赖: A.adjugate_transpose, adjugate, adjugate.map, adjugate_transpose, conjTranspose, map_adjugate, starRingEnd
-/
theorem adjugate_conjTranspose [StarRing α] (A : Matrix n n α) : A.adjugateᴴ = adjugate Aᴴ := by
  dsimp only [conjTranspose]
  have : Aᵀ.adjugate.map star = adjugate (Aᵀ.map star) := (starRingEnd α).map_adjugate Aᵀ
  rw [A.adjugate_transpose]; rw [this]

/--
theorem `isRegular_of_isLeftRegular_det` / 定理 `isRegular_of_isLeftRegular_det`

English:
theorem isRegular_of_isLeftRegular_det
  given: {A : Matrix n n α} (hA : IsLeftRegular A.det)
  proof: by
  constructor
  · intro B C h
    refine hA.matrix ?_
    simp only at h ⊢
    rw [← Matrix.one_mul B]; rw [← Matrix.one_mul C]; rw [← Matrix.smul_mul]; rw [← Matrix.smul_mul]; rw [←
      adjugate_mul]; rw [Matrix.mul_assoc]; rw [Matrix.mul_assoc]; rw [h]
  · intro B C (h : B * A = C * A)
    refine hA.matrix ?_
    simp only
    rw [← Matrix.mul_one B]; rw [← Matrix.mul_one C]; rw [← Matrix.mul_smul]; rw [← Matrix.mul_smul]; rw [←
      mul_adjugate]; rw [← Matrix.mul_assoc]; rw [← Matrix.mul_assoc]; rw [h]

中文:
定理 isRegular_of_isLeftRegular_det
  条件: {A : 矩阵 n n α} (hA : IsLeftRegular A.det)
  证明: by
  constructor
  · intro B C h
    refine hA.matrix ?_
    simp only at h ⊢
    rw [← Matrix.one_mul B]; rw [← Matrix.one_mul C]; rw [← Matrix.smul_mul]; rw [← Matrix.smul_mul]; rw [←
      adjugate_mul]; rw [Matrix.mul_assoc]; rw [Matrix.mul_assoc]; rw [h]
  · intro B C (h : B * A = C * A)
    refine hA.matrix ?_
    simp only
    rw [← Matrix.mul_one B]; rw [← Matrix.mul_one C]; rw [← Matrix.mul_smul]; rw [← Matrix.mul_smul]; rw [←
      mul_adjugate]; rw [← Matrix.mul_assoc]; rw [← Matrix.mul_assoc]; rw [h]

Depends on / 依赖: Matrix, Matrix.mul_assoc, Matrix.mul_one, Matrix.mul_smul, Matrix.one_mul, Matrix.smul_mul, adjugate_mul, hA.matrix, matrix, mul_adjugate, mul_assoc, mul_one, mul_smul, one_mul, smul_mul
-/
theorem isRegular_of_isLeftRegular_det {A : Matrix n n α} (hA : IsLeftRegular A.det) :
    IsRegular A := by
  constructor
  · intro B C h
    refine hA.matrix ?_
    simp only at h ⊢
    rw [← Matrix.one_mul B]; rw [← Matrix.one_mul C]; rw [← Matrix.smul_mul]; rw [← Matrix.smul_mul]; rw [←
      adjugate_mul]; rw [Matrix.mul_assoc]; rw [Matrix.mul_assoc]; rw [h]
  · intro B C (h : B * A = C * A)
    refine hA.matrix ?_
    simp only
    rw [← Matrix.mul_one B]; rw [← Matrix.mul_one C]; rw [← Matrix.mul_smul]; rw [← Matrix.mul_smul]; rw [←
      mul_adjugate]; rw [← Matrix.mul_assoc]; rw [← Matrix.mul_assoc]; rw [h]

/--
theorem `adjugate_mul_distrib_aux` / 定理 `adjugate_mul_distrib_aux`

English:
theorem adjugate_mul_distrib_aux
  statement: (A B : Matrix n n α) (hA : IsLeftRegular A.det)
  proof: by
  have hAB : IsLeftRegular (A * B).det := by
    rw [det_mul]
    exact hA.mul hB
  refine (isRegular_of_isLeftRegular_det hAB).left ?_
  simp only
  rw [mul_adjugate]; rw [Matrix.mul_assoc]; rw [← Matrix.mul_assoc B]; rw [mul_adjugate]; rw [smul_mul]; rw [Matrix.one_mul]; rw [Matrix.mul_smul]; rw [mul_adjugate]; rw [smul_smul]; rw [mul_comm]; rw [← det_mul]

中文:
定理 adjugate_mul_distrib_aux
  结论: (A B : 矩阵 n n α) (hA : IsLeftRegular A.det)
  证明: by
  have hAB : IsLeftRegular (A * B).det := by
    rw [det_mul]
    exact hA.mul hB
  refine (isRegular_of_isLeftRegular_det hAB).left ?_
  simp only
  rw [mul_adjugate]; rw [Matrix.mul_assoc]; rw [← Matrix.mul_assoc B]; rw [mul_adjugate]; rw [smul_mul]; rw [Matrix.one_mul]; rw [Matrix.mul_smul]; rw [mul_adjugate]; rw [smul_smul]; rw [mul_comm]; rw [← det_mul]

Depends on / 依赖: IsLeftRegular, Matrix, Matrix.mul_assoc, Matrix.mul_smul, Matrix.one_mul, det_mul, hA.mul, isRegular_of_isLeftRegular_det, mul_adjugate, mul_assoc, mul_comm, mul_smul, one_mul, smul_mul, smul_smul
-/
theorem adjugate_mul_distrib_aux (A B : Matrix n n α) (hA : IsLeftRegular A.det)
    (hB : IsLeftRegular B.det) : adjugate (A * B) = adjugate B * adjugate A := by
  have hAB : IsLeftRegular (A * B).det := by
    rw [det_mul]
    exact hA.mul hB
  refine (isRegular_of_isLeftRegular_det hAB).left ?_
  simp only
  rw [mul_adjugate]; rw [Matrix.mul_assoc]; rw [← Matrix.mul_assoc B]; rw [mul_adjugate]; rw [smul_mul]; rw [Matrix.one_mul]; rw [Matrix.mul_smul]; rw [mul_adjugate]; rw [smul_smul]; rw [mul_comm]; rw [← det_mul]

/--
theorem `adjugate_mul_distrib` / 定理 `adjugate_mul_distrib`

English:
theorem adjugate_mul_distrib
  given: (A B : Matrix n n α)
  statement: adjugate (A * B) = adjugate B * adjugate A
  proof: by
  let g : Matrix n n α -> Matrix n n α[X] := fun M =>
    M.map Polynomial.C + (Polynomial.X : α[X]) • (1 : Matrix n n α[X])
  let f' : Matrix n n α[X] ->+* Matrix n n α := (Polynomial.evalRingHom 0).mapMatrix
  have f'_inv : forall M, f' (g M) = M := by
    intro
    ext
    simp [f', g]
  have f'_adj : forall M : Matrix n n α, f' (adjugate (g M)) = adjugate M := by
    intro
    rw [RingHom.map_adjugate]; rw [f'_inv]
  have f'_g_mul : forall M N : Matrix n n α, f' (g M * g N) = M * N := by
    intro M N
    rw [map_mul]; rw [f'_inv]; rw [f'_inv]
  have hu : forall M : Matrix n n α, IsRegular (g M).det := by
    intro M
    refine Polynomial.Monic.isRegular ?_
    simp only [g, Polynomial.Monic.def, ← Polynomial.leadingCoeff_det_X_one_add_C M, add_comm]
  rw [← f'_adj]; rw [← f'_adj]; rw [← f'_adj]; rw [← f'.map_mul]; rw [←
    adjugate_mul_distrib_aux _ _ (hu A).left (hu B).left]; rw [RingHom.map_adjugate]; rw [RingHom.map_adjugate]; rw [f'_inv]; rw [f'_g_mul]

@[simp]

中文:
定理 adjugate_mul_distrib
  条件: (A B : 矩阵 n n α)
  结论: adjugate (A * B) = adjugate B * adjugate A
  证明: by
  let g : Matrix n n α -> Matrix n n α[X] := fun M =>
    M.map Polynomial.C + (Polynomial.X : α[X]) • (1 : Matrix n n α[X])
  let f' : Matrix n n α[X] ->+* Matrix n n α := (Polynomial.evalRingHom 0).mapMatrix
  have f'_inv : forall M, f' (g M) = M := by
    intro
    ext
    simp [f', g]
  have f'_adj : forall M : Matrix n n α, f' (adjugate (g M)) = adjugate M := by
    intro
    rw [RingHom.map_adjugate]; rw [f'_inv]
  have f'_g_mul : forall M N : Matrix n n α, f' (g M * g N) = M * N := by
    intro M N
    rw [map_mul]; rw [f'_inv]; rw [f'_inv]
  have hu : forall M : Matrix n n α, IsRegular (g M).det := by
    intro M
    refine Polynomial.Monic.isRegular ?_
    simp only [g, Polynomial.Monic.def, ← Polynomial.leadingCoeff_det_X_one_add_C M, add_comm]
  rw [← f'_adj]; rw [← f'_adj]; rw [← f'_adj]; rw [← f'.map_mul]; rw [←
    adjugate_mul_distrib_aux _ _ (hu A).left (hu B).left]; rw [RingHom.map_adjugate]; rw [RingHom.map_adjugate]; rw [f'_inv]; rw [f'_g_mul]

@[simp]

Depends on / 依赖: M.map, Matrix, Polynomial, Polynomial.C, Polynomial.X, Polynomial.evalRingHom, RingHom, RingHom.map_adjugate, _adj, _g_mul, _inv, adjugate, evalRingHom, mapMatrix, map_adjugate, map_mul
-/
theorem adjugate_mul_distrib (A B : Matrix n n α) : adjugate (A * B) = adjugate B * adjugate A := by
  let g : Matrix n n α -> Matrix n n α[X] := fun M =>
    M.map Polynomial.C + (Polynomial.X : α[X]) • (1 : Matrix n n α[X])
  let f' : Matrix n n α[X] ->+* Matrix n n α := (Polynomial.evalRingHom 0).mapMatrix
  have f'_inv : forall M, f' (g M) = M := by
    intro
    ext
    simp [f', g]
  have f'_adj : forall M : Matrix n n α, f' (adjugate (g M)) = adjugate M := by
    intro
    rw [RingHom.map_adjugate]; rw [f'_inv]
  have f'_g_mul : forall M N : Matrix n n α, f' (g M * g N) = M * N := by
    intro M N
    rw [map_mul]; rw [f'_inv]; rw [f'_inv]
  have hu : forall M : Matrix n n α, IsRegular (g M).det := by
    intro M
    refine Polynomial.Monic.isRegular ?_
    simp only [g, Polynomial.Monic.def, ← Polynomial.leadingCoeff_det_X_one_add_C M, add_comm]
  rw [← f'_adj]; rw [← f'_adj]; rw [← f'_adj]; rw [← f'.map_mul]; rw [←
    adjugate_mul_distrib_aux _ _ (hu A).left (hu B).left]; rw [RingHom.map_adjugate]; rw [RingHom.map_adjugate]; rw [f'_inv]; rw [f'_g_mul]

@[simp]
/--
theorem `adjugate_pow` / 定理 `adjugate_pow`

English:
theorem adjugate_pow
  given: (A : Matrix n n α) (k : Nat)
  statement: adjugate (A ^ k) = adjugate A ^ k
  proof: by
  induction k with
  | zero => simp
  | succ k IH => rw [pow_succ', adjugate_mul_distrib, IH, pow_succ]

中文:
定理 adjugate_pow
  条件: (A : 矩阵 n n α) (k : 自然数)
  结论: adjugate (A ^ k) = adjugate A ^ k
  证明: by
  induction k with
  | zero => simp
  | succ k IH => rw [pow_succ', adjugate_mul_distrib, IH, pow_succ]

Depends on / 依赖: adjugate_mul_distrib, pow_succ
-/
theorem adjugate_pow (A : Matrix n n α) (k : Nat) : adjugate (A ^ k) = adjugate A ^ k := by
  induction k with
  | zero => simp
  | succ k IH => rw [pow_succ', adjugate_mul_distrib, IH, pow_succ]

/--
theorem `det_smul_adjugate_adjugate` / 定理 `det_smul_adjugate_adjugate`

English:
theorem det_smul_adjugate_adjugate
  given: (A : Matrix n n α)
  proof: by
  have : A * (A.adjugate * A.adjugate.adjugate) =
      A * (A.det ^ (Fintype.card n - 1) • (1 : Matrix n n α)) := by
    rw [← adjugate_mul_distrib]; rw [adjugate_mul]; rw [adjugate_smul]; rw [adjugate_one]
  rwa [← Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.one_mul] at this

中文:
定理 det_smul_adjugate_adjugate
  条件: (A : 矩阵 n n α)
  证明: by
  have : A * (A.adjugate * A.adjugate.adjugate) =
      A * (A.det ^ (Fintype.card n - 1) • (1 : Matrix n n α)) := by
    rw [← adjugate_mul_distrib]; rw [adjugate_mul]; rw [adjugate_smul]; rw [adjugate_one]
  rwa [← Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.one_mul] at this

Depends on / 依赖: A.adjugate, A.adjugate.adjugate, A.det, Fintype, Fintype.card, Matrix, Matrix.mul_assoc, Matrix.mul_one, Matrix.mul_smul, Matrix.one_mul, Matrix.smul_mul, adjugate, adjugate_mul, adjugate_mul_distrib, adjugate_one, adjugate_smul, mul_adjugate, mul_assoc, mul_one, mul_smul
-/
theorem det_smul_adjugate_adjugate (A : Matrix n n α) :
    det A • adjugate (adjugate A) = det A ^ (Fintype.card n - 1) • A := by
  have : A * (A.adjugate * A.adjugate.adjugate) =
      A * (A.det ^ (Fintype.card n - 1) • (1 : Matrix n n α)) := by
    rw [← adjugate_mul_distrib]; rw [adjugate_mul]; rw [adjugate_smul]; rw [adjugate_one]
  rwa [← Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.one_mul] at this

/--
theorem `adjugate_adjugate` / 定理 `adjugate_adjugate`

English:
theorem adjugate_adjugate
  given: (A : Matrix n n α) (h : Fintype.card n != 1)
  proof: by
  -- get rid of the `- 2`
  rcases h_card : Fintype.card n with _ | n'
  · subsingleton [Fintype.card_eq_zero_iff.mp h_card]
  cases n'
  · exact (h h_card).elim
  rw [← h_card]
  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mvPolynomialX n n Int
  suffices adjugate (adjugate A') = det A' ^ (Fintype.card n - 2) • A' by
    rw [← mvPolynomialX_mapMatrix_aeval Int A]; rw [← AlgHom.map_adjugate]; rw [← AlgHom.map_adjugate]; rw [this]; rw [← AlgHom.map_det]; rw [← map_pow (MvPolynomial.aeval fun p : n × n => A p.1 p.2)]; rw [AlgHom.mapMatrix_apply]; rw [AlgHom.mapMatrix_apply]; rw [Matrix.map_smul' _ _ _ (map_mul _)]
  have h_card' : Fintype.card n - 2 + 1 = Fintype.card n - 1 := by simp [h_card]
  have is_reg : IsSMulRegular (MvPolynomial (n × n) Int) (det A') := fun x y =>
    mul_left_cancel₀ (det_mvPolynomialX_ne_zero n Int)
  apply is_reg.matrix
  simp only
  rw [smul_smul]; rw [← pow_succ']; rw [h_card']; rw [det_smul_adjugate_adjugate]

中文:
定理 adjugate_adjugate
  条件: (A : 矩阵 n n α) (h : 有限类型.card n != 1)
  证明: by
  -- get rid of the `- 2`
  rcases h_card : Fintype.card n with _ | n'
  · subsingleton [Fintype.card_eq_zero_iff.mp h_card]
  cases n'
  · exact (h h_card).elim
  rw [← h_card]
  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mvPolynomialX n n Int
  suffices adjugate (adjugate A') = det A' ^ (Fintype.card n - 2) • A' by
    rw [← mvPolynomialX_mapMatrix_aeval Int A]; rw [← AlgHom.map_adjugate]; rw [← AlgHom.map_adjugate]; rw [this]; rw [← AlgHom.map_det]; rw [← map_pow (MvPolynomial.aeval fun p : n × n => A p.1 p.2)]; rw [AlgHom.mapMatrix_apply]; rw [AlgHom.mapMatrix_apply]; rw [Matrix.map_smul' _ _ _ (map_mul _)]
  have h_card' : Fintype.card n - 2 + 1 = Fintype.card n - 1 := by simp [h_card]
  have is_reg : IsSMulRegular (MvPolynomial (n × n) Int) (det A') := fun x y =>
    mul_left_cancel₀ (det_mvPolynomialX_ne_zero n Int)
  apply is_reg.matrix
  simp only
  rw [smul_smul]; rw [← pow_succ']; rw [h_card']; rw [det_smul_adjugate_adjugate]
-/
theorem adjugate_adjugate (A : Matrix n n α) (h : Fintype.card n != 1) :
    adjugate (adjugate A) = det A ^ (Fintype.card n - 2) • A := by
  -- get rid of the `- 2`
  rcases h_card : Fintype.card n with _ | n'
  · subsingleton [Fintype.card_eq_zero_iff.mp h_card]
  cases n'
  · exact (h h_card).elim
  rw [← h_card]
  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mvPolynomialX n n Int
  suffices adjugate (adjugate A') = det A' ^ (Fintype.card n - 2) • A' by
    rw [← mvPolynomialX_mapMatrix_aeval Int A]; rw [← AlgHom.map_adjugate]; rw [← AlgHom.map_adjugate]; rw [this]; rw [← AlgHom.map_det]; rw [← map_pow (MvPolynomial.aeval fun p : n × n => A p.1 p.2)]; rw [AlgHom.mapMatrix_apply]; rw [AlgHom.mapMatrix_apply]; rw [Matrix.map_smul' _ _ _ (map_mul _)]
  have h_card' : Fintype.card n - 2 + 1 = Fintype.card n - 1 := by simp [h_card]
  have is_reg : IsSMulRegular (MvPolynomial (n × n) Int) (det A') := fun x y =>
    mul_left_cancel₀ (det_mvPolynomialX_ne_zero n Int)
  apply is_reg.matrix
  simp only
  rw [smul_smul]; rw [← pow_succ']; rw [h_card']; rw [det_smul_adjugate_adjugate]

/--
theorem `adjugate_adjugate'` / 定理 `adjugate_adjugate'`

English:
theorem adjugate_adjugate'
  given: (A : Matrix n n α) [Nontrivial n]
  proof: adjugate_adjugate _ Fintype.one_lt_card.ne'

中文:
定理 adjugate_adjugate'
  条件: (A : 矩阵 n n α) [非平凡 n]
  证明: adjugate_adjugate _ Fintype.one_lt_card.ne'

Depends on / 依赖: Fintype, Fintype.one_lt_card.ne, adjugate_adjugate, one_lt_card
-/
theorem adjugate_adjugate' (A : Matrix n n α) [Nontrivial n] :
    adjugate (adjugate A) = det A ^ (Fintype.card n - 2) • A :=
adjugate_adjugate _ Fintype.one_lt_card.ne'

end Adjugate

end Matrix
