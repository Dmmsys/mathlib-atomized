/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Composition
public import Mathlib.RingTheory.MatrixAlgebra
public import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Algebra isomorphism between matrices of polynomials and polynomials of matrices

We obtain the algebra isomorphism
```
def matPolyEquiv : Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X]
```
which is characterized by
```
coeff (matPolyEquiv m) k i j = coeff (m i j) k
```

We will use this algebra isomorphism to prove the Cayley-Hamilton theorem.
-/

@[expose] public section

universe u v w

open Polynomial TensorProduct
open Algebra.TensorProduct (algHomOfLinearMapTensorProduct includeLeft)

noncomputable section

variable (R A : Type*)
variable [CommSemiring R]
variable [Semiring A] [Algebra R A]

open Matrix

variable {R}
variable {n : Type w} [DecidableEq n] [Fintype n]

/--
Definition of `matPolyEquiv` / `matPolyEquiv` 的定义

English:
definition matPolyEquiv
  signature: : Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X]
  body: ((matrixEquivTensor n R R[X]).trans (Algebra.TensorProduct.comm R _ _)).trans
    (polyEquivTensor R (Matrix n n R)).symm

中文:
定义 matPolyEquiv
  签名: : 矩阵 n n R[X] ≃ₐ[R] (矩阵 n n R)[X]
  定义体: ((matrixEquivTensor n R R[X]).trans (Algebra.TensorProduct.comm R _ _)).trans
    (polyEquivTensor R (Matrix n n R)).symm

Depends on / 依赖: Algebra, Algebra.TensorProduct.comm, Matrix, TensorProduct, matrixEquivTensor, polyEquivTensor
-/
noncomputable def matPolyEquiv : Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X] :=
  ((matrixEquivTensor n R R[X]).trans (Algebra.TensorProduct.comm R _ _)).trans
    (polyEquivTensor R (Matrix n n R)).symm

/--
theorem `matPolyEquiv_symm_C` / 定理 `matPolyEquiv_symm_C`

English:
theorem matPolyEquiv_symm_C
  given: (M : Matrix n n R)
  statement: matPolyEquiv.symm (C M) = M.map C
  proof: by
  simp [matPolyEquiv]

中文:
定理 matPolyEquiv_symm_C
  条件: (M : 矩阵 n n R)
  结论: matPolyEquiv.symm (C M) = M.map C
  证明: by
  simp [matPolyEquiv]
-/
@[simp] theorem matPolyEquiv_symm_C (M : Matrix n n R) : matPolyEquiv.symm (C M) = M.map C := by
  simp [matPolyEquiv]

/--
theorem `matPolyEquiv_map_C` / 定理 `matPolyEquiv_map_C`

English:
theorem matPolyEquiv_map_C
  given: (M : Matrix n n R)
  statement: matPolyEquiv (M.map C) = C M
  proof: by
  rw [← matPolyEquiv_symm_C]; rw [AlgEquiv.apply_symm_apply]

中文:
定理 matPolyEquiv_map_C
  条件: (M : 矩阵 n n R)
  结论: matPolyEquiv (M.map C) = C M
  证明: by
  rw [← matPolyEquiv_symm_C]; rw [AlgEquiv.apply_symm_apply]
-/
@[simp] theorem matPolyEquiv_map_C (M : Matrix n n R) : matPolyEquiv (M.map C) = C M := by
  rw [← matPolyEquiv_symm_C]; rw [AlgEquiv.apply_symm_apply]

/--
theorem `matPolyEquiv_symm_X` / 定理 `matPolyEquiv_symm_X`

English:
theorem matPolyEquiv_symm_X
  proof: by
  simp [matPolyEquiv, Matrix.smul_one_eq_diagonal]

中文:
定理 matPolyEquiv_symm_X
  证明: by
  simp [matPolyEquiv, Matrix.smul_one_eq_diagonal]
-/
@[simp] theorem matPolyEquiv_symm_X :
    matPolyEquiv.symm X = diagonal fun _ : n => (X : R[X]) := by
  simp [matPolyEquiv, Matrix.smul_one_eq_diagonal]

/--
theorem `matPolyEquiv_diagonal_X` / 定理 `matPolyEquiv_diagonal_X`

English:
theorem matPolyEquiv_diagonal_X
  proof: by
  rw [← matPolyEquiv_symm_X]; rw [AlgEquiv.apply_symm_apply]

中文:
定理 matPolyEquiv_diagonal_X
  证明: by
  rw [← matPolyEquiv_symm_X]; rw [AlgEquiv.apply_symm_apply]
-/
@[simp] theorem matPolyEquiv_diagonal_X :
    matPolyEquiv (diagonal fun _ : n => (X : R[X])) = X := by
  rw [← matPolyEquiv_symm_X]; rw [AlgEquiv.apply_symm_apply]

open Finset

unseal Algebra.TensorProduct.mul in
/--
theorem `matPolyEquiv_coeff_apply_aux_1` / 定理 `matPolyEquiv_coeff_apply_aux_1`

English:
theorem matPolyEquiv_coeff_apply_aux_1
  given: (i j : n) (k : Nat) (x : R)
  proof: by
  simp only [matPolyEquiv, AlgEquiv.trans_apply, matrixEquivTensor_apply_single]
  apply (polyEquivTensor R (Matrix n n R)).injective
  simp only [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.comm_tmul,
    polyEquivTensor_apply, eval₂_monomial]
  simp only [one_pow,
    Algebra.TensorProduct

中文:
定理 matPolyEquiv_coeff_apply_aux_1
  条件: (i j : n) (k : 自然数) (x : R)
  证明: by
  simp only [matPolyEquiv, AlgEquiv.trans_apply, matrixEquivTensor_apply_single]
  apply (polyEquivTensor R (Matrix n n R)).injective
  simp only [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.comm_tmul,
    polyEquivTensor_apply, eval₂_monomial]
  simp only [one_pow,
    Algebra.TensorProduct

Depends on / 依赖: AlgEquiv, AlgEquiv.apply_symm_apply, AlgEquiv.trans_apply, Algebra, Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.tmul_pow, Matrix, TensorProduct, TensorProduct.smul_tmul, apply_symm_apply, comm_tmul, injective, matPolyEquiv, matrixEquivTensor_apply_single, one_pow, polyEquivTensor, polyEquivTensor_apply, single, smul_X_eq_monomial, smul_tmul
-/
theorem matPolyEquiv_coeff_apply_aux_1 (i j : n) (k : Nat) (x : R) :
    matPolyEquiv (single i j <| monomial k x) = monomial k (single i j x) := by
  simp only [matPolyEquiv, AlgEquiv.trans_apply, matrixEquivTensor_apply_single]
  apply (polyEquivTensor R (Matrix n n R)).injective
  simp only [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.comm_tmul,
    polyEquivTensor_apply, eval₂_monomial]
  simp only [one_pow,
    Algebra.TensorProduct.tmul_pow]
  rw [← smul_X_eq_monomial]; rw [← TensorProduct.smul_tmul]
  congr with i' <;> simp [single]

/--
theorem `matPolyEquiv_coeff_apply_aux_2` / 定理 `matPolyEquiv_coeff_apply_aux_2`

English:
theorem matPolyEquiv_coeff_apply_aux_2
  given: (i j : n) (p : R[X]) (k : Nat)
  proof: by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    ext
    simp [hp, hq, coeff_add, Matrix.add_apply, single_add]
  · intro k x
    simp only [matPolyEquiv_coeff_apply_aux_1, coeff_monomial]
    split_ifs <;>
      · funext
        simp

@[simp]

中文:
定理 matPolyEquiv_coeff_apply_aux_2
  条件: (i j : n) (p : R[X]) (k : 自然数)
  证明: by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    ext
    simp [hp, hq, coeff_add, Matrix.add_apply, single_add]
  · intro k x
    simp only [matPolyEquiv_coeff_apply_aux_1, coeff_monomial]
    split_ifs <;>
      · funext
        simp

@[simp]

Depends on / 依赖: Matrix, Matrix.add_apply, Polynomial, Polynomial.induction_on, add_apply, coeff_add, coeff_monomial, induction_on, matPolyEquiv_coeff_apply_aux_1, single_add, split_ifs
-/
theorem matPolyEquiv_coeff_apply_aux_2 (i j : n) (p : R[X]) (k : Nat) :
    coeff (matPolyEquiv (single i j p)) k = single i j (coeff p k) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    ext
    simp [hp, hq, coeff_add, Matrix.add_apply, single_add]
  · intro k x
    simp only [matPolyEquiv_coeff_apply_aux_1, coeff_monomial]
    split_ifs <;>
      · funext
        simp

@[simp]
/--
theorem `matPolyEquiv_coeff_apply` / 定理 `matPolyEquiv_coeff_apply`

English:
theorem matPolyEquiv_coeff_apply
  given: (m : Matrix n n R[X]) (k : Nat) (i j : n)
  proof: by
  refine Matrix.induction_on' m ?_ ?_ ?_
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro i' j' x
    rw [matPolyEquiv_coeff_apply_aux_2]
    dsimp [single]
    split_ifs <;> rename_i h
    · constructor
    · simp

@[simp]

中文:
定理 matPolyEquiv_coeff_apply
  条件: (m : 矩阵 n n R[X]) (k : 自然数) (i j : n)
  证明: by
  refine Matrix.induction_on' m ?_ ?_ ?_
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro i' j' x
    rw [matPolyEquiv_coeff_apply_aux_2]
    dsimp [single]
    split_ifs <;> rename_i h
    · constructor
    · simp

@[simp]

Depends on / 依赖: Matrix, Matrix.induction_on, induction_on, matPolyEquiv_coeff_apply_aux_2, rename_i, single, split_ifs
-/
theorem matPolyEquiv_coeff_apply (m : Matrix n n R[X]) (k : Nat) (i j : n) :
    coeff (matPolyEquiv m) k i j = coeff (m i j) k := by
  refine Matrix.induction_on' m ?_ ?_ ?_
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro i' j' x
    rw [matPolyEquiv_coeff_apply_aux_2]
    dsimp [single]
    split_ifs <;> rename_i h
    · constructor
    · simp

@[simp]
/--
theorem `matPolyEquiv_symm_apply_coeff` / 定理 `matPolyEquiv_symm_apply_coeff`

English:
theorem matPolyEquiv_symm_apply_coeff
  given: (p : (Matrix n n R)[X]) (i j : n) (k : Nat)
  proof: by
  have t : p = matPolyEquiv (matPolyEquiv.symm p) := by simp
  conv_rhs => rw [t]
  simp only [matPolyEquiv_coeff_apply]

中文:
定理 matPolyEquiv_symm_apply_coeff
  条件: (p : (矩阵 n n R)[X]) (i j : n) (k : 自然数)
  证明: by
  have t : p = matPolyEquiv (matPolyEquiv.symm p) := by simp
  conv_rhs => rw [t]
  simp only [matPolyEquiv_coeff_apply]

Depends on / 依赖: conv_rhs, matPolyEquiv, matPolyEquiv.symm, matPolyEquiv_coeff_apply
-/
theorem matPolyEquiv_symm_apply_coeff (p : (Matrix n n R)[X]) (i j : n) (k : Nat) :
    coeff (matPolyEquiv.symm p i j) k = coeff p k i j := by
  have t : p = matPolyEquiv (matPolyEquiv.symm p) := by simp
  conv_rhs => rw [t]
  simp only [matPolyEquiv_coeff_apply]

/--
theorem `matPolyEquiv_smul_one` / 定理 `matPolyEquiv_smul_one`

English:
theorem matPolyEquiv_smul_one
  given: (p : R[X])
  proof: by
  ext m i j
  simp only [matPolyEquiv_coeff_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, coeff_map, algebraMap_matrix_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  split_ifs <;> simp

@[simp]

中文:
定理 matPolyEquiv_smul_one
  条件: (p : R[X])
  证明: by
  ext m i j
  simp only [matPolyEquiv_coeff_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, coeff_map, algebraMap_matrix_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  split_ifs <;> simp

@[simp]

Depends on / 依赖: Algebra, Algebra.algebraMap_self, Matrix, Matrix.one_apply, Matrix.smul_apply, RingHom, RingHom.id_apply, algebraMap_matrix_apply, algebraMap_self, coeff_map, id_apply, matPolyEquiv_coeff_apply, mul_ite, mul_one, mul_zero, one_apply, smul_apply, smul_eq_mul, split_ifs
-/
theorem matPolyEquiv_smul_one (p : R[X]) :
    matPolyEquiv (p • (1 : Matrix n n R[X])) = p.map (algebraMap R (Matrix n n R)) := by
  ext m i j
  simp only [matPolyEquiv_coeff_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, coeff_map, algebraMap_matrix_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  split_ifs <;> simp

@[simp]
/--
lemma `matPolyEquiv_map_smul` / 引理 `matPolyEquiv_map_smul`

English:
lemma matPolyEquiv_map_smul
  given: (p : R[X]) (M : Matrix n n R[X])
  proof: by
  rw [← one_mul M]; rw [← smul_mul_assoc]; rw [map_mul]; rw [matPolyEquiv_smul_one]; rw [one_mul]

中文:
引理 matPolyEquiv_map_smul
  条件: (p : R[X]) (M : 矩阵 n n R[X])
  证明: by
  rw [← one_mul M]; rw [← smul_mul_assoc]; rw [map_mul]; rw [matPolyEquiv_smul_one]; rw [one_mul]

Depends on / 依赖: map_mul, matPolyEquiv_smul_one, one_mul, smul_mul_assoc
-/
lemma matPolyEquiv_map_smul (p : R[X]) (M : Matrix n n R[X]) :
    matPolyEquiv (p • M) = p.map (algebraMap _ _) * matPolyEquiv M := by
  rw [← one_mul M]; rw [← smul_mul_assoc]; rw [map_mul]; rw [matPolyEquiv_smul_one]; rw [one_mul]

/--
theorem `matPolyEquiv_symm_map_eval` / 定理 `matPolyEquiv_symm_map_eval`

English:
theorem matPolyEquiv_symm_map_eval
  given: (M : (Matrix n n R)[X]) (r : R)
  proof: by
  suffices ((aeval r).mapMatrix.comp matPolyEquiv.symm.toAlgHom : (Matrix n n R)[X] ->ₐ[R] _) =
      (eval₂AlgHom (AlgHom.id R _) (scalar n r)
        fun x => (scalar_commute _ (Commute.all _) _).symm) from
    DFunLike.congr_fun this M
  ext : 1
  · ext M : 1
    simp [Function.comp_def]
  · s

中文:
定理 matPolyEquiv_symm_map_eval
  条件: (M : (矩阵 n n R)[X]) (r : R)
  证明: by
  suffices ((aeval r).mapMatrix.comp matPolyEquiv.symm.toAlgHom : (Matrix n n R)[X] ->ₐ[R] _) =
      (eval₂AlgHom (AlgHom.id R _) (scalar n r)
        fun x => (scalar_commute _ (Commute.all _) _).symm) from
    DFunLike.congr_fun this M
  ext : 1
  · ext M : 1
    simp [Function.comp_def]
  · s

Depends on / 依赖: AlgHom, AlgHom.id, Commute, Commute.all, DFunLike, DFunLike.congr_fun, Function, Function.comp_def, Matrix, comp_def, congr_fun, mapMatrix, mapMatrix.comp, matPolyEquiv, matPolyEquiv.symm.toAlgHom, scalar, scalar_commute, toAlgHom
-/
theorem matPolyEquiv_symm_map_eval (M : (Matrix n n R)[X]) (r : R) :
    (matPolyEquiv.symm M).map (eval r) = M.eval (scalar n r) := by
  suffices ((aeval r).mapMatrix.comp matPolyEquiv.symm.toAlgHom : (Matrix n n R)[X] ->ₐ[R] _) =
      (eval₂AlgHom (AlgHom.id R _) (scalar n r)
        fun x => (scalar_commute _ (Commute.all _) _).symm) from
    DFunLike.congr_fun this M
  ext : 1
  · ext M : 1
    simp [Function.comp_def]
  · simp

/--
theorem `matPolyEquiv_eval_eq_map` / 定理 `matPolyEquiv_eval_eq_map`

English:
theorem matPolyEquiv_eval_eq_map
  given: (M : Matrix n n R[X]) (r : R)
  proof: by
  simpa only [AlgEquiv.symm_apply_apply] using (matPolyEquiv_symm_map_eval (matPolyEquiv M) r).symm

中文:
定理 matPolyEquiv_eval_eq_map
  条件: (M : 矩阵 n n R[X]) (r : R)
  证明: by
  simpa only [AlgEquiv.symm_apply_apply] using (matPolyEquiv_symm_map_eval (matPolyEquiv M) r).symm

Depends on / 依赖: AlgEquiv, AlgEquiv.symm_apply_apply, matPolyEquiv, matPolyEquiv_symm_map_eval, symm_apply_apply
-/
theorem matPolyEquiv_eval_eq_map (M : Matrix n n R[X]) (r : R) :
    (matPolyEquiv M).eval (scalar n r) = M.map (eval r) := by
  simpa only [AlgEquiv.symm_apply_apply] using (matPolyEquiv_symm_map_eval (matPolyEquiv M) r).symm

-- I feel like this should use `Polynomial.algHom_eval₂_algebraMap`
/--
theorem `matPolyEquiv_eval` / 定理 `matPolyEquiv_eval`

English:
theorem matPolyEquiv_eval
  given: (M : Matrix n n R[X]) (r : R) (i j : n)
  proof: by
  rw [matPolyEquiv_eval_eq_map]; rw [map_apply]

中文:
定理 matPolyEquiv_eval
  条件: (M : 矩阵 n n R[X]) (r : R) (i j : n)
  证明: by
  rw [matPolyEquiv_eval_eq_map]; rw [map_apply]

Depends on / 依赖: map_apply, matPolyEquiv_eval_eq_map
-/
theorem matPolyEquiv_eval (M : Matrix n n R[X]) (r : R) (i j : n) :
    (matPolyEquiv M).eval (scalar n r) i j = (M i j).eval r := by
  rw [matPolyEquiv_eval_eq_map]; rw [map_apply]

/--
theorem `support_subset_support_matPolyEquiv` / 定理 `support_subset_support_matPolyEquiv`

English:
theorem support_subset_support_matPolyEquiv
  given: (m : Matrix n n R[X]) (i j : n)
  proof: by
  intro k
  contrapose
  simp only [notMem_support_iff]
  intro hk
  rw [← matPolyEquiv_coeff_apply]; rw [hk]; rw [Matrix.zero_apply]

中文:
定理 support_subset_support_matPolyEquiv
  条件: (m : 矩阵 n n R[X]) (i j : n)
  证明: by
  intro k
  contrapose
  simp only [notMem_support_iff]
  intro hk
  rw [← matPolyEquiv_coeff_apply]; rw [hk]; rw [Matrix.zero_apply]

Depends on / 依赖: Matrix, Matrix.zero_apply, contrapose, matPolyEquiv_coeff_apply, notMem_support_iff, zero_apply
-/
theorem support_subset_support_matPolyEquiv (m : Matrix n n R[X]) (i j : n) :
    support (m i j) subseteq support (matPolyEquiv m) := by
  intro k
  contrapose
  simp only [notMem_support_iff]
  intro hk
  rw [← matPolyEquiv_coeff_apply]; rw [hk]; rw [Matrix.zero_apply]

/--
theorem `eval_det` / 定理 `eval_det`

English:
theorem eval_det
  given: {R : Type*} [CommRing R] (M : Matrix n n R[X]) (r : R)
  proof: by
  rw [Polynomial.eval]; rw [← coe_eval₂RingHom]; rw [RingHom.map_det]
exact congr_arg det .symm ext fun _ _ => matPolyEquiv_eval _ _ _ _

中文:
定理 eval_det
  条件: {R : 类型} [交换环 R] (M : 矩阵 n n R[X]) (r : R)
  证明: by
  rw [Polynomial.eval]; rw [← coe_eval₂RingHom]; rw [RingHom.map_det]
exact congr_arg det .symm ext fun _ _ => matPolyEquiv_eval _ _ _ _

Depends on / 依赖: Polynomial, Polynomial.eval, RingHom, RingHom.map_det, congr_arg, map_det, matPolyEquiv_eval
-/
theorem eval_det {R : Type*} [CommRing R] (M : Matrix n n R[X]) (r : R) :
    Polynomial.eval r M.det = (Polynomial.eval (scalar n r) (matPolyEquiv M)).det := by
  rw [Polynomial.eval]; rw [← coe_eval₂RingHom]; rw [RingHom.map_det]
exact congr_arg det .symm ext fun _ _ => matPolyEquiv_eval _ _ _ _

/--
lemma `eval_det_add_X_smul` / 引理 `eval_det_add_X_smul`

English:
lemma eval_det_add_X_smul
  given: {R : Type*} [CommRing R] (A : Matrix n n R[X]) (M : Matrix n n R)
  proof: by
  simp only [eval_det, map_zero, map_add, eval_add, Algebra.smul_def, map_mul]
  simp only [Algebra.algebraMap_eq_smul_one, matPolyEquiv_smul_one, map_X, X_mul, eval_mul_X,
    mul_zero, add_zero]

中文:
引理 eval_det_add_X_smul
  条件: {R : 类型} [交换环 R] (A : 矩阵 n n R[X]) (M : 矩阵 n n R)
  证明: by
  simp only [eval_det, map_zero, map_add, eval_add, Algebra.smul_def, map_mul]
  simp only [Algebra.algebraMap_eq_smul_one, matPolyEquiv_smul_one, map_X, X_mul, eval_mul_X,
    mul_zero, add_zero]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Algebra.smul_def, X_mul, add_zero, algebraMap_eq_smul_one, eval_add, eval_det, eval_mul_X, map_X, map_add, map_mul, map_zero, matPolyEquiv_smul_one, mul_zero, smul_def
-/
lemma eval_det_add_X_smul {R : Type*} [CommRing R] (A : Matrix n n R[X]) (M : Matrix n n R) :
    (det (A + (X : R[X]) • M.map C)).eval 0 = (det A).eval 0 := by
  simp only [eval_det, map_zero, map_add, eval_add, Algebra.smul_def, map_mul]
  simp only [Algebra.algebraMap_eq_smul_one, matPolyEquiv_smul_one, map_X, X_mul, eval_mul_X,
    mul_zero, add_zero]

variable {A}
/--
Definition of `RingHom.polyToMatrix` / `RingHom.polyToMatrix` 的定义

English:
definition RingHom.polyToMatrix
  signature: (f : A ->+* Matrix n n R)
  body: matPolyEquiv.symm.toRingHom.comp (mapRingHom f)

中文:
定义 环态射.polyToMatrix
  签名: (f : A ->+* 矩阵 n n R)
  定义体: matPolyEquiv.symm.toRingHom.comp (mapRingHom f)

Depends on / 依赖: mapRingHom, matPolyEquiv, matPolyEquiv.symm.toRingHom.comp, toRingHom
-/
def RingHom.polyToMatrix (f : A ->+* Matrix n n R) : A[X] ->+* Matrix n n R[X] :=
  matPolyEquiv.symm.toRingHom.comp (mapRingHom f)

variable {S : Type*} [CommSemiring S] (f : S ->+* Matrix n n R)

/--
lemma `evalRingHom_mapMatrix_comp_polyToMatrix` / 引理 `evalRingHom_mapMatrix_comp_polyToMatrix`

English:
lemma evalRingHom_mapMatrix_comp_polyToMatrix
  proof: by
  ext <;> simp [RingHom.polyToMatrix, -AlgEquiv.symm_toRingEquiv, diagonal, apply_ite]

中文:
引理 evalRingHom_mapMatrix_comp_polyToMatrix
  证明: by
  ext <;> simp [RingHom.polyToMatrix, -AlgEquiv.symm_toRingEquiv, diagonal, apply_ite]

Depends on / 依赖: AlgEquiv, AlgEquiv.symm_toRingEquiv, RingHom, RingHom.polyToMatrix, apply_ite, diagonal, polyToMatrix, symm_toRingEquiv
-/
lemma evalRingHom_mapMatrix_comp_polyToMatrix :
    (evalRingHom 0).mapMatrix.comp f.polyToMatrix = f.comp (evalRingHom 0) := by
  ext <;> simp [RingHom.polyToMatrix, -AlgEquiv.symm_toRingEquiv, diagonal, apply_ite]

/--
lemma `evalRingHom_mapMatrix_comp_compRingEquiv` / 引理 `evalRingHom_mapMatrix_comp_compRingEquiv`

English:
lemma evalRingHom_mapMatrix_comp_compRingEquiv
  given: {m} [Fintype m] [DecidableEq m]
  proof: by
  ext; simp

中文:
引理 evalRingHom_mapMatrix_comp_compRingEquiv
  条件: {m} [有限类型 m] [DecidableEq m]
  证明: by
  ext; simp
-/
lemma evalRingHom_mapMatrix_comp_compRingEquiv {m} [Fintype m] [DecidableEq m] :
    (evalRingHom 0).mapMatrix.comp (compRingEquiv m n R[X]) =
      (compRingEquiv m n R).toRingHom.comp (evalRingHom 0).mapMatrix.mapMatrix := by
  ext; simp
