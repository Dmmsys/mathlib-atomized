/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Tactic.Field
public import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Transvections

Transvections are matrices of the form `1 + single i j c`, where `single i j c`
is the basic matrix with a `c` at position `(i, j)`. Multiplying by such a transvection on the left
(resp. on the right) amounts to adding `c` times the `j`-th row to the `i`-th row
(resp `c` times the `i`-th column to the `j`-th column). Therefore, they are useful to present
algorithms operating on rows and columns.

Transvections are a special case of *elementary matrices* (according to most references, these also
contain the matrices exchanging rows, and the matrices multiplying a row by a constant).

We show that, over a field, any matrix can be written as `L * D * L'`, where `L` and `L'` are
products of transvections and `D` is diagonal. In other words, one can reduce a matrix to diagonal
form by operations on its rows and columns, a variant of Gauss' pivot algorithm.

## Main definitions and results

* `transvection i j c` is the matrix equal to `1 + single i j c`.
* `TransvectionStruct n R` is a structure containing the data of `i, j, c` and a proof that
  `i ≠ j`. These are often easier to manipulate than straight matrices, especially in inductive
  arguments.

* `exists_list_transvec_mul_diagonal_mul_list_transvec` states that any matrix `M` over a field can
  be written in the form `t_1 * ... * t_k * D * t'_1 * ... * t'_l`, where `D` is diagonal and
  the `t_i`, `t'_j` are transvections.

* `diagonal_transvection_induction` shows that a property which is true for diagonal matrices and
  transvections, and invariant under product, is true for all matrices.
* `diagonal_transvection_induction_of_det_ne_zero` is the same statement over invertible matrices.

## Implementation details

The proof of the reduction results is done inductively on the size of the matrices, reducing an
`(r + 1) × (r + 1)` matrix to a matrix whose last row and column are zeroes, except possibly for
the last diagonal entry. This step is done as follows.

If all the coefficients on the last row and column are zero, there is nothing to do. Otherwise,
one can put a nonzero coefficient in the last diagonal entry by a row or column operation, and then
subtract this last diagonal entry from the other entries in the last row and column to make them
vanish.

This step is done in the type `Fin r ⊕ Unit`, where `Fin r` is useful to choose arbitrarily some
order in which we cancel the coefficients, and the sum structure is useful to use the formalism of
block matrices.

To proceed with the induction, we reindex our matrices to reduce to the above situation.
-/

@[expose] public section


universe u₁ u₂

namespace Matrix

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]
variable [DecidableEq n] [DecidableEq p]
variable [CommRing R]

section Transvection

variable {R n} (i j : n)

/--
Definition of `transvection` / `transvection` 的定义

English:
definition transvection
  signature: (c : R)
  body: 1 + Matrix.single i j c

@[simp]

中文:
定义 transvection
  签名: (c : R)
  定义体: 1 + Matrix.single i j c

@[simp]

Depends on / 依赖: Matrix, Matrix.single, single
-/
def transvection (c : R) : Matrix n n R :=
  1 + Matrix.single i j c

@[simp]
/--
theorem `transvection_zero` / 定理 `transvection_zero`

English:
theorem transvection_zero
  statement: transvection i j (0 : R) = 1
  proof: by simp [transvection]

中文:
定理 transvection_zero
  结论: transvection i j (0 : R) = 1
  证明: by simp [transvection]

Depends on / 依赖: transvection
-/
theorem transvection_zero : transvection i j (0 : R) = 1 := by simp [transvection]

section

/--
theorem `updateRow_eq_transvection` / 定理 `updateRow_eq_transvection`

English:
theorem updateRow_eq_transvection
  given: [Finite n] (c : R)
  proof: by
  cases nonempty_fintype n
  ext a b
  by_cases ha : i = a
  · by_cases hb : j = b
    · simp only [ha, updateRow_self, Pi.add_apply, one_apply, Pi.smul_apply, hb, ↓reduceIte,
        smul_eq_mul, mul_one, transvection, add_apply, single_apply_same]
    · simp only [ha, updateRow_self, Pi.add_app

中文:
定理 updateRow_eq_transvection
  条件: [有限 n] (c : R)
  证明: by
  cases nonempty_fintype n
  ext a b
  by_cases ha : i = a
  · by_cases hb : j = b
    · simp only [ha, updateRow_self, Pi.add_apply, one_apply, Pi.smul_apply, hb, ↓reduceIte,
        smul_eq_mul, mul_one, transvection, add_apply, single_apply_same]
    · simp only [ha, updateRow_self, Pi.add_app

Depends on / 依赖: Ne.symm, Pi.add_apply, Pi.smul_apply, add_apply, add_zero, and_false, mul_one, mul_zero, nonempty_fintype, not_false_eq_true, one_apply, reduceIte, single_apply_, single_apply_of_ne, single_apply_same, smul_apply, smul_eq_mul, transvection, updateRow_ne, updateRow_self
-/
theorem updateRow_eq_transvection [Finite n] (c : R) :
    updateRow (1 : Matrix n n R) i ((1 : Matrix n n R) i + c • (1 : Matrix n n R) j) =
      transvection i j c := by
  cases nonempty_fintype n
  ext a b
  by_cases ha : i = a
  · by_cases hb : j = b
    · simp only [ha, updateRow_self, Pi.add_apply, one_apply, Pi.smul_apply, hb, ↓reduceIte,
        smul_eq_mul, mul_one, transvection, add_apply, single_apply_same]
    · simp only [ha, updateRow_self, Pi.add_apply, one_apply, Pi.smul_apply, hb, ↓reduceIte,
        smul_eq_mul, mul_zero, add_zero, transvection, add_apply, and_false, not_false_eq_true,
        single_apply_of_ne]
  · simp only [updateRow_ne, transvection, ha, Ne.symm ha, single_apply_of_ne, add_zero,
      Ne, not_false_iff,
      false_and, add_apply]

variable [Fintype n]

/--
theorem `transvection_mul_transvection_same` / 定理 `transvection_mul_transvection_same`

English:
theorem transvection_mul_transvection_same
  given: (h : i != j) (c d : R)
  proof: by
  simp [transvection, Matrix.add_mul, Matrix.mul_add, h.symm, add_assoc,
    single_add]

@[simp]

中文:
定理 transvection_mul_transvection_same
  条件: (h : i != j) (c d : R)
  证明: by
  simp [transvection, Matrix.add_mul, Matrix.mul_add, h.symm, add_assoc,
    single_add]

@[simp]

Depends on / 依赖: Matrix, Matrix.add_mul, Matrix.mul_add, add_assoc, add_mul, h.symm, mul_add, single_add, transvection
-/
theorem transvection_mul_transvection_same (h : i != j) (c d : R) :
    transvection i j c * transvection i j d = transvection i j (c + d) := by
  simp [transvection, Matrix.add_mul, Matrix.mul_add, h.symm, add_assoc,
    single_add]

@[simp]
/--
theorem `transvection_mul_apply_same` / 定理 `transvection_mul_apply_same`

English:
theorem transvection_mul_apply_same
  given: {m : Type*} (b : m) (c : R) (M : Matrix n m R)
  proof: by simp [transvection, Matrix.add_mul]

@[simp]

中文:
定理 transvection_mul_apply_same
  条件: {m : 类型} (b : m) (c : R) (M : 矩阵 n m R)
  证明: by simp [transvection, Matrix.add_mul]

@[simp]

Depends on / 依赖: Matrix, Matrix.add_mul, add_mul, transvection
-/
theorem transvection_mul_apply_same {m : Type*} (b : m) (c : R) (M : Matrix n m R) :
    (transvection i j c * M) i b = M i b + c * M j b := by simp [transvection, Matrix.add_mul]

@[simp]
/--
theorem `mul_transvection_apply_same` / 定理 `mul_transvection_apply_same`

English:
theorem mul_transvection_apply_same
  given: {m : Type*} (a : m) (c : R) (M : Matrix m n R)
  proof: by
  simp [transvection, Matrix.mul_add, mul_comm]

@[simp]

中文:
定理 mul_transvection_apply_same
  条件: {m : 类型} (a : m) (c : R) (M : 矩阵 m n R)
  证明: by
  simp [transvection, Matrix.mul_add, mul_comm]

@[simp]

Depends on / 依赖: Matrix, Matrix.mul_add, mul_add, mul_comm, transvection
-/
theorem mul_transvection_apply_same {m : Type*} (a : m) (c : R) (M : Matrix m n R) :
    (M * transvection i j c) a j = M a j + c * M a i := by
  simp [transvection, Matrix.mul_add, mul_comm]

@[simp]
/--
theorem `transvection_mul_apply_of_ne` / 定理 `transvection_mul_apply_of_ne`

English:
theorem transvection_mul_apply_of_ne
  statement: {m : Type*} (a : n) (b : m) (ha : a != i) (c : R)
  proof: by simp [transvection, Matrix.add_mul, ha]

@[simp]

中文:
定理 transvection_mul_apply_of_ne
  结论: {m : 类型} (a : n) (b : m) (ha : a != i) (c : R)
  证明: by simp [transvection, Matrix.add_mul, ha]

@[simp]

Depends on / 依赖: Matrix, Matrix.add_mul, add_mul, transvection
-/
theorem transvection_mul_apply_of_ne {m : Type*} (a : n) (b : m) (ha : a != i) (c : R)
    (M : Matrix n m R) :
    (transvection i j c * M) a b = M a b := by simp [transvection, Matrix.add_mul, ha]

@[simp]
/--
theorem `mul_transvection_apply_of_ne` / 定理 `mul_transvection_apply_of_ne`

English:
theorem mul_transvection_apply_of_ne
  statement: {m : Type*} (a : m) (b : n) (hb : b != j) (c : R)
  proof: by simp [transvection, Matrix.mul_add, hb]

@[simp]

中文:
定理 mul_transvection_apply_of_ne
  结论: {m : 类型} (a : m) (b : n) (hb : b != j) (c : R)
  证明: by simp [transvection, Matrix.mul_add, hb]

@[simp]

Depends on / 依赖: Matrix, Matrix.mul_add, mul_add, transvection
-/
theorem mul_transvection_apply_of_ne {m : Type*} (a : m) (b : n) (hb : b != j) (c : R)
    (M : Matrix m n R) :
    (M * transvection i j c) a b = M a b := by simp [transvection, Matrix.mul_add, hb]

@[simp]
/--
theorem `det_transvection_of_ne` / 定理 `det_transvection_of_ne`

English:
theorem det_transvection_of_ne
  given: (h : i != j) (c : R)
  statement: det (transvection i j c) = 1
  proof: by
  rw [← updateRow_eq_transvection i j]; rw [det_updateRow_add_smul_self _ h]; rw [det_one]

中文:
定理 det_transvection_of_ne
  条件: (h : i != j) (c : R)
  结论: det (transvection i j c) = 1
  证明: by
  rw [← updateRow_eq_transvection i j]; rw [det_updateRow_add_smul_self _ h]; rw [det_one]

Depends on / 依赖: det_one, det_updateRow_add_smul_self, updateRow_eq_transvection
-/
theorem det_transvection_of_ne (h : i != j) (c : R) : det (transvection i j c) = 1 := by
  rw [← updateRow_eq_transvection i j]; rw [det_updateRow_add_smul_self _ h]; rw [det_one]

end

variable (R n)

/--
Definition of `TransvectionStruct` / `TransvectionStruct` 的定义

English:
structure TransvectionStruct
  parameters: where
  axioms and operations (3):
    - (i(j) : n)
    - hij : i != j
    - c : R

中文:
结构 平换结构
  参数: where
  公理与运算 (3 个):
    - (i(j) : n)
    - hij : i != j
    - c : R
-/
structure TransvectionStruct where
  (i j : n)
  hij : i != j
  c : R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: n] : Nonempty (TransvectionStruct n R)
  body: by
  choose x y hxy using exists_pair_ne n
  exact ⟨⟨x, y, hxy, 0⟩⟩

中文:
实例 [非平凡
  签名: n] : 非空 (平换结构 n R)
  定义体: by
  choose x y hxy using exists_pair_ne n
  exact ⟨⟨x, y, hxy, 0⟩⟩

Depends on / 依赖: exists_pair_ne
-/
instance [Nontrivial n] : Nonempty (TransvectionStruct n R) := by
  choose x y hxy using exists_pair_ne n
  exact ⟨⟨x, y, hxy, 0⟩⟩

namespace TransvectionStruct

variable {R n}

/--
Definition of `toMatrix` / `toMatrix` 的定义

English:
definition toMatrix
  signature: (t : TransvectionStruct n R)
  body: transvection t.i t.j t.c

@[simp]

中文:
定义 toMatrix
  签名: (t : 平换结构 n R)
  定义体: transvection t.i t.j t.c

@[simp]

Depends on / 依赖: transvection
-/
def toMatrix (t : TransvectionStruct n R) : Matrix n n R :=
  transvection t.i t.j t.c

@[simp]
/--
theorem `toMatrix_mk` / 定理 `toMatrix_mk`

English:
theorem toMatrix_mk
  given: (i j : n) (hij : i != j) (c : R)
  proof: rfl

@[simp]

中文:
定理 toMatrix_mk
  条件: (i j : n) (hij : i != j) (c : R)
  证明: rfl

@[simp]
-/
theorem toMatrix_mk (i j : n) (hij : i != j) (c : R) :
    TransvectionStruct.toMatrix ⟨i, j, hij, c⟩ = transvection i j c :=
  rfl

@[simp]
/--
theorem `det` / 定理 `det`

English:
theorem det
  given: [Fintype n] (t : TransvectionStruct n R)
  statement: det t.toMatrix = 1
  proof: det_transvection_of_ne _ _ t.hij _

@[simp]

中文:
定理 det
  条件: [有限类型 n] (t : 平换结构 n R)
  结论: det t.toMatrix = 1
  证明: det_transvection_of_ne _ _ t.hij _

@[simp]
-/
protected theorem det [Fintype n] (t : TransvectionStruct n R) : det t.toMatrix = 1 :=
  det_transvection_of_ne _ _ t.hij _

@[simp]
/--
theorem `det_toMatrix_prod` / 定理 `det_toMatrix_prod`

English:
theorem det_toMatrix_prod
  given: [Fintype n] (L : List (TransvectionStruct n R))
  proof: by
  induction L with
  | nil => simp
  | cons _ _ IH => simp [IH]

中文:
定理 det_toMatrix_prod
  条件: [有限类型 n] (L : 列表 (平换结构 n R))
  证明: by
  induction L with
  | nil => simp
  | cons _ _ IH => simp [IH]
-/
theorem det_toMatrix_prod [Fintype n] (L : List (TransvectionStruct n R)) :
    det (L.map toMatrix).prod = 1 := by
  induction L with
  | nil => simp
  | cons _ _ IH => simp [IH]

/-- The inverse of a `TransvectionStruct`, designed so that `t.inv.toMatrix` is the inverse of
`t.toMatrix`. -/
@[simps]
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: (t : TransvectionStruct n R)
  body: t.i
  j := t.j
  hij := t.hij
  c := -t.c

中文:
定义 inv
  签名: (t : 平换结构 n R)
  定义体: t.i
  j := t.j
  hij := t.hij
  c := -t.c
-/
protected def inv (t : TransvectionStruct n R) : TransvectionStruct n R where
  i := t.i
  j := t.j
  hij := t.hij
  c := -t.c

section

variable [Fintype n]

/--
theorem `inv_mul` / 定理 `inv_mul`

English:
theorem inv_mul
  given: (t : TransvectionStruct n R)
  statement: t.inv.toMatrix * t.toMatrix = 1
  proof: by
  rcases t with ⟨_, _, t_hij⟩
  simp [toMatrix, transvection_mul_transvection_same, t_hij]

中文:
定理 inv_mul
  条件: (t : 平换结构 n R)
  结论: t.inv.toMatrix * t.toMatrix = 1
  证明: by
  rcases t with ⟨_, _, t_hij⟩
  simp [toMatrix, transvection_mul_transvection_same, t_hij]

Depends on / 依赖: t_hij, toMatrix, transvection_mul_transvection_same
-/
theorem inv_mul (t : TransvectionStruct n R) : t.inv.toMatrix * t.toMatrix = 1 := by
  rcases t with ⟨_, _, t_hij⟩
  simp [toMatrix, transvection_mul_transvection_same, t_hij]

/--
theorem `mul_inv` / 定理 `mul_inv`

English:
theorem mul_inv
  given: (t : TransvectionStruct n R)
  statement: t.toMatrix * t.inv.toMatrix = 1
  proof: by
  rcases t with ⟨_, _, t_hij⟩
  simp [toMatrix, transvection_mul_transvection_same, t_hij]

中文:
定理 mul_inv
  条件: (t : 平换结构 n R)
  结论: t.toMatrix * t.inv.toMatrix = 1
  证明: by
  rcases t with ⟨_, _, t_hij⟩
  simp [toMatrix, transvection_mul_transvection_same, t_hij]

Depends on / 依赖: t_hij, toMatrix, transvection_mul_transvection_same
-/
theorem mul_inv (t : TransvectionStruct n R) : t.toMatrix * t.inv.toMatrix = 1 := by
  rcases t with ⟨_, _, t_hij⟩
  simp [toMatrix, transvection_mul_transvection_same, t_hij]

/--
theorem `reverse_inv_prod_mul_prod` / 定理 `reverse_inv_prod_mul_prod`

English:
theorem reverse_inv_prod_mul_prod
  given: (L : List (TransvectionStruct n R))
  proof: by
  induction L with
  | nil => simp
  | cons t L IH =>
    suffices
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (t.inv.toMatrix * t.toMatrix) *
          (L.map toMatrix).prod = 1
      by simpa [Matrix.mul_assoc]
    simpa [inv_mul] using IH

中文:
定理 reverse_inv_prod_mul_prod
  条件: (L : 列表 (平换结构 n R))
  证明: by
  induction L with
  | nil => simp
  | cons t L IH =>
    suffices
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (t.inv.toMatrix * t.toMatrix) *
          (L.map toMatrix).prod = 1
      by simpa [Matrix.mul_assoc]
    simpa [inv_mul] using IH

Depends on / 依赖: L.map, L.reverse.map, Matrix, Matrix.mul_assoc, TransvectionStruct, TransvectionStruct.inv, inv_mul, mul_assoc, reverse, t.inv.toMatrix, t.toMatrix, toMatrix
-/
theorem reverse_inv_prod_mul_prod (L : List (TransvectionStruct n R)) :
    (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod = 1 := by
  induction L with
  | nil => simp
  | cons t L IH =>
    suffices
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (t.inv.toMatrix * t.toMatrix) *
          (L.map toMatrix).prod = 1
      by simpa [Matrix.mul_assoc]
    simpa [inv_mul] using IH

/--
theorem `prod_mul_reverse_inv_prod` / 定理 `prod_mul_reverse_inv_prod`

English:
theorem prod_mul_reverse_inv_prod
  given: (L : List (TransvectionStruct n R))
  proof: by
  induction L with
  | nil => simp
  | cons t L IH =>
    suffices
      t.toMatrix *
            ((L.map toMatrix).prod * (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod) *
          t.inv.toMatrix = 1
      by simpa [Matrix.mul_assoc]
    simp_rw [IH, Matrix.mul_one, t.mul_inv]

中文:
定理 prod_mul_reverse_inv_prod
  条件: (L : 列表 (平换结构 n R))
  证明: by
  induction L with
  | nil => simp
  | cons t L IH =>
    suffices
      t.toMatrix *
            ((L.map toMatrix).prod * (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod) *
          t.inv.toMatrix = 1
      by simpa [Matrix.mul_assoc]
    simp_rw [IH, Matrix.mul_one, t.mul_inv]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.constSMul, L.map, L.reverse.map, Matrix, Matrix.mul_assoc, Matrix.mul_one, TransvectionStruct, TransvectionStruct.inv, constSMul, hausdorffMeasure_preimage, mul_assoc, mul_inv, mul_one, reverse, simp_rw, t.inv.toMatrix, t.mul_inv, t.toMatrix, toMatrix
-/
theorem prod_mul_reverse_inv_prod (L : List (TransvectionStruct n R)) :
    (L.map toMatrix).prod * (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod = 1 := by
  induction L with
  | nil => simp
  | cons t L IH =>
    suffices
      t.toMatrix *
            ((L.map toMatrix).prod * (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod) *
          t.inv.toMatrix = 1
      by simpa [Matrix.mul_assoc]
    simp_rw [IH, Matrix.mul_one, t.mul_inv]

/--
theorem `isUnit_prod_comp_inverse` / 定理 `isUnit_prod_comp_inverse`

English:
theorem isUnit_prod_comp_inverse
  given: (L : List (TransvectionStruct n R))
  proof: by
  refine IsUnit.of_mul_eq_one (L.reverse.map toMatrix).prod ?_
  rw [← reverse_inv_prod_mul_prod L.reverse]; rw [L.reverse_reverse]

中文:
定理 isUnit_prod_comp_inverse
  条件: (L : 列表 (平换结构 n R))
  证明: by
  refine IsUnit.of_mul_eq_one (L.reverse.map toMatrix).prod ?_
  rw [← reverse_inv_prod_mul_prod L.reverse]; rw [L.reverse_reverse]

Depends on / 依赖: IsUnit, IsUnit.of_mul_eq_one, IsometryEquiv, IsometryEquiv.constSMul, L.reverse, L.reverse.map, L.reverse_reverse, constSMul, map_hausdorffMeasure, of_mul_eq_one, reverse, reverse_inv_prod_mul_prod, reverse_reverse, toMatrix
-/
theorem isUnit_prod_comp_inverse (L : List (TransvectionStruct n R)) :
    IsUnit (L.map (toMatrix ∘ .inv)).prod := by
  refine IsUnit.of_mul_eq_one (L.reverse.map toMatrix).prod ?_
  rw [← reverse_inv_prod_mul_prod L.reverse]; rw [L.reverse_reverse]

/--
theorem `_root_.Matrix.mem_range_scalar_of_commute_transvectionStruct` / 定理 `_root_.Matrix.mem_range_scalar_of_commute_transvectionStruct`

English:
theorem _root_.Matrix.mem_range_scalar_of_commute_transvectionStruct
  statement: {M : Matrix n n R}
  proof: by
  refine mem_range_scalar_of_commute_single ?_
  intro i j hij
  simpa [transvection, mul_add, add_mul] using! (hM ⟨i, j, hij, 1⟩).eq

中文:
定理 _root_.矩阵.mem_range_scalar_of_commute_transvectionStruct
  结论: {M : 矩阵 n n R}
  证明: by
  refine mem_range_scalar_of_commute_single ?_
  intro i j hij
  simpa [transvection, mul_add, add_mul] using! (hM ⟨i, j, hij, 1⟩).eq

Depends on / 依赖: IsometryEquiv, IsometryEquiv.constSMul, MulOpposite, MulOpposite.op, add_mul, constSMul, map_hausdorffMeasure, mem_range_scalar_of_commute_single, mul_add, transvection
-/
theorem _root_.Matrix.mem_range_scalar_of_commute_transvectionStruct {M : Matrix n n R}
    (hM : forall t : TransvectionStruct n R, Commute t.toMatrix M) :
    M in Set.range (Matrix.scalar n) := by
  refine mem_range_scalar_of_commute_single ?_
  intro i j hij
  simpa [transvection, mul_add, add_mul] using! (hM ⟨i, j, hij, 1⟩).eq

/--
theorem `_root_.Matrix.mem_range_scalar_iff_commute_transvectionStruct` / 定理 `_root_.Matrix.mem_range_scalar_iff_commute_transvectionStruct`

English:
theorem _root_.Matrix.mem_range_scalar_iff_commute_transvectionStruct
  given: {M : Matrix n n R}
  proof: by
  refine ⟨fun h t => ?_, mem_range_scalar_of_commute_transvectionStruct⟩
  rw [mem_range_scalar_iff_commute_single] at h
  refine (Commute.one_left M).add_left ?_
  convert! (h _ _ t.hij).smul_left t.c using 1
  rw [smul_single]; rw [smul_eq_mul]; rw [mul_one]

中文:
定理 _root_.矩阵.mem_range_scalar_iff_commute_transvectionStruct
  条件: {M : 矩阵 n n R}
  证明: by
  refine ⟨fun h t => ?_, mem_range_scalar_of_commute_transvectionStruct⟩
  rw [mem_range_scalar_iff_commute_single] at h
  refine (Commute.one_left M).add_left ?_
  convert! (h _ _ t.hij).smul_left t.c using 1
  rw [smul_single]; rw [smul_eq_mul]; rw [mul_one]

Depends on / 依赖: Commute, Commute.one_left, add_left, convert, mem_range_scalar_iff_commute_single, mem_range_scalar_of_commute_transvectionStruct, mul_one, one_left, smul_eq_mul, smul_left, smul_single, t.hij
-/
theorem _root_.Matrix.mem_range_scalar_iff_commute_transvectionStruct {M : Matrix n n R} :
    M in Set.range (Matrix.scalar n) ↔ forall t : TransvectionStruct n R, Commute t.toMatrix M := by
  refine ⟨fun h t => ?_, mem_range_scalar_of_commute_transvectionStruct⟩
  rw [mem_range_scalar_iff_commute_single] at h
  refine (Commute.one_left M).add_left ?_
  convert! (h _ _ t.hij).smul_left t.c using 1
  rw [smul_single]; rw [smul_eq_mul]; rw [mul_one]

end

open Sum

/--
Definition of `sumInl` / `sumInl` 的定义

English:
definition sumInl
  signature: (t : TransvectionStruct n R)
  body: inl t.i
  j := inl t.j
  hij := by simp [t.hij]
  c := t.c

中文:
定义 sumInl
  签名: (t : 平换结构 n R)
  定义体: inl t.i
  j := inl t.j
  hij := by simp [t.hij]
  c := t.c
-/
def sumInl (t : TransvectionStruct n R) : TransvectionStruct (n oplus p) R where
  i := inl t.i
  j := inl t.j
  hij := by simp [t.hij]
  c := t.c

/--
theorem `toMatrix_sumInl` / 定理 `toMatrix_sumInl`

English:
theorem toMatrix_sumInl
  given: (t : TransvectionStruct n R)
  proof: by
  cases t
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · by_cases h : a = b <;> simp [TransvectionStruct.sumInl, transvection, h, single]
  · simp [TransvectionStruct.sumInl, transvection]
  · simp [TransvectionStruct.sumInl, transvection]
  · by_cases h : a = b <;> simp [Transvectio

中文:
定理 toMatrix_sumInl
  条件: (t : 平换结构 n R)
  证明: by
  cases t
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · by_cases h : a = b <;> simp [TransvectionStruct.sumInl, transvection, h, single]
  · simp [TransvectionStruct.sumInl, transvection]
  · simp [TransvectionStruct.sumInl, transvection]
  · by_cases h : a = b <;> simp [Transvectio

Depends on / 依赖: TransvectionStruct, TransvectionStruct.sumInl, single, sumInl, transvection
-/
theorem toMatrix_sumInl (t : TransvectionStruct n R) :
    (t.sumInl p).toMatrix = fromBlocks t.toMatrix 0 0 1 := by
  cases t
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · by_cases h : a = b <;> simp [TransvectionStruct.sumInl, transvection, h, single]
  · simp [TransvectionStruct.sumInl, transvection]
  · simp [TransvectionStruct.sumInl, transvection]
  · by_cases h : a = b <;> simp [TransvectionStruct.sumInl, transvection, h]

@[simp]
/--
theorem `sumInl_toMatrix_prod_mul` / 定理 `sumInl_toMatrix_prod_mul`

English:
theorem sumInl_toMatrix_prod_mul
  statement: [Fintype n] [Fintype p] (M : Matrix n n R)
  proof: by
  induction L with
  | nil => simp
  | cons t L IH => simp [Matrix.mul_assoc, IH, toMatrix_sumInl, fromBlocks_multiply]

@[simp]

中文:
定理 sumInl_toMatrix_prod_mul
  结论: [有限类型 n] [有限类型 p] (M : 矩阵 n n R)
  证明: by
  induction L with
  | nil => simp
  | cons t L IH => simp [Matrix.mul_assoc, IH, toMatrix_sumInl, fromBlocks_multiply]

@[simp]

Depends on / 依赖: Matrix, Matrix.mul_assoc, fromBlocks_multiply, mul_assoc, toMatrix_sumInl
-/
theorem sumInl_toMatrix_prod_mul [Fintype n] [Fintype p] (M : Matrix n n R)
    (L : List (TransvectionStruct n R)) (N : Matrix p p R) :
    (L.map (toMatrix ∘ sumInl p)).prod * fromBlocks M 0 0 N =
      fromBlocks ((L.map toMatrix).prod * M) 0 0 N := by
  induction L with
  | nil => simp
  | cons t L IH => simp [Matrix.mul_assoc, IH, toMatrix_sumInl, fromBlocks_multiply]

@[simp]
/--
theorem `mul_sumInl_toMatrix_prod` / 定理 `mul_sumInl_toMatrix_prod`

English:
theorem mul_sumInl_toMatrix_prod
  statement: [Fintype n] [Fintype p] (M : Matrix n n R)
  proof: by
  induction L generalizing M N with
  | nil => simp
  | cons t L IH => simp [IH, toMatrix_sumInl, fromBlocks_multiply]

中文:
定理 mul_sumInl_toMatrix_prod
  结论: [有限类型 n] [有限类型 p] (M : 矩阵 n n R)
  证明: by
  induction L generalizing M N with
  | nil => simp
  | cons t L IH => simp [IH, toMatrix_sumInl, fromBlocks_multiply]

Depends on / 依赖: fromBlocks_multiply, generalizing, toMatrix_sumInl
-/
theorem mul_sumInl_toMatrix_prod [Fintype n] [Fintype p] (M : Matrix n n R)
    (L : List (TransvectionStruct n R)) (N : Matrix p p R) :
    fromBlocks M 0 0 N * (L.map (toMatrix ∘ sumInl p)).prod =
      fromBlocks (M * (L.map toMatrix).prod) 0 0 N := by
  induction L generalizing M N with
  | nil => simp
  | cons t L IH => simp [IH, toMatrix_sumInl, fromBlocks_multiply]

variable {p}

/--
Definition of `reindexEquiv` / `reindexEquiv` 的定义

English:
definition reindexEquiv
  signature: (e : n ≃ p) (t : TransvectionStruct n R)
  body: e t.i
  j := e t.j
  hij := by simp [t.hij]
  c := t.c

中文:
定义 reindexEquiv
  签名: (e : n ≃ p) (t : 平换结构 n R)
  定义体: e t.i
  j := e t.j
  hij := by simp [t.hij]
  c := t.c
-/
def reindexEquiv (e : n ≃ p) (t : TransvectionStruct n R) : TransvectionStruct p R where
  i := e t.i
  j := e t.j
  hij := by simp [t.hij]
  c := t.c

variable [Fintype n] [Fintype p]

/--
theorem `toMatrix_reindexEquiv` / 定理 `toMatrix_reindexEquiv`

English:
theorem toMatrix_reindexEquiv
  given: (e : n ≃ p) (t : TransvectionStruct n R)
  proof: by
  rcases t with ⟨t_i, t_j, _⟩
  ext a b
  simp only [reindexEquiv, transvection, toMatrix_mk]
  by_cases ha : e t_i = a <;> by_cases hb : e t_j = b <;> by_cases hab : a = b <;>
    simp [ha, hb, hab, e.eq_symm_apply, single]

中文:
定理 toMatrix_reindexEquiv
  条件: (e : n ≃ p) (t : 平换结构 n R)
  证明: by
  rcases t with ⟨t_i, t_j, _⟩
  ext a b
  simp only [reindexEquiv, transvection, toMatrix_mk]
  by_cases ha : e t_i = a <;> by_cases hb : e t_j = b <;> by_cases hab : a = b <;>
    simp [ha, hb, hab, e.eq_symm_apply, single]

Depends on / 依赖: e.eq_symm_apply, eq_symm_apply, reindexEquiv, single, toMatrix_mk, transvection
-/
theorem toMatrix_reindexEquiv (e : n ≃ p) (t : TransvectionStruct n R) :
    (t.reindexEquiv e).toMatrix = reindexAlgEquiv R _ e t.toMatrix := by
  rcases t with ⟨t_i, t_j, _⟩
  ext a b
  simp only [reindexEquiv, transvection, toMatrix_mk]
  by_cases ha : e t_i = a <;> by_cases hb : e t_j = b <;> by_cases hab : a = b <;>
    simp [ha, hb, hab, e.eq_symm_apply, single]

/--
theorem `toMatrix_reindexEquiv_prod` / 定理 `toMatrix_reindexEquiv_prod`

English:
theorem toMatrix_reindexEquiv_prod
  given: (e : n ≃ p) (L : List (TransvectionStruct n R))
  proof: by
  induction L with
  | nil => simp
  | cons t L IH => simp [toMatrix_reindexEquiv, IH]

中文:
定理 toMatrix_reindexEquiv_prod
  条件: (e : n ≃ p) (L : 列表 (平换结构 n R))
  证明: by
  induction L with
  | nil => simp
  | cons t L IH => simp [toMatrix_reindexEquiv, IH]

Depends on / 依赖: toMatrix_reindexEquiv
-/
theorem toMatrix_reindexEquiv_prod (e : n ≃ p) (L : List (TransvectionStruct n R)) :
    (L.map (toMatrix ∘ reindexEquiv e)).prod = reindexAlgEquiv R _ e (L.map toMatrix).prod := by
  induction L with
  | nil => simp
  | cons t L IH => simp [toMatrix_reindexEquiv, IH]

end TransvectionStruct

end Transvection

/-!
### Reducing matrices by left and right multiplication by transvections

In this section, we show that any matrix can be reduced to diagonal form by left and right
multiplication by transvections (or, equivalently, by elementary operations on lines and columns).
The main step is to kill the last row and column of a matrix in `Fin r ⊕ Unit` with nonzero last
coefficient, by subtracting this coefficient from the other ones. The list of these operations is
recorded in `list_transvec_col M` and `list_transvec_row M`. We have to analyze inductively how
these operations affect the coefficients in the last row and the last column to conclude that they
have the desired effect.

Once this is done, one concludes the reduction by induction on the size
of the matrices, through a suitable reindexing to identify any fintype with `Fin r ⊕ Unit`.
-/


namespace Pivot

variable {R} {r : Nat} (M : Matrix (Fin r oplus Unit) (Fin r oplus Unit) 𝕜)

open Unit Sum TransvectionStruct

/--
Definition of `listTransvecCol` / `listTransvecCol` 的定义

English:
definition listTransvecCol
  signature: : List (Matrix (Fin r oplus Unit) (Fin r oplus Unit) 𝕜)
  body: List.ofFn fun i : Fin r =>
transvection (inl i) (inr unit) -M (inl i) (inr unit) / M (inr unit) (inr unit)

中文:
定义 listTransvecCol
  签名: : 列表 (矩阵 (有限集 r oplus 单元) (有限集 r oplus 单元) 𝕜)
  定义体: List.ofFn fun i : Fin r =>
transvection (inl i) (inr unit) -M (inl i) (inr unit) / M (inr unit) (inr unit)

Depends on / 依赖: List.ofFn, transvection
-/
def listTransvecCol : List (Matrix (Fin r oplus Unit) (Fin r oplus Unit) 𝕜) :=
  List.ofFn fun i : Fin r =>
transvection (inl i) (inr unit) -M (inl i) (inr unit) / M (inr unit) (inr unit)

/--
Definition of `listTransvecRow` / `listTransvecRow` 的定义

English:
definition listTransvecRow
  signature: : List (Matrix (Fin r oplus Unit) (Fin r oplus Unit) 𝕜)
  body: List.ofFn fun i : Fin r =>
transvection (inr unit) (inl i) -M (inr unit) (inl i) / M (inr unit) (inr unit)

@[simp]

中文:
定义 listTransvecRow
  签名: : 列表 (矩阵 (有限集 r oplus 单元) (有限集 r oplus 单元) 𝕜)
  定义体: List.ofFn fun i : Fin r =>
transvection (inr unit) (inl i) -M (inr unit) (inl i) / M (inr unit) (inr unit)

@[simp]

Depends on / 依赖: List.ofFn, transvection
-/
def listTransvecRow : List (Matrix (Fin r oplus Unit) (Fin r oplus Unit) 𝕜) :=
  List.ofFn fun i : Fin r =>
transvection (inr unit) (inl i) -M (inr unit) (inl i) / M (inr unit) (inr unit)

@[simp]
/--
theorem `length_listTransvecCol` / 定理 `length_listTransvecCol`

English:
theorem length_listTransvecCol
  statement: (listTransvecCol M).length = r
  proof: by simp [listTransvecCol]

中文:
定理 length_listTransvecCol
  结论: (listTransvecCol M).length = r
  证明: by simp [listTransvecCol]

Depends on / 依赖: listTransvecCol
-/
theorem length_listTransvecCol : (listTransvecCol M).length = r := by simp [listTransvecCol]

/--
theorem `listTransvecCol_getElem` / 定理 `listTransvecCol_getElem`

English:
theorem listTransvecCol_getElem
  given: {i : Nat} (h : i < (listTransvecCol M).length)
  proof: ⟨i, length_listTransvecCol M ▸ h⟩
transvection (inl i') (inr unit) -M (inl i') (inr unit) / M (inr unit) (inr unit) := by
  simp [listTransvecCol]

@[simp]

中文:
定理 listTransvecCol_getElem
  条件: {i : 自然数} (h : i < (listTransvecCol M).length)
  证明: ⟨i, length_listTransvecCol M ▸ h⟩
transvection (inl i') (inr unit) -M (inl i') (inr unit) / M (inr unit) (inr unit) := by
  simp [listTransvecCol]

@[simp]

Depends on / 依赖: length_listTransvecCol
-/
theorem listTransvecCol_getElem {i : Nat} (h : i < (listTransvecCol M).length) :
    (listTransvecCol M)[i] =
      letI i' : Fin r := ⟨i, length_listTransvecCol M ▸ h⟩
transvection (inl i') (inr unit) -M (inl i') (inr unit) / M (inr unit) (inr unit) := by
  simp [listTransvecCol]

@[simp]
/--
theorem `length_listTransvecRow` / 定理 `length_listTransvecRow`

English:
theorem length_listTransvecRow
  statement: (listTransvecRow M).length = r
  proof: by simp [listTransvecRow]

中文:
定理 length_listTransvecRow
  结论: (listTransvecRow M).length = r
  证明: by simp [listTransvecRow]

Depends on / 依赖: listTransvecRow
-/
theorem length_listTransvecRow : (listTransvecRow M).length = r := by simp [listTransvecRow]

/--
theorem `listTransvecRow_getElem` / 定理 `listTransvecRow_getElem`

English:
theorem listTransvecRow_getElem
  given: {i : Nat} (h : i < (listTransvecRow M).length)
  proof: ⟨i, length_listTransvecRow M ▸ h⟩
transvection (inr unit) (inl i') -M (inr unit) (inl i') / M (inr unit) (inr unit) := by
  simp [listTransvecRow]

中文:
定理 listTransvecRow_getElem
  条件: {i : 自然数} (h : i < (listTransvecRow M).length)
  证明: ⟨i, length_listTransvecRow M ▸ h⟩
transvection (inr unit) (inl i') -M (inr unit) (inl i') / M (inr unit) (inr unit) := by
  simp [listTransvecRow]

Depends on / 依赖: length_listTransvecRow
-/
theorem listTransvecRow_getElem {i : Nat} (h : i < (listTransvecRow M).length) :
    (listTransvecRow M)[i] =
      letI i' : Fin r := ⟨i, length_listTransvecRow M ▸ h⟩
transvection (inr unit) (inl i') -M (inr unit) (inl i') / M (inr unit) (inr unit) := by
  simp [listTransvecRow]

/--
theorem `listTransvecCol_mul_last_row_drop` / 定理 `listTransvecCol_mul_last_row_drop`

English:
theorem listTransvecCol_mul_last_row_drop
  given: (i : Fin r oplus Unit) {k : Nat} (hk : k <= r)
  proof: by
  induction hk using Nat.decreasingInduction with
  | of_succ n hn IH =>
    have hn' : n < (listTransvecCol M).length := by simpa [listTransvecCol] using hn
    rw [List.drop_eq_getElem_cons hn']
    simpa [listTransvecCol, Matrix.mul_assoc]
  | self =>
    simp only [length_listTransvecCol, le_

中文:
定理 listTransvecCol_mul_last_row_drop
  条件: (i : 有限集 r oplus 单元) {k : 自然数} (hk : k <= r)
  证明: by
  induction hk using Nat.decreasingInduction with
  | of_succ n hn IH =>
    have hn' : n < (listTransvecCol M).length := by simpa [listTransvecCol] using hn
    rw [List.drop_eq_getElem_cons hn']
    simpa [listTransvecCol, Matrix.mul_assoc]
  | self =>
    simp only [length_listTransvecCol, le_

Depends on / 依赖: List.drop_eq_getElem_cons, List.drop_eq_nil_of_le, List.prod_nil, Matrix, Matrix.mul_assoc, Matrix.one_mul, Nat.decreasingInduction, decreasingInduction, drop_eq_getElem_cons, drop_eq_nil_of_le, le_refl, length, length_listTransvecCol, listTransvecCol, mul_assoc, of_succ, one_mul, prod_nil
-/
theorem listTransvecCol_mul_last_row_drop (i : Fin r oplus Unit) {k : Nat} (hk : k <= r) :
    (((listTransvecCol M).drop k).prod * M) (inr unit) i = M (inr unit) i := by
  induction hk using Nat.decreasingInduction with
  | of_succ n hn IH =>
    have hn' : n < (listTransvecCol M).length := by simpa [listTransvecCol] using hn
    rw [List.drop_eq_getElem_cons hn']
    simpa [listTransvecCol, Matrix.mul_assoc]
  | self =>
    simp only [length_listTransvecCol, le_refl, List.drop_eq_nil_of_le, List.prod_nil,
      Matrix.one_mul]

/--
theorem `listTransvecCol_mul_last_row` / 定理 `listTransvecCol_mul_last_row`

English:
theorem listTransvecCol_mul_last_row
  given: (i : Fin r oplus Unit)
  proof: by
  simpa using listTransvecCol_mul_last_row_drop M i zero_le

中文:
定理 listTransvecCol_mul_last_row
  条件: (i : 有限集 r oplus 单元)
  证明: by
  simpa using listTransvecCol_mul_last_row_drop M i zero_le

Depends on / 依赖: listTransvecCol_mul_last_row_drop, zero_le
-/
theorem listTransvecCol_mul_last_row (i : Fin r oplus Unit) :
    ((listTransvecCol M).prod * M) (inr unit) i = M (inr unit) i := by
  simpa using listTransvecCol_mul_last_row_drop M i zero_le

/--
theorem `listTransvecCol_mul_last_col` / 定理 `listTransvecCol_mul_last_col`

English:
theorem listTransvecCol_mul_last_col
  given: (hM : M (inr unit) (inr unit) != 0) (i : Fin r)
  proof: by
  suffices H :
    forall k : Nat,
      k <= r ->
        (((listTransvecCol M).drop k).prod * M) (inl i) (inr unit) =
          if k <= i then 0 else M (inl i) (inr unit) by
    simpa [List.drop] using H 0
  intro k hk
  induction hk using Nat.decreasingInduction with
  | of_succ n hn IH =>
   

中文:
定理 listTransvecCol_mul_last_col
  条件: (hM : M (inr unit) (inr unit) != 0) (i : 有限集 r)
  证明: by
  suffices H :
    forall k : Nat,
      k <= r ->
        (((listTransvecCol M).drop k).prod * M) (inl i) (inr unit) =
          if k <= i then 0 else M (inl i) (inr unit) by
    simpa [List.drop] using H 0
  intro k hk
  induction hk using Nat.decreasingInduction with
  | of_succ n hn IH =>
   

Depends on / 依赖: List.drop, List.drop_eq_getElem_cons, Nat.decreasingInduction, decreasingInduction, drop_eq_getElem_cons, length, listTransvecCol, of_succ, transvection
-/
theorem listTransvecCol_mul_last_col (hM : M (inr unit) (inr unit) != 0) (i : Fin r) :
    ((listTransvecCol M).prod * M) (inl i) (inr unit) = 0 := by
  suffices H :
    forall k : Nat,
      k <= r ->
        (((listTransvecCol M).drop k).prod * M) (inl i) (inr unit) =
          if k <= i then 0 else M (inl i) (inr unit) by
    simpa [List.drop] using H 0
  intro k hk
  induction hk using Nat.decreasingInduction with
  | of_succ n hn IH =>
    have hn' : n < (listTransvecCol M).length := by simpa [listTransvecCol] using hn
    let n' : Fin r := ⟨n, hn⟩
    rw [List.drop_eq_getElem_cons hn']
    have A :
      (listTransvecCol M)[n] =
        transvection (inl n') (inr unit) (-M (inl n') (inr unit) / M (inr unit) (inr unit)) := by
      simp [n', listTransvecCol]
    simp only [Matrix.mul_assoc, A, List.prod_cons]
    by_cases h : n' = i
    · have hni : n = i := by
        cases i
        simp only [n', Fin.mk_eq_mk] at h
        simp [h]
      simp only [h, transvection_mul_apply_same, IH, ← hni, add_le_iff_nonpos_right,
          listTransvecCol_mul_last_row_drop _ _ hn]
      simp [field]
    · have hni : n != i := by
        rintro rfl
        cases i
        simp [n'] at h
      simp only [ne_eq, inl.injEq, Ne.symm h, not_false_eq_true, transvection_mul_apply_of_ne]
      rw [IH]
      rcases le_or_gt (n + 1) i with (hi | hi)
      · simp only [hi, n.le_succ.trans hi, if_true]
      · rw [if_neg, if_neg]
        · simpa only [hni.symm, not_le, or_false] using Nat.lt_succ_iff_lt_or_eq.1 hi
        · simpa only [not_le] using hi
  | self =>
    simp only [length_listTransvecCol, le_refl, List.drop_eq_nil_of_le, List.prod_nil,
      Matrix.one_mul]
    rw [if_neg]
    simpa only [not_le] using i.2

/--
theorem `mul_listTransvecRow_last_col_take` / 定理 `mul_listTransvecRow_last_col_take`

English:
theorem mul_listTransvecRow_last_col_take
  given: (i : Fin r oplus Unit) {k : Nat} (hk : k <= r)
  proof: by
  induction k with
  | zero => simp only [Matrix.mul_one, List.prod_nil, List.take, Matrix.mul_one]
  | succ k IH =>
    have hkr : k < r := hk
    let k' : Fin r := ⟨k, hkr⟩
    have :
      (listTransvecRow M)[k]? =
        ↑(transvection (inr Unit.unit) (inl k')
            (-M (inr Unit.unit)

中文:
定理 mul_listTransvecRow_last_col_take
  条件: (i : 有限集 r oplus 单元) {k : 自然数} (hk : k <= r)
  证明: by
  induction k with
  | zero => simp only [Matrix.mul_one, List.prod_nil, List.take, Matrix.mul_one]
  | succ k IH =>
    have hkr : k < r := hk
    let k' : Fin r := ⟨k, hkr⟩
    have :
      (listTransvecRow M)[k]? =
        ↑(transvection (inr Unit.unit) (inl k')
            (-M (inr Unit.unit)

Depends on / 依赖: List.getElem, List.prod_append, List.prod_cons, List.prod_nil, List.take, List.take_add_one, Matrix, Matrix.mul_assoc, Matrix.mul_one, Unit.unit, _ofFn, dif_pos, getElem, listTransvecRow, mul_assoc, mul_one, prod_append, prod_cons, prod_nil, take_add_one
-/
theorem mul_listTransvecRow_last_col_take (i : Fin r oplus Unit) {k : Nat} (hk : k <= r) :
    (M * ((listTransvecRow M).take k).prod) i (inr unit) = M i (inr unit) := by
  induction k with
  | zero => simp only [Matrix.mul_one, List.prod_nil, List.take, Matrix.mul_one]
  | succ k IH =>
    have hkr : k < r := hk
    let k' : Fin r := ⟨k, hkr⟩
    have :
      (listTransvecRow M)[k]? =
        ↑(transvection (inr Unit.unit) (inl k')
            (-M (inr Unit.unit) (inl k') / M (inr Unit.unit) (inr Unit.unit))) := by
      simp only [k', listTransvecRow, hkr, dif_pos, List.getElem?_ofFn]
    simp only [List.take_add_one, ← Matrix.mul_assoc, this, List.prod_append, Matrix.mul_one,
      List.prod_cons, List.prod_nil, Option.toList_some]
    rw [mul_transvection_apply_of_ne]; rw [IH hkr.le]
    simp only [Ne, not_false_iff, reduceCtorEq]

/--
theorem `mul_listTransvecRow_last_col` / 定理 `mul_listTransvecRow_last_col`

English:
theorem mul_listTransvecRow_last_col
  given: (i : Fin r oplus Unit)
  proof: by
  have A : (listTransvecRow M).length = r := by simp [listTransvecRow]
  rw [← List.take_length (l := listTransvecRow M)]; rw [A]
  simpa using mul_listTransvecRow_last_col_take M i le_rfl

中文:
定理 mul_listTransvecRow_last_col
  条件: (i : 有限集 r oplus 单元)
  证明: by
  have A : (listTransvecRow M).length = r := by simp [listTransvecRow]
  rw [← List.take_length (l := listTransvecRow M)]; rw [A]
  simpa using mul_listTransvecRow_last_col_take M i le_rfl

Depends on / 依赖: List.take_length, le_rfl, length, listTransvecRow, mul_listTransvecRow_last_col_take, take_length
-/
theorem mul_listTransvecRow_last_col (i : Fin r oplus Unit) :
    (M * (listTransvecRow M).prod) i (inr unit) = M i (inr unit) := by
  have A : (listTransvecRow M).length = r := by simp [listTransvecRow]
  rw [← List.take_length (l := listTransvecRow M)]; rw [A]
  simpa using mul_listTransvecRow_last_col_take M i le_rfl

/--
theorem `mul_listTransvecRow_last_row` / 定理 `mul_listTransvecRow_last_row`

English:
theorem mul_listTransvecRow_last_row
  given: (hM : M (inr unit) (inr unit) != 0) (i : Fin r)
  proof: by
  suffices H :
    forall k : Nat,
      k <= r ->
        (M * ((listTransvecRow M).take k).prod) (inr unit) (inl i) =
          if k <= i then M (inr unit) (inl i) else 0 by
    have A : (listTransvecRow M).length = r := by simp [listTransvecRow]
    rw [← List.take_length (l := listTransvecRow

中文:
定理 mul_listTransvecRow_last_row
  条件: (hM : M (inr unit) (inr unit) != 0) (i : 有限集 r)
  证明: by
  suffices H :
    forall k : Nat,
      k <= r ->
        (M * ((listTransvecRow M).take k).prod) (inr unit) (inl i) =
          if k <= i then M (inr unit) (inl i) else 0 by
    have A : (listTransvecRow M).length = r := by simp [listTransvecRow]
    rw [← List.take_length (l := listTransvecRow

Depends on / 依赖: List.take_length, ite_eq_right_iff, le_rfl, length, listTransvecRow, take_length
-/
theorem mul_listTransvecRow_last_row (hM : M (inr unit) (inr unit) != 0) (i : Fin r) :
    (M * (listTransvecRow M).prod) (inr unit) (inl i) = 0 := by
  suffices H :
    forall k : Nat,
      k <= r ->
        (M * ((listTransvecRow M).take k).prod) (inr unit) (inl i) =
          if k <= i then M (inr unit) (inl i) else 0 by
    have A : (listTransvecRow M).length = r := by simp [listTransvecRow]
    rw [← List.take_length (l := listTransvecRow M)]; rw [A]
    have : ¬r <= i := by simp
    simpa only [this, ite_eq_right_iff] using! H r le_rfl
  intro k hk
  induction k with
  | zero => simp
  | succ n IH =>
    have hnr : n < r := hk
    let n' : Fin r := ⟨n, hnr⟩
    have A :
      (listTransvecRow M)[n]? =
        ↑(transvection (inr unit) (inl n')
        (-M (inr unit) (inl n') / M (inr unit) (inr unit))) := by
      simp only [n', listTransvecRow, hnr, dif_pos, List.getElem?_ofFn]
    simp only [List.take_add_one, A, ← Matrix.mul_assoc, List.prod_append, Matrix.mul_one,
      List.prod_cons, List.prod_nil, Option.toList_some]
    by_cases h : n' = i
    · have hni : n = i := by
        cases i
        simp only [n', Fin.mk_eq_mk] at h
        simp only [h]
      have : ¬n.succ <= i := by simp only [← hni, n.lt_succ_self, not_le]
      simp only [h, mul_transvection_apply_same, if_false,
        mul_listTransvecRow_last_col_take _ _ hnr.le, hni.le, this, if_true, IH hnr.le]
      field
    · have hni : n != i := by
        rintro rfl
        cases i
        tauto
      simp only [IH hnr.le, Ne, mul_transvection_apply_of_ne, Ne.symm h, inl.injEq,
        not_false_eq_true]
      rcases le_or_gt (n + 1) i with (hi | hi)
      · simp [hi, n.le_succ.trans hi]
      · rw [if_neg, if_neg]
        · simpa only [not_le] using! hi
        · simpa only [hni.symm, not_le, or_false] using! Nat.lt_succ_iff_lt_or_eq.1 hi

/--
theorem `listTransvecCol_mul_mul_listTransvecRow_last_col` / 定理 `listTransvecCol_mul_mul_listTransvecRow_last_col`

English:
theorem listTransvecCol_mul_mul_listTransvecRow_last_col
  statement: (hM : M (inr unit) (inr unit) != 0)
  proof: by
  have : listTransvecRow M = listTransvecRow ((listTransvecCol M).prod * M) := by
    simp [listTransvecRow, listTransvecCol_mul_last_row]
  rw [this]
  apply mul_listTransvecRow_last_row
  simpa [listTransvecCol_mul_last_row] using hM

中文:
定理 listTransvecCol_mul_mul_listTransvecRow_last_col
  结论: (hM : M (inr unit) (inr unit) != 0)
  证明: by
  have : listTransvecRow M = listTransvecRow ((listTransvecCol M).prod * M) := by
    simp [listTransvecRow, listTransvecCol_mul_last_row]
  rw [this]
  apply mul_listTransvecRow_last_row
  simpa [listTransvecCol_mul_last_row] using hM

Depends on / 依赖: listTransvecCol, listTransvecCol_mul_last_row, listTransvecRow, mul_listTransvecRow_last_row
-/
theorem listTransvecCol_mul_mul_listTransvecRow_last_col (hM : M (inr unit) (inr unit) != 0)
    (i : Fin r) :
    ((listTransvecCol M).prod * M * (listTransvecRow M).prod) (inr unit) (inl i) = 0 := by
  have : listTransvecRow M = listTransvecRow ((listTransvecCol M).prod * M) := by
    simp [listTransvecRow, listTransvecCol_mul_last_row]
  rw [this]
  apply mul_listTransvecRow_last_row
  simpa [listTransvecCol_mul_last_row] using hM

/--
theorem `listTransvecCol_mul_mul_listTransvecRow_last_row` / 定理 `listTransvecCol_mul_mul_listTransvecRow_last_row`

English:
theorem listTransvecCol_mul_mul_listTransvecRow_last_row
  statement: (hM : M (inr unit) (inr unit) != 0)
  proof: by
  have : listTransvecCol M = listTransvecCol (M * (listTransvecRow M).prod) := by
    simp [listTransvecCol, mul_listTransvecRow_last_col]
  rw [this]; rw [Matrix.mul_assoc]
  apply listTransvecCol_mul_last_col
  simpa [mul_listTransvecRow_last_col] using hM

中文:
定理 listTransvecCol_mul_mul_listTransvecRow_last_row
  结论: (hM : M (inr unit) (inr unit) != 0)
  证明: by
  have : listTransvecCol M = listTransvecCol (M * (listTransvecRow M).prod) := by
    simp [listTransvecCol, mul_listTransvecRow_last_col]
  rw [this]; rw [Matrix.mul_assoc]
  apply listTransvecCol_mul_last_col
  simpa [mul_listTransvecRow_last_col] using hM

Depends on / 依赖: Matrix, Matrix.mul_assoc, listTransvecCol, listTransvecCol_mul_last_col, listTransvecRow, mul_assoc, mul_listTransvecRow_last_col
-/
theorem listTransvecCol_mul_mul_listTransvecRow_last_row (hM : M (inr unit) (inr unit) != 0)
    (i : Fin r) :
    ((listTransvecCol M).prod * M * (listTransvecRow M).prod) (inl i) (inr unit) = 0 := by
  have : listTransvecCol M = listTransvecCol (M * (listTransvecRow M).prod) := by
    simp [listTransvecCol, mul_listTransvecRow_last_col]
  rw [this]; rw [Matrix.mul_assoc]
  apply listTransvecCol_mul_last_col
  simpa [mul_listTransvecRow_last_col] using hM

/--
theorem `isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow` / 定理 `isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow`

English:
theorem isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow
  proof: by
  constructor
  · ext i j
    have : j = unit := by simp only
    simp [toBlocks₁₂, this, listTransvecCol_mul_mul_listTransvecRow_last_row M hM]
  · ext i j
    have : i = unit := by simp only
    simp [toBlocks₂₁, this, listTransvecCol_mul_mul_listTransvecRow_last_col M hM]

中文:
定理 isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow
  证明: by
  constructor
  · ext i j
    have : j = unit := by simp only
    simp [toBlocks₁₂, this, listTransvecCol_mul_mul_listTransvecRow_last_row M hM]
  · ext i j
    have : i = unit := by simp only
    simp [toBlocks₂₁, this, listTransvecCol_mul_mul_listTransvecRow_last_col M hM]

Depends on / 依赖: listTransvecCol_mul_mul_listTransvecRow_last_col, listTransvecCol_mul_mul_listTransvecRow_last_row
-/
theorem isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow
    (hM : M (inr unit) (inr unit) != 0) :
    IsTwoBlockDiagonal ((listTransvecCol M).prod * M * (listTransvecRow M).prod) := by
  constructor
  · ext i j
    have : j = unit := by simp only
    simp [toBlocks₁₂, this, listTransvecCol_mul_mul_listTransvecRow_last_row M hM]
  · ext i j
    have : i = unit := by simp only
    simp [toBlocks₂₁, this, listTransvecCol_mul_mul_listTransvecRow_last_col M hM]

/--
theorem `exists_isTwoBlockDiagonal_of_ne_zero` / 定理 `exists_isTwoBlockDiagonal_of_ne_zero`

English:
theorem exists_isTwoBlockDiagonal_of_ne_zero
  given: (hM : M (inr unit) (inr unit) != 0)
  proof: by
  let L : List (TransvectionStruct (Fin r oplus Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inl i, inr unit, by simp, -M (inl i) (inr unit) / M (inr unit) (inr unit)⟩
  let L' : List (TransvectionStruct (Fin r oplus Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inr unit, inl i, by simp,

中文:
定理 存在_isTwoBlockDiagonal_of_ne_zero
  条件: (hM : M (inr unit) (inr unit) != 0)
  证明: by
  let L : List (TransvectionStruct (Fin r oplus Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inl i, inr unit, by simp, -M (inl i) (inr unit) / M (inr unit) (inr unit)⟩
  let L' : List (TransvectionStruct (Fin r oplus Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inr unit, inl i, by simp,

Depends on / 依赖: Function, Function.comp_def, L.map, List.ofFn, TransvectionStruct, comp_def, listTransvecCol, listTransvecRow, toMatrix
-/
theorem exists_isTwoBlockDiagonal_of_ne_zero (hM : M (inr unit) (inr unit) != 0) :
    exists L L' : List (TransvectionStruct (Fin r oplus Unit) 𝕜),
      IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (L'.map toMatrix).prod) := by
  let L : List (TransvectionStruct (Fin r oplus Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inl i, inr unit, by simp, -M (inl i) (inr unit) / M (inr unit) (inr unit)⟩
  let L' : List (TransvectionStruct (Fin r oplus Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inr unit, inl i, by simp, -M (inr unit) (inl i) / M (inr unit) (inr unit)⟩
  refine ⟨L, L', ?_⟩
  have A : L.map toMatrix = listTransvecCol M := by simp [L, listTransvecCol, Function.comp_def]
  have B : L'.map toMatrix = listTransvecRow M := by simp [L', listTransvecRow, Function.comp_def]
  rw [A]; rw [B]
  exact isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow M hM

/--
theorem `exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec` / 定理 `exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec`

English:
theorem exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec
  proof: by
  by_cases H : IsTwoBlockDiagonal M
  · refine ⟨List.nil, List.nil, by simpa using H⟩
  -- we have already proved this when the last coefficient is nonzero
  by_cases hM : M (inr unit) (inr unit) = 0; swap
  · exact exists_isTwoBlockDiagonal_of_ne_zero M hM
  -- when the last coefficient is zero 

中文:
定理 存在_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec
  证明: by
  by_cases H : IsTwoBlockDiagonal M
  · refine ⟨List.nil, List.nil, by simpa using H⟩
  -- we have already proved this when the last coefficient is nonzero
  by_cases hM : M (inr unit) (inr unit) = 0; swap
  · exact exists_isTwoBlockDiagonal_of_ne_zero M hM
  -- when the last coefficient is zero 

Depends on / 依赖: IsTwoBlockDiagonal, List.nil
-/
theorem exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec
    (M : Matrix (Fin r oplus Unit) (Fin r oplus Unit) 𝕜) :
    exists L L' : List (TransvectionStruct (Fin r oplus Unit) 𝕜),
      IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (L'.map toMatrix).prod) := by
  by_cases H : IsTwoBlockDiagonal M
  · refine ⟨List.nil, List.nil, by simpa using H⟩
  -- we have already proved this when the last coefficient is nonzero
  by_cases hM : M (inr unit) (inr unit) = 0; swap
  · exact exists_isTwoBlockDiagonal_of_ne_zero M hM
  -- when the last coefficient is zero but there is a nonzero coefficient on the last row or the
  -- last column, we will first put this nonzero coefficient in last position, and then argue as
  -- above.
  simp only [not_and_or, IsTwoBlockDiagonal, toBlocks₁₂, toBlocks₂₁, ← Matrix.ext_iff] at H
  have : exists i : Fin r, M (inl i) (inr unit) != 0 ∨ M (inr unit) (inl i) != 0 := by
    rcases H with H | H
    · contrapose! H
      rintro i ⟨⟩
      exact (H i).1
    · contrapose! H
      rintro ⟨⟩ j
      exact (H j).2
  rcases this with ⟨i, h | h⟩
  · let M' := transvection (inr Unit.unit) (inl i) 1 * M
    have hM' : M' (inr unit) (inr unit) != 0 := by simpa [M', hM]
    rcases exists_isTwoBlockDiagonal_of_ne_zero M' hM' with ⟨L, L', hLL'⟩
    rw [Matrix.mul_assoc] at hLL'
    refine ⟨L ++ [⟨inr unit, inl i, by simp, 1⟩], L', ?_⟩
    simp only [List.map_append, List.prod_append, Matrix.mul_one, toMatrix_mk, List.prod_cons,
      List.prod_nil, List.map, Matrix.mul_assoc (L.map toMatrix).prod]
    exact hLL'
  · let M' := M * transvection (inl i) (inr unit) 1
    have hM' : M' (inr unit) (inr unit) != 0 := by simpa [M', hM]
    rcases exists_isTwoBlockDiagonal_of_ne_zero M' hM' with ⟨L, L', hLL'⟩
    refine ⟨L, ⟨inl i, inr unit, by simp, 1⟩::L', ?_⟩
    simp only [← Matrix.mul_assoc, toMatrix_mk, List.prod_cons, List.map]
    rw [Matrix.mul_assoc (L.map toMatrix).prod]
    exact hLL'

/--
theorem `exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction` / 定理 `exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction`

English:
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction
  proof: by
  rcases exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec M with ⟨L₁, L₁', hM⟩
  let M' := (L₁.map toMatrix).prod * M * (L₁'.map toMatrix).prod
  let M'' := toBlocks₁₁ M'
  rcases IH M'' with ⟨L₀, L₀', D₀, h₀⟩
  set c := M' (inr unit) (inr unit)
  refine
    ⟨L₀.map (sumInl Unit) ++ 

中文:
定理 存在_list_transvec_mul_mul_list_transvec_eq_diagonal_induction
  证明: by
  rcases exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec M with ⟨L₁, L₁', hM⟩
  let M' := (L₁.map toMatrix).prod * M * (L₁'.map toMatrix).prod
  let M'' := toBlocks₁₁ M'
  rcases IH M'' with ⟨L₀, L₀', D₀, h₀⟩
  set c := M' (inr unit) (inr unit)
  refine
    ⟨L₀.map (sumInl Unit) ++ 

Depends on / 依赖: Sum.elim, diagonal, exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec, sumInl, toMatrix
-/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction
    (IH :
      forall M : Matrix (Fin r) (Fin r) 𝕜,
        exists (L₀ L₀' : List (TransvectionStruct (Fin r) 𝕜)) (D₀ : Fin r -> 𝕜),
          (L₀.map toMatrix).prod * M * (L₀'.map toMatrix).prod = diagonal D₀)
    (M : Matrix (Fin r oplus Unit) (Fin r oplus Unit) 𝕜) :
    exists (L L' : List (TransvectionStruct (Fin r oplus Unit) 𝕜)) (D : Fin r oplus Unit -> 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  rcases exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec M with ⟨L₁, L₁', hM⟩
  let M' := (L₁.map toMatrix).prod * M * (L₁'.map toMatrix).prod
  let M'' := toBlocks₁₁ M'
  rcases IH M'' with ⟨L₀, L₀', D₀, h₀⟩
  set c := M' (inr unit) (inr unit)
  refine
    ⟨L₀.map (sumInl Unit) ++ L₁, L₁' ++ L₀'.map (sumInl Unit),
      Sum.elim D₀ fun _ => M' (inr unit) (inr unit), ?_⟩
  suffices (L₀.map (toMatrix ∘ sumInl Unit)).prod * M' * (L₀'.map (toMatrix ∘ sumInl Unit)).prod =
      diagonal (Sum.elim D₀ fun _ => c) by
    simpa [M', c, Matrix.mul_assoc]
  have : M' = fromBlocks M'' 0 0 (diagonal fun _ => c) := by
    rw [← fromBlocks_toBlocks M']; rw [hM.1]; rw [hM.2]
    rfl
  rw [this]
  simp [h₀]

variable {n p} [Fintype n] [Fintype p]

/--
theorem `reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal` / 定理 `reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal`

English:
theorem reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal
  statement: (M : Matrix p p 𝕜)
  proof: by
  rcases H with ⟨L₀, L₀', D₀, h₀⟩
  refine ⟨L₀.map (reindexEquiv e.symm), L₀'.map (reindexEquiv e.symm), D₀ ∘ e, ?_⟩
  have : M = reindexAlgEquiv 𝕜 _ e.symm (reindexAlgEquiv 𝕜 _ e M) := by simp
  rw [this]
  simp_rw [List.map_map, toMatrix_reindexEquiv_prod, ← map_mul, h₀]
  simp

中文:
定理 reindex_存在_list_transvec_mul_mul_list_transvec_eq_diagonal
  结论: (M : 矩阵 p p 𝕜)
  证明: by
  rcases H with ⟨L₀, L₀', D₀, h₀⟩
  refine ⟨L₀.map (reindexEquiv e.symm), L₀'.map (reindexEquiv e.symm), D₀ ∘ e, ?_⟩
  have : M = reindexAlgEquiv 𝕜 _ e.symm (reindexAlgEquiv 𝕜 _ e M) := by simp
  rw [this]
  simp_rw [List.map_map, toMatrix_reindexEquiv_prod, ← map_mul, h₀]
  simp

Depends on / 依赖: List.map_map, e.symm, map_map, map_mul, reindexAlgEquiv, reindexEquiv, simp_rw, toMatrix_reindexEquiv_prod
-/
theorem reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M : Matrix p p 𝕜)
    (e : p ≃ n)
    (H :
      exists (L L' : List (TransvectionStruct n 𝕜)) (D : n -> 𝕜),
        (L.map toMatrix).prod * Matrix.reindexAlgEquiv 𝕜 _ e M * (L'.map toMatrix).prod =
          diagonal D) :
    exists (L L' : List (TransvectionStruct p 𝕜)) (D : p -> 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  rcases H with ⟨L₀, L₀', D₀, h₀⟩
  refine ⟨L₀.map (reindexEquiv e.symm), L₀'.map (reindexEquiv e.symm), D₀ ∘ e, ?_⟩
  have : M = reindexAlgEquiv 𝕜 _ e.symm (reindexAlgEquiv 𝕜 _ e M) := by simp
  rw [this]
  simp_rw [List.map_map, toMatrix_reindexEquiv_prod, ← map_mul, h₀]
  simp

/--
theorem `exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux` / 定理 `exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux`

English:
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux
  statement: (n : Type) [Fintype n]
  proof: by
  suffices forall cn, Fintype.card n = cn ->
      exists (L L' : List (TransvectionStruct n 𝕜)) (D : n -> 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D by exact this _ rfl
  intro cn hn
  induction cn generalizing n M with
  | zero =>
    refine ⟨List.nil, List.nil, f

中文:
定理 存在_list_transvec_mul_mul_list_transvec_eq_diagonal_aux
  结论: (n : 类型) [有限类型 n]
  证明: by
  suffices forall cn, Fintype.card n = cn ->
      exists (L L' : List (TransvectionStruct n 𝕜)) (D : n -> 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D by exact this _ rfl
  intro cn hn
  induction cn generalizing n M with
  | zero =>
    refine ⟨List.nil, List.nil, f

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_eq_zero_iff, Fintype.card_sum, Fintype.equivOfCardEq, L.map, List.nil, TransvectionStruct, card_eq_zero_iff, card_sum, diagonal, equivOfCardEq, generalizing, hn.elim, reinde, toMatrix
-/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux (n : Type) [Fintype n]
    [DecidableEq n] (M : Matrix n n 𝕜) :
    exists (L L' : List (TransvectionStruct n 𝕜)) (D : n -> 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  suffices forall cn, Fintype.card n = cn ->
      exists (L L' : List (TransvectionStruct n 𝕜)) (D : n -> 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D by exact this _ rfl
  intro cn hn
  induction cn generalizing n M with
  | zero =>
    refine ⟨List.nil, List.nil, fun _ => 1, ?_⟩
    ext i j
    rw [Fintype.card_eq_zero_iff] at hn
    exact hn.elim' i
  | succ r IH =>
    have e : n ≃ Fin r oplus Unit := by
      refine Fintype.equivOfCardEq ?_
      rw [hn]
      rw [@Fintype.card_sum (Fin r) Unit _ _]
      simp
    apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e
    apply
      exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction fun N =>
        IH (Fin r) N (by simp)

/--
theorem `exists_list_transvec_mul_mul_list_transvec_eq_diagonal` / 定理 `exists_list_transvec_mul_mul_list_transvec_eq_diagonal`

English:
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal
  given: (M : Matrix n n 𝕜)
  proof: by
  have e : n ≃ Fin (Fintype.card n) := Fintype.equivOfCardEq (by simp)
  apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e
  apply exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux

中文:
定理 存在_list_transvec_mul_mul_list_transvec_eq_diagonal
  条件: (M : 矩阵 n n 𝕜)
  证明: by
  have e : n ≃ Fin (Fintype.card n) := Fintype.equivOfCardEq (by simp)
  apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e
  apply exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux

Depends on / 依赖: Fintype, Fintype.card, Fintype.equivOfCardEq, equivOfCardEq, exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux, reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal
-/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M : Matrix n n 𝕜) :
    exists (L L' : List (TransvectionStruct n 𝕜)) (D : n -> 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  have e : n ≃ Fin (Fintype.card n) := Fintype.equivOfCardEq (by simp)
  apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e
  apply exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux

/--
theorem `exists_list_transvec_mul_diagonal_mul_list_transvec` / 定理 `exists_list_transvec_mul_diagonal_mul_list_transvec`

English:
theorem exists_list_transvec_mul_diagonal_mul_list_transvec
  given: (M : Matrix n n 𝕜)
  proof: by
  rcases exists_list_transvec_mul_mul_list_transvec_eq_diagonal M with ⟨L, L', D, h⟩
  refine ⟨L.reverse.map TransvectionStruct.inv, L'.reverse.map TransvectionStruct.inv, D, ?_⟩
  suffices
    M =
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod * M *
      

中文:
定理 存在_list_transvec_mul_diagonal_mul_list_transvec
  条件: (M : 矩阵 n n 𝕜)
  证明: by
  rcases exists_list_transvec_mul_mul_list_transvec_eq_diagonal M with ⟨L, L', D, h⟩
  refine ⟨L.reverse.map TransvectionStruct.inv, L'.reverse.map TransvectionStruct.inv, D, ?_⟩
  suffices
    M =
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod * M *
      

Depends on / 依赖: L.map, L.reverse.map, Matrix, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul, TransvectionStruct, TransvectionStruct.inv, exists_list_transvec_mul_mul_list_transvec_eq_diagonal, mul_assoc, mul_one, one_mul, prod_mul_reverse_inv_prod, reverse, reverse.map, reverse_inv_prod_mul_prod, toMatrix
-/
theorem exists_list_transvec_mul_diagonal_mul_list_transvec (M : Matrix n n 𝕜) :
    exists (L L' : List (TransvectionStruct n 𝕜)) (D : n -> 𝕜),
      M = (L.map toMatrix).prod * diagonal D * (L'.map toMatrix).prod := by
  rcases exists_list_transvec_mul_mul_list_transvec_eq_diagonal M with ⟨L, L', D, h⟩
  refine ⟨L.reverse.map TransvectionStruct.inv, L'.reverse.map TransvectionStruct.inv, D, ?_⟩
  suffices
    M =
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod * M *
        ((L'.map toMatrix).prod * (L'.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod)
    by simpa [← h, Matrix.mul_assoc]
  rw [reverse_inv_prod_mul_prod]; rw [prod_mul_reverse_inv_prod]; rw [Matrix.one_mul]; rw [Matrix.mul_one]

end Pivot

open Pivot TransvectionStruct

variable {n} [Fintype n]

/--
theorem `diagonal_transvection_induction` / 定理 `diagonal_transvection_induction`

English:
theorem diagonal_transvection_induction
  statement: (P : Matrix n n 𝕜 -> Prop) (M : Matrix n n 𝕜)
  proof: by
  rcases exists_list_transvec_mul_diagonal_mul_list_transvec M with ⟨L, L', D, h⟩
  have PD : P (diagonal D) := hdiag D (by simp [h])
  suffices H :
    forall (L₁ L₂ : List (TransvectionStruct n 𝕜)) (E : Matrix n n 𝕜),
      P E -> P ((L₁.map toMatrix).prod * E * (L₂.map toMatrix).prod) by
    r

中文:
定理 diagonal_transvection_induction
  结论: (P : 矩阵 n n 𝕜 -> 命题) (M : 矩阵 n n 𝕜)
  证明: by
  rcases exists_list_transvec_mul_diagonal_mul_list_transvec M with ⟨L, L', D, h⟩
  have PD : P (diagonal D) := hdiag D (by simp [h])
  suffices H :
    forall (L₁ L₂ : List (TransvectionStruct n 𝕜)) (E : Matrix n n 𝕜),
      P E -> P ((L₁.map toMatrix).prod * E * (L₂.map toMatrix).prod) by
    r

Depends on / 依赖: List.map, List.prod_nil, Matrix, Matrix.mul_assoc, Matrix.one_mul, TransvectionStruct, diagonal, exists_list_transvec_mul_diagonal_mul_list_transvec, generalizing, mul_assoc, one_mul, prod_nil, toMatrix
-/
theorem diagonal_transvection_induction (P : Matrix n n 𝕜 -> Prop) (M : Matrix n n 𝕜)
    (hdiag : forall D : n -> 𝕜, det (diagonal D) = det M -> P (diagonal D))
    (htransvec : forall t : TransvectionStruct n 𝕜, P t.toMatrix) (hmul : forall A B, P A -> P B -> P (A * B)) :
    P M := by
  rcases exists_list_transvec_mul_diagonal_mul_list_transvec M with ⟨L, L', D, h⟩
  have PD : P (diagonal D) := hdiag D (by simp [h])
  suffices H :
    forall (L₁ L₂ : List (TransvectionStruct n 𝕜)) (E : Matrix n n 𝕜),
      P E -> P ((L₁.map toMatrix).prod * E * (L₂.map toMatrix).prod) by
    rw [h]
    apply H L L'
    exact PD
  intro L₁ L₂ E PE
  induction L₁ with
  | nil =>
    simp only [Matrix.one_mul, List.prod_nil, List.map]
    induction L₂ generalizing E with
    | nil => simpa
    | cons t L₂ IH =>
      simp only [← Matrix.mul_assoc, List.prod_cons, List.map]
      apply IH
      exact hmul _ _ PE (htransvec _)
  | cons t L₁ IH =>
    simp only [Matrix.mul_assoc, List.prod_cons, List.map] at IH ⊢
    exact hmul _ _ (htransvec _) IH

/--
theorem `diagonal_transvection_induction_of_det_ne_zero` / 定理 `diagonal_transvection_induction_of_det_ne_zero`

English:
theorem diagonal_transvection_induction_of_det_ne_zero
  statement: (P : Matrix n n 𝕜 -> Prop) (M : Matrix n n 𝕜)
  proof: by
  let Q : Matrix n n 𝕜 -> Prop := fun N => det N != 0 ∧ P N
  have : Q M := by
    apply diagonal_transvection_induction Q M
    · grind
    · intro t
      exact ⟨by simp, htransvec t⟩
    · intro A B QA QB
      exact ⟨by simp [QA.1, QB.1], hmul A B QA.1 QB.1 QA.2 QB.2⟩
  exact this.2

中文:
定理 diagonal_transvection_induction_of_det_ne_zero
  结论: (P : 矩阵 n n 𝕜 -> 命题) (M : 矩阵 n n 𝕜)
  证明: by
  let Q : Matrix n n 𝕜 -> Prop := fun N => det N != 0 ∧ P N
  have : Q M := by
    apply diagonal_transvection_induction Q M
    · grind
    · intro t
      exact ⟨by simp, htransvec t⟩
    · intro A B QA QB
      exact ⟨by simp [QA.1, QB.1], hmul A B QA.1 QB.1 QA.2 QB.2⟩
  exact this.2

Depends on / 依赖: Matrix, diagonal_transvection_induction, htransvec
-/
theorem diagonal_transvection_induction_of_det_ne_zero (P : Matrix n n 𝕜 -> Prop) (M : Matrix n n 𝕜)
    (hMdet : det M != 0) (hdiag : forall D : n -> 𝕜, det (diagonal D) != 0 -> P (diagonal D))
    (htransvec : forall t : TransvectionStruct n 𝕜, P t.toMatrix)
    (hmul : forall A B, det A != 0 -> det B != 0 -> P A -> P B -> P (A * B)) : P M := by
  let Q : Matrix n n 𝕜 -> Prop := fun N => det N != 0 ∧ P N
  have : Q M := by
    apply diagonal_transvection_induction Q M
    · grind
    · intro t
      exact ⟨by simp, htransvec t⟩
    · intro A B QA QB
      exact ⟨by simp [QA.1, QB.1], hmul A B QA.1 QB.1 QA.2 QB.2⟩
  exact this.2

end Matrix
