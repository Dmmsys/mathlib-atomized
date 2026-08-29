/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Eric Wieser, Jeremy Avigad, Johan Commelin
-/
module

public import Mathlib.LinearAlgebra.Matrix.Invertible
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # 2×2 block matrices and the Schur complement

This file proves properties of 2×2 block matrices `[A B; C D]` that relate to the Schur complement
`D - C*A⁻¹*B`.

Some of the results here generalize to 2×2 matrices in a category, rather than just a ring. A few
results in this direction can be found in `Mathlib/CategoryTheory/Preadditive/Biproducts.lean`,
especially the declarations `CategoryTheory.Biprod.gaussian` and `CategoryTheory.Biprod.isoElim`.
Compare with `Matrix.invertibleOfFromBlocks₁₁Invertible`.

## Main results

* `Matrix.det_fromBlocks₁₁`, `Matrix.det_fromBlocks₂₂`: determinant of a block matrix in terms of
  the Schur complement.
* `Matrix.invOf_fromBlocks_zero₂₁_eq`, `Matrix.invOf_fromBlocks_zero₁₂_eq`: the inverse of a
  block triangular matrix.
* `Matrix.isUnit_fromBlocks_zero₂₁`, `Matrix.isUnit_fromBlocks_zero₁₂`: invertibility of a
  block triangular matrix.
* `Matrix.det_one_add_mul_comm`: the **Weinstein–Aronszajn identity**.

-/

@[expose] public section


variable {l m n α : Type*}

namespace Matrix

open scoped Matrix

section CommRing

variable [Fintype l] [Fintype m] [Fintype n]
variable [DecidableEq l] [DecidableEq m] [DecidableEq n]
variable [CommRing α]

/--
theorem `fromBlocks_eq_of_invertible₁₁` / 定理 `fromBlocks_eq_of_invertible₁₁`

English:
theorem fromBlocks_eq_of_invertible₁₁
  statement: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix l m α)
  proof: by
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one, invOf_mul_self, Matrix.mul_invOf_cancel_left,
    Matrix.mul_assoc, add_sub_cancel]

中文:
定理 fromBlocks_eq_of_invertible₁₁
  结论: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix l m α)
  证明: by
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one, invOf_mul_self, Matrix.mul_invOf_cancel_left,
    Matrix.mul_assoc, add_sub_cancel]

Depends on / 依赖: Matrix, Matrix.mul_assoc, Matrix.mul_invOf_cancel_left, Matrix.mul_one, Matrix.mul_zero, Matrix.one_mul, Matrix.zero_mul, add_sub_cancel, add_zero, fromBlocks_multiply, invOf_mul_self, mul_assoc, mul_invOf_cancel_left, mul_one, mul_zero, one_mul, zero_add, zero_mul
-/
theorem fromBlocks_eq_of_invertible₁₁ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix l m α)
    (D : Matrix l n α) [Invertible A] :
    fromBlocks A B C D =
      fromBlocks 1 0 (C * ⅟A) 1 * fromBlocks A 0 0 (D - C * ⅟A * B) *
        fromBlocks 1 (⅟A * B) 0 1 := by
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one, invOf_mul_self, Matrix.mul_invOf_cancel_left,
    Matrix.mul_assoc, add_sub_cancel]

/--
theorem `fromBlocks_eq_of_invertible₂₂` / 定理 `fromBlocks_eq_of_invertible₂₂`

English:
theorem fromBlocks_eq_of_invertible₂₂
  statement: (A : Matrix l m α) (B : Matrix l n α) (C : Matrix n m α)
  proof: (Matrix.reindex (Equiv.sumComm _ _) (Equiv.sumComm _ _)).injective by
    simpa [reindex_apply, Equiv.sumComm_symm, ← submatrix_mul_equiv _ _ _ (Equiv.sumComm n m), ←
      submatrix_mul_equiv _ _ _ (Equiv.sumComm n l), Equiv.sumComm_apply,
      fromBlocks_submatrix_sum_swap_sum_swap] using fromBlo

中文:
定理 fromBlocks_eq_of_invertible₂₂
  结论: (A : Matrix l m α) (B : Matrix l n α) (C : Matrix n m α)
  证明: (Matrix.reindex (Equiv.sumComm _ _) (Equiv.sumComm _ _)).injective by
    simpa [reindex_apply, Equiv.sumComm_symm, ← submatrix_mul_equiv _ _ _ (Equiv.sumComm n m), ←
      submatrix_mul_equiv _ _ _ (Equiv.sumComm n l), Equiv.sumComm_apply,
      fromBlocks_submatrix_sum_swap_sum_swap] using fromBlo

Depends on / 依赖: Equiv.sumComm, Equiv.sumComm_apply, Equiv.sumComm_symm, Matrix, Matrix.reindex, fromBlocks_submatrix_sum_swap_sum_swap, injective, reindex, reindex_apply, submatrix_mul_equiv, sumComm, sumComm_apply, sumComm_symm
-/
theorem fromBlocks_eq_of_invertible₂₂ (A : Matrix l m α) (B : Matrix l n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] :
    fromBlocks A B C D =
      fromBlocks 1 (B * ⅟D) 0 1 * fromBlocks (A - B * ⅟D * C) 0 0 D *
        fromBlocks 1 0 (⅟D * C) 1 :=
(Matrix.reindex (Equiv.sumComm _ _) (Equiv.sumComm _ _)).injective by
    simpa [reindex_apply, Equiv.sumComm_symm, ← submatrix_mul_equiv _ _ _ (Equiv.sumComm n m), ←
      submatrix_mul_equiv _ _ _ (Equiv.sumComm n l), Equiv.sumComm_apply,
      fromBlocks_submatrix_sum_swap_sum_swap] using fromBlocks_eq_of_invertible₁₁ D C B A

section Triangular

/-! #### Block triangular matrices -/


/-- An upper-block-triangular matrix is invertible if its diagonal is. -/
@[instance_reducible]
/--
Definition of `fromBlocksZero₂₁Invertible` / `fromBlocksZero₂₁Invertible` 的定义

English:
definition fromBlocksZero₂₁Invertible
  signature: (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
  body: invertibleOfLeftInverse _ (fromBlocks (⅟A) (-(⅟A * B * ⅟D)) 0 (⅟D)) by
    simp_rw [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      Matrix.neg_mul, invOf_mul_self, Matrix.invOf_mul_cancel_right, add_neg_cancel,
      fromBlocks_one]

中文:
定义 fromBlocksZero₂₁Invertible
  签名: (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
  定义体: invertibleOfLeftInverse _ (fromBlocks (⅟A) (-(⅟A * B * ⅟D)) 0 (⅟D)) by
    simp_rw [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      Matrix.neg_mul, invOf_mul_self, Matrix.invOf_mul_cancel_right, add_neg_cancel,
      fromBlocks_one]

Depends on / 依赖: Matrix, Matrix.invOf_mul_cancel_right, Matrix.mul_zero, Matrix.neg_mul, Matrix.zero_mul, add_neg_cancel, add_zero, fromBlocks, fromBlocks_multiply, fromBlocks_one, invOf_mul_cancel_right, invOf_mul_self, invertibleOfLeftInverse, mul_zero, neg_mul, simp_rw, zero_add, zero_mul
-/
def fromBlocksZero₂₁Invertible (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
    [Invertible A] [Invertible D] : Invertible (fromBlocks A B 0 D) :=
invertibleOfLeftInverse _ (fromBlocks (⅟A) (-(⅟A * B * ⅟D)) 0 (⅟D)) by
    simp_rw [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      Matrix.neg_mul, invOf_mul_self, Matrix.invOf_mul_cancel_right, add_neg_cancel,
      fromBlocks_one]

/-- A lower-block-triangular matrix is invertible if its diagonal is. -/
@[instance_reducible]
/--
Definition of `fromBlocksZero₁₂Invertible` / `fromBlocksZero₁₂Invertible` 的定义

English:
definition fromBlocksZero₁₂Invertible
  signature: (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
  body: invertibleOfLeftInverse _
      (fromBlocks (⅟A) 0 (-(⅟D * C * ⅟A))
        (⅟D)) <| by -- a symmetry argument is more work than just copying the proof
    simp_rw [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      Matrix.neg_mul, invOf_mul_self, Matrix.invOf_mul_cance

中文:
定义 fromBlocksZero₁₂Invertible
  签名: (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
  定义体: invertibleOfLeftInverse _
      (fromBlocks (⅟A) 0 (-(⅟D * C * ⅟A))
        (⅟D)) <| by -- a symmetry argument is more work than just copying the proof
    simp_rw [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      Matrix.neg_mul, invOf_mul_self, Matrix.invOf_mul_cance

Depends on / 依赖: Matrix, Matrix.invOf_mul_cancel_right, Matrix.mul_zero, Matrix.neg_mul, Matrix.zero_mul, add_zero, argument, copying, fromBlocks, fromBlocks_multiply, fromBlocks_one, invOf_mul_cancel_right, invOf_mul_self, invertibleOfLeftInverse, mul_zero, neg_add_cancel, neg_mul, simp_rw, symmetry, zero_add
-/
def fromBlocksZero₁₂Invertible (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible A] [Invertible D] : Invertible (fromBlocks A 0 C D) :=
  invertibleOfLeftInverse _
      (fromBlocks (⅟A) 0 (-(⅟D * C * ⅟A))
        (⅟D)) <| by -- a symmetry argument is more work than just copying the proof
    simp_rw [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      Matrix.neg_mul, invOf_mul_self, Matrix.invOf_mul_cancel_right, neg_add_cancel,
      fromBlocks_one]

/--
theorem `invOf_fromBlocks_zero₂₁_eq` / 定理 `invOf_fromBlocks_zero₂₁_eq`

English:
theorem invOf_fromBlocks_zero₂₁_eq
  statement: (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
  proof: by
  let := fromBlocksZero₂₁Invertible A B D
  convert! (rfl : ⅟(fromBlocks A B 0 D) = _)

中文:
定理 invOf_fromBlocks_zero₂₁_eq
  结论: (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
  证明: by
  let := fromBlocksZero₂₁Invertible A B D
  convert! (rfl : ⅟(fromBlocks A B 0 D) = _)

Depends on / 依赖: convert, fromBlocks
-/
theorem invOf_fromBlocks_zero₂₁_eq (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
    [Invertible A] [Invertible D] [Invertible (fromBlocks A B 0 D)] :
    ⅟(fromBlocks A B 0 D) = fromBlocks (⅟A) (-(⅟A * B * ⅟D)) 0 (⅟D) := by
  let := fromBlocksZero₂₁Invertible A B D
  convert! (rfl : ⅟(fromBlocks A B 0 D) = _)

/--
theorem `invOf_fromBlocks_zero₁₂_eq` / 定理 `invOf_fromBlocks_zero₁₂_eq`

English:
theorem invOf_fromBlocks_zero₁₂_eq
  statement: (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
  proof: by
  let := fromBlocksZero₁₂Invertible A C D
  convert! (rfl : ⅟(fromBlocks A 0 C D) = _)

中文:
定理 invOf_fromBlocks_zero₁₂_eq
  结论: (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
  证明: by
  let := fromBlocksZero₁₂Invertible A C D
  convert! (rfl : ⅟(fromBlocks A 0 C D) = _)

Depends on / 依赖: convert, fromBlocks, x.prop.compl
-/
theorem invOf_fromBlocks_zero₁₂_eq (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible A] [Invertible D] [Invertible (fromBlocks A 0 C D)] :
    ⅟(fromBlocks A 0 C D) = fromBlocks (⅟A) 0 (-(⅟D * C * ⅟A)) (⅟D) := by
  let := fromBlocksZero₁₂Invertible A C D
  convert! (rfl : ⅟(fromBlocks A 0 C D) = _)

/--
Definition of `invertibleOfFromBlocksZero₂₁Invertible` / `invertibleOfFromBlocksZero₂₁Invertible` 的定义

English:
definition invertibleOfFromBlocksZero₂₁Invertible
  signature: (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
  body: invertibleOfLeftInverse _ (⅟(fromBlocks A B 0 D)).toBlocks₁₁ by
      have := invOf_mul_self (fromBlocks A B 0 D)
      rw [← fromBlocks_toBlocks (⅟(fromBlocks A B 0 D))]; rw [fromBlocks_multiply] at this
      simpa only [Matrix.toBlocks_fromBlocks₁₁, Matrix.mul_zero, add_zero, ← fromBlocks_one] us

中文:
定义 invertibleOfFromBlocksZero₂₁Invertible
  签名: (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
  定义体: invertibleOfLeftInverse _ (⅟(fromBlocks A B 0 D)).toBlocks₁₁ by
      have := invOf_mul_self (fromBlocks A B 0 D)
      rw [← fromBlocks_toBlocks (⅟(fromBlocks A B 0 D))]; rw [fromBlocks_multiply] at this
      simpa only [Matrix.toBlocks_fromBlocks₁₁, Matrix.mul_zero, add_zero, ← fromBlocks_one] us

Depends on / 依赖: Matrix, Matrix.mul_zero, Matrix.toBlocks, Matrix.toBlocks_fromBlocks, add_zero, congr_arg, fromBlock, fromBlocks, fromBlocks_multiply, fromBlocks_one, fromBlocks_toBlocks, invOf_mul_self, invertibleOfLeftInverse, invertibleOfRightInverse, mul_invOf_self, mul_zero
-/
def invertibleOfFromBlocksZero₂₁Invertible (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
    [Invertible (fromBlocks A B 0 D)] : Invertible A × Invertible D where
  fst :=
invertibleOfLeftInverse _ (⅟(fromBlocks A B 0 D)).toBlocks₁₁ by
      have := invOf_mul_self (fromBlocks A B 0 D)
      rw [← fromBlocks_toBlocks (⅟(fromBlocks A B 0 D))]; rw [fromBlocks_multiply] at this
      simpa only [Matrix.toBlocks_fromBlocks₁₁, Matrix.mul_zero, add_zero, ← fromBlocks_one] using
        congr_arg Matrix.toBlocks₁₁ this
  snd :=
invertibleOfRightInverse _ (⅟(fromBlocks A B 0 D)).toBlocks₂₂ by
      have := mul_invOf_self (fromBlocks A B 0 D)
      rw [← fromBlocks_toBlocks (⅟(fromBlocks A B 0 D))]; rw [fromBlocks_multiply] at this
      simpa only [Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, ← fromBlocks_one] using
        congr_arg Matrix.toBlocks₂₂ this

/--
Definition of `invertibleOfFromBlocksZero₁₂Invertible` / `invertibleOfFromBlocksZero₁₂Invertible` 的定义

English:
definition invertibleOfFromBlocksZero₁₂Invertible
  signature: (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
  body: invertibleOfRightInverse _ (⅟(fromBlocks A 0 C D)).toBlocks₁₁ by
      have := mul_invOf_self (fromBlocks A 0 C D)
      rw [← fromBlocks_toBlocks (⅟(fromBlocks A 0 C D))]; rw [fromBlocks_multiply] at this
      replace := congr_arg Matrix.toBlocks₁₁ this
      simpa only [Matrix.toBlocks_fromBlocks

中文:
定义 invertibleOfFromBlocksZero₁₂Invertible
  签名: (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
  定义体: invertibleOfRightInverse _ (⅟(fromBlocks A 0 C D)).toBlocks₁₁ by
      have := mul_invOf_self (fromBlocks A 0 C D)
      rw [← fromBlocks_toBlocks (⅟(fromBlocks A 0 C D))]; rw [fromBlocks_multiply] at this
      replace := congr_arg Matrix.toBlocks₁₁ this
      simpa only [Matrix.toBlocks_fromBlocks

Depends on / 依赖: Matrix, Matrix.toBlocks, Matrix.toBlocks_fromBlocks, Matrix.zero_mul, add_zero, congr_arg, fromBlocks, fromBlocks_multiply, fromBlocks_one, fromBlocks_toBlocks, invOf_mul_self, invertibleOfLeftInverse, invertibleOfRightInverse, mul_invOf_self, replace, zero_mul
-/
def invertibleOfFromBlocksZero₁₂Invertible (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible (fromBlocks A 0 C D)] : Invertible A × Invertible D where
  fst :=
invertibleOfRightInverse _ (⅟(fromBlocks A 0 C D)).toBlocks₁₁ by
      have := mul_invOf_self (fromBlocks A 0 C D)
      rw [← fromBlocks_toBlocks (⅟(fromBlocks A 0 C D))]; rw [fromBlocks_multiply] at this
      replace := congr_arg Matrix.toBlocks₁₁ this
      simpa only [Matrix.toBlocks_fromBlocks₁₁, Matrix.zero_mul, add_zero, ← fromBlocks_one] using
        this
  snd :=
invertibleOfLeftInverse _ (⅟(fromBlocks A 0 C D)).toBlocks₂₂ by
      have := invOf_mul_self (fromBlocks A 0 C D)
      rw [← fromBlocks_toBlocks (⅟(fromBlocks A 0 C D))]; rw [fromBlocks_multiply] at this
      replace := congr_arg Matrix.toBlocks₂₂ this
      simpa only [Matrix.toBlocks_fromBlocks₂₂, Matrix.mul_zero, zero_add, ← fromBlocks_one] using
        this

/--
Definition of `fromBlocksZero₂₁InvertibleEquiv` / `fromBlocksZero₂₁InvertibleEquiv` 的定义

English:
definition fromBlocksZero₂₁InvertibleEquiv
  signature: (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
  body: invertibleOfFromBlocksZero₂₁Invertible A B D
  invFun i := by
    letI := i.1
    letI := i.2
    exact fromBlocksZero₂₁Invertible A B D
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 fromBlocksZero₂₁InvertibleEquiv
  签名: (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
  定义体: invertibleOfFromBlocksZero₂₁Invertible A B D
  invFun i := by
    letI := i.1
    letI := i.2
    exact fromBlocksZero₂₁Invertible A B D
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
-/
def fromBlocksZero₂₁InvertibleEquiv (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α) :
    Invertible (fromBlocks A B 0 D) ≃ Invertible A × Invertible D where
  toFun _ := invertibleOfFromBlocksZero₂₁Invertible A B D
  invFun i := by
    letI := i.1
    letI := i.2
    exact fromBlocksZero₂₁Invertible A B D
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/--
Definition of `fromBlocksZero₁₂InvertibleEquiv` / `fromBlocksZero₁₂InvertibleEquiv` 的定义

English:
definition fromBlocksZero₁₂InvertibleEquiv
  signature: (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
  body: invertibleOfFromBlocksZero₁₂Invertible A C D
  invFun i := by
    letI := i.1
    letI := i.2
    exact fromBlocksZero₁₂Invertible A C D
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 fromBlocksZero₁₂InvertibleEquiv
  签名: (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
  定义体: invertibleOfFromBlocksZero₁₂Invertible A C D
  invFun i := by
    letI := i.1
    letI := i.2
    exact fromBlocksZero₁₂Invertible A C D
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
-/
def fromBlocksZero₁₂InvertibleEquiv (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α) :
    Invertible (fromBlocks A 0 C D) ≃ Invertible A × Invertible D where
  toFun _ := invertibleOfFromBlocksZero₁₂Invertible A C D
  invFun i := by
    letI := i.1
    letI := i.2
    exact fromBlocksZero₁₂Invertible A C D
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- An upper block-triangular matrix is invertible iff both elements of its diagonal are.

This is a propositional form of `Matrix.fromBlocksZero₂₁InvertibleEquiv`. -/
@[simp]
/--
theorem `isUnit_fromBlocks_zero₂₁` / 定理 `isUnit_fromBlocks_zero₂₁`

English:
theorem isUnit_fromBlocks_zero₂₁
  given: {A : Matrix m m α} {B : Matrix m n α} {D : Matrix n n α}
  proof: by
  simp only [← nonempty_invertible_iff_isUnit, ← nonempty_prod,
    (fromBlocksZero₂₁InvertibleEquiv _ _ _).nonempty_congr]

中文:
定理 isUnit_fromBlocks_zero₂₁
  条件: {A : Matrix m m α} {B : Matrix m n α} {D : Matrix n n α}
  证明: by
  simp only [← nonempty_invertible_iff_isUnit, ← nonempty_prod,
    (fromBlocksZero₂₁InvertibleEquiv _ _ _).nonempty_congr]

Depends on / 依赖: nonempty_congr, nonempty_invertible_iff_isUnit, nonempty_prod
-/
theorem isUnit_fromBlocks_zero₂₁ {A : Matrix m m α} {B : Matrix m n α} {D : Matrix n n α} :
    IsUnit (fromBlocks A B 0 D) ↔ IsUnit A ∧ IsUnit D := by
  simp only [← nonempty_invertible_iff_isUnit, ← nonempty_prod,
    (fromBlocksZero₂₁InvertibleEquiv _ _ _).nonempty_congr]

/-- A lower block-triangular matrix is invertible iff both elements of its diagonal are.

This is a propositional form of `Matrix.fromBlocksZero₁₂InvertibleEquiv` forms an `iff`. -/
@[simp]
/--
theorem `isUnit_fromBlocks_zero₁₂` / 定理 `isUnit_fromBlocks_zero₁₂`

English:
theorem isUnit_fromBlocks_zero₁₂
  given: {A : Matrix m m α} {C : Matrix n m α} {D : Matrix n n α}
  proof: by
  simp only [← nonempty_invertible_iff_isUnit, ← nonempty_prod,
    (fromBlocksZero₁₂InvertibleEquiv _ _ _).nonempty_congr]

中文:
定理 isUnit_fromBlocks_zero₁₂
  条件: {A : Matrix m m α} {C : Matrix n m α} {D : Matrix n n α}
  证明: by
  simp only [← nonempty_invertible_iff_isUnit, ← nonempty_prod,
    (fromBlocksZero₁₂InvertibleEquiv _ _ _).nonempty_congr]

Depends on / 依赖: nonempty_congr, nonempty_invertible_iff_isUnit, nonempty_prod
-/
theorem isUnit_fromBlocks_zero₁₂ {A : Matrix m m α} {C : Matrix n m α} {D : Matrix n n α} :
    IsUnit (fromBlocks A 0 C D) ↔ IsUnit A ∧ IsUnit D := by
  simp only [← nonempty_invertible_iff_isUnit, ← nonempty_prod,
    (fromBlocksZero₁₂InvertibleEquiv _ _ _).nonempty_congr]

/--
theorem `inv_fromBlocks_zero₂₁_of_isUnit_iff` / 定理 `inv_fromBlocks_zero₂₁_of_isUnit_iff`

English:
theorem inv_fromBlocks_zero₂₁_of_isUnit_iff
  statement: (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
  proof: by
  by_cases hA : IsUnit A
  · have hD := hAD.mp hA
    cases hA.nonempty_invertible
    cases hD.nonempty_invertible
    let := fromBlocksZero₂₁Invertible A B D
    simp_rw [← invOf_eq_nonsing_inv, invOf_fromBlocks_zero₂₁_eq]
  · have hD := hAD.not.mp hA
    have : ¬IsUnit (fromBlocks A B 0 D) :=


中文:
定理 inv_fromBlocks_zero₂₁_of_isUnit_iff
  结论: (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
  证明: by
  by_cases hA : IsUnit A
  · have hD := hAD.mp hA
    cases hA.nonempty_invertible
    cases hD.nonempty_invertible
    let := fromBlocksZero₂₁Invertible A B D
    simp_rw [← invOf_eq_nonsing_inv, invOf_fromBlocks_zero₂₁_eq]
  · have hD := hAD.not.mp hA
    have : ¬IsUnit (fromBlocks A B 0 D) :=


Depends on / 依赖: IsUnit, Matrix, Matrix.zero_mul, Ring.inverse_non_unit, fromBlocks, fromBlocks_zero, hA.nonempty_invertible, hAD.mp, hAD.not.mp, hD.nonempty_invertible, invOf_eq_nonsing_inv, inverse_non_unit, neg_zero, nonempty_invertible, nonsing_inv_eq_ringInverse, not.mpr, not_and, simp_rw, zero_mul
-/
theorem inv_fromBlocks_zero₂₁_of_isUnit_iff (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
    (hAD : IsUnit A ↔ IsUnit D) :
    (fromBlocks A B 0 D)⁻¹ = fromBlocks A⁻¹ (-(A⁻¹ * B * D⁻¹)) 0 D⁻¹ := by
  by_cases hA : IsUnit A
  · have hD := hAD.mp hA
    cases hA.nonempty_invertible
    cases hD.nonempty_invertible
    let := fromBlocksZero₂₁Invertible A B D
    simp_rw [← invOf_eq_nonsing_inv, invOf_fromBlocks_zero₂₁_eq]
  · have hD := hAD.not.mp hA
    have : ¬IsUnit (fromBlocks A B 0 D) :=
      isUnit_fromBlocks_zero₂₁.not.mpr (not_and'.mpr fun _ => hA)
    simp_rw [nonsing_inv_eq_ringInverse, Ring.inverse_non_unit _ hA, Ring.inverse_non_unit _ hD,
      Ring.inverse_non_unit _ this, Matrix.zero_mul, neg_zero, fromBlocks_zero]

/--
theorem `inv_fromBlocks_zero₁₂_of_isUnit_iff` / 定理 `inv_fromBlocks_zero₁₂_of_isUnit_iff`

English:
theorem inv_fromBlocks_zero₁₂_of_isUnit_iff
  statement: (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
  proof: by
  by_cases hA : IsUnit A
  · have hD := hAD.mp hA
    cases hA.nonempty_invertible
    cases hD.nonempty_invertible
    let := fromBlocksZero₁₂Invertible A C D
    simp_rw [← invOf_eq_nonsing_inv, invOf_fromBlocks_zero₁₂_eq]
  · have hD := hAD.not.mp hA
    have : ¬IsUnit (fromBlocks A 0 C D) :=


中文:
定理 inv_fromBlocks_zero₁₂_of_isUnit_iff
  结论: (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
  证明: by
  by_cases hA : IsUnit A
  · have hD := hAD.mp hA
    cases hA.nonempty_invertible
    cases hD.nonempty_invertible
    let := fromBlocksZero₁₂Invertible A C D
    simp_rw [← invOf_eq_nonsing_inv, invOf_fromBlocks_zero₁₂_eq]
  · have hD := hAD.not.mp hA
    have : ¬IsUnit (fromBlocks A 0 C D) :=


Depends on / 依赖: IsUnit, Matrix, Matrix.zero_mul, Ring.inverse_non_unit, fromBlocks, fromBlocks_zero, hA.nonempty_invertible, hAD.mp, hAD.not.mp, hD.nonempty_invertible, invOf_eq_nonsing_inv, inverse_non_unit, neg_zero, nonempty_invertible, nonsing_inv_eq_ringInverse, not.mpr, not_and, simp_rw, zero_mul
-/
theorem inv_fromBlocks_zero₁₂_of_isUnit_iff (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
    (hAD : IsUnit A ↔ IsUnit D) :
    (fromBlocks A 0 C D)⁻¹ = fromBlocks A⁻¹ 0 (-(D⁻¹ * C * A⁻¹)) D⁻¹ := by
  by_cases hA : IsUnit A
  · have hD := hAD.mp hA
    cases hA.nonempty_invertible
    cases hD.nonempty_invertible
    let := fromBlocksZero₁₂Invertible A C D
    simp_rw [← invOf_eq_nonsing_inv, invOf_fromBlocks_zero₁₂_eq]
  · have hD := hAD.not.mp hA
    have : ¬IsUnit (fromBlocks A 0 C D) :=
      isUnit_fromBlocks_zero₁₂.not.mpr (not_and'.mpr fun _ => hA)
    simp_rw [nonsing_inv_eq_ringInverse, Ring.inverse_non_unit _ hA, Ring.inverse_non_unit _ hD,
      Ring.inverse_non_unit _ this, Matrix.zero_mul, neg_zero, fromBlocks_zero]

end Triangular

/-! ### 2×2 block matrices -/


section Block

/-! #### General 2×2 block matrices -/


/-- A block matrix is invertible if the bottom right corner and the corresponding Schur complement
is. -/
@[instance_reducible]
/--
Definition of `fromBlocks₂₂Invertible` / `fromBlocks₂₂Invertible` 的定义

English:
definition fromBlocks₂₂Invertible
  signature: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  body: by
  -- factor `fromBlocks` via `fromBlocks_eq_of_invertible₂₂`, and state the inverse we expect
  convert!
    Invertible.copy' _ _
      (fromBlocks (⅟(A - B * ⅟D * C)) (-(⅟(A - B * ⅟D * C) * B * ⅟D))
        (-(⅟D * C * ⅟(A - B * ⅟D * C))) (⅟D + ⅟D * C * ⅟(A - B * ⅟D * C) * B * ⅟D))
      (fromBl

中文:
定义 fromBlocks₂₂Invertible
  签名: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  定义体: by
  -- factor `fromBlocks` via `fromBlocks_eq_of_invertible₂₂`, and state the inverse we expect
  convert!
    Invertible.copy' _ _
      (fromBlocks (⅟(A - B * ⅟D * C)) (-(⅟(A - B * ⅟D * C) * B * ⅟D))
        (-(⅟D * C * ⅟(A - B * ⅟D * C))) (⅟D + ⅟D * C * ⅟(A - B * ⅟D * C) * B * ⅟D))
      (fromBl
-/
def fromBlocks₂₂Invertible (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] [Invertible (A - B * ⅟D * C)] :
    Invertible (fromBlocks A B C D) := by
  -- factor `fromBlocks` via `fromBlocks_eq_of_invertible₂₂`, and state the inverse we expect
  convert!
    Invertible.copy' _ _
      (fromBlocks (⅟(A - B * ⅟D * C)) (-(⅟(A - B * ⅟D * C) * B * ⅟D))
        (-(⅟D * C * ⅟(A - B * ⅟D * C))) (⅟D + ⅟D * C * ⅟(A - B * ⅟D * C) * B * ⅟D))
      (fromBlocks_eq_of_invertible₂₂ _ _ _ _) _
  · -- the product is invertible because all the factors are
    letI : Invertible (1 : Matrix n n α) := invertibleOne
    letI : Invertible (1 : Matrix m m α) := invertibleOne
    refine Invertible.mul ?_ (fromBlocksZero₁₂Invertible _ _ _)
    exact
      Invertible.mul (fromBlocksZero₂₁Invertible _ _ _)
        (fromBlocksZero₂₁Invertible _ _ _)
  · -- unfold the `Invertible` instances to get the raw factors
    change
      _ =
        fromBlocks 1 0 (-(1 * (⅟D * C) * 1)) 1 *
          (fromBlocks (⅟(A - B * ⅟D * C)) (-(⅟(A - B * ⅟D * C) * 0 * ⅟D)) 0 (⅟D) *
            fromBlocks 1 (-(1 * (B * ⅟D) * 1)) 0 1)
    -- combine into a single block matrix
    simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add, neg_zero, Matrix.mul_neg, Matrix.neg_mul, neg_neg, ←
      Matrix.mul_assoc, add_comm (⅟D)]

/-- A block matrix is invertible if the top left corner and the corresponding Schur complement
is. -/
@[instance_reducible]
/--
Definition of `fromBlocks₁₁Invertible` / `fromBlocks₁₁Invertible` 的定义

English:
definition fromBlocks₁₁Invertible
  signature: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  body: by
  -- we argue by symmetry
  letI := fromBlocks₂₂Invertible D C B A
  letI iDCBA :=
    submatrixEquivInvertible (fromBlocks D C B A) (Equiv.sumComm _ _) (Equiv.sumComm _ _)
  exact
    iDCBA.copy' _
      (fromBlocks (⅟A + ⅟A * B * ⅟(D - C * ⅟A * B) * C * ⅟A) (-(⅟A * B * ⅟(D - C * ⅟A * B)))
     

中文:
定义 fromBlocks₁₁Invertible
  签名: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  定义体: by
  -- we argue by symmetry
  letI := fromBlocks₂₂Invertible D C B A
  letI iDCBA :=
    submatrixEquivInvertible (fromBlocks D C B A) (Equiv.sumComm _ _) (Equiv.sumComm _ _)
  exact
    iDCBA.copy' _
      (fromBlocks (⅟A + ⅟A * B * ⅟(D - C * ⅟A * B) * C * ⅟A) (-(⅟A * B * ⅟(D - C * ⅟A * B)))
     
-/
def fromBlocks₁₁Invertible (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible A] [Invertible (D - C * ⅟A * B)] :
    Invertible (fromBlocks A B C D) := by
  -- we argue by symmetry
  letI := fromBlocks₂₂Invertible D C B A
  letI iDCBA :=
    submatrixEquivInvertible (fromBlocks D C B A) (Equiv.sumComm _ _) (Equiv.sumComm _ _)
  exact
    iDCBA.copy' _
      (fromBlocks (⅟A + ⅟A * B * ⅟(D - C * ⅟A * B) * C * ⅟A) (-(⅟A * B * ⅟(D - C * ⅟A * B)))
        (-(⅟(D - C * ⅟A * B) * C * ⅟A)) (⅟(D - C * ⅟A * B)))
      (fromBlocks_submatrix_sum_swap_sum_swap _ _ _ _).symm
      (fromBlocks_submatrix_sum_swap_sum_swap _ _ _ _).symm

/--
theorem `invOf_fromBlocks₂₂_eq` / 定理 `invOf_fromBlocks₂₂_eq`

English:
theorem invOf_fromBlocks₂₂_eq
  statement: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  proof: by
  let := fromBlocks₂₂Invertible A B C D
  convert! (rfl : ⅟(fromBlocks A B C D) = _)

中文:
定理 invOf_fromBlocks₂₂_eq
  结论: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  证明: by
  let := fromBlocks₂₂Invertible A B C D
  convert! (rfl : ⅟(fromBlocks A B C D) = _)

Depends on / 依赖: convert, fromBlocks
-/
theorem invOf_fromBlocks₂₂_eq (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] [Invertible (A - B * ⅟D * C)]
    [Invertible (fromBlocks A B C D)] :
    ⅟(fromBlocks A B C D) =
      fromBlocks (⅟(A - B * ⅟D * C)) (-(⅟(A - B * ⅟D * C) * B * ⅟D))
        (-(⅟D * C * ⅟(A - B * ⅟D * C))) (⅟D + ⅟D * C * ⅟(A - B * ⅟D * C) * B * ⅟D) := by
  let := fromBlocks₂₂Invertible A B C D
  convert! (rfl : ⅟(fromBlocks A B C D) = _)

/--
theorem `invOf_fromBlocks₁₁_eq` / 定理 `invOf_fromBlocks₁₁_eq`

English:
theorem invOf_fromBlocks₁₁_eq
  statement: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  proof: by
  let := fromBlocks₁₁Invertible A B C D
  convert! (rfl : ⅟(fromBlocks A B C D) = _)

中文:
定理 invOf_fromBlocks₁₁_eq
  结论: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  证明: by
  let := fromBlocks₁₁Invertible A B C D
  convert! (rfl : ⅟(fromBlocks A B C D) = _)

Depends on / 依赖: convert, fromBlocks
-/
theorem invOf_fromBlocks₁₁_eq (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible A] [Invertible (D - C * ⅟A * B)]
    [Invertible (fromBlocks A B C D)] :
    ⅟(fromBlocks A B C D) =
      fromBlocks (⅟A + ⅟A * B * ⅟(D - C * ⅟A * B) * C * ⅟A) (-(⅟A * B * ⅟(D - C * ⅟A * B)))
        (-(⅟(D - C * ⅟A * B) * C * ⅟A)) (⅟(D - C * ⅟A * B)) := by
  let := fromBlocks₁₁Invertible A B C D
  convert! (rfl : ⅟(fromBlocks A B C D) = _)

/-- If a block matrix is invertible and so is its bottom left element, then so is the corresponding
Schur complement. -/
@[instance_reducible]
/--
Definition of `invertibleOfFromBlocks₂₂Invertible` / `invertibleOfFromBlocks₂₂Invertible` 的定义

English:
definition invertibleOfFromBlocks₂₂Invertible
  signature: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  body: by
  suffices Invertible (fromBlocks (A - B * ⅟D * C) 0 0 D) by
    exact (invertibleOfFromBlocksZero₁₂Invertible (A - B * ⅟D * C) 0 D).1
  letI : Invertible (1 : Matrix n n α) := invertibleOne
  letI : Invertible (1 : Matrix m m α) := invertibleOne
  letI iDC : Invertible (fromBlocks 1 0 (⅟D * C) 1

中文:
定义 invertibleOfFromBlocks₂₂Invertible
  签名: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  定义体: by
  suffices Invertible (fromBlocks (A - B * ⅟D * C) 0 0 D) by
    exact (invertibleOfFromBlocksZero₁₂Invertible (A - B * ⅟D * C) 0 D).1
  letI : Invertible (1 : Matrix n n α) := invertibleOne
  letI : Invertible (1 : Matrix m m α) := invertibleOne
  letI iDC : Invertible (fromBlocks 1 0 (⅟D * C) 1

Depends on / 依赖: Invertible, Matrix, fromBlocks, invertibleOne
-/
def invertibleOfFromBlocks₂₂Invertible (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] [Invertible (fromBlocks A B C D)] :
    Invertible (A - B * ⅟D * C) := by
  suffices Invertible (fromBlocks (A - B * ⅟D * C) 0 0 D) by
    exact (invertibleOfFromBlocksZero₁₂Invertible (A - B * ⅟D * C) 0 D).1
  letI : Invertible (1 : Matrix n n α) := invertibleOne
  letI : Invertible (1 : Matrix m m α) := invertibleOne
  letI iDC : Invertible (fromBlocks 1 0 (⅟D * C) 1 : Matrix (m oplus n) (m oplus n) α) :=
    fromBlocksZero₁₂Invertible _ _ _
  letI iBD : Invertible (fromBlocks 1 (B * ⅟D) 0 1 : Matrix (m oplus n) (m oplus n) α) :=
    fromBlocksZero₂₁Invertible _ _ _
  letI iBDC := Invertible.copy ‹_› _ (fromBlocks_eq_of_invertible₂₂ A B C D).symm
  refine (iBD.mulLeft _).symm ?_
  exact (iDC.mulRight _).symm iBDC

/-- If a block matrix is invertible and so is its bottom left element, then so is the corresponding
Schur complement. -/
@[instance_reducible]
/--
Definition of `invertibleOfFromBlocks₁₁Invertible` / `invertibleOfFromBlocks₁₁Invertible` 的定义

English:
definition invertibleOfFromBlocks₁₁Invertible
  signature: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  body: by
  -- another symmetry argument
  letI iABCD' :=
    submatrixEquivInvertible (fromBlocks A B C D) (Equiv.sumComm _ _) (Equiv.sumComm _ _)
  letI iDCBA := iABCD'.copy _ (fromBlocks_submatrix_sum_swap_sum_swap _ _ _ _).symm
  exact invertibleOfFromBlocks₂₂Invertible D C B A

中文:
定义 invertibleOfFromBlocks₁₁Invertible
  签名: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  定义体: by
  -- another symmetry argument
  letI iABCD' :=
    submatrixEquivInvertible (fromBlocks A B C D) (Equiv.sumComm _ _) (Equiv.sumComm _ _)
  letI iDCBA := iABCD'.copy _ (fromBlocks_submatrix_sum_swap_sum_swap _ _ _ _).symm
  exact invertibleOfFromBlocks₂₂Invertible D C B A
-/
def invertibleOfFromBlocks₁₁Invertible (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible A] [Invertible (fromBlocks A B C D)] :
    Invertible (D - C * ⅟A * B) := by
  -- another symmetry argument
  letI iABCD' :=
    submatrixEquivInvertible (fromBlocks A B C D) (Equiv.sumComm _ _) (Equiv.sumComm _ _)
  letI iDCBA := iABCD'.copy _ (fromBlocks_submatrix_sum_swap_sum_swap _ _ _ _).symm
  exact invertibleOfFromBlocks₂₂Invertible D C B A

/--
Definition of `invertibleEquivFromBlocks₂₂Invertible` / `invertibleEquivFromBlocks₂₂Invertible` 的定义

English:
definition invertibleEquivFromBlocks₂₂Invertible
  signature: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  body: invertibleOfFromBlocks₂₂Invertible _ _ _ _
  invFun _i_schur := fromBlocks₂₂Invertible _ _ _ _
  left_inv _iABCD := Subsingleton.elim _ _
  right_inv _i_schur := Subsingleton.elim _ _

中文:
定义 invertibleEquivFromBlocks₂₂Invertible
  签名: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  定义体: invertibleOfFromBlocks₂₂Invertible _ _ _ _
  invFun _i_schur := fromBlocks₂₂Invertible _ _ _ _
  left_inv _iABCD := Subsingleton.elim _ _
  right_inv _i_schur := Subsingleton.elim _ _
-/
def invertibleEquivFromBlocks₂₂Invertible (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] :
    Invertible (fromBlocks A B C D) ≃ Invertible (A - B * ⅟D * C) where
  toFun _iABCD := invertibleOfFromBlocks₂₂Invertible _ _ _ _
  invFun _i_schur := fromBlocks₂₂Invertible _ _ _ _
  left_inv _iABCD := Subsingleton.elim _ _
  right_inv _i_schur := Subsingleton.elim _ _

/--
Definition of `invertibleEquivFromBlocks₁₁Invertible` / `invertibleEquivFromBlocks₁₁Invertible` 的定义

English:
definition invertibleEquivFromBlocks₁₁Invertible
  signature: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  body: invertibleOfFromBlocks₁₁Invertible _ _ _ _
  invFun _i_schur := fromBlocks₁₁Invertible _ _ _ _
  left_inv _iABCD := Subsingleton.elim _ _
  right_inv _i_schur := Subsingleton.elim _ _

中文:
定义 invertibleEquivFromBlocks₁₁Invertible
  签名: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  定义体: invertibleOfFromBlocks₁₁Invertible _ _ _ _
  invFun _i_schur := fromBlocks₁₁Invertible _ _ _ _
  left_inv _iABCD := Subsingleton.elim _ _
  right_inv _i_schur := Subsingleton.elim _ _
-/
def invertibleEquivFromBlocks₁₁Invertible (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible A] :
    Invertible (fromBlocks A B C D) ≃ Invertible (D - C * ⅟A * B) where
  toFun _iABCD := invertibleOfFromBlocks₁₁Invertible _ _ _ _
  invFun _i_schur := fromBlocks₁₁Invertible _ _ _ _
  left_inv _iABCD := Subsingleton.elim _ _
  right_inv _i_schur := Subsingleton.elim _ _

/--
theorem `isUnit_fromBlocks_iff_of_invertible₂₂` / 定理 `isUnit_fromBlocks_iff_of_invertible₂₂`

English:
theorem isUnit_fromBlocks_iff_of_invertible₂₂
  statement: {A : Matrix m m α} {B : Matrix m n α}
  proof: by
  simp only [← nonempty_invertible_iff_isUnit,
    (invertibleEquivFromBlocks₂₂Invertible A B C D).nonempty_congr]

中文:
定理 isUnit_fromBlocks_iff_of_invertible₂₂
  结论: {A : Matrix m m α} {B : Matrix m n α}
  证明: by
  simp only [← nonempty_invertible_iff_isUnit,
    (invertibleEquivFromBlocks₂₂Invertible A B C D).nonempty_congr]

Depends on / 依赖: nonempty_congr, nonempty_invertible_iff_isUnit
-/
theorem isUnit_fromBlocks_iff_of_invertible₂₂ {A : Matrix m m α} {B : Matrix m n α}
    {C : Matrix n m α} {D : Matrix n n α} [Invertible D] :
    IsUnit (fromBlocks A B C D) ↔ IsUnit (A - B * ⅟D * C) := by
  simp only [← nonempty_invertible_iff_isUnit,
    (invertibleEquivFromBlocks₂₂Invertible A B C D).nonempty_congr]

/--
theorem `isUnit_fromBlocks_iff_of_invertible₁₁` / 定理 `isUnit_fromBlocks_iff_of_invertible₁₁`

English:
theorem isUnit_fromBlocks_iff_of_invertible₁₁
  statement: {A : Matrix m m α} {B : Matrix m n α}
  proof: by
  simp only [← nonempty_invertible_iff_isUnit,
    (invertibleEquivFromBlocks₁₁Invertible A B C D).nonempty_congr]

中文:
定理 isUnit_fromBlocks_iff_of_invertible₁₁
  结论: {A : Matrix m m α} {B : Matrix m n α}
  证明: by
  simp only [← nonempty_invertible_iff_isUnit,
    (invertibleEquivFromBlocks₁₁Invertible A B C D).nonempty_congr]

Depends on / 依赖: nonempty_congr, nonempty_invertible_iff_isUnit
-/
theorem isUnit_fromBlocks_iff_of_invertible₁₁ {A : Matrix m m α} {B : Matrix m n α}
    {C : Matrix n m α} {D : Matrix n n α} [Invertible A] :
    IsUnit (fromBlocks A B C D) ↔ IsUnit (D - C * ⅟A * B) := by
  simp only [← nonempty_invertible_iff_isUnit,
    (invertibleEquivFromBlocks₁₁Invertible A B C D).nonempty_congr]

end Block

/-! ### Lemmas about `Matrix.det` -/


section Det

/--
theorem `det_fromBlocks₁₁` / 定理 `det_fromBlocks₁₁`

English:
theorem det_fromBlocks₁₁
  statement: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  proof: by
  rw [fromBlocks_eq_of_invertible₁₁ (A := A)]; rw [det_mul]; rw [det_mul]; rw [det_fromBlocks_zero₂₁]; rw [det_fromBlocks_zero₂₁]; rw [det_fromBlocks_zero₁₂]; rw [det_one]; rw [det_one]; rw [one_mul]; rw [one_mul]; rw [mul_one]

@[simp]

中文:
定理 det_fromBlocks₁₁
  结论: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  证明: by
  rw [fromBlocks_eq_of_invertible₁₁ (A := A)]; rw [det_mul]; rw [det_mul]; rw [det_fromBlocks_zero₂₁]; rw [det_fromBlocks_zero₂₁]; rw [det_fromBlocks_zero₁₂]; rw [det_one]; rw [det_one]; rw [one_mul]; rw [one_mul]; rw [mul_one]

@[simp]

Depends on / 依赖: det_mul, det_one, mul_one, one_mul
-/
theorem det_fromBlocks₁₁ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible A] :
    (Matrix.fromBlocks A B C D).det = det A * det (D - C * ⅟A * B) := by
  rw [fromBlocks_eq_of_invertible₁₁ (A := A)]; rw [det_mul]; rw [det_mul]; rw [det_fromBlocks_zero₂₁]; rw [det_fromBlocks_zero₂₁]; rw [det_fromBlocks_zero₁₂]; rw [det_one]; rw [det_one]; rw [one_mul]; rw [one_mul]; rw [mul_one]

@[simp]
/--
theorem `det_fromBlocks_one₁₁` / 定理 `det_fromBlocks_one₁₁`

English:
theorem det_fromBlocks_one₁₁
  given: (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α)
  proof: by
  have : Invertible (1 : Matrix m m α) := invertibleOne
  rw [det_fromBlocks₁₁]; rw [invOf_one]; rw [Matrix.mul_one]; rw [det_one]; rw [one_mul]

中文:
定理 det_fromBlocks_one₁₁
  条件: (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α)
  证明: by
  have : Invertible (1 : Matrix m m α) := invertibleOne
  rw [det_fromBlocks₁₁]; rw [invOf_one]; rw [Matrix.mul_one]; rw [det_one]; rw [one_mul]

Depends on / 依赖: Invertible, Matrix, Matrix.mul_one, det_one, invOf_one, invertibleOne, mul_one, one_mul
-/
theorem det_fromBlocks_one₁₁ (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α) :
    (Matrix.fromBlocks 1 B C D).det = det (D - C * B) := by
  have : Invertible (1 : Matrix m m α) := invertibleOne
  rw [det_fromBlocks₁₁]; rw [invOf_one]; rw [Matrix.mul_one]; rw [det_one]; rw [one_mul]

/--
theorem `det_fromBlocks₂₂` / 定理 `det_fromBlocks₂₂`

English:
theorem det_fromBlocks₂₂
  statement: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  proof: by
  have : fromBlocks A B C D =
      (fromBlocks D C B A).submatrix (Equiv.sumComm _ _) (Equiv.sumComm _ _) := by
    ext (i j)
    cases i <;> cases j <;> rfl
  rw [this]; rw [det_submatrix_equiv_self]; rw [det_fromBlocks₁₁]

@[simp]

中文:
定理 det_fromBlocks₂₂
  结论: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  证明: by
  have : fromBlocks A B C D =
      (fromBlocks D C B A).submatrix (Equiv.sumComm _ _) (Equiv.sumComm _ _) := by
    ext (i j)
    cases i <;> cases j <;> rfl
  rw [this]; rw [det_submatrix_equiv_self]; rw [det_fromBlocks₁₁]

@[simp]

Depends on / 依赖: Equiv.sumComm, det_submatrix_equiv_self, fromBlocks, submatrix, sumComm
-/
theorem det_fromBlocks₂₂ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] :
    (Matrix.fromBlocks A B C D).det = det D * det (A - B * ⅟D * C) := by
  have : fromBlocks A B C D =
      (fromBlocks D C B A).submatrix (Equiv.sumComm _ _) (Equiv.sumComm _ _) := by
    ext (i j)
    cases i <;> cases j <;> rfl
  rw [this]; rw [det_submatrix_equiv_self]; rw [det_fromBlocks₁₁]

@[simp]
/--
theorem `det_fromBlocks_one₂₂` / 定理 `det_fromBlocks_one₂₂`

English:
theorem det_fromBlocks_one₂₂
  given: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  proof: by
  have : Invertible (1 : Matrix n n α) := invertibleOne
  rw [det_fromBlocks₂₂]; rw [invOf_one]; rw [Matrix.mul_one]; rw [det_one]; rw [one_mul]

中文:
定理 det_fromBlocks_one₂₂
  条件: (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
  证明: by
  have : Invertible (1 : Matrix n n α) := invertibleOne
  rw [det_fromBlocks₂₂]; rw [invOf_one]; rw [Matrix.mul_one]; rw [det_one]; rw [one_mul]

Depends on / 依赖: Invertible, Matrix, Matrix.mul_one, det_one, invOf_one, invertibleOne, mul_one, one_mul
-/
theorem det_fromBlocks_one₂₂ (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) :
    (Matrix.fromBlocks A B C 1).det = det (A - B * C) := by
  have : Invertible (1 : Matrix n n α) := invertibleOne
  rw [det_fromBlocks₂₂]; rw [invOf_one]; rw [Matrix.mul_one]; rw [det_one]; rw [one_mul]

/--
theorem `det_one_add_mul_comm` / 定理 `det_one_add_mul_comm`

English:
theorem det_one_add_mul_comm
  given: (A : Matrix m n α) (B : Matrix n m α)
  proof: calc
    det (1 + A * B) = det (fromBlocks 1 (-A) B 1) := by
      rw [det_fromBlocks_one₂₂]; rw [Matrix.neg_mul]; rw [sub_neg_eq_add]
    _ = det (1 + B * A) := by rw [det_fromBlocks_one₁₁, Matrix.mul_neg, sub_neg_eq_add]

中文:
定理 det_one_add_mul_comm
  条件: (A : Matrix m n α) (B : Matrix n m α)
  证明: calc
    det (1 + A * B) = det (fromBlocks 1 (-A) B 1) := by
      rw [det_fromBlocks_one₂₂]; rw [Matrix.neg_mul]; rw [sub_neg_eq_add]
    _ = det (1 + B * A) := by rw [det_fromBlocks_one₁₁, Matrix.mul_neg, sub_neg_eq_add]

Depends on / 依赖: Matrix, Matrix.mul_neg, Matrix.neg_mul, fromBlocks, mul_neg, neg_mul, sub_neg_eq_add
-/
theorem det_one_add_mul_comm (A : Matrix m n α) (B : Matrix n m α) :
    det (1 + A * B) = det (1 + B * A) :=
  calc
    det (1 + A * B) = det (fromBlocks 1 (-A) B 1) := by
      rw [det_fromBlocks_one₂₂]; rw [Matrix.neg_mul]; rw [sub_neg_eq_add]
    _ = det (1 + B * A) := by rw [det_fromBlocks_one₁₁, Matrix.mul_neg, sub_neg_eq_add]

/--
theorem `det_mul_add_one_comm` / 定理 `det_mul_add_one_comm`

English:
theorem det_mul_add_one_comm
  given: (A : Matrix m n α) (B : Matrix n m α)
  proof: by rw [add_comm, det_one_add_mul_comm, add_comm]

中文:
定理 det_mul_add_one_comm
  条件: (A : Matrix m n α) (B : Matrix n m α)
  证明: by rw [add_comm, det_one_add_mul_comm, add_comm]

Depends on / 依赖: add_comm, det_one_add_mul_comm
-/
theorem det_mul_add_one_comm (A : Matrix m n α) (B : Matrix n m α) :
    det (A * B + 1) = det (B * A + 1) := by rw [add_comm, det_one_add_mul_comm, add_comm]

/--
theorem `det_one_sub_mul_comm` / 定理 `det_one_sub_mul_comm`

English:
theorem det_one_sub_mul_comm
  given: (A : Matrix m n α) (B : Matrix n m α)
  proof: by
  rw [sub_eq_add_neg]; rw [← Matrix.neg_mul]; rw [det_one_add_mul_comm]; rw [Matrix.mul_neg]; rw [← sub_eq_add_neg]

中文:
定理 det_one_sub_mul_comm
  条件: (A : Matrix m n α) (B : Matrix n m α)
  证明: by
  rw [sub_eq_add_neg]; rw [← Matrix.neg_mul]; rw [det_one_add_mul_comm]; rw [Matrix.mul_neg]; rw [← sub_eq_add_neg]

Depends on / 依赖: Matrix, Matrix.mul_neg, Matrix.neg_mul, det_one_add_mul_comm, mul_neg, neg_mul, sub_eq_add_neg
-/
theorem det_one_sub_mul_comm (A : Matrix m n α) (B : Matrix n m α) :
    det (1 - A * B) = det (1 - B * A) := by
  rw [sub_eq_add_neg]; rw [← Matrix.neg_mul]; rw [det_one_add_mul_comm]; rw [Matrix.mul_neg]; rw [← sub_eq_add_neg]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `det_one_add_replicateCol_mul_replicateRow` / 定理 `det_one_add_replicateCol_mul_replicateRow`

English:
theorem det_one_add_replicateCol_mul_replicateRow
  given: {ι : Type*} [Unique ι] (u v : m -> α)
  proof: by
  rw [det_one_add_mul_comm]; rw [det_unique]; rw [Pi.add_apply]; rw [Pi.add_apply]; rw [Matrix.one_apply_eq]; rw [Matrix.replicateRow_mul_replicateCol_apply]

中文:
定理 det_one_add_replicateCol_mul_replicateRow
  条件: {ι : 类型} [Unique ι] (u v : m -> α)
  证明: by
  rw [det_one_add_mul_comm]; rw [det_unique]; rw [Pi.add_apply]; rw [Pi.add_apply]; rw [Matrix.one_apply_eq]; rw [Matrix.replicateRow_mul_replicateCol_apply]

Depends on / 依赖: Matrix, Matrix.one_apply_eq, Matrix.replicateRow_mul_replicateCol_apply, Pi.add_apply, add_apply, det_one_add_mul_comm, det_unique, one_apply_eq, replicateRow_mul_replicateCol_apply
-/
theorem det_one_add_replicateCol_mul_replicateRow {ι : Type*} [Unique ι] (u v : m -> α) :
    det (1 + replicateCol ι u * replicateRow ι v) = 1 + v ⬝ᵥ u := by
  rw [det_one_add_mul_comm]; rw [det_unique]; rw [Pi.add_apply]; rw [Pi.add_apply]; rw [Matrix.one_apply_eq]; rw [Matrix.replicateRow_mul_replicateCol_apply]

/--
theorem `det_add_replicateCol_mul_replicateRow` / 定理 `det_add_replicateCol_mul_replicateRow`

English:
theorem det_add_replicateCol_mul_replicateRow
  statement: {ι : Type*} [Unique ι]
  proof: by
  nth_rewrite 1 [← Matrix.mul_one A]
  rwa [← Matrix.mul_nonsing_inv_cancel_left A (replicateCol ι u * replicateRow ι v),
    ← Matrix.mul_add, det_mul, ← Matrix.mul_assoc, det_one_add_mul_comm, ← Matrix.mul_assoc]

中文:
定理 det_add_replicateCol_mul_replicateRow
  结论: {ι : 类型} [Unique ι]
  证明: by
  nth_rewrite 1 [← Matrix.mul_one A]
  rwa [← Matrix.mul_nonsing_inv_cancel_left A (replicateCol ι u * replicateRow ι v),
    ← Matrix.mul_add, det_mul, ← Matrix.mul_assoc, det_one_add_mul_comm, ← Matrix.mul_assoc]

Depends on / 依赖: Matrix, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left, Matrix.mul_one, det_mul, det_one_add_mul_comm, mul_add, mul_assoc, mul_nonsing_inv_cancel_left, mul_one, nth_rewrite, replicateCol, replicateRow
-/
theorem det_add_replicateCol_mul_replicateRow {ι : Type*} [Unique ι]
    {A : Matrix m m α} (hA : IsUnit A.det) (u v : m -> α) :
    (A + replicateCol ι u * replicateRow ι v).det =
    A.det * (1 + replicateRow ι v * A⁻¹ * replicateCol ι u).det := by
  nth_rewrite 1 [← Matrix.mul_one A]
  rwa [← Matrix.mul_nonsing_inv_cancel_left A (replicateCol ι u * replicateRow ι v),
    ← Matrix.mul_add, det_mul, ← Matrix.mul_assoc, det_one_add_mul_comm, ← Matrix.mul_assoc]

/--
theorem `det_add_mul` / 定理 `det_add_mul`

English:
theorem det_add_mul
  statement: {A : Matrix m m α} (U : Matrix m n α)
  proof: by
  nth_rewrite 1 [← Matrix.mul_one A]
  rwa [← Matrix.mul_nonsing_inv_cancel_left A (U * V), ← Matrix.mul_add,
    det_mul, ← Matrix.mul_assoc, det_one_add_mul_comm, ← Matrix.mul_assoc]

中文:
定理 det_add_mul
  结论: {A : Matrix m m α} (U : Matrix m n α)
  证明: by
  nth_rewrite 1 [← Matrix.mul_one A]
  rwa [← Matrix.mul_nonsing_inv_cancel_left A (U * V), ← Matrix.mul_add,
    det_mul, ← Matrix.mul_assoc, det_one_add_mul_comm, ← Matrix.mul_assoc]

Depends on / 依赖: Matrix, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left, Matrix.mul_one, det_mul, det_one_add_mul_comm, mul_add, mul_assoc, mul_nonsing_inv_cancel_left, mul_one, nth_rewrite
-/
theorem det_add_mul {A : Matrix m m α} (U : Matrix m n α)
    (V : Matrix n m α) (hA : IsUnit A.det) :
    (A + U * V).det = A.det * (1 + V * A⁻¹ * U).det := by
  nth_rewrite 1 [← Matrix.mul_one A]
  rwa [← Matrix.mul_nonsing_inv_cancel_left A (U * V), ← Matrix.mul_add,
    det_mul, ← Matrix.mul_assoc, det_one_add_mul_comm, ← Matrix.mul_assoc]

end Det

end CommRing

end Matrix
