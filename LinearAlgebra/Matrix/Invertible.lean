/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Ahmad Alkhalawi
-/
module

public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Tactic.Abel

/-! # Extra lemmas about invertible matrices

A few of the `Invertible` lemmas generalize to multiplication of rectangular matrices.

For lemmas about the matrix inverse in terms of the determinant and adjugate, see `Matrix.inv`
in `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`.

## Main results

* `Matrix.invertibleConjTranspose`
* `Matrix.invertibleTranspose`
* `Matrix.isUnit_conjTranspose`
* `Matrix.isUnit_transpose`
-/

@[expose] public section


open scoped Matrix

variable {m n : Type*} {α : Type*}
variable [Fintype n] [DecidableEq n]

namespace Matrix

section Semiring
variable [Semiring α]

/--
theorem `invOf_mul_cancel_left` / 定理 `invOf_mul_cancel_left`

English:
theorem invOf_mul_cancel_left
  given: (A : Matrix n n α) (B : Matrix n m α) [Invertible A]
  proof: by rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]

中文:
定理 invOf_mul_cancel_left
  条件: (A : 矩阵 n n α) (B : 矩阵 n m α) [可逆 A]
  证明: by rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]
-/
protected theorem invOf_mul_cancel_left (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    ⅟A * (A * B) = B := by rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]

/--
theorem `mul_invOf_cancel_left` / 定理 `mul_invOf_cancel_left`

English:
theorem mul_invOf_cancel_left
  given: (A : Matrix n n α) (B : Matrix n m α) [Invertible A]
  proof: by rw [← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]

中文:
定理 mul_invOf_cancel_left
  条件: (A : 矩阵 n n α) (B : 矩阵 n m α) [可逆 A]
  证明: by rw [← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
-/
protected theorem mul_invOf_cancel_left (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    A * (⅟A * B) = B := by rw [← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]

/--
theorem `invOf_mul_cancel_right` / 定理 `invOf_mul_cancel_right`

English:
theorem invOf_mul_cancel_right
  given: (A : Matrix m n α) (B : Matrix n n α) [Invertible B]
  proof: by rw [Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]

中文:
定理 invOf_mul_cancel_right
  条件: (A : 矩阵 m n α) (B : 矩阵 n n α) [可逆 B]
  证明: by rw [Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]
-/
protected theorem invOf_mul_cancel_right (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A * ⅟B * B = A := by rw [Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]

/--
theorem `mul_invOf_cancel_right` / 定理 `mul_invOf_cancel_right`

English:
theorem mul_invOf_cancel_right
  given: (A : Matrix m n α) (B : Matrix n n α) [Invertible B]
  proof: by rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]

中文:
定理 mul_invOf_cancel_right
  条件: (A : 矩阵 m n α) (B : 矩阵 n n α) [可逆 B]
  证明: by rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]
-/
protected theorem mul_invOf_cancel_right (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A * B * ⅟B = A := by rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]

/--
theorem `invOf_mul_eq_iff_eq_mul_left` / 定理 `invOf_mul_eq_iff_eq_mul_left`

English:
theorem invOf_mul_eq_iff_eq_mul_left
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h, Matrix.mul_invOf_cancel_left]
  · rw [h, Matrix.invOf_mul_cancel_left]

中文:
定理 invOf_mul_eq_iff_eq_mul_left
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h, Matrix.mul_invOf_cancel_left]
  · rw [h, Matrix.invOf_mul_cancel_left]
-/
protected theorem invOf_mul_eq_iff_eq_mul_left
    {A B : Matrix n m α} {C : Matrix n n α} [Invertible C] :
    ⅟C * A = B ↔ A = C * B := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h, Matrix.mul_invOf_cancel_left]
  · rw [h, Matrix.invOf_mul_cancel_left]

/--
theorem `mul_left_eq_iff_eq_invOf_mul` / 定理 `mul_left_eq_iff_eq_invOf_mul`

English:
theorem mul_left_eq_iff_eq_invOf_mul
  proof: by
  rw [eq_comm]; rw [← Matrix.invOf_mul_eq_iff_eq_mul_left]; rw [eq_comm]

中文:
定理 mul_left_eq_iff_eq_invOf_mul
  证明: by
  rw [eq_comm]; rw [← Matrix.invOf_mul_eq_iff_eq_mul_left]; rw [eq_comm]
-/
protected theorem mul_left_eq_iff_eq_invOf_mul
    {A B : Matrix n m α} {C : Matrix n n α} [Invertible C] :
    C * A = B ↔ A = ⅟C * B := by
  rw [eq_comm]; rw [← Matrix.invOf_mul_eq_iff_eq_mul_left]; rw [eq_comm]

/--
theorem `mul_invOf_eq_iff_eq_mul_right` / 定理 `mul_invOf_eq_iff_eq_mul_right`

English:
theorem mul_invOf_eq_iff_eq_mul_right
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h, Matrix.invOf_mul_cancel_right]
  · rw [h, Matrix.mul_invOf_cancel_right]

中文:
定理 mul_invOf_eq_iff_eq_mul_right
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h, Matrix.invOf_mul_cancel_right]
  · rw [h, Matrix.mul_invOf_cancel_right]
-/
protected theorem mul_invOf_eq_iff_eq_mul_right
    {A B : Matrix m n α} {C : Matrix n n α} [Invertible C] :
    A * ⅟C = B ↔ A = B * C := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h, Matrix.invOf_mul_cancel_right]
  · rw [h, Matrix.mul_invOf_cancel_right]

/--
theorem `mul_right_eq_iff_eq_mul_invOf` / 定理 `mul_right_eq_iff_eq_mul_invOf`

English:
theorem mul_right_eq_iff_eq_mul_invOf
  proof: by
  rw [eq_comm]; rw [← Matrix.mul_invOf_eq_iff_eq_mul_right]; rw [eq_comm]

中文:
定理 mul_right_eq_iff_eq_mul_invOf
  证明: by
  rw [eq_comm]; rw [← Matrix.mul_invOf_eq_iff_eq_mul_right]; rw [eq_comm]
-/
protected theorem mul_right_eq_iff_eq_mul_invOf
    {A B : Matrix m n α} {C : Matrix n n α} [Invertible C] :
    A * C = B ↔ A = B * ⅟C := by
  rw [eq_comm]; rw [← Matrix.mul_invOf_eq_iff_eq_mul_right]; rw [eq_comm]

section ConjTranspose
variable [StarRing α] (A : Matrix n n α)

/--
Instance `invertibleConjTranspose` / 实例 `invertibleConjTranspose`

English:
instance invertibleConjTranspose
  signature: [Invertible A]
  body: Invertible.star _

中文:
实例 invertibleConjTranspose
  签名: [可逆 A]
  定义体: Invertible.star _

Depends on / 依赖: Invertible, Invertible.star
-/
instance invertibleConjTranspose [Invertible A] : Invertible Aᴴ := Invertible.star _

/--
lemma `conjTranspose_invOf` / 引理 `conjTranspose_invOf`

English:
lemma conjTranspose_invOf
  given: [Invertible A] [Invertible Aᴴ]
  statement: (⅟A)ᴴ = ⅟(Aᴴ)
  proof: star_invOf _

中文:
引理 conjTranspose_invOf
  条件: [可逆 A] [可逆 Aᴴ]
  结论: (⅟A)ᴴ = ⅟(Aᴴ)
  证明: star_invOf _

Depends on / 依赖: star_invOf
-/
lemma conjTranspose_invOf [Invertible A] [Invertible Aᴴ] : (⅟A)ᴴ = ⅟(Aᴴ) := star_invOf _

/-- A matrix is invertible if the conjugate transpose is invertible. -/
@[implicit_reducible]
/--
Definition of `invertibleOfInvertibleConjTranspose` / `invertibleOfInvertibleConjTranspose` 的定义

English:
definition invertibleOfInvertibleConjTranspose
  signature: [Invertible Aᴴ]
  body: by
  rw [← conjTranspose_conjTranspose A]; rw [← star_eq_conjTranspose]
  infer_instance

中文:
定义 invertibleOfInvertibleConjTranspose
  签名: [可逆 Aᴴ]
  定义体: by
  rw [← conjTranspose_conjTranspose A]; rw [← star_eq_conjTranspose]
  infer_instance

Depends on / 依赖: conjTranspose_conjTranspose, infer_instance, star_eq_conjTranspose
-/
def invertibleOfInvertibleConjTranspose [Invertible Aᴴ] : Invertible A := by
  rw [← conjTranspose_conjTranspose A]; rw [← star_eq_conjTranspose]
  infer_instance

/--
lemma `isUnit_conjTranspose` / 引理 `isUnit_conjTranspose`

English:
lemma isUnit_conjTranspose
  statement: IsUnit Aᴴ ↔ IsUnit A
  proof: isUnit_star

中文:
引理 isUnit_conjTranspose
  结论: 是单位 Aᴴ ↔ 是单位 A
  证明: isUnit_star
-/
@[simp] lemma isUnit_conjTranspose : IsUnit Aᴴ ↔ IsUnit A := isUnit_star

end ConjTranspose

end Semiring

section CommSemiring

variable [CommSemiring α] (A : Matrix n n α)

/--
Instance `invertibleTranspose` / 实例 `invertibleTranspose`

English:
instance invertibleTranspose
  signature: [Invertible A]
  body: (⅟A)ᵀ
  invOf_mul_self := by rw [← transpose_mul, mul_invOf_self, transpose_one]
  mul_invOf_self := by rw [← transpose_mul, invOf_mul_self, transpose_one]

中文:
实例 invertibleTranspose
  签名: [可逆 A]
  定义体: (⅟A)ᵀ
  invOf_mul_self := by rw [← transpose_mul, mul_invOf_self, transpose_one]
  mul_invOf_self := by rw [← transpose_mul, invOf_mul_self, transpose_one]
-/
instance invertibleTranspose [Invertible A] : Invertible Aᵀ where
  invOf := (⅟A)ᵀ
  invOf_mul_self := by rw [← transpose_mul, mul_invOf_self, transpose_one]
  mul_invOf_self := by rw [← transpose_mul, invOf_mul_self, transpose_one]

/--
lemma `transpose_invOf` / 引理 `transpose_invOf`

English:
lemma transpose_invOf
  given: [Invertible A] [Invertible Aᵀ]
  statement: (⅟A)ᵀ = ⅟(Aᵀ)
  proof: by
  let := invertibleTranspose A
  convert! (rfl : _ = ⅟(Aᵀ))

中文:
引理 transpose_invOf
  条件: [可逆 A] [可逆 Aᵀ]
  结论: (⅟A)ᵀ = ⅟(Aᵀ)
  证明: by
  let := invertibleTranspose A
  convert! (rfl : _ = ⅟(Aᵀ))

Depends on / 依赖: convert, invertibleTranspose
-/
lemma transpose_invOf [Invertible A] [Invertible Aᵀ] : (⅟A)ᵀ = ⅟(Aᵀ) := by
  let := invertibleTranspose A
  convert! (rfl : _ = ⅟(Aᵀ))

/-- `Aᵀ` is invertible when `A` is. -/
@[implicit_reducible]
/--
Definition of `invertibleOfInvertibleTranspose` / `invertibleOfInvertibleTranspose` 的定义

English:
definition invertibleOfInvertibleTranspose
  signature: [Invertible Aᵀ]
  body: (⅟(Aᵀ))ᵀ
  invOf_mul_self := by rw [← transpose_one, ← mul_invOf_self Aᵀ, transpose_mul, transpose_transpose]
  mul_invOf_self := by rw [← transpose_one, ← invOf_mul_self Aᵀ, transpose_mul, transpose_transpose]

中文:
定义 invertibleOfInvertibleTranspose
  签名: [可逆 Aᵀ]
  定义体: (⅟(Aᵀ))ᵀ
  invOf_mul_self := by rw [← transpose_one, ← mul_invOf_self Aᵀ, transpose_mul, transpose_transpose]
  mul_invOf_self := by rw [← transpose_one, ← invOf_mul_self Aᵀ, transpose_mul, transpose_transpose]
-/
def invertibleOfInvertibleTranspose [Invertible Aᵀ] : Invertible A where
  invOf := (⅟(Aᵀ))ᵀ
  invOf_mul_self := by rw [← transpose_one, ← mul_invOf_self Aᵀ, transpose_mul, transpose_transpose]
  mul_invOf_self := by rw [← transpose_one, ← invOf_mul_self Aᵀ, transpose_mul, transpose_transpose]

/-- Together `Matrix.invertibleTranspose` and `Matrix.invertibleOfInvertibleTranspose` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
/--
Definition of `transposeInvertibleEquivInvertible` / `transposeInvertibleEquivInvertible` 的定义

English:
definition transposeInvertibleEquivInvertible
  signature: : Invertible Aᵀ ≃ Invertible A where
  body: @invertibleOfInvertibleTranspose _ _ _ _ _ _
  invFun := @invertibleTranspose _ _ _ _ _ _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 transposeInvertibleEquivInvertible
  签名: : 可逆 Aᵀ ≃ 可逆 A where
  定义体: @invertibleOfInvertibleTranspose _ _ _ _ _ _
  invFun := @invertibleTranspose _ _ _ _ _ _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

Depends on / 依赖: invertibleOfInvertibleTranspose
-/
def transposeInvertibleEquivInvertible : Invertible Aᵀ ≃ Invertible A where
  toFun := @invertibleOfInvertibleTranspose _ _ _ _ _ _
  invFun := @invertibleTranspose _ _ _ _ _ _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/--
lemma `isUnit_transpose` / 引理 `isUnit_transpose`

English:
lemma isUnit_transpose
  statement: IsUnit Aᵀ ↔ IsUnit A
  proof: by
  simp only [← nonempty_invertible_iff_isUnit,
    (transposeInvertibleEquivInvertible A).nonempty_congr]

中文:
引理 isUnit_transpose
  结论: 是单位 Aᵀ ↔ 是单位 A
  证明: by
  simp only [← nonempty_invertible_iff_isUnit,
    (transposeInvertibleEquivInvertible A).nonempty_congr]
-/
@[simp] lemma isUnit_transpose : IsUnit Aᵀ ↔ IsUnit A := by
  simp only [← nonempty_invertible_iff_isUnit,
    (transposeInvertibleEquivInvertible A).nonempty_congr]

end CommSemiring

section Ring

section Woodbury

variable [Fintype m] [DecidableEq m] [Ring α]
    (A : Matrix n n α) (U : Matrix n m α) (C : Matrix m m α) (V : Matrix m n α)
    [Invertible A] [Invertible C] [Invertible (⅟C + V * ⅟A * U)]

-- No spaces around multiplication signs for better clarity
set_option linter.style.whitespace false in
/--
lemma `add_mul_mul_invOf_mul_eq_one` / 引理 `add_mul_mul_invOf_mul_eq_one`

English:
lemma add_mul_mul_invOf_mul_eq_one
  proof: by
  calc
    (A + U*C*V)*(⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)
    _ = A*⅟A - A*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A + U*C*V*⅟A - U*C*V*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A := by
      simp_rw [add_sub_assoc, add_mul, mul_sub, Matrix.mul_assoc]
    _ = (1 + U*C*V*⅟A) - (U*⅟(⅟C + V*⅟A*U)*V*⅟A + U*C*V*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A) :=

中文:
引理 add_mul_mul_invOf_mul_eq_one
  证明: by
  calc
    (A + U*C*V)*(⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)
    _ = A*⅟A - A*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A + U*C*V*⅟A - U*C*V*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A := by
      simp_rw [add_sub_assoc, add_mul, mul_sub, Matrix.mul_assoc]
    _ = (1 + U*C*V*⅟A) - (U*⅟(⅟C + V*⅟A*U)*V*⅟A + U*C*V*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A) :=

Depends on / 依赖: Matrix, Matrix.add_mul, Matrix.mul_assoc, Matrix.one_mul, add_mul, add_sub_assoc, mul_assoc, mul_invOf_self, mul_sub, one_mul, simp_rw, sub_right_inj
-/
lemma add_mul_mul_invOf_mul_eq_one :
    (A + U*C*V)*(⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A) = 1 := by
  calc
    (A + U*C*V)*(⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)
    _ = A*⅟A - A*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A + U*C*V*⅟A - U*C*V*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A := by
      simp_rw [add_sub_assoc, add_mul, mul_sub, Matrix.mul_assoc]
    _ = (1 + U*C*V*⅟A) - (U*⅟(⅟C + V*⅟A*U)*V*⅟A + U*C*V*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A) := by
      rw [mul_invOf_self]; rw [Matrix.one_mul]
      abel
    _ = 1 + U*C*V*⅟A - (U + U*C*V*⅟A*U)*⅟(⅟C + V*⅟A*U)*V*⅟A := by
      rw [sub_right_inj]; rw [Matrix.add_mul]; rw [Matrix.add_mul]; rw [Matrix.add_mul]
    _ = 1 + U*C*V*⅟A - U*C*(⅟C + V*⅟A*U)*⅟(⅟C + V*⅟A*U)*V*⅟A := by
      congr
      simp only [Matrix.mul_add, Matrix.mul_invOf_cancel_right, ← Matrix.mul_assoc]
    _ = 1 := by
      rw [Matrix.mul_invOf_cancel_right]
      abel

-- No spaces around multiplication signs for better clarity
set_option linter.style.whitespace false in
/--
lemma `add_mul_mul_invOf_mul_eq_one'` / 引理 `add_mul_mul_invOf_mul_eq_one'`

English:
lemma add_mul_mul_invOf_mul_eq_one'
  proof: by
  calc
    (⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)*(A + U*C*V)
    _ = ⅟A*A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*A + ⅟A*U*C*V - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*U*C*V := by
      simp_rw [add_sub_assoc, _root_.mul_add, _root_.sub_mul, Matrix.mul_assoc]
    _ = (1 + ⅟A*U*C*V) - (⅟A*U*⅟(⅟C + V*⅟A*U)*V + ⅟A*U*⅟(⅟C + V*⅟A*U)*

中文:
引理 add_mul_mul_invOf_mul_eq_one'
  证明: by
  calc
    (⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)*(A + U*C*V)
    _ = ⅟A*A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*A + ⅟A*U*C*V - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*U*C*V := by
      simp_rw [add_sub_assoc, _root_.mul_add, _root_.sub_mul, Matrix.mul_assoc]
    _ = (1 + ⅟A*U*C*V) - (⅟A*U*⅟(⅟C + V*⅟A*U)*V + ⅟A*U*⅟(⅟C + V*⅟A*U)*

Depends on / 依赖: Matrix, Matrix.invOf_mul_cancel_right, Matrix.mul_add, Matrix.mul_assoc, _root_, _root_.mul_add, _root_.sub_mul, add_sub_assoc, invOf_mul_cancel_right, invOf_mul_self, mul_add, mul_assoc, simp_rw, sub_mul, sub_right_inj
-/
lemma add_mul_mul_invOf_mul_eq_one' :
    (⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)*(A + U*C*V) = 1 := by
  calc
    (⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)*(A + U*C*V)
    _ = ⅟A*A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*A + ⅟A*U*C*V - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*U*C*V := by
      simp_rw [add_sub_assoc, _root_.mul_add, _root_.sub_mul, Matrix.mul_assoc]
    _ = (1 + ⅟A*U*C*V) - (⅟A*U*⅟(⅟C + V*⅟A*U)*V + ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*U*C*V) := by
      rw [invOf_mul_self]; rw [Matrix.invOf_mul_cancel_right]
      abel
    _ = 1 + ⅟A*U*C*V - ⅟A*U*⅟(⅟C + V*⅟A*U)*(V + V*⅟A*U*C*V) := by
      rw [sub_right_inj]; rw [Matrix.mul_add]
      simp_rw [Matrix.mul_assoc]
    _ = 1 + ⅟A*U*C*V - ⅟A*U*⅟(⅟C + V*⅟A*U)*(⅟C + V*⅟A*U)*C*V := by
      simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc,
        Matrix.invOf_mul_cancel_right]
    _ = 1 := by
      rw [Matrix.invOf_mul_cancel_right]
      abel

/-- If matrices `A`, `C`, and `C⁻¹ + V * A⁻¹ * U` are invertible, then so is `A + U * C * V`. -/
@[implicit_reducible]
/--
Definition of `invertibleAddMulMul` / `invertibleAddMulMul` 的定义

English:
definition invertibleAddMulMul
  signature: : Invertible (A + U * C * V) where
  body: ⅟A - ⅟A * U * ⅟(⅟C + V * ⅟A * U) * V * ⅟A
  invOf_mul_self := add_mul_mul_invOf_mul_eq_one' _ _ _ _
  mul_invOf_self := add_mul_mul_invOf_mul_eq_one _ _ _ _

中文:
定义 invertibleAddMulMul
  签名: : 可逆 (A + U * C * V) where
  定义体: ⅟A - ⅟A * U * ⅟(⅟C + V * ⅟A * U) * V * ⅟A
  invOf_mul_self := add_mul_mul_invOf_mul_eq_one' _ _ _ _
  mul_invOf_self := add_mul_mul_invOf_mul_eq_one _ _ _ _
-/
def invertibleAddMulMul : Invertible (A + U * C * V) where
  invOf := ⅟A - ⅟A * U * ⅟(⅟C + V * ⅟A * U) * V * ⅟A
  invOf_mul_self := add_mul_mul_invOf_mul_eq_one' _ _ _ _
  mul_invOf_self := add_mul_mul_invOf_mul_eq_one _ _ _ _

/--
theorem `invOf_add_mul_mul` / 定理 `invOf_add_mul_mul`

English:
theorem invOf_add_mul_mul
  given: [Invertible (A + U * C * V)]
  proof: by
  let := invertibleAddMulMul A U C V
  convert! (rfl : ⅟(A + U * C * V) = _)

中文:
定理 invOf_add_mul_mul
  条件: [可逆 (A + U * C * V)]
  证明: by
  let := invertibleAddMulMul A U C V
  convert! (rfl : ⅟(A + U * C * V) = _)

Depends on / 依赖: convert, invertibleAddMulMul
-/
theorem invOf_add_mul_mul [Invertible (A + U * C * V)] :
    ⅟(A + U * C * V) = ⅟A - ⅟A * U * ⅟(⅟C + V * ⅟A * U) * V * ⅟A := by
  let := invertibleAddMulMul A U C V
  convert! (rfl : ⅟(A + U * C * V) = _)

end Woodbury

section BinomialInverseTheorem

variable [Fintype m] [DecidableEq m] [Ring α]
    (A : Matrix n n α) (U : Matrix n m α) (C : Matrix m m α) (V : Matrix m n α)
    [Invertible A] [Invertible (C + C * V * ⅟A * U * C)]

/--
lemma `add_mul_mul_mul_invOf_eq_one` / 引理 `add_mul_mul_mul_invOf_eq_one`

English:
lemma add_mul_mul_mul_invOf_eq_one
  proof: by
  simp only [Matrix.mul_sub, Matrix.add_mul, mul_invOf_self']
  rw [add_sub_assoc]; rw [add_eq_left]; rw [sub_eq_zero]
  simp only [← Matrix.mul_assoc, mul_invOf_self', Matrix.one_mul]
  simp only [← Matrix.add_mul]
  congr
  rw [← Matrix.mul_right_eq_iff_eq_mul_invOf]
  simp only [Matrix.add_mul

中文:
引理 add_mul_mul_mul_invOf_eq_one
  证明: by
  simp only [Matrix.mul_sub, Matrix.add_mul, mul_invOf_self']
  rw [add_sub_assoc]; rw [add_eq_left]; rw [sub_eq_zero]
  simp only [← Matrix.mul_assoc, mul_invOf_self', Matrix.one_mul]
  simp only [← Matrix.add_mul]
  congr
  rw [← Matrix.mul_right_eq_iff_eq_mul_invOf]
  simp only [Matrix.add_mul

Depends on / 依赖: Matrix, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_right_eq_iff_eq_mul_invOf, Matrix.mul_sub, Matrix.one_mul, add_eq_left, add_mul, add_sub_assoc, mul_add, mul_assoc, mul_invOf_self, mul_right_eq_iff_eq_mul_invOf, mul_sub, one_mul, sub_eq_zero
-/
lemma add_mul_mul_mul_invOf_eq_one :
    (A + U * C * V) * (⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A) = 1 := by
  simp only [Matrix.mul_sub, Matrix.add_mul, mul_invOf_self']
  rw [add_sub_assoc]; rw [add_eq_left]; rw [sub_eq_zero]
  simp only [← Matrix.mul_assoc, mul_invOf_self', Matrix.one_mul]
  simp only [← Matrix.add_mul]
  congr
  rw [← Matrix.mul_right_eq_iff_eq_mul_invOf]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]

/--
lemma `add_mul_mul_mul_invOf_eq_one'` / 引理 `add_mul_mul_mul_invOf_eq_one'`

English:
lemma add_mul_mul_mul_invOf_eq_one'
  proof: by
  simp only [Matrix.mul_add, Matrix.sub_mul, invOf_mul_self']
  rw [sub_add]; rw [sub_eq_self]; rw [sub_eq_zero]
  simp only [Matrix.mul_assoc, ← Matrix.mul_sub]
  congr
  rw [eq_sub_iff_add_eq]; rw [← Matrix.mul_add]
  rw [Matrix.invOf_mul_eq_iff_eq_mul_left]
  simp only [Matrix.add_mul, invOf_m

中文:
引理 add_mul_mul_mul_invOf_eq_one'
  证明: by
  simp only [Matrix.mul_add, Matrix.sub_mul, invOf_mul_self']
  rw [sub_add]; rw [sub_eq_self]; rw [sub_eq_zero]
  simp only [Matrix.mul_assoc, ← Matrix.mul_sub]
  congr
  rw [eq_sub_iff_add_eq]; rw [← Matrix.mul_add]
  rw [Matrix.invOf_mul_eq_iff_eq_mul_left]
  simp only [Matrix.add_mul, invOf_m

Depends on / 依赖: Matrix, Matrix.add_mul, Matrix.invOf_mul_eq_iff_eq_mul_left, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_one, Matrix.mul_sub, Matrix.sub_mul, add_mul, add_right_inj, eq_sub_iff_add_eq, invOf_mul_eq_iff_eq_mul_left, invOf_mul_self, mul_add, mul_assoc, mul_one, mul_sub, sub_add, sub_eq_self, sub_eq_zero
-/
lemma add_mul_mul_mul_invOf_eq_one' :
    (⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A) * (A + U * C * V) = 1 := by
  simp only [Matrix.mul_add, Matrix.sub_mul, invOf_mul_self']
  rw [sub_add]; rw [sub_eq_self]; rw [sub_eq_zero]
  simp only [Matrix.mul_assoc, ← Matrix.mul_sub]
  congr
  rw [eq_sub_iff_add_eq]; rw [← Matrix.mul_add]
  rw [Matrix.invOf_mul_eq_iff_eq_mul_left]
  simp only [Matrix.add_mul, invOf_mul_self', Matrix.mul_one, add_right_inj]
  simp only [Matrix.mul_assoc]

/-- If matrices `A` and `C + C * V * A⁻¹ * U * C` are invertible, then so is `A + U * C * V`. -/
@[implicit_reducible]
/--
Definition of `invertibleAddMulMul'` / `invertibleAddMulMul'` 的定义

English:
definition invertibleAddMulMul'
  signature: : Invertible (A + U * C * V) where
  body: ⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A
  invOf_mul_self := add_mul_mul_mul_invOf_eq_one' A U C V
  mul_invOf_self := add_mul_mul_mul_invOf_eq_one A U C V

中文:
定义 invertibleAddMulMul'
  签名: : 可逆 (A + U * C * V) where
  定义体: ⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A
  invOf_mul_self := add_mul_mul_mul_invOf_eq_one' A U C V
  mul_invOf_self := add_mul_mul_mul_invOf_eq_one A U C V
-/
def invertibleAddMulMul' : Invertible (A + U * C * V) where
  invOf := ⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A
  invOf_mul_self := add_mul_mul_mul_invOf_eq_one' A U C V
  mul_invOf_self := add_mul_mul_mul_invOf_eq_one A U C V

/--
theorem `invOf_add_mul_mul'` / 定理 `invOf_add_mul_mul'`

English:
theorem invOf_add_mul_mul'
  given: [Invertible (A + U * C * V)]
  proof: by
  let := invertibleAddMulMul' A U C V
  convert! (rfl : ⅟(A + U * C * V) = _)

中文:
定理 invOf_add_mul_mul'
  条件: [可逆 (A + U * C * V)]
  证明: by
  let := invertibleAddMulMul' A U C V
  convert! (rfl : ⅟(A + U * C * V) = _)

Depends on / 依赖: convert, invertibleAddMulMul
-/
theorem invOf_add_mul_mul' [Invertible (A + U * C * V)] :
    ⅟(A + U * C * V) = ⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A := by
  let := invertibleAddMulMul' A U C V
  convert! (rfl : ⅟(A + U * C * V) = _)

end BinomialInverseTheorem

end Ring

end Matrix
