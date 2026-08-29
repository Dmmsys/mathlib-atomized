/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Lu-Ming Zhang
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Invertible
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Nonsingular inverses

In this file, we define an inverse for square matrices of invertible determinant.

For matrices that are not square or not of full rank, there is a more general notion of
pseudoinverses which we do not consider here.

The definition of inverse used in this file is the adjugate divided by the determinant.
We show that dividing the adjugate by `det A` (if possible), giving a matrix `A⁻¹` (`nonsing_inv`),
will result in a multiplicative inverse to `A`.

Note that there are at least three different inverses in mathlib:

* `A⁻¹` (`Inv.inv`): alone, this satisfies no properties, although it is usually used in
  conjunction with `Group` or `GroupWithZero`. On matrices, this is defined to be zero when no
  inverse exists.
* `⅟A` (`invOf`): this is only available in the presence of `[Invertible A]`, which guarantees an
  inverse exists.
* `A⁻¹ʳ`: this is defined on any `MonoidWithZero`, and just like `⁻¹` on matrices, is
  defined to be zero when no inverse exists.

We start by working with `Invertible`, and show the main results:

* `Matrix.invertibleOfDetInvertible`
* `Matrix.detInvertibleOfInvertible`
* `Matrix.isUnit_iff_isUnit_det`
* `Matrix.mul_eq_one_comm`

After this we define `Matrix.inv` and show it matches `⅟A` and `A⁻¹ʳ`.
The rest of the results in the file are then about `A⁻¹`

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

matrix inverse, cramer, cramer's rule, adjugate
-/

@[expose] public section


namespace Matrix

universe u u' v

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

open Matrix Equiv Equiv.Perm Finset
open scoped Ring

/-! ### Matrices are `Invertible` iff their determinants are -/


section Invertible

variable [Fintype n] [DecidableEq n] [CommRing α]
variable (A : Matrix n n α) (B : Matrix n n α)

/-- If `A.det` has a constructive inverse, produce one for `A`. -/
@[instance_reducible]
/--
Definition of `invertibleOfDetInvertible` / `invertibleOfDetInvertible` 的定义

English:
definition invertibleOfDetInvertible
  signature: [Invertible A.det]
  body: ⅟A.det • A.adjugate
  mul_invOf_self := by
    rw [mul_smul_comm]; rw [mul_adjugate]; rw [smul_smul]; rw [invOf_mul_self]; rw [one_smul]
  invOf_mul_self := by
    rw [smul_mul_assoc]; rw [adjugate_mul]; rw [smul_smul]; rw [invOf_mul_self]; rw [one_smul]

中文:
定义 invertibleOfDetInvertible
  签名: [可逆 A.det]
  定义体: ⅟A.det • A.adjugate
  mul_invOf_self := by
    rw [mul_smul_comm]; rw [mul_adjugate]; rw [smul_smul]; rw [invOf_mul_self]; rw [one_smul]
  invOf_mul_self := by
    rw [smul_mul_assoc]; rw [adjugate_mul]; rw [smul_smul]; rw [invOf_mul_self]; rw [one_smul]

Depends on / 依赖: A.adjugate, A.det, adjugate
-/
def invertibleOfDetInvertible [Invertible A.det] : Invertible A where
  invOf := ⅟A.det • A.adjugate
  mul_invOf_self := by
    rw [mul_smul_comm]; rw [mul_adjugate]; rw [smul_smul]; rw [invOf_mul_self]; rw [one_smul]
  invOf_mul_self := by
    rw [smul_mul_assoc]; rw [adjugate_mul]; rw [smul_smul]; rw [invOf_mul_self]; rw [one_smul]

/--
theorem `invOf_eq` / 定理 `invOf_eq`

English:
theorem invOf_eq
  given: [Invertible A.det] [Invertible A]
  statement: ⅟A = ⅟A.det • A.adjugate
  proof: by
  let := invertibleOfDetInvertible A
  convert! (rfl : ⅟A = _)

中文:
定理 invOf_eq
  条件: [可逆 A.det] [可逆 A]
  结论: ⅟A = ⅟A.det • A.adjugate
  证明: by
  let := invertibleOfDetInvertible A
  convert! (rfl : ⅟A = _)

Depends on / 依赖: convert, invertibleOfDetInvertible
-/
theorem invOf_eq [Invertible A.det] [Invertible A] : ⅟A = ⅟A.det • A.adjugate := by
  let := invertibleOfDetInvertible A
  convert! (rfl : ⅟A = _)

/-- `A.det` is invertible if `A` has a left inverse. -/
@[instance_reducible]
/--
Definition of `detInvertibleOfLeftInverse` / `detInvertibleOfLeftInverse` 的定义

English:
definition detInvertibleOfLeftInverse
  signature: (h : B * A = 1)
  body: B.det
  mul_invOf_self := by rw [mul_comm, ← det_mul, h, det_one]
  invOf_mul_self := by rw [← det_mul, h, det_one]

中文:
定义 detInvertibleOfLeftInverse
  签名: (h : B * A = 1)
  定义体: B.det
  mul_invOf_self := by rw [mul_comm, ← det_mul, h, det_one]
  invOf_mul_self := by rw [← det_mul, h, det_one]

Depends on / 依赖: B.det
-/
def detInvertibleOfLeftInverse (h : B * A = 1) : Invertible A.det where
  invOf := B.det
  mul_invOf_self := by rw [mul_comm, ← det_mul, h, det_one]
  invOf_mul_self := by rw [← det_mul, h, det_one]

/-- `A.det` is invertible if `A` has a right inverse. -/
@[instance_reducible]
/--
Definition of `detInvertibleOfRightInverse` / `detInvertibleOfRightInverse` 的定义

English:
definition detInvertibleOfRightInverse
  signature: (h : A * B = 1)
  body: B.det
  mul_invOf_self := by rw [← det_mul, h, det_one]
  invOf_mul_self := by rw [mul_comm, ← det_mul, h, det_one]

中文:
定义 detInvertibleOfRightInverse
  签名: (h : A * B = 1)
  定义体: B.det
  mul_invOf_self := by rw [← det_mul, h, det_one]
  invOf_mul_self := by rw [mul_comm, ← det_mul, h, det_one]

Depends on / 依赖: B.det
-/
def detInvertibleOfRightInverse (h : A * B = 1) : Invertible A.det where
  invOf := B.det
  mul_invOf_self := by rw [← det_mul, h, det_one]
  invOf_mul_self := by rw [mul_comm, ← det_mul, h, det_one]

/-- If `A` has a constructive inverse, produce one for `A.det`. -/
@[instance_reducible]
/--
Definition of `detInvertibleOfInvertible` / `detInvertibleOfInvertible` 的定义

English:
definition detInvertibleOfInvertible
  signature: [Invertible A]
  body: detInvertibleOfLeftInverse A (⅟A) (invOf_mul_self _)

中文:
定义 detInvertibleOfInvertible
  签名: [可逆 A]
  定义体: detInvertibleOfLeftInverse A (⅟A) (invOf_mul_self _)

Depends on / 依赖: detInvertibleOfLeftInverse, invOf_mul_self
-/
def detInvertibleOfInvertible [Invertible A] : Invertible A.det :=
  detInvertibleOfLeftInverse A (⅟A) (invOf_mul_self _)

/--
theorem `det_invOf` / 定理 `det_invOf`

English:
theorem det_invOf
  given: [Invertible A] [Invertible A.det]
  statement: (⅟A).det = ⅟A.det
  proof: by
  let := detInvertibleOfInvertible A
  convert! (rfl : _ = ⅟A.det)

中文:
定理 det_invOf
  条件: [可逆 A] [可逆 A.det]
  结论: (⅟A).det = ⅟A.det
  证明: by
  let := detInvertibleOfInvertible A
  convert! (rfl : _ = ⅟A.det)

Depends on / 依赖: A.det, convert, detInvertibleOfInvertible
-/
theorem det_invOf [Invertible A] [Invertible A.det] : (⅟A).det = ⅟A.det := by
  let := detInvertibleOfInvertible A
  convert! (rfl : _ = ⅟A.det)

/-- Together `Matrix.detInvertibleOfInvertible` and `Matrix.invertibleOfDetInvertible` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
/--
Definition of `invertibleEquivDetInvertible` / `invertibleEquivDetInvertible` 的定义

English:
definition invertibleEquivDetInvertible
  signature: : Invertible A ≃ Invertible A.det where
  body: @detInvertibleOfInvertible _ _ _ _ _ A
  invFun := @invertibleOfDetInvertible _ _ _ _ _ A
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 invertibleEquivDetInvertible
  签名: : 可逆 A ≃ 可逆 A.det where
  定义体: @detInvertibleOfInvertible _ _ _ _ _ A
  invFun := @invertibleOfDetInvertible _ _ _ _ _ A
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

Depends on / 依赖: detInvertibleOfInvertible
-/
def invertibleEquivDetInvertible : Invertible A ≃ Invertible A.det where
  toFun := @detInvertibleOfInvertible _ _ _ _ _ A
  invFun := @invertibleOfDetInvertible _ _ _ _ _ A
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/--
Definition of `unitOfDetInvertible` / `unitOfDetInvertible` 的定义

English:
definition unitOfDetInvertible
  signature: [Invertible A.det]
  body: @unitOfInvertible _ _ A (invertibleOfDetInvertible A)

中文:
定义 unitOfDetInvertible
  签名: [可逆 A.det]
  定义体: @unitOfInvertible _ _ A (invertibleOfDetInvertible A)

Depends on / 依赖: invertibleOfDetInvertible, unitOfInvertible
-/
def unitOfDetInvertible [Invertible A.det] : (Matrix n n α)ˣ :=
  @unitOfInvertible _ _ A (invertibleOfDetInvertible A)

/--
theorem `isUnit_iff_isUnit_det` / 定理 `isUnit_iff_isUnit_det`

English:
theorem isUnit_iff_isUnit_det
  statement: IsUnit A ↔ IsUnit A.det
  proof: by
  simp only [← nonempty_invertible_iff_isUnit, (invertibleEquivDetInvertible A).nonempty_congr]

@[simp]

中文:
定理 isUnit_iff_isUnit_det
  结论: 是单位 A ↔ 是单位 A.det
  证明: by
  simp only [← nonempty_invertible_iff_isUnit, (invertibleEquivDetInvertible A).nonempty_congr]

@[simp]

Depends on / 依赖: invertibleEquivDetInvertible, nonempty_congr, nonempty_invertible_iff_isUnit
-/
theorem isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit A.det := by
  simp only [← nonempty_invertible_iff_isUnit, (invertibleEquivDetInvertible A).nonempty_congr]

@[simp]
/--
theorem `isUnits_det_units` / 定理 `isUnits_det_units`

English:
theorem isUnits_det_units
  given: (A : (Matrix n n α)ˣ)
  statement: IsUnit (A : Matrix n n α).det
  proof: .mp A.isUnit isUnit_iff_isUnit_det _

中文:
定理 isUnits_det_units
  条件: (A : (矩阵 n n α)ˣ)
  结论: 是单位 (A : 矩阵 n n α).det
  证明: .mp A.isUnit isUnit_iff_isUnit_det _

Depends on / 依赖: A.isUnit, isUnit, isUnit_iff_isUnit_det
-/
theorem isUnits_det_units (A : (Matrix n n α)ˣ) : IsUnit (A : Matrix n n α).det :=
.mp A.isUnit isUnit_iff_isUnit_det _



/--
theorem `isUnit_det_of_invertible` / 定理 `isUnit_det_of_invertible`

English:
theorem isUnit_det_of_invertible
  given: [Invertible A]
  statement: IsUnit A.det
  proof: @isUnit_of_invertible _ _ _ (detInvertibleOfInvertible A)

中文:
定理 isUnit_det_of_invertible
  条件: [可逆 A]
  结论: 是单位 A.det
  证明: @isUnit_of_invertible _ _ _ (detInvertibleOfInvertible A)

Depends on / 依赖: detInvertibleOfInvertible, isUnit_of_invertible
-/
theorem isUnit_det_of_invertible [Invertible A] : IsUnit A.det :=
  @isUnit_of_invertible _ _ _ (detInvertibleOfInvertible A)

variable {A B}

/--
theorem `isUnit_det_of_left_inverse` / 定理 `isUnit_det_of_left_inverse`

English:
theorem isUnit_det_of_left_inverse
  given: (h : B * A = 1)
  statement: IsUnit A.det
  proof: @isUnit_of_invertible _ _ _ (detInvertibleOfLeftInverse _ _ h)

中文:
定理 isUnit_det_of_left_inverse
  条件: (h : B * A = 1)
  结论: 是单位 A.det
  证明: @isUnit_of_invertible _ _ _ (detInvertibleOfLeftInverse _ _ h)

Depends on / 依赖: detInvertibleOfLeftInverse, isUnit_of_invertible
-/
theorem isUnit_det_of_left_inverse (h : B * A = 1) : IsUnit A.det :=
  @isUnit_of_invertible _ _ _ (detInvertibleOfLeftInverse _ _ h)

/--
theorem `isUnit_det_of_right_inverse` / 定理 `isUnit_det_of_right_inverse`

English:
theorem isUnit_det_of_right_inverse
  given: (h : A * B = 1)
  statement: IsUnit A.det
  proof: @isUnit_of_invertible _ _ _ (detInvertibleOfRightInverse _ _ h)

中文:
定理 isUnit_det_of_right_inverse
  条件: (h : A * B = 1)
  结论: 是单位 A.det
  证明: @isUnit_of_invertible _ _ _ (detInvertibleOfRightInverse _ _ h)

Depends on / 依赖: detInvertibleOfRightInverse, isUnit_of_invertible
-/
theorem isUnit_det_of_right_inverse (h : A * B = 1) : IsUnit A.det :=
  @isUnit_of_invertible _ _ _ (detInvertibleOfRightInverse _ _ h)

/--
theorem `det_ne_zero_of_left_inverse` / 定理 `det_ne_zero_of_left_inverse`

English:
theorem det_ne_zero_of_left_inverse
  given: [Nontrivial α] (h : B * A = 1)
  statement: A.det != 0
  proof: (isUnit_det_of_left_inverse h).ne_zero

中文:
定理 det_ne_zero_of_left_inverse
  条件: [非平凡 α] (h : B * A = 1)
  结论: A.det != 0
  证明: (isUnit_det_of_left_inverse h).ne_zero

Depends on / 依赖: isUnit_det_of_left_inverse, ne_zero
-/
theorem det_ne_zero_of_left_inverse [Nontrivial α] (h : B * A = 1) : A.det != 0 :=
  (isUnit_det_of_left_inverse h).ne_zero

/--
theorem `det_ne_zero_of_right_inverse` / 定理 `det_ne_zero_of_right_inverse`

English:
theorem det_ne_zero_of_right_inverse
  given: [Nontrivial α] (h : A * B = 1)
  statement: A.det != 0
  proof: (isUnit_det_of_right_inverse h).ne_zero

中文:
定理 det_ne_zero_of_right_inverse
  条件: [非平凡 α] (h : A * B = 1)
  结论: A.det != 0
  证明: (isUnit_det_of_right_inverse h).ne_zero

Depends on / 依赖: isUnit_det_of_right_inverse, ne_zero
-/
theorem det_ne_zero_of_right_inverse [Nontrivial α] (h : A * B = 1) : A.det != 0 :=
  (isUnit_det_of_right_inverse h).ne_zero

end Invertible

section Inv

variable [Fintype n] [DecidableEq n] [CommRing α]
variable (A : Matrix n n α) (B : Matrix n n α)

/--
theorem `isUnit_det_transpose` / 定理 `isUnit_det_transpose`

English:
theorem isUnit_det_transpose
  given: (h : IsUnit A.det)
  statement: IsUnit Aᵀ.det
  proof: by
  rw [det_transpose]
  exact h

中文:
定理 isUnit_det_transpose
  条件: (h : 是单位 A.det)
  结论: 是单位 Aᵀ.det
  证明: by
  rw [det_transpose]
  exact h

Depends on / 依赖: det_transpose
-/
theorem isUnit_det_transpose (h : IsUnit A.det) : IsUnit Aᵀ.det := by
  rw [det_transpose]
  exact h

/-! ### A noncomputable `Inv` instance -/


/--
Instance `inv` / 实例 `inv`

English:
instance inv
  signature: : Inv (Matrix n n α)
  body: ⟨fun A => A.det⁻¹ʳ • A.adjugate⟩

中文:
实例 inv
  签名: : 取逆 (矩阵 n n α)
  定义体: ⟨fun A => A.det⁻¹ʳ • A.adjugate⟩

Depends on / 依赖: A.adjugate, A.det, adjugate
-/
noncomputable instance inv : Inv (Matrix n n α) :=
  ⟨fun A => A.det⁻¹ʳ • A.adjugate⟩

/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  given: (A : Matrix n n α)
  statement: A⁻¹ = A.det⁻¹ʳ • A.adjugate
  proof: rfl

中文:
定理 inv_def
  条件: (A : 矩阵 n n α)
  结论: A⁻¹ = A.det⁻¹ʳ • A.adjugate
  证明: rfl
-/
theorem inv_def (A : Matrix n n α) : A⁻¹ = A.det⁻¹ʳ • A.adjugate :=
  rfl

/--
theorem `nonsing_inv_apply_not_isUnit` / 定理 `nonsing_inv_apply_not_isUnit`

English:
theorem nonsing_inv_apply_not_isUnit
  given: (h : ¬IsUnit A.det)
  statement: A⁻¹ = 0
  proof: by
  rw [inv_def]; rw [Ring.inverse_non_unit _ h]; rw [zero_smul]

中文:
定理 nonsing_inv_apply_not_isUnit
  条件: (h : ¬是单位 A.det)
  结论: A⁻¹ = 0
  证明: by
  rw [inv_def]; rw [Ring.inverse_non_unit _ h]; rw [zero_smul]

Depends on / 依赖: Ring.inverse_non_unit, inv_def, inverse_non_unit, zero_smul
-/
theorem nonsing_inv_apply_not_isUnit (h : ¬IsUnit A.det) : A⁻¹ = 0 := by
  rw [inv_def]; rw [Ring.inverse_non_unit _ h]; rw [zero_smul]

/--
theorem `nonsing_inv_apply` / 定理 `nonsing_inv_apply`

English:
theorem nonsing_inv_apply
  given: (h : IsUnit A.det)
  statement: A⁻¹ = (↑h.unit⁻¹ : α) • A.adjugate
  proof: by
  rw [inv_def]; rw [← Ring.inverse_unit h.unit]; rw [IsUnit.unit_spec]

中文:
定理 nonsing_inv_apply
  条件: (h : 是单位 A.det)
  结论: A⁻¹ = (↑h.unit⁻¹ : α) • A.adjugate
  证明: by
  rw [inv_def]; rw [← Ring.inverse_unit h.unit]; rw [IsUnit.unit_spec]

Depends on / 依赖: IsUnit, IsUnit.unit_spec, Ring.inverse_unit, h.unit, inv_def, inverse_unit, unit_spec
-/
theorem nonsing_inv_apply (h : IsUnit A.det) : A⁻¹ = (↑h.unit⁻¹ : α) • A.adjugate := by
  rw [inv_def]; rw [← Ring.inverse_unit h.unit]; rw [IsUnit.unit_spec]

/-- The nonsingular inverse is the same as `invOf` when `A` is invertible. -/
@[simp]
/--
theorem `invOf_eq_nonsing_inv` / 定理 `invOf_eq_nonsing_inv`

English:
theorem invOf_eq_nonsing_inv
  given: [Invertible A]
  statement: ⅟A = A⁻¹
  proof: by
  let := detInvertibleOfInvertible A
  rw [inv_def]; rw [Ring.inverse_invertible]; rw [invOf_eq]

中文:
定理 invOf_eq_nonsing_inv
  条件: [可逆 A]
  结论: ⅟A = A⁻¹
  证明: by
  let := detInvertibleOfInvertible A
  rw [inv_def]; rw [Ring.inverse_invertible]; rw [invOf_eq]

Depends on / 依赖: Ring.inverse_invertible, detInvertibleOfInvertible, invOf_eq, inv_def, inverse_invertible
-/
theorem invOf_eq_nonsing_inv [Invertible A] : ⅟A = A⁻¹ := by
  let := detInvertibleOfInvertible A
  rw [inv_def]; rw [Ring.inverse_invertible]; rw [invOf_eq]

/-- Coercing the result of `Units.instInv` is the same as coercing first and applying the
nonsingular inverse. -/
@[simp, norm_cast]
/--
theorem `coe_units_inv` / 定理 `coe_units_inv`

English:
theorem coe_units_inv
  given: (A : (Matrix n n α)ˣ)
  statement: ↑A⁻¹ = (A⁻¹ : Matrix n n α)
  proof: by
  let := A.invertible
  rw [← invOf_eq_nonsing_inv]; rw [invOf_units]

中文:
定理 coe_units_inv
  条件: (A : (矩阵 n n α)ˣ)
  结论: ↑A⁻¹ = (A⁻¹ : 矩阵 n n α)
  证明: by
  let := A.invertible
  rw [← invOf_eq_nonsing_inv]; rw [invOf_units]

Depends on / 依赖: A.invertible, invOf_eq_nonsing_inv, invOf_units, invertible
-/
theorem coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ : Matrix n n α) := by
  let := A.invertible
  rw [← invOf_eq_nonsing_inv]; rw [invOf_units]

/--
theorem `nonsing_inv_eq_ringInverse` / 定理 `nonsing_inv_eq_ringInverse`

English:
theorem nonsing_inv_eq_ringInverse
  statement: A⁻¹ = A⁻¹ʳ
  proof: by
  by_cases h_det : IsUnit A.det
  · cases (A.isUnit_iff_isUnit_det.mpr h_det).nonempty_invertible
    rw [← invOf_eq_nonsing_inv]; rw [Ring.inverse_invertible]
  · have h := mt A.isUnit_iff_isUnit_det.mp h_det
    rw [Ring.inverse_non_unit _ h]; rw [nonsing_inv_apply_not_isUnit A h_det]

中文:
定理 nonsing_inv_eq_ringInverse
  结论: A⁻¹ = A⁻¹ʳ
  证明: by
  by_cases h_det : IsUnit A.det
  · cases (A.isUnit_iff_isUnit_det.mpr h_det).nonempty_invertible
    rw [← invOf_eq_nonsing_inv]; rw [Ring.inverse_invertible]
  · have h := mt A.isUnit_iff_isUnit_det.mp h_det
    rw [Ring.inverse_non_unit _ h]; rw [nonsing_inv_apply_not_isUnit A h_det]

Depends on / 依赖: A.det, A.isUnit_iff_isUnit_det.mp, A.isUnit_iff_isUnit_det.mpr, IsUnit, Ring.inverse_invertible, Ring.inverse_non_unit, h_det, invOf_eq_nonsing_inv, inverse_invertible, inverse_non_unit, isUnit_iff_isUnit_det, nonempty_invertible, nonsing_inv_apply_not_isUnit
-/
theorem nonsing_inv_eq_ringInverse : A⁻¹ = A⁻¹ʳ := by
  by_cases h_det : IsUnit A.det
  · cases (A.isUnit_iff_isUnit_det.mpr h_det).nonempty_invertible
    rw [← invOf_eq_nonsing_inv]; rw [Ring.inverse_invertible]
  · have h := mt A.isUnit_iff_isUnit_det.mp h_det
    rw [Ring.inverse_non_unit _ h]; rw [nonsing_inv_apply_not_isUnit A h_det]

/--
theorem `transpose_nonsing_inv` / 定理 `transpose_nonsing_inv`

English:
theorem transpose_nonsing_inv
  statement: A⁻¹ᵀ = Aᵀ⁻¹
  proof: by
  rw [inv_def]; rw [inv_def]; rw [transpose_smul]; rw [det_transpose]; rw [adjugate_transpose]

中文:
定理 transpose_nonsing_inv
  结论: A⁻¹ᵀ = Aᵀ⁻¹
  证明: by
  rw [inv_def]; rw [inv_def]; rw [transpose_smul]; rw [det_transpose]; rw [adjugate_transpose]

Depends on / 依赖: adjugate_transpose, det_transpose, inv_def, transpose_smul
-/
theorem transpose_nonsing_inv : A⁻¹ᵀ = Aᵀ⁻¹ := by
  rw [inv_def]; rw [inv_def]; rw [transpose_smul]; rw [det_transpose]; rw [adjugate_transpose]

/--
theorem `conjTranspose_nonsing_inv` / 定理 `conjTranspose_nonsing_inv`

English:
theorem conjTranspose_nonsing_inv
  given: [StarRing α]
  statement: A⁻¹ᴴ = Aᴴ⁻¹
  proof: by
  rw [inv_def]; rw [inv_def]; rw [conjTranspose_smul]; rw [det_conjTranspose]; rw [adjugate_conjTranspose]; rw [Ring.inverse_star]

中文:
定理 conjTranspose_nonsing_inv
  条件: [对合环 α]
  结论: A⁻¹ᴴ = Aᴴ⁻¹
  证明: by
  rw [inv_def]; rw [inv_def]; rw [conjTranspose_smul]; rw [det_conjTranspose]; rw [adjugate_conjTranspose]; rw [Ring.inverse_star]

Depends on / 依赖: Ring.inverse_star, adjugate_conjTranspose, conjTranspose_smul, det_conjTranspose, inv_def, inverse_star
-/
theorem conjTranspose_nonsing_inv [StarRing α] : A⁻¹ᴴ = Aᴴ⁻¹ := by
  rw [inv_def]; rw [inv_def]; rw [conjTranspose_smul]; rw [det_conjTranspose]; rw [adjugate_conjTranspose]; rw [Ring.inverse_star]

/-- The `nonsing_inv` of `A` is a right inverse. -/
@[simp]
/--
theorem `mul_nonsing_inv` / 定理 `mul_nonsing_inv`

English:
theorem mul_nonsing_inv
  given: (h : IsUnit A.det)
  statement: A * A⁻¹ = 1
  proof: by
  cases (A.isUnit_iff_isUnit_det.mpr h).nonempty_invertible
  rw [← invOf_eq_nonsing_inv]; rw [mul_invOf_self]

中文:
定理 mul_nonsing_inv
  条件: (h : 是单位 A.det)
  结论: A * A⁻¹ = 1
  证明: by
  cases (A.isUnit_iff_isUnit_det.mpr h).nonempty_invertible
  rw [← invOf_eq_nonsing_inv]; rw [mul_invOf_self]

Depends on / 依赖: A.isUnit_iff_isUnit_det.mpr, invOf_eq_nonsing_inv, isUnit_iff_isUnit_det, mul_invOf_self, nonempty_invertible
-/
theorem mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1 := by
  cases (A.isUnit_iff_isUnit_det.mpr h).nonempty_invertible
  rw [← invOf_eq_nonsing_inv]; rw [mul_invOf_self]

/-- The nonsingular inverse of `A` is a left inverse. -/
@[simp]
/--
theorem `nonsing_inv_mul` / 定理 `nonsing_inv_mul`

English:
theorem nonsing_inv_mul
  given: (h : IsUnit A.det)
  statement: A⁻¹ * A = 1
  proof: by
  cases (A.isUnit_iff_isUnit_det.mpr h).nonempty_invertible
  rw [← invOf_eq_nonsing_inv]; rw [invOf_mul_self]

中文:
定理 nonsing_inv_mul
  条件: (h : 是单位 A.det)
  结论: A⁻¹ * A = 1
  证明: by
  cases (A.isUnit_iff_isUnit_det.mpr h).nonempty_invertible
  rw [← invOf_eq_nonsing_inv]; rw [invOf_mul_self]

Depends on / 依赖: A.isUnit_iff_isUnit_det.mpr, invOf_eq_nonsing_inv, invOf_mul_self, isUnit_iff_isUnit_det, nonempty_invertible
-/
theorem nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1 := by
  cases (A.isUnit_iff_isUnit_det.mpr h).nonempty_invertible
  rw [← invOf_eq_nonsing_inv]; rw [invOf_mul_self]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Invertible
  signature: A] : Invertible A⁻¹
  body: by
  rw [← invOf_eq_nonsing_inv]
  infer_instance

@[simp]

中文:
实例 [可逆
  签名: A] : 可逆 A⁻¹
  定义体: by
  rw [← invOf_eq_nonsing_inv]
  infer_instance

@[simp]

Depends on / 依赖: infer_instance, invOf_eq_nonsing_inv
-/
instance [Invertible A] : Invertible A⁻¹ := by
  rw [← invOf_eq_nonsing_inv]
  infer_instance

@[simp]
/--
theorem `inv_inv_of_invertible` / 定理 `inv_inv_of_invertible`

English:
theorem inv_inv_of_invertible
  given: [Invertible A]
  statement: A⁻¹⁻¹ = A
  proof: by
  simp only [← invOf_eq_nonsing_inv, invOf_invOf]

@[simp]

中文:
定理 inv_inv_of_invertible
  条件: [可逆 A]
  结论: A⁻¹⁻¹ = A
  证明: by
  simp only [← invOf_eq_nonsing_inv, invOf_invOf]

@[simp]

Depends on / 依赖: invOf_eq_nonsing_inv, invOf_invOf
-/
theorem inv_inv_of_invertible [Invertible A] : A⁻¹⁻¹ = A := by
  simp only [← invOf_eq_nonsing_inv, invOf_invOf]

@[simp]
/--
theorem `mul_nonsing_inv_cancel_right` / 定理 `mul_nonsing_inv_cancel_right`

English:
theorem mul_nonsing_inv_cancel_right
  given: (B : Matrix m n α) (h : IsUnit A.det)
  statement: B * A * A⁻¹ = B
  proof: by
  simp [Matrix.mul_assoc, mul_nonsing_inv A h]

@[simp]

中文:
定理 mul_nonsing_inv_cancel_right
  条件: (B : 矩阵 m n α) (h : 是单位 A.det)
  结论: B * A * A⁻¹ = B
  证明: by
  simp [Matrix.mul_assoc, mul_nonsing_inv A h]

@[simp]

Depends on / 依赖: Matrix, Matrix.mul_assoc, mul_assoc, mul_nonsing_inv
-/
theorem mul_nonsing_inv_cancel_right (B : Matrix m n α) (h : IsUnit A.det) : B * A * A⁻¹ = B := by
  simp [Matrix.mul_assoc, mul_nonsing_inv A h]

@[simp]
/--
theorem `mul_nonsing_inv_cancel_left` / 定理 `mul_nonsing_inv_cancel_left`

English:
theorem mul_nonsing_inv_cancel_left
  given: (B : Matrix n m α) (h : IsUnit A.det)
  statement: A * (A⁻¹ * B) = B
  proof: by
  simp [← Matrix.mul_assoc, mul_nonsing_inv A h]

@[simp]

中文:
定理 mul_nonsing_inv_cancel_left
  条件: (B : 矩阵 n m α) (h : 是单位 A.det)
  结论: A * (A⁻¹ * B) = B
  证明: by
  simp [← Matrix.mul_assoc, mul_nonsing_inv A h]

@[simp]

Depends on / 依赖: Matrix, Matrix.mul_assoc, mul_assoc, mul_nonsing_inv
-/
theorem mul_nonsing_inv_cancel_left (B : Matrix n m α) (h : IsUnit A.det) : A * (A⁻¹ * B) = B := by
  simp [← Matrix.mul_assoc, mul_nonsing_inv A h]

@[simp]
/--
theorem `nonsing_inv_mul_cancel_right` / 定理 `nonsing_inv_mul_cancel_right`

English:
theorem nonsing_inv_mul_cancel_right
  given: (B : Matrix m n α) (h : IsUnit A.det)
  statement: B * A⁻¹ * A = B
  proof: by
  simp [Matrix.mul_assoc, nonsing_inv_mul A h]

@[simp]

中文:
定理 nonsing_inv_mul_cancel_right
  条件: (B : 矩阵 m n α) (h : 是单位 A.det)
  结论: B * A⁻¹ * A = B
  证明: by
  simp [Matrix.mul_assoc, nonsing_inv_mul A h]

@[simp]

Depends on / 依赖: Matrix, Matrix.mul_assoc, mul_assoc, nonsing_inv_mul
-/
theorem nonsing_inv_mul_cancel_right (B : Matrix m n α) (h : IsUnit A.det) : B * A⁻¹ * A = B := by
  simp [Matrix.mul_assoc, nonsing_inv_mul A h]

@[simp]
/--
theorem `nonsing_inv_mul_cancel_left` / 定理 `nonsing_inv_mul_cancel_left`

English:
theorem nonsing_inv_mul_cancel_left
  given: (B : Matrix n m α) (h : IsUnit A.det)
  statement: A⁻¹ * (A * B) = B
  proof: by
  simp [← Matrix.mul_assoc, nonsing_inv_mul A h]

@[simp]

中文:
定理 nonsing_inv_mul_cancel_left
  条件: (B : 矩阵 n m α) (h : 是单位 A.det)
  结论: A⁻¹ * (A * B) = B
  证明: by
  simp [← Matrix.mul_assoc, nonsing_inv_mul A h]

@[simp]

Depends on / 依赖: Matrix, Matrix.mul_assoc, mul_assoc, nonsing_inv_mul
-/
theorem nonsing_inv_mul_cancel_left (B : Matrix n m α) (h : IsUnit A.det) : A⁻¹ * (A * B) = B := by
  simp [← Matrix.mul_assoc, nonsing_inv_mul A h]

@[simp]
/--
theorem `mul_inv_of_invertible` / 定理 `mul_inv_of_invertible`

English:
theorem mul_inv_of_invertible
  given: [Invertible A]
  statement: A * A⁻¹ = 1
  proof: mul_nonsing_inv A (isUnit_det_of_invertible A)

@[simp]

中文:
定理 mul_inv_of_invertible
  条件: [可逆 A]
  结论: A * A⁻¹ = 1
  证明: mul_nonsing_inv A (isUnit_det_of_invertible A)

@[simp]

Depends on / 依赖: isUnit_det_of_invertible, mul_nonsing_inv
-/
theorem mul_inv_of_invertible [Invertible A] : A * A⁻¹ = 1 :=
  mul_nonsing_inv A (isUnit_det_of_invertible A)

@[simp]
/--
theorem `inv_mul_of_invertible` / 定理 `inv_mul_of_invertible`

English:
theorem inv_mul_of_invertible
  given: [Invertible A]
  statement: A⁻¹ * A = 1
  proof: nonsing_inv_mul A (isUnit_det_of_invertible A)

@[simp]

中文:
定理 inv_mul_of_invertible
  条件: [可逆 A]
  结论: A⁻¹ * A = 1
  证明: nonsing_inv_mul A (isUnit_det_of_invertible A)

@[simp]

Depends on / 依赖: isUnit_det_of_invertible, nonsing_inv_mul
-/
theorem inv_mul_of_invertible [Invertible A] : A⁻¹ * A = 1 :=
  nonsing_inv_mul A (isUnit_det_of_invertible A)

@[simp]
/--
theorem `mul_inv_cancel_right_of_invertible` / 定理 `mul_inv_cancel_right_of_invertible`

English:
theorem mul_inv_cancel_right_of_invertible
  given: (B : Matrix m n α) [Invertible A]
  statement: B * A * A⁻¹ = B
  proof: mul_nonsing_inv_cancel_right A B (isUnit_det_of_invertible A)

@[simp]

中文:
定理 mul_inv_cancel_right_of_invertible
  条件: (B : 矩阵 m n α) [可逆 A]
  结论: B * A * A⁻¹ = B
  证明: mul_nonsing_inv_cancel_right A B (isUnit_det_of_invertible A)

@[simp]

Depends on / 依赖: isUnit_det_of_invertible, mul_nonsing_inv_cancel_right
-/
theorem mul_inv_cancel_right_of_invertible (B : Matrix m n α) [Invertible A] : B * A * A⁻¹ = B :=
  mul_nonsing_inv_cancel_right A B (isUnit_det_of_invertible A)

@[simp]
/--
theorem `mul_inv_cancel_left_of_invertible` / 定理 `mul_inv_cancel_left_of_invertible`

English:
theorem mul_inv_cancel_left_of_invertible
  given: (B : Matrix n m α) [Invertible A]
  statement: A * (A⁻¹ * B) = B
  proof: mul_nonsing_inv_cancel_left A B (isUnit_det_of_invertible A)

@[simp]

中文:
定理 mul_inv_cancel_left_of_invertible
  条件: (B : 矩阵 n m α) [可逆 A]
  结论: A * (A⁻¹ * B) = B
  证明: mul_nonsing_inv_cancel_left A B (isUnit_det_of_invertible A)

@[simp]

Depends on / 依赖: isUnit_det_of_invertible, mul_nonsing_inv_cancel_left
-/
theorem mul_inv_cancel_left_of_invertible (B : Matrix n m α) [Invertible A] : A * (A⁻¹ * B) = B :=
  mul_nonsing_inv_cancel_left A B (isUnit_det_of_invertible A)

@[simp]
/--
theorem `inv_mul_cancel_right_of_invertible` / 定理 `inv_mul_cancel_right_of_invertible`

English:
theorem inv_mul_cancel_right_of_invertible
  given: (B : Matrix m n α) [Invertible A]
  statement: B * A⁻¹ * A = B
  proof: nonsing_inv_mul_cancel_right A B (isUnit_det_of_invertible A)

@[simp]

中文:
定理 inv_mul_cancel_right_of_invertible
  条件: (B : 矩阵 m n α) [可逆 A]
  结论: B * A⁻¹ * A = B
  证明: nonsing_inv_mul_cancel_right A B (isUnit_det_of_invertible A)

@[simp]

Depends on / 依赖: isUnit_det_of_invertible, nonsing_inv_mul_cancel_right
-/
theorem inv_mul_cancel_right_of_invertible (B : Matrix m n α) [Invertible A] : B * A⁻¹ * A = B :=
  nonsing_inv_mul_cancel_right A B (isUnit_det_of_invertible A)

@[simp]
/--
theorem `inv_mul_cancel_left_of_invertible` / 定理 `inv_mul_cancel_left_of_invertible`

English:
theorem inv_mul_cancel_left_of_invertible
  given: (B : Matrix n m α) [Invertible A]
  statement: A⁻¹ * (A * B) = B
  proof: nonsing_inv_mul_cancel_left A B (isUnit_det_of_invertible A)

中文:
定理 inv_mul_cancel_left_of_invertible
  条件: (B : 矩阵 n m α) [可逆 A]
  结论: A⁻¹ * (A * B) = B
  证明: nonsing_inv_mul_cancel_left A B (isUnit_det_of_invertible A)

Depends on / 依赖: isUnit_det_of_invertible, nonsing_inv_mul_cancel_left
-/
theorem inv_mul_cancel_left_of_invertible (B : Matrix n m α) [Invertible A] : A⁻¹ * (A * B) = B :=
  nonsing_inv_mul_cancel_left A B (isUnit_det_of_invertible A)

/--
theorem `inv_mul_eq_iff_eq_mul_of_invertible` / 定理 `inv_mul_eq_iff_eq_mul_of_invertible`

English:
theorem inv_mul_eq_iff_eq_mul_of_invertible
  given: (A : Matrix n n α) [Invertible A] (B C : Matrix n m α)
  proof: ⟨fun h => by rw [← h, mul_inv_cancel_left_of_invertible],
   fun h => by rw [h, inv_mul_cancel_left_of_invertible]⟩

中文:
定理 inv_mul_eq_iff_eq_mul_of_invertible
  条件: (A : 矩阵 n n α) [可逆 A] (B C : 矩阵 n m α)
  证明: ⟨fun h => by rw [← h, mul_inv_cancel_left_of_invertible],
   fun h => by rw [h, inv_mul_cancel_left_of_invertible]⟩

Depends on / 依赖: inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible
-/
theorem inv_mul_eq_iff_eq_mul_of_invertible (A : Matrix n n α) [Invertible A] (B C : Matrix n m α) :
    A⁻¹ * B = C ↔ B = A * C :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left_of_invertible],
   fun h => by rw [h, inv_mul_cancel_left_of_invertible]⟩

/--
theorem `mul_inv_eq_iff_eq_mul_of_invertible` / 定理 `mul_inv_eq_iff_eq_mul_of_invertible`

English:
theorem mul_inv_eq_iff_eq_mul_of_invertible
  given: (A : Matrix n n α) [Invertible A] (B C : Matrix m n α)
  proof: ⟨fun h => by rw [← h, inv_mul_cancel_right_of_invertible],
   fun h => by rw [h, mul_inv_cancel_right_of_invertible]⟩

中文:
定理 mul_inv_eq_iff_eq_mul_of_invertible
  条件: (A : 矩阵 n n α) [可逆 A] (B C : 矩阵 m n α)
  证明: ⟨fun h => by rw [← h, inv_mul_cancel_right_of_invertible],
   fun h => by rw [h, mul_inv_cancel_right_of_invertible]⟩

Depends on / 依赖: inv_mul_cancel_right_of_invertible, mul_inv_cancel_right_of_invertible
-/
theorem mul_inv_eq_iff_eq_mul_of_invertible (A : Matrix n n α) [Invertible A] (B C : Matrix m n α) :
    B * A⁻¹ = C ↔ B = C * A :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right_of_invertible],
   fun h => by rw [h, mul_inv_cancel_right_of_invertible]⟩

/--
lemma `inv_mulVec_eq_vec` / 引理 `inv_mulVec_eq_vec`

English:
lemma inv_mulVec_eq_vec
  statement: {A : Matrix n n α} [Invertible A]
  proof: by
  rw [hM]; rw [Matrix.mulVec_mulVec]; rw [Matrix.inv_mul_of_invertible]; rw [Matrix.one_mulVec]

中文:
引理 inv_mulVec_eq_vec
  结论: {A : 矩阵 n n α} [可逆 A]
  证明: by
  rw [hM]; rw [Matrix.mulVec_mulVec]; rw [Matrix.inv_mul_of_invertible]; rw [Matrix.one_mulVec]

Depends on / 依赖: Matrix, Matrix.inv_mul_of_invertible, Matrix.mulVec_mulVec, Matrix.one_mulVec, inv_mul_of_invertible, mulVec_mulVec, one_mulVec
-/
lemma inv_mulVec_eq_vec {A : Matrix n n α} [Invertible A]
    {u v : n -> α} (hM : u = A.mulVec v) : A⁻¹.mulVec u = v := by
  rw [hM]; rw [Matrix.mulVec_mulVec]; rw [Matrix.inv_mul_of_invertible]; rw [Matrix.one_mulVec]

/--
lemma `mul_right_injective_of_invertible` / 引理 `mul_right_injective_of_invertible`

English:
lemma mul_right_injective_of_invertible
  given: [Invertible A]
  proof: fun _ _ h => by simpa only [inv_mul_cancel_left_of_invertible] using congr_arg (A⁻¹ * ·) h

中文:
引理 mul_right_injective_of_invertible
  条件: [可逆 A]
  证明: fun _ _ h => by simpa only [inv_mul_cancel_left_of_invertible] using congr_arg (A⁻¹ * ·) h

Depends on / 依赖: congr_arg, inv_mul_cancel_left_of_invertible
-/
lemma mul_right_injective_of_invertible [Invertible A] :
    Function.Injective (fun (x : Matrix n m α) => A * x) :=
  fun _ _ h => by simpa only [inv_mul_cancel_left_of_invertible] using congr_arg (A⁻¹ * ·) h

/--
lemma `mul_left_injective_of_invertible` / 引理 `mul_left_injective_of_invertible`

English:
lemma mul_left_injective_of_invertible
  given: [Invertible A]
  proof: fun a x hax => by simpa only [mul_inv_cancel_right_of_invertible] using congr_arg (· * A⁻¹) hax

中文:
引理 mul_left_injective_of_invertible
  条件: [可逆 A]
  证明: fun a x hax => by simpa only [mul_inv_cancel_right_of_invertible] using congr_arg (· * A⁻¹) hax

Depends on / 依赖: congr_arg, mul_inv_cancel_right_of_invertible
-/
lemma mul_left_injective_of_invertible [Invertible A] :
    Function.Injective (fun (x : Matrix m n α) => x * A) :=
  fun a x hax => by simpa only [mul_inv_cancel_right_of_invertible] using congr_arg (· * A⁻¹) hax

/--
lemma `mul_right_inj_of_invertible` / 引理 `mul_right_inj_of_invertible`

English:
lemma mul_right_inj_of_invertible
  given: [Invertible A] {x y : Matrix n m α}
  statement: A * x = A * y ↔ x = y
  proof: (mul_right_injective_of_invertible A).eq_iff

中文:
引理 mul_right_inj_of_invertible
  条件: [可逆 A] {x y : 矩阵 n m α}
  结论: A * x = A * y ↔ x = y
  证明: (mul_right_injective_of_invertible A).eq_iff

Depends on / 依赖: eq_iff, mul_right_injective_of_invertible
-/
lemma mul_right_inj_of_invertible [Invertible A] {x y : Matrix n m α} : A * x = A * y ↔ x = y :=
  (mul_right_injective_of_invertible A).eq_iff

/--
lemma `mul_left_inj_of_invertible` / 引理 `mul_left_inj_of_invertible`

English:
lemma mul_left_inj_of_invertible
  given: [Invertible A] {x y : Matrix m n α}
  statement: x * A = y * A ↔ x = y
  proof: (mul_left_injective_of_invertible A).eq_iff

中文:
引理 mul_left_inj_of_invertible
  条件: [可逆 A] {x y : 矩阵 m n α}
  结论: x * A = y * A ↔ x = y
  证明: (mul_left_injective_of_invertible A).eq_iff

Depends on / 依赖: eq_iff, mul_left_injective_of_invertible
-/
lemma mul_left_inj_of_invertible [Invertible A] {x y : Matrix m n α} : x * A = y * A ↔ x = y :=
  (mul_left_injective_of_invertible A).eq_iff

/--
lemma `IsSymm.inv` / 引理 `IsSymm.inv`

English:
lemma IsSymm.inv
  given: {A : Matrix n n α} (hA : A.IsSymm)
  statement: A⁻¹.IsSymm
  proof: hA.adjugate.smul _

中文:
引理 是Symm.inv
  条件: {A : 矩阵 n n α} (hA : A.是Symm)
  结论: A⁻¹.是Symm
  证明: hA.adjugate.smul _

Depends on / 依赖: adjugate, hA.adjugate.smul
-/
lemma IsSymm.inv {A : Matrix n n α} (hA : A.IsSymm) : A⁻¹.IsSymm :=
  hA.adjugate.smul _

end Inv

section InjectiveMul
variable [Fintype n] [Fintype m] [DecidableEq m] [CommRing α]

/--
lemma `mul_left_injective_of_inv` / 引理 `mul_left_injective_of_inv`

English:
lemma mul_left_injective_of_inv
  given: (A : Matrix m n α) (B : Matrix n m α) (h : A * B = 1)
  proof: fun _ _ g => by
  simpa only [Matrix.mul_assoc, Matrix.mul_one, h] using congr_arg (· * B) g

中文:
引理 mul_left_injective_of_inv
  条件: (A : 矩阵 m n α) (B : 矩阵 n m α) (h : A * B = 1)
  证明: fun _ _ g => by
  simpa only [Matrix.mul_assoc, Matrix.mul_one, h] using congr_arg (· * B) g

Depends on / 依赖: Matrix, Matrix.mul_assoc, Matrix.mul_one, congr_arg, mul_assoc, mul_one
-/
lemma mul_left_injective_of_inv (A : Matrix m n α) (B : Matrix n m α) (h : A * B = 1) :
    Function.Injective (fun x : Matrix l m α => x * A) := fun _ _ g => by
  simpa only [Matrix.mul_assoc, Matrix.mul_one, h] using congr_arg (· * B) g

/--
lemma `mul_right_injective_of_inv` / 引理 `mul_right_injective_of_inv`

English:
lemma mul_right_injective_of_inv
  given: (A : Matrix m n α) (B : Matrix n m α) (h : A * B = 1)
  proof: fun _ _ g => by simpa only [← Matrix.mul_assoc, Matrix.one_mul, h] using congr_arg (A * ·) g

中文:
引理 mul_right_injective_of_inv
  条件: (A : 矩阵 m n α) (B : 矩阵 n m α) (h : A * B = 1)
  证明: fun _ _ g => by simpa only [← Matrix.mul_assoc, Matrix.one_mul, h] using congr_arg (A * ·) g

Depends on / 依赖: Matrix, Matrix.mul_assoc, Matrix.one_mul, congr_arg, mul_assoc, one_mul
-/
lemma mul_right_injective_of_inv (A : Matrix m n α) (B : Matrix n m α) (h : A * B = 1) :
    Function.Injective (fun x : Matrix m l α => B * x) :=
  fun _ _ g => by simpa only [← Matrix.mul_assoc, Matrix.one_mul, h] using congr_arg (A * ·) g

end InjectiveMul

section vecMul

section Semiring

variable {R : Type*} [Semiring R]

/--
theorem `vecMul_surjective_iff_exists_left_inverse` / 定理 `vecMul_surjective_iff_exists_left_inverse`

English:
theorem vecMul_surjective_iff_exists_left_inverse
  proof: by
  cases nonempty_fintype n
  refine ⟨fun h => ?_, fun ⟨B, hBA⟩ y => ⟨y ᵥ* B, by simp [hBA]⟩⟩
  choose rows hrows using (h <| Pi.single · 1)
  refine ⟨Matrix.of rows, Matrix.ext fun i j => ?_⟩
  rw [mul_apply_eq_vecMul]; rw [one_eq_pi_single]; rw [← hrows]
  rfl

中文:
定理 vecMul_surjective_iff_存在_left_inverse
  证明: by
  cases nonempty_fintype n
  refine ⟨fun h => ?_, fun ⟨B, hBA⟩ y => ⟨y ᵥ* B, by simp [hBA]⟩⟩
  choose rows hrows using (h <| Pi.single · 1)
  refine ⟨Matrix.of rows, Matrix.ext fun i j => ?_⟩
  rw [mul_apply_eq_vecMul]; rw [one_eq_pi_single]; rw [← hrows]
  rfl

Depends on / 依赖: Matrix, Matrix.ext, Matrix.of, Pi.single, mul_apply_eq_vecMul, nonempty_fintype, one_eq_pi_single, single
-/
theorem vecMul_surjective_iff_exists_left_inverse
    [DecidableEq n] [Fintype m] [Finite n] {A : Matrix m n R} :
    Function.Surjective A.vecMul ↔ exists B : Matrix n m R, B * A = 1 := by
  cases nonempty_fintype n
  refine ⟨fun h => ?_, fun ⟨B, hBA⟩ y => ⟨y ᵥ* B, by simp [hBA]⟩⟩
  choose rows hrows using (h <| Pi.single · 1)
  refine ⟨Matrix.of rows, Matrix.ext fun i j => ?_⟩
  rw [mul_apply_eq_vecMul]; rw [one_eq_pi_single]; rw [← hrows]
  rfl

/--
theorem `mulVec_surjective_iff_exists_right_inverse` / 定理 `mulVec_surjective_iff_exists_right_inverse`

English:
theorem mulVec_surjective_iff_exists_right_inverse
  proof: by
  cases nonempty_fintype m
  refine ⟨fun h => ?_, fun ⟨B, hBA⟩ y => ⟨B *ᵥ y, by simp [hBA]⟩⟩
  choose cols hcols using (h <| Pi.single · 1)
  refine ⟨(Matrix.of cols)ᵀ, Matrix.ext fun i j => ?_⟩
  rw [one_eq_pi_single]; rw [Pi.single_comm]; rw [← hcols j]
  rfl

中文:
定理 mulVec_surjective_iff_存在_right_inverse
  证明: by
  cases nonempty_fintype m
  refine ⟨fun h => ?_, fun ⟨B, hBA⟩ y => ⟨B *ᵥ y, by simp [hBA]⟩⟩
  choose cols hcols using (h <| Pi.single · 1)
  refine ⟨(Matrix.of cols)ᵀ, Matrix.ext fun i j => ?_⟩
  rw [one_eq_pi_single]; rw [Pi.single_comm]; rw [← hcols j]
  rfl

Depends on / 依赖: Matrix, Matrix.ext, Matrix.of, Pi.single, Pi.single_comm, nonempty_fintype, one_eq_pi_single, single, single_comm
-/
theorem mulVec_surjective_iff_exists_right_inverse
    [DecidableEq m] [Finite m] [Fintype n] {A : Matrix m n R} :
    Function.Surjective A.mulVec ↔ exists B : Matrix n m R, A * B = 1 := by
  cases nonempty_fintype m
  refine ⟨fun h => ?_, fun ⟨B, hBA⟩ y => ⟨B *ᵥ y, by simp [hBA]⟩⟩
  choose cols hcols using (h <| Pi.single · 1)
  refine ⟨(Matrix.of cols)ᵀ, Matrix.ext fun i j => ?_⟩
  rw [one_eq_pi_single]; rw [Pi.single_comm]; rw [← hcols j]
  rfl

end Semiring

variable [DecidableEq m] {R K : Type*} [CommRing R] [Field K] [Fintype m]

/--
theorem `vecMul_surjective_iff_isUnit` / 定理 `vecMul_surjective_iff_isUnit`

English:
theorem vecMul_surjective_iff_isUnit
  given: {A : Matrix m m R}
  proof: by
  rw [vecMul_surjective_iff_exists_left_inverse]; rw [isUnit_iff_exists_inv']

中文:
定理 vecMul_surjective_iff_isUnit
  条件: {A : 矩阵 m m R}
  证明: by
  rw [vecMul_surjective_iff_exists_left_inverse]; rw [isUnit_iff_exists_inv']

Depends on / 依赖: isUnit_iff_exists_inv, vecMul_surjective_iff_exists_left_inverse
-/
theorem vecMul_surjective_iff_isUnit {A : Matrix m m R} :
    Function.Surjective A.vecMul ↔ IsUnit A := by
  rw [vecMul_surjective_iff_exists_left_inverse]; rw [isUnit_iff_exists_inv']

/--
theorem `mulVec_surjective_iff_isUnit` / 定理 `mulVec_surjective_iff_isUnit`

English:
theorem mulVec_surjective_iff_isUnit
  given: {A : Matrix m m R}
  proof: by
  rw [mulVec_surjective_iff_exists_right_inverse]; rw [isUnit_iff_exists_inv]

中文:
定理 mulVec_surjective_iff_isUnit
  条件: {A : 矩阵 m m R}
  证明: by
  rw [mulVec_surjective_iff_exists_right_inverse]; rw [isUnit_iff_exists_inv]

Depends on / 依赖: isUnit_iff_exists_inv, mulVec_surjective_iff_exists_right_inverse
-/
theorem mulVec_surjective_iff_isUnit {A : Matrix m m R} :
    Function.Surjective A.mulVec ↔ IsUnit A := by
  rw [mulVec_surjective_iff_exists_right_inverse]; rw [isUnit_iff_exists_inv]

/--
theorem `vecMul_injective_iff_isUnit` / 定理 `vecMul_injective_iff_isUnit`

English:
theorem vecMul_injective_iff_isUnit
  given: {A : Matrix m m K}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← vecMul_surjective_iff_isUnit]
    exact LinearMap.surjective_of_injective (f := A.vecMulLinear) h
  exact vecMul_injective_of_isUnit h

中文:
定理 vecMul_injective_iff_isUnit
  条件: {A : 矩阵 m m K}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← vecMul_surjective_iff_isUnit]
    exact LinearMap.surjective_of_injective (f := A.vecMulLinear) h
  exact vecMul_injective_of_isUnit h

Depends on / 依赖: A.vecMulLinear, LinearMap, LinearMap.surjective_of_injective, surjective_of_injective, vecMulLinear, vecMul_injective_of_isUnit, vecMul_surjective_iff_isUnit
-/
theorem vecMul_injective_iff_isUnit {A : Matrix m m K} :
    Function.Injective A.vecMul ↔ IsUnit A := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← vecMul_surjective_iff_isUnit]
    exact LinearMap.surjective_of_injective (f := A.vecMulLinear) h
  exact vecMul_injective_of_isUnit h

/--
theorem `mulVec_injective_iff_isUnit` / 定理 `mulVec_injective_iff_isUnit`

English:
theorem mulVec_injective_iff_isUnit
  given: {A : Matrix m m K}
  proof: by
  rw [← isUnit_transpose]; rw [← vecMul_injective_iff_isUnit]
  simp_rw [vecMul_transpose]

中文:
定理 mulVec_injective_iff_isUnit
  条件: {A : 矩阵 m m K}
  证明: by
  rw [← isUnit_transpose]; rw [← vecMul_injective_iff_isUnit]
  simp_rw [vecMul_transpose]

Depends on / 依赖: isUnit_transpose, simp_rw, vecMul_injective_iff_isUnit, vecMul_transpose
-/
theorem mulVec_injective_iff_isUnit {A : Matrix m m K} :
    Function.Injective A.mulVec ↔ IsUnit A := by
  rw [← isUnit_transpose]; rw [← vecMul_injective_iff_isUnit]
  simp_rw [vecMul_transpose]

/--
theorem `linearIndependent_rows_iff_isUnit` / 定理 `linearIndependent_rows_iff_isUnit`

English:
theorem linearIndependent_rows_iff_isUnit
  given: {A : Matrix m m K}
  proof: by
  rw [← col_transpose]; rw [← mulVec_injective_iff]; rw [← coe_mulVecLin]; rw [mulVecLin_transpose]; rw [← vecMul_injective_iff_isUnit]; rw [coe_vecMulLinear]

中文:
定理 linearIndependent_rows_iff_isUnit
  条件: {A : 矩阵 m m K}
  证明: by
  rw [← col_transpose]; rw [← mulVec_injective_iff]; rw [← coe_mulVecLin]; rw [mulVecLin_transpose]; rw [← vecMul_injective_iff_isUnit]; rw [coe_vecMulLinear]

Depends on / 依赖: coe_mulVecLin, coe_vecMulLinear, col_transpose, mulVecLin_transpose, mulVec_injective_iff, vecMul_injective_iff_isUnit
-/
theorem linearIndependent_rows_iff_isUnit {A : Matrix m m K} :
    LinearIndependent K A.row ↔ IsUnit A := by
  rw [← col_transpose]; rw [← mulVec_injective_iff]; rw [← coe_mulVecLin]; rw [mulVecLin_transpose]; rw [← vecMul_injective_iff_isUnit]; rw [coe_vecMulLinear]

/--
theorem `linearIndependent_cols_iff_isUnit` / 定理 `linearIndependent_cols_iff_isUnit`

English:
theorem linearIndependent_cols_iff_isUnit
  given: {A : Matrix m m K}
  proof: by
  rw [← row_transpose]; rw [linearIndependent_rows_iff_isUnit]; rw [isUnit_transpose]

中文:
定理 linearIndependent_cols_iff_isUnit
  条件: {A : 矩阵 m m K}
  证明: by
  rw [← row_transpose]; rw [linearIndependent_rows_iff_isUnit]; rw [isUnit_transpose]

Depends on / 依赖: isUnit_transpose, linearIndependent_rows_iff_isUnit, row_transpose
-/
theorem linearIndependent_cols_iff_isUnit {A : Matrix m m K} :
    LinearIndependent K A.col ↔ IsUnit A := by
  rw [← row_transpose]; rw [linearIndependent_rows_iff_isUnit]; rw [isUnit_transpose]

/--
theorem `vecMul_surjective_of_invertible` / 定理 `vecMul_surjective_of_invertible`

English:
theorem vecMul_surjective_of_invertible
  given: (A : Matrix m m R) [Invertible A]
  proof: vecMul_surjective_iff_isUnit.2 isUnit_of_invertible A

中文:
定理 vecMul_surjective_of_invertible
  条件: (A : 矩阵 m m R) [可逆 A]
  证明: vecMul_surjective_iff_isUnit.2 isUnit_of_invertible A

Depends on / 依赖: isUnit_of_invertible, vecMul_surjective_iff_isUnit
-/
theorem vecMul_surjective_of_invertible (A : Matrix m m R) [Invertible A] :
    Function.Surjective A.vecMul :=
vecMul_surjective_iff_isUnit.2 isUnit_of_invertible A

/--
theorem `mulVec_surjective_of_invertible` / 定理 `mulVec_surjective_of_invertible`

English:
theorem mulVec_surjective_of_invertible
  given: (A : Matrix m m R) [Invertible A]
  proof: mulVec_surjective_iff_isUnit.2 isUnit_of_invertible A

中文:
定理 mulVec_surjective_of_invertible
  条件: (A : 矩阵 m m R) [可逆 A]
  证明: mulVec_surjective_iff_isUnit.2 isUnit_of_invertible A

Depends on / 依赖: isUnit_of_invertible, mulVec_surjective_iff_isUnit
-/
theorem mulVec_surjective_of_invertible (A : Matrix m m R) [Invertible A] :
    Function.Surjective A.mulVec :=
mulVec_surjective_iff_isUnit.2 isUnit_of_invertible A

/--
theorem `vecMul_injective_of_invertible` / 定理 `vecMul_injective_of_invertible`

English:
theorem vecMul_injective_of_invertible
  given: (A : Matrix m m K) [Invertible A]
  proof: vecMul_injective_iff_isUnit.2 isUnit_of_invertible A

中文:
定理 vecMul_injective_of_invertible
  条件: (A : 矩阵 m m K) [可逆 A]
  证明: vecMul_injective_iff_isUnit.2 isUnit_of_invertible A

Depends on / 依赖: isUnit_of_invertible, vecMul_injective_iff_isUnit
-/
theorem vecMul_injective_of_invertible (A : Matrix m m K) [Invertible A] :
    Function.Injective A.vecMul :=
vecMul_injective_iff_isUnit.2 isUnit_of_invertible A

/--
theorem `mulVec_injective_of_invertible` / 定理 `mulVec_injective_of_invertible`

English:
theorem mulVec_injective_of_invertible
  given: (A : Matrix m m K) [Invertible A]
  proof: mulVec_injective_iff_isUnit.2 isUnit_of_invertible A

中文:
定理 mulVec_injective_of_invertible
  条件: (A : 矩阵 m m K) [可逆 A]
  证明: mulVec_injective_iff_isUnit.2 isUnit_of_invertible A

Depends on / 依赖: isUnit_of_invertible, mulVec_injective_iff_isUnit
-/
theorem mulVec_injective_of_invertible (A : Matrix m m K) [Invertible A] :
    Function.Injective A.mulVec :=
mulVec_injective_iff_isUnit.2 isUnit_of_invertible A

/--
theorem `linearIndependent_rows_of_invertible` / 定理 `linearIndependent_rows_of_invertible`

English:
theorem linearIndependent_rows_of_invertible
  given: (A : Matrix m m K) [Invertible A]
  proof: linearIndependent_rows_iff_isUnit.2 isUnit_of_invertible A

中文:
定理 linearIndependent_rows_of_invertible
  条件: (A : 矩阵 m m K) [可逆 A]
  证明: linearIndependent_rows_iff_isUnit.2 isUnit_of_invertible A

Depends on / 依赖: isUnit_of_invertible, linearIndependent_rows_iff_isUnit
-/
theorem linearIndependent_rows_of_invertible (A : Matrix m m K) [Invertible A] :
    LinearIndependent K A.row :=
linearIndependent_rows_iff_isUnit.2 isUnit_of_invertible A

/--
theorem `linearIndependent_cols_of_invertible` / 定理 `linearIndependent_cols_of_invertible`

English:
theorem linearIndependent_cols_of_invertible
  given: (A : Matrix m m K) [Invertible A]
  proof: linearIndependent_cols_iff_isUnit.2 isUnit_of_invertible A

中文:
定理 linearIndependent_cols_of_invertible
  条件: (A : 矩阵 m m K) [可逆 A]
  证明: linearIndependent_cols_iff_isUnit.2 isUnit_of_invertible A

Depends on / 依赖: isUnit_of_invertible, linearIndependent_cols_iff_isUnit
-/
theorem linearIndependent_cols_of_invertible (A : Matrix m m K) [Invertible A] :
    LinearIndependent K A.col :=
linearIndependent_cols_iff_isUnit.2 isUnit_of_invertible A

end vecMul

variable [Fintype n] [DecidableEq n] [CommRing α]
variable (A : Matrix n n α) (B : Matrix n n α)

/--
theorem `nonsing_inv_cancel_or_zero` / 定理 `nonsing_inv_cancel_or_zero`

English:
theorem nonsing_inv_cancel_or_zero
  statement: A⁻¹ * A = 1 ∧ A * A⁻¹ = 1 ∨ A⁻¹ = 0
  proof: by
  by_cases h : IsUnit A.det
  · exact Or.inl ⟨nonsing_inv_mul _ h, mul_nonsing_inv _ h⟩
  · exact Or.inr (nonsing_inv_apply_not_isUnit _ h)

中文:
定理 nonsing_inv_cancel_or_zero
  结论: A⁻¹ * A = 1 ∧ A * A⁻¹ = 1 ∨ A⁻¹ = 0
  证明: by
  by_cases h : IsUnit A.det
  · exact Or.inl ⟨nonsing_inv_mul _ h, mul_nonsing_inv _ h⟩
  · exact Or.inr (nonsing_inv_apply_not_isUnit _ h)

Depends on / 依赖: A.det, IsUnit, Or.inl, Or.inr, mul_nonsing_inv, nonsing_inv_apply_not_isUnit, nonsing_inv_mul
-/
theorem nonsing_inv_cancel_or_zero : A⁻¹ * A = 1 ∧ A * A⁻¹ = 1 ∨ A⁻¹ = 0 := by
  by_cases h : IsUnit A.det
  · exact Or.inl ⟨nonsing_inv_mul _ h, mul_nonsing_inv _ h⟩
  · exact Or.inr (nonsing_inv_apply_not_isUnit _ h)

/--
theorem `det_nonsing_inv_mul_det` / 定理 `det_nonsing_inv_mul_det`

English:
theorem det_nonsing_inv_mul_det
  given: (h : IsUnit A.det)
  statement: A⁻¹.det * A.det = 1
  proof: by
  rw [← det_mul]; rw [A.nonsing_inv_mul h]; rw [det_one]

@[simp]

中文:
定理 det_nonsing_inv_mul_det
  条件: (h : 是单位 A.det)
  结论: A⁻¹.det * A.det = 1
  证明: by
  rw [← det_mul]; rw [A.nonsing_inv_mul h]; rw [det_one]

@[simp]

Depends on / 依赖: A.nonsing_inv_mul, det_mul, det_one, nonsing_inv_mul
-/
theorem det_nonsing_inv_mul_det (h : IsUnit A.det) : A⁻¹.det * A.det = 1 := by
  rw [← det_mul]; rw [A.nonsing_inv_mul h]; rw [det_one]

@[simp]
/--
theorem `det_nonsing_inv` / 定理 `det_nonsing_inv`

English:
theorem det_nonsing_inv
  statement: A⁻¹.det = A.det⁻¹ʳ
  proof: by
  by_cases h : IsUnit A.det
  · cases h.nonempty_invertible
    let := invertibleOfDetInvertible A
    rw [Ring.inverse_invertible]; rw [← invOf_eq_nonsing_inv]; rw [det_invOf]
  cases isEmpty_or_nonempty n
  · rw [det_isEmpty, det_isEmpty, Ring.inverse_one]
  · rw [Ring.inverse_non_unit _ h, nonsing_inv_apply_not_isUnit _ h, det_zero]

中文:
定理 det_nonsing_inv
  结论: A⁻¹.det = A.det⁻¹ʳ
  证明: by
  by_cases h : IsUnit A.det
  · cases h.nonempty_invertible
    let := invertibleOfDetInvertible A
    rw [Ring.inverse_invertible]; rw [← invOf_eq_nonsing_inv]; rw [det_invOf]
  cases isEmpty_or_nonempty n
  · rw [det_isEmpty, det_isEmpty, Ring.inverse_one]
  · rw [Ring.inverse_non_unit _ h, nonsing_inv_apply_not_isUnit _ h, det_zero]

Depends on / 依赖: A.det, IsUnit, Ring.inverse_invertible, Ring.inverse_non_unit, Ring.inverse_one, det_invOf, det_isEmpty, det_zero, h.nonempty_invertible, invOf_eq_nonsing_inv, inverse_invertible, inverse_non_unit, inverse_one, invertibleOfDetInvertible, isEmpty_or_nonempty, nonempty_invertible, nonsing_inv_apply_not_isUnit
-/
theorem det_nonsing_inv : A⁻¹.det = A.det⁻¹ʳ := by
  by_cases h : IsUnit A.det
  · cases h.nonempty_invertible
    let := invertibleOfDetInvertible A
    rw [Ring.inverse_invertible]; rw [← invOf_eq_nonsing_inv]; rw [det_invOf]
  cases isEmpty_or_nonempty n
  · rw [det_isEmpty, det_isEmpty, Ring.inverse_one]
  · rw [Ring.inverse_non_unit _ h, nonsing_inv_apply_not_isUnit _ h, det_zero]

/--
theorem `isUnit_nonsing_inv_det` / 定理 `isUnit_nonsing_inv_det`

English:
theorem isUnit_nonsing_inv_det
  given: (h : IsUnit A.det)
  statement: IsUnit A⁻¹.det
  proof: .of_mul_eq_one _ (A.det_nonsing_inv_mul_det h)

@[simp]

中文:
定理 isUnit_nonsing_inv_det
  条件: (h : 是单位 A.det)
  结论: 是单位 A⁻¹.det
  证明: .of_mul_eq_one _ (A.det_nonsing_inv_mul_det h)

@[simp]

Depends on / 依赖: A.det_nonsing_inv_mul_det, det_nonsing_inv_mul_det, of_mul_eq_one
-/
theorem isUnit_nonsing_inv_det (h : IsUnit A.det) : IsUnit A⁻¹.det :=
  .of_mul_eq_one _ (A.det_nonsing_inv_mul_det h)

@[simp]
/--
theorem `nonsing_inv_nonsing_inv` / 定理 `nonsing_inv_nonsing_inv`

English:
theorem nonsing_inv_nonsing_inv
  given: (h : IsUnit A.det)
  statement: A⁻¹⁻¹ = A
  proof: calc
    A⁻¹⁻¹ = 1 * A⁻¹⁻¹ := by rw [Matrix.one_mul]
    _ = A * A⁻¹ * A⁻¹⁻¹ := by rw [A.mul_nonsing_inv h]
    _ = A := by
      rw [Matrix.mul_assoc]; rw [A⁻¹.mul_nonsing_inv (A.isUnit_nonsing_inv_det h)]; rw [Matrix.mul_one]

中文:
定理 nonsing_inv_nonsing_inv
  条件: (h : 是单位 A.det)
  结论: A⁻¹⁻¹ = A
  证明: calc
    A⁻¹⁻¹ = 1 * A⁻¹⁻¹ := by rw [Matrix.one_mul]
    _ = A * A⁻¹ * A⁻¹⁻¹ := by rw [A.mul_nonsing_inv h]
    _ = A := by
      rw [Matrix.mul_assoc]; rw [A⁻¹.mul_nonsing_inv (A.isUnit_nonsing_inv_det h)]; rw [Matrix.mul_one]

Depends on / 依赖: A.isUnit_nonsing_inv_det, A.mul_nonsing_inv, Matrix, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul, isUnit_nonsing_inv_det, mul_assoc, mul_nonsing_inv, mul_one, one_mul
-/
theorem nonsing_inv_nonsing_inv (h : IsUnit A.det) : A⁻¹⁻¹ = A :=
  calc
    A⁻¹⁻¹ = 1 * A⁻¹⁻¹ := by rw [Matrix.one_mul]
    _ = A * A⁻¹ * A⁻¹⁻¹ := by rw [A.mul_nonsing_inv h]
    _ = A := by
      rw [Matrix.mul_assoc]; rw [A⁻¹.mul_nonsing_inv (A.isUnit_nonsing_inv_det h)]; rw [Matrix.mul_one]

/--
theorem `isUnit_nonsing_inv_det_iff` / 定理 `isUnit_nonsing_inv_det_iff`

English:
theorem isUnit_nonsing_inv_det_iff
  given: {A : Matrix n n α}
  statement: IsUnit A⁻¹.det ↔ IsUnit A.det
  proof: by
  rw [Matrix.det_nonsing_inv]; rw [isUnit_ringInverse]

@[simp]

中文:
定理 isUnit_nonsing_inv_det_iff
  条件: {A : 矩阵 n n α}
  结论: 是单位 A⁻¹.det ↔ 是单位 A.det
  证明: by
  rw [Matrix.det_nonsing_inv]; rw [isUnit_ringInverse]

@[simp]

Depends on / 依赖: Matrix, Matrix.det_nonsing_inv, det_nonsing_inv, isUnit_ringInverse
-/
theorem isUnit_nonsing_inv_det_iff {A : Matrix n n α} : IsUnit A⁻¹.det ↔ IsUnit A.det := by
  rw [Matrix.det_nonsing_inv]; rw [isUnit_ringInverse]

@[simp]
/--
theorem `isUnit_nonsing_inv_iff` / 定理 `isUnit_nonsing_inv_iff`

English:
theorem isUnit_nonsing_inv_iff
  given: {A : Matrix n n α}
  statement: IsUnit A⁻¹ ↔ IsUnit A
  proof: by
  simp_rw [isUnit_iff_isUnit_det, isUnit_nonsing_inv_det_iff]

中文:
定理 isUnit_nonsing_inv_iff
  条件: {A : 矩阵 n n α}
  结论: 是单位 A⁻¹ ↔ 是单位 A
  证明: by
  simp_rw [isUnit_iff_isUnit_det, isUnit_nonsing_inv_det_iff]

Depends on / 依赖: isUnit_iff_isUnit_det, isUnit_nonsing_inv_det_iff, simp_rw
-/
theorem isUnit_nonsing_inv_iff {A : Matrix n n α} : IsUnit A⁻¹ ↔ IsUnit A := by
  simp_rw [isUnit_iff_isUnit_det, isUnit_nonsing_inv_det_iff]

-- `IsUnit.invertible` lifts the proposition `IsUnit A` to a constructive inverse of `A`.
/-- A version of `Matrix.invertibleOfDetInvertible` with the inverse defeq to `A⁻¹` that is
therefore noncomputable. -/
@[instance_reducible]
/--
Definition of `invertibleOfIsUnitDet` / `invertibleOfIsUnitDet` 的定义

English:
definition invertibleOfIsUnitDet
  signature: (h : IsUnit A.det)
  body: ⟨A⁻¹, nonsing_inv_mul A h, mul_nonsing_inv A h⟩

中文:
定义 invertibleOfIsUnitDet
  签名: (h : 是单位 A.det)
  定义体: ⟨A⁻¹, nonsing_inv_mul A h, mul_nonsing_inv A h⟩

Depends on / 依赖: mul_nonsing_inv, nonsing_inv_mul
-/
noncomputable def invertibleOfIsUnitDet (h : IsUnit A.det) : Invertible A :=
  ⟨A⁻¹, nonsing_inv_mul A h, mul_nonsing_inv A h⟩

/--
Definition of `nonsingInvUnit` / `nonsingInvUnit` 的定义

English:
definition nonsingInvUnit
  signature: (h : IsUnit A.det)
  body: @unitOfInvertible _ _ _ (invertibleOfIsUnitDet A h)

中文:
定义 nonsingInvUnit
  签名: (h : 是单位 A.det)
  定义体: @unitOfInvertible _ _ _ (invertibleOfIsUnitDet A h)

Depends on / 依赖: invertibleOfIsUnitDet, unitOfInvertible
-/
noncomputable def nonsingInvUnit (h : IsUnit A.det) : (Matrix n n α)ˣ :=
  @unitOfInvertible _ _ _ (invertibleOfIsUnitDet A h)

/--
theorem `unitOfDetInvertible_eq_nonsingInvUnit` / 定理 `unitOfDetInvertible_eq_nonsingInvUnit`

English:
theorem unitOfDetInvertible_eq_nonsingInvUnit
  given: [Invertible A.det]
  proof: by
  ext
  rfl

中文:
定理 unitOfDetInvertible_eq_nonsingInvUnit
  条件: [可逆 A.det]
  证明: by
  ext
  rfl
-/
theorem unitOfDetInvertible_eq_nonsingInvUnit [Invertible A.det] :
    unitOfDetInvertible A = nonsingInvUnit A (isUnit_of_invertible _) := by
  ext
  rfl

variable {A} {B}

/--
theorem `inv_eq_left_inv` / 定理 `inv_eq_left_inv`

English:
theorem inv_eq_left_inv
  given: (h : B * A = 1)
  statement: A⁻¹ = B
  proof: letI := invertibleOfLeftInverse _ _ h
  invOf_eq_nonsing_inv A ▸ invOf_eq_left_inv h

中文:
定理 inv_eq_left_inv
  条件: (h : B * A = 1)
  结论: A⁻¹ = B
  证明: letI := invertibleOfLeftInverse _ _ h
  invOf_eq_nonsing_inv A ▸ invOf_eq_left_inv h

Depends on / 依赖: invOf_eq_left_inv, invOf_eq_nonsing_inv, invertibleOfLeftInverse
-/
theorem inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B :=
  letI := invertibleOfLeftInverse _ _ h
  invOf_eq_nonsing_inv A ▸ invOf_eq_left_inv h

/--
theorem `inv_eq_right_inv` / 定理 `inv_eq_right_inv`

English:
theorem inv_eq_right_inv
  given: (h : A * B = 1)
  statement: A⁻¹ = B
  proof: inv_eq_left_inv (mul_eq_one_comm.2 h)

中文:
定理 inv_eq_right_inv
  条件: (h : A * B = 1)
  结论: A⁻¹ = B
  证明: inv_eq_left_inv (mul_eq_one_comm.2 h)

Depends on / 依赖: inv_eq_left_inv, mul_eq_one_comm
-/
theorem inv_eq_right_inv (h : A * B = 1) : A⁻¹ = B :=
  inv_eq_left_inv (mul_eq_one_comm.2 h)

section InvEqInv

variable {C : Matrix n n α}

/--
theorem `left_inv_eq_left_inv` / 定理 `left_inv_eq_left_inv`

English:
theorem left_inv_eq_left_inv
  given: (h : B * A = 1) (g : C * A = 1)
  statement: B = C
  proof: by
  rw [← inv_eq_left_inv h]; rw [← inv_eq_left_inv g]

中文:
定理 left_inv_eq_left_inv
  条件: (h : B * A = 1) (g : C * A = 1)
  结论: B = C
  证明: by
  rw [← inv_eq_left_inv h]; rw [← inv_eq_left_inv g]

Depends on / 依赖: inv_eq_left_inv
-/
theorem left_inv_eq_left_inv (h : B * A = 1) (g : C * A = 1) : B = C := by
  rw [← inv_eq_left_inv h]; rw [← inv_eq_left_inv g]

/--
theorem `right_inv_eq_right_inv` / 定理 `right_inv_eq_right_inv`

English:
theorem right_inv_eq_right_inv
  given: (h : A * B = 1) (g : A * C = 1)
  statement: B = C
  proof: by
  rw [← inv_eq_right_inv h]; rw [← inv_eq_right_inv g]

中文:
定理 right_inv_eq_right_inv
  条件: (h : A * B = 1) (g : A * C = 1)
  结论: B = C
  证明: by
  rw [← inv_eq_right_inv h]; rw [← inv_eq_right_inv g]

Depends on / 依赖: inv_eq_right_inv
-/
theorem right_inv_eq_right_inv (h : A * B = 1) (g : A * C = 1) : B = C := by
  rw [← inv_eq_right_inv h]; rw [← inv_eq_right_inv g]

/--
theorem `right_inv_eq_left_inv` / 定理 `right_inv_eq_left_inv`

English:
theorem right_inv_eq_left_inv
  given: (h : A * B = 1) (g : C * A = 1)
  statement: B = C
  proof: by
  rw [← inv_eq_right_inv h]; rw [← inv_eq_left_inv g]

中文:
定理 right_inv_eq_left_inv
  条件: (h : A * B = 1) (g : C * A = 1)
  结论: B = C
  证明: by
  rw [← inv_eq_right_inv h]; rw [← inv_eq_left_inv g]

Depends on / 依赖: inv_eq_left_inv, inv_eq_right_inv
-/
theorem right_inv_eq_left_inv (h : A * B = 1) (g : C * A = 1) : B = C := by
  rw [← inv_eq_right_inv h]; rw [← inv_eq_left_inv g]

/--
theorem `inv_inj` / 定理 `inv_inj`

English:
theorem inv_inj
  given: (h : A⁻¹ = B⁻¹) (h' : IsUnit A.det)
  statement: A = B
  proof: by
  refine left_inv_eq_left_inv (mul_nonsing_inv _ h') ?_
  rw [h]
  refine mul_nonsing_inv _ ?_
  rwa [← isUnit_nonsing_inv_det_iff, ← h, isUnit_nonsing_inv_det_iff]

中文:
定理 inv_inj
  条件: (h : A⁻¹ = B⁻¹) (h' : 是单位 A.det)
  结论: A = B
  证明: by
  refine left_inv_eq_left_inv (mul_nonsing_inv _ h') ?_
  rw [h]
  refine mul_nonsing_inv _ ?_
  rwa [← isUnit_nonsing_inv_det_iff, ← h, isUnit_nonsing_inv_det_iff]

Depends on / 依赖: isUnit_nonsing_inv_det_iff, left_inv_eq_left_inv, mul_nonsing_inv
-/
theorem inv_inj (h : A⁻¹ = B⁻¹) (h' : IsUnit A.det) : A = B := by
  refine left_inv_eq_left_inv (mul_nonsing_inv _ h') ?_
  rw [h]
  refine mul_nonsing_inv _ ?_
  rwa [← isUnit_nonsing_inv_det_iff, ← h, isUnit_nonsing_inv_det_iff]

end InvEqInv

variable (A)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `inv_zero` / 定理 `inv_zero`

English:
theorem inv_zero
  statement: (0 : Matrix n n α)⁻¹ = 0
  proof: by
  rcases subsingleton_or_nontrivial α with ht | ht
  · simp [eq_iff_true_of_subsingleton]
  rcases (Fintype.card n).zero_le.eq_or_lt with hc | hc
  · rw [eq_comm, Fintype.card_eq_zero_iff] at hc
    subsingleton
  · have hn : Nonempty n := Fintype.card_pos_iff.mp hc
    refine nonsing_inv_apply_not_isUnit _ ?_
    simp [det]

中文:
定理 inv_zero
  结论: (0 : 矩阵 n n α)⁻¹ = 0
  证明: by
  rcases subsingleton_or_nontrivial α with ht | ht
  · simp [eq_iff_true_of_subsingleton]
  rcases (Fintype.card n).zero_le.eq_or_lt with hc | hc
  · rw [eq_comm, Fintype.card_eq_zero_iff] at hc
    subsingleton
  · have hn : Nonempty n := Fintype.card_pos_iff.mp hc
    refine nonsing_inv_apply_not_isUnit _ ?_
    simp [det]

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_eq_zero_iff, Fintype.card_pos_iff.mp, Nonempty, card_eq_zero_iff, card_pos_iff, eq_comm, eq_iff_true_of_subsingleton, eq_or_lt, nonsing_inv_apply_not_isUnit, subsingleton, subsingleton_or_nontrivial, zero_le, zero_le.eq_or_lt
-/
theorem inv_zero : (0 : Matrix n n α)⁻¹ = 0 := by
  rcases subsingleton_or_nontrivial α with ht | ht
  · simp [eq_iff_true_of_subsingleton]
  rcases (Fintype.card n).zero_le.eq_or_lt with hc | hc
  · rw [eq_comm, Fintype.card_eq_zero_iff] at hc
    subsingleton
  · have hn : Nonempty n := Fintype.card_pos_iff.mp hc
    refine nonsing_inv_apply_not_isUnit _ ?_
    simp [det]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvOneClass (Matrix n n α)
  body: { Matrix.one, Matrix.inv with inv_one := inv_eq_left_inv (by simp) }

中文:
实例 :
  签名: InvOne类 (矩阵 n n α)
  定义体: { Matrix.one, Matrix.inv with inv_one := inv_eq_left_inv (by simp) }

Depends on / 依赖: Matrix, Matrix.inv, Matrix.one, inv_eq_left_inv, inv_one
-/
noncomputable instance : InvOneClass (Matrix n n α) :=
  { Matrix.one, Matrix.inv with inv_one := inv_eq_left_inv (by simp) }

/--
theorem `inv_smul` / 定理 `inv_smul`

English:
theorem inv_smul
  given: (k : α) [Invertible k] (h : IsUnit A.det)
  statement: (k • A)⁻¹ = ⅟k • A⁻¹
  proof: inv_eq_left_inv (by simp [h, smul_smul])

中文:
定理 inv_smul
  条件: (k : α) [可逆 k] (h : 是单位 A.det)
  结论: (k • A)⁻¹ = ⅟k • A⁻¹
  证明: inv_eq_left_inv (by simp [h, smul_smul])

Depends on / 依赖: inv_eq_left_inv, smul_smul
-/
theorem inv_smul (k : α) [Invertible k] (h : IsUnit A.det) : (k • A)⁻¹ = ⅟k • A⁻¹ :=
  inv_eq_left_inv (by simp [h, smul_smul])

/--
theorem `inv_smul'` / 定理 `inv_smul'`

English:
theorem inv_smul'
  given: (k : αˣ) (h : IsUnit A.det)
  statement: (k • A)⁻¹ = k⁻¹ • A⁻¹
  proof: inv_eq_left_inv (by simp [h, smul_smul])

中文:
定理 inv_smul'
  条件: (k : αˣ) (h : 是单位 A.det)
  结论: (k • A)⁻¹ = k⁻¹ • A⁻¹
  证明: inv_eq_left_inv (by simp [h, smul_smul])

Depends on / 依赖: inv_eq_left_inv, smul_smul
-/
theorem inv_smul' (k : αˣ) (h : IsUnit A.det) : (k • A)⁻¹ = k⁻¹ • A⁻¹ :=
  inv_eq_left_inv (by simp [h, smul_smul])

/--
theorem `inv_adjugate` / 定理 `inv_adjugate`

English:
theorem inv_adjugate
  given: (A : Matrix n n α) (h : IsUnit A.det)
  statement: (adjugate A)⁻¹ = h.unit⁻¹ • A
  proof: by
  refine inv_eq_left_inv ?_
  rw [smul_mul]; rw [mul_adjugate]; rw [Units.smul_def]; rw [smul_smul]; rw [h.val_inv_mul]; rw [one_smul]

中文:
定理 inv_adjugate
  条件: (A : 矩阵 n n α) (h : 是单位 A.det)
  结论: (adjugate A)⁻¹ = h.unit⁻¹ • A
  证明: by
  refine inv_eq_left_inv ?_
  rw [smul_mul]; rw [mul_adjugate]; rw [Units.smul_def]; rw [smul_smul]; rw [h.val_inv_mul]; rw [one_smul]

Depends on / 依赖: Units.smul_def, h.val_inv_mul, inv_eq_left_inv, mul_adjugate, one_smul, smul_def, smul_mul, smul_smul, val_inv_mul
-/
theorem inv_adjugate (A : Matrix n n α) (h : IsUnit A.det) : (adjugate A)⁻¹ = h.unit⁻¹ • A := by
  refine inv_eq_left_inv ?_
  rw [smul_mul]; rw [mul_adjugate]; rw [Units.smul_def]; rw [smul_smul]; rw [h.val_inv_mul]; rw [one_smul]

section Diagonal

attribute [local instance] Invertible.map in
/-- `diagonal v` is invertible if `v` is -/
@[instance_reducible]
/--
Definition of `diagonalInvertible` / `diagonalInvertible` 的定义

English:
definition diagonalInvertible
  signature: {α} [NonAssocSemiring α] (v : n -> α) [Invertible v]
  body: inferInstanceAs Invertible (diagonalRingHom n α v)

中文:
定义 diagonalInvertible
  签名: {α} [非结合半环 α] (v : n -> α) [可逆 v]
  定义体: inferInstanceAs Invertible (diagonalRingHom n α v)

Depends on / 依赖: Invertible, diagonalRingHom
-/
def diagonalInvertible {α} [NonAssocSemiring α] (v : n -> α) [Invertible v] :
    Invertible (diagonal v) :=
inferInstanceAs Invertible (diagonalRingHom n α v)

/--
theorem `invOf_diagonal_eq` / 定理 `invOf_diagonal_eq`

English:
theorem invOf_diagonal_eq
  given: {α} [Semiring α] (v : n -> α) [Invertible v] [Invertible (diagonal v)]
  proof: by
  rw [@Invertible.congr _ _ _ _ _ (diagonalInvertible v) rfl]
  rfl

中文:
定理 invOf_diagonal_eq
  条件: {α} [半环 α] (v : n -> α) [可逆 v] [可逆 (diagonal v)]
  证明: by
  rw [@Invertible.congr _ _ _ _ _ (diagonalInvertible v) rfl]
  rfl

Depends on / 依赖: Invertible, Invertible.congr, diagonalInvertible
-/
theorem invOf_diagonal_eq {α} [Semiring α] (v : n -> α) [Invertible v] [Invertible (diagonal v)] :
    ⅟(diagonal v) = diagonal (⅟v) := by
  rw [@Invertible.congr _ _ _ _ _ (diagonalInvertible v) rfl]
  rfl

/-- `v` is invertible if `diagonal v` is -/
@[instance_reducible]
/--
Definition of `invertibleOfDiagonalInvertible` / `invertibleOfDiagonalInvertible` 的定义

English:
definition invertibleOfDiagonalInvertible
  signature: (v : n -> α) [Invertible (diagonal v)]
  body: diag (⅟(diagonal v))
  invOf_mul_self :=
    funext fun i => by
      let : Invertible (diagonal v).det := detInvertibleOfInvertible _
      rw [invOf_eq]; rw [diag_smul]; rw [adjugate_diagonal]; rw [diag_diagonal]
      dsimp
      rw [mul_assoc]; rw [prod_erase_mul _ _ (Finset.mem_univ _)]; rw [← det_diagonal]
      exact mul_invOf_self _
  mul_invOf_self :=
    funext fun i => by
      let : Invertible (diagonal v).det := detInvertibleOfInvertible _
      rw [invOf_eq]; rw [diag_smul]; rw [adjugate_diagonal]; rw [diag_diagonal]
      dsimp
      rw [mul_left_comm]; rw [mul_prod_erase _ _ (Finset.mem_univ _)]; rw [← det_diagonal]
      exact mul_invOf_self _

中文:
定义 invertibleOfDiagonalInvertible
  签名: (v : n -> α) [可逆 (diagonal v)]
  定义体: diag (⅟(diagonal v))
  invOf_mul_self :=
    funext fun i => by
      let : Invertible (diagonal v).det := detInvertibleOfInvertible _
      rw [invOf_eq]; rw [diag_smul]; rw [adjugate_diagonal]; rw [diag_diagonal]
      dsimp
      rw [mul_assoc]; rw [prod_erase_mul _ _ (Finset.mem_univ _)]; rw [← det_diagonal]
      exact mul_invOf_self _
  mul_invOf_self :=
    funext fun i => by
      let : Invertible (diagonal v).det := detInvertibleOfInvertible _
      rw [invOf_eq]; rw [diag_smul]; rw [adjugate_diagonal]; rw [diag_diagonal]
      dsimp
      rw [mul_left_comm]; rw [mul_prod_erase _ _ (Finset.mem_univ _)]; rw [← det_diagonal]
      exact mul_invOf_self _

Depends on / 依赖: diagonal
-/
def invertibleOfDiagonalInvertible (v : n -> α) [Invertible (diagonal v)] : Invertible v where
  invOf := diag (⅟(diagonal v))
  invOf_mul_self :=
    funext fun i => by
      let : Invertible (diagonal v).det := detInvertibleOfInvertible _
      rw [invOf_eq]; rw [diag_smul]; rw [adjugate_diagonal]; rw [diag_diagonal]
      dsimp
      rw [mul_assoc]; rw [prod_erase_mul _ _ (Finset.mem_univ _)]; rw [← det_diagonal]
      exact mul_invOf_self _
  mul_invOf_self :=
    funext fun i => by
      let : Invertible (diagonal v).det := detInvertibleOfInvertible _
      rw [invOf_eq]; rw [diag_smul]; rw [adjugate_diagonal]; rw [diag_diagonal]
      dsimp
      rw [mul_left_comm]; rw [mul_prod_erase _ _ (Finset.mem_univ _)]; rw [← det_diagonal]
      exact mul_invOf_self _

/-- Together `Matrix.diagonalInvertible` and `Matrix.invertibleOfDiagonalInvertible` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
/--
Definition of `diagonalInvertibleEquivInvertible` / `diagonalInvertibleEquivInvertible` 的定义

English:
definition diagonalInvertibleEquivInvertible
  signature: (v : n -> α)
  body: @invertibleOfDiagonalInvertible _ _ _ _ _ _
  invFun := @diagonalInvertible _ _ _ _ _ _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 diagonalInvertibleEquivInvertible
  签名: (v : n -> α)
  定义体: @invertibleOfDiagonalInvertible _ _ _ _ _ _
  invFun := @diagonalInvertible _ _ _ _ _ _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

Depends on / 依赖: invertibleOfDiagonalInvertible
-/
def diagonalInvertibleEquivInvertible (v : n -> α) : Invertible (diagonal v) ≃ Invertible v where
  toFun := @invertibleOfDiagonalInvertible _ _ _ _ _ _
  invFun := @diagonalInvertible _ _ _ _ _ _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- When lowered to a prop, `Matrix.diagonalInvertibleEquivInvertible` forms an `iff`. -/
@[simp]
/--
theorem `isUnit_diagonal` / 定理 `isUnit_diagonal`

English:
theorem isUnit_diagonal
  given: {v : n -> α}
  statement: IsUnit (diagonal v) ↔ IsUnit v
  proof: by
  simp only [← nonempty_invertible_iff_isUnit,
    (diagonalInvertibleEquivInvertible v).nonempty_congr]

中文:
定理 isUnit_diagonal
  条件: {v : n -> α}
  结论: 是单位 (diagonal v) ↔ 是单位 v
  证明: by
  simp only [← nonempty_invertible_iff_isUnit,
    (diagonalInvertibleEquivInvertible v).nonempty_congr]

Depends on / 依赖: diagonalInvertibleEquivInvertible, nonempty_congr, nonempty_invertible_iff_isUnit
-/
theorem isUnit_diagonal {v : n -> α} : IsUnit (diagonal v) ↔ IsUnit v := by
  simp only [← nonempty_invertible_iff_isUnit,
    (diagonalInvertibleEquivInvertible v).nonempty_congr]

/--
theorem `inv_diagonal` / 定理 `inv_diagonal`

English:
theorem inv_diagonal
  given: (v : n -> α)
  statement: (diagonal v)⁻¹ = diagonal v⁻¹ʳ
  proof: by
  rw [nonsing_inv_eq_ringInverse]
  by_cases h : IsUnit v
  · have := isUnit_diagonal.mpr h
    cases this.nonempty_invertible
    cases h.nonempty_invertible
    rw [Ring.inverse_invertible]; rw [Ring.inverse_invertible]; rw [invOf_diagonal_eq]
  · have := isUnit_diagonal.not.mpr h
    rw [Ring.inverse_non_unit _ h]; rw [Pi.zero_def]; rw [diagonal_zero]; rw [Ring.inverse_non_unit _ this]

中文:
定理 inv_diagonal
  条件: (v : n -> α)
  结论: (diagonal v)⁻¹ = diagonal v⁻¹ʳ
  证明: by
  rw [nonsing_inv_eq_ringInverse]
  by_cases h : IsUnit v
  · have := isUnit_diagonal.mpr h
    cases this.nonempty_invertible
    cases h.nonempty_invertible
    rw [Ring.inverse_invertible]; rw [Ring.inverse_invertible]; rw [invOf_diagonal_eq]
  · have := isUnit_diagonal.not.mpr h
    rw [Ring.inverse_non_unit _ h]; rw [Pi.zero_def]; rw [diagonal_zero]; rw [Ring.inverse_non_unit _ this]

Depends on / 依赖: IsUnit, Pi.zero_def, Ring.inverse_invertible, Ring.inverse_non_unit, diagonal_zero, h.nonempty_invertible, invOf_diagonal_eq, inverse_invertible, inverse_non_unit, isUnit_diagonal, isUnit_diagonal.mpr, isUnit_diagonal.not.mpr, nonempty_invertible, nonsing_inv_eq_ringInverse, this.nonempty_invertible, zero_def
-/
theorem inv_diagonal (v : n -> α) : (diagonal v)⁻¹ = diagonal v⁻¹ʳ := by
  rw [nonsing_inv_eq_ringInverse]
  by_cases h : IsUnit v
  · have := isUnit_diagonal.mpr h
    cases this.nonempty_invertible
    cases h.nonempty_invertible
    rw [Ring.inverse_invertible]; rw [Ring.inverse_invertible]; rw [invOf_diagonal_eq]
  · have := isUnit_diagonal.not.mpr h
    rw [Ring.inverse_non_unit _ h]; rw [Pi.zero_def]; rw [diagonal_zero]; rw [Ring.inverse_non_unit _ this]

end Diagonal

/-- The inverse of a 1×1 or 0×0 matrix is always diagonal.

While we could write this as `of fun _ _ => (A default default)⁻¹ʳ` on the RHS, this is
less useful because:

* It wouldn't work for 0×0 matrices.
* More things are true about diagonal matrices than constant matrices, and so more lemmas exist.

`Matrix.diagonal_unique` can be used to reach this form, while `Ring.inverse_eq_inv` can be used
to replace `Ring.inverse` with `⁻¹`.
-/
@[simp]
/--
theorem `inv_subsingleton` / 定理 `inv_subsingleton`

English:
theorem inv_subsingleton
  given: [Subsingleton m] [Fintype m] [DecidableEq m] (A : Matrix m m α)
  proof: by
  rw [inv_def]; rw [adjugate_subsingleton]; rw [smul_one_eq_diagonal]
  congr! with i
  exact det_eq_elem_of_subsingleton _ _

中文:
定理 inv_subsingleton
  条件: [子单例 m] [有限类型 m] [DecidableEq m] (A : 矩阵 m m α)
  证明: by
  rw [inv_def]; rw [adjugate_subsingleton]; rw [smul_one_eq_diagonal]
  congr! with i
  exact det_eq_elem_of_subsingleton _ _

Depends on / 依赖: adjugate_subsingleton, det_eq_elem_of_subsingleton, inv_def, smul_one_eq_diagonal
-/
theorem inv_subsingleton [Subsingleton m] [Fintype m] [DecidableEq m] (A : Matrix m m α) :
    A⁻¹ = diagonal fun i => (A i i)⁻¹ʳ := by
  rw [inv_def]; rw [adjugate_subsingleton]; rw [smul_one_eq_diagonal]
  congr! with i
  exact det_eq_elem_of_subsingleton _ _

section Woodbury

variable [Fintype m] [DecidableEq m]
variable (A : Matrix n n α) (U : Matrix n m α) (C : Matrix m m α) (V : Matrix m n α)

/--
theorem `add_mul_mul_inv_eq_sub` / 定理 `add_mul_mul_inv_eq_sub`

English:
theorem add_mul_mul_inv_eq_sub
  given: (hA : IsUnit A) (hC : IsUnit C) (hAC : IsUnit (C⁻¹ + V * A⁻¹ * U))
  proof: by
  obtain ⟨_⟩ := hA.nonempty_invertible
  obtain ⟨_⟩ := hC.nonempty_invertible
  obtain ⟨iAC⟩ := hAC.nonempty_invertible
  simp only [← invOf_eq_nonsing_inv] at iAC
  let := invertibleAddMulMul A U C V
  simp only [← invOf_eq_nonsing_inv]
  apply invOf_add_mul_mul

中文:
定理 add_mul_mul_inv_eq_sub
  条件: (hA : 是单位 A) (hC : 是单位 C) (hAC : 是单位 (C⁻¹ + V * A⁻¹ * U))
  证明: by
  obtain ⟨_⟩ := hA.nonempty_invertible
  obtain ⟨_⟩ := hC.nonempty_invertible
  obtain ⟨iAC⟩ := hAC.nonempty_invertible
  simp only [← invOf_eq_nonsing_inv] at iAC
  let := invertibleAddMulMul A U C V
  simp only [← invOf_eq_nonsing_inv]
  apply invOf_add_mul_mul

Depends on / 依赖: hA.nonempty_invertible, hAC.nonempty_invertible, hC.nonempty_invertible, invOf_add_mul_mul, invOf_eq_nonsing_inv, invertibleAddMulMul, nonempty_invertible
-/
theorem add_mul_mul_inv_eq_sub (hA : IsUnit A) (hC : IsUnit C) (hAC : IsUnit (C⁻¹ + V * A⁻¹ * U)) :
    (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ := by
  obtain ⟨_⟩ := hA.nonempty_invertible
  obtain ⟨_⟩ := hC.nonempty_invertible
  obtain ⟨iAC⟩ := hAC.nonempty_invertible
  simp only [← invOf_eq_nonsing_inv] at iAC
  let := invertibleAddMulMul A U C V
  simp only [← invOf_eq_nonsing_inv]
  apply invOf_add_mul_mul

/--
theorem `add_mul_mul_inv_eq_sub'` / 定理 `add_mul_mul_inv_eq_sub'`

English:
theorem add_mul_mul_inv_eq_sub'
  given: (hA : IsUnit A) (h : IsUnit (C + C * V * A⁻¹ * U * C))
  proof: by
  obtain ⟨_⟩ := hA.nonempty_invertible
  obtain ⟨ih⟩ := h.nonempty_invertible
  simp only [← invOf_eq_nonsing_inv] at ih
  let := invertibleAddMulMul' A U C V
  simp only [← invOf_eq_nonsing_inv]
  apply invOf_add_mul_mul'

中文:
定理 add_mul_mul_inv_eq_sub'
  条件: (hA : 是单位 A) (h : 是单位 (C + C * V * A⁻¹ * U * C))
  证明: by
  obtain ⟨_⟩ := hA.nonempty_invertible
  obtain ⟨ih⟩ := h.nonempty_invertible
  simp only [← invOf_eq_nonsing_inv] at ih
  let := invertibleAddMulMul' A U C V
  simp only [← invOf_eq_nonsing_inv]
  apply invOf_add_mul_mul'

Depends on / 依赖: h.nonempty_invertible, hA.nonempty_invertible, invOf_add_mul_mul, invOf_eq_nonsing_inv, invertibleAddMulMul, nonempty_invertible
-/
theorem add_mul_mul_inv_eq_sub' (hA : IsUnit A) (h : IsUnit (C + C * V * A⁻¹ * U * C)) :
    (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * C * (C + C * V * A⁻¹ * U * C)⁻¹ * C * V * A⁻¹ := by
  obtain ⟨_⟩ := hA.nonempty_invertible
  obtain ⟨ih⟩ := h.nonempty_invertible
  simp only [← invOf_eq_nonsing_inv] at ih
  let := invertibleAddMulMul' A U C V
  simp only [← invOf_eq_nonsing_inv]
  apply invOf_add_mul_mul'

end Woodbury

@[simp]
/--
theorem `inv_inv_inv` / 定理 `inv_inv_inv`

English:
theorem inv_inv_inv
  given: (A : Matrix n n α)
  statement: A⁻¹⁻¹⁻¹ = A⁻¹
  proof: by
  by_cases h : IsUnit A.det
  · rw [nonsing_inv_nonsing_inv _ h]
  · simp [nonsing_inv_apply_not_isUnit _ h]

中文:
定理 inv_inv_inv
  条件: (A : 矩阵 n n α)
  结论: A⁻¹⁻¹⁻¹ = A⁻¹
  证明: by
  by_cases h : IsUnit A.det
  · rw [nonsing_inv_nonsing_inv _ h]
  · simp [nonsing_inv_apply_not_isUnit _ h]

Depends on / 依赖: A.det, IsUnit, nonsing_inv_apply_not_isUnit, nonsing_inv_nonsing_inv
-/
theorem inv_inv_inv (A : Matrix n n α) : A⁻¹⁻¹⁻¹ = A⁻¹ := by
  by_cases h : IsUnit A.det
  · rw [nonsing_inv_nonsing_inv _ h]
  · simp [nonsing_inv_apply_not_isUnit _ h]

/--
theorem `inv_add_inv` / 定理 `inv_add_inv`

English:
theorem inv_add_inv
  given: {A B : Matrix n n α} (h : IsUnit A ↔ IsUnit B)
  proof: by
  simpa only [nonsing_inv_eq_ringInverse] using Ring.inverse_add_inverse h

中文:
定理 inv_add_inv
  条件: {A B : 矩阵 n n α} (h : 是单位 A ↔ 是单位 B)
  证明: by
  simpa only [nonsing_inv_eq_ringInverse] using Ring.inverse_add_inverse h

Depends on / 依赖: Ring.inverse_add_inverse, inverse_add_inverse, nonsing_inv_eq_ringInverse
-/
theorem inv_add_inv {A B : Matrix n n α} (h : IsUnit A ↔ IsUnit B) :
    A⁻¹ + B⁻¹ = A⁻¹ * (A + B) * B⁻¹ := by
  simpa only [nonsing_inv_eq_ringInverse] using Ring.inverse_add_inverse h

/--
theorem `inv_sub_inv` / 定理 `inv_sub_inv`

English:
theorem inv_sub_inv
  given: {A B : Matrix n n α} (h : IsUnit A ↔ IsUnit B)
  proof: by
  simpa only [nonsing_inv_eq_ringInverse] using Ring.inverse_sub_inverse h

中文:
定理 inv_sub_inv
  条件: {A B : 矩阵 n n α} (h : 是单位 A ↔ 是单位 B)
  证明: by
  simpa only [nonsing_inv_eq_ringInverse] using Ring.inverse_sub_inverse h

Depends on / 依赖: Ring.inverse_sub_inverse, inverse_sub_inverse, nonsing_inv_eq_ringInverse
-/
theorem inv_sub_inv {A B : Matrix n n α} (h : IsUnit A ↔ IsUnit B) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  simpa only [nonsing_inv_eq_ringInverse] using Ring.inverse_sub_inverse h

/--
theorem `mul_inv_rev` / 定理 `mul_inv_rev`

English:
theorem mul_inv_rev
  given: (A B : Matrix n n α)
  statement: (A * B)⁻¹ = B⁻¹ * A⁻¹
  proof: by
  simp only [inv_def]
  rw [Matrix.smul_mul]; rw [Matrix.mul_smul]; rw [smul_smul]; rw [det_mul]; rw [adjugate_mul_distrib]; rw [Ring.mul_inverse_rev]

中文:
定理 mul_inv_rev
  条件: (A B : 矩阵 n n α)
  结论: (A * B)⁻¹ = B⁻¹ * A⁻¹
  证明: by
  simp only [inv_def]
  rw [Matrix.smul_mul]; rw [Matrix.mul_smul]; rw [smul_smul]; rw [det_mul]; rw [adjugate_mul_distrib]; rw [Ring.mul_inverse_rev]

Depends on / 依赖: Matrix, Matrix.mul_smul, Matrix.smul_mul, Ring.mul_inverse_rev, adjugate_mul_distrib, det_mul, inv_def, mul_inverse_rev, mul_smul, smul_mul, smul_smul
-/
theorem mul_inv_rev (A B : Matrix n n α) : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
  simp only [inv_def]
  rw [Matrix.smul_mul]; rw [Matrix.mul_smul]; rw [smul_smul]; rw [det_mul]; rw [adjugate_mul_distrib]; rw [Ring.mul_inverse_rev]

/--
theorem `list_prod_inv_reverse` / 定理 `list_prod_inv_reverse`

English:
theorem list_prod_inv_reverse
  statement: forall l : List (Matrix n n α), l.prod⁻¹ = (l.reverse.map Inv.inv).prod

中文:
定理 list_prod_inv_reverse
  结论: 对任意 l : 列表 (矩阵 n n α), l.乘积⁻¹ = (l.reverse.map 取逆.inv).乘积
-/
theorem list_prod_inv_reverse : forall l : List (Matrix n n α), l.prod⁻¹ = (l.reverse.map Inv.inv).prod
  | [] => by rw [List.reverse_nil, List.map_nil, List.prod_nil, inv_one]
  | A::Xs => by
    rw [List.reverse_cons']; rw [List.map_concat]; rw [List.prod_concat]; rw [List.prod_cons]; rw [mul_inv_rev]; rw [list_prod_inv_reverse Xs]

/-- One form of **Cramer's rule**. See `Matrix.mulVec_cramer` for a stronger form. -/
@[simp]
/--
theorem `det_smul_inv_mulVec_eq_cramer` / 定理 `det_smul_inv_mulVec_eq_cramer`

English:
theorem det_smul_inv_mulVec_eq_cramer
  given: (A : Matrix n n α) (b : n -> α) (h : IsUnit A.det)
  proof: by
  rw [cramer_eq_adjugate_mulVec]; rw [A.nonsing_inv_apply h]; rw [← smul_mulVec]; rw [smul_smul]; rw [h.mul_val_inv]; rw [one_smul]

中文:
定理 det_smul_inv_mulVec_eq_cramer
  条件: (A : 矩阵 n n α) (b : n -> α) (h : 是单位 A.det)
  证明: by
  rw [cramer_eq_adjugate_mulVec]; rw [A.nonsing_inv_apply h]; rw [← smul_mulVec]; rw [smul_smul]; rw [h.mul_val_inv]; rw [one_smul]

Depends on / 依赖: A.nonsing_inv_apply, cramer_eq_adjugate_mulVec, h.mul_val_inv, mul_val_inv, nonsing_inv_apply, one_smul, smul_mulVec, smul_smul
-/
theorem det_smul_inv_mulVec_eq_cramer (A : Matrix n n α) (b : n -> α) (h : IsUnit A.det) :
    A.det • A⁻¹ *ᵥ b = cramer A b := by
  rw [cramer_eq_adjugate_mulVec]; rw [A.nonsing_inv_apply h]; rw [← smul_mulVec]; rw [smul_smul]; rw [h.mul_val_inv]; rw [one_smul]

/-- One form of **Cramer's rule**. See `Matrix.mulVec_cramer` for a stronger form. -/
@[simp]
/--
theorem `det_smul_inv_vecMul_eq_cramer_transpose` / 定理 `det_smul_inv_vecMul_eq_cramer_transpose`

English:
theorem det_smul_inv_vecMul_eq_cramer_transpose
  given: (A : Matrix n n α) (b : n -> α) (h : IsUnit A.det)
  proof: by
  rw [← A⁻¹.transpose_transpose]; rw [vecMul_transpose]; rw [transpose_nonsing_inv]; rw [← det_transpose]; rw [Aᵀ.det_smul_inv_mulVec_eq_cramer _ (isUnit_det_transpose A h)]

中文:
定理 det_smul_inv_vecMul_eq_cramer_transpose
  条件: (A : 矩阵 n n α) (b : n -> α) (h : 是单位 A.det)
  证明: by
  rw [← A⁻¹.transpose_transpose]; rw [vecMul_transpose]; rw [transpose_nonsing_inv]; rw [← det_transpose]; rw [Aᵀ.det_smul_inv_mulVec_eq_cramer _ (isUnit_det_transpose A h)]

Depends on / 依赖: det_smul_inv_mulVec_eq_cramer, det_transpose, isUnit_det_transpose, transpose_nonsing_inv, transpose_transpose, vecMul_transpose
-/
theorem det_smul_inv_vecMul_eq_cramer_transpose (A : Matrix n n α) (b : n -> α) (h : IsUnit A.det) :
    A.det • b ᵥ* A⁻¹ = cramer Aᵀ b := by
  rw [← A⁻¹.transpose_transpose]; rw [vecMul_transpose]; rw [transpose_nonsing_inv]; rw [← det_transpose]; rw [Aᵀ.det_smul_inv_mulVec_eq_cramer _ (isUnit_det_transpose A h)]

/-! ### Inverses of permutated matrices

Note that the simp-normal form of `Matrix.reindex` is `Matrix.submatrix`, so we prove most of these
results about only the latter.
-/


section Submatrix

variable [Fintype m]
variable [DecidableEq m]

/-- `A.submatrix e₁ e₂` is invertible if `A` is -/
@[instance_reducible]
/--
Definition of `submatrixEquivInvertible` / `submatrixEquivInvertible` 的定义

English:
definition submatrixEquivInvertible
  signature: (A : Matrix m m α) (e₁ e₂ : n ≃ m) [Invertible A]
  body: invertibleOfRightInverse _ ((⅟A).submatrix e₂ e₁) by
    rw [Matrix.submatrix_mul_equiv]; rw [mul_invOf_self]; rw [submatrix_one_equiv]

中文:
定义 submatrixEquivInvertible
  签名: (A : 矩阵 m m α) (e₁ e₂ : n ≃ m) [可逆 A]
  定义体: invertibleOfRightInverse _ ((⅟A).submatrix e₂ e₁) by
    rw [Matrix.submatrix_mul_equiv]; rw [mul_invOf_self]; rw [submatrix_one_equiv]

Depends on / 依赖: Matrix, Matrix.submatrix_mul_equiv, invertibleOfRightInverse, mul_invOf_self, submatrix, submatrix_mul_equiv, submatrix_one_equiv
-/
def submatrixEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m) [Invertible A] :
    Invertible (A.submatrix e₁ e₂) :=
invertibleOfRightInverse _ ((⅟A).submatrix e₂ e₁) by
    rw [Matrix.submatrix_mul_equiv]; rw [mul_invOf_self]; rw [submatrix_one_equiv]

/-- `A` is invertible if `A.submatrix e₁ e₂` is -/
@[instance_reducible]
/--
Definition of `invertibleOfSubmatrixEquivInvertible` / `invertibleOfSubmatrixEquivInvertible` 的定义

English:
definition invertibleOfSubmatrixEquivInvertible
  signature: (A : Matrix m m α) (e₁ e₂ : n ≃ m)
  body: invertibleOfRightInverse _ ((⅟(A.submatrix e₁ e₂)).submatrix e₂.symm e₁.symm) by
    have : A = (A.submatrix e₁ e₂).submatrix e₁.symm e₂.symm := by simp
    conv in _ * _ =>
      congr
      rw [this]
    rw [Matrix.submatrix_mul_equiv]; rw [mul_invOf_self]; rw [submatrix_one_equiv]

中文:
定义 invertibleOfSubmatrixEquivInvertible
  签名: (A : 矩阵 m m α) (e₁ e₂ : n ≃ m)
  定义体: invertibleOfRightInverse _ ((⅟(A.submatrix e₁ e₂)).submatrix e₂.symm e₁.symm) by
    have : A = (A.submatrix e₁ e₂).submatrix e₁.symm e₂.symm := by simp
    conv in _ * _ =>
      congr
      rw [this]
    rw [Matrix.submatrix_mul_equiv]; rw [mul_invOf_self]; rw [submatrix_one_equiv]

Depends on / 依赖: A.submatrix, Matrix, Matrix.submatrix_mul_equiv, invertibleOfRightInverse, mul_invOf_self, submatrix, submatrix_mul_equiv, submatrix_one_equiv
-/
def invertibleOfSubmatrixEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m)
    [Invertible (A.submatrix e₁ e₂)] : Invertible A :=
invertibleOfRightInverse _ ((⅟(A.submatrix e₁ e₂)).submatrix e₂.symm e₁.symm) by
    have : A = (A.submatrix e₁ e₂).submatrix e₁.symm e₂.symm := by simp
    conv in _ * _ =>
      congr
      rw [this]
    rw [Matrix.submatrix_mul_equiv]; rw [mul_invOf_self]; rw [submatrix_one_equiv]

/--
theorem `invOf_submatrix_equiv_eq` / 定理 `invOf_submatrix_equiv_eq`

English:
theorem invOf_submatrix_equiv_eq
  statement: (A : Matrix m m α) (e₁ e₂ : n ≃ m) [Invertible A]
  proof: by
  rw [@Invertible.congr _ _ _ _ _ (submatrixEquivInvertible A e₁ e₂) rfl]
  rfl

中文:
定理 invOf_submatrix_equiv_eq
  结论: (A : 矩阵 m m α) (e₁ e₂ : n ≃ m) [可逆 A]
  证明: by
  rw [@Invertible.congr _ _ _ _ _ (submatrixEquivInvertible A e₁ e₂) rfl]
  rfl

Depends on / 依赖: Invertible, Invertible.congr, submatrixEquivInvertible
-/
theorem invOf_submatrix_equiv_eq (A : Matrix m m α) (e₁ e₂ : n ≃ m) [Invertible A]
    [Invertible (A.submatrix e₁ e₂)] : ⅟(A.submatrix e₁ e₂) = (⅟A).submatrix e₂ e₁ := by
  rw [@Invertible.congr _ _ _ _ _ (submatrixEquivInvertible A e₁ e₂) rfl]
  rfl

/-- Together `Matrix.submatrixEquivInvertible` and
`Matrix.invertibleOfSubmatrixEquivInvertible` form an equivalence, although both sides of the
equiv are subsingleton anyway. -/
@[simps]
/--
Definition of `submatrixEquivInvertibleEquivInvertible` / `submatrixEquivInvertibleEquivInvertible` 的定义

English:
definition submatrixEquivInvertibleEquivInvertible
  signature: (A : Matrix m m α) (e₁ e₂ : n ≃ m)
  body: invertibleOfSubmatrixEquivInvertible A e₁ e₂
  invFun _ := submatrixEquivInvertible A e₁ e₂
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 submatrixEquivInvertibleEquivInvertible
  签名: (A : 矩阵 m m α) (e₁ e₂ : n ≃ m)
  定义体: invertibleOfSubmatrixEquivInvertible A e₁ e₂
  invFun _ := submatrixEquivInvertible A e₁ e₂
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

Depends on / 依赖: invertibleOfSubmatrixEquivInvertible
-/
def submatrixEquivInvertibleEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m) :
    Invertible (A.submatrix e₁ e₂) ≃ Invertible A where
  toFun _ := invertibleOfSubmatrixEquivInvertible A e₁ e₂
  invFun _ := submatrixEquivInvertible A e₁ e₂
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- When lowered to a prop, `Matrix.invertibleOfSubmatrixEquivInvertible` forms an `iff`. -/
@[simp]
/--
theorem `isUnit_submatrix_equiv` / 定理 `isUnit_submatrix_equiv`

English:
theorem isUnit_submatrix_equiv
  given: {A : Matrix m m α} (e₁ e₂ : n ≃ m)
  proof: by
  simp only [← nonempty_invertible_iff_isUnit,
    (submatrixEquivInvertibleEquivInvertible A _ _).nonempty_congr]

@[simp]

中文:
定理 isUnit_submatrix_equiv
  条件: {A : 矩阵 m m α} (e₁ e₂ : n ≃ m)
  证明: by
  simp only [← nonempty_invertible_iff_isUnit,
    (submatrixEquivInvertibleEquivInvertible A _ _).nonempty_congr]

@[simp]

Depends on / 依赖: nonempty_congr, nonempty_invertible_iff_isUnit, submatrixEquivInvertibleEquivInvertible
-/
theorem isUnit_submatrix_equiv {A : Matrix m m α} (e₁ e₂ : n ≃ m) :
    IsUnit (A.submatrix e₁ e₂) ↔ IsUnit A := by
  simp only [← nonempty_invertible_iff_isUnit,
    (submatrixEquivInvertibleEquivInvertible A _ _).nonempty_congr]

@[simp]
/--
theorem `inv_submatrix_equiv` / 定理 `inv_submatrix_equiv`

English:
theorem inv_submatrix_equiv
  given: (A : Matrix m m α) (e₁ e₂ : n ≃ m)
  proof: by
  by_cases h : IsUnit A
  · cases h.nonempty_invertible
    let := submatrixEquivInvertible A e₁ e₂
    rw [← invOf_eq_nonsing_inv]; rw [← invOf_eq_nonsing_inv]; rw [invOf_submatrix_equiv_eq A]
  · have := (isUnit_submatrix_equiv e₁ e₂).not.mpr h
    simp_rw [nonsing_inv_eq_ringInverse, Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ this,
      submatrix_zero, Pi.zero_apply]

中文:
定理 inv_submatrix_equiv
  条件: (A : 矩阵 m m α) (e₁ e₂ : n ≃ m)
  证明: by
  by_cases h : IsUnit A
  · cases h.nonempty_invertible
    let := submatrixEquivInvertible A e₁ e₂
    rw [← invOf_eq_nonsing_inv]; rw [← invOf_eq_nonsing_inv]; rw [invOf_submatrix_equiv_eq A]
  · have := (isUnit_submatrix_equiv e₁ e₂).not.mpr h
    simp_rw [nonsing_inv_eq_ringInverse, Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ this,
      submatrix_zero, Pi.zero_apply]

Depends on / 依赖: IsUnit, Pi.zero_apply, Ring.inverse_non_unit, h.nonempty_invertible, invOf_eq_nonsing_inv, invOf_submatrix_equiv_eq, inverse_non_unit, isUnit_submatrix_equiv, nonempty_invertible, nonsing_inv_eq_ringInverse, not.mpr, simp_rw, submatrixEquivInvertible, submatrix_zero, zero_apply
-/
theorem inv_submatrix_equiv (A : Matrix m m α) (e₁ e₂ : n ≃ m) :
    (A.submatrix e₁ e₂)⁻¹ = A⁻¹.submatrix e₂ e₁ := by
  by_cases h : IsUnit A
  · cases h.nonempty_invertible
    let := submatrixEquivInvertible A e₁ e₂
    rw [← invOf_eq_nonsing_inv]; rw [← invOf_eq_nonsing_inv]; rw [invOf_submatrix_equiv_eq A]
  · have := (isUnit_submatrix_equiv e₁ e₂).not.mpr h
    simp_rw [nonsing_inv_eq_ringInverse, Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ this,
      submatrix_zero, Pi.zero_apply]

/--
theorem `inv_reindex` / 定理 `inv_reindex`

English:
theorem inv_reindex
  given: (e₁ e₂ : n ≃ m) (A : Matrix n n α)
  statement: (reindex e₁ e₂ A)⁻¹ = reindex e₂ e₁ A⁻¹
  proof: inv_submatrix_equiv A e₁.symm e₂.symm

中文:
定理 inv_reindex
  条件: (e₁ e₂ : n ≃ m) (A : 矩阵 n n α)
  结论: (reindex e₁ e₂ A)⁻¹ = reindex e₂ e₁ A⁻¹
  证明: inv_submatrix_equiv A e₁.symm e₂.symm

Depends on / 依赖: inv_submatrix_equiv
-/
theorem inv_reindex (e₁ e₂ : n ≃ m) (A : Matrix n n α) : (reindex e₁ e₂ A)⁻¹ = reindex e₂ e₁ A⁻¹ :=
  inv_submatrix_equiv A e₁.symm e₂.symm

end Submatrix

open scoped Kronecker in
/--
theorem `inv_kronecker` / 定理 `inv_kronecker`

English:
theorem inv_kronecker
  statement: [Fintype m] [DecidableEq m]
  proof: by
  -- handle the special cases where either matrix is not invertible
  by_cases hA : IsUnit A.det
  swap
  · cases isEmpty_or_nonempty n
    · subsingleton
    have hAB : ¬IsUnit (A otimesₖ B).det := by
      refine mt (fun hAB => ?_) hA
      rw [det_kronecker] at hAB
      exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_left hAB)
    rw [nonsing_inv_apply_not_isUnit _ hA]; rw [zero_kronecker]; rw [nonsing_inv_apply_not_isUnit _ hAB]
  by_cases hB : IsUnit B.det; swap
  · cases isEmpty_or_nonempty m
    · subsingleton
    have hAB : ¬IsUnit (A otimesₖ B).det := by
      refine mt (fun hAB => ?_) hB
      rw [det_kronecker] at hAB
      exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_right hAB)
    rw [nonsing_inv_apply_not_isUnit _ hB]; rw [kronecker_zero]; rw [nonsing_inv_apply_not_isUnit _ hAB]
  -- otherwise follows trivially from `mul_kronecker_mul`
  · apply inv_eq_right_inv
    rw [← mul_kronecker_mul]; rw [← one_kronecker_one]; rw [mul_nonsing_inv _ hA]; rw [mul_nonsing_inv _ hB]

中文:
定理 inv_kronecker
  结论: [有限类型 m] [DecidableEq m]
  证明: by
  -- handle the special cases where either matrix is not invertible
  by_cases hA : IsUnit A.det
  swap
  · cases isEmpty_or_nonempty n
    · subsingleton
    have hAB : ¬IsUnit (A otimesₖ B).det := by
      refine mt (fun hAB => ?_) hA
      rw [det_kronecker] at hAB
      exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_left hAB)
    rw [nonsing_inv_apply_not_isUnit _ hA]; rw [zero_kronecker]; rw [nonsing_inv_apply_not_isUnit _ hAB]
  by_cases hB : IsUnit B.det; swap
  · cases isEmpty_or_nonempty m
    · subsingleton
    have hAB : ¬IsUnit (A otimesₖ B).det := by
      refine mt (fun hAB => ?_) hB
      rw [det_kronecker] at hAB
      exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_right hAB)
    rw [nonsing_inv_apply_not_isUnit _ hB]; rw [kronecker_zero]; rw [nonsing_inv_apply_not_isUnit _ hAB]
  -- otherwise follows trivially from `mul_kronecker_mul`
  · apply inv_eq_right_inv
    rw [← mul_kronecker_mul]; rw [← one_kronecker_one]; rw [mul_nonsing_inv _ hA]; rw [mul_nonsing_inv _ hB]
-/
theorem inv_kronecker [Fintype m] [DecidableEq m]
    (A : Matrix m m α) (B : Matrix n n α) : (A otimesₖ B)⁻¹ = A⁻¹ otimesₖ B⁻¹ := by
  -- handle the special cases where either matrix is not invertible
  by_cases hA : IsUnit A.det
  swap
  · cases isEmpty_or_nonempty n
    · subsingleton
    have hAB : ¬IsUnit (A otimesₖ B).det := by
      refine mt (fun hAB => ?_) hA
      rw [det_kronecker] at hAB
      exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_left hAB)
    rw [nonsing_inv_apply_not_isUnit _ hA]; rw [zero_kronecker]; rw [nonsing_inv_apply_not_isUnit _ hAB]
  by_cases hB : IsUnit B.det; swap
  · cases isEmpty_or_nonempty m
    · subsingleton
    have hAB : ¬IsUnit (A otimesₖ B).det := by
      refine mt (fun hAB => ?_) hB
      rw [det_kronecker] at hAB
      exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_right hAB)
    rw [nonsing_inv_apply_not_isUnit _ hB]; rw [kronecker_zero]; rw [nonsing_inv_apply_not_isUnit _ hAB]
  -- otherwise follows trivially from `mul_kronecker_mul`
  · apply inv_eq_right_inv
    rw [← mul_kronecker_mul]; rw [← one_kronecker_one]; rw [mul_nonsing_inv _ hA]; rw [mul_nonsing_inv _ hB]


/-! ### More results about determinants -/


section Det

variable [Fintype m] [DecidableEq m]

/--
theorem `det_conj` / 定理 `det_conj`

English:
theorem det_conj
  given: {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α)
  proof: by rw [← h.unit_spec, ← coe_units_inv, det_units_conj]

中文:
定理 det_conj
  条件: {M : 矩阵 m m α} (h : 是单位 M) (N : 矩阵 m m α)
  证明: by rw [← h.unit_spec, ← coe_units_inv, det_units_conj]

Depends on / 依赖: coe_units_inv, det_units_conj, h.unit_spec, unit_spec
-/
theorem det_conj {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) :
    det (M * N * M⁻¹) = det N := by rw [← h.unit_spec, ← coe_units_inv, det_units_conj]

/--
theorem `det_conj'` / 定理 `det_conj'`

English:
theorem det_conj'
  given: {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α)
  proof: by rw [← h.unit_spec, ← coe_units_inv, det_units_conj']

中文:
定理 det_conj'
  条件: {M : 矩阵 m m α} (h : 是单位 M) (N : 矩阵 m m α)
  证明: by rw [← h.unit_spec, ← coe_units_inv, det_units_conj']

Depends on / 依赖: coe_units_inv, det_units_conj, h.unit_spec, unit_spec
-/
theorem det_conj' {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) :
    det (M⁻¹ * N * M) = det N := by rw [← h.unit_spec, ← coe_units_inv, det_units_conj']

end Det

/-! ### More results about traces -/


section trace

variable [Fintype m] [DecidableEq m]

/--
theorem `trace_conj` / 定理 `trace_conj`

English:
theorem trace_conj
  given: {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α)
  proof: by rw [← h.unit_spec, ← coe_units_inv, trace_units_conj]

中文:
定理 trace_conj
  条件: {M : 矩阵 m m α} (h : 是单位 M) (N : 矩阵 m m α)
  证明: by rw [← h.unit_spec, ← coe_units_inv, trace_units_conj]

Depends on / 依赖: coe_units_inv, h.unit_spec, trace_units_conj, unit_spec
-/
theorem trace_conj {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) :
    trace (M * N * M⁻¹) = trace N := by rw [← h.unit_spec, ← coe_units_inv, trace_units_conj]

/--
theorem `trace_conj'` / 定理 `trace_conj'`

English:
theorem trace_conj'
  given: {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α)
  proof: by rw [← h.unit_spec, ← coe_units_inv, trace_units_conj']

中文:
定理 trace_conj'
  条件: {M : 矩阵 m m α} (h : 是单位 M) (N : 矩阵 m m α)
  证明: by rw [← h.unit_spec, ← coe_units_inv, trace_units_conj']

Depends on / 依赖: coe_units_inv, h.unit_spec, trace_units_conj, unit_spec
-/
theorem trace_conj' {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) :
    trace (M⁻¹ * N * M) = trace N := by rw [← h.unit_spec, ← coe_units_inv, trace_units_conj']

end trace

end Matrix
