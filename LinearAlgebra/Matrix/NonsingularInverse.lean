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
/-
**Matrix.invertibleOfDetInvertible** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：invertibleOfDetInvertible [Invertible A.det] : Invertible A where invOf
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A.det` has a constructive inverse, produce one for `A`.
-/
def invertibleOfDetInvertible [Invertible A.det] : Invertible A where
  invOf := ⅟A.det • A.adjugate
  mul_invOf_self := by
    rw [mul_smul_comm, mul_adjugate, smul_smul, invOf_mul_self, one_smul]
  invOf_mul_self := by
    rw [smul_mul_assoc, adjugate_mul, smul_smul, invOf_mul_self, one_smul]
/-
**Matrix.invOf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：invOf_eq [Invertible A.det] [Invertible A] : ⅟A = ⅟A.det • A.adjugate
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Invertible.congr`：Invertible.congr [Invertible a] [Invertible b] (h : a 
= b) : ⅟a = ⅟b
-/
theorem invOf_eq [Invertible A.det] [Invertible A] : ⅟A = ⅟A.det • A.adjugate := by
  let := invertibleOfDetInvertible A
  convert! (rfl : ⅟A = _)

/-- `A.det` is invertible if `A` has a left inverse. -/
@[instance_reducible]
/-
**Matrix.detInvertibleOfLeftInverse** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：detInvertibleOfLeftInverse (h : B * A = 1) : Invertible A.det where invOf
参数：h : B * A = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A.det` is invertible if `A` has a left inverse.
-/
def detInvertibleOfLeftInverse (h : B * A = 1) : Invertible A.det where
  invOf := B.det
  mul_invOf_self := by rw [mul_comm, ← det_mul, h, det_one]
  invOf_mul_self := by rw [← det_mul, h, det_one]

/-- `A.det` is invertible if `A` has a right inverse. -/
@[instance_reducible]
/-
**Matrix.detInvertibleOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：detInvertibleOfRightInverse (h : A * B = 1) : Invertible A.det where invOf
参数：h : A * B = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A.det` is invertible if `A` has a right inverse.
-/
def detInvertibleOfRightInverse (h : A * B = 1) : Invertible A.det where
  invOf := B.det
  mul_invOf_self := by rw [← det_mul, h, det_one]
  invOf_mul_self := by rw [mul_comm, ← det_mul, h, det_one]

/-- If `A` has a constructive inverse, produce one for `A.det`. -/
@[instance_reducible]
/-
**Matrix.detInvertibleOfInvertible** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：detInvertibleOfInvertible [Invertible A] : Invertible A.det
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` has a constructive inverse, produce one for `A.det`.
-/
def detInvertibleOfInvertible [Invertible A] : Invertible A.det :=
  detInvertibleOfLeftInverse A (⅟A) (invOf_mul_self _)
/-
**Matrix.det_invOf** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_invOf [Invertible A] [Invertible A.det] : (⅟A).det = ⅟A.det
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Invertible.congr`：Invertible.congr [Invertible a] [Invertible b] (h : a 
= b) : ⅟a = ⅟b
-/
theorem det_invOf [Invertible A] [Invertible A.det] : (⅟A).det = ⅟A.det := by
  let := detInvertibleOfInvertible A
  convert! (rfl : _ = ⅟A.det)

/-- Together `Matrix.detInvertibleOfInvertible` and `Matrix.invertibleOfDetInvertible` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
/-
**Matrix.invertibleEquivDetInvertible** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：invertibleEquivDetInvertible : Invertible A ≃ Invertible A.det where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Together `Matrix.detInvertibleOfInvertible` and `Matrix.invertibleOfDetInvertibl
e` form an
equivalence, although both sides of the equiv are subsingleton anyway.
-/
def invertibleEquivDetInvertible : Invertible A ≃ Invertible A.det where
  toFun := @detInvertibleOfInvertible _ _ _ _ _ A
  invFun := @invertibleOfDetInvertible _ _ _ _ _ A
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Given a proof that `A.det` has a constructive inverse, lift `A` to `(Matrix n n α)ˣ` -/
/-
**Matrix.unitOfDetInvertible** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：unitOfDetInvertible [Invertible A.det] : (Matrix n n α)ˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a proof that `A.det` has a constructive inverse, lift `A` to `(Matrix n n 
α)ˣ`
-/
def unitOfDetInvertible [Invertible A.det] : (Matrix n n α)ˣ :=
  @unitOfInvertible _ _ A (invertibleOfDetInvertible A)

/-- When lowered to a prop, `Matrix.invertibleEquivDetInvertible` forms an `iff`. -/
/-
**Matrix.isUnit_iff_isUnit_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit A.det
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
When lowered to a prop, `Matrix.invertibleEquivDetInvertible` forms an `iff`.
-/
theorem isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit A.det := by
  simp only [← nonempty_invertible_iff_isUnit, (invertibleEquivDetInvertible A).nonempty_congr]

@[simp]
/-
**Matrix.isUnits_det_units** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isUnits_det_units (A : (Matrix n n α)ˣ) : IsUnit (A : Matrix n n α).det
参数：A : (Matrix n n α)ˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.isUnit_iff_isUnit_det`：isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit 
A.det
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem isUnits_det_units (A : (Matrix n n α)ˣ) : IsUnit (A : Matrix n n α).det :=
  isUnit_iff_isUnit_det _ |>.mp A.isUnit

/-! #### Variants of the statements above with `IsUnit` -/


/-
**Matrix.isUnit_det_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isUnit_det_of_invertible [Invertible A] : IsUnit A.det
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a

--- 原说明 ---
#### Variants of the statements above with `IsUnit`
-/
theorem isUnit_det_of_invertible [Invertible A] : IsUnit A.det :=
  @isUnit_of_invertible _ _ _ (detInvertibleOfInvertible A)

variable {A B}
/-
**Matrix.isUnit_det_of_left_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isUnit_det_of_left_inverse (h : B * A = 1) : IsUnit A.det
参数：h : B * A = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
-/
theorem isUnit_det_of_left_inverse (h : B * A = 1) : IsUnit A.det :=
  @isUnit_of_invertible _ _ _ (detInvertibleOfLeftInverse _ _ h)
/-
**Matrix.isUnit_det_of_right_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isUnit_det_of_right_inverse (h : A * B = 1) : IsUnit A.det
参数：h : A * B = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
-/
theorem isUnit_det_of_right_inverse (h : A * B = 1) : IsUnit A.det :=
  @isUnit_of_invertible _ _ _ (detInvertibleOfRightInverse _ _ h)
/-
**Matrix.det_ne_zero_of_left_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_ne_zero_of_left_inverse [Nontrivial α] (h : B * A = 1) : A.det != 0
参数：h : B * A = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `Matrix.isUnit_det_of_left_inverse`：isUnit_det_of_left_inverse (h : B * A
 = 1) : IsUnit A.det
-/
theorem det_ne_zero_of_left_inverse [Nontrivial α] (h : B * A = 1) : A.det ≠ 0 :=
  (isUnit_det_of_left_inverse h).ne_zero
/-
**Matrix.det_ne_zero_of_right_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_ne_zero_of_right_inverse [Nontrivial α] (h : A * B = 1) : A.det != 0
参数：h : A * B = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `Matrix.isUnit_det_of_right_inverse`：isUnit_det_of_right_inverse (h : A *
 B = 1) : IsUnit A.det
-/
theorem det_ne_zero_of_right_inverse [Nontrivial α] (h : A * B = 1) : A.det ≠ 0 :=
  (isUnit_det_of_right_inverse h).ne_zero

end Invertible

section Inv

variable [Fintype n] [DecidableEq n] [CommRing α]
variable (A : Matrix n n α) (B : Matrix n n α)

/-
**Matrix.isUnit_det_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isUnit_det_transpose (h : IsUnit A.det) : IsUnit Aᵀ.det
参数：h : IsUnit A.det。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
-/
theorem isUnit_det_transpose (h : IsUnit A.det) : IsUnit Aᵀ.det := by
  rw [det_transpose]
  exact h

/-! ### A noncomputable `Inv` instance  -/


/-- The inverse of a square matrix, when it is invertible (and zero otherwise). -/
/-
**Matrix.inv** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：inv : Inv (Matrix n n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a square matrix, when it is invertible (and zero otherwise).
-/
noncomputable instance inv : Inv (Matrix n n α) :=
  ⟨fun A => A.det⁻¹ʳ • A.adjugate⟩
/-
**Matrix.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_def (A : Matrix n n α) : A⁻¹ = A.det⁻¹ʳ • A.adjugate
参数：A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_def (A : Matrix n n α) : A⁻¹ = A.det⁻¹ʳ • A.adjugate :=
  rfl
/-
**Matrix.nonsing_inv_apply_not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nonsing_inv_apply_not_isUnit (h : ¬IsUnit A.det) : A⁻¹ = 0
参数：h : ¬IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.inv_def`：inv_def (A : Matrix n n α) : A⁻¹ = A.det⁻¹ʳ • A.adjugate
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem nonsing_inv_apply_not_isUnit (h : ¬IsUnit A.det) : A⁻¹ = 0 := by
  rw [inv_def, Ring.inverse_non_unit _ h, zero_smul]
/-
**Matrix.nonsing_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nonsing_inv_apply (h : IsUnit A.det) : A⁻¹ = (↑h.unit⁻¹ : α) • A.adjugate
参数：h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.inv_def`：inv_def (A : Matrix n n α) : A⁻¹ = A.det⁻¹ʳ • A.adjugate
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
-/
theorem nonsing_inv_apply (h : IsUnit A.det) : A⁻¹ = (↑h.unit⁻¹ : α) • A.adjugate := by
  rw [inv_def, ← Ring.inverse_unit h.unit, IsUnit.unit_spec]

/-- The nonsingular inverse is the same as `invOf` when `A` is invertible. -/
@[simp]
/-
**Matrix.invOf_eq_nonsing_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：invOf_eq_nonsing_inv [Invertible A] : ⅟A = A⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.inv_def`：inv_def (A : Matrix n n α) : A⁻¹ = A.det⁻¹ʳ • A.adjugate
· 使用定理 `Ring.inverse_invertible`：Ring.inverse_invertible (x : α) [Invertible x] 
: x⁻¹ʳ = ⅟x
· 使用定理 `Matrix.invOf_eq`：invOf_eq [Invertible A.det] [Invertible A] : ⅟A = ⅟A.de
t • A.adjugate

--- 原说明 ---
The nonsingular inverse is the same as `invOf` when `A` is invertible.
-/
theorem invOf_eq_nonsing_inv [Invertible A] : ⅟A = A⁻¹ := by
  let := detInvertibleOfInvertible A
  rw [inv_def, Ring.inverse_invertible, invOf_eq]

/-- Coercing the result of `Units.instInv` is the same as coercing first and applying the
nonsingular inverse. -/
@[simp, norm_cast]
/-
**Matrix.coe_units_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ : Matrix n n α)
参数：A : (Matrix n n α)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.invOf_eq_nonsing_inv`：invOf_eq_nonsing_inv [Invertible A] : ⅟A = 
A⁻¹
· 使用定理 `invOf_units`：invOf_units [Monoid α] (u : αˣ) [Invertible (u : α)] : ⅟(u 
: α) = ↑u⁻¹

--- 原说明 ---
Coercing the result of `Units.instInv` is the same as coercing first and applyin
g the
nonsingular inverse.
-/
theorem coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ : Matrix n n α) := by
  let := A.invertible
  rw [← invOf_eq_nonsing_inv, invOf_units]

/-- The nonsingular inverse is the same as the general `Ring.inverse`. -/
/-
**Matrix.nonsing_inv_eq_ringInverse** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nonsing_inv_eq_ringInverse : A⁻¹ = A⁻¹ʳ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.nonempty_invertible`：IsUnit.nonempty_invertible [Monoid α] {a : α
} (h : IsUnit a) : Nonempty (Invertible a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.isUnit_iff_isUnit_det`：isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit 
A.det
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.invOf_eq_nonsing_inv`：invOf_eq_nonsing_inv [Invertible A] : ⅟A = 
A⁻¹
· 使用定理 `Ring.inverse_invertible`：Ring.inverse_invertible (x : α) [Invertible x] 
: x⁻¹ʳ = ⅟x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `Matrix.nonsing_inv_apply_not_isUnit`：nonsing_inv_apply_not_isUnit (h : ¬
IsUnit A.det) : A⁻¹ = 0

--- 原说明 ---
The nonsingular inverse is the same as the general `Ring.inverse`.
-/
theorem nonsing_inv_eq_ringInverse : A⁻¹ = A⁻¹ʳ := by
  by_cases h_det : IsUnit A.det
  · cases (A.isUnit_iff_isUnit_det.mpr h_det).nonempty_invertible
    rw [← invOf_eq_nonsing_inv, Ring.inverse_invertible]
  · have h := mt A.isUnit_iff_isUnit_det.mp h_det
    rw [Ring.inverse_non_unit _ h, nonsing_inv_apply_not_isUnit A h_det]
/-
**Matrix.transpose_nonsing_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_nonsing_inv : A⁻¹ᵀ = Aᵀ⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.inv_def`：inv_def (A : Matrix n n α) : A⁻¹ = A.det⁻¹ʳ • A.adjugate
· 使用定理 `Matrix.transpose_smul`：transpose_smul {R : Type*} [SMul R α] (c : R) (M 
: Matrix m n α) : (c • M)ᵀ = c • Mᵀ
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.adjugate_transpose`：adjugate_transpose (A : Matrix n n α) : (adju
gate A)ᵀ = adjugate Aᵀ
-/
theorem transpose_nonsing_inv : A⁻¹ᵀ = Aᵀ⁻¹ := by
  rw [inv_def, inv_def, transpose_smul, det_transpose, adjugate_transpose]
/-
**Matrix.conjTranspose_nonsing_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_nonsing_inv [StarRing α] : A⁻¹ᴴ = Aᴴ⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.inv_def`：inv_def (A : Matrix n n α) : A⁻¹ = A.det⁻¹ʳ • A.adjugate
· 使用定理 `Matrix.conjTranspose_smul`：conjTranspose_smul [Star R] [Star α] [SMul R 
α] [StarModule R α] (c : R) (M : Matrix m n α) : (c • M)ᴴ = star c • Mᴴ
· 使用定理 `Matrix.det_conjTranspose`：det_conjTranspose [StarRing R] (M : Matrix m m
 R) : det Mᴴ = star (det M)
· 使用定理 `Matrix.adjugate_conjTranspose`：adjugate_conjTranspose [StarRing α] (A : 
Matrix n n α) : A.adjugateᴴ = adjugate Aᴴ
· 使用定理 `Ring.inverse_star`：Ring.inverse_star [Semiring R] [StarRing R] (a : R) :
 (star a)⁻¹ʳ = star (a⁻¹ʳ)
-/
theorem conjTranspose_nonsing_inv [StarRing α] : A⁻¹ᴴ = Aᴴ⁻¹ := by
  rw [inv_def, inv_def, conjTranspose_smul, det_conjTranspose, adjugate_conjTranspose,
    Ring.inverse_star]

/-- The `nonsing_inv` of `A` is a right inverse. -/
@[simp]
/-
**Matrix.mul_nonsing_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1
参数：h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.nonempty_invertible`：IsUnit.nonempty_invertible [Monoid α] {a : α
} (h : IsUnit a) : Nonempty (Invertible a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.isUnit_iff_isUnit_det`：isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit 
A.det
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.invOf_eq_nonsing_inv`：invOf_eq_nonsing_inv [Invertible A] : ⅟A = 
A⁻¹
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1

--- 原说明 ---
The `nonsing_inv` of `A` is a right inverse.
-/
theorem mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1 := by
  cases (A.isUnit_iff_isUnit_det.mpr h).nonempty_invertible
  rw [← invOf_eq_nonsing_inv, mul_invOf_self]

/-- The nonsingular inverse of `A` is a left inverse. -/
@[simp]
/-
**Matrix.nonsing_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1
参数：h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.nonempty_invertible`：IsUnit.nonempty_invertible [Monoid α] {a : α
} (h : IsUnit a) : Nonempty (Invertible a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.isUnit_iff_isUnit_det`：isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit 
A.det
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.invOf_eq_nonsing_inv`：invOf_eq_nonsing_inv [Invertible A] : ⅟A = 
A⁻¹
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1

--- 原说明 ---
The nonsingular inverse of `A` is a left inverse.
-/
theorem nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1 := by
  cases (A.isUnit_iff_isUnit_det.mpr h).nonempty_invertible
  rw [← invOf_eq_nonsing_inv, invOf_mul_self]
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Invertible A] : Invertible A⁻¹ := by
  rw [← invOf_eq_nonsing_inv]
  infer_instance

@[simp]
/-
**Matrix.inv_inv_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_inv_of_invertible [Invertible A] : A⁻¹⁻¹ = A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_invOf`：invOf_invOf [Monoid α] (a : α) [Invertible a] [Invertible (
⅟a)] : ⅟(⅟a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_inv_of_invertible [Invertible A] : A⁻¹⁻¹ = A := by
  simp only [← invOf_eq_nonsing_inv, invOf_invOf]

@[simp]
/-
**Matrix.mul_nonsing_inv_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_nonsing_inv_cancel_right (B : Matrix m n α) (h : IsUnit A.det) : B * A
 * A⁻¹ = B
参数：B : Matrix m n α；h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.mul_nonsing_inv`：mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_nonsing_inv_cancel_right (B : Matrix m n α) (h : IsUnit A.det) : B * A * A⁻¹ = B := by
  simp [Matrix.mul_assoc, mul_nonsing_inv A h]

@[simp]
/-
**Matrix.mul_nonsing_inv_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_nonsing_inv_cancel_left (B : Matrix n m α) (h : IsUnit A.det) : A * (A
⁻¹ * B) = B
参数：B : Matrix n m α；h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_nonsing_inv`：mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_nonsing_inv_cancel_left (B : Matrix n m α) (h : IsUnit A.det) : A * (A⁻¹ * B) = B := by
  simp [← Matrix.mul_assoc, mul_nonsing_inv A h]

@[simp]
/-
**Matrix.nonsing_inv_mul_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nonsing_inv_mul_cancel_right (B : Matrix m n α) (h : IsUnit A.det) : B * A
⁻¹ * A = B
参数：B : Matrix m n α；h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.nonsing_inv_mul`：nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nonsing_inv_mul_cancel_right (B : Matrix m n α) (h : IsUnit A.det) : B * A⁻¹ * A = B := by
  simp [Matrix.mul_assoc, nonsing_inv_mul A h]

@[simp]
/-
**Matrix.nonsing_inv_mul_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nonsing_inv_mul_cancel_left (B : Matrix n m α) (h : IsUnit A.det) : A⁻¹ * 
(A * B) = B
参数：B : Matrix n m α；h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.nonsing_inv_mul`：nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nonsing_inv_mul_cancel_left (B : Matrix n m α) (h : IsUnit A.det) : A⁻¹ * (A * B) = B := by
  simp [← Matrix.mul_assoc, nonsing_inv_mul A h]

@[simp]
/-
**Matrix.mul_inv_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_inv_of_invertible [Invertible A] : A * A⁻¹ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mul_nonsing_inv`：mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1
· 使用定理 `Matrix.isUnit_det_of_invertible`：isUnit_det_of_invertible [Invertible A]
 : IsUnit A.det
-/
theorem mul_inv_of_invertible [Invertible A] : A * A⁻¹ = 1 :=
  mul_nonsing_inv A (isUnit_det_of_invertible A)

@[simp]
/-
**Matrix.inv_mul_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_mul_of_invertible [Invertible A] : A⁻¹ * A = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.nonsing_inv_mul`：nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1
· 使用定理 `Matrix.isUnit_det_of_invertible`：isUnit_det_of_invertible [Invertible A]
 : IsUnit A.det
-/
theorem inv_mul_of_invertible [Invertible A] : A⁻¹ * A = 1 :=
  nonsing_inv_mul A (isUnit_det_of_invertible A)

@[simp]
/-
**Matrix.mul_inv_cancel_right_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_inv_cancel_right_of_invertible (B : Matrix m n α) [Invertible A] : B *
 A * A⁻¹ = B
参数：B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mul_nonsing_inv_cancel_right`：mul_nonsing_inv_cancel_right (B : M
atrix m n α) (h : IsUnit A.det) : B * A * A⁻¹ = B
· 使用定理 `Matrix.isUnit_det_of_invertible`：isUnit_det_of_invertible [Invertible A]
 : IsUnit A.det
-/
theorem mul_inv_cancel_right_of_invertible (B : Matrix m n α) [Invertible A] : B * A * A⁻¹ = B :=
  mul_nonsing_inv_cancel_right A B (isUnit_det_of_invertible A)

@[simp]
/-
**Matrix.mul_inv_cancel_left_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_inv_cancel_left_of_invertible (B : Matrix n m α) [Invertible A] : A * 
(A⁻¹ * B) = B
参数：B : Matrix n m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mul_nonsing_inv_cancel_left`：mul_nonsing_inv_cancel_left (B : Mat
rix n m α) (h : IsUnit A.det) : A * (A⁻¹ * B) = B
· 使用定理 `Matrix.isUnit_det_of_invertible`：isUnit_det_of_invertible [Invertible A]
 : IsUnit A.det
-/
theorem mul_inv_cancel_left_of_invertible (B : Matrix n m α) [Invertible A] : A * (A⁻¹ * B) = B :=
  mul_nonsing_inv_cancel_left A B (isUnit_det_of_invertible A)

@[simp]
/-
**Matrix.inv_mul_cancel_right_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_mul_cancel_right_of_invertible (B : Matrix m n α) [Invertible A] : B *
 A⁻¹ * A = B
参数：B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.nonsing_inv_mul_cancel_right`：nonsing_inv_mul_cancel_right (B : M
atrix m n α) (h : IsUnit A.det) : B * A⁻¹ * A = B
· 使用定理 `Matrix.isUnit_det_of_invertible`：isUnit_det_of_invertible [Invertible A]
 : IsUnit A.det
-/
theorem inv_mul_cancel_right_of_invertible (B : Matrix m n α) [Invertible A] : B * A⁻¹ * A = B :=
  nonsing_inv_mul_cancel_right A B (isUnit_det_of_invertible A)

@[simp]
/-
**Matrix.inv_mul_cancel_left_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_mul_cancel_left_of_invertible (B : Matrix n m α) [Invertible A] : A⁻¹ 
* (A * B) = B
参数：B : Matrix n m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.nonsing_inv_mul_cancel_left`：nonsing_inv_mul_cancel_left (B : Mat
rix n m α) (h : IsUnit A.det) : A⁻¹ * (A * B) = B
· 使用定理 `Matrix.isUnit_det_of_invertible`：isUnit_det_of_invertible [Invertible A]
 : IsUnit A.det
-/
theorem inv_mul_cancel_left_of_invertible (B : Matrix n m α) [Invertible A] : A⁻¹ * (A * B) = B :=
  nonsing_inv_mul_cancel_left A B (isUnit_det_of_invertible A)
/-
**Matrix.inv_mul_eq_iff_eq_mul_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_mul_eq_iff_eq_mul_of_invertible (A : Matrix n n α) [Invertible A] (B C
 : Matrix n m α) : A⁻¹ * B = C ↔ B = A * C
参数：A : Matrix n n α；B C : Matrix n m α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_inv_cancel_left_of_invertible`：mul_inv_cancel_left_of_inverti
ble (B : Matrix n m α) [Invertible A] : A * (A⁻¹ * B) = B
· 使用定理 `Matrix.inv_mul_cancel_left_of_invertible`：inv_mul_cancel_left_of_inverti
ble (B : Matrix n m α) [Invertible A] : A⁻¹ * (A * B) = B
-/
theorem inv_mul_eq_iff_eq_mul_of_invertible (A : Matrix n n α) [Invertible A] (B C : Matrix n m α) :
    A⁻¹ * B = C ↔ B = A * C :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left_of_invertible],
   fun h => by rw [h, inv_mul_cancel_left_of_invertible]⟩
/-
**Matrix.mul_inv_eq_iff_eq_mul_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_inv_eq_iff_eq_mul_of_invertible (A : Matrix n n α) [Invertible A] (B C
 : Matrix m n α) : B * A⁻¹ = C ↔ B = C * A
参数：A : Matrix n n α；B C : Matrix m n α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.inv_mul_cancel_right_of_invertible`：inv_mul_cancel_right_of_inver
tible (B : Matrix m n α) [Invertible A] : B * A⁻¹ * A = B
· 使用定理 `Matrix.mul_inv_cancel_right_of_invertible`：mul_inv_cancel_right_of_inver
tible (B : Matrix m n α) [Invertible A] : B * A * A⁻¹ = B
-/
theorem mul_inv_eq_iff_eq_mul_of_invertible (A : Matrix n n α) [Invertible A] (B C : Matrix m n α) :
    B * A⁻¹ = C ↔ B = C * A :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right_of_invertible],
   fun h => by rw [h, mul_inv_cancel_right_of_invertible]⟩
/-
**Matrix.inv_mulVec_eq_vec** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：inv_mulVec_eq_vec {A : Matrix n n α} [Invertible A] {u v : n -> α} (hM : u
 = A.mulVec v) : A⁻¹.mulVec u = v
参数：hM : u = A.mulVec v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mulVec_mulVec`：mulVec_mulVec [Fintype n] [Fintype o] (v : o -> α)
 (M : Matrix m n α) (N : Matrix n o α) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v
· 使用定理 `Matrix.inv_mul_of_invertible`：inv_mul_of_invertible [Invertible A] : A⁻¹
 * A = 1
· 使用定理 `Matrix.one_mulVec`：one_mulVec (v : m -> α) : 1 *ᵥ v = v
-/
lemma inv_mulVec_eq_vec {A : Matrix n n α} [Invertible A]
    {u v : n → α} (hM : u = A.mulVec v) : A⁻¹.mulVec u = v := by
  rw [hM, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
/-
**Matrix.mul_right_injective_of_invertible** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mul_right_injective_of_invertible [Invertible A] : Function.Injective (fun
 (x : Matrix n m α) => A * x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.inv_mul_cancel_left_of_invertible`：inv_mul_cancel_left_of_inverti
ble (B : Matrix n m α) [Invertible A] : A⁻¹ * (A * B) = B
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma mul_right_injective_of_invertible [Invertible A] :
    Function.Injective (fun (x : Matrix n m α) => A * x) :=
  fun _ _ h => by simpa only [inv_mul_cancel_left_of_invertible] using congr_arg (A⁻¹ * ·) h
/-
**Matrix.mul_left_injective_of_invertible** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mul_left_injective_of_invertible [Invertible A] : Function.Injective (fun 
(x : Matrix m n α) => x * A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_inv_cancel_right_of_invertible`：mul_inv_cancel_right_of_inver
tible (B : Matrix m n α) [Invertible A] : B * A * A⁻¹ = B
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma mul_left_injective_of_invertible [Invertible A] :
    Function.Injective (fun (x : Matrix m n α) => x * A) :=
  fun a x hax => by simpa only [mul_inv_cancel_right_of_invertible] using congr_arg (· * A⁻¹) hax
/-
**Matrix.mul_right_inj_of_invertible** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mul_right_inj_of_invertible [Invertible A] {x y : Matrix n m α} : A * x = 
A * y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Matrix.mul_right_injective_of_invertible`：mul_right_injective_of_inverti
ble [Invertible A] : Function.Injective (fun (x : Matrix n m α) => A * x)
-/
lemma mul_right_inj_of_invertible [Invertible A] {x y : Matrix n m α} : A * x = A * y ↔ x = y :=
  (mul_right_injective_of_invertible A).eq_iff
/-
**Matrix.mul_left_inj_of_invertible** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mul_left_inj_of_invertible [Invertible A] {x y : Matrix m n α} : x * A = y
 * A ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Matrix.mul_left_injective_of_invertible`：mul_left_injective_of_invertibl
e [Invertible A] : Function.Injective (fun (x : Matrix m n α) => x * A)
-/
lemma mul_left_inj_of_invertible [Invertible A] {x y : Matrix m n α} : x * A = y * A ↔ x = y :=
  (mul_left_injective_of_invertible A).eq_iff
/-
**Matrix.IsSymm.inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {n : Type u'} {α : Type v} [inst : Fintype n] [inst_1 : DecidableEq n] [
inst_2 : CommRing α] {A : Matrix n n α},   A.IsSymm → A⁻¹.IsSymm
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsSymm.smul`：∀ {α : Type u_1} {n : Type u_3} {R : Type u_5} [inst
 : SMul R α] {A : Matrix n n α},   A.IsSymm → ∀ (k : R), (k • A).IsSymm
· 使用定理 `Matrix.IsSymm.adjugate`：∀ {n : Type v} {α : Type w} [inst : DecidableEq 
n] [inst_1 : Fintype n] [inst_2 : CommRing α] {A : Matrix n n α},   A.IsSymm → A
.adjugate.Is…
-/
lemma IsSymm.inv {A : Matrix n n α} (hA : A.IsSymm) : A⁻¹.IsSymm :=
  hA.adjugate.smul _

end Inv

section InjectiveMul
variable [Fintype n] [Fintype m] [DecidableEq m] [CommRing α]

/-
**Matrix.mul_left_injective_of_inv** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mul_left_injective_of_inv (A : Matrix m n α) (B : Matrix n m α) (h : A * B
 = 1) : Function.Injective (fun x : Matrix l m α => x * A)
参数：A : Matrix m n α；B : Matrix n m α；h : A * B = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma mul_left_injective_of_inv (A : Matrix m n α) (B : Matrix n m α) (h : A * B = 1) :
    Function.Injective (fun x : Matrix l m α => x * A) := fun _ _ g => by
  simpa only [Matrix.mul_assoc, Matrix.mul_one, h] using congr_arg (· * B) g
/-
**Matrix.mul_right_injective_of_inv** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mul_right_injective_of_inv (A : Matrix m n α) (B : Matrix n m α) (h : A * 
B = 1) : Function.Injective (fun x : Matrix m l α => B * x)
参数：A : Matrix m n α；B : Matrix n m α；h : A * B = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma mul_right_injective_of_inv (A : Matrix m n α) (B : Matrix n m α) (h : A * B = 1) :
    Function.Injective (fun x : Matrix m l α => B * x) :=
  fun _ _ g => by simpa only [← Matrix.mul_assoc, Matrix.one_mul, h] using congr_arg (A * ·) g

end InjectiveMul

section vecMul

section Semiring

variable {R : Type*} [Semiring R]

/-
**Matrix.vecMul_surjective_iff_exists_left_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Ma
trix`。
形式化陈述：vecMul_surjective_iff_exists_left_inverse [DecidableEq n] [Fintype m] [Fin
ite n] {A : Matrix m n R} : Function.Surjective A.vecMul ↔ exists B : Matrix n m
 R, B * A = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_apply_eq_vecMul`：mul_apply_eq_vecMul [Fintype n] (A : Matrix 
m n α) (B : Matrix n o α) (i : m) : (A * B) i = A i ᵥ* B
· 使用定理 `Matrix.one_eq_pi_single`：one_eq_pi_single {i j} : (1 : Matrix n n α) i j
 = Pi.single (M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.vecMul_vecMul`：vecMul_vecMul [Fintype n] [Fintype m] (v : m -> α)
 (M : Matrix m n α) (N : Matrix n o α) : v ᵥ* M ᵥ* N = v ᵥ* (M * N)
· 使用定理 `Matrix.vecMul_one`：vecMul_one (v : m -> α) : v ᵥ* 1 = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vecMul_surjective_iff_exists_left_inverse
    [DecidableEq n] [Fintype m] [Finite n] {A : Matrix m n R} :
    Function.Surjective A.vecMul ↔ ∃ B : Matrix n m R, B * A = 1 := by
  cases nonempty_fintype n
  refine ⟨fun h ↦ ?_, fun ⟨B, hBA⟩ y ↦ ⟨y ᵥ* B, by simp [hBA]⟩⟩
  choose rows hrows using (h <| Pi.single · 1)
  refine ⟨Matrix.of rows, Matrix.ext fun i j => ?_⟩
  rw [mul_apply_eq_vecMul, one_eq_pi_single, ← hrows]
  rfl
/-
**Matrix.mulVec_surjective_iff_exists_right_inverse** 是 Mathlib 中的一个定理，位于命名空间 `M
atrix`。
形式化陈述：mulVec_surjective_iff_exists_right_inverse [DecidableEq m] [Finite m] [Fin
type n] {A : Matrix m n R} : Function.Surjective A.mulVec ↔ exists B : Matrix n 
m R, A * B = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.one_eq_pi_single`：one_eq_pi_single {i j} : (1 : Matrix n n α) i j
 = Pi.single (M
· 使用定理 `Pi.single_comm`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} [
inst_1 : Zero M] (i : ι) (x : M) (j : ι),   Pi.single i x j = Pi.single j x i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.mulVec_mulVec`：mulVec_mulVec [Fintype n] [Fintype o] (v : o -> α)
 (M : Matrix m n α) (N : Matrix n o α) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v
· 使用定理 `Matrix.one_mulVec`：one_mulVec (v : m -> α) : 1 *ᵥ v = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulVec_surjective_iff_exists_right_inverse
    [DecidableEq m] [Finite m] [Fintype n] {A : Matrix m n R} :
    Function.Surjective A.mulVec ↔ ∃ B : Matrix n m R, A * B = 1 := by
  cases nonempty_fintype m
  refine ⟨fun h ↦ ?_, fun ⟨B, hBA⟩ y ↦ ⟨B *ᵥ y, by simp [hBA]⟩⟩
  choose cols hcols using (h <| Pi.single · 1)
  refine ⟨(Matrix.of cols)ᵀ, Matrix.ext fun i j ↦ ?_⟩
  rw [one_eq_pi_single, Pi.single_comm, ← hcols j]
  rfl

end Semiring

variable [DecidableEq m] {R K : Type*} [CommRing R] [Field K] [Fintype m]

/-
**Matrix.vecMul_surjective_iff_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_surjective_iff_isUnit {A : Matrix m m R} : Function.Surjective A.ve
cMul ↔ IsUnit A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vecMul_surjective_iff_exists_left_inverse`：vecMul_surjective_iff_
exists_left_inverse [DecidableEq n] [Fintype m] [Finite n] {A : Matrix m n R} : 
Function.Surjective A.vecMul ↔ exists …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `isUnit_iff_exists_inv'`：isUnit_iff_exists_inv' [Monoid M] [IsDedekindFin
iteMonoid M] {a : M} : IsUnit a ↔ exists b, b * a = 1
· 使用定理 `Matrix.instIsDedekindFiniteMonoidOfIsStablyFiniteRing`：∀ (n : Type u_11)
 (R : Type u_12) [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : MulOne R]
   [inst_3 : AddCommMonoid R] [IsStablyFini…
· 使用定理 `Matrix.instIsStablyFiniteRingOfCommSemiring`：∀ {R : Type u_3} [inst : Co
mmSemiring R], IsStablyFiniteRing R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem vecMul_surjective_iff_isUnit {A : Matrix m m R} :
    Function.Surjective A.vecMul ↔ IsUnit A := by
  rw [vecMul_surjective_iff_exists_left_inverse, isUnit_iff_exists_inv']
/-
**Matrix.mulVec_surjective_iff_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_surjective_iff_isUnit {A : Matrix m m R} : Function.Surjective A.mu
lVec ↔ IsUnit A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mulVec_surjective_iff_exists_right_inverse`：mulVec_surjective_iff
_exists_right_inverse [DecidableEq m] [Finite m] [Fintype n] {A : Matrix m n R} 
: Function.Surjective A.mulVec ↔ exists…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `Matrix.instIsDedekindFiniteMonoidOfIsStablyFiniteRing`：∀ (n : Type u_11)
 (R : Type u_12) [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : MulOne R]
   [inst_3 : AddCommMonoid R] [IsStablyFini…
· 使用定理 `Matrix.instIsStablyFiniteRingOfCommSemiring`：∀ {R : Type u_3} [inst : Co
mmSemiring R], IsStablyFiniteRing R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mulVec_surjective_iff_isUnit {A : Matrix m m R} :
    Function.Surjective A.mulVec ↔ IsUnit A := by
  rw [mulVec_surjective_iff_exists_right_inverse, isUnit_iff_exists_inv]
/-
**Matrix.vecMul_injective_iff_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_injective_iff_isUnit {A : Matrix m m K} : Function.Injective A.vecM
ul ↔ IsUnit A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.vecMul_surjective_iff_isUnit`：vecMul_surjective_iff_isUnit {A : M
atrix m m R} : Function.Surjective A.vecMul ↔ IsUnit A
· 使用定理 `LinearMap.surjective_of_injective`：surjective_of_injective [FiniteDimens
ional K V] {f : V ->ₗ[K] V} (hinj : Injective f) : Surjective f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `Matrix.vecMul_injective_of_isUnit`：vecMul_injective_of_isUnit [Fintype m
] [DecidableEq m] {A : Matrix m m R} (ha : IsUnit A) : Function.Injective A.vecM
ul
-/
theorem vecMul_injective_iff_isUnit {A : Matrix m m K} :
    Function.Injective A.vecMul ↔ IsUnit A := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← vecMul_surjective_iff_isUnit]
    exact LinearMap.surjective_of_injective (f := A.vecMulLinear) h
  exact vecMul_injective_of_isUnit h
/-
**Matrix.mulVec_injective_iff_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_injective_iff_isUnit {A : Matrix m m K} : Function.Injective A.mulV
ec ↔ IsUnit A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.isUnit_transpose`：∀ {n : Type u_2} {α : Type u_3} [inst : Fintype
 n] [inst_1 : DecidableEq n] [inst_2 : CommSemiring α]   (A : Matrix n n α), IsU
nit A.transpo…
· 使用定理 `Matrix.vecMul_injective_iff_isUnit`：vecMul_injective_iff_isUnit {A : Mat
rix m m K} : Function.Injective A.vecMul ↔ IsUnit A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.vecMul_transpose`：vecMul_transpose [Fintype n] (A : Matrix m n α)
 (x : n -> α) : x ᵥ* Aᵀ = A *ᵥ x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mulVec_injective_iff_isUnit {A : Matrix m m K} :
    Function.Injective A.mulVec ↔ IsUnit A := by
  rw [← isUnit_transpose, ← vecMul_injective_iff_isUnit]
  simp_rw [vecMul_transpose]
/-
**Matrix.linearIndependent_rows_iff_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linearIndependent_rows_iff_isUnit {A : Matrix m m K} : LinearIndependent K
 A.row ↔ IsUnit A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.col_transpose`：col_transpose (A : Matrix m n α) : Aᵀ.col = A.row
· 使用定理 `Matrix.mulVec_injective_iff`：Matrix.mulVec_injective_iff {M : Matrix m n
 R} : Function.Injective M.mulVec ↔ LinearIndependent R M.col
· 使用定理 `Matrix.coe_mulVecLin`：Matrix.coe_mulVecLin [Fintype n] (M : Matrix m n R
) : (M.mulVecLin : _ -> _) = M.mulVec
· 使用定理 `Matrix.mulVecLin_transpose`：∀ {R : Type u_1} [inst : CommSemiring R] {m 
: Type u_4} {n : Type u_5} [inst_1 : Fintype m] (M : Matrix m n R),   M.transpos
e.mulVecLin = M.…
· 使用定理 `Matrix.vecMul_injective_iff_isUnit`：vecMul_injective_iff_isUnit {A : Mat
rix m m K} : Function.Injective A.vecMul ↔ IsUnit A
· 使用定理 `Matrix.coe_vecMulLinear`：Matrix.coe_vecMulLinear [Fintype m] (M : Matrix
 m n R) : (M.vecMulLinear : _ -> _) = M.vecMul
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndependent_rows_iff_isUnit {A : Matrix m m K} :
    LinearIndependent K A.row ↔ IsUnit A := by
  rw [← col_transpose, ← mulVec_injective_iff, ← coe_mulVecLin, mulVecLin_transpose,
    ← vecMul_injective_iff_isUnit, coe_vecMulLinear]
/-
**Matrix.linearIndependent_cols_iff_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linearIndependent_cols_iff_isUnit {A : Matrix m m K} : LinearIndependent K
 A.col ↔ IsUnit A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.row_transpose`：row_transpose (A : Matrix m n α) : Aᵀ.row = A.col
· 使用定理 `Matrix.linearIndependent_rows_iff_isUnit`：linearIndependent_rows_iff_isU
nit {A : Matrix m m K} : LinearIndependent K A.row ↔ IsUnit A
· 使用定理 `Matrix.isUnit_transpose`：∀ {n : Type u_2} {α : Type u_3} [inst : Fintype
 n] [inst_1 : DecidableEq n] [inst_2 : CommSemiring α]   (A : Matrix n n α), IsU
nit A.transpo…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndependent_cols_iff_isUnit {A : Matrix m m K} :
    LinearIndependent K A.col ↔ IsUnit A := by
  rw [← row_transpose, linearIndependent_rows_iff_isUnit, isUnit_transpose]
/-
**Matrix.vecMul_surjective_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_surjective_of_invertible (A : Matrix m m R) [Invertible A] : Functi
on.Surjective A.vecMul
参数：A : Matrix m m R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.vecMul_surjective_iff_isUnit`：vecMul_surjective_iff_isUnit {A : M
atrix m m R} : Function.Surjective A.vecMul ↔ IsUnit A
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
-/
theorem vecMul_surjective_of_invertible (A : Matrix m m R) [Invertible A] :
    Function.Surjective A.vecMul :=
  vecMul_surjective_iff_isUnit.2 <| isUnit_of_invertible A
/-
**Matrix.mulVec_surjective_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_surjective_of_invertible (A : Matrix m m R) [Invertible A] : Functi
on.Surjective A.mulVec
参数：A : Matrix m m R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.mulVec_surjective_iff_isUnit`：mulVec_surjective_iff_isUnit {A : M
atrix m m R} : Function.Surjective A.mulVec ↔ IsUnit A
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
-/
theorem mulVec_surjective_of_invertible (A : Matrix m m R) [Invertible A] :
    Function.Surjective A.mulVec :=
  mulVec_surjective_iff_isUnit.2 <| isUnit_of_invertible A
/-
**Matrix.vecMul_injective_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_injective_of_invertible (A : Matrix m m K) [Invertible A] : Functio
n.Injective A.vecMul
参数：A : Matrix m m K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.vecMul_injective_iff_isUnit`：vecMul_injective_iff_isUnit {A : Mat
rix m m K} : Function.Injective A.vecMul ↔ IsUnit A
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
-/
theorem vecMul_injective_of_invertible (A : Matrix m m K) [Invertible A] :
    Function.Injective A.vecMul :=
  vecMul_injective_iff_isUnit.2 <| isUnit_of_invertible A
/-
**Matrix.mulVec_injective_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_injective_of_invertible (A : Matrix m m K) [Invertible A] : Functio
n.Injective A.mulVec
参数：A : Matrix m m K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.mulVec_injective_iff_isUnit`：mulVec_injective_iff_isUnit {A : Mat
rix m m K} : Function.Injective A.mulVec ↔ IsUnit A
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
-/
theorem mulVec_injective_of_invertible (A : Matrix m m K) [Invertible A] :
    Function.Injective A.mulVec :=
  mulVec_injective_iff_isUnit.2 <| isUnit_of_invertible A
/-
**Matrix.linearIndependent_rows_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`
。
形式化陈述：linearIndependent_rows_of_invertible (A : Matrix m m K) [Invertible A] : L
inearIndependent K A.row
参数：A : Matrix m m K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.linearIndependent_rows_iff_isUnit`：linearIndependent_rows_iff_isU
nit {A : Matrix m m K} : LinearIndependent K A.row ↔ IsUnit A
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
-/
theorem linearIndependent_rows_of_invertible (A : Matrix m m K) [Invertible A] :
    LinearIndependent K A.row :=
  linearIndependent_rows_iff_isUnit.2 <| isUnit_of_invertible A
/-
**Matrix.linearIndependent_cols_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`
。
形式化陈述：linearIndependent_cols_of_invertible (A : Matrix m m K) [Invertible A] : L
inearIndependent K A.col
参数：A : Matrix m m K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.linearIndependent_cols_iff_isUnit`：linearIndependent_cols_iff_isU
nit {A : Matrix m m K} : LinearIndependent K A.col ↔ IsUnit A
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
-/
theorem linearIndependent_cols_of_invertible (A : Matrix m m K) [Invertible A] :
    LinearIndependent K A.col :=
  linearIndependent_cols_iff_isUnit.2 <| isUnit_of_invertible A

end vecMul

variable [Fintype n] [DecidableEq n] [CommRing α]
variable (A : Matrix n n α) (B : Matrix n n α)

/-
**Matrix.nonsing_inv_cancel_or_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nonsing_inv_cancel_or_zero : A⁻¹ * A = 1 ∧ A * A⁻¹ = 1 ∨ A⁻¹ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.nonsing_inv_mul`：nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1
· 使用定理 `Matrix.mul_nonsing_inv`：mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1
· 使用定理 `Matrix.nonsing_inv_apply_not_isUnit`：nonsing_inv_apply_not_isUnit (h : ¬
IsUnit A.det) : A⁻¹ = 0
-/
theorem nonsing_inv_cancel_or_zero : A⁻¹ * A = 1 ∧ A * A⁻¹ = 1 ∨ A⁻¹ = 0 := by
  by_cases h : IsUnit A.det
  · exact Or.inl ⟨nonsing_inv_mul _ h, mul_nonsing_inv _ h⟩
  · exact Or.inr (nonsing_inv_apply_not_isUnit _ h)
/-
**Matrix.det_nonsing_inv_mul_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_nonsing_inv_mul_det (h : IsUnit A.det) : A⁻¹.det * A.det = 1
参数：h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.nonsing_inv_mul`：nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
-/
theorem det_nonsing_inv_mul_det (h : IsUnit A.det) : A⁻¹.det * A.det = 1 := by
  rw [← det_mul, A.nonsing_inv_mul h, det_one]

@[simp]
/-
**Matrix.det_nonsing_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_nonsing_inv : A⁻¹.det = A.det⁻¹ʳ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.nonempty_invertible`：IsUnit.nonempty_invertible [Monoid α] {a : α
} (h : IsUnit a) : Nonempty (Invertible a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_invertible`：Ring.inverse_invertible (x : α) [Invertible x] 
: x⁻¹ʳ = ⅟x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.invOf_eq_nonsing_inv`：invOf_eq_nonsing_inv [Invertible A] : ⅟A = 
A⁻¹
· 使用定理 `Matrix.det_invOf`：det_invOf [Invertible A] [Invertible A.det] : (⅟A).det
 = ⅟A.det
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Matrix.det_isEmpty`：det_isEmpty [IsEmpty n] {A : Matrix n n R} : det A =
 1
· 使用定理 `Ring.inverse_one`：inverse_one : (1 : M₀)⁻¹ʳ = 1
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `Matrix.nonsing_inv_apply_not_isUnit`：nonsing_inv_apply_not_isUnit (h : ¬
IsUnit A.det) : A⁻¹ = 0
· 使用定理 `Matrix.det_zero`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] [Nonempty n],   Matrix.det 0 = 0
-/
theorem det_nonsing_inv : A⁻¹.det = A.det⁻¹ʳ := by
  by_cases h : IsUnit A.det
  · cases h.nonempty_invertible
    let := invertibleOfDetInvertible A
    rw [Ring.inverse_invertible, ← invOf_eq_nonsing_inv, det_invOf]
  cases isEmpty_or_nonempty n
  · rw [det_isEmpty, det_isEmpty, Ring.inverse_one]
  · rw [Ring.inverse_non_unit _ h, nonsing_inv_apply_not_isUnit _ h, det_zero]
/-
**Matrix.isUnit_nonsing_inv_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isUnit_nonsing_inv_det (h : IsUnit A.det) : IsUnit A⁻¹.det
参数：h : IsUnit A.det。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Matrix.det_nonsing_inv_mul_det`：det_nonsing_inv_mul_det (h : IsUnit A.de
t) : A⁻¹.det * A.det = 1
-/
theorem isUnit_nonsing_inv_det (h : IsUnit A.det) : IsUnit A⁻¹.det :=
  .of_mul_eq_one _ (A.det_nonsing_inv_mul_det h)

@[simp]
/-
**Matrix.nonsing_inv_nonsing_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nonsing_inv_nonsing_inv (h : IsUnit A.det) : A⁻¹⁻¹ = A
参数：h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.mul_nonsing_inv`：mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.isUnit_nonsing_inv_det`：isUnit_nonsing_inv_det (h : IsUnit A.det)
 : IsUnit A⁻¹.det
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
-/
theorem nonsing_inv_nonsing_inv (h : IsUnit A.det) : A⁻¹⁻¹ = A :=
  calc
    A⁻¹⁻¹ = 1 * A⁻¹⁻¹ := by rw [Matrix.one_mul]
    _ = A * A⁻¹ * A⁻¹⁻¹ := by rw [A.mul_nonsing_inv h]
    _ = A := by
      rw [Matrix.mul_assoc, A⁻¹.mul_nonsing_inv (A.isUnit_nonsing_inv_det h), Matrix.mul_one]
/-
**Matrix.isUnit_nonsing_inv_det_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isUnit_nonsing_inv_det_iff {A : Matrix n n α} : IsUnit A⁻¹.det ↔ IsUnit A.
det
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_nonsing_inv`：det_nonsing_inv : A⁻¹.det = A.det⁻¹ʳ
· 使用定理 `isUnit_ringInverse`：isUnit_ringInverse {a : M₀} : IsUnit a⁻¹ʳ ↔ IsUnit a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUnit_nonsing_inv_det_iff {A : Matrix n n α} : IsUnit A⁻¹.det ↔ IsUnit A.det := by
  rw [Matrix.det_nonsing_inv, isUnit_ringInverse]

@[simp]
/-
**Matrix.isUnit_nonsing_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isUnit_nonsing_inv_iff {A : Matrix n n α} : IsUnit A⁻¹ ↔ IsUnit A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isUnit_nonsing_inv_iff {A : Matrix n n α} : IsUnit A⁻¹ ↔ IsUnit A := by
  simp_rw [isUnit_iff_isUnit_det, isUnit_nonsing_inv_det_iff]

-- `IsUnit.invertible` lifts the proposition `IsUnit A` to a constructive inverse of `A`.
/-- A version of `Matrix.invertibleOfDetInvertible` with the inverse defeq to `A⁻¹` that is
therefore noncomputable. -/
@[instance_reducible]
/-
**Matrix.invertibleOfIsUnitDet** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：invertibleOfIsUnitDet (h : IsUnit A.det) : Invertible A
参数：h : IsUnit A.det。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.nonsing_inv_mul`：nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1
· 使用定理 `Matrix.mul_nonsing_inv`：mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1

--- 原说明 ---
A version of `Matrix.invertibleOfDetInvertible` with the inverse defeq to `A⁻¹` 
that is
therefore noncomputable.
-/
noncomputable def invertibleOfIsUnitDet (h : IsUnit A.det) : Invertible A :=
  ⟨A⁻¹, nonsing_inv_mul A h, mul_nonsing_inv A h⟩

/-- A version of `Matrix.unitOfDetInvertible` with the inverse defeq to `A⁻¹` that is therefore
noncomputable. -/
/-
**Matrix.nonsingInvUnit** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：nonsingInvUnit (h : IsUnit A.det) : (Matrix n n α)ˣ
参数：h : IsUnit A.det。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Matrix.unitOfDetInvertible` with the inverse defeq to `A⁻¹` that i
s therefore
noncomputable.
-/
noncomputable def nonsingInvUnit (h : IsUnit A.det) : (Matrix n n α)ˣ :=
  @unitOfInvertible _ _ _ (invertibleOfIsUnitDet A h)
/-
**Matrix.unitOfDetInvertible_eq_nonsingInvUnit** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
`。
形式化陈述：unitOfDetInvertible_eq_nonsingInvUnit [Invertible A.det] : unitOfDetInvert
ible A = nonsingInvUnit A (isUnit_of_invertible _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem unitOfDetInvertible_eq_nonsingInvUnit [Invertible A.det] :
    unitOfDetInvertible A = nonsingInvUnit A (isUnit_of_invertible _) := by
  ext
  rfl

variable {A} {B}

/-- If matrix A is left invertible, then its inverse equals its left inverse. -/
/-
**Matrix.inv_eq_left_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B
参数：h : B * A = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.instIsDedekindFiniteMonoidOfIsStablyFiniteRing`：∀ (n : Type u_11)
 (R : Type u_12) [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : MulOne R]
   [inst_3 : AddCommMonoid R] [IsStablyFini…
· 使用定理 `Matrix.instIsStablyFiniteRingOfCommSemiring`：∀ {R : Type u_3} [inst : Co
mmSemiring R], IsStablyFiniteRing R
· 使用定理 `invOf_eq_left_inv`：invOf_eq_left_inv [Invertible a] (hac : b * a = 1) : 
⅟a = b
· 使用定理 `Matrix.invOf_eq_nonsing_inv`：invOf_eq_nonsing_inv [Invertible A] : ⅟A = 
A⁻¹

--- 原说明 ---
If matrix A is left invertible, then its inverse equals its left inverse.
-/
theorem inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B :=
  letI := invertibleOfLeftInverse _ _ h
  invOf_eq_nonsing_inv A ▸ invOf_eq_left_inv h

/-- If matrix A is right invertible, then its inverse equals its right inverse. -/
/-
**Matrix.inv_eq_right_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_eq_right_inv (h : A * B = 1) : A⁻¹ = B
参数：h : A * B = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.inv_eq_left_inv`：inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_eq_one_comm`：∀ {M : Type u_2} [inst : MulOne M] [IsDedekindFiniteMon
oid M] {a b : M}, a * b = 1 ↔ b * a = 1
· 使用定理 `Matrix.instIsDedekindFiniteMonoidOfIsStablyFiniteRing`：∀ (n : Type u_11)
 (R : Type u_12) [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : MulOne R]
   [inst_3 : AddCommMonoid R] [IsStablyFini…
· 使用定理 `Matrix.instIsStablyFiniteRingOfCommSemiring`：∀ {R : Type u_3} [inst : Co
mmSemiring R], IsStablyFiniteRing R

--- 原说明 ---
If matrix A is right invertible, then its inverse equals its right inverse.
-/
theorem inv_eq_right_inv (h : A * B = 1) : A⁻¹ = B :=
  inv_eq_left_inv (mul_eq_one_comm.2 h)

section InvEqInv

variable {C : Matrix n n α}

/-- The left inverse of matrix A is unique when existing. -/
/-
**Matrix.left_inv_eq_left_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：left_inv_eq_left_inv (h : B * A = 1) (g : C * A = 1) : B = C
参数：h : B * A = 1；g : C * A = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.inv_eq_left_inv`：inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B

--- 原说明 ---
The left inverse of matrix A is unique when existing.
-/
theorem left_inv_eq_left_inv (h : B * A = 1) (g : C * A = 1) : B = C := by
  rw [← inv_eq_left_inv h, ← inv_eq_left_inv g]

/-- The right inverse of matrix A is unique when existing. -/
/-
**Matrix.right_inv_eq_right_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：right_inv_eq_right_inv (h : A * B = 1) (g : A * C = 1) : B = C
参数：h : A * B = 1；g : A * C = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.inv_eq_right_inv`：inv_eq_right_inv (h : A * B = 1) : A⁻¹ = B

--- 原说明 ---
The right inverse of matrix A is unique when existing.
-/
theorem right_inv_eq_right_inv (h : A * B = 1) (g : A * C = 1) : B = C := by
  rw [← inv_eq_right_inv h, ← inv_eq_right_inv g]

/-- The right inverse of matrix A equals the left inverse of A when they exist. -/
/-
**Matrix.right_inv_eq_left_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：right_inv_eq_left_inv (h : A * B = 1) (g : C * A = 1) : B = C
参数：h : A * B = 1；g : C * A = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.inv_eq_right_inv`：inv_eq_right_inv (h : A * B = 1) : A⁻¹ = B
· 使用定理 `Matrix.inv_eq_left_inv`：inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B

--- 原说明 ---
The right inverse of matrix A equals the left inverse of A when they exist.
-/
theorem right_inv_eq_left_inv (h : A * B = 1) (g : C * A = 1) : B = C := by
  rw [← inv_eq_right_inv h, ← inv_eq_left_inv g]
/-
**Matrix.inv_inj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_inj (h : A⁻¹ = B⁻¹) (h' : IsUnit A.det) : A = B
参数：h : A⁻¹ = B⁻¹；h' : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.left_inv_eq_left_inv`：left_inv_eq_left_inv (h : B * A = 1) (g : C
 * A = 1) : B = C
· 使用定理 `Matrix.mul_nonsing_inv`：mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.isUnit_nonsing_inv_det_iff`：isUnit_nonsing_inv_det_iff {A : Matri
x n n α} : IsUnit A⁻¹.det ↔ IsUnit A.det
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
/-
**Matrix.inv_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_zero : (0 : Matrix n n α)⁻¹ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `Matrix.nonsing_inv_apply_not_isUnit`：nonsing_inv_apply_not_isUnit (h : ¬
IsUnit A.det) : A⁻¹ = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlternatingMap.map_zero`：map_zero [Nonempty ι] : f 0 = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
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
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : InvOneClass (Matrix n n α) :=
  { Matrix.one, Matrix.inv with inv_one := inv_eq_left_inv (by simp) }
/-
**Matrix.inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_smul (k : α) [Invertible k] (h : IsUnit A.det) : (k • A)⁻¹ = ⅟k • A⁻¹
参数：k : α；h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.inv_eq_left_inv`：inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `Matrix.nonsing_inv_mul`：nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_invOf_self'`：mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : a * ⅟a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_smul (k : α) [Invertible k] (h : IsUnit A.det) : (k • A)⁻¹ = ⅟k • A⁻¹ :=
  inv_eq_left_inv (by simp [h, smul_smul])
/-
**Matrix.inv_smul'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_smul' (k : αˣ) (h : IsUnit A.det) : (k • A)⁻¹ = k⁻¹ • A⁻¹
参数：k : αˣ；h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.inv_eq_left_inv`：inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_smul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Typ
e u_7} {α : Type v} [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintyp
e n] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Matrix.smul_mul`：smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] 
[IsScalarTower R α α] (a : R) (M : Matrix m n α) (N : Matrix n l α) : (a • M) * 
N = a…
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Matrix.nonsing_inv_mul`：nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_smul' (k : αˣ) (h : IsUnit A.det) : (k • A)⁻¹ = k⁻¹ • A⁻¹ :=
  inv_eq_left_inv (by simp [h, smul_smul])
/-
**Matrix.inv_adjugate** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_adjugate (A : Matrix n n α) (h : IsUnit A.det) : (adjugate A)⁻¹ = h.un
it⁻¹ • A
参数：A : Matrix n n α；h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.inv_eq_left_inv`：inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.smul_mul`：smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] 
[IsScalarTower R α α] (a : R) (M : Matrix m n α) (N : Matrix n l α) : (a • M) * 
N = a…
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Matrix.mul_adjugate`：mul_adjugate (A : Matrix n n α) : A * adjugate A = 
A.det • (1 : Matrix n n α)
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem inv_adjugate (A : Matrix n n α) (h : IsUnit A.det) : (adjugate A)⁻¹ = h.unit⁻¹ • A := by
  refine inv_eq_left_inv ?_
  rw [smul_mul, mul_adjugate, Units.smul_def, smul_smul, h.val_inv_mul, one_smul]

section Diagonal

attribute [local instance] Invertible.map in
/-- `diagonal v` is invertible if `v` is -/
@[instance_reducible]
/-
**Matrix.diagonalInvertible** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：diagonalInvertible {α} [NonAssocSemiring α] (v : n -> α) [Invertible v] : 
Invertible (diagonal v)
参数：v : n -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`diagonal v` is invertible if `v` is
-/
def diagonalInvertible {α} [NonAssocSemiring α] (v : n → α) [Invertible v] :
    Invertible (diagonal v) :=
  inferInstanceAs <| Invertible (diagonalRingHom n α v)
/-
**Matrix.invOf_diagonal_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：invOf_diagonal_eq {α} [Semiring α] (v : n -> α) [Invertible v] [Invertible
 (diagonal v)] : ⅟(diagonal v) = diagonal (⅟v)
参数：v : n -> α；diagonal v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Invertible.congr`：Invertible.congr [Invertible a] [Invertible b] (h : a 
= b) : ⅟a = ⅟b
-/
theorem invOf_diagonal_eq {α} [Semiring α] (v : n → α) [Invertible v] [Invertible (diagonal v)] :
    ⅟(diagonal v) = diagonal (⅟v) := by
  rw [@Invertible.congr _ _ _ _ _ (diagonalInvertible v) rfl]
  rfl

/-- `v` is invertible if `diagonal v` is -/
@[instance_reducible]
/-
**Matrix.invertibleOfDiagonalInvertible** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：invertibleOfDiagonalInvertible (v : n -> α) [Invertible (diagonal v)] : In
vertible v where invOf
参数：v : n -> α；diagonal v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`v` is invertible if `diagonal v` is
-/
def invertibleOfDiagonalInvertible (v : n → α) [Invertible (diagonal v)] : Invertible v where
  invOf := diag (⅟(diagonal v))
  invOf_mul_self :=
    funext fun i => by
      let : Invertible (diagonal v).det := detInvertibleOfInvertible _
      rw [invOf_eq, diag_smul, adjugate_diagonal, diag_diagonal]
      dsimp
      rw [mul_assoc, prod_erase_mul _ _ (Finset.mem_univ _), ← det_diagonal]
      exact mul_invOf_self _
  mul_invOf_self :=
    funext fun i => by
      let : Invertible (diagonal v).det := detInvertibleOfInvertible _
      rw [invOf_eq, diag_smul, adjugate_diagonal, diag_diagonal]
      dsimp
      rw [mul_left_comm, mul_prod_erase _ _ (Finset.mem_univ _), ← det_diagonal]
      exact mul_invOf_self _

/-- Together `Matrix.diagonalInvertible` and `Matrix.invertibleOfDiagonalInvertible` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
/-
**Matrix.diagonalInvertibleEquivInvertible** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：diagonalInvertibleEquivInvertible (v : n -> α) : Invertible (diagonal v) ≃
 Invertible v where toFun
参数：v : n -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Together `Matrix.diagonalInvertible` and `Matrix.invertibleOfDiagonalInvertible`
 form an
equivalence, although both sides of the equiv are subsingleton anyway.
-/
def diagonalInvertibleEquivInvertible (v : n → α) : Invertible (diagonal v) ≃ Invertible v where
  toFun := @invertibleOfDiagonalInvertible _ _ _ _ _ _
  invFun := @diagonalInvertible _ _ _ _ _ _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- When lowered to a prop, `Matrix.diagonalInvertibleEquivInvertible` forms an `iff`. -/
@[simp]
/-
**Matrix.isUnit_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isUnit_diagonal {v : n -> α} : IsUnit (diagonal v) ↔ IsUnit v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
When lowered to a prop, `Matrix.diagonalInvertibleEquivInvertible` forms an `iff
`.
-/
theorem isUnit_diagonal {v : n → α} : IsUnit (diagonal v) ↔ IsUnit v := by
  simp only [← nonempty_invertible_iff_isUnit,
    (diagonalInvertibleEquivInvertible v).nonempty_congr]
/-
**Matrix.inv_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_diagonal (v : n -> α) : (diagonal v)⁻¹ = diagonal v⁻¹ʳ
参数：v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.nonsing_inv_eq_ringInverse`：nonsing_inv_eq_ringInverse : A⁻¹ = A⁻
¹ʳ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.isUnit_diagonal`：isUnit_diagonal {v : n -> α} : IsUnit (diagonal 
v) ↔ IsUnit v
· 使用定理 `IsUnit.nonempty_invertible`：IsUnit.nonempty_invertible [Monoid α] {a : α
} (h : IsUnit a) : Nonempty (Invertible a)
· 使用定理 `Ring.inverse_invertible`：Ring.inverse_invertible (x : α) [Invertible x] 
: x⁻¹ʳ = ⅟x
· 使用定理 `Matrix.invOf_diagonal_eq`：invOf_diagonal_eq {α} [Semiring α] (v : n -> α
) [Invertible v] [Invertible (diagonal v)] : ⅟(diagonal v) = diagonal (⅟v)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `Pi.zero_def`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zero 
(M i)], 0 = fun x => 0
· 使用定理 `Matrix.diagonal_zero`：diagonal_zero [Zero α] : (diagonal fun _ => 0 : Ma
trix n n α) = 0
-/
theorem inv_diagonal (v : n → α) : (diagonal v)⁻¹ = diagonal v⁻¹ʳ := by
  rw [nonsing_inv_eq_ringInverse]
  by_cases h : IsUnit v
  · have := isUnit_diagonal.mpr h
    cases this.nonempty_invertible
    cases h.nonempty_invertible
    rw [Ring.inverse_invertible, Ring.inverse_invertible, invOf_diagonal_eq]
  · have := isUnit_diagonal.not.mpr h
    rw [Ring.inverse_non_unit _ h, Pi.zero_def, diagonal_zero, Ring.inverse_non_unit _ this]

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
/-
**Matrix.inv_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_subsingleton [Subsingleton m] [Fintype m] [DecidableEq m] (A : Matrix 
m m α) : A⁻¹ = diagonal fun i => (A i i)⁻¹ʳ
参数：A : Matrix m m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.inv_def`：inv_def (A : Matrix n n α) : A⁻¹ = A.det⁻¹ʳ • A.adjugate
· 使用定理 `Matrix.adjugate_subsingleton`：adjugate_subsingleton [Subsingleton n] (A 
: Matrix n n α) : adjugate A = 1
· 使用定理 `Matrix.smul_one_eq_diagonal`：smul_one_eq_diagonal [DecidableEq m] (a : α
) : a • (1 : Matrix m m α) = diagonal fun _ => a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.det_eq_elem_of_subsingleton`：det_eq_elem_of_subsingleton [Subsing
leton n] (A : Matrix n n R) (k : n) : det A = A k k

--- 原说明 ---
The inverse of a 1×1 or 0×0 matrix is always diagonal.

While we could write this as `of fun _ _ => (A default default)⁻¹ʳ` on the RHS, 
this is
less useful because:

* It wouldn't work for 0×0 matrices.
* More things are true about diagonal matrices than constant matrices, and so mo
re lemmas exist.

`Matrix.diagonal_unique` can be used to reach this form, while `Ring.inverse_eq_
inv` can be used
to replace `Ring.inverse` with `⁻¹`.
-/
theorem inv_subsingleton [Subsingleton m] [Fintype m] [DecidableEq m] (A : Matrix m m α) :
    A⁻¹ = diagonal fun i => (A i i)⁻¹ʳ := by
  rw [inv_def, adjugate_subsingleton, smul_one_eq_diagonal]
  congr! with i
  exact det_eq_elem_of_subsingleton _ _

section Woodbury

variable [Fintype m] [DecidableEq m]
variable (A : Matrix n n α) (U : Matrix n m α) (C : Matrix m m α) (V : Matrix m n α)

/-- The **Woodbury Identity** (`⁻¹` version).

See `add_mul_mul_inv_eq_sub'` for the binomial inverse theorem. -/
/-
**Matrix.add_mul_mul_inv_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：add_mul_mul_inv_eq_sub (hA : IsUnit A) (hC : IsUnit C) (hAC : IsUnit (C⁻¹ 
+ V * A⁻¹ * U)) : (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V 
* A⁻¹
参数：hA : IsUnit A；hC : IsUnit C；hAC : IsUnit (C⁻¹ + V * A⁻¹ * U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.nonempty_invertible`：IsUnit.nonempty_invertible [Monoid α] {a : α
} (h : IsUnit a) : Nonempty (Invertible a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.invOf_add_mul_mul`：invOf_add_mul_mul [Invertible (A + U * C * V)]
 : ⅟(A + U * C * V) = ⅟A - ⅟A * U * ⅟(⅟C + V * ⅟A * U) * V * ⅟A

--- 原说明 ---
The **Woodbury Identity** (`⁻¹` version).

See `add_mul_mul_inv_eq_sub'` for the binomial inverse theorem.
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

/-- The **binomial inverse theorem** (variant of the Woodbury identity). -/
/-
**Matrix.add_mul_mul_inv_eq_sub'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：add_mul_mul_inv_eq_sub' (hA : IsUnit A) (h : IsUnit (C + C * V * A⁻¹ * U *
 C)) : (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * C * (C + C * V * A⁻¹ * U * C)⁻¹ * C *
 V * A⁻¹
参数：hA : IsUnit A；h : IsUnit (C + C * V * A⁻¹ * U * C)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.nonempty_invertible`：IsUnit.nonempty_invertible [Monoid α] {a : α
} (h : IsUnit a) : Nonempty (Invertible a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.invOf_add_mul_mul'`：invOf_add_mul_mul' [Invertible (A + U * C * V
)] : ⅟(A + U * C * V) = ⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A

--- 原说明 ---
The **binomial inverse theorem** (variant of the Woodbury identity).
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
/-
**Matrix.inv_inv_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_inv_inv (A : Matrix n n α) : A⁻¹⁻¹⁻¹ = A⁻¹
参数：A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.nonsing_inv_nonsing_inv`：nonsing_inv_nonsing_inv (h : IsUnit A.de
t) : A⁻¹⁻¹ = A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.nonsing_inv_apply_not_isUnit`：nonsing_inv_apply_not_isUnit (h : ¬
IsUnit A.det) : A⁻¹ = 0
· 使用定理 `Matrix.inv_zero`：inv_zero : (0 : Matrix n n α)⁻¹ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_inv_inv (A : Matrix n n α) : A⁻¹⁻¹⁻¹ = A⁻¹ := by
  by_cases h : IsUnit A.det
  · rw [nonsing_inv_nonsing_inv _ h]
  · simp [nonsing_inv_apply_not_isUnit _ h]

/-- The `Matrix` version of `inv_add_inv'` -/
/-
**Matrix.inv_add_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_add_inv {A B : Matrix n n α} (h : IsUnit A ↔ IsUnit B) : A⁻¹ + B⁻¹ = A
⁻¹ * (A + B) * B⁻¹
参数：h : IsUnit A ↔ IsUnit B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.nonsing_inv_eq_ringInverse`：nonsing_inv_eq_ringInverse : A⁻¹ = A⁻
¹ʳ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ring.inverse_add_inverse`：Ring.inverse_add_inverse [Semiring R] {a b : R
} (h : IsUnit a ↔ IsUnit b) : a⁻¹ʳ + b⁻¹ʳ = a⁻¹ʳ * (a + b) * b⁻¹ʳ

--- 原说明 ---
The `Matrix` version of `inv_add_inv'`
-/
theorem inv_add_inv {A B : Matrix n n α} (h : IsUnit A ↔ IsUnit B) :
    A⁻¹ + B⁻¹ = A⁻¹ * (A + B) * B⁻¹ := by
  simpa only [nonsing_inv_eq_ringInverse] using Ring.inverse_add_inverse h

/-- The `Matrix` version of `inv_sub_inv'` -/
/-
**Matrix.inv_sub_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_sub_inv {A B : Matrix n n α} (h : IsUnit A ↔ IsUnit B) : A⁻¹ - B⁻¹ = A
⁻¹ * (B - A) * B⁻¹
参数：h : IsUnit A ↔ IsUnit B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.nonsing_inv_eq_ringInverse`：nonsing_inv_eq_ringInverse : A⁻¹ = A⁻
¹ʳ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ring.inverse_sub_inverse`：Ring.inverse_sub_inverse [Ring R] {a b : R} (h
 : IsUnit a ↔ IsUnit b) : a⁻¹ʳ - b⁻¹ʳ = a⁻¹ʳ * (b - a) * b⁻¹ʳ

--- 原说明 ---
The `Matrix` version of `inv_sub_inv'`
-/
theorem inv_sub_inv {A B : Matrix n n α} (h : IsUnit A ↔ IsUnit B) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  simpa only [nonsing_inv_eq_ringInverse] using Ring.inverse_sub_inverse h
/-
**Matrix.mul_inv_rev** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_inv_rev (A B : Matrix n n α) : (A * B)⁻¹ = B⁻¹ * A⁻¹
参数：A B : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.smul_mul`：smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] 
[IsScalarTower R α α] (a : R) (M : Matrix m n α) (N : Matrix n l α) : (a • M) * 
N = a…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Matrix.mul_smul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Typ
e u_7} {α : Type v} [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintyp
e n] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.adjugate_mul_distrib`：adjugate_mul_distrib (A B : Matrix n n α) :
 adjugate (A * B) = adjugate B * adjugate A
· 使用定理 `Ring.mul_inverse_rev`：mul_inverse_rev {M₀} [CommMonoidWithZero M₀] (a b 
: M₀) : (a * b)⁻¹ʳ = b⁻¹ʳ * a⁻¹ʳ
-/
theorem mul_inv_rev (A B : Matrix n n α) : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
  simp only [inv_def]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, det_mul, adjugate_mul_distrib,
    Ring.mul_inverse_rev]

/-- A version of `List.prod_inv_reverse` for `Matrix.inv`. -/
/-
**Matrix.list_prod_inv_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u'} {α : Type v} [inst : Fintype n] [inst_1 : DecidableEq n] [
inst_2 : CommRing α]   (l : List (Matrix n n α)), l.prod⁻¹ = (List.map Inv.inv l
.reverse).prod
参数：l : List (Matrix n n α)；List.map Inv.inv l.reverse。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `List.prod_inv_reverse` for `Matrix.inv`.
-/
theorem list_prod_inv_reverse : ∀ l : List (Matrix n n α), l.prod⁻¹ = (l.reverse.map Inv.inv).prod
  | [] => by rw [List.reverse_nil, List.map_nil, List.prod_nil, inv_one]
  | A::Xs => by
    rw [List.reverse_cons', List.map_concat, List.prod_concat, List.prod_cons,
      mul_inv_rev, list_prod_inv_reverse Xs]

/-- One form of **Cramer's rule**. See `Matrix.mulVec_cramer` for a stronger form. -/
@[simp]
/-
**Matrix.det_smul_inv_mulVec_eq_cramer** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_smul_inv_mulVec_eq_cramer (A : Matrix n n α) (b : n -> α) (h : IsUnit 
A.det) : A.det • A⁻¹ *ᵥ b = cramer A b
参数：A : Matrix n n α；b : n -> α；h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cramer_eq_adjugate_mulVec`：cramer_eq_adjugate_mulVec (A : Matrix 
n n α) (b : n -> α) : cramer A b = A.adjugate *ᵥ b
· 使用定理 `Matrix.nonsing_inv_apply`：nonsing_inv_apply (h : IsUnit A.det) : A⁻¹ = (
↑h.unit⁻¹ : α) • A.adjugate
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.smul_mulVec`：smul_mulVec [Fintype n] [DistribSMul R α] [IsScalarT
ower R α α] (b : R) (M : Matrix m n α) (v : n -> α) : (b • M) *ᵥ v = b • M *ᵥ v
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
One form of **Cramer's rule**. See `Matrix.mulVec_cramer` for a stronger form.
-/
theorem det_smul_inv_mulVec_eq_cramer (A : Matrix n n α) (b : n → α) (h : IsUnit A.det) :
    A.det • A⁻¹ *ᵥ b = cramer A b := by
  rw [cramer_eq_adjugate_mulVec, A.nonsing_inv_apply h, ← smul_mulVec, smul_smul,
    h.mul_val_inv, one_smul]

/-- One form of **Cramer's rule**. See `Matrix.mulVec_cramer` for a stronger form. -/
@[simp]
/-
**Matrix.det_smul_inv_vecMul_eq_cramer_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matr
ix`。
形式化陈述：det_smul_inv_vecMul_eq_cramer_transpose (A : Matrix n n α) (b : n -> α) (h
 : IsUnit A.det) : A.det • b ᵥ* A⁻¹ = cramer Aᵀ b
参数：A : Matrix n n α；b : n -> α；h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `Matrix.vecMul_transpose`：vecMul_transpose [Fintype n] (A : Matrix m n α)
 (x : n -> α) : x ᵥ* Aᵀ = A *ᵥ x
· 使用定理 `Matrix.transpose_nonsing_inv`：transpose_nonsing_inv : A⁻¹ᵀ = Aᵀ⁻¹
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.det_smul_inv_mulVec_eq_cramer`：det_smul_inv_mulVec_eq_cramer (A :
 Matrix n n α) (b : n -> α) (h : IsUnit A.det) : A.det • A⁻¹ *ᵥ b = cramer A b
· 使用定理 `Matrix.isUnit_det_transpose`：isUnit_det_transpose (h : IsUnit A.det) : I
sUnit Aᵀ.det

--- 原说明 ---
One form of **Cramer's rule**. See `Matrix.mulVec_cramer` for a stronger form.
-/
theorem det_smul_inv_vecMul_eq_cramer_transpose (A : Matrix n n α) (b : n → α) (h : IsUnit A.det) :
    A.det • b ᵥ* A⁻¹ = cramer Aᵀ b := by
  rw [← A⁻¹.transpose_transpose, vecMul_transpose, transpose_nonsing_inv, ← det_transpose,
    Aᵀ.det_smul_inv_mulVec_eq_cramer _ (isUnit_det_transpose A h)]

/-! ### Inverses of permutated matrices

Note that the simp-normal form of `Matrix.reindex` is `Matrix.submatrix`, so we prove most of these
results about only the latter.
-/


section Submatrix

variable [Fintype m]
variable [DecidableEq m]

/-- `A.submatrix e₁ e₂` is invertible if `A` is -/
@[instance_reducible]
/-
**Matrix.submatrixEquivInvertible** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：submatrixEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m) [Invertible A]
 : Invertible (A.submatrix e₁ e₂)
参数：A : Matrix m m α；e₁ e₂ : n ≃ m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A.submatrix e₁ e₂` is invertible if `A` is
-/
def submatrixEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m) [Invertible A] :
    Invertible (A.submatrix e₁ e₂) :=
  invertibleOfRightInverse _ ((⅟A).submatrix e₂ e₁) <| by
    rw [Matrix.submatrix_mul_equiv, mul_invOf_self, submatrix_one_equiv]

/-- `A` is invertible if `A.submatrix e₁ e₂` is -/
@[instance_reducible]
/-
**Matrix.invertibleOfSubmatrixEquivInvertible** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`
。
形式化陈述：invertibleOfSubmatrixEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m) [I
nvertible (A.submatrix e₁ e₂)] : Invertible A
参数：A : Matrix m m α；e₁ e₂ : n ≃ m；A.submatrix e₁ e₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`A` is invertible if `A.submatrix e₁ e₂` is
-/
def invertibleOfSubmatrixEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m)
    [Invertible (A.submatrix e₁ e₂)] : Invertible A :=
  invertibleOfRightInverse _ ((⅟(A.submatrix e₁ e₂)).submatrix e₂.symm e₁.symm) <| by
    have : A = (A.submatrix e₁ e₂).submatrix e₁.symm e₂.symm := by simp
    conv in _ * _ =>
      congr
      rw [this]
    rw [Matrix.submatrix_mul_equiv, mul_invOf_self, submatrix_one_equiv]
/-
**Matrix.invOf_submatrix_equiv_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：invOf_submatrix_equiv_eq (A : Matrix m m α) (e₁ e₂ : n ≃ m) [Invertible A]
 [Invertible (A.submatrix e₁ e₂)] : ⅟(A.submatrix e₁ e₂) = (⅟A).submatrix e₂ e₁
参数：A : Matrix m m α；e₁ e₂ : n ≃ m；A.submatrix e₁ e₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Invertible.congr`：Invertible.congr [Invertible a] [Invertible b] (h : a 
= b) : ⅟a = ⅟b
-/
theorem invOf_submatrix_equiv_eq (A : Matrix m m α) (e₁ e₂ : n ≃ m) [Invertible A]
    [Invertible (A.submatrix e₁ e₂)] : ⅟(A.submatrix e₁ e₂) = (⅟A).submatrix e₂ e₁ := by
  rw [@Invertible.congr _ _ _ _ _ (submatrixEquivInvertible A e₁ e₂) rfl]
  rfl

/-- Together `Matrix.submatrixEquivInvertible` and
`Matrix.invertibleOfSubmatrixEquivInvertible` form an equivalence, although both sides of the
equiv are subsingleton anyway. -/
@[simps]
/-
**Matrix.submatrixEquivInvertibleEquivInvertible** 是 Mathlib 中的一个定义，位于命名空间 `Matr
ix`。
形式化陈述：submatrixEquivInvertibleEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m)
 : Invertible (A.submatrix e₁ e₂) ≃ Invertible A where toFun _
参数：A : Matrix m m α；e₁ e₂ : n ≃ m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Together `Matrix.submatrixEquivInvertible` and
`Matrix.invertibleOfSubmatrixEquivInvertible` form an equivalence, although both
 sides of the
equiv are subsingleton anyway.
-/
def submatrixEquivInvertibleEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m) :
    Invertible (A.submatrix e₁ e₂) ≃ Invertible A where
  toFun _ := invertibleOfSubmatrixEquivInvertible A e₁ e₂
  invFun _ := submatrixEquivInvertible A e₁ e₂
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- When lowered to a prop, `Matrix.invertibleOfSubmatrixEquivInvertible` forms an `iff`. -/
@[simp]
/-
**Matrix.isUnit_submatrix_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isUnit_submatrix_equiv {A : Matrix m m α} (e₁ e₂ : n ≃ m) : IsUnit (A.subm
atrix e₁ e₂) ↔ IsUnit A
参数：e₁ e₂ : n ≃ m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
When lowered to a prop, `Matrix.invertibleOfSubmatrixEquivInvertible` forms an `
iff`.
-/
theorem isUnit_submatrix_equiv {A : Matrix m m α} (e₁ e₂ : n ≃ m) :
    IsUnit (A.submatrix e₁ e₂) ↔ IsUnit A := by
  simp only [← nonempty_invertible_iff_isUnit,
    (submatrixEquivInvertibleEquivInvertible A _ _).nonempty_congr]

@[simp]
/-
**Matrix.inv_submatrix_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_submatrix_equiv (A : Matrix m m α) (e₁ e₂ : n ≃ m) : (A.submatrix e₁ e
₂)⁻¹ = A⁻¹.submatrix e₂ e₁
参数：A : Matrix m m α；e₁ e₂ : n ≃ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.nonempty_invertible`：IsUnit.nonempty_invertible [Monoid α] {a : α
} (h : IsUnit a) : Nonempty (Invertible a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.invOf_eq_nonsing_inv`：invOf_eq_nonsing_inv [Invertible A] : ⅟A = 
A⁻¹
· 使用定理 `Matrix.invOf_submatrix_equiv_eq`：invOf_submatrix_equiv_eq (A : Matrix m 
m α) (e₁ e₂ : n ≃ m) [Invertible A] [Invertible (A.submatrix e₁ e₂)] : ⅟(A.subma
trix e₁ e₂) = (⅟A).su…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Matrix.isUnit_submatrix_equiv`：isUnit_submatrix_equiv {A : Matrix m m α}
 (e₁ e₂ : n ≃ m) : IsUnit (A.submatrix e₁ e₂) ↔ IsUnit A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.nonsing_inv_eq_ringInverse`：nonsing_inv_eq_ringInverse : A⁻¹ = A⁻
¹ʳ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_submatrix_equiv (A : Matrix m m α) (e₁ e₂ : n ≃ m) :
    (A.submatrix e₁ e₂)⁻¹ = A⁻¹.submatrix e₂ e₁ := by
  by_cases h : IsUnit A
  · cases h.nonempty_invertible
    let := submatrixEquivInvertible A e₁ e₂
    rw [← invOf_eq_nonsing_inv, ← invOf_eq_nonsing_inv, invOf_submatrix_equiv_eq A]
  · have := (isUnit_submatrix_equiv e₁ e₂).not.mpr h
    simp_rw [nonsing_inv_eq_ringInverse, Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ this,
      submatrix_zero, Pi.zero_apply]
/-
**Matrix.inv_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_reindex (e₁ e₂ : n ≃ m) (A : Matrix n n α) : (reindex e₁ e₂ A)⁻¹ = rei
ndex e₂ e₁ A⁻¹
参数：e₁ e₂ : n ≃ m；A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.inv_submatrix_equiv`：inv_submatrix_equiv (A : Matrix m m α) (e₁ e
₂ : n ≃ m) : (A.submatrix e₁ e₂)⁻¹ = A⁻¹.submatrix e₂ e₁
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem inv_reindex (e₁ e₂ : n ≃ m) (A : Matrix n n α) : (reindex e₁ e₂ A)⁻¹ = reindex e₂ e₁ A⁻¹ :=
  inv_submatrix_equiv A e₁.symm e₂.symm

end Submatrix

open scoped Kronecker in
/-
**Matrix.inv_kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_kronecker [Fintype m] [DecidableEq m] (A : Matrix m m α) (B : Matrix n
 n α) : (A otimesₖ B)⁻¹ = A⁻¹ otimesₖ B⁻¹
参数：A : Matrix m m α；B : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.inv_eq_right_inv`：inv_eq_right_inv (h : A * B = 1) : A⁻¹ = B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_kronecker_mul`：mul_kronecker_mul [Fintype m] [Fintype m'] [Co
mmSemiring α] (A : Matrix l m α) (B : Matrix m n α) (A' : Matrix l' m' α) (B' : 
Matrix m' n' α…
· 使用定理 `Matrix.one_kronecker_one`：one_kronecker_one [MulZeroOneClass α] [Decidab
leEq m] [DecidableEq n] : (1 : Matrix m m α) otimesₖ (1 : Matrix n n α) = 1
· 使用定理 `Matrix.mul_nonsing_inv`：mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_pow_iff`：∀ {M : Type u_1} [inst : Monoid M] {n : ℕ} {a : M}, n ≠ 
0 → (IsUnit (a ^ n) ↔ IsUnit a)
· 使用定理 `Fintype.card_ne_zero`：card_ne_zero [Nonempty α] : card α != 0
· 使用定理 `isUnit_of_mul_isUnit_right`：isUnit_of_mul_isUnit_right [Monoid M] [IsDed
ekindFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit y
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Matrix.det_kronecker`：det_kronecker [Fintype m] [Fintype n] [DecidableEq
 m] [DecidableEq n] [CommRing R] (A : Matrix m m R) (B : Matrix n n R) : det (A 
otimesₖ B)…
· 使用定理 `Matrix.nonsing_inv_apply_not_isUnit`：nonsing_inv_apply_not_isUnit (h : ¬
IsUnit A.det) : A⁻¹ = 0
· 使用定理 `Matrix.kronecker_zero`：kronecker_zero [MulZeroClass α] (A : Matrix l m α
) : A otimesₖ (0 : Matrix n p α) = 0
· 使用定理 `isUnit_of_mul_isUnit_left`：isUnit_of_mul_isUnit_left [Monoid M] [IsDedek
indFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit x
· 使用定理 `Matrix.zero_kronecker`：zero_kronecker [MulZeroClass α] (B : Matrix n p α
) : (0 : Matrix l m α) otimesₖ B = 0
-/
theorem inv_kronecker [Fintype m] [DecidableEq m]
    (A : Matrix m m α) (B : Matrix n n α) : (A ⊗ₖ B)⁻¹ = A⁻¹ ⊗ₖ B⁻¹ := by
  -- handle the special cases where either matrix is not invertible
  by_cases hA : IsUnit A.det
  swap
  · cases isEmpty_or_nonempty n
    · subsingleton
    have hAB : ¬IsUnit (A ⊗ₖ B).det := by
      refine mt (fun hAB => ?_) hA
      rw [det_kronecker] at hAB
      exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_left hAB)
    rw [nonsing_inv_apply_not_isUnit _ hA, zero_kronecker, nonsing_inv_apply_not_isUnit _ hAB]
  by_cases hB : IsUnit B.det; swap
  · cases isEmpty_or_nonempty m
    · subsingleton
    have hAB : ¬IsUnit (A ⊗ₖ B).det := by
      refine mt (fun hAB => ?_) hB
      rw [det_kronecker] at hAB
      exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_right hAB)
    rw [nonsing_inv_apply_not_isUnit _ hB, kronecker_zero, nonsing_inv_apply_not_isUnit _ hAB]
  -- otherwise follows trivially from `mul_kronecker_mul`
  · apply inv_eq_right_inv
    rw [← mul_kronecker_mul, ← one_kronecker_one, mul_nonsing_inv _ hA, mul_nonsing_inv _ hB]


/-! ### More results about determinants -/


section Det

variable [Fintype m] [DecidableEq m]

/-- A variant of `Matrix.det_units_conj`. -/
/-
**Matrix.det_conj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_conj {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) : det (M * N
 * M⁻¹) = det N
参数：h : IsUnit M；N : Matrix m m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `Matrix.coe_units_inv`：coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ 
: Matrix n n α)
· 使用定理 `Matrix.det_units_conj`：det_units_conj (M : (Matrix m m R)ˣ) (N : Matrix 
m m R) : det (M.val * N * M⁻¹.val) = det N

--- 原说明 ---
A variant of `Matrix.det_units_conj`.
-/
theorem det_conj {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) :
    det (M * N * M⁻¹) = det N := by rw [← h.unit_spec, ← coe_units_inv, det_units_conj]

/-- A variant of `Matrix.det_units_conj'`. -/
/-
**Matrix.det_conj'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_conj' {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) : det (M⁻¹ 
* N * M) = det N
参数：h : IsUnit M；N : Matrix m m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `Matrix.coe_units_inv`：coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ 
: Matrix n n α)
· 使用定理 `Matrix.det_units_conj'`：det_units_conj' (M : (Matrix m m R)ˣ) (N : Matri
x m m R) : det (M⁻¹.val * N * ↑M.val) = det N

--- 原说明 ---
A variant of `Matrix.det_units_conj'`.
-/
theorem det_conj' {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) :
    det (M⁻¹ * N * M) = det N := by rw [← h.unit_spec, ← coe_units_inv, det_units_conj']

end Det

/-! ### More results about traces -/


section trace

variable [Fintype m] [DecidableEq m]

/-- A variant of `Matrix.trace_units_conj`. -/
/-
**Matrix.trace_conj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_conj {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) : trace (M
 * N * M⁻¹) = trace N
参数：h : IsUnit M；N : Matrix m m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `Matrix.coe_units_inv`：coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ 
: Matrix n n α)
· 使用定理 `Matrix.trace_units_conj`：trace_units_conj (M : (Matrix m m R)ˣ) (N : Mat
rix m m R) : trace ((M : Matrix _ _ _) * N * (↑M⁻¹ : Matrix _ _ _)) = trace N

--- 原说明 ---
A variant of `Matrix.trace_units_conj`.
-/
theorem trace_conj {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) :
    trace (M * N * M⁻¹) = trace N := by rw [← h.unit_spec, ← coe_units_inv, trace_units_conj]

/-- A variant of `Matrix.trace_units_conj'`. -/
/-
**Matrix.trace_conj'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_conj' {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) : trace (
M⁻¹ * N * M) = trace N
参数：h : IsUnit M；N : Matrix m m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `Matrix.coe_units_inv`：coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ 
: Matrix n n α)
· 使用定理 `Matrix.trace_units_conj'`：trace_units_conj' (M : (Matrix m m R)ˣ) (N : M
atrix m m R) : trace ((↑M⁻¹ : Matrix _ _ _) * N * (↑M : Matrix _ _ _)) = trace N

--- 原说明 ---
A variant of `Matrix.trace_units_conj'`.
-/
theorem trace_conj' {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) :
    trace (M⁻¹ * N * M) = trace N := by rw [← h.unit_spec, ← coe_units_inv, trace_units_conj']

end trace

end Matrix

