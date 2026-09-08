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

/-- A copy of `invOf_mul_cancel_left` for rectangular matrices. -/
/-
**Matrix.invOf_mul_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [inst : Fintype n] [inst_1 
: DecidableEq n] [inst_2 : Semiring α]   (A : Matrix n n α) (B : Matrix n m α) [
inst_3 : Invertible A], ⅟A * (A * B) = B
参数：A : Matrix n n α；B : Matrix n m α；A * B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…

--- 原说明 ---
A copy of `invOf_mul_cancel_left` for rectangular matrices.
-/
protected theorem invOf_mul_cancel_left (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    ⅟A * (A * B) = B := by rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]

/-- A copy of `mul_invOf_cancel_left` for rectangular matrices. -/
/-
**Matrix.mul_invOf_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [inst : Fintype n] [inst_1 
: DecidableEq n] [inst_2 : Semiring α]   (A : Matrix n n α) (B : Matrix n m α) [
inst_3 : Invertible A], A * (⅟A * B) = B
参数：A : Matrix n n α；B : Matrix n m α；⅟A * B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…

--- 原说明 ---
A copy of `mul_invOf_cancel_left` for rectangular matrices.
-/
protected theorem mul_invOf_cancel_left (A : Matrix n n α) (B : Matrix n m α) [Invertible A] :
    A * (⅟A * B) = B := by rw [← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]

/-- A copy of `invOf_mul_cancel_right` for rectangular matrices. -/
/-
**Matrix.invOf_mul_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [inst : Fintype n] [inst_1 
: DecidableEq n] [inst_2 : Semiring α]   (A : Matrix m n α) (B : Matrix n n α) [
inst_3 : Invertible B], A * ⅟B * B = A
参数：A : Matrix m n α；B : Matrix n n α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…

--- 原说明 ---
A copy of `invOf_mul_cancel_right` for rectangular matrices.
-/
protected theorem invOf_mul_cancel_right (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A * ⅟B * B = A := by rw [Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]

/-- A copy of `mul_invOf_cancel_right` for rectangular matrices. -/
/-
**Matrix.mul_invOf_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [inst : Fintype n] [inst_1 
: DecidableEq n] [inst_2 : Semiring α]   (A : Matrix m n α) (B : Matrix n n α) [
inst_3 : Invertible B], A * B * ⅟B = A
参数：A : Matrix m n α；B : Matrix n n α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…

--- 原说明 ---
A copy of `mul_invOf_cancel_right` for rectangular matrices.
-/
protected theorem mul_invOf_cancel_right (A : Matrix m n α) (B : Matrix n n α) [Invertible B] :
    A * B * ⅟B = A := by rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]

/-- A copy oy of `invOf_mul_eq_iff_eq_mul_left` for rectangular matrices. -/
/-
**Matrix.invOf_mul_eq_iff_eq_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [inst : Fintype n] [inst_1 
: DecidableEq n] [inst_2 : Semiring α]   {A B : Matrix n m α} {C : Matrix n n α}
 [inst_3 : Invertible C], ⅟C * A = B ↔ A = C * B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_invOf_cancel_left`：∀ {m : Type u_1} {n : Type u_2} {α : Type 
u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring α]   (A : Ma
trix n n α) (B : M…
· 使用定理 `Matrix.invOf_mul_cancel_left`：∀ {m : Type u_1} {n : Type u_2} {α : Type 
u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring α]   (A : Ma
trix n n α) (B : M…

--- 原说明 ---
A copy oy of `invOf_mul_eq_iff_eq_mul_left` for rectangular matrices.
-/
protected theorem invOf_mul_eq_iff_eq_mul_left
    {A B : Matrix n m α} {C : Matrix n n α} [Invertible C] :
    ⅟C * A = B ↔ A = C * B := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h, Matrix.mul_invOf_cancel_left]
  · rw [h, Matrix.invOf_mul_cancel_left]

/-- A copy oy of `mul_left_eq_iff_eq_invOf_mul` for rectangular matrices. -/
/-
**Matrix.mul_left_eq_iff_eq_invOf_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [inst : Fintype n] [inst_1 
: DecidableEq n] [inst_2 : Semiring α]   {A B : Matrix n m α} {C : Matrix n n α}
 [inst_3 : Invertible C], C * A = B ↔ A = ⅟C * B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.invOf_mul_eq_iff_eq_mul_left`：∀ {m : Type u_1} {n : Type u_2} {α 
: Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring α]   
{A B : Matrix n m α} {C :…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A copy oy of `mul_left_eq_iff_eq_invOf_mul` for rectangular matrices.
-/
protected theorem mul_left_eq_iff_eq_invOf_mul
    {A B : Matrix n m α} {C : Matrix n n α} [Invertible C] :
    C * A = B ↔ A = ⅟C * B := by
  rw [eq_comm, ← Matrix.invOf_mul_eq_iff_eq_mul_left, eq_comm]

/-- A copy oy of `mul_invOf_eq_iff_eq_mul_right` for rectangular matrices. -/
/-
**Matrix.mul_invOf_eq_iff_eq_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [inst : Fintype n] [inst_1 
: DecidableEq n] [inst_2 : Semiring α]   {A B : Matrix m n α} {C : Matrix n n α}
 [inst_3 : Invertible C], A * ⅟C = B ↔ A = B * C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.invOf_mul_cancel_right`：∀ {m : Type u_1} {n : Type u_2} {α : Type
 u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring α]   (A : M
atrix m n α) (B : M…
· 使用定理 `Matrix.mul_invOf_cancel_right`：∀ {m : Type u_1} {n : Type u_2} {α : Type
 u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring α]   (A : M
atrix m n α) (B : M…

--- 原说明 ---
A copy oy of `mul_invOf_eq_iff_eq_mul_right` for rectangular matrices.
-/
protected theorem mul_invOf_eq_iff_eq_mul_right
    {A B : Matrix m n α} {C : Matrix n n α} [Invertible C] :
    A * ⅟C = B ↔ A = B * C := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h, Matrix.invOf_mul_cancel_right]
  · rw [h, Matrix.mul_invOf_cancel_right]

/-- A copy oy of `mul_right_eq_iff_eq_mul_invOf` for rectangular matrices. -/
/-
**Matrix.mul_right_eq_iff_eq_mul_invOf** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [inst : Fintype n] [inst_1 
: DecidableEq n] [inst_2 : Semiring α]   {A B : Matrix m n α} {C : Matrix n n α}
 [inst_3 : Invertible C], A * C = B ↔ A = B * ⅟C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_invOf_eq_iff_eq_mul_right`：∀ {m : Type u_1} {n : Type u_2} {α
 : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring α]  
 {A B : Matrix m n α} {C :…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A copy oy of `mul_right_eq_iff_eq_mul_invOf` for rectangular matrices.
-/
protected theorem mul_right_eq_iff_eq_mul_invOf
    {A B : Matrix m n α} {C : Matrix n n α} [Invertible C] :
    A * C = B ↔ A = B * ⅟C := by
  rw [eq_comm, ← Matrix.mul_invOf_eq_iff_eq_mul_right, eq_comm]

section ConjTranspose
variable [StarRing α] (A : Matrix n n α)

/-- The conjugate transpose of an invertible matrix is invertible. -/
/-
**Matrix.invertibleConjTranspose** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：invertibleConjTranspose [Invertible A] : Invertible Aᴴ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conjugate transpose of an invertible matrix is invertible.
-/
instance invertibleConjTranspose [Invertible A] : Invertible Aᴴ := Invertible.star _
/-
**Matrix.conjTranspose_invOf** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_invOf [Invertible A] [Invertible Aᴴ] : (⅟A)ᴴ = ⅟(Aᴴ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `star_invOf`：star_invOf {R : Type*} [Monoid R] [StarMul R] (r : R) [Inver
tible r] [Invertible (star r)] : star (⅟r) = ⅟(star r)
-/
lemma conjTranspose_invOf [Invertible A] [Invertible Aᴴ] : (⅟A)ᴴ = ⅟(Aᴴ) := star_invOf _

/-- A matrix is invertible if the conjugate transpose is invertible. -/
@[implicit_reducible]
/-
**Matrix.invertibleOfInvertibleConjTranspose** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：invertibleOfInvertibleConjTranspose [Invertible Aᴴ] : Invertible A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix is invertible if the conjugate transpose is invertible.
-/
def invertibleOfInvertibleConjTranspose [Invertible Aᴴ] : Invertible A := by
  rw [← conjTranspose_conjTranspose A, ← star_eq_conjTranspose]
  infer_instance
/-
**Matrix.isUnit_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_2} {α : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : Semiring α] [inst_3 : StarRing α]   (A : Matrix n n α), IsUnit A.con
jTranspose ↔ IsUnit A
参数：A : Matrix n n α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_star`：isUnit_star [Monoid R] [StarMul R] {a : R} : IsUnit (star a
) ↔ IsUnit a
-/
@[simp] lemma isUnit_conjTranspose : IsUnit Aᴴ ↔ IsUnit A := isUnit_star

end ConjTranspose

end Semiring

section CommSemiring

variable [CommSemiring α] (A : Matrix n n α)

/-- The transpose of an invertible matrix is invertible. -/
/-
**Matrix.invertibleTranspose** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：invertibleTranspose [Invertible A] : Invertible Aᵀ where invOf
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transpose of an invertible matrix is invertible.
-/
instance invertibleTranspose [Invertible A] : Invertible Aᵀ where
  invOf := (⅟A)ᵀ
  invOf_mul_self := by rw [← transpose_mul, mul_invOf_self, transpose_one]
  mul_invOf_self := by rw [← transpose_mul, invOf_mul_self, transpose_one]
/-
**Matrix.transpose_invOf** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：transpose_invOf [Invertible A] [Invertible Aᵀ] : (⅟A)ᵀ = ⅟(Aᵀ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Invertible.congr`：Invertible.congr [Invertible a] [Invertible b] (h : a 
= b) : ⅟a = ⅟b
-/
lemma transpose_invOf [Invertible A] [Invertible Aᵀ] : (⅟A)ᵀ = ⅟(Aᵀ) := by
  let := invertibleTranspose A
  convert! (rfl : _ = ⅟(Aᵀ))

/-- `Aᵀ` is invertible when `A` is. -/
@[implicit_reducible]
/-
**Matrix.invertibleOfInvertibleTranspose** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：invertibleOfInvertibleTranspose [Invertible Aᵀ] : Invertible A where invOf
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Aᵀ` is invertible when `A` is.
-/
def invertibleOfInvertibleTranspose [Invertible Aᵀ] : Invertible A where
  invOf := (⅟(Aᵀ))ᵀ
  invOf_mul_self := by rw [← transpose_one, ← mul_invOf_self Aᵀ, transpose_mul, transpose_transpose]
  mul_invOf_self := by rw [← transpose_one, ← invOf_mul_self Aᵀ, transpose_mul, transpose_transpose]

/-- Together `Matrix.invertibleTranspose` and `Matrix.invertibleOfInvertibleTranspose` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
/-
**Matrix.transposeInvertibleEquivInvertible** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：transposeInvertibleEquivInvertible : Invertible Aᵀ ≃ Invertible A where to
Fun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Together `Matrix.invertibleTranspose` and `Matrix.invertibleOfInvertibleTranspos
e` form an
equivalence, although both sides of the equiv are subsingleton anyway.
-/
def transposeInvertibleEquivInvertible : Invertible Aᵀ ≃ Invertible A where
  toFun := @invertibleOfInvertibleTranspose _ _ _ _ _ _
  invFun := @invertibleTranspose _ _ _ _ _ _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
/-
**Matrix.isUnit_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_2} {α : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring α]   (A : Matrix n n α), IsUnit A.transpose ↔ IsUnit A
参数：A : Matrix n n α。
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
/-
**Matrix.add_mul_mul_invOf_mul_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：add_mul_mul_invOf_mul_eq_one : (A + U*C*V)*(⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)
 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.Invertible.0.Matrix.add_mul_mul_in
vOf_mul_eq_one._abel_1_1`：∀ {m : Type u_3} {n : Type u_1} {α : Type u_2} [inst :
 Fintype n] [inst_1 : DecidableEq n] [inst_2 : Fintype m]   [inst_3 : DecidableE
q m] […
· 使用定理 `sub_right_inj`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a - b =
 a - c ↔ b = c
· 使用定理 `Matrix.add_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (L M : Matrix l 
m α)…
· 使用定理 `Matrix.mul_add`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (L : Matrix m n 
α) (…
· 使用定理 `Matrix.mul_invOf_cancel_right`：∀ {m : Type u_1} {n : Type u_2} {α : Type
 u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring α]   (A : M
atrix m n α) (B : M…
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.Invertible.0.Matrix.add_mul_mul_in
vOf_mul_eq_one._abel_1_3`：∀ {m : Type u_3} {n : Type u_1} {α : Type u_2} [inst :
 Fintype n] [inst_1 : DecidableEq n] [inst_2 : Fintype m]   [inst_3 : Ring α] (A
 : Mat…
-/
lemma add_mul_mul_invOf_mul_eq_one :
    (A + U*C*V)*(⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A) = 1 := by
  calc
    (A + U*C*V)*(⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)
    _ = A*⅟A - A*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A + U*C*V*⅟A - U*C*V*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A := by
      simp_rw [add_sub_assoc, add_mul, mul_sub, Matrix.mul_assoc]
    _ = (1 + U*C*V*⅟A) - (U*⅟(⅟C + V*⅟A*U)*V*⅟A + U*C*V*⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A) := by
      rw [mul_invOf_self, Matrix.one_mul]
      abel
    _ = 1 + U*C*V*⅟A - (U + U*C*V*⅟A*U)*⅟(⅟C + V*⅟A*U)*V*⅟A := by
      rw [sub_right_inj, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul]
    _ = 1 + U*C*V*⅟A - U*C*(⅟C + V*⅟A*U)*⅟(⅟C + V*⅟A*U)*V*⅟A := by
      congr
      simp only [Matrix.mul_add, Matrix.mul_invOf_cancel_right, ← Matrix.mul_assoc]
    _ = 1 := by
      rw [Matrix.mul_invOf_cancel_right]
      abel

-- No spaces around multiplication signs for better clarity
set_option linter.style.whitespace false in
/-- Like `add_mul_mul_invOf_mul_eq_one`, but with multiplication reversed. -/
/-
**Matrix.add_mul_mul_invOf_mul_eq_one'** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：add_mul_mul_invOf_mul_eq_one' : (⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)*(A + U*C*V
) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1
· 使用定理 `Matrix.invOf_mul_cancel_right`：∀ {m : Type u_1} {n : Type u_2} {α : Type
 u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring α]   (A : M
atrix m n α) (B : M…
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.Invertible.0.Matrix.add_mul_mul_in
vOf_mul_eq_one'._abel_1_1`：∀ {m : Type u_3} {n : Type u_1} {α : Type u_2} [inst 
: Fintype n] [inst_1 : DecidableEq n] [inst_2 : Fintype m]   [inst_3 : Decidable
Eq m] […
· 使用定理 `sub_right_inj`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a - b =
 a - c ↔ b = c
· 使用定理 `Matrix.mul_add`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (L : Matrix m n 
α) (…
· 使用定理 `Matrix.add_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (L M : Matrix l 
m α)…
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.Invertible.0.Matrix.add_mul_mul_in
vOf_mul_eq_one'._abel_1_3`：∀ {m : Type u_3} {n : Type u_1} {α : Type u_2} [inst 
: Fintype n] [inst_1 : DecidableEq n] [inst_2 : Fintype m]   [inst_3 : Ring α] (
A : Mat…

--- 原说明 ---
Like `add_mul_mul_invOf_mul_eq_one`, but with multiplication reversed.
-/
lemma add_mul_mul_invOf_mul_eq_one' :
    (⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)*(A + U*C*V) = 1 := by
  calc
    (⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)*(A + U*C*V)
    _ = ⅟A*A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*A + ⅟A*U*C*V - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*U*C*V := by
      simp_rw [add_sub_assoc, _root_.mul_add, _root_.sub_mul, Matrix.mul_assoc]
    _ = (1 + ⅟A*U*C*V) - (⅟A*U*⅟(⅟C + V*⅟A*U)*V + ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A*U*C*V) := by
      rw [invOf_mul_self, Matrix.invOf_mul_cancel_right]
      abel
    _ = 1 + ⅟A*U*C*V - ⅟A*U*⅟(⅟C + V*⅟A*U)*(V + V*⅟A*U*C*V) := by
      rw [sub_right_inj, Matrix.mul_add]
      simp_rw [Matrix.mul_assoc]
    _ = 1 + ⅟A*U*C*V - ⅟A*U*⅟(⅟C + V*⅟A*U)*(⅟C + V*⅟A*U)*C*V := by
      simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc,
        Matrix.invOf_mul_cancel_right]
    _ = 1 := by
      rw [Matrix.invOf_mul_cancel_right]
      abel

/-- If matrices `A`, `C`, and `C⁻¹ + V * A⁻¹ * U` are invertible, then so is `A + U * C * V`. -/
@[implicit_reducible]
/-
**Matrix.invertibleAddMulMul** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：invertibleAddMulMul : Invertible (A + U * C * V) where invOf
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.add_mul_mul_invOf_mul_eq_one'`：add_mul_mul_invOf_mul_eq_one' : (⅟
A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A)*(A + U*C*V) = 1
· 使用引理 `Matrix.add_mul_mul_invOf_mul_eq_one`：add_mul_mul_invOf_mul_eq_one : (A +
 U*C*V)*(⅟A - ⅟A*U*⅟(⅟C + V*⅟A*U)*V*⅟A) = 1

--- 原说明 ---
If matrices `A`, `C`, and `C⁻¹ + V * A⁻¹ * U` are invertible, then so is `A + U 
* C * V`.
-/
def invertibleAddMulMul : Invertible (A + U * C * V) where
  invOf := ⅟A - ⅟A * U * ⅟(⅟C + V * ⅟A * U) * V * ⅟A
  invOf_mul_self := add_mul_mul_invOf_mul_eq_one' _ _ _ _
  mul_invOf_self := add_mul_mul_invOf_mul_eq_one _ _ _ _

/-- The **Woodbury Identity** (`⅟` version).

See `Matrix.invOf_add_mul_mul'` for the Binomial Inverse Theorem. -/
/-
**Matrix.invOf_add_mul_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：invOf_add_mul_mul [Invertible (A + U * C * V)] : ⅟(A + U * C * V) = ⅟A - ⅟
A * U * ⅟(⅟C + V * ⅟A * U) * V * ⅟A
参数：A + U * C * V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Invertible.congr`：Invertible.congr [Invertible a] [Invertible b] (h : a 
= b) : ⅟a = ⅟b

--- 原说明 ---
The **Woodbury Identity** (`⅟` version).

See `Matrix.invOf_add_mul_mul'` for the Binomial Inverse Theorem.
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

/-
**Matrix.add_mul_mul_mul_invOf_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：add_mul_mul_mul_invOf_eq_one : (A + U * C * V) * (⅟A - ⅟A * U * C * ⅟(C + 
C * V * ⅟A * U * C) * C * V * ⅟A) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.mul_sub`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocRing α] [inst_1 : Fintype n]   (M : Matrix m n α) (
N N'…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.add_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (L M : Matrix l 
m α)…
· 使用定理 `mul_invOf_self'`：mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : a * ⅟a = 1
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `Matrix.instIsLeftCancelAdd`：∀ {m : Type u_2} {n : Type u_3} {α : Type v}
 [inst : Add α] [IsLeftCancelAdd α], IsLeftCancelAdd (Matrix m n α)
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_right_eq_iff_eq_mul_invOf`：∀ {m : Type u_1} {n : Type u_2} {α
 : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring α]  
 {A B : Matrix m n α} {C :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.mul_add`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (L : Matrix m n 
α) (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_mul_mul_mul_invOf_eq_one :
    (A + U * C * V) * (⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A) = 1 := by
  simp only [Matrix.mul_sub, Matrix.add_mul, mul_invOf_self']
  rw [add_sub_assoc, add_eq_left, sub_eq_zero]
  simp only [← Matrix.mul_assoc, mul_invOf_self', Matrix.one_mul]
  simp only [← Matrix.add_mul]
  congr
  rw [← Matrix.mul_right_eq_iff_eq_mul_invOf]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
/-
**Matrix.add_mul_mul_mul_invOf_eq_one'** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：add_mul_mul_mul_invOf_eq_one' : (⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * 
C) * C * V * ⅟A) * (A + U * C * V) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.mul_add`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (L : Matrix m n 
α) (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.sub_mul`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocRing α] [inst_1 : Fintype n]   (M M' : Matrix m n α
) (N…
· 使用定理 `invOf_mul_self'`：invOf_mul_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : ⅟a * a = 1
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `sub_eq_self`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = a ↔
 b = 0
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.invOf_mul_eq_iff_eq_mul_left`：∀ {m : Type u_1} {n : Type u_2} {α 
: Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring α]   
{A B : Matrix n m α} {C :…
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.add_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (L M : Matrix l 
m α)…
· 使用定理 `Matrix.instIsLeftCancelAdd`：∀ {m : Type u_2} {n : Type u_3} {α : Type v}
 [inst : Add α] [IsLeftCancelAdd α], IsLeftCancelAdd (Matrix m n α)
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_mul_mul_mul_invOf_eq_one' :
    (⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A) * (A + U * C * V) = 1 := by
  simp only [Matrix.mul_add, Matrix.sub_mul, invOf_mul_self']
  rw [sub_add, sub_eq_self, sub_eq_zero]
  simp only [Matrix.mul_assoc, ← Matrix.mul_sub]
  congr
  rw [eq_sub_iff_add_eq, ← Matrix.mul_add]
  rw [Matrix.invOf_mul_eq_iff_eq_mul_left]
  simp only [Matrix.add_mul, invOf_mul_self', Matrix.mul_one, add_right_inj]
  simp only [Matrix.mul_assoc]

/-- If matrices `A` and `C + C * V * A⁻¹ * U * C` are invertible, then so is `A + U * C * V`. -/
@[implicit_reducible]
/-
**Matrix.invertibleAddMulMul'** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：invertibleAddMulMul' : Invertible (A + U * C * V) where invOf
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.add_mul_mul_mul_invOf_eq_one'`：add_mul_mul_mul_invOf_eq_one' : (⅟
A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A) * (A + U * C * V) = 1
· 使用引理 `Matrix.add_mul_mul_mul_invOf_eq_one`：add_mul_mul_mul_invOf_eq_one : (A +
 U * C * V) * (⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A) = 1

--- 原说明 ---
If matrices `A` and `C + C * V * A⁻¹ * U * C` are invertible, then so is `A + U 
* C * V`.
-/
def invertibleAddMulMul' : Invertible (A + U * C * V) where
  invOf := ⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A
  invOf_mul_self := add_mul_mul_mul_invOf_eq_one' A U C V
  mul_invOf_self := add_mul_mul_mul_invOf_eq_one A U C V

/-- The **Binomial Inverse Theorem** (`⅟` version).

See `Matrix.invOf_add_mul_mul` for the Woodbury identity. -/
/-
**Matrix.invOf_add_mul_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：invOf_add_mul_mul' [Invertible (A + U * C * V)] : ⅟(A + U * C * V) = ⅟A - 
⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A
参数：A + U * C * V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Invertible.congr`：Invertible.congr [Invertible a] [Invertible b] (h : a 
= b) : ⅟a = ⅟b

--- 原说明 ---
The **Binomial Inverse Theorem** (`⅟` version).

See `Matrix.invOf_add_mul_mul` for the Woodbury identity.
-/
theorem invOf_add_mul_mul' [Invertible (A + U * C * V)] :
    ⅟(A + U * C * V) = ⅟A - ⅟A * U * C * ⅟(C + C * V * ⅟A * U * C) * C * V * ⅟A := by
  let := invertibleAddMulMul' A U C V
  convert! (rfl : ⅟(A + U * C * V) = _)

end BinomialInverseTheorem

end Ring

end Matrix

