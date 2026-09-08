/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Bilinear form

This file defines the conversion between bilinear forms and matrices.

## Main definitions

* `Matrix.toBilin` given a basis define a bilinear form
* `Matrix.toBilin'` define the bilinear form on `n → R`
* `BilinForm.toMatrix`: calculate the matrix coefficients of a bilinear form
* `BilinForm.toMatrix'`: calculate the matrix coefficients of a bilinear form on `n → R`

## Notation

In this file we use the following type variables:
- `M₁` is a module over the commutative semiring `R₁`,
- `M₂` is a module over the commutative ring `R₂`.

## Tags

bilinear form, bilin form, BilinearForm, matrix, basis

-/

@[expose] public section

open LinearMap (BilinForm)
open Module

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]
variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

section Matrix

variable {n o : Type*}

open Finset LinearMap Matrix

open Matrix

/-- The map from `Matrix n n R` to bilinear forms on `n → R`.

This is an auxiliary definition for the equivalence `Matrix.toBilin'`. -/
/-
**Matrix.toBilin'Aux** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{R₁ : Type u_1} →   [inst : CommSemiring R₁] → {n : Type u_5} → [Fintype n
] → Matrix n n R₁ → LinearMap.BilinForm R₁ (n → R₁)
参数：n → R₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from `Matrix n n R` to bilinear forms on `n → R`.

This is an auxiliary definition for the equivalence `Matrix.toBilin'`.
-/
def Matrix.toBilin'Aux [Fintype n] (M : Matrix n n R₁) : BilinForm R₁ (n → R₁) :=
  Matrix.toLinearMap₂'Aux _ _ M
/-
**Matrix.toBilin'Aux_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n]   (M : Matrix n n R₁) (i j : n), (M.toBilin'Aux (P
i.single i 1)) (Pi.single j 1) = M i j
参数：M : Matrix n n R₁；i j : n；M.toBilin'Aux (Pi.single i 1)；Pi.single j 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.toLinearMap₂'Aux_single`：∀ {R₁ : Type u_2} {S₁ : Type u_3} {R₂ : 
Type u_4} {S₂ : Type u_5} {N₂ : Type u_10} {n : Type u_11} {m : Type u_12}   [in
st : Semiring R₁] [i…
-/
theorem Matrix.toBilin'Aux_single [Fintype n] [DecidableEq n] (M : Matrix n n R₁) (i j : n) :
    M.toBilin'Aux (Pi.single i 1) (Pi.single j 1) = M i j :=
  Matrix.toLinearMap₂'Aux_single _ _ _ _ _

/-- The linear map from bilinear forms to `Matrix n n R` given an `n`-indexed basis.

This is an auxiliary definition for the equivalence `Matrix.toBilin'`. -/
/-
**LinearMap.BilinForm.toMatrixAux** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.toMatrixAux (b : n -> M₁) : BilinForm R₁ M₁ ->ₗ[R₁] Ma
trix n n R₁
参数：b : n -> M₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map from bilinear forms to `Matrix n n R` given an `n`-indexed basis.

This is an auxiliary definition for the equivalence `Matrix.toBilin'`.
-/
def LinearMap.BilinForm.toMatrixAux (b : n → M₁) : BilinForm R₁ M₁ →ₗ[R₁] Matrix n n R₁ :=
  LinearMap.toMatrix₂Aux R₁ b b

@[deprecated (since := "2026-01-16")] alias BilinForm.toMatrixAux := LinearMap.BilinForm.toMatrixAux

@[simp]
/-
**LinearMap.BilinForm.toMatrixAux_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.toMatrixAux_apply (B : BilinForm R₁ M₁) (b : n -> M₁) 
(i j : n) : BilinForm.toMatrixAux b B i j = B (b i) (b j)
参数：B : BilinForm R₁ M₁；b : n -> M₁；i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix₂Aux_apply`：LinearMap.toMatrix₂Aux_apply (f : M₁ ->ₛₗ[
σ₁] M₂ ->ₛₗ[σ₂] N₂) (b₁ : n -> M₁) (b₂ : m -> M₂) (i : n) (j : m) : LinearMap.to
Matrix₂Aux R b₁ b₂…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem LinearMap.BilinForm.toMatrixAux_apply (B : BilinForm R₁ M₁) (b : n → M₁) (i j : n) :
    BilinForm.toMatrixAux b B i j = B (b i) (b j) :=
  LinearMap.toMatrix₂Aux_apply R₁ B _ _ _ _

variable [Fintype n] [Fintype o]
/-
**LinearMap.toBilin'Aux_toMatrixAux** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n]   (B₂ : LinearMap.BilinForm R₁ (n → R₁)), ((Linear
Map.BilinForm.toMatrixAux fun j => Pi.single j 1) B₂).toBilin'Aux = B₂
参数：B₂ : LinearMap.BilinForm R₁ (n → R₁)；(LinearMap.BilinForm.toMatrixAux fun j =
> Pi.single j 1) B₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.toMatrixAux.eq_1`：∀ {R₁ : Type u_1} {M₁ : Type u_2} 
[inst : CommSemiring R₁] [inst_1 : AddCommMonoid M₁] [inst_2 : _root_.Module R₁ 
M₁]   {n : Type u_5} (b : …
· 使用定理 `Matrix.toBilin'Aux.eq_1`：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n :
 Type u_5} [inst_1 : Fintype n] (M : Matrix n n R₁),   M.toBilin'Aux = Matrix.to
LinearMap₂'Au…
· 使用定理 `LinearMap.toLinearMap₂'Aux_toMatrix₂Aux`：∀ (R : Type u_1) {R₁ : Type u_2
} {S₁ : Type u_3} {R₂ : Type u_4} {S₂ : Type u_5} {N₂ : Type u_10} {n : Type u_1
1}   {m : Type u_12} [inst : …
-/
theorem LinearMap.toBilin'Aux_toMatrixAux [DecidableEq n] (B₂ : BilinForm R₁ (n → R₁)) :
    Matrix.toBilin'Aux (BilinForm.toMatrixAux (fun j => Pi.single j 1) B₂) = B₂ := by
  rw [BilinForm.toMatrixAux, Matrix.toBilin'Aux, toLinearMap₂'Aux_toMatrix₂Aux]

@[deprecated (since := "2026-01-16")] alias toBilin'Aux_toMatrixAux :=
  LinearMap.toBilin'Aux_toMatrixAux

section ToMatrix'

/-! ### `ToMatrix'` section

This section deals with the conversion between matrices and bilinear forms on `n → R₂`.
-/


variable [DecidableEq n] [DecidableEq o]

/-- The linear equivalence between bilinear forms on `n → R` and `n × n` matrices -/
/-
**LinearMap.BilinForm.toMatrix'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.toMatrix' : BilinForm R₁ (n -> R₁) ≃ₗ[R₁] Matrix n n R
₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence between bilinear forms on `n → R` and `n × n` matrices
-/
def LinearMap.BilinForm.toMatrix' : BilinForm R₁ (n → R₁) ≃ₗ[R₁] Matrix n n R₁ :=
  LinearMap.toMatrix₂' R₁

/-- The linear equivalence between `n × n` matrices and bilinear forms on `n → R` -/
/-
**Matrix.toBilin'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matrix.toBilin'Aux [Fintype n] (M : Matrix n n R₁) : BilinForm R₁ (n -> R₁
)
参数：M : Matrix n n R₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence between `n × n` matrices and bilinear forms on `n → R`
-/
def Matrix.toBilin' : Matrix n n R₁ ≃ₗ[R₁] BilinForm R₁ (n → R₁) :=
  BilinForm.toMatrix'.symm

@[simp]
/-
**Matrix.toBilin'Aux_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n]   (M : Matrix n n R₁), M.toBilin'Aux = Matrix.toBi
lin' M
参数：M : Matrix n n R₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Matrix.toBilin'Aux_eq (M : Matrix n n R₁) : Matrix.toBilin'Aux M = Matrix.toBilin' M :=
  rfl
/-
**Matrix.toBilin'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n]   (M : Matrix n n R₁) (x y : n → R₁), ((Matrix.toB
ilin' M) x) y = ∑ i, ∑ j, x i * M i j * y j
参数：M : Matrix n n R₁；x y : n → R₁；(Matrix.toBilin' M) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Matrix.toLinearMap₂'_apply`：∀ {R : Type u_1} {S₁ : Type u_3} {S₂ : Type 
u_5} {N₂ : Type u_10} {n : Type u_11} {m : Type u_12}   [inst : CommSemiring R] 
[inst_1 : AddCom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Matrix.toBilin'_apply (M : Matrix n n R₁) (x y : n → R₁) :
    Matrix.toBilin' M x y = ∑ i, ∑ j, x i * M i j * y j :=
  (Matrix.toLinearMap₂'_apply _ _ _).trans
    (by simp only [smul_eq_mul, mul_comm, mul_left_comm])
/-
**Matrix.toBilin'_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n]   (M : Matrix n n R₁) (v w : n → R₁), ((Matrix.toB
ilin' M) v) w = v ⬝ᵥ M.mulVec w
参数：M : Matrix n n R₁；v w : n → R₁；(Matrix.toBilin' M) v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.toLinearMap₂'_apply'`：∀ {n : Type u_11} {m : Type u_12} [inst : F
intype n] [inst_1 : Fintype m] [inst_2 : DecidableEq n]   [inst_3 : DecidableEq 
m] {T : Type u_16…
-/
theorem Matrix.toBilin'_apply' (M : Matrix n n R₁) (v w : n → R₁) :
    Matrix.toBilin' M v w = v ⬝ᵥ M *ᵥ w := Matrix.toLinearMap₂'_apply' _ _ _

@[simp]
/-
**Matrix.toBilin'_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n]   (M : Matrix n n R₁) (i j : n), ((Matrix.toBilin'
 M) (Pi.single i 1)) (Pi.single j 1) = M i j
参数：M : Matrix n n R₁；i j : n；(Matrix.toBilin' M) (Pi.single i 1)；Pi.single j 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toBilin'_apply`：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : T
ype u_5} [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix n n R₁) (x 
y : n → R₁)…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Matrix.toBilin'_single (M : Matrix n n R₁) (i j : n) :
    Matrix.toBilin' M (Pi.single i 1) (Pi.single j 1) = M i j := by
  simp [Matrix.toBilin'_apply, Pi.single_apply]

@[simp]
/-
**LinearMap.BilinForm.toMatrix'_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinF
orm`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n],   LinearMap.BilinForm.toMatrix'.symm = Matrix.toB
ilin'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem LinearMap.BilinForm.toMatrix'_symm :
    (BilinForm.toMatrix'.symm : Matrix n n R₁ ≃ₗ[R₁] _) = Matrix.toBilin' :=
  rfl

@[simp]
/-
**Matrix.toBilin'_symm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n],   Matrix.toBilin'.symm = LinearMap.BilinForm.toMa
trix'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.symm_symm`：symm_symm (e : M ≃ₛₗ[σ] M₂) : e.symm.symm = e
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem Matrix.toBilin'_symm :
    (Matrix.toBilin'.symm : _ ≃ₗ[R₁] Matrix n n R₁) = BilinForm.toMatrix' :=
  BilinForm.toMatrix'.symm_symm

@[simp]
/-
**Matrix.toBilin'_toMatrix'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n]   (B : LinearMap.BilinForm R₁ (n → R₁)), Matrix.to
Bilin' (LinearMap.BilinForm.toMatrix' B) = B
参数：B : LinearMap.BilinForm R₁ (n → R₁)；LinearMap.BilinForm.toMatrix' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem Matrix.toBilin'_toMatrix' (B : BilinForm R₁ (n → R₁)) :
    Matrix.toBilin' (BilinForm.toMatrix' B) = B :=
  Matrix.toBilin'.apply_symm_apply B

namespace LinearMap

@[simp]
/-
**LinearMap.BilinForm.toMatrix'_toBilin'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bi
linForm`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n]   (M : Matrix n n R₁), LinearMap.BilinForm.toMatri
x' (Matrix.toBilin' M) = M
参数：M : Matrix n n R₁；Matrix.toBilin' M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem BilinForm.toMatrix'_toBilin' (M : Matrix n n R₁) :
    BilinForm.toMatrix' (Matrix.toBilin' M) = M :=
  (LinearMap.toMatrix₂' R₁).apply_symm_apply M

@[simp]
/-
**LinearMap.BilinForm.toMatrix'_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bilin
Form`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n]   (B : LinearMap.BilinForm R₁ (n → R₁)) (i j : n),
   LinearMap.BilinForm.toMatrix' B i j = (B (Pi.single i 1)) (Pi.single j 1)
参数：B : LinearMap.BilinForm R₁ (n → R₁)；i j : n；B (Pi.single i 1)；Pi.single j 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix₂'_apply`：∀ {R : Type u_1} {S₁ : Type u_3} {S₂ : Type 
u_5} {N₂ : Type u_10} {n : Type u_11} {m : Type u_12}   [inst : CommSemiring R] 
[inst_1 : AddCom…
-/
theorem BilinForm.toMatrix'_apply (B : BilinForm R₁ (n → R₁)) (i j : n) :
    BilinForm.toMatrix' B i j = B (Pi.single i 1) (Pi.single j 1) :=
  LinearMap.toMatrix₂'_apply _ _ _

@[simp]
/-
**LinearMap.BilinForm.toMatrix'_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinF
orm`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} {o : Type u_6} [
inst_1 : Fintype n] [inst_2 : Fintype o]   [inst_3 : DecidableEq n] [inst_4 : De
cidableEq o] (B : LinearMap.BilinForm R₁ (n → R₁))   (l r : (o → R₁) →ₗ[R₁] n → 
R₁),   LinearMap.BilinForm.toMatrix' (B.comp l r) =     (LinearMap.toMatrix' l).
transpose * LinearMap.BilinForm.toMatrix' B * LinearMap.toMatrix' r
参数：B : LinearMap.BilinForm R₁ (n → R₁)；l r : (o → R₁) →ₗ[R₁] n → R₁；B.comp l r；L
inearMap.toMatrix' l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix₂'_compl₁₂`：∀ {n : Type u_11} {m : Type u_12} {n' : Ty
pe u_13} {m' : Type u_14} {R : Type u_16} [inst : CommSemiring R]   [inst_1 : Fi
ntype n] [inst_2 :…
-/
theorem BilinForm.toMatrix'_comp (B : BilinForm R₁ (n → R₁)) (l r : (o → R₁) →ₗ[R₁] n → R₁) :
    (B.comp l r).toMatrix' = l.toMatrix'ᵀ * B.toMatrix' * r.toMatrix' :=
  B.toMatrix₂'_compl₁₂ _ _
/-
**LinearMap.BilinForm.toMatrix'_compLeft** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bi
linForm`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n]   (B : LinearMap.BilinForm R₁ (n → R₁)) (f : (n → 
R₁) →ₗ[R₁] n → R₁),   LinearMap.BilinForm.toMatrix' (B.compLeft f) = (LinearMap.
toMatrix' f).transpose * LinearMap.BilinForm.toMatrix' B
参数：B : LinearMap.BilinForm R₁ (n → R₁)；f : (n → R₁) →ₗ[R₁] n → R₁；B.compLeft f；L
inearMap.toMatrix' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix₂'_comp`：∀ {n : Type u_11} {m : Type u_12} {n' : Type 
u_13} {R : Type u_16} [inst : CommSemiring R] [inst_1 : Fintype n]   [inst_2 : F
intype m] [inst…
-/
theorem BilinForm.toMatrix'_compLeft (B : BilinForm R₁ (n → R₁)) (f : (n → R₁) →ₗ[R₁] n → R₁) :
    (B.compLeft f).toMatrix' = f.toMatrix'ᵀ * B.toMatrix' :=
  B.toMatrix₂'_comp _
/-
**LinearMap.BilinForm.toMatrix'_compRight** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.B
ilinForm`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n]   (B : LinearMap.BilinForm R₁ (n → R₁)) (f : (n → 
R₁) →ₗ[R₁] n → R₁),   LinearMap.BilinForm.toMatrix' (B.compRight f) = LinearMap.
BilinForm.toMatrix' B * LinearMap.toMatrix' f
参数：B : LinearMap.BilinForm R₁ (n → R₁)；f : (n → R₁) →ₗ[R₁] n → R₁；B.compRight f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix₂'_compl₂`：∀ {n : Type u_11} {m : Type u_12} {m' : Typ
e u_14} {R : Type u_16} [inst : CommSemiring R] [inst_1 : Fintype n]   [inst_2 :
 Fintype m] [inst…
-/
theorem BilinForm.toMatrix'_compRight (B : BilinForm R₁ (n → R₁)) (f : (n → R₁) →ₗ[R₁] n → R₁) :
    (B.compRight f).toMatrix' = B.toMatrix' * f.toMatrix' :=
  B.toMatrix₂'_compl₂ _
/-
**LinearMap.BilinForm.mul_toMatrix'_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bil
inForm`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} {o : Type u_6} [
inst_1 : Fintype n] [inst_2 : Fintype o]   [inst_3 : DecidableEq n] [inst_4 : De
cidableEq o] (B : LinearMap.BilinForm R₁ (n → R₁)) (M : Matrix o n R₁)   (N : Ma
trix n o R₁),   M * LinearMap.BilinForm.toMatrix' B * N =     LinearMap.BilinFor
m.toMatrix' (B.comp (Matrix.toLin' M.transpose) (Matrix.toLin' N))
参数：B : LinearMap.BilinForm R₁ (n → R₁)；M : Matrix o n R₁；N : Matrix n o R₁；B.com
p (Matrix.toLin' M.transpose) (Matrix.toLin' N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mul_toMatrix₂'_mul`：∀ {n : Type u_11} {m : Type u_12} {n' : Ty
pe u_13} {m' : Type u_14} {R : Type u_16} [inst : CommSemiring R]   [inst_1 : Fi
ntype n] [inst_2 :…
-/
theorem BilinForm.mul_toMatrix'_mul (B : BilinForm R₁ (n → R₁)) (M : Matrix o n R₁)
    (N : Matrix n o R₁) : M * B.toMatrix' * N = (B.comp (Mᵀ).toLin' N.toLin').toMatrix' :=
  B.mul_toMatrix₂'_mul _ _
/-
**LinearMap.BilinForm.mul_toMatrix'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFo
rm`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n]   (B : LinearMap.BilinForm R₁ (n → R₁)) (M : Matri
x n n R₁),   M * LinearMap.BilinForm.toMatrix' B = LinearMap.BilinForm.toMatrix'
 (B.compLeft (Matrix.toLin' M.transpose))
参数：B : LinearMap.BilinForm R₁ (n → R₁)；M : Matrix n n R₁；B.compLeft (Matrix.toLi
n' M.transpose)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mul_toMatrix'`：LinearMap.mul_toMatrix' (B : (n -> R) ->ₗ[R] (m
 -> R) ->ₗ[R] R) (M : Matrix n' n R) : M * toMatrix₂' R B = toMatrix₂' R (B.comp
 <| toLin' Mᵀ…
-/
theorem BilinForm.mul_toMatrix' (B : BilinForm R₁ (n → R₁)) (M : Matrix n n R₁) :
    M * B.toMatrix' = (B.compLeft (Mᵀ).toLin').toMatrix' :=
  LinearMap.mul_toMatrix' B _
/-
**LinearMap.BilinForm.toMatrix'_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFo
rm`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n]   (B : LinearMap.BilinForm R₁ (n → R₁)) (M : Matri
x n n R₁),   LinearMap.BilinForm.toMatrix' B * M = LinearMap.BilinForm.toMatrix'
 (B.compRight (Matrix.toLin' M))
参数：B : LinearMap.BilinForm R₁ (n → R₁)；M : Matrix n n R₁；B.compRight (Matrix.toL
in' M)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix₂'_mul`：∀ {n : Type u_11} {m : Type u_12} {m' : Type u
_14} {R : Type u_16} [inst : CommSemiring R] [inst_1 : Fintype n]   [inst_2 : Fi
ntype m] [inst…
-/
theorem BilinForm.toMatrix'_mul (B : BilinForm R₁ (n → R₁)) (M : Matrix n n R₁) :
    BilinForm.toMatrix' B * M = BilinForm.toMatrix' (B.compRight (Matrix.toLin' M)) :=
  B.toMatrix₂'_mul _

end LinearMap

/-
**Matrix.toBilin'_comp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} {o : Type u_6} [
inst_1 : Fintype n] [inst_2 : Fintype o]   [inst_3 : DecidableEq n] [inst_4 : De
cidableEq o] (M : Matrix n n R₁) (P Q : Matrix n o R₁),   (Matrix.toBilin' M).co
mp (Matrix.toLin' P) (Matrix.toLin' Q) = Matrix.toBilin' (P.transpose * M * Q)
参数：M : Matrix n n R₁；P Q : Matrix n o R₁；Matrix.toBilin' M；Matrix.toLin' P；Matri
x.toLin' Q；P.transpose * M * Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `LinearMap.BilinForm.toMatrix'_comp`：∀ {R₁ : Type u_1} [inst : CommSemiri
ng R₁] {n : Type u_5} {o : Type u_6} [inst_1 : Fintype n] [inst_2 : Fintype o]  
 [inst_3 : DecidableEq n…
· 使用定理 `LinearMap.toMatrix'_toLin'`：∀ {R : Type u_1} [inst : CommSemiring R] {m 
: Type u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : 
Matrix m n R), L…
· 使用定理 `LinearMap.BilinForm.toMatrix'_toBilin'`：∀ {R₁ : Type u_1} [inst : CommSe
miring R₁] {n : Type u_5} [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : M
atrix n n R₁), LinearMap.Bil…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Matrix.toBilin'_comp (M : Matrix n n R₁) (P Q : Matrix n o R₁) :
    M.toBilin'.comp P.toLin' Q.toLin' = (Pᵀ * M * Q).toBilin' :=
  BilinForm.toMatrix'.injective
    (by simp only [BilinForm.toMatrix'_comp, BilinForm.toMatrix'_toBilin', toMatrix'_toLin'])

end ToMatrix'

section ToMatrix

/-! ### `ToMatrix` section

This section deals with the conversion between matrices and bilinear forms on
a module with a fixed basis.
-/


variable [DecidableEq n] (b : Basis n R₁ M₁)

/-- `BilinForm.toMatrix b` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`. -/
/-
**LinearMap.BilinForm.toMatrix** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.toMatrix : BilinForm R₁ M₁ ≃ₗ[R₁] Matrix n n R₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BilinForm.toMatrix b` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`.
-/
noncomputable def LinearMap.BilinForm.toMatrix : BilinForm R₁ M₁ ≃ₗ[R₁] Matrix n n R₁ :=
  LinearMap.toMatrix₂ b b

@[deprecated (since := "2026-01-16")] alias BilinForm.toMatrix := LinearMap.BilinForm.toMatrix

/-- `BilinForm.toMatrix b` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`. -/
/-
**Matrix.toBilin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matrix.toBilin : Matrix n n R₁ ≃ₗ[R₁] BilinForm R₁ M₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BilinForm.toMatrix b` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`.
-/
noncomputable def Matrix.toBilin : Matrix n n R₁ ≃ₗ[R₁] BilinForm R₁ M₁ :=
  (LinearMap.BilinForm.toMatrix b).symm

@[simp]
/-
**LinearMap.BilinForm.toMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.toMatrix_apply (B : BilinForm R₁ M₁) (i j : n) : Bilin
Form.toMatrix b B i j = B (b i) (b j)
参数：B : BilinForm R₁ M₁；i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix₂_apply`：LinearMap.toMatrix₂_apply (B : M₁ ->ₛₗ[σ₁] M₂
 ->ₛₗ[σ₂] N₂) (i : n) (j : m) : LinearMap.toMatrix₂ b₁ b₂ B i j = B (b₁ i) (b₂ j
)
-/
theorem LinearMap.BilinForm.toMatrix_apply (B : BilinForm R₁ M₁) (i j : n) :
    BilinForm.toMatrix b B i j = B (b i) (b j) :=
  LinearMap.toMatrix₂_apply _ _ B _ _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_apply := LinearMap.BilinForm.toMatrix_apply
/-
**LinearMap.BilinForm.dotProduct_toMatrix_mulVec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.dotProduct_toMatrix_mulVec (B : BilinForm R₁ M₁) (x y 
: n -> R₁) : x ⬝ᵥ (BilinForm.toMatrix b B) *ᵥ y = B (b.equivFun.symm x) (b.equiv
Fun.symm y)
参数：B : BilinForm R₁ M₁；x y : n -> R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dotProduct_toMatrix₂_mulVec`：dotProduct_toMatrix₂_mulVec (B : M₁ ->ₛₗ[σ₁
] M₂ ->ₛₗ[σ₂] R) (x : n -> R) (y : m -> R) : (σ₁ ∘ x) ⬝ᵥ (toMatrix₂ b₁ b₂ B) *ᵥ 
(σ₂ ∘ y) = B (b₁.…
-/
theorem LinearMap.BilinForm.dotProduct_toMatrix_mulVec (B : BilinForm R₁ M₁) (x y : n → R₁) :
    x ⬝ᵥ (BilinForm.toMatrix b B) *ᵥ y = B (b.equivFun.symm x) (b.equivFun.symm y) :=
  dotProduct_toMatrix₂_mulVec b b B x y

@[deprecated (since := "2026-01-16")]
alias BilinForm.dotProduct_toMatrix_mulVec := LinearMap.BilinForm.dotProduct_toMatrix_mulVec
/-
**LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec (B : BilinForm R₁ 
M₁) (x y : M₁) : B x y = (b.repr x) ⬝ᵥ (BilinForm.toMatrix b B) *ᵥ (b.repr y)
参数：B : BilinForm R₁ M₁；x y : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `apply_eq_dotProduct_toMatrix₂_mulVec`：apply_eq_dotProduct_toMatrix₂_mulV
ec (B : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] R) (x : M₁) (y : M₂) : B x y = (σ₁ ∘ b₁.repr x) 
⬝ᵥ (toMatrix₂ b₁ b₂ B) *ᵥ …
-/
lemma LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec (B : BilinForm R₁ M₁) (x y : M₁) :
    B x y = (b.repr x) ⬝ᵥ (BilinForm.toMatrix b B) *ᵥ (b.repr y) :=
  apply_eq_dotProduct_toMatrix₂_mulVec b b B x y

@[deprecated (since := "2026-01-16")]
alias BilinForm.apply_eq_dotProduct_toMatrix_mulVec :=
  LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec

@[simp]
/-
**Matrix.toBilin_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toBilin_apply (M : Matrix n n R₁) (x y : M₁) : Matrix.toBilin b M x
 y = ∑ i, ∑ j, b.repr x i * M i j * b.repr y j
参数：M : Matrix n n R₁；x y : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Matrix.toLinearMap₂_apply`：Matrix.toLinearMap₂_apply (M : Matrix n m N₂)
 (x : M₁) (y : M₂) : Matrix.toLinearMap₂ b₁ b₂ M x y = ∑ i, ∑ j, b₁.repr x i • b
₂.repr y j • M …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Matrix.toBilin_apply (M : Matrix n n R₁) (x y : M₁) :
    Matrix.toBilin b M x y = ∑ i, ∑ j, b.repr x i * M i j * b.repr y j :=
  (Matrix.toLinearMap₂_apply _ _ _ _ _).trans
    (by simp only [smul_eq_mul, mul_comm, mul_left_comm])

-- Not a `simp` lemma since `BilinForm.toMatrix` needs an extra argument
/-
**LinearMap.BilinForm.toMatrixAux_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.toMatrixAux_eq (B : BilinForm R₁ M₁) : BilinForm.toMat
rixAux (R₁
参数：B : BilinForm R₁ M₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix₂Aux_eq`：LinearMap.toMatrix₂Aux_eq (B : M₁ ->ₛₗ[σ₁] M₂
 ->ₛₗ[σ₂] N₂) : LinearMap.toMatrix₂Aux R b₁ b₂ B = LinearMap.toMatrix₂ b₁ b₂ B
-/
theorem LinearMap.BilinForm.toMatrixAux_eq (B : BilinForm R₁ M₁) :
    BilinForm.toMatrixAux (R₁ := R₁) b B = BilinForm.toMatrix b B :=
  LinearMap.toMatrix₂Aux_eq _ _ B

@[deprecated (since := "2026-01-16")]
alias BilinearForm.toMatrixAux_eq := LinearMap.BilinForm.toMatrixAux_eq

@[simp]
/-
**LinearMap.BilinForm.toMatrix_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.toMatrix_symm : (BilinForm.toMatrix b).symm = Matrix.t
oBilin b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem LinearMap.BilinForm.toMatrix_symm : (BilinForm.toMatrix b).symm = Matrix.toBilin b :=
  rfl

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_symm := LinearMap.BilinForm.toMatrix_symm

@[simp]
/-
**Matrix.toBilin_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toBilin_symm : (Matrix.toBilin b).symm = LinearMap.BilinForm.toMatr
ix b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.symm_symm`：symm_symm (e : M ≃ₛₗ[σ] M₂) : e.symm.symm = e
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem Matrix.toBilin_symm : (Matrix.toBilin b).symm = LinearMap.BilinForm.toMatrix b :=
  (LinearMap.BilinForm.toMatrix b).symm_symm
/-
**Matrix.toBilin_basisFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toBilin_basisFun : Matrix.toBilin (Pi.basisFun R₁ n) = Matrix.toBil
in'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toBilin_apply`：Matrix.toBilin_apply (M : Matrix n n R₁) (x y : M₁
) : Matrix.toBilin b M x y = ∑ i, ∑ j, b.repr x i * M i j * b.repr y j
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.basisFun_repr`：basisFun_repr (x : η -> R) (i : η) : (Pi.basisFun R η)
.repr x i = x i
· 使用定理 `Matrix.toBilin'_apply`：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : T
ype u_5} [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix n n R₁) (x 
y : n → R₁)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Matrix.toBilin_basisFun : Matrix.toBilin (Pi.basisFun R₁ n) = Matrix.toBilin' := by
  ext M
  simp only [coe_comp, coe_single, Function.comp_apply, toBilin_apply, Pi.basisFun_repr,
    toBilin'_apply]
/-
**LinearMap.BilinForm.toMatrix_basisFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.toMatrix_basisFun : BilinForm.toMatrix (Pi.basisFun R₁
 n) = BilinForm.toMatrix'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.toMatrix.eq_1`：∀ {R₁ : Type u_1} {M₁ : Type u_2} [in
st : CommSemiring R₁] [inst_1 : AddCommMonoid M₁] [inst_2 : _root_.Module R₁ M₁]
   {n : Type u_5} [inst…
· 使用定理 `LinearMap.BilinForm.toMatrix'.eq_1`：∀ {R₁ : Type u_1} [inst : CommSemiri
ng R₁] {n : Type u_5} [inst_1 : Fintype n] [inst_2 : DecidableEq n],   LinearMap
.BilinForm.toMatrix' = L…
· 使用定理 `LinearMap.toMatrix₂_basisFun`：LinearMap.toMatrix₂_basisFun : LinearMap.t
oMatrix₂ (Pi.basisFun R n) (Pi.basisFun R m) = LinearMap.toMatrix₂' R (N₂
-/
theorem LinearMap.BilinForm.toMatrix_basisFun :
    BilinForm.toMatrix (Pi.basisFun R₁ n) = BilinForm.toMatrix' := by
  rw [BilinForm.toMatrix, BilinForm.toMatrix', LinearMap.toMatrix₂_basisFun]

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_basisFun := LinearMap.BilinForm.toMatrix_basisFun

@[simp]
/-
**Matrix.toBilin_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toBilin_toMatrix (B : BilinForm R₁ M₁) : Matrix.toBilin b (B.toMatr
ix b) = B
参数：B : BilinForm R₁ M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem Matrix.toBilin_toMatrix (B : BilinForm R₁ M₁) :
    Matrix.toBilin b (B.toMatrix b) = B :=
  (Matrix.toBilin b).apply_symm_apply B

@[simp]
/-
**LinearMap.BilinForm.toMatrix_toBilin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.toMatrix_toBilin (M : Matrix n n R₁) : BilinForm.toMat
rix b (Matrix.toBilin b M) = M
参数：M : Matrix n n R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem LinearMap.BilinForm.toMatrix_toBilin (M : Matrix n n R₁) :
    BilinForm.toMatrix b (Matrix.toBilin b M) = M :=
  (BilinForm.toMatrix b).apply_symm_apply M

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_toBilin := LinearMap.BilinForm.toMatrix_toBilin

variable {M₂' : Type*} [AddCommMonoid M₂'] [Module R₁ M₂']
variable (c : Basis o R₁ M₂')
variable [DecidableEq o]

-- Cannot be a `simp` lemma because `b` must be inferred.
/-
**LinearMap.BilinForm.toMatrix_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.toMatrix_comp (B : BilinForm R₁ M₁) (l r : M₂' ->ₗ[R₁]
 M₁) : BilinForm.toMatrix c (B.comp l r) = (LinearMap.toMatrix c b l)ᵀ * BilinFo
rm.toMatrix b B * LinearMap.toMatrix c b r
参数：B : BilinForm R₁ M₁；l r : M₂' ->ₗ[R₁] M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix₂_compl₁₂`：LinearMap.toMatrix₂_compl₁₂ (B : M₁ ->ₗ[R] 
M₂ ->ₗ[R] R) (l : M₁' ->ₗ[R] M₁) (r : M₂' ->ₗ[R] M₂) : LinearMap.toMatrix₂ b₁' b
₂' (B.compl₁₂ l r…
-/
theorem LinearMap.BilinForm.toMatrix_comp (B : BilinForm R₁ M₁) (l r : M₂' →ₗ[R₁] M₁) :
    BilinForm.toMatrix c (B.comp l r) =
      (LinearMap.toMatrix c b l)ᵀ * BilinForm.toMatrix b B * LinearMap.toMatrix c b r :=
  LinearMap.toMatrix₂_compl₁₂ _ _ _ _ B _ _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_comp := LinearMap.BilinForm.toMatrix_comp
/-
**LinearMap.BilinForm.toMatrix_compLeft** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.toMatrix_compLeft (B : BilinForm R₁ M₁) (f : M₁ ->ₗ[R₁
] M₁) : BilinForm.toMatrix b (B.compLeft f) = (LinearMap.toMatrix b b f)ᵀ * Bili
nForm.toMatrix b B
参数：B : BilinForm R₁ M₁；f : M₁ ->ₗ[R₁] M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix₂_comp`：LinearMap.toMatrix₂_comp (B : M₁ ->ₗ[R] M₂ ->ₗ
[R] R) (f : M₁' ->ₗ[R] M₁) : LinearMap.toMatrix₂ b₁' b₂ (B.comp f) = (toMatrix b
₁' b₁ f)ᵀ * Li…
-/
theorem LinearMap.BilinForm.toMatrix_compLeft (B : BilinForm R₁ M₁) (f : M₁ →ₗ[R₁] M₁) :
    BilinForm.toMatrix b (B.compLeft f) = (LinearMap.toMatrix b b f)ᵀ * BilinForm.toMatrix b B :=
  LinearMap.toMatrix₂_comp _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_compLeft := LinearMap.BilinForm.toMatrix_compLeft
/-
**LinearMap.BilinForm.toMatrix_compRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.toMatrix_compRight (B : BilinForm R₁ M₁) (f : M₁ ->ₗ[R
₁] M₁) : BilinForm.toMatrix b (B.compRight f) = BilinForm.toMatrix b B * LinearM
ap.toMatrix b b f
参数：B : BilinForm R₁ M₁；f : M₁ ->ₗ[R₁] M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix₂_compl₂`：LinearMap.toMatrix₂_compl₂ (B : M₁ ->ₗ[R] M₂
 ->ₗ[R] R) (f : M₂' ->ₗ[R] M₂) : LinearMap.toMatrix₂ b₁ b₂' (B.compl₂ f) = Linea
rMap.toMatrix₂ b…
-/
theorem LinearMap.BilinForm.toMatrix_compRight (B : BilinForm R₁ M₁) (f : M₁ →ₗ[R₁] M₁) :
    BilinForm.toMatrix b (B.compRight f) = BilinForm.toMatrix b B * LinearMap.toMatrix b b f :=
  LinearMap.toMatrix₂_compl₂ _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_compRight := LinearMap.BilinForm.toMatrix_compRight

@[simp]
/-
**LinearMap.BilinForm.toMatrix_mul_basis_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (c : Basis o R₁ M₁) (B : B
ilinForm R₁ M₁) : (b.toMatrix c)ᵀ * BilinForm.toMatrix b B * b.toMatrix c = Bili
nForm.toMatrix c B
参数：c : Basis o R₁ M₁；B : BilinForm R₁ M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix₂_mul_basis_toMatrix`：LinearMap.toMatrix₂_mul_basis_to
Matrix (c₁ : Basis n' R M₁) (c₂ : Basis m' R M₂) (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) : (
b₁.toMatrix c₁)ᵀ * LinearMap…
-/
theorem LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (c : Basis o R₁ M₁) (B : BilinForm R₁ M₁) :
    (b.toMatrix c)ᵀ * BilinForm.toMatrix b B * b.toMatrix c = BilinForm.toMatrix c B :=
  LinearMap.toMatrix₂_mul_basis_toMatrix _ _ _ _ B

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_mul_basis_toMatrix := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
/-
**LinearMap.BilinForm.mul_toMatrix_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.mul_toMatrix_mul (B : BilinForm R₁ M₁) (M : Matrix o n
 R₁) (N : Matrix n o R₁) : M * BilinForm.toMatrix b B * N = BilinForm.toMatrix c
 (B.comp (Matrix.toLin c b Mᵀ) (Matrix.toLin c b N))
参数：B : BilinForm R₁ M₁；M : Matrix o n R₁；N : Matrix n o R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mul_toMatrix₂_mul`：LinearMap.mul_toMatrix₂_mul (B : M₁ ->ₗ[R] 
M₂ ->ₗ[R] R) (M : Matrix n' n R) (N : Matrix m m' R) : M * LinearMap.toMatrix₂ b
₁ b₂ B * N = Line…
-/
theorem LinearMap.BilinForm.mul_toMatrix_mul (B : BilinForm R₁ M₁) (M : Matrix o n R₁)
    (N : Matrix n o R₁) :
    M * BilinForm.toMatrix b B * N =
      BilinForm.toMatrix c (B.comp (Matrix.toLin c b Mᵀ) (Matrix.toLin c b N)) :=
  LinearMap.mul_toMatrix₂_mul _ _ _ _ B _ _

@[deprecated (since := "2026-01-16")]
alias BilinForm.mul_toMatrix_mul := LinearMap.BilinForm.mul_toMatrix_mul
/-
**LinearMap.BilinForm.mul_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.mul_toMatrix (B : BilinForm R₁ M₁) (M : Matrix n n R₁)
 : M * BilinForm.toMatrix b B = BilinForm.toMatrix b (B.compLeft (Matrix.toLin b
 b Mᵀ))
参数：B : BilinForm R₁ M₁；M : Matrix n n R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mul_toMatrix₂`：LinearMap.mul_toMatrix₂ (B : M₁ ->ₗ[R] M₂ ->ₗ[R
] R) (M : Matrix n' n R) : M * LinearMap.toMatrix₂ b₁ b₂ B = LinearMap.toMatrix₂
 b₁' b₂ (B.co…
-/
theorem LinearMap.BilinForm.mul_toMatrix (B : BilinForm R₁ M₁) (M : Matrix n n R₁) :
    M * BilinForm.toMatrix b B = BilinForm.toMatrix b (B.compLeft (Matrix.toLin b b Mᵀ)) :=
  LinearMap.mul_toMatrix₂ _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.mul_toMatrix := LinearMap.BilinForm.mul_toMatrix
/-
**LinearMap.BilinForm.toMatrix_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.toMatrix_mul (B : BilinForm R₁ M₁) (M : Matrix n n R₁)
 : BilinForm.toMatrix b B * M = BilinForm.toMatrix b (B.compRight (Matrix.toLin 
b b M))
参数：B : BilinForm R₁ M₁；M : Matrix n n R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix₂_mul`：LinearMap.toMatrix₂_mul (B : M₁ ->ₗ[R] M₂ ->ₗ[R
] R) (M : Matrix m m' R) : LinearMap.toMatrix₂ b₁ b₂ B * M = LinearMap.toMatrix₂
 b₁ b₂' (B.co…
-/
theorem LinearMap.BilinForm.toMatrix_mul (B : BilinForm R₁ M₁) (M : Matrix n n R₁) :
    BilinForm.toMatrix b B * M = BilinForm.toMatrix b (B.compRight (Matrix.toLin b b M)) :=
  LinearMap.toMatrix₂_mul _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_mul := LinearMap.BilinForm.toMatrix_mul
/-
**Matrix.toBilin_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toBilin_comp (M : Matrix n n R₁) (P Q : Matrix n o R₁) : (Matrix.to
Bilin b M).comp (toLin c b P) (toLin c b Q) = Matrix.toBilin c (Pᵀ * M * Q)
参数：M : Matrix n n R₁；P Q : Matrix n o R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toBilin.eq_1`：∀ {R₁ : Type u_1} {M₁ : Type u_2} [inst : CommSemir
ing R₁] [inst_1 : AddCommMonoid M₁] [inst_2 : _root_.Module R₁ M₁]   {n : Type u
_5} [inst…
· 使用定理 `LinearMap.BilinForm.toMatrix.eq_1`：∀ {R₁ : Type u_1} {M₁ : Type u_2} [in
st : CommSemiring R₁] [inst_1 : AddCommMonoid M₁] [inst_2 : _root_.Module R₁ M₁]
   {n : Type u_5} [inst…
· 使用定理 `LinearMap.toMatrix₂_symm`：LinearMap.toMatrix₂_symm : (LinearMap.toMatrix
₂ b₁ b₂).symm = Matrix.toLinearMap₂ (N₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toLinearMap₂_compl₁₂`：Matrix.toLinearMap₂_compl₁₂ (M : Matrix n m
 R) (P : Matrix n n' R) (Q : Matrix m m' R) : (Matrix.toLinearMap₂ b₁ b₂ M).comp
l₁₂ (toLin b₁' b₁…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.toLinearMap₂_apply`：Matrix.toLinearMap₂_apply (M : Matrix n m N₂)
 (x : M₁) (y : M₂) : Matrix.toLinearMap₂ b₁ b₂ M x y = ∑ i, ∑ j, b₁.repr x i • b
₂.repr y j • M …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Matrix.toBilin_comp (M : Matrix n n R₁) (P Q : Matrix n o R₁) :
    (Matrix.toBilin b M).comp (toLin c b P) (toLin c b Q) = Matrix.toBilin c (Pᵀ * M * Q) := by
  ext x y
  rw [Matrix.toBilin, LinearMap.BilinForm.toMatrix, Matrix.toBilin, LinearMap.BilinForm.toMatrix,
    toMatrix₂_symm, toMatrix₂_symm, ← Matrix.toLinearMap₂_compl₁₂ b b c c]
  simp

@[simp]
/-
**LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm {B : BilinForm R₁ M₁} : (B.
toMatrix b).IsSymm ↔ B.IsSymm
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LinearMap.BilinForm.toMatrix_apply`：LinearMap.BilinForm.toMatrix_apply (
B : BilinForm R₁ M₁) (i j : n) : BilinForm.toMatrix b B i j = B (b i) (b j)
· 使用定理 `LinearMap.BilinForm.ext_iff_basis`：∀ {ι₁ : Type u_1} {Rₗ : Type u_10} {M
ₗ : Type u_11} [inst : CommSemiring Rₗ] [inst_1 : AddCommMonoid Mₗ]   [inst_2 : 
_root_.Module Rₗ Mₗ] (b…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm {B : BilinForm R₁ M₁} :
    (B.toMatrix b).IsSymm ↔ B.IsSymm := by
  simp [isSymm_iff, IsSymm.ext_iff, isSymm_iff_eq_flip, ext_iff_basis b, eq_comm]

@[simp]
/-
**Matrix.isSymm_toBilin_iff_isSymm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Matrix.isSymm_toBilin_iff_isSymm {M : Matrix n n R₁} : (M.toBilin b).IsSym
m ↔ M.IsSymm
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm`：LinearMap.BilinForm.isSy
mm_toMatrix_iff_isSymm {B : BilinForm R₁ M₁} : (B.toMatrix b).IsSymm ↔ B.IsSymm
· 使用定理 `LinearMap.BilinForm.toMatrix_toBilin`：LinearMap.BilinForm.toMatrix_toBil
in (M : Matrix n n R₁) : BilinForm.toMatrix b (Matrix.toBilin b M) = M
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Matrix.isSymm_toBilin_iff_isSymm {M : Matrix n n R₁} : (M.toBilin b).IsSymm ↔ M.IsSymm := by
  simp [← (M.toBilin b).isSymm_toMatrix_iff_isSymm b]

@[simp]
/-
**LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earMap.BilinForm`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n]   {B : LinearMap.BilinForm R₁ (n → R₁)}, (LinearMa
p.BilinForm.toMatrix' B).IsSymm ↔ B.IsSymm
参数：n → R₁；LinearMap.BilinForm.toMatrix' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm`：LinearMap.BilinForm.isSy
mm_toMatrix_iff_isSymm {B : BilinForm R₁ M₁} : (B.toMatrix b).IsSymm ↔ B.IsSymm
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm {B : BilinForm R₁ (n → R₁)} :
    B.toMatrix'.IsSymm ↔ B.IsSymm :=
  B.isSymm_toMatrix_iff_isSymm (Pi.basisFun R₁ n)

@[simp]
/-
**Matrix.isSymm_toBilin'_iff_isSymm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintyp
e n] [inst_2 : DecidableEq n]   {M : Matrix n n R₁}, (Matrix.toBilin' M).IsSymm 
↔ M.IsSymm
参数：Matrix.toBilin' M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm`：∀ {R₁ : Type u_1} [inst
 : CommSemiring R₁] {n : Type u_5} [inst_1 : Fintype n] [inst_2 : DecidableEq n]
   {B : LinearMap.BilinForm R₁ (n → R…
· 使用定理 `LinearMap.BilinForm.toMatrix'_toBilin'`：∀ {R₁ : Type u_1} [inst : CommSe
miring R₁] {n : Type u_5} [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : M
atrix n n R₁), LinearMap.Bil…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Matrix.isSymm_toBilin'_iff_isSymm {M : Matrix n n R₁} : M.toBilin'.IsSymm ↔ M.IsSymm := by
  simp [← M.toBilin'.isSymm_toMatrix'_iff_isSymm]

end ToMatrix

end Matrix

section MatrixAdjoints

open Matrix

variable {n : Type*} [Fintype n]
variable (b : Basis n R₂ M₂)
variable (J J₃ A A' : Matrix n n R₂)

/-
**Matrix.isAdjointPair_equiv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.isAdjointPair_equiv' [DecidableEq n] (P : Matrix n n R₂) (h : IsUni
t P) : (Pᵀ * J * P).IsAdjointPair (Pᵀ * J * P) A A' ↔ J.IsAdjointPair J (P * A *
 P⁻¹) (P * A' * P⁻¹)
参数：P : Matrix n n R₂；h : IsUnit P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.isAdjointPair_equiv`：Matrix.isAdjointPair_equiv (P : Matrix n n R
) (h : IsUnit P) : (Pᵀ * J * P).IsAdjointPair (Pᵀ * J * P) A₁ A₂ ↔ J.IsAdjointPa
ir J (P * A₁ * P…
-/
theorem Matrix.isAdjointPair_equiv' [DecidableEq n] (P : Matrix n n R₂) (h : IsUnit P) :
    (Pᵀ * J * P).IsAdjointPair (Pᵀ * J * P) A A' ↔
      J.IsAdjointPair J (P * A * P⁻¹) (P * A' * P⁻¹) :=
  Matrix.isAdjointPair_equiv _ _ _ _ h

variable [DecidableEq n]
/-
**mem_pairSelfAdjointMatricesSubmodule'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_pairSelfAdjointMatricesSubmodule' : A in pairSelfAdjointMatricesSubmod
ule J J₃ ↔ Matrix.IsAdjointPair J J₃ A A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_pairSelfAdjointMatricesSubmodule' :
    A ∈ pairSelfAdjointMatricesSubmodule J J₃ ↔ Matrix.IsAdjointPair J J₃ A A := by
  simp only [mem_pairSelfAdjointMatricesSubmodule]

/-- The submodule of self-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
/-
**selfAdjointMatricesSubmodule'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：selfAdjointMatricesSubmodule' : Submodule R₂ (Matrix n n R₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule of self-adjoint matrices with respect to the bilinear form corresp
onding to
the matrix `J`.
-/
def selfAdjointMatricesSubmodule' : Submodule R₂ (Matrix n n R₂) :=
  pairSelfAdjointMatricesSubmodule J J
/-
**mem_selfAdjointMatricesSubmodule'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_selfAdjointMatricesSubmodule' : A in selfAdjointMatricesSubmodule J ↔ 
J.IsSelfAdjoint A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_selfAdjointMatricesSubmodule' :
    A ∈ selfAdjointMatricesSubmodule J ↔ J.IsSelfAdjoint A := by
  simp only [mem_selfAdjointMatricesSubmodule]

/-- The submodule of skew-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
/-
**skewAdjointMatricesSubmodule'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skewAdjointMatricesSubmodule' : Submodule R₂ (Matrix n n R₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule of skew-adjoint matrices with respect to the bilinear form corresp
onding to
the matrix `J`.
-/
def skewAdjointMatricesSubmodule' : Submodule R₂ (Matrix n n R₂) :=
  pairSelfAdjointMatricesSubmodule (-J) J
/-
**mem_skewAdjointMatricesSubmodule'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_skewAdjointMatricesSubmodule' : A in skewAdjointMatricesSubmodule J ↔ 
J.IsSkewAdjoint A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_skewAdjointMatricesSubmodule' :
    A ∈ skewAdjointMatricesSubmodule J ↔ J.IsSkewAdjoint A := by
  simp only [mem_skewAdjointMatricesSubmodule]

end MatrixAdjoints

namespace LinearMap

namespace BilinForm

section Det

open Matrix

variable {A : Type*} [CommRing A] [IsDomain A] [Module A M₂] (B₃ : BilinForm A M₂)
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-
**LinearMap.BilinForm._root_.Matrix.nondegenerate_toBilin'_iff_nondegenerate_toB
ilin** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin {M : Matrix ι ι R₁}
    (b : Basis ι R₁ M₁) : M.toBilin'.Nondegenerate ↔ (Matrix.toBilin b M).Nondegenerate :=
  (nondegenerate_congr_iff b.equivFun.symm).symm

/-!
Lemmas transferring nondegeneracy between a matrix and its associated bilinear form.

These are just aliases of lemmas about `Matrix.toLinearMap₂` specialized to the cases where the
left and right spaces are the same.
-/

/-
**LinearMap.BilinForm._root_.Matrix.Nondegenerate.toBilin'** 是 Mathlib 中的一个定理，位于
命名空间 `LinearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lemmas transferring nondegeneracy between a matrix and its associated bilinear f
orm.

These are just aliases of lemmas about `Matrix.toLinearMap₂` specialized to the 
cases where the
left and right spaces are the same.
-/
theorem _root_.Matrix.Nondegenerate.toBilin' {M : Matrix ι ι R₂} (h : M.Nondegenerate) :
    M.toBilin'.Nondegenerate :=
  h.toLinearMap₂'

@[simp]
/-
**LinearMap.BilinForm._root_.Matrix.nondegenerate_toBilin'_iff** 是 Mathlib 中的一个定
理，位于命名空间 `LinearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.nondegenerate_toBilin'_iff {M : Matrix ι ι R₂} :
    M.toBilin'.Nondegenerate ↔ M.Nondegenerate :=
  Matrix.nondegenerate_toLinearMap₂'_iff
/-
**LinearMap.BilinForm._root_.Matrix.Nondegenerate.toBilin** 是 Mathlib 中的一个定理，位于命
名空间 `LinearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.Nondegenerate.toBilin {M : Matrix ι ι R₂} (h : M.Nondegenerate)
    (b : Basis ι R₂ M₂) : (Matrix.toBilin b M).Nondegenerate :=
  h.toLinearMap₂ b b

@[simp]
/-
**LinearMap.BilinForm._root_.Matrix.nondegenerate_toBilin_iff** 是 Mathlib 中的一个定理
，位于命名空间 `LinearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.nondegenerate_toBilin_iff {M : Matrix ι ι R₂} (b : Basis ι R₂ M₂) :
    (Matrix.toBilin b M).Nondegenerate ↔ M.Nondegenerate :=
  Matrix.nondegenerate_toLinearMap₂_iff b b
/-
**LinearMap.BilinForm._root_.Matrix.SeparatingLeft.toBilin'** 是 Mathlib 中的一个定理，位
于命名空间 `LinearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.SeparatingLeft.toBilin' {M : Matrix ι ι R₂} (h : M.SeparatingLeft) :
    M.toBilin'.SeparatingLeft :=
  h.toLinearMap₂'

@[simp]
/-
**LinearMap.BilinForm._root_.Matrix.separatingLeft_toBilin'_iff** 是 Mathlib 中的一个
定理，位于命名空间 `LinearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.separatingLeft_toBilin'_iff {M : Matrix ι ι R₂} :
    M.toBilin'.SeparatingLeft ↔ M.SeparatingLeft :=
  Matrix.separatingLeft_toLinearMap₂'_iff
/-
**LinearMap.BilinForm._root_.Matrix.SeparatingLeft.toBilin** 是 Mathlib 中的一个定理，位于
命名空间 `LinearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.SeparatingLeft.toBilin {M : Matrix ι ι R₂} (h : M.SeparatingLeft)
    (b : Basis ι R₂ M₂) : (Matrix.toBilin b M).SeparatingLeft :=
  h.toLinearMap₂ b b

@[simp]
/-
**LinearMap.BilinForm._root_.Matrix.separatingLeft_toBilin_iff** 是 Mathlib 中的一个定
理，位于命名空间 `LinearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.separatingLeft_toBilin_iff {M : Matrix ι ι R₂} (b : Basis ι R₂ M₂) :
    (Matrix.toBilin b M).SeparatingLeft ↔ M.SeparatingLeft :=
  Matrix.separatingLeft_toLinearMap₂_iff b b
/-
**LinearMap.BilinForm._root_.Matrix.SeparatingRight.toBilin'** 是 Mathlib 中的一个定理，
位于命名空间 `LinearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.SeparatingRight.toBilin' {M : Matrix ι ι R₂} (h : M.SeparatingRight) :
    M.toBilin'.SeparatingRight :=
  h.toLinearMap₂'

@[simp]
/-
**LinearMap.BilinForm._root_.Matrix.separatingRight_toBilin'_iff** 是 Mathlib 中的一
个定理，位于命名空间 `LinearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.separatingRight_toBilin'_iff {M : Matrix ι ι R₂} :
    M.toBilin'.SeparatingRight ↔ M.SeparatingRight :=
  Matrix.separatingRight_toLinearMap₂'_iff
/-
**LinearMap.BilinForm._root_.Matrix.SeparatingRight.toBilin** 是 Mathlib 中的一个定理，位
于命名空间 `LinearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.SeparatingRight.toBilin {M : Matrix ι ι R₂} (h : M.SeparatingRight)
    (b : Basis ι R₂ M₂) : (Matrix.toBilin b M).SeparatingRight :=
  h.toLinearMap₂ b b

@[simp]
/-
**LinearMap.BilinForm._root_.Matrix.separatingRight_toBilin_iff** 是 Mathlib 中的一个
定理，位于命名空间 `LinearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.separatingRight_toBilin_iff {M : Matrix ι ι R₂} (b : Basis ι R₂ M₂) :
    (Matrix.toBilin b M).SeparatingRight ↔ M.SeparatingRight :=
  Matrix.separatingRight_toLinearMap₂_iff b b

/-! Lemmas transferring nondegeneracy between a bilinear form and its associated matrix

These are just aliases of lemmas about `LinearMap.toMatrix₂` specialized to the cases where the
left and right spaces are the same.
-/

@[simp]
/-
**LinearMap.BilinForm.nondegenerate_toMatrix'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earMap.BilinForm`。
形式化陈述：∀ {R₂ : Type u_3} [inst : CommRing R₂] {ι : Type u_6} [inst_1 : DecidableE
q ι] [inst_2 : Fintype ι]   {B : LinearMap.BilinForm R₂ (ι → R₂)}, (LinearMap.Bi
linForm.toMatrix' B).Nondegenerate ↔ B.Nondegenerate
参数：ι → R₂；LinearMap.BilinForm.toMatrix' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.nondegenerate_toMatrix₂'_iff`：∀ {R : Type u_1} {n : Type u_11}
 {m : Type u_12} [inst : CommRing R] [inst_1 : DecidableEq m] [inst_2 : Fintype 
m]   [inst_3 : DecidableEq n…

--- 原说明 ---
Lemmas transferring nondegeneracy between a bilinear form and its associated mat
rix

These are just aliases of lemmas about `LinearMap.toMatrix₂` specialized to the 
cases where the
left and right spaces are the same.
-/
theorem nondegenerate_toMatrix'_iff {B : BilinForm R₂ (ι → R₂)} :
    B.toMatrix'.Nondegenerate (m := ι) ↔ B.Nondegenerate :=
  LinearMap.nondegenerate_toMatrix₂'_iff
/-
**LinearMap.BilinForm.Nondegenerate.toMatrix'** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap.BilinForm.Nondegenerate`。
形式化陈述：∀ {R₂ : Type u_3} [inst : CommRing R₂] {ι : Type u_6} [inst_1 : DecidableE
q ι] [inst_2 : Fintype ι]   {B : LinearMap.BilinForm R₂ (ι → R₂)}, B.Nondegenera
te → (LinearMap.BilinForm.toMatrix' B).Nondegenerate
参数：ι → R₂；LinearMap.BilinForm.toMatrix' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.Nondegenerate.toMatrix₂'`：∀ {R : Type u_1} {n : Type u_11} {m 
: Type u_12} [inst : CommRing R] [inst_1 : DecidableEq m] [inst_2 : Fintype m]  
 [inst_3 : DecidableEq n…
-/
theorem Nondegenerate.toMatrix' {B : BilinForm R₂ (ι → R₂)} (h : B.Nondegenerate) :
    B.toMatrix'.Nondegenerate :=
  h.toMatrix₂'

@[simp]
/-
**LinearMap.BilinForm.nondegenerate_toMatrix_iff** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap.BilinForm`。
形式化陈述：nondegenerate_toMatrix_iff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) : (Bi
linForm.toMatrix b B).Nondegenerate ↔ B.Nondegenerate
参数：b : Basis ι R₂ M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Matrix.nondegenerate_toBilin_iff`：∀ {R₂ : Type u_3} {M₂ : Type u_4} [ins
t : CommRing R₂] [inst_1 : AddCommGroup M₂] [inst_2 : _root_.Module R₂ M₂]   {ι 
: Type u_6} [inst_3 : …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toBilin_toMatrix`：Matrix.toBilin_toMatrix (B : BilinForm R₁ M₁) :
 Matrix.toBilin b (B.toMatrix b) = B
-/
theorem nondegenerate_toMatrix_iff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) :
    (BilinForm.toMatrix b B).Nondegenerate ↔ B.Nondegenerate :=
  (Matrix.nondegenerate_toBilin_iff b).symm.trans <| (Matrix.toBilin_toMatrix b B).symm ▸ Iff.rfl
/-
**LinearMap.BilinForm.Nondegenerate.toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `LinearMa
p.BilinForm.Nondegenerate`。
形式化陈述：∀ {R₂ : Type u_3} {M₂ : Type u_4} [inst : CommRing R₂] [inst_1 : AddCommGr
oup M₂] [inst_2 : _root_.Module R₂ M₂]   {ι : Type u_6} [inst_3 : DecidableEq ι]
 [inst_4 : Fintype ι] {B : LinearMap.BilinForm R₂ M₂},   B.Nondegenerate → ∀ (b 
: Module.Basis ι R₂ M₂), ((LinearMap.BilinForm.toMatrix b) B).Nondegenerate
参数：b : Module.Basis ι R₂ M₂；(LinearMap.BilinForm.toMatrix b) B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.BilinForm.nondegenerate_toMatrix_iff`：nondegenerate_toMatrix_i
ff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) : (BilinForm.toMatrix b B).Nondegen
erate ↔ B.Nondegenerate
-/
theorem Nondegenerate.toMatrix {B : BilinForm R₂ M₂} (h : B.Nondegenerate) (b : Basis ι R₂ M₂) :
    (BilinForm.toMatrix b B).Nondegenerate :=
  (nondegenerate_toMatrix_iff b).mpr h

@[simp]
/-
**LinearMap.BilinForm.separatingLeft_toMatrix'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap.BilinForm`。
形式化陈述：∀ {R₂ : Type u_3} [inst : CommRing R₂] {ι : Type u_6} [inst_1 : DecidableE
q ι] [inst_2 : Fintype ι]   {B : LinearMap.BilinForm R₂ (ι → R₂)}, (LinearMap.Bi
linForm.toMatrix' B).SeparatingLeft ↔ LinearMap.SeparatingLeft B
参数：ι → R₂；LinearMap.BilinForm.toMatrix' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Matrix.separatingLeft_toBilin'_iff`：∀ {R₂ : Type u_3} [inst : CommRing R
₂] {ι : Type u_6} [inst_1 : DecidableEq ι] [inst_2 : Fintype ι] {M : Matrix ι ι 
R₂},   LinearMap.Separat…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toBilin'_toMatrix'`：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n
 : Type u_5} [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (B : LinearMap.Bili
nForm R₁ (n → R…
-/
theorem separatingLeft_toMatrix'_iff {B : BilinForm R₂ (ι → R₂)} :
    B.toMatrix'.SeparatingLeft (m := ι) ↔ B.SeparatingLeft :=
  Matrix.separatingLeft_toBilin'_iff.symm.trans <| (Matrix.toBilin'_toMatrix' B).symm ▸ Iff.rfl
/-
**LinearMap.BilinForm.SeparatingLeft.toMatrix'** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map.BilinForm.SeparatingLeft`。
形式化陈述：∀ {R₂ : Type u_3} [inst : CommRing R₂] {ι : Type u_6} [inst_1 : DecidableE
q ι] [inst_2 : Fintype ι]   {B : LinearMap.BilinForm R₂ (ι → R₂)}, LinearMap.Sep
aratingLeft B → (LinearMap.BilinForm.toMatrix' B).SeparatingLeft
参数：ι → R₂；LinearMap.BilinForm.toMatrix' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.BilinForm.separatingLeft_toMatrix'_iff`：∀ {R₂ : Type u_3} [ins
t : CommRing R₂] {ι : Type u_6} [inst_1 : DecidableEq ι] [inst_2 : Fintype ι]   
{B : LinearMap.BilinForm R₂ (ι → R₂)},…
-/
theorem SeparatingLeft.toMatrix' {B : BilinForm R₂ (ι → R₂)} (h : B.SeparatingLeft) :
    B.toMatrix'.SeparatingLeft :=
  separatingLeft_toMatrix'_iff.mpr h

@[simp]
/-
**LinearMap.BilinForm.separatingLeft_toMatrix_iff** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earMap.BilinForm`。
形式化陈述：separatingLeft_toMatrix_iff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) : (B
ilinForm.toMatrix b B).SeparatingLeft ↔ B.SeparatingLeft
参数：b : Basis ι R₂ M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Matrix.separatingLeft_toBilin_iff`：∀ {R₂ : Type u_3} {M₂ : Type u_4} [in
st : CommRing R₂] [inst_1 : AddCommGroup M₂] [inst_2 : _root_.Module R₂ M₂]   {ι
 : Type u_6} [inst_3 : …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toBilin_toMatrix`：Matrix.toBilin_toMatrix (B : BilinForm R₁ M₁) :
 Matrix.toBilin b (B.toMatrix b) = B
-/
theorem separatingLeft_toMatrix_iff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) :
    (BilinForm.toMatrix b B).SeparatingLeft ↔ B.SeparatingLeft :=
  (Matrix.separatingLeft_toBilin_iff b).symm.trans <| (Matrix.toBilin_toMatrix b B).symm ▸ Iff.rfl
/-
**LinearMap.BilinForm.SeparatingLeft.toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap.BilinForm.SeparatingLeft`。
形式化陈述：∀ {R₂ : Type u_3} {M₂ : Type u_4} [inst : CommRing R₂] [inst_1 : AddCommGr
oup M₂] [inst_2 : _root_.Module R₂ M₂]   {ι : Type u_6} [inst_3 : DecidableEq ι]
 [inst_4 : Fintype ι] {B : LinearMap.BilinForm R₂ M₂},   LinearMap.SeparatingLef
t B → ∀ (b : Module.Basis ι R₂ M₂), ((LinearMap.BilinForm.toMatrix b) B).Separat
ingLeft
参数：b : Module.Basis ι R₂ M₂；(LinearMap.BilinForm.toMatrix b) B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.BilinForm.separatingLeft_toMatrix_iff`：separatingLeft_toMatrix
_iff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) : (BilinForm.toMatrix b B).Separa
tingLeft ↔ B.SeparatingLeft
-/
theorem SeparatingLeft.toMatrix {B : BilinForm R₂ M₂} (h : B.SeparatingLeft) (b : Basis ι R₂ M₂) :
    (BilinForm.toMatrix b B).SeparatingLeft :=
  (separatingLeft_toMatrix_iff b).mpr h

@[simp]
/-
**LinearMap.BilinForm.separatingRight_toMatrix'_iff** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap.BilinForm`。
形式化陈述：∀ {R₂ : Type u_3} [inst : CommRing R₂] {ι : Type u_6} [inst_1 : DecidableE
q ι] [inst_2 : Fintype ι]   {B : LinearMap.BilinForm R₂ (ι → R₂)}, (LinearMap.Bi
linForm.toMatrix' B).SeparatingRight ↔ LinearMap.SeparatingRight B
参数：ι → R₂；LinearMap.BilinForm.toMatrix' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Matrix.separatingRight_toBilin'_iff`：∀ {R₂ : Type u_3} [inst : CommRing 
R₂] {ι : Type u_6} [inst_1 : DecidableEq ι] [inst_2 : Fintype ι] {M : Matrix ι ι
 R₂},   LinearMap.Separat…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toBilin'_toMatrix'`：∀ {R₁ : Type u_1} [inst : CommSemiring R₁] {n
 : Type u_5} [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (B : LinearMap.Bili
nForm R₁ (n → R…
-/
theorem separatingRight_toMatrix'_iff {B : BilinForm R₂ (ι → R₂)} :
    B.toMatrix'.SeparatingRight (m := ι) ↔ B.SeparatingRight :=
  Matrix.separatingRight_toBilin'_iff.symm.trans <| (Matrix.toBilin'_toMatrix' B).symm ▸ Iff.rfl
/-
**LinearMap.BilinForm.SeparatingRight.toMatrix'** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap.BilinForm.SeparatingRight`。
形式化陈述：∀ {R₂ : Type u_3} [inst : CommRing R₂] {ι : Type u_6} [inst_1 : DecidableE
q ι] [inst_2 : Fintype ι]   {B : LinearMap.BilinForm R₂ (ι → R₂)}, LinearMap.Sep
aratingRight B → (LinearMap.BilinForm.toMatrix' B).SeparatingRight
参数：ι → R₂；LinearMap.BilinForm.toMatrix' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.BilinForm.separatingRight_toMatrix'_iff`：∀ {R₂ : Type u_3} [in
st : CommRing R₂] {ι : Type u_6} [inst_1 : DecidableEq ι] [inst_2 : Fintype ι]  
 {B : LinearMap.BilinForm R₂ (ι → R₂)},…
-/
theorem SeparatingRight.toMatrix' {B : BilinForm R₂ (ι → R₂)} (h : B.SeparatingRight) :
    B.toMatrix'.SeparatingRight :=
  separatingRight_toMatrix'_iff.mpr h

@[simp]
/-
**LinearMap.BilinForm.separatingRight_toMatrix_iff** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap.BilinForm`。
形式化陈述：separatingRight_toMatrix_iff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) : (
BilinForm.toMatrix b B).SeparatingRight ↔ B.SeparatingRight
参数：b : Basis ι R₂ M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Matrix.separatingRight_toBilin_iff`：∀ {R₂ : Type u_3} {M₂ : Type u_4} [i
nst : CommRing R₂] [inst_1 : AddCommGroup M₂] [inst_2 : _root_.Module R₂ M₂]   {
ι : Type u_6} [inst_3 : …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toBilin_toMatrix`：Matrix.toBilin_toMatrix (B : BilinForm R₁ M₁) :
 Matrix.toBilin b (B.toMatrix b) = B
-/
theorem separatingRight_toMatrix_iff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) :
    (BilinForm.toMatrix b B).SeparatingRight ↔ B.SeparatingRight :=
  (Matrix.separatingRight_toBilin_iff b).symm.trans <| (Matrix.toBilin_toMatrix b B).symm ▸ Iff.rfl
/-
**LinearMap.BilinForm.SeparatingRight.toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map.BilinForm.SeparatingRight`。
形式化陈述：∀ {R₂ : Type u_3} {M₂ : Type u_4} [inst : CommRing R₂] [inst_1 : AddCommGr
oup M₂] [inst_2 : _root_.Module R₂ M₂]   {ι : Type u_6} [inst_3 : DecidableEq ι]
 [inst_4 : Fintype ι] {B : LinearMap.BilinForm R₂ M₂},   LinearMap.SeparatingRig
ht B → ∀ (b : Module.Basis ι R₂ M₂), ((LinearMap.BilinForm.toMatrix b) B).Separa
tingRight
参数：b : Module.Basis ι R₂ M₂；(LinearMap.BilinForm.toMatrix b) B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.BilinForm.separatingRight_toMatrix_iff`：separatingRight_toMatr
ix_iff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) : (BilinForm.toMatrix b B).Sepa
ratingRight ↔ B.SeparatingRight
-/
theorem SeparatingRight.toMatrix {B : BilinForm R₂ M₂} (h : B.SeparatingRight) (b : Basis ι R₂ M₂) :
    (BilinForm.toMatrix b B).SeparatingRight :=
  (separatingRight_toMatrix_iff b).mpr h


/-! Some shorthands for combining the above with `Matrix.nondegenerate_of_det_ne_zero` -/

/-
**LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero** 是 Mathlib 中的一个定理，
位于命名空间 `LinearMap.BilinForm`。
形式化陈述：∀ {A : Type u_5} [inst : CommRing A] [IsDomain A] {ι : Type u_6} [inst_2 :
 DecidableEq ι] [inst_3 : Fintype ι]   {M : Matrix ι ι A}, (Matrix.toBilin' M).N
ondegenerate ↔ M.det ≠ 0
参数：Matrix.toBilin' M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.nondegenerate_toBilin'_iff`：∀ {R₂ : Type u_3} [inst : CommRing R₂
] {ι : Type u_6} [inst_1 : DecidableEq ι] [inst_2 : Fintype ι] {M : Matrix ι ι R
₂},   (Matrix.toBilin' …
· 使用定理 `Matrix.nondegenerate_iff_det_ne_zero`：nondegenerate_iff_det_ne_zero [Dec
idableEq n] : Nondegenerate M ↔ M.det != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Some shorthands for combining the above with `Matrix.nondegenerate_of_det_ne_zer
o`
-/
theorem nondegenerate_toBilin'_iff_det_ne_zero {M : Matrix ι ι A} :
    M.toBilin'.Nondegenerate ↔ M.det ≠ 0 := by
  rw [Matrix.nondegenerate_toBilin'_iff, Matrix.nondegenerate_iff_det_ne_zero]
/-
**LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'** 是 Mathlib 中的一个定理，
位于命名空间 `LinearMap.BilinForm`。
形式化陈述：∀ {A : Type u_5} [inst : CommRing A] [IsDomain A] {ι : Type u_6} [inst_2 :
 DecidableEq ι] [inst_3 : Fintype ι]   (M : Matrix ι ι A), M.det ≠ 0 → (Matrix.t
oBilin' M).Nondegenerate
参数：M : Matrix ι ι A；Matrix.toBilin' M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero`：∀ {A : Type 
u_5} [inst : CommRing A] [IsDomain A] {ι : Type u_6} [inst_2 : DecidableEq ι] [i
nst_3 : Fintype ι]   {M : Matrix ι ι A}, (Matrix…
-/
theorem nondegenerate_toBilin'_of_det_ne_zero' (M : Matrix ι ι A) (h : M.det ≠ 0) :
    M.toBilin'.Nondegenerate :=
  nondegenerate_toBilin'_iff_det_ne_zero.mpr h
/-
**LinearMap.BilinForm.nondegenerate_iff_det_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap.BilinForm`。
形式化陈述：nondegenerate_iff_det_ne_zero {B : BilinForm A M₂} (b : Basis ι A M₂) : B.
Nondegenerate ↔ (BilinForm.toMatrix b B).det != 0
参数：b : Basis ι A M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.nondegenerate_iff_det_ne_zero`：nondegenerate_iff_det_ne_zero [Dec
idableEq n] : Nondegenerate M ↔ M.det != 0
· 使用定理 `LinearMap.BilinForm.nondegenerate_toMatrix_iff`：nondegenerate_toMatrix_i
ff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) : (BilinForm.toMatrix b B).Nondegen
erate ↔ B.Nondegenerate
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nondegenerate_iff_det_ne_zero {B : BilinForm A M₂} (b : Basis ι A M₂) :
    B.Nondegenerate ↔ (BilinForm.toMatrix b B).det ≠ 0 := by
  rw [← Matrix.nondegenerate_iff_det_ne_zero, nondegenerate_toMatrix_iff]
/-
**LinearMap.BilinForm.nondegenerate_of_det_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap.BilinForm`。
形式化陈述：nondegenerate_of_det_ne_zero (b : Basis ι A M₂) (h : (BilinForm.toMatrix b
 B₃).det != 0) : B₃.Nondegenerate
参数：b : Basis ι A M₂；h : (BilinForm.toMatrix b B₃).det != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.BilinForm.nondegenerate_iff_det_ne_zero`：nondegenerate_iff_det
_ne_zero {B : BilinForm A M₂} (b : Basis ι A M₂) : B.Nondegenerate ↔ (BilinForm.
toMatrix b B).det != 0
-/
theorem nondegenerate_of_det_ne_zero (b : Basis ι A M₂) (h : (BilinForm.toMatrix b B₃).det ≠ 0) :
    B₃.Nondegenerate :=
  (nondegenerate_iff_det_ne_zero b).mpr h

end Det

section LeftRight

variable [IsDomain R₂] [Module.Free R₂ M₂] [Module.Finite R₂ M₂] {B : BilinForm R₂ M₂}

/-
**LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft** 是 Mathlib 中的一个定理，位于命名空间 `
LinearMap.BilinForm.Nondegenerate`。
形式化陈述：∀ {R₂ : Type u_3} {M₂ : Type u_4} [inst : CommRing R₂] [inst_1 : AddCommGr
oup M₂] [inst_2 : _root_.Module R₂ M₂]   [IsDomain R₂] [Module.Free R₂ M₂] [Modu
le.Finite R₂ M₂] {B : LinearMap.BilinForm R₂ M₂},   LinearMap.SeparatingLeft B →
 B.Nondegenerate
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用引理 `Module.Finite.finite_basis`：finite_basis [Nontrivial R] {ι} [Module.Fini
te R M] (b : Basis ι R M) : _root_.Finite ι
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.BilinForm.nondegenerate_toMatrix_iff`：nondegenerate_toMatrix_i
ff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) : (BilinForm.toMatrix b B).Nondegen
erate ↔ B.Nondegenerate
· 使用定理 `Matrix.nondegenerate_iff_det_ne_zero`：nondegenerate_iff_det_ne_zero [Dec
idableEq n] : Nondegenerate M ↔ M.det != 0
· 使用引理 `Matrix.separatingLeft_iff_det_ne_zero`：separatingLeft_iff_det_ne_zero [D
ecidableEq n] : SeparatingLeft M ↔ M.det != 0
· 使用定理 `LinearMap.BilinForm.separatingLeft_toMatrix_iff`：separatingLeft_toMatrix
_iff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) : (BilinForm.toMatrix b B).Separa
tingLeft ↔ B.SeparatingLeft
-/
lemma Nondegenerate.ofSeparatingLeft (hB : SeparatingLeft B) : B.Nondegenerate := by
  obtain ⟨ι, b⟩ := Module.Free.exists_basis R₂ M₂
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  have : DecidableEq ι := Classical.decEq ι
  rwa [← BilinForm.nondegenerate_toMatrix_iff b, Matrix.nondegenerate_iff_det_ne_zero,
    ← Matrix.separatingLeft_iff_det_ne_zero, separatingLeft_toMatrix_iff]
/-
**LinearMap.BilinForm.Nondegenerate.ofSeparatingRight** 是 Mathlib 中的一个定理，位于命名空间 
`LinearMap.BilinForm.Nondegenerate`。
形式化陈述：∀ {R₂ : Type u_3} {M₂ : Type u_4} [inst : CommRing R₂] [inst_1 : AddCommGr
oup M₂] [inst_2 : _root_.Module R₂ M₂]   [IsDomain R₂] [Module.Free R₂ M₂] [Modu
le.Finite R₂ M₂] {B : LinearMap.BilinForm R₂ M₂},   LinearMap.SeparatingRight B 
→ B.Nondegenerate
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LinearMap.BilinForm.nondegenerate_flip_iff`：nondegenerate_flip_iff {B : 
BilinForm R M} : B.flip.Nondegenerate ↔ B.Nondegenerate
· 使用定理 `LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft`：∀ {R₂ : Type u_3} {M
₂ : Type u_4} [inst : CommRing R₂] [inst_1 : AddCommGroup M₂] [inst_2 : _root_.M
odule R₂ M₂]   [IsDomain R₂] [Module.Fre…
-/
lemma Nondegenerate.ofSeparatingRight (hB : B.SeparatingRight) : B.Nondegenerate :=
  nondegenerate_flip_iff.mp <| .ofSeparatingLeft hB
/-
**LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `Li
nearMap.BilinForm`。
形式化陈述：nondegenerate_iff_ker_eq_bot : B.Nondegenerate ↔ B.ker = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.Nondegenerate.ker_eq_bot`：∀ {R : Type u_1} {M : Type
 u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M]   {B : LinearMap.BilinForm R…
· 使用定理 `LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft`：∀ {R₂ : Type u_3} {M
₂ : Type u_4} [inst : CommRing R₂] [inst_1 : AddCommGroup M₂] [inst_2 : _root_.M
odule R₂ M₂]   [IsDomain R₂] [Module.Fre…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.separatingLeft_iff_ker_eq_bot`：separatingLeft_iff_ker_eq_bot {
B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingLeft ↔ LinearMap.ker B = ⊥
-/
lemma nondegenerate_iff_ker_eq_bot : B.Nondegenerate ↔ B.ker = ⊥ := by
  refine ⟨Nondegenerate.ker_eq_bot, fun h ↦ .ofSeparatingLeft ?_⟩
  rwa [separatingLeft_iff_ker_eq_bot]

end LeftRight

end BilinForm

end LinearMap

