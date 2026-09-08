/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.Algebra.Bilinear

/-!
# Bundled versions of multiplication for matrices

This file provides versions of `LinearMap.mulLeft` and `LinearMap.mulRight` which work for the
heterogeneous multiplication of matrices.
-/

@[expose] public section

variable {l m n o : Type*} {R A : Type*}

section NonUnitalNonAssocSemiring
variable (R) [Fintype m]

section one_side
variable [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]

section left
variable (n) [SMulCommClass R A A]

/-- A version of `LinearMap.mulLeft` for matrix multiplication. -/
@[simps]
/-
**mulLeftLinearMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulLeftLinearMap (X : Matrix l m A) : Matrix m n A ->ₗ[R] Matrix l n A whe
re toFun
参数：X : Matrix l m A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mul_add`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (L : Matrix m n 
α) (…

--- 原说明 ---
A version of `LinearMap.mulLeft` for matrix multiplication.
-/
def mulLeftLinearMap (X : Matrix l m A) :
    Matrix m n A →ₗ[R] Matrix l n A where
  toFun := (X * ·)
  map_smul' := Matrix.mul_smul _
  map_add' := Matrix.mul_add _

/-- On square matrices, `Matrix.mulLeftLinearMap` and `LinearMap.mulLeft` coincide. -/
/-
**mulLeftLinearMap_eq_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulLeftLinearMap_eq_mulLeft : mulLeftLinearMap m R = LinearMap.mulLeft R (
A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On square matrices, `Matrix.mulLeftLinearMap` and `LinearMap.mulLeft` coincide.
-/
theorem mulLeftLinearMap_eq_mulLeft :
    mulLeftLinearMap m R = LinearMap.mulLeft R (A := Matrix m m A) := rfl

/-- A version of `LinearMap.mulLeft_zero_eq_zero` for matrix multiplication. -/
@[simp]
/-
**mulLeftLinearMap_zero_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulLeftLinearMap_zero_eq_zero : mulLeftLinearMap n R (0 : Matrix l m A) = 
0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Matrix.zero_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n
 α), …

--- 原说明 ---
A version of `LinearMap.mulLeft_zero_eq_zero` for matrix multiplication.
-/
theorem mulLeftLinearMap_zero_eq_zero : mulLeftLinearMap n R (0 : Matrix l m A) = 0 :=
  LinearMap.ext fun _ => Matrix.zero_mul _

end left

section right
variable (l) [IsScalarTower R A A]

/-- A version of `LinearMap.mulRight` for matrix multiplication. -/
@[simps]
/-
**mulRightLinearMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulRightLinearMap (Y : Matrix m n A) : Matrix l m A ->ₗ[R] Matrix l n A wh
ere toFun
参数：Y : Matrix m n A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.add_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (L M : Matrix l 
m α)…

--- 原说明 ---
A version of `LinearMap.mulRight` for matrix multiplication.
-/
def mulRightLinearMap (Y : Matrix m n A) :
    Matrix l m A →ₗ[R] Matrix l n A where
  toFun := (· * Y)
  map_smul' _ _ := Matrix.smul_mul _ _ _
  map_add' _ _ := Matrix.add_mul _ _ _

/-- On square matrices, `Matrix.mulRightLinearMap` and `LinearMap.mulRight` coincide. -/
/-
**mulRightLinearMap_eq_mulRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRightLinearMap_eq_mulRight : mulRightLinearMap m R = LinearMap.mulRight
 R (A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On square matrices, `Matrix.mulRightLinearMap` and `LinearMap.mulRight` coincide
.
-/
theorem mulRightLinearMap_eq_mulRight :
    mulRightLinearMap m R = LinearMap.mulRight R (A := Matrix m m A) := rfl

/-- A version of `LinearMap.mulLeft_zero_eq_zero` for matrix multiplication. -/
@[simp]
/-
**mulRightLinearMap_zero_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRightLinearMap_zero_eq_zero : mulRightLinearMap l R (0 : Matrix m n A) 
= 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Matrix.mul_zero`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n
 α), …

--- 原说明 ---
A version of `LinearMap.mulLeft_zero_eq_zero` for matrix multiplication.
-/
theorem mulRightLinearMap_zero_eq_zero : mulRightLinearMap l R (0 : Matrix m n A) = 0 :=
  LinearMap.ext fun _ => Matrix.mul_zero _

end right

end one_side

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]

/-- A version of `LinearMap.mul` for matrix multiplication. -/
@[simps!]
/-
**mulLinearMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulLinearMap : Matrix l m A ->ₗ[R] Matrix m n A ->ₗ[R] Matrix l n A where 
toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `LinearMap.mul` for matrix multiplication.
-/
def mulLinearMap : Matrix l m A →ₗ[R] Matrix m n A →ₗ[R] Matrix l n A where
  toFun := mulLeftLinearMap n R
  map_add' _ _ := LinearMap.ext fun _ => Matrix.add_mul _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => Matrix.smul_mul _ _ _

/-- On square matrices, `Matrix.mulLinearMap` and `LinearMap.mul` coincide. -/
/-
**mulLinearMap_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulLinearMap_eq_mul : mulLinearMap R = LinearMap.mul R (A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On square matrices, `Matrix.mulLinearMap` and `LinearMap.mul` coincide.
-/
theorem mulLinearMap_eq_mul :
    mulLinearMap R = LinearMap.mul R (A := Matrix m m A) := rfl

end NonUnitalNonAssocSemiring

section NonUnital

section one_side
variable [Fintype m] [Fintype n] [Semiring R] [NonUnitalSemiring A] [Module R A]

/-- A version of `LinearMap.mulLeft_mul` for matrix multiplication. -/
@[simp]
/-
**mulLeftLinearMap_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulLeftLinearMap_mul [SMulCommClass R A A] (a : Matrix l m A) (b : Matrix 
m n A) : mulLeftLinearMap o R (a * b) = (mulLeftLinearMap o R a).comp (mulLeftLi
nearMap o R b)
参数：a : Matrix l m A；b : Matrix m n A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mulLeftLinearMap_apply`：∀ {l : Type u_1} {m : Type u_2} (n : Type u_3) (
R : Type u_5) {A : Type u_6} [inst : Fintype m] [inst_1 : Semiring R]   [inst_2 
: NonUnitalN…
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A version of `LinearMap.mulLeft_mul` for matrix multiplication.
-/
theorem mulLeftLinearMap_mul [SMulCommClass R A A] (a : Matrix l m A) (b : Matrix m n A) :
    mulLeftLinearMap o R (a * b) = (mulLeftLinearMap o R a).comp (mulLeftLinearMap o R b) := by
  ext
  simp only [mulLeftLinearMap_apply, LinearMap.comp_apply, Matrix.mul_assoc]

/-- A version of `LinearMap.mulRight_mul` for matrix multiplication. -/
@[simp]
/-
**mulRightLinearMap_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRightLinearMap_mul [IsScalarTower R A A] (a : Matrix m n A) (b : Matrix
 n o A) : mulRightLinearMap l R (a * b) = (mulRightLinearMap l R b).comp (mulRig
htLinearMap l R a)
参数：a : Matrix m n A；b : Matrix n o A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mulRightLinearMap_apply`：∀ (l : Type u_1) {m : Type u_2} {n : Type u_3} 
(R : Type u_5) {A : Type u_6} [inst : Fintype m] [inst_1 : Semiring R]   [inst_2
 : NonUnitalN…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A version of `LinearMap.mulRight_mul` for matrix multiplication.
-/
theorem mulRightLinearMap_mul [IsScalarTower R A A] (a : Matrix m n A) (b : Matrix n o A) :
    mulRightLinearMap l R (a * b) = (mulRightLinearMap l R b).comp (mulRightLinearMap l R a) := by
  ext
  simp only [mulRightLinearMap_apply, LinearMap.comp_apply, Matrix.mul_assoc]

end one_side

variable [Fintype m] [Fintype n] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]

/-- A version of `LinearMap.commute_mulLeft_right` for matrix multiplication. -/
/-
**commute_mulLeftLinearMap_mulRightLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commute_mulLeftLinearMap_mulRightLinearMap (a : Matrix l m A) (b : Matrix 
n o A) : mulLeftLinearMap o R a ∘ₗ mulRightLinearMap m R b = mulRightLinearMap l
 R b ∘ₗ mulLeftLinearMap n R a
参数：a : Matrix l m A；b : Matrix n o A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…

--- 原说明 ---
A version of `LinearMap.commute_mulLeft_right` for matrix multiplication.
-/
theorem commute_mulLeftLinearMap_mulRightLinearMap (a : Matrix l m A) (b : Matrix n o A) :
    mulLeftLinearMap o R a ∘ₗ mulRightLinearMap m R b =
      mulRightLinearMap l R b ∘ₗ mulLeftLinearMap n R a := by
  ext c : 1
  exact (Matrix.mul_assoc a c b).symm

end NonUnital

section Semiring

section one_side
variable [Fintype m] [DecidableEq m] [Semiring R] [Semiring A]

section left
variable [Module R A] [SMulCommClass R A A]

/-- A version of `LinearMap.mulLeft_one` for matrix multiplication. -/
@[simp]
/-
**mulLeftLinearMap_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulLeftLinearMap_one : mulLeftLinearMap n R (1 : Matrix m m A) = LinearMap
.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…

--- 原说明 ---
A version of `LinearMap.mulLeft_one` for matrix multiplication.
-/
theorem mulLeftLinearMap_one : mulLeftLinearMap n R (1 : Matrix m m A) = LinearMap.id :=
  LinearMap.ext fun _ => Matrix.one_mul _

omit [DecidableEq m] in
/-- A version of `LinearMap.mulLeft_eq_zero_iff` for matrix multiplication. -/
@[simp]
/-
**mulLeftLinearMap_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulLeftLinearMap_eq_zero_iff [Nonempty n] (a : Matrix l m A) : mulLeftLine
arMap n R a = 0 ↔ a = 0
参数：a : Matrix l m A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mulLeftLinearMap_apply`：∀ {l : Type u_1} {m : Type u_2} (n : Type u_3) (
R : Type u_5) {A : Type u_6} [inst : Fintype m] [inst_1 : Semiring R]   [inst_2 
: NonUnitalN…
· 使用定理 `Matrix.mul_single_apply_same`：mul_single_apply_same (i : m) (j : n) (a :
 l) (M : Matrix l m α) : (M * single i j c) a j = M a i * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
· 使用定理 `mulLeftLinearMap_zero_eq_zero`：mulLeftLinearMap_zero_eq_zero : mulLeftLi
nearMap n R (0 : Matrix l m A) = 0

--- 原说明 ---
A version of `LinearMap.mulLeft_eq_zero_iff` for matrix multiplication.
-/
theorem mulLeftLinearMap_eq_zero_iff [Nonempty n] (a : Matrix l m A) :
    mulLeftLinearMap n R a = 0 ↔ a = 0 := by
  constructor <;> intro h
  · inhabit n
    ext i j
    classical
    replace h := DFunLike.congr_fun h (Matrix.single j (default : n) 1)
    simpa using Matrix.ext_iff.2 h i default
  · rw [h]
    exact mulLeftLinearMap_zero_eq_zero _ _

/-- A version of `LinearMap.pow_mulLeft` for matrix multiplication. -/
@[simp]
/-
**pow_mulLeftLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_mulLeftLinearMap (a : Matrix m m A) (k : Nat) : mulLeftLinearMap n R a
 ^ k = mulLeftLinearMap n R (a ^ k)
参数：a : Matrix m m A；k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `LinearMap.pow_mulLeft` for matrix multiplication.
-/
theorem pow_mulLeftLinearMap (a : Matrix m m A) (k : ℕ) :
    mulLeftLinearMap n R a ^ k = mulLeftLinearMap n R (a ^ k) :=
  match k with
  | 0 => by rw [pow_zero, pow_zero, mulLeftLinearMap_one, Module.End.one_eq_id]
  | (n + 1) => by
    rw [pow_succ, pow_succ, mulLeftLinearMap_mul, Module.End.mul_eq_comp, pow_mulLeftLinearMap]

end left

section right
variable [Module R A] [IsScalarTower R A A]

/-- A version of `LinearMap.mulRight_one` for matrix multiplication. -/
@[simp]
/-
**mulRightLinearMap_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRightLinearMap_one : mulRightLinearMap l R (1 : Matrix m m A) = LinearM
ap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…

--- 原说明 ---
A version of `LinearMap.mulRight_one` for matrix multiplication.
-/
theorem mulRightLinearMap_one : mulRightLinearMap l R (1 : Matrix m m A) = LinearMap.id :=
  LinearMap.ext fun _ => Matrix.mul_one _

omit [DecidableEq m] in
/-- A version of `LinearMap.mulRight_eq_zero_iff` for matrix multiplication. -/
@[simp]
/-
**mulRightLinearMap_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRightLinearMap_eq_zero_iff (a : Matrix m n A) [Nonempty l] : mulRightLi
nearMap l R a = 0 ↔ a = 0
参数：a : Matrix m n A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mulRightLinearMap_apply`：∀ (l : Type u_1) {m : Type u_2} {n : Type u_3} 
(R : Type u_5) {A : Type u_6} [inst : Fintype m] [inst_1 : Semiring R]   [inst_2
 : NonUnitalN…
· 使用定理 `Matrix.single_mul_apply_same`：single_mul_apply_same (i : l) (j : m) (b :
 n) (M : Matrix m n α) : (single i j c * M) i b = c * M j b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
· 使用定理 `mulRightLinearMap_zero_eq_zero`：mulRightLinearMap_zero_eq_zero : mulRigh
tLinearMap l R (0 : Matrix m n A) = 0

--- 原说明 ---
A version of `LinearMap.mulRight_eq_zero_iff` for matrix multiplication.
-/
theorem mulRightLinearMap_eq_zero_iff (a : Matrix m n A) [Nonempty l] :
    mulRightLinearMap l R a = 0 ↔ a = 0 := by
  constructor <;> intro h
  · inhabit l
    ext i j
    classical
    replace h := DFunLike.congr_fun h (Matrix.single (default : l) i 1)
    simpa using Matrix.ext_iff.2 h default j
  · rw [h]
    exact mulRightLinearMap_zero_eq_zero _ _

/-- A version of `LinearMap.pow_mulRight` for matrix multiplication. -/
@[simp]
/-
**pow_mulRightLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_mulRightLinearMap (a : Matrix m m A) (k : Nat) : mulRightLinearMap l R
 a ^ k = mulRightLinearMap l R (a ^ k)
参数：a : Matrix m m A；k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `LinearMap.pow_mulRight` for matrix multiplication.
-/
theorem pow_mulRightLinearMap (a : Matrix m m A) (k : ℕ) :
    mulRightLinearMap l R a ^ k = mulRightLinearMap l R (a ^ k) :=
  match k with
  | 0 => by rw [pow_zero, pow_zero, mulRightLinearMap_one, Module.End.one_eq_id]
  | (n + 1) => by
    rw [pow_succ, pow_succ', mulRightLinearMap_mul, Module.End.mul_eq_comp, pow_mulRightLinearMap]

end right

end one_side

end Semiring

