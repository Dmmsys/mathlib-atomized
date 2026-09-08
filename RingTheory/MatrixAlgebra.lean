/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Eric Wieser
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Composition
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Algebra isomorphisms between tensor products and matrices

## Main definitions

* `matrixEquivTensor : Matrix n n A ≃ₐ[R] (A ⊗[R] Matrix n n R)`.
* `Matrix.kroneckerTMulAlgEquiv :
    Matrix m m A ⊗[R] Matrix n n B ≃ₐ[S] Matrix (m × n) (m × n) (A ⊗[R] B)`,
  where the forward map is the (tensor-ified) Kronecker product.
-/

@[expose] public section

open TensorProduct Algebra.TensorProduct Matrix

variable {l m n p : Type*} {R S A B M N : Type*}
section Module

variable [CommSemiring R] [Semiring S] [Semiring A] [Semiring B] [AddCommMonoid M] [AddCommMonoid N]
variable [Algebra R S] [Algebra R A] [Algebra R B] [Module R M] [Module S M] [Module R N]
variable [IsScalarTower R S M]
variable [Fintype l] [Fintype m] [Fintype n] [Fintype p]
variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]

open Kronecker

variable (l m n p R S A M N)

attribute [local ext] ext_linearMap

/-- `Matrix.kroneckerTMul` as a linear equivalence, when the two arguments are tensored. -/
/-
**kroneckerTMulLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：kroneckerTMulLinearEquiv : Matrix l m M otimes[R] Matrix n p N ≃ₗ[S] Matri
x (l × n) (m × p) (M otimes[R] N)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
`Matrix.kroneckerTMul` as a linear equivalence, when the two arguments are tenso
red.
-/
def kroneckerTMulLinearEquiv :
    Matrix l m M ⊗[R] Matrix n p N ≃ₗ[S] Matrix (l × n) (m × p) (M ⊗[R] N) :=
  .ofLinearMap
    (AlgebraTensorModule.lift <| kroneckerTMulBilinear R S)
    (Matrix.liftLinear R fun ii jj =>
      AlgebraTensorModule.map (singleLinearMap S ii.1 jj.1) (singleLinearMap R ii.2 jj.2))
    (by
      ext : 4
      simp [single_kroneckerTMul_single])
    (by
      ext : 5
      simp [single_kroneckerTMul_single])

@[simp]
/-
**kroneckerTMulLinearEquiv_tmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kroneckerTMulLinearEquiv_tmul (a : Matrix l m M) (b : Matrix n p N) : kron
eckerTMulLinearEquiv l m n p R S M N (a otimesₜ b) = a otimesₖₜ b
参数：a : Matrix l m M；b : Matrix n p N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem kroneckerTMulLinearEquiv_tmul (a : Matrix l m M) (b : Matrix n p N) :
    kroneckerTMulLinearEquiv l m n p R S M N (a ⊗ₜ b) = a ⊗ₖₜ b := rfl

@[simp]
/-
**kroneckerTMulLinearEquiv_symm_kroneckerTMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kroneckerTMulLinearEquiv_symm_kroneckerTMul (a : Matrix l m M) (b : Matrix
 n p N) : (kroneckerTMulLinearEquiv l m n p R S M N).symm (a otimesₖₜ b) = a oti
mesₜ b
参数：a : Matrix l m M；b : Matrix n p N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kroneckerTMulLinearEquiv_symm_kroneckerTMul (a : Matrix l m M) (b : Matrix n p N) :
    (kroneckerTMulLinearEquiv l m n p R S M N).symm (a ⊗ₖₜ b) = a ⊗ₜ b := by
  simp [LinearEquiv.symm_apply_eq]

@[simp]
/-
**kroneckerTMulAlgEquiv_symm_single_tmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kroneckerTMulAlgEquiv_symm_single_tmul (ia : l) (ja : m) (ib : n) (jb : p)
 (a : M) (b : N) : (kroneckerTMulLinearEquiv l m n p R S M N).symm (single (ia, 
ib) (ja, jb) (a otimesₜ b)) = single ia ja a otimesₜ single ib jb b
参数：ia : l；ja : m；ib : n；jb : p；a : M；b : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `kroneckerTMulLinearEquiv_tmul`：kroneckerTMulLinearEquiv_tmul (a : Matrix
 l m M) (b : Matrix n p N) : kroneckerTMulLinearEquiv l m n p R S M N (a otimesₜ
 b) = a otimesₖₜ b
· 使用定理 `Matrix.single_kroneckerTMul_single`：single_kroneckerTMul_single [Decidab
leEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p] (i₁ : l) (j₁ : m) (i₂ : 
n) (j₂ : p) (a : α) (b :…
-/
theorem kroneckerTMulAlgEquiv_symm_single_tmul
    (ia : l) (ja : m) (ib : n) (jb : p) (a : M) (b : N) :
    (kroneckerTMulLinearEquiv l m n p R S M N).symm (single (ia, ib) (ja, jb) (a ⊗ₜ b)) =
      single ia ja a ⊗ₜ single ib jb b := by
  rw [LinearEquiv.symm_apply_eq, kroneckerTMulLinearEquiv_tmul,
    single_kroneckerTMul_single]

@[simp]
/-
**kroneckerTMulLinearEquiv_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kroneckerTMulLinearEquiv_one [Module S A] [IsScalarTower R S A] : kronecke
rTMulLinearEquiv m m n n R S A B 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.kroneckerMap_one_one`：kroneckerMap_one_one [Zero α] [Zero β] [Zer
o γ] [One α] [One β] [One γ] [DecidableEq m] [DecidableEq n] (f : α -> β -> γ) (
hf₁ : forall b, f…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
-/
theorem kroneckerTMulLinearEquiv_one [Module S A] [IsScalarTower R S A] :
    kroneckerTMulLinearEquiv m m n n R S A B 1 = 1 := by simp [Algebra.TensorProduct.one_def]

/-- Note this can't be stated for rectangular matrices because there is no
`HMul (TensorProduct R _ _) (TensorProduct R _ _) (TensorProduct R _ _)` instance. -/
@[simp]
/-
**kroneckerTMulLinearEquiv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：kroneckerTMulLinearEquiv_mul [Module S A] [IsScalarTower R S A] : forall x
 y : Matrix m m A otimes[R] Matrix n n B, kroneckerTMulLinearEquiv m m n n R S A
 B (x * y) = kroneckerTMulLinearEquiv m m n n R S A B x * kroneckerTMulLinearEqu
iv m m n n R S A B y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.map_mul_iff`：map_mul_iff (f : A ->ₗ[R] B) : (forall x y, f (x 
* y) = f x * f y) ↔ (LinearMap.mul R A).compr₂ f = (LinearMap.mul R B ∘ₗ f).comp
l₂ f
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Matrix.ext_linearMap`：ext_linearMap [Finite m] [Finite n] [Semiring R] [
AddCommMonoid α] [AddCommMonoid β] [Module R α] [Module R β] ⦃f g : Matrix m n α
 ->ₗ[R] β⦄…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `Matrix.singleLinearMap_apply`：∀ {m : Type u_2} {n : Type u_3} (R : Type 
u_5) {α : Type u_7} [inst : DecidableEq m] [inst_1 : DecidableEq n]   [inst_2 : 
Semiring R] [inst_…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `Matrix.mul_kroneckerTMul_mul`：mul_kroneckerTMul_mul [NonUnitalSemiring α
] [NonUnitalSemiring β] [Module R α] [Module R β] [IsScalarTower R α α] [SMulCom
mClass R α α] [IsS…
· 使用定理 `Matrix.single_kroneckerTMul_single`：single_kroneckerTMul_single [Decidab
leEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p] (i₁ : l) (j₁ : m) (i₂ : 
n) (j₂ : p) (a : α) (b :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Note this can't be stated for rectangular matrices because there is no
`HMul (TensorProduct R _ _) (TensorProduct R _ _) (TensorProduct R _ _)` instanc
e.
-/
theorem kroneckerTMulLinearEquiv_mul [Module S A] [IsScalarTower R S A] :
    ∀ x y : Matrix m m A ⊗[R] Matrix n n B,
      kroneckerTMulLinearEquiv m m n n R S A B (x * y) =
        kroneckerTMulLinearEquiv m m n n R S A B x * kroneckerTMulLinearEquiv m m n n R S A B y :=
  (kroneckerTMulLinearEquiv m m n n R S A B).toLinearMap.restrictScalars R |>.map_mul_iff.2 <| by
    ext : 10
    simp [single_kroneckerTMul_single, mul_kroneckerTMul_mul]

/-- `Matrix.kronecker` as a linear equivalence, when the two arguments are tensored. -/
/-
**kroneckerLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：kroneckerLinearEquiv : Matrix l m R otimes[R] Matrix n p R ≃ₗ[R] Matrix (l
 × n) (m × p) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.kronecker` as a linear equivalence, when the two arguments are tensored.
-/
def kroneckerLinearEquiv : Matrix l m R ⊗[R] Matrix n p R ≃ₗ[R] Matrix (l × n) (m × p) R :=
  (kroneckerTMulLinearEquiv l m n p R R R R).trans (TensorProduct.lid R R).mapMatrix

variable {l m n p R}
/-
**kroneckerLinearEquiv_tmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {p : Type u_4} {R : Type u_
5} [inst : CommSemiring R]   [inst_1 : Fintype l] [inst_2 : Fintype m] [inst_3 :
 Fintype n] [inst_4 : Fintype p] [inst_5 : DecidableEq l]   [inst_6 : DecidableE
q m] [inst_7 : DecidableEq n] [inst_8 : DecidableEq p] (x : Matrix l m R) (y : M
atrix n p R),   (kroneckerLinearEquiv l m n p R) (x ⊗ₜ[R] y) = Matrix.kroneckerM
ap (fun x1 x2 => x1 * x2) x y
参数：x : Matrix l m R；y : Matrix n p R；kroneckerLinearEquiv l m n p R；x ⊗ₜ[R] y；fu
n x1 x2 => x1 * x2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem kroneckerLinearEquiv_tmul (x : Matrix l m R) (y : Matrix n p R) :
    kroneckerLinearEquiv l m n p R (x ⊗ₜ y) = x ⊗ₖ y := rfl
/-
**kroneckerLinearEquiv_symm_kronecker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {p : Type u_4} {R : Type u_
5} [inst : CommSemiring R]   [inst_1 : Fintype l] [inst_2 : Fintype m] [inst_3 :
 Fintype n] [inst_4 : Fintype p] [inst_5 : DecidableEq l]   [inst_6 : DecidableE
q m] [inst_7 : DecidableEq n] [inst_8 : DecidableEq p] (x : Matrix l m R) (y : M
atrix n p R),   (kroneckerLinearEquiv l m n p R).symm (Matrix.kroneckerMap (fun 
x1 x2 => x1 * x2) x y) = x ⊗ₜ[R] y
参数：x : Matrix l m R；y : Matrix n p R；kroneckerLinearEquiv l m n p R；Matrix.krone
ckerMap (fun x1 x2 => x1 * x2) x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem kroneckerLinearEquiv_symm_kronecker (x : Matrix l m R) (y : Matrix n p R) :
    (kroneckerLinearEquiv l m n p R).symm (x ⊗ₖ y) = x ⊗ₜ y := by simp [LinearEquiv.symm_apply_eq]

end Module


variable [CommSemiring R]
variable [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable (n R A)

namespace MatrixEquivTensor

/-- (Implementation detail).
The function underlying `(A ⊗[R] Matrix n n R) →ₐ[R] Matrix n n A`,
as an `R`-bilinear map.
-/
/-
**MatrixEquivTensor.toFunBilinear** 是 Mathlib 中的一个定义，位于命名空间 `MatrixEquivTensor`。
形式化陈述：toFunBilinear : A ->ₗ[R] Matrix n n R ->ₗ[R] Matrix n n A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation detail).
The function underlying `(A ⊗[R] Matrix n n R) →ₐ[R] Matrix n n A`,
as an `R`-bilinear map.
-/
def toFunBilinear : A →ₗ[R] Matrix n n R →ₗ[R] Matrix n n A :=
  (Algebra.lsmul R R (Matrix n n A)).toLinearMap.compl₂ (Algebra.linearMap R A).mapMatrix

@[simp]
/-
**MatrixEquivTensor.toFunBilinear_apply** 是 Mathlib 中的一个定理，位于命名空间 `MatrixEquivTe
nsor`。
形式化陈述：toFunBilinear_apply (a : A) (m : Matrix n n R) : toFunBilinear n R A a m =
 a • m.map (algebraMap R A)
参数：a : A；m : Matrix n n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFunBilinear_apply (a : A) (m : Matrix n n R) :
    toFunBilinear n R A a m = a • m.map (algebraMap R A) :=
  rfl

/-- (Implementation detail).
The function underlying `(A ⊗[R] Matrix n n R) →ₐ[R] Matrix n n A`,
as an `R`-linear map.
-/
/-
**MatrixEquivTensor.toFunLinear** 是 Mathlib 中的一个定义，位于命名空间 `MatrixEquivTensor`。
形式化陈述：toFunLinear : A otimes[R] Matrix n n R ->ₗ[R] Matrix n n A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation detail).
The function underlying `(A ⊗[R] Matrix n n R) →ₐ[R] Matrix n n A`,
as an `R`-linear map.
-/
def toFunLinear : A ⊗[R] Matrix n n R →ₗ[R] Matrix n n A :=
  TensorProduct.lift (toFunBilinear n R A)

variable [DecidableEq n] [Fintype n]

/-- The function `(A ⊗[R] Matrix n n R) →ₐ[R] Matrix n n A`, as an algebra homomorphism.
-/
/-
**MatrixEquivTensor.toFunAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `MatrixEquivTensor`。
形式化陈述：toFunAlgHom : A otimes[R] Matrix n n R ->ₐ[R] Matrix n n A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `(A ⊗[R] Matrix n n R) →ₐ[R] Matrix n n A`, as an algebra homomorph
ism.
-/
def toFunAlgHom : A ⊗[R] Matrix n n R →ₐ[R] Matrix n n A :=
  algHomOfLinearMapTensorProduct (toFunLinear n R A)
    (by
      intros
      simp_rw [toFunLinear, lift.tmul, toFunBilinear_apply, Matrix.map_mul]
      ext
      dsimp
      simp_rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Finset.mul_sum,
        _root_.mul_assoc, Algebra.left_comm])
    (by
      simp_rw [toFunLinear, lift.tmul, toFunBilinear_apply,
        Matrix.map_one (algebraMap R A) (map_zero _) (map_one _), one_smul])

@[simp]
/-
**MatrixEquivTensor.toFunAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `MatrixEquivTens
or`。
形式化陈述：toFunAlgHom_apply (a : A) (m : Matrix n n R) : toFunAlgHom n R A (a otimes
ₜ m) = a • m.map (algebraMap R A)
参数：a : A；m : Matrix n n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFunAlgHom_apply (a : A) (m : Matrix n n R) :
    toFunAlgHom n R A (a ⊗ₜ m) = a • m.map (algebraMap R A) := rfl

/-- (Implementation detail.)

The bare function `Matrix n n A → A ⊗[R] Matrix n n R`.
(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
-/
/-
**MatrixEquivTensor.invFun** 是 Mathlib 中的一个定义，位于命名空间 `MatrixEquivTensor`。
形式化陈述：invFun (M : Matrix n n A) : A otimes[R] Matrix n n R
参数：M : Matrix n n A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation detail.)

The bare function `Matrix n n A → A ⊗[R] Matrix n n R`.
(We don't need to show that it's an algebra map, thankfully --- just that it's a
n inverse.)
-/
def invFun (M : Matrix n n A) : A ⊗[R] Matrix n n R :=
  ∑ p : n × n, M p.1 p.2 ⊗ₜ single p.1 p.2 1

@[simp]
/-
**MatrixEquivTensor.invFun_zero** 是 Mathlib 中的一个定理，位于命名空间 `MatrixEquivTensor`。
形式化陈述：invFun_zero : invFun n R A 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invFun_zero : invFun n R A 0 = 0 := by simp [invFun]

@[simp]
/-
**MatrixEquivTensor.invFun_add** 是 Mathlib 中的一个定理，位于命名空间 `MatrixEquivTensor`。
形式化陈述：invFun_add (M N : Matrix n n A) : invFun n R A (M + N) = invFun n R A M + 
invFun n R A N
参数：M N : Matrix n n A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invFun_add (M N : Matrix n n A) :
    invFun n R A (M + N) = invFun n R A M + invFun n R A N := by
  simp [invFun, add_tmul, Finset.sum_add_distrib]

@[simp]
/-
**MatrixEquivTensor.invFun_smul** 是 Mathlib 中的一个定理，位于命名空间 `MatrixEquivTensor`。
形式化陈述：invFun_smul (a : A) (M : Matrix n n A) : invFun n R A (a • M) = a otimesₜ 
1 * invFun n R A M
参数：a : A；M : Matrix n n A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invFun_smul (a : A) (M : Matrix n n A) :
    invFun n R A (a • M) = a ⊗ₜ 1 * invFun n R A M := by
  simp [invFun, Finset.mul_sum]

@[simp]
/-
**MatrixEquivTensor.invFun_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `MatrixEquivTens
or`。
形式化陈述：invFun_algebraMap (M : Matrix n n R) : invFun n R A (M.map (algebraMap R A
)) = 1 otimesₜ M
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Matrix.matrix_eq_sum_single`：matrix_eq_sum_single [AddCommMonoid α] [Fin
type m] [Fintype n] (x : Matrix m n α) : x = ∑ i : m, ∑ j : n, single i j (x i j
)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.smul_single`：smul_single [SMulZeroClass R α] (r : R) (i : m) (j :
 n) (a : α) : r • single i j a = single i j (r • a)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
-/
theorem invFun_algebraMap (M : Matrix n n R) : invFun n R A (M.map (algebraMap R A)) = 1 ⊗ₜ M := by
  dsimp [invFun]
  simp only [Algebra.algebraMap_eq_smul_one, smul_tmul, ← tmul_sum]
  congr
  conv_rhs => rw [matrix_eq_sum_single M]
  convert! Finset.sum_product (β := Matrix n n R) ..; simp
/-
**MatrixEquivTensor.right_inv** 是 Mathlib 中的一个定理，位于命名空间 `MatrixEquivTensor`。
形式化陈述：right_inv (M : Matrix n n A) : (toFunAlgHom n R A) (invFun n R A M) = M
参数：M : Matrix n n A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.matrix_eq_sum_single`：matrix_eq_sum_single [AddCommMonoid α] [Fin
type m] [Fintype n] (x : Matrix m n α) : x = ∑ i : m, ∑ j : n, single i j (x i j
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Matrix.map_single`：map_single (i : m) (j : n) (a : α) {β : Type*} [Zero 
β] {F : Type*} [FunLike F α β] [ZeroHomClass F α β] (f : F) : (single i j a).map
 f = si…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Matrix.smul_single`：smul_single [SMulZeroClass R α] (r : R) (i : m) (j :
 n) (a : α) : r • single i j a = single i j (r • a)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
-/
theorem right_inv (M : Matrix n n A) : (toFunAlgHom n R A) (invFun n R A M) = M := by
  simp only [invFun, map_sum, toFunAlgHom_apply]
  convert! Finset.sum_product (β := Matrix n n A) ..
  conv_lhs => rw [matrix_eq_sum_single M]
  simp
/-
**MatrixEquivTensor.left_inv** 是 Mathlib 中的一个定理，位于命名空间 `MatrixEquivTensor`。
形式化陈述：left_inv (M : A otimes[R] Matrix n n R) : invFun n R A (toFunAlgHom n R A 
M) = M
参数：M : A otimes[R] Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MatrixEquivTensor.invFun_zero`：invFun_zero : invFun n R A 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MatrixEquivTensor.invFun_smul`：invFun_smul (a : A) (M : Matrix n n A) : 
invFun n R A (a • M) = a otimesₜ 1 * invFun n R A M
· 使用定理 `MatrixEquivTensor.invFun_algebraMap`：invFun_algebraMap (M : Matrix n n R
) : invFun n R A (M.map (algebraMap R A)) = 1 otimesₜ M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MatrixEquivTensor.invFun_add`：invFun_add (M N : Matrix n n A) : invFun n
 R A (M + N) = invFun n R A M + invFun n R A N
-/
theorem left_inv (M : A ⊗[R] Matrix n n R) : invFun n R A (toFunAlgHom n R A M) = M := by
  induction M with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy =>
    rw [map_add]
    conv_rhs => rw [← hx, ← hy, ← invFun_add]

/-- (Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] Matrix n n R) ≃ Matrix n n A`.
-/
/-
**MatrixEquivTensor.equiv** 是 Mathlib 中的一个定义，位于命名空间 `MatrixEquivTensor`。
形式化陈述：equiv : A otimes[R] Matrix n n R ≃ Matrix n n A where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MatrixEquivTensor.left_inv`：left_inv (M : A otimes[R] Matrix n n R) : in
vFun n R A (toFunAlgHom n R A M) = M
· 使用定理 `MatrixEquivTensor.right_inv`：right_inv (M : Matrix n n A) : (toFunAlgHom
 n R A) (invFun n R A M) = M

--- 原说明 ---
(Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] Matrix n n R) ≃ Matrix
 n n A`.
-/
def equiv : A ⊗[R] Matrix n n R ≃ Matrix n n A where
  toFun := toFunAlgHom n R A
  invFun := invFun n R A
  left_inv := left_inv n R A
  right_inv := right_inv n R A

end MatrixEquivTensor

variable [Fintype n] [DecidableEq n]

/-- The `R`-algebra isomorphism `Matrix n n A ≃ₐ[R] (A ⊗[R] Matrix n n R)`.
-/
/-
**matrixEquivTensor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：matrixEquivTensor : Matrix n n A ≃ₐ[R] A otimes[R] Matrix n n R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-algebra isomorphism `Matrix n n A ≃ₐ[R] (A ⊗[R] Matrix n n R)`.
-/
def matrixEquivTensor : Matrix n n A ≃ₐ[R] A ⊗[R] Matrix n n R :=
  AlgEquiv.symm { MatrixEquivTensor.toFunAlgHom n R A, MatrixEquivTensor.equiv n R A with }

open MatrixEquivTensor

@[simp]
/-
**matrixEquivTensor_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：matrixEquivTensor_apply (M : Matrix n n A) : matrixEquivTensor n R A M = ∑
 p : n × n, M p.1 p.2 otimesₜ single p.1 p.2 1
参数：M : Matrix n n A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem matrixEquivTensor_apply (M : Matrix n n A) :
    matrixEquivTensor n R A M = ∑ p : n × n, M p.1 p.2 ⊗ₜ single p.1 p.2 1 :=
  rfl

-- High priority, to go before `matrixEquivTensor_apply`
@[simp high]
/-
**matrixEquivTensor_apply_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：matrixEquivTensor_apply_single (i j : n) (x : A) : matrixEquivTensor n R A
 (single i j x) = x otimesₜ single i j 1
参数：i j : n；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `TensorProduct.ite_tmul`：ite_tmul (x₁ : M) (x₂ : N) (P : Prop) [Decidable
 P] : (if P then x₁ else 0) otimesₜ[R] x₂ = if P then x₁ otimesₜ x₂ else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
-/
theorem matrixEquivTensor_apply_single (i j : n) (x : A) :
    matrixEquivTensor n R A (single i j x) = x ⊗ₜ single i j 1 := by
  have t : ∀ p : n × n, i = p.1 ∧ j = p.2 ↔ p = (i, j) := by aesop
  simp [ite_tmul, t, single]

@[simp]
/-
**matrixEquivTensor_apply_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：matrixEquivTensor_apply_symm (a : A) (M : Matrix n n R) : (matrixEquivTens
or n R A).symm (a otimesₜ M) = a • M.map (algebraMap R A)
参数：a : A；M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem matrixEquivTensor_apply_symm (a : A) (M : Matrix n n R) :
    (matrixEquivTensor n R A).symm (a ⊗ₜ M) = a • M.map (algebraMap R A) :=
  rfl

namespace Matrix
open scoped Kronecker

variable (m) (S B)
variable [CommSemiring S] [Algebra R S] [Algebra S A] [IsScalarTower R S A]
variable [Fintype m] [DecidableEq m]

/-- `Matrix.kroneckerTMul` as an algebra equivalence, when the two arguments are tensored. -/
/-
**Matrix.kroneckerTMulAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：kroneckerTMulAlgEquiv : Matrix m m A otimes[R] Matrix n n B ≃ₐ[S] Matrix (
m × n) (m × n) (A otimes[R] B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.kroneckerTMul` as an algebra equivalence, when the two arguments are ten
sored.
-/
def kroneckerTMulAlgEquiv :
    Matrix m m A ⊗[R] Matrix n n B ≃ₐ[S] Matrix (m × n) (m × n) (A ⊗[R] B) :=
  .ofLinearEquiv (kroneckerTMulLinearEquiv m m n n R S A B)
    (kroneckerTMulLinearEquiv_one _ _ _ _ _)
    (kroneckerTMulLinearEquiv_mul _ _ _ _ _)

variable {m n A B}

@[simp]
/-
**Matrix.kroneckerTMulAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerTMulAlgEquiv_apply (x : Matrix m m A otimes[R] Matrix n n B) : (k
roneckerTMulAlgEquiv m n R S A B) x = kroneckerTMulLinearEquiv m m n n R S A B x
参数：x : Matrix m m A otimes[R] Matrix n n B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem kroneckerTMulAlgEquiv_apply (x : Matrix m m A ⊗[R] Matrix n n B) :
    (kroneckerTMulAlgEquiv m n R S A B) x = kroneckerTMulLinearEquiv m m n n R S A B x :=
  rfl

@[simp]
/-
**Matrix.kroneckerTMulAlgEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerTMulAlgEquiv_symm_apply (x : Matrix (m × n) (m × n) (A otimes[R] 
B)) : (kroneckerTMulAlgEquiv m n R S A B).symm x = (kroneckerTMulLinearEquiv m m
 n n R S A B).symm x
参数：x : Matrix (m × n) (m × n) (A otimes[R] B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem kroneckerTMulAlgEquiv_symm_apply (x : Matrix (m × n) (m × n) (A ⊗[R] B)) :
    (kroneckerTMulAlgEquiv m n R S A B).symm x =
      (kroneckerTMulLinearEquiv m m n n R S A B).symm x :=
  rfl

section StarRing
variable [StarRing R] [StarAddMonoid A] [StarAddMonoid B] [StarModule R A] [StarModule R B]

variable (m n A B) in
/-- `Matrix.kroneckerTMul` as a ⋆-algebra equivalence, when the two arguments are tensored. -/
/-
**Matrix.kroneckerTMulStarAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：kroneckerTMulStarAlgEquiv : Matrix m m A otimes[R] Matrix n n B ≃⋆ₐ[S] Mat
rix (m × n) (m × n) (A otimes[R] B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.kroneckerTMul` as a ⋆-algebra equivalence, when the two arguments are te
nsored.
-/
def kroneckerTMulStarAlgEquiv :
    Matrix m m A ⊗[R] Matrix n n B ≃⋆ₐ[S] Matrix (m × n) (m × n) (A ⊗[R] B) :=
  .ofAlgEquiv (kroneckerTMulAlgEquiv m n R S A B)
  fun x ↦ x.induction_on (by simp)
    (by simp [star_eq_conjTranspose, conjTranspose_kroneckerTMul])
    (by simp_all)
/-
**Matrix.toAlgEquiv_kroneckerTMulStarAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`
。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} (R : Type u_5) (S : Type u_6) {A : Type u_
7} {B : Type u_8} [inst : CommSemiring R]   [inst_1 : Semiring A] [inst_2 : Semi
ring B] [inst_3 : Algebra R A] [inst_4 : Algebra R B] [inst_5 : Fintype n]   [in
st_6 : DecidableEq n] [inst_7 : CommSemiring S] [inst_8 : Algebra R S] [inst_9 :
 Algebra S A]   [inst_10 : IsScalarTower R S A] [inst_11 : Fintype m] [inst_12 :
 DecidableEq m] [inst_13 : StarRing R]   [inst_14 : StarAddMonoid A] [inst_15 : 
StarAddMonoid B] [inst_16 : StarModule R A] [inst_17 : StarModule R B],   (Matri
x.kroneckerTMulStarAlgEquiv m n R S A B).toAlgEquiv = Matrix.kroneckerTMulAlgEqu
iv m n R S A B
参数：R : Type u_5；S : Type u_6；Matrix.kroneckerTMulStarAlgEquiv m n R S A B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Matrix.instStarModule`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst 
: Star α] [inst_1 : Star β] [inst_2 : SMul α β] [StarModule α β],   StarModule α
 (Matrix n …
-/
@[simp] theorem toAlgEquiv_kroneckerTMulStarAlgEquiv :
    (kroneckerTMulStarAlgEquiv m n R S A B).toAlgEquiv =
      kroneckerTMulAlgEquiv m n R S A B := rfl
/-
**Matrix.kroneckerTMulStarAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} (R : Type u_5) (S : Type u_6) {A : Type u_
7} {B : Type u_8} [inst : CommSemiring R]   [inst_1 : Semiring A] [inst_2 : Semi
ring B] [inst_3 : Algebra R A] [inst_4 : Algebra R B] [inst_5 : Fintype n]   [in
st_6 : DecidableEq n] [inst_7 : CommSemiring S] [inst_8 : Algebra R S] [inst_9 :
 Algebra S A]   [inst_10 : IsScalarTower R S A] [inst_11 : Fintype m] [inst_12 :
 DecidableEq m] [inst_13 : StarRing R]   [inst_14 : StarAddMonoid A] [inst_15 : 
StarAddMonoid B] [inst_16 : StarModule R A] [inst_17 : StarModule R B]   (x : Te
nsorProduct R (Matrix m m A) (Matrix n n B)),   (Matrix.kroneckerTMulStarAlgEqui
v m n R S A B) x = (kroneckerTMulLinearEquiv m m n n R S A B) x
参数：R : Type u_5；S : Type u_6；x : TensorProduct R (Matrix m m A) (Matrix n n B)；M
atrix.kroneckerTMulStarAlgEquiv m n R S A B；kroneckerTMulLinearEquiv m m n n R S
 A B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Matrix.instStarModule`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst 
: Star α] [inst_1 : Star β] [inst_2 : SMul α β] [StarModule α β],   StarModule α
 (Matrix n …
-/
@[simp] theorem kroneckerTMulStarAlgEquiv_apply (x : Matrix m m A ⊗[R] Matrix n n B) :
    (kroneckerTMulStarAlgEquiv m n R S A B) x =
      kroneckerTMulLinearEquiv m m n n R S A B x :=
  rfl
/-
**Matrix.kroneckerTMulStarAlgEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`
。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} (R : Type u_5) (S : Type u_6) {A : Type u_
7} {B : Type u_8} [inst : CommSemiring R]   [inst_1 : Semiring A] [inst_2 : Semi
ring B] [inst_3 : Algebra R A] [inst_4 : Algebra R B] [inst_5 : Fintype n]   [in
st_6 : DecidableEq n] [inst_7 : CommSemiring S] [inst_8 : Algebra R S] [inst_9 :
 Algebra S A]   [inst_10 : IsScalarTower R S A] [inst_11 : Fintype m] [inst_12 :
 DecidableEq m] [inst_13 : StarRing R]   [inst_14 : StarAddMonoid A] [inst_15 : 
StarAddMonoid B] [inst_16 : StarModule R A] [inst_17 : StarModule R B]   (x : Ma
trix (m × n) (m × n) (TensorProduct R A B)),   (Matrix.kroneckerTMulStarAlgEquiv
 m n R S A B).symm x = (kroneckerTMulLinearEquiv m m n n R S A B).symm x
参数：R : Type u_5；S : Type u_6；x : Matrix (m × n) (m × n) (TensorProduct R A B)；Ma
trix.kroneckerTMulStarAlgEquiv m n R S A B；kroneckerTMulLinearEquiv m m n n R S 
A B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Matrix.instStarModule`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst 
: Star α] [inst_1 : Star β] [inst_2 : SMul α β] [StarModule α β],   StarModule α
 (Matrix n …
-/
@[simp] theorem kroneckerTMulStarAlgEquiv_symm_apply (x : Matrix (m × n) (m × n) (A ⊗[R] B)) :
    (kroneckerTMulStarAlgEquiv m n R S A B).symm x =
      (kroneckerTMulLinearEquiv m m n n R S A B).symm x :=
  rfl

end StarRing

variable (m n) in
/-- `Matrix.kronecker` as an algebra equivalence, when the two arguments are tensored. -/
/-
**Matrix.kroneckerAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：kroneckerAlgEquiv : (Matrix m m R otimes[R] Matrix n n R) ≃ₐ[R] Matrix (m 
× n) (m × n) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.kronecker` as an algebra equivalence, when the two arguments are tensore
d.
-/
def kroneckerAlgEquiv : (Matrix m m R ⊗[R] Matrix n n R) ≃ₐ[R] Matrix (m × n) (m × n) R :=
  (kroneckerTMulAlgEquiv m n R R R R).trans (Algebra.TensorProduct.lid R R).mapMatrix
/-
**Matrix.toLinearEquiv_kroneckerAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} (R : Type u_5) [inst : CommSemiring R] [in
st_1 : Fintype n] [inst_2 : DecidableEq n]   [inst_3 : Fintype m] [inst_4 : Deci
dableEq m], ↑(Matrix.kroneckerAlgEquiv m n R) = kroneckerLinearEquiv m m n n R
参数：R : Type u_5；Matrix.kroneckerAlgEquiv m n R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toLinearEquiv_kroneckerAlgEquiv :
    (kroneckerAlgEquiv m n R).toLinearEquiv = kroneckerLinearEquiv m m n n R := rfl
/-
**Matrix.kroneckerAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} (R : Type u_5) [inst : CommSemiring R] [in
st_1 : Fintype n] [inst_2 : DecidableEq n]   [inst_3 : Fintype m] [inst_4 : Deci
dableEq m] (x : TensorProduct R (Matrix m m R) (Matrix n n R)),   (Matrix.kronec
kerAlgEquiv m n R) x = (kroneckerLinearEquiv m m n n R) x
参数：R : Type u_5；x : TensorProduct R (Matrix m m R) (Matrix n n R)；Matrix.kroneck
erAlgEquiv m n R；kroneckerLinearEquiv m m n n R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem kroneckerAlgEquiv_apply (x : Matrix m m R ⊗ Matrix n n R) :
    kroneckerAlgEquiv m n R x = kroneckerLinearEquiv m m n n R x := rfl
/-
**Matrix.kroneckerAlgEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} (R : Type u_5) [inst : CommSemiring R] [in
st_1 : Fintype n] [inst_2 : DecidableEq n]   [inst_3 : Fintype m] [inst_4 : Deci
dableEq m] (x : Matrix (m × n) (m × n) R),   (Matrix.kroneckerAlgEquiv m n R).sy
mm x = (kroneckerLinearEquiv m m n n R).symm x
参数：R : Type u_5；x : Matrix (m × n) (m × n) R；Matrix.kroneckerAlgEquiv m n R；kron
eckerLinearEquiv m m n n R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem kroneckerAlgEquiv_symm_apply (x : Matrix (m × n) (m × n) R) :
    (kroneckerAlgEquiv m n R).symm x = (kroneckerLinearEquiv m m n n R).symm x := rfl

variable (m n) in
/-- `Matrix.kronecker` as a ⋆-algebra equivalence, when the two arguments are tensored. -/
/-
**Matrix.kroneckerStarAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：kroneckerStarAlgEquiv [StarRing R] : (Matrix m m R otimes[R] Matrix n n R)
 ≃⋆ₐ[R] Matrix (m × n) (m × n) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.kronecker` as a ⋆-algebra equivalence, when the two arguments are tensor
ed.
-/
def kroneckerStarAlgEquiv [StarRing R] :
    (Matrix m m R ⊗[R] Matrix n n R) ≃⋆ₐ[R] Matrix (m × n) (m × n) R :=
  .ofAlgEquiv (kroneckerAlgEquiv m n R)
  fun x ↦ x.induction_on (by simp)
    (by simp [star_eq_conjTranspose, conjTranspose_kronecker])
    (by simp_all)
/-
**Matrix.toAlgEquiv_kroneckerStarAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} (R : Type u_5) [inst : CommSemiring R] [in
st_1 : Fintype n] [inst_2 : DecidableEq n]   [inst_3 : Fintype m] [inst_4 : Deci
dableEq m] [inst_5 : StarRing R],   (Matrix.kroneckerStarAlgEquiv m n R).toAlgEq
uiv = Matrix.kroneckerAlgEquiv m n R
参数：R : Type u_5；Matrix.kroneckerStarAlgEquiv m n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.instStarModule`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst 
: Star α] [inst_1 : Star β] [inst_2 : SMul α β] [StarModule α β],   StarModule α
 (Matrix n …
-/
@[simp] theorem toAlgEquiv_kroneckerStarAlgEquiv [StarRing R] :
    (kroneckerStarAlgEquiv m n R).toAlgEquiv = kroneckerAlgEquiv m n R := rfl
/-
**Matrix.kroneckerStarAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} (R : Type u_5) [inst : CommSemiring R] [in
st_1 : Fintype n] [inst_2 : DecidableEq n]   [inst_3 : Fintype m] [inst_4 : Deci
dableEq m] [inst_5 : StarRing R]   (x : TensorProduct R (Matrix m m R) (Matrix n
 n R)),   (Matrix.kroneckerStarAlgEquiv m n R) x = (kroneckerLinearEquiv m m n n
 R) x
参数：R : Type u_5；x : TensorProduct R (Matrix m m R) (Matrix n n R)；Matrix.kroneck
erStarAlgEquiv m n R；kroneckerLinearEquiv m m n n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Matrix.instStarModule`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst 
: Star α] [inst_1 : Star β] [inst_2 : SMul α β] [StarModule α β],   StarModule α
 (Matrix n …
-/
@[simp] theorem kroneckerStarAlgEquiv_apply [StarRing R] (x : Matrix m m R ⊗ Matrix n n R) :
    kroneckerStarAlgEquiv m n R x = kroneckerLinearEquiv m m n n R x := rfl
/-
**Matrix.kroneckerStarAlgEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} (R : Type u_5) [inst : CommSemiring R] [in
st_1 : Fintype n] [inst_2 : DecidableEq n]   [inst_3 : Fintype m] [inst_4 : Deci
dableEq m] [inst_5 : StarRing R] (x : Matrix (m × n) (m × n) R),   (Matrix.krone
ckerStarAlgEquiv m n R).symm x = (kroneckerLinearEquiv m m n n R).symm x
参数：R : Type u_5；x : Matrix (m × n) (m × n) R；Matrix.kroneckerStarAlgEquiv m n R；
kroneckerLinearEquiv m m n n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Matrix.instStarModule`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst 
: Star α] [inst_1 : Star β] [inst_2 : SMul α β] [StarModule α β],   StarModule α
 (Matrix n …
-/
@[simp] theorem kroneckerStarAlgEquiv_symm_apply [StarRing R] (x : Matrix (m × n) (m × n) R) :
    (kroneckerStarAlgEquiv m n R).symm x = (kroneckerLinearEquiv m m n n R).symm x := rfl

end Matrix

