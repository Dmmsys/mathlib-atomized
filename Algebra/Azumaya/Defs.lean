/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Azumaya Algebras

An Azumaya algebra over a commutative ring `R` is a finitely generated, projective
and faithful R-algebra where the tensor product `A ⊗[R] Aᵐᵒᵖ` is isomorphic to the
`R`-endomorphisms of A via the map `f : a ⊗ b ↦ (x ↦ a * x * b.unop)`.
TODO : Add the three more definitions and prove they are equivalent:
· There exists an `R`-algebra `B` such that `B ⊗[R] A` is Morita equivalent to `R`;
· `Aᵐᵒᵖ ⊗[R] A` is Morita equivalent to `R`;
· The center of `A` is `R` and `A` is a separable algebra.

## Reference

* [Benson Farb, R. Keith Dennis, *Noncommutative Algebra*][bensonfarb1993]

## Tags

Azumaya algebra, central simple algebra, noncommutative algebra
-/

@[expose] public section

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

open TensorProduct MulOpposite

/-- `A` as a `A ⊗[R] Aᵐᵒᵖ`-module (or equivalently, an `A`-`A` bimodule). -/
/-
**instModuleTensorProductMop** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：instModuleTensorProductMop : Module (A otimes[R] Aᵐᵒᵖ) A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
`A` as a `A ⊗[R] Aᵐᵒᵖ`-module (or equivalently, an `A`-`A` bimodule).
-/
abbrev instModuleTensorProductMop : Module (A ⊗[R] Aᵐᵒᵖ) A := TensorProduct.Algebra.module

/-- The canonical map from `A ⊗[R] Aᵐᵒᵖ` to `Module.End R A` where
  `a ⊗ b` maps to `f : x ↦ a * x * b`. -/
/-
**AlgHom.mulLeftRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgHom.mulLeftRight : (A otimes[R] Aᵐᵒᵖ) ->ₐ[R] Module.End R A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
The canonical map from `A ⊗[R] Aᵐᵒᵖ` to `Module.End R A` where
  `a ⊗ b` maps to `f : x ↦ a * x * b`.
-/
def AlgHom.mulLeftRight : (A ⊗[R] Aᵐᵒᵖ) →ₐ[R] Module.End R A :=
  letI : Module (A ⊗[R] Aᵐᵒᵖ) A := TensorProduct.Algebra.module
  letI : IsScalarTower R (A ⊗[R] Aᵐᵒᵖ) A := {
    smul_assoc := fun r ab a ↦ by
      change TensorProduct.Algebra.moduleAux _ _ = _ • TensorProduct.Algebra.moduleAux _ _
      simp }
  Algebra.lsmul R (A := A ⊗[R] Aᵐᵒᵖ) R A

@[simp]
/-
**AlgHom.mulLeftRight_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgHom.mulLeftRight_apply (a : A) (b : Aᵐᵒᵖ) (x : A) : AlgHom.mulLeftRight
 R A (a otimesₜ b) x = a * x * b.unop
参数：a : A；b : Aᵐᵒᵖ；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma AlgHom.mulLeftRight_apply (a : A) (b : Aᵐᵒᵖ) (x : A) :
    AlgHom.mulLeftRight R A (a ⊗ₜ b) x = a * x * b.unop := by
  simp only [AlgHom.mulLeftRight, Algebra.lsmul_coe]
  change TensorProduct.Algebra.moduleAux _ _ = _
  simp [TensorProduct.Algebra.moduleAux, ← mul_assoc]

/-- An Azumaya algebra is a finitely generated, projective and faithful R-algebra where
  `AlgHom.mulLeftRight R A : (A ⊗[R] Aᵐᵒᵖ) →ₐ[R] Module.End R A` is an isomorphism. -/
/-
**IsAzumaya** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → (A : Type u_2) → [inst : CommSemiring R] → [inst_1 : Semi
ring A] → [Algebra R A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An Azumaya algebra is a finitely generated, projective and faithful R-algebra wh
ere
  `AlgHom.mulLeftRight R A : (A ⊗[R] Aᵐᵒᵖ) →ₐ[R] Module.End R A` is an isomorphi
sm.
-/
class IsAzumaya : Prop extends Module.Projective R A, FaithfulSMul R A, Module.Finite R A where
    bij : Function.Bijective <| AlgHom.mulLeftRight R A
