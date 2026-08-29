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

/--
Definition of `instModuleTensorProductMop` / `instModuleTensorProductMop` 的定义

English:
abbreviation instModuleTensorProductMop
  signature: : Module (A otimes[R] Aᵐᵒᵖ) A
  body: TensorProduct.Algebra.module

中文:
缩写 instModuleTensorProductMop
  签名: : 模 (A otimes[R] Aᵐᵒᵖ) A
  定义体: TensorProduct.Algebra.module

Depends on / 依赖: Algebra, TensorProduct, TensorProduct.Algebra.module, module
-/
abbrev instModuleTensorProductMop : Module (A otimes[R] Aᵐᵒᵖ) A := TensorProduct.Algebra.module

/--
Definition of `AlgHom.mulLeftRight` / `AlgHom.mulLeftRight` 的定义

English:
definition AlgHom.mulLeftRight
  signature: : (A otimes[R] Aᵐᵒᵖ) ->ₐ[R] Module.End R A
  body: letI : Module (A otimes[R] Aᵐᵒᵖ) A := TensorProduct.Algebra.module
  letI : IsScalarTower R (A otimes[R] Aᵐᵒᵖ) A := {
    smul_assoc := fun r ab a => by
      change TensorProduct.Algebra.moduleAux _ _ = _ • TensorProduct.Algebra.moduleAux _ _
      simp }
  Algebra.lsmul R (A := A otimes[R] Aᵐᵒᵖ) R

中文:
定义 代数态射.mulLeftRight
  签名: : (A otimes[R] Aᵐᵒᵖ) ->ₐ[R] 模.End R A
  定义体: letI : Module (A otimes[R] Aᵐᵒᵖ) A := TensorProduct.Algebra.module
  letI : IsScalarTower R (A otimes[R] Aᵐᵒᵖ) A := {
    smul_assoc := fun r ab a => by
      change TensorProduct.Algebra.moduleAux _ _ = _ • TensorProduct.Algebra.moduleAux _ _
      simp }
  Algebra.lsmul R (A := A otimes[R] Aᵐᵒᵖ) R

Depends on / 依赖: Algebra, Algebra.lsmul, IsScalarTower, Module, TensorProduct, TensorProduct.Algebra.module, TensorProduct.Algebra.moduleAux, module, moduleAux, otimes, smul_assoc
-/
def AlgHom.mulLeftRight : (A otimes[R] Aᵐᵒᵖ) ->ₐ[R] Module.End R A :=
  letI : Module (A otimes[R] Aᵐᵒᵖ) A := TensorProduct.Algebra.module
  letI : IsScalarTower R (A otimes[R] Aᵐᵒᵖ) A := {
    smul_assoc := fun r ab a => by
      change TensorProduct.Algebra.moduleAux _ _ = _ • TensorProduct.Algebra.moduleAux _ _
      simp }
  Algebra.lsmul R (A := A otimes[R] Aᵐᵒᵖ) R A

@[simp]
/--
lemma `AlgHom.mulLeftRight_apply` / 引理 `AlgHom.mulLeftRight_apply`

English:
lemma AlgHom.mulLeftRight_apply
  given: (a : A) (b : Aᵐᵒᵖ) (x : A)
  proof: by
  simp only [AlgHom.mulLeftRight, Algebra.lsmul_coe]
  change TensorProduct.Algebra.moduleAux _ _ = _
  simp [TensorProduct.Algebra.moduleAux, ← mul_assoc]

中文:
引理 代数态射.mulLeftRight_apply
  条件: (a : A) (b : Aᵐᵒᵖ) (x : A)
  证明: by
  simp only [AlgHom.mulLeftRight, Algebra.lsmul_coe]
  change TensorProduct.Algebra.moduleAux _ _ = _
  simp [TensorProduct.Algebra.moduleAux, ← mul_assoc]

Depends on / 依赖: AlgHom, AlgHom.mulLeftRight, Algebra, Algebra.lsmul_coe, TensorProduct, TensorProduct.Algebra.moduleAux, lsmul_coe, moduleAux, mulLeftRight, mul_assoc
-/
lemma AlgHom.mulLeftRight_apply (a : A) (b : Aᵐᵒᵖ) (x : A) :
    AlgHom.mulLeftRight R A (a otimesₜ b) x = a * x * b.unop := by
  simp only [AlgHom.mulLeftRight, Algebra.lsmul_coe]
  change TensorProduct.Algebra.moduleAux _ _ = _
  simp [TensorProduct.Algebra.moduleAux, ← mul_assoc]

/--
Definition of `IsAzumaya` / `IsAzumaya` 的定义

English:
class IsAzumaya
  parameters: : Prop extends Module.Projective R A, FaithfulSMul R A, Module.Finite R A where
  extends: Module.Projective R A, FaithfulSMul R A, Module.Finite R A
  axioms and operations (1):
    - bij : Function.Bijective AlgHom.mulLeftRight R A

中文:
类 是Azumaya
  参数: : 命题 extends 模.投射 R A, 忠实标量乘法 R A, 模.有限 R A where
  继承: 模.投射 R A, 忠实标量乘法 R A, 模.有限 R A
  公理与运算 (1 个):
    - bij : 函数.双射 代数态射.mulLeftRight R A
-/
class IsAzumaya : Prop extends Module.Projective R A, FaithfulSMul R A, Module.Finite R A where
bij : Function.Bijective AlgHom.mulLeftRight R A
