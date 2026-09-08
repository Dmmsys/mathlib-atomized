/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Coalgebra.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bialgebra structure on quotients

If `I` is a two-sided ideal of an `R`-bialgebra `A` whose underlying `R`-submodule is a
coideal, then the quotient `A ⧸ I` inherits a bialgebra structure.

## Main definitions

* `Bialgebra.Quotient.counitAlgHom` : the counit on `A ⧸ I`, as an `R`-algebra homomorphism.
* `Bialgebra.Quotient.comulAlgHom` : comultiplication on `A ⧸ I` as an `R`-algebra homomorphism.
* `Bialgebra.Quotient.mkBialgHom` : `Ideal.Quotient.mkₐ` as a bialgebra homomorphism.

## Main results

* `Bialgebra R (A ⧸ I)` instance when `[I.IsTwoSided]` and `[(I.restrictScalars R).IsCoideal]`.
-/

@[expose] public section

open Bialgebra Coalgebra LinearMap TensorProduct

variable {R A : Type*} [CommRing R] [Ring A] [Bialgebra R A]
variable (I : Ideal A) [I.IsTwoSided] [(I.restrictScalars R).IsCoideal]

namespace Bialgebra.Quotient

/-- The counit on `A ⧸ I`, as an `R`-algebra homomorphism. -/
/-
**Bialgebra.Quotient.counitAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra.Quotient`
。
形式化陈述：counitAlgHom : (A ⧸ I) ->ₐ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit on `A ⧸ I`, as an `R`-algebra homomorphism.
-/
def counitAlgHom : (A ⧸ I) →ₐ[R] R :=
  Ideal.Quotient.liftₐ I (Bialgebra.counitAlgHom R A)
    (Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars R))

/-- The comultiplication on `A ⧸ I`, as an `R`-algebra homomorphism. -/
/-
**Bialgebra.Quotient.comulAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra.Quotient`。
形式化陈述：comulAlgHom : (A ⧸ I) ->ₐ[R] (A ⧸ I) otimes[R] (A ⧸ I)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comultiplication on `A ⧸ I`, as an `R`-algebra homomorphism.
-/
def comulAlgHom : (A ⧸ I) →ₐ[R] (A ⧸ I) ⊗[R] (A ⧸ I) :=
  Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (Bialgebra.comulAlgHom R A))
    (Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := I.restrictScalars R))
/-
**Bialgebra.Quotient.counit_comp_mk** 是 Mathlib 中的一个引理，位于命名空间 `Bialgebra.Quotien
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma counit_comp_mkₐ :
    (counitAlgHom I).toLinearMap ∘ₗ (Ideal.Quotient.mkₐ R I).toLinearMap = counit := rfl
/-
**Bialgebra.Quotient.comul_comp_mk** 是 Mathlib 中的一个引理，位于命名空间 `Bialgebra.Quotient
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comul_comp_mkₐ :
    (comulAlgHom (R := R) I).toLinearMap ∘ₗ (Ideal.Quotient.mkₐ R I).toLinearMap =
      map (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ comul := rfl

/-- The bialgebra structure on `A ⧸ I` when `I` is a biideal. -/
/-
**Bialgebra.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Bialgebra.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bialgebra structure on `A ⧸ I` when `I` is a biideal.
-/
instance : Bialgebra R (A ⧸ I) := by
  refine .ofAlgHom (comulAlgHom I) (counitAlgHom I) ?_ ?_ ?_ <;>
    refine Ideal.Quotient.algHom_ext R (AlgHom.toLinearMap_injective ?_) <;>
    simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      comul_comp_mkₐ, counit_comp_mkₐ]
  · simp [coassoc_simps]
  · rw [CoassocSimps.map_counit_comp_comul_left]; rfl
  · rw [CoassocSimps.map_counit_comp_comul_right]; rfl
/-
**Bialgebra.Quotient.counit_mk** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.Quotient`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : Ring A] [ins
t_2 : Bialgebra R A] (I : Ideal A)   [inst_3 : I.IsTwoSided] [inst_4 : (Submodul
e.restrictScalars R I).IsCoideal] (a : A),   CoalgebraStruct.counit ((Ideal.Quot
ient.mk I) a) = CoalgebraStruct.counit a
参数：I : Ideal A；Submodule.restrictScalars R I；a : A；(Ideal.Quotient.mk I) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
@[simp] lemma counit_mk (a : A) :
    counit (R := R) (Ideal.Quotient.mk I a) = counit a := rfl
/-
**Bialgebra.Quotient.comul_mk** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.Quotient`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : Ring A] [ins
t_2 : Bialgebra R A] (I : Ideal A)   [inst_3 : I.IsTwoSided] [inst_4 : (Submodul
e.restrictScalars R I).IsCoideal] (a : A),   CoalgebraStruct.comul ((Ideal.Quoti
ent.mk I) a) =     (TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap (Idea
l.Quotient.mkₐ R I).toLinearMap)       (CoalgebraStruct.comul a)
参数：I : Ideal A；Submodule.restrictScalars R I；a : A；(Ideal.Quotient.mk I) a；Tenso
rProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ R I).toLin
earMap；CoalgebraStruct.comul a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
@[simp] lemma comul_mk (a : A) :
    comul (R := R) (Ideal.Quotient.mk I a) =
      map (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap (comul a) :=
  rfl

/-- `Ideal.Quotient.mkₐ` as a bialgebra homomorphism. -/
/-
**Bialgebra.Quotient.mkBialgHom** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra.Quotient`。
形式化陈述：mkBialgHom : A ->ₐc[R] A ⧸ I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ideal.Quotient.mkₐ` as a bialgebra homomorphism.
-/
def mkBialgHom : A →ₐc[R] A ⧸ I := .ofAlgHom (Ideal.Quotient.mkₐ R I) rfl rfl
/-
**Bialgebra.Quotient.mkBialgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.Quoti
ent`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : Ring A] [ins
t_2 : Bialgebra R A] (I : Ideal A)   [inst_3 : I.IsTwoSided] [inst_4 : (Submodul
e.restrictScalars R I).IsCoideal] (a : A),   (Bialgebra.Quotient.mkBialgHom I) a
 = (Ideal.Quotient.mk I) a
参数：I : Ideal A；Submodule.restrictScalars R I；a : A；Bialgebra.Quotient.mkBialgHom
 I；Ideal.Quotient.mk I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
@[simp] lemma mkBialgHom_apply (a : A) :
    mkBialgHom (R := R) I a = Ideal.Quotient.mk I a := rfl

end Bialgebra.Quotient

