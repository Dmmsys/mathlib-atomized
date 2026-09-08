/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Restriction of scalars for continuous linear maps

In this file, we define and study `ContinuousLinearMap.restrictScalars`, which reinterprets
a continuous `R`-linear map as a continuous `S`-linear map, for suitable `R` and `S`.
This is the continuous version of `LinearMap.restrictScalars`.
-/

@[expose] public section

section RestrictScalars

namespace ContinuousLinearMap

section Semiring

variable {A M₁ M₂ R S : Type*} [Semiring A] [Semiring R] [Semiring S]
  [AddCommMonoid M₁] [Module A M₁] [Module R M₁] [TopologicalSpace M₁]
  [AddCommMonoid M₂] [Module A M₂] [Module R M₂] [TopologicalSpace M₂]
  [LinearMap.CompatibleSMul M₁ M₂ R A]

variable (R) in
/-- If `A` is an `R`-algebra, then a continuous `A`-linear map can be interpreted as a continuous
`R`-linear map. We assume `LinearMap.CompatibleSMul M₁ M₂ R A` to match assumptions of
`LinearMap.map_smul_of_tower`. -/
/-
**ContinuousLinearMap.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：restrictScalars (f : M₁ ->L[A] M₂) : M₁ ->L[R] M₂
参数：f : M₁ ->L[A] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is an `R`-algebra, then a continuous `A`-linear map can be interpreted as
 a continuous
`R`-linear map. We assume `LinearMap.CompatibleSMul M₁ M₂ R A` to match assumpti
ons of
`LinearMap.map_smul_of_tower`.
-/
def restrictScalars (f : M₁ →L[A] M₂) : M₁ →L[R] M₂ :=
  ⟨(f : M₁ →ₗ[A] M₂).restrictScalars R, f.continuous⟩

@[simp]
/-
**ContinuousLinearMap.coe_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：coe_restrictScalars (f : M₁ ->L[A] M₂) : (f.restrictScalars R : M₁ ->ₗ[R] 
M₂) = (f : M₁ ->ₗ[A] M₂).restrictScalars R
参数：f : M₁ ->L[A] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalars (f : M₁ →L[A] M₂) :
    (f.restrictScalars R : M₁ →ₗ[R] M₂) = (f : M₁ →ₗ[A] M₂).restrictScalars R := rfl

@[simp]
/-
**ContinuousLinearMap.coe_restrictScalars'** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：coe_restrictScalars' (f : M₁ ->L[A] M₂) : ⇑(f.restrictScalars R) = f
参数：f : M₁ ->L[A] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalars' (f : M₁ →L[A] M₂) : ⇑(f.restrictScalars R) = f := rfl

@[simp]
/-
**ContinuousLinearMap.toContinuousAddMonoidHom_restrictScalars** 是 Mathlib 中的一个定
理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：toContinuousAddMonoidHom_restrictScalars (f : M₁ ->L[A] M₂) : ↑(f.restrict
Scalars R) = (f : ContinuousAddMonoidHom M₁ M₂)
参数：f : M₁ ->L[A] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem toContinuousAddMonoidHom_restrictScalars (f : M₁ →L[A] M₂) :
    ↑(f.restrictScalars R) = (f : ContinuousAddMonoidHom M₁ M₂) := rfl
/-
**ContinuousLinearMap.restrictScalars_zero** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：∀ {A : Type u_1} {M₁ : Type u_2} {M₂ : Type u_3} {R : Type u_4} [inst : Se
miring A] [inst_1 : Semiring R]   [inst_2 : AddCommMonoid M₁] [inst_3 : _root_.M
odule A M₁] [inst_4 : _root_.Module R M₁] [inst_5 : TopologicalSpace M₁]   [inst
_6 : AddCommMonoid M₂] [inst_7 : _root_.Module A M₂] [inst_8 : _root_.Module R M
₂] [inst_9 : TopologicalSpace M₂]   [inst_10 : LinearMap.CompatibleSMul M₁ M₂ R 
A], ContinuousLinearMap.restrictScalars R 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma restrictScalars_zero : (0 : M₁ →L[A] M₂).restrictScalars R = 0 := rfl

@[simp]
/-
**ContinuousLinearMap.restrictScalars_add** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：restrictScalars_add [ContinuousAdd M₂] (f g : M₁ ->L[A] M₂) : (f + g).rest
rictScalars R = f.restrictScalars R + g.restrictScalars R
参数：f g : M₁ ->L[A] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_add [ContinuousAdd M₂] (f g : M₁ →L[A] M₂) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R := rfl

variable [Module S M₂] [ContinuousConstSMul S M₂] [SMulCommClass A S M₂] [SMulCommClass R S M₂]

@[simp]
/-
**ContinuousLinearMap.restrictScalars_smul** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：restrictScalars_smul (c : S) (f : M₁ ->L[A] M₂) : (c • f).restrictScalars 
R = c • f.restrictScalars R
参数：c : S；f : M₁ ->L[A] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars_smul (c : S) (f : M₁ →L[A] M₂) :
    (c • f).restrictScalars R = c • f.restrictScalars R :=
  rfl

variable [ContinuousAdd M₂]

variable (A R S M₁ M₂) in
/-- `ContinuousLinearMap.restrictScalars` as a `LinearMap`. See also
`ContinuousLinearMap.restrictScalarsL`. -/
/-
**ContinuousLinearMap.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：restrictScalars (f : M₁ ->L[A] M₂) : M₁ ->L[R] M₂
参数：f : M₁ ->L[A] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.restrictScalars` as a `LinearMap`. See also
`ContinuousLinearMap.restrictScalarsL`.
-/
def restrictScalarsₗ : (M₁ →L[A] M₂) →ₗ[S] M₁ →L[R] M₂ where
  toFun := restrictScalars R
  map_add' := restrictScalars_add
  map_smul' := restrictScalars_smul

@[simp]
/-
**ContinuousLinearMap.coe_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：coe_restrictScalars (f : M₁ ->L[A] M₂) : (f.restrictScalars R : M₁ ->ₗ[R] 
M₂) = (f : M₁ ->ₗ[A] M₂).restrictScalars R
参数：f : M₁ ->L[A] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalarsₗ : ⇑(restrictScalarsₗ A M₁ M₂ R S) = restrictScalars R := rfl

end Semiring

section Ring
variable {A R S M₁ M₂ : Type*} [Ring A] [Ring R] [Ring S]
  [AddCommGroup M₁] [Module A M₁] [Module R M₁] [TopologicalSpace M₁]
  [AddCommGroup M₂] [Module A M₂] [Module R M₂] [TopologicalSpace M₂]
  [LinearMap.CompatibleSMul M₁ M₂ R A] [IsTopologicalAddGroup M₂]

@[simp]
/-
**ContinuousLinearMap.restrictScalars_sub** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：restrictScalars_sub (f g : M₁ ->L[A] M₂) : (f - g).restrictScalars R = f.r
estrictScalars R - g.restrictScalars R
参数：f g : M₁ ->L[A] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_sub (f g : M₁ →L[A] M₂) :
    (f - g).restrictScalars R = f.restrictScalars R - g.restrictScalars R := rfl

@[simp]
/-
**ContinuousLinearMap.restrictScalars_neg** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：restrictScalars_neg (f : M₁ ->L[A] M₂) : (-f).restrictScalars R = -f.restr
ictScalars R
参数：f : M₁ ->L[A] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_neg (f : M₁ →L[A] M₂) : (-f).restrictScalars R = -f.restrictScalars R := rfl

end Ring

end ContinuousLinearMap

end RestrictScalars

