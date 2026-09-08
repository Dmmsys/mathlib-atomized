/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Opposite

/-!
# Module operations on `Mᵐᵒᵖ`

This file contains definitions that build on top of the group action definitions in
`Mathlib/Algebra/GroupWithZero/Action/Opposite.lean`.
-/

@[expose] public section

section

variable {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [Module S M]

@[ext high]
/-
**LinearMap.ext_ring_op** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.ext_ring_op {σ : Rᵐᵒᵖ ->+* S} {f g : R ->ₛₗ[σ] M} (h : f (1 : R)
 = g (1 : R)) : f = g
参数：h : f (1 : R) = g (1 : R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `op_smul_eq_mul`：op_smul_eq_mul {α : Type*} [Mul α] (a b : α) : MulOpposi
te.op a • b = b * a
· 使用定理 `LinearMap.map_smulₛₗ`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃
 : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst…
-/
theorem LinearMap.ext_ring_op
    {σ : Rᵐᵒᵖ →+* S} {f g : R →ₛₗ[σ] M} (h : f (1 : R) = g (1 : R)) :
    f = g :=
  ext fun x ↦ by
    rw [← one_mul x, ← op_smul_eq_mul, f.map_smulₛₗ, h, g.map_smulₛₗ]

end

namespace MulOpposite

universe u v

variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The function `op` is a linear equivalence. -/
/-
**MulOpposite.opLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：opLinearEquiv : M ≃ₗ[R] Mᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `op` is a linear equivalence.
-/
def opLinearEquiv : M ≃ₗ[R] Mᵐᵒᵖ :=
  { opAddEquiv with map_smul' := MulOpposite.op_smul }

@[simp]
/-
**MulOpposite.coe_opLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：coe_opLinearEquiv : (opLinearEquiv R : M -> Mᵐᵒᵖ) = op
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_opLinearEquiv : (opLinearEquiv R : M → Mᵐᵒᵖ) = op :=
  rfl

@[simp]
/-
**MulOpposite.coe_opLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：coe_opLinearEquiv_symm : ((opLinearEquiv R).symm : Mᵐᵒᵖ -> M) = unop
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_opLinearEquiv_symm : ((opLinearEquiv R).symm : Mᵐᵒᵖ → M) = unop :=
  rfl

@[simp]
/-
**MulOpposite.coe_opLinearEquiv_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposi
te`。
形式化陈述：coe_opLinearEquiv_toLinearMap : ((opLinearEquiv R).toLinearMap : M -> Mᵐᵒᵖ
) = op
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_opLinearEquiv_toLinearMap : ((opLinearEquiv R).toLinearMap : M → Mᵐᵒᵖ) = op :=
  rfl

@[simp]
/-
**MulOpposite.coe_opLinearEquiv_symm_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `MulO
pposite`。
形式化陈述：coe_opLinearEquiv_symm_toLinearMap : ((opLinearEquiv R).symm.toLinearMap :
 Mᵐᵒᵖ -> M) = unop
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_opLinearEquiv_symm_toLinearMap :
    ((opLinearEquiv R).symm.toLinearMap : Mᵐᵒᵖ → M) = unop :=
  rfl
/-
**MulOpposite.opLinearEquiv_toAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：opLinearEquiv_toAddEquiv : (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).toAddEquiv = o
pAddEquiv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem opLinearEquiv_toAddEquiv : (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).toAddEquiv = opAddEquiv :=
  rfl

@[simp]
/-
**MulOpposite.coe_opLinearEquiv_addEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`
。
形式化陈述：coe_opLinearEquiv_addEquiv : ((opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ) : M ≃+ Mᵐᵒᵖ
) = opAddEquiv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearEquivClass.toAddEquivClass`：∀ {F : Type u_14} {R : outParam (T
ype u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S} 
  {σ : outParam (R →+* S)}…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
theorem coe_opLinearEquiv_addEquiv : ((opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ) : M ≃+ Mᵐᵒᵖ) = opAddEquiv :=
  rfl
/-
**MulOpposite.opLinearEquiv_symm_toAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposi
te`。
形式化陈述：opLinearEquiv_symm_toAddEquiv : (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm.toAd
dEquiv = opAddEquiv.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem opLinearEquiv_symm_toAddEquiv :
    (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm.toAddEquiv = opAddEquiv.symm :=
  rfl

@[simp]
/-
**MulOpposite.coe_opLinearEquiv_symm_addEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MulOppo
site`。
形式化陈述：coe_opLinearEquiv_symm_addEquiv : ((opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm :
 Mᵐᵒᵖ ≃+ M) = opAddEquiv.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearEquivClass.toAddEquivClass`：∀ {F : Type u_14} {R : outParam (T
ype u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S} 
  {σ : outParam (R →+* S)}…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
theorem coe_opLinearEquiv_symm_addEquiv :
    ((opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm : Mᵐᵒᵖ ≃+ M) = opAddEquiv.symm :=
  rfl

end MulOpposite

