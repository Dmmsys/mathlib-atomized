/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Reinterpret an additive homomorphism as a `ℚ`-linear map.
-/

@[expose] public section

open Function

variable {M M₂ : Type*}

/-- Reinterpret an additive homomorphism as a `ℚ`-linear map. -/
/-
**AddMonoidHom.toRatLinearMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonoidHom.toRatLinearMap [AddCommGroup M] [Module Rat M] [AddCommGroup 
M₂] [Module Rat M₂] (f : M ->+ M₂) : M ->ₗ[Rat] M₂
参数：f : M ->+ M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an additive homomorphism as a `ℚ`-linear map.
-/
def AddMonoidHom.toRatLinearMap [AddCommGroup M] [Module ℚ M] [AddCommGroup M₂] [Module ℚ M₂]
    (f : M →+ M₂) : M →ₗ[ℚ] M₂ :=
  { f with map_smul' := map_rat_smul f }
/-
**AddMonoidHom.toRatLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidHom.toRatLinearMap_injective [AddCommGroup M] [Module Rat M] [Add
CommGroup M₂] [Module Rat M₂] : Function.Injective (@AddMonoidHom.toRatLinearMap
 M M₂ _ _ _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem AddMonoidHom.toRatLinearMap_injective [AddCommGroup M] [Module ℚ M] [AddCommGroup M₂]
    [Module ℚ M₂] : Function.Injective (@AddMonoidHom.toRatLinearMap M M₂ _ _ _ _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

@[simp]
/-
**AddMonoidHom.coe_toRatLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidHom.coe_toRatLinearMap [AddCommGroup M] [Module Rat M] [AddCommGr
oup M₂] [Module Rat M₂] (f : M ->+ M₂) : ⇑f.toRatLinearMap = f
参数：f : M ->+ M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddMonoidHom.coe_toRatLinearMap [AddCommGroup M] [Module ℚ M] [AddCommGroup M₂]
    [Module ℚ M₂] (f : M →+ M₂) : ⇑f.toRatLinearMap = f :=
  rfl
