/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.GroupWithZero.Action.End

/-!
# Prod instances for multiplicative actions with zero

This file defines instances for `MulActionWithZero` and related structures on `α × β`

## See also

* `Algebra.GroupWithZero.Action.Opposite`
* `Algebra.GroupWithZero.Action.Pi`
* `Algebra.GroupWithZero.Action.Units`
-/

@[expose] public section

assert_not_exists Ring

variable {M N α β : Type*}

namespace Prod

section

variable [SMul M α] [SMul M β]

/-
**Prod.smul_zero_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：smul_zero_mk {α : Type*} [Monoid M] [AddMonoid α] [DistribMulAction M α] (
a : M) (c : β) : a • ((0 : α), c) = (0, a • c)
参数：a : M；c : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.smul_mk`：∀ {E : Type u_8} {α : Type u_9} {β : Type u_10} [inst : SM
ul E α] [inst_1 : SMul E β] (c : E) (a : α) (b : β),   c • (a, b) = (c • a, c • 
b)
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem smul_zero_mk {α : Type*} [Monoid M] [AddMonoid α] [DistribMulAction M α] (a : M) (c : β) :
    a • ((0 : α), c) = (0, a • c) := by rw [Prod.smul_mk, smul_zero]
/-
**Prod.smul_mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：smul_mk_zero {β : Type*} [Monoid M] [AddMonoid β] [DistribMulAction M β] (
a : M) (b : α) : a • (b, (0 : β)) = (a • b, 0)
参数：a : M；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.smul_mk`：∀ {E : Type u_8} {α : Type u_9} {β : Type u_10} [inst : SM
ul E α] [inst_1 : SMul E β] (c : E) (a : α) (b : β),   c • (a, b) = (c • a, c • 
b)
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem smul_mk_zero {β : Type*} [Monoid M] [AddMonoid β] [DistribMulAction M β] (a : M) (b : α) :
    a • (b, (0 : β)) = (a • b, 0) := by rw [Prod.smul_mk, smul_zero]

end

/-
**Prod.smulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：smulZeroClass {R M N : Type*} [Zero M] [Zero N] [SMulZeroClass R M] [SMulZ
eroClass R N] : SMulZeroClass R (M × N) where smul_zero _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulZeroClass {R M N : Type*} [Zero M] [Zero N] [SMulZeroClass R M] [SMulZeroClass R N] :
    SMulZeroClass R (M × N) where smul_zero _ := by ext <;> exact smul_zero _
/-
**Prod.distribSMul** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：distribSMul {R M N : Type*} [AddZeroClass M] [AddZeroClass N] [DistribSMul
 R M] [DistribSMul R N] : DistribSMul R (M × N) where smul_add _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribSMul {R M N : Type*} [AddZeroClass M] [AddZeroClass N] [DistribSMul R M]
    [DistribSMul R N] : DistribSMul R (M × N) where
  smul_add _ _ _ := by ext <;> exact smul_add ..
/-
**Prod.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：distribMulAction {R : Type*} [Monoid R] [AddMonoid M] [AddMonoid N] [Distr
ibMulAction R M] [DistribMulAction R N] : DistribMulAction R (M × N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction {R : Type*} [Monoid R] [AddMonoid M] [AddMonoid N]
    [DistribMulAction R M] [DistribMulAction R N] : DistribMulAction R (M × N) :=
  { Prod.mulAction, Prod.distribSMul with }
/-
**Prod.mulDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：mulDistribMulAction {R : Type*} [Monoid R] [Monoid M] [Monoid N] [MulDistr
ibMulAction R M] [MulDistribMulAction R N] : MulDistribMulAction R (M × N) where
 smul_mul _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulDistribMulAction {R : Type*} [Monoid R] [Monoid M] [Monoid N]
    [MulDistribMulAction R M] [MulDistribMulAction R N] : MulDistribMulAction R (M × N) where
  smul_mul _ _ _ := by ext <;> exact smul_mul' ..
  smul_one _ := by ext <;> exact smul_one _
/-
**Prod.smulWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：smulWithZero {R : Type*} [Zero R] [Zero M] [Zero N] [SMulWithZero R M] [SM
ulWithZero R N] : SMulWithZero R (M × N) where zero_smul _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulWithZero {R : Type*} [Zero R] [Zero M] [Zero N] [SMulWithZero R M] [SMulWithZero R N] :
    SMulWithZero R (M × N) where
  zero_smul _ := by ext <;> exact zero_smul ..
/-
**Prod.mulActionWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：mulActionWithZero {R : Type*} [MonoidWithZero R] [Zero M] [Zero N] [MulAct
ionWithZero R M] [MulActionWithZero R N] : MulActionWithZero R (M × N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulActionWithZero {R : Type*} [MonoidWithZero R] [Zero M] [Zero N] [MulActionWithZero R M]
    [MulActionWithZero R N] : MulActionWithZero R (M × N) :=
  { Prod.mulAction, Prod.smulWithZero with }

end Prod

/-! ### Scalar multiplication as a homomorphism -/

section Action_by_Prod

variable (M N α) [Monoid M] [Monoid N] [AddMonoid α]

/-- Construct a `DistribMulAction` by a product monoid from `DistribMulAction`s by the factors. -/
/-
**DistribMulAction.prodOfSMulCommClass** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：DistribMulAction.prodOfSMulCommClass [DistribMulAction M α] [DistribMulAct
ion N α] [SMulCommClass M N α] : DistribMulAction (M × N) α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a `DistribMulAction` by a product monoid from `DistribMulAction`s by t
he factors.
-/
abbrev DistribMulAction.prodOfSMulCommClass [DistribMulAction M α] [DistribMulAction N α]
    [SMulCommClass M N α] : DistribMulAction (M × N) α where
  __ := MulAction.prodOfSMulCommClass M N α
  smul_zero mn := by change mn.1 • mn.2 • 0 = (0 : α); rw [smul_zero, smul_zero]
  smul_add mn a a' := by change mn.1 • mn.2 • _ = (_ : α); rw [smul_add, smul_add]; rfl

/-- A `DistribMulAction` by a product monoid is equivalent to
  commuting `DistribMulAction`s by the factors. -/
/-
**DistribMulAction.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DistribMulAction.prodEquiv : DistribMulAction (M × N) α ≃ Σ' (_ : DistribM
ulAction M α) (_ : DistribMulAction N α), SMulCommClass M N α where toFun _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `DistribMulAction` by a product monoid is equivalent to
  commuting `DistribMulAction`s by the factors.
-/
def DistribMulAction.prodEquiv : DistribMulAction (M × N) α ≃
    Σ' (_ : DistribMulAction M α) (_ : DistribMulAction N α), SMulCommClass M N α where
  toFun _ :=
    letI instM := DistribMulAction.compHom α (.inl M N)
    letI instN := DistribMulAction.compHom α (.inr M N)
    ⟨instM, instN, (MulAction.prodEquiv M N α inferInstance).2.2⟩
  invFun _insts :=
    letI := _insts.1; letI := _insts.2.1; have := _insts.2.2
    DistribMulAction.prodOfSMulCommClass M N α
  left_inv _ := by
    dsimp only; ext ⟨m, n⟩ a
    change (m, (1 : N)) • ((1 : M), n) • a = _
    rw [smul_smul, Prod.mk_mul_mk, mul_one, one_mul]; rfl
  right_inv := by
    rintro ⟨_, x, _⟩
    dsimp only; congr 1
    · ext m a; (conv_rhs => rw [← one_smul N a]); rfl
    congr 1
    · funext i; congr; ext m a; clear i; (conv_rhs => rw [← one_smul N a]); rfl
    · ext n a; (conv_rhs => rw [← one_smul M (SMul.smul n a)]); rfl
    · exact proof_irrel_heq ..

end Action_by_Prod

