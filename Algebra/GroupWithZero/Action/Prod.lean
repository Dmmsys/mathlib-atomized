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

/--
theorem `smul_zero_mk` / 定理 `smul_zero_mk`

English:
theorem smul_zero_mk
  given: {α : Type*} [Monoid M] [AddMonoid α] [DistribMulAction M α] (a : M) (c : β)
  proof: by rw [Prod.smul_mk, smul_zero]

中文:
定理 smul_zero_mk
  条件: {α : 类型} [幺半群 M] [加法幺半群 α] [分配乘法作用 M α] (a : M) (c : β)
  证明: by rw [Prod.smul_mk, smul_zero]

Depends on / 依赖: Prod.smul_mk, smul_mk, smul_zero
-/
theorem smul_zero_mk {α : Type*} [Monoid M] [AddMonoid α] [DistribMulAction M α] (a : M) (c : β) :
    a • ((0 : α), c) = (0, a • c) := by rw [Prod.smul_mk, smul_zero]

/--
theorem `smul_mk_zero` / 定理 `smul_mk_zero`

English:
theorem smul_mk_zero
  given: {β : Type*} [Monoid M] [AddMonoid β] [DistribMulAction M β] (a : M) (b : α)
  proof: by rw [Prod.smul_mk, smul_zero]

中文:
定理 smul_mk_zero
  条件: {β : 类型} [幺半群 M] [加法幺半群 β] [分配乘法作用 M β] (a : M) (b : α)
  证明: by rw [Prod.smul_mk, smul_zero]

Depends on / 依赖: Prod.smul_mk, smul_mk, smul_zero
-/
theorem smul_mk_zero {β : Type*} [Monoid M] [AddMonoid β] [DistribMulAction M β] (a : M) (b : α) :
    a • (b, (0 : β)) = (a • b, 0) := by rw [Prod.smul_mk, smul_zero]

end

/--
Instance `smulZeroClass` / 实例 `smulZeroClass`

English:
instance smulZeroClass
  signature: {R M N : Type*} [Zero M] [Zero N] [SMulZeroClass R M] [SMulZeroClass R N]
  body: by ext <;> exact smul_zero _

中文:
实例 smulZeroClass
  签名: {R M N : 类型} [零 M] [零 N] [SMulZero类 R M] [SMulZero类 R N]
  定义体: by ext <;> exact smul_zero _

Depends on / 依赖: smul_zero
-/
instance smulZeroClass {R M N : Type*} [Zero M] [Zero N] [SMulZeroClass R M] [SMulZeroClass R N] :
    SMulZeroClass R (M × N) where smul_zero _ := by ext <;> exact smul_zero _

/--
Instance `distribSMul` / 实例 `distribSMul`

English:
instance distribSMul
  signature: {R M N : Type*} [AddZeroClass M] [AddZeroClass N] [DistribSMul R M]
  body: by ext <;> exact smul_add ..

中文:
实例 distribSMul
  签名: {R M N : 类型} [加法零类 M] [加法零类 N] [分配标量乘法 R M]
  定义体: by ext <;> exact smul_add ..

Depends on / 依赖: smul_add
-/
instance distribSMul {R M N : Type*} [AddZeroClass M] [AddZeroClass N] [DistribSMul R M]
    [DistribSMul R N] : DistribSMul R (M × N) where
  smul_add _ _ _ := by ext <;> exact smul_add ..

/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: {R : Type*} [Monoid R] [AddMonoid M] [AddMonoid N]
  body: { Prod.mulAction, Prod.distribSMul with }

中文:
实例 distribMulAction
  签名: {R : 类型} [幺半群 R] [加法幺半群 M] [加法幺半群 N]
  定义体: { Prod.mulAction, Prod.distribSMul with }

Depends on / 依赖: Prod.distribSMul, Prod.mulAction, distribSMul, mulAction
-/
instance distribMulAction {R : Type*} [Monoid R] [AddMonoid M] [AddMonoid N]
    [DistribMulAction R M] [DistribMulAction R N] : DistribMulAction R (M × N) :=
  { Prod.mulAction, Prod.distribSMul with }

/--
Instance `mulDistribMulAction` / 实例 `mulDistribMulAction`

English:
instance mulDistribMulAction
  signature: {R : Type*} [Monoid R] [Monoid M] [Monoid N]
  body: by ext <;> exact smul_mul' ..
  smul_one _ := by ext <;> exact smul_one _

中文:
实例 mulDistribMulAction
  签名: {R : 类型} [幺半群 R] [幺半群 M] [幺半群 N]
  定义体: by ext <;> exact smul_mul' ..
  smul_one _ := by ext <;> exact smul_one _

Depends on / 依赖: smul_mul, smul_one
-/
instance mulDistribMulAction {R : Type*} [Monoid R] [Monoid M] [Monoid N]
    [MulDistribMulAction R M] [MulDistribMulAction R N] : MulDistribMulAction R (M × N) where
  smul_mul _ _ _ := by ext <;> exact smul_mul' ..
  smul_one _ := by ext <;> exact smul_one _

/--
Instance `smulWithZero` / 实例 `smulWithZero`

English:
instance smulWithZero
  signature: {R : Type*} [Zero R] [Zero M] [Zero N] [SMulWithZero R M] [SMulWithZero R N]
  body: by ext <;> exact zero_smul ..

中文:
实例 smulWithZero
  签名: {R : 类型} [零 R] [零 M] [零 N] [带零标量乘法 R M] [带零标量乘法 R N]
  定义体: by ext <;> exact zero_smul ..

Depends on / 依赖: zero_smul
-/
instance smulWithZero {R : Type*} [Zero R] [Zero M] [Zero N] [SMulWithZero R M] [SMulWithZero R N] :
    SMulWithZero R (M × N) where
  zero_smul _ := by ext <;> exact zero_smul ..

/--
Instance `mulActionWithZero` / 实例 `mulActionWithZero`

English:
instance mulActionWithZero
  signature: {R : Type*} [MonoidWithZero R] [Zero M] [Zero N] [MulActionWithZero R M]
  body: { Prod.mulAction, Prod.smulWithZero with }

中文:
实例 mulActionWithZero
  签名: {R : 类型} [带零幺半群 R] [零 M] [零 N] [带零乘法作用 R M]
  定义体: { Prod.mulAction, Prod.smulWithZero with }

Depends on / 依赖: Prod.mulAction, Prod.smulWithZero, mulAction, smulWithZero
-/
instance mulActionWithZero {R : Type*} [MonoidWithZero R] [Zero M] [Zero N] [MulActionWithZero R M]
    [MulActionWithZero R N] : MulActionWithZero R (M × N) :=
  { Prod.mulAction, Prod.smulWithZero with }

end Prod

/-! ### Scalar multiplication as a homomorphism -/

section Action_by_Prod

variable (M N α) [Monoid M] [Monoid N] [AddMonoid α]

/--
Definition of `DistribMulAction.prodOfSMulCommClass` / `DistribMulAction.prodOfSMulCommClass` 的定义

English:
abbreviation DistribMulAction.prodOfSMulCommClass
  signature: [DistribMulAction M α] [DistribMulAction N α]
  body: MulAction.prodOfSMulCommClass M N α
  smul_zero mn := by change mn.1 • mn.2 • 0 = (0 : α); rw [smul_zero, smul_zero]
  smul_add mn a a' := by change mn.1 • mn.2 • _ = (_ : α); rw [smul_add, smul_add]; rfl

中文:
缩写 分配乘法作用.prodOfSMulCommClass
  签名: [分配乘法作用 M α] [分配乘法作用 N α]
  定义体: MulAction.prodOfSMulCommClass M N α
  smul_zero mn := by change mn.1 • mn.2 • 0 = (0 : α); rw [smul_zero, smul_zero]
  smul_add mn a a' := by change mn.1 • mn.2 • _ = (_ : α); rw [smul_add, smul_add]; rfl

Depends on / 依赖: MulAction, MulAction.prodOfSMulCommClass, prodOfSMulCommClass
-/
abbrev DistribMulAction.prodOfSMulCommClass [DistribMulAction M α] [DistribMulAction N α]
    [SMulCommClass M N α] : DistribMulAction (M × N) α where
  __ := MulAction.prodOfSMulCommClass M N α
  smul_zero mn := by change mn.1 • mn.2 • 0 = (0 : α); rw [smul_zero, smul_zero]
  smul_add mn a a' := by change mn.1 • mn.2 • _ = (_ : α); rw [smul_add, smul_add]; rfl

/--
Definition of `DistribMulAction.prodEquiv` / `DistribMulAction.prodEquiv` 的定义

English:
definition DistribMulAction.prodEquiv
  signature: : DistribMulAction (M × N) α ≃
  body: letI instM := DistribMulAction.compHom α (.inl M N)
    letI instN := DistribMulAction.compHom α (.inr M N)
    ⟨instM, instN, (MulAction.prodEquiv M N α inferInstance).2.2⟩
  invFun _insts :=
    letI := _insts.1; letI := _insts.2.1; have := _insts.2.2
    DistribMulAction.prodOfSMulCommClass M N α
  left_inv _ := by
    dsimp only; ext ⟨m, n⟩ a
    change (m, (1 : N)) • ((1 : M), n) • a = _
    rw [smul_smul]; rw [Prod.mk_mul_mk]; rw [mul_one]; rw [one_mul]; rfl
  right_inv := by
    rintro ⟨_, x, _⟩
    dsimp only; congr 1
    · ext m a; (conv_rhs => rw [← one_smul N a]); rfl
    congr 1
    · funext i; congr; ext m a; clear i; (conv_rhs => rw [← one_smul N a]); rfl
    · ext n a; (conv_rhs => rw [← one_smul M (SMul.smul n a)]); rfl
    · exact proof_irrel_heq ..

中文:
定义 分配乘法作用.prodEquiv
  签名: : 分配乘法作用 (M × N) α ≃
  定义体: letI instM := DistribMulAction.compHom α (.inl M N)
    letI instN := DistribMulAction.compHom α (.inr M N)
    ⟨instM, instN, (MulAction.prodEquiv M N α inferInstance).2.2⟩
  invFun _insts :=
    letI := _insts.1; letI := _insts.2.1; have := _insts.2.2
    DistribMulAction.prodOfSMulCommClass M N α
  left_inv _ := by
    dsimp only; ext ⟨m, n⟩ a
    change (m, (1 : N)) • ((1 : M), n) • a = _
    rw [smul_smul]; rw [Prod.mk_mul_mk]; rw [mul_one]; rw [one_mul]; rfl
  right_inv := by
    rintro ⟨_, x, _⟩
    dsimp only; congr 1
    · ext m a; (conv_rhs => rw [← one_smul N a]); rfl
    congr 1
    · funext i; congr; ext m a; clear i; (conv_rhs => rw [← one_smul N a]); rfl
    · ext n a; (conv_rhs => rw [← one_smul M (SMul.smul n a)]); rfl
    · exact proof_irrel_heq ..

Depends on / 依赖: DistribMulAction, DistribMulAction.compHom, DistribMulAction.prodOfSMulCommClass, MulAction, MulAction.prodEquiv, Prod.mk_mul_mk, _insts, compHom, invFun, left_inv, mk_mul_mk, mul_one, one_mul, prodEquiv, prodOfSMulCommClass, right_inv, smul_smul
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
    rw [smul_smul]; rw [Prod.mk_mul_mk]; rw [mul_one]; rw [one_mul]; rfl
  right_inv := by
    rintro ⟨_, x, _⟩
    dsimp only; congr 1
    · ext m a; (conv_rhs => rw [← one_smul N a]); rfl
    congr 1
    · funext i; congr; ext m a; clear i; (conv_rhs => rw [← one_smul N a]); rfl
    · ext n a; (conv_rhs => rw [← one_smul M (SMul.smul n a)]); rfl
    · exact proof_irrel_heq ..

end Action_by_Prod
