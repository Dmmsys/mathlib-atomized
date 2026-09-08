/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.GroupWithZero.ULift
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.ULift

/-!
# `ULift` instances for module and multiplicative actions

This file defines instances for `Module`, `MulAction` and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ULift.moduleEquiv : ULift M ≃ₗ[R] M`.
-/

@[expose] public section


namespace ULift

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}

@[to_additive]
/-
**ULift.smulLeft** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：smulLeft [SMul R M] : SMul (ULift R) M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulLeft [SMul R M] : SMul (ULift R) M :=
  ⟨fun s x => s.down • x⟩

@[to_additive (attr := simp)]
/-
**ULift.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：smul_def [SMul R M] (s : ULift R) (x : M) : s • x = s.down • x
参数：s : ULift R；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def [SMul R M] (s : ULift R) (x : M) : s • x = s.down • x :=
  rfl
/-
**ULift.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：isScalarTower [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] : IsS
calarTower (ULift R) M N
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower (ULift R) M N :=
  ⟨fun x y z => show (x.down • y) • z = x.down • y • z from smul_assoc _ _ _⟩
/-
**ULift.isScalarTower'** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：isScalarTower' [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] : Is
ScalarTower R (ULift M) N
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower' [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower R (ULift M) N :=
  ⟨fun x y z => show (x • y.down) • z = x • y.down • z from smul_assoc _ _ _⟩
/-
**ULift.isScalarTower''** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：isScalarTower'' [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] : I
sScalarTower R M (ULift N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower'' [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower R M (ULift N) :=
  ⟨fun x y z => show up ((x • y) • z.down) = ⟨x • y • z.down⟩ by rw [smul_assoc]⟩
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R M] [SMul Rᵐᵒᵖ M] [IsCentralScalar R M] : IsCentralScalar R (ULift M) :=
  ⟨fun r m => congr_arg up <| op_smul_eq_smul r m.down⟩

@[to_additive]
/-
**ULift.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：mulAction [Monoid R] [MulAction R M] : MulAction (ULift R) M where mul_smu
l _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
instance mulAction [Monoid R] [MulAction R M] : MulAction (ULift R) M where
  mul_smul _ _ := mul_smul _ _
  one_smul := one_smul _

@[to_additive]
/-
**ULift.mulAction'** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：mulAction' [Monoid R] [MulAction R M] : MulAction R (ULift M) where mul_sm
ul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction' [Monoid R] [MulAction R M] : MulAction R (ULift M) where
  mul_smul := fun _ _ _ => congr_arg ULift.up <| mul_smul _ _ _
  one_smul := fun _ => congr_arg ULift.up <| one_smul _ _
/-
**ULift.smulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：smulZeroClass [Zero M] [SMulZeroClass R M] : SMulZeroClass (ULift R) M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulZeroClass [Zero M] [SMulZeroClass R M] : SMulZeroClass (ULift R) M :=
  { ULift.smulLeft with smul_zero := fun _ => smul_zero _ }
/-
**ULift.smulZeroClass'** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：smulZeroClass' [Zero M] [SMulZeroClass R M] : SMulZeroClass R (ULift M) wh
ere smul_zero c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulZeroClass' [Zero M] [SMulZeroClass R M] : SMulZeroClass R (ULift M) where
  smul_zero c := by { ext; simp [smul_zero] }
/-
**ULift.distribSMul** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：distribSMul [AddZeroClass M] [DistribSMul R M] : DistribSMul (ULift R) M w
here smul_add _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribSMul [AddZeroClass M] [DistribSMul R M] : DistribSMul (ULift R) M where
  smul_add _ := smul_add _
/-
**ULift.distribSMul'** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：distribSMul' [AddZeroClass M] [DistribSMul R M] : DistribSMul R (ULift M) 
where smul_add c f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribSMul' [AddZeroClass M] [DistribSMul R M] : DistribSMul R (ULift M) where
  smul_add c f g := by
    ext
    simp [smul_add]
/-
**ULift.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：distribMulAction [Monoid R] [AddMonoid M] [DistribMulAction R M] : Distrib
MulAction (ULift R) M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction (ULift R) M :=
  { ULift.mulAction, ULift.distribSMul with }
/-
**ULift.distribMulAction'** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：distribMulAction' [Monoid R] [AddMonoid M] [DistribMulAction R M] : Distri
bMulAction R (ULift M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction' [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction R (ULift M) :=
  { ULift.mulAction', ULift.distribSMul' with }
/-
**ULift.mulDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：mulDistribMulAction [Monoid R] [Monoid M] [MulDistribMulAction R M] : MulD
istribMulAction (ULift R) M where smul_one _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulDistribMulAction [Monoid R] [Monoid M] [MulDistribMulAction R M] :
    MulDistribMulAction (ULift R) M where
  smul_one _ := smul_one _
  smul_mul _ := smul_mul' _
/-
**ULift.mulDistribMulAction'** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：mulDistribMulAction' [Monoid R] [Monoid M] [MulDistribMulAction R M] : Mul
DistribMulAction R (ULift M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulDistribMulAction' [Monoid R] [Monoid M] [MulDistribMulAction R M] :
    MulDistribMulAction R (ULift M) :=
  { ULift.mulAction' with
    smul_one := fun _ => by
      ext
      simp [smul_one]
    smul_mul := fun _ _ _ => by
      ext
      simp [smul_mul'] }
/-
**ULift.smulWithZero** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：smulWithZero [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero (ULift R)
 M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
instance smulWithZero [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero (ULift R) M :=
  { ULift.smulLeft with
    smul_zero := fun _ => smul_zero _
    zero_smul := zero_smul _ }
/-
**ULift.smulWithZero'** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：smulWithZero' [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero R (ULift
 M) where smul_zero _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulWithZero' [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero R (ULift M) where
  smul_zero _ := ULift.ext _ _ <| smul_zero _
  zero_smul _ := ULift.ext _ _ <| zero_smul _ _
/-
**ULift.mulActionWithZero** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：mulActionWithZero [MonoidWithZero R] [Zero M] [MulActionWithZero R M] : Mu
lActionWithZero (ULift R) M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulActionWithZero [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    MulActionWithZero (ULift R) M :=
  { ULift.smulWithZero with
    one_smul := one_smul _
    mul_smul := mul_smul }
/-
**ULift.mulActionWithZero'** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：mulActionWithZero' [MonoidWithZero R] [Zero M] [MulActionWithZero R M] : M
ulActionWithZero R (ULift M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulActionWithZero' [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    MulActionWithZero R (ULift M) :=
  { ULift.smulWithZero' with
    one_smul := one_smul _
    mul_smul := mul_smul }
/-
**ULift.module** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：module [Semiring R] [AddCommMonoid M] [Module R M] : Module (ULift R) M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module [Semiring R] [AddCommMonoid M] [Module R M] : Module (ULift R) M :=
  { ULift.smulWithZero with
    add_smul := fun _ _ => add_smul _ _
    smul_add := smul_add
    one_smul := one_smul _
    mul_smul := mul_smul }
/-
**ULift.module'** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：module' [Semiring R] [AddCommMonoid M] [Module R M] : Module R (ULift M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module' [Semiring R] [AddCommMonoid M] [Module R M] : Module R (ULift M) :=
  { ULift.smulWithZero' with
    add_smul := fun _ _ _ => ULift.ext _ _ <| add_smul _ _ _
    one_smul := one_smul _
    mul_smul := mul_smul
    smul_add := smul_add }

/-- The `R`-linear equivalence between `ULift M` and `M`.

This is a linear version of `AddEquiv.ulift`. -/
@[simps apply symm_apply]
/-
**ULift.moduleEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：moduleEquiv [Semiring R] [AddCommMonoid M] [Module R M] : ULift.{w} M ≃ₗ[R
] M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-linear equivalence between `ULift M` and `M`.

This is a linear version of `AddEquiv.ulift`.
-/
def moduleEquiv [Semiring R] [AddCommMonoid M] [Module R M] : ULift.{w} M ≃ₗ[R] M where
  toFun := ULift.down
  invFun := ULift.up
  map_smul' _ _ := rfl
  __ := AddEquiv.ulift

end ULift

