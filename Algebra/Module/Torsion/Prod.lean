/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Torsion.Free

/-!
# Product of torsion-free modules

This file shows that the product of two torsion-free modules is torsion-free.
-/

public section

open Module

variable {R M N : Type*}

namespace Prod

/-
**Prod.moduleIsTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：moduleIsTorsionFree [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Modu
le R M] [Module R N] [IsTorsionFree R M] [IsTorsionFree R N] : IsTorsionFree R (
M × N) where isSMulRegular _r hr
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_
3} {δ : Type u_4} {f : α → γ} {g : β → δ},   Function.Injective f → Function.Inj
ective g → Funct…
· 使用定理 `IsRegular.isSMulRegular`：∀ {R : Type u_1} {M : Type u_3} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Is
TorsionFree R…
-/
instance moduleIsTorsionFree [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [IsTorsionFree R M] [IsTorsionFree R N] :
    IsTorsionFree R (M × N) where
  isSMulRegular _r hr := hr.isSMulRegular.prodMap hr.isSMulRegular

end Prod

