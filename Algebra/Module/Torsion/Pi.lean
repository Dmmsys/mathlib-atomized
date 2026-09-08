/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Module.Pi

/-!
# Product of torsion-free modules

This file shows that the product of torsion-free modules is torsion-free.
-/

public section

open Module

variable {ι R : Type*} {M : ι → Type*}

namespace Pi

/-
**Pi.instModuleIsTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instModuleIsTorsionFree [Semiring R] [forall i, AddCommMonoid (M i)] [fora
ll i, Module R (M i)] [forall i, IsTorsionFree R (M i)] : Module.IsTorsionFree R
 (forall i, M i) where isSMulRegular _r hr
参数：M i；M i；M i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.piMap`：∀ {ι : Sort u_4} {α : ι → Sort u_5} {β : ι → S
ort u_6} {f : (i : ι) → α i → β i},   (∀ (i : ι), Function.Injective (f i)) → Fu
nction.Injecti…
· 使用定理 `IsRegular.isSMulRegular`：∀ {R : Type u_1} {M : Type u_3} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Is
TorsionFree R…
-/
instance instModuleIsTorsionFree [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, IsTorsionFree R (M i)] : Module.IsTorsionFree R (∀ i, M i) where
  isSMulRegular _r hr := .piMap fun _i ↦ hr.isSMulRegular

end Pi

