/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Projective

/-!
If `R` is a semisimple ring, then any `R`-module is both injective and projective.

-/

public section

namespace Module

variable (R : Type*) [Ring R] [IsSemisimpleRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-
**Module.injective_of_isSemisimpleRing** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：injective_of_isSemisimpleRing : Module.Injective R M where out X Y _ _ _ _
 f hf g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemisimpleModule.extension_property`：extension_property {P} [AddCommGr
oup P] [Module R P] (f : N ->ₗ[R] M) (hf : Function.Injective f) (g : N ->ₗ[R] P
) : exists h : M ->ₗ[R] P, …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
-/
theorem injective_of_isSemisimpleRing : Module.Injective R M where
  out X Y _ _ _ _ f hf g :=
    let ⟨h, comp⟩ := IsSemisimpleModule.extension_property f hf g
    ⟨h, fun _ ↦ by rw [← comp, LinearMap.comp_apply]⟩
/-
**Module.projective_of_isSemisimpleRing** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：projective_of_isSemisimpleRing : Module.Projective R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.of_lifting_property''`：∀ {R : Type u} [inst : Semiring
 R] {P : Type v} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P],   (∀ (
f : (P →₀ R) →ₗ[R] P), Functi…
· 使用定理 `IsSemisimpleModule.lifting_property`：lifting_property {P} [AddCommGroup 
P] [Module R P] (f : M ->ₗ[R] N) (hf : Function.Surjective f) (g : P ->ₗ[R] N) :
 exists h : P ->ₗ[R] M, f…
· 使用定理 `instIsSemisimpleModuleFinsupp`：∀ {R : Type u_2} [inst : Ring R] {M : Typ
e u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] (ι : Type u_6)   [
IsSemisimpleModule …
-/
theorem projective_of_isSemisimpleRing : Module.Projective R M :=
  .of_lifting_property'' (IsSemisimpleModule.lifting_property · · _)

end Module

