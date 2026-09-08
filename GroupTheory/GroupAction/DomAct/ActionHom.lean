/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.GroupTheory.GroupAction.DomAct.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
/-!
# Action of `Mᵈᵐᵃ` on `α →[N] β` and `A →+[N] B`

In this file we define action of `DomMulAct M = Mᵈᵐᵃ` on `α →[N] β` and on `A →+[N] B`. At the
time of writing, these homomorphisms are not widely used in the library, so we put these instances
into a separate file, not with the definition of `DomMulAct`.

## TODO

Add left actions of, e.g., `M` on `α →[N] β` to `Mathlib/Algebra/Group/Action/Hom.lean` and
`SMulCommClass` instances saying that left and right actions commute.
-/

public section

namespace DomMulAct

section MulActionSemiHom

section SMul

variable {M α N β : Type*}
variable [SMul M α] [SMul N α] [SMulCommClass M N α] [SMul N β]

/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul Mᵈᵐᵃ (α →[N] β) where
  smul c f := f.comp (SMulCommClass.toMulActionHom _ _ (mk.symm c))
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M' : Type*} [SMul M' α] [SMulCommClass M' N α] [SMulCommClass M M' α] :
    SMulCommClass Mᵈᵐᵃ M'ᵈᵐᵃ (α →[N] β) :=
  DFunLike.coe_injective.smulCommClass (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
/-
**DomMulAct.smul_mulActionHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：smul_mulActionHom_apply (c : Mᵈᵐᵃ) (f : α ->[N] β) (a : α) : (c • f) a = f
 (mk.symm c • a)
参数：c : Mᵈᵐᵃ；f : α ->[N] β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_mulActionHom_apply (c : Mᵈᵐᵃ) (f : α →[N] β) (a : α) :
    (c • f) a = f (mk.symm c • a) :=
  rfl

@[simp]
/-
**DomMulAct.mk_smul_mulActionHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：mk_smul_mulActionHom_apply (c : M) (f : α ->[N] β) (a : α) : (mk c • f) a 
= f (c • a)
参数：c : M；f : α ->[N] β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_smul_mulActionHom_apply (c : M) (f : α →[N] β) (a : α) : (mk c • f) a = f (c • a) := rfl

end SMul

/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M α N β : Type*} [Monoid M] [MulAction M α] [SMul N α] [SMulCommClass M N α] [SMul N β] :
    MulAction Mᵈᵐᵃ (α →[N] β) :=
  DFunLike.coe_injective.mulAction _ fun _ _ ↦ rfl

end MulActionSemiHom

section DistribMulActionHom

section SMul

variable {M N A B : Type*} [AddMonoid A] [DistribSMul M A] [Monoid N] [AddMonoid B]
  [DistribMulAction N A] [SMulCommClass M N A] [DistribMulAction N B]

/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul Mᵈᵐᵃ (A →+[N] B) where
  smul c f := f.comp (SMulCommClass.toDistribMulActionHom _ _ (mk.symm c))
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M' : Type*} [DistribSMul M' A] [SMulCommClass M' N A] [SMulCommClass M M' A] :
    SMulCommClass Mᵈᵐᵃ M'ᵈᵐᵃ (A →+[N] B) :=
  DFunLike.coe_injective.smulCommClass (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
/-
**DomMulAct.smul_mulDistribActionHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`
。
形式化陈述：smul_mulDistribActionHom_apply (c : Mᵈᵐᵃ) (f : A ->+[N] B) (a : A) : (c • 
f) a = f (mk.symm c • a)
参数：c : Mᵈᵐᵃ；f : A ->+[N] B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_mulDistribActionHom_apply (c : Mᵈᵐᵃ) (f : A →+[N] B) (a : A) :
    (c • f) a = f (mk.symm c • a) :=
  rfl

@[simp]
/-
**DomMulAct.mk_smul_mulDistribActionHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `DomMulA
ct`。
形式化陈述：mk_smul_mulDistribActionHom_apply (c : M) (f : A ->+[N] B) (a : A) : (mk c
 • f) a = f (c • a)
参数：c : M；f : A ->+[N] B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_smul_mulDistribActionHom_apply (c : M) (f : A →+[N] B) (a : A) :
    (mk c • f) a = f (c • a) := rfl

end SMul

/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N A B : Type*} [Monoid M] [AddMonoid A] [DistribMulAction M A] [Monoid N] [AddMonoid B]
    [DistribMulAction N A] [SMulCommClass M N A] [DistribMulAction N B] :
    MulAction Mᵈᵐᵃ (A →+[N] B) :=
  DFunLike.coe_injective.mulAction _ fun _ _ ↦ rfl

end DistribMulActionHom

end DomMulAct

