/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Group.Hom.Instances

/-! # Zero-related `•` instances on group-like morphisms -/

public section

variable {M N A B C : Type*}

namespace ZeroHom

section Zero
variable [Zero A] [Zero B] [Zero C]

/-
**ZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `ZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulZeroClass M B] : SMulZeroClass M (ZeroHom A B) where
  smul r f :=
    { toFun a := r • f a
      map_zero' := by simp only [map_zero, smul_zero] }
  smul_zero _ := ext fun _ => smul_zero _
/-
**ZeroHom.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `ZeroHom`。
形式化陈述：∀ {M : Type u_1} {A : Type u_3} {B : Type u_4} [inst : Zero A] [inst_1 : Z
ero B] [inst_2 : SMulZeroClass M B] (m : M)   (f : ZeroHom A B), ⇑(m • f) = m • 
⇑f
参数：m : M；f : ZeroHom A B；m • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] theorem coe_smul [SMulZeroClass M B] (m : M) (f : ZeroHom A B) : ⇑(m • f) = m • f :=
  rfl
/-
**ZeroHom.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZeroHom`。
形式化陈述：∀ {M : Type u_1} {A : Type u_3} {B : Type u_4} [inst : Zero A] [inst_1 : Z
ero B] [inst_2 : SMulZeroClass M B] (m : M)   (f : ZeroHom A B) (a : A), (m • f)
 a = m • f a
参数：m : M；f : ZeroHom A B；a : A；m • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem smul_apply [SMulZeroClass M B] (m : M) (f : ZeroHom A B) (a : A) :
    (m • f) a = m • f a := rfl
/-
**ZeroHom.smul_comp** 是 Mathlib 中的一个定理，位于命名空间 `ZeroHom`。
形式化陈述：smul_comp [SMulZeroClass M C] (m : M) (g : ZeroHom B C) (f : ZeroHom A B) 
: (m • g).comp f = m • g.comp f
参数：m : M；g : ZeroHom B C；f : ZeroHom A B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_comp [SMulZeroClass M C] (m : M) (g : ZeroHom B C) (f : ZeroHom A B) :
    (m • g).comp f = m • g.comp f := rfl
/-
**ZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `ZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulZeroClass M B] [SMulZeroClass N B] [SMulCommClass M N B] :
    SMulCommClass M N (ZeroHom A B) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _
/-
**ZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `ZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M N] [SMulZeroClass M B] [SMulZeroClass N B] [IsScalarTower M N B] :
    IsScalarTower M N (ZeroHom A B) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _
/-
**ZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `ZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulZeroClass M B] [SMulZeroClass Mᵐᵒᵖ B] [IsCentralScalar M B] :
    IsCentralScalar M (ZeroHom A B) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _
/-
**ZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `ZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero M] [SMulWithZero M B] : SMulWithZero M (ZeroHom A B) where
  zero_smul _ := ext fun _ => zero_smul _ _
/-
**ZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `ZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MonoidWithZero M] [MulActionWithZero M B] : MulActionWithZero M (ZeroHom A B) where
  __ : SMulWithZero _ _ := inferInstance
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _

end Zero

end ZeroHom

namespace AddMonoidHom

section
variable [AddZeroClass A] [AddZeroClass B] [AddZeroClass C]

/-
**AddMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribSMul M B] : SMulZeroClass M (A →+ B) where
  smul r f :=
    { toFun a := r • f a
      map_zero' := by simp only [map_zero, smul_zero]
      map_add' _ _ := by simp only [map_add, smul_add] }
  smul_zero _ := ext fun _ => smul_zero _
/-
**AddMonoidHom.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：∀ {M : Type u_1} {A : Type u_3} {B : Type u_4} [inst : AddZeroClass A] [in
st_1 : AddZeroClass B]   [inst_2 : DistribSMul M B] (m : M) (f : A →+ B), ⇑(m • 
f) = m • ⇑f
参数：m : M；f : A →+ B；m • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] theorem coe_smul [DistribSMul M B] (m : M) (f : A →+ B) : ⇑(m • f) = m • f := rfl
/-
**AddMonoidHom.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：∀ {M : Type u_1} {A : Type u_3} {B : Type u_4} [inst : AddZeroClass A] [in
st_1 : AddZeroClass B]   [inst_2 : DistribSMul M B] (m : M) (f : A →+ B) (a : A)
, (m • f) a = m • f a
参数：m : M；f : A →+ B；a : A；m • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem smul_apply [DistribSMul M B] (m : M) (f : A →+ B) (a : A) : (m • f) a = m • f a :=
  rfl
/-
**AddMonoidHom.smul_comp** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：smul_comp [DistribSMul M C] (m : M) (g : B ->+ C) (f : A ->+ B) : (m • g).
comp f = m • g.comp f
参数：m : M；g : B ->+ C；f : A ->+ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_comp [DistribSMul M C] (m : M) (g : B →+ C) (f : A →+ B) :
    (m • g).comp f = m • g.comp f := rfl
/-
**AddMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribSMul M B] [DistribSMul N B] [SMulCommClass M N B] :
    SMulCommClass M N (A →+ B) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _
/-
**AddMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M N] [DistribSMul M B] [DistribSMul N B] [IsScalarTower M N B] :
    IsScalarTower M N (A →+ B) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _
/-
**AddMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribSMul M B] [DistribSMul Mᵐᵒᵖ B] [IsCentralScalar M B] :
    IsCentralScalar M (A →+ B) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

end

variable [AddZeroClass A] [AddCommMonoid B]

/-
**AddMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribSMul M B] : DistribSMul M (A →+ B) where
  smul_add _ _ _ := ext fun _ => smul_add _ _ _
/-
**AddMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid M] [DistribMulAction M B] : DistribMulAction M (A →+ B) where
  __ : DistribSMul _ _ := inferInstance
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _

end AddMonoidHom

