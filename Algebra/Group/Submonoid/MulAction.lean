/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Action.Defs

/-!
# Actions by `Submonoid`s

These instances transfer the action by an element `m : M` of a monoid `M` written as `m • a` onto
the action by an element `s : S` of a submonoid `S : Submonoid M` such that `s • a = (s : M) • a`.

These instances work particularly well in conjunction with `Monoid.toMulAction`, enabling
`s • m` as an alias for `↑s * m`.
-/

@[expose] public section

assert_not_exists RelIso

namespace Submonoid

variable {M' : Type*} {α β : Type*}

section SetLike

variable {S' : Type*} [SetLike S' M'] (s : S')

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [SMul M' α] : SMul s α where
  smul m a := (m : M') • a

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [SMul M' α] [IsLeftCancelSMul M' α] : IsLeftCancelSMul s α where
  left_cancel' x _ _ := IsLeftCancelSMul.left_cancel x.1 _ _

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [SMul M' α] [IsCancelSMul M' α] : IsCancelSMul s α where
  right_cancel' _ _ _ eq := Subtype.ext <| IsCancelSMul.right_cancel _ _ _ eq

section MulOneClass

variable [MulOneClass M']

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [SMul M' β] [SMul α β] [SMulCommClass M' α β] : SMulCommClass s α β :=
  ⟨fun a _ _ => smul_comm (a : M') _ _⟩

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [SMul α β] [SMul M' β] [SMulCommClass α M' β] : SMulCommClass α s β :=
  ⟨fun a s => smul_comm a (s : M')⟩

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [SMul α β] [SMul M' α] [SMul M' β] [IsScalarTower M' α β] :
    IsScalarTower s α β :=
  ⟨fun a => smul_assoc (a : M')⟩

end MulOneClass

variable [Monoid M'] [SubmonoidClass S' M']

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [MulAction M' α] : MulAction s α where
  one_smul := one_smul M'
  mul_smul m₁ m₂ := mul_smul (m₁ : M') m₂

end SetLike

section MulOneClass

variable [MulOneClass M']

@[to_additive]
/-
**Submonoid.smul** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：smul [SMul M' α] (S : Submonoid M') : SMul S α
参数：S : Submonoid M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smul [SMul M' α] (S : Submonoid M') : SMul S α :=
  inferInstance

@[to_additive]
/-
**Submonoid.smulCommClass_left** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：smulCommClass_left [SMul M' β] [SMul α β] [SMulCommClass M' α β] (S : Subm
onoid M') : SMulCommClass S α β
参数：S : Submonoid M'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSMulCommClassSubtypeMem`：∀ {M' : Type u_1} {α : Type u_2} 
{β : Type u_3} {S' : Type u_4} [inst : SetLike S' M'] (s : S') [inst_1 : SMul M'
 β]   [inst_2 : SMul α β] […
-/
instance smulCommClass_left [SMul M' β] [SMul α β] [SMulCommClass M' α β]
    (S : Submonoid M') : SMulCommClass S α β :=
  inferInstance

@[to_additive]
/-
**Submonoid.smulCommClass_right** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：smulCommClass_right [SMul α β] [SMul M' β] [SMulCommClass α M' β] (S : Sub
monoid M') : SMulCommClass α S β
参数：S : Submonoid M'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSMulCommClassSubtypeMem_1`：∀ {M' : Type u_1} {α : Type u_2
} {β : Type u_3} {S' : Type u_4} [inst : SetLike S' M'] (s : S') [inst_1 : SMul 
α β]   [inst_2 : SMul M' β] […
-/
instance smulCommClass_right [SMul α β] [SMul M' β] [SMulCommClass α M' β]
    (S : Submonoid M') : SMulCommClass α S β :=
  inferInstance

/-- Note that this provides `IsScalarTower S M' M'` which is needed by `SMulMulAssoc`. -/
@[to_additive]
/-
**Submonoid.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：isScalarTower [SMul α β] [SMul M' α] [SMul M' β] [IsScalarTower M' α β] (S
 : Submonoid M') : IsScalarTower S α β
参数：S : Submonoid M'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instIsScalarTowerSubtypeMem`：∀ {M' : Type u_1} {α : Type u_2} 
{β : Type u_3} {S' : Type u_4} [inst : SetLike S' M'] (s : S') [inst_1 : SMul α 
β]   [inst_2 : SMul M' α] […

--- 原说明 ---
Note that this provides `IsScalarTower S M' M'` which is needed by `SMulMulAssoc
`.
-/
instance isScalarTower [SMul α β] [SMul M' α] [SMul M' β] [IsScalarTower M' α β]
      (S : Submonoid M') :
    IsScalarTower S α β :=
  inferInstance

section SMul
variable [SMul M' α] {S : Submonoid M'}

/-
**Submonoid.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass M'] [inst_1 : SMul M'
 α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
参数：g : ↥S；a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma smul_def (g : S) (a : α) : g • a = (g : M') • a := rfl

@[to_additive (attr := simp)]
/-
**Submonoid.mk_smul** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：mk_smul (g : M') (hg : g in S) (a : α) : (⟨g, hg⟩ : S) • a = g • a
参数：g : M'；hg : g in S；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_smul (g : M') (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

end SMul
end MulOneClass

variable [Monoid M']

/-- The action by a submonoid is the action by the underlying monoid. -/
@[to_additive
      /-- The additive action by an `AddSubmonoid` is the action by the underlying `AddMonoid`. -/]
/-
**Submonoid.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：mulAction [MulAction M' α] (S : Submonoid M') : MulAction S α
参数：S : Submonoid M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction [MulAction M' α] (S : Submonoid M') : MulAction S α :=
  inferInstance
/-
**Submonoid.smulDistribClass** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：smulDistribClass {β S : Type*} [SMul M' α] [SMul M' β] [SMul α β] [SetLike
 S M'] [h : SMulDistribClass M' α β] (N' : S) : SMulDistribClass N' α β
参数：N' : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulDistribClass.smul_distrib_smul`：∀ {G : Type u_9} {R : Type u_10} {S 
: Type u_11} {inst : SMul G R} {inst_1 : SMul G S} {inst_2 : SMul R S}   [self :
 SMulDistribClass G R S]…
-/
instance smulDistribClass {β S : Type*} [SMul M' α] [SMul M' β] [SMul α β] [SetLike S M']
    [h : SMulDistribClass M' α β] (N' : S) :
    SMulDistribClass N' α β := ⟨fun g _ _ ↦ h.smul_distrib_smul g _ _⟩
/-
**Submonoid.** 是 Mathlib 中的一个示例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {S : Submonoid M'} : IsScalarTower S M' M' := by infer_instance

end Submonoid

