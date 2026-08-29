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
instance (priority := low) [SMul M' α] : SMul s α where
  smul m a := (m : M') • a

@[to_additive]
instance (priority := low) [SMul M' α] [IsLeftCancelSMul M' α] : IsLeftCancelSMul s α where
  left_cancel' x _ _ := IsLeftCancelSMul.left_cancel x.1 _ _

@[to_additive]
instance (priority := low) [SMul M' α] [IsCancelSMul M' α] : IsCancelSMul s α where
right_cancel' _ _ _ eq := Subtype.ext IsCancelSMul.right_cancel _ _ _ eq

section MulOneClass

variable [MulOneClass M']

@[to_additive]
instance (priority := low) [SMul M' β] [SMul α β] [SMulCommClass M' α β] : SMulCommClass s α β :=
  ⟨fun a _ _ => smul_comm (a : M') _ _⟩

@[to_additive]
instance (priority := low) [SMul α β] [SMul M' β] [SMulCommClass α M' β] : SMulCommClass α s β :=
  ⟨fun a s => smul_comm a (s : M')⟩

@[to_additive]
instance (priority := low) [SMul α β] [SMul M' α] [SMul M' β] [IsScalarTower M' α β] :
    IsScalarTower s α β :=
  ⟨fun a => smul_assoc (a : M')⟩

end MulOneClass

variable [Monoid M'] [SubmonoidClass S' M']

@[to_additive]
instance (priority := low) [MulAction M' α] : MulAction s α where
  one_smul := one_smul M'
  mul_smul m₁ m₂ := mul_smul (m₁ : M') m₂

end SetLike

section MulOneClass

variable [MulOneClass M']

@[to_additive]
/--
Instance `smul` / 实例 `smul`

English:
instance smul
  signature: [SMul M' α] (S : Submonoid M')
  body: inferInstance

@[to_additive]

中文:
实例 smul
  签名: [标量乘法 M' α] (S : 子幺半群 M')
  定义体: inferInstance

@[to_additive]
-/
instance smul [SMul M' α] (S : Submonoid M') : SMul S α :=
  inferInstance

@[to_additive]
/--
Instance `smulCommClass_left` / 实例 `smulCommClass_left`

English:
instance smulCommClass_left
  signature: [SMul M' β] [SMul α β] [SMulCommClass M' α β]
  body: inferInstance

@[to_additive]

中文:
实例 smulCommClass_left
  签名: [标量乘法 M' β] [标量乘法 α β] [标量交换类 M' α β]
  定义体: inferInstance

@[to_additive]
-/
instance smulCommClass_left [SMul M' β] [SMul α β] [SMulCommClass M' α β]
    (S : Submonoid M') : SMulCommClass S α β :=
  inferInstance

@[to_additive]
/--
Instance `smulCommClass_right` / 实例 `smulCommClass_right`

English:
instance smulCommClass_right
  signature: [SMul α β] [SMul M' β] [SMulCommClass α M' β]
  body: inferInstance

中文:
实例 smulCommClass_right
  签名: [标量乘法 α β] [标量乘法 M' β] [标量交换类 α M' β]
  定义体: inferInstance
-/
instance smulCommClass_right [SMul α β] [SMul M' β] [SMulCommClass α M' β]
    (S : Submonoid M') : SMulCommClass α S β :=
  inferInstance

/-- Note that this provides `IsScalarTower S M' M'` which is needed by `SMulMulAssoc`. -/
@[to_additive]
/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: [SMul α β] [SMul M' α] [SMul M' β] [IsScalarTower M' α β]
  body: inferInstance

中文:
实例 isScalarTower
  签名: [标量乘法 α β] [标量乘法 M' α] [标量乘法 M' β] [标量塔 M' α β]
  定义体: inferInstance
-/
instance isScalarTower [SMul α β] [SMul M' α] [SMul M' β] [IsScalarTower M' α β]
      (S : Submonoid M') :
    IsScalarTower S α β :=
  inferInstance

section SMul
variable [SMul M' α] {S : Submonoid M'}

/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: (g : S) (a : α)
  statement: g • a = (g : M') • a
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 smul_def
  条件: (g : S) (a : α)
  结论: g • a = (g : M') • a
  证明: rfl

@[to_additive (attr := simp)]
-/
@[to_additive] lemma smul_def (g : S) (a : α) : g • a = (g : M') • a := rfl

@[to_additive (attr := simp)]
/--
lemma `mk_smul` / 引理 `mk_smul`

English:
lemma mk_smul
  given: (g : M') (hg : g in S) (a : α)
  statement: (⟨g, hg⟩ : S) • a = g • a
  proof: rfl

中文:
引理 mk_smul
  条件: (g : M') (hg : g in S) (a : α)
  结论: (⟨g, hg⟩ : S) • a = g • a
  证明: rfl
-/
lemma mk_smul (g : M') (hg : g in S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

end SMul
end MulOneClass

variable [Monoid M']

/-- The action by a submonoid is the action by the underlying monoid. -/
@[to_additive
      /-- The additive action by an `AddSubmonoid` is the action by the underlying `AddMonoid`. -/]
/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: [MulAction M' α] (S : Submonoid M')
  body: inferInstance

中文:
实例 mulAction
  签名: [乘法作用 M' α] (S : 子幺半群 M')
  定义体: inferInstance
-/
instance mulAction [MulAction M' α] (S : Submonoid M') : MulAction S α :=
  inferInstance

/--
Instance `smulDistribClass` / 实例 `smulDistribClass`

English:
instance smulDistribClass
  signature: {β S : Type*} [SMul M' α] [SMul M' β] [SMul α β] [SetLike S M']
  body: ⟨fun g _ _ => h.smul_distrib_smul g _ _⟩

example {S : Submonoid M'} : IsScalarTower S M' M' := by infer_instance

中文:
实例 smulDistribClass
  签名: {β S : 类型} [标量乘法 M' α] [标量乘法 M' β] [标量乘法 α β] [集合状 S M']
  定义体: ⟨fun g _ _ => h.smul_distrib_smul g _ _⟩

example {S : Submonoid M'} : IsScalarTower S M' M' := by infer_instance

Depends on / 依赖: UniqueSums, UniqueSums.uniqueAdd_of_nonempty, h.smul_distrib_smul, smul_distrib_smul, uniqueAdd_of_nonempty
-/
instance smulDistribClass {β S : Type*} [SMul M' α] [SMul M' β] [SMul α β] [SetLike S M']
    [h : SMulDistribClass M' α β] (N' : S) :
    SMulDistribClass N' α β := ⟨fun g _ _ => h.smul_distrib_smul g _ _⟩

example {S : Submonoid M'} : IsScalarTower S M' M' := by infer_instance

end Submonoid
