/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousMap.Defs

/-!
# Continuous order homomorphisms

This file defines continuous order homomorphisms, that is maps which are both continuous and
monotone. They are also called Priestley homomorphisms because they are the morphisms of the
category of Priestley spaces.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `ContinuousOrderHom`: Continuous monotone functions, aka Priestley homomorphisms.

## Typeclasses

* `ContinuousOrderHomClass`
-/

@[expose] public section


open Function

variable {F α β γ δ : Type*}

/--
Definition of `ContinuousOrderHom` / `ContinuousOrderHom` 的定义

English:
structure ContinuousOrderHom
  parameters: (α β : Type*) [Preorder α] [Preorder β] [TopologicalSpace α]
  extends: OrderHom α β
  axioms and operations (1):
    - continuous_toFun : Continuous toFun

中文:
结构 ContinuousOrderHom
  参数: (α β : 类型) [Preorder α] [Preorder β] [TopologicalSpace α]
  继承: OrderHom α β
  公理与运算 (1 个):
    - continuous_toFun : Continuous toFun
-/
structure ContinuousOrderHom (α β : Type*) [Preorder α] [Preorder β] [TopologicalSpace α]
  [TopologicalSpace β] extends OrderHom α β where
  continuous_toFun : Continuous toFun

@[inherit_doc] infixr:25 " ->Co " => ContinuousOrderHom

section

/--
Definition of `ContinuousOrderHomClass` / `ContinuousOrderHomClass` 的定义

English:
class ContinuousOrderHomClass
  parameters: (F : Type*) (α β : outParam Type*) [Preorder α] [Preorder β]
  extends: ContinuousMapClass F α β
  axioms and operations (1):
    - map_monotone((f : F)) : Monotone f

中文:
类 ContinuousOrderHomClass
  参数: (F : 类型) (α β : outParam 类型) [Preorder α] [Preorder β]
  继承: ContinuousMapClass F α β
  公理与运算 (1 个):
    - map_monotone((f : F)) : Monotone f
-/
class ContinuousOrderHomClass (F : Type*) (α β : outParam Type*) [Preorder α] [Preorder β]
    [TopologicalSpace α] [TopologicalSpace β] [FunLike F α β] : Prop
    extends ContinuousMapClass F α β where
  map_monotone (f : F) : Monotone f

namespace ContinuousOrderHomClass

variable [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
  [FunLike F α β] [ContinuousOrderHomClass F α β]

-- See note [lower instance priority]
instance (priority := 100) toOrderHomClass :
    OrderHomClass F α β :=
  { ‹ContinuousOrderHomClass F α β› with
    map_rel := ContinuousOrderHomClass.map_monotone }

/-- Turn an element of a type `F` satisfying `ContinuousOrderHomClass F α β` into an actual
`ContinuousOrderHom`. This is declared as the default coercion from `F` to `α →Co β`. -/
@[coe]
/--
Definition of `toContinuousOrderHom` / `toContinuousOrderHom` 的定义

English:
definition toContinuousOrderHom
  signature: (f : F)
  body: { toFun := f
      monotone' := ContinuousOrderHomClass.map_monotone f
      continuous_toFun := map_continuous f }

中文:
定义 toContinuousOrderHom
  签名: (f : F)
  定义体: { toFun := f
      monotone' := ContinuousOrderHomClass.map_monotone f
      continuous_toFun := map_continuous f }

Depends on / 依赖: ContinuousOrderHomClass, ContinuousOrderHomClass.map_monotone, continuous_toFun, map_continuous, map_monotone, monotone
-/
def toContinuousOrderHom (f : F) : α ->Co β :=
    { toFun := f
      monotone' := ContinuousOrderHomClass.map_monotone f
      continuous_toFun := map_continuous f }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC F (α ->Co β)
  body: ⟨toContinuousOrderHom⟩

中文:
实例 :
  签名: CoeTC F (α ->Co β)
  定义体: ⟨toContinuousOrderHom⟩

Depends on / 依赖: toContinuousOrderHom
-/
instance : CoeTC F (α ->Co β) :=
  ⟨toContinuousOrderHom⟩

end ContinuousOrderHomClass
/-! ### Top homomorphisms -/


namespace ContinuousOrderHom

variable [TopologicalSpace α] [Preorder α] [TopologicalSpace β]

section Preorder

variable [Preorder β] [TopologicalSpace γ] [Preorder γ] [TopologicalSpace δ] [Preorder δ]

/--
Definition of `toContinuousMap` / `toContinuousMap` 的定义

English:
definition toContinuousMap
  signature: (f : α ->Co β)
  body: { f with }

中文:
定义 toContinuousMap
  签名: (f : α ->Co β)
  定义体: { f with }
-/
def toContinuousMap (f : α ->Co β) : C(α, β) :=
  { f with }

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (α ->Co β) α β where
  body: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

中文:
实例 instFunLike
  签名: : FunLike (α ->Co β) α β where
  定义体: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike (α ->Co β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousOrderHomClass (α ->Co β) α β
  body: f.monotone'
  map_continuous f := f.continuous_toFun

中文:
实例 :
  签名: ContinuousOrderHomClass (α ->Co β) α β
  定义体: f.monotone'
  map_continuous f := f.continuous_toFun

Depends on / 依赖: f.monotone, monotone
-/
instance : ContinuousOrderHomClass (α ->Co β) α β where
  map_monotone f := f.monotone'
  map_continuous f := f.continuous_toFun

/--
theorem `coe_toOrderHom` / 定理 `coe_toOrderHom`

English:
theorem coe_toOrderHom
  given: (f : α ->Co β)
  statement: ⇑f.toOrderHom = f
  proof: rfl

中文:
定理 coe_toOrderHom
  条件: (f : α ->Co β)
  结论: ⇑f.toOrderHom = f
  证明: rfl
-/
@[simp] theorem coe_toOrderHom (f : α ->Co β) : ⇑f.toOrderHom = f := rfl

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : α ->Co β}
  statement: f.toFun = (f : α -> β)
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe
  条件: {f : α ->Co β}
  结论: f.toFun = (f : α -> β)
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe {f : α ->Co β} : f.toFun = (f : α -> β) := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : α ->Co β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : α ->Co β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : α ->Co β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : α ->Co β) (f' : α -> β) (h : f' = f)
  body: ⟨f.toOrderHom.copy f' h, h.symm.subst f.continuous_toFun⟩

@[simp]

中文:
定义 copy
  签名: (f : α ->Co β) (f' : α -> β) (h : f' = f)
  定义体: ⟨f.toOrderHom.copy f' h, h.symm.subst f.continuous_toFun⟩

@[simp]
-/
protected def copy (f : α ->Co β) (f' : α -> β) (h : f' = f) : α ->Co β :=
  ⟨f.toOrderHom.copy f' h, h.symm.subst f.continuous_toFun⟩

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : α ->Co β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : α ->Co β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : α ->Co β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : α ->Co β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : α ->Co β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : α ->Co β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : α ->Co α
  body: ⟨OrderHom.id, continuous_id⟩

中文:
定义 id
  签名: : α ->Co α
  定义体: ⟨OrderHom.id, continuous_id⟩
-/
protected def id : α ->Co α :=
  ⟨OrderHom.id, continuous_id⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (α ->Co α)
  body: ⟨ContinuousOrderHom.id _⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Inhabited (α ->Co α)
  定义体: ⟨ContinuousOrderHom.id _⟩

@[simp, norm_cast]

Depends on / 依赖: ContinuousOrderHom, ContinuousOrderHom.id
-/
instance : Inhabited (α ->Co α) :=
  ⟨ContinuousOrderHom.id _⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(ContinuousOrderHom.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(ContinuousOrderHom.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(ContinuousOrderHom.id α) = id :=
  rfl

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: ContinuousOrderHom.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: ContinuousOrderHom.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : ContinuousOrderHom.id α a = a :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : β ->Co γ) (g : α ->Co β)
  body: ⟨f.toOrderHom.comp g.toOrderHom, f.continuous_toFun.comp g.continuous_toFun⟩

@[simp]

中文:
定义 comp
  签名: (f : β ->Co γ) (g : α ->Co β)
  定义体: ⟨f.toOrderHom.comp g.toOrderHom, f.continuous_toFun.comp g.continuous_toFun⟩

@[simp]

Depends on / 依赖: continuous_toFun, f.continuous_toFun.comp, f.toOrderHom.comp, g.continuous_toFun, g.toOrderHom, toOrderHom
-/
def comp (f : β ->Co γ) (g : α ->Co β) : ContinuousOrderHom α γ :=
  ⟨f.toOrderHom.comp g.toOrderHom, f.continuous_toFun.comp g.continuous_toFun⟩

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : β ->Co γ) (g : α ->Co β)
  statement: (f.comp g : α -> γ) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : β ->Co γ) (g : α ->Co β)
  结论: (f.comp g : α -> γ) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : β ->Co γ) (g : α ->Co β) : (f.comp g : α -> γ) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : β ->Co γ) (g : α ->Co β) (a : α)
  statement: (f.comp g) a = f (g a)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : β ->Co γ) (g : α ->Co β) (a : α)
  结论: (f.comp g) a = f (g a)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : β ->Co γ) (g : α ->Co β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : γ ->Co δ) (g : β ->Co γ) (h : α ->Co β)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : γ ->Co δ) (g : β ->Co γ) (h : α ->Co β)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : γ ->Co δ) (g : β ->Co γ) (h : α ->Co β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : α ->Co β)
  statement: f.comp (ContinuousOrderHom.id α) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : α ->Co β)
  结论: f.comp (ContinuousOrderHom.id α) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : α ->Co β) : f.comp (ContinuousOrderHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : α ->Co β)
  statement: (ContinuousOrderHom.id β).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : α ->Co β)
  结论: (ContinuousOrderHom.id β).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : α ->Co β) : (ContinuousOrderHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : β ->Co γ} {f : α ->Co β} (hf : Surjective f)
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]

中文:
定理 cancel_right
  条件: {g₁ g₂ : β ->Co γ} {f : α ->Co β} (hf : Surjective f)
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : β ->Co γ} {f : α ->Co β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : β ->Co γ} {f₁ f₂ : α ->Co β} (hg : Injective g)
  proof: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : β ->Co γ} {f₁ f₂ : α ->Co β} (hg : Injective g)
  证明: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: comp_apply, congr_arg
-/
theorem cancel_left {g : β ->Co γ} {f₁ f₂ : α ->Co β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (α ->Co β)
  body: Preorder.lift ((↑) : (α ->Co β) -> α -> β)

中文:
实例 :
  签名: Preorder (α ->Co β)
  定义体: Preorder.lift ((↑) : (α ->Co β) -> α -> β)

Depends on / 依赖: Preorder, Preorder.lift
-/
instance : Preorder (α ->Co β) :=
  Preorder.lift ((↑) : (α ->Co β) -> α -> β)

end Preorder

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: β] : PartialOrder (α ->Co β)
  body: PartialOrder.lift ((↑) : (α ->Co β) -> α -> β) DFunLike.coe_injective

中文:
实例 [PartialOrder
  签名: β] : PartialOrder (α ->Co β)
  定义体: PartialOrder.lift ((↑) : (α ->Co β) -> α -> β) DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective
-/
instance [PartialOrder β] : PartialOrder (α ->Co β) :=
  PartialOrder.lift ((↑) : (α ->Co β) -> α -> β) DFunLike.coe_injective

end ContinuousOrderHom

end
