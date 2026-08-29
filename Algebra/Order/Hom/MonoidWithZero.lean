/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Hom.Monoid

/-!
# Ordered monoid and group homomorphisms

This file defines morphisms between (additive) ordered monoids with zero.

## Types of morphisms

* `OrderMonoidWithZeroHom`: Ordered monoid with zero homomorphisms.

## Notation

* `→*₀o`: Bundled ordered monoid with zero homs. Also use for group with zero homs.

## TODO

* `≃*₀o`: Bundled ordered monoid with zero isos. Also use for group with zero isos.

## Tags

monoid with zero
-/

@[expose] public section


open Function

variable {F α β γ δ : Type*}

section MonoidWithZero

variable [Preorder α] [Preorder β] [MulZeroOneClass α] [MulZeroOneClass β]

/--
Definition of `OrderMonoidWithZeroHom` / `OrderMonoidWithZeroHom` 的定义

English:
structure OrderMonoidWithZeroHom
  parameters: (α β : Type*) [Preorder α] [Preorder β] [MulZeroOneClass α]
  extends: α ->*₀ β
  axioms and operations (1):
    - monotone' : Monotone toFun

中文:
结构 带零Order幺半群态射
  参数: (α β : 类型) [预序 α] [预序 β] [乘零幺类 α]
  继承: α ->*₀ β
  公理与运算 (1 个):
    - monotone' : 递增 toFun
-/
structure OrderMonoidWithZeroHom (α β : Type*) [Preorder α] [Preorder β] [MulZeroOneClass α]
  [MulZeroOneClass β] extends α ->*₀ β where
  /-- An `OrderMonoidWithZeroHom` is a monotone function. -/
  monotone' : Monotone toFun

/-- Infix notation for `OrderMonoidWithZeroHom`. -/
infixr:25 " ->*₀o " => OrderMonoidWithZeroHom

section

variable [FunLike F α β]

/-- Turn an element of a type `F`
satisfying `OrderHomClass F α β` and `MonoidWithZeroHomClass F α β`
into an actual `OrderMonoidWithZeroHom`.
This is declared as the default coercion from `F` to `α →+*₀o β`.
TODO: Following [#mathlib4 > Mathlib's morphism hierarchy]
(https://leanprover.zulipchat.com/#narrow/channel/287929-
mathlib4/topic/Mathlib.27s.20morphism.20hierarchy/with/554383157),
rename this to `OrderMonoidWithZeroHom.ofClass` and remove `@[coe]` tag. -/
@[coe]
/--
Definition of `OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom` / `OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom` 的定义

English:
definition OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom
  signature: [OrderHomClass F α β]
  body: { (.ofClass f : α ->*₀ β) with monotone' := OrderHomClass.monotone f }

中文:
定义 OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom
  签名: [序态射类 F α β]
  定义体: { (.ofClass f : α ->*₀ β) with monotone' := OrderHomClass.monotone f }

Depends on / 依赖: OrderHomClass, OrderHomClass.monotone, monotone, ofClass
-/
def OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom [OrderHomClass F α β]
    [MonoidWithZeroHomClass F α β] (f : F) : α ->*₀o β :=
{ (.ofClass f : α ->*₀ β) with monotone' := OrderHomClass.monotone f }

end

variable [FunLike F α β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [OrderHomClass
  signature: F α β] [MonoidWithZeroHomClass F α β] : CoeTC F (α ->*₀o β)
  body: ⟨OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom⟩

中文:
实例 [序态射类
  签名: F α β] [带零幺半群态射类 F α β] : CoeTC F (α ->*₀o β)
  定义体: ⟨OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom⟩

Depends on / 依赖: OrderMonoidWithZeroHomClass, OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom, toOrderMonoidWithZeroHom
-/
instance [OrderHomClass F α β] [MonoidWithZeroHomClass F α β] : CoeTC F (α ->*₀o β) :=
  ⟨OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom⟩

end MonoidWithZero

namespace OrderMonoidWithZeroHom

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulZeroOneClass α] [MulZeroOneClass β]
  [MulZeroOneClass γ] [MulZeroOneClass δ] {f g : α ->*₀o β}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (α ->*₀o β) α β
  body: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr

initialize_simps_projections OrderMonoidWithZeroHom (toFun -> apply, -toMonoidWithZeroHom)

中文:
实例 :
  签名: 函数状 (α ->*₀o β) α β
  定义体: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr

initialize_simps_projections OrderMonoidWithZeroHom (toFun -> apply, -toMonoidWithZeroHom)

Depends on / 依赖: f.toFun
-/
instance : FunLike (α ->*₀o β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr

initialize_simps_projections OrderMonoidWithZeroHom (toFun -> apply, -toMonoidWithZeroHom)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidWithZeroHomClass (α ->*₀o β) α β
  body: f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'

中文:
实例 :
  签名: 带零幺半群态射类 (α ->*₀o β) α β
  定义体: f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'

Depends on / 依赖: f.map_mul, map_mul
-/
instance : MonoidWithZeroHomClass (α ->*₀o β) α β where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderHomClass (α ->*₀o β) α β
  body: f.monotone' h

中文:
实例 :
  签名: 序态射类 (α ->*₀o β) α β
  定义体: f.monotone' h

Depends on / 依赖: f.monotone, monotone
-/
instance : OrderHomClass (α ->*₀o β) α β where
  map_rel f _ _ h := f.monotone' h

-- Other lemmas should be accessed through the `FunLike` API
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : α ->*₀o β)
  statement: f.toFun = (f : α -> β)
  proof: rfl

@[simp]

中文:
定理 toFun_eq_coe
  条件: (f : α ->*₀o β)
  结论: f.toFun = (f : α -> β)
  证明: rfl

@[simp]
-/
theorem toFun_eq_coe (f : α ->*₀o β) : f.toFun = (f : α -> β) :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : α ->*₀ β) (h)
  statement: (OrderMonoidWithZeroHom.mk f h : α -> β) = f
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (f : α ->*₀ β) (h)
  结论: (带零Order幺半群态射.mk f h : α -> β) = f
  证明: rfl

@[simp]
-/
theorem coe_mk (f : α ->*₀ β) (h) : (OrderMonoidWithZeroHom.mk f h : α -> β) = f :=
  rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : α ->*₀o β) (h)
  statement: OrderMonoidWithZeroHom.mk (.ofClass f) h = f
  proof: rfl

中文:
定理 mk_coe
  条件: (f : α ->*₀o β) (h)
  结论: 带零Order幺半群态射.mk (.ofClass f) h = f
  证明: rfl
-/
theorem mk_coe (f : α ->*₀o β) (h) : OrderMonoidWithZeroHom.mk (.ofClass f) h = f := rfl

/--
Definition of `toOrderMonoidHom` / `toOrderMonoidHom` 的定义

English:
definition toOrderMonoidHom
  signature: (f : α ->*₀o β)
  body: { f with }

@[simp]

中文:
定义 toOrderMonoidHom
  签名: (f : α ->*₀o β)
  定义体: { f with }

@[simp]
-/
def toOrderMonoidHom (f : α ->*₀o β) : α ->*o β :=
  { f with }

@[simp]
/--
theorem `coe_monoidWithZeroHom` / 定理 `coe_monoidWithZeroHom`

English:
theorem coe_monoidWithZeroHom
  given: (f : α ->*₀o β)
  statement: ⇑(.ofClass f : α ->*₀ β) = f
  proof: rfl

@[simp]

中文:
定理 coe_monoidWithZeroHom
  条件: (f : α ->*₀o β)
  结论: ⇑(.ofClass f : α ->*₀ β) = f
  证明: rfl

@[simp]
-/
theorem coe_monoidWithZeroHom (f : α ->*₀o β) : ⇑(.ofClass f : α ->*₀ β) = f :=
  rfl

@[simp]
/--
theorem `coe_orderMonoidHom` / 定理 `coe_orderMonoidHom`

English:
theorem coe_orderMonoidHom
  given: (f : α ->*₀o β)
  statement: ⇑(f : α ->*o β) = f
  proof: rfl

中文:
定理 coe_orderMonoidHom
  条件: (f : α ->*₀o β)
  结论: ⇑(f : α ->*o β) = f
  证明: rfl
-/
theorem coe_orderMonoidHom (f : α ->*₀o β) : ⇑(f : α ->*o β) = f :=
  rfl

/--
theorem `toOrderMonoidHom_injective` / 定理 `toOrderMonoidHom_injective`

English:
theorem toOrderMonoidHom_injective
  statement: Injective (toOrderMonoidHom : _ -> α ->*o β)
  proof: fun f g h =>
ext by convert! DFunLike.ext_iff.1 h using 0

中文:
定理 toOrderMonoidHom_injective
  结论: 单射 (toOrderMonoidHom : _ -> α ->*o β)
  证明: fun f g h =>
ext by convert! DFunLike.ext_iff.1 h using 0
-/
theorem toOrderMonoidHom_injective : Injective (toOrderMonoidHom : _ -> α ->*o β) := fun f g h =>
ext by convert! DFunLike.ext_iff.1 h using 0

/--
theorem `toMonoidWithZeroHom_injective` / 定理 `toMonoidWithZeroHom_injective`

English:
theorem toMonoidWithZeroHom_injective
  statement: Injective (toMonoidWithZeroHom : _ -> α ->*₀ β)
  proof: fun f g h => ext by convert! DFunLike.ext_iff.1 h using 0

中文:
定理 toMonoidWithZeroHom_injective
  结论: 单射 (toMonoidWithZeroHom : _ -> α ->*₀ β)
  证明: fun f g h => ext by convert! DFunLike.ext_iff.1 h using 0

Depends on / 依赖: DFunLike, DFunLike.ext_iff, convert, ext_iff
-/
theorem toMonoidWithZeroHom_injective : Injective (toMonoidWithZeroHom : _ -> α ->*₀ β) :=
fun f g h => ext by convert! DFunLike.ext_iff.1 h using 0

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : α ->*₀o β) (f' : α -> β) (h : f' = f)
  body: { f.toOrderMonoidHom.copy f' h, f.toMonoidWithZeroHom.copy f' h with toFun := f' }

@[simp]

中文:
定义 copy
  签名: (f : α ->*₀o β) (f' : α -> β) (h : f' = f)
  定义体: { f.toOrderMonoidHom.copy f' h, f.toMonoidWithZeroHom.copy f' h with toFun := f' }

@[simp]
-/
protected def copy (f : α ->*₀o β) (f' : α -> β) (h : f' = f) : α ->*o β :=
  { f.toOrderMonoidHom.copy f' h, f.toMonoidWithZeroHom.copy f' h with toFun := f' }

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : α ->*₀o β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : α ->*₀o β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : α ->*₀o β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : α ->*₀o β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : α ->*₀o β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : α ->*₀o β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : α ->*₀o α
  body: { MonoidWithZeroHom.id α, OrderHom.id with }

@[simp, norm_cast]

中文:
定义 id
  签名: : α ->*₀o α
  定义体: { MonoidWithZeroHom.id α, OrderHom.id with }

@[simp, norm_cast]
-/
protected def id : α ->*₀o α :=
  { MonoidWithZeroHom.id α, OrderHom.id with }

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(OrderMonoidWithZeroHom.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(带零Order幺半群态射.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(OrderMonoidWithZeroHom.id α) = id :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (α ->*₀o α)
  body: ⟨OrderMonoidWithZeroHom.id α⟩

中文:
实例 :
  签名: 可居 (α ->*₀o α)
  定义体: ⟨OrderMonoidWithZeroHom.id α⟩

Depends on / 依赖: OrderMonoidWithZeroHom, OrderMonoidWithZeroHom.id
-/
instance : Inhabited (α ->*₀o α) :=
  ⟨OrderMonoidWithZeroHom.id α⟩

variable {α}

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : β ->*₀o γ) (g : α ->*₀o β)
  body: { (.ofClass f : β ->*₀ γ).comp (.ofClass g), f.toOrderMonoidHom.comp (g : α ->*o β) with }

@[simp]

中文:
定义 comp
  签名: (f : β ->*₀o γ) (g : α ->*₀o β)
  定义体: { (.ofClass f : β ->*₀ γ).comp (.ofClass g), f.toOrderMonoidHom.comp (g : α ->*o β) with }

@[simp]

Depends on / 依赖: f.toOrderMonoidHom.comp, ofClass, toOrderMonoidHom
-/
def comp (f : β ->*₀o γ) (g : α ->*₀o β) : α ->*₀o γ :=
  { (.ofClass f : β ->*₀ γ).comp (.ofClass g), f.toOrderMonoidHom.comp (g : α ->*o β) with }

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : β ->*₀o γ) (g : α ->*₀o β)
  statement: (f.comp g : α -> γ) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : β ->*₀o γ) (g : α ->*₀o β)
  结论: (f.comp g : α -> γ) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : β ->*₀o γ) (g : α ->*₀o β) : (f.comp g : α -> γ) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : β ->*₀o γ) (g : α ->*₀o β) (a : α)
  statement: (f.comp g) a = f (g a)
  proof: rfl

中文:
定理 comp_apply
  条件: (f : β ->*₀o γ) (g : α ->*₀o β) (a : α)
  结论: (f.comp g) a = f (g a)
  证明: rfl
-/
theorem comp_apply (f : β ->*₀o γ) (g : α ->*₀o β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

/--
theorem `ofClass_comp_monoidWithZeroHom` / 定理 `ofClass_comp_monoidWithZeroHom`

English:
theorem ofClass_comp_monoidWithZeroHom
  given: (f : β ->*₀o γ) (g : α ->*₀o β)
  proof: rfl

中文:
定理 ofClass_comp_monoidWithZeroHom
  条件: (f : β ->*₀o γ) (g : α ->*₀o β)
  证明: rfl
-/
theorem ofClass_comp_monoidWithZeroHom (f : β ->*₀o γ) (g : α ->*₀o β) :
    .ofClass (f.comp g) = (.ofClass f : β ->*₀ γ).comp (.ofClass g) :=
  rfl

/--
theorem `coe_comp_orderMonoidHom` / 定理 `coe_comp_orderMonoidHom`

English:
theorem coe_comp_orderMonoidHom
  given: (f : β ->*₀o γ) (g : α ->*₀o β)
  proof: rfl

@[simp]

中文:
定理 coe_comp_orderMonoidHom
  条件: (f : β ->*₀o γ) (g : α ->*₀o β)
  证明: rfl

@[simp]
-/
theorem coe_comp_orderMonoidHom (f : β ->*₀o γ) (g : α ->*₀o β) :
    (f.comp g : α ->*o γ) = (f : β ->*o γ).comp g :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : γ ->*₀o δ) (g : β ->*₀o γ) (h : α ->*₀o β)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : γ ->*₀o δ) (g : β ->*₀o γ) (h : α ->*₀o β)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : γ ->*₀o δ) (g : β ->*₀o γ) (h : α ->*₀o β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : α ->*₀o β)
  statement: f.comp (OrderMonoidWithZeroHom.id α) = f
  proof: rfl

@[simp]

中文:
定理 comp_id
  条件: (f : α ->*₀o β)
  结论: f.comp (带零Order幺半群态射.id α) = f
  证明: rfl

@[simp]
-/
theorem comp_id (f : α ->*₀o β) : f.comp (OrderMonoidWithZeroHom.id α) = f := rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : α ->*₀o β)
  statement: (OrderMonoidWithZeroHom.id β).comp f = f
  proof: rfl

@[simp]

中文:
定理 id_comp
  条件: (f : α ->*₀o β)
  结论: (带零Order幺半群态射.id β).comp f = f
  证明: rfl

@[simp]
-/
theorem id_comp (f : α ->*₀o β) : (OrderMonoidWithZeroHom.id β).comp f = f := rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : β ->*₀o γ} {f : α ->*₀o β} (hf : Function.Surjective f)
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun _ => by congr⟩

@[simp]

中文:
定理 cancel_right
  条件: {g₁ g₂ : β ->*₀o γ} {f : α ->*₀o β} (hf : 函数.满射 f)
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun _ => by congr⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : β ->*₀o γ} {f : α ->*₀o β} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun _ => by congr⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : β ->*₀o γ} {f₁ f₂ : α ->*₀o β} (hg : Function.Injective g)
  proof: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : β ->*₀o γ} {f₁ f₂ : α ->*₀o β} (hg : 函数.单射 g)
  证明: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: comp_apply, congr_arg
-/
theorem cancel_left {g : β ->*₀o γ} {f₁ f₂ : α ->*₀o β} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end Preorder

section Mul

variable [LinearOrderedCommMonoidWithZero α] [LinearOrderedCommMonoidWithZero β]
  [LinearOrderedCommMonoidWithZero γ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (α ->*₀o β)
  body: ⟨ fun f g => {(.ofClass f : α ->*₀ β) * (.ofClass g : α ->*₀ β) with
      monotone' := f.monotone'.mul' g.monotone'} ⟩

@[simp]

中文:
实例 :
  签名: 乘法 (α ->*₀o β)
  定义体: ⟨ fun f g => {(.ofClass f : α ->*₀ β) * (.ofClass g : α ->*₀ β) with
      monotone' := f.monotone'.mul' g.monotone'} ⟩

@[simp]

Depends on / 依赖: f.monotone, g.monotone, monotone, ofClass
-/
instance : Mul (α ->*₀o β) :=
  ⟨ fun f g => {(.ofClass f : α ->*₀ β) * (.ofClass g : α ->*₀ β) with
      monotone' := f.monotone'.mul' g.monotone'} ⟩

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (f g : α ->*₀o β)
  statement: ⇑(f * g) = f * g
  proof: rfl

@[simp]

中文:
定理 coe_mul
  条件: (f g : α ->*₀o β)
  结论: ⇑(f * g) = f * g
  证明: rfl

@[simp]
-/
theorem coe_mul (f g : α ->*₀o β) : ⇑(f * g) = f * g :=
  rfl

@[simp]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (f g : α ->*₀o β) (a : α)
  statement: (f * g) a = f a * g a
  proof: rfl

中文:
定理 mul_apply
  条件: (f g : α ->*₀o β) (a : α)
  结论: (f * g) a = f a * g a
  证明: rfl
-/
theorem mul_apply (f g : α ->*₀o β) (a : α) : (f * g) a = f a * g a :=
  rfl

/--
theorem `mul_comp` / 定理 `mul_comp`

English:
theorem mul_comp
  given: (g₁ g₂ : β ->*₀o γ) (f : α ->*₀o β)
  statement: (g₁ * g₂).comp f = g₁.comp f * g₂.comp f
  proof: rfl

中文:
定理 mul_comp
  条件: (g₁ g₂ : β ->*₀o γ) (f : α ->*₀o β)
  结论: (g₁ * g₂).comp f = g₁.comp f * g₂.comp f
  证明: rfl
-/
theorem mul_comp (g₁ g₂ : β ->*₀o γ) (f : α ->*₀o β) : (g₁ * g₂).comp f = g₁.comp f * g₂.comp f :=
  rfl

/--
theorem `comp_mul` / 定理 `comp_mul`

English:
theorem comp_mul
  given: (g : β ->*₀o γ) (f₁ f₂ : α ->*₀o β)
  statement: g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂
  proof: ext fun _ => map_mul g _ _

中文:
定理 comp_mul
  条件: (g : β ->*₀o γ) (f₁ f₂ : α ->*₀o β)
  结论: g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂
  证明: ext fun _ => map_mul g _ _

Depends on / 依赖: map_mul
-/
theorem comp_mul (g : β ->*₀o γ) (f₁ f₂ : α ->*₀o β) : g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ :=
  ext fun _ => map_mul g _ _

end Mul

section LinearOrderedCommMonoidWithZero

variable {hα : Preorder α} {hα' : MulZeroOneClass α} {hβ : Preorder β} {hβ' : MulZeroOneClass β}
  {hγ : Preorder γ} {hγ' : MulZeroOneClass γ}

@[simp]
/--
theorem `toMonoidWithZeroHom_eq_ofClass` / 定理 `toMonoidWithZeroHom_eq_ofClass`

English:
theorem toMonoidWithZeroHom_eq_ofClass
  given: (f : α ->*₀o β)
  statement: f.toMonoidWithZeroHom = .ofClass f
  proof: by
  rfl

@[simp]

中文:
定理 toMonoidWithZeroHom_eq_ofClass
  条件: (f : α ->*₀o β)
  结论: f.toMonoidWithZeroHom = .ofClass f
  证明: by
  rfl

@[simp]
-/
theorem toMonoidWithZeroHom_eq_ofClass (f : α ->*₀o β) : f.toMonoidWithZeroHom = .ofClass f := by
  rfl

@[simp]
/--
theorem `ofClass_mk` / 定理 `ofClass_mk`

English:
theorem ofClass_mk
  given: (f : α ->*₀ β) (hf : Monotone f)
  proof: by
  rfl

@[simp]

中文:
定理 ofClass_mk
  条件: (f : α ->*₀ β) (hf : 递增 f)
  证明: by
  rfl

@[simp]
-/
theorem ofClass_mk (f : α ->*₀ β) (hf : Monotone f) :
    .ofClass (OrderMonoidWithZeroHom.mk f hf) = f := by
  rfl

@[simp]
/--
lemma `ofClass_comp` / 引理 `ofClass_comp`

English:
lemma ofClass_comp
  given: (f : β ->*₀o γ) (g : α ->*₀o β)
  proof: rfl

@[simp]

中文:
引理 ofClass_comp
  条件: (f : β ->*₀o γ) (g : α ->*₀o β)
  证明: rfl

@[simp]
-/
lemma ofClass_comp (f : β ->*₀o γ) (g : α ->*₀o β) :
    .ofClass (f.comp g) = (.ofClass f : β ->*₀ γ).comp (.ofClass g) :=
  rfl

@[simp]
/--
theorem `toOrderMonoidHom_eq_coe` / 定理 `toOrderMonoidHom_eq_coe`

English:
theorem toOrderMonoidHom_eq_coe
  given: (f : α ->*₀o β)
  statement: f.toOrderMonoidHom = f
  proof: rfl

@[simp]

中文:
定理 toOrderMonoidHom_eq_coe
  条件: (f : α ->*₀o β)
  结论: f.toOrderMonoidHom = f
  证明: rfl

@[simp]
-/
theorem toOrderMonoidHom_eq_coe (f : α ->*₀o β) : f.toOrderMonoidHom = f :=
  rfl

@[simp]
/--
lemma `toOrderMonoidHom_comp` / 引理 `toOrderMonoidHom_comp`

English:
lemma toOrderMonoidHom_comp
  given: (f : β ->*₀o γ) (g : α ->*₀o β)
  proof: rfl

中文:
引理 toOrderMonoidHom_comp
  条件: (f : β ->*₀o γ) (g : α ->*₀o β)
  证明: rfl
-/
lemma toOrderMonoidHom_comp (f : β ->*₀o γ) (g : α ->*₀o β) :
    (f.comp g : α ->*o γ) = (f : β ->*o γ).comp g :=
  rfl

end LinearOrderedCommMonoidWithZero

end OrderMonoidWithZeroHom

set_option backward.isDefEq.respectTransparency false in
/-- Any ordered group is isomorphic to the units of itself adjoined with `0`. -/
@[simps! -isSimp]
/--
Definition of `OrderMonoidIso.unitsWithZero` / `OrderMonoidIso.unitsWithZero` 的定义

English:
definition OrderMonoidIso.unitsWithZero
  signature: {α : Type*} [Group α] [Preorder α]
  body: WithZero.unitsWithZeroEquiv
  map_le_map_iff' {a b} := by simp [WithZero.unitsWithZeroEquiv]

中文:
定义 OrderMonoidIso.unitsWithZero
  签名: {α : 类型} [群 α] [预序 α]
  定义体: WithZero.unitsWithZeroEquiv
  map_le_map_iff' {a b} := by simp [WithZero.unitsWithZeroEquiv]

Depends on / 依赖: WithZero, WithZero.unitsWithZeroEquiv, unitsWithZeroEquiv
-/
def OrderMonoidIso.unitsWithZero {α : Type*} [Group α] [Preorder α] : (WithZero α)ˣ ≃*o α where
  toMulEquiv := WithZero.unitsWithZeroEquiv
  map_le_map_iff' {a b} := by simp [WithZero.unitsWithZeroEquiv]

/-- A version of `Equiv.optionCongr` for `WithZero` on `OrderMonoidIso`. -/
@[simps!]
/--
Definition of `OrderMonoidIso.withZero` / `OrderMonoidIso.withZero` 的定义

English:
definition OrderMonoidIso.withZero
  signature: {G H : Type*}
  body: ⟨e.toMulEquiv.withZero, fun {a b} => by cases a <;> cases b <;> simp⟩
  invFun e := ⟨MulEquiv.withZero.symm e, fun {a b} => by simp⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext x; cases x <;> simp

中文:
定义 OrderMonoidIso.withZero
  签名: {G H : 类型}
  定义体: ⟨e.toMulEquiv.withZero, fun {a b} => by cases a <;> cases b <;> simp⟩
  invFun e := ⟨MulEquiv.withZero.symm e, fun {a b} => by simp⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext x; cases x <;> simp

Depends on / 依赖: e.toMulEquiv.withZero, toMulEquiv, withZero
-/
def OrderMonoidIso.withZero {G H : Type*}
    [Group G] [PartialOrder G] [Group H] [PartialOrder H] :
    (G ≃*o H) ≃ (WithZero G ≃*o WithZero H) where
  toFun e := ⟨e.toMulEquiv.withZero, fun {a b} => by cases a <;> cases b <;> simp⟩
  invFun e := ⟨MulEquiv.withZero.symm e, fun {a b} => by simp⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext x; cases x <;> simp

/-- Any linearly ordered group with zero is isomorphic to adjoining `0` to the units of itself. -/
@[simps!]
/--
Definition of `OrderMonoidIso.withZeroUnits` / `OrderMonoidIso.withZeroUnits` 的定义

English:
definition OrderMonoidIso.withZeroUnits
  signature: {α : Type*} [LinearOrderedCommGroupWithZero α]
  body: WithZero.withZeroUnitsEquiv
  map_le_map_iff' {a b} := by
    cases a <;> cases b <;>
    simp

中文:
定义 OrderMonoidIso.withZeroUnits
  签名: {α : 类型} [带零LinearOrderedComm群 α]
  定义体: WithZero.withZeroUnitsEquiv
  map_le_map_iff' {a b} := by
    cases a <;> cases b <;>
    simp

Depends on / 依赖: WithZero, WithZero.withZeroUnitsEquiv, withZeroUnitsEquiv
-/
def OrderMonoidIso.withZeroUnits {α : Type*} [LinearOrderedCommGroupWithZero α]
    [DecidablePred (fun a : α => a = 0)] :
    WithZero αˣ ≃*o α where
  toMulEquiv := WithZero.withZeroUnitsEquiv
  map_le_map_iff' {a b} := by
    cases a <;> cases b <;>
    simp
