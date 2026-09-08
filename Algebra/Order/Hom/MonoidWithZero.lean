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

/-- `OrderMonoidWithZeroHom α β` is the type of functions `α → β` that preserve
the `MonoidWithZero` structure.

`OrderMonoidWithZeroHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : α →+ β)`,
you should parameterize over
`(F : Type*) [FunLike F M N] [MonoidWithZeroHomClass F M N] [OrderHomClass F M N] (f : F)`. -/
/-
**OrderMonoidWithZeroHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) →   (β : Type u_7) → [Preorder α] → [Preorder β] → [MulZero
OneClass α] → [MulZeroOneClass β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderMonoidWithZeroHom α β` is the type of functions `α → β` that preserve
the `MonoidWithZero` structure.

`OrderMonoidWithZeroHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : α →+ β)`,
you should parameterize over
`(F : Type*) [FunLike F M N] [MonoidWithZeroHomClass F M N] [OrderHomClass F M N
] (f : F)`.
-/
structure OrderMonoidWithZeroHom (α β : Type*) [Preorder α] [Preorder β] [MulZeroOneClass α]
  [MulZeroOneClass β] extends α →*₀ β where
  /-- An `OrderMonoidWithZeroHom` is a monotone function. -/
  monotone' : Monotone toFun

/-- Infix notation for `OrderMonoidWithZeroHom`. -/
infixr:25 " →*₀o " => OrderMonoidWithZeroHom

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
/-
**OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom** 是 Mathlib 中的一个定义，位于命名空间
 ``。
形式化陈述：OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom [OrderHomClass F α β]
 [MonoidWithZeroHomClass F α β] (f : F) : α ->*₀o β
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHomClass.monotone`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [
inst : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomCla
ss F α β] (f…

--- 原说明 ---
Turn an element of a type `F`
satisfying `OrderHomClass F α β` and `MonoidWithZeroHomClass F α β`
into an actual `OrderMonoidWithZeroHom`.
This is declared as the default coercion from `F` to `α →+*₀o β`.
TODO: Following [#mathlib4 > Mathlib's morphism hierarchy]
(https://leanprover.zulipchat.com/#narrow/channel/287929-
mathlib4/topic/Mathlib.27s.20morphism.20hierarchy/with/554383157),
rename this to `OrderMonoidWithZeroHom.ofClass` and remove `@[coe]` tag.
-/
def OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom [OrderHomClass F α β]
    [MonoidWithZeroHomClass F α β] (f : F) : α →*₀o β :=
{ (.ofClass f : α →*₀ β) with monotone' := OrderHomClass.monotone f }

end

variable [FunLike F α β]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [OrderHomClass F α β] [MonoidWithZeroHomClass F α β] : CoeTC F (α →*₀o β) :=
  ⟨OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom⟩

end MonoidWithZero

namespace OrderMonoidWithZeroHom

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulZeroOneClass α] [MulZeroOneClass β]
  [MulZeroOneClass γ] [MulZeroOneClass δ] {f g : α →*₀o β}

/-
**OrderMonoidWithZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderMonoidWithZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (α →*₀o β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr

initialize_simps_projections OrderMonoidWithZeroHom (toFun → apply, -toMonoidWithZeroHom)
/-
**OrderMonoidWithZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderMonoidWithZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidWithZeroHomClass (α →*₀o β) α β where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'
/-
**OrderMonoidWithZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderMonoidWithZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderHomClass (α →*₀o β) α β where
  map_rel f _ _ h := f.monotone' h

-- Other lemmas should be accessed through the `FunLike` API
@[ext]
/-
**OrderMonoidWithZeroHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZeroHom`。
形式化陈述：ext (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
/-
**OrderMonoidWithZeroHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWith
ZeroHom`。
形式化陈述：toFun_eq_coe (f : α ->*₀o β) : f.toFun = (f : α -> β)
参数：f : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (f : α →*₀o β) : f.toFun = (f : α → β) :=
  rfl

@[simp]
/-
**OrderMonoidWithZeroHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZeroHo
m`。
形式化陈述：coe_mk (f : α ->*₀ β) (h) : (OrderMonoidWithZeroHom.mk f h : α -> β) = f
参数：f : α ->*₀ β；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : α →*₀ β) (h) : (OrderMonoidWithZeroHom.mk f h : α → β) = f :=
  rfl

@[simp]
/-
**OrderMonoidWithZeroHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZeroHo
m`。
形式化陈述：mk_coe (f : α ->*₀o β) (h) : OrderMonoidWithZeroHom.mk (.ofClass f) h = f
参数：f : α ->*₀o β；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.instMonoidWithZeroHomClass`：∀ {α : Type u_2} {β :
 Type u_3} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α
]   [inst_3 : MulZeroOneClass β], Monoi…
-/
theorem mk_coe (f : α →*₀o β) (h) : OrderMonoidWithZeroHom.mk (.ofClass f) h = f := rfl

/-- Reinterpret an ordered monoid with zero homomorphism as an order monoid homomorphism. -/
/-
**OrderMonoidWithZeroHom.toOrderMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoid
WithZeroHom`。
形式化陈述：toOrderMonoidHom (f : α ->*₀o β) : α ->*o β
参数：f : α ->*₀o β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α]   [inst_3 : Mul
ZeroOneClass β] (self …

--- 原说明 ---
Reinterpret an ordered monoid with zero homomorphism as an order monoid homomorp
hism.
-/
def toOrderMonoidHom (f : α →*₀o β) : α →*o β :=
  { f with }

@[simp]
/-
**OrderMonoidWithZeroHom.coe_monoidWithZeroHom** 是 Mathlib 中的一个定理，位于命名空间 `OrderM
onoidWithZeroHom`。
形式化陈述：coe_monoidWithZeroHom (f : α ->*₀o β) : ⇑(.ofClass f : α ->*₀ β) = f
参数：f : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.instMonoidWithZeroHomClass`：∀ {α : Type u_2} {β :
 Type u_3} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α
]   [inst_3 : MulZeroOneClass β], Monoi…
-/
theorem coe_monoidWithZeroHom (f : α →*₀o β) : ⇑(.ofClass f : α →*₀ β) = f :=
  rfl

@[simp]
/-
**OrderMonoidWithZeroHom.coe_orderMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `OrderMono
idWithZeroHom`。
形式化陈述：coe_orderMonoidHom (f : α ->*₀o β) : ⇑(f : α ->*o β) = f
参数：f : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3
} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α]   [inst
_3 : MulZeroOneClass β], Order…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `OrderMonoidWithZeroHom.instMonoidWithZeroHomClass`：∀ {α : Type u_2} {β :
 Type u_3} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α
]   [inst_3 : MulZeroOneClass β], Monoi…
-/
theorem coe_orderMonoidHom (f : α →*₀o β) : ⇑(f : α →*o β) = f :=
  rfl
/-
**OrderMonoidWithZeroHom.toOrderMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `O
rderMonoidWithZeroHom`。
形式化陈述：toOrderMonoidHom_injective : Injective (toOrderMonoidHom : _ -> α ->*o β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem toOrderMonoidHom_injective : Injective (toOrderMonoidHom : _ → α →*o β) := fun f g h =>
  ext <| by convert! DFunLike.ext_iff.1 h using 0
/-
**OrderMonoidWithZeroHom.toMonoidWithZeroHom_injective** 是 Mathlib 中的一个定理，位于命名空间
 `OrderMonoidWithZeroHom`。
形式化陈述：toMonoidWithZeroHom_injective : Injective (toMonoidWithZeroHom : _ -> α ->
*₀ β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem toMonoidWithZeroHom_injective : Injective (toMonoidWithZeroHom : _ → α →*₀ β) :=
  fun f g h => ext <| by convert! DFunLike.ext_iff.1 h using 0

/-- Copy of an `OrderMonoidWithZeroHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
/-
**OrderMonoidWithZeroHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidWithZeroHom`
。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Preorder α] →       [inst_
1 : Preorder β] →         [inst_2 : MulZeroOneClass α] → [inst_3 : MulZeroOneCla
ss β] → (f : α →*₀o β) → (f' : α → β) → f' = ⇑f → α →*o β
参数：f : α →*₀o β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of an `OrderMonoidWithZeroHom` with a new `toFun` equal to the old one. Use
ful to fix
definitional equalities.
-/
protected def copy (f : α →*₀o β) (f' : α → β) (h : f' = f) : α →*o β :=
  { f.toOrderMonoidHom.copy f' h, f.toMonoidWithZeroHom.copy f' h with toFun := f' }

@[simp]
/-
**OrderMonoidWithZeroHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZero
Hom`。
形式化陈述：coe_copy (f : α ->*₀o β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f'
参数：f : α ->*₀o β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : α →*₀o β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**OrderMonoidWithZeroHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZeroH
om`。
形式化陈述：copy_eq (f : α ->*₀o β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : α ->*₀o β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
· 使用定理 `OrderMonoidWithZeroHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3
} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α]   [inst
_3 : MulZeroOneClass β], Order…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `OrderMonoidWithZeroHom.instMonoidWithZeroHomClass`：∀ {α : Type u_2} {β :
 Type u_3} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α
]   [inst_3 : MulZeroOneClass β], Monoi…
-/
theorem copy_eq (f : α →*₀o β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- The identity map as an ordered monoid with zero homomorphism. -/
/-
**OrderMonoidWithZeroHom.id** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidWithZeroHom`。
形式化陈述：(α : Type u_2) → [inst : Preorder α] → [inst_1 : MulZeroOneClass α] → α →*
₀o α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preorder α] 
[inst_1 : Preorder β] (self : α →o β), Monotone self.toFun

--- 原说明 ---
The identity map as an ordered monoid with zero homomorphism.
-/
protected def id : α →*₀o α :=
  { MonoidWithZeroHom.id α, OrderHom.id with }

@[simp, norm_cast]
/-
**OrderMonoidWithZeroHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZeroHo
m`。
形式化陈述：coe_id : ⇑(OrderMonoidWithZeroHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(OrderMonoidWithZeroHom.id α) = id :=
  rfl
/-
**OrderMonoidWithZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderMonoidWithZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (α →*₀o α) :=
  ⟨OrderMonoidWithZeroHom.id α⟩

variable {α}

/-- Composition of `OrderMonoidWithZeroHom`s as an `OrderMonoidWithZeroHom`. -/
/-
**OrderMonoidWithZeroHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidWithZeroHom`
。
形式化陈述：comp (f : β ->*₀o γ) (g : α ->*₀o β) : α ->*₀o γ
参数：f : β ->*₀o γ；g : α ->*₀o β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.instMonoidWithZeroHomClass`：∀ {α : Type u_2} {β :
 Type u_3} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α
]   [inst_3 : MulZeroOneClass β], Monoi…
· 使用定理 `OrderMonoidWithZeroHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3
} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α]   [inst
_3 : MulZeroOneClass β], Order…

--- 原说明 ---
Composition of `OrderMonoidWithZeroHom`s as an `OrderMonoidWithZeroHom`.
-/
def comp (f : β →*₀o γ) (g : α →*₀o β) : α →*₀o γ :=
  { (.ofClass f : β →*₀ γ).comp (.ofClass g), f.toOrderMonoidHom.comp (g : α →*o β) with }

@[simp]
/-
**OrderMonoidWithZeroHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZero
Hom`。
形式化陈述：coe_comp (f : β ->*₀o γ) (g : α ->*₀o β) : (f.comp g : α -> γ) = f ∘ g
参数：f : β ->*₀o γ；g : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : β →*₀o γ) (g : α →*₀o β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
/-
**OrderMonoidWithZeroHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZe
roHom`。
形式化陈述：comp_apply (f : β ->*₀o γ) (g : α ->*₀o β) (a : α) : (f.comp g) a = f (g a
)
参数：f : β ->*₀o γ；g : α ->*₀o β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : β →*₀o γ) (g : α →*₀o β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
/-
**OrderMonoidWithZeroHom.ofClass_comp_monoidWithZeroHom** 是 Mathlib 中的一个定理，位于命名空
间 `OrderMonoidWithZeroHom`。
形式化陈述：ofClass_comp_monoidWithZeroHom (f : β ->*₀o γ) (g : α ->*₀o β) : .ofClass 
(f.comp g) = (.ofClass f : β ->*₀ γ).comp (.ofClass g)
参数：f : β ->*₀o γ；g : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.instMonoidWithZeroHomClass`：∀ {α : Type u_2} {β :
 Type u_3} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α
]   [inst_3 : MulZeroOneClass β], Monoi…
-/
theorem ofClass_comp_monoidWithZeroHom (f : β →*₀o γ) (g : α →*₀o β) :
    .ofClass (f.comp g) = (.ofClass f : β →*₀ γ).comp (.ofClass g) :=
  rfl
/-
**OrderMonoidWithZeroHom.coe_comp_orderMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Orde
rMonoidWithZeroHom`。
形式化陈述：coe_comp_orderMonoidHom (f : β ->*₀o γ) (g : α ->*₀o β) : (f.comp g : α ->
*o γ) = (f : β ->*o γ).comp g
参数：f : β ->*₀o γ；g : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3
} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α]   [inst
_3 : MulZeroOneClass β], Order…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `OrderMonoidWithZeroHom.instMonoidWithZeroHomClass`：∀ {α : Type u_2} {β :
 Type u_3} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α
]   [inst_3 : MulZeroOneClass β], Monoi…
-/
theorem coe_comp_orderMonoidHom (f : β →*₀o γ) (g : α →*₀o β) :
    (f.comp g : α →*o γ) = (f : β →*o γ).comp g :=
  rfl

@[simp]
/-
**OrderMonoidWithZeroHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZe
roHom`。
形式化陈述：comp_assoc (f : γ ->*₀o δ) (g : β ->*₀o γ) (h : α ->*₀o β) : (f.comp g).co
mp h = f.comp (g.comp h)
参数：f : γ ->*₀o δ；g : β ->*₀o γ；h : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : γ →*₀o δ) (g : β →*₀o γ) (h : α →*₀o β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**OrderMonoidWithZeroHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZeroH
om`。
形式化陈述：comp_id (f : α ->*₀o β) : f.comp (OrderMonoidWithZeroHom.id α) = f
参数：f : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_id (f : α →*₀o β) : f.comp (OrderMonoidWithZeroHom.id α) = f := rfl

@[simp]
/-
**OrderMonoidWithZeroHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZeroH
om`。
形式化陈述：id_comp (f : α ->*₀o β) : (OrderMonoidWithZeroHom.id β).comp f = f
参数：f : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_comp (f : α →*₀o β) : (OrderMonoidWithZeroHom.id β).comp f = f := rfl

@[simp]
/-
**OrderMonoidWithZeroHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWith
ZeroHom`。
形式化陈述：cancel_right {g₁ g₂ : β ->*₀o γ} {f : α ->*₀o β} (hf : Function.Surjective
 f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem cancel_right {g₁ g₂ : β →*₀o γ} {f : α →*₀o β} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun _ => by congr⟩

@[simp]
/-
**OrderMonoidWithZeroHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZ
eroHom`。
形式化陈述：cancel_left {g : β ->*₀o γ} {f₁ f₂ : α ->*₀o β} (hg : Function.Injective g
) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Function.Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderMonoidWithZeroHom.comp_apply`：comp_apply (f : β ->*₀o γ) (g : α ->*
₀o β) (a : α) : (f.comp g) a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : β →*₀o γ} {f₁ f₂ : α →*₀o β} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end Preorder

section Mul

variable [LinearOrderedCommMonoidWithZero α] [LinearOrderedCommMonoidWithZero β]
  [LinearOrderedCommMonoidWithZero γ]

/-- For two ordered monoid morphisms `f` and `g`, their product is the ordered monoid morphism
sending `a` to `f a * g a`. -/
/-
**OrderMonoidWithZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderMonoidWithZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For two ordered monoid morphisms `f` and `g`, their product is the ordered monoi
d morphism
sending `a` to `f a * g a`.
-/
instance : Mul (α →*₀o β) :=
  ⟨ fun f g => {(.ofClass f : α →*₀ β) * (.ofClass g : α →*₀ β) with
      monotone' := f.monotone'.mul' g.monotone'} ⟩

@[simp]
/-
**OrderMonoidWithZeroHom.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZeroH
om`。
形式化陈述：coe_mul (f g : α ->*₀o β) : ⇑(f * g) = f * g
参数：f g : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (f g : α →*₀o β) : ⇑(f * g) = f * g :=
  rfl

@[simp]
/-
**OrderMonoidWithZeroHom.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZer
oHom`。
形式化陈述：mul_apply (f g : α ->*₀o β) (a : α) : (f * g) a = f a * g a
参数：f g : α ->*₀o β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (f g : α →*₀o β) (a : α) : (f * g) a = f a * g a :=
  rfl
/-
**OrderMonoidWithZeroHom.mul_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZero
Hom`。
形式化陈述：mul_comp (g₁ g₂ : β ->*₀o γ) (f : α ->*₀o β) : (g₁ * g₂).comp f = g₁.comp 
f * g₂.comp f
参数：g₁ g₂ : β ->*₀o γ；f : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_comp (g₁ g₂ : β →*₀o γ) (f : α →*₀o β) : (g₁ * g₂).comp f = g₁.comp f * g₂.comp f :=
  rfl
/-
**OrderMonoidWithZeroHom.comp_mul** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZero
Hom`。
形式化陈述：comp_mul (g : β ->*₀o γ) (f₁ f₂ : α ->*₀o β) : g.comp (f₁ * f₂) = g.comp f
₁ * g.comp f₂
参数：g : β ->*₀o γ；f₁ f₂ : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `OrderMonoidWithZeroHom.instMonoidWithZeroHomClass`：∀ {α : Type u_2} {β :
 Type u_3} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α
]   [inst_3 : MulZeroOneClass β], Monoi…
-/
theorem comp_mul (g : β →*₀o γ) (f₁ f₂ : α →*₀o β) : g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ :=
  ext fun _ => map_mul g _ _

end Mul

section LinearOrderedCommMonoidWithZero

variable {hα : Preorder α} {hα' : MulZeroOneClass α} {hβ : Preorder β} {hβ' : MulZeroOneClass β}
  {hγ : Preorder γ} {hγ' : MulZeroOneClass γ}

@[simp]
/-
**OrderMonoidWithZeroHom.toMonoidWithZeroHom_eq_ofClass** 是 Mathlib 中的一个定理，位于命名空
间 `OrderMonoidWithZeroHom`。
形式化陈述：toMonoidWithZeroHom_eq_ofClass (f : α ->*₀o β) : f.toMonoidWithZeroHom = .
ofClass f
参数：f : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMonoidWithZeroHom_eq_ofClass (f : α →*₀o β) : f.toMonoidWithZeroHom = .ofClass f := by
  rfl

@[simp]
/-
**OrderMonoidWithZeroHom.ofClass_mk** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidWithZe
roHom`。
形式化陈述：ofClass_mk (f : α ->*₀ β) (hf : Monotone f) : .ofClass (OrderMonoidWithZer
oHom.mk f hf) = f
参数：f : α ->*₀ β；hf : Monotone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.instMonoidWithZeroHomClass`：∀ {α : Type u_2} {β :
 Type u_3} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α
]   [inst_3 : MulZeroOneClass β], Monoi…
-/
theorem ofClass_mk (f : α →*₀ β) (hf : Monotone f) :
    .ofClass (OrderMonoidWithZeroHom.mk f hf) = f := by
  rfl

@[simp]
/-
**OrderMonoidWithZeroHom.ofClass_comp** 是 Mathlib 中的一个引理，位于命名空间 `OrderMonoidWith
ZeroHom`。
形式化陈述：ofClass_comp (f : β ->*₀o γ) (g : α ->*₀o β) : .ofClass (f.comp g) = (.ofC
lass f : β ->*₀ γ).comp (.ofClass g)
参数：f : β ->*₀o γ；g : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.instMonoidWithZeroHomClass`：∀ {α : Type u_2} {β :
 Type u_3} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α
]   [inst_3 : MulZeroOneClass β], Monoi…
-/
lemma ofClass_comp (f : β →*₀o γ) (g : α →*₀o β) :
    .ofClass (f.comp g) = (.ofClass f : β →*₀ γ).comp (.ofClass g) :=
  rfl

@[simp]
/-
**OrderMonoidWithZeroHom.toOrderMonoidHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Orde
rMonoidWithZeroHom`。
形式化陈述：toOrderMonoidHom_eq_coe (f : α ->*₀o β) : f.toOrderMonoidHom = f
参数：f : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOrderMonoidHom_eq_coe (f : α →*₀o β) : f.toOrderMonoidHom = f :=
  rfl

@[simp]
/-
**OrderMonoidWithZeroHom.toOrderMonoidHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `OrderM
onoidWithZeroHom`。
形式化陈述：toOrderMonoidHom_comp (f : β ->*₀o γ) (g : α ->*₀o β) : (f.comp g : α ->*o
 γ) = (f : β ->*o γ).comp g
参数：f : β ->*₀o γ；g : α ->*₀o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3
} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α]   [inst
_3 : MulZeroOneClass β], Order…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `OrderMonoidWithZeroHom.instMonoidWithZeroHomClass`：∀ {α : Type u_2} {β :
 Type u_3} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : MulZeroOneClass α
]   [inst_3 : MulZeroOneClass β], Monoi…
-/
lemma toOrderMonoidHom_comp (f : β →*₀o γ) (g : α →*₀o β) :
    (f.comp g : α →*o γ) = (f : β →*o γ).comp g :=
  rfl

end LinearOrderedCommMonoidWithZero

end OrderMonoidWithZeroHom

set_option backward.isDefEq.respectTransparency false in
/-- Any ordered group is isomorphic to the units of itself adjoined with `0`. -/
@[simps! -isSimp]
/-
**OrderMonoidIso.unitsWithZero** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderMonoidIso.unitsWithZero {α : Type*} [Group α] [Preorder α] : (WithZer
o α)ˣ ≃*o α where toMulEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any ordered group is isomorphic to the units of itself adjoined with `0`.
-/
def OrderMonoidIso.unitsWithZero {α : Type*} [Group α] [Preorder α] : (WithZero α)ˣ ≃*o α where
  toMulEquiv := WithZero.unitsWithZeroEquiv
  map_le_map_iff' {a b} := by simp [WithZero.unitsWithZeroEquiv]

/-- A version of `Equiv.optionCongr` for `WithZero` on `OrderMonoidIso`. -/
@[simps!]
/-
**OrderMonoidIso.withZero** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderMonoidIso.withZero {G H : Type*} [Group G] [PartialOrder G] [Group H]
 [PartialOrder H] : (G ≃*o H) ≃ (WithZero G ≃*o WithZero H) where toFun e
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A version of `Equiv.optionCongr` for `WithZero` on `OrderMonoidIso`.
-/
def OrderMonoidIso.withZero {G H : Type*}
    [Group G] [PartialOrder G] [Group H] [PartialOrder H] :
    (G ≃*o H) ≃ (WithZero G ≃*o WithZero H) where
  toFun e := ⟨e.toMulEquiv.withZero, fun {a b} ↦ by cases a <;> cases b <;> simp⟩
  invFun e := ⟨MulEquiv.withZero.symm e, fun {a b} ↦ by simp⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext x; cases x <;> simp

/-- Any linearly ordered group with zero is isomorphic to adjoining `0` to the units of itself. -/
@[simps!]
/-
**OrderMonoidIso.withZeroUnits** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderMonoidIso.withZeroUnits {α : Type*} [LinearOrderedCommGroupWithZero α
] [DecidablePred (fun a : α => a = 0)] : WithZero αˣ ≃*o α where toMulEquiv
参数：fun a : α => a = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any linearly ordered group with zero is isomorphic to adjoining `0` to the units
 of itself.
-/
def OrderMonoidIso.withZeroUnits {α : Type*} [LinearOrderedCommGroupWithZero α]
    [DecidablePred (fun a : α ↦ a = 0)] :
    WithZero αˣ ≃*o α where
  toMulEquiv := WithZero.withZeroUnitsEquiv
  map_le_map_iff' {a b} := by
    cases a <;> cases b <;>
    simp
