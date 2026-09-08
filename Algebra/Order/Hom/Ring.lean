/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.Algebra.Ring.Equiv

/-!
# Ordered ring homomorphisms

Homomorphisms between ordered (semi)rings that respect the ordering.

## Main definitions

* `OrderRingHom` : Monotone semiring homomorphisms.
* `OrderRingIso` : Monotone semiring isomorphisms.

## Notation

* `→+*o`: Ordered ring homomorphisms.
* `≃+*o`: Ordered ring isomorphisms.

## Implementation notes

This file used to define typeclasses for order-preserving ring homomorphisms and isomorphisms.
In https://github.com/leanprover-community/mathlib4/pull/10544, we migrated from assumptions like `[FunLike F R S] [OrderRingHomClass F R S]`
to assumptions like `[FunLike F R S] [OrderHomClass F R S] [RingHomClass F R S]`,
making some typeclasses and instances irrelevant.

## Tags

ordered ring homomorphism, order homomorphism
-/

@[expose] public section

assert_not_exists FloorRing Archimedean

open Function

variable {F α β γ δ : Type*}

/-- `OrderRingHom α β`, denoted `α →+*o β`,
is the type of monotone semiring homomorphisms from `α` to `β`.

When possible, instead of parametrizing results over `(f : OrderRingHom α β)`,
you should parametrize over `(F : Type*) [OrderRingHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `OrderRingHomClass`. -/
/-
**OrderRingHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) →   (β : Type u_7) → [NonAssocSemiring α] → [Preorder α] → 
[NonAssocSemiring β] → [Preorder β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderRingHom α β`, denoted `α →+*o β`,
is the type of monotone semiring homomorphisms from `α` to `β`.

When possible, instead of parametrizing results over `(f : OrderRingHom α β)`,
you should parametrize over `(F : Type*) [OrderRingHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `OrderRingHomClass`.
-/
structure OrderRingHom (α β : Type*) [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β]
  [Preorder β] extends α →+* β where
  /-- The proposition that the function preserves the order. -/
  monotone' : Monotone toFun

/-- Reinterpret an ordered ring homomorphism as a ring homomorphism. -/
add_decl_doc OrderRingHom.toRingHom

@[inherit_doc]
infixl:25 " →+*o " => OrderRingHom

/-- `OrderRingIso α β`, denoted as `α ≃+*o β`,
is the type of order-preserving semiring isomorphisms between `α` and `β`.

When possible, instead of parametrizing results over `(f : OrderRingIso α β)`,
you should parametrize over `(F : Type*) [OrderRingIsoClass F α β] (f : F)`.

When you extend this structure, make sure to extend `OrderRingIsoClass`. -/
/-
**OrderRingIso** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [Mul α] → [Add α] → [Mul β] → [Add β] → 
[LE α] → [LE β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderRingIso α β`, denoted as `α ≃+*o β`,
is the type of order-preserving semiring isomorphisms between `α` and `β`.

When possible, instead of parametrizing results over `(f : OrderRingIso α β)`,
you should parametrize over `(F : Type*) [OrderRingIsoClass F α β] (f : F)`.

When you extend this structure, make sure to extend `OrderRingIsoClass`.
-/
structure OrderRingIso (α β : Type*) [Mul α] [Add α] [Mul β] [Add β] [LE α] [LE β] extends
  α ≃+* β where
  /-- The proposition that the function preserves the order bijectively. -/
  map_le_map_iff' {a b : α} : toFun a ≤ toFun b ↔ a ≤ b

@[inherit_doc]
infixl:25 " ≃+*o " => OrderRingIso

-- See module docstring for details

section Hom

variable [FunLike F α β]

/-- Turn an element of a type `F` satisfying `OrderHomClass F α β` and `RingHomClass F α β`
into an actual `OrderRingHom`.
This is declared as the default coercion from `F` to `α →+*o β`. -/
@[coe]
/-
**OrderRingHomClass.toOrderRingHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderRingHomClass.toOrderRingHom [NonAssocSemiring α] [Preorder α] [NonAss
ocSemiring β] [Preorder β] [OrderHomClass F α β] [RingHomClass F α β] (f : F) : 
α ->+*o β
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHomClass.monotone`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [
inst : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomCla
ss F α β] (f…

--- 原说明 ---
Turn an element of a type `F` satisfying `OrderHomClass F α β` and `RingHomClass
 F α β`
into an actual `OrderRingHom`.
This is declared as the default coercion from `F` to `α →+*o β`.
-/
def OrderRingHomClass.toOrderRingHom [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β]
    [Preorder β] [OrderHomClass F α β] [RingHomClass F α β] (f : F) : α →+*o β :=
  { (f : α →+* β) with monotone' := OrderHomClass.monotone f }

/-- Any type satisfying `OrderRingHomClass` can be cast into `OrderRingHom` via
  `OrderRingHomClass.toOrderRingHom`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type satisfying `OrderRingHomClass` can be cast into `OrderRingHom` via
  `OrderRingHomClass.toOrderRingHom`.
-/
instance [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β] [Preorder β]
    [OrderHomClass F α β] [RingHomClass F α β] : CoeTC F (α →+*o β) :=
  ⟨OrderRingHomClass.toOrderRingHom⟩

end Hom

section Equiv

variable [EquivLike F α β]

/-- Turn an element of a type `F` satisfying `OrderIsoClass F α β` and `RingEquivClass F α β`
into an actual `OrderRingIso`.
This is declared as the default coercion from `F` to `α ≃+*o β`. -/
@[coe]
/-
**OrderRingIsoClass.toOrderRingIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderRingIsoClass.toOrderRingIso [Mul α] [Add α] [LE α] [Mul β] [Add β] [L
E β] [OrderIsoClass F α β] [RingEquivClass F α β] (f : F) : α ≃+*o β
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIsoClass.map_le_map_iff`：∀ {F : Type u_6} {α : outParam (Type u_7)}
 {β : outParam (Type u_8)} {inst : LE α} {inst_1 : LE β}   {inst_2 : EquivLike F
 α β} [self : Orde…

--- 原说明 ---
Turn an element of a type `F` satisfying `OrderIsoClass F α β` and `RingEquivCla
ss F α β`
into an actual `OrderRingIso`.
This is declared as the default coercion from `F` to `α ≃+*o β`.
-/
def OrderRingIsoClass.toOrderRingIso [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β]
    [OrderIsoClass F α β] [RingEquivClass F α β] (f : F) : α ≃+*o β :=
  { (RingEquivClass.toRingEquiv f : α ≃+* β) with map_le_map_iff' := map_le_map_iff f }

/-- Any type satisfying `OrderRingIsoClass` can be cast into `OrderRingIso` via
  `OrderRingIsoClass.toOrderRingIso`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type satisfying `OrderRingIsoClass` can be cast into `OrderRingIso` via
  `OrderRingIsoClass.toOrderRingIso`.
-/
instance [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [OrderIsoClass F α β]
    [RingEquivClass F α β] : CoeTC F (α ≃+*o β) :=
  ⟨OrderRingIsoClass.toOrderRingIso⟩

end Equiv

/-! ### Ordered ring homomorphisms -/

namespace OrderRingHom

variable [NonAssocSemiring α] [Preorder α]

section Preorder

variable [NonAssocSemiring β] [Preorder β] [NonAssocSemiring γ] [Preorder γ] [NonAssocSemiring δ]
  [Preorder δ]

/-- Reinterpret an ordered ring homomorphism as an ordered additive monoid homomorphism. -/
/-
**OrderRingHom.toOrderAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `OrderRingHom`。
形式化陈述：toOrderAddMonoidHom (f : α ->+*o β) : α ->+o β
参数：f : α ->+*o β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : NonAssoc
Semiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3 : Preo
rder β] (sel…

--- 原说明 ---
Reinterpret an ordered ring homomorphism as an ordered additive monoid homomorph
ism.
-/
def toOrderAddMonoidHom (f : α →+*o β) : α →+o β :=
  { f with }

/-- Reinterpret an ordered ring homomorphism as an order homomorphism. -/
/-
**OrderRingHom.toOrderMonoidWithZeroHom** 是 Mathlib 中的一个定义，位于命名空间 `OrderRingHom`
。
形式化陈述：toOrderMonoidWithZeroHom (f : α ->+*o β) : α ->*₀o β
参数：f : α ->+*o β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : NonAssoc
Semiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3 : Preo
rder β] (sel…

--- 原说明 ---
Reinterpret an ordered ring homomorphism as an order homomorphism.
-/
def toOrderMonoidWithZeroHom (f : α →+*o β) : α →*₀o β :=
  { f with }
/-
**OrderRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (α →+*o β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    cases f; cases g; congr
    exact DFunLike.coe_injective h
/-
**OrderRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderHomClass (α →+*o β) α β where
  map_rel f _ _ h := f.monotone' h
/-
**OrderRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RingHomClass (α →+*o β) α β where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
/-
**OrderRingHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：toFun_eq_coe (f : α ->+*o β) : f.toFun = f
参数：f : α ->+*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (f : α →+*o β) : f.toFun = f :=
  rfl

@[ext]
/-
**OrderRingHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：ext {f g : α ->+*o β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : α →+*o β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[simp]
/-
**OrderRingHom.toRingHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：toRingHom_eq_coe (f : α ->+*o β) : f.toRingHom = f
参数：f : α ->+*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
theorem toRingHom_eq_coe (f : α →+*o β) : f.toRingHom = f :=
  RingHom.ext fun _ => rfl

@[simp]
/-
**OrderRingHom.toOrderAddMonoidHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHo
m`。
形式化陈述：toOrderAddMonoidHom_eq_coe (f : α ->+*o β) : f.toOrderAddMonoidHom = f
参数：f : α ->+*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOrderAddMonoidHom_eq_coe (f : α →+*o β) : f.toOrderAddMonoidHom = f :=
  rfl

@[simp]
/-
**OrderRingHom.toOrderMonoidWithZeroHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderR
ingHom`。
形式化陈述：toOrderMonoidWithZeroHom_eq_coe (f : α ->+*o β) : f.toOrderMonoidWithZeroH
om = f
参数：f : α ->+*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOrderMonoidWithZeroHom_eq_coe (f : α →+*o β) : f.toOrderMonoidWithZeroHom = f :=
  rfl

@[simp]
/-
**OrderRingHom.coe_coe_ringHom** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：coe_coe_ringHom (f : α ->+*o β) : ⇑(f : α ->+* β) = f
参数：f : α ->+*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
theorem coe_coe_ringHom (f : α →+*o β) : ⇑(f : α →+* β) = f :=
  rfl

@[simp]
/-
**OrderRingHom.coe_coe_orderAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom
`。
形式化陈述：coe_coe_orderAddMonoidHom (f : α ->+*o β) : ⇑(f : α ->+o β) = f
参数：f : α ->+*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
NonAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_
3 : Preorder β], Ord…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
theorem coe_coe_orderAddMonoidHom (f : α →+*o β) : ⇑(f : α →+o β) = f :=
  rfl

@[simp]
/-
**OrderRingHom.coe_coe_orderMonoidWithZeroHom** 是 Mathlib 中的一个定理，位于命名空间 `OrderRi
ngHom`。
形式化陈述：coe_coe_orderMonoidWithZeroHom (f : α ->+*o β) : ⇑(f : α ->*₀o β) = f
参数：f : α ->+*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
NonAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_
3 : Preorder β], Ord…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
theorem coe_coe_orderMonoidWithZeroHom (f : α →+*o β) : ⇑(f : α →*₀o β) = f :=
  rfl

@[norm_cast]
/-
**OrderRingHom.coe_ringHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：coe_ringHom_apply (f : α ->+*o β) (a : α) : (f : α ->+* β) a = f a
参数：f : α ->+*o β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
theorem coe_ringHom_apply (f : α →+*o β) (a : α) : (f : α →+* β) a = f a :=
  rfl

@[norm_cast]
/-
**OrderRingHom.coe_orderAddMonoidHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingH
om`。
形式化陈述：coe_orderAddMonoidHom_apply (f : α ->+*o β) (a : α) : (f : α ->+o β) a = f
 a
参数：f : α ->+*o β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
NonAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_
3 : Preorder β], Ord…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
theorem coe_orderAddMonoidHom_apply (f : α →+*o β) (a : α) : (f : α →+o β) a = f a :=
  rfl

@[norm_cast]
/-
**OrderRingHom.coe_orderMonoidWithZeroHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Order
RingHom`。
形式化陈述：coe_orderMonoidWithZeroHom_apply (f : α ->+*o β) (a : α) : (f : α ->*₀o β)
 a = f a
参数：f : α ->+*o β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
NonAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_
3 : Preorder β], Ord…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
theorem coe_orderMonoidWithZeroHom_apply (f : α →+*o β) (a : α) : (f : α →*₀o β) a = f a :=
  rfl

/-- Copy of an `OrderRingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**OrderRingHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `OrderRingHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : NonAssocSemiring α] →     
  [inst_1 : Preorder α] →         [inst_2 : NonAssocSemiring β] → [inst_3 : Preo
rder β] → (f : α →+*o β) → (f' : α → β) → f' = ⇑f → α →+*o β
参数：f : α →+*o β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of an `OrderRingHom` with a new `toFun` equal to the old one. Useful to fix
 definitional
equalities.
-/
protected def copy (f : α →+*o β) (f' : α → β) (h : f' = f) : α →+*o β :=
  { f.toRingHom.copy f' h, f.toOrderAddMonoidHom.copy f' h with }

@[simp]
/-
**OrderRingHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：coe_copy (f : α ->+*o β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f'
参数：f : α ->+*o β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : α →+*o β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**OrderRingHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：copy_eq (f : α ->+*o β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : α ->+*o β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : α →+*o β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- The identity as an ordered ring homomorphism. -/
/-
**OrderRingHom.id** 是 Mathlib 中的一个定义，位于命名空间 `OrderRingHom`。
形式化陈述：(α : Type u_2) → [inst : NonAssocSemiring α] → [inst_1 : Preorder α] → α →
+*o α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preorder α] 
[inst_1 : Preorder β] (self : α →o β), Monotone self.toFun

--- 原说明 ---
The identity as an ordered ring homomorphism.
-/
protected def id : α →+*o α :=
  { RingHom.id _, OrderHom.id with }
/-
**OrderRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (α →+*o α) :=
  ⟨OrderRingHom.id α⟩

@[simp, norm_cast]
/-
**OrderRingHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：coe_id : ⇑(OrderRingHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(OrderRingHom.id α) = id :=
  rfl

variable {α}

@[simp]
/-
**OrderRingHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：id_apply (a : α) : OrderRingHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : OrderRingHom.id α a = a :=
  rfl

@[simp]
/-
**OrderRingHom.coe_ringHom_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：coe_ringHom_id : (OrderRingHom.id α : α ->+* α) = RingHom.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
theorem coe_ringHom_id : (OrderRingHom.id α : α →+* α) = RingHom.id α :=
  rfl

@[simp]
/-
**OrderRingHom.coe_orderAddMonoidHom_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`
。
形式化陈述：coe_orderAddMonoidHom_id : (OrderRingHom.id α : α ->+o α) = OrderAddMonoid
Hom.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
NonAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_
3 : Preorder β], Ord…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
theorem coe_orderAddMonoidHom_id : (OrderRingHom.id α : α →+o α) = OrderAddMonoidHom.id α :=
  rfl

@[simp]
/-
**OrderRingHom.coe_orderMonoidWithZeroHom_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderRin
gHom`。
形式化陈述：coe_orderMonoidWithZeroHom_id : (OrderRingHom.id α : α ->*₀o α) = OrderMon
oidWithZeroHom.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
NonAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_
3 : Preorder β], Ord…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
theorem coe_orderMonoidWithZeroHom_id :
    (OrderRingHom.id α : α →*₀o α) = OrderMonoidWithZeroHom.id α :=
  rfl

/-- Composition of two `OrderRingHom`s as an `OrderRingHom`. -/
/-
**OrderRingHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `OrderRingHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     {γ : Type u_4} →       [inst : Non
AssocSemiring α] →         [inst_1 : Preorder α] →           [inst_2 : NonAssocS
emiring β] →             [inst_3 : Preorder β] →               [inst_4 : NonAsso
cSemiring γ] → [inst_5 : Preorder γ] → β →+*o γ → α →+*o β → α →+*o γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of two `OrderRingHom`s as an `OrderRingHom`.
-/
protected def comp (f : β →+*o γ) (g : α →+*o β) : α →+*o γ :=
  { f.toRingHom.comp g.toRingHom, f.toOrderAddMonoidHom.comp g.toOrderAddMonoidHom with }

@[simp]
/-
**OrderRingHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：coe_comp (f : β ->+*o γ) (g : α ->+*o β) : ⇑(f.comp g) = f ∘ g
参数：f : β ->+*o γ；g : α ->+*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : β →+*o γ) (g : α →+*o β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
/-
**OrderRingHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：comp_apply (f : β ->+*o γ) (g : α ->+*o β) (a : α) : f.comp g a = f (g a)
参数：f : β ->+*o γ；g : α ->+*o β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : β →+*o γ) (g : α →+*o β) (a : α) : f.comp g a = f (g a) :=
  rfl
/-
**OrderRingHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：comp_assoc (f : γ ->+*o δ) (g : β ->+*o γ) (h : α ->+*o β) : (f.comp g).co
mp h = f.comp (g.comp h)
参数：f : γ ->+*o δ；g : β ->+*o γ；h : α ->+*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : γ →+*o δ) (g : β →+*o γ) (h : α →+*o β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**OrderRingHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：comp_id (f : α ->+*o β) : f.comp (OrderRingHom.id α) = f
参数：f : α ->+*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_id (f : α →+*o β) : f.comp (OrderRingHom.id α) = f :=
  rfl

@[simp]
/-
**OrderRingHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：id_comp (f : α ->+*o β) : (OrderRingHom.id β).comp f = f
参数：f : α ->+*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_comp (f : α →+*o β) : (OrderRingHom.id β).comp f = f :=
  rfl

@[simp]
/-
**OrderRingHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：cancel_right {f₁ f₂ : β ->+*o γ} {g : α ->+*o β} (hg : Surjective g) : f₁.
comp g = f₂.comp g ↔ f₁ = f₂
参数：hg : Surjective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.ext`：ext {f g : α ->+*o β} (h : forall a, f a = g a) : f = 
g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem cancel_right {f₁ f₂ : β →+*o γ} {g : α →+*o β} (hg : Surjective g) :
    f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
  ⟨fun h => ext <| hg.forall.2 <| DFunLike.ext_iff.1 h, fun h => by rw [h]⟩

@[simp]
/-
**OrderRingHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingHom`。
形式化陈述：cancel_left {f : β ->+*o γ} {g₁ g₂ : α ->+*o β} (hf : Injective f) : f.com
p g₁ = f.comp g₂ ↔ g₁ = g₂
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.ext`：ext {f g : α ->+*o β} (h : forall a, f a = g a) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderRingHom.comp_apply`：comp_apply (f : β ->+*o γ) (g : α ->+*o β) (a :
 α) : f.comp g a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {f : β →+*o γ} {g₁ g₂ : α →+*o β} (hf : Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h => ext fun a => hf <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end Preorder

variable [NonAssocSemiring β]

/-
**OrderRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder β] : Preorder (OrderRingHom α β) :=
  Preorder.lift ((⇑) : _ → α → β)
/-
**OrderRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder β] : PartialOrder (OrderRingHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

end OrderRingHom

/-! ### Ordered ring isomorphisms -/


namespace OrderRingIso

section LE

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ]

/-- Reinterpret an ordered ring isomorphism as an order isomorphism. -/
@[coe]
/-
**OrderRingIso.toOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `OrderRingIso`。
形式化陈述：toOrderIso (f : α ≃+*o β) : α ≃o β
参数：f : α ≃+*o β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingIso.map_le_map_iff'`：∀ {α : Type u_6} {β : Type u_7} [inst : Mu
l α] [inst_1 : Add α] [inst_2 : Mul β] [inst_3 : Add β] [inst_4 : LE α]   [inst_
5 : LE β] (self : …

--- 原说明 ---
Reinterpret an ordered ring isomorphism as an order isomorphism.
-/
def toOrderIso (f : α ≃+*o β) : α ≃o β :=
  ⟨f.toRingEquiv.toEquiv, f.map_le_map_iff'⟩
/-
**OrderRingIso.** 是 Mathlib 中的一个实例，位于命名空间 `OrderRingIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (α ≃+*o β) α β where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv
/-
**OrderRingIso.** 是 Mathlib 中的一个实例，位于命名空间 `OrderRingIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderIsoClass (α ≃+*o β) α β where
  map_le_map_iff f _ _ := f.map_le_map_iff'
/-
**OrderRingIso.** 是 Mathlib 中的一个实例，位于命名空间 `OrderRingIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RingEquivClass (α ≃+*o β) α β where
  map_mul f := f.map_mul'
  map_add f := f.map_add'
/-
**OrderRingIso.** 是 Mathlib 中的一个实例，位于命名空间 `OrderRingIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (α ≃+*o β) (α ≃+* β) where coe := toRingEquiv
/-
**OrderRingIso.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：toFun_eq_coe (f : α ≃+*o β) : f.toFun = f
参数：f : α ≃+*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (f : α ≃+*o β) : f.toFun = f :=
  rfl

@[ext]
/-
**OrderRingIso.ext** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：ext {f g : α ≃+*o β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : α ≃+*o β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[simp]
/-
**OrderRingIso.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：coe_mk (e : α ≃+* β) (h) : ⇑(⟨e, h⟩ : α ≃+*o β) = e
参数：e : α ≃+* β；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (e : α ≃+* β) (h) : ⇑(⟨e, h⟩ : α ≃+*o β) = e :=
  rfl

@[simp]
/-
**OrderRingIso.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：mk_coe (e : α ≃+*o β) (h) : (⟨e, h⟩ : α ≃+*o β) = e
参数：e : α ≃+*o β；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingIso.ext`：ext {f g : α ≃+*o β} (h : forall a, f a = g a) : f = g
-/
theorem mk_coe (e : α ≃+*o β) (h) : (⟨e, h⟩ : α ≃+*o β) = e :=
  ext fun _ => rfl

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]
/-
**OrderRingIso.toRingEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：toRingEquiv_eq_coe (f : α ≃+*o β) : f.toRingEquiv = f
参数：f : α ≃+*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
-/
theorem toRingEquiv_eq_coe (f : α ≃+*o β) : f.toRingEquiv = f :=
  RingEquiv.ext fun _ => rfl

@[simp]
/-
**OrderRingIso.toOrderIso_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：toOrderIso_eq_coe (f : α ≃+*o β) : f.toOrderIso = f
参数：f : α ≃+*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `OrderRingIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
Mul α] [inst_1 : Add α] [inst_2 : LE α] [inst_3 : Mul β] [inst_4 : Add β]   [ins
t_5 : LE β], OrderIs…
-/
theorem toOrderIso_eq_coe (f : α ≃+*o β) : f.toOrderIso = f :=
  OrderIso.ext rfl

@[simp]
/-
**OrderRingIso.coe_toRingEquiv** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：coe_toRingEquiv (f : α ≃+*o β) : ⇑(f : α ≃+* β) = f
参数：f : α ≃+*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toRingEquiv (f : α ≃+*o β) : ⇑(f : α ≃+* β) = f :=
  rfl

@[simp, norm_cast]
/-
**OrderRingIso.coe_toOrderIso** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：coe_toOrderIso (f : α ≃+*o β) : DFunLike.coe (f : α ≃o β) = f
参数：f : α ≃+*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
Mul α] [inst_1 : Add α] [inst_2 : LE α] [inst_3 : Mul β] [inst_4 : Add β]   [ins
t_5 : LE β], OrderIs…
-/
theorem coe_toOrderIso (f : α ≃+*o β) : DFunLike.coe (f : α ≃o β) = f :=
  rfl

variable (α)

/-- The identity map as an ordered ring isomorphism. -/
@[refl]
/-
**OrderRingIso.refl** 是 Mathlib 中的一个定义，位于命名空间 `OrderRingIso`。
形式化陈述：(α : Type u_2) → [inst : Mul α] → [inst_1 : Add α] → [inst_2 : LE α] → α ≃
+*o α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map as an ordered ring isomorphism.
-/
protected def refl : α ≃+*o α :=
  ⟨RingEquiv.refl α, Iff.rfl⟩
/-
**OrderRingIso.** 是 Mathlib 中的一个实例，位于命名空间 `OrderRingIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (α ≃+*o α) :=
  ⟨OrderRingIso.refl α⟩

@[simp]
/-
**OrderRingIso.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：refl_apply (x : α) : OrderRingIso.refl α x = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply (x : α) : OrderRingIso.refl α x = x := by
  rfl

@[simp]
/-
**OrderRingIso.coe_ringEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：coe_ringEquiv_refl : (OrderRingIso.refl α : α ≃+* α) = RingEquiv.refl α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ringEquiv_refl : (OrderRingIso.refl α : α ≃+* α) = RingEquiv.refl α :=
  rfl

@[simp]
/-
**OrderRingIso.coe_orderIso_refl** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：coe_orderIso_refl : (OrderRingIso.refl α : α ≃o α) = OrderIso.refl α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
Mul α] [inst_1 : Add α] [inst_2 : LE α] [inst_3 : Mul β] [inst_4 : Add β]   [ins
t_5 : LE β], OrderIs…
-/
theorem coe_orderIso_refl : (OrderRingIso.refl α : α ≃o α) = OrderIso.refl α :=
  rfl

variable {α}

/-- The inverse of an ordered ring isomorphism as an ordered ring isomorphism. -/
@[symm]
/-
**OrderRingIso.symm** 是 Mathlib 中的一个定义，位于命名空间 `OrderRingIso`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Mul α] →       [inst_1 : A
dd α] → [inst_2 : LE α] → [inst_3 : Mul β] → [inst_4 : Add β] → [inst_5 : LE β] 
→ α ≃+*o β → β ≃+*o α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of an ordered ring isomorphism as an ordered ring isomorphism.
-/
protected def symm (e : α ≃+*o β) : β ≃+*o α := ⟨e.toRingEquiv.symm, by simp [← e.map_le_map_iff']⟩

/-- See Note [custom simps projection] -/
/-
**OrderRingIso.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `OrderRingIso.Simps`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Mul α] →       [inst_1 : A
dd α] → [inst_2 : LE α] → [inst_3 : Mul β] → [inst_4 : Add β] → [inst_5 : LE β] 
→ α ≃+*o β → β → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (e : α ≃+*o β) : β → α :=
  e.symm

@[simp]
/-
**OrderRingIso.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：symm_symm (e : α ≃+*o β) : e.symm.symm = e
参数：e : α ≃+*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (e : α ≃+*o β) : e.symm.symm = e := rfl
/-
**OrderRingIso.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：symm_bijective : Bijective (OrderRingIso.symm : (α ≃+*o β) -> β ≃+*o α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `OrderRingIso.symm_symm`：symm_symm (e : α ≃+*o β) : e.symm.symm = e
-/
theorem symm_bijective : Bijective (OrderRingIso.symm : (α ≃+*o β) → β ≃+*o α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/-
**OrderRingIso.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：symm_apply_apply (e : α ≃+*o β) (a : α) : e.symm (e a) = a
参数：e : α ≃+*o β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
-/
theorem symm_apply_apply (e : α ≃+*o β) (a : α) : e.symm (e a) = a :=
  e.toRingEquiv.symm_apply_apply a

@[simp]
/-
**OrderRingIso.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：apply_symm_apply (e : α ≃+*o β) (b : β) : e (e.symm b) = b
参数：e : α ≃+*o β；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
-/
theorem apply_symm_apply (e : α ≃+*o β) (b : β) : e (e.symm b) = b :=
  e.toRingEquiv.apply_symm_apply b

/-- Composition of `OrderRingIso`s as an `OrderRingIso`. -/
@[trans]
/-
**OrderRingIso.trans** 是 Mathlib 中的一个定义，位于命名空间 `OrderRingIso`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     {γ : Type u_4} →       [inst : Mul
 α] →         [inst_1 : Add α] →           [inst_2 : LE α] →             [inst_3
 : Mul β] →               [inst_4 : Add β] →                 [inst_5 : LE β] → [
inst_6 : Mul γ] → [inst_7 : Add γ] → [inst_8 : LE γ] → α ≃+*o β → β ≃+*o γ → α ≃
+*o γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `OrderRingIso`s as an `OrderRingIso`.
-/
protected def trans (f : α ≃+*o β) (g : β ≃+*o γ) : α ≃+*o γ :=
  ⟨f.toRingEquiv.trans g.toRingEquiv, (map_le_map_iff g).trans (map_le_map_iff f)⟩

/-- This lemma used to be generated by [simps] on `trans`, but the lhs of this simplifies under
simp. Removed [simps] attribute and added aux version below. -/
/-
**OrderRingIso.trans_toRingEquiv** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：trans_toRingEquiv (f : α ≃+*o β) (g : β ≃+*o γ) : (OrderRingIso.trans f g)
.toRingEquiv = RingEquiv.trans f.toRingEquiv g.toRingEquiv
参数：f : α ≃+*o β；g : β ≃+*o γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma used to be generated by [simps] on `trans`, but the lhs of this simpl
ifies under
simp. Removed [simps] attribute and added aux version below.
-/
theorem trans_toRingEquiv (f : α ≃+*o β) (g : β ≃+*o γ) :
    (OrderRingIso.trans f g).toRingEquiv = RingEquiv.trans f.toRingEquiv g.toRingEquiv :=
  rfl

/-- `simp`-normal form of `trans_toRingEquiv`. -/
@[simp]
/-
**OrderRingIso.trans_toRingEquiv_aux** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：trans_toRingEquiv_aux (f : α ≃+*o β) (g : β ≃+*o γ) : RingEquivClass.toRin
gEquiv (OrderRingIso.trans f g) = RingEquiv.trans f.toRingEquiv g.toRingEquiv
参数：f : α ≃+*o β；g : β ≃+*o γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingIso.instRingEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst :
 Mul α] [inst_1 : Add α] [inst_2 : LE α] [inst_3 : Mul β] [inst_4 : Add β]   [in
st_5 : LE β], RingEqu…

--- 原说明 ---
`simp`-normal form of `trans_toRingEquiv`.
-/
theorem trans_toRingEquiv_aux (f : α ≃+*o β) (g : β ≃+*o γ) :
    RingEquivClass.toRingEquiv (OrderRingIso.trans f g)
      = RingEquiv.trans f.toRingEquiv g.toRingEquiv :=
  rfl

@[simp]
/-
**OrderRingIso.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：trans_apply (f : α ≃+*o β) (g : β ≃+*o γ) (a : α) : f.trans g a = g (f a)
参数：f : α ≃+*o β；g : β ≃+*o γ；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (f : α ≃+*o β) (g : β ≃+*o γ) (a : α) : f.trans g a = g (f a) :=
  rfl

@[simp]
/-
**OrderRingIso.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：self_trans_symm (e : α ≃+*o β) : e.trans e.symm = OrderRingIso.refl α
参数：e : α ≃+*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingIso.ext`：ext {f g : α ≃+*o β} (h : forall a, f a = g a) : f = g
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem self_trans_symm (e : α ≃+*o β) : e.trans e.symm = OrderRingIso.refl α :=
  ext e.left_inv

@[simp]
/-
**OrderRingIso.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：symm_trans_self (e : α ≃+*o β) : e.symm.trans e = OrderRingIso.refl β
参数：e : α ≃+*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingIso.ext`：ext {f g : α ≃+*o β} (h : forall a, f a = g a) : f = g
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem symm_trans_self (e : α ≃+*o β) : e.symm.trans e = OrderRingIso.refl β :=
  ext e.right_inv

end LE

section Preorder

variable {R S : Type*} [Mul R] [Add R] [Mul S] [Add S] [Preorder R] [Preorder S]

/-
**OrderRingIso.lt_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：lt_symm_apply (e : R ≃+*o S) {x : R} {y : S} : x < e.symm y ↔ e x < y
参数：e : R ≃+*o S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
Mul α] [inst_1 : Add α] [inst_2 : LE α] [inst_3 : Mul β] [inst_4 : Add β]   [ins
t_5 : LE β], OrderIs…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrderRingIso.toOrderIso_eq_coe`：toOrderIso_eq_coe (f : α ≃+*o β) : f.toO
rderIso = f
· 使用定理 `OrderIso.lt_symm_apply`：lt_symm_apply (e : α ≃o β) {x : α} {y : β} : x <
 e.symm y ↔ e x < y
-/
theorem lt_symm_apply (e : R ≃+*o S) {x : R} {y : S} : x < e.symm y ↔ e x < y := by
  simpa using! e.toOrderIso.lt_symm_apply
/-
**OrderRingIso.symm_apply_lt** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：symm_apply_lt (e : R ≃+*o S) {x : R} {y : S} : e.symm y < x ↔ y < e x
参数：e : R ≃+*o S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
Mul α] [inst_1 : Add α] [inst_2 : LE α] [inst_3 : Mul β] [inst_4 : Add β]   [ins
t_5 : LE β], OrderIs…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrderRingIso.toOrderIso_eq_coe`：toOrderIso_eq_coe (f : α ≃+*o β) : f.toO
rderIso = f
· 使用定理 `OrderIso.symm_apply_lt`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder
 α] [inst_1 : Preorder β] (e : α ≃o β) {x : α} {y : β},   e.symm y < x ↔ y < e x
-/
theorem symm_apply_lt (e : R ≃+*o S) {x : R} {y : S} : e.symm y < x ↔ y < e x := by
  simpa using! e.toOrderIso.symm_apply_lt

end Preorder

section NonAssocSemiring

variable [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β] [Preorder β]

/-- Reinterpret an ordered ring isomorphism as an ordered ring homomorphism. -/
/-
**OrderRingIso.toOrderRingHom** 是 Mathlib 中的一个定义，位于命名空间 `OrderRingIso`。
形式化陈述：toOrderRingHom (f : α ≃+*o β) : α ->+*o β
参数：f : α ≃+*o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an ordered ring isomorphism as an ordered ring homomorphism.
-/
def toOrderRingHom (f : α ≃+*o β) : α →+*o β :=
  ⟨f.toRingEquiv.toRingHom, fun _ _ => (map_le_map_iff f).2⟩

@[simp]
/-
**OrderRingIso.toOrderRingHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：toOrderRingHom_eq_coe (f : α ≃+*o β) : f.toOrderRingHom = f
参数：f : α ≃+*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOrderRingHom_eq_coe (f : α ≃+*o β) : f.toOrderRingHom = f :=
  rfl

@[simp, norm_cast]
/-
**OrderRingIso.coe_toOrderRingHom** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：coe_toOrderRingHom (f : α ≃+*o β) : ⇑(f : α ->+*o β) = f
参数：f : α ≃+*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIsoClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : LE α] [inst_1 : LE β] [inst_2 : EquivLike F α β]   [OrderIsoClass 
F α β], OrderHomCla…
· 使用定理 `OrderRingIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
Mul α] [inst_1 : Add α] [inst_2 : LE α] [inst_3 : Mul β] [inst_4 : Add β]   [ins
t_5 : LE β], OrderIs…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `OrderRingIso.instRingEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst :
 Mul α] [inst_1 : Add α] [inst_2 : LE α] [inst_3 : Mul β] [inst_4 : Add β]   [in
st_5 : LE β], RingEqu…
-/
theorem coe_toOrderRingHom (f : α ≃+*o β) : ⇑(f : α →+*o β) = f :=
  rfl

@[simp]
/-
**OrderRingIso.coe_toOrderRingHom_refl** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`。
形式化陈述：coe_toOrderRingHom_refl : (OrderRingIso.refl α : α ->+*o α) = OrderRingHom
.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIsoClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : LE α] [inst_1 : LE β] [inst_2 : EquivLike F α β]   [OrderIsoClass 
F α β], OrderHomCla…
· 使用定理 `OrderRingIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
Mul α] [inst_1 : Add α] [inst_2 : LE α] [inst_3 : Mul β] [inst_4 : Add β]   [ins
t_5 : LE β], OrderIs…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `OrderRingIso.instRingEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst :
 Mul α] [inst_1 : Add α] [inst_2 : LE α] [inst_3 : Mul β] [inst_4 : Add β]   [in
st_5 : LE β], RingEqu…
-/
theorem coe_toOrderRingHom_refl : (OrderRingIso.refl α : α →+*o α) = OrderRingHom.id α :=
  rfl
/-
**OrderRingIso.toOrderRingHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `OrderRingIso`
。
形式化陈述：toOrderRingHom_injective : Injective (toOrderRingHom : α ≃+*o β -> α ->+*o
 β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext'_iff`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [i
 : DFunLike F α β] {f g : F}, f = g ↔ ⇑f = ⇑g
-/
theorem toOrderRingHom_injective : Injective (toOrderRingHom : α ≃+*o β → α →+*o β) :=
  fun f g h => DFunLike.coe_injective <| by convert! DFunLike.ext'_iff.1 h using 0

end NonAssocSemiring

end OrderRingIso

