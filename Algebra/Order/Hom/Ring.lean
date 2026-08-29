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

/--
Definition of `OrderRingHom` / `OrderRingHom` 的定义

English:
structure OrderRingHom
  parameters: (α β : Type*) [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β]
  extends: α ->+* β
  axioms and operations (1):
    - monotone' : Monotone toFun

中文:
结构 Order环态射
  参数: (α β : 类型) [非结合半环 α] [预序 α] [非结合半环 β]
  继承: α ->+* β
  公理与运算 (1 个):
    - monotone' : 递增 toFun
-/
structure OrderRingHom (α β : Type*) [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β]
  [Preorder β] extends α ->+* β where
  /-- The proposition that the function preserves the order. -/
  monotone' : Monotone toFun

/-- Reinterpret an ordered ring homomorphism as a ring homomorphism. -/
add_decl_doc OrderRingHom.toRingHom

@[inherit_doc]
infixl:25 " ->+*o " => OrderRingHom

/--
Definition of `OrderRingIso` / `OrderRingIso` 的定义

English:
structure OrderRingIso
  parameters: (α β : Type*) [Mul α] [Add α] [Mul β] [Add β] [LE α] [LE β]
  axioms and operations (1):
    - map_le_map_iff'({a b : α}) : toFun a <= toFun b ↔ a <= b

中文:
结构 OrderRingIso
  参数: (α β : 类型) [乘法 α] [加法 α] [乘法 β] [加法 β] [LE α] [LE β]
  公理与运算 (1 个):
    - map_le_map_iff'({a b : α}) : toFun a <= toFun b ↔ a <= b
-/
structure OrderRingIso (α β : Type*) [Mul α] [Add α] [Mul β] [Add β] [LE α] [LE β] extends
  α ≃+* β where
  /-- The proposition that the function preserves the order bijectively. -/
  map_le_map_iff' {a b : α} : toFun a <= toFun b ↔ a <= b

@[inherit_doc]
infixl:25 " ≃+*o " => OrderRingIso

-- See module docstring for details

section Hom

variable [FunLike F α β]

/-- Turn an element of a type `F` satisfying `OrderHomClass F α β` and `RingHomClass F α β`
into an actual `OrderRingHom`.
This is declared as the default coercion from `F` to `α →+*o β`. -/
@[coe]
/--
Definition of `OrderRingHomClass.toOrderRingHom` / `OrderRingHomClass.toOrderRingHom` 的定义

English:
definition OrderRingHomClass.toOrderRingHom
  signature: [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β]
  body: { (f : α ->+* β) with monotone' := OrderHomClass.monotone f }

中文:
定义 OrderRingHomClass.toOrderRingHom
  签名: [非结合半环 α] [预序 α] [非结合半环 β]
  定义体: { (f : α ->+* β) with monotone' := OrderHomClass.monotone f }

Depends on / 依赖: OrderHomClass, OrderHomClass.monotone, monotone
-/
def OrderRingHomClass.toOrderRingHom [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β]
    [Preorder β] [OrderHomClass F α β] [RingHomClass F α β] (f : F) : α ->+*o β :=
  { (f : α ->+* β) with monotone' := OrderHomClass.monotone f }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocSemiring
  signature: α] [Preorder α] [NonAssocSemiring β] [Preorder β]
  body: ⟨OrderRingHomClass.toOrderRingHom⟩

中文:
实例 [非结合半环
  签名: α] [预序 α] [非结合半环 β] [预序 β]
  定义体: ⟨OrderRingHomClass.toOrderRingHom⟩

Depends on / 依赖: OrderRingHomClass, OrderRingHomClass.toOrderRingHom, toOrderRingHom
-/
instance [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β] [Preorder β]
    [OrderHomClass F α β] [RingHomClass F α β] : CoeTC F (α ->+*o β) :=
  ⟨OrderRingHomClass.toOrderRingHom⟩

end Hom

section Equiv

variable [EquivLike F α β]

/-- Turn an element of a type `F` satisfying `OrderIsoClass F α β` and `RingEquivClass F α β`
into an actual `OrderRingIso`.
This is declared as the default coercion from `F` to `α ≃+*o β`. -/
@[coe]
/--
Definition of `OrderRingIsoClass.toOrderRingIso` / `OrderRingIsoClass.toOrderRingIso` 的定义

English:
definition OrderRingIsoClass.toOrderRingIso
  signature: [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β]
  body: { (RingEquivClass.toRingEquiv f : α ≃+* β) with map_le_map_iff' := map_le_map_iff f }

中文:
定义 OrderRingIsoClass.toOrderRingIso
  签名: [乘法 α] [加法 α] [LE α] [乘法 β] [加法 β] [LE β]
  定义体: { (RingEquivClass.toRingEquiv f : α ≃+* β) with map_le_map_iff' := map_le_map_iff f }

Depends on / 依赖: RingEquivClass, RingEquivClass.toRingEquiv, map_le_map_iff, toRingEquiv
-/
def OrderRingIsoClass.toOrderRingIso [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β]
    [OrderIsoClass F α β] [RingEquivClass F α β] (f : F) : α ≃+*o β :=
  { (RingEquivClass.toRingEquiv f : α ≃+* β) with map_le_map_iff' := map_le_map_iff f }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [Add α] [LE α] [Mul β] [Add β] [LE β] [OrderIsoClass F α β]
  body: ⟨OrderRingIsoClass.toOrderRingIso⟩

中文:
实例 [乘法
  签名: α] [加法 α] [LE α] [乘法 β] [加法 β] [LE β] [OrderIso类 F α β]
  定义体: ⟨OrderRingIsoClass.toOrderRingIso⟩

Depends on / 依赖: OrderRingIsoClass, OrderRingIsoClass.toOrderRingIso, toOrderRingIso
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

/--
Definition of `toOrderAddMonoidHom` / `toOrderAddMonoidHom` 的定义

English:
definition toOrderAddMonoidHom
  signature: (f : α ->+*o β)
  body: { f with }

中文:
定义 toOrderAddMonoidHom
  签名: (f : α ->+*o β)
  定义体: { f with }
-/
def toOrderAddMonoidHom (f : α ->+*o β) : α ->+o β :=
  { f with }

/--
Definition of `toOrderMonoidWithZeroHom` / `toOrderMonoidWithZeroHom` 的定义

English:
definition toOrderMonoidWithZeroHom
  signature: (f : α ->+*o β)
  body: { f with }

中文:
定义 toOrderMonoidWithZeroHom
  签名: (f : α ->+*o β)
  定义体: { f with }
-/
def toOrderMonoidWithZeroHom (f : α ->+*o β) : α ->*₀o β :=
  { f with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (α ->+*o β) α β
  body: f.toFun
  coe_injective f g h := by
    cases f; cases g; congr
    exact DFunLike.coe_injective h

中文:
实例 :
  签名: 函数状 (α ->+*o β) α β
  定义体: f.toFun
  coe_injective f g h := by
    cases f; cases g; congr
    exact DFunLike.coe_injective h

Depends on / 依赖: f.toFun
-/
instance : FunLike (α ->+*o β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    cases f; cases g; congr
    exact DFunLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderHomClass (α ->+*o β) α β
  body: f.monotone' h

中文:
实例 :
  签名: 序态射类 (α ->+*o β) α β
  定义体: f.monotone' h

Depends on / 依赖: f.monotone, monotone
-/
instance : OrderHomClass (α ->+*o β) α β where
  map_rel f _ _ h := f.monotone' h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RingHomClass (α ->+*o β) α β
  body: f.map_mul'
  map_one f := f.map_one'
  map_add f := f.map_add'
  map_zero f := f.map_zero'

中文:
实例 :
  签名: 环态射类 (α ->+*o β) α β
  定义体: f.map_mul'
  map_one f := f.map_one'
  map_add f := f.map_add'
  map_zero f := f.map_zero'

Depends on / 依赖: f.map_mul, map_mul
-/
instance : RingHomClass (α ->+*o β) α β where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_add f := f.map_add'
  map_zero f := f.map_zero'

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : α ->+*o β)
  statement: f.toFun = f
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe
  条件: (f : α ->+*o β)
  结论: f.toFun = f
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe (f : α ->+*o β) : f.toFun = f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : α ->+*o β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

@[simp]

中文:
定理 ext
  条件: {f g : α ->+*o β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : α ->+*o β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[simp]
/--
theorem `toRingHom_eq_coe` / 定理 `toRingHom_eq_coe`

English:
theorem toRingHom_eq_coe
  given: (f : α ->+*o β)
  statement: f.toRingHom = f
  proof: RingHom.ext fun _ => rfl

@[simp]

中文:
定理 toRingHom_eq_coe
  条件: (f : α ->+*o β)
  结论: f.toRingHom = f
  证明: RingHom.ext fun _ => rfl

@[simp]

Depends on / 依赖: RingHom, RingHom.ext
-/
theorem toRingHom_eq_coe (f : α ->+*o β) : f.toRingHom = f :=
  RingHom.ext fun _ => rfl

@[simp]
/--
theorem `toOrderAddMonoidHom_eq_coe` / 定理 `toOrderAddMonoidHom_eq_coe`

English:
theorem toOrderAddMonoidHom_eq_coe
  given: (f : α ->+*o β)
  statement: f.toOrderAddMonoidHom = f
  proof: rfl

@[simp]

中文:
定理 toOrderAddMonoidHom_eq_coe
  条件: (f : α ->+*o β)
  结论: f.toOrderAddMonoidHom = f
  证明: rfl

@[simp]
-/
theorem toOrderAddMonoidHom_eq_coe (f : α ->+*o β) : f.toOrderAddMonoidHom = f :=
  rfl

@[simp]
/--
theorem `toOrderMonoidWithZeroHom_eq_coe` / 定理 `toOrderMonoidWithZeroHom_eq_coe`

English:
theorem toOrderMonoidWithZeroHom_eq_coe
  given: (f : α ->+*o β)
  statement: f.toOrderMonoidWithZeroHom = f
  proof: rfl

@[simp]

中文:
定理 toOrderMonoidWithZeroHom_eq_coe
  条件: (f : α ->+*o β)
  结论: f.toOrderMonoidWithZeroHom = f
  证明: rfl

@[simp]
-/
theorem toOrderMonoidWithZeroHom_eq_coe (f : α ->+*o β) : f.toOrderMonoidWithZeroHom = f :=
  rfl

@[simp]
/--
theorem `coe_coe_ringHom` / 定理 `coe_coe_ringHom`

English:
theorem coe_coe_ringHom
  given: (f : α ->+*o β)
  statement: ⇑(f : α ->+* β) = f
  proof: rfl

@[simp]

中文:
定理 coe_coe_ringHom
  条件: (f : α ->+*o β)
  结论: ⇑(f : α ->+* β) = f
  证明: rfl

@[simp]
-/
theorem coe_coe_ringHom (f : α ->+*o β) : ⇑(f : α ->+* β) = f :=
  rfl

@[simp]
/--
theorem `coe_coe_orderAddMonoidHom` / 定理 `coe_coe_orderAddMonoidHom`

English:
theorem coe_coe_orderAddMonoidHom
  given: (f : α ->+*o β)
  statement: ⇑(f : α ->+o β) = f
  proof: rfl

@[simp]

中文:
定理 coe_coe_orderAddMonoidHom
  条件: (f : α ->+*o β)
  结论: ⇑(f : α ->+o β) = f
  证明: rfl

@[simp]
-/
theorem coe_coe_orderAddMonoidHom (f : α ->+*o β) : ⇑(f : α ->+o β) = f :=
  rfl

@[simp]
/--
theorem `coe_coe_orderMonoidWithZeroHom` / 定理 `coe_coe_orderMonoidWithZeroHom`

English:
theorem coe_coe_orderMonoidWithZeroHom
  given: (f : α ->+*o β)
  statement: ⇑(f : α ->*₀o β) = f
  proof: rfl

@[norm_cast]

中文:
定理 coe_coe_orderMonoidWithZeroHom
  条件: (f : α ->+*o β)
  结论: ⇑(f : α ->*₀o β) = f
  证明: rfl

@[norm_cast]
-/
theorem coe_coe_orderMonoidWithZeroHom (f : α ->+*o β) : ⇑(f : α ->*₀o β) = f :=
  rfl

@[norm_cast]
/--
theorem `coe_ringHom_apply` / 定理 `coe_ringHom_apply`

English:
theorem coe_ringHom_apply
  given: (f : α ->+*o β) (a : α)
  statement: (f : α ->+* β) a = f a
  proof: rfl

@[norm_cast]

中文:
定理 coe_ringHom_apply
  条件: (f : α ->+*o β) (a : α)
  结论: (f : α ->+* β) a = f a
  证明: rfl

@[norm_cast]
-/
theorem coe_ringHom_apply (f : α ->+*o β) (a : α) : (f : α ->+* β) a = f a :=
  rfl

@[norm_cast]
/--
theorem `coe_orderAddMonoidHom_apply` / 定理 `coe_orderAddMonoidHom_apply`

English:
theorem coe_orderAddMonoidHom_apply
  given: (f : α ->+*o β) (a : α)
  statement: (f : α ->+o β) a = f a
  proof: rfl

@[norm_cast]

中文:
定理 coe_orderAddMonoidHom_apply
  条件: (f : α ->+*o β) (a : α)
  结论: (f : α ->+o β) a = f a
  证明: rfl

@[norm_cast]
-/
theorem coe_orderAddMonoidHom_apply (f : α ->+*o β) (a : α) : (f : α ->+o β) a = f a :=
  rfl

@[norm_cast]
/--
theorem `coe_orderMonoidWithZeroHom_apply` / 定理 `coe_orderMonoidWithZeroHom_apply`

English:
theorem coe_orderMonoidWithZeroHom_apply
  given: (f : α ->+*o β) (a : α)
  statement: (f : α ->*₀o β) a = f a
  proof: rfl

中文:
定理 coe_orderMonoidWithZeroHom_apply
  条件: (f : α ->+*o β) (a : α)
  结论: (f : α ->*₀o β) a = f a
  证明: rfl
-/
theorem coe_orderMonoidWithZeroHom_apply (f : α ->+*o β) (a : α) : (f : α ->*₀o β) a = f a :=
  rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : α ->+*o β) (f' : α -> β) (h : f' = f)
  body: { f.toRingHom.copy f' h, f.toOrderAddMonoidHom.copy f' h with }

@[simp]

中文:
定义 copy
  签名: (f : α ->+*o β) (f' : α -> β) (h : f' = f)
  定义体: { f.toRingHom.copy f' h, f.toOrderAddMonoidHom.copy f' h with }

@[simp]
-/
protected def copy (f : α ->+*o β) (f' : α -> β) (h : f' = f) : α ->+*o β :=
  { f.toRingHom.copy f' h, f.toOrderAddMonoidHom.copy f' h with }

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : α ->+*o β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : α ->+*o β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : α ->+*o β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : α ->+*o β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : α ->+*o β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : α ->+*o β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : α ->+*o α
  body: { RingHom.id _, OrderHom.id with }

中文:
定义 id
  签名: : α ->+*o α
  定义体: { RingHom.id _, OrderHom.id with }
-/
protected def id : α ->+*o α :=
  { RingHom.id _, OrderHom.id with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (α ->+*o α)
  body: ⟨OrderRingHom.id α⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 可居 (α ->+*o α)
  定义体: ⟨OrderRingHom.id α⟩

@[simp, norm_cast]

Depends on / 依赖: OrderRingHom, OrderRingHom.id
-/
instance : Inhabited (α ->+*o α) :=
  ⟨OrderRingHom.id α⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(OrderRingHom.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(Order环态射.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(OrderRingHom.id α) = id :=
  rfl

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: OrderRingHom.id α a = a
  proof: rfl

@[simp]

中文:
定理 id_apply
  条件: (a : α)
  结论: Order环态射.id α a = a
  证明: rfl

@[simp]
-/
theorem id_apply (a : α) : OrderRingHom.id α a = a :=
  rfl

@[simp]
/--
theorem `coe_ringHom_id` / 定理 `coe_ringHom_id`

English:
theorem coe_ringHom_id
  statement: (OrderRingHom.id α : α ->+* α) = RingHom.id α
  proof: rfl

@[simp]

中文:
定理 coe_ringHom_id
  结论: (Order环态射.id α : α ->+* α) = 环态射.id α
  证明: rfl

@[simp]
-/
theorem coe_ringHom_id : (OrderRingHom.id α : α ->+* α) = RingHom.id α :=
  rfl

@[simp]
/--
theorem `coe_orderAddMonoidHom_id` / 定理 `coe_orderAddMonoidHom_id`

English:
theorem coe_orderAddMonoidHom_id
  statement: (OrderRingHom.id α : α ->+o α) = OrderAddMonoidHom.id α
  proof: rfl

@[simp]

中文:
定理 coe_orderAddMonoidHom_id
  结论: (Order环态射.id α : α ->+o α) = OrderAdd幺半群态射.id α
  证明: rfl

@[simp]
-/
theorem coe_orderAddMonoidHom_id : (OrderRingHom.id α : α ->+o α) = OrderAddMonoidHom.id α :=
  rfl

@[simp]
/--
theorem `coe_orderMonoidWithZeroHom_id` / 定理 `coe_orderMonoidWithZeroHom_id`

English:
theorem coe_orderMonoidWithZeroHom_id
  proof: rfl

中文:
定理 coe_orderMonoidWithZeroHom_id
  证明: rfl
-/
theorem coe_orderMonoidWithZeroHom_id :
    (OrderRingHom.id α : α ->*₀o α) = OrderMonoidWithZeroHom.id α :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : β ->+*o γ) (g : α ->+*o β)
  body: { f.toRingHom.comp g.toRingHom, f.toOrderAddMonoidHom.comp g.toOrderAddMonoidHom with }

@[simp]

中文:
定义 comp
  签名: (f : β ->+*o γ) (g : α ->+*o β)
  定义体: { f.toRingHom.comp g.toRingHom, f.toOrderAddMonoidHom.comp g.toOrderAddMonoidHom with }

@[simp]
-/
protected def comp (f : β ->+*o γ) (g : α ->+*o β) : α ->+*o γ :=
  { f.toRingHom.comp g.toRingHom, f.toOrderAddMonoidHom.comp g.toOrderAddMonoidHom with }

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : β ->+*o γ) (g : α ->+*o β)
  statement: ⇑(f.comp g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : β ->+*o γ) (g : α ->+*o β)
  结论: ⇑(f.comp g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : β ->+*o γ) (g : α ->+*o β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : β ->+*o γ) (g : α ->+*o β) (a : α)
  statement: f.comp g a = f (g a)
  proof: rfl

中文:
定理 comp_apply
  条件: (f : β ->+*o γ) (g : α ->+*o β) (a : α)
  结论: f.comp g a = f (g a)
  证明: rfl
-/
theorem comp_apply (f : β ->+*o γ) (g : α ->+*o β) (a : α) : f.comp g a = f (g a) :=
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : γ ->+*o δ) (g : β ->+*o γ) (h : α ->+*o β)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : γ ->+*o δ) (g : β ->+*o γ) (h : α ->+*o β)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : γ ->+*o δ) (g : β ->+*o γ) (h : α ->+*o β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : α ->+*o β)
  statement: f.comp (OrderRingHom.id α) = f
  proof: rfl

@[simp]

中文:
定理 comp_id
  条件: (f : α ->+*o β)
  结论: f.comp (Order环态射.id α) = f
  证明: rfl

@[simp]
-/
theorem comp_id (f : α ->+*o β) : f.comp (OrderRingHom.id α) = f :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : α ->+*o β)
  statement: (OrderRingHom.id β).comp f = f
  proof: rfl

@[simp]

中文:
定理 id_comp
  条件: (f : α ->+*o β)
  结论: (Order环态射.id β).comp f = f
  证明: rfl

@[simp]
-/
theorem id_comp (f : α ->+*o β) : (OrderRingHom.id β).comp f = f :=
  rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {f₁ f₂ : β ->+*o γ} {g : α ->+*o β} (hg : Surjective g)
  proof: ⟨fun h => ext hg.forall.2 DFunLike.ext_iff.1 h, fun h => by rw [h]⟩

@[simp]

中文:
定理 cancel_right
  条件: {f₁ f₂ : β ->+*o γ} {g : α ->+*o β} (hg : 满射 g)
  证明: ⟨fun h => ext hg.forall.2 DFunLike.ext_iff.1 h, fun h => by rw [h]⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, hg.forall
-/
theorem cancel_right {f₁ f₂ : β ->+*o γ} {g : α ->+*o β} (hg : Surjective g) :
    f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
⟨fun h => ext hg.forall.2 DFunLike.ext_iff.1 h, fun h => by rw [h]⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {f : β ->+*o γ} {g₁ g₂ : α ->+*o β} (hf : Injective f)
  proof: ⟨fun h => ext fun a => hf by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: {f : β ->+*o γ} {g₁ g₂ : α ->+*o β} (hf : 单射 f)
  证明: ⟨fun h => ext fun a => hf by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: comp_apply, congr_arg
-/
theorem cancel_left {f : β ->+*o γ} {g₁ g₂ : α ->+*o β} (hf : Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
⟨fun h => ext fun a => hf by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end Preorder

variable [NonAssocSemiring β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: β] : Preorder (OrderRingHom α β)
  body: Preorder.lift ((⇑) : _ -> α -> β)

中文:
实例 [预序
  签名: β] : 预序 (Order环态射 α β)
  定义体: Preorder.lift ((⇑) : _ -> α -> β)

Depends on / 依赖: Preorder, Preorder.lift
-/
instance [Preorder β] : Preorder (OrderRingHom α β) :=
  Preorder.lift ((⇑) : _ -> α -> β)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: β] : PartialOrder (OrderRingHom α β)
  body: PartialOrder.lift _ DFunLike.coe_injective

中文:
实例 [偏序
  签名: β] : 偏序 (Order环态射 α β)
  定义体: PartialOrder.lift _ DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective
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
/--
Definition of `toOrderIso` / `toOrderIso` 的定义

English:
definition toOrderIso
  signature: (f : α ≃+*o β)
  body: ⟨f.toRingEquiv.toEquiv, f.map_le_map_iff'⟩

中文:
定义 toOrderIso
  签名: (f : α ≃+*o β)
  定义体: ⟨f.toRingEquiv.toEquiv, f.map_le_map_iff'⟩

Depends on / 依赖: f.map_le_map_iff, f.toRingEquiv.toEquiv, map_le_map_iff, toEquiv, toRingEquiv
-/
def toOrderIso (f : α ≃+*o β) : α ≃o β :=
  ⟨f.toRingEquiv.toEquiv, f.map_le_map_iff'⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (α ≃+*o β) α β
  body: f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

中文:
实例 :
  签名: 等价状 (α ≃+*o β) α β
  定义体: f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

Depends on / 依赖: f.toFun
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderIsoClass (α ≃+*o β) α β
  body: f.map_le_map_iff'

中文:
实例 :
  签名: OrderIso类 (α ≃+*o β) α β
  定义体: f.map_le_map_iff'

Depends on / 依赖: f.map_le_map_iff, map_le_map_iff
-/
instance : OrderIsoClass (α ≃+*o β) α β where
  map_le_map_iff f _ _ := f.map_le_map_iff'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RingEquivClass (α ≃+*o β) α β
  body: f.map_mul'
  map_add f := f.map_add'

中文:
实例 :
  签名: 环等价类 (α ≃+*o β) α β
  定义体: f.map_mul'
  map_add f := f.map_add'

Depends on / 依赖: f.map_mul, map_mul
-/
instance : RingEquivClass (α ≃+*o β) α β where
  map_mul f := f.map_mul'
  map_add f := f.map_add'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (α ≃+*o β) (α ≃+* β)
  body: toRingEquiv

中文:
实例 :
  签名: CoeOut (α ≃+*o β) (α ≃+* β)
  定义体: toRingEquiv

Depends on / 依赖: toRingEquiv
-/
instance : CoeOut (α ≃+*o β) (α ≃+* β) where coe := toRingEquiv

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : α ≃+*o β)
  statement: f.toFun = f
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe
  条件: (f : α ≃+*o β)
  结论: f.toFun = f
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe (f : α ≃+*o β) : f.toFun = f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : α ≃+*o β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

@[simp]

中文:
定理 ext
  条件: {f g : α ≃+*o β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : α ≃+*o β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (e : α ≃+* β) (h)
  statement: ⇑(⟨e, h⟩ : α ≃+*o β) = e
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (e : α ≃+* β) (h)
  结论: ⇑(⟨e, h⟩ : α ≃+*o β) = e
  证明: rfl

@[simp]
-/
theorem coe_mk (e : α ≃+* β) (h) : ⇑(⟨e, h⟩ : α ≃+*o β) = e :=
  rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (e : α ≃+*o β) (h)
  statement: (⟨e, h⟩ : α ≃+*o β) = e
  proof: ext fun _ => rfl

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]

中文:
定理 mk_coe
  条件: (e : α ≃+*o β) (h)
  结论: (⟨e, h⟩ : α ≃+*o β) = e
  证明: ext fun _ => rfl

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]
-/
theorem mk_coe (e : α ≃+*o β) (h) : (⟨e, h⟩ : α ≃+*o β) = e :=
  ext fun _ => rfl

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]
/--
theorem `toRingEquiv_eq_coe` / 定理 `toRingEquiv_eq_coe`

English:
theorem toRingEquiv_eq_coe
  given: (f : α ≃+*o β)
  statement: f.toRingEquiv = f
  proof: RingEquiv.ext fun _ => rfl

@[simp]

中文:
定理 toRingEquiv_eq_coe
  条件: (f : α ≃+*o β)
  结论: f.toRingEquiv = f
  证明: RingEquiv.ext fun _ => rfl

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.ext
-/
theorem toRingEquiv_eq_coe (f : α ≃+*o β) : f.toRingEquiv = f :=
  RingEquiv.ext fun _ => rfl

@[simp]
/--
theorem `toOrderIso_eq_coe` / 定理 `toOrderIso_eq_coe`

English:
theorem toOrderIso_eq_coe
  given: (f : α ≃+*o β)
  statement: f.toOrderIso = f
  proof: OrderIso.ext rfl

@[simp]

中文:
定理 toOrderIso_eq_coe
  条件: (f : α ≃+*o β)
  结论: f.toOrderIso = f
  证明: OrderIso.ext rfl

@[simp]

Depends on / 依赖: OrderIso, OrderIso.ext
-/
theorem toOrderIso_eq_coe (f : α ≃+*o β) : f.toOrderIso = f :=
  OrderIso.ext rfl

@[simp]
/--
theorem `coe_toRingEquiv` / 定理 `coe_toRingEquiv`

English:
theorem coe_toRingEquiv
  given: (f : α ≃+*o β)
  statement: ⇑(f : α ≃+* β) = f
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_toRingEquiv
  条件: (f : α ≃+*o β)
  结论: ⇑(f : α ≃+* β) = f
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_toRingEquiv (f : α ≃+*o β) : ⇑(f : α ≃+* β) = f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_toOrderIso` / 定理 `coe_toOrderIso`

English:
theorem coe_toOrderIso
  given: (f : α ≃+*o β)
  statement: DFunLike.coe (f : α ≃o β) = f
  proof: rfl

中文:
定理 coe_toOrderIso
  条件: (f : α ≃+*o β)
  结论: 依赖函数状.coe (f : α ≃o β) = f
  证明: rfl
-/
theorem coe_toOrderIso (f : α ≃+*o β) : DFunLike.coe (f : α ≃o β) = f :=
  rfl

variable (α)

/-- The identity map as an ordered ring isomorphism. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : α ≃+*o α
  body: ⟨RingEquiv.refl α, Iff.rfl⟩

中文:
定义 refl
  签名: : α ≃+*o α
  定义体: ⟨RingEquiv.refl α, Iff.rfl⟩
-/
protected def refl : α ≃+*o α :=
  ⟨RingEquiv.refl α, Iff.rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (α ≃+*o α)
  body: ⟨OrderRingIso.refl α⟩

@[simp]

中文:
实例 :
  签名: 可居 (α ≃+*o α)
  定义体: ⟨OrderRingIso.refl α⟩

@[simp]

Depends on / 依赖: OrderRingIso, OrderRingIso.refl
-/
instance : Inhabited (α ≃+*o α) :=
  ⟨OrderRingIso.refl α⟩

@[simp]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (x : α)
  statement: OrderRingIso.refl α x = x
  proof: by
  rfl

@[simp]

中文:
定理 refl_apply
  条件: (x : α)
  结论: OrderRingIso.refl α x = x
  证明: by
  rfl

@[simp]
-/
theorem refl_apply (x : α) : OrderRingIso.refl α x = x := by
  rfl

@[simp]
/--
theorem `coe_ringEquiv_refl` / 定理 `coe_ringEquiv_refl`

English:
theorem coe_ringEquiv_refl
  statement: (OrderRingIso.refl α : α ≃+* α) = RingEquiv.refl α
  proof: rfl

@[simp]

中文:
定理 coe_ringEquiv_refl
  结论: (OrderRingIso.refl α : α ≃+* α) = 环等价.refl α
  证明: rfl

@[simp]
-/
theorem coe_ringEquiv_refl : (OrderRingIso.refl α : α ≃+* α) = RingEquiv.refl α :=
  rfl

@[simp]
/--
theorem `coe_orderIso_refl` / 定理 `coe_orderIso_refl`

English:
theorem coe_orderIso_refl
  statement: (OrderRingIso.refl α : α ≃o α) = OrderIso.refl α
  proof: rfl

中文:
定理 coe_orderIso_refl
  结论: (OrderRingIso.refl α : α ≃o α) = OrderIso.refl α
  证明: rfl
-/
theorem coe_orderIso_refl : (OrderRingIso.refl α : α ≃o α) = OrderIso.refl α :=
  rfl

variable {α}

/-- The inverse of an ordered ring isomorphism as an ordered ring isomorphism. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : α ≃+*o β)
  body: ⟨e.toRingEquiv.symm, by simp [← e.map_le_map_iff']⟩

中文:
定义 symm
  签名: (e : α ≃+*o β)
  定义体: ⟨e.toRingEquiv.symm, by simp [← e.map_le_map_iff']⟩
-/
protected def symm (e : α ≃+*o β) : β ≃+*o α := ⟨e.toRingEquiv.symm, by simp [← e.map_le_map_iff']⟩

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (e : α ≃+*o β)
  body: e.symm

@[simp]

中文:
定义 Simps.symm_apply
  签名: (e : α ≃+*o β)
  定义体: e.symm

@[simp]
-/
def Simps.symm_apply (e : α ≃+*o β) : β -> α :=
  e.symm

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : α ≃+*o β)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : α ≃+*o β)
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm (e : α ≃+*o β) : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Bijective (OrderRingIso.symm : (α ≃+*o β) -> β ≃+*o α)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

中文:
定理 symm_bijective
  结论: 双射 (OrderRingIso.symm : (α ≃+*o β) -> β ≃+*o α)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Bijective (OrderRingIso.symm : (α ≃+*o β) -> β ≃+*o α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : α ≃+*o β) (a : α)
  statement: e.symm (e a) = a
  proof: e.toRingEquiv.symm_apply_apply a

@[simp]

中文:
定理 symm_apply_apply
  条件: (e : α ≃+*o β) (a : α)
  结论: e.symm (e a) = a
  证明: e.toRingEquiv.symm_apply_apply a

@[simp]

Depends on / 依赖: e.toRingEquiv.symm_apply_apply, symm_apply_apply, toRingEquiv
-/
theorem symm_apply_apply (e : α ≃+*o β) (a : α) : e.symm (e a) = a :=
  e.toRingEquiv.symm_apply_apply a

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : α ≃+*o β) (b : β)
  statement: e (e.symm b) = b
  proof: e.toRingEquiv.apply_symm_apply b

中文:
定理 apply_symm_apply
  条件: (e : α ≃+*o β) (b : β)
  结论: e (e.symm b) = b
  证明: e.toRingEquiv.apply_symm_apply b

Depends on / 依赖: apply_symm_apply, e.toRingEquiv.apply_symm_apply, toRingEquiv
-/
theorem apply_symm_apply (e : α ≃+*o β) (b : β) : e (e.symm b) = b :=
  e.toRingEquiv.apply_symm_apply b

/-- Composition of `OrderRingIso`s as an `OrderRingIso`. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (f : α ≃+*o β) (g : β ≃+*o γ)
  body: ⟨f.toRingEquiv.trans g.toRingEquiv, (map_le_map_iff g).trans (map_le_map_iff f)⟩

中文:
定义 trans
  签名: (f : α ≃+*o β) (g : β ≃+*o γ)
  定义体: ⟨f.toRingEquiv.trans g.toRingEquiv, (map_le_map_iff g).trans (map_le_map_iff f)⟩
-/
protected def trans (f : α ≃+*o β) (g : β ≃+*o γ) : α ≃+*o γ :=
  ⟨f.toRingEquiv.trans g.toRingEquiv, (map_le_map_iff g).trans (map_le_map_iff f)⟩

/--
theorem `trans_toRingEquiv` / 定理 `trans_toRingEquiv`

English:
theorem trans_toRingEquiv
  given: (f : α ≃+*o β) (g : β ≃+*o γ)
  proof: rfl

中文:
定理 trans_toRingEquiv
  条件: (f : α ≃+*o β) (g : β ≃+*o γ)
  证明: rfl
-/
theorem trans_toRingEquiv (f : α ≃+*o β) (g : β ≃+*o γ) :
    (OrderRingIso.trans f g).toRingEquiv = RingEquiv.trans f.toRingEquiv g.toRingEquiv :=
  rfl

/-- `simp`-normal form of `trans_toRingEquiv`. -/
@[simp]
/--
theorem `trans_toRingEquiv_aux` / 定理 `trans_toRingEquiv_aux`

English:
theorem trans_toRingEquiv_aux
  given: (f : α ≃+*o β) (g : β ≃+*o γ)
  proof: rfl

@[simp]

中文:
定理 trans_toRingEquiv_aux
  条件: (f : α ≃+*o β) (g : β ≃+*o γ)
  证明: rfl

@[simp]
-/
theorem trans_toRingEquiv_aux (f : α ≃+*o β) (g : β ≃+*o γ) :
    RingEquivClass.toRingEquiv (OrderRingIso.trans f g)
      = RingEquiv.trans f.toRingEquiv g.toRingEquiv :=
  rfl

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (f : α ≃+*o β) (g : β ≃+*o γ) (a : α)
  statement: f.trans g a = g (f a)
  proof: rfl

@[simp]

中文:
定理 trans_apply
  条件: (f : α ≃+*o β) (g : β ≃+*o γ) (a : α)
  结论: f.trans g a = g (f a)
  证明: rfl

@[simp]
-/
theorem trans_apply (f : α ≃+*o β) (g : β ≃+*o γ) (a : α) : f.trans g a = g (f a) :=
  rfl

@[simp]
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (e : α ≃+*o β)
  statement: e.trans e.symm = OrderRingIso.refl α
  proof: ext e.left_inv

@[simp]

中文:
定理 self_trans_symm
  条件: (e : α ≃+*o β)
  结论: e.trans e.symm = OrderRingIso.refl α
  证明: ext e.left_inv

@[simp]

Depends on / 依赖: e.left_inv, left_inv
-/
theorem self_trans_symm (e : α ≃+*o β) : e.trans e.symm = OrderRingIso.refl α :=
  ext e.left_inv

@[simp]
/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (e : α ≃+*o β)
  statement: e.symm.trans e = OrderRingIso.refl β
  proof: ext e.right_inv

中文:
定理 symm_trans_self
  条件: (e : α ≃+*o β)
  结论: e.symm.trans e = OrderRingIso.refl β
  证明: ext e.right_inv

Depends on / 依赖: e.right_inv, right_inv
-/
theorem symm_trans_self (e : α ≃+*o β) : e.symm.trans e = OrderRingIso.refl β :=
  ext e.right_inv

end LE

section Preorder

variable {R S : Type*} [Mul R] [Add R] [Mul S] [Add S] [Preorder R] [Preorder S]

/--
theorem `lt_symm_apply` / 定理 `lt_symm_apply`

English:
theorem lt_symm_apply
  given: (e : R ≃+*o S) {x : R} {y : S}
  statement: x < e.symm y ↔ e x < y
  proof: by
  simpa using! e.toOrderIso.lt_symm_apply

中文:
定理 lt_symm_apply
  条件: (e : R ≃+*o S) {x : R} {y : S}
  结论: x < e.symm y ↔ e x < y
  证明: by
  simpa using! e.toOrderIso.lt_symm_apply

Depends on / 依赖: e.toOrderIso.lt_symm_apply, lt_symm_apply, toOrderIso
-/
theorem lt_symm_apply (e : R ≃+*o S) {x : R} {y : S} : x < e.symm y ↔ e x < y := by
  simpa using! e.toOrderIso.lt_symm_apply

/--
theorem `symm_apply_lt` / 定理 `symm_apply_lt`

English:
theorem symm_apply_lt
  given: (e : R ≃+*o S) {x : R} {y : S}
  statement: e.symm y < x ↔ y < e x
  proof: by
  simpa using! e.toOrderIso.symm_apply_lt

中文:
定理 symm_apply_lt
  条件: (e : R ≃+*o S) {x : R} {y : S}
  结论: e.symm y < x ↔ y < e x
  证明: by
  simpa using! e.toOrderIso.symm_apply_lt

Depends on / 依赖: e.toOrderIso.symm_apply_lt, symm_apply_lt, toOrderIso
-/
theorem symm_apply_lt (e : R ≃+*o S) {x : R} {y : S} : e.symm y < x ↔ y < e x := by
  simpa using! e.toOrderIso.symm_apply_lt

end Preorder

section NonAssocSemiring

variable [NonAssocSemiring α] [Preorder α] [NonAssocSemiring β] [Preorder β]

/--
Definition of `toOrderRingHom` / `toOrderRingHom` 的定义

English:
definition toOrderRingHom
  signature: (f : α ≃+*o β)
  body: ⟨f.toRingEquiv.toRingHom, fun _ _ => (map_le_map_iff f).2⟩

@[simp]

中文:
定义 toOrderRingHom
  签名: (f : α ≃+*o β)
  定义体: ⟨f.toRingEquiv.toRingHom, fun _ _ => (map_le_map_iff f).2⟩

@[simp]

Depends on / 依赖: f.toRingEquiv.toRingHom, map_le_map_iff, toRingEquiv, toRingHom
-/
def toOrderRingHom (f : α ≃+*o β) : α ->+*o β :=
  ⟨f.toRingEquiv.toRingHom, fun _ _ => (map_le_map_iff f).2⟩

@[simp]
/--
theorem `toOrderRingHom_eq_coe` / 定理 `toOrderRingHom_eq_coe`

English:
theorem toOrderRingHom_eq_coe
  given: (f : α ≃+*o β)
  statement: f.toOrderRingHom = f
  proof: rfl

@[simp, norm_cast]

中文:
定理 toOrderRingHom_eq_coe
  条件: (f : α ≃+*o β)
  结论: f.toOrderRingHom = f
  证明: rfl

@[simp, norm_cast]
-/
theorem toOrderRingHom_eq_coe (f : α ≃+*o β) : f.toOrderRingHom = f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_toOrderRingHom` / 定理 `coe_toOrderRingHom`

English:
theorem coe_toOrderRingHom
  given: (f : α ≃+*o β)
  statement: ⇑(f : α ->+*o β) = f
  proof: rfl

@[simp]

中文:
定理 coe_toOrderRingHom
  条件: (f : α ≃+*o β)
  结论: ⇑(f : α ->+*o β) = f
  证明: rfl

@[simp]
-/
theorem coe_toOrderRingHom (f : α ≃+*o β) : ⇑(f : α ->+*o β) = f :=
  rfl

@[simp]
/--
theorem `coe_toOrderRingHom_refl` / 定理 `coe_toOrderRingHom_refl`

English:
theorem coe_toOrderRingHom_refl
  statement: (OrderRingIso.refl α : α ->+*o α) = OrderRingHom.id α
  proof: rfl

中文:
定理 coe_toOrderRingHom_refl
  结论: (OrderRingIso.refl α : α ->+*o α) = Order环态射.id α
  证明: rfl
-/
theorem coe_toOrderRingHom_refl : (OrderRingIso.refl α : α ->+*o α) = OrderRingHom.id α :=
  rfl

/--
theorem `toOrderRingHom_injective` / 定理 `toOrderRingHom_injective`

English:
theorem toOrderRingHom_injective
  statement: Injective (toOrderRingHom : α ≃+*o β -> α ->+*o β)
  proof: fun f g h => DFunLike.coe_injective by convert! DFunLike.ext'_iff.1 h using 0

中文:
定理 toOrderRingHom_injective
  结论: 单射 (toOrderRingHom : α ≃+*o β -> α ->+*o β)
  证明: fun f g h => DFunLike.coe_injective by convert! DFunLike.ext'_iff.1 h using 0

Depends on / 依赖: DFunLike, DFunLike.coe_injective, DFunLike.ext, _iff, coe_injective, convert
-/
theorem toOrderRingHom_injective : Injective (toOrderRingHom : α ≃+*o β -> α ->+*o β) :=
fun f g h => DFunLike.coe_injective by convert! DFunLike.ext'_iff.1 h using 0

end NonAssocSemiring

end OrderRingIso
