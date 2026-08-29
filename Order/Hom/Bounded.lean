/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Hom.Basic

/-!
# Bounded order homomorphisms

This file defines (bounded) order homomorphisms.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `TopHom`: Maps which preserve `⊤`.
* `BotHom`: Maps which preserve `⊥`.
* `BoundedOrderHom`: Bounded order homomorphisms. Monotone maps which preserve `⊤` and `⊥`.

## Typeclasses

* `TopHomClass`
* `BotHomClass`
* `BoundedOrderHomClass`
-/

@[expose] public section


open Function OrderDual

variable {F α β γ δ : Type*}

/--
Definition of `TopHom` / `TopHom` 的定义

English:
structure TopHom
  parameters: (α β : Type*) [Top α] [Top β]
  axioms and operations (2):
    - toFun : α -> β
    - map_top' : toFun ⊤ = ⊤

中文:
结构 顶元素态射
  参数: (α β : 类型) [顶元素 α] [顶元素 β]
  公理与运算 (2 个):
    - toFun : α -> β
    - map_top' : toFun ⊤ = ⊤
-/
structure TopHom (α β : Type*) [Top α] [Top β] where
  /-- The underlying function. The preferred spelling is `DFunLike.coe`. -/
  toFun : α -> β
  /-- The function preserves the top element. The preferred spelling is `map_top`. -/
  map_top' : toFun ⊤ = ⊤

/-- The type of `⊥`-preserving functions from `α` to `β`. -/
@[to_dual]
/--
Definition of `BotHom` / `BotHom` 的定义

English:
structure BotHom
  parameters: (α β : Type*) [Bot α] [Bot β]
  axioms and operations (2):
    - toFun : α -> β
    - map_bot' : toFun ⊥ = ⊥

中文:
结构 底元素态射
  参数: (α β : 类型) [底元素 α] [底元素 β]
  公理与运算 (2 个):
    - toFun : α -> β
    - map_bot' : toFun ⊥ = ⊥
-/
structure BotHom (α β : Type*) [Bot α] [Bot β] where
  /-- The underlying function. The preferred spelling is `DFunLike.coe`. -/
  toFun : α -> β
  /-- The function preserves the bottom element. The preferred spelling is `map_bot`. -/
  map_bot' : toFun ⊥ = ⊥

/--
Definition of `BoundedOrderHom` / `BoundedOrderHom` 的定义

English:
structure BoundedOrderHom
  parameters: (α β : Type*) [Preorder α] [Preorder β] [BoundedOrder α]
  extends: OrderHom α β
  axioms and operations (2):
    - map_top' : toFun ⊤ = ⊤
    - map_bot' : toFun ⊥ = ⊥

中文:
结构 有界序态射
  参数: (α β : 类型) [预序 α] [预序 β] [有界序 α]
  继承: 序态射 α β
  公理与运算 (2 个):
    - map_top' : toFun ⊤ = ⊤
    - map_bot' : toFun ⊥ = ⊥

Depends on / 依赖: BoundedOrderHom, BoundedOrderHom.mk, ValuationRing, map_bot, map_top, of_isDiscreteValuationRing
-/
structure BoundedOrderHom (α β : Type*) [Preorder α] [Preorder β] [BoundedOrder α]
  [BoundedOrder β] extends OrderHom α β where
  /-- The function preserves the top element. The preferred spelling is `map_top`. -/
  map_top' : toFun ⊤ = ⊤
  /-- The function preserves the bottom element. The preferred spelling is `map_bot`. -/
  map_bot' : toFun ⊥ = ⊥

attribute [to_dual self (reorder := map_top' map_bot')] BoundedOrderHom.mk
attribute [to_dual existing] BoundedOrderHom.map_bot'

section

/--
Definition of `TopHomClass` / `TopHomClass` 的定义

English:
class TopHomClass
  parameters: (F : Type*) (α β : outParam Type*) [Top α] [Top β] [FunLike F α β]
  axioms and operations (1):
    - map_top((f : F)) : f ⊤ = ⊤

中文:
类 顶元素态射类
  参数: (F : 类型) (α β : outParam 类型) [顶元素 α] [顶元素 β] [函数状 F α β]
  公理与运算 (1 个):
    - map_top((f : F)) : f ⊤ = ⊤
-/
class TopHomClass (F : Type*) (α β : outParam Type*) [Top α] [Top β] [FunLike F α β] :
    Prop where
  /-- A `TopHomClass` morphism preserves the top element. -/
  map_top (f : F) : f ⊤ = ⊤

/-- `BotHomClass F α β` states that `F` is a type of `⊥`-preserving morphisms.

You should extend this class when you extend `BotHom`. -/
@[to_dual]
/--
Definition of `BotHomClass` / `BotHomClass` 的定义

English:
class BotHomClass
  parameters: (F : Type*) (α β : outParam Type*) [Bot α] [Bot β] [FunLike F α β]
  axioms and operations (1):
    - map_bot((f : F)) : f ⊥ = ⊥

中文:
类 底元素态射类
  参数: (F : 类型) (α β : outParam 类型) [底元素 α] [底元素 β] [函数状 F α β]
  公理与运算 (1 个):
    - map_bot((f : F)) : f ⊥ = ⊥
-/
class BotHomClass (F : Type*) (α β : outParam Type*) [Bot α] [Bot β] [FunLike F α β] :
    Prop where
  /-- A `BotHomClass` morphism preserves the bottom element. -/
  map_bot (f : F) : f ⊥ = ⊥

/--
Definition of `BoundedOrderHomClass` / `BoundedOrderHomClass` 的定义

English:
class BoundedOrderHomClass
  parameters: (F α β : Type*) [LE α] [LE β]
  extends: RelHomClass F ((· <= ·) : α -> α -> Prop) ((· <= ·) : β -> β -> Prop)
  axioms and operations (2):
    - map_top((f : F)) : f ⊤ = ⊤
    - map_bot((f : F)) : f ⊥ = ⊥

中文:
类 有界序态射类
  参数: (F α β : 类型) [LE α] [LE β]
  继承: 关系态射类 F ((· <= ·) : α -> α -> 命题) ((· <= ·) : β -> β -> 命题)
  公理与运算 (2 个):
    - map_top((f : F)) : f ⊤ = ⊤
    - map_bot((f : F)) : f ⊥ = ⊥
-/
class BoundedOrderHomClass (F α β : Type*) [LE α] [LE β]
    [BoundedOrder α] [BoundedOrder β] [FunLike F α β] : Prop
  extends RelHomClass F ((· <= ·) : α -> α -> Prop) ((· <= ·) : β -> β -> Prop) where
  /-- Morphisms preserve the top element. The preferred spelling is `_root_.map_top`. -/
  map_top (f : F) : f ⊤ = ⊤
  /-- Morphisms preserve the bottom element. The preferred spelling is `_root_.map_bot`. -/
  map_bot (f : F) : f ⊥ = ⊥

attribute [to_dual existing] BoundedOrderHomClass.map_bot

end

export TopHomClass (map_top)

export BotHomClass (map_bot)

attribute [simp] map_top map_bot

section Hom

variable [FunLike F α β]

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) BoundedOrderHomClass.toTopHomClass [LE α] [LE β]
    [BoundedOrder α] [BoundedOrder β] [BoundedOrderHomClass F α β] : TopHomClass F α β where
  __ := ‹BoundedOrderHomClass F α β›

end Hom

section Equiv

variable [EquivLike F α β]

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) OrderIsoClass.toTopHomClass [LE α] [OrderTop α]
    [PartialOrder β] [OrderTop β] [OrderIsoClass F α β] : TopHomClass F α β where
map_top := fun f => top_le_iff.1 (map_inv_le_iff f).1 le_top

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toBoundedOrderHomClass [LE α] [BoundedOrder α]
    [PartialOrder β] [BoundedOrder β] [OrderIsoClass F α β] : BoundedOrderHomClass F α β where
  __ := OrderIsoClass.toTopHomClass
  __ := OrderIsoClass.toBotHomClass

@[to_dual (attr := simp)]
/--
theorem `map_eq_top_iff` / 定理 `map_eq_top_iff`

English:
theorem map_eq_top_iff
  statement: [LE α] [OrderTop α] [PartialOrder β] [OrderTop β] [OrderIsoClass F α β]
  proof: by
  rw [← map_top f]; rw [(EquivLike.injective f).eq_iff]

中文:
定理 map_eq_top_iff
  结论: [LE α] [有顶序 α] [偏序 β] [有顶序 β] [OrderIso类 F α β]
  证明: by
  rw [← map_top f]; rw [(EquivLike.injective f).eq_iff]

Depends on / 依赖: EquivLike, EquivLike.injective, eq_iff, injective, map_top
-/
theorem map_eq_top_iff [LE α] [OrderTop α] [PartialOrder β] [OrderTop β] [OrderIsoClass F α β]
    (f : F) {a : α} : f a = ⊤ ↔ a = ⊤ := by
  rw [← map_top f]; rw [(EquivLike.injective f).eq_iff]

end Equiv

variable [FunLike F α β]

/-- Turn an element of a type `F` satisfying `TopHomClass F α β` into an actual
`TopHom`. This is declared as the default coercion from `F` to `TopHom α β`. -/
@[to_dual (attr := coe) /--
Turn an element of a type `F` satisfying `BotHomClass F α β` into an actual
`BotHom`. This is declared as the default coercion from `F` to `BotHom α β`. -/]
/--
Definition of `TopHomClass.toTopHom` / `TopHomClass.toTopHom` 的定义

English:
definition TopHomClass.toTopHom
  signature: [Top α] [Top β] [TopHomClass F α β] (f : F)
  body: ⟨f, map_top f⟩

@[to_dual]

中文:
定义 顶元素态射类.toTopHom
  签名: [顶元素 α] [顶元素 β] [顶元素态射类 F α β] (f : F)
  定义体: ⟨f, map_top f⟩

@[to_dual]

Depends on / 依赖: map_top
-/
def TopHomClass.toTopHom [Top α] [Top β] [TopHomClass F α β] (f : F) : TopHom α β :=
  ⟨f, map_top f⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Top
  signature: α] [Top β] [TopHomClass F α β] : CoeTC F (TopHom α β)
  body: ⟨TopHomClass.toTopHom⟩

中文:
实例 [顶元素
  签名: α] [顶元素 β] [顶元素态射类 F α β] : CoeTC F (顶元素态射 α β)
  定义体: ⟨TopHomClass.toTopHom⟩

Depends on / 依赖: TopHomClass, TopHomClass.toTopHom, toTopHom
-/
instance [Top α] [Top β] [TopHomClass F α β] : CoeTC F (TopHom α β) :=
  ⟨TopHomClass.toTopHom⟩

/-- Turn an element of a type `F` satisfying `BoundedOrderHomClass F α β` into an actual
`BoundedOrderHom`. This is declared as the default coercion from `F` to `BoundedOrderHom α β`. -/
@[coe]
/--
Definition of `BoundedOrderHomClass.toBoundedOrderHom` / `BoundedOrderHomClass.toBoundedOrderHom` 的定义

English:
definition BoundedOrderHomClass.toBoundedOrderHom
  signature: [Preorder α] [Preorder β] [BoundedOrder α]
  body: { (f : α ->o β) with toFun := f, map_top' := map_top f, map_bot' := map_bot f }

中文:
定义 有界序态射类.toBoundedOrderHom
  签名: [预序 α] [预序 β] [有界序 α]
  定义体: { (f : α ->o β) with toFun := f, map_top' := map_top f, map_bot' := map_bot f }

Depends on / 依赖: map_bot, map_top
-/
def BoundedOrderHomClass.toBoundedOrderHom [Preorder α] [Preorder β] [BoundedOrder α]
    [BoundedOrder β] [BoundedOrderHomClass F α β] (f : F) : BoundedOrderHom α β :=
  { (f : α ->o β) with toFun := f, map_top' := map_top f, map_bot' := map_bot f }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] [Preorder β] [BoundedOrder α] [BoundedOrder β] [BoundedOrderHomClass F α β] :
  body: ⟨BoundedOrderHomClass.toBoundedOrderHom⟩

中文:
实例 [预序
  签名: α] [预序 β] [有界序 α] [有界序 β] [有界序态射类 F α β] :
  定义体: ⟨BoundedOrderHomClass.toBoundedOrderHom⟩

Depends on / 依赖: BoundedOrderHomClass, BoundedOrderHomClass.toBoundedOrderHom, toBoundedOrderHom
-/
instance [Preorder α] [Preorder β] [BoundedOrder α] [BoundedOrder β] [BoundedOrderHomClass F α β] :
    CoeTC F (BoundedOrderHom α β) :=
  ⟨BoundedOrderHomClass.toBoundedOrderHom⟩

/-! ### Top and bot homomorphisms -/


namespace TopHom

variable [Top α]

section Top

variable [Top β] [Top γ] [Top δ]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (TopHom α β) α β
  body: TopHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_dual]

中文:
实例 :
  签名: 函数状 (顶元素态射 α β) α β
  定义体: TopHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_dual]

Depends on / 依赖: TopHom, TopHom.toFun
-/
instance : FunLike (TopHom α β) α β where
  coe := TopHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopHomClass (TopHom α β) α β
  body: TopHom.map_top'

中文:
实例 :
  签名: 顶元素态射类 (顶元素态射 α β) α β
  定义体: TopHom.map_top'

Depends on / 依赖: TopHom, TopHom.map_top, map_top
-/
instance : TopHomClass (TopHom α β) α β where
  map_top := TopHom.map_top'

-- this must come after the coe_to_fun definition
initialize_simps_projections TopHom (toFun -> apply)
initialize_simps_projections BotHom (toFun -> apply)

@[to_dual (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : TopHom α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : 顶元素态射 α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : TopHom α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `TopHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_dual /--
Copy of a `BotHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : TopHom α β) (f' : α -> β) (h : f' = f)
  body: f'
  map_top' := h.symm ▸ f.map_top'

@[to_dual (attr := simp)]

中文:
定义 copy
  签名: (f : 顶元素态射 α β) (f' : α -> β) (h : f' = f)
  定义体: f'
  map_top' := h.symm ▸ f.map_top'

@[to_dual (attr := simp)]
-/
protected def copy (f : TopHom α β) (f' : α -> β) (h : f' = f) :
    TopHom α β where
  toFun := f'
  map_top' := h.symm ▸ f.map_top'

@[to_dual (attr := simp)]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : TopHom α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

@[to_dual]

中文:
定理 coe_copy
  条件: (f : 顶元素态射 α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl

@[to_dual]
-/
theorem coe_copy (f : TopHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

@[to_dual]
/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : TopHom α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

@[to_dual]

中文:
定理 copy_eq
  条件: (f : 顶元素态射 α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

@[to_dual]

Depends on / 依赖: DFunLike, DFunLike.ext, IsDedekindDomain, IsDedekindDomain.isPrincipalIdealRing, isPrincipalIdealRing
-/
theorem copy_eq (f : TopHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (TopHom α β)
  body: ⟨⟨fun _ => ⊤, rfl⟩⟩

中文:
实例 :
  签名: 可居 (顶元素态射 α β)
  定义体: ⟨⟨fun _ => ⊤, rfl⟩⟩
-/
instance : Inhabited (TopHom α β) :=
  ⟨⟨fun _ => ⊤, rfl⟩⟩

variable (α)

/-- `id` as a `TopHom`. -/
@[to_dual /-- `id` as a `BotHom`. -/]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : TopHom α α
  body: ⟨id, rfl⟩

@[to_dual (attr := simp, norm_cast)]

中文:
定义 id
  签名: : 顶元素态射 α α
  定义体: ⟨id, rfl⟩

@[to_dual (attr := simp, norm_cast)]
-/
protected def id : TopHom α α :=
  ⟨id, rfl⟩

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(TopHom.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(顶元素态射.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(TopHom.id α) = id :=
  rfl

variable {α}

@[to_dual (attr := simp)]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: TopHom.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: 顶元素态射.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : TopHom.id α a = a :=
  rfl

/-- Composition of `TopHom`s as a `TopHom`. -/
@[to_dual /-- Composition of `BotHom`s as a `BotHom`. -/]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : TopHom β γ) (g : TopHom α β)
  body: f ∘ g
  map_top' := by rw [comp_apply, map_top, map_top]

@[to_dual (attr := simp)]

中文:
定义 comp
  签名: (f : 顶元素态射 β γ) (g : 顶元素态射 α β)
  定义体: f ∘ g
  map_top' := by rw [comp_apply, map_top, map_top]

@[to_dual (attr := simp)]
-/
def comp (f : TopHom β γ) (g : TopHom α β) :
    TopHom α γ where
  toFun := f ∘ g
  map_top' := by rw [comp_apply, map_top, map_top]

@[to_dual (attr := simp)]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : TopHom β γ) (g : TopHom α β)
  statement: (f.comp g : α -> γ) = f ∘ g
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_comp
  条件: (f : 顶元素态射 β γ) (g : 顶元素态射 α β)
  结论: (f.comp g : α -> γ) = f ∘ g
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_comp (f : TopHom β γ) (g : TopHom α β) : (f.comp g : α -> γ) = f ∘ g :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : TopHom β γ) (g : TopHom α β) (a : α)
  statement: (f.comp g) a = f (g a)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 comp_apply
  条件: (f : 顶元素态射 β γ) (g : 顶元素态射 α β) (a : α)
  结论: (f.comp g) a = f (g a)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem comp_apply (f : TopHom β γ) (g : TopHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : TopHom γ δ) (g : TopHom β γ) (h : TopHom α β)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 comp_assoc
  条件: (f : 顶元素态射 γ δ) (g : 顶元素态射 β γ) (h : 顶元素态射 α β)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem comp_assoc (f : TopHom γ δ) (g : TopHom β γ) (h : TopHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : TopHom α β)
  statement: f.comp (TopHom.id α) = f
  proof: TopHom.ext fun _ => rfl

@[to_dual (attr := simp)]

中文:
定理 comp_id
  条件: (f : 顶元素态射 α β)
  结论: f.comp (顶元素态射.id α) = f
  证明: TopHom.ext fun _ => rfl

@[to_dual (attr := simp)]

Depends on / 依赖: TopHom, TopHom.ext
-/
theorem comp_id (f : TopHom α β) : f.comp (TopHom.id α) = f :=
  TopHom.ext fun _ => rfl

@[to_dual (attr := simp)]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : TopHom α β)
  statement: (TopHom.id β).comp f = f
  proof: TopHom.ext fun _ => rfl

@[to_dual (attr := simp)]

中文:
定理 id_comp
  条件: (f : 顶元素态射 α β)
  结论: (顶元素态射.id β).comp f = f
  证明: TopHom.ext fun _ => rfl

@[to_dual (attr := simp)]

Depends on / 依赖: TopHom, TopHom.ext
-/
theorem id_comp (f : TopHom α β) : (TopHom.id β).comp f = f :=
  TopHom.ext fun _ => rfl

@[to_dual (attr := simp)]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : TopHom β γ} {f : TopHom α β} (hf : Surjective f)
  proof: ⟨fun h => TopHom.ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun g => comp g f)⟩

@[to_dual (attr := simp)]

中文:
定理 cancel_right
  条件: {g₁ g₂ : 顶元素态射 β γ} {f : 顶元素态射 α β} (hf : 满射 f)
  证明: ⟨fun h => TopHom.ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun g => comp g f)⟩

@[to_dual (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, TopHom, TopHom.ext, congr_arg, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : TopHom β γ} {f : TopHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => TopHom.ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun g => comp g f)⟩

@[to_dual (attr := simp)]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : TopHom β γ} {f₁ f₂ : TopHom α β} (hg : Injective g)
  proof: ⟨fun h => TopHom.ext fun a => hg by rw [← TopHom.comp_apply, h, TopHom.comp_apply],
    congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : 顶元素态射 β γ} {f₁ f₂ : 顶元素态射 α β} (hg : 单射 g)
  证明: ⟨fun h => TopHom.ext fun a => hg by rw [← TopHom.comp_apply, h, TopHom.comp_apply],
    congr_arg _⟩

Depends on / 依赖: TopHom, TopHom.comp_apply, TopHom.ext, comp_apply, congr_arg
-/
theorem cancel_left {g : TopHom β γ} {f₁ f₂ : TopHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => TopHom.ext fun a => hg by rw [← TopHom.comp_apply, h, TopHom.comp_apply],
    congr_arg _⟩

end Top

@[to_dual]
/--
Instance `instLE` / 实例 `instLE`

English:
instance instLE
  signature: [LE β] [Top β]
  body: (f : α -> β) <= g

@[to_dual]

中文:
实例 instLE
  签名: [LE β] [顶元素 β]
  定义体: (f : α -> β) <= g

@[to_dual]
-/
instance instLE [LE β] [Top β] : LE (TopHom α β) where
  le f g := (f : α -> β) <= g

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: β] [Top β] : Preorder (TopHom α β)
  body: Preorder.lift (DFunLike.coe : TopHom α β -> α -> β)

@[to_dual]

中文:
实例 [预序
  签名: β] [顶元素 β] : 预序 (顶元素态射 α β)
  定义体: Preorder.lift (DFunLike.coe : TopHom α β -> α -> β)

@[to_dual]

Depends on / 依赖: DFunLike, DFunLike.coe, Preorder, Preorder.lift, TopHom
-/
instance [Preorder β] [Top β] : Preorder (TopHom α β) :=
  Preorder.lift (DFunLike.coe : TopHom α β -> α -> β)

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: β] [Top β] : PartialOrder (TopHom α β)
  body: PartialOrder.lift _ DFunLike.coe_injective

中文:
实例 [偏序
  签名: β] [顶元素 β] : 偏序 (顶元素态射 α β)
  定义体: PartialOrder.lift _ DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective
-/
instance [PartialOrder β] [Top β] : PartialOrder (TopHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

section OrderTop

variable [LE β] [OrderTop β]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTop (TopHom α β)
  body: ⟨⊤, rfl⟩
  le_top := fun _ => @le_top (α -> β) _ _ _

@[to_dual (attr := simp)]

中文:
实例 :
  签名: 有顶序 (顶元素态射 α β)
  定义体: ⟨⊤, rfl⟩
  le_top := fun _ => @le_top (α -> β) _ _ _

@[to_dual (attr := simp)]
-/
instance : OrderTop (TopHom α β) where
  top := ⟨⊤, rfl⟩
  le_top := fun _ => @le_top (α -> β) _ _ _

@[to_dual (attr := simp)]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ⇑(⊤ : TopHom α β) = ⊤
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_top
  结论: ⇑(⊤ : 顶元素态射 α β) = ⊤
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_top : ⇑(⊤ : TopHom α β) = ⊤ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `top_apply` / 定理 `top_apply`

English:
theorem top_apply
  given: (a : α)
  statement: (⊤ : TopHom α β) a = ⊤
  proof: rfl

中文:
定理 top_apply
  条件: (a : α)
  结论: (⊤ : 顶元素态射 α β) a = ⊤
  证明: rfl
-/
theorem top_apply (a : α) : (⊤ : TopHom α β) a = ⊤ :=
  rfl

end OrderTop

section SemilatticeInf

variable [SemilatticeInf β] [OrderTop β] (f g : TopHom α β)

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (TopHom α β)
  body: ⟨fun f g => ⟨f ⊓ g, by rw [Pi.inf_apply, map_top, map_top, inf_top_eq]⟩⟩

@[to_dual]

中文:
实例 :
  签名: 最小值 (顶元素态射 α β)
  定义体: ⟨fun f g => ⟨f ⊓ g, by rw [Pi.inf_apply, map_top, map_top, inf_top_eq]⟩⟩

@[to_dual]

Depends on / 依赖: Pi.inf_apply, inf_apply, inf_top_eq, map_top
-/
instance : Min (TopHom α β) :=
  ⟨fun f g => ⟨f ⊓ g, by rw [Pi.inf_apply, map_top, map_top, inf_top_eq]⟩⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeInf (TopHom α β)
  body: DFunLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[to_dual (attr := simp)]

中文:
实例 :
  签名: SemilatticeInf (顶元素态射 α β)
  定义体: DFunLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[to_dual (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.semilatticeInf, coe_injective, semilatticeInf
-/
instance : SemilatticeInf (TopHom α β) :=
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[to_dual (attr := simp)]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  statement: ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_inf
  结论: ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_inf : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `inf_apply` / 定理 `inf_apply`

English:
theorem inf_apply
  given: (a : α)
  statement: (f ⊓ g) a = f a ⊓ g a
  proof: rfl

中文:
定理 inf_apply
  条件: (a : α)
  结论: (f ⊓ g) a = f a ⊓ g a
  证明: rfl
-/
theorem inf_apply (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl

end SemilatticeInf

section SemilatticeSup

variable [SemilatticeSup β] [OrderTop β] (f g : TopHom α β)

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (TopHom α β)
  body: ⟨fun f g => ⟨f ⊔ g, by rw [Pi.sup_apply, map_top, map_top, sup_top_eq]⟩⟩

@[to_dual]

中文:
实例 :
  签名: 最大值 (顶元素态射 α β)
  定义体: ⟨fun f g => ⟨f ⊔ g, by rw [Pi.sup_apply, map_top, map_top, sup_top_eq]⟩⟩

@[to_dual]

Depends on / 依赖: Pi.sup_apply, map_top, sup_apply, sup_top_eq
-/
instance : Max (TopHom α β) :=
  ⟨fun f g => ⟨f ⊔ g, by rw [Pi.sup_apply, map_top, map_top, sup_top_eq]⟩⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (TopHom α β)
  body: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[to_dual (attr := simp)]

中文:
实例 :
  签名: SemilatticeSup (顶元素态射 α β)
  定义体: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[to_dual (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.semilatticeSup, coe_injective, semilatticeSup
-/
instance : SemilatticeSup (TopHom α β) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[to_dual (attr := simp)]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  statement: ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_sup
  结论: ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_sup : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `sup_apply` / 定理 `sup_apply`

English:
theorem sup_apply
  given: (a : α)
  statement: (f ⊔ g) a = f a ⊔ g a
  proof: rfl

中文:
定理 sup_apply
  条件: (a : α)
  结论: (f ⊔ g) a = f a ⊔ g a
  证明: rfl
-/
theorem sup_apply (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl

end SemilatticeSup

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Lattice
  signature: β] [OrderTop β] : Lattice (TopHom α β)
  body: DFunLike.coe_injective.lattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_dual]

中文:
实例 [格
  签名: β] [有顶序 β] : 格 (顶元素态射 α β)
  定义体: DFunLike.coe_injective.lattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_dual]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.lattice, _apply, aeval_X, coe_injective, dp_def, hf_add, hf_mul, hf_smul, hf_zero, lattice
-/
instance [Lattice β] [OrderTop β] : Lattice (TopHom α β) :=
  DFunLike.coe_injective.lattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribLattice
  signature: β] [OrderTop β] : DistribLattice (TopHom α β)
  body: DFunLike.coe_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [Distrib格
  签名: β] [有顶序 β] : Distrib格 (顶元素态射 α β)
  定义体: DFunLike.coe_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.distribLattice, coe_injective, distribLattice
-/
instance [DistribLattice β] [OrderTop β] : DistribLattice (TopHom α β) :=
  DFunLike.coe_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

end TopHom

/-! ### Bounded order homomorphisms -/

-- TODO: remove this configuration and use the default configuration.
initialize_simps_projections BoundedOrderHom (+toOrderHom, -toFun)

namespace BoundedOrderHom

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [BoundedOrder α] [BoundedOrder β]
  [BoundedOrder γ] [BoundedOrder δ]

/-- Reinterpret a `BoundedOrderHom` as a `TopHom`. -/
@[to_dual /-- Reinterpret a `BoundedOrderHom` as a `BotHom`. -/]
/--
Definition of `toTopHom` / `toTopHom` 的定义

English:
definition toTopHom
  signature: (f : BoundedOrderHom α β)
  body: f

中文:
定义 toTopHom
  签名: (f : 有界序态射 α β)
  定义体: f
-/
def toTopHom (f : BoundedOrderHom α β) : TopHom α β where
  __ := f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (BoundedOrderHom α β) α β
  body: f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

中文:
实例 :
  签名: 函数状 (有界序态射 α β) α β
  定义体: f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

Depends on / 依赖: f.toFun
-/
instance : FunLike (BoundedOrderHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedOrderHomClass (BoundedOrderHom α β) α β
  body: @(f.monotone')
  map_top f := f.map_top'
  map_bot f := f.map_bot'

@[ext]

中文:
实例 :
  签名: 有界序态射类 (有界序态射 α β) α β
  定义体: @(f.monotone')
  map_top f := f.map_top'
  map_bot f := f.map_bot'

@[ext]

Depends on / 依赖: f.monotone, monotone
-/
instance : BoundedOrderHomClass (BoundedOrderHom α β) α β where
  map_rel f := @(f.monotone')
  map_top f := f.map_top'
  map_bot f := f.map_bot'

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : BoundedOrderHom α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : 有界序态射 α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : BoundedOrderHom α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : BoundedOrderHom α β) (f' : α -> β) (h : f' = f)
  body: { f.toOrderHom.copy f' h, f.toTopHom.copy f' h, f.toBotHom.copy f' h with }

@[simp]

中文:
定义 copy
  签名: (f : 有界序态射 α β) (f' : α -> β) (h : f' = f)
  定义体: { f.toOrderHom.copy f' h, f.toTopHom.copy f' h, f.toBotHom.copy f' h with }

@[simp]
-/
protected def copy (f : BoundedOrderHom α β) (f' : α -> β) (h : f' = f) : BoundedOrderHom α β :=
  { f.toOrderHom.copy f' h, f.toTopHom.copy f' h, f.toBotHom.copy f' h with }

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : BoundedOrderHom α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : 有界序态射 α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : BoundedOrderHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : BoundedOrderHom α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : 有界序态射 α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : BoundedOrderHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : BoundedOrderHom α α
  body: { OrderHom.id, TopHom.id α, BotHom.id α with }

中文:
定义 id
  签名: : 有界序态射 α α
  定义体: { OrderHom.id, TopHom.id α, BotHom.id α with }
-/
protected def id : BoundedOrderHom α α :=
  { OrderHom.id, TopHom.id α, BotHom.id α with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (BoundedOrderHom α α)
  body: ⟨BoundedOrderHom.id α⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 可居 (有界序态射 α α)
  定义体: ⟨BoundedOrderHom.id α⟩

@[simp, norm_cast]

Depends on / 依赖: BoundedOrderHom, BoundedOrderHom.id
-/
instance : Inhabited (BoundedOrderHom α α) :=
  ⟨BoundedOrderHom.id α⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(BoundedOrderHom.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(有界序态射.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(BoundedOrderHom.id α) = id :=
  rfl

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: BoundedOrderHom.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: 有界序态射.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : BoundedOrderHom.id α a = a :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β)
  body: { f.toOrderHom.comp g.toOrderHom, f.toTopHom.comp g.toTopHom, f.toBotHom.comp g.toBotHom with }

@[simp]

中文:
定义 comp
  签名: (f : 有界序态射 β γ) (g : 有界序态射 α β)
  定义体: { f.toOrderHom.comp g.toOrderHom, f.toTopHom.comp g.toTopHom, f.toBotHom.comp g.toBotHom with }

@[simp]

Depends on / 依赖: f.toBotHom.comp, f.toOrderHom.comp, f.toTopHom.comp, g.toBotHom, g.toOrderHom, g.toTopHom, toBotHom, toOrderHom, toTopHom
-/
def comp (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) : BoundedOrderHom α γ :=
  { f.toOrderHom.comp g.toOrderHom, f.toTopHom.comp g.toTopHom, f.toBotHom.comp g.toBotHom with }

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β)
  statement: (f.comp g : α -> γ) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : 有界序态射 β γ) (g : 有界序态射 α β)
  结论: (f.comp g : α -> γ) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) : (f.comp g : α -> γ) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) (a : α)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : 有界序态射 β γ) (g : 有界序态射 α β) (a : α)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl

@[simp]
/--
theorem `coe_comp_orderHom` / 定理 `coe_comp_orderHom`

English:
theorem coe_comp_orderHom
  given: (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_comp_orderHom
  条件: (f : 有界序态射 β γ) (g : 有界序态射 α β)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_comp_orderHom (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) :
    (f.comp g : OrderHom α γ) = (f : OrderHom β γ).comp g :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `coe_comp_topHom` / 定理 `coe_comp_topHom`

English:
theorem coe_comp_topHom
  given: (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β)
  proof: rfl

@[simp]

中文:
定理 coe_comp_topHom
  条件: (f : 有界序态射 β γ) (g : 有界序态射 α β)
  证明: rfl

@[simp]
-/
theorem coe_comp_topHom (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) :
    (f.comp g : TopHom α γ) = (f : TopHom β γ).comp g :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : BoundedOrderHom γ δ) (g : BoundedOrderHom β γ) (h : BoundedOrderHom α β)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : 有界序态射 γ δ) (g : 有界序态射 β γ) (h : 有界序态射 α β)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : BoundedOrderHom γ δ) (g : BoundedOrderHom β γ) (h : BoundedOrderHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : BoundedOrderHom α β)
  statement: f.comp (BoundedOrderHom.id α) = f
  proof: BoundedOrderHom.ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : 有界序态射 α β)
  结论: f.comp (有界序态射.id α) = f
  证明: BoundedOrderHom.ext fun _ => rfl

@[simp]

Depends on / 依赖: BoundedOrderHom, BoundedOrderHom.ext
-/
theorem comp_id (f : BoundedOrderHom α β) : f.comp (BoundedOrderHom.id α) = f :=
  BoundedOrderHom.ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : BoundedOrderHom α β)
  statement: (BoundedOrderHom.id β).comp f = f
  proof: BoundedOrderHom.ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : 有界序态射 α β)
  结论: (有界序态射.id β).comp f = f
  证明: BoundedOrderHom.ext fun _ => rfl

@[simp]

Depends on / 依赖: BoundedOrderHom, BoundedOrderHom.ext
-/
theorem id_comp (f : BoundedOrderHom α β) : (BoundedOrderHom.id β).comp f = f :=
  BoundedOrderHom.ext fun _ => rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : BoundedOrderHom β γ} {f : BoundedOrderHom α β} (hf : Surjective f)
  proof: ⟨fun h => BoundedOrderHom.ext hf.forall.2 DFunLike.ext_iff.1 h,
   congr_arg (fun g => comp g f)⟩

@[simp]

中文:
定理 cancel_right
  条件: {g₁ g₂ : 有界序态射 β γ} {f : 有界序态射 α β} (hf : 满射 f)
  证明: ⟨fun h => BoundedOrderHom.ext hf.forall.2 DFunLike.ext_iff.1 h,
   congr_arg (fun g => comp g f)⟩

@[simp]

Depends on / 依赖: BoundedOrderHom, BoundedOrderHom.ext, DFunLike, DFunLike.ext_iff, congr_arg, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : BoundedOrderHom β γ} {f : BoundedOrderHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => BoundedOrderHom.ext hf.forall.2 DFunLike.ext_iff.1 h,
   congr_arg (fun g => comp g f)⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : BoundedOrderHom β γ} {f₁ f₂ : BoundedOrderHom α β} (hg : Injective g)
  proof: ⟨fun h =>
    BoundedOrderHom.ext fun a =>
hg by rw [← BoundedOrderHom.comp_apply, h, BoundedOrderHom.comp_apply],
    congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : 有界序态射 β γ} {f₁ f₂ : 有界序态射 α β} (hg : 单射 g)
  证明: ⟨fun h =>
    BoundedOrderHom.ext fun a =>
hg by rw [← BoundedOrderHom.comp_apply, h, BoundedOrderHom.comp_apply],
    congr_arg _⟩

Depends on / 依赖: BoundedOrderHom, BoundedOrderHom.comp_apply, BoundedOrderHom.ext, comp_apply, congr_arg
-/
theorem cancel_left {g : BoundedOrderHom β γ} {f₁ f₂ : BoundedOrderHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    BoundedOrderHom.ext fun a =>
hg by rw [← BoundedOrderHom.comp_apply, h, BoundedOrderHom.comp_apply],
    congr_arg _⟩

end BoundedOrderHom

/-! ### Dual homs -/


namespace TopHom

variable [LE α] [OrderTop α] [LE β] [OrderTop β] [LE γ] [OrderTop γ]

/-- Reinterpret a top homomorphism as a bot homomorphism between the dual lattices. -/
@[to_dual (attr := simps) /--
Reinterpret a bot homomorphism as a top homomorphism between the dual lattices. -/]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: :
  body: ⟨f, f.map_top'⟩
  invFun f := ⟨f, f.map_bot'⟩

@[to_dual (attr := simp)]

中文:
定义 dual
  签名: :
  定义体: ⟨f, f.map_top'⟩
  invFun f := ⟨f, f.map_bot'⟩

@[to_dual (attr := simp)]
-/
protected def dual :
    TopHom α β ≃ BotHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨f, f.map_top'⟩
  invFun f := ⟨f, f.map_bot'⟩

@[to_dual (attr := simp)]
/--
theorem `dual_id` / 定理 `dual_id`

English:
theorem dual_id
  statement: TopHom.dual (TopHom.id α) = BotHom.id _
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 dual_id
  结论: 顶元素态射.dual (顶元素态射.id α) = 底元素态射.id _
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem dual_id : TopHom.dual (TopHom.id α) = BotHom.id _ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `dual_comp` / 定理 `dual_comp`

English:
theorem dual_comp
  given: (g : TopHom β γ) (f : TopHom α β)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 dual_comp
  条件: (g : 顶元素态射 β γ) (f : 顶元素态射 α β)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem dual_comp (g : TopHom β γ) (f : TopHom α β) :
    TopHom.dual (g.comp f) = g.dual.comp (TopHom.dual f) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `symm_dual_id` / 定理 `symm_dual_id`

English:
theorem symm_dual_id
  statement: TopHom.dual.symm (BotHom.id _) = TopHom.id α
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 symm_dual_id
  结论: 顶元素态射.dual.symm (底元素态射.id _) = 顶元素态射.id α
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem symm_dual_id : TopHom.dual.symm (BotHom.id _) = TopHom.id α :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `symm_dual_comp` / 定理 `symm_dual_comp`

English:
theorem symm_dual_comp
  given: (g : BotHom βᵒᵈ γᵒᵈ) (f : BotHom αᵒᵈ βᵒᵈ)
  proof: rfl

中文:
定理 symm_dual_comp
  条件: (g : 底元素态射 βᵒᵈ γᵒᵈ) (f : 底元素态射 αᵒᵈ βᵒᵈ)
  证明: rfl

Depends on / 依赖: dividedPowersBot
-/
theorem symm_dual_comp (g : BotHom βᵒᵈ γᵒᵈ) (f : BotHom αᵒᵈ βᵒᵈ) :
    TopHom.dual.symm (g.comp f) = (TopHom.dual.symm g).comp (TopHom.dual.symm f) :=
  rfl

end TopHom

namespace BoundedOrderHom

variable [Preorder α] [BoundedOrder α] [Preorder β] [BoundedOrder β] [Preorder γ] [BoundedOrder γ]

/-- Reinterpret a bounded order homomorphism as a bounded order homomorphism between the dual
orders. -/
@[simps]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: :
  body: ⟨f.toOrderHom.dual, f.map_bot', f.map_top'⟩
  invFun f := ⟨OrderHom.dual.symm f.toOrderHom, f.map_bot', f.map_top'⟩

@[simp]

中文:
定义 dual
  签名: :
  定义体: ⟨f.toOrderHom.dual, f.map_bot', f.map_top'⟩
  invFun f := ⟨OrderHom.dual.symm f.toOrderHom, f.map_bot', f.map_top'⟩

@[simp]

Depends on / 依赖: hI.dpow
-/
protected def dual :
    BoundedOrderHom α β ≃
      BoundedOrderHom αᵒᵈ
        βᵒᵈ where
  toFun f := ⟨f.toOrderHom.dual, f.map_bot', f.map_top'⟩
  invFun f := ⟨OrderHom.dual.symm f.toOrderHom, f.map_bot', f.map_top'⟩

@[simp]
/--
theorem `dual_id` / 定理 `dual_id`

English:
theorem dual_id
  statement: (BoundedOrderHom.id α).dual = BoundedOrderHom.id _
  proof: rfl

@[simp]

中文:
定理 dual_id
  结论: (有界序态射.id α).dual = 有界序态射.id _
  证明: rfl

@[simp]
-/
theorem dual_id : (BoundedOrderHom.id α).dual = BoundedOrderHom.id _ :=
  rfl

@[simp]
/--
theorem `dual_comp` / 定理 `dual_comp`

English:
theorem dual_comp
  given: (g : BoundedOrderHom β γ) (f : BoundedOrderHom α β)
  proof: rfl

@[simp]

中文:
定理 dual_comp
  条件: (g : 有界序态射 β γ) (f : 有界序态射 α β)
  证明: rfl

@[simp]
-/
theorem dual_comp (g : BoundedOrderHom β γ) (f : BoundedOrderHom α β) :
    (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
/--
theorem `symm_dual_id` / 定理 `symm_dual_id`

English:
theorem symm_dual_id
  statement: BoundedOrderHom.dual.symm (BoundedOrderHom.id _) = BoundedOrderHom.id α
  proof: rfl

@[simp]

中文:
定理 symm_dual_id
  结论: 有界序态射.dual.symm (有界序态射.id _) = 有界序态射.id α
  证明: rfl

@[simp]
-/
theorem symm_dual_id : BoundedOrderHom.dual.symm (BoundedOrderHom.id _) = BoundedOrderHom.id α :=
  rfl

@[simp]
/--
theorem `symm_dual_comp` / 定理 `symm_dual_comp`

English:
theorem symm_dual_comp
  given: (g : BoundedOrderHom βᵒᵈ γᵒᵈ) (f : BoundedOrderHom αᵒᵈ βᵒᵈ)
  proof: rfl

中文:
定理 symm_dual_comp
  条件: (g : 有界序态射 βᵒᵈ γᵒᵈ) (f : 有界序态射 αᵒᵈ βᵒᵈ)
  证明: rfl
-/
theorem symm_dual_comp (g : BoundedOrderHom βᵒᵈ γᵒᵈ) (f : BoundedOrderHom αᵒᵈ βᵒᵈ) :
    BoundedOrderHom.dual.symm (g.comp f) =
      (BoundedOrderHom.dual.symm g).comp (BoundedOrderHom.dual.symm f) :=
  rfl

end BoundedOrderHom
