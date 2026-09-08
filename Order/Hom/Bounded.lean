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

/-- The type of `⊤`-preserving functions from `α` to `β`. -/
/-
**TopHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [Top α] → [Top β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `⊤`-preserving functions from `α` to `β`.
-/
structure TopHom (α β : Type*) [Top α] [Top β] where
  /-- The underlying function. The preferred spelling is `DFunLike.coe`. -/
  toFun : α → β
  /-- The function preserves the top element. The preferred spelling is `map_top`. -/
  map_top' : toFun ⊤ = ⊤

/-- The type of `⊥`-preserving functions from `α` to `β`. -/
@[to_dual]
/-
**BotHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [Bot α] → [Bot β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `⊥`-preserving functions from `α` to `β`.
-/
structure BotHom (α β : Type*) [Bot α] [Bot β] where
  /-- The underlying function. The preferred spelling is `DFunLike.coe`. -/
  toFun : α → β
  /-- The function preserves the bottom element. The preferred spelling is `map_bot`. -/
  map_bot' : toFun ⊥ = ⊥

/-- The type of bounded order homomorphisms from `α` to `β`. -/
/-
**BoundedOrderHom** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：BoundedOrderHom (α β : Type*) [Preorder α] [Preorder β] [BoundedOrder α] [
BoundedOrder β] extends OrderHom α β where /-- The function preserves the top el
ement. The preferred spelling is `map_top`. -/ map_top' : toFun ⊤ = ⊤ /-- The fu
nction preserves the bottom element. The preferred spelling is `map_bot`. -/ map
_bot' : toFun ⊥ = ⊥  attribute [to_dual self (reorder
参数：α β : Type*。
继承自：OrderHom α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of bounded order homomorphisms from `α` to `β`.
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

/-- `TopHomClass F α β` states that `F` is a type of `⊤`-preserving morphisms.

You should extend this class when you extend `TopHom`. -/
/-
**TopHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) → (α : outParam (Type u_7)) → (β : outParam (Type u_8)) → [
Top α] → [Top β] → [FunLike F α β] → Prop
参数：Type u_7；Type u_8。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TopHomClass F α β` states that `F` is a type of `⊤`-preserving morphisms.

You should extend this class when you extend `TopHom`.
-/
class TopHomClass (F : Type*) (α β : outParam Type*) [Top α] [Top β] [FunLike F α β] :
    Prop where
  /-- A `TopHomClass` morphism preserves the top element. -/
  map_top (f : F) : f ⊤ = ⊤

/-- `BotHomClass F α β` states that `F` is a type of `⊥`-preserving morphisms.

You should extend this class when you extend `BotHom`. -/
@[to_dual]
/-
**BotHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) → (α : outParam (Type u_7)) → (β : outParam (Type u_8)) → [
Bot α] → [Bot β] → [FunLike F α β] → Prop
参数：Type u_7；Type u_8。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BotHomClass F α β` states that `F` is a type of `⊥`-preserving morphisms.

You should extend this class when you extend `BotHom`.
-/
class BotHomClass (F : Type*) (α β : outParam Type*) [Bot α] [Bot β] [FunLike F α β] :
    Prop where
  /-- A `BotHomClass` morphism preserves the bottom element. -/
  map_bot (f : F) : f ⊥ = ⊥

/-- `BoundedOrderHomClass F α β` states that `F` is a type of bounded order morphisms.

You should extend this class when you extend `BoundedOrderHom`. -/
/-
**BoundedOrderHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) →   (α : Type u_7) →     (β : Type u_8) → [inst : LE α] → [
inst_1 : LE β] → [BoundedOrder α] → [BoundedOrder β] → [FunLike F α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BoundedOrderHomClass F α β` states that `F` is a type of bounded order morphism
s.

You should extend this class when you extend `BoundedOrderHom`.
-/
class BoundedOrderHomClass (F α β : Type*) [LE α] [LE β]
    [BoundedOrder α] [BoundedOrder β] [FunLike F α β] : Prop
  extends RelHomClass F ((· ≤ ·) : α → α → Prop) ((· ≤ ·) : β → β → Prop) where
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
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) BoundedOrderHomClass.toTopHomClass [LE α] [LE β]
    [BoundedOrder α] [BoundedOrder β] [BoundedOrderHomClass F α β] : TopHomClass F α β where
  __ := ‹BoundedOrderHomClass F α β›

end Hom

section Equiv

variable [EquivLike F α β]

-- See note [lower instance priority]
@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderIsoClass.toTopHomClass [LE α] [OrderTop α]
    [PartialOrder β] [OrderTop β] [OrderIsoClass F α β] : TopHomClass F α β where
  map_top := fun f => top_le_iff.1 <| (map_inv_le_iff f).1 le_top

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderIsoClass.toBoundedOrderHomClass [LE α] [BoundedOrder α]
    [PartialOrder β] [BoundedOrder β] [OrderIsoClass F α β] : BoundedOrderHomClass F α β where
  __ := OrderIsoClass.toTopHomClass
  __ := OrderIsoClass.toBotHomClass

@[to_dual (attr := simp)]
/-
**map_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_eq_top_iff [LE α] [OrderTop α] [PartialOrder β] [OrderTop β] [OrderIso
Class F α β] (f : F) {a : α} : f a = ⊤ ↔ a = ⊤
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopHomClass.map_top`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Top α} {inst_1 : Top β}   {inst_2 : FunLike F α β} [se
lf : TopH…
· 使用定理 `OrderIsoClass.toTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : EquivLike F α β] [inst_1 : LE α] [inst_2 : OrderTop α]   [inst_3 : P
artialOrder β] [i…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_eq_top_iff [LE α] [OrderTop α] [PartialOrder β] [OrderTop β] [OrderIsoClass F α β]
    (f : F) {a : α} : f a = ⊤ ↔ a = ⊤ := by
  rw [← map_top f, (EquivLike.injective f).eq_iff]

end Equiv

variable [FunLike F α β]

/-- Turn an element of a type `F` satisfying `TopHomClass F α β` into an actual
`TopHom`. This is declared as the default coercion from `F` to `TopHom α β`. -/
@[to_dual (attr := coe) /--
Turn an element of a type `F` satisfying `BotHomClass F α β` into an actual
`BotHom`. This is declared as the default coercion from `F` to `BotHom α β`. -/]
/-
**TopHomClass.toTopHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TopHomClass.toTopHom [Top α] [Top β] [TopHomClass F α β] (f : F) : TopHom 
α β
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopHomClass.map_top`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Top α} {inst_1 : Top β}   {inst_2 : FunLike F α β} [se
lf : TopH…
-/
def TopHomClass.toTopHom [Top α] [Top β] [TopHomClass F α β] (f : F) : TopHom α β :=
  ⟨f, map_top f⟩

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Top α] [Top β] [TopHomClass F α β] : CoeTC F (TopHom α β) :=
  ⟨TopHomClass.toTopHom⟩

/-- Turn an element of a type `F` satisfying `BoundedOrderHomClass F α β` into an actual
`BoundedOrderHom`. This is declared as the default coercion from `F` to `BoundedOrderHom α β`. -/
@[coe]
/-
**BoundedOrderHomClass.toBoundedOrderHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：BoundedOrderHomClass.toBoundedOrderHom [Preorder α] [Preorder β] [BoundedO
rder α] [BoundedOrder β] [BoundedOrderHomClass F α β] (f : F) : BoundedOrderHom 
α β
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preorder α] 
[inst_1 : Preorder β] (self : α →o β), Monotone self.toFun

--- 原说明 ---
Turn an element of a type `F` satisfying `BoundedOrderHomClass F α β` into an ac
tual
`BoundedOrderHom`. This is declared as the default coercion from `F` to `Bounded
OrderHom α β`.
-/
def BoundedOrderHomClass.toBoundedOrderHom [Preorder α] [Preorder β] [BoundedOrder α]
    [BoundedOrder β] [BoundedOrderHomClass F α β] (f : F) : BoundedOrderHom α β :=
  { (f : α →o β) with toFun := f, map_top' := map_top f, map_bot' := map_bot f }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**TopHom.** 是 Mathlib 中的一个实例，位于命名空间 `TopHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (TopHom α β) α β where
  coe := TopHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_dual]
/-
**TopHom.** 是 Mathlib 中的一个实例，位于命名空间 `TopHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopHomClass (TopHom α β) α β where
  map_top := TopHom.map_top'

-- this must come after the coe_to_fun definition
initialize_simps_projections TopHom (toFun → apply)
initialize_simps_projections BotHom (toFun → apply)

@[to_dual (attr := ext)]
/-
**TopHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：ext {f g : TopHom α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : TopHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `TopHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_dual /--
Copy of a `BotHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/]
/-
**TopHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `TopHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} → [inst : Top α] → [inst_1 : Top β] → (f
 : TopHom α β) → (f' : α → β) → f' = ⇑f → TopHom α β
参数：f : TopHom α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def copy (f : TopHom α β) (f' : α → β) (h : f' = f) :
    TopHom α β where
  toFun := f'
  map_top' := h.symm ▸ f.map_top'

@[to_dual (attr := simp)]
/-
**TopHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：coe_copy (f : TopHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f'
参数：f : TopHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : TopHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

@[to_dual]
/-
**TopHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：copy_eq (f : TopHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : TopHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : TopHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[to_dual]
/-
**TopHom.** 是 Mathlib 中的一个实例，位于命名空间 `TopHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (TopHom α β) :=
  ⟨⟨fun _ => ⊤, rfl⟩⟩

variable (α)

/-- `id` as a `TopHom`. -/
@[to_dual /-- `id` as a `BotHom`. -/]
/-
**TopHom.id** 是 Mathlib 中的一个定义，位于命名空间 `TopHom`。
形式化陈述：(α : Type u_2) → [inst : Top α] → TopHom α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as a `TopHom`.
-/
protected def id : TopHom α α :=
  ⟨id, rfl⟩

@[to_dual (attr := simp, norm_cast)]
/-
**TopHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：coe_id : ⇑(TopHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(TopHom.id α) = id :=
  rfl

variable {α}

@[to_dual (attr := simp)]
/-
**TopHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：id_apply (a : α) : TopHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : TopHom.id α a = a :=
  rfl

/-- Composition of `TopHom`s as a `TopHom`. -/
@[to_dual /-- Composition of `BotHom`s as a `BotHom`. -/]
/-
**TopHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `TopHom`。
形式化陈述：comp (f : TopHom β γ) (g : TopHom α β) : TopHom α γ where toFun
参数：f : TopHom β γ；g : TopHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `TopHom`s as a `TopHom`.
-/
def comp (f : TopHom β γ) (g : TopHom α β) :
    TopHom α γ where
  toFun := f ∘ g
  map_top' := by rw [comp_apply, map_top, map_top]

@[to_dual (attr := simp)]
/-
**TopHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：coe_comp (f : TopHom β γ) (g : TopHom α β) : (f.comp g : α -> γ) = f ∘ g
参数：f : TopHom β γ；g : TopHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : TopHom β γ) (g : TopHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[to_dual (attr := simp)]
/-
**TopHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：comp_apply (f : TopHom β γ) (g : TopHom α β) (a : α) : (f.comp g) a = f (g
 a)
参数：f : TopHom β γ；g : TopHom α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : TopHom β γ) (g : TopHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[to_dual (attr := simp)]
/-
**TopHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：comp_assoc (f : TopHom γ δ) (g : TopHom β γ) (h : TopHom α β) : (f.comp g)
.comp h = f.comp (g.comp h)
参数：f : TopHom γ δ；g : TopHom β γ；h : TopHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : TopHom γ δ) (g : TopHom β γ) (h : TopHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[to_dual (attr := simp)]
/-
**TopHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：comp_id (f : TopHom α β) : f.comp (TopHom.id α) = f
参数：f : TopHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopHom.ext`：ext {f g : TopHom α β} (h : forall a, f a = g a) : f = g
-/
theorem comp_id (f : TopHom α β) : f.comp (TopHom.id α) = f :=
  TopHom.ext fun _ => rfl

@[to_dual (attr := simp)]
/-
**TopHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：id_comp (f : TopHom α β) : (TopHom.id β).comp f = f
参数：f : TopHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopHom.ext`：ext {f g : TopHom α β} (h : forall a, f a = g a) : f = g
-/
theorem id_comp (f : TopHom α β) : (TopHom.id β).comp f = f :=
  TopHom.ext fun _ => rfl

@[to_dual (attr := simp)]
/-
**TopHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：cancel_right {g₁ g₂ : TopHom β γ} {f : TopHom α β} (hf : Surjective f) : g
₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopHom.ext`：ext {f g : TopHom α β} (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_right {g₁ g₂ : TopHom β γ} {f : TopHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => TopHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun g => comp g f)⟩

@[to_dual (attr := simp)]
/-
**TopHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：cancel_left {g : TopHom β γ} {f₁ f₂ : TopHom α β} (hg : Injective g) : g.c
omp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopHom.ext`：ext {f g : TopHom α β} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopHom.comp_apply`：comp_apply (f : TopHom β γ) (g : TopHom α β) (a : α) 
: (f.comp g) a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : TopHom β γ} {f₁ f₂ : TopHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => TopHom.ext fun a => hg <| by rw [← TopHom.comp_apply, h, TopHom.comp_apply],
    congr_arg _⟩

end Top

@[to_dual]
/-
**TopHom.instLE** 是 Mathlib 中的一个实例，位于命名空间 `TopHom`。
形式化陈述：instLE [LE β] [Top β] : LE (TopHom α β) where le f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLE [LE β] [Top β] : LE (TopHom α β) where
  le f g := (f : α → β) ≤ g

@[to_dual]
/-
**TopHom.** 是 Mathlib 中的一个实例，位于命名空间 `TopHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder β] [Top β] : Preorder (TopHom α β) :=
  Preorder.lift (DFunLike.coe : TopHom α β → α → β)

@[to_dual]
/-
**TopHom.** 是 Mathlib 中的一个实例，位于命名空间 `TopHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder β] [Top β] : PartialOrder (TopHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

section OrderTop

variable [LE β] [OrderTop β]

@[to_dual]
/-
**TopHom.** 是 Mathlib 中的一个实例，位于命名空间 `TopHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTop (TopHom α β) where
  top := ⟨⊤, rfl⟩
  le_top := fun _ => @le_top (α → β) _ _ _

@[to_dual (attr := simp)]
/-
**TopHom.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：coe_top : ⇑(⊤ : TopHom α β) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ⇑(⊤ : TopHom α β) = ⊤ :=
  rfl

@[to_dual (attr := simp)]
/-
**TopHom.top_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：top_apply (a : α) : (⊤ : TopHom α β) a = ⊤
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_apply (a : α) : (⊤ : TopHom α β) a = ⊤ :=
  rfl

end OrderTop

section SemilatticeInf

variable [SemilatticeInf β] [OrderTop β] (f g : TopHom α β)

@[to_dual]
/-
**TopHom.** 是 Mathlib 中的一个实例，位于命名空间 `TopHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (TopHom α β) :=
  ⟨fun f g => ⟨f ⊓ g, by rw [Pi.inf_apply, map_top, map_top, inf_top_eq]⟩⟩

@[to_dual]
/-
**TopHom.** 是 Mathlib 中的一个实例，位于命名空间 `TopHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeInf (TopHom α β) :=
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl

@[to_dual (attr := simp)]
/-
**TopHom.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：coe_inf : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g :=
  rfl

@[to_dual (attr := simp)]
/-
**TopHom.inf_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：inf_apply (a : α) : (f ⊓ g) a = f a ⊓ g a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_apply (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl

end SemilatticeInf

section SemilatticeSup

variable [SemilatticeSup β] [OrderTop β] (f g : TopHom α β)

@[to_dual]
/-
**TopHom.** 是 Mathlib 中的一个实例，位于命名空间 `TopHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (TopHom α β) :=
  ⟨fun f g => ⟨f ⊔ g, by rw [Pi.sup_apply, map_top, map_top, sup_top_eq]⟩⟩

@[to_dual]
/-
**TopHom.** 是 Mathlib 中的一个实例，位于命名空间 `TopHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup (TopHom α β) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ ↦ rfl

@[to_dual (attr := simp)]
/-
**TopHom.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：coe_sup : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl

@[to_dual (attr := simp)]
/-
**TopHom.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：sup_apply (a : α) : (f ⊔ g) a = f a ⊔ g a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_apply (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl

end SemilatticeSup

@[to_dual]
/-
**TopHom.** 是 Mathlib 中的一个实例，位于命名空间 `TopHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Lattice β] [OrderTop β] : Lattice (TopHom α β) :=
  DFunLike.coe_injective.lattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

@[to_dual]
/-
**TopHom.** 是 Mathlib 中的一个实例，位于命名空间 `TopHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribLattice β] [OrderTop β] : DistribLattice (TopHom α β) :=
  DFunLike.coe_injective.distribLattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

end TopHom

/-! ### Bounded order homomorphisms -/

-- TODO: remove this configuration and use the default configuration.
initialize_simps_projections BoundedOrderHom (+toOrderHom, -toFun)

namespace BoundedOrderHom

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [BoundedOrder α] [BoundedOrder β]
  [BoundedOrder γ] [BoundedOrder δ]

/-- Reinterpret a `BoundedOrderHom` as a `TopHom`. -/
@[to_dual /-- Reinterpret a `BoundedOrderHom` as a `BotHom`. -/]
/-
**BoundedOrderHom.toTopHom** 是 Mathlib 中的一个定义，位于命名空间 `BoundedOrderHom`。
形式化陈述：toTopHom (f : BoundedOrderHom α β) : TopHom α β where __
参数：f : BoundedOrderHom α β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedOrderHom.map_top'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β
] (self : Boun…

--- 原说明 ---
Reinterpret a `BoundedOrderHom` as a `TopHom`.
-/
def toTopHom (f : BoundedOrderHom α β) : TopHom α β where
  __ := f
/-
**BoundedOrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedOrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (BoundedOrderHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr
/-
**BoundedOrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedOrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedOrderHomClass (BoundedOrderHom α β) α β where
  map_rel f := @(f.monotone')
  map_top f := f.map_top'
  map_bot f := f.map_bot'

@[ext]
/-
**BoundedOrderHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：ext {f g : BoundedOrderHom α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : BoundedOrderHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `BoundedOrderHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
/-
**BoundedOrderHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `BoundedOrderHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Preorder α] →       [inst_
1 : Preorder β] →         [inst_2 : BoundedOrder α] →           [inst_3 : Bounde
dOrder β] → (f : BoundedOrderHom α β) → (f' : α → β) → f' = ⇑f → BoundedOrderHom
 α β
参数：f : BoundedOrderHom α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `BoundedOrderHom` with a new `toFun` equal to the old one. Useful to f
ix
definitional equalities.
-/
protected def copy (f : BoundedOrderHom α β) (f' : α → β) (h : f' = f) : BoundedOrderHom α β :=
  { f.toOrderHom.copy f' h, f.toTopHom.copy f' h, f.toBotHom.copy f' h with }

@[simp]
/-
**BoundedOrderHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：coe_copy (f : BoundedOrderHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f
' h) = f'
参数：f : BoundedOrderHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : BoundedOrderHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**BoundedOrderHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：copy_eq (f : BoundedOrderHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h
 = f
参数：f : BoundedOrderHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : BoundedOrderHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `BoundedOrderHom`. -/
/-
**BoundedOrderHom.id** 是 Mathlib 中的一个定义，位于命名空间 `BoundedOrderHom`。
形式化陈述：(α : Type u_2) → [inst : Preorder α] → [inst_1 : BoundedOrder α] → Bounded
OrderHom α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as a `BoundedOrderHom`.
-/
protected def id : BoundedOrderHom α α :=
  { OrderHom.id, TopHom.id α, BotHom.id α with }
/-
**BoundedOrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedOrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (BoundedOrderHom α α) :=
  ⟨BoundedOrderHom.id α⟩

@[simp, norm_cast]
/-
**BoundedOrderHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：coe_id : ⇑(BoundedOrderHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(BoundedOrderHom.id α) = id :=
  rfl

variable {α}

@[simp]
/-
**BoundedOrderHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：id_apply (a : α) : BoundedOrderHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : BoundedOrderHom.id α a = a :=
  rfl

/-- Composition of `BoundedOrderHom`s as a `BoundedOrderHom`. -/
/-
**BoundedOrderHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `BoundedOrderHom`。
形式化陈述：comp (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) : BoundedOrderHom
 α γ
参数：f : BoundedOrderHom β γ；g : BoundedOrderHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `BoundedOrderHom`s as a `BoundedOrderHom`.
-/
def comp (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) : BoundedOrderHom α γ :=
  { f.toOrderHom.comp g.toOrderHom, f.toTopHom.comp g.toTopHom, f.toBotHom.comp g.toBotHom with }

@[simp]
/-
**BoundedOrderHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：coe_comp (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) : (f.comp g :
 α -> γ) = f ∘ g
参数：f : BoundedOrderHom β γ；g : BoundedOrderHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
/-
**BoundedOrderHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：comp_apply (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) (a : α) : (
f.comp g) a = f (g a)
参数：f : BoundedOrderHom β γ；g : BoundedOrderHom α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl

@[simp]
/-
**BoundedOrderHom.coe_comp_orderHom** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：coe_comp_orderHom (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) : (f
.comp g : OrderHom α γ) = (f : OrderHom β γ).comp g
参数：f : BoundedOrderHom β γ；g : BoundedOrderHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedOrderHomClass.toRelHomClass`：∀ {F : Type u_6} {α : Type u_7} {β :
 Type u_8} {inst : LE α} {inst_1 : LE β} {inst_2 : BoundedOrder α}   {inst_3 : B
oundedOrder β} {inst_4 :…
· 使用定理 `BoundedOrderHom.instBoundedOrderHomClass`：∀ {α : Type u_2} {β : Type u_3
} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : BoundedOrder α]   [inst_3 
: BoundedOrder β], BoundedOrde…
-/
theorem coe_comp_orderHom (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) :
    (f.comp g : OrderHom α γ) = (f : OrderHom β γ).comp g :=
  rfl

@[to_dual (attr := simp)]
/-
**BoundedOrderHom.coe_comp_topHom** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：coe_comp_topHom (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) : (f.c
omp g : TopHom α γ) = (f : TopHom β γ).comp g
参数：f : BoundedOrderHom β γ；g : BoundedOrderHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedOrderHomClass.toTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β :
 Type u_3} [inst : FunLike F α β] [inst_1 : LE α] [inst_2 : LE β]   [inst_3 : Bo
undedOrder α] [inst_4 : …
· 使用定理 `BoundedOrderHom.instBoundedOrderHomClass`：∀ {α : Type u_2} {β : Type u_3
} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : BoundedOrder α]   [inst_3 
: BoundedOrder β], BoundedOrde…
-/
theorem coe_comp_topHom (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) :
    (f.comp g : TopHom α γ) = (f : TopHom β γ).comp g :=
  rfl

@[simp]
/-
**BoundedOrderHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：comp_assoc (f : BoundedOrderHom γ δ) (g : BoundedOrderHom β γ) (h : Bounde
dOrderHom α β) : (f.comp g).comp h = f.comp (g.comp h)
参数：f : BoundedOrderHom γ δ；g : BoundedOrderHom β γ；h : BoundedOrderHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : BoundedOrderHom γ δ) (g : BoundedOrderHom β γ) (h : BoundedOrderHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**BoundedOrderHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：comp_id (f : BoundedOrderHom α β) : f.comp (BoundedOrderHom.id α) = f
参数：f : BoundedOrderHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedOrderHom.ext`：ext {f g : BoundedOrderHom α β} (h : forall a, f a 
= g a) : f = g
-/
theorem comp_id (f : BoundedOrderHom α β) : f.comp (BoundedOrderHom.id α) = f :=
  BoundedOrderHom.ext fun _ => rfl

@[simp]
/-
**BoundedOrderHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：id_comp (f : BoundedOrderHom α β) : (BoundedOrderHom.id β).comp f = f
参数：f : BoundedOrderHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedOrderHom.ext`：ext {f g : BoundedOrderHom α β} (h : forall a, f a 
= g a) : f = g
-/
theorem id_comp (f : BoundedOrderHom α β) : (BoundedOrderHom.id β).comp f = f :=
  BoundedOrderHom.ext fun _ => rfl

@[simp]
/-
**BoundedOrderHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：cancel_right {g₁ g₂ : BoundedOrderHom β γ} {f : BoundedOrderHom α β} (hf :
 Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedOrderHom.ext`：ext {f g : BoundedOrderHom α β} (h : forall a, f a 
= g a) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_right {g₁ g₂ : BoundedOrderHom β γ} {f : BoundedOrderHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => BoundedOrderHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h,
   congr_arg (fun g => comp g f)⟩

@[simp]
/-
**BoundedOrderHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：cancel_left {g : BoundedOrderHom β γ} {f₁ f₂ : BoundedOrderHom α β} (hg : 
Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedOrderHom.ext`：ext {f g : BoundedOrderHom α β} (h : forall a, f a 
= g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoundedOrderHom.comp_apply`：comp_apply (f : BoundedOrderHom β γ) (g : Bo
undedOrderHom α β) (a : α) : (f.comp g) a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : BoundedOrderHom β γ} {f₁ f₂ : BoundedOrderHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    BoundedOrderHom.ext fun a =>
      hg <| by rw [← BoundedOrderHom.comp_apply, h, BoundedOrderHom.comp_apply],
    congr_arg _⟩

end BoundedOrderHom

/-! ### Dual homs -/


namespace TopHom

variable [LE α] [OrderTop α] [LE β] [OrderTop β] [LE γ] [OrderTop γ]

/-- Reinterpret a top homomorphism as a bot homomorphism between the dual lattices. -/
@[to_dual (attr := simps) /--
Reinterpret a bot homomorphism as a top homomorphism between the dual lattices. -/]
/-
**TopHom.dual** 是 Mathlib 中的一个定义，位于命名空间 `TopHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : LE α] → [inst_1 : OrderTop
 α] → [inst_2 : LE β] → [inst_3 : OrderTop β] → TopHom α β ≃ BotHom αᵒᵈ βᵒᵈ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def dual :
    TopHom α β ≃ BotHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨f, f.map_top'⟩
  invFun f := ⟨f, f.map_bot'⟩

@[to_dual (attr := simp)]
/-
**TopHom.dual_id** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：dual_id : TopHom.dual (TopHom.id α) = BotHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_id : TopHom.dual (TopHom.id α) = BotHom.id _ :=
  rfl

@[to_dual (attr := simp)]
/-
**TopHom.dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：dual_comp (g : TopHom β γ) (f : TopHom α β) : TopHom.dual (g.comp f) = g.d
ual.comp (TopHom.dual f)
参数：g : TopHom β γ；f : TopHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_comp (g : TopHom β γ) (f : TopHom α β) :
    TopHom.dual (g.comp f) = g.dual.comp (TopHom.dual f) :=
  rfl

@[to_dual (attr := simp)]
/-
**TopHom.symm_dual_id** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：symm_dual_id : TopHom.dual.symm (BotHom.id _) = TopHom.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_id : TopHom.dual.symm (BotHom.id _) = TopHom.id α :=
  rfl

@[to_dual (attr := simp)]
/-
**TopHom.symm_dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `TopHom`。
形式化陈述：symm_dual_comp (g : BotHom βᵒᵈ γᵒᵈ) (f : BotHom αᵒᵈ βᵒᵈ) : TopHom.dual.sym
m (g.comp f) = (TopHom.dual.symm g).comp (TopHom.dual.symm f)
参数：g : BotHom βᵒᵈ γᵒᵈ；f : BotHom αᵒᵈ βᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
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
/-
**BoundedOrderHom.dual** 是 Mathlib 中的一个定义，位于命名空间 `BoundedOrderHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Preorder α] →       [inst_
1 : BoundedOrder α] →         [inst_2 : Preorder β] → [inst_3 : BoundedOrder β] 
→ BoundedOrderHom α β ≃ BoundedOrderHom αᵒᵈ βᵒᵈ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedOrderHom.map_bot'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β
] (self : Boun…
· 使用定理 `BoundedOrderHom.map_top'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β
] (self : Boun…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reinterpret a bounded order homomorphism as a bounded order homomorphism between
 the dual
orders.
-/
protected def dual :
    BoundedOrderHom α β ≃
      BoundedOrderHom αᵒᵈ
        βᵒᵈ where
  toFun f := ⟨f.toOrderHom.dual, f.map_bot', f.map_top'⟩
  invFun f := ⟨OrderHom.dual.symm f.toOrderHom, f.map_bot', f.map_top'⟩

@[simp]
/-
**BoundedOrderHom.dual_id** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：dual_id : (BoundedOrderHom.id α).dual = BoundedOrderHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_id : (BoundedOrderHom.id α).dual = BoundedOrderHom.id _ :=
  rfl

@[simp]
/-
**BoundedOrderHom.dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：dual_comp (g : BoundedOrderHom β γ) (f : BoundedOrderHom α β) : (g.comp f)
.dual = g.dual.comp f.dual
参数：g : BoundedOrderHom β γ；f : BoundedOrderHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_comp (g : BoundedOrderHom β γ) (f : BoundedOrderHom α β) :
    (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
/-
**BoundedOrderHom.symm_dual_id** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：symm_dual_id : BoundedOrderHom.dual.symm (BoundedOrderHom.id _) = BoundedO
rderHom.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_id : BoundedOrderHom.dual.symm (BoundedOrderHom.id _) = BoundedOrderHom.id α :=
  rfl

@[simp]
/-
**BoundedOrderHom.symm_dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `BoundedOrderHom`。
形式化陈述：symm_dual_comp (g : BoundedOrderHom βᵒᵈ γᵒᵈ) (f : BoundedOrderHom αᵒᵈ βᵒᵈ)
 : BoundedOrderHom.dual.symm (g.comp f) = (BoundedOrderHom.dual.symm g).comp (Bo
undedOrderHom.dual.symm f)
参数：g : BoundedOrderHom βᵒᵈ γᵒᵈ；f : BoundedOrderHom αᵒᵈ βᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_comp (g : BoundedOrderHom βᵒᵈ γᵒᵈ) (f : BoundedOrderHom αᵒᵈ βᵒᵈ) :
    BoundedOrderHom.dual.symm (g.comp f) =
      (BoundedOrderHom.dual.symm g).comp (BoundedOrderHom.dual.symm f) :=
  rfl

end BoundedOrderHom

