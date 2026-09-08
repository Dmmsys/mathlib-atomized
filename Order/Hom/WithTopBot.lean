/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.WithBot

/-!
# Adjoining `⊤` and `⊥` to order maps and lattice homomorphisms

This file defines ways to adjoin `⊤` or `⊥` or both to order maps (homomorphisms, embeddings and
isomorphisms) and lattice homomorphisms, and properties about the results.

Some definitions cause a possibly unbounded lattice homomorphism to become bounded,
so they change the type of the homomorphism.
-/

@[expose] public section


variable {α β γ : Type*}

namespace WithTop

open OrderDual

/-- Taking the dual then adding `⊤` is the same as adding `⊥` then taking the dual.
This is the order iso form of `WithTop.ofDual`, as proven by `coe_toDualBotEquiv`. -/
@[to_dual
/-- Taking the dual then adding `⊥` is the same as adding `⊤` then taking the dual.
This is the order iso form of `WithBot.ofDual`, as proven by `coe_toDualTopEquiv`. -/]
/-
**WithTop.toDualBotEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → [inst : LE α] → WithTop αᵒᵈ ≃o (WithBot α)ᵒᵈ
参数：WithBot α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def toDualBotEquiv [LE α] : WithTop αᵒᵈ ≃o (WithBot α)ᵒᵈ :=
  OrderIso.refl _

@[to_dual (attr := simp)]
/-
**WithTop.toDualBotEquiv_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：toDualBotEquiv_coe [LE α] (a : α) : WithTop.toDualBotEquiv ↑(toDual a) = t
oDual (a : WithBot α)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDualBotEquiv_coe [LE α] (a : α) :
    WithTop.toDualBotEquiv ↑(toDual a) = toDual (a : WithBot α) :=
  rfl

@[to_dual (attr := simp)]
/-
**WithTop.toDualBotEquiv_symm_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：toDualBotEquiv_symm_coe [LE α] (a : α) : WithTop.toDualBotEquiv.symm (toDu
al (a : WithBot α)) = ↑(toDual a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDualBotEquiv_symm_coe [LE α] (a : α) :
    WithTop.toDualBotEquiv.symm (toDual (a : WithBot α)) = ↑(toDual a) :=
  rfl

@[to_dual (attr := simp)]
/-
**WithTop.toDualBotEquiv_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：toDualBotEquiv_top [LE α] : WithTop.toDualBotEquiv (⊤ : WithTop αᵒᵈ) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDualBotEquiv_top [LE α] : WithTop.toDualBotEquiv (⊤ : WithTop αᵒᵈ) = ⊤ :=
  rfl

@[to_dual (attr := simp)]
/-
**WithTop.toDualBotEquiv_symm_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：toDualBotEquiv_symm_top [LE α] : WithTop.toDualBotEquiv.symm (⊤ : (WithBot
 α)ᵒᵈ) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDualBotEquiv_symm_top [LE α] : WithTop.toDualBotEquiv.symm (⊤ : (WithBot α)ᵒᵈ) = ⊤ :=
  rfl

@[to_dual]
/-
**WithTop.coe_toDualBotEquiv** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：coe_toDualBotEquiv [LE α] : (WithTop.toDualBotEquiv : WithTop αᵒᵈ -> (With
Bot α)ᵒᵈ) = toDual ∘ WithTop.ofDual
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem coe_toDualBotEquiv [LE α] :
    (WithTop.toDualBotEquiv : WithTop αᵒᵈ → (WithBot α)ᵒᵈ) = toDual ∘ WithTop.ofDual :=
  funext fun _ => rfl

@[deprecated (since := "2026-03-27")]
alias _root_.WithBot.coe_toDualTopEquiv_eq := WithBot.coe_toDualTopEquiv

/-- Embedding into `WithTop α`. -/
@[to_dual (attr := simps) /-- Embedding into `WithBot α`. -/]
/-
**WithTop._root_.Function.Embedding.coeWithTop** 是 Mathlib 中的一个定义，位于命名空间 `WithTo
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding into `WithTop α`.
-/
def _root_.Function.Embedding.coeWithTop : α ↪ WithTop α where
  toFun := (↑)
  inj' := WithTop.coe_injective

/-- The coercion `α → WithTop α` bundled as monotone map. -/
@[to_dual
/-- The coercion `α → WithBot α` bundled as monotone map. -/]
/-
**WithTop.coeOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：coeOrderHom {α : Type*} [Preorder α] : α ↪o WithTop α where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_injective`：∀ {α : Type u_1}, Function.Injective WithTop.some
-/
def coeOrderHom {α : Type*} [Preorder α] : α ↪o WithTop α where
  toFun := (↑)
  inj' := WithTop.coe_injective
  map_rel_iff' := WithTop.coe_le_coe

-- `simps` could generate this theorem, but `to_dual` is not happy with that version.
@[to_dual (attr := simp)]
/-
**WithTop.coeOrderHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：coeOrderHom_apply {α : Type*} [Preorder α] : (coeOrderHom : α -> WithTop α
) = some
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeOrderHom_apply {α : Type*} [Preorder α] : (coeOrderHom : α → WithTop α) = some := rfl

/-- Any `OrderTop` is equivalent to `WithTop` of the subtype excluding `⊤`.

See also `Equiv.optionSubtypeNe`. -/
@[to_dual
/-- Any `OrderBot` is equivalent to `WithBot` of the subtype excluding `⊥`.

See also `Equiv.optionSubtypeNe`. -/]
/-
**WithTop.subtypeOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：subtypeOrderIso [PartialOrder α] [OrderTop α] [DecidablePred (· = (⊤ : α))
] : WithTop {a : α // a != ⊤} ≃o α where toFun a
参数：· = (⊤ : α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def subtypeOrderIso [PartialOrder α] [OrderTop α] [DecidablePred (· = (⊤ : α))] :
    WithTop {a : α // a ≠ ⊤} ≃o α where
  toFun a := (a.map (↑)).untopD ⊤
  invFun a := if h : a = ⊤ then ⊤ else .some ⟨a, h⟩
  left_inv
  | .some ⟨a, h⟩ => by simp [h]
  | ⊤ => by simp
  right_inv a := by dsimp only; split_ifs <;> simp [*]
  map_rel_iff' {a b} := match a, b with
  | .some a, .some b => by simp
  | ⊤, .some ⟨b, h⟩ => by simp [h]
  | a, ⊤ => by simp

@[to_dual (attr := simp)]
/-
**WithTop.subtypeOrderIso_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：subtypeOrderIso_apply_coe [PartialOrder α] [OrderTop α] [DecidablePred (· 
= (⊤ : α))] (a : {a : α // a != ⊤}) : subtypeOrderIso (a : WithTop {a : α // a !
= ⊤}) = a
参数：· = (⊤ : α)；a : {a : α // a != ⊤}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeOrderIso_apply_coe [PartialOrder α] [OrderTop α] [DecidablePred (· = (⊤ : α))]
    (a : {a : α // a ≠ ⊤}) :
  subtypeOrderIso (a : WithTop {a : α // a ≠ ⊤}) = a := rfl

@[to_dual]
/-
**WithTop.subtypeOrderIso_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：subtypeOrderIso_symm_apply [PartialOrder α] [OrderTop α] [DecidablePred (·
 = (⊤ : α))] {a : α} (h : a != ⊤) : subtypeOrderIso.symm a = (⟨a, h⟩ : {a : α //
 a != ⊤})
参数：· = (⊤ : α)；h : a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.symm_apply_eq`：symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.s
ymm y = x ↔ y = e x
-/
theorem subtypeOrderIso_symm_apply [PartialOrder α] [OrderTop α] [DecidablePred (· = (⊤ : α))]
    {a : α} (h : a ≠ ⊤) :
    subtypeOrderIso.symm a = (⟨a, h⟩ : {a : α // a ≠ ⊤}) := by
  rw [OrderIso.symm_apply_eq]
  rfl

end WithTop

namespace OrderHom

variable [Preorder α] [Preorder β]

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `WithBot α →o WithBot β`. -/
@[to_dual (attr := simps -fullyApplied)
/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `WithTop α →o WithTop β`. -/]
/-
**OrderHom.withBotMap** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [inst : Preorder α] → [inst_1 : Preorder
 β] → (α →o β) → WithBot α →o WithBot β
参数：α →o β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def withBotMap (f : α →o β) : WithBot α →o WithBot β :=
  ⟨WithBot.map f, f.mono.withBot_map⟩

end OrderHom

namespace OrderEmbedding

variable [Preorder α] [Preorder β]

/-- A version of `WithBot.map` for order embeddings. -/
@[to_dual /-- A version of `WithTop.map` for order embeddings. -/]
/-
**OrderEmbedding.withBotMap** 是 Mathlib 中的一个定义，位于命名空间 `OrderEmbedding`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [inst : Preorder α] → [inst_1 : Preorder
 β] → α ↪o β → WithBot α ↪o WithBot β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `WithBot.map` for order embeddings.
-/
protected def withBotMap (f : α ↪o β) : WithBot α ↪o WithBot β where
  toFun := WithBot.map f
  inj' := WithBot.map_injective f.injective
  map_rel_iff' := WithBot.map_le_iff f f.map_rel_iff

-- `simps` could generate this theorem, but `to_dual` is not happy with that version.
@[to_dual (attr := simp)]
/-
**OrderEmbedding.withBotMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：withBotMap_apply (f : α ↪o β) : ⇑f.withBotMap = WithBot.map f
参数：f : α ↪o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem withBotMap_apply (f : α ↪o β) : ⇑f.withBotMap = WithBot.map f := rfl

end OrderEmbedding

namespace OrderIso

variable [PartialOrder α] [PartialOrder β] [PartialOrder γ]

/-- A version of `Equiv.optionCongr` for `WithTop`. -/
@[to_dual /-- A version of `Equiv.optionCongr` for `WithBot`. -/]
/-
**OrderIso.withTopCongr** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：withTopCongr (e : α ≃o β) : WithTop α ≃o WithTop β where toFun
参数：e : α ≃o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Equiv.optionCongr` for `WithTop`.
-/
def withTopCongr (e : α ≃o β) : WithTop α ≃o WithTop β where
  toFun := WithTop.map e
  __ := e.toOrderEmbedding.withTopMap
  __ := e.toEquiv.withTopCongr

-- `simps` could generate this theorem, but `to_dual` is not happy with that version.
@[to_dual (attr := simp)]
/-
**OrderIso.withTopCongr_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：withTopCongr_apply (e : α ≃o β) : ⇑e.withTopCongr = WithTop.map e
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem withTopCongr_apply (e : α ≃o β) : ⇑e.withTopCongr = WithTop.map e := rfl

@[simp]
/-
**OrderIso.withTopCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：withTopCongr_refl : (OrderIso.refl α).withTopCongr = OrderIso.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.toEquiv_injective`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop}, Function.Injective RelIso.toEquiv
· 使用定理 `Equiv.withTopCongr_refl`：∀ {α : Type u_1}, (Equiv.refl α).withTopCongr =
 Equiv.refl (WithTop α)
-/
theorem withTopCongr_refl : (OrderIso.refl α).withTopCongr = OrderIso.refl _ :=
  RelIso.toEquiv_injective Equiv.withTopCongr_refl

@[simp]
/-
**OrderIso.withTopCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：withTopCongr_symm (e : α ≃o β) : e.symm.withTopCongr = e.withTopCongr.symm
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.toEquiv_injective`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop}, Function.Injective RelIso.toEquiv
· 使用定理 `Equiv.withTopCongr_symm`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β), e.
symm.withTopCongr = e.withTopCongr.symm
-/
theorem withTopCongr_symm (e : α ≃o β) : e.symm.withTopCongr = e.withTopCongr.symm :=
  RelIso.toEquiv_injective e.toEquiv.withTopCongr_symm

@[simp]
/-
**OrderIso.withTopCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：withTopCongr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) : (e₁.trans e₂).withTopCong
r = e₁.withTopCongr.trans e₂.withTopCongr
参数：e₁ : α ≃o β；e₂ : β ≃o γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.toEquiv_injective`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop}, Function.Injective RelIso.toEquiv
· 使用定理 `Equiv.withTopCongr_trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3}
 (e₁ : α ≃ β) (e₂ : β ≃ γ),   (e₁.trans e₂).withTopCongr = e₁.withTopCongr.trans
 e₂.withTopCon…
-/
theorem withTopCongr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) :
    (e₁.trans e₂).withTopCongr = e₁.withTopCongr.trans e₂.withTopCongr :=
  RelIso.toEquiv_injective <| e₁.toEquiv.withTopCongr_trans e₂.toEquiv

@[to_dual existing, simp]
/-
**OrderIso.withBotCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：withBotCongr_refl : (OrderIso.refl α).withBotCongr = OrderIso.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.toEquiv_injective`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop}, Function.Injective RelIso.toEquiv
· 使用定理 `Equiv.withBotCongr_refl`：withBotCongr_refl : withBotCongr (Equiv.refl α)
 = Equiv.refl _
-/
theorem withBotCongr_refl : (OrderIso.refl α).withBotCongr = OrderIso.refl _ :=
  RelIso.toEquiv_injective Equiv.withBotCongr_refl

@[to_dual existing, simp]
/-
**OrderIso.withBotCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：withBotCongr_symm (e : α ≃o β) : e.symm.withBotCongr = e.withBotCongr.symm
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.toEquiv_injective`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop}, Function.Injective RelIso.toEquiv
· 使用定理 `Equiv.withBotCongr_symm`：withBotCongr_symm (e : α ≃ β) : withBotCongr e.
symm = (withBotCongr e).symm
-/
theorem withBotCongr_symm (e : α ≃o β) : e.symm.withBotCongr = e.withBotCongr.symm :=
  RelIso.toEquiv_injective e.toEquiv.withBotCongr_symm

@[to_dual existing, simp]
/-
**OrderIso.withBotCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：withBotCongr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) : (e₁.trans e₂).withBotCong
r = e₁.withBotCongr.trans e₂.withBotCongr
参数：e₁ : α ≃o β；e₂ : β ≃o γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.toEquiv_injective`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop}, Function.Injective RelIso.toEquiv
· 使用定理 `Equiv.withBotCongr_trans`：withBotCongr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
 withBotCongr (e₁.trans e₂) = (withBotCongr e₁).trans (withBotCongr e₂)
-/
theorem withBotCongr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) :
    (e₁.trans e₂).withBotCongr = e₁.withBotCongr.trans e₂.withBotCongr :=
  RelIso.toEquiv_injective <| e₁.toEquiv.withBotCongr_trans e₂.toEquiv

end OrderIso

namespace SupHom

variable [SemilatticeSup α] [SemilatticeSup β] [SemilatticeSup γ]

/-- Adjoins a `⊤` to the domain and codomain of a `SupHom`. -/
@[to_dual (attr := simps) /-- Adjoins a `⊥` to the domain and codomain of an `InfHom`. -/]
/-
**SupHom.withTop** 是 Mathlib 中的一个定义，位于命名空间 `SupHom`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → [inst : SemilatticeSup α] → [inst_1 : 
SemilatticeSup β] → SupHom α β → SupHom (WithTop α) (WithTop β)
参数：WithTop α；WithTop β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adjoins a `⊤` to the domain and codomain of a `SupHom`.
-/
protected def withTop (f : SupHom α β) : SupHom (WithTop α) (WithTop β) where
  toFun := WithTop.map f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => rfl
    | ⊤, (b : α) => rfl
    | (a : α), ⊤ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)

@[to_dual (attr := simp)]
/-
**SupHom.withTop_id** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：withTop_id : (SupHom.id α).withTop = SupHom.id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `WithTop.map_id`：∀ {α : Type u_1}, WithTop.map id = id
-/
theorem withTop_id : (SupHom.id α).withTop = SupHom.id _ := DFunLike.coe_injective WithTop.map_id

@[to_dual (attr := simp)]
/-
**SupHom.withTop_comp** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：withTop_comp (f : SupHom β γ) (g : SupHom α β) : (f.comp g).withTop = f.wi
thTop.comp g.withTop
参数：f : SupHom β γ；g : SupHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.map_comp_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f 
: α → β) (g : β → γ),   WithTop.map g ∘ WithTop.map f = WithTop.map (g ∘ f)
-/
theorem withTop_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
  DFunLike.coe_injective <| Eq.symm <| WithTop.map_comp_map _ _

/-- Adjoins a `⊥` to the domain and codomain of a `SupHom`. -/
@[to_dual (attr := simps) /-- Adjoins a `⊤` to the domain and codomain of an `InfHom`. -/]
/-
**SupHom.withBot** 是 Mathlib 中的一个定义，位于命名空间 `SupHom`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : SemilatticeSup α] → [inst_
1 : SemilatticeSup β] → SupHom α β → SupBotHom (WithBot α) (WithBot β)
参数：WithBot α；WithBot β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adjoins a `⊥` to the domain and codomain of a `SupHom`.
-/
protected def withBot (f : SupHom α β) : SupBotHom (WithBot α) (WithBot β) where
  toFun := WithBot.map f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => rfl
    | ⊥, (b : α) => rfl
    | (a : α), ⊥ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)
  map_bot' := rfl

@[to_dual (attr := simp)]
/-
**SupHom.withBot_id** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：withBot_id : (SupHom.id α).withBot = SupBotHom.id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `WithBot.map_id`：map_id : map (id : α -> α) = id
-/
theorem withBot_id : (SupHom.id α).withBot = SupBotHom.id _ := DFunLike.coe_injective WithBot.map_id

@[to_dual (attr := simp)]
/-
**SupHom.withBot_comp** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：withBot_comp (f : SupHom β γ) (g : SupHom α β) : (f.comp g).withBot = f.wi
thBot.comp g.withBot
参数：f : SupHom β γ；g : SupHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.map_comp_map`：map_comp_map (f : α -> β) (g : β -> γ) : WithBot.m
ap g ∘ WithBot.map f = WithBot.map (g ∘ f)
-/
theorem withBot_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).withBot = f.withBot.comp g.withBot :=
  DFunLike.coe_injective <| Eq.symm <| WithBot.map_comp_map _ _

/-- Adjoins a `⊤` to the domain of a `SupHom`. -/
@[to_dual (attr := simps) /-- Adjoins a `⊥` to the domain of an `InfHom`. -/]
/-
**SupHom.withTop'** 是 Mathlib 中的一个定义，位于命名空间 `SupHom`。
形式化陈述：withTop' [OrderTop β] (f : SupHom α β) : SupHom (WithTop α) β where toFun 
a
参数：f : SupHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adjoins a `⊤` to the domain of a `SupHom`.
-/
def withTop' [OrderTop β] (f : SupHom α β) : SupHom (WithTop α) β where
  toFun a := a.elim ⊤ f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => (top_sup_eq _).symm
    | ⊤, (b : α) => (top_sup_eq _).symm
    | (a : α), ⊤ => (sup_top_eq _).symm
    | (a : α), (b : α) => f.map_sup' _ _

/-- Adjoins a `⊥` to the domain of a `SupHom`. -/
@[to_dual (attr := simps) /-- Adjoins a `⊤` to the domain of an `InfHom`. -/]
/-
**SupHom.withBot'** 是 Mathlib 中的一个定义，位于命名空间 `SupHom`。
形式化陈述：withBot' [OrderBot β] (f : SupHom α β) : SupBotHom (WithBot α) β where toF
un a
参数：f : SupHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adjoins a `⊥` to the domain of a `SupHom`.
-/
def withBot' [OrderBot β] (f : SupHom α β) : SupBotHom (WithBot α) β where
  toFun a := a.elim ⊥ f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => (bot_sup_eq _).symm
    | ⊥, (b : α) => (bot_sup_eq _).symm
    | (a : α), ⊥ => (sup_bot_eq _).symm
    | (a : α), (b : α) => f.map_sup' _ _
  map_bot' := rfl

end SupHom

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ]

/-- Adjoins a `⊤` to the domain and codomain of a `LatticeHom`. -/
/-
**LatticeHom.withTop** 是 Mathlib 中的一个定义，位于命名空间 `LatticeHom`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → [inst : Lattice α] → [inst_1 : Lattice
 β] → LatticeHom α β → LatticeHom (WithTop α) (WithTop β)
参数：WithTop α；WithTop β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adjoins a `⊤` to the domain and codomain of a `LatticeHom`.
-/
protected def withTop (f : LatticeHom α β) : LatticeHom (WithTop α) (WithTop β) :=
  { f.toInfHom.withTop with toSupHom := f.toSupHom.withTop }

/-- Adjoins a `⊥` to the domain and codomain of a `LatticeHom`. -/
@[to_dual existing]
/-
**LatticeHom.withBot** 是 Mathlib 中的一个定义，位于命名空间 `LatticeHom`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → [inst : Lattice α] → [inst_1 : Lattice
 β] → LatticeHom α β → LatticeHom (WithBot α) (WithBot β)
参数：WithBot α；WithBot β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adjoins a `⊥` to the domain and codomain of a `LatticeHom`.
-/
protected def withBot (f : LatticeHom α β) : LatticeHom (WithBot α) (WithBot β) :=
  { f.toInfHom.withBot with toSupHom := f.toSupHom.withBot }

-- Porting note: `simps` doesn't generate those
@[to_dual (attr := simp, norm_cast)]
/-
**LatticeHom.coe_withTop** 是 Mathlib 中的一个引理，位于命名空间 `LatticeHom`。
形式化陈述：coe_withTop (f : LatticeHom α β) : ⇑f.withTop = WithTop.map f
参数：f : LatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_withTop (f : LatticeHom α β) : ⇑f.withTop = WithTop.map f := rfl

@[to_dual (attr := simp)]
/-
**LatticeHom.withTop_apply** 是 Mathlib 中的一个引理，位于命名空间 `LatticeHom`。
形式化陈述：withTop_apply (f : LatticeHom α β) (a : WithTop α) : f.withTop a = a.map f
参数：f : LatticeHom α β；a : WithTop α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma withTop_apply (f : LatticeHom α β) (a : WithTop α) : f.withTop a = a.map f := rfl

@[to_dual (attr := simp)]
/-
**LatticeHom.withTop_id** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：withTop_id : (LatticeHom.id α).withTop = LatticeHom.id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `WithTop.map_id`：∀ {α : Type u_1}, WithTop.map id = id
-/
theorem withTop_id : (LatticeHom.id α).withTop = LatticeHom.id _ :=
  DFunLike.coe_injective WithTop.map_id

@[to_dual (attr := simp)]
/-
**LatticeHom.withTop_comp** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：withTop_comp (f : LatticeHom β γ) (g : LatticeHom α β) : (f.comp g).withTo
p = f.withTop.comp g.withTop
参数：f : LatticeHom β γ；g : LatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.map_comp_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f 
: α → β) (g : β → γ),   WithTop.map g ∘ WithTop.map f = WithTop.map (g ∘ f)
-/
theorem withTop_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
  DFunLike.coe_injective <| Eq.symm <| WithTop.map_comp_map _ _

/-- Adjoins a `⊤` and `⊥` to the domain and codomain of a `LatticeHom`. -/
@[to_dual /-- Adjoins a `⊥` and `⊤` to the domain and codomain of a `LatticeHom`. -/]
/-
**LatticeHom.withTopWithBot** 是 Mathlib 中的一个定义，位于命名空间 `LatticeHom`。
形式化陈述：withTopWithBot (f : LatticeHom α β) : BoundedLatticeHom (WithTop <| WithBo
t α) (WithTop <| WithBot β)
参数：f : LatticeHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adjoins a `⊤` and `⊥` to the domain and codomain of a `LatticeHom`.
-/
def withTopWithBot (f : LatticeHom α β) :
    BoundedLatticeHom (WithTop <| WithBot α) (WithTop <| WithBot β) :=
  ⟨f.withBot.withTop, rfl, rfl⟩

-- Porting note: `simps` doesn't generate those
@[to_dual (attr := simp, norm_cast)]
/-
**LatticeHom.coe_withTopWithBot** 是 Mathlib 中的一个引理，位于命名空间 `LatticeHom`。
形式化陈述：coe_withTopWithBot (f : LatticeHom α β) : ⇑f.withTopWithBot = WithTop.map 
(WithBot.map f)
参数：f : LatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_withTopWithBot (f : LatticeHom α β) :
    ⇑f.withTopWithBot = WithTop.map (WithBot.map f) :=
  rfl

@[to_dual (attr := simp)]
/-
**LatticeHom.withTopWithBot_apply** 是 Mathlib 中的一个引理，位于命名空间 `LatticeHom`。
形式化陈述：withTopWithBot_apply (f : LatticeHom α β) (a : WithTop <| WithBot α) : f.w
ithTopWithBot a = a.map (WithBot.map f)
参数：f : LatticeHom α β；a : WithTop <| WithBot α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma withTopWithBot_apply (f : LatticeHom α β) (a : WithTop <| WithBot α) :
    f.withTopWithBot a = a.map (WithBot.map f) :=
  rfl

@[to_dual (attr := simp)]
/-
**LatticeHom.withTopWithBot_id** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：withTopWithBot_id : (LatticeHom.id α).withTopWithBot = BoundedLatticeHom.i
d _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.map_id`：map_id : map (id : α -> α) = id
· 使用定理 `WithTop.map_id`：∀ {α : Type u_1}, WithTop.map id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem withTopWithBot_id : (LatticeHom.id α).withTopWithBot = BoundedLatticeHom.id _ :=
  DFunLike.coe_injective <| by simp [WithTop.map_id, WithBot.map_id]

@[to_dual (attr := simp)]
/-
**LatticeHom.withTopWithBot_comp** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：withTopWithBot_comp (f : LatticeHom β γ) (g : LatticeHom α β) : (f.comp g)
.withTopWithBot = f.withTopWithBot.comp g.withTopWithBot
参数：f : LatticeHom β γ；g : LatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedLatticeHom.ext`：ext {f g : BoundedLatticeHom α β} (h : forall a, 
f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.map_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (h : β →
 γ) (g : α → β) (a : WithTop α),   WithTop.map h (WithTop.map g a) = WithTop.map
 (h ∘…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithBot.map_comp_map`：map_comp_map (f : α -> β) (g : β -> γ) : WithBot.m
ap g ∘ WithBot.map f = WithBot.map (g ∘ f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem withTopWithBot_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withTopWithBot = f.withTopWithBot.comp g.withTopWithBot := by
  ext; simp

/-- Adjoins a `⊤` to the domain of a `LatticeHom`. -/
/-
**LatticeHom.withTop'** 是 Mathlib 中的一个定义，位于命名空间 `LatticeHom`。
形式化陈述：withTop' [OrderTop β] (f : LatticeHom α β) : LatticeHom (WithTop α) β
参数：f : LatticeHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adjoins a `⊤` to the domain of a `LatticeHom`.
-/
def withTop' [OrderTop β] (f : LatticeHom α β) : LatticeHom (WithTop α) β :=
  { f.toSupHom.withTop', f.toInfHom.withTop' with }

/-- Adjoins a `⊥` to the domain of a `LatticeHom`. -/
@[to_dual existing (attr := simps!)]
/-
**LatticeHom.withBot'** 是 Mathlib 中的一个定义，位于命名空间 `LatticeHom`。
形式化陈述：withBot' [OrderBot β] (f : LatticeHom α β) : LatticeHom (WithBot α) β
参数：f : LatticeHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adjoins a `⊥` to the domain of a `LatticeHom`.
-/
def withBot' [OrderBot β] (f : LatticeHom α β) : LatticeHom (WithBot α) β :=
  { f.toSupHom.withBot', f.toInfHom.withBot' with }

/-- Adjoins a `⊤` and `⊥` to the domain of a `LatticeHom`. -/
@[to_dual (attr := simps!) /-- Adjoins a `⊥` and `⊤` to the domain of a `LatticeHom`. -/]
/-
**LatticeHom.withTopWithBot'** 是 Mathlib 中的一个定义，位于命名空间 `LatticeHom`。
形式化陈述：withTopWithBot' [BoundedOrder β] (f : LatticeHom α β) : BoundedLatticeHom 
(WithTop <| WithBot α) β where toLatticeHom
参数：f : LatticeHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adjoins a `⊤` and `⊥` to the domain of a `LatticeHom`.
-/
def withTopWithBot' [BoundedOrder β] (f : LatticeHom α β) :
    BoundedLatticeHom (WithTop <| WithBot α) β where
  toLatticeHom := f.withBot'.withTop'
  map_top' := rfl
  map_bot' := rfl

end LatticeHom

