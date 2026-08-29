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
/--
Definition of `toDualBotEquiv` / `toDualBotEquiv` 的定义

English:
definition toDualBotEquiv
  signature: [LE α]
  body: OrderIso.refl _

@[to_dual (attr := simp)]

中文:
定义 toDualBotEquiv
  签名: [LE α]
  定义体: OrderIso.refl _

@[to_dual (attr := simp)]
-/
protected def toDualBotEquiv [LE α] : WithTop αᵒᵈ ≃o (WithBot α)ᵒᵈ :=
  OrderIso.refl _

@[to_dual (attr := simp)]
/--
theorem `toDualBotEquiv_coe` / 定理 `toDualBotEquiv_coe`

English:
theorem toDualBotEquiv_coe
  given: [LE α] (a : α)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 toDualBotEquiv_coe
  条件: [LE α] (a : α)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem toDualBotEquiv_coe [LE α] (a : α) :
    WithTop.toDualBotEquiv ↑(toDual a) = toDual (a : WithBot α) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `toDualBotEquiv_symm_coe` / 定理 `toDualBotEquiv_symm_coe`

English:
theorem toDualBotEquiv_symm_coe
  given: [LE α] (a : α)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 toDualBotEquiv_symm_coe
  条件: [LE α] (a : α)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem toDualBotEquiv_symm_coe [LE α] (a : α) :
    WithTop.toDualBotEquiv.symm (toDual (a : WithBot α)) = ↑(toDual a) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `toDualBotEquiv_top` / 定理 `toDualBotEquiv_top`

English:
theorem toDualBotEquiv_top
  given: [LE α]
  statement: WithTop.toDualBotEquiv (⊤ : WithTop αᵒᵈ) = ⊤
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 toDualBotEquiv_top
  条件: [LE α]
  结论: WithTop.toDualBotEquiv (⊤ : WithTop αᵒᵈ) = ⊤
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem toDualBotEquiv_top [LE α] : WithTop.toDualBotEquiv (⊤ : WithTop αᵒᵈ) = ⊤ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `toDualBotEquiv_symm_top` / 定理 `toDualBotEquiv_symm_top`

English:
theorem toDualBotEquiv_symm_top
  given: [LE α]
  statement: WithTop.toDualBotEquiv.symm (⊤ : (WithBot α)ᵒᵈ) = ⊤
  proof: rfl

@[to_dual]

中文:
定理 toDualBotEquiv_symm_top
  条件: [LE α]
  结论: WithTop.toDualBotEquiv.symm (⊤ : (WithBot α)ᵒᵈ) = ⊤
  证明: rfl

@[to_dual]
-/
theorem toDualBotEquiv_symm_top [LE α] : WithTop.toDualBotEquiv.symm (⊤ : (WithBot α)ᵒᵈ) = ⊤ :=
  rfl

@[to_dual]
/--
theorem `coe_toDualBotEquiv` / 定理 `coe_toDualBotEquiv`

English:
theorem coe_toDualBotEquiv
  given: [LE α]
  proof: funext fun _ => rfl

@[deprecated (since := "2026-03-27")]
alias _root_.WithBot.coe_toDualTopEquiv_eq := WithBot.coe_toDualTopEquiv

中文:
定理 coe_toDualBotEquiv
  条件: [LE α]
  证明: funext fun _ => rfl

@[deprecated (since := "2026-03-27")]
alias _root_.WithBot.coe_toDualTopEquiv_eq := WithBot.coe_toDualTopEquiv
-/
theorem coe_toDualBotEquiv [LE α] :
    (WithTop.toDualBotEquiv : WithTop αᵒᵈ -> (WithBot α)ᵒᵈ) = toDual ∘ WithTop.ofDual :=
  funext fun _ => rfl

@[deprecated (since := "2026-03-27")]
alias _root_.WithBot.coe_toDualTopEquiv_eq := WithBot.coe_toDualTopEquiv

/-- Embedding into `WithTop α`. -/
@[to_dual (attr := simps) /-- Embedding into `WithBot α`. -/]
/--
Definition of `_root_.Function.Embedding.coeWithTop` / `_root_.Function.Embedding.coeWithTop` 的定义

English:
definition _root_.Function.Embedding.coeWithTop
  signature: : α ↪ WithTop α where
  body: (↑)
  inj' := WithTop.coe_injective

中文:
定义 _root_.函数.嵌入.coeWithTop
  签名: : α ↪ WithTop α where
  定义体: (↑)
  inj' := WithTop.coe_injective
-/
def _root_.Function.Embedding.coeWithTop : α ↪ WithTop α where
  toFun := (↑)
  inj' := WithTop.coe_injective

/-- The coercion `α → WithTop α` bundled as monotone map. -/
@[to_dual
/-- The coercion `α → WithBot α` bundled as monotone map. -/]
/--
Definition of `coeOrderHom` / `coeOrderHom` 的定义

English:
definition coeOrderHom
  signature: {α : Type*} [Preorder α]
  body: (↑)
  inj' := WithTop.coe_injective
  map_rel_iff' := WithTop.coe_le_coe

中文:
定义 coeOrderHom
  签名: {α : 类型} [预序 α]
  定义体: (↑)
  inj' := WithTop.coe_injective
  map_rel_iff' := WithTop.coe_le_coe
-/
def coeOrderHom {α : Type*} [Preorder α] : α ↪o WithTop α where
  toFun := (↑)
  inj' := WithTop.coe_injective
  map_rel_iff' := WithTop.coe_le_coe

-- `simps` could generate this theorem, but `to_dual` is not happy with that version.
@[to_dual (attr := simp)]
/--
theorem `coeOrderHom_apply` / 定理 `coeOrderHom_apply`

English:
theorem coeOrderHom_apply
  given: {α : Type*} [Preorder α]
  statement: (coeOrderHom : α -> WithTop α) = some
  proof: rfl

中文:
定理 coeOrderHom_apply
  条件: {α : 类型} [预序 α]
  结论: (coeOrderHom : α -> WithTop α) = some
  证明: rfl

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval, f.val
-/
theorem coeOrderHom_apply {α : Type*} [Preorder α] : (coeOrderHom : α -> WithTop α) = some := rfl

/-- Any `OrderTop` is equivalent to `WithTop` of the subtype excluding `⊤`.

See also `Equiv.optionSubtypeNe`. -/
@[to_dual
/-- Any `OrderBot` is equivalent to `WithBot` of the subtype excluding `⊥`.

See also `Equiv.optionSubtypeNe`. -/]
/--
Definition of `subtypeOrderIso` / `subtypeOrderIso` 的定义

English:
definition subtypeOrderIso
  signature: [PartialOrder α] [OrderTop α] [DecidablePred (· = (⊤ : α))]
  body: (a.map (↑)).untopD ⊤
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

中文:
定义 subtypeOrderIso
  签名: [偏序 α] [有顶序 α] [DecidablePred (· = (⊤ : α))]
  定义体: (a.map (↑)).untopD ⊤
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

Depends on / 依赖: a.map, untopD
-/
def subtypeOrderIso [PartialOrder α] [OrderTop α] [DecidablePred (· = (⊤ : α))] :
    WithTop {a : α // a != ⊤} ≃o α where
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
/--
theorem `subtypeOrderIso_apply_coe` / 定理 `subtypeOrderIso_apply_coe`

English:
theorem subtypeOrderIso_apply_coe
  statement: [PartialOrder α] [OrderTop α] [DecidablePred (· = (⊤ : α))]
  proof: rfl

@[to_dual]

中文:
定理 subtypeOrderIso_apply_coe
  结论: [偏序 α] [有顶序 α] [DecidablePred (· = (⊤ : α))]
  证明: rfl

@[to_dual]
-/
theorem subtypeOrderIso_apply_coe [PartialOrder α] [OrderTop α] [DecidablePred (· = (⊤ : α))]
    (a : {a : α // a != ⊤}) :
  subtypeOrderIso (a : WithTop {a : α // a != ⊤}) = a := rfl

@[to_dual]
/--
theorem `subtypeOrderIso_symm_apply` / 定理 `subtypeOrderIso_symm_apply`

English:
theorem subtypeOrderIso_symm_apply
  statement: [PartialOrder α] [OrderTop α] [DecidablePred (· = (⊤ : α))]
  proof: by
  rw [OrderIso.symm_apply_eq]
  rfl

中文:
定理 subtypeOrderIso_symm_apply
  结论: [偏序 α] [有顶序 α] [DecidablePred (· = (⊤ : α))]
  证明: by
  rw [OrderIso.symm_apply_eq]
  rfl

Depends on / 依赖: OrderIso, OrderIso.symm_apply_eq, symm_apply_eq
-/
theorem subtypeOrderIso_symm_apply [PartialOrder α] [OrderTop α] [DecidablePred (· = (⊤ : α))]
    {a : α} (h : a != ⊤) :
    subtypeOrderIso.symm a = (⟨a, h⟩ : {a : α // a != ⊤}) := by
  rw [OrderIso.symm_apply_eq]
  rfl

end WithTop

namespace OrderHom

variable [Preorder α] [Preorder β]

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `WithBot α →o WithBot β`. -/
@[to_dual (attr := simps -fullyApplied)
/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `WithTop α →o WithTop β`. -/]
/--
Definition of `withBotMap` / `withBotMap` 的定义

English:
definition withBotMap
  signature: (f : α ->o β)
  body: ⟨WithBot.map f, f.mono.withBot_map⟩

中文:
定义 withBotMap
  签名: (f : α ->o β)
  定义体: ⟨WithBot.map f, f.mono.withBot_map⟩
-/
protected def withBotMap (f : α ->o β) : WithBot α ->o WithBot β :=
  ⟨WithBot.map f, f.mono.withBot_map⟩

end OrderHom

namespace OrderEmbedding

variable [Preorder α] [Preorder β]

/-- A version of `WithBot.map` for order embeddings. -/
@[to_dual /-- A version of `WithTop.map` for order embeddings. -/]
/--
Definition of `withBotMap` / `withBotMap` 的定义

English:
definition withBotMap
  signature: (f : α ↪o β)
  body: WithBot.map f
  inj' := WithBot.map_injective f.injective
  map_rel_iff' := WithBot.map_le_iff f f.map_rel_iff

中文:
定义 withBotMap
  签名: (f : α ↪o β)
  定义体: WithBot.map f
  inj' := WithBot.map_injective f.injective
  map_rel_iff' := WithBot.map_le_iff f f.map_rel_iff
-/
protected def withBotMap (f : α ↪o β) : WithBot α ↪o WithBot β where
  toFun := WithBot.map f
  inj' := WithBot.map_injective f.injective
  map_rel_iff' := WithBot.map_le_iff f f.map_rel_iff

-- `simps` could generate this theorem, but `to_dual` is not happy with that version.
@[to_dual (attr := simp)]
/--
theorem `withBotMap_apply` / 定理 `withBotMap_apply`

English:
theorem withBotMap_apply
  given: (f : α ↪o β)
  statement: ⇑f.withBotMap = WithBot.map f
  proof: rfl

中文:
定理 withBotMap_apply
  条件: (f : α ↪o β)
  结论: ⇑f.withBotMap = WithBot.map f
  证明: rfl
-/
theorem withBotMap_apply (f : α ↪o β) : ⇑f.withBotMap = WithBot.map f := rfl

end OrderEmbedding

namespace OrderIso

variable [PartialOrder α] [PartialOrder β] [PartialOrder γ]

/-- A version of `Equiv.optionCongr` for `WithTop`. -/
@[to_dual /-- A version of `Equiv.optionCongr` for `WithBot`. -/]
/--
Definition of `withTopCongr` / `withTopCongr` 的定义

English:
definition withTopCongr
  signature: (e : α ≃o β)
  body: WithTop.map e
  __ := e.toOrderEmbedding.withTopMap
  __ := e.toEquiv.withTopCongr

中文:
定义 withTopCongr
  签名: (e : α ≃o β)
  定义体: WithTop.map e
  __ := e.toOrderEmbedding.withTopMap
  __ := e.toEquiv.withTopCongr

Depends on / 依赖: WithTop, WithTop.map
-/
def withTopCongr (e : α ≃o β) : WithTop α ≃o WithTop β where
  toFun := WithTop.map e
  __ := e.toOrderEmbedding.withTopMap
  __ := e.toEquiv.withTopCongr

-- `simps` could generate this theorem, but `to_dual` is not happy with that version.
@[to_dual (attr := simp)]
/--
theorem `withTopCongr_apply` / 定理 `withTopCongr_apply`

English:
theorem withTopCongr_apply
  given: (e : α ≃o β)
  statement: ⇑e.withTopCongr = WithTop.map e
  proof: rfl

@[simp]

中文:
定理 withTopCongr_apply
  条件: (e : α ≃o β)
  结论: ⇑e.withTopCongr = WithTop.map e
  证明: rfl

@[simp]
-/
theorem withTopCongr_apply (e : α ≃o β) : ⇑e.withTopCongr = WithTop.map e := rfl

@[simp]
/--
theorem `withTopCongr_refl` / 定理 `withTopCongr_refl`

English:
theorem withTopCongr_refl
  statement: (OrderIso.refl α).withTopCongr = OrderIso.refl _
  proof: RelIso.toEquiv_injective Equiv.withTopCongr_refl

@[simp]

中文:
定理 withTopCongr_refl
  结论: (OrderIso.refl α).withTopCongr = OrderIso.refl _
  证明: RelIso.toEquiv_injective Equiv.withTopCongr_refl

@[simp]

Depends on / 依赖: Equiv.withTopCongr_refl, RelIso, RelIso.toEquiv_injective, toEquiv_injective, withTopCongr_refl
-/
theorem withTopCongr_refl : (OrderIso.refl α).withTopCongr = OrderIso.refl _ :=
  RelIso.toEquiv_injective Equiv.withTopCongr_refl

@[simp]
/--
theorem `withTopCongr_symm` / 定理 `withTopCongr_symm`

English:
theorem withTopCongr_symm
  given: (e : α ≃o β)
  statement: e.symm.withTopCongr = e.withTopCongr.symm
  proof: RelIso.toEquiv_injective e.toEquiv.withTopCongr_symm

@[simp]

中文:
定理 withTopCongr_symm
  条件: (e : α ≃o β)
  结论: e.symm.withTopCongr = e.withTopCongr.symm
  证明: RelIso.toEquiv_injective e.toEquiv.withTopCongr_symm

@[simp]

Depends on / 依赖: RelIso, RelIso.toEquiv_injective, e.toEquiv.withTopCongr_symm, f.val, g.val, toEquiv, toEquiv_injective, withTopCongr_symm
-/
theorem withTopCongr_symm (e : α ≃o β) : e.symm.withTopCongr = e.withTopCongr.symm :=
  RelIso.toEquiv_injective e.toEquiv.withTopCongr_symm

@[simp]
/--
theorem `withTopCongr_trans` / 定理 `withTopCongr_trans`

English:
theorem withTopCongr_trans
  given: (e₁ : α ≃o β) (e₂ : β ≃o γ)
  proof: RelIso.toEquiv_injective e₁.toEquiv.withTopCongr_trans e₂.toEquiv

@[to_dual existing, simp]

中文:
定理 withTopCongr_trans
  条件: (e₁ : α ≃o β) (e₂ : β ≃o γ)
  证明: RelIso.toEquiv_injective e₁.toEquiv.withTopCongr_trans e₂.toEquiv

@[to_dual existing, simp]

Depends on / 依赖: RelIso, RelIso.toEquiv_injective, toEquiv, toEquiv.withTopCongr_trans, toEquiv_injective, withTopCongr_trans
-/
theorem withTopCongr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) :
    (e₁.trans e₂).withTopCongr = e₁.withTopCongr.trans e₂.withTopCongr :=
RelIso.toEquiv_injective e₁.toEquiv.withTopCongr_trans e₂.toEquiv

@[to_dual existing, simp]
/--
theorem `withBotCongr_refl` / 定理 `withBotCongr_refl`

English:
theorem withBotCongr_refl
  statement: (OrderIso.refl α).withBotCongr = OrderIso.refl _
  proof: RelIso.toEquiv_injective Equiv.withBotCongr_refl

@[to_dual existing, simp]

中文:
定理 withBotCongr_refl
  结论: (OrderIso.refl α).withBotCongr = OrderIso.refl _
  证明: RelIso.toEquiv_injective Equiv.withBotCongr_refl

@[to_dual existing, simp]

Depends on / 依赖: Equiv.withBotCongr_refl, Hom.id, RelIso, RelIso.toEquiv_injective, aeval_X_left, toEquiv_injective, withBotCongr_refl
-/
theorem withBotCongr_refl : (OrderIso.refl α).withBotCongr = OrderIso.refl _ :=
  RelIso.toEquiv_injective Equiv.withBotCongr_refl

@[to_dual existing, simp]
/--
theorem `withBotCongr_symm` / 定理 `withBotCongr_symm`

English:
theorem withBotCongr_symm
  given: (e : α ≃o β)
  statement: e.symm.withBotCongr = e.withBotCongr.symm
  proof: RelIso.toEquiv_injective e.toEquiv.withBotCongr_symm

@[to_dual existing, simp]

中文:
定理 withBotCongr_symm
  条件: (e : α ≃o β)
  结论: e.symm.withBotCongr = e.withBotCongr.symm
  证明: RelIso.toEquiv_injective e.toEquiv.withBotCongr_symm

@[to_dual existing, simp]

Depends on / 依赖: RelIso, RelIso.toEquiv_injective, e.toEquiv.withBotCongr_symm, toEquiv, toEquiv_injective, withBotCongr_symm
-/
theorem withBotCongr_symm (e : α ≃o β) : e.symm.withBotCongr = e.withBotCongr.symm :=
  RelIso.toEquiv_injective e.toEquiv.withBotCongr_symm

@[to_dual existing, simp]
/--
theorem `withBotCongr_trans` / 定理 `withBotCongr_trans`

English:
theorem withBotCongr_trans
  given: (e₁ : α ≃o β) (e₂ : β ≃o γ)
  proof: RelIso.toEquiv_injective e₁.toEquiv.withBotCongr_trans e₂.toEquiv

中文:
定理 withBotCongr_trans
  条件: (e₁ : α ≃o β) (e₂ : β ≃o γ)
  证明: RelIso.toEquiv_injective e₁.toEquiv.withBotCongr_trans e₂.toEquiv

Depends on / 依赖: RelIso, RelIso.toEquiv_injective, toEquiv, toEquiv.withBotCongr_trans, toEquiv_injective, withBotCongr_trans
-/
theorem withBotCongr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) :
    (e₁.trans e₂).withBotCongr = e₁.withBotCongr.trans e₂.withBotCongr :=
RelIso.toEquiv_injective e₁.toEquiv.withBotCongr_trans e₂.toEquiv

end OrderIso

namespace SupHom

variable [SemilatticeSup α] [SemilatticeSup β] [SemilatticeSup γ]

/-- Adjoins a `⊤` to the domain and codomain of a `SupHom`. -/
@[to_dual (attr := simps) /-- Adjoins a `⊥` to the domain and codomain of an `InfHom`. -/]
/--
Definition of `withTop` / `withTop` 的定义

English:
definition withTop
  signature: (f : SupHom α β)
  body: WithTop.map f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => rfl
    | ⊤, (b : α) => rfl
    | (a : α), ⊤ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)

@[to_dual (attr := simp)]

中文:
定义 withTop
  签名: (f : 并态射 α β)
  定义体: WithTop.map f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => rfl
    | ⊤, (b : α) => rfl
    | (a : α), ⊤ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)

@[to_dual (attr := simp)]
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
/--
theorem `withTop_id` / 定理 `withTop_id`

English:
theorem withTop_id
  statement: (SupHom.id α).withTop = SupHom.id _
  proof: DFunLike.coe_injective WithTop.map_id

@[to_dual (attr := simp)]

中文:
定理 withTop_id
  结论: (并态射.id α).withTop = 并态射.id _
  证明: DFunLike.coe_injective WithTop.map_id

@[to_dual (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, WithTop, WithTop.map_id, coe_injective, map_id
-/
theorem withTop_id : (SupHom.id α).withTop = SupHom.id _ := DFunLike.coe_injective WithTop.map_id

@[to_dual (attr := simp)]
/--
theorem `withTop_comp` / 定理 `withTop_comp`

English:
theorem withTop_comp
  given: (f : SupHom β γ) (g : SupHom α β)
  proof: DFunLike.coe_injective Eq.symm WithTop.map_comp_map _ _

中文:
定理 withTop_comp
  条件: (f : 并态射 β γ) (g : 并态射 α β)
  证明: DFunLike.coe_injective Eq.symm WithTop.map_comp_map _ _

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Eq.symm, WithTop, WithTop.map_comp_map, coe_injective, map_comp_map
-/
theorem withTop_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
DFunLike.coe_injective Eq.symm WithTop.map_comp_map _ _

/-- Adjoins a `⊥` to the domain and codomain of a `SupHom`. -/
@[to_dual (attr := simps) /-- Adjoins a `⊤` to the domain and codomain of an `InfHom`. -/]
/--
Definition of `withBot` / `withBot` 的定义

English:
definition withBot
  signature: (f : SupHom α β)
  body: WithBot.map f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => rfl
    | ⊥, (b : α) => rfl
    | (a : α), ⊥ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)
  map_bot' := rfl

@[to_dual (attr := simp)]

中文:
定义 withBot
  签名: (f : 并态射 α β)
  定义体: WithBot.map f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => rfl
    | ⊥, (b : α) => rfl
    | (a : α), ⊥ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)
  map_bot' := rfl

@[to_dual (attr := simp)]
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
/--
theorem `withBot_id` / 定理 `withBot_id`

English:
theorem withBot_id
  statement: (SupHom.id α).withBot = SupBotHom.id _
  proof: DFunLike.coe_injective WithBot.map_id

@[to_dual (attr := simp)]

中文:
定理 withBot_id
  结论: (并态射.id α).withBot = SupBot态射.id _
  证明: DFunLike.coe_injective WithBot.map_id

@[to_dual (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, WithBot, WithBot.map_id, coe_injective, map_id
-/
theorem withBot_id : (SupHom.id α).withBot = SupBotHom.id _ := DFunLike.coe_injective WithBot.map_id

@[to_dual (attr := simp)]
/--
theorem `withBot_comp` / 定理 `withBot_comp`

English:
theorem withBot_comp
  given: (f : SupHom β γ) (g : SupHom α β)
  proof: DFunLike.coe_injective Eq.symm WithBot.map_comp_map _ _

中文:
定理 withBot_comp
  条件: (f : 并态射 β γ) (g : 并态射 α β)
  证明: DFunLike.coe_injective Eq.symm WithBot.map_comp_map _ _

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Eq.symm, WithBot, WithBot.map_comp_map, coe_injective, map_comp_map
-/
theorem withBot_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).withBot = f.withBot.comp g.withBot :=
DFunLike.coe_injective Eq.symm WithBot.map_comp_map _ _

/-- Adjoins a `⊤` to the domain of a `SupHom`. -/
@[to_dual (attr := simps) /-- Adjoins a `⊥` to the domain of an `InfHom`. -/]
/--
Definition of `withTop'` / `withTop'` 的定义

English:
definition withTop'
  signature: [OrderTop β] (f : SupHom α β)
  body: a.elim ⊤ f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => (top_sup_eq _).symm
    | ⊤, (b : α) => (top_sup_eq _).symm
    | (a : α), ⊤ => (sup_top_eq _).symm
    | (a : α), (b : α) => f.map_sup' _ _

中文:
定义 withTop'
  签名: [有顶序 β] (f : 并态射 α β)
  定义体: a.elim ⊤ f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => (top_sup_eq _).symm
    | ⊤, (b : α) => (top_sup_eq _).symm
    | (a : α), ⊤ => (sup_top_eq _).symm
    | (a : α), (b : α) => f.map_sup' _ _

Depends on / 依赖: a.elim
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
/--
Definition of `withBot'` / `withBot'` 的定义

English:
definition withBot'
  signature: [OrderBot β] (f : SupHom α β)
  body: a.elim ⊥ f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => (bot_sup_eq _).symm
    | ⊥, (b : α) => (bot_sup_eq _).symm
    | (a : α), ⊥ => (sup_bot_eq _).symm
    | (a : α), (b : α) => f.map_sup' _ _
  map_bot' := rfl

中文:
定义 withBot'
  签名: [有底序 β] (f : 并态射 α β)
  定义体: a.elim ⊥ f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => (bot_sup_eq _).symm
    | ⊥, (b : α) => (bot_sup_eq _).symm
    | (a : α), ⊥ => (sup_bot_eq _).symm
    | (a : α), (b : α) => f.map_sup' _ _
  map_bot' := rfl

Depends on / 依赖: a.elim
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

/--
Definition of `withTop` / `withTop` 的定义

English:
definition withTop
  signature: (f : LatticeHom α β)
  body: { f.toInfHom.withTop with toSupHom := f.toSupHom.withTop }

中文:
定义 withTop
  签名: (f : 格态射 α β)
  定义体: { f.toInfHom.withTop with toSupHom := f.toSupHom.withTop }
-/
protected def withTop (f : LatticeHom α β) : LatticeHom (WithTop α) (WithTop β) :=
  { f.toInfHom.withTop with toSupHom := f.toSupHom.withTop }

/-- Adjoins a `⊥` to the domain and codomain of a `LatticeHom`. -/
@[to_dual existing]
/--
Definition of `withBot` / `withBot` 的定义

English:
definition withBot
  signature: (f : LatticeHom α β)
  body: { f.toInfHom.withBot with toSupHom := f.toSupHom.withBot }

中文:
定义 withBot
  签名: (f : 格态射 α β)
  定义体: { f.toInfHom.withBot with toSupHom := f.toSupHom.withBot }
-/
protected def withBot (f : LatticeHom α β) : LatticeHom (WithBot α) (WithBot β) :=
  { f.toInfHom.withBot with toSupHom := f.toSupHom.withBot }

-- Porting note: `simps` doesn't generate those
@[to_dual (attr := simp, norm_cast)]
/--
lemma `coe_withTop` / 引理 `coe_withTop`

English:
lemma coe_withTop
  given: (f : LatticeHom α β)
  statement: ⇑f.withTop = WithTop.map f
  proof: rfl

@[to_dual (attr := simp)]

中文:
引理 coe_withTop
  条件: (f : 格态射 α β)
  结论: ⇑f.withTop = WithTop.map f
  证明: rfl

@[to_dual (attr := simp)]
-/
lemma coe_withTop (f : LatticeHom α β) : ⇑f.withTop = WithTop.map f := rfl

@[to_dual (attr := simp)]
/--
lemma `withTop_apply` / 引理 `withTop_apply`

English:
lemma withTop_apply
  given: (f : LatticeHom α β) (a : WithTop α)
  statement: f.withTop a = a.map f
  proof: rfl

@[to_dual (attr := simp)]

中文:
引理 withTop_apply
  条件: (f : 格态射 α β) (a : WithTop α)
  结论: f.withTop a = a.map f
  证明: rfl

@[to_dual (attr := simp)]
-/
lemma withTop_apply (f : LatticeHom α β) (a : WithTop α) : f.withTop a = a.map f := rfl

@[to_dual (attr := simp)]
/--
theorem `withTop_id` / 定理 `withTop_id`

English:
theorem withTop_id
  statement: (LatticeHom.id α).withTop = LatticeHom.id _
  proof: DFunLike.coe_injective WithTop.map_id

@[to_dual (attr := simp)]

中文:
定理 withTop_id
  结论: (格态射.id α).withTop = 格态射.id _
  证明: DFunLike.coe_injective WithTop.map_id

@[to_dual (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, WithTop, WithTop.map_id, coe_injective, map_id
-/
theorem withTop_id : (LatticeHom.id α).withTop = LatticeHom.id _ :=
  DFunLike.coe_injective WithTop.map_id

@[to_dual (attr := simp)]
/--
theorem `withTop_comp` / 定理 `withTop_comp`

English:
theorem withTop_comp
  given: (f : LatticeHom β γ) (g : LatticeHom α β)
  proof: DFunLike.coe_injective Eq.symm WithTop.map_comp_map _ _

中文:
定理 withTop_comp
  条件: (f : 格态射 β γ) (g : 格态射 α β)
  证明: DFunLike.coe_injective Eq.symm WithTop.map_comp_map _ _

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Eq.symm, WithTop, WithTop.map_comp_map, coe_injective, map_comp_map
-/
theorem withTop_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
DFunLike.coe_injective Eq.symm WithTop.map_comp_map _ _

/-- Adjoins a `⊤` and `⊥` to the domain and codomain of a `LatticeHom`. -/
@[to_dual /-- Adjoins a `⊥` and `⊤` to the domain and codomain of a `LatticeHom`. -/]
/--
Definition of `withTopWithBot` / `withTopWithBot` 的定义

English:
definition withTopWithBot
  signature: (f : LatticeHom α β)
  body: ⟨f.withBot.withTop, rfl, rfl⟩

中文:
定义 withTopWithBot
  签名: (f : 格态射 α β)
  定义体: ⟨f.withBot.withTop, rfl, rfl⟩

Depends on / 依赖: f.withBot.withTop, withBot, withTop
-/
def withTopWithBot (f : LatticeHom α β) :
    BoundedLatticeHom (WithTop <| WithBot α) (WithTop <| WithBot β) :=
  ⟨f.withBot.withTop, rfl, rfl⟩

-- Porting note: `simps` doesn't generate those
@[to_dual (attr := simp, norm_cast)]
/--
lemma `coe_withTopWithBot` / 引理 `coe_withTopWithBot`

English:
lemma coe_withTopWithBot
  given: (f : LatticeHom α β)
  proof: rfl

@[to_dual (attr := simp)]

中文:
引理 coe_withTopWithBot
  条件: (f : 格态射 α β)
  证明: rfl

@[to_dual (attr := simp)]
-/
lemma coe_withTopWithBot (f : LatticeHom α β) :
    ⇑f.withTopWithBot = WithTop.map (WithBot.map f) :=
  rfl

@[to_dual (attr := simp)]
/--
lemma `withTopWithBot_apply` / 引理 `withTopWithBot_apply`

English:
lemma withTopWithBot_apply
  given: (f : LatticeHom α β) (a : WithTop <| WithBot α)
  proof: rfl

@[to_dual (attr := simp)]

中文:
引理 withTopWithBot_apply
  条件: (f : 格态射 α β) (a : WithTop <| WithBot α)
  证明: rfl

@[to_dual (attr := simp)]
-/
lemma withTopWithBot_apply (f : LatticeHom α β) (a : WithTop <| WithBot α) :
    f.withTopWithBot a = a.map (WithBot.map f) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `withTopWithBot_id` / 定理 `withTopWithBot_id`

English:
theorem withTopWithBot_id
  statement: (LatticeHom.id α).withTopWithBot = BoundedLatticeHom.id _
  proof: DFunLike.coe_injective by simp [WithTop.map_id, WithBot.map_id]

@[to_dual (attr := simp)]

中文:
定理 withTopWithBot_id
  结论: (格态射.id α).withTopWithBot = 有界格态射.id _
  证明: DFunLike.coe_injective by simp [WithTop.map_id, WithBot.map_id]

@[to_dual (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, WithBot, WithBot.map_id, WithTop, WithTop.map_id, coe_injective, map_id
-/
theorem withTopWithBot_id : (LatticeHom.id α).withTopWithBot = BoundedLatticeHom.id _ :=
DFunLike.coe_injective by simp [WithTop.map_id, WithBot.map_id]

@[to_dual (attr := simp)]
/--
theorem `withTopWithBot_comp` / 定理 `withTopWithBot_comp`

English:
theorem withTopWithBot_comp
  given: (f : LatticeHom β γ) (g : LatticeHom α β)
  proof: by
  ext; simp

中文:
定理 withTopWithBot_comp
  条件: (f : 格态射 β γ) (g : 格态射 α β)
  证明: by
  ext; simp
-/
theorem withTopWithBot_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withTopWithBot = f.withTopWithBot.comp g.withTopWithBot := by
  ext; simp

/--
Definition of `withTop'` / `withTop'` 的定义

English:
definition withTop'
  signature: [OrderTop β] (f : LatticeHom α β)
  body: { f.toSupHom.withTop', f.toInfHom.withTop' with }

中文:
定义 withTop'
  签名: [有顶序 β] (f : 格态射 α β)
  定义体: { f.toSupHom.withTop', f.toInfHom.withTop' with }

Depends on / 依赖: f.toInfHom.withTop, f.toSupHom.withTop, toInfHom, toSupHom, withTop
-/
def withTop' [OrderTop β] (f : LatticeHom α β) : LatticeHom (WithTop α) β :=
  { f.toSupHom.withTop', f.toInfHom.withTop' with }

/-- Adjoins a `⊥` to the domain of a `LatticeHom`. -/
@[to_dual existing (attr := simps!)]
/--
Definition of `withBot'` / `withBot'` 的定义

English:
definition withBot'
  signature: [OrderBot β] (f : LatticeHom α β)
  body: { f.toSupHom.withBot', f.toInfHom.withBot' with }

中文:
定义 withBot'
  签名: [有底序 β] (f : 格态射 α β)
  定义体: { f.toSupHom.withBot', f.toInfHom.withBot' with }

Depends on / 依赖: f.toInfHom.withBot, f.toSupHom.withBot, toInfHom, toSupHom, withBot
-/
def withBot' [OrderBot β] (f : LatticeHom α β) : LatticeHom (WithBot α) β :=
  { f.toSupHom.withBot', f.toInfHom.withBot' with }

/-- Adjoins a `⊤` and `⊥` to the domain of a `LatticeHom`. -/
@[to_dual (attr := simps!) /-- Adjoins a `⊥` and `⊤` to the domain of a `LatticeHom`. -/]
/--
Definition of `withTopWithBot'` / `withTopWithBot'` 的定义

English:
definition withTopWithBot'
  signature: [BoundedOrder β] (f : LatticeHom α β)
  body: f.withBot'.withTop'
  map_top' := rfl
  map_bot' := rfl

中文:
定义 withTopWithBot'
  签名: [有界序 β] (f : 格态射 α β)
  定义体: f.withBot'.withTop'
  map_top' := rfl
  map_bot' := rfl

Depends on / 依赖: f.withBot, withBot, withTop
-/
def withTopWithBot' [BoundedOrder β] (f : LatticeHom α β) :
    BoundedLatticeHom (WithTop <| WithBot α) β where
  toLatticeHom := f.withBot'.withTop'
  map_top' := rfl
  map_bot' := rfl

end LatticeHom
