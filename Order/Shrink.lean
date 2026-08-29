/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.SuccPred.Basic
public import Mathlib.Logic.Small.Defs

/-!
# Order instances on Shrink

If `α : Type v` is `u`-small, we transport various order related
instances on `α` to `Shrink.{u} α`.

-/

@[expose] public section

universe u

variable {α : Type*} [Small.{u} α]

section Bot
variable [Bot α]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (Shrink.{u} α)
  body: equivShrink _ ⊥

@[to_dual (attr := simp)]

中文:
实例 :
  签名: Bot (Shrink.{u} α)
  定义体: equivShrink _ ⊥

@[to_dual (attr := simp)]

Depends on / 依赖: equivShrink
-/
noncomputable instance : Bot (Shrink.{u} α) where
  bot := equivShrink _ ⊥

@[to_dual (attr := simp)]
/--
lemma `equivShrink_bot` / 引理 `equivShrink_bot`

English:
lemma equivShrink_bot
  statement: equivShrink.{u} α ⊥ = ⊥
  proof: rfl

@[to_dual (attr := simp)]

中文:
引理 equivShrink_bot
  结论: equivShrink.{u} α ⊥ = ⊥
  证明: rfl

@[to_dual (attr := simp)]
-/
lemma equivShrink_bot : equivShrink.{u} α ⊥ = ⊥ := rfl

@[to_dual (attr := simp)]
/--
lemma `equivShrink_symm_bot` / 引理 `equivShrink_symm_bot`

English:
lemma equivShrink_symm_bot
  statement: (equivShrink.{u} α).symm ⊥ = ⊥
  proof: (equivShrink.{u} α).injective (by simp)

中文:
引理 equivShrink_symm_bot
  结论: (equivShrink.{u} α).symm ⊥ = ⊥
  证明: (equivShrink.{u} α).injective (by simp)

Depends on / 依赖: equivShrink, injective
-/
lemma equivShrink_symm_bot : (equivShrink.{u} α).symm ⊥ = ⊥ :=
  (equivShrink.{u} α).injective (by simp)

end Bot

section Preorder
variable [Preorder α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (Shrink.{u} α)
  body: Preorder.lift (equivShrink α).symm

中文:
实例 :
  签名: Preorder (Shrink.{u} α)
  定义体: Preorder.lift (equivShrink α).symm

Depends on / 依赖: Preorder, Preorder.lift, equivShrink
-/
noncomputable instance : Preorder (Shrink.{u} α) :=
  Preorder.lift (equivShrink α).symm

variable (α) in
/--
Definition of `orderIsoShrink` / `orderIsoShrink` 的定义

English:
definition orderIsoShrink
  signature: : α ≃o Shrink.{u} α where
  body: equivShrink α
  map_rel_iff' {a b} := by
    obtain ⟨a, rfl⟩ := (equivShrink.{u} α).symm.surjective a
    obtain ⟨b, rfl⟩ := (equivShrink.{u} α).symm.surjective b
    simp only [Equiv.apply_symm_apply]
    rfl

@[simp]

中文:
定义 orderIsoShrink
  签名: : α ≃o Shrink.{u} α where
  定义体: equivShrink α
  map_rel_iff' {a b} := by
    obtain ⟨a, rfl⟩ := (equivShrink.{u} α).symm.surjective a
    obtain ⟨b, rfl⟩ := (equivShrink.{u} α).symm.surjective b
    simp only [Equiv.apply_symm_apply]
    rfl

@[simp]

Depends on / 依赖: equivShrink
-/
noncomputable def orderIsoShrink : α ≃o Shrink.{u} α where
  toEquiv := equivShrink α
  map_rel_iff' {a b} := by
    obtain ⟨a, rfl⟩ := (equivShrink.{u} α).symm.surjective a
    obtain ⟨b, rfl⟩ := (equivShrink.{u} α).symm.surjective b
    simp only [Equiv.apply_symm_apply]
    rfl

@[simp]
/--
lemma `orderIsoShrink_apply` / 引理 `orderIsoShrink_apply`

English:
lemma orderIsoShrink_apply
  given: (a : α)
  proof: rfl

@[simp]

中文:
引理 orderIsoShrink_apply
  条件: (a : α)
  证明: rfl

@[simp]
-/
lemma orderIsoShrink_apply (a : α) :
    orderIsoShrink α a = equivShrink α a := rfl

@[simp]
/--
lemma `orderIsoShrink_symm_apply` / 引理 `orderIsoShrink_symm_apply`

English:
lemma orderIsoShrink_symm_apply
  given: (a : Shrink.{u} α)
  proof: rfl

@[simp]

中文:
引理 orderIsoShrink_symm_apply
  条件: (a : Shrink.{u} α)
  证明: rfl

@[simp]
-/
lemma orderIsoShrink_symm_apply (a : Shrink.{u} α) :
    (orderIsoShrink α).symm a = (equivShrink α).symm a := rfl

@[simp]
/--
theorem `equivShrink_le_equivShrink` / 定理 `equivShrink_le_equivShrink`

English:
theorem equivShrink_le_equivShrink
  given: {x y : α}
  statement: equivShrink α x <= equivShrink α y ↔ x <= y
  proof: (orderIsoShrink α).map_rel_iff

@[simp]

中文:
定理 equivShrink_le_equivShrink
  条件: {x y : α}
  结论: equivShrink α x <= equivShrink α y ↔ x <= y
  证明: (orderIsoShrink α).map_rel_iff

@[simp]

Depends on / 依赖: map_rel_iff, orderIsoShrink
-/
theorem equivShrink_le_equivShrink {x y : α} : equivShrink α x <= equivShrink α y ↔ x <= y :=
  (orderIsoShrink α).map_rel_iff

@[simp]
/--
theorem `equivShrink_lt_equivShrink` / 定理 `equivShrink_lt_equivShrink`

English:
theorem equivShrink_lt_equivShrink
  given: {x y : α}
  statement: equivShrink α x < equivShrink α y ↔ x < y
  proof: (orderIsoShrink α).toRelIsoLT.map_rel_iff

@[to_dual]

中文:
定理 equivShrink_lt_equivShrink
  条件: {x y : α}
  结论: equivShrink α x < equivShrink α y ↔ x < y
  证明: (orderIsoShrink α).toRelIsoLT.map_rel_iff

@[to_dual]

Depends on / 依赖: map_rel_iff, orderIsoShrink, toRelIsoLT, toRelIsoLT.map_rel_iff
-/
theorem equivShrink_lt_equivShrink {x y : α} : equivShrink α x < equivShrink α y ↔ x < y :=
  (orderIsoShrink α).toRelIsoLT.map_rel_iff

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [OrderBot
  signature: α] : OrderBot (Shrink.{u} α) where
  body: by simp [← (orderIsoShrink.{u} α).symm.le_iff_le]

@[to_dual]

中文:
实例 [OrderBot
  签名: α] : OrderBot (Shrink.{u} α) where
  定义体: by simp [← (orderIsoShrink.{u} α).symm.le_iff_le]

@[to_dual]

Depends on / 依赖: le_iff_le, orderIsoShrink, symm.le_iff_le
-/
noncomputable instance [OrderBot α] : OrderBot (Shrink.{u} α) where
  bot_le a := by simp [← (orderIsoShrink.{u} α).symm.le_iff_le]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SuccOrder
  signature: α] : SuccOrder (Shrink.{u} α)
  body: SuccOrder.ofOrderIso (orderIsoShrink.{u} α)

@[to_dual]

中文:
实例 [SuccOrder
  签名: α] : SuccOrder (Shrink.{u} α)
  定义体: SuccOrder.ofOrderIso (orderIsoShrink.{u} α)

@[to_dual]

Depends on / 依赖: SuccOrder, SuccOrder.ofOrderIso, ofOrderIso, orderIsoShrink
-/
noncomputable instance [SuccOrder α] : SuccOrder (Shrink.{u} α) :=
  SuccOrder.ofOrderIso (orderIsoShrink.{u} α)

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WellFoundedLT
  signature: α] : WellFoundedLT (Shrink.{u} α) where
  body: (orderIsoShrink.{u} α).symm.toRelIsoLT.toRelEmbedding.isWellFounded.wf

中文:
实例 [WellFoundedLT
  签名: α] : WellFoundedLT (Shrink.{u} α) where
  定义体: (orderIsoShrink.{u} α).symm.toRelIsoLT.toRelEmbedding.isWellFounded.wf

Depends on / 依赖: isWellFounded, orderIsoShrink, symm.toRelIsoLT.toRelEmbedding.isWellFounded.wf, toRelEmbedding, toRelIsoLT
-/
instance [WellFoundedLT α] : WellFoundedLT (Shrink.{u} α) where
  wf := (orderIsoShrink.{u} α).symm.toRelIsoLT.toRelEmbedding.isWellFounded.wf

end Preorder

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: α] : PartialOrder (Shrink.{u} α)
  body: (equivShrink _).symm.injective.partialOrder _ .rfl .rfl

中文:
实例 [PartialOrder
  签名: α] : PartialOrder (Shrink.{u} α)
  定义体: (equivShrink _).symm.injective.partialOrder _ .rfl .rfl

Depends on / 依赖: equivShrink, injective, partialOrder, symm.injective.partialOrder
-/
noncomputable instance [PartialOrder α] : PartialOrder (Shrink.{u} α) :=
  (equivShrink _).symm.injective.partialOrder _ .rfl .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: α] : LinearOrder (Shrink.{u} α)
  body: .lift' _ (equivShrink _).symm.injective

中文:
实例 [LinearOrder
  签名: α] : LinearOrder (Shrink.{u} α)
  定义体: .lift' _ (equivShrink _).symm.injective

Depends on / 依赖: equivShrink, injective, symm.injective
-/
noncomputable instance [LinearOrder α] : LinearOrder (Shrink.{u} α) :=
  .lift' _ (equivShrink _).symm.injective
