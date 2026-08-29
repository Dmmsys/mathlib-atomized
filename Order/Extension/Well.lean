/-
Copyright (c) 2022 Yaël Dillies, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Junyan Xu
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.SetTheory.Ordinal.Rank

/-!
# Extend a well-founded order to a well-order

This file constructs a well-order (linear well-founded order) which is an extension of a given
well-founded order.

## Proof idea

We can map our order into two well-orders:
* the first map respects the order but isn't necessarily injective. Namely, this is the *rank*
  function `IsWellFounded.rank : α → Ordinal`.
* the second map is injective but doesn't necessarily respect the order. This is an arbitrary
  embedding into `Cardinal` given by `embeddingToCardinal`.

Then their lexicographic product is a well-founded linear order which our original order injects in.

## Implementation note

The definition in `mathlib` 3 used an auxiliary well-founded order on `α` lifted from `Cardinal`,
instead of using `Cardinal` directly. The new definition is definitionally equal
to the `mathlib` 3 version but avoids non-standard instances.

## Tags

well-founded relation, well order, extension
-/

@[expose] public section


universe u

variable {α : Type u} {r : α -> α -> Prop}

namespace IsWellFounded

variable {α : Type u} (r : α -> α -> Prop) [IsWellFounded α r]

/-- An arbitrary well order on `α` that extends `r`.

The construction maps `r` into two well-orders: the first map is `IsWellFounded.rank`, which is not
necessarily injective but respects the order `r`; the other map is the identity (with an arbitrarily
chosen well-order on `α`), which is injective but doesn't respect `r`.

By taking the lexicographic product of the two, we get both properties, so we can pull it back and
get a well-order that extend our original order `r`. Another way to view this is that we choose an
arbitrary well-order to serve as a tiebreak between two elements of same rank.
-/
@[instance_reducible]
/--
Definition of `wellOrderExtension` / `wellOrderExtension` 的定义

English:
definition wellOrderExtension
  signature: : LinearOrder α
  body: @LinearOrder.lift' α (Ordinal ×ₗ Cardinal) _ (fun a : α => (rank r a, embeddingToCardinal a))
fun _ _ h => embeddingToCardinal.injective congr_arg Prod.snd h

中文:
定义 wellOrderExtension
  签名: : 线性序 α
  定义体: @LinearOrder.lift' α (Ordinal ×ₗ Cardinal) _ (fun a : α => (rank r a, embeddingToCardinal a))
fun _ _ h => embeddingToCardinal.injective congr_arg Prod.snd h

Depends on / 依赖: Cardinal, LinearOrder, LinearOrder.lift, Ordinal, Prod.snd, congr_arg, embeddingToCardinal, embeddingToCardinal.injective, injective
-/
noncomputable def wellOrderExtension : LinearOrder α :=
  @LinearOrder.lift' α (Ordinal ×ₗ Cardinal) _ (fun a : α => (rank r a, embeddingToCardinal a))
fun _ _ h => embeddingToCardinal.injective congr_arg Prod.snd h

/--
Instance `wellOrderExtension.isWellFounded_lt` / 实例 `wellOrderExtension.isWellFounded_lt`

English:
instance wellOrderExtension.isWellFounded_lt
  signature: : IsWellFounded α (wellOrderExtension r).lt
  body: ⟨InvImage.wf (fun a : α => (rank r a, embeddingToCardinal a))
    Ordinal.lt_wf.prod_lex Cardinal.lt_wf⟩

中文:
实例 wellOrderExtension.isWellFounded_lt
  签名: : 是良基 α (wellOrderExtension r).lt
  定义体: ⟨InvImage.wf (fun a : α => (rank r a, embeddingToCardinal a))
    Ordinal.lt_wf.prod_lex Cardinal.lt_wf⟩

Depends on / 依赖: Cardinal, Cardinal.lt_wf, InvImage, InvImage.wf, Ordinal, Ordinal.lt_wf.prod_lex, embeddingToCardinal, lt_wf, prod_lex
-/
instance wellOrderExtension.isWellFounded_lt : IsWellFounded α (wellOrderExtension r).lt :=
⟨InvImage.wf (fun a : α => (rank r a, embeddingToCardinal a))
    Ordinal.lt_wf.prod_lex Cardinal.lt_wf⟩

/--
Instance `wellOrderExtension.isWellOrder_lt` / 实例 `wellOrderExtension.isWellOrder_lt`

English:
instance wellOrderExtension.isWellOrder_lt
  signature: : IsWellOrder α (wellOrderExtension r).lt where

中文:
实例 wellOrderExtension.isWellOrder_lt
  签名: : 是良序 α (wellOrderExtension r).lt where
-/
instance wellOrderExtension.isWellOrder_lt : IsWellOrder α (wellOrderExtension r).lt where

/--
theorem `exists_well_order_ge` / 定理 `exists_well_order_ge`

English:
theorem exists_well_order_ge
  statement: exists s, r <= s ∧ IsWellOrder α s
  proof: ⟨(wellOrderExtension r).lt, fun _ _ h => Prod.Lex.left _ _ (rank_lt_of_rel h), ⟨⟩⟩

中文:
定理 存在_well_order_ge
  结论: 存在 s, r <= s ∧ 是良序 α s
  证明: ⟨(wellOrderExtension r).lt, fun _ _ h => Prod.Lex.left _ _ (rank_lt_of_rel h), ⟨⟩⟩

Depends on / 依赖: Prod.Lex.left, rank_lt_of_rel, wellOrderExtension
-/
theorem exists_well_order_ge : exists s, r <= s ∧ IsWellOrder α s :=
  ⟨(wellOrderExtension r).lt, fun _ _ h => Prod.Lex.left _ _ (rank_lt_of_rel h), ⟨⟩⟩

end IsWellFounded

/--
Definition of `WellOrderExtension` / `WellOrderExtension` 的定义

English:
definition WellOrderExtension
  signature: (α : Type*)
  body: α

中文:
定义 WellOrderExtension
  签名: (α : 类型)
  定义体: α
-/
def WellOrderExtension (α : Type*) : Type _ := α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (WellOrderExtension α)
  body: ‹_›

中文:
实例 [可居
  签名: α] : 可居 (WellOrderExtension α)
  定义体: ‹_›
-/
instance [Inhabited α] : Inhabited (WellOrderExtension α) := ‹_›

/--
Definition of `toWellOrderExtension` / `toWellOrderExtension` 的定义

English:
definition toWellOrderExtension
  signature: : α ≃ WellOrderExtension α
  body: Equiv.refl _

中文:
定义 toWellOrderExtension
  签名: : α ≃ WellOrderExtension α
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def toWellOrderExtension : α ≃ WellOrderExtension α :=
  Equiv.refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: α] [h
  body: fast_instance% h.wellOrderExtension

中文:
实例 [LT
  签名: α] [h
  定义体: fast_instance% h.wellOrderExtension

Depends on / 依赖: fast_instance, h.wellOrderExtension, wellOrderExtension
-/
noncomputable instance [LT α] [h : WellFoundedLT α] : LinearOrder (WellOrderExtension α) :=
  fast_instance% h.wellOrderExtension

/--
Instance `WellOrderExtension.wellFoundedLT` / 实例 `WellOrderExtension.wellFoundedLT`

English:
instance WellOrderExtension.wellFoundedLT
  signature: [LT α] [WellFoundedLT α]
  body: IsWellFounded.wellOrderExtension.isWellFounded_lt (α := α) (· < ·)

中文:
实例 WellOrderExtension.wellFoundedLT
  签名: [LT α] [WellFoundedLT α]
  定义体: IsWellFounded.wellOrderExtension.isWellFounded_lt (α := α) (· < ·)

Depends on / 依赖: IsWellFounded, IsWellFounded.wellOrderExtension.isWellFounded_lt, isWellFounded_lt, wellOrderExtension
-/
instance WellOrderExtension.wellFoundedLT [LT α] [WellFoundedLT α] :
    WellFoundedLT (WellOrderExtension α) :=
  IsWellFounded.wellOrderExtension.isWellFounded_lt (α := α) (· < ·)

/--
theorem `toWellOrderExtension_strictMono` / 定理 `toWellOrderExtension_strictMono`

English:
theorem toWellOrderExtension_strictMono
  given: [Preorder α] [WellFoundedLT α]
  proof: fun _ _ h =>
Prod.Lex.left _ _ IsWellFounded.rank_lt_of_rel h

中文:
定理 toWellOrderExtension_strictMono
  条件: [预序 α] [WellFoundedLT α]
  证明: fun _ _ h =>
Prod.Lex.left _ _ IsWellFounded.rank_lt_of_rel h
-/
theorem toWellOrderExtension_strictMono [Preorder α] [WellFoundedLT α] :
    StrictMono (toWellOrderExtension : α -> WellOrderExtension α) := fun _ _ h =>
Prod.Lex.left _ _ IsWellFounded.rank_lt_of_rel h
