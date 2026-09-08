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

variable {α : Type u} {r : α → α → Prop}

namespace IsWellFounded

variable {α : Type u} (r : α → α → Prop) [IsWellFounded α r]

/-- An arbitrary well order on `α` that extends `r`.

The construction maps `r` into two well-orders: the first map is `IsWellFounded.rank`, which is not
necessarily injective but respects the order `r`; the other map is the identity (with an arbitrarily
chosen well-order on `α`), which is injective but doesn't respect `r`.

By taking the lexicographic product of the two, we get both properties, so we can pull it back and
get a well-order that extend our original order `r`. Another way to view this is that we choose an
arbitrary well-order to serve as a tiebreak between two elements of same rank.
-/
@[instance_reducible]
/-
**IsWellFounded.wellOrderExtension** 是 Mathlib 中的一个定义，位于命名空间 `IsWellFounded`。
形式化陈述：wellOrderExtension : LinearOrder α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary well order on `α` that extends `r`.

The construction maps `r` into two well-orders: the first map is `IsWellFounded.
rank`, which is not
necessarily injective but respects the order `r`; the other map is the identity 
(with an arbitrarily
chosen well-order on `α`), which is injective but doesn't respect `r`.

By taking the lexicographic product of the two, we get both properties, so we ca
n pull it back and
get a well-order that extend our original order `r`. Another way to view this is
 that we choose an
arbitrary well-order to serve as a tiebreak between two elements of same rank.
-/
noncomputable def wellOrderExtension : LinearOrder α :=
  @LinearOrder.lift' α (Ordinal ×ₗ Cardinal) _ (fun a : α => (rank r a, embeddingToCardinal a))
    fun _ _ h => embeddingToCardinal.injective <| congr_arg Prod.snd h
/-
**IsWellFounded.wellOrderExtension.isWellFounded_lt** 是 Mathlib 中的一个定理，位于命名空间 `I
sWellFounded.wellOrderExtension`。
形式化陈述：∀ {α : Type u} (r : α → α → Prop) [inst : IsWellFounded α r], IsWellFounde
d α LT.lt
参数：r : α → α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用引理 `WellFounded.prod_lex`：WellFounded.prod_lex {ra : α -> α -> Prop} {rb : β
 -> β -> Prop} (ha : WellFounded ra) (hb : WellFounded rb) : WellFounded (Prod.L
ex ra rb)
· 使用定理 `Ordinal.lt_wf`：lt_wf : @WellFounded Ordinal (· < ·)
· 使用定理 `Cardinal.lt_wf`：WellFounded fun x1 x2 => x1 < x2
-/
instance wellOrderExtension.isWellFounded_lt : IsWellFounded α (wellOrderExtension r).lt :=
  ⟨InvImage.wf (fun a : α => (rank r a, embeddingToCardinal a)) <|
    Ordinal.lt_wf.prod_lex Cardinal.lt_wf⟩
/-
**IsWellFounded.wellOrderExtension.isWellOrder_lt** 是 Mathlib 中的一个定理，位于命名空间 `IsW
ellFounded.wellOrderExtension`。
形式化陈述：∀ {α : Type u} (r : α → α → Prop) [inst : IsWellFounded α r], IsWellOrder 
α LT.lt
参数：r : α → α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.wellOrderExtension.isWellFounded_lt`：∀ {α : Type u} (r : α
 → α → Prop) [inst : IsWellFounded α r], IsWellFounded α LT.lt
-/
instance wellOrderExtension.isWellOrder_lt : IsWellOrder α (wellOrderExtension r).lt where

/-- Any well-founded relation can be extended to a well-ordering on that type. -/
/-
**IsWellFounded.exists_well_order_ge** 是 Mathlib 中的一个定理，位于命名空间 `IsWellFounded`。
形式化陈述：exists_well_order_ge : exists s, r <= s ∧ IsWellOrder α s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.rank_lt_of_rel`：rank_lt_of_rel (h : r a b) : rank r a < ra
nk r b
· 使用定理 `IsWellFounded.wellOrderExtension.isWellFounded_lt`：∀ {α : Type u} (r : α
 → α → Prop) [inst : IsWellFounded α r], IsWellFounded α LT.lt

--- 原说明 ---
Any well-founded relation can be extended to a well-ordering on that type.
-/
theorem exists_well_order_ge : ∃ s, r ≤ s ∧ IsWellOrder α s :=
  ⟨(wellOrderExtension r).lt, fun _ _ h => Prod.Lex.left _ _ (rank_lt_of_rel h), ⟨⟩⟩

end IsWellFounded

/-- A type alias for `α`, intended to extend a well-founded order on `α` to a well-order. -/
/-
**WellOrderExtension** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WellOrderExtension (α : Type*) : Type _
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type alias for `α`, intended to extend a well-founded order on `α` to a well-o
rder.
-/
def WellOrderExtension (α : Type*) : Type _ := α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (WellOrderExtension α) := ‹_›

/-- "Identity" equivalence between a well-founded order and its well-order extension. -/
/-
**toWellOrderExtension** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toWellOrderExtension : α ≃ WellOrderExtension α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
"Identity" equivalence between a well-founded order and its well-order extension
.
-/
def toWellOrderExtension : α ≃ WellOrderExtension α :=
  Equiv.refl _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [LT α] [h : WellFoundedLT α] : LinearOrder (WellOrderExtension α) :=
  fast_instance% h.wellOrderExtension
/-
**WellOrderExtension.wellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WellOrderExtension.wellFoundedLT [LT α] [WellFoundedLT α] : WellFoundedLT 
(WellOrderExtension α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.wellOrderExtension.isWellFounded_lt`：∀ {α : Type u} (r : α
 → α → Prop) [inst : IsWellFounded α r], IsWellFounded α LT.lt
-/
instance WellOrderExtension.wellFoundedLT [LT α] [WellFoundedLT α] :
    WellFoundedLT (WellOrderExtension α) :=
  IsWellFounded.wellOrderExtension.isWellFounded_lt (α := α) (· < ·)
/-
**toWellOrderExtension_strictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toWellOrderExtension_strictMono [Preorder α] [WellFoundedLT α] : StrictMon
o (toWellOrderExtension : α -> WellOrderExtension α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.rank_lt_of_rel`：rank_lt_of_rel (h : r a b) : rank r a < ra
nk r b
-/
theorem toWellOrderExtension_strictMono [Preorder α] [WellFoundedLT α] :
    StrictMono (toWellOrderExtension : α → WellOrderExtension α) := fun _ _ h =>
  Prod.Lex.left _ _ <| IsWellFounded.rank_lt_of_rel h
