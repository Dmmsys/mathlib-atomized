/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Order.Interval.Basic
public import Mathlib.Data.Prod.Lex
public import Mathlib.Tactic.FastInstance
meta import Mathlib.Order.Interval.Basic  -- shake: keep (for `#eval` testing)
meta import Mathlib.Order.Lex  -- shake: keep (for `#eval` testing)

/-!
# The lexicographic order on intervals

This order is compatible with the inclusion ordering, but is total.

Under this ordering, `[(3, 3), (2, 2), (2, 3), (1, 1), (1, 2), (1, 3)]` is sorted.
-/

public section

namespace NonemptyInterval

variable {α}

section LELT
variable [LT α] [LE α]

/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (Lex (NonemptyInterval α)) where
  le x y := toLex (ofLex x).toDualProd ≤ toLex (ofLex y).toDualProd
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LT (Lex (NonemptyInterval α)) where
  lt x y := toLex (ofLex x).toDualProd < toLex (ofLex y).toDualProd
/-
**NonemptyInterval.toLex_le_toLex** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：toLex_le_toLex {x y : NonemptyInterval α} : toLex x <= toLex y ↔ y.fst < x
.fst ∨ x.fst = y.fst ∧ x.snd <= y.snd
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.lex_def`：∀ {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β 
→ Prop} {p q : α × β},   Prod.Lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2
-/
theorem toLex_le_toLex {x y : NonemptyInterval α} :
    toLex x ≤ toLex y ↔ y.fst < x.fst ∨ x.fst = y.fst ∧ x.snd ≤ y.snd :=
  Prod.lex_def
/-
**NonemptyInterval.toLex_lt_toLex** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：toLex_lt_toLex {x y : NonemptyInterval α} : toLex x < toLex y ↔ y.fst < x.
fst ∨ x.fst = y.fst ∧ x.snd < y.snd
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.lex_def`：∀ {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β 
→ Prop} {p q : α × β},   Prod.Lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2
-/
theorem toLex_lt_toLex {x y : NonemptyInterval α} :
    toLex x < toLex y ↔ y.fst < x.fst ∨ x.fst = y.fst ∧ x.snd < y.snd :=
  Prod.lex_def
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] [DecidableLT α] [DecidableLE α] : DecidableLE (Lex (NonemptyInterval α)) :=
  fun _ _ => decidable_of_iff' _ toLex_le_toLex
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] [DecidableLT α] : DecidableLT (Lex (NonemptyInterval α)) :=
  fun _ _ => decidable_of_iff' _ toLex_lt_toLex

-- Sanity check on the ordering.
/-- info: [(3, 3), (2, 2), (2, 3), (1, 1), (1, 2), (1, 3)] -/
#guard_msgs in
#eval [
  NonemptyInterval.mk (1, 1) (by grind),
  NonemptyInterval.mk (1, 2) (by grind),
  NonemptyInterval.mk (1, 3) (by grind),
  NonemptyInterval.mk (2, 2) (by grind),
  NonemptyInterval.mk (2, 3) (by grind),
  NonemptyInterval.mk (3, 3) (by grind)].map toLex |>.mergeSort.map (·.toProd)

end LELT

/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : Preorder (Lex (NonemptyInterval α)) := fast_instance%
  Preorder.lift fun x => toLex (ofLex x).toDualProd
/-
**NonemptyInterval.toLex_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：toLex_mono [PartialOrder α] : Monotone (toLex : NonemptyInterval α -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Prod.Lex.toLex_mono`：toLex_mono : Monotone (toLex : α × β -> α ×ₗ β)
· 使用定理 `NonemptyInterval.toDualProd_mono`：toDualProd_mono : Monotone (toDualProd
 : _ -> αᵒᵈ × α)
-/
theorem toLex_mono [PartialOrder α] : Monotone (toLex : NonemptyInterval α → _) :=
  Prod.Lex.toLex_mono.comp toDualProd_mono
/-
**NonemptyInterval.toLex_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`
。
形式化陈述：toLex_strictMono [PartialOrder α] : StrictMono (toLex : NonemptyInterval α
 -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `Prod.Lex.toLex_strictMono`：toLex_strictMono : StrictMono (toLex : α × β 
-> α ×ₗ β)
· 使用定理 `NonemptyInterval.toDualProd_strictMono`：toDualProd_strictMono : StrictMo
no (toDualProd : _ -> αᵒᵈ × α)
-/
theorem toLex_strictMono [PartialOrder α] : StrictMono (toLex : NonemptyInterval α → _) :=
  Prod.Lex.toLex_strictMono.comp toDualProd_strictMono
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder α] : PartialOrder (Lex (NonemptyInterval α)) := fast_instance%
  PartialOrder.lift (fun x => toLex (ofLex x).toDualProd) <|
    toLex.injective.comp <| toDualProd_injective.comp ofLex.injective
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder α] : LinearOrder (Lex (NonemptyInterval α)) := fast_instance%
  { LinearOrder.lift' (fun x : Lex (NonemptyInterval α) => toLex (ofLex x).toDualProd) <|
      toLex.injective.comp <| toDualProd_injective.comp ofLex.injective with
    toDecidableEq := inferInstance
    toDecidableLT := inferInstance
    toDecidableLE := inferInstance }

end NonemptyInterval

