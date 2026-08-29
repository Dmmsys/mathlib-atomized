/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.Max
public import Mathlib.Order.ULift
public import Mathlib.Tactic.ByCases
public import Mathlib.Tactic.Finiteness.Attr

/-!
# ⊤ and ⊥, bounded lattices and variants

This file defines top and bottom elements (greatest and least elements) of a type, the bounded
variants of different kinds of lattices, sets up the typeclass hierarchy between them and provides
instances for `Prop` and `fun`.

## Main declarations

* `<Top/Bot> α`: Typeclasses to declare the `⊤`/`⊥` notation.
* `Order<Top/Bot> α`: Order with a top/bottom element.
* `BoundedOrder α`: Order with a top and bottom element.

-/

@[expose] public section

assert_not_exists Monotone

universe u v

variable {α : Type u} {β : Type v}

/-! ### Top, bottom element -/

/--
Definition of `OrderTop` / `OrderTop` 的定义

English:
class OrderTop
  parameters: (α : Type u) [LE α]
  extends: Top α
  axioms and operations (1):
    - le_top : forall a : α, a <= ⊤

中文:
类 有顶序
  参数: (α : 类型u) [LE α]
  继承: 顶元素 α
  公理与运算 (1 个):
    - le_top : 对任意 a : α, a <= ⊤
-/
class OrderTop (α : Type u) [LE α] extends Top α where
  /-- `⊤` is the greatest element -/
  le_top : forall a : α, a <= ⊤

/--
Definition of `OrderBot` / `OrderBot` 的定义

English:
class OrderBot
  parameters: (α : Type u) [LE α]
  extends: Bot α
  axioms and operations (1):
    - bot_le : forall a : α, ⊥ <= a

中文:
类 有底序
  参数: (α : 类型u) [LE α]
  继承: 底元素 α
  公理与运算 (1 个):
    - bot_le : 对任意 a : α, ⊥ <= a
-/
@[to_dual] class OrderBot (α : Type u) [LE α] extends Bot α where
  /-- `⊥` is the least element -/
  bot_le : forall a : α, ⊥ <= a

section OrderTop

/-- An order is (noncomputably) either an `OrderTop` or a `NoTopOrder`. Use as
`cases topOrderOrNoTopOrder α`. -/
@[to_dual /-- An order is (noncomputably) either an `OrderBot` or a `NoBotOrder`. Use as
`cases botOrderOrNoBotOrder α`. -/]
/--
Definition of `topOrderOrNoTopOrder` / `topOrderOrNoTopOrder` 的定义

English:
definition topOrderOrNoTopOrder
  signature: (α : Type*) [LE α]
  body: by
  by_cases! H : forall a : α, exists b, ¬b <= a
  · exact PSum.inr ⟨H⟩
  · letI : Top α := ⟨Classical.choose H⟩
    exact PSum.inl ⟨Classical.choose_spec H⟩

中文:
定义 topOrderOrNoTopOrder
  签名: (α : 类型) [LE α]
  定义体: by
  by_cases! H : forall a : α, exists b, ¬b <= a
  · exact PSum.inr ⟨H⟩
  · letI : Top α := ⟨Classical.choose H⟩
    exact PSum.inl ⟨Classical.choose_spec H⟩

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, PSum.inl, PSum.inr, choose_spec
-/
noncomputable def topOrderOrNoTopOrder (α : Type*) [LE α] : OrderTop α oplus' NoTopOrder α := by
  by_cases! H : forall a : α, exists b, ¬b <= a
  · exact PSum.inr ⟨H⟩
  · letI : Top α := ⟨Classical.choose H⟩
    exact PSum.inl ⟨Classical.choose_spec H⟩

section ite

variable [Top α] {p : Prop} [Decidable p]

@[to_dual (attr := aesop (rule_sets := [finiteness]) unsafe 70% apply)]
/--
theorem `dite_ne_top` / 定理 `dite_ne_top`

English:
theorem dite_ne_top
  given: {a : p -> α} {b : ¬p -> α} (ha : forall h, a h != ⊤) (hb : forall h, b h != ⊤)
  proof: by
  split <;> solve_by_elim

@[to_dual (attr := aesop (rule_sets := [finiteness]) unsafe 70% apply)]

中文:
定理 dite_ne_top
  条件: {a : p -> α} {b : ¬p -> α} (ha : 对任意 h, a h != ⊤) (hb : 对任意 h, b h != ⊤)
  证明: by
  split <;> solve_by_elim

@[to_dual (attr := aesop (rule_sets := [finiteness]) unsafe 70% apply)]

Depends on / 依赖: solve_by_elim
-/
theorem dite_ne_top {a : p -> α} {b : ¬p -> α} (ha : forall h, a h != ⊤) (hb : forall h, b h != ⊤) :
    (if h : p then a h else b h) != ⊤ := by
  split <;> solve_by_elim

@[to_dual (attr := aesop (rule_sets := [finiteness]) unsafe 70% apply)]
/--
theorem `ite_ne_top` / 定理 `ite_ne_top`

English:
theorem ite_ne_top
  given: {a b : α} (ha : p -> a != ⊤) (hb : ¬p -> b != ⊤)
  proof: dite_ne_top ha hb

中文:
定理 ite_ne_top
  条件: {a b : α} (ha : p -> a != ⊤) (hb : ¬p -> b != ⊤)
  证明: dite_ne_top ha hb

Depends on / 依赖: dite_ne_top
-/
theorem ite_ne_top {a b : α} (ha : p -> a != ⊤) (hb : ¬p -> b != ⊤) :
    (if p then a else b) != ⊤ :=
  dite_ne_top ha hb

end ite

section LE

variable [LE α] [OrderTop α] {a : α}

@[to_dual (attr := simp) bot_le]
/--
theorem `le_top` / 定理 `le_top`

English:
theorem le_top
  statement: a <= ⊤
  proof: OrderTop.le_top a

@[to_dual (attr := simp)]

中文:
定理 le_top
  结论: a <= ⊤
  证明: OrderTop.le_top a

@[to_dual (attr := simp)]

Depends on / 依赖: OrderTop, OrderTop.le_top, le_top
-/
theorem le_top : a <= ⊤ :=
  OrderTop.le_top a

@[to_dual (attr := simp)]
/--
theorem `isTop_top` / 定理 `isTop_top`

English:
theorem isTop_top
  statement: IsTop (⊤ : α)
  proof: fun _ => le_top

中文:
定理 isTop_top
  结论: IsTop (⊤ : α)
  证明: fun _ => le_top

Depends on / 依赖: le_top
-/
theorem isTop_top : IsTop (⊤ : α) := fun _ => le_top

end LE

/-- A top element can be replaced with `⊤`.

Prefer `IsTop.eq_top` if `α` already has a top element. -/
@[to_dual (attr := elab_as_elim) /-- A bottom element can be replaced with `⊥`.

Prefer `IsBot.eq_bot` if `α` already has a bottom element. -/]
/--
Definition of `IsTop.rec` / `IsTop.rec` 的定义

English:
definition IsTop.rec
  signature: [LE α] {motive : (x : α) -> IsTop x -> Sort*}
  body: @top { top := x, le_top a := hx a }

中文:
定义 IsTop.rec
  签名: [LE α] {motive : (x : α) -> IsTop x -> 类型层*}
  定义体: @top { top := x, le_top a := hx a }
-/
protected def IsTop.rec [LE α] {motive : (x : α) -> IsTop x -> Sort*}
    (top : forall [OrderTop α], motive ⊤ isTop_top) (x : α) (hx : IsTop x) : motive x hx :=
  @top { top := x, le_top a := hx a }

section Preorder

variable [Preorder α] [OrderTop α] {a b : α}

@[to_dual (attr := simp)]
/--
theorem `isMax_top` / 定理 `isMax_top`

English:
theorem isMax_top
  statement: IsMax (⊤ : α)
  proof: isTop_top.isMax

@[to_dual (attr := simp) not_lt_bot]

中文:
定理 isMax_top
  结论: IsMax (⊤ : α)
  证明: isTop_top.isMax

@[to_dual (attr := simp) not_lt_bot]

Depends on / 依赖: isTop_top, isTop_top.isMax
-/
theorem isMax_top : IsMax (⊤ : α) :=
  isTop_top.isMax

@[to_dual (attr := simp) not_lt_bot]
/--
theorem `not_top_lt` / 定理 `not_top_lt`

English:
theorem not_top_lt
  statement: ¬⊤ < a
  proof: isMax_top.not_lt

@[to_dual (attr := simp) not_covBy_bot]

中文:
定理 not_top_lt
  结论: ¬⊤ < a
  证明: isMax_top.not_lt

@[to_dual (attr := simp) not_covBy_bot]

Depends on / 依赖: isMax_top, isMax_top.not_lt, not_lt
-/
theorem not_top_lt : ¬⊤ < a :=
  isMax_top.not_lt

@[to_dual (attr := simp) not_covBy_bot]
/--
theorem `not_top_covBy` / 定理 `not_top_covBy`

English:
theorem not_top_covBy
  statement: ¬⊤ ⋖ a
  proof: fun h => not_top_lt h.1

@[to_dual ne_bot_of_gt]

中文:
定理 not_top_covBy
  结论: ¬⊤ ⋖ a
  证明: fun h => not_top_lt h.1

@[to_dual ne_bot_of_gt]

Depends on / 依赖: not_top_lt
-/
theorem not_top_covBy : ¬⊤ ⋖ a :=
  fun h => not_top_lt h.1

@[to_dual ne_bot_of_gt]
/--
theorem `ne_top_of_lt` / 定理 `ne_top_of_lt`

English:
theorem ne_top_of_lt
  given: (h : a < b)
  statement: a != ⊤
  proof: (h.trans_le le_top).ne

@[to_dual] alias LT.lt.ne_top := ne_top_of_lt

中文:
定理 ne_top_of_lt
  条件: (h : a < b)
  结论: a != ⊤
  证明: (h.trans_le le_top).ne

@[to_dual] alias LT.lt.ne_top := ne_top_of_lt

Depends on / 依赖: h.trans_le, le_top, trans_le
-/
theorem ne_top_of_lt (h : a < b) : a != ⊤ :=
  (h.trans_le le_top).ne

@[to_dual] alias LT.lt.ne_top := ne_top_of_lt

/--
theorem `lt_top_of_lt` / 定理 `lt_top_of_lt`

English:
theorem lt_top_of_lt
  given: (h : a < b)
  statement: a < ⊤
  proof: lt_of_lt_of_le h le_top

@[to_dual bot_lt] alias LT.lt.lt_top := lt_top_of_lt

@[to_dual bot_lt_iff_not_le_bot]

中文:
定理 lt_top_of_lt
  条件: (h : a < b)
  结论: a < ⊤
  证明: lt_of_lt_of_le h le_top

@[to_dual bot_lt] alias LT.lt.lt_top := lt_top_of_lt

@[to_dual bot_lt_iff_not_le_bot]
-/
@[to_dual bot_lt_of_lt] theorem lt_top_of_lt (h : a < b) : a < ⊤ :=
  lt_of_lt_of_le h le_top

@[to_dual bot_lt] alias LT.lt.lt_top := lt_top_of_lt

@[to_dual bot_lt_iff_not_le_bot]
/--
theorem `lt_top_iff_not_top_le` / 定理 `lt_top_iff_not_top_le`

English:
theorem lt_top_iff_not_top_le
  statement: a < ⊤ ↔ ¬ ⊤ <= a
  proof: by
  simp [lt_iff_le_not_ge]

@[to_dual not_isMin_iff_bot_lt]

中文:
定理 lt_top_iff_not_top_le
  结论: a < ⊤ ↔ ¬ ⊤ <= a
  证明: by
  simp [lt_iff_le_not_ge]

@[to_dual not_isMin_iff_bot_lt]

Depends on / 依赖: lt_iff_le_not_ge
-/
theorem lt_top_iff_not_top_le : a < ⊤ ↔ ¬ ⊤ <= a := by
  simp [lt_iff_le_not_ge]

@[to_dual not_isMin_iff_bot_lt]
/--
theorem `not_isMax_iff_lt_top` / 定理 `not_isMax_iff_lt_top`

English:
theorem not_isMax_iff_lt_top
  statement: ¬ IsMax a ↔ a < ⊤
  proof: by
  rw [not_isMax_iff]
  exact ⟨fun ⟨b, hb⟩ => hb.trans_le le_top, fun h => ⟨⊤, h⟩⟩

中文:
定理 not_isMax_iff_lt_top
  结论: ¬ IsMax a ↔ a < ⊤
  证明: by
  rw [not_isMax_iff]
  exact ⟨fun ⟨b, hb⟩ => hb.trans_le le_top, fun h => ⟨⊤, h⟩⟩

Depends on / 依赖: hb.trans_le, le_top, not_isMax_iff, trans_le
-/
theorem not_isMax_iff_lt_top : ¬ IsMax a ↔ a < ⊤ := by
  rw [not_isMax_iff]
  exact ⟨fun ⟨b, hb⟩ => hb.trans_le le_top, fun h => ⟨⊤, h⟩⟩

attribute [aesop (rule_sets := [finiteness]) unsafe 20%] ne_top_of_lt
-- would have been better to implement this as a "safe" "forward" rule, why doesn't this work?
-- attribute [aesop (rule_sets := [finiteness]) safe forward] ne_top_of_lt

end Preorder

variable [PartialOrder α] [OrderTop α] [Preorder β] {a b : α}

@[to_dual (attr := simp)]
/--
theorem `isMax_iff_eq_top` / 定理 `isMax_iff_eq_top`

English:
theorem isMax_iff_eq_top
  statement: IsMax a ↔ a = ⊤
  proof: ⟨fun h => h.eq_of_le le_top, fun h _ _ => h.symm ▸ le_top⟩

@[to_dual (attr := simp)]

中文:
定理 isMax_iff_eq_top
  结论: IsMax a ↔ a = ⊤
  证明: ⟨fun h => h.eq_of_le le_top, fun h _ _ => h.symm ▸ le_top⟩

@[to_dual (attr := simp)]

Depends on / 依赖: eq_of_le, h.eq_of_le, h.symm, le_top
-/
theorem isMax_iff_eq_top : IsMax a ↔ a = ⊤ :=
  ⟨fun h => h.eq_of_le le_top, fun h _ _ => h.symm ▸ le_top⟩

@[to_dual (attr := simp)]
/--
theorem `isTop_iff_eq_top` / 定理 `isTop_iff_eq_top`

English:
theorem isTop_iff_eq_top
  statement: IsTop a ↔ a = ⊤
  proof: ⟨fun h => h.isMax.eq_of_le le_top, fun h _ => h.symm ▸ le_top⟩

@[to_dual]

中文:
定理 isTop_iff_eq_top
  结论: IsTop a ↔ a = ⊤
  证明: ⟨fun h => h.isMax.eq_of_le le_top, fun h _ => h.symm ▸ le_top⟩

@[to_dual]

Depends on / 依赖: eq_of_le, h.isMax.eq_of_le, h.symm, le_top
-/
theorem isTop_iff_eq_top : IsTop a ↔ a = ⊤ :=
  ⟨fun h => h.isMax.eq_of_le le_top, fun h _ => h.symm ▸ le_top⟩

@[to_dual]
/--
theorem `not_isMax_iff_ne_top` / 定理 `not_isMax_iff_ne_top`

English:
theorem not_isMax_iff_ne_top
  statement: ¬IsMax a ↔ a != ⊤
  proof: isMax_iff_eq_top.not

@[to_dual]

中文:
定理 not_isMax_iff_ne_top
  结论: ¬IsMax a ↔ a != ⊤
  证明: isMax_iff_eq_top.not

@[to_dual]

Depends on / 依赖: isMax_iff_eq_top, isMax_iff_eq_top.not
-/
theorem not_isMax_iff_ne_top : ¬IsMax a ↔ a != ⊤ :=
  isMax_iff_eq_top.not

@[to_dual]
/--
theorem `not_isTop_iff_ne_top` / 定理 `not_isTop_iff_ne_top`

English:
theorem not_isTop_iff_ne_top
  statement: ¬IsTop a ↔ a != ⊤
  proof: isTop_iff_eq_top.not

@[to_dual]
alias ⟨IsMax.eq_top, _⟩ := isMax_iff_eq_top

@[to_dual]
alias ⟨IsTop.eq_top, _⟩ := isTop_iff_eq_top

@[to_dual (attr := simp) le_bot_iff]

中文:
定理 not_isTop_iff_ne_top
  结论: ¬IsTop a ↔ a != ⊤
  证明: isTop_iff_eq_top.not

@[to_dual]
alias ⟨IsMax.eq_top, _⟩ := isMax_iff_eq_top

@[to_dual]
alias ⟨IsTop.eq_top, _⟩ := isTop_iff_eq_top

@[to_dual (attr := simp) le_bot_iff]

Depends on / 依赖: isTop_iff_eq_top, isTop_iff_eq_top.not
-/
theorem not_isTop_iff_ne_top : ¬IsTop a ↔ a != ⊤ :=
  isTop_iff_eq_top.not

@[to_dual]
alias ⟨IsMax.eq_top, _⟩ := isMax_iff_eq_top

@[to_dual]
alias ⟨IsTop.eq_top, _⟩ := isTop_iff_eq_top

@[to_dual (attr := simp) le_bot_iff]
/--
theorem `top_le_iff` / 定理 `top_le_iff`

English:
theorem top_le_iff
  statement: ⊤ <= a ↔ a = ⊤
  proof: le_top.ge_iff_eq

中文:
定理 top_le_iff
  结论: ⊤ <= a ↔ a = ⊤
  证明: le_top.ge_iff_eq

Depends on / 依赖: ge_iff_eq, le_top, le_top.ge_iff_eq
-/
theorem top_le_iff : ⊤ <= a ↔ a = ⊤ :=
  le_top.ge_iff_eq

-- This tells grind that to prove `a = ⊤` it suffices to prove `⊤ ≤ a`.
@[to_dual (attr := grind ←=, grind ->)]
/--
theorem `top_unique` / 定理 `top_unique`

English:
theorem top_unique
  given: (h : ⊤ <= a)
  statement: a = ⊤
  proof: le_top.antisymm h

@[to_dual]

中文:
定理 top_unique
  条件: (h : ⊤ <= a)
  结论: a = ⊤
  证明: le_top.antisymm h

@[to_dual]

Depends on / 依赖: antisymm, le_top, le_top.antisymm
-/
theorem top_unique (h : ⊤ <= a) : a = ⊤ :=
  le_top.antisymm h

@[to_dual]
/--
theorem `eq_top_iff` / 定理 `eq_top_iff`

English:
theorem eq_top_iff
  statement: a = ⊤ ↔ ⊤ <= a
  proof: top_le_iff.symm

@[to_dual]

中文:
定理 eq_top_iff
  结论: a = ⊤ ↔ ⊤ <= a
  证明: top_le_iff.symm

@[to_dual]

Depends on / 依赖: top_le_iff, top_le_iff.symm
-/
theorem eq_top_iff : a = ⊤ ↔ ⊤ <= a :=
  top_le_iff.symm

@[to_dual]
/--
theorem `eq_top_mono` / 定理 `eq_top_mono`

English:
theorem eq_top_mono
  given: (h : a <= b) (h₂ : a = ⊤)
  statement: b = ⊤
  proof: top_unique h₂ ▸ h

@[to_dual bot_lt_iff_ne_bot]

中文:
定理 eq_top_mono
  条件: (h : a <= b) (h₂ : a = ⊤)
  结论: b = ⊤
  证明: top_unique h₂ ▸ h

@[to_dual bot_lt_iff_ne_bot]

Depends on / 依赖: top_unique
-/
theorem eq_top_mono (h : a <= b) (h₂ : a = ⊤) : b = ⊤ :=
top_unique h₂ ▸ h

@[to_dual bot_lt_iff_ne_bot]
/--
theorem `lt_top_iff_ne_top` / 定理 `lt_top_iff_ne_top`

English:
theorem lt_top_iff_ne_top
  statement: a < ⊤ ↔ a != ⊤
  proof: le_top.lt_iff_ne

@[to_dual (attr := simp) not_bot_lt_iff]

中文:
定理 lt_top_iff_ne_top
  结论: a < ⊤ ↔ a != ⊤
  证明: le_top.lt_iff_ne

@[to_dual (attr := simp) not_bot_lt_iff]

Depends on / 依赖: le_top, le_top.lt_iff_ne, lt_iff_ne
-/
theorem lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤ :=
  le_top.lt_iff_ne

@[to_dual (attr := simp) not_bot_lt_iff]
/--
theorem `not_lt_top_iff` / 定理 `not_lt_top_iff`

English:
theorem not_lt_top_iff
  statement: ¬a < ⊤ ↔ a = ⊤
  proof: lt_top_iff_ne_top.not_left

@[to_dual eq_bot_or_bot_lt]

中文:
定理 not_lt_top_iff
  结论: ¬a < ⊤ ↔ a = ⊤
  证明: lt_top_iff_ne_top.not_left

@[to_dual eq_bot_or_bot_lt]

Depends on / 依赖: lt_top_iff_ne_top, lt_top_iff_ne_top.not_left, not_left
-/
theorem not_lt_top_iff : ¬a < ⊤ ↔ a = ⊤ :=
  lt_top_iff_ne_top.not_left

@[to_dual eq_bot_or_bot_lt]
/--
theorem `eq_top_or_lt_top` / 定理 `eq_top_or_lt_top`

English:
theorem eq_top_or_lt_top
  given: (a : α)
  statement: a = ⊤ ∨ a < ⊤
  proof: le_top.eq_or_lt

@[aesop (rule_sets := [finiteness]) safe apply, to_dual bot_lt]

中文:
定理 eq_top_or_lt_top
  条件: (a : α)
  结论: a = ⊤ ∨ a < ⊤
  证明: le_top.eq_or_lt

@[aesop (rule_sets := [finiteness]) safe apply, to_dual bot_lt]

Depends on / 依赖: eq_or_lt, le_top, le_top.eq_or_lt
-/
theorem eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤ :=
  le_top.eq_or_lt

@[aesop (rule_sets := [finiteness]) safe apply, to_dual bot_lt]
/--
theorem `Ne.lt_top` / 定理 `Ne.lt_top`

English:
theorem Ne.lt_top
  given: (h : a != ⊤)
  statement: a < ⊤
  proof: lt_top_iff_ne_top.mpr h

@[to_dual bot_lt']

中文:
定理 不等.lt_top
  条件: (h : a != ⊤)
  结论: a < ⊤
  证明: lt_top_iff_ne_top.mpr h

@[to_dual bot_lt']

Depends on / 依赖: lt_top_iff_ne_top, lt_top_iff_ne_top.mpr
-/
theorem Ne.lt_top (h : a != ⊤) : a < ⊤ :=
  lt_top_iff_ne_top.mpr h

@[to_dual bot_lt']
/--
theorem `Ne.lt_top'` / 定理 `Ne.lt_top'`

English:
theorem Ne.lt_top'
  given: (h : ⊤ != a)
  statement: a < ⊤
  proof: h.symm.lt_top

@[to_dual]

中文:
定理 不等.lt_top'
  条件: (h : ⊤ != a)
  结论: a < ⊤
  证明: h.symm.lt_top

@[to_dual]

Depends on / 依赖: h.symm.lt_top, lt_top
-/
theorem Ne.lt_top' (h : ⊤ != a) : a < ⊤ :=
  h.symm.lt_top

@[to_dual]
/--
theorem `ne_top_of_le_ne_top` / 定理 `ne_top_of_le_ne_top`

English:
theorem ne_top_of_le_ne_top
  given: (hb : b != ⊤) (hab : a <= b)
  statement: a != ⊤
  proof: (hab.trans_lt hb.lt_top).ne

@[to_dual]

中文:
定理 ne_top_of_le_ne_top
  条件: (hb : b != ⊤) (hab : a <= b)
  结论: a != ⊤
  证明: (hab.trans_lt hb.lt_top).ne

@[to_dual]

Depends on / 依赖: hab.trans_lt, hb.lt_top, lt_top, trans_lt
-/
theorem ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : a != ⊤ :=
  (hab.trans_lt hb.lt_top).ne

@[to_dual]
/--
lemma `top_notMem_iff` / 引理 `top_notMem_iff`

English:
lemma top_notMem_iff
  given: {s : Set α}
  statement: ⊤ ∉ s ↔ forall x in s, x < ⊤
  proof: ⟨fun h x hx => Ne.lt_top (fun hx' : x = ⊤ => h (hx' ▸ hx)), fun h h₀ => (h ⊤ h₀).false⟩

中文:
引理 top_notMem_iff
  条件: {s : 集合 α}
  结论: ⊤ ∉ s ↔ 对任意 x in s, x < ⊤
  证明: ⟨fun h x hx => Ne.lt_top (fun hx' : x = ⊤ => h (hx' ▸ hx)), fun h h₀ => (h ⊤ h₀).false⟩

Depends on / 依赖: Ne.lt_top, lt_top
-/
lemma top_notMem_iff {s : Set α} : ⊤ ∉ s ↔ forall x in s, x < ⊤ :=
  ⟨fun h x hx => Ne.lt_top (fun hx' : x = ⊤ => h (hx' ▸ hx)), fun h h₀ => (h ⊤ h₀).false⟩

variable [Nontrivial α]

@[to_dual]
/--
theorem `not_isMin_top` / 定理 `not_isMin_top`

English:
theorem not_isMin_top
  statement: ¬IsMin (⊤ : α)
  proof: fun h =>
  let ⟨_, ha⟩ := exists_ne (⊤ : α)
ha top_le_iff.1 h le_top

中文:
定理 not_isMin_top
  结论: ¬IsMin (⊤ : α)
  证明: fun h =>
  let ⟨_, ha⟩ := exists_ne (⊤ : α)
ha top_le_iff.1 h le_top
-/
theorem not_isMin_top : ¬IsMin (⊤ : α) := fun h =>
  let ⟨_, ha⟩ := exists_ne (⊤ : α)
ha top_le_iff.1 h le_top

end OrderTop

@[to_dual (reorder := H (x y))]
/--
theorem `OrderTop.ext_top` / 定理 `OrderTop.ext_top`

English:
theorem OrderTop.ext_top
  statement: {α} {hA : PartialOrder α} (A : OrderTop α) {hB : PartialOrder α}
  proof: by
  cases PartialOrder.ext H
  apply top_unique
  exact @le_top _ _ A _

中文:
定理 有顶序.ext_top
  结论: {α} {hA : 偏序 α} (A : 有顶序 α) {hB : 偏序 α}
  证明: by
  cases PartialOrder.ext H
  apply top_unique
  exact @le_top _ _ A _
-/
theorem OrderTop.ext_top {α} {hA : PartialOrder α} (A : OrderTop α) {hB : PartialOrder α}
    (B : OrderTop α) (H : forall x y : α, (haveI := hA; x <= y) ↔ x <= y) :
    (@Top.top α (@OrderTop.toTop α hA.toLE A)) = (@Top.top α (@OrderTop.toTop α hB.toLE B)) := by
  cases PartialOrder.ext H
  apply top_unique
  exact @le_top _ _ A _

namespace OrderDual

variable (α)

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : Bot α] : Top αᵒᵈ
  body: ⟨h.bot⟩

@[to_dual]

中文:
实例 [h
  签名: : 底元素 α] : 顶元素 αᵒᵈ
  定义体: ⟨h.bot⟩

@[to_dual]

Depends on / 依赖: h.bot
-/
instance [h : Bot α] : Top αᵒᵈ :=
  ⟨h.bot⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: α] [h
  body: h.bot_le

中文:
实例 [LE
  签名: α] [h
  定义体: h.bot_le

Depends on / 依赖: bot_le, h.bot_le
-/
instance [LE α] [h : OrderBot α] : OrderTop αᵒᵈ where
  le_top := h.bot_le

/--
lemma `ofDual_top` / 引理 `ofDual_top`

English:
lemma ofDual_top
  given: [Bot α]
  statement: ofDual ⊤ = (⊥ : α)
  proof: rfl

中文:
引理 ofDual_top
  条件: [底元素 α]
  结论: ofDual ⊤ = (⊥ : α)
  证明: rfl
-/
@[to_dual (attr := simp)] lemma ofDual_top [Bot α] : ofDual ⊤ = (⊥ : α) := rfl
/--
lemma `toDual_top` / 引理 `toDual_top`

English:
lemma toDual_top
  given: [Top α]
  statement: toDual (⊤ : α) = ⊥
  proof: rfl

中文:
引理 toDual_top
  条件: [顶元素 α]
  结论: toDual (⊤ : α) = ⊥
  证明: rfl
-/
@[to_dual (attr := simp)] lemma toDual_top [Top α] : toDual (⊤ : α) = ⊥ := rfl

/--
lemma `ofDual_eq_top` / 引理 `ofDual_eq_top`

English:
lemma ofDual_eq_top
  given: [Top α] {a : αᵒᵈ}
  statement: ofDual a = ⊤ ↔ a = ⊥
  proof: .rfl

中文:
引理 ofDual_eq_top
  条件: [顶元素 α] {a : αᵒᵈ}
  结论: ofDual a = ⊤ ↔ a = ⊥
  证明: .rfl
-/
@[to_dual (attr := simp)] lemma ofDual_eq_top [Top α] {a : αᵒᵈ} : ofDual a = ⊤ ↔ a = ⊥ := .rfl
/--
lemma `toDual_eq_top` / 引理 `toDual_eq_top`

English:
lemma toDual_eq_top
  given: [Bot α] {a : α}
  statement: toDual a = ⊤ ↔ a = ⊥
  proof: .rfl

中文:
引理 toDual_eq_top
  条件: [底元素 α] {a : α}
  结论: toDual a = ⊤ ↔ a = ⊥
  证明: .rfl
-/
@[to_dual (attr := simp)] lemma toDual_eq_top [Bot α] {a : α} : toDual a = ⊤ ↔ a = ⊥ := .rfl

end OrderDual


/-! ### Bounded order -/


/--
Definition of `BoundedOrder` / `BoundedOrder` 的定义

English:
class BoundedOrder
  parameters: (α : Type u) [LE α]
  extends: OrderTop α, OrderBot α
  (no additional axioms)

中文:
类 有界序
  参数: (α : 类型u) [LE α]
  继承: 有顶序 α, 有底序 α
  (无附加公理)

Depends on / 依赖: BoundedOrder, BoundedOrder.mk
-/
class BoundedOrder (α : Type u) [LE α] extends OrderTop α, OrderBot α

attribute [to_dual self (reorder := 3 4)] BoundedOrder.mk
attribute [to_dual existing] BoundedOrder.toOrderTop

/--
Instance `OrderDual.instBoundedOrder` / 实例 `OrderDual.instBoundedOrder`

English:
instance OrderDual.instBoundedOrder
  signature: (α : Type u) [LE α] [BoundedOrder α]

中文:
实例 OrderDual.instBoundedOrder
  签名: (α : 类型u) [LE α] [有界序 α]
-/
instance OrderDual.instBoundedOrder (α : Type u) [LE α] [BoundedOrder α] : BoundedOrder αᵒᵈ where

section PartialOrder
variable [PartialOrder α]

@[to_dual]
/--
Instance `OrderBot.instSubsingleton` / 实例 `OrderBot.instSubsingleton`

English:
instance OrderBot.instSubsingleton
  signature: : Subsingleton (OrderBot α) where
  body: by rintro @⟨⟨a⟩, ha⟩ @⟨⟨b⟩, hb⟩; congr; exact le_antisymm (ha _) (hb _)

中文:
实例 有底序.instSubsingleton
  签名: : 子单例 (有底序 α) where
  定义体: by rintro @⟨⟨a⟩, ha⟩ @⟨⟨b⟩, hb⟩; congr; exact le_antisymm (ha _) (hb _)

Depends on / 依赖: le_antisymm
-/
instance OrderBot.instSubsingleton : Subsingleton (OrderBot α) where
  allEq := by rintro @⟨⟨a⟩, ha⟩ @⟨⟨b⟩, hb⟩; congr; exact le_antisymm (ha _) (hb _)

/--
Instance `BoundedOrder.instSubsingleton` / 实例 `BoundedOrder.instSubsingleton`

English:
instance BoundedOrder.instSubsingleton
  signature: : Subsingleton (BoundedOrder α) where
  body: by rintro ⟨⟩ ⟨⟩; congr <;> exact Subsingleton.elim _ _

中文:
实例 有界序.instSubsingleton
  签名: : 子单例 (有界序 α) where
  定义体: by rintro ⟨⟩ ⟨⟩; congr <;> exact Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
instance BoundedOrder.instSubsingleton : Subsingleton (BoundedOrder α) where
  allEq := by rintro ⟨⟩ ⟨⟩; congr <;> exact Subsingleton.elim _ _

end PartialOrder

/-! ### Function lattices -/

namespace Pi

variable {ι : Type*} {α' : ι -> Type*}

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Bot (α' i)] : Bot (forall i, α' i)
  body: ⟨fun _ => ⊥⟩

@[to_dual (attr := simp)]

中文:
实例 [对任意
  签名: i, 底元素 (α' i)] : 底元素 (对任意 i, α' i)
  定义体: ⟨fun _ => ⊥⟩

@[to_dual (attr := simp)]
-/
instance [forall i, Bot (α' i)] : Bot (forall i, α' i) :=
  ⟨fun _ => ⊥⟩

@[to_dual (attr := simp)]
/--
theorem `bot_apply` / 定理 `bot_apply`

English:
theorem bot_apply
  given: [forall i, Bot (α' i)] (i : ι)
  statement: (⊥ : forall i, α' i) i = ⊥
  proof: rfl

@[to_dual (attr := push ←)]

中文:
定理 bot_apply
  条件: [对任意 i, 底元素 (α' i)] (i : ι)
  结论: (⊥ : 对任意 i, α' i) i = ⊥
  证明: rfl

@[to_dual (attr := push ←)]
-/
theorem bot_apply [forall i, Bot (α' i)] (i : ι) : (⊥ : forall i, α' i) i = ⊥ :=
  rfl

@[to_dual (attr := push ←)]
/--
theorem `bot_def` / 定理 `bot_def`

English:
theorem bot_def
  given: [forall i, Bot (α' i)]
  statement: (⊥ : forall i, α' i) = fun _ => ⊥
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 bot_def
  条件: [对任意 i, 底元素 (α' i)]
  结论: (⊥ : 对任意 i, α' i) = fun _ => ⊥
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem bot_def [forall i, Bot (α' i)] : (⊥ : forall i, α' i) = fun _ => ⊥ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `bot_comp` / 定理 `bot_comp`

English:
theorem bot_comp
  given: {α β γ : Type*} [Bot γ] (x : α -> β)
  statement: (⊥ : β -> γ) ∘ x = ⊥
  proof: by
  rfl

@[to_dual]

中文:
定理 bot_comp
  条件: {α β γ : 类型} [底元素 γ] (x : α -> β)
  结论: (⊥ : β -> γ) ∘ x = ⊥
  证明: by
  rfl

@[to_dual]
-/
theorem bot_comp {α β γ : Type*} [Bot γ] (x : α -> β) : (⊥ : β -> γ) ∘ x = ⊥ := by
  rfl

@[to_dual]
/--
Instance `instOrderBot` / 实例 `instOrderBot`

English:
instance instOrderBot
  signature: [forall i, LE (α' i)] [forall i, OrderBot (α' i)]
  body: fun _ => bot_le

中文:
实例 instOrderBot
  签名: [对任意 i, LE (α' i)] [对任意 i, 有底序 (α' i)]
  定义体: fun _ => bot_le

Depends on / 依赖: bot_le
-/
instance instOrderBot [forall i, LE (α' i)] [forall i, OrderBot (α' i)] : OrderBot (forall i, α' i) where
  bot_le _ := fun _ => bot_le

/--
Instance `instBoundedOrder` / 实例 `instBoundedOrder`

English:
instance instBoundedOrder
  signature: [forall i, LE (α' i)] [forall i, BoundedOrder (α' i)]
  body: (inferInstance : OrderTop (forall i, α' i))
  __ := (inferInstance : OrderBot (forall i, α' i))

中文:
实例 instBoundedOrder
  签名: [对任意 i, LE (α' i)] [对任意 i, 有界序 (α' i)]
  定义体: (inferInstance : OrderTop (forall i, α' i))
  __ := (inferInstance : OrderBot (forall i, α' i))

Depends on / 依赖: OrderTop
-/
instance instBoundedOrder [forall i, LE (α' i)] [forall i, BoundedOrder (α' i)] :
    BoundedOrder (forall i, α' i) where
  __ := (inferInstance : OrderTop (forall i, α' i))
  __ := (inferInstance : OrderBot (forall i, α' i))

end Pi

section Subsingleton

/-- A type with a single element is a bounded order. -/
@[implicit_reducible]
/--
Definition of `BoundedOrder.ofUnique` / `BoundedOrder.ofUnique` 的定义

English:
definition BoundedOrder.ofUnique
  signature: (α : Type*) [Preorder α] [Unique α]
  body: default
  top := default
  le_top := by simp
  bot_le := by simp

中文:
定义 有界序.ofUnique
  签名: (α : 类型) [预序 α] [唯一 α]
  定义体: default
  top := default
  le_top := by simp
  bot_le := by simp
-/
def BoundedOrder.ofUnique (α : Type*) [Preorder α] [Unique α] : BoundedOrder α where
  bot := default
  top := default
  le_top := by simp
  bot_le := by simp

variable [PartialOrder α] [BoundedOrder α]

@[to_dual]
/--
theorem `eq_bot_of_bot_eq_top` / 定理 `eq_bot_of_bot_eq_top`

English:
theorem eq_bot_of_bot_eq_top
  given: (hα : (⊥ : α) = ⊤) (x : α)
  statement: x = (⊥ : α)
  proof: eq_bot_mono le_top (Eq.symm hα)

@[to_dual]

中文:
定理 eq_bot_of_bot_eq_top
  条件: (hα : (⊥ : α) = ⊤) (x : α)
  结论: x = (⊥ : α)
  证明: eq_bot_mono le_top (Eq.symm hα)

@[to_dual]

Depends on / 依赖: Eq.symm, eq_bot_mono, le_top
-/
theorem eq_bot_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊥ : α) :=
  eq_bot_mono le_top (Eq.symm hα)

@[to_dual]
/--
theorem `eq_top_of_bot_eq_top` / 定理 `eq_top_of_bot_eq_top`

English:
theorem eq_top_of_bot_eq_top
  given: (hα : (⊥ : α) = ⊤) (x : α)
  statement: x = (⊤ : α)
  proof: eq_top_mono bot_le hα

中文:
定理 eq_top_of_bot_eq_top
  条件: (hα : (⊥ : α) = ⊤) (x : α)
  结论: x = (⊤ : α)
  证明: eq_top_mono bot_le hα

Depends on / 依赖: bot_le, eq_top_mono
-/
theorem eq_top_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊤ : α) :=
  eq_top_mono bot_le hα

/--
theorem `subsingleton_of_top_le_bot` / 定理 `subsingleton_of_top_le_bot`

English:
theorem subsingleton_of_top_le_bot
  given: (h : (⊤ : α) <= (⊥ : α))
  statement: Subsingleton α
  proof: ⟨fun _ _ => le_antisymm
    (le_trans le_top <| le_trans h bot_le) (le_trans le_top <| le_trans h bot_le)⟩

@[to_dual]

中文:
定理 subsingleton_of_top_le_bot
  条件: (h : (⊤ : α) <= (⊥ : α))
  结论: 子单例 α
  证明: ⟨fun _ _ => le_antisymm
    (le_trans le_top <| le_trans h bot_le) (le_trans le_top <| le_trans h bot_le)⟩

@[to_dual]

Depends on / 依赖: bot_le, le_antisymm, le_top, le_trans
-/
theorem subsingleton_of_top_le_bot (h : (⊤ : α) <= (⊥ : α)) : Subsingleton α :=
  ⟨fun _ _ => le_antisymm
    (le_trans le_top <| le_trans h bot_le) (le_trans le_top <| le_trans h bot_le)⟩

@[to_dual]
/--
theorem `subsingleton_of_bot_eq_top` / 定理 `subsingleton_of_bot_eq_top`

English:
theorem subsingleton_of_bot_eq_top
  given: (hα : (⊥ : α) = (⊤ : α))
  statement: Subsingleton α
  proof: subsingleton_of_top_le_bot (ge_of_eq hα)

@[to_dual]

中文:
定理 subsingleton_of_bot_eq_top
  条件: (hα : (⊥ : α) = (⊤ : α))
  结论: 子单例 α
  证明: subsingleton_of_top_le_bot (ge_of_eq hα)

@[to_dual]

Depends on / 依赖: ge_of_eq, subsingleton_of_top_le_bot
-/
theorem subsingleton_of_bot_eq_top (hα : (⊥ : α) = (⊤ : α)) : Subsingleton α :=
  subsingleton_of_top_le_bot (ge_of_eq hα)

@[to_dual]
/--
theorem `subsingleton_iff_bot_eq_top` / 定理 `subsingleton_iff_bot_eq_top`

English:
theorem subsingleton_iff_bot_eq_top
  statement: (⊥ : α) = (⊤ : α) ↔ Subsingleton α
  proof: ⟨subsingleton_of_bot_eq_top, fun _ => Subsingleton.elim ⊥ ⊤⟩

中文:
定理 subsingleton_iff_bot_eq_top
  结论: (⊥ : α) = (⊤ : α) ↔ 子单例 α
  证明: ⟨subsingleton_of_bot_eq_top, fun _ => Subsingleton.elim ⊥ ⊤⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, subsingleton_of_bot_eq_top
-/
theorem subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ : α) ↔ Subsingleton α :=
  ⟨subsingleton_of_bot_eq_top, fun _ => Subsingleton.elim ⊥ ⊤⟩

end Subsingleton

section lift

-- See note [reducible non-instances]
/-- Pullback an `OrderTop`. -/
@[to_dual (reorder := map_le (a b)) /-- Pullback an `OrderBot`. -/]
/--
Definition of `OrderTop.lift` / `OrderTop.lift` 的定义

English:
abbreviation OrderTop.lift
  signature: [LE α] [Top α] [LE β] [OrderTop β] (f : α -> β)
  body: ⟨fun a =>
map_le _ _ by
      rw [map_top]
      exact le_top _⟩

中文:
缩写 有顶序.lift
  签名: [LE α] [顶元素 α] [LE β] [有顶序 β] (f : α -> β)
  定义体: ⟨fun a =>
map_le _ _ by
      rw [map_top]
      exact le_top _⟩

Depends on / 依赖: le_top, map_le, map_top
-/
abbrev OrderTop.lift [LE α] [Top α] [LE β] [OrderTop β] (f : α -> β)
    (map_le : forall a b, f a <= f b -> a <= b) (map_top : f ⊤ = ⊤) : OrderTop α :=
  ⟨fun a =>
map_le _ _ by
      rw [map_top]
      exact le_top _⟩

-- See note [reducible non-instances]
/-- Pullback a `BoundedOrder`. -/
@[to_dual self (reorder := 4 5, map_le (a b), map_top map_bot)]
/--
Definition of `BoundedOrder.lift` / `BoundedOrder.lift` 的定义

English:
abbreviation BoundedOrder.lift
  signature: [LE α] [Top α] [Bot α] [LE β] [BoundedOrder β] (f : α -> β)
  body: OrderTop.lift f map_le map_top
  __ := OrderBot.lift f map_le map_bot

中文:
缩写 有界序.lift
  签名: [LE α] [顶元素 α] [底元素 α] [LE β] [有界序 β] (f : α -> β)
  定义体: OrderTop.lift f map_le map_top
  __ := OrderBot.lift f map_le map_bot

Depends on / 依赖: OrderTop, OrderTop.lift, map_le, map_top
-/
abbrev BoundedOrder.lift [LE α] [Top α] [Bot α] [LE β] [BoundedOrder β] (f : α -> β)
    (map_le : forall a b, f a <= f b -> a <= b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
    BoundedOrder α where
  __ := OrderTop.lift f map_le map_top
  __ := OrderBot.lift f map_le map_bot

end lift

/-! ### Subtype, order dual, product lattices -/


namespace Subtype

variable {p : α -> Prop}

-- See note [reducible non-instances]
/-- A subtype remains a `⊥`-order if the property holds at `⊥`. -/
@[to_dual /-- A subtype remains a `⊤`-order if the property holds at `⊤`. -/]
/--
Definition of `orderBot` / `orderBot` 的定义

English:
abbreviation orderBot
  signature: [LE α] [OrderBot α] (hbot : p ⊥)
  body: ⟨⊥, hbot⟩
  bot_le _ := bot_le

中文:
缩写 orderBot
  签名: [LE α] [有底序 α] (hbot : p ⊥)
  定义体: ⟨⊥, hbot⟩
  bot_le _ := bot_le
-/
protected abbrev orderBot [LE α] [OrderBot α] (hbot : p ⊥) : OrderBot { x : α // p x } where
  bot := ⟨⊥, hbot⟩
  bot_le _ := bot_le

-- See note [reducible non-instances]
/-- A subtype remains a bounded order if the property holds at `⊥` and `⊤`. -/
@[to_dual self (reorder := hbot htop)]
/--
Definition of `boundedOrder` / `boundedOrder` 的定义

English:
abbreviation boundedOrder
  signature: [LE α] [BoundedOrder α] (hbot : p ⊥) (htop : p ⊤)
  body: Subtype.orderTop htop
  __ := Subtype.orderBot hbot

中文:
缩写 boundedOrder
  签名: [LE α] [有界序 α] (hbot : p ⊥) (htop : p ⊤)
  定义体: Subtype.orderTop htop
  __ := Subtype.orderBot hbot
-/
protected abbrev boundedOrder [LE α] [BoundedOrder α] (hbot : p ⊥) (htop : p ⊤) :
    BoundedOrder (Subtype p) where
  __ := Subtype.orderTop htop
  __ := Subtype.orderBot hbot

variable [PartialOrder α]

@[to_dual (attr := simp)]
/--
theorem `mk_bot` / 定理 `mk_bot`

English:
theorem mk_bot
  given: [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥)
  statement: mk ⊥ hbot = ⊥
  proof: le_bot_iff.1 coe_le_coe.1 bot_le

@[to_dual]

中文:
定理 mk_bot
  条件: [有底序 α] [有底序 (子类型 p)] (hbot : p ⊥)
  结论: mk ⊥ hbot = ⊥
  证明: le_bot_iff.1 coe_le_coe.1 bot_le

@[to_dual]

Depends on / 依赖: bot_le, coe_le_coe, le_bot_iff
-/
theorem mk_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : mk ⊥ hbot = ⊥ :=
le_bot_iff.1 coe_le_coe.1 bot_le

@[to_dual]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  given: [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥)
  statement: ((⊥ : Subtype p) : α) = ⊥
  proof: congr_arg Subtype.val (mk_bot hbot).symm

@[to_dual (attr := simp)]

中文:
定理 coe_bot
  条件: [有底序 α] [有底序 (子类型 p)] (hbot : p ⊥)
  结论: ((⊥ : 子类型 p) : α) = ⊥
  证明: congr_arg Subtype.val (mk_bot hbot).symm

@[to_dual (attr := simp)]
-/
theorem coe_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : ((⊥ : Subtype p) : α) = ⊥ :=
  congr_arg Subtype.val (mk_bot hbot).symm

@[to_dual (attr := simp)]
/--
theorem `coe_eq_bot_iff` / 定理 `coe_eq_bot_iff`

English:
theorem coe_eq_bot_iff
  given: [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : { x // p x }}
  proof: by
  rw [← coe_bot hbot]; rw [Subtype.ext_iff]

@[to_dual (attr := simp)]

中文:
定理 coe_eq_bot_iff
  条件: [有底序 α] [有底序 (子类型 p)] (hbot : p ⊥) {x : { x // p x }}
  证明: by
  rw [← coe_bot hbot]; rw [Subtype.ext_iff]

@[to_dual (attr := simp)]

Depends on / 依赖: Subtype, Subtype.ext_iff, coe_bot, ext_iff
-/
theorem coe_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : { x // p x }} :
    (x : α) = ⊥ ↔ x = ⊥ := by
  rw [← coe_bot hbot]; rw [Subtype.ext_iff]

@[to_dual (attr := simp)]
/--
theorem `mk_eq_bot_iff` / 定理 `mk_eq_bot_iff`

English:
theorem mk_eq_bot_iff
  given: [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : α} (hx : p x)
  proof: (coe_eq_bot_iff hbot).symm

中文:
定理 mk_eq_bot_iff
  条件: [有底序 α] [有底序 (子类型 p)] (hbot : p ⊥) {x : α} (hx : p x)
  证明: (coe_eq_bot_iff hbot).symm

Depends on / 依赖: coe_eq_bot_iff
-/
theorem mk_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : α} (hx : p x) :
    (⟨x, hx⟩ : Subtype p) = ⊥ ↔ x = ⊥ :=
  (coe_eq_bot_iff hbot).symm

end Subtype

namespace Prod

variable (α β)

@[to_dual]
/--
Instance `instTop` / 实例 `instTop`

English:
instance instTop
  signature: [Top α] [Top β]
  body: ⟨⟨⊤, ⊤⟩⟩

中文:
实例 instTop
  签名: [顶元素 α] [顶元素 β]
  定义体: ⟨⟨⊤, ⊤⟩⟩
-/
instance instTop [Top α] [Top β] : Top (α × β) :=
  ⟨⟨⊤, ⊤⟩⟩

/--
lemma `fst_top` / 引理 `fst_top`

English:
lemma fst_top
  given: [Top α] [Top β]
  statement: (⊤ : α × β).fst = ⊤
  proof: rfl

中文:
引理 fst_top
  条件: [顶元素 α] [顶元素 β]
  结论: (⊤ : α × β).fst = ⊤
  证明: rfl
-/
@[to_dual (attr := simp)] lemma fst_top [Top α] [Top β] : (⊤ : α × β).fst = ⊤ := rfl
/--
lemma `snd_top` / 引理 `snd_top`

English:
lemma snd_top
  given: [Top α] [Top β]
  statement: (⊤ : α × β).snd = ⊤
  proof: rfl

@[to_dual]

中文:
引理 snd_top
  条件: [顶元素 α] [顶元素 β]
  结论: (⊤ : α × β).snd = ⊤
  证明: rfl

@[to_dual]
-/
@[to_dual (attr := simp)] lemma snd_top [Top α] [Top β] : (⊤ : α × β).snd = ⊤ := rfl

@[to_dual]
/--
Instance `instOrderTop` / 实例 `instOrderTop`

English:
instance instOrderTop
  signature: [LE α] [LE β] [OrderTop α] [OrderTop β]
  body: (inferInstance : Top (α × β))
  le_top _ := ⟨le_top, le_top⟩

中文:
实例 instOrderTop
  签名: [LE α] [LE β] [有顶序 α] [有顶序 β]
  定义体: (inferInstance : Top (α × β))
  le_top _ := ⟨le_top, le_top⟩
-/
instance instOrderTop [LE α] [LE β] [OrderTop α] [OrderTop β] : OrderTop (α × β) where
  __ := (inferInstance : Top (α × β))
  le_top _ := ⟨le_top, le_top⟩

/--
Instance `instBoundedOrder` / 实例 `instBoundedOrder`

English:
instance instBoundedOrder
  signature: [LE α] [LE β] [BoundedOrder α] [BoundedOrder β]
  body: (inferInstance : OrderTop (α × β))
  __ := (inferInstance : OrderBot (α × β))

中文:
实例 instBoundedOrder
  签名: [LE α] [LE β] [有界序 α] [有界序 β]
  定义体: (inferInstance : OrderTop (α × β))
  __ := (inferInstance : OrderBot (α × β))

Depends on / 依赖: OrderTop
-/
instance instBoundedOrder [LE α] [LE β] [BoundedOrder α] [BoundedOrder β] :
    BoundedOrder (α × β) where
  __ := (inferInstance : OrderTop (α × β))
  __ := (inferInstance : OrderBot (α × β))

end Prod

namespace ULift

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Top
  signature: α] : Top (ULift.{v} α) where top
  body: up ⊤

中文:
实例 [顶元素
  签名: α] : 顶元素 (类型层提升.{v} α) where top
  定义体: up ⊤
-/
instance [Top α] : Top (ULift.{v} α) where top := up ⊤

/--
theorem `up_top` / 定理 `up_top`

English:
theorem up_top
  given: [Top α]
  statement: up (⊤ : α) = ⊤
  proof: rfl

中文:
定理 up_top
  条件: [顶元素 α]
  结论: up (⊤ : α) = ⊤
  证明: rfl
-/
@[to_dual (attr := simp)] theorem up_top [Top α] : up (⊤ : α) = ⊤ := rfl
/--
theorem `down_top` / 定理 `down_top`

English:
theorem down_top
  given: [Top α]
  statement: down (⊤ : ULift α) = ⊤
  proof: rfl

@[to_dual]

中文:
定理 down_top
  条件: [顶元素 α]
  结论: down (⊤ : 类型层提升 α) = ⊤
  证明: rfl

@[to_dual]
-/
@[to_dual (attr := simp)] theorem down_top [Top α] : down (⊤ : ULift α) = ⊤ := rfl

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: α] [OrderBot α] : OrderBot (ULift.{v} α)
  body: OrderBot.lift ULift.down (fun _ _ => down_le.mp) down_bot

中文:
实例 [LE
  签名: α] [有底序 α] : 有底序 (类型层提升.{v} α)
  定义体: OrderBot.lift ULift.down (fun _ _ => down_le.mp) down_bot

Depends on / 依赖: OrderBot, OrderBot.lift, ULift.down, down_bot, down_le, down_le.mp
-/
instance [LE α] [OrderBot α] : OrderBot (ULift.{v} α) :=
  OrderBot.lift ULift.down (fun _ _ => down_le.mp) down_bot

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: α] [BoundedOrder α] : BoundedOrder (ULift.{v} α) where

中文:
实例 [LE
  签名: α] [有界序 α] : 有界序 (类型层提升.{v} α) where
-/
instance [LE α] [BoundedOrder α] : BoundedOrder (ULift.{v} α) where

end ULift

section Nontrivial

variable [PartialOrder α] [BoundedOrder α] [Nontrivial α]

@[to_dual (attr := simp)]
/--
theorem `bot_ne_top` / 定理 `bot_ne_top`

English:
theorem bot_ne_top
  statement: (⊥ : α) != ⊤
  proof: fun h => not_subsingleton _ subsingleton_of_bot_eq_top h

@[simp]

中文:
定理 bot_ne_top
  结论: (⊥ : α) != ⊤
  证明: fun h => not_subsingleton _ subsingleton_of_bot_eq_top h

@[simp]

Depends on / 依赖: not_subsingleton, subsingleton_of_bot_eq_top
-/
theorem bot_ne_top : (⊥ : α) != ⊤ := fun h => not_subsingleton _ subsingleton_of_bot_eq_top h

@[simp]
/--
theorem `bot_lt_top` / 定理 `bot_lt_top`

English:
theorem bot_lt_top
  statement: (⊥ : α) < ⊤
  proof: lt_top_iff_ne_top.2 bot_ne_top

中文:
定理 bot_lt_top
  结论: (⊥ : α) < ⊤
  证明: lt_top_iff_ne_top.2 bot_ne_top

Depends on / 依赖: bot_ne_top, lt_top_iff_ne_top
-/
theorem bot_lt_top : (⊥ : α) < ⊤ :=
  lt_top_iff_ne_top.2 bot_ne_top

end Nontrivial

section Bool

open Bool

/--
Instance `Bool.instBoundedOrder` / 实例 `Bool.instBoundedOrder`

English:
instance Bool.instBoundedOrder
  signature: : BoundedOrder Bool where
  body: true
  le_top := Bool.le_true
  bot := false
  bot_le := Bool.false_le

@[simp]

中文:
实例 布尔值.instBoundedOrder
  签名: : 有界序 布尔值 where
  定义体: true
  le_top := Bool.le_true
  bot := false
  bot_le := Bool.false_le

@[simp]
-/
instance Bool.instBoundedOrder : BoundedOrder Bool where
  top := true
  le_top := Bool.le_true
  bot := false
  bot_le := Bool.false_le

@[simp]
/--
theorem `top_eq_true` / 定理 `top_eq_true`

English:
theorem top_eq_true
  statement: ⊤ = true
  proof: rfl

@[simp]

中文:
定理 top_eq_true
  结论: ⊤ = true
  证明: rfl

@[simp]
-/
theorem top_eq_true : ⊤ = true :=
  rfl

@[simp]
/--
theorem `bot_eq_false` / 定理 `bot_eq_false`

English:
theorem bot_eq_false
  statement: ⊥ = false
  proof: rfl

中文:
定理 bot_eq_false
  结论: ⊥ = false
  证明: rfl
-/
theorem bot_eq_false : ⊥ = false :=
  rfl

end Bool
