/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Order.BoundedOrder.Lattice

/-!
# Typeclasses expressing `IsBot 1` and `IsBot 0`
-/

public section

/--
Definition of `IsBotZeroClass` / `IsBotZeroClass` 的定义

English:
class IsBotZeroClass
  parameters: (α : Type*) [LE α] [Zero α]
  axioms and operations (1):
    - isBot_zero : IsBot (0 : α)

中文:
类 IsBotZeroClass
  参数: (α : 类型) [LE α] [Zero α]
  公理与运算 (1 个):
    - isBot_zero : IsBot (0 : α)
-/
class IsBotZeroClass (α : Type*) [LE α] [Zero α] : Prop where
  isBot_zero : IsBot (0 : α)

/-- A typeclass expressing that the `1` of a type is a bottom element. In a partial `OrderBot`, this
is equivalent to `⊥ = 1`. -/
@[to_additive existing]
/--
Definition of `IsBotOneClass` / `IsBotOneClass` 的定义

English:
class IsBotOneClass
  parameters: (α : Type*) [LE α] [One α]
  axioms and operations (1):
    - isBot_one : IsBot (1 : α)

中文:
类 IsBotOneClass
  参数: (α : 类型) [LE α] [One α]
  公理与运算 (1 个):
    - isBot_one : IsBot (1 : α)
-/
class IsBotOneClass (α : Type*) [LE α] [One α] : Prop where
  isBot_one : IsBot (1 : α)

variable {α : Type*} {a b : α}

section LE
variable [LE α] [One α] [IsBotOneClass α]

@[to_additive]
/--
theorem `isBot_one` / 定理 `isBot_one`

English:
theorem isBot_one
  statement: IsBot (1 : α)
  proof: IsBotOneClass.isBot_one

@[to_additive (attr := simp) zero_le]

中文:
定理 isBot_one
  结论: IsBot (1 : α)
  证明: IsBotOneClass.isBot_one

@[to_additive (attr := simp) zero_le]

Depends on / 依赖: IsBotOneClass, IsBotOneClass.isBot_one, isBot_one
-/
theorem isBot_one : IsBot (1 : α) :=
  IsBotOneClass.isBot_one

@[to_additive (attr := simp) zero_le]
/--
theorem `one_le` / 定理 `one_le`

English:
theorem one_le
  given: {a : α}
  statement: 1 <= a
  proof: isBot_one a

@[deprecated (since := "2026-05-27")]
alias zero_le' := zero_le

中文:
定理 one_le
  条件: {a : α}
  结论: 1 <= a
  证明: isBot_one a

@[deprecated (since := "2026-05-27")]
alias zero_le' := zero_le

Depends on / 依赖: isBot_one
-/
theorem one_le {a : α} : 1 <= a :=
  isBot_one a

@[deprecated (since := "2026-05-27")]
alias zero_le' := zero_le

variable (α) in
/-- Create an `OrderBot` instance, setting `1` as the bottom element. -/
@[expose, to_additive (attr := instance_reducible)
/-- Create an `OrderBot` instance, setting `0` as the bottom element. -/]
/--
Definition of `IsBotOneClass.toOrderBot` / `IsBotOneClass.toOrderBot` 的定义

English:
definition IsBotOneClass.toOrderBot
  signature: : OrderBot α where
  body: 1
  bot_le _ := one_le

中文:
定义 IsBotOneClass.toOrderBot
  签名: : OrderBot α where
  定义体: 1
  bot_le _ := one_le
-/
def IsBotOneClass.toOrderBot : OrderBot α where
  bot := 1
  bot_le _ := one_le

end LE

-- See note [lower instance priority]
instance (priority := 100) [LE α] [Zero α] [One α] [IsBotZeroClass α] : ZeroLEOneClass α where
  zero_le_one := zero_le

section Preorder
variable [Preorder α] [One α] [IsBotOneClass α]

@[to_additive (attr := simp) not_lt_zero]
/--
theorem `not_lt_one` / 定理 `not_lt_one`

English:
theorem not_lt_one
  statement: ¬ a < 1
  proof: one_le.not_gt

@[deprecated (since := "2026-05-07")]
alias not_lt_zero' := not_lt_zero

@[to_additive] -- `(attr := simp)` cannot be used here because `a` cannot be inferred by `simp`.

中文:
定理 not_lt_one
  结论: ¬ a < 1
  证明: one_le.not_gt

@[deprecated (since := "2026-05-07")]
alias not_lt_zero' := not_lt_zero

@[to_additive] -- `(attr := simp)` cannot be used here because `a` cannot be inferred by `simp`.

Depends on / 依赖: not_gt, one_le, one_le.not_gt
-/
theorem not_lt_one : ¬ a < 1 := one_le.not_gt

@[deprecated (since := "2026-05-07")]
alias not_lt_zero' := not_lt_zero

@[to_additive] -- `(attr := simp)` cannot be used here because `a` cannot be inferred by `simp`.
/--
theorem `one_lt_of_gt` / 定理 `one_lt_of_gt`

English:
theorem one_lt_of_gt
  given: (h : a < b)
  statement: 1 < b
  proof: one_le.trans_lt h

@[to_additive] alias LT.lt.one_lt := one_lt_of_gt

@[to_additive]

中文:
定理 one_lt_of_gt
  条件: (h : a < b)
  结论: 1 < b
  证明: one_le.trans_lt h

@[to_additive] alias LT.lt.one_lt := one_lt_of_gt

@[to_additive]

Depends on / 依赖: one_le, one_le.trans_lt, trans_lt
-/
theorem one_lt_of_gt (h : a < b) : 1 < b :=
  one_le.trans_lt h

@[to_additive] alias LT.lt.one_lt := one_lt_of_gt

@[to_additive]
/--
theorem `ne_one_of_lt` / 定理 `ne_one_of_lt`

English:
theorem ne_one_of_lt
  given: (h : a < b)
  statement: b != 1
  proof: h.one_lt.ne'

@[to_additive] alias LT.lt.ne_one := ne_one_of_lt

中文:
定理 ne_one_of_lt
  条件: (h : a < b)
  结论: b != 1
  证明: h.one_lt.ne'

@[to_additive] alias LT.lt.ne_one := ne_one_of_lt

Depends on / 依赖: h.one_lt.ne, one_lt
-/
theorem ne_one_of_lt (h : a < b) : b != 1 :=
  h.one_lt.ne'

@[to_additive] alias LT.lt.ne_one := ne_one_of_lt

end Preorder

section PartialOrder
variable [PartialOrder α] [One α] [IsBotOneClass α]

-- Not `simp`, as different types might have a different preferred form.
@[to_additive]
/--
theorem `bot_eq_one` / 定理 `bot_eq_one`

English:
theorem bot_eq_one
  given: [OrderBot α]
  statement: (⊥ : α) = 1
  proof: isBot_one.eq_bot.symm

@[deprecated (since := "2026-05-07")]
alias bot_eq_zero'' := bot_eq_zero

@[to_additive (attr := simp)]

中文:
定理 bot_eq_one
  条件: [OrderBot α]
  结论: (⊥ : α) = 1
  证明: isBot_one.eq_bot.symm

@[deprecated (since := "2026-05-07")]
alias bot_eq_zero'' := bot_eq_zero

@[to_additive (attr := simp)]

Depends on / 依赖: eq_bot, isBot_one, isBot_one.eq_bot.symm
-/
theorem bot_eq_one [OrderBot α] : (⊥ : α) = 1 := isBot_one.eq_bot.symm

@[deprecated (since := "2026-05-07")]
alias bot_eq_zero'' := bot_eq_zero

@[to_additive (attr := simp)]
/--
theorem `le_one_iff_eq_one` / 定理 `le_one_iff_eq_one`

English:
theorem le_one_iff_eq_one
  statement: a <= 1 ↔ a = 1
  proof: one_le.ge_iff_eq'

中文:
定理 le_one_iff_eq_one
  结论: a <= 1 ↔ a = 1
  证明: one_le.ge_iff_eq'

Depends on / 依赖: ge_iff_eq, one_le, one_le.ge_iff_eq
-/
theorem le_one_iff_eq_one : a <= 1 ↔ a = 1 :=
  one_le.ge_iff_eq'

-- TODO: deprecate
alias le_zero_iff := nonpos_iff_eq_zero

@[to_additive] alias ⟨eq_one_of_le_one, _⟩ := le_one_iff_eq_one
@[to_additive] alias LE.le.eq_one := eq_one_of_le_one

@[to_additive]
/--
theorem `one_lt_iff_ne_one` / 定理 `one_lt_iff_ne_one`

English:
theorem one_lt_iff_ne_one
  statement: 1 < a ↔ a != 1
  proof: one_le.lt_iff_ne.trans ne_comm

中文:
定理 one_lt_iff_ne_one
  结论: 1 < a ↔ a != 1
  证明: one_le.lt_iff_ne.trans ne_comm

Depends on / 依赖: lt_iff_ne, ne_comm, one_le, one_le.lt_iff_ne.trans
-/
theorem one_lt_iff_ne_one : 1 < a ↔ a != 1 :=
  one_le.lt_iff_ne.trans ne_comm

-- TODO: deprecate
alias zero_lt_iff := pos_iff_ne_zero

@[to_additive] alias ⟨_, one_lt_of_ne_one⟩ := one_lt_iff_ne_one
@[to_additive] alias Ne.one_lt := one_lt_of_ne_one

@[to_additive]
/--
theorem `eq_one_or_one_lt` / 定理 `eq_one_or_one_lt`

English:
theorem eq_one_or_one_lt
  given: (a : α)
  statement: a = 1 ∨ 1 < a
  proof: one_le.eq_or_lt'

@[to_additive]

中文:
定理 eq_one_or_one_lt
  条件: (a : α)
  结论: a = 1 ∨ 1 < a
  证明: one_le.eq_or_lt'

@[to_additive]

Depends on / 依赖: eq_or_lt, one_le, one_le.eq_or_lt
-/
theorem eq_one_or_one_lt (a : α) : a = 1 ∨ 1 < a := one_le.eq_or_lt'

@[to_additive]
/--
lemma `one_notMem_iff` / 引理 `one_notMem_iff`

English:
lemma one_notMem_iff
  given: {s : Set α}
  statement: 1 ∉ s ↔ forall x in s, 1 < x
  proof: let := IsBotOneClass.toOrderBot α
  bot_notMem_iff

@[deprecated (since := "2026-02-17")] alias NE.ne.pos := Ne.pos
@[deprecated (since := "2026-02-17")] alias NE.ne.one_lt := Ne.one_lt

中文:
引理 one_notMem_iff
  条件: {s : Set α}
  结论: 1 ∉ s ↔ 对任意 x in s, 1 < x
  证明: let := IsBotOneClass.toOrderBot α
  bot_notMem_iff

@[deprecated (since := "2026-02-17")] alias NE.ne.pos := Ne.pos
@[deprecated (since := "2026-02-17")] alias NE.ne.one_lt := Ne.one_lt

Depends on / 依赖: IsBotOneClass, IsBotOneClass.toOrderBot, bot_notMem_iff, toOrderBot
-/
lemma one_notMem_iff {s : Set α} : 1 ∉ s ↔ forall x in s, 1 < x :=
  let := IsBotOneClass.toOrderBot α
  bot_notMem_iff

@[deprecated (since := "2026-02-17")] alias NE.ne.pos := Ne.pos
@[deprecated (since := "2026-02-17")] alias NE.ne.one_lt := Ne.one_lt

end PartialOrder

section LinearOrder
variable [LinearOrder α] [One α] [IsBotOneClass α]

@[to_additive]
/--
theorem `one_min` / 定理 `one_min`

English:
theorem one_min
  given: (a : α)
  statement: min 1 a = 1
  proof: by simp

@[to_additive]

中文:
定理 one_min
  条件: (a : α)
  结论: min 1 a = 1
  证明: by simp

@[to_additive]
-/
theorem one_min (a : α) : min 1 a = 1 := by simp

@[to_additive]
/--
theorem `min_one` / 定理 `min_one`

English:
theorem min_one
  given: (a : α)
  statement: min a 1 = 1
  proof: by simp

@[to_additive]

中文:
定理 min_one
  条件: (a : α)
  结论: min a 1 = 1
  证明: by simp

@[to_additive]
-/
theorem min_one (a : α) : min a 1 = 1 := by simp

@[to_additive]
/--
theorem `one_max` / 定理 `one_max`

English:
theorem one_max
  given: (a : α)
  statement: max 1 a = a
  proof: by simp

@[to_additive]

中文:
定理 one_max
  条件: (a : α)
  结论: max 1 a = a
  证明: by simp

@[to_additive]
-/
theorem one_max (a : α) : max 1 a = a := by simp

@[to_additive]
/--
theorem `max_one` / 定理 `max_one`

English:
theorem max_one
  given: (a : α)
  statement: max a 1 = a
  proof: by simp

@[to_additive (attr := simp)]

中文:
定理 max_one
  条件: (a : α)
  结论: max a 1 = a
  证明: by simp

@[to_additive (attr := simp)]
-/
theorem max_one (a : α) : max a 1 = a := by simp

@[to_additive (attr := simp)]
/--
theorem `max_eq_one` / 定理 `max_eq_one`

English:
theorem max_eq_one
  given: {a b : α}
  statement: max a b = 1 ↔ a = 1 ∧ b = 1
  proof: let := IsBotOneClass.toOrderBot α
  max_eq_bot

@[to_additive (attr := simp)]

中文:
定理 max_eq_one
  条件: {a b : α}
  结论: max a b = 1 ↔ a = 1 ∧ b = 1
  证明: let := IsBotOneClass.toOrderBot α
  max_eq_bot

@[to_additive (attr := simp)]

Depends on / 依赖: IsBotOneClass, IsBotOneClass.toOrderBot, max_eq_bot, toOrderBot
-/
theorem max_eq_one {a b : α} : max a b = 1 ↔ a = 1 ∧ b = 1 :=
  let := IsBotOneClass.toOrderBot α
  max_eq_bot

@[to_additive (attr := simp)]
/--
theorem `min_eq_one` / 定理 `min_eq_one`

English:
theorem min_eq_one
  given: {a b : α}
  statement: min a b = 1 ↔ a = 1 ∨ b = 1
  proof: let := IsBotOneClass.toOrderBot α
  min_eq_bot

中文:
定理 min_eq_one
  条件: {a b : α}
  结论: min a b = 1 ↔ a = 1 ∨ b = 1
  证明: let := IsBotOneClass.toOrderBot α
  min_eq_bot

Depends on / 依赖: IsBotOneClass, IsBotOneClass.toOrderBot, min_eq_bot, toOrderBot
-/
theorem min_eq_one {a b : α} : min a b = 1 ↔ a = 1 ∨ b = 1 :=
  let := IsBotOneClass.toOrderBot α
  min_eq_bot

end LinearOrder

namespace NeZero
variable [Zero α]

/--
theorem `of_gt` / 定理 `of_gt`

English:
theorem of_gt
  given: [Preorder α] [IsBotZeroClass α] (h : a < b)
  statement: NeZero b
  proof: ⟨h.ne_zero⟩

中文:
定理 of_gt
  条件: [Preorder α] [IsBotZeroClass α] (h : a < b)
  结论: NeZero b
  证明: ⟨h.ne_zero⟩

Depends on / 依赖: h.ne_zero, ne_zero
-/
theorem of_gt [Preorder α] [IsBotZeroClass α] (h : a < b) : NeZero b :=
  ⟨h.ne_zero⟩

/--
theorem `pos` / 定理 `pos`

English:
theorem pos
  given: [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a]
  statement: 0 < a
  proof: NeZero.out.pos

中文:
定理 pos
  条件: [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a]
  结论: 0 < a
  证明: NeZero.out.pos

Depends on / 依赖: NeZero, NeZero.out.pos
-/
theorem pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] : 0 < a :=
  NeZero.out.pos

-- 1 < p is still an often-used `Fact`, due to `Nat.Prime` implying it, and it implying `Nontrivial`
-- on `ZMod`'s ring structure. We cannot just set this to be any `x < y`, else that becomes a
-- metavariable and it will hugely slow down typeclass inference.
instance (priority := 10) of_gt' [Preorder α] [IsBotZeroClass α] [One α]
[Fact (1 < a)] : NeZero a := of_gt @Fact.out (1 < a) _

/--
theorem `of_ge` / 定理 `of_ge`

English:
theorem of_ge
  given: [PartialOrder α] [IsBotZeroClass α] [NeZero a] (h : a <= b)
  statement: NeZero b
  proof: ⟨((pos a).trans_le h).ne_zero⟩

中文:
定理 of_ge
  条件: [PartialOrder α] [IsBotZeroClass α] [NeZero a] (h : a <= b)
  结论: NeZero b
  证明: ⟨((pos a).trans_le h).ne_zero⟩

Depends on / 依赖: ne_zero, trans_le
-/
theorem of_ge [PartialOrder α] [IsBotZeroClass α] [NeZero a] (h : a <= b) : NeZero b :=
  ⟨((pos a).trans_le h).ne_zero⟩

end NeZero
