/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Order.OrderDual

/-!
# Minimal/maximal and bottom/top elements

This file defines predicates for elements to be minimal/maximal or bottom/top and typeclasses
saying that there are no such elements.

## Predicates

* `IsBot`: An element is *bottom* if all elements are greater than it.
* `IsTop`: An element is *top* if all elements are less than it.
* `IsMin`: An element is *minimal* if no element is strictly less than it.
* `IsMax`: An element is *maximal* if no element is strictly greater than it.

See also `isBot_iff_isMin` and `isTop_iff_isMax` for the equivalences in a (co)directed order.

## Typeclasses

* `NoBotOrder`: An order without bottom elements.
* `NoTopOrder`: An order without top elements.
* `NoMinOrder`: An order without minimal elements.
* `NoMaxOrder`: An order without maximal elements.
-/

@[expose] public section


open OrderDual

universe u v

variable {α β : Type*}

/-- Order without bottom elements. -/
@[mk_iff noBotOrder_iff']
/--
Definition of `NoBotOrder` / `NoBotOrder` 的定义

English:
class NoBotOrder
  parameters: (α : Type*) [LE α]
  axioms and operations (1):
    - exists_not_ge((a : α)) : exists b, ¬a <= b

中文:
类 无底序
  参数: (α : 类型) [LE α]
  公理与运算 (1 个):
    - exists_not_ge((a : α)) : 存在 b, ¬a <= b
-/
class NoBotOrder (α : Type*) [LE α] : Prop where
  /-- For each term `a`, there is some `b` which is either incomparable or strictly smaller. -/
  exists_not_ge (a : α) : exists b, ¬a <= b

/-- Order without top elements. -/
@[to_dual, mk_iff noTopOrder_iff']
/--
Definition of `NoTopOrder` / `NoTopOrder` 的定义

English:
class NoTopOrder
  parameters: (α : Type*) [LE α]
  axioms and operations (1):
    - exists_not_le((a : α)) : exists b, ¬b <= a

中文:
类 无顶序
  参数: (α : 类型) [LE α]
  公理与运算 (1 个):
    - exists_not_le((a : α)) : 存在 b, ¬b <= a
-/
class NoTopOrder (α : Type*) [LE α] : Prop where
  /-- For each term `a`, there is some `b` which is either incomparable or strictly larger. -/
  exists_not_le (a : α) : exists b, ¬b <= a

/-- Order without minimal elements. Sometimes called coinitial or dense. -/
@[mk_iff noMinOrder_iff']
/--
Definition of `NoMinOrder` / `NoMinOrder` 的定义

English:
class NoMinOrder
  parameters: (α : Type*) [LT α]
  axioms and operations (1):
    - exists_lt((a : α)) : exists b, b < a

中文:
类 NoMin序
  参数: (α : 类型) [LT α]
  公理与运算 (1 个):
    - exists_lt((a : α)) : 存在 b, b < a
-/
class NoMinOrder (α : Type*) [LT α] : Prop where
  /-- For each term `a`, there is some strictly smaller `b`. -/
  exists_lt (a : α) : exists b, b < a

/-- Order without maximal elements. Sometimes called cofinal. -/
@[to_dual, mk_iff noMaxOrder_iff']
/--
Definition of `NoMaxOrder` / `NoMaxOrder` 的定义

English:
class NoMaxOrder
  parameters: (α : Type*) [LT α]
  axioms and operations (1):
    - exists_gt((a : α)) : exists b, a < b

中文:
类 NoMax序
  参数: (α : 类型) [LT α]
  公理与运算 (1 个):
    - exists_gt((a : α)) : 存在 b, a < b
-/
class NoMaxOrder (α : Type*) [LT α] : Prop where
  /-- For each term `a`, there is some strictly greater `b`. -/
  exists_gt (a : α) : exists b, a < b

export NoBotOrder (exists_not_ge)
export NoTopOrder (exists_not_le)
export NoMinOrder (exists_lt)
export NoMaxOrder (exists_gt)

attribute [to_dual existing] noBotOrder_iff' noMinOrder_iff'

@[to_dual nonempty_gt]
/--
Instance `nonempty_lt` / 实例 `nonempty_lt`

English:
instance nonempty_lt
  signature: [LT α] [NoMinOrder α] (a : α)
  body: nonempty_subtype.2 (exists_lt a)

@[to_dual]

中文:
实例 nonempty_lt
  签名: [LT α] [NoMin序 α] (a : α)
  定义体: nonempty_subtype.2 (exists_lt a)

@[to_dual]

Depends on / 依赖: exists_lt, nonempty_subtype
-/
instance nonempty_lt [LT α] [NoMinOrder α] (a : α) : Nonempty { x // x < a } :=
  nonempty_subtype.2 (exists_lt a)

@[to_dual]
/--
Instance `IsEmpty.toNoMinOrder` / 实例 `IsEmpty.toNoMinOrder`

English:
instance IsEmpty.toNoMinOrder
  signature: [LT α] [IsEmpty α]
  body: ⟨isEmptyElim⟩

@[to_dual]

中文:
实例 是空.toNoMinOrder
  签名: [LT α] [是空 α]
  定义体: ⟨isEmptyElim⟩

@[to_dual]

Depends on / 依赖: isEmptyElim
-/
instance IsEmpty.toNoMinOrder [LT α] [IsEmpty α] : NoMinOrder α := ⟨isEmptyElim⟩

@[to_dual]
/--
Instance `OrderDual.noBotOrder` / 实例 `OrderDual.noBotOrder`

English:
instance OrderDual.noBotOrder
  signature: [LE α] [NoTopOrder α]
  body: ⟨fun a => exists_not_le (α := α) a⟩

@[to_dual]

中文:
实例 OrderDual.noBotOrder
  签名: [LE α] [无顶序 α]
  定义体: ⟨fun a => exists_not_le (α := α) a⟩

@[to_dual]

Depends on / 依赖: exists_not_le
-/
instance OrderDual.noBotOrder [LE α] [NoTopOrder α] : NoBotOrder αᵒᵈ :=
  ⟨fun a => exists_not_le (α := α) a⟩

@[to_dual]
/--
Instance `OrderDual.noMinOrder` / 实例 `OrderDual.noMinOrder`

English:
instance OrderDual.noMinOrder
  signature: [LT α] [NoMaxOrder α]
  body: ⟨fun a => exists_gt (α := α) a⟩

中文:
实例 OrderDual.noMinOrder
  签名: [LT α] [NoMax序 α]
  定义体: ⟨fun a => exists_gt (α := α) a⟩

Depends on / 依赖: exists_gt
-/
instance OrderDual.noMinOrder [LT α] [NoMaxOrder α] : NoMinOrder αᵒᵈ :=
  ⟨fun a => exists_gt (α := α) a⟩

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) [Preorder α] [NoMinOrder α] : NoBotOrder α :=
  ⟨fun a => (exists_lt a).imp fun _ => not_le_of_gt⟩

@[to_dual]
/--
Instance `noMinOrder_of_left` / 实例 `noMinOrder_of_left`

English:
instance noMinOrder_of_left
  signature: [Preorder α] [Preorder β] [NoMinOrder α]
  body: ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt a
    exact ⟨(c, b), Prod.mk_lt_mk_iff_left.2 h⟩⟩

@[to_dual]

中文:
实例 noMinOrder_of_left
  签名: [预序 α] [预序 β] [NoMin序 α]
  定义体: ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt a
    exact ⟨(c, b), Prod.mk_lt_mk_iff_left.2 h⟩⟩

@[to_dual]

Depends on / 依赖: Prod.mk_lt_mk_iff_left, exists_lt, mk_lt_mk_iff_left
-/
instance noMinOrder_of_left [Preorder α] [Preorder β] [NoMinOrder α] : NoMinOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt a
    exact ⟨(c, b), Prod.mk_lt_mk_iff_left.2 h⟩⟩

@[to_dual]
/--
Instance `noMinOrder_of_right` / 实例 `noMinOrder_of_right`

English:
instance noMinOrder_of_right
  signature: [Preorder α] [Preorder β] [NoMinOrder β]
  body: ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt b
    exact ⟨(a, c), Prod.mk_lt_mk_iff_right.2 h⟩⟩

@[to_dual]

中文:
实例 noMinOrder_of_right
  签名: [预序 α] [预序 β] [NoMin序 β]
  定义体: ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt b
    exact ⟨(a, c), Prod.mk_lt_mk_iff_right.2 h⟩⟩

@[to_dual]

Depends on / 依赖: Prod.mk_lt_mk_iff_right, exists_lt, mk_lt_mk_iff_right
-/
instance noMinOrder_of_right [Preorder α] [Preorder β] [NoMinOrder β] : NoMinOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt b
    exact ⟨(a, c), Prod.mk_lt_mk_iff_right.2 h⟩⟩

@[to_dual]
instance {ι : Type u} {π : ι -> Type*} [Nonempty ι] [forall i, Preorder (π i)] [forall i, NoMinOrder (π i)] :
    NoMinOrder (forall i, π i) :=
  ⟨fun a => by
    classical
    obtain ⟨b, hb⟩ := exists_lt (a <| Classical.arbitrary _)
    exact ⟨_, update_lt_self_iff.2 hb⟩⟩

@[to_dual]
/--
theorem `NoBotOrder.to_noMinOrder` / 定理 `NoBotOrder.to_noMinOrder`

English:
theorem NoBotOrder.to_noMinOrder
  given: (α : Type*) [LinearOrder α] [NoBotOrder α]
  statement: NoMinOrder α
  proof: { exists_lt := fun a => by simpa [not_le] using exists_not_ge a }

@[to_dual]

中文:
定理 无底序.to_noMinOrder
  条件: (α : 类型) [线性序 α] [无底序 α]
  结论: NoMin序 α
  证明: { exists_lt := fun a => by simpa [not_le] using exists_not_ge a }

@[to_dual]

Depends on / 依赖: exists_lt, exists_not_ge, not_le
-/
theorem NoBotOrder.to_noMinOrder (α : Type*) [LinearOrder α] [NoBotOrder α] : NoMinOrder α :=
  { exists_lt := fun a => by simpa [not_le] using exists_not_ge a }

@[to_dual]
/--
theorem `noBotOrder_iff_noMinOrder` / 定理 `noBotOrder_iff_noMinOrder`

English:
theorem noBotOrder_iff_noMinOrder
  given: (α : Type*) [LinearOrder α]
  statement: NoBotOrder α ↔ NoMinOrder α
  proof: ⟨fun _ => NoBotOrder.to_noMinOrder α, fun _ => inferInstance⟩

@[to_dual]

中文:
定理 noBotOrder_iff_noMinOrder
  条件: (α : 类型) [线性序 α]
  结论: 无底序 α ↔ NoMin序 α
  证明: ⟨fun _ => NoBotOrder.to_noMinOrder α, fun _ => inferInstance⟩

@[to_dual]

Depends on / 依赖: NoBotOrder, NoBotOrder.to_noMinOrder, to_noMinOrder
-/
theorem noBotOrder_iff_noMinOrder (α : Type*) [LinearOrder α] : NoBotOrder α ↔ NoMinOrder α :=
  ⟨fun _ => NoBotOrder.to_noMinOrder α, fun _ => inferInstance⟩

@[to_dual]
/--
theorem `NoMinOrder.not_acc` / 定理 `NoMinOrder.not_acc`

English:
theorem NoMinOrder.not_acc
  given: [LT α] [NoMinOrder α] (a : α)
  statement: ¬Acc (· < ·) a
  proof: fun h =>
  Acc.recOn h fun x _ => (exists_lt x).recOn

中文:
定理 NoMin序.not_acc
  条件: [LT α] [NoMin序 α] (a : α)
  结论: ¬Acc (· < ·) a
  证明: fun h =>
  Acc.recOn h fun x _ => (exists_lt x).recOn
-/
theorem NoMinOrder.not_acc [LT α] [NoMinOrder α] (a : α) : ¬Acc (· < ·) a := fun h =>
  Acc.recOn h fun x _ => (exists_lt x).recOn

section LE

variable [LE α] {a : α}

/-- `a : α` is a bottom element of `α` if it is less than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `OrderBot`, except that a preorder may have
several bottom elements. When `α` is linear, this is useful to make a case disjunction on
`NoMinOrder α` within a proof. -/
@[to_dual /--
`a : α` is a top element of `α` if it is greater than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `OrderBot`, except that a preorder may have
several top elements. When `α` is linear, this is useful to make a case disjunction on
`NoMaxOrder α` within a proof. -/]
/--
Definition of `IsBot` / `IsBot` 的定义

English:
definition IsBot
  signature: (a : α)
  body: forall b, a <= b

中文:
定义 IsBot
  签名: (a : α)
  定义体: forall b, a <= b
-/
def IsBot (a : α) : Prop :=
  forall b, a <= b

/-- `a` is a minimal element of `α` if no element is strictly less than it. We spell it without `<`
to avoid having to convert between `≤` and `<`. Instead, `isMin_iff_forall_not_lt` does the
conversion. -/
@[to_dual /--
`a` is a maximal element of `α` if no element is strictly greater than it. We spell it without
`<` to avoid having to convert between `≤` and `<`. Instead, `isMax_iff_forall_not_lt` does the
conversion. -/]
/--
Definition of `IsMin` / `IsMin` 的定义

English:
definition IsMin
  signature: (a : α)
  body: forall ⦃b⦄, b <= a -> a <= b

@[to_dual]

中文:
定义 IsMin
  签名: (a : α)
  定义体: forall ⦃b⦄, b <= a -> a <= b

@[to_dual]
-/
def IsMin (a : α) : Prop :=
  forall ⦃b⦄, b <= a -> a <= b

@[to_dual]
/--
theorem `noBotOrder_iff` / 定理 `noBotOrder_iff`

English:
theorem noBotOrder_iff
  statement: NoBotOrder α ↔ forall x : α, ¬ IsBot x
  proof: by
  simp_rw [noBotOrder_iff', IsBot, not_forall]

@[to_dual (attr := simp)]

中文:
定理 noBotOrder_iff
  结论: 无底序 α ↔ 对任意 x : α, ¬ IsBot x
  证明: by
  simp_rw [noBotOrder_iff', IsBot, not_forall]

@[to_dual (attr := simp)]

Depends on / 依赖: noBotOrder_iff, not_forall, simp_rw
-/
theorem noBotOrder_iff : NoBotOrder α ↔ forall x : α, ¬ IsBot x := by
  simp_rw [noBotOrder_iff', IsBot, not_forall]

@[to_dual (attr := simp)]
/--
theorem `not_isBot` / 定理 `not_isBot`

English:
theorem not_isBot
  given: [NoBotOrder α] (a : α)
  statement: ¬IsBot a
  proof: fun h =>
  let ⟨_, hb⟩ := exists_not_ge a
hb h _

@[to_dual]

中文:
定理 not_isBot
  条件: [无底序 α] (a : α)
  结论: ¬IsBot a
  证明: fun h =>
  let ⟨_, hb⟩ := exists_not_ge a
hb h _

@[to_dual]
-/
theorem not_isBot [NoBotOrder α] (a : α) : ¬IsBot a := fun h =>
  let ⟨_, hb⟩ := exists_not_ge a
hb h _

@[to_dual]
/--
theorem `IsBot.isMin` / 定理 `IsBot.isMin`

English:
theorem IsBot.isMin
  given: (h : IsBot a)
  statement: IsMin a
  proof: fun b _ => h b

@[to_dual]

中文:
定理 IsBot.isMin
  条件: (h : IsBot a)
  结论: IsMin a
  证明: fun b _ => h b

@[to_dual]
-/
protected theorem IsBot.isMin (h : IsBot a) : IsMin a := fun b _ => h b

@[to_dual]
/--
theorem `IsBot.isMin_iff` / 定理 `IsBot.isMin_iff`

English:
theorem IsBot.isMin_iff
  given: {α} [PartialOrder α] {i j : α} (h : IsBot i)
  statement: IsMin j ↔ j = i
  proof: by
  simp_rw [le_antisymm_iff, h j, and_true]
  exact ⟨fun a => a (h j), fun a h' => fun _ => le_trans a (h h')⟩

@[to_dual (attr := simp)]

中文:
定理 IsBot.isMin_iff
  条件: {α} [偏序 α] {i j : α} (h : IsBot i)
  结论: IsMin j ↔ j = i
  证明: by
  simp_rw [le_antisymm_iff, h j, and_true]
  exact ⟨fun a => a (h j), fun a h' => fun _ => le_trans a (h h')⟩

@[to_dual (attr := simp)]

Depends on / 依赖: and_true, le_antisymm_iff, le_trans, simp_rw
-/
theorem IsBot.isMin_iff {α} [PartialOrder α] {i j : α} (h : IsBot i) : IsMin j ↔ j = i := by
  simp_rw [le_antisymm_iff, h j, and_true]
  exact ⟨fun a => a (h j), fun a h' => fun _ => le_trans a (h h')⟩

@[to_dual (attr := simp)]
/--
theorem `isBot_toDual_iff` / 定理 `isBot_toDual_iff`

English:
theorem isBot_toDual_iff
  statement: IsBot (toDual a) ↔ IsTop a
  proof: Iff.rfl

@[to_dual (attr := simp)]

中文:
定理 isBot_toDual_iff
  结论: IsBot (toDual a) ↔ IsTop a
  证明: Iff.rfl

@[to_dual (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem isBot_toDual_iff : IsBot (toDual a) ↔ IsTop a :=
  Iff.rfl

@[to_dual (attr := simp)]
/--
theorem `isMin_toDual_iff` / 定理 `isMin_toDual_iff`

English:
theorem isMin_toDual_iff
  statement: IsMin (toDual a) ↔ IsMax a
  proof: Iff.rfl

@[to_dual (attr := simp)]

中文:
定理 isMin_toDual_iff
  结论: IsMin (toDual a) ↔ IsMax a
  证明: Iff.rfl

@[to_dual (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem isMin_toDual_iff : IsMin (toDual a) ↔ IsMax a :=
  Iff.rfl

@[to_dual (attr := simp)]
/--
theorem `isBot_ofDual_iff` / 定理 `isBot_ofDual_iff`

English:
theorem isBot_ofDual_iff
  given: {a : αᵒᵈ}
  statement: IsBot (ofDual a) ↔ IsTop a
  proof: Iff.rfl

@[to_dual (attr := simp)]

中文:
定理 isBot_ofDual_iff
  条件: {a : αᵒᵈ}
  结论: IsBot (ofDual a) ↔ IsTop a
  证明: Iff.rfl

@[to_dual (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem isBot_ofDual_iff {a : αᵒᵈ} : IsBot (ofDual a) ↔ IsTop a :=
  Iff.rfl

@[to_dual (attr := simp)]
/--
theorem `isMin_ofDual_iff` / 定理 `isMin_ofDual_iff`

English:
theorem isMin_ofDual_iff
  given: {a : αᵒᵈ}
  statement: IsMin (ofDual a) ↔ IsMax a
  proof: Iff.rfl

@[to_dual]
alias ⟨_, IsTop.toDual⟩ := isBot_toDual_iff

@[to_dual]
alias ⟨_, IsMax.toDual⟩ := isMin_toDual_iff

@[to_dual]
alias ⟨_, IsTop.ofDual⟩ := isBot_ofDual_iff

@[to_dual]
alias ⟨_, IsMax.ofDual⟩ := isMin_ofDual_iff

中文:
定理 isMin_ofDual_iff
  条件: {a : αᵒᵈ}
  结论: IsMin (ofDual a) ↔ IsMax a
  证明: Iff.rfl

@[to_dual]
alias ⟨_, IsTop.toDual⟩ := isBot_toDual_iff

@[to_dual]
alias ⟨_, IsMax.toDual⟩ := isMin_toDual_iff

@[to_dual]
alias ⟨_, IsTop.ofDual⟩ := isBot_ofDual_iff

@[to_dual]
alias ⟨_, IsMax.ofDual⟩ := isMin_ofDual_iff

Depends on / 依赖: Iff.rfl
-/
theorem isMin_ofDual_iff {a : αᵒᵈ} : IsMin (ofDual a) ↔ IsMax a :=
  Iff.rfl

@[to_dual]
alias ⟨_, IsTop.toDual⟩ := isBot_toDual_iff

@[to_dual]
alias ⟨_, IsMax.toDual⟩ := isMin_toDual_iff

@[to_dual]
alias ⟨_, IsTop.ofDual⟩ := isBot_ofDual_iff

@[to_dual]
alias ⟨_, IsMax.ofDual⟩ := isMin_ofDual_iff

end LE

section Preorder

variable [Preorder α] {a b : α}

@[to_dual]
/--
theorem `noMinOrder_iff` / 定理 `noMinOrder_iff`

English:
theorem noMinOrder_iff
  statement: NoMinOrder α ↔ forall x : α, ¬ IsMin x
  proof: by
  simp [noMinOrder_iff', IsMin, lt_iff_le_not_ge]

@[to_dual]

中文:
定理 noMinOrder_iff
  结论: NoMin序 α ↔ 对任意 x : α, ¬ IsMin x
  证明: by
  simp [noMinOrder_iff', IsMin, lt_iff_le_not_ge]

@[to_dual]

Depends on / 依赖: lt_iff_le_not_ge, noMinOrder_iff
-/
theorem noMinOrder_iff : NoMinOrder α ↔ forall x : α, ¬ IsMin x := by
  simp [noMinOrder_iff', IsMin, lt_iff_le_not_ge]

@[to_dual]
/--
theorem `IsBot.mono` / 定理 `IsBot.mono`

English:
theorem IsBot.mono
  given: (ha : IsBot a) (h : b <= a)
  statement: IsBot b
  proof: fun _ => h.trans ha _

@[to_dual]

中文:
定理 IsBot.mono
  条件: (ha : IsBot a) (h : b <= a)
  结论: IsBot b
  证明: fun _ => h.trans ha _

@[to_dual]

Depends on / 依赖: h.trans
-/
theorem IsBot.mono (ha : IsBot a) (h : b <= a) : IsBot b := fun _ => h.trans ha _

@[to_dual]
/--
theorem `IsMin.mono` / 定理 `IsMin.mono`

English:
theorem IsMin.mono
  given: (ha : IsMin a) (h : b <= a)
  statement: IsMin b
  proof: fun _ hc => h.trans ha hc.trans h

@[to_dual]

中文:
定理 IsMin.mono
  条件: (ha : IsMin a) (h : b <= a)
  结论: IsMin b
  证明: fun _ hc => h.trans ha hc.trans h

@[to_dual]

Depends on / 依赖: h.trans, hc.trans
-/
theorem IsMin.mono (ha : IsMin a) (h : b <= a) : IsMin b := fun _ hc => h.trans ha hc.trans h

@[to_dual]
/--
theorem `IsMin.not_lt` / 定理 `IsMin.not_lt`

English:
theorem IsMin.not_lt
  given: (h : IsMin a)
  statement: ¬b < a
  proof: fun hb => hb.not_ge h hb.le

@[to_dual]

中文:
定理 IsMin.not_lt
  条件: (h : IsMin a)
  结论: ¬b < a
  证明: fun hb => hb.not_ge h hb.le

@[to_dual]

Depends on / 依赖: hb.le, hb.not_ge, not_ge
-/
theorem IsMin.not_lt (h : IsMin a) : ¬b < a := fun hb => hb.not_ge h hb.le

@[to_dual]
/--
theorem `not_isMin_of_lt` / 定理 `not_isMin_of_lt`

English:
theorem not_isMin_of_lt
  given: (h : b < a)
  statement: ¬IsMin a
  proof: fun ha => ha.not_lt h

@[to_dual]
alias LT.lt.not_isMin := not_isMin_of_lt

@[to_dual]

中文:
定理 not_isMin_of_lt
  条件: (h : b < a)
  结论: ¬IsMin a
  证明: fun ha => ha.not_lt h

@[to_dual]
alias LT.lt.not_isMin := not_isMin_of_lt

@[to_dual]

Depends on / 依赖: ha.not_lt, not_lt
-/
theorem not_isMin_of_lt (h : b < a) : ¬IsMin a := fun ha => ha.not_lt h

@[to_dual]
alias LT.lt.not_isMin := not_isMin_of_lt

@[to_dual]
/--
theorem `isMin_iff_forall_not_lt` / 定理 `isMin_iff_forall_not_lt`

English:
theorem isMin_iff_forall_not_lt
  statement: IsMin a ↔ forall b, ¬b < a
  proof: ⟨fun h _ => h.not_lt, fun h _ hba => of_not_not fun hab => h _ hba.lt_of_not_ge hab⟩

@[to_dual (attr := simp)]

中文:
定理 isMin_iff_对任意_not_lt
  结论: IsMin a ↔ 对任意 b, ¬b < a
  证明: ⟨fun h _ => h.not_lt, fun h _ hba => of_not_not fun hab => h _ hba.lt_of_not_ge hab⟩

@[to_dual (attr := simp)]

Depends on / 依赖: h.not_lt, hba.lt_of_not_ge, lt_of_not_ge, not_lt, of_not_not
-/
theorem isMin_iff_forall_not_lt : IsMin a ↔ forall b, ¬b < a :=
⟨fun h _ => h.not_lt, fun h _ hba => of_not_not fun hab => h _ hba.lt_of_not_ge hab⟩

@[to_dual (attr := simp)]
/--
theorem `not_isMin_iff` / 定理 `not_isMin_iff`

English:
theorem not_isMin_iff
  statement: ¬IsMin a ↔ exists b, b < a
  proof: by
  simp [lt_iff_le_not_ge, IsMin, not_forall]

@[to_dual (attr := simp)]

中文:
定理 not_isMin_iff
  结论: ¬IsMin a ↔ 存在 b, b < a
  证明: by
  simp [lt_iff_le_not_ge, IsMin, not_forall]

@[to_dual (attr := simp)]

Depends on / 依赖: lt_iff_le_not_ge, not_forall
-/
theorem not_isMin_iff : ¬IsMin a ↔ exists b, b < a := by
  simp [lt_iff_le_not_ge, IsMin, not_forall]

@[to_dual (attr := simp)]
/--
theorem `not_isMin` / 定理 `not_isMin`

English:
theorem not_isMin
  given: [NoMinOrder α] (a : α)
  statement: ¬IsMin a
  proof: not_isMin_iff.2 exists_lt a

中文:
定理 not_isMin
  条件: [NoMin序 α] (a : α)
  结论: ¬IsMin a
  证明: not_isMin_iff.2 exists_lt a

Depends on / 依赖: exists_lt, not_isMin_iff
-/
theorem not_isMin [NoMinOrder α] (a : α) : ¬IsMin a :=
not_isMin_iff.2 exists_lt a

namespace Subsingleton

variable [Subsingleton α]

@[to_dual]
/--
theorem `isBot` / 定理 `isBot`

English:
theorem isBot
  given: (a : α)
  statement: IsBot a
  proof: fun _ => (Subsingleton.elim _ _).le

@[to_dual]

中文:
定理 isBot
  条件: (a : α)
  结论: IsBot a
  证明: fun _ => (Subsingleton.elim _ _).le

@[to_dual]
-/
protected theorem isBot (a : α) : IsBot a := fun _ => (Subsingleton.elim _ _).le

@[to_dual]
/--
theorem `isMin` / 定理 `isMin`

English:
theorem isMin
  given: (a : α)
  statement: IsMin a
  proof: (Subsingleton.isBot _).isMin

中文:
定理 isMin
  条件: (a : α)
  结论: IsMin a
  证明: (Subsingleton.isBot _).isMin
-/
protected theorem isMin (a : α) : IsMin a :=
  (Subsingleton.isBot _).isMin

end Subsingleton

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

@[to_dual eq_of_ge]
/--
theorem `IsMin.eq_of_le` / 定理 `IsMin.eq_of_le`

English:
theorem IsMin.eq_of_le
  given: (ha : IsMin a) (h : b <= a)
  statement: b = a
  proof: h.antisymm ha h

@[to_dual eq_of_le]

中文:
定理 IsMin.eq_of_le
  条件: (ha : IsMin a) (h : b <= a)
  结论: b = a
  证明: h.antisymm ha h

@[to_dual eq_of_le]
-/
protected theorem IsMin.eq_of_le (ha : IsMin a) (h : b <= a) : b = a :=
h.antisymm ha h

@[to_dual eq_of_le]
/--
theorem `IsMin.eq_of_ge` / 定理 `IsMin.eq_of_ge`

English:
theorem IsMin.eq_of_ge
  given: (ha : IsMin a) (h : b <= a)
  statement: a = b
  proof: h.antisymm' ha h

@[to_dual lt_of_ne']

中文:
定理 IsMin.eq_of_ge
  条件: (ha : IsMin a) (h : b <= a)
  结论: a = b
  证明: h.antisymm' ha h

@[to_dual lt_of_ne']
-/
protected theorem IsMin.eq_of_ge (ha : IsMin a) (h : b <= a) : a = b :=
h.antisymm' ha h

@[to_dual lt_of_ne']
/--
theorem `IsBot.lt_of_ne` / 定理 `IsBot.lt_of_ne`

English:
theorem IsBot.lt_of_ne
  given: (ha : IsBot a) (h : a != b)
  statement: a < b
  proof: (ha b).lt_of_ne h

@[to_dual lt_of_ne']

中文:
定理 IsBot.lt_of_ne
  条件: (ha : IsBot a) (h : a != b)
  结论: a < b
  证明: (ha b).lt_of_ne h

@[to_dual lt_of_ne']
-/
protected theorem IsBot.lt_of_ne (ha : IsBot a) (h : a != b) : a < b :=
  (ha b).lt_of_ne h

@[to_dual lt_of_ne']
/--
theorem `IsTop.lt_of_ne` / 定理 `IsTop.lt_of_ne`

English:
theorem IsTop.lt_of_ne
  given: (ha : IsTop a) (h : b != a)
  statement: b < a
  proof: (ha b).lt_of_ne h

@[to_dual]

中文:
定理 IsTop.lt_of_ne
  条件: (ha : IsTop a) (h : b != a)
  结论: b < a
  证明: (ha b).lt_of_ne h

@[to_dual]
-/
protected theorem IsTop.lt_of_ne (ha : IsTop a) (h : b != a) : b < a :=
  (ha b).lt_of_ne h

@[to_dual]
/--
theorem `IsBot.not_isMax` / 定理 `IsBot.not_isMax`

English:
theorem IsBot.not_isMax
  given: [Nontrivial α] (ha : IsBot a)
  statement: ¬ IsMax a
  proof: by
  intro ha'
  obtain ⟨b, hb⟩ := exists_ne a
exact hb ha'.eq_of_ge (ha.lt_of_ne hb.symm).le

@[to_dual]

中文:
定理 IsBot.not_isMax
  条件: [非平凡 α] (ha : IsBot a)
  结论: ¬ IsMax a
  证明: by
  intro ha'
  obtain ⟨b, hb⟩ := exists_ne a
exact hb ha'.eq_of_ge (ha.lt_of_ne hb.symm).le

@[to_dual]
-/
protected theorem IsBot.not_isMax [Nontrivial α] (ha : IsBot a) : ¬ IsMax a := by
  intro ha'
  obtain ⟨b, hb⟩ := exists_ne a
exact hb ha'.eq_of_ge (ha.lt_of_ne hb.symm).le

@[to_dual]
/--
theorem `IsBot.not_isTop` / 定理 `IsBot.not_isTop`

English:
theorem IsBot.not_isTop
  given: [Nontrivial α] (ha : IsBot a)
  statement: ¬ IsTop a
  proof: mt IsTop.isMax ha.not_isMax

中文:
定理 IsBot.not_isTop
  条件: [非平凡 α] (ha : IsBot a)
  结论: ¬ IsTop a
  证明: mt IsTop.isMax ha.not_isMax
-/
protected theorem IsBot.not_isTop [Nontrivial α] (ha : IsBot a) : ¬ IsTop a :=
  mt IsTop.isMax ha.not_isMax

end PartialOrder

section Prod

variable [Preorder α] [Preorder β] {a : α} {b : β} {x : α × β}

@[to_dual]
/--
theorem `IsBot.prodMk` / 定理 `IsBot.prodMk`

English:
theorem IsBot.prodMk
  given: (ha : IsBot a) (hb : IsBot b)
  statement: IsBot (a, b)
  proof: fun _ => ⟨ha _, hb _⟩

@[to_dual]

中文:
定理 IsBot.prodMk
  条件: (ha : IsBot a) (hb : IsBot b)
  结论: IsBot (a, b)
  证明: fun _ => ⟨ha _, hb _⟩

@[to_dual]
-/
theorem IsBot.prodMk (ha : IsBot a) (hb : IsBot b) : IsBot (a, b) := fun _ => ⟨ha _, hb _⟩

@[to_dual]
/--
theorem `IsMin.prodMk` / 定理 `IsMin.prodMk`

English:
theorem IsMin.prodMk
  given: (ha : IsMin a) (hb : IsMin b)
  statement: IsMin (a, b)
  proof: fun _ hc => ⟨ha hc.1, hb hc.2⟩

@[to_dual]

中文:
定理 IsMin.prodMk
  条件: (ha : IsMin a) (hb : IsMin b)
  结论: IsMin (a, b)
  证明: fun _ hc => ⟨ha hc.1, hb hc.2⟩

@[to_dual]
-/
theorem IsMin.prodMk (ha : IsMin a) (hb : IsMin b) : IsMin (a, b) := fun _ hc => ⟨ha hc.1, hb hc.2⟩

@[to_dual]
/--
theorem `IsBot.fst` / 定理 `IsBot.fst`

English:
theorem IsBot.fst
  given: (hx : IsBot x)
  statement: IsBot x.1
  proof: fun c => (hx (c, x.2)).1

@[to_dual]

中文:
定理 IsBot.fst
  条件: (hx : IsBot x)
  结论: IsBot x.1
  证明: fun c => (hx (c, x.2)).1

@[to_dual]
-/
theorem IsBot.fst (hx : IsBot x) : IsBot x.1 := fun c => (hx (c, x.2)).1

@[to_dual]
/--
theorem `IsBot.snd` / 定理 `IsBot.snd`

English:
theorem IsBot.snd
  given: (hx : IsBot x)
  statement: IsBot x.2
  proof: fun c => (hx (x.1, c)).2

@[to_dual]

中文:
定理 IsBot.snd
  条件: (hx : IsBot x)
  结论: IsBot x.2
  证明: fun c => (hx (x.1, c)).2

@[to_dual]
-/
theorem IsBot.snd (hx : IsBot x) : IsBot x.2 := fun c => (hx (x.1, c)).2

@[to_dual]
/--
theorem `IsMin.fst` / 定理 `IsMin.fst`

English:
theorem IsMin.fst
  given: (hx : IsMin x)
  statement: IsMin x.1
  proof: fun c hc => (hx <| show (c, x.2) <= x from (and_iff_left le_rfl).2 hc).1

@[to_dual]

中文:
定理 IsMin.fst
  条件: (hx : IsMin x)
  结论: IsMin x.1
  证明: fun c hc => (hx <| show (c, x.2) <= x from (and_iff_left le_rfl).2 hc).1

@[to_dual]

Depends on / 依赖: and_iff_left, le_rfl
-/
theorem IsMin.fst (hx : IsMin x) : IsMin x.1 :=
  fun c hc => (hx <| show (c, x.2) <= x from (and_iff_left le_rfl).2 hc).1

@[to_dual]
/--
theorem `IsMin.snd` / 定理 `IsMin.snd`

English:
theorem IsMin.snd
  given: (hx : IsMin x)
  statement: IsMin x.2
  proof: fun c hc => (hx <| show (x.1, c) <= x from (and_iff_right le_rfl).2 hc).2

@[to_dual]

中文:
定理 IsMin.snd
  条件: (hx : IsMin x)
  结论: IsMin x.2
  证明: fun c hc => (hx <| show (x.1, c) <= x from (and_iff_right le_rfl).2 hc).2

@[to_dual]

Depends on / 依赖: and_iff_right, le_rfl
-/
theorem IsMin.snd (hx : IsMin x) : IsMin x.2 :=
  fun c hc => (hx <| show (x.1, c) <= x from (and_iff_right le_rfl).2 hc).2

@[to_dual]
/--
theorem `Prod.isBot_iff` / 定理 `Prod.isBot_iff`

English:
theorem Prod.isBot_iff
  statement: IsBot x ↔ IsBot x.1 ∧ IsBot x.2
  proof: ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prodMk h.2⟩

@[to_dual]

中文:
定理 积类型.isBot_iff
  结论: IsBot x ↔ IsBot x.1 ∧ IsBot x.2
  证明: ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prodMk h.2⟩

@[to_dual]

Depends on / 依赖: hx.fst, hx.snd, prodMk
-/
theorem Prod.isBot_iff : IsBot x ↔ IsBot x.1 ∧ IsBot x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prodMk h.2⟩

@[to_dual]
/--
theorem `Prod.isMin_iff` / 定理 `Prod.isMin_iff`

English:
theorem Prod.isMin_iff
  statement: IsMin x ↔ IsMin x.1 ∧ IsMin x.2
  proof: ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prodMk h.2⟩

中文:
定理 积类型.isMin_iff
  结论: IsMin x ↔ IsMin x.1 ∧ IsMin x.2
  证明: ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prodMk h.2⟩

Depends on / 依赖: hx.fst, hx.snd, prodMk
-/
theorem Prod.isMin_iff : IsMin x ↔ IsMin x.1 ∧ IsMin x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prodMk h.2⟩

end Prod
