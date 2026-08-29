/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.Order.BoundedOrder.Lattice

/-!
# Successor and predecessor limits

We define the predicate `Order.IsSuccPrelimit` for "successor pre-limits", values that don't cover
any others. They are so named since they can't be the successors of anything smaller. We define
`Order.IsPredPrelimit` analogously, and prove basic results.

For some applications, it is desirable to exclude minimal elements from being successor limits, or
maximal elements from being predecessor limits. As such, we also provide `Order.IsSuccLimit` and
`Order.IsPredLimit`, which exclude these cases.
-/

@[expose] public section

variable {α : Type*} {a b : α}

namespace Order

open Function Set OrderDual

/-! ### Successor and predecessor limits -/

section LT

variable [LT α]

/-- A successor pre-limit is a value that doesn't cover any other.

It's so named because in a successor order, a successor pre-limit can't be the successor of anything
smaller.

Use `IsSuccLimit` if you want to exclude the case of a minimal element. -/
@[to_dual
/-- A predecessor pre-limit is a value that isn't covered by any other.

It's so named because in a predecessor order, a predecessor pre-limit can't be the predecessor of
anything smaller.

Use `IsPredLimit` to exclude the case of a maximal element. -/]
/--
Definition of `IsSuccPrelimit` / `IsSuccPrelimit` 的定义

English:
definition IsSuccPrelimit
  signature: (a : α)
  body: forall b, ¬b ⋖ a

@[to_dual]

中文:
定义 IsSuccPrelimit
  签名: (a : α)
  定义体: forall b, ¬b ⋖ a

@[to_dual]
-/
def IsSuccPrelimit (a : α) : Prop :=
  forall b, ¬b ⋖ a

@[to_dual]
/--
theorem `not_isSuccPrelimit_iff` / 定理 `not_isSuccPrelimit_iff`

English:
theorem not_isSuccPrelimit_iff
  given: {a : α}
  statement: ¬IsSuccPrelimit a ↔ exists b, b ⋖ a
  proof: by
  simp [IsSuccPrelimit]

中文:
定理 not_isSuccPrelimit_iff
  条件: {a : α}
  结论: ¬IsSuccPrelimit a ↔ 存在 b, b ⋖ a
  证明: by
  simp [IsSuccPrelimit]

Depends on / 依赖: IsSuccPrelimit
-/
theorem not_isSuccPrelimit_iff {a : α} : ¬IsSuccPrelimit a ↔ exists b, b ⋖ a := by
  simp [IsSuccPrelimit]

/-- The lemma formerly named `not_isSuccPrelimit_iff` is now
`not_isSuccPrelimit_iff_succ_eq` -/
@[deprecated (since := "2026-04-19")]
alias not_isSuccPrelimit_iff_exists_covBy := not_isSuccPrelimit_iff

/-- The lemma formerly named `not_isPredPrelimit_iff` is now
`not_isPredPrelimit_iff_pred_eq` -/
@[to_dual existing, deprecated (since := "2026-04-19")]
alias not_isPredPrelimit_iff_exists_covBy := not_isPredPrelimit_iff

@[to_dual (attr := simp)]
/--
theorem `IsSuccPrelimit.of_dense` / 定理 `IsSuccPrelimit.of_dense`

English:
theorem IsSuccPrelimit.of_dense
  given: [DenselyOrdered α] (a : α)
  statement: IsSuccPrelimit a
  proof: fun _ => not_covBy

@[to_dual (attr := simp)]

中文:
定理 IsSuccPrelimit.of_dense
  条件: [DenselyOrdered α] (a : α)
  结论: IsSuccPrelimit a
  证明: fun _ => not_covBy

@[to_dual (attr := simp)]

Depends on / 依赖: not_covBy
-/
theorem IsSuccPrelimit.of_dense [DenselyOrdered α] (a : α) : IsSuccPrelimit a := fun _ => not_covBy

@[to_dual (attr := simp)]
/--
theorem `isSuccPrelimit_toDual_iff` / 定理 `isSuccPrelimit_toDual_iff`

English:
theorem isSuccPrelimit_toDual_iff
  statement: IsSuccPrelimit (toDual a) ↔ IsPredPrelimit a
  proof: by
  simp [IsSuccPrelimit, IsPredPrelimit]

@[to_dual]
alias ⟨_, IsPredPrelimit.dual⟩ := isSuccPrelimit_toDual_iff

中文:
定理 isSuccPrelimit_toDual_iff
  结论: IsSuccPrelimit (toDual a) ↔ IsPredPrelimit a
  证明: by
  simp [IsSuccPrelimit, IsPredPrelimit]

@[to_dual]
alias ⟨_, IsPredPrelimit.dual⟩ := isSuccPrelimit_toDual_iff

Depends on / 依赖: IsPredPrelimit, IsSuccPrelimit
-/
theorem isSuccPrelimit_toDual_iff : IsSuccPrelimit (toDual a) ↔ IsPredPrelimit a := by
  simp [IsSuccPrelimit, IsPredPrelimit]

@[to_dual]
alias ⟨_, IsPredPrelimit.dual⟩ := isSuccPrelimit_toDual_iff

end LT

section Preorder

variable [Preorder α]

/-- A successor limit is a value that isn't minimal and doesn't cover any other.

It's so named because in a successor order, a successor limit can't be the successor of anything
smaller.

Use `IsSuccPrelimit` if you want to include the case of a minimal element. -/
@[mk_iff]
/--
Definition of `IsSuccLimit` / `IsSuccLimit` 的定义

English:
structure IsSuccLimit
  parameters: (a : α)
  axioms and operations (2):
    - not_isMin : ¬ IsMin a
    - isSuccPrelimit : IsSuccPrelimit a

中文:
结构 IsSuccLimit
  参数: (a : α)
  公理与运算 (2 个):
    - not_isMin : ¬ IsMin a
    - isSuccPrelimit : IsSuccPrelimit a
-/
structure IsSuccLimit (a : α) : Prop where
  /-- Successor limits aren't minimal. -/
  protected not_isMin : ¬ IsMin a
  /-- Successor limits don't cover any other elements. -/
  protected isSuccPrelimit : IsSuccPrelimit a

/-- A predecessor limit is a value that isn't maximal and isn't covered by any other.

It's so named because in a predecessor order, a predecessor limit can't be the predecessor of
anything larger.

Use `IsPredPrelimit` if you want to include the case of a maximal element. -/
@[mk_iff, to_dual existing]
/--
Definition of `IsPredLimit` / `IsPredLimit` 的定义

English:
structure IsPredLimit
  parameters: (a : α)
  axioms and operations (2):
    - not_isMax : ¬ IsMax a
    - isPredPrelimit : IsPredPrelimit a

中文:
结构 IsPredLimit
  参数: (a : α)
  公理与运算 (2 个):
    - not_isMax : ¬ IsMax a
    - isPredPrelimit : IsPredPrelimit a
-/
structure IsPredLimit (a : α) : Prop where
  /-- Predecessor limits aren't maximal. -/
  protected not_isMax : ¬ IsMax a
  /-- Predecessor limits aren't covered by any other elements. -/
  protected isPredPrelimit : IsPredPrelimit a

attribute [to_dual existing] isSuccLimit_iff
attribute [simp] IsSuccLimit.isSuccPrelimit IsPredLimit.isPredPrelimit

@[to_dual (attr := simp)]
/--
theorem `isSuccLimit_toDual_iff` / 定理 `isSuccLimit_toDual_iff`

English:
theorem isSuccLimit_toDual_iff
  statement: IsSuccLimit (toDual a) ↔ IsPredLimit a
  proof: by
  simp [isSuccLimit_iff, isPredLimit_iff]

@[to_dual] alias ⟨_, IsPredLimit.dual⟩ := isSuccLimit_toDual_iff

@[to_dual]

中文:
定理 isSuccLimit_toDual_iff
  结论: IsSuccLimit (toDual a) ↔ IsPredLimit a
  证明: by
  simp [isSuccLimit_iff, isPredLimit_iff]

@[to_dual] alias ⟨_, IsPredLimit.dual⟩ := isSuccLimit_toDual_iff

@[to_dual]

Depends on / 依赖: isPredLimit_iff, isSuccLimit_iff
-/
theorem isSuccLimit_toDual_iff : IsSuccLimit (toDual a) ↔ IsPredLimit a := by
  simp [isSuccLimit_iff, isPredLimit_iff]

@[to_dual] alias ⟨_, IsPredLimit.dual⟩ := isSuccLimit_toDual_iff

@[to_dual]
/--
theorem `not_isSuccLimit_iff` / 定理 `not_isSuccLimit_iff`

English:
theorem not_isSuccLimit_iff
  statement: ¬ IsSuccLimit a ↔ IsMin a ∨ ¬ IsSuccPrelimit a
  proof: by
  rw [isSuccLimit_iff]; rw [not_and_or]; rw [not_not]

@[deprecated IsPredLimit.isPredPrelimit (since := "2026-02-22")]

中文:
定理 not_isSuccLimit_iff
  结论: ¬ IsSuccLimit a ↔ IsMin a ∨ ¬ IsSuccPrelimit a
  证明: by
  rw [isSuccLimit_iff]; rw [not_and_or]; rw [not_not]

@[deprecated IsPredLimit.isPredPrelimit (since := "2026-02-22")]

Depends on / 依赖: isSuccLimit_iff, not_and_or, not_not
-/
theorem not_isSuccLimit_iff : ¬ IsSuccLimit a ↔ IsMin a ∨ ¬ IsSuccPrelimit a := by
  rw [isSuccLimit_iff]; rw [not_and_or]; rw [not_not]

@[deprecated IsPredLimit.isPredPrelimit (since := "2026-02-22")]
/--
theorem `not_isPredLimit_of_not_isPredPrelimit` / 定理 `not_isPredLimit_of_not_isPredPrelimit`

English:
theorem not_isPredLimit_of_not_isPredPrelimit
  statement: ¬ IsPredPrelimit a -> ¬ IsPredLimit a
  proof: mt IsPredLimit.isPredPrelimit

中文:
定理 not_isPredLimit_of_not_isPredPrelimit
  结论: ¬ IsPredPrelimit a -> ¬ IsPredLimit a
  证明: mt IsPredLimit.isPredPrelimit

Depends on / 依赖: IsPredLimit, IsPredLimit.isPredPrelimit, isPredPrelimit
-/
theorem not_isPredLimit_of_not_isPredPrelimit : ¬ IsPredPrelimit a -> ¬ IsPredLimit a :=
  mt IsPredLimit.isPredPrelimit

set_option linter.existingAttributeWarning false in
@[to_dual, deprecated IsSuccLimit.mk (since := "2026-04-19")]
/--
theorem `IsSuccPrelimit.isSuccLimit_of_not_isMin` / 定理 `IsSuccPrelimit.isSuccLimit_of_not_isMin`

English:
theorem IsSuccPrelimit.isSuccLimit_of_not_isMin
  given: (h : IsSuccPrelimit a) (ha : ¬ IsMin a)
  proof: ⟨ha, h⟩

中文:
定理 IsSuccPrelimit.isSuccLimit_of_not_isMin
  条件: (h : IsSuccPrelimit a) (ha : ¬ IsMin a)
  证明: ⟨ha, h⟩
-/
theorem IsSuccPrelimit.isSuccLimit_of_not_isMin (h : IsSuccPrelimit a) (ha : ¬ IsMin a) :
    IsSuccLimit a :=
  ⟨ha, h⟩

attribute [deprecated IsPredLimit.mk (since := "2026-04-19")]
IsPredPrelimit.isPredLimit_of_not_isMax

@[to_dual]
/--
theorem `isSuccPrelimit_iff_isSuccLimit_of_not_isMin` / 定理 `isSuccPrelimit_iff_isSuccLimit_of_not_isMin`

English:
theorem isSuccPrelimit_iff_isSuccLimit_of_not_isMin
  given: (h : ¬ IsMin a)
  proof: by
  simp [isSuccLimit_iff, h]

@[to_dual]

中文:
定理 isSuccPrelimit_iff_isSuccLimit_of_not_isMin
  条件: (h : ¬ IsMin a)
  证明: by
  simp [isSuccLimit_iff, h]

@[to_dual]

Depends on / 依赖: isSuccLimit_iff
-/
theorem isSuccPrelimit_iff_isSuccLimit_of_not_isMin (h : ¬ IsMin a) :
    IsSuccPrelimit a ↔ IsSuccLimit a := by
  simp [isSuccLimit_iff, h]

@[to_dual]
/--
theorem `isSuccPrelimit_iff_isSuccLimit` / 定理 `isSuccPrelimit_iff_isSuccLimit`

English:
theorem isSuccPrelimit_iff_isSuccLimit
  given: [NoMinOrder α]
  statement: IsSuccPrelimit a ↔ IsSuccLimit a
  proof: isSuccPrelimit_iff_isSuccLimit_of_not_isMin (not_isMin a)

@[to_dual] alias ⟨IsSuccPrelimit.isSuccLimit, _⟩ := isSuccPrelimit_iff_isSuccLimit

@[to_dual]

中文:
定理 isSuccPrelimit_iff_isSuccLimit
  条件: [NoMinOrder α]
  结论: IsSuccPrelimit a ↔ IsSuccLimit a
  证明: isSuccPrelimit_iff_isSuccLimit_of_not_isMin (not_isMin a)

@[to_dual] alias ⟨IsSuccPrelimit.isSuccLimit, _⟩ := isSuccPrelimit_iff_isSuccLimit

@[to_dual]

Depends on / 依赖: isSuccPrelimit_iff_isSuccLimit_of_not_isMin, not_isMin
-/
theorem isSuccPrelimit_iff_isSuccLimit [NoMinOrder α] : IsSuccPrelimit a ↔ IsSuccLimit a :=
  isSuccPrelimit_iff_isSuccLimit_of_not_isMin (not_isMin a)

@[to_dual] alias ⟨IsSuccPrelimit.isSuccLimit, _⟩ := isSuccPrelimit_iff_isSuccLimit

@[to_dual]
/--
theorem `_root_.IsMin.not_isSuccLimit` / 定理 `_root_.IsMin.not_isSuccLimit`

English:
theorem _root_.IsMin.not_isSuccLimit
  given: (h : IsMin a)
  statement: ¬ IsSuccLimit a
  proof: fun ha => ha.not_isMin h

@[to_dual]

中文:
定理 _root_.IsMin.not_isSuccLimit
  条件: (h : IsMin a)
  结论: ¬ IsSuccLimit a
  证明: fun ha => ha.not_isMin h

@[to_dual]
-/
protected theorem _root_.IsMin.not_isSuccLimit (h : IsMin a) : ¬ IsSuccLimit a :=
  fun ha => ha.not_isMin h

@[to_dual]
/--
theorem `_root_.IsMin.isSuccPrelimit` / 定理 `_root_.IsMin.isSuccPrelimit`

English:
theorem _root_.IsMin.isSuccPrelimit
  statement: IsMin a -> IsSuccPrelimit a
  proof: fun h _ hab =>
  not_isMin_of_lt hab.lt h

@[to_dual]

中文:
定理 _root_.IsMin.isSuccPrelimit
  结论: IsMin a -> IsSuccPrelimit a
  证明: fun h _ hab =>
  not_isMin_of_lt hab.lt h

@[to_dual]
-/
protected theorem _root_.IsMin.isSuccPrelimit : IsMin a -> IsSuccPrelimit a := fun h _ hab =>
  not_isMin_of_lt hab.lt h

@[to_dual]
/--
theorem `IsSuccLimit.nonempty_Iio` / 定理 `IsSuccLimit.nonempty_Iio`

English:
theorem IsSuccLimit.nonempty_Iio
  given: (h : IsSuccLimit a)
  statement: (Set.Iio a).Nonempty
  proof: not_isMin_iff.1 h.1

@[to_dual]

中文:
定理 IsSuccLimit.nonempty_Iio
  条件: (h : IsSuccLimit a)
  结论: (Set.Iio a).Nonempty
  证明: not_isMin_iff.1 h.1

@[to_dual]

Depends on / 依赖: not_isMin_iff
-/
theorem IsSuccLimit.nonempty_Iio (h : IsSuccLimit a) : (Set.Iio a).Nonempty :=
  not_isMin_iff.1 h.1

@[to_dual]
/--
theorem `IsSuccPrelimit.noMaxOrder_Iio` / 定理 `IsSuccPrelimit.noMaxOrder_Iio`

English:
theorem IsSuccPrelimit.noMaxOrder_Iio
  given: (h : IsSuccPrelimit a)
  statement: NoMaxOrder (Set.Iio a)
  proof: by
  refine ⟨fun ⟨b, hb⟩ => ?_⟩
  obtain ⟨c, hbc, hca⟩ := (not_covBy_iff hb).1 (h b)
  exact ⟨⟨c, hca⟩, hbc⟩

@[to_dual (attr := simp)]

中文:
定理 IsSuccPrelimit.noMaxOrder_Iio
  条件: (h : IsSuccPrelimit a)
  结论: NoMaxOrder (Set.Iio a)
  证明: by
  refine ⟨fun ⟨b, hb⟩ => ?_⟩
  obtain ⟨c, hbc, hca⟩ := (not_covBy_iff hb).1 (h b)
  exact ⟨⟨c, hca⟩, hbc⟩

@[to_dual (attr := simp)]

Depends on / 依赖: not_covBy_iff
-/
theorem IsSuccPrelimit.noMaxOrder_Iio (h : IsSuccPrelimit a) : NoMaxOrder (Set.Iio a) := by
  refine ⟨fun ⟨b, hb⟩ => ?_⟩
  obtain ⟨c, hbc, hca⟩ := (not_covBy_iff hb).1 (h b)
  exact ⟨⟨c, hca⟩, hbc⟩

@[to_dual (attr := simp)]
/--
theorem `isSuccPrelimit_bot` / 定理 `isSuccPrelimit_bot`

English:
theorem isSuccPrelimit_bot
  given: [OrderBot α]
  statement: IsSuccPrelimit (⊥ : α)
  proof: isMin_bot.isSuccPrelimit

@[to_dual (attr := simp)]

中文:
定理 isSuccPrelimit_bot
  条件: [OrderBot α]
  结论: IsSuccPrelimit (⊥ : α)
  证明: isMin_bot.isSuccPrelimit

@[to_dual (attr := simp)]

Depends on / 依赖: isMin_bot, isMin_bot.isSuccPrelimit, isSuccPrelimit
-/
theorem isSuccPrelimit_bot [OrderBot α] : IsSuccPrelimit (⊥ : α) :=
  isMin_bot.isSuccPrelimit

@[to_dual (attr := simp)]
/--
theorem `not_isSuccLimit_bot` / 定理 `not_isSuccLimit_bot`

English:
theorem not_isSuccLimit_bot
  given: [OrderBot α]
  statement: ¬ IsSuccLimit (⊥ : α)
  proof: isMin_bot.not_isSuccLimit

@[to_dual]

中文:
定理 not_isSuccLimit_bot
  条件: [OrderBot α]
  结论: ¬ IsSuccLimit (⊥ : α)
  证明: isMin_bot.not_isSuccLimit

@[to_dual]

Depends on / 依赖: isMin_bot, isMin_bot.not_isSuccLimit, not_isSuccLimit
-/
theorem not_isSuccLimit_bot [OrderBot α] : ¬ IsSuccLimit (⊥ : α) :=
  isMin_bot.not_isSuccLimit

@[to_dual]
/--
theorem `IsSuccLimit.bot_lt` / 定理 `IsSuccLimit.bot_lt`

English:
theorem IsSuccLimit.bot_lt
  given: [OrderBot α] (h : IsSuccLimit a)
  statement: ⊥ < a
  proof: not_isMin_iff_bot_lt.1 h.not_isMin

@[to_dual]

中文:
定理 IsSuccLimit.bot_lt
  条件: [OrderBot α] (h : IsSuccLimit a)
  结论: ⊥ < a
  证明: not_isMin_iff_bot_lt.1 h.not_isMin

@[to_dual]

Depends on / 依赖: h.not_isMin, not_isMin, not_isMin_iff_bot_lt
-/
theorem IsSuccLimit.bot_lt [OrderBot α] (h : IsSuccLimit a) : ⊥ < a :=
  not_isMin_iff_bot_lt.1 h.not_isMin

@[to_dual]
/--
theorem `IsSuccLimit.ne_bot` / 定理 `IsSuccLimit.ne_bot`

English:
theorem IsSuccLimit.ne_bot
  given: [OrderBot α] (h : IsSuccLimit a)
  statement: a != ⊥
  proof: h.bot_lt.ne'

中文:
定理 IsSuccLimit.ne_bot
  条件: [OrderBot α] (h : IsSuccLimit a)
  结论: a != ⊥
  证明: h.bot_lt.ne'

Depends on / 依赖: bot_lt, h.bot_lt.ne
-/
theorem IsSuccLimit.ne_bot [OrderBot α] (h : IsSuccLimit a) : a != ⊥ :=
  h.bot_lt.ne'

/--
theorem `IsSuccLimit.pos` / 定理 `IsSuccLimit.pos`

English:
theorem IsSuccLimit.pos
  given: [Zero α] [IsBotZeroClass α] (h : IsSuccLimit a)
  statement: 0 < a
  proof: let := IsBotZeroClass.toOrderBot α
  h.bot_lt

中文:
定理 IsSuccLimit.pos
  条件: [Zero α] [IsBotZeroClass α] (h : IsSuccLimit a)
  结论: 0 < a
  证明: let := IsBotZeroClass.toOrderBot α
  h.bot_lt

Depends on / 依赖: IsBotZeroClass, IsBotZeroClass.toOrderBot, bot_lt, h.bot_lt, toOrderBot
-/
theorem IsSuccLimit.pos [Zero α] [IsBotZeroClass α] (h : IsSuccLimit a) : 0 < a :=
  let := IsBotZeroClass.toOrderBot α
  h.bot_lt

/--
theorem `IsSuccLimit.ne_zero` / 定理 `IsSuccLimit.ne_zero`

English:
theorem IsSuccLimit.ne_zero
  given: [Zero α] [IsBotZeroClass α] (h : IsSuccLimit a)
  statement: a != 0
  proof: h.pos.ne'

@[to_dual]

中文:
定理 IsSuccLimit.ne_zero
  条件: [Zero α] [IsBotZeroClass α] (h : IsSuccLimit a)
  结论: a != 0
  证明: h.pos.ne'

@[to_dual]

Depends on / 依赖: h.pos.ne
-/
theorem IsSuccLimit.ne_zero [Zero α] [IsBotZeroClass α] (h : IsSuccLimit a) : a != 0 :=
  h.pos.ne'

@[to_dual]
/--
theorem `IsSuccPrelimit.subtypeVal` / 定理 `IsSuccPrelimit.subtypeVal`

English:
theorem IsSuccPrelimit.subtypeVal
  statement: {s : Set α} (hs : IsLowerSet s) {a : s}
  proof: by
  intro b hb
  have := ha ⟨b, hs hb.le a.2⟩
  rw [not_covBy_iff] at this
  · obtain ⟨c, hc, hc'⟩ := this
    exact hb.2 hc hc'
  · exact hb.lt

@[to_dual]

中文:
定理 IsSuccPrelimit.subtypeVal
  结论: {s : Set α} (hs : IsLowerSet s) {a : s}
  证明: by
  intro b hb
  have := ha ⟨b, hs hb.le a.2⟩
  rw [not_covBy_iff] at this
  · obtain ⟨c, hc, hc'⟩ := this
    exact hb.2 hc hc'
  · exact hb.lt

@[to_dual]

Depends on / 依赖: hb.le, hb.lt, not_covBy_iff
-/
theorem IsSuccPrelimit.subtypeVal {s : Set α} (hs : IsLowerSet s) {a : s}
    (ha : IsSuccPrelimit a) : IsSuccPrelimit a.1 := by
  intro b hb
  have := ha ⟨b, hs hb.le a.2⟩
  rw [not_covBy_iff] at this
  · obtain ⟨c, hc, hc'⟩ := this
    exact hb.2 hc hc'
  · exact hb.lt

@[to_dual]
/--
theorem `IsSuccLimit.subtypeVal` / 定理 `IsSuccLimit.subtypeVal`

English:
theorem IsSuccLimit.subtypeVal
  statement: {s : Set α} (hs : IsLowerSet s) {a : s}
  proof: by
  refine ⟨?_, ha.isSuccPrelimit.subtypeVal hs⟩
  have := ha.1
  rw [not_isMin_iff] at ⊢ this
  obtain ⟨b, hb⟩ := this
  exact ⟨b, hb⟩

中文:
定理 IsSuccLimit.subtypeVal
  结论: {s : Set α} (hs : IsLowerSet s) {a : s}
  证明: by
  refine ⟨?_, ha.isSuccPrelimit.subtypeVal hs⟩
  have := ha.1
  rw [not_isMin_iff] at ⊢ this
  obtain ⟨b, hb⟩ := this
  exact ⟨b, hb⟩

Depends on / 依赖: ha.isSuccPrelimit.subtypeVal, isSuccPrelimit, not_isMin_iff, subtypeVal
-/
theorem IsSuccLimit.subtypeVal {s : Set α} (hs : IsLowerSet s) {a : s}
    (ha : IsSuccLimit a) : IsSuccLimit a.1 := by
  refine ⟨?_, ha.isSuccPrelimit.subtypeVal hs⟩
  have := ha.1
  rw [not_isMin_iff] at ⊢ this
  obtain ⟨b, hb⟩ := this
  exact ⟨b, hb⟩

/-- Given `j < i` with `i` a successor pre-limit, `IsSuccPrelimit.mid` picks an arbitrary element
strictly between `j` and `i`. -/
@[to_dual
/-- Given `i < j` with `i` a predecessor pre-limit, `IsSuccPrelimit.mid` picks an arbitrary element
strictly between `i` and `j`. -/]
/--
Definition of `IsSuccPrelimit.mid` / `IsSuccPrelimit.mid` 的定义

English:
definition IsSuccPrelimit.mid
  signature: {i j : α} (hi : IsSuccPrelimit i) (hj : j < i)
  body: Classical.indefiniteDescription _ ((not_covBy_iff_nonempty_Ioo hj).mp <| hi j)

@[to_dual]

中文:
定义 IsSuccPrelimit.mid
  签名: {i j : α} (hi : IsSuccPrelimit i) (hj : j < i)
  定义体: Classical.indefiniteDescription _ ((not_covBy_iff_nonempty_Ioo hj).mp <| hi j)

@[to_dual]

Depends on / 依赖: Classical, Classical.indefiniteDescription, indefiniteDescription, not_covBy_iff_nonempty_Ioo
-/
noncomputable def IsSuccPrelimit.mid {i j : α} (hi : IsSuccPrelimit i) (hj : j < i) : Ioo j i :=
  Classical.indefiniteDescription _ ((not_covBy_iff_nonempty_Ioo hj).mp <| hi j)

@[to_dual]
/--
theorem `_root_.WithTop.isSuccPrelimit_iff` / 定理 `_root_.WithTop.isSuccPrelimit_iff`

English:
theorem _root_.WithTop.isSuccPrelimit_iff
  given: [NoMaxOrder α] {x : WithTop α}
  proof: by
  cases x with
  | coe x => simp [IsSuccPrelimit, WithTop.forall]
  | top => simp [IsSuccPrelimit]

@[to_dual]

中文:
定理 _root_.WithTop.isSuccPrelimit_iff
  条件: [NoMaxOrder α] {x : WithTop α}
  证明: by
  cases x with
  | coe x => simp [IsSuccPrelimit, WithTop.forall]
  | top => simp [IsSuccPrelimit]

@[to_dual]

Depends on / 依赖: IsSuccPrelimit, WithTop, WithTop.forall
-/
theorem _root_.WithTop.isSuccPrelimit_iff [NoMaxOrder α] {x : WithTop α} :
    IsSuccPrelimit x ↔ x = ⊤ ∨ exists y : α, x = y ∧ IsSuccPrelimit y := by
  cases x with
  | coe x => simp [IsSuccPrelimit, WithTop.forall]
  | top => simp [IsSuccPrelimit]

@[to_dual]
/--
theorem `IsSuccPrelimit.withTopCoe` / 定理 `IsSuccPrelimit.withTopCoe`

English:
theorem IsSuccPrelimit.withTopCoe
  given: {x : α} (h : IsSuccPrelimit x)
  proof: by
  simpa [IsSuccPrelimit, WithTop.forall]

@[to_dual (attr := simp)]

中文:
定理 IsSuccPrelimit.withTopCoe
  条件: {x : α} (h : IsSuccPrelimit x)
  证明: by
  simpa [IsSuccPrelimit, WithTop.forall]

@[to_dual (attr := simp)]

Depends on / 依赖: IsSuccPrelimit, WithTop, WithTop.forall
-/
theorem IsSuccPrelimit.withTopCoe {x : α} (h : IsSuccPrelimit x) :
    IsSuccPrelimit (x : WithTop α) := by
  simpa [IsSuccPrelimit, WithTop.forall]

@[to_dual (attr := simp)]
/--
theorem `_root_.WithTop.isSuccPrelimit_top` / 定理 `_root_.WithTop.isSuccPrelimit_top`

English:
theorem _root_.WithTop.isSuccPrelimit_top
  given: [NoMaxOrder α]
  statement: IsSuccPrelimit (⊤ : WithTop α)
  proof: by
  simp [WithTop.isSuccPrelimit_iff]

@[to_dual]

中文:
定理 _root_.WithTop.isSuccPrelimit_top
  条件: [NoMaxOrder α]
  结论: IsSuccPrelimit (⊤ : WithTop α)
  证明: by
  simp [WithTop.isSuccPrelimit_iff]

@[to_dual]

Depends on / 依赖: WithTop, WithTop.isSuccPrelimit_iff, isSuccPrelimit_iff
-/
theorem _root_.WithTop.isSuccPrelimit_top [NoMaxOrder α] : IsSuccPrelimit (⊤ : WithTop α) := by
  simp [WithTop.isSuccPrelimit_iff]

@[to_dual]
/--
theorem `_root_.WithTop.isSuccLimit_iff` / 定理 `_root_.WithTop.isSuccLimit_iff`

English:
theorem _root_.WithTop.isSuccLimit_iff
  given: [Nonempty α] [NoMaxOrder α] {x : WithTop α}
  proof: by
  cases x with
  | coe x => simp [Order.isSuccLimit_iff, WithTop.isSuccPrelimit_iff, WithTop.exists]
  | top => simp [Order.isSuccLimit_iff, WithTop.exists]

@[to_dual]

中文:
定理 _root_.WithTop.isSuccLimit_iff
  条件: [Nonempty α] [NoMaxOrder α] {x : WithTop α}
  证明: by
  cases x with
  | coe x => simp [Order.isSuccLimit_iff, WithTop.isSuccPrelimit_iff, WithTop.exists]
  | top => simp [Order.isSuccLimit_iff, WithTop.exists]

@[to_dual]

Depends on / 依赖: Order.isSuccLimit_iff, WithTop, WithTop.exists, WithTop.isSuccPrelimit_iff, isSuccLimit_iff, isSuccPrelimit_iff
-/
theorem _root_.WithTop.isSuccLimit_iff [Nonempty α] [NoMaxOrder α] {x : WithTop α} :
    IsSuccLimit x ↔ x = ⊤ ∨ exists y : α, x = y ∧ IsSuccLimit y := by
  cases x with
  | coe x => simp [Order.isSuccLimit_iff, WithTop.isSuccPrelimit_iff, WithTop.exists]
  | top => simp [Order.isSuccLimit_iff, WithTop.exists]

@[to_dual]
/--
theorem `IsSuccLimit.withTopCoe` / 定理 `IsSuccLimit.withTopCoe`

English:
theorem IsSuccLimit.withTopCoe
  given: {x : α} (h : IsSuccLimit x)
  proof: by
  simpa [isSuccLimit_iff, WithTop.exists, h.isSuccPrelimit.withTopCoe] using h.not_isMin

@[to_dual]

中文:
定理 IsSuccLimit.withTopCoe
  条件: {x : α} (h : IsSuccLimit x)
  证明: by
  simpa [isSuccLimit_iff, WithTop.exists, h.isSuccPrelimit.withTopCoe] using h.not_isMin

@[to_dual]

Depends on / 依赖: WithTop, WithTop.exists, h.isSuccPrelimit.withTopCoe, h.not_isMin, isSuccLimit_iff, isSuccPrelimit, not_isMin, withTopCoe
-/
theorem IsSuccLimit.withTopCoe {x : α} (h : IsSuccLimit x) :
    IsSuccLimit (x : WithTop α) := by
  simpa [isSuccLimit_iff, WithTop.exists, h.isSuccPrelimit.withTopCoe] using h.not_isMin

@[to_dual]
/--
theorem `_root_.WithTop.isSuccLimit_top` / 定理 `_root_.WithTop.isSuccLimit_top`

English:
theorem _root_.WithTop.isSuccLimit_top
  given: [Nonempty α] [NoMaxOrder α]
  proof: by
  simp [WithTop.isSuccLimit_iff]

@[to_dual]

中文:
定理 _root_.WithTop.isSuccLimit_top
  条件: [Nonempty α] [NoMaxOrder α]
  证明: by
  simp [WithTop.isSuccLimit_iff]

@[to_dual]

Depends on / 依赖: WithTop, WithTop.isSuccLimit_iff, isSuccLimit_iff
-/
theorem _root_.WithTop.isSuccLimit_top [Nonempty α] [NoMaxOrder α] :
    IsSuccLimit (⊤ : WithTop α) := by
  simp [WithTop.isSuccLimit_iff]

@[to_dual]
/--
theorem `_root_.WithTop.isPredPrelimit_iff` / 定理 `_root_.WithTop.isPredPrelimit_iff`

English:
theorem _root_.WithTop.isPredPrelimit_iff
  given: {x : WithTop α}
  proof: by
  cases x with
  | coe x => simp [IsPredPrelimit, Order.isPredLimit_iff, WithTop.forall]
  | top => simp

@[to_dual]

中文:
定理 _root_.WithTop.isPredPrelimit_iff
  条件: {x : WithTop α}
  证明: by
  cases x with
  | coe x => simp [IsPredPrelimit, Order.isPredLimit_iff, WithTop.forall]
  | top => simp

@[to_dual]

Depends on / 依赖: IsPredPrelimit, Order.isPredLimit_iff, WithTop, WithTop.forall, isPredLimit_iff
-/
theorem _root_.WithTop.isPredPrelimit_iff {x : WithTop α} :
    IsPredPrelimit x ↔ x = ⊤ ∨ exists y : α, x = y ∧ IsPredLimit y := by
  cases x with
  | coe x => simp [IsPredPrelimit, Order.isPredLimit_iff, WithTop.forall]
  | top => simp

@[to_dual]
/--
theorem `IsPredLimit.withTopCoe` / 定理 `IsPredLimit.withTopCoe`

English:
theorem IsPredLimit.withTopCoe
  given: {x : α} (h : IsPredLimit x)
  statement: IsPredLimit (x : WithTop α)
  proof: by
  simpa [WithTop.isPredPrelimit_iff, isPredLimit_iff, WithTop.exists] using h

中文:
定理 IsPredLimit.withTopCoe
  条件: {x : α} (h : IsPredLimit x)
  结论: IsPredLimit (x : WithTop α)
  证明: by
  simpa [WithTop.isPredPrelimit_iff, isPredLimit_iff, WithTop.exists] using h

Depends on / 依赖: WithTop, WithTop.exists, WithTop.isPredPrelimit_iff, isPredLimit_iff, isPredPrelimit_iff
-/
theorem IsPredLimit.withTopCoe {x : α} (h : IsPredLimit x) : IsPredLimit (x : WithTop α) := by
  simpa [WithTop.isPredPrelimit_iff, isPredLimit_iff, WithTop.exists] using h

variable [SuccOrder α]

@[to_dual]
/--
theorem `IsSuccPrelimit.isMax` / 定理 `IsSuccPrelimit.isMax`

English:
theorem IsSuccPrelimit.isMax
  given: (h : IsSuccPrelimit (succ a))
  statement: IsMax a
  proof: by
  by_contra H
  exact h a (covBy_succ_of_not_isMax H)

@[to_dual]

中文:
定理 IsSuccPrelimit.isMax
  条件: (h : IsSuccPrelimit (succ a))
  结论: IsMax a
  证明: by
  by_contra H
  exact h a (covBy_succ_of_not_isMax H)

@[to_dual]
-/
protected theorem IsSuccPrelimit.isMax (h : IsSuccPrelimit (succ a)) : IsMax a := by
  by_contra H
  exact h a (covBy_succ_of_not_isMax H)

@[to_dual]
/--
theorem `IsSuccLimit.isMax` / 定理 `IsSuccLimit.isMax`

English:
theorem IsSuccLimit.isMax
  given: (h : IsSuccLimit (succ a))
  statement: IsMax a
  proof: h.isSuccPrelimit.isMax

中文:
定理 IsSuccLimit.isMax
  条件: (h : IsSuccLimit (succ a))
  结论: IsMax a
  证明: h.isSuccPrelimit.isMax
-/
protected theorem IsSuccLimit.isMax (h : IsSuccLimit (succ a)) : IsMax a :=
  h.isSuccPrelimit.isMax

set_option linter.existingAttributeWarning false in
@[to_dual, deprecated IsSuccPrelimit.isMax (since := "2026-03-31")]
/--
theorem `not_isSuccPrelimit_succ_of_not_isMax` / 定理 `not_isSuccPrelimit_succ_of_not_isMax`

English:
theorem not_isSuccPrelimit_succ_of_not_isMax
  given: (ha : ¬ IsMax a)
  statement: ¬ IsSuccPrelimit (succ a)
  proof: mt IsSuccPrelimit.isMax ha

中文:
定理 not_isSuccPrelimit_succ_of_not_isMax
  条件: (ha : ¬ IsMax a)
  结论: ¬ IsSuccPrelimit (succ a)
  证明: mt IsSuccPrelimit.isMax ha

Depends on / 依赖: IsSuccPrelimit, IsSuccPrelimit.isMax
-/
theorem not_isSuccPrelimit_succ_of_not_isMax (ha : ¬ IsMax a) : ¬ IsSuccPrelimit (succ a) :=
  mt IsSuccPrelimit.isMax ha

attribute [deprecated IsPredPrelimit.isMin (since := "2026-03-31")]
not_isPredPrelimit_pred_of_not_isMin

set_option linter.existingAttributeWarning false in
@[to_dual, deprecated IsSuccLimit.isMax (since := "2026-03-31")]
/--
theorem `not_isSuccLimit_succ_of_not_isMax` / 定理 `not_isSuccLimit_succ_of_not_isMax`

English:
theorem not_isSuccLimit_succ_of_not_isMax
  given: (ha : ¬ IsMax a)
  statement: ¬ IsSuccLimit (succ a)
  proof: mt IsSuccLimit.isMax ha

中文:
定理 not_isSuccLimit_succ_of_not_isMax
  条件: (ha : ¬ IsMax a)
  结论: ¬ IsSuccLimit (succ a)
  证明: mt IsSuccLimit.isMax ha

Depends on / 依赖: IsSuccLimit, IsSuccLimit.isMax
-/
theorem not_isSuccLimit_succ_of_not_isMax (ha : ¬ IsMax a) : ¬ IsSuccLimit (succ a) :=
  mt IsSuccLimit.isMax ha

attribute [deprecated IsPredLimit.isMin (since := "2026-03-31")]
not_isPredLimit_pred_of_not_isMin

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual]
/--
theorem `IsSuccPrelimit.succ_ne` / 定理 `IsSuccPrelimit.succ_ne`

English:
theorem IsSuccPrelimit.succ_ne
  given: (h : IsSuccPrelimit a) (b : α)
  statement: succ b != a
  proof: by
  rintro rfl
  exact not_isMax _ h.isMax

@[to_dual]

中文:
定理 IsSuccPrelimit.succ_ne
  条件: (h : IsSuccPrelimit a) (b : α)
  结论: succ b != a
  证明: by
  rintro rfl
  exact not_isMax _ h.isMax

@[to_dual]

Depends on / 依赖: h.isMax, not_isMax
-/
theorem IsSuccPrelimit.succ_ne (h : IsSuccPrelimit a) (b : α) : succ b != a := by
  rintro rfl
  exact not_isMax _ h.isMax

@[to_dual]
/--
theorem `IsSuccLimit.succ_ne` / 定理 `IsSuccLimit.succ_ne`

English:
theorem IsSuccLimit.succ_ne
  given: (h : IsSuccLimit a) (b : α)
  statement: succ b != a
  proof: h.isSuccPrelimit.succ_ne b

@[to_dual (attr := simp)]

中文:
定理 IsSuccLimit.succ_ne
  条件: (h : IsSuccLimit a) (b : α)
  结论: succ b != a
  证明: h.isSuccPrelimit.succ_ne b

@[to_dual (attr := simp)]

Depends on / 依赖: h.isSuccPrelimit.succ_ne, isSuccPrelimit, succ_ne
-/
theorem IsSuccLimit.succ_ne (h : IsSuccLimit a) (b : α) : succ b != a :=
  h.isSuccPrelimit.succ_ne b

@[to_dual (attr := simp)]
/--
theorem `not_isSuccPrelimit_succ` / 定理 `not_isSuccPrelimit_succ`

English:
theorem not_isSuccPrelimit_succ
  given: (a : α)
  statement: ¬IsSuccPrelimit (succ a)
  proof: fun h => h.succ_ne _ rfl

@[to_dual (attr := simp)]

中文:
定理 not_isSuccPrelimit_succ
  条件: (a : α)
  结论: ¬IsSuccPrelimit (succ a)
  证明: fun h => h.succ_ne _ rfl

@[to_dual (attr := simp)]

Depends on / 依赖: h.succ_ne, succ_ne
-/
theorem not_isSuccPrelimit_succ (a : α) : ¬IsSuccPrelimit (succ a) := fun h => h.succ_ne _ rfl

@[to_dual (attr := simp)]
/--
theorem `not_isSuccLimit_succ` / 定理 `not_isSuccLimit_succ`

English:
theorem not_isSuccLimit_succ
  given: (a : α)
  statement: ¬IsSuccLimit (succ a)
  proof: fun h => h.succ_ne _ rfl

中文:
定理 not_isSuccLimit_succ
  条件: (a : α)
  结论: ¬IsSuccLimit (succ a)
  证明: fun h => h.succ_ne _ rfl

Depends on / 依赖: h.succ_ne, succ_ne
-/
theorem not_isSuccLimit_succ (a : α) : ¬IsSuccLimit (succ a) := fun h => h.succ_ne _ rfl

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α] [NoMaxOrder α]

@[to_dual]
/--
theorem `IsSuccPrelimit.isMin_of_noMax` / 定理 `IsSuccPrelimit.isMin_of_noMax`

English:
theorem IsSuccPrelimit.isMin_of_noMax
  given: (h : IsSuccPrelimit a)
  statement: IsMin a
  proof: by
  intro b hb
  rcases hb.exists_succ_iterate with ⟨_ | n, rfl⟩
  · exact le_rfl
  · rw [iterate_succ_apply'] at h
    exact (not_isSuccPrelimit_succ _ h).elim

@[to_dual (attr := simp)]

中文:
定理 IsSuccPrelimit.isMin_of_noMax
  条件: (h : IsSuccPrelimit a)
  结论: IsMin a
  证明: by
  intro b hb
  rcases hb.exists_succ_iterate with ⟨_ | n, rfl⟩
  · exact le_rfl
  · rw [iterate_succ_apply'] at h
    exact (not_isSuccPrelimit_succ _ h).elim

@[to_dual (attr := simp)]

Depends on / 依赖: exists_succ_iterate, hb.exists_succ_iterate, iterate_succ_apply, le_rfl, not_isSuccPrelimit_succ
-/
theorem IsSuccPrelimit.isMin_of_noMax (h : IsSuccPrelimit a) : IsMin a := by
  intro b hb
  rcases hb.exists_succ_iterate with ⟨_ | n, rfl⟩
  · exact le_rfl
  · rw [iterate_succ_apply'] at h
    exact (not_isSuccPrelimit_succ _ h).elim

@[to_dual (attr := simp)]
/--
theorem `isSuccPrelimit_iff_of_noMax` / 定理 `isSuccPrelimit_iff_of_noMax`

English:
theorem isSuccPrelimit_iff_of_noMax
  statement: IsSuccPrelimit a ↔ IsMin a
  proof: ⟨IsSuccPrelimit.isMin_of_noMax, IsMin.isSuccPrelimit⟩

@[to_dual (attr := simp)]

中文:
定理 isSuccPrelimit_iff_of_noMax
  结论: IsSuccPrelimit a ↔ IsMin a
  证明: ⟨IsSuccPrelimit.isMin_of_noMax, IsMin.isSuccPrelimit⟩

@[to_dual (attr := simp)]

Depends on / 依赖: IsMin.isSuccPrelimit, IsSuccPrelimit, IsSuccPrelimit.isMin_of_noMax, isMin_of_noMax, isSuccPrelimit
-/
theorem isSuccPrelimit_iff_of_noMax : IsSuccPrelimit a ↔ IsMin a :=
  ⟨IsSuccPrelimit.isMin_of_noMax, IsMin.isSuccPrelimit⟩

@[to_dual (attr := simp)]
/--
theorem `not_isSuccLimit_of_noMax` / 定理 `not_isSuccLimit_of_noMax`

English:
theorem not_isSuccLimit_of_noMax
  statement: ¬ IsSuccLimit a
  proof: fun h => h.not_isMin h.isSuccPrelimit.isMin_of_noMax

@[to_dual]

中文:
定理 not_isSuccLimit_of_noMax
  结论: ¬ IsSuccLimit a
  证明: fun h => h.not_isMin h.isSuccPrelimit.isMin_of_noMax

@[to_dual]

Depends on / 依赖: h.isSuccPrelimit.isMin_of_noMax, h.not_isMin, isMin_of_noMax, isSuccPrelimit, not_isMin
-/
theorem not_isSuccLimit_of_noMax : ¬ IsSuccLimit a :=
  fun h => h.not_isMin h.isSuccPrelimit.isMin_of_noMax

@[to_dual]
/--
theorem `not_isSuccPrelimit_of_noMax` / 定理 `not_isSuccPrelimit_of_noMax`

English:
theorem not_isSuccPrelimit_of_noMax
  given: [NoMinOrder α]
  statement: ¬ IsSuccPrelimit a
  proof: by simp

中文:
定理 not_isSuccPrelimit_of_noMax
  条件: [NoMinOrder α]
  结论: ¬ IsSuccPrelimit a
  证明: by simp
-/
theorem not_isSuccPrelimit_of_noMax [NoMinOrder α] : ¬ IsSuccPrelimit a := by simp

end IsSuccArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_dual]
/--
theorem `isSuccLimit_iff_of_orderBot` / 定理 `isSuccLimit_iff_of_orderBot`

English:
theorem isSuccLimit_iff_of_orderBot
  given: [OrderBot α]
  statement: IsSuccLimit a ↔ a != ⊥ ∧ IsSuccPrelimit a
  proof: by
  rw [isSuccLimit_iff]; rw [isMin_iff_eq_bot]

中文:
定理 isSuccLimit_iff_of_orderBot
  条件: [OrderBot α]
  结论: IsSuccLimit a ↔ a != ⊥ ∧ IsSuccPrelimit a
  证明: by
  rw [isSuccLimit_iff]; rw [isMin_iff_eq_bot]

Depends on / 依赖: isMin_iff_eq_bot, isSuccLimit_iff
-/
theorem isSuccLimit_iff_of_orderBot [OrderBot α] : IsSuccLimit a ↔ a != ⊥ ∧ IsSuccPrelimit a := by
  rw [isSuccLimit_iff]; rw [isMin_iff_eq_bot]

variable [SuccOrder α]

@[to_dual]
/--
theorem `isSuccPrelimit_of_succ_ne` / 定理 `isSuccPrelimit_of_succ_ne`

English:
theorem isSuccPrelimit_of_succ_ne
  given: (h : forall b, succ b != a)
  statement: IsSuccPrelimit a
  proof: fun b hba =>
  h b (CovBy.succ_eq hba)

@[to_dual]

中文:
定理 isSuccPrelimit_of_succ_ne
  条件: (h : 对任意 b, succ b != a)
  结论: IsSuccPrelimit a
  证明: fun b hba =>
  h b (CovBy.succ_eq hba)

@[to_dual]
-/
theorem isSuccPrelimit_of_succ_ne (h : forall b, succ b != a) : IsSuccPrelimit a := fun b hba =>
  h b (CovBy.succ_eq hba)

@[to_dual]
/--
theorem `not_isSuccPrelimit_iff_succ_eq` / 定理 `not_isSuccPrelimit_iff_succ_eq`

English:
theorem not_isSuccPrelimit_iff_succ_eq
  statement: ¬ IsSuccPrelimit a ↔ exists b, ¬ IsMax b ∧ succ b = a
  proof: by
  rw [not_isSuccPrelimit_iff]
  refine exists_congr fun b => ⟨fun hba => ⟨hba.lt.not_isMax, hba.succ_eq⟩, ?_⟩
  rintro ⟨h, rfl⟩
  exact covBy_succ_of_not_isMax h

中文:
定理 not_isSuccPrelimit_iff_succ_eq
  结论: ¬ IsSuccPrelimit a ↔ 存在 b, ¬ IsMax b ∧ succ b = a
  证明: by
  rw [not_isSuccPrelimit_iff]
  refine exists_congr fun b => ⟨fun hba => ⟨hba.lt.not_isMax, hba.succ_eq⟩, ?_⟩
  rintro ⟨h, rfl⟩
  exact covBy_succ_of_not_isMax h

Depends on / 依赖: covBy_succ_of_not_isMax, exists_congr, hba.lt.not_isMax, hba.succ_eq, not_isMax, not_isSuccPrelimit_iff, succ_eq
-/
theorem not_isSuccPrelimit_iff_succ_eq : ¬ IsSuccPrelimit a ↔ exists b, ¬ IsMax b ∧ succ b = a := by
  rw [not_isSuccPrelimit_iff]
  refine exists_congr fun b => ⟨fun hba => ⟨hba.lt.not_isMax, hba.succ_eq⟩, ?_⟩
  rintro ⟨h, rfl⟩
  exact covBy_succ_of_not_isMax h

/-- See `not_isSuccPrelimit_iff_succ_eq` for a version that states that `a` is a successor of a
value other than itself. -/
@[to_dual
/-- See `not_isPredPrelimit_iff_pred_eq` for a version that states that `a` is a predecessor of a
value other than itself. -/]
/--
theorem `mem_range_succ_of_not_isSuccPrelimit` / 定理 `mem_range_succ_of_not_isSuccPrelimit`

English:
theorem mem_range_succ_of_not_isSuccPrelimit
  given: (h : ¬ IsSuccPrelimit a)
  proof: by
  obtain ⟨b, hb⟩ := not_isSuccPrelimit_iff_succ_eq.1 h
  exact ⟨b, hb.2⟩

@[to_dual]

中文:
定理 mem_range_succ_of_not_isSuccPrelimit
  条件: (h : ¬ IsSuccPrelimit a)
  证明: by
  obtain ⟨b, hb⟩ := not_isSuccPrelimit_iff_succ_eq.1 h
  exact ⟨b, hb.2⟩

@[to_dual]

Depends on / 依赖: not_isSuccPrelimit_iff_succ_eq
-/
theorem mem_range_succ_of_not_isSuccPrelimit (h : ¬ IsSuccPrelimit a) :
    a in range (succ : α -> α) := by
  obtain ⟨b, hb⟩ := not_isSuccPrelimit_iff_succ_eq.1 h
  exact ⟨b, hb.2⟩

@[to_dual]
/--
theorem `mem_range_succ_or_isSuccPrelimit` / 定理 `mem_range_succ_or_isSuccPrelimit`

English:
theorem mem_range_succ_or_isSuccPrelimit
  given: (a)
  statement: a in range (succ : α -> α) ∨ IsSuccPrelimit a
  proof: or_iff_not_imp_right.2 mem_range_succ_of_not_isSuccPrelimit

@[to_dual]

中文:
定理 mem_range_succ_or_isSuccPrelimit
  条件: (a)
  结论: a in range (succ : α -> α) ∨ IsSuccPrelimit a
  证明: or_iff_not_imp_right.2 mem_range_succ_of_not_isSuccPrelimit

@[to_dual]

Depends on / 依赖: mem_range_succ_of_not_isSuccPrelimit, or_iff_not_imp_right
-/
theorem mem_range_succ_or_isSuccPrelimit (a) : a in range (succ : α -> α) ∨ IsSuccPrelimit a :=
or_iff_not_imp_right.2 mem_range_succ_of_not_isSuccPrelimit

@[to_dual]
/--
theorem `isMin_or_mem_range_succ_or_isSuccLimit` / 定理 `isMin_or_mem_range_succ_or_isSuccLimit`

English:
theorem isMin_or_mem_range_succ_or_isSuccLimit
  given: (a)
  proof: by
  rw [isSuccLimit_iff]
  have := mem_range_succ_or_isSuccPrelimit a
  tauto

@[to_dual isPredPrelimit_of_lt_pred]

中文:
定理 isMin_or_mem_range_succ_or_isSuccLimit
  条件: (a)
  证明: by
  rw [isSuccLimit_iff]
  have := mem_range_succ_or_isSuccPrelimit a
  tauto

@[to_dual isPredPrelimit_of_lt_pred]

Depends on / 依赖: isSuccLimit_iff, mem_range_succ_or_isSuccPrelimit
-/
theorem isMin_or_mem_range_succ_or_isSuccLimit (a) :
    IsMin a ∨ a in range (succ : α -> α) ∨ IsSuccLimit a := by
  rw [isSuccLimit_iff]
  have := mem_range_succ_or_isSuccPrelimit a
  tauto

@[to_dual isPredPrelimit_of_lt_pred]
/--
theorem `isSuccPrelimit_of_succ_lt` / 定理 `isSuccPrelimit_of_succ_lt`

English:
theorem isSuccPrelimit_of_succ_lt
  given: (H : forall a < b, succ a < b)
  statement: IsSuccPrelimit b
  proof: fun a hab => (H a hab.lt).ne hab.succ_eq

@[to_dual lt_pred]

中文:
定理 isSuccPrelimit_of_succ_lt
  条件: (H : 对任意 a < b, succ a < b)
  结论: IsSuccPrelimit b
  证明: fun a hab => (H a hab.lt).ne hab.succ_eq

@[to_dual lt_pred]

Depends on / 依赖: hab.lt, hab.succ_eq, succ_eq
-/
theorem isSuccPrelimit_of_succ_lt (H : forall a < b, succ a < b) : IsSuccPrelimit b :=
  fun a hab => (H a hab.lt).ne hab.succ_eq

@[to_dual lt_pred]
/--
theorem `IsSuccPrelimit.succ_lt` / 定理 `IsSuccPrelimit.succ_lt`

English:
theorem IsSuccPrelimit.succ_lt
  given: (hb : IsSuccPrelimit b) (ha : a < b)
  statement: succ a < b
  proof: by
  by_cases h : IsMax a
  · rwa [h.succ_eq]
  · rw [lt_iff_le_and_ne, succ_le_iff_of_not_isMax h]
    refine ⟨ha, fun hab => ?_⟩
    subst hab
    exact (h hb.isMax).elim

@[to_dual lt_pred]

中文:
定理 IsSuccPrelimit.succ_lt
  条件: (hb : IsSuccPrelimit b) (ha : a < b)
  结论: succ a < b
  证明: by
  by_cases h : IsMax a
  · rwa [h.succ_eq]
  · rw [lt_iff_le_and_ne, succ_le_iff_of_not_isMax h]
    refine ⟨ha, fun hab => ?_⟩
    subst hab
    exact (h hb.isMax).elim

@[to_dual lt_pred]

Depends on / 依赖: h.succ_eq, hb.isMax, lt_iff_le_and_ne, succ_eq, succ_le_iff_of_not_isMax
-/
theorem IsSuccPrelimit.succ_lt (hb : IsSuccPrelimit b) (ha : a < b) : succ a < b := by
  by_cases h : IsMax a
  · rwa [h.succ_eq]
  · rw [lt_iff_le_and_ne, succ_le_iff_of_not_isMax h]
    refine ⟨ha, fun hab => ?_⟩
    subst hab
    exact (h hb.isMax).elim

@[to_dual lt_pred]
/--
theorem `IsSuccLimit.succ_lt` / 定理 `IsSuccLimit.succ_lt`

English:
theorem IsSuccLimit.succ_lt
  given: (hb : IsSuccLimit b) (ha : a < b)
  statement: succ a < b
  proof: hb.isSuccPrelimit.succ_lt ha

@[to_dual lt_pred_iff]

中文:
定理 IsSuccLimit.succ_lt
  条件: (hb : IsSuccLimit b) (ha : a < b)
  结论: succ a < b
  证明: hb.isSuccPrelimit.succ_lt ha

@[to_dual lt_pred_iff]

Depends on / 依赖: hb.isSuccPrelimit.succ_lt, isSuccPrelimit, succ_lt
-/
theorem IsSuccLimit.succ_lt (hb : IsSuccLimit b) (ha : a < b) : succ a < b :=
  hb.isSuccPrelimit.succ_lt ha

@[to_dual lt_pred_iff]
/--
theorem `IsSuccPrelimit.succ_lt_iff` / 定理 `IsSuccPrelimit.succ_lt_iff`

English:
theorem IsSuccPrelimit.succ_lt_iff
  given: (hb : IsSuccPrelimit b)
  statement: succ a < b ↔ a < b
  proof: ⟨fun h => (le_succ a).trans_lt h, hb.succ_lt⟩

@[to_dual lt_pred_iff]

中文:
定理 IsSuccPrelimit.succ_lt_iff
  条件: (hb : IsSuccPrelimit b)
  结论: succ a < b ↔ a < b
  证明: ⟨fun h => (le_succ a).trans_lt h, hb.succ_lt⟩

@[to_dual lt_pred_iff]

Depends on / 依赖: hb.succ_lt, le_succ, succ_lt, trans_lt
-/
theorem IsSuccPrelimit.succ_lt_iff (hb : IsSuccPrelimit b) : succ a < b ↔ a < b :=
  ⟨fun h => (le_succ a).trans_lt h, hb.succ_lt⟩

@[to_dual lt_pred_iff]
/--
theorem `IsSuccLimit.succ_lt_iff` / 定理 `IsSuccLimit.succ_lt_iff`

English:
theorem IsSuccLimit.succ_lt_iff
  given: (hb : IsSuccLimit b)
  statement: succ a < b ↔ a < b
  proof: hb.isSuccPrelimit.succ_lt_iff

@[to_dual isPredPrelimit_iff_lt_pred]

中文:
定理 IsSuccLimit.succ_lt_iff
  条件: (hb : IsSuccLimit b)
  结论: succ a < b ↔ a < b
  证明: hb.isSuccPrelimit.succ_lt_iff

@[to_dual isPredPrelimit_iff_lt_pred]

Depends on / 依赖: hb.isSuccPrelimit.succ_lt_iff, isSuccPrelimit, succ_lt_iff
-/
theorem IsSuccLimit.succ_lt_iff (hb : IsSuccLimit b) : succ a < b ↔ a < b :=
  hb.isSuccPrelimit.succ_lt_iff

@[to_dual isPredPrelimit_iff_lt_pred]
/--
theorem `isSuccPrelimit_iff_succ_lt` / 定理 `isSuccPrelimit_iff_succ_lt`

English:
theorem isSuccPrelimit_iff_succ_lt
  statement: IsSuccPrelimit b ↔ forall a < b, succ a < b
  proof: ⟨fun hb _ => hb.succ_lt, isSuccPrelimit_of_succ_lt⟩

中文:
定理 isSuccPrelimit_iff_succ_lt
  结论: IsSuccPrelimit b ↔ 对任意 a < b, succ a < b
  证明: ⟨fun hb _ => hb.succ_lt, isSuccPrelimit_of_succ_lt⟩

Depends on / 依赖: hb.succ_lt, isSuccPrelimit_of_succ_lt, succ_lt
-/
theorem isSuccPrelimit_iff_succ_lt : IsSuccPrelimit b ↔ forall a < b, succ a < b :=
  ⟨fun hb _ => hb.succ_lt, isSuccPrelimit_of_succ_lt⟩

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual]
/--
theorem `isSuccPrelimit_iff_succ_ne` / 定理 `isSuccPrelimit_iff_succ_ne`

English:
theorem isSuccPrelimit_iff_succ_ne
  statement: IsSuccPrelimit a ↔ forall b, succ b != a
  proof: ⟨IsSuccPrelimit.succ_ne, isSuccPrelimit_of_succ_ne⟩

@[to_dual]

中文:
定理 isSuccPrelimit_iff_succ_ne
  结论: IsSuccPrelimit a ↔ 对任意 b, succ b != a
  证明: ⟨IsSuccPrelimit.succ_ne, isSuccPrelimit_of_succ_ne⟩

@[to_dual]

Depends on / 依赖: IsSuccPrelimit, IsSuccPrelimit.succ_ne, isSuccPrelimit_of_succ_ne, succ_ne
-/
theorem isSuccPrelimit_iff_succ_ne : IsSuccPrelimit a ↔ forall b, succ b != a :=
  ⟨IsSuccPrelimit.succ_ne, isSuccPrelimit_of_succ_ne⟩

@[to_dual]
/--
theorem `not_isSuccPrelimit_iff_mem_range_succ` / 定理 `not_isSuccPrelimit_iff_mem_range_succ`

English:
theorem not_isSuccPrelimit_iff_mem_range_succ
  statement: ¬ IsSuccPrelimit a ↔ a in range (succ : α -> α)
  proof: by
  simp_rw [isSuccPrelimit_iff_succ_ne, not_forall, not_ne_iff, mem_range]

@[deprecated (since := "2026-04-19")]
alias not_isSuccPrelimit_iff' := not_isSuccPrelimit_iff_mem_range_succ

中文:
定理 not_isSuccPrelimit_iff_mem_range_succ
  结论: ¬ IsSuccPrelimit a ↔ a in range (succ : α -> α)
  证明: by
  simp_rw [isSuccPrelimit_iff_succ_ne, not_forall, not_ne_iff, mem_range]

@[deprecated (since := "2026-04-19")]
alias not_isSuccPrelimit_iff' := not_isSuccPrelimit_iff_mem_range_succ

Depends on / 依赖: isSuccPrelimit_iff_succ_ne, mem_range, not_forall, not_ne_iff, simp_rw
-/
theorem not_isSuccPrelimit_iff_mem_range_succ : ¬ IsSuccPrelimit a ↔ a in range (succ : α -> α) := by
  simp_rw [isSuccPrelimit_iff_succ_ne, not_forall, not_ne_iff, mem_range]

@[deprecated (since := "2026-04-19")]
alias not_isSuccPrelimit_iff' := not_isSuccPrelimit_iff_mem_range_succ

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

@[to_dual]
/--
theorem `IsSuccPrelimit.isMin` / 定理 `IsSuccPrelimit.isMin`

English:
theorem IsSuccPrelimit.isMin
  given: (h : IsSuccPrelimit a)
  statement: IsMin a
  proof: fun b hb => by
  revert h
  refine Succ.rec (fun _ => le_rfl) (fun c _ H hc => ?_) hb
  have := hc.isMax.succ_eq
  rw [this] at hc ⊢
  exact H hc

@[to_dual (attr := simp)]

中文:
定理 IsSuccPrelimit.isMin
  条件: (h : IsSuccPrelimit a)
  结论: IsMin a
  证明: fun b hb => by
  revert h
  refine Succ.rec (fun _ => le_rfl) (fun c _ H hc => ?_) hb
  have := hc.isMax.succ_eq
  rw [this] at hc ⊢
  exact H hc

@[to_dual (attr := simp)]

Depends on / 依赖: degree_eq_weight_one
-/
protected theorem IsSuccPrelimit.isMin (h : IsSuccPrelimit a) : IsMin a := fun b hb => by
  revert h
  refine Succ.rec (fun _ => le_rfl) (fun c _ H hc => ?_) hb
  have := hc.isMax.succ_eq
  rw [this] at hc ⊢
  exact H hc

@[to_dual (attr := simp)]
/--
theorem `isSuccPrelimit_iff_isMin` / 定理 `isSuccPrelimit_iff_isMin`

English:
theorem isSuccPrelimit_iff_isMin
  statement: IsSuccPrelimit a ↔ IsMin a
  proof: ⟨IsSuccPrelimit.isMin, IsMin.isSuccPrelimit⟩

@[deprecated (since := "2026-04-19")]
alias isSuccPrelimit_iff := isSuccPrelimit_iff_isMin
@[deprecated (since := "2026-04-19")]
alias isPredPrelimit_iff := isPredPrelimit_iff_isMax

@[to_dual (attr := simp)]

中文:
定理 isSuccPrelimit_iff_isMin
  结论: IsSuccPrelimit a ↔ IsMin a
  证明: ⟨IsSuccPrelimit.isMin, IsMin.isSuccPrelimit⟩

@[deprecated (since := "2026-04-19")]
alias isSuccPrelimit_iff := isSuccPrelimit_iff_isMin
@[deprecated (since := "2026-04-19")]
alias isPredPrelimit_iff := isPredPrelimit_iff_isMax

@[to_dual (attr := simp)]

Depends on / 依赖: IsMin.isSuccPrelimit, IsSuccPrelimit, IsSuccPrelimit.isMin, isSuccPrelimit
-/
theorem isSuccPrelimit_iff_isMin : IsSuccPrelimit a ↔ IsMin a :=
  ⟨IsSuccPrelimit.isMin, IsMin.isSuccPrelimit⟩

@[deprecated (since := "2026-04-19")]
alias isSuccPrelimit_iff := isSuccPrelimit_iff_isMin
@[deprecated (since := "2026-04-19")]
alias isPredPrelimit_iff := isPredPrelimit_iff_isMax

@[to_dual (attr := simp)]
/--
theorem `not_isSuccLimit_of_isSuccArchimedean` / 定理 `not_isSuccLimit_of_isSuccArchimedean`

English:
theorem not_isSuccLimit_of_isSuccArchimedean
  statement: ¬ IsSuccLimit a
  proof: fun h => h.not_isMin h.isSuccPrelimit.isMin

@[deprecated (since := "2026-04-19")]
alias not_isSuccLimit := not_isSuccLimit_of_isSuccArchimedean
@[deprecated (since := "2026-04-19")]
alias not_isPredLimit := not_isPredLimit_of_isPredArchimedean

@[to_dual]

中文:
定理 not_isSuccLimit_of_isSuccArchimedean
  结论: ¬ IsSuccLimit a
  证明: fun h => h.not_isMin h.isSuccPrelimit.isMin

@[deprecated (since := "2026-04-19")]
alias not_isSuccLimit := not_isSuccLimit_of_isSuccArchimedean
@[deprecated (since := "2026-04-19")]
alias not_isPredLimit := not_isPredLimit_of_isPredArchimedean

@[to_dual]

Depends on / 依赖: h.isSuccPrelimit.isMin, h.not_isMin, isSuccPrelimit, not_isMin
-/
theorem not_isSuccLimit_of_isSuccArchimedean : ¬ IsSuccLimit a :=
fun h => h.not_isMin h.isSuccPrelimit.isMin

@[deprecated (since := "2026-04-19")]
alias not_isSuccLimit := not_isSuccLimit_of_isSuccArchimedean
@[deprecated (since := "2026-04-19")]
alias not_isPredLimit := not_isPredLimit_of_isPredArchimedean

@[to_dual]
/--
theorem `not_isSuccPrelimit_of_isSuccArchimedean` / 定理 `not_isSuccPrelimit_of_isSuccArchimedean`

English:
theorem not_isSuccPrelimit_of_isSuccArchimedean
  given: [NoMinOrder α]
  statement: ¬ IsSuccPrelimit a
  proof: by simp

@[deprecated (since := "2026-04-19")]
alias not_isSuccPrelimit := not_isSuccPrelimit_of_isSuccArchimedean
@[deprecated (since := "2026-04-19")]
alias not_isPredPrelimit := not_isPredPrelimit_of_isPredArchimedean

中文:
定理 not_isSuccPrelimit_of_isSuccArchimedean
  条件: [NoMinOrder α]
  结论: ¬ IsSuccPrelimit a
  证明: by simp

@[deprecated (since := "2026-04-19")]
alias not_isSuccPrelimit := not_isSuccPrelimit_of_isSuccArchimedean
@[deprecated (since := "2026-04-19")]
alias not_isPredPrelimit := not_isPredPrelimit_of_isPredArchimedean
-/
theorem not_isSuccPrelimit_of_isSuccArchimedean [NoMinOrder α] : ¬ IsSuccPrelimit a := by simp

@[deprecated (since := "2026-04-19")]
alias not_isSuccPrelimit := not_isSuccPrelimit_of_isSuccArchimedean
@[deprecated (since := "2026-04-19")]
alias not_isPredPrelimit := not_isPredPrelimit_of_isPredArchimedean

end IsSuccArchimedean

end PartialOrder

section LinearOrder

variable [LinearOrder α]

@[to_dual]
/--
theorem `IsSuccPrelimit.le_iff_forall_le` / 定理 `IsSuccPrelimit.le_iff_forall_le`

English:
theorem IsSuccPrelimit.le_iff_forall_le
  given: (h : IsSuccPrelimit a)
  statement: a <= b ↔ forall c < a, c <= b
  proof: by
  use fun ha c hc => hc.le.trans ha
  intro H
  by_contra! ha
  exact h b ⟨ha, fun c hb hc => (H c hc).not_gt hb⟩

@[to_dual]

中文:
定理 IsSuccPrelimit.le_iff_forall_le
  条件: (h : IsSuccPrelimit a)
  结论: a <= b ↔ 对任意 c < a, c <= b
  证明: by
  use fun ha c hc => hc.le.trans ha
  intro H
  by_contra! ha
  exact h b ⟨ha, fun c hb hc => (H c hc).not_gt hb⟩

@[to_dual]

Depends on / 依赖: hc.le.trans, not_gt
-/
theorem IsSuccPrelimit.le_iff_forall_le (h : IsSuccPrelimit a) : a <= b ↔ forall c < a, c <= b := by
  use fun ha c hc => hc.le.trans ha
  intro H
  by_contra! ha
  exact h b ⟨ha, fun c hb hc => (H c hc).not_gt hb⟩

@[to_dual]
/--
theorem `IsSuccLimit.le_iff_forall_le` / 定理 `IsSuccLimit.le_iff_forall_le`

English:
theorem IsSuccLimit.le_iff_forall_le
  given: (h : IsSuccLimit a)
  statement: a <= b ↔ forall c < a, c <= b
  proof: h.isSuccPrelimit.le_iff_forall_le

@[to_dual]

中文:
定理 IsSuccLimit.le_iff_forall_le
  条件: (h : IsSuccLimit a)
  结论: a <= b ↔ 对任意 c < a, c <= b
  证明: h.isSuccPrelimit.le_iff_forall_le

@[to_dual]

Depends on / 依赖: h.isSuccPrelimit.le_iff_forall_le, isSuccPrelimit, le_iff_forall_le
-/
theorem IsSuccLimit.le_iff_forall_le (h : IsSuccLimit a) : a <= b ↔ forall c < a, c <= b :=
  h.isSuccPrelimit.le_iff_forall_le

@[to_dual]
/--
theorem `IsSuccPrelimit.lt_iff_exists_lt` / 定理 `IsSuccPrelimit.lt_iff_exists_lt`

English:
theorem IsSuccPrelimit.lt_iff_exists_lt
  given: (h : IsSuccPrelimit b)
  statement: a < b ↔ exists c < b, a < c
  proof: by
  rw [← not_iff_not]
  simp [h.le_iff_forall_le]

@[to_dual]

中文:
定理 IsSuccPrelimit.lt_iff_exists_lt
  条件: (h : IsSuccPrelimit b)
  结论: a < b ↔ 存在 c < b, a < c
  证明: by
  rw [← not_iff_not]
  simp [h.le_iff_forall_le]

@[to_dual]

Depends on / 依赖: h.le_iff_forall_le, le_iff_forall_le, not_iff_not
-/
theorem IsSuccPrelimit.lt_iff_exists_lt (h : IsSuccPrelimit b) : a < b ↔ exists c < b, a < c := by
  rw [← not_iff_not]
  simp [h.le_iff_forall_le]

@[to_dual]
/--
theorem `IsSuccLimit.lt_iff_exists_lt` / 定理 `IsSuccLimit.lt_iff_exists_lt`

English:
theorem IsSuccLimit.lt_iff_exists_lt
  given: (h : IsSuccLimit b)
  statement: a < b ↔ exists c < b, a < c
  proof: h.isSuccPrelimit.lt_iff_exists_lt

@[to_dual]

中文:
定理 IsSuccLimit.lt_iff_exists_lt
  条件: (h : IsSuccLimit b)
  结论: a < b ↔ 存在 c < b, a < c
  证明: h.isSuccPrelimit.lt_iff_exists_lt

@[to_dual]

Depends on / 依赖: h.isSuccPrelimit.lt_iff_exists_lt, isSuccPrelimit, lt_iff_exists_lt
-/
theorem IsSuccLimit.lt_iff_exists_lt (h : IsSuccLimit b) : a < b ↔ exists c < b, a < c :=
  h.isSuccPrelimit.lt_iff_exists_lt

@[to_dual]
/--
lemma `_root_.IsLUB.isSuccPrelimit_of_notMem` / 引理 `_root_.IsLUB.isSuccPrelimit_of_notMem`

English:
lemma _root_.IsLUB.isSuccPrelimit_of_notMem
  given: {s : Set α} (hs : IsLUB s a) (ha : a ∉ s)
  proof: by
  intro b hb
  obtain ⟨c, hc, hbc, hca⟩ := hs.exists_between hb.lt
  obtain rfl := (hb.ge_of_gt hbc).antisymm hca
  contradiction

@[to_dual]

中文:
引理 _root_.IsLUB.isSuccPrelimit_of_notMem
  条件: {s : Set α} (hs : IsLUB s a) (ha : a ∉ s)
  证明: by
  intro b hb
  obtain ⟨c, hc, hbc, hca⟩ := hs.exists_between hb.lt
  obtain rfl := (hb.ge_of_gt hbc).antisymm hca
  contradiction

@[to_dual]

Depends on / 依赖: antisymm, exists_between, ge_of_gt, hb.ge_of_gt, hb.lt, hs.exists_between
-/
lemma _root_.IsLUB.isSuccPrelimit_of_notMem {s : Set α} (hs : IsLUB s a) (ha : a ∉ s) :
    IsSuccPrelimit a := by
  intro b hb
  obtain ⟨c, hc, hbc, hca⟩ := hs.exists_between hb.lt
  obtain rfl := (hb.ge_of_gt hbc).antisymm hca
  contradiction

@[to_dual]
/--
lemma `_root_.IsLUB.mem_of_not_isSuccPrelimit` / 引理 `_root_.IsLUB.mem_of_not_isSuccPrelimit`

English:
lemma _root_.IsLUB.mem_of_not_isSuccPrelimit
  given: {s : Set α} (hs : IsLUB s a) (ha : ¬IsSuccPrelimit a)
  proof: ha.imp_symm hs.isSuccPrelimit_of_notMem

@[to_dual]

中文:
引理 _root_.IsLUB.mem_of_not_isSuccPrelimit
  条件: {s : Set α} (hs : IsLUB s a) (ha : ¬IsSuccPrelimit a)
  证明: ha.imp_symm hs.isSuccPrelimit_of_notMem

@[to_dual]

Depends on / 依赖: ha.imp_symm, hs.isSuccPrelimit_of_notMem, imp_symm, isSuccPrelimit_of_notMem
-/
lemma _root_.IsLUB.mem_of_not_isSuccPrelimit {s : Set α} (hs : IsLUB s a) (ha : ¬IsSuccPrelimit a) :
    a in s :=
  ha.imp_symm hs.isSuccPrelimit_of_notMem

@[to_dual]
/--
lemma `_root_.IsLUB.isSuccLimit_of_notMem` / 引理 `_root_.IsLUB.isSuccLimit_of_notMem`

English:
lemma _root_.IsLUB.isSuccLimit_of_notMem
  statement: {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty)
  proof: by
  refine ⟨?_, hs.isSuccPrelimit_of_notMem ha⟩
  obtain ⟨b, hb⟩ := hs'
  obtain rfl | hb := (hs.1 hb).eq_or_lt
  · contradiction
  · exact hb.not_isMin

@[to_dual]

中文:
引理 _root_.IsLUB.isSuccLimit_of_notMem
  结论: {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty)
  证明: by
  refine ⟨?_, hs.isSuccPrelimit_of_notMem ha⟩
  obtain ⟨b, hb⟩ := hs'
  obtain rfl | hb := (hs.1 hb).eq_or_lt
  · contradiction
  · exact hb.not_isMin

@[to_dual]

Depends on / 依赖: eq_or_lt, hb.not_isMin, hs.isSuccPrelimit_of_notMem, isSuccPrelimit_of_notMem, not_isMin
-/
lemma _root_.IsLUB.isSuccLimit_of_notMem {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty)
    (ha : a ∉ s) : IsSuccLimit a := by
  refine ⟨?_, hs.isSuccPrelimit_of_notMem ha⟩
  obtain ⟨b, hb⟩ := hs'
  obtain rfl | hb := (hs.1 hb).eq_or_lt
  · contradiction
  · exact hb.not_isMin

@[to_dual]
/--
lemma `_root_.IsLUB.mem_of_not_isSuccLimit` / 引理 `_root_.IsLUB.mem_of_not_isSuccLimit`

English:
lemma _root_.IsLUB.mem_of_not_isSuccLimit
  statement: {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty)
  proof: ha.imp_symm hs.isSuccLimit_of_notMem hs'

@[to_dual]

中文:
引理 _root_.IsLUB.mem_of_not_isSuccLimit
  结论: {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty)
  证明: ha.imp_symm hs.isSuccLimit_of_notMem hs'

@[to_dual]

Depends on / 依赖: ha.imp_symm, hs.isSuccLimit_of_notMem, imp_symm, isSuccLimit_of_notMem
-/
lemma _root_.IsLUB.mem_of_not_isSuccLimit {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty)
    (ha : ¬IsSuccLimit a) : a in s :=
ha.imp_symm hs.isSuccLimit_of_notMem hs'

@[to_dual]
/--
theorem `IsSuccPrelimit.isLUB_Iio` / 定理 `IsSuccPrelimit.isLUB_Iio`

English:
theorem IsSuccPrelimit.isLUB_Iio
  given: (ha : IsSuccPrelimit a)
  statement: IsLUB (Iio a) a
  proof: by
  refine ⟨fun _ => le_of_lt, fun b hb => le_of_forall_lt fun c hc => ?_⟩
  obtain ⟨d, hd, hd'⟩ := ha.lt_iff_exists_lt.1 hc
  exact hd'.trans_le (hb hd)

@[to_dual]

中文:
定理 IsSuccPrelimit.isLUB_Iio
  条件: (ha : IsSuccPrelimit a)
  结论: IsLUB (Iio a) a
  证明: by
  refine ⟨fun _ => le_of_lt, fun b hb => le_of_forall_lt fun c hc => ?_⟩
  obtain ⟨d, hd, hd'⟩ := ha.lt_iff_exists_lt.1 hc
  exact hd'.trans_le (hb hd)

@[to_dual]

Depends on / 依赖: ha.lt_iff_exists_lt, le_of_forall_lt, le_of_lt, lt_iff_exists_lt, trans_le
-/
theorem IsSuccPrelimit.isLUB_Iio (ha : IsSuccPrelimit a) : IsLUB (Iio a) a := by
  refine ⟨fun _ => le_of_lt, fun b hb => le_of_forall_lt fun c hc => ?_⟩
  obtain ⟨d, hd, hd'⟩ := ha.lt_iff_exists_lt.1 hc
  exact hd'.trans_le (hb hd)

@[to_dual]
/--
theorem `IsSuccLimit.isLUB_Iio` / 定理 `IsSuccLimit.isLUB_Iio`

English:
theorem IsSuccLimit.isLUB_Iio
  given: (ha : IsSuccLimit a)
  statement: IsLUB (Iio a) a
  proof: ha.isSuccPrelimit.isLUB_Iio

@[to_dual]

中文:
定理 IsSuccLimit.isLUB_Iio
  条件: (ha : IsSuccLimit a)
  结论: IsLUB (Iio a) a
  证明: ha.isSuccPrelimit.isLUB_Iio

@[to_dual]

Depends on / 依赖: ha.isSuccPrelimit.isLUB_Iio, isLUB_Iio, isSuccPrelimit
-/
theorem IsSuccLimit.isLUB_Iio (ha : IsSuccLimit a) : IsLUB (Iio a) a :=
  ha.isSuccPrelimit.isLUB_Iio

@[to_dual]
/--
theorem `isLUB_Iio_iff_isSuccPrelimit` / 定理 `isLUB_Iio_iff_isSuccPrelimit`

English:
theorem isLUB_Iio_iff_isSuccPrelimit
  statement: IsLUB (Iio a) a ↔ IsSuccPrelimit a
  proof: by
  refine ⟨fun ha b hb => ?_, IsSuccPrelimit.isLUB_Iio⟩
  rw [hb.Iio_eq] at ha
  obtain rfl := isLUB_Iic.unique ha
  cases hb.lt.false

中文:
定理 isLUB_Iio_iff_isSuccPrelimit
  结论: IsLUB (Iio a) a ↔ IsSuccPrelimit a
  证明: by
  refine ⟨fun ha b hb => ?_, IsSuccPrelimit.isLUB_Iio⟩
  rw [hb.Iio_eq] at ha
  obtain rfl := isLUB_Iic.unique ha
  cases hb.lt.false

Depends on / 依赖: Iio_eq, IsSuccPrelimit, IsSuccPrelimit.isLUB_Iio, hb.Iio_eq, hb.lt.false, isLUB_Iic, isLUB_Iic.unique, isLUB_Iio, unique
-/
theorem isLUB_Iio_iff_isSuccPrelimit : IsLUB (Iio a) a ↔ IsSuccPrelimit a := by
  refine ⟨fun ha b hb => ?_, IsSuccPrelimit.isLUB_Iio⟩
  rw [hb.Iio_eq] at ha
  obtain rfl := isLUB_Iic.unique ha
  cases hb.lt.false

variable [SuccOrder α]

@[to_dual pred_le_iff]
/--
theorem `IsSuccPrelimit.le_succ_iff` / 定理 `IsSuccPrelimit.le_succ_iff`

English:
theorem IsSuccPrelimit.le_succ_iff
  given: (hb : IsSuccPrelimit b)
  statement: b <= succ a ↔ b <= a
  proof: le_iff_le_iff_lt_iff_lt.2 hb.succ_lt_iff

@[to_dual pred_le_iff]

中文:
定理 IsSuccPrelimit.le_succ_iff
  条件: (hb : IsSuccPrelimit b)
  结论: b <= succ a ↔ b <= a
  证明: le_iff_le_iff_lt_iff_lt.2 hb.succ_lt_iff

@[to_dual pred_le_iff]

Depends on / 依赖: hb.succ_lt_iff, le_iff_le_iff_lt_iff_lt, succ_lt_iff
-/
theorem IsSuccPrelimit.le_succ_iff (hb : IsSuccPrelimit b) : b <= succ a ↔ b <= a :=
  le_iff_le_iff_lt_iff_lt.2 hb.succ_lt_iff

@[to_dual pred_le_iff]
/--
theorem `IsSuccLimit.le_succ_iff` / 定理 `IsSuccLimit.le_succ_iff`

English:
theorem IsSuccLimit.le_succ_iff
  given: (hb : IsSuccLimit b)
  statement: b <= succ a ↔ b <= a
  proof: hb.isSuccPrelimit.le_succ_iff

中文:
定理 IsSuccLimit.le_succ_iff
  条件: (hb : IsSuccLimit b)
  结论: b <= succ a ↔ b <= a
  证明: hb.isSuccPrelimit.le_succ_iff

Depends on / 依赖: hb.isSuccPrelimit.le_succ_iff, isSuccPrelimit, le_succ_iff
-/
theorem IsSuccLimit.le_succ_iff (hb : IsSuccLimit b) : b <= succ a ↔ b <= a :=
  hb.isSuccPrelimit.le_succ_iff

end LinearOrder

end Order

/-! ### Induction principles -/

variable {motive : α -> Sort*}

namespace Order

section isSuccPrelimitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α]
  (succ : forall a, ¬IsMax a -> motive (succ a)) (isSuccPrelimit : forall a, IsSuccPrelimit a -> motive a)

variable (b) in
open scoped Classical in
/-- A value can be built by building it on successors and successor pre-limits. -/
@[to_dual (attr := elab_as_elim)
/-- A value can be built by building it on predecessors and predecessor pre-limits. -/]
/--
Definition of `isSuccPrelimitRecOn` / `isSuccPrelimitRecOn` 的定义

English:
definition isSuccPrelimitRecOn
  signature: : motive b
  body: if hb : IsSuccPrelimit b then isSuccPrelimit b hb else
    haveI H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 hb)
    cast (congr_arg motive H.2) (succ _ H.1)

@[to_dual]

中文:
定义 isSuccPrelimitRecOn
  签名: : motive b
  定义体: if hb : IsSuccPrelimit b then isSuccPrelimit b hb else
    haveI H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 hb)
    cast (congr_arg motive H.2) (succ _ H.1)

@[to_dual]

Depends on / 依赖: Classical, Classical.choose_spec, IsSuccPrelimit, choose_spec, congr_arg, isSuccPrelimit, motive, not_isSuccPrelimit_iff_succ_eq
-/
noncomputable def isSuccPrelimitRecOn : motive b :=
  if hb : IsSuccPrelimit b then isSuccPrelimit b hb else
    haveI H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 hb)
    cast (congr_arg motive H.2) (succ _ H.1)

@[to_dual]
/--
theorem `isSuccPrelimitRecOn_of_isSuccPrelimit` / 定理 `isSuccPrelimitRecOn_of_isSuccPrelimit`

English:
theorem isSuccPrelimitRecOn_of_isSuccPrelimit
  given: (hb : IsSuccPrelimit b)
  proof: dif_pos hb

中文:
定理 isSuccPrelimitRecOn_of_isSuccPrelimit
  条件: (hb : IsSuccPrelimit b)
  证明: dif_pos hb

Depends on / 依赖: dif_pos
-/
theorem isSuccPrelimitRecOn_of_isSuccPrelimit (hb : IsSuccPrelimit b) :
    isSuccPrelimitRecOn b succ isSuccPrelimit = isSuccPrelimit b hb :=
  dif_pos hb

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α]
  (succ : forall a, ¬IsMax a -> motive (succ a)) (isSuccPrelimit : forall a, IsSuccPrelimit a -> motive a)

@[to_dual]
/--
theorem `isSuccPrelimitRecOn_succ_of_not_isMax` / 定理 `isSuccPrelimitRecOn_succ_of_not_isMax`

English:
theorem isSuccPrelimitRecOn_succ_of_not_isMax
  given: (hb : ¬IsMax b)
  proof: by
  have hb' := mt IsSuccPrelimit.isMax hb
  have H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 hb')
  rw [isSuccPrelimitRecOn]; rw [dif_neg hb']; rw [cast_eq_iff_heq]
  congr!
  exact (succ_eq_succ_iff_of_not_isMax H.1 hb).1 H.2

@[to_dual (attr := simp)]

中文:
定理 isSuccPrelimitRecOn_succ_of_not_isMax
  条件: (hb : ¬IsMax b)
  证明: by
  have hb' := mt IsSuccPrelimit.isMax hb
  have H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 hb')
  rw [isSuccPrelimitRecOn]; rw [dif_neg hb']; rw [cast_eq_iff_heq]
  congr!
  exact (succ_eq_succ_iff_of_not_isMax H.1 hb).1 H.2

@[to_dual (attr := simp)]

Depends on / 依赖: Classical, Classical.choose_spec, IsSuccPrelimit, IsSuccPrelimit.isMax, cast_eq_iff_heq, choose_spec, dif_neg, isSuccPrelimitRecOn, not_isSuccPrelimit_iff_succ_eq, succ_eq_succ_iff_of_not_isMax
-/
theorem isSuccPrelimitRecOn_succ_of_not_isMax (hb : ¬IsMax b) :
    isSuccPrelimitRecOn (Order.succ b) succ isSuccPrelimit = succ b hb := by
  have hb' := mt IsSuccPrelimit.isMax hb
  have H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 hb')
  rw [isSuccPrelimitRecOn]; rw [dif_neg hb']; rw [cast_eq_iff_heq]
  congr!
  exact (succ_eq_succ_iff_of_not_isMax H.1 hb).1 H.2

@[to_dual (attr := simp)]
/--
theorem `isSuccPrelimitRecOn_succ` / 定理 `isSuccPrelimitRecOn_succ`

English:
theorem isSuccPrelimitRecOn_succ
  given: [NoMaxOrder α] (b : α)
  proof: isSuccPrelimitRecOn_succ_of_not_isMax ..

中文:
定理 isSuccPrelimitRecOn_succ
  条件: [NoMaxOrder α] (b : α)
  证明: isSuccPrelimitRecOn_succ_of_not_isMax ..

Depends on / 依赖: isSuccPrelimitRecOn_succ_of_not_isMax
-/
theorem isSuccPrelimitRecOn_succ [NoMaxOrder α] (b : α) :
    isSuccPrelimitRecOn (Order.succ b) succ isSuccPrelimit = succ b (not_isMax b) :=
  isSuccPrelimitRecOn_succ_of_not_isMax ..

end LinearOrder

end isSuccPrelimitRecOn

section isSuccLimitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α]
  (isMin : forall a, IsMin a -> motive a) (succ : forall a, ¬IsMax a -> motive (succ a))
  (isSuccLimit : forall a, IsSuccLimit a -> motive a)

variable (b) in
open scoped Classical in
/-- A value can be built by building it on minimal elements, successors,
and successor limits. -/
@[to_dual (attr := elab_as_elim)
/-- A value can be built by building it on maximal elements, predecessors,
and predecessor limits. -/]
/--
Definition of `isSuccLimitRecOn` / `isSuccLimitRecOn` 的定义

English:
definition isSuccLimitRecOn
  signature: : motive b
  body: isSuccPrelimitRecOn b succ fun a ha =>
    if h : IsMin a then isMin a h else isSuccLimit a ⟨h, ha⟩

@[to_dual (attr := simp)]

中文:
定义 isSuccLimitRecOn
  签名: : motive b
  定义体: isSuccPrelimitRecOn b succ fun a ha =>
    if h : IsMin a then isMin a h else isSuccLimit a ⟨h, ha⟩

@[to_dual (attr := simp)]

Depends on / 依赖: isSuccLimit, isSuccPrelimitRecOn
-/
noncomputable def isSuccLimitRecOn : motive b :=
  isSuccPrelimitRecOn b succ fun a ha =>
    if h : IsMin a then isMin a h else isSuccLimit a ⟨h, ha⟩

@[to_dual (attr := simp)]
/--
theorem `isSuccLimitRecOn_of_isSuccLimit` / 定理 `isSuccLimitRecOn_of_isSuccLimit`

English:
theorem isSuccLimitRecOn_of_isSuccLimit
  given: (hb : IsSuccLimit b)
  proof: by
  rw [isSuccLimitRecOn]; rw [isSuccPrelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit]; rw [dif_neg hb.not_isMin]

中文:
定理 isSuccLimitRecOn_of_isSuccLimit
  条件: (hb : IsSuccLimit b)
  证明: by
  rw [isSuccLimitRecOn]; rw [isSuccPrelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit]; rw [dif_neg hb.not_isMin]

Depends on / 依赖: dif_neg, hb.isSuccPrelimit, hb.not_isMin, isSuccLimitRecOn, isSuccPrelimit, isSuccPrelimitRecOn_of_isSuccPrelimit, not_isMin
-/
theorem isSuccLimitRecOn_of_isSuccLimit (hb : IsSuccLimit b) :
    isSuccLimitRecOn b isMin succ isSuccLimit = isSuccLimit b hb := by
  rw [isSuccLimitRecOn]; rw [isSuccPrelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit]; rw [dif_neg hb.not_isMin]

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α]
  (isMin : forall a, IsMin a -> motive a) (succ : forall a, ¬IsMax a -> motive (succ a))
  (isSuccLimit : forall a, IsSuccLimit a -> motive a)

@[to_dual]
/--
theorem `isSuccLimitRecOn_succ_of_not_isMax` / 定理 `isSuccLimitRecOn_succ_of_not_isMax`

English:
theorem isSuccLimitRecOn_succ_of_not_isMax
  given: (hb : ¬IsMax b)
  proof: by
  rw [isSuccLimitRecOn]; rw [isSuccPrelimitRecOn_succ_of_not_isMax]

@[to_dual (attr := simp)]

中文:
定理 isSuccLimitRecOn_succ_of_not_isMax
  条件: (hb : ¬IsMax b)
  证明: by
  rw [isSuccLimitRecOn]; rw [isSuccPrelimitRecOn_succ_of_not_isMax]

@[to_dual (attr := simp)]

Depends on / 依赖: isSuccLimitRecOn, isSuccPrelimitRecOn_succ_of_not_isMax
-/
theorem isSuccLimitRecOn_succ_of_not_isMax (hb : ¬IsMax b) :
    isSuccLimitRecOn (Order.succ b) isMin succ isSuccLimit = succ b hb := by
  rw [isSuccLimitRecOn]; rw [isSuccPrelimitRecOn_succ_of_not_isMax]

@[to_dual (attr := simp)]
/--
theorem `isSuccLimitRecOn_succ` / 定理 `isSuccLimitRecOn_succ`

English:
theorem isSuccLimitRecOn_succ
  given: [NoMaxOrder α] (b : α)
  proof: isSuccLimitRecOn_succ_of_not_isMax isMin succ isSuccLimit _

@[to_dual]

中文:
定理 isSuccLimitRecOn_succ
  条件: [NoMaxOrder α] (b : α)
  证明: isSuccLimitRecOn_succ_of_not_isMax isMin succ isSuccLimit _

@[to_dual]

Depends on / 依赖: isSuccLimit, isSuccLimitRecOn_succ_of_not_isMax
-/
theorem isSuccLimitRecOn_succ [NoMaxOrder α] (b : α) :
    isSuccLimitRecOn (Order.succ b) isMin succ isSuccLimit = succ b (not_isMax b) :=
  isSuccLimitRecOn_succ_of_not_isMax isMin succ isSuccLimit _

@[to_dual]
/--
theorem `isSuccLimitRecOn_of_isMin` / 定理 `isSuccLimitRecOn_of_isMin`

English:
theorem isSuccLimitRecOn_of_isMin
  given: (hb : IsMin b)
  proof: by
  rw [isSuccLimitRecOn]; rw [isSuccPrelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit]; rw [dif_pos hb]

中文:
定理 isSuccLimitRecOn_of_isMin
  条件: (hb : IsMin b)
  证明: by
  rw [isSuccLimitRecOn]; rw [isSuccPrelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit]; rw [dif_pos hb]

Depends on / 依赖: dif_pos, hb.isSuccPrelimit, isSuccLimitRecOn, isSuccPrelimit, isSuccPrelimitRecOn_of_isSuccPrelimit
-/
theorem isSuccLimitRecOn_of_isMin (hb : IsMin b) :
    isSuccLimitRecOn b isMin succ isSuccLimit = isMin b hb := by
  rw [isSuccLimitRecOn]; rw [isSuccPrelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit]; rw [dif_pos hb]

end LinearOrder

end isSuccLimitRecOn

end Order

open Order

namespace SuccOrder

section prelimitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α] [WellFoundedLT α]
  (succ : forall a, ¬IsMax a -> motive a -> motive (Order.succ a))
  (isSuccPrelimit : forall a, IsSuccPrelimit a -> (forall b < a, motive b) -> motive a)

variable (b) in
open scoped Classical in
/-- Recursion principle on a well-founded partial `SuccOrder`. -/
@[to_dual (attr := elab_as_elim)
/-- Recursion principle on a well-founded partial `PredOrder`. -/]
/--
Definition of `prelimitRecOn` / `prelimitRecOn` 的定义

English:
definition prelimitRecOn
  signature: : motive b
  body: wellFounded_lt.fix
    (fun a IH => if h : IsSuccPrelimit a then isSuccPrelimit a h IH else
      haveI H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 h)
      cast (congr_arg motive H.2) (succ _ H.1 <| IH _ <| H.2.subst <| lt_succ_of_not_isMax H.1))
    b

@[to_dual (attr := simp)]

中文:
定义 prelimitRecOn
  签名: : motive b
  定义体: wellFounded_lt.fix
    (fun a IH => if h : IsSuccPrelimit a then isSuccPrelimit a h IH else
      haveI H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 h)
      cast (congr_arg motive H.2) (succ _ H.1 <| IH _ <| H.2.subst <| lt_succ_of_not_isMax H.1))
    b

@[to_dual (attr := simp)]

Depends on / 依赖: Classical, Classical.choose_spec, IsSuccPrelimit, choose_spec, congr_arg, isSuccPrelimit, lt_succ_of_not_isMax, motive, not_isSuccPrelimit_iff_succ_eq, wellFounded_lt, wellFounded_lt.fix
-/
noncomputable def prelimitRecOn : motive b :=
  wellFounded_lt.fix
    (fun a IH => if h : IsSuccPrelimit a then isSuccPrelimit a h IH else
      haveI H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 h)
      cast (congr_arg motive H.2) (succ _ H.1 <| IH _ <| H.2.subst <| lt_succ_of_not_isMax H.1))
    b

@[to_dual (attr := simp)]
/--
theorem `prelimitRecOn_of_isSuccPrelimit` / 定理 `prelimitRecOn_of_isSuccPrelimit`

English:
theorem prelimitRecOn_of_isSuccPrelimit
  given: (hb : IsSuccPrelimit b)
  proof: by
  rw [prelimitRecOn]; rw [WellFounded.fix_eq]; rw [dif_pos hb]; rfl

中文:
定理 prelimitRecOn_of_isSuccPrelimit
  条件: (hb : IsSuccPrelimit b)
  证明: by
  rw [prelimitRecOn]; rw [WellFounded.fix_eq]; rw [dif_pos hb]; rfl

Depends on / 依赖: WellFounded, WellFounded.fix_eq, dif_pos, fix_eq, prelimitRecOn
-/
theorem prelimitRecOn_of_isSuccPrelimit (hb : IsSuccPrelimit b) :
    prelimitRecOn b succ isSuccPrelimit =
      isSuccPrelimit b hb fun x _ => SuccOrder.prelimitRecOn x succ isSuccPrelimit := by
  rw [prelimitRecOn]; rw [WellFounded.fix_eq]; rw [dif_pos hb]; rfl

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α] [WellFoundedLT α]
  (succ : forall a, ¬IsMax a -> motive a -> motive (Order.succ a))
  (isSuccPrelimit : forall a, IsSuccPrelimit a -> (forall b < a, motive b) -> motive a)

@[to_dual]
/--
theorem `prelimitRecOn_succ_of_not_isMax` / 定理 `prelimitRecOn_succ_of_not_isMax`

English:
theorem prelimitRecOn_succ_of_not_isMax
  given: (hb : ¬IsMax b)
  proof: by
  have h := mt IsSuccPrelimit.isMax hb
  have H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 h)
  rw [prelimitRecOn]; rw [WellFounded.fix_eq]; rw [dif_neg h]
  have {a c : α} {ha hc} {x : forall a, motive a} (h : a = c) :
    cast (congr_arg (motive ∘ Order.succ) h) (succ a ha (x a)

中文:
定理 prelimitRecOn_succ_of_not_isMax
  条件: (hb : ¬IsMax b)
  证明: by
  have h := mt IsSuccPrelimit.isMax hb
  have H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 h)
  rw [prelimitRecOn]; rw [WellFounded.fix_eq]; rw [dif_neg h]
  have {a c : α} {ha hc} {x : forall a, motive a} (h : a = c) :
    cast (congr_arg (motive ∘ Order.succ) h) (succ a ha (x a)

Depends on / 依赖: Classical, Classical.choose_spec, IsSuccPrelimit, IsSuccPrelimit.isMax, Order.succ, WellFounded, WellFounded.fix_eq, choose_spec, congr_arg, dif_neg, fix_eq, motive, not_isSuccPrelimit_iff_succ_eq, prelimitRecOn, succ_eq_succ_iff_of_not_isMax
-/
theorem prelimitRecOn_succ_of_not_isMax (hb : ¬IsMax b) :
    prelimitRecOn (Order.succ b) succ isSuccPrelimit =
      succ b hb (prelimitRecOn b succ isSuccPrelimit) := by
  have h := mt IsSuccPrelimit.isMax hb
  have H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 h)
  rw [prelimitRecOn]; rw [WellFounded.fix_eq]; rw [dif_neg h]
  have {a c : α} {ha hc} {x : forall a, motive a} (h : a = c) :
    cast (congr_arg (motive ∘ Order.succ) h) (succ a ha (x a)) = succ c hc (x c) := by subst h; rfl
exact this (succ_eq_succ_iff_of_not_isMax H.1 hb).1 H.2

@[to_dual (attr := simp)]
/--
theorem `prelimitRecOn_succ` / 定理 `prelimitRecOn_succ`

English:
theorem prelimitRecOn_succ
  given: [NoMaxOrder α] (b : α)
  proof: prelimitRecOn_succ_of_not_isMax _ _ _

中文:
定理 prelimitRecOn_succ
  条件: [NoMaxOrder α] (b : α)
  证明: prelimitRecOn_succ_of_not_isMax _ _ _

Depends on / 依赖: prelimitRecOn_succ_of_not_isMax
-/
theorem prelimitRecOn_succ [NoMaxOrder α] (b : α) :
    prelimitRecOn (Order.succ b) succ isSuccPrelimit =
      succ b (not_isMax b) (prelimitRecOn b succ isSuccPrelimit) :=
  prelimitRecOn_succ_of_not_isMax _ _ _

end LinearOrder

end prelimitRecOn

section limitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α] [WellFoundedLT α] (isMin : forall a, IsMin a -> motive a)
  (succ : forall a, ¬IsMax a -> motive a -> motive (Order.succ a))
  (isSuccLimit : forall a, IsSuccLimit a -> (forall b < a, motive b) -> motive a)

variable (b) in
open scoped Classical in
/-- Recursion principle on a well-founded partial `SuccOrder`, separating out the case of a
minimal element. -/
@[to_dual (attr := elab_as_elim)
/-- Recursion principle on a well-founded partial `PredOrder`, separating out the case of a
minimal element. -/]
/--
Definition of `limitRecOn` / `limitRecOn` 的定义

English:
definition limitRecOn
  signature: : motive b
  body: prelimitRecOn b succ fun a ha IH =>
    if h : IsMin a then isMin a h else isSuccLimit a ⟨h, ha⟩ IH

@[to_dual (attr := simp)]

中文:
定义 limitRecOn
  签名: : motive b
  定义体: prelimitRecOn b succ fun a ha IH =>
    if h : IsMin a then isMin a h else isSuccLimit a ⟨h, ha⟩ IH

@[to_dual (attr := simp)]

Depends on / 依赖: isSuccLimit, prelimitRecOn
-/
noncomputable def limitRecOn : motive b :=
  prelimitRecOn b succ fun a ha IH =>
    if h : IsMin a then isMin a h else isSuccLimit a ⟨h, ha⟩ IH

@[to_dual (attr := simp)]
/--
theorem `limitRecOn_isMin` / 定理 `limitRecOn_isMin`

English:
theorem limitRecOn_isMin
  given: (hb : IsMin b)
  statement: limitRecOn b isMin succ isSuccLimit = isMin b hb
  proof: by
  rw [limitRecOn]; rw [prelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit]; rw [dif_pos hb]

@[to_dual (attr := simp)]

中文:
定理 limitRecOn_isMin
  条件: (hb : IsMin b)
  结论: limitRecOn b isMin succ isSuccLimit = isMin b hb
  证明: by
  rw [limitRecOn]; rw [prelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit]; rw [dif_pos hb]

@[to_dual (attr := simp)]

Depends on / 依赖: dif_pos, hb.isSuccPrelimit, isSuccPrelimit, limitRecOn, prelimitRecOn_of_isSuccPrelimit
-/
theorem limitRecOn_isMin (hb : IsMin b) : limitRecOn b isMin succ isSuccLimit = isMin b hb := by
  rw [limitRecOn]; rw [prelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit]; rw [dif_pos hb]

@[to_dual (attr := simp)]
/--
theorem `limitRecOn_of_isSuccLimit` / 定理 `limitRecOn_of_isSuccLimit`

English:
theorem limitRecOn_of_isSuccLimit
  given: (hb : IsSuccLimit b)
  proof: by
  rw [limitRecOn]; rw [prelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit]; rw [dif_neg hb.not_isMin]; rfl

中文:
定理 limitRecOn_of_isSuccLimit
  条件: (hb : IsSuccLimit b)
  证明: by
  rw [limitRecOn]; rw [prelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit]; rw [dif_neg hb.not_isMin]; rfl

Depends on / 依赖: dif_neg, hb.isSuccPrelimit, hb.not_isMin, isSuccPrelimit, limitRecOn, not_isMin, prelimitRecOn_of_isSuccPrelimit
-/
theorem limitRecOn_of_isSuccLimit (hb : IsSuccLimit b) :
    limitRecOn b isMin succ isSuccLimit =
      isSuccLimit b hb fun x _ => limitRecOn x isMin succ isSuccLimit := by
  rw [limitRecOn]; rw [prelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit]; rw [dif_neg hb.not_isMin]; rfl

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α] [WellFoundedLT α] (isMin : forall a, IsMin a -> motive a)
  (succ : forall a, ¬IsMax a -> motive a -> motive (Order.succ a))
  (isSuccLimit : forall a, IsSuccLimit a -> (forall b < a, motive b) -> motive a)

@[to_dual]
/--
theorem `limitRecOn_succ_of_not_isMax` / 定理 `limitRecOn_succ_of_not_isMax`

English:
theorem limitRecOn_succ_of_not_isMax
  given: (hb : ¬IsMax b)
  proof: by
  rw [limitRecOn]; rw [prelimitRecOn_succ_of_not_isMax]; rfl

@[to_dual (attr := simp)]

中文:
定理 limitRecOn_succ_of_not_isMax
  条件: (hb : ¬IsMax b)
  证明: by
  rw [limitRecOn]; rw [prelimitRecOn_succ_of_not_isMax]; rfl

@[to_dual (attr := simp)]

Depends on / 依赖: limitRecOn, prelimitRecOn_succ_of_not_isMax
-/
theorem limitRecOn_succ_of_not_isMax (hb : ¬IsMax b) :
    limitRecOn (Order.succ b) isMin succ isSuccLimit =
      succ b hb (limitRecOn b isMin succ isSuccLimit) := by
  rw [limitRecOn]; rw [prelimitRecOn_succ_of_not_isMax]; rfl

@[to_dual (attr := simp)]
/--
theorem `limitRecOn_succ` / 定理 `limitRecOn_succ`

English:
theorem limitRecOn_succ
  given: [NoMaxOrder α] (b : α)
  proof: limitRecOn_succ_of_not_isMax isMin succ isSuccLimit _

中文:
定理 limitRecOn_succ
  条件: [NoMaxOrder α] (b : α)
  证明: limitRecOn_succ_of_not_isMax isMin succ isSuccLimit _

Depends on / 依赖: isSuccLimit, limitRecOn_succ_of_not_isMax
-/
theorem limitRecOn_succ [NoMaxOrder α] (b : α) :
    limitRecOn (Order.succ b) isMin succ isSuccLimit =
      succ b (not_isMax b) (limitRecOn b isMin succ isSuccLimit) :=
  limitRecOn_succ_of_not_isMax isMin succ isSuccLimit _

end LinearOrder

end limitRecOn

end SuccOrder
