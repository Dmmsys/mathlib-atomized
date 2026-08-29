/-
Copyright (c) 2023 Yael Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yael Dillies
-/
module

public import Batteries.Tactic.Init
public import Mathlib.Tactic.ToAdditive

/-! # Lemmas about inequalities with `1`. -/

public section

assert_not_exists Monoid

variable {α : Type*}

section dite
variable [One α] {p : Prop} [Decidable p] {a : p -> α} {b : ¬p -> α}

@[to_additive dite_nonneg]
/--
lemma `one_le_dite` / 引理 `one_le_dite`

English:
lemma one_le_dite
  given: [LE α] (ha : forall h, 1 <= a h) (hb : forall h, 1 <= b h)
  statement: 1 <= dite p a b
  proof: by
  split; exacts [ha ‹_›, hb ‹_›]

@[to_additive]

中文:
引理 one_le_dite
  条件: [LE α] (ha : 对任意 h, 1 <= a h) (hb : 对任意 h, 1 <= b h)
  结论: 1 <= dite p a b
  证明: by
  split; exacts [ha ‹_›, hb ‹_›]

@[to_additive]

Depends on / 依赖: FloorRing, FloorRing.toFloorSemiring, FloorSemiring, exacts, toFloorSemiring
-/
lemma one_le_dite [LE α] (ha : forall h, 1 <= a h) (hb : forall h, 1 <= b h) : 1 <= dite p a b := by
  split; exacts [ha ‹_›, hb ‹_›]

@[to_additive]
/--
lemma `dite_le_one` / 引理 `dite_le_one`

English:
lemma dite_le_one
  given: [LE α] (ha : forall h, a h <= 1) (hb : forall h, b h <= 1)
  statement: dite p a b <= 1
  proof: by
  split; exacts [ha ‹_›, hb ‹_›]

@[to_additive dite_pos]

中文:
引理 dite_le_one
  条件: [LE α] (ha : 对任意 h, a h <= 1) (hb : 对任意 h, b h <= 1)
  结论: dite p a b <= 1
  证明: by
  split; exacts [ha ‹_›, hb ‹_›]

@[to_additive dite_pos]

Depends on / 依赖: exacts
-/
lemma dite_le_one [LE α] (ha : forall h, a h <= 1) (hb : forall h, b h <= 1) : dite p a b <= 1 := by
  split; exacts [ha ‹_›, hb ‹_›]

@[to_additive dite_pos]
/--
lemma `one_lt_dite` / 引理 `one_lt_dite`

English:
lemma one_lt_dite
  given: [LT α] (ha : forall h, 1 < a h) (hb : forall h, 1 < b h)
  statement: 1 < dite p a b
  proof: by
  split; exacts [ha ‹_›, hb ‹_›]

@[to_additive]

中文:
引理 one_lt_dite
  条件: [LT α] (ha : 对任意 h, 1 < a h) (hb : 对任意 h, 1 < b h)
  结论: 1 < dite p a b
  证明: by
  split; exacts [ha ‹_›, hb ‹_›]

@[to_additive]

Depends on / 依赖: exacts
-/
lemma one_lt_dite [LT α] (ha : forall h, 1 < a h) (hb : forall h, 1 < b h) : 1 < dite p a b := by
  split; exacts [ha ‹_›, hb ‹_›]

@[to_additive]
/--
lemma `dite_lt_one` / 引理 `dite_lt_one`

English:
lemma dite_lt_one
  given: [LT α] (ha : forall h, a h < 1) (hb : forall h, b h < 1)
  statement: dite p a b < 1
  proof: by
  split; exacts [ha ‹_›, hb ‹_›]

中文:
引理 dite_lt_one
  条件: [LT α] (ha : 对任意 h, a h < 1) (hb : 对任意 h, b h < 1)
  结论: dite p a b < 1
  证明: by
  split; exacts [ha ‹_›, hb ‹_›]

Depends on / 依赖: exacts
-/
lemma dite_lt_one [LT α] (ha : forall h, a h < 1) (hb : forall h, b h < 1) : dite p a b < 1 := by
  split; exacts [ha ‹_›, hb ‹_›]

end dite

section
variable [One α] {p : Prop} [Decidable p] {a b : α}

@[to_additive ite_nonneg]
/--
lemma `one_le_ite` / 引理 `one_le_ite`

English:
lemma one_le_ite
  given: [LE α] (ha : 1 <= a) (hb : 1 <= b)
  statement: 1 <= ite p a b
  proof: by split <;> assumption

@[to_additive]

中文:
引理 one_le_ite
  条件: [LE α] (ha : 1 <= a) (hb : 1 <= b)
  结论: 1 <= ite p a b
  证明: by split <;> assumption

@[to_additive]
-/
lemma one_le_ite [LE α] (ha : 1 <= a) (hb : 1 <= b) : 1 <= ite p a b := by split <;> assumption

@[to_additive]
/--
lemma `ite_le_one` / 引理 `ite_le_one`

English:
lemma ite_le_one
  given: [LE α] (ha : a <= 1) (hb : b <= 1)
  statement: ite p a b <= 1
  proof: by split <;> assumption

@[to_additive ite_pos]

中文:
引理 ite_le_one
  条件: [LE α] (ha : a <= 1) (hb : b <= 1)
  结论: ite p a b <= 1
  证明: by split <;> assumption

@[to_additive ite_pos]
-/
lemma ite_le_one [LE α] (ha : a <= 1) (hb : b <= 1) : ite p a b <= 1 := by split <;> assumption

@[to_additive ite_pos]
/--
lemma `one_lt_ite` / 引理 `one_lt_ite`

English:
lemma one_lt_ite
  given: [LT α] (ha : 1 < a) (hb : 1 < b)
  statement: 1 < ite p a b
  proof: by split <;> assumption

@[to_additive]

中文:
引理 one_lt_ite
  条件: [LT α] (ha : 1 < a) (hb : 1 < b)
  结论: 1 < ite p a b
  证明: by split <;> assumption

@[to_additive]
-/
lemma one_lt_ite [LT α] (ha : 1 < a) (hb : 1 < b) : 1 < ite p a b := by split <;> assumption

@[to_additive]
/--
lemma `ite_lt_one` / 引理 `ite_lt_one`

English:
lemma ite_lt_one
  given: [LT α] (ha : a < 1) (hb : b < 1)
  statement: ite p a b < 1
  proof: by split <;> assumption

中文:
引理 ite_lt_one
  条件: [LT α] (ha : a < 1) (hb : b < 1)
  结论: ite p a b < 1
  证明: by split <;> assumption
-/
lemma ite_lt_one [LT α] (ha : a < 1) (hb : b < 1) : ite p a b < 1 := by split <;> assumption

end
