/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Order.WithBot

/-! # Adjoining top/bottom elements to ordered monoids.
-/

@[expose] public section

universe u v

variable {α : Type u} {β : Type v}

open Function

namespace WithTop

section One

variable [One α] {a : α}

@[to_additive]
/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One (WithTop α)
  body: ⟨(1 : α)⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 one
  签名: : 幺 (WithTop α)
  定义体: ⟨(1 : α)⟩

@[to_additive (attr := simp, norm_cast)]
-/
instance one : One (WithTop α) :=
  ⟨(1 : α)⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : α) : WithTop α) = 1
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_one
  结论: ((1 : α) : WithTop α) = 1
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_one : ((1 : α) : WithTop α) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
lemma `coe_eq_one` / 引理 `coe_eq_one`

English:
lemma coe_eq_one
  statement: (a : WithTop α) = 1 ↔ a = 1
  proof: coe_eq_coe

中文:
引理 coe_eq_one
  结论: (a : WithTop α) = 1 ↔ a = 1
  证明: coe_eq_coe

Depends on / 依赖: coe_eq_coe
-/
lemma coe_eq_one : (a : WithTop α) = 1 ↔ a = 1 := coe_eq_coe

/--
lemma `coe_ne_one` / 引理 `coe_ne_one`

English:
lemma coe_ne_one
  statement: (a : WithTop α) != 1 ↔ a != 1
  proof: coe_eq_one.ne

@[to_additive (attr := simp, norm_cast)]

中文:
引理 coe_ne_one
  结论: (a : WithTop α) != 1 ↔ a != 1
  证明: coe_eq_one.ne

@[to_additive (attr := simp, norm_cast)]
-/
@[to_additive] lemma coe_ne_one : (a : WithTop α) != 1 ↔ a != 1 := coe_eq_one.ne

@[to_additive (attr := simp, norm_cast)]
/--
lemma `one_eq_coe` / 引理 `one_eq_coe`

English:
lemma one_eq_coe
  statement: 1 = (a : WithTop α) ↔ a = 1
  proof: eq_comm.trans coe_eq_one

中文:
引理 one_eq_coe
  结论: 1 = (a : WithTop α) ↔ a = 1
  证明: eq_comm.trans coe_eq_one

Depends on / 依赖: coe_eq_one, eq_comm, eq_comm.trans
-/
lemma one_eq_coe : 1 = (a : WithTop α) ↔ a = 1 := eq_comm.trans coe_eq_one

/--
lemma `top_ne_one` / 引理 `top_ne_one`

English:
lemma top_ne_one
  statement: (⊤ : WithTop α) != 1
  proof: top_ne_coe

中文:
引理 top_ne_one
  结论: (⊤ : WithTop α) != 1
  证明: top_ne_coe
-/
@[to_additive (attr := simp)] lemma top_ne_one : (⊤ : WithTop α) != 1 := top_ne_coe

/--
lemma `one_ne_top` / 引理 `one_ne_top`

English:
lemma one_ne_top
  statement: (1 : WithTop α) != ⊤
  proof: coe_ne_top

@[to_additive (attr := simp)]

中文:
引理 one_ne_top
  结论: (1 : WithTop α) != ⊤
  证明: coe_ne_top

@[to_additive (attr := simp)]
-/
@[to_additive (attr := simp)] lemma one_ne_top : (1 : WithTop α) != ⊤ := coe_ne_top

@[to_additive (attr := simp)]
/--
theorem `untop_one` / 定理 `untop_one`

English:
theorem untop_one
  statement: (1 : WithTop α).untop coe_ne_top = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 untop_one
  结论: (1 : WithTop α).untop coe_ne_top = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem untop_one : (1 : WithTop α).untop coe_ne_top = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `untopD_one` / 定理 `untopD_one`

English:
theorem untopD_one
  given: (d : α)
  statement: (1 : WithTop α).untopD d = 1
  proof: rfl

@[to_additive (attr := simp, norm_cast) coe_nonneg]

中文:
定理 untopD_one
  条件: (d : α)
  结论: (1 : WithTop α).untopD d = 1
  证明: rfl

@[to_additive (attr := simp, norm_cast) coe_nonneg]
-/
theorem untopD_one (d : α) : (1 : WithTop α).untopD d = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast) coe_nonneg]
/--
theorem `one_le_coe` / 定理 `one_le_coe`

English:
theorem one_le_coe
  given: [LE α] {a : α}
  statement: 1 <= (a : WithTop α) ↔ 1 <= a
  proof: coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_le_zero]

中文:
定理 one_le_coe
  条件: [LE α] {a : α}
  结论: 1 <= (a : WithTop α) ↔ 1 <= a
  证明: coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_le_zero]

Depends on / 依赖: coe_le_coe
-/
theorem one_le_coe [LE α] {a : α} : 1 <= (a : WithTop α) ↔ 1 <= a :=
  coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_le_zero]
/--
theorem `coe_le_one` / 定理 `coe_le_one`

English:
theorem coe_le_one
  given: [LE α] {a : α}
  statement: (a : WithTop α) <= 1 ↔ a <= 1
  proof: coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_pos]

中文:
定理 coe_le_one
  条件: [LE α] {a : α}
  结论: (a : WithTop α) <= 1 ↔ a <= 1
  证明: coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_pos]

Depends on / 依赖: coe_le_coe
-/
theorem coe_le_one [LE α] {a : α} : (a : WithTop α) <= 1 ↔ a <= 1 :=
  coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_pos]
/--
theorem `one_lt_coe` / 定理 `one_lt_coe`

English:
theorem one_lt_coe
  given: [LT α] {a : α}
  statement: 1 < (a : WithTop α) ↔ 1 < a
  proof: coe_lt_coe

@[to_additive (attr := simp, norm_cast) coe_lt_zero]

中文:
定理 one_lt_coe
  条件: [LT α] {a : α}
  结论: 1 < (a : WithTop α) ↔ 1 < a
  证明: coe_lt_coe

@[to_additive (attr := simp, norm_cast) coe_lt_zero]

Depends on / 依赖: coe_lt_coe
-/
theorem one_lt_coe [LT α] {a : α} : 1 < (a : WithTop α) ↔ 1 < a :=
  coe_lt_coe

@[to_additive (attr := simp, norm_cast) coe_lt_zero]
/--
theorem `coe_lt_one` / 定理 `coe_lt_one`

English:
theorem coe_lt_one
  given: [LT α] {a : α}
  statement: (a : WithTop α) < 1 ↔ a < 1
  proof: coe_lt_coe

@[to_additive (attr := simp)]

中文:
定理 coe_lt_one
  条件: [LT α] {a : α}
  结论: (a : WithTop α) < 1 ↔ a < 1
  证明: coe_lt_coe

@[to_additive (attr := simp)]

Depends on / 依赖: coe_lt_coe
-/
theorem coe_lt_one [LT α] {a : α} : (a : WithTop α) < 1 ↔ a < 1 :=
  coe_lt_coe

@[to_additive (attr := simp)]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  given: {β} (f : α -> β)
  statement: (1 : WithTop α).map f = (f 1 : WithTop β)
  proof: rfl

@[to_additive]

中文:
定理 map_one
  条件: {β} (f : α -> β)
  结论: (1 : WithTop α).map f = (f 1 : WithTop β)
  证明: rfl

@[to_additive]
-/
protected theorem map_one {β} (f : α -> β) : (1 : WithTop α).map f = (f 1 : WithTop β) :=
  rfl

@[to_additive]
/--
theorem `map_eq_one_iff` / 定理 `map_eq_one_iff`

English:
theorem map_eq_one_iff
  given: {α} {f : α -> β} {v : WithTop α} [One β]
  proof: map_eq_some_iff

@[to_additive]

中文:
定理 map_eq_one_iff
  条件: {α} {f : α -> β} {v : WithTop α} [幺 β]
  证明: map_eq_some_iff

@[to_additive]

Depends on / 依赖: map_eq_some_iff
-/
theorem map_eq_one_iff {α} {f : α -> β} {v : WithTop α} [One β] :
    WithTop.map f v = 1 ↔ exists x, v = .some x ∧ f x = 1 := map_eq_some_iff

@[to_additive]
/--
theorem `one_eq_map_iff` / 定理 `one_eq_map_iff`

English:
theorem one_eq_map_iff
  given: {α} {f : α -> β} {v : WithTop α} [One β]
  proof: some_eq_map_iff

中文:
定理 one_eq_map_iff
  条件: {α} {f : α -> β} {v : WithTop α} [幺 β]
  证明: some_eq_map_iff

Depends on / 依赖: some_eq_map_iff
-/
theorem one_eq_map_iff {α} {f : α -> β} {v : WithTop α} [One β] :
    1 = WithTop.map f v ↔ exists x, v = .some x ∧ f x = 1 := some_eq_map_iff

/--
Instance `zeroLEOneClass` / 实例 `zeroLEOneClass`

English:
instance zeroLEOneClass
  signature: [Zero α] [LE α] [ZeroLEOneClass α]
  body: ⟨coe_le_coe.2 zero_le_one⟩

@[to_additive]

中文:
实例 zeroLEOneClass
  签名: [零 α] [LE α] [ZeroLEOne类 α]
  定义体: ⟨coe_le_coe.2 zero_le_one⟩

@[to_additive]

Depends on / 依赖: coe_le_coe, zero_le_one
-/
instance zeroLEOneClass [Zero α] [LE α] [ZeroLEOneClass α] : ZeroLEOneClass (WithTop α) :=
  ⟨coe_le_coe.2 zero_le_one⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: α] [IsBotOneClass α] : IsBotOneClass (WithTop α) where
  body: by cases x <;> simp

中文:
实例 [LE
  签名: α] [是BotOne类 α] : 是BotOne类 (WithTop α) where
  定义体: by cases x <;> simp
-/
instance [LE α] [IsBotOneClass α] : IsBotOneClass (WithTop α) where
  isBot_one x := by cases x <;> simp

end One

section Add

variable [Add α] {w x y z : WithTop α} {a b : α}

/--
Instance `add` / 实例 `add`

English:
instance add
  signature: : Add (WithTop α)
  body: ⟨WithTop.map₂ (· + ·)⟩

中文:
实例 add
  签名: : 加法 (WithTop α)
  定义体: ⟨WithTop.map₂ (· + ·)⟩

Depends on / 依赖: WithTop, WithTop.map
-/
instance add : Add (WithTop α) :=
  ⟨WithTop.map₂ (· + ·)⟩

/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: (a b : α)
  statement: ↑(a + b) = (a + b : WithTop α)
  proof: rfl

中文:
引理 coe_add
  条件: (a b : α)
  结论: ↑(a + b) = (a + b : WithTop α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_add (a b : α) : ↑(a + b) = (a + b : WithTop α) := rfl

/--
lemma `top_add` / 引理 `top_add`

English:
lemma top_add
  given: (x : WithTop α)
  statement: ⊤ + x = ⊤
  proof: rfl

中文:
引理 top_add
  条件: (x : WithTop α)
  结论: ⊤ + x = ⊤
  证明: rfl
-/
@[simp] lemma top_add (x : WithTop α) : ⊤ + x = ⊤ := rfl
/--
lemma `add_top` / 引理 `add_top`

English:
lemma add_top
  given: (x : WithTop α)
  statement: x + ⊤ = ⊤
  proof: by cases x <;> rfl

中文:
引理 add_top
  条件: (x : WithTop α)
  结论: x + ⊤ = ⊤
  证明: by cases x <;> rfl
-/
@[simp] lemma add_top (x : WithTop α) : x + ⊤ = ⊤ := by cases x <;> rfl

/--
lemma `add_eq_top` / 引理 `add_eq_top`

English:
lemma add_eq_top
  statement: x + y = ⊤ ↔ x = ⊤ ∨ y = ⊤
  proof: by cases x <;> cases y <;> simp [← coe_add]

中文:
引理 add_eq_top
  结论: x + y = ⊤ ↔ x = ⊤ ∨ y = ⊤
  证明: by cases x <;> cases y <;> simp [← coe_add]
-/
@[simp] lemma add_eq_top : x + y = ⊤ ↔ x = ⊤ ∨ y = ⊤ := by cases x <;> cases y <;> simp [← coe_add]

/--
lemma `add_ne_top` / 引理 `add_ne_top`

English:
lemma add_ne_top
  statement: x + y != ⊤ ↔ x != ⊤ ∧ y != ⊤
  proof: by cases x <;> cases y <;> simp [← coe_add]

@[simp]

中文:
引理 add_ne_top
  结论: x + y != ⊤ ↔ x != ⊤ ∧ y != ⊤
  证明: by cases x <;> cases y <;> simp [← coe_add]

@[simp]

Depends on / 依赖: coe_add
-/
lemma add_ne_top : x + y != ⊤ ↔ x != ⊤ ∧ y != ⊤ := by cases x <;> cases y <;> simp [← coe_add]

@[simp]
/--
lemma `add_lt_top` / 引理 `add_lt_top`

English:
lemma add_lt_top
  given: [LT α]
  statement: x + y < ⊤ ↔ x < ⊤ ∧ y < ⊤
  proof: by
  simp_rw [WithTop.lt_top_iff_ne_top, add_ne_top]

中文:
引理 add_lt_top
  条件: [LT α]
  结论: x + y < ⊤ ↔ x < ⊤ ∧ y < ⊤
  证明: by
  simp_rw [WithTop.lt_top_iff_ne_top, add_ne_top]

Depends on / 依赖: WithTop, WithTop.lt_top_iff_ne_top, add_ne_top, lt_top_iff_ne_top, simp_rw
-/
lemma add_lt_top [LT α] : x + y < ⊤ ↔ x < ⊤ ∧ y < ⊤ := by
  simp_rw [WithTop.lt_top_iff_ne_top, add_ne_top]

/--
theorem `add_eq_coe` / 定理 `add_eq_coe`

English:
theorem add_eq_coe

中文:
定理 add_eq_coe
-/
theorem add_eq_coe :
    forall {a b : WithTop α} {c : α}, a + b = c ↔ exists a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
  | ⊤, b, c => by simp
  | some a, ⊤, c => by simp
  | some a, some b, c => by norm_cast; simp

/--
lemma `add_coe_eq_top_iff` / 引理 `add_coe_eq_top_iff`

English:
lemma add_coe_eq_top_iff
  statement: x + b = ⊤ ↔ x = ⊤
  proof: by simp

中文:
引理 add_coe_eq_top_iff
  结论: x + b = ⊤ ↔ x = ⊤
  证明: by simp
-/
lemma add_coe_eq_top_iff : x + b = ⊤ ↔ x = ⊤ := by simp
/--
lemma `coe_add_eq_top_iff` / 引理 `coe_add_eq_top_iff`

English:
lemma coe_add_eq_top_iff
  statement: a + y = ⊤ ↔ y = ⊤
  proof: by simp

中文:
引理 coe_add_eq_top_iff
  结论: a + y = ⊤ ↔ y = ⊤
  证明: by simp
-/
lemma coe_add_eq_top_iff : a + y = ⊤ ↔ y = ⊤ := by simp

/--
lemma `_root_.IsAddLeftRegular.withTop` / 引理 `_root_.IsAddLeftRegular.withTop`

English:
lemma _root_.IsAddLeftRegular.withTop
  given: (ha : IsAddLeftRegular a)
  proof: by
  rintro (_ | b) (_ | c) <;> simp [none_eq_top, some_eq_coe, ← coe_add, ha.eq_iff]

中文:
引理 _root_.IsAddLeftRegular.withTop
  条件: (ha : IsAddLeftRegular a)
  证明: by
  rintro (_ | b) (_ | c) <;> simp [none_eq_top, some_eq_coe, ← coe_add, ha.eq_iff]

Depends on / 依赖: coe_add, eq_iff, ha.eq_iff, none_eq_top, some_eq_coe
-/
lemma _root_.IsAddLeftRegular.withTop (ha : IsAddLeftRegular a) :
    IsAddLeftRegular (a : WithTop α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_top, some_eq_coe, ← coe_add, ha.eq_iff]

/--
lemma `_root_.IsAddRightRegular.withTop` / 引理 `_root_.IsAddRightRegular.withTop`

English:
lemma _root_.IsAddRightRegular.withTop
  given: (ha : IsAddRightRegular a)
  proof: by
  rintro (_ | b) (_ | c) <;> simp [none_eq_top, some_eq_coe, ← coe_add, ha.eq_iff]

中文:
引理 _root_.IsAddRightRegular.withTop
  条件: (ha : IsAddRightRegular a)
  证明: by
  rintro (_ | b) (_ | c) <;> simp [none_eq_top, some_eq_coe, ← coe_add, ha.eq_iff]

Depends on / 依赖: coe_add, eq_iff, ha.eq_iff, none_eq_top, some_eq_coe
-/
lemma _root_.IsAddRightRegular.withTop (ha : IsAddRightRegular a) :
    IsAddRightRegular (a : WithTop α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_top, some_eq_coe, ← coe_add, ha.eq_iff]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `_root_.AddLECancellable.withTop` / 引理 `_root_.AddLECancellable.withTop`

English:
lemma _root_.AddLECancellable.withTop
  given: [LE α] (ha : AddLECancellable a)
  proof: by
  rintro (_ | b) (_ | c)
  · simp [none_eq_top]
  · simp [none_eq_top]
  · simp [some_eq_coe, ← coe_add, none_eq_top]
  · simpa [none_eq_top, some_eq_coe, ← coe_add] using fun a => ha a

中文:
引理 _root_.AddLECancellable.withTop
  条件: [LE α] (ha : AddLECancellable a)
  证明: by
  rintro (_ | b) (_ | c)
  · simp [none_eq_top]
  · simp [none_eq_top]
  · simp [some_eq_coe, ← coe_add, none_eq_top]
  · simpa [none_eq_top, some_eq_coe, ← coe_add] using fun a => ha a

Depends on / 依赖: coe_add, none_eq_top, some_eq_coe
-/
lemma _root_.AddLECancellable.withTop [LE α] (ha : AddLECancellable a) :
    AddLECancellable (a : WithTop α) := by
  rintro (_ | b) (_ | c)
  · simp [none_eq_top]
  · simp [none_eq_top]
  · simp [some_eq_coe, ← coe_add, none_eq_top]
  · simpa [none_eq_top, some_eq_coe, ← coe_add] using fun a => ha a

/--
lemma `add_right_inj` / 引理 `add_right_inj`

English:
lemma add_right_inj
  given: [IsRightCancelAdd α] (hz : z != ⊤)
  statement: x + z = y + z ↔ x = y
  proof: by
  lift z to α using hz; exact (IsAddRightRegular.all _).withTop.eq_iff

中文:
引理 add_right_inj
  条件: [是右消去加法 α] (hz : z != ⊤)
  结论: x + z = y + z ↔ x = y
  证明: by
  lift z to α using hz; exact (IsAddRightRegular.all _).withTop.eq_iff

Depends on / 依赖: IsAddRightRegular, IsAddRightRegular.all, eq_iff, withTop, withTop.eq_iff
-/
lemma add_right_inj [IsRightCancelAdd α] (hz : z != ⊤) : x + z = y + z ↔ x = y := by
  lift z to α using hz; exact (IsAddRightRegular.all _).withTop.eq_iff

/--
lemma `add_right_cancel` / 引理 `add_right_cancel`

English:
lemma add_right_cancel
  given: [IsRightCancelAdd α] (hz : z != ⊤) (h : x + z = y + z)
  statement: x = y
  proof: (WithTop.add_right_inj hz).1 h

中文:
引理 add_right_cancel
  条件: [是右消去加法 α] (hz : z != ⊤) (h : x + z = y + z)
  结论: x = y
  证明: (WithTop.add_right_inj hz).1 h

Depends on / 依赖: WithTop, WithTop.add_right_inj, add_right_inj
-/
lemma add_right_cancel [IsRightCancelAdd α] (hz : z != ⊤) (h : x + z = y + z) : x = y :=
  (WithTop.add_right_inj hz).1 h

/--
lemma `add_left_inj` / 引理 `add_left_inj`

English:
lemma add_left_inj
  given: [IsLeftCancelAdd α] (hx : x != ⊤)
  statement: x + y = x + z ↔ y = z
  proof: by
  lift x to α using hx; exact (IsAddLeftRegular.all _).withTop.eq_iff

中文:
引理 add_left_inj
  条件: [是左消去加法 α] (hx : x != ⊤)
  结论: x + y = x + z ↔ y = z
  证明: by
  lift x to α using hx; exact (IsAddLeftRegular.all _).withTop.eq_iff

Depends on / 依赖: IsAddLeftRegular, IsAddLeftRegular.all, eq_iff, withTop, withTop.eq_iff
-/
lemma add_left_inj [IsLeftCancelAdd α] (hx : x != ⊤) : x + y = x + z ↔ y = z := by
  lift x to α using hx; exact (IsAddLeftRegular.all _).withTop.eq_iff

/--
lemma `add_left_cancel` / 引理 `add_left_cancel`

English:
lemma add_left_cancel
  given: [IsLeftCancelAdd α] (hx : x != ⊤) (h : x + y = x + z)
  statement: y = z
  proof: (WithTop.add_left_inj hx).1 h

中文:
引理 add_left_cancel
  条件: [是左消去加法 α] (hx : x != ⊤) (h : x + y = x + z)
  结论: y = z
  证明: (WithTop.add_left_inj hx).1 h

Depends on / 依赖: WithTop, WithTop.add_left_inj, add_left_inj
-/
lemma add_left_cancel [IsLeftCancelAdd α] (hx : x != ⊤) (h : x + y = x + z) : y = z :=
  (WithTop.add_left_inj hx).1 h

/--
Instance `addLeftMono` / 实例 `addLeftMono`

English:
instance addLeftMono
  signature: [LE α] [AddLeftMono α]
  body: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ => by gcongr

中文:
实例 addLeftMono
  签名: [LE α] [AddLeftMono α]
  定义体: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ => by gcongr

Depends on / 依赖: coe_add
-/
instance addLeftMono [LE α] [AddLeftMono α] : AddLeftMono (WithTop α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ => by gcongr

/--
Instance `addRightMono` / 实例 `addRightMono`

English:
instance addRightMono
  signature: [LE α] [AddRightMono α]
  body: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using fun _ => by gcongr

中文:
实例 addRightMono
  签名: [LE α] [AddRightMono α]
  定义体: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using fun _ => by gcongr

Depends on / 依赖: coe_add
-/
instance addRightMono [LE α] [AddRightMono α] : AddRightMono (WithTop α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using fun _ => by gcongr

/--
Instance `addLeftReflectLT` / 实例 `addLeftReflectLT`

English:
instance addLeftReflectLT
  signature: [LT α] [AddLeftReflectLT α]
  body: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using lt_of_add_lt_add_left

中文:
实例 addLeftReflectLT
  签名: [LT α] [AddLeftReflectLT α]
  定义体: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using lt_of_add_lt_add_left

Depends on / 依赖: coe_add, lt_of_add_lt_add_left
-/
instance addLeftReflectLT [LT α] [AddLeftReflectLT α] : AddLeftReflectLT (WithTop α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using lt_of_add_lt_add_left

/--
Instance `addRightReflectLT` / 实例 `addRightReflectLT`

English:
instance addRightReflectLT
  signature: [LT α] [AddRightReflectLT α]
  body: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using lt_of_add_lt_add_right

中文:
实例 addRightReflectLT
  签名: [LT α] [AddRightReflectLT α]
  定义体: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using lt_of_add_lt_add_right

Depends on / 依赖: coe_add, lt_of_add_lt_add_right
-/
instance addRightReflectLT [LT α] [AddRightReflectLT α] : AddRightReflectLT (WithTop α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using lt_of_add_lt_add_right

/--
lemma `le_of_add_le_add_left` / 引理 `le_of_add_le_add_left`

English:
lemma le_of_add_le_add_left
  given: [LE α] [AddLeftReflectLE α] (hx : x != ⊤)
  proof: by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using le_of_add_le_add_left

中文:
引理 le_of_add_le_add_left
  条件: [LE α] [加法LeftReflectLE α] (hx : x != ⊤)
  证明: by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using le_of_add_le_add_left
-/
protected lemma le_of_add_le_add_left [LE α] [AddLeftReflectLE α] (hx : x != ⊤) :
    x + y <= x + z -> y <= z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using le_of_add_le_add_left

/--
lemma `le_of_add_le_add_right` / 引理 `le_of_add_le_add_right`

English:
lemma le_of_add_le_add_right
  given: [LE α] [AddRightReflectLE α] (hz : z != ⊤)
  proof: by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using le_of_add_le_add_right

中文:
引理 le_of_add_le_add_right
  条件: [LE α] [加法RightReflectLE α] (hz : z != ⊤)
  证明: by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using le_of_add_le_add_right
-/
protected lemma le_of_add_le_add_right [LE α] [AddRightReflectLE α] (hz : z != ⊤) :
    x + z <= y + z -> x <= y := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using le_of_add_le_add_right

/--
lemma `add_lt_add_left` / 引理 `add_lt_add_left`

English:
lemma add_lt_add_left
  given: [LT α] [AddLeftStrictMono α] (hx : x != ⊤)
  proof: by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ => by gcongr

中文:
引理 add_lt_add_left
  条件: [LT α] [AddLeftStrictMono α] (hx : x != ⊤)
  证明: by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ => by gcongr
-/
protected lemma add_lt_add_left [LT α] [AddLeftStrictMono α] (hx : x != ⊤) :
    y < z -> x + y < x + z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ => by gcongr

/--
lemma `add_lt_add_right` / 引理 `add_lt_add_right`

English:
lemma add_lt_add_right
  given: [LT α] [AddRightStrictMono α] (hz : z != ⊤)
  proof: by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using fun _ => by gcongr

@[gcongr]

中文:
引理 add_lt_add_right
  条件: [LT α] [AddRightStrictMono α] (hz : z != ⊤)
  证明: by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using fun _ => by gcongr

@[gcongr]
-/
protected lemma add_lt_add_right [LT α] [AddRightStrictMono α] (hz : z != ⊤) :
    x < y -> x + z < y + z := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using fun _ => by gcongr

@[gcongr]
/--
theorem `add_lt_add` / 定理 `add_lt_add`

English:
theorem add_lt_add
  statement: [Preorder α] [AddLeftStrictMono α] [AddRightStrictMono α]
  proof: by
  apply (WithTop.add_lt_add_left xz.ne_top yw).trans_le
  cases w
  · simp
  · exact (WithTop.add_lt_add_right coe_ne_top xz).le

中文:
定理 add_lt_add
  结论: [预序 α] [AddLeftStrictMono α] [AddRightStrictMono α]
  证明: by
  apply (WithTop.add_lt_add_left xz.ne_top yw).trans_le
  cases w
  · simp
  · exact (WithTop.add_lt_add_right coe_ne_top xz).le
-/
protected theorem add_lt_add [Preorder α] [AddLeftStrictMono α] [AddRightStrictMono α]
    (xz : x < z) (yw : y < w) : x + y < z + w := by
  apply (WithTop.add_lt_add_left xz.ne_top yw).trans_le
  cases w
  · simp
  · exact (WithTop.add_lt_add_right coe_ne_top xz).le

/--
lemma `add_le_add_iff_left` / 引理 `add_le_add_iff_left`

English:
lemma add_le_add_iff_left
  given: [LE α] [AddLeftMono α] [AddLeftReflectLE α] (hx : x != ⊤)
  proof: ⟨WithTop.le_of_add_le_add_left hx, fun _ => by gcongr⟩

中文:
引理 add_le_add_iff_left
  条件: [LE α] [AddLeftMono α] [加法LeftReflectLE α] (hx : x != ⊤)
  证明: ⟨WithTop.le_of_add_le_add_left hx, fun _ => by gcongr⟩
-/
protected lemma add_le_add_iff_left [LE α] [AddLeftMono α] [AddLeftReflectLE α] (hx : x != ⊤) :
    x + y <= x + z ↔ y <= z := ⟨WithTop.le_of_add_le_add_left hx, fun _ => by gcongr⟩

/--
lemma `add_le_add_iff_right` / 引理 `add_le_add_iff_right`

English:
lemma add_le_add_iff_right
  given: [LE α] [AddRightMono α] [AddRightReflectLE α] (hz : z != ⊤)
  proof: ⟨WithTop.le_of_add_le_add_right hz, fun _ => by gcongr⟩

中文:
引理 add_le_add_iff_right
  条件: [LE α] [AddRightMono α] [加法RightReflectLE α] (hz : z != ⊤)
  证明: ⟨WithTop.le_of_add_le_add_right hz, fun _ => by gcongr⟩
-/
protected lemma add_le_add_iff_right [LE α] [AddRightMono α] [AddRightReflectLE α] (hz : z != ⊤) :
    x + z <= y + z ↔ x <= y := ⟨WithTop.le_of_add_le_add_right hz, fun _ => by gcongr⟩

/--
lemma `add_lt_add_iff_left` / 引理 `add_lt_add_iff_left`

English:
lemma add_lt_add_iff_left
  given: [LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (hx : x != ⊤)
  proof: ⟨lt_of_add_lt_add_left, WithTop.add_lt_add_left hx⟩

中文:
引理 add_lt_add_iff_left
  条件: [LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (hx : x != ⊤)
  证明: ⟨lt_of_add_lt_add_left, WithTop.add_lt_add_left hx⟩
-/
protected lemma add_lt_add_iff_left [LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (hx : x != ⊤) :
    x + y < x + z ↔ y < z := ⟨lt_of_add_lt_add_left, WithTop.add_lt_add_left hx⟩

/--
lemma `add_lt_add_iff_right` / 引理 `add_lt_add_iff_right`

English:
lemma add_lt_add_iff_right
  statement: [LT α] [AddRightStrictMono α] [AddRightReflectLT α]
  proof: ⟨lt_of_add_lt_add_right, WithTop.add_lt_add_right hz⟩

中文:
引理 add_lt_add_iff_right
  结论: [LT α] [AddRightStrictMono α] [AddRightReflectLT α]
  证明: ⟨lt_of_add_lt_add_right, WithTop.add_lt_add_right hz⟩
-/
protected lemma add_lt_add_iff_right [LT α] [AddRightStrictMono α] [AddRightReflectLT α]
    (hz : z != ⊤) : x + z < y + z ↔ x < y := ⟨lt_of_add_lt_add_right, WithTop.add_lt_add_right hz⟩

/--
theorem `add_lt_add_of_le_of_lt` / 定理 `add_lt_add_of_le_of_lt`

English:
theorem add_lt_add_of_le_of_lt
  statement: [Preorder α] [AddLeftStrictMono α]
  proof: (WithTop.add_lt_add_left hw hxz).trans_le by gcongr

中文:
定理 add_lt_add_of_le_of_lt
  结论: [预序 α] [AddLeftStrictMono α]
  证明: (WithTop.add_lt_add_left hw hxz).trans_le by gcongr
-/
protected theorem add_lt_add_of_le_of_lt [Preorder α] [AddLeftStrictMono α]
    [AddRightMono α] (hw : w != ⊤) (hwy : w <= y) (hxz : x < z) :
    w + x < y + z :=
(WithTop.add_lt_add_left hw hxz).trans_le by gcongr

/--
theorem `add_lt_add_of_lt_of_le` / 定理 `add_lt_add_of_lt_of_le`

English:
theorem add_lt_add_of_lt_of_le
  statement: [Preorder α] [AddLeftMono α]
  proof: (WithTop.add_lt_add_right hx hwy).trans_le by gcongr

中文:
定理 add_lt_add_of_lt_of_le
  结论: [预序 α] [AddLeftMono α]
  证明: (WithTop.add_lt_add_right hx hwy).trans_le by gcongr
-/
protected theorem add_lt_add_of_lt_of_le [Preorder α] [AddLeftMono α]
    [AddRightStrictMono α] (hx : x != ⊤) (hwy : w < y) (hxz : x <= z) :
    w + x < y + z :=
(WithTop.add_lt_add_right hx hwy).trans_le by gcongr

/--
lemma `addLECancellable_of_ne_top` / 引理 `addLECancellable_of_ne_top`

English:
lemma addLECancellable_of_ne_top
  statement: [LE α] [AddLeftReflectLE α]
  proof: fun _b _c => WithTop.le_of_add_le_add_left hx

中文:
引理 addLECancellable_of_ne_top
  结论: [LE α] [加法LeftReflectLE α]
  证明: fun _b _c => WithTop.le_of_add_le_add_left hx

Depends on / 依赖: WithTop, WithTop.le_of_add_le_add_left, le_of_add_le_add_left
-/
lemma addLECancellable_of_ne_top [LE α] [AddLeftReflectLE α]
    (hx : x != ⊤) : AddLECancellable x := fun _b _c => WithTop.le_of_add_le_add_left hx

/--
lemma `addLECancellable_of_lt_top` / 引理 `addLECancellable_of_lt_top`

English:
lemma addLECancellable_of_lt_top
  statement: [Preorder α] [AddLeftReflectLE α]
  proof: addLECancellable_of_ne_top hx.ne

中文:
引理 addLECancellable_of_lt_top
  结论: [预序 α] [加法LeftReflectLE α]
  证明: addLECancellable_of_ne_top hx.ne

Depends on / 依赖: addLECancellable_of_ne_top, hx.ne
-/
lemma addLECancellable_of_lt_top [Preorder α] [AddLeftReflectLE α]
    (hx : x < ⊤) : AddLECancellable x := addLECancellable_of_ne_top hx.ne

/--
lemma `addLECancellable_coe` / 引理 `addLECancellable_coe`

English:
lemma addLECancellable_coe
  given: [LE α] [AddLeftReflectLE α] (a : α)
  proof: addLECancellable_of_ne_top coe_ne_top

中文:
引理 addLECancellable_coe
  条件: [LE α] [加法LeftReflectLE α] (a : α)
  证明: addLECancellable_of_ne_top coe_ne_top

Depends on / 依赖: addLECancellable_of_ne_top, coe_ne_top
-/
lemma addLECancellable_coe [LE α] [AddLeftReflectLE α] (a : α) :
    AddLECancellable (a : WithTop α) := addLECancellable_of_ne_top coe_ne_top

/--
lemma `addLECancellable_iff_ne_top` / 引理 `addLECancellable_iff_ne_top`

English:
lemma addLECancellable_iff_ne_top
  statement: [Nonempty α] [Preorder α]
  proof: by rintro h rfl; exact (coe_lt_top <| Classical.arbitrary _).not_ge h by simp
  mpr := addLECancellable_of_ne_top

中文:
引理 addLECancellable_iff_ne_top
  结论: [非空 α] [预序 α]
  证明: by rintro h rfl; exact (coe_lt_top <| Classical.arbitrary _).not_ge h by simp
  mpr := addLECancellable_of_ne_top

Depends on / 依赖: Classical, Classical.arbitrary, addLECancellable_of_ne_top, arbitrary, coe_lt_top, not_ge
-/
lemma addLECancellable_iff_ne_top [Nonempty α] [Preorder α]
    [AddLeftReflectLE α] : AddLECancellable x ↔ x != ⊤ where
mp := by rintro h rfl; exact (coe_lt_top <| Classical.arbitrary _).not_ge h by simp
  mpr := addLECancellable_of_ne_top

-- There is no `WithTop.map_mul_of_mulHom`, since `WithTop` does not have a multiplication.
@[simp]
/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  statement: {F} [Add β] [FunLike F α β] [AddHomClass F α β]
  proof: by
  induction a
  · exact (top_add _).symm
  · induction b
    · exact (add_top _).symm
    · rw [map_coe, map_coe, ← coe_add, ← coe_add, ← map_add]
      rfl

中文:
定理 map_add
  结论: {F} [加法 β] [函数状 F α β] [加法态射类 F α β]
  证明: by
  induction a
  · exact (top_add _).symm
  · induction b
    · exact (add_top _).symm
    · rw [map_coe, map_coe, ← coe_add, ← coe_add, ← map_add]
      rfl
-/
protected theorem map_add {F} [Add β] [FunLike F α β] [AddHomClass F α β]
    (f : F) (a b : WithTop α) :
    (a + b).map f = a.map f + b.map f := by
  induction a
  · exact (top_add _).symm
  · induction b
    · exact (add_top _).symm
    · rw [map_coe, map_coe, ← coe_add, ← coe_add, ← map_add]
      rfl

end Add

/--
Instance `addSemigroup` / 实例 `addSemigroup`

English:
instance addSemigroup
  signature: [AddSemigroup α]
  body: { WithTop.add with
    add_assoc := fun _ _ _ => Option.map₂_assoc add_assoc }

中文:
实例 addSemigroup
  签名: [加法半群 α]
  定义体: { WithTop.add with
    add_assoc := fun _ _ _ => Option.map₂_assoc add_assoc }

Depends on / 依赖: Option.map, WithTop, WithTop.add, add_assoc
-/
instance addSemigroup [AddSemigroup α] : AddSemigroup (WithTop α) :=
  { WithTop.add with
    add_assoc := fun _ _ _ => Option.map₂_assoc add_assoc }

/--
Instance `addCommSemigroup` / 实例 `addCommSemigroup`

English:
instance addCommSemigroup
  signature: [AddCommSemigroup α]
  body: { WithTop.addSemigroup with
    add_comm := fun _ _ => Option.map₂_comm add_comm }

中文:
实例 addCommSemigroup
  签名: [加法交换半群 α]
  定义体: { WithTop.addSemigroup with
    add_comm := fun _ _ => Option.map₂_comm add_comm }

Depends on / 依赖: Option.map, WithTop, WithTop.addSemigroup, addSemigroup, add_comm
-/
instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (WithTop α) :=
  { WithTop.addSemigroup with
    add_comm := fun _ _ => Option.map₂_comm add_comm }

/--
Instance `addZeroClass` / 实例 `addZeroClass`

English:
instance addZeroClass
  signature: [AddZeroClass α]
  body: { WithTop.zero, WithTop.add with
    zero_add := Option.map₂_left_identity zero_add
    add_zero := Option.map₂_right_identity add_zero }

中文:
实例 addZeroClass
  签名: [加法零类 α]
  定义体: { WithTop.zero, WithTop.add with
    zero_add := Option.map₂_left_identity zero_add
    add_zero := Option.map₂_right_identity add_zero }

Depends on / 依赖: Option.map, WithTop, WithTop.add, WithTop.zero, add_zero, zero_add
-/
instance addZeroClass [AddZeroClass α] : AddZeroClass (WithTop α) :=
  { WithTop.zero, WithTop.add with
    zero_add := Option.map₂_left_identity zero_add
    add_zero := Option.map₂_right_identity add_zero }

section AddMonoid
variable [AddMonoid α]

/--
Instance `addMonoid` / 实例 `addMonoid`

English:
instance addMonoid
  signature: : AddMonoid (WithTop α) where
  body: WithTop.addSemigroup
  __ := WithTop.addZeroClass
  nsmul n a := match a, n with
    | (a : α), n => ↑(n • a)
    | ⊤, 0 => 0
    | ⊤, _n + 1 => ⊤
  nsmul_zero a := by simp_rw [HSMul.hSMul, SMul.smul]; cases a <;> simp [zero_nsmul]
  nsmul_succ n a := by
    simp_rw [HSMul.hSMul, SMul.smul]
    cases a <;> cases n <;> simp [succ_nsmul, coe_add]

中文:
实例 addMonoid
  签名: : 加法幺半群 (WithTop α) where
  定义体: WithTop.addSemigroup
  __ := WithTop.addZeroClass
  nsmul n a := match a, n with
    | (a : α), n => ↑(n • a)
    | ⊤, 0 => 0
    | ⊤, _n + 1 => ⊤
  nsmul_zero a := by simp_rw [HSMul.hSMul, SMul.smul]; cases a <;> simp [zero_nsmul]
  nsmul_succ n a := by
    simp_rw [HSMul.hSMul, SMul.smul]
    cases a <;> cases n <;> simp [succ_nsmul, coe_add]

Depends on / 依赖: WithTop, WithTop.addSemigroup, addSemigroup
-/
instance addMonoid : AddMonoid (WithTop α) where
  __ := WithTop.addSemigroup
  __ := WithTop.addZeroClass
  nsmul n a := match a, n with
    | (a : α), n => ↑(n • a)
    | ⊤, 0 => 0
    | ⊤, _n + 1 => ⊤
  nsmul_zero a := by simp_rw [HSMul.hSMul, SMul.smul]; cases a <;> simp [zero_nsmul]
  nsmul_succ n a := by
    simp_rw [HSMul.hSMul, SMul.smul]
    cases a <;> cases n <;> simp [succ_nsmul, coe_add]

/--
lemma `coe_nsmul` / 引理 `coe_nsmul`

English:
lemma coe_nsmul
  given: (a : α) (n : Nat)
  statement: ↑(n • a) = n • (a : WithTop α)
  proof: rfl

中文:
引理 coe_nsmul
  条件: (a : α) (n : 自然数)
  结论: ↑(n • a) = n • (a : WithTop α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_nsmul (a : α) (n : Nat) : ↑(n • a) = n • (a : WithTop α) := rfl

/--
Definition of `addHom` / `addHom` 的定义

English:
definition addHom
  signature: : α ->+ WithTop α where
  body: WithTop.some
  map_zero' := rfl
  map_add' _ _ := rfl

中文:
定义 addHom
  签名: : α ->+ WithTop α where
  定义体: WithTop.some
  map_zero' := rfl
  map_add' _ _ := rfl

Depends on / 依赖: WithTop, WithTop.some
-/
def addHom : α ->+ WithTop α where
  toFun := WithTop.some
  map_zero' := rfl
  map_add' _ _ := rfl

/--
lemma `coe_addHom` / 引理 `coe_addHom`

English:
lemma coe_addHom
  statement: ⇑(addHom : α ->+ WithTop α) = WithTop.some
  proof: rfl

中文:
引理 coe_addHom
  结论: ⇑(addHom : α ->+ WithTop α) = WithTop.some
  证明: rfl
-/
@[simp, norm_cast] lemma coe_addHom : ⇑(addHom : α ->+ WithTop α) = WithTop.some := rfl

end AddMonoid

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: [AddCommMonoid α]
  body: { WithTop.addMonoid, WithTop.addCommSemigroup with }

中文:
实例 addCommMonoid
  签名: [加法交换幺半群 α]
  定义体: { WithTop.addMonoid, WithTop.addCommSemigroup with }

Depends on / 依赖: WithTop, WithTop.addCommSemigroup, WithTop.addMonoid, addCommSemigroup, addMonoid
-/
instance addCommMonoid [AddCommMonoid α] : AddCommMonoid (WithTop α) :=
  { WithTop.addMonoid, WithTop.addCommSemigroup with }

/--
Instance `natCast` / 实例 `natCast`

English:
instance natCast
  signature: [NatCast α]
  body: ⟨fun n => ↑(n : α)⟩

中文:
实例 natCast
  签名: [自然数嵌入 α]
  定义体: ⟨fun n => ↑(n : α)⟩
-/
instance natCast [NatCast α] : NatCast (WithTop α) :=
  ⟨fun n => ↑(n : α)⟩

section AddMonoidWithOne
variable [AddMonoidWithOne α]

/--
Instance `addMonoidWithOne` / 实例 `addMonoidWithOne`

English:
instance addMonoidWithOne
  signature: : AddMonoidWithOne (WithTop α) where
  body: by simp [NatCast.natCast]
  natCast_succ := fun n => by simp [NatCast.natCast]

中文:
实例 addMonoidWithOne
  签名: : 加法带幺幺半群 (WithTop α) where
  定义体: by simp [NatCast.natCast]
  natCast_succ := fun n => by simp [NatCast.natCast]

Depends on / 依赖: NatCast, NatCast.natCast, natCast, natCast_succ
-/
instance addMonoidWithOne : AddMonoidWithOne (WithTop α) where
  natCast_zero := by simp [NatCast.natCast]
  natCast_succ := fun n => by simp [NatCast.natCast]

/--
lemma `coe_natCast` / 引理 `coe_natCast`

English:
lemma coe_natCast
  given: (n : Nat)
  statement: ((n : α) : WithTop α) = n
  proof: rfl

中文:
引理 coe_natCast
  条件: (n : 自然数)
  结论: ((n : α) : WithTop α) = n
  证明: rfl
-/
@[simp, norm_cast] lemma coe_natCast (n : Nat) : ((n : α) : WithTop α) = n := rfl

/--
lemma `top_ne_natCast` / 引理 `top_ne_natCast`

English:
lemma top_ne_natCast
  given: (n : Nat)
  statement: (⊤ : WithTop α) != n
  proof: top_ne_coe

中文:
引理 top_ne_natCast
  条件: (n : 自然数)
  结论: (⊤ : WithTop α) != n
  证明: top_ne_coe
-/
@[simp] lemma top_ne_natCast (n : Nat) : (⊤ : WithTop α) != n := top_ne_coe
/--
lemma `natCast_ne_top` / 引理 `natCast_ne_top`

English:
lemma natCast_ne_top
  given: (n : Nat)
  statement: (n : WithTop α) != ⊤
  proof: coe_ne_top

中文:
引理 natCast_ne_top
  条件: (n : 自然数)
  结论: (n : WithTop α) != ⊤
  证明: coe_ne_top
-/
@[simp] lemma natCast_ne_top (n : Nat) : (n : WithTop α) != ⊤ := coe_ne_top
/--
lemma `natCast_lt_top` / 引理 `natCast_lt_top`

English:
lemma natCast_lt_top
  given: [LT α] (n : Nat)
  statement: (n : WithTop α) < ⊤
  proof: coe_lt_top _

中文:
引理 natCast_lt_top
  条件: [LT α] (n : 自然数)
  结论: (n : WithTop α) < ⊤
  证明: coe_lt_top _
-/
@[simp] lemma natCast_lt_top [LT α] (n : Nat) : (n : WithTop α) < ⊤ := coe_lt_top _

/--
lemma `coe_ofNat` / 引理 `coe_ofNat`

English:
lemma coe_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: rfl

中文:
引理 coe_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: rfl
-/
@[simp] lemma coe_ofNat (n : Nat) [n.AtLeastTwo] :
    ((ofNat(n) : α) : WithTop α) = ofNat(n) := rfl
/--
lemma `coe_eq_ofNat` / 引理 `coe_eq_ofNat`

English:
lemma coe_eq_ofNat
  given: (n : Nat) [n.AtLeastTwo] (m : α)
  proof: coe_eq_coe

中文:
引理 coe_eq_of自然数
  条件: (n : 自然数) [n.AtLeastTwo] (m : α)
  证明: coe_eq_coe
-/
@[simp] lemma coe_eq_ofNat (n : Nat) [n.AtLeastTwo] (m : α) :
    (m : WithTop α) = ofNat(n) ↔ m = ofNat(n) :=
  coe_eq_coe
/--
lemma `ofNat_eq_coe` / 引理 `ofNat_eq_coe`

English:
lemma ofNat_eq_coe
  given: (n : Nat) [n.AtLeastTwo] (m : α)
  proof: coe_eq_coe

中文:
引理 of自然数_eq_coe
  条件: (n : 自然数) [n.AtLeastTwo] (m : α)
  证明: coe_eq_coe
-/
@[simp] lemma ofNat_eq_coe (n : Nat) [n.AtLeastTwo] (m : α) :
    ofNat(n) = (m : WithTop α) ↔ ofNat(n) = m :=
  coe_eq_coe
/--
lemma `ofNat_ne_top` / 引理 `ofNat_ne_top`

English:
lemma ofNat_ne_top
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : WithTop α) != ⊤
  proof: natCast_ne_top n

中文:
引理 of自然数_ne_top
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : WithTop α) != ⊤
  证明: natCast_ne_top n
-/
@[simp] lemma ofNat_ne_top (n : Nat) [n.AtLeastTwo] : (ofNat(n) : WithTop α) != ⊤ :=
  natCast_ne_top n
/--
lemma `top_ne_ofNat` / 引理 `top_ne_ofNat`

English:
lemma top_ne_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (⊤ : WithTop α) != ofNat(n)
  proof: top_ne_natCast n

中文:
引理 top_ne_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (⊤ : WithTop α) != of自然数(n)
  证明: top_ne_natCast n
-/
@[simp] lemma top_ne_ofNat (n : Nat) [n.AtLeastTwo] : (⊤ : WithTop α) != ofNat(n) :=
  top_ne_natCast n

/--
lemma `map_ofNat` / 引理 `map_ofNat`

English:
lemma map_ofNat
  given: {f : α -> β} (n : Nat) [n.AtLeastTwo]
  proof: map_coe f n

中文:
引理 map_of自然数
  条件: {f : α -> β} (n : 自然数) [n.AtLeastTwo]
  证明: map_coe f n
-/
@[simp] lemma map_ofNat {f : α -> β} (n : Nat) [n.AtLeastTwo] :
    WithTop.map f (ofNat(n) : WithTop α) = f (ofNat(n)) := map_coe f n

/--
lemma `map_natCast` / 引理 `map_natCast`

English:
lemma map_natCast
  given: {f : α -> β} (n : Nat)
  proof: map_coe f n

中文:
引理 map_natCast
  条件: {f : α -> β} (n : 自然数)
  证明: map_coe f n
-/
@[simp] lemma map_natCast {f : α -> β} (n : Nat) :
    WithTop.map f (n : WithTop α) = f n := map_coe f n

/--
lemma `map_eq_ofNat_iff` / 引理 `map_eq_ofNat_iff`

English:
lemma map_eq_ofNat_iff
  given: {f : β -> α} {n : Nat} [n.AtLeastTwo] {a : WithTop β}
  proof: map_eq_some_iff

中文:
引理 map_eq_of自然数_iff
  条件: {f : β -> α} {n : 自然数} [n.AtLeastTwo] {a : WithTop β}
  证明: map_eq_some_iff

Depends on / 依赖: map_eq_some_iff
-/
lemma map_eq_ofNat_iff {f : β -> α} {n : Nat} [n.AtLeastTwo] {a : WithTop β} :
    a.map f = ofNat(n) ↔ exists x, a = .some x ∧ f x = n := map_eq_some_iff

/--
lemma `ofNat_eq_map_iff` / 引理 `ofNat_eq_map_iff`

English:
lemma ofNat_eq_map_iff
  given: {f : β -> α} {n : Nat} [n.AtLeastTwo] {a : WithTop β}
  proof: some_eq_map_iff

中文:
引理 of自然数_eq_map_iff
  条件: {f : β -> α} {n : 自然数} [n.AtLeastTwo] {a : WithTop β}
  证明: some_eq_map_iff

Depends on / 依赖: some_eq_map_iff
-/
lemma ofNat_eq_map_iff {f : β -> α} {n : Nat} [n.AtLeastTwo] {a : WithTop β} :
    ofNat(n) = a.map f ↔ exists x, a = .some x ∧ f x = n := some_eq_map_iff

/--
lemma `map_eq_natCast_iff` / 引理 `map_eq_natCast_iff`

English:
lemma map_eq_natCast_iff
  given: {f : β -> α} {n : Nat} {a : WithTop β}
  proof: map_eq_some_iff

中文:
引理 map_eq_natCast_iff
  条件: {f : β -> α} {n : 自然数} {a : WithTop β}
  证明: map_eq_some_iff

Depends on / 依赖: map_eq_some_iff
-/
lemma map_eq_natCast_iff {f : β -> α} {n : Nat} {a : WithTop β} :
    a.map f = n ↔ exists x, a = .some x ∧ f x = n := map_eq_some_iff

/--
lemma `natCast_eq_map_iff` / 引理 `natCast_eq_map_iff`

English:
lemma natCast_eq_map_iff
  given: {f : β -> α} {n : Nat} {a : WithTop β}
  proof: some_eq_map_iff

中文:
引理 natCast_eq_map_iff
  条件: {f : β -> α} {n : 自然数} {a : WithTop β}
  证明: some_eq_map_iff

Depends on / 依赖: some_eq_map_iff
-/
lemma natCast_eq_map_iff {f : β -> α} {n : Nat} {a : WithTop β} :
    n = a.map f ↔ exists x, a = .some x ∧ f x = n := some_eq_map_iff

end AddMonoidWithOne

/--
Instance `charZero` / 实例 `charZero`

English:
instance charZero
  signature: [AddMonoidWithOne α] [CharZero α]
  body: { cast_injective := Function.Injective.comp (f := Nat.cast (R := α))
      (fun _ _ => WithTop.coe_eq_coe.1) Nat.cast_injective }

中文:
实例 charZero
  签名: [加法带幺幺半群 α] [特征零 α]
  定义体: { cast_injective := Function.Injective.comp (f := Nat.cast (R := α))
      (fun _ _ => WithTop.coe_eq_coe.1) Nat.cast_injective }

Depends on / 依赖: Function, Function.Injective.comp, Injective, Nat.cast, Nat.cast_injective, WithTop, WithTop.coe_eq_coe, cast_injective, coe_eq_coe
-/
instance charZero [AddMonoidWithOne α] [CharZero α] : CharZero (WithTop α) :=
  { cast_injective := Function.Injective.comp (f := Nat.cast (R := α))
      (fun _ _ => WithTop.coe_eq_coe.1) Nat.cast_injective }

/--
Instance `addCommMonoidWithOne` / 实例 `addCommMonoidWithOne`

English:
instance addCommMonoidWithOne
  signature: [AddCommMonoidWithOne α]
  body: { WithTop.addMonoidWithOne, WithTop.addCommMonoid with }

中文:
实例 addCommMonoidWithOne
  签名: [加法交换带幺幺半群 α]
  定义体: { WithTop.addMonoidWithOne, WithTop.addCommMonoid with }

Depends on / 依赖: WithTop, WithTop.addCommMonoid, WithTop.addMonoidWithOne, addCommMonoid, addMonoidWithOne
-/
instance addCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne (WithTop α) :=
  { WithTop.addMonoidWithOne, WithTop.addCommMonoid with }

-- instance orderedAddCommMonoid [OrderedAddCommMonoid α] : OrderedAddCommMonoid (WithTop α) where
-- add_le_add_left _ _ := add_le_add_left
--
-- instance linearOrderedAddCommMonoidWithTop [LinearOrderedAddCommMonoid α] :
-- LinearOrderedAddCommMonoidWithTop (WithTop α) :=
-- { WithTop.orderTop, WithTop.linearOrder, WithTop.orderedAddCommMonoid with
-- top_add' := WithTop.top_add }
--
/--
Instance `existsAddOfLE` / 实例 `existsAddOfLE`

English:
instance existsAddOfLE
  signature: [LE α] [Add α] [ExistsAddOfLE α]
  body: ⟨fun {a} {b} =>
    match a, b with
    | ⊤, ⊤ => by simp
    | (a : α), ⊤ => fun _ => ⟨⊤, rfl⟩
    | (a : α), (b : α) => fun h => by
      obtain ⟨c, rfl⟩ := exists_add_of_le (WithTop.coe_le_coe.1 h)
      exact ⟨c, rfl⟩
    | ⊤, (b : α) => fun h => (not_top_le_coe _ h).elim⟩

中文:
实例 存在AddOfLE
  签名: [LE α] [加法 α] [ExistsAddOfLE α]
  定义体: ⟨fun {a} {b} =>
    match a, b with
    | ⊤, ⊤ => by simp
    | (a : α), ⊤ => fun _ => ⟨⊤, rfl⟩
    | (a : α), (b : α) => fun h => by
      obtain ⟨c, rfl⟩ := exists_add_of_le (WithTop.coe_le_coe.1 h)
      exact ⟨c, rfl⟩
    | ⊤, (b : α) => fun h => (not_top_le_coe _ h).elim⟩

Depends on / 依赖: WithTop, WithTop.coe_le_coe, coe_le_coe, exists_add_of_le, not_top_le_coe
-/
instance existsAddOfLE [LE α] [Add α] [ExistsAddOfLE α] : ExistsAddOfLE (WithTop α) :=
  ⟨fun {a} {b} =>
    match a, b with
    | ⊤, ⊤ => by simp
    | (a : α), ⊤ => fun _ => ⟨⊤, rfl⟩
    | (a : α), (b : α) => fun h => by
      obtain ⟨c, rfl⟩ := exists_add_of_le (WithTop.coe_le_coe.1 h)
      exact ⟨c, rfl⟩
    | ⊤, (b : α) => fun h => (not_top_le_coe _ h).elim⟩

-- instance canonicallyOrderedAddCommMonoid [CanonicallyOrderedAddCommMonoid α] :
-- CanonicallyOrderedAddCommMonoid (WithTop α) :=
-- { WithTop.orderBot, WithTop.orderedAddCommMonoid, WithTop.existsAddOfLE with
-- le_self_add := fun a b =>
-- match a, b with
-- | ⊤, ⊤ => le_rfl
-- | (a : α), ⊤ => le_top
-- | (a : α), (b : α) => WithTop.coe_le_coe.2 le_self_add
-- | ⊤, (b : α) => le_rfl }
--
-- instance [CanonicallyLinearOrderedAddCommMonoid α] :
-- CanonicallyLinearOrderedAddCommMonoid (WithTop α) :=
-- { WithTop.canonicallyOrderedAddCommMonoid, WithTop.linearOrder with }

@[to_additive (attr := simp) top_pos]
/--
theorem `one_lt_top` / 定理 `one_lt_top`

English:
theorem one_lt_top
  given: [One α] [LT α]
  statement: (1 : WithTop α) < ⊤
  proof: coe_lt_top _

中文:
定理 one_lt_top
  条件: [幺 α] [LT α]
  结论: (1 : WithTop α) < ⊤
  证明: coe_lt_top _

Depends on / 依赖: coe_lt_top
-/
theorem one_lt_top [One α] [LT α] : (1 : WithTop α) < ⊤ := coe_lt_top _

/-- A version of `WithTop.map` for `OneHom`s. -/
@[to_additive (attr := simps -fullyApplied)
  /-- A version of `WithTop.map` for `ZeroHom`s -/]
/--
Definition of `_root_.OneHom.withTopMap` / `_root_.OneHom.withTopMap` 的定义

English:
definition _root_.OneHom.withTopMap
  signature: {M N : Type*} [One M] [One N] (f : OneHom M N)
  body: WithTop.map f
  map_one' := by rw [WithTop.map_one, map_one, coe_one]

中文:
定义 _root_.幺态射.withTopMap
  签名: {M N : 类型} [幺 M] [幺 N] (f : 幺态射 M N)
  定义体: WithTop.map f
  map_one' := by rw [WithTop.map_one, map_one, coe_one]
-/
protected def _root_.OneHom.withTopMap {M N : Type*} [One M] [One N] (f : OneHom M N) :
    OneHom (WithTop M) (WithTop N) where
  toFun := WithTop.map f
  map_one' := by rw [WithTop.map_one, map_one, coe_one]

/-- A version of `WithTop.map` for `AddHom`s. -/
@[simps -fullyApplied]
/--
Definition of `_root_.AddHom.withTopMap` / `_root_.AddHom.withTopMap` 的定义

English:
definition _root_.AddHom.withTopMap
  signature: {M N : Type*} [Add M] [Add N] (f : AddHom M N)
  body: WithTop.map f
  map_add' := WithTop.map_add f

中文:
定义 _root_.加法半群态射.withTopMap
  签名: {M N : 类型} [加法 M] [加法 N] (f : 加法半群态射 M N)
  定义体: WithTop.map f
  map_add' := WithTop.map_add f
-/
protected def _root_.AddHom.withTopMap {M N : Type*} [Add M] [Add N] (f : AddHom M N) :
    AddHom (WithTop M) (WithTop N) where
  toFun := WithTop.map f
  map_add' := WithTop.map_add f

/-- A version of `WithTop.map` for `AddMonoidHom`s. -/
@[simps -fullyApplied]
/--
Definition of `_root_.AddMonoidHom.withTopMap` / `_root_.AddMonoidHom.withTopMap` 的定义

English:
definition _root_.AddMonoidHom.withTopMap
  signature: {M N : Type*} [AddZeroClass M] [AddZeroClass N]
  body: { ZeroHom.withTopMap f.toZeroHom, AddHom.withTopMap f.toAddHom with toFun := WithTop.map f }

中文:
定义 _root_.加法幺半群态射.withTopMap
  签名: {M N : 类型} [加法零类 M] [加法零类 N]
  定义体: { ZeroHom.withTopMap f.toZeroHom, AddHom.withTopMap f.toAddHom with toFun := WithTop.map f }
-/
protected def _root_.AddMonoidHom.withTopMap {M N : Type*} [AddZeroClass M] [AddZeroClass N]
    (f : M ->+ N) : WithTop M ->+ WithTop N :=
  { ZeroHom.withTopMap f.toZeroHom, AddHom.withTopMap f.toAddHom with toFun := WithTop.map f }

end WithTop

namespace WithBot
section One
variable [One α] {a : α}

/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One (WithBot α)
  body: ⟨(1 : α)⟩

中文:
实例 one
  签名: : 幺 (WithBot α)
  定义体: ⟨(1 : α)⟩
-/
@[to_additive] instance one : One (WithBot α) := ⟨(1 : α)⟩

/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ((1 : α) : WithBot α) = 1
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
引理 coe_one
  结论: ((1 : α) : WithBot α) = 1
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
@[to_additive (attr := simp, norm_cast)] lemma coe_one : ((1 : α) : WithBot α) = 1 := rfl

@[to_additive (attr := simp, norm_cast)]
/--
lemma `coe_eq_one` / 引理 `coe_eq_one`

English:
lemma coe_eq_one
  statement: (a : WithBot α) = 1 ↔ a = 1
  proof: coe_eq_coe

@[to_additive (attr := simp, norm_cast)]

中文:
引理 coe_eq_one
  结论: (a : WithBot α) = 1 ↔ a = 1
  证明: coe_eq_coe

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: coe_eq_coe
-/
lemma coe_eq_one : (a : WithBot α) = 1 ↔ a = 1 := coe_eq_coe

@[to_additive (attr := simp, norm_cast)]
/--
lemma `one_eq_coe` / 引理 `one_eq_coe`

English:
lemma one_eq_coe
  statement: 1 = (a : WithBot α) ↔ a = 1
  proof: eq_comm.trans coe_eq_one

中文:
引理 one_eq_coe
  结论: 1 = (a : WithBot α) ↔ a = 1
  证明: eq_comm.trans coe_eq_one

Depends on / 依赖: coe_eq_one, eq_comm, eq_comm.trans
-/
lemma one_eq_coe : 1 = (a : WithBot α) ↔ a = 1 := eq_comm.trans coe_eq_one

/--
lemma `bot_ne_one` / 引理 `bot_ne_one`

English:
lemma bot_ne_one
  statement: (⊥ : WithBot α) != 1
  proof: bot_ne_coe

中文:
引理 bot_ne_one
  结论: (⊥ : WithBot α) != 1
  证明: bot_ne_coe
-/
@[to_additive (attr := simp)] lemma bot_ne_one : (⊥ : WithBot α) != 1 := bot_ne_coe
/--
lemma `one_ne_bot` / 引理 `one_ne_bot`

English:
lemma one_ne_bot
  statement: (1 : WithBot α) != ⊥
  proof: coe_ne_bot

@[to_additive (attr := simp)]

中文:
引理 one_ne_bot
  结论: (1 : WithBot α) != ⊥
  证明: coe_ne_bot

@[to_additive (attr := simp)]
-/
@[to_additive (attr := simp)] lemma one_ne_bot : (1 : WithBot α) != ⊥ := coe_ne_bot

@[to_additive (attr := simp)]
/--
theorem `unbot_one` / 定理 `unbot_one`

English:
theorem unbot_one
  statement: (1 : WithBot α).unbot coe_ne_bot = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 unbot_one
  结论: (1 : WithBot α).unbot coe_ne_bot = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem unbot_one : (1 : WithBot α).unbot coe_ne_bot = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `unbotD_one` / 定理 `unbotD_one`

English:
theorem unbotD_one
  given: (d : α)
  statement: (1 : WithBot α).unbotD d = 1
  proof: rfl

@[to_additive (attr := simp, norm_cast) coe_nonneg]

中文:
定理 unbotD_one
  条件: (d : α)
  结论: (1 : WithBot α).unbotD d = 1
  证明: rfl

@[to_additive (attr := simp, norm_cast) coe_nonneg]
-/
theorem unbotD_one (d : α) : (1 : WithBot α).unbotD d = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast) coe_nonneg]
/--
theorem `one_le_coe` / 定理 `one_le_coe`

English:
theorem one_le_coe
  given: [LE α]
  statement: 1 <= (a : WithBot α) ↔ 1 <= a
  proof: coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_le_zero]

中文:
定理 one_le_coe
  条件: [LE α]
  结论: 1 <= (a : WithBot α) ↔ 1 <= a
  证明: coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_le_zero]

Depends on / 依赖: coe_le_coe
-/
theorem one_le_coe [LE α] : 1 <= (a : WithBot α) ↔ 1 <= a := coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_le_zero]
/--
theorem `coe_le_one` / 定理 `coe_le_one`

English:
theorem coe_le_one
  given: [LE α]
  statement: (a : WithBot α) <= 1 ↔ a <= 1
  proof: coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_pos]

中文:
定理 coe_le_one
  条件: [LE α]
  结论: (a : WithBot α) <= 1 ↔ a <= 1
  证明: coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_pos]

Depends on / 依赖: coe_le_coe
-/
theorem coe_le_one [LE α] : (a : WithBot α) <= 1 ↔ a <= 1 := coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_pos]
/--
theorem `one_lt_coe` / 定理 `one_lt_coe`

English:
theorem one_lt_coe
  given: [LT α]
  statement: 1 < (a : WithBot α) ↔ 1 < a
  proof: coe_lt_coe

@[to_additive (attr := simp, norm_cast) coe_lt_zero]

中文:
定理 one_lt_coe
  条件: [LT α]
  结论: 1 < (a : WithBot α) ↔ 1 < a
  证明: coe_lt_coe

@[to_additive (attr := simp, norm_cast) coe_lt_zero]

Depends on / 依赖: coe_lt_coe
-/
theorem one_lt_coe [LT α] : 1 < (a : WithBot α) ↔ 1 < a := coe_lt_coe

@[to_additive (attr := simp, norm_cast) coe_lt_zero]
/--
theorem `coe_lt_one` / 定理 `coe_lt_one`

English:
theorem coe_lt_one
  given: [LT α]
  statement: (a : WithBot α) < 1 ↔ a < 1
  proof: coe_lt_coe

@[to_additive (attr := simp)]

中文:
定理 coe_lt_one
  条件: [LT α]
  结论: (a : WithBot α) < 1 ↔ a < 1
  证明: coe_lt_coe

@[to_additive (attr := simp)]

Depends on / 依赖: coe_lt_coe
-/
theorem coe_lt_one [LT α] : (a : WithBot α) < 1 ↔ a < 1 := coe_lt_coe

@[to_additive (attr := simp)]
/--
theorem `bot_lt_one` / 定理 `bot_lt_one`

English:
theorem bot_lt_one
  given: [LT α]
  statement: ⊥ < (1 : WithBot α)
  proof: bot_lt_coe _

@[to_additive (attr := simp)]

中文:
定理 bot_lt_one
  条件: [LT α]
  结论: ⊥ < (1 : WithBot α)
  证明: bot_lt_coe _

@[to_additive (attr := simp)]

Depends on / 依赖: bot_lt_coe
-/
theorem bot_lt_one [LT α] : ⊥ < (1 : WithBot α) := bot_lt_coe _

@[to_additive (attr := simp)]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  given: {β} (f : α -> β)
  statement: (1 : WithBot α).map f = (f 1 : WithBot β)
  proof: rfl

@[to_additive]

中文:
定理 map_one
  条件: {β} (f : α -> β)
  结论: (1 : WithBot α).map f = (f 1 : WithBot β)
  证明: rfl

@[to_additive]
-/
protected theorem map_one {β} (f : α -> β) : (1 : WithBot α).map f = (f 1 : WithBot β) :=
  rfl

@[to_additive]
/--
theorem `map_eq_one_iff` / 定理 `map_eq_one_iff`

English:
theorem map_eq_one_iff
  given: {α} {f : α -> β} {v : WithBot α} [One β]
  proof: map_eq_some_iff

@[to_additive]

中文:
定理 map_eq_one_iff
  条件: {α} {f : α -> β} {v : WithBot α} [幺 β]
  证明: map_eq_some_iff

@[to_additive]

Depends on / 依赖: map_eq_some_iff
-/
theorem map_eq_one_iff {α} {f : α -> β} {v : WithBot α} [One β] :
    WithBot.map f v = 1 ↔ exists x, v = .some x ∧ f x = 1 := map_eq_some_iff

@[to_additive]
/--
theorem `one_eq_map_iff` / 定理 `one_eq_map_iff`

English:
theorem one_eq_map_iff
  given: {α} {f : α -> β} {v : WithBot α} [One β]
  proof: some_eq_map_iff

中文:
定理 one_eq_map_iff
  条件: {α} {f : α -> β} {v : WithBot α} [幺 β]
  证明: some_eq_map_iff

Depends on / 依赖: some_eq_map_iff
-/
theorem one_eq_map_iff {α} {f : α -> β} {v : WithBot α} [One β] :
    1 = WithBot.map f v ↔ exists x, v = .some x ∧ f x = 1 := some_eq_map_iff

/--
Instance `zeroLEOneClass` / 实例 `zeroLEOneClass`

English:
instance zeroLEOneClass
  signature: [Zero α] [LE α] [ZeroLEOneClass α]
  body: ⟨coe_le_coe.2 zero_le_one⟩

中文:
实例 zeroLEOneClass
  签名: [零 α] [LE α] [ZeroLEOne类 α]
  定义体: ⟨coe_le_coe.2 zero_le_one⟩

Depends on / 依赖: coe_le_coe, zero_le_one
-/
instance zeroLEOneClass [Zero α] [LE α] [ZeroLEOneClass α] : ZeroLEOneClass (WithBot α) :=
  ⟨coe_le_coe.2 zero_le_one⟩

end One

section Add
variable [Add α] {w x y z : WithBot α} {a b : α}

/--
Instance `add` / 实例 `add`

English:
instance add
  signature: : Add (WithBot α)
  body: ⟨WithBot.map₂ (· + ·)⟩

中文:
实例 add
  签名: : 加法 (WithBot α)
  定义体: ⟨WithBot.map₂ (· + ·)⟩

Depends on / 依赖: WithBot, WithBot.map
-/
instance add : Add (WithBot α) :=
  ⟨WithBot.map₂ (· + ·)⟩

/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: (a b : α)
  statement: ↑(a + b) = (a + b : WithBot α)
  proof: rfl

中文:
引理 coe_add
  条件: (a b : α)
  结论: ↑(a + b) = (a + b : WithBot α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_add (a b : α) : ↑(a + b) = (a + b : WithBot α) := rfl

/--
lemma `bot_add` / 引理 `bot_add`

English:
lemma bot_add
  given: (x : WithBot α)
  statement: ⊥ + x = ⊥
  proof: rfl

中文:
引理 bot_add
  条件: (x : WithBot α)
  结论: ⊥ + x = ⊥
  证明: rfl
-/
@[simp] lemma bot_add (x : WithBot α) : ⊥ + x = ⊥ := rfl
/--
lemma `add_bot` / 引理 `add_bot`

English:
lemma add_bot
  given: (x : WithBot α)
  statement: x + ⊥ = ⊥
  proof: by cases x <;> rfl

中文:
引理 add_bot
  条件: (x : WithBot α)
  结论: x + ⊥ = ⊥
  证明: by cases x <;> rfl
-/
@[simp] lemma add_bot (x : WithBot α) : x + ⊥ = ⊥ := by cases x <;> rfl

/--
lemma `add_eq_bot` / 引理 `add_eq_bot`

English:
lemma add_eq_bot
  statement: x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥
  proof: by cases x <;> cases y <;> simp [← coe_add]

中文:
引理 add_eq_bot
  结论: x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥
  证明: by cases x <;> cases y <;> simp [← coe_add]
-/
@[simp] lemma add_eq_bot : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ := by cases x <;> cases y <;> simp [← coe_add]

/--
lemma `add_ne_bot` / 引理 `add_ne_bot`

English:
lemma add_ne_bot
  statement: x + y != ⊥ ↔ x != ⊥ ∧ y != ⊥
  proof: by cases x <;> cases y <;> simp [← coe_add]

@[simp]

中文:
引理 add_ne_bot
  结论: x + y != ⊥ ↔ x != ⊥ ∧ y != ⊥
  证明: by cases x <;> cases y <;> simp [← coe_add]

@[simp]

Depends on / 依赖: coe_add
-/
lemma add_ne_bot : x + y != ⊥ ↔ x != ⊥ ∧ y != ⊥ := by cases x <;> cases y <;> simp [← coe_add]

@[simp]
/--
lemma `bot_lt_add` / 引理 `bot_lt_add`

English:
lemma bot_lt_add
  given: [LT α]
  statement: ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y
  proof: by
  simp_rw [WithBot.bot_lt_iff_ne_bot, add_ne_bot]

中文:
引理 bot_lt_add
  条件: [LT α]
  结论: ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y
  证明: by
  simp_rw [WithBot.bot_lt_iff_ne_bot, add_ne_bot]

Depends on / 依赖: WithBot, WithBot.bot_lt_iff_ne_bot, add_ne_bot, bot_lt_iff_ne_bot, simp_rw
-/
lemma bot_lt_add [LT α] : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y := by
  simp_rw [WithBot.bot_lt_iff_ne_bot, add_ne_bot]

/--
theorem `add_eq_coe` / 定理 `add_eq_coe`

English:
theorem add_eq_coe

中文:
定理 add_eq_coe
-/
theorem add_eq_coe :
    forall {a b : WithBot α} {c : α}, a + b = c ↔ exists a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
  | ⊥, b, c => by simp
  | some a, ⊥, c => by simp
  | some a, some b, c => by norm_cast; simp

/--
lemma `add_coe_eq_bot_iff` / 引理 `add_coe_eq_bot_iff`

English:
lemma add_coe_eq_bot_iff
  statement: x + b = ⊥ ↔ x = ⊥
  proof: by simp

中文:
引理 add_coe_eq_bot_iff
  结论: x + b = ⊥ ↔ x = ⊥
  证明: by simp
-/
lemma add_coe_eq_bot_iff : x + b = ⊥ ↔ x = ⊥ := by simp
/--
lemma `coe_add_eq_bot_iff` / 引理 `coe_add_eq_bot_iff`

English:
lemma coe_add_eq_bot_iff
  statement: a + y = ⊥ ↔ y = ⊥
  proof: by simp

中文:
引理 coe_add_eq_bot_iff
  结论: a + y = ⊥ ↔ y = ⊥
  证明: by simp
-/
lemma coe_add_eq_bot_iff : a + y = ⊥ ↔ y = ⊥ := by simp

/--
lemma `_root_.IsAddLeftRegular.withBot` / 引理 `_root_.IsAddLeftRegular.withBot`

English:
lemma _root_.IsAddLeftRegular.withBot
  given: (ha : IsAddLeftRegular a)
  proof: by
  rintro (_ | b) (_ | c) <;> simp [none_eq_bot, some_eq_coe, ← coe_add]; simpa using @ha _ _

中文:
引理 _root_.IsAddLeftRegular.withBot
  条件: (ha : IsAddLeftRegular a)
  证明: by
  rintro (_ | b) (_ | c) <;> simp [none_eq_bot, some_eq_coe, ← coe_add]; simpa using @ha _ _

Depends on / 依赖: coe_add, none_eq_bot, some_eq_coe
-/
lemma _root_.IsAddLeftRegular.withBot (ha : IsAddLeftRegular a) :
    IsAddLeftRegular (a : WithBot α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_bot, some_eq_coe, ← coe_add]; simpa using @ha _ _

/--
lemma `_root_.IsAddRightRegular.withBot` / 引理 `_root_.IsAddRightRegular.withBot`

English:
lemma _root_.IsAddRightRegular.withBot
  given: (ha : IsAddRightRegular a)
  proof: by
  rintro (_ | b) (_ | c) <;> simp [none_eq_bot, some_eq_coe, ← coe_add]; simpa using @ha _ _

中文:
引理 _root_.IsAddRightRegular.withBot
  条件: (ha : IsAddRightRegular a)
  证明: by
  rintro (_ | b) (_ | c) <;> simp [none_eq_bot, some_eq_coe, ← coe_add]; simpa using @ha _ _

Depends on / 依赖: coe_add, none_eq_bot, some_eq_coe
-/
lemma _root_.IsAddRightRegular.withBot (ha : IsAddRightRegular a) :
    IsAddRightRegular (a : WithBot α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_bot, some_eq_coe, ← coe_add]; simpa using @ha _ _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `_root_.AddLECancellable.withBot` / 引理 `_root_.AddLECancellable.withBot`

English:
lemma _root_.AddLECancellable.withBot
  given: [LE α] (ha : AddLECancellable a)
  proof: by
  rintro (_ | b) (_ | c)
  · simp [none_eq_bot]
  · simp [none_eq_bot]
  · simp [some_eq_coe, ← coe_add, none_eq_bot]
  · simpa [none_eq_bot, some_eq_coe, ← coe_add] using fun a => ha a

中文:
引理 _root_.AddLECancellable.withBot
  条件: [LE α] (ha : AddLECancellable a)
  证明: by
  rintro (_ | b) (_ | c)
  · simp [none_eq_bot]
  · simp [none_eq_bot]
  · simp [some_eq_coe, ← coe_add, none_eq_bot]
  · simpa [none_eq_bot, some_eq_coe, ← coe_add] using fun a => ha a

Depends on / 依赖: coe_add, none_eq_bot, some_eq_coe
-/
lemma _root_.AddLECancellable.withBot [LE α] (ha : AddLECancellable a) :
    AddLECancellable (a : WithBot α) := by
  rintro (_ | b) (_ | c)
  · simp [none_eq_bot]
  · simp [none_eq_bot]
  · simp [some_eq_coe, ← coe_add, none_eq_bot]
  · simpa [none_eq_bot, some_eq_coe, ← coe_add] using fun a => ha a

/--
lemma `add_right_inj` / 引理 `add_right_inj`

English:
lemma add_right_inj
  given: [IsRightCancelAdd α] (hz : z != ⊥)
  statement: x + z = y + z ↔ x = y
  proof: by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]

中文:
引理 add_right_inj
  条件: [是右消去加法 α] (hz : z != ⊥)
  结论: x + z = y + z ↔ x = y
  证明: by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]

Depends on / 依赖: coe_add
-/
lemma add_right_inj [IsRightCancelAdd α] (hz : z != ⊥) : x + z = y + z ↔ x = y := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]

/--
lemma `add_right_cancel` / 引理 `add_right_cancel`

English:
lemma add_right_cancel
  given: [IsRightCancelAdd α] (hz : z != ⊥) (h : x + z = y + z)
  statement: x = y
  proof: (WithBot.add_right_inj hz).1 h

中文:
引理 add_right_cancel
  条件: [是右消去加法 α] (hz : z != ⊥) (h : x + z = y + z)
  结论: x = y
  证明: (WithBot.add_right_inj hz).1 h

Depends on / 依赖: WithBot, WithBot.add_right_inj, add_right_inj
-/
lemma add_right_cancel [IsRightCancelAdd α] (hz : z != ⊥) (h : x + z = y + z) : x = y :=
  (WithBot.add_right_inj hz).1 h

/--
lemma `add_left_inj` / 引理 `add_left_inj`

English:
lemma add_left_inj
  given: [IsLeftCancelAdd α] (hx : x != ⊥)
  statement: x + y = x + z ↔ y = z
  proof: by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]

中文:
引理 add_left_inj
  条件: [是左消去加法 α] (hx : x != ⊥)
  结论: x + y = x + z ↔ y = z
  证明: by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]

Depends on / 依赖: coe_add
-/
lemma add_left_inj [IsLeftCancelAdd α] (hx : x != ⊥) : x + y = x + z ↔ y = z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]

/--
lemma `add_left_cancel` / 引理 `add_left_cancel`

English:
lemma add_left_cancel
  given: [IsLeftCancelAdd α] (hx : x != ⊥) (h : x + y = x + z)
  statement: y = z
  proof: (WithBot.add_left_inj hx).1 h

中文:
引理 add_left_cancel
  条件: [是左消去加法 α] (hx : x != ⊥) (h : x + y = x + z)
  结论: y = z
  证明: (WithBot.add_left_inj hx).1 h

Depends on / 依赖: WithBot, WithBot.add_left_inj, add_left_inj
-/
lemma add_left_cancel [IsLeftCancelAdd α] (hx : x != ⊥) (h : x + y = x + z) : y = z :=
  (WithBot.add_left_inj hx).1 h

/--
Instance `addLeftMono` / 实例 `addLeftMono`

English:
instance addLeftMono
  signature: [LE α] [AddLeftMono α]
  body: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ => by gcongr

中文:
实例 addLeftMono
  签名: [LE α] [AddLeftMono α]
  定义体: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ => by gcongr

Depends on / 依赖: coe_add
-/
instance addLeftMono [LE α] [AddLeftMono α] : AddLeftMono (WithBot α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ => by gcongr

/--
Instance `addRightMono` / 实例 `addRightMono`

English:
instance addRightMono
  signature: [LE α] [AddRightMono α]
  body: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using fun _ => by gcongr

中文:
实例 addRightMono
  签名: [LE α] [AddRightMono α]
  定义体: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using fun _ => by gcongr

Depends on / 依赖: coe_add
-/
instance addRightMono [LE α] [AddRightMono α] : AddRightMono (WithBot α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using fun _ => by gcongr

/--
Instance `addLeftReflectLT` / 实例 `addLeftReflectLT`

English:
instance addLeftReflectLT
  signature: [LT α] [AddLeftReflectLT α]
  body: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using lt_of_add_lt_add_left

中文:
实例 addLeftReflectLT
  签名: [LT α] [AddLeftReflectLT α]
  定义体: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using lt_of_add_lt_add_left

Depends on / 依赖: coe_add, lt_of_add_lt_add_left
-/
instance addLeftReflectLT [LT α] [AddLeftReflectLT α] : AddLeftReflectLT (WithBot α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using lt_of_add_lt_add_left

/--
Instance `addRightReflectLT` / 实例 `addRightReflectLT`

English:
instance addRightReflectLT
  signature: [LT α] [AddRightReflectLT α]
  body: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using lt_of_add_lt_add_right

中文:
实例 addRightReflectLT
  签名: [LT α] [AddRightReflectLT α]
  定义体: by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using lt_of_add_lt_add_right

Depends on / 依赖: coe_add, lt_of_add_lt_add_right
-/
instance addRightReflectLT [LT α] [AddRightReflectLT α] : AddRightReflectLT (WithBot α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using lt_of_add_lt_add_right

/--
lemma `le_of_add_le_add_left` / 引理 `le_of_add_le_add_left`

English:
lemma le_of_add_le_add_left
  given: [LE α] [AddLeftReflectLE α] (hx : x != ⊥)
  proof: by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using le_of_add_le_add_left

中文:
引理 le_of_add_le_add_left
  条件: [LE α] [加法LeftReflectLE α] (hx : x != ⊥)
  证明: by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using le_of_add_le_add_left
-/
protected lemma le_of_add_le_add_left [LE α] [AddLeftReflectLE α] (hx : x != ⊥) :
    x + y <= x + z -> y <= z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using le_of_add_le_add_left

/--
lemma `le_of_add_le_add_right` / 引理 `le_of_add_le_add_right`

English:
lemma le_of_add_le_add_right
  given: [LE α] [AddRightReflectLE α] (hz : z != ⊥)
  proof: by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using le_of_add_le_add_right

中文:
引理 le_of_add_le_add_right
  条件: [LE α] [加法RightReflectLE α] (hz : z != ⊥)
  证明: by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using le_of_add_le_add_right
-/
protected lemma le_of_add_le_add_right [LE α] [AddRightReflectLE α] (hz : z != ⊥) :
    x + z <= y + z -> x <= y := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using le_of_add_le_add_right

/--
lemma `add_lt_add_left` / 引理 `add_lt_add_left`

English:
lemma add_lt_add_left
  given: [LT α] [AddLeftStrictMono α] (hx : x != ⊥)
  proof: by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ => by gcongr

中文:
引理 add_lt_add_left
  条件: [LT α] [AddLeftStrictMono α] (hx : x != ⊥)
  证明: by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ => by gcongr
-/
protected lemma add_lt_add_left [LT α] [AddLeftStrictMono α] (hx : x != ⊥) :
    y < z -> x + y < x + z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ => by gcongr

/--
lemma `add_lt_add_right` / 引理 `add_lt_add_right`

English:
lemma add_lt_add_right
  given: [LT α] [AddRightStrictMono α] (hz : z != ⊥)
  proof: by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using fun _ => by gcongr

中文:
引理 add_lt_add_right
  条件: [LT α] [AddRightStrictMono α] (hz : z != ⊥)
  证明: by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using fun _ => by gcongr
-/
protected lemma add_lt_add_right [LT α] [AddRightStrictMono α] (hz : z != ⊥) :
    x < y -> x + z < y + z := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using fun _ => by gcongr

/--
lemma `add_le_add_iff_left` / 引理 `add_le_add_iff_left`

English:
lemma add_le_add_iff_left
  given: [LE α] [AddLeftMono α] [AddLeftReflectLE α] (hx : x != ⊥)
  proof: ⟨WithBot.le_of_add_le_add_left hx, fun _ => by gcongr⟩

中文:
引理 add_le_add_iff_left
  条件: [LE α] [AddLeftMono α] [加法LeftReflectLE α] (hx : x != ⊥)
  证明: ⟨WithBot.le_of_add_le_add_left hx, fun _ => by gcongr⟩
-/
protected lemma add_le_add_iff_left [LE α] [AddLeftMono α] [AddLeftReflectLE α] (hx : x != ⊥) :
    x + y <= x + z ↔ y <= z := ⟨WithBot.le_of_add_le_add_left hx, fun _ => by gcongr⟩

/--
lemma `add_le_add_iff_right` / 引理 `add_le_add_iff_right`

English:
lemma add_le_add_iff_right
  given: [LE α] [AddRightMono α] [AddRightReflectLE α] (hz : z != ⊥)
  proof: ⟨WithBot.le_of_add_le_add_right hz, fun _ => by gcongr⟩

中文:
引理 add_le_add_iff_right
  条件: [LE α] [AddRightMono α] [加法RightReflectLE α] (hz : z != ⊥)
  证明: ⟨WithBot.le_of_add_le_add_right hz, fun _ => by gcongr⟩
-/
protected lemma add_le_add_iff_right [LE α] [AddRightMono α] [AddRightReflectLE α] (hz : z != ⊥) :
    x + z <= y + z ↔ x <= y := ⟨WithBot.le_of_add_le_add_right hz, fun _ => by gcongr⟩

/--
lemma `add_lt_add_iff_left` / 引理 `add_lt_add_iff_left`

English:
lemma add_lt_add_iff_left
  given: [LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (hx : x != ⊥)
  proof: ⟨lt_of_add_lt_add_left, WithBot.add_lt_add_left hx⟩

中文:
引理 add_lt_add_iff_left
  条件: [LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (hx : x != ⊥)
  证明: ⟨lt_of_add_lt_add_left, WithBot.add_lt_add_left hx⟩
-/
protected lemma add_lt_add_iff_left [LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (hx : x != ⊥) :
    x + y < x + z ↔ y < z := ⟨lt_of_add_lt_add_left, WithBot.add_lt_add_left hx⟩

/--
lemma `add_lt_add_iff_right` / 引理 `add_lt_add_iff_right`

English:
lemma add_lt_add_iff_right
  statement: [LT α] [AddRightStrictMono α] [AddRightReflectLT α]
  proof: ⟨lt_of_add_lt_add_right, WithBot.add_lt_add_right hz⟩

中文:
引理 add_lt_add_iff_right
  结论: [LT α] [AddRightStrictMono α] [AddRightReflectLT α]
  证明: ⟨lt_of_add_lt_add_right, WithBot.add_lt_add_right hz⟩
-/
protected lemma add_lt_add_iff_right [LT α] [AddRightStrictMono α] [AddRightReflectLT α]
    (hz : z != ⊥) : x + z < y + z ↔ x < y := ⟨lt_of_add_lt_add_right, WithBot.add_lt_add_right hz⟩

/--
theorem `add_lt_add_of_le_of_lt` / 定理 `add_lt_add_of_le_of_lt`

English:
theorem add_lt_add_of_le_of_lt
  statement: [Preorder α] [AddLeftStrictMono α]
  proof: (WithBot.add_lt_add_left hw hxz).trans_le by gcongr

中文:
定理 add_lt_add_of_le_of_lt
  结论: [预序 α] [AddLeftStrictMono α]
  证明: (WithBot.add_lt_add_left hw hxz).trans_le by gcongr
-/
protected theorem add_lt_add_of_le_of_lt [Preorder α] [AddLeftStrictMono α]
    [AddRightMono α] (hw : w != ⊥) (hwy : w <= y) (hxz : x < z) :
    w + x < y + z :=
(WithBot.add_lt_add_left hw hxz).trans_le by gcongr

/--
theorem `add_lt_add_of_lt_of_le` / 定理 `add_lt_add_of_lt_of_le`

English:
theorem add_lt_add_of_lt_of_le
  statement: [Preorder α] [AddLeftMono α]
  proof: (WithBot.add_lt_add_right hx hwy).trans_le by gcongr

中文:
定理 add_lt_add_of_lt_of_le
  结论: [预序 α] [AddLeftMono α]
  证明: (WithBot.add_lt_add_right hx hwy).trans_le by gcongr
-/
protected theorem add_lt_add_of_lt_of_le [Preorder α] [AddLeftMono α]
    [AddRightStrictMono α] (hx : x != ⊥) (hwy : w < y) (hxz : x <= z) :
    w + x < y + z :=
(WithBot.add_lt_add_right hx hwy).trans_le by gcongr

/--
lemma `addLECancellable_of_ne_bot` / 引理 `addLECancellable_of_ne_bot`

English:
lemma addLECancellable_of_ne_bot
  statement: [LE α] [AddLeftReflectLE α]
  proof: fun _b _c => WithBot.le_of_add_le_add_left hx

中文:
引理 addLECancellable_of_ne_bot
  结论: [LE α] [加法LeftReflectLE α]
  证明: fun _b _c => WithBot.le_of_add_le_add_left hx

Depends on / 依赖: WithBot, WithBot.le_of_add_le_add_left, le_of_add_le_add_left
-/
lemma addLECancellable_of_ne_bot [LE α] [AddLeftReflectLE α]
    (hx : x != ⊥) : AddLECancellable x := fun _b _c => WithBot.le_of_add_le_add_left hx

/--
lemma `addLECancellable_of_lt_bot` / 引理 `addLECancellable_of_lt_bot`

English:
lemma addLECancellable_of_lt_bot
  statement: [Preorder α] [AddLeftReflectLE α]
  proof: addLECancellable_of_ne_bot hx.ne

中文:
引理 addLECancellable_of_lt_bot
  结论: [预序 α] [加法LeftReflectLE α]
  证明: addLECancellable_of_ne_bot hx.ne

Depends on / 依赖: addLECancellable_of_ne_bot, hx.ne
-/
lemma addLECancellable_of_lt_bot [Preorder α] [AddLeftReflectLE α]
    (hx : x < ⊥) : AddLECancellable x := addLECancellable_of_ne_bot hx.ne

/--
lemma `addLECancellable_coe` / 引理 `addLECancellable_coe`

English:
lemma addLECancellable_coe
  given: [LE α] [AddLeftReflectLE α] (a : α)
  proof: addLECancellable_of_ne_bot coe_ne_bot

中文:
引理 addLECancellable_coe
  条件: [LE α] [加法LeftReflectLE α] (a : α)
  证明: addLECancellable_of_ne_bot coe_ne_bot

Depends on / 依赖: addLECancellable_of_ne_bot, coe_ne_bot
-/
lemma addLECancellable_coe [LE α] [AddLeftReflectLE α] (a : α) :
    AddLECancellable (a : WithBot α) := addLECancellable_of_ne_bot coe_ne_bot

/--
lemma `addLECancellable_iff_ne_bot` / 引理 `addLECancellable_iff_ne_bot`

English:
lemma addLECancellable_iff_ne_bot
  statement: [Nonempty α] [Preorder α]
  proof: by rintro h rfl; exact (bot_lt_coe <| Classical.arbitrary _).not_ge h by simp
  mpr := addLECancellable_of_ne_bot

中文:
引理 addLECancellable_iff_ne_bot
  结论: [非空 α] [预序 α]
  证明: by rintro h rfl; exact (bot_lt_coe <| Classical.arbitrary _).not_ge h by simp
  mpr := addLECancellable_of_ne_bot

Depends on / 依赖: Classical, Classical.arbitrary, addLECancellable_of_ne_bot, arbitrary, bot_lt_coe, not_ge
-/
lemma addLECancellable_iff_ne_bot [Nonempty α] [Preorder α]
    [AddLeftReflectLE α] : AddLECancellable x ↔ x != ⊥ where
mp := by rintro h rfl; exact (bot_lt_coe <| Classical.arbitrary _).not_ge h by simp
  mpr := addLECancellable_of_ne_bot

/--
lemma `add_le_add_iff_right'` / 引理 `add_le_add_iff_right'`

English:
lemma add_le_add_iff_right'
  statement: {α : Type*} [Add α] [LE α]
  proof: by
  induction a <;> induction b <;> induction c <;> norm_cast at * <;>
    aesop (add simp WithTop.add_le_add_iff_right)

中文:
引理 add_le_add_iff_right'
  结论: {α : 类型} [加法 α] [LE α]
  证明: by
  induction a <;> induction b <;> induction c <;> norm_cast at * <;>
    aesop (add simp WithTop.add_le_add_iff_right)

Depends on / 依赖: WithTop, WithTop.add_le_add_iff_right, add_le_add_iff_right
-/
lemma add_le_add_iff_right' {α : Type*} [Add α] [LE α]
    [AddRightMono α] [AddRightReflectLE α]
    {a b c : WithBot (WithTop α)} (hc : c != ⊥) (hc' : c != ⊤) :
    a + c <= b + c ↔ a <= b := by
  induction a <;> induction b <;> induction c <;> norm_cast at * <;>
    aesop (add simp WithTop.add_le_add_iff_right)

-- There is no `WithBot.map_mul_of_mulHom`, since `WithBot` does not have a multiplication.
@[simp]
/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  statement: {F} [Add β] [FunLike F α β] [AddHomClass F α β]
  proof: by
  induction a
  · exact (bot_add _).symm
  · induction b
    · exact (add_bot _).symm
    · rw [map_coe, map_coe, ← coe_add, ← coe_add, ← map_add]
      rfl

中文:
定理 map_add
  结论: {F} [加法 β] [函数状 F α β] [加法态射类 F α β]
  证明: by
  induction a
  · exact (bot_add _).symm
  · induction b
    · exact (add_bot _).symm
    · rw [map_coe, map_coe, ← coe_add, ← coe_add, ← map_add]
      rfl
-/
protected theorem map_add {F} [Add β] [FunLike F α β] [AddHomClass F α β]
    (f : F) (a b : WithBot α) :
    (a + b).map f = a.map f + b.map f := by
  induction a
  · exact (bot_add _).symm
  · induction b
    · exact (add_bot _).symm
    · rw [map_coe, map_coe, ← coe_add, ← coe_add, ← map_add]
      rfl

end Add

/--
Instance `addSemigroup` / 实例 `addSemigroup`

English:
instance addSemigroup
  signature: [AddSemigroup α]
  body: inferInstanceAs AddSemigroup (WithTop α)

中文:
实例 addSemigroup
  签名: [加法半群 α]
  定义体: inferInstanceAs AddSemigroup (WithTop α)

Depends on / 依赖: AddSemigroup, WithTop
-/
instance addSemigroup [AddSemigroup α] : AddSemigroup (WithBot α) :=
inferInstanceAs AddSemigroup (WithTop α)

/--
Instance `addCommSemigroup` / 实例 `addCommSemigroup`

English:
instance addCommSemigroup
  signature: [AddCommSemigroup α]
  body: inferInstanceAs AddCommSemigroup (WithTop α)

中文:
实例 addCommSemigroup
  签名: [加法交换半群 α]
  定义体: inferInstanceAs AddCommSemigroup (WithTop α)

Depends on / 依赖: AddCommSemigroup, WithTop
-/
instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (WithBot α) :=
inferInstanceAs AddCommSemigroup (WithTop α)

/--
Instance `addZeroClass` / 实例 `addZeroClass`

English:
instance addZeroClass
  signature: [AddZeroClass α]
  body: inferInstanceAs AddZeroClass (WithTop α)

中文:
实例 addZeroClass
  签名: [加法零类 α]
  定义体: inferInstanceAs AddZeroClass (WithTop α)

Depends on / 依赖: AddZeroClass, WithTop
-/
instance addZeroClass [AddZeroClass α] : AddZeroClass (WithBot α) :=
inferInstanceAs AddZeroClass (WithTop α)

section AddMonoid
variable [AddMonoid α]

/--
Instance `addMonoid` / 实例 `addMonoid`

English:
instance addMonoid
  signature: : AddMonoid (WithBot α)
  body: inferInstanceAs AddMonoid (WithTop α)

中文:
实例 addMonoid
  签名: : 加法幺半群 (WithBot α)
  定义体: inferInstanceAs AddMonoid (WithTop α)

Depends on / 依赖: AddMonoid, WithTop
-/
instance addMonoid : AddMonoid (WithBot α) :=
inferInstanceAs AddMonoid (WithTop α)

/--
Definition of `addHom` / `addHom` 的定义

English:
definition addHom
  signature: : α ->+ WithBot α where
  body: WithTop.some
  map_zero' := rfl
  map_add' _ _ := rfl

中文:
定义 addHom
  签名: : α ->+ WithBot α where
  定义体: WithTop.some
  map_zero' := rfl
  map_add' _ _ := rfl

Depends on / 依赖: WithTop, WithTop.some
-/
def addHom : α ->+ WithBot α where
  toFun := WithTop.some
  map_zero' := rfl
  map_add' _ _ := rfl

/--
lemma `coe_addHom` / 引理 `coe_addHom`

English:
lemma coe_addHom
  statement: ⇑(addHom : α ->+ WithBot α) = WithBot.some
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_addHom
  结论: ⇑(addHom : α ->+ WithBot α) = WithBot.some
  证明: rfl

@[simp, norm_cast]
-/
@[simp, norm_cast] lemma coe_addHom : ⇑(addHom : α ->+ WithBot α) = WithBot.some := rfl

@[simp, norm_cast]
/--
lemma `coe_nsmul` / 引理 `coe_nsmul`

English:
lemma coe_nsmul
  given: (a : α) (n : Nat)
  statement: ↑(n • a) = n • (a : WithBot α)
  proof: (addHom : α ->+ WithBot α).map_nsmul _ _

中文:
引理 coe_nsmul
  条件: (a : α) (n : 自然数)
  结论: ↑(n • a) = n • (a : WithBot α)
  证明: (addHom : α ->+ WithBot α).map_nsmul _ _

Depends on / 依赖: WithBot, addHom, map_nsmul
-/
lemma coe_nsmul (a : α) (n : Nat) : ↑(n • a) = n • (a : WithBot α) :=
  (addHom : α ->+ WithBot α).map_nsmul _ _

end AddMonoid

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: [AddCommMonoid α]
  body: inferInstanceAs AddCommMonoid (WithTop α)

中文:
实例 addCommMonoid
  签名: [加法交换幺半群 α]
  定义体: inferInstanceAs AddCommMonoid (WithTop α)

Depends on / 依赖: AddCommMonoid, WithTop
-/
instance addCommMonoid [AddCommMonoid α] : AddCommMonoid (WithBot α) :=
inferInstanceAs AddCommMonoid (WithTop α)

section NatCast
variable [NatCast α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (WithBot α)
  body: (n : α)

中文:
实例 :
  签名: 自然数嵌入 (WithBot α)
  定义体: (n : α)
-/
instance : NatCast (WithBot α) where natCast n := (n : α)

/--
lemma `unbotD_natCast` / 引理 `unbotD_natCast`

English:
lemma unbotD_natCast
  given: (d : α) (n : Nat)
  statement: unbotD d n = n
  proof: rfl

@[to_dual (attr := simp)]

中文:
引理 unbotD_natCast
  条件: (d : α) (n : 自然数)
  结论: unbotD d n = n
  证明: rfl

@[to_dual (attr := simp)]
-/
@[to_dual (attr := simp)] lemma unbotD_natCast (d : α) (n : Nat) : unbotD d n = n := rfl

@[to_dual (attr := simp)]
/--
lemma `unbotD_ofNat` / 引理 `unbotD_ofNat`

English:
lemma unbotD_ofNat
  given: (d : α) (n : Nat) [n.AtLeastTwo]
  statement: unbotD d ofNat(n) = ofNat(n)
  proof: rfl

中文:
引理 unbotD_of自然数
  条件: (d : α) (n : 自然数) [n.AtLeastTwo]
  结论: unbotD d of自然数(n) = of自然数(n)
  证明: rfl
-/
lemma unbotD_ofNat (d : α) (n : Nat) [n.AtLeastTwo] : unbotD d ofNat(n) = ofNat(n) := rfl

end NatCast

section AddMonoidWithOne
variable [AddMonoidWithOne α]

/--
Instance `addMonoidWithOne` / 实例 `addMonoidWithOne`

English:
instance addMonoidWithOne
  signature: : AddMonoidWithOne (WithBot α)
  body: inferInstanceAs AddMonoidWithOne (WithTop α)

中文:
实例 addMonoidWithOne
  签名: : 加法带幺幺半群 (WithBot α)
  定义体: inferInstanceAs AddMonoidWithOne (WithTop α)

Depends on / 依赖: AddMonoidWithOne, WithTop
-/
instance addMonoidWithOne : AddMonoidWithOne (WithBot α) :=
inferInstanceAs AddMonoidWithOne (WithTop α)

/--
lemma `coe_natCast` / 引理 `coe_natCast`

English:
lemma coe_natCast
  given: (n : Nat)
  statement: ((n : α) : WithBot α) = n
  proof: rfl

中文:
引理 coe_natCast
  条件: (n : 自然数)
  结论: ((n : α) : WithBot α) = n
  证明: rfl
-/
@[norm_cast] lemma coe_natCast (n : Nat) : ((n : α) : WithBot α) = n := rfl

/--
lemma `natCast_ne_bot` / 引理 `natCast_ne_bot`

English:
lemma natCast_ne_bot
  given: (n : Nat)
  statement: (n : WithBot α) != ⊥
  proof: coe_ne_bot

中文:
引理 natCast_ne_bot
  条件: (n : 自然数)
  结论: (n : WithBot α) != ⊥
  证明: coe_ne_bot
-/
@[simp] lemma natCast_ne_bot (n : Nat) : (n : WithBot α) != ⊥ := coe_ne_bot

/--
lemma `bot_ne_natCast` / 引理 `bot_ne_natCast`

English:
lemma bot_ne_natCast
  given: (n : Nat)
  statement: (⊥ : WithBot α) != n
  proof: bot_ne_coe

中文:
引理 bot_ne_natCast
  条件: (n : 自然数)
  结论: (⊥ : WithBot α) != n
  证明: bot_ne_coe
-/
@[simp] lemma bot_ne_natCast (n : Nat) : (⊥ : WithBot α) != n := bot_ne_coe

/--
lemma `coe_ofNat` / 引理 `coe_ofNat`

English:
lemma coe_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: rfl

中文:
引理 coe_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: rfl
-/
@[simp] lemma coe_ofNat (n : Nat) [n.AtLeastTwo] :
    ((ofNat(n) : α) : WithBot α) = ofNat(n) := rfl
/--
lemma `coe_eq_ofNat` / 引理 `coe_eq_ofNat`

English:
lemma coe_eq_ofNat
  given: (n : Nat) [n.AtLeastTwo] (m : α)
  proof: coe_eq_coe

中文:
引理 coe_eq_of自然数
  条件: (n : 自然数) [n.AtLeastTwo] (m : α)
  证明: coe_eq_coe
-/
@[simp] lemma coe_eq_ofNat (n : Nat) [n.AtLeastTwo] (m : α) :
    (m : WithBot α) = ofNat(n) ↔ m = ofNat(n) :=
  coe_eq_coe
/--
lemma `ofNat_eq_coe` / 引理 `ofNat_eq_coe`

English:
lemma ofNat_eq_coe
  given: (n : Nat) [n.AtLeastTwo] (m : α)
  proof: coe_eq_coe

中文:
引理 of自然数_eq_coe
  条件: (n : 自然数) [n.AtLeastTwo] (m : α)
  证明: coe_eq_coe
-/
@[simp] lemma ofNat_eq_coe (n : Nat) [n.AtLeastTwo] (m : α) :
    ofNat(n) = (m : WithBot α) ↔ ofNat(n) = m :=
  coe_eq_coe
/--
lemma `ofNat_ne_bot` / 引理 `ofNat_ne_bot`

English:
lemma ofNat_ne_bot
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : WithBot α) != ⊥
  proof: natCast_ne_bot n

中文:
引理 of自然数_ne_bot
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : WithBot α) != ⊥
  证明: natCast_ne_bot n
-/
@[simp] lemma ofNat_ne_bot (n : Nat) [n.AtLeastTwo] : (ofNat(n) : WithBot α) != ⊥ :=
  natCast_ne_bot n
/--
lemma `bot_ne_ofNat` / 引理 `bot_ne_ofNat`

English:
lemma bot_ne_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (⊥ : WithBot α) != ofNat(n)
  proof: bot_ne_natCast n

中文:
引理 bot_ne_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (⊥ : WithBot α) != of自然数(n)
  证明: bot_ne_natCast n
-/
@[simp] lemma bot_ne_ofNat (n : Nat) [n.AtLeastTwo] : (⊥ : WithBot α) != ofNat(n) :=
  bot_ne_natCast n

/--
lemma `map_ofNat` / 引理 `map_ofNat`

English:
lemma map_ofNat
  given: {f : α -> β} (n : Nat) [n.AtLeastTwo]
  proof: map_coe f n

中文:
引理 map_of自然数
  条件: {f : α -> β} (n : 自然数) [n.AtLeastTwo]
  证明: map_coe f n
-/
@[simp] lemma map_ofNat {f : α -> β} (n : Nat) [n.AtLeastTwo] :
    WithBot.map f (ofNat(n) : WithBot α) = f ofNat(n) := map_coe f n

/--
lemma `map_natCast` / 引理 `map_natCast`

English:
lemma map_natCast
  given: {f : α -> β} (n : Nat)
  proof: map_coe f n

中文:
引理 map_natCast
  条件: {f : α -> β} (n : 自然数)
  证明: map_coe f n
-/
@[simp] lemma map_natCast {f : α -> β} (n : Nat) :
    WithBot.map f (n : WithBot α) = f n := map_coe f n

/--
lemma `map_eq_ofNat_iff` / 引理 `map_eq_ofNat_iff`

English:
lemma map_eq_ofNat_iff
  given: {f : β -> α} {n : Nat} [n.AtLeastTwo] {a : WithBot β}
  proof: map_eq_some_iff

中文:
引理 map_eq_of自然数_iff
  条件: {f : β -> α} {n : 自然数} [n.AtLeastTwo] {a : WithBot β}
  证明: map_eq_some_iff

Depends on / 依赖: map_eq_some_iff
-/
lemma map_eq_ofNat_iff {f : β -> α} {n : Nat} [n.AtLeastTwo] {a : WithBot β} :
    a.map f = ofNat(n) ↔ exists x, a = .some x ∧ f x = n := map_eq_some_iff

/--
lemma `ofNat_eq_map_iff` / 引理 `ofNat_eq_map_iff`

English:
lemma ofNat_eq_map_iff
  given: {f : β -> α} {n : Nat} [n.AtLeastTwo] {a : WithBot β}
  proof: some_eq_map_iff

中文:
引理 of自然数_eq_map_iff
  条件: {f : β -> α} {n : 自然数} [n.AtLeastTwo] {a : WithBot β}
  证明: some_eq_map_iff

Depends on / 依赖: some_eq_map_iff
-/
lemma ofNat_eq_map_iff {f : β -> α} {n : Nat} [n.AtLeastTwo] {a : WithBot β} :
    ofNat(n) = a.map f ↔ exists x, a = .some x ∧ f x = n := some_eq_map_iff

/--
lemma `map_eq_natCast_iff` / 引理 `map_eq_natCast_iff`

English:
lemma map_eq_natCast_iff
  given: {f : β -> α} {n : Nat} {a : WithBot β}
  proof: map_eq_some_iff

中文:
引理 map_eq_natCast_iff
  条件: {f : β -> α} {n : 自然数} {a : WithBot β}
  证明: map_eq_some_iff

Depends on / 依赖: map_eq_some_iff
-/
lemma map_eq_natCast_iff {f : β -> α} {n : Nat} {a : WithBot β} :
    a.map f = n ↔ exists x, a = .some x ∧ f x = n := map_eq_some_iff

/--
lemma `natCast_eq_map_iff` / 引理 `natCast_eq_map_iff`

English:
lemma natCast_eq_map_iff
  given: {f : β -> α} {n : Nat} {a : WithBot β}
  proof: some_eq_map_iff

中文:
引理 natCast_eq_map_iff
  条件: {f : β -> α} {n : 自然数} {a : WithBot β}
  证明: some_eq_map_iff

Depends on / 依赖: some_eq_map_iff
-/
lemma natCast_eq_map_iff {f : β -> α} {n : Nat} {a : WithBot β} :
    n = a.map f ↔ exists x, a = .some x ∧ f x = n := some_eq_map_iff

/--
lemma `bot_lt_natCast` / 引理 `bot_lt_natCast`

English:
lemma bot_lt_natCast
  given: [LT α] (n : Nat)
  statement: (⊥ : WithBot α) < n
  proof: WithBot.bot_lt_coe _

中文:
引理 bot_lt_natCast
  条件: [LT α] (n : 自然数)
  结论: (⊥ : WithBot α) < n
  证明: WithBot.bot_lt_coe _
-/
@[simp] lemma bot_lt_natCast [LT α] (n : Nat) : (⊥ : WithBot α) < n :=
  WithBot.bot_lt_coe _

end AddMonoidWithOne

/--
Instance `charZero` / 实例 `charZero`

English:
instance charZero
  signature: [AddMonoidWithOne α] [CharZero α]
  body: inferInstanceAs CharZero (WithTop α)

中文:
实例 charZero
  签名: [加法带幺幺半群 α] [特征零 α]
  定义体: inferInstanceAs CharZero (WithTop α)

Depends on / 依赖: CharZero, WithTop
-/
instance charZero [AddMonoidWithOne α] [CharZero α] : CharZero (WithBot α) :=
inferInstanceAs CharZero (WithTop α)

/--
Instance `addCommMonoidWithOne` / 实例 `addCommMonoidWithOne`

English:
instance addCommMonoidWithOne
  signature: [AddCommMonoidWithOne α]
  body: inferInstanceAs AddCommMonoidWithOne (WithTop α)

中文:
实例 addCommMonoidWithOne
  签名: [加法交换带幺幺半群 α]
  定义体: inferInstanceAs AddCommMonoidWithOne (WithTop α)

Depends on / 依赖: AddCommMonoidWithOne, WithTop
-/
instance addCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne (WithBot α) :=
inferInstanceAs AddCommMonoidWithOne (WithTop α)

/-- A version of `WithBot.map` for `OneHom`s. -/
@[to_additive (attr := simps -fullyApplied)
  /-- A version of `WithBot.map` for `ZeroHom`s -/]
/--
Definition of `_root_.OneHom.withBotMap` / `_root_.OneHom.withBotMap` 的定义

English:
definition _root_.OneHom.withBotMap
  signature: {M N : Type*} [One M] [One N] (f : OneHom M N)
  body: WithBot.map f
  map_one' := by rw [WithBot.map_one, map_one, coe_one]

中文:
定义 _root_.幺态射.withBotMap
  签名: {M N : 类型} [幺 M] [幺 N] (f : 幺态射 M N)
  定义体: WithBot.map f
  map_one' := by rw [WithBot.map_one, map_one, coe_one]
-/
protected def _root_.OneHom.withBotMap {M N : Type*} [One M] [One N] (f : OneHom M N) :
    OneHom (WithBot M) (WithBot N) where
  toFun := WithBot.map f
  map_one' := by rw [WithBot.map_one, map_one, coe_one]

/-- A version of `WithBot.map` for `AddHom`s. -/
@[simps -fullyApplied]
/--
Definition of `_root_.AddHom.withBotMap` / `_root_.AddHom.withBotMap` 的定义

English:
definition _root_.AddHom.withBotMap
  signature: {M N : Type*} [Add M] [Add N] (f : AddHom M N)
  body: WithBot.map f
  map_add' := WithBot.map_add f

中文:
定义 _root_.加法半群态射.withBotMap
  签名: {M N : 类型} [加法 M] [加法 N] (f : 加法半群态射 M N)
  定义体: WithBot.map f
  map_add' := WithBot.map_add f
-/
protected def _root_.AddHom.withBotMap {M N : Type*} [Add M] [Add N] (f : AddHom M N) :
    AddHom (WithBot M) (WithBot N) where
  toFun := WithBot.map f
  map_add' := WithBot.map_add f

/-- A version of `WithBot.map` for `AddMonoidHom`s. -/
@[simps -fullyApplied]
/--
Definition of `_root_.AddMonoidHom.withBotMap` / `_root_.AddMonoidHom.withBotMap` 的定义

English:
definition _root_.AddMonoidHom.withBotMap
  signature: {M N : Type*} [AddZeroClass M] [AddZeroClass N]
  body: { ZeroHom.withBotMap f.toZeroHom, AddHom.withBotMap f.toAddHom with toFun := WithBot.map f }

中文:
定义 _root_.加法幺半群态射.withBotMap
  签名: {M N : 类型} [加法零类 M] [加法零类 N]
  定义体: { ZeroHom.withBotMap f.toZeroHom, AddHom.withBotMap f.toAddHom with toFun := WithBot.map f }
-/
protected def _root_.AddMonoidHom.withBotMap {M N : Type*} [AddZeroClass M] [AddZeroClass N]
    (f : M ->+ N) : WithBot M ->+ WithBot N :=
  { ZeroHom.withBotMap f.toZeroHom, AddHom.withBotMap f.toAddHom with toFun := WithBot.map f }

end WithBot

namespace AddEquiv

variable {γ : Type*} [Add α] [Add β] [Add γ] (e e₁ : α ≃+ β) (e₂ : β ≃+ γ)

/-- A `AddEquiv` version of `Equiv.withBotCongr`. -/
@[to_dual (attr := simps! apply) /-- A `AddEquiv` version of `Equiv.withTopCongr`. -/]
/--
Definition of `withBotCongr` / `withBotCongr` 的定义

English:
definition withBotCongr
  signature: : WithBot α ≃+ WithBot β where
  body: e.toEquiv.withBotCongr
  map_add' := e.toAddHom.withBotMap.map_add'

@[to_dual (attr := simp)]

中文:
定义 withBotCongr
  签名: : WithBot α ≃+ WithBot β where
  定义体: e.toEquiv.withBotCongr
  map_add' := e.toAddHom.withBotMap.map_add'

@[to_dual (attr := simp)]

Depends on / 依赖: e.toEquiv.withBotCongr, toEquiv, withBotCongr
-/
def withBotCongr : WithBot α ≃+ WithBot β where
  __ := e.toEquiv.withBotCongr
  map_add' := e.toAddHom.withBotMap.map_add'

@[to_dual (attr := simp)]
/--
lemma `coe_withBotCongr` / 引理 `coe_withBotCongr`

English:
lemma coe_withBotCongr
  statement: e.withBotCongr = WithBot.map e
  proof: rfl

@[to_dual (attr := simp)]

中文:
引理 coe_withBotCongr
  结论: e.withBotCongr = WithBot.map e
  证明: rfl

@[to_dual (attr := simp)]
-/
lemma coe_withBotCongr : e.withBotCongr = WithBot.map e := rfl

@[to_dual (attr := simp)]
/--
lemma `withBotCongr_toEquiv` / 引理 `withBotCongr_toEquiv`

English:
lemma withBotCongr_toEquiv
  statement: e.withBotCongr = (e : α ≃ β).withBotCongr
  proof: rfl

@[to_dual (attr := simp)]

中文:
引理 withBotCongr_toEquiv
  结论: e.withBotCongr = (e : α ≃ β).withBotCongr
  证明: rfl

@[to_dual (attr := simp)]
-/
lemma withBotCongr_toEquiv : e.withBotCongr = (e : α ≃ β).withBotCongr := rfl

@[to_dual (attr := simp)]
/--
lemma `withBotCongr_toAddHom` / 引理 `withBotCongr_toAddHom`

English:
lemma withBotCongr_toAddHom
  statement: e.withBotCongr = (e : AddHom α β).withBotMap
  proof: rfl

@[to_dual (attr := simp)]

中文:
引理 withBotCongr_toAddHom
  结论: e.withBotCongr = (e : 加法半群态射 α β).withBotMap
  证明: rfl

@[to_dual (attr := simp)]
-/
lemma withBotCongr_toAddHom : e.withBotCongr = (e : AddHom α β).withBotMap := rfl

@[to_dual (attr := simp)]
/--
lemma `withBotCongr_refl` / 引理 `withBotCongr_refl`

English:
lemma withBotCongr_refl
  statement: (AddEquiv.refl α).withBotCongr = AddEquiv.refl _
  proof: AddEquiv.ext congr_fun WithBot.map_id

@[to_dual (attr := simp)]

中文:
引理 withBotCongr_refl
  结论: (加法等价.refl α).withBotCongr = 加法等价.refl _
  证明: AddEquiv.ext congr_fun WithBot.map_id

@[to_dual (attr := simp)]

Depends on / 依赖: AddEquiv, AddEquiv.ext, WithBot, WithBot.map_id, congr_fun, map_id
-/
lemma withBotCongr_refl : (AddEquiv.refl α).withBotCongr = AddEquiv.refl _ :=
AddEquiv.ext congr_fun WithBot.map_id

@[to_dual (attr := simp)]
/--
theorem `withBotCongr_symm` / 定理 `withBotCongr_symm`

English:
theorem withBotCongr_symm
  statement: e.withBotCongr.symm = e.symm.withBotCongr
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 withBotCongr_symm
  结论: e.withBotCongr.symm = e.symm.withBotCongr
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem withBotCongr_symm : e.withBotCongr.symm = e.symm.withBotCongr := rfl

@[to_dual (attr := simp)]
/--
theorem `withBotCongr_trans` / 定理 `withBotCongr_trans`

English:
theorem withBotCongr_trans
  proof: by
  ext x
  simp

中文:
定理 withBotCongr_trans
  证明: by
  ext x
  simp
-/
theorem withBotCongr_trans :
    (e₁.trans e₂).withBotCongr = e₁.withBotCongr.trans e₂.withBotCongr := by
  ext x
  simp

end AddEquiv
