/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Tactic.ByCases

/-!
# The order relation on the integers
-/

public section

open Nat

namespace Int

variable {a b : Int}

/--
theorem `le.elim` / 定理 `le.elim`

English:
theorem le.elim
  given: (h : a <= b) {P : Prop} (h' : forall n : Nat, a + ↑n = b -> P)
  statement: P
  proof: Exists.elim (le.dest h) h'

alias ⟨le_of_ofNat_le_ofNat, ofNat_le_ofNat_of_le⟩ := ofNat_le

中文:
定理 le.elim
  条件: (h : a <= b) {P : 命题} (h' : 对任意 n : 自然数, a + ↑n = b -> P)
  结论: P
  证明: Exists.elim (le.dest h) h'

alias ⟨le_of_ofNat_le_ofNat, ofNat_le_ofNat_of_le⟩ := ofNat_le

Depends on / 依赖: Exists, Exists.elim, le.dest
-/
theorem le.elim (h : a <= b) {P : Prop} (h' : forall n : Nat, a + ↑n = b -> P) : P :=
  Exists.elim (le.dest h) h'

alias ⟨le_of_ofNat_le_ofNat, ofNat_le_ofNat_of_le⟩ := ofNat_le

/--
theorem `lt.elim` / 定理 `lt.elim`

English:
theorem lt.elim
  given: (h : a < b) {P : Prop} (h' : forall n : Nat, a + ↑(Nat.succ n) = b -> P)
  statement: P
  proof: Exists.elim (lt.dest h) h'

alias ⟨lt_of_ofNat_lt_ofNat, ofNat_lt_ofNat_of_lt⟩ := ofNat_lt

中文:
定理 lt.elim
  条件: (h : a < b) {P : 命题} (h' : 对任意 n : 自然数, a + ↑(自然数.succ n) = b -> P)
  结论: P
  证明: Exists.elim (lt.dest h) h'

alias ⟨lt_of_ofNat_lt_ofNat, ofNat_lt_ofNat_of_lt⟩ := ofNat_lt

Depends on / 依赖: Exists, Exists.elim, lt.dest
-/
theorem lt.elim (h : a < b) {P : Prop} (h' : forall n : Nat, a + ↑(Nat.succ n) = b -> P) : P :=
  Exists.elim (lt.dest h) h'

alias ⟨lt_of_ofNat_lt_ofNat, ofNat_lt_ofNat_of_lt⟩ := ofNat_lt

/--
Instance `instLinearOrder` / 实例 `instLinearOrder`

English:
instance instLinearOrder
  signature: : LinearOrder Int where
  body: Int.le_refl
  le_trans := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  lt_iff_le_not_ge := @Int.lt_iff_le_and_not_ge
  le_total := Int.le_total
  toDecidableEq := instDecidableEq
  toDecidableLE := decLe
  toDecidableLT := decLt

protected alias ⟨eq_zero_or_eq_zero_of_mul_eq_zero, _⟩ := Int.mul

中文:
实例 instLinearOrder
  签名: : 线性序 整数 where
  定义体: Int.le_refl
  le_trans := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  lt_iff_le_not_ge := @Int.lt_iff_le_and_not_ge
  le_total := Int.le_total
  toDecidableEq := instDecidableEq
  toDecidableLE := decLe
  toDecidableLT := decLt

protected alias ⟨eq_zero_or_eq_zero_of_mul_eq_zero, _⟩ := Int.mul

Depends on / 依赖: Int.le_refl, le_refl
-/
instance instLinearOrder : LinearOrder Int where
  le_refl := Int.le_refl
  le_trans := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  lt_iff_le_not_ge := @Int.lt_iff_le_and_not_ge
  le_total := Int.le_total
  toDecidableEq := instDecidableEq
  toDecidableLE := decLe
  toDecidableLT := decLt

protected alias ⟨eq_zero_or_eq_zero_of_mul_eq_zero, _⟩ := Int.mul_eq_zero

/--
theorem `nonneg_or_nonpos_of_mul_nonneg` / 定理 `nonneg_or_nonpos_of_mul_nonneg`

English:
theorem nonneg_or_nonpos_of_mul_nonneg
  statement: 0 <= a * b -> 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
  proof: by
  grind [Int.mul_comm, Int.mul_nonneg_iff_of_pos_right]

中文:
定理 nonneg_or_nonpos_of_mul_nonneg
  结论: 0 <= a * b -> 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
  证明: by
  grind [Int.mul_comm, Int.mul_nonneg_iff_of_pos_right]

Depends on / 依赖: Int.mul_comm, Int.mul_nonneg_iff_of_pos_right, mul_comm, mul_nonneg_iff_of_pos_right
-/
theorem nonneg_or_nonpos_of_mul_nonneg : 0 <= a * b -> 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0 := by
  grind [Int.mul_comm, Int.mul_nonneg_iff_of_pos_right]

/--
theorem `mul_nonneg_of_nonneg_or_nonpos` / 定理 `mul_nonneg_of_nonneg_or_nonpos`

English:
theorem mul_nonneg_of_nonneg_or_nonpos
  statement: 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0 -> 0 <= a * b

中文:
定理 mul_nonneg_of_nonneg_or_nonpos
  结论: 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0 -> 0 <= a * b

Depends on / 依赖: mul_nonneg_of_nonneg_or_nonpos, nonneg_or_nonpos_of_mul_nonneg
-/
theorem mul_nonneg_of_nonneg_or_nonpos : 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0 -> 0 <= a * b
  | .inl ⟨ha, hb⟩ => Int.mul_nonneg ha hb
  | .inr ⟨ha, hb⟩ => Int.mul_nonneg_of_nonpos_of_nonpos ha hb

/--
theorem `mul_nonneg_iff` / 定理 `mul_nonneg_iff`

English:
theorem mul_nonneg_iff
  statement: 0 <= a * b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
  proof: ⟨nonneg_or_nonpos_of_mul_nonneg, mul_nonneg_of_nonneg_or_nonpos⟩

中文:
定理 mul_nonneg_iff
  结论: 0 <= a * b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
  证明: ⟨nonneg_or_nonpos_of_mul_nonneg, mul_nonneg_of_nonneg_or_nonpos⟩
-/
protected theorem mul_nonneg_iff : 0 <= a * b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0 :=
  ⟨nonneg_or_nonpos_of_mul_nonneg, mul_nonneg_of_nonneg_or_nonpos⟩

/--
theorem `mul_pos_iff` / 定理 `mul_pos_iff`

English:
theorem mul_pos_iff
  statement: 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0
  proof: by
  rw [Int.lt_iff_le_and_ne]; rw [Int.mul_nonneg_iff]; rw [ne_comm]; rw [Int.mul_ne_zero_iff]
  lia

中文:
定理 mul_pos_iff
  结论: 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0
  证明: by
  rw [Int.lt_iff_le_and_ne]; rw [Int.mul_nonneg_iff]; rw [ne_comm]; rw [Int.mul_ne_zero_iff]
  lia
-/
protected theorem mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rw [Int.lt_iff_le_and_ne]; rw [Int.mul_nonneg_iff]; rw [ne_comm]; rw [Int.mul_ne_zero_iff]
  lia

/--
theorem `mul_nonpos_iff` / 定理 `mul_nonpos_iff`

English:
theorem mul_nonpos_iff
  statement: a * b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b
  proof: by
  rw [← not_iff_not]; rw [not_le]; rw [Int.mul_pos_iff]
  lia

中文:
定理 mul_nonpos_iff
  结论: a * b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b
  证明: by
  rw [← not_iff_not]; rw [not_le]; rw [Int.mul_pos_iff]
  lia
-/
protected theorem mul_nonpos_iff : a * b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b := by
  rw [← not_iff_not]; rw [not_le]; rw [Int.mul_pos_iff]
  lia

/--
theorem `mul_neg_iff` / 定理 `mul_neg_iff`

English:
theorem mul_neg_iff
  statement: a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b
  proof: by
  rw [← not_iff_not]; rw [not_lt]; rw [Int.mul_nonneg_iff]
  lia

中文:
定理 mul_neg_iff
  结论: a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b
  证明: by
  rw [← not_iff_not]; rw [not_lt]; rw [Int.mul_nonneg_iff]
  lia
-/
protected theorem mul_neg_iff : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  rw [← not_iff_not]; rw [not_lt]; rw [Int.mul_nonneg_iff]
  lia

end Int
