/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
module

public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Order.Interval.Set.Defs

/-!
# Lemmas on `Nat.floor` and `Nat.ceil` for semirings

This file contains basic results on the natural-valued floor and ceiling functions.

## TODO

`LinearOrder` can be relaxed to `PartialOrder` in many lemmas.

## Tags

rounding, floor, ceil
-/

public section

assert_not_exists Finset

open Set

variable {R K : Type*}

namespace Nat

section LinearOrderedSemiring

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

section floor

/-
**Nat.floor_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_lt (ha : 0 <= a) : ⌊a⌋₊ < n ↔ a < n
参数：ha : 0 <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Nat.le_floor_iff`：le_floor_iff (ha : 0 <= a) : n <= ⌊a⌋₊ ↔ (n : α) <= a
-/
theorem floor_lt (ha : 0 ≤ a) : ⌊a⌋₊ < n ↔ a < n :=
  lt_iff_lt_of_le_iff_le <| le_floor_iff ha
/-
**Nat.floor_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_lt_one (ha : 0 <= a) : ⌊a⌋₊ < 1 ↔ a < 1
参数：ha : 0 <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.floor_lt`：floor_lt (ha : 0 <= a) : ⌊a⌋₊ < n ↔ a < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem floor_lt_one (ha : 0 ≤ a) : ⌊a⌋₊ < 1 ↔ a < 1 :=
  (floor_lt ha).trans <| by rw [Nat.cast_one]
/-
**Nat.floor_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_le (ha : 0 <= a) : (⌊a⌋₊ : R) <= a
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_floor_iff`：le_floor_iff (ha : 0 <= a) : n <= ⌊a⌋₊ ↔ (n : α) <= a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem floor_le (ha : 0 ≤ a) : (⌊a⌋₊ : R) ≤ a :=
  (le_floor_iff ha).1 le_rfl
/-
**Nat.floor_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_eq_iff (ha : 0 <= a) : ⌊a⌋₊ = n ↔ ↑n <= a ∧ a < ↑n + 1
参数：ha : 0 <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_floor_iff`：le_floor_iff (ha : 0 <= a) : n <= ⌊a⌋₊ ↔ (n : α) <= a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.floor_lt`：floor_lt (ha : 0 <= a) : ⌊a⌋₊ < n ↔ a < n
· 使用定理 `Nat.lt_add_one_iff`：∀ {m n : ℕ}, m < n + 1 ↔ m ≤ n
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem floor_eq_iff (ha : 0 ≤ a) : ⌊a⌋₊ = n ↔ ↑n ≤ a ∧ a < ↑n + 1 := by
  rw [← le_floor_iff ha, ← Nat.cast_one, ← Nat.cast_add, ← floor_lt ha, Nat.lt_add_one_iff,
    le_antisymm_iff, and_comm]
/-
**Nat.lt_of_floor_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_of_floor_lt (h : ⌊a⌋₊ < n) : a < n
参数：h : ⌊a⌋₊ < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.le_floor`：le_floor (h : (n : α) <= a) : n <= ⌊a⌋₊
-/
theorem lt_of_floor_lt (h : ⌊a⌋₊ < n) : a < n :=
  lt_of_not_ge fun h' => (le_floor h').not_gt h
/-
**Nat.lt_one_of_floor_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_one_of_floor_lt_one (h : ⌊a⌋₊ < 1) : a < 1
参数：h : ⌊a⌋₊ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_of_floor_lt`：lt_of_floor_lt (h : ⌊a⌋₊ < n) : a < n
-/
theorem lt_one_of_floor_lt_one (h : ⌊a⌋₊ < 1) : a < 1 := mod_cast lt_of_floor_lt h
/-
**Nat.lt_succ_floor** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_succ_floor (a : R) : a < ⌊a⌋₊.succ
参数：a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_of_floor_lt`：lt_of_floor_lt (h : ⌊a⌋₊ < n) : a < n
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem lt_succ_floor (a : R) : a < ⌊a⌋₊.succ :=
  lt_of_floor_lt <| Nat.lt_succ_self _

@[bound]
/-
**Nat.lt_floor_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_floor_add_one (a : R) : a < ⌊a⌋₊ + 1
参数：a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.lt_succ_floor`：lt_succ_floor (a : R) : a < ⌊a⌋₊.succ
-/
theorem lt_floor_add_one (a : R) : a < ⌊a⌋₊ + 1 := by simpa using lt_succ_floor a

variable [IsStrictOrderedRing R]

@[simp]
/-
**Nat.floor_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_natCast (n : Nat) : ⌊(n : R)⌋₊ = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_floor_iff`：le_floor_iff (ha : 0 <= a) : n <= ⌊a⌋₊ ↔ (n : α) <= a
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem floor_natCast (n : ℕ) : ⌊(n : R)⌋₊ = n :=
  eq_of_forall_le_iff fun a => by
    rw [le_floor_iff, Nat.cast_le]
    exact n.cast_nonneg

@[simp]
/-
**Nat.floor_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_zero : ⌊(0 : R)⌋₊ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.floor_natCast`：floor_natCast (n : Nat) : ⌊(n : R)⌋₊ = n
-/
theorem floor_zero : ⌊(0 : R)⌋₊ = 0 := by rw [← Nat.cast_zero, floor_natCast]

@[simp]
/-
**Nat.floor_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_one : ⌊(1 : R)⌋₊ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.floor_natCast`：floor_natCast (n : Nat) : ⌊(n : R)⌋₊ = n
-/
theorem floor_one : ⌊(1 : R)⌋₊ = 1 := by rw [← Nat.cast_one, floor_natCast]

@[simp]
/-
**Nat.floor_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_ofNat (n : Nat) [n.AtLeastTwo] : ⌊(ofNat(n) : R)⌋₊ = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.floor_natCast`：floor_natCast (n : Nat) : ⌊(n : R)⌋₊ = n
-/
theorem floor_ofNat (n : ℕ) [n.AtLeastTwo] : ⌊(ofNat(n) : R)⌋₊ = ofNat(n) :=
  Nat.floor_natCast _
/-
**Nat.floor_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_of_nonpos (ha : a <= 0) : ⌊a⌋₊ = 0
参数：ha : a <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `FloorSemiring.floor_of_neg`：∀ {α : Type u_4} {inst : Semiring α} {inst_1
 : PartialOrder α} [self : FloorSemiring α] {a : α},   a < 0 → FloorSemiring.flo
or a = 0
· 使用定理 `Nat.floor_zero`：floor_zero : ⌊(0 : R)⌋₊ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem floor_of_nonpos (ha : a ≤ 0) : ⌊a⌋₊ = 0 :=
  ha.lt_or_eq.elim FloorSemiring.floor_of_neg <| by
    rintro rfl
    exact floor_zero

@[gcongr]
/-
**Nat.floor_mono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_mono : Monotone (floor : R -> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.floor_of_nonpos`：floor_of_nonpos (ha : a <= 0) : ⌊a⌋₊ = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.le_floor`：le_floor (h : (n : α) <= a) : n <= ⌊a⌋₊
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.floor_le`：floor_le (ha : 0 <= a) : (⌊a⌋₊ : R) <= a
-/
theorem floor_mono : Monotone (floor : R → ℕ) := fun a b h => by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact Nat.zero_le _
  · exact le_floor ((floor_le ha).trans h)
/-
**Nat.floor_le_floor** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : LinearOrder R] [inst_2 : Fl
oorSemiring R] {a b : R}   [IsStrictOrderedRing R], a ≤ b → ⌊a⌋₊ ≤ ⌊b⌋₊
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.floor_mono`：floor_mono : Monotone (floor : R -> Nat)
-/
@[bound] lemma floor_le_floor (hab : a ≤ b) : ⌊a⌋₊ ≤ ⌊b⌋₊ := floor_mono hab
/-
**Nat.le_floor_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_floor_iff' (hn : n != 0) : n <= ⌊a⌋₊ ↔ (n : R) <= a
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.floor_of_nonpos`：floor_of_nonpos (ha : a <= 0) : ⌊a⌋₊ = 0
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.le_floor_iff`：le_floor_iff (ha : 0 <= a) : n <= ⌊a⌋₊ ↔ (n : α) <= a
-/
theorem le_floor_iff' (hn : n ≠ 0) : n ≤ ⌊a⌋₊ ↔ (n : R) ≤ a := by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact
      iff_of_false (Nat.pos_of_ne_zero hn).not_ge
        (not_le_of_gt <| ha.trans_lt <| cast_pos.2 <| Nat.pos_of_ne_zero hn)
  · exact le_floor_iff ha

@[simp]
/-
**Nat.one_le_floor_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：one_le_floor_iff (x : R) : 1 <= ⌊x⌋₊ ↔ 1 <= x
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_floor_iff'`：le_floor_iff' (hn : n != 0) : n <= ⌊a⌋₊ ↔ (n : R) <= 
a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem one_le_floor_iff (x : R) : 1 ≤ ⌊x⌋₊ ↔ 1 ≤ x :=
  mod_cast le_floor_iff' one_ne_zero
/-
**Nat.floor_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_lt' (hn : n != 0) : ⌊a⌋₊ < n ↔ a < n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Nat.le_floor_iff'`：le_floor_iff' (hn : n != 0) : n <= ⌊a⌋₊ ↔ (n : R) <= 
a
-/
theorem floor_lt' (hn : n ≠ 0) : ⌊a⌋₊ < n ↔ a < n :=
  lt_iff_lt_of_le_iff_le <| le_floor_iff' hn
/-
**Nat.floor_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_pos : 0 < ⌊a⌋₊ ↔ 1 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_iff_add_one_le`：∀ {m n : ℕ}, m < n ↔ m + 1 ≤ n
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.le_floor_iff'`：le_floor_iff' (hn : n != 0) : n <= ⌊a⌋₊ ↔ (n : R) <= 
a
· 使用定理 `Nat.one_ne_zero`：1 ≠ 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem floor_pos : 0 < ⌊a⌋₊ ↔ 1 ≤ a := by
  rw [Nat.lt_iff_add_one_le, zero_add, le_floor_iff' Nat.one_ne_zero, cast_one]
/-
**Nat.pos_of_floor_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pos_of_floor_pos (h : 0 < ⌊a⌋₊) : 0 < a
参数：h : 0 < ⌊a⌋₊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.floor_of_nonpos`：floor_of_nonpos (ha : a <= 0) : ⌊a⌋₊ = 0
-/
theorem pos_of_floor_pos (h : 0 < ⌊a⌋₊) : 0 < a :=
  (le_or_gt a 0).resolve_left fun ha => lt_irrefl 0 <| by rwa [floor_of_nonpos ha] at h
/-
**Nat.lt_of_lt_floor** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_of_lt_floor (h : n < ⌊a⌋₊) : ↑n < a
参数：h : n < ⌊a⌋₊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.floor_le`：floor_le (ha : 0 <= a) : (⌊a⌋₊ : R) <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.pos_of_floor_pos`：pos_of_floor_pos (h : 0 < ⌊a⌋₊) : 0 < a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem lt_of_lt_floor (h : n < ⌊a⌋₊) : ↑n < a :=
  (Nat.cast_lt.2 h).trans_le <| floor_le (pos_of_floor_pos <| (Nat.zero_le n).trans_lt h).le
/-
**Nat.floor_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_le_of_le (h : a <= n) : ⌊a⌋₊ <= n
参数：h : a <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_imp_le_iff_lt_imp_lt`：le_imp_le_iff_lt_imp_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : a <= b -> c <= d ↔ d < c -> b < a
· 使用定理 `Nat.lt_of_lt_floor`：lt_of_lt_floor (h : n < ⌊a⌋₊) : ↑n < a
-/
theorem floor_le_of_le (h : a ≤ n) : ⌊a⌋₊ ≤ n :=
  le_imp_le_iff_lt_imp_lt.2 lt_of_lt_floor h
/-
**Nat.floor_le_one_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_le_one_of_le_one (h : a <= 1) : ⌊a⌋₊ <= 1
参数：h : a <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.floor_le_of_le`：floor_le_of_le (h : a <= n) : ⌊a⌋₊ <= n
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem floor_le_one_of_le_one (h : a ≤ 1) : ⌊a⌋₊ ≤ 1 :=
  floor_le_of_le <| h.trans_eq <| Nat.cast_one.symm

@[simp]
/-
**Nat.floor_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_eq_zero : ⌊a⌋₊ = 0 ↔ a < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.floor_lt'`：floor_lt' (hn : n != 0) : ⌊a⌋₊ < n ↔ a < n
· 使用定理 `Nat.one_ne_zero`：1 ≠ 0
-/
theorem floor_eq_zero : ⌊a⌋₊ = 0 ↔ a < 1 := by
  rw [← lt_one_iff, ← @cast_one R]
  exact floor_lt' Nat.one_ne_zero
/-
**Nat.floor_eq_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_eq_iff' (hn : n != 0) : ⌊a⌋₊ = n ↔ ↑n <= a ∧ a < ↑n + 1
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_floor_iff'`：le_floor_iff' (hn : n != 0) : n <= ⌊a⌋₊ ↔ (n : R) <= 
a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.floor_lt'`：floor_lt' (hn : n != 0) : ⌊a⌋₊ < n ↔ a < n
· 使用定理 `Nat.add_one_ne_zero`：∀ (n : ℕ), n + 1 ≠ 0
· 使用定理 `Nat.lt_add_one_iff`：∀ {m n : ℕ}, m < n + 1 ↔ m ≤ n
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem floor_eq_iff' (hn : n ≠ 0) : ⌊a⌋₊ = n ↔ ↑n ≤ a ∧ a < ↑n + 1 := by
  rw [← le_floor_iff' hn, ← Nat.cast_one, ← Nat.cast_add, ← floor_lt' (Nat.add_one_ne_zero n),
    Nat.lt_add_one_iff, le_antisymm_iff, and_comm]
/-
**Nat.floor_eq_on_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_eq_on_Ico (n : Nat) : forall a in (Set.Ico n (n + 1) : Set R), ⌊a⌋₊ 
= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.floor_eq_iff`：floor_eq_iff (ha : 0 <= a) : ⌊a⌋₊ = n ↔ ↑n <= a ∧ a < 
↑n + 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem floor_eq_on_Ico (n : ℕ) : ∀ a ∈ (Set.Ico n (n + 1) : Set R), ⌊a⌋₊ = n := fun _ ⟨h₀, h₁⟩ =>
  (floor_eq_iff <| n.cast_nonneg.trans h₀).mpr ⟨h₀, h₁⟩
/-
**Nat.floor_eq_on_Ico'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_eq_on_Ico' (n : Nat) : forall a in (Set.Ico n (n + 1) : Set R), (⌊a⌋
₊ : R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.floor_eq_on_Ico`：floor_eq_on_Ico (n : Nat) : forall a in (Set.Ico n 
(n + 1) : Set R), ⌊a⌋₊ = n
-/
theorem floor_eq_on_Ico' (n : ℕ) :
    ∀ a ∈ (Set.Ico n (n + 1) : Set R), (⌊a⌋₊ : R) = n :=
  fun x hx => mod_cast floor_eq_on_Ico n x hx

@[simp]
/-
**Nat.preimage_floor_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：preimage_floor_zero : (floor : R -> Nat) ⁻¹' {0} = Iio 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.floor_eq_zero`：floor_eq_zero : ⌊a⌋₊ = 0 ↔ a < 1
-/
theorem preimage_floor_zero : (floor : R → ℕ) ⁻¹' {0} = Iio 1 :=
  ext fun _ => floor_eq_zero
/-
**Nat.preimage_floor_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：preimage_floor_of_ne_zero {n : Nat} (hn : n != 0) : (floor : R -> Nat) ⁻¹'
 {n} = Ico (n : R) (n + 1)
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.floor_eq_iff'`：floor_eq_iff' (hn : n != 0) : ⌊a⌋₊ = n ↔ ↑n <= a ∧ a 
< ↑n + 1
-/
theorem preimage_floor_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (floor : R → ℕ) ⁻¹' {n} = Ico (n : R) (n + 1) :=
  ext fun _ => floor_eq_iff' hn
/-
**Nat.mul_cast_floor_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mul_cast_floor_div_cancel {n : Nat} (hn : n != 0) (a : R) : ⌊a * n⌋₊ / n =
 ⌊a⌋₊
参数：hn : n != 0；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.floor_of_nonpos`：floor_of_nonpos (ha : a <= 0) : ⌊a⌋₊ = 0
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `Nat.le_div_iff_mul_le`：∀ {k x y : ℕ}, 0 < k → (x ≤ y / k ↔ x * k ≤ y)
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用定理 `Nat.le_floor_iff`：le_floor_iff (ha : 0 <= a) : n <= ⌊a⌋₊ ↔ (n : α) <= a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_le_mul_iff_of_pos_right`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Z
ero α] [inst_2 : Preorder α] {a b c : α} [MulPosMono α] [MulPosReflectLE α],   0
 < a → (b * a ≤ c…
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_cast_floor_div_cancel {n : ℕ} (hn : n ≠ 0) (a : R) : ⌊a * n⌋₊ / n = ⌊a⌋₊ := by
  rcases le_total a 0 with ha | ha
  · rw [floor_of_nonpos, floor_of_nonpos ha]
    · simp
    apply mul_nonpos_of_nonpos_of_nonneg ha n.cast_nonneg
  refine eq_of_forall_le_iff fun m ↦ ?_
  rw [le_div_iff_mul_le (zero_lt_of_ne_zero hn), le_floor_iff (mul_nonneg ha (cast_nonneg' n)),
    le_floor_iff ha, cast_mul, mul_le_mul_iff_of_pos_right (cast_pos'.mpr (zero_lt_of_ne_zero hn))]
/-
**Nat.cast_mul_floor_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_mul_floor_div_cancel {n : Nat} (hn : n != 0) (a : R) : ⌊n * a⌋₊ / n =
 ⌊a⌋₊
参数：hn : n != 0；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_comm`：cast_comm (n : Nat) (x : α) : (n : α) * x = x * n
· 使用定理 `Nat.mul_cast_floor_div_cancel`：mul_cast_floor_div_cancel {n : Nat} (hn :
 n != 0) (a : R) : ⌊a * n⌋₊ / n = ⌊a⌋₊
-/
theorem cast_mul_floor_div_cancel {n : ℕ} (hn : n ≠ 0) (a : R) :
    ⌊n * a⌋₊ / n = ⌊a⌋₊ := by
  rw [Nat.cast_comm, mul_cast_floor_div_cancel hn]

end floor

/-! #### Ceil -/

section ceil

/-
**Nat.add_one_le_ceil_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_one_le_ceil_iff : n + 1 <= ⌈a⌉₊ ↔ (n : R) < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_ceil`：lt_ceil : n < ⌈a⌉₊ ↔ (n : α) < a
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem add_one_le_ceil_iff : n + 1 ≤ ⌈a⌉₊ ↔ (n : R) < a := by
  rw [← Nat.lt_ceil, Nat.add_one_le_iff]

@[simp]
/-
**Nat.one_le_ceil_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：one_le_ceil_iff : 1 <= ⌈a⌉₊ ↔ 0 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.add_one_le_ceil_iff`：add_one_le_ceil_iff : n + 1 <= ⌈a⌉₊ ↔ (n : R) <
 a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_le_ceil_iff : 1 ≤ ⌈a⌉₊ ↔ 0 < a := by
  rw [← zero_add 1, Nat.add_one_le_ceil_iff, Nat.cast_zero]

@[bound]
/-
**Nat.le_ceil** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_ceil (a : R) : a <= ⌈a⌉₊
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.ceil_le`：ceil_le : ⌈a⌉₊ <= n ↔ a <= n
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_ceil (a : R) : a ≤ ⌈a⌉₊ :=
  ceil_le.1 le_rfl
/-
**Nat.ceil_mono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ceil_mono : Monotone (ceil : R -> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `Nat.gc_ceil_coe`：gc_ceil_coe : GaloisConnection (ceil : α -> Nat) (↑)
-/
theorem ceil_mono : Monotone (ceil : R → ℕ) :=
  gc_ceil_coe.monotone_l
/-
**Nat.ceil_le_ceil** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : LinearOrder R] [inst_2 : Fl
oorSemiring R] {a b : R}, a ≤ b → ⌈a⌉₊ ≤ ⌈b⌉₊
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ceil_mono`：ceil_mono : Monotone (ceil : R -> Nat)
-/
@[gcongr, bound] lemma ceil_le_ceil (hab : a ≤ b) : ⌈a⌉₊ ≤ ⌈b⌉₊ := ceil_mono hab

@[simp]
/-
**Nat.ceil_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ceil_eq_zero : ⌈a⌉₊ = 0 ↔ a <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `Nat.ceil_le`：ceil_le : ⌈a⌉₊ <= n ↔ a <= n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ceil_eq_zero : ⌈a⌉₊ = 0 ↔ a ≤ 0 := by rw [← Nat.le_zero, ceil_le, Nat.cast_zero]
/-
**Nat.ceil_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ceil_eq_iff (hn : n != 0) : ⌈a⌉₊ = n ↔ ↑(n - 1) < a ∧ a <= n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ceil_le`：ceil_le : ⌈a⌉₊ <= n ↔ a <= n
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `tsub_lt_iff_right`：tsub_lt_iff_right (hbc : b <= a) : a - b < c ↔ a < c 
+ b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.lt_add_one_iff`：∀ {m n : ℕ}, m < n + 1 ↔ m ≤ n
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ceil_eq_iff (hn : n ≠ 0) : ⌈a⌉₊ = n ↔ ↑(n - 1) < a ∧ a ≤ n := by
  rw [← ceil_le, ← not_le, ← ceil_le, not_le,
    tsub_lt_iff_right (Nat.add_one_le_iff.2 (pos_iff_ne_zero.2 hn)), Nat.lt_add_one_iff,
    le_antisymm_iff, and_comm]

@[simp]
/-
**Nat.preimage_ceil_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：preimage_ceil_zero : (Nat.ceil : R -> Nat) ⁻¹' {0} = Iic 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.ceil_eq_zero`：ceil_eq_zero : ⌈a⌉₊ = 0 ↔ a <= 0
-/
theorem preimage_ceil_zero : (Nat.ceil : R → ℕ) ⁻¹' {0} = Iic 0 :=
  ext fun _ => ceil_eq_zero
/-
**Nat.preimage_ceil_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：preimage_ceil_of_ne_zero (hn : n != 0) : (Nat.ceil : R -> Nat) ⁻¹' {n} = I
oc (↑(n - 1) : R) n
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.ceil_eq_iff`：ceil_eq_iff (hn : n != 0) : ⌈a⌉₊ = n ↔ ↑(n - 1) < a ∧ a
 <= n
-/
theorem preimage_ceil_of_ne_zero (hn : n ≠ 0) : (Nat.ceil : R → ℕ) ⁻¹' {n} = Ioc (↑(n - 1) : R) n :=
  ext fun _ => ceil_eq_iff hn

@[bound]
/-
**Nat.ceil_le_floor_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ceil_le_floor_add_one (a : R) : ⌈a⌉₊ <= ⌊a⌋₊ + 1
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ceil_le`：ceil_le : ⌈a⌉₊ <= n ↔ a <= n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.lt_floor_add_one`：lt_floor_add_one (a : R) : a < ⌊a⌋₊ + 1
-/
theorem ceil_le_floor_add_one (a : R) : ⌈a⌉₊ ≤ ⌊a⌋₊ + 1 := by
  rw [ceil_le, Nat.cast_add, Nat.cast_one]
  exact (lt_floor_add_one a).le

@[simp]
/-
**Nat.ceil_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ceil_intCast {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [Floor
Semiring R] (z : Int) : ⌈(z : R)⌉₊ = z.toNat
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ceil_intCast {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
    [FloorSemiring R] (z : ℤ) :
    ⌈(z : R)⌉₊ = z.toNat :=
  eq_of_forall_ge_iff fun a => by
    simp only [ceil_le, Int.toNat_le]
    norm_cast

variable [IsStrictOrderedRing R]

@[simp]
/-
**Nat.ceil_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ceil_natCast (n : Nat) : ⌈(n : R)⌉₊ = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ceil_le`：ceil_le : ⌈a⌉₊ <= n ↔ a <= n
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ceil_natCast (n : ℕ) : ⌈(n : R)⌉₊ = n :=
  eq_of_forall_ge_iff fun a => by rw [ceil_le, cast_le]

@[simp]
/-
**Nat.ceil_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ceil_zero : ⌈(0 : R)⌉₊ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.ceil_natCast`：ceil_natCast (n : Nat) : ⌈(n : R)⌉₊ = n
-/
theorem ceil_zero : ⌈(0 : R)⌉₊ = 0 := by rw [← Nat.cast_zero, ceil_natCast]

@[simp]
/-
**Nat.ceil_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ceil_one : ⌈(1 : R)⌉₊ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.ceil_natCast`：ceil_natCast (n : Nat) : ⌈(n : R)⌉₊ = n
-/
theorem ceil_one : ⌈(1 : R)⌉₊ = 1 := by rw [← Nat.cast_one, ceil_natCast]

@[simp]
/-
**Nat.ceil_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ceil_ofNat (n : Nat) [n.AtLeastTwo] : ⌈(ofNat(n) : R)⌉₊ = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ceil_natCast`：ceil_natCast (n : Nat) : ⌈(n : R)⌉₊ = n
-/
theorem ceil_ofNat (n : ℕ) [n.AtLeastTwo] : ⌈(ofNat(n) : R)⌉₊ = ofNat(n) := ceil_natCast n
/-
**Nat.lt_of_ceil_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_of_ceil_lt (h : ⌈a⌉₊ < n) : a < n
参数：h : ⌈a⌉₊ < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem lt_of_ceil_lt (h : ⌈a⌉₊ < n) : a < n :=
  (le_ceil a).trans_lt (Nat.cast_lt.2 h)
/-
**Nat.le_of_ceil_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_of_ceil_le (h : ⌈a⌉₊ <= n) : a <= n
参数：h : ⌈a⌉₊ <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem le_of_ceil_le (h : ⌈a⌉₊ ≤ n) : a ≤ n :=
  (le_ceil a).trans (Nat.cast_le.2 h)

@[bound]
/-
**Nat.floor_le_ceil** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_le_ceil (a : R) : ⌊a⌋₊ <= ⌈a⌉₊
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.floor_of_nonpos`：floor_of_nonpos (ha : a <= 0) : ⌊a⌋₊ = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.floor_le`：floor_le (ha : 0 <= a) : (⌊a⌋₊ : R) <= a
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
-/
theorem floor_le_ceil (a : R) : ⌊a⌋₊ ≤ ⌈a⌉₊ := by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact Nat.zero_le _
  · exact cast_le.1 ((floor_le ha).trans <| le_ceil _)
/-
**Nat.floor_lt_ceil_of_lt_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_lt_ceil_of_lt_of_pos {a b : R} (h : a < b) (h' : 0 < b) : ⌊a⌋₊ < ⌈b⌉
₊
参数：h : a < b；h' : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.floor_lt`：floor_lt (ha : 0 <= a) : ⌊a⌋₊ < n ↔ a < n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
· 使用定理 `Nat.floor_of_nonpos`：floor_of_nonpos (ha : a <= 0) : ⌊a⌋₊ = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.lt_ceil`：lt_ceil : n < ⌈a⌉₊ ↔ (n : α) < a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem floor_lt_ceil_of_lt_of_pos {a b : R} (h : a < b) (h' : 0 < b) : ⌊a⌋₊ < ⌈b⌉₊ := by
  rcases le_or_gt 0 a with (ha | ha)
  · rw [floor_lt ha]
    exact h.trans_le (le_ceil _)
  · rwa [floor_of_nonpos ha.le, lt_ceil, Nat.cast_zero]

end ceil

/-! #### Intervals -/

@[simp]
/-
**Nat.preimage_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：preimage_Ioo {a b : R} (ha : 0 <= a) : (Nat.cast : Nat -> R) ⁻¹' Set.Ioo a
 b = Set.Ioo ⌊a⌋₊ ⌈b⌉₊
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
#### Intervals
-/
theorem preimage_Ioo {a b : R} (ha : 0 ≤ a) :
    (Nat.cast : ℕ → R) ⁻¹' Set.Ioo a b = Set.Ioo ⌊a⌋₊ ⌈b⌉₊ := by
  ext
  simp [floor_lt, lt_ceil, ha]

@[simp]
/-
**Nat.preimage_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：preimage_Ico {a b : R} : (Nat.cast : Nat -> R) ⁻¹' Set.Ico a b = Set.Ico ⌈
a⌉₊ ⌈b⌉₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_Ico {a b : R} : (Nat.cast : ℕ → R) ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉₊ ⌈b⌉₊ := by
  ext
  simp [ceil_le, lt_ceil]

@[simp]
/-
**Nat.preimage_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：preimage_Ioc {a b : R} (ha : 0 <= a) (hb : 0 <= b) : (Nat.cast : Nat -> R)
 ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋₊ ⌊b⌋₊
参数：ha : 0 <= a；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_Ioc {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Nat.cast : ℕ → R) ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
  ext
  simp [floor_lt, le_floor_iff, hb, ha]

@[simp]
/-
**Nat.preimage_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：preimage_Icc {a b : R} (hb : 0 <= b) : (Nat.cast : Nat -> R) ⁻¹' Set.Icc a
 b = Set.Icc ⌈a⌉₊ ⌊b⌋₊
参数：hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_Icc {a b : R} (hb : 0 ≤ b) :
    (Nat.cast : ℕ → R) ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉₊ ⌊b⌋₊ := by
  ext
  simp [ceil_le, hb, le_floor_iff]

@[simp]
/-
**Nat.preimage_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：preimage_Ioi {a : R} (ha : 0 <= a) : (Nat.cast : Nat -> R) ⁻¹' Set.Ioi a =
 Set.Ioi ⌊a⌋₊
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_Ioi {a : R} (ha : 0 ≤ a) : (Nat.cast : ℕ → R) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋₊ := by
  ext
  simp [floor_lt, ha]

@[simp]
/-
**Nat.preimage_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：preimage_Ici {a : R} : (Nat.cast : Nat -> R) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_Ici {a : R} : (Nat.cast : ℕ → R) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉₊ := by
  ext
  simp [ceil_le]

@[simp]
/-
**Nat.preimage_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：preimage_Iio {a : R} : (Nat.cast : Nat -> R) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_Iio {a : R} : (Nat.cast : ℕ → R) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉₊ := by
  ext
  simp [lt_ceil]

@[simp]
/-
**Nat.preimage_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：preimage_Iic {a : R} (ha : 0 <= a) : (Nat.cast : Nat -> R) ⁻¹' Set.Iic a =
 Set.Iic ⌊a⌋₊
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_Iic {a : R} (ha : 0 ≤ a) : (Nat.cast : ℕ → R) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋₊ := by
  ext
  simp [le_floor_iff, ha]

@[push]
/-
**Nat.floor_add_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_add_natCast [IsStrictOrderedRing R] (ha : 0 <= a) (n : Nat) : ⌊a + n
⌋₊ = ⌊a⌋₊ + n
参数：ha : 0 <= a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_floor_iff`：le_floor_iff (ha : 0 <= a) : n <= ⌊a⌋₊ ↔ (n : α) <= a
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `IsCancelAdd.toIsRightCancelAdd`：∀ {G : Type u} {inst : Add G} [self : Is
CancelAdd G], IsRightCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
-/
theorem floor_add_natCast [IsStrictOrderedRing R] (ha : 0 ≤ a) (n : ℕ) : ⌊a + n⌋₊ = ⌊a⌋₊ + n :=
  eq_of_forall_le_iff fun b => by
    rw [le_floor_iff (add_nonneg ha n.cast_nonneg)]
    obtain hb | hb := le_total n b
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add, add_comm n, add_comm (n : R), add_le_add_iff_right, add_le_add_iff_right,
        le_floor_iff ha]
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add, add_left_comm _ b, add_left_comm _ (b : R)]
      refine iff_of_true ?_ le_self_add
      exact le_add_of_nonneg_right <| ha.trans <| le_add_of_nonneg_right d.cast_nonneg

variable [IsStrictOrderedRing R]

@[push]
/-
**Nat.floor_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_add_one (ha : 0 <= a) : ⌊a + 1⌋₊ = ⌊a⌋₊ + 1
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.floor_add_natCast`：floor_add_natCast [IsStrictOrderedRing R] (ha : 0
 <= a) (n : Nat) : ⌊a + n⌋₊ = ⌊a⌋₊ + n
-/
theorem floor_add_one (ha : 0 ≤ a) : ⌊a + 1⌋₊ = ⌊a⌋₊ + 1 := by
  rw [← cast_one, floor_add_natCast ha 1]

@[push]
/-
**Nat.floor_add_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_add_ofNat (ha : 0 <= a) (n : Nat) [n.AtLeastTwo] : ⌊a + ofNat(n)⌋₊ =
 ⌊a⌋₊ + ofNat(n)
参数：ha : 0 <= a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.floor_add_natCast`：floor_add_natCast [IsStrictOrderedRing R] (ha : 0
 <= a) (n : Nat) : ⌊a + n⌋₊ = ⌊a⌋₊ + n
-/
theorem floor_add_ofNat (ha : 0 ≤ a) (n : ℕ) [n.AtLeastTwo] :
    ⌊a + ofNat(n)⌋₊ = ⌊a⌋₊ + ofNat(n) :=
  floor_add_natCast ha n

@[simp]
/-
**Nat.floor_sub_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_sub_natCast [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) (n : Na
t) : ⌊a - n⌋₊ = ⌊a⌋₊ - n
参数：a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.floor_of_nonpos`：floor_of_nonpos (ha : a <= 0) : ⌊a⌋₊ = 0
· 使用定理 `tsub_nonpos_of_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCom
mMonoid α] [inst_2 : Sub α] [OrderedSub α] {a b : α},   a ≤ b → a - b ≤ 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.floor_le`：floor_le (ha : 0 <= a) : (⌊a⌋₊ : R) <= a
· 使用定理 `eq_tsub_iff_add_eq_of_le`：eq_tsub_iff_add_eq_of_le (h : c <= b) : a = b 
- c ↔ a + c = b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.le_floor`：le_floor (h : (n : α) <= a) : n <= ⌊a⌋₊
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.floor_add_natCast`：floor_add_natCast [IsStrictOrderedRing R] (ha : 0
 <= a) (n : Nat) : ⌊a + n⌋₊ = ⌊a⌋₊ + n
· 使用定理 `le_tsub_of_add_le_left`：le_tsub_of_add_le_left (h : a + b <= c) : b <= c
 - a
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
（共 31 条，此处仅展示前 30 条）
-/
theorem floor_sub_natCast [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) (n : ℕ) :
    ⌊a - n⌋₊ = ⌊a⌋₊ - n := by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha, floor_of_nonpos (tsub_nonpos_of_le (ha.trans n.cast_nonneg)), zero_tsub]
  rcases le_total a n with h | h
  · rw [floor_of_nonpos (tsub_nonpos_of_le h), eq_comm, tsub_eq_zero_iff_le]
    exact Nat.cast_le.1 ((Nat.floor_le ha).trans h)
  · rw [eq_tsub_iff_add_eq_of_le (le_floor h), ← floor_add_natCast _, tsub_add_cancel_of_le h]
    exact le_tsub_of_add_le_left ((add_zero _).trans_le h)

@[simp]
/-
**Nat.floor_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_sub_one [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) : ⌊a - 1⌋₊ 
= ⌊a⌋₊ - 1
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.floor_sub_natCast`：floor_sub_natCast [Sub R] [OrderedSub R] [ExistsA
ddOfLE R] (a : R) (n : Nat) : ⌊a - n⌋₊ = ⌊a⌋₊ - n
-/
theorem floor_sub_one [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) : ⌊a - 1⌋₊ = ⌊a⌋₊ - 1 :=
  mod_cast floor_sub_natCast a 1

@[simp]
/-
**Nat.floor_sub_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_sub_ofNat [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) (n : Nat)
 [n.AtLeastTwo] : ⌊a - ofNat(n)⌋₊ = ⌊a⌋₊ - ofNat(n)
参数：a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.floor_sub_natCast`：floor_sub_natCast [Sub R] [OrderedSub R] [ExistsA
ddOfLE R] (a : R) (n : Nat) : ⌊a - n⌋₊ = ⌊a⌋₊ - n
-/
theorem floor_sub_ofNat [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) (n : ℕ) [n.AtLeastTwo] :
    ⌊a - ofNat(n)⌋₊ = ⌊a⌋₊ - ofNat(n) :=
  floor_sub_natCast a n
/-
**Nat.ceil_add_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ceil_add_natCast (ha : 0 <= a) (n : Nat) : ⌈a + n⌉₊ = ⌈a⌉₊ + n
参数：ha : 0 <= a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_ceil`：lt_ceil : n < ⌈a⌉₊ ↔ (n : α) < a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_lt_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [A
ddRightStrictMono α] [AddRightReflectLT α] (a : α) {b c : α},   b + a < c + a ↔ 
b < c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `lt_add_of_nonneg_of_lt`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : Preorder α] [AddRightMono α] {a b c : α}, 0 ≤ a → b < c → b < a + c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
（共 33 条，此处仅展示前 30 条）
-/
theorem ceil_add_natCast (ha : 0 ≤ a) (n : ℕ) : ⌈a + n⌉₊ = ⌈a⌉₊ + n :=
  eq_of_forall_ge_iff fun b => by
    contrapose!
    rw [lt_ceil]
    obtain hb | hb := le_or_gt n b
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add, add_comm n, add_comm (n : R), add_lt_add_iff_right, add_lt_add_iff_right,
        lt_ceil]
    · exact iff_of_true (lt_add_of_nonneg_of_lt ha <| cast_lt.2 hb) (Nat.lt_add_left _ hb)
/-
**Nat.ceil_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ceil_add_one (ha : 0 <= a) : ⌈a + 1⌉₊ = ⌈a⌉₊ + 1
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.ceil_add_natCast`：ceil_add_natCast (ha : 0 <= a) (n : Nat) : ⌈a + n⌉
₊ = ⌈a⌉₊ + n
-/
theorem ceil_add_one (ha : 0 ≤ a) : ⌈a + 1⌉₊ = ⌈a⌉₊ + 1 := by
  rw [cast_one.symm, ceil_add_natCast ha 1]
/-
**Nat.ceil_add_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ceil_add_ofNat (ha : 0 <= a) (n : Nat) [n.AtLeastTwo] : ⌈a + ofNat(n)⌉₊ = 
⌈a⌉₊ + ofNat(n)
参数：ha : 0 <= a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ceil_add_natCast`：ceil_add_natCast (ha : 0 <= a) (n : Nat) : ⌈a + n⌉
₊ = ⌈a⌉₊ + n
-/
theorem ceil_add_ofNat (ha : 0 ≤ a) (n : ℕ) [n.AtLeastTwo] :
    ⌈a + ofNat(n)⌉₊ = ⌈a⌉₊ + ofNat(n) :=
  ceil_add_natCast ha n

@[bound]
/-
**Nat.ceil_lt_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ceil_lt_add_one (ha : 0 <= a) : (⌈a⌉₊ : R) < a + 1
参数：ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_ceil`：lt_ceil : n < ⌈a⌉₊ ↔ (n : α) < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Nat.ceil_add_one`：ceil_add_one (ha : 0 <= a) : ⌈a + 1⌉₊ = ⌈a⌉₊ + 1
-/
theorem ceil_lt_add_one (ha : 0 ≤ a) : (⌈a⌉₊ : R) < a + 1 :=
  lt_ceil.1 <| (Nat.lt_succ_self _).trans_le (ceil_add_one ha).ge

@[bound]
/-
**Nat.ceil_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ceil_add_le (a b : R) : ⌈a + b⌉₊ <= ⌈a⌉₊ + ⌈b⌉₊
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ceil_le`：ceil_le : ⌈a⌉₊ <= n ↔ a <= n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
-/
theorem ceil_add_le (a b : R) : ⌈a + b⌉₊ ≤ ⌈a⌉₊ + ⌈b⌉₊ := by
  rw [ceil_le, Nat.cast_add]
  gcongr <;> apply le_ceil

variable [Sub R] [OrderedSub R] [ExistsAddOfLE R]
/-
**Nat.ceil_sub_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : LinearOrder R] [inst_2 : Fl
oorSemiring R] [IsStrictOrderedRing R]   [inst_4 : Sub R] [OrderedSub R] [Exists
AddOfLE R] (a : R) (n : ℕ), ⌈a - ↑n⌉₊ = ⌈a⌉₊ - n
参数：a : R；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.ceil_eq_zero`：ceil_eq_zero : ⌈a⌉₊ = 0 ↔ a <= 0
· 使用定理 `tsub_nonpos_of_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCom
mMonoid α] [inst_2 : Sub α] [OrderedSub α] {a b : α},   a ≤ b → a - b ≤ 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `Nat.ceil_le`：ceil_le : ⌈a⌉₊ <= n ↔ a <= n
· 使用定理 `eq_tsub_of_add_eq`：eq_tsub_of_add_eq (h : a + c = b) : a = b - c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ceil_add_natCast`：ceil_add_natCast (ha : 0 <= a) (n : Nat) : ⌈a + n⌉
₊ = ⌈a⌉₊ + n
· 使用定理 `le_tsub_of_add_le_left`：le_tsub_of_add_le_left (h : a + b <= c) : b <= c
 - a
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
-/
@[simp] lemma ceil_sub_natCast (a : R) (n : ℕ) : ⌈a - n⌉₊ = ⌈a⌉₊ - n := by
  obtain han | hna := le_total a n
  · rwa [ceil_eq_zero.2 (tsub_nonpos_of_le han), eq_comm, tsub_eq_zero_iff_le, Nat.ceil_le]
  · refine eq_tsub_of_add_eq ?_
    rw [← ceil_add_natCast, tsub_add_cancel_of_le hna]
    exact le_tsub_of_add_le_left ((add_zero _).trans_le hna)
/-
**Nat.ceil_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : LinearOrder R] [inst_2 : Fl
oorSemiring R] [IsStrictOrderedRing R]   [inst_4 : Sub R] [OrderedSub R] [Exists
AddOfLE R] (a : R), ⌈a - 1⌉₊ = ⌈a⌉₊ - 1
参数：a : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.ceil_sub_natCast`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Lin
earOrder R] [inst_2 : FloorSemiring R] [IsStrictOrderedRing R]   [inst_4 : Sub R
] [Ordered…
-/
@[simp] lemma ceil_sub_one (a : R) : ⌈a - 1⌉₊ = ⌈a⌉₊ - 1 := by simpa using ceil_sub_natCast a 1
/-
**Nat.ceil_sub_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : LinearOrder R] [inst_2 : Fl
oorSemiring R] [IsStrictOrderedRing R]   [inst_4 : Sub R] [OrderedSub R] [Exists
AddOfLE R] (a : R) (n : ℕ) [inst_7 : n.AtLeastTwo],   ⌈a - OfNat.ofNat n⌉₊ = ⌈a⌉
₊ - OfNat.ofNat n
参数：a : R；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ceil_sub_natCast`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Lin
earOrder R] [inst_2 : FloorSemiring R] [IsStrictOrderedRing R]   [inst_4 : Sub R
] [Ordered…
-/
@[simp] lemma ceil_sub_ofNat (a : R) (n : ℕ) [n.AtLeastTwo] : ⌈a - ofNat(n)⌉₊ = ⌈a⌉₊ - ofNat(n) :=
  ceil_sub_natCast a n

end LinearOrderedSemiring

section LinearOrderedRing

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]

@[bound]
/-
**Nat.sub_one_lt_floor** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sub_one_lt_floor (a : R) : a - 1 < ⌊a⌋₊
参数：a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_lt_iff_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a - c < b ↔ a < b + c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Nat.lt_floor_add_one`：lt_floor_add_one (a : R) : a < ⌊a⌋₊ + 1
-/
theorem sub_one_lt_floor (a : R) : a - 1 < ⌊a⌋₊ :=
  sub_lt_iff_lt_add.2 <| lt_floor_add_one a
/-
**Nat.self_sub_floor_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：self_sub_floor_lt_one (a : R) : a - ⌊a⌋₊ < 1
参数：a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_lt_iff_lt_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT 
α] [AddLeftStrictMono α] {a b c : α}, a - b < c ↔ a < b + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.lt_floor_add_one`：lt_floor_add_one (a : R) : a < ⌊a⌋₊ + 1
-/
lemma self_sub_floor_lt_one (a : R) : a - ⌊a⌋₊ < 1 :=
  sub_lt_iff_lt_add'.mpr <| lt_floor_add_one a
/-
**Nat.zero_le_self_sub_floor** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：zero_le_self_sub_floor {a : R} (ha : 0 <= a) : 0 <= a - ⌊a⌋₊
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.floor_le`：floor_le (ha : 0 <= a) : (⌊a⌋₊ : R) <= a
-/
lemma zero_le_self_sub_floor {a : R} (ha : 0 ≤ a) : 0 ≤ a - ⌊a⌋₊ :=
  sub_nonneg.mpr <| Nat.floor_le ha
/-
**Nat.abs_sub_floor_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：abs_sub_floor_le {a : R} (ha : 0 <= a) : |a - ⌊a⌋₊| <= 1
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.floor_le`：floor_le (ha : 0 <= a) : (⌊a⌋₊ : R) <= a
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.lt_floor_add_one`：lt_floor_add_one (a : R) : a < ⌊a⌋₊ + 1
-/
lemma abs_sub_floor_le {a : R} (ha : 0 ≤ a) : |a - ⌊a⌋₊| ≤ 1 := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa using (floor_le ha).trans (le_add_of_nonneg_right zero_le_one)
  · simpa [add_comm] using (lt_floor_add_one a).le
/-
**Nat.abs_floor_sub_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：abs_floor_sub_le {a : R} (ha : 0 <= a) : |⌊a⌋₊ - a| <= 1
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.abs_sub_floor_le`：abs_sub_floor_le {a : R} (ha : 0 <= a) : |a - ⌊a⌋₊
| <= 1
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
-/
lemma abs_floor_sub_le {a : R} (ha : 0 ≤ a) : |⌊a⌋₊ - a| ≤ 1 :=
  abs_sub_comm a ⌊a⌋₊ ▸ abs_sub_floor_le ha
/-
**Nat.abs_sub_ceil_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：abs_sub_ceil_le {a : R} (ha : 0 <= a) : |a - ⌈a⌉₊| <= 1
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.ceil_lt_add_one`：ceil_lt_add_one (ha : 0 <= a) : (⌈a⌉₊ : R) < a + 1
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
-/
lemma abs_sub_ceil_le {a : R} (ha : 0 ≤ a) : |a - ⌈a⌉₊| ≤ 1 := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa using (ceil_lt_add_one ha).le
  · simpa using (le_ceil a).trans (le_add_of_nonneg_left zero_le_one)
/-
**Nat.abs_ceil_sub_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：abs_ceil_sub_le {a : R} (ha : 0 <= a) : |⌈a⌉₊ - a| <= 1
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.abs_sub_ceil_le`：abs_sub_ceil_le {a : R} (ha : 0 <= a) : |a - ⌈a⌉₊| 
<= 1
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
-/
lemma abs_ceil_sub_le {a : R} (ha : 0 ≤ a) : |⌈a⌉₊ - a| ≤ 1 :=
  abs_sub_comm a ⌈a⌉₊ ▸ abs_sub_ceil_le ha

end LinearOrderedRing

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a : R}
variable {S : Type*} [Semiring S] [LinearOrder S] [FloorSemiring S] {b : S}

/-
**Nat.floor_congr** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：floor_congr [IsStrictOrderedRing R] [IsStrictOrderedRing S] (h : forall n 
: Nat, (n : R) <= a ↔ (n : S) <= b) : ⌊a⌋₊ = ⌊b⌋₊
参数：h : forall n : Nat, (n : R) <= a ↔ (n : S) <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Nat.floor_of_nonpos`：floor_of_nonpos (ha : a <= 0) : ⌊a⌋₊ = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Nat.le_floor`：le_floor (h : (n : α) <= a) : n <= ⌊a⌋₊
· 使用定理 `Nat.floor_le`：floor_le (ha : 0 <= a) : (⌊a⌋₊ : R) <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem floor_congr [IsStrictOrderedRing R] [IsStrictOrderedRing S]
    (h : ∀ n : ℕ, (n : R) ≤ a ↔ (n : S) ≤ b) : ⌊a⌋₊ = ⌊b⌋₊ := by
  have h₀ : 0 ≤ a ↔ 0 ≤ b := by simpa only [cast_zero] using h 0
  obtain ha | ha := lt_or_ge a 0
  · rw [floor_of_nonpos ha.le, floor_of_nonpos (le_of_not_ge <| h₀.not.mp ha.not_ge)]
  exact (le_floor <| (h _).1 <| floor_le ha).antisymm (le_floor <| (h _).2 <| floor_le <| h₀.1 ha)
/-
**Nat.ceil_congr** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ceil_congr (h : forall n : Nat, a <= n ↔ b <= n) : ⌈a⌉₊ = ⌈b⌉₊
参数：h : forall n : Nat, a <= n ↔ b <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.ceil_le`：ceil_le : ⌈a⌉₊ <= n ↔ a <= n
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem ceil_congr (h : ∀ n : ℕ, a ≤ n ↔ b ≤ n) : ⌈a⌉₊ = ⌈b⌉₊ :=
  (ceil_le.2 <| (h _).2 <| le_ceil _).antisymm <| ceil_le.2 <| (h _).1 <| le_ceil _

variable {F : Type*} [FunLike F R S] [RingHomClass F R S]
/-
**Nat.map_floor** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：map_floor [IsStrictOrderedRing R] [IsStrictOrderedRing S] (f : F) (hf : St
rictMono f) (a : R) : ⌊f a⌋₊ = ⌊a⌋₊
参数：f : F；hf : StrictMono f；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.floor_congr`：floor_congr [IsStrictOrderedRing R] [IsStrictOrderedRin
g S] (h : forall n : Nat, (n : R) <= a ↔ (n : S) <= b) : ⌊a⌋₊ = ⌊b⌋₊
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_floor [IsStrictOrderedRing R] [IsStrictOrderedRing S]
    (f : F) (hf : StrictMono f) (a : R) : ⌊f a⌋₊ = ⌊a⌋₊ :=
  floor_congr fun n => by rw [← map_natCast f, hf.le_iff_le]
/-
**Nat.map_ceil** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：map_ceil (f : F) (hf : StrictMono f) (a : R) : ⌈f a⌉₊ = ⌈a⌉₊
参数：f : F；hf : StrictMono f；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ceil_congr`：ceil_congr (h : forall n : Nat, a <= n ↔ b <= n) : ⌈a⌉₊ 
= ⌈b⌉₊
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_ceil (f : F) (hf : StrictMono f) (a : R) : ⌈f a⌉₊ = ⌈a⌉₊ :=
  ceil_congr fun n => by rw [← map_natCast f, hf.le_iff_le]

end Nat

/-- There exists at most one `FloorSemiring` structure on a linear ordered semiring. -/
/-
**subsingleton_floorSemiring** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subsingleton_floorSemiring {R} [Semiring R] [LinearOrder R] : Subsingleton
 (FloorSemiring R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `GaloisConnection.l_unique`：∀ {α : Type u} {β : Type v} [inst : PartialOr
der α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →  
   ∀ {u' : α → …
· 使用定理 `FloorSemiring.gc_ceil`：∀ {α : Type u_4} {inst : Semiring α} {inst_1 : Pa
rtialOrder α} [self : FloorSemiring α],   GaloisConnection FloorSemiring.ceil Na
t.cast
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FloorSemiring.floor_of_neg`：∀ {α : Type u_4} {inst : Semiring α} {inst_1
 : PartialOrder α} [self : FloorSemiring α] {a : α},   a < 0 → FloorSemiring.flo
or a = 0
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `FloorSemiring.gc_floor`：∀ {α : Type u_4} {inst : Semiring α} {inst_1 : P
artialOrder α} [self : FloorSemiring α] {a : α} {n : ℕ},   0 ≤ a → (n ≤ FloorSem
iring.floor …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
There exists at most one `FloorSemiring` structure on a linear ordered semiring.
-/
theorem subsingleton_floorSemiring {R} [Semiring R] [LinearOrder R] :
    Subsingleton (FloorSemiring R) := by
  refine ⟨fun H₁ H₂ => ?_⟩
  have : H₁.ceil = H₂.ceil := funext fun a => (H₁.gc_ceil.l_unique H₂.gc_ceil) fun n => rfl
  have : H₁.floor = H₂.floor := by
    ext a
    rcases lt_or_ge a 0 with h | h
    · rw [H₁.floor_of_neg, H₂.floor_of_neg] <;> exact h
    · refine eq_of_forall_le_iff fun n => ?_
      rw [H₁.gc_floor, H₂.gc_floor] <;> exact h
  cases H₁
  cases H₂
  congr
