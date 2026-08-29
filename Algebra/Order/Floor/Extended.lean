/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.Real.ENatENNReal

import Mathlib.Data.ENNReal.Operations

/-!
# Extended floor and ceil

This file defines the extended floor and ceil functions `ENat.floor, ENat.ceil : ℝ≥0∞ → ℕ∞`.

## Main declarations

* `ENat.floor r`: Greatest extended natural `n` such that `n ≤ r`.
* `ENat.ceil r`: Least extended natural `n` such that `r ≤ n`.

## Notation

* `⌊r⌋ₑ` is `ENat.floor r`.
* `⌈r⌉ₑ` is `ENat.ceil r`.

The index `ₑ` is used in analogy to the notation for `enorm`.

## TODO

The day Mathlib acquires `ENNRat`, it would be good to generalise this file to an `EFloorSemiring`
typeclass.

## Tags

efloor, eceil
-/

public section

open Set
open scoped ENNReal NNReal

namespace ENat
variable {r s : Real>=0∞} {n : Nat∞}

/--
Definition of `floor` / `floor` 的定义

English:
definition floor
  signature: : Real>=0∞ -> Nat∞

中文:
定义 floor
  签名: : 实数>=0∞ -> 自然数∞
-/
@[expose] noncomputable def floor : Real>=0∞ -> Nat∞
  | ∞ => ⊤
  | (r : Real>=0) => ⌊r⌋₊

/--
Definition of `ceil` / `ceil` 的定义

English:
definition ceil
  signature: : Real>=0∞ -> Nat∞

中文:
定义 ceil
  签名: : 实数>=0∞ -> 自然数∞
-/
@[expose] noncomputable def ceil : Real>=0∞ -> Nat∞
  | ∞ => ⊤
  | (r : Real>=0) => ⌈r⌉₊

@[inherit_doc] notation "⌊" r "⌋ₑ" => ENat.floor r
@[inherit_doc] notation "⌈" r "⌉ₑ" => ENat.ceil r

/--
lemma `floor_top` / 引理 `floor_top`

English:
lemma floor_top
  statement: ⌊∞⌋ₑ = ⊤
  proof: rfl

中文:
引理 floor_top
  结论: ⌊∞⌋ₑ = ⊤
  证明: rfl
-/
@[simp] lemma floor_top : ⌊∞⌋ₑ = ⊤ := rfl

/--
lemma `ceil_top` / 引理 `ceil_top`

English:
lemma ceil_top
  statement: ⌈∞⌉ₑ = ⊤
  proof: rfl

中文:
引理 ceil_top
  结论: ⌈∞⌉ₑ = ⊤
  证明: rfl
-/
@[simp] lemma ceil_top : ⌈∞⌉ₑ = ⊤ := rfl

/--
lemma `floor_coe` / 引理 `floor_coe`

English:
lemma floor_coe
  given: (r : Real>=0)
  statement: ⌊r⌋ₑ = ⌊r⌋₊
  proof: rfl

中文:
引理 floor_coe
  条件: (r : 实数>=0)
  结论: ⌊r⌋ₑ = ⌊r⌋₊
  证明: rfl
-/
@[simp, norm_cast] lemma floor_coe (r : Real>=0) : ⌊r⌋ₑ = ⌊r⌋₊ := rfl

/--
lemma `ceil_coe` / 引理 `ceil_coe`

English:
lemma ceil_coe
  given: (r : Real>=0)
  statement: ⌈r⌉ₑ = ⌈r⌉₊
  proof: rfl

中文:
引理 ceil_coe
  条件: (r : 实数>=0)
  结论: ⌈r⌉ₑ = ⌈r⌉₊
  证明: rfl
-/
@[simp, norm_cast] lemma ceil_coe (r : Real>=0) : ⌈r⌉ₑ = ⌈r⌉₊ := rfl

/--
lemma `floor_eq_top` / 引理 `floor_eq_top`

English:
lemma floor_eq_top
  statement: ⌊r⌋ₑ = ⊤ ↔ r = ∞
  proof: by cases r <;> simp

中文:
引理 floor_eq_top
  结论: ⌊r⌋ₑ = ⊤ ↔ r = ∞
  证明: by cases r <;> simp
-/
@[simp] lemma floor_eq_top : ⌊r⌋ₑ = ⊤ ↔ r = ∞ := by cases r <;> simp

/--
lemma `ceil_eq_top` / 引理 `ceil_eq_top`

English:
lemma ceil_eq_top
  statement: ⌈r⌉ₑ = ⊤ ↔ r = ∞
  proof: by cases r <;> simp

中文:
引理 ceil_eq_top
  结论: ⌈r⌉ₑ = ⊤ ↔ r = ∞
  证明: by cases r <;> simp
-/
@[simp] lemma ceil_eq_top : ⌈r⌉ₑ = ⊤ ↔ r = ∞ := by cases r <;> simp

/--
lemma `floor_lt_top` / 引理 `floor_lt_top`

English:
lemma floor_lt_top
  statement: ⌊r⌋ₑ < ⊤ ↔ r < ∞
  proof: by cases r <;> simp

中文:
引理 floor_lt_top
  结论: ⌊r⌋ₑ < ⊤ ↔ r < ∞
  证明: by cases r <;> simp
-/
lemma floor_lt_top : ⌊r⌋ₑ < ⊤ ↔ r < ∞ := by cases r <;> simp

/--
lemma `ceil_lt_top` / 引理 `ceil_lt_top`

English:
lemma ceil_lt_top
  statement: ⌈r⌉ₑ < ⊤ ↔ r < ∞
  proof: by cases r <;> simp

中文:
引理 ceil_lt_top
  结论: ⌈r⌉ₑ < ⊤ ↔ r < ∞
  证明: by cases r <;> simp
-/
@[simp] lemma ceil_lt_top : ⌈r⌉ₑ < ⊤ ↔ r < ∞ := by cases r <;> simp

/--
lemma `le_floor` / 引理 `le_floor`

English:
lemma le_floor
  statement: n <= ⌊r⌋ₑ ↔ n <= r
  proof: by cases r <;> cases n <;> simp [Nat.le_floor_iff]

中文:
引理 le_floor
  结论: n <= ⌊r⌋ₑ ↔ n <= r
  证明: by cases r <;> cases n <;> simp [Nat.le_floor_iff]
-/
@[simp] lemma le_floor : n <= ⌊r⌋ₑ ↔ n <= r := by cases r <;> cases n <;> simp [Nat.le_floor_iff]

/--
lemma `ceil_le` / 引理 `ceil_le`

English:
lemma ceil_le
  statement: ⌈r⌉ₑ <= n ↔ r <= n
  proof: by cases r <;> cases n <;> simp

中文:
引理 ceil_le
  结论: ⌈r⌉ₑ <= n ↔ r <= n
  证明: by cases r <;> cases n <;> simp
-/
@[simp] lemma ceil_le : ⌈r⌉ₑ <= n ↔ r <= n := by cases r <;> cases n <;> simp

/--
lemma `floor_lt` / 引理 `floor_lt`

English:
lemma floor_lt
  statement: ⌊r⌋ₑ < n ↔ r < n
  proof: lt_iff_lt_of_le_iff_le le_floor

中文:
引理 floor_lt
  结论: ⌊r⌋ₑ < n ↔ r < n
  证明: lt_iff_lt_of_le_iff_le le_floor
-/
@[simp] lemma floor_lt : ⌊r⌋ₑ < n ↔ r < n := lt_iff_lt_of_le_iff_le le_floor

/--
lemma `lt_ceil` / 引理 `lt_ceil`

English:
lemma lt_ceil
  statement: n < ⌈r⌉ₑ ↔ n < r
  proof: lt_iff_lt_of_le_iff_le ceil_le

中文:
引理 lt_ceil
  结论: n < ⌈r⌉ₑ ↔ n < r
  证明: lt_iff_lt_of_le_iff_le ceil_le

Depends on / 依赖: MulZeroOneClass
-/
@[simp] lemma lt_ceil : n < ⌈r⌉ₑ ↔ n < r := lt_iff_lt_of_le_iff_le ceil_le

/--
lemma `gc_toENNReal_floor` / 引理 `gc_toENNReal_floor`

English:
lemma gc_toENNReal_floor
  statement: GaloisConnection (↑) floor
  proof: fun _ _ => le_floor.symm

中文:
引理 gc_toENN实数_floor
  结论: GaloisConnection (↑) floor
  证明: fun _ _ => le_floor.symm

Depends on / 依赖: le_floor, le_floor.symm
-/
lemma gc_toENNReal_floor : GaloisConnection (↑) floor := fun _ _ => le_floor.symm
/--
lemma `gc_ceil_toENNReal` / 引理 `gc_ceil_toENNReal`

English:
lemma gc_ceil_toENNReal
  statement: GaloisConnection ceil (↑)
  proof: fun _ _ => ceil_le

中文:
引理 gc_ceil_toENN实数
  结论: GaloisConnection ceil (↑)
  证明: fun _ _ => ceil_le

Depends on / 依赖: ceil_le
-/
lemma gc_ceil_toENNReal : GaloisConnection ceil (↑) := fun _ _ => ceil_le

/--
lemma `floor_le_self` / 引理 `floor_le_self`

English:
lemma floor_le_self
  statement: ⌊r⌋ₑ <= r
  proof: le_floor.1 le_rfl

中文:
引理 floor_le_self
  结论: ⌊r⌋ₑ <= r
  证明: le_floor.1 le_rfl

Depends on / 依赖: MonoidWithZero
-/
@[bound] lemma floor_le_self : ⌊r⌋ₑ <= r := le_floor.1 le_rfl
/--
lemma `le_ceil_self` / 引理 `le_ceil_self`

English:
lemma le_ceil_self
  statement: r <= ⌈r⌉ₑ
  proof: ceil_le.1 le_rfl

中文:
引理 le_ceil_self
  结论: r <= ⌈r⌉ₑ
  证明: ceil_le.1 le_rfl
-/
@[bound] lemma le_ceil_self : r <= ⌈r⌉ₑ := ceil_le.1 le_rfl

/--
lemma `floor_le` / 引理 `floor_le`

English:
lemma floor_le
  given: (hn : n != ⊤)
  statement: ⌊r⌋ₑ <= n ↔ r < n + 1
  proof: by simp [← lt_add_one_iff hn]

中文:
引理 floor_le
  条件: (hn : n != ⊤)
  结论: ⌊r⌋ₑ <= n ↔ r < n + 1
  证明: by simp [← lt_add_one_iff hn]
-/
@[simp] lemma floor_le (hn : n != ⊤) : ⌊r⌋ₑ <= n ↔ r < n + 1 := by simp [← lt_add_one_iff hn]

/--
lemma `le_ceil` / 引理 `le_ceil`

English:
lemma le_ceil
  given: (hn₀ : n != 0) (hn : n != ⊤)
  statement: n <= ⌈r⌉ₑ ↔ n - 1 < r
  proof: by
  lift n to Nat using hn
  cases r
  · simp only [ceil_top, le_top, toENNReal_coe, true_iff]
    norm_cast
    exact ENNReal.coe_lt_top
  · simp only [ne_eq, Nat.cast_eq_zero, ceil_coe, Nat.cast_le, toENNReal_coe] at hn₀ ⊢
    norm_cast
    rw [← Nat.add_one_le_ceil_iff]; rw [Nat.sub_add_cancel]


中文:
引理 le_ceil
  条件: (hn₀ : n != 0) (hn : n != ⊤)
  结论: n <= ⌈r⌉ₑ ↔ n - 1 < r
  证明: by
  lift n to Nat using hn
  cases r
  · simp only [ceil_top, le_top, toENNReal_coe, true_iff]
    norm_cast
    exact ENNReal.coe_lt_top
  · simp only [ne_eq, Nat.cast_eq_zero, ceil_coe, Nat.cast_le, toENNReal_coe] at hn₀ ⊢
    norm_cast
    rw [← Nat.add_one_le_ceil_iff]; rw [Nat.sub_add_cancel]

-/
@[simp] lemma le_ceil (hn₀ : n != 0) (hn : n != ⊤) : n <= ⌈r⌉ₑ ↔ n - 1 < r := by
  lift n to Nat using hn
  cases r
  · simp only [ceil_top, le_top, toENNReal_coe, true_iff]
    norm_cast
    exact ENNReal.coe_lt_top
  · simp only [ne_eq, Nat.cast_eq_zero, ceil_coe, Nat.cast_le, toENNReal_coe] at hn₀ ⊢
    norm_cast
    rw [← Nat.add_one_le_ceil_iff]; rw [Nat.sub_add_cancel]
    lia

/--
lemma `lt_floor` / 引理 `lt_floor`

English:
lemma lt_floor
  given: (hn : n != ⊤)
  statement: n < ⌊r⌋ₑ ↔ n + 1 <= r
  proof: by simp [← add_one_le_iff hn]

中文:
引理 lt_floor
  条件: (hn : n != ⊤)
  结论: n < ⌊r⌋ₑ ↔ n + 1 <= r
  证明: by simp [← add_one_le_iff hn]

Depends on / 依赖: GroupWithZero
-/
@[simp] lemma lt_floor (hn : n != ⊤) : n < ⌊r⌋ₑ ↔ n + 1 <= r := by simp [← add_one_le_iff hn]

/--
lemma `ceil_lt` / 引理 `ceil_lt`

English:
lemma ceil_lt
  given: (hn₀ : n != 0) (hn : n != ⊤)
  statement: ⌈r⌉ₑ < n ↔ r <= n - 1
  proof: by
  simpa using (le_ceil hn₀ hn).not

中文:
引理 ceil_lt
  条件: (hn₀ : n != 0) (hn : n != ⊤)
  结论: ⌈r⌉ₑ < n ↔ r <= n - 1
  证明: by
  simpa using (le_ceil hn₀ hn).not
-/
@[simp] lemma ceil_lt (hn₀ : n != 0) (hn : n != ⊤) : ⌈r⌉ₑ < n ↔ r <= n - 1 := by
  simpa using (le_ceil hn₀ hn).not

/--
lemma `floor_mono` / 引理 `floor_mono`

English:
lemma floor_mono
  statement: Monotone (floor : Real>=0∞ -> Nat∞)
  proof: fun r s hrs => by simpa using hrs.trans' floor_le_self

中文:
引理 floor_mono
  结论: 递增 (floor : 实数>=0∞ -> 自然数∞)
  证明: fun r s hrs => by simpa using hrs.trans' floor_le_self

Depends on / 依赖: floor_le_self, hrs.trans
-/
lemma floor_mono : Monotone (floor : Real>=0∞ -> Nat∞) :=
  fun r s hrs => by simpa using hrs.trans' floor_le_self

/--
lemma `ceil_mono` / 引理 `ceil_mono`

English:
lemma ceil_mono
  statement: Monotone (ceil : Real>=0∞ -> Nat∞)
  proof: fun r s hrs => by simpa using hrs.trans le_ceil_self

中文:
引理 ceil_mono
  结论: 递增 (ceil : 实数>=0∞ -> 自然数∞)
  证明: fun r s hrs => by simpa using hrs.trans le_ceil_self

Depends on / 依赖: hrs.trans, le_ceil_self
-/
lemma ceil_mono : Monotone (ceil : Real>=0∞ -> Nat∞) := fun r s hrs => by simpa using hrs.trans le_ceil_self

/--
lemma `floor_le_floor` / 引理 `floor_le_floor`

English:
lemma floor_le_floor
  given: (hrs : r <= s)
  statement: ⌊r⌋ₑ <= ⌊s⌋ₑ
  proof: floor_mono hrs

中文:
引理 floor_le_floor
  条件: (hrs : r <= s)
  结论: ⌊r⌋ₑ <= ⌊s⌋ₑ
  证明: floor_mono hrs
-/
@[gcongr, bound] lemma floor_le_floor (hrs : r <= s) : ⌊r⌋ₑ <= ⌊s⌋ₑ := floor_mono hrs
/--
lemma `ceil_le_ceil` / 引理 `ceil_le_ceil`

English:
lemma ceil_le_ceil
  given: (hrs : r <= s)
  statement: ⌈r⌉ₑ <= ⌈s⌉ₑ
  proof: ceil_mono hrs

中文:
引理 ceil_le_ceil
  条件: (hrs : r <= s)
  结论: ⌈r⌉ₑ <= ⌈s⌉ₑ
  证明: ceil_mono hrs
-/
@[gcongr, bound] lemma ceil_le_ceil (hrs : r <= s) : ⌈r⌉ₑ <= ⌈s⌉ₑ := ceil_mono hrs

/--
lemma `floor_natCast` / 引理 `floor_natCast`

English:
lemma floor_natCast
  given: (n : Nat∞)
  statement: ⌊n⌋ₑ = n
  proof: eq_of_forall_le_iff fun r => by simp

中文:
引理 floor_natCast
  条件: (n : 自然数∞)
  结论: ⌊n⌋ₑ = n
  证明: eq_of_forall_le_iff fun r => by simp
-/
@[simp] lemma floor_natCast (n : Nat∞) : ⌊n⌋ₑ = n := eq_of_forall_le_iff fun r => by simp
/--
lemma `ceil_natCast` / 引理 `ceil_natCast`

English:
lemma ceil_natCast
  given: (n : Nat∞)
  statement: ⌈n⌉ₑ = n
  proof: eq_of_forall_ge_iff fun r => by simp

中文:
引理 ceil_natCast
  条件: (n : 自然数∞)
  结论: ⌈n⌉ₑ = n
  证明: eq_of_forall_ge_iff fun r => by simp
-/
@[simp] lemma ceil_natCast (n : Nat∞) : ⌈n⌉ₑ = n := eq_of_forall_ge_iff fun r => by simp
/--
lemma `floor_zero` / 引理 `floor_zero`

English:
lemma floor_zero
  statement: ⌊0⌋ₑ = 0
  proof: by simpa using floor_natCast 0

中文:
引理 floor_zero
  结论: ⌊0⌋ₑ = 0
  证明: by simpa using floor_natCast 0
-/
@[simp] lemma floor_zero : ⌊0⌋ₑ = 0 := by simpa using floor_natCast 0
/--
lemma `ceil_zero` / 引理 `ceil_zero`

English:
lemma ceil_zero
  statement: ⌈0⌉ₑ = 0
  proof: by simpa using ceil_natCast 0

中文:
引理 ceil_zero
  结论: ⌈0⌉ₑ = 0
  证明: by simpa using ceil_natCast 0
-/
@[simp] lemma ceil_zero : ⌈0⌉ₑ = 0 := by simpa using ceil_natCast 0
/--
lemma `floor_one` / 引理 `floor_one`

English:
lemma floor_one
  statement: ⌊1⌋ₑ = 1
  proof: by simpa using floor_natCast 1

中文:
引理 floor_one
  结论: ⌊1⌋ₑ = 1
  证明: by simpa using floor_natCast 1
-/
@[simp] lemma floor_one : ⌊1⌋ₑ = 1 := by simpa using floor_natCast 1
/--
lemma `ceil_one` / 引理 `ceil_one`

English:
lemma ceil_one
  statement: ⌈1⌉ₑ = 1
  proof: by simpa using ceil_natCast 1

中文:
引理 ceil_one
  结论: ⌈1⌉ₑ = 1
  证明: by simpa using ceil_natCast 1
-/
@[simp] lemma ceil_one : ⌈1⌉ₑ = 1 := by simpa using ceil_natCast 1
/--
lemma `floor_ofNat` / 引理 `floor_ofNat`

English:
lemma floor_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ⌊ofNat(n)⌋ₑ = ofNat(n)
  proof: ENat.floor_natCast n

中文:
引理 floor_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: ⌊of自然数(n)⌋ₑ = of自然数(n)
  证明: ENat.floor_natCast n
-/
@[simp] lemma floor_ofNat (n : Nat) [n.AtLeastTwo] : ⌊ofNat(n)⌋ₑ = ofNat(n) := ENat.floor_natCast n
/--
lemma `ceil_ofNat` / 引理 `ceil_ofNat`

English:
lemma ceil_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ⌈ofNat(n)⌉ₑ = ofNat(n)
  proof: ENat.ceil_natCast n

中文:
引理 ceil_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: ⌈of自然数(n)⌉ₑ = of自然数(n)
  证明: ENat.ceil_natCast n
-/
@[simp] lemma ceil_ofNat (n : Nat) [n.AtLeastTwo] : ⌈ofNat(n)⌉ₑ = ofNat(n) := ENat.ceil_natCast n

/--
lemma `floor_pos` / 引理 `floor_pos`

English:
lemma floor_pos
  statement: 0 < ⌊r⌋ₑ ↔ 1 <= r
  proof: by simp

中文:
引理 floor_pos
  结论: 0 < ⌊r⌋ₑ ↔ 1 <= r
  证明: by simp
-/
lemma floor_pos : 0 < ⌊r⌋ₑ ↔ 1 <= r := by simp
/--
lemma `ceil_pos` / 引理 `ceil_pos`

English:
lemma ceil_pos
  statement: 0 < ⌈r⌉ₑ ↔ 0 < r
  proof: by simp

中文:
引理 ceil_pos
  结论: 0 < ⌈r⌉ₑ ↔ 0 < r
  证明: by simp
-/
lemma ceil_pos : 0 < ⌈r⌉ₑ ↔ 0 < r := by simp

/--
lemma `floor_eq_zero` / 引理 `floor_eq_zero`

English:
lemma floor_eq_zero
  statement: ⌊r⌋ₑ = 0 ↔ r < 1
  proof: by simp [← nonpos_iff_eq_zero]

中文:
引理 floor_eq_zero
  结论: ⌊r⌋ₑ = 0 ↔ r < 1
  证明: by simp [← nonpos_iff_eq_zero]
-/
@[simp] lemma floor_eq_zero : ⌊r⌋ₑ = 0 ↔ r < 1 := by simp [← nonpos_iff_eq_zero]
/--
lemma `ceil_eq_zero` / 引理 `ceil_eq_zero`

English:
lemma ceil_eq_zero
  statement: ⌈r⌉ₑ = 0 ↔ r = 0
  proof: by simpa using ceil_le (n := 0)

中文:
引理 ceil_eq_zero
  结论: ⌈r⌉ₑ = 0 ↔ r = 0
  证明: by simpa using ceil_le (n := 0)

Depends on / 依赖: SMulZeroClass
-/
@[simp] lemma ceil_eq_zero : ⌈r⌉ₑ = 0 ↔ r = 0 := by simpa using ceil_le (n := 0)

/--
lemma `floor_le_ceil` / 引理 `floor_le_ceil`

English:
lemma floor_le_ceil
  statement: ⌊r⌋ₑ <= ⌈r⌉ₑ
  proof: mod_cast floor_le_self.trans le_ceil_self

中文:
引理 floor_le_ceil
  结论: ⌊r⌋ₑ <= ⌈r⌉ₑ
  证明: mod_cast floor_le_self.trans le_ceil_self

Depends on / 依赖: SMulWithZero
-/
@[bound] lemma floor_le_ceil : ⌊r⌋ₑ <= ⌈r⌉ₑ := mod_cast floor_le_self.trans le_ceil_self

/--
lemma `ceil_le_floor_add_one` / 引理 `ceil_le_floor_add_one`

English:
lemma ceil_le_floor_add_one
  statement: forall r : Real>=0∞, ⌈r⌉ₑ <= ⌊r⌋ₑ + 1

中文:
引理 ceil_le_floor_add_one
  结论: 对任意 r : 实数>=0∞, ⌈r⌉ₑ <= ⌊r⌋ₑ + 1
-/
@[bound] lemma ceil_le_floor_add_one : forall r : Real>=0∞, ⌈r⌉ₑ <= ⌊r⌋ₑ + 1
  | ∞ => le_rfl
  | (r : Real>=0) => by simpa using mod_cast Nat.ceil_le_floor_add_one r

/--
lemma `floor_lt_ceil` / 引理 `floor_lt_ceil`

English:
lemma floor_lt_ceil
  given: (hrs : r < s)
  statement: ⌊r⌋ₑ < ⌈s⌉ₑ
  proof: floor_lt.2 hrs.trans_le le_ceil_self

中文:
引理 floor_lt_ceil
  条件: (hrs : r < s)
  结论: ⌊r⌋ₑ < ⌈s⌉ₑ
  证明: floor_lt.2 hrs.trans_le le_ceil_self

Depends on / 依赖: DistribSMul, floor_lt, hrs.trans_le, le_ceil_self, trans_le
-/
lemma floor_lt_ceil (hrs : r < s) : ⌊r⌋ₑ < ⌈s⌉ₑ := floor_lt.2 hrs.trans_le le_ceil_self

/--
lemma `floor_congr` / 引理 `floor_congr`

English:
lemma floor_congr
  given: (h : forall n : Nat∞, n <= r ↔ n <= s)
  statement: ⌊r⌋ₑ = ⌊s⌋ₑ
  proof: eq_of_forall_le_iff by simpa

中文:
引理 floor_congr
  条件: (h : 对任意 n : 自然数∞, n <= r ↔ n <= s)
  结论: ⌊r⌋ₑ = ⌊s⌋ₑ
  证明: eq_of_forall_le_iff by simpa

Depends on / 依赖: eq_of_forall_le_iff
-/
lemma floor_congr (h : forall n : Nat∞, n <= r ↔ n <= s) : ⌊r⌋ₑ = ⌊s⌋ₑ := eq_of_forall_le_iff by simpa
/--
lemma `ceil_congr` / 引理 `ceil_congr`

English:
lemma ceil_congr
  given: (h : forall n : Nat∞, r <= n ↔ s <= n)
  statement: ⌈r⌉ₑ = ⌈s⌉ₑ
  proof: eq_of_forall_ge_iff by simpa

中文:
引理 ceil_congr
  条件: (h : 对任意 n : 自然数∞, r <= n ↔ s <= n)
  结论: ⌈r⌉ₑ = ⌈s⌉ₑ
  证明: eq_of_forall_ge_iff by simpa

Depends on / 依赖: DistribMulAction, eq_of_forall_ge_iff
-/
lemma ceil_congr (h : forall n : Nat∞, r <= n ↔ s <= n) : ⌈r⌉ₑ = ⌈s⌉ₑ := eq_of_forall_ge_iff by simpa

/--
lemma `floor_add_toENNReal` / 引理 `floor_add_toENNReal`

English:
lemma floor_add_toENNReal
  statement: forall (r : Real>=0∞) (n : Nat∞), ⌊r + n⌋ₑ = ⌊r⌋ₑ + n

中文:
引理 floor_add_toENN实数
  结论: 对任意 (r : 实数>=0∞) (n : 自然数∞), ⌊r + n⌋ₑ = ⌊r⌋ₑ + n
-/
@[simp] lemma floor_add_toENNReal : forall (r : Real>=0∞) (n : Nat∞), ⌊r + n⌋ₑ = ⌊r⌋ₑ + n
  | ∞, _ => by simp
  | _, ⊤ => by simp
  | (r : Real>=0), (n : Nat) => by
    -- FIXME: Why does `norm_cast` not use `ENNReal.ofNNReal_add_natCast`?
    norm_cast; rw [← ENNReal.ofNNReal_add_natCast]; norm_cast; exact n.floor_add_natCast zero_le

/--
lemma `ceil_add_toENNReal` / 引理 `ceil_add_toENNReal`

English:
lemma ceil_add_toENNReal
  statement: forall (r : Real>=0∞) (n : Nat∞), ⌈r + n⌉ₑ = ⌈r⌉ₑ + n

中文:
引理 ceil_add_toENN实数
  结论: 对任意 (r : 实数>=0∞) (n : 自然数∞), ⌈r + n⌉ₑ = ⌈r⌉ₑ + n

Depends on / 依赖: MulActionWithZero
-/
@[simp] lemma ceil_add_toENNReal : forall (r : Real>=0∞) (n : Nat∞), ⌈r + n⌉ₑ = ⌈r⌉ₑ + n
  | ∞, _ => by simp
  | _, ⊤ => by simp
  | (r : Real>=0), (n : Nat) => by
    -- FIXME: Why does `norm_cast` not use `ENNReal.ofNNReal_sub_natCast`?
    norm_cast; rw [← ENNReal.ofNNReal_add_natCast]; norm_cast; exact Nat.ceil_add_natCast zero_le _

/--
lemma `floor_toENNReal_add` / 引理 `floor_toENNReal_add`

English:
lemma floor_toENNReal_add
  given: (r : Real>=0∞) (n : Nat∞)
  statement: ⌊n + r⌋ₑ = n + ⌊r⌋ₑ
  proof: by
  simp [add_comm, floor_add_toENNReal]

中文:
引理 floor_toENN实数_add
  条件: (r : 实数>=0∞) (n : 自然数∞)
  结论: ⌊n + r⌋ₑ = n + ⌊r⌋ₑ
  证明: by
  simp [add_comm, floor_add_toENNReal]

Depends on / 依赖: MulActionWithZero
-/
@[simp] lemma floor_toENNReal_add (r : Real>=0∞) (n : Nat∞) : ⌊n + r⌋ₑ = n + ⌊r⌋ₑ := by
  simp [add_comm, floor_add_toENNReal]

/--
lemma `ceil_toENNReal_add` / 引理 `ceil_toENNReal_add`

English:
lemma ceil_toENNReal_add
  given: (r : Real>=0∞) (n : Nat∞)
  statement: ⌈n + r⌉ₑ = n + ⌈r⌉ₑ
  proof: by
  simp [add_comm, ceil_add_toENNReal]

中文:
引理 ceil_toENN实数_add
  条件: (r : 实数>=0∞) (n : 自然数∞)
  结论: ⌈n + r⌉ₑ = n + ⌈r⌉ₑ
  证明: by
  simp [add_comm, ceil_add_toENNReal]
-/
@[simp] lemma ceil_toENNReal_add (r : Real>=0∞) (n : Nat∞) : ⌈n + r⌉ₑ = n + ⌈r⌉ₑ := by
  simp [add_comm, ceil_add_toENNReal]

/--
lemma `floor_add_natCast` / 引理 `floor_add_natCast`

English:
lemma floor_add_natCast
  given: (r : Real>=0∞) (n : Nat)
  statement: ⌊r + n⌋ₑ = ⌊r⌋ₑ + n
  proof: floor_add_toENNReal r n

中文:
引理 floor_add_natCast
  条件: (r : 实数>=0∞) (n : 自然数)
  结论: ⌊r + n⌋ₑ = ⌊r⌋ₑ + n
  证明: floor_add_toENNReal r n
-/
@[simp] lemma floor_add_natCast (r : Real>=0∞) (n : Nat) : ⌊r + n⌋ₑ = ⌊r⌋ₑ + n := floor_add_toENNReal r n
/--
lemma `ceil_add_natCast` / 引理 `ceil_add_natCast`

English:
lemma ceil_add_natCast
  given: (r : Real>=0∞) (n : Nat)
  statement: ⌈r + n⌉ₑ = ⌈r⌉ₑ + n
  proof: ceil_add_toENNReal r n

中文:
引理 ceil_add_natCast
  条件: (r : 实数>=0∞) (n : 自然数)
  结论: ⌈r + n⌉ₑ = ⌈r⌉ₑ + n
  证明: ceil_add_toENNReal r n
-/
@[simp] lemma ceil_add_natCast (r : Real>=0∞) (n : Nat) : ⌈r + n⌉ₑ = ⌈r⌉ₑ + n := ceil_add_toENNReal r n

/--
lemma `floor_natCast_add` / 引理 `floor_natCast_add`

English:
lemma floor_natCast_add
  given: (r : Real>=0∞) (n : Nat)
  statement: ⌊n + r⌋ₑ = n + ⌊r⌋ₑ
  proof: floor_toENNReal_add r n

中文:
引理 floor_natCast_add
  条件: (r : 实数>=0∞) (n : 自然数)
  结论: ⌊n + r⌋ₑ = n + ⌊r⌋ₑ
  证明: floor_toENNReal_add r n
-/
@[simp] lemma floor_natCast_add (r : Real>=0∞) (n : Nat) : ⌊n + r⌋ₑ = n + ⌊r⌋ₑ := floor_toENNReal_add r n
/--
lemma `ceil_natCast_add` / 引理 `ceil_natCast_add`

English:
lemma ceil_natCast_add
  given: (r : Real>=0∞) (n : Nat)
  statement: ⌈n + r⌉ₑ = n + ⌈r⌉ₑ
  proof: ceil_toENNReal_add r n

中文:
引理 ceil_natCast_add
  条件: (r : 实数>=0∞) (n : 自然数)
  结论: ⌈n + r⌉ₑ = n + ⌈r⌉ₑ
  证明: ceil_toENNReal_add r n
-/
@[simp] lemma ceil_natCast_add (r : Real>=0∞) (n : Nat) : ⌈n + r⌉ₑ = n + ⌈r⌉ₑ := ceil_toENNReal_add r n

/--
lemma `floor_add_one` / 引理 `floor_add_one`

English:
lemma floor_add_one
  given: (r : Real>=0∞)
  statement: ⌊r + 1⌋ₑ = ⌊r⌋ₑ + 1
  proof: mod_cast floor_add_natCast r 1

中文:
引理 floor_add_one
  条件: (r : 实数>=0∞)
  结论: ⌊r + 1⌋ₑ = ⌊r⌋ₑ + 1
  证明: mod_cast floor_add_natCast r 1
-/
@[simp] lemma floor_add_one (r : Real>=0∞) : ⌊r + 1⌋ₑ = ⌊r⌋ₑ + 1 := mod_cast floor_add_natCast r 1
/--
lemma `ceil_add_one` / 引理 `ceil_add_one`

English:
lemma ceil_add_one
  given: (r : Real>=0∞)
  statement: ⌈r + 1⌉ₑ = ⌈r⌉ₑ + 1
  proof: mod_cast ceil_add_natCast r 1

@[simp]

中文:
引理 ceil_add_one
  条件: (r : 实数>=0∞)
  结论: ⌈r + 1⌉ₑ = ⌈r⌉ₑ + 1
  证明: mod_cast ceil_add_natCast r 1

@[simp]
-/
@[simp] lemma ceil_add_one (r : Real>=0∞) : ⌈r + 1⌉ₑ = ⌈r⌉ₑ + 1 := mod_cast ceil_add_natCast r 1

@[simp]
/--
lemma `floor_add_ofNat` / 引理 `floor_add_ofNat`

English:
lemma floor_add_ofNat
  given: (r : Real>=0∞) (n : Nat) [n.AtLeastTwo]
  statement: ⌊r + ofNat(n)⌋ₑ = ⌊r⌋ₑ + ofNat(n)
  proof: floor_add_natCast r n

@[simp]

中文:
引理 floor_add_of自然数
  条件: (r : 实数>=0∞) (n : 自然数) [n.AtLeastTwo]
  结论: ⌊r + of自然数(n)⌋ₑ = ⌊r⌋ₑ + of自然数(n)
  证明: floor_add_natCast r n

@[simp]

Depends on / 依赖: floor_add_natCast
-/
lemma floor_add_ofNat (r : Real>=0∞) (n : Nat) [n.AtLeastTwo] : ⌊r + ofNat(n)⌋ₑ = ⌊r⌋ₑ + ofNat(n) :=
  floor_add_natCast r n

@[simp]
/--
lemma `ceil_add_ofNat` / 引理 `ceil_add_ofNat`

English:
lemma ceil_add_ofNat
  given: (r : Real>=0∞) (n : Nat) [n.AtLeastTwo]
  statement: ⌈r + ofNat(n)⌉ₑ = ⌈r⌉ₑ + ofNat(n)
  proof: ceil_add_natCast r n

中文:
引理 ceil_add_of自然数
  条件: (r : 实数>=0∞) (n : 自然数) [n.AtLeastTwo]
  结论: ⌈r + of自然数(n)⌉ₑ = ⌈r⌉ₑ + of自然数(n)
  证明: ceil_add_natCast r n

Depends on / 依赖: ceil_add_natCast
-/
lemma ceil_add_ofNat (r : Real>=0∞) (n : Nat) [n.AtLeastTwo] : ⌈r + ofNat(n)⌉ₑ = ⌈r⌉ₑ + ofNat(n) :=
  ceil_add_natCast r n

/--
lemma `floor_sub_toENNReal` / 引理 `floor_sub_toENNReal`

English:
lemma floor_sub_toENNReal
  statement: forall (r : Real>=0∞) (n : Nat∞), ⌊r - n⌋ₑ = ⌊r⌋ₑ - n

中文:
引理 floor_sub_toENN实数
  结论: 对任意 (r : 实数>=0∞) (n : 自然数∞), ⌊r - n⌋ₑ = ⌊r⌋ₑ - n
-/
@[simp] lemma floor_sub_toENNReal : forall (r : Real>=0∞) (n : Nat∞), ⌊r - n⌋ₑ = ⌊r⌋ₑ - n
  | ∞, ⊤ => by simp
  | ∞, (n : Nat) => by simp
  | (r : Real>=0), ⊤ => by simp
  | (r : Real>=0), (n : Nat) => by
    -- FIXME: Why does `norm_cast` not use `ENNReal.ofNNReal_sub_natCast`?
    norm_cast; rw [← ENNReal.ofNNReal_sub_natCast]; norm_cast; exact Nat.floor_sub_natCast ..

/--
lemma `ceil_sub_toENNReal` / 引理 `ceil_sub_toENNReal`

English:
lemma ceil_sub_toENNReal
  statement: forall (r : Real>=0∞) (n : Nat∞), ⌈r - n⌉ₑ = ⌈r⌉ₑ - n

中文:
引理 ceil_sub_toENN实数
  结论: 对任意 (r : 实数>=0∞) (n : 自然数∞), ⌈r - n⌉ₑ = ⌈r⌉ₑ - n
-/
@[simp] lemma ceil_sub_toENNReal : forall (r : Real>=0∞) (n : Nat∞), ⌈r - n⌉ₑ = ⌈r⌉ₑ - n
  | ∞, ⊤ => by simp
  | ∞, (n : Nat) => by simp
  | (r : Real>=0), ⊤ => by simp
  | (r : Real>=0), (n : Nat) => by
    -- FIXME: Why does `norm_cast` not use `ENNReal.ofNNReal_sub_natCast`?
    norm_cast; rw [← ENNReal.ofNNReal_sub_natCast]; norm_cast; exact Nat.ceil_sub_natCast ..

/--
lemma `floor_sub_natCast` / 引理 `floor_sub_natCast`

English:
lemma floor_sub_natCast
  given: (r : Real>=0∞) (n : Nat)
  statement: ⌊r - n⌋ₑ = ⌊r⌋ₑ - n
  proof: floor_sub_toENNReal r n

中文:
引理 floor_sub_natCast
  条件: (r : 实数>=0∞) (n : 自然数)
  结论: ⌊r - n⌋ₑ = ⌊r⌋ₑ - n
  证明: floor_sub_toENNReal r n
-/
@[simp] lemma floor_sub_natCast (r : Real>=0∞) (n : Nat) : ⌊r - n⌋ₑ = ⌊r⌋ₑ - n := floor_sub_toENNReal r n
/--
lemma `ceil_sub_natCast` / 引理 `ceil_sub_natCast`

English:
lemma ceil_sub_natCast
  given: (r : Real>=0∞) (n : Nat)
  statement: ⌈r - n⌉ₑ = ⌈r⌉ₑ - n
  proof: ceil_sub_toENNReal r n

中文:
引理 ceil_sub_natCast
  条件: (r : 实数>=0∞) (n : 自然数)
  结论: ⌈r - n⌉ₑ = ⌈r⌉ₑ - n
  证明: ceil_sub_toENNReal r n

Depends on / 依赖: AddGroup, AddGroupSeminormClass, AddGroupSeminormClass.toZeroHomClass, toZeroHomClass
-/
@[simp] lemma ceil_sub_natCast (r : Real>=0∞) (n : Nat) : ⌈r - n⌉ₑ = ⌈r⌉ₑ - n := ceil_sub_toENNReal r n

/--
lemma `floor_sub_one` / 引理 `floor_sub_one`

English:
lemma floor_sub_one
  given: (r : Real>=0∞)
  statement: ⌊r - 1⌋ₑ = ⌊r⌋ₑ - 1
  proof: mod_cast floor_sub_toENNReal r 1

中文:
引理 floor_sub_one
  条件: (r : 实数>=0∞)
  结论: ⌊r - 1⌋ₑ = ⌊r⌋ₑ - 1
  证明: mod_cast floor_sub_toENNReal r 1
-/
@[simp] lemma floor_sub_one (r : Real>=0∞) : ⌊r - 1⌋ₑ = ⌊r⌋ₑ - 1 := mod_cast floor_sub_toENNReal r 1
/--
lemma `ceil_sub_one` / 引理 `ceil_sub_one`

English:
lemma ceil_sub_one
  given: (r : Real>=0∞)
  statement: ⌈r - 1⌉ₑ = ⌈r⌉ₑ - 1
  proof: mod_cast ceil_sub_toENNReal r 1

@[simp]

中文:
引理 ceil_sub_one
  条件: (r : 实数>=0∞)
  结论: ⌈r - 1⌉ₑ = ⌈r⌉ₑ - 1
  证明: mod_cast ceil_sub_toENNReal r 1

@[simp]
-/
@[simp] lemma ceil_sub_one (r : Real>=0∞) : ⌈r - 1⌉ₑ = ⌈r⌉ₑ - 1 := mod_cast ceil_sub_toENNReal r 1

@[simp]
/--
lemma `floor_sub_ofNat` / 引理 `floor_sub_ofNat`

English:
lemma floor_sub_ofNat
  given: (r : Real>=0∞) (n : Nat) [n.AtLeastTwo]
  statement: ⌊r - ofNat(n)⌋ₑ = ⌊r⌋ₑ - ofNat(n)
  proof: floor_sub_toENNReal r n

中文:
引理 floor_sub_of自然数
  条件: (r : 实数>=0∞) (n : 自然数) [n.AtLeastTwo]
  结论: ⌊r - of自然数(n)⌋ₑ = ⌊r⌋ₑ - of自然数(n)
  证明: floor_sub_toENNReal r n

Depends on / 依赖: floor_sub_toENNReal
-/
lemma floor_sub_ofNat (r : Real>=0∞) (n : Nat) [n.AtLeastTwo] : ⌊r - ofNat(n)⌋ₑ = ⌊r⌋ₑ - ofNat(n) :=
  floor_sub_toENNReal r n

/--
lemma `ceil_sub_ofNat` / 引理 `ceil_sub_ofNat`

English:
lemma ceil_sub_ofNat
  given: (r : Real>=0∞) (n : Nat) [n.AtLeastTwo]
  proof: ceil_sub_toENNReal r n

@[bound]

中文:
引理 ceil_sub_of自然数
  条件: (r : 实数>=0∞) (n : 自然数) [n.AtLeastTwo]
  证明: ceil_sub_toENNReal r n

@[bound]
-/
@[simp] lemma ceil_sub_ofNat (r : Real>=0∞) (n : Nat) [n.AtLeastTwo] :
    ⌈r - ofNat(n)⌉ₑ = ⌈r⌉ₑ - ofNat(n) := ceil_sub_toENNReal r n

@[bound]
/--
lemma `ceil_lt_add_one` / 引理 `ceil_lt_add_one`

English:
lemma ceil_lt_add_one
  given: (hr : r != ∞)
  statement: (⌈r⌉ₑ : Real>=0∞) < r + 1
  proof: by
  lift r to Real>=0 using hr; simpa using mod_cast Nat.ceil_lt_add_one zero_le

@[bound]

中文:
引理 ceil_lt_add_one
  条件: (hr : r != ∞)
  结论: (⌈r⌉ₑ : 实数>=0∞) < r + 1
  证明: by
  lift r to Real>=0 using hr; simpa using mod_cast Nat.ceil_lt_add_one zero_le

@[bound]

Depends on / 依赖: Nat.ceil_lt_add_one, ceil_lt_add_one, mod_cast, zero_le
-/
lemma ceil_lt_add_one (hr : r != ∞) : (⌈r⌉ₑ : Real>=0∞) < r + 1 := by
  lift r to Real>=0 using hr; simpa using mod_cast Nat.ceil_lt_add_one zero_le

@[bound]
/--
lemma `ceil_add_le` / 引理 `ceil_add_le`

English:
lemma ceil_add_le
  statement: forall (r s : Real>=0∞), ⌈r + s⌉ₑ <= ⌈r⌉ₑ + ⌈s⌉ₑ

中文:
引理 ceil_add_le
  结论: 对任意 (r s : 实数>=0∞), ⌈r + s⌉ₑ <= ⌈r⌉ₑ + ⌈s⌉ₑ

Depends on / 依赖: GroupSeminormClass, GroupSeminormClass.toNonnegHomClass, toNonnegHomClass
-/
lemma ceil_add_le : forall (r s : Real>=0∞), ⌈r + s⌉ₑ <= ⌈r⌉ₑ + ⌈s⌉ₑ
  | ∞, _ => by simp
  | _, ∞ => by simp
  | (r : Real>=0), (s : Real>=0) => mod_cast Nat.ceil_add_le r s

/--
lemma `toENNReal_iSup` / 引理 `toENNReal_iSup`

English:
lemma toENNReal_iSup
  given: {ι : Sort*} (f : ι -> Nat∞)
  proof: eq_of_forall_ge_iff fun _ => by simp [← le_floor]

中文:
引理 toENN实数_iSup
  条件: {ι : 类型层*} (f : ι -> 自然数∞)
  证明: eq_of_forall_ge_iff fun _ => by simp [← le_floor]
-/
@[simp] lemma toENNReal_iSup {ι : Sort*} (f : ι -> Nat∞) :
    toENNReal (⨆ i, f i) = ⨆ i, toENNReal (f i) := eq_of_forall_ge_iff fun _ => by simp [← le_floor]

/--
lemma `toENNReal_iInf` / 引理 `toENNReal_iInf`

English:
lemma toENNReal_iInf
  given: {ι : Sort*} (f : ι -> Nat∞)
  proof: eq_of_forall_le_iff fun _ => by simp [← ceil_le]

中文:
引理 toENN实数_iInf
  条件: {ι : 类型层*} (f : ι -> 自然数∞)
  证明: eq_of_forall_le_iff fun _ => by simp [← ceil_le]
-/
@[simp] lemma toENNReal_iInf {ι : Sort*} (f : ι -> Nat∞) :
    toENNReal (⨅ i, f i) = ⨅ i, toENNReal (f i) := eq_of_forall_le_iff fun _ => by simp [← ceil_le]

/--
lemma `preimage_toENNReal_Ioi` / 引理 `preimage_toENNReal_Ioi`

English:
lemma preimage_toENNReal_Ioi
  given: (a : Real>=0∞)
  proof: by ext; simp

中文:
引理 preimage_toENN实数_Ioi
  条件: (a : 实数>=0∞)
  证明: by ext; simp
-/
@[simp] lemma preimage_toENNReal_Ioi (a : Real>=0∞) :
    toENNReal ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋ₑ := by ext; simp

/--
lemma `preimage_toENNReal_Iio` / 引理 `preimage_toENNReal_Iio`

English:
lemma preimage_toENNReal_Iio
  given: (a : Real>=0∞)
  proof: by ext; simp

中文:
引理 preimage_toENN实数_Iio
  条件: (a : 实数>=0∞)
  证明: by ext; simp

Depends on / 依赖: NonUnitalNonAssocRing, RingSeminormClass, RingSeminormClass.toNonnegHomClass, toNonnegHomClass
-/
@[simp] lemma preimage_toENNReal_Iio (a : Real>=0∞) :
    toENNReal ⁻¹' Set.Iio a = Set.Iio ⌈a⌉ₑ := by ext; simp

/--
lemma `preimage_toENNReal_Iic` / 引理 `preimage_toENNReal_Iic`

English:
lemma preimage_toENNReal_Iic
  given: (a : Real>=0∞)
  proof: by ext; simp

中文:
引理 preimage_toENN实数_Iic
  条件: (a : 实数>=0∞)
  证明: by ext; simp

Depends on / 依赖: MulRingSeminormClass, MulRingSeminormClass.toRingSeminormClass, NonAssocRing, toRingSeminormClass
-/
@[simp] lemma preimage_toENNReal_Iic (a : Real>=0∞) :
    toENNReal ⁻¹' Set.Iic a = Set.Iic ⌊a⌋ₑ := by ext; simp

/--
lemma `preimage_toENNReal_Ici` / 引理 `preimage_toENNReal_Ici`

English:
lemma preimage_toENNReal_Ici
  given: (a : Real>=0∞)
  proof: by ext; simp

中文:
引理 preimage_toENN实数_Ici
  条件: (a : 实数>=0∞)
  证明: by ext; simp

Depends on / 依赖: MulRingNormClass, MulRingNormClass.toRingNormClass, NonAssocRing, toRingNormClass
-/
@[simp] lemma preimage_toENNReal_Ici (a : Real>=0∞) :
    toENNReal ⁻¹' Set.Ici a = Set.Ici ⌈a⌉ₑ := by ext; simp

/--
lemma `preimage_toENNReal_Icc` / 引理 `preimage_toENNReal_Icc`

English:
lemma preimage_toENNReal_Icc
  given: (a b : Real>=0∞)
  proof: by ext; simp

中文:
引理 preimage_toENN实数_Icc
  条件: (a b : 实数>=0∞)
  证明: by ext; simp
-/
@[simp] lemma preimage_toENNReal_Icc (a b : Real>=0∞) :
    toENNReal ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉ₑ ⌊b⌋ₑ := by ext; simp

/--
lemma `preimage_toENNReal_Ico` / 引理 `preimage_toENNReal_Ico`

English:
lemma preimage_toENNReal_Ico
  given: (a b : Real>=0∞)
  proof: by ext; simp

中文:
引理 preimage_toENN实数_Ico
  条件: (a b : 实数>=0∞)
  证明: by ext; simp
-/
@[simp] lemma preimage_toENNReal_Ico (a b : Real>=0∞) :
    toENNReal ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉ₑ ⌈b⌉ₑ := by ext; simp

/--
lemma `preimage_toENNReal_Ioc` / 引理 `preimage_toENNReal_Ioc`

English:
lemma preimage_toENNReal_Ioc
  given: (a b : Real>=0∞)
  proof: by ext; simp

中文:
引理 preimage_toENN实数_Ioc
  条件: (a b : 实数>=0∞)
  证明: by ext; simp
-/
@[simp] lemma preimage_toENNReal_Ioc (a b : Real>=0∞) :
    toENNReal ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋ₑ ⌊b⌋ₑ := by ext; simp

/--
lemma `preimage_toENNReal_Ioo` / 引理 `preimage_toENNReal_Ioo`

English:
lemma preimage_toENNReal_Ioo
  given: (a b : Real>=0∞)
  proof: by ext; simp

中文:
引理 preimage_toENN实数_Ioo
  条件: (a b : 实数>=0∞)
  证明: by ext; simp
-/
@[simp] lemma preimage_toENNReal_Ioo (a b : Real>=0∞) :
    toENNReal ⁻¹' Set.Ioo a b = Set.Ioo ⌊a⌋ₑ ⌈b⌉ₑ := by ext; simp

end ENat

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

alias ⟨_, natCeil_pos⟩ := ENat.ceil_pos

/-- Extension for the `positivity` tactic: `ENat.ceil` is positive if its input is. -/
@[positivity ⌈_⌉ₑ]
meta def evalENatCeil : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Nat∞), ~q(ENat.ceil $r) =>
    match ← core q(inferInstance) (some q(inferInstance)) r with
    | .positive pr =>
      assertInstancesCommute
      pure (.positive q(natCeil_pos $pr))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on ENat.ceil application"

example {r : Real>=0∞} (hr : 0 < r) : 0 < ⌈r⌉ₑ := by positivity

end Mathlib.Meta.Positivity
