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

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : Nat}

section floor

/--
theorem `floor_lt` / 定理 `floor_lt`

English:
theorem floor_lt
  given: (ha : 0 <= a)
  statement: ⌊a⌋₊ < n ↔ a < n
  proof: lt_iff_lt_of_le_iff_le le_floor_iff ha

中文:
定理 floor_lt
  条件: (ha : 0 <= a)
  结论: ⌊a⌋₊ < n ↔ a < n
  证明: lt_iff_lt_of_le_iff_le le_floor_iff ha

Depends on / 依赖: le_floor_iff, lt_iff_lt_of_le_iff_le
-/
theorem floor_lt (ha : 0 <= a) : ⌊a⌋₊ < n ↔ a < n :=
lt_iff_lt_of_le_iff_le le_floor_iff ha

/--
theorem `floor_lt_one` / 定理 `floor_lt_one`

English:
theorem floor_lt_one
  given: (ha : 0 <= a)
  statement: ⌊a⌋₊ < 1 ↔ a < 1
  proof: (floor_lt ha).trans by rw [Nat.cast_one]

中文:
定理 floor_lt_one
  条件: (ha : 0 <= a)
  结论: ⌊a⌋₊ < 1 ↔ a < 1
  证明: (floor_lt ha).trans by rw [Nat.cast_one]

Depends on / 依赖: Nat.cast_one, cast_one, floor_lt
-/
theorem floor_lt_one (ha : 0 <= a) : ⌊a⌋₊ < 1 ↔ a < 1 :=
(floor_lt ha).trans by rw [Nat.cast_one]

/--
theorem `floor_le` / 定理 `floor_le`

English:
theorem floor_le
  given: (ha : 0 <= a)
  statement: (⌊a⌋₊ : R) <= a
  proof: (le_floor_iff ha).1 le_rfl

中文:
定理 floor_le
  条件: (ha : 0 <= a)
  结论: (⌊a⌋₊ : R) <= a
  证明: (le_floor_iff ha).1 le_rfl

Depends on / 依赖: le_floor_iff, le_rfl
-/
theorem floor_le (ha : 0 <= a) : (⌊a⌋₊ : R) <= a :=
  (le_floor_iff ha).1 le_rfl

/--
theorem `floor_eq_iff` / 定理 `floor_eq_iff`

English:
theorem floor_eq_iff
  given: (ha : 0 <= a)
  statement: ⌊a⌋₊ = n ↔ ↑n <= a ∧ a < ↑n + 1
  proof: by
  rw [← le_floor_iff ha]; rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← floor_lt ha]; rw [Nat.lt_add_one_iff]; rw [le_antisymm_iff]; rw [and_comm]

中文:
定理 floor_eq_iff
  条件: (ha : 0 <= a)
  结论: ⌊a⌋₊ = n ↔ ↑n <= a ∧ a < ↑n + 1
  证明: by
  rw [← le_floor_iff ha]; rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← floor_lt ha]; rw [Nat.lt_add_one_iff]; rw [le_antisymm_iff]; rw [and_comm]

Depends on / 依赖: Nat.cast_add, Nat.cast_one, Nat.lt_add_one_iff, and_comm, cast_add, cast_one, floor_lt, le_antisymm_iff, le_floor_iff, lt_add_one_iff
-/
theorem floor_eq_iff (ha : 0 <= a) : ⌊a⌋₊ = n ↔ ↑n <= a ∧ a < ↑n + 1 := by
  rw [← le_floor_iff ha]; rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← floor_lt ha]; rw [Nat.lt_add_one_iff]; rw [le_antisymm_iff]; rw [and_comm]

/--
theorem `lt_of_floor_lt` / 定理 `lt_of_floor_lt`

English:
theorem lt_of_floor_lt
  given: (h : ⌊a⌋₊ < n)
  statement: a < n
  proof: lt_of_not_ge fun h' => (le_floor h').not_gt h

中文:
定理 lt_of_floor_lt
  条件: (h : ⌊a⌋₊ < n)
  结论: a < n
  证明: lt_of_not_ge fun h' => (le_floor h').not_gt h

Depends on / 依赖: le_floor, lt_of_not_ge, not_gt
-/
theorem lt_of_floor_lt (h : ⌊a⌋₊ < n) : a < n :=
  lt_of_not_ge fun h' => (le_floor h').not_gt h

/--
theorem `lt_one_of_floor_lt_one` / 定理 `lt_one_of_floor_lt_one`

English:
theorem lt_one_of_floor_lt_one
  given: (h : ⌊a⌋₊ < 1)
  statement: a < 1
  proof: mod_cast lt_of_floor_lt h

中文:
定理 lt_one_of_floor_lt_one
  条件: (h : ⌊a⌋₊ < 1)
  结论: a < 1
  证明: mod_cast lt_of_floor_lt h

Depends on / 依赖: lt_of_floor_lt, mod_cast
-/
theorem lt_one_of_floor_lt_one (h : ⌊a⌋₊ < 1) : a < 1 := mod_cast lt_of_floor_lt h

/--
theorem `lt_succ_floor` / 定理 `lt_succ_floor`

English:
theorem lt_succ_floor
  given: (a : R)
  statement: a < ⌊a⌋₊.succ
  proof: lt_of_floor_lt Nat.lt_succ_self _

@[bound]

中文:
定理 lt_succ_floor
  条件: (a : R)
  结论: a < ⌊a⌋₊.succ
  证明: lt_of_floor_lt Nat.lt_succ_self _

@[bound]

Depends on / 依赖: Nat.lt_succ_self, lt_of_floor_lt, lt_succ_self
-/
theorem lt_succ_floor (a : R) : a < ⌊a⌋₊.succ :=
lt_of_floor_lt Nat.lt_succ_self _

@[bound]
/--
theorem `lt_floor_add_one` / 定理 `lt_floor_add_one`

English:
theorem lt_floor_add_one
  given: (a : R)
  statement: a < ⌊a⌋₊ + 1
  proof: by simpa using lt_succ_floor a

中文:
定理 lt_floor_add_one
  条件: (a : R)
  结论: a < ⌊a⌋₊ + 1
  证明: by simpa using lt_succ_floor a

Depends on / 依赖: lt_succ_floor
-/
theorem lt_floor_add_one (a : R) : a < ⌊a⌋₊ + 1 := by simpa using lt_succ_floor a

variable [IsStrictOrderedRing R]

@[simp]
/--
theorem `floor_natCast` / 定理 `floor_natCast`

English:
theorem floor_natCast
  given: (n : Nat)
  statement: ⌊(n : R)⌋₊ = n
  proof: eq_of_forall_le_iff fun a => by
    rw [le_floor_iff]; rw [Nat.cast_le]
    exact n.cast_nonneg

@[simp]

中文:
定理 floor_natCast
  条件: (n : 自然数)
  结论: ⌊(n : R)⌋₊ = n
  证明: eq_of_forall_le_iff fun a => by
    rw [le_floor_iff]; rw [Nat.cast_le]
    exact n.cast_nonneg

@[simp]

Depends on / 依赖: Nat.cast_le, cast_le, cast_nonneg, eq_of_forall_le_iff, le_floor_iff, n.cast_nonneg
-/
theorem floor_natCast (n : Nat) : ⌊(n : R)⌋₊ = n :=
  eq_of_forall_le_iff fun a => by
    rw [le_floor_iff]; rw [Nat.cast_le]
    exact n.cast_nonneg

@[simp]
/--
theorem `floor_zero` / 定理 `floor_zero`

English:
theorem floor_zero
  statement: ⌊(0 : R)⌋₊ = 0
  proof: by rw [← Nat.cast_zero, floor_natCast]

@[simp]

中文:
定理 floor_zero
  结论: ⌊(0 : R)⌋₊ = 0
  证明: by rw [← Nat.cast_zero, floor_natCast]

@[simp]

Depends on / 依赖: Nat.cast_zero, cast_zero, floor_natCast
-/
theorem floor_zero : ⌊(0 : R)⌋₊ = 0 := by rw [← Nat.cast_zero, floor_natCast]

@[simp]
/--
theorem `floor_one` / 定理 `floor_one`

English:
theorem floor_one
  statement: ⌊(1 : R)⌋₊ = 1
  proof: by rw [← Nat.cast_one, floor_natCast]

@[simp]

中文:
定理 floor_one
  结论: ⌊(1 : R)⌋₊ = 1
  证明: by rw [← Nat.cast_one, floor_natCast]

@[simp]

Depends on / 依赖: Nat.cast_one, cast_one, floor_natCast
-/
theorem floor_one : ⌊(1 : R)⌋₊ = 1 := by rw [← Nat.cast_one, floor_natCast]

@[simp]
/--
theorem `floor_ofNat` / 定理 `floor_ofNat`

English:
theorem floor_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ⌊(ofNat(n) : R)⌋₊ = ofNat(n)
  proof: Nat.floor_natCast _

中文:
定理 floor_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: ⌊(of自然数(n) : R)⌋₊ = of自然数(n)
  证明: Nat.floor_natCast _

Depends on / 依赖: Nat.floor_natCast, floor_natCast
-/
theorem floor_ofNat (n : Nat) [n.AtLeastTwo] : ⌊(ofNat(n) : R)⌋₊ = ofNat(n) :=
  Nat.floor_natCast _

/--
theorem `floor_of_nonpos` / 定理 `floor_of_nonpos`

English:
theorem floor_of_nonpos
  given: (ha : a <= 0)
  statement: ⌊a⌋₊ = 0
  proof: ha.lt_or_eq.elim FloorSemiring.floor_of_neg by
    rintro rfl
    exact floor_zero

@[gcongr]

中文:
定理 floor_of_nonpos
  条件: (ha : a <= 0)
  结论: ⌊a⌋₊ = 0
  证明: ha.lt_or_eq.elim FloorSemiring.floor_of_neg by
    rintro rfl
    exact floor_zero

@[gcongr]

Depends on / 依赖: FloorSemiring, FloorSemiring.floor_of_neg, floor_of_neg, floor_zero, ha.lt_or_eq.elim, lt_or_eq
-/
theorem floor_of_nonpos (ha : a <= 0) : ⌊a⌋₊ = 0 :=
ha.lt_or_eq.elim FloorSemiring.floor_of_neg by
    rintro rfl
    exact floor_zero

@[gcongr]
/--
theorem `floor_mono` / 定理 `floor_mono`

English:
theorem floor_mono
  statement: Monotone (floor : R -> Nat)
  proof: fun a b h => by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact Nat.zero_le _
  · exact le_floor ((floor_le ha).trans h)

中文:
定理 floor_mono
  结论: Monotone (floor : R -> 自然数)
  证明: fun a b h => by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact Nat.zero_le _
  · exact le_floor ((floor_le ha).trans h)

Depends on / 依赖: Nat.zero_le, floor_le, floor_of_nonpos, le_floor, le_total, zero_le
-/
theorem floor_mono : Monotone (floor : R -> Nat) := fun a b h => by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact Nat.zero_le _
  · exact le_floor ((floor_le ha).trans h)

/--
lemma `floor_le_floor` / 引理 `floor_le_floor`

English:
lemma floor_le_floor
  given: (hab : a <= b)
  statement: ⌊a⌋₊ <= ⌊b⌋₊
  proof: floor_mono hab

中文:
引理 floor_le_floor
  条件: (hab : a <= b)
  结论: ⌊a⌋₊ <= ⌊b⌋₊
  证明: floor_mono hab
-/
@[bound] lemma floor_le_floor (hab : a <= b) : ⌊a⌋₊ <= ⌊b⌋₊ := floor_mono hab

/--
theorem `le_floor_iff'` / 定理 `le_floor_iff'`

English:
theorem le_floor_iff'
  given: (hn : n != 0)
  statement: n <= ⌊a⌋₊ ↔ (n : R) <= a
  proof: by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact
      iff_of_false (Nat.pos_of_ne_zero hn).not_ge
        (not_le_of_gt <| ha.trans_lt <| cast_pos.2 <| Nat.pos_of_ne_zero hn)
  · exact le_floor_iff ha

@[simp]

中文:
定理 le_floor_iff'
  条件: (hn : n != 0)
  结论: n <= ⌊a⌋₊ ↔ (n : R) <= a
  证明: by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact
      iff_of_false (Nat.pos_of_ne_zero hn).not_ge
        (not_le_of_gt <| ha.trans_lt <| cast_pos.2 <| Nat.pos_of_ne_zero hn)
  · exact le_floor_iff ha

@[simp]

Depends on / 依赖: Nat.pos_of_ne_zero, cast_pos, floor_of_nonpos, ha.trans_lt, iff_of_false, le_floor_iff, le_total, not_ge, not_le_of_gt, pos_of_ne_zero, trans_lt
-/
theorem le_floor_iff' (hn : n != 0) : n <= ⌊a⌋₊ ↔ (n : R) <= a := by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact
      iff_of_false (Nat.pos_of_ne_zero hn).not_ge
        (not_le_of_gt <| ha.trans_lt <| cast_pos.2 <| Nat.pos_of_ne_zero hn)
  · exact le_floor_iff ha

@[simp]
/--
theorem `one_le_floor_iff` / 定理 `one_le_floor_iff`

English:
theorem one_le_floor_iff
  given: (x : R)
  statement: 1 <= ⌊x⌋₊ ↔ 1 <= x
  proof: mod_cast le_floor_iff' one_ne_zero

中文:
定理 one_le_floor_iff
  条件: (x : R)
  结论: 1 <= ⌊x⌋₊ ↔ 1 <= x
  证明: mod_cast le_floor_iff' one_ne_zero

Depends on / 依赖: le_floor_iff, mod_cast, one_ne_zero
-/
theorem one_le_floor_iff (x : R) : 1 <= ⌊x⌋₊ ↔ 1 <= x :=
  mod_cast le_floor_iff' one_ne_zero

/--
theorem `floor_lt'` / 定理 `floor_lt'`

English:
theorem floor_lt'
  given: (hn : n != 0)
  statement: ⌊a⌋₊ < n ↔ a < n
  proof: lt_iff_lt_of_le_iff_le le_floor_iff' hn

中文:
定理 floor_lt'
  条件: (hn : n != 0)
  结论: ⌊a⌋₊ < n ↔ a < n
  证明: lt_iff_lt_of_le_iff_le le_floor_iff' hn

Depends on / 依赖: le_floor_iff, lt_iff_lt_of_le_iff_le
-/
theorem floor_lt' (hn : n != 0) : ⌊a⌋₊ < n ↔ a < n :=
lt_iff_lt_of_le_iff_le le_floor_iff' hn

/--
theorem `floor_pos` / 定理 `floor_pos`

English:
theorem floor_pos
  statement: 0 < ⌊a⌋₊ ↔ 1 <= a
  proof: by
  rw [Nat.lt_iff_add_one_le]; rw [zero_add]; rw [le_floor_iff' Nat.one_ne_zero]; rw [cast_one]

中文:
定理 floor_pos
  结论: 0 < ⌊a⌋₊ ↔ 1 <= a
  证明: by
  rw [Nat.lt_iff_add_one_le]; rw [zero_add]; rw [le_floor_iff' Nat.one_ne_zero]; rw [cast_one]

Depends on / 依赖: Nat.lt_iff_add_one_le, Nat.one_ne_zero, cast_one, le_floor_iff, lt_iff_add_one_le, one_ne_zero, zero_add
-/
theorem floor_pos : 0 < ⌊a⌋₊ ↔ 1 <= a := by
  rw [Nat.lt_iff_add_one_le]; rw [zero_add]; rw [le_floor_iff' Nat.one_ne_zero]; rw [cast_one]

/--
theorem `pos_of_floor_pos` / 定理 `pos_of_floor_pos`

English:
theorem pos_of_floor_pos
  given: (h : 0 < ⌊a⌋₊)
  statement: 0 < a
  proof: (le_or_gt a 0).resolve_left fun ha => lt_irrefl 0 by rwa [floor_of_nonpos ha] at h

中文:
定理 pos_of_floor_pos
  条件: (h : 0 < ⌊a⌋₊)
  结论: 0 < a
  证明: (le_or_gt a 0).resolve_left fun ha => lt_irrefl 0 by rwa [floor_of_nonpos ha] at h

Depends on / 依赖: floor_of_nonpos, le_or_gt, lt_irrefl, resolve_left
-/
theorem pos_of_floor_pos (h : 0 < ⌊a⌋₊) : 0 < a :=
(le_or_gt a 0).resolve_left fun ha => lt_irrefl 0 by rwa [floor_of_nonpos ha] at h

/--
theorem `lt_of_lt_floor` / 定理 `lt_of_lt_floor`

English:
theorem lt_of_lt_floor
  given: (h : n < ⌊a⌋₊)
  statement: ↑n < a
  proof: (Nat.cast_lt.2 h).trans_le floor_le (pos_of_floor_pos <| (Nat.zero_le n).trans_lt h).le

中文:
定理 lt_of_lt_floor
  条件: (h : n < ⌊a⌋₊)
  结论: ↑n < a
  证明: (Nat.cast_lt.2 h).trans_le floor_le (pos_of_floor_pos <| (Nat.zero_le n).trans_lt h).le

Depends on / 依赖: Nat.cast_lt, Nat.zero_le, cast_lt, floor_le, pos_of_floor_pos, trans_le, trans_lt, zero_le
-/
theorem lt_of_lt_floor (h : n < ⌊a⌋₊) : ↑n < a :=
(Nat.cast_lt.2 h).trans_le floor_le (pos_of_floor_pos <| (Nat.zero_le n).trans_lt h).le

/--
theorem `floor_le_of_le` / 定理 `floor_le_of_le`

English:
theorem floor_le_of_le
  given: (h : a <= n)
  statement: ⌊a⌋₊ <= n
  proof: le_imp_le_iff_lt_imp_lt.2 lt_of_lt_floor h

中文:
定理 floor_le_of_le
  条件: (h : a <= n)
  结论: ⌊a⌋₊ <= n
  证明: le_imp_le_iff_lt_imp_lt.2 lt_of_lt_floor h

Depends on / 依赖: le_imp_le_iff_lt_imp_lt, lt_of_lt_floor
-/
theorem floor_le_of_le (h : a <= n) : ⌊a⌋₊ <= n :=
  le_imp_le_iff_lt_imp_lt.2 lt_of_lt_floor h

/--
theorem `floor_le_one_of_le_one` / 定理 `floor_le_one_of_le_one`

English:
theorem floor_le_one_of_le_one
  given: (h : a <= 1)
  statement: ⌊a⌋₊ <= 1
  proof: floor_le_of_le h.trans_eq Nat.cast_one.symm

@[simp]

中文:
定理 floor_le_one_of_le_one
  条件: (h : a <= 1)
  结论: ⌊a⌋₊ <= 1
  证明: floor_le_of_le h.trans_eq Nat.cast_one.symm

@[simp]

Depends on / 依赖: Nat.cast_one.symm, cast_one, floor_le_of_le, h.trans_eq, trans_eq
-/
theorem floor_le_one_of_le_one (h : a <= 1) : ⌊a⌋₊ <= 1 :=
floor_le_of_le h.trans_eq Nat.cast_one.symm

@[simp]
/--
theorem `floor_eq_zero` / 定理 `floor_eq_zero`

English:
theorem floor_eq_zero
  statement: ⌊a⌋₊ = 0 ↔ a < 1
  proof: by
  rw [← lt_one_iff]; rw [← @cast_one R]
  exact floor_lt' Nat.one_ne_zero

中文:
定理 floor_eq_zero
  结论: ⌊a⌋₊ = 0 ↔ a < 1
  证明: by
  rw [← lt_one_iff]; rw [← @cast_one R]
  exact floor_lt' Nat.one_ne_zero

Depends on / 依赖: Nat.one_ne_zero, cast_one, e.symm, floor_lt, lt_one_iff, one_ne_zero
-/
theorem floor_eq_zero : ⌊a⌋₊ = 0 ↔ a < 1 := by
  rw [← lt_one_iff]; rw [← @cast_one R]
  exact floor_lt' Nat.one_ne_zero

/--
theorem `floor_eq_iff'` / 定理 `floor_eq_iff'`

English:
theorem floor_eq_iff'
  given: (hn : n != 0)
  statement: ⌊a⌋₊ = n ↔ ↑n <= a ∧ a < ↑n + 1
  proof: by
  rw [← le_floor_iff' hn]; rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← floor_lt' (Nat.add_one_ne_zero n)]; rw [Nat.lt_add_one_iff]; rw [le_antisymm_iff]; rw [and_comm]

中文:
定理 floor_eq_iff'
  条件: (hn : n != 0)
  结论: ⌊a⌋₊ = n ↔ ↑n <= a ∧ a < ↑n + 1
  证明: by
  rw [← le_floor_iff' hn]; rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← floor_lt' (Nat.add_one_ne_zero n)]; rw [Nat.lt_add_one_iff]; rw [le_antisymm_iff]; rw [and_comm]

Depends on / 依赖: Nat.add_one_ne_zero, Nat.cast_add, Nat.cast_one, Nat.lt_add_one_iff, add_one_ne_zero, and_comm, cast_add, cast_one, floor_lt, le_antisymm_iff, le_floor_iff, lt_add_one_iff
-/
theorem floor_eq_iff' (hn : n != 0) : ⌊a⌋₊ = n ↔ ↑n <= a ∧ a < ↑n + 1 := by
  rw [← le_floor_iff' hn]; rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← floor_lt' (Nat.add_one_ne_zero n)]; rw [Nat.lt_add_one_iff]; rw [le_antisymm_iff]; rw [and_comm]

/--
theorem `floor_eq_on_Ico` / 定理 `floor_eq_on_Ico`

English:
theorem floor_eq_on_Ico
  given: (n : Nat)
  statement: forall a in (Set.Ico n (n + 1) : Set R), ⌊a⌋₊ = n
  proof: fun _ ⟨h₀, h₁⟩ =>
  (floor_eq_iff <| n.cast_nonneg.trans h₀).mpr ⟨h₀, h₁⟩

中文:
定理 floor_eq_on_Ico
  条件: (n : 自然数)
  结论: 对任意 a in (Set.Ico n (n + 1) : Set R), ⌊a⌋₊ = n
  证明: fun _ ⟨h₀, h₁⟩ =>
  (floor_eq_iff <| n.cast_nonneg.trans h₀).mpr ⟨h₀, h₁⟩
-/
theorem floor_eq_on_Ico (n : Nat) : forall a in (Set.Ico n (n + 1) : Set R), ⌊a⌋₊ = n := fun _ ⟨h₀, h₁⟩ =>
  (floor_eq_iff <| n.cast_nonneg.trans h₀).mpr ⟨h₀, h₁⟩

/--
theorem `floor_eq_on_Ico'` / 定理 `floor_eq_on_Ico'`

English:
theorem floor_eq_on_Ico'
  given: (n : Nat)
  proof: fun x hx => mod_cast floor_eq_on_Ico n x hx

@[simp]

中文:
定理 floor_eq_on_Ico'
  条件: (n : 自然数)
  证明: fun x hx => mod_cast floor_eq_on_Ico n x hx

@[simp]

Depends on / 依赖: floor_eq_on_Ico, mod_cast
-/
theorem floor_eq_on_Ico' (n : Nat) :
    forall a in (Set.Ico n (n + 1) : Set R), (⌊a⌋₊ : R) = n :=
  fun x hx => mod_cast floor_eq_on_Ico n x hx

@[simp]
/--
theorem `preimage_floor_zero` / 定理 `preimage_floor_zero`

English:
theorem preimage_floor_zero
  statement: (floor : R -> Nat) ⁻¹' {0} = Iio 1
  proof: ext fun _ => floor_eq_zero

中文:
定理 preimage_floor_zero
  结论: (floor : R -> 自然数) ⁻¹' {0} = Iio 1
  证明: ext fun _ => floor_eq_zero

Depends on / 依赖: floor_eq_zero
-/
theorem preimage_floor_zero : (floor : R -> Nat) ⁻¹' {0} = Iio 1 :=
  ext fun _ => floor_eq_zero

/--
theorem `preimage_floor_of_ne_zero` / 定理 `preimage_floor_of_ne_zero`

English:
theorem preimage_floor_of_ne_zero
  given: {n : Nat} (hn : n != 0)
  proof: ext fun _ => floor_eq_iff' hn

中文:
定理 preimage_floor_of_ne_zero
  条件: {n : 自然数} (hn : n != 0)
  证明: ext fun _ => floor_eq_iff' hn

Depends on / 依赖: floor_eq_iff
-/
theorem preimage_floor_of_ne_zero {n : Nat} (hn : n != 0) :
    (floor : R -> Nat) ⁻¹' {n} = Ico (n : R) (n + 1) :=
  ext fun _ => floor_eq_iff' hn

/--
theorem `mul_cast_floor_div_cancel` / 定理 `mul_cast_floor_div_cancel`

English:
theorem mul_cast_floor_div_cancel
  given: {n : Nat} (hn : n != 0) (a : R)
  statement: ⌊a * n⌋₊ / n = ⌊a⌋₊
  proof: by
  rcases le_total a 0 with ha | ha
  · rw [floor_of_nonpos, floor_of_nonpos ha]
    · simp
    apply mul_nonpos_of_nonpos_of_nonneg ha n.cast_nonneg
  refine eq_of_forall_le_iff fun m => ?_
  rw [le_div_iff_mul_le (zero_lt_of_ne_zero hn)]; rw [le_floor_iff (mul_nonneg ha (cast_nonneg' n))]; rw [l

中文:
定理 mul_cast_floor_div_cancel
  条件: {n : 自然数} (hn : n != 0) (a : R)
  结论: ⌊a * n⌋₊ / n = ⌊a⌋₊
  证明: by
  rcases le_total a 0 with ha | ha
  · rw [floor_of_nonpos, floor_of_nonpos ha]
    · simp
    apply mul_nonpos_of_nonpos_of_nonneg ha n.cast_nonneg
  refine eq_of_forall_le_iff fun m => ?_
  rw [le_div_iff_mul_le (zero_lt_of_ne_zero hn)]; rw [le_floor_iff (mul_nonneg ha (cast_nonneg' n))]; rw [l

Depends on / 依赖: cast_mul, cast_nonneg, cast_pos, eq_of_forall_le_iff, floor_of_nonpos, le_div_iff_mul_le, le_floor_iff, le_total, mul_le_mul_iff_of_pos_right, mul_nonneg, mul_nonpos_of_nonpos_of_nonneg, n.cast_nonneg, zero_lt_of_ne_zero
-/
theorem mul_cast_floor_div_cancel {n : Nat} (hn : n != 0) (a : R) : ⌊a * n⌋₊ / n = ⌊a⌋₊ := by
  rcases le_total a 0 with ha | ha
  · rw [floor_of_nonpos, floor_of_nonpos ha]
    · simp
    apply mul_nonpos_of_nonpos_of_nonneg ha n.cast_nonneg
  refine eq_of_forall_le_iff fun m => ?_
  rw [le_div_iff_mul_le (zero_lt_of_ne_zero hn)]; rw [le_floor_iff (mul_nonneg ha (cast_nonneg' n))]; rw [le_floor_iff ha]; rw [cast_mul]; rw [mul_le_mul_iff_of_pos_right (cast_pos'.mpr (zero_lt_of_ne_zero hn))]

/--
theorem `cast_mul_floor_div_cancel` / 定理 `cast_mul_floor_div_cancel`

English:
theorem cast_mul_floor_div_cancel
  given: {n : Nat} (hn : n != 0) (a : R)
  proof: by
  rw [Nat.cast_comm]; rw [mul_cast_floor_div_cancel hn]

中文:
定理 cast_mul_floor_div_cancel
  条件: {n : 自然数} (hn : n != 0) (a : R)
  证明: by
  rw [Nat.cast_comm]; rw [mul_cast_floor_div_cancel hn]

Depends on / 依赖: Nat.cast_comm, cast_comm, mul_cast_floor_div_cancel
-/
theorem cast_mul_floor_div_cancel {n : Nat} (hn : n != 0) (a : R) :
    ⌊n * a⌋₊ / n = ⌊a⌋₊ := by
  rw [Nat.cast_comm]; rw [mul_cast_floor_div_cancel hn]

end floor

/-! #### Ceil -/

section ceil

/--
theorem `add_one_le_ceil_iff` / 定理 `add_one_le_ceil_iff`

English:
theorem add_one_le_ceil_iff
  statement: n + 1 <= ⌈a⌉₊ ↔ (n : R) < a
  proof: by
  rw [← Nat.lt_ceil]; rw [Nat.add_one_le_iff]

@[simp]

中文:
定理 add_one_le_ceil_iff
  结论: n + 1 <= ⌈a⌉₊ ↔ (n : R) < a
  证明: by
  rw [← Nat.lt_ceil]; rw [Nat.add_one_le_iff]

@[simp]

Depends on / 依赖: Nat.add_one_le_iff, Nat.lt_ceil, add_one_le_iff, lt_ceil
-/
theorem add_one_le_ceil_iff : n + 1 <= ⌈a⌉₊ ↔ (n : R) < a := by
  rw [← Nat.lt_ceil]; rw [Nat.add_one_le_iff]

@[simp]
/--
theorem `one_le_ceil_iff` / 定理 `one_le_ceil_iff`

English:
theorem one_le_ceil_iff
  statement: 1 <= ⌈a⌉₊ ↔ 0 < a
  proof: by
  rw [← zero_add 1]; rw [Nat.add_one_le_ceil_iff]; rw [Nat.cast_zero]

@[bound]

中文:
定理 one_le_ceil_iff
  结论: 1 <= ⌈a⌉₊ ↔ 0 < a
  证明: by
  rw [← zero_add 1]; rw [Nat.add_one_le_ceil_iff]; rw [Nat.cast_zero]

@[bound]

Depends on / 依赖: Nat.add_one_le_ceil_iff, Nat.cast_zero, add_one_le_ceil_iff, cast_zero, zero_add
-/
theorem one_le_ceil_iff : 1 <= ⌈a⌉₊ ↔ 0 < a := by
  rw [← zero_add 1]; rw [Nat.add_one_le_ceil_iff]; rw [Nat.cast_zero]

@[bound]
/--
theorem `le_ceil` / 定理 `le_ceil`

English:
theorem le_ceil
  given: (a : R)
  statement: a <= ⌈a⌉₊
  proof: ceil_le.1 le_rfl

中文:
定理 le_ceil
  条件: (a : R)
  结论: a <= ⌈a⌉₊
  证明: ceil_le.1 le_rfl

Depends on / 依赖: ceil_le, le_rfl
-/
theorem le_ceil (a : R) : a <= ⌈a⌉₊ :=
  ceil_le.1 le_rfl

/--
theorem `ceil_mono` / 定理 `ceil_mono`

English:
theorem ceil_mono
  statement: Monotone (ceil : R -> Nat)
  proof: gc_ceil_coe.monotone_l

中文:
定理 ceil_mono
  结论: Monotone (ceil : R -> 自然数)
  证明: gc_ceil_coe.monotone_l

Depends on / 依赖: gc_ceil_coe, gc_ceil_coe.monotone_l, monotone_l
-/
theorem ceil_mono : Monotone (ceil : R -> Nat) :=
  gc_ceil_coe.monotone_l

/--
lemma `ceil_le_ceil` / 引理 `ceil_le_ceil`

English:
lemma ceil_le_ceil
  given: (hab : a <= b)
  statement: ⌈a⌉₊ <= ⌈b⌉₊
  proof: ceil_mono hab

@[simp]

中文:
引理 ceil_le_ceil
  条件: (hab : a <= b)
  结论: ⌈a⌉₊ <= ⌈b⌉₊
  证明: ceil_mono hab

@[simp]
-/
@[gcongr, bound] lemma ceil_le_ceil (hab : a <= b) : ⌈a⌉₊ <= ⌈b⌉₊ := ceil_mono hab

@[simp]
/--
theorem `ceil_eq_zero` / 定理 `ceil_eq_zero`

English:
theorem ceil_eq_zero
  statement: ⌈a⌉₊ = 0 ↔ a <= 0
  proof: by rw [← Nat.le_zero, ceil_le, Nat.cast_zero]

中文:
定理 ceil_eq_zero
  结论: ⌈a⌉₊ = 0 ↔ a <= 0
  证明: by rw [← Nat.le_zero, ceil_le, Nat.cast_zero]

Depends on / 依赖: Nat.cast_zero, Nat.le_zero, cast_zero, ceil_le, le_zero
-/
theorem ceil_eq_zero : ⌈a⌉₊ = 0 ↔ a <= 0 := by rw [← Nat.le_zero, ceil_le, Nat.cast_zero]

/--
theorem `ceil_eq_iff` / 定理 `ceil_eq_iff`

English:
theorem ceil_eq_iff
  given: (hn : n != 0)
  statement: ⌈a⌉₊ = n ↔ ↑(n - 1) < a ∧ a <= n
  proof: by
  rw [← ceil_le]; rw [← not_le]; rw [← ceil_le]; rw [not_le]; rw [tsub_lt_iff_right (Nat.add_one_le_iff.2 (pos_iff_ne_zero.2 hn))]; rw [Nat.lt_add_one_iff]; rw [le_antisymm_iff]; rw [and_comm]

@[simp]

中文:
定理 ceil_eq_iff
  条件: (hn : n != 0)
  结论: ⌈a⌉₊ = n ↔ ↑(n - 1) < a ∧ a <= n
  证明: by
  rw [← ceil_le]; rw [← not_le]; rw [← ceil_le]; rw [not_le]; rw [tsub_lt_iff_right (Nat.add_one_le_iff.2 (pos_iff_ne_zero.2 hn))]; rw [Nat.lt_add_one_iff]; rw [le_antisymm_iff]; rw [and_comm]

@[simp]

Depends on / 依赖: Nat.add_one_le_iff, Nat.lt_add_one_iff, add_one_le_iff, and_comm, ceil_le, le_antisymm_iff, lt_add_one_iff, not_le, pos_iff_ne_zero, tsub_lt_iff_right
-/
theorem ceil_eq_iff (hn : n != 0) : ⌈a⌉₊ = n ↔ ↑(n - 1) < a ∧ a <= n := by
  rw [← ceil_le]; rw [← not_le]; rw [← ceil_le]; rw [not_le]; rw [tsub_lt_iff_right (Nat.add_one_le_iff.2 (pos_iff_ne_zero.2 hn))]; rw [Nat.lt_add_one_iff]; rw [le_antisymm_iff]; rw [and_comm]

@[simp]
/--
theorem `preimage_ceil_zero` / 定理 `preimage_ceil_zero`

English:
theorem preimage_ceil_zero
  statement: (Nat.ceil : R -> Nat) ⁻¹' {0} = Iic 0
  proof: ext fun _ => ceil_eq_zero

中文:
定理 preimage_ceil_zero
  结论: (自然数.ceil : R -> 自然数) ⁻¹' {0} = Iic 0
  证明: ext fun _ => ceil_eq_zero

Depends on / 依赖: ceil_eq_zero
-/
theorem preimage_ceil_zero : (Nat.ceil : R -> Nat) ⁻¹' {0} = Iic 0 :=
  ext fun _ => ceil_eq_zero

/--
theorem `preimage_ceil_of_ne_zero` / 定理 `preimage_ceil_of_ne_zero`

English:
theorem preimage_ceil_of_ne_zero
  given: (hn : n != 0)
  statement: (Nat.ceil : R -> Nat) ⁻¹' {n} = Ioc (↑(n - 1) : R) n
  proof: ext fun _ => ceil_eq_iff hn

@[bound]

中文:
定理 preimage_ceil_of_ne_zero
  条件: (hn : n != 0)
  结论: (自然数.ceil : R -> 自然数) ⁻¹' {n} = Ioc (↑(n - 1) : R) n
  证明: ext fun _ => ceil_eq_iff hn

@[bound]

Depends on / 依赖: ceil_eq_iff
-/
theorem preimage_ceil_of_ne_zero (hn : n != 0) : (Nat.ceil : R -> Nat) ⁻¹' {n} = Ioc (↑(n - 1) : R) n :=
  ext fun _ => ceil_eq_iff hn

@[bound]
/--
theorem `ceil_le_floor_add_one` / 定理 `ceil_le_floor_add_one`

English:
theorem ceil_le_floor_add_one
  given: (a : R)
  statement: ⌈a⌉₊ <= ⌊a⌋₊ + 1
  proof: by
  rw [ceil_le]; rw [Nat.cast_add]; rw [Nat.cast_one]
  exact (lt_floor_add_one a).le

@[simp]

中文:
定理 ceil_le_floor_add_one
  条件: (a : R)
  结论: ⌈a⌉₊ <= ⌊a⌋₊ + 1
  证明: by
  rw [ceil_le]; rw [Nat.cast_add]; rw [Nat.cast_one]
  exact (lt_floor_add_one a).le

@[simp]

Depends on / 依赖: Nat.cast_add, Nat.cast_one, cast_add, cast_one, ceil_le, lt_floor_add_one
-/
theorem ceil_le_floor_add_one (a : R) : ⌈a⌉₊ <= ⌊a⌋₊ + 1 := by
  rw [ceil_le]; rw [Nat.cast_add]; rw [Nat.cast_one]
  exact (lt_floor_add_one a).le

@[simp]
/--
theorem `ceil_intCast` / 定理 `ceil_intCast`

English:
theorem ceil_intCast
  statement: {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
  proof: eq_of_forall_ge_iff fun a => by
    simp only [ceil_le, Int.toNat_le]
    norm_cast

中文:
定理 ceil_intCast
  结论: {R : 类型} [Ring R] [LinearOrder R] [IsOrderedRing R]
  证明: eq_of_forall_ge_iff fun a => by
    simp only [ceil_le, Int.toNat_le]
    norm_cast

Depends on / 依赖: Int.toNat_le, ceil_le, eq_of_forall_ge_iff, toNat_le
-/
theorem ceil_intCast {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
    [FloorSemiring R] (z : Int) :
    ⌈(z : R)⌉₊ = z.toNat :=
  eq_of_forall_ge_iff fun a => by
    simp only [ceil_le, Int.toNat_le]
    norm_cast

variable [IsStrictOrderedRing R]

@[simp]
/--
theorem `ceil_natCast` / 定理 `ceil_natCast`

English:
theorem ceil_natCast
  given: (n : Nat)
  statement: ⌈(n : R)⌉₊ = n
  proof: eq_of_forall_ge_iff fun a => by rw [ceil_le, cast_le]

@[simp]

中文:
定理 ceil_natCast
  条件: (n : 自然数)
  结论: ⌈(n : R)⌉₊ = n
  证明: eq_of_forall_ge_iff fun a => by rw [ceil_le, cast_le]

@[simp]

Depends on / 依赖: cast_le, ceil_le, eq_of_forall_ge_iff
-/
theorem ceil_natCast (n : Nat) : ⌈(n : R)⌉₊ = n :=
  eq_of_forall_ge_iff fun a => by rw [ceil_le, cast_le]

@[simp]
/--
theorem `ceil_zero` / 定理 `ceil_zero`

English:
theorem ceil_zero
  statement: ⌈(0 : R)⌉₊ = 0
  proof: by rw [← Nat.cast_zero, ceil_natCast]

@[simp]

中文:
定理 ceil_zero
  结论: ⌈(0 : R)⌉₊ = 0
  证明: by rw [← Nat.cast_zero, ceil_natCast]

@[simp]

Depends on / 依赖: Nat.cast_zero, cast_zero, ceil_natCast
-/
theorem ceil_zero : ⌈(0 : R)⌉₊ = 0 := by rw [← Nat.cast_zero, ceil_natCast]

@[simp]
/--
theorem `ceil_one` / 定理 `ceil_one`

English:
theorem ceil_one
  statement: ⌈(1 : R)⌉₊ = 1
  proof: by rw [← Nat.cast_one, ceil_natCast]

@[simp]

中文:
定理 ceil_one
  结论: ⌈(1 : R)⌉₊ = 1
  证明: by rw [← Nat.cast_one, ceil_natCast]

@[simp]

Depends on / 依赖: Nat.cast_one, cast_one, ceil_natCast
-/
theorem ceil_one : ⌈(1 : R)⌉₊ = 1 := by rw [← Nat.cast_one, ceil_natCast]

@[simp]
/--
theorem `ceil_ofNat` / 定理 `ceil_ofNat`

English:
theorem ceil_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ⌈(ofNat(n) : R)⌉₊ = ofNat(n)
  proof: ceil_natCast n

中文:
定理 ceil_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: ⌈(of自然数(n) : R)⌉₊ = of自然数(n)
  证明: ceil_natCast n

Depends on / 依赖: ceil_natCast
-/
theorem ceil_ofNat (n : Nat) [n.AtLeastTwo] : ⌈(ofNat(n) : R)⌉₊ = ofNat(n) := ceil_natCast n

/--
theorem `lt_of_ceil_lt` / 定理 `lt_of_ceil_lt`

English:
theorem lt_of_ceil_lt
  given: (h : ⌈a⌉₊ < n)
  statement: a < n
  proof: (le_ceil a).trans_lt (Nat.cast_lt.2 h)

中文:
定理 lt_of_ceil_lt
  条件: (h : ⌈a⌉₊ < n)
  结论: a < n
  证明: (le_ceil a).trans_lt (Nat.cast_lt.2 h)

Depends on / 依赖: Nat.cast_lt, cast_lt, le_ceil, trans_lt
-/
theorem lt_of_ceil_lt (h : ⌈a⌉₊ < n) : a < n :=
  (le_ceil a).trans_lt (Nat.cast_lt.2 h)

/--
theorem `le_of_ceil_le` / 定理 `le_of_ceil_le`

English:
theorem le_of_ceil_le
  given: (h : ⌈a⌉₊ <= n)
  statement: a <= n
  proof: (le_ceil a).trans (Nat.cast_le.2 h)

@[bound]

中文:
定理 le_of_ceil_le
  条件: (h : ⌈a⌉₊ <= n)
  结论: a <= n
  证明: (le_ceil a).trans (Nat.cast_le.2 h)

@[bound]

Depends on / 依赖: Nat.cast_le, cast_le, le_ceil
-/
theorem le_of_ceil_le (h : ⌈a⌉₊ <= n) : a <= n :=
  (le_ceil a).trans (Nat.cast_le.2 h)

@[bound]
/--
theorem `floor_le_ceil` / 定理 `floor_le_ceil`

English:
theorem floor_le_ceil
  given: (a : R)
  statement: ⌊a⌋₊ <= ⌈a⌉₊
  proof: by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact Nat.zero_le _
  · exact cast_le.1 ((floor_le ha).trans <| le_ceil _)

中文:
定理 floor_le_ceil
  条件: (a : R)
  结论: ⌊a⌋₊ <= ⌈a⌉₊
  证明: by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact Nat.zero_le _
  · exact cast_le.1 ((floor_le ha).trans <| le_ceil _)

Depends on / 依赖: Nat.zero_le, cast_le, floor_le, floor_of_nonpos, le_ceil, le_total, zero_le
-/
theorem floor_le_ceil (a : R) : ⌊a⌋₊ <= ⌈a⌉₊ := by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact Nat.zero_le _
  · exact cast_le.1 ((floor_le ha).trans <| le_ceil _)

/--
theorem `floor_lt_ceil_of_lt_of_pos` / 定理 `floor_lt_ceil_of_lt_of_pos`

English:
theorem floor_lt_ceil_of_lt_of_pos
  given: {a b : R} (h : a < b) (h' : 0 < b)
  statement: ⌊a⌋₊ < ⌈b⌉₊
  proof: by
  rcases le_or_gt 0 a with (ha | ha)
  · rw [floor_lt ha]
    exact h.trans_le (le_ceil _)
  · rwa [floor_of_nonpos ha.le, lt_ceil, Nat.cast_zero]

中文:
定理 floor_lt_ceil_of_lt_of_pos
  条件: {a b : R} (h : a < b) (h' : 0 < b)
  结论: ⌊a⌋₊ < ⌈b⌉₊
  证明: by
  rcases le_or_gt 0 a with (ha | ha)
  · rw [floor_lt ha]
    exact h.trans_le (le_ceil _)
  · rwa [floor_of_nonpos ha.le, lt_ceil, Nat.cast_zero]

Depends on / 依赖: Nat.cast_zero, cast_zero, floor_lt, floor_of_nonpos, h.trans_le, ha.le, le_ceil, le_or_gt, lt_ceil, trans_le
-/
theorem floor_lt_ceil_of_lt_of_pos {a b : R} (h : a < b) (h' : 0 < b) : ⌊a⌋₊ < ⌈b⌉₊ := by
  rcases le_or_gt 0 a with (ha | ha)
  · rw [floor_lt ha]
    exact h.trans_le (le_ceil _)
  · rwa [floor_of_nonpos ha.le, lt_ceil, Nat.cast_zero]

end ceil

/-! #### Intervals -/

@[simp]
/--
theorem `preimage_Ioo` / 定理 `preimage_Ioo`

English:
theorem preimage_Ioo
  given: {a b : R} (ha : 0 <= a)
  proof: by
  ext
  simp [floor_lt, lt_ceil, ha]

@[simp]

中文:
定理 preimage_Ioo
  条件: {a b : R} (ha : 0 <= a)
  证明: by
  ext
  simp [floor_lt, lt_ceil, ha]

@[simp]

Depends on / 依赖: floor_lt, lt_ceil
-/
theorem preimage_Ioo {a b : R} (ha : 0 <= a) :
    (Nat.cast : Nat -> R) ⁻¹' Set.Ioo a b = Set.Ioo ⌊a⌋₊ ⌈b⌉₊ := by
  ext
  simp [floor_lt, lt_ceil, ha]

@[simp]
/--
theorem `preimage_Ico` / 定理 `preimage_Ico`

English:
theorem preimage_Ico
  given: {a b : R}
  statement: (Nat.cast : Nat -> R) ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉₊ ⌈b⌉₊
  proof: by
  ext
  simp [ceil_le, lt_ceil]

@[simp]

中文:
定理 preimage_Ico
  条件: {a b : R}
  结论: (自然数.cast : 自然数 -> R) ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉₊ ⌈b⌉₊
  证明: by
  ext
  simp [ceil_le, lt_ceil]

@[simp]

Depends on / 依赖: ceil_le, lt_ceil
-/
theorem preimage_Ico {a b : R} : (Nat.cast : Nat -> R) ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉₊ ⌈b⌉₊ := by
  ext
  simp [ceil_le, lt_ceil]

@[simp]
/--
theorem `preimage_Ioc` / 定理 `preimage_Ioc`

English:
theorem preimage_Ioc
  given: {a b : R} (ha : 0 <= a) (hb : 0 <= b)
  proof: by
  ext
  simp [floor_lt, le_floor_iff, hb, ha]

@[simp]

中文:
定理 preimage_Ioc
  条件: {a b : R} (ha : 0 <= a) (hb : 0 <= b)
  证明: by
  ext
  simp [floor_lt, le_floor_iff, hb, ha]

@[simp]

Depends on / 依赖: floor_lt, le_floor_iff
-/
theorem preimage_Ioc {a b : R} (ha : 0 <= a) (hb : 0 <= b) :
    (Nat.cast : Nat -> R) ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
  ext
  simp [floor_lt, le_floor_iff, hb, ha]

@[simp]
/--
theorem `preimage_Icc` / 定理 `preimage_Icc`

English:
theorem preimage_Icc
  given: {a b : R} (hb : 0 <= b)
  proof: by
  ext
  simp [ceil_le, hb, le_floor_iff]

@[simp]

中文:
定理 preimage_Icc
  条件: {a b : R} (hb : 0 <= b)
  证明: by
  ext
  simp [ceil_le, hb, le_floor_iff]

@[simp]

Depends on / 依赖: ceil_le, le_floor_iff
-/
theorem preimage_Icc {a b : R} (hb : 0 <= b) :
    (Nat.cast : Nat -> R) ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉₊ ⌊b⌋₊ := by
  ext
  simp [ceil_le, hb, le_floor_iff]

@[simp]
/--
theorem `preimage_Ioi` / 定理 `preimage_Ioi`

English:
theorem preimage_Ioi
  given: {a : R} (ha : 0 <= a)
  statement: (Nat.cast : Nat -> R) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋₊
  proof: by
  ext
  simp [floor_lt, ha]

@[simp]

中文:
定理 preimage_Ioi
  条件: {a : R} (ha : 0 <= a)
  结论: (自然数.cast : 自然数 -> R) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋₊
  证明: by
  ext
  simp [floor_lt, ha]

@[simp]

Depends on / 依赖: floor_lt
-/
theorem preimage_Ioi {a : R} (ha : 0 <= a) : (Nat.cast : Nat -> R) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋₊ := by
  ext
  simp [floor_lt, ha]

@[simp]
/--
theorem `preimage_Ici` / 定理 `preimage_Ici`

English:
theorem preimage_Ici
  given: {a : R}
  statement: (Nat.cast : Nat -> R) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉₊
  proof: by
  ext
  simp [ceil_le]

@[simp]

中文:
定理 preimage_Ici
  条件: {a : R}
  结论: (自然数.cast : 自然数 -> R) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉₊
  证明: by
  ext
  simp [ceil_le]

@[simp]

Depends on / 依赖: ceil_le
-/
theorem preimage_Ici {a : R} : (Nat.cast : Nat -> R) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉₊ := by
  ext
  simp [ceil_le]

@[simp]
/--
theorem `preimage_Iio` / 定理 `preimage_Iio`

English:
theorem preimage_Iio
  given: {a : R}
  statement: (Nat.cast : Nat -> R) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉₊
  proof: by
  ext
  simp [lt_ceil]

@[simp]

中文:
定理 preimage_Iio
  条件: {a : R}
  结论: (自然数.cast : 自然数 -> R) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉₊
  证明: by
  ext
  simp [lt_ceil]

@[simp]

Depends on / 依赖: lt_ceil
-/
theorem preimage_Iio {a : R} : (Nat.cast : Nat -> R) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉₊ := by
  ext
  simp [lt_ceil]

@[simp]
/--
theorem `preimage_Iic` / 定理 `preimage_Iic`

English:
theorem preimage_Iic
  given: {a : R} (ha : 0 <= a)
  statement: (Nat.cast : Nat -> R) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋₊
  proof: by
  ext
  simp [le_floor_iff, ha]

@[push]

中文:
定理 preimage_Iic
  条件: {a : R} (ha : 0 <= a)
  结论: (自然数.cast : 自然数 -> R) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋₊
  证明: by
  ext
  simp [le_floor_iff, ha]

@[push]

Depends on / 依赖: le_floor_iff
-/
theorem preimage_Iic {a : R} (ha : 0 <= a) : (Nat.cast : Nat -> R) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋₊ := by
  ext
  simp [le_floor_iff, ha]

@[push]
/--
theorem `floor_add_natCast` / 定理 `floor_add_natCast`

English:
theorem floor_add_natCast
  given: [IsStrictOrderedRing R] (ha : 0 <= a) (n : Nat)
  statement: ⌊a + n⌋₊ = ⌊a⌋₊ + n
  proof: eq_of_forall_le_iff fun b => by
    rw [le_floor_iff (add_nonneg ha n.cast_nonneg)]
    obtain hb | hb := le_total n b
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add]; rw [add_comm n]; rw [add_comm (n : R)]; rw [add_le_add_iff_right]; rw [add_le_add_iff_right]; rw [le_floor_iff 

中文:
定理 floor_add_natCast
  条件: [IsStrictOrderedRing R] (ha : 0 <= a) (n : 自然数)
  结论: ⌊a + n⌋₊ = ⌊a⌋₊ + n
  证明: eq_of_forall_le_iff fun b => by
    rw [le_floor_iff (add_nonneg ha n.cast_nonneg)]
    obtain hb | hb := le_total n b
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add]; rw [add_comm n]; rw [add_comm (n : R)]; rw [add_le_add_iff_right]; rw [add_le_add_iff_right]; rw [le_floor_iff 

Depends on / 依赖: Nat.cast_add, add_comm, add_le_add_iff_right, add_left_comm, add_nonneg, cast_add, cast_nonneg, d.cast, eq_of_forall_le_iff, exists_add_of_le, ha.trans, iff_of_true, le_add_of_nonneg_right, le_floor_iff, le_self_add, le_total, n.cast_nonneg
-/
theorem floor_add_natCast [IsStrictOrderedRing R] (ha : 0 <= a) (n : Nat) : ⌊a + n⌋₊ = ⌊a⌋₊ + n :=
  eq_of_forall_le_iff fun b => by
    rw [le_floor_iff (add_nonneg ha n.cast_nonneg)]
    obtain hb | hb := le_total n b
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add]; rw [add_comm n]; rw [add_comm (n : R)]; rw [add_le_add_iff_right]; rw [add_le_add_iff_right]; rw [le_floor_iff ha]
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add]; rw [add_left_comm _ b]; rw [add_left_comm _ (b : R)]
      refine iff_of_true ?_ le_self_add
exact le_add_of_nonneg_right ha.trans le_add_of_nonneg_right d.cast_nonneg

variable [IsStrictOrderedRing R]

@[push]
/--
theorem `floor_add_one` / 定理 `floor_add_one`

English:
theorem floor_add_one
  given: (ha : 0 <= a)
  statement: ⌊a + 1⌋₊ = ⌊a⌋₊ + 1
  proof: by
  rw [← cast_one]; rw [floor_add_natCast ha 1]

@[push]

中文:
定理 floor_add_one
  条件: (ha : 0 <= a)
  结论: ⌊a + 1⌋₊ = ⌊a⌋₊ + 1
  证明: by
  rw [← cast_one]; rw [floor_add_natCast ha 1]

@[push]

Depends on / 依赖: cast_one, floor_add_natCast
-/
theorem floor_add_one (ha : 0 <= a) : ⌊a + 1⌋₊ = ⌊a⌋₊ + 1 := by
  rw [← cast_one]; rw [floor_add_natCast ha 1]

@[push]
/--
theorem `floor_add_ofNat` / 定理 `floor_add_ofNat`

English:
theorem floor_add_ofNat
  given: (ha : 0 <= a) (n : Nat) [n.AtLeastTwo]
  proof: floor_add_natCast ha n

@[simp]

中文:
定理 floor_add_ofNat
  条件: (ha : 0 <= a) (n : 自然数) [n.AtLeastTwo]
  证明: floor_add_natCast ha n

@[simp]

Depends on / 依赖: floor_add_natCast
-/
theorem floor_add_ofNat (ha : 0 <= a) (n : Nat) [n.AtLeastTwo] :
    ⌊a + ofNat(n)⌋₊ = ⌊a⌋₊ + ofNat(n) :=
  floor_add_natCast ha n

@[simp]
/--
theorem `floor_sub_natCast` / 定理 `floor_sub_natCast`

English:
theorem floor_sub_natCast
  given: [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) (n : Nat)
  proof: by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha, floor_of_nonpos (tsub_nonpos_of_le (ha.trans n.cast_nonneg)), zero_tsub]
  rcases le_total a n with h | h
  · rw [floor_of_nonpos (tsub_nonpos_of_le h), eq_comm, tsub_eq_zero_iff_le]
    exact Nat.cast_le.1 ((Nat.floor_le ha).trans h)
 

中文:
定理 floor_sub_natCast
  条件: [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) (n : 自然数)
  证明: by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha, floor_of_nonpos (tsub_nonpos_of_le (ha.trans n.cast_nonneg)), zero_tsub]
  rcases le_total a n with h | h
  · rw [floor_of_nonpos (tsub_nonpos_of_le h), eq_comm, tsub_eq_zero_iff_le]
    exact Nat.cast_le.1 ((Nat.floor_le ha).trans h)
 

Depends on / 依赖: Nat.cast_le, Nat.floor_le, add_zero, cast_le, cast_nonneg, eq_comm, eq_tsub_iff_add_eq_of_le, floor_add_natCast, floor_le, floor_of_nonpos, ha.trans, le_floor, le_total, le_tsub_of_add_le_left, n.cast_nonneg, trans_le, tsub_add_cancel_of_le, tsub_eq_zero_iff_le, tsub_nonpos_of_le, zero_tsub
-/
theorem floor_sub_natCast [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) (n : Nat) :
    ⌊a - n⌋₊ = ⌊a⌋₊ - n := by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha, floor_of_nonpos (tsub_nonpos_of_le (ha.trans n.cast_nonneg)), zero_tsub]
  rcases le_total a n with h | h
  · rw [floor_of_nonpos (tsub_nonpos_of_le h), eq_comm, tsub_eq_zero_iff_le]
    exact Nat.cast_le.1 ((Nat.floor_le ha).trans h)
  · rw [eq_tsub_iff_add_eq_of_le (le_floor h), ← floor_add_natCast _, tsub_add_cancel_of_le h]
    exact le_tsub_of_add_le_left ((add_zero _).trans_le h)

@[simp]
/--
theorem `floor_sub_one` / 定理 `floor_sub_one`

English:
theorem floor_sub_one
  given: [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R)
  statement: ⌊a - 1⌋₊ = ⌊a⌋₊ - 1
  proof: mod_cast floor_sub_natCast a 1

@[simp]

中文:
定理 floor_sub_one
  条件: [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R)
  结论: ⌊a - 1⌋₊ = ⌊a⌋₊ - 1
  证明: mod_cast floor_sub_natCast a 1

@[simp]

Depends on / 依赖: floor_sub_natCast, mod_cast
-/
theorem floor_sub_one [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) : ⌊a - 1⌋₊ = ⌊a⌋₊ - 1 :=
  mod_cast floor_sub_natCast a 1

@[simp]
/--
theorem `floor_sub_ofNat` / 定理 `floor_sub_ofNat`

English:
theorem floor_sub_ofNat
  given: [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) (n : Nat) [n.AtLeastTwo]
  proof: floor_sub_natCast a n

中文:
定理 floor_sub_ofNat
  条件: [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) (n : 自然数) [n.AtLeastTwo]
  证明: floor_sub_natCast a n

Depends on / 依赖: floor_sub_natCast
-/
theorem floor_sub_ofNat [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) (n : Nat) [n.AtLeastTwo] :
    ⌊a - ofNat(n)⌋₊ = ⌊a⌋₊ - ofNat(n) :=
  floor_sub_natCast a n

/--
theorem `ceil_add_natCast` / 定理 `ceil_add_natCast`

English:
theorem ceil_add_natCast
  given: (ha : 0 <= a) (n : Nat)
  statement: ⌈a + n⌉₊ = ⌈a⌉₊ + n
  proof: eq_of_forall_ge_iff fun b => by
    contrapose!
    rw [lt_ceil]
    obtain hb | hb := le_or_gt n b
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add]; rw [add_comm n]; rw [add_comm (n : R)]; rw [add_lt_add_iff_right]; rw [add_lt_add_iff_right]; rw [lt_ceil]
    · exact iff_of_true

中文:
定理 ceil_add_natCast
  条件: (ha : 0 <= a) (n : 自然数)
  结论: ⌈a + n⌉₊ = ⌈a⌉₊ + n
  证明: eq_of_forall_ge_iff fun b => by
    contrapose!
    rw [lt_ceil]
    obtain hb | hb := le_or_gt n b
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add]; rw [add_comm n]; rw [add_comm (n : R)]; rw [add_lt_add_iff_right]; rw [add_lt_add_iff_right]; rw [lt_ceil]
    · exact iff_of_true

Depends on / 依赖: Nat.cast_add, Nat.lt_add_left, add_comm, add_lt_add_iff_right, cast_add, cast_lt, contrapose, eq_of_forall_ge_iff, exists_add_of_le, iff_of_true, le_or_gt, lt_add_left, lt_add_of_nonneg_of_lt, lt_ceil
-/
theorem ceil_add_natCast (ha : 0 <= a) (n : Nat) : ⌈a + n⌉₊ = ⌈a⌉₊ + n :=
  eq_of_forall_ge_iff fun b => by
    contrapose!
    rw [lt_ceil]
    obtain hb | hb := le_or_gt n b
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add]; rw [add_comm n]; rw [add_comm (n : R)]; rw [add_lt_add_iff_right]; rw [add_lt_add_iff_right]; rw [lt_ceil]
    · exact iff_of_true (lt_add_of_nonneg_of_lt ha <| cast_lt.2 hb) (Nat.lt_add_left _ hb)

/--
theorem `ceil_add_one` / 定理 `ceil_add_one`

English:
theorem ceil_add_one
  given: (ha : 0 <= a)
  statement: ⌈a + 1⌉₊ = ⌈a⌉₊ + 1
  proof: by
  rw [cast_one.symm]; rw [ceil_add_natCast ha 1]

中文:
定理 ceil_add_one
  条件: (ha : 0 <= a)
  结论: ⌈a + 1⌉₊ = ⌈a⌉₊ + 1
  证明: by
  rw [cast_one.symm]; rw [ceil_add_natCast ha 1]

Depends on / 依赖: cast_one, cast_one.symm, ceil_add_natCast
-/
theorem ceil_add_one (ha : 0 <= a) : ⌈a + 1⌉₊ = ⌈a⌉₊ + 1 := by
  rw [cast_one.symm]; rw [ceil_add_natCast ha 1]

/--
theorem `ceil_add_ofNat` / 定理 `ceil_add_ofNat`

English:
theorem ceil_add_ofNat
  given: (ha : 0 <= a) (n : Nat) [n.AtLeastTwo]
  proof: ceil_add_natCast ha n

@[bound]

中文:
定理 ceil_add_ofNat
  条件: (ha : 0 <= a) (n : 自然数) [n.AtLeastTwo]
  证明: ceil_add_natCast ha n

@[bound]

Depends on / 依赖: ceil_add_natCast
-/
theorem ceil_add_ofNat (ha : 0 <= a) (n : Nat) [n.AtLeastTwo] :
    ⌈a + ofNat(n)⌉₊ = ⌈a⌉₊ + ofNat(n) :=
  ceil_add_natCast ha n

@[bound]
/--
theorem `ceil_lt_add_one` / 定理 `ceil_lt_add_one`

English:
theorem ceil_lt_add_one
  given: (ha : 0 <= a)
  statement: (⌈a⌉₊ : R) < a + 1
  proof: lt_ceil.1 (Nat.lt_succ_self _).trans_le (ceil_add_one ha).ge

@[bound]

中文:
定理 ceil_lt_add_one
  条件: (ha : 0 <= a)
  结论: (⌈a⌉₊ : R) < a + 1
  证明: lt_ceil.1 (Nat.lt_succ_self _).trans_le (ceil_add_one ha).ge

@[bound]

Depends on / 依赖: Nat.lt_succ_self, ceil_add_one, lt_ceil, lt_succ_self, trans_le
-/
theorem ceil_lt_add_one (ha : 0 <= a) : (⌈a⌉₊ : R) < a + 1 :=
lt_ceil.1 (Nat.lt_succ_self _).trans_le (ceil_add_one ha).ge

@[bound]
/--
theorem `ceil_add_le` / 定理 `ceil_add_le`

English:
theorem ceil_add_le
  given: (a b : R)
  statement: ⌈a + b⌉₊ <= ⌈a⌉₊ + ⌈b⌉₊
  proof: by
  rw [ceil_le]; rw [Nat.cast_add]
  gcongr <;> apply le_ceil

中文:
定理 ceil_add_le
  条件: (a b : R)
  结论: ⌈a + b⌉₊ <= ⌈a⌉₊ + ⌈b⌉₊
  证明: by
  rw [ceil_le]; rw [Nat.cast_add]
  gcongr <;> apply le_ceil

Depends on / 依赖: Nat.cast_add, cast_add, ceil_le, le_ceil
-/
theorem ceil_add_le (a b : R) : ⌈a + b⌉₊ <= ⌈a⌉₊ + ⌈b⌉₊ := by
  rw [ceil_le]; rw [Nat.cast_add]
  gcongr <;> apply le_ceil

variable [Sub R] [OrderedSub R] [ExistsAddOfLE R]

/--
lemma `ceil_sub_natCast` / 引理 `ceil_sub_natCast`

English:
lemma ceil_sub_natCast
  given: (a : R) (n : Nat)
  statement: ⌈a - n⌉₊ = ⌈a⌉₊ - n
  proof: by
  obtain han | hna := le_total a n
  · rwa [ceil_eq_zero.2 (tsub_nonpos_of_le han), eq_comm, tsub_eq_zero_iff_le, Nat.ceil_le]
  · refine eq_tsub_of_add_eq ?_
    rw [← ceil_add_natCast]; rw [tsub_add_cancel_of_le hna]
    exact le_tsub_of_add_le_left ((add_zero _).trans_le hna)

中文:
引理 ceil_sub_natCast
  条件: (a : R) (n : 自然数)
  结论: ⌈a - n⌉₊ = ⌈a⌉₊ - n
  证明: by
  obtain han | hna := le_total a n
  · rwa [ceil_eq_zero.2 (tsub_nonpos_of_le han), eq_comm, tsub_eq_zero_iff_le, Nat.ceil_le]
  · refine eq_tsub_of_add_eq ?_
    rw [← ceil_add_natCast]; rw [tsub_add_cancel_of_le hna]
    exact le_tsub_of_add_le_left ((add_zero _).trans_le hna)
-/
@[simp] lemma ceil_sub_natCast (a : R) (n : Nat) : ⌈a - n⌉₊ = ⌈a⌉₊ - n := by
  obtain han | hna := le_total a n
  · rwa [ceil_eq_zero.2 (tsub_nonpos_of_le han), eq_comm, tsub_eq_zero_iff_le, Nat.ceil_le]
  · refine eq_tsub_of_add_eq ?_
    rw [← ceil_add_natCast]; rw [tsub_add_cancel_of_le hna]
    exact le_tsub_of_add_le_left ((add_zero _).trans_le hna)

/--
lemma `ceil_sub_one` / 引理 `ceil_sub_one`

English:
lemma ceil_sub_one
  given: (a : R)
  statement: ⌈a - 1⌉₊ = ⌈a⌉₊ - 1
  proof: by simpa using ceil_sub_natCast a 1

中文:
引理 ceil_sub_one
  条件: (a : R)
  结论: ⌈a - 1⌉₊ = ⌈a⌉₊ - 1
  证明: by simpa using ceil_sub_natCast a 1
-/
@[simp] lemma ceil_sub_one (a : R) : ⌈a - 1⌉₊ = ⌈a⌉₊ - 1 := by simpa using ceil_sub_natCast a 1

/--
lemma `ceil_sub_ofNat` / 引理 `ceil_sub_ofNat`

English:
lemma ceil_sub_ofNat
  given: (a : R) (n : Nat) [n.AtLeastTwo]
  statement: ⌈a - ofNat(n)⌉₊ = ⌈a⌉₊ - ofNat(n)
  proof: ceil_sub_natCast a n

中文:
引理 ceil_sub_ofNat
  条件: (a : R) (n : 自然数) [n.AtLeastTwo]
  结论: ⌈a - of自然数(n)⌉₊ = ⌈a⌉₊ - of自然数(n)
  证明: ceil_sub_natCast a n
-/
@[simp] lemma ceil_sub_ofNat (a : R) (n : Nat) [n.AtLeastTwo] : ⌈a - ofNat(n)⌉₊ = ⌈a⌉₊ - ofNat(n) :=
  ceil_sub_natCast a n

end LinearOrderedSemiring

section LinearOrderedRing

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]

@[bound]
/--
theorem `sub_one_lt_floor` / 定理 `sub_one_lt_floor`

English:
theorem sub_one_lt_floor
  given: (a : R)
  statement: a - 1 < ⌊a⌋₊
  proof: sub_lt_iff_lt_add.2 lt_floor_add_one a

中文:
定理 sub_one_lt_floor
  条件: (a : R)
  结论: a - 1 < ⌊a⌋₊
  证明: sub_lt_iff_lt_add.2 lt_floor_add_one a

Depends on / 依赖: lt_floor_add_one, sub_lt_iff_lt_add
-/
theorem sub_one_lt_floor (a : R) : a - 1 < ⌊a⌋₊ :=
sub_lt_iff_lt_add.2 lt_floor_add_one a

/--
lemma `self_sub_floor_lt_one` / 引理 `self_sub_floor_lt_one`

English:
lemma self_sub_floor_lt_one
  given: (a : R)
  statement: a - ⌊a⌋₊ < 1
  proof: sub_lt_iff_lt_add'.mpr lt_floor_add_one a

中文:
引理 self_sub_floor_lt_one
  条件: (a : R)
  结论: a - ⌊a⌋₊ < 1
  证明: sub_lt_iff_lt_add'.mpr lt_floor_add_one a

Depends on / 依赖: lt_floor_add_one, sub_lt_iff_lt_add
-/
lemma self_sub_floor_lt_one (a : R) : a - ⌊a⌋₊ < 1 :=
sub_lt_iff_lt_add'.mpr lt_floor_add_one a

/--
lemma `zero_le_self_sub_floor` / 引理 `zero_le_self_sub_floor`

English:
lemma zero_le_self_sub_floor
  given: {a : R} (ha : 0 <= a)
  statement: 0 <= a - ⌊a⌋₊
  proof: sub_nonneg.mpr Nat.floor_le ha

中文:
引理 zero_le_self_sub_floor
  条件: {a : R} (ha : 0 <= a)
  结论: 0 <= a - ⌊a⌋₊
  证明: sub_nonneg.mpr Nat.floor_le ha

Depends on / 依赖: Nat.floor_le, floor_le, sub_nonneg, sub_nonneg.mpr
-/
lemma zero_le_self_sub_floor {a : R} (ha : 0 <= a) : 0 <= a - ⌊a⌋₊ :=
sub_nonneg.mpr Nat.floor_le ha

/--
lemma `abs_sub_floor_le` / 引理 `abs_sub_floor_le`

English:
lemma abs_sub_floor_le
  given: {a : R} (ha : 0 <= a)
  statement: |a - ⌊a⌋₊| <= 1
  proof: by
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa using (floor_le ha).trans (le_add_of_nonneg_right zero_le_one)
  · simpa [add_comm] using (lt_floor_add_one a).le

中文:
引理 abs_sub_floor_le
  条件: {a : R} (ha : 0 <= a)
  结论: |a - ⌊a⌋₊| <= 1
  证明: by
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa using (floor_le ha).trans (le_add_of_nonneg_right zero_le_one)
  · simpa [add_comm] using (lt_floor_add_one a).le

Depends on / 依赖: abs_le, abs_le.mpr, add_comm, floor_le, le_add_of_nonneg_right, lt_floor_add_one, zero_le_one
-/
lemma abs_sub_floor_le {a : R} (ha : 0 <= a) : |a - ⌊a⌋₊| <= 1 := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa using (floor_le ha).trans (le_add_of_nonneg_right zero_le_one)
  · simpa [add_comm] using (lt_floor_add_one a).le

/--
lemma `abs_floor_sub_le` / 引理 `abs_floor_sub_le`

English:
lemma abs_floor_sub_le
  given: {a : R} (ha : 0 <= a)
  statement: |⌊a⌋₊ - a| <= 1
  proof: abs_sub_comm a ⌊a⌋₊ ▸ abs_sub_floor_le ha

中文:
引理 abs_floor_sub_le
  条件: {a : R} (ha : 0 <= a)
  结论: |⌊a⌋₊ - a| <= 1
  证明: abs_sub_comm a ⌊a⌋₊ ▸ abs_sub_floor_le ha

Depends on / 依赖: abs_sub_comm, abs_sub_floor_le
-/
lemma abs_floor_sub_le {a : R} (ha : 0 <= a) : |⌊a⌋₊ - a| <= 1 :=
  abs_sub_comm a ⌊a⌋₊ ▸ abs_sub_floor_le ha

/--
lemma `abs_sub_ceil_le` / 引理 `abs_sub_ceil_le`

English:
lemma abs_sub_ceil_le
  given: {a : R} (ha : 0 <= a)
  statement: |a - ⌈a⌉₊| <= 1
  proof: by
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa using (ceil_lt_add_one ha).le
  · simpa using (le_ceil a).trans (le_add_of_nonneg_left zero_le_one)

中文:
引理 abs_sub_ceil_le
  条件: {a : R} (ha : 0 <= a)
  结论: |a - ⌈a⌉₊| <= 1
  证明: by
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa using (ceil_lt_add_one ha).le
  · simpa using (le_ceil a).trans (le_add_of_nonneg_left zero_le_one)

Depends on / 依赖: abs_le, abs_le.mpr, ceil_lt_add_one, le_add_of_nonneg_left, le_ceil, zero_le_one
-/
lemma abs_sub_ceil_le {a : R} (ha : 0 <= a) : |a - ⌈a⌉₊| <= 1 := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa using (ceil_lt_add_one ha).le
  · simpa using (le_ceil a).trans (le_add_of_nonneg_left zero_le_one)

/--
lemma `abs_ceil_sub_le` / 引理 `abs_ceil_sub_le`

English:
lemma abs_ceil_sub_le
  given: {a : R} (ha : 0 <= a)
  statement: |⌈a⌉₊ - a| <= 1
  proof: abs_sub_comm a ⌈a⌉₊ ▸ abs_sub_ceil_le ha

中文:
引理 abs_ceil_sub_le
  条件: {a : R} (ha : 0 <= a)
  结论: |⌈a⌉₊ - a| <= 1
  证明: abs_sub_comm a ⌈a⌉₊ ▸ abs_sub_ceil_le ha

Depends on / 依赖: abs_sub_ceil_le, abs_sub_comm
-/
lemma abs_ceil_sub_le {a : R} (ha : 0 <= a) : |⌈a⌉₊ - a| <= 1 :=
  abs_sub_comm a ⌈a⌉₊ ▸ abs_sub_ceil_le ha

end LinearOrderedRing

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a : R}
variable {S : Type*} [Semiring S] [LinearOrder S] [FloorSemiring S] {b : S}

/--
theorem `floor_congr` / 定理 `floor_congr`

English:
theorem floor_congr
  statement: [IsStrictOrderedRing R] [IsStrictOrderedRing S]
  proof: by
  have h₀ : 0 <= a ↔ 0 <= b := by simpa only [cast_zero] using h 0
  obtain ha | ha := lt_or_ge a 0
  · rw [floor_of_nonpos ha.le, floor_of_nonpos (le_of_not_ge <| h₀.not.mp ha.not_ge)]
  exact (le_floor <| (h _).1 <| floor_le ha).antisymm (le_floor <| (h _).2 <| floor_le <| h₀.1 ha)

中文:
定理 floor_congr
  结论: [IsStrictOrderedRing R] [IsStrictOrderedRing S]
  证明: by
  have h₀ : 0 <= a ↔ 0 <= b := by simpa only [cast_zero] using h 0
  obtain ha | ha := lt_or_ge a 0
  · rw [floor_of_nonpos ha.le, floor_of_nonpos (le_of_not_ge <| h₀.not.mp ha.not_ge)]
  exact (le_floor <| (h _).1 <| floor_le ha).antisymm (le_floor <| (h _).2 <| floor_le <| h₀.1 ha)

Depends on / 依赖: antisymm, cast_zero, floor_le, floor_of_nonpos, ha.le, ha.not_ge, le_floor, le_of_not_ge, lt_or_ge, not.mp, not_ge
-/
theorem floor_congr [IsStrictOrderedRing R] [IsStrictOrderedRing S]
    (h : forall n : Nat, (n : R) <= a ↔ (n : S) <= b) : ⌊a⌋₊ = ⌊b⌋₊ := by
  have h₀ : 0 <= a ↔ 0 <= b := by simpa only [cast_zero] using h 0
  obtain ha | ha := lt_or_ge a 0
  · rw [floor_of_nonpos ha.le, floor_of_nonpos (le_of_not_ge <| h₀.not.mp ha.not_ge)]
  exact (le_floor <| (h _).1 <| floor_le ha).antisymm (le_floor <| (h _).2 <| floor_le <| h₀.1 ha)

/--
theorem `ceil_congr` / 定理 `ceil_congr`

English:
theorem ceil_congr
  given: (h : forall n : Nat, a <= n ↔ b <= n)
  statement: ⌈a⌉₊ = ⌈b⌉₊
  proof: (ceil_le.2 <| (h _).2 <| le_ceil _).antisymm ceil_le.2 (h _).1 le_ceil _

中文:
定理 ceil_congr
  条件: (h : 对任意 n : 自然数, a <= n ↔ b <= n)
  结论: ⌈a⌉₊ = ⌈b⌉₊
  证明: (ceil_le.2 <| (h _).2 <| le_ceil _).antisymm ceil_le.2 (h _).1 le_ceil _

Depends on / 依赖: antisymm, ceil_le, le_ceil
-/
theorem ceil_congr (h : forall n : Nat, a <= n ↔ b <= n) : ⌈a⌉₊ = ⌈b⌉₊ :=
(ceil_le.2 <| (h _).2 <| le_ceil _).antisymm ceil_le.2 (h _).1 le_ceil _

variable {F : Type*} [FunLike F R S] [RingHomClass F R S]

/--
theorem `map_floor` / 定理 `map_floor`

English:
theorem map_floor
  statement: [IsStrictOrderedRing R] [IsStrictOrderedRing S]
  proof: floor_congr fun n => by rw [← map_natCast f, hf.le_iff_le]

中文:
定理 map_floor
  结论: [IsStrictOrderedRing R] [IsStrictOrderedRing S]
  证明: floor_congr fun n => by rw [← map_natCast f, hf.le_iff_le]

Depends on / 依赖: floor_congr, hf.le_iff_le, le_iff_le, map_natCast
-/
theorem map_floor [IsStrictOrderedRing R] [IsStrictOrderedRing S]
    (f : F) (hf : StrictMono f) (a : R) : ⌊f a⌋₊ = ⌊a⌋₊ :=
  floor_congr fun n => by rw [← map_natCast f, hf.le_iff_le]

/--
theorem `map_ceil` / 定理 `map_ceil`

English:
theorem map_ceil
  given: (f : F) (hf : StrictMono f) (a : R)
  statement: ⌈f a⌉₊ = ⌈a⌉₊
  proof: ceil_congr fun n => by rw [← map_natCast f, hf.le_iff_le]

中文:
定理 map_ceil
  条件: (f : F) (hf : StrictMono f) (a : R)
  结论: ⌈f a⌉₊ = ⌈a⌉₊
  证明: ceil_congr fun n => by rw [← map_natCast f, hf.le_iff_le]

Depends on / 依赖: ceil_congr, hf.le_iff_le, le_iff_le, map_natCast
-/
theorem map_ceil (f : F) (hf : StrictMono f) (a : R) : ⌈f a⌉₊ = ⌈a⌉₊ :=
  ceil_congr fun n => by rw [← map_natCast f, hf.le_iff_le]

end Nat

/--
theorem `subsingleton_floorSemiring` / 定理 `subsingleton_floorSemiring`

English:
theorem subsingleton_floorSemiring
  given: {R} [Semiring R] [LinearOrder R]
  proof: by
  refine ⟨fun H₁ H₂ => ?_⟩
  have : H₁.ceil = H₂.ceil := funext fun a => (H₁.gc_ceil.l_unique H₂.gc_ceil) fun n => rfl
  have : H₁.floor = H₂.floor := by
    ext a
    rcases lt_or_ge a 0 with h | h
    · rw [H₁.floor_of_neg, H₂.floor_of_neg] <;> exact h
    · refine eq_of_forall_le_iff fun n => 

中文:
定理 subsingleton_floorSemiring
  条件: {R} [Semiring R] [LinearOrder R]
  证明: by
  refine ⟨fun H₁ H₂ => ?_⟩
  have : H₁.ceil = H₂.ceil := funext fun a => (H₁.gc_ceil.l_unique H₂.gc_ceil) fun n => rfl
  have : H₁.floor = H₂.floor := by
    ext a
    rcases lt_or_ge a 0 with h | h
    · rw [H₁.floor_of_neg, H₂.floor_of_neg] <;> exact h
    · refine eq_of_forall_le_iff fun n => 

Depends on / 依赖: eq_of_forall_le_iff, floor_of_neg, gc_ceil, gc_ceil.l_unique, gc_floor, l_unique, lt_or_ge
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
      rw [H₁.gc_floor]; rw [H₂.gc_floor] <;> exact h
  cases H₁
  cases H₂
  congr
