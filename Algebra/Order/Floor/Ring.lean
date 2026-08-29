/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity.Core

/-!
# Lemmas on `Int.floor`, `Int.ceil` and `Int.fract`

This file contains basic results on the integer-valued floor and ceiling functions, as well as the
fractional part operator.

## TODO

`LinearOrder` can be relaxed to `PartialOrder` in many lemmas.

## Tags

rounding, floor, ceil
-/

public section

assert_not_exists Finset

open Set

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

variable {α : Type*}

/--
theorem `int_floor_nonneg` / 定理 `int_floor_nonneg`

English:
theorem int_floor_nonneg
  given: [Ring α] [LinearOrder α] [FloorRing α] {a : α} (ha : 0 <= a)
  proof: Int.floor_nonneg.2 ha

中文:
定理 int_floor_nonneg
  条件: [环 α] [线性序 α] [Floor环 α] {a : α} (ha : 0 <= a)
  证明: Int.floor_nonneg.2 ha

Depends on / 依赖: Int.floor_nonneg, floor_nonneg
-/
theorem int_floor_nonneg [Ring α] [LinearOrder α] [FloorRing α] {a : α} (ha : 0 <= a) :
    0 <= ⌊a⌋ :=
  Int.floor_nonneg.2 ha

/--
theorem `int_floor_nonneg_of_pos` / 定理 `int_floor_nonneg_of_pos`

English:
theorem int_floor_nonneg_of_pos
  statement: [Ring α] [LinearOrder α] [FloorRing α] {a : α}
  proof: int_floor_nonneg ha.le

中文:
定理 int_floor_nonneg_of_pos
  结论: [环 α] [线性序 α] [Floor环 α] {a : α}
  证明: int_floor_nonneg ha.le

Depends on / 依赖: ha.le, int_floor_nonneg
-/
theorem int_floor_nonneg_of_pos [Ring α] [LinearOrder α] [FloorRing α] {a : α}
    (ha : 0 < a) :
    0 <= ⌊a⌋ :=
  int_floor_nonneg ha.le

/-- Extension for the `positivity` tactic: `Int.floor` is nonnegative if its input is. -/
@[positivity ⌊_⌋]
meta def evalIntFloor : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Int), ~q(@Int.floor $α' $ir $io $j $a) =>
    match ← core q(inferInstance) (some q(inferInstance)) a with
    | .positive pa =>
        assertInstancesCommute
        pure (.nonnegative q(int_floor_nonneg_of_pos (α := $α') $pa))
    | .nonnegative pa =>
        assertInstancesCommute
        pure (.nonnegative q(int_floor_nonneg (α := $α') $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Int.floor application"

/--
theorem `nat_ceil_pos` / 定理 `nat_ceil_pos`

English:
theorem nat_ceil_pos
  given: [Semiring α] [LinearOrder α] [FloorSemiring α] {a : α}
  proof: Nat.ceil_pos.2

中文:
定理 nat_ceil_pos
  条件: [半环 α] [线性序 α] [FloorSemiring α] {a : α}
  证明: Nat.ceil_pos.2

Depends on / 依赖: Nat.ceil_pos, ceil_pos
-/
theorem nat_ceil_pos [Semiring α] [LinearOrder α] [FloorSemiring α] {a : α} :
    0 < a -> 0 < ⌈a⌉₊ :=
  Nat.ceil_pos.2

/-- Extension for the `positivity` tactic: `Nat.ceil` is positive if its input is. -/
@[positivity ⌈_⌉₊]
meta def evalNatCeil : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Nat), ~q(@Nat.ceil $α' $ir $io $j $a) =>
    let _i ← synthInstanceQ q(LinearOrder $α')
    let _i ← synthInstanceQ q(IsStrictOrderedRing $α')
    assertInstancesCommute
    match ← core q(inferInstance) (some q(inferInstance)) a with
    | .positive pa =>
      assertInstancesCommute
      pure (.positive q(nat_ceil_pos (α := $α') $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Nat.ceil application"

/--
theorem `int_ceil_pos` / 定理 `int_ceil_pos`

English:
theorem int_ceil_pos
  given: [Ring α] [LinearOrder α] [FloorRing α] {a : α}
  statement: 0 < a -> 0 < ⌈a⌉
  proof: Int.ceil_pos.2

中文:
定理 int_ceil_pos
  条件: [环 α] [线性序 α] [Floor环 α] {a : α}
  结论: 0 < a -> 0 < ⌈a⌉
  证明: Int.ceil_pos.2

Depends on / 依赖: Int.ceil_pos, ceil_pos
-/
theorem int_ceil_pos [Ring α] [LinearOrder α] [FloorRing α] {a : α} : 0 < a -> 0 < ⌈a⌉ :=
  Int.ceil_pos.2

/-- Extension for the `positivity` tactic: `Int.ceil` is positive/nonnegative if its input is. -/
@[positivity ⌈_⌉]
meta def evalIntCeil : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Int), ~q(@Int.ceil $α' $ir $io $j $a) =>
    match ← core q(inferInstance) (some q(inferInstance)) a with
    | .positive pa =>
        assertInstancesCommute
        pure (.positive q(int_ceil_pos (α := $α') $pa))
    | .nonnegative pa =>
        let _i ← synthInstanceQ q(IsStrictOrderedRing $α')
        assertInstancesCommute
        pure (.nonnegative q(Int.ceil_nonneg (α := $α') $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Int.ceil application"

end Mathlib.Meta.Positivity

variable {F R S : Type*}

/-! ### Floor rings -/

namespace Int

variable [Ring R] [LinearOrder R] [FloorRing R] {z : Int} {a b : R}

/-! #### Floor -/

section floor

@[simp]
/--
theorem `floor_le_neg_one_iff` / 定理 `floor_le_neg_one_iff`

English:
theorem floor_le_neg_one_iff
  statement: ⌊a⌋ <= -1 ↔ a < 0
  proof: by
  simpa using floor_le_iff (z := -1)

中文:
定理 floor_le_neg_one_iff
  结论: ⌊a⌋ <= -1 ↔ a < 0
  证明: by
  simpa using floor_le_iff (z := -1)

Depends on / 依赖: floor_le_iff
-/
theorem floor_le_neg_one_iff : ⌊a⌋ <= -1 ↔ a < 0 := by
  simpa using floor_le_iff (z := -1)

/--
theorem `lt_succ_floor` / 定理 `lt_succ_floor`

English:
theorem lt_succ_floor
  given: (a : R)
  statement: a < ⌊a⌋.succ
  proof: floor_lt.1 Int.lt_succ_self _

@[simp, bound]

中文:
定理 lt_succ_floor
  条件: (a : R)
  结论: a < ⌊a⌋.succ
  证明: floor_lt.1 Int.lt_succ_self _

@[simp, bound]

Depends on / 依赖: Int.lt_succ_self, floor_lt, lt_succ_self
-/
theorem lt_succ_floor (a : R) : a < ⌊a⌋.succ :=
floor_lt.1 Int.lt_succ_self _

@[simp, bound]
/--
theorem `lt_floor_add_one` / 定理 `lt_floor_add_one`

English:
theorem lt_floor_add_one
  given: (a : R)
  statement: a < ⌊a⌋ + 1
  proof: by
  simpa only [Int.succ, Int.cast_add, Int.cast_one] using lt_succ_floor a

@[gcongr, mono]

中文:
定理 lt_floor_add_one
  条件: (a : R)
  结论: a < ⌊a⌋ + 1
  证明: by
  simpa only [Int.succ, Int.cast_add, Int.cast_one] using lt_succ_floor a

@[gcongr, mono]

Depends on / 依赖: Int.cast_add, Int.cast_one, Int.succ, cast_add, cast_one, lt_succ_floor
-/
theorem lt_floor_add_one (a : R) : a < ⌊a⌋ + 1 := by
  simpa only [Int.succ, Int.cast_add, Int.cast_one] using lt_succ_floor a

@[gcongr, mono]
/--
theorem `floor_mono` / 定理 `floor_mono`

English:
theorem floor_mono
  statement: Monotone (floor : R -> Int)
  proof: gc_coe_floor.monotone_u

中文:
定理 floor_mono
  结论: 递增 (floor : R -> 整数)
  证明: gc_coe_floor.monotone_u

Depends on / 依赖: gc_coe_floor, gc_coe_floor.monotone_u, monotone_u
-/
theorem floor_mono : Monotone (floor : R -> Int) :=
  gc_coe_floor.monotone_u

/--
lemma `floor_le_floor` / 引理 `floor_le_floor`

English:
lemma floor_le_floor
  given: (hab : a <= b)
  statement: ⌊a⌋ <= ⌊b⌋
  proof: floor_mono hab

中文:
引理 floor_le_floor
  条件: (hab : a <= b)
  结论: ⌊a⌋ <= ⌊b⌋
  证明: floor_mono hab
-/
@[bound] lemma floor_le_floor (hab : a <= b) : ⌊a⌋ <= ⌊b⌋ := floor_mono hab

/--
theorem `floor_pos` / 定理 `floor_pos`

English:
theorem floor_pos
  statement: 0 < ⌊a⌋ ↔ 1 <= a
  proof: by
  rw [Int.lt_iff_add_one_le]; rw [zero_add]; rw [le_floor]; rw [cast_one]

中文:
定理 floor_pos
  结论: 0 < ⌊a⌋ ↔ 1 <= a
  证明: by
  rw [Int.lt_iff_add_one_le]; rw [zero_add]; rw [le_floor]; rw [cast_one]

Depends on / 依赖: Int.lt_iff_add_one_le, cast_one, le_floor, lt_iff_add_one_le, zero_add
-/
theorem floor_pos : 0 < ⌊a⌋ ↔ 1 <= a := by
  rw [Int.lt_iff_add_one_le]; rw [zero_add]; rw [le_floor]; rw [cast_one]

/--
theorem `floor_eq_iff` / 定理 `floor_eq_iff`

English:
theorem floor_eq_iff
  statement: ⌊a⌋ = z ↔ ↑z <= a ∧ a < z + 1
  proof: by
  rw [le_antisymm_iff]; rw [le_floor]; rw [← Int.lt_add_one_iff]; rw [floor_lt]; rw [Int.cast_add]; rw [Int.cast_one]; rw [and_comm]

@[simp]

中文:
定理 floor_eq_iff
  结论: ⌊a⌋ = z ↔ ↑z <= a ∧ a < z + 1
  证明: by
  rw [le_antisymm_iff]; rw [le_floor]; rw [← Int.lt_add_one_iff]; rw [floor_lt]; rw [Int.cast_add]; rw [Int.cast_one]; rw [and_comm]

@[simp]

Depends on / 依赖: Int.cast_add, Int.cast_one, Int.lt_add_one_iff, and_comm, cast_add, cast_one, floor_lt, le_antisymm_iff, le_floor, lt_add_one_iff
-/
theorem floor_eq_iff : ⌊a⌋ = z ↔ ↑z <= a ∧ a < z + 1 := by
  rw [le_antisymm_iff]; rw [le_floor]; rw [← Int.lt_add_one_iff]; rw [floor_lt]; rw [Int.cast_add]; rw [Int.cast_one]; rw [and_comm]

@[simp]
/--
theorem `floor_eq_zero_iff` / 定理 `floor_eq_zero_iff`

English:
theorem floor_eq_zero_iff
  statement: ⌊a⌋ = 0 ↔ a in Ico (0 : R) 1
  proof: by simp [floor_eq_iff]

中文:
定理 floor_eq_zero_iff
  结论: ⌊a⌋ = 0 ↔ a in 左闭右开区间 (0 : R) 1
  证明: by simp [floor_eq_iff]

Depends on / 依赖: floor_eq_iff
-/
theorem floor_eq_zero_iff : ⌊a⌋ = 0 ↔ a in Ico (0 : R) 1 := by simp [floor_eq_iff]

/--
theorem `floor_eq_on_Ico` / 定理 `floor_eq_on_Ico`

English:
theorem floor_eq_on_Ico
  given: (n : Int)
  statement: forall a in Set.Ico (n : R) (n + 1), ⌊a⌋ = n
  proof: fun _ ⟨h₀, h₁⟩ =>
  floor_eq_iff.mpr ⟨h₀, h₁⟩

中文:
定理 floor_eq_on_Ico
  条件: (n : 整数)
  结论: 对任意 a in 集合.左闭右开区间 (n : R) (n + 1), ⌊a⌋ = n
  证明: fun _ ⟨h₀, h₁⟩ =>
  floor_eq_iff.mpr ⟨h₀, h₁⟩
-/
theorem floor_eq_on_Ico (n : Int) : forall a in Set.Ico (n : R) (n + 1), ⌊a⌋ = n := fun _ ⟨h₀, h₁⟩ =>
  floor_eq_iff.mpr ⟨h₀, h₁⟩

/--
theorem `floor_eq_on_Ico'` / 定理 `floor_eq_on_Ico'`

English:
theorem floor_eq_on_Ico'
  given: (n : Int)
  statement: forall a in Set.Ico (n : R) (n + 1), (⌊a⌋ : R) = n
  proof: fun a ha =>
congr_arg _ floor_eq_on_Ico n a ha

@[simp]

中文:
定理 floor_eq_on_Ico'
  条件: (n : 整数)
  结论: 对任意 a in 集合.左闭右开区间 (n : R) (n + 1), (⌊a⌋ : R) = n
  证明: fun a ha =>
congr_arg _ floor_eq_on_Ico n a ha

@[simp]
-/
theorem floor_eq_on_Ico' (n : Int) : forall a in Set.Ico (n : R) (n + 1), (⌊a⌋ : R) = n := fun a ha =>
congr_arg _ floor_eq_on_Ico n a ha

@[simp]
/--
theorem `preimage_floor_singleton` / 定理 `preimage_floor_singleton`

English:
theorem preimage_floor_singleton
  given: (m : Int)
  statement: (floor : R -> Int) ⁻¹' {m} = Ico (m : R) (m + 1)
  proof: ext fun _ => floor_eq_iff

中文:
定理 preimage_floor_singleton
  条件: (m : 整数)
  结论: (floor : R -> 整数) ⁻¹' {m} = 左闭右开区间 (m : R) (m + 1)
  证明: ext fun _ => floor_eq_iff

Depends on / 依赖: floor_eq_iff
-/
theorem preimage_floor_singleton (m : Int) : (floor : R -> Int) ⁻¹' {m} = Ico (m : R) (m + 1) :=
  ext fun _ => floor_eq_iff

variable [IsOrderedRing R]

@[simp, bound]
/--
theorem `sub_one_lt_floor` / 定理 `sub_one_lt_floor`

English:
theorem sub_one_lt_floor
  given: (a : R)
  statement: a - 1 < ⌊a⌋
  proof: sub_lt_iff_lt_add.2 (lt_floor_add_one a)

@[simp]

中文:
定理 sub_one_lt_floor
  条件: (a : R)
  结论: a - 1 < ⌊a⌋
  证明: sub_lt_iff_lt_add.2 (lt_floor_add_one a)

@[simp]

Depends on / 依赖: lt_floor_add_one, sub_lt_iff_lt_add
-/
theorem sub_one_lt_floor (a : R) : a - 1 < ⌊a⌋ :=
  sub_lt_iff_lt_add.2 (lt_floor_add_one a)

@[simp]
/--
theorem `floor_intCast` / 定理 `floor_intCast`

English:
theorem floor_intCast
  given: (z : Int)
  statement: ⌊(z : R)⌋ = z
  proof: eq_of_forall_le_iff fun a => by rw [le_floor, Int.cast_le]

@[simp]

中文:
定理 floor_intCast
  条件: (z : 整数)
  结论: ⌊(z : R)⌋ = z
  证明: eq_of_forall_le_iff fun a => by rw [le_floor, Int.cast_le]

@[simp]

Depends on / 依赖: Int.cast_le, cast_le, eq_of_forall_le_iff, le_floor
-/
theorem floor_intCast (z : Int) : ⌊(z : R)⌋ = z :=
  eq_of_forall_le_iff fun a => by rw [le_floor, Int.cast_le]

@[simp]
/--
theorem `floor_natCast` / 定理 `floor_natCast`

English:
theorem floor_natCast
  given: (n : Nat)
  statement: ⌊(n : R)⌋ = n
  proof: eq_of_forall_le_iff fun a => by rw [le_floor, ← cast_natCast, cast_le]

@[simp]

中文:
定理 floor_natCast
  条件: (n : 自然数)
  结论: ⌊(n : R)⌋ = n
  证明: eq_of_forall_le_iff fun a => by rw [le_floor, ← cast_natCast, cast_le]

@[simp]

Depends on / 依赖: cast_le, cast_natCast, eq_of_forall_le_iff, le_floor
-/
theorem floor_natCast (n : Nat) : ⌊(n : R)⌋ = n :=
  eq_of_forall_le_iff fun a => by rw [le_floor, ← cast_natCast, cast_le]

@[simp]
/--
theorem `floor_zero` / 定理 `floor_zero`

English:
theorem floor_zero
  statement: ⌊(0 : R)⌋ = 0
  proof: by rw [← cast_zero, floor_intCast]

@[simp]

中文:
定理 floor_zero
  结论: ⌊(0 : R)⌋ = 0
  证明: by rw [← cast_zero, floor_intCast]

@[simp]

Depends on / 依赖: cast_zero, floor_intCast
-/
theorem floor_zero : ⌊(0 : R)⌋ = 0 := by rw [← cast_zero, floor_intCast]

@[simp]
/--
theorem `floor_one` / 定理 `floor_one`

English:
theorem floor_one
  statement: ⌊(1 : R)⌋ = 1
  proof: by rw [← cast_one, floor_intCast]

中文:
定理 floor_one
  结论: ⌊(1 : R)⌋ = 1
  证明: by rw [← cast_one, floor_intCast]

Depends on / 依赖: cast_one, floor_intCast
-/
theorem floor_one : ⌊(1 : R)⌋ = 1 := by rw [← cast_one, floor_intCast]

/--
theorem `floor_ofNat` / 定理 `floor_ofNat`

English:
theorem floor_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ⌊(ofNat(n) : R)⌋ = ofNat(n)
  proof: floor_natCast n

@[simp, push]

中文:
定理 floor_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: ⌊(of自然数(n) : R)⌋ = of自然数(n)
  证明: floor_natCast n

@[simp, push]
-/
@[simp] theorem floor_ofNat (n : Nat) [n.AtLeastTwo] : ⌊(ofNat(n) : R)⌋ = ofNat(n) :=
  floor_natCast n

@[simp, push]
/--
theorem `floor_add_intCast` / 定理 `floor_add_intCast`

English:
theorem floor_add_intCast
  given: (a : R) (z : Int)
  statement: ⌊a + z⌋ = ⌊a⌋ + z
  proof: eq_of_forall_le_iff fun a => by
    rw [le_floor]; rw [← sub_le_iff_le_add]; rw [← sub_le_iff_le_add]; rw [le_floor]; rw [Int.cast_sub]

@[simp, push]

中文:
定理 floor_add_intCast
  条件: (a : R) (z : 整数)
  结论: ⌊a + z⌋ = ⌊a⌋ + z
  证明: eq_of_forall_le_iff fun a => by
    rw [le_floor]; rw [← sub_le_iff_le_add]; rw [← sub_le_iff_le_add]; rw [le_floor]; rw [Int.cast_sub]

@[simp, push]

Depends on / 依赖: Int.cast_sub, cast_sub, eq_of_forall_le_iff, le_floor, sub_le_iff_le_add
-/
theorem floor_add_intCast (a : R) (z : Int) : ⌊a + z⌋ = ⌊a⌋ + z :=
  eq_of_forall_le_iff fun a => by
    rw [le_floor]; rw [← sub_le_iff_le_add]; rw [← sub_le_iff_le_add]; rw [le_floor]; rw [Int.cast_sub]

@[simp, push]
/--
theorem `floor_add_one` / 定理 `floor_add_one`

English:
theorem floor_add_one
  given: (a : R)
  statement: ⌊a + 1⌋ = ⌊a⌋ + 1
  proof: by
  rw [← cast_one]; rw [floor_add_intCast]

@[bound]

中文:
定理 floor_add_one
  条件: (a : R)
  结论: ⌊a + 1⌋ = ⌊a⌋ + 1
  证明: by
  rw [← cast_one]; rw [floor_add_intCast]

@[bound]

Depends on / 依赖: cast_one, floor_add_intCast
-/
theorem floor_add_one (a : R) : ⌊a + 1⌋ = ⌊a⌋ + 1 := by
  rw [← cast_one]; rw [floor_add_intCast]

@[bound]
/--
theorem `le_floor_add` / 定理 `le_floor_add`

English:
theorem le_floor_add
  given: (a b : R)
  statement: ⌊a⌋ + ⌊b⌋ <= ⌊a + b⌋
  proof: by
  rw [le_floor]; rw [Int.cast_add]
  gcongr <;> apply floor_le

@[bound]

中文:
定理 le_floor_add
  条件: (a b : R)
  结论: ⌊a⌋ + ⌊b⌋ <= ⌊a + b⌋
  证明: by
  rw [le_floor]; rw [Int.cast_add]
  gcongr <;> apply floor_le

@[bound]

Depends on / 依赖: Int.cast_add, cast_add, floor_le, le_floor
-/
theorem le_floor_add (a b : R) : ⌊a⌋ + ⌊b⌋ <= ⌊a + b⌋ := by
  rw [le_floor]; rw [Int.cast_add]
  gcongr <;> apply floor_le

@[bound]
/--
theorem `le_floor_add_floor` / 定理 `le_floor_add_floor`

English:
theorem le_floor_add_floor
  given: (a b : R)
  statement: ⌊a + b⌋ - 1 <= ⌊a⌋ + ⌊b⌋
  proof: by
  rw [← sub_le_iff_le_add]; rw [le_floor]; rw [Int.cast_sub]; rw [sub_le_comm]; rw [Int.cast_sub]; rw [Int.cast_one]
  refine le_trans ?_ (sub_one_lt_floor _).le
  rw [sub_le_iff_le_add']; rw [← add_sub_assoc]; rw [sub_le_sub_iff_right]
  exact floor_le _

@[simp, push]

中文:
定理 le_floor_add_floor
  条件: (a b : R)
  结论: ⌊a + b⌋ - 1 <= ⌊a⌋ + ⌊b⌋
  证明: by
  rw [← sub_le_iff_le_add]; rw [le_floor]; rw [Int.cast_sub]; rw [sub_le_comm]; rw [Int.cast_sub]; rw [Int.cast_one]
  refine le_trans ?_ (sub_one_lt_floor _).le
  rw [sub_le_iff_le_add']; rw [← add_sub_assoc]; rw [sub_le_sub_iff_right]
  exact floor_le _

@[simp, push]

Depends on / 依赖: Int.cast_one, Int.cast_sub, add_sub_assoc, cast_one, cast_sub, floor_le, le_floor, le_trans, sub_le_comm, sub_le_iff_le_add, sub_le_sub_iff_right, sub_one_lt_floor
-/
theorem le_floor_add_floor (a b : R) : ⌊a + b⌋ - 1 <= ⌊a⌋ + ⌊b⌋ := by
  rw [← sub_le_iff_le_add]; rw [le_floor]; rw [Int.cast_sub]; rw [sub_le_comm]; rw [Int.cast_sub]; rw [Int.cast_one]
  refine le_trans ?_ (sub_one_lt_floor _).le
  rw [sub_le_iff_le_add']; rw [← add_sub_assoc]; rw [sub_le_sub_iff_right]
  exact floor_le _

@[simp, push]
/--
theorem `floor_intCast_add` / 定理 `floor_intCast_add`

English:
theorem floor_intCast_add
  given: (z : Int) (a : R)
  statement: ⌊↑z + a⌋ = z + ⌊a⌋
  proof: by
  simpa only [add_comm] using floor_add_intCast a z

@[simp, push]

中文:
定理 floor_intCast_add
  条件: (z : 整数) (a : R)
  结论: ⌊↑z + a⌋ = z + ⌊a⌋
  证明: by
  simpa only [add_comm] using floor_add_intCast a z

@[simp, push]

Depends on / 依赖: add_comm, floor_add_intCast
-/
theorem floor_intCast_add (z : Int) (a : R) : ⌊↑z + a⌋ = z + ⌊a⌋ := by
  simpa only [add_comm] using floor_add_intCast a z

@[simp, push]
/--
theorem `floor_add_natCast` / 定理 `floor_add_natCast`

English:
theorem floor_add_natCast
  given: (a : R) (n : Nat)
  statement: ⌊a + n⌋ = ⌊a⌋ + n
  proof: by
  rw [← Int.cast_natCast]; rw [floor_add_intCast]

@[simp, push]

中文:
定理 floor_add_natCast
  条件: (a : R) (n : 自然数)
  结论: ⌊a + n⌋ = ⌊a⌋ + n
  证明: by
  rw [← Int.cast_natCast]; rw [floor_add_intCast]

@[simp, push]

Depends on / 依赖: Int.cast_natCast, cast_natCast, floor_add_intCast
-/
theorem floor_add_natCast (a : R) (n : Nat) : ⌊a + n⌋ = ⌊a⌋ + n := by
  rw [← Int.cast_natCast]; rw [floor_add_intCast]

@[simp, push]
/--
theorem `floor_add_ofNat` / 定理 `floor_add_ofNat`

English:
theorem floor_add_ofNat
  given: (a : R) (n : Nat) [n.AtLeastTwo]
  proof: floor_add_natCast a n

@[simp, push]

中文:
定理 floor_add_of自然数
  条件: (a : R) (n : 自然数) [n.AtLeastTwo]
  证明: floor_add_natCast a n

@[simp, push]

Depends on / 依赖: floor_add_natCast
-/
theorem floor_add_ofNat (a : R) (n : Nat) [n.AtLeastTwo] :
    ⌊a + ofNat(n)⌋ = ⌊a⌋ + ofNat(n) :=
  floor_add_natCast a n

@[simp, push]
/--
theorem `floor_natCast_add` / 定理 `floor_natCast_add`

English:
theorem floor_natCast_add
  given: (n : Nat) (a : R)
  statement: ⌊↑n + a⌋ = n + ⌊a⌋
  proof: by
  rw [← Int.cast_natCast]; rw [floor_intCast_add]

@[simp, push]

中文:
定理 floor_natCast_add
  条件: (n : 自然数) (a : R)
  结论: ⌊↑n + a⌋ = n + ⌊a⌋
  证明: by
  rw [← Int.cast_natCast]; rw [floor_intCast_add]

@[simp, push]

Depends on / 依赖: Int.cast_natCast, cast_natCast, floor_intCast_add
-/
theorem floor_natCast_add (n : Nat) (a : R) : ⌊↑n + a⌋ = n + ⌊a⌋ := by
  rw [← Int.cast_natCast]; rw [floor_intCast_add]

@[simp, push]
/--
theorem `floor_ofNat_add` / 定理 `floor_ofNat_add`

English:
theorem floor_ofNat_add
  given: (n : Nat) [n.AtLeastTwo] (a : R)
  proof: floor_natCast_add n a

@[simp]

中文:
定理 floor_of自然数_add
  条件: (n : 自然数) [n.AtLeastTwo] (a : R)
  证明: floor_natCast_add n a

@[simp]

Depends on / 依赖: floor_natCast_add
-/
theorem floor_ofNat_add (n : Nat) [n.AtLeastTwo] (a : R) :
    ⌊ofNat(n) + a⌋ = ofNat(n) + ⌊a⌋ :=
  floor_natCast_add n a

@[simp]
/--
theorem `floor_sub_intCast` / 定理 `floor_sub_intCast`

English:
theorem floor_sub_intCast
  given: (a : R) (z : Int)
  statement: ⌊a - z⌋ = ⌊a⌋ - z
  proof: Eq.trans (by rw [Int.cast_neg, sub_eq_add_neg]) (floor_add_intCast _ _)

@[simp]

中文:
定理 floor_sub_intCast
  条件: (a : R) (z : 整数)
  结论: ⌊a - z⌋ = ⌊a⌋ - z
  证明: Eq.trans (by rw [Int.cast_neg, sub_eq_add_neg]) (floor_add_intCast _ _)

@[simp]

Depends on / 依赖: Eq.trans, Int.cast_neg, cast_neg, floor_add_intCast, sub_eq_add_neg
-/
theorem floor_sub_intCast (a : R) (z : Int) : ⌊a - z⌋ = ⌊a⌋ - z :=
  Eq.trans (by rw [Int.cast_neg, sub_eq_add_neg]) (floor_add_intCast _ _)

@[simp]
/--
theorem `floor_sub_natCast` / 定理 `floor_sub_natCast`

English:
theorem floor_sub_natCast
  given: (a : R) (n : Nat)
  statement: ⌊a - n⌋ = ⌊a⌋ - n
  proof: by
  rw [← Int.cast_natCast]; rw [floor_sub_intCast]

中文:
定理 floor_sub_natCast
  条件: (a : R) (n : 自然数)
  结论: ⌊a - n⌋ = ⌊a⌋ - n
  证明: by
  rw [← Int.cast_natCast]; rw [floor_sub_intCast]

Depends on / 依赖: Int.cast_natCast, cast_natCast, floor_sub_intCast
-/
theorem floor_sub_natCast (a : R) (n : Nat) : ⌊a - n⌋ = ⌊a⌋ - n := by
  rw [← Int.cast_natCast]; rw [floor_sub_intCast]

/--
theorem `floor_sub_one` / 定理 `floor_sub_one`

English:
theorem floor_sub_one
  given: (a : R)
  statement: ⌊a - 1⌋ = ⌊a⌋ - 1
  proof: mod_cast floor_sub_natCast a 1

@[simp]

中文:
定理 floor_sub_one
  条件: (a : R)
  结论: ⌊a - 1⌋ = ⌊a⌋ - 1
  证明: mod_cast floor_sub_natCast a 1

@[simp]
-/
@[simp] theorem floor_sub_one (a : R) : ⌊a - 1⌋ = ⌊a⌋ - 1 := mod_cast floor_sub_natCast a 1

@[simp]
/--
theorem `floor_sub_ofNat` / 定理 `floor_sub_ofNat`

English:
theorem floor_sub_ofNat
  given: (a : R) (n : Nat) [n.AtLeastTwo]
  proof: floor_sub_natCast a n

中文:
定理 floor_sub_of自然数
  条件: (a : R) (n : 自然数) [n.AtLeastTwo]
  证明: floor_sub_natCast a n

Depends on / 依赖: floor_sub_natCast
-/
theorem floor_sub_ofNat (a : R) (n : Nat) [n.AtLeastTwo] :
    ⌊a - ofNat(n)⌋ = ⌊a⌋ - ofNat(n) :=
  floor_sub_natCast a n

/--
theorem `abs_sub_lt_one_of_floor_eq_floor` / 定理 `abs_sub_lt_one_of_floor_eq_floor`

English:
theorem abs_sub_lt_one_of_floor_eq_floor
  given: {a b : R} (h : ⌊a⌋ = ⌊b⌋)
  statement: |a - b| < 1
  proof: by
  wlog h0 : b <= a generalizing a b
  · rw [abs_sub_comm]
    exact this h.symm (le_of_not_ge h0)
  calc |a - b|
    _ = a - b := abs_of_nonneg (sub_nonneg_of_le h0)
    _ < ⌊a⌋ + 1 - b := sub_lt_sub_right (lt_floor_add_one a) _
    _ <= ⌊a⌋ + 1 - ⌊b⌋ := sub_le_sub_left (floor_le b) _
    _ = 1 := by rw [h, add_sub_cancel_left]

中文:
定理 abs_sub_lt_one_of_floor_eq_floor
  条件: {a b : R} (h : ⌊a⌋ = ⌊b⌋)
  结论: |a - b| < 1
  证明: by
  wlog h0 : b <= a generalizing a b
  · rw [abs_sub_comm]
    exact this h.symm (le_of_not_ge h0)
  calc |a - b|
    _ = a - b := abs_of_nonneg (sub_nonneg_of_le h0)
    _ < ⌊a⌋ + 1 - b := sub_lt_sub_right (lt_floor_add_one a) _
    _ <= ⌊a⌋ + 1 - ⌊b⌋ := sub_le_sub_left (floor_le b) _
    _ = 1 := by rw [h, add_sub_cancel_left]

Depends on / 依赖: abs_of_nonneg, abs_sub_comm, add_sub_cancel_left, floor_le, generalizing, h.symm, le_of_not_ge, lt_floor_add_one, sub_le_sub_left, sub_lt_sub_right, sub_nonneg_of_le
-/
theorem abs_sub_lt_one_of_floor_eq_floor {a b : R} (h : ⌊a⌋ = ⌊b⌋) : |a - b| < 1 := by
  wlog h0 : b <= a generalizing a b
  · rw [abs_sub_comm]
    exact this h.symm (le_of_not_ge h0)
  calc |a - b|
    _ = a - b := abs_of_nonneg (sub_nonneg_of_le h0)
    _ < ⌊a⌋ + 1 - b := sub_lt_sub_right (lt_floor_add_one a) _
    _ <= ⌊a⌋ + 1 - ⌊b⌋ := sub_le_sub_left (floor_le b) _
    _ = 1 := by rw [h, add_sub_cancel_left]

/--
lemma `floor_eq_self_iff_mem` / 引理 `floor_eq_self_iff_mem`

English:
lemma floor_eq_self_iff_mem
  given: (a : R)
  statement: ⌊a⌋ = a ↔ a in Set.range Int.cast
  proof: by
  aesop

中文:
引理 floor_eq_self_iff_mem
  条件: (a : R)
  结论: ⌊a⌋ = a ↔ a in 集合.range 整数.cast
  证明: by
  aesop
-/
lemma floor_eq_self_iff_mem (a : R) : ⌊a⌋ = a ↔ a in Set.range Int.cast := by
  aesop

/--
theorem `floor_lt_self_iff` / 定理 `floor_lt_self_iff`

English:
theorem floor_lt_self_iff
  given: {a : R}
  statement: ⌊a⌋ < a ↔ a ∉ range Int.cast
  proof: (floor_le a).lt_iff_ne.trans (floor_eq_self_iff_mem _).not

中文:
定理 floor_lt_self_iff
  条件: {a : R}
  结论: ⌊a⌋ < a ↔ a ∉ range 整数.cast
  证明: (floor_le a).lt_iff_ne.trans (floor_eq_self_iff_mem _).not

Depends on / 依赖: floor_eq_self_iff_mem, floor_le, lt_iff_ne, lt_iff_ne.trans
-/
theorem floor_lt_self_iff {a : R} : ⌊a⌋ < a ↔ a ∉ range Int.cast :=
(floor_le a).lt_iff_ne.trans (floor_eq_self_iff_mem _).not

section LinearOrderedRing
variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] {a b : R}

/--
theorem `mul_cast_floor_div_cancel_of_pos` / 定理 `mul_cast_floor_div_cancel_of_pos`

English:
theorem mul_cast_floor_div_cancel_of_pos
  given: {n : Int} (hn : 0 < n) (a : R)
  statement: ⌊a * n⌋ / n = ⌊a⌋
  proof: by
  refine eq_of_forall_le_iff fun m => ?_
  rw [Int.le_ediv_iff_mul_le hn]; rw [le_floor]; rw [le_floor]; rw [cast_mul]; rw [mul_le_mul_iff_of_pos_right (cast_pos.mpr hn)]

中文:
定理 mul_cast_floor_div_cancel_of_pos
  条件: {n : 整数} (hn : 0 < n) (a : R)
  结论: ⌊a * n⌋ / n = ⌊a⌋
  证明: by
  refine eq_of_forall_le_iff fun m => ?_
  rw [Int.le_ediv_iff_mul_le hn]; rw [le_floor]; rw [le_floor]; rw [cast_mul]; rw [mul_le_mul_iff_of_pos_right (cast_pos.mpr hn)]

Depends on / 依赖: Int.le_ediv_iff_mul_le, cast_mul, cast_pos, cast_pos.mpr, eq_of_forall_le_iff, le_ediv_iff_mul_le, le_floor, mul_le_mul_iff_of_pos_right
-/
theorem mul_cast_floor_div_cancel_of_pos {n : Int} (hn : 0 < n) (a : R) : ⌊a * n⌋ / n = ⌊a⌋ := by
  refine eq_of_forall_le_iff fun m => ?_
  rw [Int.le_ediv_iff_mul_le hn]; rw [le_floor]; rw [le_floor]; rw [cast_mul]; rw [mul_le_mul_iff_of_pos_right (cast_pos.mpr hn)]

/--
theorem `mul_natCast_floor_div_cancel` / 定理 `mul_natCast_floor_div_cancel`

English:
theorem mul_natCast_floor_div_cancel
  given: {n : Nat} (hn : n != 0) (a : R)
  statement: ⌊a * n⌋ / n = ⌊a⌋
  proof: by
  simpa using mul_cast_floor_div_cancel_of_pos (n := n) (by positivity) a

中文:
定理 mul_natCast_floor_div_cancel
  条件: {n : 自然数} (hn : n != 0) (a : R)
  结论: ⌊a * n⌋ / n = ⌊a⌋
  证明: by
  simpa using mul_cast_floor_div_cancel_of_pos (n := n) (by positivity) a

Depends on / 依赖: mul_cast_floor_div_cancel_of_pos
-/
theorem mul_natCast_floor_div_cancel {n : Nat} (hn : n != 0) (a : R) : ⌊a * n⌋ / n = ⌊a⌋ := by
  simpa using mul_cast_floor_div_cancel_of_pos (n := n) (by positivity) a

/--
theorem `mul_fract_eq_one_iff_exists_int` / 定理 `mul_fract_eq_one_iff_exists_int`

English:
theorem mul_fract_eq_one_iff_exists_int
  given: {x : R} {k : R} (hk : 1 < k)
  proof: by
  rw [fract]; rw [mul_sub]; rw [sub_eq_iff_eq_add']
  refine ⟨fun hx => ⟨⌊x⌋, hx⟩, ?_⟩
  rintro ⟨n, hn⟩
  convert! hn
  have hk0 : 0 < (k : R) := zero_le_one.trans_lt hk
  rw [floor_eq_iff]; rw [← mul_le_mul_iff_right₀ hk0]; rw [← mul_lt_mul_iff_right₀ hk0]; rw [hn]
  simp [mul_add, hk]

中文:
定理 mul_fract_eq_one_iff_存在_int
  条件: {x : R} {k : R} (hk : 1 < k)
  证明: by
  rw [fract]; rw [mul_sub]; rw [sub_eq_iff_eq_add']
  refine ⟨fun hx => ⟨⌊x⌋, hx⟩, ?_⟩
  rintro ⟨n, hn⟩
  convert! hn
  have hk0 : 0 < (k : R) := zero_le_one.trans_lt hk
  rw [floor_eq_iff]; rw [← mul_le_mul_iff_right₀ hk0]; rw [← mul_lt_mul_iff_right₀ hk0]; rw [hn]
  simp [mul_add, hk]

Depends on / 依赖: convert, floor_eq_iff, mul_add, mul_sub, sub_eq_iff_eq_add, trans_lt, zero_le_one, zero_le_one.trans_lt
-/
theorem mul_fract_eq_one_iff_exists_int {x : R} {k : R} (hk : 1 < k) :
    k * fract x = 1 ↔ exists n : Int, k * x = k * n + 1 := by
  rw [fract]; rw [mul_sub]; rw [sub_eq_iff_eq_add']
  refine ⟨fun hx => ⟨⌊x⌋, hx⟩, ?_⟩
  rintro ⟨n, hn⟩
  convert! hn
  have hk0 : 0 < (k : R) := zero_le_one.trans_lt hk
  rw [floor_eq_iff]; rw [← mul_le_mul_iff_right₀ hk0]; rw [← mul_lt_mul_iff_right₀ hk0]; rw [hn]
  simp [mul_add, hk]

/--
theorem `cast_mul_floor_div_cancel_of_pos` / 定理 `cast_mul_floor_div_cancel_of_pos`

English:
theorem cast_mul_floor_div_cancel_of_pos
  given: {n : Int} (hn : 0 < n) (a : R)
  statement: ⌊n * a⌋ / n = ⌊a⌋
  proof: by
  rw [Commute.intCast_left]; rw [mul_cast_floor_div_cancel_of_pos hn]

中文:
定理 cast_mul_floor_div_cancel_of_pos
  条件: {n : 整数} (hn : 0 < n) (a : R)
  结论: ⌊n * a⌋ / n = ⌊a⌋
  证明: by
  rw [Commute.intCast_left]; rw [mul_cast_floor_div_cancel_of_pos hn]

Depends on / 依赖: Commute, Commute.intCast_left, intCast_left, mul_cast_floor_div_cancel_of_pos
-/
theorem cast_mul_floor_div_cancel_of_pos {n : Int} (hn : 0 < n) (a : R) : ⌊n * a⌋ / n = ⌊a⌋ := by
  rw [Commute.intCast_left]; rw [mul_cast_floor_div_cancel_of_pos hn]

/--
theorem `natCast_mul_floor_div_cancel` / 定理 `natCast_mul_floor_div_cancel`

English:
theorem natCast_mul_floor_div_cancel
  given: {n : Nat} (hn : n != 0) (a : R)
  statement: ⌊n * a⌋ / n = ⌊a⌋
  proof: by
  rw [Nat.cast_comm]; rw [mul_natCast_floor_div_cancel hn]

中文:
定理 natCast_mul_floor_div_cancel
  条件: {n : 自然数} (hn : n != 0) (a : R)
  结论: ⌊n * a⌋ / n = ⌊a⌋
  证明: by
  rw [Nat.cast_comm]; rw [mul_natCast_floor_div_cancel hn]

Depends on / 依赖: Nat.cast_comm, cast_comm, mul_natCast_floor_div_cancel
-/
theorem natCast_mul_floor_div_cancel {n : Nat} (hn : n != 0) (a : R) : ⌊n * a⌋ / n = ⌊a⌋ := by
  rw [Nat.cast_comm]; rw [mul_natCast_floor_div_cancel hn]

end LinearOrderedRing

section LinearOrderedField
variable {k : Type*} [Field k] [LinearOrder k] [IsOrderedRing k] [FloorRing k] {a b : k}

/--
theorem `floor_div_cast_of_nonneg` / 定理 `floor_div_cast_of_nonneg`

English:
theorem floor_div_cast_of_nonneg
  given: {n : Int} (hn : 0 <= n) (a : k)
  statement: ⌊a / n⌋ = ⌊a⌋ / n
  proof: by
  obtain rfl | hn := hn.eq_or_lt
  · simp
  nth_rw 2 [← div_mul_cancel₀ (a := a) (ne_of_gt (Int.cast_pos.mpr hn))]
  rw [mul_cast_floor_div_cancel_of_pos hn]

中文:
定理 floor_div_cast_of_nonneg
  条件: {n : 整数} (hn : 0 <= n) (a : k)
  结论: ⌊a / n⌋ = ⌊a⌋ / n
  证明: by
  obtain rfl | hn := hn.eq_or_lt
  · simp
  nth_rw 2 [← div_mul_cancel₀ (a := a) (ne_of_gt (Int.cast_pos.mpr hn))]
  rw [mul_cast_floor_div_cancel_of_pos hn]

Depends on / 依赖: Int.cast_pos.mpr, cast_pos, eq_or_lt, hn.eq_or_lt, mul_cast_floor_div_cancel_of_pos, ne_of_gt, nth_rw
-/
theorem floor_div_cast_of_nonneg {n : Int} (hn : 0 <= n) (a : k) : ⌊a / n⌋ = ⌊a⌋ / n := by
  obtain rfl | hn := hn.eq_or_lt
  · simp
  nth_rw 2 [← div_mul_cancel₀ (a := a) (ne_of_gt (Int.cast_pos.mpr hn))]
  rw [mul_cast_floor_div_cancel_of_pos hn]

/--
theorem `floor_div_natCast` / 定理 `floor_div_natCast`

English:
theorem floor_div_natCast
  given: (a : k) (n : Nat)
  statement: ⌊a / n⌋ = ⌊a⌋ / n
  proof: by
  simpa using floor_div_cast_of_nonneg n.cast_nonneg a

中文:
定理 floor_div_natCast
  条件: (a : k) (n : 自然数)
  结论: ⌊a / n⌋ = ⌊a⌋ / n
  证明: by
  simpa using floor_div_cast_of_nonneg n.cast_nonneg a

Depends on / 依赖: cast_nonneg, floor_div_cast_of_nonneg, n.cast_nonneg
-/
theorem floor_div_natCast (a : k) (n : Nat) : ⌊a / n⌋ = ⌊a⌋ / n := by
  simpa using floor_div_cast_of_nonneg n.cast_nonneg a

end LinearOrderedField

end floor

/-! #### Fractional part -/

section fract

@[simp]
/--
theorem `self_sub_floor` / 定理 `self_sub_floor`

English:
theorem self_sub_floor
  given: (a : R)
  statement: a - ⌊a⌋ = fract a
  proof: rfl

@[simp]

中文:
定理 self_sub_floor
  条件: (a : R)
  结论: a - ⌊a⌋ = fract a
  证明: rfl

@[simp]
-/
theorem self_sub_floor (a : R) : a - ⌊a⌋ = fract a :=
  rfl

@[simp]
/--
theorem `floor_add_fract` / 定理 `floor_add_fract`

English:
theorem floor_add_fract
  given: (a : R)
  statement: (⌊a⌋ : R) + fract a = a
  proof: add_sub_cancel _ _

@[simp]

中文:
定理 floor_add_fract
  条件: (a : R)
  结论: (⌊a⌋ : R) + fract a = a
  证明: add_sub_cancel _ _

@[simp]

Depends on / 依赖: add_sub_cancel
-/
theorem floor_add_fract (a : R) : (⌊a⌋ : R) + fract a = a :=
  add_sub_cancel _ _

@[simp]
/--
theorem `fract_add_floor` / 定理 `fract_add_floor`

English:
theorem fract_add_floor
  given: (a : R)
  statement: fract a + ⌊a⌋ = a
  proof: sub_add_cancel _ _

@[simp]

中文:
定理 fract_add_floor
  条件: (a : R)
  结论: fract a + ⌊a⌋ = a
  证明: sub_add_cancel _ _

@[simp]

Depends on / 依赖: sub_add_cancel
-/
theorem fract_add_floor (a : R) : fract a + ⌊a⌋ = a :=
  sub_add_cancel _ _

@[simp]
/--
theorem `self_sub_fract` / 定理 `self_sub_fract`

English:
theorem self_sub_fract
  given: (a : R)
  statement: a - fract a = ⌊a⌋
  proof: sub_sub_cancel _ _

@[simp]

中文:
定理 self_sub_fract
  条件: (a : R)
  结论: a - fract a = ⌊a⌋
  证明: sub_sub_cancel _ _

@[simp]

Depends on / 依赖: sub_sub_cancel
-/
theorem self_sub_fract (a : R) : a - fract a = ⌊a⌋ :=
  sub_sub_cancel _ _

@[simp]
/--
theorem `fract_sub_self` / 定理 `fract_sub_self`

English:
theorem fract_sub_self
  given: (a : R)
  statement: fract a - a = -⌊a⌋
  proof: sub_sub_cancel_left _ _

中文:
定理 fract_sub_self
  条件: (a : R)
  结论: fract a - a = -⌊a⌋
  证明: sub_sub_cancel_left _ _

Depends on / 依赖: sub_sub_cancel_left
-/
theorem fract_sub_self (a : R) : fract a - a = -⌊a⌋ :=
  sub_sub_cancel_left _ _

/--
theorem `fract_add` / 定理 `fract_add`

English:
theorem fract_add
  given: (a b : R)
  statement: exists z : Int, fract (a + b) - fract a - fract b = z
  proof: ⟨⌊a⌋ + ⌊b⌋ - ⌊a + b⌋, by unfold fract; grind⟩

中文:
定理 fract_add
  条件: (a b : R)
  结论: 存在 z : 整数, fract (a + b) - fract a - fract b = z
  证明: ⟨⌊a⌋ + ⌊b⌋ - ⌊a + b⌋, by unfold fract; grind⟩
-/
theorem fract_add (a b : R) : exists z : Int, fract (a + b) - fract a - fract b = z :=
  ⟨⌊a⌋ + ⌊b⌋ - ⌊a + b⌋, by unfold fract; grind⟩

variable [IsOrderedRing R]

@[simp]
/--
theorem `fract_add_intCast` / 定理 `fract_add_intCast`

English:
theorem fract_add_intCast
  given: (a : R) (m : Int)
  statement: fract (a + m) = fract a
  proof: by
  rw [fract]
  simp
@[simp]

中文:
定理 fract_add_intCast
  条件: (a : R) (m : 整数)
  结论: fract (a + m) = fract a
  证明: by
  rw [fract]
  simp
@[simp]
-/
theorem fract_add_intCast (a : R) (m : Int) : fract (a + m) = fract a := by
  rw [fract]
  simp
@[simp]
/--
theorem `fract_add_natCast` / 定理 `fract_add_natCast`

English:
theorem fract_add_natCast
  given: (a : R) (m : Nat)
  statement: fract (a + m) = fract a
  proof: by
  rw [fract]
  simp
@[simp]

中文:
定理 fract_add_natCast
  条件: (a : R) (m : 自然数)
  结论: fract (a + m) = fract a
  证明: by
  rw [fract]
  simp
@[simp]
-/
theorem fract_add_natCast (a : R) (m : Nat) : fract (a + m) = fract a := by
  rw [fract]
  simp
@[simp]
/--
theorem `fract_add_one` / 定理 `fract_add_one`

English:
theorem fract_add_one
  given: (a : R)
  statement: fract (a + 1) = fract a
  proof: mod_cast fract_add_natCast a 1

@[simp]

中文:
定理 fract_add_one
  条件: (a : R)
  结论: fract (a + 1) = fract a
  证明: mod_cast fract_add_natCast a 1

@[simp]

Depends on / 依赖: fract_add_natCast, mod_cast
-/
theorem fract_add_one (a : R) : fract (a + 1) = fract a := mod_cast fract_add_natCast a 1

@[simp]
/--
theorem `fract_add_ofNat` / 定理 `fract_add_ofNat`

English:
theorem fract_add_ofNat
  given: (a : R) (n : Nat) [n.AtLeastTwo]
  proof: fract_add_natCast a n

@[simp]

中文:
定理 fract_add_of自然数
  条件: (a : R) (n : 自然数) [n.AtLeastTwo]
  证明: fract_add_natCast a n

@[simp]

Depends on / 依赖: fract_add_natCast
-/
theorem fract_add_ofNat (a : R) (n : Nat) [n.AtLeastTwo] :
    fract (a + ofNat(n)) = fract a :=
  fract_add_natCast a n

@[simp]
/--
theorem `fract_intCast_add` / 定理 `fract_intCast_add`

English:
theorem fract_intCast_add
  given: (m : Int) (a : R)
  statement: fract (↑m + a) = fract a
  proof: by
  rw [add_comm]; rw [fract_add_intCast]
@[simp]

中文:
定理 fract_intCast_add
  条件: (m : 整数) (a : R)
  结论: fract (↑m + a) = fract a
  证明: by
  rw [add_comm]; rw [fract_add_intCast]
@[simp]

Depends on / 依赖: add_comm, fract_add_intCast
-/
theorem fract_intCast_add (m : Int) (a : R) : fract (↑m + a) = fract a := by
  rw [add_comm]; rw [fract_add_intCast]
@[simp]
/--
theorem `fract_natCast_add` / 定理 `fract_natCast_add`

English:
theorem fract_natCast_add
  given: (n : Nat) (a : R)
  statement: fract (↑n + a) = fract a
  proof: by
  rw [add_comm]; rw [fract_add_natCast]
@[simp]

中文:
定理 fract_natCast_add
  条件: (n : 自然数) (a : R)
  结论: fract (↑n + a) = fract a
  证明: by
  rw [add_comm]; rw [fract_add_natCast]
@[simp]

Depends on / 依赖: add_comm, fract_add_natCast
-/
theorem fract_natCast_add (n : Nat) (a : R) : fract (↑n + a) = fract a := by
  rw [add_comm]; rw [fract_add_natCast]
@[simp]
/--
theorem `fract_one_add` / 定理 `fract_one_add`

English:
theorem fract_one_add
  given: (a : R)
  statement: fract (1 + a) = fract a
  proof: mod_cast fract_natCast_add 1 a

@[simp]

中文:
定理 fract_one_add
  条件: (a : R)
  结论: fract (1 + a) = fract a
  证明: mod_cast fract_natCast_add 1 a

@[simp]

Depends on / 依赖: fract_natCast_add, mod_cast
-/
theorem fract_one_add (a : R) : fract (1 + a) = fract a := mod_cast fract_natCast_add 1 a

@[simp]
/--
theorem `fract_ofNat_add` / 定理 `fract_ofNat_add`

English:
theorem fract_ofNat_add
  given: (n : Nat) [n.AtLeastTwo] (a : R)
  proof: fract_natCast_add n a

@[simp]

中文:
定理 fract_of自然数_add
  条件: (n : 自然数) [n.AtLeastTwo] (a : R)
  证明: fract_natCast_add n a

@[simp]

Depends on / 依赖: fract_natCast_add
-/
theorem fract_ofNat_add (n : Nat) [n.AtLeastTwo] (a : R) :
    fract (ofNat(n) + a) = fract a :=
  fract_natCast_add n a

@[simp]
/--
theorem `fract_sub_intCast` / 定理 `fract_sub_intCast`

English:
theorem fract_sub_intCast
  given: (a : R) (m : Int)
  statement: fract (a - m) = fract a
  proof: by
  rw [fract]
  simp
@[simp]

中文:
定理 fract_sub_intCast
  条件: (a : R) (m : 整数)
  结论: fract (a - m) = fract a
  证明: by
  rw [fract]
  simp
@[simp]
-/
theorem fract_sub_intCast (a : R) (m : Int) : fract (a - m) = fract a := by
  rw [fract]
  simp
@[simp]
/--
theorem `fract_sub_natCast` / 定理 `fract_sub_natCast`

English:
theorem fract_sub_natCast
  given: (a : R) (n : Nat)
  statement: fract (a - n) = fract a
  proof: by
  rw [fract]
  simp
@[simp]

中文:
定理 fract_sub_natCast
  条件: (a : R) (n : 自然数)
  结论: fract (a - n) = fract a
  证明: by
  rw [fract]
  simp
@[simp]
-/
theorem fract_sub_natCast (a : R) (n : Nat) : fract (a - n) = fract a := by
  rw [fract]
  simp
@[simp]
/--
theorem `fract_sub_one` / 定理 `fract_sub_one`

English:
theorem fract_sub_one
  given: (a : R)
  statement: fract (a - 1) = fract a
  proof: mod_cast fract_sub_natCast a 1

@[simp]

中文:
定理 fract_sub_one
  条件: (a : R)
  结论: fract (a - 1) = fract a
  证明: mod_cast fract_sub_natCast a 1

@[simp]

Depends on / 依赖: fract_sub_natCast, mod_cast
-/
theorem fract_sub_one (a : R) : fract (a - 1) = fract a := mod_cast fract_sub_natCast a 1

@[simp]
/--
theorem `fract_sub_ofNat` / 定理 `fract_sub_ofNat`

English:
theorem fract_sub_ofNat
  given: (a : R) (n : Nat) [n.AtLeastTwo]
  proof: fract_sub_natCast a n

中文:
定理 fract_sub_of自然数
  条件: (a : R) (n : 自然数) [n.AtLeastTwo]
  证明: fract_sub_natCast a n

Depends on / 依赖: fract_sub_natCast
-/
theorem fract_sub_ofNat (a : R) (n : Nat) [n.AtLeastTwo] :
    fract (a - ofNat(n)) = fract a :=
  fract_sub_natCast a n

-- Was a duplicate lemma under a bad name

/--
theorem `fract_add_le` / 定理 `fract_add_le`

English:
theorem fract_add_le
  given: (a b : R)
  statement: fract (a + b) <= fract a + fract b
  proof: by
  rw [fract]; rw [fract]; rw [fract]; rw [sub_add_sub_comm]; rw [sub_le_sub_iff_left]; rw [← Int.cast_add]; rw [Int.cast_le]
  exact le_floor_add _ _

中文:
定理 fract_add_le
  条件: (a b : R)
  结论: fract (a + b) <= fract a + fract b
  证明: by
  rw [fract]; rw [fract]; rw [fract]; rw [sub_add_sub_comm]; rw [sub_le_sub_iff_left]; rw [← Int.cast_add]; rw [Int.cast_le]
  exact le_floor_add _ _

Depends on / 依赖: Int.cast_add, Int.cast_le, cast_add, cast_le, le_floor_add, sub_add_sub_comm, sub_le_sub_iff_left
-/
theorem fract_add_le (a b : R) : fract (a + b) <= fract a + fract b := by
  rw [fract]; rw [fract]; rw [fract]; rw [sub_add_sub_comm]; rw [sub_le_sub_iff_left]; rw [← Int.cast_add]; rw [Int.cast_le]
  exact le_floor_add _ _

/--
theorem `fract_add_fract_le` / 定理 `fract_add_fract_le`

English:
theorem fract_add_fract_le
  given: (a b : R)
  statement: fract a + fract b <= fract (a + b) + 1
  proof: by
  rw [fract]; rw [fract]; rw [fract]; rw [sub_add_sub_comm]; rw [sub_add]; rw [sub_le_sub_iff_left]
  exact mod_cast le_floor_add_floor a b

@[simp]

中文:
定理 fract_add_fract_le
  条件: (a b : R)
  结论: fract a + fract b <= fract (a + b) + 1
  证明: by
  rw [fract]; rw [fract]; rw [fract]; rw [sub_add_sub_comm]; rw [sub_add]; rw [sub_le_sub_iff_left]
  exact mod_cast le_floor_add_floor a b

@[simp]

Depends on / 依赖: le_floor_add_floor, mod_cast, sub_add, sub_add_sub_comm, sub_le_sub_iff_left
-/
theorem fract_add_fract_le (a b : R) : fract a + fract b <= fract (a + b) + 1 := by
  rw [fract]; rw [fract]; rw [fract]; rw [sub_add_sub_comm]; rw [sub_add]; rw [sub_le_sub_iff_left]
  exact mod_cast le_floor_add_floor a b

@[simp]
/--
theorem `fract_nonneg` / 定理 `fract_nonneg`

English:
theorem fract_nonneg
  given: (a : R)
  statement: 0 <= fract a
  proof: sub_nonneg.2 floor_le _

中文:
定理 fract_nonneg
  条件: (a : R)
  结论: 0 <= fract a
  证明: sub_nonneg.2 floor_le _

Depends on / 依赖: floor_le, sub_nonneg
-/
theorem fract_nonneg (a : R) : 0 <= fract a :=
sub_nonneg.2 floor_le _

/--
lemma `fract_pos` / 引理 `fract_pos`

English:
lemma fract_pos
  statement: 0 < fract a ↔ a != ⌊a⌋
  proof: (fract_nonneg a).lt_iff_ne.trans ne_comm.trans sub_ne_zero

中文:
引理 fract_pos
  结论: 0 < fract a ↔ a != ⌊a⌋
  证明: (fract_nonneg a).lt_iff_ne.trans ne_comm.trans sub_ne_zero

Depends on / 依赖: fract_nonneg, lt_iff_ne, lt_iff_ne.trans, ne_comm, ne_comm.trans, sub_ne_zero
-/
lemma fract_pos : 0 < fract a ↔ a != ⌊a⌋ :=
(fract_nonneg a).lt_iff_ne.trans ne_comm.trans sub_ne_zero

/--
theorem `fract_lt_one` / 定理 `fract_lt_one`

English:
theorem fract_lt_one
  given: (a : R)
  statement: fract a < 1
  proof: sub_lt_comm.1 sub_one_lt_floor _

@[simp]

中文:
定理 fract_lt_one
  条件: (a : R)
  结论: fract a < 1
  证明: sub_lt_comm.1 sub_one_lt_floor _

@[simp]

Depends on / 依赖: sub_lt_comm, sub_one_lt_floor
-/
theorem fract_lt_one (a : R) : fract a < 1 :=
sub_lt_comm.1 sub_one_lt_floor _

@[simp]
/--
theorem `fract_zero` / 定理 `fract_zero`

English:
theorem fract_zero
  statement: fract (0 : R) = 0
  proof: by rw [fract, floor_zero, cast_zero, sub_self]

@[simp]

中文:
定理 fract_zero
  结论: fract (0 : R) = 0
  证明: by rw [fract, floor_zero, cast_zero, sub_self]

@[simp]

Depends on / 依赖: cast_zero, floor_zero, sub_self
-/
theorem fract_zero : fract (0 : R) = 0 := by rw [fract, floor_zero, cast_zero, sub_self]

@[simp]
/--
theorem `fract_one` / 定理 `fract_one`

English:
theorem fract_one
  statement: fract (1 : R) = 0
  proof: by simp [fract]

中文:
定理 fract_one
  结论: fract (1 : R) = 0
  证明: by simp [fract]
-/
theorem fract_one : fract (1 : R) = 0 := by simp [fract]

/--
theorem `abs_fract` / 定理 `abs_fract`

English:
theorem abs_fract
  statement: |fract a| = fract a
  proof: abs_eq_self.mpr fract_nonneg a

@[simp]

中文:
定理 abs_fract
  结论: |fract a| = fract a
  证明: abs_eq_self.mpr fract_nonneg a

@[simp]

Depends on / 依赖: abs_eq_self, abs_eq_self.mpr, fract_nonneg
-/
theorem abs_fract : |fract a| = fract a :=
abs_eq_self.mpr fract_nonneg a

@[simp]
/--
theorem `abs_one_sub_fract` / 定理 `abs_one_sub_fract`

English:
theorem abs_one_sub_fract
  statement: |1 - fract a| = 1 - fract a
  proof: abs_eq_self.mpr sub_nonneg.mpr (fract_lt_one a).le

@[simp]

中文:
定理 abs_one_sub_fract
  结论: |1 - fract a| = 1 - fract a
  证明: abs_eq_self.mpr sub_nonneg.mpr (fract_lt_one a).le

@[simp]

Depends on / 依赖: abs_eq_self, abs_eq_self.mpr, fract_lt_one, sub_nonneg, sub_nonneg.mpr
-/
theorem abs_one_sub_fract : |1 - fract a| = 1 - fract a :=
abs_eq_self.mpr sub_nonneg.mpr (fract_lt_one a).le

@[simp]
/--
theorem `fract_intCast` / 定理 `fract_intCast`

English:
theorem fract_intCast
  given: (z : Int)
  statement: fract (z : R) = 0
  proof: by
  unfold fract
  rw [floor_intCast]
  exact sub_self _

@[simp]

中文:
定理 fract_intCast
  条件: (z : 整数)
  结论: fract (z : R) = 0
  证明: by
  unfold fract
  rw [floor_intCast]
  exact sub_self _

@[simp]

Depends on / 依赖: floor_intCast, sub_self
-/
theorem fract_intCast (z : Int) : fract (z : R) = 0 := by
  unfold fract
  rw [floor_intCast]
  exact sub_self _

@[simp]
/--
theorem `fract_natCast` / 定理 `fract_natCast`

English:
theorem fract_natCast
  given: (n : Nat)
  statement: fract (n : R) = 0
  proof: by simp [fract]

@[simp]

中文:
定理 fract_natCast
  条件: (n : 自然数)
  结论: fract (n : R) = 0
  证明: by simp [fract]

@[simp]
-/
theorem fract_natCast (n : Nat) : fract (n : R) = 0 := by simp [fract]

@[simp]
/--
theorem `fract_ofNat` / 定理 `fract_ofNat`

English:
theorem fract_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: fract_natCast n

中文:
定理 fract_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: fract_natCast n

Depends on / 依赖: fract_natCast
-/
theorem fract_ofNat (n : Nat) [n.AtLeastTwo] :
    fract (ofNat(n) : R) = 0 :=
  fract_natCast n

/--
theorem `fract_floor` / 定理 `fract_floor`

English:
theorem fract_floor
  given: (a : R)
  statement: fract (⌊a⌋ : R) = 0
  proof: fract_intCast _

@[simp]

中文:
定理 fract_floor
  条件: (a : R)
  结论: fract (⌊a⌋ : R) = 0
  证明: fract_intCast _

@[simp]

Depends on / 依赖: fract_intCast
-/
theorem fract_floor (a : R) : fract (⌊a⌋ : R) = 0 :=
  fract_intCast _

@[simp]
/--
theorem `floor_fract` / 定理 `floor_fract`

English:
theorem floor_fract
  given: (a : R)
  statement: ⌊fract a⌋ = 0
  proof: by
  rw [floor_eq_iff]; rw [Int.cast_zero]; rw [zero_add]; exact ⟨fract_nonneg _, fract_lt_one _⟩

中文:
定理 floor_fract
  条件: (a : R)
  结论: ⌊fract a⌋ = 0
  证明: by
  rw [floor_eq_iff]; rw [Int.cast_zero]; rw [zero_add]; exact ⟨fract_nonneg _, fract_lt_one _⟩

Depends on / 依赖: Int.cast_zero, cast_zero, floor_eq_iff, fract_lt_one, fract_nonneg, zero_add
-/
theorem floor_fract (a : R) : ⌊fract a⌋ = 0 := by
  rw [floor_eq_iff]; rw [Int.cast_zero]; rw [zero_add]; exact ⟨fract_nonneg _, fract_lt_one _⟩

/--
theorem `fract_eq_iff` / 定理 `fract_eq_iff`

English:
theorem fract_eq_iff
  given: {a b : R}
  statement: fract a = b ↔ 0 <= b ∧ b < 1 ∧ exists z : Int, a - b = z
  proof: ⟨fun h => by
    rw [← h]
    exact ⟨fract_nonneg _, fract_lt_one _, ⟨⌊a⌋, sub_sub_cancel _ _⟩⟩,
   by
    rintro ⟨h₀, h₁, z, hz⟩
    rw [← self_sub_floor]; rw [eq_comm]; rw [eq_sub_iff_add_eq]; rw [add_comm]; rw [← eq_sub_iff_add_eq]; rw [hz]
    refine congrArg Int.cast ?_
    rw [floor_eq_iff]; rw [← hz]
    constructor <;> simpa [sub_eq_add_neg, add_assoc] ⟩

中文:
定理 fract_eq_iff
  条件: {a b : R}
  结论: fract a = b ↔ 0 <= b ∧ b < 1 ∧ 存在 z : 整数, a - b = z
  证明: ⟨fun h => by
    rw [← h]
    exact ⟨fract_nonneg _, fract_lt_one _, ⟨⌊a⌋, sub_sub_cancel _ _⟩⟩,
   by
    rintro ⟨h₀, h₁, z, hz⟩
    rw [← self_sub_floor]; rw [eq_comm]; rw [eq_sub_iff_add_eq]; rw [add_comm]; rw [← eq_sub_iff_add_eq]; rw [hz]
    refine congrArg Int.cast ?_
    rw [floor_eq_iff]; rw [← hz]
    constructor <;> simpa [sub_eq_add_neg, add_assoc] ⟩

Depends on / 依赖: Int.cast, add_assoc, add_comm, eq_comm, eq_sub_iff_add_eq, floor_eq_iff, fract_lt_one, fract_nonneg, self_sub_floor, sub_eq_add_neg, sub_sub_cancel
-/
theorem fract_eq_iff {a b : R} : fract a = b ↔ 0 <= b ∧ b < 1 ∧ exists z : Int, a - b = z :=
  ⟨fun h => by
    rw [← h]
    exact ⟨fract_nonneg _, fract_lt_one _, ⟨⌊a⌋, sub_sub_cancel _ _⟩⟩,
   by
    rintro ⟨h₀, h₁, z, hz⟩
    rw [← self_sub_floor]; rw [eq_comm]; rw [eq_sub_iff_add_eq]; rw [add_comm]; rw [← eq_sub_iff_add_eq]; rw [hz]
    refine congrArg Int.cast ?_
    rw [floor_eq_iff]; rw [← hz]
    constructor <;> simpa [sub_eq_add_neg, add_assoc] ⟩

/--
theorem `fract_eq_fract` / 定理 `fract_eq_fract`

English:
theorem fract_eq_fract
  given: {a b : R}
  statement: fract a = fract b ↔ exists z : Int, a - b = z
  proof: ⟨fun h => ⟨⌊a⌋ - ⌊b⌋, by unfold fract at h; rw [Int.cast_sub, sub_eq_sub_iff_sub_eq_sub.1 h]⟩,
   by
    rintro ⟨z, hz⟩
    refine fract_eq_iff.2 ⟨fract_nonneg _, fract_lt_one _, z + ⌊b⌋, ?_⟩
    rw [eq_add_of_sub_eq hz]; rw [add_comm]; rw [Int.cast_add]
    exact add_sub_sub_cancel _ _ _⟩

@[simp]

中文:
定理 fract_eq_fract
  条件: {a b : R}
  结论: fract a = fract b ↔ 存在 z : 整数, a - b = z
  证明: ⟨fun h => ⟨⌊a⌋ - ⌊b⌋, by unfold fract at h; rw [Int.cast_sub, sub_eq_sub_iff_sub_eq_sub.1 h]⟩,
   by
    rintro ⟨z, hz⟩
    refine fract_eq_iff.2 ⟨fract_nonneg _, fract_lt_one _, z + ⌊b⌋, ?_⟩
    rw [eq_add_of_sub_eq hz]; rw [add_comm]; rw [Int.cast_add]
    exact add_sub_sub_cancel _ _ _⟩

@[simp]

Depends on / 依赖: Int.cast_add, Int.cast_sub, add_comm, add_sub_sub_cancel, cast_add, cast_sub, eq_add_of_sub_eq, fract_eq_iff, fract_lt_one, fract_nonneg, sub_eq_sub_iff_sub_eq_sub
-/
theorem fract_eq_fract {a b : R} : fract a = fract b ↔ exists z : Int, a - b = z :=
  ⟨fun h => ⟨⌊a⌋ - ⌊b⌋, by unfold fract at h; rw [Int.cast_sub, sub_eq_sub_iff_sub_eq_sub.1 h]⟩,
   by
    rintro ⟨z, hz⟩
    refine fract_eq_iff.2 ⟨fract_nonneg _, fract_lt_one _, z + ⌊b⌋, ?_⟩
    rw [eq_add_of_sub_eq hz]; rw [add_comm]; rw [Int.cast_add]
    exact add_sub_sub_cancel _ _ _⟩

@[simp]
/--
theorem `fract_eq_self` / 定理 `fract_eq_self`

English:
theorem fract_eq_self
  given: {a : R}
  statement: fract a = a ↔ 0 <= a ∧ a < 1
  proof: fract_eq_iff.trans and_assoc.symm.trans and_iff_left ⟨0, by simp⟩

@[simp]

中文:
定理 fract_eq_self
  条件: {a : R}
  结论: fract a = a ↔ 0 <= a ∧ a < 1
  证明: fract_eq_iff.trans and_assoc.symm.trans and_iff_left ⟨0, by simp⟩

@[simp]

Depends on / 依赖: and_assoc, and_assoc.symm.trans, and_iff_left, fract_eq_iff, fract_eq_iff.trans
-/
theorem fract_eq_self {a : R} : fract a = a ↔ 0 <= a ∧ a < 1 :=
fract_eq_iff.trans and_assoc.symm.trans and_iff_left ⟨0, by simp⟩

@[simp]
/--
theorem `fract_fract` / 定理 `fract_fract`

English:
theorem fract_fract
  given: (a : R)
  statement: fract (fract a) = fract a
  proof: fract_eq_self.2 ⟨fract_nonneg _, fract_lt_one _⟩

中文:
定理 fract_fract
  条件: (a : R)
  结论: fract (fract a) = fract a
  证明: fract_eq_self.2 ⟨fract_nonneg _, fract_lt_one _⟩

Depends on / 依赖: fract_eq_self, fract_lt_one, fract_nonneg, h.symm
-/
theorem fract_fract (a : R) : fract (fract a) = fract a :=
  fract_eq_self.2 ⟨fract_nonneg _, fract_lt_one _⟩

/--
theorem `fract_eq_zero_iff` / 定理 `fract_eq_zero_iff`

English:
theorem fract_eq_zero_iff
  given: {a : R}
  statement: fract a = 0 ↔ a in range Int.cast
  proof: by
  simp [fract_eq_iff, eq_comm]

中文:
定理 fract_eq_zero_iff
  条件: {a : R}
  结论: fract a = 0 ↔ a in range 整数.cast
  证明: by
  simp [fract_eq_iff, eq_comm]

Depends on / 依赖: eq_comm, fract_eq_iff
-/
theorem fract_eq_zero_iff {a : R} : fract a = 0 ↔ a in range Int.cast := by
  simp [fract_eq_iff, eq_comm]

/--
theorem `fract_ne_zero_iff` / 定理 `fract_ne_zero_iff`

English:
theorem fract_ne_zero_iff
  given: {a : R}
  statement: fract a != 0 ↔ a ∉ range Int.cast
  proof: fract_eq_zero_iff.not

中文:
定理 fract_ne_zero_iff
  条件: {a : R}
  结论: fract a != 0 ↔ a ∉ range 整数.cast
  证明: fract_eq_zero_iff.not

Depends on / 依赖: fract_eq_zero_iff, fract_eq_zero_iff.not
-/
theorem fract_ne_zero_iff {a : R} : fract a != 0 ↔ a ∉ range Int.cast :=
  fract_eq_zero_iff.not

/--
theorem `fract_neg` / 定理 `fract_neg`

English:
theorem fract_neg
  given: {x : R} (hx : fract x != 0)
  statement: fract (-x) = 1 - fract x
  proof: by
  rw [fract_eq_iff]
  constructor
  · rw [le_sub_iff_add_le, zero_add]
    exact (fract_lt_one x).le
  refine ⟨sub_lt_self _ (lt_of_le_of_ne' (fract_nonneg x) hx), -⌊x⌋ - 1, ?_⟩
  simp only [sub_sub_eq_add_sub, cast_sub, cast_neg, cast_one, sub_left_inj]
  conv in -x => rw [← floor_add_fract x]
  simp [-floor_add_fract]

@[simp]

中文:
定理 fract_neg
  条件: {x : R} (hx : fract x != 0)
  结论: fract (-x) = 1 - fract x
  证明: by
  rw [fract_eq_iff]
  constructor
  · rw [le_sub_iff_add_le, zero_add]
    exact (fract_lt_one x).le
  refine ⟨sub_lt_self _ (lt_of_le_of_ne' (fract_nonneg x) hx), -⌊x⌋ - 1, ?_⟩
  simp only [sub_sub_eq_add_sub, cast_sub, cast_neg, cast_one, sub_left_inj]
  conv in -x => rw [← floor_add_fract x]
  simp [-floor_add_fract]

@[simp]

Depends on / 依赖: cast_neg, cast_one, cast_sub, floor_add_fract, fract_eq_iff, fract_lt_one, fract_nonneg, le_sub_iff_add_le, lt_of_le_of_ne, sub_left_inj, sub_lt_self, sub_sub_eq_add_sub, zero_add
-/
theorem fract_neg {x : R} (hx : fract x != 0) : fract (-x) = 1 - fract x := by
  rw [fract_eq_iff]
  constructor
  · rw [le_sub_iff_add_le, zero_add]
    exact (fract_lt_one x).le
  refine ⟨sub_lt_self _ (lt_of_le_of_ne' (fract_nonneg x) hx), -⌊x⌋ - 1, ?_⟩
  simp only [sub_sub_eq_add_sub, cast_sub, cast_neg, cast_one, sub_left_inj]
  conv in -x => rw [← floor_add_fract x]
  simp [-floor_add_fract]

@[simp]
/--
theorem `fract_neg_eq_zero` / 定理 `fract_neg_eq_zero`

English:
theorem fract_neg_eq_zero
  given: {x : R}
  statement: fract (-x) = 0 ↔ fract x = 0
  proof: by
  simp only [fract_eq_iff, le_refl, zero_lt_one, tsub_zero, true_and]
  constructor <;> rintro ⟨z, hz⟩ <;> use -z <;> simp [← hz]

中文:
定理 fract_neg_eq_zero
  条件: {x : R}
  结论: fract (-x) = 0 ↔ fract x = 0
  证明: by
  simp only [fract_eq_iff, le_refl, zero_lt_one, tsub_zero, true_and]
  constructor <;> rintro ⟨z, hz⟩ <;> use -z <;> simp [← hz]

Depends on / 依赖: fract_eq_iff, le_refl, true_and, tsub_zero, zero_lt_one
-/
theorem fract_neg_eq_zero {x : R} : fract (-x) = 0 ↔ fract x = 0 := by
  simp only [fract_eq_iff, le_refl, zero_lt_one, tsub_zero, true_and]
  constructor <;> rintro ⟨z, hz⟩ <;> use -z <;> simp [← hz]

/--
theorem `fract_mul_natCast` / 定理 `fract_mul_natCast`

English:
theorem fract_mul_natCast
  given: (a : R) (b : Nat)
  statement: exists z : Int, fract a * b - fract (a * b) = z
  proof: by
  induction b with
  | zero => use 0; simp
  | succ c hc =>
    rcases hc with ⟨z, hz⟩
    rw [Nat.cast_add]; rw [mul_add]; rw [mul_add]; rw [Nat.cast_one]; rw [mul_one]; rw [mul_one]
    rcases fract_add (a * c) a with ⟨y, hy⟩
    use z - y
    rw [Int.cast_sub]; rw [← hz]; rw [← hy]
    abel

中文:
定理 fract_mul_natCast
  条件: (a : R) (b : 自然数)
  结论: 存在 z : 整数, fract a * b - fract (a * b) = z
  证明: by
  induction b with
  | zero => use 0; simp
  | succ c hc =>
    rcases hc with ⟨z, hz⟩
    rw [Nat.cast_add]; rw [mul_add]; rw [mul_add]; rw [Nat.cast_one]; rw [mul_one]; rw [mul_one]
    rcases fract_add (a * c) a with ⟨y, hy⟩
    use z - y
    rw [Int.cast_sub]; rw [← hz]; rw [← hy]
    abel

Depends on / 依赖: Int.cast_sub, Nat.cast_add, Nat.cast_one, cast_add, cast_one, cast_sub, fract_add, mul_add, mul_one
-/
theorem fract_mul_natCast (a : R) (b : Nat) : exists z : Int, fract a * b - fract (a * b) = z := by
  induction b with
  | zero => use 0; simp
  | succ c hc =>
    rcases hc with ⟨z, hz⟩
    rw [Nat.cast_add]; rw [mul_add]; rw [mul_add]; rw [Nat.cast_one]; rw [mul_one]; rw [mul_one]
    rcases fract_add (a * c) a with ⟨y, hy⟩
    use z - y
    rw [Int.cast_sub]; rw [← hz]; rw [← hy]
    abel

/--
theorem `preimage_fract` / 定理 `preimage_fract`

English:
theorem preimage_fract
  given: (s : Set R)
  proof: by
  ext x
  simp only [mem_preimage, mem_iUnion, mem_inter_iff]
  refine ⟨fun h => ⟨⌊x⌋, h, fract_nonneg x, fract_lt_one x⟩, ?_⟩
  rintro ⟨m, hms, hm0, hm1⟩
  obtain rfl : ⌊x⌋ = m := floor_eq_iff.2 ⟨sub_nonneg.1 hm0, sub_lt_iff_lt_add'.1 hm1⟩
  exact hms

中文:
定理 preimage_fract
  条件: (s : 集合 R)
  证明: by
  ext x
  simp only [mem_preimage, mem_iUnion, mem_inter_iff]
  refine ⟨fun h => ⟨⌊x⌋, h, fract_nonneg x, fract_lt_one x⟩, ?_⟩
  rintro ⟨m, hms, hm0, hm1⟩
  obtain rfl : ⌊x⌋ = m := floor_eq_iff.2 ⟨sub_nonneg.1 hm0, sub_lt_iff_lt_add'.1 hm1⟩
  exact hms

Depends on / 依赖: floor_eq_iff, fract_lt_one, fract_nonneg, mem_iUnion, mem_inter_iff, mem_preimage, sub_lt_iff_lt_add, sub_nonneg
-/
theorem preimage_fract (s : Set R) :
    fract ⁻¹' s = ⋃ m : Int, (fun x => x - (m : R)) ⁻¹' (s inter Ico (0 : R) 1) := by
  ext x
  simp only [mem_preimage, mem_iUnion, mem_inter_iff]
  refine ⟨fun h => ⟨⌊x⌋, h, fract_nonneg x, fract_lt_one x⟩, ?_⟩
  rintro ⟨m, hms, hm0, hm1⟩
  obtain rfl : ⌊x⌋ = m := floor_eq_iff.2 ⟨sub_nonneg.1 hm0, sub_lt_iff_lt_add'.1 hm1⟩
  exact hms

/--
theorem `image_fract` / 定理 `image_fract`

English:
theorem image_fract
  given: (s : Set R)
  statement: fract '' s = ⋃ m : Int, (fun x : R => x - m) '' s inter Ico 0 1
  proof: by
  ext x
  simp only [mem_image, mem_inter_iff, mem_iUnion]; constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⌊y⌋, ⟨y, hy, rfl⟩, fract_nonneg y, fract_lt_one y⟩
  · rintro ⟨m, ⟨y, hys, rfl⟩, h0, h1⟩
    obtain rfl : ⌊y⌋ = m := floor_eq_iff.2 ⟨sub_nonneg.1 h0, sub_lt_iff_lt_add'.1 h1⟩
    exact ⟨y, hys, rfl⟩

中文:
定理 image_fract
  条件: (s : 集合 R)
  结论: fract '' s = ⋃ m : 整数, (fun x : R => x - m) '' s inter 左闭右开区间 0 1
  证明: by
  ext x
  simp only [mem_image, mem_inter_iff, mem_iUnion]; constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⌊y⌋, ⟨y, hy, rfl⟩, fract_nonneg y, fract_lt_one y⟩
  · rintro ⟨m, ⟨y, hys, rfl⟩, h0, h1⟩
    obtain rfl : ⌊y⌋ = m := floor_eq_iff.2 ⟨sub_nonneg.1 h0, sub_lt_iff_lt_add'.1 h1⟩
    exact ⟨y, hys, rfl⟩

Depends on / 依赖: floor_eq_iff, fract_lt_one, fract_nonneg, mem_iUnion, mem_image, mem_inter_iff, sub_lt_iff_lt_add, sub_nonneg
-/
theorem image_fract (s : Set R) : fract '' s = ⋃ m : Int, (fun x : R => x - m) '' s inter Ico 0 1 := by
  ext x
  simp only [mem_image, mem_inter_iff, mem_iUnion]; constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⌊y⌋, ⟨y, hy, rfl⟩, fract_nonneg y, fract_lt_one y⟩
  · rintro ⟨m, ⟨y, hys, rfl⟩, h0, h1⟩
    obtain rfl : ⌊y⌋ = m := floor_eq_iff.2 ⟨sub_nonneg.1 h0, sub_lt_iff_lt_add'.1 h1⟩
    exact ⟨y, hys, rfl⟩

section LinearOrderedField

variable {k : Type*} [Field k] [LinearOrder k] [IsOrderedRing k] [FloorRing k] {b : k}

/--
theorem `fract_div_mul_self_mem_Ico` / 定理 `fract_div_mul_self_mem_Ico`

English:
theorem fract_div_mul_self_mem_Ico
  given: (a b : k) (ha : 0 < a)
  statement: fract (b / a) * a in Ico 0 a
  proof: ⟨(mul_nonneg_iff_of_pos_right ha).2 (fract_nonneg (b / a)),
    (mul_lt_iff_lt_one_left ha).2 (fract_lt_one (b / a))⟩

omit [IsOrderedRing k] in

中文:
定理 fract_div_mul_self_mem_Ico
  条件: (a b : k) (ha : 0 < a)
  结论: fract (b / a) * a in 左闭右开区间 0 a
  证明: ⟨(mul_nonneg_iff_of_pos_right ha).2 (fract_nonneg (b / a)),
    (mul_lt_iff_lt_one_left ha).2 (fract_lt_one (b / a))⟩

omit [IsOrderedRing k] in

Depends on / 依赖: fract_lt_one, fract_nonneg, mul_lt_iff_lt_one_left, mul_nonneg_iff_of_pos_right
-/
theorem fract_div_mul_self_mem_Ico (a b : k) (ha : 0 < a) : fract (b / a) * a in Ico 0 a :=
  ⟨(mul_nonneg_iff_of_pos_right ha).2 (fract_nonneg (b / a)),
    (mul_lt_iff_lt_one_left ha).2 (fract_lt_one (b / a))⟩

omit [IsOrderedRing k] in
/--
theorem `fract_div_mul_self_add_zsmul_eq` / 定理 `fract_div_mul_self_add_zsmul_eq`

English:
theorem fract_div_mul_self_add_zsmul_eq
  given: (a b : k) (ha : a != 0)
  proof: by
  rw [zsmul_eq_mul]; rw [← add_mul]; rw [fract_add_floor]; rw [div_mul_cancel₀ b ha]

中文:
定理 fract_div_mul_self_add_zsmul_eq
  条件: (a b : k) (ha : a != 0)
  证明: by
  rw [zsmul_eq_mul]; rw [← add_mul]; rw [fract_add_floor]; rw [div_mul_cancel₀ b ha]

Depends on / 依赖: add_mul, fract_add_floor, zsmul_eq_mul
-/
theorem fract_div_mul_self_add_zsmul_eq (a b : k) (ha : a != 0) :
    fract (b / a) * a + ⌊b / a⌋ • a = b := by
  rw [zsmul_eq_mul]; rw [← add_mul]; rw [fract_add_floor]; rw [div_mul_cancel₀ b ha]

/--
theorem `sub_floor_div_mul_nonneg` / 定理 `sub_floor_div_mul_nonneg`

English:
theorem sub_floor_div_mul_nonneg
  given: (a : k) (hb : 0 < b)
  statement: 0 <= a - ⌊a / b⌋ * b
  proof: sub_nonneg_of_le (le_div_iff₀ hb).1 floor_le _

中文:
定理 sub_floor_div_mul_nonneg
  条件: (a : k) (hb : 0 < b)
  结论: 0 <= a - ⌊a / b⌋ * b
  证明: sub_nonneg_of_le (le_div_iff₀ hb).1 floor_le _

Depends on / 依赖: floor_le, sub_nonneg_of_le
-/
theorem sub_floor_div_mul_nonneg (a : k) (hb : 0 < b) : 0 <= a - ⌊a / b⌋ * b :=
sub_nonneg_of_le (le_div_iff₀ hb).1 floor_le _

/--
theorem `sub_floor_div_mul_lt` / 定理 `sub_floor_div_mul_lt`

English:
theorem sub_floor_div_mul_lt
  given: (a : k) (hb : 0 < b)
  statement: a - ⌊a / b⌋ * b < b
  proof: sub_lt_iff_lt_add.2 by
    rw [← one_add_mul]; rw [← div_lt_iff₀ hb]; rw [add_comm]
    exact lt_floor_add_one _

中文:
定理 sub_floor_div_mul_lt
  条件: (a : k) (hb : 0 < b)
  结论: a - ⌊a / b⌋ * b < b
  证明: sub_lt_iff_lt_add.2 by
    rw [← one_add_mul]; rw [← div_lt_iff₀ hb]; rw [add_comm]
    exact lt_floor_add_one _

Depends on / 依赖: add_comm, lt_floor_add_one, one_add_mul, sub_lt_iff_lt_add
-/
theorem sub_floor_div_mul_lt (a : k) (hb : 0 < b) : a - ⌊a / b⌋ * b < b :=
sub_lt_iff_lt_add.2 by
    rw [← one_add_mul]; rw [← div_lt_iff₀ hb]; rw [add_comm]
    exact lt_floor_add_one _

/--
theorem `fract_div_natCast_eq_div_natCast_mod` / 定理 `fract_div_natCast_eq_div_natCast_mod`

English:
theorem fract_div_natCast_eq_div_natCast_mod
  given: {m n : Nat}
  statement: fract ((m : k) / n) = ↑(m % n) / n
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  have hn' : 0 < (n : k) := by
    norm_cast
  refine fract_eq_iff.mpr ⟨?_, ?_, m / n, ?_⟩
  · positivity
  · simpa only [div_lt_one hn', Nat.cast_lt] using m.mod_lt hn
  · rw [sub_eq_iff_eq_add', ← mul_right_inj' hn'.ne', mul_div_cancel₀ _ hn'.ne', mul_add,
      mul_div_cancel₀ _ hn'.ne']
    norm_cast
    rw [← Nat.cast_add]; rw [Nat.mod_add_div m n]

中文:
定理 fract_div_natCast_eq_div_natCast_mod
  条件: {m n : 自然数}
  结论: fract ((m : k) / n) = ↑(m % n) / n
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  have hn' : 0 < (n : k) := by
    norm_cast
  refine fract_eq_iff.mpr ⟨?_, ?_, m / n, ?_⟩
  · positivity
  · simpa only [div_lt_one hn', Nat.cast_lt] using m.mod_lt hn
  · rw [sub_eq_iff_eq_add', ← mul_right_inj' hn'.ne', mul_div_cancel₀ _ hn'.ne', mul_add,
      mul_div_cancel₀ _ hn'.ne']
    norm_cast
    rw [← Nat.cast_add]; rw [Nat.mod_add_div m n]

Depends on / 依赖: Nat.cast_add, Nat.cast_lt, Nat.mod_add_div, cast_add, cast_lt, div_lt_one, eq_zero_or_pos, fract_eq_iff, fract_eq_iff.mpr, m.mod_lt, mod_add_div, mod_lt, mul_add, mul_right_inj, n.eq_zero_or_pos, sub_eq_iff_eq_add
-/
theorem fract_div_natCast_eq_div_natCast_mod {m n : Nat} : fract ((m : k) / n) = ↑(m % n) / n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  have hn' : 0 < (n : k) := by
    norm_cast
  refine fract_eq_iff.mpr ⟨?_, ?_, m / n, ?_⟩
  · positivity
  · simpa only [div_lt_one hn', Nat.cast_lt] using m.mod_lt hn
  · rw [sub_eq_iff_eq_add', ← mul_right_inj' hn'.ne', mul_div_cancel₀ _ hn'.ne', mul_add,
      mul_div_cancel₀ _ hn'.ne']
    norm_cast
    rw [← Nat.cast_add]; rw [Nat.mod_add_div m n]

/--
theorem `fract_div_intCast_eq_div_intCast_mod` / 定理 `fract_div_intCast_eq_div_intCast_mod`

English:
theorem fract_div_intCast_eq_div_intCast_mod
  given: {m : Int} {n : Nat}
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  replace hn : 0 < (n : k) := by norm_cast
  have : forall {l : Int}, 0 <= l -> fract ((l : k) / n) = ↑(l % n) / n := by
    intro l hl
    obtain ⟨l₀, rfl | rfl⟩ := l.eq_nat_or_neg
    · rw [cast_natCast, ← natCast_mod, cast_natCast, fract_div_natCast_eq_div_natCast_mod]
    · rw [Right.nonneg_neg_iff, natCast_nonpos_iff] at hl
      simp [hl]
  obtain ⟨m₀, rfl | rfl⟩ := m.eq_nat_or_neg
  · exact this (natCast_nonneg m₀)
  let q := ⌈↑m₀ / (n : k)⌉
  let m₁ := q * ↑n - (↑m₀ : Int)
  have hm₁ : 0 <= m₁ := by
    simpa [m₁, ← @cast_le k, ← div_le_iff₀ hn] using FloorRing.gc_ceil_coe.le_u_l _
  calc
    fract ((Int.cast (-(m₀ : Int)) : k) / (n : k))
      = fract (-(m₀ : k) / n) := by simp
    _ = fract ((m₁ : k) / n) := ?_
    _ = Int.cast (m₁ % (n : Int)) / Nat.cast n := this hm₁
    _ = Int.cast (-(↑m₀ : Int) % ↑n) / Nat.cast n := ?_
  · rw [← fract_intCast_add q, ← mul_div_cancel_right₀ (q : k) hn.ne', ← add_div, ← sub_eq_add_neg]
    simp [m₁]
  · congr 2
    simp only [m₁]
    rw [sub_eq_add_neg]; rw [add_comm (q * ↑n)]; rw [add_mul_emod_self_right]

中文:
定理 fract_div_intCast_eq_div_intCast_mod
  条件: {m : 整数} {n : 自然数}
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  replace hn : 0 < (n : k) := by norm_cast
  have : forall {l : Int}, 0 <= l -> fract ((l : k) / n) = ↑(l % n) / n := by
    intro l hl
    obtain ⟨l₀, rfl | rfl⟩ := l.eq_nat_or_neg
    · rw [cast_natCast, ← natCast_mod, cast_natCast, fract_div_natCast_eq_div_natCast_mod]
    · rw [Right.nonneg_neg_iff, natCast_nonpos_iff] at hl
      simp [hl]
  obtain ⟨m₀, rfl | rfl⟩ := m.eq_nat_or_neg
  · exact this (natCast_nonneg m₀)
  let q := ⌈↑m₀ / (n : k)⌉
  let m₁ := q * ↑n - (↑m₀ : Int)
  have hm₁ : 0 <= m₁ := by
    simpa [m₁, ← @cast_le k, ← div_le_iff₀ hn] using FloorRing.gc_ceil_coe.le_u_l _
  calc
    fract ((Int.cast (-(m₀ : Int)) : k) / (n : k))
      = fract (-(m₀ : k) / n) := by simp
    _ = fract ((m₁ : k) / n) := ?_
    _ = Int.cast (m₁ % (n : Int)) / Nat.cast n := this hm₁
    _ = Int.cast (-(↑m₀ : Int) % ↑n) / Nat.cast n := ?_
  · rw [← fract_intCast_add q, ← mul_div_cancel_right₀ (q : k) hn.ne', ← add_div, ← sub_eq_add_neg]
    simp [m₁]
  · congr 2
    simp only [m₁]
    rw [sub_eq_add_neg]; rw [add_comm (q * ↑n)]; rw [add_mul_emod_self_right]

Depends on / 依赖: Right.nonneg_neg_iff, cast_natCast, eq_nat_or_neg, eq_zero_or_pos, fract_div_natCast_eq_div_natCast_mod, l.eq_nat_or_neg, m.eq_nat_or_neg, n.eq_zero_or_pos, natCast_mod, natCast_nonneg, natCast_nonpos_iff, nonneg_neg_iff, replace
-/
theorem fract_div_intCast_eq_div_intCast_mod {m : Int} {n : Nat} :
    fract ((m : k) / n) = ↑(m % n) / n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  replace hn : 0 < (n : k) := by norm_cast
  have : forall {l : Int}, 0 <= l -> fract ((l : k) / n) = ↑(l % n) / n := by
    intro l hl
    obtain ⟨l₀, rfl | rfl⟩ := l.eq_nat_or_neg
    · rw [cast_natCast, ← natCast_mod, cast_natCast, fract_div_natCast_eq_div_natCast_mod]
    · rw [Right.nonneg_neg_iff, natCast_nonpos_iff] at hl
      simp [hl]
  obtain ⟨m₀, rfl | rfl⟩ := m.eq_nat_or_neg
  · exact this (natCast_nonneg m₀)
  let q := ⌈↑m₀ / (n : k)⌉
  let m₁ := q * ↑n - (↑m₀ : Int)
  have hm₁ : 0 <= m₁ := by
    simpa [m₁, ← @cast_le k, ← div_le_iff₀ hn] using FloorRing.gc_ceil_coe.le_u_l _
  calc
    fract ((Int.cast (-(m₀ : Int)) : k) / (n : k))
      = fract (-(m₀ : k) / n) := by simp
    _ = fract ((m₁ : k) / n) := ?_
    _ = Int.cast (m₁ % (n : Int)) / Nat.cast n := this hm₁
    _ = Int.cast (-(↑m₀ : Int) % ↑n) / Nat.cast n := ?_
  · rw [← fract_intCast_add q, ← mul_div_cancel_right₀ (q : k) hn.ne', ← add_div, ← sub_eq_add_neg]
    simp [m₁]
  · congr 2
    simp only [m₁]
    rw [sub_eq_add_neg]; rw [add_comm (q * ↑n)]; rw [add_mul_emod_self_right]

end LinearOrderedField

end fract

/-! #### Ceil -/

section ceil

@[simp]
/--
theorem `one_le_ceil_iff` / 定理 `one_le_ceil_iff`

English:
theorem one_le_ceil_iff
  statement: 1 <= ⌈a⌉ ↔ 0 < a
  proof: by
  simpa using le_ceil_iff (z := 1)

@[bound]

中文:
定理 one_le_ceil_iff
  结论: 1 <= ⌈a⌉ ↔ 0 < a
  证明: by
  simpa using le_ceil_iff (z := 1)

@[bound]

Depends on / 依赖: le_ceil_iff
-/
theorem one_le_ceil_iff : 1 <= ⌈a⌉ ↔ 0 < a := by
  simpa using le_ceil_iff (z := 1)

@[bound]
/--
theorem `ceil_le_floor_add_one` / 定理 `ceil_le_floor_add_one`

English:
theorem ceil_le_floor_add_one
  given: (a : R)
  statement: ⌈a⌉ <= ⌊a⌋ + 1
  proof: by
  rw [ceil_le]; rw [Int.cast_add]; rw [Int.cast_one]
  exact (lt_floor_add_one a).le

中文:
定理 ceil_le_floor_add_one
  条件: (a : R)
  结论: ⌈a⌉ <= ⌊a⌋ + 1
  证明: by
  rw [ceil_le]; rw [Int.cast_add]; rw [Int.cast_one]
  exact (lt_floor_add_one a).le

Depends on / 依赖: Int.cast_add, Int.cast_one, cast_add, cast_one, ceil_le, lt_floor_add_one
-/
theorem ceil_le_floor_add_one (a : R) : ⌈a⌉ <= ⌊a⌋ + 1 := by
  rw [ceil_le]; rw [Int.cast_add]; rw [Int.cast_one]
  exact (lt_floor_add_one a).le

/--
theorem `ceil_mono` / 定理 `ceil_mono`

English:
theorem ceil_mono
  statement: Monotone (ceil : R -> Int)
  proof: gc_ceil_coe.monotone_l

中文:
定理 ceil_mono
  结论: 递增 (ceil : R -> 整数)
  证明: gc_ceil_coe.monotone_l

Depends on / 依赖: gc_ceil_coe, gc_ceil_coe.monotone_l, monotone_l
-/
theorem ceil_mono : Monotone (ceil : R -> Int) :=
  gc_ceil_coe.monotone_l

/--
lemma `ceil_le_ceil` / 引理 `ceil_le_ceil`

English:
lemma ceil_le_ceil
  given: (hab : a <= b)
  statement: ⌈a⌉ <= ⌈b⌉
  proof: ceil_mono hab

中文:
引理 ceil_le_ceil
  条件: (hab : a <= b)
  结论: ⌈a⌉ <= ⌈b⌉
  证明: ceil_mono hab
-/
@[gcongr, bound] lemma ceil_le_ceil (hab : a <= b) : ⌈a⌉ <= ⌈b⌉ := ceil_mono hab

/--
theorem `ceil_nonneg_of_neg_one_lt` / 定理 `ceil_nonneg_of_neg_one_lt`

English:
theorem ceil_nonneg_of_neg_one_lt
  given: (ha : -1 < a)
  statement: 0 <= ⌈a⌉
  proof: by
  rwa [Int.le_ceil_iff, Int.cast_zero, zero_sub]

中文:
定理 ceil_nonneg_of_neg_one_lt
  条件: (ha : -1 < a)
  结论: 0 <= ⌈a⌉
  证明: by
  rwa [Int.le_ceil_iff, Int.cast_zero, zero_sub]

Depends on / 依赖: Int.cast_zero, Int.le_ceil_iff, cast_zero, le_ceil_iff, zero_sub
-/
theorem ceil_nonneg_of_neg_one_lt (ha : -1 < a) : 0 <= ⌈a⌉ := by
  rwa [Int.le_ceil_iff, Int.cast_zero, zero_sub]

/--
theorem `ceil_eq_iff` / 定理 `ceil_eq_iff`

English:
theorem ceil_eq_iff
  statement: ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a <= z
  proof: by
  rw [← ceil_le]; rw [← Int.cast_one]; rw [← Int.cast_sub]; rw [← lt_ceil]; rw [Int.sub_one_lt_iff]; rw [le_antisymm_iff]; rw [and_comm]

@[simp]

中文:
定理 ceil_eq_iff
  结论: ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a <= z
  证明: by
  rw [← ceil_le]; rw [← Int.cast_one]; rw [← Int.cast_sub]; rw [← lt_ceil]; rw [Int.sub_one_lt_iff]; rw [le_antisymm_iff]; rw [and_comm]

@[simp]

Depends on / 依赖: Int.cast_one, Int.cast_sub, Int.sub_one_lt_iff, and_comm, cast_one, cast_sub, ceil_le, le_antisymm_iff, lt_ceil, sub_one_lt_iff
-/
theorem ceil_eq_iff : ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a <= z := by
  rw [← ceil_le]; rw [← Int.cast_one]; rw [← Int.cast_sub]; rw [← lt_ceil]; rw [Int.sub_one_lt_iff]; rw [le_antisymm_iff]; rw [and_comm]

@[simp]
/--
theorem `ceil_eq_zero_iff` / 定理 `ceil_eq_zero_iff`

English:
theorem ceil_eq_zero_iff
  statement: ⌈a⌉ = 0 ↔ a in Ioc (-1 : R) 0
  proof: by simp [ceil_eq_iff]

中文:
定理 ceil_eq_zero_iff
  结论: ⌈a⌉ = 0 ↔ a in 左开右闭区间 (-1 : R) 0
  证明: by simp [ceil_eq_iff]

Depends on / 依赖: ceil_eq_iff
-/
theorem ceil_eq_zero_iff : ⌈a⌉ = 0 ↔ a in Ioc (-1 : R) 0 := by simp [ceil_eq_iff]

/--
theorem `ceil_eq_on_Ioc` / 定理 `ceil_eq_on_Ioc`

English:
theorem ceil_eq_on_Ioc
  given: (z : Int)
  statement: forall a in Set.Ioc (z - 1 : R) z, ⌈a⌉ = z
  proof: fun _ ⟨h₀, h₁⟩ =>
  ceil_eq_iff.mpr ⟨h₀, h₁⟩

@[simp]

中文:
定理 ceil_eq_on_Ioc
  条件: (z : 整数)
  结论: 对任意 a in 集合.左开右闭区间 (z - 1 : R) z, ⌈a⌉ = z
  证明: fun _ ⟨h₀, h₁⟩ =>
  ceil_eq_iff.mpr ⟨h₀, h₁⟩

@[simp]
-/
theorem ceil_eq_on_Ioc (z : Int) : forall a in Set.Ioc (z - 1 : R) z, ⌈a⌉ = z := fun _ ⟨h₀, h₁⟩ =>
  ceil_eq_iff.mpr ⟨h₀, h₁⟩

@[simp]
/--
theorem `preimage_ceil_singleton` / 定理 `preimage_ceil_singleton`

English:
theorem preimage_ceil_singleton
  given: (m : Int)
  statement: (ceil : R -> Int) ⁻¹' {m} = Ioc ((m : R) - 1) m
  proof: ext fun _ => ceil_eq_iff

中文:
定理 preimage_ceil_singleton
  条件: (m : 整数)
  结论: (ceil : R -> 整数) ⁻¹' {m} = 左开右闭区间 ((m : R) - 1) m
  证明: ext fun _ => ceil_eq_iff

Depends on / 依赖: ceil_eq_iff
-/
theorem preimage_ceil_singleton (m : Int) : (ceil : R -> Int) ⁻¹' {m} = Ioc ((m : R) - 1) m :=
  ext fun _ => ceil_eq_iff

variable [IsOrderedRing R]

/--
theorem `floor_neg` / 定理 `floor_neg`

English:
theorem floor_neg
  statement: ⌊-a⌋ = -⌈a⌉
  proof: eq_of_forall_le_iff fun z => by rw [le_neg, ceil_le, le_floor, Int.cast_neg, le_neg]

中文:
定理 floor_neg
  结论: ⌊-a⌋ = -⌈a⌉
  证明: eq_of_forall_le_iff fun z => by rw [le_neg, ceil_le, le_floor, Int.cast_neg, le_neg]

Depends on / 依赖: Int.cast_neg, cast_neg, ceil_le, eq_of_forall_le_iff, le_floor, le_neg
-/
theorem floor_neg : ⌊-a⌋ = -⌈a⌉ :=
  eq_of_forall_le_iff fun z => by rw [le_neg, ceil_le, le_floor, Int.cast_neg, le_neg]

/--
theorem `ceil_neg` / 定理 `ceil_neg`

English:
theorem ceil_neg
  statement: ⌈-a⌉ = -⌊a⌋
  proof: eq_of_forall_ge_iff fun z => by rw [neg_le, ceil_le, le_floor, Int.cast_neg, neg_le]

@[simp]

中文:
定理 ceil_neg
  结论: ⌈-a⌉ = -⌊a⌋
  证明: eq_of_forall_ge_iff fun z => by rw [neg_le, ceil_le, le_floor, Int.cast_neg, neg_le]

@[simp]

Depends on / 依赖: Int.cast_neg, cast_neg, ceil_le, eq_of_forall_ge_iff, le_floor, neg_le
-/
theorem ceil_neg : ⌈-a⌉ = -⌊a⌋ :=
  eq_of_forall_ge_iff fun z => by rw [neg_le, ceil_le, le_floor, Int.cast_neg, neg_le]

@[simp]
/--
theorem `ceil_intCast` / 定理 `ceil_intCast`

English:
theorem ceil_intCast
  given: (z : Int)
  statement: ⌈(z : R)⌉ = z
  proof: eq_of_forall_ge_iff fun a => by rw [ceil_le, Int.cast_le]

@[simp]

中文:
定理 ceil_intCast
  条件: (z : 整数)
  结论: ⌈(z : R)⌉ = z
  证明: eq_of_forall_ge_iff fun a => by rw [ceil_le, Int.cast_le]

@[simp]

Depends on / 依赖: Int.cast_le, cast_le, ceil_le, eq_of_forall_ge_iff
-/
theorem ceil_intCast (z : Int) : ⌈(z : R)⌉ = z :=
  eq_of_forall_ge_iff fun a => by rw [ceil_le, Int.cast_le]

@[simp]
/--
theorem `ceil_natCast` / 定理 `ceil_natCast`

English:
theorem ceil_natCast
  given: (n : Nat)
  statement: ⌈(n : R)⌉ = n
  proof: eq_of_forall_ge_iff fun a => by rw [ceil_le, ← cast_natCast, cast_le]

@[simp]

中文:
定理 ceil_natCast
  条件: (n : 自然数)
  结论: ⌈(n : R)⌉ = n
  证明: eq_of_forall_ge_iff fun a => by rw [ceil_le, ← cast_natCast, cast_le]

@[simp]

Depends on / 依赖: cast_le, cast_natCast, ceil_le, eq_of_forall_ge_iff
-/
theorem ceil_natCast (n : Nat) : ⌈(n : R)⌉ = n :=
  eq_of_forall_ge_iff fun a => by rw [ceil_le, ← cast_natCast, cast_le]

@[simp]
/--
theorem `ceil_ofNat` / 定理 `ceil_ofNat`

English:
theorem ceil_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ⌈(ofNat(n) : R)⌉ = ofNat(n)
  proof: ceil_natCast n

@[simp]

中文:
定理 ceil_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: ⌈(of自然数(n) : R)⌉ = of自然数(n)
  证明: ceil_natCast n

@[simp]

Depends on / 依赖: ceil_natCast
-/
theorem ceil_ofNat (n : Nat) [n.AtLeastTwo] : ⌈(ofNat(n) : R)⌉ = ofNat(n) := ceil_natCast n

@[simp]
/--
theorem `ceil_add_intCast` / 定理 `ceil_add_intCast`

English:
theorem ceil_add_intCast
  given: (a : R) (z : Int)
  statement: ⌈a + z⌉ = ⌈a⌉ + z
  proof: by
  rw [← neg_inj]; rw [neg_add']; rw [← floor_neg]; rw [← floor_neg]; rw [neg_add']; rw [floor_sub_intCast]

@[simp]

中文:
定理 ceil_add_intCast
  条件: (a : R) (z : 整数)
  结论: ⌈a + z⌉ = ⌈a⌉ + z
  证明: by
  rw [← neg_inj]; rw [neg_add']; rw [← floor_neg]; rw [← floor_neg]; rw [neg_add']; rw [floor_sub_intCast]

@[simp]

Depends on / 依赖: floor_neg, floor_sub_intCast, neg_add, neg_inj
-/
theorem ceil_add_intCast (a : R) (z : Int) : ⌈a + z⌉ = ⌈a⌉ + z := by
  rw [← neg_inj]; rw [neg_add']; rw [← floor_neg]; rw [← floor_neg]; rw [neg_add']; rw [floor_sub_intCast]

@[simp]
/--
theorem `ceil_intCast_add` / 定理 `ceil_intCast_add`

English:
theorem ceil_intCast_add
  given: (z : Int) (a : R)
  statement: ⌈z + a⌉ = z + ⌈a⌉
  proof: by
  rw [add_comm]; rw [ceil_add_intCast]; rw [add_comm]

@[simp]

中文:
定理 ceil_intCast_add
  条件: (z : 整数) (a : R)
  结论: ⌈z + a⌉ = z + ⌈a⌉
  证明: by
  rw [add_comm]; rw [ceil_add_intCast]; rw [add_comm]

@[simp]

Depends on / 依赖: add_comm, ceil_add_intCast
-/
theorem ceil_intCast_add (z : Int) (a : R) : ⌈z + a⌉ = z + ⌈a⌉ := by
  rw [add_comm]; rw [ceil_add_intCast]; rw [add_comm]

@[simp]
/--
theorem `ceil_add_natCast` / 定理 `ceil_add_natCast`

English:
theorem ceil_add_natCast
  given: (a : R) (n : Nat)
  statement: ⌈a + n⌉ = ⌈a⌉ + n
  proof: by
  rw [← Int.cast_natCast]; rw [ceil_add_intCast]

@[simp]

中文:
定理 ceil_add_natCast
  条件: (a : R) (n : 自然数)
  结论: ⌈a + n⌉ = ⌈a⌉ + n
  证明: by
  rw [← Int.cast_natCast]; rw [ceil_add_intCast]

@[simp]

Depends on / 依赖: Int.cast_natCast, cast_natCast, ceil_add_intCast
-/
theorem ceil_add_natCast (a : R) (n : Nat) : ⌈a + n⌉ = ⌈a⌉ + n := by
  rw [← Int.cast_natCast]; rw [ceil_add_intCast]

@[simp]
/--
theorem `ceil_natCast_add` / 定理 `ceil_natCast_add`

English:
theorem ceil_natCast_add
  given: (n : Nat) (a : R)
  statement: ⌈n + a⌉ = n + ⌈a⌉
  proof: mod_cast ceil_intCast_add n a

@[simp]

中文:
定理 ceil_natCast_add
  条件: (n : 自然数) (a : R)
  结论: ⌈n + a⌉ = n + ⌈a⌉
  证明: mod_cast ceil_intCast_add n a

@[simp]

Depends on / 依赖: ceil_intCast_add, mod_cast
-/
theorem ceil_natCast_add (n : Nat) (a : R) : ⌈n + a⌉ = n + ⌈a⌉ :=
  mod_cast ceil_intCast_add n a

@[simp]
/--
theorem `ceil_add_one` / 定理 `ceil_add_one`

English:
theorem ceil_add_one
  given: (a : R)
  statement: ⌈a + 1⌉ = ⌈a⌉ + 1
  proof: by
  rw [← ceil_add_intCast a (1 : Int)]; rw [cast_one]

@[simp]

中文:
定理 ceil_add_one
  条件: (a : R)
  结论: ⌈a + 1⌉ = ⌈a⌉ + 1
  证明: by
  rw [← ceil_add_intCast a (1 : Int)]; rw [cast_one]

@[simp]

Depends on / 依赖: cast_one, ceil_add_intCast
-/
theorem ceil_add_one (a : R) : ⌈a + 1⌉ = ⌈a⌉ + 1 := by
  rw [← ceil_add_intCast a (1 : Int)]; rw [cast_one]

@[simp]
/--
theorem `ceil_one_add` / 定理 `ceil_one_add`

English:
theorem ceil_one_add
  given: (a : R)
  statement: ⌈1 + a⌉ = 1 + ⌈a⌉
  proof: mod_cast ceil_natCast_add 1 a

@[simp]

中文:
定理 ceil_one_add
  条件: (a : R)
  结论: ⌈1 + a⌉ = 1 + ⌈a⌉
  证明: mod_cast ceil_natCast_add 1 a

@[simp]

Depends on / 依赖: ceil_natCast_add, mod_cast
-/
theorem ceil_one_add (a : R) : ⌈1 + a⌉ = 1 + ⌈a⌉ :=
  mod_cast ceil_natCast_add 1 a

@[simp]
/--
theorem `ceil_add_ofNat` / 定理 `ceil_add_ofNat`

English:
theorem ceil_add_ofNat
  given: (a : R) (n : Nat) [n.AtLeastTwo]
  proof: ceil_add_natCast a n

@[simp]

中文:
定理 ceil_add_of自然数
  条件: (a : R) (n : 自然数) [n.AtLeastTwo]
  证明: ceil_add_natCast a n

@[simp]

Depends on / 依赖: ceil_add_natCast
-/
theorem ceil_add_ofNat (a : R) (n : Nat) [n.AtLeastTwo] :
    ⌈a + ofNat(n)⌉ = ⌈a⌉ + ofNat(n) :=
  ceil_add_natCast a n

@[simp]
/--
theorem `ceil_ofNat_add` / 定理 `ceil_ofNat_add`

English:
theorem ceil_ofNat_add
  given: (n : Nat) [n.AtLeastTwo] (a : R)
  proof: ceil_natCast_add n a

@[simp]

中文:
定理 ceil_of自然数_add
  条件: (n : 自然数) [n.AtLeastTwo] (a : R)
  证明: ceil_natCast_add n a

@[simp]

Depends on / 依赖: ceil_natCast_add
-/
theorem ceil_ofNat_add (n : Nat) [n.AtLeastTwo] (a : R) :
    ⌈ofNat(n) + a⌉ = ofNat(n) + ⌈a⌉ :=
  ceil_natCast_add n a

@[simp]
/--
theorem `ceil_sub_intCast` / 定理 `ceil_sub_intCast`

English:
theorem ceil_sub_intCast
  given: (a : R) (z : Int)
  statement: ⌈a - z⌉ = ⌈a⌉ - z
  proof: Eq.trans (by rw [Int.cast_neg, sub_eq_add_neg]) (ceil_add_intCast _ _)

@[simp]

中文:
定理 ceil_sub_intCast
  条件: (a : R) (z : 整数)
  结论: ⌈a - z⌉ = ⌈a⌉ - z
  证明: Eq.trans (by rw [Int.cast_neg, sub_eq_add_neg]) (ceil_add_intCast _ _)

@[simp]

Depends on / 依赖: Eq.trans, Int.cast_neg, cast_neg, ceil_add_intCast, sub_eq_add_neg
-/
theorem ceil_sub_intCast (a : R) (z : Int) : ⌈a - z⌉ = ⌈a⌉ - z :=
  Eq.trans (by rw [Int.cast_neg, sub_eq_add_neg]) (ceil_add_intCast _ _)

@[simp]
/--
theorem `ceil_sub_natCast` / 定理 `ceil_sub_natCast`

English:
theorem ceil_sub_natCast
  given: (a : R) (n : Nat)
  statement: ⌈a - n⌉ = ⌈a⌉ - n
  proof: by
  convert ceil_sub_intCast a n
  simp

@[simp]

中文:
定理 ceil_sub_natCast
  条件: (a : R) (n : 自然数)
  结论: ⌈a - n⌉ = ⌈a⌉ - n
  证明: by
  convert ceil_sub_intCast a n
  simp

@[simp]

Depends on / 依赖: ceil_sub_intCast, convert
-/
theorem ceil_sub_natCast (a : R) (n : Nat) : ⌈a - n⌉ = ⌈a⌉ - n := by
  convert ceil_sub_intCast a n
  simp

@[simp]
/--
theorem `ceil_sub_one` / 定理 `ceil_sub_one`

English:
theorem ceil_sub_one
  given: (a : R)
  statement: ⌈a - 1⌉ = ⌈a⌉ - 1
  proof: by
  rw [eq_sub_iff_add_eq]; rw [← ceil_add_one]; rw [sub_add_cancel]

@[simp]

中文:
定理 ceil_sub_one
  条件: (a : R)
  结论: ⌈a - 1⌉ = ⌈a⌉ - 1
  证明: by
  rw [eq_sub_iff_add_eq]; rw [← ceil_add_one]; rw [sub_add_cancel]

@[simp]

Depends on / 依赖: ceil_add_one, eq_sub_iff_add_eq, sub_add_cancel
-/
theorem ceil_sub_one (a : R) : ⌈a - 1⌉ = ⌈a⌉ - 1 := by
  rw [eq_sub_iff_add_eq]; rw [← ceil_add_one]; rw [sub_add_cancel]

@[simp]
/--
theorem `ceil_sub_ofNat` / 定理 `ceil_sub_ofNat`

English:
theorem ceil_sub_ofNat
  given: (a : R) (n : Nat) [n.AtLeastTwo]
  proof: ceil_sub_natCast a n

@[bound]

中文:
定理 ceil_sub_of自然数
  条件: (a : R) (n : 自然数) [n.AtLeastTwo]
  证明: ceil_sub_natCast a n

@[bound]

Depends on / 依赖: ceil_sub_natCast
-/
theorem ceil_sub_ofNat (a : R) (n : Nat) [n.AtLeastTwo] :
    ⌈a - ofNat(n)⌉ = ⌈a⌉ - ofNat(n) :=
  ceil_sub_natCast a n

@[bound]
/--
theorem `ceil_lt_add_one` / 定理 `ceil_lt_add_one`

English:
theorem ceil_lt_add_one
  given: (a : R)
  statement: (⌈a⌉ : R) < a + 1
  proof: by
  rw [← lt_ceil]; rw [← Int.cast_one]; rw [ceil_add_intCast]
  apply lt_add_one

@[bound]

中文:
定理 ceil_lt_add_one
  条件: (a : R)
  结论: (⌈a⌉ : R) < a + 1
  证明: by
  rw [← lt_ceil]; rw [← Int.cast_one]; rw [ceil_add_intCast]
  apply lt_add_one

@[bound]

Depends on / 依赖: Int.cast_one, cast_one, ceil_add_intCast, lt_add_one, lt_ceil
-/
theorem ceil_lt_add_one (a : R) : (⌈a⌉ : R) < a + 1 := by
  rw [← lt_ceil]; rw [← Int.cast_one]; rw [ceil_add_intCast]
  apply lt_add_one

@[bound]
/--
theorem `ceil_add_le` / 定理 `ceil_add_le`

English:
theorem ceil_add_le
  given: (a b : R)
  statement: ⌈a + b⌉ <= ⌈a⌉ + ⌈b⌉
  proof: by
  rw [ceil_le]; rw [Int.cast_add]
  gcongr <;> apply le_ceil

@[bound]

中文:
定理 ceil_add_le
  条件: (a b : R)
  结论: ⌈a + b⌉ <= ⌈a⌉ + ⌈b⌉
  证明: by
  rw [ceil_le]; rw [Int.cast_add]
  gcongr <;> apply le_ceil

@[bound]

Depends on / 依赖: Int.cast_add, cast_add, ceil_le, le_ceil
-/
theorem ceil_add_le (a b : R) : ⌈a + b⌉ <= ⌈a⌉ + ⌈b⌉ := by
  rw [ceil_le]; rw [Int.cast_add]
  gcongr <;> apply le_ceil

@[bound]
/--
theorem `ceil_add_ceil_le` / 定理 `ceil_add_ceil_le`

English:
theorem ceil_add_ceil_le
  given: (a b : R)
  statement: ⌈a⌉ + ⌈b⌉ <= ⌈a + b⌉ + 1
  proof: by
  rw [← le_sub_iff_add_le]; rw [ceil_le]; rw [Int.cast_sub]; rw [Int.cast_add]; rw [Int.cast_one]; rw [le_sub_comm]
  refine (ceil_lt_add_one _).le.trans ?_
  rw [le_sub_iff_add_le']; rw [← add_assoc]; rw [add_le_add_iff_right]
  exact le_ceil _

@[simp]

中文:
定理 ceil_add_ceil_le
  条件: (a b : R)
  结论: ⌈a⌉ + ⌈b⌉ <= ⌈a + b⌉ + 1
  证明: by
  rw [← le_sub_iff_add_le]; rw [ceil_le]; rw [Int.cast_sub]; rw [Int.cast_add]; rw [Int.cast_one]; rw [le_sub_comm]
  refine (ceil_lt_add_one _).le.trans ?_
  rw [le_sub_iff_add_le']; rw [← add_assoc]; rw [add_le_add_iff_right]
  exact le_ceil _

@[simp]

Depends on / 依赖: Int.cast_add, Int.cast_one, Int.cast_sub, add_assoc, add_le_add_iff_right, cast_add, cast_one, cast_sub, ceil_le, ceil_lt_add_one, le.trans, le_ceil, le_sub_comm, le_sub_iff_add_le
-/
theorem ceil_add_ceil_le (a b : R) : ⌈a⌉ + ⌈b⌉ <= ⌈a + b⌉ + 1 := by
  rw [← le_sub_iff_add_le]; rw [ceil_le]; rw [Int.cast_sub]; rw [Int.cast_add]; rw [Int.cast_one]; rw [le_sub_comm]
  refine (ceil_lt_add_one _).le.trans ?_
  rw [le_sub_iff_add_le']; rw [← add_assoc]; rw [add_le_add_iff_right]
  exact le_ceil _

@[simp]
/--
theorem `ceil_zero` / 定理 `ceil_zero`

English:
theorem ceil_zero
  statement: ⌈(0 : R)⌉ = 0
  proof: by rw [← cast_zero, ceil_intCast]

@[simp]

中文:
定理 ceil_zero
  结论: ⌈(0 : R)⌉ = 0
  证明: by rw [← cast_zero, ceil_intCast]

@[simp]

Depends on / 依赖: cast_zero, ceil_intCast
-/
theorem ceil_zero : ⌈(0 : R)⌉ = 0 := by rw [← cast_zero, ceil_intCast]

@[simp]
/--
theorem `ceil_one` / 定理 `ceil_one`

English:
theorem ceil_one
  statement: ⌈(1 : R)⌉ = 1
  proof: by rw [← cast_one, ceil_intCast]

omit [IsOrderedRing R] in

中文:
定理 ceil_one
  结论: ⌈(1 : R)⌉ = 1
  证明: by rw [← cast_one, ceil_intCast]

omit [IsOrderedRing R] in

Depends on / 依赖: cast_one, ceil_intCast
-/
theorem ceil_one : ⌈(1 : R)⌉ = 1 := by rw [← cast_one, ceil_intCast]

omit [IsOrderedRing R] in
/--
theorem `ceil_eq_on_Ioc'` / 定理 `ceil_eq_on_Ioc'`

English:
theorem ceil_eq_on_Ioc'
  given: (z : Int)
  statement: forall a in Set.Ioc (z - 1 : R) z, (⌈a⌉ : R) = z
  proof: fun a ha => congrArg Int.cast (ceil_eq_on_Ioc z a ha)

中文:
定理 ceil_eq_on_Ioc'
  条件: (z : 整数)
  结论: 对任意 a in 集合.左开右闭区间 (z - 1 : R) z, (⌈a⌉ : R) = z
  证明: fun a ha => congrArg Int.cast (ceil_eq_on_Ioc z a ha)

Depends on / 依赖: Int.cast, ceil_eq_on_Ioc
-/
theorem ceil_eq_on_Ioc' (z : Int) : forall a in Set.Ioc (z - 1 : R) z, (⌈a⌉ : R) = z :=
  fun a ha => congrArg Int.cast (ceil_eq_on_Ioc z a ha)

/--
lemma `ceil_eq_self_iff_mem` / 引理 `ceil_eq_self_iff_mem`

English:
lemma ceil_eq_self_iff_mem
  given: (a : R)
  statement: ⌈a⌉ = a ↔ a in Set.range Int.cast
  proof: by
  aesop

@[bound]

中文:
引理 ceil_eq_self_iff_mem
  条件: (a : R)
  结论: ⌈a⌉ = a ↔ a in 集合.range 整数.cast
  证明: by
  aesop

@[bound]
-/
lemma ceil_eq_self_iff_mem (a : R) : ⌈a⌉ = a ↔ a in Set.range Int.cast := by
  aesop

@[bound]
/--
theorem `floor_le_ceil` / 定理 `floor_le_ceil`

English:
theorem floor_le_ceil
  given: (a : R)
  statement: ⌊a⌋ <= ⌈a⌉
  proof: cast_le.1 (floor_le _).trans le_ceil _

@[bound]

中文:
定理 floor_le_ceil
  条件: (a : R)
  结论: ⌊a⌋ <= ⌈a⌉
  证明: cast_le.1 (floor_le _).trans le_ceil _

@[bound]

Depends on / 依赖: cast_le, floor_le, le_ceil
-/
theorem floor_le_ceil (a : R) : ⌊a⌋ <= ⌈a⌉ :=
cast_le.1 (floor_le _).trans le_ceil _

@[bound]
/--
theorem `floor_lt_ceil_of_lt` / 定理 `floor_lt_ceil_of_lt`

English:
theorem floor_lt_ceil_of_lt
  given: {a b : R} (h : a < b)
  statement: ⌊a⌋ < ⌈b⌉
  proof: cast_lt.1 (floor_le a).trans_lt h.trans_le le_ceil b

中文:
定理 floor_lt_ceil_of_lt
  条件: {a b : R} (h : a < b)
  结论: ⌊a⌋ < ⌈b⌉
  证明: cast_lt.1 (floor_le a).trans_lt h.trans_le le_ceil b

Depends on / 依赖: cast_lt, floor_le, h.trans_le, le_ceil, trans_le, trans_lt
-/
theorem floor_lt_ceil_of_lt {a b : R} (h : a < b) : ⌊a⌋ < ⌈b⌉ :=
cast_lt.1 (floor_le a).trans_lt h.trans_le le_ceil b

/--
lemma `ceil_eq_floor_add_one_iff_notMem` / 引理 `ceil_eq_floor_add_one_iff_notMem`

English:
lemma ceil_eq_floor_add_one_iff_notMem
  given: (a : R)
  statement: ⌈a⌉ = ⌊a⌋ + 1 ↔ a ∉ Set.range Int.cast
  proof: by
  refine ⟨fun h ht => ?_, fun h => ?_⟩
  · have h0 := ((floor_eq_self_iff_mem _).mpr ht).trans ((ceil_eq_self_iff_mem _).mpr ht).symm
    rw [h]; rw [cast_add]; rw [cast_one]; rw [left_eq_add] at h0
    exact one_ne_zero h0
  · apply le_antisymm (Int.ceil_le_floor_add_one _)
    rw [add_one_le_iff]; rw [lt_ceil]
    exact lt_of_le_of_ne (Int.floor_le a) ((iff_false_right h).mp (floor_eq_self_iff_mem a))

中文:
引理 ceil_eq_floor_add_one_iff_notMem
  条件: (a : R)
  结论: ⌈a⌉ = ⌊a⌋ + 1 ↔ a ∉ 集合.range 整数.cast
  证明: by
  refine ⟨fun h ht => ?_, fun h => ?_⟩
  · have h0 := ((floor_eq_self_iff_mem _).mpr ht).trans ((ceil_eq_self_iff_mem _).mpr ht).symm
    rw [h]; rw [cast_add]; rw [cast_one]; rw [left_eq_add] at h0
    exact one_ne_zero h0
  · apply le_antisymm (Int.ceil_le_floor_add_one _)
    rw [add_one_le_iff]; rw [lt_ceil]
    exact lt_of_le_of_ne (Int.floor_le a) ((iff_false_right h).mp (floor_eq_self_iff_mem a))

Depends on / 依赖: Int.ceil_le_floor_add_one, Int.floor_le, add_one_le_iff, cast_add, cast_one, ceil_eq_self_iff_mem, ceil_le_floor_add_one, floor_eq_self_iff_mem, floor_le, iff_false_right, le_antisymm, left_eq_add, lt_ceil, lt_of_le_of_ne, one_ne_zero
-/
lemma ceil_eq_floor_add_one_iff_notMem (a : R) : ⌈a⌉ = ⌊a⌋ + 1 ↔ a ∉ Set.range Int.cast := by
  refine ⟨fun h ht => ?_, fun h => ?_⟩
  · have h0 := ((floor_eq_self_iff_mem _).mpr ht).trans ((ceil_eq_self_iff_mem _).mpr ht).symm
    rw [h]; rw [cast_add]; rw [cast_one]; rw [left_eq_add] at h0
    exact one_ne_zero h0
  · apply le_antisymm (Int.ceil_le_floor_add_one _)
    rw [add_one_le_iff]; rw [lt_ceil]
    exact lt_of_le_of_ne (Int.floor_le a) ((iff_false_right h).mp (floor_eq_self_iff_mem a))

/--
theorem `fract_eq_zero_or_add_one_sub_ceil` / 定理 `fract_eq_zero_or_add_one_sub_ceil`

English:
theorem fract_eq_zero_or_add_one_sub_ceil
  given: (a : R)
  statement: fract a = 0 ∨ fract a = a + 1 - (⌈a⌉ : R)
  proof: by
  rcases eq_or_ne (fract a) 0 with ha | ha
  · exact Or.inl ha
  right
  suffices (⌈a⌉ : R) = ⌊a⌋ + 1 by
    rw [this]; rw [← self_sub_fract]
    abel
  rw [← Int.cast_one]; rw [← Int.cast_add]
  refine congrArg Int.cast (ceil_eq_iff.mpr ⟨?_, _root_.le_of_lt <| by simp⟩)
  rw [cast_add]; rw [cast_one]; rw [add_tsub_cancel_right]; rw [← self_sub_fract a]; rw [sub_lt_self_iff]
  exact ha.symm.lt_of_le (fract_nonneg a)

中文:
定理 fract_eq_zero_or_add_one_sub_ceil
  条件: (a : R)
  结论: fract a = 0 ∨ fract a = a + 1 - (⌈a⌉ : R)
  证明: by
  rcases eq_or_ne (fract a) 0 with ha | ha
  · exact Or.inl ha
  right
  suffices (⌈a⌉ : R) = ⌊a⌋ + 1 by
    rw [this]; rw [← self_sub_fract]
    abel
  rw [← Int.cast_one]; rw [← Int.cast_add]
  refine congrArg Int.cast (ceil_eq_iff.mpr ⟨?_, _root_.le_of_lt <| by simp⟩)
  rw [cast_add]; rw [cast_one]; rw [add_tsub_cancel_right]; rw [← self_sub_fract a]; rw [sub_lt_self_iff]
  exact ha.symm.lt_of_le (fract_nonneg a)

Depends on / 依赖: Int.cast, Int.cast_add, Int.cast_one, Or.inl, _root_, _root_.le_of_lt, add_tsub_cancel_right, cast_add, cast_one, ceil_eq_iff, ceil_eq_iff.mpr, eq_or_ne, fract_nonneg, ha.symm.lt_of_le, le_of_lt, lt_of_le, self_sub_fract, sub_lt_self_iff
-/
theorem fract_eq_zero_or_add_one_sub_ceil (a : R) : fract a = 0 ∨ fract a = a + 1 - (⌈a⌉ : R) := by
  rcases eq_or_ne (fract a) 0 with ha | ha
  · exact Or.inl ha
  right
  suffices (⌈a⌉ : R) = ⌊a⌋ + 1 by
    rw [this]; rw [← self_sub_fract]
    abel
  rw [← Int.cast_one]; rw [← Int.cast_add]
  refine congrArg Int.cast (ceil_eq_iff.mpr ⟨?_, _root_.le_of_lt <| by simp⟩)
  rw [cast_add]; rw [cast_one]; rw [add_tsub_cancel_right]; rw [← self_sub_fract a]; rw [sub_lt_self_iff]
  exact ha.symm.lt_of_le (fract_nonneg a)

/--
theorem `ceil_eq_add_one_sub_fract` / 定理 `ceil_eq_add_one_sub_fract`

English:
theorem ceil_eq_add_one_sub_fract
  given: (ha : fract a != 0)
  statement: (⌈a⌉ : R) = a + 1 - fract a
  proof: by
  rw [(or_iff_right ha).mp (fract_eq_zero_or_add_one_sub_ceil a)]
  abel

中文:
定理 ceil_eq_add_one_sub_fract
  条件: (ha : fract a != 0)
  结论: (⌈a⌉ : R) = a + 1 - fract a
  证明: by
  rw [(or_iff_right ha).mp (fract_eq_zero_or_add_one_sub_ceil a)]
  abel

Depends on / 依赖: fract_eq_zero_or_add_one_sub_ceil, or_iff_right
-/
theorem ceil_eq_add_one_sub_fract (ha : fract a != 0) : (⌈a⌉ : R) = a + 1 - fract a := by
  rw [(or_iff_right ha).mp (fract_eq_zero_or_add_one_sub_ceil a)]
  abel

/--
theorem `ceil_sub_self_eq` / 定理 `ceil_sub_self_eq`

English:
theorem ceil_sub_self_eq
  given: (ha : fract a != 0)
  statement: (⌈a⌉ : R) - a = 1 - fract a
  proof: by
  rw [(or_iff_right ha).mp (fract_eq_zero_or_add_one_sub_ceil a)]
  abel

中文:
定理 ceil_sub_self_eq
  条件: (ha : fract a != 0)
  结论: (⌈a⌉ : R) - a = 1 - fract a
  证明: by
  rw [(or_iff_right ha).mp (fract_eq_zero_or_add_one_sub_ceil a)]
  abel

Depends on / 依赖: fract_eq_zero_or_add_one_sub_ceil, or_iff_right
-/
theorem ceil_sub_self_eq (ha : fract a != 0) : (⌈a⌉ : R) - a = 1 - fract a := by
  rw [(or_iff_right ha).mp (fract_eq_zero_or_add_one_sub_ceil a)]
  abel

end ceil

section LinearOrderedField
variable {k : Type*} [Field k] [LinearOrder k] [IsOrderedRing k] [FloorRing k] {a b : k}

/--
lemma `mul_lt_floor` / 引理 `mul_lt_floor`

English:
lemma mul_lt_floor
  given: (hb₀ : 0 < b) (hb : b < 1) (hba : ⌈b / (1 - b)⌉ <= a)
  statement: b * a < ⌊a⌋
  proof: by
  calc
    b * a < b * (⌊a⌋ + 1) := by gcongr; apply lt_floor_add_one
    _ <= ⌊a⌋ := by
      rwa [_root_.mul_add_one, ← le_sub_iff_add_le', ← one_sub_mul, ← div_le_iff₀' (by linarith),
        ← ceil_le, le_floor]

中文:
引理 mul_lt_floor
  条件: (hb₀ : 0 < b) (hb : b < 1) (hba : ⌈b / (1 - b)⌉ <= a)
  结论: b * a < ⌊a⌋
  证明: by
  calc
    b * a < b * (⌊a⌋ + 1) := by gcongr; apply lt_floor_add_one
    _ <= ⌊a⌋ := by
      rwa [_root_.mul_add_one, ← le_sub_iff_add_le', ← one_sub_mul, ← div_le_iff₀' (by linarith),
        ← ceil_le, le_floor]

Depends on / 依赖: _root_, _root_.mul_add_one, ceil_le, le_floor, le_sub_iff_add_le, lt_floor_add_one, mul_add_one, one_sub_mul
-/
lemma mul_lt_floor (hb₀ : 0 < b) (hb : b < 1) (hba : ⌈b / (1 - b)⌉ <= a) : b * a < ⌊a⌋ := by
  calc
    b * a < b * (⌊a⌋ + 1) := by gcongr; apply lt_floor_add_one
    _ <= ⌊a⌋ := by
      rwa [_root_.mul_add_one, ← le_sub_iff_add_le', ← one_sub_mul, ← div_le_iff₀' (by linarith),
        ← ceil_le, le_floor]

/--
lemma `ceil_div_ceil_inv_sub_one` / 引理 `ceil_div_ceil_inv_sub_one`

English:
lemma ceil_div_ceil_inv_sub_one
  given: (ha : 1 <= a)
  statement: ⌈⌈(a - 1)⁻¹⌉ / a⌉ = ⌈(a - 1)⁻¹⌉
  proof: by
  obtain rfl | ha := ha.eq_or_lt
  · simp
  have : 0 < a - 1 := by linarith
refine le_antisymm (ceil_le.2 <| div_le_self (by positivity) ha.le) ?_
  rw [le_ceil_iff]; rw [sub_lt_comm]; rw [div_eq_mul_inv]; rw [← mul_one_sub]; rw [← lt_div_iff₀ (sub_pos.2 <| inv_lt_one_of_one_lt₀ ha)]
  convert ceil_lt_add_one (R := k) _
  field

中文:
引理 ceil_div_ceil_inv_sub_one
  条件: (ha : 1 <= a)
  结论: ⌈⌈(a - 1)⁻¹⌉ / a⌉ = ⌈(a - 1)⁻¹⌉
  证明: by
  obtain rfl | ha := ha.eq_or_lt
  · simp
  have : 0 < a - 1 := by linarith
refine le_antisymm (ceil_le.2 <| div_le_self (by positivity) ha.le) ?_
  rw [le_ceil_iff]; rw [sub_lt_comm]; rw [div_eq_mul_inv]; rw [← mul_one_sub]; rw [← lt_div_iff₀ (sub_pos.2 <| inv_lt_one_of_one_lt₀ ha)]
  convert ceil_lt_add_one (R := k) _
  field

Depends on / 依赖: ceil_le, ceil_lt_add_one, convert, div_eq_mul_inv, div_le_self, eq_or_lt, ha.eq_or_lt, ha.le, le_antisymm, le_ceil_iff, mul_one_sub, sub_lt_comm, sub_pos
-/
lemma ceil_div_ceil_inv_sub_one (ha : 1 <= a) : ⌈⌈(a - 1)⁻¹⌉ / a⌉ = ⌈(a - 1)⁻¹⌉ := by
  obtain rfl | ha := ha.eq_or_lt
  · simp
  have : 0 < a - 1 := by linarith
refine le_antisymm (ceil_le.2 <| div_le_self (by positivity) ha.le) ?_
  rw [le_ceil_iff]; rw [sub_lt_comm]; rw [div_eq_mul_inv]; rw [← mul_one_sub]; rw [← lt_div_iff₀ (sub_pos.2 <| inv_lt_one_of_one_lt₀ ha)]
  convert ceil_lt_add_one (R := k) _
  field

/--
lemma `ceil_lt_mul` / 引理 `ceil_lt_mul`

English:
lemma ceil_lt_mul
  given: (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b < a)
  statement: ⌈a⌉ < b * a
  proof: by
  obtain hab | hba := le_total a (b - 1)⁻¹
  · calc
      ⌈a⌉ <= (⌈(b - 1)⁻¹⌉ : k) := by gcongr
      _ < b * a := by rwa [← div_lt_iff₀']; positivity
  · rw [← sub_pos] at hb
    calc
      ⌈a⌉ < a + 1 := ceil_lt_add_one _
      _ = a + (b - 1) * (b - 1)⁻¹ := by rw [mul_inv_cancel₀]; positivity
      _ <= a + (b - 1) * a := by gcongr
      _ = b * a := by rw [sub_one_mul, add_sub_cancel]

中文:
引理 ceil_lt_mul
  条件: (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b < a)
  结论: ⌈a⌉ < b * a
  证明: by
  obtain hab | hba := le_total a (b - 1)⁻¹
  · calc
      ⌈a⌉ <= (⌈(b - 1)⁻¹⌉ : k) := by gcongr
      _ < b * a := by rwa [← div_lt_iff₀']; positivity
  · rw [← sub_pos] at hb
    calc
      ⌈a⌉ < a + 1 := ceil_lt_add_one _
      _ = a + (b - 1) * (b - 1)⁻¹ := by rw [mul_inv_cancel₀]; positivity
      _ <= a + (b - 1) * a := by gcongr
      _ = b * a := by rw [sub_one_mul, add_sub_cancel]

Depends on / 依赖: add_sub_cancel, ceil_lt_add_one, le_total, sub_one_mul, sub_pos
-/
lemma ceil_lt_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b < a) : ⌈a⌉ < b * a := by
  obtain hab | hba := le_total a (b - 1)⁻¹
  · calc
      ⌈a⌉ <= (⌈(b - 1)⁻¹⌉ : k) := by gcongr
      _ < b * a := by rwa [← div_lt_iff₀']; positivity
  · rw [← sub_pos] at hb
    calc
      ⌈a⌉ < a + 1 := ceil_lt_add_one _
      _ = a + (b - 1) * (b - 1)⁻¹ := by rw [mul_inv_cancel₀]; positivity
      _ <= a + (b - 1) * a := by gcongr
      _ = b * a := by rw [sub_one_mul, add_sub_cancel]

/--
lemma `ceil_le_mul` / 引理 `ceil_le_mul`

English:
lemma ceil_le_mul
  given: (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b <= a)
  statement: ⌈a⌉ <= b * a
  proof: by
  obtain rfl | hba := hba.eq_or_lt
  · rw [ceil_div_ceil_inv_sub_one hb.le, mul_div_cancel₀]
    positivity
  · exact (ceil_lt_mul hb hba).le

中文:
引理 ceil_le_mul
  条件: (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b <= a)
  结论: ⌈a⌉ <= b * a
  证明: by
  obtain rfl | hba := hba.eq_or_lt
  · rw [ceil_div_ceil_inv_sub_one hb.le, mul_div_cancel₀]
    positivity
  · exact (ceil_lt_mul hb hba).le

Depends on / 依赖: ceil_div_ceil_inv_sub_one, ceil_lt_mul, eq_or_lt, hb.le, hba.eq_or_lt
-/
lemma ceil_le_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b <= a) : ⌈a⌉ <= b * a := by
  obtain rfl | hba := hba.eq_or_lt
  · rw [ceil_div_ceil_inv_sub_one hb.le, mul_div_cancel₀]
    positivity
  · exact (ceil_lt_mul hb hba).le

/--
lemma `div_two_lt_floor` / 引理 `div_two_lt_floor`

English:
lemma div_two_lt_floor
  given: (ha : 1 <= a)
  statement: a / 2 < ⌊a⌋
  proof: by
  rw [div_eq_inv_mul]; refine mul_lt_floor ?_ ?_ ?_ <;> norm_num; assumption

中文:
引理 div_two_lt_floor
  条件: (ha : 1 <= a)
  结论: a / 2 < ⌊a⌋
  证明: by
  rw [div_eq_inv_mul]; refine mul_lt_floor ?_ ?_ ?_ <;> norm_num; assumption

Depends on / 依赖: div_eq_inv_mul, mul_lt_floor
-/
lemma div_two_lt_floor (ha : 1 <= a) : a / 2 < ⌊a⌋ := by
  rw [div_eq_inv_mul]; refine mul_lt_floor ?_ ?_ ?_ <;> norm_num; assumption

/--
lemma `ceil_lt_two_mul` / 引理 `ceil_lt_two_mul`

English:
lemma ceil_lt_two_mul
  given: (ha : 2⁻¹ < a)
  statement: ⌈a⌉ < 2 * a
  proof: ceil_lt_mul one_lt_two (by norm_num at ha ⊢; exact ha)

中文:
引理 ceil_lt_two_mul
  条件: (ha : 2⁻¹ < a)
  结论: ⌈a⌉ < 2 * a
  证明: ceil_lt_mul one_lt_two (by norm_num at ha ⊢; exact ha)

Depends on / 依赖: ceil_lt_mul, one_lt_two
-/
lemma ceil_lt_two_mul (ha : 2⁻¹ < a) : ⌈a⌉ < 2 * a :=
  ceil_lt_mul one_lt_two (by norm_num at ha ⊢; exact ha)

/--
lemma `ceil_le_two_mul` / 引理 `ceil_le_two_mul`

English:
lemma ceil_le_two_mul
  given: (ha : 2⁻¹ <= a)
  statement: ⌈a⌉ <= 2 * a
  proof: ceil_le_mul one_lt_two (by norm_num at ha ⊢; exact ha)

中文:
引理 ceil_le_two_mul
  条件: (ha : 2⁻¹ <= a)
  结论: ⌈a⌉ <= 2 * a
  证明: ceil_le_mul one_lt_two (by norm_num at ha ⊢; exact ha)

Depends on / 依赖: ceil_le_mul, one_lt_two
-/
lemma ceil_le_two_mul (ha : 2⁻¹ <= a) : ⌈a⌉ <= 2 * a :=
  ceil_le_mul one_lt_two (by norm_num at ha ⊢; exact ha)

end LinearOrderedField

/-! #### Intervals -/

@[simp]
/--
theorem `preimage_Ioo` / 定理 `preimage_Ioo`

English:
theorem preimage_Ioo
  given: {a b : R}
  statement: ((↑) : Int -> R) ⁻¹' Set.Ioo a b = Set.Ioo ⌊a⌋ ⌈b⌉
  proof: by
  ext
  simp [floor_lt, lt_ceil]

@[simp]

中文:
定理 preimage_Ioo
  条件: {a b : R}
  结论: ((↑) : 整数 -> R) ⁻¹' 集合.开区间 a b = 集合.开区间 ⌊a⌋ ⌈b⌉
  证明: by
  ext
  simp [floor_lt, lt_ceil]

@[simp]

Depends on / 依赖: floor_lt, lt_ceil
-/
theorem preimage_Ioo {a b : R} : ((↑) : Int -> R) ⁻¹' Set.Ioo a b = Set.Ioo ⌊a⌋ ⌈b⌉ := by
  ext
  simp [floor_lt, lt_ceil]

@[simp]
/--
theorem `preimage_Ico` / 定理 `preimage_Ico`

English:
theorem preimage_Ico
  given: {a b : R}
  statement: ((↑) : Int -> R) ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉ ⌈b⌉
  proof: by
  ext
  simp [ceil_le, lt_ceil]

@[simp]

中文:
定理 preimage_Ico
  条件: {a b : R}
  结论: ((↑) : 整数 -> R) ⁻¹' 集合.左闭右开区间 a b = 集合.左闭右开区间 ⌈a⌉ ⌈b⌉
  证明: by
  ext
  simp [ceil_le, lt_ceil]

@[simp]

Depends on / 依赖: ceil_le, lt_ceil
-/
theorem preimage_Ico {a b : R} : ((↑) : Int -> R) ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉ ⌈b⌉ := by
  ext
  simp [ceil_le, lt_ceil]

@[simp]
/--
theorem `preimage_Ioc` / 定理 `preimage_Ioc`

English:
theorem preimage_Ioc
  given: {a b : R}
  statement: ((↑) : Int -> R) ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋ ⌊b⌋
  proof: by
  ext
  simp [floor_lt, le_floor]

@[simp]

中文:
定理 preimage_Ioc
  条件: {a b : R}
  结论: ((↑) : 整数 -> R) ⁻¹' 集合.左开右闭区间 a b = 集合.左开右闭区间 ⌊a⌋ ⌊b⌋
  证明: by
  ext
  simp [floor_lt, le_floor]

@[simp]

Depends on / 依赖: floor_lt, le_floor
-/
theorem preimage_Ioc {a b : R} : ((↑) : Int -> R) ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋ ⌊b⌋ := by
  ext
  simp [floor_lt, le_floor]

@[simp]
/--
theorem `preimage_Icc` / 定理 `preimage_Icc`

English:
theorem preimage_Icc
  given: {a b : R}
  statement: ((↑) : Int -> R) ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉ ⌊b⌋
  proof: by
  ext
  simp [ceil_le, le_floor]

@[simp]

中文:
定理 preimage_Icc
  条件: {a b : R}
  结论: ((↑) : 整数 -> R) ⁻¹' 集合.闭区间 a b = 集合.闭区间 ⌈a⌉ ⌊b⌋
  证明: by
  ext
  simp [ceil_le, le_floor]

@[simp]

Depends on / 依赖: ceil_le, le_floor
-/
theorem preimage_Icc {a b : R} : ((↑) : Int -> R) ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉ ⌊b⌋ := by
  ext
  simp [ceil_le, le_floor]

@[simp]
/--
theorem `preimage_Ioi` / 定理 `preimage_Ioi`

English:
theorem preimage_Ioi
  statement: ((↑) : Int -> R) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋
  proof: by
  ext
  simp [floor_lt]

@[simp]

中文:
定理 preimage_Ioi
  结论: ((↑) : 整数 -> R) ⁻¹' 集合.左开右无界区间 a = 集合.左开右无界区间 ⌊a⌋
  证明: by
  ext
  simp [floor_lt]

@[simp]

Depends on / 依赖: floor_lt
-/
theorem preimage_Ioi : ((↑) : Int -> R) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋ := by
  ext
  simp [floor_lt]

@[simp]
/--
theorem `preimage_Ici` / 定理 `preimage_Ici`

English:
theorem preimage_Ici
  statement: ((↑) : Int -> R) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉
  proof: by
  ext
  simp [ceil_le]

@[simp]

中文:
定理 preimage_Ici
  结论: ((↑) : 整数 -> R) ⁻¹' 集合.左闭右无界区间 a = 集合.左闭右无界区间 ⌈a⌉
  证明: by
  ext
  simp [ceil_le]

@[simp]

Depends on / 依赖: ceil_le
-/
theorem preimage_Ici : ((↑) : Int -> R) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉ := by
  ext
  simp [ceil_le]

@[simp]
/--
theorem `preimage_Iio` / 定理 `preimage_Iio`

English:
theorem preimage_Iio
  statement: ((↑) : Int -> R) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉
  proof: by
  ext
  simp [lt_ceil]

@[simp]

中文:
定理 preimage_Iio
  结论: ((↑) : 整数 -> R) ⁻¹' 集合.左无界右开区间 a = 集合.左无界右开区间 ⌈a⌉
  证明: by
  ext
  simp [lt_ceil]

@[simp]

Depends on / 依赖: lt_ceil
-/
theorem preimage_Iio : ((↑) : Int -> R) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉ := by
  ext
  simp [lt_ceil]

@[simp]
/--
theorem `preimage_Iic` / 定理 `preimage_Iic`

English:
theorem preimage_Iic
  statement: ((↑) : Int -> R) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋
  proof: by
  ext
  simp [le_floor]

中文:
定理 preimage_Iic
  结论: ((↑) : 整数 -> R) ⁻¹' 集合.左无界右闭区间 a = 集合.左无界右闭区间 ⌊a⌋
  证明: by
  ext
  simp [le_floor]

Depends on / 依赖: le_floor
-/
theorem preimage_Iic : ((↑) : Int -> R) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋ := by
  ext
  simp [le_floor]

end Int

namespace Int

variable [Ring R] [LinearOrder R] [Ring S] [LinearOrder S] [FloorRing R] [FloorRing S]
variable [FunLike F R S] [RingHomClass F R S] {a : R} {b : S}

/--
theorem `floor_congr` / 定理 `floor_congr`

English:
theorem floor_congr
  given: (h : forall n : Int, (n : R) <= a ↔ (n : S) <= b)
  statement: ⌊a⌋ = ⌊b⌋
  proof: (le_floor.2 <| (h _).1 <| floor_le _).antisymm le_floor.2 (h _).2 floor_le _

中文:
定理 floor_congr
  条件: (h : 对任意 n : 整数, (n : R) <= a ↔ (n : S) <= b)
  结论: ⌊a⌋ = ⌊b⌋
  证明: (le_floor.2 <| (h _).1 <| floor_le _).antisymm le_floor.2 (h _).2 floor_le _

Depends on / 依赖: antisymm, floor_le, le_floor
-/
theorem floor_congr (h : forall n : Int, (n : R) <= a ↔ (n : S) <= b) : ⌊a⌋ = ⌊b⌋ :=
(le_floor.2 <| (h _).1 <| floor_le _).antisymm le_floor.2 (h _).2 floor_le _

/--
theorem `ceil_congr` / 定理 `ceil_congr`

English:
theorem ceil_congr
  given: (h : forall n : Int, a <= n ↔ b <= n)
  statement: ⌈a⌉ = ⌈b⌉
  proof: (ceil_le.2 <| (h _).2 <| le_ceil _).antisymm ceil_le.2 (h _).1 le_ceil _

中文:
定理 ceil_congr
  条件: (h : 对任意 n : 整数, a <= n ↔ b <= n)
  结论: ⌈a⌉ = ⌈b⌉
  证明: (ceil_le.2 <| (h _).2 <| le_ceil _).antisymm ceil_le.2 (h _).1 le_ceil _

Depends on / 依赖: antisymm, ceil_le, le_ceil
-/
theorem ceil_congr (h : forall n : Int, a <= n ↔ b <= n) : ⌈a⌉ = ⌈b⌉ :=
(ceil_le.2 <| (h _).2 <| le_ceil _).antisymm ceil_le.2 (h _).1 le_ceil _

/--
theorem `map_floor` / 定理 `map_floor`

English:
theorem map_floor
  given: (f : F) (hf : StrictMono f) (a : R)
  statement: ⌊f a⌋ = ⌊a⌋
  proof: floor_congr fun n => by rw [← map_intCast f, hf.le_iff_le]

中文:
定理 map_floor
  条件: (f : F) (hf : 严格递增 f) (a : R)
  结论: ⌊f a⌋ = ⌊a⌋
  证明: floor_congr fun n => by rw [← map_intCast f, hf.le_iff_le]

Depends on / 依赖: floor_congr, hf.le_iff_le, le_iff_le, map_intCast
-/
theorem map_floor (f : F) (hf : StrictMono f) (a : R) : ⌊f a⌋ = ⌊a⌋ :=
  floor_congr fun n => by rw [← map_intCast f, hf.le_iff_le]

/--
theorem `map_ceil` / 定理 `map_ceil`

English:
theorem map_ceil
  given: (f : F) (hf : StrictMono f) (a : R)
  statement: ⌈f a⌉ = ⌈a⌉
  proof: ceil_congr fun n => by rw [← map_intCast f, hf.le_iff_le]

中文:
定理 map_ceil
  条件: (f : F) (hf : 严格递增 f) (a : R)
  结论: ⌈f a⌉ = ⌈a⌉
  证明: ceil_congr fun n => by rw [← map_intCast f, hf.le_iff_le]

Depends on / 依赖: ceil_congr, hf.le_iff_le, le_iff_le, map_intCast
-/
theorem map_ceil (f : F) (hf : StrictMono f) (a : R) : ⌈f a⌉ = ⌈a⌉ :=
  ceil_congr fun n => by rw [← map_intCast f, hf.le_iff_le]

/--
theorem `map_fract` / 定理 `map_fract`

English:
theorem map_fract
  given: (f : F) (hf : StrictMono f) (a : R)
  statement: fract (f a) = f (fract a)
  proof: by
  simp_rw [fract, map_sub, map_intCast, map_floor _ hf]

中文:
定理 map_fract
  条件: (f : F) (hf : 严格递增 f) (a : R)
  结论: fract (f a) = f (fract a)
  证明: by
  simp_rw [fract, map_sub, map_intCast, map_floor _ hf]

Depends on / 依赖: map_floor, map_intCast, map_sub, simp_rw
-/
theorem map_fract (f : F) (hf : StrictMono f) (a : R) : fract (f a) = f (fract a) := by
  simp_rw [fract, map_sub, map_intCast, map_floor _ hf]

end Int

namespace Nat

variable [Ring R] [LinearOrder R] [FloorRing R] [IsStrictOrderedRing R] {a : R}

/-- a variant of `Nat.ceil_lt_add_one` with its condition `0 ≤ a` generalized to `-1 < a` -/
@[bound]
/--
lemma `ceil_lt_add_one_of_gt_neg_one` / 引理 `ceil_lt_add_one_of_gt_neg_one`

English:
lemma ceil_lt_add_one_of_gt_neg_one
  given: (ha : -1 < a)
  statement: ⌈a⌉₊ < a + 1
  proof: by
  by_cases! h : 0 <= a
  · exact ceil_lt_add_one h
  · rw [ceil_eq_zero.mpr h.le, cast_zero]
    exact neg_lt_iff_pos_add.mp ha

中文:
引理 ceil_lt_add_one_of_gt_neg_one
  条件: (ha : -1 < a)
  结论: ⌈a⌉₊ < a + 1
  证明: by
  by_cases! h : 0 <= a
  · exact ceil_lt_add_one h
  · rw [ceil_eq_zero.mpr h.le, cast_zero]
    exact neg_lt_iff_pos_add.mp ha

Depends on / 依赖: cast_zero, ceil_eq_zero, ceil_eq_zero.mpr, ceil_lt_add_one, h.le, neg_lt_iff_pos_add, neg_lt_iff_pos_add.mp
-/
lemma ceil_lt_add_one_of_gt_neg_one (ha : -1 < a) : ⌈a⌉₊ < a + 1 := by
  by_cases! h : 0 <= a
  · exact ceil_lt_add_one h
  · rw [ceil_eq_zero.mpr h.le, cast_zero]
    exact neg_lt_iff_pos_add.mp ha

end Nat

section FloorRingToSemiring

variable [Ring R] [LinearOrder R] [FloorRing R]

/-! #### A floor ring as a floor semiring -/

variable {a : R}

/--
theorem `Int.natCast_floor_eq_floor` / 定理 `Int.natCast_floor_eq_floor`

English:
theorem Int.natCast_floor_eq_floor
  given: (ha : 0 <= a)
  statement: (⌊a⌋₊ : Int) = ⌊a⌋
  proof: by
  rw [← Int.floor_toNat]; rw [Int.toNat_of_nonneg (Int.floor_nonneg.2 ha)]

中文:
定理 整数.natCast_floor_eq_floor
  条件: (ha : 0 <= a)
  结论: (⌊a⌋₊ : 整数) = ⌊a⌋
  证明: by
  rw [← Int.floor_toNat]; rw [Int.toNat_of_nonneg (Int.floor_nonneg.2 ha)]

Depends on / 依赖: Int.floor_nonneg, Int.floor_toNat, Int.toNat_of_nonneg, floor_nonneg, floor_toNat, toNat_of_nonneg
-/
theorem Int.natCast_floor_eq_floor (ha : 0 <= a) : (⌊a⌋₊ : Int) = ⌊a⌋ := by
  rw [← Int.floor_toNat]; rw [Int.toNat_of_nonneg (Int.floor_nonneg.2 ha)]

/--
theorem `Int.natCast_ceil_eq_ceil` / 定理 `Int.natCast_ceil_eq_ceil`

English:
theorem Int.natCast_ceil_eq_ceil
  given: (ha : 0 <= a)
  statement: (⌈a⌉₊ : Int) = ⌈a⌉
  proof: by
  rw [← Int.ceil_toNat]; rw [Int.toNat_of_nonneg (Int.ceil_nonneg ha)]

中文:
定理 整数.natCast_ceil_eq_ceil
  条件: (ha : 0 <= a)
  结论: (⌈a⌉₊ : 整数) = ⌈a⌉
  证明: by
  rw [← Int.ceil_toNat]; rw [Int.toNat_of_nonneg (Int.ceil_nonneg ha)]

Depends on / 依赖: Int.ceil_nonneg, Int.ceil_toNat, Int.toNat_of_nonneg, ceil_nonneg, ceil_toNat, toNat_of_nonneg
-/
theorem Int.natCast_ceil_eq_ceil (ha : 0 <= a) : (⌈a⌉₊ : Int) = ⌈a⌉ := by
  rw [← Int.ceil_toNat]; rw [Int.toNat_of_nonneg (Int.ceil_nonneg ha)]

/--
theorem `Int.natCast_ceil_eq_ceil_of_neg_one_lt` / 定理 `Int.natCast_ceil_eq_ceil_of_neg_one_lt`

English:
theorem Int.natCast_ceil_eq_ceil_of_neg_one_lt
  given: (ha : -1 < a)
  statement: (⌈a⌉₊ : Int) = ⌈a⌉
  proof: by
  rw [← Int.ceil_toNat]; rw [Int.toNat_of_nonneg (Int.ceil_nonneg_of_neg_one_lt ha)]

中文:
定理 整数.natCast_ceil_eq_ceil_of_neg_one_lt
  条件: (ha : -1 < a)
  结论: (⌈a⌉₊ : 整数) = ⌈a⌉
  证明: by
  rw [← Int.ceil_toNat]; rw [Int.toNat_of_nonneg (Int.ceil_nonneg_of_neg_one_lt ha)]

Depends on / 依赖: Int.ceil_nonneg_of_neg_one_lt, Int.ceil_toNat, Int.toNat_of_nonneg, ceil_nonneg_of_neg_one_lt, ceil_toNat, toNat_of_nonneg
-/
theorem Int.natCast_ceil_eq_ceil_of_neg_one_lt (ha : -1 < a) : (⌈a⌉₊ : Int) = ⌈a⌉ := by
  rw [← Int.ceil_toNat]; rw [Int.toNat_of_nonneg (Int.ceil_nonneg_of_neg_one_lt ha)]

/--
theorem `natCast_floor_eq_intCast_floor` / 定理 `natCast_floor_eq_intCast_floor`

English:
theorem natCast_floor_eq_intCast_floor
  given: (ha : 0 <= a)
  statement: (⌊a⌋₊ : R) = ⌊a⌋
  proof: by
  rw [← Int.natCast_floor_eq_floor ha]; rw [Int.cast_natCast]

中文:
定理 natCast_floor_eq_intCast_floor
  条件: (ha : 0 <= a)
  结论: (⌊a⌋₊ : R) = ⌊a⌋
  证明: by
  rw [← Int.natCast_floor_eq_floor ha]; rw [Int.cast_natCast]

Depends on / 依赖: Int.cast_natCast, Int.natCast_floor_eq_floor, cast_natCast, natCast_floor_eq_floor
-/
theorem natCast_floor_eq_intCast_floor (ha : 0 <= a) : (⌊a⌋₊ : R) = ⌊a⌋ := by
  rw [← Int.natCast_floor_eq_floor ha]; rw [Int.cast_natCast]

/--
theorem `natCast_ceil_eq_intCast_ceil` / 定理 `natCast_ceil_eq_intCast_ceil`

English:
theorem natCast_ceil_eq_intCast_ceil
  given: (ha : 0 <= a)
  statement: (⌈a⌉₊ : R) = ⌈a⌉
  proof: by
  rw [← Int.natCast_ceil_eq_ceil ha]; rw [Int.cast_natCast]

中文:
定理 natCast_ceil_eq_intCast_ceil
  条件: (ha : 0 <= a)
  结论: (⌈a⌉₊ : R) = ⌈a⌉
  证明: by
  rw [← Int.natCast_ceil_eq_ceil ha]; rw [Int.cast_natCast]

Depends on / 依赖: Int.cast_natCast, Int.natCast_ceil_eq_ceil, cast_natCast, natCast_ceil_eq_ceil
-/
theorem natCast_ceil_eq_intCast_ceil (ha : 0 <= a) : (⌈a⌉₊ : R) = ⌈a⌉ := by
  rw [← Int.natCast_ceil_eq_ceil ha]; rw [Int.cast_natCast]

/--
theorem `natCast_ceil_eq_intCast_ceil_of_neg_one_lt` / 定理 `natCast_ceil_eq_intCast_ceil_of_neg_one_lt`

English:
theorem natCast_ceil_eq_intCast_ceil_of_neg_one_lt
  given: (ha : -1 < a)
  statement: (⌈a⌉₊ : R) = ⌈a⌉
  proof: by
  rw [← Int.natCast_ceil_eq_ceil_of_neg_one_lt ha]; rw [Int.cast_natCast]

中文:
定理 natCast_ceil_eq_intCast_ceil_of_neg_one_lt
  条件: (ha : -1 < a)
  结论: (⌈a⌉₊ : R) = ⌈a⌉
  证明: by
  rw [← Int.natCast_ceil_eq_ceil_of_neg_one_lt ha]; rw [Int.cast_natCast]

Depends on / 依赖: Int.cast_natCast, Int.natCast_ceil_eq_ceil_of_neg_one_lt, cast_natCast, natCast_ceil_eq_ceil_of_neg_one_lt
-/
theorem natCast_ceil_eq_intCast_ceil_of_neg_one_lt (ha : -1 < a) : (⌈a⌉₊ : R) = ⌈a⌉ := by
  rw [← Int.natCast_ceil_eq_ceil_of_neg_one_lt ha]; rw [Int.cast_natCast]

end FloorRingToSemiring

/--
theorem `subsingleton_floorRing` / 定理 `subsingleton_floorRing`

English:
theorem subsingleton_floorRing
  given: {R} [Ring R] [LinearOrder R]
  statement: Subsingleton (FloorRing R)
  proof: by
  refine ⟨fun H₁ H₂ => ?_⟩
  have : H₁.floor = H₂.floor :=
    funext fun a => (H₁.gc_coe_floor.u_unique H₂.gc_coe_floor) fun _ => rfl
  have : H₁.ceil = H₂.ceil := funext fun a => (H₁.gc_ceil_coe.l_unique H₂.gc_ceil_coe) fun _ => rfl
  cases H₁; cases H₂; congr

中文:
定理 subsingleton_floorRing
  条件: {R} [环 R] [线性序 R]
  结论: 子单例 (Floor环 R)
  证明: by
  refine ⟨fun H₁ H₂ => ?_⟩
  have : H₁.floor = H₂.floor :=
    funext fun a => (H₁.gc_coe_floor.u_unique H₂.gc_coe_floor) fun _ => rfl
  have : H₁.ceil = H₂.ceil := funext fun a => (H₁.gc_ceil_coe.l_unique H₂.gc_ceil_coe) fun _ => rfl
  cases H₁; cases H₂; congr

Depends on / 依赖: gc_ceil_coe, gc_ceil_coe.l_unique, gc_coe_floor, gc_coe_floor.u_unique, l_unique, u_unique
-/
theorem subsingleton_floorRing {R} [Ring R] [LinearOrder R] : Subsingleton (FloorRing R) := by
  refine ⟨fun H₁ H₂ => ?_⟩
  have : H₁.floor = H₂.floor :=
    funext fun a => (H₁.gc_coe_floor.u_unique H₂.gc_coe_floor) fun _ => rfl
  have : H₁.ceil = H₂.ceil := funext fun a => (H₁.gc_ceil_coe.l_unique H₂.gc_ceil_coe) fun _ => rfl
  cases H₁; cases H₂; congr

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `Int.fract` is always nonnegative. -/
@[positivity Int.fract _]
meta def evalIntFract : PositivityExt where eval {_u} (_α _zα pα?) e :=
  match pα? with | none => pure .none | some pα' => do
  let ~q(@Int.fract _ (_) (_) (_) $a) := e | throwError "not Int.fract"
  let pa' ← mkAppM ``Int.fract_nonneg #[a]
  pure (.nonnegative (pα := pα') pa')

end Mathlib.Meta.Positivity
