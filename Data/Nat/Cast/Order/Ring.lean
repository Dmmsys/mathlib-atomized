/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Cast of natural numbers: lemmas about bundled ordered semirings

-/

public section

variable {R α : Type*}

namespace Nat

section AddMonoidWithOne
variable [AddMonoidWithOne α] [PartialOrder α]
variable [AddLeftMono α] [ZeroLEOneClass α]

/-- Specialisation of `Nat.cast_nonneg'`, which seems to be easier for Lean to use. -/
@[simp]
/--
theorem `cast_nonneg` / 定理 `cast_nonneg`

English:
theorem cast_nonneg
  given: {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n : Nat)
  statement: 0 <= (n : α)
  proof: cast_nonneg' n

中文:
定理 cast_nonneg
  条件: {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n : 自然数)
  结论: 0 <= (n : α)
  证明: cast_nonneg' n

Depends on / 依赖: cast_nonneg
-/
theorem cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n : Nat) : 0 <= (n : α) :=
  cast_nonneg' n

/-- Specialisation of `Nat.ofNat_nonneg'`, which seems to be easier for Lean to use. -/
@[simp]
/--
theorem `ofNat_nonneg` / 定理 `ofNat_nonneg`

English:
theorem ofNat_nonneg
  given: {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n : Nat) [n.AtLeastTwo]
  proof: ofNat_nonneg' n

@[simp, norm_cast]

中文:
定理 ofNat_nonneg
  条件: {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n : 自然数) [n.AtLeastTwo]
  证明: ofNat_nonneg' n

@[simp, norm_cast]

Depends on / 依赖: ofNat_nonneg
-/
theorem ofNat_nonneg {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n : Nat) [n.AtLeastTwo] :
    0 <= (ofNat(n) : α) :=
  ofNat_nonneg' n

@[simp, norm_cast]
/--
theorem `cast_min` / 定理 `cast_min`

English:
theorem cast_min
  given: {α} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] (m n : Nat)
  proof: (@mono_cast α _).map_min

@[simp, norm_cast]

中文:
定理 cast_min
  条件: {α} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] (m n : 自然数)
  证明: (@mono_cast α _).map_min

@[simp, norm_cast]

Depends on / 依赖: map_min, mono_cast
-/
theorem cast_min {α} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] (m n : Nat) :
    (↑(min m n : Nat) : α) = min (m : α) n :=
  (@mono_cast α _).map_min

@[simp, norm_cast]
/--
theorem `cast_max` / 定理 `cast_max`

English:
theorem cast_max
  given: {α} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] (m n : Nat)
  proof: (@mono_cast α _).map_max

中文:
定理 cast_max
  条件: {α} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] (m n : 自然数)
  证明: (@mono_cast α _).map_max

Depends on / 依赖: map_max, mono_cast
-/
theorem cast_max {α} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] (m n : Nat) :
    (↑(max m n : Nat) : α) = max (m : α) n :=
  (@mono_cast α _).map_max

section Nontrivial

variable [NeZero (1 : α)]

/-- Specialisation of `Nat.cast_pos'`, which seems to be easier for Lean to use. -/
@[simp]
/--
theorem `cast_pos` / 定理 `cast_pos`

English:
theorem cast_pos
  given: {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α] {n : Nat}
  proof: cast_pos'

中文:
定理 cast_pos
  条件: {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α] {n : 自然数}
  证明: cast_pos'

Depends on / 依赖: cast_pos
-/
theorem cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α] {n : Nat} :
    (0 : α) < n ↔ 0 < n := cast_pos'

/-- See also `Nat.ofNat_pos`, specialised to `IsOrderedRing`. -/
@[simp low]
/--
theorem `ofNat_pos'` / 定理 `ofNat_pos'`

English:
theorem ofNat_pos'
  given: {n : Nat} [n.AtLeastTwo]
  statement: 0 < (ofNat(n) : α)
  proof: cast_pos'.mpr (NeZero.pos n)

中文:
定理 ofNat_pos'
  条件: {n : 自然数} [n.AtLeastTwo]
  结论: 0 < (of自然数(n) : α)
  证明: cast_pos'.mpr (NeZero.pos n)

Depends on / 依赖: NeZero, NeZero.pos, cast_pos
-/
theorem ofNat_pos' {n : Nat} [n.AtLeastTwo] : 0 < (ofNat(n) : α) :=
  cast_pos'.mpr (NeZero.pos n)

/-- Specialisation of `Nat.ofNat_pos'`, which seems to be easier for Lean to use. -/
@[simp]
/--
theorem `ofNat_pos` / 定理 `ofNat_pos`

English:
theorem ofNat_pos
  statement: {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α]
  proof: ofNat_pos'

中文:
定理 ofNat_pos
  结论: {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α]
  证明: ofNat_pos'

Depends on / 依赖: ofNat_pos
-/
theorem ofNat_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α]
    {n : Nat} [n.AtLeastTwo] :
    0 < (ofNat(n) : α) :=
  ofNat_pos'

end Nontrivial

end AddMonoidWithOne

/-- A version of `Nat.cast_sub` that works for `ℝ≥0` and `ℚ≥0`. Note that this proof doesn't work
for `ℕ∞` and `ℝ≥0∞`, so we use type-specific lemmas for these types. -/
@[simp, norm_cast]
/--
theorem `cast_tsub` / 定理 `cast_tsub`

English:
theorem cast_tsub
  statement: [CommSemiring α] [PartialOrder α] [IsOrderedRing α] [CanonicallyOrderedAdd α]
  proof: by
  rcases le_total m n with h | h
  · rw [Nat.sub_eq_zero_of_le h, cast_zero, tsub_eq_zero_of_le]
    exact mono_cast h
  · rcases le_iff_exists_add'.mp h with ⟨m, rfl⟩
    rw [add_tsub_cancel_right]; rw [cast_add]; rw [add_tsub_cancel_right]

中文:
定理 cast_tsub
  结论: [CommSemiring α] [PartialOrder α] [IsOrderedRing α] [CanonicallyOrderedAdd α]
  证明: by
  rcases le_total m n with h | h
  · rw [Nat.sub_eq_zero_of_le h, cast_zero, tsub_eq_zero_of_le]
    exact mono_cast h
  · rcases le_iff_exists_add'.mp h with ⟨m, rfl⟩
    rw [add_tsub_cancel_right]; rw [cast_add]; rw [add_tsub_cancel_right]

Depends on / 依赖: Nat.sub_eq_zero_of_le, add_tsub_cancel_right, cast_add, cast_zero, le_iff_exists_add, le_total, mono_cast, sub_eq_zero_of_le, tsub_eq_zero_of_le
-/
theorem cast_tsub [CommSemiring α] [PartialOrder α] [IsOrderedRing α] [CanonicallyOrderedAdd α]
    [Sub α] [OrderedSub α] [AddLeftReflectLE α] (m n : Nat) : ↑(m - n) = (m - n : α) := by
  rcases le_total m n with h | h
  · rw [Nat.sub_eq_zero_of_le h, cast_zero, tsub_eq_zero_of_le]
    exact mono_cast h
  · rcases le_iff_exists_add'.mp h with ⟨m, rfl⟩
    rw [add_tsub_cancel_right]; rw [cast_add]; rw [add_tsub_cancel_right]

section Lattice
variable [Ring R] [Lattice R] [IsOrderedRing R]

@[simp, norm_cast]
/--
theorem `abs_cast` / 定理 `abs_cast`

English:
theorem abs_cast
  given: (n : Nat)
  statement: |(n : R)| = n
  proof: abs_of_nonneg n.cast_nonneg

@[simp]

中文:
定理 abs_cast
  条件: (n : 自然数)
  结论: |(n : R)| = n
  证明: abs_of_nonneg n.cast_nonneg

@[simp]

Depends on / 依赖: abs_of_nonneg, cast_nonneg, n.cast_nonneg
-/
theorem abs_cast (n : Nat) : |(n : R)| = n := abs_of_nonneg n.cast_nonneg

@[simp]
/--
theorem `abs_ofNat` / 定理 `abs_ofNat`

English:
theorem abs_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: |(ofNat(n) : R)| = ofNat(n)
  proof: abs_cast n

中文:
定理 abs_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: |(of自然数(n) : R)| = of自然数(n)
  证明: abs_cast n

Depends on / 依赖: abs_cast
-/
theorem abs_ofNat (n : Nat) [n.AtLeastTwo] : |(ofNat(n) : R)| = ofNat(n) := abs_cast n

end Lattice

section PartialOrderedRing

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] {m n : Nat}

/--
lemma `neg_cast_eq_cast` / 引理 `neg_cast_eq_cast`

English:
lemma neg_cast_eq_cast
  statement: (-m : R) = n ↔ m = 0 ∧ n = 0
  proof: by
  simp [neg_eq_iff_add_eq_zero, ← cast_add]

中文:
引理 neg_cast_eq_cast
  结论: (-m : R) = n ↔ m = 0 ∧ n = 0
  证明: by
  simp [neg_eq_iff_add_eq_zero, ← cast_add]
-/
@[simp, norm_cast] lemma neg_cast_eq_cast : (-m : R) = n ↔ m = 0 ∧ n = 0 := by
  simp [neg_eq_iff_add_eq_zero, ← cast_add]

/--
lemma `cast_eq_neg_cast` / 引理 `cast_eq_neg_cast`

English:
lemma cast_eq_neg_cast
  statement: (m : R) = -n ↔ m = 0 ∧ n = 0
  proof: by
  simp [eq_neg_iff_add_eq_zero, ← cast_add]

中文:
引理 cast_eq_neg_cast
  结论: (m : R) = -n ↔ m = 0 ∧ n = 0
  证明: by
  simp [eq_neg_iff_add_eq_zero, ← cast_add]
-/
@[simp, norm_cast] lemma cast_eq_neg_cast : (m : R) = -n ↔ m = 0 ∧ n = 0 := by
  simp [eq_neg_iff_add_eq_zero, ← cast_add]

end PartialOrderedRing

end Nat
