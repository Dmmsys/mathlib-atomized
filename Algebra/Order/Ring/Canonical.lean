/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Ring.Parity

/-!
# Canonically ordered rings and semirings.
-/

public section


open Function

universe u

variable {R : Type u}

-- see Note [lower instance priority]
instance (priority := 10) CanonicallyOrderedAdd.toZeroLEOneClass
    [AddZeroClass R] [One R] [LE R] [CanonicallyOrderedAdd R] : ZeroLEOneClass R where
  zero_le_one := zero_le

-- this holds more generally if we refactor `Odd` to use
-- either `2 • t` or `t + t` instead of `2 * t`.
/--
lemma `Odd.pos` / 引理 `Odd.pos`

English:
lemma Odd.pos
  given: [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R] [Nontrivial R] {a : R}
  proof: by
  rintro ⟨k, rfl⟩; simp

中文:
引理 Odd.pos
  条件: [半环 R] [偏序 R] [典范有序加法 R] [非平凡 R] {a : R}
  证明: by
  rintro ⟨k, rfl⟩; simp
-/
lemma Odd.pos [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R] [Nontrivial R] {a : R} :
    Odd a -> 0 < a := by
  rintro ⟨k, rfl⟩; simp

namespace CanonicallyOrderedAdd

-- see Note [lower instance priority]
instance (priority := 100) toMulLeftMono [NonUnitalNonAssocSemiring R]
    [LE R] [CanonicallyOrderedAdd R] : MulLeftMono R := by
  refine ⟨fun a b c h => ?_⟩
  rcases exists_add_of_le h with ⟨c, rfl⟩
  rw [mul_add]
  apply self_le_add_right

-- see Note [lower instance priority]
instance (priority := 100) toMulRightMono [NonUnitalNonAssocSemiring R]
    [LE R] [CanonicallyOrderedAdd R] : MulRightMono R := by
  refine ⟨fun a b c h => ?_⟩
  dsimp [swap]
  rcases exists_add_of_le h with ⟨c, rfl⟩
  rw [add_mul]
  apply self_le_add_right

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]

-- TODO: make it an instance
/--
lemma `toIsOrderedMonoid` / 引理 `toIsOrderedMonoid`

English:
lemma toIsOrderedMonoid
  statement: IsOrderedMonoid R where
  proof: mul_le_mul_left

中文:
引理 toIsOrderedMonoid
  结论: 是Ordered幺半群 R where
  证明: mul_le_mul_left

Depends on / 依赖: mul_le_mul_left
-/
lemma toIsOrderedMonoid : IsOrderedMonoid R where
  mul_le_mul_left _ _ := mul_le_mul_left

-- TODO: make it an instance
/--
lemma `toIsOrderedRing` / 引理 `toIsOrderedRing`

English:
lemma toIsOrderedRing
  statement: IsOrderedRing R where
  proof: add_le_add_left

@[simp]

中文:
引理 toIsOrderedRing
  结论: 是Ordered环 R where
  证明: add_le_add_left

@[simp]

Depends on / 依赖: add_le_add_left
-/
lemma toIsOrderedRing : IsOrderedRing R where
  add_le_add_left _ _ := add_le_add_left

@[simp]
/--
theorem `mul_pos` / 定理 `mul_pos`

English:
theorem mul_pos
  given: [NoZeroDivisors R] {a b : R}
  proof: by
  simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]

中文:
定理 mul_pos
  条件: [无零因子 R] {a b : R}
  证明: by
  simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]
-/
protected theorem mul_pos [NoZeroDivisors R] {a b : R} :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]

/--
lemma `pow_pos` / 引理 `pow_pos`

English:
lemma pow_pos
  given: [IsReduced R] {a : R} (ha : 0 < a) (n : Nat)
  statement: 0 < a ^ n
  proof: pos_iff_ne_zero.2 pow_ne_zero _ ha.ne'

中文:
引理 pow_pos
  条件: [是既约 R] {a : R} (ha : 0 < a) (n : 自然数)
  结论: 0 < a ^ n
  证明: pos_iff_ne_zero.2 pow_ne_zero _ ha.ne'

Depends on / 依赖: ha.ne, pos_iff_ne_zero, pow_ne_zero
-/
lemma pow_pos [IsReduced R] {a : R} (ha : 0 < a) (n : Nat) : 0 < a ^ n :=
pos_iff_ne_zero.2 pow_ne_zero _ ha.ne'

/--
lemma `mul_lt_mul_of_lt_of_lt` / 引理 `mul_lt_mul_of_lt_of_lt`

English:
lemma mul_lt_mul_of_lt_of_lt
  proof: by
  -- TODO: This should be an instance but it currently times out
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  obtain rfl | hc := eq_zero_or_pos c
  · rw [mul_zero]
    exact mul_pos hab.pos hcd
  · exact mul_lt_mul_of_pos' hab hcd hc hab.pos

中文:
引理 mul_lt_mul_of_lt_of_lt
  证明: by
  -- TODO: This should be an instance but it currently times out
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  obtain rfl | hc := eq_zero_or_pos c
  · rw [mul_zero]
    exact mul_pos hab.pos hcd
  · exact mul_lt_mul_of_pos' hab hcd hc hab.pos
-/
protected lemma mul_lt_mul_of_lt_of_lt
    [PosMulStrictMono R] {a b c d : R} (hab : a < b) (hcd : c < d) :
    a * c < b * d := by
  -- TODO: This should be an instance but it currently times out
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  obtain rfl | hc := eq_zero_or_pos c
  · rw [mul_zero]
    exact mul_pos hab.pos hcd
  · exact mul_lt_mul_of_pos' hab hcd hc hab.pos

end CanonicallyOrderedAdd

section Sub

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· <= ·)]

namespace AddLECancellable

/--
theorem `mul_tsub` / 定理 `mul_tsub`

English:
theorem mul_tsub
  statement: {a b c : R}
  proof: by
  obtain (hbc | hcb) := total_of (· <= ·) b c
  · rw [tsub_eq_zero_iff_le.2 hbc, mul_zero, tsub_eq_zero_iff_le.2 (mul_le_mul_right hbc a)]
  · apply h.eq_tsub_of_add_eq
    rw [← mul_add]; rw [tsub_add_cancel_of_le hcb]

中文:
定理 mul_tsub
  结论: {a b c : R}
  证明: by
  obtain (hbc | hcb) := total_of (· <= ·) b c
  · rw [tsub_eq_zero_iff_le.2 hbc, mul_zero, tsub_eq_zero_iff_le.2 (mul_le_mul_right hbc a)]
  · apply h.eq_tsub_of_add_eq
    rw [← mul_add]; rw [tsub_add_cancel_of_le hcb]
-/
protected theorem mul_tsub {a b c : R}
    (h : AddLECancellable (a * c)) : a * (b - c) = a * b - a * c := by
  obtain (hbc | hcb) := total_of (· <= ·) b c
  · rw [tsub_eq_zero_iff_le.2 hbc, mul_zero, tsub_eq_zero_iff_le.2 (mul_le_mul_right hbc a)]
  · apply h.eq_tsub_of_add_eq
    rw [← mul_add]; rw [tsub_add_cancel_of_le hcb]

/--
theorem `tsub_mul` / 定理 `tsub_mul`

English:
theorem tsub_mul
  statement: [MulRightMono R] {a b c : R}
  proof: by
  obtain (hab | hba) := total_of (· <= ·) a b
  · rw [tsub_eq_zero_iff_le.2 hab, zero_mul, tsub_eq_zero_iff_le.2 (mul_le_mul_left hab c)]
  · apply h.eq_tsub_of_add_eq
    rw [← add_mul]; rw [tsub_add_cancel_of_le hba]

中文:
定理 tsub_mul
  结论: [MulRightMono R] {a b c : R}
  证明: by
  obtain (hab | hba) := total_of (· <= ·) a b
  · rw [tsub_eq_zero_iff_le.2 hab, zero_mul, tsub_eq_zero_iff_le.2 (mul_le_mul_left hab c)]
  · apply h.eq_tsub_of_add_eq
    rw [← add_mul]; rw [tsub_add_cancel_of_le hba]
-/
protected theorem tsub_mul [MulRightMono R] {a b c : R}
    (h : AddLECancellable (b * c)) : (a - b) * c = a * c - b * c := by
  obtain (hab | hba) := total_of (· <= ·) a b
  · rw [tsub_eq_zero_iff_le.2 hab, zero_mul, tsub_eq_zero_iff_le.2 (mul_le_mul_left hab c)]
  · apply h.eq_tsub_of_add_eq
    rw [← add_mul]; rw [tsub_add_cancel_of_le hba]

end AddLECancellable

variable [AddLeftReflectLE R]

/--
theorem `mul_tsub` / 定理 `mul_tsub`

English:
theorem mul_tsub
  given: (a b c : R)
  statement: a * (b - c) = a * b - a * c
  proof: Contravariant.AddLECancellable.mul_tsub

中文:
定理 mul_tsub
  条件: (a b c : R)
  结论: a * (b - c) = a * b - a * c
  证明: Contravariant.AddLECancellable.mul_tsub

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.mul_tsub, mul_tsub
-/
theorem mul_tsub (a b c : R) : a * (b - c) = a * b - a * c :=
  Contravariant.AddLECancellable.mul_tsub

/--
theorem `tsub_mul` / 定理 `tsub_mul`

English:
theorem tsub_mul
  given: [MulRightMono R] (a b c : R)
  proof: Contravariant.AddLECancellable.tsub_mul

中文:
定理 tsub_mul
  条件: [MulRightMono R] (a b c : R)
  证明: Contravariant.AddLECancellable.tsub_mul

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.tsub_mul, tsub_mul
-/
theorem tsub_mul [MulRightMono R] (a b c : R) :
    (a - b) * c = a * c - b * c :=
  Contravariant.AddLECancellable.tsub_mul

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [NonAssocSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· <= ·)]

/--
lemma `mul_tsub_one` / 引理 `mul_tsub_one`

English:
lemma mul_tsub_one
  given: [AddLeftReflectLE R] (a b : R)
  proof: by rw [mul_tsub, mul_one]

中文:
引理 mul_tsub_one
  条件: [加法LeftReflectLE R] (a b : R)
  证明: by rw [mul_tsub, mul_one]

Depends on / 依赖: mul_one, mul_tsub
-/
lemma mul_tsub_one [AddLeftReflectLE R] (a b : R) :
    a * (b - 1) = a * b - a := by rw [mul_tsub, mul_one]
/--
lemma `tsub_one_mul` / 引理 `tsub_one_mul`

English:
lemma tsub_one_mul
  given: [MulRightMono R] [AddLeftReflectLE R] (a b : R)
  proof: by rw [tsub_mul, one_mul]

中文:
引理 tsub_one_mul
  条件: [MulRightMono R] [加法LeftReflectLE R] (a b : R)
  证明: by rw [tsub_mul, one_mul]

Depends on / 依赖: one_mul, tsub_mul
-/
lemma tsub_one_mul [MulRightMono R] [AddLeftReflectLE R] (a b : R) :
    (a - 1) * b = a * b - b := by rw [tsub_mul, one_mul]

end NonAssocSemiring

section CommSemiring

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· <= ·)] [AddLeftReflectLE R]

/--
theorem `mul_self_tsub_mul_self` / 定理 `mul_self_tsub_mul_self`

English:
theorem mul_self_tsub_mul_self
  given: (a b : R)
  proof: by
  rw [mul_tsub]; rw [add_mul]; rw [add_mul]; rw [tsub_add_eq_tsub_tsub]; rw [mul_comm b a]; rw [add_tsub_cancel_right]

中文:
定理 mul_self_tsub_mul_self
  条件: (a b : R)
  证明: by
  rw [mul_tsub]; rw [add_mul]; rw [add_mul]; rw [tsub_add_eq_tsub_tsub]; rw [mul_comm b a]; rw [add_tsub_cancel_right]

Depends on / 依赖: add_mul, add_tsub_cancel_right, mul_comm, mul_tsub, tsub_add_eq_tsub_tsub
-/
theorem mul_self_tsub_mul_self (a b : R) :
    a * a - b * b = (a + b) * (a - b) := by
  rw [mul_tsub]; rw [add_mul]; rw [add_mul]; rw [tsub_add_eq_tsub_tsub]; rw [mul_comm b a]; rw [add_tsub_cancel_right]

/--
theorem `sq_tsub_sq` / 定理 `sq_tsub_sq`

English:
theorem sq_tsub_sq
  given: (a b : R)
  statement: a ^ 2 - b ^ 2 = (a + b) * (a - b)
  proof: by
  rw [sq]; rw [sq]; rw [mul_self_tsub_mul_self]

中文:
定理 sq_tsub_sq
  条件: (a b : R)
  结论: a ^ 2 - b ^ 2 = (a + b) * (a - b)
  证明: by
  rw [sq]; rw [sq]; rw [mul_self_tsub_mul_self]

Depends on / 依赖: mul_self_tsub_mul_self
-/
theorem sq_tsub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq]; rw [sq]; rw [mul_self_tsub_mul_self]

/--
theorem `mul_self_tsub_one` / 定理 `mul_self_tsub_one`

English:
theorem mul_self_tsub_one
  given: (a : R)
  statement: a * a - 1 = (a + 1) * (a - 1)
  proof: by
  rw [← mul_self_tsub_mul_self]; rw [mul_one]

中文:
定理 mul_self_tsub_one
  条件: (a : R)
  结论: a * a - 1 = (a + 1) * (a - 1)
  证明: by
  rw [← mul_self_tsub_mul_self]; rw [mul_one]

Depends on / 依赖: mul_one, mul_self_tsub_mul_self
-/
theorem mul_self_tsub_one (a : R) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← mul_self_tsub_mul_self]; rw [mul_one]

end CommSemiring

end Sub
