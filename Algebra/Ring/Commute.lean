/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.Ring.Semiconj
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Data.Bracket

/-!
# Semirings and rings

This file gives lemmas about semirings, rings and domains.
This is analogous to `Mathlib/Algebra/Group/Basic.lean`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `Mathlib/Algebra/Ring/Defs.lean`.

-/

@[expose] public section


universe u

variable {R : Type u}

open Function

namespace Commute

@[simp]
/--
theorem `add_right` / 定理 `add_right`

English:
theorem add_right
  given: [Distrib R] {a b c : R}
  statement: Commute a b -> Commute a c -> Commute a (b + c)
  proof: SemiconjBy.add_right

中文:
定理 add_right
  条件: [Distrib R] {a b c : R}
  结论: Commute a b -> Commute a c -> Commute a (b + c)
  证明: SemiconjBy.add_right

Depends on / 依赖: SemiconjBy, SemiconjBy.add_right, add_right
-/
theorem add_right [Distrib R] {a b c : R} : Commute a b -> Commute a c -> Commute a (b + c) :=
  SemiconjBy.add_right
-- for some reason mathport expected `Semiring` instead of `Distrib`?

@[simp]
/--
theorem `add_left` / 定理 `add_left`

English:
theorem add_left
  given: [Distrib R] {a b c : R}
  statement: Commute a c -> Commute b c -> Commute (a + b) c
  proof: SemiconjBy.add_left

中文:
定理 add_left
  条件: [Distrib R] {a b c : R}
  结论: Commute a c -> Commute b c -> Commute (a + b) c
  证明: SemiconjBy.add_left

Depends on / 依赖: SemiconjBy, SemiconjBy.add_left, add_left
-/
theorem add_left [Distrib R] {a b c : R} : Commute a c -> Commute b c -> Commute (a + b) c :=
  SemiconjBy.add_left
-- for some reason mathport expected `Semiring` instead of `Distrib`?

/--
theorem `mul_self_sub_mul_self_eq` / 定理 `mul_self_sub_mul_self_eq`

English:
theorem mul_self_sub_mul_self_eq
  given: [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b)
  proof: by
  rw [add_mul]; rw [mul_sub]; rw [mul_sub]; rw [h.eq]; rw [sub_add_sub_cancel]

中文:
定理 mul_self_sub_mul_self_eq
  条件: [非幺非结合环 R] {a b : R} (h : Commute a b)
  证明: by
  rw [add_mul]; rw [mul_sub]; rw [mul_sub]; rw [h.eq]; rw [sub_add_sub_cancel]

Depends on / 依赖: add_mul, h.eq, mul_sub, sub_add_sub_cancel
-/
theorem mul_self_sub_mul_self_eq [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a + b) * (a - b) := by
  rw [add_mul]; rw [mul_sub]; rw [mul_sub]; rw [h.eq]; rw [sub_add_sub_cancel]

/--
theorem `mul_self_sub_mul_self_eq'` / 定理 `mul_self_sub_mul_self_eq'`

English:
theorem mul_self_sub_mul_self_eq'
  given: [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b)
  proof: by
  rw [mul_add]; rw [sub_mul]; rw [sub_mul]; rw [h.eq]; rw [sub_add_sub_cancel]

中文:
定理 mul_self_sub_mul_self_eq'
  条件: [非幺非结合环 R] {a b : R} (h : Commute a b)
  证明: by
  rw [mul_add]; rw [sub_mul]; rw [sub_mul]; rw [h.eq]; rw [sub_add_sub_cancel]

Depends on / 依赖: h.eq, mul_add, sub_add_sub_cancel, sub_mul
-/
theorem mul_self_sub_mul_self_eq' [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a - b) * (a + b) := by
  rw [mul_add]; rw [sub_mul]; rw [sub_mul]; rw [h.eq]; rw [sub_add_sub_cancel]

/--
theorem `mul_self_eq_mul_self_iff` / 定理 `mul_self_eq_mul_self_iff`

English:
theorem mul_self_eq_mul_self_iff
  statement: [NonUnitalNonAssocRing R] [NoZeroDivisors R] {a b : R}
  proof: by
  rw [← sub_eq_zero]; rw [h.mul_self_sub_mul_self_eq]; rw [mul_eq_zero]; rw [or_comm]; rw [sub_eq_zero]; rw [add_eq_zero_iff_eq_neg]

中文:
定理 mul_self_eq_mul_self_iff
  结论: [非幺非结合环 R] [无零因子 R] {a b : R}
  证明: by
  rw [← sub_eq_zero]; rw [h.mul_self_sub_mul_self_eq]; rw [mul_eq_zero]; rw [or_comm]; rw [sub_eq_zero]; rw [add_eq_zero_iff_eq_neg]

Depends on / 依赖: add_eq_zero_iff_eq_neg, h.mul_self_sub_mul_self_eq, mul_eq_zero, mul_self_sub_mul_self_eq, or_comm, sub_eq_zero
-/
theorem mul_self_eq_mul_self_iff [NonUnitalNonAssocRing R] [NoZeroDivisors R] {a b : R}
    (h : Commute a b) : a * a = b * b ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero]; rw [h.mul_self_sub_mul_self_eq]; rw [mul_eq_zero]; rw [or_comm]; rw [sub_eq_zero]; rw [add_eq_zero_iff_eq_neg]

section

variable [Mul R] [HasDistribNeg R] {a b : R}

/--
theorem `neg_right` / 定理 `neg_right`

English:
theorem neg_right
  statement: Commute a b -> Commute a (-b)
  proof: SemiconjBy.neg_right

@[simp]

中文:
定理 neg_right
  结论: Commute a b -> Commute a (-b)
  证明: SemiconjBy.neg_right

@[simp]

Depends on / 依赖: SemiconjBy, SemiconjBy.neg_right, neg_right
-/
theorem neg_right : Commute a b -> Commute a (-b) :=
  SemiconjBy.neg_right

@[simp]
/--
theorem `neg_right_iff` / 定理 `neg_right_iff`

English:
theorem neg_right_iff
  statement: Commute a (-b) ↔ Commute a b
  proof: SemiconjBy.neg_right_iff

中文:
定理 neg_right_iff
  结论: Commute a (-b) ↔ Commute a b
  证明: SemiconjBy.neg_right_iff

Depends on / 依赖: AlgebraicGeometry, AlgebraicGeometry.isAffine_affineScheme, Scheme, Scheme.Spec.obj_mem_essImage, SemiconjBy, SemiconjBy.neg_right_iff, isAffine_affineScheme, neg_right_iff, obj_mem_essImage
-/
theorem neg_right_iff : Commute a (-b) ↔ Commute a b :=
  SemiconjBy.neg_right_iff

/--
theorem `neg_left` / 定理 `neg_left`

English:
theorem neg_left
  statement: Commute a b -> Commute (-a) b
  proof: SemiconjBy.neg_left

@[simp]

中文:
定理 neg_left
  结论: Commute a b -> Commute (-a) b
  证明: SemiconjBy.neg_left

@[simp]

Depends on / 依赖: SemiconjBy, SemiconjBy.neg_left, neg_left
-/
theorem neg_left : Commute a b -> Commute (-a) b :=
  SemiconjBy.neg_left

@[simp]
/--
theorem `neg_left_iff` / 定理 `neg_left_iff`

English:
theorem neg_left_iff
  statement: Commute (-a) b ↔ Commute a b
  proof: SemiconjBy.neg_left_iff

中文:
定理 neg_left_iff
  结论: Commute (-a) b ↔ Commute a b
  证明: SemiconjBy.neg_left_iff

Depends on / 依赖: SemiconjBy, SemiconjBy.neg_left_iff, neg_left_iff
-/
theorem neg_left_iff : Commute (-a) b ↔ Commute a b :=
  SemiconjBy.neg_left_iff

end

section

variable [MulOneClass R] [HasDistribNeg R]

/--
theorem `neg_one_right` / 定理 `neg_one_right`

English:
theorem neg_one_right
  given: (a : R)
  statement: Commute a (-1)
  proof: SemiconjBy.neg_one_right a

中文:
定理 neg_one_right
  条件: (a : R)
  结论: Commute a (-1)
  证明: SemiconjBy.neg_one_right a

Depends on / 依赖: SemiconjBy, SemiconjBy.neg_one_right, neg_one_right
-/
theorem neg_one_right (a : R) : Commute a (-1) :=
  SemiconjBy.neg_one_right a

/--
theorem `neg_one_left` / 定理 `neg_one_left`

English:
theorem neg_one_left
  given: (a : R)
  statement: Commute (-1) a
  proof: SemiconjBy.neg_one_left a

中文:
定理 neg_one_left
  条件: (a : R)
  结论: Commute (-1) a
  证明: SemiconjBy.neg_one_left a

Depends on / 依赖: SemiconjBy, SemiconjBy.neg_one_left, neg_one_left
-/
theorem neg_one_left (a : R) : Commute (-1) a :=
  SemiconjBy.neg_one_left a

end

section

variable [NonUnitalNonAssocRing R] {a b c : R}

@[simp]
/--
theorem `sub_right` / 定理 `sub_right`

English:
theorem sub_right
  statement: Commute a b -> Commute a c -> Commute a (b - c)
  proof: SemiconjBy.sub_right

@[simp]

中文:
定理 sub_right
  结论: Commute a b -> Commute a c -> Commute a (b - c)
  证明: SemiconjBy.sub_right

@[simp]

Depends on / 依赖: SemiconjBy, SemiconjBy.sub_right, sub_right
-/
theorem sub_right : Commute a b -> Commute a c -> Commute a (b - c) :=
  SemiconjBy.sub_right

@[simp]
/--
theorem `sub_left` / 定理 `sub_left`

English:
theorem sub_left
  statement: Commute a c -> Commute b c -> Commute (a - b) c
  proof: SemiconjBy.sub_left

中文:
定理 sub_left
  结论: Commute a c -> Commute b c -> Commute (a - b) c
  证明: SemiconjBy.sub_left

Depends on / 依赖: SemiconjBy, SemiconjBy.sub_left, sub_left
-/
theorem sub_left : Commute a c -> Commute b c -> Commute (a - b) c :=
  SemiconjBy.sub_left

end

section Semiring

variable [Semiring R]

/--
lemma `add_sq` / 引理 `add_sq`

English:
lemma add_sq
  given: {a b : R} (h : Commute a b)
  proof: by
  simp [sq, add_mul, mul_add, two_mul, h.eq, add_assoc]

中文:
引理 add_sq
  条件: {a b : R} (h : Commute a b)
  证明: by
  simp [sq, add_mul, mul_add, two_mul, h.eq, add_assoc]
-/
protected lemma add_sq {a b : R} (h : Commute a b) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  simp [sq, add_mul, mul_add, two_mul, h.eq, add_assoc]

end Semiring

section Ring
variable [Ring R] {a b : R}

/--
lemma `sq_sub_sq` / 引理 `sq_sub_sq`

English:
lemma sq_sub_sq
  given: (h : Commute a b)
  statement: a ^ 2 - b ^ 2 = (a + b) * (a - b)
  proof: by
  rw [sq]; rw [sq]; rw [h.mul_self_sub_mul_self_eq]

中文:
引理 sq_sub_sq
  条件: (h : Commute a b)
  结论: a ^ 2 - b ^ 2 = (a + b) * (a - b)
  证明: by
  rw [sq]; rw [sq]; rw [h.mul_self_sub_mul_self_eq]

Depends on / 依赖: IsAffine
-/
protected lemma sq_sub_sq (h : Commute a b) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq]; rw [sq]; rw [h.mul_self_sub_mul_self_eq]

/--
lemma `sub_sq` / 引理 `sub_sq`

English:
lemma sub_sq
  given: {a b : R} (h : Commute a b)
  proof: by
  simp [sq, add_mul, sub_mul, mul_sub, two_mul, h.eq, ← sub_add, ← sub_sub]

中文:
引理 sub_sq
  条件: {a b : R} (h : Commute a b)
  证明: by
  simp [sq, add_mul, sub_mul, mul_sub, two_mul, h.eq, ← sub_add, ← sub_sub]
-/
protected lemma sub_sq {a b : R} (h : Commute a b) :
    (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  simp [sq, add_mul, sub_mul, mul_sub, two_mul, h.eq, ← sub_add, ← sub_sub]

variable [NoZeroDivisors R]

/--
lemma `sq_eq_sq_iff_eq_or_eq_neg` / 引理 `sq_eq_sq_iff_eq_or_eq_neg`

English:
lemma sq_eq_sq_iff_eq_or_eq_neg
  given: (h : Commute a b)
  statement: a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b
  proof: by
  rw [← sub_eq_zero]; rw [h.sq_sub_sq]; rw [mul_eq_zero]; rw [add_eq_zero_iff_eq_neg]; rw [sub_eq_zero]; rw [or_comm]

中文:
引理 sq_eq_sq_iff_eq_or_eq_neg
  条件: (h : Commute a b)
  结论: a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b
  证明: by
  rw [← sub_eq_zero]; rw [h.sq_sub_sq]; rw [mul_eq_zero]; rw [add_eq_zero_iff_eq_neg]; rw [sub_eq_zero]; rw [or_comm]
-/
protected lemma sq_eq_sq_iff_eq_or_eq_neg (h : Commute a b) : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero]; rw [h.sq_sub_sq]; rw [mul_eq_zero]; rw [add_eq_zero_iff_eq_neg]; rw [sub_eq_zero]; rw [or_comm]

end Ring
end Commute

section HasDistribNeg
variable (R)
variable [Monoid R] [HasDistribNeg R]

/--
lemma `neg_one_pow_eq_or` / 引理 `neg_one_pow_eq_or`

English:
lemma neg_one_pow_eq_or
  statement: forall n : Nat, (-1 : R) ^ n = 1 ∨ (-1 : R) ^ n = -1

中文:
引理 neg_one_pow_eq_or
  结论: 对任意 n : 自然数, (-1 : R) ^ n = 1 ∨ (-1 : R) ^ n = -1
-/
lemma neg_one_pow_eq_or : forall n : Nat, (-1 : R) ^ n = 1 ∨ (-1 : R) ^ n = -1
  | 0 => Or.inl (pow_zero _)
  | n + 1 => (neg_one_pow_eq_or n).symm.imp
    (fun h => by rw [pow_succ, h, neg_one_mul, neg_neg])
    (fun h => by rw [pow_succ, h, one_mul])

variable {R}

/--
lemma `neg_pow` / 引理 `neg_pow`

English:
lemma neg_pow
  given: (a : R) (n : Nat)
  statement: (-a) ^ n = (-1) ^ n * a ^ n
  proof: neg_one_mul a ▸ (Commute.neg_one_left a).mul_pow n

中文:
引理 neg_pow
  条件: (a : R) (n : 自然数)
  结论: (-a) ^ n = (-1) ^ n * a ^ n
  证明: neg_one_mul a ▸ (Commute.neg_one_left a).mul_pow n

Depends on / 依赖: Commute, Commute.neg_one_left, mul_pow, neg_one_left, neg_one_mul
-/
lemma neg_pow (a : R) (n : Nat) : (-a) ^ n = (-1) ^ n * a ^ n :=
  neg_one_mul a ▸ (Commute.neg_one_left a).mul_pow n

/--
lemma `neg_pow'` / 引理 `neg_pow'`

English:
lemma neg_pow'
  given: (a : R) (n : Nat)
  statement: (-a) ^ n = a ^ n * (-1) ^ n
  proof: mul_neg_one a ▸ (Commute.neg_one_right a).mul_pow n

中文:
引理 neg_pow'
  条件: (a : R) (n : 自然数)
  结论: (-a) ^ n = a ^ n * (-1) ^ n
  证明: mul_neg_one a ▸ (Commute.neg_one_right a).mul_pow n

Depends on / 依赖: Commute, Commute.neg_one_right, mul_neg_one, mul_pow, neg_one_right
-/
lemma neg_pow' (a : R) (n : Nat) : (-a) ^ n = a ^ n * (-1) ^ n :=
  mul_neg_one a ▸ (Commute.neg_one_right a).mul_pow n

/--
lemma `neg_sq` / 引理 `neg_sq`

English:
lemma neg_sq
  given: (a : R)
  statement: (-a) ^ 2 = a ^ 2
  proof: by simp [sq]

中文:
引理 neg_sq
  条件: (a : R)
  结论: (-a) ^ 2 = a ^ 2
  证明: by simp [sq]
-/
lemma neg_sq (a : R) : (-a) ^ 2 = a ^ 2 := by simp [sq]

/--
lemma `neg_one_sq` / 引理 `neg_one_sq`

English:
lemma neg_one_sq
  statement: (-1 : R) ^ 2 = 1
  proof: by simp [neg_sq, one_pow]

alias neg_pow_two := neg_sq

alias neg_one_pow_two := neg_one_sq

中文:
引理 neg_one_sq
  结论: (-1 : R) ^ 2 = 1
  证明: by simp [neg_sq, one_pow]

alias neg_pow_two := neg_sq

alias neg_one_pow_two := neg_one_sq

Depends on / 依赖: neg_sq, one_pow
-/
lemma neg_one_sq : (-1 : R) ^ 2 = 1 := by simp [neg_sq, one_pow]

alias neg_pow_two := neg_sq

alias neg_one_pow_two := neg_one_sq

end HasDistribNeg

section Ring
variable [Ring R] {a : R} {n : Nat}

/--
lemma `neg_one_pow_mul_eq_zero_iff` / 引理 `neg_one_pow_mul_eq_zero_iff`

English:
lemma neg_one_pow_mul_eq_zero_iff
  statement: (-1) ^ n * a = 0 ↔ a = 0
  proof: by
  rcases neg_one_pow_eq_or R n with h | h <;> simp [h]

中文:
引理 neg_one_pow_mul_eq_zero_iff
  结论: (-1) ^ n * a = 0 ↔ a = 0
  证明: by
  rcases neg_one_pow_eq_or R n with h | h <;> simp [h]
-/
@[simp] lemma neg_one_pow_mul_eq_zero_iff : (-1) ^ n * a = 0 ↔ a = 0 := by
  rcases neg_one_pow_eq_or R n with h | h <;> simp [h]

/--
lemma `mul_neg_one_pow_eq_zero_iff` / 引理 `mul_neg_one_pow_eq_zero_iff`

English:
lemma mul_neg_one_pow_eq_zero_iff
  statement: a * (-1) ^ n = 0 ↔ a = 0
  proof: by
  obtain h | h := neg_one_pow_eq_or R n <;> simp [h]

中文:
引理 mul_neg_one_pow_eq_zero_iff
  结论: a * (-1) ^ n = 0 ↔ a = 0
  证明: by
  obtain h | h := neg_one_pow_eq_or R n <;> simp [h]
-/
@[simp] lemma mul_neg_one_pow_eq_zero_iff : a * (-1) ^ n = 0 ↔ a = 0 := by
  obtain h | h := neg_one_pow_eq_or R n <;> simp [h]

/--
lemma `neg_one_pow_eq_pow_mod_two` / 引理 `neg_one_pow_eq_pow_mod_two`

English:
lemma neg_one_pow_eq_pow_mod_two
  given: (n : Nat)
  statement: (-1 : R) ^ n = (-1) ^ (n % 2)
  proof: by
  rw [← Nat.mod_add_div n 2]; rw [pow_add]; rw [pow_mul]; simp [sq]

中文:
引理 neg_one_pow_eq_pow_mod_two
  条件: (n : 自然数)
  结论: (-1 : R) ^ n = (-1) ^ (n % 2)
  证明: by
  rw [← Nat.mod_add_div n 2]; rw [pow_add]; rw [pow_mul]; simp [sq]

Depends on / 依赖: Nat.mod_add_div, mod_add_div, pow_add, pow_mul
-/
lemma neg_one_pow_eq_pow_mod_two (n : Nat) : (-1 : R) ^ n = (-1) ^ (n % 2) := by
  rw [← Nat.mod_add_div n 2]; rw [pow_add]; rw [pow_mul]; simp [sq]

variable [NoZeroDivisors R]

/--
lemma `sq_eq_one_iff` / 引理 `sq_eq_one_iff`

English:
lemma sq_eq_one_iff
  statement: a ^ 2 = 1 ↔ a = 1 ∨ a = -1
  proof: by
  rw [← (Commute.one_right a).sq_eq_sq_iff_eq_or_eq_neg]; rw [one_pow]

中文:
引理 sq_eq_one_iff
  结论: a ^ 2 = 1 ↔ a = 1 ∨ a = -1
  证明: by
  rw [← (Commute.one_right a).sq_eq_sq_iff_eq_or_eq_neg]; rw [one_pow]
-/
@[simp] lemma sq_eq_one_iff : a ^ 2 = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← (Commute.one_right a).sq_eq_sq_iff_eq_or_eq_neg]; rw [one_pow]

/--
lemma `sq_ne_one_iff` / 引理 `sq_ne_one_iff`

English:
lemma sq_ne_one_iff
  statement: a ^ 2 != 1 ↔ a != 1 ∧ a != -1
  proof: sq_eq_one_iff.not.trans not_or

中文:
引理 sq_ne_one_iff
  结论: a ^ 2 != 1 ↔ a != 1 ∧ a != -1
  证明: sq_eq_one_iff.not.trans not_or

Depends on / 依赖: not_or, sq_eq_one_iff, sq_eq_one_iff.not.trans
-/
lemma sq_ne_one_iff : a ^ 2 != 1 ↔ a != 1 ∧ a != -1 := sq_eq_one_iff.not.trans not_or

end Ring

/--
theorem `mul_self_sub_mul_self` / 定理 `mul_self_sub_mul_self`

English:
theorem mul_self_sub_mul_self
  given: [NonUnitalNonAssocCommRing R] (a b : R)
  proof: (Commute.all a b).mul_self_sub_mul_self_eq

中文:
定理 mul_self_sub_mul_self
  条件: [非幺非结合交换环 R] (a b : R)
  证明: (Commute.all a b).mul_self_sub_mul_self_eq

Depends on / 依赖: Commute, Commute.all, mul_self_sub_mul_self_eq
-/
theorem mul_self_sub_mul_self [NonUnitalNonAssocCommRing R] (a b : R) :
    a * a - b * b = (a + b) * (a - b) :=
  (Commute.all a b).mul_self_sub_mul_self_eq

/--
theorem `mul_self_sub_one` / 定理 `mul_self_sub_one`

English:
theorem mul_self_sub_one
  given: [NonAssocRing R] (a : R)
  statement: a * a - 1 = (a + 1) * (a - 1)
  proof: by
  rw [← (Commute.one_right a).mul_self_sub_mul_self_eq]; rw [mul_one]

中文:
定理 mul_self_sub_one
  条件: [非结合环 R] (a : R)
  结论: a * a - 1 = (a + 1) * (a - 1)
  证明: by
  rw [← (Commute.one_right a).mul_self_sub_mul_self_eq]; rw [mul_one]

Depends on / 依赖: Commute, Commute.one_right, mul_one, mul_self_sub_mul_self_eq, one_right
-/
theorem mul_self_sub_one [NonAssocRing R] (a : R) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← (Commute.one_right a).mul_self_sub_mul_self_eq]; rw [mul_one]

/--
theorem `mul_self_eq_mul_self_iff` / 定理 `mul_self_eq_mul_self_iff`

English:
theorem mul_self_eq_mul_self_iff
  given: [NonUnitalNonAssocCommRing R] [NoZeroDivisors R] {a b : R}
  proof: (Commute.all a b).mul_self_eq_mul_self_iff

中文:
定理 mul_self_eq_mul_self_iff
  条件: [非幺非结合交换环 R] [无零因子 R] {a b : R}
  证明: (Commute.all a b).mul_self_eq_mul_self_iff

Depends on / 依赖: Commute, Commute.all, mul_self_eq_mul_self_iff
-/
theorem mul_self_eq_mul_self_iff [NonUnitalNonAssocCommRing R] [NoZeroDivisors R] {a b : R} :
    a * a = b * b ↔ a = b ∨ a = -b :=
  (Commute.all a b).mul_self_eq_mul_self_iff

/--
theorem `mul_self_eq_one_iff` / 定理 `mul_self_eq_one_iff`

English:
theorem mul_self_eq_one_iff
  given: [NonAssocRing R] [NoZeroDivisors R] {a : R}
  proof: by
  rw [← (Commute.one_right a).mul_self_eq_mul_self_iff]; rw [mul_one]

中文:
定理 mul_self_eq_one_iff
  条件: [非结合环 R] [无零因子 R] {a : R}
  证明: by
  rw [← (Commute.one_right a).mul_self_eq_mul_self_iff]; rw [mul_one]

Depends on / 依赖: Commute, Commute.one_right, mul_one, mul_self_eq_mul_self_iff, one_right
-/
theorem mul_self_eq_one_iff [NonAssocRing R] [NoZeroDivisors R] {a : R} :
    a * a = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← (Commute.one_right a).mul_self_eq_mul_self_iff]; rw [mul_one]

section CommRing
variable [CommRing R]

/--
lemma `sq_sub_sq` / 引理 `sq_sub_sq`

English:
lemma sq_sub_sq
  given: (a b : R)
  statement: a ^ 2 - b ^ 2 = (a + b) * (a - b)
  proof: (Commute.all a b).sq_sub_sq

alias pow_two_sub_pow_two := sq_sub_sq

中文:
引理 sq_sub_sq
  条件: (a b : R)
  结论: a ^ 2 - b ^ 2 = (a + b) * (a - b)
  证明: (Commute.all a b).sq_sub_sq

alias pow_two_sub_pow_two := sq_sub_sq

Depends on / 依赖: Commute, Commute.all, sq_sub_sq
-/
lemma sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := (Commute.all a b).sq_sub_sq

alias pow_two_sub_pow_two := sq_sub_sq

/--
lemma `sub_sq` / 引理 `sub_sq`

English:
lemma sub_sq
  given: (a b : R)
  statement: (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2
  proof: by
  rw [sub_eq_add_neg]; rw [add_sq]; rw [neg_sq]; rw [mul_neg]; rw [← sub_eq_add_neg]

alias sub_pow_two := sub_sq

中文:
引理 sub_sq
  条件: (a b : R)
  结论: (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2
  证明: by
  rw [sub_eq_add_neg]; rw [add_sq]; rw [neg_sq]; rw [mul_neg]; rw [← sub_eq_add_neg]

alias sub_pow_two := sub_sq

Depends on / 依赖: add_sq, mul_neg, neg_sq, sub_eq_add_neg
-/
lemma sub_sq (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  rw [sub_eq_add_neg]; rw [add_sq]; rw [neg_sq]; rw [mul_neg]; rw [← sub_eq_add_neg]

alias sub_pow_two := sub_sq

/--
lemma `sub_sq'` / 引理 `sub_sq'`

English:
lemma sub_sq'
  given: (a b : R)
  statement: (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b
  proof: by
  rw [sub_eq_add_neg]; rw [add_sq']; rw [neg_sq]; rw [mul_neg]; rw [← sub_eq_add_neg]

中文:
引理 sub_sq'
  条件: (a b : R)
  结论: (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b
  证明: by
  rw [sub_eq_add_neg]; rw [add_sq']; rw [neg_sq]; rw [mul_neg]; rw [← sub_eq_add_neg]

Depends on / 依赖: add_sq, mul_neg, neg_sq, sub_eq_add_neg
-/
lemma sub_sq' (a b : R) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b := by
  rw [sub_eq_add_neg]; rw [add_sq']; rw [neg_sq]; rw [mul_neg]; rw [← sub_eq_add_neg]

/--
lemma `sub_sq_comm` / 引理 `sub_sq_comm`

English:
lemma sub_sq_comm
  given: (a b : R)
  statement: (a - b) ^ 2 = (b - a) ^ 2
  proof: by
  rw [sub_sq']; rw [mul_right_comm]; rw [add_comm]; rw [sub_sq']

中文:
引理 sub_sq_comm
  条件: (a b : R)
  结论: (a - b) ^ 2 = (b - a) ^ 2
  证明: by
  rw [sub_sq']; rw [mul_right_comm]; rw [add_comm]; rw [sub_sq']

Depends on / 依赖: add_comm, mul_right_comm, sub_sq
-/
lemma sub_sq_comm (a b : R) : (a - b) ^ 2 = (b - a) ^ 2 := by
  rw [sub_sq']; rw [mul_right_comm]; rw [add_comm]; rw [sub_sq']

variable [NoZeroDivisors R] {a b : R}

/--
lemma `sq_eq_sq_iff_eq_or_eq_neg` / 引理 `sq_eq_sq_iff_eq_or_eq_neg`

English:
lemma sq_eq_sq_iff_eq_or_eq_neg
  statement: a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b
  proof: (Commute.all a b).sq_eq_sq_iff_eq_or_eq_neg

中文:
引理 sq_eq_sq_iff_eq_or_eq_neg
  结论: a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b
  证明: (Commute.all a b).sq_eq_sq_iff_eq_or_eq_neg

Depends on / 依赖: Commute, Commute.all, sq_eq_sq_iff_eq_or_eq_neg
-/
lemma sq_eq_sq_iff_eq_or_eq_neg : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b :=
  (Commute.all a b).sq_eq_sq_iff_eq_or_eq_neg

/--
lemma `eq_or_eq_neg_of_sq_eq_sq` / 引理 `eq_or_eq_neg_of_sq_eq_sq`

English:
lemma eq_or_eq_neg_of_sq_eq_sq
  given: (a b : R)
  statement: a ^ 2 = b ^ 2 -> a = b ∨ a = -b
  proof: sq_eq_sq_iff_eq_or_eq_neg.1

中文:
引理 eq_or_eq_neg_of_sq_eq_sq
  条件: (a b : R)
  结论: a ^ 2 = b ^ 2 -> a = b ∨ a = -b
  证明: sq_eq_sq_iff_eq_or_eq_neg.1

Depends on / 依赖: U.property, property, sq_eq_sq_iff_eq_or_eq_neg
-/
lemma eq_or_eq_neg_of_sq_eq_sq (a b : R) : a ^ 2 = b ^ 2 -> a = b ∨ a = -b :=
  sq_eq_sq_iff_eq_or_eq_neg.1

-- Copies of the above CommRing lemmas for `Units R`.
namespace Units

/--
lemma `sq_eq_sq_iff_eq_or_eq_neg` / 引理 `sq_eq_sq_iff_eq_or_eq_neg`

English:
lemma sq_eq_sq_iff_eq_or_eq_neg
  given: {a b : Rˣ}
  statement: a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b
  proof: by
  simp_rw [Units.ext_iff, val_pow_eq_pow_val, sq_eq_sq_iff_eq_or_eq_neg, Units.val_neg]

中文:
引理 sq_eq_sq_iff_eq_or_eq_neg
  条件: {a b : Rˣ}
  结论: a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b
  证明: by
  simp_rw [Units.ext_iff, val_pow_eq_pow_val, sq_eq_sq_iff_eq_or_eq_neg, Units.val_neg]
-/
protected lemma sq_eq_sq_iff_eq_or_eq_neg {a b : Rˣ} : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  simp_rw [Units.ext_iff, val_pow_eq_pow_val, sq_eq_sq_iff_eq_or_eq_neg, Units.val_neg]

/--
lemma `eq_or_eq_neg_of_sq_eq_sq` / 引理 `eq_or_eq_neg_of_sq_eq_sq`

English:
lemma eq_or_eq_neg_of_sq_eq_sq
  given: (a b : Rˣ) (h : a ^ 2 = b ^ 2)
  statement: a = b ∨ a = -b
  proof: Units.sq_eq_sq_iff_eq_or_eq_neg.1 h

中文:
引理 eq_or_eq_neg_of_sq_eq_sq
  条件: (a b : Rˣ) (h : a ^ 2 = b ^ 2)
  结论: a = b ∨ a = -b
  证明: Units.sq_eq_sq_iff_eq_or_eq_neg.1 h
-/
protected lemma eq_or_eq_neg_of_sq_eq_sq (a b : Rˣ) (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b :=
  Units.sq_eq_sq_iff_eq_or_eq_neg.1 h

end Units
end CommRing

namespace Units

/--
theorem `inv_eq_self_iff` / 定理 `inv_eq_self_iff`

English:
theorem inv_eq_self_iff
  given: [Ring R] [NoZeroDivisors R] (u : Rˣ)
  statement: u⁻¹ = u ↔ u = 1 ∨ u = -1
  proof: by
  rw [inv_eq_iff_mul_eq_one]
  simp only [Units.ext_iff]
  push_cast
  exact mul_self_eq_one_iff

中文:
定理 inv_eq_self_iff
  条件: [环 R] [无零因子 R] (u : Rˣ)
  结论: u⁻¹ = u ↔ u = 1 ∨ u = -1
  证明: by
  rw [inv_eq_iff_mul_eq_one]
  simp only [Units.ext_iff]
  push_cast
  exact mul_self_eq_one_iff

Depends on / 依赖: Units.ext_iff, ext_iff, inv_eq_iff_mul_eq_one, mul_self_eq_one_iff
-/
theorem inv_eq_self_iff [Ring R] [NoZeroDivisors R] (u : Rˣ) : u⁻¹ = u ↔ u = 1 ∨ u = -1 := by
  rw [inv_eq_iff_mul_eq_one]
  simp only [Units.ext_iff]
  push_cast
  exact mul_self_eq_one_iff

end Units

section Bracket

variable [NonUnitalNonAssocRing R]

namespace Ring

instance (priority := 100) instBracket : Bracket R R := ⟨fun x y => x * y - y * x⟩

/--
theorem `lie_def` / 定理 `lie_def`

English:
theorem lie_def
  given: (x y : R)
  statement: ⁅x, y⁆ = x * y - y * x
  proof: rfl

中文:
定理 lie_def
  条件: (x y : R)
  结论: ⁅x, y⁆ = x * y - y * x
  证明: rfl
-/
theorem lie_def (x y : R) : ⁅x, y⁆ = x * y - y * x := rfl

end Ring

/--
theorem `commute_iff_lie_eq` / 定理 `commute_iff_lie_eq`

English:
theorem commute_iff_lie_eq
  given: {x y : R}
  statement: Commute x y ↔ ⁅x, y⁆ = 0
  proof: sub_eq_zero.symm

中文:
定理 commute_iff_lie_eq
  条件: {x y : R}
  结论: Commute x y ↔ ⁅x, y⁆ = 0
  证明: sub_eq_zero.symm

Depends on / 依赖: sub_eq_zero, sub_eq_zero.symm
-/
theorem commute_iff_lie_eq {x y : R} : Commute x y ↔ ⁅x, y⁆ = 0 := sub_eq_zero.symm

/--
theorem `Commute.lie_eq` / 定理 `Commute.lie_eq`

English:
theorem Commute.lie_eq
  given: {x y : R} (h : Commute x y)
  statement: ⁅x, y⁆ = 0
  proof: sub_eq_zero_of_eq h

中文:
定理 Commute.lie_eq
  条件: {x y : R} (h : Commute x y)
  结论: ⁅x, y⁆ = 0
  证明: sub_eq_zero_of_eq h

Depends on / 依赖: sub_eq_zero_of_eq
-/
theorem Commute.lie_eq {x y : R} (h : Commute x y) : ⁅x, y⁆ = 0 := sub_eq_zero_of_eq h

end Bracket
