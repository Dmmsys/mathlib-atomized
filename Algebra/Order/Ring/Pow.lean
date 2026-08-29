/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Nat.Cast.Commute
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Tactic.Abel

/-! # Bernoulli's inequality

In this file we prove several versions of Bernoulli's inequality.
Besides the standard version `1 + n * a ≤ (1 + a) ^ n`,
we also prove `a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n`,
which can be regarded as Bernoulli's inequality for `b / a` multiplied by `a ^ n`.

Also, we prove versions for different typeclass assumptions on the (semi)ring.
-/

public section

variable {R : Type*}

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {a b : R}

/--
lemma `Commute.pow_add_mul_le_add_pow_of_sq_nonneg` / 引理 `Commute.pow_add_mul_le_add_pow_of_sq_nonneg`

English:
lemma Commute.pow_add_mul_le_add_pow_of_sq_nonneg
  statement: (Hcomm : Commute a b) (ha : 0 <= a)
  proof: le_add_of_nonneg_right Hsq
      _ = (a + b) ^ 2 := by simp [sq, add_mul, mul_add, two_mul, Hcomm.eq, add_assoc]
  | n + 3 => by
    calc
      _ <= a ^ (n + 3) + ↑(n + 3) * a ^ (n + 2) * b +
            ((n + 1) * (b ^ 2 * (2 * a + b) * a ^ n) + a ^ (n + 1) * b ^ 2) :=
le_add_of_nonneg_right by
   

中文:
引理 Commute.pow_add_mul_le_add_pow_of_sq_nonneg
  结论: (Hcomm : Commute a b) (ha : 0 <= a)
  证明: le_add_of_nonneg_right Hsq
      _ = (a + b) ^ 2 := by simp [sq, add_mul, mul_add, two_mul, Hcomm.eq, add_assoc]
  | n + 3 => by
    calc
      _ <= a ^ (n + 3) + ↑(n + 3) * a ^ (n + 2) * b +
            ((n + 1) * (b ^ 2 * (2 * a + b) * a ^ n) + a ^ (n + 1) * b ^ 2) :=
le_add_of_nonneg_right by
   

Depends on / 依赖: Hcomm.eq, Nat.cast_add, Nat.cast_nonneg, Nat.cast_ofNat, Nat.cast_one, add_assoc, add_mul, add_nonneg, apply_rules, cast_add, cast_nonneg, cast_ofNat, cast_one, le_add_of_nonneg_right, mul_add, mul_nonneg, pow_nonneg, pow_succ, two_mul, zero_le_one
-/
lemma Commute.pow_add_mul_le_add_pow_of_sq_nonneg (Hcomm : Commute a b) (ha : 0 <= a)
    (Hsq : 0 <= b ^ 2) (Hsq' : 0 <= (a + b) ^ 2) (H : 0 <= 2 * a + b) :
    forall n : Nat, a ^ n + n * a ^ (n - 1) * b <= (a + b) ^ n
  | 0 => by simp
  | 1 => by simp
  | 2 =>
    calc
      a ^ 2 + (2 : Nat) * a ^ 1 * b <= a ^ 2 + (2 : Nat) * a ^ 1 * b + b ^ 2 :=
        le_add_of_nonneg_right Hsq
      _ = (a + b) ^ 2 := by simp [sq, add_mul, mul_add, two_mul, Hcomm.eq, add_assoc]
  | n + 3 => by
    calc
      _ <= a ^ (n + 3) + ↑(n + 3) * a ^ (n + 2) * b +
            ((n + 1) * (b ^ 2 * (2 * a + b) * a ^ n) + a ^ (n + 1) * b ^ 2) :=
le_add_of_nonneg_right by
          apply_rules [add_nonneg, mul_nonneg, Nat.cast_nonneg, pow_nonneg, zero_le_one]
      _ = (a + b) ^ 2 * (a ^ (n + 1) + ↑(n + 1) * a ^ n * b) := by
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ', add_mul, mul_add,
          two_mul, pow_zero, mul_one,
          Hcomm.eq, (n.cast_commute (_ : R)).symm.left_comm, mul_assoc, (Hcomm.pow_left _).eq,
          (Hcomm.pow_left _).left_comm, Hcomm.left_comm, ← @two_add_one_eq_three R, one_mul]
        abel
      _ <= (a + b) ^ 2 * (a + b) ^ (n + 1) := by
        gcongr
        apply Commute.pow_add_mul_le_add_pow_of_sq_nonneg <;> assumption
      _ = (a + b) ^ (n + 3) := by simp [pow_succ', mul_assoc]

/--
lemma `one_add_mul_le_pow_of_sq_nonneg` / 引理 `one_add_mul_le_pow_of_sq_nonneg`

English:
lemma one_add_mul_le_pow_of_sq_nonneg
  statement: (Hsq : 0 <= a ^ 2) (Hsq' : 0 <= (1 + a) ^ 2) (H : 0 <= 2 + a)
  proof: by
  simpa using (Commute.one_left a).pow_add_mul_le_add_pow_of_sq_nonneg zero_le_one Hsq Hsq'
    (by simpa using H) n

中文:
引理 one_add_mul_le_pow_of_sq_nonneg
  结论: (Hsq : 0 <= a ^ 2) (Hsq' : 0 <= (1 + a) ^ 2) (H : 0 <= 2 + a)
  证明: by
  simpa using (Commute.one_left a).pow_add_mul_le_add_pow_of_sq_nonneg zero_le_one Hsq Hsq'
    (by simpa using H) n

Depends on / 依赖: Commute, Commute.one_left, one_left, pow_add_mul_le_add_pow_of_sq_nonneg, zero_le_one
-/
lemma one_add_mul_le_pow_of_sq_nonneg (Hsq : 0 <= a ^ 2) (Hsq' : 0 <= (1 + a) ^ 2) (H : 0 <= 2 + a)
    (n : Nat) : 1 + n * a <= (1 + a) ^ n := by
  simpa using (Commute.one_left a).pow_add_mul_le_add_pow_of_sq_nonneg zero_le_one Hsq Hsq'
    (by simpa using H) n

end OrderedSemiring

/--
lemma `pow_add_mul_le_add_pow_of_sq_nonneg` / 引理 `pow_add_mul_le_add_pow_of_sq_nonneg`

English:
lemma pow_add_mul_le_add_pow_of_sq_nonneg
  statement: [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
  proof: (Commute.all a b).pow_add_mul_le_add_pow_of_sq_nonneg ha Hsq Hsq' H n

中文:
引理 pow_add_mul_le_add_pow_of_sq_nonneg
  结论: [交换半环 R] [偏序 R] [是Ordered环 R]
  证明: (Commute.all a b).pow_add_mul_le_add_pow_of_sq_nonneg ha Hsq Hsq' H n

Depends on / 依赖: Commute, Commute.all, pow_add_mul_le_add_pow_of_sq_nonneg
-/
lemma pow_add_mul_le_add_pow_of_sq_nonneg [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    {a b : R} (ha : 0 <= a) (Hsq : 0 <= b ^ 2) (Hsq' : 0 <= (a + b) ^ 2) (H : 0 <= 2 * a + b)
    (n : Nat) : a ^ n + n * a ^ (n - 1) * b <= (a + b) ^ n :=
  (Commute.all a b).pow_add_mul_le_add_pow_of_sq_nonneg ha Hsq Hsq' H n

/--
lemma `Commute.pow_add_mul_le_add_pow` / 引理 `Commute.pow_add_mul_le_add_pow`

English:
lemma Commute.pow_add_mul_le_add_pow
  statement: [Semiring R] [LinearOrder R] [IsOrderedRing R]
  proof: Hcomm.pow_add_mul_le_add_pow_of_sq_nonneg ha (sq_nonneg _) (sq_nonneg _) H n

中文:
引理 Commute.pow_add_mul_le_add_pow
  结论: [半环 R] [线性序 R] [是Ordered环 R]
  证明: Hcomm.pow_add_mul_le_add_pow_of_sq_nonneg ha (sq_nonneg _) (sq_nonneg _) H n

Depends on / 依赖: Hcomm.pow_add_mul_le_add_pow_of_sq_nonneg, pow_add_mul_le_add_pow_of_sq_nonneg, sq_nonneg
-/
lemma Commute.pow_add_mul_le_add_pow [Semiring R] [LinearOrder R] [IsOrderedRing R]
    [ExistsAddOfLE R] {a b : R} (Hcomm : Commute a b) (ha : 0 <= a) (H : 0 <= 2 * a + b)
    (n : Nat) : a ^ n + n * a ^ (n - 1) * b <= (a + b) ^ n :=
  Hcomm.pow_add_mul_le_add_pow_of_sq_nonneg ha (sq_nonneg _) (sq_nonneg _) H n

/--
lemma `pow_add_mul_le_add_pow` / 引理 `pow_add_mul_le_add_pow`

English:
lemma pow_add_mul_le_add_pow
  statement: [CommSemiring R] [LinearOrder R] [IsOrderedRing R] [ExistsAddOfLE R]
  proof: (Commute.all a b).pow_add_mul_le_add_pow ha H n

中文:
引理 pow_add_mul_le_add_pow
  结论: [交换半环 R] [线性序 R] [是Ordered环 R] [ExistsAddOfLE R]
  证明: (Commute.all a b).pow_add_mul_le_add_pow ha H n

Depends on / 依赖: Commute, Commute.all, pow_add_mul_le_add_pow
-/
lemma pow_add_mul_le_add_pow [CommSemiring R] [LinearOrder R] [IsOrderedRing R] [ExistsAddOfLE R]
    {a b : R} (ha : 0 <= a) (H : 0 <= 2 * a + b) (n : Nat) :
    a ^ n + n * a ^ (n - 1) * b <= (a + b) ^ n :=
  (Commute.all a b).pow_add_mul_le_add_pow ha H n

/--
lemma `one_add_le_pow_of_two_add_nonneg` / 引理 `one_add_le_pow_of_two_add_nonneg`

English:
lemma one_add_le_pow_of_two_add_nonneg
  statement: [Semiring R] [LinearOrder R] [IsOrderedRing R]
  proof: one_add_mul_le_pow_of_sq_nonneg (sq_nonneg _) (sq_nonneg _) H _

中文:
引理 one_add_le_pow_of_two_add_nonneg
  结论: [半环 R] [线性序 R] [是Ordered环 R]
  证明: one_add_mul_le_pow_of_sq_nonneg (sq_nonneg _) (sq_nonneg _) H _

Depends on / 依赖: one_add_mul_le_pow_of_sq_nonneg, sq_nonneg
-/
lemma one_add_le_pow_of_two_add_nonneg [Semiring R] [LinearOrder R] [IsOrderedRing R]
    [ExistsAddOfLE R] {a : R} (H : 0 <= 2 + a) (n : Nat) : 1 + n * a <= (1 + a) ^ n :=
  one_add_mul_le_pow_of_sq_nonneg (sq_nonneg _) (sq_nonneg _) H _

section LinearOrderedRing
variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a : R} {n : Nat}

/--
lemma `one_add_mul_le_pow` / 引理 `one_add_mul_le_pow`

English:
lemma one_add_mul_le_pow
  given: (H : -2 <= a) (n : Nat)
  statement: 1 + n * a <= (1 + a) ^ n
  proof: one_add_le_pow_of_two_add_nonneg (neg_le_iff_add_nonneg'.mp H) n

中文:
引理 one_add_mul_le_pow
  条件: (H : -2 <= a) (n : 自然数)
  结论: 1 + n * a <= (1 + a) ^ n
  证明: one_add_le_pow_of_two_add_nonneg (neg_le_iff_add_nonneg'.mp H) n

Depends on / 依赖: neg_le_iff_add_nonneg, one_add_le_pow_of_two_add_nonneg
-/
lemma one_add_mul_le_pow (H : -2 <= a) (n : Nat) : 1 + n * a <= (1 + a) ^ n :=
  one_add_le_pow_of_two_add_nonneg (neg_le_iff_add_nonneg'.mp H) n

/--
lemma `one_add_mul_sub_le_pow` / 引理 `one_add_mul_sub_le_pow`

English:
lemma one_add_mul_sub_le_pow
  given: (H : -1 <= a) (n : Nat)
  statement: 1 + n * (a - 1) <= a ^ n
  proof: by
  have : -2 <= a - 1 := by
    rwa [← one_add_one_eq_two, neg_add, ← sub_eq_add_neg, sub_le_sub_iff_right]
  simpa only [add_sub_cancel] using one_add_mul_le_pow this n

中文:
引理 one_add_mul_sub_le_pow
  条件: (H : -1 <= a) (n : 自然数)
  结论: 1 + n * (a - 1) <= a ^ n
  证明: by
  have : -2 <= a - 1 := by
    rwa [← one_add_one_eq_two, neg_add, ← sub_eq_add_neg, sub_le_sub_iff_right]
  simpa only [add_sub_cancel] using one_add_mul_le_pow this n

Depends on / 依赖: add_sub_cancel, neg_add, one_add_mul_le_pow, one_add_one_eq_two, sub_eq_add_neg, sub_le_sub_iff_right
-/
lemma one_add_mul_sub_le_pow (H : -1 <= a) (n : Nat) : 1 + n * (a - 1) <= a ^ n := by
  have : -2 <= a - 1 := by
    rwa [← one_add_one_eq_two, neg_add, ← sub_eq_add_neg, sub_le_sub_iff_right]
  simpa only [add_sub_cancel] using one_add_mul_le_pow this n

end LinearOrderedRing
