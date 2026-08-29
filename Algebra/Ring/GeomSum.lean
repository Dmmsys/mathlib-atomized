/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.Ring.GrindInstances

/-!
# Partial sums of geometric series in a ring

This file determines the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof.

Several variants are recorded, generalising in particular to the case of a noncommutative ring in
which `x` and `y` commute. Even versions not using division or subtraction, valid in each semiring,
are recorded.
-/

public section

assert_not_exists Field IsOrderedRing

open Finset MulOpposite

variable {R S : Type*}

section Semiring
variable [Semiring R] [Semiring S] {x y : R}

/--
lemma `geom_sum_succ` / 引理 `geom_sum_succ`

English:
lemma geom_sum_succ
  given: {x : R} {n : Nat}
  proof: by
  simp only [mul_sum, ← pow_succ', sum_range_succ', pow_zero]

中文:
引理 geom_sum_succ
  条件: {x : R} {n : 自然数}
  证明: by
  simp only [mul_sum, ← pow_succ', sum_range_succ', pow_zero]

Depends on / 依赖: mul_sum, pow_succ, pow_zero, sum_range_succ
-/
lemma geom_sum_succ {x : R} {n : Nat} :
    ∑ i in range (n + 1), x ^ i = (x * ∑ i in range n, x ^ i) + 1 := by
  simp only [mul_sum, ← pow_succ', sum_range_succ', pow_zero]

/--
lemma `geom_sum_succ'` / 引理 `geom_sum_succ'`

English:
lemma geom_sum_succ'
  given: {x : R} {n : Nat}
  proof: (sum_range_succ _ _).trans (add_comm _ _)

中文:
引理 geom_sum_succ'
  条件: {x : R} {n : 自然数}
  证明: (sum_range_succ _ _).trans (add_comm _ _)

Depends on / 依赖: add_comm, sum_range_succ
-/
lemma geom_sum_succ' {x : R} {n : Nat} :
    ∑ i in range (n + 1), x ^ i = x ^ n + ∑ i in range n, x ^ i :=
  (sum_range_succ _ _).trans (add_comm _ _)

/--
lemma `geom_sum_zero` / 引理 `geom_sum_zero`

English:
lemma geom_sum_zero
  given: (x : R)
  statement: ∑ i in range 0, x ^ i = 0
  proof: rfl

中文:
引理 geom_sum_zero
  条件: (x : R)
  结论: ∑ i in range 0, x ^ i = 0
  证明: rfl
-/
lemma geom_sum_zero (x : R) : ∑ i in range 0, x ^ i = 0 :=
  rfl

/--
lemma `geom_sum_one` / 引理 `geom_sum_one`

English:
lemma geom_sum_one
  given: (x : R)
  statement: ∑ i in range 1, x ^ i = 1
  proof: by simp

@[simp]

中文:
引理 geom_sum_one
  条件: (x : R)
  结论: ∑ i in range 1, x ^ i = 1
  证明: by simp

@[simp]
-/
lemma geom_sum_one (x : R) : ∑ i in range 1, x ^ i = 1 := by simp

@[simp]
/--
lemma `geom_sum_two` / 引理 `geom_sum_two`

English:
lemma geom_sum_two
  given: {x : R}
  statement: ∑ i in range 2, x ^ i = x + 1
  proof: by simp [geom_sum_succ']

@[simp]

中文:
引理 geom_sum_two
  条件: {x : R}
  结论: ∑ i in range 2, x ^ i = x + 1
  证明: by simp [geom_sum_succ']

@[simp]

Depends on / 依赖: geom_sum_succ
-/
lemma geom_sum_two {x : R} : ∑ i in range 2, x ^ i = x + 1 := by simp [geom_sum_succ']

@[simp]
/--
lemma `zero_geom_sum` / 引理 `zero_geom_sum`

English:
lemma zero_geom_sum
  statement: forall {n}, ∑ i in range n, (0 : R) ^ i = if n = 0 then 0 else 1

中文:
引理 zero_geom_sum
  结论: 对任意 {n}, ∑ i in range n, (0 : R) ^ i = if n = 0 then 0 else 1
-/
lemma zero_geom_sum : forall {n}, ∑ i in range n, (0 : R) ^ i = if n = 0 then 0 else 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [geom_sum_succ']
    simp [zero_geom_sum]

/--
lemma `one_geom_sum` / 引理 `one_geom_sum`

English:
lemma one_geom_sum
  given: (n : Nat)
  statement: ∑ i in range n, (1 : R) ^ i = n
  proof: by simp

中文:
引理 one_geom_sum
  条件: (n : 自然数)
  结论: ∑ i in range n, (1 : R) ^ i = n
  证明: by simp
-/
lemma one_geom_sum (n : Nat) : ∑ i in range n, (1 : R) ^ i = n := by simp

/--
lemma `op_geom_sum` / 引理 `op_geom_sum`

English:
lemma op_geom_sum
  given: (x : R) (n : Nat)
  statement: op (∑ i in range n, x ^ i) = ∑ i in range n, op x ^ i
  proof: by
  simp

@[simp]

中文:
引理 op_geom_sum
  条件: (x : R) (n : 自然数)
  结论: op (∑ i in range n, x ^ i) = ∑ i in range n, op x ^ i
  证明: by
  simp

@[simp]
-/
lemma op_geom_sum (x : R) (n : Nat) : op (∑ i in range n, x ^ i) = ∑ i in range n, op x ^ i := by
  simp

@[simp]
/--
lemma `op_geom_sum₂` / 引理 `op_geom_sum₂`

English:
lemma op_geom_sum₂
  given: (x y : R) (n : Nat)
  statement: ∑ i in range n, op y ^ (n - 1 - i) * op x ^ i =
  proof: by
  rw [← sum_range_reflect]
  refine sum_congr rfl fun j j_in => ?_
  grind

中文:
引理 op_geom_sum₂
  条件: (x y : R) (n : 自然数)
  结论: ∑ i in range n, op y ^ (n - 1 - i) * op x ^ i =
  证明: by
  rw [← sum_range_reflect]
  refine sum_congr rfl fun j j_in => ?_
  grind

Depends on / 依赖: j_in, sum_congr, sum_range_reflect
-/
lemma op_geom_sum₂ (x y : R) (n : Nat) : ∑ i in range n, op y ^ (n - 1 - i) * op x ^ i =
    ∑ i in range n, op y ^ i * op x ^ (n - 1 - i) := by
  rw [← sum_range_reflect]
  refine sum_congr rfl fun j j_in => ?_
  grind

/--
lemma `geom_sum₂_with_one` / 引理 `geom_sum₂_with_one`

English:
lemma geom_sum₂_with_one
  given: (x : R) (n : Nat)
  proof: sum_congr rfl fun i _ => by rw [one_pow, mul_one]

中文:
引理 geom_sum₂_with_one
  条件: (x : R) (n : 自然数)
  证明: sum_congr rfl fun i _ => by rw [one_pow, mul_one]

Depends on / 依赖: mul_one, one_pow, sum_congr
-/
lemma geom_sum₂_with_one (x : R) (n : Nat) :
    ∑ i in range n, x ^ i * 1 ^ (n - 1 - i) = ∑ i in range n, x ^ i :=
  sum_congr rfl fun i _ => by rw [one_pow, mul_one]

/--
lemma `Commute.geom_sum₂_mul_add` / 引理 `Commute.geom_sum₂_mul_add`

English:
lemma Commute.geom_sum₂_mul_add
  given: {x y : R} (h : Commute x y) (n : Nat)
  proof: by
  let f : Nat -> Nat -> R := fun m i : Nat => (x + y) ^ i * y ^ (m - 1 - i)
  change (∑ i in range n, (f n) i) * x + y ^ n = (x + y) ^ n
  induction n with
  | zero => rw [range_zero, sum_empty, zero_mul, zero_add, pow_zero, pow_zero]
  | succ n ih =>
    have f_last : f (n + 1) n = (x + y) ^ n :

中文:
引理 Commute.geom_sum₂_mul_add
  条件: {x y : R} (h : Commute x y) (n : 自然数)
  证明: by
  let f : Nat -> Nat -> R := fun m i : Nat => (x + y) ^ i * y ^ (m - 1 - i)
  change (∑ i in range n, (f n) i) * x + y ^ n = (x + y) ^ n
  induction n with
  | zero => rw [range_zero, sum_empty, zero_mul, zero_add, pow_zero, pow_zero]
  | succ n ih =>
    have f_last : f (n + 1) n = (x + y) ^ n :
-/
protected lemma Commute.geom_sum₂_mul_add {x y : R} (h : Commute x y) (n : Nat) :
    (∑ i in range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n := by
  let f : Nat -> Nat -> R := fun m i : Nat => (x + y) ^ i * y ^ (m - 1 - i)
  change (∑ i in range n, (f n) i) * x + y ^ n = (x + y) ^ n
  induction n with
  | zero => rw [range_zero, sum_empty, zero_mul, zero_add, pow_zero, pow_zero]
  | succ n ih =>
    have f_last : f (n + 1) n = (x + y) ^ n := by
      dsimp only [f]
      rw [← tsub_add_eq_tsub_tsub]; rw [Nat.add_comm]; rw [tsub_self]; rw [pow_zero]; rw [mul_one]
    have f_succ : forall i, i in range n -> f (n + 1) i = y * f n i := fun i hi => by
      dsimp only [f]
      have : Commute y ((x + y) ^ i) := (h.symm.add_right (Commute.refl y)).pow_right i
      rw [← mul_assoc]; rw [this.eq]; rw [mul_assoc]; rw [← pow_succ' y (n - 1 - i)]; rw [add_tsub_cancel_right]; rw [← tsub_add_eq_tsub_tsub]; rw [add_comm 1 i]
      have : i + 1 + (n - (i + 1)) = n := add_tsub_cancel_of_le (mem_range.mp hi)
      rw [add_comm (i + 1)] at this
      rw [← this]; rw [add_tsub_cancel_right]; rw [add_comm i 1]; rw [← add_assoc]; rw [add_tsub_cancel_right]
    rw [pow_succ' (x + y)]; rw [add_mul]; rw [sum_range_succ_comm]; rw [add_mul]; rw [f_last]; rw [add_assoc]; rw [(((Commute.refl x).add_right h).pow_right n).eq]; rw [sum_congr rfl f_succ]; rw [← mul_sum]; rw [pow_succ' y]; rw [mul_assoc]; rw [← mul_add y]; rw [ih]

/--
lemma `geom_sum₂_self` / 引理 `geom_sum₂_self`

English:
lemma geom_sum₂_self
  given: (x : R) (n : Nat)
  statement: ∑ i in range n, x ^ i * x ^ (n - 1 - i) = n * x ^ (n - 1)
  proof: calc
    ∑ i in Finset.range n, x ^ i * x ^ (n - 1 - i) =
        ∑ i in Finset.range n, x ^ (i + (n - 1 - i)) := by
      simp_rw [← pow_add]
    _ = ∑ _i in Finset.range n, x ^ (n - 1) :=
      Finset.sum_congr rfl fun _ hi =>
congr_arg _ add_tsub_cancel_of_le Nat.le_sub_one_of_lt Finset.mem_range

中文:
引理 geom_sum₂_self
  条件: (x : R) (n : 自然数)
  结论: ∑ i in range n, x ^ i * x ^ (n - 1 - i) = n * x ^ (n - 1)
  证明: calc
    ∑ i in Finset.range n, x ^ i * x ^ (n - 1 - i) =
        ∑ i in Finset.range n, x ^ (i + (n - 1 - i)) := by
      simp_rw [← pow_add]
    _ = ∑ _i in Finset.range n, x ^ (n - 1) :=
      Finset.sum_congr rfl fun _ hi =>
congr_arg _ add_tsub_cancel_of_le Nat.le_sub_one_of_lt Finset.mem_range

Depends on / 依赖: Finset, Finset.card_range, Finset.mem_range, Finset.range, Finset.sum_congr, Nat.le_sub_one_of_lt, add_tsub_cancel_of_le, card_range, congr_arg, le_sub_one_of_lt, mem_range, nsmul_eq_mul, pow_add, simp_rw, sum_congr, sum_const
-/
lemma geom_sum₂_self (x : R) (n : Nat) : ∑ i in range n, x ^ i * x ^ (n - 1 - i) = n * x ^ (n - 1) :=
  calc
    ∑ i in Finset.range n, x ^ i * x ^ (n - 1 - i) =
        ∑ i in Finset.range n, x ^ (i + (n - 1 - i)) := by
      simp_rw [← pow_add]
    _ = ∑ _i in Finset.range n, x ^ (n - 1) :=
      Finset.sum_congr rfl fun _ hi =>
congr_arg _ add_tsub_cancel_of_le Nat.le_sub_one_of_lt Finset.mem_range.1 hi
    _ = #(range n) • x ^ (n - 1) := sum_const _
    _ = n * x ^ (n - 1) := by rw [Finset.card_range, nsmul_eq_mul]

/--
lemma `geom_sum_mul_add` / 引理 `geom_sum_mul_add`

English:
lemma geom_sum_mul_add
  given: (x : R) (n : Nat)
  statement: (∑ i in range n, (x + 1) ^ i) * x + 1 = (x + 1) ^ n
  proof: by
  have := (Commute.one_right x).geom_sum₂_mul_add n
  rw [one_pow]; rw [geom_sum₂_with_one] at this
  exact this

中文:
引理 geom_sum_mul_add
  条件: (x : R) (n : 自然数)
  结论: (∑ i in range n, (x + 1) ^ i) * x + 1 = (x + 1) ^ n
  证明: by
  have := (Commute.one_right x).geom_sum₂_mul_add n
  rw [one_pow]; rw [geom_sum₂_with_one] at this
  exact this

Depends on / 依赖: Commute, Commute.one_right, one_pow, one_right
-/
lemma geom_sum_mul_add (x : R) (n : Nat) : (∑ i in range n, (x + 1) ^ i) * x + 1 = (x + 1) ^ n := by
  have := (Commute.one_right x).geom_sum₂_mul_add n
  rw [one_pow]; rw [geom_sum₂_with_one] at this
  exact this

/--
lemma `Commute.geom_sum₂_comm` / 引理 `Commute.geom_sum₂_comm`

English:
lemma Commute.geom_sum₂_comm
  given: (n : Nat) (h : Commute x y)
  proof: by
  cases n; · simp
  simp only [Nat.add_sub_cancel]
  rw [← Finset.sum_flip]
  refine Finset.sum_congr rfl fun i hi => ?_
  simpa [Nat.sub_sub_self (Nat.succ_le_succ_iff.mp (Finset.mem_range.mp hi))] using! h.pow_pow _ _

中文:
引理 Commute.geom_sum₂_comm
  条件: (n : 自然数) (h : Commute x y)
  证明: by
  cases n; · simp
  simp only [Nat.add_sub_cancel]
  rw [← Finset.sum_flip]
  refine Finset.sum_congr rfl fun i hi => ?_
  simpa [Nat.sub_sub_self (Nat.succ_le_succ_iff.mp (Finset.mem_range.mp hi))] using! h.pow_pow _ _
-/
protected lemma Commute.geom_sum₂_comm (n : Nat) (h : Commute x y) :
    ∑ i in range n, x ^ i * y ^ (n - 1 - i) = ∑ i in range n, y ^ i * x ^ (n - 1 - i) := by
  cases n; · simp
  simp only [Nat.add_sub_cancel]
  rw [← Finset.sum_flip]
  refine Finset.sum_congr rfl fun i hi => ?_
  simpa [Nat.sub_sub_self (Nat.succ_le_succ_iff.mp (Finset.mem_range.mp hi))] using! h.pow_pow _ _

-- TODO: for consistency, the next two lemmas should be moved to the root namespace
/--
lemma `RingHom.map_geom_sum` / 引理 `RingHom.map_geom_sum`

English:
lemma RingHom.map_geom_sum
  given: (x : R) (n : Nat) (f : R ->+* S)
  proof: by simp [map_sum f]

中文:
引理 环态射.map_geom_sum
  条件: (x : R) (n : 自然数) (f : R ->+* S)
  证明: by simp [map_sum f]

Depends on / 依赖: map_sum
-/
lemma RingHom.map_geom_sum (x : R) (n : Nat) (f : R ->+* S) :
    f (∑ i in range n, x ^ i) = ∑ i in range n, f x ^ i := by simp [map_sum f]

/--
lemma `RingHom.map_geom_sum₂` / 引理 `RingHom.map_geom_sum₂`

English:
lemma RingHom.map_geom_sum₂
  given: (x y : R) (n : Nat) (f : R ->+* S)
  proof: by
  simp [map_sum f]

中文:
引理 环态射.map_geom_sum₂
  条件: (x y : R) (n : 自然数) (f : R ->+* S)
  证明: by
  simp [map_sum f]

Depends on / 依赖: map_sum
-/
lemma RingHom.map_geom_sum₂ (x y : R) (n : Nat) (f : R ->+* S) :
    f (∑ i in range n, x ^ i * y ^ (n - 1 - i)) = ∑ i in range n, f x ^ i * f y ^ (n - 1 - i) := by
  simp [map_sum f]

end Semiring

section CommSemiring
variable [CommSemiring R]

/--
lemma `geom_sum₂_mul_add` / 引理 `geom_sum₂_mul_add`

English:
lemma geom_sum₂_mul_add
  given: (x y : R) (n : Nat)
  proof: (Commute.all x y).geom_sum₂_mul_add n

中文:
引理 geom_sum₂_mul_add
  条件: (x y : R) (n : 自然数)
  证明: (Commute.all x y).geom_sum₂_mul_add n

Depends on / 依赖: Commute, Commute.all
-/
lemma geom_sum₂_mul_add (x y : R) (n : Nat) :
    (∑ i in range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n :=
  (Commute.all x y).geom_sum₂_mul_add n

/--
lemma `geom_sum₂_comm` / 引理 `geom_sum₂_comm`

English:
lemma geom_sum₂_comm
  given: (x y : R) (n : Nat)
  proof: (Commute.all x y).geom_sum₂_comm n

中文:
引理 geom_sum₂_comm
  条件: (x y : R) (n : 自然数)
  证明: (Commute.all x y).geom_sum₂_comm n

Depends on / 依赖: Commute, Commute.all
-/
lemma geom_sum₂_comm (x y : R) (n : Nat) :
    ∑ i in range n, x ^ i * y ^ (n - 1 - i) = ∑ i in range n, y ^ i * x ^ (n - 1 - i) :=
  (Commute.all x y).geom_sum₂_comm n

variable [PartialOrder R] [AddLeftReflectLE R] [AddLeftMono R] [ExistsAddOfLE R] [Sub R]
  [OrderedSub R] {x y : R}

/--
lemma `geom_sum₂_mul_of_ge` / 引理 `geom_sum₂_mul_of_ge`

English:
lemma geom_sum₂_mul_of_ge
  given: (hxy : y <= x) (n : Nat)
  proof: by
  apply eq_tsub_of_add_eq
  simpa only [tsub_add_cancel_of_le hxy] using geom_sum₂_mul_add (x - y) y n

中文:
引理 geom_sum₂_mul_of_ge
  条件: (hxy : y <= x) (n : 自然数)
  证明: by
  apply eq_tsub_of_add_eq
  simpa only [tsub_add_cancel_of_le hxy] using geom_sum₂_mul_add (x - y) y n

Depends on / 依赖: eq_tsub_of_add_eq, tsub_add_cancel_of_le
-/
lemma geom_sum₂_mul_of_ge (hxy : y <= x) (n : Nat) :
    (∑ i in range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := by
  apply eq_tsub_of_add_eq
  simpa only [tsub_add_cancel_of_le hxy] using geom_sum₂_mul_add (x - y) y n

/--
lemma `geom_sum₂_mul_of_le` / 引理 `geom_sum₂_mul_of_le`

English:
lemma geom_sum₂_mul_of_le
  given: (hxy : x <= y) (n : Nat)
  proof: by
  rw [← Finset.sum_range_reflect]
  convert! geom_sum₂_mul_of_ge hxy n using 3
  simp_all only [Finset.mem_range]
  rw [mul_comm]
  congr
  lia

中文:
引理 geom_sum₂_mul_of_le
  条件: (hxy : x <= y) (n : 自然数)
  证明: by
  rw [← Finset.sum_range_reflect]
  convert! geom_sum₂_mul_of_ge hxy n using 3
  simp_all only [Finset.mem_range]
  rw [mul_comm]
  congr
  lia

Depends on / 依赖: Finset, Finset.mem_range, Finset.sum_range_reflect, convert, mem_range, mul_comm, sum_range_reflect
-/
lemma geom_sum₂_mul_of_le (hxy : x <= y) (n : Nat) :
    (∑ i in range n, x ^ i * y ^ (n - 1 - i)) * (y - x) = y ^ n - x ^ n := by
  rw [← Finset.sum_range_reflect]
  convert! geom_sum₂_mul_of_ge hxy n using 3
  simp_all only [Finset.mem_range]
  rw [mul_comm]
  congr
  lia

/--
lemma `geom_sum_mul_of_one_le` / 引理 `geom_sum_mul_of_one_le`

English:
lemma geom_sum_mul_of_one_le
  given: (hx : 1 <= x) (n : Nat)
  proof: by simpa using geom_sum₂_mul_of_ge hx n

中文:
引理 geom_sum_mul_of_one_le
  条件: (hx : 1 <= x) (n : 自然数)
  证明: by simpa using geom_sum₂_mul_of_ge hx n
-/
lemma geom_sum_mul_of_one_le (hx : 1 <= x) (n : Nat) :
    (∑ i in range n, x ^ i) * (x - 1) = x ^ n - 1 := by simpa using geom_sum₂_mul_of_ge hx n

/--
lemma `geom_sum_mul_of_le_one` / 引理 `geom_sum_mul_of_le_one`

English:
lemma geom_sum_mul_of_le_one
  given: (hx : x <= 1) (n : Nat)
  proof: by simpa using geom_sum₂_mul_of_le hx n

中文:
引理 geom_sum_mul_of_le_one
  条件: (hx : x <= 1) (n : 自然数)
  证明: by simpa using geom_sum₂_mul_of_le hx n
-/
lemma geom_sum_mul_of_le_one (hx : x <= 1) (n : Nat) :
    (∑ i in range n, x ^ i) * (1 - x) = 1 - x ^ n := by simpa using geom_sum₂_mul_of_le hx n

end CommSemiring

section Ring
variable [Ring R] {x y : R}

@[simp]
/--
lemma `neg_one_geom_sum` / 引理 `neg_one_geom_sum`

English:
lemma neg_one_geom_sum
  given: {n : Nat}
  statement: ∑ i in range n, (-1 : R) ^ i = if Even n then 0 else 1
  proof: by
  induction n with
  | zero => simp
  | succ k hk =>
    simp only [geom_sum_succ', Nat.even_add_one, hk]
    split_ifs with h
    · rw [h.neg_one_pow, add_zero]
    · rw [(Nat.not_even_iff_odd.1 h).neg_one_pow, neg_add_cancel]

中文:
引理 neg_one_geom_sum
  条件: {n : 自然数}
  结论: ∑ i in range n, (-1 : R) ^ i = if Even n then 0 else 1
  证明: by
  induction n with
  | zero => simp
  | succ k hk =>
    simp only [geom_sum_succ', Nat.even_add_one, hk]
    split_ifs with h
    · rw [h.neg_one_pow, add_zero]
    · rw [(Nat.not_even_iff_odd.1 h).neg_one_pow, neg_add_cancel]

Depends on / 依赖: Nat.even_add_one, Nat.not_even_iff_odd, add_zero, even_add_one, geom_sum_succ, h.neg_one_pow, neg_add_cancel, neg_one_pow, not_even_iff_odd, split_ifs
-/
lemma neg_one_geom_sum {n : Nat} : ∑ i in range n, (-1 : R) ^ i = if Even n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ k hk =>
    simp only [geom_sum_succ', Nat.even_add_one, hk]
    split_ifs with h
    · rw [h.neg_one_pow, add_zero]
    · rw [(Nat.not_even_iff_odd.1 h).neg_one_pow, neg_add_cancel]

/--
lemma `Commute.geom_sum₂_mul` / 引理 `Commute.geom_sum₂_mul`

English:
lemma Commute.geom_sum₂_mul
  given: (h : Commute x y) (n : Nat)
  proof: by
  have := (h.sub_left (Commute.refl y)).geom_sum₂_mul_add n
  rw [sub_add_cancel] at this
  rw [← this]; rw [add_sub_cancel_right]

中文:
引理 Commute.geom_sum₂_mul
  条件: (h : Commute x y) (n : 自然数)
  证明: by
  have := (h.sub_left (Commute.refl y)).geom_sum₂_mul_add n
  rw [sub_add_cancel] at this
  rw [← this]; rw [add_sub_cancel_right]
-/
protected lemma Commute.geom_sum₂_mul (h : Commute x y) (n : Nat) :
    (∑ i in range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := by
  have := (h.sub_left (Commute.refl y)).geom_sum₂_mul_add n
  rw [sub_add_cancel] at this
  rw [← this]; rw [add_sub_cancel_right]

/--
lemma `Commute.mul_neg_geom_sum₂` / 引理 `Commute.mul_neg_geom_sum₂`

English:
lemma Commute.mul_neg_geom_sum₂
  given: (h : Commute x y) (n : Nat)
  proof: by
  apply op_injective
  simp only [op_mul, op_sub, op_pow]
  simp [(Commute.op h.symm).geom_sum₂_mul n]

中文:
引理 Commute.mul_neg_geom_sum₂
  条件: (h : Commute x y) (n : 自然数)
  证明: by
  apply op_injective
  simp only [op_mul, op_sub, op_pow]
  simp [(Commute.op h.symm).geom_sum₂_mul n]

Depends on / 依赖: Commute, Commute.op, h.symm, op_injective, op_mul, op_pow, op_sub
-/
lemma Commute.mul_neg_geom_sum₂ (h : Commute x y) (n : Nat) :
    ((y - x) * ∑ i in range n, x ^ i * y ^ (n - 1 - i)) = y ^ n - x ^ n := by
  apply op_injective
  simp only [op_mul, op_sub, op_pow]
  simp [(Commute.op h.symm).geom_sum₂_mul n]

/--
lemma `Commute.mul_geom_sum₂` / 引理 `Commute.mul_geom_sum₂`

English:
lemma Commute.mul_geom_sum₂
  given: (h : Commute x y) (n : Nat)
  proof: by
  rw [← neg_sub (y ^ n)]; rw [← h.mul_neg_geom_sum₂]; rw [← neg_mul]; rw [neg_sub]

中文:
引理 Commute.mul_geom_sum₂
  条件: (h : Commute x y) (n : 自然数)
  证明: by
  rw [← neg_sub (y ^ n)]; rw [← h.mul_neg_geom_sum₂]; rw [← neg_mul]; rw [neg_sub]

Depends on / 依赖: h.mul_neg_geom_sum, neg_mul, neg_sub
-/
lemma Commute.mul_geom_sum₂ (h : Commute x y) (n : Nat) :
    ((x - y) * ∑ i in range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n := by
  rw [← neg_sub (y ^ n)]; rw [← h.mul_neg_geom_sum₂]; rw [← neg_mul]; rw [neg_sub]

/--
lemma `Commute.sub_dvd_pow_sub_pow` / 引理 `Commute.sub_dvd_pow_sub_pow`

English:
lemma Commute.sub_dvd_pow_sub_pow
  given: (h : Commute x y) (n : Nat)
  statement: x - y ∣ x ^ n - y ^ n
  proof: Dvd.intro _ h.mul_geom_sum₂ _

中文:
引理 Commute.sub_dvd_pow_sub_pow
  条件: (h : Commute x y) (n : 自然数)
  结论: x - y ∣ x ^ n - y ^ n
  证明: Dvd.intro _ h.mul_geom_sum₂ _

Depends on / 依赖: Dvd.intro, h.mul_geom_sum
-/
lemma Commute.sub_dvd_pow_sub_pow (h : Commute x y) (n : Nat) : x - y ∣ x ^ n - y ^ n :=
Dvd.intro _ h.mul_geom_sum₂ _

/--
lemma `one_sub_dvd_one_sub_pow` / 引理 `one_sub_dvd_one_sub_pow`

English:
lemma one_sub_dvd_one_sub_pow
  given: (x : R) (n : Nat)
  statement: 1 - x ∣ 1 - x ^ n
  proof: by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_left x).sub_dvd_pow_sub_pow n

中文:
引理 one_sub_dvd_one_sub_pow
  条件: (x : R) (n : 自然数)
  结论: 1 - x ∣ 1 - x ^ n
  证明: by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_left x).sub_dvd_pow_sub_pow n

Depends on / 依赖: Commute, Commute.one_left, conv_rhs, one_left, one_pow, sub_dvd_pow_sub_pow
-/
lemma one_sub_dvd_one_sub_pow (x : R) (n : Nat) : 1 - x ∣ 1 - x ^ n := by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_left x).sub_dvd_pow_sub_pow n

/--
lemma `sub_one_dvd_pow_sub_one` / 引理 `sub_one_dvd_pow_sub_one`

English:
lemma sub_one_dvd_pow_sub_one
  given: (x : R) (n : Nat)
  statement: x - 1 ∣ x ^ n - 1
  proof: by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_right x).sub_dvd_pow_sub_pow n

中文:
引理 sub_one_dvd_pow_sub_one
  条件: (x : R) (n : 自然数)
  结论: x - 1 ∣ x ^ n - 1
  证明: by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_right x).sub_dvd_pow_sub_pow n

Depends on / 依赖: Commute, Commute.one_right, conv_rhs, one_pow, one_right, sub_dvd_pow_sub_pow
-/
lemma sub_one_dvd_pow_sub_one (x : R) (n : Nat) : x - 1 ∣ x ^ n - 1 := by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_right x).sub_dvd_pow_sub_pow n

/--
lemma `pow_one_sub_dvd_pow_mul_sub_one` / 引理 `pow_one_sub_dvd_pow_mul_sub_one`

English:
lemma pow_one_sub_dvd_pow_mul_sub_one
  given: (x : R) (m n : Nat)
  statement: x ^ m - 1 ∣ x ^ (m * n) - 1
  proof: by
  rw [pow_mul]; exact sub_one_dvd_pow_sub_one (x ^ m) n

中文:
引理 pow_one_sub_dvd_pow_mul_sub_one
  条件: (x : R) (m n : 自然数)
  结论: x ^ m - 1 ∣ x ^ (m * n) - 1
  证明: by
  rw [pow_mul]; exact sub_one_dvd_pow_sub_one (x ^ m) n

Depends on / 依赖: pow_mul, sub_one_dvd_pow_sub_one
-/
lemma pow_one_sub_dvd_pow_mul_sub_one (x : R) (m n : Nat) : x ^ m - 1 ∣ x ^ (m * n) - 1 := by
  rw [pow_mul]; exact sub_one_dvd_pow_sub_one (x ^ m) n

/--
theorem `dvd_pow_sub_one_of_dvd` / 定理 `dvd_pow_sub_one_of_dvd`

English:
theorem dvd_pow_sub_one_of_dvd
  given: {r : R} {a b : Nat} (h : a ∣ b)
  proof: by
  obtain ⟨n, rfl⟩ := h
  exact pow_one_sub_dvd_pow_mul_sub_one r a n

中文:
定理 dvd_pow_sub_one_of_dvd
  条件: {r : R} {a b : 自然数} (h : a ∣ b)
  证明: by
  obtain ⟨n, rfl⟩ := h
  exact pow_one_sub_dvd_pow_mul_sub_one r a n

Depends on / 依赖: pow_one_sub_dvd_pow_mul_sub_one
-/
theorem dvd_pow_sub_one_of_dvd {r : R} {a b : Nat} (h : a ∣ b) :
    r ^ a - 1 ∣ r ^ b - 1 := by
  obtain ⟨n, rfl⟩ := h
  exact pow_one_sub_dvd_pow_mul_sub_one r a n

/--
theorem `dvd_pow_pow_sub_self_of_dvd` / 定理 `dvd_pow_pow_sub_self_of_dvd`

English:
theorem dvd_pow_pow_sub_self_of_dvd
  given: {r : R} {p a b : Nat} (h : a ∣ b)
  proof: by
  by_cases hp₀ : p = 0
  · by_cases hb₀ : b = 0
    · rw [hp₀, hb₀, pow_zero, pow_one, sub_self]
      exact dvd_zero _
    have ha₀ : a != 0 := by rintro rfl; rw [zero_dvd_iff] at h; tauto
    rw [hp₀]; rw [zero_pow ha₀]; rw [zero_pow hb₀]
have hp (c) : 1 <= p ^ c := Nat.pow_pos pos_of_ne_zero h

中文:
定理 dvd_pow_pow_sub_self_of_dvd
  条件: {r : R} {p a b : 自然数} (h : a ∣ b)
  证明: by
  by_cases hp₀ : p = 0
  · by_cases hb₀ : b = 0
    · rw [hp₀, hb₀, pow_zero, pow_one, sub_self]
      exact dvd_zero _
    have ha₀ : a != 0 := by rintro rfl; rw [zero_dvd_iff] at h; tauto
    rw [hp₀]; rw [zero_pow ha₀]; rw [zero_pow hb₀]
have hp (c) : 1 <= p ^ c := Nat.pow_pos pos_of_ne_zero h

Depends on / 依赖: Int.natCast_dvd_natCast.mp, Nat.pow_pos, Nat.sub_add_cancel, dvd_pow_sub_one_of_dvd, dvd_zero, mul_dvd_mul_left, mul_sub_one, natCast_dvd_natCast, pos_of_ne_zero, pow_one, pow_pos, pow_succ, pow_zero, sub_add_cancel, sub_self, zero_dvd_iff, zero_pow
-/
theorem dvd_pow_pow_sub_self_of_dvd {r : R} {p a b : Nat} (h : a ∣ b) :
    r ^ p ^ a - r ∣ r ^ p ^ b - r := by
  by_cases hp₀ : p = 0
  · by_cases hb₀ : b = 0
    · rw [hp₀, hb₀, pow_zero, pow_one, sub_self]
      exact dvd_zero _
    have ha₀ : a != 0 := by rintro rfl; rw [zero_dvd_iff] at h; tauto
    rw [hp₀]; rw [zero_pow ha₀]; rw [zero_pow hb₀]
have hp (c) : 1 <= p ^ c := Nat.pow_pos pos_of_ne_zero hp₀
  rw [← Nat.sub_add_cancel (hp a)]; rw [← Nat.sub_add_cancel (hp b)]; rw [pow_succ']; rw [pow_succ']; rw [← mul_sub_one]; rw [← mul_sub_one]
refine mul_dvd_mul_left _ dvd_pow_sub_one_of_dvd Int.natCast_dvd_natCast.mp ?_
  push_cast [hp a, hp b]
  exact dvd_pow_sub_one_of_dvd h

/--
lemma `geom_sum_mul` / 引理 `geom_sum_mul`

English:
lemma geom_sum_mul
  given: (x : R) (n : Nat)
  statement: (∑ i in range n, x ^ i) * (x - 1) = x ^ n - 1
  proof: by
  have := (Commute.one_right x).geom_sum₂_mul n
  rw [one_pow]; rw [geom_sum₂_with_one] at this
  exact this

中文:
引理 geom_sum_mul
  条件: (x : R) (n : 自然数)
  结论: (∑ i in range n, x ^ i) * (x - 1) = x ^ n - 1
  证明: by
  have := (Commute.one_right x).geom_sum₂_mul n
  rw [one_pow]; rw [geom_sum₂_with_one] at this
  exact this

Depends on / 依赖: Commute, Commute.one_right, one_pow, one_right
-/
lemma geom_sum_mul (x : R) (n : Nat) : (∑ i in range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  have := (Commute.one_right x).geom_sum₂_mul n
  rw [one_pow]; rw [geom_sum₂_with_one] at this
  exact this

/--
lemma `mul_geom_sum` / 引理 `mul_geom_sum`

English:
lemma mul_geom_sum
  given: (x : R) (n : Nat)
  statement: ((x - 1) * ∑ i in range n, x ^ i) = x ^ n - 1
  proof: op_injective by simpa using geom_sum_mul (op x) n

中文:
引理 mul_geom_sum
  条件: (x : R) (n : 自然数)
  结论: ((x - 1) * ∑ i in range n, x ^ i) = x ^ n - 1
  证明: op_injective by simpa using geom_sum_mul (op x) n

Depends on / 依赖: geom_sum_mul, op_injective
-/
lemma mul_geom_sum (x : R) (n : Nat) : ((x - 1) * ∑ i in range n, x ^ i) = x ^ n - 1 :=
op_injective by simpa using geom_sum_mul (op x) n

/--
lemma `geom_sum_mul_neg` / 引理 `geom_sum_mul_neg`

English:
lemma geom_sum_mul_neg
  given: (x : R) (n : Nat)
  statement: (∑ i in range n, x ^ i) * (1 - x) = 1 - x ^ n
  proof: by
  have := congr_arg Neg.neg (geom_sum_mul x n)
  rw [neg_sub]; rw [← mul_neg]; rw [neg_sub] at this
  exact this

中文:
引理 geom_sum_mul_neg
  条件: (x : R) (n : 自然数)
  结论: (∑ i in range n, x ^ i) * (1 - x) = 1 - x ^ n
  证明: by
  have := congr_arg Neg.neg (geom_sum_mul x n)
  rw [neg_sub]; rw [← mul_neg]; rw [neg_sub] at this
  exact this

Depends on / 依赖: Neg.neg, congr_arg, geom_sum_mul, mul_neg, neg_sub
-/
lemma geom_sum_mul_neg (x : R) (n : Nat) : (∑ i in range n, x ^ i) * (1 - x) = 1 - x ^ n := by
  have := congr_arg Neg.neg (geom_sum_mul x n)
  rw [neg_sub]; rw [← mul_neg]; rw [neg_sub] at this
  exact this

/--
lemma `mul_neg_geom_sum` / 引理 `mul_neg_geom_sum`

English:
lemma mul_neg_geom_sum
  given: (x : R) (n : Nat)
  statement: ((1 - x) * ∑ i in range n, x ^ i) = 1 - x ^ n
  proof: op_injective by simpa using geom_sum_mul_neg (op x) n

中文:
引理 mul_neg_geom_sum
  条件: (x : R) (n : 自然数)
  结论: ((1 - x) * ∑ i in range n, x ^ i) = 1 - x ^ n
  证明: op_injective by simpa using geom_sum_mul_neg (op x) n

Depends on / 依赖: geom_sum_mul_neg, op_injective
-/
lemma mul_neg_geom_sum (x : R) (n : Nat) : ((1 - x) * ∑ i in range n, x ^ i) = 1 - x ^ n :=
op_injective by simpa using geom_sum_mul_neg (op x) n

/--
lemma `Commute.mul_geom_sum₂_Ico` / 引理 `Commute.mul_geom_sum₂_Ico`

English:
lemma Commute.mul_geom_sum₂_Ico
  statement: (h : Commute x y) {m n : Nat}
  proof: by
  rw [sum_Ico_eq_sub _ hmn]
  have :
    ∑ k in range m, x ^ k * y ^ (n - 1 - k) =
      ∑ k in range m, x ^ k * (y ^ (n - m) * y ^ (m - 1 - k)) := by
    refine sum_congr rfl fun j j_in => ?_
    rw [← pow_add]
    congr
    rw [mem_range] at j_in
    lia
  rw [this]
  simp_rw [pow_mul_comm y (n

中文:
引理 Commute.mul_geom_sum₂_Ico
  结论: (h : Commute x y) {m n : 自然数}
  证明: by
  rw [sum_Ico_eq_sub _ hmn]
  have :
    ∑ k in range m, x ^ k * y ^ (n - 1 - k) =
      ∑ k in range m, x ^ k * (y ^ (n - m) * y ^ (m - 1 - k)) := by
    refine sum_congr rfl fun j j_in => ?_
    rw [← pow_add]
    congr
    rw [mem_range] at j_in
    lia
  rw [this]
  simp_rw [pow_mul_comm y (n
-/
protected lemma Commute.mul_geom_sum₂_Ico (h : Commute x y) {m n : Nat}
    (hmn : m <= n) :
    ((x - y) * ∑ i in Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) := by
  rw [sum_Ico_eq_sub _ hmn]
  have :
    ∑ k in range m, x ^ k * y ^ (n - 1 - k) =
      ∑ k in range m, x ^ k * (y ^ (n - m) * y ^ (m - 1 - k)) := by
    refine sum_congr rfl fun j j_in => ?_
    rw [← pow_add]
    congr
    rw [mem_range] at j_in
    lia
  rw [this]
  simp_rw [pow_mul_comm y (n - m) _]
  simp_rw [← mul_assoc]
  rw [← sum_mul]; rw [mul_sub]; rw [h.mul_geom_sum₂]; rw [← mul_assoc]; rw [h.mul_geom_sum₂]; rw [sub_mul]; rw [← pow_add]; rw [add_tsub_cancel_of_le hmn]; rw [sub_sub_sub_cancel_right (x ^ n) (x ^ m * y ^ (n - m)) (y ^ n)]

/--
lemma `Commute.geom_sum₂_succ_eq` / 引理 `Commute.geom_sum₂_succ_eq`

English:
lemma Commute.geom_sum₂_succ_eq
  given: (h : Commute x y) {n : Nat}
  proof: by
  simp_rw [mul_sum, sum_range_succ_comm, tsub_self, pow_zero, mul_one, add_right_inj, ← mul_assoc,
    (h.symm.pow_right _).eq, mul_assoc, ← pow_succ']
  refine sum_congr rfl fun i hi => ?_
  suffices n - 1 - i + 1 = n - i by rw [this]
  rw [Finset.mem_range] at hi
  lia

中文:
引理 Commute.geom_sum₂_succ_eq
  条件: (h : Commute x y) {n : 自然数}
  证明: by
  simp_rw [mul_sum, sum_range_succ_comm, tsub_self, pow_zero, mul_one, add_right_inj, ← mul_assoc,
    (h.symm.pow_right _).eq, mul_assoc, ← pow_succ']
  refine sum_congr rfl fun i hi => ?_
  suffices n - 1 - i + 1 = n - i by rw [this]
  rw [Finset.mem_range] at hi
  lia
-/
protected lemma Commute.geom_sum₂_succ_eq (h : Commute x y) {n : Nat} :
    ∑ i in range (n + 1), x ^ i * y ^ (n - i) =
      x ^ n + y * ∑ i in range n, x ^ i * y ^ (n - 1 - i) := by
  simp_rw [mul_sum, sum_range_succ_comm, tsub_self, pow_zero, mul_one, add_right_inj, ← mul_assoc,
    (h.symm.pow_right _).eq, mul_assoc, ← pow_succ']
  refine sum_congr rfl fun i hi => ?_
  suffices n - 1 - i + 1 = n - i by rw [this]
  rw [Finset.mem_range] at hi
  lia

/--
lemma `Commute.geom_sum₂_Ico_mul` / 引理 `Commute.geom_sum₂_Ico_mul`

English:
lemma Commute.geom_sum₂_Ico_mul
  statement: (h : Commute x y) {m n : Nat}
  proof: by
  apply op_injective
  simp only [op_sub, op_mul, op_pow, op_sum]
  have : (∑ k in Ico m n, MulOpposite.op y ^ (n - 1 - k) * MulOpposite.op x ^ k) =
      ∑ k in Ico m n, MulOpposite.op x ^ k * MulOpposite.op y ^ (n - 1 - k) := by
    refine sum_congr rfl fun k _ => ?_
    have hp := Commute.pow_

中文:
引理 Commute.geom_sum₂_Ico_mul
  结论: (h : Commute x y) {m n : 自然数}
  证明: by
  apply op_injective
  simp only [op_sub, op_mul, op_pow, op_sum]
  have : (∑ k in Ico m n, MulOpposite.op y ^ (n - 1 - k) * MulOpposite.op x ^ k) =
      ∑ k in Ico m n, MulOpposite.op x ^ k * MulOpposite.op y ^ (n - 1 - k) := by
    refine sum_congr rfl fun k _ => ?_
    have hp := Commute.pow_
-/
protected lemma Commute.geom_sum₂_Ico_mul (h : Commute x y) {m n : Nat}
    (hmn : m <= n) :
    (∑ i in Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ (n - m) * x ^ m := by
  apply op_injective
  simp only [op_sub, op_mul, op_pow, op_sum]
  have : (∑ k in Ico m n, MulOpposite.op y ^ (n - 1 - k) * MulOpposite.op x ^ k) =
      ∑ k in Ico m n, MulOpposite.op x ^ k * MulOpposite.op y ^ (n - 1 - k) := by
    refine sum_congr rfl fun k _ => ?_
    have hp := Commute.pow_pow (Commute.op h.symm) (n - 1 - k) k
    simpa [Commute, SemiconjBy] using hp
  simp only [this]
  convert! (Commute.op h).mul_geom_sum₂_Ico hmn

/--
lemma `geom_sum_Ico_mul` / 引理 `geom_sum_Ico_mul`

English:
lemma geom_sum_Ico_mul
  given: (x : R) {m n : Nat} (hmn : m <= n)
  proof: by
  rw [sum_Ico_eq_sub _ hmn]; rw [sub_mul]; rw [geom_sum_mul]; rw [geom_sum_mul]; rw [sub_sub_sub_cancel_right]

中文:
引理 geom_sum_Ico_mul
  条件: (x : R) {m n : 自然数} (hmn : m <= n)
  证明: by
  rw [sum_Ico_eq_sub _ hmn]; rw [sub_mul]; rw [geom_sum_mul]; rw [geom_sum_mul]; rw [sub_sub_sub_cancel_right]

Depends on / 依赖: geom_sum_mul, sub_mul, sub_sub_sub_cancel_right, sum_Ico_eq_sub
-/
lemma geom_sum_Ico_mul (x : R) {m n : Nat} (hmn : m <= n) :
    (∑ i in Finset.Ico m n, x ^ i) * (x - 1) = x ^ n - x ^ m := by
  rw [sum_Ico_eq_sub _ hmn]; rw [sub_mul]; rw [geom_sum_mul]; rw [geom_sum_mul]; rw [sub_sub_sub_cancel_right]

/--
lemma `geom_sum_Ico_mul_neg` / 引理 `geom_sum_Ico_mul_neg`

English:
lemma geom_sum_Ico_mul_neg
  given: (x : R) {m n : Nat} (hmn : m <= n)
  proof: by
  rw [sum_Ico_eq_sub _ hmn]; rw [sub_mul]; rw [geom_sum_mul_neg]; rw [geom_sum_mul_neg]; rw [sub_sub_sub_cancel_left]

中文:
引理 geom_sum_Ico_mul_neg
  条件: (x : R) {m n : 自然数} (hmn : m <= n)
  证明: by
  rw [sum_Ico_eq_sub _ hmn]; rw [sub_mul]; rw [geom_sum_mul_neg]; rw [geom_sum_mul_neg]; rw [sub_sub_sub_cancel_left]

Depends on / 依赖: geom_sum_mul_neg, sub_mul, sub_sub_sub_cancel_left, sum_Ico_eq_sub
-/
lemma geom_sum_Ico_mul_neg (x : R) {m n : Nat} (hmn : m <= n) :
    (∑ i in Finset.Ico m n, x ^ i) * (1 - x) = x ^ m - x ^ n := by
  rw [sum_Ico_eq_sub _ hmn]; rw [sub_mul]; rw [geom_sum_mul_neg]; rw [geom_sum_mul_neg]; rw [sub_sub_sub_cancel_left]

end Ring

section CommRing
variable [CommRing R]

/--
theorem `pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum` / 定理 `pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum`

English:
theorem pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum
  given: {x : R} {m n : Nat}
  proof: by
  grind [geom_sum_mul]

中文:
定理 pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum
  条件: {x : R} {m n : 自然数}
  证明: by
  grind [geom_sum_mul]

Depends on / 依赖: geom_sum_mul
-/
theorem pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum {x : R} {m n : Nat} :
    (x ^ m - 1) * ∑ k in range n, x ^ k = (x ^ n - 1) * ∑ k in range m, x ^ k := by
  grind [geom_sum_mul]

/--
lemma `geom_sum₂_mul` / 引理 `geom_sum₂_mul`

English:
lemma geom_sum₂_mul
  given: (x y : R) (n : Nat)
  proof: (Commute.all x y).geom_sum₂_mul n

中文:
引理 geom_sum₂_mul
  条件: (x y : R) (n : 自然数)
  证明: (Commute.all x y).geom_sum₂_mul n

Depends on / 依赖: Commute, Commute.all
-/
lemma geom_sum₂_mul (x y : R) (n : Nat) :
    (∑ i in range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n :=
  (Commute.all x y).geom_sum₂_mul n

/--
lemma `sub_dvd_pow_sub_pow` / 引理 `sub_dvd_pow_sub_pow`

English:
lemma sub_dvd_pow_sub_pow
  given: (x y : R) (n : Nat)
  statement: x - y ∣ x ^ n - y ^ n
  proof: (Commute.all x y).sub_dvd_pow_sub_pow n

中文:
引理 sub_dvd_pow_sub_pow
  条件: (x y : R) (n : 自然数)
  结论: x - y ∣ x ^ n - y ^ n
  证明: (Commute.all x y).sub_dvd_pow_sub_pow n

Depends on / 依赖: Commute, Commute.all, sub_dvd_pow_sub_pow
-/
lemma sub_dvd_pow_sub_pow (x y : R) (n : Nat) : x - y ∣ x ^ n - y ^ n :=
  (Commute.all x y).sub_dvd_pow_sub_pow n

/--
lemma `Odd.add_dvd_pow_add_pow` / 引理 `Odd.add_dvd_pow_add_pow`

English:
lemma Odd.add_dvd_pow_add_pow
  given: (x y : R) {n : Nat} (h : Odd n)
  statement: x + y ∣ x ^ n + y ^ n
  proof: by
  have h₁ := geom_sum₂_mul x (-y) n
  rw [Odd.neg_pow h y]; rw [sub_neg_eq_add]; rw [sub_neg_eq_add] at h₁
  exact Dvd.intro_left _ h₁

中文:
引理 Odd.add_dvd_pow_add_pow
  条件: (x y : R) {n : 自然数} (h : Odd n)
  结论: x + y ∣ x ^ n + y ^ n
  证明: by
  have h₁ := geom_sum₂_mul x (-y) n
  rw [Odd.neg_pow h y]; rw [sub_neg_eq_add]; rw [sub_neg_eq_add] at h₁
  exact Dvd.intro_left _ h₁

Depends on / 依赖: Dvd.intro_left, Odd.neg_pow, intro_left, neg_pow, sub_neg_eq_add
-/
lemma Odd.add_dvd_pow_add_pow (x y : R) {n : Nat} (h : Odd n) : x + y ∣ x ^ n + y ^ n := by
  have h₁ := geom_sum₂_mul x (-y) n
  rw [Odd.neg_pow h y]; rw [sub_neg_eq_add]; rw [sub_neg_eq_add] at h₁
  exact Dvd.intro_left _ h₁

/--
lemma `geom_sum₂_succ_eq` / 引理 `geom_sum₂_succ_eq`

English:
lemma geom_sum₂_succ_eq
  given: (x y : R) {n : Nat}
  proof: (Commute.all x y).geom_sum₂_succ_eq

中文:
引理 geom_sum₂_succ_eq
  条件: (x y : R) {n : 自然数}
  证明: (Commute.all x y).geom_sum₂_succ_eq

Depends on / 依赖: Commute, Commute.all
-/
lemma geom_sum₂_succ_eq (x y : R) {n : Nat} :
    ∑ i in range (n + 1), x ^ i * y ^ (n - i) = x ^ n + y * ∑ i in range n, x ^ i * y ^ (n - 1 - i) :=
  (Commute.all x y).geom_sum₂_succ_eq

/--
lemma `mul_geom_sum₂_Ico` / 引理 `mul_geom_sum₂_Ico`

English:
lemma mul_geom_sum₂_Ico
  given: (x y : R) {m n : Nat} (hmn : m <= n)
  proof: (Commute.all x y).mul_geom_sum₂_Ico hmn

中文:
引理 mul_geom_sum₂_Ico
  条件: (x y : R) {m n : 自然数} (hmn : m <= n)
  证明: (Commute.all x y).mul_geom_sum₂_Ico hmn

Depends on / 依赖: Commute, Commute.all
-/
lemma mul_geom_sum₂_Ico (x y : R) {m n : Nat} (hmn : m <= n) :
    ((x - y) * ∑ i in Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) :=
  (Commute.all x y).mul_geom_sum₂_Ico hmn

end CommRing

namespace Nat
variable {m k : Nat} (x y n : Nat)

/--
lemma `sub_dvd_pow_sub_pow` / 引理 `sub_dvd_pow_sub_pow`

English:
lemma sub_dvd_pow_sub_pow
  statement: x - y ∣ x ^ n - y ^ n
  proof: by
  rcases le_or_gt y x with h | h
  · have : y ^ n <= x ^ n := Nat.pow_le_pow_left h _
    exact mod_cast sub_dvd_pow_sub_pow (x : Int) (↑y) n
  · have : x ^ n <= y ^ n := Nat.pow_le_pow_left h.le _
    exact (Nat.sub_eq_zero_of_le this).symm ▸ dvd_zero (x - y)

中文:
引理 sub_dvd_pow_sub_pow
  结论: x - y ∣ x ^ n - y ^ n
  证明: by
  rcases le_or_gt y x with h | h
  · have : y ^ n <= x ^ n := Nat.pow_le_pow_left h _
    exact mod_cast sub_dvd_pow_sub_pow (x : Int) (↑y) n
  · have : x ^ n <= y ^ n := Nat.pow_le_pow_left h.le _
    exact (Nat.sub_eq_zero_of_le this).symm ▸ dvd_zero (x - y)
-/
protected lemma sub_dvd_pow_sub_pow : x - y ∣ x ^ n - y ^ n := by
  rcases le_or_gt y x with h | h
  · have : y ^ n <= x ^ n := Nat.pow_le_pow_left h _
    exact mod_cast sub_dvd_pow_sub_pow (x : Int) (↑y) n
  · have : x ^ n <= y ^ n := Nat.pow_le_pow_left h.le _
    exact (Nat.sub_eq_zero_of_le this).symm ▸ dvd_zero (x - y)

/--
lemma `sub_one_dvd_pow_sub_one` / 引理 `sub_one_dvd_pow_sub_one`

English:
lemma sub_one_dvd_pow_sub_one
  statement: x - 1 ∣ x ^ n - 1
  proof: by
  simpa using x.sub_dvd_pow_sub_pow 1 n

中文:
引理 sub_one_dvd_pow_sub_one
  结论: x - 1 ∣ x ^ n - 1
  证明: by
  simpa using x.sub_dvd_pow_sub_pow 1 n

Depends on / 依赖: sub_dvd_pow_sub_pow, x.sub_dvd_pow_sub_pow
-/
lemma sub_one_dvd_pow_sub_one : x - 1 ∣ x ^ n - 1 := by
  simpa using x.sub_dvd_pow_sub_pow 1 n

/--
lemma `pow_sub_pow_dvd_pow_sub_pow` / 引理 `pow_sub_pow_dvd_pow_sub_pow`

English:
lemma pow_sub_pow_dvd_pow_sub_pow
  given: (hmk : m ∣ k)
  statement: x ^ m - y ^ m ∣ x ^ k - y ^ k
  proof: by
  obtain ⟨n, rfl⟩ := hmk; simpa [pow_mul] using (x ^ m).sub_dvd_pow_sub_pow (y ^ m) n

中文:
引理 pow_sub_pow_dvd_pow_sub_pow
  条件: (hmk : m ∣ k)
  结论: x ^ m - y ^ m ∣ x ^ k - y ^ k
  证明: by
  obtain ⟨n, rfl⟩ := hmk; simpa [pow_mul] using (x ^ m).sub_dvd_pow_sub_pow (y ^ m) n

Depends on / 依赖: pow_mul, sub_dvd_pow_sub_pow
-/
lemma pow_sub_pow_dvd_pow_sub_pow (hmk : m ∣ k) : x ^ m - y ^ m ∣ x ^ k - y ^ k := by
  obtain ⟨n, rfl⟩ := hmk; simpa [pow_mul] using (x ^ m).sub_dvd_pow_sub_pow (y ^ m) n

/--
lemma `pow_sub_one_dvd_pow_sub_one` / 引理 `pow_sub_one_dvd_pow_sub_one`

English:
lemma pow_sub_one_dvd_pow_sub_one
  given: (hmk : m ∣ k)
  statement: x ^ m - 1 ∣ x ^ k - 1
  proof: by
  simpa using pow_sub_pow_dvd_pow_sub_pow x 1 hmk

中文:
引理 pow_sub_one_dvd_pow_sub_one
  条件: (hmk : m ∣ k)
  结论: x ^ m - 1 ∣ x ^ k - 1
  证明: by
  simpa using pow_sub_pow_dvd_pow_sub_pow x 1 hmk

Depends on / 依赖: pow_sub_pow_dvd_pow_sub_pow
-/
lemma pow_sub_one_dvd_pow_sub_one (hmk : m ∣ k) : x ^ m - 1 ∣ x ^ k - 1 := by
  simpa using pow_sub_pow_dvd_pow_sub_pow x 1 hmk

/--
lemma `_root_.Odd.nat_add_dvd_pow_add_pow` / 引理 `_root_.Odd.nat_add_dvd_pow_add_pow`

English:
lemma _root_.Odd.nat_add_dvd_pow_add_pow
  given: {n : Nat} (h : Odd n)
  statement: x + y ∣ x ^ n + y ^ n
  proof: mod_cast Odd.add_dvd_pow_add_pow (x : Int) (↑y) h

中文:
引理 _root_.Odd.nat_add_dvd_pow_add_pow
  条件: {n : 自然数} (h : Odd n)
  结论: x + y ∣ x ^ n + y ^ n
  证明: mod_cast Odd.add_dvd_pow_add_pow (x : Int) (↑y) h

Depends on / 依赖: Odd.add_dvd_pow_add_pow, add_dvd_pow_add_pow, mod_cast
-/
lemma _root_.Odd.nat_add_dvd_pow_add_pow {n : Nat} (h : Odd n) : x + y ∣ x ^ n + y ^ n :=
  mod_cast Odd.add_dvd_pow_add_pow (x : Int) (↑y) h

/--
lemma `geomSum_eq` / 引理 `geomSum_eq`

English:
lemma geomSum_eq
  given: (hm : 2 <= m) (n : Nat)
  statement: ∑ k in range n, m ^ k = (m ^ n - 1) / (m - 1)
  proof: by
  refine (Nat.div_eq_of_eq_mul_left (tsub_pos_iff_lt.2 hm) <| tsub_eq_of_eq_add ?_).symm
  simpa only [tsub_add_cancel_of_le (by lia : 1 <= m), eq_comm] using geom_sum_mul_add (m - 1) n

中文:
引理 geomSum_eq
  条件: (hm : 2 <= m) (n : 自然数)
  结论: ∑ k in range n, m ^ k = (m ^ n - 1) / (m - 1)
  证明: by
  refine (Nat.div_eq_of_eq_mul_left (tsub_pos_iff_lt.2 hm) <| tsub_eq_of_eq_add ?_).symm
  simpa only [tsub_add_cancel_of_le (by lia : 1 <= m), eq_comm] using geom_sum_mul_add (m - 1) n

Depends on / 依赖: Nat.div_eq_of_eq_mul_left, div_eq_of_eq_mul_left, eq_comm, geom_sum_mul_add, tsub_add_cancel_of_le, tsub_eq_of_eq_add, tsub_pos_iff_lt
-/
lemma geomSum_eq (hm : 2 <= m) (n : Nat) : ∑ k in range n, m ^ k = (m ^ n - 1) / (m - 1) := by
  refine (Nat.div_eq_of_eq_mul_left (tsub_pos_iff_lt.2 hm) <| tsub_eq_of_eq_add ?_).symm
  simpa only [tsub_add_cancel_of_le (by lia : 1 <= m), eq_comm] using geom_sum_mul_add (m - 1) n

end Nat
