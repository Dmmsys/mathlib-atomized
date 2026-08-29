/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.Transcendental.Liouville.Basic
public import Mathlib.Topology.Instances.Irrational

/-!
# Liouville numbers with a given exponent

We say that a real number `x` is a Liouville number with exponent `p : ℝ` if there exists a real
number `C` such that for infinitely many denominators `n` there exists a numerator `m` such that
`x ≠ m / n` and `|x - m / n| < C / n ^ p`. A number is a Liouville number in the sense of
`Liouville` if it is `LiouvilleWith` any real exponent, see `forall_liouvilleWith_iff`.

* If `p ≤ 1`, then this condition is trivial.

* If `1 < p ≤ 2`, then this condition is equivalent to `Irrational x`. The forward implication
  does not require `p ≤ 2` and is formalized as `LiouvilleWith.irrational`; the other implication
  follows from approximations by continued fractions and is not formalized yet.

* If `p > 2`, then this is a non-trivial condition on irrational numbers. In particular,
  [Thue–Siegel–Roth theorem](https://en.wikipedia.org/wiki/Roth's_theorem) states that such numbers
  must be transcendental.

In this file we define the predicate `LiouvilleWith` and prove some basic facts about this
predicate.

## Tags

Liouville number, irrational, irrationality exponent
-/

@[expose] public section


open Filter Metric Real Set

open scoped Filter Topology

/--
Definition of `LiouvilleWith` / `LiouvilleWith` 的定义

English:
definition LiouvilleWith
  signature: (p x : Real)
  body: exists C, existsᶠ n : Nat in atTop, exists m : Int, x != m / n ∧ |x - m / n| < C / n ^ p

中文:
定义 LiouvilleWith
  签名: (p x : 实数)
  定义体: exists C, existsᶠ n : Nat in atTop, exists m : Int, x != m / n ∧ |x - m / n| < C / n ^ p
-/
def LiouvilleWith (p x : Real) : Prop :=
  exists C, existsᶠ n : Nat in atTop, exists m : Int, x != m / n ∧ |x - m / n| < C / n ^ p

/--
theorem `liouvilleWith_one` / 定理 `liouvilleWith_one`

English:
theorem liouvilleWith_one
  given: (x : Real)
  statement: LiouvilleWith 1 x
  proof: by
  use 2
  refine ((eventually_gt_atTop 0).mono fun n hn => ?_).frequently
  have hn' : (0 : Real) < n := by simpa
  have : x < ↑(⌊x * ↑n⌋ + 1) / ↑n := by
    rw [lt_div_iff₀ hn']; rw [Int.cast_add]; rw [Int.cast_one]
    exact Int.lt_floor_add_one _
  refine ⟨⌊x * n⌋ + 1, this.ne, ?_⟩
  rw [abs_s

中文:
定理 liouvilleWith_one
  条件: (x : 实数)
  结论: LiouvilleWith 1 x
  证明: by
  use 2
  refine ((eventually_gt_atTop 0).mono fun n hn => ?_).frequently
  have hn' : (0 : Real) < n := by simpa
  have : x < ↑(⌊x * ↑n⌋ + 1) / ↑n := by
    rw [lt_div_iff₀ hn']; rw [Int.cast_add]; rw [Int.cast_one]
    exact Int.lt_floor_add_one _
  refine ⟨⌊x * n⌋ + 1, this.ne, ?_⟩
  rw [abs_s

Depends on / 依赖: Int.cast_add, Int.cast_one, Int.floor_le, Int.lt_floor_add_one, abs_of_pos, abs_sub_comm, add_div_eq_mul_add_div, cast_add, cast_one, eventually_gt_atTop, floor_le, frequently, lt_floor_add_one, rpow_one, sub_lt_iff_lt_add, sub_pos, this.ne
-/
theorem liouvilleWith_one (x : Real) : LiouvilleWith 1 x := by
  use 2
  refine ((eventually_gt_atTop 0).mono fun n hn => ?_).frequently
  have hn' : (0 : Real) < n := by simpa
  have : x < ↑(⌊x * ↑n⌋ + 1) / ↑n := by
    rw [lt_div_iff₀ hn']; rw [Int.cast_add]; rw [Int.cast_one]
    exact Int.lt_floor_add_one _
  refine ⟨⌊x * n⌋ + 1, this.ne, ?_⟩
  rw [abs_sub_comm]; rw [abs_of_pos (sub_pos.2 this)]; rw [rpow_one]; rw [sub_lt_iff_lt_add']; rw [add_div_eq_mul_add_div _ _ hn'.ne']
  gcongr
  calc _ <= x * n + 1 := by push_cast; gcongr; apply Int.floor_le
    _ < x * n + 2 := by linarith

namespace LiouvilleWith

variable {p q x : Real} {r : Rat} {m : Int} {n : Nat}

/--
theorem `exists_pos` / 定理 `exists_pos`

English:
theorem exists_pos
  given: (h : LiouvilleWith p x)
  proof: by
  rcases h with ⟨C, hC⟩
refine ⟨max C 1, zero_lt_one.trans_le le_max_right _ _, ?_⟩
  refine ((eventually_ge_atTop 1).and_frequently hC).mono ?_
  rintro n ⟨hle, m, hne, hlt⟩
  refine ⟨hle, m, hne, hlt.trans_le ?_⟩
  gcongr
  apply le_max_left

中文:
定理 exists_pos
  条件: (h : LiouvilleWith p x)
  证明: by
  rcases h with ⟨C, hC⟩
refine ⟨max C 1, zero_lt_one.trans_le le_max_right _ _, ?_⟩
  refine ((eventually_ge_atTop 1).and_frequently hC).mono ?_
  rintro n ⟨hle, m, hne, hlt⟩
  refine ⟨hle, m, hne, hlt.trans_le ?_⟩
  gcongr
  apply le_max_left

Depends on / 依赖: and_frequently, eventually_ge_atTop, hlt.trans_le, le_max_left, le_max_right, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem exists_pos (h : LiouvilleWith p x) :
    exists (C : Real) (_h₀ : 0 < C),
      existsᶠ n : Nat in atTop, 1 <= n ∧ exists m : Int, x != m / n ∧ |x - m / n| < C / n ^ p := by
  rcases h with ⟨C, hC⟩
refine ⟨max C 1, zero_lt_one.trans_le le_max_right _ _, ?_⟩
  refine ((eventually_ge_atTop 1).and_frequently hC).mono ?_
  rintro n ⟨hle, m, hne, hlt⟩
  refine ⟨hle, m, hne, hlt.trans_le ?_⟩
  gcongr
  apply le_max_left

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (h : LiouvilleWith p x) (hle : q <= p)
  statement: LiouvilleWith q x
  proof: by
  rcases h.exists_pos with ⟨C, hC₀, hC⟩
  refine ⟨C, hC.mono ?_⟩; rintro n ⟨hn, m, hne, hlt⟩
refine ⟨m, hne, hlt.trans_le ?_⟩
  gcongr
  exact_mod_cast hn

中文:
定理 mono
  条件: (h : LiouvilleWith p x) (hle : q <= p)
  结论: LiouvilleWith q x
  证明: by
  rcases h.exists_pos with ⟨C, hC₀, hC⟩
  refine ⟨C, hC.mono ?_⟩; rintro n ⟨hn, m, hne, hlt⟩
refine ⟨m, hne, hlt.trans_le ?_⟩
  gcongr
  exact_mod_cast hn

Depends on / 依赖: exists_pos, h.exists_pos, hC.mono, hlt.trans_le, trans_le
-/
theorem mono (h : LiouvilleWith p x) (hle : q <= p) : LiouvilleWith q x := by
  rcases h.exists_pos with ⟨C, hC₀, hC⟩
  refine ⟨C, hC.mono ?_⟩; rintro n ⟨hn, m, hne, hlt⟩
refine ⟨m, hne, hlt.trans_le ?_⟩
  gcongr
  exact_mod_cast hn

/--
theorem `frequently_lt_rpow_neg` / 定理 `frequently_lt_rpow_neg`

English:
theorem frequently_lt_rpow_neg
  given: (h : LiouvilleWith p x) (hlt : q < p)
  proof: by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  have : forallᶠ n : Nat in atTop, C < n ^ (p - q) := by
    simpa only [(· ∘ ·), neg_sub, one_div] using
      ((tendsto_rpow_atTop (sub_pos.2 hlt)).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop C)
  refine (this.and_frequently

中文:
定理 frequently_lt_rpow_neg
  条件: (h : LiouvilleWith p x) (hlt : q < p)
  证明: by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  have : forallᶠ n : Nat in atTop, C < n ^ (p - q) := by
    simpa only [(· ∘ ·), neg_sub, one_div] using
      ((tendsto_rpow_atTop (sub_pos.2 hlt)).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop C)
  refine (this.and_frequently

Depends on / 依赖: Nat.cast_pos, and_frequently, cast_pos, eventually, eventually_gt_atTop, exists_pos, h.exists_pos, hlt.trans, mul_comm, neg_sub, one_div, replace, rpow_add, rpow_pos_of_pos, sub_eq_add_neg, sub_pos, tendsto_natCast_atTop_atTop, tendsto_rpow_atTop, this.and_frequently
-/
theorem frequently_lt_rpow_neg (h : LiouvilleWith p x) (hlt : q < p) :
    existsᶠ n : Nat in atTop, exists m : Int, x != m / n ∧ |x - m / n| < n ^ (-q) := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  have : forallᶠ n : Nat in atTop, C < n ^ (p - q) := by
    simpa only [(· ∘ ·), neg_sub, one_div] using
      ((tendsto_rpow_atTop (sub_pos.2 hlt)).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop C)
  refine (this.and_frequently hC).mono ?_
  rintro n ⟨hnC, hn, m, hne, hlt⟩
  replace hn : (0 : Real) < n := Nat.cast_pos.2 hn
refine ⟨m, hne, hlt.trans (div_lt_iff₀ <| rpow_pos_of_pos hn _).2 ?_⟩
  rwa [mul_comm, ← rpow_add hn, ← sub_eq_add_neg]

/--
theorem `mul_rat` / 定理 `mul_rat`

English:
theorem mul_rat
  given: (h : LiouvilleWith p x) (hr : r != 0)
  statement: LiouvilleWith p (x * r)
  proof: by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  refine ⟨r.den ^ p * (|r| * C), (tendsto_id.nsmul_atTop r.pos).frequently (hC.mono ?_)⟩
  rintro n ⟨_hn, m, hne, hlt⟩
  have A : (↑(r.num * m) : Real) / ↑(r.den • id n) = m / n * r := by
    simp [← div_mul_div_comm, ← r.cast_def, mul_comm]
  refine ⟨r.nu

中文:
定理 mul_rat
  条件: (h : LiouvilleWith p x) (hr : r != 0)
  结论: LiouvilleWith p (x * r)
  证明: by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  refine ⟨r.den ^ p * (|r| * C), (tendsto_id.nsmul_atTop r.pos).frequently (hC.mono ?_)⟩
  rintro n ⟨_hn, m, hne, hlt⟩
  have A : (↑(r.num * m) : Real) / ↑(r.den • id n) = m / n * r := by
    simp [← div_mul_div_comm, ← r.cast_def, mul_comm]
  refine ⟨r.nu

Depends on / 依赖: Nat.cast_mul, abs_mul, cast_def, cast_mul, div_mul_div_comm, exists_pos, frequently, h.exists_pos, hC.mono, mul_comm, mul_r, nsmul_atTop, r.cast_def, r.den, r.num, r.pos, smul_eq_mul, sub_mul, tendsto_id, tendsto_id.nsmul_atTop
-/
theorem mul_rat (h : LiouvilleWith p x) (hr : r != 0) : LiouvilleWith p (x * r) := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  refine ⟨r.den ^ p * (|r| * C), (tendsto_id.nsmul_atTop r.pos).frequently (hC.mono ?_)⟩
  rintro n ⟨_hn, m, hne, hlt⟩
  have A : (↑(r.num * m) : Real) / ↑(r.den • id n) = m / n * r := by
    simp [← div_mul_div_comm, ← r.cast_def, mul_comm]
  refine ⟨r.num * m, ?_, ?_⟩
  · rw [A]; simp [hne, hr]
  · rw [A, ← sub_mul, abs_mul]
    simp only [smul_eq_mul, id, Nat.cast_mul]
    calc _ < C / ↑n ^ p * |↑r| := by gcongr
      _ = ↑r.den ^ p * (↑|r| * C) / (↑r.den * ↑n) ^ p := ?_
    rw [mul_rpow]; rw [mul_div_mul_left]; rw [mul_comm]; rw [mul_div_assoc]
    · simp only [Rat.cast_abs]
    all_goals positivity

/--
theorem `mul_rat_iff` / 定理 `mul_rat_iff`

English:
theorem mul_rat_iff
  given: (hr : r != 0)
  statement: LiouvilleWith p (x * r) ↔ LiouvilleWith p x
  proof: ⟨fun h => by
    simpa only [mul_assoc, ← Rat.cast_mul, mul_inv_cancel₀ hr, Rat.cast_one, mul_one] using
      h.mul_rat (inv_ne_zero hr),
    fun h => h.mul_rat hr⟩

中文:
定理 mul_rat_iff
  条件: (hr : r != 0)
  结论: LiouvilleWith p (x * r) ↔ LiouvilleWith p x
  证明: ⟨fun h => by
    simpa only [mul_assoc, ← Rat.cast_mul, mul_inv_cancel₀ hr, Rat.cast_one, mul_one] using
      h.mul_rat (inv_ne_zero hr),
    fun h => h.mul_rat hr⟩

Depends on / 依赖: Rat.cast_mul, Rat.cast_one, cast_mul, cast_one, h.mul_rat, inv_ne_zero, mul_assoc, mul_one, mul_rat
-/
theorem mul_rat_iff (hr : r != 0) : LiouvilleWith p (x * r) ↔ LiouvilleWith p x :=
  ⟨fun h => by
    simpa only [mul_assoc, ← Rat.cast_mul, mul_inv_cancel₀ hr, Rat.cast_one, mul_one] using
      h.mul_rat (inv_ne_zero hr),
    fun h => h.mul_rat hr⟩

/--
theorem `rat_mul_iff` / 定理 `rat_mul_iff`

English:
theorem rat_mul_iff
  given: (hr : r != 0)
  statement: LiouvilleWith p (r * x) ↔ LiouvilleWith p x
  proof: by
  rw [mul_comm]; rw [mul_rat_iff hr]

中文:
定理 rat_mul_iff
  条件: (hr : r != 0)
  结论: LiouvilleWith p (r * x) ↔ LiouvilleWith p x
  证明: by
  rw [mul_comm]; rw [mul_rat_iff hr]

Depends on / 依赖: mul_comm, mul_rat_iff
-/
theorem rat_mul_iff (hr : r != 0) : LiouvilleWith p (r * x) ↔ LiouvilleWith p x := by
  rw [mul_comm]; rw [mul_rat_iff hr]

/--
theorem `rat_mul` / 定理 `rat_mul`

English:
theorem rat_mul
  given: (h : LiouvilleWith p x) (hr : r != 0)
  statement: LiouvilleWith p (r * x)
  proof: (rat_mul_iff hr).2 h

中文:
定理 rat_mul
  条件: (h : LiouvilleWith p x) (hr : r != 0)
  结论: LiouvilleWith p (r * x)
  证明: (rat_mul_iff hr).2 h

Depends on / 依赖: rat_mul_iff
-/
theorem rat_mul (h : LiouvilleWith p x) (hr : r != 0) : LiouvilleWith p (r * x) :=
  (rat_mul_iff hr).2 h

/--
theorem `mul_int_iff` / 定理 `mul_int_iff`

English:
theorem mul_int_iff
  given: (hm : m != 0)
  statement: LiouvilleWith p (x * m) ↔ LiouvilleWith p x
  proof: by
  rw [← Rat.cast_intCast]; rw [mul_rat_iff (Int.cast_ne_zero.2 hm)]

中文:
定理 mul_int_iff
  条件: (hm : m != 0)
  结论: LiouvilleWith p (x * m) ↔ LiouvilleWith p x
  证明: by
  rw [← Rat.cast_intCast]; rw [mul_rat_iff (Int.cast_ne_zero.2 hm)]

Depends on / 依赖: Int.cast_ne_zero, Rat.cast_intCast, cast_intCast, cast_ne_zero, mul_rat_iff
-/
theorem mul_int_iff (hm : m != 0) : LiouvilleWith p (x * m) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_intCast]; rw [mul_rat_iff (Int.cast_ne_zero.2 hm)]

/--
theorem `mul_int` / 定理 `mul_int`

English:
theorem mul_int
  given: (h : LiouvilleWith p x) (hm : m != 0)
  statement: LiouvilleWith p (x * m)
  proof: (mul_int_iff hm).2 h

中文:
定理 mul_int
  条件: (h : LiouvilleWith p x) (hm : m != 0)
  结论: LiouvilleWith p (x * m)
  证明: (mul_int_iff hm).2 h

Depends on / 依赖: StochHom, comul_mem, infer_instance, mul_int_iff
-/
theorem mul_int (h : LiouvilleWith p x) (hm : m != 0) : LiouvilleWith p (x * m) :=
  (mul_int_iff hm).2 h

/--
theorem `int_mul_iff` / 定理 `int_mul_iff`

English:
theorem int_mul_iff
  given: (hm : m != 0)
  statement: LiouvilleWith p (m * x) ↔ LiouvilleWith p x
  proof: by
  rw [mul_comm]; rw [mul_int_iff hm]

中文:
定理 int_mul_iff
  条件: (hm : m != 0)
  结论: LiouvilleWith p (m * x) ↔ LiouvilleWith p x
  证明: by
  rw [mul_comm]; rw [mul_int_iff hm]

Depends on / 依赖: mul_comm, mul_int_iff
-/
theorem int_mul_iff (hm : m != 0) : LiouvilleWith p (m * x) ↔ LiouvilleWith p x := by
  rw [mul_comm]; rw [mul_int_iff hm]

/--
theorem `int_mul` / 定理 `int_mul`

English:
theorem int_mul
  given: (h : LiouvilleWith p x) (hm : m != 0)
  statement: LiouvilleWith p (m * x)
  proof: (int_mul_iff hm).2 h

中文:
定理 int_mul
  条件: (h : LiouvilleWith p x) (hm : m != 0)
  结论: LiouvilleWith p (m * x)
  证明: (int_mul_iff hm).2 h

Depends on / 依赖: int_mul_iff
-/
theorem int_mul (h : LiouvilleWith p x) (hm : m != 0) : LiouvilleWith p (m * x) :=
  (int_mul_iff hm).2 h

/--
theorem `mul_nat_iff` / 定理 `mul_nat_iff`

English:
theorem mul_nat_iff
  given: (hn : n != 0)
  statement: LiouvilleWith p (x * n) ↔ LiouvilleWith p x
  proof: by
  rw [← Rat.cast_natCast]; rw [mul_rat_iff (Nat.cast_ne_zero.2 hn)]

中文:
定理 mul_nat_iff
  条件: (hn : n != 0)
  结论: LiouvilleWith p (x * n) ↔ LiouvilleWith p x
  证明: by
  rw [← Rat.cast_natCast]; rw [mul_rat_iff (Nat.cast_ne_zero.2 hn)]

Depends on / 依赖: Nat.cast_ne_zero, Rat.cast_natCast, cast_natCast, cast_ne_zero, mul_rat_iff
-/
theorem mul_nat_iff (hn : n != 0) : LiouvilleWith p (x * n) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_natCast]; rw [mul_rat_iff (Nat.cast_ne_zero.2 hn)]

/--
theorem `mul_nat` / 定理 `mul_nat`

English:
theorem mul_nat
  given: (h : LiouvilleWith p x) (hn : n != 0)
  statement: LiouvilleWith p (x * n)
  proof: (mul_nat_iff hn).2 h

中文:
定理 mul_nat
  条件: (h : LiouvilleWith p x) (hn : n != 0)
  结论: LiouvilleWith p (x * n)
  证明: (mul_nat_iff hn).2 h

Depends on / 依赖: mul_nat_iff
-/
theorem mul_nat (h : LiouvilleWith p x) (hn : n != 0) : LiouvilleWith p (x * n) :=
  (mul_nat_iff hn).2 h

/--
theorem `nat_mul_iff` / 定理 `nat_mul_iff`

English:
theorem nat_mul_iff
  given: (hn : n != 0)
  statement: LiouvilleWith p (n * x) ↔ LiouvilleWith p x
  proof: by
  rw [mul_comm]; rw [mul_nat_iff hn]

中文:
定理 nat_mul_iff
  条件: (hn : n != 0)
  结论: LiouvilleWith p (n * x) ↔ LiouvilleWith p x
  证明: by
  rw [mul_comm]; rw [mul_nat_iff hn]

Depends on / 依赖: mul_comm, mul_nat_iff
-/
theorem nat_mul_iff (hn : n != 0) : LiouvilleWith p (n * x) ↔ LiouvilleWith p x := by
  rw [mul_comm]; rw [mul_nat_iff hn]

/--
theorem `nat_mul` / 定理 `nat_mul`

English:
theorem nat_mul
  given: (h : LiouvilleWith p x) (hn : n != 0)
  statement: LiouvilleWith p (n * x)
  proof: by
  rw [mul_comm]; exact h.mul_nat hn

中文:
定理 nat_mul
  条件: (h : LiouvilleWith p x) (hn : n != 0)
  结论: LiouvilleWith p (n * x)
  证明: by
  rw [mul_comm]; exact h.mul_nat hn

Depends on / 依赖: h.mul_nat, mul_comm, mul_nat
-/
theorem nat_mul (h : LiouvilleWith p x) (hn : n != 0) : LiouvilleWith p (n * x) := by
  rw [mul_comm]; exact h.mul_nat hn

/--
theorem `add_rat` / 定理 `add_rat`

English:
theorem add_rat
  given: (h : LiouvilleWith p x) (r : Rat)
  statement: LiouvilleWith p (x + r)
  proof: by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  refine ⟨r.den ^ p * C, (tendsto_id.nsmul_atTop r.pos).frequently (hC.mono ?_)⟩
  rintro n ⟨hn, m, hne, hlt⟩
  have : (↑(r.den * m + r.num * n : Int) / ↑(r.den • id n) : Real) = m / n + r := by
    rw [smul_eq_mul]; rw [id]
    nth_rewrite 4 [← Rat.num_di

中文:
定理 add_rat
  条件: (h : LiouvilleWith p x) (r : Rat)
  结论: LiouvilleWith p (x + r)
  证明: by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  refine ⟨r.den ^ p * C, (tendsto_id.nsmul_atTop r.pos).frequently (hC.mono ?_)⟩
  rintro n ⟨hn, m, hne, hlt⟩
  have : (↑(r.den * m + r.num * n : Int) / ↑(r.den • id n) : Real) = m / n + r := by
    rw [smul_eq_mul]; rw [id]
    nth_rewrite 4 [← Rat.num_di

Depends on / 依赖: Rat.num_div_den, add_div, add_sub_add_right_eq_sub, exists_pos, frequently, h.exists_pos, hC.mono, hlt.tra, mul_div_mul_left, mul_div_mul_right, nsmul_atTop, nth_rewrite, num_div_den, r.den, r.num, r.pos, smul_eq_mul, tendsto_id, tendsto_id.nsmul_atTop
-/
theorem add_rat (h : LiouvilleWith p x) (r : Rat) : LiouvilleWith p (x + r) := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  refine ⟨r.den ^ p * C, (tendsto_id.nsmul_atTop r.pos).frequently (hC.mono ?_)⟩
  rintro n ⟨hn, m, hne, hlt⟩
  have : (↑(r.den * m + r.num * n : Int) / ↑(r.den • id n) : Real) = m / n + r := by
    rw [smul_eq_mul]; rw [id]
    nth_rewrite 4 [← Rat.num_div_den r]
    push_cast
    rw [add_div]; rw [mul_div_mul_left _ _ (by positivity)]; rw [mul_div_mul_right _ _ (by positivity)]
  refine ⟨r.den * m + r.num * n, ?_⟩; rw [this, add_sub_add_right_eq_sub]
  refine ⟨by simpa, hlt.trans_le (le_of_eq ?_)⟩
  have : (r.den ^ p : Real) != 0 := by positivity
  simp [mul_rpow, mul_div_mul_left, this]

@[simp]
/--
theorem `add_rat_iff` / 定理 `add_rat_iff`

English:
theorem add_rat_iff
  statement: LiouvilleWith p (x + r) ↔ LiouvilleWith p x
  proof: ⟨fun h => by simpa using h.add_rat (-r), fun h => h.add_rat r⟩

@[simp]

中文:
定理 add_rat_iff
  结论: LiouvilleWith p (x + r) ↔ LiouvilleWith p x
  证明: ⟨fun h => by simpa using h.add_rat (-r), fun h => h.add_rat r⟩

@[simp]

Depends on / 依赖: add_rat, h.add_rat
-/
theorem add_rat_iff : LiouvilleWith p (x + r) ↔ LiouvilleWith p x :=
  ⟨fun h => by simpa using h.add_rat (-r), fun h => h.add_rat r⟩

@[simp]
/--
theorem `rat_add_iff` / 定理 `rat_add_iff`

English:
theorem rat_add_iff
  statement: LiouvilleWith p (r + x) ↔ LiouvilleWith p x
  proof: by rw [add_comm, add_rat_iff]

中文:
定理 rat_add_iff
  结论: LiouvilleWith p (r + x) ↔ LiouvilleWith p x
  证明: by rw [add_comm, add_rat_iff]

Depends on / 依赖: add_comm, add_rat_iff
-/
theorem rat_add_iff : LiouvilleWith p (r + x) ↔ LiouvilleWith p x := by rw [add_comm, add_rat_iff]

/--
theorem `rat_add` / 定理 `rat_add`

English:
theorem rat_add
  given: (h : LiouvilleWith p x) (r : Rat)
  statement: LiouvilleWith p (r + x)
  proof: add_comm x r ▸ h.add_rat r

@[simp]

中文:
定理 rat_add
  条件: (h : LiouvilleWith p x) (r : Rat)
  结论: LiouvilleWith p (r + x)
  证明: add_comm x r ▸ h.add_rat r

@[simp]

Depends on / 依赖: add_comm, add_rat, h.add_rat
-/
theorem rat_add (h : LiouvilleWith p x) (r : Rat) : LiouvilleWith p (r + x) :=
  add_comm x r ▸ h.add_rat r

@[simp]
/--
theorem `add_int_iff` / 定理 `add_int_iff`

English:
theorem add_int_iff
  statement: LiouvilleWith p (x + m) ↔ LiouvilleWith p x
  proof: by
  rw [← Rat.cast_intCast m]; rw [add_rat_iff]

@[simp]

中文:
定理 add_int_iff
  结论: LiouvilleWith p (x + m) ↔ LiouvilleWith p x
  证明: by
  rw [← Rat.cast_intCast m]; rw [add_rat_iff]

@[simp]

Depends on / 依赖: Rat.cast_intCast, add_rat_iff, cast_intCast
-/
theorem add_int_iff : LiouvilleWith p (x + m) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_intCast m]; rw [add_rat_iff]

@[simp]
/--
theorem `int_add_iff` / 定理 `int_add_iff`

English:
theorem int_add_iff
  statement: LiouvilleWith p (m + x) ↔ LiouvilleWith p x
  proof: by rw [add_comm, add_int_iff]

@[simp]

中文:
定理 int_add_iff
  结论: LiouvilleWith p (m + x) ↔ LiouvilleWith p x
  证明: by rw [add_comm, add_int_iff]

@[simp]

Depends on / 依赖: add_comm, add_int_iff
-/
theorem int_add_iff : LiouvilleWith p (m + x) ↔ LiouvilleWith p x := by rw [add_comm, add_int_iff]

@[simp]
/--
theorem `add_nat_iff` / 定理 `add_nat_iff`

English:
theorem add_nat_iff
  statement: LiouvilleWith p (x + n) ↔ LiouvilleWith p x
  proof: by
  rw [← Rat.cast_natCast n]; rw [add_rat_iff]

@[simp]

中文:
定理 add_nat_iff
  结论: LiouvilleWith p (x + n) ↔ LiouvilleWith p x
  证明: by
  rw [← Rat.cast_natCast n]; rw [add_rat_iff]

@[simp]

Depends on / 依赖: Rat.cast_natCast, add_rat_iff, cast_natCast
-/
theorem add_nat_iff : LiouvilleWith p (x + n) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_natCast n]; rw [add_rat_iff]

@[simp]
/--
theorem `nat_add_iff` / 定理 `nat_add_iff`

English:
theorem nat_add_iff
  statement: LiouvilleWith p (n + x) ↔ LiouvilleWith p x
  proof: by rw [add_comm, add_nat_iff]

中文:
定理 nat_add_iff
  结论: LiouvilleWith p (n + x) ↔ LiouvilleWith p x
  证明: by rw [add_comm, add_nat_iff]

Depends on / 依赖: add_comm, add_nat_iff
-/
theorem nat_add_iff : LiouvilleWith p (n + x) ↔ LiouvilleWith p x := by rw [add_comm, add_nat_iff]

/--
theorem `add_int` / 定理 `add_int`

English:
theorem add_int
  given: (h : LiouvilleWith p x) (m : Int)
  statement: LiouvilleWith p (x + m)
  proof: add_int_iff.2 h

中文:
定理 add_int
  条件: (h : LiouvilleWith p x) (m : 整数)
  结论: LiouvilleWith p (x + m)
  证明: add_int_iff.2 h

Depends on / 依赖: add_int_iff
-/
theorem add_int (h : LiouvilleWith p x) (m : Int) : LiouvilleWith p (x + m) :=
  add_int_iff.2 h

/--
theorem `int_add` / 定理 `int_add`

English:
theorem int_add
  given: (h : LiouvilleWith p x) (m : Int)
  statement: LiouvilleWith p (m + x)
  proof: int_add_iff.2 h

中文:
定理 int_add
  条件: (h : LiouvilleWith p x) (m : 整数)
  结论: LiouvilleWith p (m + x)
  证明: int_add_iff.2 h

Depends on / 依赖: int_add_iff
-/
theorem int_add (h : LiouvilleWith p x) (m : Int) : LiouvilleWith p (m + x) :=
  int_add_iff.2 h

/--
theorem `add_nat` / 定理 `add_nat`

English:
theorem add_nat
  given: (h : LiouvilleWith p x) (n : Nat)
  statement: LiouvilleWith p (x + n)
  proof: h.add_int n

中文:
定理 add_nat
  条件: (h : LiouvilleWith p x) (n : 自然数)
  结论: LiouvilleWith p (x + n)
  证明: h.add_int n

Depends on / 依赖: add_int, h.add_int
-/
theorem add_nat (h : LiouvilleWith p x) (n : Nat) : LiouvilleWith p (x + n) :=
  h.add_int n

/--
theorem `nat_add` / 定理 `nat_add`

English:
theorem nat_add
  given: (h : LiouvilleWith p x) (n : Nat)
  statement: LiouvilleWith p (n + x)
  proof: h.int_add n

中文:
定理 nat_add
  条件: (h : LiouvilleWith p x) (n : 自然数)
  结论: LiouvilleWith p (n + x)
  证明: h.int_add n

Depends on / 依赖: h.int_add, int_add
-/
theorem nat_add (h : LiouvilleWith p x) (n : Nat) : LiouvilleWith p (n + x) :=
  h.int_add n

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (h : LiouvilleWith p x)
  statement: LiouvilleWith p (-x)
  proof: by
  rcases h with ⟨C, hC⟩
  refine ⟨C, hC.mono ?_⟩
  rintro n ⟨m, hne, hlt⟩
  refine ⟨-m, by simp [neg_div, hne], ?_⟩
  convert! hlt using 1
  rw [abs_sub_comm]
  congr! 1; push_cast; ring

@[simp]

中文:
定理 neg
  条件: (h : LiouvilleWith p x)
  结论: LiouvilleWith p (-x)
  证明: by
  rcases h with ⟨C, hC⟩
  refine ⟨C, hC.mono ?_⟩
  rintro n ⟨m, hne, hlt⟩
  refine ⟨-m, by simp [neg_div, hne], ?_⟩
  convert! hlt using 1
  rw [abs_sub_comm]
  congr! 1; push_cast; ring

@[simp]
-/
protected theorem neg (h : LiouvilleWith p x) : LiouvilleWith p (-x) := by
  rcases h with ⟨C, hC⟩
  refine ⟨C, hC.mono ?_⟩
  rintro n ⟨m, hne, hlt⟩
  refine ⟨-m, by simp [neg_div, hne], ?_⟩
  convert! hlt using 1
  rw [abs_sub_comm]
  congr! 1; push_cast; ring

@[simp]
/--
theorem `neg_iff` / 定理 `neg_iff`

English:
theorem neg_iff
  statement: LiouvilleWith p (-x) ↔ LiouvilleWith p x
  proof: ⟨fun h => neg_neg x ▸ h.neg, LiouvilleWith.neg⟩

@[simp]

中文:
定理 neg_iff
  结论: LiouvilleWith p (-x) ↔ LiouvilleWith p x
  证明: ⟨fun h => neg_neg x ▸ h.neg, LiouvilleWith.neg⟩

@[simp]

Depends on / 依赖: LiouvilleWith, LiouvilleWith.neg, h.neg, neg_neg
-/
theorem neg_iff : LiouvilleWith p (-x) ↔ LiouvilleWith p x :=
  ⟨fun h => neg_neg x ▸ h.neg, LiouvilleWith.neg⟩

@[simp]
/--
theorem `sub_rat_iff` / 定理 `sub_rat_iff`

English:
theorem sub_rat_iff
  statement: LiouvilleWith p (x - r) ↔ LiouvilleWith p x
  proof: by
  rw [sub_eq_add_neg]; rw [← Rat.cast_neg]; rw [add_rat_iff]

中文:
定理 sub_rat_iff
  结论: LiouvilleWith p (x - r) ↔ LiouvilleWith p x
  证明: by
  rw [sub_eq_add_neg]; rw [← Rat.cast_neg]; rw [add_rat_iff]

Depends on / 依赖: Rat.cast_neg, add_rat_iff, cast_neg, sub_eq_add_neg
-/
theorem sub_rat_iff : LiouvilleWith p (x - r) ↔ LiouvilleWith p x := by
  rw [sub_eq_add_neg]; rw [← Rat.cast_neg]; rw [add_rat_iff]

/--
theorem `sub_rat` / 定理 `sub_rat`

English:
theorem sub_rat
  given: (h : LiouvilleWith p x) (r : Rat)
  statement: LiouvilleWith p (x - r)
  proof: sub_rat_iff.2 h

@[simp]

中文:
定理 sub_rat
  条件: (h : LiouvilleWith p x) (r : Rat)
  结论: LiouvilleWith p (x - r)
  证明: sub_rat_iff.2 h

@[simp]

Depends on / 依赖: sub_rat_iff
-/
theorem sub_rat (h : LiouvilleWith p x) (r : Rat) : LiouvilleWith p (x - r) :=
  sub_rat_iff.2 h

@[simp]
/--
theorem `sub_int_iff` / 定理 `sub_int_iff`

English:
theorem sub_int_iff
  statement: LiouvilleWith p (x - m) ↔ LiouvilleWith p x
  proof: by
  rw [← Rat.cast_intCast]; rw [sub_rat_iff]

中文:
定理 sub_int_iff
  结论: LiouvilleWith p (x - m) ↔ LiouvilleWith p x
  证明: by
  rw [← Rat.cast_intCast]; rw [sub_rat_iff]

Depends on / 依赖: Rat.cast_intCast, cast_intCast, sub_rat_iff
-/
theorem sub_int_iff : LiouvilleWith p (x - m) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_intCast]; rw [sub_rat_iff]

/--
theorem `sub_int` / 定理 `sub_int`

English:
theorem sub_int
  given: (h : LiouvilleWith p x) (m : Int)
  statement: LiouvilleWith p (x - m)
  proof: sub_int_iff.2 h

@[simp]

中文:
定理 sub_int
  条件: (h : LiouvilleWith p x) (m : 整数)
  结论: LiouvilleWith p (x - m)
  证明: sub_int_iff.2 h

@[simp]

Depends on / 依赖: sub_int_iff
-/
theorem sub_int (h : LiouvilleWith p x) (m : Int) : LiouvilleWith p (x - m) :=
  sub_int_iff.2 h

@[simp]
/--
theorem `sub_nat_iff` / 定理 `sub_nat_iff`

English:
theorem sub_nat_iff
  statement: LiouvilleWith p (x - n) ↔ LiouvilleWith p x
  proof: by
  rw [← Rat.cast_natCast]; rw [sub_rat_iff]

中文:
定理 sub_nat_iff
  结论: LiouvilleWith p (x - n) ↔ LiouvilleWith p x
  证明: by
  rw [← Rat.cast_natCast]; rw [sub_rat_iff]

Depends on / 依赖: Rat.cast_natCast, cast_natCast, sub_rat_iff
-/
theorem sub_nat_iff : LiouvilleWith p (x - n) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_natCast]; rw [sub_rat_iff]

/--
theorem `sub_nat` / 定理 `sub_nat`

English:
theorem sub_nat
  given: (h : LiouvilleWith p x) (n : Nat)
  statement: LiouvilleWith p (x - n)
  proof: sub_nat_iff.2 h

@[simp]

中文:
定理 sub_nat
  条件: (h : LiouvilleWith p x) (n : 自然数)
  结论: LiouvilleWith p (x - n)
  证明: sub_nat_iff.2 h

@[simp]

Depends on / 依赖: sub_nat_iff
-/
theorem sub_nat (h : LiouvilleWith p x) (n : Nat) : LiouvilleWith p (x - n) :=
  sub_nat_iff.2 h

@[simp]
/--
theorem `rat_sub_iff` / 定理 `rat_sub_iff`

English:
theorem rat_sub_iff
  statement: LiouvilleWith p (r - x) ↔ LiouvilleWith p x
  proof: by simp [sub_eq_add_neg]

中文:
定理 rat_sub_iff
  结论: LiouvilleWith p (r - x) ↔ LiouvilleWith p x
  证明: by simp [sub_eq_add_neg]

Depends on / 依赖: sub_eq_add_neg
-/
theorem rat_sub_iff : LiouvilleWith p (r - x) ↔ LiouvilleWith p x := by simp [sub_eq_add_neg]

/--
theorem `rat_sub` / 定理 `rat_sub`

English:
theorem rat_sub
  given: (h : LiouvilleWith p x) (r : Rat)
  statement: LiouvilleWith p (r - x)
  proof: rat_sub_iff.2 h

@[simp]

中文:
定理 rat_sub
  条件: (h : LiouvilleWith p x) (r : Rat)
  结论: LiouvilleWith p (r - x)
  证明: rat_sub_iff.2 h

@[simp]

Depends on / 依赖: rat_sub_iff
-/
theorem rat_sub (h : LiouvilleWith p x) (r : Rat) : LiouvilleWith p (r - x) :=
  rat_sub_iff.2 h

@[simp]
/--
theorem `int_sub_iff` / 定理 `int_sub_iff`

English:
theorem int_sub_iff
  statement: LiouvilleWith p (m - x) ↔ LiouvilleWith p x
  proof: by simp [sub_eq_add_neg]

中文:
定理 int_sub_iff
  结论: LiouvilleWith p (m - x) ↔ LiouvilleWith p x
  证明: by simp [sub_eq_add_neg]

Depends on / 依赖: sub_eq_add_neg
-/
theorem int_sub_iff : LiouvilleWith p (m - x) ↔ LiouvilleWith p x := by simp [sub_eq_add_neg]

/--
theorem `int_sub` / 定理 `int_sub`

English:
theorem int_sub
  given: (h : LiouvilleWith p x) (m : Int)
  statement: LiouvilleWith p (m - x)
  proof: int_sub_iff.2 h

@[simp]

中文:
定理 int_sub
  条件: (h : LiouvilleWith p x) (m : 整数)
  结论: LiouvilleWith p (m - x)
  证明: int_sub_iff.2 h

@[simp]

Depends on / 依赖: int_sub_iff
-/
theorem int_sub (h : LiouvilleWith p x) (m : Int) : LiouvilleWith p (m - x) :=
  int_sub_iff.2 h

@[simp]
/--
theorem `nat_sub_iff` / 定理 `nat_sub_iff`

English:
theorem nat_sub_iff
  statement: LiouvilleWith p (n - x) ↔ LiouvilleWith p x
  proof: by simp [sub_eq_add_neg]

中文:
定理 nat_sub_iff
  结论: LiouvilleWith p (n - x) ↔ LiouvilleWith p x
  证明: by simp [sub_eq_add_neg]

Depends on / 依赖: sub_eq_add_neg
-/
theorem nat_sub_iff : LiouvilleWith p (n - x) ↔ LiouvilleWith p x := by simp [sub_eq_add_neg]

/--
theorem `nat_sub` / 定理 `nat_sub`

English:
theorem nat_sub
  given: (h : LiouvilleWith p x) (n : Nat)
  statement: LiouvilleWith p (n - x)
  proof: nat_sub_iff.2 h

中文:
定理 nat_sub
  条件: (h : LiouvilleWith p x) (n : 自然数)
  结论: LiouvilleWith p (n - x)
  证明: nat_sub_iff.2 h

Depends on / 依赖: nat_sub_iff
-/
theorem nat_sub (h : LiouvilleWith p x) (n : Nat) : LiouvilleWith p (n - x) :=
  nat_sub_iff.2 h

/--
theorem `ne_cast_int` / 定理 `ne_cast_int`

English:
theorem ne_cast_int
  given: (h : LiouvilleWith p x) (hp : 1 < p) (m : Int)
  statement: x != m
  proof: by
  rintro rfl; rename' m => M
  rcases ((eventually_gt_atTop 0).and_frequently (h.frequently_lt_rpow_neg hp)).exists with
    ⟨n : Nat, hn : 0 < n, m : Int, hne : (M : Real) != m / n, hlt : |(M - m / n : Real)| < n ^ (-1 : Real)⟩
  refine hlt.not_ge ?_
  have hn' : (0 : Real) < n := by simpa
  rw 

中文:
定理 ne_cast_int
  条件: (h : LiouvilleWith p x) (hp : 1 < p) (m : 整数)
  结论: x != m
  证明: by
  rintro rfl; rename' m => M
  rcases ((eventually_gt_atTop 0).and_frequently (h.frequently_lt_rpow_neg hp)).exists with
    ⟨n : Nat, hn : 0 < n, m : Int, hne : (M : Real) != m / n, hlt : |(M - m / n : Real)| < n ^ (-1 : Real)⟩
  refine hlt.not_ge ?_
  have hn' : (0 : Real) < n := by simpa
  rw 

Depends on / 依赖: Int.add_one_le_iff, Nat.abs_cast, abs_cast, abs_div, abs_pos, add_one_le_iff, and_frequently, eq_div_iff, eventually_gt_atTop, frequently_lt_rpow_neg, h.frequently_lt_rpow_neg, hlt.not_ge, not_ge, one_div, rpow_neg_one, sub_div, sub_ne_zero, zero_add
-/
theorem ne_cast_int (h : LiouvilleWith p x) (hp : 1 < p) (m : Int) : x != m := by
  rintro rfl; rename' m => M
  rcases ((eventually_gt_atTop 0).and_frequently (h.frequently_lt_rpow_neg hp)).exists with
    ⟨n : Nat, hn : 0 < n, m : Int, hne : (M : Real) != m / n, hlt : |(M - m / n : Real)| < n ^ (-1 : Real)⟩
  refine hlt.not_ge ?_
  have hn' : (0 : Real) < n := by simpa
  rw [rpow_neg_one]; rw [← one_div]; rw [sub_div' hn'.ne']; rw [abs_div]; rw [Nat.abs_cast]
  gcongr
  norm_cast
  rw [← zero_add (1 : Int)]; rw [Int.add_one_le_iff]; rw [abs_pos]; rw [sub_ne_zero]
  rw [Ne]; rw [eq_div_iff hn'.ne'] at hne
  exact mod_cast hne

/--
theorem `irrational` / 定理 `irrational`

English:
theorem irrational
  given: (h : LiouvilleWith p x) (hp : 1 < p)
  statement: Irrational x
  proof: by
  rintro ⟨r, rfl⟩
  rcases eq_or_ne r 0 with (rfl | h0)
  · refine h.ne_cast_int hp 0 ?_; rw [Rat.cast_zero, Int.cast_zero]
  · refine (h.mul_rat (inv_ne_zero h0)).ne_cast_int hp 1 ?_
    rw [Rat.cast_inv]; rw [mul_inv_cancel₀]
    exacts [Int.cast_one.symm, Rat.cast_ne_zero.mpr h0]

中文:
定理 irrational
  条件: (h : LiouvilleWith p x) (hp : 1 < p)
  结论: Irrational x
  证明: by
  rintro ⟨r, rfl⟩
  rcases eq_or_ne r 0 with (rfl | h0)
  · refine h.ne_cast_int hp 0 ?_; rw [Rat.cast_zero, Int.cast_zero]
  · refine (h.mul_rat (inv_ne_zero h0)).ne_cast_int hp 1 ?_
    rw [Rat.cast_inv]; rw [mul_inv_cancel₀]
    exacts [Int.cast_one.symm, Rat.cast_ne_zero.mpr h0]
-/
protected theorem irrational (h : LiouvilleWith p x) (hp : 1 < p) : Irrational x := by
  rintro ⟨r, rfl⟩
  rcases eq_or_ne r 0 with (rfl | h0)
  · refine h.ne_cast_int hp 0 ?_; rw [Rat.cast_zero, Int.cast_zero]
  · refine (h.mul_rat (inv_ne_zero h0)).ne_cast_int hp 1 ?_
    rw [Rat.cast_inv]; rw [mul_inv_cancel₀]
    exacts [Int.cast_one.symm, Rat.cast_ne_zero.mpr h0]

end LiouvilleWith

namespace Liouville

variable {x : Real}

/--
theorem `frequently_exists_num` / 定理 `frequently_exists_num`

English:
theorem frequently_exists_num
  given: (hx : Liouville x) (n : Nat)
  proof: by
  by_contra! H
  simp only [eventually_atTop] at H
  rcases H with ⟨N, hN⟩
  have : forall b > (1 : Nat), forallᶠ m : Nat in atTop, forall a : Int, 1 / (b : Real) ^ m <= |x - a / b| := by
    intro b hb
    replace hb : (1 : Real) < b := Nat.one_lt_cast.2 hb
    have H : Tendsto (fun m => 1 / (b 

中文:
定理 frequently_exists_num
  条件: (hx : Liouville x) (n : 自然数)
  证明: by
  by_contra! H
  simp only [eventually_atTop] at H
  rcases H with ⟨N, hN⟩
  have : forall b > (1 : Nat), forallᶠ m : Nat in atTop, forall a : Int, 1 / (b : Real) ^ m <= |x - a / b| := by
    intro b hb
    replace hb : (1 : Real) < b := Nat.one_lt_cast.2 hb
    have H : Tendsto (fun m => 1 / (b 

Depends on / 依赖: H.eventually, Nat.one_lt_cast, Tendsto, eventually, eventually_atTop, eventually_forall_le_dist_cast_div, hx.irrational.eventually_forall_le_dist_cast_div, irrational, one_div, one_lt_cast, replace, tendsto_inv_atTop_zero, tendsto_inv_atTop_zero.comp, tendsto_pow_atTop_atTop_of_one_lt
-/
theorem frequently_exists_num (hx : Liouville x) (n : Nat) :
    existsᶠ b : Nat in atTop, exists a : Int, x != a / b ∧ |x - a / b| < 1 / (b : Real) ^ n := by
  by_contra! H
  simp only [eventually_atTop] at H
  rcases H with ⟨N, hN⟩
  have : forall b > (1 : Nat), forallᶠ m : Nat in atTop, forall a : Int, 1 / (b : Real) ^ m <= |x - a / b| := by
    intro b hb
    replace hb : (1 : Real) < b := Nat.one_lt_cast.2 hb
    have H : Tendsto (fun m => 1 / (b : Real) ^ m : Nat -> Real) atTop (𝓝 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hb)
    refine (H.eventually (hx.irrational.eventually_forall_le_dist_cast_div b)).mono ?_
    exact fun m hm a => hm a
  have : forallᶠ m : Nat in atTop, forall b < N, 1 < b -> forall a : Int, 1 / (b : Real) ^ m <= |x - a / b| :=
    (finite_lt_nat N).eventually_all.2 fun b _hb => eventually_imp_distrib_left.2 (this b)
  rcases (this.and (eventually_ge_atTop n)).exists with ⟨m, hm, hnm⟩
  rcases hx m with ⟨a, b, hb, hne, hlt⟩
  lift b to Nat using zero_le_one.trans hb.le; norm_cast at hb; push_cast at hne hlt
  rcases le_or_gt N b with h | h
  · refine (hN b h a hne).not_gt (hlt.trans_le ?_)
    gcongr
    exact_mod_cast hb.le
  · exact (hm b h hb _).not_gt hlt

/--
theorem `liouvilleWith` / 定理 `liouvilleWith`

English:
theorem liouvilleWith
  given: (hx : Liouville x) (p : Real)
  statement: LiouvilleWith p x
  proof: by
  suffices LiouvilleWith ⌈p⌉₊ x from this.mono (Nat.le_ceil p)
  refine ⟨1, ((eventually_gt_atTop 1).and_frequently (hx.frequently_exists_num ⌈p⌉₊)).mono ?_⟩
  rintro b ⟨_hb, a, hne, hlt⟩
  refine ⟨a, hne, ?_⟩
  rwa [rpow_natCast]

中文:
定理 liouvilleWith
  条件: (hx : Liouville x) (p : 实数)
  结论: LiouvilleWith p x
  证明: by
  suffices LiouvilleWith ⌈p⌉₊ x from this.mono (Nat.le_ceil p)
  refine ⟨1, ((eventually_gt_atTop 1).and_frequently (hx.frequently_exists_num ⌈p⌉₊)).mono ?_⟩
  rintro b ⟨_hb, a, hne, hlt⟩
  refine ⟨a, hne, ?_⟩
  rwa [rpow_natCast]
-/
protected theorem liouvilleWith (hx : Liouville x) (p : Real) : LiouvilleWith p x := by
  suffices LiouvilleWith ⌈p⌉₊ x from this.mono (Nat.le_ceil p)
  refine ⟨1, ((eventually_gt_atTop 1).and_frequently (hx.frequently_exists_num ⌈p⌉₊)).mono ?_⟩
  rintro b ⟨_hb, a, hne, hlt⟩
  refine ⟨a, hne, ?_⟩
  rwa [rpow_natCast]

end Liouville

/--
theorem `forall_liouvilleWith_iff` / 定理 `forall_liouvilleWith_iff`

English:
theorem forall_liouvilleWith_iff
  given: {x : Real}
  statement: (forall p, LiouvilleWith p x) ↔ Liouville x
  proof: by
  refine ⟨fun H n => ?_, Liouville.liouvilleWith⟩
  rcases ((eventually_gt_atTop 1).and_frequently
    ((H (n + 1)).frequently_lt_rpow_neg (lt_add_one (n : Real)))).exists
    with ⟨b, hb, a, hne, hlt⟩
  exact ⟨a, b, mod_cast hb, hne, by simpa [rpow_neg] using hlt⟩

中文:
定理 forall_liouvilleWith_iff
  条件: {x : 实数}
  结论: (对任意 p, LiouvilleWith p x) ↔ Liouville x
  证明: by
  refine ⟨fun H n => ?_, Liouville.liouvilleWith⟩
  rcases ((eventually_gt_atTop 1).and_frequently
    ((H (n + 1)).frequently_lt_rpow_neg (lt_add_one (n : Real)))).exists
    with ⟨b, hb, a, hne, hlt⟩
  exact ⟨a, b, mod_cast hb, hne, by simpa [rpow_neg] using hlt⟩

Depends on / 依赖: Liouville, Liouville.liouvilleWith, and_frequently, eventually_gt_atTop, frequently_lt_rpow_neg, liouvilleWith, lt_add_one, mod_cast, rpow_neg
-/
theorem forall_liouvilleWith_iff {x : Real} : (forall p, LiouvilleWith p x) ↔ Liouville x := by
  refine ⟨fun H n => ?_, Liouville.liouvilleWith⟩
  rcases ((eventually_gt_atTop 1).and_frequently
    ((H (n + 1)).frequently_lt_rpow_neg (lt_add_one (n : Real)))).exists
    with ⟨b, hb, a, hne, hlt⟩
  exact ⟨a, b, mod_cast hb, hne, by simpa [rpow_neg] using hlt⟩
