/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Rat.Sqrt
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.IntervalCases

/-!
# Irrational real numbers

In this file we define a predicate `Irrational` on `ℝ`, prove that the `n`-th root of an integer
number is irrational if it is not integer, and that `√(q : ℚ)` is irrational if and only if
`¬IsSquare q ∧ 0 ≤ q`.

We also provide dot-style constructors like `Irrational.add_ratCast`, `Irrational.ratCast_sub` etc.

With the `Decidable` instances in this file, is possible to prove `Irrational √n` using `decide`,
when `n` is a numeric literal or cast;
but this only works if you `unseal Nat.sqrt.iter in` before the theorem where you use this proof.
-/

@[expose] public section


open Rat Real

/-- A real number is irrational if it is not equal to any rational number. -/
@[wikidata Q607728]
/--
Definition of `Irrational` / `Irrational` 的定义

English:
definition Irrational
  signature: (x : Real)
  body: x ∉ Set.range ((↑) : Rat -> Real)

中文:
定义 Irrational
  签名: (x : 实数)
  定义体: x ∉ Set.range ((↑) : Rat -> Real)

Depends on / 依赖: Set.range
-/
def Irrational (x : Real) :=
  x ∉ Set.range ((↑) : Rat -> Real)

/--
theorem `irrational_iff_ne_rational` / 定理 `irrational_iff_ne_rational`

English:
theorem irrational_iff_ne_rational
  given: (x : Real)
  statement: Irrational x ↔ forall a b : Int, b != 0 -> x != a / b
  proof: by
  simp [Irrational, Rat.forall, eq_comm]

中文:
定理 irrational_iff_ne_rational
  条件: (x : 实数)
  结论: Irrational x ↔ 对任意 a b : 整数, b != 0 -> x != a / b
  证明: by
  simp [Irrational, Rat.forall, eq_comm]

Depends on / 依赖: Irrational, Rat.forall, eq_comm
-/
theorem irrational_iff_ne_rational (x : Real) : Irrational x ↔ forall a b : Int, b != 0 -> x != a / b := by
  simp [Irrational, Rat.forall, eq_comm]

/--
theorem `Irrational.ne_rational` / 定理 `Irrational.ne_rational`

English:
theorem Irrational.ne_rational
  given: {x : Real} (hx : Irrational x) (a b : Int)
  statement: x != a / b
  proof: by
  rintro rfl; exact hx ⟨a / b, by simp⟩

中文:
定理 Irrational.ne_rational
  条件: {x : 实数} (hx : Irrational x) (a b : 整数)
  结论: x != a / b
  证明: by
  rintro rfl; exact hx ⟨a / b, by simp⟩
-/
theorem Irrational.ne_rational {x : Real} (hx : Irrational x) (a b : Int) : x != a / b := by
  rintro rfl; exact hx ⟨a / b, by simp⟩

/--
theorem `exists_rat_of_not_irrational` / 定理 `exists_rat_of_not_irrational`

English:
theorem exists_rat_of_not_irrational
  given: {x : Real} (hx : ¬ Irrational x)
  statement: exists (q : Rat), x = q
  proof: by
  grind [Irrational]

中文:
定理 存在_rat_of_not_irrational
  条件: {x : 实数} (hx : ¬ Irrational x)
  结论: 存在 (q : 有理数), x = q
  证明: by
  grind [Irrational]

Depends on / 依赖: Irrational
-/
theorem exists_rat_of_not_irrational {x : Real} (hx : ¬ Irrational x) : exists (q : Rat), x = q := by
  grind [Irrational]

/--
theorem `Transcendental.irrational` / 定理 `Transcendental.irrational`

English:
theorem Transcendental.irrational
  given: {r : Real} (tr : Transcendental Rat r)
  statement: Irrational r
  proof: by
  rintro ⟨a, rfl⟩
  exact tr (isAlgebraic_algebraMap a)

中文:
定理 超越.irrational
  条件: {r : 实数} (tr : 超越 有理数 r)
  结论: Irrational r
  证明: by
  rintro ⟨a, rfl⟩
  exact tr (isAlgebraic_algebraMap a)

Depends on / 依赖: isAlgebraic_algebraMap
-/
theorem Transcendental.irrational {r : Real} (tr : Transcendental Rat r) : Irrational r := by
  rintro ⟨a, rfl⟩
  exact tr (isAlgebraic_algebraMap a)

/-!
### Irrationality of roots of integer and rational numbers
-/


/--
theorem `irrational_nrt_of_notint_nrt` / 定理 `irrational_nrt_of_notint_nrt`

English:
theorem irrational_nrt_of_notint_nrt
  statement: {x : Real} (n : Nat) (m : Int) (hxr : x ^ n = m)
  proof: by
  rintro ⟨⟨N, D, P, C⟩, rfl⟩
  rw [← cast_pow] at hxr
  have c1 : ((D : Int) : Real) != 0 := by
    rw [Int.cast_ne_zero]; rw [Int.natCast_ne_zero]
    exact P
  have c2 : ((D : Int) : Real) ^ n != 0 := pow_ne_zero _ c1
  rw [mk_eq_divInt]; rw [cast_pow]; rw [cast_divInt]; rw [div_pow]; rw [div_eq_iff_mul_eq c2]; rw [← Int.cast_pow]; rw [← Int.cast_pow]; rw [← Int.cast_mul]; rw [Int.cast_inj] at hxr
  have hdivn : (D : Int) ^ n ∣ N ^ n := Dvd.intro_left m hxr
  rw [← Int.dvd_natAbs]; rw [← Int.natCast_pow]; rw [Int.natCast_dvd_natCast]; rw [Int.natAbs_pow]; rw [Nat.pow_dvd_pow_iff hnpos.ne'] at hdivn
  obtain rfl : D = 1 := by rw [← Nat.gcd_eq_right hdivn, C.gcd_eq_one]
  refine hv ⟨N, ?_⟩
  rw [mk_eq_divInt]; rw [Int.ofNat_one]; rw [divInt_one]; rw [cast_intCast]

中文:
定理 irrational_nrt_of_notint_nrt
  结论: {x : 实数} (n : 自然数) (m : 整数) (hxr : x ^ n = m)
  证明: by
  rintro ⟨⟨N, D, P, C⟩, rfl⟩
  rw [← cast_pow] at hxr
  have c1 : ((D : Int) : Real) != 0 := by
    rw [Int.cast_ne_zero]; rw [Int.natCast_ne_zero]
    exact P
  have c2 : ((D : Int) : Real) ^ n != 0 := pow_ne_zero _ c1
  rw [mk_eq_divInt]; rw [cast_pow]; rw [cast_divInt]; rw [div_pow]; rw [div_eq_iff_mul_eq c2]; rw [← Int.cast_pow]; rw [← Int.cast_pow]; rw [← Int.cast_mul]; rw [Int.cast_inj] at hxr
  have hdivn : (D : Int) ^ n ∣ N ^ n := Dvd.intro_left m hxr
  rw [← Int.dvd_natAbs]; rw [← Int.natCast_pow]; rw [Int.natCast_dvd_natCast]; rw [Int.natAbs_pow]; rw [Nat.pow_dvd_pow_iff hnpos.ne'] at hdivn
  obtain rfl : D = 1 := by rw [← Nat.gcd_eq_right hdivn, C.gcd_eq_one]
  refine hv ⟨N, ?_⟩
  rw [mk_eq_divInt]; rw [Int.ofNat_one]; rw [divInt_one]; rw [cast_intCast]

Depends on / 依赖: Dvd.intro_left, Int.cast_inj, Int.cast_mul, Int.cast_ne_zero, Int.cast_pow, Int.dvd_natAbs, Int.natCast_ne_zero, Int.natCast_pow, cast_divInt, cast_inj, cast_mul, cast_ne_zero, cast_pow, div_eq_iff_mul_eq, div_pow, dvd_natAbs, intro_left, mk_eq_divInt, natCast_ne_zero, natCast_pow
-/
theorem irrational_nrt_of_notint_nrt {x : Real} (n : Nat) (m : Int) (hxr : x ^ n = m)
    (hv : ¬exists y : Int, x = y) (hnpos : 0 < n) : Irrational x := by
  rintro ⟨⟨N, D, P, C⟩, rfl⟩
  rw [← cast_pow] at hxr
  have c1 : ((D : Int) : Real) != 0 := by
    rw [Int.cast_ne_zero]; rw [Int.natCast_ne_zero]
    exact P
  have c2 : ((D : Int) : Real) ^ n != 0 := pow_ne_zero _ c1
  rw [mk_eq_divInt]; rw [cast_pow]; rw [cast_divInt]; rw [div_pow]; rw [div_eq_iff_mul_eq c2]; rw [← Int.cast_pow]; rw [← Int.cast_pow]; rw [← Int.cast_mul]; rw [Int.cast_inj] at hxr
  have hdivn : (D : Int) ^ n ∣ N ^ n := Dvd.intro_left m hxr
  rw [← Int.dvd_natAbs]; rw [← Int.natCast_pow]; rw [Int.natCast_dvd_natCast]; rw [Int.natAbs_pow]; rw [Nat.pow_dvd_pow_iff hnpos.ne'] at hdivn
  obtain rfl : D = 1 := by rw [← Nat.gcd_eq_right hdivn, C.gcd_eq_one]
  refine hv ⟨N, ?_⟩
  rw [mk_eq_divInt]; rw [Int.ofNat_one]; rw [divInt_one]; rw [cast_intCast]

/--
theorem `irrational_nrt_of_n_not_dvd_multiplicity` / 定理 `irrational_nrt_of_n_not_dvd_multiplicity`

English:
theorem irrational_nrt_of_n_not_dvd_multiplicity
  statement: {x : Real} (n : Nat) {m : Int} (hm : m != 0) (p : Nat)
  proof: by
  rcases Nat.eq_zero_or_pos n with (rfl | hnpos)
  · rw [eq_comm, pow_zero, ← Int.cast_one, Int.cast_inj] at hxr
    simp [hxr, multiplicity_of_one_right (mt isUnit_iff_dvd_one.1
      (mt Int.natCast_dvd_natCast.1 hp.1.not_dvd_one))] at hv
  refine irrational_nrt_of_notint_nrt _ _ hxr ?_ hnpos
  rintro ⟨y, rfl⟩
  rw [← Int.cast_pow]; rw [Int.cast_inj] at hxr
  subst m
  have : y != 0 := by rintro rfl; rw [zero_pow hnpos.ne'] at hm; exact hm rfl
  rw [(Int.finiteMultiplicity_iff.2 ⟨by simp [hp.1.ne_one], this⟩).multiplicity_pow
    (Nat.prime_iff_prime_int.1 hp.1), Nat.mul_mod_right] at hv
  exact hv rfl

中文:
定理 irrational_nrt_of_n_not_dvd_multiplicity
  结论: {x : 实数} (n : 自然数) {m : 整数} (hm : m != 0) (p : 自然数)
  证明: by
  rcases Nat.eq_zero_or_pos n with (rfl | hnpos)
  · rw [eq_comm, pow_zero, ← Int.cast_one, Int.cast_inj] at hxr
    simp [hxr, multiplicity_of_one_right (mt isUnit_iff_dvd_one.1
      (mt Int.natCast_dvd_natCast.1 hp.1.not_dvd_one))] at hv
  refine irrational_nrt_of_notint_nrt _ _ hxr ?_ hnpos
  rintro ⟨y, rfl⟩
  rw [← Int.cast_pow]; rw [Int.cast_inj] at hxr
  subst m
  have : y != 0 := by rintro rfl; rw [zero_pow hnpos.ne'] at hm; exact hm rfl
  rw [(Int.finiteMultiplicity_iff.2 ⟨by simp [hp.1.ne_one], this⟩).multiplicity_pow
    (Nat.prime_iff_prime_int.1 hp.1), Nat.mul_mod_right] at hv
  exact hv rfl

Depends on / 依赖: Int.cast_inj, Int.cast_one, Int.cast_pow, Int.finiteMultiplicity_iff, Int.natCast_dvd_natCast, Nat.eq_zero_or_pos, cast_inj, cast_one, cast_pow, eq_comm, eq_zero_or_pos, finiteMultiplicity_iff, hnpos.ne, irrational_nrt_of_notint_nrt, isUnit_iff_dvd_one, multip, multiplicity_of_one_right, natCast_dvd_natCast, ne_one, not_dvd_one
-/
theorem irrational_nrt_of_n_not_dvd_multiplicity {x : Real} (n : Nat) {m : Int} (hm : m != 0) (p : Nat)
    [hp : Fact p.Prime] (hxr : x ^ n = m)
    (hv : multiplicity (p : Int) m % n != 0) :
    Irrational x := by
  rcases Nat.eq_zero_or_pos n with (rfl | hnpos)
  · rw [eq_comm, pow_zero, ← Int.cast_one, Int.cast_inj] at hxr
    simp [hxr, multiplicity_of_one_right (mt isUnit_iff_dvd_one.1
      (mt Int.natCast_dvd_natCast.1 hp.1.not_dvd_one))] at hv
  refine irrational_nrt_of_notint_nrt _ _ hxr ?_ hnpos
  rintro ⟨y, rfl⟩
  rw [← Int.cast_pow]; rw [Int.cast_inj] at hxr
  subst m
  have : y != 0 := by rintro rfl; rw [zero_pow hnpos.ne'] at hm; exact hm rfl
  rw [(Int.finiteMultiplicity_iff.2 ⟨by simp [hp.1.ne_one], this⟩).multiplicity_pow
    (Nat.prime_iff_prime_int.1 hp.1), Nat.mul_mod_right] at hv
  exact hv rfl

/--
theorem `irrational_sqrt_of_multiplicity_odd` / 定理 `irrational_sqrt_of_multiplicity_odd`

English:
theorem irrational_sqrt_of_multiplicity_odd
  statement: (m : Int) (hm : 0 < m) (p : Nat) [hp : Fact p.Prime]
  proof: @irrational_nrt_of_n_not_dvd_multiplicity _ 2 _ (Ne.symm (ne_of_lt hm)) p hp
    (sq_sqrt (Int.cast_nonneg hm.le)) (by rw [Hpv]; exact one_ne_zero)

中文:
定理 irrational_sqrt_of_multiplicity_odd
  结论: (m : 整数) (hm : 0 < m) (p : 自然数) [hp : Fact p.素]
  证明: @irrational_nrt_of_n_not_dvd_multiplicity _ 2 _ (Ne.symm (ne_of_lt hm)) p hp
    (sq_sqrt (Int.cast_nonneg hm.le)) (by rw [Hpv]; exact one_ne_zero)

Depends on / 依赖: Int.cast_nonneg, Ne.symm, cast_nonneg, hm.le, irrational_nrt_of_n_not_dvd_multiplicity, ne_of_lt, one_ne_zero, sq_sqrt
-/
theorem irrational_sqrt_of_multiplicity_odd (m : Int) (hm : 0 < m) (p : Nat) [hp : Fact p.Prime]
    (Hpv : multiplicity (p : Int) m % 2 = 1) :
    Irrational (√m) :=
  @irrational_nrt_of_n_not_dvd_multiplicity _ 2 _ (Ne.symm (ne_of_lt hm)) p hp
    (sq_sqrt (Int.cast_nonneg hm.le)) (by rw [Hpv]; exact one_ne_zero)

/--
theorem `not_irrational_zero` / 定理 `not_irrational_zero`

English:
theorem not_irrational_zero
  statement: ¬Irrational 0
  proof: not_not_intro ⟨0, Rat.cast_zero⟩

中文:
定理 not_irrational_zero
  结论: ¬Irrational 0
  证明: not_not_intro ⟨0, Rat.cast_zero⟩
-/
@[simp] theorem not_irrational_zero : ¬Irrational 0 := not_not_intro ⟨0, Rat.cast_zero⟩
/--
theorem `not_irrational_one` / 定理 `not_irrational_one`

English:
theorem not_irrational_one
  statement: ¬Irrational 1
  proof: not_not_intro ⟨1, Rat.cast_one⟩

中文:
定理 not_irrational_one
  结论: ¬Irrational 1
  证明: not_not_intro ⟨1, Rat.cast_one⟩
-/
@[simp] theorem not_irrational_one : ¬Irrational 1 := not_not_intro ⟨1, Rat.cast_one⟩

/--
theorem `irrational_sqrt_ratCast_iff_of_nonneg` / 定理 `irrational_sqrt_ratCast_iff_of_nonneg`

English:
theorem irrational_sqrt_ratCast_iff_of_nonneg
  given: {q : Rat} (hq : 0 <= q)
  proof: by
  refine Iff.not (?_ : Exists _ ↔ Exists _)
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, Rat.cast_injective (α := Real) ?_⟩
    rw [Rat.cast_mul]; rw [hy]; rw [mul_self_sqrt (Rat.cast_nonneg.2 hq)]
  · rintro ⟨q', rfl⟩
    exact ⟨|q'|, mod_cast (sqrt_mul_self_eq_abs q').symm⟩

中文:
定理 irrational_sqrt_ratCast_iff_of_nonneg
  条件: {q : 有理数} (hq : 0 <= q)
  证明: by
  refine Iff.not (?_ : Exists _ ↔ Exists _)
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, Rat.cast_injective (α := Real) ?_⟩
    rw [Rat.cast_mul]; rw [hy]; rw [mul_self_sqrt (Rat.cast_nonneg.2 hq)]
  · rintro ⟨q', rfl⟩
    exact ⟨|q'|, mod_cast (sqrt_mul_self_eq_abs q').symm⟩

Depends on / 依赖: Exists, Iff.not, Rat.cast_injective, Rat.cast_mul, Rat.cast_nonneg, cast_injective, cast_mul, cast_nonneg, mod_cast, mul_self_sqrt, sqrt_mul_self_eq_abs
-/
theorem irrational_sqrt_ratCast_iff_of_nonneg {q : Rat} (hq : 0 <= q) :
    Irrational (√q) ↔ ¬IsSquare q := by
  refine Iff.not (?_ : Exists _ ↔ Exists _)
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, Rat.cast_injective (α := Real) ?_⟩
    rw [Rat.cast_mul]; rw [hy]; rw [mul_self_sqrt (Rat.cast_nonneg.2 hq)]
  · rintro ⟨q', rfl⟩
    exact ⟨|q'|, mod_cast (sqrt_mul_self_eq_abs q').symm⟩

/--
theorem `irrational_sqrt_ratCast_iff` / 定理 `irrational_sqrt_ratCast_iff`

English:
theorem irrational_sqrt_ratCast_iff
  given: {q : Rat}
  proof: by
  obtain hq | hq := le_or_gt 0 q
  · simp_rw [irrational_sqrt_ratCast_iff_of_nonneg hq, and_iff_left hq]
  · rw [sqrt_eq_zero_of_nonpos (Rat.cast_nonpos.2 hq.le)]
    simp_rw [not_irrational_zero, false_iff, not_and, not_le, hq, implies_true]

中文:
定理 irrational_sqrt_ratCast_iff
  条件: {q : 有理数}
  证明: by
  obtain hq | hq := le_or_gt 0 q
  · simp_rw [irrational_sqrt_ratCast_iff_of_nonneg hq, and_iff_left hq]
  · rw [sqrt_eq_zero_of_nonpos (Rat.cast_nonpos.2 hq.le)]
    simp_rw [not_irrational_zero, false_iff, not_and, not_le, hq, implies_true]

Depends on / 依赖: Rat.cast_nonpos, and_iff_left, cast_nonpos, false_iff, hq.le, implies_true, irrational_sqrt_ratCast_iff_of_nonneg, le_or_gt, not_and, not_irrational_zero, not_le, simp_rw, sqrt_eq_zero_of_nonpos
-/
theorem irrational_sqrt_ratCast_iff {q : Rat} :
    Irrational (√q) ↔ ¬IsSquare q ∧ 0 <= q := by
  obtain hq | hq := le_or_gt 0 q
  · simp_rw [irrational_sqrt_ratCast_iff_of_nonneg hq, and_iff_left hq]
  · rw [sqrt_eq_zero_of_nonpos (Rat.cast_nonpos.2 hq.le)]
    simp_rw [not_irrational_zero, false_iff, not_and, not_le, hq, implies_true]

/--
theorem `irrational_sqrt_intCast_iff_of_nonneg` / 定理 `irrational_sqrt_intCast_iff_of_nonneg`

English:
theorem irrational_sqrt_intCast_iff_of_nonneg
  given: {z : Int} (hz : 0 <= z)
  proof: by
  rw [← Rat.isSquare_intCast_iff]; rw [← irrational_sqrt_ratCast_iff_of_nonneg (mod_cast hz)]; rw [Rat.cast_intCast]

中文:
定理 irrational_sqrt_intCast_iff_of_nonneg
  条件: {z : 整数} (hz : 0 <= z)
  证明: by
  rw [← Rat.isSquare_intCast_iff]; rw [← irrational_sqrt_ratCast_iff_of_nonneg (mod_cast hz)]; rw [Rat.cast_intCast]

Depends on / 依赖: Rat.cast_intCast, Rat.isSquare_intCast_iff, cast_intCast, irrational_sqrt_ratCast_iff_of_nonneg, isSquare_intCast_iff, mod_cast
-/
theorem irrational_sqrt_intCast_iff_of_nonneg {z : Int} (hz : 0 <= z) :
    Irrational (√z) ↔ ¬IsSquare z := by
  rw [← Rat.isSquare_intCast_iff]; rw [← irrational_sqrt_ratCast_iff_of_nonneg (mod_cast hz)]; rw [Rat.cast_intCast]

/--
theorem `irrational_sqrt_intCast_iff` / 定理 `irrational_sqrt_intCast_iff`

English:
theorem irrational_sqrt_intCast_iff
  given: {z : Int}
  proof: by
  rw [← Rat.cast_intCast]; rw [irrational_sqrt_ratCast_iff]; rw [Rat.isSquare_intCast_iff]; rw [Int.cast_nonneg_iff]

中文:
定理 irrational_sqrt_intCast_iff
  条件: {z : 整数}
  证明: by
  rw [← Rat.cast_intCast]; rw [irrational_sqrt_ratCast_iff]; rw [Rat.isSquare_intCast_iff]; rw [Int.cast_nonneg_iff]

Depends on / 依赖: Int.cast_nonneg_iff, Rat.cast_intCast, Rat.isSquare_intCast_iff, cast_intCast, cast_nonneg_iff, irrational_sqrt_ratCast_iff, isSquare_intCast_iff
-/
theorem irrational_sqrt_intCast_iff {z : Int} :
    Irrational (√z) ↔ ¬IsSquare z ∧ 0 <= z := by
  rw [← Rat.cast_intCast]; rw [irrational_sqrt_ratCast_iff]; rw [Rat.isSquare_intCast_iff]; rw [Int.cast_nonneg_iff]

/--
theorem `irrational_sqrt_natCast_iff` / 定理 `irrational_sqrt_natCast_iff`

English:
theorem irrational_sqrt_natCast_iff
  given: {n : Nat}
  statement: Irrational (√n) ↔ ¬IsSquare n
  proof: by
  rw [← Rat.isSquare_natCast_iff]; rw [← irrational_sqrt_ratCast_iff_of_nonneg n.cast_nonneg]; rw [Rat.cast_natCast]

中文:
定理 irrational_sqrt_natCast_iff
  条件: {n : 自然数}
  结论: Irrational (√n) ↔ ¬IsSquare n
  证明: by
  rw [← Rat.isSquare_natCast_iff]; rw [← irrational_sqrt_ratCast_iff_of_nonneg n.cast_nonneg]; rw [Rat.cast_natCast]

Depends on / 依赖: Rat.cast_natCast, Rat.isSquare_natCast_iff, cast_natCast, cast_nonneg, irrational_sqrt_ratCast_iff_of_nonneg, isSquare_natCast_iff, n.cast_nonneg
-/
theorem irrational_sqrt_natCast_iff {n : Nat} : Irrational (√n) ↔ ¬IsSquare n := by
  rw [← Rat.isSquare_natCast_iff]; rw [← irrational_sqrt_ratCast_iff_of_nonneg n.cast_nonneg]; rw [Rat.cast_natCast]

/--
theorem `irrational_sqrt_ofNat_iff` / 定理 `irrational_sqrt_ofNat_iff`

English:
theorem irrational_sqrt_ofNat_iff
  given: {n : Nat} [n.AtLeastTwo]
  proof: irrational_sqrt_natCast_iff

中文:
定理 irrational_sqrt_of自然数_iff
  条件: {n : 自然数} [n.AtLeastTwo]
  证明: irrational_sqrt_natCast_iff

Depends on / 依赖: irrational_sqrt_natCast_iff
-/
theorem irrational_sqrt_ofNat_iff {n : Nat} [n.AtLeastTwo] :
    Irrational √(ofNat(n)) ↔ ¬IsSquare ofNat(n) :=
  irrational_sqrt_natCast_iff

/--
theorem `Nat.Prime.irrational_sqrt` / 定理 `Nat.Prime.irrational_sqrt`

English:
theorem Nat.Prime.irrational_sqrt
  given: {p : Nat} (hp : Nat.Prime p)
  statement: Irrational (√p)
  proof: irrational_sqrt_natCast_iff.mpr hp.not_isSquare

中文:
定理 自然数.素.irrational_sqrt
  条件: {p : 自然数} (hp : 自然数.素 p)
  结论: Irrational (√p)
  证明: irrational_sqrt_natCast_iff.mpr hp.not_isSquare

Depends on / 依赖: hp.not_isSquare, irrational_sqrt_natCast_iff, irrational_sqrt_natCast_iff.mpr, not_isSquare
-/
theorem Nat.Prime.irrational_sqrt {p : Nat} (hp : Nat.Prime p) : Irrational (√p) :=
  irrational_sqrt_natCast_iff.mpr hp.not_isSquare

/--
theorem `irrational_sqrt_two` / 定理 `irrational_sqrt_two`

English:
theorem irrational_sqrt_two
  statement: Irrational (√2)
  proof: by
  simpa using Nat.prime_two.irrational_sqrt

中文:
定理 irrational_sqrt_two
  结论: Irrational (√2)
  证明: by
  simpa using Nat.prime_two.irrational_sqrt

Depends on / 依赖: Nat.prime_two.irrational_sqrt, irrational_sqrt, prime_two
-/
theorem irrational_sqrt_two : Irrational (√2) := by
  simpa using Nat.prime_two.irrational_sqrt

/--
This can be used as
```lean
unseal Nat.sqrt.iter in
example : Irrational √24 := by decide
```
-/
instance {n : Nat} [n.AtLeastTwo] : Decidable (Irrational √(ofNat(n))) :=
  decidable_of_iff' _ irrational_sqrt_ofNat_iff

instance (n : Nat) : Decidable (Irrational (√n)) :=
  decidable_of_iff' _ irrational_sqrt_natCast_iff

instance (z : Int) : Decidable (Irrational (√z)) :=
  decidable_of_iff' _ irrational_sqrt_intCast_iff

instance (q : Rat) : Decidable (Irrational (√q)) :=
  decidable_of_iff' _ irrational_sqrt_ratCast_iff

/-!
### Dot-style operations on `Irrational`

#### Coercion of a rational/integer/natural number is not irrational
-/


namespace Irrational

variable {x : Real}



/--
theorem `ne_rat` / 定理 `ne_rat`

English:
theorem ne_rat
  given: (h : Irrational x) (q : Rat)
  statement: x != q
  proof: fun hq => h ⟨q, hq.symm⟩

中文:
定理 ne_rat
  条件: (h : Irrational x) (q : 有理数)
  结论: x != q
  证明: fun hq => h ⟨q, hq.symm⟩

Depends on / 依赖: hq.symm
-/
theorem ne_rat (h : Irrational x) (q : Rat) : x != q := fun hq => h ⟨q, hq.symm⟩

/--
theorem `ne_int` / 定理 `ne_int`

English:
theorem ne_int
  given: (h : Irrational x) (m : Int)
  statement: x != m
  proof: by
  rw [← Rat.cast_intCast]
  exact h.ne_rat _

中文:
定理 ne_int
  条件: (h : Irrational x) (m : 整数)
  结论: x != m
  证明: by
  rw [← Rat.cast_intCast]
  exact h.ne_rat _

Depends on / 依赖: Rat.cast_intCast, cast_intCast, h.ne_rat, ne_rat
-/
theorem ne_int (h : Irrational x) (m : Int) : x != m := by
  rw [← Rat.cast_intCast]
  exact h.ne_rat _

/--
theorem `ne_nat` / 定理 `ne_nat`

English:
theorem ne_nat
  given: (h : Irrational x) (m : Nat)
  statement: x != m
  proof: h.ne_int m

中文:
定理 ne_nat
  条件: (h : Irrational x) (m : 自然数)
  结论: x != m
  证明: h.ne_int m

Depends on / 依赖: h.ne_int, ne_int
-/
theorem ne_nat (h : Irrational x) (m : Nat) : x != m :=
  h.ne_int m

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: (h : Irrational x)
  statement: x != 0
  proof: mod_cast h.ne_nat 0

中文:
定理 ne_zero
  条件: (h : Irrational x)
  结论: x != 0
  证明: mod_cast h.ne_nat 0

Depends on / 依赖: h.ne_nat, mod_cast, ne_nat
-/
theorem ne_zero (h : Irrational x) : x != 0 := mod_cast h.ne_nat 0

/--
theorem `ne_one` / 定理 `ne_one`

English:
theorem ne_one
  given: (h : Irrational x)
  statement: x != 1
  proof: by simpa only [Nat.cast_one] using h.ne_nat 1

中文:
定理 ne_one
  条件: (h : Irrational x)
  结论: x != 1
  证明: by simpa only [Nat.cast_one] using h.ne_nat 1

Depends on / 依赖: Nat.cast_one, cast_one, h.ne_nat, ne_nat
-/
theorem ne_one (h : Irrational x) : x != 1 := by simpa only [Nat.cast_one] using h.ne_nat 1

/--
theorem `ne_ofNat` / 定理 `ne_ofNat`

English:
theorem ne_ofNat
  given: (h : Irrational x) (n : Nat) [n.AtLeastTwo]
  statement: x != ofNat(n)
  proof: h.ne_nat n

中文:
定理 ne_of自然数
  条件: (h : Irrational x) (n : 自然数) [n.AtLeastTwo]
  结论: x != of自然数(n)
  证明: h.ne_nat n
-/
@[simp] theorem ne_ofNat (h : Irrational x) (n : Nat) [n.AtLeastTwo] : x != ofNat(n) :=
  h.ne_nat n

end Irrational

@[simp]
/--
theorem `Rat.not_irrational` / 定理 `Rat.not_irrational`

English:
theorem Rat.not_irrational
  given: (q : Rat)
  statement: ¬Irrational q
  proof: fun h => h ⟨q, rfl⟩

@[simp]

中文:
定理 有理数.not_irrational
  条件: (q : 有理数)
  结论: ¬Irrational q
  证明: fun h => h ⟨q, rfl⟩

@[simp]
-/
theorem Rat.not_irrational (q : Rat) : ¬Irrational q := fun h => h ⟨q, rfl⟩

@[simp]
/--
theorem `Int.not_irrational` / 定理 `Int.not_irrational`

English:
theorem Int.not_irrational
  given: (m : Int)
  statement: ¬Irrational m
  proof: fun h => h.ne_int m rfl

@[simp]

中文:
定理 整数.not_irrational
  条件: (m : 整数)
  结论: ¬Irrational m
  证明: fun h => h.ne_int m rfl

@[simp]

Depends on / 依赖: h.ne_int, ne_int
-/
theorem Int.not_irrational (m : Int) : ¬Irrational m := fun h => h.ne_int m rfl

@[simp]
/--
theorem `Nat.not_irrational` / 定理 `Nat.not_irrational`

English:
theorem Nat.not_irrational
  given: (m : Nat)
  statement: ¬Irrational m
  proof: fun h => h.ne_nat m rfl

中文:
定理 自然数.not_irrational
  条件: (m : 自然数)
  结论: ¬Irrational m
  证明: fun h => h.ne_nat m rfl

Depends on / 依赖: h.ne_nat, ne_nat
-/
theorem Nat.not_irrational (m : Nat) : ¬Irrational m := fun h => h.ne_nat m rfl

/--
theorem `not_irrational_ofNat` / 定理 `not_irrational_ofNat`

English:
theorem not_irrational_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ¬Irrational ofNat(n)
  proof: n.not_irrational

中文:
定理 not_irrational_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: ¬Irrational of自然数(n)
  证明: n.not_irrational
-/
@[simp] theorem not_irrational_ofNat (n : Nat) [n.AtLeastTwo] : ¬Irrational ofNat(n) :=
  n.not_irrational
namespace Irrational

variable (q : Rat) {x y : Real}

/-!
#### Addition of rational/integer/natural numbers
-/


/--
theorem `add_cases` / 定理 `add_cases`

English:
theorem add_cases
  statement: Irrational (x + y) -> Irrational x ∨ Irrational y
  proof: by
  delta Irrational
  contrapose!
  rintro ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩
  exact ⟨rx + ry, cast_add rx ry⟩

中文:
定理 add_cases
  结论: Irrational (x + y) -> Irrational x ∨ Irrational y
  证明: by
  delta Irrational
  contrapose!
  rintro ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩
  exact ⟨rx + ry, cast_add rx ry⟩

Depends on / 依赖: Irrational, cast_add, contrapose
-/
theorem add_cases : Irrational (x + y) -> Irrational x ∨ Irrational y := by
  delta Irrational
  contrapose!
  rintro ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩
  exact ⟨rx + ry, cast_add rx ry⟩

/--
theorem `of_ratCast_add` / 定理 `of_ratCast_add`

English:
theorem of_ratCast_add
  given: (h : Irrational (q + x))
  statement: Irrational x
  proof: h.add_cases.resolve_left q.not_irrational

中文:
定理 of_ratCast_add
  条件: (h : Irrational (q + x))
  结论: Irrational x
  证明: h.add_cases.resolve_left q.not_irrational

Depends on / 依赖: add_cases, h.add_cases.resolve_left, not_irrational, q.not_irrational, resolve_left
-/
theorem of_ratCast_add (h : Irrational (q + x)) : Irrational x :=
  h.add_cases.resolve_left q.not_irrational
/--
theorem `ratCast_add` / 定理 `ratCast_add`

English:
theorem ratCast_add
  given: (h : Irrational x)
  statement: Irrational (q + x)
  proof: of_ratCast_add (-q) by rwa [cast_neg, neg_add_cancel_left]

中文:
定理 ratCast_add
  条件: (h : Irrational x)
  结论: Irrational (q + x)
  证明: of_ratCast_add (-q) by rwa [cast_neg, neg_add_cancel_left]

Depends on / 依赖: cast_neg, neg_add_cancel_left, of_ratCast_add
-/
theorem ratCast_add (h : Irrational x) : Irrational (q + x) :=
of_ratCast_add (-q) by rwa [cast_neg, neg_add_cancel_left]
/--
theorem `of_add_ratCast` / 定理 `of_add_ratCast`

English:
theorem of_add_ratCast
  statement: Irrational (x + q) -> Irrational x
  proof: add_comm (↑q) x ▸ of_ratCast_add q

中文:
定理 of_add_ratCast
  结论: Irrational (x + q) -> Irrational x
  证明: add_comm (↑q) x ▸ of_ratCast_add q

Depends on / 依赖: add_comm, of_ratCast_add
-/
theorem of_add_ratCast : Irrational (x + q) -> Irrational x :=
  add_comm (↑q) x ▸ of_ratCast_add q
/--
theorem `add_ratCast` / 定理 `add_ratCast`

English:
theorem add_ratCast
  given: (h : Irrational x)
  statement: Irrational (x + q)
  proof: add_comm (↑q) x ▸ h.ratCast_add q

中文:
定理 add_ratCast
  条件: (h : Irrational x)
  结论: Irrational (x + q)
  证明: add_comm (↑q) x ▸ h.ratCast_add q

Depends on / 依赖: add_comm, h.ratCast_add, ratCast_add
-/
theorem add_ratCast (h : Irrational x) : Irrational (x + q) :=
  add_comm (↑q) x ▸ h.ratCast_add q
/--
theorem `of_intCast_add` / 定理 `of_intCast_add`

English:
theorem of_intCast_add
  given: (m : Int) (h : Irrational (m + x))
  statement: Irrational x
  proof: by
  rw [← cast_intCast] at h
  exact h.of_ratCast_add m

中文:
定理 of_intCast_add
  条件: (m : 整数) (h : Irrational (m + x))
  结论: Irrational x
  证明: by
  rw [← cast_intCast] at h
  exact h.of_ratCast_add m

Depends on / 依赖: cast_intCast, h.of_ratCast_add, of_ratCast_add
-/
theorem of_intCast_add (m : Int) (h : Irrational (m + x)) : Irrational x := by
  rw [← cast_intCast] at h
  exact h.of_ratCast_add m
/--
theorem `of_add_intCast` / 定理 `of_add_intCast`

English:
theorem of_add_intCast
  given: (m : Int) (h : Irrational (x + m))
  statement: Irrational x
  proof: of_intCast_add m add_comm x m ▸ h

中文:
定理 of_add_intCast
  条件: (m : 整数) (h : Irrational (x + m))
  结论: Irrational x
  证明: of_intCast_add m add_comm x m ▸ h

Depends on / 依赖: add_comm, of_intCast_add
-/
theorem of_add_intCast (m : Int) (h : Irrational (x + m)) : Irrational x :=
of_intCast_add m add_comm x m ▸ h
/--
theorem `intCast_add` / 定理 `intCast_add`

English:
theorem intCast_add
  given: (h : Irrational x) (m : Int)
  statement: Irrational (m + x)
  proof: by
  rw [← cast_intCast]
  exact h.ratCast_add m

中文:
定理 intCast_add
  条件: (h : Irrational x) (m : 整数)
  结论: Irrational (m + x)
  证明: by
  rw [← cast_intCast]
  exact h.ratCast_add m

Depends on / 依赖: cast_intCast, h.ratCast_add, ratCast_add
-/
theorem intCast_add (h : Irrational x) (m : Int) : Irrational (m + x) := by
  rw [← cast_intCast]
  exact h.ratCast_add m
/--
theorem `add_intCast` / 定理 `add_intCast`

English:
theorem add_intCast
  given: (h : Irrational x) (m : Int)
  statement: Irrational (x + m)
  proof: add_comm (↑m) x ▸ h.intCast_add m

中文:
定理 add_intCast
  条件: (h : Irrational x) (m : 整数)
  结论: Irrational (x + m)
  证明: add_comm (↑m) x ▸ h.intCast_add m

Depends on / 依赖: add_comm, h.intCast_add, intCast_add
-/
theorem add_intCast (h : Irrational x) (m : Int) : Irrational (x + m) :=
  add_comm (↑m) x ▸ h.intCast_add m
/--
theorem `of_natCast_add` / 定理 `of_natCast_add`

English:
theorem of_natCast_add
  given: (m : Nat) (h : Irrational (m + x))
  statement: Irrational x
  proof: h.of_intCast_add m

中文:
定理 of_natCast_add
  条件: (m : 自然数) (h : Irrational (m + x))
  结论: Irrational x
  证明: h.of_intCast_add m

Depends on / 依赖: h.of_intCast_add, of_intCast_add
-/
theorem of_natCast_add (m : Nat) (h : Irrational (m + x)) : Irrational x :=
  h.of_intCast_add m
/--
theorem `of_add_natCast` / 定理 `of_add_natCast`

English:
theorem of_add_natCast
  given: (m : Nat) (h : Irrational (x + m))
  statement: Irrational x
  proof: h.of_add_intCast m

中文:
定理 of_add_natCast
  条件: (m : 自然数) (h : Irrational (x + m))
  结论: Irrational x
  证明: h.of_add_intCast m

Depends on / 依赖: h.of_add_intCast, of_add_intCast
-/
theorem of_add_natCast (m : Nat) (h : Irrational (x + m)) : Irrational x :=
  h.of_add_intCast m
/--
theorem `natCast_add` / 定理 `natCast_add`

English:
theorem natCast_add
  given: (h : Irrational x) (m : Nat)
  statement: Irrational (m + x)
  proof: h.intCast_add m

中文:
定理 natCast_add
  条件: (h : Irrational x) (m : 自然数)
  结论: Irrational (m + x)
  证明: h.intCast_add m

Depends on / 依赖: h.intCast_add, intCast_add
-/
theorem natCast_add (h : Irrational x) (m : Nat) : Irrational (m + x) :=
  h.intCast_add m
/--
theorem `add_natCast` / 定理 `add_natCast`

English:
theorem add_natCast
  given: (h : Irrational x) (m : Nat)
  statement: Irrational (x + m)
  proof: h.add_intCast m

中文:
定理 add_natCast
  条件: (h : Irrational x) (m : 自然数)
  结论: Irrational (x + m)
  证明: h.add_intCast m

Depends on / 依赖: add_intCast, h.add_intCast
-/
theorem add_natCast (h : Irrational x) (m : Nat) : Irrational (x + m) :=
  h.add_intCast m


/--
theorem `of_neg` / 定理 `of_neg`

English:
theorem of_neg
  given: (h : Irrational (-x))
  statement: Irrational x
  proof: fun ⟨q, hx⟩ => h ⟨-q, by rw [cast_neg, hx]⟩

中文:
定理 of_neg
  条件: (h : Irrational (-x))
  结论: Irrational x
  证明: fun ⟨q, hx⟩ => h ⟨-q, by rw [cast_neg, hx]⟩

Depends on / 依赖: cast_neg
-/
theorem of_neg (h : Irrational (-x)) : Irrational x := fun ⟨q, hx⟩ => h ⟨-q, by rw [cast_neg, hx]⟩

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (h : Irrational x)
  statement: Irrational (-x)
  proof: of_neg by rwa [neg_neg]

中文:
定理 neg
  条件: (h : Irrational x)
  结论: Irrational (-x)
  证明: of_neg by rwa [neg_neg]

Depends on / 依赖: add_le_add_right
-/
protected theorem neg (h : Irrational x) : Irrational (-x) :=
of_neg by rwa [neg_neg]



/--
theorem `sub_ratCast` / 定理 `sub_ratCast`

English:
theorem sub_ratCast
  given: (h : Irrational x)
  statement: Irrational (x - q)
  proof: by
  simpa only [sub_eq_add_neg, cast_neg] using h.add_ratCast (-q)

中文:
定理 sub_ratCast
  条件: (h : Irrational x)
  结论: Irrational (x - q)
  证明: by
  simpa only [sub_eq_add_neg, cast_neg] using h.add_ratCast (-q)

Depends on / 依赖: add_ratCast, cast_neg, h.add_ratCast, sub_eq_add_neg
-/
theorem sub_ratCast (h : Irrational x) : Irrational (x - q) := by
  simpa only [sub_eq_add_neg, cast_neg] using h.add_ratCast (-q)
/--
theorem `ratCast_sub` / 定理 `ratCast_sub`

English:
theorem ratCast_sub
  given: (h : Irrational x)
  statement: Irrational (q - x)
  proof: by
  simpa only [sub_eq_add_neg] using h.neg.ratCast_add q

中文:
定理 ratCast_sub
  条件: (h : Irrational x)
  结论: Irrational (q - x)
  证明: by
  simpa only [sub_eq_add_neg] using h.neg.ratCast_add q

Depends on / 依赖: h.neg.ratCast_add, ratCast_add, sub_eq_add_neg
-/
theorem ratCast_sub (h : Irrational x) : Irrational (q - x) := by
  simpa only [sub_eq_add_neg] using h.neg.ratCast_add q
/--
theorem `of_sub_ratCast` / 定理 `of_sub_ratCast`

English:
theorem of_sub_ratCast
  given: (h : Irrational (x - q))
  statement: Irrational x
  proof: of_add_ratCast (-q) by simpa only [cast_neg, sub_eq_add_neg] using h

中文:
定理 of_sub_ratCast
  条件: (h : Irrational (x - q))
  结论: Irrational x
  证明: of_add_ratCast (-q) by simpa only [cast_neg, sub_eq_add_neg] using h

Depends on / 依赖: cast_neg, of_add_ratCast, sub_eq_add_neg
-/
theorem of_sub_ratCast (h : Irrational (x - q)) : Irrational x :=
of_add_ratCast (-q) by simpa only [cast_neg, sub_eq_add_neg] using h
/--
theorem `of_ratCast_sub` / 定理 `of_ratCast_sub`

English:
theorem of_ratCast_sub
  given: (h : Irrational (q - x))
  statement: Irrational x
  proof: of_neg (of_ratCast_add q (by simpa only [sub_eq_add_neg] using h))

中文:
定理 of_ratCast_sub
  条件: (h : Irrational (q - x))
  结论: Irrational x
  证明: of_neg (of_ratCast_add q (by simpa only [sub_eq_add_neg] using h))

Depends on / 依赖: of_neg, of_ratCast_add, sub_eq_add_neg
-/
theorem of_ratCast_sub (h : Irrational (q - x)) : Irrational x :=
  of_neg (of_ratCast_add q (by simpa only [sub_eq_add_neg] using h))
/--
theorem `sub_intCast` / 定理 `sub_intCast`

English:
theorem sub_intCast
  given: (h : Irrational x) (m : Int)
  statement: Irrational (x - m)
  proof: by
  simpa only [Rat.cast_intCast] using h.sub_ratCast m

中文:
定理 sub_intCast
  条件: (h : Irrational x) (m : 整数)
  结论: Irrational (x - m)
  证明: by
  simpa only [Rat.cast_intCast] using h.sub_ratCast m

Depends on / 依赖: Rat.cast_intCast, cast_intCast, h.sub_ratCast, sub_ratCast
-/
theorem sub_intCast (h : Irrational x) (m : Int) : Irrational (x - m) := by
  simpa only [Rat.cast_intCast] using h.sub_ratCast m
/--
theorem `intCast_sub` / 定理 `intCast_sub`

English:
theorem intCast_sub
  given: (h : Irrational x) (m : Int)
  statement: Irrational (m - x)
  proof: by
  simpa only [Rat.cast_intCast] using h.ratCast_sub m

中文:
定理 intCast_sub
  条件: (h : Irrational x) (m : 整数)
  结论: Irrational (m - x)
  证明: by
  simpa only [Rat.cast_intCast] using h.ratCast_sub m

Depends on / 依赖: Rat.cast_intCast, cast_intCast, h.ratCast_sub, ratCast_sub
-/
theorem intCast_sub (h : Irrational x) (m : Int) : Irrational (m - x) := by
  simpa only [Rat.cast_intCast] using h.ratCast_sub m
/--
theorem `of_sub_intCast` / 定理 `of_sub_intCast`

English:
theorem of_sub_intCast
  given: (m : Int) (h : Irrational (x - m))
  statement: Irrational x
  proof: of_sub_ratCast m by rwa [Rat.cast_intCast]

中文:
定理 of_sub_intCast
  条件: (m : 整数) (h : Irrational (x - m))
  结论: Irrational x
  证明: of_sub_ratCast m by rwa [Rat.cast_intCast]

Depends on / 依赖: Rat.cast_intCast, cast_intCast, of_sub_ratCast
-/
theorem of_sub_intCast (m : Int) (h : Irrational (x - m)) : Irrational x :=
of_sub_ratCast m by rwa [Rat.cast_intCast]
/--
theorem `of_intCast_sub` / 定理 `of_intCast_sub`

English:
theorem of_intCast_sub
  given: (m : Int) (h : Irrational (m - x))
  statement: Irrational x
  proof: of_ratCast_sub m by rwa [Rat.cast_intCast]

中文:
定理 of_intCast_sub
  条件: (m : 整数) (h : Irrational (m - x))
  结论: Irrational x
  证明: of_ratCast_sub m by rwa [Rat.cast_intCast]

Depends on / 依赖: Rat.cast_intCast, cast_intCast, of_ratCast_sub
-/
theorem of_intCast_sub (m : Int) (h : Irrational (m - x)) : Irrational x :=
of_ratCast_sub m by rwa [Rat.cast_intCast]
/--
theorem `sub_natCast` / 定理 `sub_natCast`

English:
theorem sub_natCast
  given: (h : Irrational x) (m : Nat)
  statement: Irrational (x - m)
  proof: h.sub_intCast m

中文:
定理 sub_natCast
  条件: (h : Irrational x) (m : 自然数)
  结论: Irrational (x - m)
  证明: h.sub_intCast m

Depends on / 依赖: h.sub_intCast, sub_intCast
-/
theorem sub_natCast (h : Irrational x) (m : Nat) : Irrational (x - m) :=
  h.sub_intCast m
/--
theorem `natCast_sub` / 定理 `natCast_sub`

English:
theorem natCast_sub
  given: (h : Irrational x) (m : Nat)
  statement: Irrational (m - x)
  proof: h.intCast_sub m

中文:
定理 natCast_sub
  条件: (h : Irrational x) (m : 自然数)
  结论: Irrational (m - x)
  证明: h.intCast_sub m

Depends on / 依赖: h.intCast_sub, intCast_sub
-/
theorem natCast_sub (h : Irrational x) (m : Nat) : Irrational (m - x) :=
  h.intCast_sub m
/--
theorem `of_sub_natCast` / 定理 `of_sub_natCast`

English:
theorem of_sub_natCast
  given: (m : Nat) (h : Irrational (x - m))
  statement: Irrational x
  proof: h.of_sub_intCast m

中文:
定理 of_sub_natCast
  条件: (m : 自然数) (h : Irrational (x - m))
  结论: Irrational x
  证明: h.of_sub_intCast m

Depends on / 依赖: h.of_sub_intCast, of_sub_intCast
-/
theorem of_sub_natCast (m : Nat) (h : Irrational (x - m)) : Irrational x :=
  h.of_sub_intCast m
/--
theorem `of_natCast_sub` / 定理 `of_natCast_sub`

English:
theorem of_natCast_sub
  given: (m : Nat) (h : Irrational (m - x))
  statement: Irrational x
  proof: h.of_intCast_sub m

中文:
定理 of_natCast_sub
  条件: (m : 自然数) (h : Irrational (m - x))
  结论: Irrational x
  证明: h.of_intCast_sub m

Depends on / 依赖: h.of_intCast_sub, of_intCast_sub
-/
theorem of_natCast_sub (m : Nat) (h : Irrational (m - x)) : Irrational x :=
  h.of_intCast_sub m


/--
theorem `mul_cases` / 定理 `mul_cases`

English:
theorem mul_cases
  statement: Irrational (x * y) -> Irrational x ∨ Irrational y
  proof: by
  delta Irrational
  contrapose!
  rintro ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩
  exact ⟨rx * ry, cast_mul rx ry⟩

中文:
定理 mul_cases
  结论: Irrational (x * y) -> Irrational x ∨ Irrational y
  证明: by
  delta Irrational
  contrapose!
  rintro ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩
  exact ⟨rx * ry, cast_mul rx ry⟩

Depends on / 依赖: Irrational, cast_mul, contrapose
-/
theorem mul_cases : Irrational (x * y) -> Irrational x ∨ Irrational y := by
  delta Irrational
  contrapose!
  rintro ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩
  exact ⟨rx * ry, cast_mul rx ry⟩

/--
theorem `of_mul_ratCast` / 定理 `of_mul_ratCast`

English:
theorem of_mul_ratCast
  given: (h : Irrational (x * q))
  statement: Irrational x
  proof: h.mul_cases.resolve_right q.not_irrational

中文:
定理 of_mul_ratCast
  条件: (h : Irrational (x * q))
  结论: Irrational x
  证明: h.mul_cases.resolve_right q.not_irrational

Depends on / 依赖: h.mul_cases.resolve_right, mul_cases, not_irrational, q.not_irrational, resolve_right
-/
theorem of_mul_ratCast (h : Irrational (x * q)) : Irrational x :=
  h.mul_cases.resolve_right q.not_irrational
/--
theorem `mul_ratCast` / 定理 `mul_ratCast`

English:
theorem mul_ratCast
  given: (h : Irrational x) {q : Rat} (hq : q != 0)
  statement: Irrational (x * q)
  proof: of_mul_ratCast q⁻¹ by rwa [mul_assoc, ← cast_mul, mul_inv_cancel₀ hq, cast_one, mul_one]

中文:
定理 mul_ratCast
  条件: (h : Irrational x) {q : 有理数} (hq : q != 0)
  结论: Irrational (x * q)
  证明: of_mul_ratCast q⁻¹ by rwa [mul_assoc, ← cast_mul, mul_inv_cancel₀ hq, cast_one, mul_one]

Depends on / 依赖: cast_mul, cast_one, mul_assoc, mul_one, of_mul_ratCast
-/
theorem mul_ratCast (h : Irrational x) {q : Rat} (hq : q != 0) : Irrational (x * q) :=
of_mul_ratCast q⁻¹ by rwa [mul_assoc, ← cast_mul, mul_inv_cancel₀ hq, cast_one, mul_one]
/--
theorem `of_ratCast_mul` / 定理 `of_ratCast_mul`

English:
theorem of_ratCast_mul
  statement: Irrational (q * x) -> Irrational x
  proof: mul_comm x q ▸ of_mul_ratCast q

中文:
定理 of_ratCast_mul
  结论: Irrational (q * x) -> Irrational x
  证明: mul_comm x q ▸ of_mul_ratCast q

Depends on / 依赖: IsMarkovKernel, IsMarkovKernel.IsZeroOrMarkovKernel, IsZeroOrMarkovKernel, mul_comm, of_mul_ratCast
-/
theorem of_ratCast_mul : Irrational (q * x) -> Irrational x :=
  mul_comm x q ▸ of_mul_ratCast q
/--
theorem `ratCast_mul` / 定理 `ratCast_mul`

English:
theorem ratCast_mul
  given: (h : Irrational x) {q : Rat} (hq : q != 0)
  statement: Irrational (q * x)
  proof: mul_comm x q ▸ h.mul_ratCast hq

中文:
定理 ratCast_mul
  条件: (h : Irrational x) {q : 有理数} (hq : q != 0)
  结论: Irrational (q * x)
  证明: mul_comm x q ▸ h.mul_ratCast hq

Depends on / 依赖: IsZeroOrMarkovKernel, IsZeroOrMarkovKernel.isZeroOrProbabilityMeasure, h.mul_ratCast, isZeroOrProbabilityMeasure, mul_comm, mul_ratCast
-/
theorem ratCast_mul (h : Irrational x) {q : Rat} (hq : q != 0) : Irrational (q * x) :=
  mul_comm x q ▸ h.mul_ratCast hq
/--
theorem `of_mul_intCast` / 定理 `of_mul_intCast`

English:
theorem of_mul_intCast
  given: (m : Int) (h : Irrational (x * m))
  statement: Irrational x
  proof: of_mul_ratCast m by rwa [cast_intCast]

中文:
定理 of_mul_intCast
  条件: (m : 整数) (h : Irrational (x * m))
  结论: Irrational x
  证明: of_mul_ratCast m by rwa [cast_intCast]

Depends on / 依赖: cast_intCast, of_mul_ratCast
-/
theorem of_mul_intCast (m : Int) (h : Irrational (x * m)) : Irrational x :=
of_mul_ratCast m by rwa [cast_intCast]
/--
theorem `of_intCast_mul` / 定理 `of_intCast_mul`

English:
theorem of_intCast_mul
  given: (m : Int) (h : Irrational (m * x))
  statement: Irrational x
  proof: of_ratCast_mul m by rwa [cast_intCast]

中文:
定理 of_intCast_mul
  条件: (m : 整数) (h : Irrational (m * x))
  结论: Irrational x
  证明: of_ratCast_mul m by rwa [cast_intCast]

Depends on / 依赖: IsZeroOrMarkovKernel, IsZeroOrMarkovKernel.isFiniteKernel, cast_intCast, isFiniteKernel, of_ratCast_mul
-/
theorem of_intCast_mul (m : Int) (h : Irrational (m * x)) : Irrational x :=
of_ratCast_mul m by rwa [cast_intCast]
/--
theorem `mul_intCast` / 定理 `mul_intCast`

English:
theorem mul_intCast
  given: (h : Irrational x) {m : Int} (hm : m != 0)
  statement: Irrational (x * m)
  proof: by
  rw [← cast_intCast]
  refine h.mul_ratCast ?_
  rwa [Int.cast_ne_zero]

中文:
定理 mul_intCast
  条件: (h : Irrational x) {m : 整数} (hm : m != 0)
  结论: Irrational (x * m)
  证明: by
  rw [← cast_intCast]
  refine h.mul_ratCast ?_
  rwa [Int.cast_ne_zero]

Depends on / 依赖: Int.cast_ne_zero, cast_intCast, cast_ne_zero, h.mul_ratCast, mul_ratCast
-/
theorem mul_intCast (h : Irrational x) {m : Int} (hm : m != 0) : Irrational (x * m) := by
  rw [← cast_intCast]
  refine h.mul_ratCast ?_
  rwa [Int.cast_ne_zero]
/--
theorem `intCast_mul` / 定理 `intCast_mul`

English:
theorem intCast_mul
  given: (h : Irrational x) {m : Int} (hm : m != 0)
  statement: Irrational (m * x)
  proof: mul_comm x m ▸ h.mul_intCast hm

中文:
定理 intCast_mul
  条件: (h : Irrational x) {m : 整数} (hm : m != 0)
  结论: Irrational (m * x)
  证明: mul_comm x m ▸ h.mul_intCast hm

Depends on / 依赖: h.mul_intCast, mul_comm, mul_intCast
-/
theorem intCast_mul (h : Irrational x) {m : Int} (hm : m != 0) : Irrational (m * x) :=
  mul_comm x m ▸ h.mul_intCast hm
/--
theorem `of_mul_natCast` / 定理 `of_mul_natCast`

English:
theorem of_mul_natCast
  given: (m : Nat) (h : Irrational (x * m))
  statement: Irrational x
  proof: h.of_mul_intCast m

中文:
定理 of_mul_natCast
  条件: (m : 自然数) (h : Irrational (x * m))
  结论: Irrational x
  证明: h.of_mul_intCast m

Depends on / 依赖: h.of_mul_intCast, of_mul_intCast
-/
theorem of_mul_natCast (m : Nat) (h : Irrational (x * m)) : Irrational x :=
  h.of_mul_intCast m
/--
theorem `of_natCast_mul` / 定理 `of_natCast_mul`

English:
theorem of_natCast_mul
  given: (m : Nat) (h : Irrational (m * x))
  statement: Irrational x
  proof: h.of_intCast_mul m

中文:
定理 of_natCast_mul
  条件: (m : 自然数) (h : Irrational (m * x))
  结论: Irrational x
  证明: h.of_intCast_mul m

Depends on / 依赖: h.of_intCast_mul, of_intCast_mul
-/
theorem of_natCast_mul (m : Nat) (h : Irrational (m * x)) : Irrational x :=
  h.of_intCast_mul m
/--
theorem `mul_natCast` / 定理 `mul_natCast`

English:
theorem mul_natCast
  given: (h : Irrational x) {m : Nat} (hm : m != 0)
  statement: Irrational (x * m)
  proof: h.mul_intCast Int.natCast_ne_zero.2 hm

中文:
定理 mul_natCast
  条件: (h : Irrational x) {m : 自然数} (hm : m != 0)
  结论: Irrational (x * m)
  证明: h.mul_intCast Int.natCast_ne_zero.2 hm

Depends on / 依赖: Int.natCast_ne_zero, h.mul_intCast, mul_intCast, natCast_ne_zero
-/
theorem mul_natCast (h : Irrational x) {m : Nat} (hm : m != 0) : Irrational (x * m) :=
h.mul_intCast Int.natCast_ne_zero.2 hm
/--
theorem `natCast_mul` / 定理 `natCast_mul`

English:
theorem natCast_mul
  given: (h : Irrational x) {m : Nat} (hm : m != 0)
  statement: Irrational (m * x)
  proof: h.intCast_mul Int.natCast_ne_zero.2 hm

中文:
定理 natCast_mul
  条件: (h : Irrational x) {m : 自然数} (hm : m != 0)
  结论: Irrational (m * x)
  证明: h.intCast_mul Int.natCast_ne_zero.2 hm

Depends on / 依赖: Int.natCast_ne_zero, h.intCast_mul, intCast_mul, natCast_ne_zero
-/
theorem natCast_mul (h : Irrational x) {m : Nat} (hm : m != 0) : Irrational (m * x) :=
h.intCast_mul Int.natCast_ne_zero.2 hm


/--
theorem `of_inv` / 定理 `of_inv`

English:
theorem of_inv
  given: (h : Irrational x⁻¹)
  statement: Irrational x
  proof: fun ⟨q, hq⟩ => h hq ▸ ⟨q⁻¹, q.cast_inv⟩

中文:
定理 of_inv
  条件: (h : Irrational x⁻¹)
  结论: Irrational x
  证明: fun ⟨q, hq⟩ => h hq ▸ ⟨q⁻¹, q.cast_inv⟩

Depends on / 依赖: cast_inv, q.cast_inv
-/
theorem of_inv (h : Irrational x⁻¹) : Irrational x := fun ⟨q, hq⟩ => h hq ▸ ⟨q⁻¹, q.cast_inv⟩

/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  given: (h : Irrational x)
  statement: Irrational x⁻¹
  proof: of_inv by rwa [inv_inv]

中文:
定理 inv
  条件: (h : Irrational x)
  结论: Irrational x⁻¹
  证明: of_inv by rwa [inv_inv]
-/
protected theorem inv (h : Irrational x) : Irrational x⁻¹ :=
of_inv by rwa [inv_inv]



/--
theorem `div_cases` / 定理 `div_cases`

English:
theorem div_cases
  given: (h : Irrational (x / y))
  statement: Irrational x ∨ Irrational y
  proof: h.mul_cases.imp id of_inv

中文:
定理 div_cases
  条件: (h : Irrational (x / y))
  结论: Irrational x ∨ Irrational y
  证明: h.mul_cases.imp id of_inv

Depends on / 依赖: h.mul_cases.imp, mul_cases, of_inv
-/
theorem div_cases (h : Irrational (x / y)) : Irrational x ∨ Irrational y :=
  h.mul_cases.imp id of_inv

/--
theorem `of_ratCast_div` / 定理 `of_ratCast_div`

English:
theorem of_ratCast_div
  given: (h : Irrational (q / x))
  statement: Irrational x
  proof: (h.of_ratCast_mul q).of_inv

中文:
定理 of_ratCast_div
  条件: (h : Irrational (q / x))
  结论: Irrational x
  证明: (h.of_ratCast_mul q).of_inv

Depends on / 依赖: h.of_ratCast_mul, of_inv, of_ratCast_mul
-/
theorem of_ratCast_div (h : Irrational (q / x)) : Irrational x :=
  (h.of_ratCast_mul q).of_inv
/--
theorem `of_div_ratCast` / 定理 `of_div_ratCast`

English:
theorem of_div_ratCast
  given: (h : Irrational (x / q))
  statement: Irrational x
  proof: h.div_cases.resolve_right q.not_irrational

中文:
定理 of_div_ratCast
  条件: (h : Irrational (x / q))
  结论: Irrational x
  证明: h.div_cases.resolve_right q.not_irrational

Depends on / 依赖: div_cases, h.div_cases.resolve_right, not_irrational, q.not_irrational, resolve_right
-/
theorem of_div_ratCast (h : Irrational (x / q)) : Irrational x :=
  h.div_cases.resolve_right q.not_irrational
/--
theorem `ratCast_div` / 定理 `ratCast_div`

English:
theorem ratCast_div
  given: (h : Irrational x) {q : Rat} (hq : q != 0)
  statement: Irrational (q / x)
  proof: h.inv.ratCast_mul hq

中文:
定理 ratCast_div
  条件: (h : Irrational x) {q : 有理数} (hq : q != 0)
  结论: Irrational (q / x)
  证明: h.inv.ratCast_mul hq

Depends on / 依赖: h.inv.ratCast_mul, ratCast_mul
-/
theorem ratCast_div (h : Irrational x) {q : Rat} (hq : q != 0) : Irrational (q / x) :=
  h.inv.ratCast_mul hq
/--
theorem `div_ratCast` / 定理 `div_ratCast`

English:
theorem div_ratCast
  given: (h : Irrational x) {q : Rat} (hq : q != 0)
  statement: Irrational (x / q)
  proof: by
  rw [div_eq_mul_inv]; rw [← cast_inv]
  exact h.mul_ratCast (inv_ne_zero hq)

中文:
定理 div_ratCast
  条件: (h : Irrational x) {q : 有理数} (hq : q != 0)
  结论: Irrational (x / q)
  证明: by
  rw [div_eq_mul_inv]; rw [← cast_inv]
  exact h.mul_ratCast (inv_ne_zero hq)

Depends on / 依赖: cast_inv, div_eq_mul_inv, h.mul_ratCast, inv_ne_zero, mul_ratCast
-/
theorem div_ratCast (h : Irrational x) {q : Rat} (hq : q != 0) : Irrational (x / q) := by
  rw [div_eq_mul_inv]; rw [← cast_inv]
  exact h.mul_ratCast (inv_ne_zero hq)
/--
theorem `of_intCast_div` / 定理 `of_intCast_div`

English:
theorem of_intCast_div
  given: (m : Int) (h : Irrational (m / x))
  statement: Irrational x
  proof: h.div_cases.resolve_left m.not_irrational

中文:
定理 of_intCast_div
  条件: (m : 整数) (h : Irrational (m / x))
  结论: Irrational x
  证明: h.div_cases.resolve_left m.not_irrational

Depends on / 依赖: div_cases, h.div_cases.resolve_left, m.not_irrational, not_irrational, resolve_left
-/
theorem of_intCast_div (m : Int) (h : Irrational (m / x)) : Irrational x :=
  h.div_cases.resolve_left m.not_irrational
/--
theorem `of_div_intCast` / 定理 `of_div_intCast`

English:
theorem of_div_intCast
  given: (m : Int) (h : Irrational (x / m))
  statement: Irrational x
  proof: h.div_cases.resolve_right m.not_irrational

中文:
定理 of_div_intCast
  条件: (m : 整数) (h : Irrational (x / m))
  结论: Irrational x
  证明: h.div_cases.resolve_right m.not_irrational

Depends on / 依赖: div_cases, h.div_cases.resolve_right, m.not_irrational, not_irrational, resolve_right
-/
theorem of_div_intCast (m : Int) (h : Irrational (x / m)) : Irrational x :=
  h.div_cases.resolve_right m.not_irrational
/--
theorem `intCast_div` / 定理 `intCast_div`

English:
theorem intCast_div
  given: (h : Irrational x) {m : Int} (hm : m != 0)
  statement: Irrational (m / x)
  proof: h.inv.intCast_mul hm

中文:
定理 intCast_div
  条件: (h : Irrational x) {m : 整数} (hm : m != 0)
  结论: Irrational (m / x)
  证明: h.inv.intCast_mul hm

Depends on / 依赖: h.inv.intCast_mul, intCast_mul
-/
theorem intCast_div (h : Irrational x) {m : Int} (hm : m != 0) : Irrational (m / x) :=
  h.inv.intCast_mul hm
/--
theorem `div_intCast` / 定理 `div_intCast`

English:
theorem div_intCast
  given: (h : Irrational x) {m : Int} (hm : m != 0)
  statement: Irrational (x / m)
  proof: by
  rw [← cast_intCast]
  refine h.div_ratCast ?_
  rwa [Int.cast_ne_zero]

中文:
定理 div_intCast
  条件: (h : Irrational x) {m : 整数} (hm : m != 0)
  结论: Irrational (x / m)
  证明: by
  rw [← cast_intCast]
  refine h.div_ratCast ?_
  rwa [Int.cast_ne_zero]

Depends on / 依赖: Int.cast_ne_zero, cast_intCast, cast_ne_zero, div_ratCast, h.div_ratCast
-/
theorem div_intCast (h : Irrational x) {m : Int} (hm : m != 0) : Irrational (x / m) := by
  rw [← cast_intCast]
  refine h.div_ratCast ?_
  rwa [Int.cast_ne_zero]
/--
theorem `of_natCast_div` / 定理 `of_natCast_div`

English:
theorem of_natCast_div
  given: (m : Nat) (h : Irrational (m / x))
  statement: Irrational x
  proof: h.of_intCast_div m

中文:
定理 of_natCast_div
  条件: (m : 自然数) (h : Irrational (m / x))
  结论: Irrational x
  证明: h.of_intCast_div m

Depends on / 依赖: h.of_intCast_div, of_intCast_div
-/
theorem of_natCast_div (m : Nat) (h : Irrational (m / x)) : Irrational x :=
  h.of_intCast_div m
/--
theorem `of_div_natCast` / 定理 `of_div_natCast`

English:
theorem of_div_natCast
  given: (m : Nat) (h : Irrational (x / m))
  statement: Irrational x
  proof: h.of_div_intCast m

中文:
定理 of_div_natCast
  条件: (m : 自然数) (h : Irrational (x / m))
  结论: Irrational x
  证明: h.of_div_intCast m

Depends on / 依赖: h.of_div_intCast, of_div_intCast
-/
theorem of_div_natCast (m : Nat) (h : Irrational (x / m)) : Irrational x :=
  h.of_div_intCast m
/--
theorem `natCast_div` / 定理 `natCast_div`

English:
theorem natCast_div
  given: (h : Irrational x) {m : Nat} (hm : m != 0)
  statement: Irrational (m / x)
  proof: h.inv.natCast_mul hm

中文:
定理 natCast_div
  条件: (h : Irrational x) {m : 自然数} (hm : m != 0)
  结论: Irrational (m / x)
  证明: h.inv.natCast_mul hm

Depends on / 依赖: IsFiniteKernel, IsFiniteKernel.isSFiniteKernel, h.inv.natCast_mul, isSFiniteKernel, natCast_mul
-/
theorem natCast_div (h : Irrational x) {m : Nat} (hm : m != 0) : Irrational (m / x) :=
  h.inv.natCast_mul hm
/--
theorem `div_natCast` / 定理 `div_natCast`

English:
theorem div_natCast
  given: (h : Irrational x) {m : Nat} (hm : m != 0)
  statement: Irrational (x / m)
  proof: h.div_intCast by rwa [Int.natCast_ne_zero]

中文:
定理 div_natCast
  条件: (h : Irrational x) {m : 自然数} (hm : m != 0)
  结论: Irrational (x / m)
  证明: h.div_intCast by rwa [Int.natCast_ne_zero]

Depends on / 依赖: Int.natCast_ne_zero, div_intCast, h.div_intCast, natCast_ne_zero
-/
theorem div_natCast (h : Irrational x) {m : Nat} (hm : m != 0) : Irrational (x / m) :=
h.div_intCast by rwa [Int.natCast_ne_zero]
/--
theorem `of_one_div` / 定理 `of_one_div`

English:
theorem of_one_div
  given: (h : Irrational (1 / x))
  statement: Irrational x
  proof: of_ratCast_div 1 by rwa [cast_one]

中文:
定理 of_one_div
  条件: (h : Irrational (1 / x))
  结论: Irrational x
  证明: of_ratCast_div 1 by rwa [cast_one]

Depends on / 依赖: cast_one, of_ratCast_div
-/
theorem of_one_div (h : Irrational (1 / x)) : Irrational x :=
of_ratCast_div 1 by rwa [cast_one]



/--
theorem `of_mul_self` / 定理 `of_mul_self`

English:
theorem of_mul_self
  given: (h : Irrational (x * x))
  statement: Irrational x
  proof: h.mul_cases.elim id id

中文:
定理 of_mul_self
  条件: (h : Irrational (x * x))
  结论: Irrational x
  证明: h.mul_cases.elim id id

Depends on / 依赖: h.mul_cases.elim, mul_cases
-/
theorem of_mul_self (h : Irrational (x * x)) : Irrational x :=
  h.mul_cases.elim id id

/--
theorem `of_pow` / 定理 `of_pow`

English:
theorem of_pow
  statement: forall n : Nat, Irrational (x ^ n) -> Irrational x

中文:
定理 of_pow
  结论: 对任意 n : 自然数, Irrational (x ^ n) -> Irrational x
-/
theorem of_pow : forall n : Nat, Irrational (x ^ n) -> Irrational x
  | 0 => fun h => by
    rw [pow_zero] at h
    exact (h ⟨1, cast_one⟩).elim
  | n + 1 => fun h => by
    rw [pow_succ] at h
    exact h.mul_cases.elim (of_pow n) id

open Int in
/--
theorem `of_zpow` / 定理 `of_zpow`

English:
theorem of_zpow
  statement: forall m : Int, Irrational (x ^ m) -> Irrational x

中文:
定理 of_zpow
  结论: 对任意 m : 整数, Irrational (x ^ m) -> Irrational x
-/
theorem of_zpow : forall m : Int, Irrational (x ^ m) -> Irrational x
  | (n : Nat) => fun h => by
    rw [zpow_natCast] at h
    exact h.of_pow _
  | -[n+1] => fun h => by
    rw [zpow_negSucc] at h
    exact h.of_inv.of_pow _

end Irrational

section Polynomial

open Polynomial

variable (x : Real) (p : Int[X])

/--
theorem `one_lt_natDegree_of_irrational_root` / 定理 `one_lt_natDegree_of_irrational_root`

English:
theorem one_lt_natDegree_of_irrational_root
  statement: (hx : Irrational x) (p_nonzero : p != 0)
  proof: by
  by_contra rid
  rcases exists_eq_X_add_C_of_natDegree_le_one (not_lt.1 rid) with ⟨a, b, rfl⟩
  clear rid
  have : (a : Real) * x = -b := by simpa [eq_neg_iff_add_eq_zero] using x_is_root
  rcases em (a = 0) with (rfl | ha)
  · obtain rfl : b = 0 := by simpa
    simp at p_nonzero
  · rw [mul_comm, ← eq_div_iff_mul_eq, eq_comm] at this
    · refine hx ⟨-b / a, ?_⟩
      assumption_mod_cast
    · assumption_mod_cast

中文:
定理 one_lt_natDegree_of_irrational_root
  结论: (hx : Irrational x) (p_nonzero : p != 0)
  证明: by
  by_contra rid
  rcases exists_eq_X_add_C_of_natDegree_le_one (not_lt.1 rid) with ⟨a, b, rfl⟩
  clear rid
  have : (a : Real) * x = -b := by simpa [eq_neg_iff_add_eq_zero] using x_is_root
  rcases em (a = 0) with (rfl | ha)
  · obtain rfl : b = 0 := by simpa
    simp at p_nonzero
  · rw [mul_comm, ← eq_div_iff_mul_eq, eq_comm] at this
    · refine hx ⟨-b / a, ?_⟩
      assumption_mod_cast
    · assumption_mod_cast

Depends on / 依赖: assumption_mod_cast, eq_comm, eq_div_iff_mul_eq, eq_neg_iff_add_eq_zero, exists_eq_X_add_C_of_natDegree_le_one, mul_comm, not_lt, p_nonzero, x_is_root
-/
theorem one_lt_natDegree_of_irrational_root (hx : Irrational x) (p_nonzero : p != 0)
    (x_is_root : aeval x p = 0) : 1 < p.natDegree := by
  by_contra rid
  rcases exists_eq_X_add_C_of_natDegree_le_one (not_lt.1 rid) with ⟨a, b, rfl⟩
  clear rid
  have : (a : Real) * x = -b := by simpa [eq_neg_iff_add_eq_zero] using x_is_root
  rcases em (a = 0) with (rfl | ha)
  · obtain rfl : b = 0 := by simpa
    simp at p_nonzero
  · rw [mul_comm, ← eq_div_iff_mul_eq, eq_comm] at this
    · refine hx ⟨-b / a, ?_⟩
      assumption_mod_cast
    · assumption_mod_cast

end Polynomial

section

variable {q : Rat} {m : Int} {n : Nat} {x : Real}

open Irrational

/-!
### Simplification lemmas about operations
-/


@[simp]
/--
theorem `irrational_ratCast_add_iff` / 定理 `irrational_ratCast_add_iff`

English:
theorem irrational_ratCast_add_iff
  statement: Irrational (q + x) ↔ Irrational x
  proof: ⟨of_ratCast_add q, ratCast_add q⟩
@[simp]

中文:
定理 irrational_ratCast_add_iff
  结论: Irrational (q + x) ↔ Irrational x
  证明: ⟨of_ratCast_add q, ratCast_add q⟩
@[simp]

Depends on / 依赖: of_ratCast_add, ratCast_add
-/
theorem irrational_ratCast_add_iff : Irrational (q + x) ↔ Irrational x :=
  ⟨of_ratCast_add q, ratCast_add q⟩
@[simp]
/--
theorem `irrational_intCast_add_iff` / 定理 `irrational_intCast_add_iff`

English:
theorem irrational_intCast_add_iff
  statement: Irrational (m + x) ↔ Irrational x
  proof: ⟨of_intCast_add m, fun h => h.intCast_add m⟩
@[simp]

中文:
定理 irrational_intCast_add_iff
  结论: Irrational (m + x) ↔ Irrational x
  证明: ⟨of_intCast_add m, fun h => h.intCast_add m⟩
@[simp]

Depends on / 依赖: h.intCast_add, intCast_add, of_intCast_add
-/
theorem irrational_intCast_add_iff : Irrational (m + x) ↔ Irrational x :=
  ⟨of_intCast_add m, fun h => h.intCast_add m⟩
@[simp]
/--
theorem `irrational_natCast_add_iff` / 定理 `irrational_natCast_add_iff`

English:
theorem irrational_natCast_add_iff
  statement: Irrational (n + x) ↔ Irrational x
  proof: ⟨of_natCast_add n, fun h => h.natCast_add n⟩
@[simp]

中文:
定理 irrational_natCast_add_iff
  结论: Irrational (n + x) ↔ Irrational x
  证明: ⟨of_natCast_add n, fun h => h.natCast_add n⟩
@[simp]

Depends on / 依赖: h.natCast_add, natCast_add, of_natCast_add
-/
theorem irrational_natCast_add_iff : Irrational (n + x) ↔ Irrational x :=
  ⟨of_natCast_add n, fun h => h.natCast_add n⟩
@[simp]
/--
theorem `irrational_add_ratCast_iff` / 定理 `irrational_add_ratCast_iff`

English:
theorem irrational_add_ratCast_iff
  statement: Irrational (x + q) ↔ Irrational x
  proof: ⟨of_add_ratCast q, add_ratCast q⟩
@[simp]

中文:
定理 irrational_add_ratCast_iff
  结论: Irrational (x + q) ↔ Irrational x
  证明: ⟨of_add_ratCast q, add_ratCast q⟩
@[simp]

Depends on / 依赖: add_ratCast, of_add_ratCast
-/
theorem irrational_add_ratCast_iff : Irrational (x + q) ↔ Irrational x :=
  ⟨of_add_ratCast q, add_ratCast q⟩
@[simp]
/--
theorem `irrational_add_intCast_iff` / 定理 `irrational_add_intCast_iff`

English:
theorem irrational_add_intCast_iff
  statement: Irrational (x + m) ↔ Irrational x
  proof: ⟨of_add_intCast m, fun h => h.add_intCast m⟩
@[simp]

中文:
定理 irrational_add_intCast_iff
  结论: Irrational (x + m) ↔ Irrational x
  证明: ⟨of_add_intCast m, fun h => h.add_intCast m⟩
@[simp]

Depends on / 依赖: Function, Function.comp_def, Function.diag_def, add_intCast, comp_def, deterministic_comp_deterministic, deterministic_prod_deterministic, diag_def, h.add_intCast, of_add_intCast, parallelComp_comp_copy, simp_rw
-/
theorem irrational_add_intCast_iff : Irrational (x + m) ↔ Irrational x :=
  ⟨of_add_intCast m, fun h => h.add_intCast m⟩
@[simp]
/--
theorem `irrational_add_natCast_iff` / 定理 `irrational_add_natCast_iff`

English:
theorem irrational_add_natCast_iff
  statement: Irrational (x + n) ↔ Irrational x
  proof: ⟨of_add_natCast n, fun h => h.add_natCast n⟩
@[simp]

中文:
定理 irrational_add_natCast_iff
  结论: Irrational (x + n) ↔ Irrational x
  证明: ⟨of_add_natCast n, fun h => h.add_natCast n⟩
@[simp]

Depends on / 依赖: add_natCast, h.add_natCast, of_add_natCast
-/
theorem irrational_add_natCast_iff : Irrational (x + n) ↔ Irrational x :=
  ⟨of_add_natCast n, fun h => h.add_natCast n⟩
@[simp]
/--
theorem `irrational_ratCast_sub_iff` / 定理 `irrational_ratCast_sub_iff`

English:
theorem irrational_ratCast_sub_iff
  statement: Irrational (q - x) ↔ Irrational x
  proof: ⟨of_ratCast_sub q, ratCast_sub q⟩
@[simp]

中文:
定理 irrational_ratCast_sub_iff
  结论: Irrational (q - x) ↔ Irrational x
  证明: ⟨of_ratCast_sub q, ratCast_sub q⟩
@[simp]

Depends on / 依赖: of_ratCast_sub, ratCast_sub
-/
theorem irrational_ratCast_sub_iff : Irrational (q - x) ↔ Irrational x :=
  ⟨of_ratCast_sub q, ratCast_sub q⟩
@[simp]
/--
theorem `irrational_intCast_sub_iff` / 定理 `irrational_intCast_sub_iff`

English:
theorem irrational_intCast_sub_iff
  statement: Irrational (m - x) ↔ Irrational x
  proof: ⟨of_intCast_sub m, fun h => h.intCast_sub m⟩
@[simp]

中文:
定理 irrational_intCast_sub_iff
  结论: Irrational (m - x) ↔ Irrational x
  证明: ⟨of_intCast_sub m, fun h => h.intCast_sub m⟩
@[simp]

Depends on / 依赖: h.intCast_sub, intCast_sub, of_intCast_sub
-/
theorem irrational_intCast_sub_iff : Irrational (m - x) ↔ Irrational x :=
  ⟨of_intCast_sub m, fun h => h.intCast_sub m⟩
@[simp]
/--
theorem `irrational_natCast_sub_iff` / 定理 `irrational_natCast_sub_iff`

English:
theorem irrational_natCast_sub_iff
  statement: Irrational (n - x) ↔ Irrational x
  proof: ⟨of_natCast_sub n, fun h => h.natCast_sub n⟩
@[simp]

中文:
定理 irrational_natCast_sub_iff
  结论: Irrational (n - x) ↔ Irrational x
  证明: ⟨of_natCast_sub n, fun h => h.natCast_sub n⟩
@[simp]

Depends on / 依赖: h.natCast_sub, natCast_sub, of_natCast_sub
-/
theorem irrational_natCast_sub_iff : Irrational (n - x) ↔ Irrational x :=
  ⟨of_natCast_sub n, fun h => h.natCast_sub n⟩
@[simp]
/--
theorem `irrational_sub_ratCast_iff` / 定理 `irrational_sub_ratCast_iff`

English:
theorem irrational_sub_ratCast_iff
  statement: Irrational (x - q) ↔ Irrational x
  proof: ⟨of_sub_ratCast q, sub_ratCast q⟩
@[simp]

中文:
定理 irrational_sub_ratCast_iff
  结论: Irrational (x - q) ↔ Irrational x
  证明: ⟨of_sub_ratCast q, sub_ratCast q⟩
@[simp]

Depends on / 依赖: of_sub_ratCast, sub_ratCast
-/
theorem irrational_sub_ratCast_iff : Irrational (x - q) ↔ Irrational x :=
  ⟨of_sub_ratCast q, sub_ratCast q⟩
@[simp]
/--
theorem `irrational_sub_intCast_iff` / 定理 `irrational_sub_intCast_iff`

English:
theorem irrational_sub_intCast_iff
  statement: Irrational (x - m) ↔ Irrational x
  proof: ⟨of_sub_intCast m, fun h => h.sub_intCast m⟩
@[simp]

中文:
定理 irrational_sub_intCast_iff
  结论: Irrational (x - m) ↔ Irrational x
  证明: ⟨of_sub_intCast m, fun h => h.sub_intCast m⟩
@[simp]

Depends on / 依赖: h.sub_intCast, isDeterministic_iff_isZeroOneMeasure, of_sub_intCast, sub_intCast
-/
theorem irrational_sub_intCast_iff : Irrational (x - m) ↔ Irrational x :=
  ⟨of_sub_intCast m, fun h => h.sub_intCast m⟩
@[simp]
/--
theorem `irrational_sub_natCast_iff` / 定理 `irrational_sub_natCast_iff`

English:
theorem irrational_sub_natCast_iff
  statement: Irrational (x - n) ↔ Irrational x
  proof: ⟨of_sub_natCast n, fun h => h.sub_natCast n⟩
@[simp]

中文:
定理 irrational_sub_natCast_iff
  结论: Irrational (x - n) ↔ Irrational x
  证明: ⟨of_sub_natCast n, fun h => h.sub_natCast n⟩
@[simp]

Depends on / 依赖: h.sub_natCast, of_sub_natCast, sub_natCast
-/
theorem irrational_sub_natCast_iff : Irrational (x - n) ↔ Irrational x :=
  ⟨of_sub_natCast n, fun h => h.sub_natCast n⟩
@[simp]
/--
theorem `irrational_neg_iff` / 定理 `irrational_neg_iff`

English:
theorem irrational_neg_iff
  statement: Irrational (-x) ↔ Irrational x
  proof: ⟨of_neg, Irrational.neg⟩

@[simp]

中文:
定理 irrational_neg_iff
  结论: Irrational (-x) ↔ Irrational x
  证明: ⟨of_neg, Irrational.neg⟩

@[simp]

Depends on / 依赖: Irrational, Irrational.neg, of_neg
-/
theorem irrational_neg_iff : Irrational (-x) ↔ Irrational x :=
  ⟨of_neg, Irrational.neg⟩

@[simp]
/--
theorem `irrational_inv_iff` / 定理 `irrational_inv_iff`

English:
theorem irrational_inv_iff
  statement: Irrational x⁻¹ ↔ Irrational x
  proof: ⟨of_inv, Irrational.inv⟩

@[simp]

中文:
定理 irrational_inv_iff
  结论: Irrational x⁻¹ ↔ Irrational x
  证明: ⟨of_inv, Irrational.inv⟩

@[simp]

Depends on / 依赖: Irrational, Irrational.inv, of_inv
-/
theorem irrational_inv_iff : Irrational x⁻¹ ↔ Irrational x :=
  ⟨of_inv, Irrational.inv⟩

@[simp]
/--
theorem `irrational_ratCast_mul_iff` / 定理 `irrational_ratCast_mul_iff`

English:
theorem irrational_ratCast_mul_iff
  statement: Irrational (q * x) ↔ q != 0 ∧ Irrational x
  proof: ⟨fun h => ⟨Rat.cast_ne_zero.1 left_ne_zero_of_mul h.ne_zero, h.of_ratCast_mul q⟩, fun h =>
    h.2.ratCast_mul h.1⟩
@[simp]

中文:
定理 irrational_ratCast_mul_iff
  结论: Irrational (q * x) ↔ q != 0 ∧ Irrational x
  证明: ⟨fun h => ⟨Rat.cast_ne_zero.1 left_ne_zero_of_mul h.ne_zero, h.of_ratCast_mul q⟩, fun h =>
    h.2.ratCast_mul h.1⟩
@[simp]

Depends on / 依赖: Rat.cast_ne_zero, cast_ne_zero, h.ne_zero, h.of_ratCast_mul, left_ne_zero_of_mul, ne_zero, of_ratCast_mul, ratCast_mul
-/
theorem irrational_ratCast_mul_iff : Irrational (q * x) ↔ q != 0 ∧ Irrational x :=
⟨fun h => ⟨Rat.cast_ne_zero.1 left_ne_zero_of_mul h.ne_zero, h.of_ratCast_mul q⟩, fun h =>
    h.2.ratCast_mul h.1⟩
@[simp]
/--
theorem `irrational_mul_ratCast_iff` / 定理 `irrational_mul_ratCast_iff`

English:
theorem irrational_mul_ratCast_iff
  statement: Irrational (x * q) ↔ q != 0 ∧ Irrational x
  proof: by
  rw [mul_comm]; rw [irrational_ratCast_mul_iff]
@[simp]

中文:
定理 irrational_mul_ratCast_iff
  结论: Irrational (x * q) ↔ q != 0 ∧ Irrational x
  证明: by
  rw [mul_comm]; rw [irrational_ratCast_mul_iff]
@[simp]

Depends on / 依赖: irrational_ratCast_mul_iff, mul_comm
-/
theorem irrational_mul_ratCast_iff : Irrational (x * q) ↔ q != 0 ∧ Irrational x := by
  rw [mul_comm]; rw [irrational_ratCast_mul_iff]
@[simp]
/--
theorem `irrational_intCast_mul_iff` / 定理 `irrational_intCast_mul_iff`

English:
theorem irrational_intCast_mul_iff
  statement: Irrational (m * x) ↔ m != 0 ∧ Irrational x
  proof: by
  rw [← cast_intCast]; rw [irrational_ratCast_mul_iff]; rw [Int.cast_ne_zero]
@[simp]

中文:
定理 irrational_intCast_mul_iff
  结论: Irrational (m * x) ↔ m != 0 ∧ Irrational x
  证明: by
  rw [← cast_intCast]; rw [irrational_ratCast_mul_iff]; rw [Int.cast_ne_zero]
@[simp]

Depends on / 依赖: Int.cast_ne_zero, cast_intCast, cast_ne_zero, irrational_ratCast_mul_iff
-/
theorem irrational_intCast_mul_iff : Irrational (m * x) ↔ m != 0 ∧ Irrational x := by
  rw [← cast_intCast]; rw [irrational_ratCast_mul_iff]; rw [Int.cast_ne_zero]
@[simp]
/--
theorem `irrational_mul_intCast_iff` / 定理 `irrational_mul_intCast_iff`

English:
theorem irrational_mul_intCast_iff
  statement: Irrational (x * m) ↔ m != 0 ∧ Irrational x
  proof: by
  rw [← cast_intCast]; rw [irrational_mul_ratCast_iff]; rw [Int.cast_ne_zero]
@[simp]

中文:
定理 irrational_mul_intCast_iff
  结论: Irrational (x * m) ↔ m != 0 ∧ Irrational x
  证明: by
  rw [← cast_intCast]; rw [irrational_mul_ratCast_iff]; rw [Int.cast_ne_zero]
@[simp]

Depends on / 依赖: Int.cast_ne_zero, cast_intCast, cast_ne_zero, irrational_mul_ratCast_iff
-/
theorem irrational_mul_intCast_iff : Irrational (x * m) ↔ m != 0 ∧ Irrational x := by
  rw [← cast_intCast]; rw [irrational_mul_ratCast_iff]; rw [Int.cast_ne_zero]
@[simp]
/--
theorem `irrational_natCast_mul_iff` / 定理 `irrational_natCast_mul_iff`

English:
theorem irrational_natCast_mul_iff
  statement: Irrational (n * x) ↔ n != 0 ∧ Irrational x
  proof: by
  rw [← cast_natCast]; rw [irrational_ratCast_mul_iff]; rw [Nat.cast_ne_zero]
@[simp]

中文:
定理 irrational_natCast_mul_iff
  结论: Irrational (n * x) ↔ n != 0 ∧ Irrational x
  证明: by
  rw [← cast_natCast]; rw [irrational_ratCast_mul_iff]; rw [Nat.cast_ne_zero]
@[simp]

Depends on / 依赖: Nat.cast_ne_zero, cast_natCast, cast_ne_zero, irrational_ratCast_mul_iff
-/
theorem irrational_natCast_mul_iff : Irrational (n * x) ↔ n != 0 ∧ Irrational x := by
  rw [← cast_natCast]; rw [irrational_ratCast_mul_iff]; rw [Nat.cast_ne_zero]
@[simp]
/--
theorem `irrational_mul_natCast_iff` / 定理 `irrational_mul_natCast_iff`

English:
theorem irrational_mul_natCast_iff
  statement: Irrational (x * n) ↔ n != 0 ∧ Irrational x
  proof: by
  rw [← cast_natCast]; rw [irrational_mul_ratCast_iff]; rw [Nat.cast_ne_zero]
@[simp]

中文:
定理 irrational_mul_natCast_iff
  结论: Irrational (x * n) ↔ n != 0 ∧ Irrational x
  证明: by
  rw [← cast_natCast]; rw [irrational_mul_ratCast_iff]; rw [Nat.cast_ne_zero]
@[simp]

Depends on / 依赖: Nat.cast_ne_zero, cast_natCast, cast_ne_zero, irrational_mul_ratCast_iff
-/
theorem irrational_mul_natCast_iff : Irrational (x * n) ↔ n != 0 ∧ Irrational x := by
  rw [← cast_natCast]; rw [irrational_mul_ratCast_iff]; rw [Nat.cast_ne_zero]
@[simp]
/--
theorem `irrational_ratCast_div_iff` / 定理 `irrational_ratCast_div_iff`

English:
theorem irrational_ratCast_div_iff
  statement: Irrational (q / x) ↔ q != 0 ∧ Irrational x
  proof: by
  simp [div_eq_mul_inv]
@[simp]

中文:
定理 irrational_ratCast_div_iff
  结论: Irrational (q / x) ↔ q != 0 ∧ Irrational x
  证明: by
  simp [div_eq_mul_inv]
@[simp]

Depends on / 依赖: div_eq_mul_inv
-/
theorem irrational_ratCast_div_iff : Irrational (q / x) ↔ q != 0 ∧ Irrational x := by
  simp [div_eq_mul_inv]
@[simp]
/--
theorem `irrational_div_ratCast_iff` / 定理 `irrational_div_ratCast_iff`

English:
theorem irrational_div_ratCast_iff
  statement: Irrational (x / q) ↔ q != 0 ∧ Irrational x
  proof: by
  rw [div_eq_mul_inv]; rw [← cast_inv]; rw [irrational_mul_ratCast_iff]; rw [Ne]; rw [inv_eq_zero]
@[simp]

中文:
定理 irrational_div_ratCast_iff
  结论: Irrational (x / q) ↔ q != 0 ∧ Irrational x
  证明: by
  rw [div_eq_mul_inv]; rw [← cast_inv]; rw [irrational_mul_ratCast_iff]; rw [Ne]; rw [inv_eq_zero]
@[simp]

Depends on / 依赖: cast_inv, div_eq_mul_inv, inv_eq_zero, irrational_mul_ratCast_iff
-/
theorem irrational_div_ratCast_iff : Irrational (x / q) ↔ q != 0 ∧ Irrational x := by
  rw [div_eq_mul_inv]; rw [← cast_inv]; rw [irrational_mul_ratCast_iff]; rw [Ne]; rw [inv_eq_zero]
@[simp]
/--
theorem `irrational_intCast_div_iff` / 定理 `irrational_intCast_div_iff`

English:
theorem irrational_intCast_div_iff
  statement: Irrational (m / x) ↔ m != 0 ∧ Irrational x
  proof: by
  simp [div_eq_mul_inv]
@[simp]

中文:
定理 irrational_intCast_div_iff
  结论: Irrational (m / x) ↔ m != 0 ∧ Irrational x
  证明: by
  simp [div_eq_mul_inv]
@[simp]

Depends on / 依赖: div_eq_mul_inv
-/
theorem irrational_intCast_div_iff : Irrational (m / x) ↔ m != 0 ∧ Irrational x := by
  simp [div_eq_mul_inv]
@[simp]
/--
theorem `irrational_div_intCast_iff` / 定理 `irrational_div_intCast_iff`

English:
theorem irrational_div_intCast_iff
  statement: Irrational (x / m) ↔ m != 0 ∧ Irrational x
  proof: by
  rw [← cast_intCast]; rw [irrational_div_ratCast_iff]; rw [Int.cast_ne_zero]
@[simp]

中文:
定理 irrational_div_intCast_iff
  结论: Irrational (x / m) ↔ m != 0 ∧ Irrational x
  证明: by
  rw [← cast_intCast]; rw [irrational_div_ratCast_iff]; rw [Int.cast_ne_zero]
@[simp]

Depends on / 依赖: Int.cast_ne_zero, cast_intCast, cast_ne_zero, irrational_div_ratCast_iff
-/
theorem irrational_div_intCast_iff : Irrational (x / m) ↔ m != 0 ∧ Irrational x := by
  rw [← cast_intCast]; rw [irrational_div_ratCast_iff]; rw [Int.cast_ne_zero]
@[simp]
/--
theorem `irrational_natCast_div_iff` / 定理 `irrational_natCast_div_iff`

English:
theorem irrational_natCast_div_iff
  statement: Irrational (n / x) ↔ n != 0 ∧ Irrational x
  proof: by
  simp [div_eq_mul_inv]
@[simp]

中文:
定理 irrational_natCast_div_iff
  结论: Irrational (n / x) ↔ n != 0 ∧ Irrational x
  证明: by
  simp [div_eq_mul_inv]
@[simp]

Depends on / 依赖: div_eq_mul_inv
-/
theorem irrational_natCast_div_iff : Irrational (n / x) ↔ n != 0 ∧ Irrational x := by
  simp [div_eq_mul_inv]
@[simp]
/--
theorem `irrational_div_natCast_iff` / 定理 `irrational_div_natCast_iff`

English:
theorem irrational_div_natCast_iff
  statement: Irrational (x / n) ↔ n != 0 ∧ Irrational x
  proof: by
  rw [← cast_natCast]; rw [irrational_div_ratCast_iff]; rw [Nat.cast_ne_zero]

中文:
定理 irrational_div_natCast_iff
  结论: Irrational (x / n) ↔ n != 0 ∧ Irrational x
  证明: by
  rw [← cast_natCast]; rw [irrational_div_ratCast_iff]; rw [Nat.cast_ne_zero]

Depends on / 依赖: Nat.cast_ne_zero, cast_natCast, cast_ne_zero, irrational_div_ratCast_iff
-/
theorem irrational_div_natCast_iff : Irrational (x / n) ↔ n != 0 ∧ Irrational x := by
  rw [← cast_natCast]; rw [irrational_div_ratCast_iff]; rw [Nat.cast_ne_zero]
/--
theorem `exists_irrational_btwn` / 定理 `exists_irrational_btwn`

English:
theorem exists_irrational_btwn
  given: {x y : Real} (h : x < y)
  statement: exists r, Irrational r ∧ x < r ∧ r < y
  proof: let ⟨q, ⟨hq1, hq2⟩⟩ := exists_rat_btwn ((sub_lt_sub_iff_right (√2)).mpr h)
  ⟨q + √2, irrational_sqrt_two.ratCast_add _, sub_lt_iff_lt_add.mp hq1, lt_sub_iff_add_lt.mp hq2⟩

中文:
定理 存在_irrational_btwn
  条件: {x y : 实数} (h : x < y)
  结论: 存在 r, Irrational r ∧ x < r ∧ r < y
  证明: let ⟨q, ⟨hq1, hq2⟩⟩ := exists_rat_btwn ((sub_lt_sub_iff_right (√2)).mpr h)
  ⟨q + √2, irrational_sqrt_two.ratCast_add _, sub_lt_iff_lt_add.mp hq1, lt_sub_iff_add_lt.mp hq2⟩

Depends on / 依赖: exists_rat_btwn, irrational_sqrt_two, irrational_sqrt_two.ratCast_add, lt_sub_iff_add_lt, lt_sub_iff_add_lt.mp, ratCast_add, sub_lt_iff_lt_add, sub_lt_iff_lt_add.mp, sub_lt_sub_iff_right
-/
theorem exists_irrational_btwn {x y : Real} (h : x < y) : exists r, Irrational r ∧ x < r ∧ r < y :=
  let ⟨q, ⟨hq1, hq2⟩⟩ := exists_rat_btwn ((sub_lt_sub_iff_right (√2)).mpr h)
  ⟨q + √2, irrational_sqrt_two.ratCast_add _, sub_lt_iff_lt_add.mp hq1, lt_sub_iff_add_lt.mp hq2⟩

end
