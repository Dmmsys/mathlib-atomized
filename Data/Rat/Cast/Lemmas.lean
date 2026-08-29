/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Nonneg.Field
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Tactic.Positivity.Basic

/-!
# Some exiled lemmas about casting

These lemmas have been removed from `Mathlib/Data/Rat/Cast/Defs.lean`
to avoiding needing to import `Mathlib/Algebra/Field/Basic.lean` there.

In fact, these lemmas don't appear to be used anywhere in Mathlib,
so perhaps this file can simply be deleted.
-/

public section

namespace Rat

variable {α : Type*} [DivisionRing α]

-- Note that this is more general than `(Rat.castHom α).map_pow`.
@[simp, norm_cast]
/--
lemma `cast_pow` / 引理 `cast_pow`

English:
lemma cast_pow
  given: (p : Rat) (n : Nat)
  statement: ↑(p ^ n) = (p ^ n : α)
  proof: by
  rw [cast_def]; rw [cast_def]; rw [den_pow]; rw [num_pow]; rw [Nat.cast_pow]; rw [Int.cast_pow]; rw [div_eq_mul_inv]; rw [← inv_pow]; rw [← (Int.cast_commute _ _).mul_pow]; rw [← div_eq_mul_inv]

@[simp]

中文:
引理 cast_pow
  条件: (p : 有理数) (n : 自然数)
  结论: ↑(p ^ n) = (p ^ n : α)
  证明: by
  rw [cast_def]; rw [cast_def]; rw [den_pow]; rw [num_pow]; rw [Nat.cast_pow]; rw [Int.cast_pow]; rw [div_eq_mul_inv]; rw [← inv_pow]; rw [← (Int.cast_commute _ _).mul_pow]; rw [← div_eq_mul_inv]

@[simp]

Depends on / 依赖: Int.cast_commute, Int.cast_pow, Nat.cast_pow, cast_commute, cast_def, cast_pow, den_pow, div_eq_mul_inv, inv_pow, mul_pow, num_pow
-/
lemma cast_pow (p : Rat) (n : Nat) : ↑(p ^ n) = (p ^ n : α) := by
  rw [cast_def]; rw [cast_def]; rw [den_pow]; rw [num_pow]; rw [Nat.cast_pow]; rw [Int.cast_pow]; rw [div_eq_mul_inv]; rw [← inv_pow]; rw [← (Int.cast_commute _ _).mul_pow]; rw [← div_eq_mul_inv]

@[simp]
/--
theorem `cast_inv_nat` / 定理 `cast_inv_nat`

English:
theorem cast_inv_nat
  given: (n : Nat)
  statement: ((n⁻¹ : Rat) : α) = (n : α)⁻¹
  proof: by
  rcases n with - | n
  · simp
  rw [cast_def]; rw [inv_natCast_num]; rw [inv_natCast_den]; rw [if_neg n.succ_ne_zero]; rw [Int.sign_eq_one_of_pos (Int.ofNat_succ_pos n)]; rw [Int.cast_one]; rw [one_div]

@[simp]

中文:
定理 cast_inv_nat
  条件: (n : 自然数)
  结论: ((n⁻¹ : 有理数) : α) = (n : α)⁻¹
  证明: by
  rcases n with - | n
  · simp
  rw [cast_def]; rw [inv_natCast_num]; rw [inv_natCast_den]; rw [if_neg n.succ_ne_zero]; rw [Int.sign_eq_one_of_pos (Int.ofNat_succ_pos n)]; rw [Int.cast_one]; rw [one_div]

@[simp]

Depends on / 依赖: Int.cast_one, Int.ofNat_succ_pos, Int.sign_eq_one_of_pos, cast_def, cast_one, if_neg, inv_natCast_den, inv_natCast_num, n.succ_ne_zero, ofNat_succ_pos, one_div, sign_eq_one_of_pos, succ_ne_zero
-/
theorem cast_inv_nat (n : Nat) : ((n⁻¹ : Rat) : α) = (n : α)⁻¹ := by
  rcases n with - | n
  · simp
  rw [cast_def]; rw [inv_natCast_num]; rw [inv_natCast_den]; rw [if_neg n.succ_ne_zero]; rw [Int.sign_eq_one_of_pos (Int.ofNat_succ_pos n)]; rw [Int.cast_one]; rw [one_div]

@[simp]
/--
theorem `cast_inv_int` / 定理 `cast_inv_int`

English:
theorem cast_inv_int
  given: (n : Int)
  statement: ((n⁻¹ : Rat) : α) = (n : α)⁻¹
  proof: by
  rcases n with n | n
  · simp [cast_inv_nat]
  · simp only [Int.cast_negSucc, cast_neg, inv_neg, cast_inv_nat]

@[simp, norm_cast]

中文:
定理 cast_inv_int
  条件: (n : 整数)
  结论: ((n⁻¹ : 有理数) : α) = (n : α)⁻¹
  证明: by
  rcases n with n | n
  · simp [cast_inv_nat]
  · simp only [Int.cast_negSucc, cast_neg, inv_neg, cast_inv_nat]

@[simp, norm_cast]

Depends on / 依赖: Int.cast_negSucc, cast_inv_nat, cast_neg, cast_negSucc, inv_neg
-/
theorem cast_inv_int (n : Int) : ((n⁻¹ : Rat) : α) = (n : α)⁻¹ := by
  rcases n with n | n
  · simp [cast_inv_nat]
  · simp only [Int.cast_negSucc, cast_neg, inv_neg, cast_inv_nat]

@[simp, norm_cast]
/--
theorem `cast_nnratCast` / 定理 `cast_nnratCast`

English:
theorem cast_nnratCast
  given: {K} [DivisionRing K] (q : Rat>=0)
  proof: by
  rw [Rat.cast_def]; rw [NNRat.cast_def]; rw [NNRat.cast_def]
  have hn := @num_div_eq_of_coprime q.num q.den ?hdp q.coprime_num_den
  on_goal 1 => have hd := @den_div_eq_of_coprime q.num q.den ?hdp q.coprime_num_den
  case hdp => simpa only [Int.natCast_pos] using q.den_pos
  simp only [Int.cast_natCast, Nat.cast_inj] at hn hd
  rw [hn]; rw [hd]; rw [Int.cast_natCast]

中文:
定理 cast_nnratCast
  条件: {K} [除环 K] (q : 有理数>=0)
  证明: by
  rw [Rat.cast_def]; rw [NNRat.cast_def]; rw [NNRat.cast_def]
  have hn := @num_div_eq_of_coprime q.num q.den ?hdp q.coprime_num_den
  on_goal 1 => have hd := @den_div_eq_of_coprime q.num q.den ?hdp q.coprime_num_den
  case hdp => simpa only [Int.natCast_pos] using q.den_pos
  simp only [Int.cast_natCast, Nat.cast_inj] at hn hd
  rw [hn]; rw [hd]; rw [Int.cast_natCast]

Depends on / 依赖: Int.cast_natCast, Int.natCast_pos, NNRat.cast_def, Nat.cast_inj, Rat.cast_def, cast_def, cast_inj, cast_natCast, coprime_num_den, den_div_eq_of_coprime, den_pos, natCast_pos, num_div_eq_of_coprime, on_goal, q.coprime_num_den, q.den, q.den_pos, q.num
-/
theorem cast_nnratCast {K} [DivisionRing K] (q : Rat>=0) :
    ((q : Rat) : K) = (q : K) := by
  rw [Rat.cast_def]; rw [NNRat.cast_def]; rw [NNRat.cast_def]
  have hn := @num_div_eq_of_coprime q.num q.den ?hdp q.coprime_num_den
  on_goal 1 => have hd := @den_div_eq_of_coprime q.num q.den ?hdp q.coprime_num_den
  case hdp => simpa only [Int.natCast_pos] using q.den_pos
  simp only [Int.cast_natCast, Nat.cast_inj] at hn hd
  rw [hn]; rw [hd]; rw [Int.cast_natCast]

/-- Casting a scientific literal via `ℚ` is the same as casting directly. -/
@[simp, norm_cast]
/--
theorem `cast_ofScientific` / 定理 `cast_ofScientific`

English:
theorem cast_ofScientific
  given: {K} [DivisionRing K] (m : Nat) (s : Bool) (e : Nat)
  proof: by
  rw [← NNRat.cast_ofScientific (K := K)]; rw [← NNRat.cast_ofScientific]; rw [cast_nnratCast]

中文:
定理 cast_ofScientific
  条件: {K} [除环 K] (m : 自然数) (s : 布尔值) (e : 自然数)
  证明: by
  rw [← NNRat.cast_ofScientific (K := K)]; rw [← NNRat.cast_ofScientific]; rw [cast_nnratCast]

Depends on / 依赖: NNRat.cast_ofScientific, cast_nnratCast, cast_ofScientific
-/
theorem cast_ofScientific {K} [DivisionRing K] (m : Nat) (s : Bool) (e : Nat) :
    (OfScientific.ofScientific m s e : Rat) = (OfScientific.ofScientific m s e : K) := by
  rw [← NNRat.cast_ofScientific (K := K)]; rw [← NNRat.cast_ofScientific]; rw [cast_nnratCast]

end Rat

namespace NNRat

@[simp, norm_cast]
/--
theorem `cast_pow` / 定理 `cast_pow`

English:
theorem cast_pow
  given: {K} [DivisionSemiring K] (q : Rat>=0) (n : Nat)
  proof: by
  rw [cast_def]; rw [cast_def]; rw [den_pow]; rw [num_pow]; rw [Nat.cast_pow]; rw [Nat.cast_pow]; rw [div_eq_mul_inv]; rw [← inv_pow]; rw [← (Nat.cast_commute _ _).mul_pow]; rw [← div_eq_mul_inv]

中文:
定理 cast_pow
  条件: {K} [除半环 K] (q : 有理数>=0) (n : 自然数)
  证明: by
  rw [cast_def]; rw [cast_def]; rw [den_pow]; rw [num_pow]; rw [Nat.cast_pow]; rw [Nat.cast_pow]; rw [div_eq_mul_inv]; rw [← inv_pow]; rw [← (Nat.cast_commute _ _).mul_pow]; rw [← div_eq_mul_inv]

Depends on / 依赖: Nat.cast_commute, Nat.cast_pow, cast_commute, cast_def, cast_pow, den_pow, div_eq_mul_inv, inv_pow, mul_pow, num_pow
-/
theorem cast_pow {K} [DivisionSemiring K] (q : Rat>=0) (n : Nat) :
    NNRat.cast (q ^ n) = (NNRat.cast q : K) ^ n := by
  rw [cast_def]; rw [cast_def]; rw [den_pow]; rw [num_pow]; rw [Nat.cast_pow]; rw [Nat.cast_pow]; rw [div_eq_mul_inv]; rw [← inv_pow]; rw [← (Nat.cast_commute _ _).mul_pow]; rw [← div_eq_mul_inv]

/--
theorem `cast_zpow_of_ne_zero` / 定理 `cast_zpow_of_ne_zero`

English:
theorem cast_zpow_of_ne_zero
  given: {K} [DivisionSemiring K] (q : Rat>=0) (z : Int) (hq : (q.num : K) != 0)
  proof: by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp
  · simp_rw [zpow_neg, zpow_natCast, ← inv_pow, NNRat.cast_pow]
    congr
    rw [cast_inv_of_ne_zero hq]

中文:
定理 cast_zpow_of_ne_zero
  条件: {K} [除半环 K] (q : 有理数>=0) (z : 整数) (hq : (q.num : K) != 0)
  证明: by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp
  · simp_rw [zpow_neg, zpow_natCast, ← inv_pow, NNRat.cast_pow]
    congr
    rw [cast_inv_of_ne_zero hq]

Depends on / 依赖: NNRat.cast_pow, cast_inv_of_ne_zero, cast_pow, eq_nat_or_neg, inv_pow, simp_rw, z.eq_nat_or_neg, zpow_natCast, zpow_neg
-/
theorem cast_zpow_of_ne_zero {K} [DivisionSemiring K] (q : Rat>=0) (z : Int) (hq : (q.num : K) != 0) :
    NNRat.cast (q ^ z) = (NNRat.cast q : K) ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp
  · simp_rw [zpow_neg, zpow_natCast, ← inv_pow, NNRat.cast_pow]
    congr
    rw [cast_inv_of_ne_zero hq]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `cast_mk` / 定理 `cast_mk`

English:
theorem cast_mk
  given: {K} [DivisionRing K] (q : Rat) (h : 0 <= q)
  proof: by
  simp only [NNRat.cast_def, NNRat.num_mk, Nat.cast_natAbs, NNRat.den_mk, Rat.cast_def]
  rw [abs_of_nonneg (by simpa)]

中文:
定理 cast_mk
  条件: {K} [除环 K] (q : 有理数) (h : 0 <= q)
  证明: by
  simp only [NNRat.cast_def, NNRat.num_mk, Nat.cast_natAbs, NNRat.den_mk, Rat.cast_def]
  rw [abs_of_nonneg (by simpa)]

Depends on / 依赖: NNRat.cast_def, NNRat.den_mk, NNRat.num_mk, Nat.cast_natAbs, Rat.cast_def, abs_of_nonneg, cast_def, cast_natAbs, den_mk, num_mk
-/
theorem cast_mk {K} [DivisionRing K] (q : Rat) (h : 0 <= q) :
    (NNRat.cast ⟨q, h⟩ : K) = (q : K) := by
  simp only [NNRat.cast_def, NNRat.num_mk, Nat.cast_natAbs, NNRat.den_mk, Rat.cast_def]
  rw [abs_of_nonneg (by simpa)]

open OfScientific in
/--
theorem `Nonneg.coe_ofScientific` / 定理 `Nonneg.coe_ofScientific`

English:
theorem Nonneg.coe_ofScientific
  statement: {K} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  proof: rfl

中文:
定理 Nonneg.coe_ofScientific
  结论: {K} [域 K] [线性序 K] [是StrictOrdered环 K]
  证明: rfl
-/
theorem Nonneg.coe_ofScientific {K} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m : Nat) (s : Bool) (e : Nat) :
    (ofScientific m s e : {x : K // 0 <= x}).val = ofScientific m s e := rfl

end NNRat
