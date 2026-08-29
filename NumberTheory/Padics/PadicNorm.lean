/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean

/-!
# p-adic norm

This file defines the `p`-adic norm on `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`.

The valuation induces a norm on `ℚ`. This norm is a nonarchimedean absolute value.
It takes values in `{0} ∪ {1/p^k | k ∈ ℤ}`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/

@[expose] public section


/--
Definition of `padicNorm` / `padicNorm` 的定义

English:
definition padicNorm
  signature: (p : Nat) (q : Rat)
  body: if q = 0 then 0 else (p : Rat) ^ (-padicValRat p q)

中文:
定义 padicNorm
  签名: (p : 自然数) (q : Rat)
  定义体: if q = 0 then 0 else (p : Rat) ^ (-padicValRat p q)

Depends on / 依赖: padicValRat
-/
def padicNorm (p : Nat) (q : Rat) : Rat :=
  if q = 0 then 0 else (p : Rat) ^ (-padicValRat p q)

namespace padicNorm

open padicValRat

variable {p : Nat}

/-- Unfolds the definition of the `p`-adic norm of `q` when `q ≠ 0`. -/
@[simp]
/--
theorem `eq_zpow_of_nonzero` / 定理 `eq_zpow_of_nonzero`

English:
theorem eq_zpow_of_nonzero
  given: {q : Rat} (hq : q != 0)
  proof: by simp [hq, padicNorm]

中文:
定理 eq_zpow_of_nonzero
  条件: {q : Rat} (hq : q != 0)
  证明: by simp [hq, padicNorm]
-/
protected theorem eq_zpow_of_nonzero {q : Rat} (hq : q != 0) :
    padicNorm p q = (p : Rat) ^ (-padicValRat p q) := by simp [hq, padicNorm]

/--
theorem `nonneg` / 定理 `nonneg`

English:
theorem nonneg
  given: (q : Rat)
  statement: 0 <= padicNorm p q
  proof: if hq : q = 0 then by simp [hq, padicNorm]
  else by
    unfold padicNorm
    split_ifs
    apply zpow_nonneg
    exact mod_cast Nat.zero_le _

中文:
定理 nonneg
  条件: (q : Rat)
  结论: 0 <= padicNorm p q
  证明: if hq : q = 0 then by simp [hq, padicNorm]
  else by
    unfold padicNorm
    split_ifs
    apply zpow_nonneg
    exact mod_cast Nat.zero_le _
-/
protected theorem nonneg (q : Rat) : 0 <= padicNorm p q :=
  if hq : q = 0 then by simp [hq, padicNorm]
  else by
    unfold padicNorm
    split_ifs
    apply zpow_nonneg
    exact mod_cast Nat.zero_le _

/-- The `p`-adic norm of `0` is `0`. -/
@[simp]
/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: padicNorm p 0 = 0
  proof: by simp [padicNorm]

中文:
定理 zero
  结论: padicNorm p 0 = 0
  证明: by simp [padicNorm]
-/
protected theorem zero : padicNorm p 0 = 0 := by simp [padicNorm]

/--
theorem `one` / 定理 `one`

English:
theorem one
  statement: padicNorm p 1 = 1
  proof: by simp [padicNorm]

中文:
定理 one
  结论: padicNorm p 1 = 1
  证明: by simp [padicNorm]
-/
protected theorem one : padicNorm p 1 = 1 := by simp [padicNorm]

/--
theorem `padicNorm_p` / 定理 `padicNorm_p`

English:
theorem padicNorm_p
  given: (hp : 1 < p)
  statement: padicNorm p p = (p : Rat)⁻¹
  proof: by
  simp [padicNorm, (pos_of_gt hp).ne', padicValNat.self hp]

中文:
定理 padicNorm_p
  条件: (hp : 1 < p)
  结论: padicNorm p p = (p : Rat)⁻¹
  证明: by
  simp [padicNorm, (pos_of_gt hp).ne', padicValNat.self hp]

Depends on / 依赖: padicNorm, padicValNat, padicValNat.self, pos_of_gt
-/
theorem padicNorm_p (hp : 1 < p) : padicNorm p p = (p : Rat)⁻¹ := by
  simp [padicNorm, (pos_of_gt hp).ne', padicValNat.self hp]

/-- The `p`-adic norm of `p` is `p⁻¹` if `p` is prime.

See also `padicNorm.padicNorm_p` for a version assuming `1 < p`. -/
@[simp]
/--
theorem `padicNorm_p_of_prime` / 定理 `padicNorm_p_of_prime`

English:
theorem padicNorm_p_of_prime
  given: [Fact p.Prime]
  statement: padicNorm p p = (p : Rat)⁻¹
  proof: padicNorm_p Nat.Prime.one_lt Fact.out

中文:
定理 padicNorm_p_of_prime
  条件: [Fact p.Prime]
  结论: padicNorm p p = (p : Rat)⁻¹
  证明: padicNorm_p Nat.Prime.one_lt Fact.out

Depends on / 依赖: Fact.out, Nat.Prime.one_lt, one_lt, padicNorm_p
-/
theorem padicNorm_p_of_prime [Fact p.Prime] : padicNorm p p = (p : Rat)⁻¹ :=
padicNorm_p Nat.Prime.one_lt Fact.out

/--
theorem `padicNorm_of_prime_of_ne` / 定理 `padicNorm_of_prime_of_ne`

English:
theorem padicNorm_of_prime_of_ne
  statement: {q : Nat} [p_prime : Fact p.Prime] [q_prime : Fact q.Prime]
  proof: by
  have p : padicValRat p q = 0 := mod_cast padicValNat_primes ne
  rw [padicNorm]; rw [p]
  simp [q_prime.1.ne_zero]

中文:
定理 padicNorm_of_prime_of_ne
  结论: {q : 自然数} [p_prime : Fact p.Prime] [q_prime : Fact q.Prime]
  证明: by
  have p : padicValRat p q = 0 := mod_cast padicValNat_primes ne
  rw [padicNorm]; rw [p]
  simp [q_prime.1.ne_zero]

Depends on / 依赖: mod_cast, ne_zero, padicNorm, padicValNat_primes, padicValRat, q_prime
-/
theorem padicNorm_of_prime_of_ne {q : Nat} [p_prime : Fact p.Prime] [q_prime : Fact q.Prime]
    (ne : p != q) : padicNorm p q = 1 := by
  have p : padicValRat p q = 0 := mod_cast padicValNat_primes ne
  rw [padicNorm]; rw [p]
  simp [q_prime.1.ne_zero]

/--
theorem `padicNorm_p_lt_one` / 定理 `padicNorm_p_lt_one`

English:
theorem padicNorm_p_lt_one
  given: (hp : 1 < p)
  statement: padicNorm p p < 1
  proof: by
  rw [padicNorm_p hp]; rw [inv_lt_one_iff₀]
  exact mod_cast Or.inr hp

中文:
定理 padicNorm_p_lt_one
  条件: (hp : 1 < p)
  结论: padicNorm p p < 1
  证明: by
  rw [padicNorm_p hp]; rw [inv_lt_one_iff₀]
  exact mod_cast Or.inr hp

Depends on / 依赖: Or.inr, mod_cast, padicNorm_p
-/
theorem padicNorm_p_lt_one (hp : 1 < p) : padicNorm p p < 1 := by
  rw [padicNorm_p hp]; rw [inv_lt_one_iff₀]
  exact mod_cast Or.inr hp

/--
theorem `padicNorm_p_lt_one_of_prime` / 定理 `padicNorm_p_lt_one_of_prime`

English:
theorem padicNorm_p_lt_one_of_prime
  given: [Fact p.Prime]
  statement: padicNorm p p < 1
  proof: padicNorm_p_lt_one Nat.Prime.one_lt Fact.out

中文:
定理 padicNorm_p_lt_one_of_prime
  条件: [Fact p.Prime]
  结论: padicNorm p p < 1
  证明: padicNorm_p_lt_one Nat.Prime.one_lt Fact.out

Depends on / 依赖: Fact.out, Nat.Prime.one_lt, one_lt, padicNorm_p_lt_one
-/
theorem padicNorm_p_lt_one_of_prime [Fact p.Prime] : padicNorm p p < 1 :=
padicNorm_p_lt_one Nat.Prime.one_lt Fact.out

/--
theorem `values_discrete` / 定理 `values_discrete`

English:
theorem values_discrete
  given: {q : Rat} (hq : q != 0)
  statement: exists z : Int, padicNorm p q = (p : Rat) ^ (-z)
  proof: ⟨padicValRat p q, by simp [padicNorm, hq]⟩

中文:
定理 values_discrete
  条件: {q : Rat} (hq : q != 0)
  结论: 存在 z : 整数, padicNorm p q = (p : Rat) ^ (-z)
  证明: ⟨padicValRat p q, by simp [padicNorm, hq]⟩
-/
protected theorem values_discrete {q : Rat} (hq : q != 0) : exists z : Int, padicNorm p q = (p : Rat) ^ (-z) :=
  ⟨padicValRat p q, by simp [padicNorm, hq]⟩

/-- `padicNorm p` is symmetric. -/
@[simp]
/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (q : Rat)
  statement: padicNorm p (-q) = padicNorm p q
  proof: if hq : q = 0 then by simp [hq] else by simp [padicNorm, hq]

中文:
定理 neg
  条件: (q : Rat)
  结论: padicNorm p (-q) = padicNorm p q
  证明: if hq : q = 0 then by simp [hq] else by simp [padicNorm, hq]
-/
protected theorem neg (q : Rat) : padicNorm p (-q) = padicNorm p q :=
  if hq : q = 0 then by simp [hq] else by simp [padicNorm, hq]

variable [hp : Fact p.Prime]

/--
theorem `nonzero` / 定理 `nonzero`

English:
theorem nonzero
  given: {q : Rat} (hq : q != 0)
  statement: padicNorm p q != 0
  proof: by
  rw [padicNorm.eq_zpow_of_nonzero hq]
  apply zpow_ne_zero
  exact mod_cast ne_of_gt hp.1.pos

中文:
定理 nonzero
  条件: {q : Rat} (hq : q != 0)
  结论: padicNorm p q != 0
  证明: by
  rw [padicNorm.eq_zpow_of_nonzero hq]
  apply zpow_ne_zero
  exact mod_cast ne_of_gt hp.1.pos
-/
protected theorem nonzero {q : Rat} (hq : q != 0) : padicNorm p q != 0 := by
  rw [padicNorm.eq_zpow_of_nonzero hq]
  apply zpow_ne_zero
  exact mod_cast ne_of_gt hp.1.pos

/--
theorem `zero_of_padicNorm_eq_zero` / 定理 `zero_of_padicNorm_eq_zero`

English:
theorem zero_of_padicNorm_eq_zero
  given: {q : Rat} (h : padicNorm p q = 0)
  statement: q = 0
  proof: by
  apply by_contradiction; intro hq
  unfold padicNorm at h; rw [if_neg hq] at h
  apply absurd h
  apply zpow_ne_zero
  exact mod_cast hp.1.ne_zero

中文:
定理 zero_of_padicNorm_eq_zero
  条件: {q : Rat} (h : padicNorm p q = 0)
  结论: q = 0
  证明: by
  apply by_contradiction; intro hq
  unfold padicNorm at h; rw [if_neg hq] at h
  apply absurd h
  apply zpow_ne_zero
  exact mod_cast hp.1.ne_zero

Depends on / 依赖: absurd, by_contradiction, if_neg, mod_cast, ne_zero, padicNorm, zpow_ne_zero
-/
theorem zero_of_padicNorm_eq_zero {q : Rat} (h : padicNorm p q = 0) : q = 0 := by
  apply by_contradiction; intro hq
  unfold padicNorm at h; rw [if_neg hq] at h
  apply absurd h
  apply zpow_ne_zero
  exact mod_cast hp.1.ne_zero

/-- The `p`-adic norm is multiplicative. -/
@[simp]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: (q r : Rat)
  statement: padicNorm p (q * r) = padicNorm p q * padicNorm p r
  proof: if hq : q = 0 then by simp [hq]
  else
    if hr : r = 0 then by simp [hr]
    else by
      have : (p : Rat) != 0 := by simp [hp.1.ne_zero]
      simp [padicNorm, *, padicValRat.mul, zpow_add₀ this, mul_comm]

中文:
定理 mul
  条件: (q r : Rat)
  结论: padicNorm p (q * r) = padicNorm p q * padicNorm p r
  证明: if hq : q = 0 then by simp [hq]
  else
    if hr : r = 0 then by simp [hr]
    else by
      have : (p : Rat) != 0 := by simp [hp.1.ne_zero]
      simp [padicNorm, *, padicValRat.mul, zpow_add₀ this, mul_comm]
-/
protected theorem mul (q r : Rat) : padicNorm p (q * r) = padicNorm p q * padicNorm p r :=
  if hq : q = 0 then by simp [hq]
  else
    if hr : r = 0 then by simp [hr]
    else by
      have : (p : Rat) != 0 := by simp [hp.1.ne_zero]
      simp [padicNorm, *, padicValRat.mul, zpow_add₀ this, mul_comm]

/-- The `p`-adic norm respects division. -/
@[simp]
/--
theorem `div` / 定理 `div`

English:
theorem div
  given: (q r : Rat)
  statement: padicNorm p (q / r) = padicNorm p q / padicNorm p r
  proof: if hr : r = 0 then by simp [hr]
  else eq_div_of_mul_eq (padicNorm.nonzero hr) (by rw [← padicNorm.mul, div_mul_cancel₀ _ hr])

中文:
定理 div
  条件: (q r : Rat)
  结论: padicNorm p (q / r) = padicNorm p q / padicNorm p r
  证明: if hr : r = 0 then by simp [hr]
  else eq_div_of_mul_eq (padicNorm.nonzero hr) (by rw [← padicNorm.mul, div_mul_cancel₀ _ hr])
-/
protected theorem div (q r : Rat) : padicNorm p (q / r) = padicNorm p q / padicNorm p r :=
  if hr : r = 0 then by simp [hr]
  else eq_div_of_mul_eq (padicNorm.nonzero hr) (by rw [← padicNorm.mul, div_mul_cancel₀ _ hr])

/--
theorem `of_int` / 定理 `of_int`

English:
theorem of_int
  given: (z : Int)
  statement: padicNorm p z <= 1
  proof: by
  obtain rfl | hz := eq_or_ne z 0
  · simp
  · rw [padicNorm, if_neg (mod_cast hz)]
    exact zpow_le_one_of_nonpos₀ (mod_cast hp.1.one_le) (by simp)

中文:
定理 of_int
  条件: (z : 整数)
  结论: padicNorm p z <= 1
  证明: by
  obtain rfl | hz := eq_or_ne z 0
  · simp
  · rw [padicNorm, if_neg (mod_cast hz)]
    exact zpow_le_one_of_nonpos₀ (mod_cast hp.1.one_le) (by simp)
-/
protected theorem of_int (z : Int) : padicNorm p z <= 1 := by
  obtain rfl | hz := eq_or_ne z 0
  · simp
  · rw [padicNorm, if_neg (mod_cast hz)]
    exact zpow_le_one_of_nonpos₀ (mod_cast hp.1.one_le) (by simp)

/--
theorem `nonarchimedean_aux` / 定理 `nonarchimedean_aux`

English:
theorem nonarchimedean_aux
  given: {q r : Rat} (h : padicValRat p q <= padicValRat p r)
  proof: have hnqp : padicNorm p q >= 0 := padicNorm.nonneg _
  have hnrp : padicNorm p r >= 0 := padicNorm.nonneg _
  if hq : q = 0 then by simp [hq, max_eq_right hnrp]
  else
    if hr : r = 0 then by simp [hr, max_eq_left hnqp]
    else
      if hqr : q + r = 0 then le_trans (by simpa [hqr] using hnqp) (l

中文:
定理 nonarchimedean_aux
  条件: {q r : Rat} (h : padicValRat p q <= padicValRat p r)
  证明: have hnqp : padicNorm p q >= 0 := padicNorm.nonneg _
  have hnrp : padicNorm p r >= 0 := padicNorm.nonneg _
  if hq : q = 0 then by simp [hq, max_eq_right hnrp]
  else
    if hr : r = 0 then by simp [hr, max_eq_left hnqp]
    else
      if hqr : q + r = 0 then le_trans (by simpa [hqr] using hnqp) (l
-/
private theorem nonarchimedean_aux {q r : Rat} (h : padicValRat p q <= padicValRat p r) :
    padicNorm p (q + r) <= max (padicNorm p q) (padicNorm p r) :=
  have hnqp : padicNorm p q >= 0 := padicNorm.nonneg _
  have hnrp : padicNorm p r >= 0 := padicNorm.nonneg _
  if hq : q = 0 then by simp [hq, max_eq_right hnrp]
  else
    if hr : r = 0 then by simp [hr, max_eq_left hnqp]
    else
      if hqr : q + r = 0 then le_trans (by simpa [hqr] using hnqp) (le_max_left _ _)
      else by
        unfold padicNorm; split_ifs
        apply le_max_iff.2
        left
        apply zpow_le_zpow_right₀
        · exact mod_cast le_of_lt hp.1.one_lt
        · apply neg_le_neg
          have : padicValRat p q = min (padicValRat p q) (padicValRat p r) := (min_eq_left h).symm
          rw [this]
          exact min_le_padicValRat_add hqr

/--
theorem `nonarchimedean` / 定理 `nonarchimedean`

English:
theorem nonarchimedean
  given: {q r : Rat}
  proof: by
  wlog hle : padicValRat p q <= padicValRat p r generalizing q r
  · rw [add_comm, max_comm]
    exact this (le_of_not_ge hle)
  exact nonarchimedean_aux hle

中文:
定理 nonarchimedean
  条件: {q r : Rat}
  证明: by
  wlog hle : padicValRat p q <= padicValRat p r generalizing q r
  · rw [add_comm, max_comm]
    exact this (le_of_not_ge hle)
  exact nonarchimedean_aux hle
-/
protected theorem nonarchimedean {q r : Rat} :
    padicNorm p (q + r) <= max (padicNorm p q) (padicNorm p r) := by
  wlog hle : padicValRat p q <= padicValRat p r generalizing q r
  · rw [add_comm, max_comm]
    exact this (le_of_not_ge hle)
  exact nonarchimedean_aux hle

/--
theorem `triangle_ineq` / 定理 `triangle_ineq`

English:
theorem triangle_ineq
  given: (q r : Rat)
  statement: padicNorm p (q + r) <= padicNorm p q + padicNorm p r
  proof: calc
    padicNorm p (q + r) <= max (padicNorm p q) (padicNorm p r) := padicNorm.nonarchimedean
    _ <= padicNorm p q + padicNorm p r :=
      max_le_add_of_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)

中文:
定理 triangle_ineq
  条件: (q r : Rat)
  结论: padicNorm p (q + r) <= padicNorm p q + padicNorm p r
  证明: calc
    padicNorm p (q + r) <= max (padicNorm p q) (padicNorm p r) := padicNorm.nonarchimedean
    _ <= padicNorm p q + padicNorm p r :=
      max_le_add_of_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)

Depends on / 依赖: max_le_add_of_nonneg, nonarchimedean, nonneg, padicNorm, padicNorm.nonarchimedean, padicNorm.nonneg
-/
theorem triangle_ineq (q r : Rat) : padicNorm p (q + r) <= padicNorm p q + padicNorm p r :=
  calc
    padicNorm p (q + r) <= max (padicNorm p q) (padicNorm p r) := padicNorm.nonarchimedean
    _ <= padicNorm p q + padicNorm p r :=
      max_le_add_of_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: {q r : Rat}
  statement: padicNorm p (q - r) <= max (padicNorm p q) (padicNorm p r)
  proof: by
  rw [sub_eq_add_neg]; rw [← padicNorm.neg r]
  exact padicNorm.nonarchimedean

中文:
定理 sub
  条件: {q r : Rat}
  结论: padicNorm p (q - r) <= max (padicNorm p q) (padicNorm p r)
  证明: by
  rw [sub_eq_add_neg]; rw [← padicNorm.neg r]
  exact padicNorm.nonarchimedean
-/
protected theorem sub {q r : Rat} : padicNorm p (q - r) <= max (padicNorm p q) (padicNorm p r) := by
  rw [sub_eq_add_neg]; rw [← padicNorm.neg r]
  exact padicNorm.nonarchimedean

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAbsoluteValue (padicNorm p)
  body: padicNorm.nonneg
  abv_eq_zero' := ⟨zero_of_padicNorm_eq_zero, fun hx => by simp [hx]⟩
  abv_add' := padicNorm.triangle_ineq
  abv_mul' := padicNorm.mul

中文:
实例 :
  签名: IsAbsoluteValue (padicNorm p)
  定义体: padicNorm.nonneg
  abv_eq_zero' := ⟨zero_of_padicNorm_eq_zero, fun hx => by simp [hx]⟩
  abv_add' := padicNorm.triangle_ineq
  abv_mul' := padicNorm.mul

Depends on / 依赖: nonneg, padicNorm, padicNorm.nonneg
-/
instance : IsAbsoluteValue (padicNorm p) where
  abv_nonneg' := padicNorm.nonneg
  abv_eq_zero' := ⟨zero_of_padicNorm_eq_zero, fun hx => by simp [hx]⟩
  abv_add' := padicNorm.triangle_ineq
  abv_mul' := padicNorm.mul

/--
theorem `add_eq_max_of_ne` / 定理 `add_eq_max_of_ne`

English:
theorem add_eq_max_of_ne
  given: {q r : Rat} (hne : padicNorm p q != padicNorm p r)
  proof: IsNonarchimedean.add_eq_max_of_ne (f := IsAbsoluteValue.toAbsoluteValue (padicNorm p))
    (fun _ _ => padicNorm.nonarchimedean) hne

中文:
定理 add_eq_max_of_ne
  条件: {q r : Rat} (hne : padicNorm p q != padicNorm p r)
  证明: IsNonarchimedean.add_eq_max_of_ne (f := IsAbsoluteValue.toAbsoluteValue (padicNorm p))
    (fun _ _ => padicNorm.nonarchimedean) hne

Depends on / 依赖: IsAbsoluteValue, IsAbsoluteValue.toAbsoluteValue, IsNonarchimedean, IsNonarchimedean.add_eq_max_of_ne, add_eq_max_of_ne, nonarchimedean, padicNorm, padicNorm.nonarchimedean, toAbsoluteValue
-/
theorem add_eq_max_of_ne {q r : Rat} (hne : padicNorm p q != padicNorm p r) :
    padicNorm p (q + r) = max (padicNorm p q) (padicNorm p r) :=
  IsNonarchimedean.add_eq_max_of_ne (f := IsAbsoluteValue.toAbsoluteValue (padicNorm p))
    (fun _ _ => padicNorm.nonarchimedean) hne

/--
theorem `dvd_iff_norm_le` / 定理 `dvd_iff_norm_le`

English:
theorem dvd_iff_norm_le
  given: {n : Nat} {z : Int}
  statement: ↑(p ^ n) ∣ z ↔ padicNorm p z <= (p : Rat) ^ (-n : Int)
  proof: by
  unfold padicNorm; split_ifs with hz
  · norm_cast at hz
    simp [hz]
  · rw [zpow_le_zpow_iff_right₀, neg_le_neg_iff, padicValRat.of_int,
      padicValInt.of_ne_one_ne_zero hp.1.ne_one _]
    · norm_cast
      rw [← FiniteMultiplicity.pow_dvd_iff_le_multiplicity]
      · norm_cast
      · app

中文:
定理 dvd_iff_norm_le
  条件: {n : 自然数} {z : 整数}
  结论: ↑(p ^ n) ∣ z ↔ padicNorm p z <= (p : Rat) ^ (-n : 整数)
  证明: by
  unfold padicNorm; split_ifs with hz
  · norm_cast at hz
    simp [hz]
  · rw [zpow_le_zpow_iff_right₀, neg_le_neg_iff, padicValRat.of_int,
      padicValInt.of_ne_one_ne_zero hp.1.ne_one _]
    · norm_cast
      rw [← FiniteMultiplicity.pow_dvd_iff_le_multiplicity]
      · norm_cast
      · app

Depends on / 依赖: FiniteMultiplicity, FiniteMultiplicity.pow_dvd_iff_le_multiplicity, Int.finiteMultiplicity_iff, finiteMultiplicity_iff, hp.out.ne_one, hp.out.one_lt, mod_cast, ne_one, neg_le_neg_iff, of_int, of_ne_one_ne_zero, one_lt, padicNorm, padicValInt, padicValInt.of_ne_one_ne_zero, padicValRat, padicValRat.of_int, pow_dvd_iff_le_multiplicity, split_ifs
-/
theorem dvd_iff_norm_le {n : Nat} {z : Int} : ↑(p ^ n) ∣ z ↔ padicNorm p z <= (p : Rat) ^ (-n : Int) := by
  unfold padicNorm; split_ifs with hz
  · norm_cast at hz
    simp [hz]
  · rw [zpow_le_zpow_iff_right₀, neg_le_neg_iff, padicValRat.of_int,
      padicValInt.of_ne_one_ne_zero hp.1.ne_one _]
    · norm_cast
      rw [← FiniteMultiplicity.pow_dvd_iff_le_multiplicity]
      · norm_cast
      · apply Int.finiteMultiplicity_iff.2 ⟨by simp [hp.out.ne_one], mod_cast hz⟩
    · exact_mod_cast hz
    · exact_mod_cast hp.out.one_lt

/--
theorem `int_eq_one_iff` / 定理 `int_eq_one_iff`

English:
theorem int_eq_one_iff
  given: (m : Int)
  statement: padicNorm p m = 1 ↔ ¬(p : Int) ∣ m
  proof: by
  nth_rw 2 [← pow_one p]
  simp only [dvd_iff_norm_le, Nat.cast_one, zpow_neg, zpow_one, not_le]
  constructor
  · intro h
    rw [h]; rw [inv_lt_one₀] <;> norm_cast
    · exact Nat.Prime.one_lt Fact.out
    · exact Nat.Prime.pos Fact.out
  · simp only [padicNorm]
    split_ifs
    · rw [inv_lt_z

中文:
定理 int_eq_one_iff
  条件: (m : 整数)
  结论: padicNorm p m = 1 ↔ ¬(p : 整数) ∣ m
  证明: by
  nth_rw 2 [← pow_one p]
  simp only [dvd_iff_norm_le, Nat.cast_one, zpow_neg, zpow_one, not_le]
  constructor
  · intro h
    rw [h]; rw [inv_lt_one₀] <;> norm_cast
    · exact Nat.Prime.one_lt Fact.out
    · exact Nat.Prime.pos Fact.out
  · simp only [padicNorm]
    split_ifs
    · rw [inv_lt_z

Depends on / 依赖: Fact.out, Nat.Prime, Nat.Prime.one_lt, Nat.Prime.pos, Nat.cast_lt, Nat.cast_one, Nat.cast_zero, Nat.not_lt_zero, cast_lt, cast_one, cast_zero, dvd_iff_norm_le, inv_lt_zero, not_le, not_lt_zero, nth_rw, one_lt, padicNorm, pow_one, split_ifs
-/
theorem int_eq_one_iff (m : Int) : padicNorm p m = 1 ↔ ¬(p : Int) ∣ m := by
  nth_rw 2 [← pow_one p]
  simp only [dvd_iff_norm_le, Nat.cast_one, zpow_neg, zpow_one, not_le]
  constructor
  · intro h
    rw [h]; rw [inv_lt_one₀] <;> norm_cast
    · exact Nat.Prime.one_lt Fact.out
    · exact Nat.Prime.pos Fact.out
  · simp only [padicNorm]
    split_ifs
    · rw [inv_lt_zero, ← Nat.cast_zero, Nat.cast_lt]
      intro h
      exact (Nat.not_lt_zero p h).elim
    · have : 1 < (p : Rat) := by norm_cast; exact Nat.Prime.one_lt (Fact.out : Nat.Prime p)
      rw [← zpow_neg_one]; rw [zpow_lt_zpow_iff_right₀ this]
      have : 0 <= padicValRat p m := by simp only [of_int, Nat.cast_nonneg]
      intro h
      rw [← zpow_zero (p : Rat)]; rw [zpow_right_inj₀] <;> linarith

/--
theorem `int_lt_one_iff` / 定理 `int_lt_one_iff`

English:
theorem int_lt_one_iff
  given: (m : Int)
  statement: padicNorm p m < 1 ↔ (p : Int) ∣ m
  proof: by
  rw [← not_iff_not]; rw [← int_eq_one_iff]; rw [eq_iff_le_not_lt]
  simp only [padicNorm.of_int, true_and]

中文:
定理 int_lt_one_iff
  条件: (m : 整数)
  结论: padicNorm p m < 1 ↔ (p : 整数) ∣ m
  证明: by
  rw [← not_iff_not]; rw [← int_eq_one_iff]; rw [eq_iff_le_not_lt]
  simp only [padicNorm.of_int, true_and]

Depends on / 依赖: eq_iff_le_not_lt, int_eq_one_iff, not_iff_not, of_int, padicNorm, padicNorm.of_int, true_and
-/
theorem int_lt_one_iff (m : Int) : padicNorm p m < 1 ↔ (p : Int) ∣ m := by
  rw [← not_iff_not]; rw [← int_eq_one_iff]; rw [eq_iff_le_not_lt]
  simp only [padicNorm.of_int, true_and]

/--
theorem `of_nat` / 定理 `of_nat`

English:
theorem of_nat
  given: (m : Nat)
  statement: padicNorm p m <= 1
  proof: padicNorm.of_int (m : Int)

中文:
定理 of_nat
  条件: (m : 自然数)
  结论: padicNorm p m <= 1
  证明: padicNorm.of_int (m : Int)

Depends on / 依赖: of_int, padicNorm, padicNorm.of_int
-/
theorem of_nat (m : Nat) : padicNorm p m <= 1 :=
  padicNorm.of_int (m : Int)

/--
theorem `nat_eq_one_iff` / 定理 `nat_eq_one_iff`

English:
theorem nat_eq_one_iff
  given: (m : Nat)
  statement: padicNorm p m = 1 ↔ ¬p ∣ m
  proof: by
  rw [← Int.natCast_dvd_natCast]; rw [← int_eq_one_iff]; rw [Int.cast_natCast]

中文:
定理 nat_eq_one_iff
  条件: (m : 自然数)
  结论: padicNorm p m = 1 ↔ ¬p ∣ m
  证明: by
  rw [← Int.natCast_dvd_natCast]; rw [← int_eq_one_iff]; rw [Int.cast_natCast]

Depends on / 依赖: Int.cast_natCast, Int.natCast_dvd_natCast, cast_natCast, int_eq_one_iff, natCast_dvd_natCast
-/
theorem nat_eq_one_iff (m : Nat) : padicNorm p m = 1 ↔ ¬p ∣ m := by
  rw [← Int.natCast_dvd_natCast]; rw [← int_eq_one_iff]; rw [Int.cast_natCast]

/--
theorem `nat_lt_one_iff` / 定理 `nat_lt_one_iff`

English:
theorem nat_lt_one_iff
  given: (m : Nat)
  statement: padicNorm p m < 1 ↔ p ∣ m
  proof: by
  rw [← Int.natCast_dvd_natCast]; rw [← int_lt_one_iff]; rw [Int.cast_natCast]

中文:
定理 nat_lt_one_iff
  条件: (m : 自然数)
  结论: padicNorm p m < 1 ↔ p ∣ m
  证明: by
  rw [← Int.natCast_dvd_natCast]; rw [← int_lt_one_iff]; rw [Int.cast_natCast]

Depends on / 依赖: Int.cast_natCast, Int.natCast_dvd_natCast, cast_natCast, int_lt_one_iff, natCast_dvd_natCast
-/
theorem nat_lt_one_iff (m : Nat) : padicNorm p m < 1 ↔ p ∣ m := by
  rw [← Int.natCast_dvd_natCast]; rw [← int_lt_one_iff]; rw [Int.cast_natCast]

/--
theorem `not_int_of_not_padic_int` / 定理 `not_int_of_not_padic_int`

English:
theorem not_int_of_not_padic_int
  statement: (p : Nat) {a : Rat} [hp : Fact (Nat.Prime p)]
  proof: by
  contrapose! H
  rw [Rat.eq_num_of_isInt H]
  apply padicNorm.of_int

中文:
定理 not_int_of_not_padic_int
  结论: (p : 自然数) {a : Rat} [hp : Fact (自然数.Prime p)]
  证明: by
  contrapose! H
  rw [Rat.eq_num_of_isInt H]
  apply padicNorm.of_int

Depends on / 依赖: Rat.eq_num_of_isInt, contrapose, eq_num_of_isInt, of_int, padicNorm, padicNorm.of_int
-/
theorem not_int_of_not_padic_int (p : Nat) {a : Rat} [hp : Fact (Nat.Prime p)]
    (H : 1 < padicNorm p a) : ¬ a.isInt := by
  contrapose! H
  rw [Rat.eq_num_of_isInt H]
  apply padicNorm.of_int

/--
theorem `sum_lt` / 定理 `sum_lt`

English:
theorem sum_lt
  statement: {α : Type*} {F : α -> Rat} {t : Rat} {s : Finset α} (hs : s.Nonempty)
  proof: lt_of_le_of_lt (IsNonarchimedean.apply_sum_le_sup (fun _ _ => padicNorm.nonarchimedean) hs)
    (Finset.sup'_lt_iff hs).2 hF

中文:
定理 sum_lt
  结论: {α : 类型} {F : α -> Rat} {t : Rat} {s : Finset α} (hs : s.Nonempty)
  证明: lt_of_le_of_lt (IsNonarchimedean.apply_sum_le_sup (fun _ _ => padicNorm.nonarchimedean) hs)
    (Finset.sup'_lt_iff hs).2 hF

Depends on / 依赖: Finset, Finset.sup, IsNonarchimedean, IsNonarchimedean.apply_sum_le_sup, _lt_iff, apply_sum_le_sup, lt_of_le_of_lt, nonarchimedean, padicNorm, padicNorm.nonarchimedean
-/
theorem sum_lt {α : Type*} {F : α -> Rat} {t : Rat} {s : Finset α} (hs : s.Nonempty)
    (hF : forall i in s, padicNorm p (F i) < t) : padicNorm p (∑ i in s, F i) < t :=
lt_of_le_of_lt (IsNonarchimedean.apply_sum_le_sup (fun _ _ => padicNorm.nonarchimedean) hs)
    (Finset.sup'_lt_iff hs).2 hF

/--
theorem `sum_le` / 定理 `sum_le`

English:
theorem sum_le
  statement: {α : Type*} {F : α -> Rat} {t : Rat} {s : Finset α} (hs : s.Nonempty)
  proof: (IsNonarchimedean.apply_sum_le_sup (fun _ _ => padicNorm.nonarchimedean) hs).trans
    (Finset.sup'_le_iff hs (fun i => padicNorm p (F i))).2 hF

中文:
定理 sum_le
  结论: {α : 类型} {F : α -> Rat} {t : Rat} {s : Finset α} (hs : s.Nonempty)
  证明: (IsNonarchimedean.apply_sum_le_sup (fun _ _ => padicNorm.nonarchimedean) hs).trans
    (Finset.sup'_le_iff hs (fun i => padicNorm p (F i))).2 hF

Depends on / 依赖: Finset, Finset.sup, IsNonarchimedean, IsNonarchimedean.apply_sum_le_sup, _le_iff, apply_sum_le_sup, nonarchimedean, padicNorm, padicNorm.nonarchimedean
-/
theorem sum_le {α : Type*} {F : α -> Rat} {t : Rat} {s : Finset α} (hs : s.Nonempty)
    (hF : forall i in s, padicNorm p (F i) <= t) : padicNorm p (∑ i in s, F i) <= t :=
(IsNonarchimedean.apply_sum_le_sup (fun _ _ => padicNorm.nonarchimedean) hs).trans
    (Finset.sup'_le_iff hs (fun i => padicNorm p (F i))).2 hF

/--
theorem `sum_lt'` / 定理 `sum_lt'`

English:
theorem sum_lt'
  statement: {α : Type*} {F : α -> Rat} {t : Rat} {s : Finset α}
  proof: by
  obtain rfl | hs := Finset.eq_empty_or_nonempty s
  · simp [ht]
  · exact sum_lt hs hF

中文:
定理 sum_lt'
  结论: {α : 类型} {F : α -> Rat} {t : Rat} {s : Finset α}
  证明: by
  obtain rfl | hs := Finset.eq_empty_or_nonempty s
  · simp [ht]
  · exact sum_lt hs hF

Depends on / 依赖: Finset, Finset.eq_empty_or_nonempty, eq_empty_or_nonempty, sum_lt
-/
theorem sum_lt' {α : Type*} {F : α -> Rat} {t : Rat} {s : Finset α}
    (hF : forall i in s, padicNorm p (F i) < t) (ht : 0 < t) : padicNorm p (∑ i in s, F i) < t := by
  obtain rfl | hs := Finset.eq_empty_or_nonempty s
  · simp [ht]
  · exact sum_lt hs hF

/--
theorem `sum_le'` / 定理 `sum_le'`

English:
theorem sum_le'
  statement: {α : Type*} {F : α -> Rat} {t : Rat} {s : Finset α}
  proof: by
  obtain rfl | hs := Finset.eq_empty_or_nonempty s
  · simp [ht]
  · exact sum_le hs hF

中文:
定理 sum_le'
  结论: {α : 类型} {F : α -> Rat} {t : Rat} {s : Finset α}
  证明: by
  obtain rfl | hs := Finset.eq_empty_or_nonempty s
  · simp [ht]
  · exact sum_le hs hF

Depends on / 依赖: Finset, Finset.eq_empty_or_nonempty, eq_empty_or_nonempty, sum_le
-/
theorem sum_le' {α : Type*} {F : α -> Rat} {t : Rat} {s : Finset α}
    (hF : forall i in s, padicNorm p (F i) <= t) (ht : 0 <= t) : padicNorm p (∑ i in s, F i) <= t := by
  obtain rfl | hs := Finset.eq_empty_or_nonempty s
  · simp [ht]
  · exact sum_le hs hF

end padicNorm
